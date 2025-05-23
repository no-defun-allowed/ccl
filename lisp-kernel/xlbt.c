/*
 * Copyright 2005-2009 Clozure Associates
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "lispdcmd.h"
#include "x86-utils.h"
#include <stdio.h>
#include <signal.h>

natural
pc_from_xcf(xcf *xcf)
{
  if (functionp(xcf->nominal_function)) {
    LispObj fv = function_to_function_vector(xcf->nominal_function);
    if (fv == xcf->containing_uvector) {
      unsigned tag;

#ifdef X8664
      tag = tag_function;
#else
      tag = fulltag_misc;
#endif
      return unbox_fixnum(xcf->relative_pc) - tag;
    } else {
      LispObj tra = xcf->ra0;
      LispObj f = tra_function(tra);

      if (f && f == xcf->nominal_function)
	return tra_offset(tra);
    }
  }
  return 0;
}

void
print_lisp_frame(lisp_frame *frame)
{
  LispObj pc = frame->tra, fun=0;
  int delta = 0;

  if (pc == lisp_global(RET1VALN)) {
    pc = frame->xtra;
  }
#ifdef X8632
  if (fulltag_of(pc) == fulltag_tra) {
    if (*((unsigned char *)pc) == RECOVER_FN_OPCODE) {
      natural n = *((natural *)(pc + 1));
      fun = (LispObj)n;
    }
    if (fun && header_subtag(header_of(fun)) == subtag_function) {
      delta = pc - fun;
      Dprintf("(#x%08X) #x%08X : %s + %d", frame, pc, print_lisp_object(fun), delta);
      return;
    }
  }
  if (pc == 0) {
    natural rpc = pc_from_xcf((xcf *)frame);

    fun = ((xcf *)frame)->nominal_function;
    fprintf(dbgout, "(#x%08X) #x%08X : %s + ", frame, pc,
	    print_lisp_object(fun));
    if (rpc)
      fprintf(dbgout, "%d\n", rpc);
    else
      fprintf(dbgout, "??\n", rpc);
    return;
  }
#else
  if (pc >= (LispObj)code_area->low && pc < (LispObj)code_area->high) {
    LispObj fun = ((LispObj*)frame)[-1];
    if (fun && fulltag_of(fun) == fulltag_function) {
      LispObj *base = (LispObj*)ptr_from_lispobj(untag(fun));
      delta = pc - base[1];
    }
    Dprintf("(#x%016lX) #x%016lX : %s + %d", frame, pc, print_lisp_object(fun), delta);
  }
  if (pc == 0) {
    natural rpc = pc_from_xcf((xcf *)frame);

    fun = ((xcf *)frame)->nominal_function;
    fprintf(dbgout, "(#x%016lX) #x%016lX : %s + ", frame, pc,
	    print_lisp_object(fun));
    if (rpc)
      fprintf(dbgout, "%d\n", rpc);
    else
      fprintf(dbgout, "??\n");
    return;
  }
#endif
}

Boolean
lisp_frame_p(lisp_frame *f)
{
  LispObj ra;

  if (f) {
    ra = f->tra;
    if (ra == lisp_global(RET1VALN)) {
      ra = f->xtra;
    }

#ifdef X8632
    if (fulltag_of(ra) == fulltag_tra) {
#else
    if (ra >= (LispObj)code_area->low && ra < (LispObj)code_area->high) {
#endif
      return true;
    } else if ((ra == lisp_global(LEXPR_RETURN)) ||
	       (ra == lisp_global(LEXPR_RETURN1V))) {
      return true;
    } else if (ra == 0) {
      return true;
    }
  }
  return false;
}

void
walk_stack_frames(lisp_frame *start, lisp_frame *end) 
{
  lisp_frame *next;
  Dprintf("\n");
  while (start < end) {

    if (lisp_frame_p(start)) {
      print_lisp_frame(start);
    } else {
      if (start->backlink) {
        fprintf(dbgout, "Bogus frame %lx -> %lx\n", start, start->backlink);
        /* Try to keep scanning if we have at least progressed up the stack. */
        if (start->backlink > end || start->backlink < start) return;
      }
    }
    
    next = start->backlink;
    if (next == 0) {
      next = end;
    }
    if (next < start) {
      fprintf(dbgout, "Bad frame! (%x < %x)\n", next, start);
      break;
    }
    start = next;
  }
}

char *
interrupt_level_description(TCR *tcr)
{
  signed_natural level = (signed_natural) TCR_INTERRUPT_LEVEL(tcr);
  if (level < 0) {
    if (tcr->interrupt_pending) {
      return "disabled(pending)";
    } else {
      return "disabled";
    }
  } else {
    return "enabled";
  }
}

void
plbt_sp(LispObj current_fp)
{
  area *vs_area, *cs_area;
  TCR *tcr = (TCR *)get_tcr(true);
  char *ilevel = interrupt_level_description(tcr);

  vs_area = tcr->vs_area;
  cs_area = TCR_AUX(tcr)->cs_area;
  if ((((LispObj) ptr_to_lispobj(vs_area->low)) > current_fp) ||
      (((LispObj) ptr_to_lispobj(vs_area->high)) < current_fp)) {
    current_fp = (LispObj) (tcr->save_fp);
  }
  if ((((LispObj) ptr_to_lispobj(vs_area->low)) > current_fp) ||
      (((LispObj) ptr_to_lispobj(vs_area->high)) < current_fp)) {
    Dprintf("\nFrame pointer [#x" LISP "] in unknown area.", current_fp);
  } else {
    fprintf(dbgout, "current thread: tcr = 0x" LISP ", native thread ID = 0x" LISP ", interrupts %s\n", tcr, TCR_AUX(tcr)->native_thread_id, ilevel);

#ifndef WINDOWS
    if (lisp_global(BATCH_FLAG)) {
      /*
       * In batch mode, we will be exiting.  Reset some signal actions
       * to the default to avoid a loop of "Unhandled exception 11" or
       * whatever if we try to print some call stack that is totally
       * screwed up.  (Instead, we'll just die horribly and get it
       * over with.)
       */
      signal(SIGBUS, SIG_DFL);
      signal(SIGSEGV, SIG_DFL);
    }
#endif
    walk_stack_frames((lisp_frame *) ptr_from_lispobj(current_fp), (lisp_frame *) (vs_area->high));
    /*      walk_other_areas();*/
  }
}


void
plbt(ExceptionInformation *xp)
{
#ifdef X8664
  LispObj pc = xpGPR(xp, Iip), fun = xpGPR(xp, Ifn), nfn = xpGPR(xp, Infn);
  LispObj *base = (LispObj*)ptr_from_lispobj(untag(fun));
  LispObj *nfn_base = (LispObj*)ptr_from_lispobj(untag(nfn));
  int delta = fulltag_of(fun) == fulltag_function ? pc - base[1] : 0;
  int nfn_delta = fulltag_of(nfn) == fulltag_function ? pc - nfn_base[1] : 0;
  if (nfn_delta > 0 && nfn_delta < delta) {
    Dprintf("(%18s) #x%016lX : %s + %d", "current frame/nfn", pc, print_lisp_object(nfn), nfn_delta);
    Dprintf("(%18s) %18s : %s", "current frame/ fn", "", print_lisp_object(fun));
  } else {
    Dprintf("(%18s) #x%016lX : %s + %d", "current frame/fn", pc, print_lisp_object(fun), delta);
  }
#endif
  plbt_sp(xpGPR(xp, Ifp));
}
