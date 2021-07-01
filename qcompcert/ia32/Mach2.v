(* *********************************************************************)
(*                                                                     *)
(*             The Quantitative CompCert verified compiler             *)
(*                                                                     *)
(*                 Tahina Ramananandro, Yale University                *)
(*                                                                     *)
(*  This file is derived from the backend/Mach.v file of the           *)
(*  CompCert 1.13 verified compiler by Xavier Leroy, INRIA.            *)
(*  The CompCert verified compiler is                                  *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  The original file is           *)
(*  distributed                                                        *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*  According to this license, this modified version is distributed    *)
(*  under a similar license (see LICENSE for details).                 *)
(*                                                                     *)
(* *********************************************************************)


(** The [Mach2] intermediate language.

    As explained in Section 3.2 of our PLDI 2014 paper, [Mach2] and
    [Mach] have the same abstract syntax. [Mach2] is just a
    reinterpretation of [Mach] with a finite stack space. Stack frames
    of all function calls are merged together into a single
    whole-program stack block.

*)

Require Import Memory.
Require Import AST.
Require Import Values.
Require Import Events.
Require Import Coqlib.
Require Import Locations.
Require Import Globalenvs.
Require Import Op.
Require Import Integers.
Require Import Conventions.
Require Import Smallstep.
Require Import Mach.
Require Import Stackbounds.

Section WITHRAO.

Variable external_event_needs: event -> Z.

Variable return_address_offset: function -> code -> int -> Prop.

Section RELSEM.

Variable ge: genv.

Inductive stackframe: Type :=
  | Stackframe:
      forall (f: block)       (**r pointer to calling function *)
             (retaddr: int)   (**r Asm return address in calling function (needed to show that the code [c] below can be compiled to some assembly code)  *) 
             (c: code),       (**r program point in calling function *)
      stackframe.

Inductive state: Type :=
  | State:
      forall (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to current function *)
             (sp: val)                 (**r stack pointer *)
             (c: code)                 (**r current program point *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Callstate:
      forall
             (sp: val)                 (**r stack pointer *)
             (stack: list stackframe)  (**r call stack *)
             (f: block)                (**r pointer to function to call *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state
  | Returnstate:
      forall
             (sp: val)                 (**r stack pointer *)
             (stack: list stackframe)  (**r call stack *)
             (rs: regset)              (**r register state *)
             (m: mem),                 (**r memory state *)
      state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_Mlabel:
      forall s f sp lbl c rs m,
      step (State s f sp (Mlabel lbl :: c) rs m)
        E0 (State s f sp c rs m)
  | exec_Mgetstack:
      forall s f sp ofs ty dst c rs m v,
      load_stack m sp ty ofs = Some v ->
      step (State s f sp (Mgetstack ofs ty dst :: c) rs m)
        E0 (State s f sp c (rs#dst <- v) m)
  | exec_Msetstack:
      forall s f sp src ofs ty c rs m m',
      store_stack m sp ty ofs (rs src) = Some m' ->
      step (State s f sp (Msetstack src ofs ty :: c) rs m)
        E0 (State s f sp c (undef_setstack rs) m')
  | exec_Mgetparam:
      forall s fb f sp psp ofs ty dst c rs m v,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      psp = Val.add sp (Vint (Int.repr (f.(fn_stacksize) + size_chunk Mint32))) ->
      load_stack m psp ty ofs = Some v ->
      step (State s fb sp (Mgetparam ofs ty dst :: c) rs m)
        E0 (State s fb sp c (rs # IT1 <- Vundef # dst <- v) m)
  | exec_Mop:
      forall s f sp op args res c rs m v,
      eval_operation ge sp op rs##args m = Some v ->
      step (State s f sp (Mop op args res :: c) rs m)
        E0 (State s f sp c ((undef_op op rs)#res <- v) m)
  | exec_Mload:
      forall s f sp chunk addr args dst c rs m a v,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.loadv chunk m a = Some v ->
      step (State s f sp (Mload chunk addr args dst :: c) rs m)
        E0 (State s f sp c ((undef_temps rs)#dst <- v) m)
  | exec_Mstore:
      forall s f sp chunk addr args src c rs m m' a,
      eval_addressing ge sp addr rs##args = Some a ->
      Mem.storev chunk m a (rs src) = Some m' ->
      step (State s f sp (Mstore chunk addr args src :: c) rs m)
        E0 (State s f sp c (undef_temps rs) m')
  | exec_Mcall:
      forall s fb sp spp sig ros c rs m m' f f' ra,
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      spp = Val.sub sp (Vint (Int.repr (size_chunk Mint32))) ->
      Mem.storev Mint32 m spp (Vptr fb ra) = Some m' ->
      return_address_offset f c ra ->
      step (State s fb sp (Mcall sig ros :: c) rs m)
        E0 (Callstate spp (Stackframe fb ra c :: s)
                       f' rs m')
  | exec_Mtailcall:
      forall s fb sp spp sig ros c rs m f f',
      find_function_ptr ge ros rs = Some f' ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      spp = Val.add sp (Vint (Int.repr (f.(fn_stacksize)))) ->
      forall FID (HFID: FID = f.(fn_id)),
      step (State s fb sp (Mtailcall sig ros :: c) rs m)
        (Event_return FID :: E0) (Callstate spp s f' rs m)
  | exec_Mbuiltin:
      forall s f sp rs m ef args res b t v m',
      external_call ef ge rs##args m t v m' ->
      forall NEED: forall s o, sp = Vptr s o ->
                               Mem.range_perm m s (Int.unsigned o - size_chunk Mint32 - trace_needs external_event_needs t) (Int.unsigned o - size_chunk Mint32) Cur Freeable (* must have enough stack space for external function *),
      step (State s f sp (Mbuiltin ef args res :: b) rs m)
         t (State s f sp b ((undef_temps rs)#res <- v) m')
  | exec_Mannot:
      forall s f sp rs m ef args b vargs t v m',
      annot_arguments rs m sp args vargs ->
      external_call ef ge vargs m t v m' ->
      forall NEED: forall s o, sp = Vptr s o ->
                               Mem.range_perm m s (Int.unsigned o - size_chunk Mint32 - trace_needs external_event_needs t) (Int.unsigned o - size_chunk Mint32) Cur Freeable (* must have enough stack space for external function *),
      step (State s f sp (Mannot ef args :: b) rs m)
         t (State s f sp b rs m')
  | exec_Mgoto:
      forall s fb f sp lbl c rs m c',
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s fb sp (Mgoto lbl :: c) rs m)
        E0 (State s fb sp c' rs m)
  | exec_Mcond_true:
      forall s fb f sp cond args lbl c rs m c',
      eval_condition cond rs##args m = Some true ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s fb sp (Mcond cond args lbl :: c) rs m)
        E0 (State s fb sp c' (undef_temps rs) m)
  | exec_Mcond_false:
      forall s f sp cond args lbl c rs m,
      eval_condition cond rs##args m = Some false ->
      step (State s f sp (Mcond cond args lbl :: c) rs m)
        E0 (State s f sp c (undef_temps rs) m)
  | exec_Mjumptable:
      forall s fb f sp arg tbl c rs m n lbl c',
      rs arg = Vint n ->
      list_nth_z tbl (Int.unsigned n) = Some lbl ->
      Genv.find_funct_ptr ge fb = Some (Internal f) ->
      find_label lbl f.(fn_code) = Some c' ->
      step (State s fb sp (Mjumptable arg tbl :: c) rs m)
        E0 (State s fb sp c' (undef_temps rs) m)
  | exec_Mreturn:
      forall s fb sp psp c rs m f,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->

      (* For function return, instead of freeing the stack frame
         block, the stack pointer goes from the callee's stack frame
         to the caller's stack frame within the single whole-program
         stack block by directly performing pointer arithmetics on the
         stack pointer. Thanks to this pointer arithmetics, no
         additional back link is necessary, as was the case in the
         genuine CompCert.

         The pointer arithmetics here is specific to x86.
       *)

      psp = Val.add sp (Vint (Int.repr f.(fn_stacksize))) ->
      forall FID (HFID: FID = f.(fn_id)),
      step (State s fb sp (Mreturn :: c) rs m)
        (Event_return FID :: E0) (Returnstate psp s rs m)
  | exec_function_internal:
      forall s fb rs m f sp csp,
      Genv.find_funct_ptr ge fb = Some (Internal f) ->

      (* For function call, instead of allocating a new block, the new
         stack frame is obtained within the single whole-program stack
         block by directly performing pointer arithmetics on the stack
         pointer.

         The pointer arithmetics here is specific to x86.
       *)
         
      csp = Val.sub sp (Vint (Int.repr f.(fn_stacksize))) ->
      forall FID (HFID: FID = f.(fn_id)),
      step (Callstate sp s fb rs m)
        (Event_call FID :: E0) (State s fb csp f.(fn_code) (undef_temps rs) m)
  | exec_function_external:
      forall s fb rs m t rs' ef args res m' sp psp,
      Genv.find_funct_ptr ge fb = Some (External ef) ->
      external_call ef ge args m t res m' ->
      psp = Val.add sp (Vint (Int.repr (size_chunk  Mint32))) ->
      extcall_arguments rs m psp (ef_sig ef) args ->
      rs' = (rs#(loc_result (ef_sig ef)) <- res) ->
      forall NEED: forall s o, sp = Vptr s o ->
                               Mem.range_perm m s (Int.unsigned o - trace_needs external_event_needs t) (Int.unsigned o) Cur Freeable (* must have enough stack space for external function *),
      step (Callstate sp s fb rs m)
         t (Returnstate sp s rs' m')
  | exec_return:
      forall s f fd sp psp ra c rs m,
        psp = Val.add sp (Vint (Int.repr (size_chunk Mint32))) ->
      Mem.loadv Mint32 m sp = Some (Vptr f ra) ->
      Genv.find_funct_ptr ge f = Some (Internal fd) ->
      return_address_offset fd c ra ->      
      step (Returnstate sp (Stackframe f ra c :: s) rs m)
        E0 (State s f psp c rs m).

End RELSEM.

Section BOUNDED.

Variable bound: int.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall fb m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      forall m1 stk, 
      Mem.alloc m0 0 (Int.unsigned bound) = (m1, stk) ->
      Genv.find_symbol ge p.(prog_main) = Some fb ->
      initial_state p (Callstate (Vptr stk bound) nil fb (Regmap.init Vundef) m1).

Inductive final_state (p: program): state -> int -> Prop :=
  | final_state_intro: forall sp rs m r,
      rs (loc_result (mksignature nil (Some Tint))) = Vint r ->
      sp = Vptr (Genv.genv_next (Genv.globalenv p)) bound ->
      final_state p (Returnstate sp nil rs m) r.

Definition semantics (p: program) :=
  Semantics (step) (initial_state p) (final_state p) (Genv.globalenv p).

End BOUNDED.

End WITHRAO.
