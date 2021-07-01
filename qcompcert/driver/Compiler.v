(* *********************************************************************)
(*                                                                     *)
(*             The Quantitative CompCert verified compiler             *)
(*                                                                     *)
(*                 Tahina Ramananandro, Yale University                *)
(*                                                                     *)
(*  This file is a modified version of the                             *)
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

(** The whole compiler and its proof of semantic preservation *)

(** Libraries. *)
Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Smallstep.
(** Languages (syntax and semantics). *)
Require Csyntax.
Require Csem.
Require Cstrategy.
Require Cexec.
Require Clight.
Require Csharpminor.
Require Cminor.
Require CminorSel.
Require RTL.
Require LTL.
Require LTLin.
Require Linear.
Require Mach.
Require Asm.
(** Translation passes. *)
Require Initializers.
Require SimplExpr.
Require SimplLocals.
Require Cshmgen.
Require Cminorgen.
Require Selection.
Require RTLgen.
(* Require Tailcall.
Require Inlining. *)
Require Renumber.
Require Constprop.
Require CSE.
Require Allocation.
Require Tunneling.
Require Linearize.
Require CleanupLabels.
Require Reload.
Require RRE.
Require Stacking.
Require Asmgen.
(** Type systems. *)
Require RTLtyping.
Require LTLtyping.
Require LTLintyping.
Require Lineartyping.
(** Proofs of semantic preservation and typing preservation. *)
Require SimplExprproof.
Require SimplLocalsproof.
Require Cshmgenproof.
Require Cminorgenproof.
Require Selectionproof.
Require RTLgenproof.
(* Require Tailcallproof.
Require Inliningproof. *)
Require Renumberproof.
Require Constpropproof.
Require CSEproof.
Require Allocproof.
Require Alloctyping.
Require Tunnelingproof.
Require Tunnelingtyping.
Require Linearizeproof.
Require Linearizetyping.
Require CleanupLabelsproof.
Require CleanupLabelstyping.
Require Reloadproof.
Require Reloadtyping.
Require RREproof.
Require RREtyping.
Require Stackingproof.
Require Asmgenproof.
Require Mach2Mach2.
Require Import Memdata.
Require Import Behaviors.
Require Import Stackbounds.
Require Import Prune.
Require Import Maps.

(** Pretty-printers (defined in Caml). *)
Parameter print_Clight: Clight.program -> unit.
Parameter print_Cminor: Cminor.program -> unit.
Parameter print_RTL: RTL.program -> unit.
Parameter print_RTL_tailcall: RTL.program -> unit.
Parameter print_RTL_inline: RTL.program -> unit.
Parameter print_RTL_constprop: RTL.program -> unit.
Parameter print_RTL_cse: RTL.program -> unit.
Parameter print_LTLin: LTLin.program -> unit.
Parameter print_Mach: Mach.program -> unit.

Open Local Scope string_scope.

(** * Composing the translation passes *)

(** We first define useful monadic composition operators,
    along with funny (but convenient) notations. *)

Definition apply_total (A B: Type) (x: res A) (f: A -> B) : res B :=
  match x with Error msg => Error msg | OK x1 => OK (f x1) end.

Definition apply_partial (A B: Type)
                         (x: res A) (f: A -> res B) : res B :=
  match x with Error msg => Error msg | OK x1 => f x1 end.

Notation "a @@@ b" :=
   (apply_partial _ _ a b) (at level 50, left associativity).
Notation "a @@ b" :=
   (apply_total _ _ a b) (at level 50, left associativity).

Definition print {A: Type} (printer: A -> unit) (prog: A) : A :=
  let unused := printer prog in prog.

(** We define three translation functions for whole programs: one
  starting with a C program, one with a Cminor program, one with an
  RTL program.  The three translations produce Asm programs ready for
  pretty-printing and assembling.
 *)

Definition transf_rtl_to_mach (f: RTL.program) : res Mach.program :=
   OK f
   @@ print print_RTL
(*   @@ Tailcall.transf_program *)
   @@ print print_RTL_tailcall
(*  @@@ Inlining.transf_program *)
   @@ Renumber.transf_program
   @@ print print_RTL_inline
   @@ Constprop.transf_program
   @@ Renumber.transf_program
   @@ print print_RTL_constprop
  @@@ CSE.transf_program
   @@ print print_RTL_cse
  @@@ Allocation.transf_program
   @@ Tunneling.tunnel_program
  @@@ Linearize.transf_program
   @@ CleanupLabels.transf_program
   @@ print print_LTLin
   @@ Reload.transf_program
   @@ RRE.transf_program
  @@@ Stacking.transf_program
   @@ print print_Mach.

Definition transf_mach_program p :=
  Mach2Mach2.transf_program p
  @@@ Asmgen.transf_program.

Lemma transf_mach_program_stacksizes_pos :
  forall p tp,
    transf_mach_program p = OK tp ->
    forall f, (0 <= PMap.get f (Mach2Mach2.stacksizes p))%Z.
Proof.
  unfold transf_mach_program. intros until tp. case_eq (Mach2Mach2.transf_program p); try discriminate. intros; eauto using Mach2Mach2.stacksizes_pos.
Qed.

Definition transf_rtl_program f :=
  transf_rtl_to_mach f
  @@@ transf_mach_program.

Definition transf_cminor_to_mach (p: Cminor.program) : res Mach.program :=
   OK p
   @@ print print_Cminor
   @@ Selection.sel_program
  @@@ RTLgen.transl_program
  @@@ transf_rtl_to_mach.

Definition transf_cminor_program p :=
  transf_cminor_to_mach p
  @@@ transf_mach_program.

Definition transf_clight_to_mach (p: Clight.program) : res Mach.program :=
  OK p 
   @@ print print_Clight
  @@@ SimplLocals.transf_program
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ transf_cminor_to_mach.

Definition transf_clight_program p :=
  transf_clight_to_mach p 
  @@@ transf_mach_program.

Definition transf_clight2_to_mach (p: Clight.program) : res Mach.program :=
  OK p 
   @@ print print_Clight
  @@@ Cshmgen.transl_program
  @@@ Cminorgen.transl_program
  @@@ transf_cminor_to_mach.

Definition transf_clight2_program p :=
  transf_clight2_to_mach p 
  @@@ transf_mach_program.

Definition transf_c_to_mach p :=
  OK p 
  @@@ SimplExpr.transl_program
  @@@ transf_clight_to_mach.

Definition transf_c_program (p: Csyntax.program) : res Asm.program :=
  transf_c_to_mach p
  @@@ transf_mach_program.

(** Force [Initializers] and [Cexec] to be extracted as well. *)

Definition transl_init := Initializers.transl_init.
Definition cexec_do_step := Cexec.do_step.

(** The following lemmas help reason over compositions of passes. *)

Lemma print_identity:
  forall (A: Type) (printer: A -> unit) (prog: A),
  print printer prog = prog.
Proof.
  intros; unfold print. destruct (printer prog); auto. 
Qed.

Lemma compose_print_identity:
  forall (A: Type) (x: res A) (f: A -> unit), 
  x @@ print f = x.
Proof.
  intros. destruct x; simpl. rewrite print_identity. auto. auto. 
Qed.

(** * Semantic preservation *)

(** We first prove that the [transf_program] translations preserve semantics
  by constructing the following simulations:
- Forward simulations from [Cstrategy] / [Clight] / [Clight2] / [Cminor]
   / [RTL] to [Mach]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Mach]).
- Backward simulation from [Csem] to [Mach]
  (composition of two backward simulations)
.
Because tailcall recognition and function inlining are not yet supported,
those simulation diagrams exactly preserve the traces (including the
call/return events), thus we have a fortiori quantitative refinement.
*)

Theorem transf_rtl_to_mach_correct:
  forall p tp,
  transf_rtl_to_mach p = OK tp ->
  forward_simulation (RTL.semantics p) (Mach.semantics tp)
  * backward_simulation (RTL.semantics p) (Mach.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (RTL.semantics p) (Mach.semantics tp)).
  unfold transf_rtl_to_mach in H.
  repeat rewrite compose_print_identity in H.
  simpl in H.
  set (p1 := (* Tailcall.transf_program *) p) in *.
(*  destruct (Inlining.transf_program p1) as [p11|] eqn:?; simpl in H; try discriminate. *)
  set (p12 := Renumber.transf_program p1) in *.
  set (p2 := Constprop.transf_program p12) in *.
  set (p21 := Renumber.transf_program p2) in *.
  destruct (CSE.transf_program p21) as [p3|] eqn:?; simpl in H; try discriminate.
  destruct (Allocation.transf_program p3) as [p4|] eqn:?; simpl in H; try discriminate.
  set (p5 := Tunneling.tunnel_program p4) in *.
  destruct (Linearize.transf_program p5) as [p6|] eqn:?; simpl in H; try discriminate.
  set (p7 := CleanupLabels.transf_program p6) in *.
  set (p8 := Reload.transf_program p7) in *.
  set (p9 := RRE.transf_program p8) in *.
  destruct (Stacking.transf_program p9) as [p10|] eqn:?; simpl in H; try discriminate.

  assert(TY1: LTLtyping.wt_program p5).
    eapply Tunnelingtyping.program_typing_preserved. 
    eapply Alloctyping.program_typing_preserved; eauto.
  assert(TY2: LTLintyping.wt_program p7).
    eapply CleanupLabelstyping.program_typing_preserved.
    eapply Linearizetyping.program_typing_preserved; eauto.
  assert(TY3: Lineartyping.wt_program p9).
    eapply RREtyping.program_typing_preserved.
    eapply Reloadtyping.program_typing_preserved; eauto.

(*  eapply compose_forward_simulation. apply Tailcallproof.transf_program_correct. 
  eapply compose_forward_simulation. apply Inliningproof.transf_program_correct. eassumption. *)
  eapply compose_forward_simulation. apply Renumberproof.transf_program_correct. 
  eapply compose_forward_simulation. apply Constpropproof.transf_program_correct. 
  eapply compose_forward_simulation. apply Renumberproof.transf_program_correct. 
  eapply compose_forward_simulation. apply CSEproof.transf_program_correct. eassumption.
  eapply compose_forward_simulation. apply Allocproof.transf_program_correct. eassumption.
  eapply compose_forward_simulation. apply Tunnelingproof.transf_program_correct.
  eapply compose_forward_simulation. apply Linearizeproof.transf_program_correct. eassumption. eauto. 
  eapply compose_forward_simulation. apply CleanupLabelsproof.transf_program_correct. 
  eapply compose_forward_simulation. apply Reloadproof.transf_program_correct. eauto.
  eapply compose_forward_simulation. apply RREproof.transf_program_correct. eauto.
  apply Stackingproof.transf_program_correct.
  unfold p9, p8, p7 in *.
  congruence.
  assumption.

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply RTL.semantics_receptive.
  apply Mach.semantics_determinate.
Qed.  

Theorem transf_cminor_to_mach_correct:
  forall p tp,
  transf_cminor_to_mach p = OK tp ->
  forward_simulation (Cminor.semantics p) (Mach.semantics tp)
  * backward_simulation (Cminor.semantics p) (Mach.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (Cminor.semantics p) (Mach.semantics tp)).
  unfold transf_cminor_to_mach in H.
  repeat rewrite compose_print_identity in H.
  simpl in H. 
  set (p1 := Selection.sel_program p) in *.
  destruct (RTLgen.transl_program p1) as [p2|] eqn:?; simpl in H; try discriminate.
  eapply compose_forward_simulation. apply Selectionproof.transf_program_correct.
  eapply compose_forward_simulation. apply RTLgenproof.transf_program_correct. eassumption.
  exact (fst (transf_rtl_to_mach_correct _ _ H)).

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply Cminor.semantics_receptive.
  apply Mach.semantics_determinate.
Qed.

Theorem transf_clight2_to_mach_correct:
  forall p tp,
  transf_clight2_to_mach p = OK tp ->
  forward_simulation (Clight.semantics2 p) (Mach.semantics tp)
  * backward_simulation (Clight.semantics2 p) (Mach.semantics tp).
Proof.
  intros. 
  assert (F: forward_simulation (Clight.semantics2 p) (Mach.semantics tp)).
  revert H; unfold transf_clight2_to_mach; simpl.
  rewrite print_identity.
  caseEq (Cshmgen.transl_program p); simpl; try congruence; intros p1 EQ1.
  caseEq (Cminorgen.transl_program p1); simpl; try congruence; intros p2 EQ2.
  intros EQ3.
  eapply compose_forward_simulation. apply Cshmgenproof.transl_program_correct. eauto.
  eapply compose_forward_simulation. apply Cminorgenproof.transl_program_correct. eauto.
  exact (fst (transf_cminor_to_mach_correct _ _ EQ3)). 

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply Clight.semantics2_receptive.
  apply Mach.semantics_determinate.
Qed.

Theorem transf_clight_to_mach_correct:
  forall p tp,
  transf_clight_to_mach p = OK tp ->
  forward_simulation (Clight.semantics1 p) (Mach.semantics tp)
  * backward_simulation (Clight.semantics1 p) (Mach.semantics tp).
Proof.
  intros. 
  assert (F: forward_simulation (Clight.semantics1 p) (Mach.semantics tp)).
  revert H; unfold transf_clight_to_mach; simpl.
  rewrite print_identity.
  caseEq (SimplLocals.transf_program p); simpl; try congruence; intros p0 EQ0.
  caseEq (Cshmgen.transl_program p0); simpl; try congruence; intros p1 EQ1.
  caseEq (Cminorgen.transl_program p1); simpl; try congruence; intros p2 EQ2.
  intros EQ3.
  eapply compose_forward_simulation. apply SimplLocalsproof.transf_program_correct. eauto.
  eapply compose_forward_simulation. apply Cshmgenproof.transl_program_correct. eauto.
  eapply compose_forward_simulation. apply Cminorgenproof.transl_program_correct. eauto.
  exact (fst (transf_cminor_to_mach_correct _ _ EQ3)). 

  split. auto. 
  apply forward_to_backward_simulation. auto. 
  apply Clight.semantics_receptive.
  apply Mach.semantics_determinate.
Qed.

Theorem transf_cstrategy_to_mach_correct:
  forall p tp,
  transf_c_to_mach p = OK tp ->
  forward_simulation (Cstrategy.semantics p) (Mach.semantics tp)
  * backward_simulation (atomic (Cstrategy.semantics p)) (Mach.semantics tp).
Proof.
  intros.
  assert (F: forward_simulation (Cstrategy.semantics p) (Mach.semantics tp)).
  revert H; unfold transf_c_to_mach; simpl.
  caseEq (SimplExpr.transl_program p); simpl; try congruence; intros p0 EQ0.
  intros EQ1.
  eapply compose_forward_simulation. apply SimplExprproof.transl_program_correct. eauto.
  exact (fst (transf_clight_to_mach_correct _ _ EQ1)). 

  split. auto. 
  apply forward_to_backward_simulation.
  apply factor_forward_simulation. auto. eapply sd_traces. eapply Mach.semantics_determinate.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Mach.semantics_determinate.
Qed.

Theorem transf_c_to_mach_correct:
  forall p tp,
  transf_c_to_mach p = OK tp ->
  backward_simulation (Csem.semantics p) (Mach.semantics tp).
Proof.
  intros. 
  apply compose_backward_simulation with (atomic (Cstrategy.semantics p)).
  eapply sd_traces; eapply Mach.semantics_determinate.
  apply factor_backward_simulation. 
  apply Cstrategy.strategy_simulation.
  apply Csem.semantics_single_events.
  eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.
  exact (snd (transf_cstrategy_to_mach_correct _ _ H)).
Qed.


(** We then prove that the [transf_program] translations preserve the
    semantics of source programs, if provided a proof that the source
    program does not stack overflow.
    As explained in Section 3.2 of our PLDI 2014 paper, [Mach2] and [Asm]
    do have a finite stack, but [Asm] no longer supports call/return events.
    So it suffices to show that non-call/return traces, aka. pruned traces,
    are preserved by [transf_program].
    To this end, we construct the following simulations:
- Forward simulations from the *pruned* [Cstrategy] / [Clight] / [Clight2]
   / [Cminor] / [RTL] / [Mach] to [Asm]
  (composition of the forward simulations for each pass).
- Backward simulations for the same languages
  (derived from the forward simulation, using receptiveness of the source
  language and determinacy of [Mach]).
- Backward simulation from the *pruned* [Csem] to [Asm]
  (composition of two backward simulations)
.
*)

Section Bound.

(** We assume that the available stack size [bound] of the process in
    the target machine is machine-representable, and that the stack is
    strongly aligned. *)

Variables
  (bound : Integers.Int.int)
  (Hbound: (Stacklayout.strong_align
       | Integers.Int.unsigned bound + size_chunk Mint32))
  (external_event_needs: Events.event -> Z).

Open Scope Z_scope.

(** [Mach] to [Asm].

    To compute the weights (cf. Section 3.1) of the traces of the
    [Mach] program, we instantiate the stack metric with the sizes of
    the stack frames obtained in [Mach] and adjusted by the
    [Mach]-to-[Mach2] pass ([Mach2Mach2.stacksizes]).

    Then, the condition [NO_OVERFLOW] below imposes that those weights
    must not exceed [bound].

    Under this condition, the target [Asm] program is guaranteed to
    refine the [Mach] source program. In particular, if the [Mach]
    program does not go wrong, then the [Asm] program is guaranteed to
    not stack overflow.
*)

Theorem transf_mach_program_correct_strong:
  forall p
    (NO_OVERFLOW:
       forall beh : Behaviors.program_behavior,
       Behaviors.program_behaves (Mach.semantics p) beh ->
       forall t : Events.trace,
         Behaviors.behavior_prefix t beh ->
         trace_bound external_event_needs 
                                (Mach2Mach2.stacksizes p) t <= Integers.Int.unsigned bound)
    tp (HTRANS: transf_mach_program p = OK tp),
               forward_simulation (Prune.prune_semantics (Mach.semantics p)) (Asm.semantics bound tp)
                                  * backward_simulation (Prune.prune_semantics (Mach.semantics p)) (Asm.semantics bound tp).
Proof.
  intros.
  assert (forward_simulation (prune_semantics (Mach.semantics p)) (Asm.semantics bound tp)).
  revert HTRANS; unfold transf_mach_program; simpl.
  caseEq (Mach2Mach2.transf_program p); simpl; try congruence; intros p0 EQ0.  
  intros EQ1.
  generalize (Mach2Mach2.transf_program_correct _ (Asmgenproof.return_address_exists) _ Hbound external_event_needs _ NO_OVERFLOW _ EQ0).
  intro.
  generalize (forward_simulation_prune _ _ X).
  clear X.
  intro.
  generalize (Asmgenproof.transf_program_correct _ _ EQ1 bound external_event_needs).
  intro.
  eapply compose_forward_simulation. eassumption. assumption.
  
  split. auto. 
  apply forward_to_backward_simulation.
  assumption.
  apply receptive_prune.
  apply Mach.semantics_receptive.
  apply Asm.semantics_determinate.
Qed.

(** The following definition expresses that the source program does
    not "stack overflow".

    To compute the weights of the traces of the source [p] program, we
    instantiate the stack metric with the sizes of the stack frames
    obtained by the [transf] transformation of [p] to a [Mach] program
    [p'] and adjusted by the [Mach]-to-[Mach2] pass
    ([Mach2Mach2.stacksizes]).

    Then, the condition below imposes that those weights must not
    exceed [bound].  
*)

Definition no_overflow_with_mach {P: Type} sem transf (p: P) :=
  forall p', transf p = OK p' -> no_overflow external_event_needs (Mach2Mach2.stacksizes p') bound (sem p).

Theorem transf_mach_program_correct_weak:
  forall p
    (NOT_STUCK: not_stuck (prune_semantics (Mach.semantics p)))
    (NO_OVERFLOW: no_overflow_with_mach Mach.semantics (@OK _) p)
    tp (HTRANS: transf_mach_program p = OK tp),
               forward_simulation (Prune.prune_semantics (Mach.semantics p)) (Asm.semantics bound tp)
                                  * backward_simulation (Prune.prune_semantics (Mach.semantics p)) (Asm.semantics bound tp).
Proof.
  intros. eapply transf_mach_program_correct_strong.
  intros. eapply NO_OVERFLOW. reflexivity. eassumption.
  eapply prune_not_stuck. eassumption. assumption.
  assumption.
  assumption.
Qed.

(** Then, we show that, for any [Csem] / [Clight] / [Clight2] / [RTL]
   source program which *does not go wrong*, and such that its source
   traces do not stack overflow with the [Mach2] stack metric, then
   the compiled [Asm] program refines the source program and is
   guaranteed to not stack overflow.

   As explained in Section 3.2, it is important that the source
  program be proved to not go wrong in the unbounded-stack setting
  (condition [NOT_STUCK]. Indeed, our transformation uses the
  [transf_mach_program_correct_strong] theorem above, which depends on
  *all* traces of the [Mach] program obtained during the compilation
  of a source. If the source program were to have a wrong behavior
  [Goes_wrong t], then the compiled [Mach] program would well have a
  behavior [behavior_app t b] whose weight could well exceed [bound],
  thus violating the [NO_OVERFLOW] condition above. As each pass is
  proved independently of the others, it is not possible to track
  those behaviors of the [Mach] program that correspond to
  [Goes_wrong] behaviors of the source.
*)

Theorem transf_rtl_program_correct:
  forall p         
         (NOT_STUCK: not_stuck (prune_semantics (RTL.semantics p)))
         (NO_OVERFLOW: no_overflow_with_mach RTL.semantics transf_rtl_to_mach p)
         tp (HTRANS: transf_rtl_program p = OK tp),
               forward_simulation (Prune.prune_semantics (RTL.semantics p)) (Asm.semantics bound tp)
                                  * backward_simulation (Prune.prune_semantics (RTL.semantics p)) (Asm.semantics bound tp).
Proof.
  intros until tp.
  unfold transf_rtl_program.
  case_eq (transf_rtl_to_mach p); try discriminate.
  simpl. intros.
  destruct (transf_rtl_to_mach_correct _ _ H).
  generalize (forward_simulation_prune _ _ f).
  intro.
  refine (_ (transf_mach_program_correct_weak _ _ _ _ HTRANS)).
  destruct 1.
  generalize (compose_forward_simulation X f0).
  intro.
  split; auto.
  eapply forward_to_backward_simulation.
  eassumption.
  apply receptive_prune.
  apply RTL.semantics_receptive.
  apply Asm.semantics_determinate.
  apply not_stuck_prune.
  eapply not_stuck_backward. eassumption. apply prune_not_stuck. assumption.  
  intro. intro. inv H0. red. intros. eapply NO_OVERFLOW. assumption. eapply Behaviors.backward_simulation_same_safe_behavior. eassumption. apply prune_not_stuck. assumption. eassumption. assumption. assumption.
Qed.

Theorem transf_cminor_program_correct:
  forall p         
         (NOT_STUCK: not_stuck (prune_semantics (Cminor.semantics p)))
         (NO_OVERFLOW: no_overflow_with_mach Cminor.semantics transf_cminor_to_mach p)
         tp (HTRANS: transf_cminor_program p = OK tp),
               forward_simulation (Prune.prune_semantics (Cminor.semantics p)) (Asm.semantics bound tp)
                                  * backward_simulation (Prune.prune_semantics (Cminor.semantics p)) (Asm.semantics bound tp).
Proof.
  intros until tp.
  unfold transf_cminor_program.
  case_eq (transf_cminor_to_mach p); try discriminate.
  simpl. intros.
  destruct (transf_cminor_to_mach_correct _ _ H).
  generalize (forward_simulation_prune _ _ f).
  intro.
  refine (_ (transf_mach_program_correct_weak _ _ _ _ HTRANS)).
  destruct 1.
  generalize (compose_forward_simulation X f0).
  intro.
  split; auto.
  eapply forward_to_backward_simulation.
  eassumption.
  apply receptive_prune.
  apply Cminor.semantics_receptive.
  apply Asm.semantics_determinate.
  apply not_stuck_prune.
  eapply not_stuck_backward. eassumption. apply prune_not_stuck. assumption.  
  intro. intro. inv H0. red. intros. eapply NO_OVERFLOW. assumption.   eapply Behaviors.backward_simulation_same_safe_behavior. eassumption. apply prune_not_stuck. assumption. eassumption. assumption. assumption.
Qed.  

Theorem transf_clight2_program_correct:
  forall p         
         (NOT_STUCK: not_stuck (prune_semantics (Clight.semantics2 p)))
         (NO_OVERFLOW: no_overflow_with_mach Clight.semantics2 transf_clight2_to_mach p)
         tp (HTRANS: transf_clight2_program p = OK tp),
               forward_simulation (Prune.prune_semantics (Clight.semantics2 p)) (Asm.semantics bound tp)
                                  * backward_simulation (Prune.prune_semantics (Clight.semantics2 p)) (Asm.semantics bound tp).
Proof.
  intros until tp.
  unfold transf_clight2_program.
  case_eq (transf_clight2_to_mach p); try discriminate.
  simpl. intros.
  destruct (transf_clight2_to_mach_correct _ _ H).
  generalize (forward_simulation_prune _ _ f).
  intro.
  refine (_ (transf_mach_program_correct_weak _ _ _ _ HTRANS)).
  destruct 1.
  generalize (compose_forward_simulation X f0).
  intro.
  split; auto.
  eapply forward_to_backward_simulation.
  eassumption.
  apply receptive_prune.
  apply Clight.semantics2_receptive.
  apply Asm.semantics_determinate.
  apply not_stuck_prune.
  eapply not_stuck_backward. eassumption. apply prune_not_stuck. assumption.  
  intro. intro. inv H0. red. intros. eapply NO_OVERFLOW. assumption.   eapply Behaviors.backward_simulation_same_safe_behavior. eassumption. apply prune_not_stuck. assumption. eassumption. assumption. assumption.
Qed.

Theorem transf_clight_program_correct:
  forall p         
         (NOT_STUCK: not_stuck (prune_semantics (Clight.semantics1 p)))
         (NO_OVERFLOW: no_overflow_with_mach Clight.semantics1 transf_clight_to_mach p)
         tp (HTRANS: transf_clight_program p = OK tp),
               forward_simulation (Prune.prune_semantics (Clight.semantics1 p)) (Asm.semantics bound tp)
                                  * backward_simulation (Prune.prune_semantics (Clight.semantics1 p)) (Asm.semantics bound tp).
Proof.
  intros until tp.
  unfold transf_clight_program.
  case_eq (transf_clight_to_mach p); try discriminate.
  simpl. intros.
  destruct (transf_clight_to_mach_correct _ _ H).
  generalize (forward_simulation_prune _ _ f).
  intro.
  refine (_ (transf_mach_program_correct_weak _ _ _ _ HTRANS)).
  destruct 1.
  generalize (compose_forward_simulation X f0).
  intro.
  split; auto.
  eapply forward_to_backward_simulation.
  eassumption.
  apply receptive_prune.
  apply Clight.semantics_receptive.
  apply Asm.semantics_determinate.
  apply not_stuck_prune.
  eapply not_stuck_backward. eassumption. apply prune_not_stuck. assumption.  
  intro. intro. inv H0. red. intros. eapply NO_OVERFLOW. assumption.   eapply Behaviors.backward_simulation_same_safe_behavior. eassumption. apply prune_not_stuck. assumption. eassumption. assumption. assumption.
Qed.

Theorem transf_cstrategy_program_correct:
  forall p         
         (NOT_STUCK: not_stuck (prune_semantics (atomic (Cstrategy.semantics p))))
         (NO_OVERFLOW: no_overflow_with_mach (fun p' => atomic (Cstrategy.semantics p')) transf_c_to_mach p)
         tp (HTRANS: transf_c_program p = OK tp),
               forward_simulation (Prune.prune_semantics (atomic (Cstrategy.semantics p))) (Asm.semantics bound tp)
                                  * backward_simulation (Prune.prune_semantics (atomic (Cstrategy.semantics p))) (Asm.semantics bound tp).
Proof.
  intros until tp.
  unfold transf_c_program.
  case_eq (transf_c_to_mach p); try discriminate.
  simpl. intros.
  destruct (transf_cstrategy_to_mach_correct _ _ H).
  refine (_ (factor_forward_simulation f _)).
  clear f.
  intro f.
  generalize (forward_simulation_prune _ _ f).
  intro.
  refine (_ (transf_mach_program_correct_weak _ _ _ _ HTRANS)).
  destruct 1.
  generalize (compose_forward_simulation X f0).
  intro.
  split; auto.
  eapply forward_to_backward_simulation.
  eassumption.
  apply receptive_prune.
  apply atomic_receptive. apply Cstrategy.semantics_strongly_receptive.
  apply Asm.semantics_determinate.
  apply not_stuck_prune.
  eapply not_stuck_backward. eassumption. apply prune_not_stuck. assumption.  
  intro. intro. inv H0. red. intros. eapply NO_OVERFLOW. assumption.   eapply Behaviors.backward_simulation_same_safe_behavior. eassumption. apply prune_not_stuck. assumption. eassumption. assumption. assumption.
  apply sd_traces.  apply Mach.semantics_determinate.
Qed.

Theorem transf_c_program_correct:
  forall p         
         (NOT_STUCK: not_stuck (prune_semantics  (Csem.semantics p)))
         (NO_OVERFLOW: no_overflow_with_mach (Csem.semantics) transf_c_to_mach p)
         tp (HTRANS: transf_c_program p = OK tp),
    backward_simulation (Prune.prune_semantics (Csem.semantics p)) (Asm.semantics bound tp).
Proof.
  intros. 
  assert (backward_simulation (Csem.semantics p) (atomic (Cstrategy.semantics p))).
   apply factor_backward_simulation. 
   apply Cstrategy.strategy_simulation.
   apply Csem.semantics_single_events. 
   eapply ssr_well_behaved; eapply Cstrategy.semantics_strongly_receptive.   
  apply compose_backward_simulation with (prune_semantics (atomic (Cstrategy.semantics p))).  
  eapply sd_traces; eapply Asm.semantics_determinate.
  apply backward_simulation_prune.
  assumption.
  eapply transf_cstrategy_program_correct.
  apply not_stuck_prune.
  eapply not_stuck_backward.
  eassumption.
  apply prune_not_stuck.
  assumption.
  intro. red. intros. eapply NO_OVERFLOW. assumption. eapply Behaviors.backward_simulation_same_safe_behavior. eassumption. apply prune_not_stuck. assumption. eassumption. assumption. assumption.
  assumption.
Qed.

End Bound.

