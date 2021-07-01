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

(** Corollaries of the main semantic preservation theorem. *)

Require Import Classical.
Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Values.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Behaviors.
Require Import Csyntax.
Require Import Csem.
Require Import Cstrategy.
Require Import Clight.
Require Import Cminor.
Require Import RTL.
Require Import Asm.
Require Import Compiler.
Require Import Errors.
Require Import Prune.
Require Import Memdata.

(** We assume that the available stack size [bound] of the process in
    the target machine is machine-representable, and that the stack is
    strongly aligned. *)

Section WITHBOUNDS.
Context
  (bound : Integers.Int.int)
  (Hbound: (Stacklayout.strong_align
       | Integers.Int.unsigned bound + size_chunk Mint32))
  (external_event_needs: Events.event -> Z)
  (p: Csyntax.program) (tp: Asm.program)
  (H: transf_c_program p = OK tp)
.

(** * Preservation of whole-program behaviors *)

(** From the simulation diagrams proved in file [Compiler]. it follows that
  whole-program observable behaviors are preserved in the following sense.
  First, every behavior of the generated assembly code is matched by
  a behavior of the source C code. *)

Section CSTRATEGY.

(** If we consider the C evaluation strategy implemented by the
  compiler, we get stronger preservation results: the behaviors are
  exactly preserved. *)

Lemma prune_atomic_behaves_intro:
  forall beh, program_behaves (prune_semantics (Cstrategy.semantics p)) beh ->
              program_behaves (prune_semantics (atomic (Cstrategy.semantics p))) beh.
Proof.
  intros.
  destruct (prune_program_behaves _ _ H0).
  destruct H1.
  apply atomic_behaviors in H2.
  eapply program_behaves_prune.
  eassumption.
  assumption.
  intros. eapply ssr_well_behaved. apply Cstrategy.semantics_strongly_receptive.
Qed.

Lemma prune_atomic_behaves_elim:  
  forall beh, program_behaves (prune_semantics (atomic (Cstrategy.semantics p))) beh ->
              program_behaves (prune_semantics (Cstrategy.semantics p)) beh.
Proof.
  intros.
  destruct (prune_program_behaves _ _ H0).
  destruct H1.
  apply atomic_behaviors in H2.
  eapply program_behaves_prune.
  eassumption.
  assumption.
  intros. eapply ssr_well_behaved. apply Cstrategy.semantics_strongly_receptive.
Qed.  

(** We assume that:

    - the [Cstrategy] source program is proved not to go wrong

    - the traces of the source program do not "stack overflow". Let us
      explain this in more detail.  To compute the weights
      (cf. Section 3.1 of our PLDI 2014 paper) of the traces of the so
      program, we instantiate the stack metric with the sizes of the
      stack frames obtained in [Mach] and adjusted by the
      [Mach]-to-[Mach2] pass ([Mach2Mach2.stacksizes]). Then, the
      condition [NO_OVERFLOW] below imposes that those weights must
      not exceed [bound].
 *)

Variables
  (NOT_STUCK: not_stuck (prune_semantics (atomic (Cstrategy.semantics p))))
  (NO_OVERFLOW: no_overflow_with_mach bound external_event_needs (fun p' => atomic (Cstrategy.semantics p')) transf_c_to_mach p)
.

(** Under these conditions, the target [Asm] program is guaranteed to
    refine the [Cstrategy] source program -- and more precisely, the
    *pruned* behaviors (without call/return events) are exactly
    preserved.  In particular, the [Asm] program is guaranteed to not
    go wrong at all, and in particular, is guaranteed to not stack
    overflow.

    As explained in Section 3.2, it is important that the source
    program be proved to not go wrong in the unbounded-stack setting
    (condition [NOT_STUCK]. Indeed, our transformation uses the
    [Compiler.transf_mach_program_correct_strong] theorem, which
    depends on *all* traces of the [Mach] program obtained during the
    compilation of a source. If the source program were to have a
    wrong behavior [Goes_wrong t], then the compiled [Mach] program
    would well have a behavior [behavior_app t b] whose weight could
    well exceed [bound], thus violating the [NO_OVERFLOW] condition of
    that theorem. As each pass is proved independently of the others,
    it is not possible to track those behaviors of the [Mach] program
    that correspond to [Goes_wrong] behaviors of the source.
 *)

Theorem transf_cstrategy_program_preservation:
  (forall beh, program_behaves (prune_semantics (Cstrategy.semantics p)) beh <->
               program_behaves (Asm.semantics bound tp) beh).
Proof.
  split.
  intros.
  eapply forward_simulation_same_safe_behavior.
  eapply transf_cstrategy_program_correct.
  assumption.
  eassumption.
  eassumption.
  assumption.
  apply prune_atomic_behaves_intro.
  assumption.
  apply NOT_STUCK.
  apply prune_atomic_behaves_intro.
  assumption.
 intro.
 apply prune_atomic_behaves_elim.
 eapply backward_simulation_same_safe_behavior.
 eapply transf_cstrategy_program_correct.
 eassumption.
 assumption.
 eassumption.
 eassumption.
 assumption.
 assumption.
Qed.

End CSTRATEGY.

(** Similarly, if we assume that:

    - the [Csem] source program is proved not to go wrong

    - the traces of the source program do not "stack overflow". Let us
      explain this in more detail.  To compute the weights
      (cf. Section 3.1 of our PLDI 2014 paper) of the traces of the so
      program, we instantiate the stack metric with the sizes of the
      stack frames obtained in [Mach] and adjusted by the
      [Mach]-to-[Mach2] pass ([Mach2Mach2.stacksizes]). Then, the
      condition [NO_OVERFLOW] below imposes that those weights must
      not exceed [bound].
 *)

Variables
  (NOT_STUCK: not_stuck (prune_semantics  (Csem.semantics p)))
  (NO_OVERFLOW: no_overflow_with_mach bound external_event_needs (Csem.semantics) transf_c_to_mach p)
.


(** Then, under these conditions, the target [Asm] program is
    guaranteed to refine the [Csem] source program. In particular, the
    [Asm] program is guaranteed to not go wrong at all, and in
    particular, is guaranteed to not stack overflow.

    However, the [Asm] program may well have lost some behaviors of
    the [Csem] program, because all internal non-determinism of [Csem]
    (e.g. argument evaluation order) have been solved by
    [Cstrategy]. So we only have refinement, not exact behavior
    preservation. This is CompCert-specific, nothing to do with stack
    consumption.
*)

Theorem transf_c_program_preservation:
  forall beh,
  program_behaves (Asm.semantics bound tp) beh ->
  program_behaves (prune_semantics (Csem.semantics p)) beh.
Proof.
  intros. eapply backward_simulation_same_safe_behavior; eauto.
  eapply transf_c_program_correct; eauto.
Qed.

(** * Satisfaction of specifications *)

(** The second additional results shows that if all executions
  of the source C program satisfies a given specification
  (a predicate on the observable behavior of the program),
  then all executions of the produced Asm program satisfy
  this specification as well.  
 *)

Section SPECS_PRESERVED.

Variable spec: program_behavior -> Prop.

Theorem transf_c_program_preserves_spec:
  (forall beh, program_behaves (prune_semantics (Csem.semantics p)) beh -> spec beh) ->
  (forall beh, program_behaves (Asm.semantics bound tp) beh -> spec beh).
Proof.
  intros; eauto using transf_c_program_preservation.
Qed.

End SPECS_PRESERVED.

End WITHBOUNDS.
