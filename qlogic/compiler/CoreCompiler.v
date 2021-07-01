(************************************************************************)
(*                                                                      *)
(*                Quantitative Hoare Logic for Clight                   *)
(*                                                                      *)
(*  Author: Quentin Carbonneaux (c) 2014              Yale University   *)
(*                                                                      *)
(************************************************************************)


(* This file defines a compiler for complete
   Cxlight programs.

   The 'trans_program' function defined here
   will compile a complete program down to
   assembly and, if the compilation succeeds,
   provide you with a stack usage bound on
   every function of the input program!
   It makes use of the automatic program
   analysis defined in 'auto.v' to infer
   the bound.
*)
Add LoadPath "..".

(* Libraries *)
Require Import Coqlib.
Require Import Errors.
Require Import Integers.
Require Import List.
Require Import Maps.
Require Import PArith.

(* Quantitative Compcert compiler *)
Require Import AST.
Require Import Behaviors.
Require Import Stackbounds.
Require Import Compiler.
Require Import Globalenvs.
Require Import Memtype.
Require Import Smallstep.

(* Quantitative layer (defined in this repository) *)
Require Import Logic.
Require Import Cx2C.
Require Import AutoBound.

Open Scope Z.
Open Scope error_monad_scope.


(* Transform a Cxlight program (defined in Cxlight.v)
   into a triple containing an assembly program, a map
   which associates a resource bound to each function
   defined in the program and a bound on the maximal
   stack consumption of the overall program.

   The input program must be closed, and its call graph
   well founded, if one of those two conditions is not
   met an error is returned.
*)
Definition trans_program (p: Cxlight.program) :=
  (* Check uniqueness of function definitions. *)
  if check_norepet (prog_defs_names p) then
  (* Check closedness of the program. *)
  if check_closed (prog_defs p) then
  (* Check that the call graph is well founded. *)
  if check_cg_wellfounded (prog_defs p) then

  (* Compile! *)
  match Cx2C.transf_cxlight_to_mach p with
  | OK pmach =>
     let F f := PMap.get f (Mach2Mach2.stacksizes pmach) in
     let B f := liftO Z.add (Some (F f)) (bound_of F p f) in
     do pasm <- transf_mach_program pmach;
     match B p.(prog_main) with
     | Some b =>
         let bmain := align (b + 4) Stacklayout.strong_align - 4 in
         if zle bmain Int.max_unsigned
           then OK (pasm, B, Some (Int.repr bmain))
           else Error (msg "main will stack overflow")
     | None => OK (pasm, B, None)
     end
  | Error e => Error e
  end

  else Error (msg "call graph is not well founded")
  else Error (msg "not a closed program")
  else Error (msg "multiple definitions").


Require Import Cxlight.

Lemma star_running_main:
  forall p S t S' (STAR: Star (Cxlight.semantics p) S t S')
         main s k c main' s' k' c'
         (HS: S = Running main s k c)
         (HS': S' = Running main' s' k' c'),
  main = main'.
Proof.
induction 1; intros; try congruence.
subst. inv H.
eauto. inv STAR. inv H.
Qed.


Lemma star_many:
  forall p S t S' (STAR: Star (Cxlight.semantics p) S t S')
         main s k c s' k' c'
         (HS: S = Running main s k c)
         (HS': S' = Running main s' k' c'),
  exists ct,
    t = trtrace ct /\ Logic.many (Core.step (Genv.globalenv p)) (s, k, c) ct (s', k', c').
Proof.
induction 1; intros.
exists nil.
split. reflexivity.
subst. inv HS'.
constructor.
subst.
inv H.
exploit IHSTAR; eauto.
clear IHSTAR.
destruct 1 as [ct [CT MANY]].
subst.
unfold Events.Eapp, trtrace.
rewrite <- map_app.
eexists (_ ++ _).
split; eauto.
econstructor; eassumption.
inv STAR. inv H.
Qed.

Lemma star_final:
  forall p S t S' (STAR: Star (Cxlight.semantics p) S t S')
         main s k c ret
         (HS: S = Running main s k c)
         (HS': S' = Final ret),
  exists ct s' k' c',
    t = trtrace ct ++ (Events.Event_return (fi_name main) :: nil) /\
    Logic.many (Core.step (Genv.globalenv p)) (s, k, c) ct (s', k', c').
Proof.
induction 1; intros.
exfalso; congruence.
subst.
inv H.
exploit IHSTAR; eauto.
destruct 1 as [ct [s' [k' [c' [CT MANY]]]]].
subst.
unfold Events.Eapp, trtrace.
rewrite <- app_ass.
rewrite <- map_app.
repeat esplit.
fold (Tapp t ct).
eapply many_step; eauto.
exists nil. simpl.
inv STAR.
unfold Events.E0 in *.
eauto using many_base.
inv H.
Qed.

Lemma star_initial:
  forall p S t S' (STAR: Star (Cxlight.semantics p) S t S')
         main m (INI: S' = Initial main m),
  S = S' /\ t = Events.E0.
Proof.
induction 1.
eauto.
intros.
exploit IHSTAR; eauto.
destruct 1; subst.
inv H.
Qed.

Lemma value_trace_consumes:
  forall stacksizes l,
  Logic.value (fun f => PMap.get f stacksizes) l = trace_consumes stacksizes (trtrace l).
Proof.
unfold trace_consumes.
simpl.
induction l; simpl; try reflexivity.
destruct a; simpl; eauto with zarith.
Qed.

(* dirty hack... *)
Inductive zle_ (a b: Z): Prop := zle__intro (LE: a <= b).

Lemma many_bound:
  forall
    (p : AST.program finfo Ctypes.type)
    (PROG_WF : forall (f : ident) (fi : finfo), find_finfo (Genv.globalenv p) f = Some fi -> fi_name fi = f)
    (F : PMap.t Z)
    (FNONNEG: forall f, 0 <= F !! f)
    (n : Z)
    (BOUNDOF : bound_of (fun f => PMap.get f F) p (prog_main p) = Some n)
    (main : finfo)
    (s : stm) (k : cont) (c : conf)
    m (INIT_MEM : Genv.init_mem p = Some m)
    (stk : stack)
    (MAIN : find_finfo (Genv.globalenv p) (prog_main p) = Some main)
    (INIT : fun_init (globalenv (semantics p)) (fi_name main) nil stk)
    (t : list event)
    (MANY : many (Core.step (Genv.globalenv p)) (fi_body main, kstop, cnf stk m) t (s, k, c)),
  zle_ (trace_consumes F (trtrace t)) n.
Proof.
intros. constructor.
rewrite <- value_trace_consumes.
eapply Logic.runs_sound; eauto.
intros.
assert (CONVN: n = Z.of_nat (Z.to_nat n)).
{ rewrite Z2Nat.id; auto.
  unfold bound_of in BOUNDOF.
  eapply bound_of_lvl_nonneg; eauto.
  simpl; assumption.
}
replace n with (Z.of_nat (Z.to_nat n)).
eapply (bound_lvl_sound (aux := unit)).
eauto.
3: eapply le_refl.
2: simpl; unfold find_func_.
2: instantiate (1 := prog_main p).
2: rewrite MAIN; now reflexivity.
unfold mkctx.
unfold bound_of in BOUNDOF.
instantiate (3 := (S (Pos.to_nat (prog_main p)))).
unfold fid,ident in BOUNDOF.
rewrite BOUNDOF; reflexivity.

apply Logic.safe_kstop.
unfold pls, fun_pre.
instantiate (2 := fun _ => O).
simpl.
simpl in INIT.
erewrite PROG_WF in INIT by eassumption.
exists (Z.to_nat n).
rewrite <- CONVN.
now eauto 6 with zarith.
Grab Existential Variables. constructor.
Qed.

Lemma align_le_with_rem:
  forall n d r, d > 0 -> n <= align (n + r) d - r.
Proof.
intros.
generalize (align_le (n + r) d H).
omega.
Qed.

Ltac t :=
  match goal with
  | [ H: (if ?test then _ else _) = OK _ |- _ ] =>
      let eq := fresh in
      case_eq test; intro eq; rewrite eq in H;
      simpl in *; try discriminate
  | [ H: match ?test with OK _ => _ | Error _ => _ end = OK _ |- _ ] =>
      let eq := fresh in
      case_eq test; intros ? eq; rewrite eq in H;
      simpl in H; try discriminate
  | [ H: match ?test with Some _ => _ | None => _ end = _ |- _ ] =>
      let eq := fresh in
      case_eq test; [ intros ? eq | intro eq ]; rewrite eq in H;
      simpl in H; try discriminate
  | [ H: (do _ <- ?x; _) = OK _ |- _ ] =>
      revert H; case_eq x; try discriminate; simpl; intros
  | [ H: (if ?test then _ else _) = OK _ |- _ ] => destruct test; try discriminate
  | [ H: OK _ = OK _ |- _ ] => inv H
  | [ H: Some _ = Some _ |- _ ] => inv H
  end.

Lemma compiler_no_overflow_Some:
  forall p (PROG_WF: forall f fi, find_finfo (Genv.globalenv p) f = Some fi -> fi.(fi_name) = f),
  forall pasm B bmain (HTRANS: trans_program p = OK (pasm, B, Some bmain)),
  no_overflow_with_mach bmain (fun _ => 0) Cxlight.semantics transf_cxlight_to_mach p.
Proof.
unfold trans_program; intros. repeat t.

unfold no_overflow_with_mach.
intros.
apply no_overflow_single_events.
now apply sr_traces, Cxlight.semantics_receptive.
intros. replace p0 with p' in * by congruence. clear p0.

assert (0 <= z0).
{ unfold bound_of in H5.
  eapply bound_of_lvl_nonneg; eauto.
  eapply Compiler.transf_mach_program_stacksizes_pos.
  eassumption.
}
assert (SSNONNEG: forall f, 0 <= (Mach2Mach2.stacksizes p') !! f)
 by eauto using Compiler.transf_mach_program_stacksizes_pos.
assert (MAINNONNEG: 0 <= (Mach2Mach2.stacksizes p') !! (prog_main p))
 by eauto.

rewrite Int.unsigned_repr.
eapply Z.le_trans;
  [| eapply align_le_with_rem;
     eauto using Stacklayout.strong_align_pos ].
inv H6. destruct s'.

{ (* s' is initial *)
  exploit star_initial; eauto.
  intros [? ?]; subst.
  simpl; omega.
}

{ (* s' is running *)
  inv H7.
  inv H6.
  exploit star_running_main; eauto.
  intros; subst.
  exploit star_many; eauto.
  destruct 1 as [? [? MANY]].
  subst.
  simpl.
  exploit many_bound; eauto.
  inversion 1.
  erewrite PROG_WF by eassumption.
  intros. eauto with zarith.
}

{ (* s' is final *)
  inv H7.
  inv H6.
  exploit star_final; eauto.
  destruct 1 as [ct [s' [k' [c' [? MANY]]]]]; subst.
  simpl.
  unfold trace_consumes.
  rewrite sum_app.
  fold (trace_consumes (Mach2Mach2.stacksizes p')).
  simpl.
  exploit many_bound; eauto.
  inversion 1.
  erewrite PROG_WF by eassumption.
  intros. eauto with zarith.
}

{ split; try omega.
  eapply Z.le_trans; [| apply align_le_with_rem].
  omega.
  eauto using Stacklayout.strong_align_pos.
}
Qed.

Theorem compiler_correctness_Some:
  forall p (PROG_WF: forall f fi, find_finfo (Genv.globalenv p) f = Some fi -> fi.(fi_name) = f),
  forall pasm B bmain (HTRANS: trans_program p = OK (pasm, B, Some bmain))
         (NOT_STUCK: not_stuck (Prune.prune_semantics (semantics p))),
    forward_simulation (Prune.prune_semantics (semantics p)) (Asm.semantics bmain pasm)
  * backward_simulation (Prune.prune_semantics (semantics p)) (Asm.semantics bmain pasm).
Proof.
intros. generalize HTRANS.
unfold trans_program in HTRANS. repeat t.

assert (SSNONNEG: forall f, 0 <= (Mach2Mach2.stacksizes p0) !! f)
 by eauto using Compiler.transf_mach_program_stacksizes_pos.
assert (MAINNONNEG: 0 <= (Mach2Mach2.stacksizes p0) !! (prog_main p))
 by eauto.
assert (Z0NONNEG: 0 <= z0).
{ unfold bound_of in H5.
  eapply bound_of_lvl_nonneg; eauto.
  eapply Compiler.transf_mach_program_stacksizes_pos.
  eassumption.
}

eapply transf_cxlight_program_correct; eauto.

rewrite Int.unsigned_repr.
simpl.
match goal with [ |- context [?a - ?b + ?b] ] =>
  replace (a - b + b) with a by omega end.
apply align_divides.
eauto using Stacklayout.strong_align_pos.

split; auto.
eapply Z.le_trans; [| apply align_le_with_rem].
omega.
eauto using Stacklayout.strong_align_pos.
eapply compiler_no_overflow_Some; eauto.

revert H2 H3; clear.
unfold transf_cxlight_program, transf_cxlight_to_mach.
unfold transf_clight2_program.
unfold apply_partial.
intros. t.
rewrite H2.
assumption.
Qed.
