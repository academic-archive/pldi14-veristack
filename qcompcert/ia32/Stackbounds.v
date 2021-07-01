Require Import Coqlib.
Require Import Events.
Require Import Behaviors.
Require Import Maps.
Require Import Globalenvs.
Require Import Memtype.
Require Import Smallstep.
Require Import Integers.

Section Sum.

Context  {A: Type} (f: A -> Z).

Function sum (l: list A): Z :=
  match l with
    | nil => 0
    | a :: q => f a + sum q
  end.

Function sum_tailrec (accu: Z) (l: list A): Z :=
  match l with
    | nil => accu
    | a :: q => sum_tailrec (accu + f a) q
  end.

Lemma sum_app: forall l1 l2, sum (l1 ++ l2) = sum l1 + sum l2.
Proof.
  induction l1; simpl. reflexivity. intros. rewrite IHl1. omega.
Qed.

Lemma sum_tailrec_correct_aux:
  forall l2 l1,
    sum (l1 ++ l2) = sum_tailrec (sum l1) l2.
Proof.
  induction l2; simpl.
   intro. rewrite <- app_nil_end. reflexivity.
  intro. replace (l1 ++ a :: l2) with ((l1 ++ a :: nil) ++ l2). rewrite IHl2. rewrite sum_app. simpl. f_equal. omega.
  rewrite app_ass. reflexivity.
Qed.

Lemma sum_tailrec_correct:
  forall l,
    sum l = sum_tailrec 0 l.
Proof.
  intro. rewrite <- sum_tailrec_correct_aux with (l1 := nil). reflexivity.
Qed.

End Sum.

Section Event_needs_or_consumes.

Variable external_event_needs: event -> Z.

Function event_needs (e: event): Z :=
  match e with
    | Event_call f => 0
    | Event_return f => 0
    | _ => external_event_needs e
  end.

Definition trace_needs : forall (t: trace), Z := sum event_needs.

Variable stacksizes: PMap.t Z.

Function event_consumes (e: event): Z :=
  match e with
    | Event_call f => PMap.get f stacksizes
    | Event_return f => - PMap.get f stacksizes
    | _ => 0
  end.

Definition trace_consumes := sum event_consumes.

Definition event_needs_or_consumes (e: event): Z := event_needs e + event_consumes e.

Definition trace_needs_or_consumes := sum event_needs_or_consumes.

Lemma external_call_consumes: forall {F V: Type} (ge: Genv.t F V) ef args m t v m',
                                 external_call ef ge args m t v m' ->
                                 trace_consumes t = 0.
Proof with (subst; simpl; try reflexivity).
  destruct ef; simpl; inversion 1...
  inversion H0...
  inversion H0...
  inversion H1...
  inversion H1...
Qed.

Lemma external_call_needs: forall {F V: Type} (ge: Genv.t F V) ef args m t v m',
                                 external_call ef ge args m t v m' ->
                                 trace_needs_or_consumes t = trace_needs t.
Proof with (subst; simpl; unfold event_needs_or_consumes; simpl; try omega).
  destruct ef; simpl; inversion 1...
  inversion H0...
  inversion H0...
  inversion H1...
  inversion H1...
Qed.

Function trace_bound_and_consumes (needs_consumes: Z*Z) (t: trace): Z*Z :=
  match t with
    | nil => needs_consumes
    | e :: q =>
      match needs_consumes with
        | (needs, consumes) =>
            trace_bound_and_consumes (Z.max needs (consumes + event_needs_or_consumes e), consumes + event_consumes e) q
      end
  end.

Definition trace_bound (t: trace): Z := 
  fst (trace_bound_and_consumes (0, 0) t).

Lemma trace_bound_pos_aux:
  forall t needs consumes,
    needs <= fst (trace_bound_and_consumes (needs, consumes) t).
Proof.
  induction t; simpl.
   intros; omega.
  intros. eapply Z.le_trans. 2: eapply IHt. eapply Z.le_max_l.
Qed.

Corollary trace_bound_pos: forall t, 0 <= trace_bound t.
Proof.
  intros; eapply trace_bound_pos_aux.
Qed.

Lemma trace_bound_and_consumes_correct_aux:
  forall t needs consumes,
   snd (trace_bound_and_consumes (needs, consumes) t) = sum_tailrec event_consumes consumes t.
Proof.
  induction t; simpl.
  reflexivity.
 intros. rewrite IHt. reflexivity.
Qed.

Lemma trace_bound_and_consumes_correct: 
  forall t,
    snd (trace_bound_and_consumes (0, 0) t) = trace_consumes t.
Proof.
  intros. unfold trace_consumes. rewrite sum_tailrec_correct. eauto using trace_bound_and_consumes_correct_aux.
Qed.

Lemma trace_bound_and_consumes_tailrec:
  forall l1 l2 accu,
    trace_bound_and_consumes accu (l1 ++ l2) =
    trace_bound_and_consumes (trace_bound_and_consumes accu l1) l2.
Proof.
  induction l1; simpl.
   reflexivity.
  intros.
  destruct accu.
  auto.
Qed.

Lemma trace_bound_single_event_needs_or_consumes':
  forall l e,
    trace_consumes l + event_needs_or_consumes e <= trace_bound (l ++ e :: nil).
Proof.
  intros. unfold trace_bound. rewrite trace_bound_and_consumes_tailrec. simpl.
  case_eq (trace_bound_and_consumes (0,0) l).
  intros.
  assert (z0 = snd (trace_bound_and_consumes (0,0) l)).
   rewrite H. reflexivity.
  clear H.
  subst.
  rewrite trace_bound_and_consumes_correct.
  simpl. apply Z.le_max_r.
Qed.

Lemma event_needs_or_consumes_eq: forall e,
                                    (event_needs_or_consumes e = event_needs e /\ event_consumes e = 0) \/ (event_needs_or_consumes e = event_consumes e /\ event_needs e = 0) .
Proof.
  unfold event_needs_or_consumes; destruct e; simpl; omega.
Qed.

Lemma trace_bound_ge_consumes_aux: forall t needs consumes,
                                 consumes <= needs ->
                                 snd (trace_bound_and_consumes (needs, consumes) t) <= fst (trace_bound_and_consumes (needs, consumes) t).
Proof.
  induction t; simpl.
   tauto.
  intros.
  eapply IHt.
  destruct (event_needs_or_consumes_eq a).
   destruct H0.
   rewrite H0. 
   rewrite H1.
   eapply Z.le_trans.
   2: eapply Z.le_max_l.
   omega.
  destruct H0.
  rewrite H0.
  apply Z.le_max_r.
Qed.

Corollary trace_bound_ge_consumes: forall t,
                                     trace_consumes t <= trace_bound t.
Proof.
  intros. rewrite <- trace_bound_and_consumes_correct. eapply trace_bound_ge_consumes_aux. omega.
Qed.

Lemma trace_bound_single_event_needs_or_consumes:
  forall l', (length l' <= 1)%nat -> forall l,
    trace_consumes l + trace_needs_or_consumes l' <= trace_bound (l ++ l').
Proof.
  intros. destruct l'.
   rewrite <- app_nil_end. simpl. generalize (trace_bound_ge_consumes l). omega.
  destruct l'.
   simpl. generalize (trace_bound_single_event_needs_or_consumes' l e). omega.
  exfalso; simpl in *; omega.
Qed.

Theorem trace_bound_cons_right:
  forall l a,
    trace_bound (l ++ a :: nil) = Z.max (trace_bound l) (trace_consumes l + event_needs_or_consumes a).
Proof.
  unfold trace_bound. intros.
  rewrite trace_bound_and_consumes_tailrec.
  simpl.
  case_eq (trace_bound_and_consumes (0,0) l).
  intros.
  simpl.
  rewrite <- trace_bound_and_consumes_correct.
  rewrite H.
  reflexivity.
Qed.

Theorem trace_bound_app:
  forall l' l,
    trace_bound l <= trace_bound (l ++ l').
Proof.
  induction l' using rev_ind.
   intro. rewrite <- app_nil_end. omega.
  intro. eapply Z.le_trans. eauto. rewrite <- app_ass. rewrite trace_bound_cons_right. apply Z.le_max_l.
Qed.

Corollary trace_consumes_prefix_le_bound:
  forall l l',
    trace_consumes l <= trace_bound (l ++ l').
Proof.
  intros. eapply Z.le_trans. eapply trace_bound_ge_consumes. eapply trace_bound_app.
Qed.

Definition no_overflow bound (sem: semantics) :=
  forall beh : program_behavior,
       program_behaves sem beh ->
       not_wrong beh ->
       forall t : Events.trace,
         behavior_prefix t beh ->
         trace_bound t <= Integers.Int.unsigned bound.

End Event_needs_or_consumes.

(* Special case where external functions need zero space *)

Section NoExt.

Variable stacksizes: PMap.t Z.

Theorem trace_bound_no_external_cons_right:
  forall l a,
    trace_bound (fun _ => 0) stacksizes (l ++ a :: nil) = Z.max (trace_bound (fun _ => 0) stacksizes l) (trace_consumes stacksizes (l ++ a :: nil)). 
Proof.
  intros.
  rewrite trace_bound_cons_right.
  f_equal.
  unfold trace_consumes.
  rewrite sum_app.
  f_equal.
  simpl.
  unfold event_needs_or_consumes.
  unfold event_needs.
  destruct a; omega.
Qed.

Theorem trace_bound_no_external_reached: forall l, exists l1, exists l2, l = l1 ++ l2 /\ trace_bound (fun _ => 0) stacksizes l = trace_consumes stacksizes l1.
Proof.
  induction l using rev_ind.
   exists nil. exists nil. split; reflexivity.
  rewrite trace_bound_no_external_cons_right.
  rewrite Zmax_spec.
  destruct (zlt (trace_consumes stacksizes (l ++ x :: nil)) (trace_bound (fun _ => 0) stacksizes l)).
   destruct IHl. destruct H. destruct H. subst. rewrite H0. exists x0. exists (x1 ++ x :: nil). split; auto. rewrite app_ass. reflexivity.
  exists (l ++ x :: nil). exists nil. split; auto. rewrite <- app_nil_end. reflexivity.
Qed.

Corollary trace_bound_no_external_principle:
  forall l z,
    (forall l1 l2, l = l1 ++ l2 -> trace_consumes stacksizes l1 <= z) <->
    trace_bound (fun _ => 0) stacksizes l <= z.
Proof.
  split.
   intros. generalize (trace_bound_no_external_reached l). destruct 1 as [l1 [l2 [? EQ]]]. rewrite EQ. subst. eauto.
  intros; subst. eapply Z.le_trans. eapply trace_consumes_prefix_le_bound. eassumption.
Qed.

Theorem no_overflow_single_events:
  forall
    sem (SINGLE: single_events sem)
    bound
    (NO_OVERFLOW: forall s, initial_state sem s ->
                            forall t s', Star sem s t s' -> trace_consumes stacksizes t <= Int.unsigned bound),
    no_overflow (fun _ => 0) stacksizes bound sem.
Proof.
  intros. red. inversion 1; subst; try contradiction.
  intros.
  exploit behaviors_single_events_prefix_inv.
   eassumption. eassumption. eassumption.
  destruct 1 as [? [? [? [? ?]]]]; subst.
  apply trace_bound_no_external_principle.
  intros; subst.
  exploit star_single_events_app_inv.
   eassumption. eassumption. reflexivity.
  destruct 1 as [? [? ?]].
  eauto.
Qed.

End NoExt.   
