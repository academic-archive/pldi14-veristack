Require Import Coqlib.
Require Import List.
Require Import Events.
Require Import Smallstep.
Require Import Behaviors.
Require Import Memtype.
Open Scope nat_scope.

Function prune_trace (t: trace): trace :=
  match t with
    | nil => nil
    | Event_call _ :: q => prune_trace q
    | Event_return _ :: q => prune_trace q
    | a :: q => a :: prune_trace q
  end.

Lemma prune_trace_idem: forall l, prune_trace (prune_trace l) = prune_trace l.
Proof.
  induction l; simpl.
   reflexivity.
  destruct a; simpl; congruence.
Qed.

Lemma prune_trace_not_E0: forall l, prune_trace l <> E0 -> l <> E0.
Proof.
  unfold E0. destruct l; simpl; congruence.
Qed.

Lemma prune_trace_not_E0': forall l2, l2 <> E0 -> forall l1, l2 = prune_trace l1 -> l1 <> E0.
Proof.
  unfold E0. destruct l1; simpl; congruence.
Qed.

Lemma prune_trace_app: forall t1 t2, prune_trace (t1 ** t2) = prune_trace t1 ** prune_trace t2.
Proof.
  induction t1; simpl. reflexivity.
  intros. rewrite IHt1. destruct a; reflexivity.
Qed.

Definition is_call_or_return e :=
  exists f, e = Event_call f \/ e = Event_return f.

Lemma prune_trace_cases: forall a l,
                           {is_call_or_return a /\ prune_trace (a :: l) = prune_trace l} + {(~ is_call_or_return a) /\ prune_trace (a :: l) = a :: prune_trace l}.
Proof.
  destruct a; unfold is_call_or_return; simpl; eauto; right; split; auto; intros [? [? | ?]]; discriminate.
Qed.

Inductive prune_traceinf_head : traceinf -> traceinf -> Prop :=
| prune_traceinf_head_call_return
    e (He: is_call_or_return e) t1 t2 (Ht: prune_traceinf_head t1 t2)
  : prune_traceinf_head (Econsinf e t1) t2
| prune_traceinf_head_normal
    e (He: ~ is_call_or_return e)
    t
  : prune_traceinf_head (Econsinf e t) (Econsinf e t)
.

Lemma prune_traceinf_head_inj: forall t t1, prune_traceinf_head t t1 ->
                                            forall t2, prune_traceinf_head t t2 ->
                                                       t1 = t2.
Proof.
  induction 1; inversion 1; subst; eauto; contradiction.
Qed.

Lemma prune_traceinf_head_sim_ex:
  forall t1 t'1,
    prune_traceinf_head t1 t'1 ->
    forall t2, traceinf_sim t1 t2 ->
               exists t'2, prune_traceinf_head t2 t'2.
Proof.
  induction 1; inversion 1; subst.
   exploit IHprune_traceinf_head. eassumption. destruct 1. esplit; eleft; eauto.
  esplit. eright. assumption.
Qed.

Lemma prune_traceinf_head_sim_inj:
  forall t1 t'1,
    prune_traceinf_head t1 t'1 ->
    forall t2, traceinf_sim t1 t2 ->
               forall t'2, prune_traceinf_head t2 t'2 ->
                           traceinf_sim t'1 t'2.
Proof.
  induction 1; inversion 1; subst; inversion 1; subst; eauto; contradiction.
Qed.

Lemma prune_traceinf_head_sim_surj:
  forall t1 t'1,
    prune_traceinf_head t1 t'1 ->
    forall t'2, traceinf_sim t'1 t'2 ->
                exists t2, prune_traceinf_head t2 t'2 /\ traceinf_sim t1 t2.
Proof.
  induction 1.
   intros. exploit IHprune_traceinf_head. eassumption. destruct 1. destruct H1.
   esplit. split. 2: econstructor. 2: eassumption. eleft. assumption. assumption.
  inversion 1; subst. esplit. split. eright. assumption. assumption.
Qed.

Lemma prune_traceinf_head_no_call_return:
  forall t t', prune_traceinf_head t t' -> forall t'' e, t' = (Econsinf e t'') -> ~ is_call_or_return e.
Proof.
  induction 1; intros; subst.
   eauto.
  congruence.
Qed.

Lemma prune_traceinf_head_inv:
  forall t1 t2,
    prune_traceinf_head t1 t2 ->
    exists t, t1 = t *** t2 /\ prune_trace t = E0.
Proof.
  induction 1.
   destruct IHprune_traceinf_head. destruct H0. subst.
   exists (e :: x). split. reflexivity. 
   destruct (prune_trace_cases e x).
    destruct a. congruence.
   destruct a. contradiction.
  exists nil. split; reflexivity.
Qed.

CoInductive all_call_return: traceinf -> Prop :=
| all_call_return_call t (Ht: all_call_return t) f:
    all_call_return (Econsinf (Event_call f) t)
| all_call_return_return t (Ht: all_call_return t) f:
    all_call_return (Econsinf (Event_return f) t)
.

Lemma all_call_return_sim: forall t1, all_call_return t1 -> forall t2, traceinf_sim t1 t2 -> all_call_return t2.
Proof.
  cofix; inversion 1; subst; inversion 1; subst; econstructor; eauto.
Qed.


Lemma all_call_return_app: forall t, all_call_return t -> forall l, prune_trace l = nil -> all_call_return (Eappinf l t).
Proof.
  intros. revert H0 t H. induction l; simpl in *.
   tauto.
  intros.
  destruct a; try discriminate;  econstructor; eauto.
Qed.

Lemma all_call_return_app_recip_l: forall l t, all_call_return (Eappinf l t) -> prune_trace l = nil.
Proof.
  induction l; simpl.
   tauto.
  inversion 1; subst; eauto.
Qed.

Lemma all_call_return_app_recip_r: forall l t, all_call_return (Eappinf l t) -> all_call_return t.
Proof.
  induction l; simpl.
   tauto.
  inversion 1; subst; eauto.
Qed.

Lemma all_call_return_cons_recip_l: forall e t, all_call_return (Econsinf e t) -> is_call_or_return e.
Proof.
  inversion 1; subst; esplit; eauto.
Qed.

Lemma all_call_return_cons_recip_r: forall e t, all_call_return (Econsinf e t) -> all_call_return t.
Proof.
  inversion 1; eauto.
Qed.

CoInductive all_call_return': traceinf -> Prop :=
| all_call_return'_intro t (Ht: t <> E0) (Hprune: prune_trace t = E0) T' (HT': all_call_return' T') T (HT: T = t *** T') :
  all_call_return' T.

Lemma all_call_return'_ex:
  forall t (Ht: t <> E0) (Hprune: prune_trace t = E0) T' (HT': all_call_return' T'),
  exists e,  exists T,
                is_call_or_return e /\
                all_call_return' T /\
                Econsinf e T = t *** T'.
Proof.
  induction t.
   destruct 1. reflexivity.
  intros _.
  intros.
  destruct (prune_trace_cases a t).
   destruct a0. rewrite H0 in Hprune.
   destruct t.
    clear IHt.
    esplit. esplit. split.
    eassumption.
    split. eassumption. reflexivity.
   exploit IHt. discriminate. assumption. eassumption.
   destruct 1. destruct H1. destruct H1. destruct H2.
  esplit. esplit. split.
  eexact H.
  split.
  econstructor. 3: eexact H2. 4: instantiate (1 := (e :: t) *** T'). 4: reflexivity. 2: instantiate (1 := (x :: nil)). discriminate. 2: simpl; rewrite H3; reflexivity. simpl.
  destruct x; auto; destruct H1; destruct H1; discriminate.
 destruct a0. rewrite Hprune in *. discriminate.
Qed.

Lemma all_call_return'_all_call_return: forall T,
                                  all_call_return' T ->
                                  all_call_return  T.
Proof.
  cofix COINDHYP.
  destruct 1.
  destruct (all_call_return'_ex _ Ht Hprune _ H).
  destruct H0.
  destruct H0.
  destruct H1.
  subst.
  rewrite <- H2.
  destruct H0.
  destruct H0; subst; econstructor; eauto.
Qed.
  
Lemma no_prune_traceinf_head_all_call_return:
  forall t, (forall t', ~ prune_traceinf_head t t') ->
            all_call_return t.
Proof.
  cofix COINDHYP.
  destruct t. destruct e; try (
   edestruct 1; eright; intros [? ABS]; destruct ABS; discriminate
                            ).
  left. eapply COINDHYP; clear COINDHYP. intros. intro. edestruct H. eleft; eauto; esplit; eauto.
  right. eapply COINDHYP; clear COINDHYP. intros. intro. edestruct H. eleft; eauto; esplit; eauto.
Qed.

Lemma all_call_return_no_prune_traceinf_head: 
  forall t,
    all_call_return t ->
    forall t', ~ prune_traceinf_head t t'.
Proof.
  intros. intro. revert H. induction H0.
   inversion 1; subst; eauto.
  inversion 1; subst;  destruct He; esplit; eauto.
Qed. 

Inductive prune_traceinf_finite : traceinf -> trace -> Prop :=
| prune_traceinf_finite_nil t (Ht: all_call_return t):
    prune_traceinf_finite t nil
| prune_traceinf_finite_cons_call_return e (He: is_call_or_return e) tf t (Htf: prune_traceinf_finite tf t):
    prune_traceinf_finite (Econsinf e tf) t
| prune_traceinf_finite_cons_normal e (He: ~ is_call_or_return e) tf t (Htf: prune_traceinf_finite tf t)
:
  prune_traceinf_finite (Econsinf e tf) (e :: t)
.

Lemma prune_traceinf_finite_idem: forall t t1, prune_traceinf_finite t t1 ->
                                               prune_trace t1 = t1.
Proof.
  induction 1.
   reflexivity.
  assumption.
  destruct e; simpl; f_equal; eauto.
  edestruct He; esplit; left; reflexivity.
  edestruct He; esplit; right; reflexivity.
Qed.                                    

Inductive prune_traceinf_finite_N : nat -> traceinf -> trace -> Prop :=
| prune_traceinf_finite_N_nil t (Ht: all_call_return t) n:
    prune_traceinf_finite_N n t nil
| prune_traceinf_finite_N_cons_call_return e (He: is_call_or_return e) n tf t (Htf: prune_traceinf_finite_N n tf t):
    prune_traceinf_finite_N (S n) (Econsinf e tf) t
| prune_traceinf_finite_N_cons_normal e (He: ~ is_call_or_return e) n tf t (Htf: prune_traceinf_finite_N n tf t)
:
  prune_traceinf_finite_N (S n) (Econsinf e tf) (e :: t)
.

Lemma prune_traceinf_finite_N_ex: forall t tf,
                                    prune_traceinf_finite t tf ->
                                    exists n, prune_traceinf_finite_N n t tf.
Proof.
  induction 1.
   exists O. constructor. assumption.
  destruct IHprune_traceinf_finite. esplit. econstructor. assumption. eassumption.
  destruct IHprune_traceinf_finite. esplit. eapply prune_traceinf_finite_N_cons_normal. eassumption. eassumption.
Qed.

Lemma prune_traceinf_finite_N_app_recip_l:
  forall t1 n t tf,
    prune_traceinf_finite_N n (t1 *** t) tf ->
    (exists tf', prune_traceinf_finite_N (n - length t1) t tf' /\ (n >= length t1) /\ tf = prune_trace t1 ** tf') \/ (tf = prune_trace t1 /\ all_call_return t).
Proof.
  induction t1.
   simpl. left. replace (n - 0) with n by omega.
   eauto with arith.
  intros. simpl in H. inversion H; subst.
   right. 
   exploit all_call_return_cons_recip_r; eauto.
   exploit all_call_return_cons_recip_l; eauto.
   intros.
   exploit all_call_return_app_recip_r; eauto.
   exploit all_call_return_app_recip_l; eauto.
   intros.
   destruct (prune_trace_cases a t1).
    destruct a0. rewrite H5. rewrite H2. eauto.
   destruct a0; contradiction.
  destruct (IHt1 _ _ _ Htf).
   destruct H0. destruct H0. destruct H1.
   left. esplit. split. simpl. eassumption.
   split. simpl. omega.
   destruct (prune_trace_cases a t1). destruct a0. rewrite H4. assumption.
   destruct a0. contradiction.
  destruct H0. 
  destruct (prune_trace_cases a t1).
   destruct a0. rewrite H3. eauto.
  destruct a0. contradiction.
  destruct (IHt1 _ _ _ Htf).
   destruct H0. destruct H0. destruct H1.
   left. esplit. split. simpl. eassumption.
   split. simpl. omega.
   destruct (prune_trace_cases a t1). destruct a0. contradiction.
   destruct a0. rewrite H4. subst. reflexivity.
 destruct H0.
 destruct (prune_trace_cases a t1).
  destruct a0; contradiction.
 destruct a0. rewrite H3. right. split; auto. congruence.
Qed.

Lemma prune_traceinf_finite_all_call_return :
  forall t tf,
    prune_traceinf_finite t tf ->
    all_call_return t ->
    tf = nil.
Proof.
  induction 1; eauto; inversion 1; subst; eauto; edestruct He; esplit; eauto.
Qed.

Lemma prune_traceinf_finite_sim_inj:
  forall t1 tf1,
    prune_traceinf_finite t1 tf1 ->
    forall t2 tf2, prune_traceinf_finite t2 tf2 ->
                   traceinf_sim t1 t2 ->
                   tf1 = tf2.
Proof.
  induction 1; inversion 1; subst; inversion 1; subst; eauto; try contradiction.
  symmetry; inversion Ht; subst; eauto using prune_traceinf_finite_all_call_return, all_call_return_sim.
  inversion Ht; subst; edestruct He; esplit; eauto.
  inversion Ht; subst; eauto using prune_traceinf_finite_all_call_return, all_call_return_sim, traceinf_sim_sym.
  inversion Ht; subst; edestruct He; esplit; eauto.
  erewrite IHprune_traceinf_finite; eauto.
Qed.

Corollary prune_traceinf_finite_inj:
  forall t tf1,
    prune_traceinf_finite t tf1 ->
    forall tf2, prune_traceinf_finite t tf2 ->
                tf1 = tf2.
Proof.
  intros; eauto using prune_traceinf_finite_sim_inj, traceinf_sim_refl.
Qed.

Lemma prune_traceinf_finite_sim_ex:
  forall t1 tf,
    prune_traceinf_finite t1 tf ->
    forall t2,
      traceinf_sim t1 t2 ->
      prune_traceinf_finite t2 tf.
Proof.
  induction 1; inversion 1; subst.
  eapply prune_traceinf_finite_nil. eapply all_call_return_sim. eassumption. constructor; auto.
  eapply prune_traceinf_finite_cons_call_return. assumption. eauto.
  eapply prune_traceinf_finite_cons_normal. assumption. eauto.
Qed.

Lemma prune_traceinf_head_finite:
  forall t1 t2,
    prune_traceinf_head t1 t2 ->
    forall t, prune_traceinf_finite t2 t ->
              prune_traceinf_finite t1 t.
Proof.
  induction 1.
   intros.
   econstructor.
   assumption.
   auto.
  tauto.
Qed.

CoInductive prune_traceinf_infinite: traceinf -> traceinf -> Prop :=
| prune_traceinf_infinite_intro
    t e t1
    (Ht1_: prune_traceinf_head t (Econsinf e t1))
    t2 (Ht2_: prune_traceinf_infinite t1 t2):
    prune_traceinf_infinite t (Econsinf e t2)
.

Lemma prune_traceinf_infinite_idem:
  forall t1 t2,
    prune_traceinf_infinite t1 t2 ->
    forall t3, prune_traceinf_infinite t2 t3 ->
               traceinf_sim t2 t3.
Proof.
  cofix COINDHYP.
  inversion 1; subst.
  inversion 1; subst.
  inversion Ht1_0; subst.
   clear COINDHYP. edestruct (prune_traceinf_head_no_call_return).
   2: reflexivity.
   eexact Ht1_.
   assumption.
  constructor. eapply COINDHYP; eauto.
Qed.

Lemma prune_traceinf_infinite_sim_inj:
  forall t1 tf1,
    prune_traceinf_infinite t1 tf1 ->
    forall t2, traceinf_sim t1 t2 ->
               forall tf2, prune_traceinf_infinite t2 tf2 ->
                           traceinf_sim tf1 tf2.
Proof.
  cofix COINDHYP. inversion 1; subst; inversion 2; subst.
   generalize (prune_traceinf_head_sim_inj _ _ Ht1_ _ H0 _ Ht1_0).
   inversion 1; subst.
   constructor. eapply COINDHYP; clear COINDHYP. eassumption. eassumption. assumption.
Qed.

Lemma prune_traceinf_infinite_sim_surj:
  forall t1 tf1,
    prune_traceinf_infinite t1 tf1 ->
    forall tf2, traceinf_sim tf1 tf2 ->
                forall t2, traceinf_sim t1 t2 ->
                prune_traceinf_infinite t2 tf2.
Proof.
  cofix COINDHYP. inversion 1; subst; inversion 1; subst.
  intros; destruct (prune_traceinf_head_sim_ex _ _ Ht1_ _ H1).
  generalize (prune_traceinf_head_sim_inj _ _ Ht1_ _ H1 _ H2).
  inversion 1; subst.
  econstructor. eassumption. eapply COINDHYP. 2: eassumption. eassumption. assumption.
Qed.

Corollary prune_traceinf_infinite_sim_ex: forall t1 t,
                                        prune_traceinf_infinite t1 t ->
                                        forall t2, traceinf_sim t1 t2 ->
                                                   prune_traceinf_infinite t2 t.
Proof.
  intros. eapply prune_traceinf_infinite_sim_surj. eassumption. apply traceinf_sim_refl. assumption.
Qed.

Lemma prune_traceinf_finite_not_infinite:
  forall t tf1,
    prune_traceinf_finite t tf1 ->
    forall tf2, prune_traceinf_infinite t tf2 ->
                False.
Proof.
  induction 1.
   inversion 1; subst; eapply all_call_return_no_prune_traceinf_head; eauto.
  inversion 1; subst. inversion Ht1_; subst; eauto.
  eapply IHprune_traceinf_finite. econstructor. eassumption. eassumption.
  inversion 1; subst.
  inversion Ht1_; subst.
   contradiction.
  eauto.
Qed.

Lemma prune_traceinf_finite_app: forall t tf, prune_traceinf_finite t tf -> forall l,
                                                                              prune_traceinf_finite (Eappinf l t) (Eapp (prune_trace l) tf).
Proof.
  intros. revert t tf H. induction l.
   simpl; tauto.   
  destruct (prune_trace_cases a l).
   destruct a0. rewrite H0. intros. simpl. econstructor. assumption. eauto.  
  destruct a0. rewrite H0. intros. simpl.
  eapply prune_traceinf_finite_cons_normal.   
  assumption.
  eauto.
Qed.

Lemma prune_traceinf_finite_app_recip_r:
  forall l t tf, prune_traceinf_finite t (Eapp l tf) ->
                 exists l', exists t', t = Eappinf l' t' /\ l = prune_trace l' /\ prune_traceinf_finite t' tf.
Proof.
  intros until tf. generalize (refl_equal (l ** tf)). generalize (l ** tf) at 1 3. intros t_ H INDH. revert l tf H. induction INDH.
   intros. symmetry in H. destruct (app_eq_nil _ _ H). subst. clear H.
   exists nil. exists t. split. reflexivity. split. reflexivity. constructor. assumption.
  intros. destruct (IHINDH _ _ H). destruct H0. destruct H0. destruct H1. subst.
  exists (e :: x). eexists x0. 
  split.
  reflexivity.
  split.
  destruct (prune_trace_cases e x). destruct a. rewrite H0. reflexivity. destruct a. contradiction.
  assumption.
  destruct l.
   simpl. intros; subst. clear IHINDH.
   exists nil. esplit. split. reflexivity. split. reflexivity.
   eapply prune_traceinf_finite_cons_normal. assumption. assumption.
  injection 1; intros; subst.
  destruct (IHINDH l tf0 (refl_equal _)); clear IHINDH.
  destruct H0.
  destruct H0.
  destruct H1.
  subst.
  exists (e0 :: x).
  exists x0.
  split.
  reflexivity.
  split.
  destruct (prune_trace_cases e0 x). destruct a. contradiction. destruct a. congruence.
  assumption.
Qed.

Lemma prune_traceinf_finite_app_recip_l:
  forall l t tf, prune_traceinf_finite (Eappinf l t) tf ->
                 exists tf', tf = Eapp (prune_trace l) tf' /\ prune_traceinf_finite t tf'.
Proof.
  induction l.
   simpl. eauto.
  intros. simpl in H. inversion H; subst.
   assert (all_call_return (l *** t)) by (inversion Ht; subst; assumption).
   assert (is_call_or_return a) by (inversion Ht; subst; esplit; eauto).
   destruct (prune_trace_cases a l).
    destruct a0. rewrite H3.
    erewrite (all_call_return_app_recip_l).
    2: eassumption.
    esplit. split. reflexivity. econstructor. eapply all_call_return_app_recip_r. eassumption.
   destruct a0; contradiction.
  destruct (prune_trace_cases a l).
   destruct a0. rewrite H1. eauto.
  destruct a0; contradiction.
 destruct (prune_trace_cases a l).
  destruct a0. contradiction.
 destruct a0. rewrite H1. simpl.
 exploit IHl; eauto.
 destruct 1. destruct H2. subst. eauto.
Qed.

Lemma prune_traceinf_infinite_app: forall t tf, prune_traceinf_infinite t tf -> forall l,
                                                                                  prune_traceinf_infinite (Eappinf l t) (Eappinf (prune_trace l) tf).
Proof.
  intros. revert t tf H. induction l.
   simpl. tauto.
  destruct (prune_trace_cases a l).
   destruct a0. rewrite H0. simpl. intros.
   generalize (IHl _ _ H1).
   inversion 1; subst.
   econstructor.
   eapply prune_traceinf_head_call_return.
   assumption.
   eassumption.
   assumption.
  destruct a0.
  rewrite H0.
  simpl.
  econstructor.
  eapply prune_traceinf_head_normal.
  assumption.
  eauto.
Qed.

CoInductive prune_traceinf_infinite_N: nat -> traceinf -> traceinf -> Prop :=
| prune_traceinf_infinite_N_call_or_return:
    forall e (He: is_call_or_return e) 
           n t T (Ht: prune_traceinf_infinite_N n t T),
      prune_traceinf_infinite_N (S n) (Econsinf e t) T
| prune_traceinf_infinite_N_normal
    e (He: ~ is_call_or_return e)
    n2 t T (Ht: prune_traceinf_infinite_N n2 t T) n1 :
    prune_traceinf_infinite_N n1 (Econsinf e t) (Econsinf e T)
.

Inductive prune_traceinf_head_N : nat -> traceinf -> traceinf -> Prop :=
| prune_traceinf_head_N_call_return
    e (He: is_call_or_return e) n t1 t2 (Ht: prune_traceinf_head_N n t1 t2)
  : prune_traceinf_head_N (S n) (Econsinf e t1) t2
| prune_traceinf_head_N_normal
    e (He: ~ is_call_or_return e)
    n t
  : prune_traceinf_head_N n (Econsinf e t) (Econsinf e t)
.

Lemma prune_traceinf_head_N_ex: forall t T, 
                                  prune_traceinf_head t T ->
                                  exists n, prune_traceinf_head_N n t T.
Proof.
  induction 1.
   destruct IHprune_traceinf_head. esplit. econstructor. assumption. eassumption.
  exists O. constructor. assumption.
Qed.

Lemma prune_traceinf_infinite_N_ex':
  forall n t1 e t2, prune_traceinf_head_N n t1 (Econsinf e t2) ->
                  forall t, prune_traceinf_infinite t2 t ->
                               prune_traceinf_infinite_N n t1 (Econsinf e t).
Proof.
  cofix COINDHYP.
  inversion 1; subst.
   intros. econstructor. assumption. eapply COINDHYP; clear COINDHYP. eassumption. assumption.
  clear H. inversion 1; subst.
  destruct (prune_traceinf_head_N_ex _ _ Ht1_); clear Ht1_.  
  econstructor. assumption. eapply COINDHYP; clear COINDHYP.  2: eassumption. eassumption.
Qed.

Lemma prune_traceinf_infinite_N_ex:
  forall t T, prune_traceinf_infinite t T ->
              exists n, prune_traceinf_infinite_N n t T.
Proof.
  inversion 1; subst.
  exploit prune_traceinf_head_N_ex. eassumption.
  destruct 1.
  esplit; eauto using prune_traceinf_infinite_N_ex'.
Qed.

Lemma prune_traceinf_infinite_N_app_recip_l: 
  forall t1 n1 T2 T, prune_traceinf_infinite_N n1 (t1 *** T2) T ->
                    exists T', exists n2, prune_traceinf_infinite_N n2 T2 T' /\
                                          T = prune_trace t1 *** T' /\
                                          (prune_trace t1 <> E0 \/ (prune_trace t1 = E0 /\ n1 >= length t1 /\ n2 = n1 - length t1)).
Proof.
  induction t1.
   simpl in *. eauto 9 with arith.
  intros. simpl in H. inversion H; clear H; subst.
   exploit IHt1; clear IHt1. eassumption.
   clear Ht. destruct 1. destruct H. destruct H. destruct H0. subst.
  destruct (prune_trace_cases a t1).
  destruct a0. clear H0. rewrite H2. simpl.
  destruct H1; eauto 6.
  destruct H0. destruct H1. assert (S n >= S (length t1)) by omega. eauto 8.
  destruct a0; contradiction.
  exploit IHt1; clear IHt1.
  eassumption.
  clear Ht.
  destruct 1.
  destruct H.
  destruct H.
  destruct H0.
  clear H1.
  subst.
  destruct (prune_trace_cases a t1).
   destruct a0. contradiction.
  destruct a0. clear H0.
  rewrite H1.
  simpl.
  esplit.
  esplit.
  split.
  eassumption.
  split. reflexivity. left. discriminate.
Qed.

Lemma prune_traceinf_infinite_N_head:
  forall n t T,
    prune_traceinf_infinite_N n t T ->
    exists e, exists t', prune_traceinf_head t (Econsinf e t') /\
        exists T', exists n', prune_traceinf_infinite_N n' t' T' /\
                              T = Econsinf e T'.
Proof.
  induction n using (well_founded_induction lt_wf).
  inversion 1; subst.
   exploit H. 2: eexact Ht. omega.
  destruct 1. destruct H1. destruct H1. esplit. esplit. split. econstructor. assumption. eassumption. assumption.
 esplit. esplit. split.
 eapply prune_traceinf_head_normal. assumption.
 eauto.
Qed.

Lemma prune_traceinf_infinite_N_infinite:
  forall n t T,
    prune_traceinf_infinite_N n t T ->
    prune_traceinf_infinite t T.
Proof.
  cofix COINDHYP.
  intros. 
  destruct (prune_traceinf_infinite_N_head _ _ _  H).
  destruct H0.
  destruct H0.
  destruct H1.
  destruct H1. 
  destruct H1.
  subst.
  econstructor; eauto.
Qed.

CoInductive prune_traceinf_infinite': traceinf -> traceinf -> Prop :=
| prune_traceinf_infinite'_intro
    l (Hl: prune_trace l <> E0)
    t T (Ht: prune_traceinf_infinite' t T)
    t' (Ht': t' = l *** t)
    T' (HT': T' = prune_trace l *** T)
  :
    prune_traceinf_infinite' t' T'.

Lemma prune_traceinf_infinite'_head:
  forall 
    l (Hl: prune_trace l <> E0)
    t T (Ht: prune_traceinf_infinite' t T)
  ,
    exists e, exists t',
                prune_traceinf_head (l *** t) (Econsinf e t') /\
                exists T',
                             prune_traceinf_infinite' t' T' /\
                             prune_trace l *** T = Econsinf e T'.
Proof.
  induction l.
   simpl. destruct 1. reflexivity.
  destruct (prune_trace_cases a l).
   destruct a0. rewrite H0. simpl.
   intros. exploit IHl. assumption. eassumption. destruct 1. destruct H1. destruct H1.
   esplit. esplit. split. econstructor. assumption. eassumption.
   assumption.
  destruct a0.
  rewrite H0.
  simpl.
  intros _.
  case_eq (prune_trace l).
   intro. clear IHl.
   inversion 1; subst.
   esplit. esplit. split.
   eapply prune_traceinf_head_normal.
   assumption.
   esplit. split. econstructor.
   instantiate (1 := l ** l0). rewrite prune_trace_app. rewrite H1. assumption.
   eexact Ht0.
   rewrite Eappinf_assoc.
   reflexivity.
   reflexivity.
   simpl.
   rewrite prune_trace_app. rewrite H1. reflexivity.
  intros.
  assert (prune_trace l <> E0).
   unfold E0; congruence.
  rewrite <- H1.
  clear e l0 H1.
  exploit IHl.
  assumption.
  eassumption.
  clear IHl.
  destruct 1. destruct H1. destruct H1.
  destruct H3. destruct H3.
  esplit. esplit. split.
  eapply prune_traceinf_head_normal. assumption.
  esplit. split. 
  econstructor. eassumption. 2: reflexivity. eassumption.
  reflexivity.
  reflexivity.
Qed.  
  
Lemma prune_traceinf_infinite'_infinite: forall t1 t2,
                                           prune_traceinf_infinite' t1 t2 ->
                                           prune_traceinf_infinite t1 t2.
Proof.
  cofix COINDHYP.
  inversion 1; subst.
  destruct (prune_traceinf_infinite'_head _ Hl _ _ Ht).
  destruct H0. destruct H0. destruct H1. destruct H1.
  rewrite H2.
  econstructor; eauto.
Qed.   

(*

CoInductive prune_traceinf' : traceinf -> traceinf' -> Type :=
  | prune_traceinf'_intro
      l1 l2 (Hl: l2 = prune_trace l1)
      T1 T2 (HT: prune_traceinf' T1 T2)
      T (HT_: T = l1 *** T1)
      E2 :
    prune_traceinf' T (Econsinf' l2 T2 E2 )
.

CoInductive prune_traceinf'_t : traceinf -> Type :=
| prune_traceinf'_t_intro
    l1 l2 (Hl: l2 = prune_trace l1)
    T1 (HT: prune_traceinf'_t T1)
    T (HT_: T = l1 *** T1)
    (E2: l2 <> E0) :
    prune_traceinf'_t T
.

Lemma prune_traceinf'_infinite:
  forall T1 T2,
    prune_traceinf' T1 T2 ->
    prune_traceinf_infinite T1 (traceinf_of_traceinf' T2).
Proof.
  intros. apply prune_traceinf_infinite'_infinite.
  revert T1 T2 H.
  cofix COINDHYP.
  inversion 1; subst.
  econstructor.
  eassumption. eapply COINDHYP. eexact HT.
  reflexivity.
  rewrite traceinf_traceinf'_app. reflexivity.
Qed.

CoFixpoint prune_traceinf'_ex: forall t, prune_traceinf'_t t ->
                                         traceinf'.
Proof.
  destruct 1.
   econstructor.
   eapply prune_traceinf'_ex.
   eassumption.
   eassumption.
Defined.

Lemma prune_traceinf'_ex_t: forall t (Ht: prune_traceinf'_t t),
                              prune_traceinf' t  (prune_traceinf'_ex _ Ht) .
Proof.
  cofix COINDHYP. destruct Ht.
   rewrite (unroll_traceinf' (prune_traceinf'_ex T (prune_traceinf'_t_intro l1 l2 Hl T1 Ht T HT_ E2))).
   simpl.
   econstructor.
   eassumption.
   eapply COINDHYP; clear COINDHYP.
   assumption.
Qed.
*)

CoInductive prune_traceinf_infinite_t: traceinf -> Type :=
| prune_traceinf_infinite_t_intro
    t e t1
    (Ht1_: prune_traceinf_head t (Econsinf e t1))
    (Ht2_: prune_traceinf_infinite_t t1):
    prune_traceinf_infinite_t t
.

CoFixpoint prune_traceinf_infinite_ex:
  forall t,
    prune_traceinf_infinite_t t ->
    traceinf.
Proof.
  destruct 1.
  econstructor.
  assumption.
  eapply prune_traceinf_infinite_ex.
  eassumption.
Defined.

Lemma prune_traceinf_infinite_ex_prop :
  forall t (Ht: prune_traceinf_infinite_t t),
    prune_traceinf_infinite t (prune_traceinf_infinite_ex t Ht).
Proof.
  cofix COINDHYP.
  intros.
  rewrite (unroll_traceinf (prune_traceinf_infinite_ex t Ht)).
  destruct Ht.
  simpl.
  econstructor.
  eassumption.
  eapply COINDHYP.
Qed.

Lemma no_prune_traceinf_finite_infinite:
  forall t,
    (~ exists t', prune_traceinf_finite t t') ->
    prune_traceinf_infinite_t t.
Proof.
  cofix COINDHYP.
  intros.
  destruct (ClassicalEpsilon.excluded_middle_informative (exists t', prune_traceinf_head t t')).
  destruct (ClassicalEpsilon.constructive_indefinite_description _ e); clear e.
  destruct x.
  econstructor.
  eassumption.
  eapply COINDHYP.
  clear COINDHYP.
  intro.
  destruct H0.
  apply H.
  esplit.
  eapply prune_traceinf_head_finite.
  eassumption.
  eapply prune_traceinf_finite_cons_normal.
  eapply prune_traceinf_head_no_call_return.
  eassumption.
  reflexivity.
  eassumption.
 clear COINDHYP.
 destruct H.
 exists nil.
 constructor.
 apply no_prune_traceinf_head_all_call_return.
 intros.
 intro.
 destruct n.
 eauto.
Qed.
   
Inductive prune_traceinf_prop (t : traceinf): program_behavior -> Prop :=
| prune_traceinf_prop_finite
    tf
    (Htf: prune_traceinf_finite t tf) :
    prune_traceinf_prop t (Diverges tf)
| prune_traceinf_prop_infinite
    tf
    (Htf: prune_traceinf_infinite t tf):
    prune_traceinf_prop t (Reacts tf)
.

Lemma prune_traceinf_prop_ex:
  forall t, exists b,
    prune_traceinf_prop t b.
Proof.
  intros.
  destruct (Classical_Prop.classic (exists t', prune_traceinf_finite t t')).
   destruct H.
   esplit.
   eleft.
   eassumption.
   esplit. eright. eapply prune_traceinf_infinite_ex_prop.
   Grab Existential Variables.
   apply no_prune_traceinf_finite_infinite.
   assumption.
Qed.
  
Inductive prune_behavior : program_behavior -> program_behavior -> Prop :=
| prune_behavior_terminates t t' (Ht': prune_trace t = t') i :
    prune_behavior (Terminates t i) (Terminates t' i)
| prune_behavior_stuck t t' (Ht': prune_trace t = t')  :
    prune_behavior (Goes_wrong t) (Goes_wrong t')
| prune_behavior_diverges  t t' (Ht': prune_trace t = t')  :
    prune_behavior (Diverges t) (Diverges t')
| prune_behavior_reacts t tf (Ht: prune_traceinf_prop t tf) :
    prune_behavior (Reacts t) tf
.

Theorem prune_behavior_ex:
  forall b, exists b',
    prune_behavior b b'.
Proof.
  destruct b.
   esplit. econstructor. reflexivity.
   esplit. econstructor. reflexivity.
   destruct (prune_traceinf_prop_ex t).
   esplit. econstructor. eassumption.
   esplit. econstructor. reflexivity.
Qed.

Inductive behavior_sim: program_behavior -> program_behavior -> Prop :=
| behavior_sim_refl: forall b, behavior_sim b b
| behavior_sim_reacts: forall t1 t2, traceinf_sim t1 t2 ->
                                     behavior_sim (Reacts t1) (Reacts t2)
.

Lemma behavior_sim_sym: forall b1 b2,
                          behavior_sim b1 b2 -> behavior_sim b2 b1.
Proof.
  inversion 1; subst; eauto. constructor. eauto using traceinf_sim_sym.
Qed.

Lemma behavior_sim_trans: forall b1 b2,
                            behavior_sim b1 b2 ->
                            forall b3, behavior_sim b2 b3 ->
                                       behavior_sim b1 b3.
Proof.
  inversion 1; subst; inversion 1; subst; eauto.
  constructor. eauto using traceinf_sim_trans.
Qed.

Inductive behavior_sim': program_behavior -> program_behavior -> Prop :=
| behavior_sim'_not_reacts: forall b, (forall t, b <> Reacts t) -> behavior_sim' b b
| behavior_sim'_reacts: forall t1 t2, traceinf_sim t1 t2 ->
                                     behavior_sim' (Reacts t1) (Reacts t2)
.

Lemma behavior_sim'_sim: 
  forall b1 b2, 
    behavior_sim' b1 b2 ->
    behavior_sim b1 b2.
Proof.
  inversion 1; subst; econstructor; eauto.
Qed.

Lemma behavior_sim_sim':
  forall b1 b2, 
    behavior_sim b1 b2 ->
    behavior_sim' b1 b2.
Proof.
  inversion 1; subst.
   destruct b2; try (left; intros; discriminate).
   right. apply traceinf_sim_refl.
   constructor. assumption.
Qed.

Theorem prune_behavior_sim_inj:
  forall b1,
  forall b'1, prune_behavior b1 b'1 ->
              forall b2, behavior_sim b1 b2 ->
                         forall b'2, prune_behavior b2 b'2 ->
                                     behavior_sim b'1 b'2.
Proof.
  intros. apply behavior_sim_sim' in H0.
  inversion H; subst; inversion H0; subst; inversion H1; subst; try now constructor.
  edestruct H2; reflexivity.
  inversion Ht; inversion Ht0; subst.
   exploit prune_traceinf_finite_sim_inj. eexact Htf. eexact Htf0. assumption.
   intro; subst; constructor.
  exploit prune_traceinf_finite_sim_ex. eassumption. eassumption.
  intro.
  edestruct prune_traceinf_finite_not_infinite.
  eassumption.
  eassumption.
  exploit prune_traceinf_infinite_sim_ex. eassumption. eassumption.
  intro.
  edestruct prune_traceinf_finite_not_infinite.
  eassumption.
  eassumption.
  constructor.
  eapply prune_traceinf_infinite_sim_inj.
  eassumption.
  eassumption.
  assumption.
Qed.

Theorem prune_behavior_sim_surj:
  forall b1,
  forall b'1, prune_behavior b1 b'1 ->
              forall b2, behavior_sim b1 b2 ->
                         forall b'2, 
                                     behavior_sim b'1 b'2 ->
                                     prune_behavior b2 b'2.
Proof.
  intros. apply behavior_sim_sim' in H0. apply behavior_sim_sim' in H1.
  inversion H; subst; inversion H0; subst; inversion H1; subst; eauto.
  edestruct H2; eauto.
  inversion Ht; subst.
   econstructor. econstructor. eapply prune_traceinf_finite_sim_ex. eassumption. assumption.
  edestruct H2; eauto.
  inversion Ht; subst.
  econstructor.
  econstructor.
  eauto using prune_traceinf_infinite_sim_surj.
Qed.

Theorem prune_behavior_idem: forall b1 b2, prune_behavior b1 b2 -> forall b3, prune_behavior b2 b3 ->
                                                                              behavior_sim b2 b3.
Proof.
  inversion 1; subst; inversion 1; subst; try (rewrite prune_trace_idem; constructor; fail).
  inversion Ht.
  inversion Ht.
  inversion Ht; subst.
  erewrite prune_traceinf_finite_idem. constructor. eassumption.
  inversion Ht; subst.
  inversion Ht0; subst.
   exfalso. clear Ht H. revert Htf0 t Htf. clear. 
   induction 1.
    inversion 1; subst.
    inversion Ht; subst.
    eapply prune_traceinf_head_no_call_return. eassumption. reflexivity. esplit; left; reflexivity.
    eapply prune_traceinf_head_no_call_return. eassumption. reflexivity. esplit; right; reflexivity.
   inversion 1; subst; eauto.
   inversion 1; subst; eauto.
  constructor. eauto using prune_traceinf_infinite_idem.
Qed.   

Lemma traceinf_sim_app_recip: forall t t1 t2,
                                traceinf_sim (t *** t1) t2 ->
                                exists t'2, t2 = t *** t'2 /\ traceinf_sim t1 t'2.
Proof.
  induction t; simpl.
   eauto.
  inversion 1; subst.
  exploit IHt.
  eassumption.
  destruct 1.
  destruct H0.
  subst.
  eauto.  
Qed.

Lemma traceinf_sim_app: forall t1 t2,
                                traceinf_sim t1 t2 ->
                                forall t,
                                traceinf_sim (t *** t1) (t *** t2).
Proof.
  induction t; simpl.
   tauto.
  constructor. assumption.
Qed.
  

Section GENV.

Context {genv: Type} {state: Type} (step: genv -> state -> trace -> state -> Prop).

Inductive prune_step (ge: genv) (s: state) (t: trace) (s': state): Prop :=
| prune_step_intro t'
    (Hstep: step ge s t' s')
    (Ht': prune_trace t' = t)
.

Lemma step_prune: forall ge s t s', step ge s t s' -> prune_step ge s (prune_trace t) s'.
Proof.
  intros. esplit; eauto.
Qed.

Lemma star_prune:
  forall ge s t s',
    star step ge s t s' ->    
    star prune_step ge s (prune_trace t) s'
.
Proof.
  induction 1; simpl.
  constructor.
  eapply star_step. 
  eauto using step_prune.
  eassumption. subst. rewrite prune_trace_app. reflexivity.
Qed.

Lemma plus_prune: 
  forall ge s t s',
    plus step ge s t s' ->    
    plus prune_step ge s (prune_trace t) s'
.
Proof.
  inversion 1; subst; econstructor; eauto using step_prune, star_prune, prune_trace_app.
Qed.

Lemma prune_star: forall ge s t s',
                    star prune_step ge s t s' ->
                    exists t', star step ge s t' s' /\ t = prune_trace t'.
Proof.
  induction 1; simpl.
   esplit. split. econstructor. reflexivity.
  destruct IHstar. destruct H2. destruct H.  subst. esplit. split. econstructor. eassumption. eassumption. reflexivity. rewrite prune_trace_app. reflexivity.
Qed.                  

Lemma prune_plus: forall ge s t s',
                    plus prune_step ge s t s' ->
                    exists t', plus step ge s t' s' /\ prune_trace t' = t.
Proof.
  inversion 1; subst.
  clear H.
  destruct H0.
  subst.
  exploit prune_star; eauto.
  clear H1.
  destruct 1. destruct H.
  subst.
  esplit. split. econstructor; eauto. eauto using prune_trace_app.
Qed.


Lemma nostep_prune: forall ge s, nostep step ge s -> nostep prune_step ge s.
Proof.
  unfold nostep. intros. intro. destruct H0. eapply H. eauto.
Qed.

Lemma prune_nostep: forall ge s, nostep prune_step ge s -> nostep step ge s.
Proof.
  unfold nostep. intros. intro. edestruct H. econstructor. eassumption. reflexivity.
Qed.

Lemma forever_silent_prune: forall ge s,
                              forever_silent step ge s -> forever_silent prune_step ge s.
Proof.
  cofix COINDHYP.
  inversion 1; subst.
  assert (prune_step ge s E0 s2). clear COINDHYP.
   exploit step_prune. eassumption. intro. eassumption.
  esplit. eassumption. eapply COINDHYP; clear COINDHYP. assumption.
Qed.


Lemma forever_reactive_app: forall ge s t s', star step ge s t s' -> forall t', forever_reactive step ge s' t' -> forever_reactive step ge s (t *** t').
Proof.
  destruct t.
   inversion 2; subst.
   change (nil *** t *** T) with ((nil ** t) *** T).
   econstructor. eapply star_trans. eassumption. eassumption. reflexivity. assumption. assumption.
  intros. econstructor. eassumption. discriminate. assumption.
Qed.

Lemma forever_reactive_sim: forall ge s t1, forever_reactive step ge s t1 -> forall t2, traceinf_sim t1 t2 -> forever_reactive step ge s t2.
Proof.
  cofix COINDHYP.
  destruct 1.
   intros.
   destruct (traceinf_sim_app_recip _ _ _ H2).
   destruct H3.
   subst.
   econstructor.
   eassumption.
   assumption.
   eapply COINDHYP; clear COINDHYP.
   eassumption.
   assumption.
Qed.

CoInductive forever_reactive_N (ge: genv): nat -> state -> traceinf -> Prop :=
  | forever_reactive_N_silent: forall s1 s2,
      star step ge s1 E0 s2 -> forall n1 n2, n2 < n1 -> forall T,
          forever_reactive_N ge n2 s2 T ->
          forever_reactive_N ge n1 s1 T
  | forever_reactive_N_non_silent: forall s1 s2 t n1 n2 T,
      star step ge s1 t s2 -> t <> E0 -> forever_reactive_N ge n2 s2 T ->
      forever_reactive_N ge n1 s1 (t *** T).

Lemma forever_reactive_forever_reactive_N:
  forall ge s T,
    forever_reactive step ge s T ->
    forall n, forever_reactive_N ge n s T.
Proof.
  cofix COINDHYP. inversion 1; subst. eright. eassumption. assumption. instantiate (1 := O). eapply COINDHYP; clear COINDHYP. assumption.
Qed.

Lemma forever_reactive_N_forever_reactive': 
  forall ge n s T,
    forever_reactive_N ge n s T ->
    exists t, t <> E0 /\
              exists s', star step ge s t s' /\
                         exists n', exists T', forever_reactive_N ge n' s' T' /\
                                               T = t *** T'.
Proof.
  induction n using (well_founded_induction lt_wf).
  inversion 1; subst; eauto 8.
  exploit H.
  eassumption.
  eassumption.
  destruct 1. destruct H4. destruct H5. destruct H5.
  esplit. split. eassumption. esplit. split. eapply star_trans. eassumption. eassumption. reflexivity. assumption.
Qed.

Lemma forever_reactive_N_forever_reactive: 
  forall ge n s T,
    forever_reactive_N ge n s T ->
    forever_reactive step ge s T.
Proof.
  cofix COINDHYP. intros.
  generalize (forever_reactive_N_forever_reactive' _ _ _ _ H).
  destruct 1. destruct H0. destruct H1. destruct H1. destruct H2. destruct H2. destruct H2. subst.
  econstructor; eauto.
Qed.

Lemma forever_reactive_destr : forall ge s T ,
  forever_reactive step ge s T ->                                     
  { t : _ & {s' : _ & { T' | star step ge s t s' /\ t <> E0 /\ forever_reactive step ge s' T' /\ T = t *** T'}}}.
Proof.
  intros.
  cut (exists t, exists s', exists T', star step ge s t s' /\ t <> E0 /\ forever_reactive step ge s' T' /\ T = t *** T').
  intros.
  apply ClassicalEpsilon.constructive_indefinite_description in H0.
  destruct H0.
  apply ClassicalEpsilon.constructive_indefinite_description in e.
  destruct e.
  apply ClassicalEpsilon.constructive_indefinite_description in e.
  destruct e.
  eauto.
  inversion H; subst; eauto 7.
Qed.

CoInductive reacts_t (ge: genv) : state -> traceinf -> Type :=
| reacts_intro
  t (Ht: t <> E0)
  s s' (Hs: star step ge s t s')
  T'  (HT': reacts_t ge s' T')
  T (HT: T = Eappinf t T'):
  reacts_t ge s T
.

Lemma reacts_t_ex: forall ge s T,
  forever_reactive step ge s T ->
  {t : _ & {s' : _ & {T' | t <> E0 /\ star step ge s t s' /\ forever_reactive step ge s' T' /\ T = Eappinf t T'}}}.
Proof.
  intros. 
  cut (exists t s' T', t <> E0 /\ star step ge s t s' /\ forever_reactive step ge s' T' /\ T = Eappinf t T').
  intro.
  apply ClassicalEpsilon.constructive_indefinite_description in H0.
  destruct H0.
  apply ClassicalEpsilon.constructive_indefinite_description in e.
  destruct e.
  apply ClassicalEpsilon.constructive_indefinite_description in e.
  destruct e.
  eauto.
  inversion H; subst; eauto 7.
Qed.

Lemma reacts_reacts_t: forall ge s T,
  forever_reactive step ge s T ->
  reacts_t ge s T.
Proof.
  cofix COINDHYP.
  intros.
  destruct (reacts_t_ex _ _ _ H).
  destruct s0.
  destruct s0.
  destruct a.
  destruct H1.
  destruct H2.
  econstructor; eauto.
Qed.

Lemma reacts_t_reacts: forall ge s T,
  reacts_t ge s T ->
  forever_reactive step ge s T.
Proof.
  cofix COINDHYP.
  destruct 1.
  subst.
  econstructor; eauto.
Qed.

CoInductive reacts_t' (ge: genv) : state -> Type :=
| reacts'_intro
  t (Ht: t <> E0)
  s s' (Hs: star step ge s t s')
  (HT': reacts_t' ge s'):
  reacts_t' ge s
.

(*
CoFixpoint reacts_t_t' : forall (ge: genv) (s: state) (T: traceinf) (Hreacts: reacts_t ge s T), reacts_t' ge s.
Proof.
  destruct 1.
  econstructor.
  eassumption.
  eassumption.
  eapply reacts_t_t'.
  eassumption.
Defined.
*)

CoFixpoint reacts_t'_traceinf' : forall (ge: genv) (s: state) (Hreacts': reacts_t' ge s), traceinf'.
Proof.
  destruct 1.
  econstructor.
  2: eassumption.
  eapply reacts_t'_traceinf'.
  eassumption.
Defined.

Lemma reacts_t'_traceinf_reacts: forall ge s (Hreacts: reacts_t' ge s),
  reacts_t ge s (traceinf_of_traceinf' (reacts_t'_traceinf' _ _ Hreacts)).
Proof.
  cofix COINDHYP.
  destruct Hreacts; simpl.
  econstructor.
  eassumption.
  eassumption.
  eapply COINDHYP; clear COINDHYP.
  rewrite (unroll_traceinf' (reacts_t'_traceinf' ge s (reacts'_intro ge t  Ht s s' Hs Hreacts))).
  simpl.
  rewrite traceinf_traceinf'_app.
  reflexivity.
Qed.

(*
Lemma reacts_t'_traceinf: forall ge s T (Hreacts: reacts_t ge s T),
  traceinf_sim T (traceinf_of_traceinf' (reacts_t'_traceinf' _ _ (reacts_t_t' _ _ _ Hreacts))).
Proof.
 intros.
 apply traceinf_sim'_sim.
 revert ge s T Hreacts.
 cofix COINDHYP.
 destruct Hreacts.
 rewrite (unroll_traceinf' (reacts_t'_traceinf' ge s (reacts_t_t' ge s T (reacts_intro ge t Ht s s' Hs T' Hreacts T HT)))).
 simpl.
 rewrite traceinf_traceinf'_app.
 subst.
 econstructor.
 assumption.
 eapply COINDHYP; clear COINDHYP.
Qed.
*)


End GENV.

Lemma state_behaves_sim: forall sem s b1, state_behaves sem s b1 ->
                                          forall b2, behavior_sim b1 b2 ->
                                                     state_behaves sem s b2.
Proof.
  inversion 1; subst; inversion 1; subst; eauto.
  econstructor. eapply forever_reactive_sim. eassumption. assumption.
Qed.

Lemma program_behaves_sim: forall sem b1, program_behaves sem b1 ->
                                          forall b2, behavior_sim b1 b2 ->
                                                     program_behaves sem b2.
Proof.
  inversion 1; subst; inversion 1; subst; eauto; econstructor; eauto using state_behaves_sim.
Qed.

Section Semantics.

Variable sem: semantics.


Definition prune_semantics := Semantics (prune_step (step sem)) (initial_state sem) (final_state sem) (globalenv sem).

Lemma terminates_prune:
  forall s t v,
         state_behaves sem s (Terminates  t v) ->
         state_behaves prune_semantics s (Terminates (prune_trace t) v).
Proof.
  inversion 1; subst. econstructor. eapply star_prune. eassumption. assumption.
Qed.

Lemma prune_terminates:
  forall s t v,
    state_behaves prune_semantics s (Terminates t v) ->
    exists t', state_behaves sem s (Terminates t' v) /\ prune_trace t' = t.
Proof.
  inversion 1; subst. exploit (prune_star (step sem)). eassumption. destruct 1. destruct H0. subst.
  esplit. split. econstructor. eassumption. assumption. reflexivity.
Qed.

Lemma stuck_prune:
  forall s t,
         state_behaves sem s (Goes_wrong t) ->
         state_behaves prune_semantics s (Goes_wrong (prune_trace t)).
Proof.
  inversion 1; subst. econstructor. eapply star_prune. eassumption.
  apply nostep_prune. assumption. assumption.
Qed.

Lemma prune_stuck:
  forall s t,
    state_behaves prune_semantics s (Goes_wrong t) ->
    exists t', state_behaves sem s (Goes_wrong t') /\ prune_trace t' = t.
Proof.
  inversion 1; subst. exploit (prune_star (step sem)). eassumption. destruct 1. destruct H0. subst.
  esplit. split. econstructor. eassumption. apply prune_nostep. assumption. assumption. reflexivity.
Qed.

Lemma diverges_prune:
  forall s t,
    state_behaves sem s (Diverges t) ->
    state_behaves prune_semantics s (Diverges (prune_trace t)).
Proof.
  inversion 1; subst.
  econstructor. eapply star_prune. eassumption. apply forever_silent_prune. assumption.
Qed.

Lemma reacts_prune_all_call_return:
forall (s : state sem) (t : traceinf),
             Forever_reactive sem s t ->
             all_call_return t -> Forever_silent prune_semantics s.
Proof.
  intros. apply forever_silent_N_forever with (A := unit) (a := tt) (order := fun _ _ => False).
  intro. constructor. tauto.
  revert s t H H0.
  cofix COINDHYP.
  inversion 1; subst.
  destruct (star_inv H0).
   destruct H3. contradiction.
  clear H0.
  intros.
  generalize (all_call_return_app_recip_l _ _ H0).
  generalize (all_call_return_app_recip_r _ _ H0).
  intros.
  eright. unfold E0. rewrite <- H5. eapply plus_prune. eassumption.
  eapply COINDHYP; clear COINDHYP. eassumption. assumption.
Qed.

Lemma reacts_prune_finite:
  forall s t, Forever_reactive sem s t ->
              forall l, prune_traceinf_finite t l ->
                        exists s', Star prune_semantics s (l) s' /\
                                   Forever_silent prune_semantics s'.
Proof.
  intros. exploit prune_traceinf_finite_N_ex. eassumption. clear H0. destruct 1. revert s t H l H0.
  induction x using (well_founded_induction lt_wf).
  inversion 1; subst.
  intros.
  destruct (prune_traceinf_finite_N_app_recip_l _ _ _ _ H4).
   destruct H5. destruct H5. destruct H6.
   subst.
   assert (length t0 > 0).
    destruct t0; simpl.
     destruct H2. reflexivity.
    omega.
   refine (_ (H _ _ _ _ H3 _ H5)).
   2: omega.
   clear H.
   destruct 1. 
   destruct H.
   esplit.
   split.
   eapply star_trans.
   eapply star_prune. eassumption. eassumption. reflexivity.
   assumption.
  destruct H5.
  subst.
  esplit. split. eapply star_prune. eassumption.
  eapply reacts_prune_all_call_return. eassumption. assumption.
Qed.

Lemma reacts_prune_infinite: 
  forall s t, Forever_reactive sem s t ->
              forall T, prune_traceinf_infinite t T ->
                        Forever_reactive prune_semantics s T.
Proof.
  intros. exploit prune_traceinf_infinite_N_ex. eassumption. clear H0. destruct 1.
  eapply forever_reactive_N_forever_reactive. instantiate (1 := x).
  revert s t H T x H0.
  cofix COINDHYP.
  inversion 1; subst. clear H.
  intros.
  generalize (prune_traceinf_infinite_N_app_recip_l _ _ _ _ H3); clear H3.
  destruct 1. destruct H. destruct H. destruct H3. subst.
  destruct H4.
   eright. eapply star_prune. eassumption. assumption. eapply COINDHYP; clear COINDHYP. eassumption. eassumption.
  destruct H3. destruct H4. subst.
  assert (length t0 > 0).
   destruct t0. destruct H1; reflexivity. simpl; clear COINDHYP; omega.
  eleft. rewrite <- H3. eapply star_prune. eassumption. 2: eapply COINDHYP; clear COINDHYP. 2: eassumption. 2: rewrite H3. 2: simpl. 2: eassumption. omega.
Qed.

Theorem state_behaves_prune:
  forall s t, state_behaves sem s t ->
              forall T, prune_behavior t T ->
                        state_behaves prune_semantics s T.
Proof.
  inversion 2; subst.
   eauto using terminates_prune.
   eauto using stuck_prune.
   eauto using diverges_prune.
  inversion H; subst.
  inversion Ht; subst.   
   exploit reacts_prune_finite. eassumption. eassumption.
  destruct 1. destruct H1.
  econstructor. eassumption. assumption.
  econstructor. eauto using reacts_prune_infinite.
Qed.

Corollary program_behaves_prune:
  forall t, program_behaves sem t ->
              forall T, prune_behavior t T ->
                        program_behaves prune_semantics T.
Proof.
  inversion 1; subst.
   intros. econstructor. eassumption. eauto using state_behaves_prune.
  inversion 1; subst. eright. assumption.
Qed.

CoFixpoint prune_infinite_reacts_ex:
  forall s t (Hs: reacts_t (step prune_semantics) (globalenv prune_semantics) s t),
    reacts_t' (step sem) (globalenv sem) s.
Proof.
  intros. destruct Hs.  
  destruct (ClassicalEpsilon.constructive_indefinite_description  _ (prune_star _ _ _ _ _ Hs)).
  destruct a.
  econstructor.
  2: eassumption.
  eapply prune_trace_not_E0'.
  eassumption.
  assumption.
  eapply prune_infinite_reacts_ex.
  eassumption.
Defined.

Lemma prune_infinite_reacts_aux:
  forall s t (Hs: reacts_t (step prune_semantics) (globalenv prune_semantics) s t),
    prune_traceinf_infinite (traceinf_of_traceinf' (reacts_t'_traceinf' _ _ _ (prune_infinite_reacts_ex _ _ Hs))) t.
Proof.
  intros.
  eapply prune_traceinf_infinite'_infinite.
  revert s t Hs.
  cofix COINDHYP.
  intros.
  rewrite (unroll_traceinf' (reacts_t'_traceinf' _ _ _ (prune_infinite_reacts_ex _ _ Hs))).
  destruct Hs.
  simpl.
  destruct (ClassicalEpsilon.constructive_indefinite_description
            _
                (prune_star (step sem) (globalenv sem) s t s' Hs)).
  destruct a.
  econstructor.
  subst; eauto.
  eapply COINDHYP; clear COINDHYP.
  rewrite traceinf_traceinf'_app.
  reflexivity.
  subst. reflexivity.
Qed.

Lemma prune_infinite_reacts:
  forall s t,
    Forever_reactive prune_semantics s t ->
    exists t', Forever_reactive sem s t' /\ prune_traceinf_infinite t' t.
Proof.
  intros. generalize (reacts_reacts_t _ _ _ _ H).
  intro.
  esplit.
  split.
  2: eapply prune_infinite_reacts_aux with (Hs := X).
  eapply reacts_t_reacts.
  eapply reacts_t'_traceinf_reacts.
Qed.


Record step_aux {T: Type} (ge: T) (s: state sem) (t: trace) (s': state sem): Prop :=
 step_aux_intro {
     aux_step_step: Step sem s t s';
     aux_step_prune: prune_trace t = E0;
     aux_step_div: Forever_silent prune_semantics s'
}.

Definition prune_semantics_aux := Semantics step_aux (Forever_silent prune_semantics) (fun _ _ => False) (globalenv sem).

Lemma aux_div_step: forall s,
                     Forever_silent prune_semantics s ->
                     exists t, exists s', Step prune_semantics_aux s t s'.
Proof.
  inversion 1; subst. destruct H0.
  esplit. esplit. econstructor. eassumption. assumption. assumption.
Qed.

Lemma aux_star_div: forall s t s',
               Star prune_semantics_aux s t s' ->
               Forever_silent prune_semantics s ->
               Forever_silent prune_semantics s'.
Proof.
  induction 1.
   tauto.
  inversion H; subst; eauto.
Qed.

Lemma aux_behaves: forall s,
                     Forever_silent prune_semantics s ->
                     (exists t, state_behaves prune_semantics_aux s (Diverges t)) \/ (exists t, state_behaves prune_semantics_aux s (Reacts t)).
Proof.
  intros.
  destruct (state_behaves_exists prune_semantics_aux s).
  inversion H0; subst; eauto.
  contradiction.
  apply aux_star_div in H1.
  exploit aux_div_step. eassumption.
  destruct 1. destruct H4. edestruct H2. eassumption.
  assumption.
Qed.

Lemma aux_star_star:
  forall s t s',
    Star prune_semantics_aux s t s' ->
    Star sem s t s'.
Proof.
  induction 1.
   constructor.
  destruct H. econstructor; eauto.
Qed.

Lemma aux_silent_silent:
  forall s, 
    Forever_silent prune_semantics_aux s ->
    Forever_silent sem s.
Proof.
  cofix COINDHYP.
  destruct 1.
  destruct H.
  esplit. eassumption. eapply COINDHYP; clear COINDHYP; eauto.
Qed. 

Lemma aux_div_div:
  forall s t,
    state_behaves prune_semantics_aux s (Diverges t) ->
    state_behaves sem s (Diverges t).
Proof.
  inversion 1; subst.
  econstructor; eauto using aux_star_star, aux_silent_silent.
Qed.

Lemma aux_reacts_reacts:
  forall s t,
    Forever_reactive prune_semantics_aux s t ->
    Forever_reactive sem s t.
Proof.
  cofix COINDHYP.
  destruct 1.
  econstructor.
  eapply aux_star_star. eassumption.
  assumption.
  eapply COINDHYP; clear COINDHYP. assumption.
Qed.

Lemma aux_star_prune: forall s t s',
    Star prune_semantics_aux s t s' ->
    prune_trace t = E0.
Proof.
  induction 1.
   reflexivity.
  subst. destruct H. rewrite prune_trace_app. rewrite aux_step_prune0. rewrite IHstar. reflexivity.
Qed.

Lemma aux_reacts_all_call_return: forall s t,
                                Forever_reactive prune_semantics_aux s t ->
                                all_call_return t.
Proof.
  intros.
  apply all_call_return'_all_call_return.
  revert s t H.
  cofix COINDHYP.
  destruct 1.
   generalize (aux_star_prune _ _ _ H).
   intro.
   econstructor.
   eassumption.
   assumption.
   eapply COINDHYP; clear COINDHYP. eassumption.
   reflexivity.
Qed.

Theorem prune_state_behaves:
  forall s T, state_behaves prune_semantics s T ->
              exists t, prune_behavior t T /\
                        state_behaves sem s t.
Proof.
  inversion 1; subst.
   destruct (prune_star _ _ _ _ _ H0). destruct H2. subst. esplit. split. econstructor. reflexivity. econstructor. eassumption. assumption.
   destruct (prune_star _ _ _ _ _ H0). destruct H2. subst.
   destruct (aux_behaves _ H1).
    destruct H3.
    inversion H3; subst.
    generalize (aux_star_prune _ _ _ H5).
    intro.
    exists (Diverges (x ** x0)).
    split.
    econstructor.
    rewrite prune_trace_app. rewrite H4. unfold Eapp. rewrite <- app_nil_end. reflexivity.
    econstructor.
    eapply star_trans. eassumption. eapply aux_star_star. eassumption.
    reflexivity.
    eapply aux_silent_silent. assumption.
   destruct H3.
   inversion H3; subst.
   eexists (Reacts _).
   split.
   econstructor.
   econstructor.
   replace (prune_trace x) with (prune_trace x ** E0).
   eapply prune_traceinf_finite_app.
   econstructor.
   eapply aux_reacts_all_call_return.
   eassumption.
   unfold Eapp. rewrite <- app_nil_end. reflexivity.
   econstructor. eapply forever_reactive_app. eassumption. eapply aux_reacts_reacts. assumption.   
  exploit prune_infinite_reacts.
  eassumption.
  destruct 1.
  destruct H1.
  esplit.
  split.
  econstructor.
  econstructor.
  eassumption.
  econstructor.
  assumption.
 destruct (prune_star _ _ _ _ _ H0).
 destruct H3.
 subst.
 esplit. split. econstructor. 
 reflexivity.
 econstructor. eassumption.
 eapply prune_nostep. assumption.
 assumption.
Qed.

Theorem prune_program_behaves:
  forall T, program_behaves prune_semantics T ->
              exists t, prune_behavior t T /\
                        program_behaves sem t.
Proof.
  destruct 1.
   exploit prune_state_behaves. eassumption. destruct 1. destruct H1.
   esplit. split. eassumption. econstructor. eassumption. assumption.
  exists (Goes_wrong E0). split. econstructor. reflexivity. eright. assumption.
Qed.

End Semantics.                        


Lemma prune_match_traces:
  forall l1,  length l1 <= 1 ->
             forall {F V: Type} ge l2, Events.match_traces (F := F) (V := V) ge (prune_trace l1) l2 ->
                        exists l'2, Events.match_traces ge l1 l'2 /\
                                    l2 = prune_trace l'2.
Proof.
  destruct l1; simpl.
   inversion 2; subst.
   intros. exists nil; simpl; eauto.
  destruct l1; simpl.
  destruct e; simpl; inversion 2; subst; simpl;
  intros; try (esplit; split; try eassumption; reflexivity).
  esplit. split. econstructor. reflexivity.
  esplit. split. econstructor. reflexivity.
  intro. omegaContradiction.
Qed.

Lemma single_events_prune: forall 
                             (L : semantics)
                             (sr_traces : single_events L),
                             single_events (prune_semantics L).
Proof.
  intros. intro. destruct 1. subst.
  exploit sr_traces. eassumption.
  destruct t'; simpl.
   tauto.
  destruct e; destruct t'; simpl; try tauto; intros; try omegaContradiction; omega.
Qed.

Lemma receptive_prune:
  forall L,
    receptive L ->
    receptive (prune_semantics L).
Proof.
  inversion 1; subst; split.
  destruct 1.
  subst.
  intros.
  exploit (prune_match_traces).
  eapply sr_traces. eassumption. eassumption.
  destruct 1. destruct H1. subst.
  exploit sr_receptive.
  eassumption.
  eassumption.
  destruct 1.
  esplit. econstructor. eassumption. reflexivity.
  eauto using single_events_prune.
Qed.

Lemma forward_simulation_prune:
  forall L1 L2: semantics,
    forward_simulation L1 L2 ->
    forward_simulation (prune_semantics L1) (prune_semantics L2).
Proof.  
  inversion 1; subst.
  econstructor.
  eassumption.
  eassumption.
  assumption.
  destruct 1.
  subst.
  intros.
  exploit fsim_simulation.
   eassumption.
   eassumption.
  destruct 1.
  destruct H0.
  destruct H0.
  destruct H0.
   esplit. esplit. split. left. eapply plus_prune. eassumption. eassumption.
  destruct H0. esplit. esplit. split. right. split. eapply star_prune. eassumption. eassumption.
  assumption.
  assumption.
Qed.

Lemma match_traces_prune: 
  forall l1 l2 {F V: Type} ge, Events.match_traces (F := F) (V := V) ge l1 l2 ->
                               Events.match_traces ge (prune_trace l1) (prune_trace l2).
Proof.
  inversion 1; subst; simpl; constructor; auto.
Qed.

Lemma match_traces_prune_inj:
  forall l1 l2 {F V: Type} ge, Events.match_traces (F := F) (V := V) ge l1 l2 ->
                               prune_trace l1 = prune_trace l2 ->
                               l1 = l2.
Proof.
  inversion 1; subst; simpl; congruence.
Qed.

Lemma determinate_prune:
  forall L,
    determinate L ->
    determinate (prune_semantics L).
Proof.
  inversion 1; subst.
  constructor.
  destruct 1; subst.
  destruct 1; subst.
  exploit sd_determ. eexact Hstep. eexact Hstep0. destruct 1.
  exploit match_traces_prune; eauto.
  split; auto.
  intros; eauto using match_traces_prune_inj.
  eauto using single_events_prune.
  assumption.
  intros. eapply nostep_prune. eauto.
  assumption.
Qed.

Lemma prune_safe:
  forall L s,
    safe (prune_semantics L) s ->
    safe L s.
Proof.
  unfold safe. intros.
  generalize (star_prune _ _ _ _ _ H0).
  simpl.
  intro.
  exploit H.
  eassumption.
  destruct 1; auto.
  destruct H2.
  destruct H2.
  destruct H2.
  eauto.
Qed.

Lemma backward_simulation_prune:
  forall L1 L2: semantics,
    backward_simulation L1 L2 ->
    backward_simulation (prune_semantics L1) (prune_semantics L2).
Proof.  
  inversion 1; subst.
  esplit.
  eassumption.
  assumption.
  eassumption.
  intros.  
  exploit bsim_match_final_states.
  eassumption.
  eauto using prune_safe.
  eassumption.
  destruct 1. destruct H2.
  generalize (star_prune _ _ _ _ _ H2). simpl. eauto.
  intros. exploit bsim_progress. eassumption. eauto using prune_safe.
  destruct 1; auto.
  destruct H1. destruct H1.
  right. esplit. esplit. econstructor. eassumption. reflexivity.
  destruct 1. subst. intros. exploit bsim_simulation. eassumption. eassumption. eauto using prune_safe.
  destruct 1. destruct H1. destruct H1. destruct H1.
   esplit. esplit. split. left. eapply plus_prune. eassumption. eassumption.
   destruct H1. esplit. esplit. split. right. split. eapply star_prune. eassumption. eassumption. assumption.
   assumption.
Qed.

Lemma prune_not_stuck: forall L, not_stuck (prune_semantics L) -> not_stuck L.
Proof.
  unfold not_stuck.
  intros.
  destruct (prune_behavior_ex beh).
  generalize (program_behaves_prune _ _ H0 _ H1).
  intros.
  generalize (H _ H2).
  inversion H1; subst; simpl; tauto.
Qed.

Lemma not_stuck_prune: forall L, not_stuck L -> not_stuck (prune_semantics L).
Proof.
  unfold not_stuck.
  intros.
  destruct (prune_program_behaves _ _ H0).
  destruct H1.
  generalize (H _ H2).
  inversion H1; subst; simpl; try tauto.
  inversion Ht; subst; simpl; tauto.
Qed.

Lemma external_call_prune : forall {F V: Type} ef ge args m t res m',
 external_call (F := F) (V := V) ef ge args m t res m' ->
 prune_trace t = t.
Proof with subst; try reflexivity.
  destruct ef; simpl; inversion 1...
  inversion H0...
  inversion H0...
  inversion H1...
  inversion H1...
Qed.
