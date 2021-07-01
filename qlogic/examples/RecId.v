(************************************************************************)
(*                                                                      *)
(*                Quantitative Hoare Logic for Clight                   *)
(*                                                                      *)
(*  Author: Quentin Carbonneaux (c) 2014              Yale University   *)
(*                                                                      *)
(************************************************************************)


Add LoadPath "..".
Require Import Coqlib.
Require Import Common.

(* demonstration program *)
Section RECID.
Context (F: fid -> Z) (FNN: forall f, 0 <= F f).

Definition a_var := givar i32 42.
Definition b_var := givar i32 0.
Definition a_id := 1%positive.
Definition b_id := 2%positive.

Definition globals: list ident := a_id :: b_id :: nil.

Definition f_id := 3%positive.
Definition f_body :=
  let a    := Evar a_id i32 in
  let b    := Evar b_id i32 in
  let one  := Econst_int (Int.repr 1) i32 in
  let zero := Econst_int (Int.repr 0) i32 in
  (* function body *)
  sif a
      (* then *)
      (sseq (sgset a (Ebinop Osub a one i32))
      (sseq (sgset b (Ebinop Oadd b one i32))
      (sseq (scall None f_id nil)
            (sret (Some zero)))))
      (* else *)
      (sret (Some zero)).
Definition f_fi: finfo :=
  {| fi_name := f_id
  ;  fi_locals := nil
  ;  fi_body := f_body
  ;  fi_args := nil
  ;  fi_return := i32
  |}.

Definition ge: genv :=
  Genv.add_globals (@Genv.empty_genv _ _)
    ((a_id, Gvar a_var) :: (b_id, Gvar b_var) :: (f_id, Gfun f_fi) :: nil).

(* take int * int as auxiliary variables *)
Definition aux := (int * int)%type.

(* helper lemmas *)
Lemma globals_type:
  forall id, In id globals -> glo_typ ge id i32.
Proof.
intros.
destruct H as [? | [? | ? ]];
 try elim H; subst;
 eexists; split; reflexivity.
Qed.

Definition glo_val m id n := In id globals /\ glo_ival ge m id n.

Lemma glo_val_eval:
  forall id m n (GV: glo_val m id n) s,
  eval_expr ge (cnf s m) (Evar id i32) (Vint n).
Proof.
destruct 1; intros; apply glo_ival_eval;
 auto using globals_type.
Qed.


Definition linear idf x phi :=
  Int.signed x >= 0 /\
  Z.of_nat phi >= Int.signed x * F idf.

(* verification conditions *)
Definition pre_cond := fun z m (_: list val) phi =>
  glo_val m a_id (fst z) /\
  glo_val m b_id (snd z) /\
  linear f_id (fst z) phi.

Definition post_cond := fun z m (_: option val) phi =>
  glo_val m a_id Int.zero /\
  glo_val m b_id (Int.add (fst z) (snd z)) /\
  linear f_id (fst z) phi.

(* verification theorem *)
Theorem f_valid:
  let pre  := enter aux ge F f_id nil pre_cond (fun _ _ => True) in
  let post := leave aux ge F f_id None post_cond (fun _ _ => True ) in
  forall n, valid _ ge F (S n) pre (scall None f_id nil) post.
Proof.

Ltac destroids :=
  repeat match goal with
         | [ H: exists _, _ |- _ ] => destruct H
         | [ H: _ /\ _ |- _ ] => destruct H
         | [ H: True |- _ ] => clear H
         | [ H: False |- _ ] => elim H
         end.

simpl; intros.
eapply sound_call2; [ exact FNN | | apply validC_empty ].
unfold validf; intros.
inv H0.
apply sound_if; intros [].

(* 1. correctness of the 'then' branch *)
apply weak_pre with
  (P := fun z c phi =>
    glo_val (c_mem c) a_id (fst z) /\
    glo_val (c_mem c) b_id (snd z) /\
    linear f_id (fst z) phi /\
    0 < Int.signed (fst z)).

(* we prove that a > 0 in the 'then' branch *)
{ unfold ifP, pre_cond; simpl. intros.
  destruct H0 as [[v' [[EVALV' EVALTY] BOOLVAL]] ?].
  destroids. intuition.
  assert (fst z <> Int.zero). intro.
  exploit eval_expr_fun.
  eapply glo_val_eval; eexact H1.
  eexact EVALV'.
  intro Hv'; rewrite Hv' in BOOLVAL.
  unfold bool_val in BOOLVAL.
  rewrite EVALTY, H4 in BOOLVAL.
  inv BOOLVAL.
  destruct (zeq (Int.signed (fst z)) 0).
  exfalso; apply H4.
  rewrite <- (Int.repr_signed (fst z)).
  unfold Int.zero; congruence.
  destruct H3; simpl in *; omega.
}

apply sound_seq with
  (Q := fun o z c phi =>
    match o with
    | oskip =>
      glo_val (c_mem c) a_id (Int.sub (fst z) Int.one) /\
      glo_val (c_mem c) b_id (snd z) /\
      linear f_id (fst z) phi /\
      0 < Int.signed (fst z)
    | _ => False end).
destruct o; intuition. (* post condition for return implication *)

(* 1.1 correctness of the first assignment *)
{ eapply weak_pre; [| apply sound_gset ].
  simpl; intuition.
  admit. admit.
}

apply sound_seq with
  (Q := fun o z c phi =>
    match o with
    | oskip =>
      glo_val (c_mem c) a_id (Int.sub (fst z) Int.one) /\
      glo_val (c_mem c) b_id (Int.add (snd z) Int.one) /\
      linear f_id (fst z) phi /\
      0 < Int.signed (fst z)
    | _ => False end).
destruct o; intuition. (* post condition for return implication *)

(* 1.2 correctness of the second assignment *)
{ eapply weak_pre; [| apply sound_gset ].
  simpl; intuition.
  admit. admit.
}

apply sound_seq with
  (Q := fun o z c phi =>
    match o with
    | oskip =>
      glo_val (c_mem c) a_id Int.zero /\
      glo_val (c_mem c) b_id (Int.add (fst z) (snd z)) /\
      linear f_id (fst z) phi
    | _ => False end).
destruct o; intuition. (* post condition for return implication *)

(* 1.3 correctness of the call statement *)
eapply sound_consequence;
 [| eapply sound_call1;
    eauto; try reflexivity ].
{ instantiate (1 := fun _ _ => True).
  unfold wk, enter, leave, pls, pre_cond, post_cond, linear.
  intro; exists (Int.sub (fst z) Int.one, Int.add (snd z) Int.one).
  destruct z as [a b]; intuition; simpl in *.
  assert (SUBEQ: Int.signed (Int.sub a Int.one) = Int.signed a - 1).
  rewrite Int.sub_signed.
  erewrite Int.signed_repr.
  rewrite signed_one.
  reflexivity.
  rewrite signed_one.
  assert (Int.signed a <= Int.max_signed)
   by (apply Int.signed_range).
  assert (Int.min_signed < 0)
   by (apply Int.min_signed_neg).
  split; omega.
  assert (FRAME: le (Z.to_nat (F f_id)) r).
  set (fr := F f_id) in *.
  assert (Int.signed a * fr >= 1 * fr).
  { apply Zmult_ge_compat_r. omega.
    unfold fr; generalize (FNN f_id); omega.
  }
  apply Nat2Z.inj_le. rewrite Z2Nat.id by (apply FNN). omega.
  exists (r - Z.to_nat (F f_id))%nat; intuition.
  rewrite SUBEQ, Z.mul_sub_distr_r.
  erewrite Nat2Z.inj_sub.
  rewrite Z2Nat.id by auto.
  omega. omega.

  destruct o; destroids; simpl in *; intuition.
  replace (Int.add a b)
     with (Int.add (Int.sub a Int.one) (Int.add b Int.one)).
  assumption.
  rewrite <- Int.sub_add_l.
  rewrite <- Int.add_assoc.
  rewrite Int.add_commut.
  rewrite Int.sub_add_l.
  rewrite Int.sub_idem.
  rewrite Int.add_zero_l.
  reflexivity.
  rewrite H6, Nat2Z.inj_add.
  replace (Int.signed a)
     with (Int.signed (Int.sub a Int.one) + 1).
  rewrite Z.mul_add_distr_r. rewrite Z2Nat.id by (apply FNN). omega.
  rewrite Int.sub_signed.
  rewrite Int.signed_repr.
  rewrite signed_one.
  omega.
  rewrite signed_one.
  assert (Int.signed a <= Int.max_signed)
   by (apply Int.signed_range).
  generalize Int.min_signed_neg.
  split; omega.
}

(* 1.4 correctness of the return statement *)
{ eapply weak_pre; [| apply sound_ret ].
  unfold post_cond; intuition.
}

(* 2. correctness of the 'else' branch *)
clear.
apply weak_pre with
  (P := fun z c phi =>
    glo_val (c_mem c) a_id (fst z) /\
    glo_val (c_mem c) b_id (snd z) /\
    linear f_id (fst z) phi /\
    fst z = Int.zero).

(* we prove that a == 0 in the 'else' branch *)
{ unfold ifP, post_cond, pre_cond.
  intros. destruct c.
  destruct H as [[v' [EVALV' BOOLVAL]] ?].
  destroids. intuition.
  exploit eval_expr_fun.
  eapply glo_val_eval; eexact H0.
  eapply EVALV'.
  simpl in BOOLVAL.
  intro FST. rewrite FST, (proj2 EVALV') in BOOLVAL.
  inv BOOLVAL.
  assert (Int.eq (fst z) Int.zero = true)
   by (apply negb_false_iff; assumption).
  apply eq_spec'.
  assumption.
}

(* 2.1 correctness of the return statement *)
{ eapply weak_pre; [| apply sound_ret ].
  unfold post_cond; intuition.
  rewrite H3 in H0; eauto.
  rewrite H3.
  rewrite Int.add_zero_l; eauto.
}
Qed.

End RECID.
