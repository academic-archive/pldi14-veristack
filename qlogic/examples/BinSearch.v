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

Section BINSEARCH.
Context (F: fid -> Z) (FNN: forall f, 0 <= F f).

(* size of the array *)
Context (size: Z).

Definition n_var   := givar u32 42.
Definition beg_var := givar u32 0.
Definition end_var := givar u32 size.
Definition arr_var: globvar type :=
  {| gvar_info := Tpointer u32 noattr
  ;  gvar_init := nil
  ;  gvar_readonly := false
  ;  gvar_volatile := false
  |}.

Definition n_id    := 1%positive.
Definition beg_id  := 2%positive.
Definition end_id  := 3%positive.
Definition arr_id  := 4%positive.
Definition srch_id := 5%positive.

Definition mid_id  := 1%positive.

Definition n_e   := Evar n_id u32.
Definition b_e   := Evar beg_id u32.
Definition e_e   := Evar end_id u32.
Definition arr_e := Evar arr_id (Tpointer u32 noattr).
Definition one_e := Econst_int (Int.repr 1) u32.
Definition dif_e := Ebinop Osub e_e b_e u32.
Definition mid_e := Ebinop Oadd b_e (Ebinop Oshr dif_e one_e u32) u32.
Definition get e :=
  Ederef (Ebinop Oadd (Evar arr_id (Tpointer u32 noattr))
                 e (Tpointer u32 noattr)) u32.

Definition srch_body :=
  (sseq (sif (Ebinop Ole dif_e one_e u32)
             (sret None)                        (* then *)
             (sskip))                           (* else *)
  (sseq (sif (Ebinop Ogt (get mid_e) n_e u32)
             (sgset e_e mid_e)                  (* then *)
             (sgset b_e mid_e))                 (* else *)
  (sseq (scall None srch_id nil)
        (sret None)
  ))).

Definition srch :=
  {| fi_name := srch_id
  ;  fi_locals := nil
  ;  fi_body := srch_body
  ;  fi_args := nil
  ;  fi_return := u32
  |}.

Definition ge: genv :=
  Genv.add_globals (@Genv.empty_genv _ _) (
    (beg_id, Gvar beg_var) ::
    (end_id, Gvar end_var) ::
    (arr_id, Gvar arr_var) ::
    (srch_id, Gfun srch) ::
    nil
  ).


(* evaluating program expressions *)
Definition int_val m id n :=
  glo_ival ge m id n /\ glo_typ ge id u32.

Lemma int_var_eval:
  forall m id n (IV: int_val m id n) s,
  eval_expr ge (cnf s m) (Evar id u32) (Vint n).
Proof. destruct 1. apply glo_ival_eval; auto. Qed.

Lemma eval_dif_e:
  forall m nb (HB: int_val m beg_id nb)
           ne (HE: int_val m end_id ne) s v,
  eval_expr ge (cnf s m) dif_e v ->
  v = Vint (Int.sub ne nb).
Proof.
intros; inv H.
replace v1 with (Vint ne) in *.
replace v2 with (Vint nb) in *.
inv H7. congruence.
symmetry; eapply eval_expr_fun.
 apply int_var_eval; eauto. eassumption.
symmetry; eapply eval_expr_fun.
 apply int_var_eval; eauto. eassumption.
inv H0.
Qed.

Lemma eval_mid_e:
  forall m nb (HB: int_val m beg_id nb)
           ne (HE: int_val m end_id ne) s v,
  eval_expr ge (cnf s m) mid_e v ->
  v = Vint (Int.add nb (Int.shru (Int.sub ne nb) Int.one)).
Proof.
intros; inv H.
replace v1 with (Vint nb) in *.
replace v2 with (Vint (Int.shru (Int.sub ne nb) Int.one)) in *.
inv H7. reflexivity.
clear H7.
inv H6.
replace v0 with (Vint (Int.sub ne nb)) in *.
inv H7.
inv H8.
Transparent Int.repr. reflexivity. Opaque Int.repr.
inv H.
symmetry; eapply eval_dif_e; eauto.
inv H.
symmetry; eapply eval_expr_fun.
 apply int_var_eval; eauto. eassumption.
inv H0.
Qed.

Lemma shiftr_one: forall z, Z.shiftr z 1 = z / 2.
Proof.
intros.
rewrite Z.shiftr_div_pow2 by omega.
rewrite Z.pow_1_r.
reflexivity.
Qed.

Lemma mid_bound:
  forall b e, b <= e ->
  b <= b + Z.shiftr (e - b) 1 <= e.
Proof.
intros.
rewrite shiftr_one.
rewrite <- Z.div_add_l by omega.
cut (e = 2 * e / 2). cut (b = 2 * b / 2).
intros B E.
rewrite B at 1; rewrite E at 3.
split; apply Z.div_le_mono; omega.
rewrite Z.mul_comm; symmetry.
apply Z.div_mul; omega.
rewrite Z.mul_comm; symmetry.
apply Z.div_mul; omega.
Qed.

Lemma uint_dif_e:
  forall ne nb, uint nb <= uint ne ->
  uint (Int.sub ne nb) = uint ne - uint nb.
Proof.
intros.

assert (0 <= uint ne - uint nb <= Int.max_unsigned).
{ unfold uint in *.
  generalize (Int.unsigned_range_2 ne).
  generalize (Int.unsigned_range_2 nb).
  intros; omega.
}

unfold uint, Int.sub in *.
repeat rewrite Int.unsigned_repr; eauto.
Qed.

Lemma uint_mid_e:
  forall ne nb, uint nb <= uint ne ->
  uint (Int.add nb (Int.shru (Int.sub ne nb) Int.one)) =
  uint nb + Z.shiftr (uint ne - uint nb) 1.
Proof.
intros.
generalize (uint_dif_e _ _ H). intro DIF.
generalize (mid_bound (uint nb) (uint ne) H). intro MID.
generalize (Int.unsigned_range_2 nb).
generalize (Int.unsigned_range_2 ne).
intros.

assert (0 <= Z.shiftr (uint (Int.sub ne nb)) 1 <= Int.max_unsigned).
{ unfold uint in *. rewrite DIF. omega. }
assert (0 <= uint nb + Z.shiftr (uint (Int.sub ne nb)) 1 <= Int.max_unsigned).
{ unfold uint in *. rewrite DIF. omega. }

unfold uint, Int.add, Int.shru in *.
repeat (rewrite Int.unsigned_repr; eauto).
rewrite DIF. reflexivity.
Qed.


(* bound proof *)
Definition fsz := F srch_id.

Definition lin n phi := n * fsz <= Z.of_nat phi.

Definition pre_cond z m (_: list val) phi :=
  exists nb ne,
  Int.cmpu Cle nb ne = true /\
  int_val m beg_id nb /\ int_val m end_id ne /\
  uint ne - uint nb <= 2^z /\ lin z phi.

Definition post_cond z (_: mem) (_: option val) phi :=
  lin z phi.

Theorem srch_valid:
  let pre  := enter Z ge F srch_id nil pre_cond (fun _ _ => True) in
  let post := leave Z ge F srch_id None post_cond (fun _ _ => True ) in
  forall n, valid _ ge F (S n) pre (scall None srch_id nil) post.
Proof.

(* destruct on steroids *)
Ltac destroids :=
  repeat match goal with
         | [ H: exists _, _ |- _ ] => destruct H
         | [ H: _ /\ _ |- _ ] => destruct H
         | [ H: True |- _ ] => clear H
         | [ H: False |- _ ] => elim H
         end.

simpl; intros.
eapply sound_call2; [exact FNN | | apply validC_empty ].
unfold validf; intros.
inv H0.

eapply sound_seq with
  (Q := fun o z c phi =>
    match o with
    | oskip => exists nb ne,
      int_val (c_mem c) beg_id nb /\ int_val (c_mem c) end_id ne /\
      uint ne - uint nb > 1 /\ uint ne - uint nb <= 2^z /\
      lin z phi
    | oret _ => lin z phi
    | _ => False end).
destruct o; intuition.

(* 1. proof of the first if statement *)
apply sound_if; intros [].

(* 1.1. then branch (nb - ne <= 1) *)
{ eapply weak_pre; [| apply sound_ret ].
  unfold ifP, pre_cond, lin; simpl; intuition.
  destruct H2 as [nb [ne ?]]. destroids.
  eauto.
}

(* 1.2 else branch (nb - ne > 1) *)
{ eapply weak_pre; [| apply sound_skip ].
  unfold ifP, pre_cond; simpl; intuition.
  destruct H2 as [_ [_ [nb [ne ?]]]]; destroids.
  exists nb; exists ne; intuition.
  inv H1.
  replace v1 with (Vint (Int.sub ne nb)) in *.
  replace v2 with (Vint Int.one) in *.
  inv H15.
  unfold Int.ltu in *.
  fold (uint Int.one) in *.
  rewrite uint_one_e in *.
  rewrite uint_dif_e in *.
  destruct (zlt 1 (uint ne - uint nb)).
  omega.
  rewrite <- H8, H7 in H6; inv H6.
  apply cle_le; assumption.
  inv H14. reflexivity. inv H1.
  symmetry; eapply eval_dif_e; eauto.
  inv H8.
}

apply sound_seq with
  (Q := fun o z c phi =>
    match o with
    | oskip => exists nb ne,
      int_val (c_mem c) beg_id nb /\ int_val (c_mem c) end_id ne /\
      uint ne - uint nb <= 2^(z-1) /\ uint nb <= uint ne /\
      0 < z /\ lin z phi
    | _ => False end).
destruct o; intuition.

(* 2. proof of the second if *)
apply sound_if; intros [].

(* 2.1. search in left sub-array *)
{ eapply weak_pre; [| apply sound_gset ].
  unfold ifP; simpl in *; intuition.
  clear H1.
  destruct H2 as [nb [ne ?]]; destroids.
  pose (mid := Int.add nb (Int.shru (Int.sub ne nb) Int.one)).
  exists nb; exists mid.
  assert (0 < z).
  { apply pow_gt_one; omega. }
  intuition.

  admit. admit. (* Clight memory proofs omitted *)

  unfold mid; rewrite uint_mid_e by omega.
  replace (uint nb + Z.shiftr (uint ne - uint nb) 1 - uint nb)
     with (Z.shiftr (uint ne - uint nb) 1) by omega.
  rewrite shiftr_one.
  apply dichot; omega.

  unfold mid; rewrite uint_mid_e by omega.
  exploit (mid_bound (uint nb) (uint ne)); omega.
}

(* 2.2 search in right sub-array *)
{ eapply weak_pre; [| apply sound_gset ].
  unfold ifP; simpl in *; intuition.
  clear H1.
  destruct H2 as [nb [ne ?]]; destroids.
  exists (Int.add nb (Int.shru (Int.sub ne nb) Int.one)); exists ne.
  assert (0 < z).
  { apply pow_gt_one; omega. }
  intuition.

  admit. admit. (* Clight memory proofs omitted *)

  rewrite uint_mid_e by omega.
  pose (d := uint ne - uint nb).
  rewrite shiftr_one.
  replace (uint ne - (uint nb + (uint ne - uint nb) / 2))
     with (d - d/2) by (unfold d; omega).
  destruct (zeq (d mod 2) 0).
  rewrite splitl; eauto.
  apply dichot; unfold d in *; omega.
  rewrite splitr; eauto.
  apply dichot; unfold d in *; omega.

  rewrite uint_mid_e by omega.
  exploit (mid_bound (uint nb) (uint ne)); omega.
}

apply sound_seq with
  (Q := fun o z _ phi =>
    match o with obreak => False | _ => lin z phi end).
destruct o; intuition.

(* 3. proof of the recursive call *)
{ eapply sound_consequence;
   [| eapply sound_call1;
      eauto; try reflexivity ].
  instantiate (1 := fun _ _ => True).
  unfold wk, enter, leave, pre_cond, post_cond, pls, lin;
   simpl; intuition.
  destruct H0 as [nb [ne ?]]; destroids.
  exists (z - 1); intuition.
  + assert (0 <= Z.of_nat r - fsz).
    { cut (fsz <= Z.of_nat r). intro; omega.
      replace fsz with (1 * fsz) by omega.
      eapply Zle_trans; [| eauto ].
      apply Z.mul_le_mono_nonneg_r.
      apply FNN.
      omega.
    }
    exists (Z.to_nat (Z.of_nat r - fsz)); split.
    split; [| trivial ].
    exists nb; exists ne; intuition.
    apply le_cle; assumption.
    rewrite Z2Nat.id by eauto.
    rewrite Z.mul_sub_distr_r. omega.
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_add; fold fsz.
    rewrite Z2Nat.id by eauto.
    rewrite Z2Nat.id by (apply FNN).
    omega.
  + destruct o; try contradiction.
    destruct H6 as [k [? ?]]; destroids.
    subst.
    rewrite Nat2Z.inj_add; fold fsz.
    rewrite Z.mul_sub_distr_r in H8.
    rewrite Z2Nat.id by (apply FNN).
    omega.
}

(* 4. proof of the final return *)
{ eapply weak_pre; [| apply sound_ret ].
  unfold post_cond; simpl; intuition.
}
Qed.

End BINSEARCH.
