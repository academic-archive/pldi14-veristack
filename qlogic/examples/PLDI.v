(************************************************************************)
(*                                                                      *)
(*                Quantitative Hoare Logic for Clight                   *)
(*                                                                      *)
(*  Author: Quentin Carbonneaux (c) 2014              Yale University   *)
(*                                                                      *)
(************************************************************************)


(* Sample proof using both automation
   and manual proofs to get a bound
   on the stack consumption of a complete
   program using recursion.
*)

Add LoadPath "..".
Require Import Coqlib.
Require Import Common.

Section PLDI.
Context (F: fid -> Z) (FNN: forall f, 0 <= F f).

(* --- Program parameters, left abstract. *)
Context (ALEN: Z).
Context (SEED: Z).

Hypothesis (ALEN_POS: 0 < ALEN).
Hypothesis (ALEN_MAX: ALEN <= Int.max_unsigned).



(* ---- BEGINNING OF THE PROGRAM DEFINITION ---- *)

(* --- Global variables a and seed *)

Definition a_var: globvar type :=
  {| gvar_info := Tpointer u32 noattr
  ;  gvar_init := nil
  ;  gvar_readonly := false
  ;  gvar_volatile := false
  |}.
Definition seed_var := givar u32 SEED.


(* --- Variable Identifiers *)

(* -- globals *)
Definition a_id      := 1%positive.
Definition seed_id   := 2%positive.
Definition search_id := 3%positive.
Definition random_id := 4%positive.
Definition init_id   := 5%positive.
Definition main_id   := 6%positive.

(* -- search locals *)
Definition elem_id := 1%positive.
Definition beg_id  := 2%positive.
Definition end_id  := 3%positive.
Definition res_id  := 4%positive.

(* -- init locals *)
Definition i_id    := 1%positive.
Definition rnd_id  := 2%positive.
Definition prev_id := 3%positive.

(* -- main locals *)
(* Definition elem_id := 1%positive. *) (* already defined *)
Definition idx_id  := 2%positive.

(* --- Search Function Expressions *)

(* general purpose expressions *)
Definition one_e := Econst_int (Int.repr 1) u32.
Definition two_e := Econst_int (Int.repr 2) u32.

(* variable expressions *)
Definition elem_e := Etempvar elem_id u32.
Definition beg_e  := Etempvar beg_id u32.
Definition end_e  := Etempvar end_id u32.
Definition res_e  := Etempvar res_id u32.

Definition get e := (* a[e] *)
  Ederef (Ebinop Oadd (Evar a_id (Tpointer u32 noattr)) e
                 (Tpointer u32 noattr)) u32.
Definition dif_e := (* end - beg *)
  Ebinop Osub end_e beg_e u32.
Definition mid_e := (* (end - beg) / 2 *)
  Ebinop Oadd beg_e (Ebinop Odiv dif_e two_e u32) u32.


(* --- Search Function Definition *)

Definition search_body :=
  (sseq (sif (Ebinop Ole dif_e one_e u32)
             (sret (Some beg_e))                (* then *)
             (sskip))                           (* else *)
  (sseq (sif (Ebinop Ogt (get mid_e) elem_e u32)
             (slset end_id mid_e)               (* then *)
             (slset beg_id mid_e))              (* else *)
  (sseq (scall (Some res_id) search_id (elem_e :: beg_e :: end_e :: nil))
        (sret (Some res_e))
  ))).

Definition search :=
  {| fi_name := search_id
  ;  fi_locals := (res_id, u32) :: nil
  ;  fi_body := search_body
  ;  fi_args := (elem_id, u32) :: (beg_id, u32) :: (end_id, u32) :: nil
  ;  fi_return := u32
  |}.


(* --- Random Function Expressions *)

(* integer constants *)
Definition a_e := Econst_int (Int.repr 1664525) u32.
Definition c_e := Econst_int (Int.repr 1013904223) u32.

(* variable expressions *)
Definition seed_e := Evar seed_id u32.

Definition seed_update_e := (* seed * 1664525) + 1013904223 *)
  Ebinop Oadd (Ebinop Omul seed_e a_e u32) c_e u32.


(* --- Random Function Definition *)

Definition random_body :=
  (sseq (sgset seed_e seed_update_e)
        (sret (Some seed_e))).

Definition random :=
  {| fi_name := random_id
  ;  fi_locals := nil
  ;  fi_body := random_body
  ;  fi_args := nil
  ;  fi_return := u32
  |}.


(* --- Init Function Expressions *)

(* integer constants *)
Definition zero_e      := Econst_int (Int.repr 0) u32.
Definition seventeen_e := Econst_int (Int.repr 17) u32.
Definition ALEN_e      := Econst_int (Int.repr ALEN) u32.

(* variable expressions *)
Definition i_e    := Etempvar i_id u32.
Definition rnd_e  := Etempvar rnd_id u32.
Definition prev_e := Etempvar prev_id u32.

Definition ai_e := (* prev + rnd % 17 *)
  Ebinop Oadd prev_e (Ebinop Omod rnd_e seventeen_e u32) u32.


(* --- Init Function Definition *)

Definition init_body :=
  (sseq (slset i_id zero_e)
  (sseq (slset prev_id zero_e)

  (sseq (sloop
        (sif (Ebinop Olt i_e ALEN_e u32)

             (sseq (scall (Some rnd_id) random_id nil)
             (sseq (sgset (get i_e) ai_e)
             (sseq (slset prev_id (get i_e))
                   (slset i_id (Ebinop Oadd i_e one_e u32))
             )))

             sbreak))

        (sret None)
  ))).

Definition init :=
  {| fi_name := init_id
  ;  fi_locals := (i_id, u32) :: (rnd_id, u32) :: (prev_id, u32) :: nil
  ;  fi_body := init_body
  ;  fi_args := nil
  ;  fi_return := Tvoid
  |}.


(* --- Main Function Expressions *)

(* variable expressions *)
Definition idx_e := Etempvar idx_id u32.

Definition elem'_e := (* elem % (17 * ALEN) *)
  Ebinop Omod elem_e (Ebinop Omul seventeen_e ALEN_e u32) u32.


(* --- Main Function Definition *)

Definition main_body :=
  (sseq (scall None init_id nil)
  (sseq (scall (Some elem_id) random_id nil)
  (sseq (slset elem_id elem'_e)
  (sseq (scall (Some idx_id) search_id (elem_e :: zero_e :: ALEN_e :: nil))
        (sret (Some (Ebinop Oeq (get idx_e) elem_e i32)))
  )))).

Definition main :=
  {| fi_name := main_id
  ;  fi_locals := (elem_id, u32) :: (idx_id, u32) :: nil
  ;  fi_body := main_body
  ;  fi_args := nil
  ;  fi_return := i32
  |}.


(* --- Full Program Definition *)

Definition pldi_program :=
  {| prog_main := main_id
  ;  prog_defs :=
       (a_id, Gvar a_var) ::
       (seed_id, Gvar seed_var) ::
       (search_id, Gfun search) ::
       (random_id, Gfun random) ::
       (init_id, Gfun init) ::
       (main_id, Gfun main) ::
       nil
  |}.

Notation "'ge'" := (Genv.globalenv pldi_program) (only parsing).
(* Let ge := Genv.globalenv pldi_program. *)



(* ---- BEGINNING OF STACK BOUND PROOF ---- *)
Require Import Maps.


(* --- Manual Proof For The Search Function *)

(* Integer definitions *)
Definition itwo := Int.repr 2.

Lemma eval_const:
  forall c n v (EVAL: eval ge c (Econst_int n u32) v),
  v = (Vint n, u32).
Proof.
intros. inv EVAL. inv H. destruct v. simpl in *; congruence.
inv H1.
Qed.

(* local s id n:
   id is an integer local variable whose value is n
*)
Definition local s id n := s!id = Some (Vint n).

Lemma local_eval_expr:
  forall s id n (LOC: local s id n) m,
  eval_expr ge (cnf s m) (Etempvar id u32) (Vint n).
Proof. constructor. assumption. Qed.

Lemma local_eval:
  forall s id n (LOC: local s id n) m
         v (EVAL: eval ge (cnf s m) (Etempvar id u32) v),
  v = (Vint n, u32).
Proof.
simpl; intuition.
destruct v; f_equal; auto.
eapply Clight.eval_expr_determ; eauto.
apply local_eval_expr; auto.
Qed.

Lemma eval_dif_e:
  forall s nb (HB: local s beg_id nb)
           ne (HE: local s end_id ne)
         m v,
  eval_expr ge (cnf s m) dif_e v ->
  v = Vint (Int.sub ne nb).
Proof.
intros; inv H.
replace v1 with (Vint ne) in *.
replace v2 with (Vint nb) in *.
inv H7. congruence.
eapply Clight.eval_expr_determ; eauto.
 apply local_eval_expr; eauto.
eapply Clight.eval_expr_determ; eauto.
 apply local_eval_expr; eauto.
inv H0.
Qed.

Lemma eval_mid_e:
  forall s nb (HB: local s beg_id nb)
           ne (HE: local s end_id ne)
         m v,
  eval_expr ge (cnf s m) mid_e v ->
  v = Vint (Int.add nb (Int.divu (Int.sub ne nb) itwo)).
Proof.
intros; inv H.
replace v1 with (Vint nb) in *.
replace v2 with (Vint (Int.divu (Int.sub ne nb) itwo)) in *.
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
eapply Clight.eval_expr_determ; eauto.
 apply local_eval_expr; eauto.
inv H0.
Qed.

Lemma mid_bound:
  forall b e, b <= e ->
  b <= b + (e - b) / 2 <= e.
Proof.
intros.
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
  uint (Int.add nb (Int.divu (Int.sub ne nb) two)) =
  uint nb + (uint ne - uint nb) / 2.
Proof.
intros.
generalize (uint_dif_e _ _ H). intro DIF.
generalize (mid_bound (uint nb) (uint ne) H). intro MID.
generalize (Int.unsigned_range_2 nb).
generalize (Int.unsigned_range_2 ne).
intros.

assert (0 <= uint (Int.sub ne nb) / 2 <= Int.max_unsigned).
{ unfold uint in *. rewrite DIF. omega. }
assert (0 <= uint nb + uint (Int.sub ne nb) / 2 <= Int.max_unsigned).
{ unfold uint in *. rewrite DIF. omega. }

unfold uint, Int.add, Int.divu in *.
repeat (rewrite Int.unsigned_repr; eauto).
rewrite DIF. reflexivity.
Qed.


(* -- specification of the search function *)

Definition linear n phi := n * F search_id <= Z.of_nat phi.

Definition search_pre z (_: mem) args phi :=
  exists velm ne nb,
    args = velm :: (Vint nb, u32) :: (Vint ne, u32) :: nil /\
    Int.cmpu Cle nb ne = true /\        (* nb <= be *)
    uint ne - uint nb <= 2 ^ z /\       (* ne - nb <= 2 ^ z *)
    linear z phi.                       (* search is linear in z *)

Definition search_post z (_: mem) (_: option val) phi :=
  linear z phi.

Theorem call_search_valid:
  forall retv elem_e beg_e end_e n,
  let args := elem_e :: beg_e :: end_e :: nil in
  let pre :=
    enter Z ge F search_id args search_pre (fun _ _ => True) in
  let post :=
    leave Z ge F search_id retv search_post (fun _ _ => True) in

  valid _ ge F (S n)
        pre (scall retv search_id args) post.
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
eapply sound_call2; [ exact FNN | | apply validC_empty ].
unfold validf; intros.
inv H0.

eapply sound_seq with
  (Q := fun o z c phi =>
    match o with
    | oskip => exists nb ne,
      local (c_stack c) beg_id nb /\ local (c_stack c) end_id ne /\
      uint ne - uint nb > 1 /\ uint ne - uint nb <= 2 ^ z /\
      linear z phi
    | oret _ => linear z phi
    | _ => False end).
destruct o; auto.

(* 1. proof of the first if statement *)
apply sound_if; intros [].

(* 1.1. then branch (nb - ne <= 1) *)
{ eapply weak_pre; [| apply sound_ret ].
  unfold ifP, linear, search_pre; simpl; intuition.
  destroids; eauto.
}

(* 1.2 else branch (nb - ne > 1) *)
{ eapply weak_pre; [| apply sound_skip ].
  unfold ifP, search_pre; simpl; intuition.
  destruct H2 as [? [? [velm [ne [nb ?]]]]]. destroids.

  (* retreive the shape of the initial stack *)
  inv H0.
  assert (SRCH: Some search = Some fi) by assumption.
  replace fi with search in * by congruence. clear SRCH.
  repeat match goal with
  | [ H: castl _ _ _ |- _ ] => inv H
  | [ H: val_cast (Vint _, _) _ = Some _ |- _ ] => inv H
  end.
  inv H12.

  assert (LOCBEG: local (c_stack c) beg_id nb).
  { unfold stack,temp_env in *.
    rewrite <- H2. reflexivity. }
  assert (LOCEND: local (c_stack c) end_id ne).
  { unfold stack,temp_env in *.
    rewrite <- H2. reflexivity. }
  clear H8 H9 H10 H2 H16.

  exists nb; exists ne; intuition.
  inv H1.
  replace v1 with (Vint (Int.sub ne nb)) in *.
  replace v2 with (Vint Int.one) in *.
  inv H13.
  unfold Int.ltu in *.
  fold (uint Int.one) in *.
  rewrite uint_one_e in *.
  rewrite uint_dif_e in *.
  destruct (zlt 1 (uint ne - uint nb)).
  omega.
  rewrite <- H1, H7 in H6; inv H6.
  apply cle_le; assumption.
  inv H12. reflexivity. inv H0.
  symmetry; eapply eval_dif_e; eauto.
  inv H0.
}

apply sound_seq with
  (Q := fun o z c phi =>
    match o with
    | oskip => exists nb ne,
      local (c_stack c) beg_id nb /\ local (c_stack c) end_id ne /\
      uint ne - uint nb <= 2 ^ (z-1) /\ uint nb <= uint ne /\
      0 < z /\ linear z phi
    | _ => False end).
destruct o; intuition.

(* 2. proof of the second if *)
apply sound_if; intros [].

(* 2.1. search in left sub-array *)
{ eapply weak_pre; [| apply sound_lset ].
  unfold ifP; simpl in *; intuition.
  clear H1. (* we don't care about functional correctness *)
  destruct H2 as [nb [ne ?]]; destroids.
  pose (mid := Int.add nb (Int.divu (Int.sub ne nb) two)).
  exists nb; exists mid.
  assert (0 < z).
  { apply pow_gt_one; omega. }

  inv H3.
  repeat split; auto; unfold local.

  rewrite PTree.gso. assumption.
  unfold beg_id, end_id; congruence.
  rewrite PTree.gss.
  f_equal. eapply eval_mid_e; eauto.

  unfold mid; rewrite uint_mid_e by omega.
  replace (uint nb + (uint ne - uint nb) / 2 - uint nb)
     with ((uint ne - uint nb) / 2) by omega.
  apply dichot; omega.

  unfold mid; rewrite uint_mid_e by omega.
  exploit (mid_bound (uint nb) (uint ne)); omega.
}

(* 2.2 search in right sub-array *)
{ eapply weak_pre; [| apply sound_lset ].
  unfold ifP; simpl in *; intuition.
  clear H1. (* we don't care about functional correctness *)
  destruct H2 as [nb [ne ?]]; destroids.
  pose (mid := Int.add nb (Int.divu (Int.sub ne nb) two)).
  exists mid; exists ne.
  assert (0 < z).
  { apply pow_gt_one; omega. }

  inv H3.
  repeat split; auto; unfold local.

  rewrite PTree.gss.
  f_equal. eapply eval_mid_e; eauto.
  rewrite PTree.gso. assumption.
  unfold beg_id, end_id; congruence.

  unfold mid; rewrite uint_mid_e by omega.
  pose (d := uint ne - uint nb).
  replace (uint ne - (uint nb + (uint ne - uint nb) / 2))
     with (d - d/2) by (unfold d; omega).
  destruct (zeq (d mod 2) 0).
  rewrite splitl; eauto.
  apply dichot; unfold d in *; omega.
  rewrite splitr; eauto.
  apply dichot; unfold d in *; omega.

  unfold mid; rewrite uint_mid_e by omega.
  exploit (mid_bound (uint nb) (uint ne)); omega.
}

apply sound_seq with
  (Q := fun o z _ phi =>
    match o with obreak => False | _ => linear z phi end).
destruct o; intuition.

(* 3. proof of the recursive call *)
{ eapply sound_consequence;
   [| eapply sound_call1;
      eauto; try reflexivity ].
  instantiate (1 := fun _ _ => True).
  unfold wk, enter, leave, search_post, pls, linear;
   simpl; intuition.
  destruct H0 as [nb [ne ?]]; destroids.
  exists (z - 1); intuition.
  + assert (0 <= Z.of_nat r - F search_id).
    { cut (F search_id <= Z.of_nat r). intro; omega.
      replace (F search_id) with (1 * F search_id) by omega.
      eapply Zle_trans; [| eauto ].
      apply Z.mul_le_mono_nonneg_r.
      apply FNN.
      omega.
    }
    exists (Z.to_nat (Z.of_nat r - F search_id)); split.
    split; [| trivial ].
    repeat match goal with
      | [ H: evall _ _ _ _ |- _ ] => inv H end.
    exists v. exists ne. exists nb.
    destruct cp.
    repeat split; auto.
    repeat f_equal; eauto using local_eval.
    apply le_cle; assumption.
    unfold linear.
    rewrite Z2Nat.id by eauto.
    rewrite Z.mul_sub_distr_r. omega.
    apply Nat2Z.inj.
    rewrite Nat2Z.inj_add.
    rewrite Z2Nat.id by eauto.
    rewrite Z2Nat.id by (apply FNN).
    omega.
  + destruct o; try contradiction.
    destruct H6 as [k [? ?]]; destroids.
    subst.
    rewrite Nat2Z.inj_add.
    rewrite Z.mul_sub_distr_r in H8.
    rewrite Z2Nat.id by (apply FNN).
    omega.
}

(* 4. proof of the final return *)
{ eapply weak_pre; [| apply sound_ret ].
  unfold search_post; simpl; intuition.
}
Qed.


(* --- Automatic Proof For The Random And Init Functions *)
Require Import AutoBound.

Remark B_random_body:
  B F (fun _ => None) random_body = Some 0.
Proof. reflexivity. Qed.

Theorem random_body_valid:
  forall n, validf Z ge F n
                   (fun_pre 0) random_id (fun_post 0).
Proof.
unfold validf; intros.
inv H.
eapply sound_consequence; [| eapply sound_B; auto ].
4: apply B_random_body.
3: red; red; discriminate.
2: discriminate.
unfold wk, fun_pre, fun_post; intuition.
destruct H as [_ [_ ?]].
exists 0; intuition.
destruct o; intuition.
Qed.

Definition bctx_random fid :=
  if peq fid random_id then Some 0 else None.

Lemma valid_bctx_random:
  valid_bctx (aux := Z) F pldi_program bctx_random.
Proof.
unfold valid_bctx, mkctx, bctx_random, validC.
intros until Qg.
destruct (peq f random_id); try discriminate.
injection 1; intros; subst.
apply random_body_valid.
Qed.

(* useful rewriting lemmas to deal with automatic bound derivation *)
Lemma Zmax_0_0: Z.max 0 0 = 0. Proof. reflexivity. Qed.
Lemma Zmax_F_0: forall f, Z.max (F f) 0 = F f.
Proof. auto using Z.max_l. Qed.
Lemma Zmax_0_F: forall f, Z.max 0 (F f) = F f.
Proof. auto using Z.max_r. Qed.
Hint Rewrite Zmax_0_0 Z.add_0_r Z.add_0_l Zmax_0_F Zmax_F_0: B.

Remark B_init_body: B F bctx_random init_body = Some (F random_id).
Proof.
unfold init_body, bctx_random.
simpl.
destruct (peq random_id random_id); try congruence.
simpl. autorewrite with B. reflexivity.
Qed.

(* Prove a bound for the body of the init function
   using automation! We use the bctx_random lemma
   to provide a bound for the random function call.

   The lemma is stated in a form that allows easy
   reuse with the call2 rule of the logic.
*)
Theorem init_body_valid:
  forall n, validf Z ge F n
                   (fun_pre (F random_id)) init_id (fun_post (F random_id)).
Proof.
unfold validf; intros.
inv H.
eapply sound_consequence; [| eapply sound_B; eauto ].
4: apply B_init_body.
3: apply valid_bctx_random.
unfold wk, mkassn, fun_pre, fun_post; intuition.
destruct H as [_ [_ ?]].
exists 0; split; auto; intros.
destruct o; auto.
unfold bctx_random.
intros. destruct (peq f random_id); try discriminate.
inv H; omega.
Qed.


(* --- Manual Proof For The Main Function *)
(*     Here, we link all the proofs above. *)

(* We can now give a concrete number for
   the total stack consumption of the
   pldi_program program.

   Notice that it depends on F which is
   the metric function. It also depend on
   the program parameter ALEN.
*)
Definition main_consumption :=
  Z.max (F search_id * (2 + Z.log2 ALEN)) (F init_id + F random_id).

(* This is the main theorem.
   We give a bound for the main function
   of the pldi_program program.
*)
Theorem main_bound: forall n,
  valid Z ge F n (mkassn main_consumption) main_body (fun _ => mkassn main_consumption).
Proof.
intros.

(* First show two useful assertions. *)
assert (NNL: 0 <= F search_id * (2 + Z.log2 ALEN)).
{ apply Z.mul_nonneg_nonneg; auto.
  generalize (Z.log2_nonneg ALEN); omega.
}
assert (NNR: 0 <= F init_id + F random_id).
{ assert (0 <= F init_id /\ 0 <= F random_id) by auto.
  omega.
}

apply sound_seq with
  (Q := fun _ => mkassn main_consumption).
destruct o; auto.

(* 1. proof of the function call to init *)
{ eapply valid_max_r; auto. intro.
  eapply sound_consequence.
  2: eapply valid_le; [ apply le_n_Sn |].
  2: eapply sound_call2; [ exact FNN | | apply validC_empty ].
  2: intros; apply init_body_valid.
  instantiate (1 := fun _ _ => True); simpl.
  unfold wk, mkassn, fun_pre, fun_post, enter, leave, pls; intuition.

  exists 0; intuition.
  assert (0 <= F random_id) by auto.
  exists (Z.to_nat (Z.of_nat r - F init_id));
   repeat split; auto; intros.
  rewrite Z2Nat.id; omega.
  apply Nat2Z.inj.
  rewrite Nat2Z.inj_add.
  repeat rewrite Z2Nat.id; auto; omega.

  destruct o; intuition.
  destroids; subst.
  rewrite Nat2Z.inj_add.
  rewrite Z2Nat.id; auto; omega.
}

apply sound_seq with
  (Q := fun _ => mkassn main_consumption).
destruct o; auto.

(* 2. proof of the function call to random *)
{ eapply valid_max_r; auto. intro.
  eapply sound_consequence.
  2: eapply valid_le; [ apply le_n_Sn |].
  2: eapply sound_frame.
  2: eapply sound_call2; [ exact FNN | | apply validC_empty ].
  2: intros; apply random_body_valid.
  instantiate (1 := fun _ => Z.to_nat (F init_id)).
  instantiate (1 := fun _ _ => True); simpl.
  unfold wk, mkassn, fun_pre, fun_post, enter, leave, pls; intuition.

  exists 0; intuition.
  assert (0 <= F random_id) by auto.
  exists (Z.to_nat (Z.of_nat r - F init_id));
   split.
  exists (Z.to_nat (Z.of_nat r - F init_id - F random_id));
   repeat split; auto with zarith; intros.
  apply Nat2Z.inj.
  rewrite Nat2Z.inj_add.
  repeat rewrite Z2Nat.id; auto; omega.
  apply Nat2Z.inj.
  rewrite Nat2Z.inj_add.
  repeat rewrite Z2Nat.id; auto; omega.

  destruct o; destroids; intuition. subst.
  do 2 rewrite Nat2Z.inj_add.
  do 2 rewrite Z2Nat.id by auto. omega.
}

apply sound_seq with
  (Q := fun _ => mkassn main_consumption).
destruct o; auto.

(* 3. proof of the simple modification to elem *)
{ eapply weak_pre; [| eapply sound_lset ].
  unfold mkassn; simpl; intuition.
}

apply sound_seq with
  (Q := fun _ => mkassn main_consumption).
destruct o; auto.

(* 4. proof of the function call to search *)
{ eapply valid_max_l; auto. intro.
  eapply sound_consequence.
  2: eapply valid_le; [ apply le_n_Sn |].
  2: eapply call_search_valid.
  unfold wk, mkassn, search_pre, search_post, enter, leave, pls; intuition.

  replace (2 + Z.log2 ALEN) with (1 + (1 + Z.log2 ALEN)) in *
   by omega.
  rewrite Z.mul_add_distr_l in *.
  assert (0 <= F search_id * (1 + Z.log2 ALEN)).
  apply Z.mul_nonneg_nonneg; auto.
  generalize (Z.log2_nonneg ALEN); intro; omega.

  exists (Z.succ (Z.log2 ALEN)); split; intros.

  exists (Z.to_nat (Z.of_nat r - F search_id));
   repeat split; auto; intros.
  repeat match goal with
    | [ H: evall _ _ _ _ |- _ ] => inv H end.
  exists v. exists (Int.repr ALEN). exists (Int.repr 0).
  repeat split.
  repeat f_equal.
  eapply eval_const; eassumption.
  eapply eval_const; eassumption.
  apply le_cle. apply Int.unsigned_range.

  change (uint (Int.repr 0)) with 0.
  rewrite Int.unsigned_repr by omega.
  replace (ALEN - 0) with ALEN by omega.
  apply Z.lt_le_incl.
  apply Z.log2_spec.
  omega.

  unfold linear.
  rewrite Z.mul_comm.
  rewrite Z2Nat.id. rewrite <- Z.add_1_l. omega.
  generalize (Z.log2_nonneg ALEN); intro; omega.

  apply Nat2Z.inj.
  rewrite Nat2Z.inj_add.
  repeat rewrite Z2Nat.id; auto; omega.

  destruct o; intuition.
  destroids; subst.
  unfold linear in *.
  rewrite <- Z.add_1_l, Z.mul_comm in H3.
  rewrite Nat2Z.inj_add.
  repeat rewrite Z2Nat.id; auto; omega.
}

(* 5. proof of the last return statement *)
{ eapply weak_pre; [| apply sound_ret ].
  auto.
}
Qed.

End PLDI.
