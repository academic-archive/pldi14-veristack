(************************************************************************)
(*                                                                      *)
(*                Quantitative Hoare Logic for Clight                   *)
(*                                                                      *)
(*  Author: Quentin Carbonneaux (c) 2014              Yale University   *)
(*                                                                      *)
(************************************************************************)


Require Import Coqlib.
Require Export AST.
Require Export Clight.
Require Export Cop.
Require Export Ctypes.
Require Export Globalenvs.
Require Export Integers.
Require Export List.
Require Export Memory.
Require Export Values.
Require Export PArith.
Require Export ZArith.

Add LoadPath "..".
Require Export Cxlight.
Require Export Logic.


(* ### general Clight cruft *)
Lemma eq_spec':
  forall a b,
  (Int.eq a b = true -> a = b) /\
  (Int.eq a b = false -> a <> b).
Proof.
intros; generalize (Int.eq_spec a b).
destruct (Int.eq a b); intuition.
Qed.

Lemma signed_one: Int.signed Int.one = 1.
Proof. reflexivity. Qed.


(* ### quantitative logic helpers *)
Section QLOGIC.
Context (F: fid -> Z) (FNN: forall f, 0 <= F f) (aux: Type).

Lemma weak_pre:
  forall (P Pw: assn aux) (Q: oassn aux)
         (WP: forall z c n, Pw z c n -> P z c n)
         ge n s
         (VALID: valid aux ge F n P s Q),
  valid aux ge F n Pw s Q.
Proof.
intros; eapply sound_consequence; try eassumption.
intro; exists z; intuition.
Qed.

Lemma weak_post:
  forall (P: assn aux) (Q Qw: oassn aux)
         (WQ: forall o z c n, Q o z c n -> Qw o z c n)
         ge n s
         (VALID: valid aux ge F n P s Q),
  valid aux ge F n P s Qw.
Proof.
intros; eapply sound_consequence; try eassumption.
intro; exists z; intuition.
Qed.

Lemma validC_empty:
  forall ge n, validC aux ge F n (fun _ => None).
Proof. unfold validC; intros; discriminate. Qed.
End QLOGIC.


(* ### integer variable helpers *)
Section INTGLOBS.
Context (ge: genv).

Definition i32 := Tint I32 Signed noattr.
Definition u32 := Tint I32 Unsigned noattr.

Function is_int ty :=
  match ty with
  | Tint I32 _ _ => true
  | _ => false
  end.

Definition givar ty n: globvar type :=
  {| gvar_info := ty
  ;  gvar_init := Init_int32 (Int.repr n) :: nil
  ;  gvar_readonly := false
  ;  gvar_volatile := false
  |}.

Theorem eval_expr_fun:
  forall c id ty i v'
         (EVAL: eval_expr ge c (Evar id ty) (Vint i))
         (EVAL': eval_expr ge c (Evar id ty) v'),
  v' = Vint i.
Proof.
intros. eapply Clight.eval_expr_determ; eauto.
Qed.

Inductive glo_ival (m: mem): ident -> int -> Prop :=
  | glo_ival_intro:
      forall id l i,
      Genv.find_symbol ge id = Some l ->
      Mem.loadv Mint32 m (Vptr l Int.zero) = Some (Vint i) ->
      glo_ival m id i.

Definition glo_typ id ty :=
  exists l, Genv.find_symbol (trgenv ge) id = Some l /\
            type_of_global (trgenv ge) l = Some ty.

Theorem glo_ival_eval:
  forall id ty (GTY: glo_typ id ty) (INT: is_int ty = true)
         m n (GV: glo_ival m id n) s,
  eval_expr ge (cnf s m) (Evar id ty) (Vint n).
Proof.
destruct 1 as [loc [GE TY]].
destruct 2.
intros.
rewrite find_symbol_trgenv in H.
rewrite H in GE; inv GE.
eapply eval_Elvalue.
+ eapply eval_Evar_global.
  rewrite Maps.PTree.gempty.
  reflexivity.
  eassumption.
  eassumption.
+ econstructor.
  functional inversion INT;
   subst.
  reflexivity.
  assumption.
Qed.
End INTGLOBS.

Definition uint := Int.unsigned.
Definition sint := Int.signed.

Lemma cle_le:
  forall ne nb, Int.cmpu Cle nb ne = true ->
  uint nb <= uint ne.
Proof.
intros.
simpl in H; unfold Int.ltu in H.
destruct (zlt (Int.unsigned ne) (Int.unsigned nb)).
discriminate.
unfold uint; omega.
Qed.

Lemma le_cle: forall a b,
  uint a <= uint b -> Int.cmpu Cle a b = true.
Proof.
intros.
apply eq_true_not_negb.
unfold Int.ltu.
destruct (zlt (Int.unsigned b) (Int.unsigned a));
 [ unfold uint in *; omega | congruence ].
Qed.

Lemma scle_le:
  forall ne nb, Int.cmp Cle nb ne = true ->
  sint nb <= sint ne.
Proof.
intros.
simpl in H; unfold Int.lt in H.
destruct (zlt (Int.signed ne) (Int.signed nb)).
discriminate.
unfold sint; omega.
Qed.

Lemma sle_cle: forall a b,
  sint a <= sint b -> Int.cmp Cle a b = true.
Proof.
intros.
apply eq_true_not_negb.
unfold Int.lt.
destruct (zlt (Int.signed b) (Int.signed a));
 [ unfold sint in *; omega | congruence ].
Qed.

Lemma uint_one_e: uint (Int.one) = 1.
Proof. reflexivity. Qed.

Lemma sint_one_e: sint (Int.one) = 1.
Proof. reflexivity. Qed.

(* two is also sometimes useful *)
Definition two := Int.repr 2.

Lemma uint_two_e: uint two = 2.
Proof. reflexivity. Qed.


(* ### logarithmic functions helpers *)

Lemma dichot: forall k, k > 0 -> forall n, n > 1 -> n <= 2^k ->
  n/2 <= 2^(k-1) /\ (n mod 2 <> 0 -> n/2 + 1 <= 2^(k-1)).
Proof.
intros k.
pose (q := k - 1). fold q.
replace k with (Z.succ q)
 by (unfold q; omega).
intros.
assert (HLFBOUND: n/2 <= 2 ^ q).
{ rewrite Z.pow_succ_r in H1.
  replace (2 ^ q) with ((2 * 2 ^ q) / 2).
  apply Z.div_le_mono.
  omega.
  assumption.
  rewrite Z.mul_comm, Z_div_mult_full.
  reflexivity.
  omega.
  omega.
}
split. assumption.
intro ODD.
exploit (Z_div_mod_eq n 2). omega.
intro EUCL.
exploit (Z.mod_pos_bound n 2). omega.
intro MOD_BOUND.
assert (MOD: n mod 2 = 1) by omega.
clear MOD_BOUND ODD.
rewrite MOD in *.
destruct (zlt (n / 2) (2 ^ q)).
omega.
assert (HALF: n / 2 = 2 ^ q) by omega.
rewrite HALF in *.
rewrite EUCL in H1.
rewrite <- Z.pow_succ_r in H1.
omega. omega.
Qed.

Lemma splitr: forall n, n mod 2 <> 0 ->
  n - n/2 = n/2 + 1.
Proof.
intros.
cut (2 * (n / 2) + 1 = n).
intro; omega.
replace 1 with (n mod 2).
symmetry; apply Z_div_mod_eq.
omega.
exploit (Z.mod_pos_bound n 2). omega.
intro; omega.
Qed.

Lemma splitl: forall n, n mod 2 = 0 ->
  n - n/2 = n/2.
Proof.
intros.
rewrite (Z_div_mod_eq n 2) at 1.
omega. omega.
Qed.

Lemma pow_gt_one: forall x, 1 < 2^x -> 0 < x.
Proof.
intros.
assert (CASE: 0 < x \/ x = 0 \/ x < 0) by omega.
destruct CASE as [? | [? | ?]].
assumption.
subst; simpl in H; omega.
rewrite Z.pow_neg_r in H by assumption.
omega.
Qed.
