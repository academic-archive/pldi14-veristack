(************************************************************************)
(*                                                                      *)
(*                Quantitative Hoare Logic for Clight                   *)
(*                                                                      *)
(*  Author: Quentin Carbonneaux (c) 2014              Yale University   *)
(*                                                                      *)
(************************************************************************)


(* Proof of the stack consumption for
   a stupid Fibonacci function.
*)

Add LoadPath "..".
Require Import Coqlib.
Require Import Common.

Section FIBONACCI.
Context (F: fid -> Z) (FNN: forall f, 0 <= F f).


(* ---- PROGRAM DEFINITION *)

(*
    /* Fibonacci function from CompCert's benchmarks. */

    int fib(int n)
    {
      if (n < 2) 
        return 1;
      else
        return fib(n-1) + fib(n-2);
    }

*)

(* --- Variable Identifiers *)

(* -- global variables *)
Definition fib_id  := 1%positive.

(* -- fib locals *)
Definition n_id    := 1%positive.
Definition tmp1_id := 2%positive.
Definition tmp2_id := 3%positive.


(* --- Fib Expressions *)

Definition n_e    := Etempvar n_id i32.
Definition tmp1_e := Etempvar tmp1_id i32.
Definition tmp2_e := Etempvar tmp2_id i32.

Definition one_e := Econst_int (Int.repr 1) i32.
Definition two_e := Econst_int (Int.repr 2) i32.

(* --- Fibonacci Function Definition *)

Definition fib_body :=
  let o op a b := Ebinop op a b i32 in
  (sif (o Olt n_e two_e)
       (* base case *)
       (sret (Some one_e))
       (* recursive case *)
       (sseq (scall (Some tmp1_id) fib_id (o Osub n_e one_e :: nil))
       (sseq (scall (Some tmp2_id) fib_id (o Osub n_e two_e :: nil))
             (sret (Some (o Oadd tmp1_e tmp2_e)))
       ))
  ).

Definition fib :=
  {| fi_name := fib_id
  ;  fi_locals := (tmp1_id, i32) :: (tmp2_id, i32) :: nil
  ;  fi_body := fib_body
  ;  fi_args := (n_id, i32) :: nil
  ;  fi_return := i32
  |}.


(* --- Global Environment Used *)

Definition ge: genv :=
  Genv.add_globals (@Genv.empty_genv _ _) (
    (fib_id, Gfun fib) ::
    nil
  ).



(* ---- STACK BOUND PROOF *)
Require Import Maps.


(* --- Expression Tools *)
Definition local s id n := s!id = Some (Vint n).

Lemma eval_local:
  forall c id n (LOC: local (c_stack c) id n)
         v (EVAL: eval ge c (Etempvar id i32) v),
  v = (Vint n, i32).
Proof.
simpl; intros until v.
destruct v; intros [? ?]; f_equal; auto.
eapply Clight.eval_expr_determ; eauto.
constructor; auto.
Qed.

Lemma eval_lt_k:
  forall
    (c: conf)
    k (KBOUND: Int.min_signed <= k <= Int.max_signed)
    n_id n (LOC: local (c_stack c) n_id n)
    vb (EVLTB: eval ge c
                 (Ebinop Olt (Etempvar n_id i32)
                             (Econst_int (Int.repr k) i32) i32) vb)
    b (BBOOL: val_bool vb b),

  if b then sint n < k
       else k <= sint n.

Proof.
intros.
destruct vb as [vb vbty].
destruct EVLTB as [EV ?]; simpl in *; subst.
inv EV.
replace v1 with (Vint n) in *.
replace v2 with (Vint (Int.repr k)) in *.
inv H6.
{ revert BBOOL. unfold Int.lt, sint.
  rewrite Int.signed_repr by assumption.
  destruct (zlt (Int.signed n) k);
   injection 1; intro; subst.
  change (Int.eq Int.one Int.zero) with false;
   simpl; assumption.
  change (Int.eq Int.zero Int.zero) with true;
   simpl; omega.
}
eapply Clight.eval_expr_determ; eauto;
 constructor.
eapply Clight.eval_expr_determ; eauto;
 constructor; assumption.
inv H.
Qed.

Lemma eval_sub:
  forall
    (c: conf)
    n_id n (LOC: local (c_stack c) n_id n)
    k (KBOUND: 0 <= k <= sint n)
    v (EV: eval ge c
             (Ebinop Osub (Etempvar n_id i32)
                          (Econst_int (Int.repr k) i32) i32) v),

  v = (Vint (Int.sub n (Int.repr k)), i32) /\
  sint (Int.sub n (Int.repr k)) = sint n - k.

Proof.
intros.
destruct v as [v ty].
destruct EV as [EV ?]; simpl in *.
subst; split.

+ inv EV.
  replace v1 with (Vint n) in *.
  replace v2 with (Vint (Int.repr k)) in *.
  inv H6; reflexivity.
  eapply Clight.eval_expr_determ; eauto.
   constructor.
  eapply Clight.eval_expr_determ; eauto.
   constructor. assumption.
  inv H.
+ unfold sint in *.
  generalize (Int.signed_range n); intro.
  generalize Int.min_signed_neg; intro.
  rewrite Int.sub_signed.
  repeat rewrite Int.signed_repr; omega.
Qed.


(* --- Ltac Hacks *)

(* -- destruct on steroids *)
Ltac destroids :=
  repeat match goal with
  | [ H: exists _, _ |- _ ] => destruct H
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ H: True |- _ ] => clear H
  | [ H: False |- _ ] => elim H
  end.

(* -- kill arithmetic goals with Nat <-> Z conversions *)
Ltac zomg :=
  match goal with
  | [ |- context[ Z.of_nat (_ + _) ] ] => rewrite Nat2Z.inj_add
  | [ |- context[ Z.of_nat (Z.to_nat _) ] ] => rewrite Z2Nat.id by zomg
  | [ |- 0 <= F _ ] => apply FNN
  | [ |- _ ] => try rewrite Z.mul_sub_distr_r in *; omega
  end.


(* --- Proof For The Fib Function *)

Definition lin z phi := z * F fib_id <= Z.of_nat phi.

Theorem fibonacci_valid: forall i,
  let pre z (_: mem) args phi :=
    exists n,
      args = (Vint n, i32) :: nil /\
      0 <= sint n <= z /\
      lin z phi in
  let post z (_: mem) (_: option val) phi :=
    lin z phi in

  validf _ ge F (S i)
         pre fib_id post.
Proof. Opaque PTree.set.

intro. eapply validf_ind; [| apply validC_empty ].
clear i; intros i VALIDC.
unfold validf; intros. inv H.

apply sound_if; intros [].

(* 1. prove the base case (n < 2) *)

(* 1.1. prove the base case return *)
eapply weak_pre; [| apply sound_ret ].
unfold ifP; intros; destroids; auto.

(* 2. prove the recursive case (n >= 2) *)

(* first, we make the pre-condition nicer *)
apply weak_pre with
  (P := fun z c phi =>
    exists n,
      local (c_stack c) n_id n /\
      2 <= sint n /\
      0 <= sint n <= z /\
      lin z phi).
{ unfold ifP; intros.
  destroids; subst.
  inv H0.
  assert (FI: Some fib = Some fi) by assumption.
  replace fi with fib in * by congruence; clear FI.
  repeat match goal with
  | [ H: castl _ _ _ |- _ ] => inv H
  | [ H: val_cast (Vint _, _) _ = Some _ |- _ ] => inv H
  end.
  injection H9; clear H9; intro STACK.
  unfold stack, temp_env in *. rewrite <- STACK.
  repeat eexists; eauto.
  exploit eval_lt_k; eauto.
  split; compute; congruence.
  rewrite <- STACK; reflexivity.
  tauto.
}

pose (stack_frame z s :=        (* logical predicate on the stack *)
  exists n,
    local s n_id n /\
    2 <= sint n /\
    0 <= sint n <= z + 1
).

pose (pred z (c: conf) phi :=   (* assertion used in the sequel *)
  exists n,
    local (c_stack c) n_id n /\
    2 <= sint n /\
    0 <= sint n <= z /\
    lin z phi
).

apply sound_seq with
  (Q := fun _ => pred).
unfold pred; intros; destruct o; destroids; auto.

(* 2.1. prove the first recursive call *)
{ eapply sound_consequence;
   [| eapply sound_call1; eauto ].
  2: reflexivity.
  instantiate (1 := stack_frame).

  unfold wk, enter, leave, pls, pred, stack_frame;
   revert FNN; clear; intros.
  exists (z - 1); split; intros.

  + destruct H as [n ?]; destroids.
    assert (RFRAME: F fib_id <= Z.of_nat r).
    { unfold lin in *.
      assert (1 * F fib_id <= z * F fib_id).
      apply Z.mul_le_mono_nonneg_r; auto; omega.
      omega.
    }

    exists (Z.to_nat (Z.of_nat r - F fib_id)).
    repeat split; auto; intros.
    repeat match goal with
      [ H: evall _ _ _ _ |- _ ] => inv H end.
    exploit eval_sub; eauto. omega.
    intros [? SUBONE]; subst.
    unfold lin in *; repeat eexists; auto; repeat zomg.

    repeat eexists; eauto. omega.

    apply Nat2Z.inj. repeat zomg.

  + destruct o; try tauto.
    clear H; destroids; subst.
    unfold stack, temp_env in *.
    inv H. inv H0.
    repeat eexists; eauto.
    unfold local; rewrite PTree.gso;
     auto; compute; congruence.
    omega.
    unfold lin in *; repeat zomg.
}

apply sound_seq with
  (Q := fun _ => pred).
unfold pred; intros; destruct o; destroids; auto.

(* 2.2. prove the second recursive call *)
{ eapply sound_consequence;
   [| eapply sound_call1; eauto ].
  2: reflexivity.
  instantiate (1 := stack_frame).

  unfold wk, enter, leave, pls, pred, stack_frame;
   revert FNN; clear; intros.
  exists (z - 1); split; intros.

  + destruct H as [n ?]; destroids.
    assert (RFRAME: F fib_id <= Z.of_nat r).
    { unfold lin in *.
      assert (1 * F fib_id <= z * F fib_id).
      apply Z.mul_le_mono_nonneg_r; auto; omega.
      omega.
    }

    exists (Z.to_nat (Z.of_nat r - F fib_id)).
    repeat split; auto; intros.
    repeat match goal with
      [ H: evall _ _ _ _ |- _ ] => inv H end.
    exploit eval_sub; eauto. omega.
    intros [? SUBTWO]; subst.
    unfold lin in *; repeat eexists; auto; repeat zomg.

    repeat eexists; eauto. omega.

    apply Nat2Z.inj. repeat zomg.

  + destruct o; try tauto.
    clear H; destroids; subst.
    unfold stack, temp_env in *.
    inv H. inv H0.
    repeat eexists; eauto.
    unfold local; rewrite PTree.gso;
     auto; compute; congruence.
    omega.
    unfold lin in *; repeat zomg.
}

(* 2.3. prove the recursive return statement *)
{ eapply weak_pre; [| apply sound_ret ].
  unfold pred.
  simpl; intros; destroids; auto.
}
Qed.

End FIBONACCI.
