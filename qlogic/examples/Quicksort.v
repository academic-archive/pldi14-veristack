(************************************************************************)
(*                                                                      *)
(*                Quantitative Hoare Logic for Clight                   *)
(*                                                                      *)
(*  Author: Quentin Carbonneaux (c) 2014              Yale University   *)
(*                                                                      *)
(************************************************************************)


(* Here we prove a stack bound on a simple
   quicksort implementation.
*)

Add LoadPath "..".
Require Import Coqlib.
Require Import Common.

Section QUICKSORT.
Context (F: fid -> Z) (FNN: forall f, 0 <= F f).


(* ---- PROGRAM DEFINITION *)

(*
    /* Quicksort function from CompCert's benchmarks. */

    void quicksort(int lo, int hi, int *base)
    {
      int i,j;
      int pivot,temp;

      if (lo<hi) {
        i=lo; j=hi; pivot=base[hi];
        while (i<j) {
          while (i<hi && base[i]<=pivot) i++;
          while (j>lo && base[j]>=pivot) j--;
          if (i<j) { temp=base[i]; base[i]=base[j]; base[j]=temp; }
        }
        temp=base[i]; base[i]=base[hi]; base[hi]=temp;
        quicksort(lo,i-1,base);
        quicksort(i+1,hi,base);
      }
    }

*)


(* --- Variable Identifiers *)

(* -- global variables *)
Definition qsort_id := 1%positive.

(* -- quicksort locals *)
Definition lo_id    := 1%positive.
Definition hi_id    := 2%positive.
Definition base_id  := 3%positive.
Definition i_id     := 4%positive.
Definition j_id     := 5%positive.
Definition pivot_id := 6%positive.
Definition temp_id  := 7%positive.


(* --- Quicksort Expressions *)

Definition lo_e    := Etempvar lo_id i32.
Definition hi_e    := Etempvar hi_id i32.
Definition base_e  := Etempvar base_id i32.
Definition i_e     := Etempvar i_id i32.
Definition j_e     := Etempvar j_id i32.
Definition pivot_e := Etempvar pivot_id i32.
Definition temp_e  := Etempvar temp_id i32.

Definition one_e := Econst_int Int.one i32.

Parameter base: expr -> expr.

(* --- Quicksort Swap Code Snippet *)

Definition swap i j :=
  (sseq (slset temp_id (base i))
  (sseq (sgset (base i) (base j))
        (sgset (base j) temp_e)
  )).

(* --- Quicksort Internal Loop Definition *)

Definition inner_loop :=
  let o op a b := Ebinop op a b i32 in
  (sloop
    (sif (o Olt i_e j_e)
         (* loop body *)
         (sseq (sloop (sif (o Olt i_e hi_e)
                      (sif (o Ole (base i_e) pivot_e)
                         (slset i_id (o Oadd i_e one_e))
                         sbreak)
                         sbreak))
         (sseq (sloop (sif (o Ogt j_e lo_e)
                      (sif (o Oge pivot_e (base i_e))
                         (slset j_id (o Osub j_e one_e))
                         sbreak)
                         sbreak))
               (sif (o Olt i_e j_e) (swap i_e j_e) sskip)
         ))
         (* exit loop *)
         sbreak)
  ).


(* --- Full Quicksort Function Definition *)

Definition quicksort_body :=
  let o op a b := Ebinop op a b i32 in
  (sif (o Olt lo_e hi_e)
       (* main if statement *)
       (sseq (slset i_id lo_e)
       (sseq (slset j_id hi_e)
       (sseq (slset pivot_id (base hi_e))
       (sseq inner_loop
       (sseq (swap i_e hi_e)
       (sseq (scall None qsort_id (lo_e :: (o Osub i_e one_e) :: base_e :: nil))
       (sseq (scall None qsort_id ((o Oadd i_e one_e) :: hi_e :: base_e :: nil))
             (sret None)
       )))))))
       (* no op *)
       (sret None)
  ).

Definition quicksort :=
  {| fi_name := qsort_id
  ;  fi_locals := (i_id, i32) :: (j_id, i32) :: (pivot_id, i32) :: (temp_id, i32) :: nil
  ;  fi_body := quicksort_body
  ;  fi_args := (lo_id, i32) :: (hi_id, i32) :: (base_id, Tpointer i32 noattr) :: nil
  ;  fi_return := Tvoid
  |}.


(* --- Global Environment Used *)

Definition ge: genv :=
  Genv.add_globals (@Genv.empty_genv _ _) (
    (qsort_id, Gfun quicksort) ::
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

Lemma eval_lt:
  forall
    (c: conf)
    a_id na (LOCA: local (c_stack c) a_id na)
    b_id nb (LOCB: local (c_stack c) b_id nb)
    b (EVLTB: eval ge c
                (Ebinop Olt (Etempvar a_id i32)
                            (Etempvar b_id i32) i32) b)
      (BTRUE: val_bool b true),

    sint na < sint nb.

Proof.
intros.
destruct b as [b bty].
destruct EVLTB as [EV ?]; simpl in *; subst.
inv EV.
replace v1 with (Vint na) in *.
replace v2 with (Vint nb) in *.
inv H6.
  revert BTRUE. unfold Int.lt, sint.
  destruct (zlt (Int.signed na) (Int.signed nb));
   try discriminate; auto.
eapply Clight.eval_expr_determ; eauto.
constructor; auto.
eapply Clight.eval_expr_determ; eauto.
constructor; auto.
inv H.
Qed.

(* -- lemmas about operation on the bounds *)

(* We define here a predicate indicating if
   (lo, hi) is a valid pair of bounds to give
   to the quicksort function.
*)
Inductive bounds lo hi: Prop :=
  | bounds_rec
      (LOHI: sint lo <= sint hi)
      (LOMIN: Int.min_signed < sint lo)
      (HIMAX: sint hi < Int.max_signed)
  | bounds_base
      (LOHI: sint lo > sint hi).

(*
Lemma eval_i_add_one:
  forall
    (ge: genv) (c: conf)
    ni (LOCI: local (c_stack c) i_id ni)
    hi (LOCHI: local (c_stack c) hi_id hi)
    b (EVLTB: eval ge c (Ebinop Olt i_e hi_e i32) b)
      (BTRUE: val_bool b true)
    ve (EVADD: eval ge c (Ebinop Oadd i_e one_e i32) ve),

  fst ve = Vint (Int.add ni Int.one) /\
  sint ni < sint hi /\
  sint (Int.add ni Int.one) = sint ni + 1.
*)

Lemma eval_i_add_one:
  forall
    (c: conf)
    ni (LOCI: local (c_stack c) i_id ni)
    (NI: sint ni < Int.max_signed)
    ve (EVADD: eval ge c (Ebinop Oadd i_e one_e i32) ve),

  ve = (Vint (Int.add ni Int.one), i32) /\
  sint (Int.add ni Int.one) = sint ni + 1.

Proof.
intros. split.

+ destruct ve as [v ty].
  destruct EVADD as [EV ?]; simpl in *; subst.
  inv EV.
  replace v1 with (Vint ni) in *.
  replace v2 with (Vint Int.one) in *.
  inv H6. reflexivity.
  inv H5. reflexivity.
  inv H.
  eapply Clight.eval_expr_determ; eauto.
  constructor; auto.
  inv H.
+ rewrite Int.add_signed.
  rewrite Int.signed_repr.
  reflexivity.
  generalize (Int.signed_range ni); intro.
  change (Int.signed Int.one) with 1.
  unfold sint in *; omega.
Qed.

Lemma eval_i_add_one_bounds:
  forall
    (c: conf)
    ni (LOCI: local (c_stack c) i_id ni)
    lo hi (LOHI: sint lo < sint hi) (BOUNDS: bounds lo hi)
    (NI: sint lo <= sint ni <= sint hi)
    ve (EVADD: eval ge c (Ebinop Oadd i_e one_e i32) ve),

  ve = (Vint (Int.add ni Int.one), i32) /\
  sint (Int.add ni Int.one) = sint ni + 1 /\
  bounds (Int.add ni Int.one) hi.

Proof.
intros.
exploit eval_i_add_one; eauto.
{ destruct BOUNDS; omega. }
intros [VE IADD]; repeat split; auto.

+ destruct BOUNDS; try omega.
  assert (CASES: sint ni < sint hi \/ sint ni = sint hi)
   by omega.
  destruct CASES as [NILT | NIEQ].
  left; omega.
  right; omega.
Qed.

Lemma eval_i_sub_one_bounds:
  forall
    (c: conf)
    ni (LOCI: local (c_stack c) i_id ni)
    lo hi (LOHI: sint lo < sint hi) (BOUNDS: bounds lo hi)
    (NI: sint lo <= sint ni <= sint hi)
    ve (EVSUB: eval ge c (Ebinop Osub i_e one_e i32) ve),

  ve = (Vint (Int.sub ni Int.one), i32) /\
  sint (Int.sub ni Int.one) = sint ni - 1 /\
  bounds lo (Int.sub ni Int.one).

Proof.
intros.

assert (ISUB: sint (Int.sub ni Int.one) = sint ni - 1).
{ rewrite Int.sub_signed.
  rewrite Int.signed_repr.
  reflexivity.
  generalize (Int.signed_range hi); intro.
  generalize (Int.signed_range ni); intro.
  change (Int.signed Int.one) with 1.
  destruct BOUNDS; unfold sint in *; try omega.
}

repeat split.

+ destruct ve as [v ty].
  destruct EVSUB as [EV ?]; simpl in *; subst.
  inv EV.
  replace v1 with (Vint ni) in *.
  replace v2 with (Vint Int.one) in *.
  inv H6. reflexivity.
  inv H5. reflexivity.
  inv H.
  eapply Clight.eval_expr_determ; eauto.
  constructor; auto.
  inv H.
+ eexact ISUB.
+ destruct BOUNDS; try omega.
  assert (CASES: sint lo < sint ni \/ sint lo = sint ni)
   by omega.
  destruct CASES as [NILT | NIEQ].
  left; omega.
  right; omega.
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

(* -- some basic goal killer *)
Ltac t pre :=
  match goal with
  | [ |- pre _ _ _ ] => unfold pre, ifP in *

  (* valid proofs *)
  | [ |- valid _ _ _ _ _ (sif _ _ _) _ ] =>
      apply sound_if; unfold ifP in *; intros []
  | [ |- valid _ _ _ _ _ (sseq _ _) _ ] =>
      eapply sound_seq with (Q := fun _ => pre);
      unfold ifP, pre
  | [ |- valid _ _ _ _ _ (slset _ _) _ ] =>
      eapply weak_pre; [| apply sound_lset ]
  | [ |- valid _ _ _ _ _ (sgset _ _) _ ] =>
      eapply weak_pre; [| apply sound_gset ]
  | [ |- valid _ _ _ _ _ sskip _ ] =>
      eapply weak_pre; [| apply sound_skip ]
  | [ |- valid _ _ _ _ _ sbreak _ ] =>
      eapply weak_pre; [| apply sound_break ]

  (* kill obligations resulting from a slset statement *)
  | [ STK: stack_set_ _ _ _ _ _ |- _ ] => simpl; inv STK
  | [ H: exists (_: int), _ |- exists (_: int), _ ] =>
      let ni := fresh in
      destruct H as [ni ?]; exists ni
  | [ |- local _ _ _ ] =>
      unfold local; rewrite PTree.gso;
      try assumption; compute; congruence

  (* general purpose goal killers (fast) *)
  | [ H: _ /\ _ |- _ ] => destruct H
  | [ |- _ /\ _ ] => split
  | [ |- _ ] => intros; simpl; auto

  end.

(* -- kill arithmetic goals with Nat <-> Z conversions *)
Ltac zomg :=
  match goal with
  | [ |- context[ Z.of_nat (_ + _) ] ] => rewrite Nat2Z.inj_add
  | [ |- context[ Z.of_nat (Z.to_nat _) ] ] => rewrite Z2Nat.id by zomg
  | [ |- 0 <= F _ ] => apply FNN
  | [ |- _ ] => try rewrite Z.mul_sub_distr_r in *; omega
  end.


(* --- Proof Of Quicksort's Inner Loop *)

Lemma inner_loop_valid:
  forall pred n,
  let pre z c phi := exists hi lo ni,
    local (c_stack c) i_id ni /\
    local (c_stack c) hi_id hi /\
    local (c_stack c) lo_id lo /\
    sint lo <= sint ni <= sint hi /\
    pred hi lo z phi in

  valid Z ge F n
        pre inner_loop (fun _ => pre).
Proof.

intros.
change pre with ((fun _ => pre) (@oskip expr)) at 1.
apply sound_loop; intuition.
apply sound_if; intros [].

(* 1. proof of the loop body *)

apply sound_seq with
  (Q := fun _ => pre).
destruct o; auto.

(* 1.2. proof of the first inner loop *)
{ apply weak_pre with (P := pre). unfold ifP; intuition.
  change pre with ((fun _ => pre) (@oskip expr)) at 1.
  apply sound_loop; intuition.

  apply sound_if; intros [].
  apply sound_if; intros [].

  eapply weak_pre; [| apply sound_lset ].
  unfold ifP, pre. intuition.
  destruct H2 as [hi [lo [ni ?]]]; destroids.
  exists hi. exists lo.
  exists (Int.add ni Int.one).
  simpl; inv H3.
  generalize (Int.signed_range hi); intro HIMX.
  assert (NIHI: sint ni < sint hi)
   by (eauto using eval_lt).
  exploit eval_i_add_one; eauto.
  unfold sint in *; omega.
  intros [VE ADDEQ].
  split. subst.
  unfold local; rewrite PTree.gss. reflexivity.
  repeat (t pre).
  omega. omega.

  repeat (t pre).
  repeat (t pre).
}

apply sound_seq with
  (Q := fun _ => pre).
destruct o; auto.

(* 1.3. proof of the second inner loop *)
{ apply weak_pre with (P := pre). auto.
  change pre with ((fun _ => pre) (@oskip expr)) at 1.
  apply sound_loop; auto.
  repeat (t pre).
}

(* 1.4. proof of the swapping if *)
unfold swap; repeat (t pre).

(* 2. proof of the loop exit *)
repeat (t pre).
Qed.


(* --- Proof For The Full Quicksort Function *)

Definition lin z phi := z * F qsort_id <= Z.of_nat phi.

Theorem quicksort_valid: forall n,
  let pre z (_: mem) args phi :=
    exists hi lo base,
      args = (Vint lo, i32) :: (Vint hi, i32) :: base :: nil /\
      bounds lo hi /\
      sint hi - sint lo <= z /\
      lin z phi in
  let post z (_: mem) (_: option val) phi :=
    lin z phi in

  validf _ ge F (S n)
        pre qsort_id post.
Proof.
intro. eapply validf_ind; [| apply validC_empty ].
clear n; intros n VALIDC.
unfold validf; intros. inv H.

apply sound_if; intros [].

(* 1. prove the recursive case (lo<hi) *)

(* first, we clean the precondition *)
apply weak_pre with
  (P := fun z c phi => exists hi lo,
    local (c_stack c) hi_id hi /\
    local (c_stack c) lo_id lo /\
    bounds lo hi /\
    sint lo < sint hi /\
    sint hi - sint lo <= z /\
    lin z phi).
{ unfold ifP; intros.
  destroids; subst.
  inv H0.
  assert (FI: Some quicksort = Some fi) by assumption.
  replace fi with quicksort in * by congruence; clear FI.
  repeat match goal with
  | [ H: castl _ _ _ |- _ ] => inv H
  | [ H: val_cast (Vint _, _) _ = Some _ |- _ ] => inv H
  end.
  injection H9; clear H9; intros STACK.
  unfold stack,temp_env in *. rewrite <- STACK.
  repeat esplit; eauto.
  eapply eval_lt; eauto.
  rewrite <- STACK. reflexivity.
  rewrite <- STACK. reflexivity.
}

pose (i_lo z (c: conf) phi := exists hi lo,
  local (c_stack c) i_id lo /\
  local (c_stack c) hi_id hi /\
  local (c_stack c) lo_id lo /\
  bounds lo hi /\
  sint lo < sint hi /\
  sint hi - sint lo <= z /\
  lin z phi
).

apply sound_seq with
  (Q := fun _ => i_lo).
unfold i_lo. destruct o; intros; destroids; auto.

(* 1.1. prove the assignment to i *)
{ eapply weak_pre; [| apply sound_lset ].
  unfold i_lo; simpl; intros.
  destruct H as [hi [lo ?]]; destroids.
  exists hi. exists lo.
  destruct H1; split.
  unfold local. rewrite PTree.gss.
    f_equal. 
    eapply Clight.eval_expr_determ; eauto.
    constructor; auto.
  repeat split; t i_lo.
}

apply sound_seq with
  (Q := fun _ => i_lo).
unfold i_lo. destruct o; intros; destroids; auto.

(* 1.2. prove the assignment to j *)
repeat (t i_lo).

apply sound_seq with
  (Q := fun _ => i_lo).
unfold i_lo. destruct o; intros; destroids; auto.

(* 1.3. prove the assignment to pivot *)
repeat (t i_lo).

unfold i_lo; clear i_lo.
pose (i_mid z (c: conf) phi := exists hi lo ni,
  local (c_stack c) i_id ni /\
  local (c_stack c) hi_id hi /\
  local (c_stack c) lo_id lo /\
  bounds lo hi /\
  sint lo <= sint ni <= sint hi /\
  sint lo < sint hi /\
  sint hi - sint lo <= z /\
  lin z phi
).

apply sound_seq with
  (Q := fun _ => i_mid).
unfold i_mid. destruct o; intros; destroids; auto.

(* 1.4. prove the inner loop *)
{ pose (frame hi lo z phi :=
    sint lo < sint hi /\
    bounds lo hi /\
    sint hi - sint lo <= z /\
    lin z phi
  ).

  eapply weak_pre.
  2: eapply weak_post.
  3: apply (inner_loop_valid frame).

  unfold frame; intros.
  destroids; repeat eexists; eauto; omega.

  unfold frame; intros.
  destroids; repeat eexists; eauto; omega.
}

apply sound_seq with
  (Q := fun _ => i_mid).
unfold i_mid. destruct o; intros; destroids; auto.

(* 1.5. prove the swap correct *)
unfold swap; repeat (t i_mid).

pose (stack_frame z s := exists hi lo ni,
  local s i_id ni /\
  local s hi_id hi /\
  local s lo_id lo /\
  bounds lo hi /\
  sint lo <= sint ni <= sint hi /\
  sint lo < sint hi /\
  sint hi - sint lo <= z + 1
).

apply sound_seq with
  (Q := fun _ => i_mid).
unfold i_mid. destruct o; intros; destroids; auto.

(* 1.6. prove the first recursive call correct *)
{ eapply sound_consequence;
   [| eapply sound_call1; eauto ].
  2: reflexivity.
  instantiate (1 := stack_frame).

  unfold wk, enter, leave, pls, i_mid, stack_frame;
   revert FNN; clear; intros.
  exists (z - 1); split; intros.

  + destruct H as [hi [lo [ni ?]]]; destroids.
    assert (RFRAME: F qsort_id <= Z.of_nat r).
    { unfold lin in *.
      assert (1 * F qsort_id <= z * F qsort_id).
      apply Z.mul_le_mono_nonneg_r; auto; omega.
      omega.
    }

    exists (Z.to_nat (Z.of_nat r - F qsort_id)).
    repeat split; auto; intros.
    repeat match goal with
      [ H: evall _ _ _ _ |- _ ] => inv H end.
    exploit eval_local; eauto.
    exploit eval_i_sub_one_bounds; eauto.
    intros [? [SINT BOUNDS']] ?; subst.
    repeat eexists; auto. omega.
    unfold lin in *.
    repeat zomg.

    repeat eexists; eauto. omega.

    apply Nat2Z.inj. repeat zomg.

  + destruct o; try tauto.
    clear H. destroids.
    inv H. inv H10.
    repeat eexists; eauto. omega.
    unfold lin in *; repeat zomg.
    repeat eexists; eauto. omega.
    unfold lin in *; repeat zomg.
}

apply sound_seq with
  (Q := fun _ => i_mid).
unfold i_mid. destruct o; intros; destroids; auto.

(* 1.7. prove the second recursive call correct *)
{ eapply sound_consequence;
   [| eapply sound_call1; eauto ].
  2: reflexivity.
  instantiate (1 := stack_frame).

  unfold wk, enter, leave, pls, i_mid, stack_frame;
   revert FNN; clear; intros.
  exists (z - 1); split; intros.

  + destruct H as [hi [lo [ni ?]]]; destroids.
    assert (RFRAME: F qsort_id <= Z.of_nat r).
    { unfold lin in *.
      assert (1 * F qsort_id <= z * F qsort_id).
      apply Z.mul_le_mono_nonneg_r; auto; omega.
      omega.
    }

    exists (Z.to_nat (Z.of_nat r - F qsort_id)).
    repeat split; auto; intros.
    repeat match goal with
      [ H: evall _ _ _ _ |- _ ] => inv H end.
    clear H1. exploit eval_local; eauto.
    exploit eval_i_add_one_bounds; eauto.
    intros [? [SINT BOUNDS']] ?; subst.
    repeat eexists; auto. omega.
    unfold lin in *. repeat zomg.

    repeat eexists; eauto. omega.

    apply Nat2Z.inj. repeat zomg.

  + destruct o; try tauto.
    clear H. destroids.
    inv H. inv H10.
    repeat eexists; eauto. omega.
    unfold lin in *; repeat zomg.
    repeat eexists; eauto. omega.
    unfold lin in *; repeat zomg.
}

unfold i_mid; clear i_mid stack_frame.

(* 1.8. prove the last return statement *)
{ eapply weak_pre; [| apply sound_ret ].
  intros; destroids; auto.
}

(* 2. prove the implicit return in the else branch *)
{ eapply weak_pre; [| apply sound_ret ].
  unfold ifP; intros; destroids; auto.
}
Qed.

End QUICKSORT.
