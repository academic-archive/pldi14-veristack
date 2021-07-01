(************************************************************************)
(*                                                                      *)
(*                Quantitative Hoare Logic for Clight                   *)
(*                                                                      *)
(*  Author: Quentin Carbonneaux (c) 2014              Yale University   *)
(*                                                                      *)
(************************************************************************)


Require Import Core.
Require Import ZArith.
Open Scope Z.

Section QLOGIC.
Context `{Sem: BaseSem} (aux: Type) (ge: genv) (frame: fid -> Z).

Fixpoint value (t: trace) :=
  match t with
  | nil => 0
  | cons (ecall f) t' => value t' + frame f
  | cons (eret f) t' => value t' - frame f
  end.

Lemma value_morphism: forall t1 t2, value (Tapp t1 t2) = value t1 + value t2.
Proof.
induction t1; simpl; try reflexivity.
intros; rewrite IHt1.
destruct a; omega.
Qed.

Lemma value_call: forall f, value (T1 (ecall f)) = frame f.
Proof. intros; simpl; omega. Qed.

Lemma value_ret: forall f, value (T1 (eret f)) = - frame f.
Proof. intros; simpl; omega. Qed.

Lemma value_T0: value T0 = 0.
Proof. intros; simpl; omega. Qed.

Inductive runs: nat -> (stm * cont * conf) -> Z -> Prop :=

  | runs_zero: forall s k c r,
      0 <= r -> runs 0 (s, k, c) r

  | runs_step: forall n s k c r,
      (forall s' k' c' t,
         step ge (s, k, c) t (s', k', c') ->
         runs n (s', k', c') (r - value t)) ->
      0 <= r -> runs (S n) (s, k, c) r.

Lemma runs_le:
  forall n n' (LE: le n' n) S b (RUNS: runs n S b),
  runs n' S b.
Proof.
induction n; intros; destruct S as [[? ?] ?].
replace n' with O by omega. constructor.
inversion RUNS; assumption.
destruct n'; constructor;
 inversion RUNS; subst; try assumption.
intros.
apply IHn, H4. omega.
assumption.
Qed.

(* runs and trace values *)
Inductive many {X: Type} (R: X -> trace -> X -> Prop): X -> trace -> X -> Prop :=
  | many_base: forall s, many R s T0 s
  | many_step: forall s t s' t' s'',
      R s t s' -> many R s' t' s'' -> many R s (Tapp t t') s''.

Inductive index {X: Type} (R: X -> trace -> X -> Prop): (nat * X) -> trace -> (nat * X) -> Prop :=
  | index_intro: forall n s t s', R s t s' -> index R (S n, s) t (n, s').

Remark many_manyindex: forall X (R: X -> trace -> X -> Prop) s t s',
  many R s t s' -> exists n, many (index R) (n, s) t (O, s').
Proof.
induction 1.
exists O; constructor.
destruct IHmany as [n MANY].
exists (S n); econstructor.
constructor; eassumption.
assumption.
Qed.

Remark runs_sound_index:
  forall n s t s'
         (MANY: many (index (step ge)) (n, s) t (O, s'))
         r (RUNS: runs n s r),
  value t <= r.
Proof.
induction n; intros.
(* base case *)
inversion MANY; subst.
rewrite value_T0.
inversion RUNS; omega.
inversion H.
(* induction *)
inversion MANY; subst.
rewrite value_morphism.
inversion H; subst.
clear MANY H.
inversion RUNS; subst.
assert (value t' <= r - value t0).
destruct s'1 as [[? ?] ?].
eapply IHn,H1; eauto.
omega.
Qed.

Remark runs_sound:
  forall S t S'
         (MANY: many (step ge) S t S')
         r (RUNS: forall n, runs n S r),
  value t <= r.
Proof.
intros.
assert (INDEX: exists n', many (index (step ge)) (n', S) t (O, S'))
  by (apply many_manyindex; assumption).
destruct INDEX.
eapply runs_sound_index; eauto.
Qed.


(* logic assertions *)
Inductive outcome := oskip | obreak | oret (r: option expr).
Definition assn := aux -> conf -> nat -> Prop.
Definition oassn := outcome -> assn.
Implicit Types P Pw: assn.
Implicit Types I Q Qw R: oassn.

(* validity of triples *)
Definition pls P x: assn :=
  fun z c r => exists n, P z c n /\ r = plus n (x z).

Definition safe n z P s k :=
  forall c r, P z c r -> runs n (s, k, c) (Z.of_nat r).
Definition safek n z Q k :=
  safe n z (Q oskip) sskip k /\
  safe n z (Q obreak) sbreak k /\
  forall r, safe n z (Q (oret r)) (sret r) k.
Definition valid n P s Q :=     (* embeds a framing. *)
  forall m (Hmn: le m n)
         k x z (Hk: safek m z (fun o => pls (Q o) x) k),
  safe m z (pls P x) s k.
Definition validf n Pg f Qg :=
  forall bdy, find_func ge f = Some bdy ->
  valid n
    (fun z c r => exists (vargs: list val),
      fun_init ge f vargs (c_stack c) /\
      Pg z (c_mem c) vargs r) bdy
    (fun o z c r =>
      match o with
      | oret ret =>
        forall vret (RETEVAL: ret_eval ge c f ret vret),
        (Qg z (c_mem c) vret r: Prop)
      | _ => True end).
Definition validC n C :=
  forall f Pg Qg, C f = Some (Pg, Qg) -> validf n Pg f Qg.

Lemma pls_assoc: forall P x1 x2 z c n,
  pls P (fun z => plus (x1 z) (x2 z)) z c n <-> pls (pls P x1) x2 z c n.
Proof. unfold pls; firstorder. repeat eexists; eauto; omega. Qed.

Lemma safe_le: forall n n' (LE: le n' n) z P s k,
  safe n z P s k -> safe n' z P s k.
Proof. unfold safe; intros; eauto using runs_le. Qed.
Lemma safek_le: forall n n' (LE: le n' n) z Q k,
  safek n z Q k -> safek n' z Q k.
Proof. unfold safek; intuition; eauto using safe_le. Qed.
Lemma valid_le: forall n n' (LE: le n' n) P s Q,
  valid n P s Q -> valid n' P s Q.
Proof. unfold valid; eauto with arith. Qed.
Lemma validC_le: forall n n' (LE: le n' n) C,
  validC n C -> validC n' C.
Proof. unfold validC, validf; eauto using valid_le. Qed.

Definition app {A B: Type} C (Pg: A) f (Qg: B) g :=
  if fid_eq f g
  then Some (Pg, Qg)
  else C g.

Lemma validC_app:
  forall n C Pg f Qg
         (VALIDf: validf n Pg f Qg)
         (VALIDC: validC n C),
  validC n (app C Pg f Qg).
Proof.
unfold validC at 2, app; intros.
destruct (fid_eq f f0).
+ injection H; intros; subst.
  assumption.
+ apply VALIDC; assumption.
Qed.

Lemma validf_ind:
  forall f C Pg Qg
         (Hf: forall n,
            validC n (app C Pg f Qg) ->
            validf (S n) Pg f Qg)
         n (HC: validC n C),
 validf (S n) Pg f Qg.
Proof.
induction n using lt_wf_rec.
intros.
eapply Hf.
eapply validC_app; try assumption.
destruct n.
+ unfold validf, valid; intros.
  replace m with O by omega.
  unfold safe; intros; constructor; omega.
+ eapply H. omega.
  eauto using validC_le.
Qed.

(* soundness of rules *)

(* The 'step' database is used in the 'step'
   tactic to solve arithmetic goals.
*)
Hint Rewrite value_T0 value_ret value_call Nat2Z.inj_add : step.

Ltac step :=
  match goal with
  | [ |- runs (S ?n) _ _ ] =>
      apply runs_step;
      [ let hstep := fresh in
        intros ? ? ? ? hstep;
        inversion hstep; subst; clear hstep;
        try rewrite Z.sub_0_r
      | autorewrite with step; omega ]
  | [ |- runs (S _) _ _ ] => fail 1
  | [ |- runs ?n _ _ ] =>
      destruct n;
      [ apply runs_zero; omega
      | step
      ]
  end.

Ltac apple H :=
  match goal with
  | [ |- runs _ _ _  ]    => eapply runs_le
  | [ |- safe _ _ _ _ _ ] => eapply safe_le
  | [ |- safek _ _ _ _ ]  => eapply safek_le
  | [ |- valid _ _ _ _ ]  => eapply valid_le
  end;
  [| eapply H ]; try omega.

(* kstop is always a good continuation *)
Lemma safe_kstop:
  forall n z Q, safek n z Q kstop.
Proof.
intros; unfold safek, safe.
repeat split; intros; step.
Qed.

(* soundness of the logic rules *)

Lemma sound_skip:
  forall n Q,
  valid n (Q oskip) sskip Q.
Proof.
unfold valid, safe; intros.
apple Hk; assumption.
Qed.

Lemma sound_ret:
  forall n r Q,
  valid n (Q (oret r)) (sret r) Q.
Proof.
unfold valid, safe; intros.
apple Hk; assumption.
Qed.

Lemma sound_break:
  forall n Q,
  valid n (Q obreak) sbreak Q.
Proof.
unfold valid, safe; intros.
apple Hk; assumption.
Qed.

Lemma sound_lset:
  forall n v e Q,
  let P z c n := forall ve s',
    eval ge c e ve ->
    stack_set ge v ve (c_stack c) s' ->
    Q oskip z (cnf s' (c_mem c)) n
  in valid n P (slset v e) Q.
Proof.
unfold valid, safe; intros.
step.
apple Hk.
unfold pls in *; firstorder.
Qed.

Lemma sound_gset:
  forall n x y Q,
  let P z c n := forall lx vy m',
    leva ge c x lx ->
    eval ge c y vy ->
    mem_set ge lx vy (c_mem c) m' ->
    Q oskip z (cnf (c_stack c) m') n
  in valid n P (sgset x y) Q.
Proof.
unfold valid, safe; intros.
step.
apple Hk.
unfold pls in *; firstorder.
Qed.

Lemma sound_seq:
  forall n s1 s2 P Q R
         (HQR: forall o z c r, o <> oskip -> Q o z c r -> R o z c r)
         (VALID1: valid n P s1 Q)
         (VALID2: valid n (Q oskip) s2 R),
  valid n P (sseq s1 s2) R.
Proof.
unfold valid at 3, safe; intros.
step.
apple (VALID1 m); try eassumption.
unfold safek, safe; intuition.
+ step.
  apple (VALID2 m); try eassumption.
  apple Hk.
+ step.
  apple Hk.
  unfold pls in *; intuition.
  destruct H0 as [? [? ?]].
  esplit. esplit; eauto.
  eapply HQR. congruence. eauto.
+ step.
  apple Hk.
  unfold pls in *; intuition.
  destruct H0 as [? [? ?]].
  esplit. esplit; eauto.
  eapply HQR. congruence. eauto.
Qed.

Definition ifP b P e: assn := fun z c n =>
  (exists ve, eval ge c e ve /\ val_bool ve b) /\ P z c n.

Lemma sound_if:
  forall n e s1 s2 P Q
         (VALID: forall b, valid n (ifP b P e) (if b then s1 else s2) Q),
  valid n P (sif e s1 s2) Q.
Proof.
unfold valid at 2, ifP, safe; intros.
step; eapply (VALID b).
omega. apple Hk. firstorder.
Qed.

Lemma sound_loop:
  forall n s I Q
         (VALID: valid n (I oskip) s I)
         (HIJ1: forall z c r, I obreak z c r -> Q oskip z c r)
         (HIJ2: forall x z c r, I (oret x) z c r -> Q (oret x) z c r),
  valid n (I oskip) (sloop s) Q.
Proof.
unfold valid at 2; intros.
induction m using lt_wf_rec.
unfold safe; intros.
step.
apple (VALID m); try eassumption.
unfold safek, safe; intuition.
+ step.
  apple (H m); try eassumption.
  apple Hk.
+ step.
  apple Hk.
  unfold pls in *; firstorder.
+ step.
  apple Hk.
  unfold pls in *; firstorder.
Qed.

(* Precondition of a call statement. *)
Definition enter f args Pg L: assn :=
  pls (fun z c r => forall vargs,
        evall ge c args vargs ->
        Pg z (c_mem c) vargs r /\ L z (c_stack c))
      (fun _ => Z.to_nat (frame f)).

(* Postcondition of a call statement. *)
Definition leave f vo Qg L o: assn :=
  match o with
  | oskip =>
    pls (fun z c r => exists vret s,
          ret_stack ge vo vret s (c_stack c) /\
          Qg z (c_mem c) vret r /\ L z s)
        (fun _ => Z.to_nat (frame f))
  | _ => fun _ _ _ => False
  end.

Section FRAME_NONNEG.
Hypothesis FNN: forall f, 0 <= frame f.

Ltac phi n :=
  match goal with
  | [ |- runs _ _ ?bnd ] =>
      replace bnd with n
      by (autorewrite with step;
          try rewrite Z2Nat.id by (apply FNN);
          try omega)
  end.

Lemma sound_call:
  forall n vo f l Pg Qg L
         (VALIDF: validf n Pg f Qg),
  valid (S n) (enter f l Pg L) (scall vo f l) (leave f vo Qg L).
Proof.
unfold valid, safe, enter, leave, pls; intros.
destruct H as [? [[np [? ?]] ?]]. subst.

step. phi (Z.of_nat (np + x z)).

eapply VALIDF.
+ eassumption.
+ omega.
+ instantiate (1 := x). instantiate (1 := z).
  unfold safek, valid, safe, pls; intuition.
  - step.
  - step.
  - destruct H0 as [nq [? ?]]. subst.
    step. phi (Z.of_nat (nq + Z.to_nat (frame f) + x z)).
    apple Hk.
    repeat eexists; eauto.
    firstorder.
+ unfold pls; firstorder.
Qed.

Lemma sound_call1:
  forall n C vo f l Pg Qg L
         (Cf: C f = Some (Pg, Qg))
         (VALIDC: validC n C),
  valid (S n) (enter f l Pg L) (scall vo f l) (leave f vo Qg L).
Proof.
intros; apply sound_call.
unfold validf; intros; apple VALIDC; eauto.
Qed.

Lemma sound_call2:
  forall n C vo f l Pg Qg L
         (VALIDF: forall n, validC n (app C Pg f Qg) -> validf (S n) Pg f Qg)
         (VALIDC: validC n C),
  valid (S n) (enter f l Pg L) (scall vo f l) (leave f vo Qg L).
Proof.
intros; apply sound_call.
unfold validf; intros; apple validf_ind; eauto.
Qed.
End FRAME_NONNEG.

Lemma sound_frame:
  forall n P s Q x
         (VALIDS: valid n P s Q),
  valid n (pls P x) s (fun o => pls (Q o) x).
Proof.
unfold valid at 2, safe; intros.
eapply VALIDS. omega.
instantiate (1 := fun z => plus (x z) (x0 z)).
unfold safek, safe; intuition;
 eapply Hk, pls_assoc; eassumption.
apply pls_assoc; assumption.
Qed.

Definition wk P Q Pw Qw :=
  forall z cp r, Pw z cp r -> exists z',
  P z' cp r /\ (forall cq o r, Q o z' cq r -> Qw o z cq r).

Lemma sound_consequence:
  forall n P s Q Pw Qw
         (W: wk P Q Pw Qw)
         (VALIDS: valid n P s Q),
  valid n Pw s Qw.
Proof.
unfold valid, safe, wk; intros.
destruct H as [? [? ?]].
refine (_ (W z _ _ _)); eauto.
intros [z' [Pz' WQ]].
eapply VALIDS. assumption.
instantiate (1 := fun _ => x z).
instantiate (1 := z').
unfold safek, safe; intuition;
 eapply Hk; firstorder.
firstorder.
Qed.

End QLOGIC.
