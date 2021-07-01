(************************************************************************)
(*                                                                      *)
(*                Quantitative Hoare Logic for Clight                   *)
(*                                                                      *)
(*  Author: Quentin Carbonneaux (c) 2014              Yale University   *)
(*                                                                      *)
(************************************************************************)


Require Import Coqlib.
Require Import AST.
Require Import Globalenvs.
Require Import Memory.
Require Import Cxlight.
Require Import Logic.

Section AUTOBOUND.
Context
  {aux: Type}                    (* Arbitrary auxiliary variables type. *)
  (F: fid -> Z)                  (* Stack frame of functions. *)
  (FNN: forall f, 0 <= F f).     (* Reasonable assumption on a frame. *)

(* the program we are working on *)
Variable (p: program).
Let ge := Genv.globalenv p.


Function liftO {A B C: Type} (f: A -> B -> C) (ox: option A) (oy: option B): option C :=
  match ox with
  | Some x => match oy with
              | Some y => Some (f x y)
              | None => None
              end
  | None => None
  end.

Definition bctx: Type := fid -> option Z.

(* This is the main automation procedure, using a
   "context" mapping each function to its stack
   consumption it gives the stack needs of one
   statement. *)
Fixpoint B (Phi: bctx) (s: stm): option Z :=
  match s with
  | scall _ f _ => liftO Z.add (Some (F f)) (Phi f)
  | sseq s1 s2 => liftO Z.max (B Phi s1) (B Phi s2)
  | sif _ st sf => liftO Z.max (B Phi st) (B Phi sf)
  | sloop s => B Phi s
  | _ => Some 0
  end.

Ltac injectSome :=
  match goal with
  | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
  end.

Lemma B_nonneg:
  forall Phi (PHINONNEG: forall f n, Phi f = Some n -> 0 <= n),
  forall s n, B Phi s = Some n -> 0 <= n.
Proof.
induction s; simpl; intros;
  try injectSome; try omega; auto.
revert H; case_eq (Phi f); try discriminate.
intros; injectSome.
generalize (PHINONNEG _ _ H).
generalize (FNN f).
intros; omega.
revert H; case_eq (B Phi s1); case_eq (B Phi s2); try discriminate.
simpl; intros; injectSome.
eapply Z.le_trans; [| apply Z.le_max_l ]; auto.
revert H; case_eq (B Phi s1); case_eq (B Phi s2); try discriminate.
simpl; intros; injectSome.
eapply Z.le_trans; [| apply Z.le_max_l ]; auto.
Qed.


(* Validity of the bounds. *)

(* Define trivial function pre/post-conditions and
   assertions associated to a given integer. *)

Definition fun_pre  n (_: aux) (_: mem) (_: list val) phi :=
  n <= Z.of_nat phi.
Definition fun_post n (_: aux) (_: mem) (_: option val) phi :=
  n <= Z.of_nat phi.

Definition mkassn n: assn aux :=
  fun _ _ phi => n <= Z.of_nat phi.


(* Takes a 'bctx' and lifts it to a Logic context
   to be used in logic derivations. *)
Definition mkctx (Phi: bctx) (f: fid) :=
  match Phi f with
  | Some nf => Some (fun_pre nf, fun_post nf)
  | None => None
  end.


(* Define the validity of a bound and a context
   using the 'valid' defined by the quantitative logic. *)

Definition valid_bound (s: stm) n :=
  forall i, valid aux ge F i (mkassn n) s (fun _ => mkassn n).
Definition valid_bctx (Phi: bctx) :=
  forall i, validC aux ge F i (mkctx Phi).


(* prove a weaker consequence rule useful later *)
Lemma weak_pre:
  forall (P Pw: assn aux) (Q: oassn aux)
         (WP: forall z c n, Pw z c n -> P z c n)
         n s (VALID: valid aux ge F n P s Q),
  valid aux ge F n Pw s Q.
Proof.
intros; eapply sound_consequence; eauto.
intro; eauto.
Qed.

(* prove a lemma for compound statement *)
Lemma valid_max_l:
  forall s a b (ANNEG: 0 <= a) (BNNEG: 0 <= b)
         (VA: valid_bound s a),
  valid_bound s (Z.max a b).
Proof.
unfold valid_bound; intros.
eapply sound_consequence;
 [| apply sound_frame with (x := fun _ => Z.to_nat (Z.max a b - a));
    apply VA ].
unfold wk, pls, mkassn; intros.
generalize (Z.le_max_l a b); intro.
exists z; intuition.
exists (Z.to_nat (Z.of_nat r - Z.max a b + a)).
split.
rewrite Z2Nat.id; omega.
apply Nat2Z.inj.
rewrite <- Z2Nat.inj_add by omega.
rewrite Z2Nat.id; omega.
destruct H1 as [x [? ?]]; subst.
replace x with (Z.to_nat (Z.of_nat x)).
rewrite <- Z2Nat.inj_add by omega.
rewrite Z2Nat.id; omega.
apply Nat2Z.id.
Qed.

Lemma valid_max_r:
  forall s a b (ANNEG: 0 <= a) (BNNEG: 0 <= b)
         (VB: valid_bound s b),
  valid_bound s (Z.max a b).
Proof.
intros. rewrite Z.max_comm; auto using valid_max_l.
Qed.

Lemma sound_B:
  forall Phi (PHINONNEG: forall f n, Phi f = Some n -> 0 <= n)
         (CVALID: valid_bctx Phi) s n
         (BS: B Phi s = Some n),
  valid_bound s n.
Proof.
unfold valid_bound.
induction s; intros;
 simpl in BS;
 try injectSome.

+ apply sound_skip.

+ eapply weak_pre; [| apply sound_gset ].
  unfold mkassn; intuition.

+ eapply weak_pre; [| apply sound_lset ].
  unfold mkassn; intuition.

+ apply sound_ret with (Q := fun _ => mkassn 0).

+ apply sound_break.

+ case_eq (Phi f).
  2: intros HPHI; rewrite HPHI in *; discriminate.
  intros phif HPHI; rewrite HPHI in *.
  injectSome.

  eapply valid_le; [ apply Le.le_n_Sn |].
  eapply sound_consequence;
   [| apply sound_call2
       with (C := mkctx Phi)
            (Pg := fun_pre phif)
            (Qg := fun_post phif)
            (L := fun _ _ => True); eauto
   ].
  unfold wk, enter, leave, mkassn, pls, fun_pre, fun_post; intros.
  assert (0 <= phif) by eauto.
  assert (0 <= F f) by eauto.
  exists z; intuition.
  exists (Z.to_nat (Z.of_nat r - (F f))); intuition.
  rewrite Z2Nat.id; omega.
  apply Nat2Z.inj.
  rewrite Nat2Z.inj_add.
  repeat rewrite Z2Nat.id; omega.
  destruct o;
  repeat match goal with
         | [ H: exists _, _ |- _ ] => destruct H
         | [ H: _ /\ _ |- _ ] => destruct H
         end; try omega.
  subst.
  rewrite Nat2Z.inj_add.
  rewrite Z2Nat.id by apply FNN.
  omega.

  unfold validf; intros.
  apply CVALID; eauto.
  unfold mkctx; rewrite HPHI.
  reflexivity.

+ functional inversion BS; subst.
  apply sound_seq with (Q := fun _ => mkassn (Z.max x y)).
  intuition.
  apply valid_max_l; eauto using B_nonneg.
  unfold valid_bound; eapply IHs1; congruence.
  apply valid_max_r; eauto using B_nonneg.
  unfold valid_bound; eapply IHs2; congruence.

+ functional inversion BS; subst.
  apply sound_if with (Q := fun _ => mkassn (Z.max x y)).
  intros []; apply weak_pre with (P := mkassn (Z.max x y));
   try (unfold ifP; intuition).
  apply valid_max_l; eauto using B_nonneg.
  unfold valid_bound; eapply IHs1; congruence.
  apply valid_max_r; eauto using B_nonneg.
  unfold valid_bound; eapply IHs2; congruence.

+ eapply sound_consequence;
   [| apply sound_loop
       with (I := fun _ => mkassn n)
            (Q := fun _ => mkassn n)
   ]; unfold mkassn; intuition.
  unfold wk, mkassn; intros.
  exists z; intuition.
  eapply IHs; eauto.
Qed.


(* definition of the bound for non-recursive programs *)
Require Import List.
Require Import Arith.
Require Import PArith.

(* bound function with maximum depth *)
Fixpoint bound_of_lvl (lvl: nat) (f: fid) :=
  match lvl with
  | O => None
  | S lvl' =>
      match find_func_ ge f with
      | Some bdy => B (bound_of_lvl lvl') bdy
      | None => None
      end
  end.

Lemma bound_of_lvl_nonneg:
  forall lvl f n, bound_of_lvl lvl f = Some n -> 0 <= n.
Proof.
induction lvl; simpl; try discriminate.
intros until n.
destruct (find_func_ ge f); try discriminate.
eauto using B_nonneg.
Qed.

(* on well formed programs, B_of is complete *)
Definition bound_of f :=
  bound_of_lvl (S (Pos.to_nat f)) f.

Theorem bound_lvl_sound:
  forall l, valid_bctx (bound_of_lvl l).
Proof.
unfold valid_bctx, mkctx, validC.
induction l; intros; try discriminate.
unfold validf; intros bdy HFIND.
simpl in H, HFIND.
destruct (find_func_ ge f); try discriminate.
inv HFIND.
case_eq (B (bound_of_lvl l) bdy).
2: intro HB; rewrite HB in *; discriminate.
intros n HB; rewrite HB in *.
inv H.
eapply sound_consequence;
 [| eapply sound_B; eauto ].
unfold wk, fun_pre, fun_post, mkassn; intros.
exists z; intuition.
destruct H as [? [? ?]]; omega.
destruct o; intuition.
eauto using bound_of_lvl_nonneg.
Qed.

Inductive in_stm (f: fid): stm -> Prop :=
  | in_stm_call: forall v l, in_stm f (scall v f l)
  | in_stm_seq1: forall s1 s2, in_stm f s1 -> in_stm f (sseq s1 s2)
  | in_stm_seq2: forall s1 s2, in_stm f s2 -> in_stm f (sseq s1 s2)
  | in_stm_ift: forall e st sf, in_stm f st -> in_stm f (sif e st sf)
  | in_stm_iff: forall e st sf, in_stm f sf -> in_stm f (sif e st sf)
  | in_stm_loop: forall s, in_stm f s -> in_stm f (sloop s).
Hint Constructors in_stm.

Lemma B_in_stm:
  forall Phi s,
  (forall f, in_stm f s -> exists nf, Phi f = Some nf) ->
  exists ns, B Phi s = Some ns.
Proof.
induction s; intros;
 try (eexists; reflexivity).
exploit H; eauto.
clear H; intros [nf HPHI].
exists (F f + nf).
simpl; rewrite HPHI; reflexivity.
assert (S1: exists ns1, B Phi s1 = Some ns1). eauto.
assert (S2: exists ns2, B Phi s2 = Some ns2). eauto.
destruct S1 as [n1 HS1].
destruct S2 as [n2 HS2].
exists (Z.max n1 n2).
simpl; rewrite HS1, HS2; reflexivity.
assert (S1: exists ns1, B Phi s1 = Some ns1). eauto.
assert (S2: exists ns2, B Phi s2 = Some ns2). eauto.
destruct S1 as [n1 HS1].
destruct S2 as [n2 HS2].
exists (Z.max n1 n2).
simpl; rewrite HS1, HS2; reflexivity.
assert (SL: exists n, B Phi s = Some n). eauto.
destruct SL as [n HN].
exists n.
simpl; rewrite HN; reflexivity.
Qed.

(* hypothesis checked on the input program *)
Definition CLOSED (defs: list (ident * globdef _ Ctypes.type)) :=
  forall id fi, In (id, Gfun fi) defs ->
                forall id', in_stm id' fi.(fi_body) ->
                exists gi, In (id', Gfun gi) defs.
Definition CG_WELLFOUNDED (defs: list (ident * globdef _ Ctypes.type)) :=
  forall id fi, In (id, Gfun fi) defs ->
                forall id', in_stm id' fi.(fi_body) ->
                Pos.lt id' id.

Section PROG_NONREC.
Hypothesis PROG_DEFS_NOREPET: list_norepet (prog_defs_names p).

Lemma find_func_defs:
  forall f fi,
  In (f, Gfun fi) p.(prog_defs) ->
  find_func_ ge f = Some fi.(fi_body).
Proof.
unfold find_func_, find_finfo; intros.
exploit Genv.find_funct_ptr_exists; eauto.
fold ge. intros [b [SYM PTR]].
rewrite SYM, PTR.
reflexivity.
Qed.

Hypothesis PROG_CLOSED: CLOSED p.(prog_defs).
Hypothesis PROG_CG_WELLFOUNDED: CG_WELLFOUNDED p.(prog_defs).

Theorem bound_of_lvl_complete:
  forall lvl f (LVL: lt (Pos.to_nat f) lvl)
         fi (FDEF: In (f, Gfun fi) p.(prog_defs)),
  exists n, bound_of_lvl lvl f = Some n.
Proof.
induction lvl using lt_wf_rec; intros.
destruct lvl; [ omega | simpl ].
rewrite find_func_defs with (fi := fi) by eauto.
apply B_in_stm. intros g ?.
exploit PROG_CLOSED; eauto.
intros [gi HG].
apply H with (fi := gi); eauto.
clear HG.
exploit PROG_CG_WELLFOUNDED; eauto.
intros HFG.
rewrite Pos2Nat.inj_lt in HFG.
omega.
Qed.

Theorem bound_of_complete:
  forall f fi (FDEF: In (f, Gfun fi) p.(prog_defs)),
  exists n, bound_of f = Some n.
Proof.
unfold bound_of. intros.
eapply bound_of_lvl_complete.
omega. eassumption.
Qed.
End PROG_NONREC.


(* checkers for the properties above *)
Definition prog_funs: forall gdefs,
  { fs | forall (f: ident),
         In f fs <-> exists (fi: finfo), In (f, Gfun (V := Ctypes.type) fi) gdefs }.
induction gdefs.
 exists nil. split; simpl. tauto. intros [? ?]; tauto.
destruct IHgdefs as [fs HFS].
destruct a.
destruct g.
exists (i :: fs). intro g; split.
intros [EQ | HIN]; subst.
exists f; simpl; auto.
exploit (proj1 (HFS g)); auto.
intros [fi HFI].
exists fi; right; auto.
intros [fi [EQ | IN]].
inv EQ. left; reflexivity.
exploit (proj2 (HFS g)); eauto.
simpl; tauto.
exists fs; intro g; split.
intro H.
exploit (proj1 (HFS g)); auto.
intros [fi HIN]; exists fi.
simpl; tauto.
intros [hi [WRONG | IN]].
congruence.
exploit (proj2 (HFS g)); auto.
exists hi; assumption.
Defined.

Fixpoint forall_fids (P: fid -> bool) s :=
  match s with
  | scall _ f _ => P f
  | sseq s1 s2 => forall_fids P s1 && forall_fids P s2
  | sif _ st sf => forall_fids P st && forall_fids P sf
  | sloop s => forall_fids P s
  | _ => true
  end.

Lemma forall_fids_forall:
  forall P s (ALL: forall_fids P s = true),
  forall f, in_stm f s -> P f = true.
Proof.
induction s; intros; try now (inv H).
simpl in ALL.
exploit andb_prop; eauto. intros [? ?].
inv H; [ apply IHs1 | apply IHs2 ]; auto.
simpl in ALL.
exploit andb_prop; eauto. intros [? ?].
inv H; [ apply IHs1 | apply IHs2 ]; auto.
simpl in ALL; inv H; auto.
Qed.

Definition is_closed fs :=
  forall_fids (fun f => if in_dec peq f fs then true else false).

Lemma is_closed_spec:
  forall funs s (CLOS: is_closed funs s = true),
  forall f, in_stm f s -> In f funs.
Proof.
intros.
exploit forall_fids_forall; eauto.
simpl; intros.
destruct (in_dec peq f funs).
assumption. congruence.
Qed.

Definition check_closed defs :=
  let check_def def :=
    match def with
    | (_, Gfun fi) =>
        is_closed (proj1_sig (prog_funs defs)) fi.(fi_body)
    | _ => true
    end
  in forallb check_def defs.

Lemma check_closed_spec:
  forall defs (CLOS: check_closed defs = true), CLOSED defs.
Proof.
unfold check_closed, CLOSED; intros.
destruct (prog_funs defs) as [funs HFUNS]. simpl in *.
apply HFUNS.
eapply is_closed_spec; eauto.
apply (proj1 (forallb_forall _ _) CLOS (id, Gfun fi)).
assumption.
Qed.

Definition struct_gt f :=
  forall_fids (fun g => match Pos.compare g f with Lt => true | _ => false end).

Lemma struct_gt_spec:
  forall f s (SLT: struct_gt f s = true),
  forall g, in_stm g s -> Pos.lt g f.
Proof.
intros.
exploit forall_fids_forall; eauto.
simpl; intros.
case_eq (Pos.compare g f);
 intro EQ; rewrite EQ in *;
 congruence.
Qed.

Definition check_cg_wellfounded defs :=
  let check_def def :=
    match def with
    | (f, Gfun fi) => struct_gt f fi.(fi_body)
    | _ => true
    end
  in forallb check_def (defs: list (ident * globdef finfo Ctypes.type)).

Lemma check_cg_wellfounded_spec:
  forall defs (WF: check_cg_wellfounded defs = true), CG_WELLFOUNDED defs.
Proof.
unfold check_cg_wellfounded, CG_WELLFOUNDED; intros.
eapply struct_gt_spec; eauto.
apply (proj1 (forallb_forall _ _) WF (id, Gfun fi)).
assumption.
Qed.

Definition check_norepet l :=
  if list_norepet_dec peq l then true else false.

Lemma check_norepet_spec:
  forall l (NOREP: check_norepet l = true), list_norepet l.
Proof.
unfold check_norepet; simpl; intros.
destruct (list_norepet_dec peq l); congruence.
Qed.

End AUTOBOUND.
