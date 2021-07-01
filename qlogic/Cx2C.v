(************************************************************************)
(*                                                                      *)
(*                Quantitative Hoare Logic for Clight                   *)
(*                                                                      *)
(*  Author: Quentin Carbonneaux (c) 2014              Yale University   *)
(*                                                                      *)
(************************************************************************)


Require Import Arith.
Require Import Memory.
Require Import Ctypes.
Require Import AST.
Require Import List.
Require Import Smallstep.
Require Import Behaviors.
Require Import Stackbounds.
Require Import Globalenvs.
Require Import Values.
Require Import Integers.
Require Import Maps.
Require Import Events.
Require Import Errors.
Require Import Clight.
Require Import Cxlight.

Open Scope error_monad_scope.


(* code for the transformation from Cxlight to Clight *)
Definition type_of_fi fi :=
  Tfunction (type_of_params fi.(fi_args)) fi.(fi_return).

Function type_of_fid (ge: genv) (f: fid) :=
  match Genv.find_symbol ge f with
  | Some b =>
      match Genv.find_var_info ge b with
      | Some gv => Some (gvar_info gv)
      | None =>
          match Genv.find_funct_ptr ge b with
          | Some fi => Some (type_of_fi fi)
          | None => None
          end
      end
  | None => None
  end.

Function expr_of_fid (ge: genv) (f: fid) :=
  match find_finfo ge f with
  | Some fi =>
      match type_of_fid ge f with
      | Some ty =>
          if type_eq ty (type_of_fi fi)
          then OK (Evar f (type_of_fi fi))
          else Error (msg "type error")
      | None => Error (msg "type error")
      end
  | None => Error (msg "use of undefined function ")
  end.

Fixpoint transf_stm (ge: genv) (s: stm) :=
  match s with
  | sskip => OK Sskip
  | sgset x y => OK (Sassign x y)
  | slset v e => OK (Sset v e)
  | sret e => OK (Sreturn e)
  | sbreak => OK (Sbreak)
  | scall v f l =>
      do ef <- expr_of_fid ge f;
      OK (Scall v ef l)
  | sseq s1 s2 =>
      do s1' <- transf_stm ge s1;
      do s2' <- transf_stm ge s2;
      OK (Ssequence s1' s2')
  | sif t s1 s2 =>
      do s1' <- transf_stm ge s1;
      do s2' <- transf_stm ge s2;
      OK (Sifthenelse t s1' s2')
  | sloop s =>
      do s' <- transf_stm ge s;
      OK (Sloop Sskip s')
  end.

Definition transf_finfo (fi: finfo) (body: statement) :=
  mkfunction
    (fi_name fi)                (* fn_id *)
    (fi_return fi)              (* fn_return *)
    (fi_args fi)                (* fn_params *)
    (nil)                       (* fn_vars *)
    (fi_locals fi)              (* fn_temps *)
    (body).                     (* fn_body *)

Definition transf_fundef (ge: genv) (fi: finfo): res Clight.fundef :=
  do body <- transf_stm ge (fi_body fi);
  OK (Internal (transf_finfo fi body)).

Definition transf_program p: res Clight.program :=
  transform_partial_program (transf_fundef (Genv.globalenv p)) p.


(* correctness proof of the above transformation *)
Section CORRECTNESS.
Variable prog: program.
Variable tprog: Clight.program.
Hypothesis TRANS_PROG: transf_program prog = OK tprog.
Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.
Hypothesis PROG_WF:
  forall f fi, find_finfo ge f = Some fi -> fi.(fi_name) = f.

Fixpoint cont_invariant k main f: Prop :=
  match k with
  | kseq _ k => cont_invariant k main f
  | kloop _ k => cont_invariant k main f
  | kcall _ fname _ _ =>
      forall fi, find_finfo ge fname = Some fi ->
                 transf_fundef ge fi = OK (Internal f)
  | kstop => transf_fundef ge main = OK (Internal f)
  end.

Inductive match_cont (main: finfo): cont -> Clight.cont -> Prop :=
  | match_kcall:
      forall v f fn stk k ck,
      cont_invariant k main fn ->
      match_cont main k ck ->
      match_cont main (kcall v f stk k) (Kcall v fn empty_env stk ck)

  | match_kseq:
      forall s s' k ck,
      match_cont main k ck ->
      transf_stm ge s = OK s' ->
      match_cont main (kseq s k) (Kseq s' ck)

  | match_kloop:
      forall s s' k ck,
      match_cont main k ck ->
      transf_stm ge s = OK s' ->
      match_cont main (kloop s k) (Kloop2 Sskip s' ck)

  | match_kstop:
      match_cont main kstop Kstop.

Fixpoint cont_depth k :=
  match k with
  | kseq _ k => S (cont_depth k)
  | kloop _ k => S (cont_depth k)
  | kcall _ _ _ _ => 0
  | kstop => 1
  end.

Fixpoint call_cont k :=
  match k with
  | kseq _ k => call_cont k
  | kloop _ k => call_cont k
  | _ => k
  end.

Lemma match_call_cont:
  forall m k k', match_cont m k k' -> match_cont m (call_cont k) (Clight.call_cont k').
Proof. induction 1; try econstructor; eassumption. Qed.

Function is_sret (s: stm) :=
  match s with
  | sret _ => true
  | _ => false
  end.

Inductive match_states: nat -> state -> Clight.state -> Prop :=
  | match_running:
      forall i main f s s' k stk m ck
             (MAIN: find_finfo ge prog.(prog_main) = Some main)
             (KINV: cont_invariant k main f)
             (TRANS: transf_stm ge s = OK s')
             (NORET: is_sret s = false)
             (MATCHK: match_cont main k ck)
,
      match_states i
        (Running main s k (cnf stk m))
        (State f s' ck empty_env stk m)

  | match_returning:
      forall main f r k stk m ck
             (MAIN: find_finfo ge prog.(prog_main) = Some main)
             (KINV: cont_invariant k main f)
             (MATCHK: match_cont main (call_cont k) (Clight.call_cont ck))
,
      match_states (cont_depth k)
        (Running main (sret r) k (cnf stk m))
        (State f (Sreturn r) ck empty_env stk m)

  | match_initial:
      forall main m cmain
             (MAIN: find_finfo ge prog.(prog_main) = Some main)
             (TRANS: transf_fundef ge main = OK cmain)
,
      match_states 0
        (Initial main m)
        (Callstate cmain nil Kstop m)

  | match_final:
      forall code m
,
      match_states 0
        (Final code)
        (Returnstate (Vint code) Kstop m)
.

Lemma find_symbol_preserved: forall id,
  Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof. eapply Genv.find_symbol_transf_partial; eassumption. Qed.

Lemma find_funct_ptr_preserved:
  forall b f, Genv.find_funct_ptr ge b = Some f ->
  exists f', Genv.find_funct_ptr tge b = Some f' /\
             transf_fundef ge f = OK f'.
Proof.
unfold ge, tge; intros.
eapply Genv.find_funct_ptr_transf_partial;
 eassumption.
Qed.

Lemma type_of_global_preserved:
  forall f ty, type_of_fid ge f = Some ty ->
  forall b, Genv.find_symbol ge f = Some b ->
            type_of_global tge b = Some ty.
Proof.
unfold ge, tge; intros.
unfold type_of_global.
functional inversion H;
 rewrite H2 in H0; injection H0; intro; subst;
 erewrite Genv.find_var_info_transf_partial by eassumption.
 + rewrite H3; reflexivity.
 + rewrite H3.
   refine (_ (Genv.find_funct_ptr_transf_partial _ _ _ _ _));
    try eassumption.
   intros [f' [FINDFUNCT TRANSF]].
   rewrite FINDFUNCT.
   monadInv TRANSF.
   reflexivity.
Qed.

Lemma types_preserved: forall l ty,
  find_info ge l = Some ty ->
  type_of_global tge l = Some ty.
Proof.
unfold find_info, type_of_global, tge, ge, transf_program.
intros; erewrite Genv.find_var_info_transf_partial by eassumption.
destruct (Genv.find_var_info (Genv.globalenv prog) l).
congruence.
discriminate.
Qed.

Lemma eval_trans: forall stk m,
  (forall e v,
     eval_expr ge (cnf stk m) e v ->
     Clight.eval_expr tge empty_env stk m e v) /\
  (forall e b ofs,
     eval_lvalue (trgenv ge) empty_env stk m e b ofs ->
     Clight.eval_lvalue tge empty_env stk m e b ofs).
Proof.
unfold eval_expr.
intros; apply eval_expr_lvalue_ind;
 intros; try (econstructor; eassumption).
eapply eval_Evar_global; try assumption.
rewrite find_symbol_preserved, find_symbol_trgenv.
assumption.
rewrite (types_preserved l ty); try reflexivity.
unfold find_info, type_of_global, Genv.find_var_info,
       Genv.find_funct_ptr in *.
destruct ge; simpl in *.
destruct (ZMap.get l genv_vars).
congruence.
rewrite ZMap.gi in H1; congruence.
Qed.

Lemma eval_preserved: forall stk m e v,
  eval ge (cnf stk m) e v ->
  Clight.eval_expr tge empty_env stk m e (fst v).
Proof.
intros; destruct H.
apply eval_trans; assumption.
Qed.

Lemma leva_preserved: forall stk m e v,
  leva ge (cnf stk m) e v ->
  Clight.eval_lvalue tge empty_env stk m e (fst (fst v)) (snd (fst v)).
Proof.
intros; destruct H.
apply eval_trans; assumption.
Qed.

Lemma eval_typeof: forall ge stk m e v,
  eval ge (cnf stk m) e v ->
  typeof e = snd v.
Proof.
intros; destruct H; congruence.
Qed.

Lemma leva_typeof: forall ge stk m e v,
  leva ge (cnf stk m) e v ->
  typeof e = snd v.
Proof.
intros; destruct H; congruence.
Qed.

Lemma evall_preserved:
  forall tyl vs vs'
         (CASTL: castl vs tyl vs')
         stk m es
         (EVALL: evall ge (cnf stk m) es vs),
  Clight.eval_exprlist tge empty_env stk m es tyl vs'.
Proof.
induction 1; intros.
inversion EVALL; subst.
constructor.
inversion EVALL; subst.
econstructor; eauto.
eapply eval_preserved; eassumption.
erewrite eval_typeof by eauto.
eassumption.
Qed.

Lemma set_opttemp_preserved:
  forall vo vxty vx stk stk',
  ret_stack ge vo vxty stk stk' ->
  vx = match vxty with None => Vundef | Some (vx, _) => vx end ->
  set_opttemp vo vx stk = stk'.
Proof.
inversion 1; subst; simpl.
+ destruct vr'. intros; subst.
  destruct vo; simpl in *; eauto.
  inversion H0; subst. reflexivity.
+ reflexivity.
Qed.

Lemma store_correct:
  forall f x lx y vy s' k stk m m',
  leva ge (cnf stk m) x lx -> 
  eval ge (cnf stk m) y vy ->
  mem_set ge lx vy m m' ->
  transf_stm ge (sgset x y) = OK s' ->
  step2 tge
    (State f s' k empty_env stk m) E0
    (State f Sskip k empty_env stk m').
Proof.
intros. monadInv H2.
destruct H1.
econstructor.
eapply leva_preserved. eassumption.
eapply eval_preserved. eassumption.
erewrite eval_typeof; eauto.
erewrite leva_typeof; eauto.
erewrite leva_typeof; eauto.
Qed.

Lemma set_correct:
  forall f v e ve s' k stk stk' m,
  eval ge (cnf stk m) e ve ->
  stack_set ge v ve stk stk' ->
  transf_stm ge (slset v e) = OK s' ->
  step2 tge
    (State f s' k empty_env stk m) E0
    (State f Sskip k empty_env stk' m).
Proof.
intros. monadInv H1.
destruct H0.
econstructor.
eapply eval_preserved; eassumption.
Qed.

Lemma match_usual:
  forall main f s s' k k' stk m
         (MAIN: find_finfo ge (prog_main prog) = Some main)
         (KINV: cont_invariant k main f)
         (TRANS: transf_stm ge s = OK s')
         (MATCHK: match_cont main k k'),
  match_states (cont_depth k)
    (Running main s k (cnf stk m))
    (State f s' k' empty_env stk m).
Proof.
intros.
case_eq (is_sret s); intro HS.
functional inversion HS; subst.
monadInv TRANS.
clear HS.
eapply match_returning.
assumption.
assumption.
apply match_call_cont, MATCHK.
eapply match_running; eassumption.
Qed.

(* forward simulation *)

Lemma initial_states:
  forall S,
  initial_state prog S ->
  exists i S', Clight.initial_state tprog S' /\ match_states i S S'.
Proof.
intros. destruct H.
functional inversion H0.
unfold ge0 in *.
refine (_ (find_funct_ptr_preserved _ _ _)); eauto.
intros [main' [FUNCTPTRMAIN TRANSMAIN]].
assert (TRANSMAIN': transf_fundef ge main = OK main') by assumption.
monadInv TRANSMAIN'.
eexists; eexists; split.
econstructor.
eapply Genv.init_mem_transf_partial.
eassumption. eassumption.
fold tge; erewrite find_symbol_preserved by eassumption.
erewrite transform_partial_program_main by eassumption.
eassumption.
eassumption.
unfold transf_finfo; rewrite H1, H2.
reflexivity.
econstructor; eassumption.
Qed.

Lemma final_states:
  forall i S S' r,
  match_states i S S' -> final_state S r -> Clight.final_state S' r.
Proof.
intros. destruct H0.
inversion H; subst.
econstructor.
Qed.

Ltac inject :=
  repeat match goal with
         | [ H1: ?a = _, H2: ?a = _ |- _ ] =>
           rewrite H2 in H1; inversion H1;
           clear H1; subst
        end.

Ltac crunch :=
  (simpl; match goal with
      | [ |- _ = fi_name _ ] => symmetry; crunch
      | [ |- fi_name _ = _ ] => apply PROG_WF; eassumption
      | [ |- match_states _ _ _ ] => eapply match_usual; crunch
      | [ |- Clight.eval_expr _ _ _ _ _ _ ] => eapply eval_preserved; crunch
      end)
  || (try erewrite eval_typeof by eassumption; simpl in *; eassumption)
  || simpl; reflexivity || congruence || constructor.

Lemma simulation:
  forall s1 t s1', step ge s1 t s1' ->
  forall i s2, match_states i s1 s2 ->
  exists i', exists s2',
  (plus step2 tge s2 t s2' \/ (star step2 tge s2 t s2' /\ i' < i))
  /\ match_states i' s1' s2'.
Proof.
intros.
destruct H.

+ inversion H0; subst.
  assert (TRANSMAIN: transf_fundef ge main = OK cmain) by assumption.
  monadInv TRANS.
  destruct H. inversion H3; subst.
  replace (fi_name main) with (prog_main prog) in * by crunch.
  inject.
  eexists; eexists; split; [left |].
  eapply plus_one.
  econstructor; repeat crunch.
  eapply match_usual; repeat crunch.

+ destruct s1; inversion SEMKSTEP; subst.

  - inversion H0; subst.
    monadInv TRANS.
    inversion MATCHK; subst.
    eexists; eexists; split; [left |].
    eapply plus_one; crunch.
    crunch.

  - inversion H0; subst.
    monadInv TRANS.
    inversion MATCHK; subst.
    eexists; eexists; split; [left |].
    eapply plus_one; crunch.
    eapply match_usual; try crunch.
    simpl. rewrite H4; reflexivity.

  - inversion H0; subst.
    eexists; eexists; split; [left |];
      [ eapply plus_one, store_correct |];
      crunch.

  - inversion H0; subst.
    eexists; eexists; split; [left |];
      [ eapply plus_one, set_correct |];
      crunch.

  - inversion H0; subst.
    discriminate.
    inversion MATCHK; subst.
    inversion H8; subst; inversion H4; subst.
    * inversion H9; subst.
      assert (TRFI: transf_fundef ge fi = OK (Internal f))
       by (apply KINV; assumption).
      monadInv TRFI.
      eexists; eexists; split; [left |].
      eapply plus_two.
      econstructor; crunch.
      rewrite <- H6.
      econstructor; crunch.
      reflexivity.
      erewrite set_opttemp_preserved.
      crunch.
      eassumption.
      reflexivity.
    * inversion H; subst.
      assert (TRFI: transf_fundef ge fi = OK (Internal f))
        by (apply KINV; assumption).
      monadInv TRFI.
      eexists; eexists; split; [left |].
      eapply plus_two.
      econstructor; crunch.
      rewrite <- H6.
      econstructor; crunch.
      reflexivity.
      crunch.

  - inversion H0; subst.
    discriminate.
    exists (cont_depth k2); eexists; split; [right; split |].
    apply star_refl.
    simpl; omega.
    eapply match_returning; crunch.

  - inversion H0; subst.
    discriminate.
    exists (cont_depth k2); eexists; split; [right; split |].
    apply star_refl.
    simpl; omega.
    eapply match_returning; crunch.

  - inversion H0; subst.
    inversion MATCHK; subst.
    monadInv TRANS.
    eexists; eexists; split; [left |].
    eapply plus_one.
    econstructor.
    crunch.

  - inversion H0; subst.
    inversion MATCHK; subst.
    monadInv TRANS.
    eexists; eexists; split; [left |].
    eapply plus_one.
    econstructor.
    crunch.

  - inversion H0; subst.
    monadInv TRANS.
    simpl in H6.
    functional inversion H6.
    functional inversion H1.
    functional inversion EQ.
    destruct H11.
    inject.
    generalize (find_funct_ptr_preserved _ _ H2);
     intros [fi' [PTRFI TRANSFI]].
    monadInv TRANSFI.
    eexists; eexists; split; [left |].
    eapply plus_two.
    econstructor. reflexivity.
    econstructor.
    eapply eval_Evar_global.
    rewrite PTree.gempty; reflexivity.
    rewrite find_symbol_preserved; eassumption.
    erewrite type_of_global_preserved; crunch.
    repeat crunch.
    eapply evall_preserved; eassumption.
    eassumption.
    reflexivity.
    constructor; repeat crunch.
    simpl; reflexivity.
    eapply match_usual; eauto.
    simpl. intros; inject.
    unfold transf_fundef.
    rewrite EQ0.
    reflexivity.
    repeat crunch.

  - inversion H0; subst.
    monadInv TRANS.
    eexists; eexists; split; [left |].
    eapply plus_one; crunch.
    crunch.

  - inversion H0; subst.
    monadInv TRANS.
    destruct b0.
    eexists; eexists; split; [left |].
    eapply plus_one; econstructor; crunch.
    crunch.
    eexists; eexists; split; [left |].
    eapply plus_one; econstructor; crunch.
    crunch.

  - inversion H0; subst.
    monadInv TRANS.
    eexists; eexists; split; [left |].
    eapply plus_two.
    econstructor.
    econstructor; left; crunch.
    reflexivity.
    crunch.

+ inversion H0; subst.
  discriminate.
  inversion RETEVAL; clear RETEVAL.
  replace (fi_name main) with (prog_main prog) in * by crunch.
  assert (FMAIN: transf_fundef ge main = OK (Internal f)) by
    (apply KINV; reflexivity).
  inversion H3; subst.
  monadInv FMAIN. inject.
  exists 0; eexists; split; [right; split |].
  eapply star_one.
  econstructor; crunch.
  simpl; omega.
  inversion MATCHK.
  apply match_final.
Qed.


Theorem correctness:
  forward_simulation (semantics prog) (Clight.semantics2 tprog).
Proof.
econstructor.
+ exact lt_wf.
+ exact initial_states.
+ exact final_states.
+ exact simulation.
+ exact find_symbol_preserved.
Qed.

Theorem backward_simulation_Clight:
  backward_simulation (semantics prog) (Clight.semantics2 tprog).
Proof.
apply forward_to_backward_simulation.
apply correctness.
apply Cxlight.semantics_receptive.
apply Clight.semantics_determinate.
Qed.

End CORRECTNESS.

Require Import Compiler.
Require Import Prune.
Require Import Coqlib.

Definition transf_cxlight_to_mach p :=
  apply_partial _ _ (transf_program p) transf_clight2_to_mach.

Definition transf_cxlight_program p :=
  apply_partial _ _ (transf_program p) transf_clight2_program.

Section WITHBOUND.
Variables
  (bound : Integers.Int.int)
  (Hbound: (Stacklayout.strong_align
         | Integers.Int.unsigned bound + size_chunk Mint32))
  (external_event_needs: Events.event -> Z).

Lemma transf_cxlight_program_exists_mach:
  forall p pasm, transf_cxlight_program p = OK pasm ->
  { pmach | transf_cxlight_to_mach p = OK pmach
         /\ transf_mach_program pmach = OK pasm }.
Proof.
unfold transf_cxlight_program, transf_cxlight_to_mach, transf_clight2_program.
unfold apply_partial.
intros until pasm.
case_eq (transf_program p); try discriminate.
intros pclight ?.
case_eq (transf_clight2_to_mach pclight); try discriminate.
eauto.
Qed.

Theorem transf_cxlight_program_correct:
  forall p
         (PROG_WF: forall f fi, find_finfo (Genv.globalenv p) f = Some fi -> fi.(fi_name) = f)
         (NOT_STUCK: not_stuck (prune_semantics (semantics p)))
         (NO_OVERFLOW: no_overflow_with_mach bound external_event_needs semantics transf_cxlight_to_mach p)
         tp (HTRANS: transf_cxlight_program p = OK tp),
    forward_simulation (Prune.prune_semantics (semantics p)) (Asm.semantics bound tp)
  * backward_simulation (Prune.prune_semantics (semantics p)) (Asm.semantics bound tp).
Proof.
intros until 4.
edestruct (transf_cxlight_program_exists_mach) as [pmach [Hpmach ?]]; eauto.
generalize Hpmach.
unfold transf_cxlight_to_mach, apply_partial.
case_eq (transf_program p); try discriminate.
intros pclight TRANS1 TRANS2.
assert (transf_clight2_program pclight = OK tp).
unfold transf_clight2_program, apply_partial.
rewrite TRANS2.
assumption.
generalize (correctness _ _ TRANS1 PROG_WF).
intro FORW.
generalize (backward_simulation_Clight _ _ TRANS1 PROG_WF).
intro BACK.
refine (_ (transf_clight2_program_correct _ _ _ _ _ _ _ _)); eauto.
destruct 1.
refine (_ (compose_forward_simulation _ _)).
3: eassumption.
2: eapply forward_simulation_prune; eauto.
intros LEFT.
split; auto.
eapply forward_to_backward_simulation.
assumption.
apply receptive_prune.
apply Cxlight.semantics_receptive.
apply Asm.semantics_determinate.
eapply not_stuck_backward.
eapply backward_simulation_prune.
eassumption.
eassumption.
red; red; intros. eapply NO_OVERFLOW. congruence.
eapply Behaviors.backward_simulation_same_safe_behavior.
eassumption. apply prune_not_stuck.
assumption. eassumption. assumption. assumption.
Qed.
End WITHBOUND.
