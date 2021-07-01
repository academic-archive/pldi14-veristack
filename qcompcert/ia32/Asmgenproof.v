(* *********************************************************************)
(*                                                                     *)
(*              The Compcert verified compiler                         *)
(*                                                                     *)
(*          Xavier Leroy, INRIA Paris-Rocquencourt                     *)
(*                                                                     *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  This file is distributed       *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*                                                                     *)
(* *********************************************************************)

(** Correctness proof for x86 generation: main proof. *)

Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Op.
Require Import Locations.
Require Mach.
Require Mach2.
Require Import Conventions.
Require Import Asm.
Require Import Asmgen.
Require Import Asmgenproof0.
Require Import Asmgenproof1.
Require Prune.

Section PRESERVATION.

Variable prog: Mach.program.
Variable tprog: Asm.program.
Hypothesis TRANSF: transf_program prog = Errors.OK tprog.

Let ge := Genv.globalenv prog.
Let tge := Genv.globalenv tprog.

Lemma symbols_preserved:
  forall id, Genv.find_symbol tge id = Genv.find_symbol ge id.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_symbol_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

Lemma functions_translated:
  forall b f,
  Genv.find_funct_ptr ge b = Some f ->
  exists tf, Genv.find_funct_ptr tge b = Some tf /\ transf_fundef f = Errors.OK tf.
Proof
  (Genv.find_funct_ptr_transf_partial transf_fundef _ TRANSF).

Lemma functions_transl:
  forall fb f tf,
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transf_function f = OK tf ->
  Genv.find_funct_ptr tge fb = Some (Internal tf).
Proof.
  intros. exploit functions_translated; eauto. intros [tf' [A B]].
  monadInv B. rewrite H0 in EQ; inv EQ; auto. 
Qed.

Lemma varinfo_preserved:
  forall b, Genv.find_var_info tge b = Genv.find_var_info ge b.
Proof.
  intros. unfold ge, tge. 
  apply Genv.find_var_info_transf_partial with transf_fundef.
  exact TRANSF. 
Qed.

(** * Properties of control flow *)

Lemma transf_function_no_overflow:
  forall f tf,
  transf_function f = OK tf -> list_length_z tf <= Int.max_unsigned.
Proof.
  intros. monadInv H. destruct (zlt (list_length_z x) Int.max_unsigned); monadInv EQ0.
  rewrite list_length_z_cons. omega. 
Qed.

Lemma exec_straight_exec:
  forall fb f c (* ep *) tf tc c' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c (* ep *) tf tc ->
  exec_straight tge tf tc rs m c' rs' m' ->
  plus step tge (State rs m) E0 (State rs' m').
Proof.
  intros. inv H.
  eapply exec_straight_steps_1; eauto.
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto. 
Qed.

Lemma exec_straight_at:
  forall fb f c (* ep *) tf tc c' (* ep' *) tc' rs m rs' m',
  transl_code_at_pc ge (rs PC) fb f c (* ep *) tf tc ->
  transl_code f c' (* ep' *) = OK tc' ->
  exec_straight tge tf tc rs m tc' rs' m' ->
  transl_code_at_pc ge (rs' PC) fb f c' (* ep' *) tf tc'.
Proof.
  intros. inv H. 
  exploit exec_straight_steps_2; eauto. 
  eapply transf_function_no_overflow; eauto.
  eapply functions_transl; eauto.
  intros [ofs' [PC' CT']].
  rewrite PC'. constructor; auto.
Qed.

(** The following lemmas show that the translation from Mach to Asm
  preserves labels, in the sense that the following diagram commutes:
<<
                          translation
        Mach code ------------------------ Asm instr sequence
            |                                          |
            | Mach.find_label lbl       find_label lbl |
            |                                          |
            v                                          v
        Mach code tail ------------------- Asm instr seq tail
                          translation
>>
  The proof demands many boring lemmas showing that Asm constructor
  functions do not introduce new labels.

  In passing, we also prove a "is tail" property of the generated Asm code.
*)

Section TRANSL_LABEL.

Remark mk_mov_label:
  forall rd rs k c, mk_mov rd rs k = OK c -> tail_nolabel k c.
Proof.
  unfold mk_mov; intros. 
  destruct rd; try discriminate; destruct rs; TailNoLabel.
Qed.
Hint Resolve mk_mov_label: labels.

Remark mk_shift_label:
  forall f r1 r2 k c, mk_shift f r1 r2 k = OK c -> 
  (forall r, nolabel (f r)) ->
  tail_nolabel k c.
Proof.
  unfold mk_shift; intros. TailNoLabel.
Qed.
Hint Resolve mk_shift_label: labels.

Remark mk_mov2_label:
  forall r1 r2 r3 r4 k,
  tail_nolabel k (mk_mov2 r1 r2 r3 r4 k).
Proof.
  intros; unfold mk_mov2. 
  destruct (ireg_eq r1 r2); TailNoLabel.
  destruct (ireg_eq r3 r4); TailNoLabel.
  destruct (ireg_eq r3 r2); TailNoLabel.
  destruct (ireg_eq r1 r4); TailNoLabel.
Qed.
Hint Resolve mk_mov2_label: labels.

Remark mk_div_label:
  forall f r1 r2 k c, mk_div f r1 r2 k = OK c -> 
  (forall r, nolabel (f r)) ->
  tail_nolabel k c.
Proof.
  unfold mk_div; intros. TailNoLabel. 
  eapply tail_nolabel_trans; TailNoLabel.
Qed.
Hint Resolve mk_div_label: labels.

Remark mk_mod_label:
  forall f r1 r2 k c, mk_mod f r1 r2 k = OK c -> 
  (forall r, nolabel (f r)) ->
  tail_nolabel k c.
Proof.
  unfold mk_mod; intros. TailNoLabel. 
  eapply tail_nolabel_trans; TailNoLabel.
Qed.
Hint Resolve mk_mod_label: labels.

Remark mk_shrximm_label:
  forall r n k c, mk_shrximm r n k = OK c -> tail_nolabel k c.
Proof.
  intros. monadInv H; TailNoLabel.
Qed.
Hint Resolve mk_shrximm_label: labels.

Remark mk_intconv_label:
  forall f r1 r2 k c, mk_intconv f r1 r2 k = OK c -> 
  (forall r r', nolabel (f r r')) ->
  tail_nolabel k c.
Proof.
  unfold mk_intconv; intros. TailNoLabel. 
Qed.
Hint Resolve mk_intconv_label: labels.

Remark mk_smallstore_label:
  forall f addr r k c, mk_smallstore f addr r k = OK c -> 
  (forall r addr, nolabel (f r addr)) ->
  tail_nolabel k c.
Proof.
  unfold mk_smallstore; intros. TailNoLabel. 
Qed.
Hint Resolve mk_smallstore_label: labels.

Remark loadind_label:
  forall base ofs ty dst k c,
  loadind base ofs ty dst k = OK c ->
  tail_nolabel k c.
Proof.
  unfold loadind; intros. destruct ty.
  TailNoLabel.
  destruct (preg_of dst); TailNoLabel.
Qed.

Remark storeind_label:
  forall base ofs ty src k c,
  storeind src base ofs ty k = OK c ->
  tail_nolabel k c.
Proof.
  unfold storeind; intros. destruct ty.
  TailNoLabel.
  destruct (preg_of src); TailNoLabel.
Qed.

Remark mk_setcc_label:
  forall xc rd k,
  tail_nolabel k (mk_setcc xc rd k).
Proof.
  intros. destruct xc; simpl; destruct (ireg_eq rd EDX); TailNoLabel.
Qed.

Remark mk_jcc_label:
  forall xc lbl' k,
  tail_nolabel k (mk_jcc xc lbl' k).
Proof.
  intros. destruct xc; simpl; TailNoLabel.
Qed.

Remark transl_cond_label:
  forall cond args k c,
  transl_cond cond args k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_cond; intros.
  destruct cond; TailNoLabel.
  destruct (Int.eq_dec i Int.zero); TailNoLabel.
  destruct c0; simpl; TailNoLabel.
  destruct c0; simpl; TailNoLabel.
Qed.

Remark transl_op_label:
  forall op args r k c,
  transl_op op args r k = OK c ->
  tail_nolabel k c.
Proof.
  unfold transl_op; intros. destruct op; TailNoLabel.
  destruct (Int.eq_dec i Int.zero); TailNoLabel.
  destruct (Float.eq_dec f Float.zero); TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; eauto. eapply mk_setcc_label.  
Qed.

Remark transl_load_label:
  forall chunk addr args dest k c,
  transl_load chunk addr args dest k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Remark transl_store_label:
  forall chunk addr args src k c,
  transl_store chunk addr args src k = OK c ->
  tail_nolabel k c.
Proof.
  intros. monadInv H. destruct chunk; TailNoLabel.
Qed.

Lemma transl_instr_label:
  forall f i (* ep *) k c,
  transl_instr f i (* ep *) k = OK c ->
  match i with Mach.Mlabel lbl => c = Plabel lbl :: k | _ => tail_nolabel k c end.
Proof.
Opaque loadind.
  unfold transl_instr; intros; destruct i; TailNoLabel.
  eapply loadind_label; now eauto.
  eapply storeind_label; now eauto.
  eapply loadind_label; now eauto.
(*  eapply tail_nolabel_trans; eapply loadind_label; eauto.  *)
  eapply transl_op_label; now eauto.
  eapply transl_load_label; now eauto.
  eapply transl_store_label; now eauto.
  destruct s0; now TailNoLabel.
  destruct s0; now TailNoLabel.
  eapply tail_nolabel_trans. eapply transl_cond_label; now eauto. now eapply mk_jcc_label.  
Qed.

Lemma transl_instr_label':
  forall lbl f i (* ep *) k c,
  transl_instr f i (* ep *) k = OK c ->
  find_label lbl c = if Mach.is_label lbl i then Some k else find_label lbl k.
Proof.
  intros. exploit transl_instr_label; eauto.
  destruct i; try (intros [A B]; apply B). 
  intros. subst c. simpl. auto.
Qed.

Lemma transl_code_label:
  forall lbl f c (* ep *) tc,
  transl_code f c (* ep *) = OK tc ->
  match Mach.find_label lbl c with
  | None => find_label lbl tc = None
  | Some c' => exists tc', find_label lbl tc = Some tc' /\ transl_code f c' (* false *) = OK tc'
  end.
Proof.
  induction c; simpl; intros.
  inv H. auto.
  monadInv H. rewrite (transl_instr_label' lbl _ _ _ _ EQ0).
  generalize (Mach.is_label_correct lbl a). 
  destruct (Mach.is_label lbl a); intros.
  subst a. simpl in EQ. exists x; auto.
  eapply IHc; eauto.
Qed.

Lemma transl_find_label:
  forall lbl f tf,
  transf_function f = OK tf ->
  match Mach.find_label lbl f.(Mach.fn_code) with
  | None => find_label lbl tf = None
  | Some c => exists tc, find_label lbl tf = Some tc /\ transl_code f c (* false *) = OK tc
  end.
Proof.
  intros. monadInv H. destruct (zlt (list_length_z x) Int.max_unsigned); inv EQ0.
  simpl. eapply transl_code_label; eauto. 
Qed.

End TRANSL_LABEL.

(** A valid branch in a piece of Mach code translates to a valid ``go to''
  transition in the generated PPC code. *)

Lemma find_label_goto_label:
  forall f tf lbl rs m c' b ofs,
  Genv.find_funct_ptr ge b = Some (Internal f) ->
  transf_function f = OK tf ->
  rs PC = Vptr b ofs ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  exists tc', exists rs',
    goto_label tf lbl rs m = Next rs' m  
  /\ transl_code_at_pc ge (rs' PC) b f c' (* false *) tf tc'
  /\ forall r, r <> PC -> rs'#r = rs#r.
Proof.
  intros. exploit (transl_find_label lbl f tf); eauto. rewrite H2. 
  intros [tc [A B]].
  exploit label_pos_code_tail; eauto. instantiate (1 := 0).
  intros [pos' [P [Q R]]].
  exists tc; exists (rs#PC <- (Vptr b (Int.repr pos'))).
  split. unfold goto_label. rewrite P. rewrite H1. auto.
  split. rewrite Pregmap.gss. constructor; auto. 
  rewrite Int.unsigned_repr. replace (pos' - 0) with pos' in Q.
  auto. omega.
  generalize (transf_function_no_overflow _ _ H0). omega.
  intros. apply Pregmap.gso; auto.
Qed.

(** Existence of return addresses *)

Lemma return_address_exists:
  forall f sg ros c, is_tail (Mach.Mcall sg ros :: c) f.(Mach.fn_code) ->
  exists ra, return_address_offset f c ra.
Proof.
  intros. eapply Asmgenproof0.return_address_exists; eauto. 
- intros. exploit transl_instr_label; eauto. 
  destruct i; try (intros [A B]; apply A). intros. subst c0. repeat constructor.
- intros. monadInv H0. 
  destruct (zlt (list_length_z x) Int.max_unsigned); inv EQ0.
  exists x; (* exists true; *) split; auto. unfold fn_code. repeat constructor.
- exact transf_function_no_overflow.
Qed.

(** * Proof of semantic preservation *)

(** Semantic preservation is proved using simulation diagrams
  of the following form.
<<
           st1 --------------- st2
            |                   |
           t|                  *|t
            |                   |
            v                   v
           st1'--------------- st2'
>>
  The invariant is the [match_states] predicate below, which includes:
- The PPC code pointed by the PC register is the translation of
  the current Mach code sequence.
- Mach register values and PPC register values agree.
*)

Section BOUND.

Variable bound: int.

Inductive match_states: Mach2.state -> Asm.state -> Prop :=
  | match_states_intro:
      forall s fb sp c (* ep *) ms m m' rs f tf tc
        (STACKS: match_stack ge s)
        (FIND: Genv.find_funct_ptr ge fb = Some (Internal f))
        (MEXT: Mem.extends m m')
        (AT: transl_code_at_pc ge (rs PC) fb f c (* ep *) tf tc)
        (AG: agree ms sp rs)
        (PERM: forall o k p, Mem.perm m' (Genv.genv_next ge) o k p -> 0 <= o < Int.unsigned bound)
        (VALID: Mem.valid_block m' (Genv.genv_next ge))
        (GENV_NEXT: Genv.genv_next tge = Genv.genv_next ge)
        (* DXP: ep = true -> rs#EDX = parent_sp s *),
      match_states (Mach2.State s fb sp c ms m)
                   (Asm.State rs m')
  | match_states_call:
      forall sp s fb ms m m' rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms sp rs)
        (ATPC: rs PC = Vptr fb Int.zero)
        (PERM: forall o k p, Mem.perm m' (Genv.genv_next ge) o k p -> 0 <= o < Int.unsigned bound)
        (VALID: Mem.valid_block m' (Genv.genv_next ge))
        (GENV_NEXT: Genv.genv_next tge = Genv.genv_next ge)
        (* ATLR: rs RA = parent_ra s *),
      match_states (Mach2.Callstate sp s fb ms m)
                   (Asm.State rs m')
  | match_states_return_internal:
      forall s ms m m' sp rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms sp rs)
        b z
        (ATPC: rs PC = Vptr b z)
        f (FIND: Genv.find_funct_ptr tge b = Some (Internal f))
        (AT: find_instr (Int.unsigned z) f = Some Pret)
        (PERM: forall o k p, Mem.perm m' (Genv.genv_next ge) o k p -> 0 <= o < Int.unsigned bound)
        (VALID: Mem.valid_block m' (Genv.genv_next ge))
        (GENV_NEXT: Genv.genv_next tge = Genv.genv_next ge),
      match_states (Mach2.Returnstate sp s ms m)
                   (Asm.State rs m')
  | match_states_return_external:
      forall s ms m m' sp rs
        (STACKS: match_stack ge s)
        (MEXT: Mem.extends m m')
        (AG: agree ms sp rs)
        b
        (ATPC: rs PC = Vptr b Int.one)
        f (FIND: Genv.find_funct_ptr tge b = Some (External f))
        (PERM: forall o k p, Mem.perm m' (Genv.genv_next ge) o k p -> 0 <= o < Int.unsigned bound)
        (VALID: Mem.valid_block m' (Genv.genv_next ge))
        (GENV_NEXT: Genv.genv_next tge = Genv.genv_next ge),
        match_states (Mach2.Returnstate sp s ms m)
                     (Asm.State rs m')        
.

Lemma exec_straight_steps:
  forall s fb f rs1 i c (* ep *) tf tc m1' m2 m2' sp ms2,
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) (* ep *) tf tc ->
  forall (PERM: forall o k p, Mem.perm m1' (Genv.genv_next ge) o k p -> 0 <= o < Int.unsigned bound)
        (VALID: Mem.valid_block m1' (Genv.genv_next ge))
        (GENV_NEXT: Genv.genv_next tge = Genv.genv_next ge),
  (forall k c (TR: transl_instr f i (* ep *) k = OK c),
   exists rs2,
       exec_straight tge tf c rs1 m1' k rs2 m2'
    /\ agree ms2 sp rs2
    (* /\ (edx_preserved ep i = true -> rs2#EDX = parent_sp s) *) )  ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach2.State s fb sp c ms2 m2) st'.
Proof.
  intros. inversion H2. subst. monadInv H7. 
  exploit H3; eauto. intros [rs2 [A [B C]]]. 
  exists (State rs2 m2'); split.
  eapply exec_straight_exec; eauto. 
  econstructor; eauto. eapply exec_straight_at; eauto.
  constructor; eauto.
  intros; eauto using exec_straight_perm.
  intros; eauto using exec_straight_valid.
Qed.

Lemma exec_straight_steps_goto:
  forall s fb f rs1 i c (* ep *) tf tc m1' m2 m2' sp ms2 lbl c',
  match_stack ge s ->
  Mem.extends m2 m2' ->
  Genv.find_funct_ptr ge fb = Some (Internal f) ->
  Mach.find_label lbl f.(Mach.fn_code) = Some c' ->
  transl_code_at_pc ge (rs1 PC) fb f (i :: c) (* ep *) tf tc ->
  True (* edx_preserved ep i = false *) ->
  forall (PERM: forall o k p, Mem.perm m1' (Genv.genv_next ge) o k p -> 0 <= o < Int.unsigned bound)
         (VALID: Mem.valid_block m1' (Genv.genv_next ge))         (GENV_NEXT: Genv.genv_next tge = Genv.genv_next ge),
  (forall k c (TR: transl_instr f i (* ep *) k = OK c),
   exists jmp, exists k', exists rs2,
       exec_straight tge tf c rs1 m1' (jmp :: k') rs2 m2'
    /\ agree ms2 sp rs2
    /\ exec_instr tge tf jmp rs2 m2' = goto_label tf lbl rs2 m2') ->
  exists st',
  plus step tge (State rs1 m1') E0 st' /\
  match_states (Mach2.State s fb sp c' ms2 m2) st'.
Proof.
  intros. inversion H3. subst. monadInv H9.
  exploit H5; eauto. intros [jmp [k' [rs2 [A [B C]]]]].
  generalize (functions_transl _ _ _ H7 H8); intro FN.
  generalize (transf_function_no_overflow _ _ H8); intro NOOV.
  exploit exec_straight_steps_2; eauto. 
  intros [ofs' [PC2 CT2]].
  exploit find_label_goto_label; eauto. 
  intros [tc' [rs3 [GOTO [AT' OTH]]]].
  exists (State rs3 m2'); split.
  eapply plus_right'.
  eapply exec_straight_steps_1; eauto. 
  econstructor; eauto.
  eapply find_instr_tail. eauto. 
  rewrite C. eexact GOTO.
  traceEq.
  econstructor; eauto.
  apply agree_exten with rs2; auto with asmgen.
  intros; eauto using exec_straight_perm.
  intros; eauto using exec_straight_valid.
(*  congruence. *)
Qed.

(** We need to show that, in the simulation diagram, we cannot
  take infinitely many Mach transitions that correspond to zero
  transitions on the PPC side.  Actually, all Mach transitions
  correspond to at least one Asm transition, except maybe (but actually not) the
  transition from [Mach.Returnstate] to [Mach.State].
  So, the following integer measure will suffice to rule out
  the unwanted behaviour. *)

Definition measure (s: Mach2.state) : nat :=
  match s with
  | Mach2.State _ _ _ _ _ _ => 0%nat
  | Mach2.Callstate _ _ _ _ _ => 0%nat
  | Mach2.Returnstate _ _ _ _ => 1%nat
  end.

(** This is the simulation diagram.  We prove it by case analysis on the Mach transition. *)

Section EXTEVENT_NEEDS.

Variable external_event_needs: event -> Z.

Theorem step_simulation:
  forall S1 t S2, Mach2.step external_event_needs return_address_offset ge S1 t S2 ->
  forall S1' (MS: match_states S1 S1'),
  (exists S2', plus step tge S1' (Prune.prune_trace t) S2' /\ match_states S2 S2')
  \/ (measure S2 < measure S1 /\ Prune.prune_trace t = E0 /\ match_states S2 S1')%nat.
Proof.
  induction 1; intros; inv MS.

- (* Mlabel *)
  left; eapply exec_straight_steps; eauto; intros. 
  monadInv TR. econstructor; split. apply exec_straight_one. simpl; eauto. auto. 
(*  split. *) apply agree_nextinstr; auto. (* simpl; congruence. *)

- (* Mgetstack *)
  unfold Mach.load_stack in H.
  exploit Mem.loadv_extends; eauto. intros [v' [A B]].
  rewrite (sp_val _ _ _ AG) in A.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR.
  exploit loadind_correct; eauto. intros [rs' [P [Q R]]].
  exists rs'; split. eauto.
  (* split. *) eapply agree_set_mreg; eauto. congruence.
(*  simpl; congruence. *)

- (* Msetstack *)
  unfold Mach.store_stack in H.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [A B]]. 
  left; eapply exec_straight_steps; eauto.
  rewrite (sp_val _ _ _ AG) in A. intros. simpl in TR.
  exploit storeind_correct; eauto. intros [rs' [P Q]].
  exists rs'; split. eauto.
  (* split. *) unfold Mach.undef_setstack. eapply agree_undef_move; eauto.
  (* simpl; intros. rewrite Q; auto with asmgen. *)

- (* Mgetparam *)
  assert (f0 = f) by congruence; subst f0.
  unfold Mach.load_stack in *. 
(*  exploit Mem.loadv_extends. eauto. eexact H0. auto. 
  intros [parent' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit lessdef_parent_sp; eauto. clear B; intros B; subst parent'. *)
  exploit Mem.loadv_extends. eauto. eexact H1. auto. 
  intros [v' [C D]].
Opaque loadind.
  left; eapply exec_straight_steps; eauto; intros. 
  (* assert (DIFF: negb (mreg_eq dst IT1) = true -> IR EDX <> preg_of dst).
    intros. change (IR EDX) with (preg_of IT1). red; intros. 
    unfold proj_sumbool in H1. destruct (mreg_eq dst IT1); try discriminate.
    elim n. eapply preg_of_injective; eauto.
  destruct ep; simpl in TR. *)
  exploit loadind_correct. eexact TR.
  instantiate (2 := rs0). 
  replace (rs0 ESP) with sp.
  etransitivity.
  2: eexact C.
  instantiate (1 := m').
  f_equal.
  rewrite Val.add_assoc. unfold Val.add at 3. reflexivity.
  inversion AG; congruence.
  intros [rs1 [P [Q R]]].
  exists rs1; split. eauto. 
  eapply agree_set_mreg; eauto. eapply agree_set_mreg. eassumption. eauto.  congruence. 
  simpl; intros. rewrite Q. auto.

- (* Mop *)
  assert (eval_operation tge sp op (List.map rs args) m = Some v). 
    rewrite <- H. apply eval_operation_preserved. exact symbols_preserved.
  exploit eval_operation_lessdef. eapply preg_vals; eauto. eauto. eexact H0.
  intros [v' [A B]]. rewrite (sp_val _ _ _ AG) in A. 
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_op_correct; eauto. intros [rs2 [P [Q R]]]. 
  assert (S: Val.lessdef v (rs2 (preg_of res))) by (eapply Val.lessdef_trans; eauto).
  exists rs2; split. eauto.
(*  split. *)
  unfold Mach.undef_op.
  destruct op; try (eapply agree_set_undef_mreg; eauto).
  eapply agree_set_undef_move_mreg; eauto. 
(*  simpl; congruence. *)

- (* Mload *)
  assert (eval_addressing tge sp addr (List.map rs args) = Some a). 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  exploit Mem.loadv_extends; eauto. intros [v' [C D]].
  left; eapply exec_straight_steps; eauto; intros. simpl in TR.
  exploit transl_load_correct; eauto. intros [rs2 [P [Q R]]]. 
  exists rs2; split. eauto.
  (* split. *) eapply agree_set_undef_mreg; eauto. congruence.
  (* simpl; congruence. *)

- (* Mstore *)
  assert (eval_addressing tge sp addr (List.map rs args) = Some a). 
    rewrite <- H. apply eval_addressing_preserved. exact symbols_preserved.
  exploit eval_addressing_lessdef. eapply preg_vals; eauto. eexact H1.
  intros [a' [A B]]. rewrite (sp_val _ _ _ AG) in A.
  assert (Val.lessdef (rs src) (rs0 (preg_of src))). eapply preg_val; eauto.
  exploit Mem.storev_extends; eauto. intros [m2' [C D]].
  left; eapply exec_straight_steps; eauto.
  intros. simpl in TR. 
  exploit transl_store_correct; eauto. intros [rs2 [P Q]]. 
  exists rs2; split. eauto.
  (* split. *) eapply agree_exten_temps; eauto. 
  (* simpl; congruence. *)

- (* Mcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  destruct ros as [rf|fid]; simpl in H; monadInv H6.
+ (* Indirect call *)
  assert (rs rf = Vptr f' Int.zero).
    destruct (rs rf); try discriminate.
    generalize (Int.eq_spec i Int.zero).
    destruct (Int.eq i Int.zero); try discriminate.
    revert H. case_eq (Genv.find_funct_ptr ge b); try discriminate.
    congruence.
   assert (rs0 x0 = Vptr f' Int.zero).
    exploit ireg_val; eauto. rewrite H6; intros LD; inv LD; auto. 
   generalize (code_tail_next_int _ _ _ _ NOOV H7). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c (* false *) tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. 
  intros; subst ra.
  exploit Mem.storev_extends; eauto.
  intros [m2' [STORE' EXT']].
  inversion AG; subst.
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  unfold exec_instr. rewrite <- H1.  unfold Vone. unfold Val.add. rewrite STORE'. eauto. 
  econstructor; eauto. 
  econstructor; eauto.
  (* eapply agree_sp_def; eauto. *)
  eapply agree_set_other.
  eapply agree_change_sp.
  eassumption.
  destruct agree_sp_def. destruct H9. rewrite H9. unfold Val.sub. eauto.
  reflexivity.
  revert STORE'. unfold Mem.storev. destruct (Val.sub (rs0 ESP) (Vint (Int.repr (size_chunk Mint32)))); try discriminate. intros; eauto using Mem.perm_store_2.
  revert STORE'. unfold Mem.storev. destruct (Val.sub (rs0 ESP) (Vint (Int.repr (size_chunk Mint32)))); try discriminate. intros; eauto using Mem.store_valid_block_1.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H7). intro CT1.
  assert (TCA: transl_code_at_pc ge (Vptr fb (Int.add ofs Int.one)) fb f c (* false *) tf x).
    econstructor; eauto.
  exploit return_address_offset_correct; eauto. intros; subst ra.
  exploit Mem.storev_extends; eauto.
  intros [m2' [STORE' EXT']].
  inversion AG; subst.  
  left; econstructor; split.
  apply plus_one. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  unfold exec_instr. unfold symbol_offset. rewrite symbols_preserved. rewrite H. rewrite <- H1. unfold Vone. unfold Val.add. rewrite STORE'. eauto.
  econstructor; eauto. 
  econstructor; eauto.
  eapply agree_set_other.
  eapply agree_change_sp.
  eassumption.
  destruct agree_sp_def. destruct H6. rewrite H6. unfold Val.sub. eauto.
  reflexivity.
  revert STORE'. unfold Mem.storev. destruct (Val.sub (rs0 ESP) (Vint (Int.repr (size_chunk Mint32)))); try discriminate. intros; eauto using Mem.perm_store_2.
  revert STORE'. unfold Mem.storev. destruct (Val.sub (rs0 ESP) (Vint (Int.repr (size_chunk Mint32)))); try discriminate. intros; eauto using Mem.store_valid_block_1.

- (* Mtailcall *)
  assert (f0 = f) by congruence.  subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *.
  destruct ros as [rf|fid]; simpl in H; monadInv H4. 
+ (* Indirect call *)
  assert (rs rf = Vptr f' Int.zero).
    destruct (rs rf); try discriminate.
    generalize (Int.eq_spec i Int.zero). destruct (Int.eq i Int.zero); try discriminate.
    destruct (Genv.find_funct_ptr ge b); try discriminate. congruence.
  assert (rs0 x0 = Vptr f' Int.zero).
    exploit ireg_val; eauto. rewrite H4; intros LD; inv LD; auto.
  generalize (code_tail_next_int _ _ _ _ NOOV H5). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail. eassumption.
  simpl. unfold nextinstr. rewrite Int.add_commut. rewrite Int.add_zero. rewrite Pregmap.gso. reflexivity.
  discriminate.
  eapply star_one. eapply exec_step_internal. rewrite Pregmap.gss. rewrite <- H1. unfold Vone. unfold Val.add. reflexivity.
  eapply functions_transl; eauto. eapply find_instr_tail. eassumption.
  simpl. 
  rewrite Pregmap.gso. rewrite Pregmap.gso. reflexivity.
  unfold ireg_of in EQ1. destruct rf; simpl in EQ1; congruence.
  unfold ireg_of in EQ1. destruct rf; simpl in EQ1; congruence.
  reflexivity. (* must remove Event_call/return events *)
  econstructor.
  assumption.
  assumption.
  eapply agree_set_other. eapply agree_set_other. eapply agree_change_sp. eassumption.
  inversion AG; subst. destruct agree_sp_def. destruct H7. rewrite H7. unfold Val.add. eauto.
  reflexivity.
  reflexivity.
  rewrite Pregmap.gss. assumption.
  assumption.
  assumption.
  assumption.
+ (* Direct call *)
  generalize (code_tail_next_int _ _ _ _ NOOV H5). intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl. unfold nextinstr. rewrite Pregmap.gso. reflexivity.
  discriminate.
  eapply star_one. eapply exec_step_internal. rewrite Pregmap.gss. rewrite <- H1. unfold Vone. unfold Val.add. reflexivity.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto.
  simpl. reflexivity.
  reflexivity. (* must remove Event_call/return events *)
  econstructor.
  assumption.
  assumption.
  eapply agree_set_other. eapply agree_set_other. rewrite Int.add_commut. rewrite Int.add_zero. eapply agree_change_sp. eassumption. inversion AG; subst. destruct agree_sp_def. destruct H4. rewrite H4. unfold Val.add. eauto.
  reflexivity.
  reflexivity.
  rewrite Pregmap.gss.
  unfold symbol_offset. rewrite symbols_preserved. rewrite H. reflexivity.
  assumption.
  assumption.
  assumption.

- (* Mbuiltin *)
  inv AT. monadInv H3. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H2); intro NOOV.
  exploit external_call_mem_extends; eauto. eapply preg_vals; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one. 
  eapply exec_step_builtin. eauto. eauto.
  eapply find_instr_tail; eauto.
  erewrite Prune.external_call_prune. eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  eassumption.
  econstructor; eauto.
  instantiate (2 := tf); instantiate (1 := x).
  unfold nextinstr_nf, nextinstr. rewrite Pregmap.gss.
  simpl undef_regs. repeat rewrite Pregmap.gso; auto with asmgen. 
  rewrite <- H0. simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto.
  apply agree_nextinstr_nf. eapply agree_set_undef_mreg; eauto. 
  rewrite Pregmap.gss. auto. 
  intros. Simplifs. 
  intros. eapply PERM. eapply external_call_max_perm. eassumption. assumption. eapply Mem.perm_max. eassumption.
  eauto using external_call_valid_block.

- (* Mannot *)
  inv AT. monadInv H4. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H3); intro NOOV.
  exploit annot_arguments_match; eauto. intros [vargs' [P Q]]. 
  exploit external_call_mem_extends; eauto.
  intros [vres' [m2' [A [B [C D]]]]].
  left. econstructor; split. apply plus_one. 
  eapply exec_step_annot. eauto. eauto.
  eapply find_instr_tail; eauto. eauto.
  erewrite Prune.external_call_prune.
  eapply external_call_symbols_preserved; eauto.
  exact symbols_preserved. exact varinfo_preserved.
  eassumption.
  eapply match_states_intro (* with (ep := false) *); eauto with coqlib.
  unfold nextinstr. rewrite Pregmap.gss. 
  rewrite <- H1; simpl. econstructor; eauto.
  eapply code_tail_next_int; eauto. 
  apply agree_nextinstr. auto.
  intros. eapply PERM. eapply external_call_max_perm. eassumption. assumption. eapply Mem.perm_max. eassumption.
  eauto using external_call_valid_block.

- (* Mgoto *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H4. 
  exploit find_label_goto_label; eauto. intros [tc' [rs' [GOTO [AT2 INV]]]].
  left; exists (State rs' m'); split.
  apply plus_one. econstructor; eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.
  simpl; eauto.
  econstructor; eauto.
  eapply agree_exten; eauto with asmgen.

- (* Mcond true *)
  assert (f0 = f) by congruence. subst f0.
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps_goto; eauto.
  intros. simpl in TR.
  destruct (transl_cond_correct tge tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]]. 
  rewrite EC in B.
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  exists (Pjcc c1 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten_temps; eauto. 
  simpl. rewrite B. auto.
(* jcc; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct b1.   
  (* first jcc jumps *)
  exists (Pjcc c1 lbl); exists (Pjcc c2 lbl :: k); exists rs'.
  split. eexact A.
  split. eapply agree_exten_temps; eauto. 
  simpl. rewrite TC1. auto.
  (* second jcc jumps *)
  exists (Pjcc c2 lbl); exists k; exists (nextinstr rs').
  split. eapply exec_straight_trans. eexact A. 
  eapply exec_straight_one. simpl. rewrite TC1. auto. auto.
  split. eapply agree_exten_temps; eauto.
  intros; Simplifs.
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2.
  destruct b2; auto || discriminate.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (andb_prop _ _ H3). subst. 
  exists (Pjcc2 c1 c2 lbl); exists k; exists rs'.
  split. eexact A.
  split. eapply agree_exten_temps; eauto. 
  simpl. rewrite TC1; rewrite TC2; auto.

- (* Mcond false *)
  exploit eval_condition_lessdef. eapply preg_vals; eauto. eauto. eauto. intros EC.
  left; eapply exec_straight_steps; eauto. intros. simpl in TR. 
  destruct (transl_cond_correct tge tf cond args _ _ rs0 m' TR)
  as [rs' [A [B C]]]. 
  rewrite EC in B.
  destruct (testcond_for_condition cond); simpl in *.
(* simple jcc *)
  econstructor; split.
  eapply exec_straight_trans. eexact A. 
  apply exec_straight_one. simpl. rewrite B. eauto. auto. 
  apply agree_nextinstr. eapply agree_exten_temps; eauto.
(* jcc ; jcc *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  destruct (orb_false_elim _ _ H1); subst.
  econstructor; split.
  eapply exec_straight_trans. eexact A. 
  eapply exec_straight_two. simpl. rewrite TC1. eauto. auto. 
  simpl. rewrite eval_testcond_nextinstr. rewrite TC2. eauto. auto. auto.
  apply agree_nextinstr. apply agree_nextinstr. eapply agree_exten_temps; eauto.
(* jcc2 *)
  destruct (eval_testcond c1 rs') as [b1|] eqn:TC1;
  destruct (eval_testcond c2 rs') as [b2|] eqn:TC2; inv B.
  exists (nextinstr rs'); split.
  eapply exec_straight_trans. eexact A. 
  apply exec_straight_one. simpl. 
  rewrite TC1; rewrite TC2. 
  destruct b1. simpl in *. subst b2. auto. auto.
  auto.
  apply agree_nextinstr. eapply agree_exten_temps; eauto.

- (* Mjumptable *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. monadInv H6. 
  exploit functions_transl; eauto. intro FN.
  generalize (transf_function_no_overflow _ _ H5); intro NOOV.
  exploit find_label_goto_label. eauto. eauto. instantiate (2 := rs0#ECX <- Vundef #EDX <- Vundef). 
  repeat (rewrite Pregmap.gso by auto with asmgen). eauto. eauto. 
  intros [tc' [rs' [A [B C]]]].
  exploit ireg_val; eauto. rewrite H. intros LD; inv LD.
  left; econstructor; split.
  apply plus_one. econstructor; eauto. 
  eapply find_instr_tail; eauto. 
  simpl. rewrite <- H9. unfold Mach.label in H0; unfold label; rewrite H0. eauto.
  econstructor; eauto. 
  eapply agree_exten_temps; eauto. intros. rewrite C; auto with asmgen. Simplifs. 

- (* Mreturn *)
  assert (f0 = f) by congruence. subst f0.
  inv AT. 
  assert (NOOV: list_length_z tf <= Int.max_unsigned).
    eapply transf_function_no_overflow; eauto.
  rewrite (sp_val _ _ _ AG) in *. 
  monadInv H3.
  exploit code_tail_next_int; eauto. intro CT1.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_internal. eauto.
  eapply functions_transl; eauto. eapply find_instr_tail; eauto. 
  simpl.  rewrite <- (sp_val _ _ _ AG). unfold nextinstr.  rewrite Pregmap.gso. rewrite Int.add_commut. rewrite Int.add_zero. rewrite <- H0. unfold Vone. unfold Val.add at 1. reflexivity.
  discriminate.
  eapply star_refl.
  reflexivity. (* return event to remove *)
  econstructor; eauto.
  apply agree_set_other; auto. rewrite <- (sp_val _ _ _ AG). eapply agree_change_sp; eauto. inversion AG; subst. destruct agree_sp_def. destruct H3. rewrite H3. unfold Val.add. eauto.
  rewrite Pregmap.gss. eauto.
  eapply functions_transl; eauto.
  eapply find_instr_tail; eauto.

- (* internal function *)
  exploit functions_translated; eauto. intros [tf [A B]]. monadInv B.
  generalize EQ; intros EQ'. monadInv EQ'. 
  destruct (zlt (list_length_z x0) Int.max_unsigned); inversion EQ1. clear EQ1.
  subst.
  left; econstructor; split.
   eapply plus_left.
   eapply exec_step_internal.
   eassumption.
   eassumption.
   simpl. rewrite zeq_true. reflexivity.
   simpl. unfold nextinstr. rewrite Pregmap.gso. rewrite ATPC. simpl. reflexivity.
   discriminate.
   eapply star_refl.
   reflexivity. (* call event to remove *)
  inversion AG; subst.
  destruct agree_sp_def. destruct H0. rewrite H0. simpl. rewrite Int.add_commut. rewrite Int.add_zero. rewrite (Int.add_commut Int.zero). rewrite Int.add_zero. replace (- Mach.fn_stacksize f) with (0 - Mach.fn_stacksize f) by omega. 

  rewrite sub_repr. rewrite Int.add_commut. rewrite <- Int.sub_add_l. rewrite Int.add_commut. rewrite Int.add_zero.
  econstructor. assumption. eassumption. assumption.
  econstructor. assumption. eassumption. eassumption.
  change (Int.unsigned Int.one) with (0 + 1).
  constructor. constructor.
  eapply agree_set_other. eapply agree_change_sp. eapply agree_exten_temps. eassumption. trivial. eauto. reflexivity.
  assumption.
  assumption.
  assumption.

- (* external function *)
  exploit functions_translated; eauto.
  intros [tf [A B]]. simpl in B. inv B.
  exploit extcall_arguments_match. 3: eassumption. eapply agree_change_sp. eassumption.
  inversion AG; subst. destruct agree_sp_def. destruct H1. rewrite H1. simpl. eauto.
  eassumption.
  intros [args' [C D]].
  exploit external_call_mem_extends; eauto.
  intros [res' [m2' [P [Q [R S]]]]].
  left; econstructor; split.
  apply plus_one. eapply exec_step_external; eauto. 
  erewrite Prune.external_call_prune.
  eapply external_call_symbols_preserved; eauto. 
  exact symbols_preserved. exact varinfo_preserved.
  eassumption.
  inversion AG; subst. assumption.
  eapply match_states_return_external; eauto.
  unfold loc_external_result.
  eapply agree_set_mreg; eauto. 
  rewrite Pregmap.gso; auto with asmgen. rewrite Pregmap.gss. auto. 
  intros; Simplifs.
  rewrite Pregmap.gss. reflexivity.
  intros. eapply PERM. eapply external_call_max_perm. eassumption. assumption. eapply Mem.perm_max. eassumption.
  eauto using external_call_valid_block.

- (* return internal *)
  inv STACKS.
  replace f1 with fd in * by congruence.
  exploit Mem.loadv_extends; eauto.
  intros [v2 [HV2' HV2_]].
  inv HV2_.
  inversion AG; subst.
  left; econstructor; split.
  eapply plus_left. econstructor. eassumption. eassumption. eassumption.
  simpl. rewrite HV2'. reflexivity.
  eapply star_refl.
  reflexivity.
  econstructor. assumption. eassumption. assumption. rewrite Pregmap.gss. eassumption.
  eapply agree_set_other. eapply agree_change_sp. eassumption. destruct agree_sp_def. destruct H. rewrite H. simpl. eauto.
  reflexivity.
  assumption.
  assumption.
  assumption.

- (* return external *)
  inv STACKS.
  replace f1 with fd in * by congruence.
  exploit Mem.loadv_extends; eauto.
  intros [v2 [HV2' HV2_]].
  inv HV2_.
  inversion AG; subst.
  left; econstructor; split.
  eapply plus_left. eapply exec_step_external_return. eassumption. eassumption. instantiate (3 := nil). simpl.  rewrite HV2'. reflexivity.
  eapply star_refl.
  reflexivity.
  econstructor. assumption. eassumption. assumption. rewrite Pregmap.gss. eassumption.
  eapply agree_set_other. eapply agree_change_sp. eassumption. destruct agree_sp_def. destruct H. rewrite H. simpl. eauto.
  reflexivity.
  assumption.
  assumption.
  assumption.

Qed.

Lemma transf_initial_states:
  forall st1, Mach2.initial_state bound prog st1 ->
  exists st2, Asm.initial_state bound tprog st2 /\ match_states st1 st2.
Proof.
  intros. inversion H. unfold ge0 in *.
  econstructor; split.
  econstructor.
  eapply Genv.init_mem_transf_partial; eauto.
  eassumption.  
  replace (symbol_offset (Genv.globalenv tprog) (prog_main tprog) Int.zero)
     with (Vptr fb Int.zero).
  econstructor; eauto.
  constructor.
  apply Mem.extends_refl.
  constructor.
  rewrite Pregmap.gss. reflexivity.
  eauto.
  intro. rewrite Mach.Regmap.gi. constructor.
  unfold ge. erewrite Genv.init_mem_genv_next.  2: eassumption. erewrite <- Mem.alloc_result.  2: eassumption. intros. eapply Mem.perm_alloc_3. eassumption.  eassumption.
  unfold ge. erewrite Genv.init_mem_genv_next. 2: eassumption. erewrite <- Mem.alloc_result. 2: eassumption. eapply Mem.valid_new_block. eassumption.
  exploit Genv.init_mem_transf_partial; eauto.
  intros.
  unfold ge, tge.
  erewrite Genv.init_mem_genv_next; eauto.
  erewrite Genv.init_mem_genv_next; eauto.
  unfold symbol_offset. 
  rewrite (transform_partial_program_main _ _ TRANSF).
  rewrite symbols_preserved. 
  unfold ge; rewrite H2. auto.
Qed.

Lemma transf_final_states:
  forall st1 st2 r, 
  match_states st1 st2 -> Mach2.final_state bound prog st1 r -> Asm.final_state bound tprog st2 r.
Proof.
  intros. inv H0. inv H; inv STACKS. 
   (* internal *)
   econstructor.
   eassumption.
   eassumption.
   assumption.
   unfold loc_result in H1. simpl in H1. generalize (agree_mregs _ _ _ AG AX). rewrite H1. inversion 1; subst; eauto.
   inversion AG; subst; unfold tge, ge in *; rewrite GENV_NEXT; assumption.
   inversion AG; subst. rewrite agree_sp. simpl. case_eq (Mem.load Mint32 m' (Genv.genv_next (Genv.globalenv prog)) (Int.unsigned bound)); auto.
   intros. exfalso. exploit Mem.load_valid_access. eassumption. destruct 1.
   refine (_ (H0 (Int.unsigned bound) _)).
   intro.
   eapply PERM in x. omega.
   simpl; omega.
   (* external *)
   eapply final_state_external.
   eassumption.
   eassumption.
   unfold loc_result in H1. simpl in H1. generalize (agree_mregs _ _ _ AG AX). rewrite H1. inversion 1; subst; eauto.
   inversion AG; subst; unfold tge, ge in *; rewrite GENV_NEXT; assumption.
   inversion AG; subst. rewrite agree_sp. simpl. case_eq (Mem.load Mint32 m' (Genv.genv_next (Genv.globalenv prog)) (Int.unsigned bound)); auto.
   intros. exfalso. exploit Mem.load_valid_access. eassumption. destruct 1.
   refine (_ (H0 (Int.unsigned bound) _)).
   intro.
   eapply PERM in x. omega.
   simpl; omega.
Qed.   

Theorem transf_program_correct: 
  forward_simulation (Prune.prune_semantics (Mach2.semantics external_event_needs return_address_offset bound prog)) (Asm.semantics bound tprog).
Proof.
  eapply forward_simulation_star with (measure := measure).
  eexact symbols_preserved.
  eexact transf_initial_states.
  eexact transf_final_states.
  intros. 
  destruct H.
  subst.
  eauto using step_simulation.
Qed.

End EXTEVENT_NEEDS.

End BOUND.

End PRESERVATION.
