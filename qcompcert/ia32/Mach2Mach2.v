(* *********************************************************************)
(*                                                                     *)
(*             The Quantitative CompCert verified compiler             *)
(*                                                                     *)
(*                 Tahina Ramananandro, Yale University                *)
(*                                                                     *)
(*  See LICENSE for details on distributing this file.                 *)
(*                                                                     *)
(* *********************************************************************)

(** The correctness proof of the reinterpretation of [Mach] into [Mach2].

    As explained in Section 3.2 of our PLDI 2014 paper, [Mach2] and
    [Mach] have the same abstract syntax. [Mach2] is just a
    reinterpretation of [Mach] with a finite stack space. Stack frames
    of all function calls are merged together into a single
    whole-program stack block. This file explains how.

*)


Require Import Memory.
Require Import Values.
Require Import Coqlib.
Require Import Globalenvs.
Require Import AST.
Require Import Integers.
Require Import Smallstep.
Require Import Events.
Require Import Maps.
Require Import Registers.
Require Import Op.
Require Import Mach.
Require Import Stacklayout.
Require Import Stackbounds.
Require Mach2.

Lemma disjoint_intervals_1:
  forall P d,
    d > 0 ->
    forall d',
      d' > 0 ->
      forall a,
        (forall x, a <= x < a + d -> P x) ->
        forall a',
          (forall x, a' <= x < a' + d' -> P x -> False) ->
          (a + d <= a' \/ a' + d' <= a).
Proof.
  intros.
  destruct (zle (a+d) a'); auto.
  destruct (zle (a'+d') a); auto.
  exfalso.
  destruct (zle a a').
   eapply H1.
   instantiate (1 := a'). omega.
   eapply X. omega.
  eapply H1.
  instantiate (1 := a). omega.
  eapply X. omega.
Qed.

Lemma disjoint_intervals_2:
  forall P d,
    d > 0 ->
    forall d',
      d' > 0 ->
      forall a,
        (forall x, a <= x < a + d -> P x -> False) ->
        forall a',
          (forall x, a' <= x < a' + d' -> P x) ->
          (a + d <= a' \/ a' + d' <= a).
Proof.
  intros. 
  cut (a' + d' <= a \/ a + d <= a').
   tauto.
  eauto using disjoint_intervals_1.
Qed.

Lemma strong_align_chunk: forall chunk,
  (align_chunk chunk | strong_align).
Proof.
  intro. exists (strong_align / align_chunk chunk).
  unfold strong_align. simpl. destruct chunk; destruct (is_strong_align tt); reflexivity.
Qed.

Section WITHRAO.

Variable RAO: function -> code -> int -> Prop.
Hypothesis RAO_EX: (* comes from ASM *)
  forall f sg ros c, is_tail (Mcall sg ros :: c) f.(Mach.fn_code) ->
                     exists ra, RAO f c ra.

Section BOUND.

(** [bound] is the total size of the stack space available to the program. We assume that it is a machine-representable integer, and that the stack is strongly aligned. *)

Variable bound: int.
Hypothesis bound_align: (strong_align | Int.unsigned bound + size_chunk Mint32).
Variable external_event_needs: event -> Z.

Section GE.

Variable stacksizes: PMap.t Z.

Variable ge: genv.

Hypothesis ge_align:
  forall fb phi, Genv.find_funct_ptr ge fb = Some (Internal phi) ->
                 (strong_align | phi.(fn_stacksize) + size_chunk Mint32).

Hypothesis ge_stacksizes:
  forall fb phi, Genv.find_funct_ptr ge fb = Some (Internal phi) ->
                 PMap.get phi.(fn_id) stacksizes = phi.(fn_stacksize) + size_chunk Mint32.

Hypothesis ge_stacksizes_pos:
  forall fb phi, Genv.find_funct_ptr ge fb = Some (Internal phi) ->
                 0 <= phi.(fn_stacksize).

Section STACKBLOCK.

Variable stackblock: block.
Hypothesis stackblock_no_var: Genv.find_var_info ge stackblock = None.

Section INJ.

Variables (inj: meminj)  (m m': mem) .

(** The following invariant explains how the stack frames of the
    callers are merged into one single stack block.

    This invariant heavily relies on the abstract "control stack" of
    [Mach], which has no counterpart in [Asm]. So, it is unclear how
    this proof can be redone by reinterpreting [Asm] instead of
    [Mach].

    [ofs] is the offset of the stack pointer excluding the return
    address of the caller.
    
    This invariant is x86-specific. It assumes that the bottom of the
    stack -- excluding the return address of the "caller" of [main] --
    is at offset [bound] and the top is at offset 0.  *)

Inductive match_stacks: forall (ofs: Z) (ms: list Mach.stackframe) (m2s: list Mach2.stackframe), Prop :=
| match_stacks_nil
    ofs
    (HEQ: ofs = Int.unsigned bound)
  :match_stacks ofs nil nil
| match_stacks_cons
    fb
    (INJ_FUN: inj fb = Some (fb, 0))
    phi
    (FUN: Genv.find_funct_ptr ge fb = Some (Internal phi))
    (SIZE_POS: 0 <= phi.(fn_stacksize))
    (SIZE_ALIGN: (strong_align | phi.(fn_stacksize) + size_chunk Mint32))
    ofs
    (OFS_POS: 0 <= ofs)
    ofs_pre
    (HEQ: ofs = ofs_pre - (phi.(fn_stacksize) + (size_chunk Mint32)))
    sp
    (INJ_SP: inj sp = Some (stackblock, ofs + (size_chunk Mint32)))
    ra
    (MEM_RA: Mem.load Mint32 m' stackblock ofs = Some (Vptr fb ra))
    (MEM_RA_ACC: Mem.valid_access m' Mint32  stackblock ofs Freeable)    
    c
    (HRA: RAO phi c ra)
    (CTAIL: is_tail c (phi.(fn_code)))
    (MEM_NO_PERMS: forall b o', inj b = Some (stackblock, o') ->
                                forall ofs', ofs <= (ofs'+o') < ofs + (size_chunk Mint32) ->
                                             forall k p, ~ Mem.perm m b ofs' k p)
    (SRC_MEM_NO_PERMS: forall o k p, Mem.perm m sp o k p -> 0 <= o < phi.(fn_stacksize))
    l l'
    (HIND: match_stacks ofs_pre l l')
  :  match_stacks ofs (Mach.Stackframe fb sp c :: l) (Mach2.Stackframe fb ra c :: l').

Lemma match_stacks_bound: forall ofs ms m2s, 
                            match_stacks ofs ms m2s ->
                            0 <= ofs <= Int.unsigned bound.
Proof.
  induction 1; subst.
  generalize (Int.unsigned_range bound). omega.
  simpl in *; omega.
Qed.

Lemma match_stacks_align: forall ofs ms m2s, 
                            match_stacks ofs ms m2s ->
                            (strong_align | ofs + (size_chunk Mint32)).
Proof.
  induction 1; subst.
   assumption.
   replace (ofs_pre - (fn_stacksize phi + (size_chunk Mint32)) + (size_chunk Mint32)) with (ofs_pre + (size_chunk Mint32) - (fn_stacksize phi + (size_chunk Mint32))) by omega.
   apply Z.divide_sub_r. assumption. assumption.
Qed.

End INJ.

Lemma eqm_modulus: forall a, Int.eqm (a + Int.modulus) a.
Proof.
  intros. pattern a at 2. replace a with (a + 0) by omega. apply Int.eqm_add. apply Int.eqm_refl. exists (1). omega.
Qed.

Lemma match_stacks_store_inside:
  forall  m m' inj (HINJ: Mem.inject inj m m') chunk vloc valu m_,
      Mem.storev chunk m vloc valu = Some m_ ->
      forall v2loc,
        val_inject inj vloc v2loc ->
        forall v2alu,
          val_inject inj valu v2alu ->
           forall m' m'_,
            Mem.storev chunk m' v2loc v2alu = Some m'_ ->
          forall ofs ms m2s,
            match_stacks inj m m' ofs ms m2s ->
            match_stacks inj m_ m'_ ofs ms m2s.
Proof.
  assert (H: True) by auto.
  induction 6.
   constructor; auto.
  unfold Mem.storev in *.
  destruct v2loc; try discriminate.
  destruct vloc; try discriminate.
  inversion H1; subst.
  econstructor; eauto.
  erewrite Mem.load_store_other.
  eassumption.
  eassumption.
  destruct (zeq stackblock b); auto.
  subst b. right.
  destruct (Mem.store_valid_access_3 _ _ _ _ _ _ H0).
  revert H3.
  erewrite Mem.address_inject.
  intro.
  eapply disjoint_intervals_2 with (P := fun x => Mem.perm m b0 (x - delta) Cur Writable).
  apply size_chunk_pos.
  apply size_chunk_pos.
  simpl. intros. 
  eapply MEM_NO_PERMS in H9.
  assumption.
  eassumption.
  simpl in *; omega.
  intros.
  eapply H5.
  omega.
  eassumption.
  eapply H5.
  generalize (size_chunk_pos chunk). omega.
  eassumption.
(* valid access *)
eapply Mem.store_valid_access_1.
eassumption.
assumption.
(* perm *)
intros.
intro.
eapply MEM_NO_PERMS.
eassumption.
eassumption.
eapply Mem.perm_store_2.
eassumption.
eassumption.
(* no perm outside *)
intros; eauto using Mem.perm_store_2.
Qed.

Lemma match_stacks_store_outside:
  forall inj m m',
    Mem.inject inj m m' ->
    forall chunk b o valu m'2,
      Mem.store chunk m' b o valu = Some m'2 ->
     forall ofs ms m2s,
      match_stacks inj m m' ofs ms m2s ->      
      (b <> stackblock \/ o + size_chunk chunk <= ofs \/ Int.unsigned bound <= o) ->
      match_stacks inj m m'2 ofs ms m2s.
Proof.
  induction 3.
   constructor. assumption.
  econstructor; eauto.
   erewrite Mem.load_store_other.
   eassumption.
   eassumption.
   exploit match_stacks_bound; eauto.
   generalize (size_chunk_pos chunk).
   simpl.
   intros. 
   unfold block in *.
   simpl in *; omega.
(* valid access *)
eapply Mem.store_valid_access_1.
eassumption.
assumption.
(* IH *)
  eapply IHmatch_stacks.
   exploit match_stacks_bound; eauto.
   generalize (size_chunk_pos chunk).
   unfold block in *.
   simpl in *; omega.
Qed.

Lemma match_stacks_external:
  forall inj m1 m1'
         (INJ: Mem.inject inj m1 m1')
         inj' m2 m2'
         (OUT_OF_REACH: mem_unchanged_on (loc_out_of_reach inj m1) m1' m2')
         (INCR: inject_incr inj inj')
         (SEP: inject_separated inj inj' m1 m1')
         (PERM: forall b, Mem.valid_block m1 b -> forall ofs p, Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p)
         ofs ms m2s,
        match_stacks inj m1 m1' ofs ms m2s ->      
        match_stacks inj' m2 m2' ofs ms m2s.
Proof.
  induction 6.
   constructor; assumption.
  econstructor; eauto.
  destruct OUT_OF_REACH as [_ OUT_OF_REACH].
  eapply OUT_OF_REACH; auto.
  unfold loc_out_of_reach.
  intros i Hi. intros.
  eapply MEM_NO_PERMS.
  eassumption.
  simpl in Hi.
  simpl in *; omega.
 destruct OUT_OF_REACH as [OUT_OF_REACH _].
 destruct MEM_RA_ACC as [MEM_RA_ACC_PERM MEM_RA_ACC_ALIGN].
 split; auto.
 intro. intros.
 eapply OUT_OF_REACH.
  unfold loc_out_of_reach.
  intros.
  eapply MEM_NO_PERMS.
  eassumption.
  simpl in H0. simpl in *; omega.
  eapply MEM_RA_ACC_PERM. assumption.
 intros b o' Hb.
 case_eq (inj b).
  intros [s' o''] Hs'.
  generalize (INCR _ _ _ Hs').
  intro Hs''.
  rewrite Hb in Hs''.
  injection Hs''; clear Hs''; intros; subst.
  intro ABSURD.
  apply Mem.perm_max in ABSURD.  
  eapply PERM in ABSURD.
  eapply MEM_NO_PERMS.
  eexact Hs'.
  eassumption.
  eassumption.
  eapply Mem.valid_block_inject_1. eexact Hs'. eassumption.
 intro.
 exploit SEP; eauto.
 intros [_ INVAL].
 edestruct INVAL.
 eapply Mem.valid_access_valid_block.
 eapply Mem.valid_access_implies.
 eapply Mem.load_valid_access; eauto.
 constructor.
intros.
eauto using Mem.valid_block_inject_1, Mem.perm_max.
Qed.

Lemma match_stacks_free_left:
  forall inj m m' ofs ms m2s,
    match_stacks inj m m' ofs ms m2s ->
    forall m_,
      (forall b o k p, Mem.perm m_ b o k p -> Mem.perm m b o k p) ->
      match_stacks inj m_ m' ofs ms m2s.
Proof.
  induction 1; subst.
   constructor. reflexivity.
  econstructor; eauto.
  intros. intro. eapply MEM_NO_PERMS; eauto.
Qed.

Lemma match_stacks_alloc_left:
  forall inj inj'
         (INCR: inject_incr inj inj')
         m1 m2
         (INJ_VALID: forall b p, inj b = Some p -> Mem.valid_block m1 b)
         (PERM: forall b, Mem.valid_block m1 b -> forall ofs p, Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p)
         m' ofs ms m2s,
        match_stacks inj m1 m' ofs ms m2s -> 
        forall (INJ_NEW: forall b, inj b = None -> forall delta, inj' b = Some (stackblock, delta) -> forall o k p, Mem.perm m2 b o k p -> 0 <= o + delta < ofs),
        match_stacks inj' m2 m' ofs ms m2s.
Proof.
  induction 4.
   constructor; assumption.
  econstructor; eauto.
  intros. case_eq (inj b).
   destruct p0. intro. generalize (INCR _ _ _ H2). rewrite H0. injection 1; intros. subst b0 z. intro. apply Mem.perm_max in H4. eapply MEM_NO_PERMS. eassumption. eassumption. eapply PERM. eapply INJ_VALID. eassumption. eassumption.
  intros. intro. exploit INJ_NEW. eassumption. eassumption. eassumption. generalize (size_chunk_pos Mint32). omega.
  intros. apply Mem.perm_max in H0. eapply SRC_MEM_NO_PERMS. eapply PERM. eapply INJ_VALID. eassumption. eassumption.
  eapply IHmatch_stacks; eauto.
  intros. exploit INJ_NEW; eauto.
  generalize (size_chunk_pos Mint32).
 omega.
Qed.

Section IOFS.

Variables (ofs_bound (* actual free stack size *)
           ofs_inj (* address of stack pointer *)
           ofs_stack (* address of caller stack frame *) : Z)
          (m m': mem) (stk: list Mach.stackframe) (stk': list Mach2.stackframe) (rs r2s: regset)  (inj: meminj).

(** This invariant explains how to merge the current (callee) stack
    frame into the single stack block.

    It is x86-specific. *)

Inductive match_states' : forall (ms: Mach.state) (m2s: Mach2.state), Prop :=
| match_states_state
    fb
    (INJ_FUN: inj fb = Some (fb, 0))
    phi
    (FUN: Genv.find_funct_ptr ge fb = Some (Internal phi))
    (HOFS_INJ: ofs_inj = ofs_bound + (size_chunk Mint32))
    (HOFS_RA: Mem.valid_access m' Mint32  stackblock ofs_bound Freeable)
    (HSTACK: ofs_stack = ofs_inj + phi.(fn_stacksize))
    (HSTACK_POS: 0 <= phi.(fn_stacksize))
    (HSTACK_ALIGN: (strong_align | phi.(fn_stacksize) + (size_chunk Mint32)))
    sp    
    (INJ_SP: inj sp = Some (stackblock, ofs_inj))
    iofs'
    (HOFS': iofs' = Int.repr ofs_inj)
    c
    (CTAIL: is_tail c (phi.(fn_code)))
    (SRC_MEM_NO_PERMS: forall o k p, Mem.perm m sp o k p -> 0 <= o < phi.(fn_stacksize))
    :
      match_states'
        (Mach.State stk fb sp c rs m)
        (Mach2.State stk' fb (Vptr stackblock iofs') c r2s m')

| match_states_callstate
    (INJ_STACK_INJ: ofs_inj = ofs_stack)
    (INJ_BOUND_INJ: ofs_bound = ofs_stack)
    iofs'
    (HOFS': iofs' = Int.repr ofs_inj)
    fb
    (INJ_FUN: inj fb = Some (fb, 0))    
  : match_states'
      (Mach.Callstate stk fb rs m)
      (Mach2.Callstate (Vptr stackblock iofs') stk' fb r2s m')

| match_states_returnstate
    (INJ_STACK_INJ: ofs_inj = ofs_stack)
    (INJ_BOUND_INJ: ofs_bound = ofs_stack)
    iofs'
    (HOFS': iofs' = Int.repr ofs_inj)
  : match_states'
      (Mach.Returnstate stk rs m)
      (Mach2.Returnstate (Vptr stackblock iofs') stk' r2s m')
.

Lemma match_states'_bound:
  forall ms m2s,
    match_states' ms m2s ->
    ofs_bound <= ofs_inj <= ofs_stack.
Proof.
  inversion 1; simpl in *; omega.
Qed.

End IOFS.

Inductive match_states_ (ofs_bound: Z) (ms: Mach.state) (m2s: Mach2.state): Prop :=
  match_states_intro
    ofs_bound_
    ofs_inj ofs_stack m m'
    stk stk' 
    rs r2s inj
    (HMATCH: match_states' ofs_bound_ ofs_inj ofs_stack m m' stk stk' rs r2s inj ms m2s)
    (INJ_REG: forall r, val_inject inj (Regmap.get r rs) (Regmap.get r r2s))
    (INJ_MEM: Mem.inject inj m m')
    (STACK: match_stacks inj m m' ofs_stack stk stk')
    (HBOUND_POS: 0 <= ofs_bound_)
    (MEM_NO_PERMS: forall b o', inj b = Some (stackblock, o') ->
                                forall ofs', 0 <= (ofs'+o') < ofs_inj ->
                                             forall k p, ~ Mem.perm m b ofs' k p)
    (TGT_MEM_PERMS: forall ofs', 0 <= ofs' < ofs_inj -> Mem.perm m' stackblock ofs' Cur Freeable)
    (TGT_MEM_PERMS_BOUND: forall ofs' k p, Mem.perm m' stackblock ofs' k p -> 0 <= ofs' < Int.unsigned bound)
    (INJ_GLOBALS: meminj_preserves_globals ge inj)
    (INJ_FUNS: forall id b, Genv.find_funct_ptr ge b = Some id -> inj b = Some (b, 0))
    (STACK_VALID: Mem.valid_block m' stackblock) (* necessary for calling an external function *)
    (OFS_BOUND_: ofs_bound_ = ofs_bound)
.

Lemma meminj_preserves_symbols: forall inj
    (INJ_GLOBALS: meminj_preserves_globals ge inj)
                             ,
    ((*INJ_SYMB: *) forall id b, Genv.find_symbol ge id = Some b -> inj b = Some (b, 0)).
Proof.
  destruct 1. assumption.
Qed.

Lemma regset_inject_list: forall rs r2s inj,
   (forall r : RegEq.t, val_inject inj (Regmap.get r rs) (Regmap.get r r2s)) ->
   forall args,  val_list_inject inj rs ## args r2s ## args.
Proof.
  induction args; simpl; constructor; eauto.
Qed.

Lemma symbol_address_inject:
  forall inj,
  (forall (id : ident) (b : block),
             Genv.find_symbol ge id = Some b -> inj b = Some (b, 0)) ->
   forall (id : ident) (ofs : int),
   val_inject inj (symbol_address ge id ofs) (symbol_address ge id ofs).
Proof.
  intros. unfold symbol_address.
  case_eq (Genv.find_symbol ge id); auto.
  intros. econstructor. eauto. rewrite Int.add_zero. reflexivity.
Qed.

Lemma undef_temps_inject: forall rs r2s inj r,
                            val_inject inj (Regmap.get r rs) (Regmap.get r r2s) ->
                            val_inject inj (undef_temps rs r) (undef_temps r2s r).
Proof.
 unfold undef_temps. 
 intros.
 destruct (In_dec RegEq.eq r Conventions1.temporary_regs).
  rewrite undef_regs_same; auto.
 repeat rewrite undef_regs_other; eauto.
Qed.

Lemma undef_move_inject: forall rs r2s inj r,
                            val_inject inj (Regmap.get r rs) (Regmap.get r r2s) ->
                            val_inject inj (undef_move rs r) (undef_move r2s r).
Proof.
 unfold undef_move.
 intros.
 destruct (In_dec RegEq.eq r Conventions1.destroyed_at_move_regs).
  rewrite undef_regs_same; auto.
 repeat rewrite undef_regs_other; eauto.
Qed.

Lemma undef_op_inject: forall rs r2s inj r,
                            val_inject inj (Regmap.get r rs) (Regmap.get r r2s) ->
                            forall op,
                            val_inject inj (undef_op op rs r) (undef_op op r2s r).
Proof.
  destruct op; simpl; eauto using undef_move_inject, undef_temps_inject.
Qed.


Lemma find_function_ptr_inject: forall rs r2s inj
                                    (INJ_REG : forall r : RegEq.t,
                                                 val_inject inj (Regmap.get r rs) (Regmap.get r r2s))
                                    (INJ_FUNS : forall (id : fundef) (b : block),
             Genv.find_funct_ptr ge b = Some id -> inj b = Some (b, 0))
                                    ros f',
find_function_ptr ge ros rs = Some f' ->
find_function_ptr ge ros r2s = Some f' .
Proof.
  destruct ros; simpl; auto.
  intro. 
  case_eq (rs m); try discriminate.
  intros until 1.
  case_eq (Int.eq i Int.zero); try discriminate.
  intros until 1.
  case_eq (Genv.find_funct_ptr ge b); try discriminate.
  injection 2; intro; subst.
  generalize (INJ_REG m).
  unfold Regmap.get. rewrite H. inversion 1; subst.
  erewrite INJ_FUNS in H7. 2: eassumption. inv H7.
  rewrite Int.add_zero. rewrite H0. rewrite H1. reflexivity.
Qed.

Lemma find_function_ptr_inj: forall inj
                                    (INJ_SYMB : forall (id : ident) (b : block),
             Genv.find_symbol ge id = Some b -> inj b = Some (b, 0))
                                    (INJ_FUNS : forall (id : fundef) (b : block),
                                                  Genv.find_funct_ptr ge b = Some id -> inj b = Some (b, 0))
                                    ros rs f',
                               find_function_ptr ge ros rs = Some f' ->
                               inj f' = Some (f', 0).
Proof.
  unfold find_function_ptr. intros until f'.
  destruct ros; eauto.
  case_eq (rs m); try discriminate.
  intros until 1.
  case_eq (Int.eq i Int.zero); try discriminate.
  intros until 1.
  case_eq (Genv.find_funct_ptr ge b); try discriminate.
  injection 2; intros; subst; eauto.
Qed.

Lemma annot_arguments_inject: forall inj rs r2s
(INJ_REG : forall r : RegEq.t,
            val_inject inj (Regmap.get r rs) (Regmap.get r r2s))
sp sp' delta (HINJ: inj sp = Some (sp', delta))
(HDELTA_REPR: 0 <= delta <= Int.max_unsigned)
m m'
(INJ_MEM : Mem.inject inj m m')
args vargs
(HARGS: annot_arguments rs m (Vptr sp Int.zero) args vargs)
,
exists vargs',
annot_arguments r2s m' (Vptr sp' (Int.repr delta)) args vargs' /\
val_list_inject inj vargs vargs'.
Proof.
  induction args; inversion 1; subst.
   esplit; split; econstructor.
  destruct (IHargs _ H3) as [? [? ?]].
  inversion H1; subst.
   esplit. split. econstructor. econstructor.  eassumption. constructor; auto. apply INJ_REG.
  change (Int.unsigned Int.zero) with 0 in H9.
  simpl in *.
  exploit Mem.load_inject; eauto.
  intros [? [? ?]].
  esplit. split. econstructor. econstructor.
  rewrite Int.unsigned_repr; auto.
  replace (delta + ofs) with (ofs + delta) by omega.
  eassumption.
  eassumption.
 constructor; auto.
Qed.

Lemma extcall_arguments_inject: forall inj
                                       sp sp' delta (HINJ: inj sp = Some (sp', delta))
                                       m m'
                                       (INJ_MEM : Mem.inject inj m m')
                                       rs sg args
                                       (HARGS: extcall_arguments rs m (Vptr sp Int.zero) sg args) r2s,
exists args',
  extcall_arguments r2s m' (Vptr sp' (Int.repr delta)) sg args' /\
  val_list_inject inj args args'.
Proof.
  intros until args. unfold extcall_arguments. unfold Conventions1.loc_arguments. generalize (sig_args sg). clear sg. intro. generalize 0. revert args. induction l; simpl.
  inversion 2; subst. esplit. split. econstructor. constructor.
  destruct a; inversion 1; subst.
  inversion H1; subst. Opaque Zmult. unfold load_stack in H7. simpl load_stack in H7. simpl Val.add in H7. simpl chunk_of_type in H7. rewrite Int.add_commut in H7. rewrite (Int.add_zero) in H7.
  exploit Mem.loadv_inject; eauto.
  intros.
  destruct (IHl _ _ H3 r2s). destruct H.
  destruct H. destruct H0.
  esplit. split. econstructor. econstructor. unfold load_stack. simpl Val.add. rewrite Int.add_commut.  eassumption.
  eassumption.
  constructor; eauto.
 inversion H1; subst. Opaque Zmult. unfold load_stack in H7. simpl load_stack in H7. simpl Val.add in H7. simpl chunk_of_type in H7. rewrite Int.add_commut in H7. rewrite (Int.add_zero) in H7. 
  exploit Mem.loadv_inject; eauto.
  destruct 1. destruct H.
  intro.
  destruct (IHl _ _ H3 r2s). destruct H2.
  esplit. split. econstructor. econstructor. unfold load_stack. simpl Val.add. rewrite Int.add_commut.  eassumption.
  eassumption.
  constructor; eauto.
Qed.

Lemma find_label_is_tail:
  forall f lbl c',
    find_label lbl f = Some c' ->
    is_tail c' f.
Proof.
  induction f; simpl.
   discriminate.
  intros until c'. destruct (is_label lbl a).
   injection 1; intros; subst. constructor. constructor.
  intros. constructor. eauto.
Qed.

Theorem transf_step_correct_:
  forall s1 t s2, Mach.step ge s1 t s2 ->
  forall ofs_bound s1' (MS: match_states_ ofs_bound s1 s1') (NO_OVERFLOW: 0 <= ofs_bound - trace_needs_or_consumes external_event_needs stacksizes t),
  exists s2', Mach2.step external_event_needs RAO ge s1' t s2' /\ match_states_ (ofs_bound - trace_consumes stacksizes t) s2 s2'.
Proof.
  inversion 1; subst; inversion 1; subst; inversion HMATCH; clear MS HMATCH; subst.

+ (* label *)
  esplit.
  split.
  constructor.
  econstructor. 
  econstructor; eauto using is_tail_cons_left.
  assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption.  simpl; omega.

+ (* getstack *)
  unfold load_stack in H0.
  rewrite Val.add_commut in H0.
  replace (Val.add (Vint ofs) (Vptr sp Int.zero)) with (Vptr sp ofs) in H0.
  exploit Mem.loadv_inject; eauto.  
  intros [v2 [Hload2 Hv2]].
  esplit.
  split.
  econstructor.
  unfold load_stack.
  replace (Val.add (Vptr stackblock (Int.repr (ofs_bound + (size_chunk Mint32)))) (Vint ofs))
          with (Vptr stackblock (Int.add ofs (Int.repr (ofs_bound + (size_chunk Mint32))))).
  eassumption.
  simpl. rewrite Int.add_commut. reflexivity.
  econstructor.
  econstructor; eauto  using is_tail_cons_left.
  intros.
  unfold Regmap.get, Regmap.set.
  destruct (RegEq.eq r dst); eauto.
  assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. simpl; omega.
 simpl. rewrite Int.add_commut. rewrite Int.add_zero. reflexivity.

+ (* setstack *)
  unfold store_stack in H0.
  rewrite Val.add_commut in H0.
  replace (Val.add (Vint ofs) (Vptr sp Int.zero)) with (Vptr sp ofs) in H0.
  exploit Mem.storev_mapped_inject; eauto.
  intros [m'2 [Hm'2 Hinj2]].
  exploit match_stacks_store_inside.
   2: eexact H0.
   eassumption.
   3: eexact Hm'2.
  2: eapply INJ_REG.
  econstructor.
  eassumption.
  reflexivity.
  eassumption.
  intro STACK'.
  esplit.
  split.
  econstructor.
  unfold store_stack. 
  replace (Val.add (Vptr stackblock (Int.repr (ofs_bound + (size_chunk Mint32)))) (Vint ofs)) with (Vptr stackblock (Int.add ofs (Int.repr (ofs_bound + (size_chunk Mint32))))).
  eassumption.
  simpl. rewrite Int.add_commut. reflexivity.
 econstructor.
 simpl in Hm'2; econstructor; eauto using Mem.store_valid_access_1, is_tail_cons_left.
 intros; eauto using Mem.perm_store_2.
 unfold Regmap.get, undef_setstack. eauto using undef_move_inject.
 assumption. assumption. assumption. 
 intros. intro. eapply MEM_NO_PERMS; eauto using Mem.perm_store_2.
 intros. eapply Mem.perm_store_1. eassumption. eauto.
 intros; eauto using Mem.perm_store_2.
 assumption. assumption.
 eauto using Mem.store_valid_block_1. 
 simpl; omega.
 simpl. rewrite Int.add_commut. rewrite Int.add_zero. reflexivity.

+(* getparam *)
 unfold load_stack in H2.
 destruct s.
  discriminate.
 inversion STACK; subst.
 simpl parent_sp in H2.
 simpl Val.add in H2.
 rewrite Int.add_commut in H2.
 rewrite Int.add_zero in H2.
 exploit Mem.loadv_inject; eauto.
 intros [v2 [Hload2 Hv2]].
 esplit.
 split.
  econstructor.
  eassumption.
  reflexivity.
  unfold load_stack.
  replace 
    (Val.add
 (Val.add (Vptr stackblock (Int.repr (ofs_bound + (size_chunk Mint32))))
        (Vint (Int.repr (fn_stacksize phi + (size_chunk Mint32))))) (Vint ofs)) 
  with 
 (Vptr stackblock
                (Int.add ofs
                         (Int.repr (ofs_bound + (size_chunk Mint32) + fn_stacksize phi + (size_chunk Mint32))))).
  eassumption.
  simpl Val.add.
  replace (ofs_bound + (size_chunk Mint32) + fn_stacksize phi + (size_chunk Mint32)) with ((ofs_bound + (size_chunk Mint32)) + (fn_stacksize phi + (size_chunk Mint32))) by omega.
  rewrite add_repr.
  rewrite Int.add_commut.
  reflexivity.
 econstructor.
 econstructor.
 eassumption. eassumption. 2: eexact HOFS_RA. reflexivity. reflexivity. assumption. assumption. assumption. reflexivity. eauto using is_tail_cons_left. assumption.
 unfold Regmap.get, Regmap.set.
 intro.
 destruct (RegEq.eq r dst).
  assumption.
 destruct (RegEq.eq r Machregs.IT1).
  constructor.
 eauto.
 assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption.  simpl; omega.

+ (* op *)
exploit eval_operation_inj.
eapply symbol_address_inject. eapply INJ_GLOBALS.
intros. eapply Mem.valid_pointer_inject_val. eassumption. eassumption. econstructor. eassumption. reflexivity.
intros. eapply Mem.weak_valid_pointer_inject_val. eassumption. eassumption. econstructor. eassumption. reflexivity.
intros. eapply Mem.weak_valid_pointer_inject_no_overflow. eassumption. eassumption. eassumption.
intros. eapply Mem.different_pointers_inject; eauto.
3: eassumption.
econstructor. eassumption. symmetry. rewrite Int.add_commut. rewrite Int.add_zero. reflexivity.
eapply regset_inject_list. eassumption.
intros [v2 [Hop2 Hv2]].
esplit.
split.
econstructor.
eassumption.
econstructor.
econstructor; eauto using is_tail_cons_left.
intros. unfold Regmap.get, Regmap.set.
destruct (RegEq.eq r res); auto.
eauto using undef_op_inject.
assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption.  simpl; omega.

+ (* load *)
exploit eval_addressing_inj.
eapply symbol_address_inject. eapply INJ_GLOBALS.
3: eassumption.
econstructor. eassumption. symmetry. rewrite Int.add_commut. rewrite Int.add_zero. reflexivity.
eapply regset_inject_list. eassumption.
intros [v2 [Haddr2 Hv2]].
exploit Mem.loadv_inject; eauto.
intros [v3 [Hload3 Hv3]].
esplit. split. econstructor.
eassumption. eassumption. 
econstructor.
econstructor; eauto using is_tail_cons_left.
intros. unfold Regmap.get, Regmap.set.
destruct (RegEq.eq r dst); auto.
eauto using undef_temps_inject.
assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. simpl; omega.

+ (* store *)
exploit eval_addressing_inj.
eapply symbol_address_inject. eapply INJ_GLOBALS.
3: eassumption.
econstructor. eassumption. symmetry. rewrite Int.add_commut. rewrite Int.add_zero. reflexivity.
eapply regset_inject_list. eassumption.
intros [v2 [Haddr2 Hv2]].
exploit Mem.storev_mapped_inject; eauto.
intros [m3 [Hstore3 Hm3]].
esplit. split. econstructor.
eassumption. eassumption. 
econstructor.
econstructor; eauto using is_tail_cons_left.
destruct v2; try discriminate.
simpl in Hstore3. eauto using Mem.store_valid_access_1.
destruct a; try discriminate; simpl in *. intros; eauto using Mem.perm_store_2.
intros. unfold Regmap.get, Regmap.set. eapply undef_temps_inject; eauto.
assumption. 
eapply match_stacks_store_inside.
2: eassumption. eassumption. eassumption. eapply INJ_REG. eassumption. assumption.
assumption.
generalize H1. case_eq a; unfold Mem.storev; simpl; try discriminate.
intros until 2; subst.
intros. intro. eapply MEM_NO_PERMS. eassumption. eassumption.
eapply Mem.perm_store_2. eassumption. eassumption.
destruct v2; unfold Mem.storev; simpl in *; try discriminate.
intros. eapply Mem.perm_store_1. eassumption. eauto.
destruct v2; simpl in *; try discriminate. intros; eauto using Mem.perm_store_2.
destruct v2; simpl in *; try discriminate.
assumption. assumption. 
destruct v2; simpl in *; try discriminate; eauto using Mem.store_valid_block_1.
simpl; omega.

+ (* call *)
exploit RAO_EX.
eassumption.
destruct 1.
assert (HOFS_RA': Mem.valid_access m' Mint32 stackblock ofs_bound Writable).
 eapply Mem.valid_access_implies. eassumption. constructor.
destruct (Mem.valid_access_store _ _ _ _ (Vptr fb x) HOFS_RA').
clear HOFS_RA'.
esplit. split. econstructor.
eapply find_function_ptr_inject. eassumption. assumption. eassumption.
eassumption.
rewrite add_repr. simpl. rewrite Int.add_commut. rewrite Int.sub_add_l. rewrite Int.sub_idem. rewrite Int.add_commut. rewrite Int.add_zero. reflexivity.
simpl. rewrite Int.unsigned_repr. eassumption.
generalize (match_stacks_bound _ _ _ _ _ _ STACK).
intro.
generalize (Int.unsigned_range bound).
unfold Int.max_unsigned in *. intros. Opaque Int.modulus.
simpl in *; omega.
assumption.
econstructor.
econstructor.
3: reflexivity. reflexivity. reflexivity. 
eapply find_function_ptr_inj. eapply INJ_GLOBALS. assumption. eassumption. assumption.
eapply Mem.store_outside_inject.
eassumption.
2: eassumption.
simpl. 
destruct 3.
eapply MEM_NO_PERMS. eassumption.
instantiate (1 := ofs'). simpl; omega.
eassumption.
econstructor.
assumption.
eassumption.
assumption.
assumption.
assumption.
instantiate (1 := ofs_bound + (size_chunk Mint32) + fn_stacksize phi). omega.
assumption.
erewrite Mem.load_store_same. 2: eassumption. simpl. reflexivity.
eapply Mem.store_valid_access_1. eassumption. assumption.
assumption.
eapply is_tail_cons_left. eassumption.
intros. eapply MEM_NO_PERMS; eauto. omega.
assumption. 
eapply match_stacks_store_outside.
eassumption.
eassumption.
assumption.
simpl. right. left. omega.
assumption.
intros. eapply MEM_NO_PERMS; eauto. simpl in *; omega.
intros. eapply Mem.perm_store_1. eassumption. eapply TGT_MEM_PERMS. simpl in *; omega.
intros; eauto using Mem.perm_store_2.
assumption.
assumption.
eauto using Mem.store_valid_block_1.
simpl; omega.

+ (* tailcall *)
esplit. split. econstructor.
eapply find_function_ptr_inject. eassumption. assumption. eassumption.
eassumption.
unfold Val.add. rewrite <- add_repr. reflexivity.
congruence.
econstructor. econstructor; eauto.
eapply find_function_ptr_inj.  eapply INJ_GLOBALS. assumption. eassumption. assumption.
eapply Mem.free_left_inject. eassumption. eassumption.
eapply match_stacks_free_left. eassumption.
intros. eapply Mem.perm_free_3. eassumption. assumption.
simpl in *; omega.
intros. destruct (zlt (ofs' + o') (ofs_bound + (size_chunk Mint32))).
intro. eapply MEM_NO_PERMS; eauto using Mem.perm_free_3; omega.
intro.
exploit Mem.perm_free_3; eauto. intro.
destruct (zeq b stk).
 subst. replace o' with (ofs_bound + (size_chunk Mint32)) in * by congruence.
 generalize (SRC_MEM_NO_PERMS _ _ _ H8). intro.
 eapply Mem.perm_free_2. eassumption. replace f with phi by congruence. eassumption. eassumption.
 assert (0 <= ofs' + o' - (ofs_bound + (size_chunk Mint32)) < fn_stacksize phi) by omega.
replace phi with f in H9 by congruence.
 generalize (Mem.free_range_perm _ _ _ _ _ H4 _ H9).
 intro.
exploit Mem.inject_no_overlap.
 eassumption.
 eexact n.
 eassumption.
 eassumption.
 eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
 eapply Mem.perm_cur_max. eapply Mem.perm_implies. eassumption. constructor.
 unfold block; omega.
intros. destruct (zlt ofs' (ofs_bound + (size_chunk Mint32))).
 eapply TGT_MEM_PERMS. omega.
replace ofs' with (ofs' - (ofs_bound + (size_chunk Mint32)) + (ofs_bound + (size_chunk Mint32))) by omega.
eapply Mem.perm_inject. eassumption. eassumption.
eapply Mem.free_range_perm. eassumption. replace phi with f in * by congruence. omega.
assumption.
assumption.
assumption.
assumption.
replace phi with f in * by congruence. simpl. erewrite ge_stacksizes. simpl. omega.
eassumption.

+ (* builtin *)
exploit Events.external_call_mem_inject.
eassumption.
eassumption.
eassumption.
instantiate (1 := r2s ## args). 
eapply regset_inject_list. assumption.
intros [f' [vres' [m2' [CALL' [INJRES [INJECT' [UNMAPPED [OUT_OF_REACH [INJECT_INCR INJECT_SEP]]]]]]]]].
esplit. split. econstructor. eassumption.
Opaque size_chunk. injection 1. Transparent size_chunk. intros; subst s0; subst.
rewrite Int.unsigned_repr.
erewrite external_call_needs in NO_OVERFLOW.
intro. intros.
eapply TGT_MEM_PERMS. generalize (size_chunk_pos Mint32). omega.
eassumption.
exploit match_stacks_bound. eassumption.
generalize (Int.unsigned_range bound). unfold Int.max_unsigned. generalize (size_chunk_pos Mint32). omega.
econstructor.
econstructor.
eapply INJECT_INCR. assumption.
eassumption.
reflexivity.
inversion HOFS_RA. split; eauto.
intro. intros. eapply OUT_OF_REACH.
intro. intros.
simpl in H3. eapply MEM_NO_PERMS. eassumption. simpl in *; omega.
eapply H1; eauto.
reflexivity.
assumption.
assumption.
apply INJECT_INCR. assumption.
reflexivity.
eapply is_tail_cons_left. eassumption.
intros. apply Mem.perm_max in H1. eapply Mem.perm_implies in H1.
2: instantiate (1 := Nonempty).
exploit external_call_max_perm. eexact H0. 2: eassumption.
eapply Mem.valid_block_inject_1. eassumption. eassumption.
eauto.
constructor.
intro. unfold Regmap.get, Regmap.set.
destruct (RegEq.eq r res).
assumption.
eapply val_inject_incr. eassumption. eapply undef_temps_inject. auto.
assumption.
eapply match_stacks_external. 
2: eassumption. assumption. assumption. assumption.
intros; eauto using external_call_max_perm.
assumption.
assumption.
unfold inject_separated in INJECT_SEP.
intros. case_eq (inj b0).
 intros. destruct p0. generalize (INJECT_INCR _ _ _ H3). rewrite H1. injection 1; intros; subst b1; subst.
 intro. apply Mem.perm_max in H5. eapply Mem.perm_implies in H5.
 2: instantiate (1 := Nonempty).
 exploit external_call_max_perm. 3: eassumption. eassumption. eauto using Mem.valid_block_inject_1.
 eapply MEM_NO_PERMS; eauto.
 constructor.
intro. exploit INJECT_SEP; eauto. destruct 1.
destruct H5. eapply Mem.valid_block_inject_2. eexact INJ_SP. eassumption.
intros. eapply OUT_OF_REACH.
unfold loc_out_of_reach. intros. eapply MEM_NO_PERMS. eassumption. omega.
eauto.
intros. apply Mem.perm_max in H1.
exploit external_call_max_perm. 3: eassumption. eassumption. eauto using Mem.valid_block_inject_2.
apply TGT_MEM_PERMS_BOUND.
unfold meminj_preserves_globals, inject_incr in *. destruct INJ_GLOBALS as [? [? ?]]. split; eauto. split; eauto.
intros. case_eq (inj b1).
 destruct p. intro. exploit INJECT_INCR; eauto. rewrite H5. injection 1; intros; subst; eauto.
intro. exploit INJECT_SEP; eauto. destruct 1. destruct H8. eauto using Mem.valid_block_inject_2.
unfold inject_incr in *; eauto.
eauto using external_call_valid_block.
erewrite external_call_consumes. omega. eassumption.

+ (* annot *)
exploit annot_arguments_inject.
eassumption.
eassumption.
exploit match_stacks_bound. eassumption.
generalize (Int.unsigned_range bound). unfold Int.max_unsigned. simpl in *; omega.
eassumption.
eassumption.
destruct 1 as [? [? ?]].
exploit Events.external_call_mem_inject.
eassumption.
eassumption.
eassumption.
eassumption.
intros [f' [vres' [m2' [CALL' [INJRES [INJECT' [UNMAPPED [OUT_OF_REACH [INJECT_INCR INJECT_SEP]]]]]]]]].
esplit. split. econstructor. eassumption. eassumption.
Opaque size_chunk. injection 1. Transparent size_chunk. intros; subst s0; subst. rewrite Int.unsigned_repr.
erewrite external_call_needs in NO_OVERFLOW.
intro. intros.
eapply TGT_MEM_PERMS. generalize (size_chunk_pos Mint32). omega.
eassumption.
exploit match_stacks_bound. eassumption.
generalize (Int.unsigned_range bound). unfold Int.max_unsigned. generalize (size_chunk_pos Mint32). omega.
econstructor. 
econstructor.
eapply INJECT_INCR. assumption.
eassumption.
reflexivity.
inversion HOFS_RA. split; eauto.
intro. intros. eapply OUT_OF_REACH.
intro. intros. 
simpl in H6. eapply MEM_NO_PERMS. eassumption. simpl; omega.
eapply H4; eauto.
reflexivity.
assumption.
assumption.
apply INJECT_INCR. assumption.
reflexivity.
eapply is_tail_cons_left. eassumption.
intros. apply Mem.perm_max in H4. eapply Mem.perm_implies in H4.
2: instantiate (1 := Nonempty).
exploit external_call_max_perm. eexact H1. 2: eassumption.
eapply Mem.valid_block_inject_1. eassumption. eassumption.
eauto.
constructor.
intro. 
eapply val_inject_incr. eassumption. auto.
assumption.
eapply match_stacks_external. 
2: eassumption. assumption. assumption. assumption.
intros; eauto using external_call_max_perm.
assumption.
assumption.
unfold inject_separated in INJECT_SEP.
intros. case_eq (inj b0).
 intros. destruct p0. generalize (INJECT_INCR _ _ _ H6). rewrite H4. injection 1; intros; subst b1; subst.
 intro. apply Mem.perm_max in H8. eapply Mem.perm_implies in H8.
 2: instantiate (1 := Nonempty).
 exploit external_call_max_perm. 3: eassumption. eassumption. eauto using Mem.valid_block_inject_1.
 eapply MEM_NO_PERMS; eauto.
 constructor.
intro. exploit INJECT_SEP; eauto. destruct 1.
destruct H8. eapply Mem.valid_block_inject_2. eexact INJ_SP. eassumption.
intros. eapply OUT_OF_REACH.
unfold loc_out_of_reach. intros. eapply MEM_NO_PERMS. eassumption. omega.
eauto.
intros. apply Mem.perm_max in H4.
exploit external_call_max_perm. 3: eassumption. eassumption. eauto using Mem.valid_block_inject_2.
apply TGT_MEM_PERMS_BOUND.
unfold meminj_preserves_globals, inject_incr in *. destruct INJ_GLOBALS as [? [? ?]]. split; eauto. split; eauto.
intros. case_eq (inj b1).
 destruct p. intro. exploit INJECT_INCR; eauto. rewrite H8. injection 1; intros; subst; eauto.
intro. exploit INJECT_SEP; eauto. destruct 1. destruct H11. eauto using Mem.valid_block_inject_2.
unfold inject_incr in *; eauto.
eauto using external_call_valid_block.
erewrite external_call_consumes. omega. eassumption.

+ (* goto *)
replace phi with f in * by congruence.
esplit. split. econstructor; eauto.
econstructor. econstructor; eauto.
eauto using find_label_is_tail.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
simpl; omega.

+ (* cond true *)
replace phi with f in * by congruence.
esplit.
split.
econstructor.
eapply eval_condition_inj.
intros. eapply Mem.valid_pointer_inject_val. eassumption. eassumption. econstructor. eassumption. reflexivity.
intros. eapply Mem.weak_valid_pointer_inject_val. eassumption. eassumption. econstructor. eassumption. reflexivity.
intros. eapply Mem.weak_valid_pointer_inject_no_overflow. eassumption. eassumption. eassumption.
intros. eapply Mem.different_pointers_inject; eauto.
2: eassumption.
eapply regset_inject_list. eassumption.
eassumption.
eassumption.
econstructor.
econstructor; eauto using find_label_is_tail.
eauto using undef_temps_inject.
assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. 
simpl; omega.

+ (* cond false *)
esplit.
split.
eapply Mach2.exec_Mcond_false.
eapply eval_condition_inj.
intros. eapply Mem.valid_pointer_inject_val. eassumption. eassumption. econstructor. eassumption. reflexivity.
intros. eapply Mem.weak_valid_pointer_inject_val. eassumption. eassumption. econstructor. eassumption. reflexivity.
intros. eapply Mem.weak_valid_pointer_inject_no_overflow. eassumption. eassumption. eassumption.
intros. eapply Mem.different_pointers_inject; eauto.
2: eassumption.
eapply regset_inject_list. eassumption.
econstructor.
econstructor; eauto using is_tail_cons_left.
eauto using undef_temps_inject.
assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption. assumption.
simpl; omega.

+ (* jumptable *)
replace phi with f in * by congruence.
esplit. split. econstructor; eauto.
generalize (INJ_REG arg).
unfold Regmap.get.
rewrite H0.
inversion 1; subst. reflexivity.
econstructor. econstructor; eauto.
eauto using find_label_is_tail.
eauto using undef_temps_inject.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
simpl; omega.

+ (* return *)
replace phi with f in * by congruence.
esplit.
split.
econstructor; eauto.
econstructor.
simpl.
rewrite <- add_repr.
econstructor; eauto.
eassumption.
eapply Mem.free_left_inject. eassumption. eassumption.
eapply match_stacks_free_left. eassumption.
intros. eapply Mem.perm_free_3. eassumption. assumption.
omega.
intros. destruct (zlt (ofs' + o') (ofs_bound + (size_chunk Mint32))).
intro. eapply MEM_NO_PERMS; eauto using Mem.perm_free_3; omega.
intro.
exploit Mem.perm_free_3; eauto. intro.
destruct (zeq b stk).
 subst. replace o' with (ofs_bound + (size_chunk Mint32)) in * by congruence.
 generalize (SRC_MEM_NO_PERMS _ _ _ H7). intro.
 eapply Mem.perm_free_2. eassumption. eassumption. eassumption.
 assert (0 <= ofs' + o' - (ofs_bound + (size_chunk Mint32)) < fn_stacksize f) by (simpl in *; omega).
 generalize (Mem.free_range_perm _ _ _ _ _ H3 _ H8).
 intro.
exploit Mem.inject_no_overlap.
 eassumption.
 eexact n.
 eassumption.
 eassumption.
 eapply Mem.perm_max. eapply Mem.perm_implies. eassumption. constructor.
 eapply Mem.perm_cur_max. eapply Mem.perm_implies. eassumption. constructor.
 unfold block; omega.
intros. destruct (zlt ofs' (ofs_bound + (size_chunk Mint32))).
 eapply TGT_MEM_PERMS. omega.
replace ofs' with (ofs' - (ofs_bound + (size_chunk Mint32)) + (ofs_bound + (size_chunk Mint32))) by omega.
eapply Mem.perm_inject. eassumption. eassumption.
eapply Mem.free_range_perm. eassumption. simpl in *; omega. 
assumption.
assumption.
assumption.
assumption.
simpl. erewrite ge_stacksizes. simpl. omega.
eassumption.

+ (* callstate internal *)
assert (TRACEVAL: trace_consumes stacksizes (Event_call (fn_id f) :: E0) = (fn_stacksize f + size_chunk Mint32) /\
trace_needs_or_consumes external_event_needs stacksizes (Event_call (fn_id f) :: E0) = (fn_stacksize f + size_chunk Mint32)
).
 simpl. unfold event_needs_or_consumes. simpl. erewrite ge_stacksizes. simpl; split; omega. eassumption.
destruct TRACEVAL as [TRACEVAL_needs TRACEVAL_consumes].
rewrite TRACEVAL_needs, TRACEVAL_consumes.
generalize (ge_stacksizes_pos _ _ H0). intro SZ_POS.
intro.
exploit Mem.alloc_left_mapped_inject.
 eassumption. eassumption. eassumption.
instantiate (1 := ofs_stack - fn_stacksize f). generalize (size_chunk_pos Mint32). exploit match_stacks_bound. eassumption. generalize (Int.unsigned_range bound). unfold Int.max_unsigned. omega.
intros. exploit TGT_MEM_PERMS_BOUND. eassumption. generalize (Int.unsigned_range bound). unfold Int.max_unsigned. omega.
intros. apply Mem.perm_cur. eapply Mem.perm_implies. 2: instantiate (1 := Freeable). eapply TGT_MEM_PERMS. generalize (size_chunk_pos Mint32). omega. constructor.
intro. intros. eapply Z.divide_trans. eapply strong_align_chunk. 
replace (ofs_stack - fn_stacksize f) with (ofs_stack + size_chunk Mint32 - (fn_stacksize f + size_chunk Mint32)) by omega.
apply Z.divide_sub_r. eauto using match_stacks_align. eauto.
intros. eapply MEM_NO_PERMS. eassumption. 2: eassumption. generalize (size_chunk_pos Mint32). omega.
intros [inj' [INJ' [INJECT_INCR [INJ'_NEW INJ'_OLD]]]].
esplit. split.
econstructor. eassumption. simpl. rewrite <- sub_repr. reflexivity. reflexivity.
econstructor. econstructor.
eapply INJECT_INCR. assumption.
eassumption.
reflexivity.
2: reflexivity. 
5: replace (ofs_stack - fn_stacksize f) with (ofs_stack - (fn_stacksize f + (size_chunk Mint32)) + (size_chunk Mint32)) by omega.
5: reflexivity.
split.
 intro. intros. 
 eapply Mem.perm_implies.
 eapply TGT_MEM_PERMS.
 simpl in *; omega.
 constructor.
 replace (ofs_stack - (fn_stacksize f + size_chunk Mint32)) with
 (ofs_stack + size_chunk Mint32 - (fn_stacksize f + size_chunk Mint32) - size_chunk Mint32) by omega.
 apply Z.divide_sub_r. eapply Z.divide_trans. eapply strong_align_chunk. apply Z.divide_sub_r. eapply match_stacks_align. eassumption. eapply ge_align. eassumption.
 apply align_size_chunk_divides.
 assumption.
 eapply ge_align. eassumption.
 rewrite INJ'_NEW. f_equal. f_equal. omega.
 constructor.
 eapply Mem.perm_alloc_3. eassumption.
 intros. eapply val_inject_incr. eassumption. eapply undef_temps_inject. auto. 
 assumption.
replace (ofs_stack - (fn_stacksize f + size_chunk Mint32) + size_chunk Mint32 + fn_stacksize f) with ofs_stack by omega.
eapply match_stacks_alloc_left. eassumption. instantiate (1 := m). destruct p. intros; eauto using Mem.valid_block_inject_1.
intros. eapply Mem.perm_alloc_4. eassumption. assumption. intro. subst; eapply Mem.fresh_block_alloc; eauto.
assumption.
intros. destruct (zeq b stk).
 subst. rewrite INJ'_NEW in H5. injection H5; intros; subst. exploit Mem.perm_alloc_3; eauto. generalize (size_chunk_pos Mint32). omega.
exfalso; rewrite INJ'_OLD in H5; congruence.
assumption.
generalize (size_chunk_pos Mint32). intro.
intro. destruct (zeq b stk).
 subst. rewrite INJ'_NEW. injection 1; intros; subst. intro. exploit Mem.perm_alloc_3; eauto. omega.
rewrite INJ'_OLD. intros. intro. eapply MEM_NO_PERMS. eassumption. 2: eapply Mem.perm_alloc_4. 3: eassumption. omega. eassumption. assumption. assumption.
intros. eapply TGT_MEM_PERMS. omega.
assumption.
unfold meminj_preserves_globals, inject_incr in *. destruct INJ_GLOBALS as [? [? ?]]. split; eauto. split; eauto.
intros. destruct (zeq b1 stk).
 congruence.
rewrite INJ'_OLD in H8; eauto.
intros. apply INJECT_INCR; eauto.
assumption.
reflexivity.

+ (* callstate external *)
assert (exists args',
  extcall_arguments r2s m'0 (Val.add (Vptr stackblock (Int.repr ofs_stack)) (Vint (Int.repr (size_chunk Mint32)))) (ef_sig ef) args' /\
  val_list_inject inj args args'
).
 inversion STACK; subst.
 (* empty stack: main is external. This is a valid case, but there are no arguments *)
 unfold extcall_arguments in *. unfold Conventions1.loc_arguments in *. destruct (sig_args (ef_sig ef)); simpl in *; inversion H2; subst.
  esplit. split; constructor.
  destruct t0; discriminate.
  (* everything on stack *)
  destruct t0; injection H3; intros; subst; simpl in *; inversion H4; subst; discriminate.
 (* nonempty stack: location of arguments is known and some invariants do hold. *)
 unfold Val.add. rewrite <- add_repr. 
 eapply extcall_arguments_inject; eauto.
destruct H3.
destruct H3.
exploit Events.external_call_mem_inject.
eassumption.
eassumption.
eassumption.
eassumption.
intros [f' [vres' [m2' [CALL' [INJRES [INJECT' [UNMAPPED [OUT_OF_REACH [INJECT_INCR INJECT_SEP]]]]]]]]].
esplit. split. econstructor. eassumption.
eassumption.
reflexivity.
assumption.
reflexivity.
injection 1; intros; subst s0; subst.
erewrite external_call_needs in NO_OVERFLOW.
rewrite Int.unsigned_repr.
intro. intros.
eapply TGT_MEM_PERMS. omega.
exploit match_stacks_bound. eassumption.
generalize (Int.unsigned_range bound). unfold Int.max_unsigned. omega.
eassumption.
econstructor.
econstructor.
reflexivity.
reflexivity.
reflexivity.
instantiate (1 := f').
unfold Regmap.get, Regmap.set.
intro.
destruct (RegEq.eq r (Conventions1.loc_result (ef_sig ef))).
 assumption.
eapply val_inject_incr; eauto.
assumption.
eapply match_stacks_external. 
2: eassumption. assumption. assumption. assumption.
intros; eauto using external_call_max_perm.
assumption.
assumption.
unfold inject_separated in INJECT_SEP.
intros. case_eq (inj b).
 intros. destruct p0. generalize (INJECT_INCR _ _ _ H7). rewrite H5. injection 1; intros; subst b0; subst.
 intro. apply Mem.perm_max in H9. eapply Mem.perm_implies in H9.
 2: instantiate (1 := Nonempty).
 exploit external_call_max_perm. 3: eassumption. eassumption. eauto using Mem.valid_block_inject_1.
 eapply MEM_NO_PERMS; eauto.
 constructor.
intro. exploit INJECT_SEP; eauto. destruct 1. contradiction.
intros. eapply OUT_OF_REACH.
unfold loc_out_of_reach. intros. eapply MEM_NO_PERMS. eassumption. omega.
eauto.
intros. apply Mem.perm_max in H5.
exploit external_call_max_perm. 3: eassumption. eassumption. eauto using Mem.valid_block_inject_2.
apply TGT_MEM_PERMS_BOUND.
unfold meminj_preserves_globals, inject_incr in *. destruct INJ_GLOBALS as [? [? ?]]. split; eauto. split; eauto.
intros. case_eq (inj b1).
 destruct p. intro. exploit INJECT_INCR; eauto. rewrite H9. injection 1; intros; subst; eauto.
intro. exploit INJECT_SEP; eauto. destruct 1. destruct H12. eauto using Mem.valid_block_inject_2.
unfold inject_incr in *; eauto.
eauto using external_call_valid_block.
erewrite external_call_consumes. omega. eassumption.

+ (* returnstate *)
replace (ofs_stack - trace_consumes stacksizes E0) with ofs_stack.
inversion STACK; subst.
esplit.
split.
econstructor.
unfold Val.add. rewrite <- add_repr. replace (ofs_pre - (fn_stacksize phi + size_chunk Mint32) + size_chunk Mint32) with (ofs_pre - fn_stacksize phi) by omega. reflexivity.
unfold Mem.loadv. rewrite Int.unsigned_repr. eassumption.
exploit match_stacks_bound. eexact STACK. generalize (Int.unsigned_range bound). unfold Int.max_unsigned. omega.
eassumption.
assumption.
econstructor.
econstructor.
eassumption.
eassumption.
reflexivity.
eassumption.
instantiate (1 := ofs_pre). omega.
assumption.
assumption.
assumption.
f_equal. omega.
assumption.
assumption.
assumption.
assumption.
assumption.
assumption.
intros.
destruct (zlt (ofs' + o') (ofs_pre - (fn_stacksize phi + size_chunk Mint32))).
 eapply MEM_NO_PERMS. eassumption. omega.
eapply MEM_NO_PERMS0. eassumption. omega.
intros. destruct (zlt ofs' (ofs_pre - (fn_stacksize phi + size_chunk Mint32))).
 eapply TGT_MEM_PERMS. omega.
eapply MEM_RA_ACC. omega.
assumption.
assumption.
assumption.
assumption.
reflexivity.
simpl; omega.

Qed.

Lemma mach_single_events: forall s t s', Mach.step ge s t s' -> (length t <= 1)%nat.
Proof.
  inversion 1; subst; simpl; eauto using external_call_trace_length; omega.
Qed.

Section Initial_state.

Variable s_init: Mach.state.
Hypothesis s_init_no_overflow:
  forall s t, Smallstep.star Mach.step ge s_init t s ->
              trace_bound external_event_needs stacksizes t <= Int.unsigned bound.

Definition match_states__ s s' :=
  exists t_, Smallstep.star Mach.step ge s_init t_ s /\
             match_states_ (Int.unsigned bound - trace_consumes stacksizes t_) s s'.             
    
Theorem transf_step_correct__:
  forall s1 t s2, Mach.step ge s1 t s2 ->
  forall s1' (MS: match_states__ s1 s1'),
  exists s2', Mach2.step external_event_needs RAO ge s1' t s2' /\ match_states__ s2 s2'.
Proof.
  intros.
  destruct MS.
  destruct H0.
  generalize (star_trans H0 (star_one _ _ _ _ _ H) (refl_equal _)).
  intro.
  exploit transf_step_correct_.
  eassumption.
  eassumption.  
  refine (_ (s_init_no_overflow s2 _ _)).
  2: eassumption.
  unfold Eapp. intro.
  generalize (mach_single_events _ _ _ H).
  intro.
  generalize (trace_bound_single_event_needs_or_consumes external_event_needs stacksizes _ H3 x).
  omega.
 destruct 1.
 destruct H3.
 esplit.
 split.
 eassumption.
 econstructor.
 split.
 eassumption.
 replace (Int.unsigned bound - trace_consumes stacksizes (x ** t)) with (Int.unsigned bound - trace_consumes stacksizes x - trace_consumes stacksizes t).
 assumption.
 unfold Eapp. unfold trace_consumes in *. rewrite sum_app. omega.
Qed.

End Initial_state.

Definition match_states s s' :=
exists s_init: Mach.state,
  (forall s t, Smallstep.star Mach.step ge s_init t s ->
               trace_bound external_event_needs stacksizes t <= Int.unsigned bound
  ) /\
  match_states__ s_init s s'.
    
Theorem transf_step_correct:
  forall s1 t s2, Mach.step ge s1 t s2 ->
  forall s1' (MS: match_states s1 s1'),
  exists s2', Mach2.step external_event_needs RAO ge s1' t s2' /\ match_states s2 s2'.
Proof.
  destruct 2. destruct H0.
  exploit transf_step_correct__. eassumption. eassumption. eassumption.
  destruct 1. destruct H2.
  esplit. split. eassumption.
  esplit. split. eassumption. assumption.
Qed.


End STACKBLOCK.

End GE.

Section PROGRAM.

Variable p: Mach.program.

Function filter_functions (accu: list function) (de: list (ident * globdef fundef unit)) {struct de} : list function :=
  match de with
    | nil => accu
    | (_, Gfun (AST.Internal phi)) :: q => filter_functions (phi :: accu) q
    | _ :: q => filter_functions accu q
  end.

Lemma filter_functions_accu: forall phi accu,
                               In phi accu -> forall de, In phi (filter_functions accu de).
Proof.
  intros. revert accu H.
  induction de; simpl.
   tauto.
  destruct a. destruct g; auto. destruct f; auto.
  intros. eapply IHde. simpl; auto.
Qed.

Lemma filter_functions_correct:
  forall de fi phi, 
    In (fi, Gfun (AST.Internal phi)) de ->
    forall accu, In phi (filter_functions accu de).
Proof.
  induction de; simpl.
   tauto.
  destruct 1.
   subst.
   intros. eapply filter_functions_accu. simpl; auto.
  destruct a. destruct g; eauto. destruct f; eauto.
Qed.

Lemma filter_functions_complete_aux:
  forall de accu phi,
    In phi (filter_functions accu de) ->
    In phi accu \/ exists fi, In (fi, Gfun (AST.Internal phi)) de.
Proof.
  intros until accu. functional induction (filter_functions accu de); simpl; auto.
 intros. exploit IHl.
  eassumption.
 destruct 1.
  destruct H0.
   subst. eauto.
  auto.
 destruct H0. eauto.
 intros.
 exploit IHl.
 eassumption.
 destruct 1; eauto.
 destruct H0; eauto.
Qed.

Corollary filter_functions_complete:
  forall de phi,
    In phi (filter_functions nil de) ->
    exists fi, In (fi, Gfun (AST.Internal phi)) de.
Proof.
  intros. exploit filter_functions_complete_aux.
   eassumption.
  destruct 1; eauto; contradiction.
Qed.

Lemma stacksizes_prop:
  forall l, NoDup (List.map fn_id l) ->
            forall phi, In phi l ->
                        forall ini,
                          PMap.get phi.(fn_id) (List.fold_right (fun phi => PMap.set (phi.(fn_id)) (fn_stacksize phi + size_chunk Mint32)) ini l) = (fn_stacksize phi + size_chunk Mint32).
Proof.
  induction l; simpl.
   tauto.
  inversion 1; subst.
  destruct 1; subst.
   intros. rewrite PMap.gss. reflexivity.
  intros. rewrite PMap.gso. eauto.
  intro. eapply H2. rewrite <- H1. eapply in_map.  assumption.
Qed.

Lemma stacksizes_prop_not_in:
  forall l i, (forall phi, In phi l -> i <> phi.(fn_id)) ->
              forall ini,
                PMap.get i (List.fold_right (fun phi => PMap.set (phi.(fn_id)) (fn_stacksize phi + size_chunk Mint32)) ini l) = PMap.get i ini.
Proof.
  induction l; simpl; auto.
  intros. 
  rewrite PMap.gso; eauto.
Qed.  

Lemma identifier_searchable:
  forall l i,
    {phi | In phi l /\ phi.(fn_id) = i} + {forall phi, In phi l -> i <> phi.(fn_id)}.
Proof.
  induction l; simpl; try tauto.
  intro.
  destruct (peq (fn_id a) i); eauto.
  destruct (IHl i).
   destruct s as [? [? ?]]; eauto.
  right. destruct 1; eauto. congruence.
Qed.

Definition stacksizes := 
  List.fold_right (fun phi => PMap.set (phi.(fn_id)) (fn_stacksize phi + size_chunk Mint32))
                  (PMap.init 0)
                  (filter_functions nil (prog_defs p))
                 .

Require Import Behaviors.

(* HERE is the hypothesis that the semantics of the program does not stack overflow based on its behaviors in the infinite-stack semantics. *)
Hypothesis prog_behaviors_no_overflow: 
  forall beh, program_behaves (Mach.semantics p) beh ->
              forall t, behavior_prefix t beh ->
                        trace_bound external_event_needs stacksizes t <= Int.unsigned bound.

Let ge := Genv.globalenv p.
Let stackblock := Genv.genv_next ge.

Section Checkable_properties.

Hypothesis prog_fun_no_dup: NoDup (List.map fn_id (filter_functions nil (prog_defs p))).

Hypothesis prog_fun_align: 
  forall fi phi, In (fi, Gfun (AST.Internal phi)) (prog_defs p) ->
                 (strong_align | phi.(fn_stacksize) + size_chunk Mint32).

Hypothesis prog_fun_pos:
  forall fi phi, In (fi, Gfun (AST.Internal phi)) (prog_defs p) ->
                 0 <= phi.(fn_stacksize).

Lemma stacksizes_pos':
  forall f, 0 <= PMap.get f stacksizes.
Proof.
  intros.
  unfold stacksizes.
  destruct (identifier_searchable (filter_functions nil (prog_defs p)) f).
   destruct s. destruct a. subst.
   rewrite stacksizes_prop; auto. 
   exploit filter_functions_complete; eauto.
   destruct 1.
   generalize (prog_fun_pos _ _ H0).
   generalize (size_chunk_pos Mint32). omega.
  rewrite stacksizes_prop_not_in; auto. rewrite PMap.gi. omega.
Qed.

Theorem simulation': forward_simulation (Mach.semantics p) (Mach2.semantics external_event_needs RAO bound p).
Proof.
  eapply forward_simulation_step.
  reflexivity.
  Focus 3.
  intros. simpl. 
  instantiate (1 := match_states stacksizes ge stackblock).
  eapply transf_step_correct.
  
  unfold ge. intros.
  exploit (Genv.find_funct_ptr_inversion).
  eassumption.
  destruct 1.
  eauto.

  unfold ge. intros.
  exploit (Genv.find_funct_ptr_inversion).
  eassumption.
  destruct 1.
  eapply stacksizes_prop. assumption. eapply filter_functions_correct. eassumption.

  unfold ge. intros.
  exploit (Genv.find_funct_ptr_inversion).
  eassumption.
  destruct 1. 
  eauto.

  case_eq (Genv.find_var_info ge stackblock); auto.
  unfold Genv.find_var_info, stackblock, ge.
  intros. exfalso.
  generalize (Genv.genv_vars_range _ _ H1).
  omega.

  eassumption.

  assumption.

  (* initial states *)
  inversion 1; subst.
  unfold ge, ge0 in *. clear ge0.
  exploit Genv.initmem_inject.
  eassumption.
  intro.
  generalize (Genv.init_mem_genv_next _ H0).
  intro.
  case_eq (  Mem.alloc m0 0 (Int.unsigned bound)).
  intros.
  generalize (Mem.alloc_result _ _ _ _ _ H4).
  rewrite <- H3 in *.
  intro; subst.
  exploit Mem.alloc_right_inject.
  eassumption.
  eassumption.
  intro.
  esplit.
  split.
  econstructor.
  eassumption.
  eassumption.
  eassumption.
  econstructor.
  split.
  Focus 2.
  esplit.
  split.
  eapply star_refl.
  simpl.
  replace (Int.unsigned bound - 0) with (Int.unsigned bound) by omega.
  econstructor.
  econstructor.
  reflexivity.
  reflexivity.
  instantiate (1 := Int.unsigned bound). rewrite Int.repr_unsigned. reflexivity.
  instantiate (1 := Mem.flat_inj (Genv.genv_next (Genv.globalenv p))).
  unfold Mem.flat_inj. rewrite zlt_true. reflexivity.
  eapply Genv.genv_symb_range. eassumption.
  intros. unfold Regmap.get, Regmap.init. constructor.
  assumption.
  constructor.
  reflexivity.
  generalize (Int.unsigned_range bound). omega.
  intros. intro.
  generalize H6. unfold Mem.flat_inj. destruct (zlt b (Genv.genv_next (Genv.globalenv p))); try discriminate. injection 1; intros; subst.
  unfold stackblock in l. omega.
  intros. eapply Mem.perm_alloc_2. eassumption. assumption.
  intros. eapply Mem.perm_alloc_3. eassumption. eassumption.
  split; simpl.
   intros. unfold Mem.flat_inj. rewrite zlt_true. reflexivity. eapply Genv.genv_symb_range. eassumption.
  split. intros. unfold Mem.flat_inj. rewrite zlt_true. reflexivity. eapply Genv.genv_vars_range. eassumption.
  intros. unfold Mem.flat_inj in H7. destruct (zlt b1 (Genv.genv_next (Genv.globalenv p))); congruence. 
  intros. unfold Mem.flat_inj. rewrite zlt_true. reflexivity. eapply Genv.genv_funs_range. eassumption.
  eapply Mem.valid_new_block. eassumption.
  reflexivity.

  (* this initial state has no behaviors that stack overflow *)
  intros. 
  destruct (state_behaves_exists (Mach.semantics p) s).  
  eapply prog_behaviors_no_overflow .
  eleft. eassumption.
  eapply state_behaves_app. eassumption. eassumption.
  esplit. reflexivity.

  (* final states *)
  inversion 2; subst.
  inversion H; subst.
  destruct H2.
  destruct H3.
  destruct H3.
  inversion H4; subst.
  inversion HMATCH; subst.
  inversion STACK; subst.
  simpl. 
  econstructor. 
  generalize (INJ_REG  (Conventions1.loc_result {| sig_args := nil; sig_res := Some Tint |})).
  unfold Regmap.get.
  rewrite H1.
  inversion 1; subst. reflexivity.
  unfold stackblock. unfold ge. 
  rewrite HEQ.
  rewrite Int.repr_unsigned. reflexivity.

Qed.

End Checkable_properties.

Lemma NoDup_dec: forall l: list ident, {NoDup l} + {~ NoDup l}.
Proof.
  induction l.
   left. constructor.
  destruct (In_dec peq a l).
   right. intro. inversion H; subst. contradiction.
  destruct IHl.
   left. constructor; auto.
  right. intro. inversion H; subst. contradiction.
Defined.

Lemma prog_fun_align_dec: forall {A V: Type} (l: list (A * _)),
                            {forall fi phi, In (fi, Gfun (V := V) (AST.Internal phi)) l ->
                                            (strong_align | phi.(fn_stacksize) + size_chunk Mint32)} +
                            { ~ forall fi phi, In (fi, Gfun (AST.Internal phi)) l ->
                                            (strong_align | phi.(fn_stacksize) + size_chunk Mint32)}.
Proof.
  induction l; simpl.
   left. tauto.
  destruct a. assert ({phi | g = Gfun (Internal phi)} + {forall phi, g <> Gfun (Internal phi)}).
   destruct g; try (right; congruence). destruct f; try (right; congruence). eauto.
  destruct H.
   destruct s. subst.
  destruct (Zdivide_dec strong_align (fn_stacksize x + 4)).
   apply strong_align_pos.
   destruct IHl.
    left. destruct 1; eauto. congruence.
   right. intro. apply n; eauto.
  right. intro. apply  n; eauto.
 destruct IHl.
  left.
  destruct 1; eauto. edestruct n; congruence.
 right. intro. eapply n0; eauto.
 Grab Existential Variables.
 exact phi.
Defined.

Lemma prog_fun_pos_dec: forall {A V: Type} (l: list (A * _)),
                        {forall fi phi, In (fi, Gfun (V := V) (AST.Internal phi)) l->
                                        0 <= phi.(fn_stacksize)} + {~ forall fi phi, In (fi, Gfun (AST.Internal phi)) l->
                                        0 <= phi.(fn_stacksize)}.
Proof.
    induction l; simpl.
   left. tauto.
  destruct a. assert ({phi | g = Gfun (Internal phi)} + {forall phi, g <> Gfun (Internal phi)}).
   destruct g; try (right; congruence). destruct f; try (right; congruence). eauto.
  destruct H.
   destruct s. subst.
  destruct (zle 0 (fn_stacksize x)).
   destruct IHl.
    left. destruct 1; eauto. congruence.
   right. intro. apply n; eauto.
  right. intro. generalize (H _ _ (or_introl _ (refl_equal _))). omega.
 destruct IHl.
  left.
  destruct 1; eauto. edestruct n; congruence.
 right. intro. eapply n0; eauto.
 Grab Existential Variables.
 exact phi.
Defined.

Require Import Errors.

Definition transf_program := 
  if NoDup_dec (List.map fn_id (filter_functions nil (prog_defs p)))
               && prog_fun_align_dec (prog_defs p)
               && prog_fun_pos_dec (prog_defs p)
  then OK p else Error (msg "Program is ill-formed")
.

Theorem transf_program_correct: forall tprog,
  transf_program = OK tprog -> 
  forward_simulation (Mach.semantics p) (Mach2.semantics external_event_needs RAO bound tprog).
Proof.
  unfold transf_program. destruct (NoDup_dec (List.map fn_id (filter_functions nil (prog_defs p)))); try discriminate; simpl.
  destruct (prog_fun_align_dec (prog_defs p)); try discriminate; simpl.
  destruct (prog_fun_pos_dec (prog_defs p)); try discriminate; simpl.
  injection 1; intros; subst tprog; eauto using simulation'.
Qed.

Lemma stacksizes_pos: forall tprog,
  transf_program = OK tprog ->
  forall f, 0 <= PMap.get f stacksizes.
Proof.
  unfold transf_program. destruct (NoDup_dec (List.map fn_id (filter_functions nil (prog_defs p)))); try discriminate; simpl.
  destruct (prog_fun_align_dec (prog_defs p)); try discriminate; simpl.
  destruct (prog_fun_pos_dec (prog_defs p)); try discriminate; simpl.
  intros; eauto using stacksizes_pos'.
Qed.

End PROGRAM.

End BOUND.

End WITHRAO.

(*
Check transf_program_correct.
Goal False.
 idtac "".
Abort.

Print Assumptions transf_program_correct. 
*)
