(************************************************************************)
(*                                                                      *)
(*                Quantitative Hoare Logic for Clight                   *)
(*                                                                      *)
(*  Author: Quentin Carbonneaux (c) 2014              Yale University   *)
(*                                                                      *)
(************************************************************************)


Require Export Core.
Require Import Coqlib.
Require Import AST.
Require Import Clight.
Require Import Memory.
Require Import Events.
Require Import Values.
Require Import Integers.
Require Import Cop.
Require Import Ctypes.
Require Import Globalenvs.
Require Import Maps.
Require Import Smallstep.
Require Import List.

(* quantitative c syntax *)
Definition fid := ident.
Definition var := ident.

Instance QCSyn: BaseSyn fid var expr :=
  { fid_eq := ident_eq }.

Record finfo: Type := mkfinfo {
  fi_name: fid;
  fi_args: list (var * type);
  fi_locals: list (var * type);
  fi_body: stm;
  fi_return: type
}.

Definition genv := Genv.t finfo type.

Program Definition trgenv (ge: genv): Clight.genv :=
  Genv.mkgenv
    (Genv.genv_symb ge)
    (ZMap.init None)
    (Genv.genv_vars ge)
    (Genv.genv_next_pos ge)
    (Genv.genv_symb_range ge)
    _
    (Genv.genv_vars_range ge)
    _
    (Genv.genv_vars_inj ge).
Next Obligation. rewrite ZMap.gi in H. discriminate. Qed.
Next Obligation. rewrite ZMap.gi in H. discriminate. Qed.

Lemma find_symbol_trgenv:
  forall ge id, Genv.find_symbol ge id = Genv.find_symbol (trgenv ge) id.
Proof.
unfold Genv.find_symbol, trgenv; intros.
reflexivity.
Qed.


(* quantitative c semantics *)
Function find_info (ge: genv) (b: block) : option type :=
  match Genv.find_var_info ge b with
  | Some gv => Some gv.(gvar_info)
  | None => None
  end.

Function find_finfo (ge: genv) (f: ident): option finfo :=
  match Genv.find_symbol ge f with
  | Some b => Genv.find_funct_ptr ge b
  | None => None
  end.

Definition lval: Type := ((block * int) * type)%type.
Definition val: Type := (val * type)%type.
Definition stack := temp_env.

Definition eval_expr (ge: genv) (c: conf_) (e: expr) (v: Values.val): Prop :=
  Clight.eval_expr (trgenv ge) empty_env (c_stack c) (c_mem c) e v.

Definition leva_expr (ge: genv) (c: conf_) (e: expr) (p: block * int): Prop :=
  Clight.eval_lvalue (trgenv ge) empty_env (c_stack c) (c_mem c) e (fst p) (snd p).

Definition val_cast (v: val) (ty: type) :=
  sem_cast (fst v) (snd v) ty.

Inductive mem_set_ (ge: genv) (lx: lval) (vy: val) (m: mem): mem -> Prop :=
  | mem_set_intro:
      forall vy' m',
      val_cast vy (snd lx) = Some vy' ->
      assign_loc (snd lx) m (fst (fst lx)) (snd (fst lx)) vy' m' ->
      mem_set_ ge lx vy m m'.

Inductive stack_set_ (ge: genv) (v: var) (vx: val) (s: temp_env): temp_env -> Prop :=
  | stack_set_intro:
      stack_set_ ge v vx s (PTree.set v (fst vx) s).

Inductive castl: list val -> typelist -> list Values.val -> Prop :=
  | castl_nil: castl nil Tnil nil
  | castl_cons:
      forall vx ty v vxs tys vs,
      val_cast vx ty = Some v ->
      castl vxs tys vs ->
      castl (cons vx vxs) (Tcons ty tys) (cons v vs).

Inductive fun_init_ (ge: genv) (f: fid) (args: list val): temp_env -> Prop :=
  | fun_init_intro:
      forall fi vas s,
      find_finfo ge f = Some fi ->
      list_norepet (var_names fi.(fi_args)) ->
      list_disjoint (var_names fi.(fi_args)) (var_names fi.(fi_locals)) ->
      castl args (type_of_params fi.(fi_args)) vas ->
      bind_parameter_temps fi.(fi_args) vas (create_undef_temps fi.(fi_locals)) = Some s ->
      fun_init_ ge f args s.

Inductive fun_ret_ (ge: genv) (f: fid): option val -> option val -> Prop :=
  | fun_ret_some: forall vx vx' fi,
      find_finfo ge f = Some fi ->
      val_cast vx fi.(fi_return) = Some vx' ->
      fun_ret_ ge f (Some vx) (Some (vx', Tvoid))
  | fun_ret_none: forall fi,
      find_finfo ge f = Some fi ->
      fun_ret_ ge f None None.

Function find_func_ (ge: genv) (f: ident) :=
  match find_finfo ge f with
  | Some fi => Some fi.(fi_body)
  | None => None
  end.

Global Instance QCSem: BaseSem genv lval val mem stack QCSyn := {
  find_func := find_func_;
  (* values *)
  val_bool := fun vb b => bool_val (fst vb) (snd vb) = Some b;
  (* memory operations *)
  mem_set := mem_set_;
  stack_set := stack_set_;
  (* functions *)
  fun_init := fun_init_;
  fun_ret := fun_ret_;
  (* expressions *)
  leva := fun ge c e v => leva_expr ge c e (fst v) /\ snd v = typeof e;
  eval := fun ge c e v => eval_expr ge c e (fst v) /\ snd v = typeof e
}.

Definition trevent (e: Core.event) :=
  match e with
  | ecall f => Event_call f
  | eret f => Event_return f
  end.
Definition trtrace := map trevent.

Definition program := AST.program finfo type.
Inductive state: Type :=
  | Initial (main: finfo) (m: mem)
  | Running (main: finfo) (s: Core.stm) (k: Core.cont) (c: Core.conf)
  | Final (code: int).

Inductive step (ge: genv): state -> trace -> state -> Prop :=

  | step_start:
      forall m s main,
      fun_init ge main.(fi_name) nil s ->
      step ge
        (Initial main m) (Event_call main.(fi_name) :: nil)
        (Running main main.(fi_body) kstop (cnf s m))

  | step_core:
      forall main s1 k1 c1 s2 k2 c2 t
             (SEMKSTEP: Core.step ge (s1, k1, c1) t (s2, k2, c2)),
      step ge
        (Running main s1 k1 c1) (trtrace t)
        (Running main s2 k2 c2)

  | step_stop:
      forall main r c code ty
             (RETEVAL: ret_eval ge c main.(fi_name) r (Some (Vint code, ty))),
      step ge
        (Running main (sret r) kstop c) (Event_return main.(fi_name) :: nil)
        (Final code).

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro:
      forall main m0,
      let ge := Genv.globalenv p in
      Genv.init_mem p = Some m0 ->
      find_finfo ge p.(prog_main) = Some main ->
      main.(fi_args) = nil ->
      main.(fi_return) = type_int32s ->
      initial_state p (Initial main m0).

Inductive final_state: state -> int -> Prop :=
  | final_state_intro:
      forall code, final_state (Final code) code.

Definition semantics (p: program) :=
  Semantics step (initial_state p) final_state (Genv.globalenv p).

(* Cxlight is receptive to change in events *)
Lemma semantics_receptive:
  forall (p: program), receptive (semantics p).
Proof.
Ltac done := eexists; econstructor; now eauto.

intros. constructor; simpl; intros.
inv H.
  (* step_start *)
  inv H0; done.
  (* step_core *)
  assert (t = T0 -> exists s2, step (Genv.globalenv p) (Running main s0 k1 c1) t2 s2).
  { intros. subst. inv H0.
    change nil with (trtrace T0); done. }
  inversion SEMKSTEP; subst; auto.
    (* return *)
    inv H0.
    change (Event_return kf :: nil)
      with (trtrace (T1 (eret kf))); done.
    (* call *)
    inv H0.
    change (Event_call f :: nil)
      with (trtrace (T1 (ecall f))); done.
  (* step_stop *)
  inv H0; done.

(* single_events (semantics p) *)
red; intros. inv H; simpl; try omega.
inv SEMKSTEP; simpl; try omega.
Qed.
