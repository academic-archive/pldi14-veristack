(************************************************************************)
(*                                                                      *)
(*                Quantitative Hoare Logic for Clight                   *)
(*                                                                      *)
(*  Author: Quentin Carbonneaux (c) 2014              Yale University   *)
(*                                                                      *)
(************************************************************************)


(* Simple imperative abstract language. *)

Class BaseSyn (fid var expr: Type) :=
  { fid_eq: forall (f f': fid), { f = f' } + { f <> f' } }.

(* traces *)
Section TRACES.

Inductive event `{Syn: BaseSyn}: Type :=
  | ecall (f: fid)
  | eret (f: fid).

Context `{Syn: BaseSyn}.
Definition trace := list event.

Definition T0: trace := nil.
Definition T1 e: trace := cons e nil.
Definition Tapp (t1 t2: trace): trace := app t1 t2.

Lemma T0_left: forall t, Tapp T0 t = t.
Proof (fun _ => eq_refl).
End TRACES.


(* Clight like syntax *)
Inductive stm `{Syn: BaseSyn}: Type :=
  | sskip
  | sgset (x: expr) (y: expr)
  | slset (v: var) (x: expr)
  | sret (r: option expr)
  | sbreak
  | scall (v: option var) (f: fid) (l: list expr)
  | sseq (s1 s2: stm)
  | sif (b: expr) (st sf: stm)
  | sloop (s: stm).


Inductive conf_ {S M: Type}: Type := cnf (s: S) (m: M).
Definition c_stack {S M: Type} (c: @conf_ S M) :=
  match c with cnf s _ => s end.
Definition c_mem {S M: Type} (c: @conf_ S M) :=
  match c with cnf _ m => m end.


(* This typeclass define the primitive operations that
 * are needed to give a semantics to the Core language,
 * they can be instantiated by anything, the actual
 * instantiation that we use is defined in Cxlight.v.
 *)
Class BaseSem (genv lval val mem stack: Type) `(Syn: BaseSyn) :=

  (* global env *)
  { find_func: genv -> fid -> option stm

  (* values *)
  ; val_bool: val -> bool -> Prop

  (* memory *)
  ; conf: Type := @conf_ stack mem
  ; mem_set: genv -> lval -> val -> mem -> mem -> Prop
  ; stack_set: genv -> var -> val -> stack -> stack -> Prop

  (* functions *)
  ; fun_init: genv -> fid -> list val -> stack -> Prop
  ; fun_ret: genv -> fid -> option val -> option val -> Prop

  (* expressions *)
  ; leva: genv -> conf -> expr -> lval -> Prop
  ; eval: genv -> conf -> expr -> val -> Prop
  }.

(* continuation based semantics of programs *)
Section SEMANTICS.
Inductive cont `{Sem: BaseSem}: Type :=
  | kcall (v: option var) (f: fid) (stk: stack) (k: cont)
  | kseq (s: stm) (k: cont)
  | kloop (s: stm) (k: cont)
  | kstop.

Context `{Sem: BaseSem}.

Definition stack_seto (ge: genv) (vo: option var) (vx: val) (s s': stack): Prop :=
  match vo with
  | Some v => stack_set ge v vx s s'
  | None => s = s'
  end.

Inductive evall (ge: genv) (c: conf): list expr -> list val -> Prop :=
  | evall_nil: evall ge c nil nil
  | evall_cons: forall e v es vs,
      eval ge c e v ->
      evall ge c es vs ->
      evall ge c (cons e es) (cons v vs).

Section STEP.
Variable ge: genv.

(* Evaluation of the return value of a given function. *)
Inductive ret_eval (c: conf) (f: fid): option expr -> option val -> Prop :=

  | ret_eval_some: forall r vr vr',
      eval ge c r vr ->
      fun_ret ge f (Some vr) (Some vr') ->
      ret_eval c f (Some r) (Some vr')

  | ret_eval_none:
      fun_ret ge f None None ->
      ret_eval c f None None.

(* Caller's stack modification made after a return. *)
Inductive ret_stack: option var -> option val -> stack -> stack -> Prop :=

  | ret_stack_some: forall kv vr' ks ks',
      stack_seto ge kv vr' ks ks' ->
      ret_stack kv (Some vr') ks ks'

  | ret_stack_none: forall ks,
      ret_stack None None ks ks.

(* Small step semantics for the Core language. *)
Inductive step: (stm * cont * conf) -> trace -> (stm * cont * conf) -> Prop :=

  | step_gset: forall x lx y vy k c m,
      leva ge c x lx ->
      eval ge c y vy ->
      mem_set ge lx vy (c_mem c) m ->
      step (sgset x y, k, c) T0
           (sskip, k, cnf (c_stack c) m)

  | step_lset: forall v x vx k c s,
      eval ge c x vx ->
      stack_set ge v vx (c_stack c) s ->
      step (slset v x, k, c) T0
           (sskip, k, cnf s (c_mem c))

  | step_ret_call: forall r vr' kf kv ks k c ks',
      ret_eval c kf r vr' ->
      ret_stack kv vr' ks ks' ->
      step (sret r, kcall kv kf ks k, c) (T1 (eret kf))
           (sskip, k, cnf ks' (c_mem c))
  | step_ret_seq: forall r s k c,
      step (sret r, kseq s k, c) T0
           (sret r, k, c)
  | step_ret_loop: forall r s k c,
      step (sret r, kloop s k, c) T0
           (sret r, k, c)

  | step_break_loop: forall s k c,
      step (sbreak, kloop s k, c) T0
           (sskip, k, c)
  | step_break_seq: forall s k c,
      step (sbreak, kseq s k, c) T0
           (sbreak, k, c)

  | step_call: forall v f l vl bdy k c s,
      find_func ge f = Some bdy ->
      evall ge c l vl ->
      fun_init ge f vl s ->
      step (scall v f l, k, c) (T1 (ecall f))
           (bdy, kcall v f (c_stack c) k, cnf s (c_mem c))

  | step_skip_seq: forall s k c,
      step (sskip, kseq s k, c) T0
           (s, k, c)
  | step_seq: forall s1 s2 k c,
      step (sseq s1 s2, k, c) T0
           (s1, kseq s2 k, c)

  | step_if: forall t vt b st sf k c,
      eval ge c t vt ->
      val_bool vt b ->
      step (sif t st sf, k, c) T0
           (if b then st else sf, k, c)

  | step_skip_loop: forall s k c,
      step (sskip, kloop s k, c) T0
           (sloop s, k, c)
  | step_kloop: forall s k c,
      step (sloop s, k, c) T0
           (s, kloop s k, c).
End STEP.
End SEMANTICS.
