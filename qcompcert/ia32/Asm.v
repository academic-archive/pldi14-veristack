(* *********************************************************************)
(*                                                                     *)
(*             The Quantitative CompCert verified compiler             *)
(*                                                                     *)
(*                 Tahina Ramananandro, Yale University                *)
(*                                                                     *)
(*  This file is a modified version of the                             *)
(*  CompCert 1.13 verified compiler by Xavier Leroy, INRIA.            *)
(*  The CompCert verified compiler is                                  *)
(*  Copyright Institut National de Recherche en Informatique et en     *)
(*  Automatique.  All rights reserved.  The original file is           *)
(*  distributed                                                        *)
(*  under the terms of the INRIA Non-Commercial License Agreement.     *)
(*  According to this license, this modified version is distributed    *)
(*  under a similar license (see LICENSE for details).                 *)
(*                                                                     *)
(* *********************************************************************)

(** Abstract syntax and semantics for IA32 assembly language *)

(** The difference from the genuine CompCert is that the stack is now
a single block for the whole program. There is no need for special
stack-handling pseudo-instructions anymore. *)

Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Values.
Require Import Memory.
Require Import Events.
Require Import Globalenvs.
Require Import Smallstep.
Require Import Locations.
Require Import Stacklayout.
Require Import Conventions.

(** * Abstract syntax *)

(** ** Registers. *)

(** Integer registers. *)

Inductive ireg: Type :=
  | EAX: ireg  | EBX: ireg  | ECX: ireg  | EDX: ireg
  | ESI: ireg  | EDI: ireg  | EBP: ireg  | ESP: ireg.

(** Floating-point registers, i.e. SSE2 registers *)

Inductive freg: Type :=
  | XMM0: freg  | XMM1: freg  | XMM2: freg  | XMM3: freg
  | XMM4: freg  | XMM5: freg  | XMM6: freg  | XMM7: freg.

Lemma ireg_eq: forall (x y: ireg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

Lemma freg_eq: forall (x y: freg), {x=y} + {x<>y}.
Proof. decide equality. Defined.

(** Bits of the flags register.  [SOF] is a pseudo-bit representing
  the "xor" of the [OF] and [SF] bits. *)

Inductive crbit: Type := 
  | ZF | CF | PF | SOF.

(** All registers modeled here. *)

Inductive preg: Type :=
  | PC: preg                            (**r program counter *)
  | IR: ireg -> preg                    (**r integer register *)
  | FR: freg -> preg                    (**r XMM register *)
  | ST0: preg                           (**r top of FP stack *)
  | CR: crbit -> preg                   (**r bit of the flags register *)
(*  | RA: preg ---  pseudo-reg representing return address NO LONGER needed *)
.

Coercion IR: ireg >-> preg.
Coercion FR: freg >-> preg.
Coercion CR: crbit >-> preg.

(** Conventional names for stack pointer ([SP]) and return address ([RA]) *)

Notation SP := ESP (only parsing).

(** ** Instruction set. *)

Definition label := positive.

(** General form of an addressing mode. *)

Inductive addrmode: Type :=
  | Addrmode (base: option ireg)
             (ofs: option (ireg * int))
             (const: int + ident * int).

(** Testable conditions (for conditional jumps and more). *)

Inductive testcond: Type :=
  | Cond_e | Cond_ne
  | Cond_b | Cond_be | Cond_ae | Cond_a
  | Cond_l | Cond_le | Cond_ge | Cond_g
  | Cond_p | Cond_np.

(** Instructions.  IA32 instructions accept many combinations of
  registers, memory references and immediate constants as arguments.
  Here, we list only the combinations that we actually use.

  Naming conventions:
- [r]: integer register operand
- [f]: XMM register operand
- [m]: memory operand
- [i]: immediate integer operand
- [s]: immediate symbol operand
- [l]: immediate label operand
- [cl]: the [CL] register

  For two-operand instructions, the first suffix describes the result
  (and first argument), the second suffix describes the second argument.
*)

Inductive instruction: Type :=
  (** Moves *)
  | Pmov_rr (rd: ireg) (r1: ireg)       (**r [mov] (32-bit int) *)
  | Pmov_ri (rd: ireg) (n: int)
  | Pmov_ra (rd: ireg) (id: ident) 
  | Pmov_rm (rd: ireg) (a: addrmode)
  | Pmov_mr (a: addrmode) (rs: ireg)
  | Pmovd_fr (rd: freg) (r1: ireg)      (**r [movd] (32-bit int) *)
  | Pmovd_rf (rd: ireg) (rd: freg)
  | Pmovsd_ff (rd: freg) (r1: freg)     (**r [movsd] (single 64-bit float) *)
  | Pmovsd_fi (rd: freg) (n: float)     (**r (pseudo-instruction) *)
  | Pmovsd_fm (rd: freg) (a: addrmode)
  | Pmovsd_mf (a: addrmode) (r1: freg)
  | Pfld_f (r1: freg)                   (**r [fld] from XMM register (pseudo) *)
  | Pfld_m (a: addrmode)                (**r [fld] from memory *)
  | Pfstp_f (rd: freg)                  (**r [fstp] to XMM register (pseudo) *)
  | Pfstp_m (a: addrmode)               (**r [fstp] to memory *)
  | Pxchg_rr (r1: ireg) (r2: ireg)      (**r register-register exchange *)
  (** Moves with conversion *)
  | Pmovb_mr (a: addrmode) (rs: ireg)   (**r [mov] (8-bit int) *)
  | Pmovw_mr (a: addrmode) (rs: ireg)   (**r [mov] (16-bit int) *)
  | Pmovzb_rr (rd: ireg) (rs: ireg)    (**r [movzb] (8-bit zero-extension) *)
  | Pmovzb_rm (rd: ireg) (a: addrmode)
  | Pmovsb_rr (rd: ireg) (rs: ireg)    (**r [movsb] (8-bit sign-extension) *)
  | Pmovsb_rm (rd: ireg) (a: addrmode)
  | Pmovzw_rr (rd: ireg) (rs: ireg)    (**r [movzw] (16-bit zero-extension) *)
  | Pmovzw_rm (rd: ireg) (a: addrmode)
  | Pmovsw_rr (rd: ireg) (rs: ireg)    (**r [movsw] (16-bit sign-extension) *)
  | Pmovsw_rm (rd: ireg) (a: addrmode)
  | Pcvtss2sd_fm (rd: freg) (a: addrmode) (**r [cvtss2sd] (single float load) *)
  | Pcvtsd2ss_ff (rd: freg) (r1: freg) (**r pseudo (single conversion) *)
  | Pcvtsd2ss_mf (a: addrmode) (r1: freg) (**r [cvtsd2ss] (single float store) *)
  | Pcvttsd2si_rf (rd: ireg) (r1: freg) (**r double to signed int *)
  | Pcvtsi2sd_fr (rd: freg) (r1: ireg)  (**r signed int to double *)
  (** Integer arithmetic *)
  | Plea (rd: ireg) (a: addrmode)
  | Pneg (rd: ireg)
  | Psub_rr (rd: ireg) (r1: ireg)
  | Pimul_rr (rd: ireg) (r1: ireg)
  | Pimul_ri (rd: ireg) (n: int)
  | Pdiv (r1: ireg)
  | Pidiv (r1: ireg)
  | Pand_rr (rd: ireg) (r1: ireg)
  | Pand_ri (rd: ireg) (n: int)
  | Por_rr (rd: ireg) (r1: ireg)
  | Por_ri (rd: ireg) (n: int)
  | Pxor_r (rd: ireg)                  (**r [xor] with self = set to zero *)
  | Pxor_rr (rd: ireg) (r1: ireg)
  | Pxor_ri (rd: ireg) (n: int)
  | Psal_rcl (rd: ireg)
  | Psal_ri (rd: ireg) (n: int)
  | Pshr_rcl (rd: ireg)
  | Pshr_ri (rd: ireg) (n: int)
  | Psar_rcl (rd: ireg)
  | Psar_ri (rd: ireg) (n: int)
  | Pror_ri (rd: ireg) (n: int)
  | Pcmp_rr (r1 r2: ireg) 
  | Pcmp_ri (r1: ireg) (n: int)
  | Ptest_rr (r1 r2: ireg)
  | Ptest_ri (r1: ireg) (n: int)
  | Pcmov (c: testcond) (rd: ireg) (r1: ireg)
  | Psetcc (c: testcond) (rd: ireg)
  (** Floating-point arithmetic *)
  | Paddd_ff (rd: freg) (r1: freg)
  | Psubd_ff (rd: freg) (r1: freg)
  | Pmuld_ff (rd: freg) (r1: freg)
  | Pdivd_ff (rd: freg) (r1: freg)
  | Pnegd (rd: freg)
  | Pabsd (rd: freg)
  | Pcomisd_ff (r1 r2: freg)
  | Pxorpd_f (rd: freg)	              (**r [xor] with self = set to zero *)
  (** Branches and calls *)
  | Pjmp_l (l: label)
  | Pjmp_s (symb: ident)
  | Pjmp_r (r: ireg)
  | Pjcc (c: testcond)(l: label)
  | Pjcc2 (c1 c2: testcond)(l: label)
  | Pjmptbl (r: ireg) (tbl: list label) (**r pseudo *)
  | Pcall_s (symb: ident)
  | Pcall_r (r: ireg)
  | Pret
  (** Pseudo-instructions *)
  | Plabel(l: label)
  | Pbuiltin(ef: external_function)(args: list preg)(res: preg)
  | Pannot(ef: external_function)(args: list annot_param)
(** NOTE: The [Pallocframe] and [Pfreeframe] pseudo instructions for handling stack frames disappeared. The stack is now a single block for the whole program, as in [Mach2]. *)

with annot_param : Type :=
  | APreg: preg -> annot_param
  | APstack: memory_chunk -> Z -> annot_param.

Definition code := list instruction.
Definition function := code.
Definition fn_code (f: function) : code := f.
Definition fundef := AST.fundef code.
Definition program := AST.program fundef unit.

(** * Operational semantics *)

Lemma preg_eq: forall (x y: preg), {x=y} + {x<>y}.
Proof. decide equality. apply ireg_eq. apply freg_eq. decide equality. Defined.

Module PregEq.
  Definition t := preg.
  Definition eq := preg_eq.
End PregEq.

Module Pregmap := EMap(PregEq).

Definition regset := Pregmap.t val.
Definition genv := Genv.t fundef unit.

Notation "a # b" := (a b) (at level 1, only parsing).
Notation "a # b <- c" := (Pregmap.set b c a) (at level 1, b at next level).

(** Undefining some registers *)

Fixpoint undef_regs (l: list preg) (rs: regset) : regset :=
  match l with
  | nil => rs
  | r :: l' => undef_regs l' (rs#r <- Vundef)
  end.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)

Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end.

(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl l); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.

Variable ge: genv.

Definition symbol_offset (id: ident) (ofs: int) : val :=
  match Genv.find_symbol ge id with
  | Some b => Vptr b ofs
  | None => Vundef
  end.

(** Evaluating an addressing mode *)

Definition eval_addrmode (a: addrmode) (rs: regset) : val :=
  match a with Addrmode base ofs const =>
    Val.add (match base with
              | None => Vzero
              | Some r => rs r
             end)
    (Val.add (match ofs with
              | None => Vzero
              | Some(r, sc) =>
                  if Int.eq sc Int.one then rs r else Val.mul (rs r) (Vint sc)
              end)
             (match const with
              | inl ofs => Vint ofs
              | inr(id, ofs) => symbol_offset id ofs
              end))
  end.

(** Performing a comparison *)

(** Integer comparison between x and y:
-       ZF = 1 if x = y, 0 if x != y
-       CF = 1 if x <u y, 0 if x >=u y
-       SOF = 1 if x <s y, 0 if x >=s y
-       PF is undefined

SOF is (morally) the XOR of the SF and OF flags of the processor. *)

Definition compare_ints (x y: val) (rs: regset) (m: mem): regset :=
  rs #ZF  <- (Val.cmpu (Mem.valid_pointer m) Ceq x y)
     #CF  <- (Val.cmpu (Mem.valid_pointer m) Clt x y)
     #SOF <- (Val.cmp Clt x y)
     #PF  <- Vundef.

(** Floating-point comparison between x and y:
-       ZF = 1 if x=y or unordered, 0 if x<>y
-       CF = 1 if x<y or unordered, 0 if x>=y
-       PF = 1 if unordered, 0 if ordered.
-       SOF is undefined
*)

Definition compare_floats (vx vy: val) (rs: regset) : regset :=
  match vx, vy with
  | Vfloat x, Vfloat y =>
      rs #ZF  <- (Val.of_bool (negb (Float.cmp Cne x y)))
         #CF  <- (Val.of_bool (negb (Float.cmp Cge x y)))
         #PF  <- (Val.of_bool (negb (Float.cmp Ceq x y || Float.cmp Clt x y || Float.cmp Cgt x y)))
         #SOF <- Vundef
  | _, _ =>
      undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: nil) rs
  end.

(** Testing a condition *)

Definition eval_testcond (c: testcond) (rs: regset) : option bool :=
  match c with
  | Cond_e =>
      match rs ZF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_ne =>
      match rs ZF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | Cond_b =>
      match rs CF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_be =>
      match rs CF, rs ZF with
      | Vint c, Vint z => Some (Int.eq c Int.one || Int.eq z Int.one)
      | _, _ => None
      end
  | Cond_ae =>
      match rs CF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | Cond_a =>
      match rs CF, rs ZF with
      | Vint c, Vint z => Some (Int.eq c Int.zero && Int.eq z Int.zero)
      | _, _ => None
      end
  | Cond_l =>
      match rs SOF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_le =>
      match rs SOF, rs ZF with
      | Vint s, Vint z => Some (Int.eq s Int.one || Int.eq z Int.one)
      | _, _ => None
      end
  | Cond_ge =>
      match rs SOF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  | Cond_g =>
      match rs SOF, rs ZF with
      | Vint s, Vint z => Some (Int.eq s Int.zero && Int.eq z Int.zero)
      | _, _ => None
      end
  | Cond_p =>
      match rs PF with
      | Vint n => Some (Int.eq n Int.one)
      | _ => None
      end
  | Cond_np =>
      match rs PF with
      | Vint n => Some (Int.eq n Int.zero)
      | _ => None
      end
  end.

(** The semantics is purely small-step and defined as a function
  from the current state (a register set + a memory state)
  to either [Next rs' m'] where [rs'] and [m'] are the updated register
  set and memory state after execution of the instruction at [rs#PC],
  or [Stuck] if the processor is stuck. *)

Inductive outcome: Type :=
  | Next: regset -> mem -> outcome
  | Stuck: outcome.

(** Manipulations over the [PC] register: continuing with the next
  instruction ([nextinstr]) or branching to a label ([goto_label]).
  [nextinstr_nf] is a variant of [nextinstr] that sets condition flags
  to [Vundef] in addition to incrementing the [PC]. *)

Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.add rs#PC Vone).

Definition nextinstr_nf (rs: regset) : regset :=
  nextinstr (undef_regs (CR ZF :: CR CF :: CR PF :: CR SOF :: nil) rs).

Definition goto_label (c: code) (lbl: label) (rs: regset) (m: mem) :=
  match label_pos lbl 0 c with
  | None => Stuck
  | Some pos =>
      match rs#PC with
      | Vptr b ofs => Next (rs#PC <- (Vptr b (Int.repr pos))) m
      | _ => Stuck
    end
  end.

(** Auxiliaries for memory accesses. *)

Definition exec_load (chunk: memory_chunk) (m: mem)
                     (a: addrmode) (rs: regset) (rd: preg) :=
  match Mem.loadv chunk m (eval_addrmode a rs) with
  | Some v => Next (nextinstr_nf (rs#rd <- v)) m
  | None => Stuck
  end.

Definition exec_store (chunk: memory_chunk) (m: mem)
                      (a: addrmode) (rs: regset) (r1: preg) :=
  match Mem.storev chunk m (eval_addrmode a rs) (rs r1) with
  | Some m' => Next (nextinstr_nf (if preg_eq r1 ST0 then rs#ST0 <- Vundef else rs)) m'
  | None => Stuck
  end.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual IA32 instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the IA32 reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above.  

    Note that we set to [Vundef] the registers used as temporaries by
    the expansions of the pseudo-instructions, so that the IA32 code
    we generate cannot use those registers to hold values that must
    survive the execution of the pseudo-instruction.

    Concerning condition flags, the comparison instructions set them
    accurately; other instructions (moves, [lea]) preserve them;
    and all other instruction set those flags to [Vundef], to reflect
    the fact that the processor updates some or all of those flags,
    but we do not need to model this precisely.
*)

Definition exec_instr (c: code) (i: instruction) (rs: regset) (m: mem) : outcome :=
  match i with
  (** Moves *)
  | Pmov_rr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmov_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Vint n))) m
  | Pmov_ra rd id =>
      Next (nextinstr_nf (rs#rd <- (symbol_offset id Int.zero))) m
  | Pmov_rm rd a =>
      exec_load Mint32 m a rs rd
  | Pmov_mr a r1 =>
      exec_store Mint32 m a rs r1
  | Pmovd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovd_rf rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovsd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (rs r1))) m
  | Pmovsd_fi rd n =>
      Next (nextinstr (rs#rd <- (Vfloat n))) m
  | Pmovsd_fm rd a =>
      exec_load Mfloat64al32 m a rs rd
  | Pmovsd_mf a r1 =>
      exec_store Mfloat64al32 m a rs r1
  | Pfld_f r1 =>
      Next (nextinstr (rs#ST0 <- (rs r1))) m
  | Pfld_m a =>
      exec_load Mfloat64al32 m a rs ST0
  | Pfstp_f rd =>
      Next (nextinstr (rs#rd <- (rs ST0) #ST0 <- Vundef)) m
  | Pfstp_m a =>
      exec_store Mfloat64al32 m a rs ST0
  | Pxchg_rr r1 r2 =>
      Next (nextinstr (rs#r1 <- (rs r2) #r2 <- (rs r1))) m
  (** Moves with conversion *)
  | Pmovb_mr a r1 =>
      exec_store Mint8unsigned m a rs r1
  | Pmovw_mr a r1 =>
      exec_store Mint16unsigned m a rs r1
  | Pmovzb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 8 rs#r1))) m
  | Pmovzb_rm rd a =>
      exec_load Mint8unsigned m a rs rd
  | Pmovsb_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 8 rs#r1))) m
  | Pmovsb_rm rd a =>
      exec_load Mint8signed m a rs rd
  | Pmovzw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.zero_ext 16 rs#r1))) m
  | Pmovzw_rm rd a =>
      exec_load Mint16unsigned m a rs rd
  | Pmovsw_rr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.sign_ext 16 rs#r1))) m
  | Pmovsw_rm rd a =>
      exec_load Mint16signed m a rs rd
  | Pcvtss2sd_fm rd a =>
      exec_load Mfloat32 m a rs rd
  | Pcvtsd2ss_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.singleoffloat rs#r1))) m
  | Pcvtsd2ss_mf a r1 =>
      exec_store Mfloat32 m a rs r1
  | Pcvttsd2si_rf rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.intoffloat rs#r1)))) m
  | Pcvtsi2sd_fr rd r1 =>
      Next (nextinstr (rs#rd <- (Val.maketotal (Val.floatofint rs#r1)))) m
  (** Integer arithmetic *)
  | Plea rd a =>
      Next (nextinstr (rs#rd <- (eval_addrmode a rs))) m
  | Pneg rd =>
      Next (nextinstr_nf (rs#rd <- (Val.neg rs#rd))) m
  | Psub_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.sub rs#rd rs#r1))) m
  | Pimul_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd rs#r1))) m
  | Pimul_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.mul rs#rd (Vint n)))) m
  | Pdiv r1 =>
      let vn := rs#EAX in let vd := (rs#EDX <- Vundef)#r1 in
      match Val.divu vn vd, Val.modu vn vd with
      | Some vq, Some vr => Next (nextinstr_nf (rs#EAX <- vq #EDX <- vr)) m
      | _, _ => Stuck
      end
  | Pidiv r1 =>
      let vn := rs#EAX in let vd := (rs#EDX <- Vundef)#r1 in
      match Val.divs vn vd, Val.mods vn vd with
      | Some vq, Some vr => Next (nextinstr_nf (rs#EAX <- vq #EDX <- vr)) m
      | _, _ => Stuck
      end
  | Pand_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd rs#r1))) m
  | Pand_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.and rs#rd (Vint n)))) m
  | Por_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd rs#r1))) m
  | Por_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.or rs#rd (Vint n)))) m
  | Pxor_r rd =>
      Next (nextinstr_nf (rs#rd <- Vzero)) m
  | Pxor_rr rd r1 =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd rs#r1))) m
  | Pxor_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.xor rs#rd (Vint n)))) m
  | Psal_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd rs#ECX))) m
  | Psal_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shl rs#rd (Vint n)))) m
  | Pshr_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd rs#ECX))) m
  | Pshr_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shru rs#rd (Vint n)))) m
  | Psar_rcl rd =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd rs#ECX))) m
  | Psar_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.shr rs#rd (Vint n)))) m
  | Pror_ri rd n =>
      Next (nextinstr_nf (rs#rd <- (Val.ror rs#rd (Vint n)))) m
  | Pcmp_rr r1 r2 =>
      Next (nextinstr (compare_ints (rs r1) (rs r2) rs m)) m
  | Pcmp_ri r1 n =>
      Next (nextinstr (compare_ints (rs r1) (Vint n) rs m)) m
  | Ptest_rr r1 r2 =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (rs r2)) Vzero rs m)) m
  | Ptest_ri r1 n =>
      Next (nextinstr (compare_ints (Val.and (rs r1) (Vint n)) Vzero rs m)) m
  | Pcmov c rd r1 =>
      match eval_testcond c rs with
      | Some true => Next (nextinstr (rs#rd <- (rs#r1))) m
      | Some false => Next (nextinstr rs) m
      | None => Next (nextinstr (rs#rd <- Vundef)) m
      end
  | Psetcc c rd =>
      Next (nextinstr (rs#ECX <- Vundef #rd <- (Val.of_optbool (eval_testcond c rs)))) m
  (** Arithmetic operations over floats *)
  | Paddd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.addf rs#rd rs#r1))) m
  | Psubd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.subf rs#rd rs#r1))) m
  | Pmuld_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.mulf rs#rd rs#r1))) m
  | Pdivd_ff rd r1 =>
      Next (nextinstr (rs#rd <- (Val.divf rs#rd rs#r1))) m
  | Pnegd rd =>
      Next (nextinstr (rs#rd <- (Val.negf rs#rd))) m
  | Pabsd rd =>
      Next (nextinstr (rs#rd <- (Val.absf rs#rd))) m
  | Pcomisd_ff r1 r2 =>
      Next (nextinstr (compare_floats (rs r1) (rs r2) rs)) m
  | Pxorpd_f rd =>
      Next (nextinstr_nf (rs#rd <- (Vfloat Float.zero))) m
  (** Branches and calls *)
  | Pjmp_l lbl =>
      goto_label c lbl rs m
  | Pjmp_s id =>
      Next (rs#PC <- (symbol_offset id Int.zero)) m
  | Pjmp_r r =>
      Next (rs#PC <- (rs r)) m
  | Pjcc cond lbl =>
      match eval_testcond cond rs with
      | Some true => goto_label c lbl rs m
      | Some false => Next (nextinstr rs) m
      | None => Stuck
      end
  | Pjcc2 cond1 cond2 lbl =>
      match eval_testcond cond1 rs, eval_testcond cond2 rs with
      | Some true, Some true => goto_label c lbl rs m
      | Some _, Some _ => Next (nextinstr rs) m
      | _, _ => Stuck
      end
  | Pjmptbl r tbl =>
      match rs#r with
      | Vint n => 
          match list_nth_z tbl (Int.unsigned n) with
          | None => Stuck
          | Some lbl => goto_label c lbl (rs #ECX <- Vundef #EDX <- Vundef) m
          end
      | _ => Stuck
      end
  | Pcall_s id =>
      match Mem.storev Mint32 m (Val.sub (rs#ESP) (Vint (Int.repr (size_chunk Mint32)))) (Val.add rs#PC Vone) with
        | Some m' => Next (rs # ESP <- (Val.sub (rs#ESP) (Vint (Int.repr (size_chunk Mint32))))
                              # PC <- (symbol_offset id Int.zero)) m'
        | _ => Stuck
      end
  | Pcall_r r =>
      match Mem.storev Mint32 m (Val.sub (rs#ESP) (Vint (Int.repr (size_chunk Mint32)))) (Val.add rs#PC Vone) with
        | Some m' => Next (rs # ESP <- (Val.sub (rs#ESP) (Vint (Int.repr (size_chunk Mint32))))
                              # PC <- (rs r)) m'
        | _ => Stuck
      end
  | Pret =>
    (* Next (rs # PC <- Vzero) m *)
    match Mem.loadv Mint32 m (rs#ESP) with
      | Some v => Next (rs # ESP <- (Val.add (rs#ESP) (Vint (Int.repr (size_chunk Mint32)))) # PC <- v) m
      | _ => Stuck
    end
  (** Pseudo-instructions *)
  | Plabel lbl =>
      Next (nextinstr rs) m
  | Pbuiltin ef args res =>
      Stuck                             (**r treated specially below *)
  | Pannot ef args =>
      Stuck                             (**r treated specially below *)
  end.

(** Translation of the LTL/Linear/Mach view of machine registers
  to the Asm view.  *)

Definition preg_of (r: mreg) : preg :=
  match r with
  | AX => IR EAX
  | BX => IR EBX
  | SI => IR ESI
  | DI => IR EDI
  | BP => IR EBP
  | X0 => FR XMM0
  | X1 => FR XMM1
  | X2 => FR XMM2
  | X3 => FR XMM3
  | X4 => FR XMM4
  | X5 => FR XMM5
  | IT1 => IR EDX
  | IT2 => IR ECX
  | FT1 => FR XMM6
  | FT2 => FR XMM7
  | FP0 => ST0
  end.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use machine registers instead of locations. *)

Inductive extcall_arg (rs: regset) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_int_stack: forall ofs bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv Mint32 m (Val.add (rs (IR ESP)) (Vint (Int.repr bofs))) = Some v ->
      extcall_arg rs m (S (Outgoing ofs Tint)) v
  | extcall_arg_float_stack: forall ofs bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv Mfloat64al32 m (Val.add (rs (IR ESP)) (Vint (Int.repr bofs))) = Some v ->
      extcall_arg rs m (S (Outgoing ofs Tfloat)) v.

Definition extcall_arguments
    (rs: regset) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : preg :=
  preg_of (loc_result sg).

(** Extract the values of the arguments of an annotation. *)

Inductive annot_arg (rs: regset) (m: mem): annot_param -> val -> Prop :=
  | annot_arg_reg: forall r,
      annot_arg rs m (APreg r) (rs r)
  | annot_arg_stack: forall chunk ofs stk base v,
      rs (IR ESP) = Vptr stk base ->
      Mem.load chunk m stk (Int.unsigned base + ofs) = Some v ->
      annot_arg rs m (APstack chunk ofs) v.

Definition annot_arguments
    (rs: regset) (m: mem) (params: list annot_param) (args: list val) : Prop :=
  list_forall2 (annot_arg rs m) params args.

(** Execution of the instruction at [rs#PC]. *)

Inductive state: Type :=
  | State: regset -> mem -> state.

Inductive step: state -> trace -> state -> Prop :=
  | exec_step_internal:
      forall b ofs c i rs m rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some i ->
      exec_instr c i rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
(*  | exec_step_internal':
      forall b ofs c i rs m t rs' m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some i ->
      exec_instr' c i rs m = Some (t, rs', m') ->
      step (State rs m) t (State rs' m') *)
  | exec_step_builtin:
      forall b ofs c ef args res rs m t v m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some (Pbuiltin ef args res) ->
      external_call ef ge (map rs args) m t v m' ->
      step (State rs m) t
           (State (nextinstr_nf(rs #EDX <- Vundef #ECX <- Vundef
                                #XMM6 <- Vundef #XMM7 <- Vundef
                                #ST0 <- Vundef
                                #res <- v)) m')
  | exec_step_annot:
      forall b ofs c ef args rs m vargs t v m',
      rs PC = Vptr b ofs ->
      Genv.find_funct_ptr ge b = Some (Internal c) ->
      find_instr (Int.unsigned ofs) c = Some (Pannot ef args) ->
      annot_arguments rs m args vargs ->
      external_call ef ge vargs m t v m' ->
      step (State rs m) t
           (State (nextinstr rs) m')
  | exec_step_external:
      forall b ef args res rs m t rs' m',
      rs PC = Vptr b Int.zero ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      external_call ef ge args m t res m' ->
      extcall_arguments (rs # ESP <- (Val.add (rs#ESP) (Vint (Int.repr (size_chunk Mint32))))) m (ef_sig ef) args -> (* add 4 to ESP to cope with return address *)
      rs' = (rs#(loc_external_result (ef_sig ef)) <- res
               #PC <- (Vptr b Int.one) (* Vzero *)) ->
      step (State rs m) t (State rs' m')
  | exec_step_external_return:
      forall b ef rs m rs' m' c,
      rs PC = Vptr b Int.one ->
      Genv.find_funct_ptr ge b = Some (External ef) ->
      exec_instr c Pret rs m = Next rs' m' ->
      step (State rs m) E0 (State rs' m')
(*      
  | exec_step_return: forall rs
                             (HPC: rs PC = Vzero)
                             m v (Hv: Mem.loadv Mint32 m (rs#ESP) = Some v)
                             rs'
                             (Hrs': rs' = (rs # ESP <- (Val.add (rs#ESP) (Vint (Int.repr (size_chunk Mint32)))) # PC <- v)),
                                    step (State rs m) E0 (State rs' m)
*)
.

End RELSEM.

(** Execution of whole programs. *)

Section BOUND.

Variable bound: int.

Inductive initial_state (p: program): state -> Prop :=
  | initial_state_intro: forall m0,
      Genv.init_mem p = Some m0 ->
      forall m'0 stk, Mem.alloc m0 0 (Int.unsigned bound) = (m'0, stk) ->
      let ge := Genv.globalenv p in
      let rs0 :=
        (Pregmap.init Vundef)
        # PC <- (symbol_offset ge p.(prog_main) Int.zero)
        # ESP <- (Vptr stk  bound) in
      initial_state p (State rs0 m'0).

Inductive final_state (p: program): state -> int -> Prop :=
  | final_state_internal: forall b rs z,
      rs#PC = Vptr b z -> forall c,
      Genv.find_funct_ptr (Genv.globalenv p) b = Some (Internal c) ->
      find_instr (Int.unsigned z) c = Some Pret -> forall r,
      rs#EAX = Vint r ->
      rs#ESP = Vptr (Genv.genv_next (Genv.globalenv p)) bound -> forall m,
      Mem.loadv Mint32 m (rs#ESP) = None (* no return address, the stack pointer is at the bottom of the stack *) ->
      final_state p (State rs m) r
  | final_state_external: forall b rs,
      rs#PC = Vptr b Int.one -> forall ef,
      Genv.find_funct_ptr (Genv.globalenv p) b = Some (External ef) -> forall r,
      rs#EAX = Vint r ->
      rs#ESP = Vptr (Genv.genv_next (Genv.globalenv p)) bound -> forall m,
      Mem.loadv Mint32 m (rs#ESP) = None (* no return address, the stack pointer is at the bottom of the stack *) ->
      final_state p (State rs m) r.
      
Definition semantics (p: program) :=
  Semantics step (initial_state p) (final_state p) (Genv.globalenv p).

(** Determinacy of the [Asm] semantics. *)

Remark extcall_arguments_determ:
  forall rs m sg args1 args2,
  extcall_arguments rs m sg args1 -> extcall_arguments rs m sg args2 -> args1 = args2.
Proof.
  intros until m.
  assert (forall ll vl1, list_forall2 (extcall_arg rs m) ll vl1 ->
          forall vl2, list_forall2 (extcall_arg rs m) ll vl2 -> vl1 = vl2).
    induction 1; intros vl2 EA; inv EA.
    auto.
    f_equal; auto. 
    inv H; inv H3; congruence.
  intros. red in H0; red in H1. eauto. 
Qed.

Remark annot_arguments_determ:
  forall rs m params args1 args2,
  annot_arguments rs m params args1 -> annot_arguments rs m params args2 -> args1 = args2.
Proof.
  unfold annot_arguments. intros. revert params args1 H args2 H0. 
  induction 1; intros. 
  inv H0; auto.
  inv H1. decEq; eauto. inv H; inv H4. auto. congruence. 
Qed.

Lemma semantics_determinate: forall p, determinate (semantics p).
Proof.
Ltac Equalities :=
  match goal with
  | [ H1: ?a = ?b, H2: ?a = ?c |- _ ] =>
      rewrite H1 in H2; inv H2; Equalities
  | _ => idtac
  end.
  intros; constructor; simpl; intros.
(* determ *)
  inv H; inv H0; Equalities; try discriminate.
  split. constructor. auto.
  exploit external_call_determ. eexact H4. eexact H11. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (vargs0 = vargs) by (eapply annot_arguments_determ; eauto). subst vargs0.
  exploit external_call_determ. eexact H5. eexact H13. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  assert (args0 = args) by (eapply extcall_arguments_determ; eauto). subst args0.
  exploit external_call_determ. eexact H3. eexact H8. intros [A B].
  split. auto. intros. destruct B; auto. subst. auto.
  split. constructor. simpl in *. intros; congruence.
(* trace length *)
  red; intros; inv H; simpl.
  omega.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
  eapply external_call_trace_length; eauto.
  omega.
(* initial states *)
  inv H; inv H0. f_equal. unfold rs0, rs1, ge, ge0. congruence.
  congruence.
(* final no step *)
  inv H. red; intros; red; intros. inv H; try congruence.
  replace c0 with c in * by congruence.
  replace z with ofs in * by congruence.
  rewrite H2 in H10.
  inv H10.
  simpl in H13.
  rewrite H5 in H13.
  discriminate.
  
  red; intros; red; intros. inv H; try congruence.
  rewrite H0 in H7. discriminate.
  simpl in H11. rewrite H4 in H11. discriminate.

(* final states *)
  inv H; inv H0; congruence.
Qed.

End BOUND.

(** Classification functions for processor registers (used in Asmgenproof). *)

Definition data_preg (r: preg) : bool :=
  match r with
  | PC => false
  | IR _ => true
  | FR _ => true
  | ST0 => true
  | CR _ => false
  end.

Definition nontemp_preg (r: preg) : bool :=
  match r with
  | PC => false
  | IR ECX => false
  | IR EDX => false
  | IR _ => true
  | FR XMM6 => false
  | FR XMM7 => false
  | FR _ => true
  | ST0 => false
  | CR _ => false
  end.

