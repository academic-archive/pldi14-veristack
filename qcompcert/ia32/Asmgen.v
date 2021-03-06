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

(** Translation from Mach to IA32 Asm. *)

Require Import Coqlib.
Require Import Errors.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Op.
Require Import Locations.
Require Import Mach.
Require Import Asm.

Open Local Scope string_scope.
Open Local Scope error_monad_scope.

(** The code generation functions take advantage of several characteristics of the [Mach] code generated by earlier passes of the compiler:
- Argument and result registers are of the correct type.
- For two-address instructions, the result and the first argument
  are in the same register.  (True by construction in [RTLgen], and preserved by [Reload].)
- The top of the floating-point stack ([ST0], a.k.a. [FP0]) can only
  appear in [mov] instructions, but never in arithmetic instructions.

All these properties are true by construction, but it is painful to track them statically.  Instead, we recheck them during code generation and fail if they do not hold.
*)

(** Extracting integer or float registers. *)

Definition ireg_of (r: mreg) : res ireg :=
  match preg_of r with IR mr => OK mr | _ => Error(msg "Asmgen.ireg_of") end.

Definition freg_of (r: mreg) : res freg :=
  match preg_of r with FR mr => OK mr | _ => Error(msg "Asmgen.freg_of") end.

(** Smart constructors for various operations. *)

Definition mk_mov (rd rs: preg) (k: code) : res code :=
  match rd, rs with
  | IR rd, IR rs => OK (Pmov_rr rd rs :: k)
  | FR rd, FR rs => OK (Pmovsd_ff rd rs :: k)
  | ST0, FR rs => OK (Pfld_f rs :: k)
  | FR rd, ST0 => OK (Pfstp_f rd :: k)
  | _, _ => Error(msg "Asmgen.mk_mov")
  end.

Definition mk_shift (shift_instr: ireg -> instruction)
                    (r1 r2: ireg) (k: code) : res code :=
  if ireg_eq r2 ECX then
    OK (shift_instr r1 :: k)
  else if ireg_eq r1 ECX then
    OK (Pxchg_rr r2 ECX :: shift_instr r2 :: Pxchg_rr r2 ECX :: k)
  else
    OK (Pmov_rr ECX r2 :: shift_instr r1 :: k).

Definition mk_mov2 (src1 dst1 src2 dst2: ireg) (k: code) : code :=
  if ireg_eq src1 dst1 then
    Pmov_rr dst2 src2 :: k
  else if ireg_eq src2 dst2 then
    Pmov_rr dst1 src1 :: k
  else if ireg_eq src2 dst1 then
    if ireg_eq src1 dst2 then
      Pxchg_rr src1 src2 :: k
    else
      Pmov_rr dst2 src2 :: Pmov_rr dst1 src1 :: k
  else
    Pmov_rr dst1 src1 :: Pmov_rr dst2 src2 :: k.

Definition mk_div (div_instr: ireg -> instruction)
                  (r1 r2: ireg) (k: code) : res code :=
  if ireg_eq r1 EAX then
    if ireg_eq r2 EDX then
      OK (Pmov_rr ECX EDX :: div_instr ECX :: k)
    else
      OK (div_instr r2 :: k)
  else
      OK (Pmovd_fr XMM7 EAX ::
          mk_mov2 r1 EAX r2 ECX 
            (div_instr ECX :: Pmov_rr r1 EAX :: Pmovd_rf EAX XMM7 :: k)).

Definition mk_mod (div_instr: ireg -> instruction)
                  (r1 r2: ireg) (k: code) : res code :=
  if ireg_eq r1 EAX then
    if ireg_eq r2 EDX then
      OK (Pmov_rr ECX EDX :: div_instr ECX :: Pmov_rr EAX EDX :: k)
    else
      OK (div_instr r2 :: Pmov_rr EAX EDX :: k)
  else
      OK (Pmovd_fr XMM7 EAX ::
          mk_mov2 r1 EAX r2 ECX 
            (div_instr ECX :: Pmov_rr r1 EDX :: Pmovd_rf EAX XMM7 :: k)).

Definition mk_shrximm (r: ireg) (n: int) (k: code) : res code :=
  let tmp := if ireg_eq r ECX then EDX else ECX in
  let p := Int.sub (Int.shl Int.one n) Int.one in
  OK (Ptest_rr r r ::
      Plea tmp (Addrmode (Some r) None (inl _ p)) ::
      Pcmov Cond_l r tmp ::
      Psar_ri r n :: k).

Definition low_ireg (r: ireg) : bool :=
  match r with
  | EAX | EBX | ECX | EDX => true
  | ESI | EDI | EBP | ESP => false
  end.

Definition mk_intconv (mk: ireg -> ireg -> instruction) (rd rs: ireg) (k: code) :=
  if low_ireg rs then
    OK (mk rd rs :: k)
  else
    OK (Pmov_rr EDX rs :: mk rd EDX :: k).

Definition addressing_mentions (addr: addrmode) (r: ireg) : bool :=
  match addr with Addrmode base displ const =>
      match base with Some r' => ireg_eq r r' | None => false end
   || match displ with Some(r', sc) => ireg_eq r r' | None => false end
  end.

Definition mk_smallstore (sto: addrmode -> ireg ->instruction) 
                         (addr: addrmode) (rs: ireg) (k: code) :=
  if low_ireg rs then
    OK (sto addr rs :: k)
  else if addressing_mentions addr ECX then
    OK (Plea ECX addr :: Pmov_rr EDX rs ::
        sto (Addrmode (Some ECX) None (inl _ Int.zero)) EDX :: k)
  else
    OK (Pmov_rr ECX rs :: sto addr ECX :: k).

(** Accessing slots in the stack frame.  *)

Definition loadind (base: ireg) (ofs: int) (ty: typ) (dst: mreg) (k: code) :=
  match ty with
  | Tint =>
      do r <- ireg_of dst;
      OK (Pmov_rm r (Addrmode (Some base) None (inl _ ofs)) :: k)
  | Tfloat =>
      match preg_of dst with
      | FR r => OK (Pmovsd_fm r (Addrmode (Some base) None (inl _ ofs)) :: k)
      | ST0  => OK (Pfld_m (Addrmode (Some base) None (inl _ ofs)) :: k)
      | _ => Error (msg "Asmgen.loadind")
      end
  end.

Definition storeind (src: mreg) (base: ireg) (ofs: int) (ty: typ) (k: code) :=
  match ty with
  | Tint =>
      do r <- ireg_of src;
      OK (Pmov_mr (Addrmode (Some base) None (inl _ ofs)) r :: k)
  | Tfloat =>
      match preg_of src with
      | FR r => OK (Pmovsd_mf (Addrmode (Some base) None (inl _ ofs)) r :: k)
      | ST0  => OK (Pfstp_m (Addrmode (Some base) None (inl _ ofs)) :: k)
      | _ => Error (msg "Asmgen.loadind")
      end
  end.

(** Translation of addressing modes *)

Definition transl_addressing (a: addressing) (args: list mreg): res addrmode :=
  match a, args with
  | Aindexed n, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode (Some r1) None (inl _ n))
  | Aindexed2 n, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK(Addrmode (Some r1) (Some(r2, Int.one)) (inl _ n))
  | Ascaled sc n, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode None (Some(r1, sc)) (inl _ n))
  | Aindexed2scaled sc n, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2;
      OK(Addrmode (Some r1) (Some(r2, sc)) (inl _ n))
  | Aglobal id ofs, nil =>
      OK(Addrmode None None (inr _ (id, ofs)))
  | Abased id ofs, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode (Some r1) None (inr _ (id, ofs)))
  | Abasedscaled sc id ofs, a1 :: nil =>
      do r1 <- ireg_of a1; OK(Addrmode None (Some(r1, sc)) (inr _ (id, ofs)))
  | Ainstack n, nil =>
      OK(Addrmode (Some ESP) None (inl _ n))
  | _, _ =>
      Error(msg "Asmgen.transl_addressing")
  end.

(** Floating-point comparison.  We swap the operands in some cases
   to simplify the handling of the unordered case. *)

Definition floatcomp (cmp: comparison) (r1 r2: freg) : instruction :=
  match cmp with
  | Clt | Cle => Pcomisd_ff r2 r1
  | Ceq | Cne | Cgt | Cge => Pcomisd_ff r1 r2
  end.

(** Translation of a condition.  Prepends to [k] the instructions
  that evaluate the condition and leave its boolean result in bits
  of the condition register. *)

Definition transl_cond
              (cond: condition) (args: list mreg) (k: code) : res code :=
  match cond, args with
  | Ccomp c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2; OK (Pcmp_rr r1 r2 :: k)
  | Ccompu c, a1 :: a2 :: nil =>
      do r1 <- ireg_of a1; do r2 <- ireg_of a2; OK (Pcmp_rr r1 r2 :: k)
  | Ccompimm c n, a1 :: nil =>
      do r1 <- ireg_of a1;
      OK (if Int.eq_dec n Int.zero then Ptest_rr r1 r1 :: k else Pcmp_ri r1 n :: k)
  | Ccompuimm c n, a1 :: nil =>
      do r1 <- ireg_of a1; OK (Pcmp_ri r1 n :: k)
  | Ccompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; OK (floatcomp cmp r1 r2 :: k)
  | Cnotcompf cmp, a1 :: a2 :: nil =>
      do r1 <- freg_of a1; do r2 <- freg_of a2; OK (floatcomp cmp r1 r2 :: k)
  | Cmaskzero n, a1 :: nil =>
      do r1 <- ireg_of a1; OK (Ptest_ri r1 n :: k)
  | Cmasknotzero n, a1 :: nil =>
      do r1 <- ireg_of a1; OK (Ptest_ri r1 n :: k)
  | _, _ =>
     Error(msg "Asmgen.transl_cond")
  end.

(** What processor condition to test for a given Mach condition. *)

Definition testcond_for_signed_comparison (cmp: comparison) :=
  match cmp with
  | Ceq => Cond_e
  | Cne => Cond_ne
  | Clt => Cond_l
  | Cle => Cond_le
  | Cgt => Cond_g
  | Cge => Cond_ge
  end.

Definition testcond_for_unsigned_comparison (cmp: comparison) :=
  match cmp with
  | Ceq => Cond_e
  | Cne => Cond_ne
  | Clt => Cond_b
  | Cle => Cond_be
  | Cgt => Cond_a
  | Cge => Cond_ae
  end.

Inductive extcond: Type :=
  | Cond_base (c: testcond)
  | Cond_or (c1 c2: testcond)
  | Cond_and (c1 c2: testcond).

Definition testcond_for_condition (cond: condition) : extcond :=
  match cond with
  | Ccomp c => Cond_base(testcond_for_signed_comparison c)
  | Ccompu c => Cond_base(testcond_for_unsigned_comparison c)
  | Ccompimm c n => Cond_base(testcond_for_signed_comparison c)
  | Ccompuimm c n => Cond_base(testcond_for_unsigned_comparison c)
  | Ccompf c =>
      match c with
      | Ceq => Cond_and Cond_np Cond_e
      | Cne => Cond_or Cond_p Cond_ne
      | Clt => Cond_base Cond_a
      | Cle => Cond_base Cond_ae
      | Cgt => Cond_base Cond_a
      | Cge => Cond_base Cond_ae
      end
  | Cnotcompf c =>
      match c with
      | Ceq => Cond_or Cond_p Cond_ne
      | Cne => Cond_and Cond_np Cond_e
      | Clt => Cond_base Cond_be
      | Cle => Cond_base Cond_b
      | Cgt => Cond_base Cond_be
      | Cge => Cond_base Cond_b
      end
  | Cmaskzero n => Cond_base Cond_e
  | Cmasknotzero n => Cond_base Cond_ne
  end.

(** Acting upon extended conditions. *)

Definition mk_setcc (cond: extcond) (rd: ireg) (k: code) :=
  match cond with
  | Cond_base c => Psetcc c rd :: k
  | Cond_and c1 c2 =>
      if ireg_eq rd EDX
      then Psetcc c1 EDX :: Psetcc c2 ECX :: Pand_rr EDX ECX :: k
      else Psetcc c1 EDX :: Psetcc c2 rd  :: Pand_rr rd EDX :: k
  | Cond_or c1 c2 => 
      if ireg_eq rd EDX
      then Psetcc c1 EDX :: Psetcc c2 ECX :: Por_rr EDX ECX :: k
      else Psetcc c1 EDX :: Psetcc c2 rd  :: Por_rr rd EDX :: k
  end.

Definition mk_jcc (cond: extcond) (lbl: label) (k: code) :=
  match cond with
  | Cond_base c => Pjcc c lbl :: k
  | Cond_and c1 c2 => Pjcc2 c1 c2 lbl :: k
  | Cond_or c1 c2 => Pjcc c1 lbl :: Pjcc c2 lbl :: k
  end.

(** Translation of the arithmetic operation [r <- op(args)].
  The corresponding instructions are prepended to [k]. *)

Definition transl_op
             (op: operation) (args: list mreg) (res: mreg) (k: code) : Errors.res code :=
  match op, args with
  | Omove, a1 :: nil =>
      mk_mov (preg_of res) (preg_of a1) k
  | Ointconst n, nil =>
      do r <- ireg_of res;
      OK ((if Int.eq_dec n Int.zero then Pxor_r r else Pmov_ri r n) :: k)
  | Ofloatconst f, nil =>
      do r <- freg_of res; 
      OK ((if Float.eq_dec f Float.zero then Pxorpd_f r else Pmovsd_fi r f) :: k)
  | Oindirectsymbol id, nil =>
      do r <- ireg_of res;
      OK (Pmov_ra r id :: k)
  | Ocast8signed, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv Pmovsb_rr r r1 k
  | Ocast8unsigned, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv Pmovzb_rr r r1 k
  | Ocast16signed, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv Pmovsw_rr r r1 k
  | Ocast16unsigned, a1 :: nil =>
      do r1 <- ireg_of a1; do r <- ireg_of res; mk_intconv Pmovzw_rr r r1 k
  | Oneg, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pneg r :: k)
  | Osub, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Psub_rr r r2 :: k)
  | Omul, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pimul_rr r r2 :: k)
  | Omulimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pimul_ri r n :: k)
  | Odiv, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; mk_div Pidiv r r2 k
  | Odivu, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; mk_div Pdiv r r2 k
  | Omod, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; mk_mod Pidiv r r2 k
  | Omodu, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; mk_mod Pdiv r r2 k
  | Oand, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pand_rr r r2 :: k)
  | Oandimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pand_ri r n :: k)
  | Oor, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Por_rr r r2 :: k)
  | Oorimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Por_ri r n :: k)
  | Oxor, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; OK (Pxor_rr r r2 :: k)
  | Oxorimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pxor_ri r n :: k)
  | Oshl, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; mk_shift Psal_rcl r r2 k
  | Oshlimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Psal_ri r n :: k)
  | Oshr, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; mk_shift Psar_rcl r r2 k
  | Oshrimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Psar_ri r n :: k)
  | Oshru, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; do r2 <- ireg_of a2; mk_shift Pshr_rcl r r2 k
  | Oshruimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pshr_ri r n :: k)
  | Oshrximm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; mk_shrximm r n k
  | Ororimm n, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- ireg_of res; OK (Pror_ri r n :: k)
  | Olea addr, _ =>
      do am <- transl_addressing addr args; do r <- ireg_of res;
      OK (Plea r am :: k)
  | Onegf, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- freg_of res; OK (Pnegd r :: k)
  | Oabsf, a1 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- freg_of res; OK (Pabsd r :: k)
  | Oaddf, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Paddd_ff r r2 :: k)
  | Osubf, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Psubd_ff r r2 :: k)
  | Omulf, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Pmuld_ff r r2 :: k)
  | Odivf, a1 :: a2 :: nil =>
      do x <- assertion (mreg_eq a1 res);
      do r <- freg_of res; do r2 <- freg_of a2; OK (Pdivd_ff r r2 :: k)
  | Osingleoffloat, a1 :: nil =>
      do r <- freg_of res; do r1 <- freg_of a1; OK (Pcvtsd2ss_ff r r1 :: k)
  | Ointoffloat, a1 :: nil =>
      do r <- ireg_of res; do r1 <- freg_of a1; OK (Pcvttsd2si_rf r r1 :: k)
  | Ofloatofint, a1 :: nil =>
      do r <- freg_of res; do r1 <- ireg_of a1; OK (Pcvtsi2sd_fr r r1 :: k)
  | Ocmp c, args =>
      do r <- ireg_of res;
      transl_cond c args (mk_setcc (testcond_for_condition c) r k)
  | _, _ =>
      Error(msg "Asmgen.transl_op")
  end.

(** Translation of memory loads and stores *)

Definition transl_load (chunk: memory_chunk)
                       (addr: addressing) (args: list mreg) (dest: mreg)
                       (k: code) : res code :=
  do am <- transl_addressing addr args;
  match chunk with
  | Mint8unsigned =>
      do r <- ireg_of dest; OK(Pmovzb_rm r am :: k)
  | Mint8signed =>
      do r <- ireg_of dest; OK(Pmovsb_rm r am :: k)
  | Mint16unsigned =>
      do r <- ireg_of dest; OK(Pmovzw_rm r am :: k)
  | Mint16signed =>
      do r <- ireg_of dest; OK(Pmovsw_rm r am :: k)
  | Mint32 =>
      do r <- ireg_of dest; OK(Pmov_rm r am :: k)
  | Mfloat32 =>
      do r <- freg_of dest; OK(Pcvtss2sd_fm r am :: k)
  | Mfloat64 | Mfloat64al32 =>
      do r <- freg_of dest; OK(Pmovsd_fm r am :: k)
  end.

Definition transl_store (chunk: memory_chunk)
                        (addr: addressing) (args: list mreg) (src: mreg)
                        (k: code) : res code :=
  do am <- transl_addressing addr args;
  match chunk with
  | Mint8unsigned | Mint8signed =>
      do r <- ireg_of src; mk_smallstore Pmovb_mr am r k
  | Mint16unsigned | Mint16signed =>
      do r <- ireg_of src; OK(Pmovw_mr am r :: k)
  | Mint32 =>
      do r <- ireg_of src; OK(Pmov_mr am r :: k)
  | Mfloat32 =>
      do r <- freg_of src; OK(Pcvtsd2ss_mf am r :: k)
  | Mfloat64 | Mfloat64al32 =>
      do r <- freg_of src; OK(Pmovsd_mf am r :: k)
  end.

(** Translation of arguments to annotations *)

Definition transl_annot_param (p: Mach.annot_param) : Asm.annot_param :=
  match p with
  | Mach.APreg r => APreg (preg_of r)
  | Mach.APstack chunk ofs => APstack chunk ofs
  end.

(** Translation of a Mach instruction. *)

Definition transl_instr (f: Mach.function) (i: Mach.instruction)
                        (* edx_is_parent: bool *) (k: code) :=
  match i with
  | Mgetstack ofs ty dst =>
      loadind ESP ofs ty dst k
  | Msetstack src ofs ty =>
      storeind src ESP ofs ty k
  | Mgetparam ofs ty dst =>
      loadind ESP (Int.add (Int.repr (f.(fn_stacksize) + Memdata.size_chunk Mint32)) ofs) ty dst k
(*      if edx_is_parent then
        loadind EDX ofs ty dst k
      else
        (do k1 <- loadind EDX ofs ty dst k;
         loadind ESP f.(fn_link_ofs) Tint IT1 k1) *)
  | Mop op args res =>
      transl_op op args res k
  | Mload chunk addr args dst =>
      transl_load chunk addr args dst k
  | Mstore chunk addr args src =>
      transl_store chunk addr args src k
  | Mcall sig (inl reg) =>
      do r <- ireg_of reg; OK (Pcall_r r :: k)
  | Mcall sig (inr symb) =>
      OK (Pcall_s symb :: k)
  | Mtailcall sig (inl reg) =>
      do r <- ireg_of reg; 
      OK (Plea ESP (Addrmode (Some ESP) None (inl _ (Int.repr f.(fn_stacksize)))) ::
          Pjmp_r r :: k)
  | Mtailcall sig (inr symb) =>
      OK (Plea ESP (Addrmode (Some ESP) None (inl _ (Int.repr f.(fn_stacksize)))) :: 
          Pjmp_s symb :: k)
  | Mlabel lbl =>
      OK(Plabel lbl :: k)
  | Mgoto lbl =>
      OK(Pjmp_l lbl :: k)
  | Mcond cond args lbl =>
      transl_cond cond args (mk_jcc (testcond_for_condition cond) lbl k)
  | Mjumptable arg tbl =>
      do r <- ireg_of arg; OK (Pjmptbl r tbl :: k)
  | Mreturn =>
      OK (Plea ESP (Addrmode (Some ESP) None (inl _ (Int.repr f.(fn_stacksize)))) :: 
          Pret :: k)
  | Mbuiltin ef args res =>
      OK (Pbuiltin ef (List.map preg_of args) (preg_of res) :: k)
  | Mannot ef args =>
      OK (Pannot ef (map transl_annot_param args) :: k)
  end.

(** Translation of a code sequence *)

(*
Definition edx_preserved (before: bool) (i: Mach.instruction) : bool :=
  match i with
  | Msetstack src ofs ty => before
  | Mgetparam ofs ty dst => negb (mreg_eq dst IT1)
  | _ => false
  end.
*)

Fixpoint transl_code (f: Mach.function) (il: list Mach.instruction)  (* edx_is_parent: bool *) :=
  match il with
  | nil => OK nil
  | i1 :: il' =>
      do k <- transl_code f il' (* edx_preserved edx_is_parent i1*);
      transl_instr f i1 (* edx_is_parent *) k
  end.

(** Translation of a whole function.  Note that we must check
  that the generated code contains less than [2^32] instructions,
  otherwise the offset part of the [PC] code pointer could wrap
  around, leading to incorrect executions. *)

Definition transf_function (f: Mach.function) : res Asm.code :=
  do c <- transl_code f f.(Mach.fn_code) (* true *);
  if zlt (list_length_z c) Int.max_unsigned 
  then
      OK (Plea ESP (Addrmode (Some ESP) None (inl _ (Int.repr (0 - f.(fn_stacksize))))) :: c)
  else Error (msg "code size exceeded").

Definition transf_fundef (f: Mach.fundef) : res Asm.fundef :=
  transf_partial_fundef transf_function f.

Definition transf_program (p: Mach.program) : res Asm.program :=
  transform_partial_program transf_fundef p.
