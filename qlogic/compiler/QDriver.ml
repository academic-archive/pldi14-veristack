(* Driver for the resource
   aware C compiler.

   Uses automatic analysis
   to derive bound on Cxlight
   programs before feeding
   them to a quantitative
   aware CompCert.

   Some code is from CompCert's
   original driver.
*)

(* Convert regular C to Cxlight. *)
module C2Cxlight = struct

  open AST
  open Errors
  open Csyntax

  let unsupported x =
    failwith (Printf.sprintf "Cxlight error: unsupported feature (%s)." x)

  let convE loc =
    let rec f = function
    | Eval (Values.Vint i, ty) ->       Clight.Econst_int (i, ty)
    | Eval (Values.Vfloat f, ty) ->     Clight.Econst_float (f, ty)
    | Eval (_, _) ->                    unsupported "value"
    | Evar (i, ty) ->                   if List.mem i loc
                                          then Clight.Etempvar (i, ty)
                                          else Clight.Evar (i, ty)
    | Efield (e, i, ty) ->              Clight.Efield (f e, i, ty)
    | Evalof (e, _) ->                  f e
    | Ederef (e, ty) ->                 Clight.Ederef (f e, ty)
    | Eaddrof (e, ty) ->                Clight.Eaddrof (f e, ty)
    | Eunop (u, e, ty) ->               Clight.Eunop (u, f e, ty)
    | Ebinop (b, el, er, ty) ->         Clight.Ebinop (b, f el, f er, ty)
    | Ecast (e, ty) ->                  Clight.Ecast (f e, ty)
    | Eseqand (e1, e2, ty) ->           Clight.Ebinop (Cop.Oand, f e1 , f e2, ty)
    | Eseqor (e1, e2, ty) ->            Clight.Ebinop (Cop.Oor, f e1 , f e2, ty)
    | Econdition (_, _, _, _) ->        unsupported "ternary operator"
    | Esizeof (ty1, ty2) ->             Clight.coq_Esizeof ty1 ty2
    | Ealignof (ty1, ty2) ->            Clight.coq_Ealignof ty1 ty2
    | Eassign (_, _, _) ->              unsupported "expression assignment"
    | Eassignop (_, _, _, _, _) ->      unsupported "+= -= *= /= &= |="
    | Epostincr (_, _, _) ->            unsupported "post increment"
    | Ecomma (_, _, _) ->               unsupported "comma operator"
    | Ecall (_, _, _) ->                unsupported "call"
    | Ebuiltin (_, _, _, _) ->          unsupported "builtin"
    | Eloc (_, _, _) ->                 unsupported "loc expression"
    | Eparen (e, ty) ->                 Clight.Ecast (f e, ty)
  in f

  let rec convElist loc = function
  | Enil -> []
  | Econs (e, l) -> convE loc e :: convElist loc l

  let epostincr iod e ty =
    let one = Clight.Econst_int (Integers.Int.one, Ctypes.type_int32s) in
    let op =
      match iod with
      | Cop.Incr -> Cop.Oadd
      | Cop.Decr -> Cop.Osub
    in Clight.Ebinop (op, e, one, ty)

  let rec convSdo loc = function

  | Eassign (Evar (v, _), Ecall (Evalof (Evar (f, _), _), el, _), _) ->
    Core.Coq_scall (Some v, f, convElist loc el)
  | Eassign (x, y, _) ->
    begin match x with
    | Evar (v, _) when List.mem v loc -> Core.Coq_slset (v, convE loc y)
    | _ -> Core.Coq_sgset (convE loc x, convE loc y)
    end

  | Ecall (Evalof (Evar (f, _), _), el, _) ->
    Core.Coq_scall (None, f, convElist loc el)
  | Ecall (x, _, _) -> unsupported (Printf.sprintf "call %d" (Obj.tag (Obj.repr x)))

  (* | Eparen (e, _) -> convSdo loc e *)

  | Epostincr (o, Evar (v, tv), ty) when List.mem v loc ->
    Core.Coq_slset (v, epostincr o (Clight.Etempvar (v, tv)) ty)
  | Epostincr (o, e, ty) ->
    Core.Coq_sgset (convE loc e, epostincr o (convE loc e) ty)

  | Eassignop (op, Evar (v, tv), r, tyres, _) when List.mem v loc ->
    Core.Coq_slset
      (v, Clight.Ebinop (op, Clight.Etempvar (v, tv), convE loc r, tyres))
  | Eassignop (op, l, r, tyres, _) ->
    let l' = convE loc l and r' = convE loc r in
    Core.Coq_sgset (l', Clight.Ebinop (op, l', r', tyres))

  | e -> unsupported "effectful expression"

  let convS loc =
      let make_while e s =
        Core.Coq_sloop (Core.Coq_sif (convE loc e, s, Core.Coq_sbreak)) in
      let rec f = function
      | Sskip ->                        Core.Coq_sskip
      | Sdo s ->                        convSdo loc s
      | Ssequence (s1, s2) ->           Core.Coq_sseq (f s1, f s2)
      | Sifthenelse (e, s1, s2) ->      Core.Coq_sif (convE loc e, f s1, f s2)
      | Swhile (e, s) ->                make_while e (f s)
      | Sdowhile (e, s) ->
        Core.Coq_sloop (Core.Coq_sseq
          (f s, Core.Coq_sif (convE loc e, Core.Coq_sbreak, Core.Coq_sskip)))
      | Sfor (ini, test, inc, s) ->
        Core.Coq_sseq (f ini, make_while test (Core.Coq_sseq (f s, f inc)))
      | Sbreak ->                       Core.Coq_sbreak
      | Scontinue ->                    unsupported "continue"
      | Sreturn e ->
        Core.Coq_sret (
          match e with
          | Some e' -> Some (convE loc e')
          | None -> None
        )
      | Sswitch (_, _) ->               unsupported "switch"
      | Slabel _ ->                     unsupported "label"
      | Sgoto _ ->                      unsupported "goto"

    in f

  let convF fn =
    let body = convS (List.map fst (fn.fn_vars @ fn.fn_params)) fn.fn_body in
    { Cxlight.fi_name = fn.fn_id
    ; Cxlight.fi_args = fn.fn_params
    ; Cxlight.fi_locals = fn.fn_vars
    ; Cxlight.fi_body = body
    ; Cxlight.fi_return = fn.fn_return
    }

  let convP p =
    let rec f = function
    | [] -> []
    | (id, Gvar v) :: defs -> (id, Gvar v) :: f defs
    | (id, Gfun (Internal i)) :: defs -> (id, Gfun (convF i)) :: f defs
    | _ :: defs -> f defs (* warn ? *)
  in { prog_defs = f p.prog_defs; prog_main = p.prog_main }

  let convertProgram p =
    try Some (convP p)
    with Failure m -> prerr_endline m; None

end

(* Make sure the call graph is well founded and
   rename functions to express it. The result of
   this transformation is then checked in Coq
   for correctness.
*)
module Reorder = struct

  open AST
  open BinPos
  open Camlcoq
  open Core
  open Cxlight
  open Datatypes

  type fnode =
    { fn_id: AST.ident
    ; mutable fn_rename: AST.ident option
    ; fn_calling: AST.ident list
    }

  let cmp_pos x y =
    match Pos.compare x y with
    | Gt -> 1
    | Eq -> 0
    | Lt -> -1

  let cmp x y = cmp_pos x.fn_id y.fn_id

  module FSet = Set.Make(struct type t = fnode  let compare = cmp end)
  module FMap = Map.Make(struct type t = AST.ident  let compare = cmp_pos end)

  let rec calling = function
  | Coq_scall (_, g, _) -> [ g ]
  | Coq_sseq (s1, s2)
  | Coq_sif (_, s1, s2) -> calling s1 @ calling s2
  | Coq_sloop s -> calling s
  | _ -> []

  exception Cycle of AST.ident

  let topological_sorting fm =
    let rec f curr rest =
      if FSet.is_empty curr then
        if FSet.is_empty rest then () else
        raise (Cycle (FSet.choose rest).fn_id)
      else begin
        let fn = FSet.choose curr in
        let curr' = FSet.remove fn curr in
        let a = !next_atom in
        next_atom := Pos.succ a;
        fn.fn_rename <- Some a;
        Hashtbl.add string_of_atom a (extern_atom fn.fn_id);
        let (new_curr, rest') =
          FSet.partition
            (fun g ->
              let ok h =
                try (FMap.find h fm).fn_rename <> None
                with _ -> raise (Cycle g.fn_id)
              in List.for_all ok g.fn_calling)
            rest in
        f (FSet.union new_curr curr') rest'
      end
    in let base, rest =
      FMap.fold
        (fun _ fn (base, rest) ->
          if fn.fn_calling = []
            then (FSet.add fn base, rest)
            else (base, FSet.add fn rest))
        fm (FSet.empty, FSet.empty)
    in f base rest

  let get_new_name fm f =
    match (FMap.find f fm).fn_rename with
    | Some x -> x | None -> assert false

  let convS fm =
    let rec f = function
    | Coq_scall (v, g, l) -> Coq_scall (v, get_new_name fm g, l)
    | Coq_sseq (s1, s2) -> Coq_sseq (f s1, f s2)
    | Coq_sif (t, s1, s2) -> Coq_sif (t, f s1, f s2)
    | Coq_sloop s -> Coq_sloop (f s)
    | x -> x
  in f

  let convProgdef fm = function
    | (_, Gfun fi) ->
      let fi_rename = get_new_name fm fi.fi_name
      in (fi_rename, Gfun { fi with fi_name = fi_rename;
                                    fi_body = convS fm fi.fi_body })
    | x -> x

  let convertProgram p =
    let rec get_fi = function
      | [] -> []
      | (_, Gfun f) :: defs -> f :: get_fi defs
      | _ :: defs -> get_fi defs
    in let fm =
      List.fold_left
        (fun fm fi ->
          FMap.add fi.fi_name {
            fn_id = fi.fi_name;
            fn_rename = None;
            fn_calling = calling fi.fi_body
          } fm)
        FMap.empty
        (get_fi p.prog_defs)
    in try
      topological_sorting fm;
      Some { prog_main = (try get_new_name fm p.prog_main with _ -> p.prog_main);
             prog_defs = List.map (convProgdef fm) p.prog_defs }
    with
    | Cycle f ->
      Printf.eprintf
        "Error: function '%s' is recursive or uses external functions.\n"
        (extern_atom f); None

end


(* Driving code. *)

open Camlcoq
open Printf
open Clflags

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (extern_atom i)
  | Errors.POS i -> fprintf oc "%ld" (P.to_int32 i)
  in
    List.iter print_one_error msg;
    output_char oc '\n'

let command = Sys.command

let safe_remove file =
  try Sys.remove file with Sys_error _ -> ()

let quote_options opts =
  String.concat " " (List.rev_map Filename.quote opts)

(* Determine names for output files.  We use -o option if specified
   and if this is the final destination file (not a dump file).
   Otherwise, we generate a file in the current directory. *)

let output_filename ?(final = false) source_file source_suffix output_suffix =
  match !option_o with
  | Some file when final -> option_o := None; file
  | _ -> 
    Filename.basename (Filename.chop_suffix source_file source_suffix)
    ^ output_suffix

(* From C to preprocessed C. *)

let preprocess ifile ofile =
  let output =
    if ofile = "-" then "" else sprintf "> %s" ofile in
  let cmd =
    sprintf "%s -D__COMPCERT__ %s %s %s %s"
      Configuration.prepro ""
      (*(if Configuration.has_runtime_lib
       then sprintf "-I%s" !stdlib_path
       else "")*)
      (quote_options !prepro_options)
      ifile output in
  if command cmd <> 0 then begin
    if ofile <> "-" then safe_remove ofile;
    eprintf "Error: preprocessor failure.\n";
    exit 2
  end

(* From preprocessed C to Cxlight. *)

let parse_cx_file sourcename ifile =
  let get_some = function
    | Some b -> b
    | None -> exit 2 in
  Sections.initialize ();
  let simplifs = "b" in
  (* Parse the AST *)
  let ast = get_some (Parse.preprocessed_file simplifs sourcename ifile) in
  (* Remove the temporary preprocessed file. *)
  safe_remove ifile;
  (* Convert to Csyntax. *)
  let csyntax = get_some (C2C.convertProgram ast) in
  flush stderr;
  (* Convert to Cxlight. *)
  let cxlight = get_some (C2Cxlight.convertProgram csyntax) in
  (* Perform the ident reordering and return Cxlight program. *)
  get_some (Reorder.convertProgram cxlight)

(* Compile Cxlight code to asm. *)

let compile_cx_ast sourcename cxlight ofile bfile =
  (* Convert to Asm *)
  let set_dest dst opt ext =
    dst := if !opt then Some (output_filename sourcename ".c" ext)
                   else None in
  set_dest PrintClight.destination (ref true) ".light.c";
  let ((asm, bound_of), bmain) =
    match CoreCompiler.trans_program cxlight with
    | Errors.OK x -> x
    | Errors.Error msg ->
        eprintf "Error: ";
        print_error stderr msg;
        exit 2 in
  (* Print Asm in text form *)
  let oc = open_out ofile in
  PrintAsm.print_program oc (Unusedglob.transf_program asm);
  close_out oc;
  (* Dump the bounds *)
  let oc = open_out bfile in
  fprintf oc "[-] Stack bounds for program functions:\n\n";
  let rec dmp = function
  | (fn, AST.Gfun _) :: defs ->
    let bnd =
      match bound_of fn with
      | Some b -> Z.to_int b
      | None -> assert false
    in fprintf oc "%s <= %d bytes\n" (extern_atom fn) bnd; dmp defs
  | _ :: defs -> dmp defs
  | [] -> () in
  dmp cxlight.AST.prog_defs;
  begin match bmain with
  | Some b ->
    fprintf oc "\n[-] Overall stack consumption <= %ld bytes\n"
               (camlint_of_coqint b)
  | None -> ()
  end;
  close_out oc

(* From C code to asm *)

let compile_cx_file sourcename ifile ofile bfile =
  compile_cx_ast sourcename (parse_cx_file sourcename ifile) ofile bfile

(* Full processing of a Cxlight file. *)

let process_cx_file sourcename =
  let preproname = Filename.temp_file "compcert" ".i" in
  preprocess sourcename preproname;
  compile_cx_file sourcename preproname
                  (output_filename ~final:true sourcename ".c" ".s")
                  (output_filename sourcename ".c" ".bnd")

(* Process args. *)

let process_args () =
  let rec f i =
    if i >= Array.length Sys.argv then () else
    let with_arg err k =
      if i + 1 >= Array.length Sys.argv then begin
        eprintf "Option %s expects a%s.\n" Sys.argv.(i) err;
        exit 2
      end else
        k Sys.argv.(i+1) in
    match Sys.argv.(i) with
    | "-o" ->
      with_arg " file name" (fun fn ->
        option_o := Some fn;
        f (i+2)
      )
    | "-D" ->
      with_arg " macro definition" (fun d ->
        prepro_options := d :: "-D" :: !prepro_options;
        f (i+2)
      )
    | fn when Filename.check_suffix fn ".c" ->
      process_cx_file fn; f (i+1)
    | opt ->
      eprintf "Invalid option %S.\n" opt;
      exit 2
  in f 1

let _ =
  Gc.set { (Gc.get ()) with Gc.minor_heap_size = 524288 };
  Machine.config :=
    begin match Configuration.arch with
    | "ia32"    -> Machine.x86_32
    | _         -> failwith "unsupported architecture"
    end;
  Builtins.set C2C.builtins;
  CPragmas.initialize ();
  process_args ()
