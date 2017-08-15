
open Julia
open Compiler
open Parsr
open Lexr

open Lexing
open Printf

(* The following two functions comes from
 * https://github.com/realworldocaml/examples/tree/master/code/parsing-test
 * which is under UNLICENSE
 *)
let print_position outx lexbuf =
  let pos = lexbuf.lex_curr_p in
  fprintf outx "%s:%d:%d" pos.pos_fname
    pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)

let parse_with_error lexbuf =
  try Parsr.main Lexr.read lexbuf with
  | SyntaxError msg ->
    fprintf stderr "%a: %s\n" print_position lexbuf msg;
    exit (-1)
  | Parsr.Error ->
    fprintf stderr "%a: syntax error\n" print_position lexbuf;
    exit (-1)
  | a ->
    raise a

let rec value_to_string = function
 | FalseV -> "false"
 | TrueV -> "true"
 | IntV i -> Z.to_string i
 | StringV i -> "'" ^ Z.to_string i ^ "'"
 | ListV lst -> "[" ^ String.concat "," (List.map value_to_string lst) ^ "]"
 | FunctionV (id, _, _, _) -> "function " ^ Z.to_string id
 | BuiltinV _ -> "builtin"
 | GBuiltinV _ -> "state builtin"

let parse_file fname =
  let lexbuf = Lexing.from_channel (open_in fname) in
  parse_with_error lexbuf

let builtins = [
  "addu256", AddU256;
]

let print_state l =
  Pmap.iter (fun k v -> prerr_endline (Z.to_string k ^ " -> " ^ value_to_string v)) l 

let builtins2 = [
  "mstore", MStore;
  "mstore8", MStore8;
  "mload", MLoad;
  "sstore", SStore;
  "sload", SLoad;
  "return", Return;
  "revert", Revert;
  "create", Create;
  "call", Call;
]

let init =
  List.fold_left (fun acc (k,v) -> Pmap.add (JuliaUtil.string_to_Z k) {func_label=BFunc v; func_returns=0} acc) (Pmap.empty compare) builtins

let init =
  List.fold_left (fun acc (k,v) -> Pmap.add (JuliaUtil.string_to_Z k) {func_label=GFunc v; func_returns=0} acc) init builtins2

let print_inst i =
  prerr_endline ("Inst " ^ String.concat "," (List.map (fun x -> Z.format "%x" (Word8.word8ToNatural x)) (Evm.inst_code i)))

let check_statement st =
  let code, ctx = Compiler.compile_statement {empty_context with funcs=init} st in
  let final_code = Compiler.handle_labels code in
  prerr_endline "Compiled statement";
  List.iter print_inst final_code

let main () =
  if Array.length Sys.argv < 2 then prerr_endline "need filename" else
  let lst = parse_file Sys.argv.(1) in
  let _ = prerr_endline "Finished parsing" in
  List.iter check_statement lst

let _ =
  main ()

