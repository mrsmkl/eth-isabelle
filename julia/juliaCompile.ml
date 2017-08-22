
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

let tbuiltins = [
  "addu256", FType ([U256; U256], [U256])
]

let type_map =
  List.fold_left (fun acc (k,v) -> Pmap.add (JuliaUtil.string_to_Z k) v acc) (Pmap.empty compare) tbuiltins

let print_inst i =
  prerr_endline ("Inst " ^ String.concat "," (List.map (fun x -> Z.format "%x" (Word8.word8ToNatural x)) (Evm.inst_code i)))

open Evm

let debug_vm c1 = function
  | InstructionContinue v ->
     ( match vctx_next_instruction v c1 with
      | Some i ->
        (* prerr_endline ("Watch " ^ w256hex (v.vctx_storage (Word256.word256FromNat 1))); *)
        (* prerr_endline ("Calldata " ^ String.concat "," (List.map (fun x -> Z.format "%x" (Word8.word8ToNatural x)) v.vctx_data_sent)); *)
        prerr_endline ("Stack " ^ String.concat "," (List.map (fun x -> Z.format "%d" (Word256.word256ToNatural x)) v.vctx_stack));
        print_inst i
      | None -> () )
  | InstructionToEnvironment( _, v, _) -> prerr_endline ("Exiting, Gas left " ^ Z.to_string v.vctx_gas)

exception ToEnvironment of instruction_result

let the_stopper r = raise (ToEnvironment r)

let program_sem_wrapper c n net r =
  try Evm.next_state the_stopper c net r
  with ToEnvironment a -> a

let rec run_vm c r =
  debug_vm c r ;
  match r with
  | InstructionContinue _ ->
     let r = program_sem_wrapper c 1000 Evm.Homestead r in
     run_vm c r
  | _ -> ()

let zero = Word256.word256FromInteger Z.zero
let zero_addr = Word160.word160FromInteger Z.zero

let empty_block = {
  block_blockhash = (fun _ -> zero);
  block_coinbase = zero_addr;
  block_timestamp = zero;
  block_number = zero;
  block_difficulty = zero;
  block_gaslimit = zero;
  
}

let empty_env = {
    vctx_stack = [];
    vctx_memory = empty_memory; (* The memory is also initialized for every invocation *)
    vctx_memory_usage = Z.zero; (* The memory usage is initialized. *)
    vctx_storage = (fun _ -> zero); (* The storage is taken from the account state *)
    vctx_pc = Z.zero; (* The program counter is initialized to zero *)
    vctx_balance = (fun (addr:address) -> zero);
    vctx_caller = zero_addr; (* the caller is specified by the environment *)
    vctx_value_sent = zero; (* the sent value is specified by the environment *)
     vctx_data_sent = []; (* the sent data is specified by the environment *)
     vctx_storage_at_call =  (fun _ -> zero); (* the snapshot of the storage is remembered in case of failure *)
     vctx_balance_at_call =  (fun (addr:address) -> zero); (* the snapshot of the balance is remembered in case of failure *)
     vctx_origin = zero_addr; (* the origin of the transaction is arbitrarily chosen *)
     vctx_gasprice = zero; (* the gasprice of the transaction is arbitrarily chosen *) 
     vctx_ext_program = (fun (addr:address) -> {program_length=Z.zero; program_content = (fun _ -> None)}); (* the codes of the external programs are arbitrary. *)
     vctx_block = empty_block; (* the block information is chosen arbitrarily. *)
     vctx_gas = Z.of_int 1000000; (* the amount of gas is chosen arbitrarily. *)
     vctx_account_existence = (fun (addr:address) -> false); (* existence is chosen arbitrarily *)
     vctx_touched_storage_index = [];
     vctx_logs = [];
     vctx_refund = Z.zero;
}


let check_statement st =
  let st = Compiler.elim_forloop_init st in
  let _ = match Typecheck.check_statement type_map st with
   | None -> prerr_endline "Type error"
   | Some _ -> () in
  let code, ctx = Compiler.compile_statement {empty_context with funcs=init} st in
  let final_code = Compiler.handle_labels 0 code in
  prerr_endline "Compiled statement";
  List.iter print_inst final_code;
  prerr_endline "Going to run it now!!!";
  let code_exp = List.concat (List.map expand2 final_code) in
  let codemap x =
    if Z.lt x Z.zero then None else
    try Some (List.nth code_exp (Z.to_int x))
    with Failure _ -> None in
   let prog = {
       program_length = Z.of_int (List.length final_code);
       program_content = codemap } in
  let c = { cctx_program = prog; cctx_this = zero_addr; cctx_hash_filter = (fun _ -> true) } in
  run_vm c (InstructionContinue empty_env)

let main () =
  if Array.length Sys.argv < 2 then prerr_endline "need filename" else
  let lst = parse_file Sys.argv.(1) in
  let _ = prerr_endline "Finished parsing" in
  List.iter check_statement lst

let _ =
  main ()

