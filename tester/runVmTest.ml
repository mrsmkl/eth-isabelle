open Yojson.Basic
open Jsonparser
open Constant

(* for now executes the first vmTest found in a particular file *)

let () =
  let () = Printf.printf "hello\n" in
  let vm_arithmetic_test : json = Yojson.Basic.from_file "../tests/VMTests/vmArithmeticTest.json" in
  let vm_arithmetic_test_assoc : (string * json) list = Util.to_assoc vm_arithmetic_test in
  let (label, j) = List.nth vm_arithmetic_test_assoc 0 in
  let () = Printf.printf "test case: %s\n" label in
  let test_case : test_case = parse_test_case j in
  let open Evm in
  let open Conv in
  (*val program_sem : variable_ctx -> constant_ctx -> int -> nat -> program_result*)
  (* TODO: cut below as a function, maybe into Conv *)

  let addr : address = word160_of_big_int test_case.exec.address in
  let initial_storage : storage = lookup_storage addr test_case.pre in
  let initial_balance : address -> w256 = construct_global_balance test_case.pre in
  let v : variable_ctx =
    { vctx_stack = []
    ; vctx_memory = empty_memory
    ; vctx_memory_usage = 0
    ; vctx_storage = initial_storage
    ; vctx_pc = 0
    ; vctx_balance = initial_balance
    ; vctx_caller = word160_of_big_int test_case.exec.caller
    ; vctx_value_sent = word256_of_big_int test_case.exec.value
    ; vctx_data_sent = byte_list_of_hex_string test_case.exec.data
    ; vctx_storage_at_call = initial_storage
    ; vctx_balance_at_call = initial_balance
    ; vctx_origin = word160_of_big_int test_case.exec.origin
    ; vctx_ext_program = construct_ext_program test_case.pre
    ; vctx_block = construct_block_info test_case
    ; vctx_gas = Big_int.int_of_big_int test_case.exec.gas
    ; vctx_account_existence = construct_account_existence test_case.pre
    ; vctx_touched_storage_index = []
    } in
  let c : constant_ctx =
    { cctx_program = test_case.exec.code
    ; cctx_this = Conv.word160_of_big_int test_case.exec.address
    } in
  (* let ret : program_result = Evm.program_sem  in *)
  ()