theory Basic
  imports "../lem/Compiler" "../Hoare/Hoare"
begin

(* How to tell if Julia and Evm contexts are equal *)

definition eqU256 :: "int \<Rightarrow> 256 word \<Rightarrow> bool" where
"eqU256 a b = (a = uint b)"

fun eq_value :: "value0 \<Rightarrow> 256 word \<Rightarrow> bool" where
"eq_value (IntV v) w = eqU256 v w"
| "eq_value (StringV v) w = eqU256 v w"
| "eq_value FalseV w = eqU256 0 w"
| "eq_value TrueV w = eqU256 1 w"
| "eq_value _ _ = False"

fun byte_value :: "value0 \<Rightarrow> value0" where
"byte_value FalseV = IntV 0"
| "byte_value TrueV = IntV 1"
| "byte_value a = a"

fun word_value :: "value0 \<Rightarrow> value0" where
"word_value FalseV = IntV 0"
| "word_value TrueV = IntV 1"
| "word_value (StringV v) = IntV v"
| "word_value a = a"

definition eq_memory :: "(int \<Rightarrow> value0) \<Rightarrow> memory \<Rightarrow> bool" where
"eq_memory a b = (\<forall>k. IntV (uint (b k)) = byte_value (a (uint k)))"

definition eq_storage :: "(int \<Rightarrow> value0) \<Rightarrow> storage \<Rightarrow> bool" where
"eq_storage a b = (\<forall>k. IntV (uint (b k)) = word_value (a (uint k)))"

definition eq_context :: "state \<Rightarrow> variable_ctx \<Rightarrow> bool" where
"eq_context a b = (
  memory_size a = vctx_memory_usage b \<and>
  eq_memory (Julia.memory a) (vctx_memory b) \<and>
  eq_storage (Julia.storage (accounts a (address a))) (vctx_storage b)
)"

definition eq_ccontext :: "state \<Rightarrow> constant_ctx \<Rightarrow> bool" where
"eq_ccontext a b = (
   address a = uint (cctx_this b) \<and>
   ( case Julia.code (accounts a (address a)) of
     None \<Rightarrow> False
   |  Some st \<Rightarrow> cctx_program b = compile_program empty_context st ) )"

fun eq_stack :: "state * (int, value0) map \<Rightarrow> variable_ctx * context0 \<Rightarrow> bool" where
"eq_stack (a,vrs) (b,info) = (\<forall>x. (case (vrs x, vars info x) of
    (None, None) \<Rightarrow> True
  | (Some v, Some pr) \<Rightarrow>
      let sh = int (length (vctx_stack b)) in
      let pos = int pr + sh - int (ptr info) in
      pos \<ge> 0 \<and> IntV (uint (vctx_stack b ! nat pos)) = word_value v
  | _ \<Rightarrow> False ))"

fun sub_expressions :: "expression \<Rightarrow> expression list" where
  "sub_expressions (FunctionCall _ lst) = lst"
| "sub_expressions e = []"

fun sub_expressions_tr :: "expression \<Rightarrow> expression list" where
 "sub_expressions_tr e = [e] @ (case e of
    FunctionCall _ lst \<Rightarrow> List.concat (map (%e. sub_expressions e) lst)
  | _ \<Rightarrow> [])"

fun option_to_list :: "'a option \<Rightarrow> 'a list" where
"option_to_list e = (case e of None \<Rightarrow> [] | Some x \<Rightarrow> [x])"

fun sub_statements :: "statement \<Rightarrow> statement list" where
 "sub_statements st = [st] @ (case st of
    Block lst \<Rightarrow> List.concat (map (%st. sub_statements st) lst)
  | Switch _ lst def \<Rightarrow>
      let lst = option_to_list def @ map (%el. let (_,_,st) = el in st) lst in
      List.concat (map sub_statements lst)
  | ForLoop _ st1 st2 \<Rightarrow> sub_statements st1 @ sub_statements st2
  | ForLoopInit lst _ st1 st2 \<Rightarrow> List.concat (map sub_statements (st1#st2#lst))
  | FunctionDefinition _ _ _ st \<Rightarrow> sub_statements st
  | _ \<Rightarrow> [])"

(* subexpressions for statements *)
fun statement_expressions :: "statement \<Rightarrow> expression list" where
  "statement_expressions (VariableDeclaration _ ex) = [ex]"
| "statement_expressions (Assignment _ ex) = [ex]"
| "statement_expressions (Expression ex) = [ex]"
| "statement_expressions (ForLoop ex _ _) = [ex]"
| "statement_expressions (ForLoopInit _ ex _ _) = [ex]"
| "statement_expressions (Switch e lst _) =
      e # map (%el. let (l,t,_) = el in Literal l t) lst"
| "statement_expressions _ = []"

declare sub_statements.simps [simp del]

lemma aux1 :
"set (sub_statements (Block (lst @ [ForLoop e st1 st2]))) =
 set (List.concat (map sub_statements lst)) \<union> set (sub_statements st1)
 \<union> set (sub_statements st2) \<union>
   {Block (lst @ [ForLoop e st1 st2]), ForLoop e st1 st2}"
by (auto simp add: sub_statements.simps)

lemma for_loop_init_elim : "ForLoopInit a b c d \<notin> set (sub_statements (elim_forloop_init st))"
apply (induction st arbitrary: a b c d)
apply (auto simp:elim_forloop_init.simps)
apply (simp add: sub_statements.simps)
apply (simp add: sub_statements.simps)
apply (simp add: sub_statements.simps)
apply (simp add: sub_statements.simps)
apply (simp add: sub_statements.simps)
defer
apply (simp add: sub_statements.simps)
apply (simp add: sub_statements.simps)
defer
apply (simp add: sub_statements.simps)
apply (simp add: sub_statements.simps)
apply (case_tac x3)
apply (auto simp add: sub_statements.simps)[1]
apply (auto simp add: sub_statements.simps)[1]
apply (auto simp add: aux1)[1]
done

(* perhaps check some issues independently *)

definition step :: "network \<Rightarrow> constant_ctx \<Rightarrow> variable_ctx \<Rightarrow> instruction_result" where
"step net cctx vctx = next_state (%a. ()) cctx net (InstructionContinue vctx)"

lemma const_gen_list : "set (genlist (\<lambda>_. a) n) \<subseteq> {a}"
by (induction n, auto)

lemma const_gen_list1 : "set (genlist (\<lambda>_. a) 0) = {}"
by (auto)

lemma const_gen_list2 : "set (genlist (\<lambda>_. a) (Suc n)) = {a}"
by (induction n, auto)

lemma no_jumps :
  "(pcode, c2) = compile_statement c1 st \<Longrightarrow>
   N (Pc JUMP) \<notin> set pcode"
apply (induction st arbitrary: pcode c2 c1)
apply (auto simp add: compile_statement.simps)
(* Blocks*)
subgoal for x pcode c2 c1
apply (case_tac "compile_block c1 x", simp)
apply auto
apply (induction x arbitrary: pcode c2 c1)
  apply auto[1]
apply auto
apply (case_tac "compile_statement c1 a", simp)
apply (case_tac "compile_block ba x", simp)
apply auto
  apply metis
  apply blast
apply (case_tac "ptr b - ptr c1")
apply simp
subgoal for a b nat
using const_gen_list2 [of "N (Stack POP)" "nat"]
  by auto
done
(* others should be similar, pretty tedious *)
oops

lemma no_jumpis :
  "(pcode, c2) = compile_statement c1 st \<Longrightarrow>
   N (Pc JUMPI) \<notin> set pcode"
oops

lemma no_getpc :
  "(pcode, c2) = compile_statement c1 st \<Longrightarrow>
   N (Pc PC) \<notin> set pcode"
oops

(** need to be more precise, where in the program we are *)
lemma relocation :
   "cctx_program cctx1 = compile_program_to c off st \<Longrightarrow>
    cctx_program cctx2 = compile_program_to c (off+n) st \<Longrightarrow>
    step net cctx1 vctx = step net cctx2 (vctx\<lparr> vctx_pc := vctx_pc vctx + int n  \<rparr>)"
oops

(* The stack will be unchanged, except there will be breaks ... *)

definition will_fail :: "network \<Rightarrow> constant_ctx \<Rightarrow> variable_ctx \<Rightarrow> bool" where
"will_fail net cctx vctx =
 (\<exists>k stopper a b c. program_sem stopper cctx k net (InstructionContinue vctx) = InstructionToEnvironment a c b)"

definition compiled_at :: "context0 \<Rightarrow> constant_ctx \<Rightarrow> nat \<Rightarrow> statement \<Rightarrow> context0 \<Rightarrow> bool" where
"compiled_at c cctx offset st c2 = (
   let prog = program_content (cctx_program cctx) in
   let st = elim_forloop_init st in
   let (code, c2') = compile_statement c st in
   let code = handle_labels offset code in
   c2' = c2 \<and> (\<forall>i. i < length code \<longrightarrow> prog (int (i+offset)) = Some (code!i)))"

(* ptr is actually the stack limit? *)
lemma correctness :
  "compiled_at c cctx off st c2 \<Longrightarrow>
   eq_context jst vctx \<Longrightarrow>
   eq_stack (jst,jst_map) (vctx,compile_map) \<Longrightarrow>
   will_fail net cctx vctx \<or>
   (\<exists>k m. program_sem stopper cctx k net (InstructionContinue vctx) = InstructionContinue v2 \<and>
   eval_statement jst jst_map st m = Normal (jst2, jst_map2, mode) \<and>
   eq_stack (jst2,jst_map2) (v2,compile_map2) \<and> eq_context jst2 v2 \<and>
   drop (ptr c) (vctx_stack vctx) = drop (ptr c2) (vctx_stack v2))"
oops

end

