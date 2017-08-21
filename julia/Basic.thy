theory Basic
  imports "../lem/Compiler"
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
  eq_memory (memory a) (vctx_memory b) \<and>
  eq_storage (storage (accounts a (address a))) (vctx_storage b)
)"

definition eq_ccontext :: "state \<Rightarrow> constant_ctx \<Rightarrow> bool" where
"eq_ccontext a b = (
   address a = uint (cctx_this b) \<and>
   ( case code (accounts a (address a)) of
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

end
