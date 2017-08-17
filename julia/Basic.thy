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

end
