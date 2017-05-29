theory "CFGExamples"

imports "../Hoare/HoareCFG"
begin

lemmas evm_fun_simps = inst_stack_numbers.simps stack_inst_code.simps inst_size_def inst_code.simps 
pc_inst_numbers.simps 
misc_inst_numbers.simps

lemmas cfg_simps = build_cfg_def update_edges_def byteListInt_def find_block_def deconstruct_def extract_indexes_def

lemmas word_rcat_simps = word_rcat_def bin_rcat_def

lemma pure_true_simps[simp]:
 "(\<langle> True \<rangle> \<and>* R) s = R s"
 "(R \<and>* \<langle> True \<rangle>) s = R s"
"\<langle> True \<rangle> {}"
 apply (simp add: pure_def sep_conj_def emp_def )+
apply (simp add: zero_set_def)
done

lemma pure_false_simps[simp]:
 "(\<langle> False \<rangle> \<and>* R) = \<langle> False \<rangle>"
 "(R \<and>* \<langle> False \<rangle>) = \<langle> False \<rangle>"
 by (rule ext, simp add: pure_def sep_conj_def emp_def )+

lemma word_rcat_eq: "word_rcat [x] = x"
   by (simp add: word_rcat_simps)

(* Example with a Jumpi and a No block *)

lemma word_rcat_1:
"word_rcat [(1::byte)] \<noteq> (0::w256)"
by(auto simp add: word_rcat_simps)

definition c where
"c x = build_cfg [ Stack (PUSH_N [1]), Stack (PUSH_N [8]), Pc JUMPI, Stack (PUSH_N [1]), Misc STOP, Pc JUMPDEST, Stack (PUSH_N [2]), Misc STOP]"

schematic_goal c_val:
 " c x = ?p"
 by(simp add: c_def  word_rcat_simps Let_def evm_fun_simps dropWhile.simps  cfg_simps next_i_def concat_map_def
  split:if_splits nat.splits option.splits )

(* Should not apply any auto. Otherwise, auto simplify with "cond=0" even when it is wrong *)
(* For a jumpif that can be solved statically, it works *)
lemma
notes if_split[ split del ]
shows
 " triple_cfg (c cond)
(continuing ** stack_height 0 ** program_counter (0,0) ** gas_pred 1000)
(the (cfg_blocks (c cond) 0))
(stack 0 (word_rcat [1::byte]) )
"
apply(unfold c_val)
apply (simp)
apply(rule cfg_jumpi)
 apply(simp)
 apply(simp)
 apply(simp)
apply(rule seq_inst)
apply(rule inst_strengthen_pre[OF inst_push_n[where rest=emp]])
 apply(rule impI)
 apply(sep_cancel)+
 apply(simp add: gas_pred_def)
 apply(rule conjI;clarsimp)
 apply(simp)
 apply(simp)
apply(rule seq_inst)
apply(rule inst_strengthen_pre[OF inst_push_n[where rest="stack 0 (word_rcat [1])" 
      and h="Suc 0"]])
 apply(rule impI)
 apply(sep_cancel)+
 apply(simp add: program_counter_def)
apply(rule seq_jumpi)
 apply(rule impI)
 apply (sep_select 5)
apply(sep_cancel)+
apply (subst sep_emp)
apply (simp add: program_counter_def)
apply(rule conjI; clarsimp)
apply(simp)
apply(simp)
apply(simp)
apply(simp add: word_rcat_1)
apply(rule cfg_no)
apply(rule seq_inst)
apply(rule inst_strengthen_pre[OF inst_push_n[where h="0" and rest=emp and g="(1000 - 2 * Gverylow - Ghigh)"]])
 apply(rule impI)
 apply(sep_cancel)+
 apply(simp add: gas_pred_def)
apply(rule seq_inst)
apply(rule inst_strengthen_pre[OF inst_stop[where h="Suc 0" and rest="stack 0 (word_rcat [1]) \<and>* gas_pred (1000 - 2 * Gverylow - Ghigh -
          Gverylow)"]])
 apply(rule impI)
 apply(sep_cancel)+
 apply(simp add: program_counter_def)
 apply(simp)
apply(rule seq_strengthen_pre[OF seq_no])
apply (rule impI)
apply(sep_cancel)+
done

end
