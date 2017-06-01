theory "HoareCFG"

imports "HoareTripleForInstructions"

begin
type_synonym position = "int * int"
type_synonym pred = "(position state_element set \<Rightarrow> bool)"

(* To be completed *)
inductive triple_inst :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
  inst_push_n : "triple_inst (\<langle> h \<le> 1023 \<and> length lst > 0 \<and> 32 \<ge> length lst\<rangle> **
                       continuing **
                       program_counter (n,m) **
                       stack_height h **
                       gas_pred g **
                       rest
                      )
                      ((n,m), Stack (PUSH_N lst))
                      (continuing **
                       program_counter (n,m + 1 + int (length lst)) **
                       stack_height (Suc h) **
                       gas_pred (g - Gverylow) **
                       stack h (word_rcat lst) **
                       rest
                      )"
| inst_stop : "triple_inst 
          (\<langle> h \<le> 1024 \<rangle> \<and>* \<langle> 0 \<le> g \<rangle> ** continuing ** program_counter (n,m) ** stack_height h ** gas_pred g ** rest)
          ((n,m), Misc STOP)
          (stack_height h ** not_continuing ** program_counter (n,m) ** action (ContractReturn []) ** gas_pred g ** rest )"
| inst_jumpdest : "triple_inst (\<langle> h \<le> 1024 \<rangle> **
                       continuing ** 
                       program_counter (n,m) **
                       stack_height h **
                       gas_pred g **
                       rest
                      )
                      (_, Pc JUMPDEST)
                      (continuing **
                       program_counter (n,m + 1) **
                       stack_height h **
                       gas_pred (g - Gjumpdest) **
                       rest
                      )"
| inst_strengthen_pre: "triple_inst p i q \<Longrightarrow> (\<And>s. r s \<longrightarrow> p s) \<Longrightarrow> triple_inst r i q"
| inst_false_pre: "triple_inst \<langle>False\<rangle> i post"

inductive triple_seq :: "pred \<Rightarrow> vertex \<Rightarrow> pred \<Rightarrow> bool" where
  seq_inst : "
  \<lbrakk> triple_inst pre x q;
    triple_seq q (n, xs, ty) post \<rbrakk>
  \<Longrightarrow> triple_seq pre (n, x#xs, ty) post"
| seq_no : "triple_seq (p ** rest) (n, [], No) p"
| seq_next : "triple_seq pre (n, [], Next) pre"
| seq_jump : "(\<And>s. pre s \<longrightarrow> post s) \<Longrightarrow>
   triple_seq pre (n, [], Jump) post"
| seq_jumpi : "
   (\<And>s. pre s \<longrightarrow> post s) \<Longrightarrow>
   triple_seq pre (n, [], Jumpi) post"
| seq_weaken_post : "triple_seq pre a post \<Longrightarrow> (\<And>s. post s \<longrightarrow> q s) \<Longrightarrow> triple_seq pre a q "
| seq_strengthen_pre: "triple_seq p i q \<Longrightarrow> (\<And>s. r s \<longrightarrow> p s) \<Longrightarrow> triple_seq r i q" 
| seq_false_pre: "triple_seq \<langle>False\<rangle> i post"

inductive triple_cfg :: "cfg \<Rightarrow> pred \<Rightarrow> vertex \<Rightarrow> pred \<Rightarrow> bool" where
  cfg_no : " triple_seq pre (n, insts, No) post
  \<Longrightarrow> triple_cfg cfg pre (n, insts, No) post"
| cfg_next : " 
  \<lbrakk> cfg_edges cfg n = Some (i,_);
    cfg_blocks cfg i = Some block;
    triple_seq pre (n, insts, Next) (program_counter (n,m) ** q);
    triple_cfg cfg (program_counter (i,0) ** q) block post\<rbrakk>
  \<Longrightarrow> triple_cfg cfg pre (n, insts, Next) post"
| cfg_jump : " 
  \<lbrakk> cfg_edges cfg n = Some (i,_);
    cfg_blocks cfg i = Some block;
    triple_seq pre (n, insts, Jump) 
      (\<langle> h \<le> 1023 \<rangle> **
       stack_height (Suc h) **
       stack h _ **
       gas_pred g **
       continuing **
       program_counter (n,m) **
       rest
      );
    triple_cfg cfg 
      (stack_height h **
       gas_pred (g - Gmid) **
       continuing **
       program_counter (i,0) **
       rest
      ) block post\<rbrakk>
  \<Longrightarrow> triple_cfg cfg pre (n, insts, Jump) post"
| cfg_jumpi : " 
  \<lbrakk> cfg_edges cfg n = Some (i, Some j);
    cfg_blocks cfg i = Some blocki;
    cfg_blocks cfg j = Some blockj;
    triple_seq pre (n, insts, Jumpi) 
        ((\<langle> h \<le> 1022  \<rangle> **
         stack_height (Suc (Suc h)) **
         stack (Suc h) d **
         stack h cond **
         gas_pred g **
         continuing **
         program_counter (n,m) **
          rest
        ));
    r = (stack_height h **
         gas_pred (g - Ghigh) **
         continuing **
          rest
        );
    (cond = 0 \<Longrightarrow> triple_cfg cfg (r ** program_counter (i,0)) blocki post);
    (cond \<noteq> 0 \<Longrightarrow> triple_cfg cfg (r ** program_counter (j,0)) blockj post)
\<rbrakk>
  \<Longrightarrow> triple_cfg cfg pre (n, insts, Jumpi) post"
| cfg_false_pre: "triple_cfg cfg \<langle>False\<rangle> i post"

definition wf_program_cfg :: "position program \<Rightarrow> bool" where
"wf_program_cfg p =
	(\<forall>m n i. program_advance_pc p (m,n) i = (m,n + i))"

definition wf_cctx_cfg :: "position constant_ctx \<Rightarrow> bool" where
"wf_cctx_cfg c = wf_program_cfg (cctx_program c)"

lemma advance_pc_change_cfg :
" wf_program_cfg p \<Longrightarrow>
	(\<forall>a n. program_advance_pc p
			a (inst_size n) \<noteq> a) "
apply(simp add: wf_program_cfg_def)
done

definition triple_inst_sem :: "pred \<Rightarrow> pos_inst \<Rightarrow> pred \<Rightarrow> bool" where
"triple_inst_sem pre inst post ==
    \<forall> co_ctx presult rest stopper.
				no_assertion co_ctx \<longrightarrow>
				wf_cctx_cfg co_ctx \<longrightarrow>
       (pre ** code {inst} ** rest) (instruction_result_as_set co_ctx presult) \<longrightarrow>
       ((post ** code {inst} ** rest) (instruction_result_as_set co_ctx (program_sem stopper co_ctx 1 presult)))"

lemma inst_strengthen_pre_sem:
  assumes  "triple_inst_sem P c Q"
  and      "(\<forall> s. R s \<longrightarrow> P s)"
  shows    " triple_inst_sem R c Q"
  using assms(1)
  apply (simp add: triple_inst_sem_def)
  apply(clarify)
  apply(drule_tac x = co_ctx in spec)
  apply(simp)
  apply(drule_tac x = presult in spec)
  apply(drule_tac x = rest in spec)
  apply simp
  apply (erule impE)
   apply (sep_drule assms(2)[rule_format])
   apply assumption
  apply simp
done

lemma inst_false_pre_sem:
  "triple_inst_sem \<langle>False\<rangle> i q"
apply(simp add: triple_inst_sem_def sep_basic_simps pure_def)
done

lemmas as_set_simps =
balance_as_set_def contract_action_as_set_def annotation_failure_as_set
contexts_as_set_def constant_ctx_as_set_def memory_as_set_def storage_as_set_def
data_sent_as_set_def log_as_set_def stack_as_set_def instruction_result_as_set_def
program_as_set_def

lemmas sep_tools_simps = 
sep_emp emp_sep sep_true pure_sepD pure_sep sep_lc sep_three 
 imp_sepL sep_impL

lemmas sep_fun_simps = 
caller_sep  sep_caller sep_caller_sep
balance_sep sep_balance sep_balance_sep
not_continuing_sep sep_not_continuing_sep
this_account_sep sep_this_account sep_this_account_sep
action_sep sep_action sep_action_sep
memory8_sepD memory8_sepI memory8_sep_h_cancelD sep_memory8 sep_memory8_sep memory8_sep
memory_usage_sep sep_memory_usage sep_memory_usage_sep
memory_range_sep sep_memory_range
contiuning_sep sep_continuing_sep
gas_pred_sep sep_gas_pred 
gas_any_sep sep_gas_any_sep
program_counter_sep sep_program_counter sep_program_counter_sep
stack_height_sep sep_stack_height sep_stack_height_sep
stack_sep sep_stack sep_stack_sep
block_number_pred_sep sep_block_number_pred_sep
sep_log_numberI sep_log_number_h_cancelD sep_log_numberD
sep_log_number_sep sep_log_number_sep_weak sep_logged
storage_sep sep_storage
code_sep sep_code sep_sep_code sep_code_sep

lemmas inst_numbers_simps =
dup_inst_numbers_def storage_inst_numbers.simps stack_inst_numbers.simps 
pc_inst_numbers.simps info_inst_numbers.simps inst_stack_numbers.simps 
arith_inst_numbers.simps 

lemmas stack_nb_simps=
stack_0_0_op_def stack_0_1_op_def stack_1_1_op_def
stack_2_1_op_def stack_3_1_op_def

lemmas gas_value_simps =
Gjumpdest_def Gzero_def Gbase_def Gcodedeposit_def Gcopy_def
Gmemory_def Gverylow_def Glow_def Gsha3word_def Gcall_def
Gtxcreate_def Gtxdatanonzero_def Gtxdatazero_def Gexp_def
Ghigh_def Glogdata_def Gmid_def Gblockhash_def Gsha3_def
Gsreset_def Glog_def Glogtopic_def  Gcallstipend_def Gcallvalue_def
Gcreate_def Gnewaccount_def Gtransaction_def Gexpbyte_def
Gsset_def Gsuicide_def Gbalance_def Gsload_def Gextcode_def

lemmas instruction_sem_simps =
instruction_sem_def
stack_0_0_op_def stack_0_1_op_def stack_1_1_op_def
stack_2_1_op_def stack_3_1_op_def
subtract_gas.simps meter_gas_def C_def Cmem_def
new_memory_consumption.simps thirdComponentOfC_def 
vctx_next_instruction_default_def vctx_next_instruction_def
check_resources_def

lemmas simp_for_triples = 
  instruction_failure_result_def 
 blockedInstructionContinue_def vctx_pop_stack_def 
 general_dup_def  

lemma inst_stop_sem:
"triple_inst_sem
        (\<langle> h \<le> 1024 \<rangle> \<and>* \<langle> 0 \<le> g \<rangle> \<and>*
         continuing \<and>*
         program_counter (n,m) \<and>* stack_height h \<and>* gas_pred g \<and>* rest)
        ((n,m), Misc STOP)
        (stack_height h \<and>*
         not_continuing \<and>*
         program_counter (n,m) \<and>* action (ContractReturn []) \<and>* gas_pred g \<and>* rest)"
apply(simp add: triple_inst_sem_def program_sem.simps as_set_simps sep_conj_ac)
apply(clarify)
apply(simp split: instruction_result.splits)
 apply(simp add: vctx_next_instruction_def)
 apply(split option.splits)
 apply(simp add: sep_conj_commute[where P="rest"] sep_conj_assoc)
 apply(clarsimp)
 apply(rule conjI)
  apply(clarsimp split: option.splits)
 apply(rule allI)
 apply(rule conjI)
  apply(rule impI)
  apply(rule conjI)
   apply(rule impI)
   apply(rule impI)
   apply(simp split: option.splits)
    apply(clarify)
    apply(rule conjI)
     apply(simp add: instruction_sem_simps stop_def)
    apply(rule conjI)
     apply(simp add: instruction_sem_simps stop_def)
    apply(simp add: instruction_sem_simps stop_def gas_value_simps inst_numbers_simps)
    apply(simp add: sep_not_continuing_sep sep_action_sep del:sep_program_counter_sep)
    apply(sep_select 3;simp only:sep_fun_simps;simp)
   apply(rule conjI)
    apply(rule allI;clarify)
    apply(simp add: instruction_sem_simps stop_def inst_numbers_simps)
   apply(rule conjI)
    apply(simp only: sep_fun_simps)
    apply(simp add: instruction_sem_simps stop_def )
   apply(simp add: instruction_sem_simps stop_def  gas_value_simps)
   apply(clarsimp)
   apply(simp add: sep_not_continuing_sep sep_action_sep del:sep_program_counter_sep)
   apply(sep_select 3;simp only:sep_fun_simps;simp)
  apply(rule impI)
  apply(rule impI)
  apply(simp split:option.splits; clarify)
   apply(simp add: check_resources_def inst_numbers_simps)
  apply(simp add: check_resources_def inst_numbers_simps)
 apply(rule impI)
 apply(rule conjI)
  apply(rule impI)
  apply(rule impI)
  apply(simp split:option.splits; clarify)
   apply(simp add: check_resources_def inst_numbers_simps)
  apply(simp add: check_resources_def inst_numbers_simps)
 apply(rule impI)
 apply(rule impI)
 apply(simp split:option.splits; clarify)
 apply(simp add: instruction_sem_simps stop_def  gas_value_simps)
 apply(simp add: check_resources_def inst_numbers_simps)
 apply(subgoal_tac "meter_gas (Misc STOP) x1 co_ctx = 0")
  apply(simp)
 apply(simp add: instruction_sem_simps gas_value_simps)
done

lemma inst_push_sem:
"triple_inst_sem
        (\<langle> h \<le> 1023 \<and> 0 < length lst \<and> length lst \<le> 32 \<rangle> \<and>*
         continuing \<and>*
         program_counter (n, m) \<and>*
         stack_height h \<and>* gas_pred g \<and>* rest)
        ((n, m), Stack (PUSH_N lst))
        (continuing \<and>*
         program_counter (n, m + 1 + int (length lst)) \<and>*
         stack_height (Suc h) \<and>*
         gas_pred (g - Gverylow) \<and>*
         stack h (word_rcat lst) \<and>* rest)"
sorry

lemma inst_jumpdest_sem:
"triple_inst_sem
        (\<langle> h \<le> 1024 \<rangle> \<and>*
         continuing \<and>*
         program_counter (n, m) \<and>*
         stack_height h \<and>* gas_pred g \<and>* rest)
        (uu, Pc JUMPDEST)
        (continuing \<and>*
         program_counter (n, m + 1) \<and>*
         stack_height h \<and>* gas_pred (g - Gjumpdest) \<and>* rest)"
sorry

lemma inst_soundness:
  "triple_inst p i q \<Longrightarrow> triple_inst_sem p i q"
  apply(induction rule:triple_inst.induct)
      apply(simp only: inst_push_sem)
     apply(simp only: inst_stop_sem)
    apply(simp only: inst_jumpdest_sem)
   apply(simp add: inst_strengthen_pre_sem)
  apply(simp add: inst_false_pre_sem)
done

end