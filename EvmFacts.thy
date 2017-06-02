(*
   Copyright 2017 Sidney Amani
   Copyright 2017 Maksym Bortin

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)
theory EvmFacts
  imports "lem/Evm"
      "Hoare/Hoare"
begin

lemmas gas_simps = Gverylow_def Glow_def Gmid_def Gbase_def Gzero_def Glogtopic_def 
    Gsha3word_def Gsha3_def Gextcode_def Gcopy_def Gblockhash_def Gexpbyte_def Gexp_def
    Gbalance_def Gsload_def Gsreset_def Gsset_def Gjumpdest_def Ghigh_def
    Glogdata_def  Glog_def Gcreate_def Ccall_def 
    Cgascap_def Cextra_def Gnewaccount_def Cxfer_def Cnew_def
    Gcall_def Gcallvalue_def 

lemma log256floor_ge_0:
  "0 \<le> log256floor s"
  apply (induct s rule: log256floor.induct)
  subgoal for x
    by (case_tac "\<not> x \<le> 255")
       (clarsimp simp: log256floor.simps)+
  done
declare  log256floor.simps[simp del ]

lemma Cextra_gt_0:
  "0 < Cextra  a b c"
  by (simp add:  gas_simps)

lemma Cgascap_gt_0:
  "0 \<le> Cgascap net a b c d e"
by (auto simp:gas_simps L_def)

lemma Ccall_gt_0:
  " 0 < Ccall net s0 s1 s2 recipient_empty
            remaining_gas blocknumber"
  unfolding Ccall_def
  using Cextra_gt_0 Cgascap_gt_0
  by (simp add: ordered_comm_monoid_add_class.add_nonneg_pos)

lemma Csuicide_gt_0:
  "Gsuicide blocknumber \<noteq> 0 \<Longrightarrow> 0 < Csuicide recipient_empty blocknumber"
  unfolding Csuicide_def
  by (auto split: if_splits
           simp add: gas_simps Gsuicide_def)

lemma thirdComponentOfC_gt_0:
  "i \<noteq> Misc STOP \<Longrightarrow> i \<noteq> Misc RETURN \<Longrightarrow> (\<forall>v. i \<noteq> Unknown v) \<Longrightarrow>
   i = Misc SUICIDE \<longrightarrow> Gsuicide net \<noteq> 0 \<Longrightarrow>
   i = Misc DELEGATECALL \<longrightarrow> \<not> before_homestead net \<Longrightarrow>
  0 < thirdComponentOfC i s0 s1 s2 s3 recipient_empty orig_val new_val remaining_gas net waht"
  unfolding thirdComponentOfC_def
  apply (case_tac i ; simp add: gas_simps )
            apply fastforce
           apply (case_tac x2; simp add: gas_simps)
          apply (case_tac x3; simp add: gas_simps )
         apply (case_tac x4 ; simp add: gas_simps)
         using log256floor_ge_0[where s="uint s1"]
                 apply (simp add: )
              apply (clarsimp; simp add: word_less_def word_neq_0_conv)
                apply (case_tac x5; simp add: gas_simps)
              apply (case_tac x7; simp add: gas_simps)
                apply (case_tac "s2 = 0" ; auto simp: word_less_def word_neq_0_conv)
                apply (case_tac "s2 = 0" ; auto simp: word_less_def word_neq_0_conv)
              apply (case_tac "s3 = 0" ; auto simp: word_less_def word_neq_0_conv)
            apply (case_tac x8; simp add: gas_simps Csstore_def)
            apply (case_tac x9; simp add: gas_simps Csstore_def)
           apply (case_tac x10; simp add: gas_simps Csstore_def)
          apply ( case_tac x12; case_tac "s1 = 0"; 
             simp add: gas_simps word_less_def word_neq_0_conv)
         apply (clarsimp split: misc_inst.splits)
         apply (rule conjI, clarsimp simp add: gas_simps L_def)
         apply (rule conjI)
          apply (simp add: Ccall_gt_0)+
         apply (clarsimp simp: Csuicide_gt_0 )
         done

lemma Cmem_lift:
  "0 \<le> x \<Longrightarrow> x \<le> y \<Longrightarrow> Cmem x \<le> Cmem y"
  apply (simp add: Cmem_def Gmemory_def)
  apply (case_tac "x = y")
   apply clarsimp
  apply (drule (1) order_class.le_neq_trans)
  apply simp
  apply (rule add_mono, simp)
  apply (rule zdiv_mono1[rotated], simp)
  apply (rule mult_mono ; simp)
  done
    
lemma vctx_memory_usage_never_decreases:
  "vctx_memory_usage var \<le> new_memory_consumption inst var"
  by (case_tac inst)
     (rename_tac x, case_tac x; auto simp add: new_memory_consumption.simps M_def)+
    
lemma meter_gas_gt_0:
  " inst \<noteq> Misc STOP \<Longrightarrow>
    inst \<noteq> Misc RETURN \<Longrightarrow>
    inst \<noteq> Misc SUICIDE \<Longrightarrow>
    inst \<notin> range Unknown \<Longrightarrow>
   0\<le> vctx_memory_usage var \<Longrightarrow>
   0 < meter_gas inst var const"
  using Cmem_lift[OF _ vctx_memory_usage_never_decreases[where inst=inst and var=var]]
  by (simp add: C_def meter_gas_def)
     (fastforce  intro: ordered_comm_monoid_add_class.add_nonneg_pos
          thirdComponentOfC_gt_0)

lemma subtract_gas_lower_gas:
   "subtract_gas m (InstructionContinue var) = InstructionContinue v
    \<Longrightarrow> 0 < m \<Longrightarrow> vctx_gas v < vctx_gas var "
  by (auto simp add: subtract_gas.simps)

lemmas stack_op_simps = stack_0_0_op_def stack_0_1_op_def
   stack_2_1_op_def stack_1_1_op_def stack_3_1_op_def

lemmas op_simps = mstore8_def mload_def sha3_def
  general_dup_def mstore_def swap_def ret_def create_def
  call_def suicide_def calldatacopy_def codecopy_def
  extcodecopy_def sstore_def jump_def jumpi_def
  pc_def pop_def log_def callcode_def delegatecall_def
  
lemmas instruction_sem_simps =
  stack_op_simps instruction_failure_result_def
  subtract_gas.simps vctx_advance_pc_def
  op_simps vctx_update_storage_def
  blocked_jump_def blockedInstructionContinue_def
  strict_if_def vctx_pop_stack_def
  vctx_next_instruction_def 

lemma instruction_sem_not_continuing:
  "\<lbrakk> inst \<in> {Misc STOP, Misc RETURN, Misc SUICIDE} \<union> range Unknown \<rbrakk> \<Longrightarrow>
\<forall>v. instruction_sem var const inst \<noteq> InstructionContinue v"
  apply (case_tac inst; clarsimp simp: instruction_sem_def instruction_failure_result_def subtract_gas.simps)
  subgoal for opcode v
   apply (case_tac opcode; simp add: ret_def suicide_def image_def stop_def instruction_sem_def instruction_failure_result_def subtract_gas.simps split:list.splits)
   done
  done

lemma instruction_sem_continuing:
  "\<lbrakk> instruction_sem var const inst = InstructionContinue v \<rbrakk> \<Longrightarrow>
inst \<notin> {Misc STOP, Misc RETURN, Misc SUICIDE} \<union> range Unknown"
  apply (case_tac inst; clarsimp simp: instruction_sem_def instruction_failure_result_def subtract_gas.simps)
  subgoal for opcode
   apply (case_tac opcode; simp add: ret_def suicide_def image_def stop_def instruction_sem_def instruction_failure_result_def subtract_gas.simps split:list.splits)
   done
  done

lemma inst_sem_gas_consume:
  "instruction_sem var const inst = InstructionContinue v \<Longrightarrow>
   inst \<notin> {Misc STOP, Misc RETURN, Misc SUICIDE} \<union> range Unknown \<Longrightarrow>
   0\<le> vctx_memory_usage var \<Longrightarrow>
  \<not> vctx_gas var \<le> 0 \<Longrightarrow>
  vctx_gas v < vctx_gas var"
  apply (cut_tac meter_gas_gt_0[where inst=inst and var=var and const=const]; simp)
  apply (simp only: instruction_sem_def)
  apply (case_tac inst; clarsimp)
(*
   apply (rename_tac x, case_tac "x"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits if_splits;
           (rename_tac x, case_tac "x"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits if_splits )? )+
  done
*)
             apply (case_tac x2 ; 
          clarsimp simp: instruction_sem_simps
           split:list.splits)
         apply (case_tac x3 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x4 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x5 ; clarsimp simp: instruction_sem_simps split:list.splits)
         apply (case_tac x6 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x7 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
         apply (case_tac x8 ; clarsimp simp: instruction_sem_simps split:list.splits option.splits)
      apply (case_tac x9 ; clarsimp simp: instruction_sem_simps Let_def split:list.splits option.splits pc_inst.splits )
      apply (case_tac x2; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits)
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x21a = 0"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
       apply (case_tac "x2a"; clarsimp simp: instruction_sem_simps Let_def split: pc_inst.splits option.splits)
     apply (case_tac "x10"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits)
     apply (clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x12"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits)
     apply (case_tac "x13"; clarsimp simp: instruction_sem_simps  split: pc_inst.splits option.splits list.splits if_splits)
    done

termination program_sem_t
  apply (relation "measure (\<lambda>(c,ir). nat (case ir of InstructionContinue v \<Rightarrow>  vctx_gas v | _ \<Rightarrow> 0))")
   apply (simp)
  apply clarsimp
  subgoal for const var inst
    apply (case_tac "instruction_sem var const inst" ; simp)
    apply (clarsimp simp add: check_resources_def prod.case_eq_if )
     apply (frule instruction_sem_continuing)
     apply (erule (3) inst_sem_gas_consume)
    done
  done

    
lemma program_sem_no_gas_not_continuing:
  "\<lbrakk>vctx_gas var \<le> 0 ; 0\<le> vctx_memory_usage var \<rbrakk> \<Longrightarrow>
\<forall>v. program_sem_t const (InstructionContinue var) \<noteq> InstructionContinue v"
  apply (clarsimp simp add: check_resources_def prod.case_eq_if  split:option.split)
  apply (drule instruction_sem_continuing)
  subgoal for inst
  using meter_gas_gt_0[where inst=inst and var=var and const=const]
  apply simp
  done
 done

declare program_sem_t.simps[simp del]
declare next_state_def[simp del]

lemma program_sem_t_imp_program_sem:
  shows
 "\<exists>k. program_sem_t const ir = program_sem (\<lambda>_. ()) const k ir"
  apply (induct rule:program_sem_t.induct)
  apply (case_tac p)
      apply clarify
      apply (rename_tac c p inst)
      apply (drule_tac x=inst in meta_spec)
      apply (case_tac "vctx_next_instruction inst c", simp add: vctx_next_instruction_def split:option.splits)
      apply (rename_tac nxt_inst)
      apply (drule_tac x="nxt_inst" in meta_spec)
      apply (erule meta_impE , simp)
      apply (subst program_sem_t.simps)
      apply (simp only: instruction_result.simps)
      apply (split if_split)
      apply (rule conjI)
       apply clarify
       apply (rule exI[where x="Suc 0"])
       apply (simp add: program_sem.simps next_state_def split: if_split)
      apply (rule impI)
      apply (simp only: option.simps split:if_split)
      apply (rule impI | rule conjI)+
      apply (rule exI[where x="Suc 0"])
         apply (simp add: program_sem.simps next_state_def)
    apply (rule impI)
      apply (rule exI[where x="Suc 0"])
        apply (simp add: program_sem.simps next_state_def)
       apply (rule impI | rule conjI)+
        apply (erule meta_impE, simp)+
        apply clarsimp
        apply (rule_tac x="Suc k" in exI)
        apply (simp add: program_sem.simps next_state_def )
       apply clarsimp
       apply (rule exI[where x="Suc 0"])
      apply (simp add: program_sem.simps next_state_def)
      apply (rule impI | rule conjI)+
      apply clarsimp
        apply (rule exI[where x="Suc 0"])
        apply (simp add: program_sem.simps next_state_def)
      apply clarsimp
        apply (rule exI[where x="Suc 0"])
        apply (simp add: program_sem.simps next_state_def)
      apply (rule impI | rule conjI)+
      apply clarsimp
        apply (rule_tac x="Suc k" in exI)
        apply (simp add: program_sem.simps next_state_def)
      apply clarsimp
        apply (rule exI[where x="Suc 0"])
        apply (simp add: program_sem.simps next_state_def)
  
      apply clarsimp
        apply (rule exI[where x="Suc 0"])
        apply (simp add: program_sem_t.simps program_sem.simps next_state_def)
      apply clarsimp
            apply (rule exI[where x="Suc 0"])
         apply (simp add: program_sem.simps program_sem_t.simps next_state_def)
  done
    
definition hoare_triple ::
 "[failure_reason set, state_element set \<Rightarrow> bool,
   (int * inst) set, state_element set \<Rightarrow> bool] \<Rightarrow> bool"
 ("_ \<turnstile> \<lbrace>_\<rbrace> _ \<lbrace>_\<rbrace>" [81,81,81,81] 100)
where
  "hoare_triple F P c Q \<equiv>
    \<forall>const ir rest. no_assertion const \<longrightarrow>
       (P ** code c ** rest) (instruction_result_as_set const ir) \<longrightarrow>
         (((Q ** code c ** rest) (instruction_result_as_set const (program_sem_t const ir)))
         \<or> failed_for_reasons F (program_sem_t const ir))"

lemma diff_diff_union:
  "S - A - B = S - (A \<union> B)"
  by blast
    
lemma Collect_union_disj_pair:
 "{P x y | x y. (x,y) \<in> c1} \<union> {P x y |x y. (x,y) \<in> c2} = {P x y|x y.  (x,y) \<in> c1 \<or> (x,y) \<in> c2}"
  by blast
    
lemma hoare_comp:
   "F \<turnstile> \<lbrace>P\<rbrace> c1 \<lbrace>R\<rbrace> \<Longrightarrow> F \<turnstile> \<lbrace>R\<rbrace> c2 \<lbrace>Q\<rbrace> \<Longrightarrow> c = c1 \<union> c2 \<Longrightarrow> c1 \<inter> c2 = {} \<Longrightarrow>  F \<turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"
  apply (simp add: hoare_triple_def)
  apply clarsimp
  apply (drule_tac x=const in spec)+
  apply clarsimp
  apply (drule_tac x=ir and y="code c2 ** rest" in spec2)
  apply clarsimp
  apply (drule mp)
  apply (rule conjI)
    apply fastforce
  apply (rule conjI)
    apply fastforce
   apply (subst diff_diff_union)
   apply (subst Collect_union_disj_pair)
   apply simp
  apply clarsimp
  apply (drule_tac x="program_sem_t const ir" in spec)
  apply (drule_tac x="rest ** code c1" in spec)
  apply (drule mp)
  apply (rule conjI)
    apply blast
  defer
   apply (rule conjI)
    apply (subst Collect_union_disj_pair[symmetric])
     apply (subst (asm) Diff_triv ) back back back
     oops   
end
