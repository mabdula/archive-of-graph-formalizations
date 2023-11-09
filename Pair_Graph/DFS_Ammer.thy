theory DFS_Ammer
  imports Pair_Graph_Specs
begin

datatype 'a tree = Leaf | Node "'a tree" 'a "'a tree"

fun fold_tree where
"fold_tree f Leaf a = a"
| "fold_tree f (Node l x r) a = fold_tree f r (fold_tree f l a)" 

thm fold_tree.induct

term Suc

datatype return = Reachable | NotReachable

record ('ver, 'neighb) DFS_state = stack:: "'ver list" visited:: "'neighb" return:: return
                                   seen:: "'neighb"

locale DFS =
  (*set_ops: Set2 where empty = empty and insert = neighb_insert and isin = neighb_isin +*)
  Graph: Pair_Graph_Specs
    where lookup = lookup +
 set_ops: Set2 neighb_empty neighb_delete _ t_set neighb_inv neighb_insert


for lookup :: "'adj \<Rightarrow> 'a \<Rightarrow> 'neighb option" +

fixes t::"'a"
assumes finite_neighbourhoods:
        "finite (t_set N)"

begin


notation "Graph.neighbourhood" ("\<N>\<^sub>G _" 100)

notation "inter" (infixl "\<inter>\<^sub>G" 100)

notation "diff" (infixl "-\<^sub>G" 100)

notation "union" (infixl "\<union>\<^sub>G" 100)

declare set_ops.set_union[simp] set_ops.set_inter[simp] set_ops.set_diff[simp] set_ops.invar_union[simp]
        set_ops.invar_inter[simp] set_ops.invar_diff[simp]

function (domintros) DFS::"('a, 'neighb) DFS_state \<Rightarrow> ('a, 'neighb) DFS_state" where
  "DFS dfs_state = 
     (case (stack dfs_state) of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          (dfs_state \<lparr>return := Reachable\<rparr>)
        else ((if (\<N>\<^sub>G v -\<^sub>G ((seen dfs_state))) \<noteq> \<emptyset>\<^sub>N then
                  DFS (dfs_state \<lparr>stack := (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state))) # (stack dfs_state),
                                  seen := neighb_insert (sel ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state))) (seen dfs_state)\<rparr>)
                 else DFS (dfs_state \<lparr>stack := stack_tl, visited := neighb_insert v (visited dfs_state)\<rparr>))
              )
      )
     | _ \<Rightarrow> (dfs_state \<lparr>return := NotReachable\<rparr>)
    )"
  by pat_completeness auto

named_theorems call_cond_elims
named_theorems call_cond_intros
named_theorems ret_holds_intros
named_theorems invar_props_intros
named_theorems invar_holds_intros
named_theorems state_rel_intros
named_theorems state_rel_holds_intros

definition "DFS_call_1_conds dfs_state \<equiv> 
    (case stack dfs_state of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          False
        else ((if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) \<noteq> (\<emptyset>\<^sub>N) then
                  True
                 else False)
              )
      )
     | _ \<Rightarrow> False
    )"

lemma DFS_call_1_conds[call_cond_elims]: 
  "DFS_call_1_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    hd (stack dfs_state) \<noteq> t;
    (\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G (seen dfs_state) \<noteq> (\<emptyset>\<^sub>N)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_call_1_conds_def split: list.splits option.splits if_splits)

definition "DFS_upd1 dfs_state \<equiv> (
    let
      N = (\<N>\<^sub>G (hd (stack dfs_state)))
    in
      dfs_state \<lparr>stack := (sel ((N -\<^sub>G (seen dfs_state)))) # (stack dfs_state),
                 seen := neighb_insert (sel (N -\<^sub>G (seen dfs_state))) (seen dfs_state)\<rparr>)" 

definition "DFS_call_2_conds dfs_state \<equiv>
(case stack dfs_state of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          False
        else (
                (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) \<noteq> (\<emptyset>\<^sub>N) then
                  False
                 else True)
              )
      )
     | _ \<Rightarrow> False
    )"

term "{}"

lemma DFS_call_2_conds[call_cond_elims]: 
  "DFS_call_2_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>\<exists>v stack_tl. stack dfs_state = v # stack_tl;
    hd (stack dfs_state) \<noteq> t;
    (\<N>\<^sub>G (hd (stack dfs_state))) -\<^sub>G (seen dfs_state) = (\<emptyset>\<^sub>N)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_call_2_conds_def split: list.splits option.splits if_splits)

definition "DFS_upd2 dfs_state \<equiv> 
  ((dfs_state \<lparr>stack := tl (stack dfs_state), visited := neighb_insert (hd (stack dfs_state)) (visited dfs_state)\<rparr>))"


definition "DFS_ret_1_conds dfs_state \<equiv>
   (case stack dfs_state of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          False
        else (
                (if ((\<N>\<^sub>G v) -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                  False
                 else False)                     
              )
      )
     | _ \<Rightarrow> True
   )"

lemma DFS_ret_1_conds[call_cond_elims]:
  "DFS_ret_1_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_ret_1_conds_def split: list.splits option.splits if_splits)

lemma DFS_call_4_condsI[call_cond_intros]:
  "\<lbrakk>stack dfs_state = []\<rbrakk> \<Longrightarrow> DFS_ret_1_conds dfs_state"
  by(auto simp: DFS_ret_1_conds_def split: list.splits option.splits if_splits)

abbreviation "DFS_ret1 dfs_state \<equiv> (dfs_state \<lparr>return := NotReachable\<rparr>)"

definition "DFS_ret_2_conds dfs_state \<equiv>
   (case stack dfs_state of (v # stack_tl) \<Rightarrow>
       (if v = t then 
          True
        else (
                (if (\<N>\<^sub>G v -\<^sub>G (seen dfs_state)) \<noteq> \<emptyset>\<^sub>N then
                  False
                 else False)
              )
      )
     | _ \<Rightarrow> False
   )"


lemma DFS_ret_2_conds[call_cond_elims]:
  "DFS_ret_2_conds dfs_state \<Longrightarrow> 
   \<lbrakk>\<And>v stack_tl. \<lbrakk>stack dfs_state = v # stack_tl;
    (hd (stack dfs_state)) = t\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> 
   P"
  by(auto simp: DFS_ret_2_conds_def split: list.splits option.splits if_splits)

lemma DFS_ret_2_condsI[call_cond_intros]:
  "\<And>v stack_tl. \<lbrakk>stack dfs_state = v # stack_tl; (hd (stack dfs_state)) = t\<rbrakk> \<Longrightarrow> DFS_ret_2_conds dfs_state"
  by(auto simp: DFS_ret_2_conds_def split: list.splits option.splits if_splits)

abbreviation "DFS_ret2 dfs_state \<equiv> (dfs_state \<lparr>return := Reachable\<rparr>)"

lemma DFS_cases:
  assumes "DFS_call_1_conds dfs_state \<Longrightarrow> P"
      "DFS_call_2_conds dfs_state \<Longrightarrow> P"
      "DFS_ret_1_conds dfs_state \<Longrightarrow> P"
      "DFS_ret_2_conds dfs_state \<Longrightarrow> P"
  shows "P"
proof-
  have "DFS_call_1_conds dfs_state \<or> DFS_call_2_conds dfs_state \<or>
        DFS_ret_1_conds dfs_state \<or> DFS_ret_2_conds dfs_state"
    by (auto simp add: DFS_call_1_conds_def DFS_call_2_conds_def
                        DFS_ret_1_conds_def DFS_ret_2_conds_def
           split: list.split_asm option.split_asm if_splits)
  then show ?thesis
    using assms
    by auto
qed

lemma DFS_simps:
  assumes "DFS_dom dfs_state" 
  shows"DFS_call_1_conds dfs_state \<Longrightarrow> DFS dfs_state = DFS (DFS_upd1 dfs_state)"
      "DFS_call_2_conds dfs_state \<Longrightarrow> DFS dfs_state = DFS (DFS_upd2 dfs_state)"
      "DFS_ret_1_conds dfs_state \<Longrightarrow> DFS dfs_state = DFS_ret1 dfs_state"
      "DFS_ret_2_conds dfs_state \<Longrightarrow> DFS dfs_state = DFS_ret2 dfs_state"
  by (auto simp add: DFS.psimps[OF assms] Let_def
                       DFS_call_1_conds_def DFS_upd1_def DFS_call_2_conds_def DFS_upd2_def
                       DFS_ret_1_conds_def
                       DFS_ret_2_conds_def
            split: list.splits option.splits if_splits)

lemma DFS_induct: 
  assumes "DFS_dom dfs_state"
  assumes "\<And>dfs_state. \<lbrakk>DFS_dom dfs_state;
                        DFS_call_1_conds dfs_state \<Longrightarrow> P (DFS_upd1 dfs_state);
                        DFS_call_2_conds dfs_state \<Longrightarrow> P (DFS_upd2 dfs_state)\<rbrakk> \<Longrightarrow> P dfs_state"
  shows "P dfs_state"
  apply(rule DFS.pinduct)
  subgoal using assms(1) .
  apply(rule assms(2))
  by (auto simp add: DFS_call_1_conds_def DFS_upd1_def DFS_call_2_conds_def DFS_upd2_def Let_def
           split: list.splits option.splits if_splits)

definition "invar_1 dfs_state = neighb_inv (visited dfs_state)"

term DFS.invar_1

lemma invar_1_props[dest!]: "invar_1 dfs_state \<Longrightarrow> neighb_inv (visited dfs_state)"
  by (auto simp: invar_1_def)

lemma invar_1_intro[invar_props_intros]: "neighb_inv (visited dfs_state) \<Longrightarrow> invar_1 dfs_state"
  by (auto simp: invar_1_def)

lemma invar_1_holds_1[invar_holds_intros]: "\<lbrakk>DFS_call_1_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_upd1 dfs_state)"
  by (auto simp: DFS_upd1_def Let_def intro: invar_props_intros)

lemma invar_1_holds_2[invar_holds_intros]: "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_upd2 dfs_state)"
  by (auto simp: DFS_upd2_def intro: invar_props_intros)

lemma invar_1_holds_4[invar_holds_intros]: "\<lbrakk>DFS_ret_1_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_ret1 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_1_holds_5[invar_holds_intros]: "\<lbrakk>DFS_ret_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> invar_1 (DFS_ret2 dfs_state)"
  by (auto simp: intro: invar_props_intros)

declare[[simp_trace_depth_limit=1000]]

lemma invar_1_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state"
   shows "invar_1 (DFS dfs_state)"
  using assms(2)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-4) invar_holds_intros  simp: DFS_simps[OF IH(1)])
qed

definition "invar_1b dfs_state = neighb_inv (seen dfs_state)"

term DFS.invar_1

lemma invar_1b_props[dest!]: "invar_1b dfs_state \<Longrightarrow> neighb_inv (seen dfs_state)"
  by (auto simp: invar_1b_def)

lemma invar_1b_intro[invar_props_intros]: "neighb_inv (seen dfs_state) \<Longrightarrow> invar_1b dfs_state"
  by (auto simp: invar_1b_def)

lemma invar_1b_holds_1[invar_holds_intros]:
 "\<lbrakk>DFS_call_1_conds dfs_state; invar_1b dfs_state\<rbrakk> \<Longrightarrow> invar_1b (DFS_upd1 dfs_state)"
  by (auto simp: DFS_upd1_def Let_def intro: invar_props_intros)

lemma invar_1b_holds_2[invar_holds_intros]: 
"\<lbrakk>DFS_call_2_conds dfs_state; invar_1b dfs_state\<rbrakk> \<Longrightarrow> invar_1b (DFS_upd2 dfs_state)"
  by (auto simp: DFS_upd2_def intro: invar_props_intros)

lemma invar_1b_holds_4[invar_holds_intros]: 
"\<lbrakk>DFS_ret_1_conds dfs_state; invar_1b dfs_state\<rbrakk> \<Longrightarrow> invar_1b (DFS_ret1 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_1b_holds_5[invar_holds_intros]: 
"\<lbrakk>DFS_ret_2_conds dfs_state; invar_1b dfs_state\<rbrakk> \<Longrightarrow> invar_1b (DFS_ret2 dfs_state)"
  by (auto simp: intro: invar_props_intros)

declare[[simp_trace_depth_limit=1000]]

lemma invar_1b_holds: 
   assumes "DFS_dom dfs_state" "invar_1b dfs_state"
   shows "invar_1b (DFS dfs_state)"
  using assms(2)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-4) invar_holds_intros  simp: DFS_simps[OF IH(1)])
qed

definition "invar_2 dfs_state = (Vwalk.vwalk Graph.digraph_abs (rev (stack dfs_state)))"

lemma invar_2_props[dest!]: "invar_2 dfs_state \<Longrightarrow> (Vwalk.vwalk Graph.digraph_abs (rev (stack dfs_state)))"
  by (auto simp: invar_2_def)

lemma invar_2_intro[invar_props_intros]: "Vwalk.vwalk Graph.digraph_abs (rev (stack dfs_state)) \<Longrightarrow> invar_2 dfs_state"
  by (auto simp: invar_2_def)

lemma invar_2_holds_1[invar_holds_intros]:
  assumes "DFS_call_1_conds dfs_state" "invar_1b dfs_state" "invar_2 dfs_state"
  shows "invar_2 (DFS_upd1 dfs_state)"
  using assms
  unfolding DFS_upd1_def Let_def invar_2_def invar_1b_def apply simp
  apply(rule DFS_call_1_conds, simp)
  using Vwalk.vwalk_append2
  by (auto simp add: Graph.are_connected_absD Graph.neighb.choose'' last_rev vwalk_append_single)

lemma invar_2_holds_2[invar_holds_intros]: "\<lbrakk>DFS_call_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (DFS_upd2 dfs_state)"
  by (auto simp: DFS_upd2_def dest!: append_vwalk_pref intro!: invar_props_intros elim: call_cond_elims)

lemma invar_2_holds_4[invar_holds_intros]: "\<lbrakk>DFS_ret_1_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (DFS_ret1 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_2_holds_5[invar_holds_intros]: "\<lbrakk>DFS_ret_2_conds dfs_state; invar_2 dfs_state\<rbrakk> \<Longrightarrow> invar_2 (DFS_ret2 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_2_holds: 
   assumes "DFS_dom dfs_state" "invar_1b dfs_state" "invar_2 dfs_state"
   shows "invar_2 (DFS dfs_state)"
  using assms(2-3)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_simps[OF IH(1)])
qed

definition "invar_2a dfs_state = (set (stack dfs_state) \<subseteq> t_set (seen dfs_state))"

lemma invar_2a_props[dest!]: "invar_2a dfs_state \<Longrightarrow> (set (stack dfs_state) \<subseteq> t_set (seen dfs_state))"
  by (auto simp: invar_2a_def)

lemma invar_2a_intro[invar_props_intros]: 
"(set (stack dfs_state) \<subseteq> t_set (seen dfs_state)) \<Longrightarrow> invar_2a dfs_state"
  by (auto simp: invar_2a_def)

lemma invar_2a_holds_1[invar_holds_intros]:
  assumes "DFS_call_1_conds dfs_state" "invar_1b dfs_state" "invar_2a dfs_state"
  shows "invar_2a (DFS_upd1 dfs_state)"
  using assms
  unfolding DFS_upd1_def Let_def invar_2a_def invar_1b_def apply simp
  apply(rule DFS_call_1_conds, simp)
  using Vwalk.vwalk_append2
  by (auto simp add: Graph.are_connected_absD Graph.neighb.choose'' last_rev vwalk_append_single)

lemma invar_2a_holds_2[invar_holds_intros]:
 "\<lbrakk>DFS_call_2_conds dfs_state; invar_2a dfs_state\<rbrakk> \<Longrightarrow> invar_2a (DFS_upd2 dfs_state)"
  unfolding invar_2a_def DFS_upd2_def 
  by (auto elim!: DFS_call_2_conds)

lemma invar_2a_holds_4[invar_holds_intros]: 
"\<lbrakk>DFS_ret_1_conds dfs_state; invar_2a dfs_state\<rbrakk> \<Longrightarrow> invar_2a (DFS_ret1 dfs_state)"
  by (auto simp: invar_2a_def intro: invar_props_intros)

lemma invar_2a_holds_5[invar_holds_intros]: 
"\<lbrakk>DFS_ret_2_conds dfs_state; invar_2a dfs_state\<rbrakk> \<Longrightarrow> invar_2a (DFS_ret2 dfs_state)"
  by (auto simp: invar_2a_def intro: invar_props_intros)

lemma invar_2a_holds: 
   assumes "DFS_dom dfs_state" "invar_1b dfs_state" "invar_2a dfs_state"
   shows "invar_2a (DFS dfs_state)"
  using assms(2-3)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_simps[OF IH(1)])
qed

definition "invar_2b dfs_state = 
(((set (stack dfs_state) \<union> t_set (visited dfs_state)) = t_set (seen dfs_state)))"

lemma invar_2b_props[dest!]:
 "invar_2b dfs_state \<Longrightarrow> ((set (stack dfs_state) \<union> t_set (visited dfs_state) = t_set (seen dfs_state)))"
  by (auto simp: invar_2b_def)

lemma invar_2b_intro[invar_props_intros]: 
"((set (stack dfs_state) \<union> t_set (visited dfs_state) = t_set (seen dfs_state))) \<Longrightarrow> invar_2b dfs_state"
  by (auto simp: invar_2b_def)

lemma invar_2b_holds_1[invar_holds_intros]:
  assumes "DFS_call_1_conds dfs_state" "invar_1b dfs_state" "invar_2b dfs_state" 
  shows "invar_2b (DFS_upd1 dfs_state)"
  using assms
  unfolding DFS_upd1_def Let_def invar_2b_def invar_1b_def by simp

lemma invar_2b_holds_2[invar_holds_intros]:
 "\<lbrakk>DFS_call_2_conds dfs_state; invar_2b dfs_state; invar_1 dfs_state\<rbrakk>
 \<Longrightarrow> invar_2b (DFS_upd2 dfs_state)"
  unfolding invar_2b_def DFS_upd2_def invar_1_def invar_1b_def
  by(rule DFS_call_2_conds, force+)

lemma invar_2b_holds_4[invar_holds_intros]: 
"\<lbrakk>DFS_ret_1_conds dfs_state; invar_2b dfs_state\<rbrakk> \<Longrightarrow> invar_2b (DFS_ret1 dfs_state)"
  by (auto simp: invar_2b_def intro: invar_props_intros)

lemma invar_2b_holds_5[invar_holds_intros]: 
"\<lbrakk>DFS_ret_2_conds dfs_state; invar_2b dfs_state\<rbrakk> \<Longrightarrow> invar_2b (DFS_ret2 dfs_state)"
  by (auto simp: invar_2b_def intro: invar_props_intros)

lemma invar_2b_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_1b dfs_state" "invar_2b dfs_state"
   shows "invar_2b (DFS dfs_state)"
  using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH invar_holds_intros simp: DFS_simps[OF IH(1)])
qed

definition "invar_2c dfs_state = 
(\<forall> v \<in> t_set (visited dfs_state). \<forall> n. n \<in>\<^sub>G \<N>\<^sub>G v \<longrightarrow>  n \<in>\<^sub>G (seen dfs_state))"

lemma invar_2c_props[dest!]:
 "invar_2c dfs_state \<Longrightarrow> (\<forall> v \<in> t_set (visited dfs_state). \<forall> n. n \<in>\<^sub>G \<N>\<^sub>G v \<longrightarrow>  n \<in>\<^sub>G (seen dfs_state))"
  by (auto simp: invar_2c_def)

lemma invar_2c_intro[invar_props_intros]: 
"(\<forall> v \<in> t_set (visited dfs_state). \<forall> n. n \<in>\<^sub>G \<N>\<^sub>G v \<longrightarrow>  n \<in>\<^sub>G (seen dfs_state))
 \<Longrightarrow> invar_2c dfs_state"
  by (auto simp: invar_2c_def)

lemma invar_2c_holds_1[invar_holds_intros]:
  assumes "DFS_call_1_conds dfs_state" "invar_1b dfs_state" "invar_2c dfs_state" 
  shows "invar_2c (DFS_upd1 dfs_state)"
  using assms
  unfolding DFS_upd1_def Let_def invar_2c_def invar_1b_def by simp

lemma invar_2c_holds_2[invar_holds_intros]:
 "\<lbrakk>DFS_call_2_conds dfs_state; invar_2c dfs_state; invar_1 dfs_state; invar_1b dfs_state\<rbrakk>
 \<Longrightarrow> invar_2c (DFS_upd2 dfs_state)"
  unfolding invar_2c_def DFS_upd2_def invar_1_def invar_1b_def
  by(rule DFS_call_2_conds, force+)

lemma invar_2c_holds_4[invar_holds_intros]: 
"\<lbrakk>DFS_ret_1_conds dfs_state; invar_2c dfs_state\<rbrakk> \<Longrightarrow> invar_2c (DFS_ret1 dfs_state)"
  by (auto simp: invar_2c_def intro: invar_props_intros)

lemma invar_2c_holds_5[invar_holds_intros]: 
"\<lbrakk>DFS_ret_2_conds dfs_state; invar_2c dfs_state\<rbrakk> \<Longrightarrow> invar_2c (DFS_ret2 dfs_state)"
  by (auto simp: invar_2c_def intro: invar_props_intros)

lemma invar_2c_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_1b dfs_state" "invar_2c dfs_state"
   shows "invar_2c (DFS dfs_state)"
  using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH invar_holds_intros simp: DFS_simps[OF IH(1)])
qed

definition "invar_2d dfs_state = (t \<notin> t_set (visited dfs_state))"

lemma invar_2d_props[dest!]:"invar_2d dfs_state \<Longrightarrow> (t \<notin> t_set (visited dfs_state))"
  by (auto simp: invar_2d_def)

lemma invar_2d_intro[invar_props_intros]: "(t \<notin> t_set (visited dfs_state)) \<Longrightarrow> invar_2d dfs_state"
  by (auto simp: invar_2d_def)

lemma invar_2d_holds_1[invar_holds_intros]:
  assumes "DFS_call_1_conds dfs_state"  "invar_2d dfs_state" 
  shows "invar_2d (DFS_upd1 dfs_state)"
  using assms
  unfolding DFS_upd1_def Let_def invar_2d_def invar_1b_def by simp

lemma invar_2d_holds_2[invar_holds_intros]:
 "\<lbrakk>DFS_call_2_conds dfs_state; invar_2d dfs_state; invar_1 dfs_state\<rbrakk>
 \<Longrightarrow> invar_2d (DFS_upd2 dfs_state)"
  unfolding invar_2d_def DFS_upd2_def invar_1_def invar_1b_def
  by(rule DFS_call_2_conds, force+)

lemma invar_2d_holds_4[invar_holds_intros]: 
"\<lbrakk>DFS_ret_1_conds dfs_state; invar_2d dfs_state\<rbrakk> \<Longrightarrow> invar_2d (DFS_ret1 dfs_state)"
  by (auto simp: invar_2d_def intro: invar_props_intros)

lemma invar_2d_holds_5[invar_holds_intros]: 
"\<lbrakk>DFS_ret_2_conds dfs_state; invar_2d dfs_state\<rbrakk> \<Longrightarrow> invar_2d (DFS_ret2 dfs_state)"
  by (auto simp: invar_2d_def intro: invar_props_intros)

lemma invar_2d_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_2d dfs_state"
   shows "invar_2d (DFS dfs_state)"
  using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH invar_holds_intros simp: DFS_simps[OF IH(1)])
qed


\<comment> \<open>Example of funciton package bad ind ppcl?\<close>
(*
definition "invar_3 dfs_state = (\<forall>v \<in> t_set (seen dfs_state). (\<nexists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) )"

lemma invar_3_props[elim!]: "invar_3 dfs_state \<Longrightarrow> (\<lbrakk>\<And>v p. v \<in> t_set (seen dfs_state) \<Longrightarrow> \<not> (Vwalk.vwalk_bet Graph.digraph_abs v p t)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: invar_3_def)

lemma invar_3_intro[invar_props_intros]: "\<lbrakk>\<And>v p. v \<in> t_set (seen dfs_state) \<Longrightarrow>  \<not> (Vwalk.vwalk_bet Graph.digraph_abs v p t)\<rbrakk> \<Longrightarrow> invar_3 dfs_state"
  by (auto simp: invar_3_def)

lemma invar_3_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_call_1_conds state; invar_3 state; invar_2a state; invar_1b state\<rbrakk> 
\<Longrightarrow> invar_3 (DFS_upd1 state)"
  unfolding invar_3_def invar_2a_def invar_1b_def DFS_upd1_def Let_def apply simp
  apply(rule DFS_call_1_conds, simp) apply auto
proof(goal_cases)
  case (1 v stack_tl p)
  define w where "w  = (sel (\<N>\<^sub>G v -\<^sub>G seen state))"
  have "vwalk_bet Graph.digraph_abs v [v, w] w"
    using 1(5,3) unfolding w_def 
    by (metis Diff_iff Graph.are_connected_absD Graph.neighb.choose' Graph.neighbourhood_invars' edges_are_vwalk_bet set_ops.invar_diff set_ops.set_diff)
  hence "vwalk_bet Graph.digraph_abs v p  t"
    using 1(7)
    using "1"(2) "1"(8) vwalk_bet_transitive w_def by fastforce
  then show ?case 
    using 1(2,8) by simp
qed

lemma invar_3_holds_2[invar_holds_intros]: 
"\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_upd2 dfs_state)"
  unfolding invar_3_def DFS_upd2_def invar_1_def
  by(auto intro: DFS_call_2_conds)

lemma invar_3_holds_4[invar_holds_intros]: "\<lbrakk>DFS_ret_1_conds dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_ret1 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_holds_5[invar_holds_intros]: "\<lbrakk>DFS_ret_2_conds dfs_state; invar_3 dfs_state\<rbrakk> \<Longrightarrow> invar_3 (DFS_ret2 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_holds: 
  assumes "DFS_dom dfs_state" "invar_1b dfs_state" "invar_2a dfs_state" 
          "invar_1 dfs_state" "invar_3 dfs_state"
   shows "invar_3 (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-7) invar_holds_intros simp: DFS_simps[OF IH(1)])
qed*)

(*
definition "invar_3b dfs_state = (\<forall> v \<in> t_set (visited dfs_state).
                                  ((\<nexists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) \<and> v \<noteq> t))"

lemma invar_3b_props[elim!]: 
"invar_3b dfs_state \<Longrightarrow> (\<lbrakk>\<And>v p.
 v \<in> t_set (visited dfs_state) \<Longrightarrow> v \<noteq> t \<and> \<not> (Vwalk.vwalk_bet (Graph.digraph_abs ) v p t)\<rbrakk> \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: invar_3b_def)

lemma invar_3b_intro[invar_props_intros]:
 "\<lbrakk>\<And>v p. v \<in> t_set (visited dfs_state) \<Longrightarrow>  v \<noteq> t \<and>
  \<not> (Vwalk.vwalk_bet (Graph.digraph_abs ) v p t)\<rbrakk> \<Longrightarrow> invar_3b dfs_state"
  by (auto simp: invar_3b_def)

lemma invar_3b_holds_1[invar_holds_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state; invar_3b dfs_state\<rbrakk> \<Longrightarrow> invar_3b (DFS_upd1 dfs_state)"
  by (auto simp: Let_def DFS_upd1_def dest!: append_vwalk_pref intro!: invar_props_intros)

lemma invar_3b_holds_2[invar_holds_intros]: 
"\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state; invar_3b dfs_state\<rbrakk> 
\<Longrightarrow> invar_3b (DFS_upd2 dfs_state)"
proof(goal_cases)
  case 1
  note assms=this
  show ?case
  proof(rule DFS_call_2_conds[OF 1(1)], goal_cases)
    case 1
    note expanded = this
    have "vwalk_bet Graph.digraph_abs (hd (stack dfs_state)) p t \<Longrightarrow> False" for p
    proof(goal_cases)
      case 1
      have "length p \<ge> 2" 
        using 1 expanded unfolding vwalk_bet_def 
        using "1" impossible_Cons le_add2 list.size(4) not_less_eq_eq by auto
      then obtain a where "vwalk_bet Graph.digraph_abs (hd (stack dfs_state)) 
                      [hd (stack dfs_state), a] a"
                     "vwalk_bet Graph.digraph_abs a (tl p) t"
        by (metis "1" edges_are_vwalk_bet expanded(2) list.sel(3) vwalk_betE)
      moreover hence "a \<in>\<^sub>G \<N>\<^sub>G (hd (stack dfs_state))"
        by (simp add: Graph.are_connected_absI edge_iff_vwalk_bet)
      moreover hence "a \<in> t_set (visited dfs_state)" 
        using expanded
    show ?case 
    proof(cases p)
  qed
  show ?case
    apply(rule invar_3b_intro)
    unfolding DFS_upd2_def apply simp
qed

  by (auto simp: Let_def DFS_upd2_def  elim: vwalk_betE  dest!:
 Graph.neighb.emptyD append_vwalk_pref intro!: invar_props_intros elim!:
 DFS_call_2_conds; erule vwalk_betE)+
  oops

lemma invar_3b_holds_4[invar_holds_intros]: 
"\<lbrakk>DFS_ret_1_conds dfs_state; invar_3b dfs_state\<rbrakk> \<Longrightarrow> invar_3b (DFS_ret1 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3b_holds_5[invar_holds_intros]: 
"\<lbrakk>DFS_ret_2_conds dfs_state; invar_3b dfs_state\<rbrakk> \<Longrightarrow> invar_3b (DFS_ret2 dfs_state)"
  by (auto simp: intro: invar_props_intros)

lemma invar_3_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_3 dfs_state"
   shows "invar_3 (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-5) invar_holds_intros simp: DFS_simps[OF IH(1)])
qed
*)
(*
abbreviation "seen_verts dfs_state \<equiv> (set (stack dfs_state) \<union> t_set (visited dfs_state))"

definition "state_rel_1 dfs_state_1 dfs_state_2 
              \<equiv> seen_verts dfs_state_1 \<subseteq> seen_verts dfs_state_2"

lemma state_rel_1_props[elim!]: "state_rel_1 dfs_state_1 dfs_state_2 \<Longrightarrow>
                                  (seen_verts dfs_state_1 \<subseteq> seen_verts dfs_state_2 \<Longrightarrow> P) \<Longrightarrow> P "
  by (auto simp: state_rel_1_def)

lemma state_rel_1_intro[state_rel_intros]: "\<lbrakk>seen_verts dfs_state_1 \<subseteq> seen_verts dfs_state_2\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state_1 dfs_state_2"
  by (auto simp: state_rel_1_def)

lemma state_rel_1_trans:
  "\<lbrakk>state_rel_1 dfs_state_1 dfs_state_2; state_rel_1 dfs_state_2 dfs_state_3\<rbrakk> \<Longrightarrow>
   state_rel_1 dfs_state_1 dfs_state_3"
  by (auto intro!: state_rel_intros)

lemma state_rel_1_holds_1[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_upd1 dfs_state)"
  by (auto simp: DFS_upd1_def Let_def intro!: state_rel_intros)

lemma state_rel_1_holds_2[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_2_conds dfs_state; invar_1 dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_upd2 dfs_state)"
  by (auto simp: DFS_upd2_def intro!: state_rel_intros elim: call_cond_elims)

lemma state_rel_1_holds_4[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_ret1 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_1_holds_5[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_2_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_1 dfs_state (DFS_ret2 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_1_holds: 
   assumes "DFS_dom dfs_state" "invar_1 dfs_state"
   shows "state_rel_1 dfs_state (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro: state_rel_1_trans invar_holds_intros state_rel_holds_intros intro!: IH(2-) simp: DFS_simps[OF IH(1)])
qed

definition "state_rel_2 dfs_state_1 dfs_state_2 
              \<equiv> (\<forall>v \<in> set (stack dfs_state_1). ((\<exists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) \<or> v = t) \<longrightarrow> v \<in> set (stack dfs_state_2))"

lemma state_rel_2_props[elim!]: "state_rel_2 dfs_state_1 dfs_state_2 \<Longrightarrow>
                                  \<lbrakk>\<lbrakk>\<And>v.\<lbrakk>v \<in> set (stack dfs_state_1); (\<exists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) \<or> v = t\<rbrakk>
                                    \<Longrightarrow> v \<in> set (stack dfs_state_2)\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P "
  by (auto simp: state_rel_2_def)

lemma state_rel_2_intro[state_rel_intros]: "\<lbrakk>\<And>v. \<lbrakk>v \<in> set (stack dfs_state_1); (\<exists>p. Vwalk.vwalk_bet Graph.digraph_abs v p t) \<or> v = t\<rbrakk>
                                    \<Longrightarrow> v \<in> set (stack dfs_state_2)\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state_1 dfs_state_2"
  by (auto simp: state_rel_2_def)

lemma state_rel_2_trans:
  "\<lbrakk>state_rel_2 dfs_state_1 dfs_state_2; state_rel_2 dfs_state_2 dfs_state_3\<rbrakk> \<Longrightarrow>
   state_rel_2 dfs_state_1 dfs_state_3"
  by (auto intro!: state_rel_intros)

lemma state_rel_2_holds_1[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state (DFS_upd1 dfs_state)"
  by (auto simp: Let_def DFS_upd1_def intro!: state_rel_intros)

lemma state_rel_2_holds_2[state_rel_holds_intros]:
  "\<lbrakk>DFS_call_2_conds dfs_state; invar_1b dfs_state; invar_3 dfs_state\<rbrakk>
      \<Longrightarrow> state_rel_2 dfs_state (DFS_upd2 dfs_state)"
  by (force simp: Let_def DFS_upd2_def intro!: state_rel_intros elim!: DFS_call_2_conds)

lemma state_rel_2_holds_4[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_1_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state (DFS_ret1 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_2_holds_5[state_rel_holds_intros]:
  "\<lbrakk>DFS_ret_2_conds dfs_state\<rbrakk> \<Longrightarrow> state_rel_2 dfs_state (DFS_ret2 dfs_state)"
  by (auto simp: intro!: state_rel_intros)

lemma state_rel_2_holds: 
  assumes "DFS_dom dfs_state" "invar_1 dfs_state" "invar_1b dfs_state" "invar_2a dfs_state" 
             "invar_3 dfs_state"
   shows "state_rel_2 dfs_state (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro: state_rel_2_trans invar_holds_intros state_rel_holds_intros intro!: IH(2-) 
              simp: DFS_simps[OF IH(1)])
qed

lemma DFS_ret_1[ret_holds_intros]: "DFS_ret_1_conds (dfs_state) \<Longrightarrow> DFS_ret_1_conds (DFS_ret1 dfs_state)"
  by (auto simp: elim!: call_cond_elims intro!: call_cond_intros)

lemma ret1_holds:
   assumes "DFS_dom dfs_state" "return (DFS dfs_state) = NotReachable"
   shows "DFS_ret_1_conds (DFS dfs_state)" 
   using assms(2-)
proof(induction  rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    using IH(4)                                                                
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: DFS_simps[OF IH(1)])
qed

lemma DFS_ret_2[ret_holds_intros]: "DFS_ret_2_conds (dfs_state) \<Longrightarrow> DFS_ret_2_conds (DFS_ret2 dfs_state)"
  by (auto simp: elim!: call_cond_elims intro!: call_cond_intros)

lemma ret2_holds:
   assumes "DFS_dom dfs_state" "return (DFS dfs_state) = Reachable"
   shows "DFS_ret_2_conds (DFS dfs_state)" 
   using assms(2-)
proof(induction  rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    using IH(4)                                                                
    by (auto intro: ret_holds_intros intro!: IH(2-) simp: DFS_simps[OF IH(1)])
qed
*)

definition "invar_4 state \<equiv> distinct (stack state)"

lemma invar_4I[invar_props_intros]: "distinct (stack state) \<Longrightarrow> invar_4 state"
  unfolding invar_4_def by simp
lemma invar_4E[invar_props_intros]: "invar_4 state \<Longrightarrow> (distinct (stack state) \<Longrightarrow> P) \<Longrightarrow> P" 
  unfolding invar_4_def by simp

lemma invar_4_holds_1[invar_holds_intros]: 
"\<lbrakk>DFS_call_1_conds dfs_state; invar_4 dfs_state; invar_2a dfs_state; invar_1b dfs_state\<rbrakk> 
  \<Longrightarrow> invar_4 (DFS_upd1 dfs_state)"
  by(force elim!:  DFS_call_1_conds invar_4E intro: invar_4I
        simp add: DFS_upd1_def Let_def invar_2a_def invar_1b_def) 
 
lemma invar_4_holds_2[invar_holds_intros]: 
"\<lbrakk>DFS_call_2_conds dfs_state; invar_4 dfs_state\<rbrakk> \<Longrightarrow> invar_4 (DFS_upd2 dfs_state)"
  by(force elim!:  DFS_call_2_conds invar_4E intro: invar_4I
        simp add: DFS_upd2_def Let_def invar_2a_def invar_1b_def) 

lemma invar_4_holds_4[invar_holds_intros]: 
"\<lbrakk>DFS_ret_1_conds dfs_state; invar_4 dfs_state\<rbrakk> \<Longrightarrow> invar_4 (DFS_ret1 dfs_state)"
  by (auto simp: invar_4_def intro: invar_props_intros)

lemma invar_4_holds_5[invar_holds_intros]: 
"\<lbrakk>DFS_ret_2_conds dfs_state; invar_4 dfs_state\<rbrakk> \<Longrightarrow> invar_4 (DFS_ret2 dfs_state)"
  by (auto simp: invar_4_def intro: invar_props_intros)

lemma invar_4_holds: 
  assumes "DFS_dom dfs_state" "invar_1b dfs_state" "invar_2a dfs_state" 
           "invar_4 dfs_state"
   shows "invar_4 (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: DFS_simps[OF IH(1)])
qed

definition "invar_5 s state \<equiv> 
(t_set (seen state) \<subseteq> insert s {v | v. \<exists> p. Vwalk.vwalk_bet Graph.digraph_abs s p v})"

lemma invar_5I[invar_props_intros]: 
"(t_set (seen state) \<subseteq> insert s  {v | v. \<exists> p. Vwalk.vwalk_bet Graph.digraph_abs s p v}) \<Longrightarrow> invar_5 s state"
  unfolding invar_5_def by simp

lemma invar_5E[invar_props_intros]: "invar_5 s state \<Longrightarrow>
 ((t_set (seen state) \<subseteq> insert s  {v | v. \<exists> p. Vwalk.vwalk_bet Graph.digraph_abs s p v}) \<Longrightarrow> P) \<Longrightarrow> P" 
  unfolding invar_5_def by simp

lemma invar_5_holds_1[invar_holds_intros]: 
"\<lbrakk>DFS_call_1_conds dfs_state; invar_5 s dfs_state; invar_1b dfs_state; invar_2a dfs_state\<rbrakk> 
  \<Longrightarrow> invar_5 s (DFS_upd1 dfs_state)"
  unfolding invar_5_def DFS_upd1_def Let_def invar_1b_def invar_2a_def
proof(rule DFS_call_1_conds, simp, simp, goal_cases)
  case 1
  note case1=this
  have "hd (stack dfs_state) \<in> insert s {uu| uu. \<exists>p. vwalk_bet Graph.digraph_abs s p uu}"
    using 1 by auto
  then obtain p where 
   "vwalk_bet Graph.digraph_abs s p ( hd (stack dfs_state)) \<or> ( hd (stack dfs_state)) = s"
     by auto
  moreover have "vwalk_bet Graph.digraph_abs ( hd (stack dfs_state)) 
        [( hd (stack dfs_state)) ,(sel (\<N>\<^sub>G hd (stack dfs_state) -\<^sub>G seen dfs_state))]
                    (sel (\<N>\<^sub>G hd (stack dfs_state) -\<^sub>G seen dfs_state))"
    using 1 
    by (metis Diff_iff Graph.are_connected_absD Graph.neighb.choose' Graph.neighbourhood_invars'
 edges_are_vwalk_bet set_ops.invar_diff set_ops.set_diff)
  ultimately show ?case 
    by (meson vwalk_bet_transitive)
qed 

lemma invar_5_holds_2[invar_holds_intros]: 
"\<lbrakk>DFS_call_2_conds dfs_state; invar_5 s dfs_state\<rbrakk> \<Longrightarrow> invar_5 s (DFS_upd2 dfs_state)"
  by(force elim!:  DFS_call_2_conds  intro: 
        simp add: DFS_upd2_def Let_def invar_5_def) 

lemma invar_5_holds_4[invar_holds_intros]: 
"\<lbrakk>DFS_ret_1_conds dfs_state; invar_5 s dfs_state\<rbrakk> \<Longrightarrow> invar_5 s (DFS_ret1 dfs_state)"
  by (auto simp: invar_5_def intro: invar_props_intros)

lemma invar_5_holds_5[invar_holds_intros]: 
"\<lbrakk>DFS_ret_2_conds dfs_state; invar_5 s dfs_state\<rbrakk> \<Longrightarrow> invar_5 s (DFS_ret2 dfs_state)"
  by (auto simp: invar_5_def intro: invar_props_intros)

lemma invar_5_holds: 
  assumes "DFS_dom dfs_state" "invar_1b dfs_state" "invar_2a dfs_state" 
           "invar_5 s dfs_state"
   shows "invar_5 s (DFS dfs_state)" 
   using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case IH: (1 dfs_state)
  show ?case
    apply(rule DFS_cases[where dfs_state = dfs_state])
    by (auto intro!: IH(2-) invar_holds_intros simp: DFS_simps[OF IH(1)])
qed

lemma DFS_term_call1: "DFS_call_1_conds state \<Longrightarrow>
                       DFS_dom (DFS_upd1 state) \<Longrightarrow> DFS_dom state"
  by(auto elim!: DFS_call_1_conds intro: DFS.domintros simp add:  DFS_upd1_def Let_def) 

lemma DFS_term_call2: "DFS_call_2_conds state \<Longrightarrow>
                       DFS_dom (DFS_upd2 state) \<Longrightarrow> DFS_dom state"
  apply(rule DFS_call_2_conds, simp)
  unfolding DFS_upd2_def Let_def
  by(rule DFS.domintros, auto) 

lemma card_setminus_less_flip:"finite A \<Longrightarrow> B \<subseteq> A \<Longrightarrow> C \<subseteq> A \<Longrightarrow> card (A - B) < card (A - C) \<longleftrightarrow> card C < card B"
  by (smt (verit) Diff_Diff_Int Diff_subset Int_absorb1 antisym_conv2 card_Diff_subset 
card_mono diff_less_mono2 infinite_super leD)

lemma DFS_term_gen: 
  assumes "finite (insert s {v | v. \<exists> p. Vwalk.vwalk_bet Graph.digraph_abs s p v})"
          "invar_5 s state"
          "remaining = card (insert s {v | v. \<exists> p. Vwalk.vwalk_bet Graph.digraph_abs s p v}-
                             (t_set (seen state)))"
          "invar_1b state" "invar_2a state"
    shows "DFS_dom (state)"
  using assms 
proof(induction remaining arbitrary: state rule: less_induct)
  case (less remaining)
  define remaining' where "remaining' = remaining"
  define state' where "state' = state"
  note Less = less[simplified sym[OF remaining'_def] sym[OF state'_def]]
  define l where "l = length (stack state)"
  show ?case
    using l_def less
  proof(induction l arbitrary: state  rule: less_induct)
    case (less l)
    show ?case 
    proof(rule DFS_cases[of state], goal_cases)
    case 1
    note case1=this
    show ?thesis 
      proof(rule DFS_call_1_conds[OF 1], goal_cases)
        case 1
        have invar5_next: "invar_5 s (DFS_upd1 state)"
          by(auto intro: invar_5_holds_1 simp add: case1 less)
        have invar1b_next: "invar_1b (DFS_upd1 state)"
          by(auto intro: invar_1b_holds_1 simp add: case1 less)
        have invar2a_next: "invar_2a (DFS_upd1 state)"
          by(auto intro: invar_2a_holds_1 simp add: case1 less)
       show ?thesis 
         apply(rule DFS_term_call1[OF case1])
         apply(rule less(3)[OF _ less(4) invar5_next refl invar1b_next invar2a_next])
         using card_setminus_less_flip[OF less(4)] 1 invar5_next finite_neighbourhoods less 
         unfolding invar_5_def DFS_upd1_def Let_def
         by auto
    qed
  next
    case 2
    show ?thesis
      proof(rule DFS_call_2_conds[OF 2], goal_cases)
        case 1
        have invar5_next: "invar_5 s (DFS_upd2 state)"
          by(auto intro: invar_5_holds_2 simp add: 2 less)
        have invar1b_next: "invar_1b (DFS_upd2 state)"
          by(auto intro: invar_1b_holds_2 simp add: 2 less)
        have invar2a_next: "invar_2a (DFS_upd2 state)"
          by(auto intro: invar_2a_holds_2 simp add: 2 less)
        show ?thesis
          apply(rule DFS_term_call2[OF 2])
          unfolding DFS_upd2_def
          apply(rule less(1)[OF _ refl _ _ _ ])
          using less(6) less(2) Less(2) invar5_next invar1b_next invar2a_next 1
          unfolding DFS_upd2_def less(2)
          by (force , intro less(3)[OF _  Less(2) _ refl], auto)   
      qed  
    next
    case 4
    show ?thesis
      by (rule DFS_ret_2_conds[OF 4])
         (rule DFS.domintros, simp, simp)
  next
    case 3
    show ?thesis
      by (rule DFS_ret_1_conds[OF 3])
         (rule DFS.domintros, simp, simp)
  qed 
qed
qed

definition "initial s \<equiv> \<lparr>stack = [s] , visited = \<emptyset>\<^sub>N, 
                         return= undefined, seen = neighb_insert s \<emptyset>\<^sub>N\<rparr> "

lemma DFS_term: 
  assumes "finite (insert s {v | v. \<exists> p. Vwalk.vwalk_bet Graph.digraph_abs s p v})"
  shows "DFS_dom (initial s)"
  apply(rule DFS_term_gen[OF assms _ refl])
  unfolding invar_5_def initial_def invar_1b_def invar_2a_def 
  by auto

lemma invar_1_initial: "invar_1 (initial s)"
  unfolding invar_1_def initial_def by simp

lemma invar_1b_initial: "invar_1b (initial s)"
  unfolding invar_1b_def initial_def by simp

lemma invar_2_initial: "s \<in> dVs Graph.digraph_abs \<Longrightarrow> invar_2 (initial s)"
  unfolding invar_2_def initial_def by simp

lemma invar_2a_initial: "invar_2a (initial s)"
  unfolding invar_2a_def initial_def by simp
(*
lemma invar_3_initial: " \<nexists> p. vwalk_bet Graph.digraph_abs s p t \<Longrightarrow> invar_3 (initial s)"
  unfolding invar_3_def initial_def by simp
*)
lemma invar_4_initial: "invar_4 (initial s)"
  unfolding invar_4_def initial_def by simp

lemma invar_5_initial: "invar_5 s (initial s)"
  unfolding invar_5_def initial_def by simp

lemma DFS_correctness:
  assumes
      "DFS_dom state"
      "stack state \<noteq> []"
      "invar_2 state"
      "invar_1b state"
      "invar_2a state"
      "invar_1 state"
      "(\<nexists> p. vwalk_bet Graph.digraph_abs (last (stack state)) p t) \<and>
            (last (stack state)) \<noteq> t"
    shows "return (DFS state) = NotReachable"
  using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case (1 state)
  note IH =this
  show ?case 
  proof(cases rule: DFS_cases[of state])
    case 1
    note case1=this
    show ?thesis
    proof(rule DFS_call_1_conds[OF 1], goal_cases)
      case 1
      have same_last:"last (stack state) = last (stack (DFS_upd1 state))"
        using IH(4) unfolding DFS_upd1_def Let_def by simp
      have stack_non_empt:"stack (DFS_upd1 state) \<noteq> []"
        using 1 unfolding DFS_upd1_def Let_def by simp
      have no_p:"(\<nexists>p. vwalk_bet Graph.digraph_abs (last (stack (DFS_upd1 state))) p t)"
      proof(simp, rule, rule, goal_cases)
        case (1 p)
        then show ?case 
          apply(subst (asm) sym[OF same_last])
          using IH(9) by simp
      qed
      show ?case 
        apply(subst DFS_simps(1)[OF IH(1) case1])
        apply(rule IH(2)[OF case1 stack_non_empt])
        using no_p same_last IH(9)
        by(auto intro: invar_2_holds_1[OF case1 IH(6) IH(5)]  invar_1b_holds_1[OF case1 IH(6)]
                       invar_2a_holds_1[OF case1 IH(6) IH(7)] invar_1_holds_1[OF case1 IH(8)])
    qed
  next
    case 2
    show ?thesis 
    proof(cases rule: DFS_call_2_conds[OF 2])
      case 1
      note case1 = this
      then obtain v stack_tl where stack_split: "stack state = v # stack_tl" by auto
      show ?thesis
      proof(cases stack_tl)
        case Nil
        show ?thesis 
           apply(subst DFS_simps(2)[OF IH(1) 2])
           unfolding DFS_upd2_def stack_split
           using Nil 
           by(subst DFS.psimps, auto intro: DFS.domintros)         
      next
        case (Cons a list)
        hence last_Same:"last (stack state)= last (stack_tl)"
          by (simp add: stack_split)
        have last_Same':"last (stack_tl) = last (stack (DFS_upd2 state))"
          using stack_split unfolding DFS_upd2_def by simp
        have stack_non_empt: "stack (DFS_upd2 state) \<noteq> []"
          using DFS_simps(2)[OF IH(1) 2] stack_split Cons unfolding DFS_upd2_def by simp
        have no_path: " (\<nexists>p. vwalk_bet Graph.digraph_abs (last (stack (DFS_upd2 state))) p t) "
          using last_Same last_Same' IH(9) by simp
        show ?thesis 
          apply(subst DFS_simps(2)[OF IH(1) 2 ])
          apply(rule IH(3)[OF 2 stack_non_empt])
          using no_path last_Same last_Same' IH(9)
          by(auto intro: invar_2_holds_2[OF 2 IH(5)] invar_1b_holds_2[OF 2 IH(6)]
                         invar_2a_holds_2[OF 2 IH(7)] invar_1_holds_2[OF 2 IH(8)])
      qed
    qed
  next
    case 3
    show ?thesis 
      using IH DFS_ret_1_conds[OF 3] by auto
  next
    case 4
    show ?thesis
    proof(rule DFS_ret_2_conds[OF 4], goal_cases)
      case (1 v stack_tl)
      have "vwalk_bet Graph.digraph_abs (last (stack state))(rev (stack state)) (hd (stack state))"
        unfolding vwalk_bet_def
        using IH(5) 1 last_rev[of "stack state"] hd_rev[of "stack state"]
        unfolding invar_2_def  by simp
      then show ?case 
        using IH(9) 1 by simp
    qed
  qed 
qed 

lemma neighbourhoods_inductive_set:
      assumes "\<And>v n. v \<in> t_set S \<Longrightarrow>  n \<in>\<^sub>G \<N>\<^sub>G v  \<Longrightarrow>  n \<in> t_set  S"
              "vwalk_bet Graph.digraph_abs u P v"
              "u \<in> t_set S"
              "l = length P"
            shows "v \<in> t_set S"
  using assms
proof(induction l arbitrary: P u)
  case 0
  then show ?case unfolding vwalk_bet_def by simp
next
  case (Suc l)
  note cons =  this
  show ?case
  proof(cases P)
    case Nil
    hence "u = v" 
      using cons(3) by blast
    then show ?thesis 
      using cons by simp
  next
    case (Cons b list)
    note cons' = Cons
    show ?thesis 
    proof(cases list)
      case Nil
      hence "u = v" 
        using cons(3) local.Cons by blast
      then show ?thesis using Suc by simp
    next
      case (Cons c listc)
    have  a:"vwalk_bet Graph.digraph_abs c list v"
      by (metis cons' cons(3) list.distinct(1) list.sel(1) local.Cons vwalk_bet_cons vwalk_bet_def)
    have b:"c \<in> t_set S" 
      apply(rule Suc(2)[of u, OF Suc(4)])
      by (metis Graph.are_connected_absI Graph.neighb.set_isin Graph.neighbourhood_invars' 
           cons' cons(3) list.sel(1) local.Cons vwalk_2 vwalk_bet_def)
    show ?thesis 
      apply(rule Suc(1)[of c list])
      using Suc(2) apply fast
      using a apply simp
      using b apply simp
      using cons' cons Cons 
      by (metis length_Cons nat.inject)
  qed
qed
qed


lemma DFS_completeness:
  assumes
      "DFS_dom state"
      "stack state \<noteq> []"
      "invar_2 state"
      "invar_1b state"
      "invar_2a state"
      "invar_1 state"
      "(\<exists> p. vwalk_bet Graph.digraph_abs (last (stack state)) p t) \<or>
            (last (stack state)) = t"
      "invar_2b state"
      "invar_2c state"
      "invar_2d state"
    shows "return (DFS state) = Reachable"
  using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case (1 state)
  note IH =this
  show ?case 
  proof(cases rule: DFS_cases[of state])
    case 1
    note case1=this
    show ?thesis
    proof(rule DFS_call_1_conds[OF 1], goal_cases)
      case 1
      have same_last:"last (stack state) = last (stack (DFS_upd1 state))"
        using IH(4) unfolding DFS_upd1_def Let_def by simp
      have stack_non_empt:"stack (DFS_upd1 state) \<noteq> []"
        using 1 unfolding DFS_upd1_def Let_def by simp
      have ex_p:"(\<exists> p. vwalk_bet Graph.digraph_abs (last (stack (DFS_upd1 state))) p t)
                  \<or> last (stack state) = t"
        using IH(9) same_last  by simp
      show ?case 
        apply(subst DFS_simps(1)[OF IH(1) case1])
        apply(rule IH(2)[OF case1 stack_non_empt])
        using ex_p same_last IH(9) invar_2d_holds_1[OF case1 IH(12)]
        by(auto intro: invar_2_holds_1[OF case1 IH(6) IH(5)]  invar_1b_holds_1[OF case1 IH(6)]
                       invar_2a_holds_1[OF case1 IH(6) IH(7)] invar_1_holds_1[OF case1 IH(8)]
                       invar_2b_holds_1[OF case1 IH(6) IH(10)]
                       invar_2c_holds_1[OF case1 IH(6) IH(11)] )
    qed
  next
    case 2
    show ?thesis 
    proof(cases rule: DFS_call_2_conds[OF 2])
      case 1
      note case1 = this
      then obtain v stack_tl where stack_split: "stack state = v # stack_tl" by auto
      show ?thesis
      proof(cases stack_tl)
        case Nil
        have visited_seen_same: "t_set (visited (DFS_upd2 state)) = t_set (seen (DFS_upd2 state))"
          using  invar_2b_holds_2[OF 2 IH(10) IH(8), simplified invar_2b_def] stack_split
          unfolding DFS_upd2_def Nil by simp
        hence "\<forall>v\<in>t_set (seen (DFS_upd2 state)). \<forall>n. n \<in>\<^sub>G \<N>\<^sub>G v \<longrightarrow> n \<in>\<^sub>G seen (DFS_upd2 state)"         
          using invar_2c_holds_2[OF 2 IH(11) IH(8) IH(6), simplified invar_2c_def] by simp
        hence induct:"(\<And>v n. v \<in> t_set (seen (DFS_upd2 state)) \<Longrightarrow> n \<in>\<^sub>G \<N>\<^sub>G v \<Longrightarrow> n \<in> t_set (seen (DFS_upd2 state)))"
          using "2" Graph.neighb.set_isin  invar_1b_holds_2[OF 2 IH(6)] invar_1b_props by fast
        have "t \<in> t_set (seen (DFS_upd2 state))"
        proof(cases rule: disjE[OF IH(9)])
          case 1
          then obtain P where P_prop:"vwalk_bet Graph.digraph_abs (last (stack state)) P t" by auto
          have "t \<in> t_set (seen (DFS_upd2 state))"
            apply(rule neighbourhoods_inductive_set[of "(seen (DFS_upd2 state))"
                   "(last (stack state))" P t])
            using induct  P_prop  IH(7) stack_split
            unfolding DFS_upd2_def unfolding invar_2a_def by auto
          thus ?thesis
            using visited_seen_same by blast
        next
          case 2
          then show ?thesis 
            using case1 IH(7) unfolding invar_2a_def DFS_upd2_def 
            by force
        qed
          hence "t \<in> t_set (visited state)" 
            using case1 2 invar_2d_holds_2[OF 2] IH(8)  visited_seen_same
            unfolding  invar_2d_def DFS_upd2_def by auto
          hence False using IH(12) unfolding invar_2d_def by simp
          thus ?thesis by simp
      next
        case (Cons a list)
        hence last_Same:"last (stack state)= last (stack_tl)"
          by (simp add: stack_split)
        have last_Same':"last (stack_tl) = last (stack (DFS_upd2 state))"
          using stack_split unfolding DFS_upd2_def by simp
        have stack_non_empt: "stack (DFS_upd2 state) \<noteq> []"
          using DFS_simps(2)[OF IH(1) 2] stack_split Cons unfolding DFS_upd2_def by simp
        have no_path: " (\<exists> p. vwalk_bet Graph.digraph_abs (last (stack (DFS_upd2 state))) p t) \<or>
                        last (stack (DFS_upd2 state)) = t"
          using last_Same last_Same' IH(9) by simp
        show ?thesis 
          apply(subst DFS_simps(2)[OF IH(1) 2 ])
          apply(rule IH(3)[OF 2 stack_non_empt])
          using no_path last_Same last_Same' IH(9) invar_2d_holds_2[OF 2 IH(12) IH(8)]
          by(auto intro: invar_2_holds_2[OF 2 IH(5)] invar_1b_holds_2[OF 2 IH(6)]
                         invar_2a_holds_2[OF 2 IH(7)] invar_1_holds_2[OF 2 IH(8)]
                         invar_2b_holds_2[OF 2 IH(10) IH(8)]
                         invar_2c_holds_2[OF 2 IH(11) IH(8) IH(6)])
      qed
    qed
  next
    case 3
    show ?thesis 
      using IH DFS_ret_1_conds[OF 3] by auto
  next
    case 4
    show ?thesis
      using DFS_simps(4)[OF IH(1) 4] by simp
  qed 
qed

lemma DFS_stack_hd_t:
  assumes "DFS_dom state"
          "return (DFS state) = Reachable"
          "stack state \<noteq> []"
    shows "hd (stack (DFS state)) = t \<and> last (stack (DFS state)) = last (stack state)"
  using assms(2-)
proof(induction rule: DFS_induct[OF assms(1)])
  case (1 state)
  note IH = this
  show ?case 
  proof(cases rule: DFS_cases[of state ])
    case 1
    have same_last:"last (stack (DFS_upd1 state)) =last (stack state)" 
      using DFS_call_1_conds[OF 1] IH(5,4) unfolding DFS_upd1_def Let_def by simp
    show ?thesis 
      apply(subst DFS_simps(1)[OF IH(1) 1])+
      apply(subst sym[OF same_last], rule IH(2)[OF 1])
      using IH(2)[OF 1] IH(5,4) DFS_simps(1)[OF IH(1) 1] 
      unfolding DFS_upd1_def Let_def 
      by auto
  next
    case 2
    show ?thesis
    proof(rule DFS_call_2_conds[OF 2], goal_cases)
      case 1
      then obtain v stack_tl where stack_split: "stack state = v # stack_tl" by auto
      hence hd: "(hd (stack state)) = v" by simp
      show ?case 
      proof(cases stack_tl)
        case Nil
        have final:"DFS (DFS_upd2 state) = DFS_ret1 (DFS_upd2 state)"
         unfolding DFS_upd2_def
         apply((subst stack_split)+, (subst Nil)+, subst DFS_simps(3))
         unfolding DFS_ret_1_conds_def 
         by (auto intro: DFS.domintros)
        show ?thesis 
         using IH(4) final stack_split  DFS_simps(2)[OF IH(1) 2]
         unfolding DFS_upd2_def Nil by auto      
       next
         case (Cons a list)
         have same_last:"last (stack (DFS_upd2 state)) =last (stack state)" 
           using DFS_call_2_conds[OF 2] IH(5,4) Cons stack_split 
           unfolding DFS_upd2_def Let_def by simp
         show ?thesis 
           apply(subst DFS_simps(2)[OF IH(1) 2])+
           apply(subst sym[OF same_last])+
           apply(rule IH(3)[OF 2])
           using DFS_simps(2)[OF IH(1) 2] IH(4)  stack_split Cons 
           unfolding DFS_upd2_def by auto
      qed
    qed
  next
    case 3
    show ?thesis 
      using DFS_ret_1_conds[OF 3] IH by simp
  next
    case 4
    show ?thesis 
      using  DFS_simps(4)[OF IH(1) 4]
      by (auto intro:  DFS_ret_2_conds[OF 4])
  qed
qed


end                                                      
end
