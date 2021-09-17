theory Odd_components
  imports Bipartite
begin

definition odd_components where
  "odd_components E = {C. \<exists> v \<in> Vs E. connected_component E v = C \<and> odd (card C)}"

definition even_components where
  "even_components E = {C. \<exists> v \<in> Vs E. connected_component E v = C \<and> even (card C)}"

definition count_odd_components where
  "count_odd_components E = card (odd_components E)"

definition graph_diff where
  "graph_diff E X = {e. e \<in> E \<and> e \<inter> X = {}}"

definition singleton_in_diff where 
  "singleton_in_diff E X = {a. \<exists> v. a = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)}"

definition diff_odd_components where
  "diff_odd_components E X = (odd_components (graph_diff E X)) \<union> (singleton_in_diff E X)"

definition count_diff_odd_components where
  "count_diff_odd_components E X = card (diff_odd_components E X)"

definition tutte_condition where
  "tutte_condition E \<equiv> \<forall> X \<subseteq> Vs E. card (diff_odd_components E X) \<le> card X"

definition barrier where
  "barrier E X \<equiv> X \<noteq> {} \<and> card (diff_odd_components E X) = card X"

lemma graph_diff_member[iff?]: "e \<in> graph_diff E X \<longleftrightarrow>
   e \<in> E \<and> e \<inter> X = {}"
  unfolding graph_diff_def by simp


lemma graph_diff_elim[elim]:
  assumes "e \<in> graph_diff E X"
  shows "e \<in> E \<and> e \<inter> X = {}"
  using assms 
    by(auto simp: graph_diff_member)


lemma graph_diff_intro[intro]:
  assumes "e \<in> E"
  assumes "e \<inter> X = {}"
  shows "e \<in> graph_diff E X" 
  using assms graph_diff_def by auto

lemma graph_diff_subset: "graph_diff E X \<subseteq> E"
  by (simp add: graph_diff_def)

lemma connected_component_subset:
  assumes "v \<in> Vs E"
  shows "connected_component E v \<subseteq> Vs E"
  using assms by (metis in_connected_component_in_edges subsetI)

lemma diff_connected_component_subset:
  assumes "v \<in> Vs E"
  shows "connected_component (graph_diff E X) v \<subseteq> Vs E" 
  by (meson assms con_comp_subset connected_component_subset dual_order.trans graph_diff_subset)

lemma odd_component_member[iff?]: "C \<in> odd_components E \<longleftrightarrow>
   (\<exists>v \<in> Vs E. connected_component E v = C \<and> odd (card C))"
  unfolding odd_components_def by simp


lemma odd_components_elim[elim]:
  assumes "C \<in> odd_components E" 
  obtains v where "v \<in> Vs E" "connected_component E v = C" "odd (card C)"
  using assms 
    by(auto simp: odd_component_member)


lemma odd_components_intro[intro]:
  assumes "odd (card C)"
  assumes "v \<in> Vs E"
  assumes "connected_component E v = C"
shows "C \<in> odd_components E" 
  using assms odd_components_def by auto

lemma singleton_in_diff_member[iff?]: "C \<in> singleton_in_diff E  X \<longleftrightarrow>
   (\<exists> v. C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X))"
  unfolding singleton_in_diff_def by simp


lemma singleton_in_diff_elim[elim]:
  assumes "C \<in> singleton_in_diff E X" 
  obtains v where "v \<in> Vs E" "C = {v}" "v \<notin> X" "v \<notin> Vs (graph_diff E X)"
  using assms singleton_in_diff_member[of C E X] 
    by(auto simp: singleton_in_diff_member)


lemma singleton_in_diff_intro[intro]:
  assumes "v \<in> Vs E"
  assumes "C = {v}"
  assumes "v \<notin> X"
  assumes "v \<notin> Vs (graph_diff E X)"
shows "C \<in> singleton_in_diff E X" 
  using  assms 
  by (simp add: singleton_in_diff_member)

lemma odd_components_intersection_singletions_empty:
  shows "odd_components (graph_diff E X) \<inter> singleton_in_diff E X = {}"
  using disjoint_iff_not_equal
  by (metis connected_component_subset insert_subset odd_component_member singleton_in_diff_member)

lemma diff_odd_components_member[iff?]:
  "C \<in> diff_odd_components E X \<longleftrightarrow> C \<in> odd_components (graph_diff E X) \<or> C \<in> singleton_in_diff E X"
  by (simp add: diff_odd_components_def)

lemma diff_odd_components_elim[elim]:
  assumes "C \<in> diff_odd_components E X"
  shows "C \<in> odd_components (graph_diff E X) \<or> C \<in> singleton_in_diff E X" 
  by (metis assms diff_odd_components_member)

lemma diff_odd_components_intro[intro]:
  assumes "C \<in> odd_components (graph_diff E X) \<or> C \<in> singleton_in_diff E X"
  shows "C \<in> diff_odd_components E X" 
  by (simp add: assms diff_odd_components_member)

lemma diff_odd_components_intro1[intro]:
  assumes "C \<in> odd_components (graph_diff E X)"
  shows "C \<in> diff_odd_components E X" 
  by (simp add: assms diff_odd_components_member)

lemma diff_odd_components_intro2[intro]:
  assumes " C \<in> singleton_in_diff E X"
  shows "C \<in> diff_odd_components E X" 
  by (simp add: assms diff_odd_components_member)

lemma edge_subset_component:
 assumes "graph_invar E"
  assumes "e \<in> E"
  assumes "v \<in> e"
  shows "e \<subseteq> (connected_component E v)"
  using assms
  by (metis connected_components_member_sym in_con_comp_insert in_own_connected_component
      insertE insert_Diff singletonD subsetI)

lemma edge_in_E_card:
 assumes "graph_invar E"
 assumes "e \<in> E"
 shows "card e = 2" 
  using assms(1) assms(2) by auto

lemma component_is_finite:
  assumes "graph_invar E"
  shows "finite (connected_component E v)"
  by (metis assms connected_component_subset 
      connected_components_notE_singletons finite.simps finite_subset)

lemma connected_component_not_singleton:
  assumes "graph_invar E"
  assumes "v\<in> Vs E"
  shows "card (connected_component E v) > 1"
proof -
  obtain e where "e \<in> E" "v \<in> e" using assms(2) vs_member_elim by metis
  then have "e \<subseteq> (connected_component E v)"
    by (simp add: edge_subset_component assms(1) \<open>v\<in> Vs E\<close>)
  then have "card (connected_component E v) \<ge> 2"
    using edge_in_E_card[of E e] component_is_finite[of E v]  assms(1)
    by (metis \<open>e \<in> E\<close> card_mono)
  then show ?thesis  by linarith
qed


lemma odd_component_is_component:
  assumes "C \<in> odd_components E"
 assumes "x \<in> C"
 shows "connected_component E x = C"
 by (metis assms connected_components_member_eq odd_component_member)

lemma singleton_in_diff_is_component:
  assumes "C \<in> singleton_in_diff E X"
 assumes "x \<in> C"
 shows "connected_component (graph_diff E X) x = C"
 by (metis assms connected_components_notE_singletons singletonD singleton_in_diff_member)


lemma diff_odd_components_is_component:
  assumes "C \<in> (diff_odd_components E X)"
  assumes "x \<in> C"
  shows "connected_component (graph_diff E X) x = C"
  using singleton_in_diff_is_component
   odd_component_is_component 
  by (metis assms diff_odd_components_member)


lemma odd_components_nonempty:
  assumes "graph_invar E"
  assumes "C \<in> (diff_odd_components E X)"
  shows "C \<noteq> {}" 
  by (metis assms(2) diff_odd_components_member insert_not_empty odd_card_imp_not_empty 
      odd_component_member singleton_in_diff_member)

lemma odd_component_in_E:
  assumes "C \<in> (odd_components E)"
  shows "C \<subseteq> Vs E" 
  by (metis assms connected_component_subset odd_component_member)

lemma singleton_in_diff_in_E:
  assumes "C \<in> (singleton_in_diff E X)"
  shows "C \<subseteq> Vs E"
  using assms by blast

lemma component_in_E:
  assumes "C \<in> (diff_odd_components E X)"
  shows "C \<subseteq> Vs E"
  using  odd_component_in_E
        singleton_in_diff_in_E assms 
  by (metis Un_iff Vs_subset diff_odd_components_def graph_diff_subset order_trans)

lemma component_of_el_in_E:
  assumes "connected_component E x \<in> (diff_odd_components E X)"
  shows "x \<in> Vs E"
  using component_in_E 
  by (metis assms in_mono in_own_connected_component)

lemma diff_odd_components_not_in_X:
  assumes "C \<in> (diff_odd_components E X)"
  shows  "C \<inter> X = {}"
proof(rule ccontr)
  assume "C \<inter> X \<noteq> {}"
  show False 
  proof(cases "C \<in> (odd_components (graph_diff E X))")
    case True
    have "C \<subseteq> Vs (graph_diff E X)"
      by (simp add: True odd_component_in_E)
    then show ?thesis 
      by (metis \<open>C \<inter> X \<noteq> {}\<close> disjoint_iff_not_equal graph_diff_elim in_mono vs_member_elim)
  next
    case False
    then have "C \<in> (singleton_in_diff E X)" 
      by (meson assms diff_odd_components_member)
    then show ?thesis 
      using \<open>C \<inter> X \<noteq> {}\<close> by blast
  qed
qed

lemma card_singleton_in_diff_is_one:
  assumes "C \<in> singleton_in_diff E X"
  shows "card C = 1" 
  using singleton_in_diff_elim[of C E X] assms
  by (metis is_singletonI is_singleton_altdef)

lemma diff_odd_compoenent_has_odd_card:
  assumes "C \<in> diff_odd_components E X"
  shows "odd (card C)"
    using card_singleton_in_diff_is_one[of C E X] 
    by (metis assms diff_odd_components_member odd_component_member odd_one)
  
lemma diff_odd_components_are_components:
  assumes "graph_invar E"
  shows"diff_odd_components E X = 
  {C. \<exists> v\<in>Vs E-X. connected_component (graph_diff E X) v = C \<and> odd (card C)}"
proof(safe)
  {
    fix C
    assume C_doc:"C \<in> diff_odd_components E X"
    then obtain v where C_el_comp:"connected_component (graph_diff E X) v = C" 
      by (metis assms diff_odd_components_is_component odd_components_nonempty subsetI subset_empty)
    have "odd (card C)" 
      using diff_odd_compoenent_has_odd_card C_doc by auto
    then show " \<exists>v\<in>Vs E-X. connected_component (graph_diff E X) v = C \<and> odd (card C)" 
      using C_doc C_el_comp diff_odd_components_not_in_X
      by (metis DiffI component_in_E disjoint_iff_not_equal in_mono in_own_connected_component)
  }
  fix v
  assume "v \<in> Vs E" "v \<notin> X" "odd (card (connected_component (graph_diff E X) v))"
  then show "connected_component (graph_diff E X) v \<in> diff_odd_components E X"
    by (metis connected_components_notE_singletons diff_odd_components_intro1 
        diff_odd_components_intro2 odd_components_intro singleton_in_diff_intro)
qed

lemma diff_component_disjoint:
  assumes "graph_invar E"
  assumes "C1 \<in> (diff_odd_components E X)"
  assumes "C2 \<in> (diff_odd_components E X)"
  assumes "C1 \<noteq> C2"
  shows "C1 \<inter> C2 = {}" using connected_components_disj
proof(cases "C1 \<in> (odd_components (graph_diff E X))")
  case True

  show ?thesis
  proof(rule ccontr)
    assume "C1 \<inter> C2 \<noteq> {}"
    then have "\<exists>u. u \<in> C1 \<inter> C2" by auto
    then  obtain u where "u \<in> C1 \<inter> C2" by auto
    then have "connected_component (graph_diff E X) u = C1" 
      using True unfolding odd_components_def 
      using connected_components_member_eq by force
    then have "card C1 > 1" using connected_component_not_singleton
      by (smt (verit, del_insts) True Vs_subset assms(1) finite_subset graph_diff_subset mem_Collect_eq odd_components_def subset_eq)
    show False 
    proof(cases "C2 \<in> (odd_components (graph_diff E X))")
      case True
      then have "\<exists> v \<in> Vs (graph_diff E X). connected_component (graph_diff E X) v = C2"
        using odd_components_def 
        by auto
      have "u \<in> C2" using `u \<in> C1 \<inter> C2` by auto
      then have "connected_component (graph_diff E X) u = C2" 
        by (metis \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C2\<close> connected_components_member_eq)

      then show ?thesis 
        by (simp add: \<open>C1 \<noteq> C2\<close> \<open>connected_component (graph_diff E X) u = C1\<close>)
    next
      case False
      then have "C2 \<in> (singleton_in_diff E X)" 
        by (metis UnE \<open>C2 \<in> diff_odd_components E X\<close> diff_odd_components_def)
      then have " \<exists> v. C2 = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)"
        by (simp add: singleton_in_diff_def)
      have "C2 = {u}" 
        using \<open>\<exists>v. C2 = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)\<close> \<open>u \<in> C1 \<inter> C2\<close> by fastforce
      then have "u \<notin> X \<and> u \<notin> Vs (graph_diff E X)" 
        using \<open>\<exists>v. C2 = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)\<close> by fastforce
      then show ?thesis 
        by (metis \<open>C1 \<noteq> C2\<close> \<open>C2 = {u}\<close> \<open>connected_component (graph_diff E X) u = C1\<close> connected_components_notE_singletons)
    qed
  qed
next
  case False
  then have "C1 \<in> (singleton_in_diff E X)" 
    by (metis UnE \<open>C1 \<in> diff_odd_components E X\<close> diff_odd_components_def)
  then have " \<exists> v. C1 = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)"
    by (simp add: singleton_in_diff_def)
  then obtain u where " C1 = {u} \<and> u \<in> Vs E \<and> u \<notin> X \<and> u \<notin> Vs (graph_diff E X)" by auto

  show ?thesis
  proof(rule ccontr)
    assume "C1 \<inter> C2 \<noteq> {}"
    then have "u \<in> C2" 
      by (simp add: \<open>C1 = {u} \<and> u \<in> Vs E \<and> u \<notin> X \<and> u \<notin> Vs (graph_diff E X)\<close>)
    show False
    proof(cases "C2 \<in> (odd_components (graph_diff E X))")
      case True
      have "\<exists> v \<in> Vs E. connected_component E v = C2" 
        by (smt (verit, best) True \<open>C1 = {u} \<and> u \<in> Vs E \<and> u \<notin> X \<and> u \<notin> Vs (graph_diff E X)\<close> \<open>u \<in> C2\<close> in_connected_component_in_edges mem_Collect_eq odd_components_def)
      then have "connected_component E u = C2" 
        by (metis \<open>u \<in> C2\<close> connected_components_member_eq)
      then show ?thesis 
        by (smt (verit) True \<open>C1 = {u} \<and> u \<in> Vs E \<and> u \<notin> X \<and> u \<notin> Vs (graph_diff E X)\<close> \<open>u \<in> C2\<close> in_connected_component_in_edges mem_Collect_eq odd_components_def)
    next
      case False
      then have "C2 = {u}" 
        by (smt (verit, ccfv_threshold) UnE \<open>C2 \<in> diff_odd_components E X\<close> \<open>u \<in> C2\<close> diff_odd_components_def mem_Collect_eq mk_disjoint_insert singleton_in_diff_def singleton_insert_inj_eq')
      then show ?thesis 
        using \<open>C1 = {u} \<and> u \<in> Vs E \<and> u \<notin> X \<and> u \<notin> Vs (graph_diff E X)\<close> \<open>C1 \<noteq> C2\<close> by blast
    qed
  qed
qed

end