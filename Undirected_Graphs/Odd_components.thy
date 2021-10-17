theory Odd_components
  imports Bipartite Cardinality_sums
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

lemma even_component_member[iff?]: "C \<in> even_components E \<longleftrightarrow>
   (\<exists>v \<in> Vs E. connected_component E v = C \<and> even (card C))"
  unfolding even_components_def by simp


lemma even_components_elim[elim]:
  assumes "C \<in> even_components E" 
  obtains v where "v \<in> Vs E" "connected_component E v = C" "even (card C)"
  using assms 
  by(auto simp: even_component_member)


lemma even_components_intro[intro]:
  assumes "even (card C)"
  assumes "v \<in> Vs E"
  assumes "connected_component E v = C"
  shows "C \<in> even_components E" 
  using assms even_components_def by auto

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


lemma odd_components_sum_singletions_is_component:
  shows "(odd_components (graph_diff E X)) \<oplus> (singleton_in_diff E X) = diff_odd_components E X"
  using odd_components_intersection_singletions_empty 
  by (metis (no_types, lifting) Int_Un_eq(4) Un_Diff_Int Un_left_commute diff_odd_components_def
      sup_bot_right symmetric_diff_def)


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
  assumes "C \<in> (diff_odd_components E X)"
  shows "C \<noteq> {}" 
  by (metis assms diff_odd_components_member insert_not_empty odd_card_imp_not_empty 
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
  shows"diff_odd_components E X = 
  {C. \<exists> v\<in>Vs E-X. connected_component (graph_diff E X) v = C \<and> odd (card C)}"
proof(safe)
  {
    fix C
    assume C_doc:"C \<in> diff_odd_components E X"
    then obtain v where C_el_comp:"connected_component (graph_diff E X) v = C" 
      by (metis diff_odd_components_is_component odd_components_nonempty subsetI subset_empty)
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


lemma diff_odd_components_are_components_elim[elim]:
  assumes "C \<in> diff_odd_components E X"
  
obtains v where "v\<in>Vs E-X" "connected_component (graph_diff E X) v = C" "odd (card C)"
  using diff_odd_components_are_components[of E X] 
  using assms by fastforce

lemma diff_odd_components_are_components_intro[intro]:
  assumes "odd (card C)"
  assumes "v\<in>Vs E-X"
  assumes "connected_component (graph_diff E X) v = C"
  shows "C \<in> diff_odd_components E X"
 using diff_odd_components_are_components[of E X] 
  using assms by fastforce

lemma diff_odd_components_are_components_intro2[intro]:
   assumes "odd (card C)"
  assumes "C \<in> connected_components (graph_diff E X)"
  shows "C \<in> diff_odd_components E X"
  by (metis assms(1) assms(2) connected_comp_has_vert
       diff_odd_components_intro1 odd_components_intro)

lemma diff_component_disjoint:
  assumes "C1 \<in> (diff_odd_components E X)"
  assumes "C2 \<in> (diff_odd_components E X)"
  assumes "C1 \<noteq> C2"
  shows "C1 \<inter> C2 = {}"
  by (metis assms diff_odd_components_is_component disjoint_iff_not_equal)


lemma components_is_union_even_and_odd:
  shows "connected_components E = odd_components E \<union> even_components E"
  unfolding connected_components_def odd_components_def even_components_def
proof(safe)
qed auto


lemma components_parity_is_odd_components_parity:
  assumes "graph_invar E"
  shows "even (sum card (connected_components E)) = even (card (odd_components E))"
proof -
  let ?Cs = " (connected_components E)"
  have "finite ?Cs"  
    by (simp add: assms finite_con_comps)
  then have "even (sum card (connected_components E)) = even (card {C \<in> ?Cs. odd (card C)})"
    using Parity.semiring_parity_class.even_sum_iff[of ?Cs card] by auto
  moreover have "{C \<in> ?Cs. odd (card C)} = odd_components E" 
    unfolding connected_components_def odd_components_def  by blast
  ultimately show ?thesis by presburger 
qed

lemma odd_components_eq_modulo_cardinality:
  assumes "graph_invar E"
  shows "even (card (odd_components E)) = even (card (Vs E))"
  using components_parity_is_odd_components_parity[of E] 
    sum_card_connected_components[of E]
    assms
  by auto


lemma diff_is_union_elements:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  shows "Vs (graph_diff E X) \<union> Vs (singleton_in_diff E X) \<union> X = Vs E"
  apply safe
     apply (meson graph_diff_subset subset_iff vs_member)
    apply (metis insert_Diff insert_subset singleton_in_diff_in_E vs_member)
  using assms(2)
proof -
qed (auto)

lemma el_vs_singleton_is_in_singleton:
  assumes "x \<in> Vs (singleton_in_diff E X)"
  shows "{x} \<in> (singleton_in_diff E X)"
  unfolding singleton_in_diff_def
  by (smt (verit, ccfv_SIG) assms connected_component_subset connected_components_notE_singletons 
      insert_subset mem_Collect_eq singleton_in_diff_is_component singleton_in_diff_member vs_member)

lemma diff_disjoint_elements:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  shows "Vs (graph_diff E X) \<inter> Vs (singleton_in_diff E X) = {}" 
    "Vs (graph_diff E X) \<inter> X = {}"
    "Vs (singleton_in_diff E X) \<inter> X = {}"
    apply safe
  using el_vs_singleton_is_in_singleton finite.emptyI odd_components_intersection_singletions_empty
    apply fastforce
   apply (metis IntI graph_diff_elim vs_member)
  using el_vs_singleton_is_in_singleton by fastforce

lemma diff_card_is_sum_elements:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  shows "card (Vs (graph_diff E X)) + card (Vs (singleton_in_diff E X)) +  card X = card (Vs E)"
  using diff_is_union_elements[of E X] diff_disjoint_elements[of E X]
  by (smt (z3) Int_Un_distrib2 assms(1) assms(2) card_Un_disjoint finite_Un sup_bot_right)

lemma singleton_set_card_eq_vertices:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  shows "card (Vs (singleton_in_diff E X)) = card (singleton_in_diff E X)"
proof -
  let ?A = "(singleton_in_diff E X)"
  have "finite ?A" 
    by (metis Vs_def assms diff_is_union_elements finite_Un finite_UnionD)
  moreover have "\<forall>C \<in> ?A. finite C" 
    by blast
  moreover have "\<forall> C1 \<in> ?A. \<forall> C2 \<in> ?A. C1 \<noteq> C2 \<longrightarrow> C1 \<inter> C2 = {}"   
    by blast
  ultimately  have "sum card ?A = card (Vs ?A)" using assms 
      Vs_def card_Union_disjoint disjnt_def pairwise_def 
    by (simp add: Vs_def card_Union_disjoint disjnt_def pairwise_def)
  also have "sum card ?A = card ?A" 
    by (metis card_eq_sum card_singleton_in_diff_is_one sum.cong)
  finally show ?thesis 
    by presburger
qed

lemma finite_odd_components:
  assumes "graph_invar E"
  shows "finite (odd_components (graph_diff E X))" 
proof -
  have "finite (connected_components (graph_diff E X))" 
    by (meson Vs_subset assms finite_con_comps finite_subset graph_diff_subset)
  then show ?thesis 
    by (simp add: components_is_union_even_and_odd)
qed


lemma finite_diff_odd_components:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E" 
  shows "finite (diff_odd_components E X)" 
  by (metis Vs_def assms(1) assms(2) diff_is_union_elements
      diff_odd_components_def finite_Un finite_UnionD finite_odd_components)

lemma graph_invar_subset:
  assumes "graph_invar E"
  assumes "A \<subseteq> E"
  shows "graph_invar A" 
  by (meson Vs_subset assms finite_subset subsetD)

lemma graph_invar_diff:
  assumes "graph_invar E"
  shows "graph_invar (graph_diff E X)"
  by (meson Vs_subset assms finite_subset graph_diff_member graph_diff_subset)

lemma diff_odd_component_card_is_sum:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  shows "card (diff_odd_components E X) = 
        card (odd_components (graph_diff E X)) + card (singleton_in_diff E X)" 
  using finite_diff_odd_components[of E X] 
  by (simp add: odd_components_intersection_singletions_empty 
      assms card_Un_disjoint diff_odd_components_def)

lemma diff_odd_component_parity_sum:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  shows "even (card (diff_odd_components E X) + card X )  = even (card (Vs E))"
proof -
  let ?odd = "(odd_components (graph_diff E X))"
  let ?singl = "(singleton_in_diff E X)"
  let ?EwoX = "(graph_diff E X)"
  let ?allOdd = "diff_odd_components E X"

  have "even (card ?allOdd + card X) =  even (card X + card ?odd + card ?singl)"
    using diff_odd_component_card_is_sum[of E X] assms 
    by presburger
  also have "\<dots> = even (card X + card (Vs ?EwoX) + card ?singl)" 
    using odd_components_eq_modulo_cardinality[of "?EwoX"] graph_invar_diff[of E X]
      assms(1) 
    by auto
  also have "\<dots> = even (card (Vs ?EwoX) + card (Vs ?singl) + card X)" 
    using singleton_set_card_eq_vertices[of E X] assms by presburger
  also have "\<dots>  = even (card (Vs E))"
    using diff_card_is_sum_elements[of E X] assms(1) assms(2) 
    by presburger
  finally show ?thesis by auto
qed

lemma diff_odd_component_parity':
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  assumes  "card X \<le> card (diff_odd_components E X)"
  shows "even (card (diff_odd_components E X) - card X ) = even (card (Vs E))"
  using diff_odd_component_parity_sum[of E X] assms even_diff_nat not_less
  by force

lemma diff_odd_component_parity:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  assumes  "card X \<ge> card (diff_odd_components E X)"
  shows "even (card X - card (diff_odd_components E X)) = even (card (Vs E))"
  using diff_odd_component_parity_sum[of E X] assms even_diff_nat not_less
  by force

lemma defvd':
  assumes "path E p"
  assumes "C \<in> connected_components E"
  assumes "last p \<in> C"
  shows "\<forall>x \<in> set p. x \<in> C" using assms(1) assms(3)
proof(induct p)
  case path0
  then show ?case by auto
next
  case (path1 v)
  then show ?case 
    by fastforce
next
  case (path2 v v' vs)
  then show ?case 
    by (metis assms(2) connected_components_closed' in_con_comp_insert insert_Diff insert_commute
        last_ConsR list.set_intros(1) list.simps(3) set_ConsD)
qed

lemma exist_edge_in_component:
  assumes "graph_invar E"
  assumes "C \<in> connected_components E"
  assumes "x \<in> C" 
  obtains e where "e \<in> E" "x\<in> e" "e \<subseteq> C" 
proof - 
  have "C \<subseteq> Vs E" 
    by (simp add: assms(2) connected_component_subs_Vs)
  then obtain e where "e \<in> E" "x \<in> e" 
    by (meson assms(3) subsetD vs_member_elim)
  then show ?thesis 
    by (smt (z3) Diff_eq_empty_iff Diff_subset \<open>C \<subseteq> Vs E\<close> assms connected_components_closed'
        connected_components_member_sym in_con_comp_insert insert_Diff insert_iff insert_subset that)
qed  

lemma defvd:
  assumes "graph_invar E"
  assumes "path E p"
  assumes "C \<in> connected_components E"
  assumes "hd p \<in> C"
  assumes "(component_edges E C) \<noteq> {}" 
  shows "path (component_edges E C) p" using assms(2) assms(4) 
proof(induct p)
  case path0
  then show ?case 
    by simp
next
  case (path1 v)
  have "v \<in> C" 
    using path1.prems by auto
  then obtain e where  "e \<in> E \<and> v \<in> e \<and> e \<subseteq> C" 
    using exist_edge_in_component[of E C v]  assms(1) assms(3) by fastforce
  then show ?case 
    using assms(1) edge_in_component_edges by auto
next
  case (path2 v v' vs)
  have "v \<in> C" 
    using path2.prems by auto
  have "v' \<in> C" 
    by (metis assms(3) edges_are_walks in_con_compI list.sel(1) path2.hyps(1) path2.prems)
  then have "{v, v'} \<subseteq> C" 
    by (simp add: \<open>v \<in> C\<close>)
  then have "{v, v'} \<in> (component_edges E C)"
    by (simp add: assms(1) edge_in_component_edges path2.hyps(1))
  then show "path (component_edges E C) (v # v' # vs)" 
    by (simp add: \<open>v' \<in> C\<close> path2.hyps(3))
qed

lemma graph_invar_union:
  assumes "finite A"
  assumes "\<forall>a \<in> A.  graph_invar a"
  assumes "\<forall>a \<in> A. finite (Vs a)"
  shows "graph_invar (\<Union>A)"
proof
  show " \<forall>e\<in>\<Union> A. \<exists>u v. e = {u, v} \<and> u \<noteq> v" 
    using assms(2) by fastforce
  then show "finite (Vs (\<Union> A))" using  assms(1) assms(3)
    by (metis Vs_def  finite.simps finite_Union finite_UnionD)
qed


lemma perfect_matching_union:
  assumes "finite A"
  assumes "\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> Vs a1 \<inter> Vs a2 = {}"
  assumes "\<forall>a \<in> A. \<exists>M. perfect_matching a M"
  shows "\<exists>M. perfect_matching (\<Union>A) M"
proof -
  let ?Ms = "{Ms. \<exists>a \<in> A. Ms = {M. perfect_matching a M}}"
  have "\<forall>a \<in> A.  graph_invar a"
    by (meson assms(3) perfect_matching_def)
  then have "graph_invar (\<Union>A)" using graph_invar_union 
    by (simp add: graph_invar_union \<open>\<forall>a\<in>A. graph_invar a\<close> assms(1))

  have "\<forall>a \<in> A. finite (Vs a)" 
    by (simp add: \<open>\<forall>a\<in>A. graph_invar a\<close>)

  have disjoint_edges:"\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}" 
    by (metis \<open>\<forall>a\<in>A. graph_invar a\<close> assms(2) disjoint_iff_not_equal edges_are_Vs)


  let ?f = "(\<lambda>a. {{M. perfect_matching a M}})"
  have "?Ms = (\<Union>a\<in>A. ?f a)" by blast

  then have "finite ?Ms" using assms(1)
    by simp
  have "\<forall>a \<in> A. {M. perfect_matching a M} \<subseteq> {a1. a1 \<subseteq> a}" 
    by (simp add: Collect_mono perfect_matching_def)

  then have "\<forall>a \<in> A. finite {M. perfect_matching a M}"
    by (metis Vs_def \<open>\<forall>a\<in>A. finite (Vs a)\<close> finite_Collect_subsets finite_UnionD finite_subset)
  then have "finite (Vs ?Ms)"
    by (smt (verit) Vs_def \<open>finite ?Ms\<close> finite_Union mem_Collect_eq)

  have "\<forall>a1 \<in> A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow>
     {M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M} = {}" 
    apply safe 
     apply (metis UnionI Vs_subset \<open>graph_invar (\<Union> A)\<close> assms(2) edges_are_Vs empty_iff 
        le_iff_inf perfect_matching_elim(3) perfect_matching_elim(4))
    by (metis UnionI Vs_subset \<open>graph_invar (\<Union> A)\<close> assms(2) edges_are_Vs empty_iff le_iff_inf 
        perfect_matching_elim(3) perfect_matching_elim(4))

  then have matchings_are_diff: "\<forall>a1 \<in> ?Ms.\<forall>a2\<in>?Ms. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}" 
    by force
  have "\<forall>a\<in> ?Ms. \<exists>b\<in> Vs ?Ms. b \<in> a" 
    by (smt (z3) assms(3) mem_Collect_eq vs_member_intro)
  then obtain C where C_sub_Ms:"C\<subseteq> Vs ?Ms \<and> (\<forall>Ms\<in> ?Ms. \<exists>!M\<in>C. M \<in> Ms)"
    using yfsdf2[of ?Ms] matchings_are_diff \<open>finite (Vs ?Ms)\<close> \<open>finite ?Ms\<close> by presburger
  have "\<forall>c \<in>C. matching c"
  proof
    fix c
    assume "c \<in> C"
    then have "c \<in> Vs ?Ms" using C_sub_Ms by blast
    then have "\<exists>a\<in>A. perfect_matching a c" 
      by (smt (verit, best) mem_Collect_eq vs_member)
    then show "matching c"
      using perfect_matching_def by blast
  qed

  have "matching (\<Union>C)" unfolding matching_def
  proof(safe)
    fix e1 X e2 Xa x xa
    {
      fix e1 X e2 Xa x xa
      assume assums:"e1 \<in> X" "X \<in> C" "e2 \<in> Xa" "Xa \<in> C" "x \<in> e1" "x \<notin> e2" "xa \<in> e1" "xa \<in> e2"
      show " xa \<in> {}"
      proof(cases "Xa = X")
        case True
        then show ?thesis using assums
          by (metis \<open>\<forall>c\<in>C. matching c\<close>  matching_unique_match)
      next
        case False
        have "Xa \<in> Vs ?Ms" 
          using C_sub_Ms \<open>Xa \<in> C\<close> by blast
        then obtain a1 where a1_match:"a1\<in>A \<and> perfect_matching a1 Xa"
          by (smt (verit) mem_Collect_eq vs_member)
        have "X \<in> Vs ?Ms" 
          using C_sub_Ms \<open>X \<in> C\<close> by blast
        then obtain a2 where a2_match:"a2\<in>A \<and> perfect_matching a2 X"
          by (smt (verit) mem_Collect_eq vs_member)
        have "a1 \<noteq> a2" 
          using C_sub_Ms False \<open>X \<in> C\<close> \<open>Xa \<in> C\<close> a1_match a2_match by auto
        then have "a1 \<inter> a2 = {}" 
          by (simp add: a1_match a2_match disjoint_edges)

        then show ?thesis using assums
          by (smt (z3) IntI \<open>a1 \<noteq> a2\<close> 
              a1_match a2_match assms(2) perfect_matching_elim(4) vs_member_intro)
      qed
    }
    then show "e1 \<in> X \<Longrightarrow> X \<in> C \<Longrightarrow> e2 \<in> Xa \<Longrightarrow> Xa \<in> C \<Longrightarrow> x \<in> e2 \<Longrightarrow>
       x \<notin> e1 \<Longrightarrow> xa \<in> e1 \<Longrightarrow> xa \<in> e2 \<Longrightarrow> xa \<in> {}"
      by blast
  qed   

  have "\<Union>C \<subseteq> \<Union>A"
  proof
    fix x
    assume "x \<in> \<Union>C"
    then obtain c where "c\<in>C \<and> x \<in> c" by auto
    then have "c \<in> Vs ?Ms" 
      using C_sub_Ms by blast
    then obtain a where "a\<in>A \<and> perfect_matching a c" 
      by (smt (verit, best) mem_Collect_eq vs_member)
    then show "x \<in> \<Union>A" 
      using \<open>a \<in> A \<and> perfect_matching a c\<close> \<open>c \<in> C \<and> x \<in> c\<close>
      by (meson UnionI perfect_matching_elim(3) subsetD)
  qed
  have "Vs (\<Union>C) = Vs (\<Union>A)"
  proof(safe)
    fix x 
    assume "x \<in> Vs (\<Union> A)" 
    then obtain e where "e \<in> (\<Union> A) \<and> x \<in> e"
      by (meson vs_member_elim)
    then obtain a where "a \<in> A \<and> e \<in> a" by auto
    then obtain c where "c \<in> C \<and> perfect_matching a c" 
      by (metis (mono_tags, lifting) C_sub_Ms mem_Collect_eq)
    then have "x \<in> Vs c" 
      using \<open>a \<in> A \<and> e \<in> a\<close> \<open>e \<in> \<Union> A \<and> x \<in> e\<close> 
      by (metis perfect_matching_elim(4) vs_member_intro)
    then show "x \<in> Vs (\<Union> C)" 
      by (metis Vs_def \<open>c \<in> C \<and> perfect_matching a c\<close> vs_member)
  qed (meson Vs_subset \<open>\<Union> C \<subseteq> \<Union> A\<close> subsetD)

  then have "perfect_matching (\<Union> A) (\<Union> C)" 
    by (simp add: \<open>\<Union> C \<subseteq> \<Union> A\<close> \<open>graph_invar (\<Union> A)\<close> \<open>matching (\<Union> C)\<close> perfect_matching_intro)
  then show ?thesis by auto
qed

lemma odd_components_subset_vertices:
  assumes "C \<in> (diff_odd_components E X)"
  shows "C \<subseteq> Vs E"
   by (meson assms component_in_E)

lemma graph_diff_empty:
  shows "E = graph_diff E {}" 
  unfolding graph_diff_def by auto

lemma vertices_edges_in_same_component:
  assumes "{x, y} \<in> E"
  shows "y \<in> connected_component E x"
  by (meson assms(1) edges_are_walks has_path_in_connected_component)

lemma graph_diff_of_empty: 
  "graph_diff {} X = {}"
using graph_diff_subset by auto

lemma empty_graph_odd_components:
  shows "diff_odd_components {} X = {}" 
  unfolding diff_odd_components_def
proof
qed (metis el_vs_singleton_is_in_singleton equals0I 
      graph_diff_of_empty odd_components_elim singleton_in_diff_member)

lemma component_edges_singleton_is_empty:
  assumes "graph_invar E" 
  shows "component_edges E {x} = {}"
  by (smt (verit) Collect_empty_eq assms component_edges_def insert_not_empty 
      singleton_insert_inj_eq' subset_singleton_iff)

lemma component_edges_subset:
  assumes "Y \<subseteq> C"
  shows "(component_edges E Y) \<subseteq> (component_edges E C)"
  unfolding component_edges_def
  by (smt (verit, ccfv_SIG) Collect_mono_iff assms(1) subset_trans)

lemma graph_diff_is_contained_in_set:
  assumes "Y \<subseteq> X"
  shows "graph_diff E X \<subseteq> graph_diff E Y"
  unfolding graph_diff_def 
  using assms by auto

lemma add_subset_change_odd_components:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  assumes "C \<in> (diff_odd_components E X)"
  assumes "Y \<subseteq> C"
  assumes "Y \<noteq> {}"
  shows "diff_odd_components E (X\<union>Y) = ((diff_odd_components E X) - {C}) \<union>
    diff_odd_components (component_edges (graph_diff E X) C) Y"
proof(cases "C\<in> singleton_in_diff E X")
  case True
  then have "C = Y" unfolding singleton_in_diff_def
    using assms(5) assms(4) by blast

  then obtain x where singl_x:"C = {x}" "x \<in> Vs E" "x \<notin> X" "x \<notin> Vs (graph_diff E X)"
    by (metis True singleton_in_diff_elim)
  then have "Y = {x}" 
    by (simp add: \<open>C = Y\<close>)

  then have "(graph_diff E X) = (graph_diff E (X\<union>{x}))" unfolding graph_diff_def   
    using `x \<notin> Vs (graph_diff E X)`  by blast 

  then have "(odd_components (graph_diff E X)) = (odd_components (graph_diff E (X\<union>{x})))"
    by auto
  have "(singleton_in_diff E X) - {{x}} = singleton_in_diff E (X \<union> {x})"
    unfolding singleton_in_diff_def
    using \<open>graph_diff E X = graph_diff E (X \<union> {x})\<close>         
    apply safe 
     apply (metis Un_iff singletonD)
    by metis
  have "{x} \<notin> (odd_components (graph_diff E X))" 
    using odd_component_in_E singl_x(4) by auto
  then have "diff_odd_components E (X\<union>{x}) = ((diff_odd_components E X) - {{x}})"
    unfolding diff_odd_components_def 
    by (simp add: Un_Diff \<open>graph_diff E X = graph_diff E (X \<union> {x})\<close> 
                          \<open>singleton_in_diff E X - {{x}} = singleton_in_diff E (X \<union> {x})\<close>)
 

  have "(component_edges (graph_diff E X) C) = {}" 
    by (smt (verit, best) assms(1) component_edges_singleton_is_empty graph_invar_diff singl_x(1))
  then have "diff_odd_components (component_edges (graph_diff E X) C) Y = {}" 
    by (simp add: empty_graph_odd_components)

  then show ?thesis unfolding diff_odd_components_def  
    by (metis \<open>C = Y\<close> \<open>diff_odd_components E (X \<union> {x}) = diff_odd_components E X - {{x}}\<close> diff_odd_components_def singl_x(1) sup_bot_right)
next
  case False
  then have "C \<in> odd_components (graph_diff E X)" 
    by (meson assms(3) diff_odd_components_elim)
  show "diff_odd_components E (X\<union>Y) = ((diff_odd_components E X) - {C}) \<union>
    diff_odd_components (component_edges (graph_diff E X) C) Y" 
  proof
    show " diff_odd_components E (X \<union> Y) \<subseteq> diff_odd_components E X - {C} \<union>
       diff_odd_components (component_edges (graph_diff E X) C) Y"
    proof
      fix C'
      assume "C' \<in> diff_odd_components E (X \<union> Y)"
      then have "C' \<noteq> {}" 
        using odd_components_nonempty by blast
      then obtain c where "c \<in> C'" by auto
      then have "connected_component (graph_diff E (X \<union> Y)) c = C'"
        using diff_odd_components_is_component 
        by (metis \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close>)

      show "C' \<in> diff_odd_components E X - {C} \<union>
              diff_odd_components (component_edges (graph_diff E X) C) Y"
      proof(cases "c \<in> C")
        case True
        then have "connected_component (graph_diff E X) c = C" 
          by (meson assms(3) diff_odd_components_is_component)
        then have "c \<in> Vs (graph_diff E X)" 
          by (meson True \<open>C \<in> odd_components (graph_diff E X)\<close> odd_component_in_E subsetD)
     
        then obtain e where "e\<in>(graph_diff E X)" "c \<in> e"  by (meson vs_member_elim)
        then have "e \<subseteq> C" using edge_subset_component[of "(graph_diff E X)" e c]
          by (metis \<open>connected_component (graph_diff E X) c = C\<close> assms(1) graph_invar_diff)
    
          have "C' = connected_component (graph_diff E (X\<union> Y)) c" 
            by (simp add: \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close>)

          have "connected_component (graph_diff E (X\<union> Y)) c = 
      connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c"
          proof(safe)
            {
              fix x
              assume "x \<in> connected_component (graph_diff E (X\<union> Y)) c"
              show "x \<in>  connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c"
              proof(cases "x = c")
                case True
                then show ?thesis 
                  by (simp add: in_own_connected_component)
              next
                case False
                then have "(\<exists>p. walk_betw (graph_diff E (X\<union> Y)) x p c)"
                  unfolding connected_component_def 
                  by (metis \<open>x \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> connected_components_member_sym in_con_comp_has_walk)
                then obtain p where p_walk:"walk_betw (graph_diff E (X\<union> Y)) x p c" by auto
                then have "last p = c" 
                  by fastforce
               
                then have "path (graph_diff E (X\<union> Y)) p" using p_walk unfolding walk_betw_def  by auto
                then have "\<forall>z \<in> set p.  z \<in> C \<and>
       z \<in> connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c"
                  using `last p = c`
                 proof(induct p)
                   case path0
                   then show ?case 
                     by auto
                 next
                   case (path1 v)
                   then show ?case 
                     by (metis True  empty_iff empty_set in_own_connected_component last_ConsL set_ConsD)
                 next
                   case (path2 v v' vs)
                   have "v' \<in> C" 
                     by (metis last_ConsR list.set_intros(1) list.simps(3) path2.hyps(3) path2.prems)
            
                 
                 have "{v, v'} \<inter> (X\<union>Y) = {}" 
                       by (meson graph_diff_elim path2.hyps(1))
                  then have "{v, v'} \<inter> X = {}" 
                    by (simp add: Int_Un_distrib)
                  then have "{v, v'} \<in> (graph_diff E (X))"   
                    by (meson graph_diff_elim graph_diff_intro path2.hyps(1))
                    then have "v \<in> C" 
                      by (metis \<open>connected_component (graph_diff E X) c = C\<close> \<open>v' \<in> C\<close> 
                          connected_components_member_eq insert_commute 
                          vertices_edges_in_same_component)
                    then have "{v, v'} \<in> (component_edges (graph_diff E X) C)"
                      using \<open>v' \<in> C\<close> \<open>{v, v'} \<in> graph_diff E X\<close> component_edges_def by blast     
                    then have "{v, v'} \<in> (graph_diff (component_edges (graph_diff E X) C) Y)"
                      using \<open>{v, v'} \<inter> (X \<union> Y) = {}\<close> by auto       
                    then have "v' \<in> connected_component 
                                (graph_diff (component_edges (graph_diff E X) C) Y) c" 
                      by (metis last_ConsR list.set_intros(1) list.simps(3) path2.hyps(3) 
                          path2.prems)
                     then have "v \<in> connected_component 
                                (graph_diff (component_edges (graph_diff E X) C) Y) c"
                       by (metis \<open>{v, v'} \<in> graph_diff (component_edges (graph_diff E X) C) Y\<close> 
                           connected_components_member_eq insert_commute 
                           vertices_edges_in_same_component)
                  then show ?case 
                    by (metis \<open>v \<in> C\<close> last_ConsR list.simps(3) path2.hyps(3) path2.prems set_ConsD)
                qed

               
                then show "x \<in> connected_component 
                          (graph_diff (component_edges (graph_diff E X) C) Y) c"
                  by (metis list.set_sel(1) p_walk walk_betw_def)
              qed
            }
            fix x
            assume "x \<in> connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c" 
            show " x \<in> connected_component (graph_diff E (X \<union> Y)) c"
            proof(cases "x = c")
              case True
              then show ?thesis 
                by (simp add: in_own_connected_component)
            next
              case False
              then have "(\<exists>p. walk_betw  (graph_diff (component_edges (graph_diff E X) C) Y) x p c)"
                unfolding connected_component_def 
                by (metis \<open>x \<in> connected_component  (graph_diff (component_edges (graph_diff E X) C) Y) c\<close> connected_components_member_sym in_con_comp_has_walk)
              then obtain p where p_walk:"walk_betw  (graph_diff (component_edges (graph_diff E X) C) Y) x p c" by auto
              then have "last p = c" 
                by fastforce
              then have "path  (graph_diff (component_edges (graph_diff E X) C) Y) p" using p_walk unfolding walk_betw_def  by auto

              then have "\<forall>z \<in> set p. z \<in> connected_component (graph_diff E (X \<union> Y)) c"
                using `last p = c`
              proof(induct p) 
                case path0
                then show ?case 
                  by auto
              next
                case (path1 v)
                then show ?case 
                  using \<open>C' = connected_component (graph_diff E (X \<union> Y)) c\<close> \<open>c \<in> C'\<close> by auto

              next
                case (path2 v v' vs)
                have "last (v' # vs) = c" 
                  using path2.prems 
                  by auto
                have "\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E (X \<union> Y)) c" 
                  using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
                have "{v, v'} \<in> (graph_diff (component_edges (graph_diff E X) C) Y)" 
                  by (simp add: path2.hyps(1))
                then have "{v, v'} \<inter> Y = {}" unfolding graph_diff_def 
                  by fastforce
                have "{v, v'} \<in>  (component_edges (graph_diff E X) C)" 
                  using graph_diff_subset path2.hyps(1) by blast
                then have "{v, v'} \<in> (graph_diff E X)" 
                  using component_edges_subset 
                  using Berge.component_edges_subset insert_Diff insert_subset by blast
                then have "{v, v'} \<inter> X = {}" unfolding graph_diff_def  
                  by fastforce
                then have "{v, v'} \<in> (graph_diff E (X\<union>Y))" unfolding graph_diff_def 
                  using `{v, v'} \<inter> Y = {}` 
                  using \<open>{v, v'} \<in> graph_diff E X\<close> graph_diff_def by fastforce

                then have "v' \<in> connected_component (graph_diff E (X\<union>Y)) c" 

                  by (simp add: \<open>\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E (X \<union> Y)) c\<close>)
                then have "v \<in>  connected_component (graph_diff E (X\<union>Y)) c"

                  by (metis \<open>{v, v'} \<in> graph_diff E (X \<union> Y)\<close> connected_components_member_eq connected_components_member_sym vertices_edges_in_same_component)




                then show ?case 
                  using \<open>\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> by fastforce
              qed 
              then show ?thesis 
                by (metis list.set_sel(1) p_walk walk_betw_def)
            qed
          qed
          then have " connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c = C'"

            by (simp add: \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close>)
        
          have "odd (card C')" 
            using \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> diff_odd_compoenent_has_odd_card by auto

          have "c \<in> Vs (component_edges (graph_diff E X) C)" 
            
            by (smt (verit, best) \<open>c \<in> e\<close> \<open>e \<in> graph_diff E X\<close> \<open>e \<subseteq> C\<close> assms(1) edge_in_component_edges graph_invar_diff vs_member)
          have "c \<notin> Y" 
            by (smt (verit, ccfv_SIG) Un_subset_iff \<open>C' = connected_component (graph_diff E (X \<union> Y)) c\<close> \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> assms(1) assms(2) assms(3) assms(4) connected_components_notE_singletons diff_disjoint_elements(2) diff_odd_components_not_in_X dual_order.trans insert_Diff insert_disjoint(2) odd_components_subset_vertices subsetD sup.cobounded2)
          then have "c \<in> Vs (component_edges (graph_diff E X) C) - Y" 
            
            using \<open>c \<in> Vs (component_edges (graph_diff E X) C)\<close> by blast
          then have "C' \<in> diff_odd_components
           (component_edges (graph_diff E X) C) Y" 
            using \<open>connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c = C'\<close> \<open>odd (card C')\<close> by blast
         
          then show "  C' \<in> diff_odd_components E X - {C} \<union>
          diff_odd_components
           (component_edges (graph_diff E X) C) Y" 
            by (simp add: diff_odd_components_def)
       next
        case False
        then  have "c \<notin> C" by auto
        have "connected_component (graph_diff E X) c = connected_component (graph_diff E (X \<union> Y)) c"

        proof(safe)
          {
            fix x
            assume "x \<in> connected_component (graph_diff E X) c"
            show " x \<in> connected_component
               (graph_diff E (X \<union> Y)) c"
            proof(cases "x = c")
              case True
              then show ?thesis 
                by (simp add: \<open>c \<in> C'\<close> \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close>)
            next
              case False

              then have "(\<exists>p. walk_betw (graph_diff E X) x p c)"
                unfolding connected_component_def 
                by (metis \<open>x \<in> connected_component (graph_diff E X) c\<close> connected_components_member_sym in_con_comp_has_walk)
              then obtain p where p_walk:"walk_betw (graph_diff E X) x p c" by auto
              then have "last p = c" 
                by fastforce
              then have "path (graph_diff E X) p" using p_walk unfolding walk_betw_def  by auto

              then have "\<forall>z \<in> set p. z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E X) c"
                using `last p = c`
              proof(induct p) 
                case path0
                then show ?case 
                  by auto
              next
                case (path1 v)
                then show ?case 
                  using \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> 
                  by (metis empty_iff empty_set in_own_connected_component last_ConsL set_ConsD)
              next
                case (path2 v v' vs)
                have "last (v' # vs) = c" 
                  using path2.prems 
                  by auto
                have "\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E X) c" 
                  using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
                have "{v, v'} \<in> (graph_diff E X)" 
                  by (simp add: path2.hyps(1))
                then have "v' \<in> connected_component (graph_diff E X) c" 
                  by (simp add: \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E X) c\<close>)
                then have "v \<in> connected_component (graph_diff E X) v'"
                  by (meson connected_components_member_sym path2.hyps(1) vertices_edges_in_same_component)
                then have "v \<in> connected_component (graph_diff E X) c"
                  by (meson \<open>v' \<in> connected_component (graph_diff E X) c\<close> connected_components_member_trans)
                then have "v \<notin> C" 
                  by (metis \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E X) c\<close> assms(1) assms(3) assms(4) connected_components_member_eq diff_odd_components_is_component list.set_intros(1))
                then have "v \<notin> Y" 
                  using assms(4) by blast
                have "v' \<notin> Y" 
                  by (meson \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E X) c\<close> assms(4) list.set_intros(1) subsetD)
                then have "{v, v'} \<inter> (Y) = {}" 
                  by (simp add: \<open>v \<notin> Y\<close>)
                have "{v, v'} \<inter> X = {}" using `{v, v'} \<in> (graph_diff E X)` unfolding graph_diff_def  
                  by fastforce
                then have "{v, v'} \<inter> (X\<union>Y) = {}" 
                  by (simp add: Int_Un_distrib \<open>{v, v'} \<inter> Y = {}\<close>)
                then have "{v, v'} \<in> (graph_diff E (X \<union> Y))" 
                  by (metis (mono_tags, lifting) graph_diff_def mem_Collect_eq path2.hyps(1))

                then have "v \<in> C'" 
                  by (metis \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E X) c\<close> \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close> connected_components_member_eq connected_components_member_sym list.set_intros(1) vertices_edges_in_same_component) 

                then show ?case 
                  using \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E X) c\<close> \<open>v \<in> connected_component (graph_diff E X) c\<close> \<open>v \<notin> C\<close> by auto
              qed

              then have "x \<in> C' \<and> x \<notin> C \<and> x \<in> connected_component (graph_diff E X) c" 
                by (metis list.set_sel(1) p_walk walk_betw_def)
              then show " x \<in> connected_component (graph_diff E (X \<union> Y)) c" 
                by (simp add: \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close>)
            qed
          }
          fix x
          assume "x \<in> connected_component (graph_diff E (X \<union> Y)) c"
          show " x \<in> connected_component (graph_diff E X) c"
          proof(cases "x = c")
            case True
            then show ?thesis 
              by (simp add: in_own_connected_component)

          next
            case False
            then have "(\<exists>p. walk_betw (graph_diff E (X \<union> Y)) x p c)"
              unfolding connected_component_def 
              by (metis \<open>x \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> connected_components_member_sym in_con_comp_has_walk)
            then obtain p where p_walk:"walk_betw (graph_diff E (X \<union> Y)) x p c" by auto
            then have "last p = c" 
              by fastforce
            then have "path (graph_diff E (X \<union> Y)) p" using p_walk unfolding walk_betw_def  by auto

            then have "\<forall>z \<in> set p. z \<in> connected_component (graph_diff E X) c"
              using `last p = c`
            proof(induct p) 
              case path0
              then show ?case 
                by auto
            next
              case (path1 v)
              then show ?case 
                using \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> 
                by (metis empty_iff empty_set in_own_connected_component last_ConsL set_ConsD)
            next
              case (path2 v v' vs)
              have "last (v' # vs) = c" 
                using path2.prems 
                by auto
              have "\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E X) c" 
                using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
              have "{v, v'} \<in> (graph_diff E (X \<union> Y))" 
                by (simp add: path2.hyps(1))
              then have "{v, v'} \<in> (graph_diff E (X))" unfolding graph_diff_def  
                by blast
              then have "v' \<in> connected_component (graph_diff E X) c" 
                by (simp add: \<open>\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E X) c\<close>)

              then show ?case 
                by (metis \<open>\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E X) c\<close> \<open>{v, v'} \<in> graph_diff E X\<close> connected_components_member_eq insert_commute set_ConsD vertices_edges_in_same_component)
            qed
            then show " x \<in> connected_component (graph_diff E (X)) c" 
              by (metis list.set_sel(1) p_walk walk_betw_def)
          qed
        qed
        then have "connected_component (graph_diff E X) c = C'" 
          by (simp add: \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close>)
        have "C' \<in> diff_odd_components E X"
        proof(cases "C' \<in> singleton_in_diff E (X\<union>Y)")
          case True
          then have "C' = {c}" 
            by (smt (verit, ccfv_SIG) IntI Un_subset_iff \<open>c \<in> C'\<close> \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close> assms(1) assms(3) assms(4) assms(2) component_in_E connected_components_notE_singletons diff_disjoint_elements(1) empty_iff sup.absorb_iff1 vs_member_intro)
          have "connected_component (graph_diff E X) c = {c}" 
            by (simp add: \<open>C' = {c}\<close> \<open>connected_component (graph_diff E X) c = C'\<close>)
          have " c \<notin> Vs (graph_diff E X)"
          proof(rule ccontr)
            assume " \<not> c \<notin> Vs (graph_diff E X)"
            then have "\<exists> e. c \<in> e \<and> e \<in> (graph_diff E X)" 
              by (meson vs_member_elim)
            then obtain e where "c \<in> e \<and> e \<in> (graph_diff E X)" by auto
            then have "e \<subseteq> connected_component (graph_diff E X) c" 
              by (smt (z3) \<open>connected_component (graph_diff E X) c = {c}\<close> assms(1) graph_diff_subset in_con_comp_insert insertE insert_Diff insert_commute insert_subset singletonD)
            then show False 
              by (metis \<open>c \<in> e \<and> e \<in> graph_diff E X\<close> \<open>connected_component (graph_diff E X) c = {c}\<close> assms(1) graph_diff_subset insert_absorb insert_subset singleton_insert_inj_eq')
          qed

          then have "C' \<in> singleton_in_diff E X" unfolding singleton_in_diff_def
            using \<open>C' = {c}\<close> \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> component_in_E diff_odd_components_not_in_X 
            
            using True by fastforce
          then show ?thesis unfolding diff_odd_components_def 
            by simp


        next
          case False
          then have "C' \<in> odd_components (graph_diff E (X\<union>Y))" 
            by (metis UnE \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> diff_odd_components_def)
          then have "odd (card C')" 
            by (simp add: odd_components_def)
          have "c\<in>Vs (graph_diff E X)"
          proof(rule ccontr)
            assume "c \<notin> Vs (graph_diff E X)"
            have "c \<notin>  Vs (graph_diff E (X\<union>Y))"
            proof(rule ccontr)
              assume " \<not> c \<notin> Vs (graph_diff E (X \<union> Y))"
              then have "\<exists>e. c \<in> e \<and> e \<in> (graph_diff E (X \<union> Y))" 
                by (meson vs_member_elim)
              then obtain e where "c \<in> e \<and> e \<in> (graph_diff E (X \<union> Y))" by auto
              then have "e \<inter> (X \<union> Y) = {}" 
                by (simp add: graph_diff_def)
              then have "e \<inter> X = {}" by auto
              then have "e \<in> (graph_diff E X)" 
                by (metis (mono_tags, lifting) \<open>c \<in> e \<and> e \<in> graph_diff E (X \<union> Y)\<close> graph_diff_def mem_Collect_eq)
              then have "c \<in> Vs (graph_diff E X)" 
                using \<open>c \<in> e \<and> e \<in> graph_diff E (X \<union> Y)\<close> by blast
              then show False 
                using \<open>c \<notin> Vs (graph_diff E X)\<close> by blast
            qed
            have "c \<notin> X \<union> Y" 
              by (metis IntI \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> \<open>c \<in> C'\<close> diff_odd_components_not_in_X empty_iff)
            then have "{c} \<in> singleton_in_diff E (X\<union>Y)" unfolding singleton_in_diff_def 

              using \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> \<open>c \<notin> Vs (graph_diff E (X \<union> Y))\<close> \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close>
                component_in_E connected_components_notE_singletons 
              
              by (metis (no_types, lifting) False \<open>c \<in> C'\<close> singleton_in_diff_intro subsetD)
            
            then have "{c} \<in> diff_odd_components E (X\<union>Y)" 
              by (simp add: diff_odd_components_def)
            then have "connected_component (graph_diff E (X\<union>Y)) c = {c}" 

              by (simp add: \<open>c \<notin> Vs (graph_diff E (X \<union> Y))\<close> connected_components_notE_singletons)
            then have "C' = {c}" 
              by (simp add: \<open>connected_component (graph_diff E (X\<union>Y)) c = C'\<close>)
            then have "C' \<in>  singleton_in_diff E (X\<union>Y)" 
              by (simp add: \<open>{c} \<in> singleton_in_diff E (X\<union>Y)\<close>)

            then show False 
              by (simp add: False)
          qed
          then have "C' \<in> odd_components (graph_diff E X)" unfolding odd_components_def

            using \<open>connected_component (graph_diff E X) c = C'\<close> \<open>odd (card C')\<close> by blast
          then show ?thesis 
            by (simp add: diff_odd_components_def)
        qed
        then show " C' \<in> diff_odd_components E X - {C} \<union>
          diff_odd_components (component_edges (graph_diff E X) C) Y"

          using False \<open>c \<in> C'\<close> by blast
      qed
    qed
    show " diff_odd_components E X - {C} \<union>
    diff_odd_components
     (component_edges (graph_diff E X) C) Y
    \<subseteq> diff_odd_components E (X \<union> Y)"
    proof
      fix C'
      assume "C' \<in> diff_odd_components E X - {C} \<union>
             diff_odd_components
              (component_edges (graph_diff E X)
                C)
              Y"
      show "C' \<in> diff_odd_components E (X \<union> Y)"
      proof(cases "C' \<in> diff_odd_components E X - {C}")
        case True
        then have "C' \<noteq> C" 
          by blast
        then have "C' \<inter> C = {}" 
          by (metis DiffD1 True assms(1) assms(3) diff_component_disjoint)
        have "C' \<in> diff_odd_components E X" 
          using True by auto
        have "C' \<noteq> {}" 
          using \<open>C' \<in> diff_odd_components E X\<close> assms(1) assms(3) odd_components_nonempty by auto
        then obtain c where "c \<in> C'" by blast
        then have "connected_component (graph_diff E X) c = C'" 
          by (simp add: \<open>C' \<in> diff_odd_components E X\<close> assms(1) assms(3) diff_odd_components_is_component)
        have "c \<notin> C" 
          by (metis IntI \<open>C' \<in> diff_odd_components E X\<close> \<open>C' \<noteq> C\<close> \<open>c \<in> C'\<close> assms(1) assms(3) diff_component_disjoint empty_iff)

        have "connected_component (graph_diff E X) c = connected_component (graph_diff E (X \<union> Y)) c"
        proof(safe)
          {
            fix x
            assume "x \<in> connected_component (graph_diff E X) c"
            show " x \<in> connected_component
               (graph_diff E (X \<union> Y)) c"
            proof(cases "x = c")
              case True
              then show ?thesis 
                by (simp add: in_own_connected_component)
            next
              case False

              then have "(\<exists>p. walk_betw (graph_diff E X) x p c)"
                unfolding connected_component_def 
                by (metis \<open>x \<in> connected_component (graph_diff E X) c\<close> connected_components_member_sym in_con_comp_has_walk)
              then obtain p where p_walk:"walk_betw (graph_diff E X) x p c" by auto
              then have "last p = c" 
                by fastforce
              then have "path (graph_diff E X) p" using p_walk unfolding walk_betw_def  by auto

              then have "\<forall>z \<in> set p. z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E (X\<union>Y)) c"
                using `last p = c`
              proof(induct p) 
                case path0
                then show ?case 
                  by auto
              next
                case (path1 v)
                then show ?case 
                  by (metis \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> empty_iff empty_set in_own_connected_component last_ConsL set_ConsD)


              next
                case (path2 v v' vs)
                have "last (v' # vs) = c" 
                  using path2.prems 
                  by auto
                have "\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E (X\<union>Y)) c" 
                  using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
                have "{v, v'} \<in> (graph_diff E X)" 
                  by (simp add: path2.hyps(1))
                then have "{v, v'} \<inter> X = {}" 
                  by (metis (mono_tags, lifting) graph_diff_def mem_Collect_eq)
                then have "v' \<in> connected_component (graph_diff E X) c" 

                  by (simp add: \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> \<open>connected_component (graph_diff E X) c = C'\<close>)

                then have "v \<in> connected_component (graph_diff E X) v'"

                  by (meson connected_components_member_sym path2.hyps(1) vertices_edges_in_same_component)
                then have "v \<notin> C" 
                  by (metis \<open>C' \<inter> C = {}\<close> \<open>connected_component (graph_diff E X) c = C'\<close> \<open>v' \<in> connected_component (graph_diff E X) c\<close> connected_components_member_eq disjoint_iff_not_equal)
                then have "v \<notin> Y" 
                  using assms(4) by blast
                have "v' \<notin> Y" 
                  using \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> assms(4) by auto
                then have "{v, v'} \<inter> (Y) = {}" 
                  by (simp add: \<open>v \<notin> Y\<close>)
                have "{v, v'} \<inter> X = {}" using `{v, v'} \<in> (graph_diff E X)` unfolding graph_diff_def  
                  by fastforce
                then have "{v, v'} \<inter> (X\<union>Y) = {}" 
                  by (simp add: Int_Un_distrib \<open>{v, v'} \<inter> Y = {}\<close>)
                then have "{v, v'} \<in> (graph_diff E (X \<union> Y))" 
                  by (metis (mono_tags, lifting) graph_diff_def mem_Collect_eq path2.hyps(1))

                then show ?case 
                  by (metis \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> \<open>connected_component (graph_diff E X) c = C'\<close> \<open>v \<in> connected_component (graph_diff E X) v'\<close> \<open>v \<notin> C\<close> connected_components_member_eq connected_components_member_sym list.set_intros(1) set_ConsD vertices_edges_in_same_component)
              qed
              then show " x \<in> connected_component (graph_diff E (X \<union> Y)) c" 
                by (metis list.set_sel(1) p_walk walk_betw_def)

            qed
          }
          fix x
          assume "x \<in> connected_component (graph_diff E (X \<union> Y)) c"
          show " x \<in> connected_component (graph_diff E X) c"
          proof(cases "x = c")
            case True
            then show ?thesis 
              by (simp add: in_own_connected_component)

          next 
            case False
            then have "(\<exists>p. walk_betw (graph_diff E (X \<union> Y)) x p c)"
              unfolding connected_component_def 
              by (metis \<open>x \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> connected_components_member_sym in_con_comp_has_walk)
            then obtain p where p_walk:"walk_betw (graph_diff E (X \<union> Y)) x p c" by auto
            then have "last p = c" 
              by fastforce
            then have "path (graph_diff E (X \<union> Y)) p" using p_walk unfolding walk_betw_def  by auto

            then have "\<forall>z \<in> set p. z \<in> connected_component (graph_diff E X) c"
              using `last p = c`
            proof(induct p) 
              case path0
              then show ?case 
                by auto
            next
              case (path1 v)
              then show ?case 
                using \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> 
                by (metis empty_iff empty_set in_own_connected_component last_ConsL set_ConsD)
            next
              case (path2 v v' vs)
              have "last (v' # vs) = c" 
                using path2.prems 
                by auto
              have "\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E X) c" 
                using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
              have "{v, v'} \<in> (graph_diff E (X \<union> Y))" 
                by (simp add: path2.hyps(1))
              then have "{v, v'} \<in> (graph_diff E (X))" unfolding graph_diff_def  
                by blast
              then have "v' \<in> connected_component (graph_diff E X) c" 
                by (simp add: \<open>\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E X) c\<close>)

              then show ?case 
                by (metis \<open>\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E X) c\<close> \<open>{v, v'} \<in> graph_diff E X\<close> connected_components_member_eq insert_commute set_ConsD vertices_edges_in_same_component)
            qed
            then show " x \<in> connected_component (graph_diff E (X)) c" 
              by (metis list.set_sel(1) p_walk walk_betw_def)
          qed
        qed
        then have " connected_component (graph_diff E (X \<union> Y)) c = C'" 
          by (simp add: \<open>connected_component (graph_diff E X) c = C'\<close>)
        show " C' \<in> diff_odd_components  E (X \<union> Y)"
        proof(cases "C' \<in> singleton_in_diff E X")
          case True
          then have "C' = {c}" 
            by (smt (verit) IntI \<open>c \<in> C'\<close> \<open>connected_component (graph_diff E X) c = C'\<close> assms(1) assms(2) connected_components_notE_singletons diff_disjoint_elements(1) empty_iff vs_member_intro)
          then have "connected_component (graph_diff E (X\<union>Y)) c = {c}" 
            by (simp add: \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close>)
          then have "c \<notin>  Vs (graph_diff E X)"
            by (smt (verit, ccfv_SIG) IntI True \<open>c \<in> C'\<close> assms(1) assms(2) diff_disjoint_elements(1) empty_iff vs_member_intro)
          have " c \<notin> Vs (graph_diff E (X\<union>Y))"
          proof(rule ccontr)
            assume " \<not> c \<notin> Vs (graph_diff E (X\<union>Y))"
            then have "\<exists> e. c \<in> e \<and> e \<in> (graph_diff E (X\<union>Y))" 
              by (meson vs_member_elim)
            then obtain e where "c \<in> e \<and> e \<in> (graph_diff E (X\<union>Y))" by auto
            then have "e \<subseteq> connected_component (graph_diff E (X\<union>Y)) c" 
              by (smt (z3) \<open>connected_component (graph_diff E (X\<union>Y)) c = {c}\<close> assms(1) graph_diff_subset in_con_comp_insert insertE insert_Diff insert_commute insert_subset singletonD)
            then show False 

              by (metis Set.set_insert \<open>c \<in> e \<and> e \<in> graph_diff E (X \<union> Y)\<close> \<open>connected_component (graph_diff E (X \<union> Y)) c = {c}\<close> assms(1) graph_diff_subset insert_subset singletonD)
          qed
          have "c \<notin> X \<union> Y" 
            by (metis IntI Un_iff \<open>C' \<in> diff_odd_components E X\<close> \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> assms(4) diff_odd_components_not_in_X empty_iff subsetD)
          then have "{c} \<in> singleton_in_diff E (X\<union>Y)" 
            by (smt (verit, del_insts) \<open>C' = {c}\<close> \<open>C' \<in> diff_odd_components E X\<close> \<open>c \<notin> Vs (graph_diff E (X \<union> Y))\<close> component_in_E insert_subset mem_Collect_eq singleton_in_diff_def)

          then have "C' \<in> singleton_in_diff E (X\<union>Y)" 
            by (simp add: \<open>C' = {c}\<close>)

          then show ?thesis 
            by (simp add: diff_odd_components_def)
        next
          case False
          then have "C' \<in> odd_components (graph_diff E X)" 
            by (metis UnE \<open>C' \<in> diff_odd_components E X\<close> diff_odd_components_def)
          then have "odd (card C')" 
            by (simp add: odd_components_def)
          have "c \<notin> X \<union> Y" 
            by (metis IntI Un_iff \<open>C' \<in> diff_odd_components E X\<close> \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> assms(4) diff_odd_components_not_in_X empty_iff subsetD)
          have "c\<in>Vs (graph_diff E (X))" 
            by (smt (verit, del_insts) False UnI1 \<open>C' \<in> diff_odd_components E X\<close> \<open>c \<notin> X \<union> Y\<close> \<open>connected_component (graph_diff E X) c = C'\<close> component_in_E connected_components_notE_singletons insert_subset mem_Collect_eq singleton_in_diff_def)
          then have "\<exists>e. c \<in> e \<and> e \<in> (graph_diff E (X))" 
            by (meson vs_member_elim)
          then obtain e where "c \<in> e \<and> e \<in> (graph_diff E (X))" 
            by blast
          then have "c \<in> e \<and> e \<in> E \<and> e \<inter> X = {}" 
            by (simp add: graph_diff_def)
          then have "e \<subseteq> C'" 
            by (smt (z3) \<open>C' \<inter> C = {}\<close> \<open>c \<in> C'\<close> \<open>c \<in> e \<and> e \<in> graph_diff E X\<close> \<open>connected_component (graph_diff E X) c = C'\<close> assms(1) empty_iff in_con_comp_insert inf_le1 insertE insert_Diff insert_commute insert_subset)
          then have "e \<inter> Y = {}" 
            using \<open>C' \<inter> C = {}\<close> assms(4) by blast
          then have "e \<inter> (X \<union> Y) = {}" 
            by (simp add: Int_Un_distrib \<open>c \<in> e \<and> e \<in> E \<and> e \<inter> X = {}\<close>)
          then have "e \<in> (graph_diff E (X \<union> Y))" 
            by (simp add: \<open>c \<in> e \<and> e \<in> E \<and> e \<inter> X = {}\<close> graph_diff_def)

          then have "c\<in>Vs (graph_diff E (X \<union> Y))" 
            using \<open>c \<in> e \<and> e \<in> graph_diff E X\<close> by blast

          then have "C' \<in> odd_components (graph_diff E (X \<union> Y))" unfolding odd_components_def

            using \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close> \<open>odd (card C')\<close> 

            by blast

          then show ?thesis 
            by (simp add: diff_odd_components_def)
        qed 

      next
        case False
        then have "C' \<in>  diff_odd_components (component_edges (graph_diff E X) C) Y"
          using \<open>C' \<in> diff_odd_components E X - {C} \<union> diff_odd_components (component_edges (graph_diff E X) C) Y\<close> by blast
        let ?C = "(component_edges (graph_diff E X) C)"
        have "graph_invar ?C" 
          by (smt (verit, best) Berge.component_edges_subset assms(1) graph_diff_subset graph_invar_subset)
        have "C' \<subseteq> Vs ?C" 
          by (meson \<open>C' \<in> diff_odd_components (component_edges (graph_diff E X) C) Y\<close> component_in_E)
        have "Vs ?C \<subseteq> C" unfolding component_edges_def  
          by (smt (verit, ccfv_SIG) mem_Collect_eq subset_eq vs_member)
        then have "C' \<subseteq> C" 
          using \<open>C' \<subseteq> Vs (component_edges (graph_diff E X) C)\<close> by auto
        have "C' \<inter> Y = {}" 
          using \<open>C' \<in> diff_odd_components (component_edges (graph_diff E X) C) Y\<close> diff_odd_components_not_in_X by auto

        then have "C' \<noteq> {}" using odd_components_nonempty
          using \<open>C' \<in> diff_odd_components ?C Y\<close> `graph_invar ?C` by fastforce
        then obtain c where "c \<in> C'"
          by blast
        then have "connected_component (graph_diff ?C Y) c = C'"
          using diff_odd_components_is_component
          using `graph_invar ?C` `C' \<in> diff_odd_components ?C Y` 
          
          by (simp add: diff_odd_components_is_component)

        have "connected_component (graph_diff E (X\<union> Y)) c = 
      connected_component (graph_diff ?C Y) c"
        proof(safe)
          {
            fix x
            assume "x \<in> connected_component (graph_diff E (X\<union> Y)) c"
            show "x \<in>  connected_component (graph_diff ?C Y) c"
            proof(cases "x = c")
              case True
              then show ?thesis 
                by (simp add: in_own_connected_component)
            next
              case False
              then have "(\<exists>p. walk_betw (graph_diff E (X\<union> Y)) x p c)"
                unfolding connected_component_def 
                by (metis \<open>x \<in> connected_component (graph_diff E (X\<union> Y)) c\<close> connected_components_member_sym in_con_comp_has_walk)


              then obtain p where p_walk:"walk_betw (graph_diff E (X\<union> Y)) x p c" by auto
              then have "last p = c" 
                by fastforce
              then have "path (graph_diff E (X\<union> Y)) p" using p_walk unfolding walk_betw_def  by auto

              then have "\<forall>z \<in> set p. z \<in> C'"
                using `last p = c`
              proof(induct p)
                case path0
                then show ?case 
                  by auto
              next
                case (path1 v)
                then show ?case  
                  using \<open>c \<in> C'\<close> \<open>connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c = C'\<close> 

                  by (metis \<open>C' \<subseteq> C\<close> empty_iff empty_set in_own_connected_component last_ConsL set_ConsD subset_eq)
              next
                case (path2 v v' vs)
                have "last (v' # vs) = c" 
                  using path2.prems 
                  by auto
                have "\<forall>z\<in>set (v' # vs). z \<in> C' " 
                  using \<open>last (v' # vs) = c\<close> path2.hyps(3)
                  by fastforce
                have "{v, v'} \<in> (graph_diff E (X\<union>Y))" 
                  by (simp add: path2.hyps(1))
                then have "{v, v'} \<inter> (X \<union>Y) = {}" 
                  by (smt (verit, ccfv_threshold) Un_subset_iff assms(1) assms(3) assms(4) assms(2) component_in_E diff_disjoint_elements(2) disjoint_iff_not_equal dual_order.trans vs_member_intro)
                then have "{v, v'} \<inter> Y = {}"
                  by blast
                then have "{v, v'} \<inter> X = {}" using `{v, v'} \<inter> (X \<union>Y) = {}`
                  by blast
                then have "{v, v'} \<in> (graph_diff E X)" unfolding graph_diff_def 
                  using graph_diff_subset path2.hyps(1) by auto

                have "v' \<in> C'"

                  by (simp add: \<open>\<forall>z\<in>set (v' # vs). z \<in> C'\<close>)
                then have "v' \<in> C"
                  using \<open>C' \<subseteq> C\<close> by blast

                then have "C = connected_component  (graph_diff E (X)) c" 

                  by (metis (no_types, lifting) \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> assms(1) assms(3) diff_odd_components_is_component subsetD)
                then have "v' \<in> connected_component  (graph_diff E (X)) c"

                  using \<open>v' \<in> C\<close> by blast
                then have "v \<in> C" 
                  by (metis \<open>C = connected_component (graph_diff E X) c\<close> \<open>{v, v'} \<in> graph_diff E X\<close> connected_components_member_eq connected_components_member_sym vertices_edges_in_same_component)
                then have "{v, v'} \<subseteq> C" 
                  by (simp add: \<open>v' \<in> C\<close>)
                then have "{v, v'} \<in> ?C" using component_edges_def 
                  using \<open>{v, v'} \<in> graph_diff E X\<close> by fastforce

                then have "{v, v'} \<in> (graph_diff ?C Y)" using `{v, v'} \<inter> Y = {}`
                  unfolding graph_diff_def 
                  by blast
                then have "v' \<in> connected_component (graph_diff ?C Y) c" 
                  using \<open>connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c = C'\<close> \<open>v' \<in> C'\<close> by blast
                then have "v \<in> connected_component (graph_diff ?C Y) c" 
                  by (metis \<open>{v, v'} \<in> graph_diff (component_edges (graph_diff E X) C) Y\<close> connected_components_member_eq insert_commute vertices_edges_in_same_component)
                then have "v \<in> C'" 
                  using \<open>connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c = C'\<close> by blast

                then show ?case 
                  using \<open>\<forall>z\<in>set (v' # vs). z \<in> C'\<close> by fastforce

              qed
              then show "x  \<in> connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c"
                by (metis \<open>connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c = C'\<close> list.set_sel(1) p_walk walk_betw_def)
            qed
          }
          fix x
          assume "x \<in> connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c" 
          show " x \<in> connected_component (graph_diff E (X \<union> Y)) c"
          proof(cases "x = c")
            case True
            then show ?thesis 
              by (simp add: in_own_connected_component)

          next
            case False
            then have "(\<exists>p. walk_betw  (graph_diff (component_edges (graph_diff E X) C) Y) x p c)"
              unfolding connected_component_def 
              by (metis \<open>x \<in> connected_component  (graph_diff (component_edges (graph_diff E X) C) Y) c\<close> connected_components_member_sym in_con_comp_has_walk)
            then obtain p where p_walk:"walk_betw  (graph_diff (component_edges (graph_diff E X) C) Y) x p c" by auto
            then have "last p = c" 
              by fastforce
            then have "path  (graph_diff (component_edges (graph_diff E X) C) Y) p" using p_walk unfolding walk_betw_def  by auto

            then have "\<forall>z \<in> set p. z \<in> connected_component (graph_diff E (X \<union> Y)) c"
              using `last p = c`
            proof(induct p) 
              case path0
              then show ?case 
                by auto
            next
              case (path1 v)
              then show ?case 
                by (metis empty_iff empty_set in_own_connected_component last_ConsL set_ConsD)
            next
              case (path2 v v' vs)
              have "last (v' # vs) = c" 
                using path2.prems 
                by auto
              have "\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E (X \<union> Y)) c" 
                using \<open>last (v' # vs) = c\<close> path2.hyps(3) by blast
              have "{v, v'} \<in> (graph_diff (component_edges (graph_diff E X) C) Y)" 
                by (simp add: path2.hyps(1))
              then have "{v, v'} \<inter> Y = {}" unfolding graph_diff_def 
                by fastforce
              have "{v, v'} \<in>  (component_edges (graph_diff E X) C)" 
                using graph_diff_subset path2.hyps(1) by blast
              then have "{v, v'} \<in> (graph_diff E X)" 
                using Berge.component_edges_subset by blast
              then have "{v, v'} \<inter> X = {}" unfolding graph_diff_def  
                by fastforce
              then have "{v, v'} \<in> (graph_diff E (X\<union>Y))" unfolding graph_diff_def 
                using `{v, v'} \<inter> Y = {}` 
                using \<open>{v, v'} \<in> graph_diff E X\<close> graph_diff_def by fastforce

              then have "v' \<in> connected_component (graph_diff E (X\<union>Y)) c" 

                by (simp add: \<open>\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E (X \<union> Y)) c\<close>)
              then have "v \<in>  connected_component (graph_diff E (X\<union>Y)) c"

                by (metis \<open>{v, v'} \<in> graph_diff E (X \<union> Y)\<close> connected_components_member_eq connected_components_member_sym vertices_edges_in_same_component)




              then show ?case 
                using \<open>\<forall>z\<in>set (v' # vs). z \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> by fastforce
            qed 
            then show ?thesis 
              by (metis list.set_sel(1) p_walk walk_betw_def)
          qed
        qed
        then have " connected_component (graph_diff E (X \<union> Y)) c = C'"
          by (simp add: \<open>connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c = C'\<close>)


        show " C' \<in> diff_odd_components  E (X \<union> Y)"
        proof(cases "C' \<in> singleton_in_diff ?C Y")
          case True
          then have "\<exists>v. C' = {v} \<and> v \<in> Vs ?C \<and> v \<notin> Y \<and> v \<notin> Vs (graph_diff ?C Y)"
            unfolding singleton_in_diff_def

            by blast
          then have "C' = {c}" 
            using \<open>c \<in> C'\<close> by force


          then have "connected_component (graph_diff E (X\<union>Y)) c = {c}" 
            by (simp add: \<open>C' = {c}\<close> \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close>)

          have " c \<notin> Vs (graph_diff E (X\<union>Y))"
          proof(rule ccontr)
            assume " \<not> c \<notin> Vs (graph_diff E (X\<union>Y))"
            then have "\<exists> e. c \<in> e \<and> e \<in> (graph_diff E (X\<union>Y))" 
              by (meson vs_member_elim)
            then obtain e where "c \<in> e \<and> e \<in> (graph_diff E (X\<union>Y))" by auto
            then have "e \<subseteq> connected_component (graph_diff E (X\<union>Y)) c" 
              by (smt (z3) \<open>connected_component (graph_diff E (X\<union>Y)) c = {c}\<close> assms(1) graph_diff_subset in_con_comp_insert insertE insert_Diff insert_commute insert_subset singletonD)
            then show False 

              by (metis Set.set_insert \<open>c \<in> e \<and> e \<in> graph_diff E (X \<union> Y)\<close> \<open>connected_component (graph_diff E (X \<union> Y)) c = {c}\<close> assms(1) graph_diff_subset insert_subset singletonD)
          qed
          have "c \<notin> X \<union> Y" 
            by (metis Un_iff \<open>C' \<inter> Y = {}\<close> \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> assms(3) diff_odd_components_not_in_X disjoint_iff_not_equal subset_eq)
          then have "{c} \<in> singleton_in_diff E (X\<union>Y)" 

            by (smt (verit, ccfv_SIG) \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> \<open>c \<notin> Vs (graph_diff E (X \<union> Y))\<close> assms(3) component_in_E mem_Collect_eq singleton_in_diff_def subsetD)

          then have "C' \<in> singleton_in_diff E (X\<union>Y)" 
            by (simp add: \<open>C' = {c}\<close>)

          then show ?thesis 
            by (simp add: diff_odd_components_def)
        next
          case False
          then have "C' \<in> odd_components (graph_diff ?C Y)" 
            using \<open>C' \<in> diff_odd_components (component_edges (graph_diff E X) C) Y\<close>
              diff_odd_components_def 
            by (simp add: diff_odd_components_def)
          then have "odd (card C')" 
            by (simp add: odd_components_def)
          have "c \<notin> X \<union> Y" 
            by (metis Un_iff \<open>C' \<inter> Y = {}\<close> \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> assms(3) diff_odd_components_not_in_X disjoint_iff_not_equal subset_eq)

          have "c\<in>Vs (graph_diff ?C Y)" 
            using `C' \<in> odd_components (graph_diff ?C Y)`
            unfolding odd_components_def 
            by (smt (verit) \<open>\<And>thesis. (\<And>c. c \<in> C' \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c = C'\<close> connected_components_notE_singletons in_connected_component_in_edges mem_Collect_eq singletonD)

          then have "\<exists>e. c \<in> e \<and> e \<in> (graph_diff ?C Y)" 
            by (meson vs_member_elim)
          then obtain e where "c \<in> e \<and> e \<in> (graph_diff ?C Y)" 
            by blast
          then have "c \<in> e \<and> e \<in> ?C \<and> e \<inter> Y = {}" 
            by (simp add: graph_diff_def)
          then have "e \<subseteq> C'" 
            by (metis (full_types) \<open>C' \<inter> Y = {}\<close> \<open>c \<in> C'\<close> \<open>c \<in> e \<and> e \<in> graph_diff (component_edges (graph_diff E X) C) Y\<close> \<open>connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c = C'\<close> \<open>graph_invar (component_edges (graph_diff E X) C)\<close> in_con_comp_insert inf_le1 insertE insert_Diff insert_commute insert_subset singletonD)


          then have "e \<inter> (X \<union> Y) = {}" 
            by (smt (z3) Int_Un_distrib Int_Un_eq(4) Un_Int_assoc_eq Un_absorb Un_commute \<open>C' \<subseteq> C\<close> \<open>c \<in> e \<and> e \<in> component_edges (graph_diff E X) C \<and> e \<inter> Y = {}\<close> assms(3) diff_odd_components_not_in_X subset_trans)
          have "e \<in> E" using `c \<in> e \<and> e \<in> ?C \<and> e \<inter> Y = {}` 
            by (metis Diff_insert_absorb Berge.component_edges_subset graph_diff_subset subset_Diff_insert)

          then have "e \<in> (graph_diff E (X \<union> Y))" 
            by (simp add: \<open>e \<inter> (X \<union> Y) = {}\<close> graph_diff_def)

          then have "c\<in>Vs (graph_diff E (X \<union> Y))" 
            using \<open>c \<in> e \<and> e \<in> graph_diff (component_edges (graph_diff E X) C) Y\<close> by blast

          then have "C' \<in> odd_components (graph_diff E (X \<union> Y))" unfolding odd_components_def

            using \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close> \<open>odd (card C')\<close> 

            by blast

          then show ?thesis 
            by (simp add: diff_odd_components_def)
        qed 

      qed
    qed
  qed
qed

lemma diff_odd_components_same_inter_vertices:
  assumes "graph_invar E"
  shows "diff_odd_components E (Y \<inter> Vs E) = diff_odd_components E Y"
proof -
  have "graph_diff E (Y \<inter> Vs E) = graph_diff E Y" unfolding graph_diff_def by blast

  then have "singleton_in_diff E (Y \<inter> Vs E) = singleton_in_diff E Y" unfolding singleton_in_diff_def
    apply safe 
     apply (simp)
     by force

   then show ?thesis 
     by (simp add: \<open>graph_diff E (Y \<inter> Vs E) = graph_diff E Y\<close> diff_odd_components_def)
 qed

end