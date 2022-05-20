theory Tutte_theorem3
  imports Odd_components Cardinality_sums
begin

definition tutte_condition where
  "tutte_condition E \<equiv> \<forall> X \<subseteq> Vs E. card (odd_comps_in_diff E X) \<le> card X"

definition comp_out where 
  "comp_out E C X \<equiv> {e. e \<in> E \<and> (\<exists> x y. e = {x,y} \<and> y \<in> C \<and> x \<in> X)}"

lemma tutte_condition_member[iff?]: "tutte_condition E \<longleftrightarrow>
  (\<forall> X \<subseteq> Vs E. card (odd_comps_in_diff E X) \<le> card X)"
  unfolding tutte_condition_def by simp


lemma tutte_condition_elim[elim]:
  assumes "tutte_condition E"
  assumes "X \<subseteq> Vs E"
  shows "card (odd_comps_in_diff E X) \<le> card X"
  using assms 
  by(auto simp: tutte_condition_member)


lemma tutte_condition_intro[intro]:
  assumes "\<forall>X \<subseteq> Vs E. card (odd_comps_in_diff E X) \<le> card X"
  shows "tutte_condition E" 
  using assms tutte_condition_member by auto

lemma comp_out_member[iff?]:
  "e \<in> comp_out E C X \<longleftrightarrow> e \<in> E \<and> (\<exists> x y. e = {x,y} \<and> y \<in> C \<and> x \<in> X)" 
  by (simp add: comp_out_def)

lemma comp_out_elim[elim]:
  assumes "e \<in> comp_out E C X"
  obtains x y where "e = {x,y}" "y \<in> C" "x \<in> X"  "e \<in> E"   
  by (meson assms comp_out_member)

lemma comp_out_intro[intro]:
  assumes "e = {x,y}" "y \<in> C" "x \<in> X"  "e \<in> E"
  shows "e \<in>  comp_out E C X"   
  using assms comp_out_member by blast


lemma odd_components_in_tutte_graph:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  shows "(odd_comps_in_diff E {}) = {}"
proof -
  have "finite (odd_comps_in_diff E {})" 
    by (simp add: assms(1) finite_odd_comps_in_diff)
  have "{} \<subseteq> E" by auto
  then have "card (odd_comps_in_diff E {}) \<le> card {}" using assms(2) 
    by (metis card.empty empty_subsetI tutte_condition_elim)
  then show ?thesis 
    using \<open>finite (odd_comps_in_diff E {})\<close> by auto
qed

lemma connected_comp_if_comp_out_empty:
  assumes "C \<in> odd_comps_in_diff E X"
  assumes "comp_out E C X = {}"
  shows "C \<in> connected_components E"
proof -
 obtain x where "x \<in> Vs E \<and> x \<in> C"
      using component_in_E[of C E X] 
      by (metis assms(1) disjoint_iff_not_equal le_iff_inf odd_components_nonempty)
  
  then have "connected_component (graph_diff E X) x = C"
    using odd_comps_in_diff_is_component[of C E X] 
    by (simp add: \<open>C \<in> odd_comps_in_diff E X\<close>)
  have " \<nexists>x y. x \<in> C \<and> y \<in> X \<and> {x, y} \<in> E" 
    by (metis assms(2) comp_out_intro insert_absorb insert_commute insert_not_empty)
    then have "\<forall>x y. {x, y} \<in> E \<and> x \<in> C \<longrightarrow> {x, y} \<in> graph_diff E X"   
      using assms(1) odd_comps_in_diff_not_in_X 
      by (metis Int_empty_left disjoint_iff_not_equal graph_diffI insert_disjoint(1))
    then have "\<forall>x y. {x, y} \<in> E \<and> x \<in> C \<longrightarrow> y \<in> C" 
      by (metis assms(1) odd_comps_in_diff_is_component vertices_edges_in_same_component)
 have "connected_component E x = C" 
    proof(safe)
        fix y
        assume "y \<in> connected_component E x"
        show "y \<in> C"
        proof(cases "x = y")
          case True
          then show ?thesis 
            using \<open>x \<in> Vs E \<and> x \<in> C\<close> by auto
        next
          case False
          then obtain p where p_walk:"walk_betw E x p y"
            using `y \<in> connected_component E x`
            by (metis  in_con_comp_has_walk )
        
          then have "hd p \<in> C" 
            by (metis \<open>x \<in> Vs E \<and> x \<in> C\<close> walk_between_nonempty_path(3))
          
          then have "path E p" using p_walk unfolding walk_betw_def  by auto

          then have "\<forall>z \<in> set p. z \<in> C"  using `hd p \<in> C`
            apply (induct p)
              apply force
                apply auto[1]
              by (metis \<open>\<forall>x y. {x, y} \<in> E \<and> x \<in> C \<longrightarrow> y \<in> C\<close> list.sel(1) set_ConsD)
         
          then show "y \<in> C" 
            by (metis last_in_set p_walk walk_betw_def)
        qed   
    qed (metis \<open>connected_component (graph_diff E X) x = C\<close> 
            con_comp_subset graph_diff_subset insert_absorb insert_subset)
    then show ?thesis 
      by (metis \<open>x \<in> Vs E \<and> x \<in> C\<close> connected_components_closed' own_connected_component_unique)
  qed

lemma comp_out_nonempty:
  assumes "graph_invar E"
  assumes "C \<in> odd_comps_in_diff E X"
assumes "tutte_condition E"
  shows "comp_out E C X \<noteq> {}"
proof(rule ccontr)
  assume "\<not> comp_out E C X \<noteq> {}"
  then have "comp_out E C X = {}" by auto

  
 obtain x where "x \<in> Vs E \<and> x \<in> C"
      using component_in_E[of C E X] assms(2)
      by (metis odd_components_nonempty subset_empty subset_eq)

  then have "connected_component (graph_diff E X) x = C"
    using odd_comps_in_diff_is_component[of C E X] 
    by (simp add: \<open>C \<in> odd_comps_in_diff E X\<close>)

  have "C \<in> connected_components E" 
    by (meson \<open>comp_out E C X = {}\<close> assms(2) connected_comp_if_comp_out_empty)

  then have "C \<in> (odd_comps_in_diff E {})" 
    by (metis assms(2) diff_odd_compoenent_has_odd_card graph_diff_empty 
        odd_comps_in_diff_are_componentsI2)
    then show False using odd_components_in_tutte_graph[of E]
      by (simp add: assms  odd_components_in_tutte_graph)
  qed

    
lemma tutte1:
  assumes "\<exists>M. perfect_matching E M"
  shows "tutte_condition E"
proof(rule ccontr)
  obtain M where "perfect_matching E M" using assms by auto
  assume "\<not> tutte_condition E"

  then obtain X where "X \<subseteq> Vs E \<and> card (odd_comps_in_diff E X) > card X"
    by (meson le_less_linear tutte_condition_def)

  then have "X \<subseteq> Vs M" "graph_invar E" "matching M" "M\<subseteq>E" "Vs M = Vs E"
    using \<open>perfect_matching E M\<close> perfect_matchingE 
    by metis+ 
  then have "finite (Vs M)" by simp
  have "finite M" 
    by (metis Vs_def \<open>Vs M = Vs E\<close> \<open>graph_invar E\<close> finite_UnionD)

  let ?comp_out  = "\<lambda> C. {e. e \<in> M \<and> (\<exists> x y. e = {x,y} \<and> y \<in> C \<and> x \<in> X)}"
  let ?QX = "(odd_comps_in_diff E X)"

  have 2: "\<forall> e\<in> E. card e = 2" 
    using \<open>graph_invar E\<close> card_edge by blast
  have "\<forall> C \<in> ?QX. (?comp_out C) \<subseteq> M"
    by blast

  have "\<forall> C \<in> ?QX. card (?comp_out C) * 2 = card ( Vs (?comp_out C))"
  proof
    fix C
    assume "C \<in> ?QX"
    have "card (Vs (?comp_out C)) =  sum (\<lambda> e. card e) (?comp_out C)"
      using \<open>finite (Vs M)\<close> \<open>matching M\<close> matching_card_is_sum by fastforce
    also have "\<dots> =  sum (\<lambda> e. 2) (?comp_out C)" 
      by (smt (verit, del_insts) \<open>M \<subseteq> E\<close> \<open>graph_invar E\<close> card_edge mem_Collect_eq subset_eq sum.cong)
    also have "\<dots> = card (?comp_out C) * 2" by simp  
    ultimately show "\<dots> = card (Vs (?comp_out C))" 
      by presburger
  qed

  have "\<forall> C \<in> ?QX. card ((Vs (?comp_out C)) \<inter> X) = card (?comp_out C)" 
  proof
    fix C
    assume "C \<in> ?QX"
    have 5:"\<forall> e \<in> (?comp_out C). card (e \<inter> X) = 1"
      using Int_commute odd_comps_in_diff_not_in_X[of C E X]  \<open>C \<in> ?QX\<close> by force
    have "card ((Vs (?comp_out C)) \<inter> X) = sum (\<lambda> e. card (e \<inter> X)) (?comp_out C)"
      using matching_int_card_is_sum[of M "(?comp_out C)" X] `matching M` `finite (Vs M)` 
      by blast
    then show "card ((Vs (?comp_out C)) \<inter> X) =  card (?comp_out C)" using 5  
      by force   
  qed

  have "(\<Union>C \<in>?QX. ((Vs (?comp_out C)) \<inter> X)) \<subseteq> X" 
    by blast

  let ?f = "(\<lambda> C. ((Vs (?comp_out C)) \<inter> X))"
  have "\<forall>C \<in> ?QX. finite ((Vs (?comp_out C)) \<inter> X)" 
    by (meson \<open>X \<subseteq> Vs M\<close> \<open>finite (Vs M)\<close> finite_Int finite_subset)
  have "finite ?QX" 
    by (metis \<open>X \<subseteq> Vs E \<and> card X < card ?QX\<close> card_eq_0_iff card_gt_0_iff less_imp_triv)
  have "\<forall> C1 \<in>?QX. \<forall> C2 \<in> ?QX.  C1 \<noteq> C2 \<longrightarrow> ((Vs (?comp_out C1))) \<inter> ((Vs (?comp_out C2))) = {}"
    by (smt (verit, del_insts) \<open>matching M\<close> diff_component_disjoint odd_comps_in_diff_not_in_X 
            disjoint_iff_not_equal doubleton_eq_iff matching_unique_match mem_Collect_eq vs_member)
  then have "\<forall> C1 \<in>?QX. \<forall> C2 \<in> ?QX. 
    C1 \<noteq> C2 \<longrightarrow> ((Vs (?comp_out C1)) \<inter> X) \<inter> ((Vs (?comp_out C2)) \<inter> X) = {}"   
    by blast

  then have "card (\<Union>C \<in>?QX. ((Vs (?comp_out C) \<inter> X))) = 
    sum (\<lambda> C. card (Vs (?comp_out C) \<inter> X)) ?QX"
    using union_card_is_sum[of "?QX" ?f]
      `\<forall>C \<in> ?QX. finite ((Vs (?comp_out C)) \<inter> X)`
      `finite ?QX` 
    by presburger

  then  have "sum (\<lambda> C. card ((Vs (?comp_out C)) \<inter> X)) ?QX \<le> card X" 
    by (metis (no_types, lifting) \<open>(\<Union>C \<in>?QX. ((Vs (?comp_out C)) \<inter> X)) \<subseteq> X\<close> 
          \<open>X \<subseteq> Vs M\<close> \<open>finite (Vs M)\<close> card_mono finite_subset)

  then have "sum (\<lambda> C. card (?comp_out C)) ?QX \<le> card X" 
    using \<open>\<forall>C\<in>odd_comps_in_diff E X. card (Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<inter> X) = card {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}\<close> by auto

  then have "\<forall> C \<in> ?QX. finite (?comp_out C)" 
    by (simp add: \<open>finite M\<close>) 
  have "\<forall> C \<in> ?QX. ?comp_out C \<noteq> {}" 
  proof
    fix C
    assume "C \<in> ?QX" 
    show "?comp_out C \<noteq> {}"
    proof(rule ccontr)
      assume "\<not> ?comp_out C \<noteq> {}" 
      then have "?comp_out C = {}" by auto
      have e_in_C:"\<forall> e \<in> M. e \<inter> C = {} \<or> e \<inter> C = e"
      proof(safe)
        fix e x y
        assume assms_edge: "e \<in> M" " x \<in> e" "x \<notin> C" "y \<in> e" "y \<in> C" 
        have "e = {x, y}" 
            using \<open>M \<subseteq> E\<close> \<open>graph_invar E\<close> assms_edge(1) assms_edge(2) assms_edge(3) assms_edge(4) assms_edge(5) insert_eq_iff by auto

       then have "e \<inter> X = {}" 
         using \<open>C \<in> odd_comps_in_diff E X\<close> \<open>{e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}\<close>
            assms_edge(1) assms_edge(5) odd_comps_in_diff_not_in_X by blast

       then have "e \<in> (graph_diff E X)" 
          using \<open>M \<subseteq> E\<close> \<open>e \<in> M\<close> 
          by (simp add: graph_diffI subsetD)
        then have "x \<in> C" 
          by (smt (verit, ccfv_SIG) \<open>C \<in> ?QX\<close> \<open>M \<subseteq> E\<close> \<open>graph_invar E\<close> assms_edge
              odd_comps_in_diff_is_component empty_iff in_con_comp_insert 
              insert_Diff insert_commute insert_iff subsetD)
        then show "y \<in> {}"  using \<open>x \<notin> C\<close> by auto
      qed

      have " ((Vs M) \<inter> C) = C" 
        by (metis Int_absorb1 \<open>C \<in> odd_comps_in_diff E X\<close> \<open>Vs M = Vs E\<close> component_in_E)
      have "card ((Vs M) \<inter> C) = sum (\<lambda> e. card (e \<inter> C)) M"
        using matching_int_card_is_sum[of M M C]  `matching M`  \<open>finite (Vs M)\<close> by blast
      then have "even (card C)" 
        using \<open>Vs M \<inter> C = C\<close>
        by (smt (verit) "2" \<open>M \<subseteq> E\<close> e_in_C dvd_sum even_numeral odd_card_imp_not_empty subset_eq)
      then show False 
        using diff_odd_compoenent_has_odd_card[of C E X] \<open>C \<in> ?QX\<close> by auto
    qed
  qed

  then have "\<forall> C \<in> ?QX. card(?comp_out C) \<ge> 1"
    by (simp add: \<open>\<forall>C\<in>odd_comps_in_diff E X. finite (?comp_out C)\<close> card_gt_0_iff Suc_leI)  
  then have "sum (\<lambda> C. card (?comp_out C)) ?QX \<ge> card ?QX"
    using sum_mono by fastforce
  then have "card X \<ge> card ?QX"  
    using \<open>(\<Sum>C\<in>odd_comps_in_diff E X. card {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}) \<le> card X\<close> order_trans by blast

  then show False 
    using \<open>X \<subseteq> Vs E \<and> card X < card ?QX\<close> not_less by blast
qed


lemma odd_comps_in_diff_connected:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  assumes "C \<in> (odd_comps_in_diff E X)" 
  shows "\<exists>x y. x \<in> C \<and> y \<in> X \<and> {x, y} \<in> E"
  using comp_out_nonempty[of E C X] 
  by (smt (verit, best) Collect_empty_eq assms(1) assms(2) assms(3) comp_out_def insert_commute)




definition barrier where
  "barrier E X \<equiv> X \<noteq> {} \<and> card (odd_comps_in_diff E X) = card X"

lemma diff_components_finite:
  assumes "graph_invar E"

shows "finite (odd_comps_in_diff E X)" 
  unfolding odd_comps_in_diff_def
proof(safe)

  have "finite (connected_components (graph_diff E (X)))"
    by (meson Vs_subset assms finite_con_comps finite_subset graph_diff_subset)
  have "  (odd_components (graph_diff E (X )))
          \<subseteq> connected_components (graph_diff E (X ))"
    unfolding odd_components_def 
    unfolding connected_components_def 
    using odd_componentE by fastforce
  then show "finite  (odd_components (graph_diff E (X)))" 

    using \<open>finite (connected_components (graph_diff E (X)))\<close> finite_subset by blast
  have "finite (Vs E)"           by (simp add: assms)

  have "finite  {{v} |v. v \<in> Vs E}"
  proof -
    have "\<forall>x \<in>  {{v} |v. v \<in> Vs E}. \<exists>c \<in> Vs E. x = {c}"

      by blast
    let ?f = "(\<lambda>c. {{c}})"
    have "{{v} |v. v \<in> Vs E} = (\<Union>c\<in>(Vs E). (?f c))"
    proof(safe) 
      {
        fix x v
        assume "v \<in> Vs E"
        then show "{v} \<in> (\<Union>c\<in>Vs E. {{c}})" 
          by blast
      }
      fix x c
      assume "c \<in> Vs E"
      show "\<exists>v. {c} = {v} \<and> v \<in> Vs E" 
        using \<open>c \<in> Vs E\<close> by blast
    qed

    then show "finite {{v} |v. v \<in> Vs E}" 
      by (simp add: \<open>finite (Vs E)\<close>)
  qed
  have " singl_in_diff E (X) \<subseteq> {{v} |v. v \<in> Vs E}"
    unfolding singl_in_diff_def 
    by blast
  then show "finite ( singl_in_diff E (X))" using \<open>finite {{v} |v. v \<in> Vs E}\<close> 
      finite_subset[of "( singl_in_diff E (X))" "{{v} |v. v \<in> Vs E}"]

    by blast
qed

lemma new_components_subset_of_old_one:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  assumes "C \<in> (odd_comps_in_diff E X)"
  assumes "Y \<subseteq> C"
  assumes "C' \<in>  odd_comps_in_diff (component_edges (graph_diff E X) C) Y"
  shows " C' \<subseteq> Vs  (component_edges (graph_diff E X) C)"
  using component_in_E[of C' "(component_edges (graph_diff E X) C)" "Y"]   
  using assms(5) by blast

lemma new_components_in_old_one:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  assumes "C \<in> (odd_comps_in_diff E X)"
  shows " Vs  (component_edges (graph_diff E X) C) \<subseteq> C" 
proof
  fix x
  assume "x \<in> Vs (component_edges (graph_diff E X) C)"
  then have "\<exists>e. e \<in> (component_edges (graph_diff E X) C) \<and> x\<in>e"

    by (meson vs_member_elim)
  then obtain e where " e \<in> (component_edges (graph_diff E X) C) \<and> x\<in>e" by auto
  then have "e \<subseteq> C" unfolding component_edges_def  
    by auto
  then show "x\<in>C" 
    using \<open>e \<in> component_edges (graph_diff E X) C \<and> x \<in> e\<close> by auto
qed

lemma new_components_intersection_old_is_empty:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  assumes "C \<in> (odd_comps_in_diff E X)"
  assumes "Y \<subseteq> C"
  shows "(odd_comps_in_diff E X - {C}) \<inter> 
 odd_comps_in_diff (component_edges (graph_diff E X) C) Y= {}" 
proof(rule ccontr)
  assume "(odd_comps_in_diff E X - {C}) \<inter>
    odd_comps_in_diff (component_edges (graph_diff E X) C) Y \<noteq>
    {}"
  then obtain C' where "C' \<in> (odd_comps_in_diff E X - {C}) \<inter>
    odd_comps_in_diff (component_edges (graph_diff E X) C) Y"

    by (meson ex_in_conv)
  then have "C' \<subseteq> C" using new_components_in_old_one[of E X C]
      new_components_subset_of_old_one[of E X C Y C'] 
    by (metis IntD2 assms(1) assms(2) assms(3) dual_order.trans odd_components_subset_vertices)
  have "\<forall>C'\<in>odd_comps_in_diff E X - {C}. C' \<inter> C = {}" 
    by (metis DiffD2  assms(3) diff_component_disjoint insert_Diff insert_iff)
  have "C' \<inter> C = {}" 
    by (meson IntD1 \<open>C' \<in> (odd_comps_in_diff E X - {C}) \<inter> odd_comps_in_diff (component_edges (graph_diff E X) C) Y\<close> \<open>\<forall>C'\<in>odd_comps_in_diff E X - {C}. C' \<inter> C = {}\<close>)
  then have "C' = {}" 
    using \<open>C' \<subseteq> C\<close> by auto
  have "C' \<noteq> {}"
    using \<open>C' \<in> (odd_comps_in_diff E X - {C}) \<inter> odd_comps_in_diff (component_edges (graph_diff E X) C) Y\<close> assms(1) odd_components_nonempty by fastforce
  then show False 
    by (simp add: \<open>C' = {}\<close>)
qed

lemma max_barrier_add_vertex_empty_odd_components:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  assumes "X \<subseteq> Vs E"
  assumes "barrier E X"
  assumes "\<forall> Y \<in> {Z. Z \<subseteq> Vs E \<and> barrier E Z}. Y \<noteq> X \<longrightarrow> \<not> (X \<subseteq> Y)"
  assumes "C \<in> (odd_comps_in_diff E X)"
  assumes "x \<in> C"
  shows "odd_comps_in_diff (component_edges (graph_diff E X) C) {x} = {}" (is "?docX = {}")
proof(rule ccontr)
  assume "?docX \<noteq> {}"
  have "{x} \<noteq> {}" 
    by simp
  have " odd_comps_in_diff E (X \<union> {x}) =
 odd_comps_in_diff E X - {C} \<union> odd_comps_in_diff (component_edges (graph_diff E X) C) {x}"
    using add_subset_change_odd_components[of E X C "{x}"] assms by auto
  have "graph_invar (component_edges (graph_diff E X) C)" 
    
    by (smt (verit) Berge.component_edges_subset assms(1) graph_diff_subset graph_invar_subset)
  have "finite ?docX" using diff_components_finite[of "(component_edges (graph_diff E X) C)"]

    using \<open>graph_invar (component_edges (graph_diff E X) C)\<close> by blast
  then have "card ?docX \<ge> 1" 
    by (simp add: Suc_leI \<open>odd_comps_in_diff (component_edges (graph_diff E X) C) {x} \<noteq> {}\<close> card_gt_0_iff)
  have "card (odd_comps_in_diff E (X\<union>{x})) \<le> card (X\<union>{x})"
    using assms(2) unfolding tutte_condition_def 
    by (metis Un_insert_right assms(3) assms(6) assms(7) boolean_algebra_cancel.sup0 component_in_E insert_subset subsetD)
  have "card (odd_comps_in_diff E (X\<union>{x}))\<le> card X +1" 
    by (metis One_nat_def Un_insert_right \<open>card (odd_comps_in_diff E (X \<union> {x})) \<le> card (X \<union> {x})\<close> add.right_neutral add_Suc_right assms(1) assms(3) boolean_algebra_cancel.sup0 card.insert finite_subset insert_absorb trans_le_add1)
  have "card (odd_comps_in_diff E X) = card X" 
    using assms(4) barrier_def by blast
  have "card ((odd_comps_in_diff E X) - {C}) = card X - 1" 
    by (metis assms(1) assms(3) assms(4) assms(6) barrier_def card.infinite card_0_eq card_Diff_singleton finite_subset)
  then have "card (odd_comps_in_diff E (X\<union>{x})) \<le> (card X - 1) + 2" 

    using \<open>card (odd_comps_in_diff E (X \<union> {x})) \<le> card X + 1\<close> by linarith
  then have "card (odd_comps_in_diff E (X\<union>{x})) \<le> card ((odd_comps_in_diff E X) - {C}) + 2"

    using \<open>card (odd_comps_in_diff E X - {C}) = card X - 1\<close> by presburger
  then have "card (odd_comps_in_diff E X - {C} \<union> 
  odd_comps_in_diff (component_edges (graph_diff E X) C) {x})
\<le> card ((odd_comps_in_diff E X) - {C}) + 2" 
    using \<open>odd_comps_in_diff E (X \<union> {x}) = odd_comps_in_diff E X - {C} \<union> odd_comps_in_diff (component_edges (graph_diff E X) C) {x}\<close> by auto



  have "\<forall>C' \<in> (odd_comps_in_diff E X - {C}). C' \<inter> C = {}"

    by (metis DiffD1 DiffD2 assms(1) assms(6) diff_component_disjoint insert_iff)
  then have "Vs (odd_comps_in_diff E X - {C}) \<inter> C = {}" 
    by (smt (verit, ccfv_SIG) Int_ac(3) Vs_def assms(1) assms(6) diff_component_disjoint disjoint_iff_not_equal insert_Diff insert_partition)


  then have "card ?docX \<le> 2" 
    by (smt (verit, ccfv_SIG) Int_lower2 Nat.le_diff_conv2 Un_upper1 \<open>card (odd_comps_in_diff E X - {C} \<union> odd_comps_in_diff (component_edges (graph_diff E X) C) {x}) \<le> card (odd_comps_in_diff E X - {C}) + 2\<close> \<open>finite (odd_comps_in_diff (component_edges (graph_diff E X) C) {x})\<close> add.commute assms(1) assms(2) assms(3) assms(4) assms(6) assms(7) card_Un_disjoint card_mono diff_add_inverse diff_components_finite finite_Diff finite_Un insert_subset le_antisym nat_le_linear new_components_intersection_old_is_empty)
  show False
  proof(cases "card ?docX = 2")
    case True
    then have "card (odd_comps_in_diff E (X\<union>{x})) = card X + 1" 
      using  new_components_intersection_old_is_empty[of E X C "{x}"] 

      by (smt (verit, best) Int_lower2 Nat.add_diff_assoc Nat.add_diff_assoc2 One_nat_def Suc_leI \<open>1 \<le> card (odd_comps_in_diff (component_edges (graph_diff E X) C) {x})\<close> \<open>Vs (odd_comps_in_diff E X - {C}) \<inter> C = {}\<close> \<open>card (odd_comps_in_diff E X - {C}) = card X - 1\<close> \<open>odd_comps_in_diff E (X \<union> {x}) = odd_comps_in_diff E X - {C} \<union> odd_comps_in_diff (component_edges (graph_diff E X) C) {x}\<close> \<open>finite (odd_comps_in_diff (component_edges (graph_diff E X) C) {x})\<close> assms(1) assms(2) assms(3) assms(4) assms(6) assms(7) barrier_def card_Un_disjoint card_gt_0_iff diff_add_inverse2 finite_Diff finite_subset insert_subsetI one_add_one)
    then have "card (odd_comps_in_diff E (X\<union>{x})) = card (X\<union>{x})" 
      by (metis One_nat_def Un_insert_right \<open>card (odd_comps_in_diff E X) = card X\<close> add.right_neutral add_Suc_right assms(1) assms(3) card.insert finite_subset insert_absorb sup_bot_right)
    then have "barrier E (X\<union>{x})"
      by (simp add: barrier_def)
    have "X \<subseteq> (X\<union>{x})" 
      by auto
    then show ?thesis using assms(5) `barrier E (X\<union>{x})`  
      by (metis (no_types, lifting) One_nat_def Un_subset_iff \<open>card (odd_comps_in_diff E (X \<union> {x})) = card X + 1\<close> \<open>card (odd_comps_in_diff E (X \<union> {x})) \<le> card (X \<union> {x})\<close> assms(3) assms(6) assms(7) component_in_E diff_add_inverse diff_is_0_eq' insert_Diff insert_is_Un mem_Collect_eq nat.simps(3))

  next
    case False
    then have " card (odd_comps_in_diff (component_edges(graph_diff E X) C) {x})  = 1" 
      using \<open>1 \<le> card (odd_comps_in_diff (component_edges (graph_diff E X) C) {x})\<close> \<open>card (odd_comps_in_diff (component_edges (graph_diff E X) C) {x}) \<le> 2\<close> by linarith
    then have "\<exists>!C'. C' \<in> (odd_comps_in_diff (component_edges(graph_diff E X) C) {x})"

      by (metis card_1_singletonE empty_iff insert_iff)
    have "(odd_comps_in_diff E X - {C}) \<inter> odd_comps_in_diff (component_edges (graph_diff E X) C) {x} = {}"
      using  new_components_intersection_old_is_empty[of E X C "{x}"] assms 
      by simp
    have "Vs (component_edges(graph_diff E X) C) = C" 
      by (smt (verit, best) IntI Nat.add_diff_assoc2 One_nat_def Suc_leI Un_insert_right \<open>(odd_comps_in_diff E X - {C}) \<inter> odd_comps_in_diff (component_edges (graph_diff E X) C) {x} = {}\<close> \<open>card (odd_comps_in_diff (component_edges (graph_diff E X) C) {x}) = 1\<close> \<open>card (odd_comps_in_diff E X - {C}) = card X - 1\<close> \<open>card (odd_comps_in_diff E X) = card X\<close> \<open>odd_comps_in_diff E (X \<union> {x}) = odd_comps_in_diff E X - {C} \<union> odd_comps_in_diff (component_edges (graph_diff E X) C) {x}\<close> \<open>finite (odd_comps_in_diff (component_edges (graph_diff E X) C) {x})\<close> add.right_neutral add_Suc_right assms(1) assms(3) assms(6) assms(7) boolean_algebra_cancel.sup0 card.empty card.insert card_Un_disjoint card_gt_0_iff component_in_E diff_add_inverse2 diff_components_finite diff_is_0_eq' diff_odd_component_parity odd_comps_in_diff_not_in_X empty_iff finite_Diff insert_subset nat_le_linear odd_card_imp_not_empty odd_one subsetD)



    then show ?thesis 
      by (smt (verit, ccfv_threshold) IntI Nat.add_diff_assoc2 One_nat_def Suc_leI Un_insert_right \<open>(odd_comps_in_diff E X - {C}) \<inter> odd_comps_in_diff (component_edges (graph_diff E X) C) {x} = {}\<close> \<open>card (odd_comps_in_diff (component_edges (graph_diff E X) C) {x}) = 1\<close> \<open>card (odd_comps_in_diff E X - {C}) = card X - 1\<close> \<open>card (odd_comps_in_diff E X) = card X\<close> \<open>odd_comps_in_diff E (X \<union> {x}) = odd_comps_in_diff E X - {C} \<union> odd_comps_in_diff (component_edges (graph_diff E X) C) {x}\<close> \<open>finite (odd_comps_in_diff (component_edges (graph_diff E X) C) {x})\<close> add_Suc_right assms(1) assms(2) assms(3) assms(6) assms(7) boolean_algebra_cancel.sup0 card.empty card.insert card_Un_disjoint card_gt_0_iff component_in_E diff_add_inverse2 diff_components_finite diff_is_0_eq' diff_odd_component_parity odd_comps_in_diff_not_in_X empty_iff finite_Diff insert_subset le_iff_add odd_card_imp_not_empty odd_one subsetD tutte_condition_def)
  qed
qed

lemma max_barrier_add_vertex_doesnt_increase_odd_components:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  assumes "X \<subseteq> Vs E"
  assumes "barrier E X"
  assumes "\<forall> Y \<in> {Z. Z \<subseteq> Vs E \<and> barrier E Z}. Y \<noteq> X \<longrightarrow> \<not> (X \<subseteq> Y)"
  assumes "C \<in> (odd_comps_in_diff E X)"
  assumes "x \<in> C"
  shows "odd_comps_in_diff E (X\<union>{x}) = (odd_comps_in_diff E X) - {C}"
proof -
  have "{x} \<noteq> {}" 
    by simp
  have " odd_comps_in_diff E (X \<union> {x}) =
 odd_comps_in_diff E X - {C} \<union> odd_comps_in_diff (component_edges (graph_diff E X) C) {x}"
    using add_subset_change_odd_components[of E X C "{x}"] assms by auto
  let ?docX = "odd_comps_in_diff (component_edges (graph_diff E X) C) {x}"
  have "?docX = {}" 
    by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) max_barrier_add_vertex_empty_odd_components)
  then show " odd_comps_in_diff E (X \<union> {x}) = odd_comps_in_diff E X - {C}"

    using \<open>odd_comps_in_diff E (X \<union> {x}) = odd_comps_in_diff E X - {C} \<union> odd_comps_in_diff (component_edges (graph_diff E X) C) {x}\<close> by auto
qed

lemma component_edges_same_in_diff:
  assumes "C \<in> odd_comps_in_diff E X"
  shows  "(component_edges (graph_diff E X) C) = (component_edges E C)"
proof - 
  have "\<forall>e \<subseteq> C. e \<in> E \<longrightarrow> e \<in> graph_diff E X"
  proof(safe)
    fix e
    assume "e \<subseteq> C" "e \<in> E"
    then have "e \<inter> X = {}" 
      using assms odd_comps_in_diff_not_in_X by blast
    then show "e \<in> graph_diff E X" unfolding graph_diff_def 

      by (simp add: \<open>e \<in> E\<close>)
  qed
  then show ?thesis      unfolding component_edges_def 
    by (meson graph_diff_subset subsetD)
qed

lemma graph_diff_trans:
  assumes "graph_invar E"
  shows "graph_diff E (X\<union>Y) = graph_diff (graph_diff E X) Y"
  unfolding graph_diff_def
  by (simp add: inf_sup_distrib1)

lemma vertices_of_edges_in_component_same:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  assumes "C \<in> odd_components (graph_diff E X)"
  shows " Vs (component_edges E C) = C"
proof(safe)
  {
    fix x
    assume "x \<in> Vs (component_edges E C)"
    then obtain e where " x \<in> e \<and> e \<in> (component_edges E C)" 
      by (meson vs_member_elim)
    have "C \<in> odd_comps_in_diff E X" 
      by (simp add: assms(3) odd_comps_in_diff_def)
    then have "e \<subseteq> C" using `x \<in> e \<and> e \<in> (component_edges E C)` 
      unfolding component_edges_def 
      by blast

    then show "x \<in> C" 
      using \<open>x \<in> e \<and> e \<in> component_edges E C\<close> by blast
  }
  fix x
  assume "x \<in> C"
  then have "x \<in> Vs (graph_diff E X) \<and> connected_component (graph_diff E X) x = C \<and> odd (card C)"
    by (meson assms(3) odd_component_def odd_component_is_component odd_componentsE odd_components_elem_in_E subsetD)
 then obtain e where "x \<in> e \<and> e \<in> (graph_diff E X)" 
    by (meson vs_member_elim)
  have "graph_invar  (graph_diff E X)"

    by (metis assms(1) assms(2) diff_is_union_elements finite_Un graph_diff_subset insert_Diff insert_subset)


  then obtain x' y where  " e = {x', y}" using `x \<in> e \<and> e \<in> (graph_diff E X)` 
    by meson
  then have "connected_component (graph_diff E X) x' = C" 
    by (metis \<open>x \<in> Vs (graph_diff E X) \<and> connected_component (graph_diff E X) x = C \<and> odd (card C)\<close> \<open>x \<in> e \<and> e \<in> graph_diff E X\<close> connected_components_member_eq insert_iff singletonD vertices_edges_in_same_component)
  then have "connected_component (graph_diff E X) y = C" using ` e = {x', y}`
    by (metis  \<open>x \<in> e \<and> e \<in> graph_diff E X\<close> connected_components_member_eq  vertices_edges_in_same_component)
  then have "e \<subseteq> C" 
    by (metis \<open>connected_component (graph_diff E X) x' = C\<close> \<open>e = {x', y}\<close> \<open>x \<in> e \<and> e \<in> graph_diff E X\<close> connected_components_member_sym insert_subset singletonD subsetI vertices_edges_in_same_component)
  then have "e \<in> (component_edges E C)" unfolding component_edges_def 
    using \<open>e = {x', y}\<close> \<open>x \<in> e \<and> e \<in> graph_diff E X\<close> graph_diff_subset insert_Diff insert_subset by fastforce
  then show "x \<in> Vs  (component_edges E C)" 
    using \<open>x \<in> e \<and> e \<in> graph_diff E X\<close> by blast
qed


lemma possible_connected_vertices_in_expanded_graph_intersection:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  assumes "C \<in> odd_comps_in_diff E X"
  assumes "x' \<in> C"
  assumes "{connected_component (graph_diff E X) x', {y'}} \<in> M'"
  assumes "matching M'" 
  assumes "y' \<in> X"
  shows " Vs {{c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} |x y.
     y\<in> X \<and>   {connected_component (graph_diff E X) x, {y}} \<in> M'} \<inter> C =
    {c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'}" (is "Vs ?Z2 \<inter> C = ?C'")
proof
  have "connected_component (graph_diff E X) x' = C" 
    by (simp add: assms(1) assms(3) assms(4) odd_comps_in_diff_is_component)
        show "Vs ?Z2 \<inter> C \<subseteq> ?C'"
        proof
          fix z
          assume "z\<in> Vs ?Z2 \<inter> C"
          then have "\<exists>C' \<in> ?Z2. z \<in> C'" 
            by (meson IntD1 vs_member_elim)
          then obtain C' where "C' \<in> ?Z2 \<and> z \<in> C'" by blast
          then have "\<exists>x1 y1. C' = {c . \<exists> e. e \<in> E \<and> e = {c, y1}  \<and> c \<notin> X
                     \<and> c \<in> connected_component (graph_diff E X) x1} \<and> y1 \<in> X
        \<and> {connected_component (graph_diff E X) x1, {y1}} \<in> M'" by auto
          then obtain x1 y1 where " C' = {c . \<exists> e. e \<in> E \<and> e = {c, y1}  \<and> c \<notin> X
                     \<and> c \<in> connected_component (graph_diff E X) x1}  \<and> y1 \<in> X
        \<and> {connected_component (graph_diff E X) x1, {y1}} \<in> M'" by auto



          then have " z \<in> connected_component (graph_diff E X) x1"
            using \<open>C' \<in> {{c. \<exists>e. e \<in> E \<and> e = {c, y}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. y\<in> X \<and>{connected_component (graph_diff E X) x, {y}} \<in> M'} \<and> z \<in> C'\<close> by auto
          then have " connected_component (graph_diff E X) z = connected_component (graph_diff E X) x1"

            by (metis (no_types, lifting) connected_components_member_eq)
          then have "C' = {c . \<exists> e. e \<in> E \<and> e = {c, y1}  \<and> c \<notin> X
                     \<and> c \<in> connected_component (graph_diff E X) z}  \<and> y1 \<in> X
        \<and> {connected_component (graph_diff E X) z, {y1}} \<in> M'
" 
            using \<open>C' = {c. \<exists>e. e \<in> E \<and> e = {c, y1} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x1} \<and> y1 \<in> X \<and> {connected_component (graph_diff E X) x1, {y1}} \<in> M'\<close> by presburger
         
          have "connected_component (graph_diff E X) x' = C" 
            by (simp add: \<open>connected_component (graph_diff E X) x' = C\<close>)
          have "connected_component (graph_diff E X) z = connected_component (graph_diff E X) x'"
            
            using \<open>connected_component (graph_diff E X) x' = C\<close> \<open>z \<in> Vs {{c. \<exists>e. e \<in> E \<and> e = {c, y}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. y \<in> X \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'} \<inter> C\<close> connected_components_member_eq by force
          then have "{connected_component (graph_diff E X) z, {y1}} \<inter>
                    {connected_component (graph_diff E X) x', {y'}} \<noteq> {}"

            by (simp add: \<open>connected_component (graph_diff E X) z = connected_component (graph_diff E X) x'\<close>)
          have "matching M'" using assms(6) by blast 
         
          then have "{connected_component (graph_diff E X) z, {y1}} =
                    {connected_component (graph_diff E X) x', {y'}}"
            
            by (meson \<open>C' = {c. \<exists>e. e \<in> E \<and> e = {c, y1} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z} \<and> y1 \<in> X \<and> {connected_component (graph_diff E X) z, {y1}} \<in> M'\<close> \<open>{connected_component (graph_diff E X) z, {y1}} \<inter> {connected_component (graph_diff E X) x', {y'}} \<noteq> {}\<close> assms(5) matching_def)
          then have "y1 = y'" 
            by (metis (full_types) \<open>connected_component (graph_diff E X) z = connected_component (graph_diff E X) x'\<close> doubleton_eq_iff)
          then have "C' = ?C'" 
            using \<open>C' = {c. \<exists>e. e \<in> E \<and> e = {c, y1} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z} \<and> y1 \<in> X \<and> {connected_component (graph_diff E X) z, {y1}} \<in> M'\<close> \<open>connected_component (graph_diff E X) z = connected_component (graph_diff E X) x'\<close> by presburger

          then show "z \<in> ?C'" 
            using \<open>C' \<in> {{c. \<exists>e. e \<in> E \<and> e = {c, y}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. y \<in> X \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'} \<and> z \<in> C'\<close> by blast
        qed
        show "?C' \<subseteq> Vs ?Z2 \<inter> C" 
        proof
          fix z
          assume "z \<in> ?C'"
          then have  "\<exists>e. e \<in> E \<and> e = {z, y'} \<and> z \<notin> X \<and> z \<in> connected_component (graph_diff E X) x'"
            
            by blast
            
            then have "z \<in> C"
            by (simp add: \<open>connected_component (graph_diff E X) x' = C\<close>)
          then have "{connected_component (graph_diff E X) z, {y'}} \<in> M'" 
            using \<open>\<exists>e. e \<in> E \<and> e = {z, y'} \<and> z \<notin> X \<and> z \<in> connected_component (graph_diff E X) x'\<close> assms(5) connected_components_member_eq by force
        
          have "?C' \<in> ?Z2"
          proof(safe)
            have " {c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} =
          {c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'}" 
              by blast
            then have "{c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} =
          {c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} \<and>  y' \<in> X \<and>
          {connected_component (graph_diff E X) x', {y'}} \<in> M'" 
              using assms(5) 
              using assms(7) by blast
              show " \<exists>x y. {c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} =
          {c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} \<and> y \<in> X \<and>
          {connected_component (graph_diff E X) x, {y}} \<in> M'" 
                
                using Collect_cong \<open>{c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} = {c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} \<and> y' \<in> X \<and> {connected_component (graph_diff E X) x', {y'}} \<in> M'\<close> by auto

           
            qed
            then show "z \<in> Vs ?Z2 \<inter> C" 
              by (metis (no_types, lifting) IntI \<open>z \<in> C\<close> \<open>z \<in> {c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'}\<close> vs_member_intro)

      qed
    qed



lemma subset_graph_finite:
  assumes "finite A"
  shows "finite {{X, Y}| X Y.  X \<subseteq> A \<and> Y \<subseteq> A}" (is "finite ?UA")
proof -
  have "finite {(X, Y) |X Y. X \<subseteq> A \<and> Y \<subseteq> A}"
    using assms by auto
  let ?f = "(\<lambda>(X, Y). {{X, Y}})" 
  have "{{X, Y}| X Y.  X \<subseteq> A \<and> Y \<subseteq> A} =  (\<Union>a\<in>{(X, Y) |X Y. X \<subseteq> A \<and> Y \<subseteq> A}. ?f a)"
  proof(safe)
  qed (auto)
  then show ?thesis 
    using \<open>finite {(X, Y) |X Y. X \<subseteq> A \<and> Y \<subseteq> A}\<close> by auto
qed

lemma union_of_set_finite:
  assumes "finite A"
  assumes "\<forall>a \<in> A. finite a"
  shows "finite (\<Union>A)" 
  using assms(1) assms(2) by blast

lemma odd_comps_in_diff_are_components:
  assumes "graph_invar E"
  shows"odd_comps_in_diff E X = {C. \<exists> v\<in>Vs E-X. connected_component (graph_diff E X) v = C \<and> odd (card C)}"
proof(safe)
  {
    fix C
    assume "C \<in> odd_comps_in_diff E X"
    then obtain v where "connected_component (graph_diff E X) v = C" 
      using assms(1) odd_comps_in_diff_is_component odd_components_nonempty 
  by (metis subset_empty subset_emptyI)
    
    have "odd (card C)"
    proof(cases "C \<in> odd_components (graph_diff E X)")
      case True
      then show ?thesis unfolding odd_components_def odd_component_def
        by fastforce
    next
      case False
      then have "C \<in> singl_in_diff E X" 
        by (metis UnE \<open>C \<in> odd_comps_in_diff E X\<close> odd_comps_in_diff_def)
      then show ?thesis unfolding singl_in_diff_def 
        by force  
    qed
    have "v \<in> Vs E" 
      by (metis \<open>C \<in> odd_comps_in_diff E X\<close> \<open>connected_component (graph_diff E X) v = C\<close> component_in_E in_own_connected_component subsetD)
    have "v \<notin> X" 
      by (metis IntI \<open>C \<in> odd_comps_in_diff E X\<close> \<open>connected_component (graph_diff E X) v = C\<close> odd_comps_in_diff_not_in_X empty_iff in_own_connected_component)

    then show " \<exists>v\<in>Vs E-X. connected_component (graph_diff E X) v = C \<and> odd (card C)" 
      using \<open>connected_component (graph_diff E X) v = C\<close> \<open>odd (card C)\<close> \<open>v \<in> Vs E\<close> by blast
  }
  fix v
  assume "v \<in> Vs E" "v \<notin> X"
  assume " odd (card (connected_component (graph_diff E X) v))"
  show " connected_component (graph_diff E X) v \<in> odd_comps_in_diff E X"
  proof(cases "v \<in> Vs (graph_diff E X)")
    case True
    then have " connected_component
     (graph_diff E X) v \<in>  odd_components (graph_diff E X)" 
      unfolding odd_components_def odd_component_def
      using \<open>odd (card (connected_component (graph_diff E X) v))\<close> by blast
then show ?thesis 
  by (simp add: odd_comps_in_diff_def)
next
  case False
  have "(connected_component (graph_diff E X) v) = {v}"
    by (simp add: False connected_components_notE_singletons)
  have " v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)"
    by (simp add: False \<open>v \<in> Vs E\<close> \<open>v \<notin> X\<close>)
  then have "{v} \<in> singl_in_diff E X" 
    by (simp add: singl_in_diff_def)
  then show ?thesis 
    by (simp add: \<open>connected_component (graph_diff E X) v = {v}\<close> odd_comps_in_diff_def)
qed
qed

lemma new_component_subset_old:
  assumes "graph_invar E"
  assumes "Y \<subseteq> X"
  shows "connected_component (graph_diff E X) u \<subseteq> connected_component (graph_diff E Y) u"
  by (metis assms(1) assms(2) con_comp_subset graph_diff_subset graph_diff_trans subset_Un_eq)

lemma new_component_is_old:
  assumes "graph_invar E"
  assumes "Y \<subseteq> X"
  assumes "\<forall>y\<in>connected_component (graph_diff E Y) u. y \<notin> X"
  shows "connected_component (graph_diff E X) u = connected_component (graph_diff E Y) u"
proof
show "connected_component (graph_diff E Y) u
    \<subseteq> connected_component (graph_diff E X) u"
proof 
  fix y
  assume "y \<in> connected_component (graph_diff E Y) u" 
  then have "y \<notin> X" 
    using assms(3) by blast
  have "y = u \<or> (\<exists>p. walk_betw (graph_diff E Y) u p y)" 
    by (meson \<open>y \<in> connected_component (graph_diff E Y) u\<close> in_con_comp_has_walk)
  show "y \<in> connected_component (graph_diff E X) u"
  proof(cases "y = u")
case True
then show ?thesis 
  using \<open>y \<in> connected_component (graph_diff E Y) u\<close> assms(3) 
  
  by (simp add: in_own_connected_component)
next
  case False
  then obtain p where "walk_betw (graph_diff E Y) y p u" 
    by (meson \<open>y = u \<or> (\<exists>p. walk_betw (graph_diff E Y) u p y)\<close> walk_symmetric)
  have "set (edges_of_path p) \<subseteq> (graph_diff E Y)" 
    by (meson \<open>walk_betw (graph_diff E Y) y p u\<close> path_edges_subset walk_between_nonempty_path(1))

  have "\<forall>x\<in>set p. x \<in>  connected_component (graph_diff E Y) u" 
    by (metis \<open>walk_betw (graph_diff E Y) y p u\<close> \<open>y \<in> connected_component (graph_diff E Y) u\<close> connected_components_member_eq path_subset_conn_comp subsetD walk_between_nonempty_path(1) walk_between_nonempty_path(3))
  then have "\<forall>x\<in>set p. x \<notin> X" 
    using assms(3) by blast


 
  have "set (edges_of_path p) \<subseteq> (graph_diff E X)" 
  proof
    fix e
    assume "e \<in> set (edges_of_path p)" 
    then have "e \<inter> X = {}" 
      by (meson Int_emptyI \<open>\<forall>x\<in>set p. x \<notin> X\<close> v_in_edge_in_path_gen)
    then show "e \<in>  (graph_diff E X)" 
      by (metis (mono_tags, lifting) \<open>e \<in> set (edges_of_path p)\<close> \<open>set (edges_of_path p) \<subseteq> graph_diff E Y\<close> graph_diff_def mem_Collect_eq subsetD)
  qed

  then have "walk_betw (graph_diff E X) y p u" 
    by (smt (z3) False One_nat_def Suc_1 Suc_leI Suc_lessI \<open>walk_betw (graph_diff E Y) y p u\<close> diff_is_0_eq' edges_of_path.simps(1) edges_of_path_Vs edges_of_path_length empty_iff empty_set in_edges_of_path last_in_set length_pos_if_in_set neq0_conv path_edges_of_path_refl path_subset subset_empty walk_betw_def)
  then show ?thesis 
    by (meson connected_components_member_sym has_path_in_connected_component)
qed
qed
  show "connected_component (graph_diff E X) u
    \<subseteq> connected_component (graph_diff E Y) u" 
    by (simp add: assms(1) assms(2) new_component_subset_old)
qed

lemma every_el_in_barrier_connected:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  assumes "X \<subseteq> Vs E"
  assumes "barrier E X"
  shows"\<forall>x \<in>X. \<exists>y \<in>Vs E - X. {x, y} \<in> E"
proof
  fix x
  assume "x \<in> X"
  show "\<exists>y \<in>Vs E - X. {x, y} \<in> E"
  proof(rule ccontr)
   assume "\<not> (\<exists>y\<in>Vs E - X.  {x, y} \<in> E)"
   then have "\<forall>e \<in> E. x \<in> e \<longrightarrow> e \<subseteq> X" 
     by (smt (z3) Diff_iff \<open>x \<in> X\<close> assms(1) insert_Diff insert_commute insert_iff subset_iff vs_member_intro)
    have "(graph_diff E X) = (graph_diff E (X - {x}))"
         unfolding graph_diff_def 
         using \<open>\<forall>e\<in>E. x \<in> e \<longrightarrow> e \<subseteq> X\<close> assms(1) by fastforce
       then have "odd_components (graph_diff E X) = odd_components (graph_diff E (X - {x}))"
         by presburger
       have "(singl_in_diff E X) \<union> {{x}} = singl_in_diff E (X-{x})"
         unfolding singl_in_diff_def
       proof(safe) 
         {    fix  v
       assume "v \<in> Vs E"
       "v \<notin> X"
       "v \<notin> Vs (graph_diff E X)"
       show "\<exists>va. {v} = {va} \<and> va \<in> Vs E \<and> va \<notin> X - {x} \<and> va \<notin> Vs (graph_diff E (X - {x}))"
         
         by (metis \<open>graph_diff E X = graph_diff E (X - {x})\<close> \<open>v \<in> Vs E\<close> \<open>v \<notin> Vs (graph_diff E X)\<close> \<open>v \<notin> X\<close> \<open>x \<in> X\<close> insert_Diff insert_iff)
     }
     {
       show "\<exists>v. {x} = {v} \<and>
              v \<in> Vs E \<and>
              v \<notin> X - {x} \<and> v \<notin> Vs (graph_diff E (X - {x}))" 
         
         by (smt (verit, ccfv_threshold) Diff_iff Int_iff \<open>graph_diff E X = graph_diff E (X - {x})\<close> \<open>x \<in> X\<close> assms(1) assms(3) diff_disjoint_elements(2) empty_iff singletonI subsetD)

     }
     fix v
     assume " {v} \<notin> {}"
       "\<nexists>va. {v} = {va} \<and>
            va \<in> Vs E \<and> va \<notin> X \<and> va \<notin> Vs (graph_diff E X)"
       "v \<in> Vs E"
        "v \<notin> Vs (graph_diff E (X - {x}))"  "v \<notin> X"
     then show "v = x" 
       by (simp add: \<open>graph_diff E X = graph_diff E (X - {x})\<close>)
   qed

   then have "(odd_comps_in_diff E X) \<union> {{x}} = odd_comps_in_diff E (X-{x})" 
     unfolding odd_comps_in_diff_def 
     using \<open>graph_diff E X = graph_diff E (X - {x})\<close> by auto
   have "card (odd_comps_in_diff E (X-{x})) = 
        card ((odd_comps_in_diff E X) \<union> {{x}})" 
     
     using \<open>odd_comps_in_diff E X \<union> {{x}} = odd_comps_in_diff E (X - {x})\<close> by presburger
   have "(odd_comps_in_diff E X) \<inter> {{x}} = {}" 
     using \<open>x \<in> X\<close> odd_comps_in_diff_not_in_X by blast
   then have "card (odd_comps_in_diff E (X-{x})) = 
        card (odd_comps_in_diff E X) + card {{x}}" 
     by (metis \<open>card (odd_comps_in_diff E (X - {x})) = card (odd_comps_in_diff E X \<union> {{x}})\<close> assms(1) card_Un_disjoint diff_components_finite finite.emptyI finite.insertI)
   then have "card (odd_comps_in_diff E (X-{x})) = card X + 1" 
     by (metis One_nat_def assms(4) barrier_def card.empty card.insert finite.emptyI insert_absorb insert_not_empty)
   have "card (odd_comps_in_diff E (X-{x})) \<le> card (X-{x})" 
     by (metis \<open>x \<in> X\<close> assms(2) assms(3) insert_Diff insert_subset tutte_condition_def)
   then show False 
     by (metis One_nat_def \<open>card (odd_comps_in_diff E (X - {x})) = card X + 1\<close> assms(1) assms(3) card.empty card_Diff1_le card_gt_0_iff diff_add_inverse diff_is_0_eq' finite_subset le_trans zero_less_Suc)
 qed
qed

lemma singleton_set_is_union_singletons:
  assumes "finite X"
  shows "(\<Union>x\<in>X. {{x}}) = {{x} |x. x \<in> X}"
proof(safe)
qed(auto)

lemma card_singleton_set_same:
  assumes "finite X"
  assumes "A \<subseteq> {{x}|x. x \<in> X}"
  shows "card A = card {a. {a} \<in> A}" 
proof -
  let ?f = "(\<lambda>x. {{x}})" 
  have "A = (\<Union>x\<in>{a. {a} \<in> A}. ?f x)" 
  proof(safe)
    fix a
    assume "a \<in> A"
    then obtain x where "a = {x}" 
      using assms by blast
    then have "x \<in> {a. {a} \<in> A}"       using \<open>a \<in> A\<close> by fastforce

    show "a \<in> (\<Union>x\<in>{a. {a} \<in> A}. {{x}})" 
      using \<open>a = {x}\<close> \<open>x \<in> {a. {a} \<in> A}\<close> by blast
  qed
  have "finite {{x}|x. x \<in> X}"
    using assms(1) by auto 
  then have "finite A" using assms(2) finite_subset by blast

  then have "finite {a. {a} \<in> A}" using `A \<subseteq> {{x}|x. x \<in> X}`
proof(induct A) 
  case empty
  then show ?case 
    by simp
next
  case (insert x F)
  obtain a where "x = {a}" 
    using insert.prems by auto
  have "{a. {a} \<in> insert x F} =  {a. {a} \<in> F} \<union> {a}" using \<open>x = {a}\<close>
  proof(safe)
  qed
  then show "finite {a. {a} \<in> insert x F}" 
    using insert.hyps(3) insert.prems by force
qed
  have " \<forall>C\<in>{a. {a} \<in> A}. finite {{C}}" by auto
  have " \<forall>C1\<in>{a. {a} \<in> A}.
     \<forall>C2\<in>{a. {a} \<in> A}.
        C1 \<noteq> C2 \<longrightarrow> {{C1}} \<inter> {{C2}} = {} " 
    by blast
  then have "card (\<Union>x\<in>{a. {a} \<in> A}. ?f x) =  sum (\<lambda>x. (card (?f x))) {a. {a} \<in> A}" 
using union_card_is_sum[of "{a. {a} \<in> A}" ?f] 
  using \<open>\<forall>C\<in>{a. {a} \<in> A}. finite {{C}}\<close> \<open>finite {a. {a} \<in> A}\<close> by presburger
  then have "card (\<Union>x\<in>{a. {a} \<in> A}. ?f x) = card {a. {a} \<in> A}" 
    by (metis (no_types, lifting) One_nat_def card.empty card.insert card_eq_sum empty_iff finite.intros(1) sum.cong)
  then show "card A = card {a. {a} \<in> A}" 
    using \<open>A = (\<Union>x\<in>{a. {a} \<in> A}. {{x}})\<close> by simp
qed

lemma vertices_path_in_component:
  assumes "walk_betw E u p v"
  shows "\<forall>x\<in> set p. x \<in> connected_component E u"
  
  by (metis assms path_subset_conn_comp subsetD walk_between_nonempty_path(1) walk_between_nonempty_path(3))


lemma tutte2:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  shows "\<exists>M. perfect_matching E M" using assms

proof(induction "card (Vs E)" arbitrary: E rule: less_induct) 
  case less


  show "\<exists>M. perfect_matching E M"
  proof(cases "card (Vs E) \<le> 2")
    case True
    then show ?thesis
    proof(cases "card (Vs E) = 2")
      case True
      then obtain x y where "x \<in> Vs E \<and> y \<in> Vs E \<and> x \<noteq> y" 
        by (meson card_2_iff')
      then have "{x, y} =  Vs E" using True 
        by (smt (verit, best) card_2_iff doubleton_eq_iff insert_absorb insert_iff)
      have "\<forall> e \<in> E. e = {x, y}"
      proof
        fix e
        assume "e \<in> E"
        show "e = {x, y}"
        proof(rule ccontr)
          assume " e \<noteq> {x, y}"
          then obtain u where "u \<in> e \<and> (u \<noteq> x \<and> u \<noteq> y)" 
            by (metis "less.prems"(1) \<open>e \<in> E\<close> insertCI insert_commute)

          then have "u \<in> Vs E"
            using \<open>e \<in> E\<close> by blast
          then show False 
            using \<open>u \<in> e \<and> u \<noteq> x \<and> u \<noteq> y\<close> \<open>{x, y} = Vs E\<close> by blast
        qed
      qed
      then have "E = {{x, y}}" 
        using \<open>x \<in> Vs E \<and> y \<in> Vs E \<and> x \<noteq> y\<close> vs_member by fastforce
      then have "matching E" 
        using matching_def by fastforce
      moreover have "E \<subseteq> E" by auto
      ultimately have "perfect_matching E E" unfolding perfect_matching_def
        using "less.prems"(1) by blast
      then show ?thesis by auto
    next
      case False
      then show ?thesis
      proof(cases "card (Vs E) = 1")
        case True
        then show ?thesis 
          by (metis One_nat_def "less.prems"(1) card_Suc_eq card_mono connected_component_not_singleton connected_component_subset not_less singletonI)
      next
        case False
        then have "card (Vs E) = 0" using `card (Vs E) \<le> 2` `card (Vs E) \<noteq> 2` 
          by (metis One_nat_def Suc_1 bot_nat_0.extremum_uniqueI not_less_eq_eq verit_la_disequality)
        then show ?thesis
          by (metis "less.prems"(1) card_eq_0_iff equals0D matching_def2 order_refl perfect_matching_def)
      qed
    qed
  next
    case False


    have "even (card (Vs E))"
    proof(rule ccontr)
      assume "odd (card (Vs E))"
      have " {} \<subseteq> E" by auto
      then have "card (odd_comps_in_diff E {}) \<le> card {}" 
        by (metis "less.prems"(2) bot.extremum card.empty tutte_condition_def)
      then have "card (odd_comps_in_diff E {}) = 0" by simp
      have "graph_diff E {} = E" 
        by (simp add: graph_diff_def)
      then have "(singl_in_diff E {}) = {}" 
        unfolding singl_in_diff_def 
        by simp
      then have "odd_comps_in_diff E {} = odd_components E"
        unfolding odd_comps_in_diff_def using `graph_diff E {} = E`
        by simp
      have "card (odd_components E) \<ge> 1" using `odd (card (Vs E))` 
        by (metis "less.prems"(1) \<open>card (odd_comps_in_diff E {}) = 0\<close> \<open>odd_comps_in_diff E {} = odd_components E\<close> card.empty odd_card_imp_not_empty odd_components_eq_modulo_cardinality)
      then show False
        using \<open>card (odd_comps_in_diff E {}) = 0\<close> \<open>odd_comps_in_diff E {} = odd_components E\<close> by force
    qed
    have "\<forall>x \<in> (Vs E). card {x} \<ge> card (odd_comps_in_diff E {x})"
      using "less.prems"(2) 
      by (meson bot.extremum insert_subsetI tutte_condition_def)
    then  have "\<forall>x \<in> (Vs E). even (card {x} - card (odd_comps_in_diff E {x}))" 
      using `even (card (Vs E))` diff_odd_component_parity
      by (metis "less.prems"(1) bot.extremum insert_subsetI)
    then have "\<forall>x \<in> (Vs E).card (odd_comps_in_diff E {x}) = 1"
      by (metis One_nat_def Suc_leI \<open>\<forall>x\<in>Vs E. card (odd_comps_in_diff E {x}) \<le> card {x}\<close> antisym_conv card.empty card.insert dvd_diffD empty_iff finite.emptyI not_less odd_card_imp_not_empty odd_one zero_order(2))
    then have "\<forall>x \<in> (Vs E). barrier E {x}"
      by (metis barrier_def insert_not_empty is_singleton_altdef is_singleton_def)
    then have "\<exists> X \<subseteq> Vs E. barrier E X" 
      by (metis "less.prems"(1) False Suc_leI card.empty finite.simps insertCI insert_is_Un le_less_linear nat.simps(3) sup_ge1 zero_order(2))

    let ?B = "{X. X \<subseteq> Vs E \<and> barrier E X}"
    have "finite (Vs E)" 
      by (simp add: "less.prems"(1))
    then  have "finite ?B" by auto
    then  have "\<exists>X \<in> ?B. \<forall> Y \<in> ?B. Y \<noteq> X \<longrightarrow> \<not> (X \<subseteq> Y)" 
      by (metis (no_types, lifting) \<open>\<exists>X\<subseteq>Vs E. barrier E X\<close> empty_iff finite_has_maximal mem_Collect_eq)
    then obtain X where X_max:"X \<in> ?B \<and> ( \<forall> Y \<in> ?B. Y \<noteq> X \<longrightarrow> \<not> (X \<subseteq> Y))" by meson
    then have " X \<subseteq> Vs E \<and> barrier E X" by auto
    then have "card (odd_comps_in_diff E X) = card X" unfolding barrier_def by auto
    have "even_components (graph_diff E X) = {}"
    proof(rule ccontr)
      assume " even_components (graph_diff E X) \<noteq> {}"
      then obtain C where "C \<in>  even_components (graph_diff E X)" by auto
      then have "\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C"
        by (simp add:  even_components_def)
      then obtain v where "v \<in> C"
        by (smt (verit) even_components_def in_own_connected_component mem_Collect_eq)
      then have comp_C:"connected_component (graph_diff E X) v = C"
        by (metis \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> connected_components_member_eq)


      have "singl_in_diff E X \<subseteq> singl_in_diff E (X \<union> {v})"
      proof
        fix xs
        assume "xs \<in> singl_in_diff E X"

        then have "\<exists>x. xs = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)" 
          unfolding singl_in_diff_def by auto
        then obtain x where " xs = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)" 
          by presburger
        then have "x \<notin> X \<union> {v}" 
          by (metis UnE \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> in_connected_component_in_edges singletonD)
        have "x \<notin> Vs (graph_diff E X)" 
          by (simp add: \<open>xs = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)\<close>)
        then have "x \<notin> Vs (graph_diff E (X \<union> {v}))" unfolding graph_diff_def
          by (simp add: vs_member)
        then have "{x} \<in> singl_in_diff E (X \<union> {v})" unfolding
            singl_in_diff_def
          using \<open>x \<notin> X \<union> {v}\<close> \<open>xs = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)\<close> by blast
        then show "xs \<in> singl_in_diff E (X \<union> {v})" 
          by (simp add: \<open>xs = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)\<close>)
      qed


      have "graph_diff E (X\<union>{v}) \<subseteq> graph_diff E X" unfolding graph_diff_def
        by (simp add: Collect_mono)






      have "odd_components (graph_diff E X) \<subseteq> odd_components (graph_diff E (X \<union> {v}))"
      proof
        fix C'
        assume "C' \<in> odd_components (graph_diff E X)"
        then have "\<exists>x \<in> Vs (graph_diff E X). 
      connected_component (graph_diff E X) x = C' \<and> odd (card C')"
          unfolding odd_components_def odd_component_def
          by blast
        then  obtain x where odd_x:"x \<in> Vs (graph_diff E X) \<and>
                          connected_component (graph_diff E X) x = C' \<and> 
                            odd (card C')" by auto


        then have "x \<notin> C" 
          by (smt (verit) \<open>C \<in> even_components (graph_diff E X)\<close> connected_components_member_eq even_components_def mem_Collect_eq)
        then have "x \<noteq> v" 
          using \<open>v \<in> C\<close> by blast
        then have "\<exists>e \<in> (graph_diff E X). x \<in> e" 
          by (meson odd_x vs_member_elim)
        then obtain e where "e \<in> (graph_diff E X) \<and> x \<in> e" by auto
        then have "e \<subseteq> C'" 
          by (smt (z3) "less.prems"(1) empty_subsetI graph_diff_subset in_con_comp_insert in_own_connected_component insertE insert_Diff insert_commute insert_subset odd_x singletonD)

        then have "e \<in> component_edges (graph_diff E X) C'"
          unfolding component_edges_def 
          by (smt (verit) "less.prems"(1) \<open>e \<in> graph_diff E X \<and> x \<in> e\<close> graph_diff_subset insert_Diff insert_subset mem_Collect_eq) 
        have "\<forall>z \<in> C'. z \<in>   Vs (graph_diff E (X \<union> {v}))"
        proof
          fix z
          assume "z\<in> C'" 
          have "z\<noteq>v"
            by (metis \<open>x \<notin> C\<close> \<open>z \<in> C'\<close> comp_C connected_components_member_sym odd_x)
          then have "z \<notin> C" 
            by (metis \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>x \<notin> C\<close> \<open>z \<in> C'\<close> connected_components_member_eq in_own_connected_component odd_x)

          have "\<exists>e \<in> E. e \<inter> X = {} \<and> z \<in> e" 
            by (smt (z3) \<open>\<And>thesis. (\<And>x. x \<in> Vs (graph_diff E X) \<and> connected_component (graph_diff E X) x = C' \<and> odd (card C') \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>z \<in> C'\<close> graph_diff_def in_connected_component_in_edges mem_Collect_eq vs_member)
          then obtain e where "e\<in>E \<and>  e \<inter> X = {} \<and> z \<in> e" by auto
          have "v \<notin> e" 
          proof(rule ccontr)
            assume "\<not> v \<notin> e"
            then have "v \<in> e"  by auto
            then have "e = {z, v}" using `graph_invar E` `z \<noteq> v` 
              using \<open>e \<in> E \<and> e \<inter> X = {} \<and> z \<in> e\<close> by fastforce
            then have "e \<in> (graph_diff E X)"
              using \<open>e \<in> E \<and> e \<inter> X = {} \<and> z \<in> e\<close> graph_diff_def by auto
            then have "z \<in> connected_component (graph_diff E X) v"
              by (metis \<open>e = {z, v}\<close> in_con_comp_insert insert_Diff insert_commute)
            then have "z \<in> C" 
              by (simp add: comp_C)
            then show False 
              using \<open>z \<notin> C\<close> by auto
          qed
          then have "e\<in>E \<and>  e \<inter> (X\<inter>{v}) = {} \<and> z \<in> e" 
            using \<open>e \<in> E \<and> e \<inter> X = {} \<and> z \<in> e\<close> by blast
          then have "e \<in> graph_diff E (X\<union>{v})" unfolding graph_diff_def
            using \<open>e \<in> E \<and> e \<inter> X = {} \<and> z \<in> e\<close> \<open>v \<notin> e\<close> by blast
          then show "z\<in> Vs (graph_diff E (X \<union> {v}))" 
            using \<open>e \<in> E \<and> e \<inter> (X \<inter> {v}) = {} \<and> z \<in> e\<close> by blast
        qed
        have "\<forall>z \<in> C'. z \<in> connected_component (graph_diff E (X\<union>{v})) x"
        proof
          fix z
          assume "z\<in>C'"
          then have "(\<exists>p. walk_betw (graph_diff E X) x p z)" 
            by (metis in_connected_component_has_path odd_x)



          then obtain p where "walk_betw (graph_diff E X) x p z" by auto




          have "walk_betw (graph_diff E (X\<union>{v})) x p z"
          proof
            show "p \<noteq> []" 
              using \<open>walk_betw (graph_diff E X) x p z\<close> by auto
            show "hd p = x"
              using \<open>walk_betw (graph_diff E X) x p z\<close> by auto
            show "last p = z"
              using \<open>walk_betw (graph_diff E X) x p z\<close> by auto
            have "path (graph_diff E X) p" 
              by (meson \<open>walk_betw (graph_diff E X) x p z\<close> walk_betw_def)

            have "graph_invar (graph_diff E X)" 
              by (metis "less.prems"(1) \<open>X \<subseteq> Vs E \<and> barrier E X\<close> diff_is_union_elements finite_Un graph_diff_subset insert_Diff insert_subset)
            have "C' \<in> connected_components (graph_diff E X)" 
              by (simp add: \<open>C' \<in> odd_components (graph_diff E X)\<close> \<open>graph_invar (graph_diff E X)\<close> components_is_union_even_and_odd)
            have "hd p \<in> C'" 
              by (metis \<open>hd p = x\<close> in_own_connected_component odd_x)
            have "(component_edges (graph_diff E X) C') \<noteq> {}" 
              using \<open>e \<in> component_edges (graph_diff E X) C'\<close> by auto



            have "path (component_edges (graph_diff E X) C')  p" 
              by (simp add: \<open>C' \<in> connected_components (graph_diff E X)\<close> \<open>component_edges (graph_diff E X) C' \<noteq> {}\<close> \<open>graph_invar (graph_diff E X)\<close> \<open>hd p \<in> C'\<close> \<open>path (graph_diff E X) p\<close> path_in_comp_edges)

            have "(component_edges (graph_diff E X) C') = (component_edges (graph_diff E (X\<union>{v})) C')"
            proof(safe)
              { fix e
                assume "e \<in> component_edges (graph_diff E X) C'"
                then have "e \<subseteq> C'" unfolding component_edges_def
                  by blast
                then have "e \<in> (graph_diff E X)" using `e \<in> component_edges (graph_diff E X) C'`
                  using Berge.component_edges_subset by blast
                have "v \<notin> e" 
                  by (metis \<open>C' \<in> connected_components (graph_diff E X)\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>e \<subseteq> C'\<close> \<open>v \<in> C\<close> \<open>x \<notin> C\<close> connected_components_closed' connected_components_member_sym odd_x subsetD)
                then have "e \<inter> (X \<union> {v}) = {}" 
                  by (smt (verit) "less.prems"(1) DiffD2 Diff_insert_absorb UnE UnionI Vs_def \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>e \<in> graph_diff E X\<close> diff_disjoint_elements(2) disjoint_iff_not_equal)
                then have "e \<in> (graph_diff E (X\<union>{v}))" 
                  by (metis (mono_tags, lifting) \<open>e \<in> graph_diff E X\<close> graph_diff_def mem_Collect_eq)
                then show "e \<in> (component_edges (graph_diff E (X\<union>{v})) C')" 
                  unfolding component_edges_def 
                  using \<open>e \<in> graph_diff E X\<close> \<open>e \<subseteq> C'\<close> \<open>graph_invar (graph_diff E X)\<close> by fastforce
              }
              fix e
              assume "e \<in> (component_edges (graph_diff E (X\<union>{v})) C')"
              then have "e \<subseteq> C'" unfolding component_edges_def
                by blast
              then have "e \<in> (graph_diff E (X\<union>{v}))" 
                using \<open>e \<in> component_edges (graph_diff E (X \<union> {v})) C'\<close> Berge.component_edges_subset by blast

              then have "e \<inter> X = {}" unfolding graph_diff_def  
                by blast
              then have "e \<in> (graph_diff E X)" unfolding graph_diff_def 
                using \<open>e \<in> graph_diff E (X \<union> {v})\<close> graph_diff_subset by blast
              then show "e \<in> component_edges (graph_diff E X) C'" unfolding component_edges_def  
                using \<open>e \<subseteq> C'\<close> \<open>graph_invar (graph_diff E X)\<close> by fastforce
            qed

            then show "path (graph_diff E (X \<union> {v})) p"
              using `path (component_edges (graph_diff E X) C')  p` 
              by (metis Berge.component_edges_subset path_subset)

          qed

          then show "z \<in> connected_component (graph_diff E (X\<union>{v})) x" 
            by (simp add: has_path_in_connected_component)
        qed

        then have "C' \<subseteq> connected_component (graph_diff E (X\<union>{v})) x"
          by blast
        have "connected_component (graph_diff E (X \<union> {v})) x \<subseteq> C'"
        proof
          fix z
          assume "z \<in> connected_component (graph_diff E (X \<union> {v})) x"
          then have "\<exists>p. walk_betw (graph_diff E (X\<union>{v})) x p z" 
            by (meson \<open>\<forall>z\<in>C'. z \<in> Vs (graph_diff E (X \<union> {v}))\<close> \<open>e \<in> graph_diff E X \<and> x \<in> e\<close> \<open>e \<subseteq> C'\<close> in_connected_component_has_path subsetD)
          then obtain p where "walk_betw (graph_diff E (X\<union>{v})) x p z" by auto
          then have "path (graph_diff E (X\<union>{v})) p" 
            by (meson walk_betw_def)
          then have "path (graph_diff E X) p" 
            using \<open>graph_diff E (X \<union> {v}) \<subseteq> graph_diff E X\<close> path_subset by blast
          then have "walk_betw (graph_diff E X) x p z" 
            by (meson \<open>graph_diff E (X \<union> {v}) \<subseteq> graph_diff E X\<close> \<open>walk_betw (graph_diff E (X \<union> {v})) x p z\<close> walk_subset)
          then show "z \<in> C'" 
            using odd_x by blast
        qed
        then have "C' = connected_component (graph_diff E (X\<union>{v})) x" 
          using \<open>C' \<subseteq> connected_component (graph_diff E (X \<union> {v})) x\<close> by blast
        then show "C' \<in> odd_components (graph_diff E (X \<union> {v}))"
          unfolding odd_components_def odd_component_def
          using \<open>\<forall>z\<in>C'. z \<in> Vs (graph_diff E (X \<union> {v}))\<close> \<open>e \<in> graph_diff E X \<and> x \<in> e\<close> \<open>e \<subseteq> C'\<close> odd_x by fastforce
      qed
      then have "odd_comps_in_diff E X \<subseteq> odd_comps_in_diff E (X \<union> {v})"
        by (metis \<open>singl_in_diff E X \<subseteq> singl_in_diff E (X \<union> {v})\<close> odd_comps_in_diff_def sup.mono)
      
      show False
      proof(cases "\<exists>x \<in> (C-{v}). x \<notin> Vs (graph_diff E (X \<union> {v}))")
        case True
        then  obtain x where "x \<in> (C-{v}) \<and> (x \<notin> Vs (graph_diff E (X \<union> {v})))" by auto
        then have "x \<in> Vs E"
          by (metis DiffD1 Diff_insert_absorb Vs_subset \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> connected_component_subset graph_diff_subset subset_Diff_insert)

        then have "x \<notin> X \<and> x \<notin> Vs (graph_diff E (X\<union>{v}))" 
          by (smt (verit, best) "less.prems"(1) DiffD1 \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> connected_component_subset diff_disjoint_elements(2) disjoint_iff_not_equal subset_iff)
        then have "{x} \<in> singl_in_diff E (X \<union> {v})" unfolding singl_in_diff_def

          using \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> \<open>x \<in> Vs E\<close> by auto
        have "x \<in> Vs (graph_diff E X)" 
          by (metis DiffD1 Diff_insert_absorb \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> connected_component_subset subset_Diff_insert)
        then have "{x} \<notin> singl_in_diff E (X)" unfolding singl_in_diff_def 
          by blast
        have "{x} \<notin> odd_components (graph_diff E X)" 
          unfolding odd_components_def odd_component_def
          by (smt (verit, del_insts) Diff_insert_absorb \<open>v \<in> C\<close> \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> comp_C connected_components_member_eq insert_iff mem_Collect_eq mk_disjoint_insert singletonI singleton_insert_inj_eq')
        then have "{x} \<notin> odd_comps_in_diff E X"  unfolding odd_comps_in_diff_def

          using \<open>{x} \<notin> singl_in_diff E X\<close> by force

        then have "odd_comps_in_diff E X \<subset> odd_comps_in_diff E (X \<union> {v})" 
          unfolding odd_comps_in_diff_def 
          by (metis UnCI \<open>odd_comps_in_diff E X \<subseteq> odd_comps_in_diff E (X \<union> {v})\<close> \<open>{x} \<in> singl_in_diff E (X \<union> {v})\<close> odd_comps_in_diff_def psubsetI)

        have "finite (connected_components (graph_diff E (X \<union> {v})))"

          by (meson "less.prems"(1) Vs_subset finite_con_comps finite_subset graph_diff_subset)
        have "  (odd_components (graph_diff E (X \<union> {v})))
          \<subseteq> connected_components (graph_diff E (X \<union> {v}))"
          unfolding odd_components_def 
          unfolding connected_components_def odd_component_def
          by blast
        then have "finite  (odd_components (graph_diff E (X \<union> {v})))" 

          using \<open>finite (connected_components (graph_diff E (X \<union> {v})))\<close> finite_subset by blast

        have "finite ( singl_in_diff E (X \<union> {v}))" 
          by (smt (verit) "less.prems"(1) Un_insert_right Vs_def Vs_subset \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> boolean_algebra_cancel.sup0 connected_component_subset diff_is_union_elements finite_Un finite_UnionD graph_diff_subset insert_Diff insert_subset)

        then have "finite (odd_comps_in_diff E (X \<union> {v}))" 
          by (metis \<open>finite (odd_components (graph_diff E (X \<union> {v})))\<close> odd_comps_in_diff_def finite_Un)
        then have "card (odd_comps_in_diff E X) < card (odd_comps_in_diff E (X \<union> {v}))"

          by (meson \<open>odd_comps_in_diff E X \<subset> odd_comps_in_diff E (X \<union> {v})\<close> psubset_card_mono)
        then have "card(X) + 1 \<le> card (odd_comps_in_diff E (X \<union> {v}))" 
          by (simp add: \<open>card (odd_comps_in_diff E X) = card X\<close>)
        have "card (X \<union> {v}) = (card X) + 1" 
          by (metis "less.prems"(1) IntI One_nat_def Un_insert_right \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> add.right_neutral add_Suc_right card.insert diff_disjoint_elements(2) empty_iff finite_subset in_connected_component_in_edges sup_bot_right)

        have "card (odd_comps_in_diff E (X \<union> {v})) \<le> card (X \<union> {v})" using assms(2) unfolding tutte_condition_def

          by (metis "less.prems"(2) DiffD1 Un_insert_right \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>v \<in> C\<close> \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> \<open>x \<in> Vs E\<close> boolean_algebra_cancel.sup0 comp_C connected_components_member_eq diff_connected_component_subset insert_Diff insert_subset tutte_condition_def)
        then have "card (odd_comps_in_diff E (X \<union> {v})) \<le> (card X) + 1" 

          using \<open>card (X \<union> {v}) = card X + 1\<close> by presburger
        then have "barrier E (X \<union> {v})" 
          by (metis Un_empty \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>card (X \<union> {v}) = card X + 1\<close> \<open>card X + 1 \<le> card (odd_comps_in_diff E (X \<union> {v}))\<close> barrier_def le_antisym)
        then have " (X \<union> {v}) \<in> ?B" 
          by (metis DiffD1 Un_insert_right \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> \<open>x \<in> Vs E\<close> connected_components_member_eq diff_connected_component_subset insert_subsetI mem_Collect_eq subsetD sup_bot_right)
        then show ?thesis 
          by (metis X_max \<open>card (odd_comps_in_diff E X) < card (odd_comps_in_diff E (X \<union> {v}))\<close> sup.strict_order_iff sup_ge1)
      next
        case False
        assume "\<not> (\<exists>x\<in>C - {v}. x \<notin> Vs (graph_diff E (X \<union> {v})))"
        then have "\<forall>x\<in>C - {v}. x \<in> Vs (graph_diff E (X \<union> {v}))" by auto


        have "\<exists> C' \<in> connected_components (graph_diff E (X \<union> {v})).C' \<subseteq> (C-{v}) \<and> odd (card C')"
        proof(rule ccontr)
          assume "\<not> (\<exists>C'\<in>connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> (C-{v}) \<and> odd (card C'))"
          then have "\<forall> C' \<in> connected_components (graph_diff E (X \<union> {v})).  \<not> C' \<subseteq> (C-{v}) \<or> even (card C')"
            by blast
          then have "\<forall> C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> (C-{v}) \<longrightarrow> (card C') \<noteq> 1"
            by fastforce
          then have "\<forall> C' \<in> connected_components (graph_diff E (X \<union> {v})).
     C' \<subseteq> (C-{v}) \<longrightarrow> (\<exists>x y. {x, y} \<subseteq> C')"
            by (metis connected_comp_nempty empty_subsetI equals0I insert_subset)

          have "\<forall> C' \<in> connected_components (graph_diff E (X \<union> {v})).
     C' \<subseteq> (C-{v}) \<longrightarrow> component_edges (graph_diff E (X \<union> {v})) C' \<noteq> {}"
          proof
            fix C'
            assume "C' \<in> connected_components (graph_diff E (X \<union> {v}))"
            show " C' \<subseteq> (C-{v}) \<longrightarrow> component_edges (graph_diff E (X \<union> {v})) C' \<noteq> {}"
            proof
              assume "C' \<subseteq> C - {v}"
              have "(card C') \<noteq> 1" 
                using \<open>C' \<in> connected_components (graph_diff E (X \<union> {v}))\<close> \<open>C' \<subseteq> C - {v}\<close> \<open>\<forall>C'\<in>connected_components (graph_diff E (X \<union> {v})). \<not> C' \<subseteq> C - {v} \<or> even (card C')\<close> by fastforce
              then have "(\<exists>x y. {x, y} \<subseteq> C' \<and> x \<noteq> y)" 
                by (metis \<open>C' \<in> connected_components (graph_diff E (X \<union> {v}))\<close> connected_comp_nempty empty_subsetI insert_subset is_singletonI' is_singleton_altdef)
              then obtain x y where "{x, y} \<subseteq> C' \<and> x \<noteq> y" by auto
              then have "y \<in> connected_component (graph_diff E (X \<union> {v})) x" 
                by (metis \<open>C' \<in> connected_components (graph_diff E (X \<union> {v}))\<close> connected_components_closed' insert_subset)
              then have "\<exists> p. walk_betw (graph_diff E (X \<union> {v})) x p y" 
                by (meson \<open>C' \<in> connected_components (graph_diff E (X \<union> {v}))\<close> \<open>{x, y} \<subseteq> C' \<and> x \<noteq> y\<close> connected_comp_verts_in_verts in_connected_component_has_path insert_subset)
              then obtain p where p_walk: "walk_betw (graph_diff E (X \<union> {v})) x p y" by auto
              then have "path (graph_diff E (X \<union> {v})) p"
                by (meson walk_betw_def)
              have "p \<noteq> []" using p_walk by auto

              have "hd p = x \<and> last p = y" using p_walk by auto
              then have "size p \<ge> 2" using  `{x, y} \<subseteq> C' \<and> x \<noteq> y` 
                by (metis One_nat_def Suc_1 Suc_leI \<open>p \<noteq> []\<close> antisym_conv1 append.simps(1) diff_add_inverse2 diff_less hd_Cons_tl last_snoc length_0_conv lessI less_Suc0 list.size(4) not_le)
              then have "{x, hd (tl p)} \<in> (graph_diff E (X \<union> {v}))" 
                by (metis One_nat_def Suc_1 Suc_pred \<open>hd p = x \<and> last p = y\<close> \<open>p \<noteq> []\<close> \<open>path (graph_diff E (X \<union> {v})) p\<close> hd_Cons_tl length_greater_0_conv length_tl lessI list.size(3) not_le path_2)
              have " hd (tl p) \<in> C'" 
                by (meson \<open>C' \<in> connected_components (graph_diff E (X \<union> {v}))\<close> \<open>{x, hd (tl p)} \<in> graph_diff E (X \<union> {v})\<close> \<open>{x, y} \<subseteq> C' \<and> x \<noteq> y\<close> edges_are_walks in_con_compI insert_subset)
              then have "{x, hd (tl p)} \<subseteq> C'" 
                using \<open>{x, y} \<subseteq> C' \<and> x \<noteq> y\<close> by blast
              then show " component_edges (graph_diff E (X \<union> {v})) C' \<noteq> {}" 
                by (smt (verit) \<open>{x, hd (tl p)} \<in> graph_diff E (X \<union> {v})\<close> component_edges_def empty_Collect_eq)
            qed
          qed

          have "(C-{v}) = \<Union>{C'. C' \<in> connected_components (graph_diff E (X \<union> {v})) \<and> C' \<subseteq> (C-{v})}"
          proof
            show "C - {v} \<subseteq> \<Union> {C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v}}"
            proof
              fix x
              assume "x \<in> C - {v}"

              then have "connected_component (graph_diff E X) x = C" 
                by (metis DiffD1 comp_C connected_components_member_eq)




              then have "\<exists> C'. C' = connected_component (graph_diff E (X \<union> {v})) x"
                by blast
              then obtain C' where "C' = connected_component (graph_diff E (X \<union> {v})) x" by auto
              then have "C' \<subseteq> C - {v}"
                by (smt (verit, ccfv_SIG) "less.prems"(1) Diff_empty Un_insert_right Vs_subset \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>graph_diff E (X \<union> {v}) \<subseteq> graph_diff E X\<close> \<open>x \<in> C - {v}\<close> boolean_algebra_cancel.sup0 con_comp_subset connected_components_member_eq diff_disjoint_elements(2) disjoint_insert(2) graph_diff_subset in_connected_component_in_edges insert_subsetI subset_Diff_insert subset_iff)

              then have "C' \<in> connected_components (graph_diff E (X \<union> {v}))"
                unfolding connected_components_def
                using `C' = connected_component (graph_diff E (X \<union> {v})) x` 
                using False \<open>x \<in> C - {v}\<close> by fastforce

              then have "C' \<in> {C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v}}"

                using \<open>C' \<subseteq> C - {v}\<close> by blast
              then  show "x \<in> \<Union> {C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v}}"

                using UnionI \<open>C' = connected_component (graph_diff E (X \<union> {v})) x\<close> in_own_connected_component by fastforce
            qed

            show "\<Union> {C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v}} \<subseteq> C - {v}"

              by blast
          qed
          let ?A = "{C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v}}"
          have "finite ?A"

            by (metis (no_types, lifting) "less.prems"(1) Diff_empty Vs_subset \<open>C - {v} = \<Union> {C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v}}\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> connected_component_subset finite_Diff_insert finite_UnionD finite_subset graph_diff_subset)
          have "\<forall>C \<in> ?A. finite C" 
            by (metis (no_types, lifting) "less.prems"(1) Vs_subset connected_component_subs_Vs finite_subset graph_diff_subset mem_Collect_eq)
          have "\<forall>C1\<in>?A. \<forall>C2 \<in>?A. C1 \<noteq> C2 \<longrightarrow> C1 \<inter> C2 = {}" 
            by (metis (no_types, lifting) connected_components_disj mem_Collect_eq)
          then have "sum (\<lambda> C. card C) ?A = card (\<Union>C\<in>?A. C)" using union_card_is_sum[of ?A "(\<lambda> C. C)"]

            using \<open>\<forall>C\<in>{C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v}}. finite C\<close> \<open>finite {C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v}}\<close> by blast
          then have "even (sum (\<lambda> C. card C) ?A)" 
            by (metis (no_types, lifting) \<open>\<not> (\<exists>C'\<in>connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v} \<and> odd (card C'))\<close> dvd_sum mem_Collect_eq)
          then have "even (card (C -{v}))" 
            using \<open>C - {v} = \<Union> {C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v}}\<close> \<open>sum card {C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v}} = card (\<Union>C\<in>{C' \<in> connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v}}. C)\<close> by fastforce
          have "even (card C)" 
            using \<open>C \<in> even_components (graph_diff E X)\<close> even_components_def by fastforce

          have "odd (card (C -{v}))" using `even (card C)` 
            by (smt (verit, ccfv_threshold) "less.prems"(1) Diff_empty Diff_insert_absorb Diff_single_insert One_nat_def Vs_subset \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> card.empty card.insert card_Diff_subset card_gt_0_iff card_le_sym_Diff connected_component_subset double_diff dvd_diffD1 empty_iff empty_subsetI finite_Diff finite_subset graph_diff_subset insert_Diff nat_le_linear not_less odd_one)

          then show False 
            using \<open>even (card (C - {v}))\<close> by blast
        qed
        then obtain C' where "C'\<in>connected_components (graph_diff E (X \<union> {v})) \<and>
     C' \<subseteq> C - {v} \<and> odd (card C')" by auto

        then have "C' \<in> odd_components (graph_diff E (X \<union> {v}))" 
          unfolding odd_components_def odd_component_def
          by (smt (z3) connected_comp_has_vert mem_Collect_eq)
        then have "C'  \<notin> odd_components (graph_diff E (X))" 
          unfolding singl_in_diff_def 
          by (metis \<open>C' \<in> connected_components (graph_diff E (X \<union> {v})) \<and> C' \<subseteq> C - {v} \<and> odd (card C')\<close> comp_C connected_comp_has_vert connected_components_member_eq in_own_connected_component insert_Diff insert_iff odd_comps_in_diffI1 odd_comps_in_diff_is_component subsetD subset_Diff_insert)

        have "C'  \<notin> singl_in_diff E X" unfolding singl_in_diff_def 

          by (smt (verit, ccfv_threshold) Vs_subset \<open>C' \<in> connected_components (graph_diff E (X \<union> {v})) \<and> C' \<subseteq> C - {v} \<and> odd (card C')\<close> \<open>graph_diff E (X \<union> {v}) \<subseteq> graph_diff E X\<close> connected_component_subs_Vs insert_subset mem_Collect_eq order_trans)
        then have "C' \<notin> odd_comps_in_diff E X"  unfolding odd_comps_in_diff_def

          using \<open>C' \<notin> odd_components (graph_diff E (X))\<close> by force

        then have "odd_comps_in_diff E X \<subset> odd_comps_in_diff E (X \<union> {v})" 
          unfolding odd_comps_in_diff_def 
          by (metis UnCI \<open>C' \<in> odd_components (graph_diff E (X \<union> {v}))\<close> \<open>odd_comps_in_diff E X \<subseteq> odd_comps_in_diff E (X \<union> {v})\<close> odd_comps_in_diff_def psubsetI)

        have "finite (connected_components (graph_diff E (X \<union> {v})))"

          by (meson "less.prems"(1) Vs_subset finite_con_comps finite_subset graph_diff_subset)
        have "  (odd_components (graph_diff E (X \<union> {v})))
          \<subseteq> connected_components (graph_diff E (X \<union> {v}))"
          unfolding odd_components_def odd_component_def
          unfolding connected_components_def 
          by blast
        then have "finite  (odd_components (graph_diff E (X \<union> {v})))" 

          using \<open>finite (connected_components (graph_diff E (X \<union> {v})))\<close> finite_subset by blast

        have "finite ( singl_in_diff E (X \<union> {v}))" 
          by (smt (verit) "less.prems"(1) Un_insert_right Vs_def Vs_subset \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> boolean_algebra_cancel.sup0 connected_component_subset diff_is_union_elements finite_Un finite_UnionD graph_diff_subset insert_Diff insert_subset)

        then have "finite (odd_comps_in_diff E (X \<union> {v}))" 
          by (metis \<open>finite (odd_components (graph_diff E (X \<union> {v})))\<close> odd_comps_in_diff_def finite_Un)
        then have "card (odd_comps_in_diff E X) < card (odd_comps_in_diff E (X \<union> {v}))"

          by (meson \<open>odd_comps_in_diff E X \<subset> odd_comps_in_diff E (X \<union> {v})\<close> psubset_card_mono)
        then have "card(X) + 1 \<le> card (odd_comps_in_diff E (X \<union> {v}))" 
          by (simp add: \<open>card (odd_comps_in_diff E X) = card X\<close>)
        have "card (X \<union> {v}) = (card X) + 1" 
          by (metis "less.prems"(1) IntI One_nat_def Un_insert_right \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> add.right_neutral add_Suc_right card.insert diff_disjoint_elements(2) empty_iff finite_subset in_connected_component_in_edges sup_bot_right)

        have "card (odd_comps_in_diff E (X \<union> {v})) \<le> card (X \<union> {v})" using assms(2) unfolding tutte_condition_def

          by (smt (verit, ccfv_threshold) "less.prems"(2) "less.prems"(1) Un_insert_right Un_upper1 \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> boolean_algebra_cancel.sup0 connected_component_subset diff_is_union_elements insert_Diff insert_subset tutte_condition_def)
        then have "card (odd_comps_in_diff E (X \<union> {v})) \<le> (card X) + 1" 

          using \<open>card (X \<union> {v}) = card X + 1\<close> by presburger
        then have "barrier E (X \<union> {v})" 
          by (metis Un_empty \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>card (X \<union> {v}) = card X + 1\<close> \<open>card X + 1 \<le> card (odd_comps_in_diff E (X \<union> {v}))\<close> barrier_def le_antisym)
        then have " (X \<union> {v}) \<in> ?B" 
          by (metis Un_insert_right Vs_subset \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> connected_component_subset graph_diff_subset insert_subsetI mem_Collect_eq subsetD sup_bot_right)
        then show ?thesis 
          by (metis X_max \<open>card (odd_comps_in_diff E X) < card (odd_comps_in_diff E (X \<union> {v}))\<close> sup.strict_order_iff sup_ge1)
      qed
    qed















    then have "{C. \<exists>x \<in> Vs E - X. C = connected_component (graph_diff E X) x \<and> even (card C)} = {}"
      unfolding even_components_def 
      by (smt (verit, ccfv_threshold) Collect_empty_eq One_nat_def card.empty card.insert connected_components_notE_singletons empty_iff finite.emptyI odd_one)


    have "(odd_comps_in_diff E X) = {C. \<exists>x \<in> Vs E - X. C = connected_component (graph_diff E X) x \<and> odd (card C)}" 
      using odd_comps_in_diff_are_components[of E X]  
      using Collect_cong less.prems(1) by auto

    then have "(odd_comps_in_diff E X) = {C. \<exists>x \<in> Vs E - X. C = connected_component (graph_diff E X) x}"
      
      by (smt (verit, ccfv_SIG) Collect_cong DiffD1 \<open>\<forall>x\<in>Vs E. card (odd_comps_in_diff E {x}) = 1\<close> \<open>\<forall>x\<in>Vs E. card (odd_comps_in_diff E {x}) \<le> card {x}\<close> \<open>\<forall>x\<in>Vs E. even (card {x} - card (odd_comps_in_diff E {x}))\<close> \<open>even_components (graph_diff E X) = {}\<close> bex_empty connected_components_notE_singletons dvd_diffD1 even_components_def mem_Collect_eq odd_one)


    have "\<forall>x \<in>X. \<exists>y \<in>Vs E - X. {x, y} \<in> E" 
      by (simp add: \<open>X \<subseteq> Vs E \<and> barrier E X\<close> every_el_in_barrier_connected less.prems(1) less.prems(2))
    




    let ?G' = "{e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x,{y}}}"

    have "\<forall>x \<in> X. {x} \<in> Vs ?G'" 
    proof
      fix x
      assume "x \<in> X"
      then obtain y where  "y \<in>Vs E - X \<and>  {x, y} \<in> E" 
        by (meson \<open>\<forall>x\<in>X. \<exists>y\<in>Vs E - X. {x, y} \<in> E\<close>)
        then have "{connected_component (graph_diff E X) y,{x}} \<in> ?G'" 
          by (smt (verit, ccfv_threshold) DiffD2 \<open>x \<in> X\<close> insert_commute mem_Collect_eq)
        then show "{x} \<in> Vs ?G'" by auto
      qed


      let ?f = "(\<lambda>x. {{x}})"
      have "Vs ?G' - (odd_comps_in_diff E X) = (\<Union>x\<in>X. ?f x)"
      proof(safe)
        {
          fix y
          assume "y \<in> Vs ?G'"
          assume "y \<notin> (odd_comps_in_diff E X)"
          then have "\<nexists>x. x\<in> Vs E - X \<and> y = connected_component (graph_diff E X) x"
            
            using \<open>odd_comps_in_diff E X = {C. \<exists>x\<in>Vs E - X. C = connected_component (graph_diff E X) x}\<close> by blast
          obtain e' u v where "{u, v} \<in> E \<and> u \<notin> X \<and> v \<in> X \<and> e' = {connected_component (graph_diff E X) u, {v}} \<and> y \<in> e'"
            using `y \<in> Vs ?G'` 
            by (smt (verit, del_insts) mem_Collect_eq vs_member_elim)
          then have "\<exists>u. u \<in> X \<and> y = {u}" 
            by (metis Diff_iff \<open>\<nexists>x. x \<in> Vs E - X \<and> y = connected_component (graph_diff E X) x\<close> edges_are_Vs insert_iff singletonD)
          then show "y \<in> (\<Union>x\<in>X. ?f x)" 
            by blast
          
        }
        {
        fix y
        assume "y \<in> X" 
        show "{y} \<in> Vs ?G'" 
          using \<open>\<forall>x\<in>X. {x} \<in> Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> \<open>y \<in> X\<close> by fastforce
      }
      fix y
      assume "y \<in> X"
      assume "{y} \<in> odd_comps_in_diff E X"
      show False 
        by (metis IntI \<open>y \<in> X\<close> \<open>{y} \<in> odd_comps_in_diff E X\<close> odd_comps_in_diff_not_in_X empty_iff insertCI)
    qed






    have "graph_invar ?G'"
    proof(safe)
      {
        fix e x y
        assume "{x, y} \<in> E" " x \<notin> X" "y \<in> X"  
        then show "\<exists>u v. {connected_component (graph_diff E X) x, {y}} = {u, v} \<and> u \<noteq> v"
          
          by (metis  in_own_connected_component singleton_iff)
      }
      have "finite (Vs E)" 
        by (simp add: less.prems(1))
      then  have "finite {X.  X \<subseteq> Vs E}"  
        by force

      have "finite {{X, Y}| X Y.  X \<subseteq> Vs E \<and> Y \<subseteq> Vs E}" using `finite (Vs E)`
subset_graph_finite[of "(Vs E)"] by auto
      then have "finite {{X, Y}| X Y.  X \<subseteq> Vs E \<and> Y \<subseteq> Vs E \<and> ( \<exists>x\<in>X.\<exists> y\<in>Y. {x, y} \<in> E)}" 
        by (smt (verit) Collect_mono rev_finite_subset)
      have "?G' \<subseteq> {{X, Y}| X Y.  X \<subseteq> Vs E \<and> Y \<subseteq> Vs E}"
      proof
        fix e
        assume "e \<in> ?G'"
        then obtain x y where  edge_in_G':"{x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e = {connected_component (graph_diff E X) x, {y}}"
          by auto
        have "connected_component (graph_diff E X) x \<subseteq> Vs E" 
          by (meson edge_in_G' diff_connected_component_subset edges_are_Vs)
        have "{y} \<subseteq> Vs E" 
          using edge_in_G' subsetD by blast
        then show "e \<in> {{X, Y}| X Y.  X \<subseteq> Vs E \<and> Y \<subseteq> Vs E}" 
          using \<open>connected_component (graph_diff E X) x \<subseteq> Vs E\<close> edge_in_G' by blast
      qed
      then have "finite ?G'" 
        using \<open>finite {{X, Y} |X Y. X \<subseteq> Vs E \<and> Y \<subseteq> Vs E}\<close> finite_subset by fastforce

      have "\<forall>C \<in> ?G'. finite C" 
        by blast
      then show "finite (Vs ?G')"
        by (simp add: union_of_set_finite Vs_def \<open>finite {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close>)
    qed
    have "(odd_comps_in_diff E X) \<subseteq> Vs ?G'" 
    proof
      fix C
      assume "C \<in> (odd_comps_in_diff E X)"
      then obtain x y where  " {x, y} \<in> E \<and> x \<in> C \<and> y \<in> X" 
        by (metis \<open>X \<subseteq> Vs E \<and> barrier E X\<close> odd_comps_in_diff_connected less.prems(1) less.prems(2))
      then have " {connected_component (graph_diff E X) x, {y}} \<in> ?G'" 
        using \<open>C \<in> odd_comps_in_diff E X\<close> odd_comps_in_diff_not_in_X 
        by (smt (verit) IntI empty_iff mem_Collect_eq) 
      have "C = connected_component (graph_diff E X) x" 
        by (metis \<open>C \<in> odd_comps_in_diff E X\<close> \<open>{x, y} \<in> E \<and> x \<in> C \<and> y \<in> X\<close> odd_comps_in_diff_is_component less.prems(1))
      then have "{C, {y}} \<in> ?G'" 
        using \<open>{connected_component (graph_diff E X) x, {y}} \<in> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> by blast
      then show "C \<in> Vs ?G'" 
        by (meson edges_are_Vs)
    qed
    have "\<forall> e \<in> ?G'. \<exists> u v.  e= {u, v}  \<and> (u \<in> (odd_comps_in_diff E X) \<and> v \<in> Vs ?G' - (odd_comps_in_diff E X))"
    proof
      fix e
      assume "e \<in> ?G'"
      then obtain x y where "{x, y} \<in> E \<and>  x \<notin> X \<and>  y \<in> X \<and> e = {connected_component (graph_diff E X) x, {y}}"
        by auto 
      then have "connected_component (graph_diff E X) x \<in> (odd_comps_in_diff E X)"
        by (smt (verit, ccfv_SIG) Union_eq Vs_def \<open>odd_comps_in_diff E X = {C. \<exists>x\<in>Vs E - X. C = connected_component (graph_diff E X) x}\<close> insert_Collect mem_Collect_eq set_diff_eq singleton_conv)
      have "{y} \<in> Vs ?G'" 
        using \<open>{x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e = {connected_component (graph_diff E X) x, {y}}\<close> by auto
      have "{y} \<notin> (odd_comps_in_diff E X)" 
        by (metis IntI \<open>{x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e = {connected_component (graph_diff E X) x, {y}}\<close> odd_comps_in_diff_not_in_X empty_iff singletonI)
      then have "{y} \<in> Vs ?G' - (odd_comps_in_diff E X)" 
        by (simp add: \<open>{y} \<in> Vs ?G'\<close>)
      then show "\<exists> u v.  e= {u, v}  \<and> (u \<in> (odd_comps_in_diff E X) \<and> v \<in> Vs ?G' - (odd_comps_in_diff E X))"
        
        using \<open>connected_component (graph_diff E X) x \<in> odd_comps_in_diff E X\<close> \<open>{x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e = {connected_component (graph_diff E X) x, {y}}\<close> by blast
    qed

    then have "partitioned_bipartite ?G' (odd_comps_in_diff E X)" unfolding partitioned_bipartite_def
      by (metis (no_types, lifting) \<open>odd_comps_in_diff E X \<subseteq> Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> \<open>graph_invar {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close>)

    have "((card  (odd_comps_in_diff E X)) = card (Vs ?G' - (odd_comps_in_diff E X)))"
    proof - 
      have "card  (odd_comps_in_diff E X) = card X" 
        by (simp add: \<open>card (odd_comps_in_diff E X) = card X\<close>)
     
    have "finite X" 
      using \<open>X \<subseteq> Vs E \<and> barrier E X\<close> less.prems(1) rev_finite_subset by auto
    have "\<forall>x \<in> X. finite (?f x)" 
      by blast
    have "\<forall> C1 \<in> X. \<forall> C2 \<in> X. C1 \<noteq> C2 \<longrightarrow> ?f C1 \<inter> ?f C2 = {}" by auto
    then have "card (\<Union>x\<in>X. ?f x) = sum (\<lambda> C. card (?f C)) X" 
    using union_card_is_sum[of X ?f] 
    using \<open>\<forall>x\<in>X. finite {{x}}\<close> \<open>finite X\<close> by presburger
  have "sum (\<lambda> C. card (?f C)) X =  sum (\<lambda> C. 1) X" 
    by simp
  have "sum (\<lambda> C. 1) X = card X" 
    by fastforce
  then have "card (\<Union>x\<in>X. ?f x) = card X" 
    using \<open>(\<Sum>C\<in>X. card {{C}}) = (\<Sum>C\<in>X. 1)\<close> \<open>card (\<Union>x\<in>X. {{x}}) = (\<Sum>C\<in>X. card {{C}})\<close> by presburger
     
  
  have " card (Vs ?G' - (odd_comps_in_diff E X)) = card X" 
    using \<open>Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} - odd_comps_in_diff E X = (\<Union>x\<in>X. {{x}})\<close> \<open>card (\<Union>x\<in>X. {{x}}) = card X\<close> by presburger

  then show ?thesis 
    using \<open>card (odd_comps_in_diff E X) = card X\<close> by presburger
qed
  
  
  
  
  
  
  
  
  
  have "\<exists>M. perfect_matching ?G' M"
    proof(rule ccontr)
      assume "\<nexists>M. perfect_matching ?G' M" 
      then have "\<not> (\<forall>A \<subseteq>  (odd_comps_in_diff E X). card (reachable ?G' A) \<ge> card A \<and>
                   ((card  (odd_comps_in_diff E X)) = card (Vs ?G' - (odd_comps_in_diff E X))))"
        using frobeneus_matching[of ?G' "(odd_comps_in_diff E X)" ] 
            `partitioned_bipartite ?G' (odd_comps_in_diff E X)` 
        by blast
      
      then have "\<exists> A\<subseteq>  (odd_comps_in_diff E X). card (reachable ?G' A) < card A \<or>
                   ((card  (odd_comps_in_diff E X)) \<noteq> card (Vs ?G' - (odd_comps_in_diff E X)))"
        using le_less_linear by blast

      then obtain A where  " A\<subseteq>  (odd_comps_in_diff E X) \<and> card (reachable ?G' A) < card A" 
        using \<open>card (odd_comps_in_diff E X) = card (Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} - odd_comps_in_diff E X)\<close> by blast
      
      have "(reachable ?G' (odd_comps_in_diff E X)) = Vs ?G' - (odd_comps_in_diff E X)"
        using reachble_bipartite[of ?G' "(odd_comps_in_diff E X)"]
          `partitioned_bipartite ?G' (odd_comps_in_diff E X)` 
        
        by fastforce
      have "(reachable ?G' A) \<subseteq> (reachable ?G' (odd_comps_in_diff E X))" using 
      reachable_subset[of A "(odd_comps_in_diff E X)"]  
        using \<open>A \<subseteq> odd_comps_in_diff E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> by blast
      then have "(reachable ?G' A) \<subseteq> Vs ?G' - (odd_comps_in_diff E X)" 
        
        by (simp add: \<open>reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} (odd_comps_in_diff E X) = Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} - odd_comps_in_diff E X\<close>)


      then have "(reachable ?G' A) \<subseteq> (\<Union>x\<in>X. ?f x)" 
        by (simp add: \<open>Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} - odd_comps_in_diff E X = (\<Union>x\<in>X. {{x}})\<close>)
     
      have "(\<Union>x\<in>X. ?f x) = {{x} |x. x \<in> X}" using  singleton_set_is_union_singletons[of X]
        by (meson \<open>X \<subseteq> Vs E \<and> barrier E X\<close> less.prems(1) rev_finite_subset)

      then have "(reachable ?G' A) \<subseteq> {{x} |x. x \<in> X}" 
        using \<open>reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A \<subseteq> (\<Union>x\<in>X. {{x}})\<close> by presburger

     
      let ?ReachA = "(\<lambda> A. {x. {x}\<in>(reachable ?G' A)})"
      have "finite A" 
        using \<open>A \<subseteq> odd_comps_in_diff E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> diff_components_finite finite_subset less.prems(1) by auto
      have "finite X" 
        using \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>finite (Vs E)\<close> rev_finite_subset by blast
       
      then have "card (?ReachA A) = card (reachable ?G' A)" 
        using 
     card_singleton_set_same[of X "(reachable ?G' A)"]
        using \<open>reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A \<subseteq> {{x} |x. x \<in> X}\<close> by presburger


      have "(?ReachA A) \<subseteq> X" using `(reachable ?G' A) \<subseteq> {{x} |x. x \<in> X}` by auto

      have "(?ReachA A) = {y'. \<exists>x'. {x', y'} \<in> E \<and> connected_component (graph_diff E X) x' \<in> A \<and> y' \<in> X}"
        unfolding reachable_def 
      proof(safe)
  
     {
     fix x u e xa y
     assume  " {y} \<in> A"
       "{xa, y} \<in> E"
       "xa \<notin> X"
      " y \<in> X"
      " \<nexists>x'. {x', x} \<in> E \<and> connected_component (graph_diff E X) x' \<in> A \<and> x \<in> X"
      " {x} = connected_component (graph_diff E X) xa"
     then show "x = y" 
       
       by (metis IntI \<open>A \<subseteq> odd_comps_in_diff E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> odd_comps_in_diff_not_in_X empty_iff insertCI subsetD)

     
     
   }
   fix x x'
   assume    " {x', x} \<in> E"
       "connected_component (graph_diff E X) x' \<in> A"
       "x \<in> X"
   then have " {connected_component (graph_diff E X) x', {x}} \<in> ?G'"
     using IntI \<open>A \<subseteq> odd_comps_in_diff E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> odd_comps_in_diff_not_in_X empty_iff in_own_connected_component mem_Collect_eq subsetD
     
     by (smt (verit, del_insts))
 
   then   have "x \<in> (?ReachA A)"  unfolding reachable_def 
     by (smt (verit, best) \<open>A \<subseteq> odd_comps_in_diff E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> \<open>connected_component (graph_diff E X) x' \<in> A\<close> \<open>x \<in> X\<close> odd_comps_in_diff_not_in_X disjoint_insert(2) insertCI insert_Diff mem_Collect_eq subset_iff)


   
   then  show " \<exists>u\<in>A. \<exists>e\<in>?G'. {x} \<noteq> u \<and> u \<in> e \<and> {x} \<in> e" unfolding reachable_def
     
     by blast
 qed (auto)


      have "A \<subseteq> odd_comps_in_diff E (?ReachA A)"
      proof
        fix C
        assume "C \<in> A" 
        then have "C \<in>  (odd_comps_in_diff E X)" 
          using \<open>A \<subseteq> odd_comps_in_diff E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> by blast
        have "C \<noteq> {}" 
          using \<open>C \<in> odd_comps_in_diff E X\<close> less.prems(1) odd_components_nonempty by auto
        then obtain u where "u \<in> C" 
          by blast
        then have "connected_component (graph_diff E X) u = C" 
          by (simp add: \<open>C \<in> odd_comps_in_diff E X\<close> odd_comps_in_diff_is_component less.prems(1))
       
            have "\<forall>y\<in>connected_component (graph_diff E (?ReachA A)) u. y \<notin> X"
            proof
              fix y
              assume "y\<in>connected_component (graph_diff E (?ReachA A)) u" 
              show "y\<notin>X"
              proof(cases "y=u")
                case True
                then show ?thesis 
                  using \<open>C \<in> odd_comps_in_diff E X\<close> \<open>u \<in> C\<close> odd_comps_in_diff_not_in_X by blast
next
case False

  then obtain p where  " walk_betw (graph_diff E (?ReachA A)) y p u"
    using `y\<in>connected_component (graph_diff E (?ReachA A)) u`
                unfolding connected_component_def 
                using mem_Collect_eq walk_symmetric by fastforce


              then  have "\<forall>x\<in>set p. x \<in> connected_component (graph_diff E (?ReachA A)) u" 
                
                by (metis (no_types, lifting) \<open>y \<in> connected_component (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) u\<close> connected_components_member_eq vertices_path_in_component)
              have "u \<notin> X" 
                using \<open>C \<in> odd_comps_in_diff E X\<close> \<open>u \<in> C\<close> odd_comps_in_diff_not_in_X by auto
              have " last p = u" 
                by (meson \<open>walk_betw (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) y p u\<close> walk_betw_def)

             then have "path (graph_diff E (?ReachA A)) p" using ` walk_betw (graph_diff E (?ReachA A)) y p u`
                by (meson walk_betw_def)
              then have "\<forall>x \<in> set p. x \<notin> X \<and> x \<in> connected_component (graph_diff E X) u" using `last p = u`
              proof(induct p)
case path0
then show ?case 
  by force
next
  case (path1 v)
then show ?case 
  using \<open>u \<notin> X\<close> in_own_connected_component by force
next
  case (path2 v v' vs)
  have "{v, v'} \<in> (graph_diff E (?ReachA A))" 
    using path2.hyps(1) by blast
  then have "{v, v'} \<inter> (?ReachA A) = {}" 
    by (metis (mono_tags, lifting) graph_diff_def mem_Collect_eq)
  then have "{v} \<notin> reachable ?G' A" 
    by blast
  then have "\<nexists>C. C\<in>A \<and> {C, {v}} \<in> ?G'" unfolding reachable_def  
    by (smt (verit, best) \<open>graph_invar {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> doubleton_eq_iff insertCI mem_Collect_eq)
  then have "{C, {v}} \<notin> ?G'" 
    using \<open>C \<in> A\<close> by presburger
   have "v' \<in> connected_component (graph_diff E X) u" 
    using path2.hyps(3) path2.prems by fastforce

  then have "{connected_component (graph_diff E X) v', {v}} \<notin> ?G'"
    
    by (metis (no_types, lifting) \<open>connected_component (graph_diff E X) u = C\<close> \<open>{C, {v}} \<notin> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> connected_components_member_eq)

    
  have "\<forall>x\<in>set (v' # vs). x \<notin> X" 
    by (metis last_ConsR list.simps(3) path2.hyps(3) path2.prems)
 
   have "v \<notin> X"
  proof
    assume "v \<in> X"
    have " {v', v} \<in> E \<and> v' \<notin> X"
    by (metis (no_types, lifting) \<open>\<forall>x\<in>set (v' # vs). x \<notin> X\<close> graph_diff_subset insert_commute list.set_intros(1) path2.hyps(1) subsetD)
  then have "{connected_component (graph_diff E X) v', {v}} \<in> ?G'" 
    
    using \<open>v \<in> X\<close> by blast
 
  then show False 
    using \<open>{connected_component (graph_diff E X) v', {v}} \<notin> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> by blast
qed
  have "{v, v'} \<inter> X = {}" 
    by (simp add: \<open>\<forall>x\<in>set (v' # vs). x \<notin> X\<close> \<open>v \<notin> X\<close>)
  then have "{v, v'} \<in> (graph_diff E X)" unfolding graph_diff_def  
    using graph_diff_subset path2.hyps(1) by auto
  then have "v \<in> connected_component (graph_diff E X) u" 
    
    by (metis \<open>v' \<in> connected_component (graph_diff E X) u\<close> connected_components_member_eq insert_commute vertices_edges_in_same_component)


  then show ?case 
    by (metis \<open>v \<notin> X\<close> last_ConsR list.simps(3) path2.hyps(3) path2.prems set_ConsD)
qed
  then show " y \<notin> X" 
    by (metis (no_types, lifting) \<open>walk_betw (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) y p u\<close> list.set_sel(1) walk_betw_def)
qed
qed



  then  have "connected_component (graph_diff E X) u = 
                    connected_component (graph_diff E (?ReachA A)) u"
    by (metis (no_types, lifting) \<open>{x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A} \<subseteq> X\<close> less.prems(1) new_component_is_old)


  then have " connected_component (graph_diff E (?ReachA A)) u = C" 
    using \<open>connected_component (graph_diff E X) u = C\<close> by presburger

    then have "C \<in> {C. \<exists> v\<in>Vs E-X. connected_component (graph_diff E X) v = C \<and> odd (card C)}"
      
      using \<open>C \<in> odd_comps_in_diff E X\<close> odd_comps_in_diff_are_components less.prems(1) 
      
      by (simp add: Tutte_theorem3.odd_comps_in_diff_are_components)
    then have "odd (card C)" by auto
   then have "C \<in> {C. \<exists> v\<in>Vs E-X. connected_component (graph_diff E (?ReachA A)) v = C \<and> odd (card C)}"
     using \<open>C \<in> odd_comps_in_diff E X\<close> \<open>\<forall>y\<in>connected_component (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) u. y \<notin> X\<close> \<open>connected_component (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) u = C\<close> \<open>u \<in> C\<close> component_in_E insert_Diff insert_subset mem_Collect_eq
     
     by (smt (z3) DiffI)

          then show "C \<in>  odd_comps_in_diff E (?ReachA A)" 
using odd_comps_in_diff_are_components[of E " (?ReachA A)"] 
  by (smt (z3) DiffI \<open>C \<in> odd_comps_in_diff E X\<close> \<open>\<forall>y\<in>connected_component (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) u. y \<notin> X\<close> \<open>connected_component (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) u = C\<close> \<open>u \<in> C\<close> \<open>{x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A} \<subseteq> X\<close> component_in_E less.prems(1) mem_Collect_eq subsetD)
qed


  then  have "card A \<le> card (odd_comps_in_diff E (?ReachA A))"
    
    by (simp add: card_mono diff_components_finite less.prems(1))

  have "card A > card (?ReachA A)" 
    using \<open>A \<subseteq> odd_comps_in_diff E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> \<open>card {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A} = card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A)\<close> by presburger

  then have "card (?ReachA A) < card (odd_comps_in_diff E (?ReachA A))"
    
    using \<open>card A \<le> card (odd_comps_in_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A})\<close> by linarith
  have "(?ReachA A) \<subseteq> Vs E" 
    using \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>{x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A} \<subseteq> X\<close> by blast
  then have "card (?ReachA A) \<ge> card (odd_comps_in_diff E (?ReachA A))"
  using assms(2)  unfolding tutte_condition_def 
    
    by (meson less.prems(2) tutte_condition_def)

 then show False 
   using \<open>card {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A} < card (odd_comps_in_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A})\<close> not_less by blast
qed



                                
          
    then obtain M' where "perfect_matching ?G' M'" by auto

    let ?Z2 = "{C. \<exists> x y. C = {c . \<exists> e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x}
         \<and>  y\<in> X  \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}"

    have "Vs ?Z2 \<inter> X = {}" 
    proof(safe)
      fix x
      assume "x \<in> Vs ?Z2" "x \<in> X"

      then obtain C x' y' where "(C = {c . \<exists> e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X 
        \<and> c \<in> connected_component (graph_diff E X) x'}
 \<and> {connected_component (graph_diff E X) x', {y'}} \<in> M') \<and> x \<in> C"         
        using vs_member[of x ?Z2]  
        by blast
      then have "x \<notin> X" 
        by blast
      then show "x \<in> {}" using \<open>x \<in> X\<close> by blast
    qed


    have "Vs ?Z2 \<subseteq> Vs E"
    proof
      fix z
      assume "z \<in> Vs ?Z2" 
      then obtain C where "C \<in> ?Z2 \<and> z \<in> C" 
        by (meson vs_member_elim)
      then obtain x y where "C = {c . \<exists> e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> 
                    c \<in> connected_component (graph_diff E X) x}
             \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'" by blast 
      then have "C \<subseteq> Vs E"
      proof(safe) qed(auto)
      then show "z\<in> Vs E" using `C \<in> ?Z2 \<and> z \<in> C` by auto
    qed


   
    then have "finite (Vs ?Z2)" 
      by (simp add: finite_subset less.prems(1))
    have "\<forall>a1 \<in>?Z2.\<forall>a2\<in>?Z2. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
    proof(safe)
      { fix a1 a2 x xa y ya xb e xc ea eb
      assume "{connected_component (graph_diff E X) x, {y}} \<in> M'"
       "{connected_component (graph_diff E X) xa, {ya}} \<in> M'"
       "{xb, y} \<in> E"
       "xb \<notin> X"
       "xb \<in> connected_component (graph_diff E X) x"
      " \<nexists>e. e \<in> E \<and> e = {xb, ya} \<and> xb \<notin> X \<and> xb \<in> connected_component (graph_diff E X) xa"
       "{xc, y} \<in> E"
       "{xc, ya} \<in> E"
       "xc \<notin> X"
       "xc \<in> connected_component (graph_diff E X) x"
       "xc \<notin> X"
       "xc \<in> connected_component (graph_diff E X) xa"
      then show "xc \<in> {}" 
        by (smt (verit, ccfv_SIG) \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> connected_components_member_eq doubleton_eq_iff insertCI matching_unique_match perfect_matching_def)
    }

fix x xa y ya xb e xc ea eb

  show " {connected_component (graph_diff E X) x, {y}} \<in> M' \<Longrightarrow>
       {connected_component (graph_diff E X) xa, {ya}} \<in> M' \<Longrightarrow>
       {xb, ya} \<in> E \<Longrightarrow>
       xb \<notin> X \<Longrightarrow>
       xb \<in> connected_component (graph_diff E X) xa \<Longrightarrow>
       \<nexists>e. e \<in> E \<and> e = {xb, y} \<and> xb \<notin> X \<and> xb \<in> connected_component (graph_diff E X) x \<Longrightarrow>
       {xc, y} \<in> E \<Longrightarrow>
       {xc, ya} \<in> E \<Longrightarrow>
       xc \<notin> X \<Longrightarrow>
       xc \<in> connected_component (graph_diff E X) x \<Longrightarrow>
       xc \<notin> X \<Longrightarrow> xc \<in> connected_component (graph_diff E X) xa \<Longrightarrow> xc \<in> {}"
    using \<open>\<And>ya y xc xb xa x. \<lbrakk>{connected_component (graph_diff E X) x, {y}} \<in> M'; {connected_component (graph_diff E X) xa, {ya}} \<in> M'; {xb, y} \<in> E; xb \<notin> X; xb \<in> connected_component (graph_diff E X) x; \<nexists>e. e \<in> E \<and> e = {xb, ya} \<and> xb \<notin> X \<and> xb \<in> connected_component (graph_diff E X) xa; {xc, y} \<in> E; {xc, ya} \<in> E; xc \<notin> X; xc \<in> connected_component (graph_diff E X) x; xc \<notin> X; xc \<in> connected_component (graph_diff E X) xa\<rbrakk> \<Longrightarrow> xc \<in> {}\<close> by presburger
qed

  have "\<forall>C \<in> ?Z2. finite C" 
  proof
    fix C
    assume "C \<in> ?Z2"
 then obtain x y where "C = {c . \<exists> e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> 
                    c \<in> connected_component (graph_diff E X) x}
             \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'" by blast 
      then have "C \<subseteq> Vs E"
      proof(safe) qed(auto)
      then show "finite C" 
        using \<open>finite (Vs E)\<close> finite_subset by auto
    qed

    have "finite ?Z2"
    proof(rule ccontr)
      assume "infinite ?Z2" 
      then have "infinite (\<Union>?Z2)" 
        using finite_UnionD by blast
      then have "infinite (Vs ?Z2)" 
        by (simp add: Vs_def)
      then show False 
        using \<open>finite (Vs ?Z2)\<close> by blast
    qed

    have "\<forall>a\<in>?Z2. a \<noteq> {}"
    proof
      fix a
      assume "a \<in> ?Z2"
      then obtain x y where  "{connected_component (graph_diff E X) x, {y}} \<in> M' \<and> y \<in> X \<and>
          a = {c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x}"
        by blast
      then have "{connected_component (graph_diff E X) x, {y}} \<in> ?G'" 
        by (metis (no_types, lifting) \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> perfect_matching_def subsetD)
      then obtain x' y' where "{x', y'} \<in> E \<and> x' \<notin> X \<and> y' \<in> X  \<and> 
                      {connected_component (graph_diff E X) x, {y}} = 
                      {connected_component (graph_diff E X) x', {y'}}" by auto
      
      have "y = y'" 
        by (metis (no_types, lifting) \<open>{connected_component (graph_diff E X) x, {y}} \<in> M' \<and> y \<in> X \<and> a = {c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x}\<close> \<open>{x', y'} \<in> E \<and> x' \<notin> X \<and> y' \<in> X \<and> {connected_component (graph_diff E X) x, {y}} = {connected_component (graph_diff E X) x', {y'}}\<close> doubleton_eq_iff empty_iff in_own_connected_component insert_iff)

  then have "x' \<in> a" 
    by (metis (no_types, lifting) \<open>{connected_component (graph_diff E X) x, {y}} \<in> M' \<and> y \<in> X \<and> a = {c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x}\<close> \<open>{x', y'} \<in> E \<and> x' \<notin> X \<and> y' \<in> X \<and> {connected_component (graph_diff E X) x, {y}} = {connected_component (graph_diff E X) x', {y'}}\<close> doubleton_eq_iff in_own_connected_component mem_Collect_eq)
  then show "a \<noteq> {}" by auto
qed
    


  have "\<forall>a\<in>?Z2. \<exists>b\<in> Vs ?Z2. b \<in> a"
  proof
    fix a
    assume "a \<in> ?Z2" 
    then have "a \<noteq> {}" using `\<forall>a\<in>?Z2. a \<noteq> {}` by auto

    then obtain x where "x \<in> a" by blast
    then have "x \<in> Vs ?Z2" using `a \<in> ?Z2` 
      by (meson vs_member_intro)
    then show "\<exists>b\<in> Vs ?Z2. b \<in> a" 
      using \<open>x \<in> a\<close> by blast
  qed
    then  have "\<exists>Z' \<subseteq> Vs ?Z2. \<forall>C \<in> ?Z2. \<exists>!z \<in> Z'. z \<in> C"
      using ex_subset_same_elem_card[of ?Z2] `finite ?Z2` `\<forall>a1 \<in>?Z2.\<forall>a2\<in>?Z2. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}`
        `finite (Vs ?Z2)`
      by presburger
    then obtain Z' where "Z' \<subseteq> Vs ?Z2 \<and> ( \<forall>C \<in> ?Z2. \<exists>!z \<in> Z'. z \<in> C)" by auto


    let ?M' = "{e. \<exists> x y. e = {x, y} \<and> e \<in> E \<and> {connected_component (graph_diff E X) x, {y}} \<in> M' \<and> x \<in> Z'}"

   


  have "\<forall>C \<in> (odd_comps_in_diff E X). \<forall>z \<in> C. Vs (graph_diff (component_edges E C) {z}) = C - {z}"
  proof
    fix C 
    assume "C \<in> (odd_comps_in_diff E X)" 
    show "\<forall>z \<in> C. Vs (graph_diff (component_edges E C) {z}) = C - {z}"
    proof 
    fix z
    assume "z \<in> C"
    have "odd_comps_in_diff (component_edges (graph_diff E X) C) {z} = {}"
        using max_barrier_add_vertex_empty_odd_components[of E X C z] 
        using X_max \<open>C \<in> odd_comps_in_diff E X\<close>  less.prems(1) less.prems(2) 
        using \<open>z \<in> C\<close> by fastforce

    show "Vs (graph_diff (component_edges E C) {z}) = C - {z}"
    proof
        show "Vs (graph_diff (component_edges E C) {z}) \<subseteq> C - {z}"
        proof
          fix x
          assume "x \<in> Vs (graph_diff (component_edges E C) {z})"
          then obtain e where "e \<in> (graph_diff (component_edges E C) {z}) \<and> x \<in> e"    
            by (meson vs_member_elim)
          then have "e \<in> (component_edges E C) \<and> e \<inter> {z} = {}" 
            by (simp add: graph_diff_def)
          then have "e \<subseteq> C" unfolding component_edges_def 
            by blast
          then show "x \<in> C - {z}" 
            using \<open>e \<in> graph_diff (component_edges E C) {z} \<and> x \<in> e\<close> 

            using \<open>e \<in> component_edges E C \<and> e \<inter> {z} = {}\<close> by blast
        qed
        show "C - {z} \<subseteq> Vs (graph_diff (component_edges E C) {z})"
        proof
          fix x
          assume "x \<in> C - {z}"
          have "singl_in_diff (component_edges (graph_diff E X) C) {z} = {}"

            using \<open>odd_comps_in_diff (component_edges (graph_diff E X) C) {z} = {}\<close> odd_comps_in_diff_def by auto
          then have "singl_in_diff (component_edges E C) {z} = {}"

            by (simp add: \<open>C \<in> odd_comps_in_diff E X\<close> component_edges_same_in_diff)

          then have "\<nexists> v.  v \<in> Vs (component_edges E C) \<and> 
              v \<notin> {z} \<and> v \<notin> Vs (graph_diff (component_edges E C) {z})"
            unfolding singl_in_diff_def  
            by blast
          show "x \<in> Vs (graph_diff (component_edges E C) {z})"
          proof(cases "C \<in> odd_components (graph_diff E X)" )
            case True
            have "Vs (component_edges E C) = C" 
              by (meson True \<open>X \<subseteq> Vs E \<and> barrier E X\<close> less.prems(1) vertices_of_edges_in_component_same)
            have "x \<in>  Vs (component_edges E C)" 
              using \<open>Vs (component_edges E C) = C\<close> \<open>x \<in> C - {z}\<close> by auto
            have "x \<in> Vs (component_edges E C) \<and> 
              x \<notin> {z}" 
              using \<open>x \<in> C - {z}\<close> \<open>x \<in> Vs (component_edges E C)\<close> by blast
            then show "x \<in> Vs (graph_diff (component_edges E C) {z})"

              using \<open>\<nexists>v. v \<in> Vs (component_edges E C) \<and> v \<notin> {z} \<and> v \<notin> Vs (graph_diff (component_edges E C) {z})\<close> by blast
          next
            case False
            then have "C \<in> singl_in_diff E X" 
              by (metis UnE \<open>C \<in> odd_comps_in_diff E X\<close> odd_comps_in_diff_def)
            then have "C = {z}" unfolding singl_in_diff_def 
              using \<open>z \<in> C\<close> by fastforce
            then show ?thesis 
              using \<open>x \<in> C - {z}\<close> by blast
          qed
        qed
      qed
    qed
  qed


    have "\<forall>C \<in> (odd_comps_in_diff E X). 
      \<exists>M. perfect_matching (graph_diff (component_edges E C) Z') M"
    proof
      fix C
      assume "C \<in> (odd_comps_in_diff E X)"
      have "\<exists>x y. x \<in> C \<and> y \<in> X \<and> {x, y} \<in> E" 
        using "less.prems"(2) "less.prems"(2) \<open>C \<in> odd_comps_in_diff E X\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> Tutte_theorem3.odd_comps_in_diff_connected 

        using less.prems(1)
        by metis 
      then obtain x y where "x \<in> C \<and> y \<in> X \<and> {x, y} \<in> E" by auto
      then have "connected_component (graph_diff E X) x = C" 
        by (meson "less.prems"(1) \<open>C \<in> odd_comps_in_diff E X\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> odd_comps_in_diff_is_component)
      then have "{C, {y}} \<in> ?G'" 
        using \<open>x \<in> C \<and> y \<in> X \<and> {x, y} \<in> E\<close> 
        using \<open>C \<in> odd_comps_in_diff E X\<close> odd_comps_in_diff_not_in_X[of C E X]  by fastforce
      then have "C \<in> Vs ?G'" 
        by auto
      then have "C \<in> Vs M'" 
        by (metis (no_types, lifting) \<open>perfect_matching ?G' M'\<close> perfect_matching_def)
      then have "\<exists>e. C \<in> e \<and> e \<in> M'" 
        by (meson vs_member_elim) 
      then obtain e where " C \<in> e \<and> e \<in> M'" by auto
      then have "\<exists>x y. {x, y} \<in> E \<and> y \<in> X \<and> e = {connected_component (graph_diff E X) x,{y}}"
        by (smt (verit, ccfv_threshold) \<open>perfect_matching ?G' M'\<close> mem_Collect_eq perfect_matching_def subsetD)
      then obtain x' y' where "{x', y'} \<in> E \<and> y' \<in> X \<and> e = {connected_component (graph_diff E X) x',{y'}}" by auto
      then have "connected_component (graph_diff E X) x' = C" 
        using \<open>C \<in> odd_comps_in_diff E X\<close> \<open>C \<in> e \<and> e \<in> M'\<close> odd_comps_in_diff_not_in_X[of C E X] by fastforce
      then have "x' \<in> C" 
        by (meson in_own_connected_component)
      let ?C' = "{c . \<exists> e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'}" 

      have "?C' \<subseteq> C"
        using \<open>connected_component (graph_diff E X) x' = C\<close> by force
      have "{connected_component (graph_diff E X) x', {y'}} \<in> M'" 
        using \<open>C \<in> e \<and> e \<in> M'\<close> \<open>{x', y'} \<in> E \<and> y' \<in> X \<and> e = {connected_component (graph_diff E X) x', {y'}}\<close> by blast
      then have "?C' = {c . \<exists> e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X
                     \<and> c \<in> connected_component (graph_diff E X) x'}
             \<and> {connected_component (graph_diff E X) x', {y'}} \<in> M'" 
        by force
      have "\<exists>x' y'.  ?C' = {c . \<exists> e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X
                     \<and> c \<in> connected_component (graph_diff E X) x'} \<and> y' \<in> X 
             \<and> {connected_component (graph_diff E X) x', {y'}} \<in> M'"
      proof
        show "\<exists>y'a. {c. \<exists>e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} =
          {c. \<exists>e. e \<in> E \<and> e = {c, y'a}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} \<and> y'a \<in> X  \<and>
          {connected_component (graph_diff E X) x', {y'a}} \<in> M'"
        proof
          show "{c. \<exists>e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} =
    {c. \<exists>e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} \<and> y' \<in> X  \<and> 
    {connected_component (graph_diff E X) x', {y'}} \<in> M'"
            
            using \<open>{connected_component (graph_diff E X) x', {y'}} \<in> M'\<close> \<open>{x', y'} \<in> E \<and> y' \<in> X \<and> e = {connected_component (graph_diff E X) x', {y'}}\<close> by blast
        qed
      qed
      then have "?C' \<in> ?Z2" 
        by blast
      have " ( \<forall>C \<in> ?Z2. \<exists>!z \<in> Z'. z \<in> C)" 
        using \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> by linarith

       
      then have " \<exists>!z \<in> Z'. z \<in> ?C'" 
        by (metis (no_types, lifting) \<open>{c. \<exists>e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} \<in> ?Z2\<close>)
      have "Z' \<subseteq> Vs ?Z2" 
    using \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> by linarith


      have "Vs ?Z2 \<inter> C = ?C'"
        using possible_connected_vertices_in_expanded_graph_intersection[of E X C x' y' M']
        
        using \<open>C \<in> odd_comps_in_diff E X\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> \<open>x' \<in> C\<close> \<open>{connected_component (graph_diff E X) x', {y'}} \<in> M'\<close> \<open>{x', y'} \<in> E \<and> y' \<in> X \<and> e = {connected_component (graph_diff E X) x', {y'}}\<close> less.prems(1) perfect_matching_def by auto


    
      then have "\<exists>!z \<in> Z'. z \<in> C"  
        by (smt (verit) Int_iff \<open>Z' \<subseteq> Vs ?Z2\<close> \<open>\<exists>!z. z \<in> Z' \<and> z \<in> {c. \<exists>e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'}\<close> subset_eq)

      then obtain z where "z \<in> Z' \<and> z \<in> C" by auto
      have "C - Z' = C - {z}"
      proof
        show " C - Z' \<subseteq> C - {z}" 
          by (simp add: \<open>z \<in> Z' \<and> z \<in> C\<close> subset_Diff_insert)
        show "C - {z} \<subseteq> C - Z'" 
          using \<open>\<exists>!z. z \<in> Z' \<and> z \<in> C\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> by blast
      qed
      have "(graph_diff (component_edges E C) Z') = (graph_diff (component_edges E C) {z})"
        unfolding graph_diff_def
      proof(safe)
        {
          fix x
          assume " x \<in> component_edges E C"
            " x \<inter> Z' = {}" "z \<in> x"
          show "z \<in> {}" 
            using \<open>x \<inter> Z' = {}\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> \<open>z \<in> x\<close> by auto
        }
        fix x xa
        assume "x \<in> component_edges E C""
       x \<inter> {z} = {}"" xa \<in> x "" xa \<in> Z'"
        then show "xa \<in> {}" 
          by (smt (verit, best) Int_insert_right_if1 \<open>\<exists>!z. z \<in> Z' \<and> z \<in> C\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> component_edges_def insertCI mem_Collect_eq subset_eq)
      qed
      let ?Cz = "(graph_diff (component_edges E C) {z})"

      have "odd_comps_in_diff (component_edges (graph_diff E X) C) {z} = {}"
        using max_barrier_add_vertex_empty_odd_components[of E X C z] 
        using X_max \<open>C \<in> odd_comps_in_diff E X\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> less.prems(1) less.prems(2) by fastforce



      then have "odd_comps_in_diff (component_edges E C) {z} = {}"
        using \<open>odd_comps_in_diff (component_edges (graph_diff E X) C) {z} = {}\<close> 

        by (simp add: \<open>C \<in> odd_comps_in_diff E X\<close> component_edges_same_in_diff) 
      have "Vs (graph_diff (component_edges E C) {z}) = C - {z}"
        using `\<forall>C \<in> (odd_comps_in_diff E X). \<forall>z \<in> C. Vs (graph_diff (component_edges E C) {z}) = C - {z}` 
        by (simp add: \<open>C \<in> odd_comps_in_diff E X\<close> \<open>z \<in> Z' \<and> z \<in> C\<close>)





      have "(component_edges E C) \<subseteq> E" 
        unfolding component_edges_def 
        by force
      then  have "graph_invar (component_edges E C)" using `graph_invar E`

        by (metis Vs_subset insert_absorb insert_subset rev_finite_subset)
      have "(graph_diff (component_edges E C) {z}) \<subseteq> E" 
        unfolding graph_diff_def
        unfolding component_edges_def

        by blast
      then   have "graph_invar (graph_diff (component_edges E C) {z})" 

        by (metis \<open>C \<in> odd_comps_in_diff E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> component_in_E finite_Diff less.prems(1) rev_finite_subset subset_iff)

      have "card (Vs (graph_diff (component_edges E C) {z})) < card (Vs E)" 
        by (metis (no_types, lifting) Diff_insert_absorb \<open>C \<in> odd_comps_in_diff E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> component_in_E insert_subset less.prems(1) mk_disjoint_insert psubsetI psubset_card_mono)

      have " tutte_condition ?Cz \<Longrightarrow>
  Ex (perfect_matching ?Cz)"  using "less.hyps"(1) 
        using \<open>card (Vs (graph_diff (component_edges E C) {z})) < card (Vs E)\<close> \<open>graph_invar (graph_diff (component_edges E C) {z})\<close> by presburger


      have "\<exists>M. (perfect_matching
       (graph_diff (component_edges E C) {z}) M)" 
      proof(cases "C \<in> odd_components (graph_diff E X)")
        case True
        then have "\<exists> c \<in> Vs (graph_diff E X).
              connected_component (graph_diff E X) c = C \<and> odd (card C)"
          unfolding odd_components_def odd_component_def
          by blast
        have " Vs (component_edges E C) = C" 
          by (meson True \<open>X \<subseteq> Vs E \<and> barrier E X\<close> less.prems(1) vertices_of_edges_in_component_same)

        show ?thesis 
        proof(rule ccontr)
          assume " \<nexists>M. perfect_matching
         (graph_diff (component_edges E C) {z}) M"
          then have "\<not> tutte_condition ?Cz" 
            using \<open>tutte_condition (graph_diff (component_edges E C) {z}) \<Longrightarrow> Ex (perfect_matching (graph_diff (component_edges E C) {z}))\<close> by blast
          then have "\<exists>Y\<subseteq> Vs ?Cz. card (odd_comps_in_diff ?Cz Y) > card Y"

            by (meson le_less_linear tutte_condition_def)
          then obtain Y where "Y\<subseteq> Vs ?Cz \<and> card (odd_comps_in_diff ?Cz Y) > card Y" by auto
          have "Vs ?Cz = C - {z}" 
            using \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> by auto
          have "odd (card C)" 
            using \<open>\<exists>c\<in>Vs (graph_diff E X). connected_component (graph_diff E X) c = C \<and> odd (card C)\<close> by blast

          have "even (card (C - {z}))" using `odd (card C)` 
            by (metis \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>graph_invar (graph_diff (component_edges E C) {z})\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> card_Diff_singleton even_diff_nat infinite_remove odd_add odd_one)

          then have "even (card (odd_comps_in_diff ?Cz Y) - card Y)"

            by (metis \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y)\<close> \<open>graph_invar (graph_diff (component_edges E C) {z})\<close> diff_odd_component_parity' even_diff_nat linorder_le_less_linear)
          then have "card (odd_comps_in_diff ?Cz Y) - card Y \<ge> 2" 
            by (metis (no_types, lifting) One_nat_def Suc_leI \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y)\<close> add_0_right add_Suc_right diff_diff_cancel diff_zero le_eq_less_or_eq nat_dvd_1_iff_1 nat_neq_iff one_add_one zero_order(2))
          then have "card (odd_comps_in_diff ?Cz Y) \<ge> card Y + 2" 
            by linarith

          have "odd_comps_in_diff E (X \<union> (Y\<union>{z})) = odd_comps_in_diff E X - {C} \<union> 
       odd_comps_in_diff (component_edges (graph_diff E X) C) (Y\<union>{z})" 
            by (smt (verit, ccfv_threshold) Diff_empty Un_insert_right \<open>C \<in> odd_comps_in_diff E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y)\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> add_subset_change_odd_components boolean_algebra_cancel.sup0 empty_not_insert insert_subset less.prems(1) less.prems(2) subset_Diff_insert)
          have "(odd_comps_in_diff E X - {C}) \<inter> 
                (odd_comps_in_diff (component_edges (graph_diff E X) C) (Y\<union>{z})) = {}"

            using new_components_intersection_old_is_empty[of E X C "(Y\<union>{z})"] 
            by (metis Diff_empty Un_subset_iff \<open>C \<in> odd_comps_in_diff E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y)\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> insert_Diff insert_Diff_single insert_is_Un less.prems(1) less.prems(2) subset_Diff_insert subset_Un_eq)

          then have "card (odd_comps_in_diff E (X \<union> (Y\<union>{z}))) = card (odd_comps_in_diff E X - {C})
+ card (odd_comps_in_diff (component_edges (graph_diff E X) C) (Y\<union>{z}))" 

            by (metis \<open>odd_comps_in_diff E (X \<union> (Y \<union> {z})) = odd_comps_in_diff E X - {C} \<union> odd_comps_in_diff (component_edges (graph_diff E X) C) (Y \<union> {z})\<close> card_Un_disjoint diff_components_finite finite_Un less.prems(1))
          have " card (odd_comps_in_diff E X - {C}) = card (odd_comps_in_diff E X) - 1" 
            by (simp add: \<open>C \<in> odd_comps_in_diff E X\<close> diff_components_finite less.prems(1))
          then have " card (odd_comps_in_diff E X - {C}) = card X - 1" 
            using \<open>card (odd_comps_in_diff E X) = card X\<close> by presburger



          have "odd_components (graph_diff (component_edges E C) (Y\<union>{z})) =
        odd_components (graph_diff ?Cz Y)" 
            using graph_diff_trans[of "(component_edges E C)" Y "{z}"]
            using `graph_invar (component_edges E C)` 
            by (metis graph_diff_trans sup_commute)

          have "\<forall>v.  v \<in> Vs (component_edges E C) \<and> v \<notin> Y \<union> {z} \<longleftrightarrow>
  v \<in> Vs (graph_diff (component_edges E C) {z}) \<and>  v \<notin> Y "
          proof
            fix v
            have " Vs (component_edges E C) = C" 
              by (simp add: \<open>Vs (component_edges E C) = C\<close>)
            have "Vs (graph_diff (component_edges E C) {z}) = C - {z}" 
              using \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> by blast
            show " (v \<in> Vs (component_edges E C) \<and> v \<notin> Y \<union> {z}) =
         (v \<in> Vs (graph_diff (component_edges E C) {z}) \<and> v \<notin> Y)" 
              by (simp add: \<open>Vs (component_edges E C) = C\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close>)
          qed
          have "graph_diff (component_edges E C) (Y \<union> {z}) = graph_diff (graph_diff (component_edges E C) {z}) Y"

            by (metis \<open>graph_invar (component_edges E C)\<close> graph_diff_trans sup_commute)
          have " Vs (graph_diff (component_edges E C) (Y \<union> {z})) =
  Vs (graph_diff (graph_diff (component_edges E C) {z}) Y)"
            using `graph_diff (component_edges E C) (Y \<union> {z}) = graph_diff (graph_diff (component_edges E C) {z}) Y`

            by presburger

          then have " singl_in_diff (component_edges E C) (Y \<union> {z}) =
  singl_in_diff (graph_diff (component_edges E C) {z}) Y"
            unfolding singl_in_diff_def 
            using \<open>\<forall>v. (v \<in> Vs (component_edges E C) \<and> v \<notin> Y \<union> {z}) = (v \<in> Vs (graph_diff (component_edges E C) {z}) \<and> v \<notin> Y)\<close> by fastforce


          have "odd_comps_in_diff (component_edges E C) (Y\<union>{z}) =
       odd_comps_in_diff ?Cz Y" unfolding odd_comps_in_diff_def 

            using \<open>odd_components (graph_diff (component_edges E C) (Y \<union> {z})) = odd_components (graph_diff (graph_diff (component_edges E C) {z}) Y)\<close> \<open>singl_in_diff (component_edges E C) (Y \<union> {z}) = singl_in_diff (graph_diff (component_edges E C) {z}) Y\<close> by presburger


          then have "card (odd_comps_in_diff E (X \<union> (Y\<union>{z}))) = card X - 1 + card (odd_comps_in_diff ?Cz Y)"

            using \<open>card (odd_comps_in_diff E (X \<union> (Y \<union> {z}))) = card (odd_comps_in_diff E X - {C}) + card (odd_comps_in_diff (component_edges (graph_diff E X) C) (Y \<union> {z}))\<close> \<open>card (odd_comps_in_diff E X - {C}) = card (odd_comps_in_diff E X) - 1\<close> \<open>card (odd_comps_in_diff E X) = card X\<close>

            by (simp add: \<open>card (odd_comps_in_diff E (X \<union> (Y \<union> {z}))) = card (odd_comps_in_diff E X - {C}) + card (odd_comps_in_diff (component_edges (graph_diff E X) C) (Y \<union> {z}))\<close> \<open>card (odd_comps_in_diff E X - {C}) = card (odd_comps_in_diff E X) - 1\<close> \<open>card (odd_comps_in_diff E X) = card X\<close> \<open>odd_comps_in_diff (component_edges E C) (Y \<union> {z}) = odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y\<close> \<open>C \<in> odd_comps_in_diff E X\<close> component_edges_same_in_diff)

          then have "card (odd_comps_in_diff E (X \<union> (Y\<union>{z}))) \<ge> card X - 1 + card Y + 2" 
            using \<open>card Y + 2 \<le> card (odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y)\<close> by linarith
          then have "card (odd_comps_in_diff E (X \<union> (Y\<union>{z}))) \<ge> card X + card Y + 1" 
            by linarith
          have "X \<inter> (Y\<union>{z}) = {}"
            by (smt (verit, del_insts) Diff_empty Int_Un_distrib Int_Un_eq(3) Int_Un_eq(4) Int_empty_right Int_insert_left_if1 Int_insert_right_if0 Un_Int_assoc_eq Un_subset_iff \<open>C \<in> odd_comps_in_diff E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y)\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> odd_comps_in_diff_not_in_X insert_not_empty mk_disjoint_insert subset_Diff_insert sup_commute)

          then have "card (X \<union> (Y\<union>{z})) = card X + card(Y\<union>{z})" 
            by (meson \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y)\<close> \<open>graph_invar (graph_diff (component_edges E C) {z})\<close> card_Un_disjoint finite.emptyI finite.insertI finite_Un finite_subset less.prems(1))
          have "(Y\<inter>{z}) = {}" 
            using \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y)\<close> by blast
          then have "card (X \<union> (Y\<union>{z})) = card X + card Y + 1" 
            by (metis \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y)\<close> \<open>card (X \<union> (Y \<union> {z})) = card X + card (Y \<union> {z})\<close> \<open>graph_invar (graph_diff (component_edges E C) {z})\<close> card_Un_disjoint finite.emptyI finite.insertI finite_subset group_cancel.add1 is_singletonI is_singleton_altdef)

          have "card (odd_comps_in_diff E (X \<union> (Y\<union>{z}))) \<le> card (X \<union> (Y\<union>{z}))" 
            using `tutte_condition E` 
            by (smt (verit, ccfv_threshold) Un_Int_assoc_eq \<open>C \<in> odd_comps_in_diff E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y)\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> component_in_E inf.absorb_iff2 insert_Diff insert_subset order_trans sup_bot_right tutte_condition_def)
          then have "card (odd_comps_in_diff E (X \<union> (Y\<union>{z}))) = card (X \<union> (Y\<union>{z}))" 
            using \<open>card (X \<union> (Y \<union> {z})) = card X + card Y + 1\<close> \<open>card X + card Y + 1 \<le> card (odd_comps_in_diff E (X \<union> (Y \<union> {z})))\<close> le_antisym by presburger
          then have "barrier E (X \<union> (Y\<union>{z}))" 
            by (simp add: barrier_def)
          have "X \<subseteq> X \<union> (Y\<union>{z})" 
            by auto
          have "X \<union> (Y\<union>{z}) \<subseteq> Vs E" 
            by (smt (verit, del_insts) Diff_empty Un_subset_iff \<open>C \<in> odd_comps_in_diff E X\<close> \<open>Vs (component_edges E C) = C\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (odd_comps_in_diff (graph_diff (component_edges E C) {z}) Y)\<close> \<open>graph_invar (component_edges E C)\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> component_in_E diff_is_union_elements insert_subset subset_Diff_insert sup_bot_right)

          then show False using X_max 
            by (metis (no_types, lifting) Int_absorb1 Un_empty \<open>X \<inter> (Y \<union> {z}) = {}\<close> \<open>X \<subseteq> X \<union> (Y \<union> {z})\<close> \<open>barrier E (X \<union> (Y \<union> {z}))\<close> insert_not_empty mem_Collect_eq subset_Un_eq sup_commute)
        qed


      next
        case False
        then have "C \<in> singl_in_diff E X" 
          by (metis UnE \<open>C \<in> odd_comps_in_diff E X\<close> odd_comps_in_diff_def)
        then have "\<exists> v. C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)"
          unfolding singl_in_diff_def 
          by blast
        then have "C = {z}" 
          using \<open>z \<in> Z' \<and> z \<in> C\<close> by fastforce
        then have "z \<notin>  Vs (graph_diff E X)"
          using \<open>\<exists>v. C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)\<close> by blast
        have "\<forall>e\<subseteq>C. e \<in> E \<longrightarrow> e \<in> graph_diff E X" 
          using \<open>C = {z}\<close> less.prems(1) by fastforce
        then have "(component_edges E C) = {}"
          using `z \<notin>  Vs (graph_diff E X)` 

          by (smt (verit, best) Collect_empty_eq \<open>C = {z}\<close>  component_edges_def insert_subset order_refl singletonD vs_member_intro)
        then have "(graph_diff (component_edges E C) {z}) = {}" 

          by (metis bot.extremum_uniqueI graph_diff_subset)
        then have "perfect_matching {} {}" 
          unfolding perfect_matching_def 
          by (metis Vs_def  empty_subsetI ex_in_conv finite.simps matching_def matching_def2)

        then show ?thesis 
          using \<open>graph_diff (component_edges E C) {z} = {}\<close> by auto
      qed

      then show " \<exists>M. perfect_matching
              (graph_diff (component_edges E C) Z') M"

        by (simp add: \<open>graph_diff (component_edges E C) Z' = graph_diff (component_edges E C) {z}\<close>)
    qed

    have "M' \<subseteq> ?G'" 
      by (metis (no_types, lifting) \<open>perfect_matching ?G' M'\<close> perfect_matching_def)

    have "Z' \<inter> X = {}" 
      using \<open>Vs ?Z2 \<inter> X = {}\<close> \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> by blast
  

      let ?M2 = "{e. \<exists> x y. e = {x, y} \<and> x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}"

      have "Vs M' = Vs ?G'" 
        by (metis (no_types, lifting) \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> perfect_matching_def)

      
    have "Vs ?M2 = Z' \<union> X"
    proof(safe)
      {
        fix x
        assume "x \<in> Vs ?M2" "x \<notin> X"
        then have "\<exists>e. x \<in> e \<and> ( \<exists> x y. e = {x, y} \<and> x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M')"
           
          by (smt (verit) mem_Collect_eq vs_member)
        then obtain e x' y' where
          " x \<in> e \<and> (e = {x', y'} \<and> x' \<in> Z' \<and> {connected_component (graph_diff E X) x', {y'}} \<in> M')"
          by auto
        then have "x' \<notin> X" 
          using \<open>Vs ?Z2 \<inter> X = {}\<close> \<open>Z' \<subseteq> Vs?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> empty_iff by auto

        have "{connected_component (graph_diff E X) x', {y'}} \<in> ?G'" 
          using \<open>M' \<subseteq> ?G'\<close> \<open>x \<in> e \<and> e = {x', y'} \<and> x' \<in> Z' \<and> {connected_component (graph_diff E X) x', {y'}} \<in> M'\<close> by blast

        then  have "y' \<in> X" 
          by (smt (verit, best) \<open>x' \<notin> X\<close> doubleton_eq_iff empty_iff in_own_connected_component insertE mem_Collect_eq)
        then show " x \<in> Z'" 
          using \<open>x \<in> e \<and> e = {x', y'} \<and> x' \<in> Z' \<and> {connected_component (graph_diff E X) x', {y'}} \<in> M'\<close> \<open>x \<notin> X\<close> by blast
      }

      {
        fix x
        assume " x \<in> Z'"
        then have "x \<in>  Vs ?Z2" 
          using \<open>Z' \<subseteq> Vs?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> by blast
        then obtain C x' y' where   "
               C = {c. \<exists>e. e \<in> E \<and> e = {c, y'} 
                        \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} \<and> 
                  {connected_component (graph_diff E X) x', {y'}} \<in> M' \<and> x \<in> C"
          by (smt (z3) mem_Collect_eq vs_member)
        then have "{connected_component (graph_diff E X) x, {y'}} \<in> M'" 
          using connected_components_member_eq by force
        then show "x \<in> Vs {{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}"
          
          using \<open>x \<in> Z'\<close> by auto
      
      }
      fix x
      assume "x \<in> X" 
      then have "{x} \<in> Vs ?G'" 
        using \<open>\<forall>x\<in>X. {x} \<in> Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> by fastforce
      then have "{x} \<in> Vs M'" 
        using \<open>Vs M' = Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> by blast

      then obtain e' z' x' where  "{x} \<in> e' \<and> e' \<in> M' \<and> {z', x'} \<in> E \<and> z' \<notin> X \<and> x' \<in> X \<and> e' =
                                    {connected_component (graph_diff E X) z', {x'}}"
        using \<open>M' \<subseteq> ?G'\<close>
        by (smt (verit, best)  mem_Collect_eq subset_eq vs_member_elim)
      then have "x = x'" 
        using \<open>x \<in> X\<close> in_own_connected_component by force
      have "\<exists>z \<in> connected_component (graph_diff E X) z'. z \<in> Z'" 
        by (metis (mono_tags, lifting) \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> \<open>{x} \<in> e' \<and> e' \<in> M' \<and> {z', x'} \<in> E \<and> z' \<notin> X \<and> x' \<in> X \<and> e' = {connected_component (graph_diff E X) z', {x'}}\<close> mem_Collect_eq)
      then obtain z where "z \<in> connected_component (graph_diff E X) z' \<and> z \<in> Z'" by auto
      then have "{connected_component (graph_diff E X) z, {x}} \<in> M'" 
        using \<open>x = x'\<close> \<open>{x} \<in> e' \<and> e' \<in> M' \<and> {z', x'} \<in> E \<and> z' \<notin> X \<and> x' \<in> X \<and> e' = {connected_component (graph_diff E X) z', {x'}}\<close> connected_components_member_eq by force

      


      then show " x \<in> Vs {{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}"
        
        by (smt (verit, ccfv_SIG) \<open>\<exists>z\<in>connected_component (graph_diff E X) z'. z \<in> Z'\<close> \<open>x = x'\<close> \<open>{x} \<in> e' \<and> e' \<in> M' \<and> {z', x'} \<in> E \<and> z' \<notin> X \<and> x' \<in> X \<and> e' = {connected_component (graph_diff E X) z', {x'}}\<close> connected_components_member_eq connected_components_notE_singletons edges_are_Vs insert_commute mem_Collect_eq)

    qed   



    have "?M2 \<subseteq> E" 
    proof
      fix e
      assume "e \<in> ?M2"
      then obtain z x where edge_in_M': "e = {z, x} \<and> z \<in> Z' \<and> {connected_component (graph_diff E X) z, {x}} \<in> M'" 
        by blast
      then have "z \<notin> X" 
        using \<open>Z' \<inter> X = {}\<close> by blast
      have "{connected_component (graph_diff E X) z, {x}} \<in> ?G'" 
        using \<open>M' \<subseteq> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> edge_in_M' by blast

      then have "x \<in> X" 
        by (smt (verit, ccfv_SIG) \<open>z \<notin> X\<close> doubleton_eq_iff in_own_connected_component mem_Collect_eq singletonD)
   let ?C' = "{c. \<exists>e. e \<in> E \<and>
                 e = {c, x} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z}" 
     have "?C' \<in> ?Z2" using edge_in_M' `x \<in> X` by blast
       
     then obtain  C where  "C \<in> ?Z2 \<and>  z \<in> C" 
       by (metis (no_types, lifting) \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> edge_in_M' subsetD vs_member_elim)
 
       obtain z' x' where "{connected_component (graph_diff E X) z', {x'}} \<in> M'
                \<and> C = {c. \<exists>e. e \<in> E \<and> e = {c, x'} \<and> c \<notin> X \<and>
         c \<in> connected_component (graph_diff E X) z'}"
        
         using \<open>C \<in>?Z2 \<and> z \<in> C\<close> by blast
       then have "z \<in> connected_component (graph_diff E X) z'" 
         using \<open>C \<in>?Z2 \<and> z \<in> C\<close> by blast
       then have "connected_component (graph_diff E X) z \<in>
         {connected_component (graph_diff E X) z, {x}} 
      \<inter> {connected_component (graph_diff E X) z', {x'}}"   
         by (metis Int_iff connected_components_member_eq insertCI)
       then have "{connected_component (graph_diff E X) z, {x}} =
         {connected_component (graph_diff E X) z', {x'}}" 
         by (meson IntD1 IntD2 \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> \<open>{connected_component (graph_diff E X) z', {x'}} \<in> M' \<and> C = {c. \<exists>e. e \<in> E \<and> e = {c, x'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z'}\<close> edge_in_M' matching_unique_match perfect_matching_def)
       then have "x = x'" 
         by (metis (no_types, lifting) \<open>z \<in> connected_component (graph_diff E X) z'\<close> connected_components_member_eq doubleton_eq_iff)

       then have "C = ?C'" 
         by (metis (no_types, lifting) Collect_cong \<open>z \<in> connected_component (graph_diff E X) z'\<close> \<open>{connected_component (graph_diff E X) z', {x'}} \<in> M' \<and> C = {c. \<exists>e. e \<in> E \<and> e = {c, x'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z'}\<close> connected_components_member_eq)



       then have "z \<in> ?C'" using \<open>C \<in>?Z2 \<and> z \<in> C\<close> by auto
   
       then show "e \<in> E" 
         using edge_in_M' by fastforce
     qed


     have "perfect_matching ?M2 ?M2" unfolding perfect_matching_def
     proof
       show "graph_invar ?M2" 
         by (metis (no_types, lifting) \<open>Vs {{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'} = Z' \<union> X\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> \<open>finite (Vs ?Z2)\<close> \<open>{{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'} \<subseteq> E\<close> finite_UnI finite_subset less.prems(1) subset_eq)
       have "matching ?M2" unfolding matching_def
       proof
         fix e1
         assume "e1 \<in> ?M2"
         then obtain z1 x1 where e1_in_M': "e1 = {z1, x1} \<and> z1 \<in> Z' \<and>
                                       {connected_component (graph_diff E X) z1, {x1}} \<in> M'"
           by blast
       then have "z1 \<notin> X" 
        using \<open>Z' \<inter> X = {}\<close> by blast
      have "{connected_component (graph_diff E X) z1, {x1}} \<in> ?G'" 
        using \<open>M' \<subseteq> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> e1_in_M' by blast

      then have "x1 \<in> X"          
        by (smt (verit, ccfv_SIG) \<open>z1 \<notin> X\<close> doubleton_eq_iff in_own_connected_component mem_Collect_eq singletonD)

         let ?C1 = "{c. \<exists>e. e \<in> E \<and> e = {c, x1} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z1}"
         have "?C1 \<in> ?Z2" using e1_in_M'`x1 \<in> X` by blast
      
         then obtain C1 where  "C1 \<in> ?Z2 \<and> z1 \<in> C1 "
           
           by (metis (no_types, lifting) \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> e1_in_M' subsetD vs_member_elim)
       
 obtain z1' x1' where "{connected_component (graph_diff E X) z1', {x1'}} \<in> M'
                \<and> C1 = {c. \<exists>e. e \<in> E \<and> e = {c, x1'} \<and> c \<notin> X \<and>
         c \<in> connected_component (graph_diff E X) z1'}"
        
         using \<open>C1 \<in>?Z2 \<and> z1 \<in> C1\<close> by blast
       then have "z1 \<in> connected_component (graph_diff E X) z1'" 
         using \<open>C1 \<in> ?Z2 \<and> z1 \<in> C1\<close> by blast
       then have "connected_component (graph_diff E X) z1 \<in>
         {connected_component (graph_diff E X) z1, {x1}} 
      \<inter> {connected_component (graph_diff E X) z1', {x1'}}"   
         by (metis Int_iff connected_components_member_eq insertCI)
       then have "{connected_component (graph_diff E X) z1, {x1}} =
         {connected_component (graph_diff E X) z1', {x1'}}" 
         by (meson IntD1 IntD2 \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> \<open>{connected_component (graph_diff E X) z1', {x1'}} \<in> M' \<and> C1 = {c. \<exists>e. e \<in> E \<and> e = {c, x1'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z1'}\<close> e1_in_M' matching_unique_match perfect_matching_def)
       then have "x1 = x1'" 
         by (metis (no_types, lifting) \<open>z1 \<in> connected_component (graph_diff E X) z1'\<close> connected_components_member_eq doubleton_eq_iff)

       then have "C1 = ?C1" 
         by (metis (no_types, lifting) Collect_cong \<open>z1 \<in> connected_component (graph_diff E X) z1'\<close> \<open>{connected_component (graph_diff E X) z1', {x1'}} \<in> M' \<and> C1 = {c. \<exists>e. e \<in> E \<and> e = {c, x1'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z1'}\<close> connected_components_member_eq)
       then have "z1 \<in> ?C1" 
         using \<open>C1 \<in> ?Z2 \<and> z1 \<in> C1\<close> by blast




         have "{connected_component (graph_diff E X) z1, {x1}} \<in> ?G'" 
           
           using \<open>M' \<subseteq> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> e1_in_M' by blast
         then have "z1 \<notin> X" 
           using \<open>Vs ?Z2 \<inter> X = {}\<close> \<open>Z' \<subseteq> Vs?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> e1_in_M' empty_iff subset_iff by auto
         then have "x1 \<in> X" 
           by (smt (z3) \<open>{connected_component (graph_diff E X) z1, {x1}} \<in> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> doubleton_eq_iff in_own_connected_component mem_Collect_eq singletonD)

         
         show "\<forall>e2 \<in> ?M2.  e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {}"
         proof
           fix e2
           assume "e2 \<in> ?M2"
           then obtain z2 x2 where e2_in_M': "e2 = {z2, x2} \<and> z2 \<in> Z' \<and> 
                                    {connected_component (graph_diff E X) z2, {x2}} \<in> M'" 
             by blast
  then have "z2 \<notin> X" 
        using \<open>Z' \<inter> X = {}\<close> by blast
      have "{connected_component (graph_diff E X) z2, {x2}} \<in> ?G'" 
        using \<open>M' \<subseteq> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> e2_in_M' by blast

      then have "x2 \<in> X"          
        by (smt (verit, ccfv_SIG) \<open>z2 \<notin> X\<close> doubleton_eq_iff in_own_connected_component mem_Collect_eq singletonD)

         let ?C2 = "{c. \<exists>e. e \<in> E \<and> e = {c, x2} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z2}"
         have "?C2 \<in> ?Z2" using e2_in_M'`x2 \<in> X` by blast
      
         then obtain C2 where  "C2 \<in> ?Z2 \<and> z2 \<in> C2 "
           
           by (metis (no_types, lifting) \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> e2_in_M' subsetD vs_member_elim)
       
 obtain z2' x2' where "{connected_component (graph_diff E X) z2', {x2'}} \<in> M'
                \<and> C2 = {c. \<exists>e. e \<in> E \<and> e = {c, x2'} \<and> c \<notin> X \<and>
         c \<in> connected_component (graph_diff E X) z2'}"
        
         using \<open>C2 \<in>?Z2 \<and> z2 \<in> C2\<close> by blast
       then have "z2 \<in> connected_component (graph_diff E X) z2'" 
         using \<open>C2 \<in> ?Z2 \<and> z2 \<in> C2\<close> by blast
       then have "connected_component (graph_diff E X) z2 \<in>
         {connected_component (graph_diff E X) z2, {x2}} 
      \<inter> {connected_component (graph_diff E X) z2', {x2'}}"   
         by (metis Int_iff connected_components_member_eq insertCI)
       then have "{connected_component (graph_diff E X) z2, {x2}} =
         {connected_component (graph_diff E X) z2', {x2'}}" 
         by (meson IntD1 IntD2 \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> \<open>{connected_component (graph_diff E X) z2', {x2'}} \<in> M' \<and> C2 = {c. \<exists>e. e \<in> E \<and> e = {c, x2'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z2'}\<close> e2_in_M' matching_unique_match perfect_matching_def)
       then have "x2 = x2'" 
         by (metis (no_types, lifting) \<open>z2 \<in> connected_component (graph_diff E X) z2'\<close> connected_components_member_eq doubleton_eq_iff)

       then have "C2 = ?C2" 
         by (metis (no_types, lifting) Collect_cong \<open>z2 \<in> connected_component (graph_diff E X) z2'\<close> \<open>{connected_component (graph_diff E X) z2', {x2'}} \<in> M' \<and> C2 = {c. \<exists>e. e \<in> E \<and> e = {c, x2'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z2'}\<close> connected_components_member_eq)
       then have "z2 \<in> ?C2" 
         using \<open>C2 \<in> ?Z2 \<and> z2 \<in> C2\<close> by blast







    have "{connected_component (graph_diff E X) z2, {x2}} \<in> ?G'" 
           
           using \<open>M' \<subseteq> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> e2_in_M' by blast
         then have "z2 \<notin> X" 
           using \<open>Vs ?Z2 \<inter> X = {}\<close> \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> e2_in_M' empty_iff subset_iff by auto
         then have "x2 \<in> X" 
           by (smt (z3) \<open>{connected_component (graph_diff E X) z2, {x2}} \<in> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> doubleton_eq_iff in_own_connected_component mem_Collect_eq singletonD)

           show " e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {}"
           proof
             assume " e1 \<noteq> e2"
             have "x1 \<noteq> z2" 
               using \<open>x1 \<in> X\<close> \<open>z2 \<notin> X\<close> by blast
             then have "connected_component (graph_diff E X) z2 \<noteq> {x1}" 
               using in_own_connected_component by force
             have "x2 \<noteq> z1" 
               using \<open>x2 \<in> X\<close> \<open>z1 \<notin> X\<close> by blast
             then have "connected_component (graph_diff E X) z1 \<noteq> {x2}" 
               using in_own_connected_component by force
             then have "x1 \<noteq> x2 \<or> z1 \<noteq> z2" 
               using e1_in_M' e2_in_M' `e1 \<noteq> e2` by fastforce
             have "matching M'" 
               using \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> perfect_matching_def by blast
             have "{connected_component (graph_diff E X) z1, {x1}} 
                                    \<noteq> {connected_component (graph_diff E X) z2, {x2}}"
             proof
               assume "{connected_component (graph_diff E X) z1, {x1}} =
    {connected_component (graph_diff E X) z2, {x2}}" 
               then have "x1 = x2" 
                 by (metis \<open>connected_component (graph_diff E X) z1 \<noteq> {x2}\<close> doubleton_eq_iff)
               have "connected_component (graph_diff E X) z1 = 
                          connected_component (graph_diff E X) z2" 
                 by (metis \<open>x1 = x2\<close> \<open>{connected_component (graph_diff E X) z1, {x1}} = {connected_component (graph_diff E X) z2, {x2}}\<close> doubleton_eq_iff)
              

               have "?C1 = ?C2" 
                 using \<open>connected_component (graph_diff E X) z1 = connected_component (graph_diff E X) z2\<close> \<open>x1 = x2\<close> by presburger

               then have "z1 = z2" 
                 by (metis (no_types, lifting) \<open>C1 = {c. \<exists>e. e \<in> E \<and> e = {c, x1} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z1}\<close> \<open>C1 \<in> ?Z2 \<and> z1 \<in> C1\<close> \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> \<open>z2 \<in> {c. \<exists>e. e \<in> E \<and> e = {c, x2} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z2}\<close> e1_in_M' e2_in_M')
               then show False 
                 using \<open>x1 = x2\<close> \<open>x1 \<noteq> x2 \<or> z1 \<noteq> z2\<close> by blast
             qed
             
             
             have " {connected_component (graph_diff E X) z1, {x1}}
                                    \<inter>  {connected_component (graph_diff E X) z2, {x2}} = {}"
               
               by (meson \<open>matching M'\<close> \<open>{connected_component (graph_diff E X) z1, {x1}} \<noteq> {connected_component (graph_diff E X) z2, {x2}}\<close> e1_in_M' e2_in_M' matching_def)
             then have "x1 \<noteq> x2" 
               by blast
             then have "z1 \<noteq> z2" 
               using \<open>connected_component (graph_diff E X) z1 \<in> {connected_component (graph_diff E X) z1, {x1}} \<inter> {connected_component (graph_diff E X) z1', {x1'}}\<close> \<open>{connected_component (graph_diff E X) z1, {x1}} \<inter> {connected_component (graph_diff E X) z2, {x2}} = {}\<close> by force

             then have "{z1, x1} \<inter> {z2, x2} = {}" 
               using \<open>x1 \<noteq> x2\<close> \<open>x1 \<noteq> z2\<close> \<open>x2 \<in> X\<close> \<open>z1 \<notin> X\<close> by fastforce
             then show " e1 \<inter> e2 = {}" 
               using e1_in_M' e2_in_M' by fastforce
           qed
         qed
       qed
       have "?M2 \<subseteq> ?M2" by auto
       have "Vs ?M2 = Vs ?M2" by auto
       then show "matching ?M2 \<and> ?M2 \<subseteq> ?M2 \<and> Vs ?M2 = Vs ?M2"
         using \<open>matching {{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}\<close> by blast
     qed
         
     let ?E' = "{(graph_diff (component_edges E C) Z')| C. C \<in> (odd_comps_in_diff E X)} \<union> {?M2}"
     have "\<forall>CE \<in> {(graph_diff (component_edges E C) Z')| C. C \<in> (odd_comps_in_diff E X)}.
            \<exists>M. perfect_matching CE M" 
       using \<open>\<forall>C\<in>odd_comps_in_diff E X. \<exists>M. perfect_matching (graph_diff (component_edges E C) Z') M\<close> by blast

     then have "\<forall>CE \<in> ?E'.  \<exists>M. perfect_matching CE M" 
       using \<open>perfect_matching {{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'} {{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}\<close> by blast


     let ?ce = "(\<lambda> C. {(graph_diff (component_edges E C) Z')})"
     let ?CES = " {(graph_diff (component_edges E C) Z')| C. C \<in> (odd_comps_in_diff E X)}"
     have "?CES  =  ( \<Union>C\<in>(odd_comps_in_diff E X). (?ce C))"
     proof(safe) qed(auto)
     have "finite  ( \<Union>C\<in>(odd_comps_in_diff E X). (?ce C))" 
       by (meson \<open>odd_comps_in_diff E X \<subseteq> Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> \<open>graph_invar {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> finite.emptyI finite_UN_I finite_insert finite_subset)

        
     then  have "finite ?CES" 
       
       using \<open>{graph_diff (component_edges E C) Z' |C. C \<in> odd_comps_in_diff E X} = (\<Union>C\<in>odd_comps_in_diff E X. {graph_diff (component_edges E C) Z'})\<close> by presburger
     then have "finite ?E'" 
       by blast


     have "\<forall>CE1 \<in> ?CES. \<forall>CE2 \<in> ?CES. CE1 \<noteq> CE2 \<longrightarrow> Vs CE1 \<inter> Vs CE2 = {}"
     proof(safe)
       {
       fix  C Ca e xa
       
      assume "C \<in> odd_comps_in_diff E X"
       "Ca \<in> odd_comps_in_diff E X"
      " e \<in> graph_diff (component_edges E C) Z'"
      " e \<notin> graph_diff (component_edges E Ca) Z'"
      " xa \<in> Vs (graph_diff (component_edges E C) Z')"
       "xa \<in> Vs (graph_diff (component_edges E Ca) Z')"
      have "graph_diff (component_edges E C) Z' \<subseteq> (component_edges E C)"
        by (simp add: graph_diff_subset)
  then have "e \<in> (component_edges E C)" 
    by (simp add: \<open>e \<in> graph_diff (component_edges E C) Z'\<close> subset_eq)
  have "e \<inter> Z' = {}"  
    by (metis (mono_tags, lifting) \<open>e \<in> graph_diff (component_edges E C) Z'\<close> graph_diff_def mem_Collect_eq)
  have "graph_diff (component_edges E Ca) Z' \<subseteq> (component_edges E Ca)"
    by (simp add: graph_diff_subset)
  then have "e \<notin>  (component_edges E Ca)" 
    using \<open>e \<inter> Z' = {}\<close> \<open>e \<notin> graph_diff (component_edges E Ca) Z'\<close> graph_diff_def by blast
  then have "(component_edges E Ca) \<noteq> (component_edges E C)" 
    using \<open>e \<in> component_edges E C\<close> by blast
  then have "Ca \<noteq> C" unfolding component_edges_def 
    by blast
  then have "Ca \<inter> C = {}" 
    by (meson \<open>C \<in> odd_comps_in_diff E X\<close> \<open>Ca \<in> odd_comps_in_diff E X\<close> diff_component_disjoint less.prems(1))
  have "Vs (graph_diff (component_edges E C) Z') \<subseteq> Vs (component_edges E C)" 
    by (simp add: Vs_subset \<open>graph_diff (component_edges E C) Z' \<subseteq> component_edges E C\<close>)
  have "Vs (graph_diff (component_edges E Ca) Z') \<subseteq> Vs (component_edges E Ca)" 
    by (simp add: Vs_subset \<open>graph_diff (component_edges E Ca) Z' \<subseteq> component_edges E Ca\<close>)
  then have "Vs (graph_diff (component_edges E Ca) Z') \<inter> 
Vs (graph_diff (component_edges E C) Z') = {}" 
    by (smt (verit, ccfv_threshold) \<open>C \<in> odd_comps_in_diff E X\<close> \<open>Ca \<in> odd_comps_in_diff E X\<close> \<open>Ca \<inter> C = {}\<close> \<open>Vs (graph_diff (component_edges E C) Z') \<subseteq> Vs (component_edges E C)\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> component_edges_same_in_diff disjoint_iff_not_equal less.prems(1) less.prems(2) new_components_in_old_one subsetD)

        
      then show  "xa \<in> {}" 
        using \<open>xa \<in> Vs (graph_diff (component_edges E C) Z')\<close> \<open>xa \<in> Vs (graph_diff (component_edges E Ca) Z')\<close> by blast
    }
    fix C Ca x xa
    show "
       C \<in> odd_comps_in_diff E X \<Longrightarrow>
       Ca \<in> odd_comps_in_diff E X \<Longrightarrow>
       x \<in> graph_diff (component_edges E Ca) Z' \<Longrightarrow>
       x \<notin> graph_diff (component_edges E C) Z' \<Longrightarrow>
       xa \<in> Vs (graph_diff (component_edges E C)
                  Z') \<Longrightarrow>
       xa \<in> Vs (graph_diff (component_edges E Ca)
                  Z') \<Longrightarrow>
       xa \<in> {}" 
      using \<open>\<And>xa e Ca C. \<lbrakk>C \<in> odd_comps_in_diff E X; Ca \<in> odd_comps_in_diff E X; e \<in> graph_diff (component_edges E C) Z'; e \<notin> graph_diff (component_edges E Ca) Z'; xa \<in> Vs (graph_diff (component_edges E C) Z'); xa \<in> Vs (graph_diff (component_edges E Ca) Z')\<rbrakk> \<Longrightarrow> xa \<in> {}\<close> by blast
  qed
  have "\<forall>CE \<in> ?CES.  CE \<noteq> ?M2 \<longrightarrow> Vs CE \<inter> Vs ?M2 = {}" 
  proof 
    fix CE
    assume "CE \<in> ?CES"
    then obtain C where CE_in_diff: "C \<in> odd_comps_in_diff E X \<and> CE = graph_diff
          (component_edges E C) Z'" by auto
    have "Vs CE \<inter> Z' = {}"
    proof(safe)
      fix x
      assume " x \<in> Vs CE" " x \<in> Z'"
      then obtain e where "e \<in> CE \<and> x \<in> e" 
        by (meson vs_member_elim)
      then have "e \<inter> Z' = {}" using CE_in_diff unfolding graph_diff_def by auto
      then show "x \<in> {}" 
        using \<open>e \<in> CE \<and> x \<in> e\<close> \<open>x \<in> Z'\<close> by blast
    qed
    have "Vs CE \<subseteq> Vs (component_edges E C)" 
      by (simp add: CE_in_diff Vs_subset graph_diff_subset)
    have "Vs (component_edges E C) \<subseteq> C" unfolding component_edges_def 
      by (smt (verit) mem_Collect_eq subset_eq vs_member)
    then have "Vs CE \<inter> X = {}" 
      by (metis CE_in_diff \<open>Vs CE \<subseteq> Vs (component_edges E C)\<close> odd_comps_in_diff_not_in_X disjoint_iff_not_equal subset_eq)

    then have "Vs CE \<inter> (X \<union> Z') = {}" 
      using \<open>Vs CE \<inter> Z' = {}\<close> by auto
then


    show "CE \<noteq> ?M2 \<longrightarrow> Vs CE \<inter> Vs ?M2 = {}" 
      by (simp add: Un_commute \<open>Vs {{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'} = Z' \<union> X\<close>)
  qed
  then have "\<forall>CE1 \<in> ?E'. \<forall>CE2 \<in> ?E'. CE1 \<noteq> CE2 \<longrightarrow> Vs CE1 \<inter> Vs CE2 = {}" 
    by (simp add: Int_commute \<open>\<forall>CE1\<in>{graph_diff (component_edges E C) Z' |C. C \<in> odd_comps_in_diff E X}. \<forall>CE2\<in>{graph_diff (component_edges E C) Z' |C. C \<in> odd_comps_in_diff E X}. CE1 \<noteq> CE2 \<longrightarrow> Vs CE1 \<inter> Vs CE2 = {}\<close>)

  then have "\<exists>M. perfect_matching (\<Union>?E') M" 
    using perfect_matching_union[of ?E'] 
    using \<open>\<forall>CE\<in>{graph_diff (component_edges E C) Z' |C. C \<in> odd_comps_in_diff E X} \<union> {{{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}}. \<exists>M. perfect_matching CE M\<close> \<open>finite ({graph_diff (component_edges E C) Z' |C. C \<in> odd_comps_in_diff E X} \<union> {{{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}})\<close> by blast
  then obtain M where "perfect_matching (\<Union>?E') M" by auto

  have "(\<Union>?E') \<subseteq> E" 
  proof(safe)
    {
    fix e Xa C
    assume "e \<in> graph_diff (component_edges E C) Z'"
     "C \<in> odd_comps_in_diff E X" 
    then have "e \<in> (component_edges E C)"
      using graph_diff_subset by blast
    then show "e \<in> E" 
      using Berge.component_edges_subset by blast
  }

  fix Xa xa y
  assume  "xa \<in> Z'"
       "{connected_component (graph_diff E X) xa, {y}} \<in> M'"
  then show     " {xa, y} \<in> E" 
    using \<open>{{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'} \<subseteq> E\<close> by blast
qed

     
  have "Vs (odd_comps_in_diff E X) = Vs E - X" 
  proof(safe)
    {  fix x
    assume "x \<in> Vs (odd_comps_in_diff E X)" 
    then obtain C where "C \<in> (odd_comps_in_diff E X) \<and> x \<in> C" 
      by (meson vs_member_elim)
    have "C \<subseteq> Vs E" 
      by (meson \<open>C \<in> odd_comps_in_diff E X \<and> x \<in> C\<close> component_in_E)

    then show "x \<in> Vs E" 
      using \<open>C \<in> odd_comps_in_diff E X \<and> x \<in> C\<close> by blast
  }
  {
    fix x
    assume "x \<in> Vs (odd_comps_in_diff E X)" "x \<in> X"
    then show False 
      by (metis odd_comps_in_diff_not_in_X disjoint_insert(2) insert_Diff vs_member_elim)
  }
  fix x
  assume "x \<in> Vs E" "x\<notin>X" 
  then have "x \<in> connected_component (graph_diff E X) x"
    by (simp add: in_own_connected_component)

  then show "x \<in> Vs (odd_comps_in_diff E X)" 
    using \<open>odd_comps_in_diff E X = {C. \<exists>x\<in>Vs E - X. C = connected_component (graph_diff E X) x}\<close> \<open>x \<in> Vs E\<close> \<open>x \<notin> X\<close> by auto
qed

  

 have "\<forall>C \<in> (odd_comps_in_diff E X). \<exists>!z \<in> Z'. z \<in> C"
    proof
      fix C
      assume "C \<in> (odd_comps_in_diff E X)" 
      then have "C \<in> Vs M'" 
        by (metis (no_types, lifting) \<open>odd_comps_in_diff E X \<subseteq> Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> perfect_matching_def subsetD)
      then obtain e where "C \<in> e \<and> e \<in> M'" 
        by (meson vs_member_elim)
      then have "e \<in> ?G'" 
        by (metis (no_types, lifting) \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> perfect_matching_def subsetD)

      obtain x where "connected_component (graph_diff E X) x = C" 
        using \<open>C \<in> odd_comps_in_diff E X\<close> \<open>odd_comps_in_diff E X = {C. \<exists>x\<in>Vs E - X. C = connected_component (graph_diff E X) x \<and> odd (card C)}\<close> by auto
      then obtain y where "{connected_component (graph_diff E X) x, {y}} \<in> M' \<and> y \<in> X" 
        using \<open>C \<in> odd_comps_in_diff E X\<close> \<open>C \<in> e \<and> e \<in> M'\<close> \<open>e \<in> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> odd_comps_in_diff_not_in_X[of C E X] by fastforce
      let ?C' = "{c . \<exists> e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x}" 
      have "?C' \<in> ?Z2" using `{connected_component (graph_diff E X) x, {y}} \<in> M' \<and> y \<in> X`
        by blast
        have "\<exists>!z \<in> Z'. z \<in> ?C'" 
          by (metis (no_types, lifting) \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> 
                \<open>{c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} \<in> ?Z2\<close>)
        then obtain z where "z \<in> Z' \<and> z \<in> ?C'" by auto
      have "?C' \<subseteq> C"
        using \<open>connected_component (graph_diff E X) x = C\<close> by blast
      have "\<forall>y \<in> Z' - {z}. y \<notin> C" 
      proof
        fix y'
        assume "y' \<in> Z' - {z}" 
        show "y' \<notin> C"
        proof
          assume "y' \<in> C"
          have "y' \<in> Vs ?Z2" 
          using \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>?Z2. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> \<open>y' \<in> Z' - {z}\<close> by blast
        then obtain Cy where "Cy \<in> ?Z2 \<and> y' \<in> Cy" 
  by (meson vs_member_elim)
       then have "y' \<notin> X" 
          using \<open>Z' \<inter> X = {}\<close> by auto
        
        then  obtain x' z' where "Cy = {c. \<exists>e. e \<in> E \<and> e = {c, x'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z'} 
              \<and> {connected_component (graph_diff E X) z', {x'}} \<in> M'" 
          using `Cy \<in> ?Z2 \<and> y' \<in> Cy` by blast
        then have "y' \<in> connected_component (graph_diff E X) z'" 
          using \<open>Cy \<in> ?Z2 \<and> y' \<in> Cy\<close> by fastforce
        then have "connected_component (graph_diff E X) z' = C" 
          by (metis \<open>\<And>thesis. (\<And>x. connected_component (graph_diff E X) x = C \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>y' \<in> C\<close> connected_components_member_eq)
        then have "y = x'" 
          by (smt (verit, del_insts) \<open>Cy = {c. \<exists>e. e \<in> E \<and> e = {c, x'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z'} \<and> {connected_component (graph_diff E X) z', {x'}} \<in> M'\<close> \<open>connected_component (graph_diff E X) x = C\<close> \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> \<open>{connected_component (graph_diff E X) x, {y}} \<in> M' \<and> y \<in> X\<close> doubleton_eq_iff insertCI matching_unique_match perfect_matching_def)
        then have "Cy = ?C'" 
          using \<open>Cy = {c. \<exists>e. e \<in> E \<and> e = {c, x'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z'} \<and> {connected_component (graph_diff E X) z', {x'}} \<in> M'\<close> \<open>connected_component (graph_diff E X) x = C\<close> \<open>connected_component (graph_diff E X) z' = C\<close> by presburger

        then show False 
          using \<open>Cy \<in> ?Z2 \<and> y' \<in> Cy\<close> \<open>\<exists>!z. z \<in> Z' \<and> z \<in> {c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x}\<close> \<open>y' \<in> Z' - {z}\<close> \<open>z \<in> Z' \<and> z \<in> {c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x}\<close> by blast
      qed
    qed
    then show "\<exists>!z. z \<in> Z' \<and> z \<in> C" 
      using \<open>connected_component (graph_diff E X) x = C\<close> \<open>z \<in> Z' \<and> z \<in> {c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x}\<close> by blast
  qed
        

  have "Vs (\<Union>?CES) = Vs (odd_comps_in_diff E X) - Z'" 
  proof(safe)
    {
      fix x
      assume "x \<in> Vs (\<Union>?CES)" 
      then obtain C where "C \<in> (odd_comps_in_diff E X) \<and> x \<in> Vs (graph_diff
               (component_edges E C) Z')" 
        by (smt (verit, best) Union_iff mem_Collect_eq vs_member_elim vs_member_intro)
      then have "Vs (graph_diff
               (component_edges E C) Z') \<subseteq> C" 
        by (smt (verit, ccfv_threshold) Vs_subset \<open>X \<subseteq> Vs E \<and> barrier E X\<close> component_edges_same_in_diff graph_diff_subset less.prems(1) less.prems(2) new_components_in_old_one order_trans)

      then show "x \<in>  Vs (odd_comps_in_diff E X)" 
        using \<open>C \<in> odd_comps_in_diff E X \<and> x \<in> Vs (graph_diff (component_edges E C) Z')\<close> by blast
    }
    {
      fix x
      assume "x \<in> Vs (\<Union>?CES)" "x \<in> Z'"
        then obtain C where "C \<in> (odd_comps_in_diff E X) \<and> x \<in> Vs (graph_diff
               (component_edges E C) Z')" 
          by (smt (verit, best) Union_iff mem_Collect_eq vs_member_elim vs_member_intro)
        have " Vs (graph_diff (component_edges E C) Z') \<inter> Z' = {}"
        proof(safe)
          fix z
          assume "z \<in>  Vs (graph_diff (component_edges E C) Z')" 
          then obtain e where "z \<in> e \<and> e \<inter> Z' = {}" unfolding graph_diff_def 
            
            using vs_member_elim by force
          assume "z \<in> Z'" 
          then show "z \<in> {}" 
            using \<open>z \<in> e \<and> e \<inter> Z' = {}\<close> by blast
        qed
        then show False 
          using \<open>C \<in> odd_comps_in_diff E X \<and> x \<in> Vs (graph_diff (component_edges E C) Z')\<close> \<open>x \<in> Z'\<close> by blast   
    }
    fix x
    assume "x  \<in> Vs (odd_comps_in_diff E X)" " x \<notin> Z'"
    then obtain C where "C \<in> (odd_comps_in_diff E X) \<and> x \<in> C"
      by (meson vs_member_elim)
    then have "\<exists>!z \<in> Z'. z \<in> C" 
      by (simp add: \<open>\<forall>C\<in>odd_comps_in_diff E X. \<exists>!z. z \<in> Z' \<and> z \<in> C\<close>)
    then obtain z where "z \<in> Z' \<and> z \<in> C" 
      by auto
    have "Vs (graph_diff (component_edges E C) {z}) =  C - {z}" 
      by (simp add: \<open>C \<in> odd_comps_in_diff E X \<and> x \<in> C\<close> \<open>\<forall>C\<in>odd_comps_in_diff E X. \<forall>z\<in>C. Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>z \<in> Z' \<and> z \<in> C\<close>)

      have "(graph_diff (component_edges E C) Z') = (graph_diff (component_edges E C) {z})"
        unfolding graph_diff_def
      proof(safe)
        {
          fix x
          assume " x \<in> component_edges E C"
            " x \<inter> Z' = {}" "z \<in> x"
          show "z \<in> {}" 
            using \<open>x \<inter> Z' = {}\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> \<open>z \<in> x\<close> by auto
        }
        fix x xa
        assume "x \<in> component_edges E C""
       x \<inter> {z} = {}"" xa \<in> x "" xa \<in> Z'"
        then show "xa \<in> {}" 
          by (smt (verit, best) Int_insert_right_if1 \<open>\<exists>!z. z \<in> Z' \<and> z \<in> C\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> component_edges_def insertCI mem_Collect_eq subset_eq)
      qed

      have "C - Z' = C - {z}"
      proof
        show " C - Z' \<subseteq> C - {z}" 
          by (simp add: \<open>z \<in> Z' \<and> z \<in> C\<close> subset_Diff_insert)
        show "C - {z} \<subseteq> C - Z'" 
          using \<open>\<exists>!z. z \<in> Z' \<and> z \<in> C\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> by blast
      qed

      have "Vs (graph_diff (component_edges E C) Z') =  C - Z'" 
        
        using \<open>C - Z' = C - {z}\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>graph_diff (component_edges E C) Z' = graph_diff (component_edges E C) {z}\<close> by presburger

      then have "x \<in> Vs (graph_diff (component_edges E C) Z')"
        
        by (simp add: \<open>C \<in> odd_comps_in_diff E X \<and> x \<in> C\<close> \<open>x \<notin> Z'\<close>)
    

    then show "x \<in> Vs (\<Union>?CES)" 
      by (smt (verit) Vs_def \<open>C \<in> odd_comps_in_diff E X \<and> x \<in> C\<close> mem_Collect_eq vs_member_elim vs_member_intro)
  qed
      
  then have " Vs (\<Union>?CES) = (Vs E - Z') - X" 
    using \<open>Vs (odd_comps_in_diff E X) = Vs E - X\<close> by auto 
  then have "Vs (\<Union>?CES) = Vs E - (Z' \<union> X)" by auto  
  then have "Vs (\<Union>?CES) = Vs E - (Vs ?M2)"
    using \<open>Vs {{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'} = Z' \<union> X\<close> by presburger
  then have "Vs (\<Union>?CES) \<union> Vs (?M2) = Vs E" 
        by (metis (no_types, lifting) Int_commute Un_Diff_Int Vs_subset \<open>{{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'} \<subseteq> E\<close> le_iff_inf)


  then  have "Vs (\<Union>?E') = Vs E" 
    by (smt (verit, ccfv_SIG) Sup_empty Sup_insert Sup_union_distrib Vs_def sup_bot_right)

  have "perfect_matching E M" unfolding perfect_matching_def
  proof
    show "graph_invar E" 
      using less.prems(1) by auto
    have "matching M" 
      using \<open>perfect_matching (\<Union> ({graph_diff (component_edges E C) Z' |C. C \<in> odd_comps_in_diff E X} \<union> {{{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}})) M\<close> perfect_matching_def by blast
    have "M \<subseteq> (\<Union>?E')" 
      by (metis (no_types, lifting) \<open>perfect_matching (\<Union> ({graph_diff (component_edges E C) Z' |C. C \<in> odd_comps_in_diff E X} \<union> {{{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}})) M\<close> perfect_matching_def)
    then have "M \<subseteq> E"  using \<open>(\<Union>?E') \<subseteq> E\<close> 
      by (meson order_trans)
    have "Vs M = Vs (\<Union>?E')" 
      by (metis (no_types, lifting) \<open>perfect_matching (\<Union> ({graph_diff (component_edges E C) Z' |C. C \<in> odd_comps_in_diff E X} \<union> {{{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}})) M\<close> perfect_matching_def)
    then have "Vs M = Vs E" using `Vs (\<Union>?E') = Vs E` by auto
    then show " matching M \<and> M \<subseteq> E \<and> Vs M = Vs E" using \<open>matching M\<close> \<open>M \<subseteq> E\<close> by auto
  qed
  then show " \<exists>M. perfect_matching E M" by auto
qed
qed

lemma tutte:
  assumes "graph_invar E"
  shows "tutte_condition E \<longleftrightarrow> (\<exists>M. perfect_matching E M)"
  using tutte1 tutte2 
  using assms by auto

end
