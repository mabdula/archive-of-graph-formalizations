theory Berge_formula
  imports Tutte_theorem3
begin

lemma matching_vertices_double_size:
  assumes "graph_invar M"
  assumes "matching M"
  shows "2 * (card M) = card (Vs M)"
proof -
  have "finite (Vs M)" using assms(1) 
    by simp
  have "card (Vs M) =  sum (\<lambda> e. card e) M"
    using \<open>finite (Vs M)\<close> \<open>matching M\<close> werew by fastforce
  also have "\<dots> =  sum (\<lambda> e. 2) M" 
    by (smt (verit, del_insts)  \<open>graph_invar M\<close> card_edge mem_Collect_eq subset_eq sum.cong)
  also have "\<dots> = card M * 2" by simp  
  ultimately show ?thesis 
    by presburger
qed

lemma left_uncoverred_matching:
  assumes "graph_invar E"
  assumes "graph_matching E M"
  assumes "X \<subseteq> Vs E"
  shows " 2 * (card M) + card (diff_odd_components E X) - card X \<le> card (Vs E)"
proof -
  have "finite (Vs M)" 
    by (meson Vs_subset assms(1) assms(2) finite_subset)
  have "matching M" 
    by (simp add: assms(2))
  have "M \<subseteq> E" 
    by (simp add: assms(2))
  let ?comp_out  = "\<lambda> C. {e. e \<in> M \<and> (\<exists> x y. e = {x,y} \<and> y \<in> C \<and> x \<in> X)}"
  let ?QX = "(diff_odd_components E X)"

  have 2: "\<forall> e\<in> E. card e = 2" 
    using \<open>graph_invar E\<close> card_edge by blast
  have "\<forall> C \<in> ?QX. (?comp_out C) \<subseteq> M"
    by blast

  have "\<forall> C \<in> ?QX. card (?comp_out C) * 2 = card ( Vs (?comp_out C))"
  proof
    fix C
    assume "C \<in> ?QX"
    have "card (Vs (?comp_out C)) =  sum (\<lambda> e. card e) (?comp_out C)"
      using \<open>finite (Vs M)\<close> \<open>matching M\<close> werew by fastforce
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
      using Int_commute diff_odd_components_not_in_X[of C E X]  \<open>C \<in> ?QX\<close> by force
    have "card ((Vs (?comp_out C)) \<inter> X) = sum (\<lambda> e. card (e \<inter> X)) (?comp_out C)"
      using werew2[of M "(?comp_out C)" X] `matching M` `finite (Vs M)` 
      by blast
    then show "card ((Vs (?comp_out C)) \<inter> X) =  card (?comp_out C)" using 5  
      by force   
  qed

  have "(\<Union>C \<in>?QX. ((Vs (?comp_out C)) \<inter> X)) \<subseteq> X" 
    by blast

  let ?f = "(\<lambda> C. ((Vs (?comp_out C)) \<inter> X))"
  have "\<forall>C \<in> ?QX. finite ((Vs (?comp_out C)) \<inter> X)" 
    by (meson assms(1) assms(3) finite_Int finite_subset)
  have "finite ?QX" 
    by (simp add: assms(1) diff_components_finite)
  have "\<forall> C1 \<in>?QX. \<forall> C2 \<in> ?QX.  C1 \<noteq> C2 \<longrightarrow> ((Vs (?comp_out C1))) \<inter> ((Vs (?comp_out C2))) = {}"
    by (smt (verit, del_insts) \<open>matching M\<close> diff_component_disjoint diff_odd_components_not_in_X 
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

    by (metis (no_types, lifting) \<open>(\<Union>C\<in>diff_odd_components E X. Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<inter> X) \<subseteq> X\<close> assms(1) assms(3) card_mono finite_subset)


  then have "sum (\<lambda> C. card (?comp_out C)) ?QX \<le> card X" 
    using \<open>\<forall>C\<in>diff_odd_components E X. card (Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<inter> X) = card {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}\<close> by auto


  then have "\<forall> C \<in> ?QX. finite (?comp_out C)" 
    by (metis (mono_tags, lifting) Vs_def \<open>\<forall>C\<in>diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<subseteq> M\<close> assms(1) assms(2) finite_UnionD finite_subset)

  let ?comp_out_empty = "{C. C \<in> ?QX \<and> ?comp_out C = {}}"
  let ?comp_out_non = "{C. C \<in> ?QX \<and> ?comp_out C \<noteq> {}}"
  have "card ?comp_out_empty \<ge> card ?QX - card X"
  proof(rule ccontr)
    assume "\<not> card ?comp_out_empty \<ge> card ?QX - card X"
    then have  "card ?comp_out_empty < card ?QX - card X" 
      using not_less by blast
    have " ?comp_out_non \<union> ?comp_out_empty = ?QX" 
      by blast
    have "?comp_out_non \<inter> ?comp_out_empty = {}" 
      by blast
    have "sum (\<lambda> C. card (?comp_out C)) ?comp_out_empty = 0" 
      by (smt (verit, del_insts) card.empty mem_Collect_eq sum.infinite sum_eq_0_iff)
    then have "sum (\<lambda> C. card (?comp_out C)) ?QX =
                 sum (\<lambda> C. card (?comp_out C)) (?comp_out_non \<union> ?comp_out_empty)" 
      using `?comp_out_non \<union> ?comp_out_empty = ?QX` by auto
    have "sum (\<lambda> C. card (?comp_out C)) (?comp_out_non \<union> ?comp_out_empty) = 
        sum (\<lambda> C. card (?comp_out C)) (?comp_out_non) + sum (\<lambda> C. card (?comp_out C)) (?comp_out_empty)"

      by (metis (no_types, lifting) \<open>finite (diff_odd_components E X)\<close> \<open>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<noteq> {}} \<inter> {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}} = {}\<close> \<open>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<noteq> {}} \<union> {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}} = diff_odd_components E X\<close> finite_Un sum.union_disjoint)
    then have "sum (\<lambda> C. card (?comp_out C)) ?comp_out_non = sum (\<lambda> C. card (?comp_out C)) ?QX"    
      using \<open>(\<Sum>C | C \<in> diff_odd_components E X \<and> {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}. card {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}) = 0\<close> \<open>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<noteq> {}} \<union> {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}} = diff_odd_components E X\<close> by auto

    then have "sum (\<lambda> C. card (?comp_out C)) ?comp_out_non \<le> card X" 
      using \<open>(\<Sum>C\<in>diff_odd_components E X. card {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}) \<le> card X\<close> by presburger

    then have "\<forall> C \<in> ?comp_out_non. card(?comp_out C) \<ge> 1"
      by (simp add: \<open>\<forall>C\<in>diff_odd_components E X. finite (?comp_out C)\<close> card_gt_0_iff Suc_leI)  
    then have "sum (\<lambda> C. card (?comp_out C)) ?comp_out_non \<ge> card ?comp_out_non"
      using sum_mono 
      by (metis (no_types, lifting) card_eq_sum)
    then have "card X \<ge> card ?comp_out_non" 
      using \<open>(\<Sum>C | C \<in> diff_odd_components E X \<and> {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<noteq> {}. card {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}) \<le> card X\<close> order_trans by blast
    have "card ?QX = card ?comp_out_empty + card ?comp_out_non"
      by (metis (no_types, lifting) \<open>finite (diff_odd_components E X)\<close> \<open>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<noteq> {}} \<inter> {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}} = {}\<close> \<open>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<noteq> {}} \<union> {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}} = diff_odd_components E X\<close> add.commute card_Un_disjoint finite_Un)

    have "card ?comp_out_empty < card ?comp_out_empty + card ?comp_out_non - card X"
      using \<open>card (diff_odd_components E X) = card {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}} + card {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<noteq> {}}\<close> \<open>card {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}} < card (diff_odd_components E X) - card X\<close> by presburger

    then have "card ?comp_out_non > card X" 
      by (meson less_diff_conv nat_add_left_cancel_less)
    then show False 
      using \<open>card {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<noteq> {}} \<le> card X\<close> not_less by blast
  qed

  have "\<forall>C \<in> ?comp_out_empty. \<exists>v \<in> C. v \<notin> Vs M"
  proof
    fix C
    assume "C \<in> ?comp_out_empty" 
    have "C \<in> ?QX" 
      using \<open>C \<in> {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}\<close> by force
    have "?comp_out C = {}" using `C \<in> ?comp_out_empty`  
      by fastforce
    have e_in_C:"\<forall> e \<in> M. e \<inter> C = {} \<or> e \<inter> C = e"
    proof(safe)
      fix e x y
      assume assms_edge: "e \<in> M" " x \<in> e" "x \<notin> C" "y \<in> e" "y \<in> C" 
      then have "e \<inter> X = {}" 
        using Diff_disjoint \<open>C \<in> ?QX\<close> \<open>M \<subseteq> E\<close> \<open>graph_invar E\<close> \<open>?comp_out C = {}\<close> 
          diff_odd_components_not_in_X 
        by (smt (verit, ccfv_threshold) disjoint_iff_not_equal insert_commute insert_iff mem_Collect_eq singletonD subset_eq)

      then have "e \<in> (graph_diff E X)" 
        using \<open>M \<subseteq> E\<close> \<open>e \<in> M\<close> by blast
      then have "x \<in> C" 
        by (smt (verit, ccfv_SIG) \<open>C \<in> ?QX\<close> \<open>M \<subseteq> E\<close> \<open>graph_invar E\<close> assms_edge
            diff_odd_components_is_component empty_iff in_con_comp_insert 
            insert_Diff insert_commute insert_iff subsetD)
      then show "y \<in> {}"  using \<open>x \<notin> C\<close> by auto
    qed
    show "\<exists>v \<in> C. v \<notin> Vs M" 
    proof(rule ccontr)
      assume "\<not> (\<exists>v\<in>C. v \<notin> Vs M)" 
      then have "\<forall>v \<in> C. v \<in> Vs M" by blast
      then have " ((Vs M) \<inter> C) = C" by auto
      have "card ((Vs M) \<inter> C) = sum (\<lambda> e. card (e \<inter> C)) M"
        using werew2[of M M C]  `matching M`  \<open>finite (Vs M)\<close> by blast
      then have "even (card C)" 
        using \<open>Vs M \<inter> C = C\<close>
        by (smt (verit) "2" \<open>M \<subseteq> E\<close> e_in_C dvd_sum even_numeral odd_card_imp_not_empty subset_eq)
      then show False 
        using diff_odd_compoenent_has_odd_card[of C E X] \<open>C \<in> ?QX\<close> by auto
    qed
  qed
  let ?not_in_M = "\<lambda> C. {v. v \<in> C \<and> v \<notin> Vs M}"
  have "\<forall>C \<in> ?comp_out_empty. ?not_in_M C \<noteq> {}" 
    using \<open>\<forall>C\<in>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}. \<exists>v\<in>C. v \<notin> Vs M\<close> by auto

  have "\<forall>C \<in> ?comp_out_empty.  (?not_in_M C) \<subseteq> C"
    by blast
  then  have "\<forall>C \<in> ?comp_out_empty. finite (?not_in_M C)" 
    by (metis (no_types, lifting) assms(1) finite_subset mem_Collect_eq odd_components_subset_vertices)

  then have "\<forall>C \<in> ?comp_out_empty. card (?not_in_M C) \<ge> 1" 
    by (metis (no_types, lifting) One_nat_def Suc_leI \<open>\<forall>C\<in>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}. {v \<in> C. v \<notin> Vs M} \<noteq> {}\<close> card_gt_0_iff)
  then have "sum (\<lambda> C. card (?not_in_M C)) ?comp_out_empty \<ge> card ?comp_out_empty"
    by (metis (no_types, lifting) card_eq_sum sum_mono)

  have "finite ?comp_out_empty" 
    using \<open>finite (diff_odd_components E X)\<close> by auto
  have "\<forall>C \<in> ?comp_out_empty. finite (?not_in_M C)" 
    using \<open>\<forall>C\<in>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}. finite {v \<in> C. v \<notin> Vs M}\<close> by blast
  have "\<forall> C1 \<in> ?comp_out_empty. \<forall> C2 \<in> ?comp_out_empty. C1 \<noteq> C2 \<longrightarrow> ?not_in_M C1 \<inter> ?not_in_M C2 = {}"

    by (metis (no_types, lifting) diff_component_disjoint disjoint_iff_not_equal mem_Collect_eq)

  then have "sum (\<lambda> C. card (?not_in_M C)) ?comp_out_empty = 
      card  (\<Union>C \<in> ?comp_out_empty. (?not_in_M C))"
    using union_card_is_sum[of ?comp_out_empty ?not_in_M] 
    using \<open>\<forall>C\<in>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}. finite {v \<in> C. v \<notin> Vs M}\<close> \<open>finite {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}\<close> by blast

  have "(\<Union>C \<in> ?comp_out_empty. (?not_in_M C)) = (?not_in_M (\<Union>C \<in> ?comp_out_empty. C))"
    apply safe
     apply blast
    by blast


  have "(\<Union>C \<in> ?comp_out_empty. C) \<subseteq> Vs E" 
    by (metis (mono_tags, lifting) SUP_least mem_Collect_eq odd_components_subset_vertices)
  have "(?not_in_M (\<Union>C \<in> ?comp_out_empty. C)) \<subseteq> ?not_in_M (Vs E)" 
    using \<open>(\<Union>C\<in>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}. C) \<subseteq> Vs E\<close> by auto

  have "?not_in_M (Vs E)\<subseteq> Vs E" by blast
  then have "finite (?not_in_M (Vs E))" 
    by (meson assms(1) finite_subset)
  then have "card (?not_in_M (\<Union>C \<in> ?comp_out_empty. C)) \<le> card (?not_in_M (Vs E))"
    using \<open>{v \<in> \<Union>C\<in>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}. C. v \<notin> Vs M} \<subseteq> {v \<in> Vs E. v \<notin> Vs M}\<close> card_mono by blast
  have "card (?not_in_M (Vs E)) = card (Vs E - Vs M)" 
    by (metis  set_diff_eq) 
  have "card (Vs E - Vs M) = card (Vs E) - card (Vs M)" 
    by (meson Vs_subset \<open>M \<subseteq> E\<close> \<open>finite (Vs M)\<close> card_Diff_subset)

  then have "card ?comp_out_empty + card (Vs M) \<le> card (Vs E)" 
    by (metis (no_types, lifting) Nat.le_diff_conv2 Vs_subset \<open>(\<Sum>C | C \<in> diff_odd_components E X \<and> {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}. card {v \<in> C. v \<notin> Vs M}) = card (\<Union>C\<in>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}. {v \<in> C. v \<notin> Vs M})\<close> \<open>(\<Union>C\<in>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}. {v \<in> C. v \<notin> Vs M}) = {v \<in> \<Union>C\<in>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}. C. v \<notin> Vs M}\<close> \<open>M \<subseteq> E\<close> \<open>card {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}} \<le> (\<Sum>C | C \<in> diff_odd_components E X \<and> {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}. card {v \<in> C. v \<notin> Vs M})\<close> \<open>card {v \<in> Vs E. v \<notin> Vs M} = card (Vs E - Vs M)\<close> \<open>card {v \<in> \<Union>C\<in>{C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}. C. v \<notin> Vs M} \<le> card {v \<in> Vs E. v \<notin> Vs M}\<close> assms(1) card_mono le_trans)
  then have "card (Vs M) + card ?QX - card X \<le> card (Vs E)" 
    using \<open>card (diff_odd_components E X) - card X \<le> card {C \<in> diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}}\<close> by linarith
  then show " 2 * (card M) + card (diff_odd_components E X) - card X \<le> card (Vs E)" 
    by (metis \<open>finite (Vs M)\<close> assms(1) assms(2) matching_vertices_double_size subset_iff)
qed

lemma vertices_sum_in_components:
  shows "(\<Union>C \<in> (diff_odd_components E X). C) \<subseteq> (Vs E - X)"
  apply safe
   apply (meson in_mono odd_components_subset_vertices)
  using diff_odd_components_not_in_X by blast


lemma diff_odd_comps_card:
  assumes "graph_invar E"
  shows "card (diff_odd_components E X) \<le> card (Vs E - X)"
proof -
  have "\<forall>C \<in> (diff_odd_components E X). \<exists>c \<in> (Vs E - X). connected_component (graph_diff E X) c = C" 
    by (meson diff_odd_components_are_components_elim)

  have "(\<Union>C \<in> (diff_odd_components E X). C) \<subseteq> (Vs E - X)" 
    by (metis vertices_sum_in_components)
  then have "card (\<Union>C \<in> (diff_odd_components E X). C) \<le> card (Vs E - X)" 
    by (simp add: assms card_mono)
  
  have "card (\<Union>C \<in> (diff_odd_components E X). C) = (\<Sum>C \<in> (diff_odd_components E X). card C)" 
    by (smt (verit, ccfv_SIG) assms card_eq_0_iff diff_component_disjoint diff_components_finite diff_odd_compoenent_has_odd_card odd_card_imp_not_empty sum.cong union_card_is_sum)

  have "\<forall>C \<in> (diff_odd_components E X). card C \<ge> 1" 
    using odd_components_nonempty 
    by (metis One_nat_def Suc_leI card_eq_0_iff card_gt_0_iff diff_odd_compoenent_has_odd_card odd_card_imp_not_empty)
  then have "(\<Sum>C \<in> (diff_odd_components E X). card C) \<ge> card (diff_odd_components E X)"
    by (metis card_eq_sum sum_mono)

  then show "card (diff_odd_components E X) \<le> card (Vs E - X)" 
    using \<open>card (\<Union>C\<in>diff_odd_components E X. C) = sum card (diff_odd_components E X)\<close> \<open>card (\<Union>C\<in>diff_odd_components E X. C) \<le> card (Vs E - X)\<close> by linarith
qed


lemma construct_perfect_matching_with_new_vertices:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  assumes "\<forall>Y \<subseteq> Vs E. card (diff_odd_components E X) - card X \<ge> 
          card (diff_odd_components E Y) - card Y"
  assumes "finite A" 
  assumes "card A = card (diff_odd_components E X) - card X"
  assumes "A \<inter> Vs E = {}" 
shows "\<exists>M. perfect_matching (E \<union> {{x, y}| x y. x \<in> Vs E \<and> y \<in> A}) M"  
proof(cases "E={}")
  case True
  have "Vs E = {}" using True 
    by (simp add: Vs_def)
  then  have "{{x, y}| x y. x \<in> Vs E \<and> y \<in> A} = {}" 
    by blast
  then have "(E \<union> {{x, y}| x y. x \<in> Vs E \<and> y \<in> A}) = {}" using True by auto
  then show ?thesis 
    by (metis (no_types, lifting) True \<open>Vs E = {}\<close> assms(1) empty_iff matching_def2 perfect_matching_def sup_ge1)
next
  case False
  then have "E \<noteq> {}" by auto
  let ?H = "(E \<union> {{x, y}| x y. x \<in> Vs E \<and> y \<in> A})" 
  let ?k = "card (diff_odd_components E X) - card X" 

  show "\<exists>M. perfect_matching (E \<union> {{x, y}| x y. x \<in> Vs E \<and> y \<in> A}) M"
  proof(cases "card (diff_odd_components E X) - card X \<le> 0")
    case True
    then have "\<forall>Y \<subseteq> Vs E. card (diff_odd_components E Y) - card Y \<le> 0" 
      by (metis assms(3) bot_nat_0.extremum_uniqueI) 
    then have "\<forall>Y \<subseteq> Vs E. card (diff_odd_components E Y) \<le> card Y" by auto
    then have "tutte_condition E" by auto
    have "card A = 0" 
    using True assms(5) by force
  then have "A = {}" 
    using assms(4) card_0_eq by blast
  then have "(E \<union> {{x, y}| x y. x \<in> Vs E \<and> y \<in> A}) = E" by blast
  then show ?thesis using tutte 
    using \<open>tutte_condition E\<close> assms(1) by fastforce
next
  case False
  assume " \<not> card (diff_odd_components E X) - card X \<le> 0"
  then have "card (diff_odd_components E X) - card X > 0" 
    by (meson not_le)
  then have "card (diff_odd_components E X) \<ge> card X" 
    by simp
  have "Vs ?H = Vs E \<union> A"
  proof(safe)
    {
      fix x
      assume "x \<in> Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})"
      then have "x \<in> Vs E \<or> x \<in> Vs {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}"
        by (simp add: Vs_def)

      assume "x \<notin> A"
      show "x \<in> Vs E"
      proof(cases "x \<in> Vs E")
        case True
then show ?thesis by auto
next
  case False
  have "x \<in> Vs {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}" 
  using False \<open>x \<in> Vs E \<or> x \<in> Vs {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}\<close> by blast
  then obtain x' y' where " x' \<in> Vs E \<and> y' \<in> A \<and> x \<in> {x', y'}" 
    by (smt (verit, del_insts) Union_eq Vs_def mem_Collect_eq singleton_conv2)
  then show ?thesis using `x \<notin> A` 
    by blast
qed
}
  fix x
  assume " x \<in> A"
  obtain y where "y \<in> Vs E" 
    by (metis  Vs_def \<open>E \<noteq> {}\<close> assms(1) equals0I insertI1 vs_member_intro)
  then have "{x, y} \<in> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}" 
    using \<open>x \<in> A\<close> by blast
  then show "x \<in> Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})" 
    using  insertCI by auto
qed (simp add: Vs_def)

  then have "card (Vs ?H) = card (Vs E) + card A" 
    by (simp add: assms(1) assms(4) assms(6) card_Un_disjoint sup_commute)
  then have "card (Vs ?H) = card (Vs E) + ?k" 
    using assms(5) by presburger

  have "finite (Vs ?H)" using `Vs ?H = Vs E \<union> A`
    by (simp add: assms(1) assms(4))
 
  have "graph_invar ?H"  using `finite (Vs ?H)`  
    using assms(1) assms(6) by fastforce

  have "?k \<le> card (Vs E)" 
    by (metis (no_types, lifting) assms(1) assms(2) card_Diff_subset diff_le_self diff_odd_comps_card dual_order.trans finite_subset)

  show "\<exists>M. perfect_matching ?H M"
  proof(rule ccontr)
    assume "\<nexists>M. perfect_matching ?H M" 
    then have "\<not> tutte_condition ?H" 
      by (simp add: \<open>graph_invar (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> tutte)
    then have "\<exists>Y \<subseteq> Vs ?H. card (diff_odd_components ?H Y) > card Y"
      by (meson le_less_linear tutte_condition_def)
    then obtain Y where Y_subs:"Y \<subseteq> Vs ?H \<and> card (diff_odd_components ?H Y) > card Y" by auto
    have "even ?k = even (card (Vs E))" using diff_odd_component_parity'[of E X]
      using `card (diff_odd_components E X) \<ge> card X`
      using assms(1) assms(2) by blast
    then have "even (card (Vs E) + ?k)" by auto
    then have "even (card (Vs ?H)) = even (card (Vs E) + ?k)"
      using `card (Vs ?H) = card (Vs E) + ?k` 
      by presburger
    have "even (card (Vs ?H))" 
      using \<open>even (card (Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}))) = even (card (Vs E) + (card (diff_odd_components E X) - card X))\<close> \<open>even (card (Vs E) + (card (diff_odd_components E X) - card X))\<close> by blast
    
    have "Vs ?H \<in> connected_components ?H"
    proof -
      have "Vs ?H \<noteq> {}" 
        using False \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> assms(5) by force
      then obtain v where "v \<in> Vs E" 
        by fastforce
      have "A \<noteq> {}" 
        by (metis False assms(5) card.empty order_refl)
      then obtain a where "a \<in> A" by auto
      then have "{v, a} \<in> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}" 
        using \<open>v \<in> Vs E\<close> by blast
      then have "{v, a} \<in> ?H" 
        by blast
      have "\<forall>x \<in> Vs ?H. x \<in> connected_component ?H v" 
      proof
        fix x
        assume "x \<in> Vs ?H"
        show "x \<in> connected_component ?H v" 
        proof(cases "x \<in> A")
          case True
  then have "{v, x} \<in> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}" 
        using \<open>v \<in> Vs E\<close> by blast
      then have "{v, x} \<in> ?H" 
        by blast
  then show ?thesis 
    by (meson vertices_edges_in_same_component)
next
  case False
  have "x \<in> Vs E" 
    using False \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> \<open>x \<in> Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> by fastforce
  then have "{a, x} \<in> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}" 
        using \<open>x \<in> Vs E\<close> `a \<in> A`  by blast
      then have "{a, x} \<in> ?H" 
        by blast
  then show ?thesis 
    by (metis (no_types, lifting) \<open>{v, a} \<in> E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}\<close> connected_components_member_trans vertices_edges_in_same_component)

qed
qed
   have "Vs ?H = connected_component ?H v"
  proof(safe)
    {
      fix x 
      assume "x \<in> Vs ?H"
      then show "x \<in> connected_component ?H v" 
        using \<open>\<forall>x\<in>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}). x \<in> connected_component (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) v\<close> by blast
    
    }
    fix x
    assume "x \<in> connected_component ?H v"
    then show "x \<in> Vs ?H" 
      using \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> \<open>v \<in> Vs E\<close> in_connected_component_in_edges by fastforce
  qed
  show ?thesis 
    by (smt (verit, ccfv_SIG) \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = connected_component (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) v\<close> \<open>v \<in> Vs E\<close> \<open>{v, a} \<in> E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}\<close> connected_components_def insertCI mem_Collect_eq vs_transport)
qed

  have "connected_components ?H = {Vs ?H}"
  proof 
    show "connected_components ?H \<subseteq> {Vs ?H}"
    proof
      fix C
      assume "C \<in> connected_components ?H"
      obtain c where "c \<in> C" 
        by (metis (no_types, lifting) \<open>C \<in> connected_components (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> connected_comp_has_vert in_own_connected_component)
      then have "c \<in> Vs ?H" 
        by (metis (no_types, lifting) \<open>C \<in> connected_components (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> connected_comp_verts_in_verts)
      then have "C = Vs ?H" 
        by (metis (no_types, lifting) Int_iff \<open>C \<in> connected_components (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) \<in> connected_components (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> \<open>c \<in> C\<close> connected_components_disj empty_iff)
      then show "C \<in> {Vs ?H}"
        by blast
    qed
    show "{Vs ?H} \<subseteq> connected_components ?H" 
      using \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) \<in> connected_components (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> by blast
  qed
  have "diff_odd_components ?H {} = {}" 
    by (smt (verit) Collect_empty_eq Diff_disjoint Diff_eq_empty_iff Odd_components.diff_odd_components_are_components Un_Diff_Int Y_subs \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) \<in> connected_components (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> \<open>even (card (Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})))\<close> boolean_algebra_cancel.sup0 connected_comp_has_vert connected_components_member_eq graph_diff_empty)
  have "\<exists>y \<in> Vs E. y \<notin> Y"
      proof(rule ccontr)
        assume "\<not> (\<exists>y\<in>Vs E. y \<notin> Y)" 
        then have "\<forall>y\<in>Vs E. y \<in> Y" by auto
        then have "Vs E \<subseteq> Y" by auto
        then have "card (Vs E) \<le> card Y" 
          by (meson Y_subs \<open>graph_invar (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> card_mono finite_subset)
        then have "card (diff_odd_components ?H Y) > card (Vs E)" 
          using Y_subs by linarith 
        then show False 
          by (smt (verit, del_insts) Diff_disjoint Int_commute Nat.le_diff_conv2 Un_Diff_Int Un_Int_eq(1) Y_subs \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> \<open>card (Vs E) \<le> card Y\<close> \<open>card (diff_odd_components E X) - card X \<le> card (Vs E)\<close> \<open>graph_invar (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> add_le_mono assms(1) assms(4) assms(5) assms(6) card_Un_Int diff_add_inverse2 diff_le_self diff_odd_comps_card finite_Diff finite_subset le_trans not_less subset_Un_eq)
      qed
     then obtain y where "y \<in> Vs E \<and> y \<notin> Y" using `\<exists>y \<in> Vs E. y \<notin> Y` by auto
    
    have "A \<subseteq> Y"
    proof(rule ccontr)
      assume " \<not> A \<subseteq> Y"
      then obtain a where "a \<in> A \<and> a \<notin> Y"
        by blast
      have "a \<in> Vs ?H - Y" 
        by (simp add: \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> \<open>a \<in> A \<and> a \<notin> Y\<close>)
    
     
      have "{y, a} \<in> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}" 
        using \<open>a \<in> A \<and> a \<notin> Y\<close> \<open>y \<in> Vs E \<and> y \<notin> Y\<close> by blast
      then have "{y, a} \<in> ?H" by auto
      then have "{y, a} \<in> graph_diff ?H Y" 
        by (simp add: \<open>a \<in> A \<and> a \<notin> Y\<close> \<open>y \<in> Vs E \<and> y \<notin> Y\<close> graph_diff_intro)
      then have "a \<in> Vs (graph_diff ?H Y)" by auto


      have "\<forall>x\<in>Vs ?H - Y. x \<in> connected_component (graph_diff ?H Y) a"
      proof
        fix x
        assume "x \<in> Vs ?H - Y"
        show "x \<in> connected_component (graph_diff ?H Y) a" 
        proof(cases "x \<in> Vs E")
          case True
          then have "{x, a} \<in> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}" 
            using \<open>a \<in> A \<and> a \<notin> Y\<close> by blast
          then have "{x, a} \<in> ?H" by auto
          have "{x, a} \<inter> Y = {}" using \<open>a \<in> A \<and> a \<notin> Y\<close> \<open>x \<in> Vs ?H - Y\<close> 
            by blast
  then show ?thesis 
    by (metis (no_types, lifting) \<open>{x, a} \<in> E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}\<close> graph_diff_intro insert_commute vertices_edges_in_same_component)

next
  case False
  then have "x \<in> A" 
    using \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> \<open>x \<in> Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) - Y\<close> by auto
  then have "{x, y} \<in> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}" 
    using \<open>y \<in> Vs E \<and> y \<notin> Y\<close> by blast
  then have "{x, y} \<in> ?H" 
    by blast
   have "{x, y} \<inter> Y = {}" 
     by (meson DiffD2 \<open>x \<in> Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) - Y\<close> \<open>{y, a} \<in> graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y\<close> graph_diff_elim insert_disjoint(1))
   then have "{x, y} \<in> graph_diff ?H Y" 
     using \<open>{x, y} \<in> E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}\<close> by blast
  then show ?thesis 
    by (metis (no_types, lifting) \<open>{y, a} \<in> graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y\<close> connected_components_member_sym connected_components_member_trans vertices_edges_in_same_component)

qed
qed

      have "connected_components (graph_diff ?H Y) = {connected_component (graph_diff ?H Y) a}"
      proof
        show " connected_components (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y)
    \<subseteq> {connected_component (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) a}"
        proof
          fix C
          assume "C \<in> connected_components (graph_diff ?H Y)"
          then obtain c where "C = connected_component (graph_diff ?H Y) c \<and> 
                                c \<in> (Vs (graph_diff ?H Y))"
            by (meson connected_comp_has_vert)
          then have "c \<in> Vs ?H - Y" 
            by (smt (verit, ccfv_threshold) DiffI Int_iff Y_subs \<open>graph_invar (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> diff_disjoint_elements(2) empty_iff graph_diff_subset subset_iff vs_member)

          then have "C = connected_component (graph_diff ?H Y) a" 
            by (simp add: \<open>C = connected_component (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) c \<and> c \<in> Vs (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y)\<close> \<open>\<forall>x\<in>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) - Y. x \<in> connected_component (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) a\<close> connected_components_member_eq)
          then show "C \<in> {connected_component (graph_diff ?H Y) a}" by auto
        qed
        show "{connected_component (graph_diff ?H Y) a} \<subseteq> 
            connected_components (graph_diff ?H Y)" 
        proof 
          fix C
          assume "C \<in> {connected_component (graph_diff ?H Y) a}"
          then have "C = connected_component (graph_diff ?H Y) a" by auto
          then show "C \<in> connected_components (graph_diff ?H Y)" 
            by (metis (mono_tags, lifting) \<open>C \<in> {connected_component (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) a}\<close> \<open>a \<in> Vs (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y)\<close> \<open>connected_components (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) \<subseteq> {connected_component (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) a}\<close> empty_iff own_connected_component_unique subset_singleton_iff)
        qed
      qed

      have "(odd_components (graph_diff ?H Y)) \<subseteq> connected_components (graph_diff ?H Y)" 
        by (simp add: components_is_union_even_and_odd)

      have "singleton_in_diff ?H Y = {}" 
      proof(rule ccontr)
        assume " singleton_in_diff ?H Y \<noteq> {}"
        then obtain v where "{v} \<in> singleton_in_diff ?H Y \<and> v \<in> Vs ?H \<and> v \<notin> Y \<and> v \<notin> Vs (graph_diff ?H Y)"
          by (smt (verit) empty_subsetI singleton_in_diff_elim subsetI subset_antisym)
        then have "v \<in> connected_component (graph_diff ?H Y) a" 
          by (simp add: \<open>\<forall>x\<in>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) - Y. x \<in> connected_component (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) a\<close>)
        then show False 
          by (smt (z3) Diff_iff Diff_insert_absorb \<open>\<forall>x\<in>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) - Y. x \<in> connected_component (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) a\<close> \<open>a \<in> Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) - Y\<close> \<open>a \<in> Vs (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y)\<close> \<open>{v} \<in> singleton_in_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y \<and> v \<in> Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) \<and> v \<notin> Y \<and> v \<notin> Vs (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y)\<close> connected_components_member_eq insertCI singleton_in_diff_is_component)
      qed
      then have "(odd_components (graph_diff ?H Y)) = (diff_odd_components ?H Y)" 
        by (simp add: diff_odd_components_def)

      then have "(diff_odd_components ?H Y) \<subseteq> {connected_component (graph_diff ?H Y) a}" 
        using \<open>connected_components (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) = {connected_component (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) a}\<close> \<open>odd_components (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) \<subseteq> connected_components (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y)\<close> by presburger
      then have "card (diff_odd_components ?H Y) \<le> card {connected_component (graph_diff ?H Y) a}" 
        by (meson card_mono finite.emptyI finite.insertI)
      then have "card (diff_odd_components ?H Y) \<le> 1" 
        by force
      show False
      proof(cases "card (diff_odd_components ?H Y) = 1")
case True

  then have "card Y = 0"  
    using Y_subs by linarith
  then have "Y = {}" 
    by (meson Y_subs \<open>graph_invar (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> card_eq_0_iff rev_finite_subset)
  then have "(diff_odd_components ?H Y) = {}"
    using \<open>diff_odd_components (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) {} = {}\<close> by fastforce
  then show ?thesis 
    using Y_subs by auto
next
case False
  then show ?thesis 
    by (smt (z3) One_nat_def Y_subs \<open>diff_odd_components (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y \<subseteq> {connected_component (graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y) a}\<close> card.empty card.insert finite.emptyI insert_absorb le0 not_less subset_singleton_iff)

qed
qed

  then have "graph_diff ?H Y = graph_diff E Y" unfolding graph_diff_def
   proof(safe) qed (blast)

   have "singleton_in_diff ?H Y = singleton_in_diff E Y" 
     unfolding singleton_in_diff_def
     apply safe
     
     using \<open>A \<subseteq> Y\<close> \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> \<open>graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y = graph_diff E Y\<close> subsetD apply fastforce
     
     by (simp add: \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> \<open>graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y = graph_diff E Y\<close>)

   then have "diff_odd_components ?H Y = diff_odd_components E Y" 
     by (simp add: \<open>graph_diff (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y = graph_diff E Y\<close> diff_odd_components_def)

   have "diff_odd_components E (Y \<inter> Vs E) = diff_odd_components E Y" 
     by (simp add: diff_odd_components_same_inter_vertices assms(1))
   then have "card (diff_odd_components E (Y \<inter> Vs E)) > card Y" 
     using Y_subs \<open>diff_odd_components (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) Y = diff_odd_components E Y\<close> by auto

   have "Y = (Y \<inter> Vs E) \<union> A" 
     by (metis Un_Int_assoc_eq Y_subs \<open>A \<subseteq> Y\<close> \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> le_iff_inf)
   then have "card Y = card (Y \<inter> Vs E) + card A" 
     by (metis Int_commute Un_Int_eq(2) assms(1) assms(4) assms(6) card_Un_disjoint finite_Int inf_assoc)
   then have "card Y = card (Y \<inter> Vs E) + ?k" 
     using assms(5) by presburger
   then have "card (diff_odd_components E (Y \<inter> Vs E)) > card (Y \<inter> Vs E) + ?k" 
     using \<open>card Y < card (diff_odd_components E (Y \<inter> Vs E))\<close> by presburger
   then have "card (diff_odd_components E (Y \<inter> Vs E)) - card (Y \<inter> Vs E) > ?k" by auto

   then show False 
     by (meson Int_lower2 assms(3) not_less)
 qed
qed
qed


lemma  berge_formula2:
  assumes "graph_invar E"
  assumes "graph_matching E M"
  assumes "X \<subseteq> Vs E"
 assumes "\<forall>Y \<subseteq> Vs E. int (card (diff_odd_components E X)) - int (card X) \<ge> 
          int (card (diff_odd_components E Y)) - int (card Y)" 
 assumes "\<forall>M'. graph_matching E M' \<longrightarrow> card M \<ge> card M'"
assumes "finite A" 
  assumes "card A = card (diff_odd_components E X) - card X"
  assumes "A \<inter> Vs E = {}" 
  shows " 2 * (card M) + card (diff_odd_components E X) - card X \<ge> card (Vs E)"
proof(cases "E={}")
  case True
  have "Vs E = {}" using True 
    by (simp add: Vs_def)
  then  have "{{x, y}| x y. x \<in> Vs E \<and> y \<in> A} = {}" 
    by blast
  then have "(E \<union> {{x, y}| x y. x \<in> Vs E \<and> y \<in> A}) = {}" using True by auto
  then show ?thesis 
    using \<open>Vs E = {}\<close> by auto
next
  case False
  then have "E \<noteq> {}" by auto
 let ?H = "(E \<union> {{x, y}| x y. x \<in> Vs E \<and> y \<in> A})" 
  let ?k = "card (diff_odd_components E X) - card X"

  show ?thesis
  proof(cases "card (diff_odd_components E X) \<le> card X")
    case True

    then have "\<forall>Y \<subseteq> Vs E. card (diff_odd_components E Y) \<le> card Y" 
      
      by (smt (verit, ccfv_threshold) assms(4) of_nat_le_iff)
    then have "tutte_condition E" by auto
    then obtain M' where "perfect_matching E M'" using tutte
      using assms(1) by auto
    then have "graph_matching E M'" 
      by (meson perfect_matching_elim(2) perfect_matching_elim(3))
    then have "card M' \<le> card M" 
      by (simp add: assms(5))
    then have "card (Vs M') \<le> card (Vs M)" 
      by (smt (verit, del_insts) Vs_subset \<open>perfect_matching E M'\<close> add_le_mono assms(2) finite_subset matching_vertices_double_size mult_2 perfect_matching_def subset_iff)
    then have "card (Vs M) \<ge> card (Vs E)" 
      by (metis \<open>perfect_matching E M'\<close> perfect_matching_elim(4))
    have "Vs M \<subseteq> Vs E" 
      by (simp add: Vs_subset assms(2))
    then have "Vs M =  Vs E" 
      by (metis Diff_eq_empty_iff \<open>card (Vs E) \<le> card (Vs M)\<close> assms(1) card.empty card_Diff_subset card_gt_0_iff diff_is_0_eq finite_Diff finite_subset subset_antisym)
    then have "perfect_matching E M" 
      by (simp add: assms(1) assms(2) perfect_matching_intro)
    have "2 * card M = card (Vs E)" 
      by (metis \<open>Vs M = Vs E\<close> assms(1) assms(2) matching_vertices_double_size subset_iff)

   have "\<forall>x \<in> (Vs E). card {x} \<ge> card (diff_odd_components E {x})"
     
     by (metis Int_lower2 \<open>\<forall>Y\<subseteq>Vs E. card (diff_odd_components E Y) \<le> card Y\<close> assms(8) insert_subset)
   then  have "\<forall>x \<in> (Vs E). even (card {x} - card (diff_odd_components E {x}))"
     by (metis Int_lower2 \<open>2 * card M = card (Vs E)\<close> assms(1) assms(8) diff_odd_component_parity dvd_triv_left insert_subset)

   
    then have "\<forall>x \<in> (Vs E).card (diff_odd_components E {x}) = 1"
      by (metis One_nat_def Suc_leI \<open>\<forall>x\<in>Vs E. card (diff_odd_components E {x}) \<le> card {x}\<close> antisym_conv card.empty card.insert dvd_diffD empty_iff finite.emptyI not_less odd_card_imp_not_empty odd_one zero_order(2))
    then have "\<forall>x \<in> (Vs E). barrier E {x}"
      by (metis barrier_def insert_not_empty is_singleton_altdef is_singleton_def)
    then have "\<exists> X \<subseteq> Vs E. barrier E X" 
      by (metis False Vs_def assms(1) bot.extremum ex_in_conv insert_subset vs_member)
    then obtain X' where "X' \<subseteq> Vs E \<and> card (diff_odd_components E X') = card X'"
      by (meson Tutte_theorem3.barrier_def)
    have "card (diff_odd_components E X) - card X = 0" 
      using True diff_is_0_eq' by blast 
    then show ?thesis 
      using \<open>2 * card M = card (Vs E)\<close> assms(4) by force
  next
    case False
 
  have "card (diff_odd_components E X) \<ge> card X" 
    by (meson False le_cases)
 have "Vs ?H = Vs E \<union> A"
  proof(safe)
    {
      fix x
      assume "x \<in> Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})"
      then have "x \<in> Vs E \<or> x \<in> Vs {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}"
        by (simp add: Vs_def)

      assume "x \<notin> A"
      show "x \<in> Vs E"
      proof(cases "x \<in> Vs E")
        case True
then show ?thesis by auto
next
  case False
  have "x \<in> Vs {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}" 
  using False \<open>x \<in> Vs E \<or> x \<in> Vs {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}\<close> by blast
  then obtain x' y' where " x' \<in> Vs E \<and> y' \<in> A \<and> x \<in> {x', y'}" 
    by (smt (verit, del_insts) Union_eq Vs_def mem_Collect_eq singleton_conv2)
  then show ?thesis using `x \<notin> A` 
    by blast
qed
}
  fix x
  assume " x \<in> A"
  obtain y where "y \<in> Vs E" 
    by (metis  Vs_def \<open>E \<noteq> {}\<close> assms(1) equals0I insertI1 vs_member_intro)
  then have "{x, y} \<in> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}" 
    using \<open>x \<in> A\<close> by blast
  then show "x \<in> Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})" 
    using  insertCI by auto
qed (simp add: Vs_def)
   have "card (Vs ?H) = card (Vs E) + card A" 
     by (simp add: \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> assms(1) assms(6) assms(8) card_Un_disjoint sup_commute)
  then have "card (Vs ?H) = card (Vs E) + ?k" 
    using assms(7) by presburger

  have "finite (Vs ?H)" using `Vs ?H = Vs E \<union> A` 
    by (simp add: assms(1) assms(6))
 
  have "graph_invar ?H"  using `finite (Vs ?H)`  
    using assms(1) assms(8) by fastforce
  obtain Mh where Mh:"perfect_matching ?H Mh" 
    using  construct_perfect_matching_with_new_vertices[of E X A] 
    using assms(1) assms(3) assms(4) assms(6) assms(7) assms(8) 
    by (smt (verit, best) \<open>card X \<le> card (diff_odd_components E X)\<close> diff_add_inverse le_Suc_ex le_diff_conv of_nat_add of_nat_le_iff)
  have "matching Mh" 
    using Mh perfect_matching_elim(2) by blast
  have "Vs Mh = Vs ?H" 
    by (simp add: Mh perfect_matching_elim(4))

  have "\<forall>a \<in> Vs ?H. \<exists>! e \<in> Mh. a \<in> e" 
    by (metis (no_types, lifting) \<open>Vs Mh = Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> \<open>matching Mh\<close> matching_def2)
  have "\<forall>a \<in> A.  \<exists>! e \<in> Mh. a \<in> e" 
    by (simp add: \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> \<open>\<forall>a\<in>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}). \<exists>!e. e \<in> Mh \<and> a \<in> e\<close>)

  let ?edges_A = " {e. e \<in> Mh \<and> e \<inter> A \<noteq> {}}"
  have "?edges_A \<subseteq> Mh" by auto
  then have "card ((Vs ?edges_A) \<inter> A) = sum (\<lambda> e. card (e \<inter> A)) (?edges_A)" 
    using werew2[of Mh ?edges_A] `matching Mh` 
    using \<open>Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}) = Vs E \<union> A\<close> \<open>Vs Mh = Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> assms(1) assms(6) by fastforce

  have "((Vs ?edges_A) \<inter> A) = A"
  proof(safe)
    fix x
    assume "x \<in> A"
    then obtain e where "e\<in> Mh \<and> x \<in> e" 
    using `\<forall>a \<in> A.  \<exists>! e \<in> Mh. a \<in> e` 
    by blast
  then have "e \<in> ?edges_A" 
    using \<open>x \<in> A\<close> by blast
  then show "x \<in> (Vs ?edges_A)" 
    using \<open>e \<in> Mh \<and> x \<in> e\<close> by blast
qed
  have "\<forall>e \<in> (?edges_A). card (e \<inter> A) = 1"
  proof
    fix e
    assume "e \<in> ?edges_A"
    then have "(e \<inter> A)  \<noteq> {}" by auto
    then have "card (e \<inter> A) \<ge> 1" 
      by (simp add: Suc_leI assms(6) card_gt_0_iff)
then have "e \<in> ?H" 
        using Mh \<open>e \<in> {e \<in> Mh. e \<inter> A \<noteq> {}}\<close> perfect_matching_elim(3) by auto
    have "card (e \<inter> A) \<noteq> 2" 
    proof
      assume "card (e \<inter> A) = 2" 
      
      have "e \<notin> E"         using \<open>e \<inter> A \<noteq> {}\<close> assms(8) by blast
      have "e \<in>{{x, y} |x y. x \<in> Vs E \<and> y \<in> A}"       
        using \<open>e \<in> E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}\<close> \<open>e \<notin> E\<close> by blast
      then obtain x y where "e = {x, y} \<and> x \<in> Vs E \<and> y \<in> A" by blast
      then have "(e \<inter> A) = {y}" 
        by (metis Int_insert_left_if0 Int_insert_left_if1 assms(8) disjoint_iff inf_bot_right)
      then have "card (e \<inter> A) = 1" by simp
      then show False using `card (e \<inter> A) = 2` by auto
    qed
    have "card e = 2" using `graph_invar ?H` `e \<in> ?H` 
      by (meson card_edge)

    then show "card (e \<inter> A) = 1" using `card (e \<inter> A) \<ge> 1` 
      by (smt (verit, ccfv_threshold) Int_insert_left_if0 Int_insert_left_if1 One_nat_def \<open>card (e \<inter> A) \<noteq> 2\<close> \<open>e \<in> E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}\<close> \<open>e \<inter> A \<noteq> {}\<close> \<open>graph_invar (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> assms(8) card.empty card.insert finite.emptyI inf_commute inf_right_idem insert_absorb)
  qed
  then have "sum (\<lambda> e. card (e \<inter> A)) (?edges_A) = card ?edges_A" 
    by auto
  have "card {e. e \<in> Mh \<and> e \<inter> A \<noteq> {}} = card A" 
    using \<open>(\<Sum>e | e \<in> Mh \<and> e \<inter> A \<noteq> {}. card (e \<inter> A)) = card {e \<in> Mh. e \<inter> A \<noteq> {}}\<close> \<open>Vs {e \<in> Mh. e \<inter> A \<noteq> {}} \<inter> A = A\<close> \<open>card (Vs {e \<in> Mh. e \<inter> A \<noteq> {}} \<inter> A) = (\<Sum>e | e \<in> Mh \<and> e \<inter> A \<noteq> {}. card (e \<inter> A))\<close> by presburger
  have "{e. e \<in> Mh \<and> e \<inter> A = {}} \<union> {e. e \<in> Mh \<and> e \<inter> A \<noteq> {}} = Mh" by blast
  have "{e. e \<in> Mh \<and> e \<inter> A = {}} \<inter> {e. e \<in> Mh \<and> e \<inter> A \<noteq> {}} = {}" by blast
  have "finite Mh"    
    by (metis (mono_tags, lifting) Vs_def \<open>Vs Mh = Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> \<open>graph_invar (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> finite_UnionD)

  then have "card {e. e \<in> Mh \<and> e \<inter> A = {}} + card {e. e \<in> Mh \<and> e \<inter> A \<noteq> {}} = card Mh "  
    by (metis (no_types, lifting) \<open>{e \<in> Mh. e \<inter> A = {}} \<inter> {e \<in> Mh. e \<inter> A \<noteq> {}} = {}\<close> \<open>{e \<in> Mh. e \<inter> A = {}} \<union> {e \<in> Mh. e \<inter> A \<noteq> {}} = Mh\<close> card_Un_disjoint finite_Un)
  then have "card {e. e \<in> Mh \<and> e \<inter> A = {}} = card Mh - card A" 
    using \<open>card {e \<in> Mh. e \<inter> A \<noteq> {}} = card A\<close> by presburger

  then  have "card (graph_diff Mh A) = card Mh - card A" unfolding graph_diff_def  by blast
  have "(graph_diff Mh A) \<subseteq> Mh" 
    by (simp add: graph_diff_subset)
  have "matching (graph_diff Mh A)" 
    by (meson \<open>graph_diff Mh A \<subseteq> Mh\<close> \<open>matching Mh\<close> matching_def subset_iff)
  have "(graph_diff Mh A) \<subseteq> E " unfolding graph_diff_def
  proof(safe)    
    fix e
    assume "e \<in> Mh" "e \<inter> A = {}" 
    have "e \<in> ?H" 
      using Mh \<open>e \<in> Mh\<close> perfect_matching_elim(3) by auto
    have "e \<notin> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}" 
      using \<open>e \<inter> A = {}\<close> by blast
    then show "e \<in> E" 
      using \<open>e \<in> E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A}\<close> by blast
  qed
  then have "graph_matching E (graph_diff Mh A)" 
    by (simp add: \<open>matching (graph_diff Mh A)\<close>)
  then have "card M \<ge> card Mh - card A" 
    by (metis \<open>card (graph_diff Mh A) = card Mh - card A\<close> assms(5))
  then have "card M + card M \<ge> card Mh + card Mh - card A - card A" 
    by auto
  then have "2* card M + card A\<ge> 2*card Mh - card A" 
    by (metis le_diff_conv mult_2)


  then have "2* card M + ?k \<ge> 2*card Mh - card A" using `2* card M + card A\<ge> 2*card Mh - card A`
    by (metis assms(7))
  also have "2*card Mh - card A = card (Vs Mh) - card A" 
    by (metis (no_types, lifting) Mh \<open>Vs Mh = Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> \<open>graph_invar (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> \<open>matching Mh\<close> matching_vertices_double_size perfect_matching_elim(3) subsetD)
  also have "card (Vs Mh) - card A = card (Vs ?H) - card A" 
    using \<open>Vs Mh = Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})\<close> by presburger
  also  have "card (Vs ?H) - card A = card(Vs E)" 
    using \<open>card (Vs (E \<union> {{x, y} |x y. x \<in> Vs E \<and> y \<in> A})) = card (Vs E) + card A\<close> by presburger
  also have "2 * card M + (card (diff_odd_components E X) - card X) = 
      2 * card M +  card (diff_odd_components E X) - card X"
      using `card (diff_odd_components E X) \<ge> card X` 
    by simp
  finally  show "card (Vs E)
    \<le> 2 * card M + card (diff_odd_components E X) - card X" 
    by blast
qed
qed

lemma  berge_formula2':
  assumes "graph_invar E"
  assumes "graph_matching E M"
  assumes "X \<subseteq> Vs E"
 assumes "\<forall>Y \<subseteq> Vs E. int (card (diff_odd_components E X)) - int (card X) \<ge> 
          int (card (diff_odd_components E Y)) - int (card Y)" 
 assumes "\<forall>M'. graph_matching E M' \<longrightarrow> card M \<ge> card M'" 
  shows " 2 * (card M) + card (diff_odd_components E X) - card X \<ge> card (Vs E)"
proof -
  let ?E' = "{{{x}, {y}}| x y. {x, y} \<in> E}"
  let ?M' = "{{{x}, {y}}| x y. {x, y} \<in> M}"
  let ?X' = "{{x}| x. x \<in> X}"
  have "?M' \<subseteq> ?E'" 
    using assms(2) by blast
  have "matching ?M'" unfolding matching_def 
    apply safe 
           apply (metis assms(2) doubleton_eq_iff insertCI matching_unique_match)
      apply (smt (verit, ccfv_SIG) Diff_insert_absorb assms(2) insertCI insert_commute insert_subsetI matching_unique_match singleton_insert_inj_eq')
         apply (metis assms(2) doubleton_eq_iff insertCI matching_unique_match)
        apply (metis assms(2) doubleton_eq_iff insertCI matching_unique_match)
   apply (smt (z3) Diff_insert_absorb assms(2) insertCI insert_absorb insert_commute matching_unique_match singleton_insert_inj_eq)
  apply (smt (verit) Diff_insert_absorb assms(2) insertCI insert_commute insert_subsetI matching_unique_match singleton_insert_inj_eq')
  apply (smt (z3) assms(2) insertCI insert_absorb insert_ident matching_unique_match singleton_insert_inj_eq')
  by (smt (verit) Diff_insert_absorb assms(2) insertCI insert_absorb insert_commute matching_unique_match singleton_insert_inj_eq)


  then  have "graph_matching ?E' ?M'" 
    using \<open>{{{x}, {y}} |x y. {x, y} \<in> M} \<subseteq> {{{x}, {y}} |x y. {x, y} \<in> E}\<close> by fastforce






  obtain A where "finite A \<and> card A = card (diff_odd_components E X) - card X \<and> A \<inter> Vs E = {}" 
    sorry
  then show " 2 * (card M) + card (diff_odd_components E X) - card X \<ge> card (Vs E)"
    using berge_formula2[of E M X A] assms 
    by blast
qed

end
