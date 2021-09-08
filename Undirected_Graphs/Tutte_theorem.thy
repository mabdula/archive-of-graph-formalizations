theory Tutte_theorem
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

lemma connected_component_not_singleton:
  assumes "graph_invar E"
  assumes "v\<in> Vs E"
  shows "card (connected_component E v) > 1"
proof -
  have "\<exists>e \<in> E. v \<in> e" using assms 
    by (meson vs_member_elim)
  then obtain e where "e \<in> E" "v \<in> e" by auto
  then have "\<exists>u \<in> Vs E. \<exists> t \<in> Vs E.  e = {t, u}" 
    by (metis assms(1) edges_are_Vs insert_commute)
  then obtain u t where "u \<in> Vs E" "t \<in> Vs E" "e = {t, u}" by auto

  show ?thesis 
    by (smt (verit, best) \<open>e = {t, u}\<close> \<open>e \<in> E\<close> \<open>u \<in> Vs E\<close> \<open>v \<in> e\<close> assms(1) card_0_eq card_1_singletonE connected_component_subs_Vs connected_components_closed' doubleton_eq_iff finite_subset in_con_comp_insert insert_absorb insert_iff less_one linorder_neqE_nat own_connected_component_unique)
qed

lemma werew:
  assumes "finite (Vs M)"
  assumes "matching M"
  assumes " C \<subseteq> M "
  shows "card ( Vs C) = sum (\<lambda> e. card e) (C)" 
proof -
  have "finite M" using assms(1) 
    by (metis Vs_def finite_UnionD)
  then have "finite C"  
    using assms(3) finite_subset by auto
  show ?thesis using `finite C` assms(3)
  proof(induct C)
    case empty
    then show ?case 
      by (simp add: Vs_def)
  next
    case (insert x F)
    have "finite F" 
      by (simp add: insert.hyps(1))
    then have "finite (Vs F)" 
      by (meson Vs_subset assms(1) finite_subset insert.prems insert_subset)
    have "finite {x}"  by auto
    have "F \<subseteq> M"
      using insert.prems by auto
    then have "card (Vs F) = sum card F"
      using insert.hyps(3) by blast
    have "x \<in> M" 
      using insert.prems by auto
    then have "\<forall>y \<in> F. x \<inter> y = {}" 
      by (metis Int_emptyI \<open>F \<subseteq> M\<close> assms(2) insert.hyps(2) matching_unique_match subset_iff)
    then have "Vs F \<inter> Vs {x} = {}" 
      by (metis Int_commute Sup_empty Sup_insert Vs_def assms(2) insert.hyps(2) insert.prems insert_partition matching_def subsetD sup_bot_right)
    have "card ((Vs F) \<union> (Vs {x})) = card (Vs F) + card (Vs {x})" 
      by (metis Sup_empty Sup_insert Vs_def Vs_subset \<open>Vs F \<inter> Vs {x} = {}\<close> assms(1) card_Un_disjoint finite_Un finite_subset insert.prems sup_bot_right)
    then have "card (Vs (insert x F)) = card (Vs F) + card x"
      by (simp add: Vs_def sup_commute)
    then show ?case 
      by (simp add: \<open>card (Vs F) = sum card F\<close> insert.hyps(1) insert.hyps(2))
  qed
qed

lemma werew2:
  assumes "finite (Vs M)"
  assumes "matching M"
  assumes " C \<subseteq> M "
  shows "card ((Vs C) \<inter> X) = sum (\<lambda> e. card (e \<inter> X)) (C)" 
proof -
  have "finite M" using assms(1) 
    by (metis Vs_def finite_UnionD)
  then have "finite C"  
    using assms(3) finite_subset by auto
  show ?thesis using `finite C` assms(3)
  proof(induct C)
    case empty
    then show ?case   by (simp add: Vs_def)
  next
    case (insert x F)
    have "finite F" 
      by (simp add: insert.hyps(1))
    then have "finite (Vs F)" 
      by (meson Vs_subset assms(1) finite_subset insert.prems insert_subset)
    have "finite {x}"  by auto
    have "F \<subseteq> M"
      using insert.prems by auto
    then have "card (Vs F \<inter> X) = (\<Sum>e\<in>F. card (e \<inter> X))"
      using insert.hyps(3) by blast
    have "x \<in> M" 
      using insert.prems by auto
    then have "\<forall>y \<in> F. x \<inter> y = {}" 
      by (metis Int_emptyI \<open>F \<subseteq> M\<close> assms(2) insert.hyps(2) matching_unique_match subset_iff)
    then have "Vs F \<inter> Vs {x} = {}" 
      by (metis Int_commute Sup_empty Sup_insert Vs_def assms(2) insert.hyps(2) insert.prems insert_partition matching_def subsetD sup_bot_right)
    have "card ((Vs F \<inter> X) \<union> (Vs {x} \<inter> X)) = card (Vs F \<inter> X) + card (Vs {x} \<inter> X)" 

      by (smt (verit, ccfv_threshold) Int_Un_eq(2) Int_ac(3) Sup_empty Sup_insert Vs_def Vs_subset \<open>Vs F \<inter> Vs {x} = {}\<close> \<open>finite (Vs F)\<close> assms(1) boolean_algebra_cancel.inf2 card_Un_disjoint finite_Int finite_subset inf_sup_absorb insert.prems sup_bot_right)
    then have "card (Vs (insert x F) \<inter> X ) = card (Vs F \<inter> X) + card (x \<inter> X)"    
      by (metis Int_Un_distrib2 Sup_empty Sup_insert Un_left_commute Vs_def sup_bot_right)
    then show ?case 
      by (simp add: \<open>card (Vs F \<inter> X) = (\<Sum>e\<in>F. card (e \<inter> X))\<close> insert.hyps(1) insert.hyps(2))
  qed
qed


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

lemma component_in_E:
  assumes "C \<in> (diff_odd_components E X)"
  shows "C \<subseteq> Vs E"
proof(cases "C \<in> (odd_components (graph_diff E X))")
  case True
  then have "\<exists> v \<in> Vs (graph_diff E X). connected_component (graph_diff E X) v = C"
    unfolding odd_components_def 
    by blast
  then show ?thesis 
    by (metis diff_connected_component_subset graph_diff_subset subset_eq vs_member)
next
  case False
  have "C \<in> (singleton_in_diff E X)" 
    by (metis False UnE assms diff_odd_components_def)
  then show ?thesis 
    by (smt (z3) Diff_eq_empty_iff Diff_subset_conv Un_upper1 insert_subset mem_Collect_eq singleton_in_diff_def)
qed

lemma card_sum_is_multiplication:
  fixes k :: real
  assumes "finite A"
  shows "sum (\<lambda> e. k) A = k * (card A)"

  by simp


lemma union_card_is_sum:
  assumes "finite A"
  assumes "\<forall>C \<in> A. finite (f C)" 
  assumes "\<forall> C1 \<in> A. \<forall> C2 \<in> A. C1 \<noteq> C2 \<longrightarrow> f C1 \<inter> f C2 = {}"
  shows "sum (\<lambda> C. card (f C)) A = card (\<Union>C\<in>A. (f C))" using assms
proof(induct A)
  case empty
  then show ?case 
    by simp
next
  case (insert x F)
  then have "\<forall>C1\<in> F. \<forall>C2\<in> F. C1 \<noteq> C2 \<longrightarrow> f C1 \<inter> f C2 = {}" using insert.prems
    by simp
  then have " (\<Sum>C\<in>F. card (f C)) =  card (\<Union> (f ` F))"
    using insert.hyps(3) 
    by (simp add: insert.prems(1))
  have "\<Union> (f ` (insert x F)) = (\<Union> (f ` F)) \<union> f x" 
    by blast
  have "\<Union> (f ` F) \<inter> f x = {}" 
    using insert.hyps(2) insert.prems by fastforce
  then have " card ((\<Union> (f ` F)) \<union> f x) =  card (\<Union> (f ` F)) + card (f x)" 
    by (meson card_Un_disjoint finite_UN_I insert.hyps(1) insert.prems(1) insertCI)
  then have "card (\<Union> (f ` (insert x F))) = card (\<Union> (f ` F)) + card (f x)"
    using \<open>\<Union> (f ` insert x F) = \<Union> (f ` F) \<union> f x\<close> by presburger
  then show ?case 
    by (simp add: \<open>(\<Sum>C\<in>F. card (f C)) = card (\<Union> (f ` F))\<close> insert.hyps(1) insert.hyps(2))
qed  

lemma diff_odd_components_not_in_X:
  assumes "C \<in> (diff_odd_components E X)"
  shows  "C \<inter> X = {}"
proof(rule ccontr)
  assume "C \<inter> X \<noteq> {}"
  then obtain c where "c \<in> C" "c \<in> X" by blast
  show False
  proof(cases "C \<in> (odd_components (graph_diff E X))")
    case True
    then have "\<exists> v \<in> Vs (graph_diff E X). connected_component (graph_diff E X) v = C" 
      using odd_components_def by auto
    then have "connected_component (graph_diff E X) c = C" 
      by (metis \<open>c \<in> C\<close> connected_components_member_eq)

    then have "c \<in> Vs (graph_diff E X)"
      by (metis \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>c \<in> C\<close> in_connected_component_in_edges)

    then show ?thesis unfolding graph_diff_def  
      by (smt (verit) \<open>c \<in> X\<close> insert_Diff insert_disjoint(1) mem_Collect_eq vs_member)
  next
    case False
    then have "C \<in>  (singleton_in_diff E X)"
      using \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_def by auto
    then have "\<exists>v. C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)" unfolding 
        singleton_in_diff_def 
      by blast
    then show ?thesis 
      using \<open>c \<in> C\<close> \<open>c \<in> X\<close> by blast
  qed
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

lemma tutte1:
  assumes "\<exists>M. perfect_matching E M"
  shows "tutte_condition E"
proof(rule ccontr)
  obtain M where "perfect_matching E M" using assms by auto
  assume "\<not> tutte_condition E"
  then have "\<exists> X \<subseteq> Vs E. card (diff_odd_components E X) > card X" unfolding tutte_condition_def
    by (meson le_less_linear)
  then obtain X where "X \<subseteq> Vs E \<and> card (diff_odd_components E X) > card X"
    by blast
  then have "X \<subseteq> Vs M"
    using `perfect_matching E M`
    unfolding perfect_matching_def by auto
  have "graph_invar E" 
    using \<open>perfect_matching E M\<close> 
      perfect_matching_def by auto

  have  "matching M" 
    using \<open>perfect_matching E M\<close>
      perfect_matching_def by blast 
  have "finite M"
    by (metis Vs_def \<open>perfect_matching E M\<close> finite_UnionD perfect_matching_def)
  then have "finite (Vs M)" 
    by (metis \<open>perfect_matching E M\<close> perfect_matching_def)
  let ?comp_out  = "\<lambda> C. {e. e \<in> M \<and> (\<exists> x y. e = {x,y} \<and> y \<in> C \<and> x \<in> X)}"
  let ?QX = "(diff_odd_components E X)"

  have 2:"\<forall> e \<in> E. card e = 2" using `graph_invar E` by auto


  have "\<forall> C \<in> ?QX. (?comp_out C) \<subseteq> M"
    by blast

  have 3:"\<forall> C \<in> ?QX. card (Vs (?comp_out C)) =  sum (\<lambda> e. card e) (?comp_out C)"
    using \<open>finite (Vs M)\<close> \<open>matching M\<close> werew by fastforce


  have "\<forall> C \<in> ?QX. finite (?comp_out C)" 
    by (simp add: \<open>finite M\<close>)
  have "\<forall> C \<in> ?QX. \<forall> e \<in> (?comp_out C). card e = 2" using 2
    using \<open>perfect_matching E M\<close> perfect_matching_def by auto

  then have "\<forall> C \<in> ?QX. sum (\<lambda> e. card e) (?comp_out C) = 
      sum (\<lambda> e. 2) (?comp_out C)"  by (meson sum.cong)

  then have "\<forall> C \<in> ?QX. card (Vs (?comp_out C)) = 
      sum (\<lambda> e. 2) (?comp_out C)" using 3
    by simp 
  then have "\<forall> C \<in> ?QX. card (?comp_out C) * 2 =
    sum (\<lambda> e. 2) (?comp_out C) " by simp

  then have "\<forall> C \<in> ?QX. card (?comp_out C) * 2 =
     card ( Vs (?comp_out C))" 
    by (metis (no_types, lifting) \<open>\<forall>C\<in>diff_odd_components E X. card (Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}) = (\<Sum>e | e \<in> M \<and> (\<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X). 2)\<close>)

  have 5:"\<forall> C \<in> ?QX. \<forall> e \<in> (?comp_out C).  card (e \<inter> X) = 1"
  proof
    fix C
    assume "C \<in> ?QX"
    then have "C \<inter> X = {}" using  diff_odd_components_not_in_X[of C E X] by simp
    then show "\<forall> e \<in> (?comp_out C). card (e \<inter> X) = 1"
      using Int_commute 
      by fastforce
  qed
  have "\<forall> C \<in> ?QX. sum (\<lambda> e. card (e \<inter> X)) (?comp_out C) =
      sum (\<lambda> e. 1) (?comp_out C)" using 5 
    by simp
  then have "\<forall> C \<in> ?QX. 
    sum (\<lambda> e. card (e \<inter> X)) (?comp_out C) = card (?comp_out C)" 
    by fastforce
  have card_sum:"\<forall> C \<in> ?QX.

 card ((Vs (?comp_out C)) \<inter> X) = sum (\<lambda> e. card (e \<inter> X)) (?comp_out C)"
    using werew2 `matching M` `finite (Vs M)`
      `\<forall> C \<in> ?QX. (?comp_out C) \<subseteq> M`
    using sum.cong by fastforce


  then have "\<forall> C \<in> ?QX.
 card ((Vs (?comp_out C)) \<inter> X) =  card (?comp_out C)" using card_sum

    by (simp add: \<open>\<forall> C \<in> ?QX. 
    sum (\<lambda> e. card (e \<inter> X)) (?comp_out C) = card (?comp_out C)\<close>)

  then have "sum (\<lambda> C. card (?comp_out C)) ?QX = 
            sum (\<lambda> C. card ((Vs (?comp_out C)) \<inter> X)) ?QX"   
    by force

  have "( \<Union>C \<in>?QX. (((Vs (?comp_out C)) \<inter> X))) \<subseteq> X "
  proof
    fix x
    assume "x \<in> ( \<Union>C \<in>?QX. (((Vs (?comp_out C)) \<inter> X)))"
    then have "\<exists> C \<in> ?QX. x \<in> ((Vs (?comp_out C)) \<inter> X)"
      by blast
    then show "x \<in> X" 
      by blast
  qed
  let ?f = "(\<lambda> C. ((Vs (?comp_out C)) \<inter> X))"
  have "\<forall>C \<in> ?QX. finite ((Vs (?comp_out C)) \<inter> X)" 
    by (meson \<open>X \<subseteq> Vs M\<close> \<open>finite (Vs M)\<close> finite_Int finite_subset)
  have "finite ?QX" 
    by (metis \<open>X \<subseteq> Vs E \<and> card X < card ?QX\<close> card_eq_0_iff card_gt_0_iff less_imp_triv)



  have "\<forall> C1 \<in>?QX. \<forall> C2 \<in> ?QX.
    C1 \<noteq> C2 \<longrightarrow> ((Vs (?comp_out C1)) \<inter> X) \<inter> ((Vs (?comp_out C2)) \<inter> X) = {}"
  proof
    fix C1 
    assume "C1 \<in>?QX"
    show " \<forall> C2 \<in> ?QX.
    C1 \<noteq> C2 \<longrightarrow> ((Vs (?comp_out C1)) \<inter> X) \<inter> ((Vs (?comp_out C2)) \<inter> X) = {}"
    proof
      fix C2
      assume "C2 \<in> ?QX"
      show " C1 \<noteq> C2 \<longrightarrow> ((Vs (?comp_out C1)) \<inter> X) \<inter> ((Vs (?comp_out C2)) \<inter> X) = {}"
      proof
        assume "C1 \<noteq> C2"

        show "((Vs (?comp_out C1)) \<inter> X) \<inter> ((Vs (?comp_out C2)) \<inter> X) = {}"
        proof(rule ccontr)
          assume "((Vs (?comp_out C1)) \<inter> X) \<inter> ((Vs (?comp_out C2)) \<inter> X) \<noteq> {}"
          then have "\<exists>u. u \<in> ((Vs (?comp_out C1)) \<inter> X) \<inter> ((Vs (?comp_out C2)) \<inter> X)" by auto
          then obtain u where "u \<in> ((Vs (?comp_out C1)) \<inter> X)" "u \<in>((Vs (?comp_out C2)) \<inter> X)" 
            by auto
          then have "u \<in> X" by blast
          have "u \<in> (Vs (?comp_out C1))" 
            using \<open>u \<in> ((Vs (?comp_out C1)) \<inter> X)\<close> by blast
          have"u \<in> (Vs (?comp_out C2))"
            using \<open>u \<in> ((Vs (?comp_out C2)) \<inter> X)\<close> by blast


          then have "\<exists> e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C2 \<and> x \<in> X \<and> u \<in> e" 
            by (smt (verit) mem_Collect_eq vs_member)
          then obtain e2 where "e2 \<in> M \<and> (\<exists>x y. e2 = {x, y} \<and> y \<in> C2 \<and> x \<in> X) \<and> u \<in> e2" by auto

          then have "\<exists> e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C1 \<and> x \<in> X \<and> u \<in> e" 
            using `u \<in> (Vs (?comp_out C1)) ` by (smt (verit) mem_Collect_eq vs_member)
          then obtain e1 where "e1 \<in> M \<and> (\<exists>x y. e1 = {x, y} \<and> y \<in> C1 \<and> x \<in> X) \<and> u \<in> e1" by auto
          then have "e1 = e2" 
            by (meson \<open>matching M\<close> \<open>e2 \<in> M \<and> (\<exists>x y. e2 = {x, y} \<and> y \<in> C2 \<and> x \<in> X) \<and> u \<in> e2\<close>
                matching_unique_match)
          then show False
            using diff_component_disjoint[of E C1 X C2] 
              `graph_invar E`
              \<open>C1 \<in> diff_odd_components E X\<close>
              \<open>C1 \<noteq> C2\<close> 
              \<open>C2 \<in> diff_odd_components E X\<close>
              \<open>e1 \<in> M \<and> (\<exists>x y. e1 = {x, y} \<and> y \<in> C1 \<and> x \<in> X) \<and> u \<in> e1\<close> 
              \<open>e2 \<in> M \<and> (\<exists>x y. e2 = {x, y} \<and> y \<in> C2 \<and> x \<in> X) \<and> u \<in> e2\<close>
            by (metis  diff_odd_components_not_in_X disjoint_iff doubleton_eq_iff)
        qed
      qed
    qed
  qed
  then  have "card ( \<Union>C \<in>?QX. (((Vs (?comp_out C)) \<inter> X))) = 
    sum (\<lambda> C. card ((Vs (?comp_out C)) \<inter> X)) ?QX"
    using union_card_is_sum[of  "?QX" ?f]
      `\<forall>C \<in> ?QX. finite ((Vs (?comp_out C)) \<inter> X)`
      `finite ?QX` 
    by presburger

  then  have "sum (\<lambda> C. card ((Vs (?comp_out C)) \<inter> X)) ?QX \<le> card X" 
    by (metis (no_types, lifting) \<open>(\<Union>C\<in>diff_odd_components E X. Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<inter> X) \<subseteq> X\<close> \<open>X \<subseteq> Vs M\<close> \<open>finite (Vs M)\<close> card_mono finite_subset)

  then have "sum (\<lambda> C. card (?comp_out C)) ?QX \<le> card X"
    using \<open>(\<Sum>C\<in>diff_odd_components E X. card {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}) = (\<Sum>C\<in>diff_odd_components E X. card (Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<inter> X))\<close> by presburger

  then have " \<forall> C \<in> ?QX. finite (?comp_out C)" 
    by (simp add: \<open>finite M\<close>) 
  have "\<forall> C \<in> ?QX. ?comp_out C \<noteq> {}"
  proof
    fix C
    assume "C \<in> ?QX" 
    show "?comp_out C \<noteq> {}"
    proof (cases "C \<in> (odd_components (graph_diff E X))")
      case True
      then have "\<exists> v \<in> Vs (graph_diff E X). connected_component (graph_diff E X) v = C \<and> odd (card C)" 
        using odd_components_def by auto
      then obtain v where "v \<in> Vs (graph_diff E X) \<and> connected_component (graph_diff E X) v = C \<and> odd (card C)"
        by auto

      show ?thesis
      proof(rule ccontr)
        assume "\<not> {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<noteq> {}"
        then have " {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}" by auto
        have "\<forall>x \<in> C. \<exists> e \<in> M. \<exists> y. e = {x, y} \<and> y \<in> C"
        proof
          fix x
          assume "x\<in> C"

          then have "x \<in> Vs E" 
            using \<open>C \<in> diff_odd_components E X\<close> component_in_E by blast
          then have "x \<in> Vs M" 
            by (metis \<open>perfect_matching E M\<close> perfect_matching_def)
          then have "\<exists> e \<in> M. x \<in> e" using `perfect_matching E M` unfolding perfect_matching_def
            by (meson matching_def2)
          then obtain e where "e \<in> M" "x \<in> e" by auto
          have "graph_invar M" 
            by (metis \<open>perfect_matching E M\<close> perfect_matching_def subset_eq)
          then have " \<exists> y \<in> Vs M. e = {x, y}" 
            by (metis (full_types) \<open>e \<in> M\<close> \<open>x \<in> e\<close> edges_are_Vs empty_iff insert_commute insert_iff)
          then obtain y where "y \<in> Vs M \<and> e = {x, y}" by auto
          then have "y \<notin> X" 
            using \<open>e \<in> M\<close> \<open>x \<in> C\<close> \<open>{e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} = {}\<close> by auto
          have "x \<notin> X" 
            using \<open>C \<in> diff_odd_components E X\<close> \<open>x \<in> C\<close> diff_odd_components_not_in_X by blast
          then have "e \<inter> X = {}" 
            using \<open>y \<in> Vs M \<and> e = {x, y}\<close> \<open>y \<notin> X\<close> by fastforce
          then have "e \<in>  (graph_diff E X)" 
            by (metis (mono_tags, lifting) \<open>e \<in> M\<close> \<open>perfect_matching E M\<close> graph_diff_def mem_Collect_eq perfect_matching_def subsetD)
          then have "connected_component (graph_diff E X) x = C" 
            by (metis \<open>v \<in> Vs (graph_diff E X) \<and> connected_component (graph_diff E X) v = C \<and> odd (card C)\<close> \<open>x \<in> C\<close> connected_components_member_eq)
          have "connected_component (graph_diff E X) y = C" 
            by (metis \<open>connected_component (graph_diff E X) x = C\<close> \<open>e \<in> graph_diff E X\<close> \<open>y \<in> Vs M \<and> e = {x, y}\<close> connected_components_member_eq in_con_comp_insert mk_disjoint_insert)
          then have "y \<in> C" 
            by (meson in_own_connected_component)
          then show " \<exists> e \<in> M. \<exists> y. e = {x, y} \<and> y \<in> C" 
            using \<open>e \<in> M\<close> \<open>y \<in> Vs M \<and> e = {x, y}\<close> by blast
        qed
        have "\<forall> e \<in> M. e \<inter> C = {} \<or> e \<inter> C = e"
        proof
          fix e
          assume "e \<in> M" 
          show "e \<inter> C = {} \<or> e \<inter> C = e" 
          proof(rule ccontr)
            assume "\<not> (e \<inter> C = {} \<or> e \<inter> C = e)"
            then have "e \<inter> C \<noteq> {} \<and> e \<inter> C \<noteq> e" 
              by auto
            then have "\<exists> x. x \<in> (e \<inter> C)" by auto
            then obtain x where "x \<in> (e \<inter> C)" by auto
            then have "x \<in> e" "x \<in> C" 
               apply simp 
              using \<open>x \<in> e \<inter> C\<close> by auto
            have "\<exists> y. y \<in> e \<and> y \<notin> C" 
              using \<open>\<not> (e \<inter> C = {} \<or> e \<inter> C = e)\<close> by blast
            show False using `\<forall>x \<in> C. \<exists> e \<in> M. \<exists> y. e = {x, y} \<and> y \<in> C` 
              by (metis \<open>matching M\<close> \<open>\<exists>y. y \<in> e \<and> y \<notin> C\<close> \<open>e \<in> M\<close> \<open>x \<in> C\<close> \<open>x \<in> e\<close> empty_iff insert_iff matching_unique_match)
          qed
        qed
        have " ((Vs M) \<inter> C) = C" 
          by (metis Int_absorb1 \<open>C \<in> diff_odd_components E X\<close> \<open>perfect_matching E M\<close> component_in_E perfect_matching_def)
        have "card ((Vs M) \<inter> C) = sum (\<lambda> e. card (e \<inter> C)) M" using werew2[of M M C] `finite M` `matching M` 
          using \<open>finite (Vs M)\<close> by blast

        have "even (sum (\<lambda> e. card (e \<inter> C)) M)" 
          by (smt (verit, best) "2" \<open>\<forall>e\<in>M. e \<inter> C = {} \<or> e \<inter> C = e\<close> \<open>perfect_matching E M\<close> dvd_sum even_numeral odd_card_imp_not_empty perfect_matching_def subset_eq)

        then have "even (card C)" 
          using \<open>Vs M \<inter> C = C\<close> \<open>card (Vs M \<inter> C) = (\<Sum>e\<in>M. card (e \<inter> C))\<close> by presburger
        show False 
          using \<open>even (card C)\<close> \<open>v \<in> Vs (graph_diff E X) \<and> connected_component (graph_diff E X) v = C \<and> odd (card C)\<close> by blast
      qed
    next
      case False
      then have "C \<in> (singleton_in_diff E X)"
        by (metis UnE \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_def)
      then have " \<exists> v. C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)"
        unfolding singleton_in_diff_def 
        by blast
      then obtain v where " C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)" by auto
      then have "v \<in> Vs M" 
        by (metis \<open>perfect_matching E M\<close> perfect_matching_def)
      then have "\<exists> e \<in> M. v \<in> e" 
        by (meson vs_member_elim)
      then obtain e where " e \<in> M \<and> v \<in> e" 
        by (meson \<open>C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)\<close> vs_member_elim)
      then have "e \<in> E" 
        using \<open>perfect_matching E M\<close> perfect_matching_def by blast
      then have "e \<notin> (graph_diff E X)" 
        using \<open>C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)\<close> 
        using \<open>e \<in> M \<and> v \<in> e\<close> by blast
      then have "e \<inter> X \<noteq> {}" 
        by (simp add: \<open>e \<in> E\<close> graph_diff_def)
      then have "\<exists> y. y \<in> e \<and> y \<in> X" by auto
      then obtain y where "y \<in> e \<and> y \<in> X" by auto
      have "v \<noteq> y" 
        using \<open>C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)\<close> \<open>y \<in> e \<and> y \<in> X\<close> by fastforce
      then have "e = {v, y}" using `y \<in> e \<and> y \<in> X` `e \<in> M \<and> v \<in> e` `graph_invar E` `e \<in> E`
        by fastforce 
      have "v\<in> C" 
        by (simp add: \<open>C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)\<close>)
      then have " \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X" using `y \<in> e \<and> y \<in> X`   using \<open>e = {v, y}\<close> by blast
      then have "e \<in> ?comp_out C" 
        by (simp add: \<open>e \<in> M \<and> v \<in> e\<close>)

      then show ?thesis 
        by blast
    qed
  qed

  then have "\<forall> C \<in> ?QX. card( ?comp_out C) > 0" 
    by (simp add: \<open>\<forall>C\<in>diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<noteq> {}\<close> \<open>\<forall>C\<in>diff_odd_components E X. finite {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}\<close> card_gt_0_iff)
  then have "\<forall> C \<in> ?QX. card( ?comp_out C) \<ge> 1"
    by (simp add: Suc_leI)
  then have "sum (\<lambda> C. card (?comp_out C)) ?QX \<ge> 
    card ?QX"
    using sum_mono by fastforce
  then have " card X \<ge>  card ?QX"  
    using \<open>(\<Sum>C\<in>diff_odd_components E X. card {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}) \<le> card X\<close> order_trans by blast

  then show False 
    using \<open>X \<subseteq> Vs E \<and> card X < card ?QX\<close> not_less by blast
qed

lemma graph_component_edges_partition:
  assumes "graph_invar E"
  shows "\<Union> (components_edges E) = E"
  unfolding components_edges_def
proof(safe)
  fix e
  assume "e \<in> E" 
  then obtain x y where "e = {x, y}" using assms 
    by meson
  then obtain C where "e \<subseteq> C" "C \<in> connected_components E"
    by (metis \<open>e \<in> E\<close> edge_in_component) 
  moreover then have "e \<in> component_edges E C" 
    using \<open>e \<in> E\<close> component_edges_def `e = {x, y}`
    by fastforce
  show "e  \<in> \<Union> {component_edges E C |C.  C \<in> connected_components E}" 

    using \<open>e \<in> component_edges E C\<close> calculation(2) by blast
qed (auto simp add: component_edges_def)

lemma graph_component_partition:
  assumes "graph_invar E"
  shows "\<Union> (connected_components E) = Vs E" 
  unfolding connected_components_def
proof(safe)

  { fix x v
    assume " x \<in> connected_component E v" "v \<in> Vs E"
    then show "x \<in> Vs E" 
      by (metis in_connected_component_in_edges)}

  fix y
  assume "y \<in> Vs E"
  show "y \<in> \<Union> {connected_component E v |v. v \<in> Vs E}" 
    using \<open>y \<in> Vs E\<close> in_own_connected_component by fastforce
qed


lemma sum_card_connected_components:
  assumes "graph_invar E"
  shows "sum (\<lambda> x. card x) (connected_components E) = card (Vs E)"
proof -
  let ?Cs = "connected_components E"
  have "finite ?Cs"  
    by (simp add: assms finite_con_comps)
  moreover  have "\<forall>C \<in> ?Cs. finite C" 
    by (meson assms connected_component_subs_Vs finite_subset)
  moreover have "\<forall> C1 \<in> ?Cs. \<forall> C2 \<in> ?Cs. C1 \<noteq> C2 \<longrightarrow>  C1 \<inter>  C2 = {}"
    by (simp add: connected_components_disj)
  ultimately have "sum (\<lambda> C. card C) ?Cs = card (\<Union>C\<in>?Cs. C)"
    using union_card_is_sum[of ?Cs "(\<lambda> C. C)"] by blast
  then show ?thesis using graph_component_partition[of E] assms by auto
qed

lemma components_is_union_even_and_odd:
  assumes "graph_invar E"
  shows "connected_components E = odd_components E \<union> even_components E"
  unfolding connected_components_def odd_components_def even_components_def
  apply safe
  by auto


lemma components_parity_is_odd_components_parity:
  assumes "graph_invar E"
  shows "even (sum card (connected_components E)) = even (card (odd_components E))"
proof -
  let ?Cs = " (connected_components E)"
  have "finite ?Cs"  
    by (simp add: assms finite_con_comps)
  then have "even (sum card (connected_components E)) = even (card {C \<in> ?Cs. odd (card C)})"
    using Parity.semiring_parity_class.even_sum_iff[of ?Cs card] by auto
  moreover have "{C \<in> ?Cs. odd (card C)} = odd_components E" unfolding connected_components_def
      odd_components_def 
    by blast
  ultimately show ?thesis
    by presburger 
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
proof(safe)
  {
    fix x
    assume "x \<in> Vs (graph_diff E X)"
    then show "x \<in> Vs E" 
      by (meson Vs_subset graph_diff_subset subsetD)
  }
  {
    fix x
    assume " x \<in> Vs (singleton_in_diff E X)"
    then show "x \<in> Vs E" unfolding singleton_in_diff_def
      using vs_transport by fastforce
  }
  {
    fix x
    assume "x \<in> X"
    then show "x \<in> Vs E" using assms(2) by auto
  }
  fix x
  assume " x \<in> Vs E" "x \<notin> X" "x \<notin> Vs (singleton_in_diff E X)"
  then have "\<not> (x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X))" 
    unfolding singleton_in_diff_def 
    by blast


  then show " x \<in> Vs (graph_diff E X)" unfolding graph_diff_def

    using \<open>x \<in> Vs E\<close> \<open>x \<notin> X\<close> by fastforce
qed

lemma diff_disjoint_elements:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  shows "Vs (graph_diff E X) \<inter> Vs (singleton_in_diff E X) = {}" 
    "Vs (graph_diff E X) \<inter> X = {}"
    "Vs (singleton_in_diff E X) \<inter> X = {}"
proof(safe)
  {
    fix x
    assume " x \<in> Vs (graph_diff E X)"
      " x \<in> Vs (singleton_in_diff E X)"
    then show "x \<in> {}" unfolding singleton_in_diff_def 
      by (smt (verit) mem_Collect_eq singletonD vs_member)
  }
  {
    fix x
    assume "x \<in> Vs (graph_diff E X)"  "x \<in> X"
    then have "x \<notin> X" unfolding graph_diff_def
      by (smt (verit, best) disjoint_iff_not_equal mem_Collect_eq vs_member)
    then show "x \<in> {}" using `x \<in> X` by auto
  }

  fix x
  assume "x \<in> Vs (singleton_in_diff E X)" "x \<in> X"
  then show "x \<in> {}" unfolding singleton_in_diff_def
    by (smt (verit) mem_Collect_eq singletonD vs_member)
qed

lemma diff_card_is_sum_elements:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  shows "card (Vs (graph_diff E X)) + card (Vs (singleton_in_diff E X)) +  card X = card (Vs E)"
  using diff_is_union_elements[of E X] diff_disjoint_elements[of E X]
  by (smt (z3) Int_Un_distrib2 assms(1) assms(2) card_Un_disjoint finite_Un sup_bot_right)


value "even (nat (abs (-1)))"

lemma singleton_set_card_eq_vertices:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  shows "card (Vs (singleton_in_diff E X)) = card (singleton_in_diff E X)"
proof -
  let ?A = "(singleton_in_diff E X)"
  have "finite ?A" 
    by (metis Vs_def assms(1) assms(2) diff_is_union_elements finite_Un finite_UnionD)
  moreover  have "\<forall>C \<in> ?A. finite C" 
    by (metis Un_iff assms(1) component_in_E diff_odd_components_def finite_subset)
  moreover have "\<forall> C1 \<in> ?A. \<forall> C2 \<in> ?A. C1 \<noteq> C2 \<longrightarrow> C1 \<inter> C2 = {}" 
    by (smt (verit, best) Int_def empty_Collect_eq mem_Collect_eq singletonD singleton_in_diff_def)

  ultimately  have "sum card ?A = card (Vs ?A)" using assms 
    by (simp add: Vs_def card_Union_disjoint disjnt_def pairwise_def)

  have "\<forall>C \<in> ?A. card C = 1" unfolding singleton_in_diff_def
    using is_singleton_altdef by blast
  then have "sum card ?A = card ?A" 
    by force
  then show ?thesis 
    using \<open>sum card (singleton_in_diff E X) = card (Vs (singleton_in_diff E X))\<close> by presburger
qed

lemma diff_odd_component_parity':
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  assumes  "card X \<le> card (diff_odd_components E X)"
  shows "even (card (diff_odd_components E X) - card X )  = even (card (Vs E))"
proof -
  let ?odd = "(odd_components (graph_diff E X))"
  let ?singl = "(singleton_in_diff E X)"
  let ?EwoX = "(graph_diff E X)"
  let ?allOdd = "diff_odd_components E X"

  have "finite X" 
    using assms(1) assms(2) finite_subset by auto
  then have "finite ?allOdd" unfolding diff_odd_components_def 
    by (smt (verit, ccfv_threshold) Vs_def assms(1) assms(2) components_is_union_even_and_odd diff_is_union_elements finite_Un finite_UnionD finite_con_comps graph_diff_subset subset_eq)
  have "finite ?odd" 
    by (metis \<open>finite ?allOdd\<close> diff_odd_components_def finite_Un)

  have "graph_invar ?EwoX" 
    by (metis (no_types, lifting) assms(1) assms(2) diff_is_union_elements finite_Un graph_diff_subset insert_subset mk_disjoint_insert)

  have "?odd \<inter> ?singl = {}"
    unfolding odd_components_def singleton_in_diff_def 
    using connected_component_subset 
    by fastforce
  then have "card ?allOdd =  card ?odd + card ?singl" 
    unfolding diff_odd_components_def 
    by (metis \<open>finite ?allOdd\<close> card_Un_disjoint diff_odd_components_def finite_Un)
  have "even (card ?allOdd - card X) = even ( card ?allOdd + card X)"
    by (meson assms(3) even_diff_nat not_less)
  also have "\<dots> =  even (card X + card ?odd + card ?singl)"
    using \<open>card ?allOdd = card ?odd + card ?singl\<close> by presburger
  also have "\<dots> = even (card X + card (Vs ?EwoX) + card ?singl)" 
    using odd_components_eq_modulo_cardinality[of "?EwoX"] `graph_invar ?EwoX`
    by auto
  also have "\<dots> = even (card (Vs ?EwoX) + card (Vs ?singl) + card X)" 
    using singleton_set_card_eq_vertices[of E X] assms by presburger
  also have "\<dots>  = even (card (Vs E))"
    using diff_card_is_sum_elements[of E X] assms(1) assms(2) 
    by presburger
  finally show ?thesis by auto
qed

lemma diff_odd_component_parity:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  assumes  "card X \<ge> card (diff_odd_components E X)"
  shows "even (card X - card (diff_odd_components E X)) = even (card (Vs E))"
proof -
  let ?odd = "(odd_components (graph_diff E X))"
  let ?singl = "(singleton_in_diff E X)"
  let ?EwoX = "(graph_diff E X)"
  let ?allOdd = "diff_odd_components E X"

  have "finite X" 
    using assms(1) assms(2) finite_subset by auto
  then have "finite ?allOdd" unfolding diff_odd_components_def 
    by (smt (verit, ccfv_threshold) Vs_def assms(1) assms(2) components_is_union_even_and_odd diff_is_union_elements finite_Un finite_UnionD finite_con_comps graph_diff_subset subset_eq)
  have "finite ?odd" 
    by (metis \<open>finite ?allOdd\<close> diff_odd_components_def finite_Un)

  have "graph_invar ?EwoX" 
    by (metis (no_types, lifting) assms(1) assms(2) diff_is_union_elements finite_Un graph_diff_subset insert_subset mk_disjoint_insert)

  have "?odd \<inter> ?singl = {}"
    unfolding odd_components_def singleton_in_diff_def 
    using connected_component_subset 
    by fastforce
  then have "card ?allOdd =  card ?odd + card ?singl" 
    unfolding diff_odd_components_def 
    by (metis \<open>finite ?allOdd\<close> card_Un_disjoint diff_odd_components_def finite_Un)
  have "even (card X - card ?allOdd) = even (card X + card ?allOdd)"
    by (meson assms(3) even_diff_nat not_less)
  also have "\<dots> =  even (card X + card ?odd + card ?singl)"
    using \<open>card ?allOdd = card ?odd + card ?singl\<close> by presburger
  also have "\<dots> = even (card X + card (Vs ?EwoX) + card ?singl)" 
    using odd_components_eq_modulo_cardinality[of "?EwoX"] `graph_invar ?EwoX`
    by auto
  also have "\<dots> = even (card (Vs ?EwoX) + card (Vs ?singl) + card X)" 
    using singleton_set_card_eq_vertices[of E X] assms by presburger
  also have "\<dots>  = even (card (Vs E))"
    using diff_card_is_sum_elements[of E X] assms(1) assms(2) 
    by presburger
  finally show ?thesis by auto
qed

lemma defvd:
  assumes "graph_invar E"
  assumes "path E p"
  assumes "C \<in> connected_components E"
  assumes "hd p \<in> C"
  assumes "(component_edges E C) \<noteq> {}" 
  shows "path (component_edges E C) p" using assms(2) assms(4) 
proof(induct p rule:list.induct)
  case Nil
  then show ?case 
    by simp
next
  case (Cons x1 x2)
  have "path E (x1 # x2)" 
    by (simp add: Cons.prems(1))
  then have "path E x2" 
    by (metis list.sel(3) tl_path_is_path)
  have "x1 \<in> C" 
    using Cons.prems(2) by auto
  then have "C =  connected_component E x1"
    by (simp add: assms(3) connected_components_closed')

  have "x1 \<in> Vs E"
    by (meson \<open>x1 \<in> C\<close> assms(3) connected_comp_verts_in_verts)
  then have "\<exists> e \<in> E.  x1 \<in> e" 
    by (meson vs_member_elim)
  then obtain e where "e \<in> E \<and> x1 \<in> e" by auto
  then have "\<exists>y. e = {x1, y}"
    using assms(1) by auto 
  then obtain y where " e = {x1, y}" by auto
  then have "y \<in> C" 
    by (metis \<open>C = connected_component E x1\<close> \<open>e \<in> E \<and> x1 \<in> e\<close> in_con_comp_insert insert_Diff)

  then have "e \<subseteq> C" using `x1 \<in> C` 
    by (simp add: \<open>e = {x1, y}\<close>)
  then have "e \<in> (component_edges E C)" unfolding component_edges_def
    using \<open>e = {x1, y}\<close> \<open>e \<in> E \<and> x1 \<in> e\<close> by blast
  then have "x1 \<in> Vs (component_edges E C)" 
    by (simp add: \<open>e = {x1, y}\<close> edges_are_Vs)
  show ?case
  proof(cases "x2 = []")
    case True

    have "path (component_edges E C) [x1]" 
      by (simp add: \<open>x1 \<in> Vs (component_edges E C)\<close>)
    then show ?thesis
      by (simp add: True)
  next
    case False
    have "{x1, hd x2} = hd (edges_of_path (x1 # x2))" 
      by (metis False edges_of_path.simps(3) list.exhaust list.sel(1))
    then have "{x1, hd x2} \<in> E"

      by (metis Cons.prems(1) False equals0D last_in_edge list.set(1) list.set_sel(1) path_ball_edges)
    then have "walk_betw E x1 [x1, hd x2] (hd x2)" 
      by (simp add: edges_are_walks)
    then have "hd x2 \<in> C" 
      by (meson \<open>x1 \<in> C\<close> assms(3) in_con_compI)
    then have "{x1, hd x2} \<subseteq> C" 
      using \<open>e = {x1, y}\<close> \<open>e \<subseteq> C\<close> by blast
    then have "{x1, hd x2} \<in> (component_edges E C)"
      unfolding component_edges_def using `{x1, hd x2} \<in> E`  
      by blast

    then have "path (component_edges E C) x2" using `hd x2 \<in> C`
      by (simp add: Cons.hyps \<open>path E x2\<close>)

    then show ?thesis 
      by (metis False \<open>{x1, hd x2} \<in> component_edges E C\<close> hd_Cons_tl path_2)
  qed
qed

lemma inj_cardinality:
  assumes "finite A"
  assumes "finite B"
  assumes "\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
  assumes "\<forall>a\<in>A. \<exists>b\<in>B. b \<in> a"
  shows "card A \<le> card B" using assms(1) assms(2) assms(3) assms(4)
proof(induct A arbitrary: B)
  case empty
  then show ?case by auto
next
  case (insert x F)
  have "\<forall>a1\<in>F. \<forall>a2\<in>F. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"

    by (simp add: insert.prems(2))
  have "\<exists>b\<in>B. b \<in> x" 
    by (simp add: insert.prems(3))
  then obtain b where "b \<in> B \<and> b \<in> x" by auto
  then have " \<forall>a\<in>F. b \<notin> a" 
    using UnionI insert.hyps(2) insert.prems(2) by auto
  then have " \<forall>a\<in>F. \<exists>b1\<in>B. b1 \<in> a \<and> b1 \<noteq> b" 
    using insert.prems(3)
    by (metis insert_iff)
  then have "\<forall>a\<in>F. \<exists>b1\<in>B-{b}. b1 \<in> a" 
    by (metis \<open>b \<in> B \<and> b \<in> x\<close> insertE insert_Diff)
  have "finite (B - {b})" 
    using insert.prems(1) by blast
  then  have "card F \<le> card (B - {b})" 
    using \<open>\<forall>a1\<in>F. \<forall>a2\<in>F. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}\<close> \<open>\<forall>a\<in>F. \<exists>b1\<in>B - {b}. b1 \<in> a\<close> insert.hyps(3) by presburger 
  then have "card F \<le> card B - 1" 
    by (metis One_nat_def \<open>b \<in> B \<and> b \<in> x\<close> card.empty card.infinite card.insert card_Diff_singleton card_insert_le diff_is_0_eq' emptyE finite.emptyI infinite_remove)
  then have "card F + 1 \<le> card B" using assms
  proof -
    show ?thesis
      by (metis (no_types) One_nat_def Suc_leI \<open>b \<in> B \<and> b \<in> x\<close> \<open>card F \<le> card B - 1\<close> add_Suc_right add_leE card_Diff1_less insert.prems(1) nat_arith.rule0 ordered_cancel_comm_monoid_diff_class.le_diff_conv2)
  qed

  then have "card (insert x F) \<le> card B" 
    by (simp add: insert.hyps(1) insert.hyps(2))
  then show ?case by auto
qed


lemma yfsdf:
  assumes "finite A"
  assumes "finite B"
  assumes "\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
  assumes "\<forall>a\<in>A. \<exists>b\<in>B. b \<in> a"
  shows "\<exists>C\<subseteq>B . \<forall>a\<in>A. \<exists>b\<in>C. b \<in> a \<and> card A = card C" using assms(1) assms(2) assms(3) assms(4)
proof(induct A arbitrary: B)
  case empty
  then show ?case by auto
next
  case (insert x F)
  have "\<forall>a1\<in>F. \<forall>a2\<in>F. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"

    by (simp add: insert.prems(2))
  have "\<exists>b\<in>B. b \<in> x" 
    by (simp add: insert.prems(3))
  then obtain b where "b \<in> B \<and> b \<in> x" by auto
  then have " \<forall>a\<in>F. b \<notin> a" 
    using UnionI insert.hyps(2) insert.prems(2) by auto
  then have " \<forall>a\<in>F. \<exists>b1\<in>B. b1 \<in> a \<and> b1 \<noteq> b" 
    using insert.prems(3)
    by (metis insert_iff)
  then have "\<forall>a\<in>F. \<exists>b1\<in>B-{b}. b1 \<in> a" 
    by (metis \<open>b \<in> B \<and> b \<in> x\<close> insertE insert_Diff)
  have "finite (B - {b})" 
    using insert.prems(1) by blast
  have "\<exists>C\<subseteq>(B - {b}). \<forall>a\<in>F. \<exists>b\<in>C. b \<in> a  \<and> card F = card C" 
    using \<open>\<forall>a1\<in>F. \<forall>a2\<in>F. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}\<close> \<open>\<forall>a\<in>F. \<exists>b1\<in>B - {b}. b1 \<in> a\<close> \<open>finite (B - {b})\<close> insert.hyps(3) by presburger
  then  obtain C where "C\<subseteq>(B - {b}) \<and> (\<forall>a\<in>F. \<exists>b\<in>C. b \<in> a)  \<and> card F = card C"

    by (metis card.empty empty_subsetI finite_has_maximal insert.hyps(1))
  then have "(C \<union> {b}) \<subseteq> B" 
    using \<open>b \<in> B \<and> b \<in> x\<close> by blast
  have "\<forall>a\<in>insert x F. \<exists>b\<in> (C \<union> {b}). b \<in> a" 
    using \<open>C \<subseteq> B - {b} \<and> (\<forall>a\<in>F. \<exists>b\<in>C. b \<in> a) \<and> card F = card C\<close> \<open>b \<in> B \<and> b \<in> x\<close> by blast
  have "card F = card C" 
    by (simp add: \<open>C \<subseteq> B - {b} \<and> (\<forall>a\<in>F. \<exists>b\<in>C. b \<in> a) \<and> card F = card C\<close>)

  have "card (insert x F) = card C + 1" 
    by (simp add: \<open>card F = card C\<close> insert.hyps(1) insert.hyps(2))

  then show ?case 
    by (metis Un_insert_right \<open>C \<subseteq> B - {b} \<and> (\<forall>a\<in>F. \<exists>b\<in>C. b \<in> a) \<and> card F = card C\<close> \<open>C \<union> {b} \<subseteq> B\<close> \<open>\<forall>a\<in>insert x F. \<exists>b\<in>C \<union> {b}. b \<in> a\<close> \<open>finite (B - {b})\<close> boolean_algebra_cancel.sup0 card.insert finite_subset insert.hyps(1) insert.hyps(2) subset_Diff_insert)
qed

lemma yfsdf1:
  assumes "finite A"
  assumes "finite B"
  assumes "\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
  assumes "\<forall>a\<in>A. \<exists>b\<in>B. b \<in> a"
  shows "\<exists>C\<subseteq>B . \<forall>a\<in>A. \<exists>!b\<in>C. b \<in> a"
  using assms(1) assms(2) assms(3) assms(4)
proof(induct A arbitrary: B)
  case empty
  then show ?case by auto
next
  case (insert x F)
  have "\<forall>a1\<in>F. \<forall>a2\<in>F. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"

    by (simp add: insert.prems(2))
  have "\<exists>b\<in>B. b \<in> x" 
    by (simp add: insert.prems(3))
  then obtain b where "b \<in> B \<and> b \<in> x" by auto
  then have " \<forall>a\<in>F. b \<notin> a" 
    using UnionI insert.hyps(2) insert.prems(2) by auto
  then have " \<forall>a\<in>F. \<exists>b1\<in>B. b1 \<in> a \<and> b1 \<noteq> b" 
    using insert.prems(3)
    by (metis insert_iff)
  then have " \<forall>a\<in>F. \<exists>b1\<in>B. b1 \<in> a \<and> b1 \<notin> x" 
    using insert.hyps(2) insert.prems(2) by fastforce 


  then have "\<forall>a\<in>F. \<exists>b1\<in>B-x. b1 \<in> a" 
    by (meson DiffI)
  have "finite (B - x)" 
    using insert.prems(1) by blast
  then have "\<exists>C\<subseteq> (B - x) . \<forall>a\<in>F. \<exists>!b. b \<in> C \<and>  b \<in> a" 
    using \<open>\<forall>a1\<in>F. \<forall>a2\<in>F. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}\<close> \<open>\<forall>a\<in>F. \<exists>b1\<in>B - x. b1 \<in> a\<close> insert.hyps(3) by presburger
  then obtain C where "C\<subseteq> (B - x) \<and> ( \<forall>a\<in>F. \<exists>!b. b \<in> C \<and>  b \<in> a)" by presburger
  then have "C \<union>{b} \<subseteq> B" 
    using \<open>b \<in> B \<and> b \<in> x\<close> by blast
  have "\<forall>a\<in> F. \<exists>!b1. b1 \<in> C\<union>{b} \<and> b1 \<in> a" using `\<forall>a\<in>F. b \<notin> a` 
    using DiffD2 \<open>C \<subseteq> B - x \<and> (\<forall>a\<in>F. \<exists>!b. b \<in> C \<and> b \<in> a)\<close> by auto


  have "\<exists>!b1. b1 \<in> C\<union>{b} \<and> b1 \<in> x" 
    using \<open>C \<subseteq> B - x \<and> (\<forall>a\<in>F. \<exists>!b. b \<in> C \<and> b \<in> a)\<close> \<open>b \<in> B \<and> b \<in> x\<close> by blast
  then show ?case using `\<forall>a\<in>F. b \<notin> a` 
    by (metis \<open>C \<union> {b} \<subseteq> B\<close> \<open>\<forall>a\<in>F. \<exists>!b1. b1 \<in> C \<union> {b} \<and> b1 \<in> a\<close> insert_iff)
qed


lemma yfsdf2:
  assumes "finite A"
  assumes "finite (Vs A)"
  assumes "\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}"
  assumes "\<forall>a\<in>A. \<exists>b\<in> Vs A. b \<in> a"
  shows "\<exists>C\<subseteq> Vs A. \<forall>a\<in>A. \<exists>!b\<in>C. b \<in> a"
  by (simp add: assms(1) assms(2) assms(3) assms(4) yfsdf1)

lemma perfect_matching_union:
  assumes "finite A"
  assumes "\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> Vs a1 \<inter> Vs a2 = {}"
  assumes "\<forall>a \<in> A. \<exists>M. perfect_matching a M"
  shows "\<exists>M. perfect_matching (\<Union>A) M"
proof -
  let ?Ms = "{Ms. \<exists>a \<in> A. Ms = {M. perfect_matching a M}}"
  have "\<forall>a \<in> A.  graph_invar a"
    by (meson assms(3) perfect_matching_def)
  have "\<forall>a \<in> A. finite (Vs a)" 
    by (simp add: \<open>\<forall>a\<in>A. graph_invar a\<close>)
  have "graph_invar (\<Union>A)"
  proof
    show " \<forall>e\<in>\<Union> A. \<exists>u v. e = {u, v} \<and> u \<noteq> v" 
      using \<open>\<forall>a\<in>A. graph_invar a\<close> by fastforce
    show "finite (Vs (\<Union> A))" using `\<forall>a \<in> A. finite (Vs a)` assms(1)  
      by (metis Vs_def \<open>\<forall>e\<in>\<Union> A. \<exists>u v. e = {u, v} \<and> u \<noteq> v\<close> finite.simps finite_Union finite_UnionD)
  qed

  have disjoint_edges:"\<forall>a1 \<in>A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}" 
    by (metis \<open>\<forall>a\<in>A. graph_invar a\<close> assms(2) disjoint_iff_not_equal edges_are_Vs)


  let ?f = "(\<lambda>a. {{M. perfect_matching a M}})"
  have "?Ms = (\<Union>a\<in>A. ?f a)" by blast
  have "finite (\<Union>a\<in>A. ?f a)" using assms(1) 
    by blast
  then have "finite ?Ms" using assms(1)
    by simp
  have "\<forall>a \<in> A. {M. perfect_matching a M} \<subseteq> {a1. a1 \<subseteq> a}" 
    by (simp add: Collect_mono perfect_matching_def)

  then have "\<forall>a \<in> A. finite {M. perfect_matching a M}"
    by (metis Vs_def \<open>\<forall>a\<in>A. finite (Vs a)\<close> finite_Collect_subsets finite_UnionD finite_subset)
  then have "finite (Vs ?Ms)"
    by (smt (verit) Vs_def \<open>finite ?Ms\<close> finite_Union mem_Collect_eq)
  have "\<forall>a1 \<in> A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> {a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2} = {{}}"
  proof
    fix a1
    assume "a1 \<in> A"
    show "\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> {a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2} = {{}}"
    proof
      fix a2
      assume "a2 \<in> A"
      show "a1 \<noteq> a2 \<longrightarrow> {a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2} = {{}}"
      proof
        assume "a1 \<noteq> a2" 
        have "a1 \<inter> a2 = {}"
          using `a1 \<in> A` `a2 \<in> A` `a1 \<noteq> a2` disjoint_edges
          by auto
        show "{a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2} = {{}}"
        proof(rule ccontr)
          assume "{a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2} \<noteq> {{}}"
          have "{} \<in> {a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2}" 
            by simp
          then have "{{}} \<subset>  {a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2}"

            by (metis \<open>{a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2} \<noteq> {{}}\<close> empty_subsetI insert_subsetI psubsetI)
          then have "\<exists>a. a \<in> {a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2} \<and> a \<noteq> {}"

            by force
          then obtain a where "a \<in> {a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2} \<and> a \<noteq> {}" by auto
          then have "\<exists>x \<in> a. x \<in> a1 \<and> x \<in> a2" 
            using Int_Collect by blast
          then show False 
            using \<open>a1 \<inter> a2 = {}\<close> by blast
        qed
      qed
    qed
  qed
  have "\<forall>a1 \<in> A.\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow>
     {M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M} = {}" 
  proof 
    fix a1
    assume "a1 \<in> A"
    show "\<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow>
     {M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M} = {}"
    proof
      fix a2
      assume "a2 \<in> A"
      show "a1 \<noteq> a2 \<longrightarrow>
     {M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M} = {}"
      proof
        assume "a1 \<noteq> a2" 
        have "a1 \<inter> a2 = {}"
          using `a1 \<in> A` `a2 \<in> A` `a1 \<noteq> a2` disjoint_edges
          by auto
        have "{M. perfect_matching a1 M} \<subseteq> {a. a \<subseteq> a1}" 
          by (simp add: Collect_mono perfect_matching_def)
        have "{M. perfect_matching a2 M} \<subseteq> {a. a \<subseteq> a2}" 
          by (simp add: Collect_mono perfect_matching_def)
        then have "{M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M}
            \<subseteq> {a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2}" 
          using \<open>{M. perfect_matching a1 M} \<subseteq> {a. a \<subseteq> a1}\<close> inf_mono by blast
        then have "{M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M} \<subseteq> {{}}"

          by (simp add: \<open>\<forall>a1\<in>A. \<forall>a2\<in>A. a1 \<noteq> a2 \<longrightarrow> {a. a \<subseteq> a1} \<inter> {a. a \<subseteq> a2} = {{}}\<close> \<open>a1 \<in> A\<close> \<open>a1 \<noteq> a2\<close> \<open>a2 \<in> A\<close>)
        have "a1 \<noteq> {} \<or> a2 \<noteq> {}" 
          using \<open>a1 \<noteq> a2\<close> by blast

        have "{} \<notin> {M. perfect_matching a1 M} \<or> {} \<notin> {M. perfect_matching a2 M}"
        proof(rule ccontr)
          assume " \<not> ({} \<notin> {M. perfect_matching a1 M} \<or> {} \<notin> {M. perfect_matching a2 M})"
          then have "{} \<in> {M. perfect_matching a1 M} \<and> {} \<in> {M. perfect_matching a2 M}" by auto
          then have "perfect_matching a1 {}" by auto
          then have "a1 = {}" unfolding perfect_matching_def 
            by (metis edges_are_Vs ex_in_conv matching_def2)
          then have "perfect_matching a2 {}" 
            using \<open>\<not> ({} \<notin> {M. perfect_matching a1 M} \<or> {} \<notin> {M. perfect_matching a2 M})\<close> by blast
          then have "a2 = {}" unfolding perfect_matching_def 
            by (metis edges_are_Vs ex_in_conv matching_def2)
          then show False 
            using \<open>a1 = {}\<close> \<open>a1 \<noteq> {} \<or> a2 \<noteq> {}\<close> by auto
        qed
        then have "{} \<notin> {M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M}"

          by blast
        then show "{M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M} = {}"

          using \<open>{M. perfect_matching a1 M} \<inter> {M. perfect_matching a2 M} \<subseteq> {{}}\<close> by auto
      qed
    qed
  qed
  then have "\<forall>a1 \<in> ?Ms.\<forall>a2\<in>?Ms. a1 \<noteq> a2 \<longrightarrow>
     a1 \<inter> a2 = {}" 
    by force
  have "\<forall>a\<in> ?Ms. \<exists>b\<in> Vs ?Ms. b \<in> a" 
    by (smt (z3) assms(3) mem_Collect_eq vs_member_intro)



  then  have "\<exists>C\<subseteq> Vs ?Ms. \<forall>Ms\<in> ?Ms. \<exists>!M\<in>C. M \<in> Ms" using yfsdf2[of ?Ms]
    using \<open>\<forall>a1\<in>{Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}}. \<forall>a2\<in>{Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}}. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}\<close> \<open>finite (Vs {Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}})\<close> \<open>finite {Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}}\<close> by fastforce
  then obtain C where "C\<subseteq> Vs ?Ms \<and> (\<forall>Ms\<in> ?Ms. \<exists>!M\<in>C. M \<in> Ms)" by auto
  have "\<forall>c \<in>C. matching c"
  proof
    fix c
    assume "c \<in>  C"
    then have "c \<in> Vs ?Ms" 
      using \<open>C \<subseteq> Vs {Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}} \<and> (\<forall>Ms\<in>{Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}}. \<exists>!M. M \<in> C \<and> M \<in> Ms)\<close> by blast
    then have "\<exists>a\<in>A. perfect_matching a c" 
      by (smt (verit, best) mem_Collect_eq vs_member)
    then show " matching c" unfolding perfect_matching_def by auto
  qed

  have "matching (\<Union>C)" unfolding matching_def
  proof
    fix e1
    assume "e1 \<in> (\<Union>C)"
    then have "\<exists>c1\<in>C. e1 \<in> c1" by auto
    then obtain c1 where "c1\<in>C \<and> e1 \<in> c1" by auto
    show " \<forall>e2\<in>\<Union> C. e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {}"
    proof
      fix e2
      assume "e2\<in>\<Union> C"
      then have "\<exists>c2\<in>C. e2 \<in> c2" by auto
      then obtain c2 where "c2\<in>C \<and> e2 \<in> c2" by auto
      show "e1 \<noteq> e2 \<longrightarrow> e1 \<inter> e2 = {}"
      proof
        assume "e1 \<noteq> e2"
        show "e1 \<inter> e2 = {}"
        proof(cases "c1 = c2")
          case True
          have "matching c1" 
            by (simp add: \<open>\<forall>c\<in>C. matching c\<close> \<open>c1 \<in> C \<and> e1 \<in> c1\<close>)
          then show ?thesis 
            by (metis True \<open>c1 \<in> C \<and> e1 \<in> c1\<close> \<open>c2 \<in> C \<and> e2 \<in> c2\<close> \<open>e1 \<noteq> e2\<close> matching_def)
        next
          case False
          have "c1 \<in> Vs ?Ms" using `c1 \<in> C \<and> e1 \<in> c1`
            using \<open>C \<subseteq> Vs {Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}} \<and> (\<forall>Ms\<in>{Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}}. \<exists>!M. M \<in> C \<and> M \<in> Ms)\<close> by blast

          then have "\<exists>a1\<in>A. perfect_matching a1 c1" 
            by (smt (verit, best) mem_Collect_eq vs_member)
          then obtain a1 where "a1\<in>A \<and> perfect_matching a1 c1" by blast


          have "c2 \<in> Vs ?Ms" using `c2 \<in> C \<and> e2 \<in> c2`
            using \<open>C \<subseteq> Vs {Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}} \<and> (\<forall>Ms\<in>{Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}}. \<exists>!M. M \<in> C \<and> M \<in> Ms)\<close> by blast

          then have "\<exists>a2\<in>A. perfect_matching a2 c2" 
            by (smt (verit, best) mem_Collect_eq vs_member)
          then obtain a2 where "a2\<in>A \<and> perfect_matching a2 c2" by blast
          have "a1 \<noteq> a2"
          proof(rule ccontr)
            assume "\<not> a1 \<noteq> a2"
            then have "a1 = a2" by auto
            have "(\<exists>!M\<in>C. M \<in> {M. perfect_matching a1 M})" 
              using \<open>C \<subseteq> Vs {Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}} \<and> (\<forall>Ms\<in>{Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}}. \<exists>!M. M \<in> C \<and> M \<in> Ms)\<close> \<open>\<not> a1 \<noteq> a2\<close> \<open>a2 \<in> A \<and> perfect_matching a2 c2\<close> \<open>c2 \<in> C \<and> e2 \<in> c2\<close> by auto
            then have "c1 = c2" 
              using \<open>a1 = a2\<close> \<open>a1 \<in> A \<and> perfect_matching a1 c1\<close> \<open>a2 \<in> A \<and> perfect_matching a2 c2\<close> \<open>c1 \<in> C \<and> e1 \<in> c1\<close> \<open>c2 \<in> C \<and> e2 \<in> c2\<close> by blast
            then show False 
              using False by auto
          qed
          have "a1 \<inter> a2 = {}" 
            by (simp add: \<open>a1 \<in> A \<and> perfect_matching a1 c1\<close> \<open>a1 \<noteq> a2\<close> \<open>a2 \<in> A \<and> perfect_matching a2 c2\<close> disjoint_edges)
          have "c1 \<subseteq> a1 \<and> c2 \<subseteq> a2" 
            using \<open>a1 \<in> A \<and> perfect_matching a1 c1\<close> \<open>a2 \<in> A \<and> perfect_matching a2 c2\<close> perfect_matching_def by blast
          have "c1 \<inter> c2 = {}" 
            using \<open>a1 \<inter> a2 = {}\<close> \<open>c1 \<subseteq> a1 \<and> c2 \<subseteq> a2\<close> by blast
          then show ?thesis 
            by (metis \<open>a1 \<in> A \<and> perfect_matching a1 c1\<close> \<open>a1 \<noteq> a2\<close> \<open>a2 \<in> A \<and> perfect_matching a2 c2\<close> \<open>c1 \<in> C \<and> e1 \<in> c1\<close> \<open>c2 \<in> C \<and> e2 \<in> c2\<close> assms(2) disjoint_iff_not_equal perfect_matching_def vs_member_intro)
        qed
      qed
    qed
  qed
  have "\<Union>C \<subseteq> \<Union>A"
  proof
    fix x
    assume "x \<in> \<Union>C"
    then have "\<exists>c\<in>C. x \<in> c" by auto
    then obtain c where "c\<in>C \<and> x \<in> c" by auto
    then have "c \<in> Vs ?Ms" 
      using \<open>C \<subseteq> Vs {Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}} \<and> (\<forall>Ms\<in>{Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}}. \<exists>!M. M \<in> C \<and> M \<in> Ms)\<close> by blast

    then have "\<exists>a1\<in>A. perfect_matching a1 c" 
      by (smt (verit, best) mem_Collect_eq vs_member)
    then obtain a where "a\<in>A \<and> perfect_matching a c" by blast
    then have "c \<subseteq> a" unfolding perfect_matching_def by auto
    then have "x \<in> a" 
      using \<open>c \<in> C \<and> x \<in> c\<close> by blast
    then show "x \<in> \<Union>A" 
      using \<open>a \<in> A \<and> perfect_matching a c\<close> by blast
  qed
  have "Vs (\<Union>C) = Vs (\<Union>A)"
  proof(safe)
    {
      fix x
      assume " x \<in> Vs (\<Union> C)"
      then have "\<exists>e \<in> (\<Union> C). x \<in> e" 
        by (meson vs_member_elim)
      then obtain e where "e \<in> (\<Union> C) \<and> x \<in> e" by auto
      then have "\<exists>c\<in>C. e \<in> c" by auto
      then obtain c where "c\<in>C \<and> e \<in> c" by auto
      then have "c \<in> Vs ?Ms" 
        using \<open>C \<subseteq> Vs {Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}} \<and> (\<forall>Ms\<in>{Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}}. \<exists>!M. M \<in> C \<and> M \<in> Ms)\<close> by blast

      then have "\<exists>a1\<in>A. perfect_matching a1 c" 
        by (smt (verit, best) mem_Collect_eq vs_member)
      then obtain a where "a\<in>A \<and> perfect_matching a c" by blast
      then have "c \<subseteq> a" unfolding perfect_matching_def by auto
      then have "e \<in> a" 
        using \<open>c \<in> C \<and> e \<in> c\<close> by blast
      then have "e \<in> \<Union>A"  using \<open>a \<in> A \<and> perfect_matching a c\<close> by blast
      then show "x \<in> Vs (\<Union> A)" 
        by (meson \<open>e \<in> \<Union> C \<and> x \<in> e\<close> vs_member_intro)
    }
    fix x 
    assume "x \<in> Vs (\<Union> A)"
    then have "\<exists>e \<in> (\<Union> A). x \<in> e" 
      by (meson vs_member_elim)
    then obtain e where "e \<in> (\<Union> A) \<and> x \<in> e" by auto
    then have "\<exists>a \<in>A. e \<in> a" 
      by blast
    then obtain a where "a \<in>A \<and> e \<in> a" by auto
    then have "\<exists>c \<in> C. perfect_matching a c" 
      by (metis (mono_tags, lifting) \<open>C \<subseteq> Vs {Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}} \<and> (\<forall>Ms\<in>{Ms. \<exists>a\<in>A. Ms = {M. perfect_matching a M}}. \<exists>!M. M \<in> C \<and> M \<in> Ms)\<close> mem_Collect_eq)
    then obtain c where "c \<in> C \<and> perfect_matching a c" by auto
    then have "Vs a =  Vs c" unfolding perfect_matching_def by auto
    then have "x \<in> Vs c" 
      using \<open>a \<in> A \<and> e \<in> a\<close> \<open>e \<in> \<Union> A \<and> x \<in> e\<close> by blast 
    then show "x \<in> Vs (\<Union> C)" 
      by (metis Vs_def \<open>c \<in> C \<and> perfect_matching a c\<close> vs_member)
  qed
  then have "perfect_matching (\<Union> A) (\<Union> C)" unfolding perfect_matching_def
    using \<open>\<Union> C \<subseteq> \<Union> A\<close> \<open>graph_invar (\<Union> A)\<close> \<open>matching (\<Union> C)\<close> by blast
  then show ?thesis by auto
qed

lemma odd_components_in_tutte_graph:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  shows "(diff_odd_components E {}) = {}"
proof -
  have "(graph_diff E {}) = E" unfolding graph_diff_def by auto
  have "finite (diff_odd_components E {})" unfolding diff_odd_components_def
  proof(safe)
    have "finite (connected_components E)" 
      by (simp add: assms(1) finite_con_comps)

    then have "finite (odd_components E)" unfolding odd_components_def 
      using assms(1) by auto
    show "finite
     (odd_components
       (graph_diff E {}))" unfolding odd_components_def 
      by (metis  \<open>finite (odd_components E)\<close> \<open>graph_diff E {} = E\<close> odd_components_def)
    show "finite (singleton_in_diff E {})" unfolding singleton_in_diff_def  
      by (simp add: \<open>graph_diff E {} = E\<close>)
  qed
  have "{} \<subseteq> E" by auto
  then have "card (diff_odd_components E {}) \<le> card {}" using assms(2) 
    unfolding tutte_condition_def
    by (metis bot.extremum card.empty)
  then have "card (diff_odd_components E {}) = 0" 
    by simp
  then show ?thesis 
    by (meson \<open>finite (diff_odd_components E {})\<close> card_0_eq)
qed

lemma odd_components_nonempty:
  assumes "graph_invar E"
  shows "\<forall>C \<in> (diff_odd_components E X). C \<noteq> {}"
proof
  fix C
  assume "C \<in> (diff_odd_components E X)"
  show "C \<noteq> {}"
  proof(cases "C \<in> (odd_components (graph_diff E X))")
    case True
    then show ?thesis 
      using odd_components_def by fastforce
  next
    case False
    have "C \<in> (singleton_in_diff E X)" 
      by (metis False UnE \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_def)
    then show ?thesis unfolding singleton_in_diff_def
      by blast
  qed
qed

lemma odd_components_subset_vertices:
  assumes "graph_invar E"
  assumes "X \<subseteq> Vs E"
  shows "\<forall>C \<in> (diff_odd_components E X). C \<subseteq> Vs E"
proof
  fix C
  assume "C \<in> (diff_odd_components E X)"
  show "C \<subseteq> Vs E" 
    by (meson \<open>C \<in> diff_odd_components E X\<close> component_in_E)
qed

lemma graph_diff_empty:
  assumes "graph_invar E"
  shows "E = graph_diff E {}" 
  unfolding graph_diff_def by auto

lemma diff_odd_components_is_component:
  assumes "graph_invar E"
  shows "\<forall>C \<in> (diff_odd_components E X). \<forall>x \<in> C. connected_component (graph_diff E X) x = C"
proof
  fix C
  assume "C \<in> (diff_odd_components E X)"
  show " \<forall>x\<in>C. connected_component (graph_diff E X) x = C"
  proof
    fix x
    assume "x \<in> C"

    show "connected_component (graph_diff E X) x = C"
    proof(cases "C \<in> (odd_components (graph_diff E X))")
      case True
      then show ?thesis 
        using odd_components_def 
        by (smt (verit, best) \<open>x \<in> C\<close> connected_components_member_eq mem_Collect_eq)
    next
      case False
      have "C \<in> (singleton_in_diff E X)" 
        by (metis False UnE \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_def)
      then show ?thesis unfolding singleton_in_diff_def 
        using \<open> x \<in> C\<close> connected_components_notE_singletons by fastforce
    qed
  qed
qed

lemma vertices_edges_in_same_component:
  assumes "{x, y} \<in> E"
  shows "y \<in> connected_component E x"
  by (meson assms(1) edges_are_walks has_path_in_connected_component)

lemma diff_odd_components_connected:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  assumes "X \<subseteq> Vs E"
  shows "\<forall>C \<in> (diff_odd_components E X). \<exists>x y. x \<in> C \<and> y \<in> X \<and> {x, y} \<in> E"
proof
  fix C
  assume "C \<in> (diff_odd_components E X)"
  then have "\<exists>x \<in> Vs E. x \<in> C" using component_in_E[of C E X]
    by (metis assms(1) assms(3) odd_components_nonempty subset_empty subset_eq)
  then obtain x where "x \<in> Vs E \<and> x \<in> C" by auto
  then have "connected_component (graph_diff E X) x = C"
    using diff_odd_components_is_component[of E X] assms(1) assms(2) 
    using \<open>C \<in> diff_odd_components E X\<close> assms(3) by fastforce

  show "\<exists>x y. x \<in> C \<and> y \<in> X \<and> {x, y} \<in> E" 
  proof(rule ccontr)
    assume " \<nexists>x y. x \<in> C \<and> y \<in> X \<and> {x, y} \<in> E"

    then have "\<forall>x y. {x, y} \<in> E \<and> x \<in> C  \<longrightarrow> y \<notin> X"
      by blast
    then have "\<forall>x y. {x, y} \<in> E \<and> x \<in> C \<longrightarrow> {x, y} \<in> graph_diff E X"
      unfolding graph_diff_def
      using \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_not_in_X mem_Collect_eq by fastforce
    then have "\<forall>x y. {x, y} \<in> E \<and> x \<in> C \<longrightarrow> y \<in> connected_component (graph_diff E X) x" 
      by (meson edges_are_walks has_path_in_connected_component)
    then have "\<forall>x y. {x, y} \<in> E \<and> x \<in> C \<longrightarrow> y \<in> C" 
      by (metis \<open>connected_component (graph_diff E X) x = C\<close> connected_components_member_eq)
    have "connected_component E x = C"
    proof(safe)
      {
        fix y
        assume "y \<in> connected_component E x"
        show "y \<in> C"
        proof(cases "x = y")
          case True
          then show ?thesis 
            using \<open>x \<in> Vs E \<and> x \<in> C\<close> by auto
        next
          case False

          then have "(\<exists>p. walk_betw E y p x)" using `y \<in> connected_component E x`
            by (metis connected_components_member_sym in_con_comp_has_walk )

          then obtain p where p_walk:"walk_betw E y p x" by auto
          then have "last p = x" 
            by fastforce
          then have "path E p" using p_walk unfolding walk_betw_def  by auto

          then have "\<forall>z \<in> set p. z \<in> C" using `last p = x`
          proof(induct p) 
            case path0
            then show ?case 
              by auto
          next
            case (path1 v)
            then show ?case
              by (metis \<open>x \<in> Vs E \<and> x \<in> C\<close> empty_iff empty_set last_ConsL set_ConsD)
          next
            case (path2 v v' vs)
            have "last (v' # vs) = x" 
              using path2.prems by force
            have "\<forall>z\<in>set (v' # vs). z \<in> C" 
              using \<open>last (v' # vs) = x\<close> path2.hyps(3) by blast
            have "{v, v'} \<in> E" 
              by (simp add: path2.hyps(1))
            then have "v \<in> C" 
              by (metis \<open>\<forall>x y. {x, y} \<in> E \<and> x \<in> C \<longrightarrow> y \<in> C\<close> \<open>\<forall>z\<in>set (v' # vs). z \<in> C\<close> insert_commute list.set_intros(1))
            then show ?case 
              by (metis \<open>\<forall>z\<in>set (v' # vs). z \<in> C\<close> set_ConsD)
          qed
          then show "y \<in> C" 
            by (metis list.set_sel(1) p_walk walk_betw_def)
        qed
      }
      fix y
      assume "y \<in> C"
      then show "y \<in> connected_component E x" 
        by (metis \<open>connected_component (graph_diff E X) x = C\<close> con_comp_subset graph_diff_subset insert_absorb insert_subset)
    qed
    have "C \<in> (diff_odd_components E {})"
    proof(cases "C \<in> (odd_components (graph_diff E X))")
      case True 
      then have "odd (card C)" unfolding odd_components_def 
        by blast
      then have "C \<in> (odd_components E)" 
        using \<open>connected_component E x = C\<close> \<open>x \<in> Vs E \<and> x \<in> C\<close> odd_components_def by auto
      then have "C \<in> (odd_components (graph_diff E {}))"
        using graph_diff_empty using assms(1) by fastforce
      then show ?thesis
        by (simp add: diff_odd_components_def)

    next
      case False
      have "C \<in>(singleton_in_diff E X)" 
        by (metis False UnE \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_def)
      then show ?thesis 
        by (smt (verit, ccfv_threshold) \<open>\<forall>x y. {x, y} \<in> E \<and> x \<in> C \<longrightarrow> {x, y} \<in> graph_diff E X\<close> assms(1) empty_iff insert_commute insert_iff mem_Collect_eq singleton_in_diff_def vs_member)
    qed
    then show False 
      by (simp add: assms(1) assms(2) odd_components_in_tutte_graph)
  qed
qed

lemma empty_graph_odd_components:
  shows "diff_odd_components {} X = {}"
  unfolding diff_odd_components_def
proof
  have "graph_diff {} X = {}" 
    using graph_diff_subset by auto
  then have "odd_components (graph_diff {} X) = {}" unfolding odd_components_def 
    using vs_member by fastforce
  have " singleton_in_diff {} X = {}" unfolding singleton_in_diff_def 
    using vs_member 
    using \<open>graph_diff {} X = {}\<close> by auto
  then show "odd_components
     (graph_diff {} X) =
    {} \<and>
    singleton_in_diff {} X = {}" 
    by (simp add: \<open>odd_components (graph_diff {} X) = {}\<close>)
qed


lemma add_subset_change_odd_components:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  assumes "X \<subseteq> Vs E"
  assumes "C \<in> (diff_odd_components E X)"
  assumes "Y \<subseteq> C"
  assumes "Y \<noteq> {}"
  shows "diff_odd_components E (X\<union>Y) = ((diff_odd_components E X) - {C}) \<union>
    diff_odd_components (component_edges (graph_diff E X) C) Y"
proof(cases "C\<in> singleton_in_diff E X")
  case True
  then have "C = Y" unfolding singleton_in_diff_def
    using assms(5) assms(6) by blast
  have "\<exists> v. C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)"
    using `C\<in> singleton_in_diff E X` unfolding singleton_in_diff_def 
    by fastforce
  then obtain x where "C = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)" by auto
  then have "Y = {x}" 
    by (simp add: \<open>C = Y\<close>)
  have "x \<notin> Vs (graph_diff E X)" 
    using \<open>C = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)\<close> by blast

  then have "(graph_diff E X) = (graph_diff E (X\<union>{x}))" unfolding graph_diff_def   
    by blast

  then have "(odd_components (graph_diff E X)) = (odd_components (graph_diff E (X\<union>{x})))"
    by auto
  have "(singleton_in_diff E X) - {{x}} = singleton_in_diff E (X \<union> {x})"
  proof
    show " singleton_in_diff E X - {{x}}
    \<subseteq> singleton_in_diff E (X \<union> {x})"
    proof
      fix C'
      assume "C' \<in> singleton_in_diff E X - {{x}}"
      then have "\<exists>v. C' = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)"
        unfolding singleton_in_diff_def 
        by blast
      then obtain v where "C' = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)"
        by auto
      have "v \<notin> {x}" 
        using \<open>C' = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)\<close> \<open>C' \<in> singleton_in_diff E X - {{x}}\<close> by blast
      then have "C' = {v} \<and> v \<in> Vs E \<and> v \<notin> (X\<union>{x}) \<and> v \<notin> Vs (graph_diff E X)" 
        by (simp add: \<open>C' = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)\<close>)
      then have "C' = {v} \<and> v \<in> Vs E \<and> v \<notin> (X\<union>{x}) \<and> v \<notin> Vs (graph_diff E (X\<union>{x}))"

        by (simp add: \<open>graph_diff E X = graph_diff E (X \<union> {x})\<close>)
      then show "C' \<in> singleton_in_diff E (X \<union> {x})" unfolding singleton_in_diff_def 
        by simp
    qed
    show "singleton_in_diff E (X \<union> {x})
    \<subseteq> singleton_in_diff E X - {{x}}" unfolding singleton_in_diff_def 
      using \<open>graph_diff E X = graph_diff E (X \<union> {x})\<close> by force
  qed
  then have "diff_odd_components E (X\<union>{x}) = ((diff_odd_components E X) - {C})" 

    by (smt (z3) Diff_empty Diff_insert0 Un_Diff \<open>C = Y\<close> \<open>C = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)\<close> \<open>graph_diff E X = graph_diff E (X \<union> {x})\<close> assms(6) diff_odd_components_def diff_odd_components_not_in_X inf_sup_absorb insert_Diff insert_Diff_single sup_commute)
  then have "diff_odd_components E (X\<union>Y) = ((diff_odd_components E X) - {C})" 
    using \<open>C = Y\<close> \<open>C = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)\<close> by fastforce
  have " (component_edges (graph_diff E X) C) = {}" 
    by (smt (verit, del_insts) \<open>C = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)\<close> component_edges_def empty_Collect_eq insert_not_empty insert_subset subset_singleton_iff vs_member)
  then have " diff_odd_components (component_edges (graph_diff E X) C) Y = {}" 
    by (simp add: empty_graph_odd_components)

  then show ?thesis unfolding diff_odd_components_def  
    by (metis \<open>diff_odd_components E (X \<union> Y) = diff_odd_components E X - {C}\<close> diff_odd_components_def sup_bot_right)
next
  case False
  then have "C \<in> odd_components (graph_diff E X)" 
    by (metis UnE assms(4) diff_odd_components_def)
  show "diff_odd_components E (X\<union>Y) = ((diff_odd_components E X) - {C}) \<union>
    diff_odd_components (component_edges (graph_diff E X) C) Y" 
  proof
    show " diff_odd_components E (X \<union> Y)
    \<subseteq> diff_odd_components E X - {C} \<union>
       diff_odd_components (component_edges (graph_diff E X) C) Y"
    proof
      fix C'
      assume "C' \<in> diff_odd_components E (X \<union> Y)"
      then have "C' \<noteq> {}" 
        by (metis Un_subset_iff assms(1) assms(3) assms(4) assms(5) component_in_E odd_components_nonempty order_trans)
      then have "\<exists>c. c \<in> C'" 
        by blast
      then obtain c where "c \<in> C'" by auto
      then have "connected_component (graph_diff E (X \<union> Y)) c = C'"
        using diff_odd_components_is_component[of E "X \<union> Y"] 
        by (metis Un_subset_iff \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> assms(1) assms(3) assms(4) assms(5) component_in_E subset_Un_eq)

      show "C' \<in> diff_odd_components E X - {C} \<union>
              diff_odd_components (component_edges (graph_diff E X) C) Y"
      proof(cases "c \<in> C")
        case True
        then have "connected_component (graph_diff E X) c =C" 
          by (simp add: assms(1) assms(3) assms(4) diff_odd_components_is_component)
        then have "c \<in> Vs (graph_diff E X)" 
          by (smt (verit, best) IntD1 IntI True Un_Int_eq(2) Un_subset_iff \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close> assms(1) assms(3) assms(4) assms(5) assms(6) component_in_E connected_components_notE_singletons diff_disjoint_elements(2) diff_odd_components_not_in_X subset_singleton_iff)
        then have "\<exists>e. e\<in>(graph_diff E X)  \<and> c \<in> e" 
          by (meson vs_member_elim)
        then obtain e where " e\<in>(graph_diff E X)  \<and> c \<in> e" by auto
        then have "e \<subseteq> C" 
          by (metis True \<open>connected_component (graph_diff E X) c = C\<close> assms(1) assms(4) connected_components_member_sym diff_odd_components_not_in_X graph_diff_subset in_con_comp_insert inf_le1 insertE insert_Diff insert_subset singleton_iff)

        show ?thesis
        proof(cases "C'\<in> singleton_in_diff E (X \<union> Y)" )
          case True
          then have "C' = {c}" 
            by (smt (verit, ccfv_SIG) IntI Un_subset_iff \<open>c \<in> C'\<close> \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close> assms(1) assms(3) assms(4) assms(5) component_in_E connected_components_notE_singletons diff_disjoint_elements(1) empty_iff subset_Un_eq vs_member_intro)
          then have "c \<notin> Vs (graph_diff E (X\<union>Y))" 
            by (smt (verit, ccfv_threshold) True Un_subset_iff \<open>c \<in> C'\<close> assms(1) assms(3) assms(4) assms(5) component_in_E diff_disjoint_elements(1) dual_order.trans insert_Diff insert_disjoint(1) vs_member_intro)

          then have "\<nexists>e. e \<in> E \<and> c \<in> e \<and> e \<inter> (X \<union> Y) = {}"
            using graph_diff_def by auto
          have "c \<notin> Y" 
            by (metis IntD1 Un_Int_eq(2) \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> \<open>c \<in> C'\<close> diff_odd_components_not_in_X disjoint_iff_not_equal)

          have " (component_edges (graph_diff E X) C) = {e. e \<subseteq> C \<and> e \<in> (graph_diff E X)}"
            unfolding component_edges_def  
            by (metis assms(1) graph_diff_subset subset_iff)
          then have "(component_edges (graph_diff E X) C) = 
                {e. e \<subseteq> C \<and> e \<in> E \<and> e \<inter> X = {}}" 
            by (smt (verit) Collect_cong graph_diff_def mem_Collect_eq)  
          have "c \<notin> Vs (graph_diff (component_edges (graph_diff E X) C) Y)"
          proof(rule ccontr)
            assume " \<not> c \<notin> Vs (graph_diff (component_edges (graph_diff E X) C) Y)"
            then have "\<exists>e. e \<subseteq> C \<and> e \<in> E \<and> e \<inter> X = {} \<and> c \<in> e \<and> e \<inter> Y = {}" 
              by (smt (verit, best) component_edges_def graph_diff_def mem_Collect_eq vs_member_elim)
            then have "\<exists>e.  e \<in> E \<and> c \<in> e \<and> e \<inter> (X \<union> Y) = {}"
              using Un_Int_distrib by auto
            then show False 
              using \<open>\<nexists>e. e \<in> E \<and> c \<in> e \<and> e \<inter> (X \<union> Y) = {}\<close> by blast
          qed
          then have "c \<in> Vs (component_edges (graph_diff E X) C)" 
            using \<open>component_edges (graph_diff E X) C = {e. e \<subseteq> C \<and> e \<in> E \<and> e \<inter> X = {}}\<close> \<open>e \<in> graph_diff E X \<and> c \<in> e\<close> \<open>e \<subseteq> C\<close> graph_diff_def mem_Collect_eq by fastforce
          then have "{c} \<in> singleton_in_diff (component_edges (graph_diff E X) C) Y"
            unfolding singleton_in_diff_def  
            using \<open>c \<notin> Vs (graph_diff (component_edges (graph_diff E X) C) Y)\<close> \<open>c \<notin> Y\<close> by blast
          then have "C' \<in> singleton_in_diff (component_edges (graph_diff E X) C) Y" 
            by (simp add: \<open>C' = {c}\<close>)
          then have "C' \<in>  diff_odd_components (component_edges (graph_diff E X) C) Y"

            by (simp add: diff_odd_components_def)
          then show "C' \<in> diff_odd_components E X - {C} \<union>
          diff_odd_components
           (component_edges (graph_diff E X) C) Y" 
            by blast 

        next
          case False
          then have "C' \<in> odd_components (graph_diff E (X\<union> Y))" 
            by (metis UnE \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> diff_odd_components_def)
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
                  by (metis \<open>x \<in> connected_component (graph_diff E (X\<union> Y)) c\<close> connected_components_member_sym in_con_comp_has_walk)
                then obtain p where p_walk:"walk_betw (graph_diff E (X\<union> Y)) x p c" by auto
                then have "last p = c" 
                  by fastforce
                then have "path (graph_diff E (X\<union> Y)) p" using p_walk unfolding walk_betw_def  by auto

                then have "\<forall>z \<in> set p. z \<in> C' \<and> z \<in> C \<and>
       z \<in> connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c"
                  using `last p = c`
                proof(induct p)
                  case path0
                  then show ?case 
                    by auto
                next
                  case (path1 v)
                  then show ?case  
                    by (metis True \<open>c \<in> C'\<close> empty_iff empty_set in_own_connected_component last_ConsL set_ConsD)
                next
                  case (path2 v v' vs)
                  have "last (v' # vs) = c" 
                    using path2.prems 
                    by auto
                  have "\<forall>z\<in>set (v' # vs). z \<in> C' \<and>  z \<in> C \<and>
z \<in> connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c" 
                    using \<open>last (v' # vs) = c\<close> path2.hyps(3)
                    by linarith
                  have "{v, v'} \<in> (graph_diff E (X\<union>Y))" 
                    by (simp add: path2.hyps(1))
                  then have "v' \<in> connected_component (graph_diff E (X\<union>Y)) c" 

                    using \<open>C' = connected_component (graph_diff E (X \<union> Y)) c\<close> \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<in> C \<and> z \<in> connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c\<close> by auto
                  then have "v \<in> connected_component (graph_diff E (X \<union> Y)) v'"
                    by (meson connected_components_member_sym path2.hyps(1) vertices_edges_in_same_component)
                  then have "v \<in> connected_component (graph_diff E (X \<union> Y)) c"
                    by (meson \<open>v' \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> connected_components_member_trans)
                  then have "v \<in> C'" 
                    by (simp add: \<open>C' = connected_component (graph_diff E (X \<union> Y)) c\<close>)
                  have "v' \<in> C" 
                    by (simp add: \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<in> C \<and> z \<in> connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c\<close>)
                  have "{v, v'} \<inter> (X\<union>Y) = {}" 
                    using \<open>C' = connected_component (graph_diff E (X \<union> Y)) c\<close> \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> \<open>v \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> \<open>v' \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> diff_odd_components_not_in_X by auto
                  then have "{v, v'} \<inter> X = {}" 
                    by (simp add: Int_Un_distrib)
                  then have "{v, v'} \<in> (graph_diff E (X))" unfolding graph_diff_def 
                    using graph_diff_subset path2.hyps(1) by auto
                  have "connected_component (graph_diff E (X)) v' = C" 
                    by (metis \<open>connected_component (graph_diff E X) c = C\<close> \<open>v' \<in> C\<close> connected_components_member_eq)
                  then have "v \<in> C" 
                    by (meson \<open>{v, v'} \<in> graph_diff E X\<close> connected_components_member_sym vertices_edges_in_same_component)
                  then have "{v, v'} \<subseteq> C" 
                    using \<open>v' \<in> C\<close> by blast
                  then have "{v, v'} \<in> (component_edges (graph_diff E X) C)"

                    using \<open>{v, v'} \<in> graph_diff E X\<close> component_edges_def by fastforce
                  have "v' \<notin> Y" 
                    using \<open>{v, v'} \<inter> (X \<union> Y) = {}\<close> by blast

                  have "v \<notin> Y" 
                    using \<open>{v, v'} \<inter> (X \<union> Y) = {}\<close> by blast
                  then have "{v, v'} \<in> (graph_diff (component_edges (graph_diff E X) C) Y)"
                    using `{v, v'} \<in> (component_edges (graph_diff E X) C)`
                    unfolding graph_diff_def 
                    using \<open>{v, v'} \<inter> (X \<union> Y) = {}\<close> by auto
                  then have "v \<in> connected_component (graph_diff
                   (component_edges (graph_diff E X) C) Y) c" 
                    by (metis \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<in> C \<and> z \<in> connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c\<close> connected_components_member_eq connected_components_member_sym list.set_intros(1) vertices_edges_in_same_component)

                  then show ?case 
                    by (metis \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<in> C \<and> z \<in> connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c\<close> \<open>v \<in> C'\<close> \<open>v \<in> C\<close> set_ConsD)

                qed
                then show "x  \<in> connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c"

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
                  using component_edges_subset by blast
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
            using \<open>C' \<in> odd_components (graph_diff E (X \<union> Y))\<close> odd_components_def by force
          have "c \<in> Vs (graph_diff (component_edges (graph_diff E X) C) Y)"
          proof(rule ccontr)
            assume " c \<notin> Vs (graph_diff (component_edges (graph_diff E X) C) Y)"
            then have "\<nexists>e. e \<in> (component_edges (graph_diff E X) C) \<and> e \<inter> Y = {} \<and> c \<in> e"
              unfolding graph_diff_def 
              by blast
            then have "\<nexists>e. e \<in> (graph_diff E X) \<and> e \<subseteq> C \<and> e \<inter> Y = {} \<and> c \<in> e"
              unfolding component_edges_def 
              by (smt (verit, del_insts) assms(1) graph_diff_subset insert_Diff insert_subset mem_Collect_eq)
            then have "\<nexists>e. e \<in> E \<and>  e \<inter> Y = {} \<and> e \<inter> X = {} \<and> c \<in> e"
              unfolding graph_diff_def 
              by (smt (z3) Int_lower2 True \<open>connected_component (graph_diff E X) c = C\<close> assms(1) assms(5) graph_diff_def insertE insert_commute insert_subset mem_Collect_eq singleton_iff subset_trans vertices_edges_in_same_component)
            then have "\<nexists>e. e \<in> E \<and>  e \<inter> (X \<union>Y) = {}  \<and> c \<in> e" 
              by (metis Int_Un_distrib Un_empty)
            then have "c \<notin> Vs(graph_diff E (X\<union>Y))" unfolding graph_diff_def 
              by (simp add: vs_member)
            then have "{c} \<in> singleton_in_diff E (X\<union>Y)" using singleton_in_diff_def[of E "(X\<union>Y)"]

              by (smt (verit, ccfv_threshold) \<open>C' = connected_component (graph_diff E (X \<union> Y)) c\<close> \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> \<open>\<exists>c. c \<in> C'\<close> component_in_E connected_components_notE_singletons diff_odd_components_not_in_X disjoint_iff_not_equal insert_subset mem_Collect_eq singletonD)
            then have "{c} \<in> diff_odd_components E (X\<union>Y)" 
              using diff_odd_components_def by blast
            then have "{c} = connected_component (graph_diff E (X \<union> Y)) c" 

              by (simp add: \<open>c \<notin> Vs (graph_diff E (X \<union> Y))\<close> connected_components_notE_singletons)
            then have "C' \<in> singleton_in_diff E (X\<union>Y)" 
              using \<open>C' = connected_component (graph_diff E (X \<union> Y)) c\<close> \<open>{c} \<in> singleton_in_diff E (X \<union> Y)\<close> by auto
            then show False 
              by (simp add: False)
          qed
          then have "C' \<in> odd_components (graph_diff (component_edges (graph_diff E X) C) Y)"
            unfolding odd_components_def 
            using \<open>connected_component (graph_diff (component_edges (graph_diff E X) C) Y) c = C'\<close> \<open>odd (card C')\<close> by blast

          then show "  C' \<in> diff_odd_components E X - {C} \<union>
          diff_odd_components
           (component_edges (graph_diff E X) C) Y" 
            by (simp add: diff_odd_components_def)

        qed

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
                  using assms(5) by blast
                have "v' \<notin> Y" 
                  by (meson \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E X) c\<close> assms(5) list.set_intros(1) subsetD)
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
            by (smt (verit, ccfv_SIG) IntI Un_subset_iff \<open>c \<in> C'\<close> \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close> assms(1) assms(3) assms(4) assms(5) component_in_E connected_components_notE_singletons diff_disjoint_elements(1) empty_iff sup.absorb_iff1 vs_member_intro)
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
            using \<open>C' = {c}\<close> \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> component_in_E diff_odd_components_not_in_X by fastforce
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

              using \<open>C' \<in> diff_odd_components E (X \<union> Y)\<close> \<open>c \<notin> Vs (graph_diff E (X \<union> Y))\<close> \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close> component_in_E connected_components_notE_singletons by fastforce
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
          by (metis DiffD1 True assms(1) assms(4) diff_component_disjoint)
        have "C' \<in> diff_odd_components E X" 
          using True by auto
        have "C' \<noteq> {}" 
          using \<open>C' \<in> diff_odd_components E X\<close> assms(1) assms(3) odd_components_nonempty by auto
        then obtain c where "c \<in> C'" by blast
        then have "connected_component (graph_diff E X) c = C'" 
          by (simp add: \<open>C' \<in> diff_odd_components E X\<close> assms(1) assms(3) diff_odd_components_is_component)
        have "c \<notin> C" 
          by (metis IntI \<open>C' \<in> diff_odd_components E X\<close> \<open>C' \<noteq> C\<close> \<open>c \<in> C'\<close> assms(1) assms(4) diff_component_disjoint empty_iff)

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
                  using assms(5) by blast
                have "v' \<notin> Y" 
                  using \<open>\<forall>z\<in>set (v' # vs). z \<in> C' \<and> z \<notin> C \<and> z \<in> connected_component (graph_diff E (X \<union> Y)) c\<close> assms(5) by auto
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
            by (smt (verit) IntI \<open>c \<in> C'\<close> \<open>connected_component (graph_diff E X) c = C'\<close> assms(1) assms(3) connected_components_notE_singletons diff_disjoint_elements(1) empty_iff vs_member_intro)
          then have "connected_component (graph_diff E (X\<union>Y)) c = {c}" 
            by (simp add: \<open>connected_component (graph_diff E (X \<union> Y)) c = C'\<close>)
          then have "c \<notin>  Vs (graph_diff E X)"
            by (smt (verit, ccfv_SIG) IntI True \<open>c \<in> C'\<close> assms(1) assms(3) diff_disjoint_elements(1) empty_iff vs_member_intro)
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
            by (metis IntI Un_iff \<open>C' \<in> diff_odd_components E X\<close> \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> assms(5) diff_odd_components_not_in_X empty_iff subsetD)
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
            by (metis IntI Un_iff \<open>C' \<in> diff_odd_components E X\<close> \<open>c \<in> C'\<close> \<open>c \<notin> C\<close> assms(5) diff_odd_components_not_in_X empty_iff subsetD)
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
            using \<open>C' \<inter> C = {}\<close> assms(5) by blast
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
          by (meson Vs_subset assms(1) component_edges_subset finite_subset graph_diff_subset subset_eq)
        have "C' \<subseteq> Vs ?C" 
          by (meson \<open>C' \<in> diff_odd_components (component_edges (graph_diff E X) C) Y\<close> component_in_E)
        have "Vs ?C \<subseteq> C" unfolding component_edges_def  
          by (smt (verit, ccfv_SIG) mem_Collect_eq subset_eq vs_member)
        then have "C' \<subseteq> C" 
          using \<open>C' \<subseteq> Vs (component_edges (graph_diff E X) C)\<close> by auto
        have "C' \<inter> Y = {}" 
          using \<open>C' \<in> diff_odd_components (component_edges (graph_diff E X) C) Y\<close> diff_odd_components_not_in_X by auto

        then have "C' \<noteq> {}" using odd_components_nonempty[of ?C Y]  
          using \<open>C' \<in> diff_odd_components ?C Y\<close> `graph_invar ?C` by fastforce
        then obtain c where "c \<in> C'"
          by blast
        then have "connected_component (graph_diff ?C Y) c = C'"
          using diff_odd_components_is_component[of ?C Y]
          using `graph_invar ?C` `C' \<in> diff_odd_components ?C Y` 
          by fastforce 

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
                  by (smt (verit, ccfv_threshold) Un_subset_iff assms(1) assms(3) assms(4) assms(5) component_in_E diff_disjoint_elements(2) disjoint_iff_not_equal dual_order.trans vs_member_intro)
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

                  by (metis (no_types, lifting) \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> assms(1) assms(4) diff_odd_components_is_component subsetD)
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
                using component_edges_subset by blast
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
            by (metis Un_iff \<open>C' \<inter> Y = {}\<close> \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> assms(4) diff_odd_components_not_in_X disjoint_iff_not_equal subset_eq)
          then have "{c} \<in> singleton_in_diff E (X\<union>Y)" 

            by (smt (verit, ccfv_SIG) \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> \<open>c \<notin> Vs (graph_diff E (X \<union> Y))\<close> assms(4) component_in_E mem_Collect_eq singleton_in_diff_def subsetD)

          then have "C' \<in> singleton_in_diff E (X\<union>Y)" 
            by (simp add: \<open>C' = {c}\<close>)

          then show ?thesis 
            by (simp add: diff_odd_components_def)
        next
          case False
          then have "C' \<in> odd_components (graph_diff ?C Y)" 
            using \<open>C' \<in> diff_odd_components (component_edges (graph_diff E X) C) Y\<close> diff_odd_components_def by auto
          then have "odd (card C')" 
            by (simp add: odd_components_def)
          have "c \<notin> X \<union> Y" 
            by (metis Un_iff \<open>C' \<inter> Y = {}\<close> \<open>C' \<subseteq> C\<close> \<open>c \<in> C'\<close> assms(4) diff_odd_components_not_in_X disjoint_iff_not_equal subset_eq)

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
            by (smt (z3) Int_Un_distrib Int_Un_eq(4) Un_Int_assoc_eq Un_absorb Un_commute \<open>C' \<subseteq> C\<close> \<open>c \<in> e \<and> e \<in> component_edges (graph_diff E X) C \<and> e \<inter> Y = {}\<close> assms(4) diff_odd_components_not_in_X subset_trans)
          have "e \<in> E" using `c \<in> e \<and> e \<in> ?C \<and> e \<inter> Y = {}` 
            by (metis Diff_insert_absorb component_edges_subset graph_diff_subset subset_Diff_insert)

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

lemma diff_components_finite:
  assumes "graph_invar E"

shows "finite (diff_odd_components E X)" 
  unfolding diff_odd_components_def
proof(safe)

  have "finite (connected_components (graph_diff E (X)))"
    by (meson Vs_subset assms finite_con_comps finite_subset graph_diff_subset)
  have "  (odd_components (graph_diff E (X )))
          \<subseteq> connected_components (graph_diff E (X ))"
    unfolding odd_components_def 
    unfolding connected_components_def 
    by blast
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
  have " singleton_in_diff E (X) \<subseteq> {{v} |v. v \<in> Vs E}"
    unfolding singleton_in_diff_def 
    by blast
  then show "finite ( singleton_in_diff E (X))" using \<open>finite {{v} |v. v \<in> Vs E}\<close> 
      finite_subset[of "( singleton_in_diff E (X))" "{{v} |v. v \<in> Vs E}"]

    by blast
qed

lemma new_components_subset_of_old_one:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  assumes "X \<subseteq> Vs E"
  assumes "C \<in> (diff_odd_components E X)"
  assumes "Y \<subseteq> C"
  assumes "C' \<in>  diff_odd_components (component_edges (graph_diff E X) C) Y"
  shows " C' \<subseteq> Vs  (component_edges (graph_diff E X) C)"
  using component_in_E[of C' "(component_edges (graph_diff E X) C)" "Y"]   
  using assms(6) by blast

lemma new_components_in_old_one:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  assumes "X \<subseteq> Vs E"
  assumes "C \<in> (diff_odd_components E X)"
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
  assumes "tutte_condition E"
  assumes "X \<subseteq> Vs E"
  assumes "C \<in> (diff_odd_components E X)"
  assumes "Y \<subseteq> C"
  shows "(diff_odd_components E X - {C}) \<inter> 
 diff_odd_components (component_edges (graph_diff E X) C) Y= {}" 
proof(rule ccontr)
  assume "(diff_odd_components E X - {C}) \<inter>
    diff_odd_components (component_edges (graph_diff E X) C) Y \<noteq>
    {}"
  then obtain C' where "C' \<in> (diff_odd_components E X - {C}) \<inter>
    diff_odd_components (component_edges (graph_diff E X) C) Y"

    by (meson ex_in_conv)
  then have "C' \<subseteq> C" using new_components_in_old_one[of E X C]
      new_components_subset_of_old_one[of E X C Y C'] 
    using assms(1) assms(2) assms(3) assms(5) assms(4) by auto
  have "\<forall>C'\<in>diff_odd_components E X - {C}. C' \<inter> C = {}" 
    by (metis DiffD2 assms(1) assms(4) diff_component_disjoint insert_Diff insert_iff)
  have "C' \<inter> C = {}" 
    by (meson IntD1 \<open>C' \<in> (diff_odd_components E X - {C}) \<inter> diff_odd_components (component_edges (graph_diff E X) C) Y\<close> \<open>\<forall>C'\<in>diff_odd_components E X - {C}. C' \<inter> C = {}\<close>)
  then have "C' = {}" 
    using \<open>C' \<subseteq> C\<close> by auto
  have "C' \<noteq> {}"
    using \<open>C' \<in> (diff_odd_components E X - {C}) \<inter> diff_odd_components (component_edges (graph_diff E X) C) Y\<close> assms(1) odd_components_nonempty by fastforce
  then show False 
    by (simp add: \<open>C' = {}\<close>)
qed

lemma max_barrier_add_vertex_empty_odd_components:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  assumes "X \<subseteq> Vs E"
  assumes "barrier E X"
  assumes "\<forall> Y \<in> {Z. Z \<subseteq> Vs E \<and> barrier E Z}. Y \<noteq> X \<longrightarrow> \<not> (X \<subseteq> Y)"
  assumes "C \<in> (diff_odd_components E X)"
  assumes "x \<in> C"
  shows "diff_odd_components (component_edges (graph_diff E X) C) {x} = {}" (is "?docX = {}")
proof(rule ccontr)
  assume "?docX \<noteq> {}"
  have "{x} \<noteq> {}" 
    by simp
  have " diff_odd_components E (X \<union> {x}) =
 diff_odd_components E X - {C} \<union> diff_odd_components (component_edges (graph_diff E X) C) {x}"
    using add_subset_change_odd_components[of E X C "{x}"] assms by auto
  have "graph_invar (component_edges (graph_diff E X) C)" 
    by (meson Vs_subset assms(1) component_edges_subset finite_subset graph_diff_subset subsetD)
  have "finite ?docX" using diff_components_finite[of "(component_edges (graph_diff E X) C)"]

    using \<open>graph_invar (component_edges (graph_diff E X) C)\<close> by blast
  then have "card ?docX \<ge> 1" 
    by (simp add: Suc_leI \<open>diff_odd_components (component_edges (graph_diff E X) C) {x} \<noteq> {}\<close> card_gt_0_iff)
  have "card (diff_odd_components E (X\<union>{x})) \<le> card (X\<union>{x})"
    using assms(2) unfolding tutte_condition_def 
    by (metis Un_insert_right assms(3) assms(6) assms(7) boolean_algebra_cancel.sup0 component_in_E insert_subset subsetD)
  have "card (diff_odd_components E (X\<union>{x}))\<le> card X +1" 
    by (metis One_nat_def Un_insert_right \<open>card (diff_odd_components E (X \<union> {x})) \<le> card (X \<union> {x})\<close> add.right_neutral add_Suc_right assms(1) assms(3) boolean_algebra_cancel.sup0 card.insert finite_subset insert_absorb trans_le_add1)
  have "card (diff_odd_components E X) = card X" 
    using assms(4) barrier_def by blast
  have "card ((diff_odd_components E X) - {C}) = card X - 1" 
    by (metis assms(1) assms(3) assms(4) assms(6) barrier_def card.infinite card_0_eq card_Diff_singleton finite_subset)
  then have "card (diff_odd_components E (X\<union>{x})) \<le> (card X - 1) + 2" 

    using \<open>card (diff_odd_components E (X \<union> {x})) \<le> card X + 1\<close> by linarith
  then have "card (diff_odd_components E (X\<union>{x})) \<le> card ((diff_odd_components E X) - {C}) + 2"

    using \<open>card (diff_odd_components E X - {C}) = card X - 1\<close> by presburger
  then have "card (diff_odd_components E X - {C} \<union> 
  diff_odd_components (component_edges (graph_diff E X) C) {x})
\<le> card ((diff_odd_components E X) - {C}) + 2" 
    using \<open>diff_odd_components E (X \<union> {x}) = diff_odd_components E X - {C} \<union> diff_odd_components (component_edges (graph_diff E X) C) {x}\<close> by auto



  have "\<forall>C' \<in> (diff_odd_components E X - {C}). C' \<inter> C = {}"

    by (metis DiffD1 DiffD2 assms(1) assms(6) diff_component_disjoint insert_iff)
  then have "Vs (diff_odd_components E X - {C}) \<inter> C = {}" 
    by (smt (verit, ccfv_SIG) Int_ac(3) Vs_def assms(1) assms(6) diff_component_disjoint disjoint_iff_not_equal insert_Diff insert_partition)


  then have "card ?docX \<le> 2" 
    by (smt (verit, ccfv_SIG) Int_lower2 Nat.le_diff_conv2 Un_upper1 \<open>card (diff_odd_components E X - {C} \<union> diff_odd_components (component_edges (graph_diff E X) C) {x}) \<le> card (diff_odd_components E X - {C}) + 2\<close> \<open>finite (diff_odd_components (component_edges (graph_diff E X) C) {x})\<close> add.commute assms(1) assms(2) assms(3) assms(4) assms(6) assms(7) card_Un_disjoint card_mono diff_add_inverse diff_components_finite finite_Diff finite_Un insert_subset le_antisym nat_le_linear new_components_intersection_old_is_empty)
  show False
  proof(cases "card ?docX = 2")
    case True
    then have "card (diff_odd_components E (X\<union>{x})) = card X + 1" 
      using  new_components_intersection_old_is_empty[of E X C "{x}"] 

      by (smt (verit, best) Int_lower2 Nat.add_diff_assoc Nat.add_diff_assoc2 One_nat_def Suc_leI \<open>1 \<le> card (diff_odd_components (component_edges (graph_diff E X) C) {x})\<close> \<open>Vs (diff_odd_components E X - {C}) \<inter> C = {}\<close> \<open>card (diff_odd_components E X - {C}) = card X - 1\<close> \<open>diff_odd_components E (X \<union> {x}) = diff_odd_components E X - {C} \<union> diff_odd_components (component_edges (graph_diff E X) C) {x}\<close> \<open>finite (diff_odd_components (component_edges (graph_diff E X) C) {x})\<close> assms(1) assms(2) assms(3) assms(4) assms(6) assms(7) barrier_def card_Un_disjoint card_gt_0_iff diff_add_inverse2 finite_Diff finite_subset insert_subsetI one_add_one)
    then have "card (diff_odd_components E (X\<union>{x})) = card (X\<union>{x})" 
      by (metis One_nat_def Un_insert_right \<open>card (diff_odd_components E X) = card X\<close> add.right_neutral add_Suc_right assms(1) assms(3) card.insert finite_subset insert_absorb sup_bot_right)
    then have "barrier E (X\<union>{x})"
      by (simp add: barrier_def)
    have "X \<subseteq> (X\<union>{x})" 
      by auto
    then show ?thesis using assms(5) `barrier E (X\<union>{x})`  
      by (metis (no_types, lifting) One_nat_def Un_subset_iff \<open>card (diff_odd_components E (X \<union> {x})) = card X + 1\<close> \<open>card (diff_odd_components E (X \<union> {x})) \<le> card (X \<union> {x})\<close> assms(3) assms(6) assms(7) component_in_E diff_add_inverse diff_is_0_eq' insert_Diff insert_is_Un mem_Collect_eq nat.simps(3))

  next
    case False
    then have " card (diff_odd_components (component_edges(graph_diff E X) C) {x})  = 1" 
      using \<open>1 \<le> card (diff_odd_components (component_edges (graph_diff E X) C) {x})\<close> \<open>card (diff_odd_components (component_edges (graph_diff E X) C) {x}) \<le> 2\<close> by linarith
    then have "\<exists>!C'. C' \<in> (diff_odd_components (component_edges(graph_diff E X) C) {x})"

      by (metis card_1_singletonE empty_iff insert_iff)
    have "(diff_odd_components E X - {C}) \<inter> diff_odd_components (component_edges (graph_diff E X) C) {x} = {}"
      using  new_components_intersection_old_is_empty[of E X C "{x}"] assms 
      by simp
    have "Vs (component_edges(graph_diff E X) C) = C" 
      by (smt (verit, best) IntI Nat.add_diff_assoc2 One_nat_def Suc_leI Un_insert_right \<open>(diff_odd_components E X - {C}) \<inter> diff_odd_components (component_edges (graph_diff E X) C) {x} = {}\<close> \<open>card (diff_odd_components (component_edges (graph_diff E X) C) {x}) = 1\<close> \<open>card (diff_odd_components E X - {C}) = card X - 1\<close> \<open>card (diff_odd_components E X) = card X\<close> \<open>diff_odd_components E (X \<union> {x}) = diff_odd_components E X - {C} \<union> diff_odd_components (component_edges (graph_diff E X) C) {x}\<close> \<open>finite (diff_odd_components (component_edges (graph_diff E X) C) {x})\<close> add.right_neutral add_Suc_right assms(1) assms(3) assms(6) assms(7) boolean_algebra_cancel.sup0 card.empty card.insert card_Un_disjoint card_gt_0_iff component_in_E diff_add_inverse2 diff_components_finite diff_is_0_eq' diff_odd_component_parity diff_odd_components_not_in_X empty_iff finite_Diff insert_subset nat_le_linear odd_card_imp_not_empty odd_one subsetD)



    then show ?thesis 
      by (smt (verit, ccfv_threshold) IntI Nat.add_diff_assoc2 One_nat_def Suc_leI Un_insert_right \<open>(diff_odd_components E X - {C}) \<inter> diff_odd_components (component_edges (graph_diff E X) C) {x} = {}\<close> \<open>card (diff_odd_components (component_edges (graph_diff E X) C) {x}) = 1\<close> \<open>card (diff_odd_components E X - {C}) = card X - 1\<close> \<open>card (diff_odd_components E X) = card X\<close> \<open>diff_odd_components E (X \<union> {x}) = diff_odd_components E X - {C} \<union> diff_odd_components (component_edges (graph_diff E X) C) {x}\<close> \<open>finite (diff_odd_components (component_edges (graph_diff E X) C) {x})\<close> add_Suc_right assms(1) assms(2) assms(3) assms(6) assms(7) boolean_algebra_cancel.sup0 card.empty card.insert card_Un_disjoint card_gt_0_iff component_in_E diff_add_inverse2 diff_components_finite diff_is_0_eq' diff_odd_component_parity diff_odd_components_not_in_X empty_iff finite_Diff insert_subset le_iff_add odd_card_imp_not_empty odd_one subsetD tutte_condition_def)
  qed
qed

lemma max_barrier_add_vertex_doesnt_increase_odd_components:
  assumes "graph_invar E"
  assumes "tutte_condition E"
  assumes "X \<subseteq> Vs E"
  assumes "barrier E X"
  assumes "\<forall> Y \<in> {Z. Z \<subseteq> Vs E \<and> barrier E Z}. Y \<noteq> X \<longrightarrow> \<not> (X \<subseteq> Y)"
  assumes "C \<in> (diff_odd_components E X)"
  assumes "x \<in> C"
  shows "diff_odd_components E (X\<union>{x}) = (diff_odd_components E X) - {C}"
proof -
  have "{x} \<noteq> {}" 
    by simp
  have " diff_odd_components E (X \<union> {x}) =
 diff_odd_components E X - {C} \<union> diff_odd_components (component_edges (graph_diff E X) C) {x}"
    using add_subset_change_odd_components[of E X C "{x}"] assms by auto
  let ?docX = "diff_odd_components (component_edges (graph_diff E X) C) {x}"
  have "?docX = {}" 
    by (simp add: assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) max_barrier_add_vertex_empty_odd_components)
  then show " diff_odd_components E (X \<union> {x}) = diff_odd_components E X - {C}"

    using \<open>diff_odd_components E (X \<union> {x}) = diff_odd_components E X - {C} \<union> diff_odd_components (component_edges (graph_diff E X) C) {x}\<close> by auto
qed

lemma component_edges_same_in_diff:
  assumes "C \<in> diff_odd_components E X"
  shows  "(component_edges (graph_diff E X) C) = (component_edges E C)"
proof - 
  have "\<forall>e \<subseteq> C. e \<in> E \<longrightarrow> e \<in> graph_diff E X"
  proof(safe)
    fix e
    assume "e \<subseteq> C" "e \<in> E"
    then have "e \<inter> X = {}" 
      using assms diff_odd_components_not_in_X by blast
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
    have "C \<in> diff_odd_components E X" 
      by (simp add: assms(3) diff_odd_components_def)
    then have "e \<subseteq> C" using `x \<in> e \<and> e \<in> (component_edges E C)` 
      unfolding component_edges_def 
      by blast

    then show "x \<in> C" 
      using \<open>x \<in> e \<and> e \<in> component_edges E C\<close> by blast
  }
  fix x
  assume "x \<in> C"
  then have "x \<in> Vs (graph_diff E X) \<and> connected_component (graph_diff E X) x = C \<and> odd (card C)"

    by (smt (verit) assms(3) connected_components_member_eq in_connected_component_in_edges mem_Collect_eq odd_components_def)
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
  assumes "C \<in> diff_odd_components E X"
  assumes "x' \<in> C"
  assumes "{connected_component (graph_diff E X) x', {y'}} \<in> M'"
  assumes "matching M'" 
  shows " Vs {{c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} |x y.
        {connected_component (graph_diff E X) x, {y}} \<in> M'} \<inter> C =
    {c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'}" (is "Vs ?Z2 \<inter> C = ?C'")
proof
  have "connected_component (graph_diff E X) x' = C" 
    by (simp add: assms(1) assms(3) assms(4) diff_odd_components_is_component)
        show "Vs ?Z2 \<inter> C \<subseteq> ?C'"
        proof
          fix z
          assume "z\<in> Vs ?Z2 \<inter> C"
          then have "\<exists>C' \<in> ?Z2. z \<in> C'" 
            by (meson IntD1 vs_member_elim)
          then obtain C' where "C' \<in> ?Z2 \<and> z \<in> C'" by blast
          then have "\<exists>x1 y1. C' = {c . \<exists> e. e \<in> E \<and> e = {c, y1}  \<and> c \<notin> X
                     \<and> c \<in> connected_component (graph_diff E X) x1} 
        \<and> {connected_component (graph_diff E X) x1, {y1}} \<in> M'" by auto
          then obtain x1 y1 where " C' = {c . \<exists> e. e \<in> E \<and> e = {c, y1}  \<and> c \<notin> X
                     \<and> c \<in> connected_component (graph_diff E X) x1} 
        \<and> {connected_component (graph_diff E X) x1, {y1}} \<in> M'" by auto



          then have " z \<in> connected_component (graph_diff E X) x1"
            using \<open>C' \<in> {{c. \<exists>e. e \<in> E \<and> e = {c, y}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'} \<and> z \<in> C'\<close> by auto
          then have " connected_component (graph_diff E X) z = connected_component (graph_diff E X) x1"

            by (metis (no_types, lifting) connected_components_member_eq)
          then have "C' = {c . \<exists> e. e \<in> E \<and> e = {c, y1}  \<and> c \<notin> X
                     \<and> c \<in> connected_component (graph_diff E X) z} 
        \<and> {connected_component (graph_diff E X) z, {y1}} \<in> M'
" 
            using \<open>C' = {c. \<exists>e. e \<in> E \<and> e = {c, y1}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x1} \<and> {connected_component (graph_diff E X) x1, {y1}} \<in> M'\<close> by presburger
         
          have "connected_component (graph_diff E X) x' = C" 
            by (simp add: \<open>connected_component (graph_diff E X) x' = C\<close>)
          have "connected_component (graph_diff E X) z = connected_component (graph_diff E X) x'"
            
            using \<open>connected_component (graph_diff E X) x' = C\<close> \<open>z \<in> Vs {{c. \<exists>e. e \<in> E \<and> e = {c, y}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'} \<inter> C\<close> connected_components_member_eq by force
          then have "{connected_component (graph_diff E X) z, {y1}} \<inter>
                    {connected_component (graph_diff E X) x', {y'}} \<noteq> {}"

            by (simp add: \<open>connected_component (graph_diff E X) z = connected_component (graph_diff E X) x'\<close>)
          have "matching M'" using assms(6) by blast 
         
          then have "{connected_component (graph_diff E X) z, {y1}} =
                    {connected_component (graph_diff E X) x', {y'}}"

            by (meson \<open>C' = {c. \<exists>e. e \<in> E \<and> e = {c, y1}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) z} \<and> {connected_component (graph_diff E X) z, {y1}} \<in> M'\<close> \<open>{connected_component (graph_diff E X) x', {y'}} \<in> M'\<close> \<open>{connected_component (graph_diff E X) z, {y1}} \<inter> {connected_component (graph_diff E X) x', {y'}} \<noteq> {}\<close> matching_def)
          then have "y1 = y'" 
            by (metis (full_types) \<open>connected_component (graph_diff E X) z = connected_component (graph_diff E X) x'\<close> doubleton_eq_iff)
          then have "C' = ?C'" 
            using \<open>C' = {c. \<exists>e. e \<in> E \<and> e = {c, y1}  \<and> c \<notin> X  \<and> c \<in> connected_component (graph_diff E X) z} \<and> {connected_component (graph_diff E X) z, {y1}} \<in> M'\<close> \<open>connected_component (graph_diff E X) z = connected_component (graph_diff E X) x'\<close> by presburger
          then show "z \<in> ?C'" 
            using \<open>C' \<in> {{c. \<exists>e. e \<in> E \<and> e = {c, y}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'} \<and> z \<in> C'\<close> by blast
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
          {c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} \<and>
          {connected_component (graph_diff E X) x', {y'}} \<in> M'" 
              using assms(5) by fastforce
              show " \<exists>x y. {c. \<exists>e. e \<in> E \<and> e = {c, y'} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} =
          {c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} \<and>
          {connected_component (graph_diff E X) x, {y}} \<in> M'" 
                by (metis Collect_cong \<open>\<exists>e. e \<in> E \<and> e = {z, y'} \<and> z \<notin> X \<and> z \<in> connected_component (graph_diff E X) x'\<close> \<open>{connected_component (graph_diff E X) z, {y'}} \<in> M'\<close> connected_components_member_eq)

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

lemma diff_odd_components_are_components:
  assumes "graph_invar E"
  shows"diff_odd_components E X = {C. \<exists> v\<in>Vs E-X. connected_component (graph_diff E X) v = C \<and> odd (card C)}"
proof(safe)
  {
    fix C
    assume "C \<in> diff_odd_components E X"
    then obtain v where "connected_component (graph_diff E X) v = C" 
      using assms(1) diff_odd_components_is_component odd_components_nonempty 
  by (metis subset_empty subset_emptyI)
    
    have "odd (card C)"
    proof(cases "C \<in> odd_components (graph_diff E X)")
      case True
      then show ?thesis unfolding odd_components_def 
        by fastforce
    next
      case False
      then have "C \<in> singleton_in_diff E X" 
        by (metis UnE \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_def)
      then show ?thesis unfolding singleton_in_diff_def 
        by force  
    qed
    have "v \<in> Vs E" 
      by (metis \<open>C \<in> diff_odd_components E X\<close> \<open>connected_component (graph_diff E X) v = C\<close> component_in_E in_own_connected_component subsetD)
    have "v \<notin> X" 
      by (metis IntI \<open>C \<in> diff_odd_components E X\<close> \<open>connected_component (graph_diff E X) v = C\<close> diff_odd_components_not_in_X empty_iff in_own_connected_component)

    then show " \<exists>v\<in>Vs E-X. connected_component (graph_diff E X) v = C \<and> odd (card C)" 
      using \<open>connected_component (graph_diff E X) v = C\<close> \<open>odd (card C)\<close> \<open>v \<in> Vs E\<close> by blast
  }
  fix v
  assume "v \<in> Vs E" "v \<notin> X"
  assume " odd (card (connected_component (graph_diff E X) v))"
  show " connected_component (graph_diff E X) v \<in> diff_odd_components E X"
  proof(cases "v \<in> Vs (graph_diff E X)")
    case True
    then have " connected_component
     (graph_diff E X) v \<in>  odd_components (graph_diff E X)" unfolding odd_components_def
      using \<open>odd (card (connected_component (graph_diff E X) v))\<close> by blast
then show ?thesis 
  by (simp add: diff_odd_components_def)
next
  case False
  have "(connected_component (graph_diff E X) v) = {v}"
    by (simp add: False connected_components_notE_singletons)
  have " v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)"
    by (simp add: False \<open>v \<in> Vs E\<close> \<open>v \<notin> X\<close>)
  then have "{v} \<in> singleton_in_diff E X" 
    by (simp add: singleton_in_diff_def)
  then show ?thesis 
    by (simp add: \<open>connected_component (graph_diff E X) v = {v}\<close> diff_odd_components_def)
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
       have "(singleton_in_diff E X) \<union> {{x}} = singleton_in_diff E (X-{x})"
         unfolding singleton_in_diff_def
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

   then have "(diff_odd_components E X) \<union> {{x}} = diff_odd_components E (X-{x})" 
     unfolding diff_odd_components_def 
     using \<open>graph_diff E X = graph_diff E (X - {x})\<close> by auto
   have "card (diff_odd_components E (X-{x})) = 
        card ((diff_odd_components E X) \<union> {{x}})" 
     
     using \<open>diff_odd_components E X \<union> {{x}} = diff_odd_components E (X - {x})\<close> by presburger
   have "(diff_odd_components E X) \<inter> {{x}} = {}" 
     using \<open>x \<in> X\<close> diff_odd_components_not_in_X by blast
   then have "card (diff_odd_components E (X-{x})) = 
        card (diff_odd_components E X) + card {{x}}" 
     by (metis \<open>card (diff_odd_components E (X - {x})) = card (diff_odd_components E X \<union> {{x}})\<close> assms(1) card_Un_disjoint diff_components_finite finite.emptyI finite.insertI)
   then have "card (diff_odd_components E (X-{x})) = card X + 1" 
     by (metis One_nat_def assms(4) barrier_def card.empty card.insert finite.emptyI insert_absorb insert_not_empty)
   have "card (diff_odd_components E (X-{x})) \<le> card (X-{x})" 
     by (metis \<open>x \<in> X\<close> assms(2) assms(3) insert_Diff insert_subset tutte_condition_def)
   then show False 
     by (metis One_nat_def \<open>card (diff_odd_components E (X - {x})) = card X + 1\<close> assms(1) assms(3) card.empty card_Diff1_le card_gt_0_iff diff_add_inverse diff_is_0_eq' finite_subset le_trans zero_less_Suc)
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
      then have "card (diff_odd_components E {}) \<le> card {}" 
        by (metis "less.prems"(2) bot.extremum card.empty tutte_condition_def)
      then have "card (diff_odd_components E {}) = 0" by simp
      have "graph_diff E {} = E" 
        by (simp add: graph_diff_def)
      then have "(singleton_in_diff E {}) = {}" 
        unfolding singleton_in_diff_def 
        by simp
      then have "diff_odd_components E {} = odd_components E"
        unfolding diff_odd_components_def using `graph_diff E {} = E`
        by simp
      have "card (odd_components E) \<ge> 1" using `odd (card (Vs E))` 
        by (metis "less.prems"(1) \<open>card (diff_odd_components E {}) = 0\<close> \<open>diff_odd_components E {} = odd_components E\<close> card.empty odd_card_imp_not_empty odd_components_eq_modulo_cardinality)
      then show False
        using \<open>card (diff_odd_components E {}) = 0\<close> \<open>diff_odd_components E {} = odd_components E\<close> by force
    qed
    have "\<forall>x \<in> (Vs E). card {x} \<ge> card (diff_odd_components E {x})"
      using "less.prems"(2) 
      by (meson bot.extremum insert_subsetI tutte_condition_def)
    then  have "\<forall>x \<in> (Vs E). even (card {x} - card (diff_odd_components E {x}))" 
      using `even (card (Vs E))` diff_odd_component_parity
      by (metis "less.prems"(1) bot.extremum insert_subsetI)
    then have "\<forall>x \<in> (Vs E).card (diff_odd_components E {x}) = 1"
      by (metis One_nat_def Suc_leI \<open>\<forall>x\<in>Vs E. card (diff_odd_components E {x}) \<le> card {x}\<close> antisym_conv card.empty card.insert dvd_diffD empty_iff finite.emptyI not_less odd_card_imp_not_empty odd_one zero_order(2))
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
    then have "card (diff_odd_components E X) = card X" unfolding barrier_def by auto
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


      have "singleton_in_diff E X \<subseteq> singleton_in_diff E (X \<union> {v})"
      proof
        fix xs
        assume "xs \<in> singleton_in_diff E X"

        then have "\<exists>x. xs = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)" 
          unfolding singleton_in_diff_def by auto
        then obtain x where " xs = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)" 
          by presburger
        then have "x \<notin> X \<union> {v}" 
          by (metis UnE \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> in_connected_component_in_edges singletonD)
        have "x \<notin> Vs (graph_diff E X)" 
          by (simp add: \<open>xs = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)\<close>)
        then have "x \<notin> Vs (graph_diff E (X \<union> {v}))" unfolding graph_diff_def
          by (simp add: vs_member)
        then have "{x} \<in> singleton_in_diff E (X \<union> {v})" unfolding
            singleton_in_diff_def
          using \<open>x \<notin> X \<union> {v}\<close> \<open>xs = {x} \<and> x \<in> Vs E \<and> x \<notin> X \<and> x \<notin> Vs (graph_diff E X)\<close> by blast
        then show "xs \<in> singleton_in_diff E (X \<union> {v})" 
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
          unfolding odd_components_def
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

              by (simp add: \<open>C' \<in> connected_components (graph_diff E X)\<close> \<open>component_edges (graph_diff E X) C' \<noteq> {}\<close> \<open>graph_invar (graph_diff E X)\<close> \<open>hd p \<in> C'\<close> \<open>path (graph_diff E X) p\<close> defvd)

            have "(component_edges (graph_diff E X) C') = (component_edges (graph_diff E (X\<union>{v})) C')"
            proof(safe)
              { fix e
                assume "e \<in> component_edges (graph_diff E X) C'"
                then have "e \<subseteq> C'" unfolding component_edges_def
                  by blast
                then have "e \<in> (graph_diff E X)" using `e \<in> component_edges (graph_diff E X) C'`
                  using component_edges_subset by blast
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
                using \<open>e \<in> component_edges (graph_diff E (X \<union> {v})) C'\<close> component_edges_subset by blast

              then have "e \<inter> X = {}" unfolding graph_diff_def  
                by blast
              then have "e \<in> (graph_diff E X)" unfolding graph_diff_def 
                using \<open>e \<in> graph_diff E (X \<union> {v})\<close> graph_diff_subset by blast
              then show "e \<in> component_edges (graph_diff E X) C'" unfolding component_edges_def  
                using \<open>e \<subseteq> C'\<close> \<open>graph_invar (graph_diff E X)\<close> by fastforce
            qed

            then show "path (graph_diff E (X \<union> {v})) p"
              using `path (component_edges (graph_diff E X) C')  p` 
              by (metis component_edges_subset path_subset)

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
          unfolding odd_components_def
          using \<open>\<forall>z\<in>C'. z \<in> Vs (graph_diff E (X \<union> {v}))\<close> \<open>e \<in> graph_diff E X \<and> x \<in> e\<close> \<open>e \<subseteq> C'\<close> odd_x by fastforce
      qed
      then have "diff_odd_components E X \<subseteq> diff_odd_components E (X \<union> {v})"
        unfolding diff_odd_components_def
        using \<open>singleton_in_diff E X \<subseteq> singleton_in_diff E (X \<union> {v})\<close> by blast

      show False
      proof(cases "\<exists>x \<in> (C-{v}). x \<notin> Vs (graph_diff E (X \<union> {v}))")
        case True
        then  obtain x where "x \<in> (C-{v}) \<and> (x \<notin> Vs (graph_diff E (X \<union> {v})))" by auto
        then have "x \<in> Vs E"
          by (metis DiffD1 Diff_insert_absorb Vs_subset \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> connected_component_subset graph_diff_subset subset_Diff_insert)

        then have "x \<notin> X \<and> x \<notin> Vs (graph_diff E (X\<union>{v}))" 
          by (smt (verit, best) "less.prems"(1) DiffD1 \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> connected_component_subset diff_disjoint_elements(2) disjoint_iff_not_equal subset_iff)
        then have "{x} \<in> singleton_in_diff E (X \<union> {v})" unfolding singleton_in_diff_def

          using \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> \<open>x \<in> Vs E\<close> by auto
        have "x \<in> Vs (graph_diff E X)" 
          by (metis DiffD1 Diff_insert_absorb \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> connected_component_subset subset_Diff_insert)
        then have "{x} \<notin> singleton_in_diff E (X)" unfolding singleton_in_diff_def 
          by blast
        have "{x} \<notin> odd_components (graph_diff E X)" unfolding odd_components_def 
          by (smt (verit, del_insts) Diff_insert_absorb \<open>v \<in> C\<close> \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> comp_C connected_components_member_eq insert_iff mem_Collect_eq mk_disjoint_insert singletonI singleton_insert_inj_eq')
        then have "{x} \<notin> diff_odd_components E X"  unfolding diff_odd_components_def

          using \<open>{x} \<notin> singleton_in_diff E X\<close> by force

        then have "diff_odd_components E X \<subset> diff_odd_components E (X \<union> {v})" 
          unfolding diff_odd_components_def 
          by (metis UnCI \<open>diff_odd_components E X \<subseteq> diff_odd_components E (X \<union> {v})\<close> \<open>{x} \<in> singleton_in_diff E (X \<union> {v})\<close> diff_odd_components_def psubsetI)

        have "finite (connected_components (graph_diff E (X \<union> {v})))"

          by (meson "less.prems"(1) Vs_subset finite_con_comps finite_subset graph_diff_subset)
        have "  (odd_components (graph_diff E (X \<union> {v})))
          \<subseteq> connected_components (graph_diff E (X \<union> {v}))"
          unfolding odd_components_def 
          unfolding connected_components_def 
          by blast
        then have "finite  (odd_components (graph_diff E (X \<union> {v})))" 

          using \<open>finite (connected_components (graph_diff E (X \<union> {v})))\<close> finite_subset by blast

        have "finite ( singleton_in_diff E (X \<union> {v}))" 
          by (smt (verit) "less.prems"(1) Un_insert_right Vs_def Vs_subset \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> boolean_algebra_cancel.sup0 connected_component_subset diff_is_union_elements finite_Un finite_UnionD graph_diff_subset insert_Diff insert_subset)

        then have "finite (diff_odd_components E (X \<union> {v}))" 
          by (metis \<open>finite (odd_components (graph_diff E (X \<union> {v})))\<close> diff_odd_components_def finite_Un)
        then have "card (diff_odd_components E X) < card (diff_odd_components E (X \<union> {v}))"

          by (meson \<open>diff_odd_components E X \<subset> diff_odd_components E (X \<union> {v})\<close> psubset_card_mono)
        then have "card(X) + 1 \<le> card (diff_odd_components E (X \<union> {v}))" 
          by (simp add: \<open>card (diff_odd_components E X) = card X\<close>)
        have "card (X \<union> {v}) = (card X) + 1" 
          by (metis "less.prems"(1) IntI One_nat_def Un_insert_right \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> add.right_neutral add_Suc_right card.insert diff_disjoint_elements(2) empty_iff finite_subset in_connected_component_in_edges sup_bot_right)

        have "card (diff_odd_components E (X \<union> {v})) \<le> card (X \<union> {v})" using assms(2) unfolding tutte_condition_def

          by (metis "less.prems"(2) DiffD1 Un_insert_right \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>v \<in> C\<close> \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> \<open>x \<in> Vs E\<close> boolean_algebra_cancel.sup0 comp_C connected_components_member_eq diff_connected_component_subset insert_Diff insert_subset tutte_condition_def)
        then have "card (diff_odd_components E (X \<union> {v})) \<le> (card X) + 1" 

          using \<open>card (X \<union> {v}) = card X + 1\<close> by presburger
        then have "barrier E (X \<union> {v})" 
          by (metis Un_empty \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>card (X \<union> {v}) = card X + 1\<close> \<open>card X + 1 \<le> card (diff_odd_components E (X \<union> {v}))\<close> barrier_def le_antisym)
        then have " (X \<union> {v}) \<in> ?B" 
          by (metis DiffD1 Un_insert_right \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> \<open>x \<in> C - {v} \<and> x \<notin> Vs (graph_diff E (X \<union> {v}))\<close> \<open>x \<in> Vs E\<close> connected_components_member_eq diff_connected_component_subset insert_subsetI mem_Collect_eq subsetD sup_bot_right)
        then show ?thesis 
          by (metis X_max \<open>card (diff_odd_components E X) < card (diff_odd_components E (X \<union> {v}))\<close> sup.strict_order_iff sup_ge1)
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
                by (metis (no_types, hide_lams) \<open>C' \<in> connected_components (graph_diff E (X \<union> {v}))\<close> \<open>\<forall>C'\<in>connected_components (graph_diff E (X \<union> {v})). C' \<subseteq> C - {v} \<longrightarrow> (\<exists>x y. {x, y} \<subseteq> C')\<close> bot.extremum insert_subset insert_subsetI is_singletonI is_singleton_altdef order_class.order.eq_iff subsetI) 
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
          unfolding odd_components_def  
          by (smt (z3) connected_comp_has_vert mem_Collect_eq)
        then have "C'  \<notin> odd_components (graph_diff E (X))" unfolding singleton_in_diff_def 

          by (smt (verit, ccfv_SIG) Diff_empty \<open>C' \<in> connected_components (graph_diff E (X \<union> {v})) \<and> C' \<subseteq> C - {v} \<and> odd (card C')\<close> comp_C connected_components_member_eq in_own_connected_component mem_Collect_eq odd_components_def subsetD subset_Diff_insert)
        have "C'  \<notin> singleton_in_diff E X" unfolding singleton_in_diff_def 

          by (smt (verit, ccfv_threshold) Vs_subset \<open>C' \<in> connected_components (graph_diff E (X \<union> {v})) \<and> C' \<subseteq> C - {v} \<and> odd (card C')\<close> \<open>graph_diff E (X \<union> {v}) \<subseteq> graph_diff E X\<close> connected_component_subs_Vs insert_subset mem_Collect_eq order_trans)
        then have "C' \<notin> diff_odd_components E X"  unfolding diff_odd_components_def

          using \<open>C' \<notin> odd_components (graph_diff E (X))\<close> by force

        then have "diff_odd_components E X \<subset> diff_odd_components E (X \<union> {v})" 
          unfolding diff_odd_components_def 
          by (metis UnCI \<open>C' \<in> odd_components (graph_diff E (X \<union> {v}))\<close> \<open>diff_odd_components E X \<subseteq> diff_odd_components E (X \<union> {v})\<close> diff_odd_components_def psubsetI)

        have "finite (connected_components (graph_diff E (X \<union> {v})))"

          by (meson "less.prems"(1) Vs_subset finite_con_comps finite_subset graph_diff_subset)
        have "  (odd_components (graph_diff E (X \<union> {v})))
          \<subseteq> connected_components (graph_diff E (X \<union> {v}))"
          unfolding odd_components_def 
          unfolding connected_components_def 
          by blast
        then have "finite  (odd_components (graph_diff E (X \<union> {v})))" 

          using \<open>finite (connected_components (graph_diff E (X \<union> {v})))\<close> finite_subset by blast

        have "finite ( singleton_in_diff E (X \<union> {v}))" 
          by (smt (verit) "less.prems"(1) Un_insert_right Vs_def Vs_subset \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> boolean_algebra_cancel.sup0 connected_component_subset diff_is_union_elements finite_Un finite_UnionD graph_diff_subset insert_Diff insert_subset)

        then have "finite (diff_odd_components E (X \<union> {v}))" 
          by (metis \<open>finite (odd_components (graph_diff E (X \<union> {v})))\<close> diff_odd_components_def finite_Un)
        then have "card (diff_odd_components E X) < card (diff_odd_components E (X \<union> {v}))"

          by (meson \<open>diff_odd_components E X \<subset> diff_odd_components E (X \<union> {v})\<close> psubset_card_mono)
        then have "card(X) + 1 \<le> card (diff_odd_components E (X \<union> {v}))" 
          by (simp add: \<open>card (diff_odd_components E X) = card X\<close>)
        have "card (X \<union> {v}) = (card X) + 1" 
          by (metis "less.prems"(1) IntI One_nat_def Un_insert_right \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> add.right_neutral add_Suc_right card.insert diff_disjoint_elements(2) empty_iff finite_subset in_connected_component_in_edges sup_bot_right)

        have "card (diff_odd_components E (X \<union> {v})) \<le> card (X \<union> {v})" using assms(2) unfolding tutte_condition_def

          by (smt (verit, ccfv_threshold) "less.prems"(2) "less.prems"(1) Un_insert_right Un_upper1 \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> boolean_algebra_cancel.sup0 connected_component_subset diff_is_union_elements insert_Diff insert_subset tutte_condition_def)
        then have "card (diff_odd_components E (X \<union> {v})) \<le> (card X) + 1" 

          using \<open>card (X \<union> {v}) = card X + 1\<close> by presburger
        then have "barrier E (X \<union> {v})" 
          by (metis Un_empty \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>card (X \<union> {v}) = card X + 1\<close> \<open>card X + 1 \<le> card (diff_odd_components E (X \<union> {v}))\<close> barrier_def le_antisym)
        then have " (X \<union> {v}) \<in> ?B" 
          by (metis Un_insert_right Vs_subset \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C\<close> \<open>v \<in> C\<close> connected_component_subset graph_diff_subset insert_subsetI mem_Collect_eq subsetD sup_bot_right)
        then show ?thesis 
          by (metis X_max \<open>card (diff_odd_components E X) < card (diff_odd_components E (X \<union> {v}))\<close> sup.strict_order_iff sup_ge1)
      qed
    qed















    then have "{C. \<exists>x \<in> Vs E - X. C = connected_component (graph_diff E X) x \<and> even (card C)} = {}"
      unfolding even_components_def 
      by (smt (verit, ccfv_threshold) Collect_empty_eq One_nat_def card.empty card.insert connected_components_notE_singletons empty_iff finite.emptyI odd_one)


    have "(diff_odd_components E X) = {C. \<exists>x \<in> Vs E - X. C = connected_component (graph_diff E X) x \<and> odd (card C)}" 
      using diff_odd_components_are_components[of E X]  
      using Collect_cong less.prems(1) by auto

    then have "(diff_odd_components E X) = {C. \<exists>x \<in> Vs E - X. C = connected_component (graph_diff E X) x}"
      
      by (smt (verit, ccfv_SIG) Collect_cong DiffD1 \<open>\<forall>x\<in>Vs E. card (diff_odd_components E {x}) = 1\<close> \<open>\<forall>x\<in>Vs E. card (diff_odd_components E {x}) \<le> card {x}\<close> \<open>\<forall>x\<in>Vs E. even (card {x} - card (diff_odd_components E {x}))\<close> \<open>even_components (graph_diff E X) = {}\<close> bex_empty connected_components_notE_singletons dvd_diffD1 even_components_def mem_Collect_eq odd_one)


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
      have "Vs ?G' - (diff_odd_components E X) = (\<Union>x\<in>X. ?f x)"
      proof(safe)
        {
          fix y
          assume "y \<in> Vs ?G'"
          assume "y \<notin> (diff_odd_components E X)"
          then have "\<nexists>x. x\<in> Vs E - X \<and> y = connected_component (graph_diff E X) x"
            
            using \<open>diff_odd_components E X = {C. \<exists>x\<in>Vs E - X. C = connected_component (graph_diff E X) x}\<close> by blast
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
      assume "{y} \<in> diff_odd_components E X"
      show False 
        by (metis IntI \<open>y \<in> X\<close> \<open>{y} \<in> diff_odd_components E X\<close> diff_odd_components_not_in_X empty_iff insertCI)
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
    have "(diff_odd_components E X) \<subseteq> Vs ?G'" 
    proof
      fix C
      assume "C \<in> (diff_odd_components E X)"
      then obtain x y where  " {x, y} \<in> E \<and> x \<in> C \<and> y \<in> X" 
        by (metis \<open>X \<subseteq> Vs E \<and> barrier E X\<close> diff_odd_components_connected less.prems(1) less.prems(2))
      then have " {connected_component (graph_diff E X) x, {y}} \<in> ?G'" 
        using \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_not_in_X by fastforce
      have "C = connected_component (graph_diff E X) x" 
        by (metis \<open>C \<in> diff_odd_components E X\<close> \<open>{x, y} \<in> E \<and> x \<in> C \<and> y \<in> X\<close> diff_odd_components_is_component less.prems(1))
      then have "{C, {y}} \<in> ?G'" 
        using \<open>{connected_component (graph_diff E X) x, {y}} \<in> {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> by blast
      then show "C \<in> Vs ?G'" 
        by (meson edges_are_Vs)
    qed
    have "\<forall> e \<in> ?G'. \<exists> u v.  e= {u, v}  \<and> (u \<in> (diff_odd_components E X) \<and> v \<in> Vs ?G' - (diff_odd_components E X))"
    proof
      fix e
      assume "e \<in> ?G'"
      then obtain x y where "{x, y} \<in> E \<and>  x \<notin> X \<and>  y \<in> X \<and> e = {connected_component (graph_diff E X) x, {y}}"
        by auto 
      then have "connected_component (graph_diff E X) x \<in> (diff_odd_components E X)"
        by (smt (verit, ccfv_SIG) Union_eq Vs_def \<open>diff_odd_components E X = {C. \<exists>x\<in>Vs E - X. C = connected_component (graph_diff E X) x}\<close> insert_Collect mem_Collect_eq set_diff_eq singleton_conv)
      have "{y} \<in> Vs ?G'" 
        using \<open>{x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e = {connected_component (graph_diff E X) x, {y}}\<close> by auto
      have "{y} \<notin> (diff_odd_components E X)" 
        by (metis IntI \<open>{x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e = {connected_component (graph_diff E X) x, {y}}\<close> diff_odd_components_not_in_X empty_iff singletonI)
      then have "{y} \<in> Vs ?G' - (diff_odd_components E X)" 
        by (simp add: \<open>{y} \<in> Vs ?G'\<close>)
      then show "\<exists> u v.  e= {u, v}  \<and> (u \<in> (diff_odd_components E X) \<and> v \<in> Vs ?G' - (diff_odd_components E X))"
        
        using \<open>connected_component (graph_diff E X) x \<in> diff_odd_components E X\<close> \<open>{x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e = {connected_component (graph_diff E X) x, {y}}\<close> by blast
    qed

    then have "partitioned_bipartite ?G' (diff_odd_components E X)" unfolding partitioned_bipartite_def
      by (metis (no_types, lifting) \<open>diff_odd_components E X \<subseteq> Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close> \<open>graph_invar {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}}\<close>)

    have "((card  (diff_odd_components E X)) = card (Vs ?G' - (diff_odd_components E X)))"
    proof - 
      have "card  (diff_odd_components E X) = card X" 
        by (simp add: \<open>card (diff_odd_components E X) = card X\<close>)
     
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
     
  
  have " card (Vs ?G' - (diff_odd_components E X)) = card X" 
    using \<open>Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} - diff_odd_components E X = (\<Union>x\<in>X. {{x}})\<close> \<open>card (\<Union>x\<in>X. {{x}}) = card X\<close> by presburger

  then show ?thesis 
    using \<open>card (diff_odd_components E X) = card X\<close> by presburger
qed
  
  
  
  
  
  
  
  
  
  have "\<exists>M. perfect_matching ?G' M"
    proof(rule ccontr)
      assume "\<nexists>M. perfect_matching ?G' M" 
      then have "\<not> (\<forall>A \<subseteq>  (diff_odd_components E X). card (reachable ?G' A) \<ge> card A \<and>
                   ((card  (diff_odd_components E X)) = card (Vs ?G' - (diff_odd_components E X))))"
        using frobeneus_matching[of ?G' "(diff_odd_components E X)" ] 
            `partitioned_bipartite ?G' (diff_odd_components E X)` 
        by blast
      
      then have "\<exists> A\<subseteq>  (diff_odd_components E X). card (reachable ?G' A) < card A \<or>
                   ((card  (diff_odd_components E X)) \<noteq> card (Vs ?G' - (diff_odd_components E X)))"
        using le_less_linear by blast

      then obtain A where  " A\<subseteq>  (diff_odd_components E X) \<and> card (reachable ?G' A) < card A" 
        using \<open>card (diff_odd_components E X) = card (Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} - diff_odd_components E X)\<close> by blast
      
      have "(reachable ?G' (diff_odd_components E X)) = Vs ?G' - (diff_odd_components E X)"
        using reachble_bipartite[of ?G' "(diff_odd_components E X)"]
          `partitioned_bipartite ?G' (diff_odd_components E X)` 
        
        by fastforce
      have "(reachable ?G' A) \<subseteq> (reachable ?G' (diff_odd_components E X))" using 
      reachable_subset[of A "(diff_odd_components E X)"]  
        using \<open>A \<subseteq> diff_odd_components E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> by blast
      then have "(reachable ?G' A) \<subseteq> Vs ?G' - (diff_odd_components E X)" 
        
        by (simp add: \<open>reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} (diff_odd_components E X) = Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} - diff_odd_components E X\<close>)


      then have "(reachable ?G' A) \<subseteq> (\<Union>x\<in>X. ?f x)" 
        by (simp add: \<open>Vs {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} - diff_odd_components E X = (\<Union>x\<in>X. {{x}})\<close>)
     
      have "(\<Union>x\<in>X. ?f x) = {{x} |x. x \<in> X}" using  singleton_set_is_union_singletons[of X]
        by (meson \<open>X \<subseteq> Vs E \<and> barrier E X\<close> less.prems(1) rev_finite_subset)

      then have "(reachable ?G' A) \<subseteq> {{x} |x. x \<in> X}" 
        using \<open>reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A \<subseteq> (\<Union>x\<in>X. {{x}})\<close> by presburger

     
      let ?ReachA = "(\<lambda> A. {x. {x}\<in>(reachable ?G' A)})"
      have "finite A" 
        using \<open>A \<subseteq> diff_odd_components E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> diff_components_finite finite_subset less.prems(1) by auto
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
       
       by (metis IntI \<open>A \<subseteq> diff_odd_components E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> diff_odd_components_not_in_X empty_iff insertCI subsetD)

     
     
   }
   fix x x'
   assume    " {x', x} \<in> E"
       "connected_component (graph_diff E X) x' \<in> A"
       "x \<in> X"
   then have " {connected_component (graph_diff E X) x', {x}} \<in> ?G'"
     using IntI \<open>A \<subseteq> diff_odd_components E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> diff_odd_components_not_in_X empty_iff in_own_connected_component mem_Collect_eq subsetD by fastforce
 
   then   have "x \<in> (?ReachA A)"  unfolding reachable_def 
     by (smt (verit, best) \<open>A \<subseteq> diff_odd_components E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> \<open>connected_component (graph_diff E X) x' \<in> A\<close> \<open>x \<in> X\<close> diff_odd_components_not_in_X disjoint_insert(2) insertCI insert_Diff mem_Collect_eq subset_iff)


   
   then  show " \<exists>u\<in>A. \<exists>e\<in>?G'. {x} \<noteq> u \<and> u \<in> e \<and> {x} \<in> e" unfolding reachable_def
     
     by blast
 qed (auto)


      have "A \<subseteq> diff_odd_components E (?ReachA A)"
      proof
        fix C
        assume "C \<in> A" 
        then have "C \<in>  (diff_odd_components E X)" 
          using \<open>A \<subseteq> diff_odd_components E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> by blast
        have "C \<noteq> {}" 
          using \<open>C \<in> diff_odd_components E X\<close> less.prems(1) odd_components_nonempty by auto
        then obtain u where "u \<in> C" 
          by blast
        then have "connected_component (graph_diff E X) u = C" 
          by (simp add: \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_is_component less.prems(1))
       
            have "\<forall>y\<in>connected_component (graph_diff E (?ReachA A)) u. y \<notin> X"
            proof
              fix y
              assume "y\<in>connected_component (graph_diff E (?ReachA A)) u" 
              show "y\<notin>X"
              proof(cases "y=u")
                case True
                then show ?thesis 
                  using \<open>C \<in> diff_odd_components E X\<close> \<open>u \<in> C\<close> diff_odd_components_not_in_X by blast
next
case False

  then obtain p where  " walk_betw (graph_diff E (?ReachA A)) y p u"
    using `y\<in>connected_component (graph_diff E (?ReachA A)) u`
                unfolding connected_component_def 
                using mem_Collect_eq walk_symmetric by fastforce


              then  have "\<forall>x\<in>set p. x \<in> connected_component (graph_diff E (?ReachA A)) u" 
                
                by (metis (no_types, lifting) \<open>y \<in> connected_component (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) u\<close> connected_components_member_eq vertices_path_in_component)
              have "u \<notin> X" 
                using \<open>C \<in> diff_odd_components E X\<close> \<open>u \<in> C\<close> diff_odd_components_not_in_X by auto
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
      
      using \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_are_components less.prems(1) by fastforce
    then have "odd (card C)" by auto
   then have "C \<in> {C. \<exists> v\<in>Vs E-X. connected_component (graph_diff E (?ReachA A)) v = C \<and> odd (card C)}"
            using \<open>C \<in> diff_odd_components E X\<close> \<open>\<forall>y\<in>connected_component (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) u. y \<notin> X\<close> \<open>connected_component (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) u = C\<close> \<open>u \<in> C\<close> component_in_E insert_Diff insert_subset mem_Collect_eq by fastforce

          then show "C \<in>  diff_odd_components E (?ReachA A)" 
using diff_odd_components_are_components[of E " (?ReachA A)"] 
  by (smt (z3) DiffI \<open>C \<in> diff_odd_components E X\<close> \<open>\<forall>y\<in>connected_component (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) u. y \<notin> X\<close> \<open>connected_component (graph_diff E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A}) u = C\<close> \<open>u \<in> C\<close> \<open>{x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A} \<subseteq> X\<close> component_in_E less.prems(1) mem_Collect_eq subsetD)
qed


  then  have "card A \<le> card (diff_odd_components E (?ReachA A))"
    
    by (simp add: card_mono diff_components_finite less.prems(1))

  have "card A > card (?ReachA A)" 
    using \<open>A \<subseteq> diff_odd_components E X \<and> card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A) < card A\<close> \<open>card {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A} = card (reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A)\<close> by presburger

  then have "card (?ReachA A) < card (diff_odd_components E (?ReachA A))"
    
    using \<open>card A \<le> card (diff_odd_components E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A})\<close> by linarith
  have "(?ReachA A) \<subseteq> Vs E" 
    using \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>{x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A} \<subseteq> X\<close> by blast
  then have "card (?ReachA A) \<ge> card (diff_odd_components E (?ReachA A))"
  using assms(2)  unfolding tutte_condition_def 
    
    by (meson less.prems(2) tutte_condition_def)

 then show False 
   using \<open>card {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A} < card (diff_odd_components E {x. {x} \<in> reachable {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} A})\<close> not_less by blast
qed



                                
          
    then obtain M' where "perfect_matching ?G' M'" by auto

    let ?Z2 = "{C. \<exists> x y. C = {c . \<exists> e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x}
             \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}"

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

    have "finite ?Z2" sorry
    have "finite (Vs ?Z2)" sorry
    have "\<forall>a1 \<in>?Z2.\<forall>a2\<in>?Z2. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}" sorry
    have "\<forall>a\<in>?Z2. \<exists>b\<in> Vs ?Z2. b \<in> a" sorry
    then  have "\<exists>Z' \<subseteq> Vs ?Z2. \<forall>C \<in> ?Z2. \<exists>!z \<in> Z'. z \<in> C"
      using yfsdf2[of ?Z2] `finite ?Z2` `\<forall>a1 \<in>?Z2.\<forall>a2\<in>?Z2. a1 \<noteq> a2 \<longrightarrow> a1 \<inter> a2 = {}`
        `finite (Vs ?Z2)` 
      by blast
    then obtain Z' where "Z' \<subseteq> Vs ?Z2 \<and> ( \<forall>C \<in> ?Z2. \<exists>!z \<in> Z'. z \<in> C)" by auto


    let ?M' = "{e. \<exists> x y. e = {x, y} \<and> e \<in> E \<and> {connected_component (graph_diff E X) x, {y}} \<in> M' \<and> x \<in> Z'}"



    have "\<forall>C \<in> (diff_odd_components E X). 
      \<exists>M. perfect_matching (graph_diff (component_edges E C) Z') M"
    proof
      fix C
      assume "C \<in> (diff_odd_components E X)"
      have "\<exists>x y. x \<in> C \<and> y \<in> X \<and> {x, y} \<in> E" 
        using "less.prems"(2) "less.prems"(2) \<open>C \<in> diff_odd_components E X\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> diff_odd_components_connected 

        using less.prems(1) by fastforce
      then obtain x y where "x \<in> C \<and> y \<in> X \<and> {x, y} \<in> E" by auto
      then have "connected_component (graph_diff E X) x = C" 
        by (meson "less.prems"(1) \<open>C \<in> diff_odd_components E X\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> diff_odd_components_is_component)
      then have "{C, {y}} \<in> ?G'" 
        using \<open>x \<in> C \<and> y \<in> X \<and> {x, y} \<in> E\<close> 
        using \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_not_in_X by fastforce
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
        using \<open>C \<in> diff_odd_components E X\<close> \<open>C \<in> e \<and> e \<in> M'\<close> diff_odd_components_not_in_X by fastforce
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
                     \<and> c \<in> connected_component (graph_diff E X) x'}
             \<and> {connected_component (graph_diff E X) x', {y'}} \<in> M'"
      proof
        show "\<exists>y'a. {c. \<exists>e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} =
          {c. \<exists>e. e \<in> E \<and> e = {c, y'a}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} \<and>
          {connected_component (graph_diff E X) x', {y'a}} \<in> M'"
        proof
          show "{c. \<exists>e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} =
    {c. \<exists>e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} \<and>
    {connected_component (graph_diff E X) x', {y'}} \<in> M'"

            using \<open>?C' = {c. \<exists>e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} \<and> {connected_component (graph_diff E X) x', {y'}} \<in> M'\<close> by blast
        qed
      qed
      then have "?C' \<in> ?Z2" 
        by blast
      have " ( \<forall>C \<in> ?Z2. \<exists>!z \<in> Z'. z \<in> C)" 
        using \<open>Z' \<subseteq> Vs {{c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'} \<and> (\<forall>C\<in>{{c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'}. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> by linarith

       
      then have " \<exists>!z \<in> Z'. z \<in> ?C'" 
        by (metis (no_types, lifting) \<open>{c. \<exists>e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'} \<in> {{c. \<exists>e. e \<in> E \<and> e = {c, y}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'}\<close>)
      have "Z' \<subseteq> Vs ?Z2" 
        using \<open>Z' \<subseteq> Vs ?Z2 \<and> (\<forall>C\<in>{{c. \<exists>e. e \<in> E \<and> e = {c, y}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'}. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> by linarith

      have "Vs ?Z2 \<inter> C = ?C'"
        using possible_connected_vertices_in_expanded_graph_intersection[of E X C x' y' M']
        using \<open>C \<in> diff_odd_components E X\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>perfect_matching {e'. \<exists>x y. {x, y} \<in> E \<and> x \<notin> X \<and> y \<in> X \<and> e' = {connected_component (graph_diff E X) x, {y}}} M'\<close> \<open>x' \<in> C\<close> \<open>{connected_component (graph_diff E X) x', {y'}} \<in> M'\<close> less.prems(1) perfect_matching_def by auto

    
      then have "\<exists>!z \<in> Z'. z \<in> C"  
        by (smt (verit) Int_iff \<open>Z' \<subseteq> Vs {{c. \<exists>e. e \<in> E \<and> e = {c, y}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'}\<close> \<open>\<exists>!z. z \<in> Z' \<and> z \<in> {c. \<exists>e. e \<in> E \<and> e = {c, y'}  \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x'}\<close> subset_eq)

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

      have "diff_odd_components (component_edges (graph_diff E X) C) {z} = {}"
        using max_barrier_add_vertex_empty_odd_components[of E X C z] 
        using X_max \<open>C \<in> diff_odd_components E X\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> less.prems(1) less.prems(2) by fastforce



      then have "diff_odd_components (component_edges E C) {z} = {}"
        using \<open>diff_odd_components (component_edges (graph_diff E X) C) {z} = {}\<close> 

        by (simp add: \<open>C \<in> diff_odd_components E X\<close> component_edges_same_in_diff) 
      have "Vs (graph_diff (component_edges E C) {z}) = C - {z}"
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
          have "singleton_in_diff (component_edges (graph_diff E X) C) {z} = {}"

            using \<open>diff_odd_components (component_edges (graph_diff E X) C) {z} = {}\<close> diff_odd_components_def by auto
          then have "singleton_in_diff (component_edges E C) {z} = {}"

            by (simp add: \<open>C \<in> diff_odd_components E X\<close> component_edges_same_in_diff)

          then have "\<nexists> v.  v \<in> Vs (component_edges E C) \<and> 
              v \<notin> {z} \<and> v \<notin> Vs (graph_diff (component_edges E C) {z})"
            unfolding singleton_in_diff_def  
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
            then have "C \<in> singleton_in_diff E X" 
              by (metis UnE \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_def)
            then have "C = {z}" unfolding singleton_in_diff_def 
              using \<open>z \<in> Z' \<and> z \<in> C\<close> by fastforce
            then show ?thesis 
              using \<open>x \<in> C - {z}\<close> by blast
          qed
        qed
      qed




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

        by (metis \<open>C \<in> diff_odd_components E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> component_in_E finite_Diff less.prems(1) rev_finite_subset subset_iff)

      have "card (Vs (graph_diff (component_edges E C) {z})) < card (Vs E)" 
        by (metis (no_types, lifting) Diff_insert_absorb \<open>C \<in> diff_odd_components E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> component_in_E insert_subset less.prems(1) mk_disjoint_insert psubsetI psubset_card_mono)

      have " tutte_condition ?Cz \<Longrightarrow>
  Ex (perfect_matching ?Cz)"  using "less.hyps"(1) 
        using \<open>card (Vs (graph_diff (component_edges E C) {z})) < card (Vs E)\<close> \<open>graph_invar (graph_diff (component_edges E C) {z})\<close> by presburger


      have "\<exists>M. (perfect_matching
       (graph_diff (component_edges E C) {z}) M)" 
      proof(cases "C \<in> odd_components (graph_diff E X)")
        case True
        then have "\<exists> c \<in> Vs (graph_diff E X).
              connected_component (graph_diff E X) c = C \<and> odd (card C)"
          unfolding odd_components_def 
          by blast
        have " Vs (component_edges E C) = C" 
          by (meson True \<open>X \<subseteq> Vs E \<and> barrier E X\<close> less.prems(1) vertices_of_edges_in_component_same)

        show ?thesis 
        proof(rule ccontr)
          assume " \<nexists>M. perfect_matching
         (graph_diff (component_edges E C) {z}) M"
          then have "\<not> tutte_condition ?Cz" 
            using \<open>tutte_condition (graph_diff (component_edges E C) {z}) \<Longrightarrow> Ex (perfect_matching (graph_diff (component_edges E C) {z}))\<close> by blast
          then have "\<exists>Y\<subseteq> Vs ?Cz. card (diff_odd_components ?Cz Y) > card Y"

            by (meson le_less_linear tutte_condition_def)
          then obtain Y where "Y\<subseteq> Vs ?Cz \<and> card (diff_odd_components ?Cz Y) > card Y" by auto
          have "Vs ?Cz = C - {z}" 
            using \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> by auto
          have "odd (card C)" 
            using \<open>\<exists>c\<in>Vs (graph_diff E X). connected_component (graph_diff E X) c = C \<and> odd (card C)\<close> by blast

          have "even (card (C - {z}))" using `odd (card C)` 
            by (metis \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>graph_invar (graph_diff (component_edges E C) {z})\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> card_Diff_singleton even_diff_nat infinite_remove odd_add odd_one)

          then have "even (card (diff_odd_components ?Cz Y) - card Y)"

            by (metis \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (diff_odd_components (graph_diff (component_edges E C) {z}) Y)\<close> \<open>graph_invar (graph_diff (component_edges E C) {z})\<close> diff_odd_component_parity' even_diff_nat linorder_le_less_linear)
          then have "card (diff_odd_components ?Cz Y) - card Y \<ge> 2" 
            by (metis (no_types, lifting) One_nat_def Suc_leI \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (diff_odd_components (graph_diff (component_edges E C) {z}) Y)\<close> add_0_right add_Suc_right diff_diff_cancel diff_zero le_eq_less_or_eq nat_dvd_1_iff_1 nat_neq_iff one_add_one zero_order(2))
          then have "card (diff_odd_components ?Cz Y) \<ge> card Y + 2" 
            by linarith

          have "diff_odd_components E (X \<union> (Y\<union>{z})) = diff_odd_components E X - {C} \<union> 
       diff_odd_components (component_edges (graph_diff E X) C) (Y\<union>{z})" 
            by (smt (verit, ccfv_threshold) Diff_empty Un_insert_right \<open>C \<in> diff_odd_components E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (diff_odd_components (graph_diff (component_edges E C) {z}) Y)\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> add_subset_change_odd_components boolean_algebra_cancel.sup0 empty_not_insert insert_subset less.prems(1) less.prems(2) subset_Diff_insert)
          have "(diff_odd_components E X - {C}) \<inter> 
                (diff_odd_components (component_edges (graph_diff E X) C) (Y\<union>{z})) = {}"

            using new_components_intersection_old_is_empty[of E X C "(Y\<union>{z})"] 
            by (metis Diff_empty Un_subset_iff \<open>C \<in> diff_odd_components E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (diff_odd_components (graph_diff (component_edges E C) {z}) Y)\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> insert_Diff insert_Diff_single insert_is_Un less.prems(1) less.prems(2) subset_Diff_insert subset_Un_eq)

          then have "card (diff_odd_components E (X \<union> (Y\<union>{z}))) = card (diff_odd_components E X - {C})
+ card (diff_odd_components (component_edges (graph_diff E X) C) (Y\<union>{z}))" 

            by (metis \<open>diff_odd_components E (X \<union> (Y \<union> {z})) = diff_odd_components E X - {C} \<union> diff_odd_components (component_edges (graph_diff E X) C) (Y \<union> {z})\<close> card_Un_disjoint diff_components_finite finite_Un less.prems(1))
          have " card (diff_odd_components E X - {C}) = card (diff_odd_components E X) - 1" 
            by (simp add: \<open>C \<in> diff_odd_components E X\<close> diff_components_finite less.prems(1))
          then have " card (diff_odd_components E X - {C}) = card X - 1" 
            using \<open>card (diff_odd_components E X) = card X\<close> by presburger



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

          then have " singleton_in_diff (component_edges E C) (Y \<union> {z}) =
  singleton_in_diff (graph_diff (component_edges E C) {z}) Y"
            unfolding singleton_in_diff_def 
            using \<open>\<forall>v. (v \<in> Vs (component_edges E C) \<and> v \<notin> Y \<union> {z}) = (v \<in> Vs (graph_diff (component_edges E C) {z}) \<and> v \<notin> Y)\<close> by fastforce


          have "diff_odd_components (component_edges E C) (Y\<union>{z}) =
       diff_odd_components ?Cz Y" unfolding diff_odd_components_def 

            using \<open>odd_components (graph_diff (component_edges E C) (Y \<union> {z})) = odd_components (graph_diff (graph_diff (component_edges E C) {z}) Y)\<close> \<open>singleton_in_diff (component_edges E C) (Y \<union> {z}) = singleton_in_diff (graph_diff (component_edges E C) {z}) Y\<close> by presburger


          then have "card (diff_odd_components E (X \<union> (Y\<union>{z}))) = card X - 1 + card (diff_odd_components ?Cz Y)"

            using \<open>card (diff_odd_components E (X \<union> (Y \<union> {z}))) = card (diff_odd_components E X - {C}) + card (diff_odd_components (component_edges (graph_diff E X) C) (Y \<union> {z}))\<close> \<open>card (diff_odd_components E X - {C}) = card (diff_odd_components E X) - 1\<close> \<open>card (diff_odd_components E X) = card X\<close>

            by (simp add: \<open>card (diff_odd_components E (X \<union> (Y \<union> {z}))) = card (diff_odd_components E X - {C}) + card (diff_odd_components (component_edges (graph_diff E X) C) (Y \<union> {z}))\<close> \<open>card (diff_odd_components E X - {C}) = card (diff_odd_components E X) - 1\<close> \<open>card (diff_odd_components E X) = card X\<close> \<open>diff_odd_components (component_edges E C) (Y \<union> {z}) = diff_odd_components (graph_diff (component_edges E C) {z}) Y\<close> \<open>C \<in> diff_odd_components E X\<close> component_edges_same_in_diff)

          then have "card (diff_odd_components E (X \<union> (Y\<union>{z}))) \<ge> card X - 1 + card Y + 2" 
            using \<open>card Y + 2 \<le> card (diff_odd_components (graph_diff (component_edges E C) {z}) Y)\<close> by linarith
          then have "card (diff_odd_components E (X \<union> (Y\<union>{z}))) \<ge> card X + card Y + 1" 
            by linarith
          have "X \<inter> (Y\<union>{z}) = {}"
            by (smt (verit, del_insts) Diff_empty Int_Un_distrib Int_Un_eq(3) Int_Un_eq(4) Int_empty_right Int_insert_left_if1 Int_insert_right_if0 Un_Int_assoc_eq Un_subset_iff \<open>C \<in> diff_odd_components E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (diff_odd_components (graph_diff (component_edges E C) {z}) Y)\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> diff_odd_components_not_in_X insert_not_empty mk_disjoint_insert subset_Diff_insert sup_commute)

          then have "card (X \<union> (Y\<union>{z})) = card X + card(Y\<union>{z})" 
            by (meson \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (diff_odd_components (graph_diff (component_edges E C) {z}) Y)\<close> \<open>graph_invar (graph_diff (component_edges E C) {z})\<close> card_Un_disjoint finite.emptyI finite.insertI finite_Un finite_subset less.prems(1))
          have "(Y\<inter>{z}) = {}" 
            using \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (diff_odd_components (graph_diff (component_edges E C) {z}) Y)\<close> by blast
          then have "card (X \<union> (Y\<union>{z})) = card X + card Y + 1" 
            by (metis \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (diff_odd_components (graph_diff (component_edges E C) {z}) Y)\<close> \<open>card (X \<union> (Y \<union> {z})) = card X + card (Y \<union> {z})\<close> \<open>graph_invar (graph_diff (component_edges E C) {z})\<close> card_Un_disjoint finite.emptyI finite.insertI finite_subset group_cancel.add1 is_singletonI is_singleton_altdef)

          have "card (diff_odd_components E (X \<union> (Y\<union>{z}))) \<le> card (X \<union> (Y\<union>{z}))" 
            using `tutte_condition E` 
            by (smt (verit, ccfv_threshold) Un_Int_assoc_eq \<open>C \<in> diff_odd_components E X\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (diff_odd_components (graph_diff (component_edges E C) {z}) Y)\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> component_in_E inf.absorb_iff2 insert_Diff insert_subset order_trans sup_bot_right tutte_condition_def)
          then have "card (diff_odd_components E (X \<union> (Y\<union>{z}))) = card (X \<union> (Y\<union>{z}))" 
            using \<open>card (X \<union> (Y \<union> {z})) = card X + card Y + 1\<close> \<open>card X + card Y + 1 \<le> card (diff_odd_components E (X \<union> (Y \<union> {z})))\<close> le_antisym by presburger
          then have "barrier E (X \<union> (Y\<union>{z}))" 
            by (simp add: barrier_def)
          have "X \<subseteq> X \<union> (Y\<union>{z})" 
            by auto
          have "X \<union> (Y\<union>{z}) \<subseteq> Vs E" 
            by (smt (verit, del_insts) Diff_empty Un_subset_iff \<open>C \<in> diff_odd_components E X\<close> \<open>Vs (component_edges E C) = C\<close> \<open>Vs (graph_diff (component_edges E C) {z}) = C - {z}\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>Y \<subseteq> Vs (graph_diff (component_edges E C) {z}) \<and> card Y < card (diff_odd_components (graph_diff (component_edges E C) {z}) Y)\<close> \<open>graph_invar (component_edges E C)\<close> \<open>z \<in> Z' \<and> z \<in> C\<close> component_in_E diff_is_union_elements insert_subset subset_Diff_insert sup_bot_right)

          then show False using X_max 
            by (metis (no_types, lifting) Int_absorb1 Un_empty \<open>X \<inter> (Y \<union> {z}) = {}\<close> \<open>X \<subseteq> X \<union> (Y \<union> {z})\<close> \<open>barrier E (X \<union> (Y \<union> {z}))\<close> insert_not_empty mem_Collect_eq subset_Un_eq sup_commute)
        qed


      next
        case False
        then have "C \<in> singleton_in_diff E X" 
          by (metis UnE \<open>C \<in> diff_odd_components E X\<close> diff_odd_components_def)
        then have "\<exists> v. C = {v} \<and> v \<in> Vs E \<and> v \<notin> X \<and> v \<notin> Vs (graph_diff E X)"
          unfolding singleton_in_diff_def 
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
    proof(safe)

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
          using \<open>Vs {{c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'} \<inter> X = {}\<close> \<open>Z' \<subseteq> Vs {{c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'} \<and> (\<forall>C\<in>{{c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'}. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> empty_iff by auto

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
          using \<open>Z' \<subseteq> Vs {{c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'} \<and> (\<forall>C\<in>{{c. \<exists>e. e \<in> E \<and> e = {c, y} \<and> c \<notin> X \<and> c \<in> connected_component (graph_diff E X) x} | x y. {connected_component (graph_diff E X) x, {y}} \<in> M'}. \<exists>!z. z \<in> Z' \<and> z \<in> C)\<close> by blast
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
  

      show " x \<in> Vs {{x, y} |x y. x \<in> Z' \<and> {connected_component (graph_diff E X) x, {y}} \<in> M'}"
        sledgehammer



    have "?M2 \<subseteq> E" sorry
    have "perfect_matching ?M2 ?M2" sorry

    let ?E' = "{e. e \<inter> Vs ?M2 = {} \<and> e \<in> E}"
    let ?E'_comp = "{E'. \<exists> C \<in> (diff_odd_components E X). E' = {e. e \<subseteq> C \<and> e \<inter> Vs ?M2 = {} \<and> e \<in> E}}"
    have "\<forall>E' \<in> ?E'_comp. \<exists>M. perfect_matching E' M" sorry













    have "\<forall>C \<in> (diff_odd_components E X). finite C"
      by (meson "1.prems"(2) component_in_E finite_subset)
    have "\<forall>C \<in> (diff_odd_components E X). C \<noteq> {} " 
      by (smt (verit, ccfv_threshold) UnE diff_odd_components_def disjoint_insert(2) inf_bot_right mem_Collect_eq odd_card_imp_not_empty odd_components_def singleton_in_diff_def)
    then have "\<forall>C \<in> (diff_odd_components E X). \<exists>c. c\<in>C" by auto

    then have "\<exists>Z. \<forall>C \<in> (diff_odd_components E X).\<exists>c \<in> Z. c\<in>C" 
      by (metis Collect_const mem_Collect_eq)
    then have "\<exists>Z. (\<forall>C \<in> (diff_odd_components E X). \<exists>c \<in> Z. c\<in>C) \<and>
                   (\<forall>z \<in> Z. z \<in> Vs (diff_odd_components E X))" 
      by (metis vs_member_intro)
    then obtain Z where "(\<forall>C \<in> (diff_odd_components E X).\<exists>c \<in> Z. c\<in>C) \<and> (\<forall>z \<in> Z. z \<in> Vs (diff_odd_components E X))"     
      by meson

    then have "Z \<subseteq> Vs (diff_odd_components E X)" 
      by fastforce
    then have "\<forall>z \<in>Z. \<exists>C\<in> (diff_odd_components E X). z \<in> C" 
      by (meson \<open>(\<forall>C\<in>diff_odd_components E X. \<exists>c\<in>Z. c \<in> C) \<and> (\<forall>z\<in>Z. z \<in> Vs (diff_odd_components E X))\<close> vs_member_elim)
    have "\<forall>C\<in> (diff_odd_components E X). C \<subseteq> Vs E" 
      by (simp add: component_in_E)


    then have "Z \<subseteq> Vs E" 
      by (meson \<open>\<forall>z\<in>Z. \<exists>C\<in>diff_odd_components E X. z \<in> C\<close> subsetD subsetI)
    then have "finite Z" 
      using "1.prems"(2) finite_subset by auto

    have "\<exists>T\<subseteq>Z . \<forall>C\<in>(diff_odd_components E X).
       \<exists>b\<in>T. b \<in> C \<and> card (diff_odd_components E X) = card T"
      using yfsdf[of "(diff_odd_components E X)" Z] 
      by (smt (verit, best) "1.prems"(2) \<open>(\<forall>C\<in>diff_odd_components E X. \<exists>c\<in>Z. c \<in> C) \<and> (\<forall>z\<in>Z. z \<in> Vs (diff_odd_components E X))\<close> \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>finite Z\<close> barrier_def card_eq_0_iff diff_component_disjoint finite_subset)




    have "(\<forall>C \<in> (diff_odd_components E X).\<exists>c \<in> Z. c\<in>C)" 
      using \<open>(\<forall>C\<in>diff_odd_components E X. \<exists>c\<in>Z. c \<in> C) \<and> (\<forall>z\<in>Z. z \<in> Vs (diff_odd_components E X))\<close> by blast

    then have "card Z \<ge> card (diff_odd_components E X)"
      using  inj_cardinality[of "(diff_odd_components E X)" Z]
      by (metis (no_types, lifting) "1.prems"(2) \<open>X \<subseteq> Vs E \<and> barrier E X\<close> \<open>finite Z\<close> barrier_def card_eq_0_iff diff_component_disjoint finite_subset)

    then  have "\<exists>T \<subseteq> Z.  card T =  card (diff_odd_components E X)"
      by (meson obtain_subset_with_card_n)
    then obtain T where "T \<subseteq> Z \<and>  card T = card (diff_odd_components E X)" 



      then have "\<forall>C \<in> (diff_odd_components E X). card (C \<inter> Z) \<ge> 1" 
        by (metis One_nat_def Suc_leI \<open>\<forall>C\<in>diff_odd_components E X. \<exists>c\<in>Z. c \<in> C\<close> \<open>finite Z\<close> card_gt_0_iff disjoint_iff finite_Int)




      have "\<exists>T \<subseteq> Z. \<forall>C \<in> (diff_odd_components E X). card (C \<inter> T) = 1"
      proof(rule ccontr)
        assume "\<not> (\<exists>T\<subseteq>Z. \<forall>C\<in>diff_odd_components E X. card (C \<inter> T) = 1)"
        then have "\<forall>T\<subseteq>Z. \<exists>C\<in>diff_odd_components E X. card (C \<inter> T) \<noteq> 1"
          by meson
        then obtain T1 C1 where "T1 \<subseteq>Z \<and>  C1\<in>diff_odd_components E X \<and> card (C1 \<inter> T1) \<noteq> 1"

          by (meson Int_lower2)
        then have "card (C1 \<inter> T1) > 1" sledgehammer






          then have "\<exists>Z. \<forall>C \<in> (diff_odd_components E X). Z \<inter> C \<noteq> {}" 
            by (meson disjoint_iff)

          let ?Z = {a. a = 

          then have "\<exists>Z. \<forall>C \<in> (diff_odd_components E X).\<exists>c. Z \<inter> C = {c}"  
            obtain Z where "\<forall>C \<in> (diff_odd_components E X).\<exists>c.  Z\<inter>C = {c}" 










              then show False sledgehammer































end