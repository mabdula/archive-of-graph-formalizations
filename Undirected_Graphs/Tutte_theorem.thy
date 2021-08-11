theory Tutte_theorem
  imports Bipartite
begin

definition odd_components where
  "odd_components E = {C. \<exists> v \<in> Vs E. connected_component E v = C \<and> odd (card C)}"

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
  fixes f :: "'a set \<Rightarrow> 'a set" 
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
  then have "X \<subseteq> Vs M" using `perfect_matching E M` unfolding perfect_matching_def by auto
  have "graph_invar E" 
    using \<open>perfect_matching E M\<close> perfect_matching_def by auto
  let ?bridge_edges = "{e. e \<in> M \<and> (\<exists> x y. e = {x,y} \<and> (\<exists> C \<in> (diff_odd_components E X). x \<in> C) \<and> y \<in> X)}"

  have 1: "matching M" 
    using \<open>perfect_matching E M\<close> perfect_matching_def by blast 
  have "finite M"
    by (metis Vs_def \<open>perfect_matching E M\<close> finite_UnionD perfect_matching_def)
  then have "finite (Vs M)" 
    by (metis \<open>perfect_matching E M\<close> perfect_matching_def)
  let ?component_out_edges  = "\<lambda> C. {e. e \<in> M \<and> (\<exists> x y. e = {x,y} \<and>  y \<in> C \<and> x \<in> X)}"

  have 2:"\<forall> e \<in> E. card e = 2"
    by (meson \<open>perfect_matching E M\<close> card_edge perfect_matching_def)

  have "\<forall> C \<in> (diff_odd_components E X). C \<inter> X = {}"
  proof
    fix C
    assume "C \<in> (diff_odd_components E X)"
    show " C \<inter> X = {}"
    proof(rule ccontr)
      assume "C \<inter> X \<noteq> {}"
      then obtain c where "c \<in> C" "c \<in> X" by blast
      have "{c} \<notin> (singleton_in_diff E X)" unfolding singleton_in_diff_def
        using \<open>c \<in> X\<close> by blast
      show False
      proof(cases "C \<in> (odd_components (graph_diff E X))")
        case True
        then have "\<exists> v \<in> Vs (graph_diff E X). connected_component (graph_diff E X) v = C" 
          using odd_components_def by auto
        then show ?thesis
          by (smt (verit, del_insts) \<open>\<And>thesis. (\<And>c. \<lbrakk>c \<in> C; c \<in> X\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> disjoint_insert(2) graph_diff_def in_connected_component_in_edges mem_Collect_eq mk_disjoint_insert vs_member)
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
  qed
  have "\<forall> C \<in> (diff_odd_components E X). (?component_out_edges C) \<subseteq> M"
    by blast

  have 3:"\<forall> C \<in> (diff_odd_components E X). card (Vs (?component_out_edges C)) = 
      sum (\<lambda> e. card e) (?component_out_edges C)"
  proof 
    fix C
    assume "C \<in> (diff_odd_components E X)"
    then have "(?component_out_edges C) \<subseteq> M" by blast
    have "finite (Vs M)" 
      by (metis \<open>perfect_matching E M\<close> perfect_matching_def)
    show "card (Vs (?component_out_edges C)) = 
      sum (\<lambda> e. card e) (?component_out_edges C)" using werew
      using "1" \<open>finite (Vs M)\<close> \<open>{e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<subseteq> M\<close> by blast
  qed
  have " \<forall> C \<in> (diff_odd_components E X). C \<subseteq> Vs E"
    by (meson component_in_E)
  have "\<forall> C \<in> (diff_odd_components E X). finite (?component_out_edges C)" 
    by (simp add: \<open>finite M\<close>)
  have "\<forall> C \<in> (diff_odd_components E X). \<forall> e \<in> (?component_out_edges C). card e = 2" using 2
    using \<open>perfect_matching E M\<close> perfect_matching_def by auto

  then have "\<forall> C \<in> (diff_odd_components E X). sum (\<lambda> e. card e) (?component_out_edges C) = 
      sum (\<lambda> e. 2) (?component_out_edges C)"  by (meson sum.cong)

  then have "\<forall> C \<in> (diff_odd_components E X). card (Vs (?component_out_edges C)) = 
      sum (\<lambda> e. 2) (?component_out_edges C)" using 3
    by simp 
  then have "\<forall> C \<in> (diff_odd_components E X). card (?component_out_edges C) * 2 =
    sum (\<lambda> e. 2) (?component_out_edges C) " by simp

  then have "\<forall> C \<in> (diff_odd_components E X). card (?component_out_edges C) * 2 =
     card ( Vs (?component_out_edges C))" 
    by (metis (no_types, lifting) \<open>\<forall>C\<in>diff_odd_components E X. card (Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}) = (\<Sum>e | e \<in> M \<and> (\<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X). 2)\<close>)

  have 5:"\<forall> C \<in> (diff_odd_components E X). \<forall> e \<in> (?component_out_edges C).
      card (e \<inter> X) = 1"
    using Int_commute \<open>\<forall>C\<in>diff_odd_components E X. C \<inter> X = {}\<close> by fastforce
  then have "\<forall> C \<in> (diff_odd_components E X).
 card ((Vs (?component_out_edges C)) \<inter> X) = sum (\<lambda> e. card (e \<inter> X)) (?component_out_edges C)" 
    using werew2 `matching M` `finite (Vs M)`
      `\<forall> C \<in> (diff_odd_components E X). (?component_out_edges C) \<subseteq> M`
    using sum.cong by fastforce
  have "\<forall> C \<in> (diff_odd_components E X). sum (\<lambda> e. card (e \<inter> X)) (?component_out_edges C) =
      sum (\<lambda> e. 1) (?component_out_edges C)" using 5 
    by simp
  then have "\<forall> C \<in> (diff_odd_components E X). sum (\<lambda> e. card (e \<inter> X)) (?component_out_edges C) =
      card (?component_out_edges C)" 
    by fastforce
  then have "\<forall> C \<in> (diff_odd_components E X).
 card ((Vs (?component_out_edges C)) \<inter> X) =  card (?component_out_edges C)" 
    by (simp add: \<open>\<forall>C\<in>diff_odd_components E X. card (Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<inter> X) = (\<Sum>e | e \<in> M \<and> (\<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X). card (e \<inter> X))\<close>)

  then have "sum (\<lambda> C. card (?component_out_edges C)) (diff_odd_components E X) = 
            sum (\<lambda> C. card ((Vs (?component_out_edges C)) \<inter> X)) (diff_odd_components E X)"   
    by force


  have "\<Union>{C1. \<exists> C \<in> (diff_odd_components E X) .
          C1 = ((Vs (?component_out_edges C)) \<inter> X) } \<subseteq> X"
  proof
    fix x
    assume "x \<in> \<Union>{C1. \<exists> C \<in> (diff_odd_components E X). C1 = ((Vs (?component_out_edges C)) \<inter> X) }"
    then have "\<exists> C \<in> (diff_odd_components E X). x \<in> ((Vs (?component_out_edges C)) \<inter> X)"
      by blast
    then show "x \<in> X" 
      by blast
  qed

  have "( \<Union>C \<in>(diff_odd_components E X). (((Vs (?component_out_edges C)) \<inter> X))) \<subseteq> X "
  proof
    fix x
    assume "x \<in> ( \<Union>C \<in>(diff_odd_components E X). (((Vs (?component_out_edges C)) \<inter> X)))"
    then have "\<exists> C \<in> (diff_odd_components E X). x \<in> ((Vs (?component_out_edges C)) \<inter> X)"
      by blast
    then show "x \<in> X" 
      by blast
  qed
  let ?f = "(\<lambda> C. ((Vs (?component_out_edges C)) \<inter> X))"
  have "\<forall>C \<in> (diff_odd_components E X). finite ((Vs (?component_out_edges C)) \<inter> X)" 
    by (meson \<open>X \<subseteq> Vs M\<close> \<open>finite (Vs M)\<close> finite_Int finite_subset)
  have "finite (diff_odd_components E X)" 
    by (metis \<open>X \<subseteq> Vs E \<and> card X < card (diff_odd_components E X)\<close> card_eq_0_iff card_gt_0_iff less_imp_triv)

  have "\<forall> C1 \<in>(diff_odd_components E X). \<forall> C2 \<in> (diff_odd_components E X).
    C1 \<noteq> C2 \<longrightarrow> ((Vs (?component_out_edges C1)) \<inter> X) \<inter> ((Vs (?component_out_edges C2)) \<inter> X) = {}"
  proof
    fix C1 
    assume "C1 \<in>(diff_odd_components E X)"
    show " \<forall> C2 \<in> (diff_odd_components E X).
    C1 \<noteq> C2 \<longrightarrow> ((Vs (?component_out_edges C1)) \<inter> X) \<inter> ((Vs (?component_out_edges C2)) \<inter> X) = {}"
    proof
      fix C2
      assume "C2 \<in> (diff_odd_components E X)"
      show " C1 \<noteq> C2 \<longrightarrow> ((Vs (?component_out_edges C1)) \<inter> X) \<inter> ((Vs (?component_out_edges C2)) \<inter> X) = {}"
      proof
        assume "C1 \<noteq> C2"
        have "C1 \<inter> C2 = {}"
        proof(cases "C1 \<in> (odd_components (graph_diff E X))")
          case True
          then have "\<exists> v \<in> Vs (graph_diff E X). connected_component (graph_diff E X) v = C1"
            using odd_components_def by auto
          show ?thesis
          proof(rule ccontr)
            assume "C1 \<inter> C2 \<noteq> {}"
            then have "\<exists>u. u \<in> C1 \<inter> C2" by auto
            then  obtain u where "u \<in> C1 \<inter> C2" by auto
            then have "connected_component (graph_diff E X) u = C1" 
              by (metis IntD1 \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C1\<close> connected_components_member_eq)
            then have "card C1 > 1" using connected_component_not_singleton 
              by (smt (verit, del_insts) Vs_subset \<open>\<exists>v\<in>Vs (graph_diff E X). connected_component (graph_diff E X) v = C1\<close> \<open>perfect_matching E M\<close> finite_subset graph_diff_subset perfect_matching_def subset_eq)


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
        show "((Vs (?component_out_edges C1)) \<inter> X) \<inter> ((Vs (?component_out_edges C2)) \<inter> X) = {}"
        proof(rule ccontr)
          assume "((Vs (?component_out_edges C1)) \<inter> X) \<inter> ((Vs (?component_out_edges C2)) \<inter> X) \<noteq> {}"
          then have "\<exists>u. u \<in> ((Vs (?component_out_edges C1)) \<inter> X) \<inter> ((Vs (?component_out_edges C2)) \<inter> X)" by auto
          then obtain u where "u \<in> ((Vs (?component_out_edges C1)) \<inter> X) \<inter> ((Vs (?component_out_edges C2)) \<inter> X)" by auto
          then have "u \<in> X" by blast
          have "u \<in> (Vs (?component_out_edges C1))" 
            using \<open>u \<in> Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C1 \<and> x \<in> X} \<inter> X \<inter> (Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C2 \<and> x \<in> X} \<inter> X)\<close> by blast
          have"u \<in> (Vs (?component_out_edges C2))"
            using \<open>u \<in> Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C1 \<and> x \<in> X} \<inter> X \<inter> (Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C2 \<and> x \<in> X} \<inter> X)\<close> by blast



          then have "\<exists> e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C2 \<and> x \<in> X \<and> u \<in> e" 
            by (smt (verit) mem_Collect_eq vs_member)
          then obtain e2 where "e2 \<in> M \<and> (\<exists>x y. e2 = {x, y} \<and> y \<in> C2 \<and> x \<in> X) \<and> u \<in> e2" by auto

          then have "\<exists> e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C1 \<and> x \<in> X \<and> u \<in> e" 
            using `u \<in> (Vs (?component_out_edges C1)) ` by (smt (verit) mem_Collect_eq vs_member)
          then obtain e1 where "e1 \<in> M \<and> (\<exists>x y. e1 = {x, y} \<and> y \<in> C1 \<and> x \<in> X) \<and> u \<in> e1" by auto
          then have "e1 = e2" 
            by (meson "1" \<open>e2 \<in> M \<and> (\<exists>x y. e2 = {x, y} \<and> y \<in> C2 \<and> x \<in> X) \<and> u \<in> e2\<close> matching_unique_match)
          then show False 
            by (metis \<open>C1 \<in> diff_odd_components E X\<close> \<open>C1 \<inter> C2 = {}\<close> \<open>\<forall>C\<in>diff_odd_components E X. C \<inter> X = {}\<close> \<open>e1 \<in> M \<and> (\<exists>x y. e1 = {x, y} \<and> y \<in> C1 \<and> x \<in> X) \<and> u \<in> e1\<close> \<open>e2 \<in> M \<and> (\<exists>x y. e2 = {x, y} \<and> y \<in> C2 \<and> x \<in> X) \<and> u \<in> e2\<close> disjoint_iff doubleton_eq_iff)
        qed
      qed
    qed
  qed
  then  have "card ( \<Union>C \<in>(diff_odd_components E X). (((Vs (?component_out_edges C)) \<inter> X))) = 
    sum (\<lambda> C. card ((Vs (?component_out_edges C)) \<inter> X)) (diff_odd_components E X)"
    using union_card_is_sum[of  "(diff_odd_components E X)" ?f]
      `\<forall>C \<in> (diff_odd_components E X). finite ((Vs (?component_out_edges C)) \<inter> X)`
      `finite (diff_odd_components E X)` 
    by presburger

  then  have "sum (\<lambda> C. card ((Vs (?component_out_edges C)) \<inter> X)) (diff_odd_components E X) \<le> card X" 
    by (metis (no_types, lifting) \<open>(\<Union>C\<in>diff_odd_components E X. Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<inter> X) \<subseteq> X\<close> \<open>X \<subseteq> Vs M\<close> \<open>finite (Vs M)\<close> card_mono finite_subset)

  then have "sum (\<lambda> C. card (?component_out_edges C)) (diff_odd_components E X) \<le> card X"
    using \<open>(\<Sum>C\<in>diff_odd_components E X. card {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}) = (\<Sum>C\<in>diff_odd_components E X. card (Vs {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<inter> X))\<close> by presburger

  then have " \<forall> C \<in> (diff_odd_components E X). finite (?component_out_edges C)" 
    by (simp add: \<open>finite M\<close>) 
  have "\<forall> C \<in> (diff_odd_components E X). ?component_out_edges C \<noteq> {}"
  proof
    fix C
    assume "C \<in> (diff_odd_components E X)" 
    show "?component_out_edges C \<noteq> {}"
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
            using \<open>C \<in> diff_odd_components E X\<close> \<open>\<forall>C\<in>diff_odd_components E X. C \<subseteq> Vs E\<close> by blast
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
            using \<open>C \<in> diff_odd_components E X\<close> \<open>\<forall>C\<in>diff_odd_components E X. C \<inter> X = {}\<close> \<open>x \<in> C\<close> by blast
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
              by (metis "1" \<open>\<exists>y. y \<in> e \<and> y \<notin> C\<close> \<open>e \<in> M\<close> \<open>x \<in> C\<close> \<open>x \<in> e\<close> empty_iff insert_iff matching_unique_match)
          qed
        qed
        have " ((Vs M) \<inter> C) = C" 
          by (metis Int_absorb1 \<open>C \<in> diff_odd_components E X\<close> \<open>\<forall>C\<in>diff_odd_components E X. C \<subseteq> Vs E\<close> \<open>perfect_matching E M\<close> perfect_matching_def)
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
      then have "e \<in> ?component_out_edges C" 
        by (simp add: \<open>e \<in> M \<and> v \<in> e\<close>)

      then show ?thesis 
        by blast
    qed
  qed

  then have "\<forall> C \<in> (diff_odd_components E X). card( ?component_out_edges C) > 0" 
    by (simp add: \<open>\<forall>C\<in>diff_odd_components E X. {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X} \<noteq> {}\<close> \<open>\<forall>C\<in>diff_odd_components E X. finite {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}\<close> card_gt_0_iff)
  then have "\<forall> C \<in> (diff_odd_components E X). card( ?component_out_edges C) \<ge> 1"
    by (simp add: Suc_leI)
  then have "sum (\<lambda> C. card (?component_out_edges C)) (diff_odd_components E X) \<ge> 
    card (diff_odd_components E X)"
    using sum_mono by fastforce
  then have " card X \<ge>  card (diff_odd_components E X)"  
    using \<open>(\<Sum>C\<in>diff_odd_components E X. card {e \<in> M. \<exists>x y. e = {x, y} \<and> y \<in> C \<and> x \<in> X}) \<le> card X\<close> order_trans by blast

  then show False 
    using \<open>X \<subseteq> Vs E \<and> card X < card (diff_odd_components E X)\<close> not_less by blast
qed

end