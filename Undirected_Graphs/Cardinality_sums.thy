theory Cardinality_sums
  imports Bipartite
begin


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


lemma sum_card_connected_components:
  assumes "graph_invar E"
  shows "sum (\<lambda> x. card x) (connected_components E) = card (Vs E)"
proof -
  let ?Cs = "connected_components E"
  have "finite ?Cs"  
    by (simp add: assms finite_con_comps)
  moreover have "\<forall>C \<in> ?Cs. finite C" 
    by (meson assms connected_component_subs_Vs finite_subset)
  moreover have "\<forall> C1 \<in> ?Cs. \<forall> C2 \<in> ?Cs. C1 \<noteq> C2 \<longrightarrow>  C1 \<inter>  C2 = {}"
    by (simp add: connected_components_disj)
  ultimately have "sum (\<lambda> C. card C) ?Cs = card (\<Union>C\<in>?Cs. C)"
    using union_card_is_sum[of ?Cs "(\<lambda> C. C)"] by blast
  then show ?thesis using graph_component_partition[of E] assms by auto
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


end