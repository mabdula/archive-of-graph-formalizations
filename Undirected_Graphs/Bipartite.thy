theory Bipartite
  imports Berge "HOL.Set"
begin


definition bipartite where 
  "bipartite E \<equiv> graph_invar E \<and> (\<exists> X \<subseteq> Vs E. \<forall> e \<in> E. \<exists> u v. 
                                   e = {u, v} \<and> (u \<in> X \<and> v \<in> Vs E - X))" 

definition partitioned_bipartite where
  "partitioned_bipartite E X \<equiv> graph_invar E \<and> X \<subseteq> Vs E \<and> 
              (\<forall> e \<in> E. \<exists> u v. e = {u, v} \<and> (u \<in> X \<and> v \<in> Vs E - X))"

lemma part_biparite_is_bipartite: "partitioned_bipartite E X \<longrightarrow> bipartite E "
  unfolding  partitioned_bipartite_def bipartite_def by auto

definition perfect_matching where
  "perfect_matching E M \<equiv> graph_invar E \<and> matching M \<and> M \<subseteq> E \<and> Vs M = Vs E"

definition cover_matching where
  "cover_matching E M A \<equiv> graph_invar E \<and> matching M \<and> M \<subseteq> E \<and> A \<subseteq> Vs M"

definition reachable where
  "reachable E X  \<equiv> {v. \<exists> u \<in> X. \<exists> e \<in> E. v \<noteq> u \<and> u \<in> e \<and> v\<in> e}"

lemma perfect_matching_member[iff?]: "perfect_matching E M \<longleftrightarrow>
  graph_invar E \<and> matching M \<and> M \<subseteq> E \<and> Vs M = Vs E"
  unfolding perfect_matching_def by simp

lemma perfect_matchingE:
 "perfect_matching E M \<Longrightarrow>
   (\<lbrakk>graph_invar E; 
     matching M;
     M \<subseteq> E; 
     Vs M = Vs E\<rbrakk> \<Longrightarrow> R)
   \<Longrightarrow> R"
   by(auto simp: perfect_matching_member)

lemma perfect_matchingI:
  assumes "graph_invar E" "matching M" "M \<subseteq> E" "Vs M = Vs E"
  shows "perfect_matching E M" 
  using assms
  by (simp add: perfect_matching_member)


lemma card_edge:
  assumes "graph_invar E"
  shows "\<forall> e\<in> E. card e = 2" 
  by (simp add: assms card_2_iff)

lemma reachable_is_union:
  shows "reachable E X = \<Union> {r. \<exists> x\<in>X. r = (reachable E {x})}"
proof -
  show ?thesis unfolding reachable_def by blast
qed

lemma reachable_subset:
  assumes "A \<subseteq> X"
  shows "reachable E A \<subseteq> reachable E X"
  unfolding reachable_def 
  by (smt (verit, best) Collect_mono assms subset_eq)


lemma reachble_bipartite:
  assumes "partitioned_bipartite E A"
  shows "reachable E A = Vs E - A" 
proof -
  have partition:"\<forall> e \<in> E. \<exists> u v. e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs E - A)"
    using assms unfolding partitioned_bipartite_def by auto
  show ?thesis
  proof
    show "reachable E A \<subseteq> Vs E - A"
      unfolding reachable_def using partition insert_absorb insert_commute by fastforce
    show "Vs E - A \<subseteq> reachable E A"
    proof
      fix x
      assume "x \<in> Vs E - A"
      then obtain e where "e \<in> E \<and> x \<in> e" 
        using DiffD1 vs_member_elim  by metis
      then obtain u  where 2:"e = {u, x} \<and> (u \<in> A \<and> x \<in> Vs E - A) \<and> u \<noteq> x" 
        using partition \<open>x \<in> Vs E - A\<close> by fastforce
      then have "u \<in> e" 
        by blast
      then show "x \<in> reachable E A" 
        unfolding reachable_def 
        by (smt (verit) "2" \<open>e \<in> E \<and> x \<in> e\<close> mem_Collect_eq)
    qed
  qed
qed

lemma partitioned_bipartite_swap:
  assumes "partitioned_bipartite E A"
  shows "partitioned_bipartite E (Vs E - A)" 
  using assms unfolding partitioned_bipartite_def  by fastforce 

lemma reachable_intersection_is_empty:
  assumes "partitioned_bipartite E A"
  shows" \<forall>X \<subseteq> A. reachable E X \<inter> X = {}" 
proof safe
  fix X x
  assume "X \<subseteq> A" "x \<in> reachable E X" "x \<in> X"
  then show "x \<in> {}" 
    by (metis Diff_iff assms in_mono reachable_subset reachble_bipartite)
qed

lemma reachable_in_matching_singl:
  assumes "x \<in> Vs M"
  assumes "matching M"
  assumes" M \<subseteq> E"
  assumes "graph_invar E"
  shows "\<exists> v. (reachable M {x}) = {v}"
proof -
  have "\<exists>!e. e \<in> M \<and> x \<in> e"  using matching_def2 assms(2) assms(1)  by metis
  then obtain e where e: " e \<in> M \<and> x \<in> e" by auto
  then have x_one_edge:"\<forall> e' \<in> M. e' \<noteq> e \<longrightarrow> x \<notin> e'" 
    using \<open>\<exists>!e. e \<in> M \<and> x \<in> e\<close> by blast
  have "\<exists>v. (\<exists> e\<in>M. x \<in> e \<and> v\<in>e \<and> x \<noteq> v)"
    by (metis e assms(3) assms(4) insertCI subsetD)
  then obtain v where "(\<exists> e\<in>M. x\<in> e \<and> v \<in> e \<and> x \<noteq> v)" by auto
  have "\<forall>v'. (\<exists> e\<in>M. x\<in> e \<and> v'\<in>e \<and> x \<noteq> v') \<longrightarrow> v = v'" 
    by (metis x_one_edge \<open>\<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v\<close> assms(3)
        assms(4) empty_iff insert_iff subsetD)
  then have "\<exists>!v. \<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v" 
    using \<open>\<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v\<close> by blast
  then show ?thesis unfolding reachable_def 
    by auto
qed

lemma finite_reachable:
  assumes" M \<subseteq> E"
  assumes "graph_invar E"
  shows "finite (reachable M X)" 
proof -
  have 1: "finite (Vs M)"
    by (meson Vs_subset assms(2) assms(1) finite_subset)
  have 2: "(reachable M X) \<subseteq> Vs M" 
    by (smt (verit, best) mem_Collect_eq reachable_def subsetI vs_member)
  then show ?thesis using  1 2 
    using finite_subset by blast
qed

lemma vertex_not_in_source_then_not_reachable:
  assumes "matching M"
  assumes "{x, y} \<in> M"
  assumes "x \<notin> X"
  shows "y \<notin> reachable M X"
proof(rule ccontr)
  assume "\<not> y \<notin> reachable M X"
  then show False 
    unfolding reachable_def 
    by (smt (verit) assms insert_iff matching_unique_match mem_Collect_eq singleton_iff)
qed

lemma reachable_insert: "reachable M (insert x F) = reachable M F \<union> reachable M {x}"
  unfolding reachable_def  by blast

lemma card_ther_vertex:
  assumes "graph_invar E"
  assumes "matching M"
  assumes" M \<subseteq> E"
  assumes "X \<subseteq> Vs M"
  shows" card X = card (reachable M X)" 
proof -
  have "finite X" using assms(1)
    by (meson Vs_subset assms(3) assms(4) finite_subset)
  show ?thesis
    using \<open>finite X\<close> \<open>X \<subseteq> Vs M\<close>
  proof (induct X)
    case empty
    then show ?case 
      by (simp add: reachable_def)
  next
    case (insert x F)  
    then have "\<exists>v. reachable M {x} = {v}"
      using reachable_in_matching_singl assms(1-3) by fastforce
    then obtain v where v:"reachable M {x} = {v}" by auto
    then obtain e where e: "e \<in> M \<and> x \<in> e \<and> v \<in> e \<and> x \<noteq> v" 
      unfolding reachable_def by auto
    then have "e = {x, v}" 
      using assms(1) assms(3) by fastforce
    then have "v \<notin> reachable M F" 
      by (metis assms(2) e insert.hyps(2) vertex_not_in_source_then_not_reachable)
    then have  "reachable M {x} \<inter> reachable M F = {}" 
      by (simp add: v)
    then have card_sum_u: "card (reachable M {x}) + card( reachable M F) = 
                  card (reachable M {x} \<union> reachable M F)"
      by (metis finite_reachable assms(1) assms(3) card_Un_disjoint)
    have " reachable M (insert x F) = reachable M F \<union> reachable M {x}"
      by (meson reachable_insert)
    then have 3: "card (reachable M (insert x F)) = card (reachable M F) + 1"
      using v card_sum_u  by simp
    have "card (insert x F) = card F + 1"
      by (simp add: insert.hyps(1) insert.hyps(2)) 
    then show  "card (insert x F) = card (reachable M (insert x F))" using 3
      by (metis insert.hyps(3) insert.prems insert_subset)
  qed
qed

lemma part_bipart_of_cover_matching:
  fixes E :: "'a set set"
  fixes M
  assumes "partitioned_bipartite E A"
  assumes "cover_matching E M A"
  shows "partitioned_bipartite M A"
proof -
  have M_subs:"M \<subseteq> E" 
    using assms(2) unfolding cover_matching_def by auto
  have "graph_invar E"
    using assms(1) partitioned_bipartite_def by auto
  then have "graph_invar M"
    by (meson M_subs Vs_subset finite_subset subsetD)
  have "A \<subseteq> Vs M" 
    using assms(2) unfolding cover_matching_def by auto
  have "\<forall> e \<in> E. \<exists> u v. e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs E - A)"
    using assms(1) unfolding partitioned_bipartite_def by auto
  then have "\<forall>e \<in> M. \<exists> u v. e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs M - A)" 
    by (metis M_subs Diff_iff edges_are_Vs insert_commute subsetD)
  then show ?thesis 
    unfolding partitioned_bipartite_def
    using \<open>A \<subseteq> Vs M\<close> \<open>graph_invar M\<close>  by auto
qed

lemma hall_reachable:
  fixes E :: "'a set set"
  assumes "cover_matching E M A"
  shows "\<forall> X \<subseteq> A. card (reachable M X) = card X"
  using assms card_ther_vertex 
  unfolding cover_matching_def 
  by fastforce

lemma graph_subs_reach:
  assumes "M \<subseteq> E"
  shows "reachable M X \<subseteq> reachable E X"
  using assms subset_eq unfolding reachable_def  by fastforce

lemma hall1:
  fixes E :: "'a set set"
  assumes "cover_matching E M A"
  shows "\<forall> X \<subseteq> A. card (reachable E X) \<ge> card X"
proof rule+
  fix X
  assume "X \<subseteq> A"
  show "card X \<le> card (reachable E X)"
  proof -
    have 1:"finite (reachable M X)" 
      by (meson assms cover_matching_def finite_reachable)
    have "E \<subseteq> E" by auto
    then have 2:"finite (reachable E X)"
      by (meson assms cover_matching_def finite_reachable)
    have "reachable M X \<subseteq> reachable E X" 
      by (meson assms cover_matching_def graph_subs_reach)
    then have 3: "card (reachable M X) \<le> card (reachable E X)" using 1 2 
      by (simp add: card_mono)
    have "card X = card (reachable M X)" 
      by (metis \<open>X \<subseteq> A\<close> assms hall_reachable)
    then show ?thesis using 3 by auto
  qed
qed

lemma part_bipartite_diff:
  assumes "partitioned_bipartite E A"
  shows "partitioned_bipartite (E - X) (A \<inter> Vs (E - X))"
proof -
  let ?A' = "(A \<inter> Vs (E - X))" 
  have 2: "graph_invar (E - X)" 
    by (meson DiffD1 Diff_subset Vs_subset assms(1) finite_subset partitioned_bipartite_def)
  have  "A \<subseteq> Vs E" 
    by (metis assms partitioned_bipartite_def)
  have 3: "?A' \<subseteq> Vs (E - X)" by blast 
  have "( \<forall> e \<in> E - X. \<exists> u v.  e = {u, v} \<and> (u \<in> ?A' \<and> v \<in> Vs (E - X) - ?A'))"
  proof 
    fix e
    assume "e \<in> E - X"
    then obtain u v where u'_v': "e = {u, v} \<and> u \<noteq> v \<and> (u \<in> A \<and> v \<in> Vs E - A)"
      using `partitioned_bipartite E A` unfolding partitioned_bipartite_def 
      by (metis (no_types, lifting) Diff_iff \<open>e \<in> E - X\<close>)

    then have "u \<in> ?A'" 
      using UnionI u'_v' \<open>e \<in> E - X\<close> by auto

    then have "v \<in> Vs (E - X) - ?A'"
      using IntE u'_v' \<open>e \<in> E - X\<close> by auto
    then show "\<exists> ua va. e = {ua, va} \<and> (ua \<in> ?A' \<and> va \<in> Vs (E - X) - ?A')"
      using \<open>u \<in> ?A'\<close> u'_v' by blast
  qed
  then show ?thesis 
    using "2" 3 
    by (simp add: partitioned_bipartite_def)
qed

lemma reachable_remove_vert:
  assumes "graph_invar E"
  assumes "S \<inter> X = {}"
  shows "reachable E X \<subseteq> S \<union> reachable (E - {e. e \<in> E \<and> e \<inter> S \<noteq> {}}) X"
proof 
  fix y
  assume "y \<in> reachable E X"
  then obtain x e  where x_e: "x \<in> X \<and> e \<in> E \<and> x \<noteq> y \<and> x \<in> e \<and> y \<in> e" 
    unfolding reachable_def by blast
  then have e: "e = {x, y}"
    using assms(1) by fastforce
  then have "x \<notin> S" 
    using assms(2)  x_e by blast
  show "y \<in> S \<union> reachable (E - {e. e \<in> E \<and> e \<inter> S \<noteq> {}}) X" 
  proof(cases "y \<in> S")
    case True
    then show ?thesis 
      by blast
  next
    case False 
    then have "e \<inter> S = {}" 
      using `x \<notin> S` e by blast
    then have "e \<notin> {e. e \<in> E \<and> e \<inter> S \<noteq> {}}" 
      using False \<open>x \<notin> S\<close> e  
      by blast  
    then show ?thesis 
      unfolding reachable_def using False \<open>x \<notin> S\<close> x_e by force
  qed
qed

lemma reachable_un: "reachable E (Y \<union> X) = (reachable E Y - reachable E X) \<union> reachable E X"
  unfolding reachable_def using UnE by blast

lemma hall2:
  fixes E :: "'a set set"
  assumes "partitioned_bipartite E A"
  assumes  "\<forall> X \<subseteq> A. card (reachable E X) \<ge> card X"
  shows  "\<exists> M. cover_matching E M A"
  using assms(1) assms(2)
proof(induct "card A" arbitrary: A E rule: less_induct)
  case less
  have graphE: "graph_invar E" 
    using less.prems(1) unfolding partitioned_bipartite_def 
    by linarith
  have Asubs: "A \<subseteq> Vs E" 
    using less.prems(1) unfolding partitioned_bipartite_def
    by linarith
  then show ?case
  proof(cases "\<forall> X \<subset> A. X \<noteq> {} \<longrightarrow>  card (reachable E X) > card X")
    case True
    have 7:"\<forall> X \<subset> A. X \<noteq> {} \<longrightarrow> card (reachable E X) > card X"
      by (simp add: True)
    then show ?thesis
    proof (cases "E = {}") 
      case True
      then show ?thesis 
        by (metis cover_matching_def equals0D graphE Asubs matching_def subset_empty)
    next
      case False
      have "\<exists> e. e \<in> E" 
        using False by blast
      then obtain e where e:"\<exists>u v. e \<in> E \<and> e = {u, v} \<and> u \<in> A \<and> v \<in> Vs E - A"
        by (metis less.prems(1) partitioned_bipartite_def)
      then obtain u v where u_v: "e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs E - A)" 
        by auto
      then  have "(u \<in> A \<and> v \<in> Vs E - A)" by auto
      have " {u, v} \<in> E" using e u_v by fastforce
      let ?E_s = "E - {e. e \<in> E \<and> (u \<in> e \<or> v \<in> e)}"

      let ?A_s = "A \<inter> Vs ?E_s"
      let ?B_s = "Vs ?E_s - ?A_s"
      have 0:"?E_s \<subseteq> E" 
        by force
      have "u \<notin> Vs ?E_s"
        by (smt (verit, best) DiffD1 DiffD2 mem_Collect_eq vs_member)
      then have "u \<notin> ?A_s" by auto
      have "v \<notin> Vs ?E_s"
        by (smt (verit, best) DiffD1 DiffD2 mem_Collect_eq vs_member)
      then have "v \<notin> ?B_s" by auto
      have "card ?A_s < card A" 
        by (smt (verit, best) DiffD1 DiffD2 IntE \<open>u \<in> A \<and> v \<in> Vs E - A\<close> finite_subset inf_le1 
            graphE Asubs mem_Collect_eq psubsetI psubset_card_mono vs_member)

      have "partitioned_bipartite ?E_s ?A_s"
        using less.prems(1) part_bipartite_diff by blast
      then have graph_E': "graph_invar ?E_s" 
        unfolding partitioned_bipartite_def 
        by fastforce
      have "reachable ?E_s ?A_s = Vs ?E_s - ?A_s" 
        using part_bipartite_diff
        by (metis (no_types, lifting) less.prems(1) reachble_bipartite) 
      have 6:"?A_s \<subset> A" 
        using \<open>card ?A_s < card A\<close> by fastforce

      have " \<forall>X\<subseteq>?A_s. card X \<le> card (reachable ?E_s X)" 
      proof rule+
        fix X
        assume "X \<subseteq> ?A_s"
        then  have " X \<subset> A" using 6
          by (meson subset_psubset_trans)
        show "card X \<le> card (reachable ?E_s X)"
        proof(cases "X = {}")
          case True
          then show ?thesis 
            by simp
        next
          case False
          have "X \<noteq> {}" 
            by (simp add: False)
          then have "card X < card (reachable E X)"
            by (simp add: "7" `X \<noteq> {}` `X \<subset> A`)
          then have "card X \<le> card (reachable E X) - 1" 
            by linarith
          have "finite (reachable E X)" 
            using finite_reachable graphE by auto

          have "(reachable ?E_s X) \<subseteq> (reachable E X)" 
            unfolding reachable_def
            using 0 by blast

          have "{u, v} \<inter> X = {}" 
            by (metis (no_types, lifting) DiffD2 Int_ac(3) Int_subset_iff 
                \<open>X \<subseteq> ?A_s\<close> \<open>u \<notin> ?A_s\<close> disjoint_insert(1) inf_bot_right subsetD u_v)

          then have "reachable E X \<subseteq> {u,v} \<union> reachable ?E_s X" 
            using reachable_remove_vert[of E "{u,v}" X] 
            using `{u, v} \<inter> X = {}` graphE
            by auto
          have "reachable E A \<subseteq> Vs E - A" 
            by (simp add: less.prems(1) reachble_bipartite)

          then have "u \<notin> reachable E X" using reachable_subset[of X A E]  
            using \<open>X \<subset> A\<close> \<open>u \<in> A \<and> v \<in> Vs E - A\<close> by blast

          then have "reachable E X \<subseteq> {v} \<union> reachable ?E_s X"  
            using \<open>reachable E X \<subseteq> {u, v} \<union> reachable (E - {e \<in> E. u \<in> e \<or> v \<in> e}) X\<close> by fastforce

          then have "card (reachable E X) - 1 \<le> card (reachable ?E_s X)"
            by (smt (z3) \<open>finite (reachable E X)\<close> \<open>reachable (E - {e \<in> E. u \<in> e \<or> v \<in> e}) X \<subseteq> reachable E X\<close> card_Diff_singleton diff_le_self insert_is_Un insert_subset order_refl subset_antisym subset_insert_iff)

          then show " card X \<le> card (reachable ?E_s X)" 
            using \<open>card X \<le> card (reachable E X) - 1\<close> le_trans by blast
        qed
      qed
      then have " \<exists>M. cover_matching ?E_s M ?A_s" 
        using graph_E' \<open>card ?A_s < card A\<close> \<open>partitioned_bipartite ?E_s ?A_s\<close> less.hyps by auto
      then  obtain M where "cover_matching ?E_s M ?A_s" by auto

      have "?A_s = A - {u}" 
      proof - 
        have " A - {u} \<subseteq> Vs ?E_s" 
        proof
          fix a 
          assume "a \<in> A - {u}"
          then have "{a} \<subset> A" 
            using \<open>u \<in> A \<and> v \<in> Vs E - A\<close> by blast
          then have "card (reachable E {a}) > card {a}" 
            using "7" by blast
          then have "card (reachable E {a}) \<ge> 2" 
            by simp
          then obtain v1 v2 where v1_v2:"v1 \<noteq> v2 \<and> v1 \<in> reachable E {a} \<and> v2 \<in> reachable E {a}"
            by (metis One_nat_def card.infinite card_le_Suc0_iff_eq not_less_eq_eq numerals(2) 
                order_less_imp_le zero_less_one)
          then have "v1 \<noteq> v \<or> v2 \<noteq> v" 
            by blast
          then have "\<exists> v'. v' \<noteq> v \<and> (\<exists> u \<in> {a}. \<exists> e \<in> E. v' \<noteq> u \<and> u \<in> e \<and> v' \<in> e)"
            by (smt (verit, ccfv_SIG) v1_v2 mem_Collect_eq reachable_def)
          then obtain v' e' where v'_e: "v' \<noteq> v \<and> e' \<in> E \<and>  v' \<noteq> a \<and> a \<in> e' \<and> v' \<in> e'" 
            by blast
          then have "e' = {a, v'}"
            using graphE by fastforce
          then have "a \<in> A \<and> v' \<in> Vs E - A"
            using `partitioned_bipartite E A` 
            unfolding partitioned_bipartite_def reachable_def 
            by (metis Diff_iff \<open>a \<in> A - {u}\<close> v'_e doubleton_eq_iff)   
          have "v' \<in> Vs E - A"
            using \<open>a \<in> A \<and> v' \<in> Vs E - A\<close> by blast
          have "v' \<noteq> u" 
            using u_v \<open>v' \<in> Vs E - A\<close> by blast
          then have "e' \<in> E \<and> a \<in> e' \<and> u \<notin> e' \<and> v \<notin> e'"
            using \<open>a \<in> A - {u}\<close>  \<open>(u \<in> A \<and> v \<in> Vs E - A)\<close> \<open>{a} \<subset> A\<close> \<open>e' = {a, v'}\<close> v'_e 
            by fast
          then show "a \<in> Vs ?E_s" by blast
        qed   
        then show ?thesis 
          using \<open>u \<notin> Vs ?E_s\<close> by blast
      qed
      have "cover_matching E M ?A_s" 
        using `cover_matching ?E_s M ?A_s`
        unfolding cover_matching_def using graphE by blast
      then have "cover_matching E M (A - {u})" 
        by (simp add: \<open>?A_s = A - {u}\<close>)
      then have "A - {u} \<subseteq> Vs M" 
        by (simp add: cover_matching_def)
      have "M \<subseteq> E" 
        using \<open>cover_matching E M ?A_s\<close> cover_matching_def by blast
      have "matching M" 
        using \<open>cover_matching E M ?A_s\<close> cover_matching_def by blast
      have "\<forall> e \<in> M. u \<notin> e \<and> v \<notin> e "
        by (metis (no_types, lifting) \<open>cover_matching ?E_s M ?A_s\<close> cover_matching_def 
            mem_Collect_eq set_diff_eq subset_iff)
      then have "\<forall> e \<in> M. e \<noteq> {u, v} \<longrightarrow> e \<inter> {u, v} = {}" 
        by simp
      then have 8:"matching (insert {u, v} M)"
        using `matching M` unfolding matching_def  
        by auto 
      then have "A \<subseteq> Vs (insert {u, v} M)"
        using `A - {u} \<subseteq> Vs M` 
        by (smt (verit, ccfv_threshold) Sup_insert UnCI Vs_def u_v
            insertCI insertE insert_Diff subset_iff)
      have "insert {u, v} M \<subseteq> E" 
        using `{u, v} \<in> E`  \<open>M \<subseteq> E\<close> by blast
      then have "cover_matching E (insert {u, v} M) A"
        unfolding cover_matching_def using  `graph_invar E` 8 
        using \<open>A \<subseteq> Vs (insert {u, v} M)\<close> by blast
      then show ?thesis by auto
    qed
  next
    case False
    have "\<exists> X \<subset> A. X \<noteq> {} \<and> card (reachable E X) \<le> card X" 
      using False le_less_linear by blast
    then obtain X where X:"X \<subset> A \<and> X \<noteq> {}\<and> card (reachable E X) = card X"
      by (meson antisym less.prems(2) psubset_imp_subset)
    then have "X \<subset> A" by auto
    have "card X = card (reachable E X)"
      by (simp add: \<open>X \<subset> A \<and> X \<noteq> {} \<and> card (reachable E X) = card X\<close>)
    show ?thesis
    proof -

      let  ?X_gr = "{e \<in> E. \<exists>x \<in> X. x \<in> e}"
      have "?X_gr \<subseteq> E" by auto
      have "\<forall> Y \<subseteq> A. card Y \<le> card (reachable E Y)"
        using less.prems(2) by blast
      then  have  "\<forall> Y \<subseteq> X. card Y \<le> card (reachable E Y)" 
        by (meson \<open>X \<subset> A\<close> psubsetE subset_psubset_trans)
      have 1:"\<forall> Y \<subseteq> X. (reachable E Y) = reachable ?X_gr Y"
        unfolding reachable_def 
        by(safe, blast+)
      have "card X < card A" using `X \<subset> A` 
        by (meson finite_subset graphE Asubs psubset_card_mono)
      have "graph_invar ?X_gr" 
        using \<open>?X_gr \<subseteq> E\<close>
        by (meson  Vs_subset finite_subset graphE subsetD)
      have "X \<subseteq> Vs ?X_gr" 
        by (smt (verit, best) vs_member_elim X  Asubs mem_Collect_eq
            psubsetD subset_iff vs_transport)
      have "(\<forall>e\<in> ?X_gr. \<exists>u v. e = {u, v} \<and> (u \<in> X \<and> v \<in> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e} - X))"
      proof 
        fix e
        assume "e \<in> ?X_gr"
        have "e \<in> E" 
          using \<open>e \<in> {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> by blast
        then obtain u v where u_v: " e = {u, v}  \<and> (u \<in> A \<and> v \<in> Vs E - A)"
          using `partitioned_bipartite E A` unfolding partitioned_bipartite_def by meson
        have "v \<in> Vs ?X_gr" 
          using \<open>e \<in> ?X_gr\<close> u_v vs_member by fastforce
        then have "v \<in>  Vs ?X_gr - X" 
          using \<open>X \<subset> A\<close> u_v by blast
        then  show "( \<exists>u v. e = {u, v} \<and> (u \<in> X \<and> v \<in> Vs ?X_gr - X))" 
          using \<open>e \<in> ?X_gr\<close> u_v by blast
      qed   
      then  have "partitioned_bipartite ?X_gr X"
        unfolding partitioned_bipartite_def
        by (simp add: \<open>X \<subseteq> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> \<open>graph_invar {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> )

      then have "\<exists>M. cover_matching ?X_gr M X" using
          ` card X < card A` `X \<subseteq> Vs ?X_gr`
        using `graph_invar ?X_gr` less.hyps 1 
        using \<open>\<forall>Y\<subseteq>X. card Y \<le> card (reachable E Y)\<close> by presburger
      let ?AX_gr = "{e. e \<in> E \<and> (\<exists> x \<in> A - X. \<exists> y \<in> Vs E - (reachable E X) - A. y \<in> e \<and>  x \<in> e)}"
      have "?X_gr \<inter> ?AX_gr = {}"
        apply (safe; auto simp: reachable_def) 
        using \<open>X \<subset> A\<close> by auto
      have "?AX_gr \<subseteq> E" 
        by blast
      have "X \<noteq> {}"
        by (simp add: \<open>X \<subset> A \<and> X \<noteq> {} \<and> card (reachable E X) = card X\<close>)
      have " card (A - X) < card A"
        by (metis \<open>X \<noteq> {}\<close> \<open>X \<subset> A\<close> card_Diff_subset card_gt_0_iff diff_less 
            dual_order.strict_implies_order finite_subset graphE Asubs subset_empty)
      have A_X_graph:"graph_invar ?AX_gr" using `?AX_gr \<subseteq> E`
        by (meson Vs_subset finite_subset graphE subsetD)
      have A_X_vs:"A - X \<subseteq> Vs ?AX_gr"
      proof
        fix x
        assume "x \<in> A - X"
        then have"card (reachable E (X \<union> {x})) \<ge> card (X \<union> {x})"
          using X less.prems(2) by force
        then have "card (reachable E (X \<union> {x})) > card X" 
          using \<open>X \<subseteq> Vs ?X_gr\<close> \<open>graph_invar ?X_gr\<close> \<open>x \<in> A - X\<close> card_seteq 
            finite.emptyI finite_subset by fastforce
        then have card_gr:"card (reachable E (X \<union> {x})) > card (reachable E X)"
          by (simp add: X)
        then  have  "(reachable E (X)) \<subseteq> (reachable E (X \<union> {x})) "
          unfolding reachable_def by blast
        then have "(reachable E (X)) \<subset> (reachable E (X \<union> {x})) "
          using card_gr   by force
        then obtain z where z:"z\<in> reachable E (X \<union> {x}) \<and> z\<notin> reachable E (X)"
          by blast
        then obtain x' e where x'_e:"x' \<in> {x} \<and> e \<in> E \<and> z \<noteq> x' \<and> x' \<in> e \<and> z\<in> e"
          using z unfolding reachable_def 
          by blast
        then have "e = {x, z}"
          using x'_e graphE by fastforce
        have "z \<in> Vs E - A" 
          using less.prems(1) z unfolding partitioned_bipartite_def
          by (metis Diff_iff \<open>e = {x, z}\<close> \<open>x \<in> A - X\<close> doubleton_eq_iff x'_e)
        then have "e \<in> E \<and> x\<in>A - X \<and>  z \<in> Vs E - reachable E X - A \<and>  z \<in> e \<and> x \<in> e" 
          using \<open>x \<in> A - X\<close> x'_e z by blast
        then show "x \<in> Vs ?AX_gr"
          by blast
      qed
      have "Vs E - reachable E X - A \<subseteq> Vs ?AX_gr" 
      proof
        fix x
        assume asm:"x \<in> Vs E - reachable E X - A" 
        then obtain e where e:"e \<in> E \<and> x \<in> e" 
          by (meson DiffD1 vs_member_elim)
        then  have "\<nexists> u . u \<in> X \<and> ( \<exists> e \<in> E. x \<noteq> u \<and> u \<in> e \<and> x\<in> e)"                    
          using reachable_def asm by force
        then have "\<exists> u. u \<in> (A - X) \<and>  x \<noteq> u \<and> u \<in> e \<and> x\<in> e"
          using e less.prems(1) unfolding partitioned_bipartite_def 
          by (metis Diff_iff asm insertCI )
        then have "e \<in> ?AX_gr"
          using e asm by blast
        then show "x \<in> Vs ?AX_gr"
          by (meson e vs_member_intro)
      qed
      then have vs_subs: "Vs E - reachable E X - A \<subseteq> Vs ?AX_gr - (A - X)"
        by blast
      have AX_unfold:"\<forall>e\<in> ?AX_gr. \<exists>u v. e = {u, v} \<and> (u \<in> A - X \<and> v \<in> Vs ?AX_gr - (A - X))" 
        using less.prems(1)
        unfolding partitioned_bipartite_def
        apply safe
        by (smt (verit, best) DiffI insert_iff singletonD subsetD vs_subs)
      then have AX_partb:"partitioned_bipartite ?AX_gr (A - X)"
        unfolding partitioned_bipartite_def 
        using A_X_graph A_X_vs by fastforce

      have "\<forall>Y\<subseteq>(A-X). card Y \<le> card (reachable ?AX_gr Y)"
      proof rule+
        fix Y
        assume "Y \<subseteq> (A-X)"
        have reach_AX_Y:"reachable ?AX_gr Y = reachable E Y - reachable E X"
        proof
          show "reachable ?AX_gr Y \<subseteq> reachable E Y - reachable E X"
          proof
            fix x
            assume asm: "x \<in> reachable ?AX_gr Y"
            have "reachable ?AX_gr Y \<subseteq> reachable E Y"
              using `?AX_gr \<subseteq> E` unfolding reachable_def
              by blast
            then have "x \<in> reachable E Y" 
              using asm by blast
            obtain u e where u_e:" u \<in> Y \<and>  e \<in> ?AX_gr \<and> x \<noteq> u \<and> u \<in> e \<and> x\<in> e"
              using asm unfolding reachable_def 
              by blast
            then have "\<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e" 
              by blast
            then have "x \<in> Vs E - reachable E X - A" 
              using A_X_graph DiffD2 \<open>Y \<subseteq> A - X\<close> u_e  by auto
            then  show "x \<in> reachable E Y - reachable E X"
              by (simp add: \<open>x \<in> reachable E Y\<close>) 
          qed
          show "reachable E Y - reachable E X \<subseteq> reachable ?AX_gr Y"
          proof
            fix x
            assume asm: "x \<in> reachable E Y - reachable E X"
            have "reachable E Y \<subseteq> Vs E - A"
              using reachble_bipartite[OF less.prems(1)] 
                reachable_subset[of Y A E] \<open>Y \<subseteq> A - X\<close> by auto   
            then obtain u e where u_e:"u \<in> Y \<and>  e \<in> E \<and> x \<noteq> u \<and> u \<in> e \<and> x\<in> e"
              using asm unfolding reachable_def  by auto
            then have "e \<in> ?AX_gr" 
              using asm  \<open>Y \<subseteq> A - X\<close> \<open>reachable E Y \<subseteq> Vs E - A\<close> by auto 
            then show "x \<in> reachable ?AX_gr Y" 
              unfolding reachable_def using u_e by blast 
          qed
        qed
        then have "card (reachable ?AX_gr Y) = card (reachable E Y - reachable E X)"
          by presburger

        have "(reachable E Y - reachable E X) \<inter> reachable E X = {}"  by auto
        then have "card (reachable E (Y \<union> X))  = 
                   card (reachable E Y - reachable E X) + card (reachable E X)"
          by (metis (no_types, lifting) \<open>X \<noteq> {}\<close> \<open>X \<subset> A\<close> \<open>card X = card (reachable E X)\<close> 
              \<open>?AX_gr \<subseteq> E\<close>  card.infinite card_0_eq card_Un_disjoint finite_reachable finite_subset
              graphE Asubs psubset_imp_subset reach_AX_Y reachable_un)
        then have card_diff:"card (reachable E Y - reachable E X) = 
                   card (reachable E (Y \<union> X)) - card (reachable E X)" by auto
        have "card (reachable E (Y \<union> X)) \<ge> card (Y \<union> X)"
          by (metis Diff_subset \<open>X \<subset> A\<close> \<open>Y \<subseteq> A - X\<close> le_sup_iff less.prems(2) 
              psubset_imp_subset subset_Un_eq)
        then have "card (reachable E (Y \<union> X)) - card (reachable E X) \<ge> card (Y \<union> X) - card X"
          using `card X = card (reachable E X)` by auto
        moreover have "X \<inter> Y = {}"
          by (metis Diff_eq Int_commute Int_subset_iff \<open>Y \<subseteq> A - X\<close> disjoint_eq_subset_Compl)
        moreover have "card (Y \<union> X) - card X = card Y" 
          by (metis (no_types, lifting) A_X_graph A_X_vs Un_commute \<open>X \<inter> Y = {}\<close> \<open>X \<subset> A\<close> 
              \<open>Y \<subseteq> A - X\<close> add_diff_cancel_left' card_Un_disjoint finite_subset graphE Asubs
              psubset_imp_subset)
        ultimately show "card Y \<le> card (reachable ?AX_gr Y)" 
          using card_diff reach_AX_Y by presburger
      qed

      then have "\<exists>M. cover_matching ?AX_gr M (A-X)" 
        using AX_partb A_X_graph A_X_vs \<open>card (A - X) < card A\<close> less.hyps by presburger
      then obtain M' where M':"cover_matching ?AX_gr M'(A-X)" by auto
      obtain M where M:"cover_matching ?X_gr M X"
        using \<open>\<exists>M. cover_matching {e \<in> E. \<exists>x\<in>X. x \<in> e} M X\<close> by blast

      have Vs_inter:"Vs ?X_gr \<inter> Vs ?AX_gr = {}"
      proof(rule ccontr)
        assume "Vs ?X_gr \<inter> Vs ?AX_gr \<noteq> {}"
        then obtain z where z: "z \<in> Vs ?X_gr \<and> z\<in> Vs ?AX_gr" 
          by auto
        then have "\<exists> e \<in> E. \<exists>x\<in>X. x \<in> e \<and> z \<in> e"
          by (smt (verit, ccfv_SIG) mem_Collect_eq vs_member_elim)
        then obtain e' x' where e'_x':"e' \<in> E \<and> x'\<in>X \<and> x' \<in> e' \<and> z \<in> e'" 
          by auto
        then obtain e x y where e:"e \<in> E \<and> z \<in> e \<and> x \<in> A - X \<and> 
                               y \<in> Vs E - reachable E X - A \<and> y \<in> e \<and> x \<in> e"
          by (smt (verit) mem_Collect_eq vs_member z)
        then have "z = x \<or> z = y"
          using graphE by fastforce
        then have "z \<in> A - X \<or> z\<in> Vs E - reachable E X - A" using e by presburger
        show False
        proof (cases "z \<in> X")
          case True
          have "z \<notin> A" using `z \<in> A - X \<or> z\<in> Vs E - reachable E X - A` 
            using True by blast
          then show ?thesis
            using True \<open>X \<subset> A\<close> by blast
        next
          case False
          then have "z \<in> reachable E X"
            using e'_x' reachable_def by fastforce
          then have " z \<in> A - X" using `z \<in> A - X \<or> z\<in> Vs E - reachable E X - A` by blast
          have "\<exists>u v. e' = {u, v} \<and> (u \<in> A \<and> v \<in> Vs E - A)"
            using less.prems(1) unfolding partitioned_bipartite_def
            using e'_x' by blast
          then show ?thesis
            using \<open>z \<in> A - X\<close>  False \<open>X \<subset> A\<close> e'_x' by blast 
        qed
      qed
      then have Vs_M: "Vs M \<subseteq> Vs ?X_gr" 
        using M unfolding cover_matching_def 
        by (meson Vs_subset)
      have Vs_M': "Vs M' \<subseteq> Vs ?AX_gr"
        using M' unfolding cover_matching_def 
        by (meson Vs_subset)
      then have "Vs M \<inter> Vs M' = {}" 
        using Vs_M Vs_inter by blast
      then have "Vs M \<union> Vs M' = Vs (M \<union> M')"
        by (simp add: Vs_def)
      have "\<forall>v \<in> Vs (M \<union> M'). \<exists>!e\<in>(M \<union> M'). v \<in> e" 
      proof 
        fix v
        assume "v \<in> Vs (M \<union> M')" 
        show " \<exists>!e\<in>(M \<union> M'). v \<in> e"
        proof(cases "v \<in> Vs M")
          case True
          have "\<exists>!e\<in>(M). v \<in> e" 
            using M unfolding cover_matching_def 
            by (simp add: True matching_def2)  
          then show ?thesis using True
            using \<open>Vs M \<inter> Vs M' = {}\<close> disjoint_iff_not_equal vs_member by auto
        next
          case False
          have "\<exists>!e\<in>(M'). v \<in> e" 
            using M' unfolding cover_matching_def 
            by (metis (no_types, lifting) False UnE \<open>Vs M \<union> Vs M' = Vs (M \<union> M')\<close> 
                \<open>v \<in> Vs (M \<union> M')\<close> matching_def2)
          then show ?thesis 
            using False \<open>Vs M \<inter> Vs M' = {}\<close> UnE by blast
        qed
      qed
      then  have "matching (M \<union> M')" 
        by (simp add: matching_def2)
      have "M \<union> M' \<subseteq> E" 
        using M M' unfolding cover_matching_def
        by fast
      have "A \<subseteq> Vs (M \<union> M')" 
        using M M' unfolding cover_matching_def
        by (metis (no_types, lifting) Diff_partition Un_mono 
            \<open>Vs M \<union> Vs M' = Vs (M \<union> M')\<close> \<open>X \<subset> A\<close> psubset_imp_subset)
      then have "cover_matching E (M \<union> M') A" 
        unfolding cover_matching_def 
        using \<open>M \<union> M' \<subseteq> E\<close> \<open>matching (M \<union> M')\<close> graphE by fastforce
      then show "\<exists>M. cover_matching E M A" by auto
    qed
  qed
qed

lemma hall:
  fixes E :: "'a set set"
  assumes "partitioned_bipartite E A"
  shows "(\<exists> M. cover_matching E M A) \<longleftrightarrow> (\<forall> X \<subseteq> A. card (reachable E X) \<ge> card X)"
  using hall1 hall2[OF assms]
  by blast

lemma frobeneus_matching:
  fixes E :: "'a set set"
  assumes "partitioned_bipartite E A"
  shows "(\<exists> M. perfect_matching E M) \<longleftrightarrow> 
         (\<forall> X \<subseteq> A. card (reachable E X) \<ge> card X) \<and> (card A) = card (Vs E - A)"
proof
  show "\<exists>M. perfect_matching E M \<Longrightarrow> 
        (\<forall>X\<subseteq>A. card X  \<le> card (reachable E X)) \<and> card A = card (Vs E - A)"
  proof -
    assume "\<exists>M. perfect_matching E M"
    show "(\<forall>X\<subseteq>A. card X  \<le> card (reachable E X)) \<and> card A = card (Vs E - A)"
    proof
      obtain M where "perfect_matching E M"
        using \<open>\<exists>M. perfect_matching E M\<close> by auto
      then  have "Vs M = Vs E" 
        unfolding perfect_matching_def by auto
      then have "A \<subseteq> Vs M"
        using assms partitioned_bipartite_def by fastforce
      then have "cover_matching E M A"
        by (meson \<open>perfect_matching E M\<close> cover_matching_def perfect_matching_def)
      then show "\<forall>X\<subseteq>A. card X  \<le> card (reachable E X)"
        using assms hall by auto

      have "Vs E - A = reachable E A" 
        by (simp add: assms reachble_bipartite)
      have "partitioned_bipartite E (Vs E - A)" 
        by (simp add: assms partitioned_bipartite_swap)
      then have "cover_matching E M (Vs E - A)"
        using \<open>cover_matching E M A\<close> unfolding cover_matching_def
        by (simp add: \<open>Vs M = Vs E\<close>)
      then have "card (Vs E - A) \<le> card (reachable E (Vs E - A))"
        using hall \<open>partitioned_bipartite E (Vs E - A)\<close> 
        by blast
      moreover have "card A  \<le> card (reachable E A)"
        by (simp add: \<open>\<forall>X\<subseteq>A. card X \<le> card (reachable E X)\<close>)
      moreover have "A = reachable E (Vs E - A)" 
        using reachble_bipartite assms
        unfolding partitioned_bipartite_def 
        by (simp add: Diff_Diff_Int \<open>partitioned_bipartite E (Vs E - A)\<close>
            inf.absorb_iff2 reachble_bipartite)  
      ultimately show "card A = card (Vs E - A)" 
        using \<open>Vs E - A = reachable E A\<close> by auto
    qed
  qed
  show "(\<forall>X\<subseteq>A. card X \<le> card (reachable E X)) \<and> card A = card (Vs E - A) \<Longrightarrow> 
        \<exists>M. perfect_matching E M"
  proof -
    assume asm: "(\<forall>X\<subseteq>A. card X \<le> card (reachable E X)) \<and> card A = card (Vs E - A)"
    then  have "\<forall>X\<subseteq>A. card X \<le> card (reachable E X)" 
      by auto
    then have "\<exists>M. cover_matching E M A"
      using hall assms by auto
    then obtain M where M:"cover_matching E M A"
      by auto
    then have "card A = card (reachable M A)" 
      by (simp add: hall_reachable) 
    have "reachable M A \<subseteq> reachable E A"
      by (meson M cover_matching_def graph_subs_reach)
    have "Vs E - A = reachable E A" 
      by (simp add: assms reachble_bipartite)
    then have "reachable M A = Vs E - A" 
      using M unfolding cover_matching_def 
      by (metis \<open>card A = card (reachable M A)\<close> \<open>reachable M A \<subseteq> reachable E A\<close> asm card_subset_eq finite_Diff)
    have "Vs E = Vs M" 
      using  reachble_bipartite[OF part_bipart_of_cover_matching[OF assms M]] 
        M assms unfolding partitioned_bipartite_def cover_matching_def
      using assms M unfolding partitioned_bipartite_def cover_matching_def
      by (metis Diff_partition \<open>reachable M A = Vs E - A\<close>)
    then show "\<exists>M. perfect_matching E M"
      using \<open>cover_matching E M A\<close> unfolding cover_matching_def perfect_matching_def
      by auto
  qed
qed

lemma edge_in_component_edges:
  assumes "graph_invar E"
  assumes "e \<in> E"
  assumes "e \<subseteq> C" 
  shows "e \<in> component_edges E C"
  using assms component_edges_def by fastforce 

lemma graph_component_edges_partition:
  assumes "graph_invar E"
  shows "\<Union> (components_edges E) = E"
  unfolding components_edges_def
proof(safe)
  fix e
  assume "e \<in> E" 
  then obtain C where "e \<subseteq> C" "C \<in> connected_components E" 
    by (metis assms edge_in_component)
  moreover then have "e \<in> component_edges E C" 
    by (simp add: \<open>e \<in> E\<close> assms edge_in_component_edges)
  ultimately show "e \<in> \<Union>{component_edges E C |C.  C \<in> connected_components E}" 
    by blast 
qed (auto simp add: component_edges_def)

lemma graph_component_partition:
  assumes "graph_invar E"
  shows "\<Union> (connected_components E) = Vs E" 
  unfolding connected_components_def
proof(safe)
  fix y
  assume "y \<in> Vs E"
  then show "y \<in> \<Union> {connected_component E v |v. v \<in> Vs E}" 
    using  in_own_connected_component by fastforce
qed (metis in_connected_component_in_edges)

end