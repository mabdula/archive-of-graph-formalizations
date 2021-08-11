theory Bipartite
  imports Berge "HOL.Set"
begin


definition bipartite where 
  "bipartite E \<equiv> (graph_invar E) \<and> 
                   (\<exists> X \<subseteq> Vs E. \<forall> e \<in> E. \<exists> u v. 
               e= {u, v}  \<and> ((u \<in> X \<and> v \<in> Vs E - X) \<or> (u \<in> Vs E -  X \<and> v \<in> X)))"

(*
locale graph_bipartite =
  graph_abs +
  assumes " (\<exists> X \<subseteq> Vs E. \<forall> e \<in> E. \<exists> u v.  e= {u, v}  \<and> ((u \<in> X \<and> v \<in> Vs E - X)) \<or> (u \<in> Vs E -  X \<and> v \<in> X))"
begin

end
*)

definition partitioned_bipartite where
  "partitioned_bipartite E X \<equiv>  (graph_invar E) \<and> 
                                  X \<subseteq> Vs E  \<and> 
              ( \<forall> e \<in> E. \<exists> u v.  e= {u, v}  \<and> ((u \<in> X \<and> v \<in> Vs E - X) \<or> (u \<in> Vs E -  X \<and> v \<in> X)))"

lemma part_biparite_is_bipartite: "partitioned_bipartite E X \<longrightarrow> bipartite E "
  unfolding  partitioned_bipartite_def bipartite_def by auto

definition perfect_matching where
  "perfect_matching E M \<equiv> graph_invar E \<and> matching M \<and> M \<subseteq> E \<and> Vs M = Vs E"

definition cover_matching where
  "cover_matching E M A \<equiv> graph_invar E \<and> matching M \<and> M \<subseteq> E \<and> A \<subseteq> Vs M"

definition reachable where
  "reachable E X  \<equiv> {v. \<exists> u \<in> X. \<exists> e \<in> E. v \<noteq> u \<and> u \<in> e \<and> v\<in> e}"

definition other_vertex where
  "other_vertex M x \<equiv> { v . (\<exists> e\<in>M. x\<in> e \<and> v\<in>e \<and> x \<noteq> v)}"

lemma card_edge:
  assumes "graph_invar E"
  shows "\<forall> e\<in> E. card e = 2" 
  by (simp add: assms card_2_iff)

lemma reachable_is_union:
  shows "reachable E X = \<Union> {r. \<exists> x\<in>X.  r = (reachable E {x})}"
proof -
  show ?thesis unfolding reachable_def by blast
qed

lemma reach_singleton:
  "reachable E {x} = other_vertex E x"
  unfolding reachable_def other_vertex_def by auto

lemma reachable_other_vertex:
  shows "reachable E X = \<Union>  {r. \<exists> x\<in>X. r = other_vertex E x}"
  using reach_singleton reachable_is_union 
  by (smt (verit, best) Collect_cong)

lemma reachble_bipartite:
  assumes "partitioned_bipartite E A"
  shows "reachable E A =  Vs E - A" 
proof -
  have " (graph_invar E)" using assms unfolding partitioned_bipartite_def by auto
  have " A \<subseteq> Vs E" using assms unfolding partitioned_bipartite_def by auto
  have 1:"( \<forall> e \<in> E. \<exists> u v.  e= {u, v}  \<and> ((u \<in> A \<and> v \<in> Vs E - A) \<or> (u \<in> Vs E -  A \<and> v \<in> A)))"
    using assms unfolding partitioned_bipartite_def by auto

  show ?thesis
  proof
    show "reachable E A \<subseteq> Vs E - A" 
    proof
      fix x
      assume "x \<in> reachable E A"
      then have "\<exists> u \<in> A. \<exists> e \<in> E. x \<noteq> u \<and> u \<in> e \<and> x\<in> e" unfolding reachable_def by auto
      then obtain u e where "u \<in> A \<and> e \<in> E \<and> x \<noteq> u \<and> u \<in> e \<and> x\<in> e" by auto
      then have "e= {u, x}  \<and> ((u \<in> A \<and> x \<in> Vs E - A) \<or> (u \<in> Vs E -  A \<and> x \<in> A))" using 1
        using insert_absorb insert_commute by fastforce
      then have "(u \<in> A \<and> x \<in> Vs E - A)"
        using \<open>u \<in> A \<and> e \<in> E \<and> x \<noteq> u \<and> u \<in> e \<and> x \<in> e\<close> by force 
      then show  "x \<in> Vs E - A" by auto
    qed
    show "Vs E - A \<subseteq> reachable E A"
    proof
      fix x
      assume "x \<in> Vs E - A"
      then have "\<exists> e \<in> E. x \<in> e" 
        by (meson DiffD1 vs_member_elim)

      then obtain e where "e \<in> E \<and> x \<in> e" by auto
      then have "\<exists> u v.  e= {u, v}  \<and> ((u \<in> A \<and> v \<in> Vs E - A) \<or> (u \<in> Vs E -  A \<and> v \<in> A))" 
        using 1 by auto
      then obtain u v where 2:"e= {u, v}  \<and> ((u \<in> A \<and> v \<in> Vs E - A) \<or> (u \<in> Vs E -  A \<and> v \<in> A))" by auto
      show "x \<in> reachable E A"
      proof(cases "x = u")
        case True
        have "x=u" using True by auto
        then  have "e= {x, v}  \<and> ((x \<in> A \<and> v \<in> Vs E - A) \<or> (x \<in> Vs E -  A \<and> v \<in> A))" using 2 by auto

        then have "(x \<in> Vs E -  A \<and> v \<in> A)" using \<open>x \<in> Vs E -  A\<close> by auto
        then have "x \<in> {v. \<exists> u \<in> A. \<exists> e \<in> E. v \<noteq> u \<and> u \<in> e \<and> v\<in> e}"
          by (smt (verit, ccfv_SIG) DiffD2 \<open>\<And>thesis. (\<And>u v. e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs E - A \<or> u \<in> Vs E - A \<and> v \<in> A) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> \<open>e \<in> E \<and> x \<in> e\<close> insertCI mem_Collect_eq)
        then show ?thesis using reachable_def
          by (simp add: reachable_def)
      next
        case False
        then have "x = v" using \<open>e \<in> E \<and> x \<in> e\<close> 2 by simp
        then have "e= {u, x}  \<and> ((u \<in> A \<and> x \<in> Vs E - A) \<or> (u \<in> Vs E -  A \<and> x \<in> A))" using 2 by auto
        then have "(u \<in> A \<and> x \<in> Vs E - A)" 
          using \<open>x \<in> Vs E - A\<close> by blast
        then have "x \<in> {v. \<exists> u \<in> A. \<exists> e \<in> E. v \<noteq> u \<and> u \<in> e \<and> v\<in> e}" 
          using \<open>e = {u, x} \<and> (u \<in> A \<and> x \<in> Vs E - A \<or> u \<in> Vs E - A \<and> x \<in> A)\<close> \<open>e \<in> E \<and> x \<in> e\<close> insert_compr by force
        then show ?thesis  by (simp add: reachable_def)
      qed
    qed
  qed
qed

lemma partitioned_bipartite_swap:
  assumes "partitioned_bipartite E A"
  shows "partitioned_bipartite E (Vs E - A)" 
proof -
  have "(graph_invar E)" using assms partitioned_bipartite_def by auto
  have " (Vs E - A)  \<subseteq> Vs E" 
    by simp
  have "Vs E - (Vs E - A) =  A" 
    by (metis Diff_partition Diff_subset_conv Un_Diff_cancel \<open>Vs E - A \<subseteq> Vs E\<close> assms double_diff partitioned_bipartite_def)
  then show ?thesis 
  unfolding partitioned_bipartite_def 
  by (metis \<open>Vs E - A \<subseteq> Vs E\<close> assms partitioned_bipartite_def)
qed

lemma reachable_intersection_is_empty:
  assumes "partitioned_bipartite E A"
  shows" \<forall>X \<subseteq> A. reachable E X \<inter> X = {}"
proof
  fix X 
  show "X \<subseteq> A \<longrightarrow> reachable E X \<inter> X = {}"
  proof
    assume "X \<subseteq> A"
    then have "reachable E X \<subseteq> reachable E A" unfolding reachable_def by auto
    then have "reachable E X \<subseteq> Vs E - X" using reachble_bipartite assms
      by (smt (verit) Diff_iff \<open>X \<subseteq> A\<close> subsetD subsetI)
    then show "reachable E X \<inter> X = {}" 
      by (simp add: Diff_eq disjoint_eq_subset_Compl)
  qed
qed

lemma asd:
  assumes "x \<in> Vs M"
  assumes "matching M"
  assumes" M \<subseteq> E"
  assumes "graph_invar E"
  shows"card (other_vertex M x) = 1"
proof -
  have "\<exists>!e. e \<in> M \<and> x \<in> e"  using matching_def2 assms(2) assms(1)  by metis
  then obtain e where 1: " e \<in> M \<and> x \<in> e" by auto
  have 3:"\<forall> e' \<in> M. e' \<noteq> e \<longrightarrow>x \<notin> e'"
  proof(rule ccontr)
    assume "\<not> (\<forall>e'\<in>M. e' \<noteq> e \<longrightarrow> x \<notin> e')"
    then have "\<exists> e'\<in>M. e' \<noteq> e \<longrightarrow> x \<in> e'" by blast   
    then obtain e' where 2: " e'\<in>M \<and> e' \<noteq> e \<and> x \<in> e'" 
      by (meson \<open>\<not> (\<forall>e'\<in>M. e' \<noteq> e \<longrightarrow> x \<notin> e')\<close>)
    show False 
      using "1" "2" \<open>\<exists>!e. e \<in> M \<and> x \<in> e\<close> by auto
  qed
  have "\<exists>v.  (\<exists> e\<in>M. x\<in> e \<and> v\<in>e \<and> x \<noteq> v)"
    by (metis "1" assms(3) assms(4) insertCI subsetD)
  then obtain v where "(\<exists> e\<in>M. x\<in> e \<and> v\<in>e \<and> x \<noteq> v)" by auto

  have "\<forall>v'.  (\<exists> e\<in>M. x\<in> e \<and> v'\<in>e \<and> x \<noteq> v') \<longrightarrow> v = v'"
  proof(rule ccontr)
    assume " \<not> (\<forall>v'. (\<exists>e\<in>M. x \<in> e \<and> v' \<in> e \<and>  x \<noteq> v') \<longrightarrow>v = v')"
    then have "\<exists> v'. (\<exists>e\<in>M. x \<in> e \<and> v' \<in> e \<and>  x \<noteq> v') \<and> v \<noteq> v'" by simp
    then obtain v' where "(\<exists>e\<in>M. x \<in> e \<and> v' \<in> e \<and>  x \<noteq> v') \<and> v \<noteq> v'" by auto
    then obtain e' where " x \<in> e' \<and> v' \<in> e' \<and>  x \<noteq> v' \<and> v \<noteq> v'" by auto
    then have  "\<exists> e' \<in> M. e' \<noteq> e \<longrightarrow> x \<in> e'" 
      using "1" by blast
    then show False using 3
      by (metis \<open>(\<exists>e\<in>M. x \<in> e \<and> v' \<in> e \<and> x \<noteq> v') \<and> v \<noteq> v'\<close> \<open>\<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v\<close> assms(3) assms(4) empty_iff insert_iff subsetD)
  qed
  then have 4:"\<exists>!v. \<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v" 
    using \<open>\<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v\<close> by blast
  let ?P = "(\<lambda> v. \<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v)" 
  have "Ex1  ?P" using 4 by auto
  have "Ex1 ?P \<equiv> \<exists> u. {u. ?P u} = {u}"  unfolding  HOL.nitpick_unfold(124) by auto


  then have "\<exists>v. {v. \<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v} = {v}" unfolding Nitpick.Ex1_unfold
    using "4" \<open>\<exists>!v. \<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v \<equiv> \<exists>u. {u. \<exists>e\<in>M. x \<in> e \<and> u \<in> e \<and> x \<noteq> u} = {u}\<close> by presburger

  then have "card {v. \<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v} = 1"
    by fastforce
  then show ?thesis unfolding other_vertex_def  by simp
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

lemma card_ther_vertex:
  assumes "X \<subseteq> Vs M"
  assumes "matching M"
  assumes" M \<subseteq> E"
  assumes "graph_invar E"
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
    have " F \<subseteq> Vs M \<Longrightarrow> card F = card (reachable M F)"
      using insert.hyps(3) by blast
    have " insert x F \<subseteq> Vs M" using  insert.hyps 
      using insert.prems by blast
    then have "x \<in> Vs M" by auto
    then have "card (other_vertex M x) = 1"
      by (meson asd assms(2) assms(3) assms(4))
    then have "\<exists>v. (other_vertex M x) = {v}"
      by (meson card_1_singletonE)
    then obtain v where " (other_vertex M x) = {v}" by auto
    then have "(\<exists> e\<in>M. x\<in> e \<and> v\<in>e \<and> x \<noteq> v)" unfolding other_vertex_def by auto
    then obtain e where "e\<in>M \<and> x\<in> e \<and> v\<in>e \<and> x \<noteq> v" by auto
    then have " e = {x, v}" 
      using assms(3) assms(4) by fastforce
    have "reachable M {x} = other_vertex M x"
      by (simp add: reach_singleton)
    have "v \<notin> reachable M F"
    proof(rule ccontr)
      assume "\<not> v \<notin> reachable M F"
      then have  "v \<in> reachable M F" by auto
      then have "\<exists> u \<in> F. \<exists> e \<in> M. v \<noteq> u \<and> u \<in> e \<and> v\<in> e" unfolding reachable_def 
        by (smt (verit, best) \<open>\<exists>e\<in>M. x \<in> e \<and> v \<in> e \<and> x \<noteq> v\<close> assms(3) assms(4) assms(2) insert.hyps(2) insert_iff matching_def2 mem_Collect_eq singletonD subsetD vs_member_intro)
      then  obtain u where "u \<in> F \<and> (\<exists> e \<in> M. v \<noteq> u \<and> u \<in> e \<and> v\<in> e)" by auto
      then obtain e' where "e' \<in> M \<and> v \<noteq> u \<and> u \<in> e' \<and> v\<in> e'" by auto
      then have "e' = {u, v}"  using assms(4) assms(3)
        by (metis \<open>e = {x, v}\<close> \<open>e \<in> M \<and> x \<in> e \<and> v \<in> e \<and> x \<noteq> v\<close> assms(2) insertE insert_absorb matching_unique_match singleton_insert_inj_eq')
      have " x\<noteq> u" using insert.hyps(2) `u \<in> F \<and> (\<exists> e \<in> M. v \<noteq> u \<and> u \<in> e \<and> v\<in> e)` by auto
      have "x \<noteq> u \<and> x \<in> e \<and> u \<in> e'"
        by (simp add: \<open>e \<in> M \<and> x \<in> e \<and> v \<in> e \<and> x \<noteq> v\<close> \<open>e' \<in> M \<and> v \<noteq> u \<and> u \<in> e' \<and> v \<in> e'\<close> \<open>x \<noteq> u\<close>)
      have "e \<noteq> e'" 
        using \<open>e = {x, v}\<close> \<open>e' = {u, v}\<close> \<open>x \<noteq> u \<and> x \<in> e \<and> u \<in> e'\<close> by blast
      then show False 
        by (meson \<open>e \<in> M \<and> x \<in> e \<and> v \<in> e \<and> x \<noteq> v\<close> \<open>e' \<in> M \<and> v \<noteq> u \<and> u \<in> e' \<and> v \<in> e'\<close> assms(2) matching_unique_match)
    qed
    then have 1: "reachable M {x} \<inter> reachable M F = {}" 
      by (simp add: \<open>other_vertex M x = {v}\<close> \<open>reachable M {x} = other_vertex M x\<close>)
    have "finite (reachable M {x})"
      by (simp add: \<open>other_vertex M x = {v}\<close> \<open>reachable M {x} = other_vertex M x\<close>)

    then have 2: "card (reachable M {x}) + card( reachable M F) = card (reachable M {x} \<union> reachable M F)"
      using finite_reachable 1
      by (metis assms(4) assms(3) card_Un_disjoint)

    have " reachable M (insert x F) = reachable M F \<union> reachable M {x}"
    proof
      show " reachable M (insert x F) \<subseteq> reachable M F \<union> reachable M {x}"
      proof 
        fix u
        assume "u \<in> reachable  M (insert x F)"
        show "u \<in> reachable M F \<union> reachable M {x}" unfolding reachable_def 
          by (smt (verit, ccfv_threshold) UnCI \<open>u \<in> reachable M (insert x F)\<close> insert_iff mem_Collect_eq reachable_def)
      qed
      show "reachable M F \<union> reachable M {x} \<subseteq> reachable M (insert x F)" unfolding reachable_def 
        by blast
    qed

    then have "card (reachable M (insert x F)) =
          card (reachable M F) + card (reachable M {x})" using 2
      using \<open>other_vertex M x = {v}\<close> \<open>reachable M {x} = other_vertex M x\<close> by auto
    then have 3: "card (reachable M (insert x F)) = card (reachable M F) + 1"
      using \<open>card (other_vertex M x) = 1\<close> \<open>reachable M {x} = other_vertex M x\<close> by presburger
    have "card (insert x F) = card F + 1"
      by (simp add: insert.hyps(1) insert.hyps(2)) 
    then show  "card (insert x F) = card (reachable M (insert x F))" using 3
      by (metis insert.hyps(3) insert.prems insert_subset)
  qed
qed



lemma halrewrw:
  fixes E :: "'a set set"
  fixes M
  assumes "partitioned_bipartite E A"
  assumes "cover_matching E M A"
  shows "partitioned_bipartite M A"
proof -
  have 1:"M \<subseteq> E" using assms(2) unfolding cover_matching_def by auto
  have "graph_invar E"
    using assms(1) partitioned_bipartite_def by auto
  then have "graph_invar M" using 1
    by (meson Vs_subset finite_subset subsetD)
  have "A \<subseteq> Vs M" using assms(2) unfolding cover_matching_def by auto
  have " ( \<forall> e \<in> E. \<exists> u v.  e= {u, v}  \<and> ((u \<in> A \<and> v \<in> Vs E - A) \<or> (u \<in> Vs E -  A \<and> v \<in> A)))"
    using assms(1) unfolding partitioned_bipartite_def by auto
  have "\<forall>e \<in> M.  \<exists> u v.  e= {u, v}  \<and> ((u \<in> A \<and> v \<in> Vs M - A) \<or> (u \<in> Vs M -  A \<and> v \<in> A))" 
    by (metis "1" Diff_iff \<open>\<forall>e\<in>E. \<exists>u v. e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs E - A \<or> u \<in> Vs E - A \<and> v \<in> A)\<close> edges_are_Vs in_mono insert_commute)
  show ?thesis 
    using \<open>A \<subseteq> Vs M\<close> \<open>\<forall>e\<in>M. \<exists>u v. e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs M - A \<or> u \<in> Vs M - A \<and> v \<in> A)\<close> \<open>graph_invar M\<close> partitioned_bipartite_def by auto
qed



lemma hall_reachable:
  fixes E :: "'a set set"
  assumes "partitioned_bipartite E A"
  assumes "cover_matching E M A"
  shows "\<forall> X \<subseteq> A. card (reachable M X) = card X"
proof
  show " \<And>X. X \<subseteq> A \<longrightarrow>  card (reachable M X) = card X"
  proof
    fix X
    assume "X \<subseteq> A"
    show "card (reachable M X) = card X" using card_ther_vertex 
      by (smt (verit, ccfv_SIG) \<open>X \<subseteq> A\<close> assms(2) cover_matching_def subset_trans)
  qed
qed


lemma hall1:
  fixes E :: "'a set set"
  assumes "partitioned_bipartite E A"
  assumes "cover_matching E M A"
  shows "\<forall> X \<subseteq> A. card (reachable E X) \<ge> card X"
proof
  fix X
  show "X \<subseteq> A \<longrightarrow> card X \<le> card (reachable E X)"
  proof
    assume "X \<subseteq> A"
    show "card X \<le> card (reachable E X)"
    proof -
      have 1:"finite (reachable M X)" 
        by (meson assms(2) cover_matching_def finite_reachable)
      have "E \<subseteq> E" by auto
      then have 2:"finite (reachable E X)"
        by (meson assms(2) cover_matching_def finite_reachable)
      have "reachable M X \<subseteq> reachable E X" unfolding reachable_def 
        by (smt (verit) Collect_mono assms(2) cover_matching_def subset_iff)
      then have 3: "card (reachable M X) \<le> card (reachable E X)" using 1 2 
        by (simp add: card_mono)
      have "card X = card (reachable M X)" 
        by (metis \<open>X \<subseteq> A\<close> assms(1) assms(2) hall_reachable)
      then show ?thesis using 3 by auto
    qed
  qed
qed


lemma hall2:
  fixes E :: "'a set set"
  assumes "graph_invar E"
  assumes "A \<subseteq> Vs E"
  assumes "partitioned_bipartite E A"
  assumes  "\<forall> X \<subseteq> A. card (reachable E X) \<ge> card X"
  shows  "\<exists> M. cover_matching E M A"
  using assms(1) assms(2) assms(3) assms(4)
proof(induct "card A" arbitrary: A E rule: less_induct)
  case less
  then show ?case
  proof(cases "card A \<ge> 2")
    case True
    have card2: "card A \<ge> 2" 
      by (simp add: True)
    then show ?thesis
    proof(cases "\<forall> X \<subset> A. X \<noteq> {} \<longrightarrow>  card (reachable E X) > card X")
      case True
      have 7:"\<forall> X \<subset> A. X \<noteq> {} \<longrightarrow> card (reachable E X) > card X"
        by (simp add: True)
      then show ?thesis
      proof (cases "E = {}") 
        case True
        then show ?thesis 
          by (metis cover_matching_def equals0D less.prems(1) less.prems(2) matching_def subset_empty)
      next
        case False
        have "\<exists> e. e \<in> E" 
          using False by blast
        then obtain e where "\<exists>u v. e \<in>E \<and> e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs E - A \<or> u \<in> Vs E - A \<and> v \<in> A)"
          by (metis less.prems(3) partitioned_bipartite_def)
        then obtain u v where "e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs E - A)" 
          by auto
        then  have "(u \<in> A \<and> v \<in> Vs E - A)" by auto
        have " {u, v} \<in> E"
          using \<open>\<exists>u v. e \<in> E \<and> e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs E - A \<or> u \<in> Vs E - A \<and> v \<in> A)\<close> \<open>e = {u, v} \<and> u \<in> A \<and> v \<in> Vs E - A\<close> by fastforce
        let ?E_s = "E - {e. e \<in> E \<and> (u \<in> e \<or> v \<in> e)}"
        let ?A_s = "(A \<inter> Vs ?E_s)- {u}"
        let ?B_s = "Vs ?E_s - ?A_s - {v}"
        have 0:"?E_s \<subseteq> E" 
          by force
        have "card ?A_s < card A"
          by (smt (verit, ccfv_threshold) Diff_disjoint Diff_subset Int_commute Int_insert_right_if1 `(u \<in> A \<and> v \<in> Vs E - A)` finite_subset inf_le1 insert_not_empty less.prems(1) less.prems(2) psubsetI psubset_card_mono subset_trans)
        have 2: "graph_invar ?E_s" 
          by (meson Diff_iff Diff_subset Vs_subset finite_subset less.prems(1))
        have 3: "?A_s \<subseteq> Vs ?E_s" by blast
        have " ( \<forall> e \<in> ?E_s. \<exists> u v.  e= {u, v}  
            \<and> ((u \<in> ?A_s \<and> v \<in> Vs ?E_s - ?A_s) \<or> (u \<in> Vs ?E_s -  ?A_s \<and> v \<in> ?A_s)))"
        proof
          fix e'
          assume "e' \<in> ?E_s" 
          then have "\<exists>u v. e' = {u, v} \<and> u \<noteq> v" 
            using "2" by blast
          then obtain u' v' where "e' = {u', v'} \<and> u' \<noteq> v'" by auto
          have "e' \<in> E" using 0 `e' \<in> ?E_s` by auto
          then have 4:"((u' \<in> A \<and> v' \<in> Vs E - A) \<or> (u' \<in> Vs E -  A \<and> v' \<in> A))"
            using `partitioned_bipartite E A` unfolding partitioned_bipartite_def 
            by (metis \<open>e' = {u', v'} \<and> u' \<noteq> v'\<close> doubleton_eq_iff)
          show " \<exists> u v.  e'= {u, v}  
            \<and> ((u \<in> ?A_s \<and> v \<in> Vs ?E_s - ?A_s) \<or> (u \<in> Vs ?E_s -  ?A_s \<and> v \<in> ?A_s))"
          proof(cases "(u' \<in> A \<and> v' \<in> Vs E - A)")
            case True
            have "u' \<in> A"  by (simp add: True)
            then have "u' \<in> ?A_s" 
              using UnionI \<open>e' = {u', v'} \<and> u' \<noteq> v'\<close> \<open>e' \<in> E - {e \<in> E. u \<in> e \<or> v \<in> e}\<close> by auto
            have "v' \<in> Vs E - A"
              using True by auto
            then have "v' \<in> Vs ?E_s - ?A_s"
              using IntE \<open>e' = {u', v'} \<and> u' \<noteq> v'\<close> \<open>e' \<in> E - {e \<in> E. u \<in> e \<or> v \<in> e}\<close> by auto
            then show ?thesis 
              using \<open>e' = {u', v'} \<and> u' \<noteq> v'\<close> \<open>u' \<in> A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u}\<close> by blast
          next
            case False
            have 5:"(u' \<in> Vs E -  A \<and> v' \<in> A)" using False 4 by auto
            have "v' \<in> A"  
              by (simp add: "5")
            then have "v' \<in> ?A_s" 
              using UnionI \<open>e' = {u', v'} \<and> u' \<noteq> v'\<close> \<open>e' \<in> E - {e \<in> E. u \<in> e \<or> v \<in> e}\<close> by auto
            have "u' \<in> Vs E - A"
              using 5 by auto
            then have "u' \<in> Vs ?E_s - ?A_s"
              using IntE \<open>e' = {u', v'} \<and> u' \<noteq> v'\<close> \<open>e' \<in> E - {e \<in> E. u \<in> e \<or> v \<in> e}\<close> by auto
            then show ?thesis 
              using \<open>e' = {u', v'} \<and> u' \<noteq> v'\<close> \<open>v' \<in> A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u}\<close> by blast
          qed
        qed
        then have "partitioned_bipartite ?E_s ?A_s"
          using "2" 3 
          by (simp add: \<open>\<forall>e\<in>E - {e \<in> E. u \<in> e \<or> v \<in> e}. \<exists>ua va. e = {ua, va} \<and> (ua \<in> A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u} \<and> va \<in> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - (A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u}) \<or> ua \<in> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - (A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u}) \<and> va \<in> A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u})\<close> partitioned_bipartite_def)

        have "reachable ?E_s ?A_s = Vs ?E_s - ?A_s" 
          using \<open>partitioned_bipartite (E - {e \<in> E. u \<in> e \<or> v \<in> e}) (A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u})\<close> reachble_bipartite by blast


        have 6:"?A_s \<subset> A" 
          using \<open>card (A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u}) < card A\<close> by fastforce

        have " \<forall>X\<subseteq>?A_s. card X \<le> card (reachable ?E_s X)"
        proof
          fix X
          show "X \<subseteq> ?A_s \<longrightarrow> card X \<le> card (reachable ?E_s X)"
          proof
            assume "X \<subseteq> ?A_s"
            then  have " X \<subset> A" using 6
              by (meson subset_psubset_trans)
            show "card X \<le> card (reachable ?E_s X)"
            proof(cases "X={}")
              case True
              then show ?thesis 
                by simp
            next
              case False
              then show ?thesis 
              proof -
                have "X \<noteq> {}" 
                  by (simp add: False)
                then  have " X \<subset> A" using 6
                  by (simp add: \<open>X \<subset> A\<close>)


                then have "card X < card (reachable E X)"
                  by (simp add: "7" `X \<noteq> {}` )
                then have "card X \<le> card (reachable E X) - 1" 
                  by linarith
                have "finite (reachable E X)" 
                  using finite_reachable less.prems(1) by auto
                have "finite (reachable ?E_s X)"
                  by (meson Diff_subset finite_reachable less.prems(1))
                have "(reachable ?E_s X) \<subseteq> (reachable E X)" unfolding reachable_def
                  using 0 by blast
                then have "card (reachable ?E_s X) \<le> card (reachable E X)"  
                  using \<open>finite (reachable E X)\<close> \<open>finite (reachable ?E_s X)\<close>
                  by (simp add: card_mono)


                have "reachable ?E_s X = 
                     {z. \<exists> t \<in> X. \<exists> e' \<in> E. z \<in> e' \<and> t \<in> e' \<and> t \<noteq> z \<and> e'\<notin> {e. e \<in> E \<and> (u \<in> e \<or> v \<in> e)}}"
                  unfolding reachable_def 
                  by fastforce

                have "reachable E X \<subseteq> {v} \<union>
                     {z. \<exists> t \<in> X. \<exists> e' \<in> E. z \<in> e' \<and>  t \<in> e' \<and> t \<noteq> z \<and> e'\<notin> {e. e \<in> E \<and> (u \<in> e \<or> v \<in> e)}}"
                proof
                  fix z
                  assume "z \<in> reachable E X"
                  then have "z \<in> {v. \<exists> u \<in> X. \<exists> e \<in> E. v \<noteq> u \<and> u \<in> e \<and> v\<in> e}" using reachable_def by fast

                  show "z \<in> {v} \<union>  {z. \<exists> t \<in> X. \<exists> e' \<in> E. z \<in> e' \<and> t \<in> e' \<and> t \<noteq> z \<and> e'\<notin> {e. e \<in> E \<and> (u \<in> e \<or> v \<in> e)}}"
                  proof(cases "z = v")
                    case True
                    then show ?thesis 
                      by blast
                  next
                    case False
                    have "z \<noteq> v" 
                      by (simp add: False)

                    have "z \<notin> X" using reachable_intersection_is_empty \<open>z \<in> reachable E X\<close>
                      by (metis \<open>X \<subset> A\<close> disjoint_insert(2) less.prems(3) mk_disjoint_insert psubset_imp_subset)

                    have "reachable E X \<subseteq> reachable E A" unfolding reachable_def 
                      using \<open>X \<subset> A\<close> by blast
                    then have "z \<in> reachable E A"
                      using \<open>z \<in> reachable E X\<close> by blast
                    then have "z \<notin> A" using reachable_intersection_is_empty 
                      by (simp add: less.prems(3) reachble_bipartite)
                    then have "z \<noteq> u" 
                      by (metis  \<open>e = {u, v} \<and> (u \<in> A \<and> v \<in> Vs E - A)\<close>)
                    have "u \<notin> X" 
                      by (meson Diff_disjoint \<open>X \<subseteq> A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u}\<close> insert_disjoint(1) subset_iff)
                    have "\<exists> u \<in> X. \<exists> e \<in> E. z \<noteq> u \<and> u \<in> e \<and> z\<in> e" 
                      using \<open>z \<in> {v. \<exists>u\<in>X. \<exists>e\<in>E. v \<noteq> u \<and> u \<in> e \<and> v \<in> e}\<close> by blast
                    then  obtain u' e' where " u' \<in> X \<and> e' \<in> E \<and> z \<noteq> u' \<and> u' \<in> e' \<and> z\<in> e'" 
                      by blast
                    then have "u \<noteq> u'" using `u \<notin> X` 
                      by force
                    then have "e' = {u', z}"
                      using less.prems(1)
                      using \<open>u' \<in> X \<and> e' \<in> E \<and> z \<noteq> u' \<and> u' \<in> e' \<and> z \<in> e'\<close> by fastforce
                    have "v \<notin> A" 
                      using `(u \<in> A \<and> v \<in> Vs E - A)` \<open>reachable E X \<subseteq> reachable E A\<close> less.prems(3) reachble_bipartite by auto
                    then have "v \<noteq> u'" 
                      using \<open>X \<subset> A\<close> \<open>u' \<in> X \<and> e' \<in> E \<and> z \<noteq> u' \<and> u' \<in> e' \<and> z \<in> e'\<close> by blast
                    then have "v \<notin> e' \<and> u \<notin> e'" 
                      using False \<open>e' = {u', z}\<close> \<open>u \<noteq> u'\<close> \<open>z \<noteq> u\<close> by fastforce
                    then have " e' \<notin> {e \<in> E. u \<in> e \<or> v \<in> e}"
                      by blast
                    then have "\<exists> t \<in> X. \<exists> e' \<in> E. z \<in> e' \<and> t \<in> e' \<and> t \<noteq> z \<and> e'\<notin> {e. e \<in> E \<and> (u \<in> e \<or> v \<in> e)}" 
                      using \<open>u' \<in> X \<and> e' \<in> E \<and> z \<noteq> u' \<and> u' \<in> e' \<and> z \<in> e'\<close> by blast
                    then show ?thesis
                      by blast
                  qed
                qed

                have " {z. \<exists> t \<in> X. \<exists> e' \<in> E. z \<in> e' \<and> t \<in> e' \<and> t \<noteq> z \<and> e'\<notin> {e. e \<in> E \<and> (u \<in> e \<or> v \<in> e)}} = reachable ?E_s X"              
                  using \<open>reachable (E - {e \<in> E. u \<in> e \<or> v \<in> e}) X = {z. \<exists>t\<in>X. \<exists>e'\<in>E. z \<in> e' \<and> t \<in> e' \<and> t \<noteq> z \<and> e' \<notin> {e \<in> E. u \<in> e \<or> v \<in> e}}\<close> by presburger
                then have "reachable E X \<subseteq> {v} \<union> reachable ?E_s X" 
                  using \<open>reachable E X \<subseteq> {v} \<union> {z. \<exists>t\<in>X. \<exists>e'\<in>E. z \<in> e' \<and> t \<in> e' \<and> t \<noteq> z \<and> e' \<notin> {e \<in> E. u \<in> e \<or> v \<in> e}}\<close> by presburger

                then have "card (reachable E X) - 1 \<le> card (reachable ?E_s X)"
                  by (smt (z3) \<open>finite (reachable E X)\<close> \<open>reachable (E - {e \<in> E. u \<in> e \<or> v \<in> e}) X \<subseteq> reachable E X\<close> card_Diff_singleton diff_le_self insert_is_Un insert_subset order_refl subset_antisym subset_insert_iff)

                then show " card X \<le> card (reachable ?E_s X)" 
                  using \<open>card X \<le> card (reachable E X) - 1\<close> le_trans by blast
              qed
            qed
          qed
        qed
        then have " \<exists>M. cover_matching ?E_s M ?A_s"
          using "2" "3" \<open>card (A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u}) < card A\<close> 
            \<open>partitioned_bipartite (E - {e \<in> E. u \<in> e \<or> v \<in> e}) (A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u})\<close> 
            less.hyps by presburger  
        then  obtain M where "cover_matching ?E_s M ?A_s" by auto
        have "?A_s = A - {u}"
        proof - 
          have " A - {u} \<subseteq> Vs ?E_s" 
          proof
            fix a 
            assume "a \<in> A - {u}"
            then have "{a} \<subset> A" using card2 by auto

            then have "card (reachable E {a}) > card {a}" 
              using "7" by blast
            then have "card (reachable E {a}) \<ge> 2" by simp
            then have "\<exists> v1 v2. v1 \<noteq> v2 \<and> v1 \<in> reachable E {a} \<and> v2 \<in> reachable E {a}" 
              by (metis \<open>card {a} < card (reachable E {a})\<close> card.empty card.insert card_le_Suc0_iff_eq card_le_Suc_iff empty_iff finite.emptyI finite_insert not_less numerals(2))
            then obtain v1 v2 where "v1 \<noteq> v2 \<and> v1 \<in> reachable E {a} \<and> v2 \<in> reachable E {a}" by auto
            then have "v1 \<noteq> v \<or> v2 \<noteq> v" by blast
            then have "\<exists> v'. v' \<noteq> v \<and> (\<exists> u \<in> {a}. \<exists> e \<in> E. v' \<noteq> u \<and> u \<in> e \<and> v' \<in> e)"
              by (smt (verit, ccfv_SIG) \<open>v1 \<noteq> v2 \<and> v1 \<in> reachable E {a} \<and> v2 \<in> reachable E {a}\<close> mem_Collect_eq reachable_def)
            then have "\<exists> v'. v' \<noteq> v \<and> ( \<exists> e \<in> E. v' \<noteq> a \<and> a \<in> e \<and> v' \<in> e)"
              by blast
            then obtain v' e' where "v' \<noteq> v \<and> e' \<in> E \<and>  v' \<noteq> a \<and> a \<in> e' \<and> v' \<in> e'"  by blast
            then have "e' = {a, v'}"
              using less.prems(1) by fastforce
            then have "a \<in> A \<and> v' \<in> Vs E - A"
              using `partitioned_bipartite E A` 
              unfolding partitioned_bipartite_def
              by (metis Diff_iff \<open>a \<in> A - {u}\<close> \<open>v' \<noteq> v \<and> e' \<in> E \<and> v' \<noteq> a \<and> a \<in> e' \<and> v' \<in> e'\<close> doubleton_eq_iff)
            have "a \<noteq> u"  
              using \<open>a \<in> A - {u}\<close> by blast
            have "a \<noteq> v"
              using \<open>(u \<in> A \<and> v \<in> Vs E - A)\<close> \<open>{a} \<subset> A\<close> by blast
            have "v' \<noteq> v"
              by (simp add: \<open>v' \<noteq> v \<and> e' \<in> E \<and> v' \<noteq> a \<and> a \<in> e' \<and> v' \<in> e'\<close>)
            have "v' \<in> reachable E {a}"
              using \<open>v' \<noteq> v \<and> e' \<in> E \<and> v' \<noteq> a \<and> a \<in> e' \<and> v' \<in> e'\<close> reachable_def by fastforce
            have "v' \<in> Vs E - A"
              using \<open>a \<in> A \<and> v' \<in> Vs E - A\<close> by blast
            have "v' \<noteq> u" 
              using \<open>e = {u, v} \<and> u \<in> A \<and> v \<in> Vs E - A\<close> \<open>v' \<in> Vs E - A\<close> by blast
            then have "e' \<in> E \<and> a \<in> e' \<and> u \<notin> e' \<and> v \<notin> e'"
              using \<open>a \<noteq> u\<close> \<open>a \<noteq> v\<close> \<open>e' = {a, v'}\<close> \<open>v' \<noteq> v \<and> e' \<in> E \<and> v' \<noteq> a \<and> a \<in> e' \<and> v' \<in> e'\<close> by fastforce

            then have "\<exists> e \<in> E. a \<in> e \<and> e \<notin> {e. e \<in> E \<and> (u \<in> e \<or> v \<in> e)}" by auto
            show "a \<in> Vs ?E_s"
              using \<open>\<exists>e\<in>E. a \<in> e \<and> e \<notin> {e \<in> E. u \<in> e \<or> v \<in> e}\<close> by blast
          qed   
          then show ?thesis
            by blast
        qed
        have "cover_matching E M ?A_s" using `cover_matching ?E_s M ?A_s` unfolding cover_matching_def
          using less.prems(1) by blast
        then have "cover_matching E M (A - {u})" 
          by (simp add: \<open>A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u} = A - {u}\<close>)
        then have "A - {u} \<subseteq> Vs M" 
          by (simp add: cover_matching_def)
        have "M \<subseteq> E"  using \<open>cover_matching E M (A - {u})\<close> cover_matching_def by blast
        have "matching M" 
          using \<open>cover_matching E M (A - {u})\<close> cover_matching_def by blast
        have "\<forall> e \<in> M. u \<notin> e \<and> v \<notin> e "
          by (metis (no_types, lifting) \<open>cover_matching (E - {e \<in> E. u \<in> e \<or> v \<in> e}) M (A \<inter> Vs (E - {e \<in> E. u \<in> e \<or> v \<in> e}) - {u})\<close> cover_matching_def mem_Collect_eq set_diff_eq subset_iff)
        then have "\<forall> e \<in> M. e \<noteq> {u, v} \<longrightarrow> e \<inter> {u, v} = {}" 
          by simp
        have 8:"matching (insert {u, v} M)" using `matching M` unfolding matching_def  
          using \<open>\<forall>e\<in>M. e \<noteq> {u, v} \<longrightarrow> e \<inter> {u, v} = {}\<close> by auto 
        then have "A \<subseteq> Vs (insert {u, v} M)" using `A - {u} \<subseteq> Vs M` 
          by (smt (verit, ccfv_threshold) Sup_insert UnCI Vs_def \<open>e = {u, v} \<and> u \<in> A \<and> v \<in> Vs E - A\<close> insertCI insertE insert_Diff subset_iff)
        have "insert {u, v} M \<subseteq> E" using `{u, v} \<in> E`  
          using \<open>M \<subseteq> E\<close> by blast
        then have "cover_matching E (insert {u, v} M) A"
          unfolding cover_matching_def using  `graph_invar E` 8 
          using \<open>A \<subseteq> Vs (insert {u, v} M)\<close> by blast
        then show ?thesis by auto
      qed

    next
      case False
      have "\<exists> X \<subset> A. X \<noteq> {} \<and> card (reachable E X) \<le> card X" 
        using False le_less_linear by blast
      then have "\<exists> X \<subset> A. X \<noteq> {} \<and> card (reachable E X) = card X"
        by (metis False less.prems(4) order.order_iff_strict)
      then obtain X where "X \<subset> A \<and> X \<noteq> {}\<and> card (reachable E X) = card X" by auto
      then have "X \<subset> A" by auto
      have "card X = card (reachable E X)"
        by (simp add: \<open>X \<subset> A \<and> X \<noteq> {} \<and> card (reachable E X) = card X\<close>)
      show ?thesis
      proof -
        let ?X_gr = "{e \<in> E. \<exists>x\<in>X. x \<in> e}"

        have " ?X_gr \<subseteq> E" by auto
        have "\<forall> Y \<subseteq> A. card Y \<le> card (reachable E Y)"
          using less.prems(4) by blast
        then  have  "\<forall> Y \<subseteq> X. card Y \<le> card (reachable E Y)" 
          by (meson \<open>X \<subset> A\<close> psubsetE subset_psubset_trans)
        have 1:"\<forall> Y \<subseteq> X. (reachable E Y) = reachable ?X_gr Y"
        proof
          fix Y
          show " Y \<subseteq> X \<longrightarrow> (reachable E Y) = reachable ?X_gr Y"
          proof
            assume "Y \<subseteq> X"
            show " (reachable E Y) = reachable ?X_gr Y"
            proof
              show "(reachable E Y) \<subseteq> reachable ?X_gr Y"
              proof
                fix x 
                assume "x \<in> (reachable E Y)"
                then have " \<exists> u \<in> Y. \<exists> e \<in> E. x \<noteq> u \<and> u \<in> e \<and> x\<in> e" unfolding reachable_def

                  by blast
                then have "\<exists>e \<in> E. \<exists>x\<in>X. x \<in> e" 
                  using \<open>Y \<subseteq> X\<close> by blast
                show "x \<in> reachable ?X_gr Y" 
                  using \<open>Y \<subseteq> X\<close> \<open>\<exists>u\<in>Y. \<exists>e\<in>E. x \<noteq> u \<and> u \<in> e \<and> x \<in> e\<close> reachable_def by fastforce
              qed
              show " reachable ?X_gr Y \<subseteq> (reachable E Y) " unfolding reachable_def 
                using `?X_gr \<subseteq> E`
                by blast
            qed
          qed
        qed

        have "card X < card A" using `X \<subset> A` 
          by (meson finite_subset less.prems(1) less.prems(2) psubset_card_mono)


        then have " graph_invar ?X_gr" 
          by (metis (no_types, lifting) Vs_subset \<open>{e \<in> E. \<exists>x\<in>X. x \<in> e} \<subseteq> E\<close> finite_subset less.prems(1) subsetD)
        have " X \<subseteq> Vs ?X_gr"
        proof
          fix x 
          assume "x \<in> X" 
          have "\<exists> e \<in> E. x \<in> e"
            by (meson \<open>X \<subset> A \<and> X \<noteq> {} \<and> card (reachable E X) = card X\<close> \<open>x \<in> X\<close> less.prems(2) psubsetD subsetD vs_member_elim) 
          show " x \<in> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e}" 
            using \<open>\<exists>e\<in>E. x \<in> e\<close> \<open>x \<in> X\<close> by blast
        qed

        have "(\<forall>e\<in> ?X_gr. \<exists>u v. e = {u, v} \<and>
              (u \<in> X \<and> v \<in> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e} - X \<or>
               u \<in> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e} - X \<and> v \<in> X))"
        proof 
          fix e
          assume "e \<in> ?X_gr"
          have "e \<in> E" 
            using \<open>e \<in> {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> by blast
          have "( \<forall> e \<in> E. \<exists> u v.  e= {u, v}  \<and> ((u \<in> A \<and> v \<in> Vs E - A) \<or> (u \<in> Vs E -  A \<and> v \<in> A)))"
            using `partitioned_bipartite E A` 
            by (meson partitioned_bipartite_def)
          then have "\<forall> e \<in> E. \<exists> u v.  e= {u, v}  \<and> ((u \<in> A \<and> v \<in> Vs E - A))"
            by (metis insert_commute)
          then obtain u v where " e= {u, v}  \<and> ((u \<in> A \<and> v \<in> Vs E - A))"
            by (meson \<open>e \<in> E\<close>)
          then  have "\<exists>x\<in>X. x \<in> e" using `e \<in> ?X_gr` by auto
          then obtain x where "x \<in> X \<and> x \<in> e" by auto
          then have "x = u"
            using \<open>X \<subset> A\<close> \<open>e = {u, v} \<and> u \<in> A \<and> v \<in> Vs E - A\<close> by blast
          have "v \<in> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e}" 
            using \<open>e = {u, v} \<and> u \<in> A \<and> v \<in> Vs E - A\<close> \<open>e \<in> {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> vs_member by fastforce
          then have "v \<in>  Vs {e \<in> E. \<exists>x\<in>X. x \<in> e} - X" 
            using \<open>X \<subset> A\<close> \<open>e = {u, v} \<and> u \<in> A \<and> v \<in> Vs E - A\<close> by blast


          then  show "\<exists>u v. e = {u, v} \<and>
              (u \<in> X \<and> v \<in> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e} - X \<or>
               u \<in> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e} - X \<and> v \<in> X)"
            using \<open>e = {u, v} \<and> u \<in> A \<and> v \<in> Vs E - A\<close> \<open>x \<in> X \<and> x \<in> e\<close> by blast
        qed   
        then  have "partitioned_bipartite ?X_gr X"
          by (simp add: \<open>X \<subseteq> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> \<open>graph_invar {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> partitioned_bipartite_def)

        then have "\<exists>M. cover_matching ?X_gr M X" using
            ` card X < card A` `X \<subseteq> Vs ?X_gr`
          using `graph_invar ?X_gr` less.hyps 1 
          using \<open>\<forall>Y\<subseteq>X. card Y \<le> card (reachable E Y)\<close> by presburger


        let ?AX_gr = "{e. e \<in> E \<and> (\<exists> x \<in> A - X. \<exists> y \<in> Vs E - (reachable E X) - A. y \<in> e \<and>  x \<in> e)}"
        have "?X_gr \<inter> ?AX_gr = {}"
        proof(rule ccontr)
          assume "?X_gr \<inter> ?AX_gr \<noteq> {}"
          then have "\<exists> e. e \<in> ?X_gr \<inter> ?AX_gr" by auto
          then obtain e where "e \<in> ?X_gr \<inter> ?AX_gr" by auto
          then have "(\<exists> x \<in> A - X. \<exists> y \<in> Vs E - (reachable E X) - A. y \<in> e \<and>  x \<in> e)" by auto
          then obtain x y where 1:" x \<in> A - X \<and>  y \<in> Vs E -(reachable E X) - A \<and> y \<in> e \<and>  x \<in> e" by auto
          have "\<exists>x\<in>X. x \<in> e" using `e \<in> ?X_gr \<inter> ?AX_gr` by auto
          then have "x \<in> X \<or> y \<in> X"
            using \<open>e \<in> {e \<in> E. \<exists>x\<in>X. x \<in> e} \<inter> {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - (reachable E X) - A. y \<in> e \<and> x \<in> e}\<close>

            by (smt (verit, del_insts) Diff_iff Int_iff \<open>X \<subset> A\<close> mem_Collect_eq psubsetD reachable_def)

          then show False 
            using "1" \<open>X \<subset> A\<close> by blast
        qed


        have "?AX_gr \<subseteq> E" 
          by blast
        have "X \<noteq> {}"
          by (simp add: \<open>X \<subset> A \<and> X \<noteq> {} \<and> card (reachable E X) = card X\<close>)
        have " card (A - X) < card A"
          by (metis \<open>X \<noteq> {}\<close> \<open>X \<subset> A\<close> card_Diff_subset card_gt_0_iff diff_less dual_order.strict_implies_order finite_subset less.prems(1) less.prems(2) subset_empty)
        have "graph_invar ?AX_gr" using `?AX_gr \<subseteq> E`
          by (meson Vs_subset finite_subset less.prems(1) subsetD)
        have "(A - X) \<subseteq> Vs ?AX_gr"
        proof
          fix x
          assume "x \<in> (A - X)"
          then have
            "card (reachable E (X \<union> {x})) \<ge> card (X \<union> {x})"
            using \<open>X \<subset> A \<and> X \<noteq> {} \<and> card (reachable E X) = card X\<close> less.prems(4) by force
          then have "card (reachable E (X \<union> {x})) > card X" 
            using \<open>X \<subseteq> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> \<open>graph_invar {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> \<open>x \<in> A - X\<close> card_seteq finite.emptyI finite_subset by fastforce
          then have "card (reachable E (X \<union> {x})) > card (reachable E (X))"
            by (simp add: \<open>X \<subset> A \<and> X \<noteq> {} \<and> card (reachable E X) = card X\<close>)
          have "X \<subseteq> X \<union> {x}"  by auto
          then  have  "(reachable E (X)) \<subseteq> (reachable E (X \<union> {x})) "
            unfolding reachable_def
            by blast
          then have "(reachable E (X)) \<subset> (reachable E (X \<union> {x})) "
            using `card (reachable E (X \<union> {x})) > card (reachable E (X))`  
            by force
          then have "\<exists> z. z\<in> reachable E (X \<union> {x}) \<and> z\<notin> reachable E (X)" 
            by blast
          then obtain z where 1:"z\<in> reachable E (X \<union> {x}) \<and> z\<notin> reachable E (X)"
            by blast
          then have "\<exists> u \<in> (X \<union> {x}). \<exists> e \<in> E. z \<noteq> u \<and> u \<in> e \<and> z\<in> e" 
            by (simp add: reachable_def)
          have "\<nexists> u . u \<in> X \<and> ( \<exists> e \<in> E. z \<noteq> u \<and> u \<in> e \<and> z\<in> e)" using 1                    
            using reachable_def by force
          then have "\<exists> u \<in> {x}. \<exists> e \<in> E. z \<noteq> u \<and> u \<in> e \<and> z\<in> e"
            using \<open>\<exists>u\<in>X \<union> {x}. \<exists>e\<in>E. z \<noteq> u \<and> u \<in> e \<and> z \<in> e\<close> by blast
          then  obtain x' e where "x' \<in> {x} \<and> e \<in> E \<and> z \<noteq> x' \<and> x' \<in> e \<and> z\<in> e" by auto
          then have "x' = x" by auto
          then have "e = {x, z}"
            using \<open>x' \<in> {x} \<and> e \<in> E \<and> z \<noteq> x' \<and> x' \<in> e \<and> z \<in> e\<close> less.prems(1) by fastforce
          have "z \<in> Vs E - A" using 1
            by (metis Diff_iff \<open>e = {x, z}\<close> \<open>x \<in> A - X\<close> \<open>x' \<in> {x} \<and> e \<in> E \<and> z \<noteq> x' \<and> x' \<in> e \<and> z \<in> e\<close> doubleton_eq_iff less.prems(3) partitioned_bipartite_def)
          then have "z \<in> Vs E - A - reachable E X"
            using "1" by blast
          then have "e \<in> E \<and> x\<in>A - X \<and>  z \<in>Vs E - reachable E X - A \<and>  z \<in> e \<and> x \<in> e" 

            using \<open>x \<in> A - X\<close> \<open>x' \<in> {x} \<and> e \<in> E \<and> z \<noteq> x' \<and> x' \<in> e \<and> z \<in> e\<close> by blast
          then have "e \<in> ?AX_gr" 
            by blast
          then show "x \<in> Vs ?AX_gr"
            using \<open>e \<in> E \<and> x \<in> A - X \<and> z \<in> Vs E - reachable E X - A \<and> z \<in> e \<and> x \<in> e\<close> by blast
        qed
        have "Vs E - reachable E X - A \<subseteq> Vs ?AX_gr" 
        proof
          fix x
          assume "x \<in> Vs E - reachable E X - A" 
          then have "\<exists> e \<in> E. x \<in> e"
            by (meson DiffD1 vs_member_elim)
          then obtain e where "e \<in> E \<and> x \<in> e" by auto
          have "x \<notin> reachable E X"
            using \<open>x \<in> Vs E - reachable E X - A\<close> by blast
          then  have "\<nexists> u . u \<in> X \<and> ( \<exists> e \<in> E. x \<noteq> u \<and> u \<in> e \<and> x\<in> e)"                    
            using reachable_def by force
          have "\<exists> u \<in> A. (x \<noteq> u \<and> u \<in> e \<and> x\<in> e)"
            using `partitioned_bipartite E A` unfolding partitioned_bipartite_def 
            by (metis DiffD2 \<open>e \<in> E \<and> x \<in> e\<close> \<open>x \<in> Vs E - reachable E X - A\<close> insertCI) 
          then have "\<exists> u. u \<in> (A - X) \<and>  x \<noteq> u \<and> u \<in> e \<and> x\<in> e"
            using \<open>\<nexists>u. u \<in> X \<and> (\<exists>e\<in>E. x \<noteq> u \<and> u \<in> e \<and> x \<in> e)\<close> \<open>e \<in> E \<and> x \<in> e\<close> by auto
          then have "e \<in> ?AX_gr"
            using \<open>e \<in> E \<and> x \<in> e\<close> \<open>x \<in> Vs E - reachable E X - A\<close> by blast
          then show "x \<in> Vs ?AX_gr"
            by (meson \<open>e \<in> E \<and> x \<in> e\<close> vs_member_intro)
        qed
        then have "Vs E - reachable E X - A \<subseteq> Vs ?AX_gr - (A - X)"
          by blast
        have "(\<forall>e\<in> ?AX_gr. \<exists>u v. e = {u, v} \<and> (u \<in> A - X \<and> v \<in> Vs ?AX_gr - (A - X)))" 
        proof 
          fix e
          assume "e \<in> ?AX_gr"
          have "e \<in> E"
            using \<open>e \<in> {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e}\<close> by fastforce
          have "( \<forall> e \<in> E. \<exists> u v.  e= {u, v}  \<and> ((u \<in> A \<and> v \<in> Vs E - A) \<or> (u \<in> Vs E -  A \<and> v \<in> A)))"
            using `partitioned_bipartite E A` 
            by (meson partitioned_bipartite_def)
          then have "\<forall> e \<in> E. \<exists> u v.  e= {u, v}  \<and> ((u \<in> A \<and> v \<in> Vs E - A))"
            by (metis insert_commute)
          then obtain u v where " e= {u, v}  \<and> ((u \<in> A \<and> v \<in> Vs E - A))"
            by (meson \<open>e \<in> E\<close>)
          have "\<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e"
            using `e \<in> ?AX_gr`
            by blast
          then obtain u1 v1  where "u1 \<in> A - X \<and> v1 \<in> Vs E - reachable E X - A \<and> u1 \<in> e \<and> v1 \<in> e" by auto
          then have "u = u1 \<and> v = v1"
            using \<open>X \<subset> A\<close> \<open>e = {u, v} \<and> u \<in> A \<and> v \<in> Vs E - A\<close> by blast


          then  show "\<exists>u v. e = {u, v} \<and>
              (u \<in> (A - X) \<and> v \<in> Vs ?AX_gr - (A -X))"
            using \<open>e = {u, v} \<and> u \<in> A \<and> v \<in> Vs E - A\<close>
            by (metis (no_types, lifting) Diff_eq_empty_iff Diff_iff \<open>Vs E - reachable E X - A \<subseteq> Vs {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} - (A - X)\<close> \<open>u1 \<in> A - X \<and> v1 \<in> Vs E - reachable E X - A \<and> u1 \<in> e \<and> v1 \<in> e\<close> empty_iff)
        qed   

        then have "partitioned_bipartite ?AX_gr (A - X)" unfolding 
            partitioned_bipartite_def 
          by (metis (no_types, lifting) \<open>A - X \<subseteq> Vs {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e}\<close> \<open>graph_invar {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e}\<close>)

        have "\<forall>Y\<subseteq>(A-X). card Y \<le> card (reachable ?AX_gr Y)"
        proof
          fix Y
          show " Y \<subseteq> (A-X) \<longrightarrow> card Y \<le> card (reachable ?AX_gr Y)" 
          proof
            assume " Y \<subseteq> (A-X)"
            have " reachable ?AX_gr Y = reachable E Y - reachable E X"
            proof
              show "reachable ?AX_gr Y \<subseteq> reachable E Y - reachable E X"
              proof
                fix x
                assume "x \<in> reachable ?AX_gr Y"
                have " reachable ?AX_gr Y \<subseteq> reachable E Y" using `?AX_gr \<subseteq> E` unfolding reachable_def
                  by blast
                then have "x \<in> reachable E Y"
                  using \<open>x \<in> reachable {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} Y\<close> by blast
                have "\<exists> u . u \<in> Y \<and> ( \<exists> e \<in> ?AX_gr. x \<noteq> u \<and> u \<in> e \<and> x\<in> e)" 
                  by (smt (verit, ccfv_threshold) \<open>x \<in> reachable {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} Y\<close> mem_Collect_eq reachable_def)
                then obtain u e where " u \<in> Y \<and>  e \<in> ?AX_gr \<and> x \<noteq> u \<and> u \<in> e \<and> x\<in> e" by auto
                then have "\<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e" 
                  by blast
                then have "u \<in> A - X" 
                  using \<open>Y \<subseteq> A - X\<close> \<open>u \<in> Y \<and> e \<in> {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} \<and> x \<noteq> u \<and> u \<in> e \<and> x \<in> e\<close> by blast
                then have "x \<in> Vs E - reachable E X - A"
                  using Diff_disjoint Int_iff \<open>Vs E - reachable E X - A \<subseteq> Vs {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} - (A - X)\<close> \<open>\<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e\<close> \<open>\<forall>e\<in>{e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e}. \<exists>u v. e = {u, v} \<and> u \<in> A - X \<and> v \<in> Vs {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} - (A - X)\<close> \<open>u \<in> Y \<and> e \<in> {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} \<and> x \<noteq> u \<and> u \<in> e \<and> x \<in> e\<close> by auto

                then  have " x \<notin>  reachable E X" by auto 
                then  show "x \<in> reachable E Y - reachable E X"
                  by (simp add: \<open>x \<in> reachable E Y\<close>) 
              qed
              show "reachable E Y - reachable E X \<subseteq> reachable ?AX_gr Y"
              proof
                fix x
                assume "x \<in> reachable E Y - reachable E X"
                then have "x \<in> reachable E Y"
                  by simp
                have " reachable E Y \<subseteq> Vs E - A"
                proof 
                  fix y 
                  assume "y \<in> reachable E Y"
                  then have "\<exists> u . u \<in> Y \<and> ( \<exists> e \<in> E. y \<noteq> u \<and> u \<in> e \<and> y\<in> e)" unfolding reachable_def                  
                    by blast
                  then obtain u e where "u \<in> Y \<and> e \<in> E \<and> y \<noteq> u \<and> u \<in> e \<and> y\<in> e" by auto
                  have "(e \<in> E \<and> ( \<exists> u v.  e= {u, v}  \<and> (u \<in> A \<and> v \<in> Vs E - A)))" using 
                      `partitioned_bipartite E A` unfolding partitioned_bipartite_def 
                    by (metis \<open>u \<in> Y \<and> e \<in> E \<and> y \<noteq> u \<and> u \<in> e \<and> y \<in> e\<close> doubleton_eq_iff)
                  then show "y \<in> Vs E - A"
                    using \<open>Y \<subseteq> A - X\<close> \<open>u \<in> Y \<and> e \<in> E \<and> y \<noteq> u \<and> u \<in> e \<and> y \<in> e\<close> by auto
                qed
                then have " x \<in> Vs E - reachable E X - A"
                  using \<open>x \<in> reachable E Y - reachable E X\<close> by blast
                then have "\<exists> u . u \<in> Y \<and> ( \<exists> e \<in> E. x \<noteq> u \<and> u \<in> e \<and> x\<in> e) " 
                  using   `x \<in> reachable E Y` unfolding  reachable_def  by blast
                then obtain u e where "u \<in> Y \<and>  e \<in> E \<and> x \<noteq> u \<and> u \<in> e \<and> x\<in> e" by auto
                then have " e \<in> ?AX_gr" 
                  using \<open>Y \<subseteq> A - X\<close> \<open>x \<in> Vs E - reachable E X - A\<close> by blast 
                then show "x \<in> reachable ?AX_gr Y"
                  using \<open>u \<in> Y \<and> e \<in> E \<and> x \<noteq> u \<and> u \<in> e \<and> x \<in> e\<close> mem_Collect_eq reachable_def by fastforce
              qed
            qed
            then have "card (reachable ?AX_gr Y) = card (reachable E Y - reachable E X)"
              by presburger
            have "reachable E (Y \<union> X) = reachable E Y \<union> reachable E X" 
            proof
              show "reachable E (Y \<union> X) \<subseteq> reachable E Y \<union> reachable E X" 
              proof
                fix x 
                assume "x \<in> reachable E (Y \<union> X)"
                then have "\<exists> u . u \<in> Y \<union> X \<and> ( \<exists> e \<in> E. x \<noteq> u \<and> u \<in> e \<and> x\<in> e)" unfolding reachable_def by blast
                then have "\<exists> u . (u \<in> Y  \<and> ( \<exists> e \<in> E. x \<noteq> u \<and> u \<in> e \<and> x\<in> e))
                          \<or> (\<exists> u . u \<in> X \<and> ( \<exists> e \<in> E. x \<noteq> u \<and> u \<in> e \<and> x\<in> e))" by auto
                then show "x \<in>  reachable E Y \<union> reachable E X" unfolding reachable_def 
                  using UnE by blast
              qed
              show "reachable E Y \<union> reachable E X \<subseteq> reachable E (Y \<union> X)" 
              proof
                fix x
                assume "x \<in> reachable E Y \<union> reachable E X"
                then have "\<exists> u . (u \<in> Y  \<and> ( \<exists> e \<in> E. x \<noteq> u \<and> u \<in> e \<and> x\<in> e))
                          \<or> (\<exists> u . u \<in> X \<and> ( \<exists> e \<in> E. x \<noteq> u \<and> u \<in> e \<and> x\<in> e))" unfolding reachable_def 
                  by blast
                then show "x \<in>   reachable E (Y \<union> X)" unfolding reachable_def by blast
              qed
            qed
            then have "reachable E (Y \<union> X) = (reachable E Y - reachable E X) \<union> reachable E X"
              by simp
            have "(reachable E Y - reachable E X) \<inter> reachable E X = {}"  by auto
            then have "card (reachable E (Y \<union> X))  = 
                  card (reachable E Y - reachable E X) + card (reachable E X)"

              by (smt (verit, ccfv_threshold) Diff_subset Un_Int_eq(3) Un_subset_iff \<open>A - X \<subseteq> Vs {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e}\<close> \<open>X \<subset> A \<and> X \<noteq> {} \<and> card (reachable E X) = card X\<close> \<open>X \<subseteq> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> \<open>Y \<subseteq> A - X\<close> \<open>graph_invar {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e}\<close> \<open>graph_invar {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> \<open>reachable E (Y \<union> X) = reachable E Y - reachable E X \<union> reachable E X\<close> \<open>reachable {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} Y = reachable E Y - reachable E X\<close> \<open>{e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} \<subseteq> E\<close> add.right_neutral card.empty card.infinite card_Un_disjoint card_seteq dual_order.strict_implies_order finite_Un finite_reachable finite_subset less.prems(1) less.prems(4) subset_trans sup.cobounded2)
            then have "card (reachable E Y - reachable E X) = 
                card (reachable E (Y \<union> X)) - card (reachable E X)" by auto
            have "card (reachable E (Y \<union> X)) \<ge> card (Y \<union> X)"
              by (metis Diff_subset \<open>X \<subset> A \<and> X \<noteq> {} \<and> card (reachable E X) = card X\<close> \<open>Y \<subseteq> A - X\<close> dual_order.strict_implies_order le_sup_iff less.prems(4) subset_Un_eq)
            then have "card (reachable E (Y \<union> X)) - card (reachable E X) \<ge> card (Y \<union> X) - card X"
              using `card X = card (reachable E X)` by auto
            then have "card (reachable ?AX_gr Y) \<ge> card (Y \<union> X) - card X"
              using \<open>card (reachable E Y - reachable E X) = card (reachable E (Y \<union> X)) - card (reachable E X)\<close> \<open>reachable {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} Y = reachable E Y - reachable E X\<close> by presburger
            have "X \<inter> Y = {}"
              by (metis Diff_eq Int_commute Int_subset_iff \<open>Y \<subseteq> A - X\<close> disjoint_eq_subset_Compl)

            then have "card (Y \<union> X) - card X = card Y"
              by (metis (no_types, lifting) \<open>A - X \<subseteq> Vs {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e}\<close> \<open>X \<subseteq> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> \<open>Y \<subseteq> A - X\<close> \<open>graph_invar {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e}\<close> \<open>graph_invar {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> add_diff_cancel_left' card_Un_disjoint finite_subset sup_commute)

            then show "card Y \<le> card (reachable ?AX_gr Y)" 
              using \<open>card (Y \<union> X) - card X \<le> card (reachable {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} Y)\<close> by presburger
          qed
        qed
        then have "\<exists>M.  cover_matching ?AX_gr M (A-X)" 
          using \<open>A - X \<subseteq> Vs {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e}\<close> \<open>card (A - X) < card A\<close> \<open>graph_invar {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e}\<close> \<open>partitioned_bipartite {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} (A - X)\<close> less.hyps by presburger
        then obtain M' where " cover_matching ?AX_gr M' (A-X)" by auto
        obtain M where " cover_matching ?X_gr M X"
          using \<open>\<exists>M. cover_matching {e \<in> E. \<exists>x\<in>X. x \<in> e} M X\<close> by blast

        have "Vs ?X_gr \<inter> Vs ?AX_gr = {}"
        proof(rule ccontr)
          assume "Vs ?X_gr \<inter> Vs ?AX_gr \<noteq> {}"
          then have "\<exists> z. z \<in> Vs ?X_gr \<and> z\<in> Vs ?AX_gr" by auto
          then obtain z where 1: "z \<in> Vs ?X_gr \<and> z\<in> Vs ?AX_gr" by auto
          then have "\<exists> e \<in> E. \<exists>x\<in>X. x \<in> e \<and> z \<in> e"
            by (smt (verit, ccfv_SIG) mem_Collect_eq vs_member_elim)
          then obtain e' x' where "e' \<in> E \<and> x'\<in>X \<and> x' \<in> e' \<and> z \<in> e'" by auto
          have " \<exists> e \<in> ?AX_gr. z \<in> e" using 1 
            by (metis (no_types, lifting) vs_member_elim)

          then have "\<exists> e \<in> E. z \<in> e \<and> (\<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e)"
            by blast 
          then obtain e x y where "e \<in> E \<and>  z \<in> e \<and> x\<in>A - X \<and> y\<in>Vs E - reachable E X - A \<and> y \<in> e \<and> x \<in> e" by auto
          then have "z = x \<or> z = y"
            using less.prems(1) by fastforce
          then have "z \<in> A - X \<or> z\<in> Vs E - reachable E X - A"
            using \<open>e \<in> E \<and> z \<in> e \<and> x \<in> A - X \<and> y \<in> Vs E - reachable E X - A \<and> y \<in> e \<and> x \<in> e\<close> by presburger
          show False
          proof (cases "z \<in> X")
            case True
            have "z \<notin> A" using `z \<in> A - X \<or> z\<in> Vs E - reachable E X - A` 
              using True by blast
            then show ?thesis
              using True \<open>X \<subset> A\<close> by blast
          next
            case False
            then have "z \<notin> X" 
              by simp
            have  "e' \<in> E \<and> x'\<in>X \<and> x' \<in> e' \<and> z \<in> e'"
              by (simp add: \<open>e' \<in> E \<and> x' \<in> X \<and> x' \<in> e' \<and> z \<in> e'\<close>)
            have "x' \<noteq> z"
              using False \<open>e' \<in> E \<and> x' \<in> X \<and> x' \<in> e' \<and> z \<in> e'\<close> by auto
            then have "z \<in> reachable E X"
              using \<open>e' \<in> E \<and> x' \<in> X \<and> x' \<in> e' \<and> z \<in> e'\<close> reachable_def by fastforce
            then have " z \<in> A - X" using `z \<in> A - X \<or> z\<in> Vs E - reachable E X - A` by blast
            have "\<exists>u v. e' = {u, v} \<and> (u \<in> A \<and> v \<in> Vs E - A)"
              using `partitioned_bipartite E A` unfolding partitioned_bipartite_def
              by (metis \<open>e' \<in> E \<and> x' \<in> X \<and> x' \<in> e' \<and> z \<in> e'\<close> doubleton_eq_iff)
            then have "z \<in> Vs E - A"
              using \<open>X \<subset> A\<close> \<open>e' \<in> E \<and> x' \<in> X \<and> x' \<in> e' \<and> z \<in> e'\<close> \<open>z \<in> A - X\<close> by blast
            then show ?thesis
              using \<open>z \<in> A - X\<close> by blast
          qed
        qed
        then have "Vs M \<subseteq> Vs ?X_gr" 
          by (metis (no_types, lifting) Vs_subset \<open>cover_matching {e \<in> E. \<exists>x\<in>X. x \<in> e} M X\<close> cover_matching_def)
        have " Vs M' \<subseteq> Vs ?AX_gr"
          by (metis (no_types, lifting) Vs_subset \<open>cover_matching {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} M' (A - X)\<close> cover_matching_def)
        then have "Vs M \<inter> Vs M' = {}" 
          using \<open>Vs M \<subseteq> Vs {e \<in> E. \<exists>x\<in>X. x \<in> e}\<close> \<open>Vs {e \<in> E. \<exists>x\<in>X. x \<in> e} \<inter> Vs {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} = {}\<close> by blast
        then have "Vs M \<union> Vs M' = Vs (M \<union> M')"
          by (simp add: Vs_def)
        have "\<forall>v \<in> Vs (M \<union> M'). \<exists>!e\<in>(M \<union> M'). v \<in> e" 
        proof 
          fix v
          assume "v \<in> Vs (M \<union> M')" 
          show " \<exists>!e\<in>(M \<union> M'). v \<in> e"
          proof(cases "v\<in>Vs M")
            case True
            then have "v \<notin> Vs  M'"
              using \<open>Vs M \<inter> Vs M' = {}\<close> by blast
            have "\<exists>!e\<in>(M). v \<in> e" by (meson True \<open>cover_matching {e \<in> E. \<exists>x\<in>X. x \<in> e} M X\<close> cover_matching_def matching_unique_match vs_member)

            then show ?thesis
              by (metis UnE \<open>v \<notin> Vs M'\<close> subsetD sup_ge1 vs_member)
          next
            case False
            then have "v \<notin> Vs  M"
              using \<open>Vs M \<inter> Vs M' = {}\<close> by blast
            have "\<exists>!e\<in>(M'). v \<in> e" 
              by (meson False UnE \<open>cover_matching {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} M' (A - X)\<close> \<open>v \<in> Vs (M \<union> M')\<close> cover_matching_def matching_unique_match vs_member)

            then show ?thesis 
              using False UnE by blast
          qed
        qed

        then  have "matching (M \<union> M')" 
          by (simp add: matching_def2)
        have "M \<union> M' \<subseteq> E"
          by (meson Un_subset_iff \<open>cover_matching {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} M' (A - X)\<close> \<open>cover_matching {e \<in> E. \<exists>x\<in>X. x \<in> e} M X\<close> \<open>{e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} \<subseteq> E\<close> \<open>{e \<in> E. \<exists>x\<in>X. x \<in> e} \<subseteq> E\<close> cover_matching_def subset_trans)
        have "X \<subseteq> Vs M" 
          by (meson \<open>cover_matching {e \<in> E. \<exists>x\<in>X. x \<in> e} M X\<close> cover_matching_def)
        have "A-X \<subseteq> Vs M'"
          by (meson \<open>cover_matching {e \<in> E. \<exists>x\<in>A - X. \<exists>y\<in>Vs E - reachable E X - A. y \<in> e \<and> x \<in> e} M' (A - X)\<close> cover_matching_def)
        then have "A \<subseteq> Vs (M \<union> M')" 
          by (smt (z3) Un_Diff_cancel2 Un_mono \<open>Vs M \<union> Vs M' = Vs (M \<union> M')\<close> \<open>X \<subset> A\<close> \<open>X \<subseteq> Vs M\<close> sup.strict_order_iff sup_commute)
        then have "cover_matching E (M \<union> M') A" unfolding cover_matching_def 
          using \<open>M \<union> M' \<subseteq> E\<close> \<open>matching (M \<union> M')\<close> less.prems(1) by fastforce

        then show "\<exists>M. cover_matching E M A" by auto
      qed
    qed
  next
    case False
    then  have "card A < 2" by auto
    show ?thesis
    proof(cases "card A = 0")
      case True
      have "A = {}"
        by (meson True card_eq_0_iff less.prems(1) less.prems(2) rev_finite_subset)
      then show ?thesis
        by (metis cover_matching_def empty_iff empty_subsetI less.prems(1) matching_def)
    next
      case False
      then have "card A  = 1" using `card A < 2` 
        by simp
      then have "\<exists>a \<in> Vs E. A = {a}"
        by (metis card_1_singletonE insert_subset less.prems(2))
      then obtain a where "a \<in> Vs E \<and>  A = {a}" by auto
      then have "\<exists>e \<in> E. a \<in> e"
        by (meson vs_member_elim)
      then obtain e where "e \<in> E \<and> a \<in> e" by auto
      then have "matching {e}"
        using matching_def by blast
      have "A \<subseteq> Vs {e}"
        using \<open>e \<in> E \<and> a \<in> e\<close>
        using \<open>a \<in> Vs E \<and> A = {a}\<close> by blast
      have "cover_matching E {e} A" unfolding cover_matching_def
        by (simp add: \<open>A \<subseteq> Vs {e}\<close> \<open>e \<in> E \<and> a \<in> e\<close> \<open>matching {e}\<close> less.prems(1))
      then show ?thesis by auto
    qed
  qed
qed

lemma hall:
  fixes E :: "'a set set"
  assumes "partitioned_bipartite E A"
  shows "(\<exists> M. cover_matching E M A) \<longleftrightarrow> (\<forall> X \<subseteq> A. card (reachable E X) \<ge> card X)"
proof
  show "(\<exists>M. cover_matching E M A) \<Longrightarrow> (\<forall>X\<subseteq>A. card X \<le> card (reachable E X))"
  proof -
    assume "\<exists> M. cover_matching E M A"
    then show "\<forall>X\<subseteq>A. card X \<le> card (reachable E X)" using assms hall1 by auto
  qed
  show "(\<forall> X \<subseteq> A. card (reachable E X) \<ge> card X) \<Longrightarrow>(\<exists> M. cover_matching E M A) "
  proof -
    assume "(\<forall> X \<subseteq> A. card (reachable E X) \<ge> card X)"
    have "graph_invar E" using assms unfolding partitioned_bipartite_def by auto
    have "A \<subseteq> Vs E"  using assms unfolding partitioned_bipartite_def by auto
    then show "(\<exists> M. cover_matching E M A)" using assms hall2 
      by (simp add: hall2 \<open>\<forall>X\<subseteq>A. card X \<le> card (reachable E X)\<close> \<open>graph_invar E\<close>)
  qed
qed


lemma frobeneus_matching:
 fixes E :: "'a set set"
 assumes "partitioned_bipartite E A"
 shows "(\<exists> M. perfect_matching E M) \<longleftrightarrow> (\<forall> X \<subseteq> A. card (reachable E X) \<ge> card X) \<and> ((card A) = card (Vs E - A))"
proof
  show " \<exists>M. perfect_matching E M \<Longrightarrow> (\<forall>X\<subseteq>A. card X  \<le> card (reachable E X)) \<and> card A = card (Vs E - A)"
  proof -
    assume "\<exists>M. perfect_matching E M"
    show "(\<forall>X\<subseteq>A. card X  \<le> card (reachable E X)) \<and> card A = card (Vs E - A)"
    proof
      obtain M where "perfect_matching E M" using \<open>\<exists>M. perfect_matching E M\<close> by auto
      then  have "Vs M = Vs E" unfolding perfect_matching_def by auto
      then have "A \<subseteq> Vs M"
        using assms partitioned_bipartite_def by fastforce
      then have "cover_matching E M A"
        by (meson \<open>perfect_matching E M\<close> cover_matching_def perfect_matching_def)
      then show "\<forall>X\<subseteq>A. card X  \<le> card (reachable E X)" using assms hall by auto
      have "card A  \<le> card (reachable E A)"
        by (simp add: \<open>\<forall>X\<subseteq>A. card X \<le> card (reachable E X)\<close>)
      have "Vs E - A = reachable E A" by (simp add: assms reachble_bipartite)
      have "partitioned_bipartite E (Vs E - A)" using assms
        by (simp add: partitioned_bipartite_swap)
      then have "cover_matching E M (Vs E - A)"
        by (metis Diff_subset \<open>Vs M = Vs E\<close> \<open>cover_matching E M A\<close> cover_matching_def)
      then have "card (Vs E - A) \<le> card (reachable E (Vs E - A))"
        using hall \<open>partitioned_bipartite E (Vs E - A)\<close> 
        by blast
      then have "A = reachable E (Vs E - A)" 
        using  reachble_bipartite \<open>partitioned_bipartite E (Vs E - A)\<close>
        by (metis assms double_diff partitioned_bipartite_def subset_refl)
      show "card A = card (Vs E - A)" 
        using \<open>A = reachable E (Vs E - A)\<close> \<open>Vs E - A = reachable E A\<close> \<open>card (Vs E - A) \<le> card (reachable E (Vs E - A))\<close> \<open>card A \<le> card (reachable E A)\<close> by fastforce
    qed
  qed
  show " (\<forall>X\<subseteq>A. card X \<le> card (reachable E X)) \<and> card A = card (Vs E - A) \<Longrightarrow> \<exists>M. perfect_matching E M"
  proof -
    assume "(\<forall>X\<subseteq>A. card X \<le> card (reachable E X)) \<and> card A = card (Vs E - A)"
    then  have "\<forall>X\<subseteq>A. card X \<le> card (reachable E X)" by auto
    then have "\<exists>M. cover_matching E M A" using hall assms by auto
    then obtain M where "cover_matching E M A" by auto
    have "card A = card (reachable M A)"
      by (metis \<open>cover_matching E M A\<close> assms hall_reachable order_refl)
    have "reachable M A \<subseteq> reachable E A"
      by (metis Diff_mono Vs_subset \<open>cover_matching E M A\<close> assms cover_matching_def halrewrw order_refl reachble_bipartite)
    have "Vs E - A = reachable E A" by (simp add: assms reachble_bipartite)

    then have "reachable M A = Vs E - A"
      by (metis \<open>(\<forall>X\<subseteq>A. card X \<le> card (reachable E X)) \<and> card A = card (Vs E - A)\<close> \<open>card A = card (reachable M A)\<close> \<open>cover_matching E M A\<close> \<open>reachable M A \<subseteq> reachable E A\<close> card_subset_eq cover_matching_def finite_Diff)
     have " Vs E  = Vs M"
      by (metis Diff_partition \<open>cover_matching E M A\<close> \<open>reachable M A = Vs E - A\<close> assms halrewrw partitioned_bipartite_def reachble_bipartite)

    then  show "\<exists>M. perfect_matching E M"
      by (smt (verit) \<open>cover_matching E M A\<close> cover_matching_def perfect_matching_def)
  qed
qed

end