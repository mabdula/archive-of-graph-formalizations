theory Tutte_matrix
  imports "HOL-Algebra.Cycles" "HOL-Analysis.Determinants" Tutte_theorem3
begin




lemma cancel_even_sum:
  fixes A :: "'a::comm_ring_1 set"
  assumes "finite A"
  assumes "even (card A)"
  assumes "\<forall>a \<in> A. \<exists>!a' \<in> A. a \<noteq> a' \<and> (a' + a = 0)" 
  shows "\<Sum> A = 0"
  using assms
proof(induct "card A" arbitrary: A rule: less_induct)
  case less

  then show ?case
  proof(cases "card A = 0")
    case True
    have "A = {}" 
      using True card_0_eq less.prems(1) by blast
    then show ?thesis 
      using sum_clauses(1) by blast
  next
    case False
    then show ?thesis
    proof(cases "odd (card A)")
      case True
      then show ?thesis 
        using less.prems(2) by blast
    next
      case False
      have "even (card A)" using False by auto

      obtain a where "a \<in> A \<and> a \<noteq> 0" 
        using \<open>card A \<noteq> 0\<close> 
        by (metis Diff_eq_empty_iff One_nat_def card.empty card_Suc_Diff1 equals0I less.prems(1) less.prems(2) odd_one singletonI subset_eq)

      then obtain a' where "a' \<in> A \<and> a + a' = 0" 
        by (metis add.commute less.prems(3))
      have "card (A - {a, a'}) < card A" 
        by (metis Diff_insert2 \<open>a \<in> A \<and> a \<noteq> 0\<close> \<open>a' \<in> A \<and> a + a' = 0\<close> card_Diff2_less less.prems(1))
      have "a \<noteq> a'" 
        by (metis \<open>a' \<in> A \<and> a + a' = 0\<close> add_right_cancel less.prems(3))
      then have "even (card (A - {a, a'}))" 
        by (simp add: \<open>a \<in> A \<and> a \<noteq> 0\<close> \<open>a' \<in> A \<and> a + a' = 0\<close> less.prems(1) less.prems(2)) 
      have " \<forall>x\<in>(A - {a, a'}).  \<exists>!x'. x' \<in> (A - {a, a'}) \<and> x \<noteq> x' \<and> x' + x = 0" 
        by (smt (verit, ccfv_SIG) DiffD1 Diff_insert Diff_insert_absorb \<open>a' \<in> A \<and> a + a' = 0\<close> add_diff_cancel add_diff_cancel_left' insert_iff less.prems(3) mk_disjoint_insert)

      have "\<Sum> (A - {a, a'}) = 0" using less.hyps  
        using \<open>\<forall>x\<in>A - {a, a'}. \<exists>!x'. x' \<in> A - {a, a'} \<and> x \<noteq> x' \<and> x' + x = 0\<close> \<open>card (A - {a, a'}) < card A\<close> \<open>even (card (A - {a, a'}))\<close> less.prems(1) by auto
      have "\<Sum>A = \<Sum> (A - {a, a'}) + \<Sum> {a, a'}" 
        by (meson \<open>a \<in> A \<and> a \<noteq> 0\<close> \<open>a' \<in> A \<and> a + a' = 0\<close> empty_subsetI insert_subset less.prems(1) sum.subset_diff)
      then show "\<Sum>A = 0" 
        by (simp add: \<open>\<Sum> (A - {a, a'}) = 0\<close> \<open>a \<noteq> a'\<close> \<open>a' \<in> A \<and> a + a' = 0\<close>)
    qed
  qed
qed

lemma even_set_pairs_inverse:
  fixes A :: "'a::comm_ring_1 set"
  assumes "finite A"
  assumes "odd (card A)"
  assumes "\<forall>a \<in> A. \<exists>!a' \<in> A. a \<noteq> a' \<and> (a' + a = 0)" 
  shows "\<Sum> A = 0" 
  using assms
proof(induct "card A" arbitrary: A rule: less_induct)
  case less
  have "card A \<noteq> 0" 
    by (metis card.empty less.prems(2) odd_card_imp_not_empty)
  have "odd (card A)"
    by (simp add: less.prems(2))
  show ?case
  proof(cases "card A  = 1")
    case True
    then show ?thesis 
      by (metis cancel_comm_monoid_add_class.diff_cancel card_0_eq card_Diff_singleton empty_iff finite_Diff insertE insert_Diff less.prems(1) less.prems(3) sum.neutral)

  next
    case False
    have "card A > 1" 
      by (meson False \<open>card A \<noteq> 0\<close> less_one linorder_neqE_nat)
    then  obtain a where "a \<in> A \<and> a \<noteq> 0" 
      using \<open>card A \<noteq> 0\<close> 
      by (metis card.empty equals0I less.prems(3))

    then obtain a' where "a' \<in> A \<and> a + a' = 0" 
      by (metis add.commute less.prems(3))
    have "card (A - {a, a'}) < card A" 
      by (metis Diff_insert2 \<open>a \<in> A \<and> a \<noteq> 0\<close> \<open>a' \<in> A \<and> a + a' = 0\<close> card_Diff2_less less.prems(1))
    have "a \<noteq> a'" 
      by (metis \<open>a' \<in> A \<and> a + a' = 0\<close> add_right_cancel less.prems(3))
    then have "odd (card (A - {a, a'}))" 
      using \<open>1 < card A\<close> \<open>a \<in> A \<and> a \<noteq> 0\<close> \<open>a' \<in> A \<and> a + a' = 0\<close> less.prems(1) less.prems(2) by auto
    have " \<forall>x\<in>(A - {a, a'}).  \<exists>!x'. x' \<in> (A - {a, a'}) \<and> x \<noteq> x' \<and> x' + x = 0" 
      by (smt (verit, ccfv_SIG) DiffD1 Diff_insert Diff_insert_absorb \<open>a' \<in> A \<and> a + a' = 0\<close> add_diff_cancel add_diff_cancel_left' insert_iff less.prems(3) mk_disjoint_insert)

    have "\<Sum> (A - {a, a'}) = 0" using less.hyps  
      using \<open>\<forall>x\<in>A - {a, a'}. \<exists>!x'. x' \<in> A - {a, a'} \<and> x \<noteq> x' \<and> x' + x = 0\<close> \<open>card (A - {a, a'}) < card A\<close> \<open>odd (card (A - {a, a'}))\<close> less.prems(1) by auto
    have "\<Sum>A = \<Sum> (A - {a, a'}) + \<Sum> {a, a'}" 
      by (meson \<open>a \<in> A \<and> a \<noteq> 0\<close> \<open>a' \<in> A \<and> a + a' = 0\<close> empty_subsetI insert_subset less.prems(1) sum.subset_diff)
    then show "\<Sum>A = 0" 
      by (simp add: \<open>\<Sum> (A - {a, a'}) = 0\<close> \<open>a \<noteq> a'\<close> \<open>a' \<in> A \<and> a + a' = 0\<close>)
  qed
qed

lemma cancel_sum:
  fixes A :: "'a::comm_ring_1 set"
  assumes "finite A"
  assumes "\<forall>a \<in> A. \<exists>!a' \<in> A. a \<noteq> a' \<and> (a' + a = 0)" 
  shows "\<Sum> A = 0"
  using assms(1) assms(2) cancel_even_sum even_set_pairs_inverse by blast


lemma dewe':
  fixes A :: "'a  set"
  fixes f :: "'a \<Rightarrow> 'a"
  fixes val :: "'a \<Rightarrow> 'n::comm_ring_1" 
  assumes "finite A"
  assumes "\<forall>a \<in> A.  f a \<in> A"
  assumes "\<forall>a \<in> A. f ( f a) = a"
  assumes "\<forall>a \<in> A. val a + val (f a) = 0"
  assumes "\<forall>a \<in> A. a = f a \<longrightarrow> val a = 0"
  shows "sum val A = 0"
  using assms
proof(induct "card A" arbitrary: A rule: less_induct)
  case less

  then show ?case
  proof(cases "card A = 0")
    case True
    have "A = {}"  
      using True card_0_eq less.prems(1) by blast
    then show ?thesis 
      using sum_clauses(1) by blast
  next
    case False

    show "sum val A = 0"
    proof(cases "\<forall>x \<in> A. f x = x")
      case True
      then show ?thesis 
        by (simp add: less.prems(5))
    next
      case False

      obtain a where "a \<in> A \<and> f a \<noteq> a" using False 
        by fastforce


      then obtain a' where "a' = f a" 
        by simp
      then have "a'\<in> A" 
        by (simp add: \<open>a \<in> A \<and> f a \<noteq> a\<close> less.prems(2))
      have "card (A - {a, a'}) < card A" 
        by (metis Diff_insert2 \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' \<in> A\<close> card_Diff2_less less.prems(1))
      have " \<forall>x\<in>(A - {a, a'}). f x \<in> (A - {a, a'})" 
        by (metis Diff_iff \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' = f a\<close> empty_iff insert_iff less.prems(2) less.prems(3))
      have " \<forall>x\<in>(A - {a, a'}). f (f x) = x" 
        by (meson DiffD1 less.prems(3))
      have " \<forall>x\<in>(A - {a, a'}). val x + val (f x) = 0" 
        by (meson DiffD1 less.prems(4))
      then have "sum val (A - {a, a'}) = 0" 
        using \<open>\<forall>x\<in>A - {a, a'}. f (f x) = x\<close> \<open>\<forall>x\<in>A - {a, a'}. f x \<in> A - {a, a'}\<close> \<open>card (A - {a, a'}) < card A\<close> less.hyps less.prems(1)

        using less.prems(5) by fastforce
      have "val a + val (f a) = 0" 
        using \<open>a \<in> A \<and> f a \<noteq> a\<close> less.prems(4) by auto
      have "sum val {a, a'} = 0" 
        using \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' = f a\<close> \<open>val a + val (f a) = 0\<close> by force

      then show "sum val A = 0" 
        by (smt (verit, ccfv_SIG) Diff_insert \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' \<in> A\<close> \<open>sum val (A - {a, a'}) = 0\<close> empty_iff finite.emptyI finite.insertI finite_Diff_insert insertE insert_Diff_single insert_absorb insert_commute less.prems(1) singleton_iff sum.empty sum.insert_remove sum_clauses(2))
    qed
  qed
qed

value "set [a, b]"  

lemma "fst (1, 3) = 1" by simp

value[simp] "vec (1, 3)"


context fixes X :: "('a \<times> 'a) set" begin

definition verts where 
  "verts = {x. \<exists> e \<in> X. x = fst e \<or> x = snd e} "

inductive dpath where
  dpath0: "dpath []" |
  dpath1: "v \<in> verts  \<Longrightarrow> dpath [v]" |
  dpath2: "(v,v') \<in> X \<Longrightarrow> dpath (v'#vs) \<Longrightarrow> dpath (v#v'#vs)"
end

value[nbe] "path {{1::nat, 2}, {2, 3}, {3, 4}} [1, 4, 3] = True"

declare dpath0[simp]

inductive_simps dpath_1[simp]: "dpath X [v]"

inductive_simps dpath_2[simp]: "dpath X (v # v' # vs)"

definition "dwalk_betw E u p v \<equiv> (p \<noteq> [] \<and> dpath E p \<and> hd p = u \<and> last p = v)"


locale tutte_matrix =
  fixes E :: "'a::wellorder set set"
  fixes f :: "'n::finite \<Rightarrow> 'a "  
  assumes graph: "graph_invar E"
  assumes bij: "bij_betw f (UNIV :: 'n set) (Vs E)"
begin 

lemma vertices_in_range:
  assumes "x \<in> Vs E" 
  shows "\<exists> a \<in> (UNIV :: 'n set). f a = x" using bij  
  by (metis assms bij_betw_def imageE)

definition list_vertices :: " 'a list" where 
  "list_vertices  = sorted_list_of_set (Vs E)"

definition vert :: " 'a^'n" where
  "vert  = (\<chi> i. f i) "


definition oriented_edges :: " ('a \<times> 'a) set"  where 
  "oriented_edges  = {(a, b)| a b.   {a, b} \<in>  E \<and> a < b}"

definition all_oriented :: "('a \<times> 'a) set"  where 
  "all_oriented  = {(a, b)| a b.   {a, b} \<in>  E}"

lemma oriented_edges[elim?]:
  assumes "(a, b) \<in> oriented_edges" 
  shows "{a, b} \<in> E" using assms unfolding oriented_edges_def  
  by force


definition tutte_matrix:: " ('a set => 'b ) \<Rightarrow> 'b::comm_ring_1^'n^'n" where
  "tutte_matrix x = (\<chi> i j. if (f i, f j) \<in> oriented_edges  then x {f i, f j}
                            else 
                                (if (f j, f i) \<in> oriented_edges then (- x {f i, f j}) 
                                 else 0 ))"

lemma in_oriented:
  assumes "(f i, f j) \<in> oriented_edges"
  shows "tutte_matrix x $i$j = x {f i, f j}" 
  unfolding tutte_matrix_def 
  using assms by fastforce

lemma rev_in_oriented:
  assumes "(f j, f i) \<in> oriented_edges"
  shows "tutte_matrix x $i$j = - x {f i, f j}" 
proof -
  have "(f i, f j) \<notin> oriented_edges" 
    using assms order_less_asym oriented_edges_def by auto
  then show ?thesis   unfolding tutte_matrix_def 
    using assms by fastforce
qed

lemma not_in_edges:
  assumes "{f i, f j} \<notin> E"
  shows "tutte_matrix x $i$j = 0"
proof -
 have "(f i, f j) \<notin> oriented_edges" 
   using assms order_less_asym oriented_edges_def by auto
 have "(f j, f i) \<notin> oriented_edges" 
    using assms  oriented_edges_def 
    by (metis (mono_tags, lifting) insert_commute oriented_edges)
  show ?thesis  unfolding tutte_matrix_def 
    by (simp add: \<open>(f i, f j) \<notin> oriented_edges\<close> \<open>(f j, f i) \<notin> oriented_edges\<close>)
qed

lemma not_in_both_oriented:
  assumes "(f j, f i) \<notin> oriented_edges"
  assumes "(f i, f j) \<notin> oriented_edges" 
  shows "{f i, f j} \<notin> E"
proof(rule ccontr)
  assume "\<not> {f i, f j} \<notin> E"
  then have "{f i, f j} \<in> E" by auto
  have "f i \<ge> f j" using assms(1) oriented_edges_def 
    using \<open>{f i, f j} \<in> E\<close> assms(2) by auto
  have "f i \<le> f j" using assms(1) oriented_edges_def 
    using \<open>{f i, f j} \<in> E\<close> assms(2) 
    by (smt (verit) CollectI insert_commute le_less_linear)
  then have "f i= f j" 
    using \<open>f j \<le> f i\<close> by auto
  then show False 
    using \<open>{f i, f j} \<in> E\<close> graph by fastforce
qed

lemma edge_not_in_E_zero_elem:
  assumes "{f i, f j} \<notin> E"
  shows "tutte_matrix X$i$j = 0"
proof -
  have "(f i, f j) \<notin> oriented_edges" using assms 
    by (meson oriented_edges)
  have "(f j, f i) \<notin> oriented_edges" using assms 
    by (metis insert_commute oriented_edges)
  then show ?thesis 
    by (simp add: \<open>(f i, f j) \<notin> oriented_edges\<close> local.tutte_matrix_def)
qed

lemma tutte_matrix_det:
  "det (tutte_matrix x) =  sum (\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set))
      {p. p permutes (UNIV :: 'n set)}" 
  using det_def by blast

definition all_perms where 
  "all_perms = {p. p permutes (UNIV :: 'n set)}"

definition nonzero_perms :: "('a set => 'b::comm_ring_1 ) \<Rightarrow> ('n \<Rightarrow> 'n) set "where
  "nonzero_perms x = {p. p permutes (UNIV :: 'n set) \<and> 
         prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set) \<noteq> 0}"

definition p_edges :: "('n \<Rightarrow> 'n) \<Rightarrow> ('a \<times> 'a) set" where
  "p_edges p = {(f i, f (p i))|i. i \<in> (UNIV :: 'n set)}"


definition u_edges :: "('n \<Rightarrow> 'n) \<Rightarrow> 'a set  set" where
  "u_edges p = {{f i, f (p i)}|i. i \<in> (UNIV :: 'n set)}"


lemma wqewqe:
  assumes "p \<in> nonzero_perms x"
  shows "p_edges p \<subseteq> all_oriented"
proof
  fix e
  assume "e \<in> p_edges p"
  then obtain i where "e = (f i, f (p i)) \<and>  i \<in> (UNIV :: 'n set)" 
    unfolding p_edges_def by auto
  have "p permutes (UNIV :: 'n set) \<and> 
         prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set) \<noteq> 0"
    using assms unfolding nonzero_perms_def by auto
  then have "prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set) \<noteq> 0" by auto
  have "\<forall>i \<in> (UNIV :: 'n set).  (tutte_matrix x)$i$p i \<noteq> 0" 
  proof
    fix i
    assume "i \<in> (UNIV :: 'n set)"
    have "finite (UNIV :: 'n set)" 
      by simp
    show "(tutte_matrix x)$i$p i \<noteq> 0"
    proof(rule ccontr)
      assume " \<not> local.tutte_matrix x $ i $ p i \<noteq> 0"
      then have "local.tutte_matrix x $ i $ p i = 0" by auto
      then have "prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set) = 0"
        using Groups_Big.comm_semiring_1_class.prod_zero   \<open>finite UNIV\<close> \<open>i \<in> UNIV\<close>
        by fast
      then show False 
        using \<open>(\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i) \<noteq> 0\<close> by blast  
    qed
  qed
  then have "(tutte_matrix x)$i$p i \<noteq> 0" 
    by blast
  have "(f i, f (p i)) \<in> oriented_edges \<or> (f (p i), f i) \<in> oriented_edges"
  proof(rule ccontr)
    assume " \<not> ((f i, f (p i)) \<in> oriented_edges \<or>
        (f (p i), f i) \<in> oriented_edges)"
    then have " (f i, f (p i)) \<notin> oriented_edges" 
      by auto
    have "(f (p i), f i) \<notin> oriented_edges" 
      using \<open>\<not> ((f i, f (p i)) \<in> oriented_edges \<or> (f (p i), f i) \<in> oriented_edges)\<close> by auto
    then have "(tutte_matrix x)$i$p i = 0" unfolding tutte_matrix_def 
      using \<open>\<not> ((f i, f (p i)) \<in> oriented_edges \<or> (f (p i), f i) \<in> oriented_edges)\<close> by auto
    then show False 
      using \<open>local.tutte_matrix x $ i $ p i \<noteq> 0\<close> by auto
  qed
  then have "{f i, f (p i)} \<in> E" 
    by (metis insert_commute oriented_edges)
  then show "e \<in> all_oriented" 
    by (simp add: \<open>e = (f i, f (p i)) \<and> i \<in> UNIV\<close> all_oriented_def)
qed


lemma wqewqe1:
  assumes "p \<in> nonzero_perms x"
  shows "u_edges p \<subseteq> E"
proof
  fix e
  assume "e \<in> u_edges p"
  then obtain i where "e = {f i, f (p i)} \<and>  i \<in> (UNIV :: 'n set)" 
    unfolding u_edges_def by auto
  have "p permutes (UNIV :: 'n set) \<and> 
         prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set) \<noteq> 0"
    using assms unfolding nonzero_perms_def by auto
  then have "prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set) \<noteq> 0" by auto
  have "\<forall>i \<in> (UNIV :: 'n set).  (tutte_matrix x)$i$p i \<noteq> 0" 
  proof
    fix i
    assume "i \<in> (UNIV :: 'n set)"
    have "finite (UNIV :: 'n set)" 
      by simp
    show "(tutte_matrix x)$i$p i \<noteq> 0"
    proof(rule ccontr)
      assume " \<not> local.tutte_matrix x $ i $ p i \<noteq> 0"
      then have "local.tutte_matrix x $ i $ p i = 0" by auto
      then have "prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set) = 0"
        using Groups_Big.comm_semiring_1_class.prod_zero   \<open>finite UNIV\<close> \<open>i \<in> UNIV\<close>
        by fast
      then show False 
        using \<open>(\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i) \<noteq> 0\<close> by blast  
    qed
  qed
  then have "(tutte_matrix x)$i$p i \<noteq> 0" 
    by blast
  have "(f i, f (p i)) \<in> oriented_edges \<or> (f (p i), f i) \<in> oriented_edges"
  proof(rule ccontr)
    assume " \<not> ((f i, f (p i)) \<in> oriented_edges \<or>
        (f (p i), f i) \<in> oriented_edges)"
    then have " (f i, f (p i)) \<notin> oriented_edges" 
      by auto
    have "(f (p i), f i) \<notin> oriented_edges" 
      using \<open>\<not> ((f i, f (p i)) \<in> oriented_edges \<or> (f (p i), f i) \<in> oriented_edges)\<close> by auto
    then have "(tutte_matrix x)$i$p i = 0" unfolding tutte_matrix_def 
      using \<open>\<not> ((f i, f (p i)) \<in> oriented_edges \<or> (f (p i), f i) \<in> oriented_edges)\<close> by auto
    then show False 
      using \<open>local.tutte_matrix x $ i $ p i \<noteq> 0\<close> by auto
  qed
  then have "{f i, f (p i)} \<in> E" 
    by (metis insert_commute oriented_edges)
  then show "e \<in> E" 
    using \<open>e = {f i, f (p i)} \<and> i \<in> UNIV\<close> by auto
qed

lemma directed_same_verts:
  assumes "p \<in> nonzero_perms X"
  shows "verts (p_edges p) = Vs E"
proof(safe)
  {
    fix x
    assume "x \<in> verts (p_edges p)" 
    then obtain e where "(fst e = x \<or> snd e = x) \<and> e \<in> (p_edges p)" 
      by (smt (z3) mem_Collect_eq verts_def)
    then have "e \<in> all_oriented"  using wqewqe assms by auto  
    then obtain a b where "e = (a, b) \<and> {a, b} \<in> E" 
      using all_oriented_def by auto
    then have "x = a \<or> x = b" 
      using \<open>(fst e = x \<or> snd e = x) \<and> e \<in> p_edges p\<close> by force
    show " x \<in> Vs E" 
      using \<open>e = (a, b) \<and> {a, b} \<in> E\<close> \<open>x = a \<or> x = b\<close> insert_commute by auto
  }
  fix x
  assume "x \<in> Vs E"
  obtain i where "i \<in> (UNIV :: 'n set) \<and> f i = x" using vertices_in_range
    using \<open>x \<in> Vs E\<close> by blast
  then have "(f i, f (p i)) \<in> (p_edges p)" unfolding p_edges_def by auto
  then have "f i \<in> verts (p_edges p)" 
    using verts_def by force
  then show "x \<in> verts (p_edges p)" 
    by (simp add: \<open>i \<in> UNIV \<and> f i = x\<close>)
qed

lemma one_out_egde_in_perm:
  assumes "p \<in> nonzero_perms X"
  assumes "x \<in> Vs E"
  shows"\<exists>!e \<in> p_edges p. fst e = x"
proof(safe)
  obtain i where "i \<in> (UNIV :: 'n set) \<and> f i = x" using vertices_in_range
    using \<open>x \<in> Vs E\<close> by blast
  then have "(f i, f (p i)) \<in> (p_edges p)" unfolding p_edges_def by auto
  then show "\<exists> a. a \<in> p_edges p \<and> fst a = x" 
    using \<open>i \<in> UNIV \<and> f i = x\<close> by auto
  {
    fix a b aa ba
    assume "(a, b) \<in> p_edges p"
      " x = fst (a, b)"
      "(aa, ba) \<in> p_edges p"
      "fst (aa, ba) = fst (a, b)" 
    then show "a = aa" 
      by simp
  }
  fix a b aa ba
  assume "(a, b) \<in> p_edges p"
    " x = fst (a, b)"
    "(aa, ba) \<in> p_edges p"
    "fst (aa, ba) = fst (a, b)"
  then show "b = ba" 
    by (smt  bij bij_betw_iff_bijections fst_conv mem_Collect_eq p_edges_def snd_conv)
qed

lemma one_in_egde_in_perm:
  assumes "p \<in> nonzero_perms X"
  assumes "x \<in> Vs E"
  shows"\<exists>!e \<in> p_edges p. snd e = x"
proof(safe)
  have "p permutes  (UNIV :: 'n set)" using assms(1) unfolding nonzero_perms_def by auto
  obtain i where "i \<in> (UNIV :: 'n set) \<and> f i = x" using vertices_in_range
    using \<open>x \<in> Vs E\<close> by blast
  then obtain j where "j \<in> (UNIV :: 'n set) \<and> p j = i" 
    by (meson \<open>p permutes UNIV\<close> iso_tuple_UNIV_I permutes_univ)
  then have "(f j, f (p j)) \<in> (p_edges p)" unfolding p_edges_def by auto
  then have "(f j, x) \<in> (p_edges p)" 
    by (simp add: \<open>i \<in> UNIV \<and> f i = x\<close> \<open>j \<in> UNIV \<and> p j = i\<close>)
  then show "\<exists>e. e \<in> p_edges p \<and> snd e = x" 
    by auto
  {
    fix a b aa ba
    assume "(a, b) \<in> p_edges p"
      "x = snd (a, b)"
      "(aa, ba) \<in> p_edges p"
      "snd (aa, ba) = snd (a, b)"  
    show "a = aa" 
      by (smt (verit, del_insts) \<open>(a, b) \<in> p_edges p\<close> \<open>(aa, ba) \<in> p_edges p\<close> \<open>p permutes UNIV\<close> \<open>snd (aa, ba) = snd (a, b)\<close> bij bij_betw_iff_bijections fst_conv mem_Collect_eq p_edges_def permutes_imp_bij snd_conv)
  }
  fix a b aa ba
  assume "(a, b) \<in> p_edges p"
    "x = snd (a, b)"
    "(aa, ba) \<in> p_edges p"
    "snd (aa, ba) = snd (a, b)"
  show "b = ba" 
    using \<open>snd (aa, ba) = snd (a, b)\<close> by auto
qed

lemma u_edges_finite:
  shows "finite (u_edges p)"
proof -
  have "finite (UNIV :: 'n set)" 
    by simp
  let ?g = "(\<lambda> i. {{f i, f (p i)}})"
  have " (\<Union>i\<in>(UNIV :: 'n set). (?g i)) = (u_edges p)" unfolding u_edges_def 
    apply safe
     apply blast
    by blast
  have "finite (\<Union>i\<in>(UNIV :: 'n set). (?g i))" 
    using \<open>finite UNIV\<close> by blast

  show ?thesis 
    using \<open>(\<Union>i. {{f i, f (p i)}}) = u_edges p\<close> \<open>finite (\<Union>i. {{f i, f (p i)}})\<close> by presburger
qed

lemma u_edges_is_graph:
  assumes "p \<in> nonzero_perms X"
  shows "graph_invar (u_edges p)" 
  by (metis assms graph graph_invar_subset tutte_matrix.wqewqe1 tutte_matrix_axioms)

definition prev where
  "prev p x = (inv p) x" 

definition nxt where
  "nxt p x = p x"


lemma p_is_permutation:
  assumes "p permutes (UNIV :: 'n set)"
  shows "permutation p" 
  using assms finite_class.finite_UNIV permutation_permutes by blast

lemma even_circuits_connected_component:
  shows "(f ((p^^j) i), f ((p^^(j+1)) i)) \<in>  (p_edges p)" 
  using p_edges_def by auto

lemma even_circuits_connected_component':
  shows "{f ((p^^j) i), f ((p^^(j+1)) i)} \<in>  (u_edges p)" 
  using u_edges_def by auto

lemma nonzero_perms_not_id:
  assumes "p \<in> nonzero_perms X"
  shows "p i \<noteq> i" 
proof(rule ccontr)
  assume "\<not> (p i \<noteq> i)"
  then have "p i = i" by auto
  have "{f i, f i} \<notin> E" 
    using graph by fastforce
  then have "tutte_matrix X $ i $ p i = 0" using edge_not_in_E_zero_elem 
    by (metis \<open>\<not> p i \<noteq> i\<close>)
  then have "prod (\<lambda>i. (tutte_matrix X)$i$p i) (UNIV :: 'n set) = 0"
    using Groups_Big.comm_semiring_1_class.prod_zero 
      finite_class.finite_UNIV by fast  
  then show False using assms(1) nonzero_perms_def
    by blast   
qed

lemma oriented_edges_correspond_to_undirected:
  assumes "p \<in> nonzero_perms X"
  assumes "(x, y) \<in> (p_edges p)"
  shows "{x, y} \<in> u_edges p" 
proof -
  obtain i where "(f i, f (p i)) = (x, y)" 
    using assms(2) p_edges_def by auto
  then have "{f i, f (p i)} \<in> u_edges p" 
    using u_edges_def by auto
  then show ?thesis 
    using \<open>(f i, f (p i)) = (x, y)\<close> by blast
qed

lemma end_of_circuit_edge:
  assumes "p \<in> nonzero_perms X"
  assumes "i \<in> (UNIV :: 'n set)"
  shows "(f ((p^^((least_power p i)-1)) i), f i) \<in>  (p_edges p)" 
proof -
  have  "(f ((p^^((least_power p i)-1)) i), f ((p^^(((least_power p i)-1)+1)) i)) \<in>  (p_edges p)"
    using even_circuits_connected_component by blast
  have "p i \<noteq> i" using nonzero_perms_not_id assms(1) by auto
  have "permutation p" using assms(1) unfolding nonzero_perms_def 
    using p_is_permutation 
    by blast
  then obtain n where "(p ^^ n) = id" and "n > 0" using permutation_is_nilpotent
    by blast
  then have "least_power p i > 0" using least_powerI 
    by (simp add: \<open>permutation p\<close> least_power_of_permutation(2))
  then have "(f ((p^^((least_power p i)-1)) i), f ((p^^((least_power p i))) i)) \<in>  (p_edges p)"
    using \<open>(f ((p ^^ (least_power p i - 1)) i), f ((p ^^ (least_power p i - 1 + 1)) i)) \<in> p_edges p\<close> by force
  then show ?thesis 
    by (simp add: \<open>permutation p\<close> least_power_of_permutation(1))
qed

lemma fewfw:
  assumes "\<forall>i < size xs-1. (xs!i, xs!(i+1)) \<in> A"
  assumes "size xs \<ge> 2" 
  shows "dpath A xs" using assms
proof(induct xs)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a xs)
  have "length (a#xs) - 1 = length xs" 
    by simp
  have "\<forall>i<length xs-1. (xs ! i, xs ! (i + 1)) \<in> A" 
    using Cons.prems 
    using less_diff_conv by auto

  have " ((a # xs) ! 0, (a # xs) ! (0 + 1)) \<in> A" 
    using Cons.prems 
    by (metis One_nat_def Suc_pred \<open>length (a # xs) - 1 = length xs\<close> diff_Suc_1 diff_is_0_eq' length_greater_0_conv list.simps(3) list.size(3) nat_1_add_1 plus_1_eq_Suc)
  then have "(a, xs!0) \<in> A" 
    by simp
  show ?case
  proof(cases "xs = []")
    case True
    have "a \<in> verts A" unfolding verts_def using `(a, xs!0) \<in> A` 

      by force
    have "dpath A [a]" 
      by (simp add: \<open>a \<in> verts A\<close>)
    then show ?thesis 
      by (simp add: True)
  next
    case False


    have "xs \<noteq> []" 
      by (simp add: False)
    show ?thesis
    proof(cases "size xs = 1")
      case True

      have "xs!0 \<in> verts A" unfolding verts_def using `(a, xs!0) \<in> A` 
        by force
      have "xs = [xs!0]" 
        by (metis One_nat_def Suc_length_conv True length_0_conv nth_Cons_0)
      have "dpath A [a, xs!0]" 
        by (simp add: \<open>(a, xs ! 0) \<in> A\<close> \<open>xs ! 0 \<in> verts A\<close>)
      then show ?thesis 
        using \<open>xs = [xs ! 0]\<close> by auto
    next
      case False
      have " dpath A xs" 
        using Cons.hyps \<open>\<forall>i<length xs-1. (xs ! i, xs ! (i + 1)) \<in> A\<close> 
        by (metis False Suc_leI \<open>xs \<noteq> []\<close> length_greater_0_conv less_one nat_neq_iff one_add_one plus_1_eq_Suc)

      have "xs = hd xs # tl xs" 
        by (simp add: \<open>xs \<noteq> []\<close>)
      then have "(a, hd xs) \<in> A" 
        by (metis \<open>(a, xs ! 0) \<in> A\<close> nth_Cons_0)

      then show ?thesis 
        by (metis \<open>dpath A xs\<close> \<open>xs = hd xs # tl xs\<close> dpath_2) 
    qed
  qed
qed

lemma fewfw':
  assumes "\<forall>i < size xs-1. {xs!i, xs!(i+1)} \<in> A"
  assumes "size xs \<ge> 2" 
  shows "path A xs" using assms
proof(induct xs)
  case Nil
  then show ?case 
    by auto
next
  case (Cons a xs)
  have "length (a#xs) - 1 = length xs" 
    by simp
  have "\<forall>i<length xs-1. {xs ! i, xs ! (i + 1)} \<in> A" 
    using Cons.prems 
    using less_diff_conv by auto

  have " {(a # xs) ! 0, (a # xs) ! (0 + 1)} \<in> A" 
    using Cons.prems 
    by (metis One_nat_def Suc_pred \<open>length (a # xs) - 1 = length xs\<close> diff_Suc_1 diff_is_0_eq' length_greater_0_conv list.simps(3) list.size(3) nat_1_add_1 plus_1_eq_Suc)
  then have "{a, xs!0} \<in> A" 
    by simp
  show ?case
  proof(cases "xs = []")
    case True
    have "a \<in> Vs A" 
      by (meson \<open>{a, xs ! 0} \<in> A\<close> edges_are_Vs) 
    have "path A [a]" 
      by (simp add: \<open>a \<in> Vs A\<close>)
    then show ?thesis 
      by (simp add: True)
  next
    case False


    have "xs \<noteq> []" 
      by (simp add: False)
    show ?thesis
    proof(cases "size xs = 1")
      case True

      have "xs!0 \<in> Vs A" 
        using \<open>{(a # xs) ! 0, (a # xs) ! (0 + 1)} \<in> A\<close> nth_Cons' by auto
      have "xs = [xs!0]" 
        by (metis One_nat_def Suc_length_conv True length_0_conv nth_Cons_0)
      have "path A [a, xs!0]" 
        by (simp add: \<open>{a, xs ! 0} \<in> A\<close> \<open>xs ! 0 \<in> Vs A\<close>)
      then show ?thesis 
        using \<open>xs = [xs ! 0]\<close> by auto
    next
      case False
      have " path A xs" 
        using Cons.hyps \<open>\<forall>i<length xs-1. {xs ! i, xs ! (i + 1)} \<in> A\<close> 
        by (metis False Suc_leI \<open>xs \<noteq> []\<close> length_greater_0_conv less_one nat_neq_iff one_add_one plus_1_eq_Suc)

      have "xs = hd xs # tl xs" 
        by (simp add: \<open>xs \<noteq> []\<close>)
      then have "{a, hd xs} \<in> A" 
        by (metis \<open>{a, xs ! 0} \<in> A\<close> nth_Cons_0)

      then show ?thesis 
        by (metis \<open>path A xs\<close> \<open>xs = hd xs # tl xs\<close> path_2) 
    qed
  qed
qed



lemma circuit_is_dpath:
  assumes "p \<in> nonzero_perms X"
  shows "dpath (p_edges p) (map f (support p i))"
proof -
  let ?xs = "(map f (support p i))"
  have "\<forall>j <size ?xs. ?xs!j = f ((p^^j) i)" 
    by simp
  have "\<forall>i < size ?xs-1. (?xs!i, ?xs!(i+1)) \<in> (p_edges p)"
    using even_circuits_connected_component 
    by auto
  have "p i \<noteq> i" using nonzero_perms_not_id assms(1) by auto
  have "permutation p" using assms(1) unfolding nonzero_perms_def 
    using p_is_permutation 
    by blast

  have "(least_power p i) > 1" 
    by (simp add: \<open>p i \<noteq> i\<close> \<open>permutation p\<close> least_power_gt_one)
  then have "size (support p i) \<ge> 2" 
    by simp 
  then have "size  (map f (support p i)) \<ge> 2" 
    by simp
  then show "dpath (p_edges p) (map f (support p i))"
    using

fewfw 
    using \<open>\<forall>ia<length (map f (support p i)) - 1. (map f (support p i) ! ia, map f (support p i) ! (ia + 1)) \<in> p_edges p\<close> by blast
qed

lemma circuit_is_upath:
  assumes "p permutes (UNIV::'n set)"
  shows "path (u_edges p) (map f (support p i))"
proof(cases "p i \<noteq> i")
  case True
  let ?xs = "(map f (support p i))"
  have "\<forall>j <size ?xs. ?xs!j = f ((p^^j) i)" 
    by simp
  have "\<forall>i < size ?xs-1. {?xs!i, ?xs!(i+1)} \<in> (u_edges p)"
    using even_circuits_connected_component' 
    by auto
  have "p i \<noteq> i" using True by auto
  have "permutation p" using assms(1) unfolding nonzero_perms_def 
    using p_is_permutation 
    by blast

  have "(least_power p i) > 1" 
    by (simp add: \<open>p i \<noteq> i\<close> \<open>permutation p\<close> least_power_gt_one)
  then have "size (support p i) \<ge> 2" 
    by simp 
  then have "size  (map f (support p i)) \<ge> 2" 
    by simp
  then show "path (u_edges p) (map f (support p i))"
    using \<open>\<forall>ia<length (map f (support p i)) - 1. {map f (support p i) ! ia, map f (support p i) ! (ia + 1)} \<in> u_edges p\<close> fewfw' by blast
next
  case False
  have "p i = i" 
    using False by auto
  then have "{f i, f (p i)} \<in> u_edges p" 
    using u_edges_def by auto
  then have "f i \<in> Vs (u_edges p)" 
    by (meson edges_are_Vs)
  then have "path (u_edges p) [f i]" 
    by simp
  have "(p^^(Suc 0)) i = i" using `p i = i` 
    by auto
  then have "(p^^1) i = i" 
    by simp
  then have "least_power p i = 1" 
    by (meson least_power_minimal nat_dvd_1_iff_1)
  then have "support p i = [i]" 
    by simp
  then have "map f (support p i) = [f i]" by auto
  then show ?thesis 
    using \<open>path (u_edges p) [f i]\<close> by presburger
qed 

lemma dedge_in_circuit:
  assumes "Suc j < (least_power p i)" 
  shows "((map f (support p i))!j, (map f (support p i))!(Suc j)) \<in> p_edges p"
  using assms even_circuits_connected_component by force

lemma uedge_in_circuit:
  assumes "Suc j < (least_power p i)" 
  shows "{(map f (support p i))!j, (map f (support p i))!(Suc j)} \<in> u_edges p"
  using assms even_circuits_connected_component' by force


lemma support_is_connected_component:
  assumes "p permutes (UNIV :: 'n set)"
  assumes "C \<in> connected_components (u_edges p)" 
  assumes "f i \<in> C"
  shows "set (map f (support p i)) = C" (is "set ?l = C")
proof(safe)
  have "(support p i)!0 = (p^^0) i" 
    using assms(1) least_power_of_permutation(2) tutte_matrix.nonzero_perms_def tutte_matrix.p_is_permutation tutte_matrix_axioms by fastforce
  then have "hd (support p i) = i" 
    by (metis (no_types, lifting) Nil_is_map_conv assms(1) diff_zero funpow_0 hd_conv_nth least_power_of_permutation(2) length_greater_0_conv length_upt mem_Collect_eq tutte_matrix.nonzero_perms_def tutte_matrix.p_is_permutation tutte_matrix_axioms)
  then  have "hd ?l = f i" 
    by (metis (no_types, lifting) assms(1) diff_zero least_power_of_permutation(2) length_greater_0_conv length_map length_upt list.map_sel(1) mem_Collect_eq tutte_matrix.nonzero_perms_def tutte_matrix.p_is_permutation tutte_matrix_axioms)
  then have "f i \<in> set ?l" 
    by (metis (no_types, lifting) Nil_is_map_conv add.right_neutral assms(1) least_power_of_permutation(2) length_greater_0_conv length_upt less_diff_conv list.set_sel(1) mem_Collect_eq tutte_matrix.nonzero_perms_def tutte_matrix.p_is_permutation tutte_matrix_axioms)


  {
    fix x
    assume "x \<in> set (map f (support p i))" 
    then obtain j where "(map f (support p i))!j = x" 
      by (meson in_set_conv_nth)
    have "path (u_edges p) (map f (support p i))" 
      using assms(1) circuit_is_upath by blast
    obtain ys zs where "?l = ys @ x # zs"
      by (metis \<open>x \<in> set (map f (support p i))\<close> split_list)
    then have "(ys @ [x]) @ zs = ?l" by simp
    then have "path (u_edges p) (ys @ [x])" 
      by (metis \<open>path (u_edges p) (map f (support p i))\<close> path_pref)
    then have "hd (ys @ [x]) = f i" using `hd ?l = f i`
      by (metis Nil_is_append_conv \<open>(ys @ [x]) @ zs = map f (support p i)\<close> hd_append2 list.distinct(1))
    have "last (ys @ [x]) = x" 
      by simp 
    have "walk_betw (u_edges p) (f i) (ys @ [x]) x" 
      by (simp add: \<open>hd (ys @ [x]) = f i\<close> \<open>path (u_edges p) (ys @ [x])\<close> nonempty_path_walk_between)
    then have "x \<in> connected_component (u_edges p) (f i)" 
      by blast
    then show "x \<in> C" 
      by (meson \<open>walk_betw (u_edges p) (f i) (ys @ [x]) x\<close> assms(2) assms(3) in_con_compI)
  }
  fix x 
  assume "x \<in> C"

  show " x \<in> set ?l"
  proof(rule ccontr)
    assume "x \<notin> set ?l" 
    obtain xs where "walk_betw (u_edges p) (f i) xs x" 
      by (meson \<open>x \<in> C\<close> assms(2) assms(3) same_con_comp_walk)
    show False
    proof(cases "set  (edges_of_path xs) = {}")
      case True
      have "length (edges_of_path xs) = 0" 
        using True by blast
      then have "0 = length xs - 1" 
        by (simp add: edges_of_path_length)
      have "xs \<noteq> []" using `walk_betw (u_edges p) (f i) xs x` 
        by (meson walk_nonempty) 
      then have "length xs > 0" by fastforce
      then have "length xs  = 1" 
        using \<open>0 = length xs - 1\<close> by linarith
      then obtain a where "xs = [a]" 
        by (metis One_nat_def Suc_length_conv length_0_conv)
      then have "a = f i " using `walk_betw (u_edges p) (f i) xs x`
        unfolding walk_betw_def 
        by simp
      have "a = x" using `walk_betw (u_edges p) (f i) xs x` `xs = [a]`
        unfolding walk_betw_def 
        by auto
      have "f i = x" 
        using \<open>a = f i\<close> \<open>a = x\<close> by auto
      then show ?thesis 
        using \<open>f i \<in> set (map f (support p i))\<close> \<open>x \<notin> set (map f (support p i))\<close> by blast
    next
      case False

      have "set  (edges_of_path xs) \<noteq> {}" 
        using False by auto

      let ?P = "(\<lambda> y. y \<in> set ?l)" 
      let ?P' = "(\<lambda> y. y \<notin> set ?l)"
      show False
      proof(cases "set (filter ?P' xs) = set xs")
        case True
        then have "\<forall>y \<in> set xs. y \<notin> set ?l" 
          by (metis  filter_set member_filter)
        have "hd xs \<in> set xs" 
          by (metis False edges_of_path.simps(1) empty_set hd_in_set)
        then have "f i \<notin> set ?l" 
          by (metis \<open>\<forall>y\<in>set xs. y \<notin> set (map f (support p i))\<close> \<open>walk_betw (u_edges p) (f i) xs x\<close> walk_between_nonempty_path(3))
        then show False 
          using \<open>f i \<in> set (map f (support p i))\<close> by blast
      next
        case False 
        then show ?thesis 
        proof(cases "set (filter ?P' xs) = {}")
          case True
          have "last xs \<in> set xs" 
            by (metis False True empty_set last_in_set)
          then have "x \<in> set (filter ?P' xs)" 

            by (metis \<open>walk_betw (u_edges p) (f i) xs x\<close> \<open>x \<notin> set (map f (support p i))\<close> filter_set member_filter walk_between_nonempty_path(4))
          then have "x \<in> set ?l" 
            by (metis True empty_iff)
          then show ?thesis 
            using \<open>x \<notin> set (map f (support p i))\<close> by blast
        next
          case False
          case False
          obtain y where "y = hd (filter ?P' xs)" 
            by blast
          have "(filter ?P' xs) = y# (tl (filter ?P' xs))" 
            by (metis False \<open>y = hd (filter (\<lambda>y. y \<notin> set (map f (support p i))) xs)\<close> hd_Cons_tl list.set(1))
          then  obtain ys zs where "xs = ys @ y # zs \<and> (\<forall>u\<in>set ys. \<not> ?P' u) \<and> ?P' y"
            using Cons_eq_filterD 
            by (metis (no_types, lifting))
          then have "xs = (ys @ [y]) @ zs" by simp
          then have "path (u_edges p) (ys @ [y])" 
            by (metis \<open>walk_betw (u_edges p) (f i) xs x\<close> path_pref walk_between_nonempty_path(1))
          show False 
          proof(cases "ys = []")
            case True
            have "hd xs = y" 
              by (simp add: True \<open>xs = ys @ y # zs \<and> (\<forall>u\<in>set ys. \<not> u \<notin> set (map f (support p i))) \<and> y \<notin> set (map f (support p i))\<close>)
            then have "f i = y" 
              by (metis \<open>walk_betw (u_edges p) (f i) xs x\<close> walk_between_nonempty_path(3))

            then show ?thesis 
              using \<open>f i \<in> set (map f (support p i))\<close> \<open>xs = ys @ y # zs \<and> (\<forall>u\<in>set ys. \<not> u \<notin> set (map f (support p i))) \<and> y \<notin> set (map f (support p i))\<close> by blast

          next
            case False
            have "last ys \<in> set ?l" 
              using False \<open>xs = ys @ y # zs \<and> (\<forall>u\<in>set ys. \<not> u \<notin> set (map f (support p i))) \<and> y \<notin> set (map f (support p i))\<close> last_in_set by blast
            have "{last ys, y} \<in> set (edges_of_path xs)" 
              by (simp add: False \<open>xs = ys @ y # zs \<and> (\<forall>u\<in>set ys. \<not> u \<notin> set (map f (support p i))) \<and> y \<notin> set (map f (support p i))\<close> edges_of_path_append_3)
            then have "{last ys, y} \<in> u_edges p" 
              by (meson \<open>walk_betw (u_edges p) (f i) xs x\<close> path_ball_edges walk_between_nonempty_path(1))
            then obtain j where js:"{last ys, y} = {f j, f (p j)} \<and> j \<in> (UNIV:: 'n set)" unfolding u_edges_def 
              by blast
            then have "(last ys = f j \<and> y = f (p j)) \<or> (last ys = f (p j) \<and> y = f j)"
              by (meson doubleton_eq_iff)
            show False 
            proof(cases "(last ys = f j \<and> y = f (p j))")
              case True
              then have "f j \<in> set ?l" 
                using \<open>last ys \<in> set (map f (support p i))\<close> 
                by presburger
              obtain n where "f j = ?l!n \<and> n < length ?l" using in_set_conv_nth 
                by (metis True \<open>last ys \<in> set (map f (support p i))\<close>)
              have "?l!n = f ((support p i) ! n)" using nth_map 
                using \<open>f j = map f (support p i) ! n \<and> n < length (map f (support p i))\<close> by auto
              then have "f j = f ((support p i) ! n)"
                using `f j = ?l!n \<and> n < length ?l` `?l!n = f ((support p i) ! n)` 
                by presburger
              have "inj_on f (UNIV :: 'n set)" using bij 
                using bij_betw_imp_inj_on by auto
              then have "j = ((support p i) ! n)" using `f j = f ((support p i) ! n)` 
                by (meson inj_def)
              have "j = (p^^n) i" 
                using \<open>f j = map f (support p i) ! n \<and> n < length (map f (support p i))\<close> \<open>j = support p i ! n\<close> by auto
              then have "p j = p((p^^n) i)" 
                by blast
              then have "p j = (p^^(n+1)) i" 
                by simp
              show False
              proof(cases "n = (least_power p i) -1")
                case True
                then have "(p^^(n+1)) i = i" 
                  by (metis (no_types, lifting) One_nat_def Suc_pred \<open>last ys \<in> set (map f (support p i))\<close> add.right_neutral add_Suc_right assms(1) diff_zero empty_iff least_power_of_permutation(1) length_greater_0_conv length_map length_upt list.set(1) mem_Collect_eq tutte_matrix.nonzero_perms_def tutte_matrix.p_is_permutation tutte_matrix_axioms)
                then have "f (p j) = f i" 
                  using \<open>p j = (p ^^ (n + 1)) i\<close> by presburger
                then show ?thesis 
                  using \<open>f i \<in> set (map f (support p i))\<close> \<open>f j \<in> set (map f (support p i))\<close> \<open>last ys = f j \<and> y = f (p j) \<or> last ys = f (p j) \<and> y = f j\<close> \<open>xs = ys @ y # zs \<and> (\<forall>u\<in>set ys. \<not> u \<notin> set (map f (support p i))) \<and> y \<notin> set (map f (support p i))\<close> by presburger

              next
                case False
                then have "n+1 < (least_power p i)" 
                  by (metis Suc_eq_plus1 Suc_lessI \<open>f j = map f (support p i) ! n \<and> n < length (map f (support p i))\<close> diff_Suc_1 diff_zero length_map length_upt)
                have "p j = (support p i)!(n+1)" 
                  using \<open>n + 1 < least_power p i\<close> \<open>p j = (p ^^ (n + 1)) i\<close> by auto
                then have "f (p j) = ?l!(n+1)" 
                  using \<open>n + 1 < least_power p i\<close> by auto
                then have "y \<in> set ?l" 
                  by (metis True \<open>n + 1 < least_power p i\<close> diff_zero in_set_conv_nth length_map length_upt)
                then show ?thesis 
                  using \<open>xs = ys @ y # zs \<and> (\<forall>u\<in>set ys. \<not> u \<notin> set (map f (support p i))) \<and> y \<notin> set (map f (support p i))\<close> by blast
              qed
            next
              case False
              then have "(last ys = f (p j) \<and> y = f j)" 
                using \<open>last ys = f j \<and> y = f (p j) \<or> last ys = f (p j) \<and> y = f j\<close> by blast
              then have "f (p j) \<in> set ?l" 
                using \<open>last ys \<in> set (map f (support p i))\<close> 
                by presburger
              obtain n where "f (p j) = ?l!n \<and> n < length ?l" using in_set_conv_nth 
                by (metis \<open>f (p j) \<in> set (map f (support p i))\<close>)
              have "?l!n = f ((support p i) ! n)" using nth_map 
                using \<open>f (p j) = map f (support p i) ! n \<and> n < length (map f (support p i))\<close> by auto
              then have "f (p j) = f ((support p i) ! n)" 
                using \<open>f (p j) = map f (support p i) ! n \<and> n < length (map f (support p i))\<close> by presburger

              have "inj_on f (UNIV :: 'n set)" using bij 
                using bij_betw_imp_inj_on by auto
              then have "p j = ((support p i) ! n)" 
                by (simp add: \<open>f (p j) = f (support p i ! n)\<close> inj_def)
              have "p j = (p^^n) i" 
                using \<open>f (p j) = map f (support p i) ! n \<and> n < length (map f (support p i))\<close> \<open>p j = support p i ! n\<close> by force
              have "p permutes (UNIV :: 'n set)"
                using assms(1) nonzero_perms_def by auto

              then have "inj p" 
                using permutes_inj by blast
              show False
              proof(cases "n = 0")
                case True
                have "p j = i" 
                  by (simp add: True \<open>p j = (p ^^ n) i\<close>)

                have "p j = (p^^(least_power p i)) i" 
                  by (metis \<open>p j = i\<close> \<open>p permutes UNIV\<close> dvd_refl least_power_dvd tutte_matrix.p_is_permutation tutte_matrix_axioms)
                have "(least_power p i) > 0" 
                  by (simp add: \<open>p permutes UNIV\<close> least_power_of_permutation(2) p_is_permutation)

                then have "(p^^(least_power p i)) i = ((p^^(((least_power p i)-1)+1)) i)"
                  by fastforce
                then have "(p^^(((least_power p i)-1)+1)) = p \<circ> (p^^(((least_power p i)-1)))"
                  by simp
                then have "((p^^(((least_power p i)-1)+1)) i) = p (((p^^((least_power p i)-1)) i))"
                  by simp

                then have "(p^^(least_power p i)) i = p (((p^^((least_power p i)-1)) i))" 

                  using \<open>(p ^^ least_power p i) i = (p ^^ (least_power p i - 1 + 1)) i\<close> by presburger
                then have "p j = p (((p^^((least_power p i)-1)) i))" 
                  using \<open>p j = (p ^^ least_power p i) i\<close> by presburger
                then have "j = ((p^^((least_power p i)-1)) i)" using `inj p` 
                  by (meson inj_eq)
                then have "j = (support p i)!((least_power p i)-1)" 
                  using \<open>f (p j) = map f (support p i) ! n \<and> n < length (map f (support p i))\<close> by auto
                then have "f j = ?l!((least_power p i)-1)" 
                  by (simp add: \<open>0 < least_power p i\<close>)
                then have "y \<in> set ?l " 
                  by (simp add: \<open>0 < least_power p i\<close> \<open>last ys = f (p j) \<and> y = f j\<close>)
                then show False 
                  using \<open>\<And>thesis. (\<And>ys zs. xs = ys @ y # zs \<and> (\<forall>u\<in>set ys. \<not> u \<notin> set (map f (support p i))) \<and> y \<notin> set (map f (support p i)) \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> by blast
              next
                case False
                have "n > 0" 
                  using False by blast
                then have "n-1 \<ge> 0" 
                  by simp
                then have "(p^^n) i = (p \<circ> (p^^(n-1))) i" 
                  by (metis One_nat_def Suc_pred \<open>0 < n\<close> funpow.simps(2))
                then have "(p^^n) i = p ((p^^(n-1)) i)" 
                  by simp
                then have "p j = p ((p^^(n-1)) i)" 
                  using \<open>p j = (p ^^ n) i\<close> by presburger
                then have "j = (p^^(n-1)) i" using `inj p` 
                  by (meson inj_eq)
                then have "j = (support p i)!(n-1)" 
                  using \<open>f (p j) = map f (support p i) ! n \<and> n < length (map f (support p i))\<close> by auto
                then have "f j = ?l!(n-1)" 
                  by (metis \<open>f (p j) = map f (support p i) ! n \<and> n < length (map f (support p i))\<close> length_map less_imp_diff_less nth_map)

                then have "y \<in> set ?l " 
                  by (metis \<open>f (p j) = map f (support p i) ! n \<and> n < length (map f (support p i))\<close> \<open>last ys = f (p j) \<and> y = f j\<close> less_imp_diff_less nth_mem)

                then show False 
                  using \<open>xs = ys @ y # zs \<and> (\<forall>u\<in>set ys. \<not> u \<notin> set (map f (support p i))) \<and> y \<notin> set (map f (support p i))\<close> by blast
              qed
            qed
          qed
        qed
      qed
    qed
  qed 
qed

lemma fgdgfg:

  assumes "even n"
  shows "card {j. j \<in> {0..<n} \<and> even j} * 2 = n" using assms
proof(induct n  rule: less_induct)
  case (less x)
  then show ?case
  proof(cases "x = 0")
    case True
    then show ?thesis 
      by auto
  next
    case False
    have "x \<ge> 2"  using dvd_imp_le less.prems False odd_one 
      by blast
    then have "x - 2 \<ge> 0" by auto
    have "x-2 < x" 
      using False diff_less pos2 by blast
    have "even (x-2)" 
      by (simp add: less.prems)
    then have "card {j \<in> {0..<x-2}. even j} * 2 = x - 2" 
      using less.hyps[of "x-2"] 
      using \<open>x - 2 < x\<close> by blast

    have "{j \<in> {0..<x}. even j} = {j \<in> {0..<x-2}. even j} \<union> {x-2}" 
    proof(safe)
      {   fix xa
      assume "xa \<notin> {}"
          "xa \<noteq> x - 2"
          "xa \<in> {0..<x}" "even xa" 
      then have "xa \<noteq> x -1 "
        by (metis One_nat_def Suc_pred \<open>0 \<le> x - 2\<close> \<open>x - 2 < x\<close> even_Suc le_less_trans less.prems)

      then show "xa \<in> {0..<x - 2}" 
        by (smt (verit) One_nat_def Suc_leI Suc_pred \<open>xa \<in> {0..<x}\<close> \<open>xa \<noteq> x - 2\<close> add.left_neutral add_2_eq_Suc' atLeastLessThan_iff diff_Suc_Suc le_less_trans linorder_neqE_nat not_le)
    }
    { fix xa
    show " xa \<in> {0..<x - 2} \<Longrightarrow> even xa \<Longrightarrow> xa \<in> {0..<x}" 
      by (meson \<open>x - 2 < x\<close> atLeastLessThan_iff less_trans)
  }
  {
    fix xa
    show "x - 2 \<in> {0..<x}" 
      by (meson \<open>0 \<le> x - 2\<close> \<open>x - 2 < x\<close> atLeastLessThan_iff)
  }
  fix xa
  show "even (x - 2)" 
    using \<open>even (x - 2)\<close> by blast
qed

  have "card {j \<in> {0..<x}. even j} = card ({j \<in> {0..<x-2}. even j} \<union> {x-2})"
    
    using \<open>{j \<in> {0..<x}. even j} = {j \<in> {0..<x - 2}. even j} \<union> {x - 2}\<close> by presburger

  have "x-2 \<notin> {j \<in> {0..<x-2}. even j}" 
    by force
  then have "{j \<in> {0..<x-2}. even j} \<inter> {x -2} = {}" 
    by blast
  have "finite  {0..<x-2}" 
    by blast
  then have "finite {j \<in> {0..<x-2}. even j}"  by auto
  have "finite {x-2}" by auto
  then have "card ({j \<in> {0..<x-2}. even j} \<union> {x-2}) =
        card {j \<in> {0..<x-2}. even j} + card {x-2}" 
    using \<open>finite {j \<in> {0..<x - 2}. even j}\<close> \<open>{j \<in> {0..<x - 2}. even j} \<inter> {x - 2} = {}\<close> card_Un_disjoint by blast
  then have "card {j \<in> {0..<x}. even j} = card {j \<in> {0..<x-2}. even j} + card {x-2}"
    
    using \<open>card {j \<in> {0..<x}. even j} = card ({j \<in> {0..<x - 2}. even j} \<union> {x - 2})\<close> by presburger
  then have "2 * card {j \<in> {0..<x}. even j} = 2 * (card {j \<in> {0..<x-2}. even j} + card {x-2})"
    by presburger
  then have "2 * card {j \<in> {0..<x}. even j} = 2 * card {j \<in> {0..<x-2}. even j} + 2 *  card {x-2}"
    
    by simp
  then have "2 * card {j \<in> {0..<x}. even j} = (x - 2) + 2 *  card {x-2}" 
    using \<open>card {j \<in> {0..<x - 2}. even j} * 2 = x - 2\<close> by presburger
  have "card {x-2} = 1" by auto
  have "2 * card {j \<in> {0..<x}. even j} = (x - 2) + 2 * 1" 
    using \<open>2 * card {j \<in> {0..<x}. even j} = x - 2 + 2 * card {x - 2}\<close> \<open>card {x - 2} = 1\<close> by presburger
  then have "2 * card {j \<in> {0..<x}. even j} = x" 
    using \<open>2 \<le> x\<close> by linarith
  then show ?thesis 
    by presburger
qed
qed

lemma perm_support_distinct:
  assumes "p permutes (UNIV :: 'n set)"
  shows "distinct (support p i)" 
  by (simp add: assms cycle_of_permutation p_is_permutation)

lemma cycle_vert_is_distict:
  assumes "p permutes (UNIV :: 'n set)"
  shows "distinct (map f (support p i))"
proof -
  have "distinct (support p i)"   using perm_support_distinct assms 
    by simp
  have "inj_on f (set (support p i))" 
    by (metis bij bij_betw_imp_inj_on inj_eq inj_onI)
  then show ?thesis using distinct_map 
    using \<open>cycle (support p i)\<close> by blast
qed

lemma p_in_same_cycle:
  assumes "p permutes (UNIV :: 'n set)"
  assumes "a \<in> set (support p i)"
  shows "p a \<in> set (support p i)" 
  by (metis (no_types, lifting) assms(1) assms(2) cycle_is_surj cycle_restrict image_iff 
map_eq_conv p_is_permutation perm_support_distinct)

lemma nths_in_result:
  assumes "i \<in> I"
  assumes "i < length xs"
  shows "xs!i \<in> set (nths xs I)" 
  using assms(1) assms(2) set_nths by fastforce

lemma nths_obtain_index:
  assumes "a \<in>  set (nths xs I)"
  obtains i where "a = xs!i" "i \<in> I" "i < length xs"
 using assms(1)  set_nths
  by (smt (verit, ccfv_threshold) mem_Collect_eq)

lemma next_elem_by_p:
  assumes "p permutes (UNIV :: 'n set)"
  assumes "0 < n" 
  assumes "n < length (support p i)" 
  shows "support p i ! n = p ((support p i)!(n-1))" 
proof -
  have "support p i ! n = (p^^n) i" 
    using assms(3) by fastforce
  have "(support p i)!(n-1) = (p^^(n-1)) i" 
    using assms(3) by fastforce
  have "(p^^n) i = (p \<circ> (p^^(n-1))) i" 
    by (metis Suc_diff_1 assms(2) funpow.simps(2))
  then have "(p^^n) i = p ((p^^(n-1)) i)" 
    by simp
  then show ?thesis 
    using \<open>support p i ! (n - 1) = (p ^^ (n - 1)) i\<close> \<open>support p i ! n = (p ^^ n) i\<close> by presburger
qed

lemma next_elem_by_p':
  assumes "p permutes (UNIV :: 'n set)"
  assumes "n < length (support p i) - 1" 
  shows "support p i ! (n+1) = p ((support p i)!n)"
proof -
  have "0 < n+1"   using zero_less_one by blast
  have "n + 1< length (support p i)" using assms(2) by linarith
  then show ?thesis
  using next_elem_by_p[of p "n+1"] assms 
  by (metis (no_types, lifting) \<open>0 < n + 1\<close> add_diff_cancel_right'  length_map length_upt)
qed

lemma perm_verts_in_all_verts:
  assumes "p permutes (UNIV :: 'n set)"
  shows "Vs (u_edges p) \<subseteq> Vs E" 
proof
  fix x
  assume "x \<in> Vs (u_edges p)" 
  then obtain e where "e \<in> (u_edges p) \<and> x \<in> e" 
    by (meson vs_member_elim)
  then obtain i where "i \<in> (UNIV :: 'n set) \<and> {f i, f (p i)} = e" 
    using u_edges_def by auto
  then show "x \<in> Vs E" 
  proof(cases "x = f i")
case True
  then show ?thesis 
    by (metis \<open>i \<in> UNIV \<and> {f i, f (p i)} = e\<close> bij bij_betw_apply)
next
  case False
  then have "x = f (p i)" 
    using \<open>e \<in> u_edges p \<and> x \<in> e\<close> \<open>i \<in> UNIV \<and> {f i, f (p i)} = e\<close> by fastforce
  then show ?thesis 
    by (metis \<open>i \<in> UNIV \<and> {f i, f (p i)} = e\<close> assms bij bij_betw_iff_bijections permutes_imp_bij)
qed
qed


lemma even_circuits_has_perfect_matching:
  assumes "p \<in> nonzero_perms X"
  assumes "\<forall>C \<in> connected_components (u_edges p). even (card C) "
  shows "\<exists> M. perfect_matching (u_edges p) M"
proof -
  have "p permutes (UNIV :: 'n set)" using assms(1) 
    using tutte_matrix.nonzero_perms_def tutte_matrix_axioms by auto
  have "finite (u_edges p)" 
    by (simp add: u_edges_finite)
  have "\<forall> C \<in> connected_components (u_edges p). 
        \<exists> M'. perfect_matching (component_edges (u_edges p) C) M'"
  proof
    fix C
    assume "C \<in> connected_components (u_edges p)"
    then have "even (card C)" using assms(2) by auto
    have "C \<subseteq> Vs (u_edges p)" 
      by (simp add: \<open>C \<in> connected_components (u_edges p)\<close> connected_component_subs_Vs)

    obtain x where "x \<in> C" 
      by (metis \<open>C \<in> connected_components (u_edges p)\<close> connected_comp_nempty ex_in_conv)
    then have "x \<in> Vs (u_edges p)" 
      by (meson \<open>C \<in> connected_components (u_edges p)\<close> connected_comp_verts_in_verts)

    then obtain i where "f i = x" 
      by (meson `p permutes (UNIV :: 'n set)` perm_verts_in_all_verts subsetD vertices_in_range)
    have "set (map f (support p i)) = C" 
      using \<open>C \<in> connected_components (u_edges p)\<close> \<open>f i = x\<close> \<open>x \<in> C\<close> `p permutes (UNIV :: 'n set)` support_is_connected_component by fastforce
    let ?l = "map f (support p i)"
    let ?even_i = "{j. j \<in> {0..<length (support p i)} \<and> even j}"
    have "length (support p i) = length (map f (support p i))" 
      by auto
    have "card (set (map f (support p i))) = length (map f (support p i))" 
      using List.distinct_card 
  by (metis (no_types, lifting)   assms(1) cycle_vert_is_distict length_map mem_Collect_eq  tutte_matrix.nonzero_perms_def tutte_matrix_axioms)
  then have "even (length (map f (support p i)))" 
    by (metis \<open>even (card C)\<close> \<open>set (map f (support p i)) = C\<close>)
  then have "even (length (support p i))" 
    by simp

  let ?start_vert = "nths (support p i) ?even_i"
  let ?m_edges = "{{f j, f (p j)}| j. j \<in> set ?start_vert}"


  have " set ?start_vert \<subseteq> (UNIV :: 'n set)" 
    by blast
  then have "?m_edges \<subseteq> u_edges p" 
    using tutte_matrix.u_edges_def tutte_matrix_axioms by fastforce

  have "Vs ?m_edges = set (map f (support p i))"
  proof(safe)
    {  fix x
    assume "x \<in> Vs ?m_edges"
    then obtain a where "x \<in> {f a, f (p a)} \<and> a \<in> set ?start_vert" 
      by (smt (z3) mem_Collect_eq vs_member_elim)
    then have "a \<in> set (support p i)" 
      by (meson notin_set_nthsI)
    then have "p a \<in> set (support p i)"
      using \<open>p permutes UNIV\<close> p_in_same_cycle by presburger
    then show "x \<in> set (map f (support p i))" 
      using \<open>a \<in> set (support p i)\<close> \<open>x \<in> {f a, f (p a)} \<and> a \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})\<close> by auto
  }
  fix x
  assume "x \<in> set (map f (support p i))" 
  then obtain a where "x = f a" 
    by auto
  then have "a \<in> set (support p i)"  
    by (smt (verit) UNIV_I \<open>length (support p i) = length (map f (support p i))\<close> \<open>x \<in> set (map f (support p i))\<close> bij bij_betw_iff_bijections in_set_conv_nth nth_map)
  then obtain n where "a = (support p i)!n \<and> n < least_power p i" 
    by (metis diff_zero in_set_conv_nth length_map length_upt)
  show "x \<in> Vs ?m_edges"
  proof(cases "even n")
    case True
    then have "n \<in>  {j \<in> {0..<length (support p i)}. even j}" 
      by (simp add: \<open>a = support p i ! n \<and> n < least_power p i\<close>)
    then have "a \<in> set (nths (support p i)
                        {j \<in> {0..<length (support p i)}. even j})" 
      by (metis (mono_tags, lifting) \<open>a = support p i ! n \<and> n < least_power p i\<close> diff_zero length_map length_upt nths_in_result)
    then have "{f a, f (p a)} \<in> ?m_edges" 
      by blast
    then show ?thesis 
      using \<open>x = f a\<close> by blast
  next
    case False
    have "n > 0" using False  
      using odd_pos by auto
    then have "even (n-1)" 
      by (simp add: False)
     then have "n - 1 \<in>  {j \<in> {0..<length (support p i)}. even j}" 
       by (simp add: \<open>a = support p i ! n \<and> n < least_power p i\<close> less_imp_diff_less)
     have "(support p i)!(n-1)\<in> set (nths (support p i)
                        {j \<in> {0..<length (support p i)}. even j})" 
       
       by (metis (no_types, lifting) \<open>a = support p i ! n \<and> n < least_power p i\<close> \<open>n - 1 \<in> {j \<in> {0..<length (support p i)}. even j}\<close> diff_zero length_map length_upt less_imp_diff_less nths_in_result)
     have "support p i ! n = p ((support p i)!(n-1))"  
       using \<open>0 < n\<close> \<open>a = support p i ! n \<and> n < least_power p i\<close> \<open>p permutes UNIV\<close> length_upt map_eq_conv next_elem_by_p by force
     have "{f ((support p i)!(n-1)), f (p ((support p i)!(n-1)))} \<in> ?m_edges"  
       using \<open>support p i ! (n - 1) \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})\<close> by blast
     then have "f (p ((support p i)!(n-1))) = x" 
       using \<open>a = support p i ! n \<and> n < least_power p i\<close> \<open>support p i ! n = p (support p i ! (n - 1))\<close> \<open>x = f a\<close> by presburger

    then show ?thesis 
      using \<open>{f (support p i ! (n - 1)), f (p (support p i ! (n - 1)))} \<in> {{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})}\<close> insert_commute by auto

  qed
qed
  then have "Vs ?m_edges = C" 
    using \<open>set (map f (support p i)) = C\<close> by fastforce
  have "matching ?m_edges" unfolding matching_def
  proof
    fix e1 
    assume "e1 \<in> ?m_edges"

    show "\<forall>e2 \<in> ?m_edges. e1 \<noteq> e2 \<longrightarrow>e1 \<inter> e2 = {}"
    proof
      fix e2
      assume "e2 \<in> ?m_edges"
      show "e1 \<noteq> e2 \<longrightarrow>e1 \<inter> e2 = {}"
      proof
        assume "e1 \<noteq> e2"
        show "e1 \<inter> e2 = {}"
        proof(rule ccontr)
          assume " e1 \<inter> e2 \<noteq> {}" 
          then obtain t where "t \<in> e1 \<inter> e2" by auto
          obtain u v where "e1 = {u, t} \<and> e2 = {t, v}" 
            by (smt (z3) IntD1 IntD2 \<open>e1 \<in> {{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})}\<close> \<open>e2 \<in> {{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})}\<close> \<open>t \<in> e1 \<inter> e2\<close> empty_iff insert_commute insert_iff mem_Collect_eq)
          then have "u \<noteq> v" 
            using \<open>e1 \<noteq> e2\<close> by fastforce
          then obtain a where a_elem:"{f a, f (p a)} = {u, t}  \<and> a \<in> set ?start_vert" 
            using \<open>e1 = {u, t} \<and> e2 = {t, v}\<close> \<open>e1 \<in> {{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})}\<close> by force
          obtain b where b_elem:"{f b, f (p b)} = {v, t}  \<and> b \<in> set ?start_vert" 
            by (smt (z3) \<open>e1 = {u, t} \<and> e2 = {t, v}\<close> \<open>e2 \<in> {{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})}\<close> insert_commute mem_Collect_eq)

            have "even (length (support p i))" 
              using \<open>even (length (support p i))\<close> by blast
           
             have "a \<in> set (support p i)"  
              using \<open>{f a, f (p a)} = {u, t} \<and> a \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})\<close> notin_set_nthsI by fastforce

            then obtain an where "a = (support p i)!an  \<and>  an \<in> {j \<in> {0..<length (support p i)}. even j}" 
              using a_elem nths_obtain_index[of a "(support p i)" "{j \<in> {0..<length (support p i)}. even j}"]
              by force
            then have "even an" 
              by blast
 then have "an < (length (support p i)) - 1" using `even (length (support p i))` 
   using \<open>a = support p i ! an \<and> an \<in> {j \<in> {0..<length (support p i)}. even j}\<close> by fastforce
          have "b \<in> set (support p i)"  
            using b_elem notin_set_nthsI by fastforce
          then obtain bn where "b = (support p i)!bn  \<and>  bn \<in> {j \<in> {0..<length (support p i)}. even j}"
            using b_elem  nths_obtain_index by force
 then have "bn < (length (support p i)) - 1" using `even (length (support p i))` by fastforce
  have "even bn" 
    using \<open>b = support p i ! bn \<and> bn \<in> {j \<in> {0..<length (support p i)}. even j}\<close> by blast
          
          show False
          proof(cases "f a = u \<and> f (p a) = t")
            case True

            then show ?thesis
            proof(cases "f b = v \<and> f (p b) = t")
              case True
              have "f (p a) = f (p b)" using `f a = u \<and> f (p a) = t` True 
                by simp
              then have "p a = p b" 
                by (metis UNIV_I bij bij_betw_iff_bijections)
              then have "a = b" 
                by (smt (verit, ccfv_SIG) \<open>p permutes UNIV\<close> \<open>set (nths (support p i) {j \<in> {0..<length (support p i)}. even j}) \<subseteq> UNIV\<close> \<open>{f a, f (p a)} = {u, t} \<and> a \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})\<close> \<open>{f b, f (p b)} = {v, t} \<and> b \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})\<close> bij_betw_iff_bijections permutes_imp_bij subsetD)
              then have "f a = f b" by auto
              then show ?thesis 
                using True \<open>a = b\<close> \<open>e1 = {u, t} \<and> e2 = {t, v}\<close> \<open>e1 \<noteq> e2\<close> \<open>{f a, f (p a)} = {u, t} \<and> a \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})\<close> by blast
            next
              case False
              have "f b = t \<and> f (p b) = v" 
                by (meson False \<open>{f b, f (p b)} = {v, t} \<and> b \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})\<close> doubleton_eq_iff)

              have "p ((support p i)!an) = (support p i)!(an+1)" 
                using  next_elem_by_p'[of p an i] 
                using \<open>an < length (support p i) - 1\<close> \<open>p permutes UNIV\<close> by presburger
              then have "p a = (support p i)!(an+1)" 
                using \<open>a = support p i ! an \<and> an \<in> {j \<in> {0..<length (support p i)}. even j}\<close> by fastforce
              then have "(support p i)!(an+1) = (support p i)!(bn)" 
                by (metis (no_types, lifting) True UNIV_I \<open>b = support p i ! bn \<and> bn \<in> {j \<in> {0..<length (support p i)}. even j}\<close> \<open>f b = t \<and> f (p b) = v\<close> bij bij_betw_iff_bijections)

              have "an +1 \<noteq> bn" 
                using \<open>even an\<close> \<open>even bn\<close> even_add odd_one by blast
              then have "\<not> distinct (support p i)" 
                by (metis (no_types, lifting) \<open>an < length (support p i) - 1\<close> \<open>bn < length (support p i) - 1\<close> \<open>support p i ! (an + 1) = support p i ! bn\<close> add_diff_cancel_right' less_diff_conv less_imp_diff_less nth_eq_iff_index_eq)

              then show ?thesis 
                using \<open>card (set (map f (support p i))) = length (map f (support p i))\<close> card_distinct distinct_map by blast
            qed
          next
            case False
            have "f a =  t \<and> f (p a) = u" 
              by (meson False a_elem doubleton_eq_iff) 
              have "p ((support p i)!bn) = (support p i)!(bn+1)" 
                using  next_elem_by_p'[of p bn i] 
                using \<open>bn < length (support p i) - 1\<close> \<open>p permutes UNIV\<close> by presburger
              then have "p b = (support p i)!(bn+1)" 
                using \<open>b = support p i ! bn \<and> bn \<in> {j \<in> {0..<length (support p i)}. even j}\<close> by fastforce

              show ?thesis 
 proof(cases "f b = v \<and> f (p b) = t")
   case True
   have "f a = f (p b)" 
     by (simp add: True \<open>f a = t \<and> f (p a) = u\<close>)
   then have "a = p b" 
     by (metis UNIV_I bij bij_betw_iff_bijections)
   then have "(support p i)!(bn+1) = (support p i)!(an)" 
     using \<open>a = support p i ! an \<and> an \<in> {j \<in> {0..<length (support p i)}. even j}\<close> \<open>p b = support p i ! (bn + 1)\<close> by presburger
   have "bn +1 \<noteq> an" 
     using \<open>even an\<close> \<open>even bn\<close> even_add odd_one by blast
  then have "\<not> distinct (support p i)" 
                by (metis (no_types, lifting) \<open>an < length (support p i) - 1\<close> \<open>bn < length (support p i) - 1\<close> \<open>support p i ! (bn + 1) = support p i ! an\<close> add_diff_cancel_right' less_diff_conv less_imp_diff_less nth_eq_iff_index_eq)

              then show ?thesis 
                using \<open>card (set (map f (support p i))) = length (map f (support p i))\<close> card_distinct distinct_map by blast

 next
   case False
   have "f b = t \<and> f (p b) = v"  
     by (meson False b_elem doubleton_eq_iff)
   then have "f b = f a" 
     using \<open>f a = t \<and> f (p a) = u\<close> by auto
   then have "a = b" 
     by (metis UNIV_I bij bij_betw_iff_bijections)
   then have "u = v" 
     using \<open>f a = t \<and> f (p a) = u\<close> \<open>f b = t \<and> f (p b) = v\<close> by blast
   then show ?thesis 
     using \<open>u \<noteq> v\<close> by auto
 qed
qed
qed
qed
qed
qed
  have "?m_edges \<subseteq> (component_edges (u_edges p) C)"
  proof
    fix e
    assume "e \<in> ?m_edges" 
    have "e \<in> (u_edges p)" 
      using \<open>e \<in> {{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})}\<close> \<open>{{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})} \<subseteq> u_edges p\<close> by blast
    have "e \<subseteq> C" 
      using \<open>Vs {{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})} = C\<close> \<open>e \<in> {{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})}\<close> vs_member_intro by blast
    then show "e \<in> (component_edges (u_edges p) C)" unfolding component_edges_def
      
      using \<open>e \<in> u_edges p\<close> assms(1) tutte_matrix.u_edges_is_graph tutte_matrix_axioms by fastforce
  qed
  have "Vs (component_edges (u_edges p) C) = C" 
    using vs_connected_component[of "u_edges p" C]
    `C \<in> connected_components (u_edges p)` 
    by (meson assms(1) tutte_matrix.u_edges_is_graph tutte_matrix_axioms)

  have "graph_invar (component_edges (u_edges p) C)" 
    by (metis (no_types, lifting) Berge.component_edges_subset \<open>C \<subseteq> Vs (u_edges p)\<close> \<open>Vs (component_edges (u_edges p) C) = C\<close> assms(1) finite_subset insert_subset mk_disjoint_insert tutte_matrix.u_edges_is_graph tutte_matrix_axioms)
  then  have " perfect_matching (component_edges (u_edges p) C) ?m_edges"
    unfolding perfect_matching_def 
    using \<open>Vs (component_edges (u_edges p) C) = C\<close> \<open>Vs {{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})} = C\<close> \<open>matching {{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})}\<close> \<open>{{f j, f (p j)} |j. j \<in> set (nths (support p i) {j \<in> {0..<length (support p i)}. even j})} \<subseteq> component_edges (u_edges p) C\<close> 
    by auto

    then show "\<exists> M'. perfect_matching (component_edges (u_edges p) C) M'" 
      by blast
  qed

  then  show "\<exists> M. perfect_matching (u_edges p) M" using 
perfect_matching_union_components[of "u_edges p"] u_edges_is_graph assms(1)
    by blast
qed

definition least_odd :: "('n \<Rightarrow> 'n) \<Rightarrow> 'a"
  where "least_odd p = (LEAST a. odd (least_power p ((inv f) a)))"


definition rev_p :: "('n \<Rightarrow> 'n) \<Rightarrow> ('n \<Rightarrow> 'n)" 
  where "rev_p p = (\<lambda> i. if i \<in> set (support p ((inv f) (least_odd p))) then 
        (inv p) i else p i)" 

lemma least_power_same_in_support:
   assumes "permutation p"
   assumes "a \<in> set (support p i)"
   shows "(p^^least_power p i) a = a" 
proof -
  obtain n where "(p^^n) i = a \<and> n < least_power p i" using assms 
    by fastforce
  have "(p^^n) i = ((p^^n) \<circ> (p^^least_power p i)) i" 
    by (simp add: assms(1) least_power_of_permutation(1))
  then have "((p^^least_power p i)\<circ>(p^^n)) i = (p^^n) i" 
    by (metis add.commute funpow_add)
  then have "(p^^least_power p i) ((p^^n) i) = (p^^n) i" 
    by simp
  show ?thesis 
    using \<open>(p ^^ least_power p i) ((p ^^ n) i) = (p ^^ n) i\<close> \<open>(p ^^ n) i = a \<and> n < least_power p i\<close> by auto
qed

lemma inv_in_support:
  assumes "permutation p"
  assumes "a \<in> set (support p i)"
  shows "(inv p) a \<in> set (support p i)" 
proof  -
    have "least_power p i > 0" 
      by (simp add: assms(1) least_power_of_permutation(2))
  have "p ((inv p) a) = a" 
    by (meson assms(1) bij_inv_eq_iff permutation_bijective)
  have "(p \<circ> (p^^((least_power p i)-1))) a = a" using least_power_same_in_support
assms 
    by (metis One_nat_def Suc_pred \<open>0 < least_power p i\<close> funpow.simps(2))
  then have "p ((p^^((least_power p i)-1)) a) = a" by simp
  then have "p ((inv p) a) = p ((p^^((least_power p i)-1)) a)" 
    using \<open>p (inv p a) = a\<close> by presburger
  then have "(inv p) a = (p^^((least_power p i)-1)) a" 
    by (metis assms(1) bij_inv_eq_iff permutation_bijective)
  then show ?thesis 
    by (smt (z3) One_nat_def Suc_pred \<open>0 < least_power p i\<close> assms(1) assms(2) comp_def cycle_is_surj cycle_of_permutation cycle_restrict funpow.simps(2) funpow_swap1 image_iff least_power_same_in_support map_eq_conv)
qed



lemma mod_least_power_same:
  assumes "permutation p" 
  assumes "(p ^^ n) a = b"
  shows "(p^^(n mod (least_power p a))) a = b"
proof (cases "n = 0", simp)
  {
  let ?lpow = "least_power p" 
  assume "n \<noteq> 0" then have "n > 0" by simp
  have  "(p ^^ (?lpow a)) a = a" 
  using assms  
  by (meson least_power_of_permutation(1))
  hence aux_lemma: "(p ^^ ((?lpow a) * k)) a = a" for k :: nat
    by (induct k) (simp_all add: funpow_add)

  have "(p ^^ (n mod ?lpow a)) ((p ^^ (n - (n mod ?lpow a))) a) = (p ^^ n) a"
    by (metis add_diff_inverse_nat funpow_add mod_less_eq_dividend not_less o_apply)
  with \<open>(p ^^ n) a = b\<close> 
  show "(p ^^ (n mod ?lpow a)) a = b"
    using aux_lemma by (simp add: minus_mod_eq_mult_div) 
}
  show "n = 0 \<Longrightarrow> a = b" 
    using assms(2) by auto
qed

lemma elemnets_in_support_expo:
  fixes n :: "nat"
  assumes "permutation p" 
  assumes "x \<in> set (support p i)"
  assumes "y = (p^^n) x"
  shows "y \<in> set (support p i)" 
proof -
  let ?len = "least_power p i"
  obtain k where "(p^^k) i = x \<and> k < least_power p i" using assms 
    by fastforce
  have "((p^^n)\<circ>(p^^k)) i = y" 
    by (simp add: \<open>(p ^^ k) i = x \<and> k < least_power p i\<close> assms(3)) 
  then have "(p^^(n+k)) i = y" 
    by (simp add: funpow_add) 
  then have "(p^^((n+k) mod ?len)) i = y" 
    by (simp add: assms(1) mod_least_power_same)
  have "((n+k) mod ?len) < ?len" 
    by (meson assms(1) least_power_of_permutation(2) mod_less_divisor)
  then have "(support p i)!((n+k) mod ?len) = y" 
    by (simp add: \<open>(p ^^ ((n + k) mod least_power p i)) i = y\<close>)
  then show ?thesis  
    using \<open>(n + k) mod least_power p i < least_power p i\<close> by force
qed

lemma elemnets_in_support_expo':
  fixes n :: "nat"
  assumes "permutation p" 
  assumes "x \<in> set (support p i)"
  assumes "x = (p^^n) y"
  shows "y \<in> set (support p i)"
proof -
  have "permutation (p^^n)" 
    by (simp add: assms(1) permutation_funpow)
  let ?len = "(least_power p i)" 
    obtain k where "(p^^k) i = x \<and> k < least_power p i" using assms 
      by fastforce
    have "(p^^k) i = (p^^n) y" 
      by (simp add: \<open>(p ^^ k) i = x \<and> k < least_power p i\<close> assms(3))
    have "permutation (p^^k)" 
      by (simp add: assms(1) permutation_funpow)
  let ?dvd = "n div ?len" 
  have "n = ?dvd * ?len + (n mod ?len)" 
    by presburger
  have "permutation (p^^(?dvd * ?len))" 
    using assms(1) permutation_funpow by blast
   have "(p^^k) i = ((p^^(?dvd * ?len))\<circ> p^^(n mod ?len)) y" 
     by (metis \<open>(p ^^ k) i = (p ^^ n) y\<close> div_mult_mod_eq funpow_add)
   have "i = (p^^(?dvd * ?len)) i" 
     by (metis add.right_neutral assms(1) dvd_eq_mod_eq_0 least_power_dvd least_power_of_permutation(2) mod_less mod_mult_self3)
   then have "(p^^k) i = ((p^^k) \<circ> (p^^(?dvd * ?len))) i" 
     by auto
   then have "(p^^k) i = (p^^(?dvd * ?len)) ((p^^k) i)" 
     by (metis add.commute comp_apply funpow_add)
   have "(p^^(?dvd * ?len)) ((p^^k) i) = (p^^(?dvd * ?len)) (( p^^(n mod ?len)) y )" 
     
     by (metis \<open>(p ^^ k) i = (p ^^ (n div least_power p i * least_power p i) \<circ> p ^^ (n mod least_power p i)) y\<close> \<open>(p ^^ k) i = (p ^^ (n div least_power p i * least_power p i)) ((p ^^ k) i)\<close> comp_apply)
   then have "(p ^^ k) i = ( p^^(n mod ?len)) y" 
     using `permutation (p^^(?dvd * ?len))` permutation_permutes permutes_def  
     by (smt (verit))
  have "permutation (p^^(n mod ?len))" 
    using assms(1) permutation_funpow by auto
   show ?thesis
  proof(cases "k \<ge> (n mod ?len)")
    case True

    have "(p^^k) i = ((p^^(n mod ?len)) \<circ> (((p^^(k-(n mod ?len)))))) i" 
      by (metis True add_diff_inverse_nat funpow_add leD)
    then have "(p^^(n mod ?len)) y = ((p^^(n mod ?len)) \<circ> (((p^^(k-(n mod ?len)))))) i" 
      using \<open>(p ^^ k) i = (p ^^ (n mod least_power p i)) y\<close> by presburger
    then have "(p^^(n mod ?len)) y = (p^^(n mod ?len)) ((p^^(k-(n mod ?len))) i)" 
      by simp
    then have "y = ((p^^(k-(n mod ?len))) i)" using `permutation (p^^(n mod ?len))`
 permutation_permutes permutes_def  
     by (smt (verit))
    then have "y = support p i !(k-(n mod ?len))" 
      by (simp add: \<open>(p ^^ k) i = x \<and> k < least_power p i\<close> less_imp_diff_less) 
  then show ?thesis 
    by (simp add: \<open>(p ^^ k) i = x \<and> k < least_power p i\<close> less_imp_diff_less)
next
  case False
  have "k + ?len \<ge> (n mod ?len)" 
    by (meson assms(1) least_power_of_permutation(2) mod_le_divisor trans_le_add2)
   have "(p^^(n mod ?len)) y = ((p^^k) \<circ> (((p^^((n mod ?len)-k))))) y" 
   
       by (metis False add_diff_inverse_nat funpow_add less_imp_le)
    then have "(p^^k) i = ((p^^k) \<circ> (((p^^((n mod ?len)-k))))) y" 
      using \<open>(p ^^ k) i = (p ^^ (n mod ?len)) y\<close> 
      by presburger
    then have "(p^^k) i = (p^^k) ((p^^((n mod ?len)-k)) y)" 
      by simp
    then have "i = ((p^^((n mod ?len)-k)) y)" using `permutation (p^^k)`  
      by (metis permutation_permutes permutes_def)


    have "(p^^k) ((p^^?len) i) = (p ^^ (n mod ?len)) y" 
      by (simp add: \<open>(p ^^ k) i = (p ^^ (n mod ?len)) y\<close> assms(1) least_power_of_permutation(1))
    then have "(p^^(k + ?len)) i = (p ^^ (n mod ?len)) y" 
      by (simp add: funpow_add)
    then have "((p ^^ (n mod ?len)) \<circ> (p^^(k + ?len - (n mod ?len)))) i = (p^^(k + ?len)) i"
      
      by (metis \<open>n mod least_power p i \<le> k + least_power p i\<close> funpow_add ordered_cancel_comm_monoid_diff_class.add_diff_inverse)
    then have "(p ^^ (n mod ?len)) ((p^^(k + ?len - (n mod ?len))) i) = (p ^^ (n mod ?len)) y"
      
      by (simp add: \<open>(p ^^ (k + least_power p i)) i = (p ^^ (n mod least_power p i)) y\<close>)
    then have "(p^^(k + ?len - (n mod ?len))) i =  y" 
      using `permutation (p^^(n mod ?len))`   
      by (smt (verit, ccfv_threshold) permutation_permutes permutes_def)
    then have "support p i!(k + ?len - (n mod ?len)) = y" 
      by (metis False \<open>n mod least_power p i \<le> k + least_power p i\<close> diff_self_eq_0 diff_zero le_add_diff_inverse2 less_add_eq_less less_or_eq_imp_le not_le nth_map_upt)

  then show ?thesis 
    using False \<open>n mod least_power p i \<le> k + least_power p i\<close> by force
qed
qed

lemma inv_notin_support:
  assumes "permutation p"
  assumes "a \<notin> set (support p i)"
  shows "(inv p) a \<notin> set (support p i)"
proof(rule ccontr)
  assume "\<not> (inv p) a \<notin> set (support p i)"
  then have "(inv p) a \<in> set (support p i)" by auto
    then have "p ((inv p) a) = a" 
      by (meson assms(1) bij_inv_eq_iff permutation_bijective)
    have "p ((inv p) a) \<in> set (support p i)" 
      by (metis (no_types, lifting) \<open>inv p a \<in> set (support p i)\<close> assms(1) cycle_is_surj cycle_of_permutation cycle_restrict image_iff map_eq_conv)
    then show False 
      using \<open>p (inv p a) = a\<close> assms(2) by auto
  qed

lemma p_rev_p_same:
  assumes "p permutes (UNIV::'n set)"
  assumes "x \<in> set (support p ((inv f) (least_odd p)))" 
  shows "p (rev_p p x) = x" 
proof -
   have "(rev_p p x) = (inv p) x" 
    using rev_p_def 
    using assms(2) by presburger
  then show ?thesis 
    by (metis assms(1) permutes_inv_eq)
qed

lemma p_rev_p_same':
  assumes "p permutes (UNIV::'n set)"
  assumes "x \<notin> set (support p ((inv f) (least_odd p)))" 
  shows "(rev_p p x) = p x" 
  using assms(2) rev_p_def by presburger

lemma rev_p_permutes:
  assumes "p permutes (UNIV::'n set)"
  shows "(rev_p p) permutes (UNIV::'n set)" 
proof -
  have "(\<forall>y. \<exists>!x. p x = y)" 
    by (metis assms permutes_univ)
  have "(\<forall>x\<in>(UNIV::'n set). \<forall>y\<in>(UNIV::'n set). (rev_p p) x = (rev_p p) y \<longrightarrow> x = y)"
  proof(rule+)
    fix x y
    assume "x \<in> (UNIV::'n set)" "y \<in> (UNIV::'n set)" "(rev_p p) x = (rev_p p) y"
    show "x = y"
    proof(cases "x \<in> set (support p ((inv f) (least_odd p)))")
      case True
      have "p (rev_p p x) = x" 
        using True assms p_rev_p_same by presburger

      then show ?thesis 
      proof(cases "y \<in> set (support p ((inv f) (least_odd p)))")
        case True
            have "p (rev_p p y) = y" 
        using True assms p_rev_p_same by presburger

        then show ?thesis 
          by (metis \<open>p (rev_p p x) = x\<close> \<open>rev_p p x = rev_p p y\<close>)
      next
        case False
        have "(rev_p p y) = p y"    
          using False assms p_rev_p_same' by blast

          have "p ((rev_p p y)) = x"  
            using \<open>p (rev_p p x) = x\<close> \<open>rev_p p x = rev_p p y\<close> by auto
          then have "p (p y) = x" 
            by (simp add: \<open>rev_p p y = p y\<close>)
          then have "(p^^2) y = x" 
            by (metis One_nat_def add.right_neutral add_Suc_right funpow.simps(2) funpow_0 nat_1_add_1 o_apply)
          then have "y \<in> set (support p ((inv f) (least_odd p)))" 
            by (smt (verit, ccfv_threshold) True \<open>rev_p p x = rev_p p y\<close> assms inv_in_support map_eq_conv p_is_permutation permutes_inverses(2) rev_p_def)

then show ?thesis 
  using False by blast
qed
next
  case False
  then have "(rev_p p x) = p x"
    using assms p_rev_p_same' by presburger
  then show ?thesis
  proof(cases "y \<in> set (support p ((inv f) (least_odd p)))")
    case True
    have "p (rev_p p y) = y" 
      by (meson True assms tutte_matrix.p_rev_p_same tutte_matrix_axioms)
    then have "p (p x) = y" 
      using \<open>rev_p p x = p x\<close> \<open>rev_p p x = rev_p p y\<close> by auto
    then have "(p^^2) x = y" 
      by (metis One_nat_def funpow.simps(2) funpow_0 o_apply one_add_one plus_1_eq_Suc)
    then have "x \<in> set (support p ((inv f) (least_odd p)))" 
      by (smt (z3) True \<open>rev_p p x = rev_p p y\<close> assms inv_in_support map_eq_conv p_is_permutation permutes_inverses(2) rev_p_def)

    then show ?thesis 
      using False by blast
  next
    case False
    have "(rev_p p y) = p y" 
      using False assms p_rev_p_same' by presburger
    then show ?thesis 
      using \<open>\<forall>y. \<exists>!x. p x = y\<close> \<open>rev_p p x = p x\<close> \<open>rev_p p x = rev_p p y\<close> by auto
  qed
qed
qed

  have "inj_on (rev_p p) (UNIV::'n set)" 
    by (simp add: \<open>\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. rev_p p x = rev_p p y \<longrightarrow> x = y\<close> injI)

  have "(rev_p p) ` (UNIV::'n set) = (UNIV::'n set)"
  proof 
    show "range (rev_p p) \<subseteq> UNIV" by auto
    show "UNIV \<subseteq> range (rev_p p)" 
    proof
      fix x
      assume "x \<in> (UNIV :: 'n set )" 
      show "x \<in> range (rev_p p)" 
      proof(cases "x \<in> set (support p ((inv f) (least_odd p)))")
        case True
        have "p x \<in> set (support p ((inv f) (least_odd p)))" 
          using True assms inv_notin_support p_is_permutation permutes_inverses(2) by fastforce
        then have "p (rev_p p (p x)) = p x" 
          using True assms p_rev_p_same by presburger
        then have "(rev_p p (p x)) = x" 
          by (meson assms injD permutes_inj)
        then show ?thesis  
          by (metis range_eqI)
      next
        case False
        have "(rev_p p x) = p x" 
          using False assms p_rev_p_same' by presburger
        then have "(rev_p p (inv p x)) = p (inv p x)" 
          by (smt (verit, ccfv_SIG) \<open>x \<in> UNIV\<close> assms inv_notin_support map_eq_conv p_is_permutation p_rev_p_same permutes_inv_eq rev_p_def)
        then have "(rev_p p (inv p x)) = x" 
          by (metis assms permutes_inv_eq)
        then show ?thesis 
          by (metis range_eqI)
      qed
    qed
  qed
  then have "bij_betw (rev_p p) UNIV UNIV" 
    by (simp add: \<open>inj (rev_p p)\<close> bij_betw_def)

  then show "(rev_p p) permutes UNIV" 
    by (simp add: bij_iff permutes_univ)
qed



lemma odd_component_then_odd_circuit:
  assumes "p permutes (UNIV :: 'n set)" 
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C) "
  obtains i where "odd (least_power p i)"
proof -
  obtain C where "C \<in> connected_components (u_edges p) \<and> odd (card C)"
    using assms by blast
  then obtain x where "x \<in> C" 
    by (metis card.empty card.infinite finite_has_maximal odd_card_imp_not_empty)
  then have "x \<in> Vs (u_edges p)" 
    by (meson \<open>C \<in> connected_components (u_edges p) \<and> odd (card C)\<close> connected_comp_verts_in_verts)

  then obtain i where "f i = x" using perm_verts_in_all_verts 
    by (meson assms(1) subsetD vertices_in_range)
  have "C = set (map f (support p i))" using support_is_connected_component[of p C i]  
    using \<open>C \<in> connected_components (u_edges p) \<and> odd (card C)\<close> \<open>f i = x\<close> \<open>x \<in> C\<close> assms(1) by fastforce
  then have " odd (least_power p i)" 
    by (metis (no_types, lifting) \<open>C \<in> connected_components (u_edges p) \<and> odd (card C)\<close> 
          assms(1) cycle_vert_is_distict diff_zero distinct_card length_map length_upt)
  show ?thesis 
    using \<open>odd (least_power p i)\<close> that by auto
qed



lemma least_odd_is_odd:
  assumes "p permutes (UNIV :: 'n set)" 
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C) "
  shows "odd (least_power p ((inv f) (least_odd p)))" 
proof -
  obtain i where "odd (least_power p i)" using odd_component_then_odd_circuit[of p] assms 
    by blast
  have "(inv f) (f i) = i" 
    by (meson UNIV_I bij bij_betw_inv_into_left)
  then have " odd (least_power p ((inv f) (f i)))" 
    by (simp add: \<open>odd (least_power p i)\<close>)
  then show ?thesis
    by (metis least_odd_def wellorder_Least_lemma(1))
qed

lemma rev_value_minus:
 assumes "p permutes (UNIV::'n set)"
      shows "(tutte_matrix x)$i$p i = - (tutte_matrix x) $ p i$i " 
      proof(cases "(f i, f (p i)) \<in> oriented_edges")
        case True
        then have "(tutte_matrix x)$i$p i = x {f i, f (p i)}" using in_oriented 
          by blast
        have "(f (p i), f i) \<notin> oriented_edges" 
          using True order_less_asym oriented_edges_def by auto
        then show ?thesis 
          by (simp add: True \<open>local.tutte_matrix x $ i $ p i = x {f i, f (p i)}\<close> insert_commute rev_in_oriented)
      next
        case False
        then have "(f i, f (p i)) \<notin> oriented_edges" 
          by simp
        then show ?thesis 
        proof(cases "(f (p i), f i) \<in> oriented_edges")
          case True
 then have "(tutte_matrix x)$i$p i = - x {f i, f (p i)}" using rev_in_oriented 
          by blast
        then show ?thesis 
          by (simp add: True \<open>local.tutte_matrix x $ i $ p i = - x {f i, f (p i)}\<close> in_oriented insert_commute)
next
  case False
  have "{f i, f (p i)} \<notin> E" using not_in_both_oriented False 
    by (simp add: \<open>(f i, f (p i)) \<notin> oriented_edges\<close>)
  then have "(tutte_matrix x)$i$p i = 0" 
    by (simp add: edge_not_in_E_zero_elem)
  have "(tutte_matrix x)$p i$i = 0" 
    by (meson False \<open>(f i, f (p i)) \<notin> oriented_edges\<close> edge_not_in_E_zero_elem not_in_both_oriented)

  then show ?thesis 
    using \<open>local.tutte_matrix x $ i $ p i = 0\<close> by force
qed 
qed


lemma reverse_for_each_product:
  fixes h :: "'n \<Rightarrow> 'b::comm_ring_1"
  assumes "\<forall>a \<in> A. h a = - (g a)"
  assumes "odd (card A)"
  shows "prod h A = - prod g A" 
 using assms
proof(induct "card A" arbitrary: A rule: less_induct)
  case less
  have "finite A" 
    by (metis card_eq_0_iff dvd_0_right less.prems(2))
  then show ?case
  proof(cases "card A = 1")
    case True
    obtain a where "a \<in> A" 
      by (metis True card.empty card_mono finite.emptyI le_0_eq subset_eq zero_neq_one)
    then have "A = {a}" 
      using True card_1_singletonE by blast
    then have "prod h A = h a" 
      by simp
    have "prod g A = g a" using `A = {a}` by simp
  
then show ?thesis 
  using \<open>a \<in> A\<close> \<open>prod h A = h a\<close> less.prems(1) by force
next
  case False
  then have "card A > 1" 
    by (metis card.empty less.prems(2) less_one linorder_neqE_nat odd_card_imp_not_empty)
  then obtain a b where "a \<in> A \<and> b \<in> A \<and> a \<noteq> b" 
    by (metis Diff_iff One_nat_def card_Suc_Diff1 card_eq_0_iff ex_in_conv less_imp_not_less not_one_less_zero singletonI)
  then have "odd (card (A - {a, b}))" 
    by (smt (verit, ccfv_threshold) Suc_pred \<open>1 < card A\<close> add_diff_cancel_left' canonically_ordered_monoid_add_class.lessE card.infinite card_0_eq card_Diff_insert card_Diff_singleton card_gt_0_iff even_Suc even_add even_diff_nat insert_absorb insert_iff insert_not_empty less.prems(2) plus_1_eq_Suc)
  have "(card (A - {a, b})) < card A" 
    by (metis Diff_insert2 \<open>1 < card A\<close> \<open>a \<in> A \<and> b \<in> A \<and> a \<noteq> b\<close> card.infinite card_Diff2_less dual_order.strict_trans finite.insertI finite_Diff2 less_one)
  have "\<forall>a \<in> (A - {a, b}). h a = - (g a)" 
    by (meson DiffD1 less.prems(1))
  then have "prod h (A - {a, b}) = - prod g (A - {a, b})" 
    using \<open>card (A - {a, b}) < card A\<close> \<open>odd (card (A - {a, b}))\<close> less.hyps by presburger
  have "prod h A = prod h (A - {a, b}) * prod h {a, b}" 
    by (metis Diff_cancel Diff_subset \<open>a \<in> A \<and> b \<in> A \<and> a \<noteq> b\<close> \<open>finite A\<close> insert_subset prod.subset_diff)
  have "prod g A = prod g (A - {a, b}) * prod g {a, b}"
    by (metis Diff_cancel Diff_subset \<open>a \<in> A \<and> b \<in> A \<and> a \<noteq> b\<close> \<open>finite A\<close> insert_subset prod.subset_diff)
  have " prod h {a, b} = h a * h b" 
    by (simp add: \<open>a \<in> A \<and> b \<in> A \<and> a \<noteq> b\<close>)
  have " prod g {a, b} = g a * g b" 
    by (simp add: \<open>a \<in> A \<and> b \<in> A \<and> a \<noteq> b\<close>)
  then have "h a * h b = (- g a)*(-g b)" 
    by (simp add: \<open>a \<in> A \<and> b \<in> A \<and> a \<noteq> b\<close> less.prems(1))

  have "(- g a)*(-g b) = ((-1) * g a) * ((-1) * g b)" 
    by simp
  then show ?thesis 
    by (simp add: \<open>h a * h b = - g a * - g b\<close> \<open>prod g A = prod g (A - {a, b}) * prod g {a, b}\<close> \<open>prod g {a, b} = g a * g b\<close> \<open>prod h (A - {a, b}) = - prod g (A - {a, b})\<close> \<open>prod h A = prod h (A - {a, b}) * prod h {a, b}\<close> \<open>prod h {a, b} = h a * h b\<close>)
qed
qed

definition on_odd where
  "on_odd p = (\<lambda> x. if x \<in> set (support p ((inv f) (least_odd p))) then p x else x)" 

definition not_on_odd where
  "not_on_odd p = (\<lambda> x. if x \<notin> set (support p ((inv f) (least_odd p))) then p x else x)" 


lemma on_odd_in:
  assumes "x \<in>  set (support p ((inv f) (least_odd p)))"
  shows "on_odd p x = p x" 
  unfolding on_odd_def using assms by auto

lemma on_odd_out:
  assumes "x \<notin>  set (support p ((inv f) (least_odd p)))"
  shows "on_odd p x = x" 
  unfolding on_odd_def using assms by auto

lemma not_on_odd_in:
  assumes "x \<notin>  set (support p ((inv f) (least_odd p)))"
  shows "not_on_odd p x = p x" 
  unfolding not_on_odd_def using assms by auto

lemma not_on_odd_out:
  assumes "x \<in>  set (support p ((inv f) (least_odd p)))"
  shows "not_on_odd p x = x" 
  unfolding not_on_odd_def using assms by auto


lemma on_odd_p_permutes:
  assumes "p permutes (UNIV::'n set)"
  shows "(on_odd p) permutes (set (support p ((inv f) (least_odd p))))" 
proof -
  let ?A = "(set (support p ((inv f) (least_odd p))))" 
  have "(\<forall>x\<in>?A. \<forall>y\<in>?A. (on_odd p) x = (on_odd p) y \<longrightarrow> x = y)"
  proof(rule+)
    fix x y
    assume "x \<in> ?A" "y \<in> ?A"  "on_odd p x = on_odd p y" 
   then have "on_odd p x = p x" 
        using on_odd_in
        by blast
   then have "on_odd p y = p y" 
        using on_odd_in 
        using \<open>y \<in> set (support p (inv f (least_odd p)))\<close> by blast

      then show "x = y" 
        by (metis \<open>on_odd p x = on_odd p y\<close> \<open>on_odd p x = p x\<close> assms permutes_def)
    qed
    then have "inj_on (on_odd p) ?A" 
      using inj_on_def by blast
    have "(on_odd p) ` ?A = ?A"
    proof(safe)
      { 
        fix x
        assume "x \<in> ?A"
        then have "p x \<in> ?A" 
          using assms p_in_same_cycle by blast

        then show "on_odd p x \<in> ?A" 
          using \<open>x \<in> set (support p (inv f (least_odd p)))\<close> on_odd_def by presburger
      }
      fix x
      assume "x \<in> ?A" 
      show "x \<in> (on_odd p) ` ?A" 
        by (smt (verit, ccfv_SIG) \<open>x \<in> set (support p (inv f (least_odd p)))\<close> assms image_iff inv_in_support map_eq_conv p_is_permutation rev_p_def tutte_matrix.on_odd_def tutte_matrix.p_rev_p_same tutte_matrix_axioms)
    qed
 then have "bij_betw (on_odd p) ?A ?A" unfolding bij_betw_def 
   using \<open>inj_on (on_odd p) ?A\<close> by blast
  have "(\<And>x. x \<notin> ?A \<Longrightarrow> (on_odd p) x = x)" 
    using on_odd_out by presburger
  then show " (on_odd p) permutes ?A" using  Permutations.bij_imp_permutes
    
    using \<open>bij_betw (on_odd p) (set (support p (inv f (least_odd p)))) (set (support p (inv f (least_odd p))))\<close> by blast
qed

lemma on_odd_p_permutes_UNIV:
  assumes "p permutes (UNIV::'n set)"
  shows "(on_odd p) permutes UNIV" using on_odd_p_permutes assms 
  by (meson bij_imp_permutes iso_tuple_UNIV_I permutes_bij)

lemma not_on_odd_p_permutes:
  assumes "p permutes (UNIV::'n set)"
  shows "(not_on_odd p) permutes (UNIV::'n set) - (set (support p ((inv f) (least_odd p))))"
proof -
  let ?A = "(UNIV::'n set) - (set (support p ((inv f) (least_odd p))))"
  have "(\<forall>x\<in>?A. \<forall>y\<in>?A. (not_on_odd p) x = (not_on_odd p) y \<longrightarrow> x = y)"
  proof(rule+) 
    fix x y
    assume "x \<in> ?A" "y \<in> ?A"  "not_on_odd p x = not_on_odd p y" 
   then have "not_on_odd p x = p x" 
        using not_on_odd_in
        by blast
   then have "not_on_odd p y = p y" 
        using not_on_odd_in 
        using \<open>y \<in> ?A\<close> by blast

      then show "x = y" 
        by (metis \<open>not_on_odd p x = not_on_odd p y\<close> \<open>not_on_odd p x = p x\<close> assms permutes_inv_eq)
    qed
  then have "inj_on (not_on_odd p) ?A" 
      using inj_on_def by blast
    have "(not_on_odd p) ` ?A = ?A"
    proof(rule)+
      show "?A \<subseteq> not_on_odd p ` ?A"
      proof
        fix x
        assume "x \<in> ?A"
        then have "p x \<in> ?A" 
          by (smt (z3) Diff_iff UNIV_I assms bij_betw_inv_into_left inv_in_support map_eq_conv p_is_permutation permutes_imp_bij)

    
        then show "x \<in> not_on_odd p ` ?A" 
          using \<open>x \<in> ?A\<close> not_on_odd_def 
          by (smt (z3) Diff_iff assms bij_is_surj image_iff inj_onD map_eq_conv on_odd_def on_odd_p_permutes permutes_imp_bij permutes_inj)

      qed
      fix x
      assume "x \<in>  not_on_odd p ` ?A"  "x \<in>  set (support p (inv f (least_odd p))) " 
     have "(inv p x) \<in> set (support p (inv f (least_odd p)))" 
        by (smt (z3) \<open>x \<in> set (support p (inv f (least_odd p)))\<close> assms bij_is_surj map_eq_conv on_odd_def on_odd_p_permutes p_is_permutation permutation_bijective permutation_inverse permutes_inv_inv permutes_inverses(1) surj_f_inv_f)
      then have "x \<in> ?A" 
        by (smt (z3) \<open>x \<in> not_on_odd p ` (UNIV - set (support p (inv f (least_odd p))))\<close> assms bij_is_surj f_inv_into_f inv_into_into mem_Collect_eq p_is_permutation permutation_bijective permutation_inverse set_diff_eq tutte_matrix.not_on_odd_def tutte_matrix_axioms)

      then show False 
        using \<open>x \<in> set (support p (inv f (least_odd p)))\<close> by force
    qed
 then have "bij_betw (not_on_odd p) ?A ?A" unfolding bij_betw_def 
   using \<open>inj_on (not_on_odd p) ?A\<close> by blast
 have "(\<And>x. x \<notin> ?A \<Longrightarrow> (not_on_odd p) x = x)" 
    using not_on_odd_out 
    by simp
  then show " (not_on_odd p) permutes ?A" using  Permutations.bij_imp_permutes
    using \<open>bij_betw (not_on_odd p) (UNIV - set (support p (inv f (least_odd p)))) (UNIV - set (support p (inv f (least_odd p))))\<close> by blast
qed

lemma not_on_odd_p_permutes_UNIV:
  assumes "p permutes (UNIV::'n set)"
  shows "(not_on_odd p) permutes (UNIV::'n set)"
  using not_on_odd_p_permutes assms 
  using permutes_subset by blast

lemma least_odd_inv_same:
  assumes "p permutes (UNICV ::'n set)"
  shows " (least_odd (inv p)) =  (least_odd p)"
  oops

lemma rev_is_composition:
  assumes "p permutes (UNIV::'n set)"
  shows "rev_p p = ((inv (on_odd  p)) \<circ>  not_on_odd p)"
proof
  let ?A = "(set (support p ((inv f) (least_odd p))))" 
  fix x
  show " rev_p p x = ((inv (on_odd  p)) \<circ>  not_on_odd p) x"
  proof(cases "x \<in> ?A")
    case True
    have "not_on_odd p x = x" 
      using True not_on_odd_out by presburger
   have " (on_odd  p) x = p x" using on_odd_in[of x "inv p"] True 
     using on_odd_def by presburger
   then have "inv (on_odd  p) x = (inv p) x" 
     by (smt (verit, ccfv_threshold) assms on_odd_p_permutes_UNIV permutes_inv_eq tutte_matrix.on_odd_def tutte_matrix_axioms)
   then have "rev_p p x = (inv p x)" 
  by (metis \<open>on_odd p x = p x\<close> assms on_odd_def permutes_inv_eq rev_p_def)
then show ?thesis 
  by (simp add: \<open>inv (on_odd p) x = inv p x\<close> \<open>not_on_odd p x = x\<close>)
next
  case False
  have "rev_p p x = p x" using False assms unfolding  rev_p_def 
    by presburger
  have "not_on_odd p x = p x" 
    using False not_on_odd_in by presburger
  have "inv (on_odd  p) (p x) = p x" 
    by (smt (z3) \<open>not_on_odd p x = p x\<close> assms bij_is_surj inj_imp_surj_inv not_on_odd_def on_odd_def on_odd_p_permutes_UNIV permutes_imp_bij permutes_inj permutes_inv_inv surj_f_inv_f)

  then show ?thesis 
    using \<open>not_on_odd p x = p x\<close> \<open>rev_p p x = p x\<close> by force
qed
  
qed

lemma p_is_composition:
  assumes "p permutes (UNIV::'n set)"
  shows "p = on_odd  p \<circ>  not_on_odd p"
proof
  fix x
 let ?A = "(set (support p ((inv f) (least_odd p))))" 
  show "p x = (on_odd p \<circ> not_on_odd p) x" 
  proof(cases "x \<in> ?A")
    case True
    have "not_on_odd p x = x" 
      using True not_on_odd_out by presburger
    have "on_odd p x = p x" 
      by (metis \<open>not_on_odd p x = x\<close> not_on_odd_def on_odd_def)
    then show ?thesis 
      by (simp add: \<open>not_on_odd p x = x\<close>)
  next
    case False
     have "not_on_odd p x = p x" 
      using False not_on_odd_in by presburger
    have "on_odd p (p x) = p x" 
      by (metis (full_types) \<open>not_on_odd p x = p x\<close> assms not_on_odd_def not_on_odd_p_permutes_UNIV on_odd_def permutes_univ)

    then show ?thesis 
      by (simp add: \<open>not_on_odd p x = p x\<close>)
  qed
qed


lemma rev_product_is_minus:
  assumes "p permutes (UNIV::'n set)"
 assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C) "
  shows " prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set) = 
          -  prod (\<lambda>i. (tutte_matrix x)$i$(rev_p p) i) (UNIV :: 'n set)" 
proof -
  let ?A = "set (support p ((inv f) (least_odd p)))"
  let ?h = "(\<lambda>i. (tutte_matrix x)$i$p i)" 
  let ?g = "(\<lambda>i. (tutte_matrix x)$i$(rev_p p) i)" 

  have "prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set) = 
      prod (\<lambda>i. (tutte_matrix x)$i$p i) ?A *  prod (\<lambda>i. (tutte_matrix x)$i$p i) ((UNIV :: 'n set) - ?A)"
    by (metis (no_types, lifting) finite_class.finite_UNIV mult.commute prod.subset_diff top_greatest)

  have "prod (\<lambda>i. (tutte_matrix x)$i$(rev_p p) i) (UNIV :: 'n set) = 
      prod (\<lambda>i. (tutte_matrix x)$i$(rev_p p) i) ?A *  prod (\<lambda>i. (tutte_matrix x)$i$(rev_p p) i) ((UNIV :: 'n set) - ?A)"
    by (metis (no_types, lifting) finite_class.finite_UNIV mult.commute prod.subset_diff top_greatest)

  have "\<forall> i\<in> ((UNIV :: 'n set) - ?A). (rev_p p) i = p i" 
    using assms p_rev_p_same' by auto
  then have " prod ?h ((UNIV :: 'n set) - ?A) =  prod ?g ((UNIV :: 'n set) - ?A)"    
    by force
  have "odd (card ?A)" 
    by (smt (verit, del_insts) assms(1) assms(2) diff_zero distinct_card least_odd_is_odd length_map length_upt map_eq_conv perm_support_distinct)
  have "\<forall> i \<in> ?A. (tutte_matrix x)$i$p i = - (tutte_matrix x)$p i$(rev_p p) (p i)" 
  proof
    fix i
    assume "i \<in> ?A"
    show "(tutte_matrix x)$i$p i = - (tutte_matrix x)$p i$((rev_p p) (p i))"
    proof - 
      have "p (rev_p p i) = i" 
       
        using \<open>i \<in> set (support p (inv f (least_odd p)))\<close> assms(1) p_rev_p_same by presburger
      then have "(rev_p p) (p i) = i" 
        by (smt (verit, best) assms(1) bij_inv_eq_iff map_eq_conv p_is_permutation permutes_imp_bij rev_p_def tutte_matrix.inv_notin_support tutte_matrix_axioms)
      show ?thesis 
        using \<open>rev_p p (p i) = i\<close> assms(1) rev_value_minus by auto
    qed
  qed
  then have "\<forall> i \<in> ?A. ?h i = - (?g \<circ> (on_odd p)) i" 
    using tutte_matrix.on_odd_def tutte_matrix_axioms by fastforce
  then have "prod ?h ?A = - prod (?g \<circ> (on_odd p)) ?A" using reverse_for_each_product 
    by (metis (no_types, lifting) \<open>odd (card (set (support p (inv f (least_odd p)))))\<close>)
  
   
  have " prod ?g ?A =  prod (?g \<circ> (on_odd p)) ?A"
    using  Permutations.comm_monoid_mult_class.prod.permute [of "on_odd p" "?A" ?g] 
    using assms(1) on_odd_p_permutes by presburger
  then have "prod ?h ?A = -  prod ?g ?A " 
    using \<open>(\<Prod>i\<in>set (support p (inv f (least_odd p))). local.tutte_matrix x $ i $ p i) = - prod ((\<lambda>i. local.tutte_matrix x $ i $ rev_p p i) \<circ> on_odd p) (set (support p (inv f (least_odd p))))\<close> by presburger
  then show ?thesis 
    using \<open>(\<Prod>i\<in>UNIV - set (support p (inv f (least_odd p))). local.tutte_matrix x $ i $ p i) = (\<Prod>i\<in>UNIV - set (support p (inv f (least_odd p))). local.tutte_matrix x $ i $ rev_p p i)\<close> \<open>(\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i) = (\<Prod>i\<in>set (support p (inv f (least_odd p))). local.tutte_matrix x $ i $ p i) * (\<Prod>i\<in>UNIV - set (support p (inv f (least_odd p))). local.tutte_matrix x $ i $ p i)\<close> \<open>(\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ rev_p p i) = (\<Prod>i\<in>set (support p (inv f (least_odd p))). local.tutte_matrix x $ i $ rev_p p i) * (\<Prod>i\<in>UNIV - set (support p (inv f (least_odd p))). local.tutte_matrix x $ i $ rev_p p i)\<close> by force
qed



lemma rev_has_same_parity:
  assumes "p permutes (UNIV::'n set)"
 shows "evenperm p = evenperm (rev_p p)"
proof -
  have "permutation p" 
    by (simp add: assms(1) p_is_permutation)
  have "permutation (on_odd p)" 
    by (simp add: assms(1) on_odd_p_permutes_UNIV p_is_permutation)
  have "permutation (not_on_odd p)" 
    by (simp add: assms(1) not_on_odd_p_permutes_UNIV p_is_permutation)
  have "p = on_odd  p \<circ>  not_on_odd p" 
    by (simp add: assms(1) p_is_composition)
  have "(rev_p p) = (inv (on_odd  p)) \<circ>  not_on_odd p"
    using rev_is_composition 
    using assms(1) by auto
  have "evenperm p \<longleftrightarrow> evenperm (on_odd  p) = evenperm (not_on_odd p)" 
    by (metis \<open>p = on_odd p \<circ> not_on_odd p\<close> \<open>permutation (not_on_odd p)\<close> \<open>permutation (on_odd p)\<close> evenperm_comp)

  have "evenperm (on_odd  p) = evenperm (inv (on_odd  p))" 
    by (simp add: \<open>permutation (on_odd p)\<close> evenperm_inv)
  have "evenperm (rev_p p) \<longleftrightarrow> evenperm (inv (on_odd  p)) = evenperm (not_on_odd p)"
    by (simp add: \<open>permutation (not_on_odd p)\<close> \<open>permutation (on_odd p)\<close> \<open>rev_p p = inv (on_odd p) \<circ> not_on_odd p\<close> evenperm_comp permutation_inverse)
  then show ?thesis 
    by (simp add: \<open>evenperm p = (evenperm (on_odd p) = evenperm (not_on_odd p))\<close> \<open>permutation (on_odd p)\<close> evenperm_inv)
qed

lemma rev_same_sign:
  assumes "p permutes (UNIV :: 'n set)" 
  shows "of_int (sign p) = of_int (sign (rev_p p))" 
  by (simp add: assms rev_has_same_parity sign_def)

lemma rev_opposite_value:
  assumes "p permutes (UNIV :: 'n set)"
 assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C) " 
  shows "(\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set)) p = 
 - (\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set)) (rev_p p)" (is  " ?g  p = - ?g (rev_p p)")
 
proof -
  have "of_int (sign p) = of_int (sign (rev_p p))" 
    using assms(1) rev_same_sign by blast
  have " prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set) =
  -  prod (\<lambda>i. (tutte_matrix x)$i$(rev_p p) i) (UNIV :: 'n set)"
    using rev_product_is_minus assms   
    by blast
  then show ?thesis 
    by (simp add: \<open>of_int (sign p) = of_int (sign (rev_p p))\<close>)
qed

lemma rev_nonzero_is_nonzero:
  assumes "p \<in> nonzero_perms x"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows "rev_p p \<in> nonzero_perms x" 
proof -
  have "p permutes UNIV" 
    using assms nonzero_perms_def by auto
  have " prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set) \<noteq> 0"
    using assms unfolding nonzero_perms_def  
    by force
  then have " prod (\<lambda>i. (tutte_matrix x)$i$(rev_p p) i) (UNIV :: 'n set) \<noteq> 0"
    by (simp add: \<open>(\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i) \<noteq> 0\<close> \<open>\<exists>C\<in>connected_components (u_edges p). odd (card C)\<close> \<open>p \<in> nonzero_perms x\<close> rev_product_is_minus \<open>p permutes UNIV\<close> add.inverse_neutral)
  then show "rev_p p \<in> nonzero_perms x" unfolding nonzero_perms_def 
    using \<open>p permutes UNIV\<close> rev_p_permutes by force
qed

lemma rev_least_odd_same:
 assumes "p permutes (UNIV:: 'n set)"
 assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
 shows "least_odd p = least_odd (rev_p p)" 
proof -
  let ?A = "(set (support p ((inv f) (least_odd p))))" 
  let ?i = "(inv f) (least_odd p)"
  have "odd (least_power p ?i)"  
    using assms(1) assms(2) least_odd_is_odd by presburger
  have "(p^^0) ?i = ?i" sledgehammer
  have "?i \<in> ?A" 



lemma rev_rev_same:
  assumes "p permutes (UNIV:: 'n set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows "rev_p (rev_p p) = p" 
proof 
  fix x
let ?A = "(set (support p ((inv f) (least_odd p))))" 
  have "rev_p p = ((inv (on_odd  p)) \<circ>  not_on_odd p)"
  
  using assms(1) rev_is_composition by auto
  then have "rev_p (rev_p p) = ((inv (on_odd  (rev_p p))) \<circ>  not_on_odd (rev_p p))"
    using assms(1) rev_is_composition rev_p_permutes by blast
  then have "rev_p (rev_p p) = ((inv (on_odd  ((inv (on_odd  p)) \<circ>  not_on_odd p))) \<circ>  
          not_on_odd ((inv (on_odd  p)) \<circ>  not_on_odd p))" 
    by (simp add: \<open>rev_p p = inv (on_odd p) \<circ> not_on_odd p\<close>)
 
  show "rev_p (rev_p p) x = p x"
  proof(cases "x \<in> ?A")
    case True
    
    then show ?thesis sorry
  next
    case False
    then show ?thesis sorry
  qed

lemma zero_det_each_has_odd_circuit:
  assumes "\<forall>p \<in> nonzero_perms x. \<exists>C \<in> connected_components (u_edges p). odd (card C) "
  shows "det (tutte_matrix x) = 0"
proof -
  let ?g = "(\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix x)$i$p i) (UNIV :: 'n set))" 
  have "finite {p. p permutes (UNIV :: 'n set)}" 
    by simp
  then have "{p. p permutes (UNIV :: 'n set)} = 
        {p. p permutes (UNIV :: 'n set) \<and> ?g p \<noteq> 0 } \<union> 
            {p. p permutes (UNIV :: 'n set) \<and> ?g p = 0}" by auto
  have " {p. p permutes (UNIV :: 'n set) \<and> ?g p \<noteq> 0 } \<inter> 
            {p. p permutes (UNIV :: 'n set) \<and> ?g p = 0} = {}" by auto
  then have "sum ?g {p. p permutes (UNIV :: 'n set)} = 
            sum ?g  {p. p permutes (UNIV :: 'n set) \<and> ?g p \<noteq> 0 } + 
            sum ?g  {p. p permutes (UNIV :: 'n set) \<and> ?g p = 0 }"
    
    by (simp add: \<open>{p. p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i) \<noteq> 0} \<inter> {p. p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i) = 0} = {}\<close> \<open>finite {p. p permutes UNIV}\<close> \<open>{p. p permutes UNIV} = {p. p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i) \<noteq> 0} \<union> {p. p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i) = 0}\<close>  sum.union_disjoint)
  have " sum ?g  {p. p permutes (UNIV :: 'n set) \<and> ?g p = 0 } = 0" 
    by auto
  then have "sum ?g {p. p permutes (UNIV :: 'n set)} = 
            sum ?g  {p. p permutes (UNIV :: 'n set) \<and> ?g p \<noteq> 0 }"  
    by (simp add: \<open>(\<Sum>p | p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i)) = (\<Sum>p | p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i) \<noteq> 0. of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i)) + (\<Sum>p | p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i) = 0. of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i))\<close>)

  have "det (tutte_matrix x) =  sum ?g {p. p permutes (UNIV :: 'n set)}" 
    using tutte_matrix_det by force
  then have "det (tutte_matrix x) = 
     sum ?g {p. p permutes (UNIV :: 'n set) \<and> ?g p \<noteq> 0}"
    using \<open>(\<Sum>p | p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i)) = (\<Sum>p | p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i) \<noteq> 0. of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix x $ i $ p i))\<close> by presburger

  
    

end

end