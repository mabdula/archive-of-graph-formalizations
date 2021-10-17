theory Tutte_matrix
  imports "HOL-Library.Permutations" "HOL-Analysis.Determinants" Tutte_theorem3
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
  fixes E :: "'a::linorder set set"
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

lemma even_circuits_has_perfect_matching:
  assumes "p \<in> nonzero_perms X"
  assumes "\<forall>C \<in> connected_components (u_edges p). even (card C) "
  shows "\<exists> M. perfect_matching (u_edges p) M"
proof
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
    show "\<exists> M'. perfect_matching (component_edges (u_edges p) C) M'"
    proof
      let ?C = "(component_edges (u_edges p) C)"
      have "Vs ?C = C"
      proof(safe)
        {
          fix x 
          assume "x \<in> Vs ?C"
          then obtain x' y' where "{x', y'} \<in> ?C \<and> x \<in> {x', y'}" 
  by (smt (verit) Berge.component_edges_subset assms(1) graph subsetD tutte_matrix.wqewqe1 tutte_matrix_axioms vs_member_elim)

  then have "{x', y'} \<subseteq> C \<and> {x', y'} \<in> (u_edges p)" unfolding component_edges_def
    
    by force
          show "x \<in> C" 
            using \<open>{x', y'} \<in> component_edges (u_edges p) C \<and> x \<in> {x', y'}\<close> \<open>{x', y'} \<subseteq> C \<and> {x', y'} \<in> u_edges p\<close> by blast
        }

        fix x
        assume "x \<in> C"
        then obtain y where " {x, y} \<in> (u_edges p)" 
          by (smt (verit, ccfv_SIG) \<open>C \<subseteq> Vs (u_edges p)\<close> assms(1) insert_commute insert_iff singletonD subsetD tutte_matrix.u_edges_is_graph tutte_matrix_axioms vs_member_elim)

        then have "C = connected_component  (u_edges p) x" 
          by (simp add: \<open>C \<in> connected_components (u_edges p)\<close> \<open>x \<in> C\<close> connected_components_closed')
        then have "y \<in> C" 
          by (smt (verit, ccfv_threshold) \<open>{x, y} \<in> u_edges p\<close> connected_comp_has_vert connected_components_closed edge_in_component insertCI subsetD)
        then have "{x, y} \<subseteq> C" 
          by (simp add: \<open>x \<in> C\<close>)
        show "x \<in> Vs ?C" 
          by (smt (verit, del_insts) \<open>{x, y} \<in> u_edges p\<close> \<open>{x, y} \<subseteq> C\<close> assms(1) edge_in_component_edges insertCI tutte_matrix.u_edges_is_graph tutte_matrix_axioms vs_member)
      qed

        
      have "\<forall> X \<subseteq> C. card (diff_odd_components ?C X) \<le> card X"
      proof(rule)+
        fix X
        assume "X \<subseteq> C"
        have "finite X" 
          by (meson \<open>C \<subseteq> Vs (u_edges p)\<close> \<open>X \<subseteq> C\<close> assms(1) finite_subset u_edges_is_graph)
        show "card (diff_odd_components ?C X) \<le> card X" using `finite X`
        proof(induct X)
          case empty
          
          have "(diff_odd_components ?C {}) =
  {C'. \<exists> v\<in>Vs ?C-{}. connected_component (graph_diff ?C {}) v = C' \<and> odd (card C')}" by blast
          have "graph_diff ?C {} = ?C" 
            using graph_diff_empty by blast
          have " {C'. \<exists> v\<in>Vs ?C-{}. connected_component (graph_diff ?C {}) v = C' \<and> odd (card C')} =
           {C'. \<exists> v\<in>C. connected_component ?C v = C' \<and> odd (card C')}" 
    using \<open>Vs (component_edges (u_edges p) C) = C\<close> \<open>graph_diff (component_edges (u_edges p) C) {} = component_edges (u_edges p) C\<close> by force
  have "connected_components ?C = {C}" sorry


  then show ?case 
    by (smt (verit, best) Collect_empty_eq \<open>C \<in> connected_components (u_edges p)\<close> \<open>diff_odd_components (component_edges (u_edges p) C) {} = {C'. \<exists>v\<in>Vs (component_edges (u_edges p) C) - {}. connected_component (graph_diff (component_edges (u_edges p) C) {}) v = C' \<and> odd (card C')}\<close> \<open>{C'. \<exists>v\<in>Vs (component_edges (u_edges p) C) - {}. connected_component (graph_diff (component_edges (u_edges p) C) {}) v = C' \<and> odd (card C')} = {C'. \<exists>v\<in>C. connected_component (component_edges (u_edges p) C) v = C' \<and> odd (card C')}\<close> assms(2) card.empty card_mono connected_components_closed' finite.emptyI singletonI subset_iff)

next
case (insert x F)
then show ?case sorry
qed

end



fun get_cycles :: "('n \<Rightarrow> 'n) \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
"get_cycles [] xs = xs"


function f ::"Enum.finite_3 \<Rightarrow> Enum.finite_3 set " where
"f (0::Enum.finite_3) = {1, 2}" |
"f (1::Enum.finite_3) = {0, 2}" |
"f (2::Enum.finite_3) = {0, 1}"
proof -
  fix P

  show "\<And>x. (x = 0 \<Longrightarrow> P) \<Longrightarrow>
           (x = 1 \<Longrightarrow> P) \<Longrightarrow>
           (x = 2 \<Longrightarrow> P) \<Longrightarrow> P" 
    proof -
    fix x
    show  " (x = (0::Enum.finite_3) \<Longrightarrow> P) \<Longrightarrow> (x = 1 \<Longrightarrow> P) \<Longrightarrow> (x = 2 \<Longrightarrow> P) \<Longrightarrow> P"

value "tutte_matrix "
end