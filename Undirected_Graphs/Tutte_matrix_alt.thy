theory Tutte_matrix_alt
  imports "HOL-Algebra.Cycles" "HOL-Analysis.Determinants" Tutte_theorem3
    "HOL-Library.Poly_Mapping"
begin


text \<open>Embedding of indeterminates and constants in type-class polynomials,
  can be used as constructors.\<close>
  (* Author: Andreas Lochbihler, ETH Zurich
   Author: Florian Haftmann, TU Muenchen
  MPoly_Type.thy from package Polynimials
*)

definition Var\<^sub>0 :: "'a \<Rightarrow> ('a \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 'b::{one,zero}" where
  "Var\<^sub>0 n \<equiv> Poly_Mapping.single (Poly_Mapping.single n 1) 1"

text \<open>end of definitions taken from 
 MPoly_Type.thy from package Polynimials\<close>

text \<open>this function is used to prove if a determinant is zero
when we have a corresponding inverse element\<close>

lemma var_not_zero:
  shows "((Var\<^sub>0 n) :: ('a \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 real) \<noteq> 0" unfolding Var\<^sub>0_def 
  by (smt (z3) lookup_single_eq single_zero)


lemma sum_of_values_cancel_out:
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
      then have "a \<noteq> a'" 
        using \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' = f a\<close> by fastforce
      have "card (A - {a, a'}) < card A" 
        by (metis Diff_insert2 \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' \<in> A\<close> card_Diff2_less less.prems(1))
      have " \<forall>x\<in>(A - {a, a'}). f x \<in> (A - {a, a'})" 
        by (metis Diff_iff \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' = f a\<close> empty_iff insert_iff 
            less.prems(2) less.prems(3))
      moreover have  " \<forall>x\<in>(A - {a, a'}). f (f x) = x" 
        by (meson DiffD1 less.prems(3))
      moreover  have " \<forall>x\<in>(A - {a, a'}). val x + val (f x) = 0" 
        by (meson DiffD1 less.prems(4))
      ultimately have "sum val (A - {a, a'}) = 0" 
        using  \<open>card (A - {a, a'}) < card A\<close> less.hyps less.prems(1)

        using less.prems(5) by fastforce
      have "val a + val (f a) = 0" 
        using \<open>a \<in> A \<and> f a \<noteq> a\<close> less.prems(4) by auto
      have "sum val {a, a'} = 0" 
        using \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' = f a\<close> \<open>val a + val (f a) = 0\<close> by force
      have "sum val A = sum val (A - {a, a'}) + sum val {a, a'}" 
        using \<open>a \<noteq> a'\<close> \<open>a \<in> A \<and> f a \<noteq> a\<close> \<open>a' \<in> A\<close>
        by (meson  empty_subsetI insert_subset less.prems(1) sum.subset_diff)
      then show "sum val A = 0" 
        by (simp add: \<open>sum val (A - {a, a'}) = 0\<close> \<open>sum val {a, a'} = 0\<close>)     
    qed
  qed
qed

text \<open>we define a locale so we can ensure the universe is 
finite and corresponds to the vertices of the graph. We need that 
to define a determinant using permutations over that universe.\<close>

locale tutte_matrix =
  fixes E :: "'a::{wellorder,finite} set set"
  assumes graph: "graph_invar E"
  assumes univ: "(UNIV :: 'a set) =  (Vs E)"
begin

text \<open>random orientation of the edges. 
    CURRENTLY THE SEED IS (1, 1). NEEDS TO BE CHANGED.\<close>


definition get_oriented :: "'a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a)" where
  "get_oriented a b = (if fst (Random.range (2::natural) (1, 1)) = 1 then (a, b) else (b, a))"

lemma get_oriented_either_direction:
  shows "get_oriented a b = (a, b) \<or> get_oriented a b = (b, a)"
  by (meson get_oriented_def)

definition oriented_edges :: " ('a \<times> 'a) set"  where 
  "oriented_edges  = {get_oriented a b| a b. {a, b} \<in>  E \<and> a < b}"

lemma univ_is_finite:
  "finite (UNIV :: 'a set)" 
  by (simp add: univ graph)

lemma oriented_edges[elim?]:
  assumes "(a, b) \<in> oriented_edges" 
  shows "{a, b} \<in> E" 
  using assms 
  unfolding oriented_edges_def  
  unfolding get_oriented_def
  by (smt (z3) fst_conv insert_commute mem_Collect_eq prod.sel(2))

lemma one_direction_in_oriented:
  assumes "{a, b} \<in> E"
  shows "(a, b) \<in> oriented_edges \<or> (b, a) \<in> oriented_edges" 
proof -
  have "a \<noteq> b" 
    using assms graph by fastforce
  then show ?thesis  unfolding oriented_edges_def 
    unfolding get_oriented_def 
    by (smt (z3) CollectI assms insert_commute neqE)
qed

text \<open>We define the Tutte matrix. On the rows and columns we have 
the vertices. If we have an edge in the oriented version of the graph, we put 
a variable. If we have an edge in the other direction, we put minus of the variable.
Otherwise we put 0.\<close>

definition tutte_matrix:: "((('a set \<Rightarrow>\<^sub>0 nat) \<Rightarrow>\<^sub>0 real, 'a) vec, 'a) vec" where
  "tutte_matrix = (\<chi> i j. if (i, j) \<in> oriented_edges  
                          then Var\<^sub>0 {i, j}
                          else (if (j, i) \<in> oriented_edges 
                                then - (Var\<^sub>0 {i, j})  
                                else 0))"

lemma in_oriented:
  assumes "(i, j) \<in> oriented_edges"
  shows "tutte_matrix $i$j = Var\<^sub>0 {i, j}" 
  unfolding tutte_matrix_def 
  using assms by fastforce

lemma rev_in_oriented:
  assumes "(j, i) \<in> oriented_edges"
  shows "tutte_matrix $i$j = - (Var\<^sub>0 {i, j})" 
proof -
  have "(i, j) \<notin> oriented_edges" 
    unfolding oriented_edges_def 
    using assms get_oriented_def oriented_edges_def by auto
  then show ?thesis   
    unfolding tutte_matrix_def 
    using assms by fastforce
qed

lemma not_in_edges_tutte_zero:
  assumes "{i, j} \<notin> E"
  shows "tutte_matrix $i$j = 0"
proof -
  have "(i, j) \<notin> oriented_edges" 
    using assms oriented_edges by blast
  have "(j, i) \<notin> oriented_edges" 
    using assms  oriented_edges_def 
    by (metis (mono_tags, lifting) insert_commute oriented_edges)
  show ?thesis  unfolding tutte_matrix_def 
    by (simp add: \<open>(i, j) \<notin> oriented_edges\<close> \<open>(j, i) \<notin> oriented_edges\<close>)
qed

lemma in_edges:
  assumes "{i, j} \<in> E"
  shows "tutte_matrix $i$j \<noteq> 0"
proof(cases "(i, j) \<in> oriented_edges")
  case True
  then show ?thesis using in_oriented 
    by (simp add: var_not_zero)
next
  case False
  have "(j, i) \<in> oriented_edges" 
    using one_direction_in_oriented 
      assms  False by blast
  then show ?thesis 
    by (simp add: rev_in_oriented var_not_zero)
qed

lemma zero_tutte_not_in_oriented:
  assumes "tutte_matrix $i$j = 0"
  shows "(i, j) \<notin> oriented_edges" 
proof
  assume "(i, j) \<in> oriented_edges"
  then have "tutte_matrix $i$j = Var\<^sub>0 {i, j}" 
    using in_oriented assms by blast 
  have "Poly_Mapping.lookup (Var\<^sub>0 {i, j}) ((Poly_Mapping.single {i, j} 1)) \<noteq> (0::real)" 
    by (simp add: Var\<^sub>0_def)
  then show False using assms 
    using \<open>local.tutte_matrix $ i $ j = Var\<^sub>0 {i, j}\<close> by fastforce
qed

lemma tutte_skew_symmetric:
  shows "tutte_matrix $i$j = - tutte_matrix $j$i"
  by (metis (no_types, hide_lams) add.inverse_inverse add.inverse_neutral in_oriented 
      insert_commute not_in_edges_tutte_zero one_direction_in_oriented rev_in_oriented)

lemma zero_then_not_in_edges:
  assumes "tutte_matrix $i$j = 0"
  shows  "{i, j} \<notin> E"
proof -
  have "(i, j) \<notin> oriented_edges" using zero_tutte_not_in_oriented 
    by (simp add: assms)
  moreover have "(j, i) \<notin> oriented_edges" 
    by (metis add.inverse_neutral assms tutte_skew_symmetric 
        zero_tutte_not_in_oriented)
  ultimately show ?thesis 
    using  one_direction_in_oriented by blast
qed

lemma not_in_both_oriented:
  assumes "(j, i) \<notin> oriented_edges"
  assumes "(i, j) \<notin> oriented_edges" 
  shows "{i, j} \<notin> E" 
  using assms one_direction_in_oriented by auto

lemma tutte_matrix_det:
  "det (tutte_matrix) =  sum (\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV :: 'a set))
      {p. p permutes (UNIV :: 'a set)}" 
  using det_def by blast

definition all_perms where 
  "all_perms = {p. p permutes (UNIV :: 'a set)}"

lemma all_perms_elim[elim]:
  assumes "p \<in> all_perms"
  shows "p permutes (UNIV :: 'a set)"
  using assms
  unfolding all_perms_def
  by auto

lemma all_perms_intro[intro]:
  assumes "p permutes (UNIV :: 'a set)"
  shows "p \<in> all_perms"
  unfolding all_perms_def using assms 
  by auto

definition nonzero_perms :: "('a \<Rightarrow> 'a) set "where
  "nonzero_perms  = {p. p permutes (UNIV :: 'a set) \<and> 
         prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV :: 'a set) \<noteq> 0}"

lemma nonzero_perms_elim[elim]:
  assumes "p \<in> nonzero_perms"
  shows "p permutes (UNIV :: 'a set)"  
    "prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV :: 'a set) \<noteq> 0"
  using assms 
  unfolding nonzero_perms_def
   apply blast
  using assms nonzero_perms_def by force

lemma nonzero_perms_intro[intro]:
  assumes "p permutes (UNIV :: 'a set)"
  assumes "prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV :: 'a set) \<noteq> 0"
  shows "p \<in> nonzero_perms" 
  unfolding nonzero_perms_def using assms by auto

text \<open>edges corresponding to the permutation.\<close>

definition u_edges :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a set  set" where
  "u_edges p = {{i, p i}|i. i \<in> (UNIV :: 'a set)}"

lemma u_edges_elim[elim]:
  assumes "e \<in> u_edges p"
  obtains i where "e = {i, p i} \<and>  i \<in> (UNIV :: 'a set)"
  using assms 
  unfolding u_edges_def 
  by blast

lemma u_edges_intro[intro]:
  assumes "i \<in> (UNIV :: 'a set)"
  shows "{i, p i} \<in> u_edges p"
  unfolding u_edges_def 
  by blast

lemma nonzero_perms_nonzero_tutte:
  assumes "p \<in> nonzero_perms"
  shows "\<forall>i. tutte_matrix$i$p i \<noteq> 0"
proof
  fix i
  have "prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV \<noteq> 0"
    using assms nonzero_perms_elim(1) nonzero_perms_elim(2) by blast
  also have "finite (UNIV :: 'a set)" 
    by simp
  ultimately show "(tutte_matrix)$i$p i \<noteq> 0" 
    by (meson UNIV_I prod_zero)
qed

lemma nonzero_edge_in_graph:
  assumes "p \<in> nonzero_perms"
  shows "{i, p i} \<in> E" 
  using assms nonzero_perms_nonzero_tutte 
    not_in_edges_tutte_zero by blast

lemma nonzero_perms_u_edges_in_graph:
  assumes "p \<in> nonzero_perms"
  shows "u_edges p \<subseteq> E"
proof
  fix e
  assume "e \<in> u_edges p"
  then obtain i where "e = {i, (p i)} \<and>  i \<in> (UNIV :: 'a set)" 
    by (meson u_edges_elim)
  then have "{i, (p i)} \<in> E" 
    using assms nonzero_edge_in_graph tutte_matrix_axioms by auto
  then show "e \<in> E" 
    using \<open>e = {i, (p i)} \<and> i \<in> UNIV\<close> by auto
qed

lemma u_edges_finite:
  shows "finite (u_edges p)"
  by simp

lemma u_edges_is_graph:
  assumes "p \<in> nonzero_perms "
  shows "graph_invar (u_edges p)" 
  by (metis assms finite graph insert_Diff insert_subset nonzero_perms_u_edges_in_graph)

lemma p_is_permutation:
  assumes "p permutes (UNIV :: 'a set)"
  shows "permutation p" 
  using assms finite_class.finite_UNIV permutation_permutes by blast

lemma even_circuits_connected_component':
  shows "{(p^^j) i, (p^^(j+1)) i} \<in>  u_edges p" 
  using u_edges_def by auto

lemma nonzero_perms_not_id:
  assumes "p \<in> nonzero_perms"
  shows "p i \<noteq> i" 
proof(rule ccontr)
  assume "\<not> (p i \<noteq> i)"
  then have "p i = i" by auto
  have "{i, i} \<notin> E" 
    using graph by fastforce
  then show False 
    by (metis \<open>p i = i\<close> assms nonzero_edge_in_graph)
qed

lemma edges_construct_a_path:
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
    using Cons.prems  less_diff_conv by auto
  have " {(a # xs) ! 0, (a # xs) ! (0 + 1)} \<in> A" 
    using Cons.prems 
    by (metis Nat.le_diff_conv2 \<open>length (a # xs) - 1 = length xs\<close> add_leD2 length_greater_0_conv
        list.size(3) nat_1_add_1 not_one_le_zero)
  then have "{a, xs!0} \<in> A" 
    by simp
  show ?case
  proof(cases "xs = []")
    case True
    have "a \<in> Vs A" 
      by (meson \<open>{a, xs ! 0} \<in> A\<close> edges_are_Vs) 
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
      have "2 \<le> length xs" 
        using Cons.prems(2) False \<open>length (a # xs) - 1 = length xs\<close> by linarith
      then have "path A xs"
        using Cons.hyps \<open>\<forall>i<length xs-1. {xs ! i, xs ! (i + 1)} \<in> A\<close> 
        by blast
      have "xs = hd xs # tl xs" 
        by (simp add: \<open>xs \<noteq> []\<close>)
      then have "{a, hd xs} \<in> A" 
        by (metis \<open>{a, xs ! 0} \<in> A\<close> nth_Cons_0)
      then show ?thesis 
        by (metis \<open>path A xs\<close> \<open>xs = hd xs # tl xs\<close> path_2) 
    qed
  qed
qed

lemma circuit_is_upath:
  assumes "p permutes (UNIV::'a set)"
  shows "path (u_edges p) (support p i)" 
proof(cases "p i \<noteq> i")
  case True
  let ?xs = "support p i"
  have "\<forall>i < size ?xs-1. {?xs!i, ?xs!(i+1)} \<in> (u_edges p)"
    using even_circuits_connected_component' 
    by auto
  have "p i \<noteq> i" using True by auto
  have "permutation p" 
    by (simp add: assms p_is_permutation) 
  have "(least_power p i) > 1" 
    by (simp add: \<open>p i \<noteq> i\<close> \<open>permutation p\<close> least_power_gt_one)
  then have "size (support p i) \<ge> 2" 
    by simp 
  then show "path (u_edges p) (support p i)" 
    using \<open>\<forall>i < size ?xs-1. {?xs!i, ?xs!(i+1)} \<in> (u_edges p)\<close> 
      edges_construct_a_path by blast
next
  case False
  have "p i = i" 
    using False by auto
  then have "{i, (p i)} \<in> u_edges p" 
    using u_edges_def by auto
  then have "i \<in> Vs (u_edges p)" 
    by (meson edges_are_Vs)
  have "(p^^(Suc 0)) i = i" using `p i = i` 
    by auto
  then have "(p^^1) i = i" 
    by simp
  then have "least_power p i = 1" 
    by (meson least_power_minimal nat_dvd_1_iff_1)
  then show ?thesis 
    by (simp add: \<open>i \<in> Vs (u_edges p)\<close>)
qed 


lemma uedge_in_circuit:
  assumes "Suc j < (least_power p i)" 
  shows "{(support p i)!j, (support p i)!(Suc j)} \<in> u_edges p"
  using assms even_circuits_connected_component' by force

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

lemma el_in_support_represented:
  assumes "permutation p" 
  assumes "x = (p^^j) i" 
  assumes "j < least_power p i" 
  shows "(p^^((least_power p i)-j)) x = i" 
proof -
  have "((inv p)^^j) x= i" 
    by (metis assms(1) assms(2) bij_fn bij_inv_eq_iff inv_fn permutation_bijective)
  have "(least_power p i)-j > 0" 
    using assms(3) zero_less_diff by blast
  have "(p^^(least_power p i)) x = (p^^((least_power p i) + j)) i" 
    by (simp add: assms(2) funpow_add)
  then have "(p^^(((least_power p i)-j)+j)) x = (p^^((least_power p i)+j)) i"
    using `(least_power p i)-j > 0`  
    by simp
  then have "(p^^(((least_power p i)-j))) x = (p^^((least_power p i))) i"
    by (smt (z3) add.commute add_diff_inverse_nat assms(2) assms(3) funpow_add o_apply order.asym)
  then show "(p^^((least_power p i)-j)) x = i" 
    by (simp add: assms least_power_of_permutation(1) p_is_permutation)
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

lemma inv_least_power_same:
  assumes "p permutes (UNIV:: 'a set)"
  shows "least_power p i = least_power (inv p) i" 
proof -
  let ?l = "least_power p i" 
  let ?inv_l = "least_power (inv p) i"
  have "(p^^?l) i = i" 
    by (simp add: assms least_power_of_permutation(1) p_is_permutation)
  have "((inv p)^^(?inv_l)) i = i" 
    by (simp add: assms least_power_of_permutation(1) p_is_permutation permutation_inverse)
  then have "i = (p^^?inv_l) i" 
    by (metis assms bij_fn bij_inv_eq_iff inv_fn permutes_imp_bij)

  show ?thesis
  proof(rule ccontr)
    assume "?l \<noteq> ?inv_l"
    then have "?l < ?inv_l" 
      by (metis \<open>i = (p ^^ least_power (inv p) i) i\<close> assms le_eq_less_or_eq least_power_le least_power_of_permutation(2) p_is_permutation permutation_inverse)

    then show False 
      by (metis \<open>(p ^^ least_power p i) i = i\<close> assms bij_betw_inv_into_left bij_fn bij_is_surj inv_fn leD least_power_le least_power_of_permutation(2) p_is_permutation permutes_imp_bij range_eqI)
  qed
qed


lemma el_in_own_support:
  assumes "p permutes (UNIV :: 'a set)"
  shows "i \<in> set (support p i)" 
proof -
  have "(p^^0) i = i" by simp
  then have "support p i!0 = i" 
    by (simp add: assms least_power_of_permutation(2) p_is_permutation)
  then show ?thesis 
    by (metis assms least_power_of_permutation(2) length_map length_upt nth_mem p_is_permutation zero_less_diff)
qed

lemma p_diff_inv_p_pow:
  assumes "permutation p"
  assumes "n \<ge> k"
  shows "((inv p)^^ k) ((p^^n) i) = (p^^(n-k)) i" 
proof -
  have "(p^^n) i = ((p^^k) \<circ> (p^^(n-k))) i" 
    by (metis add_diff_inverse_nat assms(2) funpow_add not_le)
  then show ?thesis 
    by (metis assms(1) bij_fn bij_inv_eq_iff comp_apply inv_fn permutation_bijective)
qed

lemma inv_support_same:
  assumes "permutation p"
  shows "set (support p i) = set (support (inv p) i)" 
proof(safe)
  let ?len = "least_power p i"  
  have "i \<in> set (support (inv p) i)" 
    using el_in_own_support assms 
    by (smt (z3) least_power_of_permutation(1) map_eq_conv permutation_inverse range_eqI support_set)

  { 
    fix x
    assume "x \<in> set (support p i)"
    then obtain j where "x = (p^^j) i \<and> j < least_power p i" 
      by fastforce
    have "i = ((inv p)^^?len) i" 
      by (metis assms bij_fn bij_inv_eq_iff inv_fn least_power_of_permutation(1) permutation_bijective)


    then have "x = (p^^j) (((inv p)^^?len) i)" 
      using \<open>x = (p ^^ j) i \<and> j < least_power p i\<close> by presburger
    then have "x = ((inv p)^^(?len - j)) i"  
      using p_diff_inv_p_pow[of p j ?len] 
      by (metis \<open>x = (p ^^ j) i \<and> j < least_power p i\<close> assms diff_diff_cancel diff_le_self least_power_of_permutation(1) less_imp_le_nat p_diff_inv_p_pow)

    then show "x \<in>  set (support (inv p) i)" using elemnets_in_support_expo[of "inv p" i i x "?len - j"] 
      using \<open>i \<in> set (support (inv p) i)\<close> assms p_is_permutation permutation_inverse by blast
  }
  fix x
  assume "x \<in>  set (support (inv p) i)"
  then obtain j where "x = ((inv p)^^j) i \<and> j < least_power (inv p) i" 
    by fastforce
  have "i = (p^^?len) i" 
    by (simp add: assms least_power_of_permutation(1) p_is_permutation)

  then have "x = ((inv p)^^j) (((p)^^?len) i)" 
    using \<open>x = ((inv p) ^^ j) i \<and> j < least_power (inv p) i\<close> by presburger
  then have "x = (p^^(?len - j)) i"   using p_diff_inv_p_pow[of "inv p" j ?len] 

    by (smt (z3) \<open>i = (p ^^ least_power p i) i\<close> \<open>x = (inv p ^^ j) i \<and> j < least_power (inv p) i\<close> assms bij_is_surj dual_order.strict_trans funpow_diff inj_iff inv_inv_eq least_power_le least_power_of_permutation(2) not_le p_diff_inv_p_pow permutation_bijective permutation_inverse surj_iff) 



  then show "x \<in>  set (support p i)"  using elemnets_in_support_expo[of "p" i i x "?len - j"] 
    using assms least_power_of_permutation(2) by force
qed

lemma elemnets_in_support_expo':
  fixes n :: "nat"
  assumes "permutation p" 
  assumes "x \<in> set (support p i)"
  assumes "x = (p^^n) y"
  shows "y \<in> set (support p i)"
proof -
  have "permutation (inv p)" 
    using assms(1) permutation_inverse by blast
  have "x \<in>  set (support (inv p) i)" 
    using assms(1) assms(2) inv_support_same by fastforce
  have "((inv p)^^n) x = y" 
    by (metis assms(1) assms(3) bij_fn bij_inv_eq_iff inv_fn permutation_bijective)
  then have "y \<in> set (support (inv p) i)" 
    using \<open>permutation (inv p)\<close> \<open>x \<in> set (support (inv p) i)\<close> elemnets_in_support_expo by fastforce
  then show ?thesis 
    using assms(1) assms(2) inv_support_same by fastforce
qed

thm  Nil_is_map_conv  finite le_zero_eq least_power_of_permutation(2) 
  list.set_sel(1) neq0_conv permutation_permutes upt_eq_Nil_conv

lemma support_is_connected_component:
  assumes "p permutes (UNIV :: 'a set)"
  assumes "C \<in> connected_components (u_edges p)" 
  assumes "i \<in> C"
  shows "set (support p i) = C" (is "set ?l = C")
proof(safe)
  have "hd (support p i) = i" 
    by (simp add: assms(1) hd_conv_nth least_power_of_permutation(2) p_is_permutation)
  moreover have "?l \<noteq> []" 
    by (simp add: assms(1) least_power_of_permutation(2) p_is_permutation)
  ultimately have "i \<in> set ?l" 
    by (metis  hd_in_set) 

  {
    fix x
    assume "x \<in> set ?l" 
    then obtain j where "?l!j = x" 
      by (meson in_set_conv_nth)
    have "path (u_edges p) ?l" 
      using assms(1) circuit_is_upath by blast
    obtain ys zs where "?l = ys @ x # zs" 
      by (metis \<open>x \<in> set ?l\<close> split_list)
    then have "(ys @ [x]) @ zs = ?l" by simp
    then have "path (u_edges p) (ys @ [x])" 
      by (metis \<open>path (u_edges p) ?l\<close> path_pref)
    then have "hd (ys @ [x]) = i" using `hd ?l = i`
      by (metis Nil_is_append_conv \<open>(ys @ [x]) @ zs = ?l\<close> hd_append2 list.distinct(1))
    have "last (ys @ [x]) = x" 
      by simp 
    have "walk_betw (u_edges p) i (ys @ [x]) x" 
      by (simp add: \<open>hd (ys @ [x]) = i\<close> \<open>path (u_edges p) (ys @ [x])\<close> nonempty_path_walk_between)
    then have "x \<in> connected_component (u_edges p) i" 
      by blast
    then show "x \<in> C" 
      by (meson \<open>walk_betw (u_edges p) i (ys @ [x]) x\<close> assms(2) assms(3) in_con_compI)
  }
  fix x 
  assume "x \<in> C"
  obtain xs where "walk_betw (u_edges p) x xs i" 
    by (meson \<open>x \<in> C\<close> assms(2) assms(3) same_con_comp_walk)
  then have "hd xs = x" by auto
  then have "x \<in> set xs" 
    using \<open>walk_betw (u_edges p) x xs i\<close> by force
  have "path (u_edges p) xs" 
    by (meson \<open>walk_betw (u_edges p) x xs i\<close> walk_between_nonempty_path(1))
  have "last xs = i" 
    using \<open>walk_betw (u_edges p) x xs i\<close> by auto
  have "\<forall>y \<in> set xs. \<exists>n. (p^^n) i = y" using `path (u_edges p) xs` `last xs = i`
  proof(induct xs)
    case path0 
    then show ?case by auto
  next
    case (path1 v)
    have "v = i" 
      using path1.prems by auto
    then show ?case 
      by (metis funpow_0 list.set_cases neq_Nil_conv set_ConsD)
  next
    case (path2 v v' vs)
    have "v = p v' \<or> v' = p v" 
      by (metis doubleton_eq_iff path2.hyps(1) u_edges_elim)

    obtain n where "(p^^n) i = v'" 
      using path2.hyps(3) path2.prems by auto
    then have "v' \<in> set (support p i)" 
      using elemnets_in_support_expo[of p i i v' n] 
      using \<open>i \<in> set (support p i)\<close> assms(1) p_is_permutation by blast

    then show ?case 
    proof(cases "v = p v'")
      case True
      have "p ((p^^n) i) = v" 
        by (simp add: True \<open>(p ^^ n) i = v'\<close>)
      then have "(p \<circ> (p^^n)) i = v" by auto
      then have "(p^^(n+1)) i = v" by simp

      then show ?thesis 
        by (metis last_ConsR list.discI path2.hyps(3) path2.prems set_ConsD)
    next
      case False
      have " v' = p v" 
        using False \<open>v = p v' \<or> v' = p v\<close> by auto
      then have "(p^^(1::nat)) v = v'" 
        by (simp add: \<open>(p ^^ n) i = v'\<close>)
      then have "v \<in> set (support p i)"  
        using elemnets_in_support_expo'[of p v' i "(1::nat)" v] 
        using \<open>v' \<in> set (support p i)\<close> assms(1) p_is_permutation by blast
      then obtain j where "v = support p i!j \<and> j < least_power p i" 
        by (smt (verit, best) add.left_neutral atLeastLessThan_iff diff_zero imageE 
            length_upt nth_map nth_upt set_map set_upt)
      then have "(p^^j) i = v" 
        by simp
      then show ?thesis 
        using path2.hyps(3) path2.prems by auto
    qed
  qed
  then obtain n where "(p^^n) i = x" 
    using \<open>x \<in> set xs\<close> by blast
  then show "x \<in> set (support p i)" 
    by (metis \<open>i \<in> set (support p i)\<close> assms(1) elemnets_in_support_expo p_is_permutation)
qed


lemma perm_support_distinct:
  assumes "p permutes (UNIV :: 'a set)"
  shows "distinct (support p i)" 
  by (simp add: assms cycle_of_permutation p_is_permutation)

lemma cycle_vert_is_distict:
  assumes "p permutes (UNIV :: 'a set)"
  shows "distinct (support p i)"
  by (simp add: assms cycle_of_permutation p_is_permutation)

lemma p_in_same_cycle:
  assumes "p permutes (UNIV :: 'a set)"
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
  assumes "p permutes (UNIV :: 'a set)"
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
  assumes "p permutes (UNIV :: 'a set)"
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
  assumes "p permutes (UNIV :: 'a set)"
  shows "Vs (u_edges p) \<subseteq> Vs E" 
  using univ by auto

lemma perm_verts_eq_all:
  assumes "p \<in> nonzero_perms"
  shows "Vs (u_edges p) = Vs E" 
proof - 
  have "Vs (u_edges p) = UNIV" 
    by (smt (verit, ccfv_SIG) insertCI mem_Collect_eq subsetI subset_antisym
        top_greatest tutte_matrix.u_edges_def tutte_matrix_axioms vs_member) 
  then show " Vs (u_edges p) = Vs E" 
    by (simp add: univ)
qed

lemma edges_of_path_component:
 assumes "p \<in> nonzero_perms"
 assumes "C \<in> connected_components (u_edges p)"
 assumes "x \<in> C"
 shows "set (edges_of_path (support p x)) \<subseteq> (component_edges (u_edges p) C)" 
  apply safe
  by (smt (verit, ccfv_SIG) assms circuit_is_upath edges_path_subset_edges 
      map_eq_conv subset_code(1) support_is_connected_component tutte_matrix.nonzero_perms_elim(1)
      tutte_matrix_axioms)


lemma alt_list_matching:
  assumes "M \<subseteq> set (edges_of_path p)"
  assumes "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path p)"
  assumes "distinct p"
  shows "matching M"  using assms(1) assms(2) assms(3)
  proof(induct  arbitrary: M rule: induct_list012 )
    case 1
    have "set (edges_of_path []) = {}" 
      by auto
    then show ?case 
      using "1.prems"(1) matching_def by auto
  next
    case (2 x)
    then show ?case 
      using matching_def by auto
  next
    case (3 x y zs)
    have "edges_of_path (x#y#zs) = {x, y} # edges_of_path (y#zs)" 
      by simp
    have "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) ({x, y} # edges_of_path (y#zs))" 
      using "3.prems"(2) by force
    have "alt_list (\<lambda>e. e \<notin> M) (\<lambda>e. e \<in> M) (edges_of_path (y#zs))"      
      by (metis \<open>alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) ({x, y} # edges_of_path (y # zs))\<close> alt_list_step)
    have "{x, y} \<in> M" 
      by (metis \<open>alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) ({x, y} # edges_of_path (y # zs))\<close> alt_list_step)

    show ?case
    proof(cases "zs = []")
      case True
      have "edges_of_path (y#zs) = []" 
        by (simp add: True)
      then have "M \<subseteq> {{x, y}}" 
        using "3.prems"(1) by auto
then show ?thesis 
  by (metis equals0D insertE matching_def subsetD)
next
  case False
then obtain z ss where "zs = z # ss" 
  by (meson edges_of_path.elims)
 have "edges_of_path (y#z#ss) = {y, z} # edges_of_path (z#ss)" 
   by simp
  then have "(edges_of_path (y#zs)) = {y, z} # edges_of_path zs" 
    by (simp add: \<open>zs = z # ss\<close>)
    have "alt_list (\<lambda>e. e \<in> M) (\<lambda>e. e \<notin> M) (edges_of_path zs)"      
      by (metis \<open>alt_path M (y # zs)\<close> \<open>edges_of_path (y # z # ss) = {y, z} # edges_of_path (z # ss)\<close> \<open>zs = z # ss\<close> alt_list_step)
    have "{x, y} \<notin> set (edges_of_path zs)"
          using "3.prems"(3) v_in_edge_in_path by fastforce
        have "\<forall>e' \<in> set (edges_of_path zs). (\<lambda>e. e \<in> M) e'  \<longrightarrow> (\<lambda>e. e \<in> M - {{x, y}}) e'" 
          using \<open>{x, y} \<notin> set (edges_of_path zs)\<close> by force
        have "\<forall>e' \<in> set (edges_of_path zs). (\<lambda>e. e \<notin> M) e'  \<longrightarrow> (\<lambda>e. e \<notin> M - {{x, y}}) e'" 
          by blast
    then have "alt_list (\<lambda>e. e \<in> M - {{x, y}}) (\<lambda>e. e \<notin> M - {{x, y}}) (edges_of_path zs)"
      using alt_list_cong   
      using \<open>\<forall>e'\<in>set (edges_of_path zs). e' \<in> M \<longrightarrow> e' \<in> M - {{x, y}}\<close> \<open>rev_alt_path M zs\<close> by fastforce
    have " M - {{x, y}} \<subseteq> set (edges_of_path zs)" 
      by (smt (z3) "3.prems"(1) \<open>alt_path M (y # zs)\<close> \<open>edges_of_path (x # y # zs) = {x, y} # edges_of_path (y # zs)\<close> \<open>edges_of_path (y # z # ss) = {y, z} # edges_of_path (z # ss)\<close> \<open>zs = z # ss\<close> \<open>{x, y} \<in> M\<close> alt_list_step insert_commute list.simps(15) subset_insert_iff)
    have "cycle zs" 
      using "3.prems"(3) by auto
    then have "matching (M - {{x, y}})" 
      using "3.hyps"(1) \<open>M - {{x, y}} \<subseteq> set (edges_of_path zs)\<close> \<open>rev_alt_path (M - {{x, y}}) zs\<close> by blast
    have "x \<notin> set zs" 
      using "3.prems"(3) by force
    have "y \<notin> set zs" 
      using "3.prems"(3) by force
    then have "\<forall>e \<in> set (edges_of_path zs). e \<inter> {x, y} = {}" 
      by (metis \<open>x \<notin> set zs\<close> disjoint_insert(2) inf_bot_right v_in_edge_in_path_gen)   
  then show ?thesis 
    by (smt (z3) \<open>M - {{x, y}} \<subseteq> set (edges_of_path zs)\<close> \<open>\<forall>e'\<in>set (edges_of_path zs). e' \<in> M \<longrightarrow> e' \<in> M - {{x, y}}\<close> \<open>matching (M - {{x, y}})\<close> \<open>{x, y} \<in> M\<close> inf_commute insert_iff matching_def subset_eq subset_insert_iff)
qed
  qed


  text \<open>
Every vertex is in the matching:
  1 - We show that every vertex is mapped to one of two consecutive edges

  2 - We show that, out of every two consecutive edges, one is in the matching

  3 - We have that, since the path has an odd number of edges, then the last edges
      is in the matching: alternating_list_odd_last
\<close>
definition consec_edges where 
 "consec_edges e1 e2 es \<equiv> \<exists>es1  es2. es = es1 @ [e1,e2] @ es2"

lemma consec_edges_alternate_pred:
  "\<lbrakk>alt_list P1 P2 (es1 @ [e1,e2] @ es2); \<And>e1. P1 e1 \<longleftrightarrow> \<not> (P2 e1)\<rbrakk> \<Longrightarrow>
   P1 e1 = P2 e2 \<and> P2 e1 = P1 e2"
proof(induction es1 arbitrary: P1 P2 e1 e2)
  case Nil
  then show ?case
    by (auto simp: alt_list_step)
next
  case (Cons e' es1')
  hence "\<And>e1. P2 e1 \<longleftrightarrow> \<not> (P1 e1)"
    by fastforce
  then show ?case
    using Cons
    by (metis alt_list_append_1 alt_list_step)
qed

lemma consec_edges_alternate:
  assumes "alt_list P1 P2 (es1 @ [e1,e2] @ es2)" "\<And>e1. P1 e1 \<longleftrightarrow> \<not> (P2 e1)"
  shows "P1 e1 \<or> P1 e2"
  using assms
proof(induction "(es1 @ [e1,e2] @ es2)" 
      arbitrary: P1 P2 es1 e1 e2 rule: induct_list012)
  case (3 x y zs)
  then show ?case
  proof(cases es1)
    case Nil
    then show ?thesis
      using 3 by (auto simp: alt_list_step)
  next
    case (Cons e' es1')
    moreover hence "\<And>e1. P2 e1 \<longleftrightarrow> \<not> (P1 e1)"
      using \<open>\<And>e1. P1 e1 = (\<not> P2 e1)\<close>
      by fastforce
    ultimately have "P2 e1 \<or> P2 e2"
      apply(intro 3(2)[of es1' _ _ _ P1])
      using 3
      by (auto simp: alt_list_step)
    then show ?thesis
      using consec_edges_alternate_pred[OF \<open>alt_list P1 P2 (es1 @ [e1, e2] @ es2)\<close>]
          \<open>\<And>e1. P1 e1 = (\<not> P2 e1)\<close> 
      by auto
  qed
qed auto

lemma fef'':
  assumes "Suc i < length p"
  assumes "i > 0"
  shows  "\<exists>es1 es2. edges_of_path p = es1 @ [edges_of_path p! (i - 1), edges_of_path p!i] @ es2" 
  using assms
proof -
  let ?ep = "edges_of_path p" 
  have "i < length ?ep" 
    apply (auto simp: edges_of_path_length)
    using assms(1) less_diff_conv by presburger
  moreover then have "?ep = take (i - 1) ?ep @ ?ep ! (i - 1) # drop i ?ep" 
    using id_take_nth_drop[of "i-1" ?ep] 
    by (metis Suc_pred' assms(2) less_imp_diff_less)
  moreover then obtain x xs where "drop i ?ep = x # xs" 
    by (metis Cons_nth_drop_Suc calculation(1))
  moreover then  have "x = ?ep ! i" 
    by (simp add: nth_via_drop)
  moreover have "?ep =  take (i - 1) ?ep  @ [?ep ! (i - 1), x] @ xs"    
    using calculation by force  
  ultimately show ?thesis 
    by blast
qed


lemma fef:
  assumes "Suc i < length p"
  assumes "i > 0"
  obtains es1 es2 where "edges_of_path p = es1 @ [edges_of_path p! (i - 1), edges_of_path p!i] @ es2" 
  using assms fef'' 
  by blast



lemma vertex_in_path_consec_edges:
  assumes "x \<in> set p"
  assumes "x \<noteq> hd p"
  assumes "x \<noteq> last p"
  obtains es1 e1 e2 es2 where 
    "(es1 @ [e1, e2] @ es2) = (edges_of_path p) \<and> x \<in> e1 \<and> x \<in> e2" 
proof - 
  obtain i where "p ! i = x \<and> i < length p" 
    by (meson assms(1) in_set_conv_nth)
  have "Suc i < length p" 
  proof(rule ccontr)
    assume "\<not> Suc i < length p" 
    then have "Suc i \<ge> length p" 
      by (meson not_le)
    then have "i = length p - 1" 
      by (metis Suc_lessI \<open>\<not> Suc i < length p\<close> \<open>p ! i = x \<and> i < length p\<close> diff_Suc_1)
    then show False 
      by (metis \<open>p ! i = x \<and> i < length p\<close> assms(1) assms(3) empty_iff last_conv_nth list.set(1))
  qed
  have "i > 0" 
  proof(rule ccontr)
    assume "\<not> 0 < i"
    then have "i = 0" by auto
    then have "hd p = x" 
      using \<open>p ! i = x \<and> i < length p\<close> hd_conv_nth by auto
    then show False 
      using assms(2) by auto
  qed
  then obtain u w where "{u, x} = edges_of_path p ! (i - 1)" "{x, w} = edges_of_path p ! i"
    using edges_of_path_for_inner `Suc i < length p`
    by (metis \<open>p ! i = x \<and> i < length p\<close>)
  then obtain es1 es2 where "edges_of_path p = es1 @ [{u, x}, {x, w}] @ es2" 
    using fef[of i p]
    by (metis \<open>0 < i\<close> \<open>Suc i < length p\<close>)
  then show ?thesis 
    by (metis insert_iff that)
qed

lemma inner_vertex_in_path_has_pred_edge:
  assumes "x \<in> set p"
  assumes "x \<noteq> hd p"
  assumes "x \<noteq> last p"
  assumes "alt_list P1 P2 (edges_of_path p)" 
  assumes "\<And>e1. P1 e1 \<longleftrightarrow> \<not> (P2 e1)"
  shows "\<exists> e \<in> set (edges_of_path p). x \<in> e \<and> P1 e" 
proof -
  obtain  es1 e1 e2 es2 where 
    "(es1 @ [e1, e2] @ es2) = (edges_of_path p) \<and> x \<in> e1 \<and> x \<in> e2" 
    using assms vertex_in_path_consec_edges[of x p] by blast
  moreover then have "P1 e1 \<or> P1 e2" 
    by (metis assms(4) assms(5) consec_edges_alternate)
  moreover then have "(x \<in> e1 \<and> P1 e1) \<or> (x \<in> e2 \<and> P1 e2)"
    
    by (simp add: calculation(1))
  moreover have "e1 \<in> set (edges_of_path p)"  
    using `(es1 @ [e1, e2] @ es2) = (edges_of_path p) \<and> x \<in> e1 \<and> x \<in> e2`   
    by  (metis append_Cons in_set_conv_decomp)
   moreover have "e2 \<in> set (edges_of_path p)"  
    using `(es1 @ [e1, e2] @ es2) = (edges_of_path p) \<and> x \<in> e1 \<and> x \<in> e2`   
    apply  (auto simp:   in_set_conv_decomp)
    by (metis Cons_eq_append_conv append.assoc append_Cons)
  ultimately  show ?thesis  
    by blast 
qed

lemma head_in_path_has_pred_edge:
  assumes "x = hd p"
  assumes "edges_of_path p \<noteq> []" 
  assumes "alt_list P1 P2 (edges_of_path p)" 
  assumes "\<And>e1. P1 e1 \<longleftrightarrow> \<not> (P2 e1)"
  shows "\<exists> e \<in> set (edges_of_path p). x \<in> e \<and> P1 e"
proof -
  have "x \<in> hd (edges_of_path p)" 
    by (metis Suc_1 Suc_leI assms(1) assms(2) edges_of_path_length hd_v_in_hd_e length_greater_0_conv zero_less_diff)
  have "P1 (hd (edges_of_path p))" 
    by (metis alt_list.cases assms(2-3) list.sel(1))
  then show ?thesis 
    using \<open>x \<in> hd (edges_of_path p)\<close> assms(2) hd_in_set by blast
qed

lemma last_in_path_has_pred_edge:
  assumes "x = last p"
  assumes "even (length p)"
  assumes "p \<noteq> []"  
  assumes "alt_list P1 P2 (edges_of_path p)" 
  assumes "\<And>e1. P1 e1 \<longleftrightarrow> \<not> (P2 e1)"
  shows "\<exists> e \<in> set (edges_of_path p). x \<in> e \<and> P1 e"
proof -
  have "odd (length (edges_of_path p))"
    using edges_of_path_length 
    by (simp add: edges_of_path_length assms(2) assms(3))
  have "x \<in> last (edges_of_path p)"  
    by (metis Suc_1 Suc_leI \<open>odd (length (edges_of_path p))\<close>
        assms(1) edges_of_path_length last_v_in_last_e odd_pos zero_less_diff) 
  have "P1 (last (edges_of_path p))" 
    using alternating_list_odd_last 
    using \<open>odd (length (edges_of_path p))\<close> assms(3) 
    using assms(4) by blast
  then show ?thesis 
    using \<open>x \<in> last (edges_of_path p)\<close> assms(2) last_in_set 
    by (metis \<open>odd (length (edges_of_path p))\<close> length_greater_0_conv odd_pos)
qed

lemma vertex_in_path_has_pred_edge:
  assumes "x \<in> set p"
  assumes "alt_list P1 P2 (edges_of_path p)" 
  assumes "\<And>e1. P1 e1 \<longleftrightarrow> \<not> (P2 e1)"
  assumes "even (length p)"
  assumes "p \<noteq> []" 
  shows "\<exists> e \<in> set (edges_of_path p). x \<in> e \<and> P1 e" 
proof -
  have "edges_of_path p \<noteq> []" 
    by (metis One_nat_def Suc_pred assms(4) assms(5) edges_of_path_length length_greater_0_conv list.size(3) odd_one)
  then show ?thesis 
    by (metis assms head_in_path_has_pred_edge inner_vertex_in_path_has_pred_edge last_in_path_has_pred_edge)
qed

lemma alt_list_split_23:
  assumes "alt_list P1 P2 (l1 @ l2)" "odd (length l1)"
  shows "alt_list P2 P1 l2"
  using assms
  apply(induction l1 rule: induct_list012)
    apply(auto simp: alt_list_empty)
  apply(auto simp:alt_list_step)
  done


lemma fwefqwer: 
  assumes "distinct L" 
  shows "alt_list (\<lambda> e. e \<in> {{L!j, L!Suc j} |j. j \<in> {0..<length L - 1} \<and> even j}) 
         (\<lambda> e. e \<notin> {{L!j, L!Suc j} |j. j \<in> {0..<length L - 1} \<and> even j}) (edges_of_path L)"
  using assms
proof(induct "edges_of_path L" arbitrary: L  rule: induct_list012) 
 
  case 1
  then show ?case 
    using alt_list_empty by auto
next
  case (2 x)
  then show ?case 
    apply(auto simp:alt_list_empty)
    
    by (smt (verit) All_less_Suc One_nat_def Suc_eq_plus1 alt_list_empty alt_list_step edges_of_path_index edges_of_path_length even_zero gr0I list.size(3) list.size(4) nth_Cons_0 zero_less_diff)
    

next
  case (3 e1 e2 zs)
let ?M = "(\<lambda> l. {{l!j, l!Suc j} |j. j \<in> {0..<length l - 1} \<and> even j})"
  have "distinct (edges_of_path L)" 
    by (simp add: distinct_edges_of_vpath "3.prems")
  have "length L \<ge> 3"
    by (metis "3.hyps"(3) Suc_eq_plus1 Suc_leI Suc_lessI add_diff_cancel_right' dual_order.eq_iff edges_of_path_length less_Suc_eq_le list.size(4) numeral_3_eq_3 zero_less_diff zero_order(1))
  then obtain x y z xs where "L = x # y # z # xs" 
    by (metis Suc_le_length_iff numeral_3_eq_3)
  then have "e1 = {x, y}" 
    using "3.hyps"(3) by force
  have "e2 = {y, z}" 
    using "3.hyps"(3) \<open>L = x # y # z # xs\<close> by force
  have "zs = edges_of_path (z # xs)" 
    using "3.hyps"(3) \<open>L = x # y # z # xs\<close> by auto
  have 1: "rev_alt_path (?M (z# xs)) (z # xs)" 
    using "3.hyps"(1)[of "z # xs"]
    using \<open>zs = edges_of_path (z # xs)\<close> 
    using "3.prems" \<open>L = x # y # z # xs\<close> by fastforce 
  have "e2 # zs = edges_of_path (y# z# xs)" 
    by (simp add: \<open>e2 = {y, z}\<close> \<open>zs = edges_of_path (z # xs)\<close>)
  then have "rev_alt_path (?M (y# z# xs)) (y# z# xs)"
    using "3.hyps"(2)[of "y # z # xs"] 
    using "3.prems" \<open>L = x # y # z # xs\<close> by fastforce
  have "edges_of_path (z # xs) = zs"
    by (simp add: \<open>zs = edges_of_path (z # xs)\<close>)
  then have "set zs \<union> {e1, e2}= set (edges_of_path L)"
    
    by (metis "3.hyps"(3) Un_insert_right list.simps(15) sup_bot_right)
  then have "set zs = set (edges_of_path L) - {e1, e2}"
    
    by (metis "3.hyps"(3) Diff_insert2 Diff_insert_absorb \<open>cycle (edges_of_path L)\<close> distinct.simps(2) list.simps(15))

  have "e1 \<in> ?M L"
    
    by (smt (verit, ccfv_SIG) "3.hyps"(3) One_nat_def atLeastLessThan_iff edges_of_path.elims edges_of_path_length even_zero length_greater_0_conv list.distinct(1) mem_Collect_eq not_less_eq_eq not_one_le_zero nth_Cons_0 nth_Cons_Suc)
    have "e2 \<notin> ?M L"
    proof(rule ccontr)
      assume " \<not> e2 \<notin> {{L ! j, L ! Suc j} |j.
             j \<in> {0..<length L - 1} \<and>
             even j} "
      then obtain j where "e2 = {L ! j, L ! Suc j} \<and> j \<in> {0..<length L - 1} \<and>
             even j" 
        by blast
      have "2 < length L" 
        using \<open>3 \<le> length L\<close> by linarith
      have "j < length L" 
        using \<open>e2 = {L ! j, L ! Suc j} \<and> j \<in> {0..<length L - 1} \<and> even j\<close> atLeastLessThan_iff 
        by auto
      
      have "e2 = {L ! 1, L ! 2}" 
        by (simp add: \<open>L = x # y # z # xs\<close> \<open>e2 = {y, z}\<close>)
      then have "L ! 2 = L ! j \<or> L ! 2 = L ! Suc j" 
        
        using \<open>e2 = {L ! j, L ! Suc j} \<and> j \<in> {0..<length L - 1} \<and> even j\<close> by auto
      then have "L ! 2 = L ! j"
        
        using "3.prems" \<open>2 < length L\<close> \<open>e2 = {L ! j, L ! Suc j} \<and> j \<in> {0..<length L - 1} \<and> even j\<close> distinct_conv_nth by fastforce
      then have "2 = j"
 using `distinct L` using nth_eq_iff_index_eq[of L 2 j] 
  using \<open>2 < length L\<close> \<open>j < length L\<close> by fastforce
  then have " L ! 3 = L ! 1" 
    by (metis One_nat_def Suc_1 \<open>e2 = {L ! 1, L ! 2}\<close> \<open>e2 = {L ! j, L ! Suc j} \<and> j \<in> {0..<length L - 1} \<and> even j\<close> doubleton_eq_iff numeral_3_eq_3)
     
  
  then show False 
    using "3.prems" \<open>2 = j\<close> \<open>e2 = {L ! j, L ! Suc j} \<and> j \<in> {0..<length L - 1} \<and> even j\<close> nth_eq_iff_index_eq by fastforce
qed
  have "?M (z # xs) \<union> {e1} = ?M L"
  proof
    show "?M (z # xs) \<union> {e1} \<subseteq> ?M L"
    proof(safe)
      {
        fix a j
        assume "j \<in> {0..<length (z # xs) - 1}"
        assume "even j"
        have "length (z # xs) + 2 = length L" 
          by (simp add: \<open>L = x # y # z # xs\<close>)
        have "(z # xs) ! j =  L ! (j + 2)" 
          by (simp add: \<open>L = x # y # z # xs\<close>)
        have "(z # xs) ! Suc j =  L ! Suc (j + 2)" 
          by (simp add: \<open>L = x # y # z # xs\<close>)
        have "{(z # xs) ! j, (z # xs) ! Suc j} = {L ! (j + 2), L ! Suc (j + 2)} \<and>
                (j + 2) \<in> {0..<length L - 1} \<and> even (j + 2)" 
          by (metis "3.hyps"(3) Suc_less_eq \<open>(z # xs) ! Suc j = L ! Suc (j + 2)\<close> \<open>(z # xs) ! j = L ! (j + 2)\<close> \<open>even j\<close> \<open>j \<in> {0..<length (z # xs) - 1}\<close> \<open>zs = edges_of_path (z # xs)\<close> add_2_eq_Suc' atLeastLessThan_iff dvd_add_triv_right_iff edges_of_path_length length_Cons zero_order(1))
        then show "\<exists>ja. {(z # xs) ! j, (z # xs) ! Suc j} = {L ! ja, L ! Suc ja} \<and>
                ja \<in> {0..<length L - 1} \<and> even ja" 
          by fast
      }
      fix a
      show "\<exists>j. e1 = {L ! j, L ! Suc j} \<and>
             j \<in> {0..<length L - 1} \<and>
             even j" 
        by (metis "3.hyps"(3) One_nat_def \<open>L = x # y # z # xs\<close> \<open>e1 = {x, y}\<close> atLeastLessThan_iff edges_of_path_length even_zero length_Cons less_Suc_eq_0_disj not_less_eq_eq not_one_le_zero nth_Cons_0 nth_Cons_Suc)
    qed
    show "?M L \<subseteq> ?M (z # xs) \<union> {e1}" 
    proof
      fix a
      assume "a \<in> ?M L"
      then obtain j where "a = {L ! j, L ! Suc j} \<and>
        j \<in> {0..<length L - 1} \<and> even j" by auto
      show "a \<in> ?M (z # xs) \<union> {e1}"
      proof(cases "j = 0")
        case True
        have "a = {L ! 0, L ! 1}" 
          by (simp add: True \<open>a = {L ! j, L ! Suc j} \<and> j \<in> {0..<length L - 1} \<and> even j\<close>)
        then have "a = e1" 
          by (simp add: \<open>L = x # y # z # xs\<close> \<open>e1 = {x, y}\<close>)
        then show ?thesis 
          by blast
      next
        case False
        have "j \<ge> 2" 
          by (metis False One_nat_def Suc_1 \<open>a = {L ! j, L ! Suc j} \<and> j \<in> {0..<length L - 1} \<and> even j\<close> atLeastLessThan_iff dual_order.antisym even_Suc even_zero not_less_eq_eq)
        then have "(z # xs) ! (j - 2) =  L ! (j)" 
          
          by (metis False Suc_1 \<open>L = x # y # z # xs\<close> diff_diff_left nat_1_add_1 not_le not_less_eq_eq nth_Cons' nth_Cons_pos zero_less_diff)
        have "(z # xs) ! Suc (j - 2) =  L ! Suc j"
          
          by (metis (full_types) Suc_1 Suc_diff_1 Suc_diff_Suc Suc_le_lessD \<open>2 \<le> j\<close> \<open>L = x # y # z # xs\<close> less_le_trans nth_Cons_Suc pos2)
       
        have "(j - 2) \<in> {0..<length (z # xs) - 1} \<and> even (j - 2)"
          
          by (metis (mono_tags, hide_lams) "3.hyps"(3) One_nat_def Suc_1 Suc_diff_Suc Suc_pred \<open>2 \<le> j\<close> \<open>a = {L ! j, L ! Suc j} \<and> j \<in> {0..<length L - 1} \<and> even j\<close> \<open>zs = edges_of_path (z # xs)\<close> atLeastLessThan_iff bot_nat_0.extremum diff_Suc_1 edges_of_path_length eq_imp_le length_Cons less_Suc_eq less_Suc_eq_0_disj less_eq_dvd_minus less_le_trans minus_nat.diff_0 not_le not_less_eq_eq)
        then have "{(z # xs) ! (j -2), (z # xs) ! Suc (j - 2)} \<in> ?M (z # xs)"
          by blast
        
        then show ?thesis 
          using \<open>(z # xs) ! (j - 2) = L ! j\<close> \<open>(z # xs) ! Suc (j - 2) = L ! Suc j\<close> \<open>a = {L ! j, L ! Suc j} \<and> j \<in> {0..<length L - 1} \<and> even j\<close> by auto

      qed
    qed
  qed

  then have "?M (z # xs) \<subseteq> ?M L"
    by auto

  then have 2:"\<forall>x \<in> set (edges_of_path (z # xs)). (\<lambda> y. y \<in>  (?M (z # xs)))  x \<longrightarrow> (\<lambda> y. y \<in>  (?M L)) x"
    
    using \<open>{{(z # xs) ! j, (z # xs) ! Suc j} |j. j \<in> {0..<length (z # xs) - 1} \<and> even j} \<subseteq> {{L ! j, L ! Suc j} |j. j \<in> {0..<length L - 1} \<and> even j}\<close> by blast
 

  have "\<forall>x \<in> set (edges_of_path (z # xs)). (\<lambda> y. y \<notin>  (?M (z # xs)))  x \<longrightarrow> (\<lambda> y. y \<notin>  (?M L)) x"
  proof
    fix a
    assume "a \<in> set (edges_of_path (z # xs))"
    then have "a \<in> set (edges_of_path (L)) - {e1, e2}" 
      using \<open>set zs = set (edges_of_path L) - {e1, e2}\<close> \<open>zs = edges_of_path (z # xs)\<close> by blast
    show " a \<notin>  (?M (z # xs)) \<longrightarrow> a \<notin>  (?M L)" 
    proof
      assume "a \<notin>  (?M (z # xs))" 
      have "a \<noteq> e1" 
        using \<open>a \<in> set (edges_of_path L) - {e1, e2}\<close> by blast
      then show "a \<notin>  (?M L)" 
        by (metis (no_types, lifting) Un_insert_right \<open>a \<notin> {{(z # xs) ! j, (z # xs) ! Suc j} |j. j \<in> {0..<length (z # xs) - 1} \<and> even j}\<close> \<open>{{(z # xs) ! j, (z # xs) ! Suc j} |j. j \<in> {0..<length (z # xs) - 1} \<and> even j} \<union> {e1} = {{L ! j, L ! Suc j} |j. j \<in> {0..<length L - 1} \<and> even j}\<close> insert_iff sup_bot_right)
    qed
  qed
  then have "rev_alt_path (?M L) (z # xs)" 
    using alt_list_cong[of "(\<lambda> x. x\<in> (?M (z # xs)))" "(\<lambda> x. x \<notin> (?M (z # xs)))"
          "edges_of_path (z # xs)" "(\<lambda> x. x\<in> (?M L))" "(\<lambda> x. x \<notin> (?M L))"] 
    using 1 2 
    by blast

  have "alt_list (\<lambda> x. x\<in> (?M L)) (\<lambda> x. x \<notin> (?M L)) [e1, e2]" 
    
    by (metis (no_types, lifting) \<open>e1 \<in> {{L ! j, L ! Suc j} |j. j \<in> {0..<length L - 1} \<and> even j}\<close> \<open>e2 \<notin> {{L ! j, L ! Suc j} |j. j \<in> {0..<length L - 1} \<and> even j}\<close> alt_list.intros(2) alt_list_empty)

  have "alt_list (\<lambda> x. x\<in> (?M L)) (\<lambda> x. x \<notin> (?M L)) ([e1, e2] @ (edges_of_path (z # xs)))" 
    using alt_list_append_3 
    using \<open>alt_list (\<lambda>x. x \<in> {{L ! j, L ! Suc j} |j. j \<in> {0..<length L - 1} \<and> even j}) (\<lambda>x. x \<notin> {{L ! j, L ! Suc j} |j. j \<in> {0..<length L - 1} \<and> even j}) [e1, e2]\<close> \<open>rev_alt_path {{L ! j, L ! Suc j} |j. j \<in> {0..<length L - 1} \<and> even j} (z # xs)\<close> by fastforce
  then have "alt_list (\<lambda> x. x\<in> (?M L)) (\<lambda> x. x \<notin> (?M L)) (edges_of_path L)"
    
    using "3.hyps"(3) \<open>zs = edges_of_path (z # xs)\<close> by auto
  then show ?case 
    by blast
qed

lemma even_circuit_matching:
  assumes "p \<in> nonzero_perms"
  assumes "C \<in> connected_components (u_edges p)"
  assumes "even (card C)"
  shows "\<exists> M. perfect_matching (component_edges (u_edges p) C) M"
proof -
  have "p permutes (UNIV :: 'a set)" using assms(1) 
    by (simp add: nonzero_perms_elim(1))
  have "even (card C)" using assms(3) by auto
  have "C \<subseteq> Vs (u_edges p)" 
    by (simp add: \<open>C \<in> connected_components (u_edges p)\<close> connected_component_subs_Vs)

  obtain x where "x \<in> C" 
    by (metis \<open>C \<in> connected_components (u_edges p)\<close> connected_comp_nempty ex_in_conv)
  then have "x \<in> Vs (u_edges p)" 
    by (meson \<open>C \<in> connected_components (u_edges p)\<close> connected_comp_verts_in_verts)


  have "set (support p x) = C" 
    using \<open>C \<in> connected_components (u_edges p)\<close>  \<open>x \<in> C\<close> `p permutes (UNIV :: 'a set)` support_is_connected_component by fastforce
  let ?l = "(support p x)"
  let ?m_edges = "{{?l ! j, ?l ! Suc j} |j. j \<in> {0..<length ?l - 1} \<and> even j}"
  let ?p_in = "(\<lambda> e. e \<in> ?m_edges)"
  let ?p_out = "(\<lambda> e. e \<notin> ?m_edges)" 

  have "\<And>e1. ?p_in e1 \<longleftrightarrow> \<not> (?p_out e1)" 
    by blast
   have "even (length ?l)" 
     by (metis (mono_tags, lifting) \<open>p permutes UNIV\<close> \<open>set (support p x) = C\<close> assms(3) distinct_card  perm_support_distinct)
  have  "?l \<noteq> []" 
    using \<open>set (support p x) = C\<close> \<open>x \<in> C\<close> by force
  have "?m_edges \<subseteq> set (edges_of_path ?l)" 
  proof
    fix e
    assume "e \<in> ?m_edges"
    then obtain j where "e = {?l ! j, ?l ! Suc j} \<and>  
        j \<in> {0..<length ?l - 1} \<and> even j" by auto
    then show  "e \<in> set (edges_of_path ?l)" 
      by (metis (no_types, lifting) One_nat_def Suc_less_eq Suc_pred \<open>support p x \<noteq> []\<close> atLeastLessThan_iff edges_of_path_index edges_of_path_length length_greater_0_conv nth_mem) 
  qed
    

  have "distinct (support p x)" 
    by (simp add: \<open>p permutes UNIV\<close> perm_support_distinct)
  have "alt_list ?p_in ?p_out (edges_of_path ?l)" 
    using  fwefqwer[of ?l]  
    using \<open>cycle (support p x)\<close> by blast

  then have "matching  ?m_edges"
    using alt_list_matching[of ?m_edges "(support p x)"]
    using `?m_edges \<subseteq> set (edges_of_path ?l)` 
    using `distinct (support p x)`

  by blast

  have "Vs ?m_edges = set  (support p x)" 
  proof(safe)
    {  fix y
      assume "y \<in> Vs ?m_edges"
      then obtain j where "y \<in> {?l ! j , ?l ! Suc j} \<and>  j \<in> {0..<length ?l - 1} \<and> even j"
        by (smt (verit) mem_Collect_eq vs_member)
      then show "y \<in> set (support p x)"  
        by (smt (z3) One_nat_def Suc_less_eq Suc_pred \<open>support p x \<noteq> []\<close> atLeastLessThan_iff empty_iff insertE length_greater_0_conv less_Suc_eq nth_mem)
    }
    fix y
    assume "y \<in> set ?l"


    then have "\<exists> e \<in> set (edges_of_path ?l). y \<in> e \<and> ?p_in e"
      using vertex_in_path_has_pred_edge[of y ?l ?p_in ?p_out] 
      
      using \<open>even (length ?l)\<close> 
      using \<open>rev_alt_path {{support p x ! j, support p x ! Suc j} |j. j \<in> {0..<length (support p x) - 1} \<and> even j} (support p x)\<close> \<open>support p x \<noteq> []\<close> by blast
       
    then show "y \<in> Vs ?m_edges" 
      by (meson vs_member)
  qed
   then have "Vs ?m_edges = C" 
    using \<open>set (support p x) = C\<close> by fastforce
 
  then have "?m_edges \<subseteq> u_edges p" 
    using tutte_matrix.u_edges_def tutte_matrix_axioms by fastforce

have "?m_edges \<subseteq> (component_edges (u_edges p) C)"
  proof
    fix e
    assume "e \<in> ?m_edges" 
    then have "e \<in> (u_edges p)"         
      using  \<open>?m_edges \<subseteq> u_edges p\<close> by blast
    have "e \<subseteq> C" 
      using \<open>Vs ?m_edges = set (support p x)\<close> \<open>e \<in> ?m_edges\<close> \<open>set (support p x) = C\<close>
        subset_iff vs_member by blast
    then show "e \<in> (component_edges (u_edges p) C)" unfolding component_edges_def
      using \<open>e \<in> u_edges p\<close> by fastforce

  qed
  have "Vs (component_edges (u_edges p) C) = C" 
    using vs_connected_component[of "u_edges p" C]
      `C \<in> connected_components (u_edges p)` 
    by (meson assms(1) tutte_matrix.u_edges_is_graph tutte_matrix_axioms)

  have "graph_invar (component_edges (u_edges p) C)" 
    by (metis (no_types, lifting) Berge.component_edges_subset \<open>C \<subseteq> Vs (u_edges p)\<close> \<open>Vs (component_edges (u_edges p) C) = C\<close> assms(1) finite_subset insert_subset mk_disjoint_insert tutte_matrix.u_edges_is_graph tutte_matrix_axioms)
  then  have " perfect_matching (component_edges (u_edges p) C) ?m_edges"
    unfolding perfect_matching_def 
    using \<open>Vs (component_edges (u_edges p) C) = C\<close> 

    using \<open>Vs {{support p x ! j, support p x ! Suc j} |j. j \<in> {0..<length (support p x) - 1} \<and> even j} = C\<close> \<open>matching {{support p x ! j, support p x ! Suc j} |j. j \<in> {0..<length (support p x) - 1} \<and> even j}\<close> \<open>{{support p x ! j, support p x ! Suc j} |j. j \<in> {0..<length (support p x) - 1} \<and> even j} \<subseteq> component_edges (u_edges p) C\<close>
    by auto


  then show "\<exists> M'. perfect_matching (component_edges (u_edges p) C) M'" 
    by blast

qed


lemma even_circuits_has_perfect_matching:
  assumes "p \<in> nonzero_perms"
  assumes "\<forall>C \<in> connected_components (u_edges p). even (card C) "
  shows "\<exists> M. perfect_matching (u_edges p) M"
proof -
  have "p permutes (UNIV :: 'a set)" using assms(1) 
    using tutte_matrix.nonzero_perms_def tutte_matrix_axioms by auto
  have "finite (u_edges p)" 
    by (simp add: u_edges_finite)
  have "\<forall> C \<in> connected_components (u_edges p). 
        \<exists> M'. perfect_matching (component_edges (u_edges p) C) M'"
    using even_circuit_matching 
    using assms(1) assms(2) by blast
  then  show "\<exists> M. perfect_matching (u_edges p) M" using 
      perfect_matching_union_components[of "u_edges p"] u_edges_is_graph assms(1)
    by blast
qed

definition least_odd :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "least_odd p = (LEAST a. odd (least_power p a))"


definition rev_p :: "('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)" 
  where "rev_p p = (\<lambda> i. if i \<in> set (support p (least_odd p)) then 
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
    using \<open>(p ^^ least_power p i) ((p ^^ n) i) = (p ^^ n) i\<close> 
      \<open>(p ^^ n) i = a \<and> n < least_power p i\<close> 
    by auto
qed

lemma inv_in_support:
  assumes "permutation p"
  assumes "a \<in> set (support p i)"
  shows "(inv p) a \<in> set (support p i)" 
proof  -
  have "permutation (inv p)" 
    using assms(1) permutation_inverse by blast
  have "a \<in> set (support (inv p) i)" 
    using assms(1) assms(2) inv_support_same by fastforce
  have "(inv p) a \<in> set (support (inv p) i)" 
    by (smt (verit, ccfv_SIG) \<open>a \<in> set (support (inv p) i)\<close> \<open>permutation (inv p)\<close> cycle_is_surj 
        cycle_of_permutation cycle_restrict image_iff map_eq_conv)
  then show ?thesis 
    using assms(1) inv_support_same by fastforce
qed

lemma perm_in_support:
  assumes "permutation p"
  assumes "a \<in> set (support p i)"
  shows "p a \<in> set (support p i)"
proof - 
  have "permutation (inv p)" 
    by (simp add: assms(1) permutation_inverse)
  moreover have "a \<in> set (support (inv p) i)" 
    using assms(1) assms(2) inv_support_same by fastforce
  ultimately have "p a \<in> set (support (inv p) i)" 
    using inv_in_support[of "inv p" a i] 
    by (metis  assms(1) inv_inv_eq permutation_bijective)
  then show ?thesis 
    using assms(1) inv_support_same by fastforce
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
    by (metis (no_types, lifting) \<open>inv p a \<in> set (support p i)\<close> assms(1) cycle_is_surj 
        cycle_of_permutation cycle_restrict image_iff map_eq_conv)
  then show False 
    using \<open>p (inv p a) = a\<close> assms(2) by auto
qed

lemma p_rev_p_same:
  assumes "p permutes (UNIV::'a set)"
  assumes "x \<in> set (support p (least_odd p))" 
  shows "p (rev_p p x) = x" 
proof -
  have "(rev_p p x) = (inv p) x" 
    using rev_p_def 
    using assms(2) by presburger
  then show ?thesis 
    by (metis assms(1) permutes_inv_eq)
qed

lemma p_rev_p_same':
  assumes "p permutes (UNIV::'a set)"
  assumes "x \<notin> set (support p (least_odd p))" 
  shows "(rev_p p x) = p x" 
  using assms(2) rev_p_def by presburger


definition on_odd where
  "on_odd p = (\<lambda> x. if x \<in> set (support p (least_odd p)) then p x else x)" 


definition not_on_odd where
  "not_on_odd p = (\<lambda> x. if x \<notin> set (support p (least_odd p)) then p x else x)" 


lemma on_odd_in:
  assumes "x \<in>  set (support p (least_odd p))"
  shows "on_odd p x = p x" 
  unfolding on_odd_def using assms by auto

lemma on_odd_out:
  assumes "x \<notin>  set (support p (least_odd p))"
  shows "on_odd p x = x" 
  unfolding on_odd_def using assms by auto

lemma not_on_odd_in:
  assumes "x \<notin>  set (support p (least_odd p))"
  shows "not_on_odd p x = p x" 
  unfolding not_on_odd_def using assms by auto

lemma not_on_odd_out:
  assumes "x \<in>  set (support p (least_odd p))"
  shows "not_on_odd p x = x" 
  unfolding not_on_odd_def using assms by auto


lemma on_odd_p_permutes:
  assumes "p permutes (UNIV::'a set)"
  shows "(on_odd p) permutes (set (support p (least_odd p)))" 
proof -
  let ?A = "set (support p  (least_odd p))"
  have "(\<forall>x\<in>?A. \<forall>y\<in>?A. (on_odd p) x = (on_odd p) y \<longrightarrow> x = y)"
    apply rule+
    by (metis assms on_odd_def permutes_inv_eq)

  then have "inj_on (on_odd p) ?A" 
    using inj_on_def by blast
  have "(on_odd p) ` ?A = ?A"
    apply safe 
    using assms on_odd_def p_in_same_cycle apply presburger
  proof -
    fix x
    assume "x \<in> ?A" 
    have "(inv p) x \<in> ?A" 
      using \<open>x \<in> ?A\<close> assms inv_in_support p_is_permutation by fastforce
    have "(on_odd p) ((inv p) x) = x" 
      by (metis \<open>inv p x \<in> ?A\<close> assms  on_odd_def permutes_inverses(1))
    then show "x \<in> (on_odd p) ` ?A" 
      by (metis \<open>inv p x \<in> ?A\<close> image_eqI)
  qed
  then have "bij_betw (on_odd p) ?A ?A" 
    unfolding bij_betw_def 
    using \<open>inj_on (on_odd p) ?A\<close> by blast
  have "(\<And>x. x \<notin> ?A \<Longrightarrow> (on_odd p) x = x)" 
    using on_odd_out by presburger
  then show " (on_odd p) permutes ?A" 
    using  Permutations.bij_imp_permutes
    using \<open>bij_betw (on_odd p) ?A ?A\<close> by blast
qed

lemma on_odd_p_permutes_UNIV:
  assumes "p permutes (UNIV::'a set)"
  shows "(on_odd p) permutes UNIV" using on_odd_p_permutes assms 
  by (meson bij_imp_permutes iso_tuple_UNIV_I permutes_bij)

lemma not_on_odd_p_permutes:
  assumes "p permutes (UNIV::'a set)"
  shows "(not_on_odd p) permutes (UNIV::'a set) - (set (support p  (least_odd p)))"
proof -
  let ?A = "(UNIV::'a set) - (set (support p (least_odd p)))"
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
    assume "x \<in>  not_on_odd p ` ?A"  "x \<in>  set (support p (least_odd p)) " 
    have "(inv p x) \<in> set (support p (least_odd p))" 
      using \<open>x \<in> set (support p (least_odd p))\<close> assms inv_in_support p_is_permutation by fastforce
    then have "x \<in> ?A" 
      by (smt (z3) DiffD2 UNIV_I \<open>x \<in> not_on_odd p ` (UNIV - set (support p (least_odd p)))\<close> assms image_iff inv_into_f_f permutes_inj tutte_matrix.not_on_odd_def tutte_matrix_axioms)

    then show False 
      using \<open>x \<in> set (support p (least_odd p))\<close> by force
  qed
  then have "bij_betw (not_on_odd p) ?A ?A" unfolding bij_betw_def 
    using \<open>inj_on (not_on_odd p) ?A\<close> by blast
  have "(\<And>x. x \<notin> ?A \<Longrightarrow> (not_on_odd p) x = x)" 
    using not_on_odd_out 
    by simp
  then show " (not_on_odd p) permutes ?A" using  Permutations.bij_imp_permutes
    using \<open>bij_betw (not_on_odd p) (UNIV - set (support p (least_odd p))) (UNIV - set (support p (least_odd p)))\<close> by blast
qed

lemma not_on_odd_p_permutes_UNIV:
  assumes "p permutes (UNIV::'a set)"
  shows "(not_on_odd p) permutes (UNIV::'a set)"
  using not_on_odd_p_permutes assms 
  using permutes_subset by blast

lemma rev_is_composition:
  assumes "p permutes (UNIV::'a set)"
  shows "rev_p p = ((inv (on_odd  p)) \<circ>  not_on_odd p)"
proof
  let ?A = "(set (support p  (least_odd p)))" 
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


lemma rev_p_permutes:
  assumes "p permutes (UNIV::'a set)"
  shows "(rev_p p) permutes (UNIV::'a set)" 
  using rev_is_composition not_on_odd_p_permutes_UNIV assms 
  by (simp add: on_odd_p_permutes_UNIV permutes_compose permutes_inv)

lemma odd_component_then_odd_circuit:
  assumes "p permutes (UNIV :: 'a set)" 
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C) "
  obtains x where "odd (least_power p x)"
proof -
  obtain C where "C \<in> connected_components (u_edges p) \<and> odd (card C)"
    using assms by blast
  then obtain x where "x \<in> C" 
    by (metis card.empty card.infinite finite_has_maximal odd_card_imp_not_empty)
  then have "x \<in> Vs (u_edges p)" 
    by (meson \<open>C \<in> connected_components (u_edges p) \<and> odd (card C)\<close> connected_comp_verts_in_verts)

  have "C = set (support p x)" using support_is_connected_component[of p C x]  
    using \<open>C \<in> connected_components (u_edges p) \<and> odd (card C)\<close>  \<open>x \<in> C\<close> assms(1) by fastforce
  then have " odd (least_power p x)" 
    by (metis (no_types, lifting) \<open>C \<in> connected_components (u_edges p) \<and> odd (card C)\<close> 
        assms(1) cycle_vert_is_distict diff_zero distinct_card length_map length_upt)
  show ?thesis 
    using \<open>odd (least_power p x)\<close> that by auto
qed



lemma least_odd_is_odd:
  assumes "p permutes (UNIV :: 'a set)" 
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C) "
  shows "odd (least_power p  (least_odd p))" 
proof -
  obtain i where "odd (least_power p i)" using odd_component_then_odd_circuit[of p] assms 
    by blast
  then show ?thesis
    by (metis least_odd_def wellorder_Least_lemma(1))
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
      using True card_1_singletonE 
      by (metis empty_iff insertE)
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


lemma p_is_composition:
  assumes "p permutes (UNIV::'a set)"
  shows "p = on_odd  p \<circ>  not_on_odd p"
proof
  fix x
  let ?A = "(set (support p  (least_odd p)))" 
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
      by (metis (full_types) \<open>not_on_odd p x = p x\<close> assms not_on_odd_def not_on_odd_p_permutes_UNIV
          on_odd_def permutes_univ)

    then show ?thesis 
      by (simp add: \<open>not_on_odd p x = p x\<close>)
  qed
qed

lemma rev_p_opposit_tutte_value:
  assumes "p permutes (UNIV::'a set)"
  assumes "i \<in> set (support p  (least_odd p))"
  shows "(tutte_matrix )$i$p i = - (tutte_matrix )$p i$(rev_p p) (p i)"
proof - 
  have "p i \<in> set (support p  (least_odd p))" 
    by (metis assms on_odd_def on_odd_p_permutes permutes_inv_eq)   
  then have "(rev_p p) (p i) = i"  
    unfolding rev_p_def 
    by (metis assms(1) permutes_inv_eq)
  then show ?thesis 
    using  assms(1) tutte_skew_symmetric 
    by metis
qed

lemma least_odd_support_is_odd:
  assumes "p permutes (UNIV::'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)" 
  shows "odd (card (set (support p (least_odd p))))" 
proof -
  have "card (set (support p (least_odd p))) = least_power p (least_odd p)"
    using \<open>p permutes UNIV\<close> distinct_card perm_support_distinct by force
  then show ?thesis 
    using assms(1) assms(2) least_odd_is_odd by presburger
qed   

lemma rev_product_is_minus:
  assumes "p permutes (UNIV::'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows " prod (\<lambda>i. (tutte_matrix )$i$p i) (UNIV :: 'a set) = 
          -  prod (\<lambda>i. (tutte_matrix)$i$(rev_p p) i) (UNIV :: 'a set)" 
proof -
  let ?A = "set (support p  (least_odd p))"
  let ?h = "(\<lambda>i. (tutte_matrix )$i$p i)" 
  let ?g = "(\<lambda>i. (tutte_matrix )$i$(rev_p p) i)" 

  have 3: "prod ?h UNIV =  prod ?h ?A *  prod ?h (UNIV - ?A)" 
    by (metis (no_types, lifting) mult.commute prod.subset_diff top_greatest univ_is_finite)

  have 4:"prod ?g UNIV =  prod ?g ?A *  prod ?g (UNIV - ?A)"
    by (metis (no_types, lifting) mult.commute prod.subset_diff top_greatest univ_is_finite)

  have "\<forall> i\<in> (UNIV - ?A). (rev_p p) i = p i" 
    using assms p_rev_p_same' by auto
  then have 2:" prod ?h (UNIV  - ?A) =  prod ?g (UNIV - ?A)"    
    by force
  have "odd (card ?A)" 
    using assms(1) assms(2) least_odd_support_is_odd by blast
  have "\<forall> i \<in> ?A. (tutte_matrix )$i$p i = - (tutte_matrix )$p i$(rev_p p) (p i)" 

    by (simp add: assms(1) assms(2) rev_p_opposit_tutte_value)

  then have "\<forall> i \<in> ?A. ?h i = - (?g \<circ> (on_odd p)) i" 
    using tutte_matrix.on_odd_def tutte_matrix_axioms by fastforce
  then have 1: "prod ?h ?A = - prod (?g \<circ> (on_odd p)) ?A"
    using reverse_for_each_product[of ?A ?h ] \<open>odd (card ?A)\<close> 
    by blast


  have " prod ?g ?A =  prod (?g \<circ> (on_odd p)) ?A"
    using  Permutations.comm_monoid_mult_class.prod.permute [of "on_odd p" "?A" ?g] 
    using assms(1) on_odd_p_permutes by presburger
  then have "prod ?h ?A = -  prod ?g ?A " 
    using 1 by presburger
  then show ?thesis
    using 2 3 4 by auto
qed



lemma rev_has_same_parity:
  assumes "p permutes (UNIV::'a set)"
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
  assumes "p permutes (UNIV :: 'a set)" 
  shows "of_int (sign p) = of_int (sign (rev_p p))" 
  by (simp add: assms rev_has_same_parity sign_def)

lemma rev_opposite_value:
  assumes "p permutes (UNIV :: 'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C) " 
  shows "(\<lambda>p. of_int (sign p) * prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV) p = 
 - (\<lambda>p. of_int (sign p) *  prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV) (rev_p p)" 
    (is  " ?g  p = - ?g (rev_p p)")
proof -
  have "of_int (sign p) = of_int (sign (rev_p p))" 
    using assms(1) rev_same_sign by blast
  have " prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV =
  -  prod (\<lambda>i. (tutte_matrix)$i$(rev_p p) i) UNIV"
    using rev_product_is_minus assms   
    by blast
  then show ?thesis 
    by (simp add: \<open>of_int (sign p) = of_int (sign (rev_p p))\<close>)
qed

lemma rev_nonzero_is_nonzero:
  assumes "p \<in> nonzero_perms"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows "rev_p p \<in> nonzero_perms" 
proof -
  have "p permutes UNIV" 
    using assms nonzero_perms_def by auto
  have " prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV \<noteq> 0"
    using assms unfolding nonzero_perms_def  
    by force
  then have " prod (\<lambda>i. (tutte_matrix)$i$(rev_p p) i) UNIV \<noteq> 0"
    by (simp add: \<open>\<exists>C\<in>connected_components (u_edges p). odd (card C)\<close>  rev_product_is_minus \<open>p permutes UNIV\<close> )
  then show "rev_p p \<in> nonzero_perms" unfolding nonzero_perms_def 
    using \<open>p permutes UNIV\<close> rev_p_permutes by force
qed

lemma pow_rev_p_is_inv:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "a \<in> (set (support p  (least_odd p)))" 
  shows "((inv p)^^n) a = ((rev_p p)^^n) a"
proof (induct n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  let ?A = "(set (support p  (least_odd p)))"
  have "permutation p" using assms(1) 
    by (simp add: p_is_permutation)
  then  have same_support: " (set (support p  (least_odd p))) =  (set (support (inv p) (least_odd p)))"
    using  inv_support_same 
    by fastforce
  then have " (inv p) a \<in> (set (support (inv p)  (least_odd p)))" 
    by (smt (z3) \<open>permutation p\<close> assms(2) inv_in_support map_eq_conv)

  then have "((inv p ^^ n) a) \<in> (set (support (inv p)  (least_odd p)))"
    by (metis same_support  assms(1) assms(2) elemnets_in_support_expo p_is_permutation permutation_inverse)
  then have "((inv p ^^ n) a) \<in> (set (support p (least_odd p)))"
    using same_support by blast

  then have "(rev_p p) ((inv p ^^ n) a) = (inv p) ((inv p ^^ n) a)"  
    using rev_p_def by presburger

  then show "(inv p ^^ Suc n) a = (rev_p p ^^ Suc n) a" 
    by (simp add: Suc.hyps)
qed

lemma pow_rev_p_is_same:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "a \<notin> (set (support p  (least_odd p)))" 
  shows "(p^^n) a = ((rev_p p)^^n) a"
proof (induct n)
  case 0
  then show ?case 
    by simp
next
  case (Suc n)
  let ?A = "(set (support p (least_odd p)))" 
  have "permutation p" using assms(1) 
    by (simp add: p_is_permutation)
  then  have "(p^^n) a \<notin>  (set (support p  (least_odd p)))" 
    by (metis assms(2) elemnets_in_support_expo')
  then have "(rev_p p) ((p ^^ n) a) = p ((p ^^ n) a)" 
    using assms(1) p_rev_p_same' 
    by presburger
  then show "(p ^^ Suc n) a = (rev_p p ^^ Suc n) a" 
    by (simp add: Suc.hyps)
qed

lemma rev_p_support_same:
  assumes "p permutes (UNIV:: 'a set)"
  shows "set (support p i) = set (support (rev_p p) i)" 
proof(safe)
  let ?A = "(set (support p  (least_odd p)))" 
  have "i \<in> set (support (rev_p p) i)" 
    using el_in_own_support assms 
    using rev_p_permutes by presburger

  have "i \<in> set (support p  i)" 
    using el_in_own_support assms 
    using rev_p_permutes by presburger

  have "permutation ((rev_p p))" 
    by (simp add: assms p_is_permutation rev_p_permutes) 
  have "permutation p" 
    by (simp add: assms p_is_permutation)
  { 
    fix x
    assume "x \<in> set (support p i)"
    then obtain j where "x = (p^^j) i \<and> j < least_power p i" 
      by fastforce
    then have "((inv p)^^j) x= i" 
      by (metis assms bij_fn bij_inv_eq_iff inv_fn permutes_imp_bij)
    have "(least_power p i)-j > 0" 
      by (simp add: \<open>x = (p ^^ j) i \<and> j < least_power p i\<close>)
    have "(p^^(least_power p i)) x = (p^^((least_power p i) + j)) i" 

      by (simp add: \<open>x = (p ^^ j) i \<and> j < least_power p i\<close> funpow_add)
    then have "(p^^(((least_power p i)-j)+j)) x = (p^^((least_power p i)+j)) i"
      using `(least_power p i)-j > 0`  
      by simp
    then have "(p^^(((least_power p i)-j))) x = (p^^((least_power p i))) i"

      by (metis (no_types, lifting) Nat.add_diff_assoc2 \<open>x = (p ^^ j) i \<and> j < least_power p i\<close> add_diff_cancel_right' funpow_add less_imp_le o_apply)
    then have "(p^^((least_power p i)-j)) x = i" 
      by (simp add: assms least_power_of_permutation(1) p_is_permutation)

    show "x \<in>  set (support (rev_p p) i)" 
    proof(cases "x \<in> ?A")
      case True
      then have "((inv p)^^j) x = ((rev_p p)^^j) x" 
        using assms pow_rev_p_is_inv by presburger
      then have "((rev_p p)^^j) x = i" 
        using \<open>(inv p ^^ j) x = i\<close> by presburger
      then show ?thesis using 
          `i \<in> set (support (rev_p p) i)` 
          elemnets_in_support_expo'[of "(rev_p p)" i i j x] 
        using \<open>permutation (rev_p p)\<close> by fastforce

    next
      case False
      have "(p^^((least_power p i)-j)) x = ((rev_p p)^^((least_power p i)-j)) x" 
        using pow_rev_p_is_same[of p x "(least_power p i)-j"]
        using False assms by blast
      then have "((rev_p p)^^((least_power p i)-j)) x = i" 
        using \<open>(p ^^ (least_power p i - j)) x = i\<close> by presburger
      then show ?thesis using
          `i \<in> set (support (rev_p p) i)` 
          elemnets_in_support_expo'[of "(rev_p p)" i i "(least_power p i - j)" x] 
        using \<open>permutation (rev_p p)\<close> by fastforce
    qed
  }
  let ?lp = "least_power (rev_p p) i" 
  fix x
  assume "x \<in>  set (support (rev_p p) i)"
  then obtain j where j_sup:"x = ((rev_p p)^^j) i \<and> j < least_power (rev_p p) i" 

    by fastforce

  have "?lp-j > 0" 
    by (simp add: j_sup)
  have "((rev_p p)^^?lp) x = ((rev_p p)^^(?lp + j)) i" 

    by (simp add:j_sup funpow_add)
  then have "((rev_p p)^^((?lp-j)+j)) x = ((rev_p p)^^(?lp+j)) i"
    using `?lp-j > 0`  
    by simp
  then have "((rev_p p)^^((?lp-j))) x = ((rev_p p)^^(?lp)) i"

    by (metis (no_types, lifting) Nat.add_diff_assoc2 j_sup add_diff_cancel_right' funpow_add less_imp_le o_apply)
  then have "((rev_p p)^^(?lp-j)) x = i" 
    by (simp add: \<open>permutation (rev_p p)\<close> least_power_of_permutation(1))
  show "x \<in>  set (support p i)" 
  proof(cases "i \<in> ?A")
    case True
    then have "((inv p)^^j) i = ((rev_p p)^^j) i" 
      using assms pow_rev_p_is_inv by presburger
    then have "((inv p)^^j) i = x" 
      using j_sup by presburger
    then have "i = (p^^j) x" 
      by (metis (no_types, lifting) assms bij_fn bij_inv_eq_iff inv_fn permutes_imp_bij)
    then show ?thesis using 
        `i \<in> set (support p  i)` 
        elemnets_in_support_expo'[of p i i j x] assms 
      using p_is_permutation by blast 
  next
    case False
    have "(p^^((least_power p i)-j)) i = ((rev_p p)^^((least_power p i)-j)) i" 
      using pow_rev_p_is_same[of p i "(least_power p i)-j"]
      using False assms by blast
    then have "((rev_p p)^^(?lp-j)) x = i" 
      using \<open>(rev_p p ^^ (least_power (rev_p p) i - j)) x = i\<close> by blast 
    then show ?thesis using
        `i \<in> set (support p i)` 
        elemnets_in_support_expo' `permutation p` 
      by (metis False assms j_sup pow_rev_p_is_same)
  qed
qed

lemma rev_u_edges_same:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows "(u_edges p) = (u_edges (rev_p p))" 
proof(safe)
  let ?A = "(set (support p  (least_odd p)))"
  {
    fix e
    assume "e \<in> (u_edges p)"
    then obtain i where "e = {i, p i}" 
      using u_edges_def by fastforce

    show "e \<in> (u_edges (rev_p p))" 
    proof(cases "i \<in> ?A")
      case True
      then have "p i \<in> ?A" 
        by (smt (verit, best) assms(1) comp_apply map_eq_conv not_on_odd_def on_odd_p_permutes 
            p_is_composition permutes_in_image)

      then have "(rev_p p) (p i) = (inv p) (p i)" 
        using rev_p_def by presburger
      then have "(rev_p p) (p i) = i " 
        by (metis assms(1) permutes_inverses(2))
      have "{(p i), ((rev_p p) (p i))} \<in> (u_edges (rev_p p))"  
        using tutte_matrix.u_edges_def tutte_matrix_axioms by fastforce
      then show ?thesis 
        by (simp add: \<open>e = {i, (p i)}\<close> \<open>rev_p p (p i) = i\<close> insert_commute)
    next
      case False
      then have "(rev_p p) i = p i" 
        using assms(1) p_rev_p_same' by presburger
      have "{i, ((rev_p p) i)} \<in> (u_edges (rev_p p))"  
        using tutte_matrix.u_edges_def tutte_matrix_axioms by fastforce
      then show ?thesis 
        by (simp add: \<open>e = {i, (p i)}\<close> \<open>rev_p p i = p i\<close>)
    qed
  }
  fix e
  assume "e \<in>  u_edges (rev_p p)"
  then obtain i where "e = {i, ((rev_p p) i)}" 
    using u_edges_def by fastforce
  show "e \<in> (u_edges p)" 
  proof(cases "i \<in> ?A")
    case True
    have "(rev_p p) i = (inv p) i"   using True rev_p_def by presburger
    have "{((inv p) i), (p ((inv p) i))} \<in>  u_edges p" 
      using u_edges_def by auto
    then show ?thesis 
      by (metis \<open>e = {i, (rev_p p i)}\<close> \<open>rev_p p i = inv p i\<close> assms(1) doubleton_eq_iff permutes_inv_eq)

  next
    case False
    have "(rev_p p) i = p i" using False 
      using assms(1) p_rev_p_same' by presburger
    then show ?thesis 
      using \<open>e = {i, (rev_p p i)}\<close> u_edges_def by auto
  qed
qed

lemma least_odd_least:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  assumes "odd (least_power p a)"
  shows "(least_odd p) \<le> a" 
  unfolding least_odd_def
  by (metis Least_le  assms(3))


lemma rev_least_odd_same:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows "least_odd p = least_odd (rev_p p)" 
proof -

  have "(rev_p p) permutes  (UNIV:: 'a set)" 
    by (simp add: assms(1) rev_p_permutes)
  have "\<exists>C \<in> connected_components (u_edges (rev_p p)). odd (card C)"

    using assms(1) assms(2) rev_u_edges_same by presburger
  let ?sup = "(\<lambda> p i. (set (support p i)))" 
  let ?A_rev = "(set (support (rev_p p) ((inv f) (least_odd (rev_p p)))))"
  let ?i = "(least_odd p)"
  let ?i_rev = "(least_odd (rev_p p))"
  have "odd (least_power p ?i)"  
    using assms(1) assms(2) least_odd_is_odd by presburger

  have "odd (least_power (rev_p p) ?i_rev)"
    using assms(1) assms(2) least_odd_is_odd 
    by (simp add: \<open>\<exists>C\<in>connected_components (u_edges (rev_p p)). odd (card C)\<close> \<open>rev_p p permutes UNIV\<close>)

  have "?sup p ?i = ?sup (rev_p p) ?i" 
    using assms(1) rev_p_support_same by presburger
  then have "odd (least_power (rev_p p) ?i)" 
    by (smt (verit, best) \<open>odd (least_power p (least_odd p))\<close> \<open>rev_p p permutes UNIV\<close> assms(1) diff_zero distinct_card length_map length_upt map_eq_conv perm_support_distinct)



  have  "?sup p ?i_rev = ?sup (rev_p p) ?i_rev" 
    using assms(1) rev_p_support_same by presburger
  then  have "odd (least_power p ?i_rev)"  
  proof -
    have f1: "\<forall>n. cycle (support p n)"
      using assms(1) perm_support_distinct by blast
    have "card (set (support p (least_odd (rev_p p)))) = least_power (rev_p p) (least_odd (rev_p p))"
      using \<open>rev_p p permutes UNIV\<close> \<open>set (support p (least_odd (rev_p p))) = set (support (rev_p p) (least_odd (rev_p p)))\<close> distinct_card perm_support_distinct by force
    then show ?thesis
      using f1 by (metis (no_types) \<open>odd (least_power (rev_p p) (least_odd (rev_p p)))\<close> diff_zero distinct_card length_map length_upt)
  qed

  have "least_odd p \<le> least_odd (rev_p p)" 
    by (metis \<open>odd (least_power p (least_odd (rev_p p)))\<close> least_odd_def wellorder_Least_lemma(2))
  have "least_odd p \<ge> least_odd (rev_p p)"  
    using \<open>odd (least_power (rev_p p) (least_odd p))\<close> least_odd_def wellorder_Least_lemma(2) by fastforce
  then show ?thesis 
    using \<open>least_odd p \<le> least_odd (rev_p p)\<close> by auto
qed


lemma p_also_not_in_support:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "x \<notin> set (support p i)"
  shows "(p x) \<notin> set (support p i)" 
proof(rule ccontr)
  have "i \<in> set (support p i)" 
    using assms(1) el_in_own_support by blast 
  assume "\<not> p x \<notin> set (support p i)" 
  then have "p x \<in> set (support p i)" by auto
  then have "p x \<in> set (support (inv p) i)" 
    using assms(1) inv_support_same p_is_permutation by fastforce
  then have "(inv p) (p x) \<in> set (support (inv p) i)" 
    using assms(1) inv_in_support inv_support_same p_is_permutation by fastforce
  then have "x \<in> set (support (inv p) i)" 
    by (metis assms(1) permutes_inv_eq)
  then show False 
    using assms(1) assms(2) inv_support_same p_is_permutation by fastforce
qed

lemma rev_rev_same:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "\<exists>C \<in> connected_components (u_edges p). odd (card C)"
  shows "rev_p (rev_p p) = p" 
proof 
  fix x
  let ?A = "(set (support p (least_odd p)))" 
  let ?A' = "(set (support (rev_p p) (least_odd (rev_p p))))" 
  have "?A = ?A'" 
    using assms(1) assms(2) rev_least_odd_same rev_p_support_same by presburger
  have "rev_p p = ((inv (on_odd  p)) \<circ>  not_on_odd p)"

    using assms(1) rev_is_composition by auto
  then have "rev_p (rev_p p) = ((inv (on_odd  (rev_p p))) \<circ>  not_on_odd (rev_p p))"
    using assms(1) rev_is_composition rev_p_permutes by blast
  then have "rev_p (rev_p p) = ((inv (on_odd  ((inv (on_odd  p)) \<circ>  not_on_odd p))) \<circ>  
          not_on_odd ((inv (on_odd  p)) \<circ>  not_on_odd p))" 
    by (simp add: \<open>rev_p p = inv (on_odd p) \<circ> not_on_odd p\<close>)

  show "(rev_p (rev_p p)) x = p x" 
  proof(cases "x \<in> ?A")
    case True
    then have "not_on_odd (rev_p p) x = x" 
      using \<open>set (support p (least_odd p)) = set (support (rev_p p)  (least_odd (rev_p p)))\<close> not_on_odd_out by force
    have "p x \<in> ?A" 
      by (smt (z3) True assms(1) bij_imp_bij_inv bij_is_surj map_eq_conv on_odd_def on_odd_p_permutes_UNIV permutes_imp_bij permutes_inv_inv surj_f_inv_f)

    then have "(on_odd  (rev_p p)) (p x) = (inv p) (p x)"   
      unfolding  on_odd_def
      using \<open>set (support p (least_odd p)) = set (support (rev_p p) (least_odd (rev_p p)))\<close> rev_p_def by fastforce

    then have "(on_odd  (rev_p p)) (p x) = x" 
      by (metis assms(1) permutes_inv_eq) 
    then have "inv ((on_odd  (rev_p p))) x = p x" 
      by (metis assms(1) on_odd_p_permutes_UNIV permutes_inv_eq rev_p_permutes)
    then show "(rev_p (rev_p p)) x = p x" 
      by (simp add: \<open>not_on_odd (rev_p p) x = x\<close> \<open>rev_p (rev_p p) = inv (on_odd (rev_p p)) \<circ> not_on_odd (rev_p p)\<close>)
  next
    case False
    then have "not_on_odd (rev_p p) x = (rev_p p) x" using not_on_odd_in[of x "(rev_p p)"]  
      using \<open>set (support p (least_odd p)) = set (support (rev_p p)  (least_odd (rev_p p)))\<close> by blast 
    have "(rev_p p) x = p x" unfolding rev_p_def 
      using False by presburger
    have "p x \<notin> ?A" using False p_also_not_in_support  
      using assms(1) by presburger

    then  have "(on_odd  (rev_p p)) (p x) = (p x)" 
      by (metis \<open>not_on_odd (rev_p p) x = rev_p p x\<close> \<open>rev_p p x = p x\<close> assms(1) comp_def tutte_matrix.p_is_composition tutte_matrix.rev_p_permutes tutte_matrix_axioms)

    then have "inv (on_odd  (rev_p p)) (p x) = (p x)" 
      by (metis assms(1) on_odd_p_permutes_UNIV permutes_inv_eq rev_p_permutes)
    then show "(rev_p (rev_p p)) x = p x"  
      by (simp add: \<open>not_on_odd (rev_p p) x = rev_p p x\<close> \<open>rev_p (rev_p p) = inv (on_odd (rev_p p)) \<circ> not_on_odd (rev_p p)\<close> \<open>rev_p p x = p x\<close>)
  qed
qed

lemma det_is_sum_nonzero:
  shows "det (tutte_matrix ) = sum (\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix )$i$p i) (UNIV :: 'a set)) nonzero_perms" 
proof -
  let ?g = "(\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix )$i$p i) (UNIV :: 'a set))" 
  have "finite {p. p permutes (UNIV :: 'a set)}" 
    by simp
  then have "{p. p permutes (UNIV :: 'a set)} = 
        {p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0 } \<union> 
            {p. p permutes (UNIV :: 'a set) \<and> ?g p = 0}" by auto
  have " {p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0 } \<inter> 
            {p. p permutes (UNIV :: 'a set) \<and> ?g p = 0} = {}" by auto
  then have "sum ?g {p. p permutes (UNIV :: 'a set)} = 
            sum ?g  {p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0 } + 
            sum ?g  {p. p permutes (UNIV :: 'a set) \<and> ?g p = 0 }"

    by (simp add: \<open>{p. p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix  $ i $ p i) \<noteq> 0} \<inter> {p. p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) = 0} = {}\<close> \<open>finite {p. p permutes UNIV}\<close> \<open>{p. p permutes UNIV} = {p. p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) \<noteq> 0} \<union> {p. p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) = 0}\<close>  sum.union_disjoint)
  have " sum ?g  {p. p permutes (UNIV :: 'a set) \<and> ?g p = 0 } = 0" 
    by auto
  then have "sum ?g {p. p permutes (UNIV :: 'a set)} = 
            sum ?g  {p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0 }"  
    by (simp add: \<open>(\<Sum>p | p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i)) = (\<Sum>p | p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) \<noteq> 0. of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i)) + (\<Sum>p | p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) = 0. of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i))\<close>)

  have "det (tutte_matrix) =  sum ?g {p. p permutes (UNIV :: 'a set)}" 
    using tutte_matrix_det by force
  then have "det (tutte_matrix) = 
     sum ?g {p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0}"
    using \<open>(\<Sum>p | p permutes UNIV. of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i)) = (\<Sum>p | p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) \<noteq> 0. of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix  $ i $ p i))\<close> by presburger

  let ?A = "nonzero_perms"
  have "{p. p permutes (UNIV :: 'a set) \<and> ?g p \<noteq> 0} = ?A" 

  proof(safe)
    {
      fix p
      assume "p permutes (UNIV:: 'a set)" 
      assume " of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix  $ i $ p i) \<noteq> 0"
      then have "(\<Prod>i\<in>UNIV. local.tutte_matrix  $ i $ p i) \<noteq> 0" by force
      then show "p \<in> nonzero_perms " unfolding nonzero_perms_def 
        using \<open>p permutes UNIV\<close> by blast
    }
    {
      fix p
      assume "p \<in>  nonzero_perms"
      then show "p permutes UNIV" 
        by (simp add: nonzero_perms_def)
    }
    fix p
    assume "p \<in>  nonzero_perms" "?g p = 0"
    then have "(\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) \<noteq> 0" 
      unfolding nonzero_perms_def  
      by blast
    have "of_int (sign p) \<noteq> 0" 
      by (simp add: sign_def)
    then have "(\<Prod>i\<in>UNIV. local.tutte_matrix  $ i $ p i) = 0" using `?g p = 0` 
      by (smt (verit, best) Groups.mult_ac(2) mult.right_neutral mult_minus_right neg_equal_0_iff_equal of_int_1 of_int_minus sign_def)

    then show False 
      using \<open>(\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) \<noteq> 0\<close> by blast
  qed
  show ?thesis 
    using \<open>det local.tutte_matrix = (\<Sum>p | p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) \<noteq> 0. of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i))\<close> \<open>{p. p permutes UNIV \<and> of_int (sign p) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ p i) \<noteq> 0} = nonzero_perms\<close> by presburger
qed


lemma zero_det_each_has_odd_circuit:
  assumes "\<forall>p \<in> nonzero_perms. \<exists>C \<in> connected_components (u_edges p). odd (card C) "
  shows "det (tutte_matrix ) = 0"
proof -
  let ?g = "(\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix )$i$p i) (UNIV :: 'a set))" 
  let ?A = "nonzero_perms"
  let ?h = "rev_p"  
  have "finite ?A" 
    by simp
  have "\<forall>a \<in> ?A.  rev_p a \<in> ?A" 
    using assms rev_nonzero_is_nonzero by blast
  have "\<forall>a \<in> ?A. rev_p (rev_p a) = a" 
    by (simp add: assms nonzero_perms_def rev_rev_same)
  have  "\<forall>a \<in> ?A. ?g a + ?g (rev_p a) = 0"
  proof
    fix a
    assume "a \<in> ?A" 
    have "a permutes (UNIV :: 'a set)" 
      using \<open>a \<in> nonzero_perms \<close> nonzero_perms_def by auto
    have " \<exists>C \<in> connected_components (u_edges a). odd (card C)" 
      using assms 
      by (simp add: \<open>a \<in> nonzero_perms \<close>)
    have "?g a = - ?g (rev_p a)" using rev_opposite_value[of a]  
      using \<open>\<exists>C\<in>connected_components (u_edges a). odd (card C)\<close> \<open>a permutes UNIV\<close> by blast
    then show "?g a + ?g (rev_p a) = 0" by simp
  qed
  have "\<forall>a \<in> ?A. a = (rev_p) a \<longrightarrow> ?g a = 0"
  proof
    fix a
    assume "a \<in> ?A" 
    then have "a permutes UNIV" 
      by (simp add: nonzero_perms_def)
    show "a = (rev_p) a \<longrightarrow> ?g a = 0"
    proof
      assume "a = (rev_p) a"
      let ?i = "least_odd a"
      obtain i where "i = (least_odd a)" 
        by auto
      then  have "i \<in> set (support a (least_odd a))"
        using el_in_own_support 
        using \<open>a permutes UNIV\<close> by blast
      then have "a ((rev_p a) i) = i" 
        using \<open>a permutes UNIV\<close> p_rev_p_same by presburger
      then have "a (a i) = i" 
        using \<open>a = rev_p a\<close> by auto
      then have "(a^^2) i = i" 
        by (metis One_nat_def funpow.simps(2) funpow_0 nat_1_add_1 o_apply plus_1_eq_Suc)

      then have "least_power a i \<le> 2" 
        by (simp add: least_power_le)


      have "odd (least_power a i)" 
        using \<open>a \<in> nonzero_perms \<close> \<open>a permutes UNIV\<close> \<open>i = (least_odd a)\<close> assms tutte_matrix.least_odd_is_odd tutte_matrix_axioms by blast
      then have "(least_power a i) = 1" 
        by (smt (z3) \<open>a permutes UNIV\<close> \<open>least_power a i \<le> 2\<close> dbl_simps(3) dbl_simps(5) even_numeral int_ops(2) le_antisym le_eq_less_or_eq least_power_of_permutation(2) less_one neq0_conv numerals(1) of_nat_le_iff of_nat_numeral p_is_permutation)
      then have "(a^^1) i = i" 
        by (metis \<open>a permutes UNIV\<close> least_power_dvd one_dvd p_is_permutation)
      then have "a i = i" 
        by simp
      show "?g a = 0" 
        using \<open>a \<in> nonzero_perms \<close> \<open>a i = i\<close> nonzero_perms_not_id by blast
    qed
  qed
  have "sum ?g ?A = 0" using sum_of_values_cancel_out[of ?A rev_p ?g] 
    using `finite ?A` `\<forall>a \<in> ?A.  rev_p a \<in> ?A` `\<forall>a \<in> ?A. rev_p (rev_p a) = a`
      `\<forall>a \<in> ?A. ?g a + ?g (rev_p a) = 0` `\<forall>a \<in> ?A. a = (rev_p) a \<longrightarrow> ?g a = 0` 
    by blast


  then show ?thesis using det_is_sum_nonzero 
    by presburger
qed



lemma no_perfect_matching_zero_det:
  assumes "\<nexists> M. perfect_matching E M"
  shows "det (tutte_matrix) = 0" 
proof(cases "\<exists> p \<in> nonzero_perms. \<forall>C \<in> connected_components (u_edges p). even (card C)")
  case True
  then obtain p where "p \<in> nonzero_perms \<and> (\<forall>C \<in> connected_components (u_edges p). even (card C))" 
    by auto
  then have "\<exists> M. perfect_matching (u_edges p) M" using even_circuits_has_perfect_matching
    by meson
  then obtain M where " perfect_matching (u_edges p) M" by auto
  have "u_edges p \<subseteq> E" 
    by (simp add: \<open>p \<in> nonzero_perms \<and> (\<forall>C\<in>connected_components (u_edges p). even (card C))\<close> nonzero_perms_u_edges_in_graph)
  have "Vs (u_edges p) = Vs E" 
    by (meson \<open>p \<in> nonzero_perms  \<and> (\<forall>C\<in>connected_components (u_edges p). even (card C))\<close> perm_verts_eq_all)
  then have "perfect_matching E M" unfolding perfect_matching_def  
    by (metis \<open>perfect_matching (u_edges p) M\<close> \<open>u_edges p \<subseteq> E\<close> graph perfect_matching_member subset_trans) 

  then show ?thesis 
    using assms by auto
next
  case False
  then have "\<forall>p \<in> nonzero_perms. \<exists>C \<in> connected_components (u_edges p). odd (card C)" 
    by blast
  then show ?thesis using zero_det_each_has_odd_circuit 
    by blast
qed

definition var_sign where
  "var_sign p = (if (prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV
                then 1
                else -1)" 



lemma product_is_var_product'':
  assumes "p permutes (UNIV::'a set)"
  assumes "finite A" 
  assumes "\<forall>i \<in> A. {i, p i} \<in> E" (* *)
  shows "(prod (\<lambda>i. (tutte_matrix)$i$p i) (A::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) A
    \<or> - (prod (\<lambda>i. (tutte_matrix)$i$p i) A) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) A" using assms(2) assms(3)
proof(induct A)
  case empty
  then show ?case 
    by auto
next
  case (insert a F)
  then show ?case 
  proof(cases "(prod (\<lambda>i. (tutte_matrix)$i$p i) F) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) F")
    case True
    have 1:"(prod (\<lambda>i. (tutte_matrix)$i$p i) (insert a F) =
        (prod (\<lambda>i. (tutte_matrix)$i$p i) F) * (tutte_matrix)$a$p a)" 
      by (simp add: insert.hyps(2))
    have 2: " prod (\<lambda> i. Var\<^sub>0 ({i, p i}))  (insert a F) = 
        prod (\<lambda> i. Var\<^sub>0 ( {i, p i})) F * ( Var\<^sub>0 ( {a, p a}))" 
      by (simp add: insert.hyps(2) mult.commute)
    then show ?thesis
    proof(cases "(a, p a) \<in> oriented_edges")
      case True
      have "(tutte_matrix)$a$p a =  Var\<^sub>0  {a, p a}" 
        by (simp add: True in_oriented)
      then show ?thesis 
        by (smt (z3) "1" "2" insert.hyps(3) insert.prems insert_iff mult_minus_left)
    next
      case False
      then have "(p a, a) \<in> oriented_edges" unfolding oriented_edges_def 

        by (metis (mono_tags, lifting) insert.prems insertCI not_in_both_oriented oriented_edges_def)
      then have  "(tutte_matrix)$a$p a = -  Var\<^sub>0 ({a, p a})" 
        by (simp add: rev_in_oriented)
      then have "(prod (\<lambda>i. (tutte_matrix)$i$p i) (insert a F) = 
        - prod (\<lambda> i.  Var\<^sub>0 ({i, p i}))  (insert a F))" 
        by (simp add: True 1 2)
      then show ?thesis 
        by fastforce
    qed
  next
    case False
    then have "(prod (\<lambda>i. (tutte_matrix)$i$p i) F) = - prod (\<lambda> i.  Var\<^sub>0 ({i, p i})) F"
      by (metis (no_types, lifting) add.inverse_inverse insert.hyps(3) insert.prems insert_iff)
    have 1:"(prod (\<lambda>i. (tutte_matrix)$i$p i) (insert a F) =
        (prod (\<lambda>i. (tutte_matrix)$i$p i) F) * (tutte_matrix)$a$p a)" 
      by (simp add: insert.hyps(2))
    have 2:"prod (\<lambda> i.  Var\<^sub>0 ({i, p i}))  (insert a F) = 
        prod (\<lambda> i.  Var\<^sub>0 ({i, p i})) F * (  Var\<^sub>0 ({a, p a}))" 
      by (simp add: insert.hyps(2) mult.commute)
    then show ?thesis
    proof(cases "(a, p a) \<in> oriented_edges")
      case True
      have "(tutte_matrix)$a$p a =  Var\<^sub>0  {a, p a}" 
        by (simp add: True in_oriented)
      then show ?thesis 
        by (smt (z3) "1" "2" insert.hyps(3) insert.prems insert_iff mult_minus_left)

    next
      case False
      then have "(p a, a) \<in> oriented_edges" unfolding oriented_edges_def 

        by (metis (mono_tags, lifting) insert.prems insertCI not_in_both_oriented oriented_edges_def)
      then have  "(tutte_matrix)$a$p a = -  Var\<^sub>0 ({a, p a})" 
        by (simp add: rev_in_oriented)
      then have "(prod (\<lambda>i. (tutte_matrix)$i$p i) (insert a F) = 
         prod (\<lambda> i.  Var\<^sub>0 ({i, p i}))  (insert a F))" 
        by (simp add: "1" "2" \<open>(\<Prod>i\<in>F. local.tutte_matrix $ i $ p i) = - (\<Prod>i\<in>F. Var\<^sub>0 {i, p i})\<close>)
      then show ?thesis 
        by fastforce
    qed
  qed

qed

(* TODO: 
 clean it out by introduction of new function.*)
lemma product_is_var_product:
  assumes "p \<in> nonzero_perms"
  assumes "finite A" 
  shows "(prod (\<lambda>i. (tutte_matrix)$i$p i) (A::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) A
    \<or> - (prod (\<lambda>i. (tutte_matrix)$i$p i) A) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) A" 
proof -
  have "\<forall>i. {i, p i} \<in> E" using nonzero_edge_in_graph assms(1) by blast
  then show ?thesis using product_is_var_product''[of p A]  
    using assms nonzero_perms_elim(1) by blast
qed


lemma product_is_var_product_sign:
  assumes "p \<in> nonzero_perms"
  shows "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = var_sign p * prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV" 
proof(cases "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV")
  case True
  have "var_sign p = 1" 
    by (meson True var_sign_def)
  then show ?thesis 
    by (simp add: \<open>var_sign p = 1\<close> True)
next
  case False
  have "var_sign p = -1"
    by (meson False var_sign_def)
  have "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = - prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV"
    by (metis (no_types, lifting) \<open>var_sign p = - 1\<close> assms finite_class.finite_UNIV 
        minus_equation_iff one_neq_neg_one  product_is_var_product var_sign_def)
  then show ?thesis 
    by (simp add: \<open>var_sign p = - 1\<close>)
qed

lemma product_Var_mapping:
  assumes "p permutes (UNIV:: 'a set)" 
  assumes "finite A" 
  shows "prod (\<lambda> i. Var\<^sub>0 ({i, p i})) A = 
         Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) A) (1::real)" using assms(2)
proof(induct A)
  case empty
  then show ?case 
    by simp
next
  case (insert x F)
  have 1: "prod (\<lambda> i. Var\<^sub>0 ({i, p i})) (insert x F) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) F * Var\<^sub>0 {x, p x}" 
    by (simp add: insert.hyps(2) mult.commute)
  have 2: "Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) (insert x F)) 1 =
    Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) F + Poly_Mapping.single {x, p x} 1) 1" 
    by (simp add: add.commute insert.hyps(2))
  have " (Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) F) 1) *
   Poly_Mapping.single (Poly_Mapping.single {x, p x} 1) 1 = Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) F +
 Poly_Mapping.single {x, p x} 1) (1::real)"
    by (simp add: mult_single[of "sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) F" 1 "Poly_Mapping.single {x, p x} 1" 1])
  then have "Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) (insert x F)) (1::real) = 
(Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} 1) F) 1) *  Var\<^sub>0 {x, p x}" 
    unfolding Var\<^sub>0_def 
    by (smt (z3) 2)
  then show ?case
    by (simp add:1 insert.hyps(3))
qed 




lemma all_edges_in_E_prod_nonzero:
  assumes "p permutes (UNIV::'a set)"
  assumes "\<forall>i. {i, p i} \<in> E" 
  shows "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) \<noteq> 0"
proof -
  have "finite (UNIV::'a set)" by simp

  have 1:"prod (\<lambda> i. Var\<^sub>0 ({i, p i})) (UNIV::'a set) = 
         Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) (1::real)" 
    using product_Var_mapping[of p UNIV] assms `finite (UNIV::'a set)` 
    by blast
  then have " Poly_Mapping.lookup ( Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) (1::real))
       (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set))  \<noteq> 0" 
    by simp
  then have " Poly_Mapping.single (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV::'a set)) (1::real) 
      \<noteq> 0" 
    by (smt (z3) lookup_zero)
  then have "prod (\<lambda> i. Var\<^sub>0 ({i, p i}) ::(_\<Rightarrow>\<^sub>0 real)) (UNIV::'a set) \<noteq> 0" using 1 
    by presburger

  have "(prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV::'a set)) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV
    \<or> - (prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV) = prod (\<lambda> i. Var\<^sub>0 ({i, p i})) UNIV" 
    using product_is_var_product''[of p UNIV]  
    using assms(1) assms(2) finite_class.finite_UNIV by blast

  then show ?thesis 
    using \<open>(\<Prod>i\<in>UNIV. Var\<^sub>0 {i, p i}) \<noteq> 0\<close> by force
qed



(* we need the g sign function *)
lemma unique_single_sum:
  assumes "finite A"
  assumes "a \<in> A"
  assumes "\<forall>a' \<in> A - {a}.  f a  \<noteq> f a'" 
  assumes "\<forall>a' \<in> A. g a' \<in> {1::int, -1}"
  shows "Poly_Mapping.lookup (sum (\<lambda> b. of_int (sign b) * of_int (g b) *
      (Poly_Mapping.single (f b) (1::real))) A) (f a) \<noteq> 0" using assms
proof(induct A)

  case empty
  then show ?case 
    by auto
next
  case (insert x F)
  let ?m = "(\<lambda> b. of_int (sign b) * of_int(g b) *(Poly_Mapping.single (f b) (1::real)))" 
  have " \<forall>a'\<in>F - {a}. f a \<noteq> f a'" 
    by (meson DiffD1 DiffD2 DiffI insert.prems(2) subsetD subset_insertI)
  then show ?case
  proof(cases "a =x")
    case True
    have "a \<notin> F" 
      by (simp add: True insert.hyps(2))
    have "\<forall>a'\<in>F. g a' \<in> {1::int, - 1}" 
      using insert.prems(3) by blast 
    have "finite F" 
      by (simp add: insert.hyps(1))
    then have "poly_mapping.lookup (\<Sum>b\<in>F. ?m b) (f a) = 0" 
      using  `a \<notin> F` `\<forall>a'\<in>F - {a}. f a \<noteq> f a'` `\<forall>a'\<in>F. g a' \<in> {1::int, - 1}` 
    proof(induct F)
      case empty
      then show ?case by auto
    next
      case (insert t T)
      have "a \<notin> T" 
        using insert.prems by auto
      have " poly_mapping.lookup (\<Sum>b\<in>(insert t T). ?m b) (f a) =  poly_mapping.lookup (\<Sum>b\<in>T. ?m b) (f a) +
      poly_mapping.lookup (?m t) (f a)" 
        by (smt (verit, del_insts) insert.hyps(1) insert.hyps(2) lookup_sum sum.insert)
      have "a \<noteq> t" 
        using insert.prems by auto
      have " \<forall>a'\<in>T - {a}. f a \<noteq> f a'" 
        by (simp add: insert.prems(2))
      then have "f a \<noteq> f t" 
        using insert.prems(1) insert.prems(2) by force
      then have "poly_mapping.lookup (?m t) (f a) = 0" 
        by (metis (no_types, lifting)  lookup_single_not_eq mult.right_neutral mult_of_int_commute mult_single of_int_1 single_of_int)


      then have "poly_mapping.lookup (\<Sum>b\<in>(insert t T). ?m b) (f a) =  poly_mapping.lookup (\<Sum>b\<in>T. ?m b) (f a)"
        using \<open>poly_mapping.lookup (\<Sum>b\<in>insert t T. of_int (sign b) * of_int (g b) * Poly_Mapping.single (f b) 1) (f a) = poly_mapping.lookup (\<Sum>b\<in>T. of_int (sign b) * of_int (g b) * Poly_Mapping.single (f b) 1) (f a) + poly_mapping.lookup (of_int (sign t) * of_int (g t) * Poly_Mapping.single (f t) 1) (f a)\<close> by linarith
      then show ?case 
        using \<open>\<forall>a'\<in>T - {a}. f a \<noteq> f a'\<close> \<open>a \<notin> T\<close>  
        using insert.hyps(3) insert.prems(3) by force

    qed
    have "(\<Sum>b\<in>(insert x F). ?m b) =  (\<Sum>b\<in>F. ?m b) +  ?m x" 
      by (simp add: insert.hyps(1) insert.hyps(2))
    have " poly_mapping.lookup (\<Sum>b\<in>(insert x F). ?m b) (f a) =  poly_mapping.lookup (\<Sum>b\<in>F. ?m b) (f a) +
      poly_mapping.lookup (?m x) (f a)" 
      by (simp add: \<open>(\<Sum>b\<in>insert x F. of_int (sign b) * of_int (g b) * Poly_Mapping.single (f b) 1) = (\<Sum>b\<in>F. of_int (sign b) * of_int (g b) * Poly_Mapping.single (f b) 1) + of_int (sign x) * of_int (g x) * Poly_Mapping.single (f x) 1\<close> lookup_add)
    then have "poly_mapping.lookup (\<Sum>b\<in>(insert x F). ?m b) (f a) = 
       poly_mapping.lookup (?m x) (f a)" 
      using \<open>poly_mapping.lookup (\<Sum>b\<in>F. of_int (sign b) * of_int (g b) * Poly_Mapping.single (f b) 1) (f a) = 0\<close> by linarith


    have "poly_mapping.lookup (Poly_Mapping.single (f a) (int 1)) (f a) \<noteq> 0"
      by simp
    have "g a \<in> {1::int, -1}" using assms(2) assms(4) 
      by auto
    then have "poly_mapping.lookup ( of_int (sign a) * of_int (g a) * (Poly_Mapping.single (f a) (int 1))) (f a) \<noteq> 0"
      using sign_def 
      by (smt (z3) insert_iff lookup_single_eq mult.right_neutral mult_minus_left mult_of_int_commute of_int_1 of_int_minus of_nat_1 single_uminus singletonD)

    then  have "poly_mapping.lookup (?m x) (f a) \<noteq> 0" 
      using True 
      by (smt (z3) \<open>g a \<in> {1, - 1}\<close> insert_iff lambda_one lookup_single_eq mult_minus_left of_int_1 of_int_minus sign_def single_uminus singletonD)

    then show ?thesis 
      using \<open>poly_mapping.lookup (\<Sum>b\<in>insert x F. of_int (sign b) * of_int (g b) * Poly_Mapping.single (f b) 1) (f a) = poly_mapping.lookup (of_int (sign x) * of_int (g x) * Poly_Mapping.single (f x) 1) (f a)\<close> by presburger
  next 
    case False
    then have "a \<in> F" 
      using insert.prems(1) by auto
    then have " poly_mapping.lookup (\<Sum>b\<in>F. ?m b) (f a) \<noteq> 0" 
      using insert.hyps 
      using \<open>\<forall>a'\<in>F - {a}. f a \<noteq> f a'\<close> 
      using insert.prems(3) by blast
    have "(f x ) \<noteq> (f a )" 
      by (metis False insert.prems(1) insert.prems(2) insert_Diff insert_iff)
    have "(\<Sum>b\<in>(insert x F). ?m b) =  (\<Sum>b\<in>F. ?m b) +  ?m x" 
      by (simp add: insert.hyps(1) insert.hyps(2))
    have " poly_mapping.lookup (\<Sum>b\<in>(insert x F). ?m b) (f a) =  poly_mapping.lookup (\<Sum>b\<in>F. ?m b) (f a) +
      poly_mapping.lookup (?m x) (f a)" 
      by (simp add: \<open>(\<Sum>b\<in>insert x F. of_int (sign b) * of_int (g b) * Poly_Mapping.single (f b) 1) = (\<Sum>b\<in>F. of_int (sign b) * of_int (g b) * Poly_Mapping.single (f b) 1) + of_int (sign x) * of_int (g x) * Poly_Mapping.single (f x) 1\<close> lookup_add)
    have " poly_mapping.lookup (?m x) (f a) = 0"

      by (metis (no_types, lifting) \<open>f x \<noteq> f a\<close>  lookup_single_not_eq mult.assoc mult.left_neutral mult_single single_of_int single_one)
    then have "poly_mapping.lookup (\<Sum>b\<in>(insert x F). ?m b) (f a) =  poly_mapping.lookup (\<Sum>b\<in>F. ?m b) (f a)"

      by (simp add: \<open>poly_mapping.lookup (\<Sum>b\<in>insert x F. of_int (sign b) * of_int (g b) * Poly_Mapping.single (f b) 1) (f a) = poly_mapping.lookup (\<Sum>b\<in>F. of_int (sign b) * of_int (g b) * Poly_Mapping.single (f b) 1) (f a) + poly_mapping.lookup (of_int (sign x) * of_int (g x) * Poly_Mapping.single (f x) 1) (f a)\<close>)
    then show ?thesis 
      using \<open>poly_mapping.lookup (\<Sum>b\<in>F. of_int (sign b) * of_int (g b) * Poly_Mapping.single (f b) 1) (f a) \<noteq> 0\<close> by presburger
  qed
qed


lemma el_in_sum_is_nonzero:
  assumes "finite A"
  assumes "a \<in> A"
  shows "Poly_Mapping.lookup (sum (\<lambda> b. 
      (Poly_Mapping.single (f b) (1::nat))) A) (f a) \<noteq> 0" using assms
  by (metis (mono_tags, lifting) lookup_single_eq lookup_sum one_neq_zero sum_eq_0_iff)



lemma monom_is_nonzero_for_unique_p:
  assumes "p \<in> nonzero_perms" 
  assumes "\<forall> p' \<in> nonzero_perms - {p}.  
       (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p i} (1::nat)) \<noteq> 
    (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat))"
  shows "Poly_Mapping.lookup (det tutte_matrix) 
        (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV:: 'a set)) \<noteq> 0"   
proof -
  have "p \<in> nonzero_perms" 
    by (simp add: all_perms_def assms(1))
  have "finite nonzero_perms" 
    by simp
  let ?f = "(\<lambda> p'. (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat)))"
  have "\<forall>a' \<in> nonzero_perms - {p}.  ?f p  \<noteq> ?f a'" 
    using assms(2) by blast
  have 1:"Poly_Mapping.lookup (sum (\<lambda> b. of_int (sign b) * (var_sign b) *
      (Poly_Mapping.single (?f b) (1::real))) nonzero_perms) (?f p) \<noteq> 0" 
    using unique_single_sum[of nonzero_perms p ?f var_sign] `\<forall>a' \<in> nonzero_perms - {p}.  ?f p  \<noteq> ?f a'`
      \<open>finite nonzero_perms\<close> \<open>p \<in> nonzero_perms\<close> 
    by (smt (verit) insert_iff of_int_1 of_int_minus sum.cong var_sign_def)
  have "\<forall>b \<in> nonzero_perms.
      (var_sign b)* (Poly_Mapping.single (?f b) (1::real)) =  
var_sign b * prod (\<lambda> i. Var\<^sub>0 ({i, b i})) UNIV" 
    by (simp add: nonzero_perms_def product_Var_mapping)
  then have " \<forall>b \<in> nonzero_perms.
      (var_sign b)*  (Poly_Mapping.single (?f b) (1::real)) = 
    (prod (\<lambda>i. (tutte_matrix)$i$b i) (UNIV::'a set))"
    using product_is_var_product_sign  
    by simp
  then  have "(sum (\<lambda> b. of_int (sign b) * 
      (prod (\<lambda>i. (tutte_matrix)$i$b i) (UNIV::'a set))) nonzero_perms) =
       (sum (\<lambda> b. of_int (sign b) * (var_sign b) *
      (Poly_Mapping.single (?f b) (1::nat))) nonzero_perms)"

    by (smt (z3) mult.commute mult.right_neutral mult_minus_right of_int_1 of_int_minus of_nat_1 sign_def sum.cong)
  then have "Poly_Mapping.lookup (sum (\<lambda> b. of_int (sign b) * 
      (prod (\<lambda>i. (tutte_matrix)$i$b i) (UNIV::'a set))) nonzero_perms) (?f p) \<noteq> 0"
    using 1  
    by force
  have "det tutte_matrix =
      sum (\<lambda>p. of_int (sign p) *
     prod (\<lambda>i. (tutte_matrix)$i$p i) (UNIV :: 'a set)) nonzero_perms" 
    using det_is_sum_nonzero 
    by blast
  then show "Poly_Mapping.lookup (det tutte_matrix) (?f p) \<noteq> 0"

    using \<open>poly_mapping.lookup (\<Sum>b\<in>nonzero_perms. of_int (sign b) * (\<Prod>i\<in>UNIV. local.tutte_matrix $ i $ b i)) (\<Sum>i\<in>UNIV. Poly_Mapping.single {i, p i} 1) \<noteq> 0\<close> by presburger

qed



lemma u_edges_unique_poly_map:
  assumes "p permutes (UNIV:: 'a set)"
  assumes "p' permutes (UNIV:: 'a set)"
  assumes "u_edges p \<noteq> u_edges p'"
  shows " (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p i} (1::nat)) \<noteq> 
    (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat))" 
proof -
  have "finite (UNIV::'a set)" by simp
  show ?thesis

  proof(cases "u_edges p - u_edges p' \<noteq> {}")
    case True
    obtain e where "e \<in> u_edges p - u_edges p'" 
      using True by blast
    then obtain a where "e = {a, p a} \<and> a \<in> (UNIV:: 'a set)" 
      using u_edges_def by auto
    have "e \<notin> u_edges p'" 
      using \<open>e \<in> u_edges p - u_edges p'\<close> by auto


    have "Poly_Mapping.lookup (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p i} (1::nat)) 
          e \<noteq> 0"  using el_in_sum_is_nonzero[of "(UNIV:: 'a set)" a "\<lambda> j. {j, p j}"] 
      using \<open>e = {a, p a} \<and> a \<in> UNIV\<close> finite_class.finite_UNIV by blast 

    have "Poly_Mapping.lookup (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat)) 
          e = 0" using lookup_single_eq lookup_sum 
      by (smt (verit, best) \<open>e \<notin> u_edges p'\<close> lookup_single_not_eq mem_Collect_eq sum_eq_0_iff u_edges_def univ_is_finite)


    then show ?thesis 
      using \<open>poly_mapping.lookup (\<Sum>i\<in>UNIV. Poly_Mapping.single {i, p i} 1) e \<noteq> 0\<close> by fastforce
  next
    case False
    have "u_edges p' - u_edges p \<noteq> {}" 
      using False assms(3) by blast
    then obtain e where "e \<in> u_edges p' - u_edges p" 
      by blast
    then obtain a where "e = {a, p' a} \<and> a \<in> (UNIV:: 'a set)" 
      using u_edges_def by auto
    have "e \<notin> u_edges p" 
      using \<open>e \<in> u_edges p' - u_edges p\<close> by auto


    have "Poly_Mapping.lookup (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat)) 
          e \<noteq> 0"  using el_in_sum_is_nonzero[of "(UNIV:: 'a set)" a "\<lambda> j. {j, p' j}"] 
      using \<open>e = {a, p' a} \<and> a \<in> UNIV\<close> finite_class.finite_UNIV by blast 

    have "Poly_Mapping.lookup (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p i} (1::nat)) 
          e = 0" using lookup_single_eq lookup_sum 
      by (smt (verit, best) \<open>e \<notin> u_edges p\<close> lookup_single_not_eq mem_Collect_eq sum_eq_0_iff u_edges_def univ_is_finite)


    then show ?thesis 
      using \<open>poly_mapping.lookup (\<Sum>i\<in>UNIV. Poly_Mapping.single {i, p' i} 1) e \<noteq> 0\<close> by fastforce
  qed
qed

lemma monom_is_nonzero_for_unique_edges:
  assumes "p \<in> nonzero_perms" 
  assumes "\<forall> p' \<in> nonzero_perms - {p}.   u_edges p \<noteq> u_edges p'"
  shows " det tutte_matrix  \<noteq> 0"
proof -
  have "p permutes (UNIV::'a set)" using assms(1) 
    using nonzero_perms_def by auto
  have "\<forall> p' \<in> nonzero_perms - {p}.  
       (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p i} (1::nat)) \<noteq> 
    (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat))"
  proof
    fix p'
    assume "p' \<in> nonzero_perms - {p}" 
    then have "p' permutes UNIV" 
      by (simp add: nonzero_perms_def)
    have "u_edges p \<noteq> u_edges p'" 
      using \<open>p' \<in> nonzero_perms - {p}\<close> assms(2) by blast
    then show " (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p i} (1::nat)) \<noteq> 
    (\<Sum>i\<in>(UNIV:: 'a set). Poly_Mapping.single {i, p' i} (1::nat))" 
      using \<open>p permutes UNIV\<close> \<open>p' permutes UNIV\<close> u_edges_unique_poly_map by presburger
  qed
  then have "Poly_Mapping.lookup (det tutte_matrix) 
        (sum (\<lambda> i. Poly_Mapping.single {i, p i} (1::nat)) (UNIV:: 'a set)) \<noteq> 0" 
    using assms(1) monom_is_nonzero_for_unique_p by blast
  then show ?thesis 
    by fastforce
qed



lemma wqewqe2:
  assumes "p permutes (UNIV::'a set)"
  assumes "u_edges p \<subseteq> E"
  shows "p \<in> nonzero_perms" 
proof -
  have "\<forall>i. {i, (p i)} \<in> E" using assms(2) unfolding u_edges_def
    by blast
  then have "\<forall>i. (i, (p i)) \<in> oriented_edges \<or> ((p i), i) \<in> oriented_edges"
    using not_in_both_oriented by blast

  then have "prod (\<lambda>i. (tutte_matrix)$i$p i) UNIV \<noteq> 0" 
    using all_edges_in_E_prod_nonzero[of p] 
    using \<open>\<forall>i. {i, p i} \<in> E\<close> assms(1) by fastforce
  then show "p \<in> nonzero_perms" unfolding nonzero_perms_def 
    using assms(1) by blast
qed



lemma perfect_matching_nonzero_det:
  assumes "\<exists> M. perfect_matching E M"
  shows "det (tutte_matrix) \<noteq> 0"
proof -
  obtain M where "perfect_matching E M" using assms 
    by blast
  then have "matching M" 
    by auto
  have "Vs M = UNIV" 
    by (metis \<open>perfect_matching E M\<close> perfect_matching_member univ)
  have "graph_invar M" 
    by (metis \<open>perfect_matching E M\<close> insert_subset mk_disjoint_insert perfect_matching_member)
  let ?singletons = "(\<lambda> i. {e - {i}| e. e \<in> M \<and> i \<in> e})" 
  have "\<forall> i \<in> Vs M. is_singleton (?singletons i)"
  proof
    fix i
    assume "i \<in> Vs M" 
    have "\<exists>!e.  e \<in> M \<and> i \<in> e" 
      by (metis \<open>i \<in> Vs M\<close> \<open>matching M\<close> matching_def2)
    then obtain e where "e \<in> M \<and> i \<in> e" by auto
    then have "{e . e \<in> M \<and> i \<in> e} =  {e}" 
      using \<open>\<exists>!e. e \<in> M \<and> i \<in> e\<close> by blast
    then have " (?singletons i) = {e - {i}}" by blast
    then show "is_singleton (?singletons i)" 
      by simp
  qed
  then have "\<forall> i. is_singleton (?singletons i)" 
    by (simp add: \<open>Vs M = UNIV\<close>)
  have "\<forall> i \<in> Vs M. is_singleton (\<Union>{e - {i} |e. e \<in> M \<and> i \<in> e})" 
  proof
    fix i
    assume "i \<in> Vs M" 
    have "\<exists>!e.  e \<in> M \<and> i \<in> e" 
      by (metis \<open>i \<in> Vs M\<close> \<open>matching M\<close> matching_def2)
    then obtain e where "e \<in> M \<and> i \<in> e" by auto
    then have "{e . e \<in> M \<and> i \<in> e} =  {e}" 
      using \<open>\<exists>!e. e \<in> M \<and> i \<in> e\<close> by blast
    then have "{e - {i} |e. e \<in> M \<and> i \<in> e} = {e - {i}}" by blast
    then obtain j where "e = {i, j}" using `graph_invar M` 

      by (smt (verit, best) Diff_insert_absorb \<open>e \<in> M \<and> i \<in> e\<close> insert_Diff insert_Diff_if singleton_insert_inj_eq)
    then have "{e - {i} |e. e \<in> M \<and> i \<in> e} = {{j}}" 

      using \<open>e \<in> M \<and> i \<in> e\<close> \<open>graph_invar M\<close> \<open>{e - {i} |e. e \<in> M \<and> i \<in> e} = {e - {i}}\<close> doubleton_eq_iff singletonD by force
    then show "is_singleton (\<Union>{e - {i} |e. e \<in> M \<and> i \<in> e})" 
      by simp
  qed
  then have "\<forall> i. is_singleton (\<Union>{e - {i} |e. e \<in> M \<and> i \<in> e})" 
    by (simp add: \<open>Vs M = UNIV\<close>)


  let ?f = "\<lambda> i. the_elem (\<Union> (?singletons i))"

  have "?f permutes (UNIV::'a set)" 
  proof -
    have "bij_betw ?f UNIV UNIV"
      unfolding bij_betw_def
    proof
      show "inj_on ?f UNIV" 
      proof
        fix x y
        assume " x \<in> (UNIV::'a set)" " y \<in> (UNIV::'a set)"
        assume "?f x = ?f y"
        then obtain a where "?f x = a" 
          by blast
        have "is_singleton (\<Union>{e - {x} |e. e \<in> M \<and> x \<in> e})" 
          using `\<forall> i. is_singleton (\<Union>{e - {i} |e. e \<in> M \<and> i \<in> e})` 
          by blast

        then have "\<Union>{e - {x} |e. e \<in> M \<and> x \<in> e} = {a}" 
          by (metis (no_types, lifting)  \<open>?f x = a\<close> is_singleton_the_elem)
        have "is_singleton {e - {x} |e. e \<in> M \<and> x \<in> e}" 
          using `\<forall> i. is_singleton (?singletons i)` by auto
        then have "{a} \<in> {e - {x} |e. e \<in> M \<and> x \<in> e}" 
          by (metis (no_types, lifting) \<open>\<Union> {e - {x} |e. e \<in> M \<and> x \<in> e} = {a}\<close> ccpo_Sup_singleton is_singleton_the_elem singletonI)
        then have "{x, a} \<in> M" 
          using \<open>{a} \<in> {e - {x} |e. e \<in> M \<and> x \<in> e}\<close> insert_Diff by force


        have "is_singleton (\<Union>{e - {y} |e. e \<in> M \<and> y \<in> e})" 
          using `\<forall> i. is_singleton (\<Union>{e - {i} |e. e \<in> M \<and> i \<in> e})` 
          by blast

        then have "\<Union>{e - {y} |e. e \<in> M \<and> y \<in> e} = {a}" using `?f x = ?f y` 
          by (metis (no_types, lifting)  \<open>?f x = a\<close> is_singleton_the_elem)
        have "is_singleton {e - {y} |e. e \<in> M \<and> y \<in> e}" 
          using `\<forall> i. is_singleton (?singletons i)` by auto
        then have "{a} \<in> {e - {y} |e. e \<in> M \<and> y \<in> e}" 
          by (metis (no_types, lifting) \<open>\<Union> {e - {y} |e. e \<in> M \<and> y \<in> e} = {a}\<close> ccpo_Sup_singleton is_singleton_the_elem singletonI)


        then have "{y, a} \<in> M" 
          using \<open>{a} \<in> {e - {y} |e. e \<in> M \<and> y \<in> e}\<close> insert_Diff by force
        then show "x = y" using `matching M` 
          by (metis \<open>{x, a} \<in> M\<close> doubleton_eq_iff insertCI matching_unique_match)
      qed
      show "?f ` UNIV = UNIV"
        apply safe

        apply blast
      proof -
        fix x
        assume "x \<in> (UNIV :: 'a set)"

        obtain e where "x \<in> e \<and> e \<in> M" 
          by (metis \<open>Vs M = UNIV\<close> \<open>matching M\<close> \<open>x \<in> UNIV\<close> matching_def2)
        then obtain y where "e = {x, y}" 
          using \<open>graph_invar M\<close> by fastforce
        then have "y \<in> e \<and> e \<in> M" 
          using \<open>x \<in> e \<and> e \<in> M\<close> by fastforce
        then have "y \<in> Vs M" 
          by (simp add: \<open>Vs M = UNIV\<close>)
        have "\<exists>!e.  e \<in> M \<and> y \<in> e" 
          by (metis \<open>y \<in> Vs M\<close> \<open>matching M\<close> matching_def2)
        then have "{e . e \<in> M \<and> y \<in> e} =  {e}" 
          using \<open>\<exists>!e. e \<in> M \<and> y \<in> e\<close>  `y \<in> e \<and> e \<in> M` 
          by blast
        then have "{e - {y} |e. e \<in> M \<and> y \<in> e} = {e - {y}}" by blast
        then have "{e - {y} |e. e \<in> M \<and> y \<in> e} = {{x}}" 
          using \<open>e = {x, y}\<close> \<open>graph_invar M\<close> \<open>y \<in> e \<and> e \<in> M\<close> by force

        then have "?f y = x" by simp
        then show "x \<in> range ?f" 
          by blast
      qed
    qed
    then show "?f permutes UNIV" 
      using bij_imp_permutes by blast
  qed
  have "u_edges ?f = M"
  proof(safe)
    {
      fix e
      assume "e \<in> u_edges ?f" 
      then obtain a where "e = {a, ?f a}" unfolding u_edges_def 
        by blast
      then obtain b where "b = ?f a" 
        by presburger
      have "is_singleton (\<Union>{e - {a} |e. e \<in> M \<and> a \<in> e})" 
        using `\<forall> i. is_singleton (\<Union>{e - {i} |e. e \<in> M \<and> i \<in> e})` 
        by blast

      then have "\<Union>{e - {a} |e. e \<in> M \<and> a \<in> e} = {b}" 
        by (metis (no_types, lifting)  \<open>b = ?f a\<close> is_singleton_the_elem)
      have "is_singleton {e - {a} |e. e \<in> M \<and> a \<in> e}" 
        using `\<forall> i. is_singleton (?singletons i)` by auto
      then have "{b} \<in> {e - {a} |e. e \<in> M \<and> a \<in> e}" 
        by (metis (no_types, lifting) \<open>\<Union> {e - {a} |e. e \<in> M \<and> a \<in> e} = {b}\<close> ccpo_Sup_singleton is_singleton_the_elem singletonI)
      then have "{a, b} \<in> M" 
        using  insert_Diff 
        by (smt (verit, del_insts) insert_commute mem_Collect_eq)

      then show "e \<in> M" 
        by (simp add: \<open>b = the_elem (\<Union> {e - {a} |e. e \<in> M \<and> a \<in> e})\<close> \<open>e = {a, the_elem (\<Union> {e - {a} |e. e \<in> M \<and> a \<in> e})}\<close>) 
    }

    fix e
    assume "e \<in> M"
    then obtain a b where "e = {a, b}" 
      by (meson \<open>graph_invar M\<close>)
    then have "{b} \<in> {e - {a} |e. e \<in> M \<and> a \<in> e}" 
      by (smt (verit, ccfv_SIG) Diff_insert_absorb \<open>e \<in> M\<close> \<open>graph_invar M\<close> insertCI insert_absorb mem_Collect_eq singleton_insert_inj_eq)
    have "is_singleton {e - {a} |e. e \<in> M \<and> a \<in> e}" 
      using `\<forall> i. is_singleton (?singletons i)` by auto

    then have "\<Union>{e - {a} |e. e \<in> M \<and> a \<in> e} = {b}" 
      by (metis (no_types, lifting) \<open>{b} \<in> {e - {a} |e. e \<in> M \<and> a \<in> e}\<close> ccpo_Sup_singleton is_singleton_def singletonD)
    then have "?f a = b" 
      by simp   
    have "{a, ?f a} \<in> u_edges ?f" unfolding u_edges_def by blast 

    then show "e \<in> u_edges ?f" 
      using \<open>e = {a, b}\<close> \<open>the_elem (\<Union> {e - {a} |e. e \<in> M \<and> a \<in> e}) = b\<close> by fastforce
  qed

  have "?f \<in> nonzero_perms" using wqewqe2[of ?f] 
    using \<open>(\<lambda>i. the_elem (\<Union> {e - {i} |e. e \<in> M \<and> i \<in> e})) permutes UNIV\<close> \<open>perfect_matching E M\<close> \<open>u_edges (\<lambda>i. the_elem (\<Union> {e - {i} |e. e \<in> M \<and> i \<in> e})) = M\<close> perfect_matching_def by blast

  have "\<forall> p' \<in> nonzero_perms - {?f}.   u_edges ?f \<noteq> u_edges p'"
  proof
    fix p
    assume "p \<in> nonzero_perms - {?f}"
    show "u_edges ?f \<noteq> u_edges p" 
    proof(rule ccontr)
      assume "\<not> u_edges ?f \<noteq> u_edges p"
      then have "u_edges ?f = u_edges p" by auto

      have "\<forall>x. ?f x = p x" 
      proof
        fix x
        have "\<exists>!e. e \<in> M \<and> x \<in> e" 
          by (metis UNIV_I \<open>Vs M = UNIV\<close> \<open>matching M\<close> matching_def2)
        then have "\<exists>!e. e \<in> u_edges ?f \<and> x \<in> e" 
          using \<open>u_edges (\<lambda>i. the_elem (\<Union> {e - {i} |e. e \<in> M \<and> i \<in> e})) = M\<close> by presburger
        then have "\<exists>!e. e \<in> u_edges p \<and> x \<in> e" 
          by (simp add: \<open>u_edges (\<lambda>i. the_elem (\<Union> {e - {i} |e. e \<in> M \<and> i \<in> e})) = u_edges p\<close>)
        obtain e where "e \<in> M \<and> x \<in> e" 
          using \<open>\<exists>!e. e \<in> M \<and> x \<in> e\<close> by auto
        have "{x, ?f x} \<in> u_edges ?f" unfolding u_edges_def by blast 
        have "{x, p x} \<in> u_edges p" unfolding u_edges_def by blast
        then have "{x, ?f x} = {x, p x}" 
          using \<open>\<exists>!e. e \<in> u_edges p \<and> x \<in> e\<close> \<open>u_edges (\<lambda>i. the_elem (\<Union> {e - {i} |e. e \<in> M \<and> i \<in> e})) = u_edges p\<close> \<open>{x, the_elem (\<Union> {e - {x} |e. e \<in> M \<and> x \<in> e})} \<in> u_edges (\<lambda>i. the_elem (\<Union> {e - {i} |e. e \<in> M \<and> i \<in> e}))\<close> by blast
        then show "?f x = p x" 
          by (metis (no_types, lifting) doubleton_eq_iff)
      qed
      then have "?f = p"by auto 
      then show False 
        using \<open>p \<in> nonzero_perms - {\<lambda>i. the_elem (\<Union> {e - {i} |e. e \<in> M \<and> i \<in> e})}\<close> by fastforce
    qed
  qed
  then show ?thesis using monom_is_nonzero_for_unique_edges[of ?f] 
    using \<open>(\<lambda>i. the_elem (\<Union> {e - {i} |e. e \<in> M \<and> i \<in> e})) \<in> nonzero_perms\<close> by blast
qed

lemma perfect_matching_iff_nonzero_det:
  shows "(\<exists> M. perfect_matching E M) \<longleftrightarrow> det (tutte_matrix) \<noteq> 0"
  using no_perfect_matching_zero_det tutte_matrix.perfect_matching_nonzero_det 
    tutte_matrix_axioms by blast


end