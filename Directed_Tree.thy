theory Directed_Tree
  imports
    "Graph_Theory.Graph_Theory"
    "Graph_Theory_Batteries" "LCA"
begin

section \<open>Directed tree\<close>

text \<open>
The following locale defines the notion of a rooted directed tree. The tree property is
established by asserting a unique walk from the root to each vertex. Note that we need
@{const pre_digraph.awalk} and not @{const pre_digraph.apath} here since we want to have only one
incoming arc for each vertex. In the locale all the usual properties of trees are established, e.g.
non-existence of @{const pre_digraph.cycle}, absence of loops with @{locale loopfree_digraph} and
multi-arcs with @{locale nomulti_digraph}.
We also prove the admissibility of an induction rule for finite trees which constructs any tree
inductively by starting with a single node (the root) and consecutively adding leaves.
\<close>

locale directed_tree = wf_digraph T for T +
  fixes root :: 'a
  assumes
    root_in_verts: "root \<in> verts T" and
    unique_awalk: "v \<in> verts T \<Longrightarrow> \<exists>!p. awalk root p v"

locale fin_directed_tree = directed_tree T root + fin_digraph T for T root

subsection \<open>General properties of trees\<close>

context directed_tree
begin

lemma reachable_from_root: "v \<in> verts T \<Longrightarrow> root \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v"
  using unique_awalk reachable_awalkI by blast

lemma non_empty: "verts T \<noteq> {}"
  using root_in_verts by blast

theorem nexists_cycle: "\<nexists>c. cycle c"
proof
  assume "\<exists>c. cycle c"
  then obtain c where c: "cycle c" by blast
  from unique_awalk[of "awhd root c", OF awhd_in_verts[OF root_in_verts, of c]]
  obtain p where p: "awalk root p (awhd root c)"
    using c[unfolded cycle_conv] unfolding awalk_conv by auto
  from c p awalk_appendI have "awalk root (p@c) (awhd root c)"
    by (metis awalkE' cycle_def awalk_verts_ne_eq)
  with unique_awalk p c show "False"
    using awalk_last_in_verts unfolding cycle_def by blast
qed

lemma apath_if_awalk: "awalk r p v \<Longrightarrow> apath r p v"
  unfolding apath_def
  using awalk_cyc_decompE' closed_w_imp_cycle nexists_cycle by blast

lemma distinct_awalk_verts:
  "awalk u p v \<Longrightarrow> distinct (awalk_verts u p)"
  using apath_if_awalk unfolding apath_def by blast

lemma not_reachable1_if_flip_reachable1:
  "x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y \<Longrightarrow> \<not> y \<rightarrow>\<^sup>+\<^bsub>T\<^esub> x"
proof
  assume "x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> y" "y \<rightarrow>\<^sup>+\<^bsub>T\<^esub> x"
  then obtain p where "p \<noteq> []" "awalk x p x"
    by (meson reachable1_awalk trancl_trans)
  with nexists_cycle show False
    unfolding cycle_def
    by (meson apath_ends apath_if_awalk)
qed

lemma not_in_awalk_verts_if_dominated:
  "\<lbrakk> u \<rightarrow>\<^bsub>T\<^esub> v; awalk r p u \<rbrakk> \<Longrightarrow> v \<notin> set (awalk_verts r p)"
  using awalk_verts_reachable_to not_reachable1_if_flip_reachable1
  by blast

sublocale loopfree: loopfree_digraph T
proof(standard, rule ccontr)
  fix e assume arc: "e \<in> arcs T" and loop: "\<not> tail T e \<noteq> head T e"
  then have "cycle [e]"
    unfolding cycle_conv
    using arc_implies_awalk by force
  with nexists_cycle show "False" by blast
qed

sublocale nomulti: nomulti_digraph T
proof(standard, rule ccontr, goal_cases)
  case (1 e1 e2)
  let ?u = "tail T e1" and ?v = "head T e1"
  from unique_awalk obtain p where "awalk root p ?u"
    using 1 tail_in_verts by blast
  with 1 have "awalk root (p@[e1]) ?v" and "awalk root (p@[e2]) ?v"
    unfolding arc_to_ends_def
    using arc_implies_awalk by (fastforce)+

  with unique_awalk show "False"
    using \<open>e1 \<noteq> e2\<close> by blast
qed


lemma connected': "\<lbrakk> u \<in> verts T; v \<in> verts T \<rbrakk> \<Longrightarrow> u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric T\<^esub> v"
proof -
  let ?T' = "mk_symmetric T"
  fix u v assume "u \<in> verts T" and "v \<in> verts T"
  then have "\<exists>up. awalk root up u" and "\<exists>vp. awalk root vp v"
    using unique_awalk by blast+
  then obtain up vp where up: "awalk root up u" and vp: "awalk root vp v" by blast
  then have "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric T\<^esub> root" and "root \<rightarrow>\<^sup>*\<^bsub>mk_symmetric T\<^esub> v"
    by (meson reachable_awalkI reachable_mk_symmetricI
        symmetric_mk_symmetric symmetric_reachable)+
  then show "u \<rightarrow>\<^sup>*\<^bsub>mk_symmetric T\<^esub> v"
    by (meson wellformed_mk_symmetric wf_digraph.reachable_trans wf_digraph_wp_iff)
qed

theorem connected: "connected T"
  unfolding connected_def strongly_connected_def
  using connected' root_in_verts by auto

lemma unique_awalk_All: "\<exists>p. awalk u p v \<Longrightarrow> \<exists>!p. awalk u p v"
proof(rule ccontr)
  assume "\<exists>p. awalk u p v" "\<nexists>!p. awalk u p v"
  then have "\<exists>p q. awalk u p v \<and> awalk u q v \<and> p \<noteq> q"
    by blast
  then obtain p q where
    p: "awalk u p v" and q: "awalk u q v" and "p \<noteq> q" by blast
  from unique_awalk obtain w where w: "awalk root w u"
    using \<open>awalk u p v\<close> by blast
  then have "awalk root (w@p) v" and "awalk root (w@q) v" and "(w@p) \<noteq> (w@q)"
    using \<open>awalk u p v\<close> \<open>awalk u q v\<close> \<open>p \<noteq> q\<close> awalk_appendI by auto
  with unique_awalk show False by blast
qed

lemma unique_arc:
  shows "u \<rightarrow>\<^bsub>T\<^esub> v \<Longrightarrow> \<exists>!e \<in> arcs T. tail T e = u \<and> head T e = v"
    and "(\<nexists>e. e \<in> arcs T \<and> tail T e = u \<and> head T e = v) \<Longrightarrow> \<not> u \<rightarrow>\<^bsub>T\<^esub> v"
  using unique_awalk_All nomulti.no_multi_arcs unfolding arc_to_ends_def
  by auto

lemma unique_arc_set:
  fixes u v
  defines "A \<equiv> {e \<in> arcs T. tail T e = u \<and> head T e = v}"
  shows "A = {} \<or> (\<exists>e. A = {e})"
proof(cases "u \<rightarrow>\<^bsub>T\<^esub> v")
  case True
  note unique_arc(1)[OF True]
  then show ?thesis unfolding A_def by blast
next
  case False
  then have "\<nexists>e. e \<in> arcs T \<and> tail T e = u \<and> head T e = v"
    using in_arcs_imp_in_arcs_ends arcs_ends_def by blast
  then show ?thesis unfolding A_def by auto
qed

lemma sp_eq_awalk_cost: "awalk a p b \<Longrightarrow> awalk_cost w p = \<mu> w a b"
proof -
  assume "awalk a p b"
  with unique_awalk_All have "{p. awalk a p b} = {p}"
    by blast
  then show ?thesis unfolding \<mu>_def
    by (metis cInf_singleton image_empty image_insert)
qed

lemma sp_cost_finite: "awalk a p b \<Longrightarrow> \<mu> w a b > -\<infinity> \<and> \<mu> w a b < \<infinity>"
  using sp_eq_awalk_cost[symmetric] by simp

theorem sp_append_if_awalk:
  "\<lbrakk> awalk a p b; awalk b q c \<rbrakk> \<Longrightarrow> \<mu> w a c = \<mu> w a b + \<mu> w b c"
proof -
  assume p: "awalk a p b" and q: "awalk b q c"
  then have p_q: "awalk a (p@q) c" by auto
  then have "awalk_cost w (p@q) = awalk_cost w p + awalk_cost w q"
    using awalk_cost_append by blast

  with p q p_q show ?thesis using sp_eq_awalk_cost
    by (metis plus_ereal.simps(1))
qed

lemma sp_append_if_reachable:
  "\<lbrakk> v1 \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v2; v2 \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v3 \<rbrakk> \<Longrightarrow> \<mu> w v1 v3 = \<mu> w v1 v2 + \<mu> w v2 v3"
  using reachable_awalk sp_append_if_awalk by auto

theorem connected_minimal: "e \<in> arcs T \<Longrightarrow>  \<not> (tail T e) \<rightarrow>\<^sup>*\<^bsub>(del_arc e)\<^esub> (head T e)"
proof
  let ?T' = "del_arc e" and ?u = "tail T e" and ?v = "head T e"
  assume "e \<in> arcs T" and "?u \<rightarrow>\<^sup>*\<^bsub>?T'\<^esub> ?v"
  note e = this
  then have T'_wf: "wf_digraph ?T'" by blast

  from e have "awalk ?u [e] ?v"
    by (simp add: arc_implies_awalk)
  moreover
  note wf_digraph.reachable_awalk[OF T'_wf, of ?u ?v]
  with e obtain p where p: "pre_digraph.awalk ?T' ?u p ?v" by blast

  from e have "e \<notin> arcs ?T'" by simp
  with e p have "e \<notin> set p" by (meson T'_wf subsetCE wf_digraph.awalkE')
  with p have "[e] \<noteq> p" and "awalk ?u p ?v"
    by (auto simp: subgraph_awalk_imp_awalk subgraph_del_arc)

  ultimately show False using unique_awalk_All by blast
qed

lemma All_arcs_in_path: "e \<in> arcs T \<Longrightarrow> \<exists>p u v. awalk u p v \<and> e \<in> set p"
  by (meson arc_implies_awalk list.set_intros(1))

end

subsection \<open>Theorems about \<^term>\<open>pre_digraph.leaf\<close>\<close>

lemma (in fin_directed_tree) ex_leaf: "\<exists>v \<in> verts T. leaf v"
proof(rule ccontr, unfold bex_simps)
  assume no_leaves: "\<forall>x\<in>verts T. \<not> leaf x"
  then have "\<forall>x \<in> verts T. \<exists>e. e \<in> out_arcs T x"
    unfolding leaf_def by (simp add: out_arcs_def)
  then have "\<forall>x \<in> verts T. \<exists>x' e. awalk x [e] x'"
    unfolding out_arcs_def using arc_implies_awalk by force
  then have extend: "\<exists>p v'. awalk u (ps@[p]) v'" if "awalk u ps v" for u ps v
    using that by force
  have "\<exists>u p v. awalk u p v \<and> length p = n" for n
  proof(induction n)
    case 0
    from root_in_verts have "awalk root [] root"
      by (simp add: awalk_Nil_iff)
    then show ?case by blast
  next
    case (Suc n)
    then obtain u p v where "awalk u p v" and "length p = n" by blast
    from extend[OF this(1)] obtain e v' where "awalk u (p@[e]) v'" and "length (p@[e]) = Suc n"
      using length_append_singleton \<open>length p = n\<close> by auto
    then show ?case by blast
  qed
  with not_distinct_awalk_verts[OF finite_verts] have "\<exists>p. cycle p"
    using awalk_cyc_decompE' closed_w_imp_cycle by (metis order_refl)
  with nexists_cycle show False by blast
qed

context directed_tree
begin

lemma leaf_not_mem_awalk_verts:
  "\<lbrakk> leaf x; awalk u p v; v \<noteq> x \<rbrakk> \<Longrightarrow> x \<notin> set (awalk_verts u p)"
proof(induction p arbitrary: u)
  case Nil
  then have "u = v" unfolding awalk_conv by simp
  with Nil show ?case by auto
next
  case (Cons a p)
  then have "x \<notin> set (awalk_verts (head T a) p)" by (simp add: awalk_Cons_iff)
  moreover
  from Cons.prems have "tail T a \<noteq> x"
    unfolding leaf_def out_arcs_def by auto
  ultimately show ?case by simp
qed

lemma directed_tree_del_vert:
  assumes "v \<noteq> root" and "leaf v"
  shows "directed_tree (del_vert v) root"
proof(unfold_locales)
  from \<open>v \<noteq> root\<close> show "root \<in> verts (del_vert v)" using verts_del_vert root_in_verts by auto

  have "\<exists>!p. pre_digraph.awalk (del_vert v) root p u"
    if "u \<in> verts (del_vert v)" for u
  proof -
    from \<open>u \<in> verts (del_vert v)\<close> have "u \<in> verts T" "u \<noteq> v"
      by (simp_all add: verts_del_vert)
    then obtain p where p: "awalk root p u" "\<forall>p'. awalk root p' u \<longrightarrow> p = p'"
    using unique_awalk[OF \<open>u \<in> verts T\<close>] by auto
    then have "v \<notin> set (awalk_verts root p)"
    using leaf_not_mem_awalk_verts[OF \<open>leaf v\<close> _ \<open>u \<noteq> v\<close>] by blast
    with p have
      "pre_digraph.awalk (del_vert v) root p u"
      "\<forall>p'. pre_digraph.awalk (del_vert v) root p' u \<longrightarrow> p = p'"
      using awalk_del_vert subgraph_awalk_imp_awalk subgraph_del_vert by blast+
    then show ?thesis by blast
  qed
  then show "\<exists>!p. pre_digraph.awalk (del_vert v) root p va"
    if "va \<in> verts (del_vert v)" for va
    using that by blast
qed (meson wf_digraph_del_vert wf_digraph_def)+


subsection \<open>In and out degrees\<close>

lemma in_degree_root_zero[simp]: "in_degree T root = 0"
proof(rule ccontr)
  assume "in_degree T root \<noteq> 0"
  then obtain e u where e: "tail T e = u" "head T e = root" "u \<in> verts T" "e \<in> arcs T"
    by (metis tail_in_verts all_not_in_conv card.empty in_degree_def in_in_arcs_conv)
  with unique_awalk obtain p where p: "awalk root p u"
    by blast
  with e have "awalk root (p@[e]) root"
    using awalk_appendI arc_implies_awalk by auto
  moreover have "awalk root [] root"
    by (simp add: awalk_Nil_iff root_in_verts)
  ultimately show "False"
    using unique_awalk by blast
qed

lemma two_in_arcs_contr:
  assumes "e1 \<in> arcs T" "e2 \<in> arcs T" and "e1 \<noteq> e2" and "head T e1 = head T e2"
  shows "False"
proof -
  from unique_awalk assms obtain p1 p2
    where "awalk root p1 (tail T e1)" and "awalk root p2 (tail T e2)"
    by (meson tail_in_verts in_in_arcs_conv)
  with assms have "awalk root (p1@[e1]) (head T e1)" and "awalk root (p2@[e2]) (head T e1)"
    unfolding in_arcs_def
    using arc_implies_awalk by force+
  with unique_awalk \<open>e1 \<noteq> e2\<close> show "False" by blast
qed

lemma finite_in_arcs[simp]: "v \<in> verts T \<Longrightarrow> finite (in_arcs T v)"
proof(rule ccontr)
  assume "\<not> finite (in_arcs T v)"
  then obtain e1 e2
    where e1_e2: "e1 \<in> in_arcs T v" "e2 \<in> in_arcs T v" "e1 \<noteq> e2"
    by (metis finite.emptyI finite_insert finite_subset insertI1 subsetI)
  with two_in_arcs_contr show "False" unfolding in_arcs_def by auto
qed

lemma in_arcs_root[simp]: "in_arcs T root = {}"
  using in_degree_root_zero
  by (auto simp: in_degree_def root_in_verts)

lemma root_root: "local.root root"
  using root_in_verts unfolding root_def by simp

lemma not_root_if_dominated: "u \<rightarrow>\<^bsub>T\<^esub> v \<Longrightarrow> v \<noteq> root"
  using in_arcs_root unfolding in_arcs_def by auto

lemma in_degree_one_if_not_root: "\<lbrakk> v \<in> verts T; v \<noteq> root \<rbrakk>  \<Longrightarrow> in_degree T v = 1"
proof(rule ccontr)
  assume "v \<noteq> root" and "v \<in> verts T" and "in_degree T v \<noteq> 1"
  then have "in_degree T v \<noteq> 0"
  proof -
    from unique_awalk \<open>v \<in> verts T\<close> obtain p where "awalk root p v" by blast
    with \<open>v \<noteq> root\<close> have "root \<rightarrow>\<^sup>+\<^bsub>T\<^esub> v" using reachable_awalkI by blast
    then have "\<exists>u. u \<rightarrow>\<^bsub>T\<^esub> v" by (meson tranclD2)
    then show ?thesis
      using finite_in_arcs[OF \<open>v \<in> verts T\<close>] unfolding in_degree_def
      using card_eq_0_iff by fastforce
  qed
  moreover
  have "\<not> in_degree T v \<ge> 2"
  proof
    assume in_deg_ge_2: "in_degree T v \<ge> 2"
    have "\<exists>e1 e2. e1 \<in> in_arcs T v \<and> e2 \<in> in_arcs T v \<and> e1 \<noteq> e2"
    proof(cases "in_arcs T v = {}")
      case True
      then show ?thesis using in_deg_ge_2[unfolded in_degree_def] by simp
    next
      case False
      then obtain e1 where "e1 \<in> in_arcs T v" by blast
      then have "card (in_arcs T v) = 1" if "\<forall>e2 \<in> in_arcs T v. e1 = e2"
        using that by(auto simp: card_Suc_eq[where ?A="(in_arcs T v)"])
      then show ?thesis
        using in_deg_ge_2[unfolded in_degree_def] \<open>e1 \<in> in_arcs T v\<close> by force
    qed
    with two_in_arcs_contr show "False" unfolding in_arcs_def by auto
  qed
  ultimately show "False" using \<open>in_degree T v \<noteq> 1\<close> by linarith
qed

lemma in_deg_one_imp_not_root: "\<lbrakk> v \<in> verts T; in_degree T v = 1 \<rbrakk>  \<Longrightarrow> v \<noteq> root"
  using in_degree_root_zero by auto

corollary in_deg_one_iff: "v \<in> verts T \<Longrightarrow> v \<noteq> root \<longleftrightarrow> in_degree T v = 1"
  using in_degree_one_if_not_root in_deg_one_imp_not_root by blast

lemma ex_in_arc: "\<lbrakk> v \<noteq> root; v \<in> verts T \<rbrakk> \<Longrightarrow> \<exists>e. in_arcs T v = {e}"
  using in_degree_one_if_not_root unfolding in_degree_def
  by (auto simp: card_Suc_eq)

lemma root_unique: "local.root r \<Longrightarrow> r = root"
  using ex_in_arc by blast

subsection \<open>Definition of a parent\<close>

definition parent :: "'a \<Rightarrow> 'a" where
  "parent v \<equiv> if v = root \<or> v \<notin> verts T then v else (THE u. u \<rightarrow>\<^bsub>T\<^esub> v)"

lemma parent_cases:
  obtains
    (root) "v = root"
  | (not_in_verts) "v \<notin> verts T"
  | (not_root) "v \<noteq> root" "v \<in> verts T"
  using root_in_verts by auto

lemma exists_unique_dominates_if_neq_root:
  assumes "v \<noteq> root" "v \<in> verts T" 
  shows "\<exists>!u. u \<rightarrow>\<^bsub>T\<^esub> v"
proof -
  from ex_in_arc[OF assms] obtain e where "in_arcs T v = {e}"
    by blast
  then have "tail T e \<rightarrow>\<^bsub>T\<^esub> v"
    using in_arcs_imp_in_arcs_ends by fastforce
  moreover from \<open>in_arcs T v = {e}\<close> have "u = tail T e" if "u \<rightarrow>\<^bsub>T\<^esub> v" for u
    using that in_arcs_imp_in_arcs_ends by fastforce
  ultimately show ?thesis
    by blast
qed

lemma parent_root_eq_root[simp]: "parent root = root"
  unfolding parent_def by simp

lemma parent_id_if_not_in_verts[simp]: "v \<notin> verts T \<Longrightarrow> parent v = v"
  unfolding parent_def by simp

lemma parent_dominates_if_in_verts_and_not_root[intro]:
  "v \<in> verts T \<Longrightarrow> v \<noteq> root \<Longrightarrow> parent v \<rightarrow>\<^bsub>T\<^esub> v"
  using exists_unique_dominates_if_neq_root[THEN theI']
  unfolding parent_def by simp

lemma parent_neq_if_in_verts_and_not_root:
  "v \<in> verts T \<Longrightarrow> v \<noteq> root \<Longrightarrow> parent v \<noteq> v"
  using parent_dominates_if_in_verts_and_not_root
  by (metis loopfree.adj_not_same)

lemma parent_reachable_if_in_verts: "v \<in> verts T \<Longrightarrow> parent v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v"
  by (cases v rule: parent_cases) auto

lemma parent_in_verts:
  "v \<in> verts T \<Longrightarrow> parent v \<in> verts T"
  using parent_reachable_if_in_verts reachable_in_verts(1) by blast

lemma arcs_del_leafE:
  assumes "leaf v" "v \<noteq> root"
  obtains e where
    "arcs (del_vert v) = arcs T - {e}" "e \<in> arcs T"
    "tail T e = parent v" "head T e = v"
proof -
  from assms ex_in_arc obtain e where "in_arcs T v = {e}"
    by force
  moreover from assms have "out_arcs T v = {}"
    by simp
  ultimately have "arcs (del_vert v) = arcs T - {e}"
    unfolding arcs_del_vert by auto
  moreover from \<open>in_arcs T v = {e}\<close> assms(2) have "tail T e = parent v" "head T e = v"
    using unique_arc(2) by force+
  moreover from \<open>in_arcs T v = {e}\<close> have "e \<in> arcs T"
    by auto
  ultimately show ?thesis
    using that by blast
qed


subsection \<open>An induction rule for finite trees\<close>
text \<open>
In this section we develop an induction rule for finite trees. Since this induction rule works by
inductively adding trees we first need to define the notion of a leaf and prove numerous facts
about them.
\<close>
lemma finite_arcs_if_finite_verts[simp, intro]:
  "finite (verts T) \<Longrightarrow> finite (arcs T)"
proof -
  assume "finite (verts T)"
  then have "finite (verts T \<times> verts T)" by simp
  let ?a = "\<lambda>(u,v). {e \<in> arcs T.  tail T e = u \<and> head T e = v}"
  let ?A = "\<Union>(?a ` (verts T \<times> verts T))"
  have "arcs T \<subseteq> ?A"
  proof
    fix e assume e: "e \<in> arcs T"
    then have "tail T e \<in> verts T" and "head T e \<in> verts T"
      using wellformed by auto
    with e show "e \<in> ?A" by blast
  qed
  moreover have "finite (?a (u,v))" for u v
    using unique_arc_set[of u v] finite.simps by auto
  then have "finite ?A"
    by (auto simp: finite_UN[where ?B="?a", OF \<open>finite (verts T \<times> verts T)\<close>])
  ultimately show "finite (arcs T)" using finite_subset by blast
qed

lemma root_leaf_iff: "leaf root \<longleftrightarrow> verts T = {root}"
proof
  from root_in_verts show "leaf root" if "verts T = {root}"
  proof -
    from that have "finite (verts T)"
      by simp
    then interpret fin_directed_tree T root
      using directed_tree_axioms
      by unfold_locales simp_all
    from ex_leaf that show ?thesis
      unfolding leaf_def by force
  qed
  show "leaf root \<Longrightarrow> verts T = {root}"
  proof(rule ccontr)
    assume "leaf root" and "verts T \<noteq> {root}"
    with non_empty obtain u where u: "u \<in> verts T" "u \<noteq>root"
      by blast
    with unique_awalk obtain p where p: "awalk root p u" by blast
    with \<open>u \<noteq> root\<close> obtain e where e: "e = hd p" "tail T e = root"
      by (metis awalkE' awalk_ends pre_digraph.cas_simp)
    with u p have "e \<in> out_arcs T root" unfolding out_arcs_def
      by (simp, metis awalkE awalk_ends hd_in_set subset_iff)
    with \<open>leaf root\<close> show "False"
      unfolding leaf_def out_degree_def by auto
  qed
qed

lemma arcs_del_leaf:
  assumes "e \<in> arcs T" "head T e = v" and "leaf v"
  shows "arcs (del_vert v) = arcs T - {e}"
proof -
  from assms have "v \<noteq> root"
    using in_arcs_root by fastforce
  from arcs_del_leafE[OF \<open>leaf v\<close> this] assms show ?thesis
    by (metis two_in_arcs_contr)
qed

end

context fin_directed_tree
begin

lemma fin_directed_tree_del_vert:
  assumes "v \<noteq> root" and "leaf v"
  shows "fin_directed_tree (del_vert v) root"
proof -
  note directed_tree_del_vert[OF assms] fin_digraph_del_vert[of v]
  then show ?thesis
    unfolding fin_directed_tree_def by blast
qed

lemma del_leaf_induct[case_names single_vert del_leaf]:
  assumes single_vert: "\<And>t h root. P \<lparr> verts = {root}, arcs = {}, tail = t, head = h \<rparr>"
  assumes del_leaf: "\<And>T' root v.
    \<lbrakk> pre_digraph.leaf T' v; v \<noteq> root
    ; fin_directed_tree T' root
    ; P (pre_digraph.del_vert T' v)
    \<rbrakk> \<Longrightarrow> P T'"
  shows "P T"
  using finite_verts fin_directed_tree_axioms
proof(induction "card (verts T)" arbitrary: T root)
  case 0
  then have "verts T = {}"
    using card_eq_0_iff by simp
  with directed_tree.non_empty \<open>fin_directed_tree T root\<close> show ?case
    unfolding fin_directed_tree_def by fast
next
  case (Suc n)
  then interpret T: fin_directed_tree T root
    by blast
  show ?case
  proof(cases n)
    case 0
    with Suc have "card (verts T) = 1"
      by simp
    with T.root_in_verts have "verts T = {root}"
      by (metis card_1_singletonE singletonD)
    then have "arcs T = {}"
      using T.loopfree.no_loops T.tail_in_verts by fastforce
    with \<open>verts T = {root}\<close> single_vert show ?thesis
      by (cases T) auto
  next
    case Suc': (Suc n')
    from T.ex_leaf obtain v where "T.leaf v"
      by blast
    with Suc' have "v \<noteq> root"
      using T.root_leaf_iff Suc.hyps(2) by fastforce

    note fin_d_tree_del_vert = T.fin_directed_tree_del_vert[OF \<open>v \<noteq> root\<close> \<open>T.leaf v\<close>]
    
    from Suc have "n = card (verts (T.del_vert v))" "finite (verts (T.del_vert v))"
      unfolding T.verts_del_vert using \<open>T.leaf v\<close> by force+
    note IH = Suc.hyps(1)[OF this fin_d_tree_del_vert]

    from del_leaf[OF \<open>T.leaf v\<close> \<open>v \<noteq> root\<close> T.fin_directed_tree_axioms IH]
    show ?thesis .
  qed
qed

lemma add_leaf_induct[case_names single_vert add_leaf]:
  assumes single_vert: "\<And>t h root. P \<lparr> verts = {root}, arcs = {}, tail = t, head = h \<rparr>"
      and add_leaf: "\<And>T' V A t h u root a v.
        \<lbrakk> T' = \<lparr> verts = V, arcs = A, tail = t, head = h \<rparr>
        ; fin_directed_tree T' root
        ; P T'
        ; u \<in> V; v \<notin> V; a \<notin> A
        \<rbrakk> \<Longrightarrow> P \<lparr> verts = V \<union> {v}, arcs = A \<union> {a}, tail = t(a := u), head = h(a := v) \<rparr>"
    shows "P T"
proof(induction rule: del_leaf_induct)
  case (del_leaf T' root v)
  then interpret T': fin_directed_tree T' root
    by blast
  from del_leaf T'.arcs_del_leafE obtain e where e:
    "arcs (T'.del_vert v) = arcs T' - {e}" "e \<in> arcs T'"
    "tail T' e = T'.parent v" "head T' e = v"
    by blast

  let ?T = "T'.del_vert v"
  have T_eq:
    "?T = \<lparr> verts = verts T' - {v}, arcs = arcs T' - {e}, tail = tail T', head = head T' \<rparr>"
    using e by (simp add: T'.del_vert_def)

  have T'_eq:
    "T' = \<lparr> verts = (verts T' - {v}) \<union> {v}, arcs = (arcs T' - {e}) \<union> {e}
          , tail = (tail T')(e := T'.parent v), head = (head T')(e := v) \<rparr>"
    using e fun_upd_triv \<open>T'.leaf v\<close>[THEN T'.leaf_in_vertsD]
    by (cases T') force

  note fin_dir_tree_T = T'.fin_directed_tree_del_vert[OF del_leaf(2,1)]
  note add_leaf[OF T_eq fin_dir_tree_T del_leaf.IH]
  note add_leaf = this[of "T'.parent v" v e, folded T'_eq]
  show ?case
    by (rule add_leaf) (use e(2,4) e(3)[symmetric] T'.loopfree.no_loops in auto)
qed (use single_vert in simp)


text \<open>A simple consequence of the induction rule is that a tree with n vertices has n-1 arcs.\<close>
lemma Suc_card_arcs_eq_card_verts:
  "Suc (card (arcs T)) = card (verts T)"
proof(induction rule: del_leaf_induct)
  case (del_leaf T' root v)
  then interpret T': fin_directed_tree T' root
    by blast
  from del_leaf T'.finite_verts T'.finite_arcs show ?case
    unfolding T'.verts_del_vert
    by (metis T'.arcs_del_leafE T'.leaf_in_vertsD card.remove)
qed simp

end

end
