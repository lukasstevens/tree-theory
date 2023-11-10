theory Tree
  imports Directed_Tree
begin

experiment
begin

definition example_dag :: "nat pair_pre_digraph" where
  "example_dag \<equiv> \<lparr> pverts = {0, 1, 2}, parcs = {(0, 1), (0, 2), (1, 2)} \<rparr>"

interpretation ex_dag: wf_digraph example_dag
  unfolding example_dag_def with_proj_def
  by (unfold_locales) auto

lemma nexists_cycle_if_arcs_mono:
  fixes G :: "('a::linorder, 'b) pre_digraph"
  assumes "wf_digraph G"
  assumes "\<forall>e \<in> arcs G. tail G e < head G e"
  shows "\<nexists>c. pre_digraph.cycle G c"
proof
  from \<open>wf_digraph G\<close> interpret wf_digraph G
    by blast
  assume "\<exists>c. cycle c"
  then obtain u p e where "awalk u (p @ [e]) u"
    unfolding pre_digraph.cycle_def by (metis rev_exhaust)

  have sorted: "sorted_wrt (<) (map (tail G) p)" if "awalk u p v" for p v
    using that
  proof(induction p arbitrary: v rule: rev_induct)
    case (snoc a p)
    then have "awalk u p (tail G a)"
      by (metis awalk_Cons_iff awalk_append_iff)
    note snoc.IH[OF this]
    moreover from snoc.prems have "\<forall>b \<in> set p. tail G b < tail G a"
    proof(induction p arbitrary: a v rule: rev_induct)
      case (snoc x xs)
      then have "head G x = tail G a"
        by (simp add: awalk_Cons_iff)
      with assms(2) snoc.prems have "tail G x < tail G a"
        using awalk_Cons_iff by auto
      moreover from snoc have "\<forall>b\<in>set xs. tail G b < tail G x"
        using awalk_append_iff by blast
      ultimately show ?case
        by auto
    qed simp
    ultimately show ?case
      by (simp add: sorted_wrt_append)
  qed simp
  
  from \<open>awalk u (p @ [e]) u\<close> have "tail G (hd (p @ [e])) = u"
    by (auto simp: hd_append cas_simp)
  with sorted[OF \<open>awalk u (p @ [e]) u\<close>] have "u \<le> tail G e"
    by (cases p) auto
  with assms(2) \<open>awalk u (p @ [e]) u\<close> have "u < head G e"
    using awalk_append_iff by force
  with \<open>awalk u (p @ [e]) u\<close> show False
    by auto
qed

lemma nexists_cycle_ex_dag: "\<nexists>c. ex_dag.cycle c"
  by (intro nexists_cycle_if_arcs_mono ex_dag.wf_digraph_axioms)
     (auto simp: example_dag_def)

lemma forest_ex_dag: "forest example_dag"
  using nexists_cycle_ex_dag unfolding forest_def .
  
end

text \<open>Should we disallow multi-edges, i.e. should we add @{locale nomulti_digraph}?\<close>

locale forest = loopfree_digraph F + sym_digraph F for F +
  assumes nexists_cycle: "\<nexists>c. cycle c \<and> length c \<ge> 3"

locale fin_forest = forest F + fin_digraph F for F

locale tree = forest T for T +
  assumes strongly_connected: "strongly_connected T"

locale fin_tree = tree T + fin_digraph T for T

lemma (in loopfree_digraph) loopfree_digraph_if_subgraph:
  assumes "subgraph S G"
  shows "loopfree_digraph S"
proof -
  from assms interpret S: wf_digraph S
    by blast
  from assms show ?thesis
    apply (unfold_locales)
    using compatible_head compatible_tail no_loops by fastforce
qed

lemma (in forest) tree_if_in_sccs:
  assumes "T \<in> sccs"
    shows "tree T"
proof -
  from assms interpret T: wf_digraph T
    by blast
  from assms interpret T: loopfree_digraph T
    by (intro loopfree_digraph_if_subgraph) blast
  from assms have "strongly_connected T"
    by auto
  moreover from assms have "\<nexists>c. T.cycle c \<and> length c \<ge> 3"
    using nexists_cycle subgraph_cycle by fastforce
  moreover from assms have "symmetric T"
    using induced_graph_imp_symmetric in_sccs_imp_induced by auto   
  ultimately show ?thesis
    by unfold_locales blast+
qed

context forest
begin

definition "dtree_at r \<equiv>
  \<lparr> verts = {v. r \<rightarrow>\<^sup>*\<^bsub>F\<^esub> v}
  , arcs = {e |e p v. apath r p v \<and> e \<in> set p}
  , tail = tail F, head = head F
  \<rparr>"

lemma directed_tree_dtree_at:
  assumes "r \<in> verts F"
  shows "directed_tree (dtree_at r) r"
proof -
  interpret dtree_at: wf_digraph "dtree_at r"
    unfolding dtree_at_def
    by (unfold_locales)
       (auto dest: awalkI_apath simp: awalk_verts_arc1 awalk_verts_arc2 awalk_verts_reachable_from)
  from assms have "r \<in> verts (dtree_at r)"
    unfolding dtree_at_def by auto
  moreover have "\<exists>!p. dtree_at.awalk r p v" if "v \<in> verts (dtree_at r)" for v
    sorry
  ultimately show "directed_tree (dtree_at r) r"
    by unfold_locales assumption+
  oops

end

lemma (in tree) verts_dtree_at[simp]:
  assumes "r \<in> verts T"
    shows "verts (dtree_at r) = verts T"
  oops

lemma (in fin_tree) add_leaf_induct[case_names single_vert add_leaf]:
  assumes base: "\<And>t h root. P \<lparr> verts = {root}, arcs = {}, tail = t, head = h \<rparr>"
      and add_leaf: "\<And>T' V A t h u root a1 a2 v.
        \<lbrakk> T' = \<lparr> verts = V, arcs = A, tail = t, head = h \<rparr>
        ; fin_tree T'
        ; P T'
        ; u \<in> V; v \<notin> V; a1 \<notin> A; a2 \<notin> A
        \<rbrakk> \<Longrightarrow> P \<lparr> verts = V \<union> {v}, arcs = A \<union> {a1, a2}
                , tail = t(a1 := u, a2 := v), head = h(a1 := v, a2 := u) \<rparr>"
    shows "P T"
  oops

end