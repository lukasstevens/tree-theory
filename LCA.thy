theory LCA
  imports "Graph_Theory.Graph_Theory" "Graph_Theory_Batteries"
begin

context wf_digraph
begin

definition (in pre_digraph) lca :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
  "lca ca x y \<equiv> let H = G \<restriction> {ca. ca \<rightarrow>\<^sup>* x \<and> ca \<rightarrow>\<^sup>* y} in ca \<in> verts H \<and> pre_digraph.leaf H ca"

lemma lca_reachableD[simp]:
  assumes "lca ca x y"
  shows "ca \<rightarrow>\<^sup>* x" "ca \<rightarrow>\<^sup>* y"
  using assms unfolding lca_def by simp_all

lemma lca_symmetric:
  "lca ca x y \<Longrightarrow> lca ca y x"
  unfolding lca_def pre_digraph.leaf_def by auto

lemma not_lca_if_awalk_lca:
  assumes "lca ca x y" "awalk ca' p ca" "p \<noteq> []"
  shows "\<not> lca ca' x y"
  using assms
proof -
  let ?G' = "G \<restriction> {v. v \<rightarrow>\<^sup>* x \<and> v \<rightarrow>\<^sup>* y}"
  interpret G': wf_digraph ?G'
    by blast

  have "v \<rightarrow>\<^sup>* x \<and> v \<rightarrow>\<^sup>* y" if "v \<in> set (awalk_verts ca' p)" for v
    using assms that unfolding lca_def Let_def 
    by simp (meson awalk_verts_reachable_to reachable_trans)
  with assms have "set (awalk_verts ca' p) \<subseteq> verts ?G'"
    by auto
  with assms have "G'.awalk ca' p ca"
    using awalk_induce by fastforce
  with \<open>p \<noteq> []\<close> have "ca' \<rightarrow>\<^bsub>?G'\<^esub> head ?G' (hd p)"
    using G'.awalk_Cons_iff G'.in_arcs_imp_in_arcs_ends
    by (cases p) auto
  then have "\<not> G'.leaf ca'"
    using G'.not_leaf_if_dominates by blast
  then show ?thesis
    unfolding lca_def Let_def by blast
qed

lemma not_lca_if_reachable1_lca:
  assumes "lca ca x y" "ca' \<rightarrow>\<^sup>+ ca"
  shows "\<not> lca ca' x y"
  using assms not_lca_if_awalk_lca
  by (meson reachable1_awalk)

end

end