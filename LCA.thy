theory LCA
  imports "Graph_Theory.Graph_Theory" "Graph_Theory_Batteries"
begin

context pre_digraph
begin

definition root :: "'a \<Rightarrow> bool" where
  "root v \<equiv> v \<in> verts G \<and> in_arcs G v = {}"

lemma root_in_vertsD[simp]: "root v \<Longrightarrow> v \<in> verts G"
  unfolding root_def by simp

lemma root_in_arcsD[simp]: "root v \<Longrightarrow> in_arcs G v = {}"
  unfolding root_def by simp

lemma root_in_degree_zero[simp]: "root v \<Longrightarrow> in_degree G v = 0"
  unfolding root_def in_degree_def by auto

lemma rootE[elim]:
  assumes "root v"
  obtains "v \<in> verts G" "in_arcs G v = {}"
  using assms unfolding root_def by auto

definition leaf :: "'a \<Rightarrow> bool" where
  "leaf v \<equiv> v \<in> verts G \<and> out_arcs G v = {}"

lemma leaf_in_vertsD[simp]: "leaf v \<Longrightarrow> v \<in> verts G"
  unfolding leaf_def by simp

lemma leaf_out_arcsD[simp]: "leaf v \<Longrightarrow> out_arcs G v = {}"
  unfolding leaf_def by simp

lemma leaf_out_degree_zero[simp]: "leaf v \<Longrightarrow> out_degree G v = 0"
  unfolding leaf_def out_degree_def by auto

lemma leafE[elim]:
  assumes "leaf v"
  obtains "v \<in> verts G" "out_arcs G v = {}"
  using assms unfolding leaf_def by auto

end

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
end

end