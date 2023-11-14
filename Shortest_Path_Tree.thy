theory Shortest_Path_Tree
  imports Directed_Tree Graph_Neighborhood Graph_Diameter
begin

text \<open>
This theory defines the notion of a partial shortest path tree in the locale @{text psp_tree}.
A partial shortest path tree contains the s nearest notes with respect to some weight function.
Since, at the time of writing, the definition of @{const forest} only guarantees acyclicity
and the definition of @{const tree} is also incorrect by extension, we develop our own definition
of a directed tree in the locale @{text directed_tree}.
\<close>

section \<open>Depth of a tree\<close>
context directed_tree
begin

definition depth where "depth w \<equiv> Sup {\<mu> w root v|v. v \<in> verts T}"

context
  fixes w :: "'b weight_fun"
  assumes "\<forall>e \<in> arcs T. w e \<ge> 0"
begin

lemma sp_from_root_le: "u \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v \<Longrightarrow> \<mu> w root v \<ge> \<mu> w u v"
proof -
  assume "u \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v"

  have "\<mu> w root u \<ge> 0"
    using \<open>\<forall>e\<in>arcs T. 0 \<le> w e\<close> sp_non_neg_if_w_non_neg by simp
  moreover
  have "root \<rightarrow>\<^sup>*\<^bsub>T\<^esub> u"
    using \<open>u \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v\<close> reachable_from_root reachable_in_verts(1) by auto
  ultimately show ?thesis
    using \<open>u \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v\<close> sp_append_if_reachable ereal_le_add_self2 by auto
qed

lemma depth_lowerB: "v \<in> verts T \<Longrightarrow> depth w \<ge> \<mu> w root v"
proof -
  assume "v \<in> verts T"
  then have "\<mu> w root v \<in> {\<mu> w root v|v. v \<in> verts T}" by auto
  then show "depth w \<ge> \<mu> w root v"
    unfolding depth_def by (simp add: Sup_upper)
qed

lemma depth_upperB: "\<forall>v \<in> verts T. \<mu> w root v \<le> d \<Longrightarrow> depth w \<le> d"
proof -
  assume "\<forall>v \<in> verts T. \<mu> w root v \<le> d"
  then have "\<forall>x \<in> {\<mu> w root v |v. v \<in> verts T}. x \<le> d"
    by auto
  then show ?thesis
    unfolding depth_def using Sup_least by fast
qed

text \<open>
This relation between depth of a tree and its diameter is later used to establish the
correctness of the diameter estimate.
\<close>
lemma depth_eq_fin_dia: "fin_digraph T \<Longrightarrow> depth w = fin_diameter w"
proof -
  assume "fin_digraph T"
  have "\<forall>v \<in> verts T. \<mu> w root v < \<infinity>"
    using \<mu>_reach_conv reachable_from_root by blast
  then have "{\<mu> w root v|v. v \<in> verts T} \<subseteq> fin_sp_costs w"
    unfolding fin_sp_costs_def using root_in_verts by blast
  then have "depth w \<le> fin_diameter w"
    unfolding depth_def fin_diameter_def by (simp add: Sup_subset_mono)
  moreover
  have "\<not> depth w < fin_diameter w"
  proof
    assume "depth w < fin_diameter w"
    obtain u v where "\<mu> w u v = fin_diameter w" "u \<in> verts T" "v \<in> verts T"
      using fin_digraph.ex_sp_eq_fin_diameter[OF \<open>fin_digraph T\<close> non_empty] by blast
    then have "u \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v"
      by (metis \<mu>_reach_conv fin_digraph.fin_diameter_lt_inf[OF \<open>fin_digraph T\<close>])
    then have "\<mu> w u v \<le> \<mu> w root v" using sp_from_root_le by blast
    also have "\<dots> \<le> depth w" using depth_lowerB[OF \<open>v \<in> verts T\<close>] by simp
    finally have "fin_diameter w \<le> depth w"
      using \<open>\<mu> w u v = fin_diameter w\<close> by simp
    with \<open>depth w < fin_diameter w\<close> show False by simp
  qed
  ultimately show ?thesis by simp
qed

end

end

section \<open>Partial shortest path three\<close>

locale psp_tree =
  T: directed_tree T source + G: wf_digraph G for G T :: "('a, 'b) pre_digraph" and w source n +
assumes
    subgraph_of_G: "subgraph T G" and
    source_in_G: "source \<in> verts G" and
    partial: "G.n_nearest_verts w source n (verts T)" and
    sp: "u \<in> verts T \<Longrightarrow> T.\<mu> w source u = G.\<mu> w source u"
begin

text \<open>
Here we formalize the notion of a partial shortest path tree. This is a shortest path tree where
only the @{term n} nearest nodes in the graph @{term G} are explored.
Consequently, a partial shortest path tree is a subtree of the complete shortest path tree.
We can obtain the complete shortest path tree by choosing n to be larger than the cardinality
of the graph @{term G}.
\<close>

sublocale T: fin_directed_tree T source
  using G.nnvs_finite[OF partial]
  by unfold_locales auto

lemma card_verts_le: "card (verts T) \<le> Suc n"
  using G.nnvs_card_le_n partial by auto

lemma reachable_subs: "{x. r \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x} \<subseteq> {x. r \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
  by (simp add: Collect_mono G.reachable_mono subgraph_of_G)

text \<open>The following lemma proves that we explore all nodes if we set @{term n} large enough.\<close>
lemma sp_tree:
  assumes "fin_digraph G"
  assumes card_reachable: "Suc n \<ge> card {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
  shows "verts T = {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
  using fin_digraph.nnvs_imp_all_reachable_Suc[OF \<open>fin_digraph G\<close> partial card_reachable] .

corollary sp_tree2:
  assumes "fin_digraph G"
  assumes "Suc n \<ge> card (verts G)"
  shows "verts T = {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
proof -
  have "{x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x} \<subseteq> verts G"
    using source_in_G G.reachable_in_verts(2) by blast
  then have "Suc n \<ge> card {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
    using \<open>Suc n \<ge> card (verts G)\<close> fin_digraph.finite_verts[OF \<open>fin_digraph G\<close>]
    by (meson card_mono dual_order.trans)
  from sp_tree[OF \<open>fin_digraph G\<close> this] show ?thesis .
qed

lemma strongly_con_imp_card_verts_eq:
  assumes "fin_digraph G"
  assumes "strongly_connected G"
  assumes card_verts: "Suc n \<le> card (verts G)"
  shows "card (verts T) = Suc n"
proof -
  have verts_G: "verts G = {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}"
    using G.reachable_eq_verts_if_strongly_connected
      [OF source_in_G \<open>strongly_connected G\<close>, symmetric] .
  with card_verts have "Suc n \<le> card {x. source \<rightarrow>\<^sup>*\<^bsub>G\<^esub> x}" by simp

  from fin_digraph.nnvs_imp_reachable[OF \<open>fin_digraph G\<close> partial this]
  show ?thesis by blast
qed

lemma depth_fin_dia_lB:
  assumes "\<forall>e \<in> arcs G. w e \<ge> 0"
  shows "T.depth w \<le> G.fin_diameter w"
proof(rule ccontr)
  assume "\<not> T.depth w \<le> G.fin_diameter w"
  then have "T.depth w > G.fin_diameter w"
    by auto
  then have "\<exists>v \<in> verts T. T.\<mu> w source v > G.fin_diameter w"
    unfolding T.depth_def less_Sup_iff by blast
  then obtain v where v: "v \<in> verts T" "v \<in> verts G" "T.\<mu> w source v > G.fin_diameter w"
    using subgraph_of_G by blast
  moreover
  have "T.\<mu> w source v < \<infinity>"
    using T.reachable_from_root T.\<mu>_reach_conv v(1) by blast
  ultimately show "False"
    using source_in_G G.fin_diameter_lowerB[OF source_in_G \<open>v \<in> verts G\<close>] sp v
    by (metis linorder_not_less)
qed

end

end