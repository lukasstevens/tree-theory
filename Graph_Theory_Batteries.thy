theory Graph_Theory_Batteries
  imports "Graph_Theory.Graph_Theory"
begin

section \<open>Miscellaneous\<close>

lemma (in wf_digraph) awalk_not_Nil_butlastD:
  assumes "awalk x p y"
  assumes "p \<noteq> []"
  shows
    "awalk x (butlast p) (awlast x (butlast p))"
    "awalk (awlast x (butlast p)) [last p] y"
proof -
  from assms have "p = butlast p @ [last p]"
    by simp
  with assms awalk_append_iff show
    "awalk x (butlast p) (awlast x (butlast p))"
    "awalk (awlast x (butlast p)) [last p] y"
    by metis+
qed

lemma (in wf_digraph) last_in_awalk_verts:
  "awalk x p y \<Longrightarrow> y \<in> set (awalk_verts x p)"
  "apath x p y \<Longrightarrow> y \<in> set (awalk_verts x p)"
  by (auto simp: apath_def)

lemma (in wf_digraph) strongly_connected_connectedD[dest?, simp]:
  assumes "strongly_connected G"
  shows "connected G"
  using assms unfolding strongly_connected_def
  by (auto intro!: connectedI reachable_mk_symmetricI)

lemma (in wf_digraph) reachable_eq_verts_if_strongly_connected:
  "\<lbrakk> r \<in> verts G; strongly_connected G \<rbrakk> \<Longrightarrow> {x. r \<rightarrow>\<^sup>* x} = verts G"
  unfolding strongly_connected_def using reachable_in_verts(2) by blast

lemma (in fin_digraph) finite_reachable: "finite {x. u \<rightarrow>\<^sup>* x}"
  using finite_verts
  by (metis finite_subset mem_Collect_eq reachable_in_vertsE subsetI)

lemma (in wf_digraph) not_distinct_awalk_verts:
  assumes "finite (verts G)" and "awalk u p v" and "length p \<ge> card (verts G)"
  shows "\<not> distinct (awalk_verts u p)"
proof -
  have *: "length (awalk_verts u p) > length p"
    by (induction p arbitrary: u) auto

  show ?thesis
  proof(cases "length p = 0")
    case True
    with assms show ?thesis unfolding awalk_def by simp
  next
    case False
    with assms * have "length (awalk_verts u p) > card (verts G)"
      by auto
    moreover
    have "set (awalk_verts u p) \<subseteq> verts G" using assms(2) by blast
    ultimately show ?thesis using assms(1)
      by (induction p arbitrary: u)
         (auto, metis card_subset_eq distinct_card less_antisym)
  qed
qed

lemma (in wf_digraph) awalk_del_vert:
  "\<lbrakk> awalk u p v; x \<notin> set (awalk_verts u p) \<rbrakk> \<Longrightarrow> pre_digraph.awalk (del_vert x) u p v"
proof(induction p arbitrary: u)
  case Nil
  then have "set (awalk_verts u []) = {u}" by auto
  with Nil have "x \<noteq> u" by simp
  moreover
  from Nil have "u = v" unfolding awalk_def by auto
  ultimately show ?case using Nil
    by (simp add: awalk_hd_in_verts pre_digraph.verts_del_vert
        wf_digraph.awalk_Nil_iff wf_digraph_del_vert)
next
  case (Cons a p)
  then obtain u' where u': "pre_digraph.awalk (del_vert x) u' p v"
    using awalk_Cons_iff by auto
  moreover
  from Cons.prems have "head G a \<noteq> x"
    using hd_in_awalk_verts(1) awalk_Cons_iff by auto
  ultimately show ?case using Cons
    by (auto simp: awalk_Cons_iff head_del_vert pre_digraph.del_vert_simps(2)
        tail_del_vert wf_digraph.awalk_Cons_iff wf_digraph_del_vert)
qed


context wf_digraph
begin

lemma awalk_imp_subgraph_awalk:
  assumes "subgraph H G"
  assumes "awalk x p y"
  assumes "y \<in> verts H" "set p \<subseteq> arcs H"
  shows "pre_digraph.awalk H x p y"
proof -
  from assms interpret H: wf_digraph H
    by blast
  from assms(2-4) show ?thesis
  proof(induction p arbitrary: x)
    case Nil
    then show ?case
      unfolding awalk_Nil_iff H.awalk_Nil_iff by blast
  next
    case (Cons a p)
    from assms(1) have "compatible G H"
      by blast
    with Cons show ?case
      using H.arc_implies_awalk
      unfolding awalk_Cons_iff H.awalk_Cons_iff 
      by (auto simp: compatible_tail compatible_head)
  qed
qed

lemma subgraph_add_arc:
  "subgraph G (add_arc a)"
  using wf_digraph_axioms wf_digraph_add_arc
  by (intro subgraphI) (auto simp: compatible_def verts_add_arc_conv)

lemma awalk_add_arc_if_awalk:
  assumes "awalk x p y"
  shows "pre_digraph.awalk (add_arc a) x p y"
  using assms subgraph_add_arc wf_digraph.subgraph_awalk_imp_awalk[OF wf_digraph_add_arc]
  by simp

lemma awalk_if_awalk_add_arc:
  assumes "pre_digraph.awalk (add_arc a) x p y"
  assumes "verts (add_arc a) = verts G"
  assumes "a \<notin> set p"
  shows "awalk x p y"
  using assms
proof(induction p arbitrary: x)
  case Nil
  then show ?case
    unfolding awalk_Nil_iff wf_digraph.awalk_Nil_iff[OF wf_digraph_add_arc]
    by blast
next
  case (Cons a' p)
  then show ?case
    unfolding awalk_Cons_iff wf_digraph.awalk_Cons_iff[OF wf_digraph_add_arc]
    by auto
qed

lemma awalk_if_awalk_del_arc:
  assumes "pre_digraph.awalk (del_arc a) x p y"
  shows "awalk x p y"
  using assms subgraph_awalk_imp_awalk subgraph_del_arc by blast

end

text \<open>This is an alternative formulation of @{thm pre_digraph.arcs_del_vert}.\<close>
lemma (in pre_digraph) arcs_del_vert2:
  "arcs (del_vert v) = arcs G - in_arcs G v - out_arcs G v"
  using arcs_del_vert by force

section \<open>Lemmas about \<^term>\<open>\<mu>\<close>\<close>

lemma (in wf_digraph) sp_non_neg_if_w_non_neg:
  assumes w_non_neg: "\<forall>e \<in> arcs G. w e \<ge> 0"
  shows "\<mu> w u v \<ge> 0"
proof(cases "u \<rightarrow>\<^sup>*\<^bsub>G\<^esub> v")
  case True
  have *: "awalk u p v \<Longrightarrow> awalk_cost w p \<ge> 0" for p
    by (simp add: pos_cost_pos_awalk_cost w_non_neg)
  then show ?thesis unfolding \<mu>_def
    by (metis (mono_tags, lifting) INF_less_iff ereal_less_eq(5) mem_Collect_eq not_less)
next
  case False
  then show ?thesis by (simp add: shortest_path_inf)
qed


lemma (in wf_digraph) sp_to_self_if_w_non_neg:
  assumes w_non_neg: "\<forall>e \<in> arcs G. w e \<ge> 0" and "u \<in> verts G"
  shows "\<mu> w u u = 0"
proof -
  have "awalk u [] u" and "awalk_cost w [] = 0"
    by (auto simp: assms(2) awalk_Nil_iff)
  moreover
  have "\<mu> w u u \<ge> 0" by (simp add: sp_non_neg_if_w_non_neg w_non_neg)
  ultimately show "\<mu> w u u = 0"
    by (metis antisym ereal_eq_0(2) min_cost_le_walk_cost)
qed

lemma (in wf_digraph) strongly_con_imp_sp_finite:
  "\<lbrakk> u \<in> verts G; v \<in> verts G; strongly_connected G \<rbrakk> \<Longrightarrow> \<mu> w u v < \<infinity>"
  unfolding strongly_connected_def using \<mu>_reach_conv by auto

text \<open>This is an alternative formulation of @{thm fin_digraph.min_cost_awalk} with different
  assumptions.\<close>
lemma (in fin_digraph) min_cost_awalk2:
  assumes "\<mu> w a b \<noteq> \<infinity>" "\<mu> w a b \<noteq> -\<infinity>"
  shows "\<exists>p. apath a p b \<and> \<mu> w a b = awalk_cost w p"
proof -
  from assms have "a \<rightarrow>\<^sup>* b" using \<mu>_reach_conv by auto
  then show ?thesis using no_neg_cyc_reach_imp_path
    using assms(2) neg_cycle_imp_inf_\<mu> by blast
qed

lemma (in fin_digraph) sp_triangle:
  assumes "a \<in> verts G" "b \<in> verts G" "c \<in> verts G"
      and w_non_neg: "\<forall>e \<in> arcs G. w e \<ge> 0"
    shows "\<mu> w a c \<le> \<mu> w a b + \<mu> w b c"
proof(rule ccontr)
  assume "\<not> \<mu> w a c \<le> \<mu> w a b + \<mu> w b c"
  then have *: "\<mu> w a c > \<mu> w a b + \<mu> w b c"
    using not_less by blast
  consider (minf) "\<mu> w a c = -\<infinity>" | (pinf) "\<mu> w a c = \<infinity>"
    | (fin) "\<mu> w a c \<noteq> -\<infinity> \<and> \<mu> w a c \<noteq> \<infinity>" by auto
  then show "False"
  proof(cases)
    case minf
    with * show ?thesis by auto
  next
    case pinf
    with * have "\<mu> w a b < \<infinity>" "\<mu> w b c < \<infinity>"
      by auto
    then have "a \<rightarrow>\<^sup>* b" "b \<rightarrow>\<^sup>* c" using \<mu>_reach_conv by auto
    then have "a \<rightarrow>\<^sup>* c" using reachable_trans by blast
    then have "\<mu> w a c \<noteq> \<infinity>" using \<mu>_reach_conv by auto
    with pinf show ?thesis by simp
  next
    case fin
    with * have "\<mu> w a b \<noteq> \<infinity>" "\<mu> w b c \<noteq> \<infinity>" by auto
    moreover
    from fin * have "\<mu> w a b \<noteq> -\<infinity>" "\<mu> w b c \<noteq> -\<infinity>"
      using w_non_neg sp_non_neg_if_w_non_neg by auto
    ultimately have
      "\<exists>p. awalk a p b \<and> awalk_cost w p = \<mu> w a b"
      "\<exists>p. awalk b p c \<and> awalk_cost w p = \<mu> w b c"
      using min_cost_awalk2 by (fastforce intro: awalkI_apath)+
    then obtain p1 p2 where
      "awalk a p1 b" "awalk_cost w p1 = \<mu> w a b" and
      "awalk b p2 c" "awalk_cost w p2 = \<mu> w b c" by blast
    then have "awalk a (p1@p2) c \<and> awalk_cost w (p1@p2) = \<mu> w a b + \<mu> w b c"
      by (auto intro: awalk_appendI) (metis plus_ereal.simps(1))
    then show ?thesis
      using min_cost_le_walk_cost \<open>\<not> \<mu> w a c \<le> \<mu> w a b + \<mu> w b c\<close>
      by metis
  qed
qed

section \<open>Root and Leaf\<close>

context pre_digraph
begin

definition root :: "'a \<Rightarrow> bool" where
  "root v \<equiv> v \<in> verts G \<and> in_arcs G v = {}"

lemma rootI:
  assumes "v \<in> verts G" "in_arcs G v = {}"
  shows "root v"
  using assms unfolding root_def by blast

lemma root_in_vertsD[simp]: "root v \<Longrightarrow> v \<in> verts G"
  unfolding root_def by simp

lemma root_in_arcsD[simp]: "root v \<Longrightarrow> in_arcs G v = {}"
  unfolding root_def by simp

lemma root_in_degree_0[simp]: "root v \<Longrightarrow> in_degree G v = 0"
  unfolding root_def in_degree_def by auto

lemma rootE[elim]:
  assumes "root v"
  obtains "v \<in> verts G" "in_arcs G v = {}"
  using assms unfolding root_def by auto

lemma not_root_if_dominated: "u \<rightarrow>\<^bsub>G\<^esub> v \<Longrightarrow> \<not> root v"
  unfolding root_def in_arcs_def by auto

lemma dominated_if_not_root:
  "v \<in> verts G \<Longrightarrow> \<not> root v \<Longrightarrow> \<exists>u. u \<rightarrow>\<^bsub>G\<^esub> v"
  unfolding root_def in_arcs_def using arcs_ends_conv by blast

lemma not_root_if_reachable1: "u \<rightarrow>\<^sup>+\<^bsub>G\<^esub> v \<Longrightarrow> \<not> root v"
  by (meson not_root_if_dominated tranclD2)

lemma subgraph_root_iff_if_root:
  assumes "subgraph H G"
  assumes "root v"
  shows "pre_digraph.root H v \<longleftrightarrow> v \<in> verts H"
  using assms unfolding pre_digraph.root_def subgraph_def
  using compatible_head by fastforce

definition leaf :: "'a \<Rightarrow> bool" where
  "leaf v \<equiv> v \<in> verts G \<and> out_arcs G v = {}"

lemma leaf_in_vertsD[simp]: "leaf v \<Longrightarrow> v \<in> verts G"
  unfolding leaf_def by simp

lemma leaf_out_arcsD[simp]: "leaf v \<Longrightarrow> out_arcs G v = {}"
  unfolding leaf_def by simp

lemma leaf_out_degree_zero[simp]: "leaf v \<Longrightarrow> out_degree G v = 0"
  unfolding leaf_def out_degree_def by auto

lemma not_leaf_if_dominates:
  "v \<rightarrow> v' \<Longrightarrow> \<not> leaf v"
  unfolding leaf_def by force

lemma leafE[elim]:
  assumes "leaf v"
  obtains "v \<in> verts G" "out_arcs G v = {}"
  using assms unfolding leaf_def by auto

end

end