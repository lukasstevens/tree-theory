theory LCA_Directed_Tree
  imports LCA Directed_Tree "HOL-Library.Sublist"
begin

context directed_tree
begin

lemma in_awalk_verts_if_awalk:
  assumes "awalk x pxy y"
      and "x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y"
    shows "v \<in> set (awalk_verts x pxy)"
proof -
  from assms obtain pxv pvy where pxy: "awalk x pxv v" and pvy: "awalk v pvy y"
    using reachable_awalk by auto
  with assms have "pxy = pxv @ pvy"
    using unique_awalk_All by force
  with pxy pvy show ?thesis
    using set_awalk_verts_append by auto
qed

lemma lca_same_if_reachable:
  assumes "x \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y"
  shows "lca x x y"
proof -
  from assms obtain pxy where "awalk x pxy y"
    using reachable_awalk by blast
  note in_awalk_verts_if_awalk[OF this]
  have "\<not> v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x" if "x \<rightarrow>\<^sup>+\<^bsub>T\<^esub> v" "v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y" for v
    using that
    using not_reachable1_if_flip_reachable1 by blast
  with assms \<open>awalk x pxy y\<close> show "lca x x y"
    unfolding lca_def pre_digraph.leaf_def
    using in_arcs_imp_in_arcs_ends by fastforce
qed

lemma one_not_reachable_if_reachable1_from_lca:
  assumes "awalk ca (ax # px) x" "awalk ca (ay # py) y"
  assumes "ax \<noteq> ay"
  assumes "ca \<rightarrow>\<^sup>+\<^bsub>T\<^esub> v"
  shows "\<not> (v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x \<and> v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y)"
proof
  presume "v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x" "v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y"
  then obtain pvx pvy where
    pvx: "awalk v pvx x" and pvy: "awalk v pvy y"
    using reachable_awalk by fastforce
  from \<open>ca \<rightarrow>\<^sup>+\<^bsub>T\<^esub> v\<close> obtain pcav where pcav: "awalk ca pcav v" "pcav \<noteq> []"
    using reachable1_awalk by auto
  with pvx pvy have "awalk ca (pcav @ pvx) x" "awalk ca (pcav @ pvy) y"
    by simp_all
  with assms(1,2) have "ax # px = pcav @ pvx" "ay # py = pcav @ pvy"
    using unique_awalk_All by blast+
  with \<open>pcav \<noteq> []\<close> \<open>ax \<noteq> ay\<close> show False
    by (cases pcav) auto
qed safe

lemma lca_last_longest_common_prefix_awalk_verts:
  assumes "awalk ca p1 x" "awalk ca p2 y"
  defines "p \<equiv> longest_common_prefix (awalk_verts ca p1) (awalk_verts ca p2)"
  shows "lca (last p) x y"
  using assms unfolding p_def
proof(induction p1 p2 arbitrary: ca rule: longest_common_prefix.induct)
  case (1 a as b bs)
  with 1 have awalk: "awalk (head T a) as x" "awalk (head T b) bs y"
    using awalk_Cons_iff by auto
  then show ?case
  proof(cases "a = b")
    case True
    note "1.hyps"(1)[OF True awalk[unfolded True]]
    with True awalk show ?thesis
      by (cases as; cases bs) (auto simp: awalk_Cons_iff)
  next
    case False
    with 1 have "head T a \<noteq> head T b"
      by (meson awalk_Cons_iff two_in_arcs_contr)
    moreover note one_not_reachable_if_reachable1_from_lca[OF "1.hyps"(2,3) False]
    then have "\<not> (v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x \<and> v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y)" if "ca \<rightarrow>\<^sup>+\<^bsub>T\<^esub> v" for v
      using that by blast
    with "1.hyps"(2,3)[THEN reachable_awalkI] have "lca ca x y"
      unfolding lca_def using in_arcs_imp_in_arcs_ends 
      by (fastforce simp: pre_digraph.leaf_def)
    ultimately show ?thesis
      using 1 awalk_Cons_iff by (cases as; cases bs) auto
  qed
next
  case ("2_1" pcay)
  then show ?case
    by (cases pcay) (auto intro: lca_same_if_reachable reachable_awalkI simp: awalk_Nil_iff)
next
  case ("2_2" pcax)
  then show ?case
    using lca_same_if_reachable[THEN lca_symmetric]
    by (cases pcax) (auto intro: reachable_awalkI simp: awalk_Nil_iff)
qed

lemma disjoint_tl_awalk_verts_if_awalk_lca:
  assumes "lca ca x y" "x \<noteq> y"
  assumes "awalk ca px x" "awalk ca py y"
  shows "set (tl (awalk_verts ca px)) \<inter> set (tl (awalk_verts ca py)) = {}"
proof(cases "ca = x \<or> ca = y")
  case True
  with assms have "px = [] \<or> py = []"
    using apath_if_awalk apath_nonempty_ends by blast
  then show ?thesis
    by auto
next
  case False
  with assms obtain ax px' ay ay' where
    px: "px = ax # px'" and py: "py = ay # ay'"
    by (metis awalk_empty_ends neq_Nil_conv)
  have "ax \<noteq> ay"
  proof
    assume "ax = ay"
    with assms px py have "head T ax \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x" "head T ax \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y"
      by (auto simp: awalk_Cons_iff in_arcs_imp_in_arcs_ends intro: reachable_awalkI)
    moreover from assms px have "ax \<in> out_arcs T ca"
      using awalk_Cons_iff by simp
    ultimately have "ax \<in> out_arcs (T \<restriction> {ca. ca \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x \<and> ca \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y}) ca"
      using assms unfolding induce_subgraph_def by auto
    then have "\<not> lca ca x y"
      unfolding lca_def Let_def pre_digraph.leaf_def by blast
    with assms show False
      by blast
  qed
  note one_not_reachable =
    one_not_reachable_if_reachable1_from_lca[OF assms(3,4)[unfolded px py] \<open>ax \<noteq> ay\<close>]
  show ?thesis
  proof(rule ccontr)
    assume "set (tl (awalk_verts ca px)) \<inter> set (tl (awalk_verts ca py)) \<noteq> {}"
    then obtain v where v:
      "v \<in> set (tl (awalk_verts ca px))" "v \<in> set (tl (awalk_verts ca py))"
      by blast
    with awalk_verts_reachable_from assms have "ca \<rightarrow>\<^sup>*\<^bsub>T\<^esub> v"
      by (cases px) auto
    moreover from v assms have "ca \<noteq> v"
      by (cases px; cases py) (auto simp: apath_Cons_iff dest: apath_if_awalk)
    ultimately have "ca \<rightarrow>\<^sup>+\<^bsub>T\<^esub> v"
      using reachable_neq_reachable1 by blast
    with one_not_reachable v show False
      using assms awalk_verts_reachable_to
      by (meson awalk_verts_non_Nil list.set_sel(2))
  qed
qed

lemma disjoint_awalk_if_awalk_lca:
  assumes "lca ca x y" "x \<noteq> y"
  assumes "awalk ca px x" "awalk ca py y"
  shows "set px \<inter> set py = {}"
proof -
  from assms have
    "tl (awalk_verts ca px) = map (head T) px"
    "tl (awalk_verts ca py) = map (head T) py"
    using awalk_verts_conv' by auto
  note disjoint_tl_awalk_verts_if_awalk_lca[OF assms, unfolded this]
  then show ?thesis
    by auto
qed

lemma longest_common_prefix_awalk_verts_eq:
  assumes "awalk u p1 v1" "awalk u p2 v2"
  shows "u # map (head T) (longest_common_prefix p1 p2) =
    longest_common_prefix (awalk_verts u p1) (awalk_verts u p2)"
  using assms
proof(induction p1 p2 arbitrary: u rule: longest_common_prefix.induct)
  case (1 x xs y ys)
  then have "head T x \<noteq> head T y" if "x \<noteq> y"
    using that
    by (metis awalk_Cons_iff two_in_arcs_contr)
  with 1 show ?case
    by (cases xs; cases ys) (auto simp: awalk_Cons_iff)
next
  case ("2_1" puv2)
  then show ?case
    by (cases puv2) (auto simp: awalk_Nil_iff)
next
  case ("2_2" puv1)
  then show ?case
    by (cases puv1) (auto simp: awalk_Nil_iff)
qed

end

end