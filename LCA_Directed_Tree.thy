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

lemma
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


lemma  
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
      using awalk_Cons_iff two_in_arcs_contr by force
    moreover have "\<not> (v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x \<and> v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y)" if "ca \<rightarrow>\<^sup>+\<^bsub>T\<^esub> v" for v
    proof
      presume "v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> x" "v \<rightarrow>\<^sup>*\<^bsub>T\<^esub> y"
      then obtain pvx pvy where
        pvx: "awalk v pvx x" and pvy: "awalk v pvy y"
        using reachable_awalk by fastforce
      from that obtain pcav where pcav: "awalk ca pcav v" "pcav \<noteq> []"
        using reachable1_awalk by auto
      with pvx pvy have "awalk ca (pcav @ pvx) x" "awalk ca (pcav @ pvy) y"
        by simp_all
      with 1 have "a # as = pcav @ pvx" "b # bs = pcav @ pvy"
        using unique_awalk_All by blast+
      with \<open>pcav \<noteq> []\<close> False show False
        by (cases pcav) auto
    qed safe
    with "1.hyps"(2,3)[THEN reachable_awalkI] have "lca ca x y"
      unfolding lca_def using in_arcs_imp_in_arcs_ends 
      by (fastforce simp: pre_digraph.leaf_def)
    ultimately show ?thesis
      using \<open>a \<noteq> b\<close> 1 awalk_Cons_iff by (cases as; cases bs) auto
  qed
next
  case ("2_1" pcay)
  then show ?case
    apply(cases pcay)
     apply(auto simp: awalk_Nil_iff)
    
    find_theorems "awalk _ [] _"
    sorry
next
  case ("2_2" uu)
  then show ?case apply(simp) sorry
qed
    
end

end