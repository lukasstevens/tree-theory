theory Directed_Forest
  imports
    "Graph_Theory.Graph_Theory"
    "Graph_Theory_Batteries"
    "HOL-Library.Sublist"
begin

locale directed_forest = wf_digraph F for F +
  assumes
    Ex1_root_reachable: "v \<in> verts F \<Longrightarrow> \<exists>!r. root r \<and> r \<rightarrow>\<^sup>*\<^bsub>F\<^esub> v" and
    Uniq_awalk: "\<exists>\<^sub>\<le>\<^sub>1p. awalk v p v'"

locale fin_directed_forest = directed_forest F + fin_digraph F for F

context directed_forest
begin

lemma unique_awalk:
  assumes "awalk u p v"
  shows "\<forall>p'. awalk u p' v \<longrightarrow> p' = p"
  using assms Uniq_awalk unfolding Uniq_def by blast

theorem NEx_cycle: "\<nexists>c. cycle c"
  unfolding cycle_def using unique_awalk
  by (meson append_self_conv2 awalk_appendI)

lemma apath_if_awalk: "awalk r p v \<Longrightarrow> apath r p v"
  unfolding apath_def
  using awalk_cyc_decompE' closed_w_imp_cycle NEx_cycle by blast

lemma distinct_awalk_verts:
  "awalk u p v \<Longrightarrow> distinct (awalk_verts u p)"
  using apath_if_awalk unfolding apath_def by blast

lemma not_reachable1_if_flip_reachable1:
  "x \<rightarrow>\<^sup>+\<^bsub>F\<^esub> y \<Longrightarrow> \<not> y \<rightarrow>\<^sup>+\<^bsub>F\<^esub> x"
proof
  assume "x \<rightarrow>\<^sup>+\<^bsub>F\<^esub> y" "y \<rightarrow>\<^sup>+\<^bsub>F\<^esub> x"
  then obtain p where "p \<noteq> []" "awalk x p x"
    by (meson reachable1_awalk trancl_trans)
  with NEx_cycle show False
    unfolding cycle_def
    by (meson apath_ends apath_if_awalk)
qed

lemma not_in_awalk_verts_if_dominated:
  "\<lbrakk> u \<rightarrow>\<^bsub>F\<^esub> v; awalk r p u \<rbrakk> \<Longrightarrow> v \<notin> set (awalk_verts r p)"
  using awalk_verts_reachable_to not_reachable1_if_flip_reachable1
  by blast

sublocale loopfree: loopfree_digraph F
proof(standard, rule ccontr)
  fix e assume arc: "e \<in> arcs F" and loop: "\<not> tail F e \<noteq> head F e"
  then have "cycle [e]"
    unfolding cycle_conv
    using arc_implies_awalk by force
  with NEx_cycle show "False" by blast
qed

sublocale nomulti: nomulti_digraph F
proof(standard, rule ccontr, goal_cases)
  case (1 e1 e2)
  let ?u = "tail F e1" and ?v = "head F e1"
  from unique_awalk Ex1_root_reachable obtain r p where
    r: "root r" and p: "awalk r p ?u"
    using 1 tail_in_verts by (metis mem_Collect_eq reachable_awalk)
  with 1 have "awalk r (p@[e1]) ?v" and "awalk r (p@[e2]) ?v"
    unfolding arc_to_ends_def
    using arc_implies_awalk by (fastforce)+

  with unique_awalk show "False"
    using \<open>e1 \<noteq> e2\<close> by blast
qed

lemma two_in_arcs_contr:
  assumes "e1 \<in> arcs F" "e2 \<in> arcs F" and "e1 \<noteq> e2" and "head F e1 = head F e2"
  shows "False"
proof -
  from Ex1_root_reachable assms obtain r
    where "r \<rightarrow>\<^sup>*\<^bsub>F\<^esub> tail F e1" and "r \<rightarrow>\<^sup>*\<^bsub>F\<^esub> tail F e2"
    by (metis in_arcs_imp_in_arcs_ends reachable_adj_trans reachable_in_vertsE tail_in_verts)
  with assms obtain p1 p2 where
    "awalk r (p1@[e1]) (head F e1)" and "awalk r (p2@[e2]) (head F e1)"
    unfolding in_arcs_def
    using reachable_awalk arc_implies_awalk by (metis awalk_appendI)
  with Ex1_root_reachable \<open>e1 \<noteq> e2\<close> show "False"
    by (meson append1_eq_conv unique_awalk)
qed

lemma finite_in_arcs[simp]:
  "finite (in_arcs F v)"
proof(rule ccontr)
  assume "\<not> finite (in_arcs F v)"
  then obtain e1 e2
    where e1_e2: "e1 \<in> in_arcs F v" "e2 \<in> in_arcs F v" "e1 \<noteq> e2"
    by (metis finite.emptyI finite_insert finite_subset insertI1 subsetI)
  with two_in_arcs_contr show "False" unfolding in_arcs_def by auto
qed

lemma in_degree_1_if_not_root: "\<lbrakk> v \<in> verts F; \<not> root v \<rbrakk> \<Longrightarrow> in_degree F v = 1"
proof(rule ccontr)
  assume "\<not> root v" and "v \<in> verts F" and "in_degree F v \<noteq> 1"
  have "in_degree F v \<noteq> 0"
  proof
    assume "in_degree F v = 0"
    with \<open>v \<in> verts F\<close> have "root v"
      unfolding root_def in_degree_def by simp
    with \<open>\<not> root v\<close> show False
      by blast
  qed
  moreover
  have "\<not> in_degree F v \<ge> 2"
  proof
    assume in_deg_ge_2: "in_degree F v \<ge> 2"
    have "\<exists>e1 e2. e1 \<in> in_arcs F v \<and> e2 \<in> in_arcs F v \<and> e1 \<noteq> e2"
    proof(cases "in_arcs F v = {}")
      case True
      then show ?thesis using in_deg_ge_2[unfolded in_degree_def] by simp
    next
      case False
      then obtain e1 where "e1 \<in> in_arcs F v" by blast
      then have "card (in_arcs F v) = 1" if "\<forall>e2 \<in> in_arcs F v. e1 = e2"
        using that by(auto simp: card_Suc_eq[where ?A="(in_arcs F v)"])
      then show ?thesis
        using in_deg_ge_2[unfolded in_degree_def] \<open>e1 \<in> in_arcs F v\<close> by force
    qed
    with two_in_arcs_contr show "False" unfolding in_arcs_def by auto
  qed
  ultimately show "False" using \<open>in_degree F v \<noteq> 1\<close> by linarith
qed

lemma not_root_if_in_degree_1: "\<lbrakk> v \<in> verts F; in_degree F v = 1 \<rbrakk> \<Longrightarrow> \<not> root v"
  by auto

corollary in_degree_1_iff: "v \<in> verts F \<Longrightarrow> \<not> root v \<longleftrightarrow> in_degree F v = 1"
  using in_degree_1_if_not_root not_root_if_in_degree_1 by blast

lemma Ex_in_arc: "\<lbrakk> v \<in> verts F; \<not> root v \<rbrakk> \<Longrightarrow> \<exists>e. in_arcs F v = {e}"
  using in_degree_1_if_not_root unfolding in_degree_def
  by (auto simp: card_Suc_eq)

lemma in_arcs_eq_empty_or_singleton:
  "in_arcs F v = {} \<or> (\<exists>a. in_arcs F v = {a})"
  using Ex_in_arc by (cases "v \<in> verts F") auto

lemma (in fin_digraph) directed_forest_if_in_arcs_and_NEx_cycle:
  assumes "\<forall>v \<in> verts G. in_arcs G v = {} \<or> (\<exists>a. in_arcs G v = {a})"
  assumes "\<nexists>c. cycle c"
  shows "directed_forest G"
proof(unfold_locales)
  show Uniq_awalk: "\<exists>\<^sub>\<le>\<^sub>1 p. awalk u p v" for u v
  proof(rule ccontr)
    assume "\<not> (\<exists>\<^sub>\<le>\<^sub>1 p. awalk u p v)"
    then obtain p1 p2 where p1: "awalk u p1 v" and p2: "awalk u p2 v" and "p1 \<noteq> p2"
      unfolding Uniq_def by blast
    then obtain pp1 pp2 pcs where
      p1_eq: "p1 = pp1 @ pcs" and p2_eq: "p2 = pp2 @ pcs" and
      pp1_pp2_cases: "pp1 = [] \<or> pp2 = [] \<or> last pp1 \<noteq> last pp2"
      using longest_common_suffix by blast
    then show False
    proof(cases "pp1 = [] \<or> pp2 = []")
      case True
      with p1 p2 p1_eq p2_eq \<open>p1 \<noteq> p2\<close> obtain p where "awalk u p u" "p \<noteq> []"
        using awalk_ends by simp metis
      with \<open>\<nexists>c. cycle c\<close> show False
        using closed_w_imp_cycle[unfolded closed_w_def] by blast
    next
      case False
      with pp1_pp2_cases have "pp1 \<noteq> []" "pp2 \<noteq> []" "last pp1 \<noteq> last pp2"
        by blast+
      moreover from this p1 p2 p1_eq p2_eq have
        "head G (last pp1) = head G (last pp2)"
        by simp (metis awalk_ends awalk_verts_conv last_snoc)
      moreover from False pp1_pp2_cases p1 p2 p1_eq p2_eq have
        "last pp1 \<in> arcs G" "last pp2 \<in> arcs G"
        by (meson awalk_Cons_iff awalk_append_iff awalk_not_Nil_butlastD(2))+
      ultimately have "{last pp1, last pp2} \<subseteq> in_arcs G (head G (last pp1))"
        unfolding in_arcs_def by auto
      moreover from this have "head G (last pp1) \<in> verts G"
        by simp
      ultimately show False
        using assms \<open>last pp1 \<noteq> last pp2\<close> by fastforce
    qed
  qed

  show "\<exists>!r. root r \<and> r \<rightarrow>\<^sup>* v" if "v \<in> verts G" for v
  proof -
    have False if "root r1" "root r2" "r1 \<rightarrow>\<^sup>* v" "r2 \<rightarrow>\<^sup>* v" "r1 \<noteq> r2" for r1 r2
    proof -
      from that have "r1 \<rightarrow>\<^sup>+ v" "r2 \<rightarrow>\<^sup>+ v"
        using not_root_if_reachable1 by auto
      with that obtain p1 p2 where
        p1: "awalk r1 p1 v" and p2: "awalk r2 p2 v" and "p1 \<noteq> []" "p2 \<noteq> []"
        by (meson reachable1_awalk)
      then obtain pp1 pp2 pcs where
        p1_eq: "p1 = pp1 @ pcs" and p2_eq: "p2 = pp2 @ pcs" and
        pp1_pp2_cases: "pp1 = [] \<or> pp2 = [] \<or> last pp1 \<noteq> last pp2"
        using longest_common_suffix by blast
      from that p1 p2 have "pp1 \<noteq> []" "pp2 \<noteq> []"
        unfolding p1_eq p2_eq awalk_append_iff
        by (metis awalk_ends not_root_if_reachable1 reachable1_awalkI)+
      moreover from this p1 p2 p1_eq p2_eq have
        "head G (last pp1) = head G (last pp2)"
        by simp (metis awalk_ends awalk_verts_conv last_snoc)
      moreover from p1 p2 p1_eq p2_eq \<open>pp1 \<noteq> []\<close> \<open>pp2 \<noteq> []\<close> have
        "last pp1 \<in> arcs G" "last pp2 \<in> arcs G"
        by (meson awalk_Cons_iff awalk_append_iff awalk_not_Nil_butlastD(2))+
      ultimately have "{last pp1, last pp2} \<subseteq> in_arcs G (head G (last pp1))"
        unfolding in_arcs_def by auto
      moreover from this have "head G (last pp1) \<in> verts G"
        by simp
      ultimately show False
        using assms \<open>pp1 \<noteq> []\<close> \<open>pp2 \<noteq> []\<close> pp1_pp2_cases by fastforce
    qed
    moreover have False if not_root: "\<forall>r. r \<rightarrow>\<^sup>* v \<longrightarrow> \<not> root r"
    proof -
      have "finite {r. r \<rightarrow>\<^sup>* v}"
        using finite_verts reachable_in_verts
        by (metis infinite_super mem_Collect_eq subsetI)
      then show False
        using that \<open>v \<in> verts G\<close>
      proof(induction "card {r. r \<rightarrow>\<^sup>* v}" arbitrary: v rule: less_induct)
        case less
        then have "v \<in> {r. r \<rightarrow>\<^sup>* v}"
          by auto
        from less have "\<not> root v"
          by blast
        with assms less obtain u where "u \<rightarrow> v" 
          unfolding root_def 
          by (metis in_arcs_imp_in_arcs_ends in_in_arcs_conv insertCI)
        then have reachable_u_subs: "{r. r \<rightarrow>\<^sup>* u} \<subseteq> {r. r \<rightarrow>\<^sup>* v}"
          using reachable_adj_trans by blast
        then show ?case
        proof(cases "{r. r \<rightarrow>\<^sup>* u} = {r. r \<rightarrow>\<^sup>* v}")
          case True
          with reachable_u_subs \<open>v \<in> {r. r \<rightarrow>\<^sup>* v}\<close> \<open>u \<rightarrow> v\<close> have "u \<rightarrow>\<^sup>+ u"
            using reachable1_reachable_trans by blast
          then obtain p where "awalk u p u" "p \<noteq> []"
            using reachable1_awalk by blast
          with \<open>\<nexists>c. cycle c\<close> show ?thesis
            using closed_w_imp_cycle[unfolded closed_w_def] by auto
        next
          case False
          with less.prems reachable_u_subs have "card {r. r \<rightarrow>\<^sup>* u} < card {r. r \<rightarrow>\<^sup>* v}"
            by (metis psubsetI psubset_card_mono)
          moreover from reachable_u_subs less have "finite {r. r \<rightarrow>\<^sup>* u}"
            using finite_subset by blast
          ultimately show False
            using less.prems \<open>u \<rightarrow> v\<close> 
            by (intro less.hyps) (blast intro: reachable_adj_trans adj_in_verts)+
        qed
      qed
    qed
    ultimately show ?thesis
      by blast
  qed
qed

lemma (in fin_directed_forest) directed_forest_if_subgraph:
  assumes "subgraph F' F"
  shows "fin_directed_forest F'"
proof -
  from assms interpret F': fin_digraph F'
    by (rule fin_digraph_subgraph)
  interpret F': directed_forest F'
  proof (rule F'.directed_forest_if_in_arcs_and_NEx_cycle)
    from assms NEx_cycle show "\<nexists>c. F'.cycle c"
      using subgraph_cycle by blast

    show "\<forall>v \<in> verts F'. in_arcs F' v = {} \<or> (\<exists>a. in_arcs F' v = {a})"
    proof
      fix v assume "v \<in> verts F'"
      with assms have "in_arcs F' v \<subseteq> in_arcs F v"
        using compatible_head by fastforce
      with \<open>v \<in> verts F'\<close> show "in_arcs F' v = {} \<or> (\<exists>a. in_arcs F' v = {a})"
        using in_arcs_eq_empty_or_singleton
        by (metis subset_empty subset_singleton_iff)
    qed
  qed
  show ?thesis
    by unfold_locales
qed

definition "induced_subtree r \<equiv> F \<restriction> {v. r \<rightarrow>\<^sup>*\<^bsub>F\<^esub> v}"

lemma subgraph_induced_subtree:
  "subgraph (induced_subtree r) F"
  unfolding induced_subtree_def using reachable_in_verts
  by (intro subgraph_induce_subgraphI) blast

lemma wf_digraph_induced_subtree:
  "wf_digraph (induced_subtree r)"
  using subgraph_induced_subtree by blast

lemma verts_induced_subtree:
  "verts (induced_subtree r) = {v. r \<rightarrow>\<^sup>*\<^bsub>F\<^esub> v}"
  unfolding induced_subtree_def by simp

lemma
  tail_induced_subtree: "tail (induced_subtree r) e = tail F e" and
  head_induced_subtree: "head (induced_subtree r) e = head F e" and
  arc_to_ends_induced_subtree:
    "arc_to_ends (induced_subtree r) e = arc_to_ends F e"
  using induced_subtree_def by fastforce+

lemmas awalk_if_awalk_induced_subtree =
  subgraph_awalk_imp_awalk[OF _ subgraph_induced_subtree]

lemmas reachable_root_induced_subtree_if_reachable_root =
  induce_reachable_preserves_paths[folded induced_subtree_def]

lemma awalk_induced_subtree_if_awalk:
  assumes "awalk r p v"
  shows "pre_digraph.awalk (induced_subtree r) r p v"
proof -
  from assms have "r \<rightarrow>\<^sup>*\<^bsub>induced_subtree r\<^esub> v"
    using reachable_awalk reachable_root_induced_subtree_if_reachable_root
    by blast
  then obtain p' where "pre_digraph.awalk (induced_subtree r) r p' v"
    using wf_digraph.reachable_awalk[OF wf_digraph_induced_subtree] by blast
  moreover from this have "awalk r p' v"
    using awalk_if_awalk_induced_subtree by blast
  ultimately show ?thesis
    using assms Uniq_awalk Uniq_D by metis
qed

(*
lemma directed_tree_induced_subtree:
  assumes "r \<in> verts F"
  shows "directed_tree (induced_subtree r) r"
proof -
  interpret T: wf_digraph "induced_subtree r"
    using induced_subtree_def by auto
  from Uniq_awalk have "\<exists>\<^sub>\<le>\<^sub>1p. T.awalk v p v'" for v v'
    unfolding Uniq_def using awalk_if_awalk_induced_subtree by blast
  with assms roots_subs_verts show ?thesis
    using reachable_root_induced_subtree_if_reachable_root
    by (intro T.directed_treeI') (auto simp: verts_induced_subtree)
qed
*)

end

lemma (in fin_directed_forest) fin_digraph_induced_subtree:
  "fin_digraph (induced_subtree r)"
  by (simp add: fin_digraph_subgraph subgraph_induced_subtree)

end