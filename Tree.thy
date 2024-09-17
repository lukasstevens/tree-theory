theory Tree
  imports Directed_Tree
begin

text \<open>
  We illustrate that definitions of \<^const>\<open>tree\<close> and \<^const>\<open>forest\<close> are incorrect by
  introducing the directed acyclic graph below that fulfils both of these predicates.
\<close>

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

end
