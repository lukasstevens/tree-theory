theory Graph_Diameter
  imports
    "Graph_Theory.Digraph_Component" "Graph_Theory.Shortest_Path"
    "Graph_Theory_Batteries"
begin

section \<open>Diameter and finite diameter\<close>
text \<open>
The diameter is defined as the longest shortest path in the corresponding graph. If there is no path
between any two vertices in the graph, then the diameter is infinite.
We also make use of the notion of a @{text fin_diameter} which only considers the shortest path
between connected nodes.
\<close>

context wf_digraph
begin

definition sp_costs :: "'b weight_fun \<Rightarrow> ereal set" where
  "sp_costs f = {c | u v c. u \<in> verts G \<and> v \<in> verts G \<and> \<mu> f u v = c}"

definition diameter :: "'b weight_fun \<Rightarrow> ereal" where
  "diameter f = Sup (sp_costs f)"

definition fin_sp_costs :: "'b weight_fun \<Rightarrow> ereal set" where
  "fin_sp_costs f = {c | u v c. u \<in> verts G \<and> v \<in> verts G \<and> \<mu> f u v = c \<and> c < \<infinity>}"

definition fin_diameter :: "'b weight_fun \<Rightarrow> ereal" where
  "fin_diameter f = Sup (fin_sp_costs f)"


subsection \<open>In general graphs\<close>

lemma diameter_eq_minf_if_verts_empty: "verts G = {} \<Longrightarrow> diameter w = -\<infinity>"
  unfolding diameter_def sp_costs_def
  by (simp add: bot_ereal_def)

lemma fin_diameter_eq_minf_if_verts_empty: "verts G = {} \<Longrightarrow> fin_diameter w = -\<infinity>"
  unfolding fin_diameter_def fin_sp_costs_def
  by (simp add: bot_ereal_def)

lemma diameter_eq_fin_diameter_if_diameter_lt_inf:
  "diameter f < \<infinity> \<Longrightarrow> diameter f = fin_diameter f"
proof -
  assume "diameter f < \<infinity>"
  then have "\<infinity> \<notin> sp_costs f"
    unfolding diameter_def using Sup_eq_PInfty by auto
  then have "sp_costs f = fin_sp_costs f"
    unfolding sp_costs_def fin_sp_costs_def by auto
  then show ?thesis
    unfolding diameter_def fin_diameter_def by simp
qed

lemma fin_diameter_lowerB:
  "\<lbrakk> u \<in> verts G; v \<in> verts G; \<mu> w u v < \<infinity>\<rbrakk>
  \<Longrightarrow> fin_diameter w \<ge> \<mu> w u v"
  unfolding fin_diameter_def fin_sp_costs_def
  by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq)

lemma diameter_lowerB:
  "\<lbrakk> u \<in> verts G; v \<in> verts G \<rbrakk>
  \<Longrightarrow> diameter w \<ge> \<mu> w u v"
  unfolding diameter_def sp_costs_def
  by (metis (mono_tags, lifting) Sup_upper mem_Collect_eq)


subsection \<open>In finite graphs\<close>

lemma (in fin_digraph) finite_sp_costs: "finite (sp_costs f)"
  unfolding sp_costs_def by auto

lemma (in fin_digraph) finite_fin_sp_costs: "finite (fin_sp_costs f)"
  unfolding fin_sp_costs_def by auto

lemma (in fin_digraph) ex_sp_eq_dia:
  "verts G \<noteq> {} \<Longrightarrow> \<exists>u \<in> verts G. \<exists>v \<in> verts G. \<mu> f u v = diameter f"
proof -
  assume "verts G \<noteq> {}"
  then have "sp_costs f \<noteq> {}"
    unfolding sp_costs_def using \<mu>_reach_conv by fastforce

  with finite_sp_costs have "\<exists>c \<in> sp_costs f. c = diameter f"
    unfolding diameter_def by (auto simp: max_def intro!: finite_Sup_in)
  then show "?thesis"
    unfolding diameter_def sp_costs_def by auto
qed

text \<open>Analogous to the proof of @{thm fin_digraph.ex_sp_eq_dia}.\<close>
lemma (in fin_digraph) ex_sp_eq_fin_diameter:
  "verts G \<noteq> {} \<Longrightarrow> \<exists>u \<in> verts G. \<exists>v \<in> verts G. \<mu> f u v = fin_diameter f"
proof -
  assume "verts G \<noteq> {}"
  then have "fin_sp_costs f \<noteq> {}"
    unfolding fin_sp_costs_def using \<mu>_reach_conv by fastforce

  with finite_fin_sp_costs have "\<exists>c \<in> fin_sp_costs f. c = fin_diameter f"
    unfolding fin_diameter_def
    by (auto simp: max_def intro!: finite_Sup_in)
  then show "?thesis" 
    unfolding fin_diameter_def fin_sp_costs_def by auto
qed


lemma (in fin_digraph) fin_diameter_lt_inf: "fin_diameter f < \<infinity>"
proof(rule ccontr)
  fix f assume dia_infty: "\<not> fin_diameter f < \<infinity>"

  then have infty_cont: "\<infinity> \<in> fin_sp_costs f" if *: "fin_sp_costs f \<noteq> {}"
    unfolding fin_diameter_def using *
    by (metis ereal_infty_less(1) finite_fin_sp_costs infinite_growing less_Sup_iff)

  then show "False"
  proof(cases "fin_sp_costs f = {}")
    case True
    then have "fin_diameter f = -\<infinity>"
      unfolding fin_diameter_def by (simp add: bot_ereal_def)
    with dia_infty show ?thesis by simp
  next
    case False
    from infty_cont[OF this] dia_infty show ?thesis
      unfolding fin_diameter_def fin_sp_costs_def by auto
  qed
qed

lemma (in fin_digraph) ex_min_apath_eq_fin_dia:
  "\<lbrakk> verts G \<noteq> {}; \<forall>e \<in> arcs G. f e \<ge> 0 \<rbrakk>
  \<Longrightarrow> \<exists>u \<in> verts G. \<exists>v \<in> verts G. \<exists>p. apath u p v \<and> awalk_cost f p = fin_diameter f"
proof -
  assume "verts G \<noteq> {}" and w_non_neg: "\<forall>e \<in> arcs G. f e \<ge> 0"
  from ex_sp_eq_fin_diameter[OF this(1)] obtain u v
    where u_v: "u \<in> verts G" "v \<in> verts G" and sp_eq_dia: "\<mu> f u v = fin_diameter f"
    by blast
  from sp_eq_dia have "\<mu> f u v < \<infinity>" using fin_diameter_lt_inf by auto
  then have "u \<rightarrow>\<^sup>* v" using \<mu>_reach_conv by blast
  from min_cost_awalk[OF this] w_non_neg obtain p
    where "apath u p v" "\<mu> f u v = awalk_cost f p"
    by auto
  with u_v sp_eq_dia show ?thesis by auto
qed

subsection \<open>Relation between diameter and finite diameter\<close>

theorem diameter_eq_fin_diameter_if_strongly_connected:
  "strongly_connected G \<Longrightarrow> diameter = fin_diameter"
proof
  fix f assume strongly_con: "strongly_connected G"
  then have "\<infinity> \<notin> sp_costs f"
    unfolding sp_costs_def using \<mu>_reach_conv by auto
  then have "sp_costs f = fin_sp_costs f"
    unfolding fin_sp_costs_def sp_costs_def by auto
  then show "diameter f = fin_diameter f"
    unfolding diameter_def fin_diameter_def by auto
qed

end

end