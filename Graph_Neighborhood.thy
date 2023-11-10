theory Graph_Neighborhood
  imports
    "Graph_Theory.Digraph_Component" "Graph_Theory.Shortest_Path"
    "Graph_Theory_Batteries"
begin


section \<open>K-neighborhood definition\<close>

context wf_digraph
begin

definition k_neighborhood :: "'b weight_fun \<Rightarrow> 'a \<Rightarrow> real \<Rightarrow> 'a set" where
  "k_neighborhood w v k = {u \<in> verts G. \<mu> w v u \<le> k } - {v}"

lemma k_nh_reachable: "u \<in> k_neighborhood w v k \<Longrightarrow> v \<rightarrow>\<^sup>* u"
  unfolding k_neighborhood_def
  using shortest_path_inf by fastforce

lemma source_nmem_k_nh: "v \<notin> k_neighborhood w v k"
  unfolding k_neighborhood_def by simp

end

section \<open>N-nearest vertices\<close>
text \<open>
The definition of @{text n_nearest_verts} is used to formalize the abstract behaviour of the
Dijkstra algorithm which iteratively visits the nearest undiscovered vertex until all
vertices are discovered.
\<close>

context wf_digraph
begin

definition unvisited_verts :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
"unvisited_verts u U = {x. x \<in> verts G - U \<and> u \<rightarrow>\<^sup>* x}"

definition nearest_vert :: "'b weight_fun \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> 'a" where
"nearest_vert w u U =
  (SOME x. x \<in> unvisited_verts u U \<and> (\<forall>y \<in> unvisited_verts u U. \<mu> w u y \<ge> \<mu> w u x))"

inductive n_nearest_verts :: "'b weight_fun \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a set \<Rightarrow> bool" where
  zero_nnvs: "u \<in> verts G \<Longrightarrow> n_nearest_verts _ u 0 {u}"
| n_nnvs_unvis: "\<lbrakk> n_nearest_verts w u n U; unvisited_verts u U \<noteq> {} \<rbrakk>
   \<Longrightarrow> n_nearest_verts w u (Suc n) (insert (nearest_vert w u U) U)"
| n_nnvs_vis: "\<lbrakk> n_nearest_verts w u n U; unvisited_verts u U = {} \<rbrakk>
   \<Longrightarrow> n_nearest_verts w u (Suc n) U"

inductive_cases nnvs_ind_cases: "n_nearest_verts w u n U"
thm nnvs_ind_cases

subsection \<open>In general graphs\<close>

lemma source_mem_nnvs: "n_nearest_verts w u n U \<Longrightarrow> u \<in> verts G"
  by (induction rule: n_nearest_verts.induct) auto

lemma unvis_insert: "unvisited_verts u (insert x U) = (unvisited_verts u U) - {x}"
  unfolding unvisited_verts_def by auto

lemma disj_unvis_vis: "unvisited_verts u U \<inter> U = {}"
  unfolding unvisited_verts_def by auto

lemma nnvs_finite: "n_nearest_verts w u n U \<Longrightarrow> finite U"
  by (induction rule: n_nearest_verts.induct) auto

lemma nnvs_card_le_n: "n_nearest_verts w u n U \<Longrightarrow> card U \<le> Suc n"
  by (induction rule: n_nearest_verts.induct) (auto simp: card_insert_le_m1)

lemma nnvs_mem: "n_nearest_verts w u n U \<Longrightarrow> u \<in> U"
  by (induction rule: n_nearest_verts.induct) auto

lemma unvis_empty: "unvisited_verts u {a. u \<rightarrow>\<^sup>* a} = {}"
  unfolding unvisited_verts_def by auto

end

subsection \<open>In finite graphs\<close>
context fin_digraph begin

lemma k_nh_finite: "finite (k_neighborhood w v k)"
  unfolding k_neighborhood_def using finite_verts by force

lemma unvis_finite: "finite (unvisited_verts u U)"
  unfolding unvisited_verts_def using finite_verts by auto

lemma ex_unvis_vert:
  assumes "unvisited_verts u U \<noteq> {}"
  shows "\<exists>x \<in> unvisited_verts u U. (\<forall>y \<in> unvisited_verts u U. \<mu> w u y \<ge> \<mu> w u x)"
  unfolding nearest_vert_def using unvis_finite assms
proof(induction "unvisited_verts u U" arbitrary: u U rule: finite_induct)
  case (insert x F)
  then have "F = unvisited_verts u U - {x}"
    by auto
  then have F: "F = unvisited_verts u (insert x U)"
    using unvis_insert[symmetric] by simp

  show ?case
  proof(cases "unvisited_verts u (insert x U) = {}")
    case True
    with insert.prems show ?thesis using unvis_insert by auto
  next
    case False
    from insert(3)[OF F this] obtain x' where "x' \<in> unvisited_verts u (insert x U)"
      and "\<forall>y\<in>unvisited_verts u (insert x U). \<mu> w u x' \<le> \<mu> w u y" by blast
    note x' = this

    show ?thesis
    proof(cases "\<mu> w u x' \<le> \<mu> w u x")
      case True
      from x' F insert.hyps(4) have "x' \<in> unvisited_verts u U" by blast
      moreover
      have "\<forall>y \<in> unvisited_verts u U. \<mu> w u x' \<le> \<mu> w u y"
        using F True insert.hyps(4) x' by auto
      ultimately show ?thesis by blast
    next
      case False
      with x' have "\<forall>y \<in> unvisited_verts u (insert x U). \<mu> w u x \<le> \<mu> w u y"
        by fastforce
      with F insert.hyps(4) have "\<forall>y \<in> unvisited_verts u U. \<mu> w u x \<le> \<mu> w u y"
        by fastforce
      with insert.hyps(4) show ?thesis by blast
    qed
  qed
qed blast

lemma some_unvis_vert:
  fixes x
  assumes "unvisited_verts u U \<noteq> {}" and "x = nearest_vert w u U"
  shows "x \<in> unvisited_verts u U"
    and "\<forall>y \<in> unvisited_verts u U. \<mu> w u y \<ge> \<mu> w u x"
proof -
  define nv where "nv \<equiv> \<lambda>x. x \<in> unvisited_verts u U
    \<and> (\<forall>y\<in>unvisited_verts u U. \<mu> w u x \<le> \<mu> w u y)"

  from ex_unvis_vert[OF assms(1)]
  obtain x' where "nv x'" unfolding nv_def
    by blast
  then have "nv (SOME x. nv x)" using some_eq_ex by blast
  with assms(2) have "nv x" unfolding nearest_vert_def nv_def by blast
  then show
    "x \<in> unvisited_verts u U" and
    "\<forall>y \<in> unvisited_verts u U. \<mu> w u y \<ge> \<mu> w u x"
    unfolding nv_def by blast+
qed

lemma nearest_vert_unvis:
  "unvisited_verts u U \<noteq> {} \<Longrightarrow> nearest_vert w u U \<in> unvisited_verts u U"
  using some_unvis_vert by simp

lemma nearest_vert_not_mem:
  "unvisited_verts u U \<noteq> {} \<Longrightarrow> nearest_vert w u U \<notin> U"
  using disj_unvis_vis some_unvis_vert(1) by fastforce

lemma nearest_vert_reachable:
  "unvisited_verts u U \<noteq> {} \<Longrightarrow> u \<rightarrow>\<^sup>* nearest_vert w u U"
  using some_unvis_vert(1) unvisited_verts_def by auto

lemma nnvs_card_ge_n:
  "\<lbrakk> n_nearest_verts w u n U; unvisited_verts u U \<noteq> {} \<rbrakk>
  \<Longrightarrow> card U \<ge> Suc n"
proof(induction rule: n_nearest_verts.induct)
  case (n_nnvs_unvis w u n U)
  have "nearest_vert w u U \<notin> U"
    using nearest_vert_unvis[OF n_nnvs_unvis.hyps(2)] disj_unvis_vis by auto
  then have "card (insert (nearest_vert w u U) U) = Suc (card U)"
    using n_nnvs_unvis.hyps(1) nnvs_finite by auto
  with n_nnvs_unvis.IH[OF n_nnvs_unvis.hyps(2)] show ?case by simp
qed simp_all

corollary nnvs_card_eq_n: "\<lbrakk> n_nearest_verts w u n U; unvisited_verts u U \<noteq> {} \<rbrakk>
  \<Longrightarrow> card U = Suc n"
  using nnvs_card_le_n nnvs_card_ge_n le_antisym by blast


subsubsection \<open>Reachability and n-nearest vertices\<close>

lemma reachable_subs_nnvs:
  "\<lbrakk> u \<in> verts G; Suc n \<le> card {x. u \<rightarrow>\<^sup>* x} \<rbrakk>
  \<Longrightarrow> \<exists>A \<subseteq> {x. u \<rightarrow>\<^sup>* x}. card A = Suc n \<and> n_nearest_verts w u n A"
proof(induction n)
  case 0
  then have "{u} \<subseteq> {x. u \<rightarrow>\<^sup>* x}" by simp
  with zero_nnvs[OF \<open>u \<in> verts G\<close>] show ?case
    by (metis card_Suc_eq card.empty empty_iff)
next
  case (Suc n)
  from Suc.IH[OF Suc.prems(1)] obtain A
    where "A \<subseteq> {a. u \<rightarrow>\<^sup>* a}" and "card A = Suc n" and "n_nearest_verts w u n A"
    using Suc.prems(2) Suc_leD by blast
  note A = this

  show ?case
  proof(cases "Suc n = card {a. u \<rightarrow>\<^sup>* a}")
    case True
    with A Suc.prems(2) show ?thesis by linarith
  next
    case False
    with Suc.prems(2) have "Suc n < card {a. u \<rightarrow>\<^sup>* a}" by simp
    with A have "\<exists>x \<in> {a. u \<rightarrow>\<^sup>* a}. x \<notin> A"
      using subset_antisym by fastforce
    then have unvis_non_empty: "unvisited_verts u A \<noteq> {}"
      unfolding unvisited_verts_def using reachable_in_verts(2) by auto

    let ?A' = "insert (nearest_vert w u A) A"

    note n_nnvs_unvis[OF A(3) unvis_non_empty]
    moreover
    from A(1) have "?A' \<subseteq> {a. u \<rightarrow>\<^sup>* a}"
      using some_unvis_vert[OF unvis_non_empty]
      by (simp add: unvisited_verts_def)
    moreover
    note nearest_vert_not_mem[OF unvis_non_empty]
    with A(2) card.insert[OF nnvs_finite[OF A(3)]] nnvs_finite
    have "card ?A' = Suc (Suc n)" by auto

    ultimately show ?thesis by blast
  qed
qed

corollary all_reachable_eq_nnvs:
  "\<lbrakk> U = {x. u \<rightarrow>\<^sup>* x}; card U = Suc n \<rbrakk>
  \<Longrightarrow> n_nearest_verts w u n U"
  using reachable_subs_nnvs reachable_verts_finite reachable_in_verts(1)
  by (metis card_Suc_eq card_subset_eq insertI1 le_Suc_eq mem_Collect_eq)

lemma all_reachable_eq_nnvs_Suc:
  assumes "u \<in> verts G" and "U = {x. u \<rightarrow>\<^sup>* x}" and "Suc n \<ge> card U"
  shows "n_nearest_verts w u n U"
proof -
  note * = all_reachable_eq_nnvs le_Suc_eq
  show ?thesis using assms
  proof(induction n)
    case 0
    then show ?case using * reachable_verts_finite by auto
  next
    case (Suc n)
    then show ?case using  * n_nnvs_vis unvis_empty by auto
  qed
qed


lemma nnvs_imp_reachable: 
  "\<lbrakk> n_nearest_verts w u n A; Suc n \<le> card {x. u \<rightarrow>\<^sup>* x} \<rbrakk>
  \<Longrightarrow> A \<subseteq> {x. u \<rightarrow>\<^sup>* x} \<and> card A = Suc n"
proof(induction rule: n_nearest_verts.induct)
  case (zero_nnvs u)
  then show ?case using nearest_vert_reachable by simp
next
  case (n_nnvs_unvis w u n U)
  then show ?case using nearest_vert_reachable
    by (simp add: nearest_vert_not_mem nnvs_finite)
next
  case (n_nnvs_vis w u n U)
  from n_nnvs_vis.hyps(2) have "{a. u \<rightarrow>\<^sup>* a} \<subseteq> U"
    unfolding unvisited_verts_def using reachable_in_verts(2) by auto
  moreover
  from n_nnvs_vis have "U \<subseteq> {a. u \<rightarrow>\<^sup>* a}"
    using Suc_leD by blast
  ultimately show ?case
    using n_nnvs_vis by auto
qed

corollary nnvs_imp_all_reachable:
  "\<lbrakk> n_nearest_verts w u n U; Suc n = card {x. u \<rightarrow>\<^sup>* x} \<rbrakk>
  \<Longrightarrow> U = {x. u \<rightarrow>\<^sup>* x}"
  using nnvs_imp_reachable
  by (simp add: card_subset_eq reachable_verts_finite)

lemma nnvs_imp_all_reachable_Suc:
  assumes "n_nearest_verts w u n U"  "Suc n \<ge> card {x. u \<rightarrow>\<^sup>* x}"
  shows "U = {x. u \<rightarrow>\<^sup>* x}"
  using assms
proof(induction rule: n_nearest_verts.induct)
  case (zero_nnvs u)
  have u_mem: "u \<in> {a. u \<rightarrow>\<^sup>* a}" by (simp add: zero_nnvs.hyps)
  moreover
  from u_mem have "card {a. u \<rightarrow>\<^sup>* a} = 1"
    using le_Suc_eq reachable_verts_finite zero_nnvs.prems by force
  ultimately show ?case by (metis card_1_singletonE singletonD)
next
  case (n_nnvs_unvis w u n U)
  then show ?case
    by (metis le_Suc_eq n_nearest_verts.n_nnvs_unvis
        nnvs_imp_all_reachable unvis_empty)
next
  case (n_nnvs_vis w u n U)
  then show ?case
    by (metis le_Suc_eq n_nearest_verts.n_nnvs_vis
        nnvs_imp_all_reachable)
qed

lemma nnvs_subs_verts: "n_nearest_verts w u n U \<Longrightarrow> U \<subseteq> verts G"
proof(induction rule: n_nearest_verts.induct)
  case (n_nnvs_unvis w u n U)
  then have "nearest_vert w u U \<in> unvisited_verts u U"
    by (simp add: nearest_vert_unvis)
  then have "nearest_vert w u U \<in> verts G"
    unfolding unvisited_verts_def by simp
  with n_nnvs_unvis show ?case by blast
qed auto

subsubsection \<open>Relation between n-nearest vertices and k-neighborhood\<close>


lemma unvis_nearest_vert_contr:
  "\<lbrakk> n_nearest_verts w u n U; x \<in> U; x \<noteq> u; y \<in> unvisited_verts u U; \<mu> w u y < \<mu> w u x \<rbrakk>
  \<Longrightarrow> False"
proof(induction rule: n_nearest_verts.induct)
  case (n_nnvs_unvis w u n U)
  then obtain x where x: "x \<in> insert (nearest_vert w u U) U - {u}"
    "\<exists>y\<in>unvisited_verts u (insert (nearest_vert w u U) U). \<mu> w u y < \<mu> w u x" by blast
  then show ?case
  proof(cases "x = nearest_vert w u U")
    case True
    with n_nnvs_unvis x show ?thesis
      using some_unvis_vert unvis_insert by (metis DiffD1 not_le)
  next
    case False
    with n_nnvs_unvis x show ?thesis
      using unvis_insert by (auto, metis not_le some_unvis_vert(2))
  qed
qed blast

lemma nnvs_subs_k_nh:
  assumes nnvs: "n_nearest_verts w u n U"
      and card_N: "card (k_neighborhood w u k) \<ge> n"
    shows "U - {u} \<subseteq> k_neighborhood w u k"
proof -
  from nnvs_card_le_n[OF nnvs] have card_U: "card (U - {u}) \<le> n"
    using nnvs_mem[OF nnvs] nnvs_finite[OF nnvs] by auto
  show ?thesis
  proof(rule ccontr, safe, rule ccontr)
    fix x assume x: "x \<in> U" "x \<notin> k_neighborhood w u k" "x \<noteq> u"
    then have "{x, u} \<subseteq> U" using nnvs_mem[OF nnvs] by auto
    from card_mono[OF nnvs_finite[OF nnvs], OF this] have "card U \<ge> 2"
      using \<open>x \<noteq> u\<close> by auto
    then have "card (U - {u} - {x}) < card (U - {u})"
      using nnvs nnvs_finite nnvs_mem x by auto
    also have "\<dots> \<le> card (k_neighborhood w u k)"
      using card_N card_U by linarith
    finally have "card (U - {u} - {x}) < card (k_neighborhood w u k)" .
    then obtain y where y: "y \<in> k_neighborhood w u k" "y \<notin> U - {u} - {x}"
      using nnvs_finite[OF nnvs] by (meson card_mono finite_Diff not_le subset_iff)
    from k_nh_reachable[OF y(1)] y \<open>x \<notin> k_neighborhood w u k\<close>
    have y_unvis: "y \<in> unvisited_verts u U"
      unfolding unvisited_verts_def k_neighborhood_def by blast

    from y have "\<mu> w u y \<le> k" unfolding k_neighborhood_def by simp
    moreover
    from x have "\<mu> w u x > k" unfolding k_neighborhood_def
      using nnvs_subs_verts[OF nnvs] by fastforce
    ultimately have "\<mu> w u y < \<mu> w u x" by simp
    from unvis_nearest_vert_contr[OF nnvs \<open>x \<in> U\<close> \<open>x \<noteq> u\<close> y_unvis this] show "False" .
  qed
qed

lemma k_nh_subs_nnvs:
  assumes nnvs: "n_nearest_verts w u n U"
      and card_nh: "card (k_neighborhood w u k) < card U"
    shows "k_neighborhood w u k \<subseteq> U"
proof(rule ccontr)
  assume "\<not> k_neighborhood w u k \<subseteq> U"
  then obtain v where v: "v \<in> verts G" "v \<noteq> u" "\<mu> w u v \<le> k" "v \<notin> U"
    unfolding k_neighborhood_def by auto
  then have v_unvis: "v \<in> unvisited_verts u U"
    unfolding unvisited_verts_def
    using \<mu>_reach_conv[of w u v] PInfty_neq_ereal(1)[of k] by force

  let ?close_verts = "{v \<in> verts G. \<mu> w u v \<le> k} - {u}"
  let ?far_verts = "{v \<in> verts G. \<mu> w u v > k} - {u}"

  have vert_part: "verts G - {u} = ?close_verts \<union> ?far_verts"
    "?close_verts \<inter> ?far_verts = {}" by auto
  with finite_verts have "finite ?close_verts" and "finite ?far_verts"
    by auto

  have "card (k_neighborhood w u k) \<le> card (U - {u})"
    using card_nh nnvs nnvs_finite nnvs_mem by auto
  then have "card ?close_verts \<le> card (U - {u})"
    unfolding k_neighborhood_def
    by (cases "\<mu> w u u \<le> k") (auto simp: insert_absorb source_mem_nnvs[OF nnvs])

  have "?far_verts \<inter> (U - {u}) \<noteq> {}"
  proof(rule ccontr, unfold not_not)
    assume "?far_verts \<inter> (U - {u}) = {}"
    then have "U - {u} \<subseteq> ?close_verts"
      using nnvs_subs_verts[OF nnvs] by auto
    then have "card (U - {u}) \<le> card ?close_verts"
      by (simp add: card_mono)
    with \<open>card ?close_verts \<le> card (U - {u})\<close> have "?close_verts = U - {u}"
      using card_seteq[OF \<open>finite ?close_verts\<close> \<open>U - {u} \<subseteq> ?close_verts\<close>]
      by blast
    then show "False" using v by auto
  qed
  then obtain x where x: "x \<in> ?far_verts" "x \<in> U" "x \<noteq> u"
    by auto
  then have "\<mu> w u v < \<mu> w u x" using \<open>\<mu> w u v \<le> k\<close> by auto
  from unvis_nearest_vert_contr[OF nnvs x(2,3) v_unvis this]
  show "False" .
qed

end

end