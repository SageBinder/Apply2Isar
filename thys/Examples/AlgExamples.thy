theory AlgExamples
  imports
    "Apply2Isar.Apply2Isar"
    "HOL.Modules"
    "HOL-Algebra.IntRing"
    "HOL-Algebra.Bij"
    "HOL-Algebra.Elementary_Groups"
    "HOL-Algebra.Divisibility"
    "HOL-Algebra.Exact_Sequence"

begin

text "These are some examples of Apply2Isar on apply scripts from the HOL-Algebra library."

section "Test 1"

context module
begin

lemma span_add: "x \<in> span S \<Longrightarrow> y \<in> span S \<Longrightarrow> x + y \<in> span S"
  unfolding span_explicit
proof safe
  fix tx ty rx ry assume *: "finite tx" "finite ty" "tx \<subseteq> S" "ty \<subseteq> S"
  have [simp]: "(tx \<union> ty) \<inter> tx = tx" "(tx \<union> ty) \<inter> ty = ty"
    by auto
  show "\<exists>t r. (\<Sum>a\<in>tx. rx a *s a) + (\<Sum>a\<in>ty. ry a *s a) = (\<Sum>a\<in>t. r a *s a) \<and> finite t \<and> t \<subseteq> S"
    apply2isar\<open>
    apply (intro exI[of _ "tx \<union> ty"])
    apply (intro exI[of _ "\<lambda>a. (if a \<in> tx then rx a else 0) + (if a \<in> ty then ry a else 0)"])
    apply (auto simp: * scale_left_distrib sum.distrib if_distrib[of "\<lambda>r. r *s a" for a] sum.If_cases)
    done\<close>
  proof-
    have h_3_1: "(\<Sum>a\<in>tx. rx a *s a) + (\<Sum>a\<in>ty. ry a *s a) = (\<Sum>a\<in>sup tx ty. ((if a \<in> tx then rx a else 0) + (if a \<in> ty then ry a else 0)) *s a) \<and> finite (sup tx ty) \<and> sup tx ty \<le> S"
      by ( auto simp : * scale_left_distrib sum.distrib if_distrib [ of "\<lambda>r. r *s a" for a ] sum.If_cases ) (* LEAF *)
    have h_2_1: "\<exists>r. (\<Sum>a\<in>tx. rx a *s a) + (\<Sum>a\<in>ty. ry a *s a) = (\<Sum>a\<in>sup tx ty. r a *s a) \<and> finite (sup tx ty) \<and> sup tx ty \<le> S"
      by ( intro exI [ of _ "\<lambda>a. (if a \<in> tx then rx a else 0) + (if a \<in> ty then ry a else 0)" ] )
        ( fact h_3_1 ) 
    show h_1_1: "\<exists>t r. (\<Sum>a\<in>tx. rx a *s a) + (\<Sum>a\<in>ty. ry a *s a) = (\<Sum>a\<in>t. r a *s a) \<and> finite t \<and> t \<le> S"
      by ( intro exI [ of _ "tx \<union> ty" ] )
        ( fact h_2_1 ) 
  qed
qed

end

section "Test 2"

corollary ZMod_eq_mod: "ZMod m a = ZMod m b \<longleftrightarrow> a mod m = b mod m"
  apply2isar\<open>
  apply (rule iffI)
  apply (erule ZMod_imp_zmod)
  apply (erule zmod_imp_ZMod)
  done\<close>
proof-
  have h_2_2: "a mod m = b mod m \<Longrightarrow> ZMod m a = ZMod m b"
    by ( erule zmod_imp_ZMod ) (* LEAF *)
  have h_2_1: "ZMod m a = ZMod m b \<Longrightarrow> a mod m = b mod m"
    by ( erule ZMod_imp_zmod ) (* LEAF *)
  show h_1_1: "(ZMod m a = ZMod m b) = (a mod m = b mod m)"
    by ( rule iffI )
      ( fact h_2_1, fact h_2_2 ) 
qed

section "Test 3"

lemma (in abelian_group_hom) abelian_subgroup_a_kernel:
  "abelian_subgroup (a_kernel G H h) G"
  apply2isar\<open>
  apply (rule abelian_subgroupI)
   apply (simp add: G.abelian_group_axioms abelian_subgroup.a_normal abelian_subgroupI3 additive_subgroup_a_kernel)
  apply (simp add: G.a_comm)
  done\<close>
proof-
  have h_2_2: "\<And>x y. x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> x \<oplus> y = y \<oplus> x"
    by ( simp add : G.a_comm ) (* LEAF *)
  have h_2_1: "a_kernel G (H::('c, 'd) ring_scheme) (h::'a \<Rightarrow> 'c) \<lhd> add_monoid G"
    by ( simp add : G.abelian_group_axioms abelian_subgroup.a_normal abelian_subgroupI3 additive_subgroup_a_kernel ) (* LEAF *)
  show h_1_1: "abelian_subgroup (a_kernel G H h) G"
    by ( rule abelian_subgroupI )
      ( fact h_2_1, fact h_2_2 ) 
qed

section "Test 4"

lemma inv_BijGroup:
     "f \<in> Bij S \<Longrightarrow> m_inv (BijGroup S) f = (\<lambda>x \<in> S. (inv_into S f) x)"
  apply2isar\<open>
apply (rule group.inv_equality [OF group_BijGroup])
apply (simp_all add:BijGroup_def restrict_inv_into_Bij Bij_compose_restrict_eq)
done\<close>
proof-
  have
    h_2_1: "(f::'a \<Rightarrow> 'a) \<in> Bij (S::'a set) \<Longrightarrow> restrict (inv_into S f) S \<otimes>\<^bsub>BijGroup S\<^esub> f = \<one>\<^bsub>BijGroup S\<^esub>"
    and h_2_2: "f \<in> Bij S \<Longrightarrow> f \<in> carrier (BijGroup S)"
    and h_2_3: "(f::'a \<Rightarrow> 'a) \<in> Bij (S::'a set) \<Longrightarrow> restrict (inv_into S f) S \<in> carrier (BijGroup S)"
    by ( simp_all add : BijGroup_def restrict_inv_into_Bij Bij_compose_restrict_eq ) (* LEAF *)
  show h_1_1: "(f::'a \<Rightarrow> 'a) \<in> Bij (S::'a set) \<Longrightarrow> inv\<^bsub>BijGroup S\<^esub> f = restrict (inv_into S f) S"
    by ( rule group.inv_equality [ OF group_BijGroup ] )
      ( fact h_2_1, fact h_2_2, fact h_2_3 ) 
qed

section "Test 5"

lemma (in group_disjoint_sum) mon_group_mul_eq:
    "(\<lambda>(x,y). x \<otimes> y) \<in> mon (subgroup_generated G A \<times>\<times> subgroup_generated G B) G
     \<longleftrightarrow> A \<inter> B = {\<one>} \<and> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x)"
proof -
  have subGA: "generate G (carrier G \<inter> A) \<subseteq> A"
    by (simp add: AG.subgroup_axioms generate_subgroup_incl)
  have subGB: "generate G (carrier G \<inter> B) \<subseteq> B"
    by (simp add: BG.subgroup_axioms generate_subgroup_incl)
  show ?thesis
    apply2isar\<open>
    apply (auto simp: mon_def hom_group_mul_eq simp flip: subset_one)
     apply (simp_all (no_asm_use) add: inj_on_def AG.carrier_subgroup_generated_subgroup BG.carrier_subgroup_generated_subgroup)
    using cancel apply blast+
    done\<close>
  proof-
    have
      h_3_1: "\<And>x. \<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x \<Longrightarrow> \<forall>x\<in>A. \<forall>y\<in>B. \<forall>xa\<in>A. \<forall>ya\<in>B. x \<otimes> y = xa \<otimes> ya \<longrightarrow> x = xa \<and> y = ya \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x = \<one>"
      and h_3_2: "inf A B \<le> insert \<one> bot \<Longrightarrow> \<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x \<Longrightarrow> \<forall>x\<in>A. \<forall>y\<in>B. \<forall>xa\<in>A. \<forall>ya\<in>B. x \<otimes> y = xa \<otimes> ya \<longrightarrow> x = xa \<and> y = ya"
      using cancel
      by ( ( blast )+ ) (* LEAF *)
    have
      h_2_1: "\<And>x::'a. \<forall>x::'a\<in>A::'a set. \<forall>y::'a\<in>B::'a set. x \<otimes> y = y \<otimes> x \<Longrightarrow> inj_on (\<lambda>(x::'a, y::'a). x \<otimes> y) (A \<times> B) \<Longrightarrow> x \<in> A \<Longrightarrow> x \<in> B \<Longrightarrow> x = \<one>"
      and h_2_2: "(A::'a set) \<inter> (B::'a set) \<subseteq> {\<one>} \<Longrightarrow> \<forall>x::'a\<in>A. \<forall>y::'a\<in>B. x \<otimes> y = y \<otimes> x \<Longrightarrow> inj_on (\<lambda>(x::'a, y::'a). x \<otimes> y) (A \<times> B)"
      by ( simp_all ( no_asm_use ) add : inj_on_def AG.carrier_subgroup_generated_subgroup BG.carrier_subgroup_generated_subgroup )
        ( fact h_3_1, fact h_3_2 ) 
    show h_1_1: "((\<lambda>(x, y). x \<otimes> y) \<in> mon (subgroup_generated G A \<times>\<times> subgroup_generated G B) G) = (inf A B = insert \<one> bot \<and> (\<forall>x\<in>A. \<forall>y\<in>B. x \<otimes> y = y \<otimes> x))"
      by ( auto simp : mon_def hom_group_mul_eq simp flip : subset_one )
        ( fact h_2_1, fact h_2_2 ) 
  qed
qed

section "Test 6"

lemma exact_sequence_sum_lemma:
  assumes "comm_group G" and h: "h \<in> iso A C" and k: "k \<in> iso B D"
    and ex: "exact_seq ([D,G,A], [g,i])" "exact_seq ([C,G,B], [f,j])"
    and fih: "\<And>x. x \<in> carrier A \<Longrightarrow> f(i x) = h x"
    and gjk: "\<And>x. x \<in> carrier B \<Longrightarrow> g(j x) = k x"
  shows "(\<lambda>(x, y). i x \<otimes>\<^bsub>G\<^esub> j y) \<in> Group.iso (A \<times>\<times> B) G \<and> (\<lambda>z. (f z, g z)) \<in> Group.iso G (C \<times>\<times> D)"
    (is "?ij \<in> _ \<and> ?gf \<in> _")
proof (rule epi_iso_compose_rev)
  interpret comm_group G
    by (rule assms)
  interpret f: group_hom G C f
    using ex by (simp add: group_hom_def group_hom_axioms_def)
  interpret g: group_hom G D g
    using ex by (simp add: group_hom_def group_hom_axioms_def)
  interpret i: group_hom A G i
    using ex by (simp add: group_hom_def group_hom_axioms_def)
  interpret j: group_hom B G j
    using ex by (simp add: group_hom_def group_hom_axioms_def)
  have kerf: "kernel G C f = j ` carrier B" and "group A" "group B" "i \<in> hom A G"
    using ex by (auto simp: group_hom_def group_hom_axioms_def)
  then obtain h' where "h' \<in> hom C A" "(\<forall>x \<in> carrier A. h'(h x) = x)"
    and hh': "(\<forall>y \<in> carrier C. h(h' y) = y)" and "group_isomorphisms A C h h'"
    using h by (auto simp: group.iso_iff_group_isomorphisms group_isomorphisms_def)
  have homij: "?ij \<in> hom (A \<times>\<times> B) G"
    apply2isar\<open>
    unfolding case_prod_unfold
    apply (rule hom_group_mult)
    using ex by (simp_all add: group_hom_def hom_of_fst [unfolded o_def] hom_of_snd [unfolded o_def])
    \<close>
  proof-
    have
      h_2_1: "(\<lambda>x. i (fst x)) \<in> hom (A \<times>\<times> B) G"
      and h_2_2: "(\<lambda>x. j (snd x)) \<in> hom (A \<times>\<times> B) G"
      using ex
      by ( simp_all add : group_hom_def hom_of_fst [ unfolded o_def ] hom_of_snd [ unfolded o_def ] ) (* LEAF *)
    show h_1_1: "(\<lambda>(x, y). i x \<otimes>\<^bsub>G\<^esub> j y) \<in> hom (A \<times>\<times> B) G"
      unfolding case_prod_unfold
      by ( rule hom_group_mult )
        ( fact h_2_1, fact h_2_2 ) 
  qed
  show homgf: "?gf \<in> hom G (C \<times>\<times> D)"
    using ex by (simp add: hom_paired)
  show "?ij \<in> epi (A \<times>\<times> B) G"
  proof (clarsimp simp add: epi_iff_subset homij)
    fix x
    assume x: "x \<in> carrier G"
    with \<open>i \<in> hom A G\<close> \<open>h' \<in> hom C A\<close> have "x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub>(i(h'(f x))) \<in> kernel G C f"
      by (simp add: kernel_def hom_in_carrier hh' fih)
    with kerf obtain y where y: "y \<in> carrier B" "j y = x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub>(i(h'(f x)))"
      by auto
    have "i (h' (f x)) \<otimes>\<^bsub>G\<^esub> (x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> i (h' (f x))) = x \<otimes>\<^bsub>G\<^esub> (i (h' (f x)) \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> i (h' (f x)))"
      by (meson \<open>h' \<in> hom C A\<close> x f.hom_closed hom_in_carrier i.hom_closed inv_closed m_lcomm)
    also have "\<dots> = x"
      using \<open>h' \<in> hom C A\<close> hom_in_carrier x by fastforce
    finally show "x \<in> (\<lambda>(x, y). i x \<otimes>\<^bsub>G\<^esub> j y) ` (carrier A \<times> carrier B)"
      apply2isar\<open>
      using x y apply (clarsimp simp: image_def)
      apply (rule_tac x="h'(f x)" in bexI)
       apply (rule_tac x=y in bexI, auto)
      by (meson \<open>h' \<in> hom C A\<close> f.hom_closed hom_in_carrier)\<close>
    proof-
      assume h_init: "i (h' (f x)) \<otimes>\<^bsub>G\<^esub> (x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> i (h' (f x))) = x"
      have h_3_2: "i (h' (f x)) \<otimes>\<^bsub>G\<^esub> (x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> i (h' (f x))) = x \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier B \<Longrightarrow> j y = x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> i (h' (f x)) \<Longrightarrow> h' (f x) \<in> carrier A"
        by ( meson \<open>h' \<in> hom C A\<close> f.hom_closed hom_in_carrier ) (* LEAF *)
      have h_3_1: "i (h' (f x)) \<otimes>\<^bsub>G\<^esub> (x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> i (h' (f x))) = x \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier B \<Longrightarrow> j y = x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> i (h' (f x)) \<Longrightarrow> \<exists>y\<in>carrier B. x = i (h' (f x)) \<otimes>\<^bsub>G\<^esub> j y"
        by ( rule_tac x = y in bexI , auto ) (* LEAF *)
      have h_2_1: "i (h' (f x)) \<otimes>\<^bsub>G\<^esub> (x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> i (h' (f x))) = x \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier B \<Longrightarrow> j y = x \<otimes>\<^bsub>G\<^esub> inv\<^bsub>G\<^esub> i (h' (f x)) \<Longrightarrow> \<exists>xa\<in>carrier A. \<exists>y\<in>carrier B. x = i xa \<otimes>\<^bsub>G\<^esub> j y"
        by ( rule_tac x = "h'(f x)" in bexI )
          ( fact h_3_1, fact h_3_2 ) 
      show h_1_1: "x \<in> (\<lambda>(x, y). i x \<otimes>\<^bsub>G\<^esub> j y) ` (SIGMA _:carrier A. carrier B)"
        using h_init
        using x y
        by ( clarsimp simp : image_def )
          ( fact h_2_1 ) 
    qed
  qed
  show "(\<lambda>z. (f z, g z)) \<circ> (\<lambda>(x, y). i x \<otimes>\<^bsub>G\<^esub> j y) \<in> Group.iso (A \<times>\<times> B) (C \<times>\<times> D)"
    apply2isar\<open>
    apply (rule group.iso_eq [where f = "\<lambda>(x,y). (h x,k y)"])
    using ex
    apply (auto simp: group_hom_def group_hom_axioms_def DirProd_group iso_paired2 h k fih gjk kernel_def set_eq_iff)
     apply (metis f.hom_closed f.r_one fih imageI)
    apply (metis g.hom_closed g.l_one gjk imageI)
    done\<close>
  proof-
    have h_3_2: "\<And>(a::'a) b::'a. \<forall>x::'a. (x \<in> carrier (G::'a monoid) \<and> (g::'a \<Rightarrow> 'a) x = \<one>\<^bsub>D::'a monoid\<^esub>) = (x \<in> (i::'a \<Rightarrow> 'a) ` carrier (A::'a monoid)) \<Longrightarrow> \<forall>x::'a. (x \<in> carrier G \<and> (f::'a \<Rightarrow> 'a) x = \<one>\<^bsub>C::'a monoid\<^esub>) = (x \<in> (j::'a \<Rightarrow> 'a) ` carrier (B::'a monoid)) \<Longrightarrow> a \<in> carrier A \<Longrightarrow> b \<in> carrier B \<Longrightarrow> g (i a) \<otimes>\<^bsub>D\<^esub> (k::'a \<Rightarrow> 'a) b = k b"
      by ( metis g.hom_closed g.l_one gjk imageI ) (* LEAF *)
    have h_3_1: "\<And>(a::'a) b::'a. \<forall>x::'a. (x \<in> carrier (G::'a monoid) \<and> (g::'a \<Rightarrow> 'a) x = \<one>\<^bsub>D::'a monoid\<^esub>) = (x \<in> (i::'a \<Rightarrow> 'a) ` carrier (A::'a monoid)) \<Longrightarrow> \<forall>x::'a. (x \<in> carrier G \<and> (f::'a \<Rightarrow> 'a) x = \<one>\<^bsub>C::'a monoid\<^esub>) = (x \<in> (j::'a \<Rightarrow> 'a) ` carrier (B::'a monoid)) \<Longrightarrow> a \<in> carrier A \<Longrightarrow> b \<in> carrier B \<Longrightarrow> (h::'a \<Rightarrow> 'a) a \<otimes>\<^bsub>C\<^esub> f (j b) = h a"
      by ( metis f.hom_closed f.r_one fih imageI ) (* LEAF *)
    have
      h_2_1: "Group.group (A \<times>\<times> B)"
      and h_2_2: "(\<lambda>(x, y). (h x, k y)) \<in> Group.iso (A \<times>\<times> B) (C \<times>\<times> D)"
      and h_2_3: "\<And>x. x \<in> carrier (A \<times>\<times> B) \<Longrightarrow> ((\<lambda>z. (f z, g z)) \<circ> (\<lambda>(x, y). i x \<otimes>\<^bsub>G\<^esub> j y)) x = (\<lambda>(x, y). (h x, k y)) x"
      using ex
      by ( auto simp : group_hom_def group_hom_axioms_def DirProd_group iso_paired2 h k fih gjk kernel_def set_eq_iff )
        ( fact h_3_1, fact h_3_2 ) 
    show h_1_1: "(\<lambda>z. (f z, g z)) \<circ> (\<lambda>(x, y). i x \<otimes>\<^bsub>G\<^esub> j y) \<in> Group.iso (A \<times>\<times> B) (C \<times>\<times> D)"
      by ( rule group.iso_eq [ where f = "\<lambda>(x,y). (h x,k y)" ] )
        ( fact h_2_1, fact h_2_2, fact h_2_3 ) 
  qed
qed

section "Test 7 (introducing facts using 'with')"

context module
begin

lemma unusual_tacs_test_4: "x \<in> span S \<Longrightarrow> y \<in> span S \<Longrightarrow> x + y \<in> span S"
  unfolding span_explicit
proof safe
  fix tx ty rx ry assume *: "finite tx" "finite ty" "tx \<subseteq> S" "ty \<subseteq> S"
  have [simp]: "(tx \<union> ty) \<inter> tx = tx" "(tx \<union> ty) \<inter> ty = ty"
    by auto
  with * show "\<exists>t r. (\<Sum>a\<in>tx. rx a *s a) + (\<Sum>a\<in>ty. ry a *s a) = (\<Sum>a\<in>t. r a *s a) \<and> finite t \<and> t \<subseteq> S"
    apply2isar\<open>
    apply (intro exI[of _ "tx \<union> ty"])
    apply (intro exI[of _ "\<lambda>a. (if a \<in> tx then rx a else 0) + (if a \<in> ty then ry a else 0)"])
    apply (auto simp: scale_left_distrib sum.distrib if_distrib[of "\<lambda>r. r *s a" for a] sum.If_cases)
    done\<close>
  proof-
    assume h_init:
      "finite tx"
      "finite ty"
      "tx \<le> S"
      "ty \<le> S"
      "inf (sup tx ty) tx = tx"
      "inf (sup tx ty) ty = ty"
    have h_3_1: "finite tx \<Longrightarrow> finite ty \<Longrightarrow> tx \<le> S \<Longrightarrow> ty \<le> S \<Longrightarrow> inf (sup tx ty) tx = tx \<Longrightarrow> inf (sup tx ty) ty = ty \<Longrightarrow> (\<Sum>a\<in>tx. rx a *s a) + (\<Sum>a\<in>ty. ry a *s a) = (\<Sum>a\<in>sup tx ty. ((if a \<in> tx then rx a else 0) + (if a \<in> ty then ry a else 0)) *s a) \<and> finite (sup tx ty) \<and> sup tx ty \<le> S"
      by ( auto simp : scale_left_distrib sum.distrib if_distrib [ of "\<lambda>r. r *s a" for a ] sum.If_cases ) (* LEAF *)
    have h_2_1: "finite tx \<Longrightarrow> finite ty \<Longrightarrow> tx \<le> S \<Longrightarrow> ty \<le> S \<Longrightarrow> inf (sup tx ty) tx = tx \<Longrightarrow> inf (sup tx ty) ty = ty \<Longrightarrow> \<exists>r. (\<Sum>a\<in>tx. rx a *s a) + (\<Sum>a\<in>ty. ry a *s a) = (\<Sum>a\<in>sup tx ty. r a *s a) \<and> finite (sup tx ty) \<and> sup tx ty \<le> S"
      by ( intro exI [ of _ "\<lambda>a. (if a \<in> tx then rx a else 0) + (if a \<in> ty then ry a else 0)" ] )
        ( fact h_3_1 ) 
    show h_1_1: "\<exists>t r. (\<Sum>a\<in>tx. rx a *s a) + (\<Sum>a\<in>ty. ry a *s a) = (\<Sum>a\<in>t. r a *s a) \<and> finite t \<and> t \<le> S"
      using h_init
      by ( intro exI [ of _ "tx \<union> ty" ] )
        ( fact h_2_1 ) 
  qed
qed

end

section "Test 8"

lemma (in monoid) unusual_tacs_test_1':
  "weak_partial_order (division_rel G)"
  apply2isar\<open>apply unfold_locales
      apply (simp_all add: associated_sym divides_antisym)
    apply (metis associated_trans)
   apply (metis divides_trans)
  by (meson associated_def divides_trans)\<close>
proof-
  have h_3_3: "\<And>x y z w. x \<sim> y \<Longrightarrow> z \<sim> w \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G \<Longrightarrow> w \<in> carrier G \<Longrightarrow> x divides z = y divides w"
    by ( meson associated_def divides_trans ) (* LEAF *)
  have h_3_2: "\<And>x y z. x divides y \<Longrightarrow> y divides z \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G \<Longrightarrow> x divides z"
    by ( metis divides_trans ) (* LEAF *)
  have h_3_1: "\<And>x y z. x \<sim> y \<Longrightarrow> y \<sim> z \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G \<Longrightarrow> x \<sim> z"
    by ( metis associated_trans ) (* LEAF *)
  have
    h_2_1: "\<And>x. x \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> x .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> x"
    and h_2_2: "\<And>x y. x .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> y \<Longrightarrow> x \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> y \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> y .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> x"
    and h_2_3: "\<And>x y z. x .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> y \<Longrightarrow> y .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> z \<Longrightarrow> x \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> y \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> z \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> x .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> z"
    and h_2_4: "\<And>x. x \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> x \<sqsubseteq>\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> x"
    and h_2_5: "\<And>x y. x \<sqsubseteq>\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> y \<Longrightarrow> y \<sqsubseteq>\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> x \<Longrightarrow> x \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> y \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> x .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> y"
    and h_2_6: "\<And>x y z. x \<sqsubseteq>\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> y \<Longrightarrow> y \<sqsubseteq>\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> z \<Longrightarrow> x \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> y \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> z \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> x \<sqsubseteq>\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> z"
    and h_2_7: "\<And>x y z w. x .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> y \<Longrightarrow> z .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> w \<Longrightarrow> x \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> y \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> z \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> w \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> (x \<sqsubseteq>\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> z) = (y \<sqsubseteq>\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> w)"
    by ( simp_all add : associated_sym divides_antisym )
      ( fact h_3_1, fact h_3_2, fact h_3_3 ) 
  show h_1_1: "weak_partial_order \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>"
    by ( unfold_locales )
      ( fact h_2_1, fact h_2_2, fact h_2_3, fact h_2_4, fact h_2_5, fact h_2_6, fact h_2_7 ) 
qed

section "Test 9"

lemma (in monoid) division_equiv: "equivalence (division_rel G)"
  apply2isar\<open>
  apply unfold_locales
    apply simp_all
   apply (metis associated_def)
  apply (iprover intro: associated_trans)
  done\<close>
proof-
  have h_3_2: "\<And>x y z. x \<sim> y \<Longrightarrow> y \<sim> z \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> z \<in> carrier G \<Longrightarrow> x \<sim> z"
    by ( iprover intro : associated_trans ) (* LEAF *)
  have h_3_1: "\<And>x y. x \<sim> y \<Longrightarrow> x \<in> carrier G \<Longrightarrow> y \<in> carrier G \<Longrightarrow> y \<sim> x"
    by ( metis associated_def ) (* LEAF *)
  have
    h_2_1: "\<And>x. x \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> x .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> x"
    and h_2_2: "\<And>x y. x .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> y \<Longrightarrow> x \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> y \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> y .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> x"
    and h_2_3: "\<And>x y z. x .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> y \<Longrightarrow> y .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> z \<Longrightarrow> x \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> y \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> z \<in> carrier \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr> \<Longrightarrow> x .=\<^bsub>\<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>\<^esub> z"
    by ( simp_all )
      ( fact h_3_1, fact h_3_2 ) 
  show h_1_1: "equivalence \<lparr>carrier = carrier G, eq = (\<sim>), le = (divides)\<rparr>"
    by ( unfold_locales )
      ( fact h_2_1, fact h_2_2, fact h_2_3 ) 
qed

end
