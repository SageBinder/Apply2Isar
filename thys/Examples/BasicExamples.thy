theory BasicExamples
  imports 
    "Apply2Isar.Apply2Isar"

begin

text "These are some examples of Apply2Isar on basic examples."

section "By test"

subsection "Test 1"

lemma by_test_1: "P \<longleftrightarrow> \<not> \<not> P"
  apply2isar\<open>
  by auto\<close>
proof-
  show h_1_1: "P = (\<not> \<not> P)"
    by ( auto ) (* LEAF *)
qed

subsection "Test 2"

(* Also tests subgoal *)
lemma by_test_2: "P \<longleftrightarrow> \<not> \<not> P"
  apply2isar\<open>
  subgoal by auto
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  show h_1_1: "P = (\<not> \<not> P)"
  proof-
    show h_1_1: "P = (\<not> \<not> P)"
      by ( auto ) (* LEAF *)
  qed
qed

subsection "Test 3"

text "Tests `by METHOD1 METHOD2`"

lemma by_test_3:
  fixes Q
  defines "P \<equiv> Q"
  shows "P \<Longrightarrow> Q" "Q \<Longrightarrow> P" "Q \<or> \<not> Q" "P \<or> \<not>P"
  apply2isar\<open>
     apply (simp add: P_def)
  by (simp_all add: P_def)\<close>
proof-
  have
    h_1_2: "Q \<Longrightarrow> P"
    and h_1_3: "Q \<or> \<not> Q"
    and h_1_4: "P \<or> \<not> P"
    by ( simp_all add : P_def ) (* LEAF *)
  have h_1_1: "P \<Longrightarrow> Q"
    by ( simp add : P_def ) (* LEAF *)
  show
    "P \<Longrightarrow> Q"
    and "Q \<Longrightarrow> P"
    and "Q \<or> \<not> Q"
    and "P \<or> \<not> P"
    by ( fact h_1_1, fact h_1_2, fact h_1_3, fact h_1_4 ) (* COMBINED SHOW *)
qed

section "Trivial proof test"

lemma trivial_proof_test_1:
  assumes "P"
  defines "Q \<equiv> P"
  shows "Q" "Q"
  apply2isar\<open>
  using assms(1)[simplified, unfolded Q_def]
   apply (subst Q_def)
   defer
  using assms(1)
   apply (subst Q_def)
  .\<close>
proof-
  have
    h_2_1: "P \<Longrightarrow> P"
    and h_3_1: "P \<Longrightarrow> P"
    . (* TRIVIAL LEAF *)
  have h_1_2: "Q"
    using assms(1)
    by ( subst Q_def )
      ( fact h_2_1 ) 
  have h_1_1: "Q"
    using assms(1)[ simplified, unfolded Q_def ]
    by ( subst Q_def )
      ( fact h_2_1 ) 
  show
    "Q"
    and "Q"
    by ( fact h_1_1, fact h_1_2 ) (* COMBINED SHOW *)
qed

lemma trivial_proof_test_2:
  assumes "A \<subseteq> B" "B \<subseteq> A"
  shows "A = B"
  apply2isar\<open>
  using assms ..\<close>
proof-
  show h_1_1: "A = B"
    using assms
    .. (* TRIVIAL LEAF *)
qed

section "Subgoal test"

subsection "Test 1"

text
  "Tests multiple doubly-nested subgoals with no arguments (no fixed vars, etc.) 
  We also throw in 'by' occasionally. "

lemma subgoal_test_1: "(P \<longleftrightarrow> Q) \<longleftrightarrow> (\<not>P \<longleftrightarrow> \<not>Q)"
  apply2isar\<open>
  apply (rule iffI)
  subgoal
    apply (rule iffI)
    subgoal
      apply simp
      done
    by satx
  subgoal
    subgoal
      apply (rule iffI)
      subgoal
        by argo
      subgoal
        apply blast
        done
      done
    done
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have h_2_1: "P = Q \<Longrightarrow> (\<not> P) = (\<not> Q)"
  proof-
    (* MOVED SUBPROOFS AND NOTES *)
    have h_2_1: "P = Q \<Longrightarrow> \<not> P \<Longrightarrow> \<not> Q"
    proof-
      show h_1_1: "P = Q \<Longrightarrow> \<not> P \<Longrightarrow> \<not> Q"
        by ( simp ) (* LEAF *)
    qed
      (* BEGIN MAIN BODY *)
    have h_2_2: "P = Q \<Longrightarrow> \<not> Q \<Longrightarrow> \<not> P"
      by ( satx ) (* LEAF *)
    show h_1_1: "P = Q \<Longrightarrow> (\<not> P) = (\<not> Q)"
      by ( rule iffI )
        ( fact h_2_1, fact h_2_2 ) 
  qed
  have h_2_2: "(\<not> P) = (\<not> Q) \<Longrightarrow> P = Q"
  proof-
    (* MOVED SUBPROOFS AND NOTES *)
    show h_1_1: "(\<not> P) = (\<not> Q) \<Longrightarrow> P = Q"
    proof-
      (* MOVED SUBPROOFS AND NOTES *)
      have h_2_1: "(\<not> P) = (\<not> Q) \<Longrightarrow> P \<Longrightarrow> Q"
      proof-
        show h_1_1: "(\<not> P) = (\<not> Q) \<Longrightarrow> P \<Longrightarrow> Q"
          by ( argo ) (* LEAF *)
      qed
      have h_2_2: "(\<not> P) = (\<not> Q) \<Longrightarrow> Q \<Longrightarrow> P"
      proof-
        show h_1_1: "(\<not> P) = (\<not> Q) \<Longrightarrow> Q \<Longrightarrow> P"
          by ( blast ) (* LEAF *)
      qed
        (* BEGIN MAIN BODY *)
      show h_1_1: "(\<not> P) = (\<not> Q) \<Longrightarrow> P = Q"
        by ( rule iffI )
          ( fact h_2_1, fact h_2_2 ) 
    qed
  qed
    (* BEGIN MAIN BODY *)
  show h_1_1: "(P = Q) = ((\<not> P) = (\<not> Q))"
    by ( rule iffI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 2"

text "Tests a single subgoal command with a single fixed var."

lemma subgoal_test_2: "\<And>x. P x \<longrightarrow> P x"
  apply2isar\<open>
  subgoal
    apply (rule impI)
    apply assumption
    done
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  show h_1_1: "\<And>x. P x \<longrightarrow> P x"
  proof-
    fix xa
    have h_2_1: "P xa \<Longrightarrow> P xa"
      by ( assumption ) (* LEAF *)
    show h_1_1: "P xa \<longrightarrow> P xa"
      by ( rule impI )
        ( fact h_2_1 ) 
  qed
qed

subsection "Test 4"

lemma subgoal_test_4:
  fixes Q R
  defines "P \<equiv> \<lambda>x. Q x \<and> R x"
  assumes R: "R = (\<lambda>x. Q x)"
  shows "Q x \<Longrightarrow> P x"
  apply2isar\<open>
  using P_def
  subgoal
    unfolding R
    by simp
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  show h_1_1: "Q x \<Longrightarrow> P x"
  proof-
    show h_1_1: "Q x \<Longrightarrow> P x"
      using P_def
      unfolding R
      by ( simp ) (* LEAF *)
  qed
qed

subsection "Test 5"

lemma subgoal_test_5:
  assumes "P"
  defines "Q \<equiv> P"
  defines "R \<equiv> Q"
  shows "Q" "Q" "R"
  apply2isar\<open>
    apply (subst Q_def)
    apply fact
  unfolding R_def
  subgoal
    unfolding Q_def using assms(1) .
  by fact+\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have h_1_2: "Q"
  proof-
    show h_1_1: "Q"
      unfolding Q_def
      using assms(1)
      . (* TRIVIAL LEAF *)
  qed
    (* BEGIN MAIN BODY *)
  have h_3_1: "Q"
    by ( ( fact )+ ) (* LEAF *)
  have h_1_3: "R"
    unfolding R_def
    by( fact h_1_2 ) 
  have h_2_1: "P"
    by ( fact ) (* LEAF *)
  have h_1_1: "Q"
    by ( subst Q_def )
      ( fact h_2_1 ) 
  show
    "Q"
    and "Q"
    and "R"
    by ( fact h_1_1, fact h_1_2, fact h_1_3 ) (* COMBINED SHOW *)
qed

subsection "Test 6"

text "Basically a simpler version of test 5 (we use this in the paper)"

lemma subgoal_test_6:
  assumes "P1" "P2"
  defines "Q \<equiv> P1"
  defines "R \<equiv> P2"
  shows "Q \<and> R" "R"
  apply2isar\<open>
  unfolding R_def
  subgoal
    unfolding Q_def by (rule conjI, (rule assms)+)
  by (rule assms(2))\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have h_2_1: "Q \<and> P2"
  proof-
    show h_1_1: "Q \<and> P2"
      unfolding Q_def
      by ( rule conjI , ( rule assms )+ ) (* LEAF *)
  qed
    (* BEGIN MAIN BODY *)
  have h_2_2: "P2"
    by ( rule assms ( 2 ) ) (* LEAF *)
  show
    h_1_1: "Q \<and> R"
    and h_1_2: "R"
    unfolding R_def
    by( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 7"

text "Fixing vars without user explicit providing the name"

lemma subgoal_test_7:
  fixes Q
  defines "P \<equiv> Q"
  assumes "\<forall>x. P x"
  shows "\<And>x y. Q x"
  apply2isar\<open>
  subgoal
    unfolding P_def[symmetric]
    using assms(2)
    by auto
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  show h_1_1: "\<And>(x::'a) y::'b. (Q::'a \<Rightarrow> bool) x"
  proof-
    fix xa ya
    show h_1_1: "Q xa"
      unfolding P_def[ symmetric ]
      using assms(2)
      by ( auto ) (* LEAF *)
  qed
qed

section "Subgoal fixing vars test"

(* declare[[apply2isar_avoid_subgoal_shadow = false]] *)

subsection "Test 1"

text "User only fixes one var, but there is more than one quantified var"

lemma subgoal_fixing_test_1:
  fixes Q
  defines "P \<equiv> Q"
  assumes "\<forall>x. P x"
  shows "\<And>x y. Q x"
  apply2isar\<open>
  subgoal for y
    unfolding P_def[symmetric]
    using assms(2)
    by auto
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  show h_1_1: "\<And>(x::'a) y::'b. (Q::'a \<Rightarrow> bool) x"
  proof-
    fix y yb
    show h_1_1: "Q y"
      unfolding P_def[ symmetric ]
      using assms(2)
      by ( auto ) (* LEAF *)
  qed
qed

subsection "Test 2"

text "Shadowing"

declare[[apply2isar_subgoal_fix_fresh = true]]

lemma subgoal_fixing_test_2:
  fixes x
  assumes Px: "P x"
  assumes imp: "P x \<Longrightarrow> (\<forall>y. P y)"
  shows "\<And>y. P y"
  apply2isar\<open>
  subgoal for x
    apply (rule spec[of P])
    apply (rule imp)
    by (rule Px)
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  show h_1_1: "\<And>y. P y"
  proof-
    fix xa
    have h_3_1: "P x"
      by ( rule Px ) (* LEAF *)
    have h_2_1: "\<forall>x. P x"
      by ( rule imp )
        ( fact h_3_1 ) 
    show h_1_1: "P xa"
      by ( rule spec [ of P ] )
        ( fact h_2_1 ) 
  qed
qed

subsection "Test 3"

text "Underscores"

lemma subgoal_fixing_test_3:
  fixes x
  assumes Px: "P x"
  assumes imp: "P x \<Longrightarrow> (\<forall>y. P y)"
  shows "\<And>x y. P y"
  apply2isar\<open>
  subgoal for _ x
    apply (rule spec[of P])
    apply (rule imp)
    by (rule Px)
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  show h_1_1: "\<And>(x::'b) y::'a. (P::'a \<Rightarrow> bool) y"
  proof-
    fix xc xa
    have h_3_1: "P x"
      by ( rule Px ) (* LEAF *)
    have h_2_1: "\<forall>x. P x"
      by ( rule imp )
        ( fact h_3_1 ) 
    show h_1_1: "P xa"
      by ( rule spec [ of P ] )
        ( fact h_2_1 ) 
  qed
qed

declare[[apply2isar_subgoal_fix_fresh = false]]

section "Subgoal premises test"

subsection "Test 1"

lemma subgoal_premises_1: "\<And>x. P x \<Longrightarrow> P x"
  apply2isar\<open>
  subgoal for x
    subgoal premises h
      by (simp add: h)
    done
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  show h_1_1: "\<And>x. P x \<Longrightarrow> P x"
  proof-
    fix x
      (* MOVED SUBPROOFS AND NOTES *)
    show h_1_1: "P x \<Longrightarrow> P x"
    proof-
      assume h:  "P x"
      show h_1_1: "P x"
        by ( simp add : h ) (* LEAF *)
    qed
  qed
qed

subsection "Test 2"

lemma subgoal_premises_2: "\<And>x y. P x \<Longrightarrow> Q x \<Longrightarrow> P x \<and> Q x"
  apply2isar\<open>
  subgoal for y
    subgoal premises h
      by (simp add: h)
    done
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  show h_1_1: "\<And>(x::'a) y::'b. (P::'a \<Rightarrow> bool) x \<Longrightarrow> (Q::'a \<Rightarrow> bool) x \<Longrightarrow> P x \<and> Q x"
  proof-
    fix y yb
      (* MOVED SUBPROOFS AND NOTES *)
    show h_1_1: "P y \<Longrightarrow> Q y \<Longrightarrow> P y \<and> Q y"
    proof-
      assume h: 
        "P y"
        "Q y"
      show h_1_1: "P y \<and> Q y"
        by ( simp add : h ) (* LEAF *)
    qed
  qed
qed

section "Subgoal label test"

subsection "Test 1"

lemma subgoal_label_1: "\<And>x. (P x \<Longrightarrow> (P x \<and> P x))"
  apply2isar\<open>
  apply (rule conjI)
  subgoal hi for x
    by (simp)
  by (rule hi)\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have hi: "\<And>x. P x \<Longrightarrow> P x"
  proof-
    fix x
    show h_1_1: "P x \<Longrightarrow> P x"
      by ( simp ) (* LEAF *)
  qed
    (* BEGIN MAIN BODY *)
  have h_2_2: "\<And>x. P x \<Longrightarrow> P x"
    by ( rule hi ) (* LEAF *)
  have h_2_1: "\<And>x. P x \<Longrightarrow> P x"
    by ( fact hi ) (* SUBPROOF DUMMY *)
  show h_1_1: "\<And>x. P x \<Longrightarrow> P x \<and> P x"
    by ( rule conjI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 2"

lemma subgoal_label_2: "(\<And>x. P x \<Longrightarrow> P x) &&& (\<And>x. P x \<Longrightarrow> P x)"
  apply2isar\<open>
  subgoal hi premises h for x
    by (simp add: h)
  by (rule hi)\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have hi: "\<And>x. P x \<Longrightarrow> P x"
  proof-
    fix x
    assume h:  "P x"
    show h_1_1: "P x"
      by ( simp add : h ) (* LEAF *)
  qed
    (* BEGIN MAIN BODY *)
  have h_1_2: "\<And>x. P x \<Longrightarrow> P x"
    by ( rule hi ) (* LEAF *)
  have h_1_1: "\<And>x. P x \<Longrightarrow> P x"
    by ( fact hi ) (* SUBPROOF DUMMY *)
  show
    "\<And>x. P x \<Longrightarrow> P x"
    and "\<And>x. P x \<Longrightarrow> P x"
    by ( fact h_1_1, fact h_1_2 ) (* COMBINED SHOW *)
qed

subsection "Test 3"

lemma subgoal_label_3:
  assumes "P"
  defines "Q \<equiv> P"
  shows "Q" "Q"
  apply2isar\<open>
  subgoal hi
    apply (subst Q_def)
    by (rule assms(1))
  subgoal hi2
    by (rule hi)
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have hi: "Q"
  proof-
    have h_2_1: "P"
      by ( rule assms ( 1 ) ) (* LEAF *)
    show h_1_1: "Q"
      by ( subst Q_def )
        ( fact h_2_1 ) 
  qed
  have hi2: "Q"
  proof-
    show h_1_1: "Q"
      by ( rule hi ) (* LEAF *)
  qed
    (* BEGIN MAIN BODY *)
  have h_1_2: "Q"
    by ( fact hi2 ) (* SUBPROOF DUMMY *)
  have h_1_1: "Q"
    by ( fact hi ) (* SUBPROOF DUMMY *)
  show
    "Q"
    and "Q"
    by ( fact h_1_1, fact h_1_2 ) (* COMBINED SHOW *)
qed

subsection "Test 4"

text "Demonstrates why we must apply using/unfolding data on subgoal"

lemma subgoal_label_test_4:
  fixes Q
  defines "P \<equiv> Q"
  assumes "Q"
  shows "P" "Q"
  apply2isar\<open>
  unfolding P_def
  subgoal hi
  proof-
    show "Q" using assms(2) by simp
  qed
  by (rule hi)\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have hi: "Q"
  proof-
    show h_1_1: "Q"
      (* SWITCH TO ISAR *)
    proof-
      show "Q" using assms(2) by simp
    qed
  qed
    (* BEGIN MAIN BODY *)
  have h_2_1: "Q"
    by ( rule hi ) (* LEAF *)
  have h_1_2: "Q"
    by ( fact hi ) (* SUBPROOF DUMMY *)
  have h_1_1: "P"
    unfolding P_def
    by( fact h_1_2 ) 
  show
    "P"
    and "Q"
    by ( fact h_1_1, fact h_1_2 ) (* COMBINED SHOW *)
qed

section "Multiple subgoals test"

(* Our tool tries to detect whether a tactic:
   (1) closes the first subgoal entirely (tactics like "blast", "force", "argo", etc.),
   (2) reduces the first subgoal to some other subgoals (tactics like "rule", "subst", "simp"),
   (3) or modifies all subgoals (tactics like "auto", "simp_all").

   These tests are meant to ensure this is working properly.
*)

subsection "Test 1"

declare[[apply2isar_named_facts = true]]

text "Operates on first subgoal yielding a single new subgoal"
lemma goals_test_1: "P \<longleftrightarrow> \<not> \<not> P"
  apply2isar\<open>
  apply (rule iffI)
   apply (rule cnf.clause2raw_not_not)
   apply simp
  apply simp
  done\<close>
proof-
  have h_2_2: "\<not> \<not> P \<Longrightarrow> P"
    by ( simp ) (* LEAF *)
  have h_3_1: "P \<Longrightarrow> P"
    by ( simp ) (* LEAF *)
  have h_2_1: "P \<Longrightarrow> \<not> \<not> P"
    by ( rule cnf.clause2raw_not_not )
      ( fact h_3_1 ) 
  show h_1_1: "P = (\<not> \<not> P)"
    by ( rule iffI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 2"

text "Closes all subgoals simultaneously."

lemma goals_test_2: "P \<longleftrightarrow> (P \<and> Q \<or> P \<and> \<not>Q)"
  apply2isar\<open>
  apply (rule iffI)
  by auto\<close>
proof-
  have
    h_2_1: "P \<Longrightarrow> P \<and> Q \<or> P \<and> \<not> Q"
    and h_2_2: "P \<and> Q \<or> P \<and> \<not> Q \<Longrightarrow> P"
    by ( auto ) (* LEAF *)
  show h_1_1: "P = (P \<and> Q \<or> P \<and> \<not> Q)"
    by ( rule iffI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 3"

(* Operates on first subgoal yielding multiple new subgoals *)
lemma goals_test_3: "(P \<longrightarrow> Q \<longrightarrow> (\<not>P \<or> Q) \<and> (P \<or> \<not>Q)) \<and> ((\<forall>x. R x) \<longrightarrow> (\<exists>x. R x))"
  apply2isar\<open>
  apply (rule conjI)
   apply (rule impI)
   apply (rule impI)
   apply (rule conjI)
    apply (rule disjI2)
    apply assumption
   apply (rule disjI1)
   apply assumption
  by blast\<close>
proof-
  have h_2_2: "(\<forall>x. R x) \<longrightarrow> (\<exists>x. R x)"
    by ( blast ) (* LEAF *)
  have h_7_1: "P \<Longrightarrow> Q \<Longrightarrow> P"
    by ( assumption ) (* LEAF *)
  have h_5_2: "P \<Longrightarrow> Q \<Longrightarrow> P \<or> \<not> Q"
    by ( rule disjI1 )
      ( fact h_7_1 ) 
  have h_6_1: "P \<Longrightarrow> Q \<Longrightarrow> Q"
    by ( assumption ) (* LEAF *)
  have h_5_1: "P \<Longrightarrow> Q \<Longrightarrow> \<not> P \<or> Q"
    by ( rule disjI2 )
      ( fact h_6_1 ) 
  have h_4_1: "P \<Longrightarrow> Q \<Longrightarrow> (\<not> P \<or> Q) \<and> (P \<or> \<not> Q)"
    by ( rule conjI )
      ( fact h_5_1, fact h_5_2 ) 
  have h_3_1: "P \<Longrightarrow> Q \<longrightarrow> (\<not> P \<or> Q) \<and> (P \<or> \<not> Q)"
    by ( rule impI )
      ( fact h_4_1 ) 
  have h_2_1: "P \<longrightarrow> Q \<longrightarrow> (\<not> P \<or> Q) \<and> (P \<or> \<not> Q)"
    by ( rule impI )
      ( fact h_3_1 ) 
  show h_1_1: "(P \<longrightarrow> Q \<longrightarrow> (\<not> P \<or> Q) \<and> (P \<or> \<not> Q)) \<and> ((\<forall>x. R x) \<longrightarrow> (\<exists>x. R x))"
    by ( rule conjI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 4"

text "Closes first subgoal entirely."

lemma goal_test_4: "(P \<or> \<not> P) \<and> (P \<longrightarrow> P)"
  apply2isar\<open>
  apply (rule conjI)
   apply simp
  by simp\<close>
proof-
  have h_2_2: "P \<longrightarrow> P"
    by ( simp ) (* LEAF *)
  have h_2_1: "P \<or> \<not> P"
    by ( simp ) (* LEAF *)
  show h_1_1: "(P \<or> \<not> P) \<and> (P \<longrightarrow> P)"
    by ( rule conjI )
      ( fact h_2_1, fact h_2_2 ) 
qed

section "Unfolding tests"

subsection "Test 1"

lemma unfolding_test_1:
  fixes Q
  defines "P \<equiv> \<lambda>x. Q x"
  shows "P x \<longleftrightarrow> Q x"
  apply2isar\<open>
  unfolding P_def
  by (rule refl)\<close>
proof-
  show h_1_1: "P x = Q x"
    unfolding P_def
    by ( rule refl ) (* LEAF *)
qed

subsection "Test 2"

text "Tests interaction with switching to terminal Isar."

lemma unfolding_test_2:
  fixes Q
  defines "P \<equiv> \<lambda>x. Q x"
  shows "P x \<longleftrightarrow> Q x"
  apply2isar\<open>
  unfolding P_def
proof-
  show "Q x = Q x" by (rule refl)
qed\<close>
proof-
  show h_1_1: "P x = Q x"
    (* SWITCH TO ISAR *)
    unfolding P_def
  proof-
    show "Q x = Q x" by (rule refl)
  qed
qed

section "Prefer test"

subsection "Test 1"

lemma "(P \<longleftrightarrow> P) \<and> (P \<or> \<not> P)"
  apply2isar\<open>
  apply (rule conjI)
   prefer 2
   apply (cases P)
    apply (rule disjI1, assumption)
   apply (rule disjI2, assumption)
  by (rule refl)\<close>
proof-
  have h_2_1: "P = P"
    by ( rule refl ) (* LEAF *)
  have h_3_2: "\<not> P \<Longrightarrow> P \<or> \<not> P"
    by ( rule disjI2 , assumption ) (* LEAF *)
  have h_3_1: "P \<Longrightarrow> P \<or> \<not> P"
    by ( rule disjI1 , assumption ) (* LEAF *)
  have h_2_2: "P \<or> \<not> P"
    by ( cases P )
      ( fact h_3_1, fact h_3_2 ) 
  show h_1_1: "P = P \<and> (P \<or> \<not> P)"
    by ( rule conjI )
      ( fact h_2_1, fact h_2_2 ) 
qed

section "Defer test"

subsection "Test 1"

lemma "(P \<longleftrightarrow> P) \<and> (P \<or> \<not> P)"
  apply2isar\<open>
  apply (rule conjI)
   defer
   apply (cases P)
    apply (rule disjI1, assumption)
   apply (rule disjI2, assumption)
  by (rule refl)\<close>
proof-
  have h_2_1: "P = P"
    by ( rule refl ) (* LEAF *)
  have h_3_2: "\<not> P \<Longrightarrow> P \<or> \<not> P"
    by ( rule disjI2 , assumption ) (* LEAF *)
  have h_3_1: "P \<Longrightarrow> P \<or> \<not> P"
    by ( rule disjI1 , assumption ) (* LEAF *)
  have h_2_2: "P \<or> \<not> P"
    by ( cases P )
      ( fact h_3_1, fact h_3_2 ) 
  show h_1_1: "P = P \<and> (P \<or> \<not> P)"
    by ( rule conjI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 2"

text "Also tests edge case behavior of immediate proof."

lemma "(P \<longleftrightarrow> P) \<and> (P \<or> \<not> P)" "P \<longleftrightarrow> P"
  apply2isar\<open>
  apply (rule conjI)
    defer 2
    apply (rule refl)
   apply (rule refl)
  subgoal
    apply (cases P)
     apply (rule disjI1, assumption)
    apply (rule disjI2, assumption)
    .
  .\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have h_2_1: "P \<or> \<not> P"
  proof-
    have h_2_2: "\<not> P \<Longrightarrow> P \<or> \<not> P"
      by ( rule disjI2 , assumption ) (* LEAF *)
    have h_2_1: "P \<Longrightarrow> P \<or> \<not> P"
      by ( rule disjI1 , assumption ) (* LEAF *)
    show h_1_1: "P \<or> \<not> P"
      by ( cases P )
        ( fact h_2_1, fact h_2_2 ) 
  qed
    (* BEGIN MAIN BODY *)
  have h_2_2: "P = P"
    by ( rule refl ) (* LEAF *)
  have h_1_2: "P = P"
    by ( rule refl ) (* LEAF *)
  have h_1_1: "P = P \<and> (P \<or> \<not> P)"
    by ( rule conjI )
      ( fact h_1_2, fact h_2_1 ) 
  show
    "P = P \<and> (P \<or> \<not> P)"
    and "P = P"
    by ( fact h_1_1, fact h_1_2 ) (* COMBINED SHOW *)
qed

section "Combinators Tests"

(* Tests for combinators like simp[2], blast+ etc. *)

subsection "Test 1"

(* Testing + combinator*)
lemma combinators_test_1: "(P \<longleftrightarrow> P) \<and> (P \<or> \<not> P)"
  apply2isar\<open>
  apply (rule conjI)
  by simp+\<close>
proof-
  have
    h_2_1: "P = P"
    and h_2_2: "P \<or> \<not> P"
    by ( ( simp )+ ) (* LEAF *)
  show h_1_1: "P = P \<and> (P \<or> \<not> P)"
    by ( rule conjI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 2"

lemma combinators_test_2: "(P \<longleftrightarrow> P) \<and> (P \<or> \<not> P)"
  apply2isar\<open>
  by ((auto | simp add: conjI)? | auto, simp+)[1]\<close>
proof-
  show h_1_1: "P = P \<and> (P \<or> \<not> P)"
    by ( ( ( auto | simp add : conjI )? | auto , ( simp )+ )[1] ) (* LEAF *)
qed

section "Switching from apply-style to Isar test"

subsection "Test 1"

lemma apply_apply2isar_test_1: "P \<longleftrightarrow> P"
  apply2isar\<open>
  apply (rule iffI)
proof-
  show "P" if "P" using that by blast
  show "P" if "P" using that by blast
qed\<close>
proof-
  have
    h_2_1: "P \<Longrightarrow> P"
    and h_2_2: "P \<Longrightarrow> P"
    (* SWITCH TO ISAR *)
  proof-
    show "P" if "P" using that by blast
    show "P" if "P" using that by blast
  qed
  show h_1_1: "P = P"
    by ( rule iffI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 2"

lemma apply_apply2isar_test_2: "P \<longleftrightarrow> P"
  apply2isar\<open>
  apply (rule iffI)
  subgoal
  proof-
    show "P" if "P" using that by blast
  qed
  subgoal
  proof-
    show "P \<Longrightarrow> P" by simp
  qed
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have h_2_1: "P \<Longrightarrow> P"
  proof-
    show h_1_1: "P \<Longrightarrow> P"
      (* SWITCH TO ISAR *)
    proof-
      show "P" if "P" using that by blast
    qed
  qed
  have h_2_2: "P \<Longrightarrow> P"
  proof-
    show h_1_1: "P \<Longrightarrow> P"
      (* SWITCH TO ISAR *)
    proof-
      show "P \<Longrightarrow> P" by simp
    qed
  qed
    (* BEGIN MAIN BODY *)
  show h_1_1: "P = P"
    by ( rule iffI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 3"

lemma apply_apply2isar_test_3: "\<And>x. ((P \<longleftrightarrow> P) \<and> (Q x \<or> \<not> Q x)) \<and> (R x \<or> \<not> R x)"
  apply2isar\<open>
  apply (rule conjI)+
  subgoal
  proof-
    show ?thesis by blast
  qed
  subgoal for x
  proof-
    show ?thesis by blast
  qed
  subgoal for y
  proof-
    show ?thesis by simp
  qed
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have h_2_1: "\<And>x::'a. (P::bool) = P"
  proof-
    fix xa
    show h_1_1: "P = P"
      (* SWITCH TO ISAR *)
    proof-
      show ?thesis by blast
    qed
  qed
  have h_2_2: "\<And>x. Q x \<or> \<not> Q x"
  proof-
    fix x
    show h_1_1: "Q x \<or> \<not> Q x"
      (* SWITCH TO ISAR *)
    proof-
      show ?thesis by blast
    qed
  qed
  have h_2_3: "\<And>x. R x \<or> \<not> R x"
  proof-
    fix y
    show h_1_1: "R y \<or> \<not> R y"
      (* SWITCH TO ISAR *)
    proof-
      show ?thesis by simp
    qed
  qed
    (* BEGIN MAIN BODY *)
  show h_1_1: "\<And>x. (P = P \<and> (Q x \<or> \<not> Q x)) \<and> (R x \<or> \<not> R x)"
    by ( ( rule conjI )+ )
      ( fact h_2_1, fact h_2_2, fact h_2_3 ) 
qed

subsection "Test 4"

lemma apply_apply2isar_test_4: "\<And>x. (P \<longleftrightarrow> P) \<and> (Q x \<or> \<not> Q x)"
  apply2isar\<open>
  apply (rule conjI)
  subgoal
  proof-
    show ?thesis by blast
  qed
  proof-
    show "Q x \<or> \<not> Q x" for x by blast
  qed\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have h_2_1: "\<And>x::'a. (P::bool) = P"
  proof-
    fix xa
    show h_1_1: "P = P"
      (* SWITCH TO ISAR *)
    proof-
      show ?thesis by blast
    qed
  qed
    (* BEGIN MAIN BODY *)
  have h_2_2: "\<And>x. Q x \<or> \<not> Q x"
    (* SWITCH TO ISAR *)
  proof-
    show "Q x \<or> \<not> Q x" for x by blast
  qed
  show h_1_1: "\<And>x. P = P \<and> (Q x \<or> \<not> Q x)"
    by ( rule conjI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 5"

lemma apply_apply2isar_test_5: "\<And>x. (P \<longleftrightarrow> P) \<and> (Q x \<or> \<not> Q x)"
  apply2isar\<open>
  apply (rule conjI)
  subgoal
    subgoal
      subgoal 
      proof-
        show ?thesis by blast
      qed
    done
  done
  proof-
    show "Q x \<or> \<not> Q x" for x by blast
  qed\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have h_2_1: "\<And>x::'a. (P::bool) = P"
  proof-
    fix xa
      (* MOVED SUBPROOFS AND NOTES *)
    show h_1_1: "P = P"
    proof-
      (* MOVED SUBPROOFS AND NOTES *)
      show h_1_1: "P = P"
      proof-
        show h_1_1: "P = P"
          (* SWITCH TO ISAR *)
        proof-
          show ?thesis by blast
        qed
      qed
    qed
  qed
    (* BEGIN MAIN BODY *)
  have h_2_2: "\<And>x. Q x \<or> \<not> Q x"
    (* SWITCH TO ISAR *)
  proof-
    show "Q x \<or> \<not> Q x" for x by blast
  qed
  show h_1_1: "\<And>x. P = P \<and> (Q x \<or> \<not> Q x)"
    by ( rule conjI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Test 6"

lemma apply_apply2isar_test_6:
  assumes "P"
  shows "P" "Q \<or> P" "Q \<or> \<not> Q"
  apply2isar\<open>
    apply (rule assms)
proof-
  show "Q \<or> P" using assms by simp
qed (simp add: assms)\<close>
proof-
  have
    h_1_2: "Q \<or> P"
    and h_1_3: "Q \<or> \<not> Q"
    (* SWITCH TO ISAR *)
  proof-
    show "Q \<or> P" using assms by simp
  qed ( simp add : assms )
  have h_1_1: "P"
    by ( rule assms ) (* LEAF *)
  show
    "P"
    and "Q \<or> P"
    and "Q \<or> \<not> Q"
    by ( fact h_1_1, fact h_1_2, fact h_1_3 ) (* COMBINED SHOW *)
qed

subsection "Test 7"

text "Testing integration with unfolding"

lemma apply_apply2isar_test_7:
  assumes "P"
  defines "Q \<equiv> P"
  defines "R \<equiv> Q"
  shows "Q" "R" "P"
  apply2isar\<open>
    apply (subst Q_def)
    apply fact
  unfolding R_def Q_def
  proof-
    show "P" by fact
    show "P" by fact
  qed\<close>
proof-
  have
    h_1_2: "R"
    and h_2_1: "P"
    (* SWITCH TO ISAR *)
    unfolding R_def Q_def
  proof-
    show "P" by fact
    show "P" by fact
  qed
  have h_1_3: "P"
    by ( fact ) (* LEAF *)
  have h_1_1: "Q"
    by ( subst Q_def )
      ( fact h_1_3 ) 
  show
    "Q"
    and "R"
    and "P"
    by ( fact h_1_1, fact h_1_2, fact h_1_3 ) (* COMBINED SHOW *)
qed

section "Type annotations tests"

subsubsection "Test 1 (FIXED)"

declare[[apply2isar_print_types = necessary]]

lemma types_test_1': "(\<forall>x :: nat. 0 \<le> x) \<and> (\<not> (a::int) < b \<longrightarrow> \<not> b < a \<longrightarrow> a = b)"
  apply2isar\<open>apply (rule conjI)
  subgoal
    apply simp
    done
  apply clarify
  apply (rule antisym)
  subgoal
    apply auto
    done
  subgoal
    apply linarith
    done
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have h_2_1: "\<forall>x::nat. (0::nat) \<le> x"
  proof-
    show h_1_1: "\<forall>x::nat. (0::nat) \<le> x"
      by ( simp ) (* LEAF *)
  qed
  have h_4_1: "\<not> a < b \<Longrightarrow> \<not> b < a \<Longrightarrow> a \<le> b"
  proof-
    show h_1_1: "\<not> a < b \<Longrightarrow> \<not> b < a \<Longrightarrow> a \<le> b"
      by ( auto ) (* LEAF *)
  qed
  have h_4_2: "\<not> a < b \<Longrightarrow> \<not> b < a \<Longrightarrow> b \<le> a"
  proof-
    show h_1_1: "\<not> a < b \<Longrightarrow> \<not> b < a \<Longrightarrow> b \<le> a"
      by ( linarith ) (* LEAF *)
  qed
    (* BEGIN MAIN BODY *)
  have h_3_1: "\<not> a < b \<Longrightarrow> \<not> b < a \<Longrightarrow> a = b"
    by ( rule antisym )
      ( fact h_4_1, fact h_4_2 ) 
  have h_2_2: "\<not> a < b \<longrightarrow> \<not> b < a \<longrightarrow> a = b"
    by ( clarify )
      ( fact h_3_1 ) 
  show h_1_1: "(\<forall>x::nat. (0::nat) \<le> x) \<and> (\<not> (a::int) < (b::int) \<longrightarrow> \<not> b < a \<longrightarrow> a = b)"
    by ( rule conjI )
      ( fact h_2_1, fact h_2_2 ) 
qed

subsection "Subst under meta quantifier"

text "These used to not work, but with the improved robustness they now work perfectly."

subsection "Test 1"

lemma subst_meta_1: "\<And>x. (P \<longleftrightarrow> P) \<and> (Q x \<or> \<not> Q x) \<and> (R x \<or> \<not> R x)"
  apply2isar\<open>
  apply (subst conj_assoc[symmetric])
  apply (rule conjI)+
  subgoal
  proof-
    show ?thesis by blast
  qed
  subgoal for x
  proof-
    show ?thesis by blast
  qed
  subgoal for y
  proof-
    show ?thesis by simp
  qed
  done\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have h_3_1: "\<And>x::'a. (P::bool) = P"
  proof-
    fix xa
    show h_1_1: "P = P"
      (* SWITCH TO ISAR *)
    proof-
      show ?thesis by blast
    qed
  qed
  have h_3_2: "\<And>x. Q x \<or> \<not> Q x"
  proof-
    fix x
    show h_1_1: "Q x \<or> \<not> Q x"
      (* SWITCH TO ISAR *)
    proof-
      show ?thesis by blast
    qed
  qed
  have h_3_3: "\<And>x. R x \<or> \<not> R x"
  proof-
    fix y
    show h_1_1: "R y \<or> \<not> R y"
      (* SWITCH TO ISAR *)
    proof-
      show ?thesis by simp
    qed
  qed
    (* BEGIN MAIN BODY *)
  have h_2_1: "\<And>x. (P = P \<and> (Q x \<or> \<not> Q x)) \<and> (R x \<or> \<not> R x)"
    by ( ( rule conjI )+ )
      ( fact h_3_1, fact h_3_2, fact h_3_3 ) 
  show h_1_1: "\<And>x. P = P \<and> (Q x \<or> \<not> Q x) \<and> (R x \<or> \<not> R x)"
    by ( subst conj_assoc [ symmetric ] )
      ( fact h_2_1 ) 
qed

subsection "Test 2"

lemma misc_brittle_2':
  fixes P
  defines "Q \<equiv> P"
  shows "\<And>x. Q x \<longleftrightarrow> P x"
  apply2isar\<open>
  apply (subst Q_def)
  apply (rule iffI)
   apply simp
  by simp\<close>
proof-
  have h_3_2: "\<And>x. P x \<Longrightarrow> P x"
    by ( simp ) (* LEAF *)
  have h_3_1: "\<And>x. P x \<Longrightarrow> P x"
    by ( simp ) (* LEAF *)
  have h_2_1: "\<And>x. P x = P x"
    by ( rule iffI )
      ( fact h_3_1, fact h_3_2 ) 
  show h_1_1: "\<And>x. Q x = P x"
    by ( subst Q_def )
      ( fact h_2_1 ) 
qed

section "Resolution tests"

lemma resolution_test_1:
  assumes "A"
  assumes "A \<Longrightarrow> B"
  assumes "B \<Longrightarrow> C"
  assumes "C \<Longrightarrow> D"
  shows "D" "C"
  apply2isar\<open>
  apply (rule assms(4))
  apply (rule assms(3))
   apply (rule assms(2))
  apply (rule assms(1))
  apply (rule assms(3))
  apply (rule assms(2))
  by (rule assms(1))\<close>
proof-
  have h_6_1: "A"
    by ( rule assms ( 1 ) ) (* LEAF *)
  have h_5_1: "B"
    by ( rule assms ( 2 ) )
      ( fact h_6_1 ) 
  have h_2_1: "C"
    by ( rule assms ( 3 ) )
      ( fact h_5_1 ) 
  have h_4_1: "A"
    by ( rule assms ( 1 ) ) (* LEAF *)
  have h_3_1: "B"
    by ( rule assms ( 2 ) )
      ( fact h_4_1 ) 
  have h_1_2: "C"
    by ( rule assms ( 3 ) )
      ( fact h_3_1 ) 
  have h_1_1: "D"
    by ( rule assms ( 4 ) )
      ( fact h_1_2 ) 
  show
    "D"
    and "C"
    by ( fact h_1_1, fact h_1_2 ) (* COMBINED SHOW *)
qed

section "Back test"

declare[[apply2isar_print_types = false]]

subsection "Test 1"

text "From the Isabelle tutorial"

lemma back_test_1: "\<lbrakk> x = f x; triple (f x) (f x) x \<rbrakk> \<Longrightarrow> triple x x x"
  apply2isar\<open>
  apply (erule ssubst)
  back
  back
  back
  back
  apply assumption
  done\<close>
proof-
  have h_2_1: "triple (f x) (f x) x \<Longrightarrow> triple (f x) (f x) x"
    by ( assumption ) (* LEAF *)
  show h_1_1: "x = f x \<Longrightarrow> triple (f x) (f x) x \<Longrightarrow> triple x x x"
    by ( erule ssubst )
      ( fact h_2_1 ) 
qed

section "Supply test"

subsection "Test 1"

lemma supply_test_1: "True" "P \<Longrightarrow> P \<or> Q"
  apply2isar\<open>
   supply myThms = TrueI disjI1
   apply (rule myThms(1))
  by (rule myThms(2))\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  note myThms = TrueI disjI1
    (* BEGIN MAIN BODY *)
  have h_1_2: "P \<Longrightarrow> P \<or> Q"
    by ( rule myThms ( 2 ) ) (* LEAF *)
  have h_1_1: "True"
    by ( rule myThms ( 1 ) ) (* LEAF *)
  show
    "True"
    and "P \<Longrightarrow> P \<or> Q"
    by ( fact h_1_1, fact h_1_2 ) (* COMBINED SHOW *)
qed

subsection "Test 2"

lemma supply_test_2:
  assumes "\<And>x. (P x \<Longrightarrow> (P x \<and> P x))"
  shows "\<And>x. (P x \<Longrightarrow> (P x \<and> P x))"
  apply2isar\<open>
  supply TrueI[simp]
  supply b = TrueI[[simproc del: defined_all, simproc del: defined_all]]
  by (rule assms)
\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  note TrueI[ simp ]
  note b = TrueI [[ simproc del : defined_all, simproc del : defined_all ]]
    (* BEGIN MAIN BODY *)
  show h_1_1: "\<And>x. P x \<Longrightarrow> P x \<and> P x"
    by ( rule assms ) (* LEAF *)
qed

section "Sorry test"

subsection "Test 1"

lemma sorry_test_1:
  assumes "P \<Longrightarrow> Q"
  shows "R \<Longrightarrow> Q"
  apply2isar\<open>
  apply (rule assms)
  sorry\<close>
proof-
  have h_2_1: "R \<Longrightarrow> P"
    sorry
  show h_1_1: "R \<Longrightarrow> Q"
    by ( rule assms )
      ( fact h_2_1 ) 
qed

subsection "Test 2"

lemma sorry_test_2:
  shows "P" "Q" "R" "S"
  apply2isar\<open>
  subgoal using conjI sorry
  subgoal unfolding TrueI sorry
  sorry\<close>
proof-
  (* MOVED SUBPROOFS AND NOTES *)
  have h_1_1: "P"
  proof-
    show h_1_1: "P"
      using conjI
      sorry
  qed
  have h_1_2: "Q"
  proof-
    show h_1_1: "Q"
      unfolding TrueI
      sorry
  qed
    (* BEGIN MAIN BODY *)
  have
    h_1_3: "R"
    and h_1_4: "S"
    sorry
  show
    "P"
    and "Q"
    and "R"
    and "S"
    by ( fact h_1_1, fact h_1_2, fact h_1_3, fact h_1_4 ) (* COMBINED SHOW *)
qed

section "Schematic goals test"

subsection "Test 1"

lemma schematic_test_1:
  assumes Px: "P x" and B: "B"
  shows "(\<exists>x. P x) \<and> B"
  apply2isar\<open>
  apply (rule conjI, intro exI)
proof-
  show "P x" by (rule Px)
qed (simp add: B)\<close>
    (* @SCHEMATIC *)
proof-
  show h_1_1: "(\<exists>x. P x) \<and> B"
    apply ( rule conjI , intro exI )
      (* SWITCH TO ISAR *)
  proof-
    show "P x" by (rule Px)
  qed ( simp add : B )
qed

end
