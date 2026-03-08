theory Prep2Isar
  imports Apply2Isar
  keywords
    "prep2isar" :: thy_decl and
    "apply2noop" :: prf_script % "proof" and
    "apply2sorry" :: prf_script % "proof"
begin

ML\<open>

fun is_proof_command tok =
  Token.is_command tok andalso (
    Token.unparse tok = "apply"
    orelse Token.unparse tok = "subgoal"
    orelse Token.unparse tok = "using"
    orelse Token.unparse tok = "unfolding"
    orelse Token.unparse tok = "prefer"
    orelse Token.unparse tok = "defer"
    orelse Token.unparse tok = "supply"
    orelse Token.unparse tok = "by"
    orelse Token.unparse tok = "done"
    orelse Token.unparse tok = "."
    orelse Token.unparse tok = ".."
    orelse Token.unparse tok = "back"
  )

val str_of_toks = map Token.unparse #> implode

fun
  any _ [] = false
| any P (x :: xs) = P x orelse any P xs

fun wrap_cond tok =
  Token.is_command tok andalso (
    Token.unparse tok = "apply"
    orelse Token.unparse tok = "subgoal"
    orelse Token.unparse tok = "prefer"
    orelse Token.unparse tok = "defer"
    orelse Token.unparse tok = "supply"
  )

fun
  prepend_after_opening_whitespace x [] = [ x ]
| prepend_after_opening_whitespace x (tok :: toks) =
  if Token.is_blank tok orelse Token.is_space tok orelse Token.is_newline tok then
    (Token.unparse tok) :: (prepend_after_opening_whitespace x toks)
  else
    x :: (Token.unparse tok) :: map Token.unparse toks

fun append_before_closing_whitespace x = rev #> prepend_after_opening_whitespace x #> rev #> implode

val open_cartouche = "\\" ^ "<open>"

val close_cartouche = "\\" ^ "<close>(*CLOSE_TAG*)sorry"

fun apply2isar_wrap toks =
  if any wrap_cond toks then
    ("apply2isar" ^ open_cartouche ^ (append_before_closing_whitespace close_cartouche toks) ^ "\n")
  else
    str_of_toks toks

fun
  prep' toks_acc _ _ [] = toks_acc
| prep' toks_acc buffer in_proof (tok :: toks) =
  if is_proof_command tok then
    prep' toks_acc (buffer @ [ tok ]) true toks
  else if Token.is_command tok andalso Token.unparse tok = "proof" andalso in_proof then
  let
    val (isar_toks, toks') = term_isar_parser0' 1 0 toks
  in
    prep' toks_acc (buffer @ (tok :: isar_toks)) in_proof toks'
  end
  else if Token.is_command tok orelse Token.is_eof tok then (* tok is a command but not a proof command *)
    prep' (toks_acc ^ (apply2isar_wrap buffer) ^ (Token.unparse tok)) [] false toks
  else if in_proof then (* We're in a proof and tok isn't a non-proof command, so the proof hasn't ended *)
    prep' toks_acc (buffer @ [ tok ]) true toks
  else (* We're not in a proof and tok didn't start a proof *)
    prep' (toks_acc ^ (Token.unparse tok)) buffer false toks
    


val prep = prep' "" [] false

fun prep_apply2isar m =
let
  val keywords = Thy_Header.get_keywords' @{context}
  val toks = (Token.explode0 keywords m) @ [Token.eof]
  val toks' = toks |> prep
  val _ = writeln (Active.sendback_markup_command toks')
in
  ()
end

fun tacs_to_isar' proof_str st =
  let
    val _ = apply2isar proof_str st
  in
    Seq.make_results (Seq.single st)
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>prep2isar\<close> "Processes an entire theory document and wraps apply-style proofs in apply2isar\<open>\<close> blocks." (
    (toks_debug @{context} "all" Parse.cartouche)
    >> (fn m => (prep_apply2isar m; I)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply2noop\<close> "Parses a cartouche then does nothing." (
    (toks_debug @{context} "all" Parse.cartouche)
    >> K (Toplevel.proofs (Seq.single #> Seq.make_results)));

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply2sorry\<close> "Parses a cartouche then runs sorry." (
    (toks_debug @{context} "all" Parse.cartouche)
    >> K Isar_Cmd.skip_proof);

\<close>

declare[[apply2isar_print_types = "necessary"]]
declare[[apply2isar_smart_goals = true]]
declare[[apply2isar_smart_unfolds = true]]
declare[[apply2isar_named_facts = true]]
declare[[apply2isar_subgoal_fix_fresh = false]]
declare[[apply2isar_linebreaks = false]]
declare[[apply2isar_timeout = 30]]

end
