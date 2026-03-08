theory Apply2Isar
  imports Main
  keywords
    "apply2isar" :: prf_script % "proof"

begin

section "Setup"

ML \<open>

(* Tracing *)

val trace_flag = Attrib.setup_config_bool \<^binding>\<open>apply2isar_tracing\<close> (K false);

fun cond_trace flag f x = if flag then tracing ("Apply2Isar: " ^ f x) else ();

fun trace_msg ctxt = cond_trace (Config.get ctxt trace_flag);

fun pretty tag lines = map Pretty.str lines |> Pretty.big_list tag |> Pretty.string_of

fun print_message ctxt a b = trace_msg ctxt (pretty ("(" ^ a ^ ", " ^ b ^ ")")) []

(* Option flags *)

val print_types_flag = Attrib.setup_config_string \<^binding>\<open>apply2isar_print_types\<close> (K "necessary");

val smart_goals_flag = Attrib.setup_config_bool \<^binding>\<open>apply2isar_smart_goals\<close> (K true);

val smart_unfolds_flag = Attrib.setup_config_bool \<^binding>\<open>apply2isar_smart_unfolds\<close> (K true);

val named_facts_flag = Attrib.setup_config_bool \<^binding>\<open>apply2isar_named_facts\<close> (K true);

val dummy_subproofs_flag = Attrib.setup_config_bool \<^binding>\<open>apply2isar_dummy_subproofs\<close> (K false);

val subgoal_fix_fresh_flag = Attrib.setup_config_bool \<^binding>\<open>apply2isar_subgoal_fix_fresh\<close> (K false);

val linebreaks_flag = Attrib.setup_config_bool \<^binding>\<open>apply2isar_linebreaks\<close> (K false);

val fact_name_prefix_opt =
  Attrib.setup_config_string \<^binding>\<open>apply2isar_fact_name_prefix\<close> (K "h");

val timeout_opt = Attrib.setup_config_int \<^binding>\<open>apply2isar_timeout\<close> (K 30);

type apply2isar_options = {
  smart_goals : bool,
  dummy_subproofs : bool,
  named_facts : bool,
  smart_unfolds : bool,
  subgoal_fix_fresh : bool,
  fact_name_prefix : string,
  linebreaks : bool
}

fun options_from_ctxt ctxt = {
  smart_goals = Config.get ctxt smart_goals_flag,
  dummy_subproofs = Config.get ctxt dummy_subproofs_flag,
  named_facts = Config.get ctxt named_facts_flag,
  smart_unfolds = Config.get ctxt smart_unfolds_flag,
  subgoal_fix_fresh = Config.get ctxt subgoal_fix_fresh_flag,
  fact_name_prefix = Config.get ctxt fact_name_prefix_opt,
  linebreaks = Config.get ctxt linebreaks_flag
} : apply2isar_options

(* Misc. utils *)

fun
  any _ [] = false
| any P (x :: xs) = P x orelse any P xs

fun set_print_types_to b ctxt =
  ctxt
    |> Config.put (Printer.show_types) b
    |> Config.put (Printer.show_markup) b

val contains_prop = exists_subtype (can \<^Type_fn>\<open>prop => \<open>()\<close>\<close>)

val contains_tvar = exists_subtype Term.is_TVar

val contains_itself = exists_subtype (fn (Type ("itself", _)) => true | _ => false)

fun
  strip_bad_constraints ctxt ((c as Const ("_type_constraint_", ty)) $ t) =
    if contains_prop ty orelse contains_tvar ty orelse contains_itself ty then  
      (print_message ctxt "stripping type constraint" (Syntax.string_of_typ ctxt ty);
      strip_bad_constraints ctxt t)
    else
      c $ strip_bad_constraints ctxt t
  | strip_bad_constraints ctxt (t $ u) = strip_bad_constraints ctxt t $ strip_bad_constraints ctxt u
  | strip_bad_constraints ctxt (Abs (x, T, t)) = Abs (x, T, strip_bad_constraints ctxt t)
  | strip_bad_constraints _ a = a;

exception No_Term_Eq_Original

fun
  try_pps1 _ fallback_pp [] tm = fallback_pp tm
| try_pps1 ctxt fallback_pp (pp :: pps) tm =
let
  val tm_str = pp tm
in
  case try (singleton (Syntax.read_terms ctxt)) tm_str of
    SOME tm' => if tm aconv tm' then tm_str else try_pps1 ctxt fallback_pp pps tm
  | NONE => try_pps1 ctxt fallback_pp pps tm
end

fun
  try_pps2 _ fallback_pp [] tm = fallback_pp tm
| try_pps2 ctxt fallback_pp (pp :: pps) tm =
let
  val tm_str = pp tm
in
  case try (singleton (Syntax.read_terms ctxt)) tm_str of
    SOME _ => tm_str
  | NONE => try_pps2 ctxt fallback_pp pps tm
end

fun try_pps ctxt fallback_pp pps1 pps2 = try_pps1 ctxt (try_pps2 ctxt fallback_pp pps2) pps1

fun print_term ctxt tm =
let
  val tm = if HOLogic.is_Trueprop tm then HOLogic.dest_Trueprop tm else tm (* Shadowing *)
  val ctxt_types = ctxt |> set_print_types_to true
  val pp_no_types =
    Syntax.unparse_term (ctxt |> set_print_types_to false)
    #> Pretty.pure_string_of
  val pp_types =
    Syntax.unparse_term ctxt_types
    #> Pretty.pure_string_of
  val pp1 = 
    singleton (Syntax.uncheck_terms ctxt_types)
    #> Sledgehammer_Isar_Annotate.annotate_types_in_term ctxt_types
    #> strip_bad_constraints ctxt_types
    #> pp_types
  val pp2 =
    Sledgehammer_Isar_Annotate.annotate_types_in_term ctxt_types
    #> strip_bad_constraints ctxt_types
    #> pp_types
  val pp3 =
    strip_bad_constraints ctxt_types
    #> pp_types
in
  case Config.get ctxt print_types_flag of
    "none" =>
      tm |> pp_no_types |> Sledgehammer_Util.simplify_spaces
  | "necessary" =>
      try_pps
        ctxt
        (fn _ => raise No_Term_Eq_Original)
        [ pp_no_types, pp1, pp2, pp3 ]
        [ pp1, pp2, pp3 ]
        tm
  | "all" =>
      try_pps
        ctxt
        (fn _ => raise No_Term_Eq_Original)
        [ pp1, pp2, pp3 ]
        [ pp1, pp2, pp3 ]
        tm
  | _ =>
      tm |> pp_no_types |> Sledgehammer_Util.simplify_spaces
end


fun toks_to_string (toks : Token.T list) =
  toks
  |> map Token.text_of
  |> map (fn (a,b) => "( " ^ a ^ ", " ^ b ^ " )\n")
  |> implode

fun toks_debug ctxt tag parser toks = ((print_message ctxt tag (toks_to_string toks)); parser toks)

fun str_debug ctxt tag f s = ((print_message ctxt tag s); f s)

open List

fun singleton x = [x]

fun interior xs = drop (take (xs, length xs - 1), 1)

fun add_delims delim strs = (map (fn s => s @ [delim]) (take (strs, (length strs - 1)))) @ [last strs]

fun join delim xs = if xs = [] then "" else foldr1 (fn (s, s') => s ^ delim ^ s') xs

fun quote s = "\"" ^ (s |> Sledgehammer_Util.simplify_spaces) ^ "\""

fun quote_level (opts : apply2isar_options) level s =
  if #linebreaks opts then let
    val num_spaces = 2 * level + 4
    val spaces = foldr (op ^) "" (map (K " ") (1 upto num_spaces))
    fun add_spaces c = if String.str c = "\n" then "\n" ^ spaces else String.str c
    val s' = String.translate add_spaces s
  in
    "\"" ^ s' ^ "\""
  end
  else
    quote s

exception Concl_Not_Prop

fun no_prop_concl_of thm =
  case Thm.concl_of thm of
    Const ("Pure.prop", _) $ t => t
  | _ => raise Concl_Not_Prop

fun concls_of_state st =
  st
  |> Proof.raw_goal
  |> #goal
  |> no_prop_concl_of
  |> Logic.dest_conjunctions
  |> map (print_term (Proof.context_of st))

fun parse_while P =
  Scan.repeat (
    Scan.unless Parse.eof (Scan.one P)
  )

val apply2isar_if_label = "apply2isar_if"

\<close>

section "Parse tokens to proof step sequence"

ML \<open>
(* Copied from Isabelle/ML libraries *)

val opt_fact_binding =
  Scan.optional (Parse.binding -- Parse.opt_attribs || Parse.attribs >> pair Binding.empty)
    Binding.empty_atts;

val for_params =
  Scan.optional
    (\<^keyword>\<open>for\<close> |--
      Parse.!!! ((Scan.option Parse.dots >> is_some) --
        (Scan.repeat1 (Parse.maybe_position Parse.name_position))))
    (false, []);

val subgoal_parser =
  opt_fact_binding
  -- (Scan.option (\<^keyword>\<open>premises\<close> |-- Parse.!!! opt_fact_binding))
  -- for_params

val facts = Parse.and_list1 Parse.thms1

(* We first parse the token sequence into a sequence of proof steps.
   This includes commands like "apply [data]", "subgoal [data]", "done".
   We simply produce a sequence of these commands (represented in a custom datatype);
   we do not yet worry about capturing the nested structure. *)

(* The data associated with a subgoal command *)
type subgoal_data =
  ((binding * Token.src list) * (binding * Token.src list) option) * (bool * (string option * Position.T) list)

(* The data associated with an apply command *)
type apply_data = Method.text_range

(* The data associated with a by command *)
type by_data = Method.text_range * (Method.text_range option)

(* The data associated with an unfolding command *)
type unfolding_data = ((Facts.ref * Token.src list) list) list

(* The data associated with a using command *)
type using_data = ((Facts.ref * Token.src list) list) list

(* The data associated with a prefer command *)
type prefer_data = int

(* The data associated with a defer command *)
type defer_data = int

(* The data associated with a supply command *)
type supply_data = (Attrib.binding * (Facts.ref * Token.src list) list) list

(* Datatype representing the various kinds of proof steps we handle *)
datatype proof_step = 
  Apply_Step of apply_data
| By_Step of by_data
| Using_Step of using_data
| Using_Step_Dummy of using_data
| Unfolding_Step of unfolding_data
| Subgoal_Step of subgoal_data
| Prefer_Step of prefer_data
| Defer_Step of defer_data
| Supply_Step of supply_data
| Immediate_Proof_Step
| Default_Proof_Step
| Term_Isar_Step of apply_data option
| Back_Step
| Done_Step
| Sorry_Step

datatype unfolding_using_data =
  Unfolding of unfolding_data
| Using of using_data
| Using_Dummy of using_data

fun uu_data_of_strs ss = [ map (fn s => (Facts.Named ((s, Position.none), NONE), [])) ss ]

(* A proof consists of a list of proof steps. *)
type proof_steps = proof_step list

fun
  toks_to_str [] = ""
| toks_to_str toks =
    "[ " ^ (toks |> map (map (Token.unparse)) |> map (join " ") |> (join ", ")) ^ " ]"

fun
  fact_ref_to_str (Facts.Fact s) = "\<open>" ^ s ^ "\<close>"
| fact_ref_to_str r = Facts.string_of_ref r

fun
  refs_to_strs [] = []
| refs_to_strs ((r, []) :: xs) = fact_ref_to_str r :: refs_to_strs xs
| refs_to_strs ((r, ts) :: xs) =
  let
    val handle_toks = map (Token.unparse) #> join " "
    val s = 
    let
      val r_str = fact_ref_to_str r
    in if r_str = "" then
      "[[ " ^ (map handle_toks ts |> join ", ") ^ " ]]"
    else
      r_str ^ "[ " ^ (map handle_toks ts |> join ", ") ^ " ]"
    end
  in
    s :: refs_to_strs xs
  end

fun subgoal_cmd_parser ctxt = 
  Parse.command_name "subgoal"
  |-- subgoal_parser
  >> Subgoal_Step

fun using_keyword_parser ctxt = 
  Parse.command_name "using"
  |-- facts
  >> Using_Step

fun unfolding_cmd_parser ctxt = 
  Parse.command_name "unfolding"
  |-- facts
  >> Unfolding_Step

fun done_cmd_parser ctxt =
  Parse.command_name "done"
  |-- Scan.succeed Done_Step

fun apply_cmd_parser ctxt =
  Parse.command_name "apply"
  |-- Method.parse
  >> Apply_Step

fun by_cmd_parser ctxt =
  Parse.command_name "by"
  |-- Method.parse
  -- Scan.option Method.parse
  >> By_Step

fun prefer_cmd_parser ctxt =
  Parse.command_name "prefer"
  |-- Parse.nat
  >> Prefer_Step

fun defer_cmd_parser ctxt =
  Parse.command_name "defer"
  |-- Scan.optional Parse.nat 1
  >> Defer_Step

fun supply_cmd_parser ctxt =
  Parse.command_name "supply"
  |-- Parse_Spec.name_facts
  >> Supply_Step

fun immediate_proof_cmd_parser ctxt =
  Parse.command_name "."
  >> K Immediate_Proof_Step

fun default_proof_cmd_parser ctxt =
  Parse.command_name ".."
  >> K Default_Proof_Step

(* Parse a terminal Isar proof. Note that "terminal" means it terminates the current subgoal;
   there may be multiple "terminal" Isar proofs spread under different "subgoal" commands within
   a single apply script. *)
fun
  term_isar_parser' _ _ _ [] =
    (NONE : apply_data option, [ Token.eof ] : Token.T list)
| term_isar_parser' ctxt proofs qeds toks =
  if proofs = qeds andalso proofs <> 0 then let
    val (m, toks') = Scan.option Method.parse toks
  in
    (m, toks')
  end
  else let
    val (cmd, _) = Scan.option Parse.command toks (* Parses one token *)
    val proofs' = case cmd of SOME s => if s = "proof" then proofs + 1 else proofs | NONE => proofs
    val qeds' = case cmd of SOME s => if s = "qed" then qeds + 1 else qeds | NONE => qeds
    val (m, rest_toks) = term_isar_parser' ctxt proofs' qeds' (tl toks)
  in
    (m, rest_toks)
  end

(* Does not try to parse term tac *)
fun
  term_isar_parser0' _ _ [] =
    ([] : Token.T list, [Token.eof] : Token.T list)
| term_isar_parser0' proofs qeds toks =
  if proofs = qeds andalso proofs <> 0 then
    ([], toks)
  else let
    val (cmd, _) = Scan.option Parse.command toks (* Parses one token *)
    val proofs' = case cmd of SOME s => if s = "proof" then proofs + 1 else proofs | NONE => proofs
    val qeds' = case cmd of SOME s => if s = "qed" then qeds + 1 else qeds | NONE => qeds
    val (proof_toks, rest_toks) = term_isar_parser0' proofs' qeds' (tl toks)
  in
    (hd toks :: proof_toks, rest_toks)
  end

fun term_isar_parser ctxt =
  Parse.command_name "proof"
  |-- (term_isar_parser' ctxt 1 0)
  >> Term_Isar_Step

fun back_parser ctxt =
  Parse.command_name "back"
  >> K Back_Step

fun sorry_parser ctxt =
  Parse.command_name "sorry"
  >> K Sorry_Step

exception ParseError

(* Parse a sequence of tokens into proof_steps (a proof_step list).*)
fun script_toks_parser' ctxt =
  Scan.repeat (
    Scan.first [
      apply_cmd_parser ctxt |> toks_debug ctxt "apply init",
      by_cmd_parser ctxt |> toks_debug ctxt "by init",
      subgoal_cmd_parser ctxt |> toks_debug ctxt "subgoal init",
      unfolding_cmd_parser ctxt |> toks_debug ctxt "unfolding init",
      using_keyword_parser ctxt |> toks_debug ctxt "using init",
      done_cmd_parser ctxt |> toks_debug ctxt "done init",
      prefer_cmd_parser ctxt |> toks_debug ctxt "prefer init",
      defer_cmd_parser ctxt |> toks_debug ctxt "defer init",
      supply_cmd_parser ctxt |> toks_debug ctxt "supply init",
      immediate_proof_cmd_parser ctxt |> toks_debug ctxt "immediate proof init",
      default_proof_cmd_parser ctxt |> toks_debug ctxt "default proof init",
      term_isar_parser ctxt |> toks_debug ctxt "term isar init",
      back_parser ctxt |> toks_debug ctxt "back init",
      sorry_parser ctxt |> toks_debug ctxt "sorry init"
    ]
  )

(* Eats tokens until the first Isar proof in the token stream, then parses that Isar. *)
fun parse_first_isar ctxt =
  parse_while (fn tok => Token.unparse tok <> "proof")
  |-- Parse.command_name "proof"
  |-- term_isar_parser0' 1 0

(* Parses all Isar proofs in a token stream. *)
fun parse_all_isars ctxt = Scan.repeat (parse_first_isar ctxt)

\<close>

section "Parse proof step sequence to Isar string"

subsection "Setup"

ML \<open>

open Proof

(* The datatype we use to represent the nested structure of apply scripts and Isar scripts.
   Effectively, we use this to build ASTs. *)
datatype ('a, 'b) nested_list_item =
  Item of 'a
| Nested of ('b * (('a, 'b) nested_list_item list))

fun
  nested_list_map _ _ [] = []
| nested_list_map f g ((Item x)::xs) =
    (Item (f x))::(nested_list_map f g xs)
| nested_list_map f g ((Nested (x, xs))::xs') =
    (Nested ((g x), (nested_list_map f g xs)))::(nested_list_map f g xs')

fun
  nested_list_map' _ _ [] = []
| nested_list_map' f g ((Item x)::xs) =
    (Item (f x))::(nested_list_map' f g xs)
| nested_list_map' f g ((Nested (x, xs))::xs') =
    (Nested (x, g (nested_list_map' f g xs))) :: (nested_list_map' f g xs')

fun
  nested_list_map'' _ _ _ [] = []
| nested_list_map'' f g h ((Item x)::xs) =
    (Item (f x))::(nested_list_map'' f g h xs)
| nested_list_map'' f g h ((Nested (x, xs))::xs') =
    (Nested (g x, h x (nested_list_map'' f g h xs))) :: (nested_list_map'' f g h xs')

(* Instantiate our nested_list_item type with the necessary data to represent
   apply script ASTs and Isar ASTs. *)
type apply_node = (proof_step, subgoal_data) nested_list_item

type apply_script = apply_node list

datatype isar_unfolding_using_data =
  Isar_Unfolding of string list
| Isar_Using of string list

type isar_have_data = {
  haves : string list,
  have_labels : (int * int) option list
}

datatype trivial_proof = Immediate_Proof | Default_Proof | Sorry_Proof

datatype isar_proof_data =
  Tactic of {
    if_labels : (int * int) option list,

    extra : string list,
    
    uu_strs : isar_unfolding_using_data list,
    tac : string,

    is_subproof_dummy : bool,
    is_combined_show : bool
  }
| Trivial of {
  extra : string list,
  uu_strs : isar_unfolding_using_data list,
  proof : trivial_proof
}
| Term_Isar of {
  uu_strs : isar_unfolding_using_data list,
  extra : string list,
  toks : Token.T list,
  term_tac : string
}

type isar_subproof_data = {
  if_labels : (int * int) option list,
  uu_strs : isar_unfolding_using_data list,
  user_label : string option,
  prems_binding : (string * string list) option,
  fixed_vars : string list,
  options : apply2isar_options
}

type isar_note_data = (string option * string list) list

datatype isar_item =
  Have_Item of { have_data : isar_have_data, proof_data : isar_proof_data }
| Note_Item of isar_note_data
| Gap
| Comment of string

type isar_nested = {
  have_data : isar_have_data,
  subproof_data : isar_subproof_data
}

type isar_node = (isar_item, isar_nested) nested_list_item

type isar_script = isar_node list

fun seq_return x = x |> Seq.Result |> Seq.single

fun hd_st st_seq =
  hd (Seq.list_of st_seq)
  |> (
    fn
      (Seq.Result a) => a
    | _ => raise ERROR "Could not reconstruct proof. Are you sure the original proof succeeds?"
  )

\<close>

subsection "Process proof step sequence into proof step AST"

ML \<open>

(* Parse proof_steps to a proof step AST *)
fun
  proof_steps_parser [] = ([], [])
| proof_steps_parser (Subgoal_Step x :: steps) =
    let
      val (script, rest_of_steps) = proof_steps_parser steps
      val (script', rest_of_steps') = proof_steps_parser rest_of_steps
    in
      ((Nested (x, script)) :: script', rest_of_steps')
    end
| proof_steps_parser (By_Step x :: steps) =
    ([ Item (By_Step x) ], steps)
| proof_steps_parser (Default_Proof_Step :: steps) =
    ([ Item Default_Proof_Step ], steps)
| proof_steps_parser (Immediate_Proof_Step :: steps) =
    ([ Item Immediate_Proof_Step ], steps)
| proof_steps_parser (Done_Step :: steps) =
    ([ Item Done_Step ], steps)
| proof_steps_parser (Term_Isar_Step x :: steps) =
    ([ Item (Term_Isar_Step x) ], steps)
| proof_steps_parser (Sorry_Step :: steps) =
    ([ Item Sorry_Step ], steps)
| proof_steps_parser (step :: steps) =
    let
      val (script, rest_of_steps) = proof_steps_parser steps
    in
      ((Item step)::script, rest_of_steps)
    end

(* Combine our previous parsers to parse a token sequence into a proof script AST. *)
fun script_toks_parser ctxt = (
  script_toks_parser' ctxt
  >> proof_steps_parser
  >> fst
) : apply_script parser

\<close>

subsection "Process proof step AST into Isar tree"

text "This is where we run the apply script internally to reconstruct the proof states"

ML \<open>

open List

val get_prems = Proof.raw_goal #> #goal #> Thm.prems_of

fun
  index_of' _ [] _ = NONE
| index_of' y (x::xs) i = (if y = x then SOME i else index_of' y xs (i + 1))

val index_of = (fn x => fn xs => index_of' x xs 0)

val goal_of_state = Proof.raw_goal #> #goal

fun dest_nested_conjunctions tm =
let
  val tms = Logic.dest_conjunction_list tm
  val tms' =
    if length tms = 1 then
      tms
    else
      tms |> map dest_nested_conjunctions |> foldr1 (op @)
in
  tms'
end

fun prems_of_state st =
let
  val x = try (goal_of_state #> Thm.prems_of #> map dest_nested_conjunctions #> foldr (op @) []) st
in case x of
  NONE => []
| SOME xs => xs
end

exception Tac_Combinator_Print_Exception
fun
  show_tac' (Method.Source x) = map Token.print x
| show_tac' (Method.Combinator (_, Method.Then, xs)) =
    (xs |> (map show_tac') |> (add_delims ",") |> foldr (op @) [])
| show_tac' (Method.Combinator (_, Method.Then_All_New, xs)) =
    (xs |> (map show_tac') |> (add_delims ";") |> foldr (op @) [])
| show_tac' (Method.Combinator (_, Method.Orelse, xs)) =
    (xs |> (map show_tac') |> (add_delims "|") |> foldr (op @) [])
| show_tac' (Method.Combinator (_, Method.Try, xs)) =
    "(" :: (xs |> hd |> show_tac') @ [")?"]
| show_tac' (Method.Combinator (_, Method.Repeat1, xs)) =
    "(" :: (xs |> hd |> show_tac') @ [")+"]
| show_tac' (Method.Combinator (_, Method.Select_Goals i, xs)) =
    "(" :: (xs |> hd |> show_tac') @ [")[" ^ (string_of_int i) ^ "]"]
| show_tac' _ = raise Tac_Combinator_Print_Exception

val show_tac = fst #> show_tac' #> join " "

fun
  name_of_tac (Method.Source xs) = Token.print (hd xs)
| name_of_tac (Method.Combinator (_, _, xs)) = name_of_tac (hd xs)
| name_of_tac _ = raise Tac_Combinator_Print_Exception

val zip = map2 pair

val unzip = foldr (fn ((x, y), (xs, ys)) => (x :: xs, y :: ys)) ([], [])

type labels = (int * int) list

fun collapse_labels labels = map (pair (fst labels)) (snd labels)

fun tm_list_eq ts ts' =
  if length ts <> length ts' then
    false
  else if length ts = 0 then
    true
  else
    all (fn i => nth(ts,i) aconv nth(ts',i)) (0 upto length ts - 1)

fun make_fresh ctxt vs =
  map (fn x => (x, ())) vs
    |> Name.variant_names (Variable.names_of ctxt)
    |> map fst

fun
  yank_first' _ _ [] = NONE
| yank_first' acc P (x :: xs) = if P x then SOME (x, acc @ xs) else yank_first' (acc @ [ x ]) P xs

fun yank_first (P : 'a -> bool) (xs : 'a list) = yank_first' [] P xs

fun construct_goal smart schematic_data level (labels : labels) st st' =
let
  val st = case schematic_data of NONE => st | SOME x => fst x
  val prems = prems_of_state st
  val prems' = prems_of_state st'

  val no_change =
    length prems = length prems'
    andalso (all I (map (fn i => (nth (prems, i)) aconv (nth (prems', i))) (0 upto length prems - 1)))
  val smart = if no_change then false else smart (* Shadowing *)

  val all_new_labels = if length prems' = 0 then [] else (collapse_labels (level + 1, 1 upto length prems'))

  fun
    compute_changed_prems [] _ = []
  | compute_changed_prems ((x as (tm, _)) :: xs) (ys : term list) =
      case yank_first (curry (op aconv) tm) ys of
        NONE => x :: compute_changed_prems xs ys
      | SOME (_, ys') => compute_changed_prems xs ys'

  val (have_tms, have_labels, if_labels, labels') =
    if not smart then
      (prems, labels, all_new_labels, all_new_labels)
    else let
      val labeled_prems = zip prems labels
      val changed_prems = compute_changed_prems (rev labeled_prems) (rev prems') |> rev |> unzip

      fun
        pick_new_labels _ [] _ = []
      | pick_new_labels i (tm' :: xs) ys =
          case yank_first (fst #> curry (op aconv) tm') ys of
            NONE => (level + 1, i) :: pick_new_labels (i + 1) xs ys
          | (SOME ((_, lab), ys')) => lab :: pick_new_labels i xs ys'
      val labels' = pick_new_labels 1 prems' (rev labeled_prems)
      val labeled_prems' = zip prems' labels'
      val new_labeled_prems' = compute_changed_prems (rev labeled_prems') (rev prems) |> rev
    in
      if length (fst changed_prems) = 0 then
        (prems, labels, all_new_labels, all_new_labels)
      else let
        val (have_tms, have_labels) = changed_prems
        val if_labels = new_labeled_prems' |> map snd
        val labels' = pick_new_labels 1 prems' (rev labeled_prems)
      in
        (have_tms, have_labels, if_labels, labels')
      end
    end

  val level' =
    if not smart orelse length if_labels > 0 then
      level + 1 (* If we created any new prems, increase level *)
    else
      level

  val have_labels' = map SOME have_labels
  val if_labels' = map SOME if_labels
  val level' = if any is_schematic prems' then level else level' (* Shadowing *)
  val labels' = if any is_schematic prems' then labels else labels' (* Shadowing *)
in
  (have_tms, have_labels', if_labels', level', labels')
end

fun
  apply_uu (Using_Dummy _) = I
| apply_uu (Using data) = Proof.using_cmd data
| apply_uu (Unfolding data) = Proof.unfolding_cmd data

fun apply_uu_list uu_list (st : Proof.state) = foldl (uncurry apply_uu) st uu_list

val uu_data_to_strs = foldr (op @) [] #> refs_to_strs

val uu_data_to_isar =
  map (
    fn datum => case datum of
      Unfolding data => Isar_Unfolding (uu_data_to_strs data)
      | Using data => Isar_Using (uu_data_to_strs data)
      | Using_Dummy data => Isar_Using (uu_data_to_strs data)
  )

fun
  count_usings' acc [] = acc
| count_usings' acc ((Using _) :: xs) = count_usings' (acc + 1) xs
| count_usings' acc ((Using_Dummy _) :: xs) = count_usings' (acc + 1) xs
| count_usings' acc ((Unfolding _) :: xs) = count_usings' acc xs

val count_usings = count_usings' 0

fun
  count_unfolds' acc [] = acc
| count_unfolds' acc ((Unfolding _) :: xs) = count_unfolds' (acc + 1) xs
| count_unfolds' acc (_ :: xs) = count_unfolds' acc xs

val count_unfolds = count_unfolds' 0

fun
  butlast [] = []
| butlast xs = take (xs, length xs - 1)

fun
  schematic_data_to_strs NONE = []
| schematic_data_to_strs (SOME (_, extra)) = extra

fun construct_tactic m uu_data schematic_data level labels st st' =
let
  val ctxt = Proof.context_of st

  val uu_strs = uu_data_to_isar uu_data

  val tac = case m of SOME text => text |> show_tac | NONE => ""

  val _ = print_message ctxt "Applying tactic" tac

  val smart = ctxt |> options_from_ctxt |> #smart_goals
  val (have_tms, have_labels, if_labels, level', labels') =
    construct_goal smart schematic_data level labels st st'
  val haves = have_tms |> map (print_term ctxt)

  val have_data = { haves = haves, have_labels = have_labels } : isar_have_data
  val proof_data = Tactic {
      if_labels = if_labels,
      extra = schematic_data_to_strs schematic_data,
      uu_strs = uu_strs,
      tac = tac,
      is_subproof_dummy = false,
      is_combined_show = false
    }
in
  ({ have_data = have_data, proof_data = proof_data }, level', labels')
end

fun construct_unfolding uu_data schematic_data level labels st st' =
  construct_tactic NONE uu_data schematic_data level labels st st'

val filter_usings = filter (fn Using_Dummy _ => false | Using _ => false | Unfolding _ => true)

fun construct_unfolding_smart uu_data schematic_data level labels st =
let
  val smart_unfolds = st |> Proof.context_of |> options_from_ctxt |> #smart_unfolds
  val uu_cmd = if smart_unfolds then apply_uu_list uu_data else I
  val st' = st |> uu_cmd
  val construct_unfolding_opt =
    if smart_unfolds andalso count_unfolds uu_data > 0 then
      SOME (construct_unfolding (filter_usings uu_data) schematic_data level labels st st')  
    else
      NONE
  val (uu_item, level', labels') =
    case construct_unfolding_opt of
      SOME (uu_item, level', labels') => ([ Item (Have_Item uu_item) ], level', labels')
    | NONE => ([], level, labels)
in
  (uu_item, level', labels', st')
end

fun construct_by m uu_data schematic_data level labels st =
  construct_tactic m uu_data schematic_data level labels st (Proof.init (Proof.context_of st))

fun construct_trivial_proof triv uu_data schematic_data level labels st =
let
  val ctxt = Proof.context_of st
  val st' = Proof.init ctxt
  val uu_strs = uu_data_to_isar uu_data

  val _ =
    print_message
      ctxt
      "Trivial proof"
      (case triv of Immediate_Proof => "." | Default_Proof => ".." | Sorry_Proof => "");

  val (have_tms, have_labels, _, _, labels') = construct_goal false schematic_data level labels st st'
  val haves = have_tms |> map (print_term ctxt)
  val have_data = { haves = haves, have_labels = have_labels } : isar_have_data
  val proof_data = Trivial { extra = schematic_data_to_strs schematic_data, uu_strs = uu_strs, proof = triv }
in
  ({ have_data = have_data, proof_data = proof_data }, labels')
end

fun binding_to_str b =
let
  val b' = (Binding.name_of (fst b))
in
  if b' = "" then NONE else SOME b'
end

fun construct_supply (data : supply_data) =
let
  fun handle_label (b, refs) = (binding_to_str b, refs_to_strs refs)
  val note_data : isar_note_data = map handle_label data
in
  note_data
end

fun construct_term_isar uu_data schematic_data all_isars term_tac level labels st =
let
  val ctxt = Proof.context_of st
  val st' = Proof.init ctxt

  val uu_strs = uu_data_to_isar uu_data

  val _ = print_message ctxt "Terminal Isar" ""

  val (have_tms, have_labels, _, level', labels') = construct_goal false schematic_data level labels st st'
  val haves = have_tms |> map (print_term ctxt)
  val have_data = { haves = haves, have_labels = have_labels } : isar_have_data
  val proof_data = Term_Isar {
    uu_strs = uu_strs,
    extra = schematic_data_to_strs schematic_data,
    toks = hd all_isars,
    term_tac = case term_tac of NONE => "" | SOME m => show_tac m
  }
in
  ( { have_data = have_data, proof_data = proof_data }, level', labels')
end

val collect_fixed_vars =
  snd #> map fst #> foldr (fn (opt, xs) => case opt of (SOME x) => x :: xs | NONE => xs) []

val collect_fixed_vars_with_holes = snd #> map fst #> foldr ((op ::)) []

fun construct_subgoal
  (a : Attrib.binding)
  (b : Attrib.binding option)
  (c : bool * (string option * Position.T) list)
  uu_data level labels st st' st'' =
let
  val ctxt = Proof.context_of st
  val ctxt' = Proof.context_of st'

  val _ = print_message ctxt "Subgoal" ""

  val uu_strs = uu_data_to_isar uu_data

  val fixed_vars = collect_fixed_vars c
  val user_label = binding_to_str a
  
  val hyps =
    case b of
      NONE => []
    | SOME (b', _) =>
      (ctxt' |> Proof_Context.get_fact)
        (Facts.Named ((Binding.name_of b', Position.none), NONE))
      |> map (Thm.forall_intr_vars #> Thm.prop_of #> print_term ctxt')
  val prems_binding =
    case (b, hyps) of
      (NONE, _) => NONE
    | (SOME (b', _), _) => SOME (Binding.name_of b', hyps)

  val smart = ctxt |> options_from_ctxt |> #smart_goals
  val (haves, have_labels, if_labels, level', labels') = construct_goal smart NONE level labels st st''
  val have = hd haves |> print_term ctxt
  val extra_haves = tl haves |> map (print_term ctxt)
  val if_labels' =
    hd have_labels 
    :: (if length (prems_of_state st) = 1 then [] else if_labels)

  val options = options_from_ctxt ctxt
  val have_data = {
    haves = if smart then [ have ] else have :: extra_haves,
    have_labels = have_labels
  } : isar_have_data
  val subproof_data = {
    if_labels = if_labels',
    uu_strs = uu_strs,
    user_label = user_label,
    prems_binding = prems_binding,
    fixed_vars = fixed_vars,
    options = options
  } : isar_subproof_data
in
  ({ have_data = have_data, subproof_data = subproof_data }, level', labels')
end

exception Reconstruction_Exception

fun at_bottom st = Proof.level st <= 1

fun apply_terminal_cmd local_cmd global_cmd st =
  if at_bottom st then let
    val _ = global_cmd st  
  in
    Proof.init (Proof.context_of st)
  end
  else local_cmd st

(*

Reconstruct an Isar proof given an initial state and a proof script AST.
This is where we call the internal functions which construct a proof.

We keep track of "using" and "unfolding" commands, since we need to be careful with how these
steps interact with each other and with tactics.

We also take a list of all Isar scripts in the proof (represented as Token.T list list).
We do this so that we can maintain the user's newline information in each Terminal Isar proof.
To get this information, we must tokenize the apply script with Token.explode0—this function
maintains newline and spacing information, unlike the Parse.read_embedded function which we use
also use to tokenize the apply script. The need to tokenize the apply script twice—once with
newline and spacing information and once without—is why we pass in the list of terminal Isar
proofs here (so they can include the newline and spacing information).

*)

fun prefer xs i =
  nth (xs, i) :: (take (xs, i)) @ (drop (xs, i + 1))

fun defer xs i = (take (xs, i)) @ (drop (xs, i + 1)) @ [ nth (xs, i) ]

fun
  count_backs_ahead [] = (0, [])
| count_backs_ahead (Item Back_Step :: steps) =
  let
    val (backs', steps') = count_backs_ahead steps
  in
    (backs' + 1, steps')
  end
| count_backs_ahead steps = (0, steps)

fun repeat f i x = foldr (fn (_, x') => f x') x (1 upto i)

fun
  drop_until_using [] = []
| drop_until_using (xs as (Using _) :: _) = xs
| drop_until_using (xs as (Using_Dummy _) :: _) = xs
| drop_until_using ((Unfolding _) :: xs) = drop_until_using xs

fun
  merge_user_var_names [] [] = []
| merge_user_var_names (SOME u :: user_vn) [] = u :: merge_user_var_names user_vn [] (* Shouldn't happen *)
| merge_user_var_names (NONE :: user_vn) [] = "x" :: merge_user_var_names user_vn [] (* Shouldn't happen *)
| merge_user_var_names [] (b :: bound_vn) = b :: merge_user_var_names [] bound_vn
| merge_user_var_names (NONE :: user_vn) (b :: bound_vn) = b :: merge_user_var_names user_vn bound_vn
| merge_user_var_names (SOME u :: user_vn) (_ :: bound_vn) = u :: merge_user_var_names user_vn bound_vn

type reconstruction_acc = {
  apply_script : apply_script,
  uu_data : unfolding_using_data list,
  schematic_data : (Proof.state * string list) option,
  all_isars : Token.T list list,
  level : int,
  labels : labels,
  st : Proof.state,
  any_schematic : bool
}

type reconstruction_val = (isar_script * Token.T list list * Proof.state * bool)

fun
  isar_uu_data_to_str (Isar_Using ss) = "using " ^ (join " " ss)
| isar_uu_data_to_str (Isar_Unfolding ss) = "unfolding " ^ (join " " ss)

fun
  schematic_isar_item_to_str { proof_data = Tactic { uu_strs, tac, ... }, ... } =
    (if length uu_strs > 0 then "\n" else "")
    ^ (uu_strs |> map isar_uu_data_to_str |> join "\n") ^ "\n"
    ^ (if tac = "" then "." else "apply ( " ^ tac ^ " )")
| schematic_isar_item_to_str _ = ""

fun make_sorry_acc
  { all_isars, level, labels, st, any_schematic, ... } = {
  apply_script = [ Item Sorry_Step ],
  uu_data = [],
  schematic_data = NONE,
  all_isars = all_isars,
  level = level,
  labels = labels,
  st = st,
  any_schematic = any_schematic
} : reconstruction_acc

fun
  applies_to_isar' ({
    apply_script = [],
    all_isars,
    st,
    any_schematic,
    ...
  } : reconstruction_acc) =
    ([], all_isars, st, any_schematic) : reconstruction_val
| applies_to_isar' {
    apply_script = (Nested (((a, b), c), sub_xs) :: xs),
    uu_data,
    schematic_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  } =
    let
      (* If smart_unfolds is on, we need to create a "have" step at this point in the Isar
         to capture the effects of the current unfolds.
         If smart_unfolds is off, we will have already created the "have" step, so we don't need
         to worry about it.
         The construct_unfolding_smart function checks if smart_goals is on or off; if off, it
         does nothing.
      *)
      val (uu_item, level', labels', st') = construct_unfolding_smart uu_data schematic_data level labels st
      val sub_uu_data = drop_until_using uu_data

      (* Skolemizing meta quantified vars *)
      val ctxt = st |> Proof.context_of
      val fixed_vars =
      let
        val bound_var_names = st' |> prems_of_state |> hd |> strip_all_vars |> map fst
        val user_var_names =
        let
          val names = collect_fixed_vars_with_holes c
        in
          names @ (map (K NONE) (1 upto (length bound_var_names - length names)))
        end
        val ctxt' = st |> Subgoal.subgoal_cmd a b c |> snd |> Proof.context_of
        val bound_var_names' = make_fresh ctxt' bound_var_names
        val var_names = merge_user_var_names user_var_names bound_var_names'
      in if ctxt |> options_from_ctxt |> #subgoal_fix_fresh then
        make_fresh ctxt var_names
      else
        var_names
      end
          
      val c' = (fst c, map (fn v => (SOME v, Position.none)) fixed_vars)

      val subgoal_cmd = Subgoal.subgoal_cmd a b c'
      val st'' = st' |> subgoal_cmd |> snd

      val sub_acc = {
        apply_script = sub_xs,
        uu_data = sub_uu_data,
        schematic_data = NONE,
        all_isars = all_isars,
        level = 1,
        labels = [(1, 1)],
        st = st'',
        any_schematic = any_schematic
      }
      val (sub_isar, all_isars', st''', any_schematic') = applies_to_isar' sub_acc
      val (nested_item, level'', labels'') = construct_subgoal a b c' [] level' labels' st' st'' st'''

      val rest_acc = {
        apply_script = xs,
        uu_data = [],
        schematic_data = NONE,
        all_isars = all_isars',
        level = level'',
        labels = labels'',
        st = st''',
        any_schematic = any_schematic
      }
      val (rest, all_isars'', st'''', any_schematic'') = applies_to_isar' rest_acc
    in
      (uu_item @ ((Nested (nested_item, sub_isar)) :: rest), all_isars'', st'''', any_schematic' orelse any_schematic'')
    end
| applies_to_isar' (acc as {
    apply_script = (Item (Apply_Step m) :: xs),
    uu_data,
    schematic_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic
  }) =
    let
      val smart_unfolds = st |> Proof.context_of |> options_from_ctxt |> #smart_unfolds
      val uu_cmd = if smart_unfolds then apply_uu_list uu_data else I
      val st' = st |> uu_cmd

      val apply_cmd = Proof.apply m
      val back_cmd = Proof_Node.back
      val (backs, xs') = count_backs_ahead xs
      val st''_opt = Proof_Node.init st' |> try (Proof_Node.applys apply_cmd)

      val ret = case st''_opt of
        SOME st'' => let
          val st''' =
            st''
            |> repeat back_cmd backs
            |> Proof_Node.current
          val (have_item, level', labels') = construct_tactic (SOME m) uu_data schematic_data level labels st st'''

          val new_state_is_schematic = any is_schematic (prems_of_state st''')
          val back_strs =
            if new_state_is_schematic then
              map (fn _ => "back") (1 upto backs)
            else
              []
          val schematic_data' =
            case (schematic_data, new_state_is_schematic) of
              (NONE, true) => SOME (st, [ schematic_isar_item_to_str have_item ] @ back_strs)
            | (NONE, false) => NONE
            | (SOME (init_st, schem_isar), true) =>
                SOME (init_st, schem_isar @ [ schematic_isar_item_to_str have_item ] @ back_strs)
            | (SOME _, false) => NONE
          val rest_acc = {
            apply_script = xs',
            uu_data = [],
            schematic_data = schematic_data',
            all_isars = all_isars,
            level = level',
            labels = labels',
            st = st''',
            any_schematic = any_schematic orelse new_state_is_schematic
          }
          val ret =
            if new_state_is_schematic then
              applies_to_isar' rest_acc
            else let
              val (rest, all_isars', st''', any_schematic') = applies_to_isar' rest_acc
            in
              (Item (Have_Item have_item) :: rest, all_isars', st''', any_schematic')
            end
        in
          ret
        end
      | NONE => applies_to_isar' (make_sorry_acc acc)
    in
      ret
    end
| applies_to_isar' (acc as {
    apply_script = (Item (By_Step (m1, m2_opt)) :: _),
    uu_data,
    schematic_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  }) =
    let
      val smart_unfolds = st |> Proof.context_of |> options_from_ctxt |> #smart_unfolds
      val uu_cmd = if smart_unfolds then apply_uu_list uu_data else I
      val st' = st |> uu_cmd

      val by_cmd = Proof.local_terminal_proof (m1, m2_opt)
      val global_by_cmd = Proof.global_terminal_proof (m1, m2_opt)
      val st''_opt = st' |> try (apply_terminal_cmd by_cmd global_by_cmd)
      val ret =
        case st''_opt of
          SOME st'' => let
            val m =
              case m2_opt of
                NONE => m1
              | SOME m2 =>
                ( Method.Combinator (Method.no_combinator_info, Method.Then, [ fst m1, fst m2 ]),
                  Position.no_range)
            val (have_item, _, _) = construct_by (SOME m) uu_data schematic_data level labels st
          in
            ([ Item (Have_Item have_item) ], all_isars, st'', any_schematic)
          end
        | NONE => applies_to_isar' (make_sorry_acc acc)
    in
      ret
    end
| applies_to_isar' {
    apply_script = (Item (Unfolding_Step data) :: xs),
    uu_data,
    schematic_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  } =
    let
      val smart_unfolds = st |> Proof.context_of |> options_from_ctxt |> #smart_unfolds
      val unfolding_cmd = if smart_unfolds then I else Proof.unfolding_cmd data
      val st' = st |> unfolding_cmd

      val is_schematic = case schematic_data of NONE => false | SOME _ => true
      val (have_item, level', labels') =
        if smart_unfolds orelse is_schematic then
          ([], level, labels)
        else case construct_unfolding [ Unfolding data ] schematic_data level labels st st' of
          (x, y, z) => ([Item (Have_Item x)], y, z)
      
      (* We only need to re-apply this unfolding data later if there was a change it unfolded 
         a definition in a fact in the proof state. *)
      val uu_data' =
        if not smart_unfolds andalso not is_schematic andalso count_usings uu_data = 0 then
          uu_data
        else
          uu_data @ [ Unfolding data ]
      val rest_acc = {
        apply_script = xs,
        uu_data = uu_data',
        schematic_data = schematic_data,
        all_isars = all_isars,
        level = level',
        labels = labels',
        st = st',
        any_schematic = any_schematic
      }
      val (rest, all_isars', st'', any_schematic') = applies_to_isar' rest_acc
    in
      (have_item @ rest, all_isars', st'', any_schematic')
    end
| applies_to_isar' {
    apply_script = (Item (Using_Step data) :: xs),
    uu_data,
    schematic_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  } =
    let
      val smart_unfolds = st |> Proof.context_of |> options_from_ctxt |> #smart_unfolds
      val using_cmd = if smart_unfolds then I else Proof.using_cmd data
      val st' = st |> using_cmd

      val rest_acc = {
          apply_script = xs,
          uu_data = uu_data @ [ Using data ],
          schematic_data = schematic_data,
          all_isars = all_isars,
          level = level,
          labels = labels,
          st = st',
          any_schematic = any_schematic
        }
      val (rest, all_isars', st'', any_schematic') = applies_to_isar' rest_acc
    in
      (rest, all_isars', st'', any_schematic')
    end
| applies_to_isar' (acc as {
    apply_script = (Item Done_Step :: _),
    uu_data,
    all_isars,
    st,
    any_schematic,
    ...
  }) =
    let
      val smart_unfolds = st |> Proof.context_of |> options_from_ctxt |> #smart_unfolds
      val uu_cmd = if smart_unfolds then apply_uu_list uu_data else I
      val st' = st |> uu_cmd

      val done_cmd = Proof.local_done_proof
      val global_done_cmd = Proof.global_done_proof
      val st''_opt = st' |> try (apply_terminal_cmd done_cmd global_done_cmd)
      val ret =
        case st''_opt of
          SOME st'' => ([], all_isars, st'', any_schematic)
        | NONE => applies_to_isar' (make_sorry_acc acc)
    in
      ret
    end
| applies_to_isar' {
    apply_script = (Item (Term_Isar_Step term_tac) :: _),
    uu_data,
    schematic_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  } =
    let
      val smart_unfolds = st |> Proof.context_of |> options_from_ctxt |> #smart_unfolds
      val uu_data' = if smart_unfolds then uu_data else drop_until_using uu_data

      (* Arg "true" here avoids the need to enable quick_and_dirty mode *)
      val sorry_cmd = Proof.local_skip_proof true
      val global_sorry_cmd = Proof.global_skip_proof true
      val st' = st |> apply_terminal_cmd sorry_cmd global_sorry_cmd

      val (term_isar_item, _, _) =
        construct_term_isar uu_data' schematic_data all_isars term_tac level labels st
    in
      ([ Item (Have_Item term_isar_item) ], tl all_isars, st', any_schematic)
    end
| applies_to_isar' {
    apply_script = (Item (Prefer_Step i) :: xs),
    uu_data,
    schematic_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  } =
    let
      val prefer_cmd = Proof.prefer i
      val st' = st |> prefer_cmd
      val labels' =
        case (schematic_data, (try (prefer labels)) (i - 1)) of
          (NONE, NONE) => raise Reconstruction_Exception
        | (NONE, SOME x) => x
        | (SOME _, _) => labels

      val schematic_data' =
        case schematic_data of 
          NONE => NONE
        | SOME (init_st, extra) => SOME (init_st, extra @  [ "prefer " ^ (string_of_int i) ])
      val rest_acc = {
        apply_script = xs,
        uu_data = uu_data,
        schematic_data = schematic_data',
        all_isars = all_isars,
        level = level,
        labels = labels',
        any_schematic = any_schematic,
        st = st'
      }
      val (rest, all_isars', st'', any_schematic') = applies_to_isar' rest_acc
    in
      (rest, all_isars', st'', any_schematic')
    end
| applies_to_isar' {
    apply_script = (Item (Defer_Step i) :: xs),
    uu_data,
    schematic_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  } =
    let
      val defer_cmd = Proof.defer i
      val st' = st |> defer_cmd
      val labels' =
        case (schematic_data, (try (defer labels)) (i - 1)) of
          (NONE, NONE) => raise Reconstruction_Exception
        | (NONE, SOME x) => x
        | (SOME _, _) => labels

      val schematic_data' =
        case schematic_data of 
          NONE => NONE
        | SOME (init_st, extra) => SOME (init_st, extra @  [ "defer " ^ (string_of_int i) ])

      val rest_acc = {
        apply_script = xs,
        uu_data = uu_data,
        schematic_data = schematic_data',
        all_isars = all_isars,
        level = level,
        labels = labels',
        st = st',
        any_schematic = any_schematic
      }
      val (rest, all_isars', st'', any_schematic') = applies_to_isar' rest_acc
    in
      (rest, all_isars', st'', any_schematic')
    end
| applies_to_isar' {
    apply_script = (Item (Supply_Step data) :: xs),
    uu_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  } =
    let
      val supply_cmd = Proof.supply_cmd data
      val st' = st |> supply_cmd
      val note_item = construct_supply data

      val rest_acc = {
        apply_script = xs,
        uu_data = uu_data,
        schematic_data = NONE,
        all_isars = all_isars,
        level = level,
        labels = labels,
        st = st',
        any_schematic = any_schematic
      }
      val (rest, all_isars', st'', any_schematic') = applies_to_isar' rest_acc
    in
      (Item (Note_Item note_item) :: rest, all_isars', st'', any_schematic')
    end
| applies_to_isar' (acc as {
    apply_script = (Item Immediate_Proof_Step :: _),
    uu_data,
    schematic_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  }) =
    let
      val smart_unfolds = st |> Proof.context_of |> options_from_ctxt |> #smart_unfolds
      val uu_cmd = if smart_unfolds then apply_uu_list uu_data else I
      val st' = st |> uu_cmd
      val uu_data' = if smart_unfolds then uu_data else drop_until_using uu_data

      val immediate_cmd = Proof.local_immediate_proof
      val global_immediate_cmd = Proof.global_immediate_proof
      val st''_opt = st' |> try (apply_terminal_cmd immediate_cmd global_immediate_cmd)
      val ret =
        case st''_opt of
          SOME st'' => let
            val have_item =
              if length (prems_of_state st) > 0 then        
                [ Item (Have_Item (fst (construct_trivial_proof Immediate_Proof uu_data' schematic_data level labels st))) ]
              else
                []
          in
            (have_item, all_isars, st'', any_schematic)
          end
        | NONE => applies_to_isar' (make_sorry_acc acc)
    in
      ret
    end
| applies_to_isar' (acc as {
    apply_script = (Item Default_Proof_Step :: _),
    uu_data,
    schematic_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  }) =
    let
      val smart_unfolds = st |> Proof.context_of |> options_from_ctxt |> #smart_unfolds
      val uu_cmd = if smart_unfolds then apply_uu_list uu_data else I
      val st' = st |> uu_cmd
      val uu_data' = if smart_unfolds then uu_data else drop_until_using uu_data

      val default_cmd = Proof.local_default_proof
      val global_default_cmd = Proof.global_default_proof
      val st''_opt = st' |> try (apply_terminal_cmd default_cmd global_default_cmd)
      val ret =
        case st''_opt of
          SOME st'' => let
            val (have_item, _) = construct_trivial_proof Default_Proof uu_data' schematic_data level labels st
          in
            ([ Item (Have_Item have_item) ], all_isars, st'', any_schematic)
          end
        | NONE => applies_to_isar' (make_sorry_acc acc)
    in
      ret
    end
| applies_to_isar' {
    apply_script = (Item (Using_Step_Dummy data) :: xs),
    uu_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  } =
    let
      val rest_acc = {
        apply_script = xs,
        uu_data = uu_data @ [ Using_Dummy data ],
        schematic_data = NONE,
        all_isars = all_isars,
        level = level,
        labels = labels,
        st = st,
        any_schematic = any_schematic
      }
      val (rest, all_isars', st', any_schematic') = applies_to_isar' rest_acc
    in
      (rest, all_isars', st', any_schematic')
    end
| applies_to_isar' {
    apply_script = (Item Sorry_Step :: _),
    uu_data,
    schematic_data,
    all_isars,
    level,
    labels,
    st,
    any_schematic,
    ...
  } =
    let
      val smart_unfolds = st |> Proof.context_of |> options_from_ctxt |> #smart_unfolds
      val uu_cmd = if smart_unfolds then apply_uu_list uu_data else I
      val st' = st |> uu_cmd
      val uu_data' = if smart_unfolds then uu_data else drop_until_using uu_data

      val sorry_cmd = Proof.local_skip_proof true
      val global_sorry_cmd = Proof.global_skip_proof true
      val st'' = st' |> apply_terminal_cmd sorry_cmd global_sorry_cmd
      val (have_item, _) = construct_trivial_proof Sorry_Proof uu_data' schematic_data level labels st
    in
      ([ Item (Have_Item have_item) ], all_isars, st'', any_schematic)
    end
| applies_to_isar' _ = raise Reconstruction_Exception

fun mk_lab opts (level, i) = (#fact_name_prefix opts) ^ "_" ^ string_of_int level ^ "_" ^ string_of_int i

fun
  mk_lab_opt _ NONE = ""
| mk_lab_opt opts (SOME x) = mk_lab opts x

exception NoIsarException

fun applies_to_isar xs all_isars st =
let
  val ctxt = Proof.context_of st
  val all_haves = prems_of_state st
  val init_acc = {
      apply_script = xs,
      uu_data = [],
      schematic_data = NONE,
      all_isars = all_isars,
      level = 1,
      labels = (map (pair 1) (1 upto length all_haves)),
      st = st,
      any_schematic = false
    }
  val (isar, _, _, any_schematic) = applies_to_isar' init_acc

  (* find_last actually finds the first instance because everything is reversed (tactic script reasons backward, Isar forward) *)
  fun
    find_last [] = NONE
  | find_last ((x as Item (Have_Item _)) :: _) = SOME x
  | find_last ((x as Nested (_, _)) :: _) = SOME x
  | find_last (_ :: isar') = find_last isar'

  val last = find_last isar
  val last_haves =
    case last of
      NONE => raise NoIsarException
    | SOME (Item (Have_Item data)) => data |> #have_data |> #haves
    | SOME (Nested (data, _)) => data |> #have_data |> #haves
    | SOME _ => []

  val opts = options_from_ctxt ctxt
  val tac =
    if ctxt |> options_from_ctxt |> #named_facts then
      ((map (fn i => "fact " ^ (mk_lab opts (1, i))) (1 upto length all_haves)) |> join ", ")
    else
      "fact+"

  val last' =
    if length last_haves = length all_haves then
      []
    else
      singleton (Item (Have_Item {
        have_data = {
          haves = all_haves |> map (print_term ctxt),
          have_labels = []
        },
        proof_data = Tactic {
          if_labels = [],
          extra = [],
          uu_strs = [],
          tac = tac,
          is_subproof_dummy = false,
          is_combined_show = true
        }
      }))
in
(* last' actually goes at the beginning because everything gets reversed (tactic script reasons
   backward but we want Isar to reason forward). *)
  (last' @ isar, any_schematic)
end

\<close>

subsection "Process Isar tree into final string to be printed"

ML \<open>

fun
  isar_uu_strs_to_str [] = ""
| isar_uu_strs_to_str xs =
    xs
    |> map (
        fn uu => case uu of
          Isar_Unfolding xs => if xs = [] then "" else "\nunfolding " ^ (join " " xs)
        | Isar_Using xs => if xs = [] then "" else "\nusing " ^ (join " " xs)
      )
    |> implode

(* ISAR PROCESSING *)
(* We define a sequence of transformations which, when composed, process an Isar AST
   into the final string we will print. *)

fun
  mk_have opts level have (SOME lab) = mk_lab opts lab ^ ": " ^ quote_level opts level have
| mk_have opts level have NONE = quote_level opts level have

fun
  zip_haves_labs [] [] = []
| zip_haves_labs [] _ = []
| zip_haves_labs (have :: haves) [] = (have, NONE) :: (zip_haves_labs haves [])
| zip_haves_labs (have :: haves) (lab :: labs) = (have, lab) :: (zip_haves_labs haves labs)

fun
  process_isar_have_data' _ _ _ [] [] = "\n"
| process_isar_have_data' opts level _ (have::[]) [] = " " ^ mk_have opts level have NONE
| process_isar_have_data' opts level _ (have::[]) (lab::[]) = " " ^ mk_have opts level have lab
| process_isar_have_data' opts level delim haves labs = "\n" ^ (zip_haves_labs haves labs |> map (uncurry (mk_have opts level)) |> join delim)
                                                
fun process_isar_have_data opts level b { have_data = have_data, ... } =
( if b then "show" else "have") ^
( if #named_facts opts then
    process_isar_have_data' opts level "\nand " (#haves have_data) (#have_labels have_data)
  else
    process_isar_have_data' opts level "\nand " (#haves have_data) []
)

fun
  print_lab_for_fact _ NONE = ""
| print_lab_for_fact opts (SOME lab) = " " ^ mk_lab opts lab

fun mk_fact_tac options x =
let
  val tac = if #tac x = "" then "" else " ( " ^ (#tac x) ^ " )"
  val (spacer, fact_tac) =
    if #named_facts options then
      ( if #tac x = "" then "" else "\n"
      , "( " ^ (map (fn lab => "fact" ^ (print_lab_for_fact options lab)) (#if_labels x) |> join ", ") ^ " )")
    else
      (" ", "( fact+ )")
in
  "\nby" ^ tac ^ spacer ^ fact_tac
end

fun
  process_thms [] = ""
| process_thms [x] = x
| process_thms xs = join " " xs

fun
  process_label_with_thms (NONE, xs) = process_thms xs
| process_label_with_thms (SOME l, xs) = l ^ " = " ^ process_thms xs

fun
  process_labels_with_thms [] = ""
| process_labels_with_thms [x] = "note " ^ process_label_with_thms x
| process_labels_with_thms xs = "note\n" ^ ((map process_label_with_thms xs) |> join "\nand ")

fun process_tac opts x =
let
  val comment =
    if #is_subproof_dummy x then
      "(* SUBPROOF DUMMY *)"
    else if #is_combined_show x then
      "(* COMBINED SHOW *)"
    else if length (#if_labels x) = 0 then
      "(* LEAF *)"
    else
      ""
in
  if length (#if_labels x) = 0 then
    "\nby ( " ^ (#tac x) ^ " ) " ^ comment
  else
    mk_fact_tac opts x ^ " " ^ comment
end

fun
  process_triv { proof = Immediate_Proof, ... } = "\n. (* TRIVIAL LEAF *)"
| process_triv { proof = Default_Proof, ... } = "\n.. (* TRIVIAL LEAF *)"
| process_triv { proof = Sorry_Proof, ... } = "\nsorry"

fun
  process_isar_proof_data opts { proof_data = Tactic data, ... } =
    (data |> #extra |> implode)
    ^ (isar_uu_strs_to_str (#uu_strs data))
    ^ process_tac opts data
| process_isar_proof_data _ { proof_data = Trivial data, ... } =
    (data |> #extra |> implode)
    ^ (isar_uu_strs_to_str (#uu_strs data))
    ^ process_triv data
| process_isar_proof_data _ { proof_data = Term_Isar data, ... } =
    (data |> #extra |> implode)
    ^ "\n(* SWITCH TO ISAR *)"
    ^ (isar_uu_strs_to_str (#uu_strs data))
    ^ "\nproof" ^ ((#toks data) |> map Token.unparse |> implode)
    ^ (if #term_tac data = "" then "" else " ( " ^ #term_tac data ^ " )" )

fun process_isar_script_item opts level b (Have_Item data) =
  process_isar_have_data opts level b data
  ^ process_isar_proof_data opts data
| process_isar_script_item _ _ _ (Note_Item data) = process_labels_with_thms data
| process_isar_script_item _ _ _ Gap = ""
| process_isar_script_item _ _ _ (Comment s) = "(* " ^ s ^ " *)"

fun
  process_fixed_vars [] = ""
| process_fixed_vars fvs = "\nfix " ^ (fvs |> join " ") ^ ""

fun
  process_prems_binding _ _ (NONE : (string * string list) option) = ""
| process_prems_binding opts level (SOME (name, facts)) =
    "\nassume " ^ name ^ ": " ^ (process_isar_have_data' opts level "\n" facts [])

fun print_label opts have_data subproof_data =
  case #user_label subproof_data of
    NONE => 
      if #named_facts opts then
        " " ^ (mk_lab_opt opts (hd (#have_labels have_data))) ^ ": "
      else
        " "
  | SOME s => " " ^ s ^ ": "

val (subproof_is_labeled : isar_subproof_data -> bool) = (#user_label) #> (curry (op <>) NONE)

fun process_isar_subproof_data opts level (data : isar_subproof_data) = 
    (isar_uu_strs_to_str (#uu_strs data))
    ^ "\nproof-"
    ^ (process_fixed_vars (#fixed_vars data))
    ^ (process_prems_binding opts level (#prems_binding data))

fun
  process_isar_script_nested opts level b ({have_data : isar_have_data, subproof_data : isar_subproof_data}) =
    (if b then "show" else "have")
    ^ (print_label opts have_data subproof_data) ^ (quote_level opts level (hd (#haves have_data)))
    ^ process_isar_subproof_data opts (level + 1) subproof_data

fun
  process_isar_script' _ _ _ [] = []
| process_isar_script' opts level b (Item (x as (Have_Item _)) :: xs) =
    (Item (process_isar_script_item opts level b x)) :: (process_isar_script' opts level false xs)
| process_isar_script' opts level b (Item x :: xs) =
    (Item (process_isar_script_item opts level b x)) :: (process_isar_script' opts level b xs)
| process_isar_script' opts level b (Nested (x, ys) :: xs) =
    (Item "qed") (* "qed" comes first cause of reversing *)
    :: (Nested (process_isar_script_nested opts level b x, process_isar_script' opts (level + 1) true ys))
    :: (process_isar_script' opts level false xs)

val rev_isar = rev #> (nested_list_map' I rev)

val rev_str = rev #> (nested_list_map' I rev)

fun process_isar_script options = rev_isar #> process_isar_script' options 1 true #> rev_str

fun
  raise_subproofs' _ (subgoal_acc : isar_script) (isar_acc : isar_script) ([] : isar_script) =
  let
    val prepend = if length subgoal_acc > 0 then [ Item (Comment "MOVED SUBPROOFS AND NOTES") ] else []
    val separator =
      if length subgoal_acc > 0 andalso length isar_acc > 0 then
        [ Item (Comment "BEGIN MAIN BODY") ]
      else
        []
  in
    prepend @ subgoal_acc @ separator @ isar_acc
  end
| raise_subproofs' options subgoal_acc isar_acc ((x as Nested (data : isar_nested, _)) :: isar) =
  let
    val have_data = #have_data data
    val subproof_data = #subproof_data data
    val haves =
      if #smart_goals options then
        [ hd (#haves have_data) ]
      else
        data |> #have_data |> #haves
    val if_labels = tl (#if_labels subproof_data)
    val tac =
      case #user_label subproof_data of
        NONE =>
          "fact" ^ (if #named_facts options then " " ^ (mk_lab_opt options (hd (#if_labels subproof_data))) else "")
      | SOME l =>
          "fact" ^ (if #named_facts options then " " ^ l else "")
  
    (* Even if the Subproof Dummies option is disabled, we still use them if Smart Goals is disabled
       (since Smart Goals being disabled means we linear reasoning, which requires a subproof dummy),
       or if the subproof has a user label (this is because of the way we handle labels; during
       reconstruction, we cannot know if a step's premises will later be discharged by a labeled subgoal,
       but the subproof dummy copies the fact with a new label according to the expected format).*)
    val subproof_dummy_condition = 
      #dummy_subproofs options 
      orelse not (#smart_goals options) 
      orelse (#user_label subproof_data <> NONE andalso #named_facts options)
    val have_data' = { haves = haves, have_labels = #have_labels have_data } : isar_have_data
    val proof_data = Tactic {
      if_labels = if_labels,
      extra = [],
      uu_strs = [],
      tac = tac,
      is_combined_show = false,
      is_subproof_dummy = true
    }
    val have_item =
      if subproof_dummy_condition then
        [ Item (Have_Item { have_data = have_data', proof_data = proof_data }) ]
      else
        []
  in
    raise_subproofs' options (x :: subgoal_acc) isar_acc (have_item @ isar)
  end
| raise_subproofs' options subgoal_acc isar_acc ((x as (Item (Note_Item _))) :: isar) =
    raise_subproofs' options (x :: subgoal_acc) isar_acc isar
| raise_subproofs' options subgoal_acc isar_acc ((x as (Item _)) :: isar) =
    raise_subproofs' options subgoal_acc (isar_acc @ [x]) isar

fun raise_subproofs (options : apply2isar_options) =
  (raise_subproofs' options [] []) #> (nested_list_map' I (raise_subproofs' options [] []))
  : isar_script -> isar_script

type subproof_options = {
  extra_haves : bool
}

fun
  prepend s (Item x) = Item (s ^ x)
| prepend s (Nested (x, c)) = Nested (s ^ x, c)

(* Adds newlines between steps in proof, also adds "qed" to end of each subproof. *)
fun
  add_newlines [] = ""
| add_newlines ((Item x)::xs) = "\n" ^ x ^ (add_newlines xs)
| add_newlines ((Nested (x, xs))::xs') =
    "\n" ^ x
    ^ (add_newlines xs)
    ^ (add_newlines xs')

fun init_facts_label options = (#fact_name_prefix options) ^ "_init"

fun
  process_init_facts _ [] = ""
| process_init_facts options (fact::[]) =
    "\nassume " ^ init_facts_label options ^ ": " ^ (quote fact)
| process_init_facts options facts =
    "\nassume " ^ init_facts_label options ^ ":\n"
    ^ (map (fn fact => quote fact) facts |> join "\n")

(* Wraps final proof in "proof- [...] qed", and also processes initial facts if there are any. *)
fun wrap_final_proof options init_facts body =
  "proof-"
  ^ (process_init_facts options init_facts)
  ^ body
  ^ "\nqed"

fun isar_script_to_string init_facts options =
    rev_isar
    #> (raise_subproofs options)
    #> (process_isar_script options)
    #> add_newlines
    #> (wrap_final_proof options init_facts)

\<close>

section "Top-level command(s)"

ML \<open>

(* Given an apply script (represented as a string) and an initial state, we want to:
   (1) Parse the apply script string into an apply script AST,
   (2) Reconstruct the apply script AST to an Isar AST (by replaying the commands and tactics),
   (3) Process the Isar AST to the final string and print it as active markup.

   We simply call our previous functions to accomplish each step.
*)

fun apply2isar proof_str st =
  let
    val ctxt = Proof.context_of st
    val options = options_from_ctxt (Proof.context_of st)

    val keywords = Thy_Header.get_keywords' ctxt
    val apply_script = Parse.read_embedded ctxt keywords (script_toks_parser ctxt) (Input.string proof_str)

    val init_facts =
      st
      |> Proof.goal
      |> #facts
      |> map Thm.forall_intr_vars (* Makes schematic vars meta-quantified *)
      |> map (Thm.full_prop_of #> print_term ctxt)

    val using_dummy = Item (Using_Step_Dummy (uu_data_of_strs [ init_facts_label options ]))
    val apply_script' = if length init_facts > 0 then using_dummy :: apply_script else apply_script

    val script0_toks = (Token.explode0 keywords proof_str) @ [Token.eof]
    val all_isars = fst (parse_all_isars ctxt script0_toks)

    datatype result = Result of (isar_script * bool) | Print_Fail | Timeout
    val timeout = Config.get ctxt timeout_opt
    val res =
      Result (Timeout.apply (Time.fromSeconds timeout) (applies_to_isar apply_script' all_isars) st)
        handle
          No_Term_Eq_Original => Print_Fail
        | (Timeout.TIMEOUT _) => Timeout
    val isar_str =
      case res of
        Result (isar_script, any_schematic) => let
          val schematic_tag = if any_schematic then "(* @SCHEMATIC *)\n" else ""
        in      
          schematic_tag ^ isar_script_to_string init_facts options isar_script
        end
      | Print_Fail => "(* @FAIL_PRINT *)\nsorry"
      | Timeout => "(* @FAIL_TIMEOUT *)\nsorry"

    val _ = writeln (Active.sendback_markup_command isar_str)
  in
    Seq.make_results (Seq.single st)
  end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>apply2isar\<close> "Attempts to convert an apply script to an Isar script." (
    (toks_debug @{context} "all" Parse.cartouche)
    >> (fn m => (Toplevel.proofs (fn st => apply2isar m st))));

\<close>

end
