# Apply2Isar: Automatically Convert Isabelle/HOL Apply-Style Proof Scripts to Structured Isar
In Isabelle/HOL, apply-style proof scripts are proofs that consist primarily of
`apply m` commands, where `m` is a method.
Each `apply` command performs backward chaining to manipulate the goal(s).
The proof concludes when all goals have been discharged, i.e.,
when a "solved" state is found.
Since the intermediate goals in apply-style scripts are not explicit and not fixed by the proof,
they can be brittle when theorems or methods change.
This can happen,
for instance, when the set of simplification lemmas changes,
or when theorems are refactored.
These changes could cause an `apply m` call to produce a different (unintended) proof state,
which may break the proof.
In the worst case,
the proof will break many lines after the modified `apply m` step,
making it very difficult to track down and fix the problem.

In contrast,
Isar provides structured proof commands,
which allow the user to explicitly state intermediate goals
and discharge them with short proofs.
This structure means that breakages due to refactoring
are isolated to particular intermediate goals,
and do not affect the rest of the proof.
Moreover,
the explicit nature of these structured proofs can make them easier to read,
since the intermediate goals are all immediately visible—in contrast,
to see the intermediate goals in an apply-style proof,
the user must interactively step through the proof line by line.

Thus,
we developed Apply2Isar,
a tool written in Isabelle/ML to automatically convert these apply-style proofs
to structured Isar.

# Authors
Apply2Isar is the result of work by Sage Binder ([@SageBinder](https://github.com/SageBinder)), Hanna Lachnitt ([@lachnitt](https://github.com/lachnitt)), and Katherine Kosaian ([@kcordwel](https://github.com/kcordwel)).

# Installation
For instructions on installing Isabelle, see https://isabelle.in.tum.de/.
We have tested Apply2Isar with Isabelle version 2025-2 (released in January 2026).
On Windows, you should use the Cygwin terminal provided by the Isabelle distribution.

To install Apply2Isar, navigate to `thys/Apply2Isar` and run `isabelle components -u .`.
Once this is done, you should be able to import Apply2Isar in any of your Isabelle developments with
`imports "Apply2Isar.Apply2Isar"`.

# Usage
Suppose you have an apply-style script like the following:
``` isabelle
lemma "[...]"
  using fact1
  apply m1
  unfolding X_def
  [...]
  done
```
To run Apply2Isar on this apply script,
wrap the proof in a pair of cartouches (`‹[...]›` or `\<open>[...]\<close>`)
preceded by `apply2isar` as follows:
``` isabelle
lemma "[...]"
  apply2isar‹
  using fact1
  apply m1
  unfolding X_def
  [...]
  done›
```
When the caret is placed in the `apply2isar‹[...]›` block,
you should see a clickable element in the output window containing the translated proof.
When clicked,
the translated proof will automatically be inserted into the proof document
(this is the same proof-insertion mechanism that you may be familiar with from Sledgehammer).
You should ensure that the caret is on the last line of the `apply2isar‹[...]›` block when you insert the translated proof.

# Options
Options can be set by writing `declare[[apply2isar_[OPTION] = ...]]`
in your development.
The following table lists all Apply2Isar options.
| Option | Type | Description | Default |
| ------ | ---- | ----------- | ------- |
| `tracing` | `bool` | If `true`, Apply2Isar prints basic tracing info in the output window. | `false` |
| `print_types` | `string` | Can be `"none"`, `"necessary"`, or `"all"`. If `"none"`, Apply2Isar prints no type annotations; if `"all"`, it prints all type annotations; if `"necessary"`, it prints type annotations when it detects they are necessary. (See paper for details.) | `"necessary"` |
| `smart_goals` | `bool` | If `true`, Apply2Isar will only print goals that change at each step. | `true` |
| `smart_unfolds` | `bool` | If `true`, Apply2Isar will try to avoid creating a separate `have` statement for `unfolding` steps. | `true` |
| `named_facts` | `bool` | If `true`, Apply2Isar names the fact(s) in each `have` statements and refers to them by name. | `true` |
| `dummy_subproofs` | `bool` | In the translation, Apply2Isar moves subproofs to the top of the structured Isar block containing it (see paper for details). If `dummy_subproofs = true`, Apply2Isar will create a "dummy subproof" in place of each moved subproof so the order of the original proof is still reflected in the translation. | `false` |
| `subgoal_fix_fresh` | `bool` | If `true`, Apply2Isar automatically renames skolemized variables when the user-chosen name shadows existing variables. This option can fix some translations but break others (see paper). | `false` |
| `linebreaks` | `bool` | If `true`, Apply2Isar keeps newlines in printed goals and attempts to indent them appropriately. | `false` |
| `fact_name_prefix` | `string` | Sets the prefix that Apply2Isar will use in facts it names. This may need to be changed to avoid shadowing existing lemma names. | `"h"` |
| `timeout` | `int` | The number of seconds Apply2Isar will run before timing out. | `30` |

# Examples
To see our examples,
navigate to `thys/Examples` and run the command `isabelle jedit -d . -R "Apply2Isar-Examples"`.
The `BasicExamples.thy` file contains basic examples that demonstrate most of the features of Apply2Isar.
The `AlgExamples.thy` file contains some examples of Apply2Isar on apply-style proofs taken from the Isabelle/HOL Algebra library (`HOL-Algebra.*` and `HOL.Modules`).

# Source Code
To see the source code,
navigate to `thys/Apply2Isar` and run the command `isabelle jedit -d . -R "Apply2Isar"`.
The `Prep2Isar.thy` file defines some auxiliary commands that were useful for our evaluation.

# Potential Failure Cases
We evaluated Apply2Isar on thousands of apply-style proofs from the Isabelle Archive of Formal Proofs
and found that it can completely or partially translate 95-99% of proofs.

Any proofs with schematic goals (goals with schematic term or type variables)
will be "partially" translated.
That is,
for any input proof containing schematic goals,
Apply2Isar will avoid translating the schematic portions of the proof,
instead just repeating the original apply-style script in the translation.
Often,
these portions are short,
so the resulting translation is still primarily a structured proof.

In our evaluation,
we observed that the rare failure cases were often caused by term-printing inconsistencies in Isabelle,
where goals are printed "correctly" (that is, exactly as they appear in the output window),
yet cannot be re-parsed (or are re-parsed to a diferent term).

See paper for more details.

# Paper
Our paper will be available on arXiv shortly.
