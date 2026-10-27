# Protocol for peer Lean projects — version 1

The preparation project coordinates mathematical contracts and assignment.
Projects numbered 1, 2, ... implement substantial packages in one shared
public Lean repository. The author mediates completion, blockers and changes
of assignment. Projects have equal status and do not direct one another.

## 1. Authority and assignment

`BOARD.json` in this directory is authoritative for project IDs, assignments,
package revisions, dependencies and acceptance. `BOARD.md` is its generated
view. Each package has one owner; each active project has at most one current
package. A package normally covers a connected piece of several pages of
mathematics. Module tasks and individual lemmas are internal milestones.

Only the preparation project changes allocations, accepts results or changes
the mathematical scope. Workers update their numbered report and their Lean
implementation on their own branch. They do not edit another project's
report or take an unassigned package. No routine approval is needed for
implementation choices, auxiliary lemmas or fixes within the assigned scope.

At the start of each active turn, read the current default-branch board,
protocol, package and relevant decisions, then compare them with the saved
checkpoint. Check again before a push or final submission if the shared base
may have moved. A project checks while it works; continuous background
monitoring is not part of this protocol. If its assignment is withdrawn,
paused or materially revised, checkpoint and notify the author.

## 2. Git and public interfaces

Use a project-specific branch, for example `project-1/B001`, from the
current accepted default branch. Record the base commit. No direct push to
the default branch, force push, shared-branch rewriting or modifications to
unrelated repositories. Open a PR containing the package and its report.
The author/preparation project handles acceptance and integration.

Use the shared `lean-toolchain`, Lake configuration and committed dependency
manifest. After bootstrap, changing these is a shared-interface change.
No independent toolchain upgrades or duplicated copies of shared definitions.
Namespaces and filenames proposed in a package are provisional until B001
has compiled and recorded the actual layout.

Implementations may freely add local helpers without changing the contract.
For a shared signature/representation change, record the proposed change,
affected callers, reason and migration in the report. If it is wholly inside
the assigned initial API, make the choice and document it. If it affects an
accepted API or another project, checkpoint the affected work and notify the
author; continue independent work inside the package where possible.

## 3. Proof status and mathematical fidelity

Read the actual source proofs and the module proof notes, not only the DAG.
Source labels identify mathematics, not already existing Lean declarations.
Preserve the exact quantified hypotheses. In particular keep RAW equality
separate from STRONG distinct-vertex products, and AP/SAP/CCO/NR2 separate.

A compiled signature is not a proved theorem. A theorem conditional on an
explicit provider is not an instantiated source theorem. State providers
as visible arguments/structures with precise laws, never as hidden global
axioms. A completed export must have no `sorry`/`admit` or `sorryAx` in its
transitive dependencies and no additional unproved axioms. Ordinary Lean
foundational axioms such as classical choice/propext are not mathematical
gaps. Record an actual axiom/dependency audit, not just a text search.

Draft work may be incomplete on a work branch, with its status clearly
marked. The accepted default branch and completed exports contain only
verified implementations. Future contracts may live as explicit interfaces
or documentation; never invent proofs merely to make a downstream build pass.

Keep encoding-only details in Lean/support notes. Send mathematical fixes,
counterexamples and useful simplifications back in the report, identifying
source labels and affected callers. Do not silently strengthen a theorem,
weaken a conclusion or rewrite the human article.

## 4. Checkpoints and exceptions

Keep one concise report at `reports/PROJECT_ID.md` on the work branch:
package/revision, base and work commits, completed exports, exact conditional
providers, checks and their outcome, remaining work and resume instructions.
Commit useful checkpoints so another chat in the same project can resume.
The first project also records shared representations and the actual
build/test/audit commands for later workers.

Continue autonomous formalization within the package. Notify the author when:

- the package is ready for acceptance;
- a mathematical gap, counterexample or unavailable prerequisite blocks it;
- a shared API/toolchain change or work outside the assignment is needed;
- assignment/permission problems prevent progress.

For a blocker, give the smallest precise obstruction, attempted approaches,
affected claim and a proposed next step. Save the branch/report and work on
independent parts if useful. Do not repeatedly retry the same failing job,
change the mathematical contract or start a different package. Tell the
author directly in the chat; no cross-project messaging or issue polling loop
is required.

## 5. Completion and acceptance

Submission includes a PR, source-to-Lean export map, exact hypotheses,
provider status, successful shared build, meaningful consumer checks and
dependency/axiom checks for the exported results. Record the checked commit
and CI run when available. A green job alone does not establish that the
statement expresses the intended mathematics.

The worker marks its report `SUBMITTED` and tells the author. The board
remains assigned until the preparation project reviews the report and updates
it. Acceptance requires integration and checks on the resulting default
branch; record that integration commit in the board. Projects may report
completion autonomously, but do not mark their own package accepted or choose
the next one. After acceptance the preparation project marks the project
`WAITING` until a new package is allocated. The author returns with the next
assignment or a repair request.
