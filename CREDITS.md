# Credits

How this formalization was made, from the run log and the session transcripts.

## Who

- **Author and maintainer:** The-Anh Vu-Le, who asked for the formalization of this paper. The scope was left to the procedure.
- **Formalization:** Claude Opus 5.5 (`claude-opus-5-5`), in Claude Code 2.1.314, through the VS Code extension. One session. There was no earlier draft.
- **Procedure:** the skill [formalize-math-paper](https://github.com/vltanh/formalize-math-paper), version 3.0.0.
- **Review:** no person has reviewed the proofs. Lean's kernel and NanoDa checked them, through Comparator. Independent agents compared the statements with the paper, and checked the audit against
  the paper and its sources.

## First formalization (2026-11-01)

How it was made:

- **Reading.** The main session read the published PDF and the arXiv v1 TeX, read the figures from page images, and tested the paper's claims numerically before writing any Lean.
- **Statements.** The main session wrote every definition and statement, with `sorry`, and the Challenge. A first sub-agent, working from the paper and the figures, reviewed them against the paper. It found no false statement, and
  it found one trivially true statement, one counterexample that ignored the paper's context, and several docstrings that overstated. These were fixed before the baseline commit.
- **Proofs.** The main session wrote all the proofs. The work was small enough not to need parallel provers.
- **Literature.** A second sub-agent searched for the work before, alongside and after the paper, and for other formalizations.
- **Audit.** The main session wrote [`REPORT.md`](REPORT.md). A third sub-agent checked every finding against the published text, recomputed the numbers, compared the formal proofs with the paper's derivations, and checked the sources of the literature section. It found
  19 problems, including an overstatement in E3 and a misreading in E8, and two steps of the appendix that needed recording as departures. All were addressed, and two Lean theorems were strengthened as a result.
- **Integration and checks.** The main session ran the build, the axiom audit, the route check, Comparator and Palomar's local checks.

A fourth sub-agent refereed the private plans for follow-up papers. It is counted in the figures below, as is the main session's work on those plans. That referee also compiled and ran the authors' public code in a scratch directory, which
was not asked of it. No result in this repository depends on that run.

Figures, from 2026-11-01 09:44:54 to 12:05:48 (UTC-6), the commit that completes [`REPORT.md`](REPORT.md):

- elapsed time: 2.35 hours;
- sub-agents: 4, with at most 2 running at once, and 2.4 hours of total working time;
- sub-agents: 368 tool calls; tokens: 0.64M output, 2.16M input, 32M cache reads;
- main session: 115 tool calls; tokens: 0.47M output, 0.73M input, 38M cache reads;
- model calls: `claude-opus-5-5`, 88 in the main session and 137 by the sub-agents.

These figures come from `session_stats.py`, in the skill. They do not include the packaging done after that commit, or the time spent by the toolchain on builds beyond what the session waited for.
