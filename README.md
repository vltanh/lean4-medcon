# Median consensus clustering in Lean

A Lean 4 formalization of the mathematics of Md Taufique Hussain, Mahantesh Halappanavar, Samrat Chatterjee, Filippo
Radicchi, Santo Fortunato and Ariful Azad, *Parallel median consensus clustering in complex networks*,
[Scientific Reports 15, 3788 (2025)](https://doi.org/10.1038/s41598-025-87479-6). Given partitions `P₁, …, P_k` of the vertices
of a graph, the paper seeks a median partition, one that minimizes the total Mirkin distance to the inputs, by a greedy
algorithm that moves vertices along the edges of the graph. The paper is applied, with no numbered theorems. Its mathematics
is the derivation of the objective and of the gain of a move, and claims about the algorithm. The formalization is
unconditional, and it does not cover the paper's experiments.

## What is proved

- **Everything the paper derives:** Eqs. (2), (3) and (7); the derivation of the objective of Eq. (4) from Eq. (1); the exact
  gain `ΔD` of Eq. (5); and the worked example of Figs. 1 and 2, computed from the definitions.
- **What it claims without proof:** the Mirkin distance is a metric, and the Rand distance is its normalization; a negative
  `ΔD` reduces the distance; the greedy policy does not guarantee an optimum, and the order of the moves matters; an iteration
  has at most `2 m̂` potential moves, with the cost bound `O(m̂ n k_h / b)` as an explicit count.
- **What it needs but does not state:** moves made one at a time stop, in at most `k n (n - 1) / 2` moves.
- **The cited result it relies on:** the split-join distance is a metric (van Dongen 2000), in `External/`, by a direct count rather than van Dongen's argument.
- **Status:** no `sorry` outside `Challenge.lean`, and no `axiom`. `scripts/Audit.lean` checks that every declaration depends only
  on `propext`, `Classical.choice` and `Quot.sound`, and `scripts/route_check.py` checks the routes of the proofs against the paper's.

Not formalized: the experiments, NP-completeness, the variation of information, and the validation checks of the authors' code
(`REPORT.md`, Section 9).

## The main results

Each theorem of `Challenge.lean`, in the namespace `MedianConsensus.Challenge`:

| Theorem | In plain language |
| --- | --- |
| `equation2`, `equation3` | `δ_uv(P)` is `0` or `1` as `u, v` are together or not, and `δ_uv` counts the inputs that separate them |
| `equation7`, `mirkin_eq_card_symmDiff`, `mirkin_isMetric` | The Mirkin distance through `δ`, as a symmetric difference, and as a metric |
| `card_ordered_disagreements`, `sum_sq_parts_add_sum_sq_parts` | The paper's `d = b + c` is half of the Mirkin metric of the literature |
| `appendix_identity`, `equation4`, `equation1` | `∑_i d(C, P_i) = ∑_uv δ_uv + ∑_uv [k - 2 δ_uv] δ_uv(C)`; so the medians minimize the objective of Eq. (4); and they exist |
| `moveVertex_of_ne`, `moveVertex_self` | What a move to a cluster does |
| `equation5`, `moveVertex_reduces` | A move changes the objective by exactly `ΔD`, and a negative `ΔD` reduces the total distance |
| `equation6`, `not_canMove_iff` | The best move exists exactly when `v` has a neighbour; and the stopping condition |
| `greedyStep_wellFounded`, `exists_stable`, `greedy_run_length_le` | Moves made one at a time stop, in at most `k n (n - 1) / 2` moves |
| `greedy_not_optimal` | On the complete graph on four vertices, with three inputs, every stopping partition fails to be a median |
| `card_potentialMoves_le` | An iteration has at most `2 m̂` potential moves |
| `figure1`, `figure2` | The paper's worked example |

## Palomar

The project is packaged for [Palomar](https://palomar-registry.org): `Challenge.lean` states the results, `Solution.lean` proves them,
and `comparator.json` and `formalization.yaml` describe the pair. To check it, run `lake env lake comparator --config=comparator.json`,
which needs bubblewrap, and should print "Your solution is okay!". `.github/workflows/palomar_preflight.yml` runs Palomar's verification
on demand. Nothing has been submitted.

## Audit summary

The full audit is in `REPORT.md`. The objective of Eq. (4) and the gain of a move are correct, under the readings below.

- **Errors.**
  - Eq. (5) as printed sums over `u = v` as well, and is off by `k`. The paper's Fig. 2 has `-4` where the printed formula has `0` (E4).
  - "NP-complete for `k > 2`" goes beyond its citation, which says "Nothing is known for k ≥ 3". The case `k = 3` is proved in a paper that
    this one does not cite, and the sources read have no proof for any fixed `k ≥ 4` (E3).
  - Claims in running text that are false as written, and leave the method intact: a group of partitions need not have all its distances below `λ` (E6);
    `m̂` high and `b` low can occur together for same-size clusters, in a state that the algorithm reaches, at a cost of `n² k_h` (E8); the split-join distance is not a
    count of operations (E10). "Minimizing intra-cluster disagreements and maximizing inter-cluster disagreements" is undefined as written, and omits a term on the only
    definition on record (E2).
  - "Consequently" does not follow: the order can change the candidates with every run still optimal, and on the instance of `greedy_not_optimal` every run fails (E5). The Mirkin
    distance is counted in two ways, differing by a factor of `2` (E1).
- **Gaps.** The paper does not show that the algorithm stops, and the validation checks of its iteration are not specified. Without checks, the iteration can
  raise the objective and never stop (E7, `batch_counterexample`). Two steps of the appendix are left out (E11). The memory figures could not be
  reproduced (E9).
- **Missing hypotheses.** Only degenerate ones (`REPORT.md`, Section 4). **Redundant hypotheses.** None.
- **Use of cited results.** Two are stated wrongly (E3, E10), and one reference is mislabelled (E12).
- **Proofs.** The paper's few derivations are followed, with two departures, each repairing a step with a gap (E11): Eq. (7) applies the set identity to the separated pairs rather
  than the co-clustered pairs that the paper names, and Eq. (5) proves directly the change that the appendix asserts as its first line. The rest of what is proved here, the paper states
  without a derivation.

## Credits

- Written by Claude Opus 5.5, in Claude Code, at the request of The-Anh Vu-Le, following the
  [formalize-math-paper](https://github.com/vltanh/formalize-math-paper) procedure. No person has reviewed the proofs yet; Lean's kernel and NanoDa checked them, and independent agents
  checked the statements and the audit against the paper.
- Made on 2026-11-01, with five sub-agents. `CREDITS.md` has the details.

## Related work

From `REPORT.md`, Section 10.

- **History.** Median partition is NP-hard for unbounded `k`, and APX-hard for `k = 3` (Bonizzoni et al. 2008). Filkov and Skiena (2004) gave the factor-2 bound for the
  best input, and the one-element moves that this paper's greedy rule follows go back to them and to Goder and Filkov (2008).
- **Alongside and since.** No erratum was found. FastEnsemble (2024) addresses the same question by another method. The one substantial comparison is the CVC paper
  (Vu-Le et al., 2026, whose first author appears to be the requester of this formalization), which reports a more accurate pipeline.
- **Formalizations.** None of this paper, of median partition, or of the Mirkin metric was found. Three Lean projects touch correlation clustering, and were not
  consulted.

## What's next

No approximation guarantee is known for the greedy rule from the singletons. Whether a rule for the validation checks can guarantee descent while keeping the parallelism, how the
connectivity of clusters interacts with the median objective, and the complexity for fixed `k ≥ 4` are open. See `REPORT.md`, Section 11.

## Building

```sh
lake exe cache get
lake build
lake env lean scripts/Audit.lean                                                        # the axioms and the routes
python3 scripts/route_check.py check docs/paper_routes.tsv --accept docs/route_differences.tsv
python3 scripts/sync_challenge_defs.py --check                                          # the Challenge's copy of the definitions
python3 scripts/linkify_docs.py                                                         # update the documents' links, after a build
```

The toolchain is `leanprover/lean4:v4.36.0-rc2`, with Mathlib's tag `v4.36.0-rc2`. The block of shared definitions in `Challenge.lean` is generated from
`MedianConsensus/Defs.lean` by `scripts/sync_challenge_defs.py`. To keep it current, edit `Defs.lean` and rerun the script.

## Layout

Three libraries, in layers: `Basic`, general mathematics; `External`, the cited result; and `MedianConsensus`, the paper's.

| Module | Paper content |
| --- | --- |
| `MedianConsensus.Defs` | All the definitions that the Challenge uses: Eqs. (1)-(6) and the data of Figs. 1 and 2 |
| `MedianConsensus.Problem.CoClustering` | Eqs. (2) and (3), the Hamming description of Fig. 1 |
| `MedianConsensus.Problem.Mirkin` | Eq. (7), the metric, the two counts, the classical formula |
| `MedianConsensus.Problem.Objective` | The appendix's derivation, Eqs. (1) and (4), intra- and inter-cluster disagreements |
| `MedianConsensus.GraphAware.Move` | Moves, Eq. (5) |
| `MedianConsensus.GraphAware.BestMove` | Eq. (6), the stopping condition |
| `MedianConsensus.GraphAware.Figures` | Figs. 1 and 2 |
| `MedianConsensus.Algorithm.Greedy` | Termination, and the length of a run |
| `MedianConsensus.Algorithm.Examples` | The greedy policy does not guarantee an optimum; the order of the moves |
| `MedianConsensus.Algorithm.Parallel` | The iteration without validation checks |
| `MedianConsensus.Algorithm.Complexity` | The counts of moves and of operations |
| `MedianConsensus.Grouping` | Grouping homogeneous partitions |
| `MedianConsensus.Evaluation.Rand` | Fig. 10, the Rand distance |
| `External.VanDongen.SplitJoin` | The split-join distance is a metric (`External/VanDongen/README.md`) |
| `Basic.Data.Finset.SymmDiff` | The size of a symmetric difference |
| `Basic.Algebra.BigOperators.OrderedPairs` | Sums over pairs `x < y` |

## GitHub configuration

- `.github/workflows/lean_action_ci.yml` builds the project on every push, and runs the audit, the route check, and the checks of the shared definitions, the links and
  the tables. It needs no settings.
- `.github/workflows/palomar_preflight.yml` runs Palomar's verification, on demand. The repository must be public. Its `authorization_relationship` option is a claim about the
  person who runs it: check that it is accurate first.

## License

Apache-2.0: see `LICENSE`.
