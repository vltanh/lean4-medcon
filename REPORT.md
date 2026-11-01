# Audit of the paper and the formalization

Paper: Md Taufique Hussain, Mahantesh Halappanavar, Samrat Chatterjee, Filippo Radicchi, Santo Fortunato
and Ariful Azad, *Parallel median consensus clustering in complex networks*, Scientific Reports 15, 3788
(2025), [doi:10.1038/s41598-025-87479-6](https://doi.org/10.1038/s41598-025-87479-6). The audit was made
against the published PDF, the version of record, and uses the LaTeX source of
[arXiv:2408.11331v1](https://arxiv.org/abs/2408.11331) for exact formulas and labels. The arXiv version is
older than the published one, and the differences are noted where they matter. Page numbers are those of
the published PDF. The paper numbers its equations and figures, but neither its sections nor any results.

The paper is an applied one, with no theorems. Its mathematics is in Eqs. (1)-(7), the derivations in its
appendix, the worked example of Figs. 1 and 2, and claims in running text. Most of the paper is
experimental, and is not formalized (Section 9).

Status of the formalization:

- Everything in the paper that can be stated mathematically and that concerns its objective and its
  algorithm is stated and proved, except what Section 9 lists. Where a claim is false as written, the
  formalization proves a counterexample and the correct version (Section 3).
- The derivations of Eq. (4) from Eq. (1) and of Eq. (5) follow the paper's appendix, with two small repairs
  (Section 7). The paper cites no theorem in a proof, though its appendix follows a derivation of Filkov and
  Skiena without saying so (Section 2). The one cited fact that the formalization relies on, that the
  split-join distance is a metric, is proved in [`External/`](External).
- Nothing is assumed. The formalization is unconditional.
- `lake build` succeeds with no `sorry` outside [`Challenge.lean`](Challenge.lean), and no `axiom`. [`scripts/Audit.lean`](scripts/Audit.lean) checks
  that every declaration of the library depends only on [`propext`](https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#propext), [`Classical.choice`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Classical.choice) and [`Quot.sound`](https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot.sound).
- [`Challenge.lean`](Challenge.lean) states the main results, [`Solution.lean`](Solution.lean) proves them from the library, and Comparator
  accepts the solution under Lean's kernel and NanoDa.
- Three formulas are read with a correction, all recorded below: the summand of Eq. (3), the range of the
  sum in Eq. (5), and the `≈` in the appendix. No other statement of the paper was changed. Claims that
  are false as written are not changed either: the library proves what fails, and what holds instead.
- Every derivation that the paper gives is followed, and two of its steps are repaired, as departures
  (Section 7). The formalization also proves many claims that the paper makes with no proof; those proofs
  are its own.

## 1. Summary

- **Errors.** Eq. (5) as printed is off by `k`, and the paper's own Fig. 2 contradicts it (E4). The
  statement of NP-completeness for `k > 2` goes beyond its citation, which says that this is not known (E3).
  Three claims in running text are false as written, and leave the method intact: the distances inside a group
  of partitions (E6), the claim that `m̂` high and `b` low cannot occur together (E8), and the description of the
  split-join distance (E10). A fourth is undefined as written, and false on the only definition on record (E2).
  "Consequently" in the claim about optimality does not follow (E5). The Mirkin distance is counted in two
  ways, differing by a factor of `2` (E1).
- **Gaps.** The paper does not show that its algorithm stops, and the validation checks that its iteration
  needs are not specified; without checks it can fail to stop (E7). Two steps of the appendix are left out
  (E11). The memory figures could not be reproduced from the stated assumptions, and "linear speedup" does not
  fit the reported figures (E9).
- **Missing hypotheses.** Only degenerate ones: Section 4.
- **Redundant hypotheses.** None: Section 5.
- **Use of cited results.** Two are stated wrongly (E3, E10). One reference is mislabelled (E12).
- **No error affects the objective of Eq. (4) or the exact gain of a move.** Both are correct, under the
  readings of Section 6.

## 2. Results from prior work and how the paper uses them

### Proved in `External/`

| Result | Where the paper uses it | Source | Theorem in `External/` |
| --- | --- | --- | --- |
| The split-join distance is a metric | "Grouping homogeneous partitions"; "Evaluation metrics": "All three of these measures are true distance metrics" | van Dongen, [CWI report INS-R0012](https://ir.cwi.nl/pub/4461/04461D.pdf) (2000), Definition 12 and Theorem 4 | [`External.VanDongen.splitJoin_isMetric`](External/VanDongen/SplitJoin.lean#L149), by a direct count ([`External.VanDongen.projection_add_projection_le`](External/VanDongen/SplitJoin.lean#L51)) and not by van Dongen's shortest-path argument |

### Assumed

None.

### Standard facts used without citation

| Fact | Where | In the formalization |
| --- | --- | --- |
| `\|A △ B\| = \|A\| + \|B\| - 2 \|A ∩ B\|` | Appendix, for Eq. (7) | [`Finset.card_symmDiff_add_two_mul_card_inter`](Basic/Data/Finset/SymmDiff.lean#L22) |
| The symmetric difference distance satisfies the triangle inequality | Appendix: "This distance is a metric" | [`Finset.card_symmDiff_triangle`](Basic/Data/Finset/SymmDiff.lean#L32) |
| There are `n (n - 1) / 2` pairs | Complexity, "`k(k-1)/2` pairs" | [`card_pairs`](MedianConsensus/Algorithm/Complexity.lean#L25) |

### Does the paper use each cited result correctly?

| Cited result | Where | Verdict |
| --- | --- | --- |
| Filkov and Skiena (ref. 10): NP-completeness | p. 3: "NP-complete problem for `k > 2`" | Goes beyond the source: E3 |
| Filkov and Skiena (ref. 10): the derivation | Appendix, pp. 12-13 | Not cited there, though the appendix follows it: their Eqs. (7)-(10) are the chain to Eq. (4), with their `r` in place of `δ`, and their Lemma 3 and Corollary 1 are the gain of a move, with `j ≠ x` printed in the sum (E4, E11). The paper says only that its `δ` is a distance where theirs is a similarity |
| Wakabayashi; Křivánek and Morávek (refs. 22, 23): NP-hardness | p. 2: exact optimization "is NP-Hard" | Correct for an unbounded number of input partitions, as later sources attribute it. These two were not read here. Ref. 22 is mislabelled: E12 |
| Mirkin (ref. 21): the distance | pp. 2-3, appendix | Correct, up to the factor of `2`: E1 |
| van Dongen (ref. 30): split-join | pp. 5, 8 | The metric property is correct, and proved here; the description is not: E10 |
| Rand (ref. 52): Rand distance | p. 8 | Correct: [`randDistance_eq_mirkin_div`](MedianConsensus/Evaluation/Rand.lean#L57), [`randDistance_isMetric`](MedianConsensus/Evaluation/Rand.lean#L71). Rand (1971) itself was not read; Meilă (2007, Eq. (9)) gives this normalization |
| Meilă (ref. 51): variation of information is a metric | p. 8 | Correct per Meilă (2007, Property 1), and not formalized here |

The other citations give context and are used in no argument: the survey of consensus methods, the
community-detection algorithms used to generate inputs, Meilă's impossibility result (ref. 11), the elbow
method, and igraph's running time for split-join (ref. 34).

## 3. Errors and gaps in the paper

**E1. Methods, p. 3, and appendix, p. 13: two counts of the Mirkin distance.** The Methods say that the
distance "counts (twice) the number of vertex pairs `(u, v)` that are grouped together in one partition but
separated into different clusters in the other". The appendix says that it "is defined as the number of
pairs of elements that are clustered together in one partition but not in the other", and sets
`d(P₁, P₂) = b + c`. With "pairs" meaning the same in both, these differ by a factor of `2`. Eq. (7) and
Fig. 10 leave open what `∑_uv` ranges over. The unordered count is the one that the paper's numbers use: Fig. 2
says that the move "reduces the total distance by 4", with `ΔD = -4`, and this holds only for unordered pairs
(`figure2`), and Filkov and Skiena's Eq. (7), which the appendix follows, sums over `1 ≤ i < j ≤ n`. The factor
changes no minimizer. The formalization
takes `d = b + c`, proves that ordered pairs give `2 d` (`card_ordered_disagreements`), and identifies `2 d`
with the classical Mirkin metric (`sum_sq_parts_add_sum_sq_parts`; Meilă 2007, Eqs. (8)-(9) in the author's
revised manuscript, whose numbering may differ from the journal's).

**E2. Methods, p. 3: "minimizing intra-cluster disagreements and maximizing inter-cluster disagreements".**
The paper says that "minimizing equation (1) is equivalent to" this, without defining the two quantities;
its sentence "We call it the inter-cluster disagreements" has no clear antecedent. So the claim is undefined as
written. On the one definition on record, in a passage commented out in the arXiv source, they are the sums of
`δ_uv` over the pairs inside and between the clusters of `C`. Then the claim omits a term:
`∑_i d(C, P_i)` equals `intra - inter + k · #(separated pairs)` ([`totalDistance_eq_intra_sub_inter`](MedianConsensus/Problem/Objective.lean#L99)). Without the
term, the singleton partition minimizes the first quantity and maximizes the second for all inputs
([`bot_minimizes_intra_maximizes_inter`](MedianConsensus/Problem/Objective.lean#L121)), and it is not a median partition in general
([`exists_bot_not_isMedian`](MedianConsensus/Problem/Objective.lean#L141)). The arXiv source shows an earlier objective of exactly this form, commented out and
replaced. A kinder reading is possible: if "disagreement" means the signed quantity `2 δ_uv - k`, the factor
printed in Eq. (5), the sentence is exactly true, since the total is then a constant minus the second quantity, and
the two sum to a constant. Either way this concerns only the phrase. Eq. (4) is correct, and it contains the term.

**E3. Naive optimization, p. 3: "NP-complete problem for `k > 2`".** The paper says: "Solving Eq. (4) exactly
poses an NP-complete problem for `k > 2` due to the exponential number of potential consensus partitions",
citing Filkov and Skiena. The cited source says that this is not known: "CC is NP-complete in general, yet it is not
known whether it is NP-complete for any particular k. … The case of k = 2 is also simple … Nothing is known for
k ≥ 3" ([authors' preprint](https://www.cs.ucdavis.edu/~filkov/software/conpas/HeterCons.pdf)). The case `k = 3` was
settled later, in a paper that this one does not cite: "Minimum Consensus Clustering is APX-hard even for three input
partitions" (Bonizzoni, Della Vedova, Dondi and Jiang, [JCSS 74 (2008)](https://doi.org/10.1016/j.jcss.2007.06.024)).
That paper's introduction speaks of any constant `k > 2`, but its proof treats `k = 3`, and the sources read in
Section 10 contain no proof for any fixed `k ≥ 4`. So the claim may well be true, and it is unsupported as cited. Also, the
size of a search space is not a hardness argument, and an optimization problem is not itself NP-complete. The easy
cases are proved here: every input is a median for `k = 1, 2` ([`isMedian_of_one`](MedianConsensus/Problem/Objective.lean#L65), [`isMedian_of_two`](MedianConsensus/Problem/Objective.lean#L72)). The method is
unaffected, since the claim only motivates a heuristic. The formalization does not state hardness (Section 9).

**E4. Graph-aware consensus clustering, Eq. (5), p. 4, and appendix, p. 13: the sum includes `u = v`.** Eq. (5)
sums over `u`, and `σ_v(c) = 1` for the current cluster `c` of `v`. Read literally, the term `u = v` adds
`k - 2 δ_vv = k`, so the printed sum is `ΔD + k` when `v ∈ c` and `v ∉ c'` ([`sum_all_eq_deltaD_add`](MedianConsensus/GraphAware/Move.lean#L147)). This is not
the change in the objective, and it changes decisions: for the move of Fig. 2, the literal sum is `0`, where the
figure has `-4` ([`figure2_literal`](MedianConsensus/GraphAware/Figures.lean#L59)), and the move would not be made. Fig. 2 leaves `v₃` out of its sum over `c₁`,
the authors' code skips `u = v`, and Filkov and Skiena's Eq. (12), the source of this formula, prints `j ≠ x` in the
sum, as does an earlier formula in the arXiv source (commented out). So only one reading can be intended. The formalization sums over `u ≠ v`, and then `ΔD` is exactly the change in the
objective (`equation5`) and in the total distance ([`totalDistance_moveVertex`](MedianConsensus/GraphAware/Move.lean#L201)). The appendix's first line, with
its sum over `u ∈ c`, has the same slip.

**E5. Graph-aware consensus clustering, p. 4: "Consequently".** The paper says that the order of the moves
influences the set of potential moves, and "Consequently, this greedy moving policy, like any greedy
algorithm, does not guarantee an optimal solution". The premise and the conclusion are both true, but the second
does not follow from the first. On the instance of [`order_influences_candidates`](MedianConsensus/Algorithm/Examples.lean#L83), the order changes the candidates,
and yet every run stops at a median. On the instance of `greedy_not_optimal`, *every* run stops at a partition that is
not a median, so the failure does not come from the order. The order can matter ([`greedy_order_dependent`](MedianConsensus/Algorithm/Examples.lean#L151), with unique
best moves throughout). "Like any greedy algorithm" is also too broad: Kruskal's algorithm is greedy and optimal. And
p. 6 evaluates all the moves of an iteration "at the beginning of the iteration", where the order plays no role within
an iteration.

**E6. Grouping homogeneous partitions, p. 5: distances in a group.** The paper removes the edges "whose weights
are greater than a threshold `λ`", and says that this "creates multiple connected components where each
component is composed of relatively homogeneous partitions with inter-partition distances less than `λ`". This
is false for two partitions of a component, by chaining. Three partitions with split-join distances `1, 1, 2`
lie in one component at `λ = 1` ([`group_distances_counterexample_splitJoin`](MedianConsensus/Grouping.lean#L81)), and the same happens for the
Mirkin distance ([`group_distances_counterexample_mirkin`](MedianConsensus/Grouping.lean#L97)). An edge of weight exactly `λ` is kept too, so even
consecutive partitions have distance at most `λ`, not less. What holds is that two partitions of a component of
`m` partitions have distance at most `(m - 1) λ` ([`dist_le_of_reachable`](MedianConsensus/Grouping.lean#L39), [`splitJoin_le_of_reachable`](MedianConsensus/Grouping.lean#L71)). The
paper's hedge "relatively homogeneous" softens this, and the method is unaffected.

**E7. The algorithm and Parallel algorithm, pp. 5-6: the stopping condition and the unspecified checks.** The
paper says that "The algorithm stops when no vertex can be moved", with no argument that this happens. For moves
made one at a time, it does: each move decreases the total distance, a natural number, so every run stops
(`greedyStep_wellFounded`, `exists_stable`), in at most `k n (n - 1) / 2` moves (`greedy_run_length_le`). The
paper's iteration differs: it "identifies the best possible move for every vertex considering the consensus
partition at the beginning of the iteration. After some validation checks of the identified moves, all moves are
performed together". (A comment in the arXiv source says that all the experiments use this version.) The checks
are not specified, and they matter. Without them, the iteration can raise the objective and then never reach its
stopping condition: on three vertices and three inputs, the singletons lead to a partition with a larger
objective, which then leads back to itself, while vertices can still move ([`batch_counterexample`](MedianConsensus/Algorithm/Parallel.lean#L45)). The authors'
code has two checks. One invalidates one of two vertices attracted to each other. The other applies only when the same
set of vertices moves as in the previous iteration: it compares the summed predicted `ΔD`, and ends the loop when this has
not decreased. There is also an iteration limit, so the code always stops, but that need not be the paper's stopping
condition. The formalization does not model these. The paper's statements that the two versions reach the same quality are
empirical, and are not contradicted here.

**E8. Computation and memory complexity, p. 6: "both of those conditions cannot occur simultaneously".** The paper
raises a worry and dismisses it: "One can argue that this complexity can be as high as `O(n²)` if `m̂` is very high and `b`
is very low. For the simple case of same-size clusters, it is easy to see that both of those conditions cannot occur
simultaneously." Its reasons are that `m̂` and `b` are both high at the start, from singletons, and both decrease later. The
two conditions can occur together in a state that the algorithm reaches: on the complete graph on `n = 2 s` vertices, with
the two halves as the one input, a run from the singletons reaches the two halves, with `b = 2` and `m̂ = n² / 4`
([`both_conditions_occur`](MedianConsensus/Algorithm/Complexity.lean#L444)). There the cost of an iteration is exactly `n² k_h` ([`iterationCost_halves`](MedianConsensus/Algorithm/Complexity.lean#L429)), so the worry is
realized, and the reassurance fails in its reason and its conclusion. A sparse graph does the same: two paths of `s` vertices
with a perfect matching between them have `m̂ = s` and `b = 2`, with cost of order `n²` (computed by script). The paper's formula
overestimates at the state above, at `n³ k_h / 8`, because an iteration has at most `n (b - 1)` potential moves
([`card_potentialMoves_le_mul`](MedianConsensus/Algorithm/Complexity.lean#L89)), not only `2 m̂` (`card_potentialMoves_le`). What holds is the upper bound `2 n² k_h` for same-size
clusters ([`iterationCost_le_quadratic`](MedianConsensus/Algorithm/Complexity.lean#L153)). Without same-size clusters it fails ([`iterationCost_large_cluster`](MedianConsensus/Algorithm/Complexity.lean#L173)), and the excess
grows: the complete graph on 80 vertices, with one cluster of 40 and singletons, costs `70360` against `12800` (by script). This
agrees with the paper's next remark on large clusters. The bound `O(m̂ n k_h / b)` itself is proved, with its constant, along the
paper's derivation ([`iterationCost_mul_parts_le`](MedianConsensus/Algorithm/Complexity.lean#L141)).

**E9. Computation and memory complexity, p. 6, and Conclusions, p. 12: reported figures.** The paper says: "Given that all
algorithms utilize 8-byte numbers for each piece of information, our algorithm required 296 megabytes of memory while some other
baseline methods required nearly 268 gigabytes", for `n = 514k`, `m = 12` million and `k = 16`. These could not be reproduced from
what the paper states. `O(m + nk)` numbers give 162 MB at one number per edge, 258 MB at two, and 354 MB at three. A dense matrix of
`n²` 8-byte numbers takes 2.1 TB, and `n (n - 1) / 2` of them 1.06 TB; 268 GB is close to `n²` single bytes. The accounting behind
268 GB would also need only about 16 GB at `n = 125000`, where the paper reports that `boem` and `lf-consensus` ran out of memory on a
256 GB machine (p. 11), so the figure and the experiment do not fit one model. The paper does not give its accounting, so this may be a
difference of accounting and not an error, and the conclusion that the baselines cannot run on that machine stands in any case.
Separately, the Conclusions claim "linear speedup", while the abstract reports `35x` on 64 cores, an efficiency of 55%. Computed by
script, and not in Lean.

**E10. Evaluation metrics, p. 8: the description of the split-join distance.** The paper says that it "quantifies
the minimum number of split and join operations required to transform one partition into the other". One split
takes `{{0, 1, 2, 3}}` to `{{0, 1}, {2, 3}}`, at distance `2` ([`splitJoin_one_split`](MedianConsensus/Grouping.lean#L134)). The proof of van Dongen's
Theorem 4 shows that the distance is a shortest path where a split or a join costs the size of the smaller part, and he
reads it as a number of node moves. The paper's use of the distance is unaffected.

**E11. Appendix, pp. 12-13: two steps left out.** Both statements hold, and both steps are filled in here.

- *Eq. (7).* The appendix calls the distance the symmetric difference of "the sets of all co-clustered pairs", and derives Eq. (7) from
  `|A △ B| = |A| + |B| - 2 |A ∩ B|`. For those sets, this gives an expression in `1 - δ_uv`, not Eq. (7). The identity gives Eq. (7) for the
  complements, the separated pairs, and the two symmetric differences coincide. A comment in the arXiv source notices the point, with a sign
  error: `(1-x)+(1-y)+2(1-x)(1-y)` for `(1-x)+(1-y)-2(1-x)(1-y)`. The formalization uses the complements ([`mirkin_eq_card_symmDiff_sepPairs`](MedianConsensus/Problem/Mirkin.lean#L51),
  `equation7`).
- *The gain of a move.* The derivation starts from `∑_{u ∈ c} (k - 2 δ_uv) - ∑_{u ∈ c'} (k - 2 δ_uv)`, and this first line, which is the actual
  content, is asserted; the rest is algebra. It needs that a move changes `δ_uv(C)` only for the pairs containing `v`, and for those, to
  `1 - σ_u(c')` from `1 - σ_u(c)`. `equation5` proves this, through [`coClustered_moveVertex_of_ne`](MedianConsensus/GraphAware/Move.lean#L21) and [`coClustered_moveVertex_self`](MedianConsensus/GraphAware/Move.lean#L27). Filkov and
  Skiena prove the analogous step (their Lemma 3).

**E12. Typos.**

- Eq. (3), p. 3: the summand is `δ_uv(P_k)`, for `δ_uv(P_i)`.
- Appendix, p. 13: `≈` in the last line of the derivation of Eq. (4), for equality up to the constant `∑_uv δ_uv`.
- The algorithm, p. 5: "Section 3.3", though the published sections have no numbers.
- Clustering single-cell experiment data, p. 10: "Fig. 7 shows that … we could recover more accurate clusters". This
  is Fig. 6(b), as the arXiv source's `\ref{fig:levine13}` shows; Fig. 7 shows distances to the inputs on LFR graphs.
- Fig. 1, panel `P₁`: the labels `v₁` and `v₂` are swapped relative to the other panels. Both vertices are red in
  `P₁`, so nothing changes. In panel `P₄`, `v₇` and `v₉` are a lighter red, but `δ_{v₃v₉} = 2` requires one cluster.
- Ref. 22 gives Wakabayashi (1986) as "Acta Inform."; it is a doctoral thesis (Augsburg).
- Naive optimization, p. 3: "`O(n²)` time" for computing `δ_uv` for all pairs omits the factor `k`; Filkov and Skiena have `O(n² k)`.
- Spellings: "Fawlkes" (Fowlkes), "Skienna" (Skiena), "split-joint", "partion"; "Eq. (5). ." on p. 6.

## 4. Missing hypotheses

No statement of the paper needs a hypothesis of substance. These are degenerate cases that the paper leaves implicit.

| Where | Missing hypothesis | Counterexample without it | In the formalization |
| --- | --- | --- | --- |
| Eq. (6) | `v` has a neighbour | For an isolated `v`, `C_v` is empty, and the `argmin` does not exist | `equation6` proves this equivalence; the algorithm then does not move `v` |
| Rand distance | `n ≥ 2` | For `n ≤ 1`, the denominator `C(n, 2)` vanishes | [`randDistance_eq_mirkin_div`](MedianConsensus/Evaluation/Rand.lean#L57) and [`randDistance_isMetric`](MedianConsensus/Evaluation/Rand.lean#L71) assume it |
| Eq. (5) | `c'` is a cluster of `C` | Otherwise there is no such move | `equation5` assumes it |

## 5. Redundant hypotheses

None. The one explicit hypothesis is "the assumption of all clusters being of equal size" for the bound `O(m̂ n k_h / b)`, and it is needed:
`cost · b ≤ 4 m̂ n k_h` fails without it (`2058 > 1728`, for 12 vertices, on the graph joining a set of 6 to the other 6, with the 6 as a cluster and
the others as singletons; by script). Eqs. (1)-(5) do not involve the graph, as in the paper.

## 6. How the formalization reads the paper

- **Partitions.** A partition of the vertex set is a `Finpartition (univ : Finset V)`, as `Clustering V`. Eq. (2) is
  defined as the product over its parts, and `equation2` proves its values.
- **Vertices and pairs.** `V` is a finite linear order. A sum `∑_uv` runs over the unordered pairs of distinct vertices,
  listed as `(u, v)` with `u < v` ([`pairs`](Challenge.lean#L92)). The order only names the pairs: `card_ordered_disagreements` and
  [`two_mul_objective`](MedianConsensus/Problem/Objective.lean#L58) express the distance and the objective without it. See E1.
- **Eq. (1).** The `argmin` is a set, so the formalization has a predicate, [`IsMedian`](Challenge.lean#L129). Minimizers exist (`equation1`), and
  need not be unique ([`isMedian_of_two`](MedianConsensus/Problem/Objective.lean#L72)).
- **Values.** `σ`, `δ` and the objective take values in `ℤ`, since `k - 2 δ_uv` can be negative. The total distance is in
  `ℕ`; the identities that relate them are in `ℤ`.
- **A move.** [`moveVertex`](Challenge.lean#L152) is defined through labels: `v` gets the label `c'`, and every other vertex keeps its cluster as its
  label. [`coClustered_moveVertex_of_ne`](MedianConsensus/GraphAware/Move.lean#L21) and [`coClustered_moveVertex_self`](MedianConsensus/GraphAware/Move.lean#L27) characterize it, and [`parts_moveVertex`](MedianConsensus/GraphAware/Move.lean#L39) proves that
  its clusters are the expected ones. If `c'` is not a cluster, `v` becomes a singleton: this is not a move of the paper, and
  the theorems assume that `c'` is a cluster.
- **Eq. (5).** The sum runs over `u ≠ v` (E4).
- **Eq. (6).** [`IsBestMove`](Challenge.lean#L163) is a predicate, since the minimizer need not be unique. `C_v` may contain the current cluster of `v`,
  with `ΔD = 0`; such a pick is not a move, since a move needs `ΔD < 0`.
- **The algorithm, one move at a time.** [`GreedyStep`](Challenge.lean#L176) lets any vertex with a negative best move take any of its best moves. The
  theorems about it therefore hold for every order and every way of breaking ties. The start is `⊥`, the singletons
  ([`coClustered_bot`](MedianConsensus/Problem/CoClustering.lean#L83)).
- **The iteration.** [`BatchStep`](MedianConsensus/Algorithm/Parallel.lean#L37) performs all the best moves together, and has no validation checks, since the paper does not
  say what they are (E7).
- **Cost.** The paper's `O(·)` statements are informal. The formalization counts operations for an explicit model: evaluating a
  term of Eq. (5) for a cluster `c` costs `k_h` per vertex of `c` ([`moveCost`](MedianConsensus/Algorithm/Complexity.lean#L111), [`iterationCost`](MedianConsensus/Algorithm/Complexity.lean#L115)).
- **Thresholds.** In the grouping, `d` and `λ` are natural numbers. The paper's thresholds between `0.05` and `1` are for a
  normalized distance that it does not define. The authors' code uses `d / (2 n)`, and `d / (2 n) ≤ λ` is `d ≤ ⌊2 n λ⌋`.
- **The figures.** The partitions and the 23 edges of Figs. 1 and 2 were read from the published figures, and checked by a second
  reader. `figure1` and `figure2` compute the paper's numbers from the definitions.

Corrections of statements, all obvious misprints with one possible reading: the summand of Eq. (3), the range of the sum in
Eq. (5) (E4), and `≈` in the appendix (E12).

## 7. Departures from the paper's proofs

The paper gives few derivations, and they are short:

- Eq. (7), through the symmetric difference and the identity for its size: [`mirkin_eq_card_symmDiff_sepPairs`](MedianConsensus/Problem/Mirkin.lean#L51), `equation7`.
- The chain from Eq. (1) to Eq. (4), which `appendix_identity` follows line by line, and `equation4`.
- The derivation of `ΔD`: [`deltaD_eq_sum_sub_sum`](MedianConsensus/GraphAware/Move.lean#L124), [`deltaD_eq_second_form`](MedianConsensus/GraphAware/Move.lean#L117), `equation5`.
- The bound `O(m̂ n k_h / b)`, from the number of potential moves and the cost of each: [`iterationCost_mul_parts_le`](MedianConsensus/Algorithm/Complexity.lean#L141).

All follow the paper, with two repairs of a step, each forced because the paper's step has a gap:

| Result | The paper's argument | The formalization's | Why it is necessary | E-item |
| --- | --- | --- | --- | --- |
| `equation7` | The identity for `\|A △ B\|`, with the sets of co-clustered pairs named | The same identity, for the sets of separated pairs, which are what `δ` indicates | The identity for the named sets does not give Eq. (7) | E11 |
| `equation5` | Asserts the change in the objective as the first line of the derivation, then algebra | Proves the change directly from the pairs containing `v`, for the form that [`deltaD`](Challenge.lean#L140) defines; the first line is then [`deltaD_eq_sum_sub_sum`](MedianConsensus/GraphAware/Move.lean#L124) | The paper gives no argument for its first line, so there is nothing to follow at that step | E11 |

Everything else that the formalization proves, the paper states without a derivation, or derives by an argument that turns out to be wrong (the reasoning of E8, which
is not formalized, since its conclusion fails). Those proofs are the formalization's own, and each is the evident one: the metric property through the symmetric
difference, as the appendix suggests, and termination through the total distance. The proof of the cited metric property of the split-join distance is a direct count, not
van Dongen's argument (Section 2). An independent reader compared these formal proofs with the published text and the TeX.

## 8. What each result depends on

Generated from [`scripts/Audit.lean`](scripts/Audit.lean).

| Result | Lean | Results from prior work used |
| --- | --- | --- |
| Eq. (1) | `equation1` | – |
| Eq. (2) | `equation2` | – |
| Eq. (3) | `equation3` | – |
| Fig. 1 caption, Hamming | [`deltaTotal_eq_hammingDist`](MedianConsensus/Problem/CoClustering.lean#L127) | – |
| Eq. (7) | `equation7` | – |
| Mirkin metric | `mirkin_isMetric` | – |
| Mirkin counts twice | `card_ordered_disagreements` | – |
| Appendix identity | `appendix_identity` | – |
| Eq. (4) | `equation4` | – |
| Intra/inter | [`totalDistance_eq_intra_sub_inter`](MedianConsensus/Problem/Objective.lean#L99) | – |
| Eq. (5) | `equation5` | – |
| Negative reduces | `moveVertex_reduces` | – |
| Eq. (6) | `equation6` | – |
| Stopping condition | `not_canMove_iff` | – |
| The algorithm stops | `greedyStep_wellFounded` | – |
| Not optimal | `greedy_not_optimal` | – |
| Order dependence | [`order_influences_candidates`](MedianConsensus/Algorithm/Examples.lean#L83) | – |
| Parallel batch | [`batch_counterexample`](MedianConsensus/Algorithm/Parallel.lean#L45) | – |
| Pairs count | [`card_pairs`](MedianConsensus/Algorithm/Complexity.lean#L25) | – |
| Moves list | [`potentialMoves_eq_image`](MedianConsensus/Algorithm/Complexity.lean#L31) | – |
| Moves at most 2m̂ | `card_potentialMoves_le` | – |
| Moves at most m | [`card_potentialMoves_le_two_mul_edges`](MedianConsensus/Algorithm/Complexity.lean#L83) | – |
| Iteration cost | [`iterationCost_mul_parts_le`](MedianConsensus/Algorithm/Complexity.lean#L141) | – |
| Large clusters | [`iterationCost_large_cluster`](MedianConsensus/Algorithm/Complexity.lean#L173) | – |
| Both conditions | [`both_conditions_occur`](MedianConsensus/Algorithm/Complexity.lean#L444) | – |
| Group distances | [`group_distances_counterexample_splitJoin`](MedianConsensus/Grouping.lean#L81) | – |
| Group distances, corrected | [`splitJoin_le_of_reachable`](MedianConsensus/Grouping.lean#L71) | [`External.VanDongen.splitJoin_isMetric`](External/VanDongen/SplitJoin.lean#L149) |
| Groups decrease | [`card_components_antitone`](MedianConsensus/Grouping.lean#L120) | – |
| Split-join and operations | [`splitJoin_one_split`](MedianConsensus/Grouping.lean#L134) | – |
| Rand metric | [`randDistance_isMetric`](MedianConsensus/Evaluation/Rand.lean#L71) | – |
| Rand normalized | [`randDistance_eq_mirkin_div`](MedianConsensus/Evaluation/Rand.lean#L57) | – |
| Fig. 1 | `figure1` | – |
| Fig. 2 | `figure2` | – |
| Fig. 10 | [`contingency_sum`](MedianConsensus/Evaluation/Rand.lean#L33) | – |

[`External.VanDongen.splitJoin_isMetric`](External/VanDongen/SplitJoin.lean#L149) is used by [`splitJoin_le_of_reachable`](MedianConsensus/Grouping.lean#L71). The route check passes, with one difference recorded in [`docs/route_differences.tsv`](docs/route_differences.tsv), with its reason (the values of `δ` in Eq. (2), which the
paper uses throughout without citing). This is weak evidence here. The paper has no theorem environments and its derivations cite almost nothing, so [`docs/paper_routes.tsv`](docs/paper_routes.tsv) was
written by hand, after the proofs were finished. The comparison that counts is the line-by-line one of Section 7.

## 9. Not formalized

- **The experiments**: all the accuracy, median-quality, runtime and speedup results (Figs. 3-9), the comparisons with `boem`,
  `lf-consensus` and `kirkley-newman`, and the conclusions drawn from them, including the statements that the sequential and parallel
  versions reach the same quality and that the speedup is linear.
- **NP-completeness** of the problem (E3): it motivates the heuristic, and no proof uses it.
- **The variation of information**, and that it is a metric (p. 8). It is an evaluation metric only. Meilă's proof would need the
  entropy of partitions, which is a moderate project that no argument of the paper needs.
- **The `O(·)` statements** as such: the formalization proves explicit counts instead (Section 6). The running time of split-join, of
  connected components, and the memory bound `O(m + nk)` are not formalized, since they depend on data structures.
- **The elbow method** for choosing `λ`, and the validation checks of the authors' code (E7).

## 10. The paper in the literature

Searched on 2026-11-01: Crossref, Crossmark, PubMed, Europe PMC, the arXiv API, Semantic Scholar, OpenAlex, OpenCitations and general
web search, and for formalizations GitHub, the Archive of Formal Proofs, mathlib, the Lean Zulip archive and the Palomar registry.
Google Scholar was not queried. Works were screened by abstract, and the closest were read. Some sources were read in an earlier or
alternate version, as stated.

### Before the paper

- **Hardness.** Median partition is NP-hard for an unbounded number of inputs, per sources that attribute this to Křivánek and Morávek
  (1986) and Wakabayashi (1986) (for example [Betzler et al., JCSS 2011](https://doi.org/10.1016/j.jcss.2010.07.005); neither original
  was read). [Wakabayashi (1998)](https://revistas.usp.br/resenhasimeusp/article/view/74876) proves results for arbitrary relations, and
  says that the partition case can be derived. Ailon, Charikar and Newman ([JACM 2008](https://doi.org/10.1145/1411509.1411513)) note
  that the problem "is not known to be NP-hard if the number of input clusters is constant". [Bonizzoni et al.
  (2008)](https://doi.org/10.1016/j.jcss.2007.06.024) prove APX-hardness for three inputs. [Dörnfelder et al. (TCS
  2014)](https://doi.org/10.1016/j.tcs.2014.05.002) prove NP-hardness when each input has at most two blocks, with unboundedly many
  inputs, and also that local search within a Mirkin radius `d` is W[1]-hard in `d`. [Chen, Hermelin and Sorge (preprint,
  2018)](https://arxiv.org/abs/1807.08949) refine this.
- **Approximation.** Filkov and Skiena (2004) show that the best of the inputs is a factor-2 approximation, with a family reaching
  `2(k-1)/k`. Gionis, Mannila and Tsaparas ([ICDE 2005](http://www.cs.uoi.gr/~tsap/publications/aggregated.pdf); TKDD 2007) give the
  bound `2(1 - 1/k)`, and BALLS with ratio at most 3. Ailon et al. give `11/7` in expectation, and `4/3` with an LP. The paper cites
  Ailon et al. and Filkov and Skiena, but mentions none of these guarantees.
- **Local search.** The paper's greedy rule descends from `boem`: "we repeatedly perform the best one element move as long as it decreases
  S" ([Goder and Filkov, ALENEX 2008](https://www.cs.ucdavis.edu/~filkov/papers/consensuseval.pdf)). Their moves may go to an empty block, unlike the paper's. They also
  test seeding it with the best input, as Filkov and Skiena (§4.2) suggest; since moves only decrease the distance, such a run keeps the guarantee of the best input. The search
  found no theorem that bounds the ratio of the local optima of one-element moves for median partition. [Cohen-Addad et al. (STOC
  2024)](https://arxiv.org/abs/2404.05433) analyse local search for unweighted correlation clustering, with larger moves.
- **Graphs.** Lancichinetti and Fortunato (2012) started consensus clustering for networks, through the co-clustering matrix; Tandon et al.
  (2019) and Kirkley and Newman (2022) followed. The search found no earlier work on median partition restricted to clusters that contain
  a neighbour. The closest is the argument of [Cordner and Kollios (COCOA 2023)](https://cs-people.bu.edu/ncordner/papers/cocoa2023_paper.pdf)
  for correlation clustering, where the neighbour graph is the graph of positive pairs, unlike here.
- **Synchronous moves.** That moves made together can fail is known for neighbouring problems. Raghavan et al.
  ([PRE 2007](https://arxiv.org/abs/0709.2938)) note oscillations of synchronous label propagation on bipartite subgraphs. Cordasco and
  Gargano ([BASNA 2010](https://arxiv.org/abs/1103.4550)) prove convergence of a semi-synchronous version. Lu, Halappanavar and
  Kalyanaraman ([Parallel Comput. 2015](https://arxiv.org/abs/1410.1237)) show that a parallel modularity gain "cannot be guaranteed to be
  always positive", and use a rule against swaps between singletons. Shi et al. ([PVLDB 2021](http://www.vldb.org/pvldb/vol14/p2305-shi.pdf))
  say of correlation clustering that "these moves in tandem may lower the total objective; there is no guarantee of convergence". So
  [`batch_counterexample`](MedianConsensus/Algorithm/Parallel.lean#L45) is the median-partition instance of a known phenomenon. The paper's statement that "there has been no study on
  parallelization strategies of the consensus clustering algorithm" is about consensus clustering in particular; parallel correlation
  clustering, which contains it as a weighted case, had been studied (also [Pan et al., preprint 2015](https://arxiv.org/abs/1507.05086)).
- **The distances.** [Meilă (JMVA 2007)](https://doi.org/10.1016/j.jmva.2006.11.013) gives the Mirkin metric in the form of
  `sum_sq_parts_add_sum_sq_parts`, and proves that the variation of information is a metric. Van Dongen (2000) defines the split-join
  distance and proves that it is a metric.

### Concurrent work

[FastEnsemble](https://arxiv.org/abs/2409.02077) (Tabatabaee, Wedell, Park and Warnow; arXiv, 3 September 2024, thirteen days after this
paper's arXiv version; published in PLOS Complex Systems, October 2025) is an ensemble clustering method for large networks. It addresses
the same question by another method, and its published version cites this paper as a method still to compare with.

### Since the paper

- No erratum or correction was found (Crossmark: "Document is current"), and arXiv v1 is the only arXiv version.
- Seven citing works were found. None extends, corrects or analyses the algorithm. The one substantial comparison is Vu-Le et al.,
  [CVC](https://doi.org/10.1007/s41109-026-00809-z), Applied Network Science 11:53 (2026), whose first author appears to be the person who requested this formalization. It reports that its pipeline "is also more
  accurate than the Median Consensus approach", that Median Consensus accuracy "degraded substantially when the ensemble includes low node
  coverage clustering methods", and that it is otherwise comparable.
- The others cite it in passing: Vu-Le et al. ([preprint, 2025](https://arxiv.org/abs/2508.17013)); FastEnsemble, above; Romero Moreno et al.
  ([medRxiv, 2026](https://doi.org/10.64898/2026.05.25.26353178)). Two (van Dreven et al., Inf. Fusion 2026; Lu et al., Neurocomputing 2026)
  were confirmed by Crossref as citing the paper, but were not read.
- [Das and Kumar (SODA 2025)](https://pure.psu.edu/en/publications/breaking-the-two-approximation-barrier-for-various-consensus-clus/) go below
  factor 2 for related consensus problems; only the abstract was read.

### Formalizations

No formalization of this paper, of median partition, of the Mirkin metric, of the Rand index, of the split-join distance or of the variation
of information was found. Three public Lean projects touch correlation clustering: [vinhqdang/correlation_clustering](https://github.com/vinhqdang/correlation_clustering),
whose `CC.cost_move` is the nearest analogue of Eq. (5), for unweighted cluster editing;
[teganwilson/CompetitiveRandomOrderCorrelationkClustering-Lean](https://github.com/teganwilson/CompetitiveRandomOrderCorrelationkClustering-Lean);
and `CorrClustBBC` in [prove2me/formalpedia](https://github.com/prove2me/formalpedia). They formalize other results, and this work did not
consult or use them.

## 11. What's next

Plans for follow-up papers are kept in `NEXT.md`, which is not published.

### Open directions

- **A guarantee for the algorithm.** No approximation guarantee is known for the greedy rule from the singletons, and [`graph_restriction_stuck`](MedianConsensus/Algorithm/Examples.lean#L183) and `greedy_not_optimal` show
  that it cannot be exact without some condition. What ratio holds for its runs on the complete graph, and under what relation between `G` and the inputs?
- **The validation checks.** Which rule for the moves of an iteration guarantees that the objective decreases and the iteration stops, while still making many moves in each
  iteration? Performing only the single best move, which p. 6 mentions, guarantees descent, and gives up the parallelism. So the question is about the progress per iteration.
- **Moves that the algorithm lacks.** A vertex cannot leave its cluster to become a singleton, though this can decrease the objective, and `boem` allows it. Two clusters cannot
  merge; the analogous step in Louvain is its aggregation phase. What do such moves add to the local optima?
- **Connectivity of the clusters.** The paper moves vertices along edges, and Louvain-style moves are known to produce disconnected communities
  (Traag et al., [Sci. Rep. 2019](https://arxiv.org/abs/1810.08473)). How does this play out for a median objective?
- **The complexity for fixed `k`.** Is the problem NP-hard for every fixed `k ≥ 4`? Bonizzoni et al. treat three, and the paper's claim for all `k > 2` (E3) needs the others.
- **From the paper.** It proposes an extension to dynamic networks, the use of correspondences between partitions, and sampling or sketching for
  large clusters.

### Simpler proofs

- **Eq. (7).** The paper goes through sets and the size of a symmetric difference. For `x, y ∈ {0, 1}`, `|x - y| = x + y - 2 x y`, and summing over
  the pairs gives Eq. (7) at once, with no sets. Checked on paper; the Lean proof follows the paper's route.

The appendix's chain to Eq. (4) is already this computation, per pair. The rest of the paper's derivations are short.

### The formalization

- **What could extend it.** The variation of information and its metric property; the validation checks of the authors' code, once a precise
  statement is agreed; the `O(·)` statements against a real cost model; hardness (E3).
- **[`Basic/`](Basic)** holds [`Finset.card_symmDiff_add_two_mul_card_inter`](Basic/Data/Finset/SymmDiff.lean#L22) and [`Finset.card_symmDiff_triangle`](Basic/Data/Finset/SymmDiff.lean#L32), which could go to
  `Mathlib/Data/Finset/SymmDiff.lean`, and the sums over pairs `x < y`, which could go to `Mathlib/Algebra/BigOperators/` and
  `Mathlib/Combinatorics/SimpleGraph/Finite.lean`. They depend on nothing else.
- **[`External/`](External)** holds the proof that the split-join distance is a metric, in `Finset` and `Finpartition` terms, which other formalizations
  about comparing partitions can reuse.
