# The split-join distance

**Source.** S. van Dongen, *Performance criteria for graph clustering and Markov cluster experiments*,
CWI report INS-R0012 (2000).

**Statement.** For partitions `P`, `Q` of an `n`-element set, let the projection number be
`p_P(Q) = ∑_{c ∈ P} max_{c' ∈ Q} |c ∩ c'|`. Then `d(P, Q) = 2 n - p_P(Q) - p_Q(P)` is a metric on the
partitions of the set (`External.VanDongen.splitJoin_isMetric`).

**Proof.** The triangle inequality follows from `p_A(B) + p_B(C) ≤ p_A(C) + n`
(`External.VanDongen.projection_add_projection_le`), for which one chooses a best cluster of `B` for
each cluster of `A`, and a best cluster of `C` for each cluster of `B`, and counts the vertices that
leave. If `p_P(Q) = n`, every cluster of `P` lies in one of `Q`, which gives the identity of
indiscernibles. This is not van Dongen's proof, which shows that the distance is a shortest path where a
split or a join costs the size of the smaller part. The direct count is shorter here, and the source's
statement is the same.

**How the paper uses it.** The section "Grouping homogeneous partitions" weights a complete graph on
the input partitions by this distance, and the section "Evaluation metrics" evaluates results with it.
The theorem is used through `MedianConsensus.splitJoin_le_of_reachable`, the corrected form of the
paper's claim about the groups. The Lean statements are in the source's terms: they mention only
`Finpartition`, and nothing of the paper. The authors' code normalizes the distance by `2 n`, which
changes neither the metric property nor the components, up to rescaling the threshold.
