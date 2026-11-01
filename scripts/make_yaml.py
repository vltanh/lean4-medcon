#!/usr/bin/env python3
"""Write formalization.yaml from the Challenge's theorem names, so that its alignment stays complete."""
import json, re, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
WALL = sys.argv[1] if len(sys.argv) > 1 else 'not yet recorded'
AGENTS = sys.argv[2] if len(sys.argv) > 2 else 'independent agents'
names = [n.split('.')[-1] for n in json.loads((ROOT / 'comparator.json').read_text())['theorem_names']]
src = {
 'equation2': 'Eq. (2)', 'equation3': 'Eq. (3), with the misprint P_k corrected to P_i',
 'equation7': 'Eq. (7)', 'mirkin_eq_card_symmDiff': 'Appendix: the Mirkin distance as a symmetric difference',
 'mirkin_isMetric': 'Appendix: "This distance is a metric"',
 'card_ordered_disagreements': 'Methods: "counts (twice)"',
 'sum_sq_parts_add_sum_sq_parts': 'The classical formula for the Mirkin metric (Meila 2007), identifying the definition',
 'appendix_identity': 'Appendix: the derivation of Eq. (4) from Eq. (1)',
 'equation4': 'Eq. (4)', 'equation1': 'Eq. (1): the argmin exists',
 'moveVertex_of_ne': 'The move of a vertex: pairs not containing it', 'moveVertex_self': 'The move of a vertex: pairs containing it',
 'equation5': 'Eq. (5), with the sum over u different from v', 'moveVertex_reduces': 'Graph-aware consensus clustering: a negative gain reduces the disagreements',
 'equation6': 'Eq. (6): when the argmin exists', 'not_canMove_iff': 'The algorithm: the stopping condition',
 'greedyStep_wellFounded': 'The algorithm: it stops, for moves made one at a time (not proved in the paper)',
 'exists_stable': 'The algorithm: from every partition, a run reaches the stopping condition (not proved in the paper)',
 'greedy_run_length_le': 'The algorithm: a bound on the number of moves (not in the paper)',
 'greedy_not_optimal': 'Graph-aware consensus clustering: the policy "does not guarantee an optimal solution"',
 'card_potentialMoves_le': 'Computation and memory complexity: at most 2 m-hat potential moves',
 'figure1': 'Fig. 1: the values of delta', 'figure2': 'Fig. 2: the computation of the best move',
}
assert set(names) == set(src), set(names) ^ set(src)
align = ''.join(f'''    - source: {json.dumps(src[n], ensure_ascii=False)}
      lean: "MedianConsensus.Challenge.{n}"
      module: "Challenge"
      status: "proved"
''' for n in names)
text = f'''# yaml-language-server: $schema=https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json
version: "v0.4"

project:
  name: "Median consensus clustering: the mathematics of Hussain et al. (2025)"
  description: >-
    A formalization of the mathematics of Hussain, Halappanavar, Chatterjee, Radicchi, Fortunato and Azad,
    Parallel median consensus clustering in complex networks, Sci. Rep. 15, 3788 (2025). Given partitions of a
    finite vertex set, a median partition minimizes the total Mirkin distance to them. The formalization proves
    that the Mirkin distance is a metric, derives the objective of Eq. (4) and the exact change Delta D of Eq. (5)
    under moving a vertex, and proves that the paper's greedy algorithm stops when moves are made one at a time,
    that on some instances it stops only at non-medians, and that an iteration has at most 2 m-hat potential moves. It computes the
    paper's worked example from the definitions.


    It also records an audit of the paper. Eq. (5) as printed is off by k, and the paper's own figure contradicts it.
    Several claims in running text are false as written or undefined, with Lean counterexamples and corrected statements. Performing
    all the moves of an iteration together, without the checks that the paper leaves unspecified, can raise the
    objective and never stop. The paper's experiments are not formalized.
  authors:
    - "The-Anh Vu-Le"
  license: "Apache-2.0"
  responsible_maintainers:
    - "The-Anh Vu-Le"

classification:
  arxiv: ["cs.SI", "cs.DS"]
  msc2020: ["05A18", "62H30", "68R10", "68W40", "68V20"]

sources:
  - title: "Parallel median consensus clustering in complex networks"
    authors:
      - "Md Taufique Hussain"
      - "Mahantesh Halappanavar"
      - "Samrat Chatterjee"
      - "Filippo Radicchi"
      - "Santo Fortunato"
      - "Ariful Azad"
    id: "doi:10.1038/s41598-025-87479-6"
    type: "article"
    location: "https://doi.org/10.1038/s41598-025-87479-6"
    relationship: "formalizes"
    note: "The version of record. The labels come from the TeX source of arXiv:2408.11331v1, an older version."
    license: "CC BY-NC-ND 4.0"
    author_endorsement: "not-contacted"
  - title: "Performance criteria for graph clustering and Markov cluster experiments"
    authors:
      - "Stijn van Dongen"
    id: "CWI report INS-R0012"
    type: "technical report"
    location: "https://ir.cwi.nl/pub/4461/04461D.pdf"
    relationship: "background"
    note: "The split-join distance is a metric: the formalization proves it, in External/VanDongen."
  - title: "Comparing clusterings - an information based distance"
    authors:
      - "Marina Meila"
    id: "doi:10.1016/j.jmva.2006.11.013"
    type: "article"
    location: "https://doi.org/10.1016/j.jmva.2006.11.013"
    relationship: "background"
    note: "The classical formula for the Mirkin metric, against which the definition is compared."

related_formalizations: []

status:
  scope: >-
    Formalized: the definitions and derivations of the paper (Eqs. (1)-(7), its appendix), the worked example of its Figs. 1 and 2, and its
    mathematical claims in running text, with counterexamples and corrected statements where they are false as written. The results are
    unconditional. Not formalized: the experiments and the conclusions drawn from them, the NP-completeness of the problem, the variation of
    information, the O(.) statements as such (explicit counts are proved instead), and the validation checks of the authors' code, which the
    paper does not specify. The moves performed together are formalized without checks.
  sorry_count: 0
  sorry_in_definitions: 0
  axioms: []

automation:
  methods:
    - method: "agent"
      models: ["claude-opus-5-5"]
      framework: "Claude Code (VS Code extension, Claude Agent SDK)"
      tool_setup: "The formalize-math-paper skill, with {AGENTS}: statement review, literature search, audit verification, and refereeing of follow-up ideas."
      cost:
        wall_time: "{WALL}"
        spend_usd: "not tracked"
        hardware: "local machine"
      prompting_notes: "One prompt: the paper's URL, with the skill."
  spend_usd: "not tracked"
  notes: "An AI agent did the formalization and the audit, at the request of the author. See CREDITS.md."

fidelity:
  divergences: >-
    Readings: partitions are Finpartition (univ : Finset V); the sums over uv are over unordered pairs of distinct vertices, listed with u < v,
    which is the count d = b + c of the appendix and of Fig. 2, while the Methods' "counts (twice)" is the count over ordered pairs, also proved;
    the move of a vertex is defined through labels, with a bridge lemma for its clusters; GreedyStep is one move at a time; the iteration with all
    the moves together is formalized without the unspecified checks; the costs are explicit counts; the grouping threshold is a natural number.
    Corrected misprints: the summand of Eq. (3) (P_k for P_i), the range of the sum in Eq. (5) (u different from v, as in the paper's Fig. 2, since
    the printed sum is larger by k), and the approximation sign in the appendix (equality up to a constant). Claims false as written, which are not
    changed, but proved false with the correct version beside them: the distances in a group of partitions, the claim that m-hat high and b low cannot
    occur together, and the description of the split-join distance; and the description through intra- and inter-cluster disagreements, undefined as
    written and false on the one definition on record. Departures from the paper's proofs, both repairing a step with a gap: Eq. (7) applies the identity
    for the symmetric difference to the separated pairs, since the co-clustered pairs that the paper names do not give Eq. (7); and Eq. (5) proves directly
    the change that the appendix asserts as its first line. The cited metric property of the split-join distance is proved by a direct count, not by the
    source's argument. Every other derivation of the paper is followed. REPORT.md has the details.

review:
  status: "agent-reviewed"
  reviewers:
    - "none"
  notes: >-
    No person has reviewed the proofs. Independent AI agents compared the statements and the Challenge with the paper, and verified the audit's
    findings and the literature account against the sources. Comparator accepts the Solution under Lean's kernel and NanoDa.

alignment:
  namespace: "MedianConsensus.Challenge"
  statements:
{align}
acknowledgements: "Mathlib. The formalize-math-paper procedure. The authors' public code, read to settle the reading of Eq. (5) and to describe the checks of its iteration."
'''
(ROOT / 'formalization.yaml').write_text(text)
