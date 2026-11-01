# Results that the paper cites

The paper's derivations cite no earlier theorem: its appendix uses only the definition of the Mirkin
distance and the identity `|A △ B| = |A| + |B| - 2 |A ∩ B|` (which is in `Basic/`). So this library
holds only what the paper asserts of a source about a distance it uses.

| Directory | Source | What it proves | How the paper uses it |
| --- | --- | --- | --- |
| `VanDongen/` | S. van Dongen, *Performance criteria for graph clustering and Markov cluster experiments*, CWI report INS-R0012 (2000) | the split-join distance is a metric, by a direct count rather than van Dongen's argument | the distance used to group homogeneous partitions, and one of the three evaluation metrics, which "are true distance metrics" |

The other citations of the paper that make mathematical claims give context and are used in no proof.
`REPORT.md`, Section 2, lists them.
