# feat(ErdosProblems): formalize problem 1075

Fixes #1115.

Add the statements of Erdős Problem 1075 and closely related variants.
The assertion quantified over every r >= 3 is false, with counterexamples for every r >= 5. The r = 3 and r = 4 variants remain open.

Formalization choices:

- Edges are a finite set of finite vertex sets, each of cardinality r.
- For every prescribed subgraph order m, the conclusion holds at all sufficiently large n. This expresses the required divergence of the subgraph order.
- Counting all edges contained in a vertex set is equivalent to asking for some subgraph on that set. The bridge uses the proved counterexamples with m = 1.

The external proof attributes link to the [proved results](https://github.com/FireflySentinel/erdos-1075/blob/2910c83a757d951eea37a228cc763243d4e998d8/Erdos1075/Main.lean).
`checks/FormalConjecturesBridge.lean` in the proof repository proves the linked
statements using the proposed definitions. Its axiom guards allow only
`propext`, `Classical.choice`, and `Quot.sound`.

Validation: `lake --wfail build 'FormalConjectures.ErdosProblems.«1075»'`
on Lean 4.33.1; the proof bridge compiles on the proof repository's Lean 4.33.0.
A source comparison checks that the definitions and linked statement types agree.

AI assistance: OpenAI Codex (GPT-6) was used to prepare the statements, proof
bridges, and this draft.
