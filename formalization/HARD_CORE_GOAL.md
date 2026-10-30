# Revised goal: difficult kernels and a verified handoff to Luna max

Status: completed on 27 October 2026. P1 and the three new kernel modules build;
85 declarations were axiom-audited. The original full P0–P7 result remains open.
See `OddPiPowers/docs/LUNA_HANDOFF.md` for the accepted checkpoint and remaining
construction/analytic obligations.

This goal replaces pursuing the entire P0–P7 formalization in this chat. The original complete specification remains in `FORMALIZATION_GOAL.md` as background, not the completion criterion for this smaller goal.

## Required deliverables

1. Close P1, build the complete abstract irrationality-transfer theorem, and check its transitive axioms.
2. Prove a reusable repeated-node Taylor/jet uniqueness and confluent-matrix nondegeneracy kernel. It must support arbitrary finite distinct nodes with arbitrary multiplicities, and explain how local unit factors affect the jets.
3. Prove a reusable local power-series denominator calculus, including reciprocal linear factors and the product/convolution budget. Spell out its connection with the actual pole and regular factors of the manuscript.
4. If feasible, prove the pairwise real algebra inequality behind the full horizontal-line tail bound; explain the remaining finite-product and analytic steps.
5. Supply a precise Luna max handoff: working build, named checked declarations, required next statements, existing API choices, source links and any remaining genuinely difficult proof obligations. Do not describe unresolved analysis or construction bridges as mechanical if they are not.

These are mathematical kernels with concrete definitions and proofs, not structures whose fields assume the very claims being advertised.

## Completion boundary

This goal does not claim a complete integer auxiliary construction, the exact determinant identity at i, the prime divisor asymptotic, the contour deformation estimate, or any of the four numerical bounds. Such results must remain clearly marked open unless separately proved.

The required P1, repeated-node kernel, and denominator kernel must build without project axioms or placeholders. The optional horizontal kernel is reported at its actual status. The final handoff must distinguish proved kernels from their unproved application bridges.

Do not start another task, modify the other thread's goal, install another model, or spawn subagents unless separately authorized. Luna max is the user's intended model for the later handoff; this goal prepares that handoff.
