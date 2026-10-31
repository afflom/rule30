# Experiments

Finite, exact computations on the seeded Rule 30 orbit. Nothing here is a
proof input: every script states its bounds and assumes no infinite center
period. Run one with `bin/r30 experiment run <name> [args]`, which executes it
isolated (`python3 -I`) from the repository root.

| Script | Measures |
| --- | --- |
| `diagnose_qadic_windows.py` | the classified seeded cancellation windows and the q-adic rank change at each step |
| `diagnose_front_coupling.py` | the center coupling law at every agreeing step, the q-order histogram, front slack, evaluation points, arrival statistics |

`legacy/` holds the exploratory scripts of the early strategy phases (coarse
graining, interface orders, zero-state facets, period tables). They are kept
for the record and are not maintained.
