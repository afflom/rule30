module

public import Rule30UOR.Interfaces.Part01
public import Rule30UOR.Interfaces.Part02
public import Rule30UOR.Interfaces.Part03
public import Rule30UOR.Interfaces.Part04
public import Rule30UOR.Interfaces.Part05
public import Rule30UOR.Interfaces.Part06
public import Rule30UOR.Interfaces.Part07
public import Rule30UOR.Interfaces.Part08
public import Rule30UOR.Interfaces.Part09
public import Rule30UOR.Interfaces.Part10
public import Rule30UOR.Interfaces.Part11
public import Rule30UOR.Interfaces.Part12
public import Rule30UOR.Interfaces.Part13
public import Rule30UOR.Interfaces.Part14
public import Rule30UOR.Interfaces.Part15
public import Rule30UOR.Interfaces.Part16
public import Rule30UOR.Interfaces.Part17

/-!
# Rule 30 at the interfaces of its linear part

Rows of rule 30 as natural numbers: bit `i` is a cell, and one step is
`phi y = y ⊕ (2y ∨ 4y)` (the right edge at bit 0). The linear part `y ⊕ 2y ⊕ 4y` is
multiplication by `Φ₃(x) = 1 + x + x²` over `F₂`, the irreducible polynomial form of `3`; the
remainder is the carry `2 (y ∧ 2y)`.

Two interfaces, the two irreducible factors met so far:
* `1 + x` (evaluate at `x = 1`, the parity of the row): `par_phi`,
  `par (phi y) = par y ⊕ par (y ∧ 2y)`.
* `Φ₃` (evaluate at a root `ω` of `1 + x + x²` in `F₄`): `val_phi`,
  `val (phi y) = ω · val (y ∧ 2y)`. The linear part vanishes there; the row's value is the
  previous row's carry.

`F₄` is `Bool × Bool`, the pair `(a, b)` standing for `a + b ω`, with `ω² = 1 + ω`.
-/

@[expose] public section
