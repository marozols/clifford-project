import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Analysis.SpecialFunctions.Complex.Circle

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

#doc (Manual) "Roots of unity" =>

:::group "roots_of_unity"
Roots of unity and their basic properties.
:::

This section defines roots of unity and proves various basic facts about them.
Throughout this section we assume that $`d ≥ 1`.

```lean "non_zero_dimension"
variable (d : ℕ) [NeZero d]
```

Define the primitive $`d`-th root of unity.

:::definition "omega" (parent := "roots_of_unity") (owner := "Maris_Ozols")
Let $`ω = \exp(2πi/d)` be the primitive $`d`-th root of unity.
:::

```lean "omega"
noncomputable
def ω : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / d)
```

:::lemma_ "omega_pow_d_eq_one" (parent := "roots_of_unity") (effort := "small")
$`ω^d = 1`.
:::

:::proof "omega_pow_d_eq_one"
$`ω^d = (\exp(2πi/d))^d = \exp(2πid/d) = \exp(2πi) = 1`.
:::

```lean "omega_pow_d_eq_one"
lemma omega_pow_d_eq_one : ω^d = 1 :=
  sorry
```

We will also need another root of unity which we call $`τ`.

:::definition "tau" (parent := "roots_of_unity") (owner := "Maris_Ozols")
Let $`τ = -\exp(πi/d)`.
:::

```lean "tau"
noncomputable
def τ : ℂ :=
  - Complex.exp (Real.pi * Complex.I / d)
```

:::lemma_ "tau_sq_eq_omega" (parent := "roots_of_unity") (effort := "small") (owner := "Christian_Schaffner")
$`τ^2 = ω`.
:::

:::proof "tau_sq_eq_omega"
$`τ^2 = (-\exp(πi/d))^2 = (-1)^2 · (\exp(πi/d))^2 = 1 · \exp(2πi/d) = ω`.
:::

```lean "tau_sq_eq_omega"
lemma tau_sq_eq_omega : τ^2 = ω :=
  sorry
```

:::lemma_ "tau_pow_d_eq_one_of_odd" (parent := "roots_of_unity") (effort := "small") (owner := "Carli_Bruinsma")
If $`d` is odd then $`τ^d = 1`.
:::

:::proof "tau_pow_d_eq_one_of_odd"
$`τ^d = (-\exp(πi/d))^d = (-1)^d · (\exp(πi/d))^d = (-1)^d · \exp(πi) = (-1)^d · (-1) = (-1)^{d+1} = 1` when $`d` is odd.
:::

```lean "tau_pow_d_eq_one_of_odd"
lemma tau_pow_d_eq_one (hodd : Odd d) : τ^d = 1 :=
  sorry
```

:::lemma_ "tau_pow_d_sq_eq_one" (parent := "roots_of_unity") (effort := "small")
$`τ^{d^2} = 1`.
:::

:::proof "tau_pow_d_sq_eq_one"
$`τ^{d^2} = (-\exp(πi/d))^{d^2} = (-1)^{d^2} · (-1)^d = (-1)^{d(d+1)} = 1`
since either $`d` or $`d+1` is even.
:::

```lean "tau_pow_d_sq_eq_one"
lemma tau_pow_d2_one : τ d ^ d ^ 2 = 1 :=
  sorry
```
