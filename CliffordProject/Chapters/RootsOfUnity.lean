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

:::lemma_ "d_invertible" (parent := "roots_of_unity") (effort := "small") (owner := "Maris_Ozols")
$`d` is invertible in $`ℂ`.
:::

:::proof "d_invertible"
The inverse of $`d` exists since $`d ∈ ℕ` and $`d ≠ 0`.
:::

```lean "d_invertible"
lemma d_invertible : IsUnit (d : ℂ) := by
  simp only [isUnit_iff_ne_zero, ne_eq, Nat.cast_eq_zero]
  exact NeZero.ne d
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

:::lemma_ "omega_pow_d_eq_one" (parent := "roots_of_unity") (effort := "small") (owner := "Maris_Ozols")
$`ω^d = 1`.
:::

:::proof "omega_pow_d_eq_one"
$`ω^d = (\exp(2πi/d))^d = \exp(d(2πi/d)) = \exp(2πi) = 1` where we could cancel $`d` since $`d ≠ 0`.
:::

```lean "omega_pow_d_eq_one"
lemma omega_pow_d_eq_one : (ω d)^d = 1 := by
  unfold ω
  rw [← Complex.exp_nat_mul]
  rw [IsUnit.mul_div_cancel]
  · exact Complex.exp_two_pi_mul_I
  · exact d_invertible d
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
lemma tau_sq_eq_omega : (τ d)^2 = ω d := by
  sorry
```

:::lemma_ "tau_pow_d_eq_one_of_odd" (parent := "roots_of_unity") (effort := "small") (owner := "Carli_Bruinsma")
If $`d` is odd then $`τ^d = 1`.
:::

:::proof "tau_pow_d_eq_one_of_odd"
$`τ^d = (-\exp(πi/d))^d = (-1)^d · (\exp(πi/d))^d = (-1)^d · \exp(πi) = (-1)^d · (-1) = (-1)^{d+1} = 1` when $`d` is odd.
:::

```lean "tau_pow_d_eq_one_of_odd"
lemma tau_pow_d_eq_one (hodd : Odd d) : (τ d)^d = 1 := by
  calc
    (-Complex.exp (↑Real.pi * Complex.I * (↑d)⁻¹)) ^ d
        = (-1 : ℂ)^d *
        Complex.exp (↑Real.pi *
        Complex.I * (↑d)⁻¹) ^ d := by
      rw [← mul_neg_one, mul_comm, mul_pow]
    _ = (-1 : ℂ)^d *
        Complex.exp (↑Real.pi *
        Complex.I * ↑d * (↑d)⁻¹) := by
      rw [← Complex.exp_nat_mul,
        ← mul_assoc, mul_comm (↑d) (↑Real.pi * Complex.I)]
    _ = (-1 : ℂ)^d *
        Complex.exp (↑Real.pi * Complex.I) := by
      rw [mul_assoc,
        mul_inv_cancel₀  (NeZero.natCast_ne d ℂ), mul_one]
    _ = (-1)^(d+1) := by
      rw [Complex.exp_pi_mul_I, Eq.symm (pow_succ (-1) d)]
    _ = 1 := by
      apply (neg_one_pow_eq_one_iff_even ?_).mpr
      · obtain ⟨k, hk⟩ := hodd
        unfold Even
        use (k + 1)
        rw [hk, mul_comm 2, Nat.mul_two,
         add_assoc k, add_comm k, ← add_assoc]
      · norm_num
```

:::lemma_ "tau_pow_d_sq_eq_one" (parent := "roots_of_unity") (effort := "small") (owner := "Maris_Ozols")
$`τ^{d^2} = 1`.
:::

:::proof "tau_pow_d_sq_eq_one"
$`τ^{d^2} = (-\exp(πi/d))^{d^2} = (-1)^{d^2} · (-1)^d = (-1)^{d(d+1)} = 1`
since either $`d` or $`d+1` is even.
:::

```lean "tau_pow_d_sq_eq_one"
lemma tau_pow_d2_one : (τ d) ^ (d ^ 2) = 1 := by
  unfold τ
  rw [← neg_one_mul]
  rw [pow_two]
  rw [mul_pow]
  rw [← Complex.exp_nat_mul]
  rw [Nat.cast_mul]
  rw [mul_assoc]
  rw [IsUnit.mul_div_cancel]
  rw [Complex.exp_nat_mul]
  rw [Complex.exp_pi_mul_I]
  rw [← pow_add]
  rw [← mul_add_one]
  rw [neg_one_pow_eq_one_iff_even]
  exact Nat.even_mul_succ_self d
  · norm_num
  · exact d_invertible d
```
