import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.RingTheory.RootsOfUnity.Complex

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

:::lemma_ "omega_ne_zero" (parent := "roots_of_unity") (effort := "small") (owner := "Carli_Bruinsma")
$`ω ≠ 0`.
:::

```lean "omega_ne_zero"
omit [NeZero d] in
lemma omega_ne_zero : ω d ≠ 0 := by
  exact Complex.exp_ne_zero (2 * ↑Real.pi * Complex.I / ↑d)
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

```lean "order_omega"
lemma order_omega : orderOf (ω d) = d := by
  refine orderOf_eq_of_pow_and_pow_div_prime ?_ ?_ ?_
  exact Nat.pos_of_neZero d
  exact omega_pow_d_eq_one d
  intro p hp hpdivd
  unfold ω
  rw [← Complex.exp_nat_mul]
  rw [(Nat.cast_div hpdivd (Nat.cast_ne_zero.2 (Nat.Prime.ne_zero hp)))]
  rw [div_mul_div_comm]
  nth_rw 4 [mul_comm]
  rw [← div_mul_div_comm]
  --#check div_self (Nat.cast_ne_zero.2 (NeZero.ne d))
  --rw [div_self, one_mul]
  rw [← (Nat.cast_div (dvd_refl d) (Nat.cast_ne_zero.2 (NeZero.ne d)))]
  simp only [dvd_refl, Nat.cast_div_charZero, div_self_of_invertible, one_mul, ne_eq]
  rw [← mul_one (2*Real.pi*Complex.I)]
  nth_rw 1 [← (Nat.cast_one (R:= ℂ )) ]
  by_contra hfalse
  exact ((Nat.Prime.not_dvd_one hp) (((Complex.exp_two_pi_mul_I_mul_div_eq_one_iff (Nat.Prime.ne_zero hp)).1 ) hfalse))

```

This is an additional corrolary that is nice to have.

:::lemma_ "omega_pow_n_mod_d" (parent := "roots_of_unity") (effort := "small") (owner := "Gina_Muuss")
$`ω^n = ω^{n \mod d}`.
:::

```lean "omega_pow_n_mod_d"
lemma omega_pow_n_mod_d :
  ∀ n : Nat, (ω d) ^ n = (ω d) ^ (n % d) := by
    intro n
    nth_rw 1 [←(Nat.mod_add_div n d)]
    rw [pow_add, pow_mul, omega_pow_d_eq_one,
      one_pow, mul_one]
```

```lean "omega_pow_k_mod_d_eq_pow_k_int"
lemma omega_pow_k_mod_d_eq_pow_k_int :
  ∀ k : Int, (ω d) ^ k = (ω d) ^ (k % d) := by
    intro k
    nth_rw 1 [← (Int.emod_add_ediv_mul k d)]
    rw [zpow_add']
    nth_rw 2 [mul_comm]
    rw [zpow_mul]
    rw [zpow_natCast]
    rw [omega_pow_d_eq_one, one_zpow, mul_one]
    apply Or.inl
    unfold ω
    apply Complex.exp_ne_zero
```

```lean "omega_pow_k_mod_d_eq_pow_k_zmod"
lemma omega_pow_k_mod_d_eq_pow_k_zmod :
  ∀ k : Int, (ω d) ^ k = (ω d) ^ (k : ZMod d).val := by
    intro k
    rw [omega_pow_k_mod_d_eq_pow_k_int]
    rw [(Eq.symm (ZMod.val_intCast k))]
    exact zpow_natCast (ω d) (k : ZMod d).val
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
lemma tau_pow_d_eq_one_of_odd (hodd : Odd d) :
    (τ d)^d = 1 := by
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

:::lemma_ "tau_ne_zero" (parent := "roots_of_unity") (effort := "small") (owner := "Carli_Bruinsma")
$`τ ≠ 0`.
:::

```lean "tau_ne_zero"
omit [NeZero d] in
lemma tau_ne_zero : τ d ≠ 0 := by
  unfold τ
  apply neg_ne_zero.mp
  rw [neg_neg]
  exact Complex.exp_ne_zero (↑Real.pi * Complex.I / ↑d)
```

```lean "zero_le_c_mod_d"
lemma mod_d_nonneg (a : ℤ) : 0 ≤ a % ↑d := by
    apply Int.emod_nonneg
    exact Nat.cast_ne_zero.mpr (NeZero.ne d)
```
:::lemma_ "tau_pow_n_mod_d_odd" (parent := "roots_of_unity") (effort := "small") (owner := "Carli_Bruinsma")
If $`d` is odd then $`τ^{n} = τ^{n \mod d}`.
:::

```lean "tau_pow_n_mod_d_odd"
theorem tau_pow_n_mod_d_of_d_odd
    (n d : ℕ) (hodd : Odd d) [NeZero d] :
    τ d ^ n = τ d ^ (n % ↑d) :=
  pow_eq_pow_mod n (tau_pow_d_eq_one_of_odd d hodd)
```


```lean "tau_star"
theorem tau_star
    (d : ℕ) (n : ℤ) [NeZero d] :
    star (τ d ^ n)  = τ d^(-n) := by
  unfold τ
  rw [star_zpow₀, star_neg, RCLike.star_def, ← Complex.exp_conj]
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, map_natCast, neg_inj]
  by_cases h : Even n
  . rw [h.neg_zpow,  (even_neg.2 h).neg_zpow]
    rw [← Complex.exp_int_mul, ← Complex.exp_int_mul]
    rw [Int.cast_neg]
    ring_nf
  apply Int.not_even_iff_odd.1 at h
  rw [h.neg_zpow, (odd_neg.2 h).neg_zpow]
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul]
  rw [Int.cast_neg]
  ring_nf
```
