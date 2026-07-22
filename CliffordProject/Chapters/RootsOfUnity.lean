import Verso
import VersoManual
import VersoBlueprint

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography

import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.RingTheory.RootsOfUnity.Complex
import CliffordProject.Tools.MatrixAlgebra


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
-- This instance is referred to later, needs naming
variable (d : ℕ) [hnezero : NeZero d]
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
noncomputable def ω : ℂˣ := .mk
  (Complex.exp (2 * Real.pi * Complex.I / d))
  (Complex.exp (- 2 * Real.pi * Complex.I / d))
  (by rw[<- Complex.exp_add]; simp; ring; rw[Complex.exp_zero])
  (by rw[<- Complex.exp_add]; simp; ring; rw[Complex.exp_zero])
```

Some basic lemmas about $`\omega`

:::lemma_ "omega_one" (parent := "roots_of_unity") (effort := "small") (owner := "William_Hasley")
When $`d = 1`, $`\omega = 1`
:::

```lean "omega_one"
@[simp]
lemma omega_one : (ω 1) = 1 := by
  ext; unfold ω; simp;

omit [NeZero d] in
@[simp]
lemma omega_one' (hd : d = 1) : ω d = 1 := by
  rw[hd]; simp
```

:::lemma_ "omega_inv_pow" (parent := "roots_of_unity") (effort := "small") (owner := "William_Hasley")
Let $`i ∈ ℤ_d`, then $`\left(\omega^{i}\right)^{-1} = \omega^{-i}`
:::

```lean "omega_inv_pow"
@[simp]
lemma omega_inv_pow (i : ZMod d) : ((ω d).val ^ i.val)⁻¹ = (ω d).val ^ (-i).val
  := by sorry;
```

:::lemma_ "omega_pow_d_eq_one" (parent := "roots_of_unity") (effort := "small") (owner := "Maris_Ozols")
$`ω^d = 1`.
:::

:::proof "omega_pow_d_eq_one"
$`ω^d = (\exp(2πi/d))^d = \exp(d(2πi/d)) = \exp(2πi) = 1` where we could cancel $`d` since $`d ≠ 0`.
:::

```lean "omega_pow_d_eq_one"
omit [NeZero d] in
@[simp]
lemma omega_pow_d_eq_one : (ω d)^d = 1 := by
  unfold ω; ext; simp
  rw [← Complex.exp_nat_mul]; by_cases hd : d = 0
  · rw[hd]; simp
  · ring_nf; calc
      Complex.exp (↑d * ↑Real.pi * Complex.I * (↑d)⁻¹ * 2) = Complex.exp (↑d * (↑d)⁻¹ * ↑Real.pi * Complex.I * 2)
        := by ring_nf
      _ = Complex.exp (↑Real.pi * Complex.I * 2)
        := by rw[Complex.mul_inv_cancel, one_mul]; simp; apply hd
      _ = 1 := by rw[mul_comm, <- mul_assoc, Complex.exp_two_pi_mul_I];

@[simp]
lemma omega_val_pow_d_eq_one : ((ω d).val) ^ d = 1 := by
  rw[<- Units.val_pow_eq_pow_val, omega_pow_d_eq_one]; simp
```

:::lemma_ "omega_star"
For $`z ∈ \mathbb{C}`, let $`z^*` denote the usual complex conjugate of $`z`. Then $`\omega^* = \omega^{-1}`
:::

```lean "omega_star"
omit [NeZero d] in
@[simp]
lemma omega_star : star ((ω d).val) = (ω d).val⁻¹
 := by rw[Complex.inv_def]; simp; unfold ω; simp;
        rw[<- Complex.sq_norm, Complex.norm_exp]; simp

omit [NeZero d] in
@[simp]
lemma omega_pow_star (i : ℕ) : star (((ω d).val) ^ i) = ((ω d).val ^ i)⁻¹
  := by simp;
```

```lean "order_omega"
lemma order_omega : orderOf (ω d) = d := by
  rw[orderOf_eq_iff]; apply And.intro; apply omega_pow_d_eq_one;
  intro m hm hm'; intro hAbs; rw[Units.ext_iff] at hAbs; simp at hAbs;
  unfold ω at hAbs; simp at hAbs; rw[<- Complex.exp_nsmul] at hAbs; simp at hAbs;
  rw[Complex.exp_eq_one_iff] at hAbs; obtain ⟨n, hn⟩ := hAbs;

  have calc_md : (m : ℝ) / (d : ℝ) = (n : ℂ) := by rw[mul_div_left_comm, mul_comm] at hn; simp at hn; apply hn
  have d_ge_zero : 0 < d := by apply Nat.zero_lt_of_ne_zero; apply hnezero.out;
  have ratio_between : (m : ℝ) / (d : ℝ) > 0 ∧ (m : ℝ) / d < 1 := by sorry; -- apply And.intro;
  simp at calc_md;
  --rw[calc_md] at ratio_between;
  sorry;
  apply Nat.zero_lt_of_ne_zero; apply hnezero.out
  -- apply d_ge_zero; rw[div_lt_one m d]

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

lemma omega_val_pow_n_mod_d :
  ∀ n : Nat, (ω d).val ^ n = (ω d).val ^ (n % d) := by
    intro n
    nth_rw 1 [←(Nat.mod_add_div n d)]
    rw [pow_add, pow_mul, omega_val_pow_d_eq_one,
      one_pow, mul_one]
```

```lean "omega_pow_k_mod_d_eq_pow_k_int"
lemma omega_pow_k_mod_d_eq_pow_k_int :
  ∀ k : ℤ, (ω d) ^ k = (ω d) ^ (k % d) := by
    intro k; --unfold ω; ext; simp
    nth_rw 1 [← (Int.emod_add_ediv_mul k d)]
    rw[zpow_add]; simp
    rw[mul_comm, zpow_mul]
    simp
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
noncomputable def τ : ℂˣ := .mk
  (- Complex.exp (Real.pi * Complex.I / d))
  (- Complex.exp (- Real.pi * Complex.I / d))
  (by simp; rw[<- Complex.exp_add]; ring; rw[Complex.exp_zero])
  (by simp; rw[<- Complex.exp_add]; ring; rw[Complex.exp_zero])
```

Some basic lemmas about $`\tau`

:::lemma_ "tau_star" (parent := "roots_of_unity") (effort := "small") (owner := "William_Hasley")
Much like $`\omega`, since $`τ` lies on the Unit circle, one has $`\tau^* = \tau^{-1}`
:::

```lean "tau_star"
lemma tau_star (d : ℕ) (n : ℤ) [NeZero d] :
    star (τ d ^ n)  = (τ d)^(-n) := by
  unfold τ; ext; simp; rw[← Complex.exp_conj]; simp;
  rw [← neg_one_mul, mul_zpow]; nth_rw 3 [← neg_one_mul]; rw[mul_zpow]; simp;
  rw [<- Complex.exp_int_mul, <- Complex.exp_int_mul, <- Complex.exp_neg];
  rw [mul_comm, ← neg_one_mul]; nth_rw 3 [← neg_one_mul]; sorry -- rw[Units.inv_pow_eq_pow_inv (-1) n]
```

:::lemma_ "tau_sq_eq_omega" (parent := "roots_of_unity") (effort := "small") (owner := "Christian_Schaffner")
$`τ^2 = ω`.
:::

:::proof "tau_sq_eq_omega"
$`τ^2 = (-\exp(πi/d))^2 = (-1)^2 · (\exp(πi/d))^2 = 1 · \exp(2πi/d) = ω`.
:::

```lean "tau_sq_eq_omega"
@[simp]
lemma tau_sq_eq_omega (d : ℕ) [NeZero d] : (τ d)^2 = ω d := by
  unfold τ ω; ext; simp; rw[<- Complex.exp_nsmul]; simp; rw[mul_assoc, <- mul_div_assoc];
```

:::lemma_ "tau_pow_d_eq_one_of_odd" (parent := "roots_of_unity") (effort := "small") (owner := "Carli_Bruinsma")
If $`d` is odd then $`τ^d = 1`.
:::

:::proof "tau_pow_d_eq_one_of_odd"
$`τ^d = (-\exp(πi/d))^d = (-1)^d · (\exp(πi/d))^d = (-1)^d · \exp(πi) = (-1)^d · (-1) = (-1)^{d+1} = 1` when $`d` is odd.
:::

```lean "tau_pow_d_eq_one_of_odd"
@[simp]
lemma tau_pow_d_eq_one_of_odd (hodd : Odd d) :
    (τ d)^d = 1 := by
    unfold τ; ext; simp; rw [← neg_one_mul, mul_pow, neg_one_pow_odd d hodd]
    rw[<- Complex.exp_nsmul]; simp;
    rw[mul_comm]; simp
    where
    neg_one_pow_odd : ∀ x : ℕ, Odd x → (((-1) : ℂ)) ^ x = (-1) :=
      by intro x hoddx; rw[neg_one_pow_eq_neg_one_iff_odd]; apply hoddx; norm_num
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
  unfold τ; ext; simp
  rw [← neg_one_mul]
  rw [pow_two]
  rw [mul_pow];
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

```lean "tau_pow_n_mod_d_of_d_odd"
lemma mod_d_nonneg (a : ℤ) : 0 ≤ a % ↑d := by
    apply Int.emod_nonneg
    exact Nat.cast_ne_zero.mpr (NeZero.ne d)

theorem tau_pow_n_mod_d_of_d_odd
    (n d : ℕ) (hodd : Odd d) [NeZero d] :
    τ d ^ n = τ d ^ (n % ↑d) :=
  pow_eq_pow_mod n (tau_pow_d_eq_one_of_odd d hodd)
```
