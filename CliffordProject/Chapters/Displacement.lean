import Verso
import VersoManual
import VersoBlueprint

import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.LinearAlgebra.UnitaryGroup


import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography
import CliffordProject.Chapters.RootsOfUnity
import CliffordProject.Chapters.Pauli
import CliffordProject.Chapters.SymplecticForm

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

#doc (Manual) "Displacement operators" =>

:::group "displacement_core"
Core properties of the single-qudit Pauli group.
:::

This section uses the generalized Pauli $`X` and $`Z` matrices to define the displacement operators $`D_{x,z}`.
These operators effectively constitute the generalized Pauli or Weyl–Heisenberg group on a single quantum system of dimension $`d`.
Unless stated otherwise, we assume that $`d ≥ 1`.

```lean "dimension_again2"
variable (d : ℕ) [NeZero d]
```

We use the generalized Pauli $`X` and $`Z` to define the displacement operators, see Eq. (8) in {citet Appleby}[].

:::definition "displacement" (parent := "displacement_core") (effort := "small") (owner := "Maris_Ozols")
The *displacement operator* corresponding to $`x,z ∈ ℤ` is defined as
$$`D_{x,z} = τ^{xz} X^x Z^z`
where $`τ` comes from {uses "tau"}[], $`X` comes from {uses "Pauli_X"}[], and $`Z` comes from {uses "Pauli_Z"}[].
:::

```lean "displacement"
noncomputable def D
  (x z : ZMod d) : Matrix (ZMod d) (ZMod d) ℂ :=
  (τ d)^(x.val * z.val) • (X d)^(x.val) * (Z d)^(z.val)
```

Displacement operators behave nicely under complex conjugation, see Eq. (9) in {citet Appleby}[].

:::lemma_ "D_conj" (parent := "displacement_core") (effort := "small")  (owner := "Gina_Muuss")
For all $`x,z ∈ ℤ`,
$$`D_{x,z}^† = D_{-x,-z}`
where $`\dagger` denotes the conjugate transpose.
:::

```lean "D_conj"
lemma conjTranspose_D (x z : ℤ) :
    (D d x z).conjTranspose = D d (-x) (-z) := by
  unfold D
  rw [smul_mul_assoc]
  rw [(X_pow_Z_pow_eq_omega_mul_Z_pow_X_pow d x z)]
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_smul]
  rw [X_inv_pow, Z_inv_pow]
  rw [smul_mul_assoc]
  #check (tau_star d (((x: ZMod d).val) * ((z: ZMod d).val)))
  #check zpow_natCast
  rw [← tau_sq_eq_omega]
  nth_rw 2 [star_pow]
  nth_rw 2 [pow_mul]
  have tau_star_nat
    (d : ℕ) (n : ℕ) [NeZero d] :
    star (τ d ^ n) = τ d^(-(n: ℤ)) := by
      have h := tau_star d (n : ℤ)
      rw [zpow_natCast] at h
      exact h
  rw [tau_star_nat, tau_star_nat]
  rw [← smul_assoc]
  -- This is a insane bodge, but this way lean can do the casts...
  have hh (z : ℂ ) (a: ℤ ) (b: ℕ ): z ^(a*b) = (z^a)^b  :=by
    exact zpow_mul z a b
  rw [← (hh (τ d) (-(2 : ℕ)) (-((x: ZMod d) * (z: ZMod d))).val)]
  rw [smul_eq_mul]
  rw [← pow_mul]
  congr
  nth_rw 3 [mul_comm]
  rw [Int.mul_neg, ← Nat.cast_mul]
  rw [← (zpow_add₀ (tau_ne_zero d))]
  #check ZMod.val_mul
  unfold τ
  sorry
  /-
  --rw [Matrix.conjTranspose_apply]
  --unfold Matrix.conjTranspose_mul

  --rw [Matrix.conjTranspose_mul]

  simp only [star_pow, star_neg, RCLike.star_def]
  --unfold τ

  --rw [starRingEnd_apply]
  #check starRingEnd
  #check star_pow
  #check star_neg
  --rw[star_neg]
  --simp only [RCLike.star_def]
  --simp only [RCLike.star_def, even_two, Even.neg_pow]
  rw[ ← Complex.exp_conj]
  #check neg_pow
  simp only [map_div₀, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, map_natCast]
  rw [neg_pow]
  rw [(neg_pow (Complex.exp (↑Real.pi * Complex.I / ↑d))
    ((-(x : ZMod d)).val * (-(z : ZMod d)).val))] -- Somehow here we have to specify....
  rw [← Complex.exp_nat_mul]
  rw [← Complex.exp_nat_mul]
  rw [ZMod.val_mul]
  #check neg_one_pow_congr

  --rw [← Complex.exp_nsmul,← Complex.exp_int_mul, ← Complex.exp_neg]
  #check neg_mul
--  rw [neg_smul, ← Complex.exp_int_mul,  ← Complex.exp_add]
-/
```

Multiplication of displacement operators corresponds to adding their subscripts and introducing a phase given by the symplectic inner product, see Eq. (10) in {citet Appleby}[].

:::lemma_ "D_mul" (parent := "displacement_core") (effort := "small") (owner := "Daan_Planken")
For all $`\p, \q ∈ ℤ^2`,
$$`D_\p D_\q = τ^{\braket{\p,\q}} D_{\p+\q}`
where $`τ` is the root of unity from {uses "tau"}[] and $`\braket{\cdot,\cdot}` is the symplectic inner product from {uses "symplectic_inner_product"}[].
:::

```lean "D_mul"
lemma D_mul (p q : ZMod d × ZMod d) :
    (D d p.1 p.2) * (D d q.1 q.2) =
    τ d ^ (symp p q).val •
    D d (p.1 + q.1) (p.2 + q.2) := by
      unfold D
      simp

      nth_rewrite 1 [← mul_assoc]
      nth_rewrite 2 [mul_assoc]

      rw [Z_pow_X_pow_eq_omega_mul_X_pow_Z_pow]
      simp
      rw [← mul_assoc]
      ring
      rw [← pow_add]
      have h2 : τ d ^ (q.1 * q.2) • τ d ^ (p.1 * p.2) • ω d ^ ((p.2 % ↑d).toNat * (q.1 % ↑d).toNat) • (X d ^ ((p.1 % ↑d).toNat + (q.1 % ↑d).toNat) * Z d ^ (p.2 % ↑d).toNat * Z d ^ (q.2 % ↑d).toNat) = (τ d ^ (q.1 * q.2) • τ d ^ (p.1 * p.2)) • ω d ^ ((p.2 % ↑d).toNat * (q.1 % ↑d).toNat) • (X d ^ ((p.1 % ↑d).toNat + (q.1 % ↑d).toNat) * (Z d ^ (p.2 % ↑d).toNat * Z d ^ (q.2 % ↑d).toNat)) := by
        ring
        apply?
      rw [h2]
      rw [← pow_add]
      ---have h4 : τ d ^ (q.1 * q.2) • τ d ^ (p.1 * p.2) • ω d ^ ((p.2 % ↑d).toNat * (q.1 % ↑d).toNat) • (X d ^ ((q.1 % ↑d).toNat + (p.1 % ↑d).toNat) * Z d ^ (p.2 % ↑d).toNat * Z d ^ (q.2 % ↑d).toNat) = τ d ^ (q.1 * q.2) • τ d ^ (p.1 * p.2) • ω d ^ ((p.2 % ↑d).toNat * (q.1 % ↑d).toNat) • (X d ^ ((q.1 % ↑d).toNat + (p.1 % ↑d).toNat) * Z d ^ (p.2 % ↑d).toNat * Z d ^ (q.2 % ↑d).toNat) := by
      have h4 : τ d ^ (q.1 * q.2) • τ d ^ (p.1 * p.2) • ω d ^ ((p.2 % ↑d).toNat * (q.1 % ↑d).toNat) • (X d ^ ((q.1 % ↑d).toNat + (p.1 % ↑d).toNat) * Z d ^ (p.2 % ↑d).toNat * Z d ^ (q.2 % ↑d).toNat) = (τ d ^ (q.1 * q.2) * τ d ^ (p.1 * p.2) * ω d ^ ((p.2 % ↑d).toNat * (q.1 % ↑d).toNat)) • (X d ^ ((q.1 % ↑d).toNat + (p.1 % ↑d).toNat) * Z d ^ (p.2 % ↑d).toNat * Z d ^ (q.2 % ↑d).toNat) := by
        ring
        sorry


```
The $`n`-th power of a displacement operator is again a displacement operator.

:::lemma_ "D_pow_nsmul" (parent := "displacement_core") (owner := "Joppe_Stokvis")
For all $`\p \in ℤ^2` and $`n \geq 0`,
$$`D_\p^n = D_{n\p}.`
:::

:::proof "D_pow_nsmul"
We proceed by induction on $`n`. The base case $`n = 0` gives $`D_\p^0 = I = D_\mathbf{0}`. For the inductive step, assuming $`D_\p^n = D_{n\p}` we get
$$`D_\p^{n+1} = D_\p^n · D_\p = D_{n\p} \cdot D_\p = \tau^{\langle n\p,\p\rangle} D_{(n+1)\p},`
where the last step used {uses "D_mul"}[].
The result follows since $`\langle n\p,\p\rangle = n \langle\p,\p\rangle = 0` thanks to {uses "self_eq_zero"}[].
:::

```lean "D_pow_nsmul"
lemma D_pow_nsmul (p : ZMod d × ZMod d) (n : ℕ) :
    D d p.1 p.2 ^ n = D d (n • p).1 (n • p).2 := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    unfold D
    simp
  | succ n ih =>
    rw [pow_succ, ih]
    rw [D_mul]
    have h : symp ( n • p) p = 0 := by
      unfold symp; simp; ring
    rw [h, ZMod.val_zero, pow_zero, one_smul]
    simp; ring


```


If $`d` is odd, adding a multiple of $`d` to the index of a displacement operator does not change it, see Eq. (11) in {citet Appleby}[].

:::lemma_ "D_add_nsmul" (owner := "Carli_Bruinsma")
If $`d` is odd then $`D_{\p+d\q} = D_{\p}` for all $`\p, \q ∈ ℤ^2`.
:::

```lean "D_add_nsmul"
lemma D_add_nsmul (p q : ZMod d × ZMod d) (hodd : Odd d) :
    D d (p.1 + d * q.1) (p.2 + d * q.2)
    = D d p.1 p.2 := by
  unfold D
  rw [ZMod.val_add, ZMod.val_mul, Nat.add_mod,
    ZMod.val_natCast, Nat.mod_self, zero_mul,
    Nat.zero_mod, Nat.zero_mod, add_zero, Nat.mod_mod,
    ZMod.val_add, ZMod.val_mul, Nat.add_mod,
    ZMod.val_natCast, Nat.mod_self, zero_mul,
    Nat.zero_mod, Nat.zero_mod, add_zero, Nat.mod_mod,
    tau_pow_n_mod_d_of_d_odd, ← Nat.mul_mod,
    ← tau_pow_n_mod_d_of_d_odd,
   ← X_pow_n_mod_d, ← Z_pow_n_mod_d]
  <;> exact hodd -- for tau_pow_n_mod_d_of_d_odd
```

If $`d` is odd, the index $`\p` of a displacement operator $`D_\p` can be treated modulo $`d`.
In other words, it makes sense to write $`\p \in ℤ_d^2`.

:::lemma_ "D_mod_d" (parent := "displacement_core") (effort := "small") (owner := "William_Hasley")
If $`d` is odd, then for all $`\p \in ℤ^2`,
$$`D_\p = D_{\p \pmod d}.`
:::

:::proof "D_mod_d"
This is a direct consequence of {uses "D_add_nsmul"}[]
:::

```lean "D_mod_d"
@[default_instance]
instance : EuclideanDomain ℤ := Int.euclideanDomain

lemma D_mod_d (p : ZMod d × ZMod d) (hodd : Odd d):
    D d p.1 p.2 = D d p.1 p.2 :=
    sorry
    /-
    by calc
      D d p.1 p.2 =
      D d (p.1 % d + d * (p.1 / d))
        (p.2 % d + d * (p.2 / d))

      := by rw[EuclideanDomain.mod_add_div p.1];
            rw[EuclideanDomain.mod_add_div p.2]
    _ = D d (p.1 % d) (p.2 % d)
      := D_add_nsmul d (p.1 % d, p.2 % d)
          (p.1 / d, p.2 / d) hodd
    -/
```


The displacement operators have order $`d`.

:::lemma_ "D_pow_d_eq_one" (parent := "displacement_core") (effort := "small") (owner := "William_Hasley")
If $`d` is odd, then for all $`\p \in ℤ^2`,
$$`D_\p^d = I.`
:::

:::proof "D_pow_d_eq_one"
By {uses "D_pow_nsmul"}[], $`D_\p^d = D_{d\p} = D_\mathbf{0} = I`, using $`d\p = \mathbf{0}` in $`ℤ_d^2`.
:::

```lean "D_pow_d_eq_one"
lemma D_pow_d_eq_one (p : ZMod d × ZMod d) (hOdd : Odd d) :
    D d p.1 p.2 ^ d = 1 :=
    by sorry

    /-rw [D_pow_nsmul]; calc
    D d (d • p).1 (d • p).2 =
       D d ((d • p).1 % d) ((d • p).2 % d)
    := D_mod_d d (d • p) hOdd
    _ = D d 0 ((d • p).2 % d)
    := by simp
    _ = D d 0 0
    := by simp
    _ = 1 := by unfold D; simp
    -/
```

Displacement operators with different $`\p` (modulo $`d`) are indeed different.

:::lemma_ "D_p_neq_D_q" (parent := "displacement_core") (effort := "medium") (owner := "Carli_Bruinsma")
Let $`\p,\q \in ℤ^2` and assume $`α,β ∈ ℂ` are both non-zero.
If
$$`α D_\p = β D_\q`
then $`\p \equiv \q \pmod{d}`.
:::

:::proof "D_p_neq_D_q"
This theorem always holds when $`d = 1`.
For $`d > 1`, (to be continues... from the assumption, you work out the matrices, take the diagonal entries at 0 and 1, and find your proof)
:::

```lean "D_p_neq_D_q"
lemma D_p_neq_D_q
    (p q : ZMod d × ZMod d)
    (α β : ℂ) [NeZero α] [NeZero β] :
    α • (D d p.1 p.2) = β • (D d q.1 q.2) →
    p.1 = q.1 ∧ p.2 = q.2 := by
  unfold D
  intro h
  by_cases hd : d = 1
  · subst d
    exact ⟨Subsingleton.elim p.1 q.1,
      Subsingleton.elim p.2 q.2⟩
  · rw [← smul_mul_assoc, ← mul_smul,
      ← smul_mul_assoc, ← mul_smul] at h
    apply_fun (· * (Z d ^ (-p.2).val)) at h
    rw [mul_assoc, ← pow_add, Z_pow_n_mod_d,
      ← ZMod.val_add, ← sub_eq_add_neg, sub_self,
      ZMod.val_zero, pow_zero, mul_one, mul_assoc,
      ← pow_add, Z_pow_n_mod_d, ← ZMod.val_add,
      ← sub_eq_add_neg] at h
    apply_fun (X d ^ (-q.1).val * · ) at h
    rw [mul_smul_comm, smul_mul_assoc, mul_smul_comm,
      ← mul_assoc, ← pow_add, X_pow_n_mod_d,
      ← ZMod.val_add, add_comm, ← sub_eq_add_neg,
      ← pow_add, X_pow_n_mod_d d ((-q.1).val + q.1.val),
      ← ZMod.val_add, add_comm, ← sub_eq_add_neg,
      sub_self, ZMod.val_zero, pow_zero, one_mul] at h
    apply Matrix.ext_iff.mpr at h
    rw [X_pow_pos_n, Z_pow_n, ZMod.natCast_val] at h
    have hphase := h 0 0
    rw [Matrix.smul_apply, Matrix.smul_apply,
      Matrix.diagonal_apply, if_pos rfl, ZMod.val_zero,
      zero_mul, pow_zero, smul_eq_mul, smul_eq_mul, mul_one,
      Matrix.of_apply, zero_add, ZMod.cast_id] at hphase
    have h1 : p.1 - q.1 = 0 := by
      by_contra h1'
      rw [if_neg h1', mul_zero] at hphase
      have h_false := (mul_ne_zero
          (NeZero.ne β) (pow_ne_zero
          (q.1.val * q.2.val) (tau_ne_zero d))).symm
      contradiction
    constructor
    · apply_fun ( · -q.1) using sub_left_injective
      dsimp only
      rw [sub_self]
      exact h1
    · rw [if_pos h1, mul_one] at hphase
      specialize h 1 1
      rw [h1, Matrix.smul_apply, Matrix.smul_apply,
        Matrix.of_apply, Matrix.diagonal_apply,
        ← hphase, ZMod.cast_zero, add_zero, if_pos rfl,
        if_pos rfl, smul_eq_mul, smul_eq_mul, mul_one,
        ZMod.val_one''
          (Ne.symm (Ne.intro fun a => hd (id (Eq.symm a)))),
        one_mul] at h
      apply_fun
        ((α * τ d ^ (p.1.val * p.2.val))⁻¹ * · ) at h
      have c1 : (α * τ d ^ (p.1.val * p.2.val)) ≠ 0 :=
        mul_ne_zero (NeZero.ne α)
        (pow_ne_zero _ (tau_ne_zero d))
      have c2 : 2 * ↑Real.pi * Complex.I ≠ (0 : ℂ)
          := by norm_num
      have c3 : 2 * ↑Real.pi * Complex.I / ↑d ≠ (0 : ℂ)
          := by
        apply Complex.normSq_pos.mp
        norm_num
        exact (NeZero.ne d)
      rw [mul_comm, ← mul_assoc, Complex.mul_inv_cancel c1,
        mul_comm ((α * τ d ^ (p.1.val * p.2.val))⁻¹),
        Complex.mul_inv_cancel c1, one_mul] at h
      unfold ω at h
      symm at h
      rw [← Complex.exp_nat_mul] at h
      apply Complex.exp_eq_one_iff.mp at h
      obtain ⟨n, hn⟩ := h
      apply_fun
        (· * (2 * ↑Real.pi * Complex.I / ↑d)⁻¹) at hn
      rw [mul_assoc, Complex.mul_inv_cancel c3, mul_one,
        div_eq_mul_inv, mul_inv, inv_inv, mul_assoc,
        ← mul_assoc ((2 * ↑Real.pi * Complex.I)),
        Complex.mul_inv_cancel c2, one_mul] at hn
      have hn_int : ((q.2 - p.2).val : ℤ) = n * d := by
        exact_mod_cast hn
      have hd : 0 < (↑d : ℤ) :=
        Int.natCast_pos.mpr (NeZero.pos d)
      have h_ub : n ≤ 0 := by -- n * ↑d < d := by
        rw [← sub_self 1]
        apply Int.le_sub_one_of_lt
        apply (mul_lt_iff_lt_one_left hd).mp
        rw [← hn_int]
        exact Int.ofNat_lt.mpr (ZMod.val_lt (q.2 - p.2))
      have h_lb : 0 ≤ n * ↑d := by
        rw [← hn_int]
        apply Int.natCast_nonneg
      have h_lb := Int.nonneg_of_mul_nonneg_left h_lb hd
      rw [le_antisymm h_ub h_lb, zero_mul] at hn_int
      have h2 : q.2 - p.2 = 0 :=
        (ZMod.val_eq_zero (q.2 - p.2)).mp
        (Int.ofNat_eq_zero.mp hn_int)
      apply_fun (· +p.2) at h2
      rw [sub_add, sub_self, sub_zero, zero_add] at h2
      exact h2.symm
```

Displacement operators with phases that are arbitrary powers of $`τ` form a group.

:::definition "Pauli_group" (parent := "displacement_core") (owner := "William_Hasley")
The *generalized Pauli group* or *discrete Weyl–Heisenberg group* consists of
$$`\GP(d) = \{τ^a D_\p : a ∈ ℤ_d, \p ∈ ℤ_d^2\}`
where $`τ` is from {uses "tau"}[] and $`D_\p` is from {uses "displacement"}[].
:::

```lean "Pauli_group"
def pauliGroup (d : ℕ) [NeZero d] :
    Subgroup (Matrix.unitaryGroup (ZMod d) ℂ) where
  carrier := {U | ∃ (a : ZMod d) (p : ZMod d × ZMod d),
    (U : Matrix (ZMod d) (ZMod d) ℂ) =
      (τ d) ^ a.val • D d (p.1.val : ℤ) (p.2.val : ℤ)}

  one_mem' := by use 0; use (0,0); simp; unfold D; simp
  mul_mem' := @fun A B A' B' => sorry -- Need 5.30
  inv_mem' := sorry


```

We could have equivalently written
$$`\GP(d) = \{τ^a X^x Z^z : a,x,z ∈ ℤ_d\}`
where $`X` and $`Z` are the generalized Pauli matrices.
The generalized Pauli group $`\GP(d)` modulo its center $`\{\tau^a I : a \in \Z_d\}` is isomorphic to $`ℤ_d^2`.
