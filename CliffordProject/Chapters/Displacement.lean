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
  (x z : ℤ) : Matrix (ZMod d) (ZMod d) ℂ :=
  (τ d)^(x * z) • (X d)^(x % d).toNat * (Z d)^(z % d).toNat
```

Displacement operators behave nicely under complex conjugation, see Eq. (9) in {citet Appleby}[].

:::lemma_ "D_conj" (parent := "displacement_core") (effort := "small")  (owner := "Gina_Muuss")
For all $`x,z ∈ ℤ`,
$$`D_{x,z}^† = D_{-x,-z}`
where $`\dagger` denotes the conjugate transpose.
:::

```lean "D_conj"
lemma conjTranspose_D (x z : ℤ) :
    (D d x z).conjTranspose = D d (-x) (-z) :=
  sorry
```

Multiplication of displacement operators corresponds to adding their subscripts and introducing a phase given by the symplectic inner product, see Eq. (10) in {citet Appleby}[].

:::lemma_ "D_mul" (parent := "displacement_core") (effort := "small") (owner := "Daan_Planken")
For all $`\p, \q ∈ ℤ^2`,
$$`D_\p D_\q = τ^{\braket{\p,\q}} D_{\p+\q}`
where $`τ` is the root of unity from {uses "tau"}[] and $`\braket{\cdot,\cdot}` is the symplectic inner product from {uses "symplectic_inner_product"}[].
:::

```lean "D_mul"
-- Carli added this definition, I needed it in the proof of D_add_nsmul
-- Feel free to change it if necessary!
-- If you change it, you can also update my proof
lemma D_mul (p q : ℤ × ℤ) :
    (D d p.1 p.2) * (D d q.1 q.2) =
    τ d ^ symp p q •
    D d (p.1 + q.1) (p.2 + q.2) := by
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
lemma D_pow_nsmul (p : ℤ × ℤ) (n : ℕ) :
    D d p.1 p.2 ^ n = D d (n • p).1 (n • p).2 := by
  induction n with
  | zero =>
    rw [pow_zero, zero_smul]
    unfold D
    simp
  | succ n ih =>
    rw [pow_succ, ih]
    sorry
    -- rw [D_mul]
    -- simp [symp_smul_left, self_eq_zero]
```

If $`d` is odd, adding a multiple of $`d` to the index of a displacement operator does not change it, see Eq. (11) in {citet Appleby}[].

:::lemma_ "D_add_nsmul" (owner := "Carli_Bruinsma")
If $`d` is odd then $`D_{\p+d\q} = D_{\p}` for all $`\p, \q ∈ ℤ^2`.
:::

```lean "D_add_nsmul"
lemma D_add_nsmul (p q : ℤ × ℤ) (hodd : Odd d) :
    D d (p.1 + d * q.1) (p.2 + d * q.2)
    = D d p.1 p.2 :=
  have h : (D d (d * q).1 (d * q).2) = 1 := by
    unfold D
    norm_num
    rw [mul_assoc, zpow_mul, zpow_natCast,
    tau_pow_d_eq_one_of_odd d hodd, one_zpow, one_smul]
  calc D d (p.1 + d * q.1) (p.2 + d * q.2) =
    (1 : ℂ) • D d (p.1 + d * q.1) (p.2 + d * q.2) := by
        norm_num
    _ = ((1 : ℂ) ^ (p.2 * q.1 - p.1 * q.2))
      • D d (p.1 + d * q.1) (p.2 + d * q.2) := by
        rw [one_zpow]
    _ = ((τ d ^ (d : ℤ)) ^ (p.2 * q.1 - p.1 * q.2))
      • D d (p.1 + d * q.1) (p.2 + d * q.2) := by
        rw [zpow_natCast, tau_pow_d_eq_one_of_odd d hodd]
    _ = (τ d ^ (p.2 * (d * q.1) - p.1 * (d * q.2)))
      • D d (p.1 + d * q.1) (p.2 + d * q.2) := by
        rw [← zpow_mul, mul_sub, ← mul_assoc,
        mul_comm ↑d p.2, mul_assoc p.2,
        mul_comm ↑d (p.1 * q.2), mul_assoc p.1,
        mul_comm q.2]
    _ = (τ d ^ symp p ⟨d * q.1, d * q.2⟩)
      • D d (p.1 + d * q.1) (p.2 + d * q.2) := by
        simp [symp]
    _ = (D d p.1 p.2) * (D d (d * q).1 (d * q).2) := by
        simp
        rw [D_mul d p ⟨d * q.1, d * q.2⟩]
    _ = D d p.1 p.2 := by
        rw [h, mul_one]
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

lemma D_mod_d (p : ℤ × ℤ) (hodd : Odd d):
    D d p.1 p.2 = D d (p.1 % d) (p.2 % d) :=
    by calc
      D d p.1 p.2 =
      D d (p.1 % d + d * (p.1 / d))
        (p.2 % d + d * (p.2 / d))

      := by rw[EuclideanDomain.mod_add_div p.1];
            rw[EuclideanDomain.mod_add_div p.2]
    _ = D d (p.1 % d) (p.2 % d)
      := D_add_nsmul d (p.1 % d, p.2 % d)
          (p.1 / d, p.2 / d) hodd

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
lemma D_pow_d_eq_one (p : ℤ × ℤ) (hOdd : Odd d) :
    D d p.1 p.2 ^ d = 1 :=
    by rw [D_pow_nsmul]; calc
    D d (d • p).1 (d • p).2 =
       D d ((d • p).1 % d) ((d • p).2 % d)
    := D_mod_d d (d • p) hOdd
    _ = D d 0 ((d • p).2 % d)
    := by simp
    _ = D d 0 0
    := by simp
    _ = 1 := by unfold D; simp
```

Displacement operators with different $`\p` (modulo $`d`) are indeed different.

:::lemma_ "D_p_neq_D_q" (parent := "displacement_core") (effort := "medium") (owner := "Carli_Bruinsma")
Let $`\p,\q \in ℤ^2` and assume $`α,β ∈ ℂ` are both non-zero.
Then
$$`α D_\p = β D_\q`
if and only if $`\p \equiv \q \pmod{d}`.
:::

```lean "D_p_neq_D_q"
lemma D_p_neq_D_q
    (p q : ℤ × ℤ)
    (α β : ℂ) [NeZero α] [NeZero β] :
    α • (D d p.1 p.2) = β • (D d q.1 q.2) ↔
    (p.1 ≡ q.1 [ZMOD (d : ℤ)] ∧
    p.2 ≡ q.2 [ZMOD (d : ℤ)]) := by
  -- Probably not the correct statement yet!
  constructor
  · intro h
    let c1 : ℂ := α * τ d ^ (p.1 * p.2)
    let c2 : ℂ := β * τ d ^ (q.1 * q.2)
    have hc1 : c1 = α * τ d ^ (p.1 * p.2) := by rfl
    have hc2 : c2 = β * τ d ^ (q.1 * q.2) := by rfl
    let kq : ℤ := q.1 / d + 1
    let kp : ℤ := p.2 / d + 1
    let dif2 : ℕ := Int.toNat ((q.2 - q.1)  % d)
    have hc (c : ℤ) : 0 ≤ c % ↑d := by
        apply Int.emod_nonneg
        exact Nat.cast_ne_zero.mpr (NeZero.ne d)
    have h'' (a b : ℤ) :
        (a % d).toNat + (b % d).toNat =
        ((a + b) % d).toNat := by
      sorry
      --rw [← zpow_natCast, Int.toNat_of_nonneg h]
      --apply Int.toNat_of_nonneg


    have h' : c1 • X d ^ ((p.1 - q.1) % ↑d).toNat
        = c2 • (Z d ^ ((q.2 + -p.2) % ↑d).toNat) := by
      unfold D at h
      rw [← smul_mul_assoc, ← mul_smul,
      ← smul_mul_assoc, ← mul_smul, ← hc1, ← hc2] at h
      apply_fun (· * (Z d ^ (-p.2 % ↑d).toNat)) at h
      rw [mul_assoc, ← pow_add, h'', mul_assoc, ← pow_add,
      h'', ← sub_eq_add_neg] at h
      apply_fun ((X d ^ (-q.1 % ↑d).toNat) * ·) at h
      rw [smul_mul_assoc, mul_smul_comm, ← mul_assoc,
      ← pow_add, h'', add_comm, ← sub_eq_add_neg,
      smul_mul_assoc, mul_smul_comm, ← mul_assoc,
      ← pow_add, h'', add_comm, ← sub_eq_add_neg] at h
      rw [sub_self, Int.zero_emod, sub_self,
      Int.zero_emod] at h
      have koekje : Int.toNat 0 = (0 : ℕ) := by simp
      repeat rw [koekje] at h
      repeat rw [pow_zero] at h
      rw [mul_one, one_mul] at h
      exact h
    have hZ : Z d ^ ((q.2 + -p.2) % ↑d).toNat =
        Matrix.diagonal (fun (i : ZMod d) =>
        (ω d ^ (i.val * (((q.2 + -p.2) % ↑d).toNat)))) := by
      have hZ' : Z d = Matrix.diagonal
        (fun i : ZMod d => ω d ^ i.val) := by rfl
      rw [hZ', Matrix.diagonal_pow]
      simp
      intro i
      ring
    rw [hZ] at h'
    rw [X_pow_pos_n] at h'
    simp at h'
    have hentry : ∀ (i j : ZMod d),
        c1 * (if j + ↑((p.1 - q.1) % ↑d).toNat = i
        then (1 : ℂ) else 0) =
        if i = j
        then c2 * ω d ^ (i.val * ((q.2 + -p.2) % ↑d).toNat)
        else 0
    := by
      intro i j
      have := congr_fun (congr_fun h' i) j
      simp [Matrix.smul_apply, Matrix.of_apply,
      Matrix.diagonal_apply, smul_eq_mul] at this
      simp
      exact this
    have koek := hentry 1 1
    have koekje : c2 * ω d ^ ((ZMod.val (1 : ZMod d)) * ((q.2 + -p.2) % ↑d).toNat) ≠ 0 := by sorry
    simp at koek
    constructor
    · split_ifs at koek with blub
      · dsimp [Int.ModEq]
        apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr
        have hdvd := (ZMod.natCast_eq_zero_iff _ d).mp blub
        apply Int.emod_eq_zero_of_dvd
        have hnn : 0 ≤ (p.1 - q.1) % ↑d :=
          Int.emod_nonneg _ (by exact_mod_cast NeZero.ne d)
        have hlt : ((p.1 - q.1) % ↑d).toNat < d := by
          refine (Int.toNat_lt (hc (p.1 - q.1))).mpr ?_
          refine Int.emod_lt_of_pos (p.1 - q.1) ?_
          refine Int.natCast_pos.mpr ?_
          exact Nat.pos_of_neZero d
        have hzero : ((p.1 - q.1) % ↑d).toNat = 0 :=
          Nat.eq_zero_of_dvd_of_lt hdvd hlt
        apply Int.dvd_of_emod_eq_zero
        have h := Int.toNat_of_nonneg hnn
        rw [hzero, Nat.cast_zero] at h
        exact h.symm
      · symm at koek
        contradiction
    ·
  · sorry

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
