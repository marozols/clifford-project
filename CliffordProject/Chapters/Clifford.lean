import Verso
import VersoManual
import VersoBlueprint


import Mathlib.Algebra.Group.Subgroup.Defs

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography
import CliffordProject.Chapters.Displacement

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Clifford group" =>

:::group "Clifford_core"
Definition of the Clifford group.
:::

Clifford group is defined as the normalizer of the Pauli group.
Here we assume that $`d ≥ 1`.

:::definition "Clifford_group" (parent := "Clifford_core") (effort := "medium") (owner := "Maris_Ozols")
The *Clifford group* $`\Cliff(d)` consists of all $`d × d` unitaries $`U` such that
$$`U \GP(d) U^† = \GP(d),`
i.e., it is the _normalizer_ of the Generalized Pauli group $`\GP(d)`, see {uses "Pauli_group"}[].
:::

```lean "Clifford_group"
def cliffordGroup (d : ℕ) [NeZero d] :=
  Subgroup.normalizer (pauliGroup d).carrier
```

Note that according to this definition the Clifford group is infinite since $`U ∈ \Cliff(d)` implies that $`e^{i \varphi} U ∈ \Cliff(d)` for all $`\varphi ∈ ℝ`.
To get a finite group we need to mod out the center of $`\Cliff(d)` which consists of all $`e^{i\varphi} I` where $`\varphi ∈ ℝ`.

The following lemma gives a slightly more explicit description of how Clifford group elements act on displacement operators under conjugation.

:::lemma_ "Clifford_group_action" (parent := "Clifford_core") (effort := "medium") (owner := "Maris_Ozols")
For each Clifford unitary $`U ∈ \Cliff(d)` (see {uses "Clifford_group"}[]) there exist functions $`f: ℤ_d^2 → ℤ_d^2` and $`g: ℤ_d^2 → ℝ` such that
$$`U D_\p U^† = e^{i g(\p)} D_{f(\p)}`
for all $`\p ∈ ℤ_d^2`.
:::

```lean "Clifford_group_action"
lemma cliffordGroupAction (d : ℕ) [NeZero d]
  (U : Matrix.unitaryGroup (ZMod d) ℂ)
  (hU : U ∈ cliffordGroup d)
  (p : ℤ × ℤ) :
    ∃ f : ℤ × ℤ → ℤ × ℤ,
    ∃ g : ℤ × ℤ → ℝ,
    U * (D d p) * U.val.conjTranspose
    = Complex.exp (Complex.I * g p)
    • (D d (f p)) := by
  sorry
      /-
  have hD : (D d p.1 p.2) ∈ Matrix.unitaryGroup (ZMod d) ℂ
      := by
    unfold Matrix.unitaryGroup
    unfold unitary
    simp
    constructor
    · rw [Matrix.star_eq_conjTranspose,
      conjTranspose_D, D_mul d ⟨-p.1, -p.2⟩]
      unfold symp
      ring
      unfold D
      rw [ZMod.val_zero, pow_zero, one_smul, one_smul,
        pow_zero, pow_zero, mul_one]
    · rw [Matrix.star_eq_conjTranspose,
      conjTranspose_D, D_mul d ⟨p.1, p.2⟩ ⟨-p.1, -p.2⟩]
      unfold symp
      ring
      unfold D
      rw [ZMod.val_zero, pow_zero, one_smul, one_smul,
        pow_zero, pow_zero, mul_one]
  have hD' : ⟨D d p.1 p.2, hD⟩ ∈ pauliGroup d := by
    unfold pauliGroup
    simp
    unfold D
    use 0
    use p.1
    use p.2
    rw [ZMod.val_zero, pow_zero, one_smul]
  unfold cliffordGroup at hU
  unfold Subgroup.normalizer at hU
  simp at hU
  specialize hU (D d p.1 p.2) hD
  obtain ⟨g, hg⟩ := hU.mp hD'
  simp at hg
  simp
  rw [Matrix.star_eq_conjTranspose] at hg
  obtain ⟨a, ⟨b, hb⟩⟩ := hg
  unfold τ at hb
  rw [neg_eq_neg_one_mul, ← Complex.exp_pi_mul_I,
  ← Complex.exp_add, mul_div_assoc, ← mul_add] at hb
  nth_rewrite 1 [← mul_one Complex.I] at hb
  rw [div_eq_mul_inv, ← mul_add, ← Complex.exp_nat_mul,
    ← mul_assoc (↑Real.pi : ℂ), ← mul_assoc, ← mul_assoc,
    mul_comm (↑g.val * ↑Real.pi : ℂ),
    mul_assoc Complex.I] at hb
  use fun _ ↦ ⟨a, b⟩
  dsimp
  use fun _ ↦ ↑g.val * ↑Real.pi * (1 + (↑d)⁻¹)
  rw [hb]
  dsimp
  have horrible_casting_situation :
      (↑((↑g.val : ℝ) * Real.pi * (1 + (↑d : ℝ)⁻¹)) : ℂ)
      = (↑g.val : ℂ) * (↑Real.pi : ℂ) * (1 + (↑d : ℂ)⁻¹)
    := by
    rw [← Complex.ofReal_natCast d]
    norm_cast
  rw [horrible_casting_situation]
  -/

```
