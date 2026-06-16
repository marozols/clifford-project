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
  (p : ZMod d × ZMod d) :
    ∃ f : ZMod d × ZMod d → ZMod d × ZMod d,
    ∃ g : ZMod d × ZMod d → ℝ,
    U * (D d p.1.val p.2.val) * U.val.conjTranspose
    = Complex.exp (Complex.I * g p)
    • (D d (f p).1.val (f p).2.val) :=
  sorry
```
