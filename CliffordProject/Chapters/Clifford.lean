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
The *Clifford group* $`\Cliff(d)` consists of all $`d × d` unitaries $`U` for which there exist functions $`f: ℤ_d^2 → ℤ_d^2` and $`g: ℤ_d^2 → ℝ` such that
$$`U D_\p U^† = e^{i g(\p)} D_{f(\p)}`
for all $`\p ∈ ℤ_d^2`.
The displacement operators $`D_\p` are defined in {uses "displacement"}[].
:::

The Lean code below differs from the above since it defines the Clifford group as the normalizer of the Pauli group by using built-in Mathlib constructs.

```lean "Clifford_group"
def cliffordGroup (d : ℕ) [NeZero d] :=
  Subgroup.normalizer (pauliGroup d).carrier
```

Note that according to this definition the Clifford group is infinite since $`U ∈ \Cliff(d)` implies that $`e^{i \varphi} U ∈ \Cliff(d)` for all $`\varphi ∈ ℝ`.
To get a finite group we need to mod out the center of $`\Cliff(d)` which consists of all $`e^{i\varphi} I` where $`\varphi ∈ ℝ`.
