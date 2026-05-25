import Verso
import VersoManual
import VersoBlueprint

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

#doc (Manual) "Clifford group structure" =>

:::group "Structure_core"
Structure of the Clifford group.
:::

Let us define the semidirect product of $`\SL(2,ℤ_d)` and $`ℤ_d^2`.

:::definition "semidirect_product" (parent := "Structure_core")
The *semidirect product* $`\SL(2,ℤ_d) \ltimes ℤ_d^2` consists of pairs $`(F, \bchi) \in \SL(2,ℤ_d) \times ℤ_d^2` with composition given by
$$`(F_1, \bchi_1) \cdot (F_2, \bchi_2) = (F_1 F_2,\, \bchi_1 + F_1 \bchi_2).`
:::

The main result of our formalization is the following theorem that describes the structure of the Clifford group in dimension $`d` that is an odd prime.
It corresponds to Theorem 1 in {citet Appleby}[].

:::theorem "Clifford_group_structure" (parent := "Structure_core") (effort := "large")
Let $`d` be an odd prime.
Let $`\mathrm{I}(d) = \{ e^{i\theta} I : \theta \in \mathbb{R} \}` be the subgroup of $`\Cliff(d)` from {uses "Clifford_group"}[] consisting of all scalar multiples of the identity.
There exists a unique group isomorphism
$$`f \colon \SL(2,ℤ_d) \ltimes ℤ_d^2 \to \Cliff(d)/\mathrm{I}(d)`
such that for each $`U` in the coset $`f(F, \bchi)` and all $`\p \in ℤ^2`,
$$`U D_{\p} U^\dagger = \omega^{\langle \bchi, F\p \rangle} D_{F\p}`
where $`\omega` is the $`d`-th root of unity from {uses "omega"}[], $`D_\p` is the displacement operator from {uses "displacement"}[], and $`\braket{\cdot,\cdot}` is the symplectic inner product from {uses "symplectic_inner_product"}[].
:::

This theorem allows us to compute the size of the Clifford group, see Lemma 5 in {citet Appleby}[].

:::lemma_ "Clifford_group_size" (parent := "Structure_core") (effort := "medium")
If $`d` is an odd prime then
$$`|\Cliff(d)/\mathrm{I}(d)| = d^3 (d^2 - 1).`
:::
