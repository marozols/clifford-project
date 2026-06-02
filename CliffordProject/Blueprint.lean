import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary

import CliffordProject.LaTeXMacros
import CliffordProject.Authors
import CliffordProject.Bibliography
import CliffordProject.Chapters.RootsOfUnity
import CliffordProject.Chapters.SymplecticForm
import CliffordProject.Chapters.Pauli
import CliffordProject.Chapters.Displacement
import CliffordProject.Chapters.Clifford
import CliffordProject.Chapters.SymplecticAction
import CliffordProject.Chapters.WeylRepresentation
import CliffordProject.Chapters.CliffordGroupStructure

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

#doc (Manual) "Clifford project" =>

This is a blueprint for the *[Clifford project](https://github.com/marozols/clifford-project)* whose goal is to formalize the structure theorem of the single-qudit Clifford group based on {citet Appleby}[].
This formalization is work in progress and is done by participants of the
[Lean seminar](https://carli-b.github.io/lean-seminar/)
at the University of Amsterdam.

# Overview

This document formalizes a standard result in quantum computing that characterizes the structure of the Clifford group.
For simplicity, we focus only on the case of a single system (qudit) and we assume that its dimension $`d` is an odd prime.
If we have time, we might later generalize this formalization to odd $`d` or even to an arbitrary $`d ≥ 1`.
This formalization is based on Sections 2 and 3 of {citet Appleby}[].

The project is organized into the following chapters:

* *Roots of unity* — Defines the primitive $`d`-th roots of unity $`ω = e^{2πi/d}` and $`τ = -e^{πi/d}`, and establishes basic facts about them.
* *Symplectic form* — Introduces the symplectic inner product $`\braket{\p,\q} = p_2 q_1 - p_1 q_2` on $`ℤ_d^2` and proves some basic properties.
* *Pauli matrices* — Defines the generalized single-qudit Pauli operators $`X` and $`Z` acting on $`ℂ^d` and derives their fundamental relations.
* *Displacement operators* — Builds the displacement operators $`D_{x,z} = τ^{xz} X^x Z^z` from $`X` and $`Z`, and shows their basic properties. They constitute the Pauli group.
* *Clifford group* — Defines the Clifford group $`\Cliff(d)` as the normalizer of the Pauli group, i.e. all $`d × d` unitaries that conjugate displacement operators to scalar multiples of displacement operators.
* *Symplectic action* — Shows that conjugation by a Clifford element induces an action on displacement operators via a matrix in $`\SL(2,ℤ_d)`.
* *Weyl representation* — Constructs the Weyl (or metaplectic) representation, a group homomorphism $`\SL(2,ℤ_d) → \U(d)` whose image is the Clifford group.
* *Clifford group structure* — Proves the main structure theorem: the Clifford group $`\Cliff(d)` (modulo phases) is isomorphic to the semidirect product $`\SL(2,ℤ_d) \ltimes ℤ_d^2`.

{include 0 CliffordProject.Chapters.RootsOfUnity}
{include 0 CliffordProject.Chapters.SymplecticForm}
{include 0 CliffordProject.Chapters.Pauli}
{include 0 CliffordProject.Chapters.Displacement}
{include 0 CliffordProject.Chapters.Clifford}
{include 0 CliffordProject.Chapters.SymplecticAction}
{include 0 CliffordProject.Chapters.WeylRepresentation}
{include 0 CliffordProject.Chapters.CliffordGroupStructure}

{blueprint_graph}
{blueprint_summary}
{blueprint_bibliography}
