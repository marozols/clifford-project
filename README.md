# Clifford Project

This is an ongoing [Lean](https://lean-lang.org/) formalization of the structure theorem for the single-qudit Clifford group, restricted to the case where the dimension $d$ is an odd prime.
This formalization is based on Sections 2 and 3 of

> D. M. Appleby, *SIC-POVMs and the Extended Clifford Group*,
> [arXiv:quant-ph/0412001](https://arxiv.org/abs/quant-ph/0412001),
> [J. Math. Phys. **46**, 052107 (2005)](https://doi.org/10.1063/1.1896384)

[Here](https://marozols.github.io/clifford-project/) is the latest HTML version of the blueprint.

## Contributing

This project is part of the [Lean seminar](https://carli-b.github.io/lean-seminar/) at CWI and the University of Amsterdam, coordinated by [Maris Ozols](https://homepages.cwi.nl/~maris/) and [Carli Bruinsma](https://carli-b.github.io/).
All participants of the Lean seminar are welcome to contribute. Here is how to get started:

- **Get push access:** Share your GitHub username on our Zulip channel so you can be added as a collaborator and push to the repository.

- **First contribution:** Clone the repository and add your name to [CliffordProject/Authors.lean](CliffordProject/Authors.lean).

- **What to work on?** Browse the [HTML blueprint](https://marozols.github.io/clifford-project/), its [summary](https://marozols.github.io/clifford-project/Blueprint-Summary/) or [dependency graph](https://marozols.github.io/clifford-project/Dependency-Graph/) to find where to contribute.

- **Coordination:** Use our private Zulip channel to coordinate efforts and ask questions if you run into any problems.

- **Claim ownership:** Before you start working on an item, mark it as yours by adding the `(owner := "Your_Name")` tag to it in the blueprint. This prevents duplicate effort.

- **Natural language first:** Every item should have both a natural language statement and a Lean formalization. If you are formalizing a proof — even a very simple one — first make sure a natural language version exists, is complete, and easy to follow. Most simple lemmas in the blueprint do not yet have natural language proofs, so you will likely need to write one before you start formalizing it.

- **Change everything!** You are encouraged to modify everything — definitions, lemmas, and even the main theorems — both their natural language statements as well as Lean formalizations.

- **Adding new items:** Feel free to add new items as needed. While the overall proof has been pre-digested, adding well-chosen auxiliary lemmas can make formalization significantly easier. In particular, feel free to break down larger items (especially theorems) into sequences of smaller intermediate lemmas.

- **Keeping things building:** It is fine to leave `sorry`s in your contribution, but please make sure your code type-checks since every commit triggers a GitHub Action that regenerates the [HTML blueprint](https://marozols.github.io/clifford-project/). It is advisable to first [build the HTML locally](#building-the-html-site) to make sure your contribution does not break anything.

- **AI use:** This project could easily be auto-formalized with AI, but that is not our intention — the goal is to learn Lean. Please do the formalization by hand, using AI only for assistance if you get stuck.

## Overview

The formalization is organized into the following chapters (in [CliffordProject/Chapters/](CliffordProject/Chapters/)):

| Chapter | File | Summary |
|---------|------|---------|
| Roots of unity | [RootsOfUnity.lean](CliffordProject/Chapters/RootsOfUnity.lean) | Defines the primitive $d$-th roots of unity $ω = e^{2πi/d}$ and $τ = -e^{πi/d}$, and establishes basic facts about them. |
| Symplectic form | [SymplecticForm.lean](CliffordProject/Chapters/SymplecticForm.lean) | Introduces the symplectic inner product $\langle\mathbf{p},\mathbf{q}\rangle = p_2 q_1 - p_1 q_2$ on $ℤ_d^2$ and proves basic properties. |
| Pauli matrices | [Pauli.lean](CliffordProject/Chapters/Pauli.lean) | Defines the generalized single-qudit Pauli operators $X$ and $Z$ acting on $ℂ^d$ and derives their fundamental relations. |
| Displacement operators | [Displacement.lean](CliffordProject/Chapters/Displacement.lean) | Builds the displacement operators $D_{x,z} = τ^{xz} X^x Z^z$ from the Pauli matrices. They constitute the Pauli/Weyl–Heisenberg group. |
| Clifford group | [Clifford.lean](CliffordProject/Chapters/Clifford.lean) | Defines the Clifford group as the normalizer of the Pauli group. |
| Symplectic action | [SymplecticAction.lean](CliffordProject/Chapters/SymplecticAction.lean) | Shows that conjugation by a Clifford element induces an action on displacement operators via a matrix in $\mathrm{SL}(2, ℤ_d)$. |
| Weyl representation | [WeylRepresentation.lean](CliffordProject/Chapters/WeylRepresentation.lean) | Constructs the Weyl (metaplectic) representation, a group homomorphism $\mathrm{SL}(2, ℤ_d) \to U(d)$ whose image is the Clifford group. |
| Clifford group structure | [CliffordGroupStructure.lean](CliffordProject/Chapters/CliffordGroupStructure.lean) | Proves that the Clifford group $\mathrm{C}(d)$ is isomorphic to the semidirect product $\mathrm{SL}(2, ℤ_d) \ltimes ℤ_d^2$. |

## Verso Blueprint

This project uses [Verso Blueprint](https://github.com/leanprover/verso-blueprint), a Lean package for blueprints that is built upon [Verso](https://verso.lean-lang.org/), which allows one to interleave informal mathematical exposition with formal Lean proofs.
The top-level document is [CliffordProject/Blueprint.lean](CliffordProject/Blueprint.lean).

### Building the HTML site

Build and render the blueprint with:

```bash
./scripts/ci-pages.sh
```

This is equivalent to:

```bash
lake build CliffordProject
lake env lean --run CliffordProjectMain.lean --output _out/site
```

### Viewing it locally

The generated HTML is written to `_out/site/html-multi/`. Because the site uses absolute paths, it must be served via a local HTTP server rather than opened as plain files. Use Python's built-in server:

```bash
cd _out/site/html-multi
python3 -m http.server
```

Then open [http://127.0.0.1:8000/](http://127.0.0.1:8000/) in your browser.

## Dependencies

- [Mathlib4](https://github.com/leanprover-community/mathlib4) — the Lean mathematical library
- [Verso Blueprint](https://github.com/leanprover/verso-blueprint) — the blueprint document system