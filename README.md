# Catt-formalization
An agda prototype formalization of the [CaTT type theory](https://github.com/ThiBen/catt).

 The theory is presented in a cut-free style, without axiom K, introducing a pre-syntax and inference rules on it. All lemmas usually admitted are checked formally by induction on derivation trees.

 The development was compiled with Agda version 2.6.3

## The type theory CaTT
CaTT is the dependent type theory that describes coherences for weak omega-categories. The theory is described in a less formal way in this [short article](https://arxiv.org/abs/1706.02866) or in this [longer article](https://arxiv.org/abs/2106.04475). The formalization in this repository is presented in the [following article](https://arxiv.org/abs/2111.14736). The exact state of the project corresponding to the above article is kept in the branch [TYPES2021](https://github.com/thibautbenjamin/catt-formalization/tree/TYPES2021).

## Globular Type Theories
A general framework for studying type theories over globular sets. These type theories all share in common their type constructors and type introduction rules, but term constructors can be arbitrarily complex. The initial globular type theory is GSeTT, it has just variables and no term constructors. This theory is defined and studied first independently, and general notion of globular type theory is then defined, as a theory whose term constructors can be arbitrary, and whose term introduction rules are parametrized by judgments in the theory GSeTT.


## Structure of the Code
* `GSeTT/` - The type theory for globular sets
  * `Syntax.agda` : untyped syntax (type constructors and variables, contexts, substitutions)
  * `Rules.agda` : Typing rules - introduction rules for types and variables, formation of contexts and substitutions
  * `CwF-Structure.agda` : Structure of Category with families carried by the theory
  * `Dec-Type-Checking` : Decidability of type checking for this theory
  * `Uniqueness-Derivations` : Uniqueness of derivation for a derivable judgment
  * `Typed-Syntax` : Types for pairs of the form (Syntax, Derivation) where the derivation ensures that the syntactic object is valid in the theory.
  * `Disks` : Disk and sphere context and proof that they classify terms and types in other contexts.
* `Globular-TT/` - A globular type theory, the term constructors and introduction rules  are parametrized over judgments in GSeTT
  * `Syntax.agda` : untyped syntax (type constructors and variables, contexts, substitutions)
  * `Rules.agda` : Typing rules - introduction rules for types and variables, formation of contexts and substitutions
  * `CwF-Structure.agda` : Structure of Category with families carried by the theory
  * `Dec-Type-Checking` : Decidability of type checking for this theory
  * `Uniqueness-Derivations` : Uniqueness of derivation for a derivable judgment
  * `Typed-Syntax` : Types for pairs of the form (Syntax, Derivation) where the derivation ensures that the syntactic object is valid in the theory.
  * `Disks` : Disk and sphere context and proof that they classify terms and types in other contexts.
* `CaTT/` -  The type theory CaTT as a particular case of a globular type theory. It is defined by chosing an appropriate parametrization of the judgments over GSeTT.
  * `Ps-contexts.agda` : the ps-contexts are globular contexts that represent pasting schemes for weak omega-categories.
  * `Relation.agda` : a relation on variables of a context that characterize ps-contexts when it is linear (see [this article](https://arxiv.org/abs/1706.02866) by Mimram and Finster)
  * `Decidability-ps.agda` : Decidability of the judgment characterizing ps-contexts
  * `Uniqueness-derivations-ps.agda` : Uniqueness of derivations for the judgments characterizing ps-contexts
  * `Fullness.agda` a characterization of the terms that appropriately use the variables of the context like dexcribed in the papers.
