# Catt-formalization
An agda prototype formalization of the [CaTT type theory](https://github.com/ThiBen/catt).

This is early stage development. The theory is presented in a cut-free style, introducing a pre-syntax and inference rules on it. All lemmas usually admitted are checked formally by induction on derivation trees. 

## Globular Type Theories
A general framework for studying type theories over globular sets. These type theories all share in common their type constructors and type introduction rules, but term constructors can be arbitrarily complex. The initial globular type theory is GSeTT, it has just variables and no term constructors. This theory is defined and studied first independently, and general notion of globular type theory is then defined, as a theory whose term constructors can be arbitrary, and whose term introduction rules are parametrized by judgments in the theory GSeTT.


## Structure of the Code
* GSeTT - The type theory for globular sets
..* Syntax.agda : untyped syntax (type constructors and variables, contexts, substitutions)
..* Rules.agda : Typing rules - introduction rules for types and variables, formation of contexts and substitutions
..* CwF-Structure.agda : Structure of Category with families carried by the theory
..* Dec-Type-Checking : Decidability of type checking for this theory
..* Uniqueness-Derivations : Uniqueness of derivation for a derivable judgment
..* Typed-Syntax : (Probably better not to use it)
* Globular-TT - A globular type theory, the term constructors and introduction rules  are parametrized over judgments in GSeTT
..* Syntax.agda : untyped syntax (type constructors and variables, contexts, substitutions)
..* Rules.agda : Typing rules - introduction rules for types and variables, formation of contexts and substitutions
..* CwF-Structure.agda : Structure of Category with families carried by the theory



