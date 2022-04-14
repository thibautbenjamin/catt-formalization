# Catt-formalization
An agda prototype formalization of the [CaTT type theory](https://github.com/ThiBen/catt).

 The theory is presented in a cut-free style, without axiom K, introducing a pre-syntax and inference rules on it. All lemmas usually admitted are checked formally by induction on derivation trees.

 The development was compiled with Agda version 2.6.3

## The type theory CaTT
CaTT is the dependent type theory that describes coherences for weak omega-categories. The theory is described in a less formal way in this [short article](https://arxiv.org/abs/1706.02866) or in this [longer article](https://arxiv.org/abs/2106.04475). The formalization in this repository is presented in the [following article](https://arxiv.org/abs/2111.14736). The exact state of the project corresponding to the above article is kept in the branch [TYPES2021](https://github.com/thibautbenjamin/catt-formalization/tree/TYPES2021).

## Globular Type Theories
A general framework for studying type theories over globular sets. These type theories all share in common their type constructors and type introduction rules, but term constructors can be arbitrarily complex. The initial globular type theory is GSeTT, it has just variables and no term constructors. This theory is defined and studied first independently, and general notion of globular type theory is then defined, as a theory whose term constructors can be arbitrary, and whose term introduction rules are parametrized by judgments in the theory GSeTT.


## Structure of the Code
The code base is separated into the files at the project root which correspond to library files used throughout the entire project, folders containing files related to the formalization of a particular dependent type theory. Each of the folders contains an agda file with the same name, that can be used to import the entire dependent type theory that it corresponds to.

Here is a list of the folders with a short description of the theory that they contain
* `GSeTT/`: A formalization of the dependent type theory for globular sets. The theory has type constructors describing the globes but no term constructors. It is a prerequisite for other developments.
* `Globular-TT/`: A formalization of globular type theories. Those are theories that have the same type constructors as `GSeTT`, but also have term constructors. They are introduced in a generic way, and indexed over syntactic elements in `GSeTT`, in such a way that any dependent type theory with those type constructors can be constructed as a globular type theory.
* `CaTT/`: A formalization of the type theory CaTT, which describes weak omega-categories, as a particular instance of a globular type theory.
* `MCaTT/`: A formalization of the type theory MCaTT, which describes monoidal weak omega-categories as a particular instance of a globular type theory.


The folders `GSeTT/` and `Globular-TT/` both follow the exact same structure, where first the syntax is introduced, then the rules of the theory, and then several meta-properties of the theories are proved. Precisely the structure of the project is as follows:
* `Name/` (where `Name` is `GSeTT` of `Globular-TT`):
  * `Syntax.agda` : Untyped syntax, i.e., the definition contexts, substitutions, types and terms along with operations that compute them it such as the application of a substitution.
  * `Rules.agda` : Typing rules, i.e., the formation rules for contexts and substitutions, the introduction rules for types and terms.
  * `CwF-Structure.agda` : Structure of Category with families carried by the theory, showing that the composition of substitution is associative, that the application of substitution preserves the derivability, and that it respects the composition.
  * `Dec-Type-Checking.agda` : Decidability of type checking for the theory, showing that there exists an algorithm that verifies in finite type whether a term is of a given type in a specified context.
  * `Uniqueness-Derivations.agda` : Show that every derivable judgment of the theory has a unique derivation tree, or in other words the type of proofs that a judgment is derivable is a proposition.
  * `Typed-Syntax.agda` : Define the typed syntax, that is the type of pairs of a syntactic entities together with a derivation tree of a judgment that ensures that the entity is valid in the theory.
  * `Disks.agda` : Definition of disk and sphere context, that are specific to those theories,
and proof that they classify terms and types in other contexts.
  * `Name.agda`: Import all the other files
* `CaTT/`:
  * `Ps-contexts.agda`: The ps-contexts are globular contexts that represent pasting schemes for weak omega-categories.
  * `Relation.agda` : a relation on variables of a context that characterize ps-contexts when it is linear (see [this article](https://arxiv.org/abs/1706.02866) by Mimram and Finster)
  * `Decidability-ps.agda`: Decidability of the judgment characterizing ps-contexts
  * `Uniqueness-derivations-ps.agda` : Uniqueness of derivations for the judgments characterizing ps-contexts
  * `Fullness.agda`: A characterization of the terms that appropriately use the variables of the context like dexcribed in the papers.
  * `CaTT.agda`: Import all other files and define the right index to import `Globular-TT`.
* `MCaTT/`:
  * `Desuspension.agda`: The desuspension operation on the globular syntax and proof o correctness
  * `MCaTT.agda`: Definition of the general desuspension operation, and definition of the index to import `Globular-TT`.
