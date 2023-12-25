
Aith is a perfomant systems programming language with am empathises on type systems.
As of now Aith is very early stages and very little is implemented.
[Link to typing rules](https://github.com/Superstar64/aith/blob/images/rules/rules.pdf).

| <img src="https://raw.githubusercontent.com/Superstar64/aith/images/rules/internals.svg"> |
| :--: |
| visualization of compiler internals |

| <img src="https://raw.githubusercontent.com/Superstar64/aith/images/rules/hierarchy.svg"> |
| :--: |
| visualization of type system |

| <img src="https://raw.githubusercontent.com/Superstar64/aith/images/rules/pure.svg"> |
| :--: |
| pure type system subset |


# Features

(todo: expand on all of these)

## Levity Polymorphic System-F
In languages like in C++ or Rust, generics perform monomorphization.
When a generic is used in these languages they will generate code for each instante of type they use.

Rather then do this, Aith uses levity polymorphism, which can be seen as a generalization of Java's type erasure generics.
In Aith, a type's kind, which is the type of a type, determines how (and if) it will be represented at runtime.

## First Class Inline Functions (staging)
Aith has first class inline functions, a unique (as far as I can tell) take on staging.
In Aith, inline functions can take inline functions as argument and return inline functions,
all of which is completely erased at runtime.

Inline functions that type check always generate valid code
and inline functions are prevented from appearing at runtime though kind checking.

## Linear / Unique Types
Aith supports linear types and unique types.
These are types that limit how copying of variables.
Linear types promise that a variable of a linear type will be used exactly once.
Unique types promise that a variable of a unique type will has not been aliased.

Aith has linear types at the inline level with multiplicity in the arrow like Linear Haskell.
Aith has necessarily unique types at the runtime level with multiplicity via kinds.

## Effectful Regions
Aith has support for effectful regions, similar to Rust's lifetimes.
Regions allow programs to reason about borrowing and scoping resources (like memory).
Conceptually, an executing program has a stack of regions that it accessing at any given time (think stack frames).
If a region is alive, then that region and all it's parent regions are valid.

In Aith, regions are effectful, meaning that all runtime expressions are attached to a region that they live in.
These expressions can only access memory in their region or regions proven to be parents of said region. 

## Type Inference
(todo)

### First Class Polymorpism (System-F)
(todo)

### Boolean Unification
(todo)

# Building and Running Tests
Install ghc, cabal and make.
Run `make` to build aith, `make tests` to run the tests and `make test.c` to generate the test c source file.

# Todo List

* Better newtypes
* Add higher kinded types (System-F A)
* Runtime level higher rank polymorphism
* Simplify boolean types to DNF rather then ANF
* Refactoring and syntax changes as usual

# Syntax

Files are lists of declarations, where these declarations could be a plain variable declaration or a path declaration. For example `f(x) { x }` is a plain declaration and `example/f(x) { x }` is a path declaration.

Folders concatenates all it's contents where the folder name is prepend to all the declarations. A folder named `abc` prepends `abc/` to all it's contents.

## Declarations(code)
| Description | Syntax |
|-|-|
| Inline Term | `inline x = e;`|
| Inline Term Ascribe | `inline x : σ = e;`|
| Function | `x(pm, pm', ...) { e }` |
| Function Ascribe | `x(pm, pm', ...) : σ in π { e }`|
| Function Ascribe | `x(pm, pm', ...) :: σ { e }`|
| Synonym | `type x = σ;` |
| New Type Declaration | `newtype x : κ;` |

## Terms(e)
| Description | Syntax |
|-|-|
| Variable | `x` |
| Variable | `x @_` |
| Variable | `x @<σ, σ', ...>` |
| Global Variable | `/x/x'/...` |
| Inline Abstraction | ` \pm -> e` |
| Inline Application | `e {e'}`|
| Inline Binding | `inline pm = e; e'`|
| Extern | `extern [arity] "sym"` |
| Function Application | `e (e', e'', ...)`|
| Runtime Binding | `let pm = e; e'` |
| Tuple Construction | `(e, e', ...)` |
| Read Pointer | `*e` |
| Write Pointer | `*e = (e')` |
| Array Increment | `&e[e']` |
| Array to Pointer | `&*e` |
| Number Literal | `n` |
| Addition | `e + e'` |
| Subtraction | `e - e'` |
| Multiplication | `e * e'` |
| Divsion | `e / e'` |
| Equality | `e == e'` |
| Inequality | `e != e'` |
| Less | `e < e'` |
| Less or Equal | `e <= e'` |
| Greater | `e > e'` |
| Greater or Equal | `e >= e'` |
| True | `true` |
| False | `false` |
| Switch | `switch e { pm -> e; pm' -> e'; ... }` |
| Poly Introduction| `ς e` |
| Poly Elimination | `e @_` |
| Poly Elimination | `e @<σ, σ', ...>` |
| Type Annotation | `e : σ` |
| Pretype Annotation | `e :: σ` |
| Continue | `continue e` |
| Break | `break e` |
| Loop | `loop (let pm = e) { e' }` |
| Unsafe Cast | `cast e` |

## Terms (Syntax Sugar) (e)
| Description | Syntax | Meaning |
| - | - | - |
| Not | `!e` | `if e { false } else { true }` |
| And | `e & e'` | `if e { e' } else { false }` |
| Or | `e \| e'` | `if e { true } else { e' }` |
| Do | `e; e'` | `let () = e; e'` |
| If | `if e { e' } else { e''}` | `switch (e) { true -> e; false -> e'; } ` | 

## Meta Patterns(pm)
| Description | Syntax |
|-|-|
| Linear Variable | `x`|
| Linear Variable Abscribe | `x : σ` |
| Unrestricted Variable Abscribe | `x :* σ` |
| Polymorphic Variable Abscribe | `x :^τ σ` |

## Runtime Patterns(pm)
| Description | Syntax |
|-|-|
| Variable | `x` |
| Variable Abscribe | `x : σ` |
| Tuple Destruction | `(pm, pm', ...)` |
| True | `true` |
| False | `false` |

# Scheme(ς)
| Description | Syntax |
|-|-|
| TypeScheme | `<pmσ, pmσ', ...>` |

## Types(σ, τ, π, κ, ρ)
| Description | Syntax |
|-|-|
| Hole | `_` |
| Variable | `x` |
| Linear Inline Function | `σ -> τ`|
| Unrestricted Inline Function | `σ -* τ` |
| Polymorphic Inline Function | `σ -π τ ` |
| Poly | `ς σ` |
| Function Pointer | `function(σ, σ', ...) -> τ uses π` |
| Tuple | `(σ, σ', ...)` |
| Effect | `σ in π` |
| Unique | `unique σ` |
| Shared | `σ @ π` |
| Pointer | `σ*` |
| Array | `σ[]` |
| Number | `ρ integer(ρ')` |
| Boolean | `bool` |
| IO Region | `io` |
| Step | `step<σ, τ>` |
| Type | `type` |
| Pretype | `pretype<s>` |
| Boxed | `boxed` |
| Capacity | `capacity` |
| Region | `region` |
| Pointer Representation | `pointer` |
| Struct Representation | `struct (ρ, ρ', ...)` |
| Union Representation | `union (ρ, ρ', ...)` |
| Word Representation | `ρ word` |
| Signed | `signed` |
| Unsigned | `unsigned` |
| Byte Size | `8bit`|
| Short Size | `16bit`|
| Int Size | `32bit` |
| Long Size | `64bit` |
| Native Size | `native` |
| Representation | `representation` |
| Signedness | `signedness` |
| Size | `size` |
| Type True | `true` |
| Type False | `false` |
| Type And | `σ & τ` |
| Type Or | `σ \| τ` |
| Type Not | `!σ` |
| Type Xor | `σ (+) τ` |

# Types (Internal) (σ, τ, π, κ, ρ)
| Description | Syntax |
| - | - |
| Unification | `unification` |
| Kind | `kind<σ>` |
| Syntactic |`syntactic` |
| Propositional |`propositional` |
| Top | `/\|\` |
| Function Literal Type | `function literal(σ) -> τ uses π` |
| Label | `label` |
| Ambiguous Label | `ambiguous` |

# Types (Syntax Sugar) (σ, τ, π, κ, ρ)
| Description | Syntax | Meaning |
|-|-|-|
| Byte | `byte` | `signed integer(8bit)` |
| Short | `short` | `signed integer(16bit)` |
| Int | `int` | `signed integer(32bit)` |
| Long | `long` | `signed integer(64bit)` |
| PtrDiff | `ptrdiff` | `signed integer(native)` |
| UByte | `ubyte` | `unsigned integer(8bit)` |
| UShort | `ushort` | `unsigned integer(16bit)` |
| UInt | `uint` | `unsigned integer(32bit)` |
| ULong | `ulong` | `unsigned integer(64bit)` |
| Integer | `integer(σ)` | `signed integer(σ)` |
| Natural | `natural(σ)` | `unsigned integer(σ)` |
| Native Integer | `integer` | `signed integer(native)` |
| Native Natural | `natural` | `unsigned integer(native)` |



## Type Pattern(pmσ)
| Description | Syntax |
|-|-|
| Variable | `x : κ` |
| Concrete Variable | `x :* κ` |


# C Compiler Requirements
This list may be incomplete.
* All pointers must have the same representation (including function pointers).
* Signed integers must have 2's complement wrapping. (`-fwrapv` on gcc)

# Papers
Useful / Inspirational papers:

## Implemented

### Linear / Unique Types
* [Linear Haskell](https://arxiv.org/pdf/1710.09756.pdf) [(video)](https://youtu.be/t0mhvd3-60Y)
  * Implemented for inline functions
### Levity polymorphism
* [Levity Polymorphism](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/levity-pldi17.pdf) [(video)](https://youtu.be/lSJwXZ7vWBw)
  * Implemented with more restrictive representation lambda.
### Compiler Design
* [Invertible Syntax Descriptions: Unifying Parsing and Pretty Printing](https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf)
  * Implemented with prisms instead of partial isomorphisms.
### Reduction
* [Demonstrating Lambda Calculus Reduction](https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf)
  * Applicative order reduction used for inline function reduction.
### Unification
* [Unification Theory](https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf)
  * Reference for unification and E-unification
* [Embedding Boolean Expressions into Logic Programming](https://core.ac.uk/download/pdf/82206645.pdf)

### Type Inference (First Class Polymorphism)
PolyML is implemented, but with scope type variables are used rather then schematic ones.
* [Semi-Explicit First-Class Polymorphism for ML](https://caml.inria.fr/pub/papers/garrigue_remy-poly-ic99.pdf)
### Compiler Design
* [How OCaml type checker works -- or what polymorphism and garbage collection have in common](https://okmij.org/ftp/ML/generalization.html)
  * Only implemented for checking escaping skolem variables. Still need to implement let generalization.
### Regions
* 
  * [Monadic and Substructural Type Systems for Region-Based Memory Management](https://www.cs.rit.edu/~mtf/research/thesis/fluet-thesis.single.pdf)
    * General guide for regions.
  * [Monadic Regions](https://www.cs.cornell.edu/people/fluet/research/rgn-monad/JFP06/jfp06.pdf)
  * [A Step-Indexed Model of Substructural State](https://www.cs.cornell.edu/people/fluet/research/substruct-state/ICFP05/icfp05.pdf)
  * [Linear Regions Are All You Need](https://www.cs.cornell.edu/people/fluet/research/substruct-regions/ESOP06/esop06.pdf)

## Inspirational, and / or Formerly Used

### General Introductions
* [Practical Foundations for Programming Languages](https://profs.sci.univr.it/~merro/files/harper.pdf)
* [Type Systems](http://lucacardelli.name/Papers/TypeSystems.pdf)
### Pure Type Systems
* [An Introduction to Generalized Type Systems](https://www.researchgate.net/profile/Henk-hendrik-Barendregt/publication/216300104_An_Introduction_to_Generalized_Type_Systems/links/584c326d08aeb989251f7565/An-Introduction-to-Generalized-Type-Systems.pdf)
* [The Structural Theory of Pure Type Systems](https://www.andrew.cmu.edu/user//fpv/papers/struct_pts.pdf) [(video)](https://youtu.be/8zuTuE9f9Jg)
### Linear / Unique Types
*
  * [Making Uniqueness Typing Less Unique](http://edsko.net/pubs/thesis.pdf)
  * [Uniqueness Typing Redefined](http://www.edsko.net/pubs/ifl06-paper.pdf)
  * [Equality-Based Uniqueness Typing](http://www.edsko.net/pubs/tfp07-paper.pdf)
  * [Uniqueness Typing Simplified](http://www.edsko.net/pubs/ifl07-paper.pdf)
  * [Modelling Unique and Affine Typing using Polymorphism](http://www.edsko.net/pubs/modelling-unique-and-affine.pdf)
* [A taste of linear logic](https://homepages.inf.ed.ac.uk/wadler/papers/lineartaste/lineartaste-revised.pdf)
* [Linearity and Uniqueness: An Entente Cordiale](https://granule-project.github.io/papers/esop22-paper.pdf)
* [The Best of Both Worlds: Linear Functional Programming without Compromise](https://jgbm.github.io/pubs/morris-icfp2016-linearity-extended.pdf) [(video)](https://youtu.be/ij9DbNTr-B8)
### Effect Tracking
 * [Polymorphic Types and Effects with Boolean Unification](https://flix.dev/paper/oopsla2020b.pdf)
### Type Inference (First Class Polymorphism)
*
  * [HMF: Simple type inference for first-class polymorphism](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2007-118.pdf)
  * [Flexible types: robust type inference for first-class polymorphism](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2008-55.pdf)
* [FreezeML : Complete and Easy Type Inference for First-Class Polymorphism](https://export.arxiv.org/pdf/2004.00396) [(video)](https://youtu.be/bZKC3o4jsek)
* [A Quick Look at Impredicativity](https://www.microsoft.com/en-us/research/uploads/prod/2020/01/quick-look-icfp20.pdf) [(video)](https://youtu.be/ZuNMo136QqI)
* [QML : Explicit First-Class Polymorphism for ML](https://www.microsoft.com/en-us/research/wp-content/uploads/2009/09/QML-Explicit-First-Class-Polymorphism-for-ML.pdf)
### Type Inference (Subtyping)
*
  * [Algebraic Subtyping](https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf)
  * [Polymorphism, Subtyping, and Type Inference in MLsub](https://www.repository.cam.ac.uk/bitstream/handle/1810/261583/Dolan_and_Mycrof-2017-POPL-AM.pdf) [(video)](https://youtu.be/-P1ks4NPIyk)
* [The Simple Essence of Algebraic Subtyping](https://dl.acm.org/doi/pdf/10.1145/3409006) [(video)](https://youtu.be/d10q-b8jNKg)
### Unification
* [Unification Under a Mixed Prefix](https://www.lix.polytechnique.fr/~dale/papers/jsc92.pdf)
### Internals
* [System F with Type Equality Coercions](https://www.microsoft.com/en-us/research/wp-content/uploads/2007/01/tldi22-sulzmann-with-appendix.pdf)
* [Generalizing Hindley-Milner Type Inference Algorithms](https://www.cs.uu.nl/research/techreps/repo/CS-2002/2002-031.pdf)


# Copyright
Copyright © Freddy A Cubas, "Superstar64"

Licensed under GPL3 only. See LICENSE for more info.
