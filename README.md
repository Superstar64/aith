
Aith is a perfomant systems programming language with am empathises on type systems.
As of now Aith is very early stages and very little is implemented.
[Link to typing rules](https://github.com/Superstar64/aith/blob/images/rules/rules.pdf).

| <img src="https://raw.githubusercontent.com/Superstar64/aith/images/rules/hierarchy.svg"> |
| :--: |
| visualization of (current) type system |

# Features

(todo: expand on all of these)

## Levity Polymorphic System-F
In languages like in C++ or Rust, generics perform monomorphization.
When a generic is used in these languages they will generate code for each instante of type they use.

Rather then do this, Aith uses levity polymorphism, which can be seen as a generalization of Java's type erasure generics.
In Aith, a type's kind, which is the type of a type, determines how (and if) it will be represented at runtime.

## Generalized Inline Functions (staging)
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

Aith has classical linear types (`!σ`) at the inline level and qualified necessarily unique types(unique types though type clasess) at the runtime level.

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

### Subtyping
(todo)

# Building and Running Tests
Install ghc, cabal and make.
Run `make` to build aith, `make tests` to run the tests and `make test.c` to generate the test c source file.


# Road Map (subject to change)

* [ ] Essentials
  * [ ] Runtime Primitives
    * [x] Booleans
      * [x] Boolean Type
      * [x] Boolean Literals
      * [x] If expression
      * [ ] Logical Operators
    * [x] Integers
      * [x] Arithmatic
      * [x] Relational Operators
    * [x] Pointers
      * [x] Shared
        * [ ] Type
        * [ ] Stack Allocation
        * [x] Get
        * [x] Set
      * [ ] Unique
        * [x] Type
        * [ ] Heap Allocation
      * [x] Borrowing
    * [ ] Arrays
      * [ ] Shared
        * [x] Type
        * [x] Array to Pointer
        * [x] Pointer Addition
        * [ ] Pointer Difference
        * [ ] Heap Allocation
      * [ ] Unique
        * [x] Type
        * [ ] Heap Allocation
      * [x] Borrowing
    * [x] Function Pointers
    * [x] Pairs
    * [ ] Records
    * [ ] Tagged Unions
  * [ ] New Types
  * [x] Modules
  * [ ] Hindley Milner
    * [x] Syntatical Unification
    * [ ] Higher Order Unification (System-F ω)
    * [x] Builtin Typeclasses (evidence only)
    * [ ] User Defined Typeclasses
  * [ ] Pattern Matching
    * [x] Destructure Products
    * [ ] Literals
    * [ ] Destructure Unions
* [x] Inline Lambda Calculus
* [ ] System-F
  * [x] Levity Polymorphism
  * [x] Type Lambda / Application
  * [x] Kind Lambda / Application
  * [ ] Type Lambda / Application for Runtime Terms
  * [ ] Higher Order Unification (System-F ω)
* [ ] Linear / Unique Types
  * [x] Basic Linear Types (at meta level)
  * [ ] Multiplicity Polymorphism
  * [x] Qualified Unique Types
* [ ] Effectful Regions
  * [x] Effects
  * [x] References
    * [x] Type
    * [x] Read
    * [x] Write
  * [ ] Let Region
  * [x] Region Subtyping
* [x] C Code Generation

# Syntax

Files start with `code` `:::`.

## Modules(code)
| Description | Syntax |
|-|-|
| Module | ``module x = { code };`` |
| Inline Term | ``inline x = e; ``|
| Inline Term Ascribe | ``inline x ς : σ; x ς = e; ``|
| Function | ``x = e;`` |
| Function Ascribe | ``x ς : σ; x ς = e;``|
| Import | ``import x = /x'/x''/...;``|

## Terms(e)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Inline Abstraction | `` \pm { e }`` |
| Inline Abstraction | `` \pm => e`` |
| Inline Application | ``e `e'``|
| Of Course Introduction | ``![e]`` |
| Inline Binding | ``inline pm = e; e'``|
| Extern | ``extern "sym"`` |
| Function Application | ``e (e')``|
| Function Literal | ``function(pm) => e`` |
| Function Literal | ``function(pm) { e }`` |
| Runtime Binding | ``let pm = e; e'`` |
| Pair Construction | ``e, e'`` |
| Unit Construction | ``()`` |
| Read Pointer | ``*e`` |
| Write Pointer | ``*e = e'`` |
| Array Increment | ``&e[e']`` |
| Number Literal | ``n`` |
| Addition | ``e + e'`` |
| Subtraction | ``e - e'`` |
| Multiplication | ``e * e'`` |
| Divsion | ``e / e'`` |
| Equality | ``e == e'`` |
| Inequality | ``e != e'`` |
| Less | ``e < e'`` |
| Less or Equal | ``e <= e'`` |
| Greater | ``e > e'`` |
| Greater or Equal | ``e >= e'`` |
| True | ``true`` |
| False | ``false`` |
| If | ``if e { e' } else { e''}`` |
| Poly Introduction| ``ς e`` |
| Poly Elimination | ``\|< e >\|`` |
| Borrow | ``borrow e as <α >= π>(pm) { e }`` |
| Type Annotation | ``e : σ`` |
| Pretype Annotation | ``e :: σ`` |

## Terms (Syntax Sugar) (e)
| Description | Syntax | Meaning |
| - | - | - |
| Not | ``~e`` | ``if e { false } else { true }`` |
| And | ``e & e'`` | ``if e { e' } else { false }`` |
| Or | ``e \| e'`` | ``if e { true } else { e' }`` |
| Do | ``e; e'`` | ``let () = e; e'`` |

## Meta Patterns(pm)
| Description | Syntax |
|-|-|
| Variable | ``x``|
| Variable Abscribe | ``x : σ`` |
| OfCourse | ``![pm]`` |

## Runtime Patterns(pm)
| Description | Syntax |
|-|-|
| Variable | ``x``|
| Variable Abscribe | ``x : σ`` |
| Pair Destruction | ``pm , pm'`` |
| Unit Destruction | ``()`` |

# Scheme(ς)
| Description | Syntax |
|-|-|
| TypeScheme | ``<'pmκ, 'pmκ', ..., pmσ, pmσ', ...>`` |

## Types(σ, τ, π)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Inline Function | ``σ -> τ``|
| Poly | ``ς σ`` |
| Of Course | ``![σ]`` |
| Function Pointer | ``function*(σ) => τ uses π`` |
| Function Literal Type | ``function(σ) => τ uses π`` |
| Pair | ``σ, σ'`` |
| Unit | ``()`` |
| Effect | ``σ in π`` |
| Unique | ``unique σ`` |
| Shared | ``σ @ π`` |
| Pointer | ``σ[τ]`` |
| Wildcard | ``:`` |
| Number | ``ρ integer(ρ')`` |
| Boolean | ``bool`` |
| IO Region | ``io`` |
| Type | ``*`` |
| Pretype | ``+[s]`` |
| Boxed | ``-`` |
| Capacity | ``capacity`` |
| Region | ``region`` |
| Pointer Representation | ``pointer``|
| Struct Representation | ``struct (ρ, ρ', ...)`` |
| Word Representation | ``ρ word`` |
| Signed | ``signed`` |
| Unsigned | ``unsigned`` |
| Byte Size | ``8bit``|
| Short Size | ``16bit``|
| Int Size | ``32bit`` |
| Long Size | ``64bit`` |
| Native Size | ``native`` |
| Kind | ``[κ]`` |
| Representation | ``representation`` |
| Signedness | ``signedness`` |
| Size | ``size`` |


# Types (Syntax Sugar) (σ, τ, π)
| Description | Syntax | Meaning |
|-|-|-|
| Byte | ``byte`` | ``#signed byte`` |
| Short | ``short`` | ``#signed short`` |
| Int | ``int`` | ``#signed int`` |
| Long | ``long`` | ``#signed long`` |
| PtrDiff | ``ptrdiff`` | ``#signed native`` |
| UByte | ``ubyte`` | ``#unsigned byte`` |
| UShort | ``ushort`` | ``#unsigned short`` |
| UInt | ``uint`` | ``#unsigned int`` |
| ULong | ``ulong`` | ``#unsigned long`` |
| Native | ``native`` | ``#unsigned native`` |

## Type Pattern(pmσ)
| Description | Syntax |
|-|-|
| Variable | ``x if c & c' & ... >= π & π' & ...`` |
| Variable Ascribe | ``x : κ if c & c' & ... >= π & π' & ...`` |


## Constraints (c)
| Description | Syntax |
|-|-|
| Copy | ``copy`` |



# Kind Pattern (pmκ)
| Description | Syntax |
|-|-|
| Variable Ascribe | ``x : μ`` |


# C Compiler Requirements
This list may be incomplete.
* All pointers must have the same representation (including function pointers).
* Signed integers must have 2's complement wrapping. (`-fwrapv` on gcc)

# Papers
Useful / Inspirational papers:

## Implemented

### Linear / Unique Types
* [A taste of linear logic](https://homepages.inf.ed.ac.uk/wadler/papers/lineartaste/lineartaste-revised.pdf)
  * Faithfully implemented
### Levity polymorphism
* [Levity Polymorphism](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/levity-pldi17.pdf) [(video)](https://youtu.be/lSJwXZ7vWBw)
  * Implemented with more restrictive representation lambda.
### Compiler Design
* [Invertible Syntax Descriptions: Unifying Parsing and Pretty Printing](https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf)
  * Implemented with prisms instead of partial isomorphisms.
### Algorithms
* [Demonstrating Lambda Calculus Reduction](https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf)
  * Applicative order reduction used for reduction.
* [Unification Theory](https://www.cs.bu.edu/fac/snyder/publications/UnifChapter.pdf)
  * Pointer for Robinson unification algorithm
### Type Inference (First Class Polymorphism)
The idea of having an implicit type scheme and explicit type scheme is taken from these two papers (QML and the Explicit Poly-ML variant).
The major modification is that scope type variables are used rather then schematic ones.
* [Semi-Explicit First-Class Polymorphism for ML](https://caml.inria.fr/pub/papers/garrigue_remy-poly-ic99.pdf)
* [QML : Explicit First-Class Polymorphism for ML](https://www.microsoft.com/en-us/research/wp-content/uploads/2009/09/QML-Explicit-First-Class-Polymorphism-for-ML.pdf)
### Type Inference (Subtyping)
* [The Simple Essence of Algebraic Subtyping](https://lptk.github.io/files/%5Bv1.8%5D%20simple-essence-algebraic-subtyping.pdf)
  * A tiny subset is implemented for type checking regions. See my [var sub](https://github.com/Superstar64/var_sub/) repo.
### Compiler Design
* [How OCaml type checker works -- or what polymorphism and garbage collection have in common](https://okmij.org/ftp/ML/generalization.html)
  * Only implemented for checking escaping skolem variables. Still need to implement let generalization.

## Planned

### Linear / Unique Types
* [The Best of Both Worlds: Linear Functional Programming without Compromise](https://jgbm.github.io/pubs/morris-icfp2016-linearity-extended.pdf) [(video)](https://youtu.be/ij9DbNTr-B8)
  * `Un` typeclass implemented as a builtin currently.
### Regions
* 
  * [Monadic and Substructural Type Systems for Region-Based Memory Management](https://www.cs.rit.edu/~mtf/research/thesis/fluet-thesis.single.pdf)
    * Implementation of single effect region calculus is in progress 
  * [Monadic Regions](https://www.cs.cornell.edu/people/fluet/research/rgn-monad/JFP06/jfp06.pdf)
  * [A Step-Indexed Model of Substructural State](https://www.cs.cornell.edu/people/fluet/research/substruct-state/ICFP05/icfp05.pdf)
  * [Linear Regions Are All You Need](https://www.cs.cornell.edu/people/fluet/research/substruct-regions/ESOP06/esop06.pdf)
## Related / Unused

### General Introductions
* [Practical Foundations for Programming Languages](https://profs.sci.univr.it/~merro/files/harper.pdf)
* [Type Systems](http://lucacardelli.name/Papers/TypeSystems.pdf)
### Pure Type Systems
* [An Introduction to Generalized Type Systems](https://www.researchgate.net/profile/Henk-hendrik-Barendregt/publication/216300104_An_Introduction_to_Generalized_Type_Systems/links/584c326d08aeb989251f7565/An-Introduction-to-Generalized-Type-Systems.pdf)
* [The Structural Theory of Pure Type Systems](https://www.andrew.cmu.edu/user//fpv/papers/struct_pts.pdf) [(video)](https://youtu.be/8zuTuE9f9Jg)
### Linear / Unique Types
* [Linear Haskell](https://arxiv.org/pdf/1710.09756.pdf) [(video)](https://youtu.be/t0mhvd3-60Y)
*
  * [Making Uniqueness Typing Less Unique](http://edsko.net/pubs/thesis.pdf)
  * [Uniqueness Typing Redefined](http://www.edsko.net/pubs/ifl06-paper.pdf)
  * [Equality-Based Uniqueness Typing](http://www.edsko.net/pubs/tfp07-paper.pdf)
  * [Uniqueness Typing Simplified](http://www.edsko.net/pubs/ifl07-paper.pdf)
  * [Modelling Unique and Affine Typing using Polymorphism](http://www.edsko.net/pubs/modelling-unique-and-affine.pdf)
### Type Inference (First Class Polymorphism)
*
  * [HMF: Simple type inference for first-class polymorphism](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2007-118.pdf)
  * [Flexible types: robust type inference for first-class polymorphism](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2008-55.pdf)
* [FreezeML : Complete and Easy Type Inference for First-Class Polymorphism](https://export.arxiv.org/pdf/2004.00396) [(video)](https://youtu.be/bZKC3o4jsek)
* [A Quick Look at Impredicativity](https://www.microsoft.com/en-us/research/uploads/prod/2020/01/quick-look-icfp20.pdf) [(video)](https://youtu.be/ZuNMo136QqI)
### Type Inference (Subtyping)
* [Algebraic Subtyping](https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf)
### Unification
* [Unification Under a Mixed Prefix](https://www.lix.polytechnique.fr/~dale/papers/jsc92.pdf)
### Internals
* [System F with Type Equality Coercions](https://www.microsoft.com/en-us/research/wp-content/uploads/2007/01/tldi22-sulzmann-with-appendix.pdf)
* [Generalizing Hindley-Milner Type Inference Algorithms](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.18.9348&rep=rep1&type=pdf)


# Copyright
Copyright © Freddy A Cubas, "Superstar64"

Licensed under GPL3 only. See LICENSE for more info.
