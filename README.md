
Aith is a low level functional programming language with linear types, kind based staging / macros, levity polymorphism, and effectful regions.
As of now aith is very early stages and very little is implemented.
See ``/rules`` for typing rules.

# Road Map

* [x] Macro Lambda Calculus
* [x] Macro Beta Reduction
* [ ] System-F
  * [x] Type Lambda / Application
  * [ ] Kind Lambda / Application
  * [ ] Type Lambda / Application for Effects
* [ ] System-F ω
* [ ] New Types
* [ ] Builtin Typeclasses
* [ ] User Defined Typeclasses
* [x] Pattern Matching
* [x] Basic Linear Types
* [ ] Multiplicity Polymorphism
* [ ] Multiplicity Predicates
* [x] Levity Polymorphism
* [x] Stage Polymorphism
* [x] Modules
* [ ] Runtime Primitives
  * [ ] Booleans
  * [x] Integers
  * [x] Pointers
  * [ ] Arrays
  * [x] Function Pointers
  * [x] Pairs
  * [ ] Records
  * [ ] Tagged Unions 
  * [ ] Recursive Types
* [ ] Effectful Regions
  * [x] Effects
  * [ ] References
    * [x] Type
    * [x] Read
    * [ ] Write
  * [ ] Let Region
* [x] Hindley Milner
  * [x] Builtin typeclasses
  * [ ] User defined typeclasses
* [x] C Code Generation
* [ ] Javascript Code Generation

# Syntax

## Modules(code)
| Description | Syntax |
|-|-|
| Module | ``module x = { code };`` |
| Inline Term | ``inline x = e; ``|
| Inline Term Ascribe | ``inline _ :: ς; inline x = e; ``|
| Function | ``function x = e;`` |
| Function Ascribe | ``function _ :: ς; function x = e;``|
| Import | ``import x = /x'/x''/...;``|

## Terms(e)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Macro Abstraction | `` `\pm { e }`` |
| Macro Abstraction | `` `\pm => e`` |
| Macro Application | ``e `e'``|
| Macro Application Ascribe | ``e `(e : σ)``|
| Of Course Introduction | ``![e]`` |
| Macro Binding | ``inline pm = e; e'``|
| Extern | ``extern "x" σa -> σa σa'`` |
| Function Application | ``e $ e'``|
| Function Application Ascribe | ``e $ (e' : σ)``|
| Function Literal | ``\pm => e`` |
| Function Literal | ``\pm { e }`` |
| Runtime Binding | ``let pm = e; e'`` |
| Runtime Pair Construction | ``e, e'`` |
| Read Reference | ``*e`` |
| Number Literal | ``n`` |
| Addition | ``e + e'`` |
| Addition with Sign | ``e +'ρ e'`` |
| Subtraction | ``e - e'`` |
| Subtraction with Sign | ``e -'ρ e'`` |
| Multiplication | ``e * e'`` |
| Multiplication with Sign | ``e *'ρ e'`` |
| Divsion | ``e / e'`` |
| Division with Sign | ``e /'ρ e'`` |
| Type Abstraction | ``/\pmσ => e`` |
| Type Abstraction | ``/\pmσ { e }`` |
| Type Application | ``e [[\/pmσ => σ]]<τ>``|

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
| Runtime Pair Destruction | ``pm , pm'`` |

## Auto Type (σa)
| Description | Syntax |
|-|-|
| Type | ``σ`` |
| Hole | ``_`` |

# Type Scheme(ς)
| Description | Syntax |
|-|-|
| TypeScheme | ``<'pmκ, 'pmκ', ..., pmσ, pmσ', ...> => σ`` |

## Types(σ, τ, π)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Macro | ``σ -`> τ``|
| Forall | ``\/x : κ => σ`` |
| Forall | ``\/x : κ { σ }`` |
| Of Course | ``![σ]`` |
| Function Pointer | `` τ -*> π σ `` |
| Function Literal Type | `` τ -> π σ `` |
| Runtime Pair | ``σ, σ'`` |
| Effect | ``σ @ π`` |
| Region Reference | ``reference π σ`` |
| Number | ``{{ρ}} ρ'`` |


## Type Pattern(pmσ)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Variable Ascribe | ``x : κ``|
| Variable Constrained | ``x + c & c' & ...`` |
| Variable Ascribe Constrained | ``x : κ + c & c' & ...`` |

## Constraints (c)
| Description | Syntax |
|-|-|
| Copy | ``copy`` |

## Auto Kind (κa)
| Description | Syntax |
|-|-|
| Kind | ``κ`` |
| Hole | ``_`` |

## Kinds(κ,s,ρ)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Type | ``*`` |
| Pretype | ``+[s]`` |
| Region | ``region`` |
| Real | ``#ρ#``|
| Imaginary | ``imaginary`` |
| Pointer Representation | ``pointer``|
| Struct Representation | ``struct (ρ, ρ', ...)`` |
| Word Representation | ``word ρ`` |
| Signed | ``signed`` |
| Unsigned | ``unsigned`` |
| Byte Size | ``byte``|
| Short Size | ``short``|
| Int Size | ``int`` |
| Long Size | ``long`` |

# Kind Pattern (pmκ)
| Description | Syntax |
|-|-|
| Variable Ascribe | ``x : μ`` |

## Sorts(μ)
| Description | Syntax |
|-|-|
| Kind | ``[ ]`` |
| Existance | ``existance`` |
| Representation | ``representation`` |
| Signedness | ``signedness`` |
| Size | ``size`` |

# C Compiler Requirements
* All pointers must have the same representation

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
  * Substitution composition algorithm taken from here
### Type Inference
* [QML : Explicit First-Class Polymorphism for ML](https://www.microsoft.com/en-us/research/wp-content/uploads/2009/09/QML-Explicit-First-Class-Polymorphism-for-ML.pdf)
  * Implemented with scoped type variables
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
    * Mix of single effect region calculus and monadic regions is in progress 
  * [Monadic Regions](https://www.cs.cornell.edu/people/fluet/research/rgn-monad/JFP06/jfp06.pdf)
  * [Linear Regions Are All You Need](https://www.cs.cornell.edu/people/fluet/research/substruct-regions/ESOP06/esop06.pdf)
### Type Inference (Subtyping)
* [The Simple Essence of Algebraic Subtyping](https://lptk.github.io/files/%5Bv1.8%5D%20simple-essence-algebraic-subtyping.pdf)
  * A tiny subset is planned for type checking regions. See my [var sub](https://github.com/Superstar64/var_sub/) repo.
## Related / Unused

### General Introductions
* [Practical Foundations for Programming Languages](https://profs.sci.univr.it/~merro/files/harper.pdf)
* [Type Systems](http://lucacardelli.name/Papers/TypeSystems.pdf)
### Linear / Unique Types
* [Linear Haskell](https://arxiv.org/pdf/1710.09756.pdf) [(video)](https://youtu.be/t0mhvd3-60Y)
*
  * [Making Uniqueness Typing Less Unique](http://edsko.net/pubs/thesis.pdf)
  * [Uniqueness Typing Simplified](http://www.edsko.net/pubs/ifl07-paper.pdf)
  * [Modelling Unique and Affine Typing using Polymorphism](http://www.edsko.net/pubs/modelling-unique-and-affine.pdf)
### Type Inference (First Class Polymorphism)
*
  * [HMF: Simple type inference for first-class polymorphism](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2007-118.pdf)
  * [Flexible types: robust type inference for first-class polymorphism](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-2008-55.pdf)
* [FreezeML : Complete and Easy Type Inference for First-Class Polymorphism](https://export.arxiv.org/pdf/2004.00396)
## Type Inference (Subtyping)
* [Algebraic Subtyping](https://www.cs.tufts.edu/~nr/cs257/archive/stephen-dolan/thesis.pdf)
### Unification
* [Unification Under a Mixed Prefix](https://www.lix.polytechnique.fr/~dale/papers/jsc92.pdf)
### Internals
* [System F with Type Equality Coercions](https://www.microsoft.com/en-us/research/wp-content/uploads/2007/01/tldi22-sulzmann-with-appendix.pdf)
* [Generalizing Hindley-Milner Type Inference Algorithms](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.18.9348&rep=rep1&type=pdf)


# Copyright
Copyright © Freddy A Cubas, "Superstar64"

Licensed under GPL3 only. See LICENSE for more info.
