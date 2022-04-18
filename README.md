
Aith is a low level functional programming language with linear types, generalized inline functions (staging), levity polymorphism, and effectful regions.
As of now aith is very early stages and very little is implemented.
See ``/rules`` for typing rules.

# Road Map

* [x] Inline Lambda Calculus
* [x] Inline Beta Reduction
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
  * [x] Region Subtyping
* [x] Hindley Milner
  * [x] Builtin typeclasses
  * [ ] User defined typeclasses
* [x] C Code Generation
* [ ] Javascript Code Generation

# Building and Running Tests
Install ghc, cabal and make.
Run `make` to build aith, `make tests` to run the tests and `make test.c` to generate the test c source file.

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
| Inline Abstraction | `` `\pm { e }`` |
| Inline Abstraction | `` `\pm => e`` |
| Inline Application | ``e `e'``|
| Inline Application Ascribe | ``e `(e : σ)``|
| Of Course Introduction | ``![e]`` |
| Inline Binding | ``inline pm = e; e'``|
| Extern | ``extern "x" function (σa) => σa uses σa'`` |
| Function Application | ``e $ e'``|
| Function Application Ascribe | ``e $ (e' : σ)``|
| Function Literal | ``function(pm) => e`` |
| Function Literal | ``function(pm) { e }`` |
| Runtime Binding | ``let pm = e; e'`` |
| Runtime Pair Construction | ``e, e'`` |
| Read Reference | ``*e`` |
| Number Literal | ``n`` |
| Addition | ``e + e'`` |
| Subtraction | ``e - e'`` |
| Multiplication | ``e * e'`` |
| Divsion | ``e / e'`` |
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

# Scheme(ς)
| Description | Syntax |
|-|-|
| TypeScheme | ``<'pmκ, 'pmκ', ..., pmσ, pmσ', ...>`` |

## Types(σ, τ, π)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Inline Function | ``σ -> τ``|
| Forall | ``\/x : κ => σ`` |
| Forall | ``\/x : κ { σ }`` |
| Of Course | ``![σ]`` |
| Function Pointer | ``function*(σ) => τ uses π`` |
| Function Literal Type | ``function(σ) => τ uses π`` |
| Runtime Pair | ``σ, σ'`` |
| Effect | ``σ @ π`` |
| Pointer | ``σ* @ π`` |
| Number | ``#ρ ρ'`` |

# Types (Syntax Sugar) (σ, τ, π)
| Description | Syntax | Meaning|
|-|-|-|
| Byte | ``byte`` | ``#signed byte`` |
| Short | ``short`` | ``#signed short`` |
| Int | ``int`` | ``#signed int`` |
| Long | ``long`` | ``#signed long`` |
| UByte | ``ubyte`` | ``#unsigned byte`` |
| UShort | ``ushort`` | ``#unsigned short`` |
| UInt | ``uint`` | ``#unsigned int`` |
| ULong | ``ulong`` | ``#unsigned long`` |





## Type Pattern(pmσ)
| Description | Syntax |
|-|-|
| Variable | ``x if c & c' & ... >= π & π' & ...`` |
| Variable Ascribe | ``x : κ if c & c' & ... >= π & π' & ...`` |


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
  * Reference for Robinson unification algorithm
### Type Inference (First Class Polymorphism)
* [QML : Explicit First-Class Polymorphism for ML](https://www.microsoft.com/en-us/research/wp-content/uploads/2009/09/QML-Explicit-First-Class-Polymorphism-for-ML.pdf)
  * Explicit type lambdas based mostly of this, with some major changes: Scoped type variables are used rather then schematic type variables, type lambdas don't need type annotations, lastly type application have an optional slot for the type parameter.
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
    * Mix of single effect region calculus and monadic regions is in progress 
  * [Monadic Regions](https://www.cs.cornell.edu/people/fluet/research/rgn-monad/JFP06/jfp06.pdf)
  * [Linear Regions Are All You Need](https://www.cs.cornell.edu/people/fluet/research/substruct-regions/ESOP06/esop06.pdf)
## Related / Unused

### General Introductions
* [Practical Foundations for Programming Languages](https://profs.sci.univr.it/~merro/files/harper.pdf)
* [Type Systems](http://lucacardelli.name/Papers/TypeSystems.pdf)
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
* [FreezeML : Complete and Easy Type Inference for First-Class Polymorphism](https://export.arxiv.org/pdf/2004.00396)
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
