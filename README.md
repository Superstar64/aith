
Aith is a low level functional programming language with linear types, kind based staging / macros, and levity polymorphism.
As of now aith is very early stages and very little is implemented.
See ``/documentation`` for typing rules.

# Road Map

* [x] Macro Lambda Calculus
* [x] Macro Beta Reduction
* [x] System-F
* [x] System-F ω
* [ ] New Types
* [x] Pattern Matching
* [x] Basic Linear Types
* [ ] Multiplicity Polymorphism
* [ ] Multiplicity Predicates
* [x] Levity Polymorphism
* [x] Stage Polymorphism
* [x] Modules
* [ ] Runtime Primitives
  * [ ] Booleans
  * [ ] Integers
  * [ ] Pointers
  * [ ] Arrays
  * [x] Function Pointers
  * [x] Tuples
  * [ ] Choice (Sums) 
* [ ] Hindley Milner Subset
* [x] C Code Generation
* [ ] Javascript Code Generation

# Syntax

## Modules(code)
| Description | Syntax |
|-|-|
| Module | ``module x = { code };`` |
| Inline Symbol | ``inline x =  e; ``|
| Import | ``import x = /x'/x''/...;``|
| Function | ``function x = ef;`` |
| Type Synonym | ``type x = σ;`` |

## Terms(e)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Of Course Introduction | ``!e`` |
| Binding | ``_let pm = e1 ; e2 ``|
| Runtime Binding | ``_alias pme = e1; e2`` |
| Macro Abstraction | ``\pm { e }``|
| Macro Abstraction | ``\pm => e ``|
| Macro Application | ``e e'``|
| Type Abstraction | `` `\pmσ { e }`` |
| Type Abstraction | `` `pmσ => e`` |
| Type Application | ``e`(σ)`` |
| Kind Abstraction | ``` ``\x : μ => e``` |
| Kind Abstraction | ``` ``\x : μ { e }``` |
| Kind Application | ``` e``(κ) ``` |
| Extern | ``_extern "x" (σ) _multiarg ((τ), (τ'), ...)`` |
| Extern | ``_extern "x" (σ) (τ) `` |
| Function Application | ``e(*) _multiarg (e1,e2, ...) ``|
| Function Application | ``e(*) e' ``|
| Function Literal | ``_function _multiarg (pme, pme', ...) => e`` |
| Function Literal | ``_function _multiarg (pme, pme', ...) { e }`` |
| Function Literal | ``_function pme => e`` |
| Function Literal | ``_function pme { e }`` |
| Erased Qualified Assumption | ``_when σ => e `` |
| Erased Qualified Assumption | ``_when σ { e } `` |
| Erased Qualified Check | ``e?`` |
| Pair Constructor (Left Associative) | ``#(e,e',...)`` |
| Recursive Type Introduction | ``_pack (pmσ => σ) e `` |
| Recursive Type Introduction| ``_pack (pmσ { σ }) e `` |
| Recursive Type Elimination | ``_unpack e`` |

# Function Sugar Term (ef)
|Description | Syntax |
|-|-|
| Type Abstraction | `` `\pmσ ef `` |
| Erased Qualified Assumption | `` when σ ef `` |
| Function Literal | ``_multiarg (pme, pme', ...) => e `` |
| Function Literal | ``_multiarg (pme, pme', ...) { e } `` |
| Function Literal | ``pme { e } `` |
| Function Literal | ``pme =>  e `` |
| Explict | ``~e`` |

## Patterns(pm)
| Description | Syntax |
|-|-|
| Variable | ``(x : σ)``|
| OfCourse | ``!pm`` |

## Runtime Patterns(pme)
| Description | Syntax |
|-|-|
| Variable | ``(x : σ)``|
| Pair Destruction (Left Associative) | ``(pm, pm', ...)`` |

## Types(σ, τ, π)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Forall | `` `\/pmσ { σ }`` |
| Forall | `` `\/pmσ => σ`` |
| KindForall | ``` ``\/s : μ => σ``` |
| KindForall | ``` ``\/s : μ { σ }``` |
| Macro | ``σ -> σ'``|
| Of Course | ``!σ``|
| Type Operator | `` \x : κ { σ }``|
| Type Operator | `` \x : κ => σ ``|
| Poly Operator | `` `\x : μ => κ`` |
| Poly Operator | `` `\x : μ { κ }`` |
| Poly Construction | `` σ`(κ) ``
| Type Construction | `` σ τ `` |
| Function Pointer | `` σ(*) _multiarg (τ, τ', ...) `` |
| Function Pointer | `` σ(*) τ `` |
| Function Literal Type | `` σ _function _multiarg(τ, τ', ...) `` |
| Function Literal Type | `` σ _function τ `` |
| Erased Qualified Type | `` π =>? σ `` |
| Copy Predicate | ``_copy σ`` |
| Pair (Left Associative) | ``#(σ, σ', ...)`` |
| Recursive Type | `` _recursive pmσ => σ`` |
| Recursive Type | `` _recursive pmσ { σ }`` |

## Type Pattern(pmσ)
|Description | Syntax |
|-|-|
| Variable | ``x : κ`` |
| Runtime Pointer Variable | ``x`` |

## Kinds(κ,s,ρ)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Type | `` _type s `` |
| Higher | `` κ -> κ' `` |
| Poly | `` `\/ x : μ => κ `` |
| Poly | `` `\/ x : μ { κ } `` |
| Constraint | `` _constraint `` |
| Runtime | ``_runtime ρ`` |
| Meta | ``_meta`` |
| Text | ``_text`` |
| Pointer Representation | ``_pointer``|
| Struct Representation | ``_struct (ρ, ρ', ...)`` |

## Sorts(μ)
| Description | Syntax |
|-|-|
| Kind | ``_kind`` |
| Stage | ``_stage`` |
| Representation | ``_representation`` |

# C Compiler Requirements
* All pointers must have the same representation

# Papers
Useful / Inspirational papers:

## Linear Types
* [A taste of linear logic](https://homepages.inf.ed.ac.uk/wadler/papers/lineartaste/lineartaste-revised.pdf)
* [The Best of Both Worlds: Linear Functional Programming without Compromise](https://jgbm.github.io/pubs/morris-icfp2016-linearity-extended.pdf)
* [Linear Haskell](https://arxiv.org/pdf/1710.09756.pdf)
* [Making Uniqueness Typing Less Unique](http://edsko.net/pubs/thesis.pdf)
* [Modelling Unique and Affine Typing using Polymorphism](http://www.edsko.net/pubs/modelling-unique-and-affine.pdf)
## Levity polymorphism
* [Levity Polymorphism](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/levity-pldi17.pdf)
## Misc
* [Type Systems](http://lucacardelli.name/Papers/TypeSystems.pdf)
* [System F with Type Equality Coercions](https://www.microsoft.com/en-us/research/wp-content/uploads/2007/01/tldi22-sulzmann-with-appendix.pdf)
* [Typed Tagless Final Interpreters](http://okmij.org/ftp/tagless-final/index.html)
* [Demonstrating Lambda Calculus Reduction](https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf)
* [Invertible Syntax Descriptions: Unifying Parsing and Pretty Printing](https://www.mathematik.uni-marburg.de/~rendel/rendel10invertible.pdf)

# Copyright
Copyright © Freddy A Cubas, "Superstar64"

Licensed under GPL3 only. See LICENSE for more info.
