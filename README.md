
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
* [ ] Runtime Lambda Calculus
* [ ] Runtime Primatives
* [ ] Hindley Milner Subset
* [x] C Code Generation
* [ ] Javascript Code Generation

# Syntax

## Modules(code)
| Description | Syntax |
|-|-|
| Module | ``module x = { code };`` |
| Inline Symbol | ``inline x =  e; ``|
| Import | ``import x = x'/x''/...``|
| Function | ``function x = ef;`` |

## Terms(e)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Of Course Introduction | ``!e`` |
| Binding | ``%let pm = e1 ; e2 ``|
| Macro Abstraction | ``λ pm { e }``|
| Macro Abstraction | ``λ pm => e ``|
| Macro Application | ``e(e')``|
| Type Abstraction | ``Λ<pmσ> { e }`` |
| Type Abstraction | ``Λ<pmσ> => e`` |
| Type Application | ``e<σ>`` |
| Kind Abstraction | ``Λ@ x : μ => e`` |
| Kind Abstraction | ``Λ@ x : μ { e }`` |
| Kind Application | ``e @ κ`` |
| Extern | ``%extern "x" (σ)(τ, τ', ...)`` |
| Function Application | ``e(*)(e1,e2, ...) ``|
| Function Literal | ``%function (τ)(pme, pme', ...) => e`` |
| Function Literal | ``%function (τ)(pme, pme', ...) { e }`` |
| Erased Qualified Assumption | ``ξ σ => e `` |
| Erased Qualified Assumption | ``ξ σ { e } `` |
| Erased Qualified Check | ``e?`` |


# Function Sugar Term (ef)
|Description | Syntax |
|-|-|
| Type Abstraction | `` <pmσ> ef `` |
| Erased Qualified Assumption | `` when (σ) ef `` |
| Function Literal | ``(τ)(pme, pme', ...) => e `` |
| Function Literal | ``(τ)(pme, pme', ...) { e } `` |
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

## Types(σ, τ, π)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Forall | ``∀<pmσ> { σ }`` |
| Forall | ``∀<pmσ> => σ`` |
| KindForall | ``∀@s : μ => σ`` |
| KindForall | ``∀@s : μ { σ }`` |
| Macro | ``σ -> σ'``|
| Of Course | ``!σ``|
| Type Operator | `` λ x : κ { σ }``|
| Type Operator | `` λ x : κ => σ ``|
| Type Construction | `` σ (τ) `` |
| Function Pointer | `` σ(*)(τ, τ', ...) `` |
| Function Literal Type | `` σ %function (τ, τ', ...) `` |
| Erased Qualified Type | `` π =>? σ `` |
| Copy Predicate | ``%copy σ`` |

## Type Pattern(pmσ)
|Description | Syntax |
|-|-|
| Variable | ``x : κ`` |
| Runtime Pointer Variable | ``x`` |

## Kinds(κ,s,ρ)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Type | `` %type s `` |
| Higher | `` κ -> κ' `` |
| Runtime | ``%runtime ρ`` |
| Meta | ``%meta`` |
| Text | ``%text`` |
| Pointer Representation | ``%pointer``|

## Sorts(μ)
| Description | Syntax |
|-|-|
| Kind | ``%kind`` |
| Stage | ``%stage`` |
| Representation | ``%representation`` |

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
