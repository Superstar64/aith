
Aith is a low level functional programming language with linear types, kind based staging / macros, and levity polymorphism.
As of now aith is very early stages and very little is implemented.
See ``/documentation`` for typing rules.

# Road Map

* [x] Macro Lambda Calculus
* [x] Macro Beta Reduction
* [x] System-F
* [ ] System-F ω
* [ ] Basic Linear Types
* [ ] Multiplicity Polymorphism
* [ ] Multiplicity Predicates
* [ ] Levity Polymorphism
* [ ] Stage Polymorphism
* [ ] Modules
* [ ] Runtime Lambda Calculus
* [ ] Runtime Primatives
* [ ] Hindley Milner Subset
* [ ] C Code Generation
* [ ] Javascript Code Generation

# Syntax
## Terms(e)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Type Abstraction | ``Λ<x : κ> { e }`` |
| Type Abstraction | ``Λ<x : κ> => e`` |
| Type Application | ``e<σ>`` |
| Term Abstraction | ``λ pm { e }``|
| Term Abstraction | ``λ pm => e ``|
| Term Application | ``e(e')``|
| Of Course Introduction | ``!e`` |
| Binding | ``%let pm = e1 ; e2 ``|

## Patterns(pm)
| Description | Syntax |
|-|-|
| Variable | ``(x : σ)``|
| OfCourse | ``!pm`` |

## Types (σ)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Forall | ``∀<x : κ> { σ }`` |
| Forall | ``∀<x : κ> => σ`` |
| Macro | ``σ -> σ'``|
| Of Course | ``!σ``|

## Stages (s)
| Description | Syntax |
|-|-|
| Runtime | ``%runtime`` |
| Macro | ``s -> s'`` |

## Kinds(κ)
| Description | Syntax |
|-|-|
| Type | `` s `` |

# Papers
Useful / Inspirational papers:

## Linear Types
* [A taste of linear logic](https://homepages.inf.ed.ac.uk/wadler/papers/lineartaste/lineartaste-revised.pdf)
* [The Best of Both Worlds Linear Functional Programming without Compromise](https://jgbm.github.io/pubs/morris-icfp2016-linearity-extended.pdf)
* [Linear Haskell](https://arxiv.org/pdf/1710.09756.pdf)
* [Making Uniqueness Typing Less Unique](http://edsko.net/pubs/thesis.pdf)
* [Modelling Unique and Affine Typing using Polymorphism](http://www.edsko.net/pubs/modelling-unique-and-affine.pdf)
## Levity polymorphism
* [Levity Polymorphism](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/levity-pldi17.pdf)
## Misc
* [Type Systems](http://lucacardelli.name/Papers/TypeSystems.pdf)
* [Typed Tagless Final Interpreters](http://okmij.org/ftp/tagless-final/index.html)
* [Demonstrating Lambda Calculus Reduction](https://www.cs.cornell.edu/courses/cs6110/2014sp/Handouts/Sestoft.pdf)

# Copyright
Copyright © Freddy A Cubas, "Superstar64"

Licensed under GPL3 only. See LICENSE for more info.
