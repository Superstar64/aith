
Aith is a low level functional programming language with linear types, kind based staging / macros, and levity polymorphism.
As of now aith is very early stages and very little is implemented.
See ``/documentation`` for typing rules.

# Road Map

* [x] Macro Lambda Calculus
* [x] Macro Beta Reduction
* [x] System-F
* [ ] System-F ω
* [x] Multiplicity Polymorphism
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
| Multiplicity Abstraction | ``Λ[x] { e } `` |
| Multiplicity Abstraction | ``Λ[x] => e `` |
| Multiplicity Application | ``e[l]``
| Type Abstraction | ``Λ<x : κ> { e }`` |
| Type Abstraction | ``Λ<x : κ> => e`` |
| Type Application | ``e<σ>`` |
| Term Abstraction | ``λ[l](x : σ) { e }``|
| Term Abstraction | ``λ[l](x : σ) => e ``|
| Term Application | ``e(e')``|

## Types (σ)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Linear Forall | ``∀[x] { σ }`` |
| Linear Forall | ``∀[x] => σ`` |
| Forall | ``∀<x : κ> { σ }`` |
| Forall | ``∀<x : κ> => σ`` |
| Macro | ``σ -[l]> σ'``|

## Multiplicity (l) 
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Linear | ``%linear`` |
| Unrestricted | ``%unrestricted`` |

## Stages (s)
| Description | Syntax |
|-|-|
| Runtime | ``%runtime`` |
| Macro | ``s -> s'`` |

## Kinds(κ)
| Description | Syntax |
|-|-|
| Type | `` l @ s`` |

# Papers
Papers that inspired this language:
* https://jgbm.github.io/pubs/morris-icfp2016-Multiplicity-extended.pdf
* https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/levity-pldi17.pdf

# Copyright
Copyright © Freddy A Cubas, "Superstar64"

Licensed under GPL3 only. See LICENSE for more info.
