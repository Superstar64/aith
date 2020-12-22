
Aith is a low level functional programming language with linear types, kind based staging / macros, and levity polymorphism.
As of now aith is very early stages and very little is implemented.
See ``/documentation`` for typing rules.

# Road Map

* [x] Macro Lambda Calculus
* [x] Macro Beta Reduction
* [x] System-F
* [ ] System-F ω
* [x] Linearity Polymorphism
* [ ] Linearity Predicates
* [ ] Levity Polymorphism
* [ ] Stage Polymorphism
* [ ] Modules
* [ ] Runtime Lambda Calculus
* [ ] Runtime Primatives
* [ ] Hindley Milner Subset

# Syntax
## Terms(e)
| Description | Syntax |
|-|-|
| Variable | ``x`` |
| Linearity Abstraction | ``Λ[x] { e } `` |
| Linearity Abstraction | ``Λ[x] => e `` |
| Linearity Application | ``e[l]``
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

## Linearity (l) 
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

## Kinds
| Description | Syntax |
|-|-|
| Type | `` l @ s`` |

# Copyright
Copyright © Freddy A Cubas, "Superstar64"
