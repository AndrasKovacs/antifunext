# antifunext

Checked with: Agda-2.6.4.3, stdlib 2.0

A model of Martin-Löf type theory (with pi, sigma, nat, identity, countable
universes) where function extensionality is false. It's due to Pierre-Marie
Pédrot who explained this to me at the TYPES 2024 conference.

## Overview

It's pretty easy to prove that function extensionality is *consistent* with
MLTT, we just need to give a model where funext is true, and which is also
non-trivial, i.e. there is no closed term of the empty type in the model. It's
easy because many simple models have funext just by inheriting it from a
metatheory, like set-theoretical models.

It's more tricky to show that funext is *unprovable* in MLTT. For this, we need
a model where funext is not inhabited (as expressed using types and terms of the
model). The complication is that functions have both beta and eta rules in MLTT,
and the eta rule blocks many naive attempts.

The solution here by Pierre-Marie is the simplest one that I know. It's
significantly simpler than the [polynomial
model](https://github.com/AndrasKovacs/polynomial-model) that I previously
formalized.

Let's summarize the idea.

We need a type with one inhabitant, but no judgmental eta rule; let's call it
`One` with inhabitant `one`. This is easily derivable even if we don't have it
primitively. Then, informally, we extend the theory with "error values" for
every type, which are only propagated by eliminators of positive types.

Now the function `λ (x : One). x` behaves differently to `λ (x : One). one`,
because `(λ x. x) error` is equal to `error` while `(λ x. one) error` is equal
to `one`. But in ordinary MLTT the two functions are provably pointwise equal.

So as a first step, we define a model where every type is pointed, and the extra
point is being preserved by positive eliminators. I sketch contexts, types and
terms, omitting universe levels:

    Con : Set
    Con = Set

	Ty : Con → Set
	Ty Γ = (A : Γ → Set) × ((γ : Γ) → A γ)

	Tm : (Γ : Con) → Ty Γ → Set
	Tm Γ (A, err) = (γ : Γ) → A γ

	...

	Bool : Ty Γ
	Bool = (λ _. Maybe MetaBool, λ _. Nothing)

    ...

We only add extra points explicitly to positive types, because functions can
be eta-expanded to constant errors and pairs to pairs of errors.

However, this doesn't refute funext, because *every* type is inhabited in the
model, including the type of funext.

But this is easily fixed by restricting the terms of the model to those which
don't actually produce any new errors.

    Con : Set
    Con = (Γ : Set) × (Γ → Set)

	Ty : Con → Set
	Ty (Γ, P) = (A : Γ → Set) × ((γ : Γ) → A γ) × ((γ : Γ) → P γ → A γ → Set)

	Tm : (Γ : Con) → Ty Γ → Set
	Tm (Γ, P) (A, err, Q) = (t : (γ : Γ) → A γ) × ((γ : Γ)(γᴾ : P γ) → Q γ γᴾ (t γ))

The last components of `Con` and `Ty` are predicates picking out the non-error
values, and the second component of `Tm` expresses that terms produce non-errors
in non-error environments.

Now, `λ x. x` and `λ x. one` are distinct in the model, and we can actually
refute funext: terms are required to produce non-error outputs from non-error
inputs, and there is no such term as an inhabitant of funext.

Moreover, although I didn't formalize this, it's clear that the negation of
funext, as a type in the model, is inhabited.

## As a model construction

In the Agda formalization, all equalities are dispatched with `refl`. This means
that everything would still work if we defined the model using the types and
terms of an arbitrary model of MLTT, instead of Agda's types and terms.

So, from any model of MLTT+(enough inductives) we get a new model of
MLTT+(enough inductives) where the negation of funext is inhabited. This mapping
also extends to a right adjoint endofunctor on the category of models of
MLTT+(enough inductives). I don't know if this is useful for anything though.
