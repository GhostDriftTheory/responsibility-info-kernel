# Responsibility Information Kernel for Responsibility OS

This repository contains Lean developments supporting the Responsibility OS glossary and its mathematical claim about responsibility-relevant information.

There are two Lean files:

- `ResponsibilityInfoKernel.lean`
- `GenericNoncommutativity.lean`

`ResponsibilityInfoKernel` is the main kernel. It formalizes why responsibility-relevant information must preserve histories and order-sensitive distinctions for retrospective inspectability.

`GenericNoncommutativity` is an independent companion result. It shows that, in finite-state transition dynamics, noncommutativity is generic rather than exceptional. It supports the motivation of the main kernel, but the main kernel does not depend on it.

## Core Claim

Responsibility information treats real-world judgment, action, observation, recording, review, audit, and AI inference as history-bearing information processes.

For any nonempty process with at least two distinguishable events, adding chronological history yields a noncommutative information state: doing `A` then `B` and doing `B` then `A` reach different information states, even if a coarse output, label, score, or commutative summary later collapses them.

Responsibility information preserves selected distinctions so that they remain retrospectively inspectable.

## Main Kernel: `ResponsibilityInfoKernel`

`ResponsibilityInfoKernel.lean` is the main Lean development.

It formalizes:

- state-transition systems;
- chronological traces;
- output-only observations;
- responsibility-enriched observations;
- retrospective inspectability;
- loss of inspectability under coarse or commutative observations;
- `TraceLift`, which adds chronological history to the information state;
- a categorical bridge to the `ResponsibilityOS` policy-preservation framework.

The central construction is:

```text
TraceLift T
```

For a transition system `T`, `TraceLift T` has states of the form:

```text
T.State × Trace T.Act
```

Its step function updates both the original state and the chronological history:

```text
(state, history) |--a--> (T.step a state, history ++ [a])
```

The history is chronological, not reverse chronological.

The main structural theorem is:

```lean
trace_lift_of_any_nontrivial_information_process_is_noncommutative
```

It says that if a transition system has at least one possible state and at least two distinguishable events, then the trace-lifted system reaches different information states for `[a, b]` and `[b, a]`.

This is the formal core of the Responsibility OS claim that order-sensitive histories must not be discarded when later inspection matters.

## Companion Result: `GenericNoncommutativity`

`GenericNoncommutativity.lean` is an independent companion theorem.

It does not prove the main responsibility-information theorem. Instead, it supports the motivation by showing that noncommutativity is not an artificial edge case in finite-state transition dynamics.

It models two events as arbitrary endomorphisms:

```lean
f g : S -> S
```

on a finite state space `S`.

It proves that, as `|S|` grows, the proportion of commuting pairs shrinks toward `0`, so the proportion of noncommuting pairs tends to `1`.

One concrete theorem is:

```lean
noncommuting_pairs_at_least_99_percent
```

For finite state spaces with at least `101` states, at least `99%` of all endomorphism pairs are noncommuting, under the uniform counting measure over all pairs of functions `S -> S`.

This does not mean that 99% of real-world processes are noncommutative. It means that, in the mathematical space of all finite-state transition functions, noncommutativity is generic.

## Relation Between the Two Lean Files

The relationship is:

```text
GenericNoncommutativity
= companion theorem
= genericity of noncommutativity
= finite-state transition pairs are usually noncommuting under uniform counting

ResponsibilityInfoKernel
= main kernel
= responsibility information / history / inspectability
= histories and order-sensitive distinctions must be preserved for later inspection
```

The conceptual flow is:

```text
Companion result:
finite-state dynamics are generically noncommutative.
        ↓
Main responsibility-information kernel:
coarse outputs, labels, scores, and aggregates can lose order-sensitive distinctions.
        ↓
TraceLift theorem:
when chronological history is included in the information state,
distinguishable event orders become inspectable distinctions.
```

The main kernel does not depend on `GenericNoncommutativity`. The companion result is an independent motivation and strengthening.

## Relation to the Responsibility OS Glossary

This Lean development is a mathematical kernel supporting the Responsibility OS glossary.

It does not attempt to formalize the standard definitions of provenance, traceability, audit trails, metadata, auditability, or verifiability as used in existing information science standards. For example, it does not formalize W3C PROV itself.

Instead, it formalizes the structural reason why those concepts matter for Responsibility OS: responsibility-relevant information must preserve distinctions in state transitions, histories, and observations that may be lost by output-only, label-only, or commutative abstractions.

In this sense, the glossary and this Lean kernel correspond as follows.

### 1. Existing Information Science Terms

Terms such as provenance, traceability, audit trail, metadata, auditability, verifiability, and state transition provide the established vocabulary.

This Lean kernel does not redefine those terms. It gives an abstract mathematical setting in which their responsibility-relevant role can be expressed: they help preserve the information needed to inspect, audit, or verify a past decision or state transition.

### 2. Core Responsibility OS Terms

Terms such as accountability-relevant information, accountability state, and unverified conditions are Responsibility OS terms built on top of the existing vocabulary.

This Lean kernel directly supports this layer by formalizing responsibility-relevant information as information that preserves distinctions needed for retrospective inspectability.

In particular, it shows that when histories or relevant transition distinctions are forgotten, later inspection may become impossible; when those histories are retained, the relevant differences can remain inspectable.

### 3. Mathematical Responsibility OS Terms

Terms such as noncommutativity, commutativization, and information loss are the mathematical layer of the glossary.

This Lean kernel directly supports this layer.

Noncommutativity captures the fact that the order of events may matter. Commutativization captures the collapse of ordered or history-sensitive information into outputs, labels, scores, or aggregates. Information loss refers not merely to a reduction in data volume, but to the loss of distinctions that are relevant for responsibility, audit, or verification.

### 4. Real-World Information

The Lean formalization does not prove an empirical claim that all real-world information is noncommutative.

Rather, it proves a structural claim: when real-world information is modeled as a process of state transitions, and when distinguishable events and their histories are included, order-sensitive differences can be preserved as inspectable distinctions.

This is the mathematical role of the Responsibility Information Kernel: it connects the glossary's information-science vocabulary to the Responsibility OS claim that responsibility-relevant information must preserve the histories and distinctions required for later inspection.

In Japanese:

```text
このLeanは、用語集の標準語そのものを証明するものではなく、
標準語を「責任情報」に束ね直すための数理核です。
```

## What This Proves

The development proves three kinds of claims.

First, `ResponsibilityInfoKernel` proves that any nonempty transition system with at least two distinguishable events becomes order-sensitive once chronological history is included in the information state.

Second, it proves that if an observation collapses `[a, b]` and `[b, a]`, then the claim "this was exactly `a` then `b`" cannot be inspected from that observation alone, while full chronological history can make that distinction inspectable.

Third, `GenericNoncommutativity` proves that, over finite state spaces, noncommuting endomorphism pairs are generic under the uniform counting measure on all pairs of functions.

## What This Does Not Prove

This development does not prove a complete legal, ethical, or institutional theory of responsibility.

It does not formalize W3C PROV or any other information-science standard.

It does not claim that every natural, social, or AI system is fully captured by this transition-system abstraction.

It does not claim that all real-world information processes are empirically noncommutative.

It does not claim that responsibility information preserves every possible distinction.

It does not claim that full trace preservation is always required in every deployment.

It proves a mathematical kernel: selected distinctions can be lost by coarse observations, and appropriately designed responsibility information can make those distinctions retrospectively inspectable.

## Build Notes

`ResponsibilityInfoKernel.lean` imports:

```lean
import Std
import ResponsibilityOS
```

It is intended to be checked inside a Lean project where `ResponsibilityOS.lean` is available as a module. Its categorical bridge also relies on the Mathlib category-theory environment provided by `ResponsibilityOS`.

`GenericNoncommutativity.lean` imports:

```lean
import Mathlib
```

It is independent of `ResponsibilityInfoKernel.lean` and `ResponsibilityOS.lean`, but it must be checked inside a Mathlib-enabled Lean project.

Typical commands inside a configured Lake project are:

```powershell
lake env lean ResponsibilityInfoKernel.lean
lake env lean GenericNoncommutativity.lean
```

These files are not intended to be checked with a bare Lean installation that has no Mathlib or `ResponsibilityOS` module on the search path.

## Suggested One-Sentence Summary

`ResponsibilityInfoKernel` formalizes why responsibility-relevant information must preserve histories and order-sensitive distinctions for retrospective inspectability; `GenericNoncommutativity` independently shows that, in finite-state transition dynamics, noncommutativity is generic rather than exceptional.
