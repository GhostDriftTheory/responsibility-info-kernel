import Std
import ResponsibilityOS

/-!
# Responsibility Info Kernel, with categorical bridge

This file has three layers.

**Layer 1 (information-theoretic kernel).** Transition systems, traces,
`evalTrace`, output observation, responsibility-enriched observation, and
retrospective inspectability. This layer formalizes:

* transition traces can be noncommutative;
* output-only or commutative observations can collapse order distinctions;
* responsibility information can preserve selected distinctions;
* when the information is explicit enough, the distinction is retrospectively
  inspectable by a checker.

`TraceLift` shows that any nonempty transition system with two
distinguishable events becomes noncommutative once chronological history is
carried in the state, *without discarding the original dynamics*
(`trace_lift_eval_base`, `trace_lift_eval_history`).

**Layer 2 (order-pair kernel).** The concrete `commSummary` / `B_then_A` /
`A_then_B` example is generalized: for *any* event type and *any* observation
that collapses an ordered pair `[a, b]` / `[b, a]`, the "exactly a then b"
predicate becomes non-inspectable, while full history preserves it
(`order_pair_not_inspectable_from_collapsing_observation`,
`full_history_is_responsibility_info_for_any_collapsed_order_pair`). Complete
inspectability of "what exactly happened" is shown to be equivalent to
injectivity of the observation, both for set-valued observations
(`all_singleton_history_predicates_inspectable_implies_observation_injective`,
`observation_injective_implies_all_singleton_history_predicates_inspectable`)
and for information maps
(`all_singleton_history_predicates_inspectable_from_info_implies_info_injective`,
`info_injective_iff_full_history_decodable`). The latter gives a minimality
result: any information map that is completely inspectable
(`CompletelyInspectableFromInfo`) must sit at or above `fullHistoryInfo` in
the `InformationBelow` order
(`full_history_is_minimal_for_complete_history_inspectability`). So full
history is not merely *one example* of responsibility information; it is the
standard against which any sufficient information must be measured.

**Layer 3 (categorical bridge to `ResponsibilityOS`).** Chronological traces
under concatenation form a one-object category `TraceCat`. For functors out
of `TraceCat`, faithfulness is exactly trace-map injectivity
(`trace_functor_faithful_iff_trace_map_injective`), and preserving the
`ResponsibilityOS.CompletePolicy` is exactly the same thing
(`trace_preserves_complete_policy_iff_trace_map_injective`). A local policy
(`OrderPairPolicy`) shows that a single collapsed order pair already breaks
policy preservation, without requiring the full `CompletePolicy`.

The bridge back to Layer 2 is `obsOfTraceFunctor`: every `TraceCat` functor
`F` induces a Layer-2 observation `obsOfTraceFunctor F : Trace Act -> O`, and
this observation is always *compositional*
(`obsOfTraceFunctor_isCompositional`, `IsCompositionalObservation`) -- the
precise condition under which an arbitrary `obs` could be functorial in the
first place. Closing the loop,
`complete_inspectability_from_trace_functor_iff_preserves_complete_policy`
shows that complete retrospective inspectability of `obsOfTraceFunctor F`
(Layer 2) is *equivalent* to `F` preserving `ResponsibilityOS.CompletePolicy`
(Layer 3) -- not merely analogous to it.

Layer 2 is deliberately stated for *arbitrary* observations `obs : Trace Act
-> O`, which need not be compositional and therefore need not arise from any
functor. The categorical bridge applies only to the compositional
(functorial) case. This division of labor is intentional, not a gap: it is
the precise sense in which "information-theoretic kernel for arbitrary
observations" and "categorical kernel for compositional/functorial
observations" fit together.

**Dependencies.** Layers 1 and 2 do not need Mathlib and could be split into
a standalone file. Layer 3 requires Mathlib (`CategoryTheory`) and imports
`ResponsibilityOS.lean` as a module from the same project. This combined file
therefore depends on both Mathlib and `ResponsibilityOS.lean`; that is the
price of having the bridge live alongside the information-theoretic kernel in
one file. If a dependency-free standalone kernel is needed for distribution,
split Layer 3 (everything from `TraceCat` onwards) into a separate
`ResponsibilityInfoKernelBridge.lean` that imports both this file and
`ResponsibilityOS.lean`.

`TraceCat` is intentionally minimal: it is the one-object category generated
by `List Act` under concatenation (the "delooping" of the free monoid on
`Act`). It is a small but genuine instance of the `ResponsibilityOS`
framework, not a claim that every responsibility-relevant system reduces to
it.
-/

namespace ResponsibilityInfoKernel

open CategoryTheory

universe u v w z

/-- A generic transition system.  Natural, social, and AI judgment processes
can be treated as instances of this abstract shape: states, actions, and a
state update for each action. -/
structure TransitionSystem where
  State : Type u
  Act : Type v
  step : Act -> State -> State

/-- The three intended application domains for the first-layer theorem. -/
inductive JudgmentDomain where
  | natural
  | social
  | ai
deriving DecidableEq, Repr

/--
A judgment process is a transition system tagged by its domain.

The tag does not prove empirical adequacy by itself; it records the intended
reading that natural, social, and AI judgment processes are treated through the
same state-transition interface.
-/
structure JudgmentProcess where
  domain : JudgmentDomain
  State : Type u
  Act : Type v
  step : Act -> State -> State

/-- A trace is a chronological list of actions. -/
abbrev Trace (Act : Type u) := List Act

/-- The trace type of a tagged judgment process. -/
abbrev JTrace (J : JudgmentProcess.{u, v}) := Trace J.Act

/--
Evaluate a trace from left to right.

For example, `[a, b]` means: first perform `a`, then perform `b`.
-/
def evalTrace {X : Type u} {Act : Type v}
    (step : Act -> X -> X) : Trace Act -> X -> X
  | [], x => x
  | a :: rest, x => evalTrace step rest (step a x)

/-- Evaluate traces in a tagged judgment process. -/
def JEval (J : JudgmentProcess.{u, v}) : JTrace J -> J.State -> J.State :=
  evalTrace J.step

/-- Local noncommutativity at an initial state. -/
def LocallyNoncommutative {X : Type u}
    (A B : X -> X) (x : X) : Prop :=
  A (B x) ≠ B (A x)

/-- Two traces form a noncommutative transition difference at `x` when they
reach different states from the same initial state. -/
def NoncommutativeTraceDifference
    {X : Type u} {Act : Type v}
    (step : Act -> X -> X)
    (x : X)
    (t1 t2 : Trace Act) : Prop :=
  evalTrace step t1 x ≠ evalTrace step t2 x

/--
Two distinct events generate distinct two-step chronological histories.

This is the elementary list fact underlying the order-distinction theorems
below: it is *not* claimed to be deep on its own, but it is the hinge on
which the non-inspectability results in Layer 2 turn.
-/
theorem two_step_histories_are_distinct
    {Act : Type u} {a b : Act} (hab : a ≠ b) :
    ([a, b] : Trace Act) ≠ [b, a] := by
  intro h
  have hhead : a = b := by simpa using congrArg List.head? h
  exact hab hhead

/-- A transition system has at least one possible state. -/
def HasPossibleState (T : TransitionSystem.{u, v}) : Prop :=
  Nonempty T.State

/-- A transition system has at least two distinguishable events. -/
def HasTwoDistinguishableEvents (T : TransitionSystem.{u, v}) : Prop :=
  ∃ a b : T.Act, a ≠ b

/-- A transition system lifted with its chronological information history.

The lifted state keeps both the original state and the chronological
history. This is *not* a free list process detached from the original
transition system: the first component still evolves by `T.step`, as shown
by `trace_lift_eval_base`. -/
def TraceLift (T : TransitionSystem.{u, v}) : TransitionSystem.{max u v, v} where
  State := T.State × Trace T.Act
  Act := T.Act
  step := fun a s => (T.step a s.1, s.2 ++ [a])

/--
The base component of `TraceLift T` evolves exactly as `T` does: lifting to a
history-bearing state does not discard or alter the original dynamics.
-/
theorem trace_lift_eval_base (T : TransitionSystem.{u, v}) :
    ∀ (t : Trace T.Act) (x : T.State) (h : Trace T.Act),
      (evalTrace (TraceLift T).step t (x, h)).1 = evalTrace T.step t x
  | [], _, _ => rfl
  | a :: rest, x, h => trace_lift_eval_base T rest (T.step a x) (h ++ [a])

/--
The history component of `TraceLift T` is the previously recorded history
followed by the chronological trace that was just executed.
-/
theorem trace_lift_eval_history (T : TransitionSystem.{u, v}) :
    ∀ (t : Trace T.Act) (x : T.State) (h : Trace T.Act),
      (evalTrace (TraceLift T).step t (x, h)).2 = h ++ t
  | [], _, h => (List.append_nil h).symm
  | a :: rest, x, h => by
      have ih := trace_lift_eval_history T rest (T.step a x) (h ++ [a])
      simpa [List.append_assoc] using ih

/--
Any nonempty information process with two distinguishable events becomes
noncommutative once chronological history is included in the information
state.

The proof goes through `trace_lift_eval_history`: the history components of
the two evaluations are `[] ++ [a, b]` and `[] ++ [b, a]`, which are distinct
by `two_step_histories_are_distinct`. The base components are not even
inspected, which is the point: regardless of how `T.step` behaves, carrying
chronological history makes order observable.
-/
theorem trace_lift_of_any_nontrivial_information_process_is_noncommutative
    (T : TransitionSystem.{u, v})
    (hState : HasPossibleState T)
    (hEvents : HasTwoDistinguishableEvents T) :
    ∃ x : (TraceLift T).State,
    ∃ t1 t2 : Trace (TraceLift T).Act,
      evalTrace (TraceLift T).step t1 x ≠
      evalTrace (TraceLift T).step t2 x := by
  rcases hState with ⟨x0⟩
  rcases hEvents with ⟨a, b, hab⟩
  refine ⟨(x0, []), [a, b], [b, a], ?_⟩
  intro h
  have hsnd := congrArg Prod.snd h
  rw [trace_lift_eval_history T [a, b] x0 [],
      trace_lift_eval_history T [b, a] x0 []] at hsnd
  simp only [List.nil_append] at hsnd
  exact two_step_histories_are_distinct hab hsnd

/-- A property selects one side of a noncommutative trace difference. -/
structure SelectsNoncommutativeDifference
    {X : Type u} {Act : Type v}
    (step : Act -> X -> X)
    (x : X)
    (P : Trace Act -> Prop)
    (t1 t2 : Trace Act) : Prop where
  noncommutative :
    NoncommutativeTraceDifference step x t1 t2
  true_on_left :
    P t1
  false_on_right :
    ¬ P t2

/-- The kernel relation induced by an observation map. -/
def Ker {S : Type u} {Y : Type v} (f : S -> Y) : S -> S -> Prop :=
  fun a b => f a = f b

/-- Output-only observation of a trace from a fixed initial state. -/
def OutputObs
    {X : Type u} {Act : Type v} {Y : Type w}
    (step : Act -> X -> X)
    (out : X -> Y)
    (x : X) : Trace Act -> Y :=
  fun t => out (evalTrace step t x)

/-- responsibility-enriched observation: output plus auxiliary information. -/
def RespObs
    {X : Type u} {Act : Type v} {Y : Type w} {Info : Type z}
    (step : Act -> X -> X)
    (out : X -> Y)
    (info : Trace Act -> Info)
    (x : X) : Trace Act -> Y × Info :=
  fun t => (out (evalTrace step t x), info t)

/-- responsibility-enriched equality implies output-only equality. -/
theorem resp_kernel_implies_output_kernel
    {X : Type u} {Act : Type v} {Y : Type w} {Info : Type z}
    (step : Act -> X -> X)
    (out : X -> Y)
    (info : Trace Act -> Info)
    (x : X)
    {t1 t2 : Trace Act}
    (h : Ker (RespObs step out info x) t1 t2) :
    Ker (OutputObs step out x) t1 t2 := by
  exact congrArg Prod.fst h

/-- responsibility-enriched equality also implies information equality. -/
theorem resp_kernel_implies_info_kernel
    {X : Type u} {Act : Type v} {Y : Type w} {Info : Type z}
    (step : Act -> X -> X)
    (out : X -> Y)
    (info : Trace Act -> Info)
    (x : X)
    {t1 t2 : Trace Act}
    (h : Ker (RespObs step out info x) t1 t2) :
    info t1 = info t2 := by
  exact congrArg Prod.snd h

/--
If the responsibility information separates two traces, then the enriched
observation separates them even when the output component might be equal.
-/
theorem info_difference_separates_resp_observation
    {X : Type u} {Act : Type v} {Y : Type w} {Info : Type z}
    (step : Act -> X -> X)
    (out : X -> Y)
    (info : Trace Act -> Info)
    (x : X)
    {t1 t2 : Trace Act}
    (hinfo : info t1 ≠ info t2) :
    RespObs step out info x t1 ≠ RespObs step out info x t2 := by
  intro h
  exact hinfo (congrArg Prod.snd h)

/-- An information map preserves a selected distinction if it separates every
pair of traces satisfying that distinction. -/
def PreservesDistinction
    {S : Type u} {Info : Type v}
    (info : S -> Info)
    (D : S -> S -> Prop) : Prop :=
  ∀ ⦃a b : S⦄, D a b -> info a ≠ info b

/-- A preserved distinction is separated by responsibility-enriched observation. -/
theorem preserved_distinction_separates_resp_observation
    {X : Type u} {Act : Type v} {Y : Type w} {Info : Type z}
    (step : Act -> X -> X)
    (out : X -> Y)
    (info : Trace Act -> Info)
    (x : X)
    (D : Trace Act -> Trace Act -> Prop)
    (hpres : PreservesDistinction info D)
    {t1 t2 : Trace Act}
    (hd : D t1 t2) :
    RespObs step out info x t1 ≠ RespObs step out info x t2 := by
  exact info_difference_separates_resp_observation step out info x (hpres hd)

/--
A property is retrospectively inspectable from information when a Boolean
checker can decide the property by looking only at that information.
-/
def InspectableFromInfo
    {S : Type u} {Info : Type v}
    (info : S -> Info)
    (P : S -> Prop) : Prop :=
  ∃ check : Info -> Bool,
    ∀ s : S, check (info s) = true ↔ P s

/-- A property is inspectable from an observation when a Boolean checker can
decide the property using only that observed value. -/
def InspectableFromObservation
    {S : Type u} {O : Type v}
    (obs : S -> O)
    (P : S -> Prop) : Prop :=
  ∃ check : O -> Bool,
    ∀ s : S, check (obs s) = true ↔ P s

/-- A property is lost by an observation when it is not retrospectively
inspectable from that observation alone. -/
def LostByObservation
    {S : Type u} {O : Type v}
    (obs : S -> O)
    (P : S -> Prop) : Prop :=
  ¬ InspectableFromObservation obs P

/--
`info` is responsibility information for a selected distinction `P`, relative
to a commutative observation `commObs`, when `P` is lost by `commObs` but
inspectable from `info`.
-/
structure ResponsibilityInfoFor
    {S : Type u} {C : Type v} {Info : Type w}
    (commObs : S -> C)
    (info : S -> Info)
    (P : S -> Prop) : Prop where
  lost_from_commutative_observation :
    LostByObservation commObs P
  inspectable_from_responsibility_info :
    InspectableFromInfo info P

/-- If a commutative observation loses `P` and `info` makes `P` inspectable,
then `info` is responsibility information for `P`. -/
theorem responsibility_info_makes_lost_difference_inspectable
    {S : Type u} {C : Type v} {Info : Type w}
    (commObs : S -> C)
    (info : S -> Info)
    (P : S -> Prop)
    (hlost : LostByObservation commObs P)
    (hinspect : InspectableFromInfo info P) :
    ResponsibilityInfoFor commObs info P := by
  exact ⟨hlost, hinspect⟩

/-- The first-layer theorem applies to any tagged judgment process once it is
represented through traces, regardless of whether the tag is natural, social,
or AI. -/
theorem first_layer_applies_to_any_judgment_process
    (J : JudgmentProcess.{u, v})
    {C : Type w} {Info : Type z}
    (commObs : JTrace J -> C)
    (info : JTrace J -> Info)
    (P : JTrace J -> Prop)
    (hlost : LostByObservation commObs P)
    (hinspect : InspectableFromInfo info P) :
    ResponsibilityInfoFor commObs info P := by
  exact responsibility_info_makes_lost_difference_inspectable
    commObs info P hlost hinspect

/--
If an observation identifies `a` and `b`, but a property is true of `a` and
false of `b`, then that property is not inspectable from the observation alone.
-/
theorem not_inspectable_if_observation_collision
    {S : Type u} {O : Type v}
    (obs : S -> O)
    (P : S -> Prop)
    {a b : S}
    (hobs : obs a = obs b)
    (hPa : P a)
    (hPb : ¬ P b) :
    ¬ ∃ check : O -> Bool,
      ∀ s : S, check (obs s) = true ↔ P s := by
  intro h
  rcases h with ⟨check, hcheck⟩
  have ha : check (obs a) = true := (hcheck a).mpr hPa
  have hb : check (obs b) = true := by
    simpa [hobs] using ha
  have pb : P b := (hcheck b).mp hb
  exact hPb pb

/-- Collision with different truth values is exactly a loss of inspectability
from that observation. -/
theorem lost_by_observation_if_collision
    {S : Type u} {O : Type v}
    (obs : S -> O)
    (P : S -> Prop)
    {a b : S}
    (hobs : obs a = obs b)
    (hPa : P a)
    (hPb : ¬ P b) :
    LostByObservation obs P := by
  exact not_inspectable_if_observation_collision obs P hobs hPa hPb

/-! ## Layer 2: order-pair kernel

The `commSummary` / `B_then_A` / `A_then_B` example near the end of this file
is a single concrete instance. The theorems in this section generalize it to
*any* event type `Act` and *any* observation that collapses an ordered pair.
-/

/-- The exact order predicate: the trace was exactly `a` then `b`. -/
def IsThen {Act : Type u} (a b : Act) (t : Trace Act) : Prop :=
  t = [a, b]

/-- An observation collapses the order pair `a then b` / `b then a` when it
cannot distinguish the two corresponding two-step traces. -/
def CollapsesOrderPair
    {Act : Type u} {O : Type v}
    (obs : Trace Act -> O)
    (a b : Act) : Prop :=
  obs [a, b] = obs [b, a]

/--
If an observation collapses `a then b` and `b then a`, then the claim "this
was exactly a then b" is not retrospectively inspectable from that
observation -- for *any* observation whatsoever, not just `commSummary`.

This is the impossibility result at the heart of responsibility information:
the moment an observation identifies the two orders, no checker built from
that observation alone can recover which order actually happened.
-/
theorem order_pair_not_inspectable_from_collapsing_observation
    {Act : Type u} {O : Type v} {obs : Trace Act -> O} {a b : Act}
    (hab : a ≠ b) (hcollapse : CollapsesOrderPair obs a b) :
    LostByObservation obs (IsThen a b) := by
  apply lost_by_observation_if_collision obs (IsThen a b) hcollapse
  · rfl
  · intro h
    have h' : ([b, a] : Trace Act) = [a, b] := h
    have hhead : b = a := by simpa using congrArg List.head? h'
    exact hab hhead.symm

/-- Full chronological history makes the exact order predicate inspectable,
for any event type and any pair of events. -/
theorem order_pair_inspectable_from_full_history
    {Act : Type u} [DecidableEq Act] (a b : Act) :
    InspectableFromInfo (fun t : Trace Act => t) (IsThen a b) := by
  refine ⟨fun t => decide (t = [a, b]), ?_⟩
  intro t
  unfold IsThen
  by_cases h : t = [a, b]
  · simp [h]
  · simp [h]

/--
For any distinguishable event pair, full chronological history is
responsibility information for the order distinction lost by any observation
that collapses the two opposite orders.

This is the general theorem of which `full_trace_is_responsibility_info_for_order_difference`
(below, for `commSummary` and `Op.opA`/`Op.opB`) is a single instance; see
`full_trace_is_responsibility_info_for_order_difference_via_general_theorem`.
-/
theorem full_history_is_responsibility_info_for_any_collapsed_order_pair
    {Act : Type u} {O : Type v} [DecidableEq Act] {obs : Trace Act -> O}
    {a b : Act} (hab : a ≠ b) (hcollapse : CollapsesOrderPair obs a b) :
    ResponsibilityInfoFor obs (fun t : Trace Act => t) (IsThen a b) :=
  responsibility_info_makes_lost_difference_inspectable obs
    (fun t : Trace Act => t) (IsThen a b)
    (order_pair_not_inspectable_from_collapsing_observation hab hcollapse)
    (order_pair_inspectable_from_full_history a b)

/--
If every singleton history predicate "the trace was exactly `target`" is
inspectable from an observation, then the observation is injective on traces.

This is the information-theoretic form of *complete* retrospective
inspectability: being able to check "was it exactly this history?" for every
possible history is the same as the observation never identifying two
distinct histories.
-/
theorem all_singleton_history_predicates_inspectable_implies_observation_injective
    {Act : Type u} {O : Type v} (obs : Trace Act -> O)
    (hinspect : ∀ target : Trace Act,
      InspectableFromObservation obs (fun t => t = target)) :
    ∀ {t1 t2 : Trace Act}, obs t1 = obs t2 -> t1 = t2 := by
  intro t1 t2 hobs
  rcases hinspect t1 with ⟨check, hcheck⟩
  have htrue : check (obs t1) = true := (hcheck t1).mpr rfl
  have htrue2 : check (obs t2) = true := by
    simpa [hobs] using htrue
  exact ((hcheck t2).mp htrue2).symm

/--
Conversely, if an observation is injective on traces, every singleton history
predicate is inspectable from it.

Together with `all_singleton_history_predicates_inspectable_implies_observation_injective`,
this gives:

```text
(complete retrospective inspectability of "what exactly happened")
  ↔
(the observation does not collapse any distinct histories, i.e. is injective)
```
-/
theorem observation_injective_implies_all_singleton_history_predicates_inspectable
    {Act : Type u} {O : Type v} (obs : Trace Act -> O)
    (hinj : ∀ {t1 t2 : Trace Act}, obs t1 = obs t2 -> t1 = t2) :
    ∀ target : Trace Act,
      InspectableFromObservation obs (fun t => t = target) := by
  classical
  intro target
  refine ⟨fun o => decide (o = obs target), ?_⟩
  intro t
  by_cases hobs : obs t = obs target
  · have ht : t = target := hinj hobs
    simp [ht]
  · have ht : t ≠ target := fun ht => hobs (by rw [ht])
    simp [hobs, ht]

/-- Complete retrospective inspectability of an observation: every exact
history "the trace was exactly `target`" can be checked from `obs` alone.

By `all_singleton_history_predicates_inspectable_implies_observation_injective`
and `observation_injective_implies_all_singleton_history_predicates_inspectable`,
this holds iff `obs` is injective on traces. -/
def CompletelyInspectableFromObservation
    {Act : Type u} {O : Type v} (obs : Trace Act -> O) : Prop :=
  ∀ target : Trace Act, InspectableFromObservation obs (fun t => t = target)

/-- Complete retrospective inspectability of an *information* map: every
exact history "the trace was exactly `target`" can be checked from `info`
alone. -/
def CompletelyInspectableFromInfo
    {Act : Type u} {Info : Type v} (info : Trace Act -> Info) : Prop :=
  ∀ target : Trace Act, InspectableFromInfo info (fun t => t = target)

/-- `info₁` is at most as informative as `info₂`: `info₂` can always be
decoded down to `info₁`. Read `InformationBelow info₁ info₂` as
"`info₂` carries at least as much information as `info₁`". -/
def InformationBelow
    {Act : Type u} {Info₁ : Type v} {Info₂ : Type w}
    (info₁ : Trace Act -> Info₁) (info₂ : Trace Act -> Info₂) : Prop :=
  ∃ decode : Info₂ -> Info₁, ∀ t : Trace Act, decode (info₂ t) = info₁ t

/-- The full chronological history, viewed as a `Trace Act`-valued information
map. This is the canonical "preserve everything" responsibility information. -/
def fullHistoryInfo {Act : Type u} : Trace Act -> Trace Act :=
  fun t => t

/--
An observation is compositional when traces that are indistinguishable
before and after concatenation remain indistinguishable when concatenated:
if `obs t1 = obs t2` and `obs u1 = obs u2` then `obs (t1 ++ u1) = obs (t2 ++ u2)`.

An arbitrary `obs : Trace Act -> O` need *not* satisfy this. The categorical
bridge below (`obsOfTraceFunctor`) only applies to observations of this
compositional/functorial form; `obsOfTraceFunctor_isCompositional` shows that
every observation arising from a `TraceCat` functor is automatically
compositional. This is the precise division of labor between the two
kernels: the information-theoretic kernel above handles *arbitrary*
observations, while the categorical bridge handles *compositional*
(functorial) ones.
-/
def IsCompositionalObservation
    {Act : Type u} {O : Type v} (obs : Trace Act -> O) : Prop :=
  ∀ t1 t2 u1 u2 : Trace Act,
    obs t1 = obs t2 -> obs u1 = obs u2 -> obs (t1 ++ u1) = obs (t2 ++ u2)

/-- If every singleton history predicate is inspectable from an information
map, that map is injective on traces. This is the information-map analogue of
`all_singleton_history_predicates_inspectable_implies_observation_injective`. -/
theorem all_singleton_history_predicates_inspectable_from_info_implies_info_injective
    {Act : Type u} {Info : Type v} (info : Trace Act -> Info)
    (hinspect : CompletelyInspectableFromInfo info) :
    ∀ {t1 t2 : Trace Act}, info t1 = info t2 -> t1 = t2 := by
  intro t1 t2 hinfo
  rcases hinspect t1 with ⟨check, hcheck⟩
  have htrue : check (info t1) = true := (hcheck t1).mpr rfl
  have htrue2 : check (info t2) = true := by simpa [hinfo] using htrue
  exact ((hcheck t2).mp htrue2).symm

/--
An information map is injective on traces iff the full chronological history
can be decoded from it.

This is the precise sense in which "preserving enough information to recover
what exactly happened" and "being able to decode the full history" coincide.
-/
theorem info_injective_iff_full_history_decodable
    {Act : Type u} {Info : Type v} (info : Trace Act -> Info) :
    (∀ {t1 t2 : Trace Act}, info t1 = info t2 -> t1 = t2) ↔
      ∃ decode : Info -> Trace Act, ∀ t : Trace Act, decode (info t) = t := by
  constructor
  · intro hinj
    classical
    refine ⟨fun y => if h : ∃ s : Trace Act, info s = y then Classical.choose h else [], ?_⟩
    intro t
    have h : ∃ s : Trace Act, info s = info t := ⟨t, rfl⟩
    simp only [dif_pos h]
    exact hinj (Classical.choose_spec h)
  · intro hdec t1 t2 hinfo
    rcases hdec with ⟨decode, hdecode⟩
    calc
      t1 = decode (info t1) := (hdecode t1).symm
      _ = decode (info t2) := by rw [hinfo]
      _ = t2 := hdecode t2

/--
**Minimality of full chronological history.** Any information map that is
completely inspectable -- i.e. that supports checking "was the history
exactly `target`?" for every `target` -- can be decoded down to the full
history. In the `InformationBelow` order, `fullHistoryInfo` sits below every
completely-inspectable `info`.

This is the precise sense in which full history is not merely *one* example
of responsibility information: any information sufficient for complete
retrospective inspectability must carry at least as much as the full history.
-/
theorem full_history_is_minimal_for_complete_history_inspectability
    {Act : Type u} {Info : Type v} (info : Trace Act -> Info)
    (hcomplete : CompletelyInspectableFromInfo info) :
    InformationBelow fullHistoryInfo info :=
  (info_injective_iff_full_history_decodable info).mp
    (all_singleton_history_predicates_inspectable_from_info_implies_info_injective
      info hcomplete)

/-- The full chronological history is itself completely inspectable: it is a
witness showing that `CompletelyInspectableFromInfo` is satisfiable, and the
baseline that `full_history_is_minimal_for_complete_history_inspectability`
says everything else must sit above. -/
theorem full_history_is_completely_inspectable {Act : Type u} :
    CompletelyInspectableFromInfo (fullHistoryInfo (Act := Act)) := by
  classical
  intro target
  refine ⟨fun t => decide (t = target), ?_⟩
  intro t
  by_cases h : t = target
  · simp [h, fullHistoryInfo]
  · simp [h, fullHistoryInfo]

/-- An information map that identifies two distinct traces cannot be
completely inspectable: complete inspectability requires injectivity, by
`all_singleton_history_predicates_inspectable_from_info_implies_info_injective`. -/
theorem noninjective_info_cannot_be_completely_inspectable
    {Act : Type u} {Info : Type v} (info : Trace Act -> Info)
    (hnotinj : ∃ t1 t2 : Trace Act, info t1 = info t2 ∧ t1 ≠ t2) :
    ¬ CompletelyInspectableFromInfo info := by
  intro hcomplete
  rcases hnotinj with ⟨t1, t2, hinfo, hneq⟩
  exact hneq
    (all_singleton_history_predicates_inspectable_from_info_implies_info_injective
      info hcomplete hinfo)

/-! ## Concrete first-stage model -/

/-- Two primitive operations. -/
inductive Op where
  | opA
  | opB
deriving DecidableEq, Repr

abbrev OpTrace := Trace Op

/-- `[B, A]` means first `B`, then `A`. -/
def B_then_A : OpTrace :=
  [Op.opB, Op.opA]

/-- `[A, B]` means first `A`, then `B`. -/
def A_then_B : OpTrace :=
  [Op.opA, Op.opB]

/--
Commutative summary: remember only how many `A` and `B` operations occurred.
This intentionally forgets chronological order.
-/
def commSummary : OpTrace -> Nat × Nat
  | [] => (0, 0)
  | Op.opA :: rest =>
      let c := commSummary rest
      (c.1 + 1, c.2)
  | Op.opB :: rest =>
      let c := commSummary rest
      (c.1, c.2 + 1)

/-- The two traces are chronologically distinct. -/
theorem traces_are_order_distinct :
    B_then_A ≠ A_then_B := by
  decide

/-- The commutative summary collapses the chronological distinction. -/
theorem commutative_summary_collapses_order :
    commSummary B_then_A = commSummary A_then_B := by
  decide

/-- The order claim used for retrospective inspection. -/
def IsBThenA (t : OpTrace) : Prop :=
  t = B_then_A

theorem B_then_A_is_B_then_A :
    IsBThenA B_then_A := by
  rfl

theorem A_then_B_is_not_B_then_A :
    ¬ IsBThenA A_then_B := by
  unfold IsBThenA A_then_B B_then_A
  decide

/--
After commutativization, the claim "this was B then A" is not inspectable.
The summary cannot distinguish `[B, A]` from `[A, B]`.
-/
theorem order_not_inspectable_from_commutative_summary :
    ¬ ∃ check : Nat × Nat -> Bool,
      ∀ t : OpTrace, check (commSummary t) = true ↔ IsBThenA t := by
  exact not_inspectable_if_observation_collision
    commSummary
    IsBThenA
    commutative_summary_collapses_order
    B_then_A_is_B_then_A
    A_then_B_is_not_B_then_A

/-- Minimal responsibility information: preserve the full chronological trace. -/
abbrev ResponsibilityTraceInfo := OpTrace

def fullTraceInfo (t : OpTrace) : ResponsibilityTraceInfo :=
  t

/-- With the full trace preserved, the claim "this was B then A" is inspectable. -/
theorem order_inspectable_from_full_trace_info :
    InspectableFromInfo fullTraceInfo IsBThenA := by
  refine ⟨fun i => decide (i = B_then_A), ?_⟩
  intro t
  unfold fullTraceInfo IsBThenA
  by_cases h : t = B_then_A
  · simp [h]
  · simp [h]

/--
Full chronological trace is responsibility information for the order
distinction that commutative summary loses.
-/
theorem full_trace_is_responsibility_info_for_order_difference :
    ResponsibilityInfoFor commSummary fullTraceInfo IsBThenA := by
  exact responsibility_info_makes_lost_difference_inspectable
    commSummary
    fullTraceInfo
    IsBThenA
    order_not_inspectable_from_commutative_summary
    order_inspectable_from_full_trace_info

/--
The concrete `commSummary` example is an instance of the general
order-pair theorem `full_history_is_responsibility_info_for_any_collapsed_order_pair`,
with `a := Op.opB`, `b := Op.opA`, and `obs := commSummary`.

This is the formal sense in which Layer 2 subsumes the concrete example: the
same conclusion as `full_trace_is_responsibility_info_for_order_difference`
is derived here from the general theorem applied to this specific instance,
rather than proved from scratch.
-/
theorem full_trace_is_responsibility_info_for_order_difference_via_general_theorem :
    ResponsibilityInfoFor commSummary fullTraceInfo IsBThenA :=
  full_history_is_responsibility_info_for_any_collapsed_order_pair
    (a := Op.opB) (b := Op.opA)
    (by decide)
    commutative_summary_collapses_order

/-- Concrete noncommutative operations on natural-number states. -/
def evalOpNat : Op -> Nat -> Nat
  | Op.opA, n => n + 1
  | Op.opB, n => 2 * n

def evalOpTraceNat : OpTrace -> Nat -> Nat :=
  evalTrace evalOpNat

/-- The two chronological orders reach different states from `1`. -/
theorem noncommutative_state_transition_example :
    evalOpTraceNat B_then_A 1 ≠ evalOpTraceNat A_then_B 1 := by
  decide

/-- The order property selects one side of an actual noncommutative transition
difference. -/
theorem IsBThenA_selects_noncommutative_order_difference :
    SelectsNoncommutativeDifference
      evalOpNat
      1
      IsBThenA
      B_then_A
      A_then_B := by
  exact
    { noncommutative := noncommutative_state_transition_example
      true_on_left := B_then_A_is_B_then_A
      false_on_right := A_then_B_is_not_B_then_A }

/-- Output-only observation that intentionally collapses all states. -/
def outUnit : Nat -> Unit :=
  fun _ => ()

/-- Output-only abstraction collapses the noncommutative transition example. -/
theorem output_only_collapses_noncommutative_example :
    OutputObs evalOpNat outUnit 1 B_then_A =
    OutputObs evalOpNat outUnit 1 A_then_B := by
  rfl

/-- A less artificial output: a pass/fail label that records only whether the
resulting state meets a threshold.  Both `3` and `4` pass. -/
def outPassLabel (n : Nat) : Bool :=
  decide (3 <= n)

/-- A label-only output can also collapse the noncommutative example. -/
theorem label_output_collapses_noncommutative_example :
    OutputObs evalOpNat outPassLabel 1 B_then_A =
    OutputObs evalOpNat outPassLabel 1 A_then_B := by
  native_decide

/-- responsibility-enriched observation separates the same traces even when
the output is a realistic pass/fail label. -/
theorem responsibility_observation_separates_label_output_example :
    RespObs evalOpNat outPassLabel fullTraceInfo 1 B_then_A ≠
    RespObs evalOpNat outPassLabel fullTraceInfo 1 A_then_B := by
  decide

/-- A tagged instance of the first-layer transition model. -/
def opNatJudgmentProcess (domain : JudgmentDomain) : JudgmentProcess where
  domain := domain
  State := Nat
  Act := Op
  step := evalOpNat

/-- Natural-domain reading: a coarse visible label can hide ordered changes. -/
def naturalJudgmentProcess : JudgmentProcess :=
  opNatJudgmentProcess JudgmentDomain.natural

/-- Social-domain reading: an institutional process can be treated the same way. -/
def socialJudgmentProcess : JudgmentProcess :=
  opNatJudgmentProcess JudgmentDomain.social

/-- AI-domain reading: a model or automated decision process is also a
state-transition process at this abstraction layer. -/
def aiJudgmentProcess : JudgmentProcess :=
  opNatJudgmentProcess JudgmentDomain.ai

theorem full_trace_is_responsibility_info_for_natural_example :
    ResponsibilityInfoFor
      (fun t : JTrace naturalJudgmentProcess => commSummary t)
      (fun t : JTrace naturalJudgmentProcess => fullTraceInfo t)
      IsBThenA := by
  simpa [naturalJudgmentProcess, opNatJudgmentProcess]
    using full_trace_is_responsibility_info_for_order_difference

theorem full_trace_is_responsibility_info_for_social_example :
    ResponsibilityInfoFor
      (fun t : JTrace socialJudgmentProcess => commSummary t)
      (fun t : JTrace socialJudgmentProcess => fullTraceInfo t)
      IsBThenA := by
  simpa [socialJudgmentProcess, opNatJudgmentProcess]
    using full_trace_is_responsibility_info_for_order_difference

theorem full_trace_is_responsibility_info_for_ai_example :
    ResponsibilityInfoFor
      (fun t : JTrace aiJudgmentProcess => commSummary t)
      (fun t : JTrace aiJudgmentProcess => fullTraceInfo t)
      IsBThenA := by
  simpa [aiJudgmentProcess, opNatJudgmentProcess]
    using full_trace_is_responsibility_info_for_order_difference

/-- Full trace information distinguishes the two orders. -/
theorem responsibility_info_distinguishes_order_example :
    fullTraceInfo B_then_A ≠ fullTraceInfo A_then_B := by
  decide

/-- responsibility-enriched observation separates what output-only observation collapses. -/
theorem responsibility_observation_separates_noncommutative_example :
    RespObs evalOpNat outUnit fullTraceInfo 1 B_then_A ≠
    RespObs evalOpNat outUnit fullTraceInfo 1 A_then_B := by
  decide

/--
Bundled first-stage theorem.

There are two noncommutative traces whose state results differ, whose
commutative summary and output-only observation collapse together, and whose
responsibility-enriched observation remains distinct.
-/
theorem output_only_and_commutative_abstraction_can_collapse_noncommutative_responsibility_states :
    evalOpTraceNat B_then_A 1 ≠ evalOpTraceNat A_then_B 1 ∧
    commSummary B_then_A = commSummary A_then_B ∧
    OutputObs evalOpNat outUnit 1 B_then_A =
      OutputObs evalOpNat outUnit 1 A_then_B ∧
    fullTraceInfo B_then_A ≠ fullTraceInfo A_then_B ∧
    RespObs evalOpNat outUnit fullTraceInfo 1 B_then_A ≠
      RespObs evalOpNat outUnit fullTraceInfo 1 A_then_B := by
  constructor
  · exact noncommutative_state_transition_example
  · constructor
    · exact commutative_summary_collapses_order
    · constructor
      · exact output_only_collapses_noncommutative_example
      · constructor
        · exact responsibility_info_distinguishes_order_example
        · exact responsibility_observation_separates_noncommutative_example

/-! ## Layer 3: categorical bridge to `ResponsibilityOS`

This section connects the order-pair / injectivity results of Layer 2 to the
categorical kernel in `ResponsibilityOS.lean`: `ResponsibilityOS.Faithful`,
`ResponsibilityOS.ObservationPolicy`, `ResponsibilityOS.PreservesPolicy`, and
`ResponsibilityOS.CompletePolicy`.

`TraceCat Act` is the one-object category whose morphisms from the unique
object to itself are chronological traces (`List Act`), with composition
given by concatenation. This is the "delooping" of the free monoid on `Act`:
it is a small, concrete, and genuine instance of a category, not a
restatement of the list facts above under new names. -/

/-- The one-object category generated by chronological traces over `Act`.
Morphisms from the unique object to itself are traces; composition is
chronological concatenation, with the empty trace as identity. -/
abbrev TraceCat (_ : Type u) := PUnit

instance traceCatCategory (Act : Type u) : Category (TraceCat Act) where
  Hom _ _ := Trace Act
  id _ := []
  comp f g := f ++ g
  id_comp := by intro X Y f; simp
  comp_id := by intro X Y f; simp
  assoc := by intro W X Y Z f g h; simp [List.append_assoc]

/--
For a functor out of the one-object trace category, faithfulness is exactly
injectivity of the induced map on chronological traces.

This is where Layer 2's "observation injective on traces" statement becomes
literally a statement about `Functor.Faithful`.
-/
theorem trace_functor_faithful_iff_trace_map_injective
    {Act : Type u} {C : Type w} [Category C]
    (F : TraceCat Act ⥤ C) :
    F.Faithful ↔
      ∀ t1 t2 : Trace Act,
        F.map (X := PUnit.unit) (Y := PUnit.unit) t1 =
        F.map (X := PUnit.unit) (Y := PUnit.unit) t2 → t1 = t2 := by
  constructor
  · intro hF t1 t2 hmap
    exact hF.map_injective hmap
  · intro hinj
    exact
      { map_injective := by
          intro X Y f g hmap
          cases X
          cases Y
          exact hinj f g hmap }

/--
Preserving the complete `ResponsibilityOS` policy on the trace category is
exactly injectivity on chronological traces.

Combined with Layer 2 (`all_singleton_history_predicates_inspectable_implies_observation_injective`
and `observation_injective_implies_all_singleton_history_predicates_inspectable`),
this gives the three-step chain:

```text
complete retrospective inspectability of traces
  ↔  observation injective on traces                  (Layer 2)
  ↔  Functor.Faithful                                  (trace_functor_faithful_iff_trace_map_injective)
  ↔  PreservesPolicy F (CompletePolicy (TraceCat Act))  (ResponsibilityOS.preserves_complete_policy_iff_faithful)
```
-/
theorem trace_preserves_complete_policy_iff_trace_map_injective
    {Act : Type u} {C : Type w} [Category C]
    (F : TraceCat Act ⥤ C) :
    ResponsibilityOS.PreservesPolicy F
      (ResponsibilityOS.CompletePolicy (TraceCat Act)) ↔
      ∀ t1 t2 : Trace Act,
        F.map (X := PUnit.unit) (Y := PUnit.unit) t1 =
        F.map (X := PUnit.unit) (Y := PUnit.unit) t2 → t1 = t2 :=
  (ResponsibilityOS.preserves_complete_policy_iff_faithful F).trans
    (trace_functor_faithful_iff_trace_map_injective F)

/--
The local order policy: "`a` then `b`" and "`b` then `a`" are policy-relevant
responsibility distinctions on the trace category.

This is weaker than `CompletePolicy`: it only requires this single ordered
pair to remain distinguishable, not every pair of distinct traces.
`two_step_histories_are_distinct` provides the required soundness proof
(policy-relevant pairs really are distinct morphisms).
-/
def OrderPairPolicy {Act : Type u} (a b : Act) (hab : a ≠ b) :
    ResponsibilityOS.ObservationPolicy (TraceCat Act) where
  relevant := fun {_ _} f g =>
    (f = [a, b] ∧ g = [b, a]) ∨ (f = [b, a] ∧ g = [a, b])
  sound := by
    intro X Y f g hrel
    rcases hrel with h | h
    · obtain ⟨rfl, rfl⟩ := h
      exact two_step_histories_are_distinct hab
    · obtain ⟨rfl, rfl⟩ := h
      intro hEq
      exact two_step_histories_are_distinct hab hEq.symm

/--
A functor that collapses the order pair `a then b` / `b then a` cannot
preserve the corresponding local responsibility policy on the trace category.

This is the categorical restatement of
`order_pair_not_inspectable_from_collapsing_observation`: collapsing this one
ordered pair is already enough to break `PreservesPolicy`, without needing the
full `CompletePolicy`.
-/
theorem trace_functor_collapsing_order_pair_does_not_preserve_order_policy
    {Act : Type u} {C : Type w} [Category C]
    (F : TraceCat Act ⥤ C) {a b : Act} (hab : a ≠ b)
    (hcollapse :
      F.map (X := PUnit.unit) (Y := PUnit.unit) ([a, b] : Trace Act) =
      F.map (X := PUnit.unit) (Y := PUnit.unit) ([b, a] : Trace Act)) :
    ¬ ResponsibilityOS.PreservesPolicy F (OrderPairPolicy a b hab) := by
  intro hpres
  have hrel : (OrderPairPolicy a b hab).relevant
      (X := PUnit.unit) (Y := PUnit.unit)
      ([a, b] : Trace Act) ([b, a] : Trace Act) := Or.inl ⟨rfl, rfl⟩
  exact (hpres hrel) hcollapse

/-! ### From `TraceCat` functors back to Layer-2 observations

`obsOfTraceFunctor` turns a `TraceCat`-functor into a `Trace Act -> O`
observation in the sense of Layer 2, by reading off its action on morphisms
out of the unique object. This is the concrete sense in which "an arbitrary
`obs : Trace Act -> O`" (Layer 2) and "a functor `F : TraceCat Act ⥤ C`"
(Layer 3) are connected: every `TraceCat`-functor gives rise to a Layer-2
observation, and `obsOfTraceFunctor_isCompositional` shows this observation is
always compositional (`IsCompositionalObservation`). The converse -- lifting
an arbitrary, possibly non-compositional `obs` to a functor -- is not claimed
and is not true in general; that division of labor is intentional. -/

/-- The set-valued observation induced by a `TraceCat` functor: the image of a
trace under `F.map`, read as a Layer-2 observation `Trace Act -> O`. -/
def obsOfTraceFunctor
    {Act : Type u} {C : Type w} [Category C] (F : TraceCat Act ⥤ C) :
    Trace Act -> (F.obj PUnit.unit ⟶ F.obj PUnit.unit) :=
  fun t => F.map (X := PUnit.unit) (Y := PUnit.unit) t

/-- Every observation arising from a `TraceCat` functor is compositional, by
functoriality (`F.map_comp`): images of indistinguishable traces compose to
images of indistinguishable concatenations. -/
theorem obsOfTraceFunctor_isCompositional
    {Act : Type u} {C : Type w} [Category C] (F : TraceCat Act ⥤ C) :
    IsCompositionalObservation (obsOfTraceFunctor F) := by
  intro t1 t2 u1 u2 h1 h2
  have e1 : obsOfTraceFunctor F (t1 ++ u1) =
      obsOfTraceFunctor F t1 ≫ obsOfTraceFunctor F u1 :=
    F.map_comp t1 u1
  have e2 : obsOfTraceFunctor F (t2 ++ u2) =
      obsOfTraceFunctor F t2 ≫ obsOfTraceFunctor F u2 :=
    F.map_comp t2 u2
  rw [e1, e2, h1, h2]

/-- If a `TraceCat` functor collapses the order pair `a then b` / `b then a`,
then the induced Layer-2 observation `obsOfTraceFunctor F` collapses it too. -/
theorem functor_collapse_gives_observation_collapse
    {Act : Type u} {C : Type w} [Category C] (F : TraceCat Act ⥤ C)
    {a b : Act}
    (hcollapse :
      F.map (X := PUnit.unit) (Y := PUnit.unit) ([a, b] : Trace Act) =
      F.map (X := PUnit.unit) (Y := PUnit.unit) ([b, a] : Trace Act)) :
    CollapsesOrderPair (obsOfTraceFunctor F) a b :=
  hcollapse

/-- If a `TraceCat` functor collapses the order pair `a then b` / `b then a`,
the claim "this was exactly a then b" is not retrospectively inspectable from
the induced observation `obsOfTraceFunctor F`. -/
theorem order_pair_not_inspectable_from_collapsing_trace_functor
    {Act : Type u} {C : Type w} [Category C] (F : TraceCat Act ⥤ C)
    {a b : Act} (hab : a ≠ b)
    (hcollapse :
      F.map (X := PUnit.unit) (Y := PUnit.unit) ([a, b] : Trace Act) =
      F.map (X := PUnit.unit) (Y := PUnit.unit) ([b, a] : Trace Act)) :
    LostByObservation (obsOfTraceFunctor F) (IsThen a b) :=
  order_pair_not_inspectable_from_collapsing_observation hab
    (functor_collapse_gives_observation_collapse F hcollapse)

/-- Against any `TraceCat` functor that collapses the order pair `a then b` /
`b then a`, full chronological history is responsibility information for the
"exactly a then b" distinction. -/
theorem full_history_is_responsibility_info_against_collapsing_trace_functor
    {Act : Type u} {C : Type w} [Category C] [DecidableEq Act]
    (F : TraceCat Act ⥤ C) {a b : Act} (hab : a ≠ b)
    (hcollapse :
      F.map (X := PUnit.unit) (Y := PUnit.unit) ([a, b] : Trace Act) =
      F.map (X := PUnit.unit) (Y := PUnit.unit) ([b, a] : Trace Act)) :
    ResponsibilityInfoFor (obsOfTraceFunctor F) (fun t : Trace Act => t)
      (IsThen a b) :=
  responsibility_info_makes_lost_difference_inspectable
    (obsOfTraceFunctor F) (fun t : Trace Act => t) (IsThen a b)
    (order_pair_not_inspectable_from_collapsing_trace_functor F hab hcollapse)
    (order_pair_inspectable_from_full_history a b)

/-! ### Complete inspectability ↔ Faithful ↔ `PreservesPolicy CompletePolicy`

This closes the loop opened in Layer 2: "complete retrospective
inspectability of traces" (an information-theoretic statement about
`obsOfTraceFunctor F`) is equivalent both to `F.Faithful` and to `F` preserving
`ResponsibilityOS.CompletePolicy`. The chain is:

```text
CompletelyInspectableFromObservation (obsOfTraceFunctor F)
  ↔ (∀ t1 t2, obsOfTraceFunctor F t1 = obsOfTraceFunctor F t2 → t1 = t2)   [Layer 2]
  ↔ F.Faithful                                                              [trace_functor_faithful_iff_trace_map_injective]
  ↔ ResponsibilityOS.PreservesPolicy F (ResponsibilityOS.CompletePolicy (TraceCat Act))
                                                                             [ResponsibilityOS.preserves_complete_policy_iff_faithful]
```
-/

/-- Complete retrospective inspectability of `obsOfTraceFunctor F` is exactly
`F.Faithful`. -/
theorem complete_inspectability_from_trace_functor_iff_faithful
    {Act : Type u} {C : Type w} [Category C] (F : TraceCat Act ⥤ C) :
    CompletelyInspectableFromObservation (obsOfTraceFunctor F) ↔ F.Faithful := by
  constructor
  · intro hcomplete
    exact (trace_functor_faithful_iff_trace_map_injective F).mpr
      (fun t1 t2 hmap =>
        all_singleton_history_predicates_inspectable_implies_observation_injective
          (obsOfTraceFunctor F) hcomplete hmap)
  · intro hfaithful
    exact observation_injective_implies_all_singleton_history_predicates_inspectable
      (obsOfTraceFunctor F)
      (fun hmap =>
        (trace_functor_faithful_iff_trace_map_injective F).mp hfaithful _ _ hmap)

/-- Complete retrospective inspectability of `obsOfTraceFunctor F` is exactly
`F` preserving `ResponsibilityOS.CompletePolicy` on `TraceCat Act`.

This is the formal endpoint of the bridge: an information-theoretic statement
about what can be checked from `obsOfTraceFunctor F` (Layer 2) is literally
equivalent to a policy-preservation statement in `ResponsibilityOS.lean`
(Layer 3). -/
theorem complete_inspectability_from_trace_functor_iff_preserves_complete_policy
    {Act : Type u} {C : Type w} [Category C] (F : TraceCat Act ⥤ C) :
    CompletelyInspectableFromObservation (obsOfTraceFunctor F) ↔
      ResponsibilityOS.PreservesPolicy F
        (ResponsibilityOS.CompletePolicy (TraceCat Act)) :=
  (complete_inspectability_from_trace_functor_iff_faithful F).trans
    (ResponsibilityOS.preserves_complete_policy_iff_faithful F).symm

end ResponsibilityInfoKernel
