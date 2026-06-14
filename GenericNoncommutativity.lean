import Mathlib

/-!
# Generic noncommutativity of finite-state transition pairs

This file is **independent** of `ResponsibilityInfoKernel.lean` and
`ResponsibilityOS.lean`. It proves a finite-combinatorics genericity result:

> Model two "events" as arbitrary endomorphisms `f g : S -> S` of a finite
> state space `S`. As `|S|` grows, the proportion of commuting pairs `(f, g)`
> (i.e. `f ∘ g = g ∘ f`) shrinks toward `0`, so the proportion of
> *noncommuting* pairs tends to `1`.

The core counting argument
(`commuting_right_fiber_card_le`): fix `f ≠ id`. Choose `x` with `f x ≠ x`
and set `y = f x`. If `g` commutes with `f`, then `g y = g (f x) = f (g x)`,
so `g y` is *forced* by the value of `g x`. Hence `g` is determined by its
restriction to `S \ {y}`, giving at most `|S|^(|S|-1)` such `g`.

From this, `commuting_endopairs_card_bound` bounds the total number of
commuting pairs by `n^n + (n^n - 1) * n^(n-1)` (where `n = |S|`), and
`generic_bound_arithmetic_general` / `noncommuting_pairs_at_least_99_percent`
turn this into explicit ratio bounds: for `n` large enough, at least a
`K/(K+1)` fraction of pairs are noncommuting, for any `K`.

## Relationship to `ResponsibilityInfoKernel.lean`

The kernel's `TraceLift` theorem
(`trace_lift_of_any_nontrivial_information_process_is_noncommutative`) is a
*constructive existence* statement: any nonempty process with two
distinguishable events has *some* noncommuting pair of traces once history is
carried. This file proves a complementary *genericity* statement about the
space of all possible transition functions on a finite state space: when
events are modeled as arbitrary endomorphisms of `S`, commuting pairs are the
exception, not the rule, and this exceptionality becomes total as `|S|` grows.

**This file's results are not used by, and the kernel's claims do not depend
on, this file.** It is offered as an independent, fully proved (no `sorry`)
companion result about finite-state transition dynamics in general.

**Scope.** These statements are about the space `S -> S` of *all* functions
under the uniform/"all pairs" counting measure. They are not statements about
the distribution of any specific real-world pair of operations: a deliberately
designed pair of operations (e.g. two operations chosen precisely because they
commute) is not "generic" in this sense, and this file does not claim
otherwise.
-/

namespace GenericNoncommutativity

universe u

/-- Two state transitions commute when applying `f` then `g` is the same as
applying `g` then `f` at every state. -/
def CommuteActions {S : Type u} (f g : S -> S) : Prop :=
  ∀ x : S, f (g x) = g (f x)

/-- Two state transitions are noncommuting when there is at least one state
where their two chronological orders differ. -/
def NoncommuteActions {S : Type u} (f g : S -> S) : Prop :=
  ∃ x : S, f (g x) ≠ g (f x)

/-- Pairs of endomorphisms on a state space. -/
abbrev EndoPair (S : Type u) :=
  (S -> S) × (S -> S)

/-- The subtype of commuting endomorphism pairs. -/
abbrev CommutingEndoPairs (S : Type u) :=
  {p : EndoPair S // CommuteActions p.1 p.2}

/-- The subtype of noncommuting endomorphism pairs. -/
abbrev NoncommutingEndoPairs (S : Type u) :=
  {p : EndoPair S // NoncommuteActions p.1 p.2}

noncomputable instance commutingRightFiberFintype
    {S : Type u} [Fintype S] [DecidableEq S] (f : S -> S) :
    Fintype {g : S -> S // CommuteActions f g} := by
  classical
  infer_instance

noncomputable instance commutingEndoPairsFintype
    {S : Type u} [Fintype S] [DecidableEq S] :
    Fintype (CommutingEndoPairs S) := by
  classical
  infer_instance

noncomputable instance noncommutingEndoPairsFintype
    {S : Type u} [Fintype S] [DecidableEq S] :
    Fintype (NoncommutingEndoPairs S) := by
  classical
  infer_instance

/-- On any state space, noncommuting is the negation of commuting. -/
theorem noncommute_iff_not_commute
    {S : Type u} (f g : S -> S) :
    NoncommuteActions f g ↔ ¬ CommuteActions f g := by
  constructor
  · intro h hcomm
    rcases h with ⟨x, hx⟩
    exact hx (hcomm x)
  · intro hnot
    by_contra hnone
    apply hnot
    intro x
    by_contra hx
    exact hnone ⟨x, hx⟩

/-- A non-identity endomorphism moves at least one state. -/
theorem nonidentity_has_moved_point
    {S : Type u}
    (f : S -> S) (hf : f ≠ id) :
    ∃ x : S, f x ≠ x := by
  by_contra h
  apply hf
  funext x
  by_cases hx : f x = x
  · exact hx
  · exact False.elim (h ⟨x, hx⟩)

/-! ## The right-fiber bound -/

/-- Commuting pairs are equivalent to choosing `f`, then choosing a `g`
commuting with that `f`. -/
def commutingPairsEquivSigma (S : Type u) :
    CommutingEndoPairs S ≃ Σ f : S -> S, {g : S -> S // CommuteActions f g} where
  toFun p := ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
  invFun q := ⟨(q.1, q.2.1), q.2.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/--
Fix a non-identity transition `f : S -> S`.

Then the number of transitions `g : S -> S` commuting with `f` is at most
`|S|^(|S|-1)`.

Reason: choose `x` with `f x ≠ x`, put `y = f x`. If `g` commutes with `f`,
then `g y = g (f x) = f (g x)`. So once `g` is known away from `y`, its value
at `y` is forced. Thus commuting `g`s inject into functions
`{z // z ≠ y} -> S`, of which there are `|S|^(|S|-1)`.
-/
theorem commuting_right_fiber_card_le
    {S : Type u} [Fintype S] [DecidableEq S]
    (f : S -> S) (hf : f ≠ id) :
    Fintype.card {g : S -> S // CommuteActions f g}
      ≤ (Fintype.card S) ^ (Fintype.card S - 1) := by
  classical
  obtain ⟨x, hx⟩ := nonidentity_has_moved_point f hf
  set y : S := f x with hy
  have hxy : x ≠ y := fun h => hx h.symm
  let restrictAway : {g : S -> S // CommuteActions f g} -> ({z : S // z ≠ y} -> S) :=
    fun g z => g.1 z.1
  have hinj : Function.Injective restrictAway := by
    intro g₁ g₂ hres
    apply Subtype.ext
    funext z
    by_cases hz : z = y
    · subst hz
      have c₁ : f (g₁.1 x) = g₁.1 y := g₁.2 x
      have c₂ : f (g₂.1 x) = g₂.1 y := g₂.2 x
      have hgx : g₁.1 x = g₂.1 x := congrFun hres ⟨x, hxy⟩
      rw [← c₁, ← c₂, hgx]
    · exact congrFun hres ⟨z, hz⟩
  have hcardInject :
      Fintype.card {g : S -> S // CommuteActions f g}
        ≤ Fintype.card ({z : S // z ≠ y} -> S) :=
    Fintype.card_le_of_injective restrictAway hinj
  have hcardAway : Fintype.card {z : S // z ≠ y} = Fintype.card S - 1 := by
    have hfilter_eq : (Finset.univ.filter (· ≠ y)) = Finset.univ.erase y := by
      ext z
      simp [Finset.mem_filter, Finset.mem_erase]
    rw [Fintype.card_subtype, hfilter_eq,
        Finset.card_erase_of_mem (Finset.mem_univ y), Finset.card_univ]
  calc
    Fintype.card {g : S -> S // CommuteActions f g}
        ≤ Fintype.card ({z : S // z ≠ y} -> S) := hcardInject
    _ = (Fintype.card S) ^ (Fintype.card {z : S // z ≠ y}) := Fintype.card_fun
    _ = (Fintype.card S) ^ (Fintype.card S - 1) := by rw [hcardAway]

/-! ## Total commuting-pair count -/

/--
Upper bound for commuting transition pairs on a finite state space.

Let `n = |S|`. There are `n^n` possible endomorphisms `S -> S`.

* If `f = id`, all `n^n` choices of `g` commute with it.
* If `f ≠ id`, at most `n^(n-1)` choices of `g` commute with it
  (`commuting_right_fiber_card_le`).

Therefore commuting pairs are bounded by `n^n + (n^n - 1) * n^(n-1)`.
-/
theorem commuting_endopairs_card_bound
    {S : Type u} [Fintype S] [DecidableEq S] :
    Fintype.card (CommutingEndoPairs S)
      ≤ (Fintype.card S) ^ (Fintype.card S)
        + ((Fintype.card S) ^ (Fintype.card S) - 1)
            * (Fintype.card S) ^ (Fintype.card S - 1) := by
  classical
  set n := Fintype.card S with hn_def
  have hsplit :
      Fintype.card (CommutingEndoPairs S)
        = ∑ f : S -> S, Fintype.card {g : S -> S // CommuteActions f g} := by
    rw [Fintype.card_congr (commutingPairsEquivSigma S), Fintype.card_sigma]
  have htotalEndo : Fintype.card (S -> S) = n ^ n := Fintype.card_fun
  have hid :
      Fintype.card {g : S -> S // CommuteActions (id : S -> S) g} = n ^ n := by
    rw [← htotalEndo]
    apply Fintype.card_congr
    exact
      { toFun := fun g => g.1
        invFun := fun g => ⟨g, fun _ => rfl⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hnonid :
      ∀ f : S -> S, f ≠ id ->
        Fintype.card {g : S -> S // CommuteActions f g} ≤ n ^ (n - 1) :=
    fun f hf => commuting_right_fiber_card_le f hf
  have hmem : (id : S -> S) ∈ (Finset.univ : Finset (S -> S)) := Finset.mem_univ _
  have hsum_split :
      ∑ f : S -> S, Fintype.card {g : S -> S // CommuteActions f g}
        = Fintype.card {g : S -> S // CommuteActions (id : S -> S) g}
          + Finset.sum (Finset.univ.erase (id : S -> S))
              (fun f => Fintype.card {g : S -> S // CommuteActions f g}) := by
    conv_lhs => rw [← Finset.insert_erase hmem]
    rw [Finset.sum_insert (Finset.notMem_erase _ _)]
  have hrest_bound :
      Finset.sum (Finset.univ.erase (id : S -> S))
          (fun f => Fintype.card {g : S -> S // CommuteActions f g})
        ≤ Finset.sum (Finset.univ.erase (id : S -> S)) (fun _f => n ^ (n - 1)) := by
    apply Finset.sum_le_sum
    intro f hf
    exact hnonid f (Finset.ne_of_mem_erase hf)
  have hrest_card :
      Finset.sum (Finset.univ.erase (id : S -> S)) (fun _f => n ^ (n - 1))
        = (n ^ n - 1) * n ^ (n - 1) := by
    simp [Finset.sum_const, Finset.card_erase_of_mem hmem, Finset.card_univ, htotalEndo]
  calc
    Fintype.card (CommutingEndoPairs S)
        = ∑ f : S -> S, Fintype.card {g : S -> S // CommuteActions f g} := hsplit
    _ = Fintype.card {g : S -> S // CommuteActions (id : S -> S) g}
          + Finset.sum (Finset.univ.erase (id : S -> S))
              (fun f => Fintype.card {g : S -> S // CommuteActions f g}) := hsum_split
    _ ≤ n ^ n + Finset.sum (Finset.univ.erase (id : S -> S)) (fun _f => n ^ (n - 1)) := by
        rw [hid]; exact Nat.add_le_add_left hrest_bound _
    _ = n ^ n + (n ^ n - 1) * n ^ (n - 1) := by rw [hrest_card]

/-! ## Commuting / noncommuting partition -/

/-- Commuting and noncommuting pairs partition all endomorphism pairs:
`|NoncommutingEndoPairs S| = |EndoPair S| - |CommutingEndoPairs S|`. -/
theorem commuting_noncommuting_partition_card
    {S : Type u} [Fintype S] [DecidableEq S] :
    Fintype.card (NoncommutingEndoPairs S)
      = Fintype.card (EndoPair S) - Fintype.card (CommutingEndoPairs S) := by
  classical
  have hequiv :
      NoncommutingEndoPairs S ≃ {p : EndoPair S // ¬ CommuteActions p.1 p.2} :=
    Equiv.subtypeEquivRight (fun p => noncommute_iff_not_commute p.1 p.2)
  rw [Fintype.card_congr hequiv]
  exact Fintype.card_subtype_compl (fun p : EndoPair S => CommuteActions p.1 p.2)

theorem generic_ratio_from_commuting_bound
    (K T C N : Nat)
    (hpart : N = T - C)
    (hKC : (K + 1) * C ≤ T) :
    K * T ≤ (K + 1) * N := by
  rw [hpart]
  have hC_le_T : C ≤ T := by
    calc
      C = 1 * C := (one_mul C).symm
      _ ≤ (K + 1) * C := Nat.mul_le_mul_right C (by omega)
      _ ≤ T := hKC
  have hsplit : T = C + (T - C) := (Nat.add_sub_of_le hC_le_T).symm
  have hKCsum : C + K * C ≤ C + (T - C) := by
    have hKC' : (K + 1) * C ≤ C + (T - C) := by
      rw [hsplit] at hKC
      exact hKC
    have hcomm : C + K * C = (K + 1) * C := by
      ring
    simpa [hcomm] using hKC'
  have hKN : K * C ≤ T - C := Nat.le_of_add_le_add_left hKCsum
  calc
    K * T = K * (C + (T - C)) := congrArg (fun q => K * q) hsplit
    _ = K * C + K * (T - C) := by rw [Nat.mul_add]
    _ ≤ (T - C) + K * (T - C) := Nat.add_le_add_right hKN _
    _ = (K + 1) * (T - C) := by
      ring

/-! ## Arithmetic: the genericity ratio bound

`generic_bound_arithmetic_general` is the pure `Nat` arithmetic fact needed to
turn `commuting_endopairs_card_bound` into a ratio bound: for `K ≥ 1` and
`n ≥ K + 2`,

```text
(K + 1) * (n^n + (n^n - 1) * n^(n-1)) ≤ n^n * n^n.
```

Writing `n = m + 1` and `k = (m+1)^m = n^(n-1)`, the bound `n^n = k * n`
reduces this to the core inequality `(K+1)*(1+k) ≤ n*k`, which holds because
`k ≥ n ≥ K + 2 > K + 1` and `n - (K+1) ≥ 1` (from `n ≥ K+2`), so
`(n-(K+1))*k ≥ k ≥ K+1`.
-/

theorem generic_bound_arithmetic_general (K n : Nat) (hK : 1 ≤ K) (hn : K + 2 ≤ n) :
    (K + 1) * (n ^ n + (n ^ n - 1) * n ^ (n - 1)) ≤ n ^ n * n ^ n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : K + 1 ≤ m := by omega
  have hsub : (m + 1) - 1 = m := rfl
  have hpow : (m + 1) ^ (m + 1) = (m + 1) ^ m * (m + 1) := pow_succ (m + 1) m
  have hge : (m + 1) ≤ (m + 1) ^ m := by
    calc
      (m + 1) = (m + 1) ^ 1 := (pow_one _).symm
      _ ≤ (m + 1) ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  rw [hsub, hpow]
  set k := (m + 1) ^ m with hk_def
  have hcore : (K + 1) * (1 + k) ≤ (m + 1) * k := by
    have h1 : 1 ≤ m - K := by omega
    have h5 : (m + 1) * k = (m - K) * k + (K + 1) * k := by
      rw [← add_mul]
      congr 1
      omega
    have h4 : K + 1 ≤ (m - K) * k := by
      calc
        (K + 1 : Nat) ≤ k := le_trans (by omega) hge
        _ = 1 * k := (one_mul k).symm
        _ ≤ (m - K) * k := Nat.mul_le_mul h1 (le_refl k)
    calc
      (K + 1) * (1 + k) = (K + 1) + (K + 1) * k := by ring
      _ ≤ (m - K) * k + (K + 1) * k := Nat.add_le_add_right h4 _
      _ = (m + 1) * k := h5.symm
  have hle : (k * (m + 1) - 1) * k ≤ k * (m + 1) * k :=
    Nat.mul_le_mul (Nat.sub_le _ _) (le_refl k)
  calc
    (K + 1) * (k * (m + 1) + (k * (m + 1) - 1) * k)
        ≤ (K + 1) * (k * (m + 1) + k * (m + 1) * k) :=
          Nat.mul_le_mul (le_refl (K + 1)) (Nat.add_le_add_left hle _)
    _ = (k * (m + 1)) * ((K + 1) * (1 + k)) := by ring
    _ ≤ (k * (m + 1)) * ((m + 1) * k) := Nat.mul_le_mul (le_refl _) hcore
    _ = (k * (m + 1)) * (k * (m + 1)) := by ring

/-- The fixed 99% special case (`K = 99`, so `n ≥ 101`): at least 99% of
endomorphism pairs on a state space of size `≥ 101` are noncommuting. -/
theorem noncommuting_pairs_at_least_99_percent
    {S : Type u} [Fintype S] [DecidableEq S]
    (hcard : 101 ≤ Fintype.card S) :
    99 * Fintype.card (EndoPair S) ≤ 100 * Fintype.card (NoncommutingEndoPairs S) := by
  classical
  set n := Fintype.card S with hn_def
  have htotalEndo : Fintype.card (S -> S) = n ^ n := Fintype.card_fun
  have hT : Fintype.card (EndoPair S) = n ^ n * n ^ n := by
    show Fintype.card ((S -> S) × (S -> S)) = n ^ n * n ^ n
    rw [Fintype.card_prod, htotalEndo]
  have hC : Fintype.card (CommutingEndoPairs S)
      ≤ n ^ n + (n ^ n - 1) * n ^ (n - 1) :=
    commuting_endopairs_card_bound
  have hArith : 100 * (n ^ n + (n ^ n - 1) * n ^ (n - 1)) ≤ n ^ n * n ^ n :=
    generic_bound_arithmetic_general 99 n (by norm_num) (by omega)
  have h100C : 100 * Fintype.card (CommutingEndoPairs S) ≤ Fintype.card (EndoPair S) := by
    rw [hT]
    calc
      100 * Fintype.card (CommutingEndoPairs S)
          ≤ 100 * (n ^ n + (n ^ n - 1) * n ^ (n - 1)) := Nat.mul_le_mul (le_refl 100) hC
      _ ≤ n ^ n * n ^ n := hArith
  have hpart := commuting_noncommuting_partition_card (S := S)
  exact generic_ratio_from_commuting_bound 99
    (Fintype.card (EndoPair S))
    (Fintype.card (CommutingEndoPairs S))
    (Fintype.card (NoncommutingEndoPairs S))
    hpart h100C

/--
**General genericity bound.** For any `K ≥ 1`, on a state space with
`|S| ≥ K + 2`, at least a `K / (K + 1)` fraction of endomorphism pairs are
noncommuting:

```text
K * |EndoPair S| ≤ (K + 1) * |NoncommutingEndoPairs S|.
```

Since `K / (K + 1) -> 1` as `K -> ∞`, and the hypothesis `|S| ≥ K + 2` can be
satisfied for arbitrarily large `K` by taking `|S|` large enough, this is the
precise sense in which "the density of noncommuting transition pairs tends to
`1` as the number of states grows": for every target ratio `K/(K+1) < 1`,
states spaces large enough relative to `K` already achieve at least that
ratio.
-/
theorem generic_noncommutativity_ratio_lower_bound
    {S : Type u} [Fintype S] [DecidableEq S]
    (K : Nat) (hK : 1 ≤ K) (hcard : K + 2 ≤ Fintype.card S) :
    K * Fintype.card (EndoPair S) ≤ (K + 1) * Fintype.card (NoncommutingEndoPairs S) := by
  classical
  set n := Fintype.card S with hn_def
  have htotalEndo : Fintype.card (S -> S) = n ^ n := Fintype.card_fun
  have hT : Fintype.card (EndoPair S) = n ^ n * n ^ n := by
    show Fintype.card ((S -> S) × (S -> S)) = n ^ n * n ^ n
    rw [Fintype.card_prod, htotalEndo]
  have hC : Fintype.card (CommutingEndoPairs S)
      ≤ n ^ n + (n ^ n - 1) * n ^ (n - 1) :=
    commuting_endopairs_card_bound
  have hArith : (K + 1) * (n ^ n + (n ^ n - 1) * n ^ (n - 1)) ≤ n ^ n * n ^ n :=
    generic_bound_arithmetic_general K n hK hcard
  have hKC : (K + 1) * Fintype.card (CommutingEndoPairs S) ≤ Fintype.card (EndoPair S) := by
    rw [hT]
    calc
      (K + 1) * Fintype.card (CommutingEndoPairs S)
          ≤ (K + 1) * (n ^ n + (n ^ n - 1) * n ^ (n - 1)) :=
            Nat.mul_le_mul (le_refl (K + 1)) hC
      _ ≤ n ^ n * n ^ n := hArith
  have hpart := commuting_noncommuting_partition_card (S := S)
  exact generic_ratio_from_commuting_bound K
    (Fintype.card (EndoPair S))
    (Fintype.card (CommutingEndoPairs S))
    (Fintype.card (NoncommutingEndoPairs S))
    hpart hKC

end GenericNoncommutativity
