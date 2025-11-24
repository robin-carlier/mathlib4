/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.GroupTheory.Coxeter.Length
public import Mathlib.Order.ConditionallyCompleteLattice.Defs
public import Mathlib.Order.Fin.Basic

/-! # Recognition principle for coxeter groups

In this file, we give useful criteria to show that a group is a Coxeter group.

This is essentially [Björer-Brenti, 1.5](bjorner2005),
and this will be applied to symmetric groups.

TODO: module systemize parts of this file
-/

@[expose] public section

/-- Given a coxeter matrix `M`, a Pre-Coxeter system on a Group `G` is the data of a
surjective group homomorphism `hom : M.Group →* G` such that the orders of the images of simple
reflections are the coefficients of the given Coxeter matrix.

In practice, this corresponds to a set
of distinct order `2` generators in `G`, and the assertion that `M` is the Coxeter matrix one
can build out of these generators.

This definition allows us to reuse some of the infrastructure developed about length of elements
in a Coxeter system: given `x` in `G`, the length of `x` can be defined as the minimum of
the length of the preimages of `x`.

We will prove below that if the pre-Coxeter System `S` satisfies the so-called "exchange property",
then its hom field is in fact injective, which will extend it to a full-fledged `CoxeterSystem`. -/

structure PreCoxeterSystem {B : Type*} (M : CoxeterMatrix B) (G : Type*) [Group G] where
  /-- The structure group homomorphism. -/
  hom : M.Group →* G
  surjective_hom : Function.Surjective hom
  orderOf_eq (i j : B) : M i j = orderOf (hom (M.simple i) * hom (M.simple j))
  hom_simple_ne_one (i : B) :  hom (M.simple i) ≠ 1

namespace PreCoxeterSystem
variable {B : Type*} {M : CoxeterMatrix B} {G : Type*} [Group G] (S : PreCoxeterSystem M G)

lemma eq_of_hom_simple_eq {i j : B} (h : S.hom (M.simple i) = S.hom (M.simple j)) :
    M.simple i = M.simple j := by
  have := congr($h * S.hom (M.simple j))
  simp only [← map_mul, ← map_mul, ← CoxeterMatrix.toCoxeterSystem_simple,
    CoxeterSystem.simple_mul_simple_self, map_one] at this
  simp only [CoxeterMatrix.toCoxeterSystem_simple, map_mul] at this
  rw [← orderOf_eq_one_iff, ← S.orderOf_eq] at this
  rw [show i = j by grind [CoxeterMatrix.off_diagonal]]

open scoped Classical in
/-- The length of an element of `g` is the minimal length (in the sense of coxeter systems) of
the length of the preimages of `g` in `M.Group`. This corresponds to the minimal length of
a word of generators needed to express `g`. -/
noncomputable def length (g : G) : ℕ :=
  Nat.find <| show (M.toCoxeterSystem.length '' (S.hom⁻¹' {g})).Nonempty by simp [S.surjective_hom]

local prefix:100 "ℓ " => S.length
local prefix:100 "π " => M.toCoxeterSystem.wordProd
local notation "φ " x:max => S.hom (M.toCoxeterSystem.wordProd x)

/-- Every element of `g` can be written as a product of generators in such a way that
the length of the list is minimal. -/
lemma exists_reduced_word (g : G) :
    ∃ (ω : List B), ω.length = ℓ g ∧ φ ω = g := by
  classical
  have : (M.toCoxeterSystem.length '' (S.hom⁻¹' {g})).Nonempty := by simp [S.surjective_hom]
  obtain ⟨x, rfl, h⟩ := Nat.find_spec this
  obtain ⟨ω, l, rfl⟩ := M.toCoxeterSystem.exists_reduced_word x
  grind [length]

/-- Every element of `g` can be written as a product of generators in such a way that
the length of the list is minimal. -/
lemma exists_reduced_word' (g : G) :
    ∃ (ω : List B), ω.length = ℓ g ∧
      ω.length = M.toCoxeterSystem.length (π ω) ∧
      φ ω = g := by
  classical
  have : (M.toCoxeterSystem.length '' (S.hom⁻¹' {g})).Nonempty := by simp [S.surjective_hom]
  obtain ⟨x, rfl, h⟩ := Nat.find_spec this
  obtain ⟨ω, l, rfl⟩ := M.toCoxeterSystem.exists_reduced_word x
  grind [length]

variable {S} in
lemma length_wordProd_le (ω : List B) : ℓ (S.hom (π ω)) ≤ ω.length := by
  classical
  have m : M.toCoxeterSystem.length (π ω) ≤ ω.length := M.toCoxeterSystem.length_wordProd_le ω
  have ne : (M.toCoxeterSystem.length '' (S.hom⁻¹' {(φ ω)})).Nonempty := by simp [S.surjective_hom]
  have : M.toCoxeterSystem.length (π ω) ∈ (M.toCoxeterSystem.length '' (S.hom⁻¹' {φ ω})) := by grind
  exact (Nat.find_le (h := ne) this).trans m

variable {S} in
lemma length_le_of_eq_wordProd (g : G) (ω : List B) (h : g = S.hom (π ω)) : ℓ g ≤ ω.length :=
  h ▸ (length_wordProd_le ω)

/-! The next few lemmas are essentially duplications/generalizations to pre-Coxeter
systems of those from coxeter systems.
These correspond to properties (ii), (iii), (iv) and (vi) of prop 1.4.2 from
[A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*](bjorner2005). -/
@[simp] theorem length_one : ℓ (1 : G) = 0 :=
  Nat.eq_zero_of_le_zero (by simpa using length_wordProd_le [])

@[simp]
theorem length_eq_zero_iff {g : G} : ℓ g = 0 ↔ g = 1 := by
  constructor
  · intro h
    rcases S.exists_reduced_word g with ⟨ω, hω, rfl⟩
    have : ω = [] := List.eq_nil_of_length_eq_zero (hω.trans h)
    rw [this, CoxeterSystem.wordProd_nil, map_one]
  · rintro rfl
    exact S.length_one

@[simp]
theorem length_inv (w : G) : ℓ (w⁻¹) = ℓ w := by
  apply Nat.le_antisymm
  · rcases S.exists_reduced_word w with ⟨ω, hω, rfl⟩
    have := S.length_wordProd_le (List.reverse ω)
    rwa [CoxeterSystem.wordProd_reverse, List.length_reverse, hω, map_inv] at this
  · rcases S.exists_reduced_word w⁻¹ with ⟨ω, hω, h'ω⟩
    have := S.length_wordProd_le (List.reverse ω)
    rwa [CoxeterSystem.wordProd_reverse, List.length_reverse, map_inv, hω, h'ω, inv_inv] at this

theorem length_mul_le (w₁ w₂ : G) :
    ℓ (w₁ * w₂) ≤ ℓ w₁ + ℓ w₂ := by
  rcases S.exists_reduced_word w₁ with ⟨ω₁, hω₁, rfl⟩
  rcases S.exists_reduced_word w₂ with ⟨ω₂, hω₂, rfl⟩
  have := S.length_wordProd_le (ω₁ ++ ω₂)
  simpa [hω₁, hω₂, CoxeterSystem.wordProd_append, ← map_mul] using this

@[simp, grind =]
lemma length_simple (i : B) : ℓ (S.hom <| M.toCoxeterSystem.simple i) = 1 := by
  rw [← CoxeterSystem.wordProd_singleton]
  suffices h : ℓ (S.hom <| M.toCoxeterSystem.simple i) ≠ 0 by
    apply le_antisymm <;> grind [length_wordProd_le, CoxeterSystem.wordProd_singleton]
  rw [Iff.ne S.length_eq_zero_iff]
  exact S.hom_simple_ne_one _

@[simp, grind =]
lemma length_simple' (i : B) : ℓ (S.hom <| M.simple i) = 1 := by simpa using S.length_simple i

/-- A word `ω` in `B` (i.e a list of elements of `B`) is said to be reduced (with respect to
a pre-Coxeter System `S` if it has minimal length, i.e if the length of the word is the length of
the element of `G` it defines. -/
abbrev IsReduced (ω : List B) : Prop := ℓ (S.hom <| π ω ) = ω.length

private theorem isReduced_take_and_drop {ω : List B} (hω : S.IsReduced ω) (j : ℕ) :
    S.IsReduced (ω.take j) ∧ S.IsReduced (ω.drop j) := by
  have h₁ : ℓ (S.hom <| π (ω.take j)) ≤ (ω.take j).length := S.length_wordProd_le (ω.take j)
  have h₂ : ℓ (S.hom <| π (ω.drop j)) ≤ (ω.drop j).length := S.length_wordProd_le (ω.drop j)
  have h₃ := calc
    (ω.take j).length + (ω.drop j).length
    _ = ω.length := by rw [← List.length_append, ω.take_append_drop j]
    _ = ℓ (S.hom <| π ω) := hω.symm
    _ = ℓ (S.hom <| π (ω.take j) * π (ω.drop j)) := by
      rw [← CoxeterSystem.wordProd_append, ω.take_append_drop j]
    _ ≤ ℓ (S.hom <| π (ω.take j)) + ℓ (S.hom <| π (ω.drop j)) := by grind [length_mul_le]
  cutsat

variable {S} in
theorem IsReduced.take {ω : List B} (hω : S.IsReduced ω) (j : ℕ) :
    S.IsReduced (ω.take j) :=
  (isReduced_take_and_drop _ hω _).1

variable {S} in
theorem IsReduced.drop {ω : List B} (hω : S.IsReduced ω) (j : ℕ) :
    S.IsReduced (ω.drop j) :=
  (isReduced_take_and_drop _ hω _).2

@[grind .]
lemma IsReduced.nil : S.IsReduced [] := by
  grind [CoxeterSystem.wordProd_nil, length_one, List.length_nil]

lemma isReduced_of_length_eq_of_hom_wordProd_eq {ω ω' : List B}
    (hl : ω.length = ω'.length) (h : φ ω = φ ω')
    (hr : S.IsReduced ω) :
    S.IsReduced ω' := by
  grind

@[simp, grind =]
private lemma List.take_eraseIdx (L : List B) (i : ℕ) : (L.eraseIdx i).take i = L.take i := by
  induction L generalizing i with
  | nil => simp
  | cons head tail ih => induction i generalizing tail with grind

@[simp, grind =]
private lemma List.drop_eraseIdx (L : List B) (i : ℕ) : (L.eraseIdx i).drop i = L.drop (i + 1) := by
  induction L generalizing i with
  | nil => simp
  | cons head tail ih => induction i generalizing tail with grind

-- TODO: upstream this one
@[simp]
lemma _root_.CoxeterSystem.wordprod_self_cons {cs : CoxeterSystem M G} (a : B) (ω : List B) :
    cs.wordProd (a :: a :: ω) = cs.wordProd ω := by
  simp [cs.wordProd_cons]


/-- The "deletion property" for a Pre-Coxeter system `S`: if a word of generators
$$w = s_1\cdotss_k$$ in `G` is not reduced, then there exists `1 ≤ i < j ≤ k` such that
$$w = s_1 \cdots \hat{s_i} \cdots \hat{s_j} \cdots s_k$$.

This property implies that `hom` is injective, and so that one can extend the data in `S` to an
actual `CoxeterSystem`. -/
def DeletionProperty : Prop :=
    ∀ (ω : List B), (¬ S.IsReduced ω) →
      ∃ (i j : ℕ) (_ : i < j) (_ : j < ω.length),
        φ ω = φ ((ω.eraseIdx i).eraseIdx <| j - 1)

/-- The "exchage property" for a Pre-Coxeter system `S`: if a word of generators
$$w = s_1\cdotss_k$$ in `G` is reduced and reduces further when multiplying on a left by a
generator, then there exists `1 ≤ i < j ≤ k` such that
$$s*w = s_1 \cdots \hat{s_i} \cdots \hat{s_j} \cdots s_k$$.

This property implies that `hom` is injective, and so that one can extend the data in `S` to an
actual `CoxeterSystem`. -/
def ExchangeProperty : Prop :=
    ∀ (ω : List B) (_ : S.IsReduced ω) (b : B) (_ : ℓ (φ (b :: ω)) ≤ ω.length),
      ∃ (i : ℕ) (_ : i < ω.length), φ (b :: ω) = φ (ω.eraseIdx i)

lemma simple_reduced (s : B) : S.IsReduced ([s]) := by
  dsimp [IsReduced]
  have := S.length_wordProd_le [s]
  suffices ℓ (φ [s]) ≠ 0 by grind
  simp

private lemma exists_index_max_nonreduced_suffix (ω : List B) (h : ¬ S.IsReduced ω) :
    ∃ i : ℕ, i < (ω.length - 1) ∧ S.IsReduced (ω.drop (i + 1)) ∧ ¬ (S.IsReduced <| ω.drop i) := by
  induction ω with
  | nil => grind
  | cons s ω ih =>
    simp only [List.length_cons, add_tsub_cancel_right, List.drop_succ_cons, ne_eq,
      List.length_drop]
    by_cases h : S.IsReduced ω
    · use 0
      cases ω with | nil => grind [simple_reduced] | cons s' ω =>
      grind
    · obtain ⟨i, hi, hi', hi''⟩ := ih h
      use (i + 1)
      grind

theorem exchangeProperty_iff_deletionProperty : S.DeletionProperty ↔ S.ExchangeProperty where
  mp D := by
    intro ω hred s hl
    obtain ⟨i, j, hij, hj, e⟩ := D (s :: ω) (by grind)
    have : i = 0 := by
      by_contra!
      obtain ⟨i, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero this
      obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ j by grind)
      have := congr(ℓ $(congr(φ [s] * $e)))
      simp only [List.eraseIdx_cons_succ, Nat.add_one_sub_one,
        ← map_mul, ← CoxeterSystem.wordProd_append, List.singleton_append,
        CoxeterSystem.wordprod_self_cons, hred] at this
      suffices h : ((ω.eraseIdx i).eraseIdx j).length < ω.length by
        have := S.length_wordProd_le ((ω.eraseIdx i).eraseIdx j)
        cutsat
      grind
    grind
  mpr E := by
    intro ω hred
    obtain ⟨i, hi, hred, hnred⟩ := S.exists_index_max_nonreduced_suffix ω hred
    have hi' : i < ω.length := by cutsat
    rw [List.drop_eq_getElem_cons hi'] at hnred
    obtain ⟨j, hj, hj'⟩ := E (ω.drop (i + 1)) hred ω[i] (by
      have := S.length_wordProd_le (ω.drop i);
      simp only [List.getElem_cons_drop, List.length_drop, ge_iff_le]
      dsimp [IsReduced] at hnred
      simp only [List.getElem_cons_drop, List.length_drop] at hnred this
      cutsat)
    have := congr(φ (ω.take i) * $hj')
    simp only [List.getElem_cons_drop, ← map_mul, ← CoxeterSystem.wordProd_append,
      List.take_append_drop] at this
    have eq₁ := List.eraseIdx_append_of_length_le
      (k := j + (ω.take i).length) (l := ω.take i) (by cutsat) (ω.drop (i + 1))
    simp only [List.length_take, add_tsub_cancel_right] at eq₁
    rw [← eq₁, ← List.eraseIdx_eq_take_drop_succ] at this
    use i, i + j + 1, by grind, by grind
    convert this using 4
    grind

lemma _root_.List.reverse_eraseIdx {α : Type*} (l : List α) (i : ℕ) (hi : i < l.length) :
    (l.eraseIdx i).reverse = l.reverse.eraseIdx (l.length - (i + 1)) := by
  grind [List.take_reverse, List.drop_reverse]

/-- A variant of `ExchangeProperty` where instead we multiply on the right, which corresponds
to appending singletons at the end of lists. -/
def ExchangeProperty' : Prop :=
    ∀ (ω : List B) (_ : S.IsReduced ω) (b : B) (_ : ℓ (φ (ω ++ [b])) ≤ ω.length),
      ∃ (i : ℕ) (_ : i < ω.length), φ (ω ++ [b]) = φ (ω.eraseIdx i)

lemma exchangeProperty_iff_exchangeProperty' :
    S.ExchangeProperty ↔ S.ExchangeProperty' where
  mp E := by
    intro ω hred b hl
    rw [← S.length_inv, ← map_inv, ← CoxeterSystem.wordProd_reverse, List.reverse_append,
      List.reverse_singleton, List.singleton_append, ← List.length_reverse] at hl
    have : S.IsReduced ω.reverse := by
      grind [length_inv, CoxeterSystem.wordProd_reverse]
    obtain ⟨i, hi, hi'⟩ := E _ this _ hl
    have := congr($hi'⁻¹)
    simp_rw [← map_inv, ← CoxeterSystem.wordProd_reverse, List.reverse_cons,
      List.reverse_reverse, ω.reverse.reverse_eraseIdx i (by simpa using hi)] at this
    grind
  mpr E := by
    intro ω hred b hl
    rw [← S.length_inv, ← map_inv, ← CoxeterSystem.wordProd_reverse, List.reverse_cons,
      ← List.length_reverse] at hl
    have : S.IsReduced ω.reverse := by
      grind [length_inv, CoxeterSystem.wordProd_reverse]
    obtain ⟨i, hi, hi'⟩ := E _ this _ hl
    have := congr($hi'⁻¹)
    simp_rw [← map_inv, ← CoxeterSystem.wordProd_reverse, List.reverse_append,
      List.reverse_reverse, ω.reverse.reverse_eraseIdx i (by simpa using hi)] at this
    grind

private lemma even_length_of_hom_wordProd_eq_one
    (D : S.DeletionProperty) (ω : List B) (hω : φ ω = 1) :
    Even ω.length := by
  generalize hL : ω.length = L
  induction L using Nat.strongRecOn generalizing ω with | ind n ih =>
  by_cases hred : S.IsReduced ω
  · -- If ω is reduced then it must be []
    dsimp [IsReduced] at hred
    simp [hω] at hred
    grind
  · obtain ⟨i, j, hij, hj, e⟩ := D ω hred
    have : 2 ≤ n := by cutsat
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le this
    have := ih k (by cutsat) ((ω.eraseIdx i).eraseIdx (j - 1)) (by grind) (by grind)
    simpa [parity_simps] using this

/-- Given `S : PreCoxeterSystem M G` and two words (lists) ω, ω' of generators,
they are said to be fine if their equality in
`G` means they were already equal in `M.Group`.
Almost tautologically, `S` is an actual coxeter system (i.e `S.hom` is injective)
if and only if all pairs of lists are fine. -/
private abbrev Fine : List B → List B → Prop := fun ω ω' ↦
  φ ω = φ ω' → π ω = π ω'

open CoxeterSystem in
/-- An application of the exchange property that gets used multiple times in the course of the
argument. -/
private lemma exchangeProperty_cons
    (E : S.ExchangeProperty)
    {s₁ s₁' : B} {ω ω' : List B}
    (hl : ω.length = ω'.length)
    (h : φ (s₁ :: ω) = φ (s₁' :: ω'))
    (hred : S.IsReduced (s₁ :: ω)) :
    ∃ i < ω.length + 1, φ ((s₁ :: ω).eraseIdx i) = φ ω' := by
  have : S.IsReduced (s₁' :: ω') :=
    S.isReduced_of_length_eq_of_hom_wordProd_eq (by grind) h hred
  obtain ⟨i, hi, hi'⟩ := E (s₁ :: ω) (by grind) s₁' <| by
    simp_rw [CoxeterSystem.wordProd_cons, map_mul] at h ⊢
    simp_rw [h, ← map_mul, ← mul_assoc, CoxeterSystem.simple_mul_simple_self, one_mul]
    grind [length_wordProd_le]
  use i, by grind
  rw [← mul_right_inj (S.hom (M.toCoxeterSystem.simple s₁')), ← hi', ← map_mul, ← map_mul,
    ← CoxeterSystem.wordProd_cons, ← CoxeterSystem.wordProd_cons, ← h]
  simp

-- TODO Clean this up a little bit
/-- A first "discharge case": during an induction on the length of words,
if a word is not reduced then any relation involving it is fine as it reduces to a shorter one. -/
private lemma nonReduced_case
    (E : S.ExchangeProperty)
    {ω ω' : List B}
    (hl : ω.length = ω'.length)
    (h : S.hom (π ω) = S.hom (π ω'))
    (ih : ∀ m < ω.length, ∀ (ω₀ ω₀' : List B),
      ω₀.length = m → m = ω₀'.length → S.Fine ω₀ ω₀')
    (hred : ¬ S.IsReduced ω) :
    π ω = π ω' := by
  let m' := ℓ (S.hom <| π ω)
  have m'_eq : m' = ℓ (S.hom <| π ω') := by grind
  have : m' ≤ ω.length := hl ▸ S.length_le_of_eq_wordProd _ ω rfl
  have : m' ≠ ω.length := by grind
  -- The idea is to simplify the words to get relations between shorters words,
  -- which are handled by our induction hypothesis.
  -- first we "cut" the words according to a maximal reduced prefix
  obtain ⟨i, hi₀, hi₁, hi₂⟩ := S.exists_index_max_nonreduced_suffix ω (by grind)
  obtain ⟨i', hi₀', hi₁', hi₂'⟩ := S.exists_index_max_nonreduced_suffix ω' (by grind)
  -- we can use the exchange property to reduce s₁ :: ω to a shorter word:
  obtain ⟨j, hj₁, hj₂⟩ := E (List.drop (i + 1) ω) hi₁ ω[i] <| by
    grind [List.getElem_cons_drop, length_wordProd_le]
  replace hj₂ := congr(S.hom (M.toCoxeterSystem.wordProd [ω[i]]) * $hj₂)
  simp only [← map_mul, ← CoxeterSystem.wordProd_append,
    List.cons_append, List.nil_append, CoxeterSystem.wordprod_self_cons] at hj₂
  have eq₁ := congr(S.hom (M.toCoxeterSystem.wordProd (ω.take (i + 1))) * $hj₂)
  simp only [← map_mul, ← CoxeterSystem.wordProd_append, List.take_append_drop] at eq₁
  rw [List.take_succ_eq_append_getElem (by grind)] at eq₁
  simp only [List.append_assoc, List.singleton_append, CoxeterSystem.wordProd_append,
    CoxeterSystem.wordprod_self_cons] at eq₁
  simp only [← CoxeterSystem.wordProd_append] at eq₁
  --same with s₁' :: ω'
  obtain ⟨j', hj₁', hj₂'⟩ := E (List.drop (i' + 1) ω') hi₁' ω'[i'] <| by
    grind [List.getElem_cons_drop, length_wordProd_le]
  replace hj₂' := congr(S.hom (M.toCoxeterSystem.wordProd [ω'[i']]) * $hj₂')
  simp only [← map_mul, ← CoxeterSystem.wordProd_append,
    List.cons_append, List.nil_append, CoxeterSystem.wordprod_self_cons] at hj₂'
  have eq₁' := congr(S.hom (M.toCoxeterSystem.wordProd (ω'.take (i' + 1))) * $hj₂')
  simp only [← map_mul, ← CoxeterSystem.wordProd_append, List.take_append_drop] at eq₁'
  rw [List.take_succ_eq_append_getElem (by grind)] at eq₁'
  simp only [List.append_assoc, List.singleton_append, CoxeterSystem.wordProd_append,
    CoxeterSystem.wordprod_self_cons] at eq₁'
  simp only [← CoxeterSystem.wordProd_append] at eq₁'
  -- Then we apply the induction hyp to get equalities in the Coxeter group, as all
  -- of the relations derived above are between words of shorter length
  have ind₁ := ih _ (by grind)
    (List.take i ω ++ (List.drop (i + 1) ω).eraseIdx j)
    (List.take i' ω' ++ (List.drop (i' + 1) ω').eraseIdx j')
    rfl
    (by grind)
    (by grind)
  have ind₂ := ih _ (by grind) _ _ rfl (by grind) hj₂
  have ind₂' := ih _ (by grind) _ _ rfl (by grind) hj₂'
  have eq₁'' := congr(M.toCoxeterSystem.wordProd (ω.take (i + 1)) * $ind₂)
  simp only [← CoxeterSystem.wordProd_append, List.take_append_drop] at eq₁''
  rw [List.take_succ_eq_append_getElem (by grind)] at eq₁''
  have eq₁''' := congr(M.toCoxeterSystem.wordProd (ω'.take (i' + 1)) * $ind₂')
  simp only [← CoxeterSystem.wordProd_append, List.take_append_drop] at eq₁'''
  rw [List.take_succ_eq_append_getElem (by grind)] at eq₁'''
  grind [CoxeterSystem.wordProd_append, CoxeterSystem.wordprod_self_cons]

/-- This is "Case 1" in [Björer-Brenti, proof of 1.5.1 (p.19)](bjorner2005) : when
applying the exchange property, this is the case that has to be handled if the index
is not maximal. -/
private lemma fine_cons_non_maximal_index
    {s₁ s₁' : B} {ω ω' : List B}
    (hl : ω.length = ω'.length)
    (ih : ∀ m < ω.length + 1, ∀ (ω₀ ω₀' : List B),
      ω₀.length = m → m = ω₀'.length → S.Fine ω₀ ω₀')
    (i : ℕ) (hi : i < ω.length) (hi' : φ ((s₁ :: ω).eraseIdx i) = φ ω')
    (h : φ (s₁ :: ω) = φ (s₁' :: ω'))
    (hr : S.IsReduced (s₁ :: ω)) :
    π (s₁ :: ω) = π (s₁' :: ω') := by
  by_cases hs : π [s₁] = π [s₁']
  · -- easy case: the heads of the list cancel, giving a shorter relation
    suffices π ω = π ω' by
      have := congr($hs*$this)
      grind [CoxeterSystem.wordProd_cons, _=_ CoxeterSystem.wordProd_append]
    replace h := congr(S.hom (π [s₁]) * $h)
    apply ih ω.length (by cutsat) ω ω' rfl hl
      (by
        simp only [CoxeterSystem.wordProd_cons, CoxeterMatrix.toCoxeterSystem_simple,
          CoxeterSystem.wordProd_nil, mul_one, map_mul, mul_right_inj] at h hs
        grind [CoxeterSystem.simple_mul_simple_self, mul_right_inj])
  · push_neg at hs
    have e₂ : π ((s₁ :: ω).eraseIdx i) = π ω' := ih _ (by grind) _ _ rfl (by grind) hi'
    have e₃'' : S.hom (π (s₁' :: ((s₁ :: ω).eraseIdx i))) = S.hom (π (s₁' :: ω')) := by
      grind [CoxeterSystem.wordProd_cons]
    have e₃ : π (s₁' :: ((s₁ :: ω).eraseIdx i)) = π (s₁' :: ω') := by
      grind [CoxeterSystem.wordProd_cons]
    cases i with
    | zero =>
      simp only [List.eraseIdx_zero, List.tail_cons] at e₂ e₃ hl
      simp only [CoxeterSystem.wordProd_cons, CoxeterMatrix.toCoxeterSystem_simple, e₂,
        map_mul, mul_left_inj] at h
      simpa using hs (S.eq_of_hom_simple_eq h)
    | succ i =>
      simp only [List.eraseIdx_cons_succ] at e₂ e₃ hi'
      have : φ (s₁' :: s₁ :: (ω.take i)) = φ (s₁ :: ω.take (i + 1)) := by
        rw [List.eraseIdx_eq_take_drop_succ, ← List.cons_append,
          CoxeterSystem.wordProd_append, map_mul] at hi'
        simp only [CoxeterSystem.wordProd_cons, CoxeterMatrix.toCoxeterSystem_simple, map_mul,
          List.eraseIdx_eq_take_drop_succ, CoxeterSystem.wordProd_append, mul_right_inj] at h e₃
        rw [← e₃, map_mul, map_mul] at h
        conv at h in S.hom (M.toCoxeterSystem.wordProd ω) => rw [← ω.take_append_drop (i + 1)]
        simp_rw [CoxeterSystem.wordProd_append, map_mul, ← mul_assoc] at h
        simp only [mul_left_inj] at h
        simpa [CoxeterSystem.wordProd_cons, mul_assoc] using h.symm
      have e₄ := ih _ (by grind) _ _ rfl (by grind) this
      rw [← e₃]
      simp only [List.eraseIdx_eq_take_drop_succ, ← List.cons_append,
        CoxeterSystem.wordProd_append, e₄]
      simp [CoxeterSystem.wordProd_cons, mul_assoc, ← CoxeterSystem.wordProd_append]

open CoxeterSystem in
/-- A reduction that we have to perform multiple time in the rest of the argumment. -/
private lemma reduction_step
    (E : S.ExchangeProperty)
    {s₁ s₁' : B} {ω ω' : List B}
    {n : ℕ} (hn : ω.length = n) (hn' : ω'.length = n)
    (ih : ∀ m < n + 1, ∀ (ω₀ ω₀' : List B),
      ω₀.length = m → m = ω₀'.length → S.Fine ω₀ ω₀')
    (ih₂ : ∀ (s₁ s₁' : B) (ω₀ ω₀' : List B) (_ : ω₀.length = n) (_ : ω₀'.length = n)
      (_ : S.IsReduced (s₁ :: ω₀)),
      φ (s₁ :: ω₀) = φ (s₁' :: ω₀') →
        (∀ i < ω₀.length, (_ : φ ((s₁ :: ω₀).eraseIdx i) = φ ω₀') →
          π (s₁ :: ω₀) = π (s₁' :: ω₀'))) :
   S.Fine (s₁' :: (s₁ :: ω).dropLast) (s₁ :: ω) → S.Fine (s₁ :: ω) (s₁' :: ω') := by
  intro hFine
  by_cases hred : ¬ S.IsReduced (s₁ :: ω)
  · exact fun h => S.nonReduced_case E (by grind) h (by simpa [hn]) hred
  push_neg at hred
  intro h
  obtain ⟨i, hi, hi'⟩ := S.exchangeProperty_cons E (by grind) h hred
  by_cases h_eq : i = ω.length
  · suffices h₀ : S.Fine (s₁' :: (s₁ :: ω).dropLast) (s₁ :: ω) by
      rw [List.eraseIdx_eq_dropLast (by simpa using h_eq)] at hi'
      have := ih _ (by simp; cutsat) _ _ rfl (by simp; cutsat) hi'
      grind [CoxeterSystem.wordProd_cons]
    assumption
  · apply ih₂ (i := i) <;> grind

open CoxeterSystem in
theorem prod_alternatingWord_eq_mul_pow (i i' : B) (m : ℕ) :
    φ (alternatingWord i i' m) = (if Even m then 1 else φ [i']) * (φ [i] * φ [i']) ^ (m / 2) := by
  induction m with
  | zero => simp [alternatingWord]
  | succ m ih =>
    rw [alternatingWord_succ', wordProd_cons, map_mul, ih]
    by_cases hm : Even m
    · have h₁ : ¬ Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 := Nat.succ_div_of_not_dvd <| by rwa [← even_iff_two_dvd]
      simp [hm, h₁, h₂]
    · have h₁ : Even (m + 1) := by simp [hm, parity_simps]
      have h₂ : (m + 1) / 2 = m / 2 + 1 := Nat.succ_div_of_dvd h₁.two_dvd
      simp [hm, h₁, h₂, ← pow_succ', ← mul_assoc]

@[simp, grind =] lemma mul_phi_self (s : B) :
    S.hom (M.toCoxeterSystem.simple s) * S.hom (M.toCoxeterSystem.simple s) = 1 := by
  rw [← map_mul, CoxeterSystem.simple_mul_simple_self, map_one]

@[simp, grind =] lemma mul_phi_self' (s : B) :
    S.hom (M.simple s) * S.hom (M.simple s) = 1 := by
  simp_rw [← M.toCoxeterSystem_simple, ← map_mul, CoxeterSystem.simple_mul_simple_self, map_one]

-- TODO these ones belong elsewhere
@[simp, grind =] lemma inv_simple (s : B) :
    (M.simple s)⁻¹ = M.simple s := by
  rw [← mul_inv_eq_one]
  simp [← M.toCoxeterSystem_simple, -CoxeterMatrix.toCoxeterSystem_simple]

@[simp, grind =] lemma simple_mul_simple (s : B) :
    (M.simple s) * M.simple s = 1 := by
  simp [← M.toCoxeterSystem_simple, -CoxeterMatrix.toCoxeterSystem_simple]

@[simp, grind =] lemma inv_phi_self' (s : B) :
    (S.hom (M.simple s))⁻¹ = S.hom (M.simple s) := by
  rw [← mul_inv_eq_one]
  simp [← mul_inv_rev]

private lemma mul_pow_mul_pow_eq {G : Type*} [Group G] (a b : G) (k : ℕ) :
    a * (b * a) ^ k * b * (a * b) ^ k = (a * b) ^ (2*k + 1) := by
  induction k with
  | zero => simp
  | succ n hr =>
    nth_rw 1 [pow_succ']
    nth_rw 1 [pow_succ]
    simp only [← mul_assoc]
    have := congr(a * b * $hr * a * b)
    conv_rhs at this => rw [← pow_succ', mul_assoc, ← pow_succ]
    grind

private lemma mul_pow_mul_pow_eq' {G : Type*} [Group G] (a b : G) (k : ℕ) :
    (a * (b * a) ^ k * b) = (a * b) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ n hr =>
    nth_rw 1 [pow_succ']
    simp only [← mul_assoc]
    rw [mul_assoc (a*b), mul_assoc, hr, ← pow_succ']

open CoxeterSystem in
/-- One of the actual base case of the induction: relations between alternating words are fine. -/
private lemma fine_alternatingWord (s₁ s₁' : B) (j : ℕ) :
    S.Fine (alternatingWord s₁ s₁' (j + 1)) (alternatingWord s₁ s₁' j ++ [s₁]) := by
  intro h
  simp only [alternatingWord_succ, List.concat_eq_append]
  have eq₁ := S.prod_alternatingWord_eq_mul_pow s₁ s₁' (j + 1)
  have eq₂ := S.prod_alternatingWord_eq_mul_pow s₁ s₁ j
  simp [CoxeterSystem.wordProd_append, CoxeterSystem.prod_alternatingWord_eq_mul_pow] at h ⊢
  -- In both cases, the idea is that the relation φ … = φ … will reduce through computations to
  -- something of the form (φ [i] * φ [j])^k, and same for π, and by definition of a pre-Coxeter
  -- System the order of φ [i] * φ [j] and of π [i] * π [j] are equal.
  by_cases hj : Even j -- Unfortunately, the computation is slightly different in each case.
  · have h₁ : ¬ Even (j + 1) := by simp [hj, parity_simps]
    have h₂ : (j + 1) / 2 = j / 2 := Nat.succ_div_of_not_dvd <| by rwa [← even_iff_two_dvd]
    simp only [h₁, ↓reduceIte, h₂, map_mul, map_pow, hj] at h ⊢
    rw [← mul_inv_eq_one] at h ⊢
    simp only [mul_inv_rev, inv_phi_self', ← inv_pow, mul_assoc, inv_simple] at h ⊢
    simp only [← map_mul, ← map_pow, ← mul_assoc] at h
    rw [mul_pow_mul_pow_eq, map_pow, map_mul] at h
    have o_le := orderOf_dvd_of_pow_eq_one h
    simp only [← S.orderOf_eq s₁' s₁] at o_le
    -- now same computation on the other side
    simp only [← mul_assoc (M.simple s₁') (M.simple s₁), ← pow_succ', ← pow_add,
      show j / 2 + (j / 2 + 1) = 2 * (j / 2) + 1 by grind]
    have := M.toCoxeterSystem.simple_mul_simple_pow s₁' s₁
    obtain ⟨k, h⟩ := o_le
    simp only [CoxeterMatrix.toCoxeterSystem_simple] at this
    simp [h, -CoxeterSystem.simple_mul_simple_self, pow_mul, this]
  · have h₁ : Even (j + 1) := by simp [hj, parity_simps]
    have h₂ : (j + 1) / 2 = j / 2 + 1 := Nat.succ_div_of_dvd h₁.two_dvd
    simp [hj, h₁, h₂] at h ⊢
    rw [← mul_inv_eq_one] at h ⊢
    simp only [mul_assoc, mul_inv_rev, inv_phi_self', ← inv_pow, inv_simple] at h ⊢
    rw [← mul_assoc (S.hom (M.simple s₁)), mul_pow_mul_pow_eq', ← pow_add,
      show j / 2 + 1 + (j / 2 + 1) = 2*(j/2) + 2 by grind] at h
    have o_le := orderOf_dvd_of_pow_eq_one h
    simp only [← S.orderOf_eq s₁ s₁'] at o_le
    simp only [← mul_assoc (M.simple s₁') (M.simple s₁), ← mul_assoc, ← pow_succ', ← pow_add,
      show j / 2 + (j / 2 + 1) = 2 * (j / 2) + 1 by grind]
    have := M.toCoxeterSystem.simple_mul_simple_pow s₁ s₁'
    obtain ⟨k, h⟩ := o_le
    suffices h₀ :
        (M.simple s₁ * M.simple s₁') ^ (2 * (j / 2) + 2) =
        M.simple s₁ * (M.simple s₁' * M.simple s₁) ^ (2 * (j / 2) + 1) * M.simple s₁' by
      simp_rw [← h₀, ← M.toCoxeterSystem_simple, h, pow_mul, this, one_pow]
    generalize 2*(j/2) = k₀, M.simple s₁ = a, M.simple s₁' = b
    exact mul_pow_mul_pow_eq' _ _ _|>.symm

open CoxeterSystem in
/-- The most tricky part of the argument: assuming we are in the process of an induction and
that we repeatedly get the largest possible index when using the exchange property,
we show that eventually the situation reduces to fineness of relations involving
alternating words, which we handled in `fine_alternatingWord`.
This is part of "Case 2" as described in [Björer-Brenti, proof of 1.5.1](bjorner2005). -/
private lemma fine_alternatingWord_append_induction
    (E : S.ExchangeProperty)
    {s₁ s₁' : B} {ω : List B}
    (j k : ℕ) (hjk : j + k = ω.length)
    (ih : ∀ m < j + k + 1, ∀ (ω₀ ω₀' : List B),
      ω₀.length = m → m = ω₀'.length → S.Fine ω₀ ω₀')
    (ih₂ : ∀ (s₁ s₁' : B) (ω₀ ω₀' : List B) (_ : ω₀.length = j + k) (_ : ω₀'.length = j + k)
      (_ : S.IsReduced (s₁ :: ω₀)),
      φ (s₁ :: ω₀) = φ (s₁' :: ω₀') →
        (∀ i < ω₀.length, (_ : φ ((s₁ :: ω₀).eraseIdx i) = φ ω₀') →
          π (s₁ :: ω₀) = π (s₁' :: ω₀'))) :
    S.Fine
      (alternatingWord s₁ s₁' (j + 1) ++ List.take k (s₁ :: ω))
      (alternatingWord s₁ s₁' j ++ List.take (k + 1) (s₁ :: ω)) := by
  induction k generalizing j s₁ s₁' ω with
  | zero =>
    simpa using fine_alternatingWord S s₁ s₁' j
  | succ k hrec =>
      -- We need some lemmas to help the cutsat calls
    have min₁ : min k ω.length = k := by rw [min_eq_left_iff]; cutsat
    have min₁' : min (k + 1) ω.length = (k + 1) := by rw [min_eq_left_iff]; cutsat
    cases j with
    | zero => -- We need to special-case j = 0 extract the head of the list
      simp only [zero_add, alternatingWord, List.concat_eq_append, List.nil_append,
        List.take_succ_cons, List.cons_append] at hjk ⊢
      apply S.reduction_step E (n := k + 1) (by grind) (by grind) (by simpa using ih)
        (by simpa using ih₂)
      simp only [List.dropLast_eq_take, List.length_cons, List.length_take, min₁,
        add_tsub_cancel_right, List.take_succ_cons]
      cases k with
      | zero => simpa using fine_alternatingWord S s₁ s₁' 1 -- This is the easiest case
      | succ n =>
        intro h
        have ih := hrec (s₁ := s₁) (s₁' := s₁') (ω := ω) 1 (by cutsat)
          (by grind) (by grind) (by simpa [List.take_take, alternatingWord] using h)
        simpa [List.take_take, alternatingWord] using ih
    | succ j =>
      simp [alternatingWord_succ'] at ⊢
      -- setting some names here makes things slightly less annoying to write some expressions and
      -- makes more apparent the fact that we follow the same process as in other parts of the proof
      let s₀ := (if Even (j + 1) then s₁' else s₁)
      let s₀' := (if Even j then s₁' else s₁)
      let ω₀ := s₀' :: (alternatingWord s₁ s₁' j ++ s₁ :: List.take k ω)
      let ω₀' := alternatingWord s₁ s₁' j ++ s₁ :: List.take (k + 1) ω
      -- need some lemmas to help the cutsat calls
      have : ω₀.length = ω.length := by grind [length_alternatingWord]
      have : ω₀.length = ω₀'.length := by grind [length_alternatingWord]
      change S.Fine (s₀ :: ω₀) (s₀' :: ω₀')
      apply S.reduction_step E (n := j + 1 + k + 1) (by grind) (by grind) (by simpa using ih)
        (by simpa using ih₂)
      cases k with
      | zero => -- reduces to a purely alternating word
        simp only [ne_eq, reduceCtorEq, not_false_eq_true, List.dropLast_cons_of_ne_nil]
        convert S.fine_alternatingWord s₁ s₁' (j + 2) using 1
        · simp [s₀', s₀, ω₀, alternatingWord_succ', parity_simps,
            List.dropLast_cons_of_ne_nil (l := alternatingWord s₁ s₁' j ++ [s₁]) (by simp)]
        · simp [s₀', s₀, ω₀, alternatingWord_succ', parity_simps]
      | succ k => -- this case reduces to the induction hypothesis.
        intro h
        suffices h₀ :
            (s₀' :: (s₀ :: ω₀).dropLast =
              alternatingWord s₁ s₁' (j + 2 + 1) ++ s₁ :: List.take k ω) ∧
            s₀ :: ω₀ = alternatingWord s₁ s₁' (j + 2) ++ s₁ :: List.take (k + 1) ω by
          rw [h₀.1, h₀.2] at h ⊢
          exact hrec (s₁ := s₁) (s₁' := s₁') (ω := ω) (j + 2) (by cutsat)
            (by simpa +arith using ih) (by simpa +arith using ih₂) h
        dsimp [s₀, s₀', ω₀, ω₀']
        have : j + (min (k + 1) ω.length + 1) =
          (alternatingWord s₁ s₁' (j + 1)).length + (k + 1) := by simp +arith [min₁]
        -- Finally, it’s just a List computation.
        simp only [Nat.even_add_one, Nat.not_even_iff_odd, List.dropLast_eq_take, List.length_cons,
          List.length_append, length_alternatingWord, List.length_take, this, alternatingWord_succ',
          add_tsub_cancel_right, Nat.not_odd_iff_even, List.cons_append, List.cons.injEq, true_and,
          and_true]
        simp_rw [← List.cons_append, ← alternatingWord_succ']
        nth_rw 1 [← length_alternatingWord s₁ s₁' (j + 1)]
        rw [List.take_length_add_append]
        grind

open CoxeterSystem in
/-- This is the rest of "Case 2" from [Björer-Brenti, proof of 1.5.1](bjorner2005) -/
private lemma fine_cons_maximal_index
    (E : S.ExchangeProperty)
    {s₁ s₁' : B} {ω ω' : List B}
    {n : ℕ}
    (hl : ω.length = n)
    (hl' : ω'.length = n)
    (ih : ∀ m < n + 1, ∀ (ω₀ ω₀' : List B),
      ω₀.length = m → m = ω₀'.length → S.Fine ω₀ ω₀')
    (ih₂ : ∀ (s₁ s₁' : B) (ω₀ ω₀' : List B) (_ : ω₀.length = n) (_ : ω₀'.length = n)
      (_ : S.IsReduced (s₁ :: ω₀)),
      φ (s₁ :: ω₀) = φ (s₁' :: ω₀') →
        ∀ i < ω₀.length, (φ ((s₁ :: ω₀).eraseIdx i) = φ ω₀') → π (s₁ :: ω₀) = π (s₁' :: ω₀')) :
    S.Fine (s₁ :: ω) (s₁' :: ω') := by
  apply S.reduction_step E hl hl' ih ih₂
  -- at this point, ω' is no longer needed so we clear a bit the context.
  clear hl' ω'
  suffices H : ∀ j < (s₁ :: ω).length,
    S.Fine
      ((CoxeterSystem.alternatingWord s₁ s₁' (j + 1)) ++
        (s₁ :: ω).take ((s₁ :: ω).length - j - 1))
      ((CoxeterSystem.alternatingWord s₁ s₁' j) ++ (s₁ :: ω).take ((s₁ :: ω).length - j)) by
    have := H 0
    simp only [List.length_cons, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true,
      alternatingWord, List.concat_eq_append, List.nil_append, tsub_zero, add_tsub_cancel_right,
      List.cons_append, List.take_succ_cons, List.take_length, forall_const] at this
    rwa [List.take_eq_dropLast (by grind)] at this
  intro j hj
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hj
  clear hj
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hk
  simp only [List.length_cons, hk, show j + k + 1 - j = k + 1 by grind, add_tsub_cancel_right,
    List.take_succ_cons]
  apply S.fine_alternatingWord_append_induction E _ _ hk.symm (by grind) (by grind)

open scoped List in
lemma eq_of_hom_eq_one_of_exchangeProperty' (E : S.ExchangeProperty) (ω ω' : List B)
    (hl : ω.length = ω'.length) (h : S.hom (π ω) = S.hom (π ω')) :
    π ω = π ω' := by
  generalize hk : ω.length = k at hl
  induction k using Nat.strongRec generalizing ω ω' with | ind k ih =>
  cases k with
  | zero => grind [CoxeterSystem.wordProd_nil, List.length_eq_zero_iff]
  | succ n =>
    -- Consider the length of the words
    let m' := ℓ (S.hom <| π ω)
    have : m' ≤ n + 1 := hk ▸ S.length_le_of_eq_wordProd _ ω rfl
    by_cases hm'n : m' ≠ n + 1
    · -- Case 1: the words are not reduced
      exact S.nonReduced_case E (by grind) (by grind)
        (fun m n ω₀ ω₀' _ _ _ => by
          apply ih m (by grind) <;> assumption) (by grind)
    · -- Case 2 : the words are reduced: this is the harder case.
      cases ω with | nil => grind | cons s₁ ω =>
      cases ω' with | nil => grind | cons s₁' ω' =>
      exact S.fine_cons_maximal_index E rfl (by grind) (by grind)
        (fun _ _ ω ω' _ _ _ h i hi hi' =>
          S.fine_cons_non_maximal_index (by grind) (by grind) _ hi hi' (by grind) (by grind)) h

theorem injective_hom_of_exchangeProperty (E : S.ExchangeProperty) : Function.Injective S.hom := by
  rw [← MonoidHom.ker_eq_bot_iff, ← le_bot_iff]
  intro x hx
  simp only [MonoidHom.mem_ker, Subgroup.mem_bot] at hx ⊢
  obtain ⟨ω₀, hω₀, rfl⟩ := M.toCoxeterSystem.exists_reduced_word x
  generalize hk : ω₀.length = k at hω₀ ⊢
  obtain ⟨k'', rfl⟩ : ∃ u, k = 2*u := by
    have := S.even_length_of_hom_wordProd_eq_one (S.exchangeProperty_iff_deletionProperty.mpr E) ω₀
      hx
    rwa [even_iff_exists_two_mul, hk] at this
  rw [← ω₀.take_append_drop k'', CoxeterSystem.wordProd_append, map_mul,
    mul_eq_one_iff_eq_inv, ← map_inv, ← CoxeterSystem.wordProd_reverse] at hx
  let ω' := ω₀.take k''
  let ω'' := (ω₀.drop k'').reverse
  have hω' : ω'.length = k'' := by grind
  have hω'' : ω''.length = k'' := by grind
  induction k'' with
  | zero => grind [CoxeterSystem.wordProd_nil]
  | succ k'' hr =>
    suffices H : S.Fine ω' ω'' by
      have := H hx
      rwa [← ω₀.take_append_drop (k'' + 1), CoxeterSystem.wordProd_append,
        mul_eq_one_iff_eq_inv, ← CoxeterSystem.wordProd_reverse]
    intro _
    exact S.eq_of_hom_eq_one_of_exchangeProperty' E _ _ (by cutsat) (by assumption)

@[simps! mulEquiv_symm_apply]
noncomputable def toCoxeterSystem (E : S.ExchangeProperty) : CoxeterSystem M G where
  mulEquiv :=
    MulEquiv.ofBijective _ ⟨S.injective_hom_of_exchangeProperty E, S.surjective_hom⟩ |>.symm

end PreCoxeterSystem

end
