/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
module

public import Mathlib.GroupTheory.Coxeter.Recognition
public import Mathlib.GroupTheory.Perm.Fin

/-! # `Equiv.Perm (Fin (n + 1))` is a Coxeter group of type `Aₙ`.

In this file, we apply the criteria from the file `Mathlib/GroupTheory/Coxeter/Recognition.lean`
to show that the sroup `Equiv.Perm (Fin n)`, with adjacent transpositions as generators,
gives a Coxeter system of type `Aₙ`.

-- TODO: think about the API. Modulize this file better. -/

@[expose] public section

attribute [local grind =] Equiv.Perm.mul_apply Equiv.Perm.one_apply

attribute [local ext, local grind ext] Fin.ext
attribute [local grind =] Fin.val_succ Fin.coe_castSucc

private lemma Equiv.Perm.orderOf_swap_mul_swap_eq_three_of_ne {α : Type*} [DecidableEq α]
      (a b c d : α) (_ : a ≠ b) (_ : a ≠ c) (_ : c ≠ d)
      (hb : (c = b ∧ d ≠ a) ∨ (d = a ∧ c ≠ b)) :
    orderOf ((Equiv.swap a b) * (Equiv.swap c d)) = 3 := by
  rw [orderOf_eq_prime (p := 3)]
  · grind (splits := 16) [swap_apply_of_ne_of_ne, pow_three]
  · intro h
    have e₄ := congr($h d)
    grind [swap_apply_of_ne_of_ne]

private lemma Equiv.Perm.orderOf_swap_mul_swap_eq_two_of_nodup
    {α : Type*} [DecidableEq α] (a b c d : α) (h : [a, b, c, d].Nodup) :
    orderOf ((Equiv.swap a b) * (Equiv.swap c d)) = 2 := by
  rw [orderOf_eq_prime (p := 2)]
  · grind (splits := 16) [swap_apply_of_ne_of_ne, pow_two]
  · intro h
    have := congr($h a)
    grind

/-- The canonical morphism that realizes the Coxeter group of the Coxeter matrix Aₙ
in the symmetric group. It sends the generator `i` to the transposition `(i, i + 1)`. -/
def CoxeterMatrix.Aₙ_to_perm (n : ℕ) : (CoxeterMatrix.Aₙ n).Group →* Equiv.Perm (Fin (n + 1)) :=
  (CoxeterMatrix.Aₙ n).toCoxeterSystem.lift
    ⟨fun i ↦ Equiv.swap i.castSucc i.succ, fun i j => by
        have succ_ne_castSucc : ∀ (i : Fin n), i.succ ≠ i.castSucc := by
          grind [Fin.coe_castSucc, Fin.val_succ]
        dsimp [CoxeterMatrix.Aₙ]
        split_ifs with h h' <;> (convert pow_orderOf_eq_one _; symm)
        · subst h
          simp
        · grind [Equiv.Perm.orderOf_swap_mul_swap_eq_three_of_ne]
        · grind [Equiv.Perm.orderOf_swap_mul_swap_eq_two_of_nodup]⟩


@[simp]
lemma CoxeterMatrix.Aₙ_to_perm_simple {n : ℕ} (j : Fin n) :
    CoxeterMatrix.Aₙ_to_perm n ((CoxeterMatrix.Aₙ n).simple j) = Equiv.swap j.castSucc j.succ := rfl

@[simp]
lemma CoxeterMatrix.Aₙ_to_perm_simple' {n : ℕ} (j : Fin n) :
    CoxeterMatrix.Aₙ_to_perm n ((CoxeterMatrix.Aₙ n).toCoxeterSystem.simple j) =
    Equiv.swap j.castSucc j.succ := rfl

def Fin.preCoxeterSystem (n : ℕ) :
    PreCoxeterSystem (CoxeterMatrix.Aₙ n) (Equiv.Perm (Fin (n + 1))) where
  hom := CoxeterMatrix.Aₙ_to_perm n
  surjective_hom := by
    -- Equiv.Perm.mclosure_swap_castSucc_succ
    rw [← MonoidHom.mrange_eq_top, eq_top_iff, ← Equiv.Perm.mclosure_swap_castSucc_succ n]
    -- have := Equiv.Perm.mclosure_swap_castSucc_succ n
    simp [Set.range_subset_iff]
    intro i
    exact ⟨(CoxeterMatrix.Aₙ n).toCoxeterSystem.simple i, rfl⟩
  orderOf_eq i j := by
    -- TODO prove this separately and use in the def of Aₙ_to_perm instead
    have succ_ne_castSucc : ∀ (i : Fin n), i.succ ≠ i.castSucc := by
      grind [Fin.coe_castSucc, Fin.val_succ]
    simp
    simp [CoxeterMatrix.Aₙ]
    split_ifs with h h' <;> symm
    · subst h
      simp
    · grind [Equiv.Perm.orderOf_swap_mul_swap_eq_three_of_ne]
    · grind [Equiv.Perm.orderOf_swap_mul_swap_eq_two_of_nodup]
  hom_simple_ne_one i := by
    simp only [CoxeterMatrix.Aₙ_to_perm_simple, ne_eq, Equiv.swap_eq_one_iff]
    grind [Fin.coe_castSucc, Fin.val_succ]

variable {n : ℕ}

@[simp, grind =]
lemma preCoxeterSystem_hom_simple (i : Fin n) :
    (Fin.preCoxeterSystem n).hom ((CoxeterMatrix.Aₙ n).simple i) =
    Equiv.swap i.castSucc i.succ :=
  rfl

section exchange
/-! This section is devoted to showing that `Fin.PreCoxeterSystem` defined above satisfies the
"exchange property" (see `Mathlib/GroupTheory/Coxeter/Recognition.lean`). To show this,
one must first relate the the length in the sense of this preCoxeterSystem to a more
known notion: the inversion number of a permutation. -/

local prefix:100 "ℐ " => Fin.inversionSet
local prefix:100 "ι " => Fin.inversionNumber

local notation "Ψ " x:max => Equiv.swap (Fin.castSucc x) (Fin.succ x)

private lemma inversionNumber_le_length (σ : Equiv.Perm (Fin (n + 1))) :
    ι σ ≤ (Fin.preCoxeterSystem n).length σ := by
  obtain ⟨ω, hω, hred⟩ := Fin.preCoxeterSystem n |>.exists_reduced_word σ
  rw [← hω, ← hred]
  clear hω hred
  induction ω using List.reverseRecOn generalizing σ with
  | nil => simpa using Fin.inversionNumber_one
  | append_singleton ω s ih =>
    simp [CoxeterSystem.wordProd_append,
      Fin.preCoxeterSystem] at ⊢
    simp at ih
    rw [Fin.inversionNumber_mul_swap_castSucc_succ_eq]
    suffices h :
        ι (CoxeterMatrix.Aₙ_to_perm n)
          ((CoxeterMatrix.Aₙ n).toCoxeterSystem.wordProd ω) ≤ ω.length by
      grind
    exact ih

private lemma length_le_inversionNumber (σ : Equiv.Perm (Fin (n + 1))) :
   (Fin.preCoxeterSystem n).length σ ≤ ι σ := by
  induction h : ι σ generalizing σ with
  | zero => simpa [← Fin.inversionNumber_eq_zero_iff] using h
  | succ k ih =>
    obtain ⟨i, hi⟩ : ∃ i : Fin n, ι (σ * (Ψ i)) = k := by
      by_contra! h'
      simp only [Fin.inversionNumber_mul_swap_castSucc_succ_eq, h, add_tsub_cancel_right, ne_eq,
        ite_eq_right_iff, Classical.not_imp] at h'
      suffices σ = 1 by grind [Fin.inversionNumber_one]
      suffices StrictMono σ by
        have := le_antisymm (StrictMono.le_id this) (StrictMono.id_le this)
        ext x
        exact congr($this x)
      exact Fin.strictMono_iff_lt_succ.mpr (by grind)
    have hr := ih (σ * (Ψ i)) hi
    have le' := (Fin.preCoxeterSystem n).length_mul_le (σ * (Ψ i)) (Ψ i)
    have : (Fin.preCoxeterSystem n).length (Ψ i) = 1 := by
      simpa using (Fin.preCoxeterSystem n).length_simple i
    simp only [Equiv.mul_swap_mul_self, this] at le'
    grind

theorem length_eq_inversionNumber (σ : Equiv.Perm (Fin (n + 1))) :
   (Fin.preCoxeterSystem n).length σ = ι σ :=
  le_antisymm (length_le_inversionNumber σ) (inversionNumber_le_length σ)

-- Local non-hygienic notation, but really saves space in what follows.
set_option quotPrecheck false in
local notation "φ " x:max =>
  (Fin.preCoxeterSystem n).hom ((CoxeterMatrix.Aₙ n).toCoxeterSystem.wordProd x)


theorem exchange : (Fin.preCoxeterSystem n).ExchangeProperty' := by
  intro ω hω i hi
  simp [CoxeterSystem.wordProd_append] at hi ⊢
  dsimp [PreCoxeterSystem.IsReduced] at hω
  rw [← hω]
  set σ := φ ω
  simp [length_eq_inversionNumber] at *
  have inversion : σ i.succ < σ i.castSucc := by
    grind [Fin.inversionNumber_mul_swap_castSucc_succ_eq, Equiv.injective,
      Fin.lt_def, Fin.val_succ, Fin.coe_castSucc]
  -- Names and notations from Björner-Brenti
  let b := σ i.castSucc
  let a := σ i.succ
  have a_ne_b : a ≠ b := by grind
  -- if ω = [s₁, …, sₖ], Consider the first index for which [s₁,…, sᵢ] "inverts b and a"
  let i₀ := ω.inits.findIdx (fun l ↦ (φ l)⁻¹ b < (φ l)⁻¹ a)
  -- as [s₁,…, sₖ]  inverts a and b, i₀ is at least < ω.length + 1,
  -- (the number of initial sublists of ω)
  have hi₀ : i₀ < ω.length + 1 := by
    dsimp [i₀]
    rw [← List.length_inits, List.findIdx_lt_length]
    exact ⟨ω, by simp, by simp [a, b, σ]⟩
  -- as [] does not inverts a and b, 0 < i₀
  have hi₀' : 0 < i₀ := by
    dsimp [i₀]
    apply List.lt_findIdx_of_not
    · intro j hj
      simp only [nonpos_iff_eq_zero] at hj
      subst hj
      simpa [a, b, σ] using inversion.le
    · simp
  -- by definition, ω.take i₀ "inverts b and a"
  have inv₀ : (φ (ω.take i₀))⁻¹ b < (φ (ω.take i₀))⁻¹ a := by
    simpa using
      ω.inits.findIdx_getElem (p := fun l ↦ (φ l)⁻¹ b < (φ l)⁻¹ a) (w := by simpa using hi₀)
  have inv₁ : ∀ j < i₀, (φ (ω.take j))⁻¹ a < (φ (ω.take j))⁻¹ b := by
    intro j hj
    have : (φ (ω.take j))⁻¹ a ≤ (φ (ω.take j))⁻¹ b := by
      simpa using ω.inits.not_of_lt_findIdx (p := fun l ↦ (φ l)⁻¹ b < (φ l)⁻¹ a) hj
    grind [Equiv.injective]
  obtain ⟨i'', hi''⟩ := Nat.exists_add_one_eq.mpr hi₀'
  simp [← hi''] at inv₀ inv₁ hi₀ hi₀'
  rw [List.take_succ_eq_append_getElem hi₀] at inv₀
  -- Let’s use this index.
  use i''
  refine ⟨by grind, ?_⟩
  ext k : 1
  -- We compute ω[i''] in terms of i
  obtain ⟨e₁, e₂⟩ :
    (φ (ω.drop i'')) i.succ = ω[i''].castSucc ∧
      (φ (ω.drop i'')) i.castSucc = ω[i''].succ := by
    -- The idea is to show this is an inversion for Equiv.swap ω[i''].castSucc ω[i''].succ.
    have inv₀' := inv₁ i'' (lt_add_one i'')
    simp only [↓CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton,
      CoxeterMatrix.toCoxeterSystem_simple, map_mul, preCoxeterSystem_hom_simple,
      ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.coe_mul, Equiv.Perm.coe_inv,
      Function.comp_apply, a, σ, b] at inv₀ inv₀'
    nth_rewrite 4 8 [← ω.take_append_drop i''] at inv₀
    nth_rewrite 2 4 [← ω.take_append_drop i''] at inv₀'
    simp only [↓CoxeterSystem.wordProd_append, map_mul, Equiv.Perm.coe_mul, Function.comp_apply,
      Equiv.symm_apply_apply] at inv₀ inv₀'
    have : ((φ (ω.drop i'')) i.succ, (φ (ω.drop i'')) i.castSucc) ∈ (ℐ (Ψ ω[i''])) := by
      grind
    simpa [Fin.inversionSet_swap_castSucc] using this
  obtain ⟨e₁', e₂'⟩ :
    (φ (ω.drop (i'' + 1))) i.succ = ω[i''].succ ∧
      (φ (ω.drop (i'' + 1))) i.castSucc = ω[i''].castSucc := by
    nth_rewrite 1 [← (ω.drop i'').cons_head_tail (by simpa using hi₀)] at e₁ e₂
    simp only [↓CoxeterSystem.wordProd_cons, List.head_drop, CoxeterMatrix.toCoxeterSystem_simple,
      List.tail_drop, map_mul, preCoxeterSystem_hom_simple, Equiv.Perm.coe_mul,
      Function.comp_apply] at e₁ e₂
    grind
  -- Thanks to that computation, we can now compute the value on both sides depending on
  -- wether or not `k ∈ {i.castSucc, i.succ}`, and observe the results are the same.
  simp only [Equiv.Perm.coe_mul, Function.comp_apply, List.eraseIdx_eq_take_drop_succ,
    CoxeterSystem.wordProd_append, map_mul]
  by_cases! hk : k = i.castSucc ∨ k = i.succ
  · dsimp [σ, a, b]
    nth_rewrite 1 [← ω.take_append_drop i'']
    simp only [↓CoxeterSystem.wordProd_append, map_mul, Equiv.Perm.coe_mul, Function.comp_apply,
      EmbeddingLike.apply_eq_iff_eq]
    grind
  · rw [Equiv.swap_apply_of_ne_of_ne hk.1 hk.2]
    dsimp [σ]
    nth_rewrite 1 [← ω.take_append_drop (i'' + 1), List.take_succ_eq_append_getElem hi₀]
    simp only [↓CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_singleton,
      CoxeterMatrix.toCoxeterSystem_simple, map_mul, preCoxeterSystem_hom_simple,
      Equiv.Perm.coe_mul, Function.comp_apply, EmbeddingLike.apply_eq_iff_eq]
    grind [Equiv.swap_apply_of_ne_of_ne, Equiv.injective]

end exchange

noncomputable def Fin.coxeterSystem (n : ℕ) :
    CoxeterSystem (CoxeterMatrix.Aₙ n) (Equiv.Perm (Fin (n + 1))) :=
  (Fin.preCoxeterSystem n).toCoxeterSystem
   ((Fin.preCoxeterSystem n).exchangeProperty_iff_exchangeProperty'.mpr exchange)

lemma Fin.coxeterSystem_simple (i : Fin n) :
    (Fin.coxeterSystem n).simple i = Equiv.swap i.castSucc i.succ := rfl

end
