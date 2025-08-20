/-
Copyright (c) 2025 Robin Carlier. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Carlier
-/
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.ComposableArrows
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases

/-! # Coherent tensor families of elements in monoidal categories

In this file, we construct an `n`-ary tensor product functor
`tensorProdFunctor : (Fin (n + 1) → C) ⥤ C`, which takes
an n-uple `(x₀, x₁, x₂, …, xₙ)` to `x₀ ⊗ x₁ ⊗ ⋯ ⊗ xₙ`. This functor
is recursively defined, and thus does not have very good defeqs and
is hard to work with in general, in general,
though it does have nice defeqs for small explicit values of `n`.

The bulk of this file deals with the fact that
this construction is in fact functorial with respect to
functors `Fin (n + 1) ⥤ Fin (m + 1)`: informally, a functor
`Φ : Fin (n + 1) ⥤ Fin (m + 1)` will transform
`x₀ ⊗ ⋯ ⊗ xᵢ ⊗ ⋯ ⊗ xₘ` to the tensor product of the
xⱼ for `j ∈ Φ⁻¹ {i}`. The core difficulty here is that one
needs to deal with the fact that the expressions gets reassociated in
this description; the inductive definition of `tensorProdFunctor` is
very badly suited for this kind of manipulations.

To deal with this problem, we introduce a construction `CoherentTensorFamily C n`,
which is a model with better defeq for pseudofunctors from
`LocallyDiscrete (Fin (n + 1))` to `MonoidalSingleObj C`: such data
consists of families of objects of `c` indexed by inequalities `i ≤ j`,
with extra coherence isomorphisms of the form `c i j ⊗ c j k ≅ c i k` added
for `i ≤ j ≤ k`: these family have good functoriality properies with respect
to functors `Φ : Fin (n + 1) ⥤ Fin (m + 1)`, which intuitively corresponds
here with precomposition of pseudofunctors.

We then inductively construct an equivalene of categories
`CoherentTensorFamily C n ≌ Fin n ⟶ C`, and show that
through the identification `CoherentTensorFamily C 1 ≌ C`, the operation
`CoherentTensorFamily C n ⥤ C` that sends a family `i, j ↦ c i j` to `c 0 n`
is is indeed naturaly isomorphic to
`tensorProdFunctor : (Fin (n + 1) → C) ⥤ C`: this is the isomorphism
`tupleEquivFunctorHomFunctor` near the end of this file.

-/

universe v u

namespace CategoryTheory.MonoidalCategory

variable (C : Type u) [Category.{v} C] [MonoidalCategory C]

/-- A wrapper for `grind` which prefaces it with some quick and useful
attempts -/
macro "valid" : tactic =>
  `(tactic|
      first
      | assumption
      | apply le_rfl
      | apply zero_le
      | transitivity <;> assumption
      | grind)

attribute [local grind] Fin.le_def Fin.zero_le

structure CoherentTensorFamily (n : ℕ) where
  c (i j : Fin (n + 1)) (hij := by valid) : C
  Δ (i j k : Fin (n + 1))
    (hij : i ≤ j := by valid) (hjk : j ≤ k := by valid) :
    c i j ⊗ c j k ≅ c i k (hij.trans hjk)
  η (i : Fin (n + 1)) : c i i (le_refl i) ≅ 𝟙_ C
  Δ_comp (i j k l : Fin (n + 1))
      (hij : i ≤ j := by valid) (hkj : j ≤ k := by valid)
      (hkl : k ≤ l := by valid) :
      (Δ i j k).hom ▷ c k l ≫ (Δ i k l).hom =
      (α_ (c i j) (c j k) (c k l)).hom ≫
        c i j ◁ (Δ j k l).hom ≫ (Δ i j l).hom := by
    cat_disch
  Δ_id_right (i j : Fin (n + 1)) (hij : i ≤ j := by valid) :
    (Δ i j j).hom = c i j ◁ (η j).hom ≫ (ρ_ (c i j)).hom := by cat_disch
  Δ_id_left (i j : Fin (n + 1)) (hij : i ≤ j := by valid) :
    (Δ i i j).hom = (η i).hom ▷ c i j ≫ (λ_ (c i j)).hom := by cat_disch

namespace CoherentTensorFamily

attribute [simp, reassoc, grind] Δ_id_right Δ_id_left
attribute [grind _=_] Δ_comp

variable {C} {n : ℕ}

@[simp]
abbrev hom {n : ℕ} (δ : CoherentTensorFamily C n) : C :=
  δ.c 0 ⟨n, by valid⟩ (bot_le)

@[ext, grind ext]
structure Hom (δ δ' : CoherentTensorFamily C n) where
  φ (i j : Fin (n + 1)) (hij : i ≤ j := by valid) : δ.c i j ⟶ δ'.c i j
  φ_comp (i j k : Fin (n + 1))
      (hij : i ≤ j := by valid) (hjk : j ≤ k := by valid) :
      (δ.Δ i j k).hom ≫ φ i k =
      δ.c i j ◁ φ j k ≫ φ i j ▷ δ'.c j k ≫ (δ'.Δ i j k).hom := by
    cat_disch
  φ_id (i : Fin (n + 1)) : φ i i = (δ.η i).hom ≫ (δ'.η i).inv := by cat_disch

namespace Hom

attribute [reassoc (attr := simp)] φ_id φ_comp

@[simps!]
def comp {δ δ' δ'' : CoherentTensorFamily C n} (f : Hom δ δ') (g : Hom δ' δ'') :
    Hom δ δ'' where
  φ i j hij := f.φ i j ≫ g.φ i j
  φ_comp i j k hij hjk := by simp [whisker_exchange_assoc]

end Hom

@[simps!]
instance : Category (CoherentTensorFamily C n) where
  Hom := Hom
  comp f g :=
    { φ i j hij := f.φ i j ≫ g.φ i j
      φ_comp i j k hij hjk := by simp [whisker_exchange_assoc] }
  id f := { φ i j hij := 𝟙 _ }

attribute [grind] id_φ
attribute [grind _=_] comp_φ

@[ext, grind ext]
lemma hom_ext {δ δ' : CoherentTensorFamily C n} {f g : δ ⟶ δ'}
    (h : ∀ (i j : Fin (n + 1)) (hij : i ≤ j), f.φ i j = g.φ i j) :
    f = g := by
  change Hom _ _ at f g
  change @Eq (Hom _ _) _ _
  ext
  apply h

variable (C) in
/-- The `CoherentTensorFamily` where every object is the unit object -/
@[simps]
def unit (n : ℕ) : CoherentTensorFamily C n where
  c _ _ _ := 𝟙_ C
  Δ _ _ _ _ _ := λ_ _
  η _ := .refl _
  Δ_comp i j k l _ _ _ := by
    simp [unitors_equal]
  Δ_id_left i j _ := by
    simp [unitors_equal]
  Δ_id_right i j _ := by
    simp [unitors_equal]

@[simps]
instance : Inhabited (CoherentTensorFamily C n) where
  default := unit C n

@[grind <=]
private lemma monotone_functor {n m : ℕ} {Φ : Fin (n + 1) ⥤ Fin (m + 1)}
    (i j : Fin (n + 1)) (hij : i ≤ j) :
    Φ.obj i ≤ Φ.obj j :=
  Φ.monotone hij

@[simps]
def whiskerLeftFunctor {n m : ℕ} (Φ : Fin (n + 1) ⥤ Fin (m + 1)) :
    CoherentTensorFamily C m ⥤ CoherentTensorFamily C n where
  obj δ :=
    { c i j hij := δ.c (Φ.obj i) (Φ.obj j)
      Δ i j k hij hjk := δ.Δ (Φ.obj i) (Φ.obj j) (Φ.obj k)
      η i := δ.η (Φ.obj i)
      Δ_comp i j k l hij hjk hkl :=
        δ.Δ_comp (Φ.obj i) (Φ.obj j) (Φ.obj k) (Φ.obj l) }
  map {δ δ'} f := { φ i j hij := f.φ (Φ.obj i) (Φ.obj j) }

section

/-- The functor `Fin 1 ⥤ Fin (n + 1)` induced by the inclusion. -/
def _root_.Fin.inclFunctor (n : ℕ) : Fin 2 ⥤ Fin (n + 2) :=
    (Fin.castLEOrderEmb (by valid)).toOrderHom.toFunctor

@[simp]
lemma _root_.Fin.inclFunctor_obj_zero (n : ℕ) :
    (Fin.inclFunctor n).obj 0 = 0 := by
  rfl

@[simp]
lemma _root_.Fin.inclFunctor_obj_zero' (n : ℕ) :
    (Fin.inclFunctor n).obj ⟨0, by valid⟩ = 0 := by
  rfl

@[simp]
lemma _root_.Fin.inclFunctor_obj_one (n : ℕ) :
    (Fin.inclFunctor n).obj 1 = 1 := by
  rfl

@[simp]
lemma _root_.Fin.inclFunctor_obj_one' (n : ℕ) :
    (Fin.inclFunctor n).obj ⟨1, by valid⟩ = 1 := by
  rfl

variable (C) in
@[simps!]
def fstArrow (n : ℕ) :
    CoherentTensorFamily C (n + 1) ⥤ CoherentTensorFamily C 1 :=
  whiskerLeftFunctor (Fin.inclFunctor _)

@[simp]
lemma fstArrow_obj_c_zero_one {n : ℕ} (δ : CoherentTensorFamily C (n + 1)) :
    (fstArrow C n|>.obj δ).c 0 1 (by simp) = δ.c 0 1 (by simp) :=
  rfl

@[simp]
lemma fstArrow_obj_η_zero {n : ℕ} (δ : CoherentTensorFamily C (n + 1)) :
    (fstArrow C n|>.obj δ).η 0 = δ.η 0 :=
  rfl

@[simp]
lemma fstArrow_obj_η_one {n : ℕ} (δ : CoherentTensorFamily C (n + 1)) :
    (fstArrow C n|>.obj δ).η 1 = δ.η 1 :=
  rfl

@[simp]
lemma fstArrow_obj_hom {n : ℕ} (δ : CoherentTensorFamily C (n + 1)) :
    (fstArrow C n|>.obj δ).hom = δ.c 0 1 (by simp) :=
  rfl

@[simp]
lemma fstArrow_map_φ_zero_zero {n : ℕ} {δ δ' : CoherentTensorFamily C (n + 1)}
    (f : δ ⟶ δ') :
    (fstArrow C n|>.map f).φ 0 0 = f.φ 0 0 :=
  rfl

@[simp]
lemma fstArrow_map_φ_zero_one {n : ℕ} {δ δ' : CoherentTensorFamily C (n + 1)}
    (f : δ ⟶ δ') :
    (fstArrow C n|>.map f).φ 0 1 = f.φ 0 1 (by simp) :=
  rfl

@[simp]
lemma fstArrow_map_φ_one_one {n : ℕ} {δ δ' : CoherentTensorFamily C (n + 1)}
    (f : δ ⟶ δ') :
    (fstArrow C n|>.map f).φ 1 1 = f.φ 1 1 :=
  rfl

end

variable (C) in
@[simps!]
def δ₀Functor (n : ℕ) :
    CoherentTensorFamily C (n + 1) ⥤ CoherentTensorFamily C n :=
  whiskerLeftFunctor (Fin.succFunctor _)

/-- An `extension` of `δ : CoherentTensorFamily C n` bundles the data required
to extend `δ` to a `CoherentTensorFamily C (n + 1)` such that the
last face of the extended family is `δ` (see `extension.family`). -/
structure extension (δ : CoherentTensorFamily C n) where
  /-- For every `i : Fin (n + 1)`, an element of `C`. This will
  correspond to `c 0 i` in the extended family. The name is primed so that
  `extension.c` can be used for the `c` field of the extended family. -/
  c' (i : Fin (n + 2)) : C
  /-- For every `j ≤ k : Fin (n + 1)` with `k + 1 < n + 1`, an isomorphism
  `a (j + 1) ⊗ δ.c j k ≅ a (k + 1)`. This will correspond to
  `Δ 0 (i + 1) (j + 1)` in the extended family.
  The name is primed so that the name `extension.Δ` can be used for the actual
  construction of the `Δ` field of the extended family. -/
  Δ' (j k : ℕ) (hjk : j ≤ k := by valid) (hkn : k + 1 < n + 2 := by valid) :
    c' ⟨j + 1, by valid⟩ ⊗ δ.c ⟨j, by valid⟩ ⟨k, by valid⟩ ≅
    c' ⟨k + 1, by valid⟩
  /-- An isomorphism `a 0 ≅ 𝟙_ C`. The name is primed, as the name
  `extension.η` will be used for the field `η` of the extended family. -/
  η' : c' 0 ≅ 𝟙_ C
  Δ'_comp (i j k : ℕ) (hij : i ≤ j := by valid) (hjk : j ≤ k := by valid)
      (hkn : k + 1 < n + 2 := by valid) :
    (Δ' i j).hom ▷ δ.c ⟨j, by valid⟩ ⟨k, by valid⟩ ≫ (Δ' j k).hom =
    (α_ (c' ⟨i + 1, by valid⟩)
      (δ.c ⟨i, by valid⟩ ⟨j, by valid⟩)
      (δ.c ⟨j, by valid⟩ ⟨k, by valid⟩)).hom ≫
      _ ◁ (δ.Δ ⟨i, by valid⟩ ⟨j, by valid⟩ ⟨k, by valid⟩).hom ≫
      (Δ' i k).hom
  Δ'_id (j : ℕ) (hkn : j + 1 < n + 2 := by valid) :
    (Δ' j j).hom =
    c' ⟨j + 1, (by valid)⟩ ◁ (δ.η ⟨j, by valid⟩).hom ≫
      (ρ_ (c' ⟨j + 1, by valid⟩)).hom

namespace extension

variable {δ : CoherentTensorFamily C n} (e : extension δ)

/-- (impl.) The `c` field of `extension.family`. -/
def c : ∀ (i j : Fin (n + 2)) (_ : i ≤ j := by valid), C
  | ⟨0, _⟩, i, _ => e.c' i
  | ⟨i + 1, _⟩, ⟨j + 1, _⟩, hij => δ.c ⟨i, by valid⟩ ⟨j, by valid⟩

@[simp] lemma c_zero (i : Fin (n + 2)) : e.c 0 i = e.c' i := rfl
@[simp] lemma c_succ_succ (i j : ℕ) (hi : i + 1 < n + 2) (hj : j + 1 < n + 2)
    (hij : (⟨i + 1, hi⟩ : Fin (n + 2)) ≤ ⟨j + 1, hj⟩) :
  e.c ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ = δ.c ⟨i, by valid⟩ ⟨j, by valid⟩ := rfl

/-- (impl.) The `c` field of `extension.family`. -/
def η : ∀ (i : Fin (n + 2)), e.c i i (le_refl i) ≅ 𝟙_ C
  | ⟨0, _⟩ => e.η'
  | ⟨i + 1, _⟩ => δ.η ⟨i, by valid⟩

@[simp] lemma η_zero : e.η 0 = e.η' := rfl
@[simp] lemma η_succ (i : ℕ) (hi : i + 1 < n + 2) :
  e.η ⟨i + 1, hi⟩ = δ.η ⟨i, by valid⟩ := rfl

/-- (impl.) The `Δ` field of `extension.family`. -/
def Δ :
    ∀ (i j k: Fin (n + 2)) (_ : i ≤ j := by valid) (_ : j ≤ k := by valid),
      (e.c i j) ⊗ (e.c j k) ≅ e.c i k
  | ⟨0, _⟩, ⟨0, _⟩, _, _, _ => whiskerRightIso (e.η _) _ ≪≫ λ_ _
  | ⟨0, _⟩, ⟨j + 1, hj⟩, ⟨k + 1, hk⟩, _, _ => e.Δ' j k _ _
  | ⟨i + 1, _⟩, ⟨j + 1, _⟩, ⟨k + 1, _⟩, _, _ =>
    δ.Δ ⟨i, by valid⟩ ⟨j, by valid⟩ ⟨k, by valid⟩

/-- Packages the data of an extension into a `CoherentTensorFamily`.
This is the main inductive constructor for coherent tensor families. -/
def family : CoherentTensorFamily C (n + 1) where
  c i j hj := e.c i j
  η := e.η
  Δ i j k _ _ := e.Δ i j k
  Δ_comp i j k l hij hjk hkl := by
    -- Nothing is hard, but there are quite a few cases to cover.
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    obtain ⟨k, hk⟩ := k
    obtain ⟨l, hk⟩ := l
    simp only [Fin.mk_le_mk] at hij hjk hkl
    obtain _ | i := i
    · obtain _ | j := j
      · obtain _ | k := k
        · simp only [Fin.zero_eta, c_zero, Δ, η_zero, Iso.trans_hom,
            whiskerRightIso_hom, comp_whiskerRight, leftUnitor_whiskerRight,
            Category.assoc, whiskerLeft_comp]
          rw [← cancel_epi (e.η'.inv ▷ e.c' 0 ▷ e.c' ⟨l, by valid⟩)]
          simp only [← comp_whiskerRight_assoc, leftUnitor_tensor_hom_assoc,
            Iso.hom_inv_id_assoc,
            associator_naturality_left_assoc, ← whisker_exchange_assoc,
            ← whisker_exchange_assoc]
          simp
        · obtain _ | l := l
          · grind
          · simp [Δ, whisker_exchange_assoc]
      · obtain _ | k := k
        · grind
        · obtain _ | l := l
          · grind
          · obtain h | hjk := hjk.eq_or_lt
            · simp at h
              subst h
              simpa using e.Δ'_comp j j l
            · obtain h' | hkl := hkl.eq_or_lt
              · simp only [Nat.add_right_cancel_iff] at h'
                subst h'
                simpa using e.Δ'_comp j k k
              · simp [Δ, e.Δ'_comp j k l]
    · obtain _ | j := j
      · grind
      · obtain _ | k := k
        · grind
        · obtain _ | l := l
          · grind
          · simpa [Δ] using
              δ.Δ_comp ⟨i, by valid⟩ ⟨j, by valid⟩ ⟨k, by valid⟩ ⟨l, by valid⟩
                _ _ (by simpa using hkl)
  Δ_id_left i j hij := by
    obtain _ | i := i
    · simp [Δ]
    · obtain _ | j := j
      · grind
      · simp [Δ]
  Δ_id_right i j hij := by
    obtain _ | i := i
    · obtain _ | j := j
      · simp only [Fin.zero_eta, c_zero, Δ, η_zero, Iso.trans_hom,
          whiskerRightIso_hom]
        rw [← cancel_epi (e.η'.inv ▷ e.c' 0)]
        simp [← whisker_exchange_assoc, ← unitors_equal]
      · simp [Δ, e.Δ'_id j]
    · obtain _ | j := j
      · grind
      · simp [Δ]

section

@[simp]
lemma family_c_zero (i : Fin (n + 2)) : e.family.c 0 i = e.c' i := rfl

@[simp]
lemma family_c_succ_succ (i j : ℕ) (hi : i + 1 < n + 2) (hj : j + 1 < n + 2)
    (hij : (⟨i + 1, hi⟩ : Fin (n + 2)) ≤ ⟨j + 1, hj⟩) :
    e.family.c ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ = δ.c ⟨i, by valid⟩ ⟨j, by valid⟩ :=
  rfl

@[simp]
lemma family_c_one_succ (j : ℕ) (hj : j + 1 < n + 2) :
    e.family.c 1 ⟨j + 1, hj⟩ (by simp [← Fin.mk_one]) = δ.c 0 ⟨j, by valid⟩ :=
  rfl

@[simp]
lemma family_Δ_zero_zero (i : Fin (n + 2)) :
    e.family.Δ 0 0 i = whiskerRightIso e.η' _ ≪≫ λ_ _ := rfl

@[simp]
lemma family_Δ_zero_succ_succ
    (i j : ℕ) (hi : i + 1 < n + 2) (hj : j + 1 < n + 2)
    (hij : (⟨i + 1, hi⟩ : Fin (n + 2)) ≤ ⟨j + 1, hj⟩) :
    e.family.Δ 0 ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ = e.Δ' i j _ _ :=
  rfl

@[simp]
lemma family_Δ_zero_one_succ
    (j : ℕ) (hj : j + 1 < n + 2) :
    e.family.Δ 0 1 ⟨j + 1, hj⟩ (by simp) (by simp [← Fin.mk_one]) = e.Δ' 0 j _ _ :=
  rfl


@[simp]
lemma family_Δ_succ_succ_succ
    (i j k : ℕ) (hi : i + 1 < n + 2) (hj : j + 1 < n + 2)
    (hk : k + 1 < n + 2)
    (hij : (⟨i + 1, hi⟩ : Fin (n + 2)) ≤ ⟨j + 1, hj⟩)
    (hjk : (⟨j + 1, hj⟩ : Fin (n + 2)) ≤ ⟨k + 1, hk⟩) :
    e.family.Δ ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ ⟨k + 1, hk⟩ hij hjk =
      δ.Δ ⟨i, by valid⟩ ⟨j, by valid⟩ ⟨k, by valid⟩ :=
  rfl

/-- The last face of the extended family isomorphic (in fact, equal) to the
family we extend. -/
@[simps!]
def δ₀FamilyIso : (δ₀Functor C n).obj e.family ≅ δ := .refl _

end

end extension

/-- Given a `δ : CoherentTensorFamily C n` and `c : C`, there is a
an extension of `δ` that puts `c` as the "first element" of the extension,
and lets all the remaining isomorphism data be identities. -/
def tensorExtension (c : C) (δ : CoherentTensorFamily C n) :
    extension δ where
  c'
  | ⟨0, _⟩ => (𝟙_ C)
  | ⟨1, _⟩ => c
  | ⟨j + 2, hj⟩ => c ⊗ δ.c 0 ⟨j + 1, by valid⟩
  Δ'
  | 0, 0, _, _ => whiskerLeftIso c (δ.η _) ≪≫ ρ_ _
  | 0, (j + 1), _, _ => .refl _
  | (i + 1), (j + 1), _, _ => α_ _ _ _ ≪≫ whiskerLeftIso c (δ.Δ _ _ _)
  η' := .refl _
  Δ'_comp i j k hij hjk hkn := by
    obtain _ | i := i
    · obtain _ | j := j
      · obtain _ | k := k
        · dsimp [← Fin.mk_one]
          simp only [comp_whiskerRight, whisker_assoc, Category.assoc,
            triangle_assoc_comp_right, Δ_id_right, whiskerLeft_comp,
            whiskerLeft_rightUnitor, Iso.cancel_iso_hom_left]
          rw [← cancel_epi (c ◁ (δ.η 0).inv ▷ δ.c 0 0 hjk)]
          simp only [← whiskerLeft_comp_assoc, inv_hom_whiskerRight_assoc,
            ← whisker_exchange]
          simp
        · dsimp [← Fin.mk_one]
          simp only [comp_whiskerRight, whisker_assoc, Category.assoc,
            triangle_assoc_comp_right, Iso.cancel_iso_hom_left]
          rw [← cancel_epi (c ◁ (δ.η 0).inv ▷ δ.c 0 ⟨k + 1, by valid⟩ hjk)]
          simp only [← whiskerLeft_comp_assoc, inv_hom_whiskerRight_assoc]
          simp
      · obtain _ | k := k
        · grind
        · dsimp [← Fin.mk_one]
          simp
    · obtain _ | j := j
      · grind
      · obtain _ | k := k
        · grind
        · dsimp
          rw [← cancel_epi ((α_ c (δ.c 0 ⟨i + 1, by valid⟩)
              (δ.c ⟨i + 1, by valid⟩ ⟨j + 1, by valid⟩ hij)).inv ▷
              δ.c ⟨j + 1, by valid⟩ ⟨k + 1, by valid⟩ hjk)]
          simp only [comp_whiskerRight, whisker_assoc, Category.assoc,
            Iso.inv_hom_id_assoc, inv_hom_whiskerRight_assoc, tensor_whiskerLeft,
            pentagon_inv_hom_hom_hom_hom_assoc, Iso.cancel_iso_hom_left]
          simp only [← whiskerLeft_comp]
          congr 1
          simpa using δ.Δ_comp 0 _ _ _
  Δ'_id i hi := by
    obtain _ | i := i
    · rfl
    · simp

section
variable (c : C) (δ : CoherentTensorFamily C n)
@[simp]
lemma tensorExtension_Δ'_zero_succ (j : ℕ) (hj : j + 1 + 1 < n + 2) :
    (tensorExtension c δ).Δ' 0 (j + 1) = Iso.refl _ := rfl

@[simp]
lemma tensorExtension_c'_one :
    (tensorExtension c δ).c' 1 = c := rfl

@[simp]
lemma tensorExtension_c'_succ_succ (j : ℕ) (hj : j + 2 < n + 2) :
    (tensorExtension c δ).c' ⟨j + 2, hj⟩ = c ⊗ δ.c 0 ⟨j + 1, by valid⟩ :=
  rfl

end
namespace homMk'

variable {n : ℕ} {δ δ' : CoherentTensorFamily C (n + 1)}
    (f_fst : (fstArrow C n).obj δ ⟶ (fstArrow C n).obj δ')
    (f_δ₀ : (δ₀Functor C n).obj δ ⟶ (δ₀Functor C n).obj δ')

private abbrev CompProperty
    (φ : ∀ (i j : Fin (n + 2)) (hij : i ≤ j := by valid),
      δ.c i j hij ⟶ δ'.c i j hij)
    (i j k : Fin (n + 2)) (hij : i ≤ j := by valid)
      (hjk : j ≤ k := by valid) : Prop :=
  (δ.Δ i j k).hom ≫ φ i k =
  δ.c i j ◁ φ j k ≫ φ i j ▷ δ'.c j k ≫ (δ'.Δ i j k).hom

private lemma compProperty_four_out_of_three
    (φ : ∀ (i j : Fin (n + 2)) (hij : i ≤ j := by valid),
      δ.c i j hij ⟶ δ'.c i j hij)
    (i j k l : Fin (n + 2))
    (hij : i ≤ j := by valid) (hjk : j ≤ k := by valid)
    (hkl : k ≤ l := by valid)
    (nat_ijk : CompProperty @φ i j k)
    (nat_jkl : CompProperty @φ j k l)
    (nat_ijl : CompProperty @φ i j l) :
    CompProperty @φ i k l := by
  dsimp [CompProperty] at nat_ijk nat_jkl nat_ijl ⊢
  have e₃ := (δ.Δ i j k).inv ≫= nat_ijk
  have e₁ := (δ.Δ i j k).inv ▷ _ ≫= δ.Δ_comp i j k l
      -- Δ.mapCompOfLE_hom_whiskerRight_comp_mapCompOfLE_hom i j k l
      --   (by omega) (by omega) (by omega)
  have e₂ := (δ'.Δ i j k).inv ▷ _ ≫= δ'.Δ_comp i j k l
  simp only [inv_hom_whiskerRight_assoc, Iso.inv_hom_id_assoc] at e₁ e₂ e₃
  simp only [e₁, e₂, Category.assoc, nat_ijl, ← whiskerLeft_comp_assoc,
    nat_jkl, whisker_exchange_assoc]
  simp [e₃, whisker_exchange_assoc]

def φ : ∀ (i j : Fin (n + 2)) (hij : i ≤ j := by valid),
    δ.c i j hij ⟶ δ'.c i j hij
  | ⟨0, _⟩, ⟨0, _⟩, _ => (δ.η 0).hom ≫ (δ'.η 0).inv
  | ⟨0, _⟩, ⟨1, _⟩, _ => f_fst.φ 0 1
  | ⟨0, _⟩, ⟨(j + 2), hj⟩, h =>
      (δ.Δ 0 1 ⟨(j + 2), by valid⟩ (by simp) (by simp [← Fin.mk_one])).inv ≫
        δ.c 0 1 (by simp) ◁ (f_δ₀.φ 0 ⟨j + 1, (by valid)⟩ (by simp)) ≫
        (f_fst.φ 0 1) ▷ (δ'.c 1 ⟨(j + 2), hj⟩ (by simp [← Fin.mk_one])) ≫
          (δ'.Δ 0 1 ⟨(j + 2), hj⟩ (by simp) (by simp [← Fin.mk_one])).hom
  | ⟨(i + 1), _⟩, ⟨(j + 1), _⟩, hij => f_δ₀.φ ⟨i, by valid⟩ ⟨j, by valid⟩

private lemma φ_comp_succ_succ_succ (i j k : ℕ)
    (hi : i + 1 < n + 1 + 1 := by valid)
    (hj : j + 1 < n + 1 + 1 := by valid)
    (hk : k + 1 < n + 1 + 1 := by valid)
    (hij : i ≤ j) (hjk : j ≤ k) :
    CompProperty (@φ (f_fst := f_fst) (f_δ₀ := f_δ₀))
      ⟨(i + 1), by valid⟩ ⟨(j + 1), by valid⟩ ⟨(k + 1), by valid⟩
      (hij := by simpa using hij) (hjk := by simpa using hjk) := by
  simpa [φ] using f_δ₀.φ_comp ⟨i, by valid⟩ ⟨j, by valid⟩ ⟨k, by valid⟩

private lemma φ_comp_zero_one_succ_succ (k : ℕ)
    (hk : k + 2 < n + 1 + 1 := by valid) :
    CompProperty (@φ (f_fst := f_fst) (f_δ₀ := f_δ₀))
      0 1 ⟨(k + 2), by valid⟩
      (hij := by simp) (hjk := by simp [← Fin.mk_one]) := by
  simp only [← Fin.mk_one, ← Fin.zero_eta, CompProperty, φ]
  simp

end homMk'

open homMk' in
def homMk' {δ δ' : CoherentTensorFamily C (n + 1)}
    (f_fst : (fstArrow C n).obj δ ⟶ (fstArrow C n).obj δ')
    (f_δ₀ : (δ₀Functor C n).obj δ ⟶ (δ₀Functor C n).obj δ') :
    δ ⟶ δ' where
  φ i j hij := φ f_fst f_δ₀ i j hij
  φ_id := by
    rintro ⟨j, hj⟩
    cases j with
    | zero => simp [φ]
    | succ j => simp [φ]
  φ_comp := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hij hjk
    match i, j, k with
    | 0, 0, 0 => simpa [φ] using f_fst.φ_comp 0 0 0
    | 0, 0, i + 1 => simp [φ, whisker_exchange_assoc]
    | 0, i + 1, 0 => simp at hjk
    | 0, 1, 1 => simp [φ, whisker_exchange_assoc]
    | 0, 1, k + 2 => exact φ_comp_zero_one_succ_succ _ _ _
    | 0, j + 2, k + 2 =>
      exact compProperty_four_out_of_three (j := 1)
        (φ := @φ (f_fst := f_fst) (f_δ₀ := f_δ₀))
        _ _ _ _ _ _
        (φ_comp_zero_one_succ_succ _ _ _)
        (φ_comp_succ_succ_succ _ _ _ _ _
          (by valid) hj (by valid) (by valid) (by valid))
        (φ_comp_zero_one_succ_succ _ _ _)
    | i + 1, 0, 0 => simp at hij
    | i + 1, 0, k + 1 => simp at hij
    | i + 1, j + 1, 0 => simp at hjk
    | i + 1, j + 1, k + 1 =>
      simpa [φ] using f_δ₀.φ_comp ⟨i, by valid⟩ ⟨j, by valid⟩ ⟨k, by valid⟩

section

variable {δ δ' : CoherentTensorFamily C (n + 1)}
  (f_fst : (fstArrow C n).obj δ ⟶ (fstArrow C n).obj δ')
  (f_δ₀ : (δ₀Functor C n).obj δ ⟶ (δ₀Functor C n).obj δ')

@[simp]
lemma homMk'_φ_zero_one : (homMk' f_fst f_δ₀).φ 0 1 = f_fst.φ 0 1 := rfl

@[simp]
lemma homMk'_φ_zero_zero : (homMk' f_fst f_δ₀).φ 0 0 = (δ.η 0).hom ≫ (δ'.η 0).inv := rfl

@[simp]
lemma homMk'_φ_zero_succ_succ (j : ℕ) (hj : j + 2 < n + 1 + 1) :
    (homMk' f_fst f_δ₀).φ 0 ⟨j + 2, hj⟩ =
    (δ.Δ 0 1 ⟨(j + 2), by valid⟩ (by valid) (by simp [← Fin.mk_one])).inv ≫
      δ.c 0 1 (by simp) ◁ (f_δ₀.φ 0 ⟨j + 1, (by valid)⟩ (by simp)) ≫
      (f_fst.φ 0 1) ▷ (δ'.c 1 ⟨(j + 2), hj⟩ (by simp [← Fin.mk_one])) ≫
      (δ'.Δ 0 1 ⟨(j + 2), hj⟩ (by valid) (by simp [← Fin.mk_one])).hom :=
  rfl

@[simp]
lemma homMk'_φ_succ_succ (i j : ℕ) (hi : i + 1 < n + 2) (hj : j + 1 < n + 2)
    (hij : i + 1 ≤ j + 1) :
    (homMk' f_fst f_δ₀).φ ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ =
    f_δ₀.φ ⟨i, by valid⟩ ⟨j, by valid⟩ :=
  rfl

end

@[ext 1100, grind ext]
lemma hom_ext₁ {δ δ' : CoherentTensorFamily C 1} {f g : δ ⟶ δ'}
    (hf : f.φ 0 1 = g.φ 0 1) : f = g := by
  ext i j hij
  fin_cases i <;> fin_cases j
  · simp
  · exact hf
  · grind
  · simp

@[simp]
lemma fstArrow_map_homMk'
    {δ δ' : CoherentTensorFamily C (n + 1)}
    (f_fst : (fstArrow C n).obj δ ⟶ (fstArrow C n).obj δ')
    (f_δ₀ : (δ₀Functor C n).obj δ ⟶ (δ₀Functor C n).obj δ') :
    (fstArrow C _).map (homMk' f_fst f_δ₀) = f_fst := by
  cat_disch

@[simp]
lemma δ₀Functor_map_homMk'
    {δ δ' : CoherentTensorFamily C (n + 1)}
    (f_fst : (fstArrow C n).obj δ ⟶ (fstArrow C n).obj δ')
    (f_δ₀ : (δ₀Functor C n).obj δ ⟶ (δ₀Functor C n).obj δ') :
    (δ₀Functor C n).map (homMk' f_fst f_δ₀) = f_δ₀ :=
  rfl

lemma hom_ext_fst_δ₀ {δ δ' : CoherentTensorFamily C (n + 1)} {f g : δ ⟶ δ'}
    (h_fst : (fstArrow C n).map f = (fstArrow C n).map g)
    (h_δ₀ : (δ₀Functor C n).map f = (δ₀Functor C n).map g) :
    f = g := by
  apply hom_ext
  intro i j hij
  match i, j, hij with
  | ⟨0, _⟩, ⟨0, _⟩, _ => exact congr(($h_fst).φ 0 0)
  | ⟨0, _⟩, ⟨1, _⟩, _ => exact congr(($h_fst).φ 0 1)
  | ⟨0, _⟩, ⟨(j + 2), _⟩, _ =>
      have f_comp := (δ.Δ 0 1 ⟨j + 2, by valid⟩ _
          (by simp [← Fin.mk_one])).inv ≫=
        f.φ_comp 0 1 ⟨j + 2, by valid⟩ (by simp) (by simp [← Fin.mk_one])
      have g_comp := (δ.Δ 0 1 ⟨j + 2, by valid⟩ _
          (by simp [← Fin.mk_one])).inv ≫=
        g.φ_comp 0 1 ⟨j + 2, by valid⟩ (by simp) (by simp [← Fin.mk_one])
      rw [Iso.inv_hom_id_assoc] at f_comp g_comp
      simp only [Fin.zero_eta, f_comp, g_comp]
      have e₁ := congr(($h_fst).φ 0 1)
      have e₂ := congr(($h_δ₀).φ ⟨0, by valid⟩ ⟨j + 1, by valid⟩)
      dsimp [Fin.inclFunctor, Fin.castLE] at e₁ e₂
      simp [e₁, e₂]
  | ⟨(i + 1), _⟩, ⟨(j + 1), _⟩, _ => exact congr(($h_δ₀).φ ⟨i, by valid⟩ ⟨j, by valid⟩)

def homMk₁ {δ δ' : CoherentTensorFamily C 1} (f : δ.c 0 1 ⟶ δ'.c 0 1) :
    δ ⟶ δ' where
  φ
    |0, 0, _ => (δ.η 0).hom ≫ (δ'.η 0).inv
    |0, 1, _ => f
    |1, 0, _ => False.elim <| by grind
    |1, 1, _ => (δ.η 1).hom ≫ (δ'.η 1).inv
  φ_comp i j k hij hjk := by
    fin_cases i <;> fin_cases j <;> fin_cases k
    · simp only [Nat.reduceAdd, Fin.zero_eta, Fin.isValue,
        CoherentTensorFamily.Δ_id_right, Category.assoc, whiskerLeft_comp,
        comp_whiskerRight, ← whisker_exchange_assoc, id_whiskerLeft,
        whiskerRight_id, ← unitors_equal, Iso.inv_hom_id,
        Category.comp_id, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
      simp [whisker_exchange_assoc, unitors_equal]
    · simp [whisker_exchange_assoc]
    · grind
    · simp [whisker_exchange_assoc]
    · grind
    · grind
    · grind
    · simp only [Nat.reduceAdd, Fin.mk_one, Fin.isValue,
        CoherentTensorFamily.Δ_id_right, Category.assoc, whiskerLeft_comp,
        comp_whiskerRight, ← whisker_exchange_assoc, id_whiskerLeft,
        whiskerRight_id, ← unitors_equal, Iso.inv_hom_id,
        Category.comp_id, Iso.inv_hom_id_assoc, Iso.hom_inv_id]
      simp [whisker_exchange_assoc, unitors_equal]
  φ_id i := by fin_cases i <;> simp

@[simp, grind]
lemma homMk₁_φ_zero_one {δ δ' : CoherentTensorFamily C 1}
    (f : δ.c 0 1 ⟶ δ'.c 0 1) :
    (homMk₁ f).φ 0 1 = f :=
  rfl

variable (C) (n) in
/-- functorially "prepend" an element `c : C` to a `CoherentTensorFamily C n` to
get a `CoherentTensorFamily C (n + 1)`. -/
@[simps]
def prependBifunctor :
    C ⥤ CoherentTensorFamily C n ⥤ CoherentTensorFamily C (n + 1) where
  obj c :=
    { obj δ := tensorExtension c δ|>.family
      map f := homMk' (homMk₁ (𝟙 c)) f
      map_id x := by
        apply hom_ext_fst_δ₀
        · simp only [fstArrow_map_homMk', Functor.map_id]
          apply hom_ext₁
          rfl
        · simp only [δ₀Functor_map_homMk', Functor.map_id]
          rfl
      map_comp {x y z} f g := by
        apply hom_ext_fst_δ₀
        · simp only [fstArrow_map_homMk', Functor.map_comp]
          apply hom_ext₁
          dsimp [Fin.inclFunctor, Fin.castLE, tensorExtension, ← Fin.mk_one]
          simp
        · simp }
  map f :=
    { app δ := homMk' (homMk₁ f) (𝟙 _)
      naturality {δ δ'} f := by
        apply hom_ext_fst_δ₀
        · apply hom_ext₁
          dsimp [Fin.inclFunctor, Fin.castLE, tensorExtension, ← Fin.mk_one]
          simp
        · simp }
  map_id c := by
    ext : 2
    apply hom_ext_fst_δ₀
    · apply hom_ext₁
      dsimp [Fin.inclFunctor, Fin.castLE, tensorExtension, ← Fin.mk_one]
      simp
    · simp
  map_comp {c c' c''} f g := by
    ext : 2
    apply hom_ext_fst_δ₀
    · apply hom_ext₁
      dsimp [Fin.inclFunctor, Fin.castLE, tensorExtension, ← Fin.mk_one]
      simp
    · simp

def mk₁ (c : C) : CoherentTensorFamily C 1 :=
  tensorExtension c (unit C 0)|>.family

variable (C) in
@[simps]
def ev₀₁ : CoherentTensorFamily C 1 ⥤ C where
  obj δ := δ.c 0 1
  map f := f.φ 0 1

variable (C)

@[simps]
def mk₁Functor : C ⥤ CoherentTensorFamily C 1 where
  obj c := mk₁ c
  map f := homMk₁ f

@[simps]
def equiv₁ : C ≌ CoherentTensorFamily C 1 where
  functor := mk₁Functor C
  inverse := ev₀₁ C
  unitIso :=
    NatIso.ofComponents
      (fun _ ↦ .refl _)
  counitIso := NatIso.ofComponents
    (fun _ ↦
      { hom := homMk₁ (𝟙 _)
        inv := homMk₁ (𝟙 _) })

def splitEquiv (n : ℕ) : CoherentTensorFamily C (n + 1) ≌ C × CoherentTensorFamily C n where
  functor := (fstArrow C n ⋙ ev₀₁ C).prod' (δ₀Functor C n)
  inverse := Functor.uncurry.obj (prependBifunctor C n)
  unitIso := NatIso.ofComponents
    (fun _ ↦
      { hom := homMk' (homMk₁ (𝟙 _)) (𝟙 _)
        inv := homMk' (homMk₁ (𝟙 _)) (𝟙 _)
        hom_inv_id := by
          apply hom_ext_fst_δ₀
          · apply hom_ext₁
            dsimp [Fin.inclFunctor, Fin.castLE, tensorExtension, ← Fin.mk_one]
            simp
          · simp
        inv_hom_id := by
          apply hom_ext_fst_δ₀
          · apply hom_ext₁
            dsimp [Fin.inclFunctor, Fin.castLE, tensorExtension, ← Fin.mk_one]
            simp
          · simp })

    (fun {x y} f ↦ by
      apply hom_ext_fst_δ₀
      · apply hom_ext₁
        dsimp [Fin.inclFunctor, Fin.castLE, tensorExtension, ← Fin.mk_one]
        simp
      · simp)
  counitIso :=
    NatIso.ofComponents
      (fun _ ↦ .refl _)
      (fun {x y} f ↦ by
        simp only [Functor.comp_obj, Functor.uncurry_obj_obj,
          prependBifunctor_obj_obj, Functor.prod'_obj, ev₀₁_obj, Fin.isValue,
          fstArrow_obj_c, Nat.reduceAdd, Functor.id_obj, prod_Hom,
          Functor.comp_map, Functor.uncurry_obj_map, prependBifunctor_map_app,
          prependBifunctor_obj_map, Functor.prod'_map, Functor.map_comp,
          fstArrow_map_homMk', ev₀₁_map, comp_φ, homMk₁_φ_zero_one,
          δ₀Functor_map_homMk', Category.id_comp, Iso.refl_hom, prod_id,
          prod_comp, Category.comp_id, Functor.id_map, Prod.mk.eta]
        ext : 1
        · simp [Fin.inclFunctor, Fin.castLE, tensorExtension, ← Fin.mk_one]
        · rfl)

def zeroEquiv : CoherentTensorFamily C 0 ≌ (Fin 0 → C) where
  functor :=
    { obj x := fun _ ↦ 𝟙_ C
      map f := fun _ ↦ 𝟙 _ }
  inverse :=
    { obj _ := unit C 0
      map _ := 𝟙 _ }
  unitIso :=
    NatIso.ofComponents (fun x ↦
      { hom :=
          { φ | 0, 0, _ => (x.η 0).hom
            φ_comp | 0, 0, 0, _, _ => by simp [unitors_equal]
            φ_id | 0 => by simp }
        inv :=
          { φ | 0, 0, _ => (x.η 0).inv
            φ_comp
            | 0, 0, 0, _, _ => by
              simpa [← whisker_exchange_assoc] using unitors_equal
            φ_id | 0 => by simp }} )
  counitIso :=
    NatIso.ofComponents
      (fun x ↦
        { hom := fun j ↦ j.elim0
          inv := fun j ↦ j.elim0
          hom_inv_id := by
            ext j
            exact j.elim0
          inv_hom_id := by
            ext j
            exact j.elim0 })
      (fun {x y} f ↦ by
        ext j
        exact j.elim0 )
  functor_unitIso_comp δ := by
    ext j
    exact j.elim0

/-- Fin.cons as an equivalence of categories -/
def consEquiv : C × (Fin n → C) ≌ Fin (n + 1) → C where
  functor :=
    { obj x := Fin.cons x.1 x.2
      map f := Fin.cons f.1 f.2
      map_id x := by
        ext i
        induction i using Fin.induction <;> rfl
      map_comp {x y z} f g := by
        ext i
        induction i using Fin.induction <;> rfl }
  inverse :=
    { obj x := ⟨x 0, fun i ↦ x i.succ⟩
      map f := ⟨f 0, fun i ↦ f i.succ⟩
      map_id x := rfl
      map_comp {x y z} f g := rfl }
  unitIso := NatIso.ofComponents (fun x ↦ Iso.refl _)
  counitIso := NatIso.ofComponents
    (fun x ↦
      { hom := fun i ↦ Fin.cases (𝟙 _) (fun _ ↦ 𝟙 _) i
        inv := fun i ↦ Fin.cases (𝟙 _) (fun _ ↦ 𝟙 _) i
        hom_inv_id := by
          ext i
          cases i using Fin.cases <;> simp
        inv_hom_id := by
          ext i
          cases i using Fin.cases <;> simp })
    (fun {x y} f ↦ by
        ext i
        cases i using Fin.cases <;> simp)
  functor_unitIso_comp x := by
    ext i
    cases i using Fin.cases
    · simp only [prod_Hom, Functor.id_obj, Functor.comp_obj,
        NatIso.ofComponents_hom_app, Iso.refl_hom, prod_id_fst, prod_id_snd,
        Pi.comp_apply, Fin.cons_zero, Fin.cases_zero, Category.comp_id,
        Pi.id_apply]
      rfl
    · simp only [prod_Hom, Functor.id_obj, Functor.comp_obj,
        NatIso.ofComponents_hom_app, Iso.refl_hom, prod_id_fst, prod_id_snd,
        Pi.comp_apply, Fin.cons_succ, Pi.id_apply, Fin.cases_succ,
        Category.comp_id]
      rfl

/-- An first inductively defined equivalence, we will give a one with better defeq below, once
we identify the functor of this equivalence with evalAsTuple. -/
def tupleEquiv : ∀ n : ℕ, CoherentTensorFamily C n ≌ (Fin n → C)
  | 0 => zeroEquiv C
  | j + 1 => (splitEquiv C j).trans <|
      ((Equivalence.refl (C := C)).prod (tupleEquiv j)).trans (consEquiv C)

variable (n) in
@[simps]
def evalAsTuple : (CoherentTensorFamily C n) ⥤ (Fin n → C) where
  obj δ := fun i ↦ δ.c i.castSucc i.succ (by simp [Fin.le_def])
  map f := fun i ↦ f.φ i.castSucc i.succ (by simp [Fin.le_def])

def tupleEquivFunctorIso : ∀ n : ℕ, (tupleEquiv C n).functor ≅ evalAsTuple C n
  | 0 => NatIso.ofComponents
    (fun _ ↦
      { hom := fun j ↦ j.elim0
        inv := fun j ↦ j.elim0
        hom_inv_id := by ext j; exact j.elim0
        inv_hom_id := by ext j; exact j.elim0 })
    (fun {x y} f ↦ by ext j; exact j.elim0)
  | n + 1 =>
    NatIso.ofComponents (fun x ↦
      { hom := fun i ↦ Fin.cases (𝟙 _) (fun j ↦
          ((tupleEquivFunctorIso n).hom.app ((δ₀Functor C n).obj x) j)) i
        inv := fun i ↦ Fin.cases (𝟙 _) (fun j ↦
          ((tupleEquivFunctorIso n).inv.app ((δ₀Functor C n).obj x) j)) i
        hom_inv_id := by
          ext i
          cases i using Fin.cases with
          | zero => simp
          | succ i =>
            haveI := congr_arg (fun t ↦ t i) <|
              (tupleEquivFunctorIso n).hom_inv_id_app ((δ₀Functor C n).obj x)
            dsimp at this
            simp only [evalAsTuple_obj, Fin.castSucc_zero, Fin.succ_zero_eq_one,
              Pi.comp_apply, Fin.castSucc_succ, Fin.cases_succ, this, Pi.id_apply]
            rfl
        inv_hom_id := by
          ext i
          cases i using Fin.cases with
          | zero => simp
          | succ i =>
            haveI := congr_arg (fun t ↦ t i) <|
              (tupleEquivFunctorIso n).inv_hom_id_app ((δ₀Functor C n).obj x)
            dsimp at this
            simp only [evalAsTuple_obj, Fin.castSucc_succ, Fin.castSucc_zero,
              Fin.succ_zero_eq_one, Pi.comp_apply, Fin.cases_succ, this,
              Pi.id_apply] })
      (fun {x y} f ↦ by
        ext i
        cases i using Fin.cases with
        | zero =>
          simp only [evalAsTuple_obj, Fin.castSucc_zero,
            Fin.succ_zero_eq_one, Pi.comp_apply, Fin.cases_zero, Category.comp_id,
            evalAsTuple_map, Category.id_comp]
          rfl
        | succ i =>
          simp only [evalAsTuple_obj, Fin.castSucc_succ, Pi.comp_apply,
            Fin.cases_succ, evalAsTuple_map]
          haveI := congr_arg (fun t ↦ t i) <|
            (tupleEquivFunctorIso n).hom.naturality ((δ₀Functor C n).map f)
          dsimp at this
          simp [tupleEquiv, consEquiv, splitEquiv, this])

def tupleEquiv' (n : ℕ) : CoherentTensorFamily C n ≌ (Fin n → C) :=
  (tupleEquiv C n).changeFunctor (tupleEquivFunctorIso C n)

-- Now time for the ultimate sanity check: that through all the identitfications, one
-- finds back the tensor product for small values

def tensorProdFunctor : ∀ (n : ℕ), (Fin (n + 1) → C) ⥤ C
  | 0 =>
    { obj x := x 0
      map f := f 0 }
  | n + 1 =>
    { obj x := x 0 ⊗ (tensorProdFunctor n).obj (fun i ↦ x i.succ)
      map f := f 0 ⊗ₘ (tensorProdFunctor n).map (fun i ↦ f i.succ)
      map_id X := by
        change (𝟙 _) ⊗ₘ ((tensorProdFunctor n).map (𝟙 _)) = _
        simp
      map_comp {x y z} f g := by
        change (_ ≫ _) ⊗ₘ ((tensorProdFunctor n).map (_ ≫ _)) = _
        simp }

variable (n) in
@[simps!]
def homFunctor : CoherentTensorFamily C (n + 1) ⥤ C where
  obj x := x.hom
  map f := f.φ 0 ⟨n + 1, by valid⟩

def tupleEquivFunctorHomFunctor : ∀ (n : ℕ),
    (tupleEquiv C (n + 1)).inverse ⋙ homFunctor C n ≅ tensorProdFunctor C n
  | 0 => NatIso.ofComponents (fun _ ↦ .refl _)
      (fun {x y} f ↦ by simp
        [tupleEquiv, splitEquiv, consEquiv, homMk', homMk₁, homMk'.φ,
          tensorExtension, extension.family, extension.c, extension.Δ,
          Fin.inclFunctor, tensorProdFunctor])
  | m + 1 =>
    NatIso.ofComponents
      (fun x ↦
        whiskerLeftIso (x 0) ((tupleEquivFunctorHomFunctor m).app (fun i ↦ x i.succ)))
      (fun {x y} f ↦ by
        have := congr_arg (fun t ↦ y 0 ◁ t) <|
          (tupleEquivFunctorHomFunctor m).hom.naturality (fun i ↦ f i.succ)
        dsimp [tupleEquiv] at this ⊢
        dsimp only [splitEquiv, Functor.uncurry_obj_map, prependBifunctor] at this ⊢
        dsimp [consEquiv] at this ⊢
        simp only [Category.assoc, whiskerLeft_comp] at this
        simp only [whiskerLeft_id, Fin.inclFunctor, Fin.isValue,
          Monotone.functor_obj, OrderEmbedding.toOrderHom_coe,
          Fin.castLEOrderEmb_apply, Fin.castLE, Fin.coe_ofNat_eq_mod,
          Nat.zero_mod, Fin.zero_eta, Nat.reduceMod, Fin.mk_one,
          extension.family_c_zero, tensorExtension_c'_one, Category.comp_id,
          Category.id_comp, whiskerLeft_comp, id_whiskerRight, Category.assoc]
        simp [this, ← whisker_exchange_assoc, ← whisker_exchange,
          tensorProdFunctor, tensorHom_def, ← whisker_exchange])

end CoherentTensorFamily

end CategoryTheory.MonoidalCategory
