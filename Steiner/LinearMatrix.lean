module

public import Steiner.Homogeneous
public import Mathlib.LinearAlgebra.Matrix.Rank

@[expose] public section

/-!
# Multiplication by a matrix of linear forms

The source and target are actual homogeneous polynomial spaces. This module
proves the elementary rank and degree-propagation facts; it makes no assertion
that a general matrix has maximal rank.
-/

noncomputable section

namespace Steiner

open MvPolynomial Module

variable (K : Type*) [Field K] (n : ℕ)

/-- A genuine `a × c` matrix of linear forms in `n + 1` variables. -/
abbrev LinearMatrix (a c : ℕ) := Matrix (Fin a) (Fin c) (Forms K (n + 1) 1)

/-- The source of the induced map in twist `t`. -/
abbrev MatrixSource (c t : ℕ) := Fin c → Forms K (n + 1) t

/-- The target of the induced map in twist `t`. -/
abbrev MatrixTarget (a t : ℕ) := Fin a → Forms K (n + 1) (t + 1)

variable {K n} {a c t : ℕ}

/-- Multiplication by one linear form, with degrees written in successor form. -/
def multiplyLinear (q : Forms K (n + 1) 1) (f : Forms K (n + 1) t) : Forms K (n + 1) (t + 1) :=
  ⟨q.val * f.val, by
    change (q.val * f.val).IsHomogeneous (t + 1)
    simpa only [Nat.add_comm] using q.property.mul f.property⟩

@[simp] theorem multiplyLinear_val (q : Forms K (n + 1) 1) (f : Forms K (n + 1) t) :
    (multiplyLinear q f).val = q.val * f.val := rfl

/-- Entrywise multiplication of a homogeneous vector by one linear form. -/
def multiplyVector {b : ℕ} (q : Forms K (n + 1) 1) (v : Fin b → Forms K (n + 1) t) :
    Fin b → Forms K (n + 1) (t + 1) := fun i => multiplyLinear q (v i)

/-- The degree-`t` polynomial multiplication map defined by the matrix. -/
def linearMatrixMap (L : LinearMatrix K n a c) (t : ℕ) :
    MatrixSource K n c t →ₗ[K] MatrixTarget K n a t where
  toFun v i := ⟨∑ j, (L i j).val * (v j).val, by
    apply IsHomogeneous.sum
    intro j _
    simpa only [Nat.add_comm] using (L i j).property.mul (v j).property⟩
  map_add' v w := by
    funext i
    apply Subtype.ext
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' k v := by
    funext i
    apply Subtype.ext
    simp [Finset.smul_sum]

@[simp] theorem linearMatrixMap_val (L : LinearMatrix K n a c) (t : ℕ)
    (v : MatrixSource K n c t) (i : Fin a) :
    (linearMatrixMap L t v i).val = ∑ j, (L i j).val * (v j).val := rfl

/-- Source dimension of the degree-`t` matrix map. -/
theorem finrank_matrixSource (K : Type*) [Field K] (n c t : ℕ) :
    finrank K (MatrixSource K n c t) = c * (n + t).choose t := by
  simp [MatrixSource, Module.finrank_pi_fintype, finrank_forms,
    show n + 1 + t - 1 = n + t by omega]

/-- Target dimension of the degree-`t` matrix map. -/
theorem finrank_matrixTarget (K : Type*) [Field K] (n a t : ℕ) :
    finrank K (MatrixTarget K n a t) = a * (n + (t + 1)).choose (t + 1) := by
  simp [MatrixTarget, Module.finrank_pi_fintype, finrank_forms,
    show n + 1 + (t + 1) - 1 = n + (t + 1) by omega]

/-- Maximal rank has its literal finite-dimensional meaning. -/
def LinearMatrixMaximalRank (L : LinearMatrix K n a c) (t : ℕ) : Prop :=
  finrank K (linearMatrixMap L t).range =
    min (finrank K (MatrixSource K n c t)) (finrank K (MatrixTarget K n a t))

/-- The cokernel is the actual quotient by the image. -/
abbrev LinearMatrixCokernel (L : LinearMatrix K n a c) (t : ℕ) :=
  MatrixTarget K n a t ⧸ (linearMatrixMap L t).range

/-- Polynomial multiplication commutes with the matrix map. -/
theorem linearMatrixMap_multiplyVector (L : LinearMatrix K n a c)
    (q : Forms K (n + 1) 1) (v : MatrixSource K n c t) :
    linearMatrixMap L (t + 1) (multiplyVector q v) =
      multiplyVector q (linearMatrixMap L t v) := by
  funext i
  apply Subtype.ext
  simp [linearMatrixMap, multiplyVector, multiplyLinear, Finset.mul_sum,
    mul_left_comm]

/-- A nonzero linear form multiplies homogeneous vectors injectively. -/
theorem multiplyVector_injective {b : ℕ} (q : Forms K (n + 1) 1) (hq : q.val ≠ 0) :
    Function.Injective (multiplyVector (b := b) (t := t) q) := by
  intro v w h
  funext i
  apply Subtype.ext
  exact mul_left_cancel₀ hq (congrArg Subtype.val (congrFun h i))

/-- Injectivity in one twist implies injectivity in the preceding twist. -/
theorem linearMatrixMap_injective_of_succ (L : LinearMatrix K n a c)
    (h : Function.Injective (linearMatrixMap L (t + 1))) :
    Function.Injective (linearMatrixMap L t) := by
  let q : Forms K (n + 1) 1 := ⟨X 0, isHomogeneous_X K 0⟩
  have hq : q.val ≠ 0 := X_ne_zero 0
  intro v w hvw
  apply multiplyVector_injective q hq
  apply h
  rw [linearMatrixMap_multiplyVector, linearMatrixMap_multiplyVector, hvw]

/-- Injectivity propagates to all lower twists. -/
theorem linearMatrixMap_injective_downward (L : LinearMatrix K n a c)
    {s t : ℕ} (hst : s ≤ t) (h : Function.Injective (linearMatrixMap L t)) :
    Function.Injective (linearMatrixMap L s) := by
  induction t generalizing s with
  | zero =>
    have hs : s = 0 := by omega
    subst s
    exact h
  | succ t ih =>
    by_cases hs : s = t + 1
    · subst s
      exact h
    · apply ih (by omega : s ≤ t)
      exact linearMatrixMap_injective_of_succ L h

/-- Surjectivity in one twist implies surjectivity in the next twist. -/
theorem linearMatrixMap_surjective_succ (L : LinearMatrix K n a c)
    (h : Function.Surjective (linearMatrixMap L t)) :
    Function.Surjective (linearMatrixMap L (t + 1)) := by
  classical
  have hsingle (i : Fin a) (p : Poly K (n + 1)) (hp : p ∈ Forms K (n + 1) (t + 1 + 1)) :
      Pi.single i (⟨p, hp⟩ : Forms K (n + 1) (t + 1 + 1)) ∈
        (linearMatrixMap L (t + 1)).range := by
    have heq : Forms K (n + 1) 1 * Forms K (n + 1) (t + 1) = Forms K (n + 1) (t + 1 + 1) := by
      simpa only [Nat.add_comm] using
        (forms_mul_forms (K := K) (n := n + 1) (d := 1) (e := t + 1))
    have hprod : p ∈ Forms K (n + 1) 1 * Forms K (n + 1) (t + 1) := by rw [heq]; exact hp
    have hresult : ∀ q : Poly K (n + 1), q ∈ Forms K (n + 1) 1 * Forms K (n + 1) (t + 1) →
        ∀ hq : q ∈ Forms K (n + 1) (t + 1 + 1),
          Pi.single i (⟨q, hq⟩ : Forms K (n + 1) (t + 1 + 1)) ∈
            (linearMatrixMap L (t + 1)).range := by
      intro q hq
      refine Submodule.mul_induction_on'
        (M := Forms K (n + 1) 1) (N := Forms K (n + 1) (t + 1))
        (C := fun q _ => ∀ hq : q ∈ Forms K (n + 1) (t + 1 + 1),
          Pi.single i (⟨q, hq⟩ : Forms K (n + 1) (t + 1 + 1)) ∈
            (linearMatrixMap L (t + 1)).range) ?_ ?_ hq
      · intro f hf g hg hfg
        obtain ⟨v, hv⟩ := h (Pi.single i (⟨g, hg⟩ : Forms K (n + 1) (t + 1)))
        refine ⟨multiplyVector (⟨f, hf⟩ : Forms K (n + 1) 1) v, ?_⟩
        rw [linearMatrixMap_multiplyVector, hv]
        funext j
        apply Subtype.ext
        by_cases hji : j = i
        · subst j
          simp [multiplyVector, multiplyLinear]
        · simp [multiplyVector, multiplyLinear, hji]
      · intro q hq r hr hq_ih hr_ih hqr
        have hq' : q ∈ Forms K (n + 1) (t + 1 + 1) := by rw [← heq]; exact hq
        have hr' : r ∈ Forms K (n + 1) (t + 1 + 1) := by rw [← heq]; exact hr
        obtain ⟨v, hv⟩ := hq_ih hq'
        obtain ⟨w, hw⟩ := hr_ih hr'
        refine ⟨v + w, ?_⟩
        rw [map_add, hv, hw]
        funext j
        apply Subtype.ext
        by_cases hji : j = i
        · subst j
          simp
        · simp [hji]
    exact hresult p hprod hp
  intro y
  have hy : y ∈ (linearMatrixMap L (t + 1)).range := by
    have hsum := (linearMatrixMap L (t + 1)).range.sum_mem
      (t := Finset.univ) (f := fun i => Pi.single i (y i))
      (fun i _ => hsingle i (y i).val (y i).property)
    have heq : (∑ i : Fin a, Pi.single i (y i)) = y := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    rwa [heq] at hsum
  exact hy

/-- Surjectivity propagates to all higher twists. -/
theorem linearMatrixMap_surjective_upward (L : LinearMatrix K n a c)
    {s t : ℕ} (hst : s ≤ t) (h : Function.Surjective (linearMatrixMap L s)) :
    Function.Surjective (linearMatrixMap L t) := by
  induction t, hst using Nat.le_induction with
  | base => exact h
  | succ t hst ih => exact linearMatrixMap_surjective_succ L ih

/-- An injective matrix map has maximal rank. -/
theorem linearMatrixMaximalRank_of_injective (L : LinearMatrix K n a c) (t : ℕ)
    (h : Function.Injective (linearMatrixMap L t)) : LinearMatrixMaximalRank L t := by
  have hr := LinearMap.finrank_range_of_inj h
  have hle := Submodule.finrank_le (linearMatrixMap L t).range
  rw [hr] at hle
  exact hr.trans (min_eq_left hle).symm

/-- A surjective matrix map has maximal rank. -/
theorem linearMatrixMaximalRank_of_surjective (L : LinearMatrix K n a c) (t : ℕ)
    (h : Function.Surjective (linearMatrixMap L t)) : LinearMatrixMaximalRank L t := by
  have hr : (linearMatrixMap L t).range = ⊤ := LinearMap.range_eq_top.mpr h
  have hdim := LinearMap.finrank_range_le (linearMatrixMap L t)
  rw [hr, finrank_top] at hdim
  dsimp [LinearMatrixMaximalRank]
  rw [hr, finrank_top, min_eq_right hdim]

/-- When the source is smaller, maximal rank is equivalent to injectivity. -/
theorem linearMatrixMaximalRank_iff_injective (L : LinearMatrix K n a c) (t : ℕ)
    (hsize : finrank K (MatrixSource K n c t) ≤ finrank K (MatrixTarget K n a t)) :
    LinearMatrixMaximalRank L t ↔ Function.Injective (linearMatrixMap L t) := by
  constructor
  · intro h
    dsimp [LinearMatrixMaximalRank] at h
    rw [min_eq_left hsize] at h
    have hk := LinearMap.finrank_range_add_finrank_ker (linearMatrixMap L t)
    apply LinearMap.ker_eq_bot.mp
    apply Submodule.finrank_eq_zero.mp
    omega
  · exact linearMatrixMaximalRank_of_injective L t

/-- When the target is smaller, maximal rank is equivalent to surjectivity. -/
theorem linearMatrixMaximalRank_iff_surjective (L : LinearMatrix K n a c) (t : ℕ)
    (hsize : finrank K (MatrixTarget K n a t) ≤ finrank K (MatrixSource K n c t)) :
    LinearMatrixMaximalRank L t ↔ Function.Surjective (linearMatrixMap L t) := by
  constructor
  · intro h
    dsimp [LinearMatrixMaximalRank] at h
    rw [min_eq_right hsize] at h
    apply LinearMap.range_eq_top.mp
    exact Submodule.eq_top_of_finrank_eq h
  · exact linearMatrixMaximalRank_of_surjective L t

/-- Maximal rank means injectivity or surjectivity. -/
theorem linearMatrixMaximalRank_iff (L : LinearMatrix K n a c) (t : ℕ) :
    LinearMatrixMaximalRank L t ↔
      Function.Injective (linearMatrixMap L t) ∨
        Function.Surjective (linearMatrixMap L t) := by
  constructor
  · intro h
    by_cases hs : finrank K (MatrixSource K n c t) ≤ finrank K (MatrixTarget K n a t)
    · exact Or.inl ((linearMatrixMaximalRank_iff_injective L t hs).mp h)
    · exact Or.inr ((linearMatrixMaximalRank_iff_surjective L t (by omega)).mp h)
  · rintro (h | h)
    · exact linearMatrixMaximalRank_of_injective L t h
    · exact linearMatrixMaximalRank_of_surjective L t h

/-- Maximal rank gives the expected nonnegative cokernel dimension. -/
theorem finrank_linearMatrixCokernel (L : LinearMatrix K n a c) (t : ℕ)
    (h : LinearMatrixMaximalRank L t) :
    finrank K (LinearMatrixCokernel L t) =
      a * (n + (t + 1)).choose (t + 1) - c * (n + t).choose t := by
  have hquot := (linearMatrixMap L t).range.finrank_quotient_add_finrank
  dsimp [LinearMatrixMaximalRank] at h
  rw [h, finrank_matrixSource, finrank_matrixTarget] at hquot
  dsimp [LinearMatrixCokernel]
  omega

/-- Two consecutive injectivity and surjectivity checks cover every twist. -/
theorem linearMatrixMaximalRank_all_of_two_checks (L : LinearMatrix K n a c)
    (t₀ : ℕ) (hinj : Function.Injective (linearMatrixMap L t₀))
    (hsurj : Function.Surjective (linearMatrixMap L (t₀ + 1))) :
    ∀ t, LinearMatrixMaximalRank L t := by
  intro t
  by_cases ht : t ≤ t₀
  · exact linearMatrixMaximalRank_of_injective L t
      (linearMatrixMap_injective_downward L ht hinj)
  · exact linearMatrixMaximalRank_of_surjective L t
      (linearMatrixMap_surjective_upward L (by omega) hsurj)

/-- The two-check statement expressed using maximal ranks at the crossing. -/
theorem linearMatrixMaximalRank_all_of_critical_checks (L : LinearMatrix K n a c)
    (t₀ : ℕ)
    (hsmall : finrank K (MatrixSource K n c t₀) ≤ finrank K (MatrixTarget K n a t₀))
    (hlarge : finrank K (MatrixTarget K n a (t₀ + 1)) ≤
      finrank K (MatrixSource K n c (t₀ + 1)))
    (hleft : LinearMatrixMaximalRank L t₀)
    (hright : LinearMatrixMaximalRank L (t₀ + 1)) :
    ∀ t, LinearMatrixMaximalRank L t :=
  linearMatrixMaximalRank_all_of_two_checks L t₀
    ((linearMatrixMaximalRank_iff_injective L t₀ hsmall).mp hleft)
    ((linearMatrixMaximalRank_iff_surjective L (t₀ + 1) hlarge).mp hright)

/-- A single bijective twist suffices for maximal rank in every twist. -/
theorem linearMatrixMaximalRank_all_of_bijective (L : LinearMatrix K n a c)
    (t₀ : ℕ) (h : Function.Bijective (linearMatrixMap L t₀)) :
    ∀ t, LinearMatrixMaximalRank L t := by
  intro t
  by_cases ht : t ≤ t₀
  · exact linearMatrixMaximalRank_of_injective L t
      (linearMatrixMap_injective_downward L ht h.1)
  · exact linearMatrixMaximalRank_of_surjective L t
      (linearMatrixMap_surjective_upward L (by omega) h.2)

end Steiner
