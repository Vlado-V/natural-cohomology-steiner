module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Dual.Lemmas

set_option backward.privateInPublic true
@[expose] public section

/-! # Natural cohomology from genuine short exact sequences
The hypotheses concern actual abelian sheaves, the cohomology of their two
known terms, and the induced cohomology map. No cohomological conclusion for
the unknown kernel or cokernel is assumed.
-/

noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Abelian
universe u v w w'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}]
  [HasExt.{w'} (Sheaf J AddCommGrpCat.{w})]

/-- Nonzero cohomology is confined to at most one degree. -/
def HasNaturalCohomology (F : Sheaf J AddCommGrpCat.{w}) : Prop :=
  ∃ d : ℕ, ∀ q : ℕ, q ≠ d → Subsingleton (Sheaf.H F q)

/-- Equivalent to the usual rank condition in finite-dimensional linear algebra. -/
def HasMaximalRank {A B : Type*} (f : A → B) : Prop :=
  Function.Injective f ∨ Function.Surjective f

/-- The functional maximal-rank criterion is precisely rank equal to the
minimum dimension for finite-dimensional vector spaces. -/
theorem hasMaximalRank_iff_finrank_range_eq_min
    {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K U] [FiniteDimensional K V]
    (f : U →ₗ[K] V) :
    HasMaximalRank f ↔ Module.finrank K f.range =
      min (Module.finrank K U) (Module.finrank K V) := by
  constructor
  · rintro (hinj | hsurj)
    · rw [LinearMap.finrank_range_of_inj hinj,
        min_eq_left (LinearMap.finrank_le_finrank_of_injective hinj)]
    · rw [LinearMap.range_eq_top.mpr hsurj, finrank_top,
        min_eq_right (LinearMap.finrank_le_finrank_of_surjective hsurj)]
  · intro hrank
    rcases le_total (Module.finrank K U) (Module.finrank K V) with hle | hle
    · left
      rw [min_eq_left hle] at hrank
      have hnull := f.finrank_range_add_finrank_ker
      have hker : Module.finrank K f.ker = 0 := by omega
      exact LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hker)
    · right
      rw [min_eq_right hle] at hrank
      exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hrank)

/-- Taking the algebraic dual exchanges injectivity and surjectivity,
hence preserves maximal rank over every field. -/
theorem hasMaximalRank_dualMap_iff
    {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
    [AddCommGroup V] [Module K V] (f : U →ₗ[K] V) :
    HasMaximalRank f.dualMap ↔ HasMaximalRank f := by
  simp only [HasMaximalRank, LinearMap.dualMap_injective_iff,
    LinearMap.dualMap_surjective_iff, or_comm]

/-- Maximal rank is invariant under genuine identifications of the source
and target spaces. -/
theorem hasMaximalRank_congr {A B A' B' : Type*}
    (eA : A ≃ A') (eB : B ≃ B') (f : A → B) (g : A' → B')
    (h : ∀ a, eB (f a) = g (eA a)) :
    HasMaximalRank f ↔ HasMaximalRank g := by
  have hinj : Function.Injective f ↔ Function.Injective g := by
    constructor
    · intro hf x y hxy
      obtain ⟨a, rfl⟩ := eA.surjective x
      obtain ⟨b, rfl⟩ := eA.surjective y
      exact congrArg eA (hf (eB.injective (by rw [h a, h b]; exact hxy)))
    · intro hg a b hab
      exact eA.injective (hg (by rw [← h a, ← h b, hab]))
  have hsurj : Function.Surjective f ↔ Function.Surjective g := by
    constructor
    · intro hf y
      obtain ⟨a, ha⟩ := hf (eB.symm y)
      exact ⟨eA a, by rw [← h a, ha, eB.apply_symm_apply]⟩
    · intro hg y
      obtain ⟨a, ha⟩ := hg (eB y)
      refine ⟨eA.symm a, eB.injective ?_⟩
      rw [h, eA.apply_symm_apply, ha]
  exact or_congr hinj hsurj

variable {S : ShortComplex (Sheaf J AddCommGrpCat.{w})} (hS : S.ShortExact)
include hS

private lemma boundary_map_zero (q : ℕ) (x : Sheaf.H S.X₃ q) :
    Sheaf.H.map S.f (q+1) (Sheaf.H.δ hS q (q+1) rfl x) = 0 := by
  change (x.comp hS.extClass rfl).comp (Ext.mk₀ S.f) (add_zero (q+1)) = 0
  simp only [Ext.comp_assoc_of_third_deg_zero,
    ShortComplex.ShortExact.extClass_comp, Ext.comp_zero]

private lemma map_boundary_zero (q : ℕ) (x : Sheaf.H S.X₂ q) :
    Sheaf.H.δ hS q (q+1) rfl (Sheaf.H.map S.g q x) = 0 := by
  change (x.comp (Ext.mk₀ S.g) (add_zero q)).comp hS.extClass rfl = 0
  simp only [Ext.comp_assoc_of_second_deg_zero,
    ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

/-- Vanishing at either side of a left-hand term in the long exact sequence. -/
theorem kernel_cohomology_succ_vanishes (q : ℕ)
    (hC : Subsingleton (Sheaf.H S.X₃ q))
    (hB : Subsingleton (Sheaf.H S.X₂ (q+1))) :
    Subsingleton (Sheaf.H S.X₁ (q+1)) := by
  let :=  hC
  let :=  hB
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₁ hS x (Subsingleton.elim _ _) rfl
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

/-- Vanishing at either side of a right-hand term in the long exact sequence. -/
theorem cokernel_cohomology_vanishes (q : ℕ)
    (hB : Subsingleton (Sheaf.H S.X₂ q))
    (hA : Subsingleton (Sheaf.H S.X₁ (q+1))) :
    Subsingleton (Sheaf.H S.X₃ q) := by
  let :=  hB
  let :=  hA
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₃ hS x rfl (Subsingleton.elim _ _)
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

/-- A cokernel of two sheaves with vanishing positive cohomology has cohomology
only in degree zero. This applies to nonnegative twists of a Steiner presentation. -/
theorem cokernel_natural_of_positive_vanishing
    (hA : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H S.X₁ q))
    (hB : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H S.X₂ q)) :
    HasNaturalCohomology S.X₃ := by
  refine ⟨0, fun q hq => cokernel_cohomology_vanishes hS q (hB q ?_) (hA (q+1) ?_)⟩
  · exact Nat.pos_of_ne_zero hq
  · exact Nat.zero_lt_succ q

/-- Injectivity of the next cohomology map kills cokernel cohomology. -/
theorem cokernel_cohomology_vanishes_of_next_injective (q : ℕ)
    (hB : Subsingleton (Sheaf.H S.X₂ q))
    (hinj : Function.Injective (Sheaf.H.map S.f (q+1))) :
    Subsingleton (Sheaf.H S.X₃ q) := by
  let :=  hB
  refine subsingleton_of_forall_eq 0 fun x => ?_
  have hx : Sheaf.H.δ hS q (q+1) rfl x = 0 :=
    hinj (by simpa using boundary_map_zero hS q x)
  obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₃ hS x rfl hx
  rw [Subsingleton.elim y 0, map_zero] at hy
  exact hy.symm

/-- Surjectivity kills cokernel cohomology if the next left group vanishes. -/
theorem cokernel_cohomology_vanishes_of_surjective (q : ℕ)
    (hsurj : Function.Surjective (Sheaf.H.map S.f q))
    (hA : Subsingleton (Sheaf.H S.X₁ (q+1))) :
    Subsingleton (Sheaf.H S.X₃ q) := by
  let :=  hA
  refine subsingleton_of_forall_eq 0 fun x => ?_
  obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₃ hS x rfl (Subsingleton.elim _ _)
  obtain ⟨z, hz⟩ := hsurj y
  rw [← hz] at hy
  have hz0 : Sheaf.H.map S.g q (Sheaf.H.map S.f q z) = 0 := by
    change (z.comp (Ext.mk₀ S.f) (add_zero q)).comp (Ext.mk₀ S.g) (add_zero q) = 0
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      ShortComplex.zero, Ext.mk₀_zero, Ext.comp_zero]
  exact hy.symm.trans hz0

/-- If the two known terms have cohomology only in positive degree `n`,
their cokernel can have cohomology only in degrees `n-1` and `n`. -/
theorem cokernel_cohomology_concentrated_in_two_degrees (n : ℕ) (hn : 0 < n)
    (hA : ∀ q : ℕ, q ≠ n → Subsingleton (Sheaf.H S.X₁ q))
    (hB : ∀ q : ℕ, q ≠ n → Subsingleton (Sheaf.H S.X₂ q))
    (q : ℕ) (hqn : q ≠ n) (hqprev : q ≠ n-1) :
    Subsingleton (Sheaf.H S.X₃ q) := by
  apply cokernel_cohomology_vanishes hS q (hB q hqn) (hA (q+1) _)
  omega

/-- Maximal rank on top cohomology gives natural cohomology of the actual
cokernel, including dimension one, where the possible degrees are zero and one. -/
theorem cokernel_natural_of_top_maximalRank (n : ℕ) (hn : 0 < n)
    (hA : ∀ q : ℕ, q ≠ n → Subsingleton (Sheaf.H S.X₁ q))
    (hB : ∀ q : ℕ, q ≠ n → Subsingleton (Sheaf.H S.X₂ q))
    (hmax : HasMaximalRank (Sheaf.H.map S.f n)) :
    HasNaturalCohomology S.X₃ := by
  rcases hmax with hinj | hsurj
  · refine ⟨n, fun q hq => ?_⟩
    by_cases hprev : q = n-1
    · subst q
      apply cokernel_cohomology_vanishes_of_next_injective hS (n-1)
        (hB (n-1) (by omega))
      have hnt : n - 1 + 1 = n := by omega
      rw [hnt]
      exact hinj
    · exact cokernel_cohomology_concentrated_in_two_degrees hS n hn hA hB q hq hprev
  · refine ⟨n-1, fun q hq => ?_⟩
    by_cases htop : q = n
    · subst q
      exact cokernel_cohomology_vanishes_of_surjective hS n hsurj (hA (n+1) (by omega))
    · exact cokernel_cohomology_concentrated_in_two_degrees hS n hn hA hB q htop hq

/-- Maximal rank on H0 gives natural cohomology of the actual kernel when
the other two terms have vanishing positive cohomology. -/
theorem kernel_natural_of_degreeZero_maximalRank
    (hB : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H S.X₂ q))
    (hC : ∀ q : ℕ, 0 < q → Subsingleton (Sheaf.H S.X₃ q))
    (hmax : HasMaximalRank (Sheaf.H.map S.g 0)) :
    HasNaturalCohomology S.X₁ := by
  have hhigh (q : ℕ) (hq : 1 < q) : Subsingleton (Sheaf.H S.X₁ q) := by
    obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
    exact kernel_cohomology_succ_vanishes hS q (hC q (by omega)) (hB (q+1) (by omega))
  rcases hmax with hinj | hsurj
  · refine ⟨1, fun q hq => ?_⟩
    by_cases hq0 : q = 0
    · subst q
      let : Mono S.f := hS.mono_f
      have hf : Function.Injective (Sheaf.H.map S.f 0) :=
        Ext.postcomp_mk₀_injective_of_mono _ S.f
      refine subsingleton_of_forall_eq 0 fun x => hf ?_
      apply hinj
      simp only [map_zero]
      change (x.comp (Ext.mk₀ S.f) (add_zero 0)).comp (Ext.mk₀ S.g) (add_zero 0) = 0
      simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
        ShortComplex.zero, Ext.mk₀_zero, Ext.comp_zero]
    · exact hhigh q (by omega)
  · refine ⟨0, fun q hq => ?_⟩
    by_cases hq1 : q = 1
    · subst q
      let :=  hB 1 (by omega)
      refine subsingleton_of_forall_eq 0 fun x => ?_
      obtain ⟨y, hy⟩ := Sheaf.H.longSequence_exact₁ hS x (Subsingleton.elim _ _) rfl
      obtain ⟨z, hz⟩ := hsurj y
      rw [← hz, map_boundary_zero] at hy
      exact hy.symm
    · exact hhigh q (by omega)
end SteinerGeometry
