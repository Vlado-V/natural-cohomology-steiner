import SteinerGeometry.ProjectiveCohomology
import SteinerGeometry.ModuleNaturality

/-! The sheaf-cohomology deduction for actual Steiner presentations. -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry
open SheafCohomology.Projective
namespace SteinerGeometry

universe u
variable {R : Type u} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

private theorem cohomology_subsingleton_of_iso
    {n : ℕ} {M N : (projectiveSpace R n).Modules} (e : M ≅ N)
    (q : ℕ) (hN : Subsingleton (SchemeModules.H N q)) :
    Subsingleton (SchemeModules.H M q) := by
  letI := hN
  let h := (SheafCohomology.AffineH.Projective.zariskiFunctor (projectiveSpace R n) q).mapIso e
  have hinj : Function.Injective h.hom := by
    intro a b hab
    have h' := congrArg (fun x => h.inv x) hab
    simpa using h'
  exact hinj.subsingleton

/-- A Steiner presentation in a nonnegative twist has cohomology only in degree zero.
The proof applies to the actual short exact sequence of module sheaves. -/
theorem steinerCokernel_nonnegative_natural {n t r : ℕ} (hn : 0 < n)
    (b : ℤ) (hb : 0 ≤ b)
    (S : ShortComplex (projectiveSpace R n).Modules) (hS : S.ShortExact)
    (eA : S.X₁ ≅ projectiveTwistSum R n t (b-1))
    (eB : S.X₂ ≅ projectiveTwistSum R n (t+r) b) :
    SchemeModules.HasNaturalCohomology S.X₃ := by
  apply SchemeModules.cokernel_natural_of_positive_vanishing hS
  · intro q hq
    apply cohomology_subsingleton_of_iso eA q
    change Subsingleton (projectiveTwistSumCohomology R n t (b-1) q)
    apply projectiveTwistSumCohomology_subsingleton
    exact projectiveTwistCohomology_positive_of_degree_gt n (b-1) (by omega) q hq
  · intro q hq
    apply cohomology_subsingleton_of_iso eB q
    change Subsingleton (projectiveTwistSumCohomology R n (t+r) b q)
    exact projectiveTwistSumCohomology_positive_of_nonnegative n (t+r) b hb q hq

/-- Negative twists of an actual Steiner presentation have natural cohomology
whenever their induced map on top cohomology has maximal rank. -/
theorem steinerCokernel_negative_natural {n t r : ℕ} (hn : 0 < n)
    (b : ℤ) (hb : b < 0)
    (S : ShortComplex (projectiveSpace R n).Modules) (hS : S.ShortExact)
    (eA : S.X₁ ≅ projectiveTwistSum R n t (b-1))
    (eB : S.X₂ ≅ projectiveTwistSum R n (t+r) b)
    (hmax : HasMaximalRank
      ((SheafCohomology.AffineH.Projective.zariskiFunctor (projectiveSpace R n) n).map S.f)) :
    SchemeModules.HasNaturalCohomology S.X₃ := by
  apply SchemeModules.cokernel_natural_of_top_maximalRank hS n hn
  · intro q hq
    apply cohomology_subsingleton_of_iso eA q
    change Subsingleton (projectiveTwistSumCohomology R n t (b-1) q)
    exact projectiveTwistSumCohomology_negative_off_top n t hn (b-1) (by omega) q hq
  · intro q hq
    apply cohomology_subsingleton_of_iso eB q
    change Subsingleton (projectiveTwistSumCohomology R n (t+r) b q)
    exact projectiveTwistSumCohomology_negative_off_top n (t+r) hn b hb q hq
  · exact hmax

/-- In the remaining shallow negative twists the target top group vanishes,
so its map is automatically surjective; no matrix calculation is needed. -/
theorem steinerCokernel_shallow_negative_natural {n t r : ℕ} (hn : 0 < n)
    (b : ℤ) (hb : b < 0) (hbn : -(n : ℤ) ≤ b)
    (S : ShortComplex (projectiveSpace R n).Modules) (hS : S.ShortExact)
    (eA : S.X₁ ≅ projectiveTwistSum R n t (b-1))
    (eB : S.X₂ ≅ projectiveTwistSum R n (t+r) b) :
    SchemeModules.HasNaturalCohomology S.X₃ := by
  apply steinerCokernel_negative_natural hn b hb S hS eA eB
  have hB : Subsingleton (SchemeModules.H S.X₂ n) := by
    apply cohomology_subsingleton_of_iso eB n
    change Subsingleton (projectiveTwistSumCohomology R n (t+r) b n)
    apply projectiveTwistSumCohomology_subsingleton
    exact projectiveTwistCohomology_positive_of_degree_gt n b (by omega) n hn
  letI := hB
  exact Or.inr fun y => ⟨0, Subsingleton.elim _ _⟩

/-- The all-twist sheaf conclusion is reduced to the induced top maps of the
actual negative-twist presentations. It includes projective dimension one. -/
theorem steinerCokernel_all_twists_natural {n t r : ℕ} (hn : 0 < n)
    (S : ℤ → ShortComplex (projectiveSpace R n).Modules)
    (hS : ∀ b, (S b).ShortExact)
    (eA : ∀ b, (S b).X₁ ≅ projectiveTwistSum R n t (b-1))
    (eB : ∀ b, (S b).X₂ ≅ projectiveTwistSum R n (t+r) b)
    (hmax : ∀ b : ℤ, b < -(n : ℤ) → HasMaximalRank
      ((SheafCohomology.AffineH.Projective.zariskiFunctor (projectiveSpace R n) n).map (S b).f)) :
    ∀ b : ℤ, SchemeModules.HasNaturalCohomology (S b).X₃ := by
  intro b
  by_cases hb : 0 ≤ b
  · exact steinerCokernel_nonnegative_natural hn b hb (S b) (hS b) (eA b) (eB b)
  · by_cases hdeep : b < -(n : ℤ)
    · exact steinerCokernel_negative_natural hn b (by omega) (S b) (hS b) (eA b) (eB b) (hmax b hdeep)
    · exact steinerCokernel_shallow_negative_natural hn b (by omega) (by omega) (S b) (hS b) (eA b) (eB b)

end SteinerGeometry
