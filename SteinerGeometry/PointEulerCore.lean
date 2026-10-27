module

public import SteinerGeometry.CurveCohomologyCore
public import SteinerGeometry.PointSections

set_option backward.privateInPublic true
@[expose] public section

/-! Genuine Euler characteristic of a complex point and finite products of points. -/
noncomputable section

namespace SteinerGeometry.PointEuler
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

/-- The spectrum of a finite product of copies of ℂ has one Euler unit per factor. -/
theorem finiteProductSpec_structure_euler (J : Type) [Fintype J] :
    χ (Spec.map (CommRingCat.ofHom (algebraMap ℂ (J → ℂ))))
      (Line.Bundles.structureModule (Spec (.of (J → ℂ)))) = Fintype.card J := by
  let R := J → ℂ
  let b : Spec (.of R) ⟶ Spec (.of ℂ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
  have hdim : topologicalKrullDim (Spec (.of R)) ≤ 0 :=
    topologicalKrullDim_zero_of_discreteTopology _
  have hv (q : ℕ) : IsZero (H b (Line.Bundles.structureModule (Spec (.of R))) (q + 1)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply OAI.AlgebraicGeometry.SheafCohomology.VanishingGrothendieckVanishing.Projective.GrothendieckVanishing
      (TopCat.of (Spec (.of R))) (q + 1) (hdim.trans_lt ?_)
    exact_mod_cast Nat.succ_pos q
  change CohomologyEulerCharacteristic.coefficientEulerCharacteristic b
    (Line.Bundles.structureModule (Spec (.of R))) = Fintype.card J
  rw [CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing
    _ _ hv]
  have he := PointSections.spec_structure_sections_finrank R
  rw [Module.finrank_fintype_fun_eq_card] at he
  exact_mod_cast he

/-- A point has only its degree-zero cohomology, which is its coefficient field. -/
theorem complexPoint_structure_euler :
    χ (𝟙 (Spec (.of ℂ))) (Line.Bundles.structureModule (Spec (.of ℂ))) = 1 := by
  have hdim : topologicalKrullDim (Spec (.of ℂ)) = 0 := by
    change topologicalKrullDim (PrimeSpectrum ℂ) = 0
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  have hv (q : ℕ) : IsZero
      (H (𝟙 (Spec (.of ℂ))) (Line.Bundles.structureModule (Spec (.of ℂ))) (q + 1)) := by
    apply ModuleCat.isZero_iff_subsingleton.mpr
    apply OAI.AlgebraicGeometry.SheafCohomology.VanishingGrothendieckVanishing.Projective.GrothendieckVanishing
      (TopCat.of (Spec (.of ℂ))) (q + 1) ?_
    rw [hdim]
    exact_mod_cast Nat.succ_pos q
  change CohomologyEulerCharacteristic.coefficientEulerCharacteristic
    (𝟙 (Spec (.of ℂ))) (Line.Bundles.structureModule (Spec (.of ℂ))) = 1
  rw [CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing
    _ _ hv]
  exact_mod_cast PointSections.complexPoint_structure_sections_finrank

end SteinerGeometry.PointEuler
