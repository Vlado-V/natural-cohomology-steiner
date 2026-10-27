import SteinerGeometry.CurveCohomology
import SteinerGeometry.EulerDegree
import SteinerGeometry.SectionFunctorCohomology

noncomputable section
namespace SteinerGeometry.EllipticCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

/-- On a genus-one curve, one nontrivial degree-zero line gives positive-degree
H¹ vanishing by a section and the exact cokernel sequence. -/
theorem positive_euler_h1_zero_of_reference
    {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (J : Line.Bundles.LineBundle X) (hJ : 0 < χ p J.sheaf)
    (P : Line.Bundles.LineBundle X) (hP : χ p P.sheaf = 0)
    (hPne : ¬ Nonempty (P.sheaf ≅ Line.Bundles.structureModule X))
    (L : Line.Bundles.LineBundle X) (hL : 0 < χ p L.sheaf) :
    IsZero (H p L.sheaf 1) := by
  have hP1 := (zero_euler_nontrivial_cohomology p hd hO P hP hPne).2
  have hPinv := EulerDegree.reciprocal_euler p hd hO J hJ P
  have hEuler := EulerDegree.tensor_euler_add p hd hO J hJ L P.reciprocalFrameBundle
  have hpos : 0 < χ p (L.tensor P.reciprocalFrameBundle).sheaf := by omega
  obtain ⟨s, hs⟩ := positive_euler_has_section p hd
    (L.tensor P.reciprocalFrameBundle).sheaf hpos
  have hprod := sectionMultiply_h1_zero p hd (L.tensor P.reciprocalFrameBundle) P s hs hP1
  let e : ((L.tensor P.reciprocalFrameBundle).tensor P).sheaf ≅ L.sheaf :=
    L.tensorAssocIso P.reciprocalFrameBundle P ≪≫
      Tensor.ProductSheaf.tensorModuleCongr (Iso.refl L.sheaf) P.reciprocalFrameTensorIso ≪≫
        Tensor.UnitRight.tensorModuleUnitRightIso L.sheaf
  exact hprod.of_iso
    ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) 1).mapIso e).symm

/-- The positive degree is exactly the dimension used by the polynomial operator. -/
theorem positive_euler_sectionFunctor_finrank
    {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (J : Line.Bundles.LineBundle X) (hJ : 0 < χ p J.sheaf)
    (P : Line.Bundles.LineBundle X) (hP : χ p P.sheaf = 0)
    (hPne : ¬ Nonempty (P.sheaf ≅ Line.Bundles.structureModule X))
    (L : Line.Bundles.LineBundle X) (hL : 0 < χ p L.sheaf) :
    (Module.finrank ℂ ((SteinerGeometry.sectionFunctor p).obj L.sheaf) : ℤ) =
      χ p L.sheaf := by
  rw [SteinerGeometry.sectionFunctor_finrank_eq_native]
  symm
  change CohomologyEulerCharacteristic.coefficientEulerCharacteristic p L.sheaf = _
  apply CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing
  intro q
  cases q with
  | zero => exact positive_euler_h1_zero_of_reference p hd hO J hJ P hP hPne L hL
  | succ q => exact curve_cohomology_above_one p hd L.sheaf (q + 2) (by omega)

/-- Finite coherent cohomology gives the actual section spaces finite dimension. -/
theorem line_sectionFunctor_finite
    {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p]
    (L : Line.Bundles.LineBundle X) :
    Module.Finite ℂ ((SteinerGeometry.sectionFunctor p).obj L.sheaf) := by
  let _ : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  let _ : L.sheaf.IsFiniteType := L.isFiniteType
  let _ : Module.Finite ℂ (H p L.sheaf 0) :=
    CurveCohomologyFinite.finite (p := p) L.sheaf 0
  exact Module.Finite.equiv (SteinerGeometry.cohomologyZeroSectionFunctorEquiv p L.sheaf)

end SteinerGeometry.EllipticCohomology
