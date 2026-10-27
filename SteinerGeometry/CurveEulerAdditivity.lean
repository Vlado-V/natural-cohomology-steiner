import SteinerGeometry.CurveCohomologyFinite
import SteinerGeometry.CurveCohomologyCore
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LineBundleSectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyDimensionBalance
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.IntegralLineBundleMonomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.QuotientFiniteType

/-! Euler additivity on a curve follows from its actual six-term cohomology
sequence and finite-dimensional coherent cohomology. -/
noncomputable section
namespace SteinerGeometry.CurveEulerAdditivity
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

theorem coherent_euler_additive {X : Scheme.{0}} [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p]
    (hd : topologicalKrullDim X ≤ 1)
    {S : ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₁.IsFiniteType]
    [S.X₂.IsQuasicoherent] [S.X₂.IsFiniteType]
    [S.X₃.IsQuasicoherent] [S.X₃.IsFiniteType] :
    χ p S.X₂ = χ p S.X₁ + χ p S.X₃ := by
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap p
  have h0 := CohomologyDimensionBalance.coefficientCohomology_dimension_balance_zero c hS
  have h1 := CohomologyDimensionBalance.coefficientCohomology_dimension_balance_succ c hS 0
  have hzero : Subsingleton (H p S.X₁ 2) :=
    ModuleCat.isZero_iff_subsingleton.mp (curve_cohomology_above_one p hd S.X₁ 2 le_rfl)
  let _ := hzero
  have hr : Module.finrank ℂ
      (LinearMap.range (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap c hS 1).hom) = 0 :=
    Module.finrank_zero_of_subsingleton
  have hχ₁ := curve_euler_eq_h0_sub_h1 p hd S.X₁
  have hχ₂ := curve_euler_eq_h0_sub_h1 p hd S.X₂
  have hχ₃ := curve_euler_eq_h0_sub_h1 p hd S.X₃
  change Module.finrank ℂ (H p S.X₁ 0) + Module.finrank ℂ (H p S.X₃ 0) =
    Module.finrank ℂ (H p S.X₂ 0) + _ at h0
  change Module.finrank ℂ (H p S.X₁ 1) + Module.finrank ℂ (H p S.X₃ 1) =
    Module.finrank ℂ (H p S.X₂ 1) + _ + _ at h1
  rw [hr] at h1
  omega

/-- The genuine cokernel of multiplication by a nonzero line section has the
Euler difference of the two actual line sheaves. -/
theorem sectionCokernel_euler {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p]
    (hd : topologicalKrullDim X ≤ 1)
    (L M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf)
    [Nonempty (Ample.LineBundles.sectionNonvanishing s)] :
    χ p (cokernel (LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s)) =
      χ p (L.tensor M).sheaf - χ p M.sheaf := by
  have : M.sheaf.IsFiniteType := M.isFiniteType
  have : (L.tensor M).sheaf.IsFiniteType := (L.tensor M).isFiniteType
  have : M.sheaf.IsQuasicoherent := M.isQuasicoherent
  have : (L.tensor M).sheaf.IsQuasicoherent := (L.tensor M).isQuasicoherent
  let f := LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s
  have : Mono f := IntegralLineBundleMonomorphisms.lineBundleSectionMultiply_mono L M s
  have : (cokernel f).IsQuasicoherent := Quasicoherent.Cokernels.module_quasicoherent_cokernel f
  have : (cokernel f).IsFiniteType := Quasicoherent.QuotientFiniteType.quasicoherent_cokernel_finiteType f
  let S : ShortComplex X.Modules := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact f⟩
  have h := coherent_euler_additive p hd hS
  change χ p (L.tensor M).sheaf = χ p M.sheaf + χ p (cokernel f) at h
  change χ p (cokernel f) = _
  omega
end SteinerGeometry.CurveEulerAdditivity
