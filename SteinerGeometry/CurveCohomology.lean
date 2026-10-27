module

public import SteinerGeometry.ElementaryCurveCohomology
public import SteinerGeometry.CurveEulerAdditivity
public import SteinerGeometry.EulerIso
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ExactPairs
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitRight

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry.EllipticCohomology
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

theorem flasqueModule_isZero_of_euler_zero {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (M : X.Modules)
    [M.IsQuasicoherent] [M.IsFiniteType]
    (hf : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf X.ringCatSheaf).obj M))
    (he : χ p M = 0) : IsZero M := by
  have hfini := CurveCohomologyFinite.finite (p := p) M 0
  let _ : Module.Finite ℂ (H p M 0) := hfini
  have hEuler := CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing
    p M (fun q => cohomology_isZero_of_flasque p M hf q)
  change χ p M = _ at hEuler
  have hz : Module.finrank ℂ (H p M 0) = 0 := by
    have hdim := (CoefficientCohomology.DegreeZero.ZariskiCohomology.coefficientCohomologyZeroSectionsEquiv
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) M).finrank_eq
    change Module.finrank ℂ (H p M 0) = Module.finrank ℂ
      ((Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj M) at hdim
    omega
  have h0 : Subsingleton (H p M 0) := Module.finrank_zero_iff.mp hz
  apply flasqueModule_isZero_of_sections M hf
  exact (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections M).toEquiv.subsingleton_congr.mp h0

/-- Negative degree, expressed by the intrinsic difference of Euler characteristics,
forces the actual section module to vanish. -/
theorem negative_euler_difference_h0_zero {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (L : Line.Bundles.LineBundle X)
    (hneg : χ p L.sheaf < χ p (Line.Bundles.structureModule X)) :
    IsZero (H p L.sheaf 0) := by
  apply h0_isZero_of_sections_zero p L.sheaf
  intro s
  by_contra hs
  let _ := section_nonvanishing_nonempty L s hs
  have hc := sectionCokernel_euler_nonneg p hd L (Line.Bundles.LineBundle.trivial X) s hs
  change 0 ≤ χ p (cokernel (LineBundle.SectionMultiplication.lineBundleSectionMultiply L
    (Line.Bundles.LineBundle.trivial X) s)) at hc
  rw [CurveEulerAdditivity.sectionCokernel_euler p hd L
    (Line.Bundles.LineBundle.trivial X) s] at hc
  have hu := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p
    (Tensor.UnitRight.tensorModuleUnitRightIso L.sheaf)
  change 0 ≤ χ p (L.tensor (Line.Bundles.LineBundle.trivial X)).sheaf -
    χ p (Line.Bundles.structureModule X) at hc
  change χ p (L.tensor (Line.Bundles.LineBundle.trivial X)).sheaf = χ p L.sheaf at hu
  omega

/-- A degree-zero line bundle with a nonzero section is trivial. -/
theorem zero_euler_difference_trivial_of_section {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (L : Line.Bundles.LineBundle X)
    (he : χ p L.sheaf = χ p (Line.Bundles.structureModule X))
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (hs : s ≠ 0) :
    Nonempty (L.sheaf ≅ Line.Bundles.structureModule X) := by
  let _ := section_nonvanishing_nonempty L s hs
  let f := LineBundle.SectionMultiplication.lineBundleSectionMultiply L (Line.Bundles.LineBundle.trivial X) s
  let _ : Mono f := IntegralLineBundleMonomorphisms.lineBundleSectionMultiply_mono L _ s
  let _ : (Line.Bundles.LineBundle.trivial X).sheaf.IsQuasicoherent :=
    (Line.Bundles.LineBundle.trivial X).isQuasicoherent
  let _ : (L.tensor (Line.Bundles.LineBundle.trivial X)).sheaf.IsQuasicoherent :=
    (L.tensor (Line.Bundles.LineBundle.trivial X)).isQuasicoherent
  let _ : (L.tensor (Line.Bundles.LineBundle.trivial X)).sheaf.IsFiniteType :=
    (L.tensor (Line.Bundles.LineBundle.trivial X)).isFiniteType
  let _ : (cokernel f).IsQuasicoherent := Quasicoherent.Cokernels.module_quasicoherent_cokernel f
  let _ : (cokernel f).IsFiniteType := Quasicoherent.QuotientFiniteType.quasicoherent_cokernel_finiteType f
  have hEuler : χ p (cokernel f) = 0 := by
    have hc := CurveEulerAdditivity.sectionCokernel_euler p hd L
      (Line.Bundles.LineBundle.trivial X) s
    have hu := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p
      (Tensor.UnitRight.tensorModuleUnitRightIso L.sheaf)
    change χ p (L.tensor (Line.Bundles.LineBundle.trivial X)).sheaf = χ p L.sheaf at hu
    change χ p (cokernel f) = χ p (L.tensor (Line.Bundles.LineBundle.trivial X)).sheaf -
      χ p (Line.Bundles.structureModule X) at hc
    rw [hu, he, sub_self] at hc
    exact hc
  have hz := flasqueModule_isZero_of_euler_zero p (cokernel f)
    (sectionCokernel_flasque hd L (Line.Bundles.LineBundle.trivial X) s hs) hEuler
  let _ : Epi f := Preadditive.epi_of_isZero_cokernel f hz
  let _ : IsIso f := isIso_of_mono_of_epi f
  exact ⟨((asIso f) ≪≫ Tensor.UnitRight.tensorModuleUnitRightIso L.sheaf).symm⟩

/-- The degree-zero nontrivial case, with the actual genus-one structure
Euler characteristic supplied separately from the line bundle. -/
theorem zero_euler_nontrivial_cohomology {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (L : Line.Bundles.LineBundle X) (he : χ p L.sheaf = 0)
    (hne : ¬ Nonempty (L.sheaf ≅ Line.Bundles.structureModule X)) :
    IsZero (H p L.sheaf 0) ∧ IsZero (H p L.sheaf 1) := by
  have h0 : IsZero (H p L.sheaf 0) := by
    apply h0_isZero_of_sections_zero p L.sheaf
    intro s
    by_contra hs
    exact hne (zero_euler_difference_trivial_of_section p hd L (he.trans hO.symm) s hs)
  have hdim0 : Module.finrank ℂ (H p L.sheaf 0) = 0 := by
    let _ := ModuleCat.subsingleton_of_isZero h0
    exact Module.finrank_zero_of_subsingleton
  let _ : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  let _ : L.sheaf.IsFiniteType := L.isFiniteType
  let _ : Module.Finite ℂ (H p L.sheaf 1) :=
    CurveCohomologyFinite.finite (p := p) L.sheaf 1
  have hdim1 : Module.finrank ℂ (H p L.sheaf 1) = 0 := by
    have hχ := curve_euler_eq_h0_sub_h1 p hd L.sheaf
    rw [he, hdim0, Nat.cast_zero] at hχ
    omega
  let _ : Subsingleton (H p L.sheaf 1) := Module.finrank_zero_iff.mp hdim1
  exact ⟨h0, ModuleCat.isZero_of_subsingleton _⟩

theorem sectionMultiply_h1_zero {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (L M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (hs : s ≠ 0)
    (hM : IsZero (H p M.sheaf 1)) : IsZero (H p (L.tensor M).sheaf 1) := by
  let _ := section_nonvanishing_nonempty L s hs
  let f := LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s
  let _ : Mono f := IntegralLineBundleMonomorphisms.lineBundleSectionMultiply_mono L M s
  let S : ShortComplex X.Modules := ShortComplex.mk f (cokernel.π f) (cokernel.condition f)
  have hS : S.ShortExact := ⟨ShortComplex.cokernelSequence_exact f⟩
  have hQ := sectionCokernel_positive_vanish p hd L M s hs 0
  have hsubM := ModuleCat.subsingleton_of_isZero hM
  have hsubQ := ModuleCat.subsingleton_of_isZero hQ
  apply ModuleCat.isZero_iff_subsingleton.mpr
  constructor
  intro x y
  have hz (z : H p (L.tensor M).sheaf 1) : z = 0 := by
    have hg : ((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
        (Coefficient.ModulePresheaf.schemeCoefficientMap p) 1).map S.g).hom z = 0 :=
      hsubQ.elim _ _
    obtain ⟨w, hw⟩ := (CoefficientCohomology.ExactPairs.ZariskiCohomology.coefficientCohomology_exact_middle
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS 1 z).mp hg
    rw [hsubM.elim w 0, map_zero] at hw
    exact hw.symm
  exact (hz x).trans (hz y).symm

theorem zero_euler_nontrivial_all_cohomology {X : Scheme.{0}}
    [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (L : Line.Bundles.LineBundle X) (he : χ p L.sheaf = 0)
    (hne : ¬ Nonempty (L.sheaf ≅ Line.Bundles.structureModule X)) (q : ℕ) :
    IsZero (H p L.sheaf q) := by
  cases q with
  | zero => exact (zero_euler_nontrivial_cohomology p hd hO L he hne).1
  | succ q =>
    cases q with
    | zero => exact (zero_euler_nontrivial_cohomology p hd hO L he hne).2
    | succ q => exact curve_cohomology_above_one p hd L.sheaf (q + 2) (by omega)


end SteinerGeometry.EllipticCohomology
