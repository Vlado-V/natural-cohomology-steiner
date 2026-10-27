module

public import SteinerGeometry.NativeCohomology
public import SteinerGeometry.CurveSectionFunctor
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.ExactPairs

set_option backward.privateInPublic true
@[expose] public section

noncomputable section

namespace SteinerGeometry.EvaluationCohomology

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

/-- The long exact sequence lifts every quotient section when H¹ of the
kernel vanishes. All sections here are sections of the actual module sheaf. -/
theorem sections_surjective_of_h1_zero {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) {S : ShortComplex X.Modules} (hS : S.ShortExact)
    (h1 : IsZero (H p S.X₁ 1)) : Function.Surjective (S.g.app ⊤) := by
  intro z
  let e₃ := Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections S.X₃
  let e₂ := Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections S.X₂
  let x : H p S.X₃ 0 := e₃.symm z
  have hx : (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS 0).hom x = 0 :=
    (ModuleCat.subsingleton_of_isZero h1).elim _ _
  obtain ⟨y, hy⟩ :=
    (CoefficientCohomology.ExactPairs.ZariskiCohomology.coefficientCohomology_exact_right
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS 0 x).mp hx
  refine ⟨e₂ y, ?_⟩
  exact (Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections_naturality S.g y).trans
    ((congrArg e₃ hy).trans (e₃.apply_symm_apply z))

/-- For a point evaluation sequence, the previous statement is literally
surjectivity of the canonical pullback-unit evaluation map. -/
theorem evaluation_surjective_of_h1_zero {X Y : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) (a : Y ⟶ X) (E I : X.Modules)
    (i : I ⟶ E)
    (hi : i ≫ (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E = 0)
    (hS : (ShortComplex.mk i
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app E) hi).ShortExact)
    (h1 : IsZero (H p I 1)) :
    Function.Surjective (sectionEvaluation p E a) := by
  exact sections_surjective_of_h1_zero p hS h1


end SteinerGeometry.EvaluationCohomology
