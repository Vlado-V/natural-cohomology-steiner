module

public import SteinerGeometry.CohomologySections
public import SteinerGeometry.SectionContraction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Steiner
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

local instance operatorCohomology_hasFiniteBiproducts (X : Scheme.{0}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

local instance operatorCohomology_sectionFunctor_preservesFiniteLimits {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) : PreservesFiniteLimits (sectionFunctor p) := by
  let R : ℂ →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of ℂ)).inv ≫ p.appTop).hom
  let F : X.Modules ⥤ ModuleCat.{0} Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (Opposite.op ⊤)
  let _ : PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits X.ringCatSheaf (Opposite.op ⊤)
  let G : ModuleCat.{0} Γ(X, ⊤) ⥤ ModuleCat.{0} ℂ := ModuleCat.restrictScalars R
  have hG : PreservesLimitsOfSize.{0, 0} G :=
    (ModuleCat.extendRestrictScalarsAdj R).rightAdjoint_preservesLimits
  let _ : PreservesFiniteLimits G := by
    constructor
    intro J _ _
    exact hG.preservesLimitsOfShape
  exact comp_preservesFiniteLimits F G

/-- Zero H⁰ of the actual sheaf kernel implies injectivity of the coefficient
operator obtained from global sections. -/
theorem operatorDifferential_injective_of_kernel_h0
    {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) {n : ℕ} {B D : X.Modules}
    (T : Fin (n+1) → (B ⟶ D)) (d : ℕ)
    (h0 : IsZero (H p (kernel (sectionContraction T d)) 0)) :
    Function.Injective (operatorDifferential
      (fun i => ((sectionFunctor p).map (T i)).hom) d) := by
  intro x y hxy
  have hnull : operatorDifferential
      (fun i => ((sectionFunctor p).map (T i)).hom) d (x-y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨z, hz, _⟩ :=
    (sectionContraction_kernel_sections (sectionFunctor p) T d (x-y)).mp hnull
  have hz0 : z = 0 := by
    let e := Zariski.Cohomology.ZariskiCohomology.hZeroEquivGlobalSections
      (kernel (sectionContraction T d))
    apply e.symm.injective
    exact (ModuleCat.subsingleton_of_isZero h0).elim _ _
  rw [hz0, map_zero, map_zero] at hz
  exact sub_eq_zero.mp hz.symm

/-- Zero H¹ of the actual sheaf kernel implies surjectivity of the coefficient
operator when the sheaf contraction is epimorphic. -/
theorem operatorDifferential_surjective_of_kernel_h1
    {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) {n : ℕ} {B D : X.Modules}
    (T : Fin (n+1) → (B ⟶ D)) (d : ℕ) [Epi (sectionContraction T d)]
    (h1 : IsZero (H p (kernel (sectionContraction T d)) 1)) :
    Function.Surjective (operatorDifferential
      (fun i => ((sectionFunctor p).map (T i)).hom) d) := by
  let F := sectionFunctor p
  have hS : (ShortComplex.kernelSequence (sectionContraction T d)).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact _,
      epi_g := by change Epi (sectionContraction T d); infer_instance }
  have hsurj := EvaluationCohomology.sections_surjective_of_h1_zero p hS h1
  intro y
  obtain ⟨z, hz⟩ := hsurj ((biproductCoordinates F D (Sym (Fin (n+1)) d)).symm y)
  refine ⟨biproductCoordinates F B (Sym (Fin (n+1)) (d+1)) z, ?_⟩
  let z' : F.obj (⨁ fun _ : Sym (Fin (n+1)) (d+1) => B) := z
  have hc := (biproductCoordinates F B (Sym (Fin (n+1)) (d+1))).symm_apply_apply z'
  have h := (congrArg (fun v => biproductCoordinates F D (Sym (Fin (n+1)) d)
    (F.map (sectionContraction T d) v)) hc).symm.trans
      (sectionContraction_sections F T d
        (biproductCoordinates F B (Sym (Fin (n+1)) (d+1)) z'))
  rw [← h]
  change biproductCoordinates F D _ ((sectionContraction T d).app ⊤ z) = y
  change (sectionContraction T d).app ⊤ z = _ at hz
  rw [hz]
  exact LinearEquiv.apply_symm_apply _ _

/-- The curve construction's genuine contraction gives the operator injection. -/
theorem curve_operatorDifferential_injective_of_h0
    {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) {n : ℕ}
    (L B : Line.Bundles.LineBundle X)
    (s : Fin (n+1) → (Line.Bundles.structureModule X ⟶ L.sheaf)) (d : ℕ)
    (h0 : IsZero (H p (curveContractionKernel L B s d) 0)) :
    Function.Injective (operatorDifferential
      (fun i => ((sectionFunctor p).map
        (LineBundle.SectionMultiplication.lineBundleSectionMultiply L B (s i))).hom) d) :=
  operatorDifferential_injective_of_kernel_h0 p _ d h0

/-- The curve construction's genuine contraction gives the operator surjection. -/
theorem curve_operatorDifferential_surjective_of_h1
    {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) {n : ℕ}
    (L B : Line.Bundles.LineBundle X)
    (s : Fin (n+1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) (d : ℕ)
    (h1 : IsZero (H p (curveContractionKernel L B s d) 1)) :
    Function.Surjective (operatorDifferential
      (fun i => ((sectionFunctor p).map
        (LineBundle.SectionMultiplication.lineBundleSectionMultiply L B (s i))).hom) d) := by
  have : Epi (sectionContraction
      (fun i => LineBundle.SectionMultiplication.lineBundleSectionMultiply L B (s i)) d) :=
    curveSectionContraction_epi p L B s hs d
  exact operatorDifferential_surjective_of_kernel_h1 p _ d h1

end SteinerGeometry
