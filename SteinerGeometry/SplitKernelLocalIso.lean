module

public import SteinerGeometry.SectionTensorKernelGlobal
public import SteinerGeometry.SheafMatrixCoordinates
public import SteinerGeometry.SectionContraction

set_option backward.privateInPublic true
@[expose] public section

/-! Local isomorphism criterion for the genuine split-monomial kernel morphism. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}
local instance splitKernelLocalIsoBiproducts : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

private instance splitKernelLocalIsoEvalAdditive (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive where
  map_add := by intros; rfl

/-- Coordinates of actual sections of the direct sum of monomial line factors. -/
def splitMonomialSectionCoordinates {n : ℕ} (L : Fin n → Line.Bundles.LineBundle X)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (s : ℕ) (U : X.Opens) :
    Γ(splitMonomialSource L s, U) ≃ₗ[Γ(X, U)] (Sym (Fin n) s → Γ(X, U)) :=
  (sheafIsoSections (splitMonomialFrameIso L frames s) U).trans
    (structureSumCoordinates U (Sym (Fin n) s))

/-- Given the invertible completion of the first kernel frame, the global
monomial morphism is bijective on sections of each trivializing chart. -/
theorem splitMonomialKernelMap_bijective_sections_of_matrices
    {K : Type u} [Field K] [CharZero K] {n d : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (L : Fin n → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (hc : ∀ j, ∑ i, (c j ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ e i = 0)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (U : X.Opens) [Algebra K Γ(X, U)]
    (A B : Matrix (Fin (n+1)) (Fin (n+1)) Γ(X, U))
    (hAB : A * B = 1) (hBA : B * A = 1)
    (hRows : ∀ i : Fin n, A i.succ = kernelRowCoefficients L c frames U i)
    (hA : ∀ i, ∑ j, structureMapValue (e j) U (1 : Γ(X, U)) * A i j =
      if i = 0 then 1 else 0) :
    Function.Bijective ((splitMonomialKernelMap (d := d) e L c hc).app U) := by
  classical
  let delta := sectionContraction e d
  let mu := splitMonomialMap L c (d+1)
  let kappa := splitMonomialKernelMap (d := d) e L c hc
  let SC := splitMonomialSectionCoordinates L frames (d+1) U
  let TC := structureSumCoordinates U (Sym (Fin (n+1)) (d+1))
  let f : Fin (n+1) → Γ(X, U) := fun i => structureMapValue (e i) U (1 : Γ(X, U))
  have hform (v : Sym (Fin n) (d+1) → Γ(X, U)) :
      TC (mu.app U (SC.symm v)) = splitPolynomialMap A (d+1) v := by
    exact splitMonomialMap_coordinates_of_rows L c frames U A hRows v
  have hcomm (x : Γ(splitMonomialSource L (d+1), U)) :
      (kernel.ι delta).app U (kappa.app U x) = mu.app U x := by
    exact congrArg (fun g => g.app U x) (splitMonomialKernelMap_ι (d := d) e L c hc)
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : PreservesFiniteLimits F := SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have hinj : Function.Injective ((kernel.ι delta).app U) := by
    exact (ModuleCat.mono_iff_injective (F.map (kernel.ι delta))).mp inferInstance
  constructor
  · intro x y h
    apply SC.injective
    apply splitPolynomialMap_injective A B hAB (d+1)
    have hh := congrArg (fun z => TC ((kernel.ι delta).app U z)) h
    rw [hcomm, hcomm] at hh
    have hx := hform (SC x)
    have hy := hform (SC y)
    rw [SC.symm_apply_apply] at hx hy
    exact hx.symm.trans (hh.trans hy)
  · intro z
    let y := TC ((kernel.ι delta).app U z)
    have hzero : delta.app U ((kernel.ι delta).app U z) = 0 := by
      exact congrArg (fun g => g.app U z) (kernel.condition delta)
    have hz : weightedContraction f d y = 0 := by
      have ht := sectionContraction_structure_coordinates e d U y
      have hy : TC.symm y = (kernel.ι delta).app U z := TC.symm_apply_apply _
      change structureSumCoordinates U (Sym (Fin (n+1)) d)
        (delta.app U (TC.symm y)) = weightedContraction f d y at ht
      rw [hy, hzero, map_zero] at ht
      exact ht.symm
    obtain ⟨v, hv, _⟩ := (weightedContraction_kernel_exact (K := K) f A B hAB hBA hA d y).mp hz
    refine ⟨SC.symm v, ?_⟩
    apply hinj
    apply TC.injective
    rw [hcomm, hform, hv]

/-- On a chart with actual line frames and invertible kernel completions, the
monomial map is an isomorphism onto the genuine contraction kernel sheaf. -/
theorem splitMonomialKernelMap_isIso_of_matrices
    {K : Type u} [Field K] [CharZero K] (p : X ⟶ Spec (.of K)) {n d : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (L : Fin n → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (hc : ∀ j, ∑ i, (c j ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ e i = 0)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (hmat : ∀ U : X.Opens, ∃ A B : Matrix (Fin (n+1)) (Fin (n+1)) Γ(X, U),
      A * B = 1 ∧ B * A = 1 ∧
      (∀ i : Fin n, A i.succ = kernelRowCoefficients L c frames U i) ∧
      (∀ i, ∑ j, structureMapValue (e j) U (1 : Γ(X, U)) * A i j =
        if i = 0 then 1 else 0)) :
    IsIso (splitMonomialKernelMap (d := d) e L c hc) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let co : K →+* Γ(X, U) := (X.presheaf.map U.leTop.op).hom.comp
    (Coefficient.ModulePresheaf.schemeCoefficientMap p)
  let _ : Algebra K Γ(X, U) := co.toAlgebra
  obtain ⟨A, B, hAB, hBA, hRows, hA⟩ := hmat U
  exact splitMonomialKernelMap_bijective_sections_of_matrices (K := K)
    e L c hc frames U A B hAB hBA hRows hA

end SteinerGeometry
