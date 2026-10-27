import SteinerGeometry.SectionContractionCategory
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Coefficient.SectionEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.SectionMultiplication
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.EpimorphismCover
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Section.Frames
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Power.Nonvanishing
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! The actual section contraction on sheaves and its short exact sequence. -/

noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

universe u

local instance sectionContractionBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

private theorem module_epi_of_app_surjective {X : Scheme.{u}} {M N : X.Modules}
    (f : M ⟶ N) (hf : ∀ U : X.Opens, Function.Surjective (f.app U)) : Epi f := by
  constructor
  intro P g h hgh
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨y, rfl⟩ := hf U x
  have he := congrArg (fun q : M ⟶ P => q.app U y) hgh
  exact he

/-- A locally invertible coefficient guarantees that the actual sheaf contraction
is an epimorphism. The base coefficient map supplies characteristic zero. -/
theorem sectionContraction_epi_of_local_isIso
    {X : Scheme.{u}} {K : Type u} [Field K] [CharZero K]
    (p : X ⟶ Spec (.of K)) {n : ℕ} {M N : X.Modules}
    (T : Fin (n+1) → (M ⟶ N)) {ι : Type*} (U : ι → X.Opens)
    (hU : ∀ x : X, ∃ i, x ∈ U i) (j : ι → Fin (n+1))
    (hT : ∀ i, IsIso ((Scheme.Modules.restrictFunctor (U i).ι).map (T (j i))))
    (d : ℕ) : Epi (sectionContraction T d) := by
  apply Module.EpimorphismCover.module_epi_of_restrict_cover U hU
  intro i
  apply module_epi_of_app_surjective
  intro V
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap ((U i).ι ≫ p)
  let F := Scheme.Modules.restrictFunctor (U i).ι ⋙
    Coefficient.SectionEvaluation.coefficientSectionFunctor c V
  let _ := hT i
  have hsurj : Function.Surjective (F.map (T (j i))) := by
    have : IsIso (F.map (T (j i))) := by
      dsimp [F]
      infer_instance
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  let _ : F.Additive := by
    constructor
    intro A B f g
    apply ModuleCat.hom_ext
    ext x
    rfl
  exact sectionContraction_map_surjective F T (j i) hsurj d

/-- The sheaf map in the section multiplication lemma. Its components are the
integer partial-derivative multiplicities times actual multiplication by sections. -/
def curveSectionContraction {X : Scheme.{u}} {n : ℕ}
    (L B : Line.Bundles.LineBundle X)
    (s : Fin (n+1) → (Line.Bundles.structureModule X ⟶ L.sheaf)) (d : ℕ) :
    (⨁ fun _ : Sym (Fin (n+1)) (d+1) => B.sheaf) ⟶
      (⨁ fun _ : Sym (Fin (n+1)) d => (L.tensor B).sheaf) :=
  sectionContraction (fun i => LineBundle.SectionMultiplication.lineBundleSectionMultiply L B (s i)) d

/-- Basepoint-free sections give the short exact symmetric-contraction sheaf sequence. -/
theorem curveSectionContraction_epi {X : Scheme.{u}}
    {K : Type u} [Field K] [CharZero K] (p : X ⟶ Spec (.of K))
    {n : ℕ} (L B : Line.Bundles.LineBundle X)
    (s : Fin (n+1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) (d : ℕ) :
    Epi (curveSectionContraction L B s d) := by
  apply sectionContraction_epi_of_local_isIso p _
    (fun i => Ample.LineBundles.sectionNonvanishing (s i)) hs (fun i => i)
  intro i
  apply (Power.Nonvanishing.isIso_restrict_map_iff _ _).mpr
  exact LineBundle.SectionMultiplication.lineBundleSectionMultiply_pullback_isIso _ L B (s i)

/-- The kernel is the actual kernel sheaf of contraction. -/
abbrev curveContractionKernel {X : Scheme.{u}} {n : ℕ}
    (L B : Line.Bundles.LineBundle X)
    (s : Fin (n+1) → (Line.Bundles.structureModule X ⟶ L.sheaf)) (d : ℕ) :=
  kernel (curveSectionContraction L B s d)

/-- The resulting short complex of actual module sheaves is short exact. -/
theorem curveSectionContraction_shortExact {X : Scheme.{u}}
    {K : Type u} [Field K] [CharZero K] (p : X ⟶ Spec (.of K))
    {n : ℕ} (L B : Line.Bundles.LineBundle X)
    (s : Fin (n+1) → (Line.Bundles.structureModule X ⟶ L.sheaf))
    (hs : ∀ x : X, ∃ i, x ∈ Ample.LineBundles.sectionNonvanishing (s i)) (d : ℕ) :
    (ShortComplex.kernelSequence (curveSectionContraction L B s d)).ShortExact := by
  have hepi := curveSectionContraction_epi p L B s hs d
  refine { exact := ShortComplex.kernelSequence_exact _, epi_g := ?_ }
  exact hepi

end SteinerGeometry
