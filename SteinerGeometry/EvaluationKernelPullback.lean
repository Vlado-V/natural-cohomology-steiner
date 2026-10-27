import SteinerGeometry.CyclicKernelSplitting
import SteinerGeometry.FirstKernelCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Ample.LineBundles

/-! The evaluated component sections and their actual first kernel after pullback. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open OAI.AlgebraicGeometry.Picard.Homomorphisms
universe u
local instance evaluationKernelPullbackBiproducts (X : Scheme.{u}) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The canonical finite-free comparison for actual scheme pullback. -/
def freeLinearPullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ) :
    (Scheme.Modules.pullback f).obj (DualEvaluation.freeSheaf (X := X) (n+1)) ≅
      DualEvaluation.freeSheaf (X := Y) (n+1) :=
  (Scheme.Modules.pullback f).mapBiproduct
      (fun _ : Fin (n+1) => Line.Bundles.structureModule X) ≪≫
    biproduct.mapIso (fun _ => Line.Bundles.structureModulePullbackIso f)

@[simp]
theorem freeLinearPullbackIso_ι_inv {X Y : Scheme.{u}} (f : Y ⟶ X) (n : ℕ)
    (i : Fin (n+1)) :
    biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule Y) i ≫
        (freeLinearPullbackIso f n).inv =
      (Line.Bundles.structureModulePullbackIso f).inv ≫
        (Scheme.Modules.pullback f).map
          (biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule X) i) := by
  change _ ≫ (biproduct.map (fun _ => (Line.Bundles.structureModulePullbackIso f).inv) ≫
    biproduct.desc (fun i => (Scheme.Modules.pullback f).map
      (biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule X) i))) = _
  rw [← Category.assoc, biproduct.ι_map, Category.assoc, biproduct.ι_desc]

/-- Evaluation of a finite family of sections commutes with its literal pulled sections. -/
theorem structureEvaluation_pullback {X Y : Scheme.{u}} (f : Y ⟶ X) {n : ℕ} {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N)) :
    (freeLinearPullbackIso f n).inv ≫
        (Scheme.Modules.pullback f).map (structureEvaluation e) =
      structureEvaluation (fun i => Ample.LineBundles.pullbackSection f (e i)) := by
  apply biproduct.hom_ext'
  intro i
  rw [← Category.assoc, freeLinearPullbackIso_ι_inv, Category.assoc,
    ← Functor.map_comp, show biproduct.ι _ i ≫ structureEvaluation e = e i from biproduct.ι_desc e i]
  exact (biproduct.ι_desc (fun i => Ample.LineBundles.pullbackSection f (e i)) i).symm

namespace DualEvaluation

/-- The actual component sections of the dual evaluation map. -/
def componentSections {X : Scheme.{u}} {n : ℕ} (R : Line.Bundles.LineBundle X)
    (i : R.sheaf ⟶ freeSheaf (n+1)) :
    Fin (n+1) → (Line.Bundles.structureModule X ⟶ (targetLine R).sheaf) :=
  fun j => biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule X) j ≫ evaluation R i

@[simp]
theorem structureEvaluation_componentSections {X : Scheme.{u}} {n : ℕ}
    (R : Line.Bundles.LineBundle X) (i : R.sheaf ⟶ freeSheaf (n+1)) :
    structureEvaluation (componentSections R i) = evaluation R i := by
  apply biproduct.hom_ext'
  intro j
  exact biproduct.ι_desc _ j

/-- Pullback of the dual-evaluation kernel is the kernel of evaluation of
    the actual pulled-back component sections. -/
def kernelPullbackIso {X Y : Scheme.{u}} (f : Y ⟶ X) {n : ℕ}
    (R : Line.Bundles.LineBundle X) (i : R.sheaf ⟶ freeSheaf (n+1))
    [IsIso (kernelComparison (evaluation R i) (Scheme.Modules.pullback f))] :
    (Scheme.Modules.pullback f).obj (kernel (evaluation R i)) ≅
      kernel (structureEvaluation
        (fun j => Ample.LineBundles.pullbackSection f (componentSections R i j))) :=
  asIso (kernelComparison (evaluation R i) (Scheme.Modules.pullback f)) ≪≫
    kernel.mapIso _ _ (freeLinearPullbackIso f n) (Iso.refl _) (by
      apply (cancel_epi (freeLinearPullbackIso f n).inv).mp
      simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.refl_hom, Category.comp_id,
        structureEvaluation_componentSections] using
          structureEvaluation_pullback f (componentSections R i))

end DualEvaluation

namespace CyclicEtaleIsogeny
variable {S : Scheme} {D : Abelian.Schemes.AbelianScheme 1 S} {n : ℕ}
    (q : CyclicEtaleIsogeny D n) [NeZero n]
    [IsLocallyNoetherian q.target.scheme.left]

/-- A fixed finite labeling converts the cyclic deck group to Fin n. -/
def kernelIndexEquiv (_q : CyclicEtaleIsogeny D n) : Fin n ≃ Multiplicative (ZMod n) :=
  (Fintype.equivFinOfCardEq (by simp)).symm

/-- The line summands indexed in the finite form used by the symmetric contraction. -/
def firstKernelLineFamily (A : Line.Bundles.LineBundle D.scheme.left) :
    Fin n → Line.Bundles.LineBundle D.scheme.left :=
  fun j => LineBundleDual.Construction.lineBundleDual
    (q.translatedLineBundle A (q.kernelIndexEquiv j))

/-- The first evaluation kernel in exactly the finite form needed by the
    symmetric-power contraction, using its actual pulled component sections. -/
def componentKernelSplitting
    (A : Line.Bundles.LineBundle D.scheme.left)
    (R : Line.Bundles.LineBundle q.target.scheme.left)
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf (n+1))
    (p : DualEvaluation.freeSheaf (n+1) ⟶ q.linePushforward A) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk i p w).ShortExact) :
    (⨁ fun j => (q.firstKernelLineFamily A j).sheaf) ≅
      kernel (structureEvaluation (fun j => Ample.LineBundles.pullbackSection q.map.hom.left
        (DualEvaluation.componentSections R i j))) := by
  have : A.sheaf.IsQuasicoherent := A.isQuasicoherent
  have : (q.linePushforward A).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom q.map.hom.left
  let U : q.target.scheme.left.affineOpens → q.target.scheme.left.Opens := fun U => U.1
  have hU : iSup U = ⊤ := iSup_affineOpens_eq_top q.target.scheme.left
  have hs := evaluation_locallySplit_of_affine_presentation R i p w hS U (fun U => U.2)
    (fun U => (linePushforward_affineRestriction_finite_projective q.map.hom.left A U.1 U.2).2)
  have := LocallySplitPullbackKernel.kernelComparison_isIso_of_locallySplit
    q.map.hom.left (DualEvaluation.evaluation R i) U hU hs
  let G := fun j : Multiplicative (ZMod n) =>
    (LineBundleDual.Construction.lineBundleDual (q.translatedLineBundle A j)).sheaf
  let E : (⨁ fun j => (q.firstKernelLineFamily A j).sheaf) ≅ ⨁ G :=
    biproduct.whiskerEquiv (f := fun j => (q.firstKernelLineFamily A j).sheaf) (g := G)
      q.kernelIndexEquiv (fun _ => Iso.refl _)
  exact E ≪≫
    biproduct.isoCoproduct G ≪≫ (q.evaluationKernelPullbackSplitting A R i p w hS).symm ≪≫
    DualEvaluation.kernelPullbackIso q.map.hom.left R i

end CyclicEtaleIsogeny
end SteinerGeometry
