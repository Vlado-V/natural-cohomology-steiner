import SteinerGeometry.SplitDualPullback
import SteinerGeometry.PullbackKernelSplitting
import SteinerGeometry.LocallySplitPullbackKernel
import SteinerGeometry.DualEvaluationLocalSplit

/-! Pullback of a genuine line-to-free presentation and its dual kernel. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

local instance pullbackDualKernelBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

namespace SheafDual

/-- Dual base change for the actual finite free sheaf. -/
def freeDualPullbackIso {X Y : Scheme} (f : Y ⟶ X) (m : ℕ) :
    (Scheme.Modules.pullback f).obj (dual (DualEvaluation.freeSheaf (X := X) m)) ≅
      dual ((Scheme.Modules.pullback f).obj (DualEvaluation.freeSheaf (X := X) m)) :=
  splitDualPullbackIso f (fun _ : Fin m => Line.Bundles.LineBundle.trivial X)

/-- The dual inclusion square commutes for a map from a line into a free sheaf. -/
theorem freeDualPullback_naturality {X Y : Scheme} (f : Y ⟶ X) {m : ℕ}
    (R : Line.Bundles.LineBundle X) (i : R.sheaf ⟶ DualEvaluation.freeSheaf m) :
    (Scheme.Modules.pullback f).map (dualMap i) ≫ (lineDualPullbackIso f R).hom =
      (freeDualPullbackIso f m).hom ≫ dualMap ((Scheme.Modules.pullback f).map i) :=
  splitDualPullbackIso_naturality_from_line f
    (fun _ : Fin m => Line.Bundles.LineBundle.trivial X) R i

end SheafDual

/-- Pulling back the dual evaluation and removing its free-dual coordinate identification. -/
def mappedEvaluationKernelIso {X Y : Scheme} (f : Y ⟶ X) {m : ℕ}
    (R : Line.Bundles.LineBundle X) (i : R.sheaf ⟶ DualEvaluation.freeSheaf m) :
    kernel ((Scheme.Modules.pullback f).map (DualEvaluation.evaluation R i)) ≅
      kernel ((Scheme.Modules.pullback f).map (SheafDual.dualMap i)) :=
  kernel.mapIso _ _ ((Scheme.Modules.pullback f).mapIso
      (DualEvaluation.freeDualIso m)).symm (Iso.refl _) (by
    simp only [DualEvaluation.evaluation, Functor.map_comp,
      Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.comp_id])

/-- Canonical free and line dual base change identifies the pulled dual kernel. -/
def mappedDualKernelIso {X Y : Scheme} (f : Y ⟶ X) {m : ℕ}
    (R : Line.Bundles.LineBundle X) (i : R.sheaf ⟶ DualEvaluation.freeSheaf m) :
    kernel ((Scheme.Modules.pullback f).map (SheafDual.dualMap i)) ≅
      kernel (SheafDual.dualMap ((Scheme.Modules.pullback f).map i)) :=
  kernel.mapIso _ _ (SheafDual.freeDualPullbackIso f m)
    (SheafDual.lineDualPullbackIso f R) (SheafDual.freeDualPullback_naturality f R i)

/-- If the canonical kernel comparison is invertible, pullback of the actual
    evaluation kernel is the dual of the pulled quotient. -/
def pullbackEvaluationKernelDualIso {X Y : Scheme} (f : Y ⟶ X) {m : ℕ}
    (R : Line.Bundles.LineBundle X) (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    {Q : X.Modules} (p : DualEvaluation.freeSheaf m ⟶ Q) (w : i ≫ p = 0)
    (h : IsColimit (CokernelCofork.ofπ p w))
    [IsIso (kernelComparison (DualEvaluation.evaluation R i) (Scheme.Modules.pullback f))] :
    (Scheme.Modules.pullback f).obj (kernel (DualEvaluation.evaluation R i)) ≅
      SheafDual.dual ((Scheme.Modules.pullback f).obj Q) :=
  asIso (kernelComparison (DualEvaluation.evaluation R i) (Scheme.Modules.pullback f)) ≪≫
    mappedEvaluationKernelIso f R i ≪≫ mappedDualKernelIso f R i ≪≫
    (SheafDual.dualCokernelIso ((Scheme.Modules.pullback f).map i)
      ((Scheme.Modules.pullback f).map p)
      (by rw [← Functor.map_comp, w, Functor.map_zero])
      ((CokernelCofork.ofπ p w).mapIsColimit h (Scheme.Modules.pullback f))).symm

/-- The actual locally split hypothesis supplies the canonical kernel comparison. -/
def pullbackEvaluationKernelDualIso_of_locallySplit {X Y : Scheme} (f : Y ⟶ X) {m : ℕ}
    (R : Line.Bundles.LineBundle X) (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    {Q : X.Modules} (p : DualEvaluation.freeSheaf m ⟶ Q) (w : i ≫ p = 0)
    (h : IsColimit (CokernelCofork.ofπ p w))
    {I : Type} (U : I → X.Opens) (hU : iSup U = ⊤)
    (hsplit : ∀ j, IsSplitEpi
      ((Scheme.Modules.pullback (U j).ι).map (DualEvaluation.evaluation R i))) :
    (Scheme.Modules.pullback f).obj (kernel (DualEvaluation.evaluation R i)) ≅
      SheafDual.dual ((Scheme.Modules.pullback f).obj Q) := by
  haveI := LocallySplitPullbackKernel.kernelComparison_isIso_of_locallySplit
    f (DualEvaluation.evaluation R i) U hU hsplit
  exact pullbackEvaluationKernelDualIso f R i p w h

namespace CyclicEtaleIsogeny
variable {S : Scheme} {D : Abelian.Schemes.AbelianScheme 1 S} {n : ℕ}
    (q : CyclicEtaleIsogeny D n) [NeZero n]

/-- The actual evaluation kernel splits into dual translated line bundles on
    the cyclic cover whenever its canonical kernel comparison is invertible. -/
def presentationKernelSplitting {m : ℕ}
    (A : Line.Bundles.LineBundle D.scheme.left)
    (R : Line.Bundles.LineBundle q.target.scheme.left)
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (p : DualEvaluation.freeSheaf m ⟶ q.linePushforward A) (w : i ≫ p = 0)
    (h : IsColimit (CokernelCofork.ofπ p w))
    [IsIso (kernelComparison (DualEvaluation.evaluation R i)
      (Scheme.Modules.pullback q.map.hom.left))] :
    (Scheme.Modules.pullback q.map.hom.left).obj (kernel (DualEvaluation.evaluation R i)) ≅
      ∐ (fun j : Multiplicative (ZMod n) =>
        (OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual
          (q.translatedLineBundle A j)).sheaf) :=
  pullbackEvaluationKernelDualIso q.map.hom.left R i p w h ≪≫
    q.dualPullbackPushforwardSplitting A

/-- A locally split genuine presentation yields the paper's first-kernel splitting. -/
def presentationKernelSplitting_of_locallySplit {m : ℕ}
    (A : Line.Bundles.LineBundle D.scheme.left)
    (R : Line.Bundles.LineBundle q.target.scheme.left)
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (p : DualEvaluation.freeSheaf m ⟶ q.linePushforward A) (w : i ≫ p = 0)
    (h : IsColimit (CokernelCofork.ofπ p w))
    {I : Type} (U : I → q.target.scheme.left.Opens) (hU : iSup U = ⊤)
    (hsplit : ∀ j, IsSplitEpi
      ((Scheme.Modules.pullback (U j).ι).map (DualEvaluation.evaluation R i))) :
    (Scheme.Modules.pullback q.map.hom.left).obj (kernel (DualEvaluation.evaluation R i)) ≅
      ∐ (fun j : Multiplicative (ZMod n) =>
        (OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual
          (q.translatedLineBundle A j)).sheaf) :=
  pullbackEvaluationKernelDualIso_of_locallySplit q.map.hom.left R i p w h U hU hsplit ≪≫
    q.dualPullbackPushforwardSplitting A

/-- A genuine short exact line-to-free presentation of the finite-flat direct
    image has the claimed kernel splitting, with local projectivity checked
    on an affine cover. -/
def presentationKernelSplitting_of_affine_presentation {m : ℕ}
    (A : Line.Bundles.LineBundle D.scheme.left)
    (R : Line.Bundles.LineBundle q.target.scheme.left)
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (p : DualEvaluation.freeSheaf m ⟶ q.linePushforward A) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk i p w).ShortExact)
    {I : Type} (U : I → q.target.scheme.left.Opens) (hU : iSup U = ⊤)
    (haff : ∀ j, IsAffine (U j).toScheme)
    (hproj : ∀ j, Module.Projective Γ((U j).toScheme, ⊤)
      Γ((Scheme.Modules.restrictFunctor (U j).ι).obj (q.linePushforward A), ⊤)) :
    (Scheme.Modules.pullback q.map.hom.left).obj (kernel (DualEvaluation.evaluation R i)) ≅
      ∐ (fun j : Multiplicative (ZMod n) =>
        (OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual
          (q.translatedLineBundle A j)).sheaf) := by
  have : A.sheaf.IsQuasicoherent := A.isQuasicoherent
  have : (q.linePushforward A).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom q.map.hom.left
  exact q.presentationKernelSplitting_of_locallySplit A R i p w hS.gIsCokernel U hU
    (evaluation_locallySplit_of_affine_presentation R i p w hS U haff hproj)

end CyclicEtaleIsogeny
end SteinerGeometry
