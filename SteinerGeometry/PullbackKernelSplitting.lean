module

public import SteinerGeometry.SheafDualKernel
public import SteinerGeometry.DualEvaluation
public import SteinerGeometry.CyclicLinePushforward

set_option backward.privateInPublic true
@[expose] public section

/-! The dual of a presented quotient and its splitting on the cyclic cover. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

local instance pullbackKernelSplittingBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

namespace SheafDual

/-- Finite direct sums of sheaf duals are the sheaf dual of the direct sum. -/
def dualCoproductIso {X : Scheme} {I : Type} [Fintype I] (M : I → X.Modules) :
    dual (∐ M) ≅ ∐ (fun i => dual (M i)) :=
  dualIso (biproduct.isoCoproduct M).symm ≪≫ dualBiproductIso M ≪≫
    biproduct.isoCoproduct (fun i => dual (M i))

end SheafDual

/-- Dualizing a genuine presentation identifies the evaluation kernel with
    the actual internal-Hom dual of its quotient. -/
def presentationKernelDualIso {X : Scheme} {m : ℕ} (R : Line.Bundles.LineBundle X)
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m) {Q : X.Modules}
    (p : DualEvaluation.freeSheaf m ⟶ Q) (w : i ≫ p = 0)
    (h : IsColimit (CokernelCofork.ofπ p w)) :
    kernel (DualEvaluation.evaluation R i) ≅ SheafDual.dual Q :=
  DualEvaluation.kernelIso R i ≪≫ (SheafDual.dualCokernelIso i p w h).symm

/-- Pullback of that actual kernel retains the presented quotient's dual. -/
def pullbackPresentationKernelDualIso {X Y : Scheme} (f : Y ⟶ X) {m : ℕ}
    (R : Line.Bundles.LineBundle X) (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    {Q : X.Modules} (p : DualEvaluation.freeSheaf m ⟶ Q) (w : i ≫ p = 0)
    (h : IsColimit (CokernelCofork.ofπ p w)) :
    (Scheme.Modules.pullback f).obj (kernel (DualEvaluation.evaluation R i)) ≅
      (Scheme.Modules.pullback f).obj (SheafDual.dual Q) :=
  (Scheme.Modules.pullback f).mapIso (presentationKernelDualIso R i p w h)

namespace CyclicEtaleIsogeny
variable {S : Scheme} {D : Abelian.Schemes.AbelianScheme 1 S} {n : ℕ}
    (q : CyclicEtaleIsogeny D n) [NeZero n]

/-- Dualizing the actual line splitting gives its finite sum of inverse line bundles. -/
def dualPullbackPushforwardSplitting (A : Line.Bundles.LineBundle D.scheme.left) :
    SheafDual.dual ((Scheme.Modules.pullback q.map.hom.left).obj (q.linePushforward A)) ≅
      ∐ (fun i : Multiplicative (ZMod n) =>
        (LineBundleDual.Construction.lineBundleDual (q.translatedLineBundle A i)).sheaf) :=
  SheafDual.dualIso (q.pullbackPushforwardSplitting A) ≪≫
    SheafDual.dualCoproductIso (fun i : Multiplicative (ZMod n) =>
      (q.translatedLineBundle A i).sheaf)

/-- A dual-base-change identification transports the genuine evaluation
kernel to the inverse line summands on the cyclic cover. -/
def presentationKernelSplittingOfDualBaseChange {m : ℕ}
    (A : Line.Bundles.LineBundle D.scheme.left)
    (R : Line.Bundles.LineBundle q.target.scheme.left)
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (p : DualEvaluation.freeSheaf m ⟶ q.linePushforward A) (w : i ≫ p = 0)
    (h : IsColimit (CokernelCofork.ofπ p w))
    (e : (Scheme.Modules.pullback q.map.hom.left).obj (SheafDual.dual (q.linePushforward A)) ≅
      SheafDual.dual ((Scheme.Modules.pullback q.map.hom.left).obj (q.linePushforward A))) :
    (Scheme.Modules.pullback q.map.hom.left).obj (kernel (DualEvaluation.evaluation R i)) ≅
      ∐ (fun j : Multiplicative (ZMod n) =>
        (LineBundleDual.Construction.lineBundleDual (q.translatedLineBundle A j)).sheaf) :=
  pullbackPresentationKernelDualIso q.map.hom.left R i p w h ≪≫ e ≪≫
    q.dualPullbackPushforwardSplitting A

end CyclicEtaleIsogeny
end SteinerGeometry
