import SteinerGeometry.KernelPullbackFromFrames
import SteinerGeometry.TildeFiniteProjective
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.Frames

/-! # Pullback of kernels of epimorphisms onto finite sums of a line bundle -/
noncomputable section
namespace SteinerGeometry.KernelPullbackLineSum
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

local instance kernelPullbackLineSum_hasFiniteBiproducts (X : Scheme.{u}) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- The actual finite biproduct of copies of a line bundle. -/
abbrev lineSum {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (I : Type u) [Finite I] : X.Modules := ⨁ fun _ : I => L.sheaf

/-- A frame of the line bundle induces the actual free frame of its finite sum. -/
def lineSumFrame {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (I : Type u) [Finite I] (U : X.Opens)
    (e : (Scheme.Modules.pullback U.ι).obj L.sheaf ≅ Line.Bundles.structureModule U.toScheme) :
    (Scheme.Modules.pullback U.ι).obj (lineSum L I) ≅ SheafOfModules.free I := by
  let F := Scheme.Modules.pullback U.ι
  let : PreservesColimitsOfSize.{u, u} F :=
    (Scheme.Modules.pullbackPushforwardAdjunction U.ι).leftAdjoint_preservesColimits
  exact F.mapIso (biproduct.isoCoproduct (fun _ : I => L.sheaf)) ≪≫
    PreservesCoproduct.iso F (fun _ : I => L.sheaf) ≪≫ Sigma.mapIso (fun _ : I => e)

/-- Finite line sums are locally free, with the same affine frame cover as
the underlying line bundle. -/
theorem lineSum_locallyFree {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (I : Type u) [Finite I] : (lineSum L I).IsLocallyFree := by
  classical
  choose U hx hU e using L.exists_affine_frame
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  apply KernelLocalFreeness.locallyFree_of_local_frames (lineSum L I) U hcover (fun _ => I)
  intro x
  exact TildeFiniteProjective.overFrameOfPullback (lineSum L I) (U x) I
    (lineSumFrame L I (U x) (Classical.choice (e x)))

theorem lineSum_isQuasicoherent {X : Scheme.{u}} (L : Line.Bundles.LineBundle X)
    (I : Type u) [Finite I] : (lineSum L I).IsQuasicoherent := by
  let h := lineSum_locallyFree L I
  let q := h.exists_isLocallyFreeData.choose
  let : q.IsLocallyFreeData := h.exists_isLocallyFreeData.choose_spec
  exact q.quasiCoherentData.isQuasicoherent

/-- An arbitrary geometric pullback preserves the canonical kernel of
every quasicoherent epimorphism onto a finite sum of an actual line bundle.
No source frames or flatness hypothesis on the pullback are required. -/
theorem kernelComparison_isIso_of_epi_lineSum
    {X Y : Scheme.{u}} (f : Y ⟶ X) (L : Line.Bundles.LineBundle X)
    (I : Type u) [Finite I] {M : X.Modules} [M.IsQuasicoherent]
    (e : M ⟶ lineSum L I) [Epi e] :
    IsIso (kernelComparison e (Scheme.Modules.pullback f)) := by
  classical
  let : (lineSum L I).IsQuasicoherent := lineSum_isQuasicoherent L I
  choose U hx hU frame using L.exists_affine_frame
  have hcover : iSup U = ⊤ := by
    apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  exact KernelPullbackFromFrames.kernelComparison_isIso_of_epi_affine_target_frames f e U hcover
    (fun x => hU x) (fun _ => I) (fun _ => inferInstance)
    (fun x => lineSumFrame L I (U x) (Classical.choice (frame x)))

end SteinerGeometry.KernelPullbackLineSum
