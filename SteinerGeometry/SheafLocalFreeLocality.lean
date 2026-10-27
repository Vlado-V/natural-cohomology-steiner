import SteinerGeometry.SheafLocalFreeTransport

/-! # Gluing local freeness across an open cover -/
noncomputable section
namespace SteinerGeometry.TildeFiniteProjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Module
universe u

/-- A geometric open cover equipped with actual free pullback frames. -/
structure GeometricFrameCover {X : Scheme.{u}} (M : X.Modules) where
  I : Type u
  U : I → X.Opens
  covers : iSup U = ⊤
  Q : I → Type u
  frame : ∀ i, (Scheme.Modules.pullback (U i).ι).obj M ≅ SheafOfModules.free (Q i)

/-- Native locally-free data gives geometric free frames. -/
def geometricFramesOfLocallyFree {X : Scheme.{u}} (M : X.Modules)
    (hM : M.IsLocallyFree) : GeometricFrameCover M := by
  let D := hM.exists_isLocallyFreeData.choose
  have hD : D.IsLocallyFreeData := hM.exists_isLocallyFreeData.choose_spec
  refine ⟨D.I, D.X, ?_, fun i => (D.generators i).I, ?_⟩
  · simpa only [Opens.coversTop_iff, IsOpenCover] using D.coversTop
  · intro i
    letI : IsIso (D.generators i).π := hD.isIso i
    exact pullbackFrameOfOver M (D.X i) (D.generators i).I (asIso (D.generators i).π)

/-- Compose a free frame on a subopen with its containing open immersion. -/
def imagePullbackFrame {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (V : U.toScheme.Opens) (Q : Type u)
    (e : (Scheme.Modules.pullback V.ι).obj ((Scheme.Modules.pullback U.ι).obj M) ≅
      SheafOfModules.free Q) :
    (Scheme.Modules.pullback (U.ι ''ᵁ V).ι).obj M ≅ SheafOfModules.free Q := by
  let j := U.ι.isoImage V
  exact (Scheme.Modules.pullbackCongr (U.ι.isoImage_inv_ι V).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp j.inv (V.ι ≫ U.ι)).app M).symm ≪≫
    (Scheme.Modules.pullback j.inv).mapIso ((Scheme.Modules.pullbackComp V.ι U.ι).app M).symm ≪≫
    (Scheme.Modules.pullback j.inv).mapIso e ≪≫ pullbackFreeIso j.inv Q

/-- Geometric frames on a two-level open cover assemble to native local-freeness. -/
theorem locallyFree_of_openCover_frames {X : Scheme.{u}} (M : X.Modules)
    {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤)
    (D : ∀ i, GeometricFrameCover ((Scheme.Modules.pullback (U i).ι).obj M)) :
    M.IsLocallyFree := by
  let V : (Σ i, (D i).I) → X.Opens := fun s => (U s.1).ι ''ᵁ (D s.1).U s.2
  have hV : iSup V = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := (IsOpenCover.mk hU).exists_mem x
    let y : (U i).toScheme := ⟨x, hi⟩
    obtain ⟨j, hj⟩ := (IsOpenCover.mk (D i).covers).exists_mem y
    refine Opens.mem_iSup.mpr ⟨⟨i,j⟩, ?_⟩
    exact ⟨y, hj, rfl⟩
  apply KernelLocalFreeness.locallyFree_of_local_frames M V hV (fun s => (D s.1).Q s.2)
  intro s
  exact overFrameOfPullback M (V s) ((D s.1).Q s.2)
    (imagePullbackFrame M (U s.1) ((D s.1).U s.2) ((D s.1).Q s.2) ((D s.1).frame s.2))

/-- Local freeness is local for an arbitrary algebraic open cover. -/
theorem locallyFree_of_openCover {X : Scheme.{u}} (M : X.Modules)
    {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤)
    (h : ∀ i, ((Scheme.Modules.pullback (U i).ι).obj M).IsLocallyFree) :
    M.IsLocallyFree :=
  locallyFree_of_openCover_frames M U hU
    (fun i => geometricFramesOfLocallyFree _ (h i))

end SteinerGeometry.TildeFiniteProjective
