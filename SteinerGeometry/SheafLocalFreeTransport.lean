module

public import SteinerGeometry.TildeFiniteProjective

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry.TildeFiniteProjective
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite Module
universe u

/-- Local freeness is invariant under an actual module-sheaf isomorphism. -/
theorem locallyFree_of_iso {X : Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) (hM : M.IsLocallyFree) : N.IsLocallyFree := by
  let D := hM.exists_isLocallyFreeData.choose
  have hD : D.IsLocallyFreeData := hM.exists_isLocallyFreeData.choose_spec
  have hU : iSup D.X = ⊤ := by
    simpa only [Opens.coversTop_iff, IsOpenCover] using D.coversTop
  apply KernelLocalFreeness.locallyFree_of_local_frames N D.X hU (fun i => (D.generators i).I)
  intro i
  letI : IsIso (D.generators i).π := hD.isIso i
  exact asIso (D.generators i).π ≪≫
    (SheafOfModules.overFunctor X.ringCatSheaf (D.X i)).mapIso e

/-- Convert an `over`-frame into a geometric pullback frame. -/
def pullbackFrameOfOver {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (Q : Type u)
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) Q ≅ M.over U) :
    (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free Q :=
  ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv U).app M).symm ≪≫
    (Scheme.Modules.overEquiv U).functor.mapIso e.symm ≪≫ overEquivFreeIso U Q

/-- Arbitrary scheme pullback preserves local freeness. -/
theorem locallyFree_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    (hM : M.IsLocallyFree) : ((Scheme.Modules.pullback f).obj M).IsLocallyFree := by
  let D := hM.exists_isLocallyFreeData.choose
  have hDfree : D.IsLocallyFreeData := hM.exists_isLocallyFreeData.choose_spec
  let U : D.I → X.Opens := fun i => f ⁻¹ᵁ D.X i
  have hD : TopologicalSpace.IsOpenCover D.X := by
    simpa only [Opens.coversTop_iff, IsOpenCover] using D.coversTop
  have hU : iSup U = ⊤ := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := hD.exists_mem (f x)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  apply KernelLocalFreeness.locallyFree_of_local_frames ((Scheme.Modules.pullback f).obj M)
    U hU (fun i => (D.generators i).I)
  intro i
  letI : IsIso (D.generators i).π := hDfree.isIso i
  let eU := pullbackFrameOfOver M (D.X i) (D.generators i).I (asIso (D.generators i).π)
  apply overFrameOfPullback ((Scheme.Modules.pullback f).obj M) (U i) (D.generators i).I
  exact (Scheme.Modules.pullbackComp (U i).ι f).app M ≪≫
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι f (D.X i)).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (f ∣_ D.X i) (Scheme.Opens.ι (X := Y) (D.X i))).app M).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ D.X i)).mapIso eU ≪≫
    pullbackFreeIso (f ∣_ D.X i) (D.generators i).I

/-- On an affine spectrum, a quasicoherent sheaf with a finite projective
module of global sections is locally free. -/
theorem locallyFree_of_spec_sections_projective {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent]
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj M)]
    [Module.Projective R ((moduleSpecΓFunctor (R := R)).obj M)] : M.IsLocallyFree := by
  let N := (moduleSpecΓFunctor (R := R)).obj M
  have hN : (tilde N).IsLocallyFree := tilde_locallyFree_of_finite_projective N
  have : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  exact locallyFree_of_iso (asIso M.fromTildeΓ) hN


end SteinerGeometry.TildeFiniteProjective
