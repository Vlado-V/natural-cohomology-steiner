module

public import SteinerGeometry.LinePushforwardLocallyFree

set_option backward.privateInPublic true
@[expose] public section

/-! # Finite geometric frames from finite projective affine sections -/
noncomputable section
namespace SteinerGeometry.TildeFiniteProjective

open CategoryTheory AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

/-- A genuine geometric frame cover, with each frame of finite rank. -/
structure FiniteGeometricFrameCover {X : Scheme.{u}} (M : X.Modules)
    extends GeometricFrameCover M where
  finite : ∀ i, Finite (Q i)

def FiniteGeometricFrameCover.mapIso {X : Scheme.{u}} {M N : X.Modules}
    (D : FiniteGeometricFrameCover M) (e : M ≅ N) : FiniteGeometricFrameCover N where
  I := D.I
  U := D.U
  covers := D.covers
  Q := D.Q
  frame i := (Scheme.Modules.pullback (D.U i).ι).mapIso e.symm ≪≫ D.frame i
  finite := D.finite

def finiteFramesTilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] : FiniteGeometricFrameCover (tilde M) where
  I := PrimeSpectrum R
  U p := PrimeSpectrum.basicOpen (chooseLocalBasis M p).scalar
  covers := by
    apply top_unique
    intro p _
    exact Opens.mem_iSup.mpr ⟨p, (chooseLocalBasis M p).not_mem⟩
  Q p := (chooseLocalBasis M p).Index
  frame p := basicOpenFreeTrivialization M _ _ (chooseLocalBasis M p).basis.repr
  finite p := (chooseLocalBasis M p).finite

def FiniteGeometricFrameCover.pullback {X Y : Scheme.{u}} {M : Y.Modules}
    (D : FiniteGeometricFrameCover M) (f : X ⟶ Y) :
    FiniteGeometricFrameCover ((Scheme.Modules.pullback f).obj M) where
  I := D.I
  U i := f ⁻¹ᵁ D.U i
  covers := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := (IsOpenCover.mk D.covers).exists_mem (f x)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  Q := D.Q
  frame i :=
    (Scheme.Modules.pullbackComp (f ⁻¹ᵁ D.U i).ι f).app M ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι f (D.U i)).symm).app M ≪≫
      ((Scheme.Modules.pullbackComp (f ∣_ D.U i) (D.U i).ι).app M).symm ≪≫
      (Scheme.Modules.pullback (f ∣_ D.U i)).mapIso (D.frame i) ≪≫
      pullbackFreeIso (f ∣_ D.U i) (D.Q i)
  finite := D.finite

/-- Finite frames on a cover assemble into a finite frame cover. -/
def finiteFramesOfOpenCover {X : Scheme.{u}} (M : X.Modules)
    {I : Type u} (U : I → X.Opens) (hU : iSup U = ⊤)
    (D : ∀ i, FiniteGeometricFrameCover ((Scheme.Modules.pullback (U i).ι).obj M)) :
    FiniteGeometricFrameCover M where
  I := Σ i, (D i).I
  U s := (U s.1).ι ''ᵁ (D s.1).U s.2
  covers := by
    apply top_unique
    intro x _
    obtain ⟨i, hi⟩ := (IsOpenCover.mk hU).exists_mem x
    let y : (U i).toScheme := ⟨x, hi⟩
    obtain ⟨j, hj⟩ := (IsOpenCover.mk (D i).covers).exists_mem y
    exact Opens.mem_iSup.mpr ⟨⟨i, j⟩, y, hj, rfl⟩
  Q s := (D s.1).Q s.2
  frame s := imagePullbackFrame M (U s.1) ((D s.1).U s.2)
    ((D s.1).Q s.2) ((D s.1).frame s.2)
  finite s := (D s.1).finite s.2

/-- Finite projective native affine sections give finite geometric frames. -/
def finiteFramesOfAffineSections (X : Scheme.{u}) [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent]
    [Module.Finite Γ(X, ⊤) Γ(M, ⊤)] [Module.Projective Γ(X, ⊤) Γ(M, ⊤)] :
    FiniteGeometricFrameCover M := by
  let A := (Affine.SectionAdjunction.AffineSectionAdjunction.sections X).obj M
  have : Module.Finite Γ(X, ⊤) A := inferInstanceAs (Module.Finite Γ(X, ⊤) Γ(M, ⊤))
  have : Module.Projective Γ(X, ⊤) A := inferInstanceAs (Module.Projective Γ(X, ⊤) Γ(M, ⊤))
  exact ((finiteFramesTilde A).pullback X.toSpecΓ).mapIso
    (Affine.SectionCounit.AffineSectionAdjunction.counitIso X M)

end SteinerGeometry.TildeFiniteProjective

namespace SteinerGeometry
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

/-- Actual finite local frames for a finite-flat line-bundle direct image. -/
def linePushforward_finiteFrames
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f] (L : Line.Bundles.LineBundle Y) :
    TildeFiniteProjective.FiniteGeometricFrameCover
      ((Scheme.Modules.pushforward f).obj L.sheaf) := by
  apply TildeFiniteProjective.finiteFramesOfOpenCover _
    (fun U : X.affineOpens => (U : X.Opens)) (iSup_affineOpens_eq_top X)
  intro U
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  let A := L.pullback (f ⁻¹ᵁ U.1).ι
  have : A.sheaf.IsQuasicoherent := A.isQuasicoherent
  have : ((Scheme.Modules.pushforward (f ∣_ U.1)).obj A.sheaf).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom (f ∣_ U.1)
  obtain ⟨hfin, hproj⟩ := affineLinePushforward_sections_projective (f ∣_ U.1) A
  let := hfin
  let := hproj
  exact (TildeFiniteProjective.finiteFramesOfAffineSections _ _).mapIso
    (linePushforwardOpenIso f L U.1).symm

end SteinerGeometry
