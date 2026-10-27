import SteinerGeometry.AffineLocalFreeness
import SteinerGeometry.SheafLocalFreeLocality
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.BaseChangeMate
import SteinerGeometry.LinePushforwardProjective
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Local freeness of a finite-flat line-bundle direct image on affine bases -/
noncomputable section
namespace SteinerGeometry

open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

/-- The direct image of an actual line bundle by a finite flat map of affine
schemes is locally free over a locally Noetherian base. -/
theorem affineLinePushforward_locallyFree
    {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f] (L : Line.Bundles.LineBundle Y) :
    ((Scheme.Modules.pushforward f).obj L.sheaf).IsLocallyFree := by
  have : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  have : ((Scheme.Modules.pushforward f).obj L.sheaf).IsQuasicoherent :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_pushforward_of_isAffineHom f
  obtain ⟨hfin, hproj⟩ := affineLinePushforward_sections_projective f L
  let := hfin
  let := hproj
  exact TildeFiniteProjective.locallyFree_of_affine_sections_projective X _


/-- Direct image restricted to an open agrees with direct image of the
restricted line bundle, through the actual open-base-change isomorphism. -/
def linePushforwardOpenIso {X Y : Scheme.{u}} (f : Y ⟶ X)
    (L : Line.Bundles.LineBundle Y) (U : X.Opens) :
    (Scheme.Modules.pullback U.ι).obj ((Scheme.Modules.pushforward f).obj L.sheaf) ≅
      (Scheme.Modules.pushforward (f ∣_ U)).obj (L.pullback (f ⁻¹ᵁ U).ι).sheaf := by
  letI : IsIso (OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap f U) :=
    OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap_isIso f U
  exact ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).symm ≪≫
    asIso ((OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap f U).app L.sheaf) ≪≫
    (Scheme.Modules.pushforward (f ∣_ U)).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app L.sheaf)

/-- Over an arbitrary locally Noetherian base, finite flat direct image of
an actual line bundle is locally free. -/
theorem linePushforward_locallyFree
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f] (L : Line.Bundles.LineBundle Y) :
    ((Scheme.Modules.pushforward f).obj L.sheaf).IsLocallyFree := by
  apply TildeFiniteProjective.locallyFree_of_openCover
    ((Scheme.Modules.pushforward f).obj L.sheaf)
    (fun U : X.affineOpens => (U : X.Opens)) (iSup_affineOpens_eq_top X)
  intro U
  let : IsAffine U.1.toScheme := U.2
  let : IsAffine (f ⁻¹ᵁ U.1).toScheme := U.2.preimage f
  have h := affineLinePushforward_locallyFree (f ∣_ U.1) (L.pullback (f ⁻¹ᵁ U.1).ι)
  exact TildeFiniteProjective.locallyFree_of_iso (linePushforwardOpenIso f L U.1).symm h

end SteinerGeometry
