module

public import SteinerGeometry.LinePushforwardLocallyFree

set_option backward.privateInPublic true
@[expose] public section

/-! Finite projective sections on every affine chart of a finite-flat line direct image. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem linePushforward_affineRestriction_finite_projective
    {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Y ⟶ X) [IsFinite f] [Flat f] (L : Line.Bundles.LineBundle Y)
    (U : X.Opens) (hU : IsAffineOpen U) :
    Module.Finite Γ(U.toScheme, ⊤)
      Γ(((Scheme.Modules.pushforward f).obj L.sheaf).restrict U.ι, ⊤) ∧
    Module.Projective Γ(U.toScheme, ⊤)
      Γ(((Scheme.Modules.pushforward f).obj L.sheaf).restrict U.ι, ⊤) := by
  haveI : IsAffine U.toScheme := hU
  haveI : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  let A := L.pullback (f ⁻¹ᵁ U).ι
  obtain ⟨hfinite, hprojective⟩ := affineLinePushforward_sections_projective (f ∣_ U) A
  let e := ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app _).trans
    (linePushforwardOpenIso f L U)
  let E := ((Affine.SectionAdjunction.AffineSectionAdjunction.sections U.toScheme).mapIso e).toLinearEquiv
  haveI : Module.Finite Γ(U.toScheme, ⊤)
      ((Affine.SectionAdjunction.AffineSectionAdjunction.sections U.toScheme).obj
        ((Scheme.Modules.pushforward (f ∣_ U)).obj (L.pullback (f ⁻¹ᵁ U).ι).sheaf)) := hfinite
  haveI : Module.Projective Γ(U.toScheme, ⊤)
      ((Affine.SectionAdjunction.AffineSectionAdjunction.sections U.toScheme).obj
        ((Scheme.Modules.pushforward (f ∣_ U)).obj (L.pullback (f ⁻¹ᵁ U).ι).sheaf)) := hprojective
  exact ⟨Module.Finite.equiv E.symm, Module.Projective.of_equiv E.symm⟩

end SteinerGeometry
