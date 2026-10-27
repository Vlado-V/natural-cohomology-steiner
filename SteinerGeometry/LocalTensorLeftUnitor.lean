module

public import SteinerGeometry.LocalTensorFrames
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.RestrictedUnitTensorSection

set_option backward.privateInPublic true
@[expose] public section

/-! The left unitor acts on arbitrary local pure tensor sections. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SteinerGeometry.LocalTensorLeftUnitor
open CategoryTheory AlgebraicGeometry MonoidalCategory Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u

attribute [local instance] TwistPowers.MvPolynomial.instMonoidalCategoryModules_oAI

/-- The adjunction unit is an isomorphism on sections over the open being
restricted, so local identities may be checked after extension by direct image. -/
private theorem restrictAdjunction_unit_app_isIso {X : Scheme.{u}}
    (M : X.Modules) (U : X.Opens) :
    IsIso (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app U) := by
  have h := Scheme.Modules.Hom.isIso_iff_isIso_app.mp
    (LocalTensorFrames.restrict_unit_isIso M U) (⊤ : U.toScheme.Opens)
  change IsIso (((Scheme.Modules.restrictAdjunction U.ι).unit.app M).app
    (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) at h
  erw [Scheme.Opens.ι_image_top] at h
  exact h

/-- The local unit section tensored with any local section is sent back to
that section by the left unitor. No global extension of the section is assumed. -/
theorem leftUnitor_tensorSection {X : Scheme.{u}} (M : X.Modules)
    (U : X.Opens) (x : Γ(M, U)) :
    (λ_ M).hom.val.app (op U)
      (TensorSections.tensorSection (𝟙_ X.Modules) M U
        (PowerCancellationPairing.localMonoidalUnitSection X U) x) = x := by
  let A := (Scheme.Modules.pushforward U.ι).obj (M.restrict U.ι)
  let a : M ⟶ A := (Scheme.Modules.restrictAdjunction U.ι).unit.app M
  have : IsIso (a.app U) := restrictAdjunction_unit_app_isIso M U
  apply (AddCommGrpCat.mono_iff_injective (a.app U)).mp inferInstance
  let t := TensorSections.tensorSection (𝟙_ X.Modules) M U
    (PowerCancellationPairing.localMonoidalUnitSection X U) x
  have hn : (𝟙 (𝟙_ X.Modules) ⊗ₘ a) ≫ (λ_ A).hom = (λ_ M).hom ≫ a := by
    simpa only [id_tensorHom] using leftUnitor_naturality a
  have h := congrArg (fun k => k.val.app (op U) t) hn
  change (λ_ A).hom.val.app (op U)
      ((𝟙 (𝟙_ X.Modules) ⊗ₘ a).val.app (op U) t) =
    a.val.app (op U) ((λ_ M).hom.val.app (op U) t) at h
  dsimp only [t] at h
  rw [TensorFrameSections.tensorSection_map] at h
  change (λ_ A).hom.val.app (op U)
      (TensorSections.tensorSection (𝟙_ X.Modules) A U
        (PowerCancellationPairing.localMonoidalUnitSection X U)
        (a.val.app (op U) x)) =
    a.val.app (op U) ((λ_ M).hom.val.app (op U) t) at h
  have hx := LocalTensorFrames.unit_local_eq_extended M U x
  change a.val.app (op U) x = A.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (LocalTensorFrames.extended M U x) at hx
  rw [hx, RestrictedUnitTensorSection.leftUnitor_tensorSection_restrict] at h
  exact h.symm.trans hx.symm

end SteinerGeometry.LocalTensorLeftUnitor
