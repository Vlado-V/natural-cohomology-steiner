import SteinerGeometry.ModuleBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Flat.BundleSectionBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PullbackSectionValues
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.QuasicoherentPullback
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.Image
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleSectionIdentity

/-! Flat affine base change for actual line-bundle direct images. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open scoped ChangeOfRings

namespace SteinerGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
  {f : X ⟶ S} {g : Y ⟶ S}

theorem cartesianBaseChange_tmul [IsAffine S] [IsAffine Y]
    (H : IsPullback a b f g) (M : X.Modules)
    [((Scheme.Modules.pushforward f).obj M).IsQuasicoherent]
    (r : Γ(Y, ⊤)) (s : Γ(M, ⊤)) :
    (cartesianBaseChange H M).app ⊤
        ((Affine.GeometricSections.AffineGeometricSections.iso g
          ((Scheme.Modules.pushforward f).obj M)).hom.hom
            (r ⊗ₜ[Γ(S, ⊤), g.appTop.hom] s)) =
      r • (show Γ((Scheme.Modules.pushforward b).obj
        ((Scheme.Modules.pullback a).obj M), ⊤) from
          ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ s) := by
  erw [Affine.PullbackSectionValues.affinePullbackSections_map_tmul,
    cartesianBaseChange_normalization, cartesianBaseChangeAdjoint_app_top]

theorem affineLineBaseChange_appTop_bijective [IsAffine S] [IsAffine X] [IsAffine Y]
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)] :
    Function.Bijective ((cartesianBaseChange H L.sheaf).app ⊤) := by
  letI : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  letI : ((Scheme.Modules.pushforward f).obj L.sheaf).IsQuasicoherent :=
    Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f L.sheaf
  letI := g.appTop.hom.toAlgebra
  let e := Affine.GeometricSections.AffineGeometricSections.iso g
    ((Scheme.Modules.pushforward f).obj L.sheaf)
  let l := (e.hom ≫ (Affine.SectionAdjunction.AffineSectionAdjunction.sections Y).map
    (cartesianBaseChange H L.sheaf)).hom
  let β := (Cartesian.ModuleTensorComparison.baseChangeModuleTensorComparison H L.sheaf).app
    (.op ⊤)
  let c := Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso f.appTop.hom L.sheaf
  let dom := TensorProduct.congr
    (LinearEquiv.refl Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)) c
  let cod := Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso f.appTop.hom
    ((Scheme.Modules.pushforward a).obj ((Scheme.Modules.pullback a).obj L.sheaf))
  have hl : (fun t => l (dom t)) = (fun t => cod (β t)) := by
    funext t
    induction t using TensorProduct.inductionOn with
    | tmul r s =>
      rw [TensorProduct.congr_tmul]
      change (cartesianBaseChange H L.sheaf).app ⊤
        (e.hom.hom (r ⊗ₜ[Γ(S, ⊤)] (c s))) = cod (β (r ⊗ₜ[Γ(S, ⊤)] s))
      rw [cartesianBaseChange_tmul]
      change b.appTop r •
        (show Γ((Scheme.Modules.pullback a).obj L.sheaf, ⊤) from
          (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app L.sheaf).app ⊤ s)) =
        (show Γ(P, ⊤) from
          P.presheaf.map (homOfLE (show a ⁻¹ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op
            (b.appTop r)) •
        (show Γ((Scheme.Modules.pullback a).obj L.sheaf, ⊤) from
          (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app L.sheaf).app ⊤ s))
      congr 1
      have hid : homOfLE (show a ⁻¹ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top) = 𝟙 _ :=
        Subsingleton.elim _ _
      rw [hid, CategoryTheory.op_id]
      erw [P.presheaf.map_id]
      rfl
    | add t t' ht ht' =>
      simp only [map_add, ht, ht']
  have hbij : Function.Bijective l := by
    apply (Function.Bijective.of_comp_iff l dom.bijective).mp
    change Function.Bijective (fun t => l (dom t))
    rw [hl]
    exact cod.bijective.comp
      (Flat.BundleSectionBaseChange.flat_lineBundleTensorComparison_bijective H L)
  exact (Function.Bijective.of_comp_iff ((cartesianBaseChange H L.sheaf).app ⊤)
    e.toLinearEquiv.bijective).mp hbij

theorem affineLineBaseChange_isIso [IsAffine S] [IsAffine X] [IsAffine Y]
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)] :
    IsIso (cartesianBaseChange H L.sheaf) := by
  letI : IsAffine P := .of_isPullback H
  letI : L.sheaf.IsQuasicoherent := L.isQuasicoherent
  letI : ((Scheme.Modules.pushforward f).obj L.sheaf).IsQuasicoherent :=
    Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent f L.sheaf
  letI : ((Scheme.Modules.pullback g).obj
      ((Scheme.Modules.pushforward f).obj L.sheaf)).IsQuasicoherent :=
    Affine.QuasicoherentPullback.affine_pullback_quasicoherent g _
  letI : ((Scheme.Modules.pullback a).obj L.sheaf).IsQuasicoherent :=
    (L.pullback a).isQuasicoherent
  letI : ((Scheme.Modules.pushforward b).obj
      ((Scheme.Modules.pullback a).obj L.sheaf)).IsQuasicoherent :=
    Quasicoherent.Image.quasiCompact_separated_directImage_quasicoherent b _
  apply Affine.ModuleGlobalSectionsIsomorphism.affineModule_isIso_of_globalSections_isIso
    (cartesianBaseChange H L.sheaf)
  rw [ConcreteCategory.isIso_iff_bijective]
  exact affineLineBaseChange_appTop_bijective H L

def affineLineBaseChangeIso [IsAffine S] [IsAffine X] [IsAffine Y]
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    [Module.Flat Γ(S, ⊤) (Affine.TensorSectionComparison.morphismGlobalAlgebra g)] :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj L.sheaf) ≅
      (Scheme.Modules.pushforward b).obj ((Scheme.Modules.pullback a).obj L.sheaf) := by
  haveI := affineLineBaseChange_isIso H L
  exact asIso (cartesianBaseChange H L.sheaf)

end SteinerGeometry
