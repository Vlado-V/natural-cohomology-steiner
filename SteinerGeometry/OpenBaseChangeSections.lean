import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.OpenModule.BaseChangeMate
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.RestrictedSectionBases

/-! The open base-change map is ordinary restriction on actual sections. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

namespace SteinerGeometry
universe u
variable {X Y : Scheme.{u}}

theorem moduleRestrictTopIso_natural {M N : X.Modules} (φ : M ⟶ N)
    (U : X.Opens) (s : Γ(M.restrict U.ι, ⊤)) :
    (Open.RestrictedSectionBases.moduleRestrictTopIso N U).hom
        (((Scheme.Modules.restrictFunctor U.ι).map φ).app ⊤ s) =
      φ.app U ((Open.RestrictedSectionBases.moduleRestrictTopIso M U).hom s) := by
  change N.presheaf.map (eqToHom U.ι_image_top.symm).op (φ.app (U.ι ''ᵁ ⊤) s) =
    φ.app U (M.presheaf.map (eqToHom U.ι_image_top.symm).op s)
  exact (ConcreteCategory.congr_hom
    (φ.mapPresheaf.naturality (eqToHom U.ι_image_top.symm).op) s).symm

set_option backward.isDefEq.respectTransparency false in
theorem openBaseChangeMap_top_value (f : X ⟶ Y) (U : Y.Opens) (M : X.Modules)
    (s : Γ(((Scheme.Modules.pushforward f).obj M).restrict U.ι, ⊤)) :
    (Open.RestrictedSectionBases.moduleRestrictTopIso M (f ⁻¹ᵁ U)).hom
        (((OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap f U).app M).app ⊤ s) =
      (Open.RestrictedSectionBases.moduleRestrictTopIso
        ((Scheme.Modules.pushforward f).obj M) U).hom s := by
  simp only [OpenModule.BaseChangeMate.OpenPullbackSquare.openBaseChangeMap_app,
    Scheme.Modules.Hom.comp_app,
    OpenModule.BaseChangeMate.OpenPullbackSquare.restrict_map_app,
    Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app,
    Scheme.Modules.restrictAdjunction_counit_app_app,
    OpenModule.BaseChangeMate.OpenPullbackSquare.pushforwardSquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app]
  change M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ (M.presheaf.map _ s))) =
    M.presheaf.map _ s
  simp only [← CategoryTheory.Functor.map_comp_apply]
  congr 1

end SteinerGeometry
