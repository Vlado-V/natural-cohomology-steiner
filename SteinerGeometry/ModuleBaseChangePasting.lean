module

public import SteinerGeometry.ModuleBaseChange

set_option backward.privateInPublic true
@[expose] public section

/-! Canonical module base change commutes with composition of Cartesian squares. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace SteinerGeometry
universe u
variable {S X Y Z P Q : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ S} {g : Y ⟶ S} {c : Q ⟶ P} {d : Q ⟶ Z} {h : Z ⟶ Y}
theorem cartesianPushforwardIso_paste (H : IsPullback a b f g)
    (J : IsPullback c d b h) (M : Q.Modules) :
    (cartesianPushforwardIso H).hom.app ((Scheme.Modules.pushforward c).obj M) ≫
      (Scheme.Modules.pushforward g).map ((cartesianPushforwardIso J).hom.app M) ≫
      (Scheme.Modules.pushforwardComp h g).hom.app ((Scheme.Modules.pushforward d).obj M) =
    (Scheme.Modules.pushforward f).map ((Scheme.Modules.pushforwardComp c a).hom.app M) ≫
      (cartesianPushforwardIso (J.paste_horiz H)).hom.app M := by
  apply Scheme.Modules.hom_ext
  intro U
  simp only [cartesianPushforwardIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Category.id_comp, Category.comp_id,
    Scheme.Modules.pushforward_obj_presheaf_map]
  apply ConcreteCategory.hom_ext
  intro s
  change M.presheaf.map _ (M.presheaf.map _ s) = M.presheaf.map _ s
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  congr 2

theorem pullbackUnit_comp (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M ≫
      (Scheme.Modules.pushforward a).map
        ((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app ((Scheme.Modules.pullback a).obj M)) ≫
      (Scheme.Modules.pushforwardComp c a).hom.app
        ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback a).obj M)) ≫
      (Scheme.Modules.pushforward (c ≫ a)).map ((Scheme.Modules.pullbackComp c a).hom.app M) =
    (Scheme.Modules.pullbackPushforwardAdjunction (c ≫ a)).unit.app M := by
  have hu := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction a).comp (Scheme.Modules.pullbackPushforwardAdjunction c))
    (Scheme.Modules.pullbackPushforwardAdjunction (c ≫ a))
    (Scheme.Modules.pullbackComp c a).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at hu
  have hv := congrArg (fun k => k ≫ (Scheme.Modules.pushforward (c ≫ a)).map
    ((Scheme.Modules.pullbackComp c a).hom.app M)) hu
  simp only [Adjunction.comp_unit_app, Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app] at hv
  rw [(Scheme.Modules.pushforward (c ≫ a)).map_id] at hv
  exact hv.trans (Category.comp_id _)

theorem cartesianBaseChangeAdjoint_paste (H : IsPullback a b f g)
    (J : IsPullback c d b h) (M : X.Modules) :
    cartesianBaseChangeAdjoint H M ≫
      (Scheme.Modules.pushforward g).map
        (cartesianBaseChangeAdjoint J ((Scheme.Modules.pullback a).obj M)) ≫
      (Scheme.Modules.pushforwardComp h g).hom.app
        ((Scheme.Modules.pushforward d).obj
          ((Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback a).obj M))) ≫
      (Scheme.Modules.pushforward (h ≫ g)).map
        ((Scheme.Modules.pushforward d).map ((Scheme.Modules.pullbackComp c a).hom.app M)) =
    cartesianBaseChangeAdjoint (J.paste_horiz H) M := by
  let K := (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback a).obj M)
  let μ := (Scheme.Modules.pullbackComp c a).hom.app M
  let η := (Scheme.Modules.pullbackPushforwardAdjunction c).unit.app
    ((Scheme.Modules.pullback a).obj M)
  have he := (cartesianPushforwardIso H).hom.naturality η
  have hp := cartesianPushforwardIso_paste H J K
  have hn := (cartesianPushforwardIso (J.paste_horiz H)).hom.naturality μ
  simp only [Functor.comp_map] at he hn
  dsimp only [cartesianBaseChangeAdjoint]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% he, reassoc_of% hp]
  dsimp only [K, μ] at hn ⊢
  simp only [Functor.comp_obj] at hn
  rw [← hn]
  have hu := congrArg (fun k => (Scheme.Modules.pushforward f).map k ≫
    (cartesianPushforwardIso (J.paste_horiz H)).hom.app
      ((Scheme.Modules.pullback (c ≫ a)).obj M)) (pullbackUnit_comp (a := a) (c := c) M)
  simpa only [Functor.map_comp, Category.assoc] using hu

theorem pullbackCompositionHomEquiv {A B C : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (M : C.Modules) {N : A.Modules}
    (φ : (Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj M ⟶ N) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)).homEquiv M N
      ((Scheme.Modules.pullbackComp f g).inv.app M ≫ φ) =
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).homEquiv M N φ ≫
        (Scheme.Modules.pushforwardComp f g).hom.app N := by
  let adj₁ := (Scheme.Modules.pullbackPushforwardAdjunction g).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let adj₂ := Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g)
  have ht := unit_conjugateEquiv adj₁ adj₂ (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv] at ht
  calc
    _ = (adj₂.unit.app M ≫ (Scheme.Modules.pushforward (f ≫ g)).map
          ((Scheme.Modules.pullbackComp f g).inv.app M)) ≫
        (Scheme.Modules.pushforward (f ≫ g)).map φ := by
      rw [Adjunction.homEquiv_unit, Functor.map_comp, Category.assoc]
    _ = (adj₁.unit.app M ≫ (Scheme.Modules.pushforwardComp f g).hom.app
          ((Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback f).obj M)) ≫
        (Scheme.Modules.pushforward (f ≫ g)).map φ := by rw [← ht]
    _ = _ := by
      rw [Category.assoc, ← (Scheme.Modules.pushforwardComp f g).hom.naturality φ,
        ← Category.assoc]
      rfl

theorem cartesianBaseChange_paste (H : IsPullback a b f g)
    (J : IsPullback c d b h) (M : X.Modules) :
    (Scheme.Modules.pullbackComp h g).inv.app ((Scheme.Modules.pushforward f).obj M) ≫
      (Scheme.Modules.pullback h).map (cartesianBaseChange H M) ≫
      cartesianBaseChange J ((Scheme.Modules.pullback a).obj M) ≫
      (Scheme.Modules.pushforward d).map ((Scheme.Modules.pullbackComp c a).hom.app M) =
    cartesianBaseChange (J.paste_horiz H) M := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (h ≫ g)).homEquiv _ _).injective
  rw [pullbackCompositionHomEquiv, Adjunction.comp_homEquiv]
  change (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
    ((Scheme.Modules.pullbackPushforwardAdjunction h).homEquiv _ _ _) ≫ _ = _
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    cartesianBaseChange_normalization, Adjunction.homEquiv_naturality_right,
    cartesianBaseChange_normalization, cartesianBaseChange_normalization]
  simp only [Functor.map_comp, Category.assoc]
  have hn := (Scheme.Modules.pushforwardComp h g).hom.naturality
    ((Scheme.Modules.pushforward d).map ((Scheme.Modules.pullbackComp c a).hom.app M))
  simp only [Functor.comp_map] at hn
  rw [hn]
  exact cartesianBaseChangeAdjoint_paste H J M

end SteinerGeometry
