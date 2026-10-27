module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Limits

set_option backward.privateInPublic true
@[expose] public section

/-! The adjunction-defined module base-change map, with its section
normalization. This is defined for actual scheme module sheaves. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SteinerGeometry
universe u

variable {S X Y P : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
  {f : X ⟶ S} {g : Y ⟶ S}

def cartesianPushforwardIso (H : IsPullback a b f g) :
    Scheme.Modules.pushforward a ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward b ⋙ Scheme.Modules.pushforward g :=
  Scheme.Modules.pushforwardComp a f ≪≫ Scheme.Modules.pushforwardCongr H.w ≪≫
    (Scheme.Modules.pushforwardComp b g).symm

def cartesianBaseChangeAdjoint (H : IsPullback a b f g) (M : X.Modules) :
    (Scheme.Modules.pushforward f).obj M ⟶
      (Scheme.Modules.pushforward g).obj
        ((Scheme.Modules.pushforward b).obj ((Scheme.Modules.pullback a).obj M)) :=
  (Scheme.Modules.pushforward f).map
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M) ≫
    (cartesianPushforwardIso H).hom.app ((Scheme.Modules.pullback a).obj M)

def cartesianBaseChange (H : IsPullback a b f g) (M : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward b).obj ((Scheme.Modules.pullback a).obj M) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
    (cartesianBaseChangeAdjoint H M)

@[simp] theorem cartesianBaseChange_normalization (H : IsPullback a b f g)
    (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        (cartesianBaseChange H M) = cartesianBaseChangeAdjoint H M :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).apply_symm_apply _

theorem cartesianBaseChangeAdjoint_app_top (H : IsPullback a b f g)
    (M : X.Modules) (s : Γ(M, ⊤)) :
    (cartesianBaseChangeAdjoint H M).app ⊤ s =
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ s := by
  simp only [cartesianBaseChangeAdjoint, cartesianPushforwardIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  change (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ ≫
    ((Scheme.Modules.pullback a).obj M).presheaf.map (𝟙 (Opposite.op (⊤ : P.Opens)))) s = _
  erw [CategoryTheory.Functor.map_id]
  rfl

end SteinerGeometry
