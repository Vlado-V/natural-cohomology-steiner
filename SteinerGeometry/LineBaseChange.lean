import SteinerGeometry.ModuleBaseChangePasting
import SteinerGeometry.AffineLineBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.CanonicalBaseChange
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Local.ModuleIsomorphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Cartesian.OpenRestriction

/-! Compatibility and localization of canonical base change for module sheaves. -/

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

namespace SteinerGeometry
universe u

variable {S X Y Z P Q : Scheme.{u}} {a : P ⟶ X} {b : P ⟶ Y}
  {f : X ⟶ S} {g : Y ⟶ S} {c : Q ⟶ P} {d : Q ⟶ Z} {h : Z ⟶ Y}

/-- The local adapter uses the same canonical adjunction mate as the library. -/
theorem cartesianBaseChange_eq (H : IsPullback a b f g) (M : X.Modules) :
    cartesianBaseChange H M = (SchemeModule.SchemeModuleBaseChange.map H).app M := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).injective
  rw [cartesianBaseChange_normalization]
  exact (Structure.BaseChangeMateIdentification.schemeModuleBaseChange_normalization H M).symm

theorem cartesianBaseChange_naturality (H : IsPullback a b f g)
    {M N : X.Modules} (k : M ⟶ N) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pushforward f).map k) ≫
      cartesianBaseChange H N = cartesianBaseChange H M ≫
        (Scheme.Modules.pushforward b).map ((Scheme.Modules.pullback a).map k) := by
  simp only [cartesianBaseChange_eq]
  exact (SchemeModule.SchemeModuleBaseChange.map H).naturality k

/-- Restricting the base to an open is an invertible instance of canonical base change. -/
theorem openCartesianBaseChange_isIso (f : X ⟶ S) (U : S.Opens) (M : X.Modules) :
    IsIso (cartesianBaseChange (isPullback_morphismRestrict f U).flip M) := by
  rw [cartesianBaseChange_eq]
  exact Open.CanonicalBaseChange.openModuleBaseChange_isIso f U M

/-- Equality of the boundary morphisms is the only choice in a Cartesian square. -/
theorem cartesianBaseChange_isIso_congr
    {a' : P ⟶ X} {g' : Y ⟶ S} (H : IsPullback a b f g)
    (H' : IsPullback a' b f g') (ha : a = a') (hg : g = g') (M : X.Modules) :
    IsIso (cartesianBaseChange H M) ↔ IsIso (cartesianBaseChange H' M) := by
  subst a'
  subst g'
  rfl

/-- For affine horizontal maps, flat base change is invertible on the inverse
image of each affine open of the original base. -/
theorem lineBaseChange_preimage_isIso [IsAffineHom f] [IsAffineHom g] [Flat g]
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X)
    (U : S.Opens) (hU : IsAffineOpen U) :
    IsIso ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).map (cartesianBaseChange H L.sheaf)) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine (f ⁻¹ᵁ U).toScheme := hU.preimage f
  have : IsAffine (g ⁻¹ᵁ U).toScheme := hU.preimage g
  let Ho := (isPullback_morphismRestrict f U).flip
  let Hl := Cartesian.OpenRestriction.restrictedCartesianSquare H U
  let Hb := (isPullback_morphismRestrict b (g ⁻¹ᵁ U)).flip
  have : Module.Flat Γ(U.toScheme, ⊤)
      (Affine.TensorSectionComparison.morphismGlobalAlgebra (g ∣_ U)) :=
    (g ∣_ U).flat_appTop
  have : IsIso (cartesianBaseChange Ho L.sheaf) :=
    openCartesianBaseChange_isIso f U L.sheaf
  have : IsIso (cartesianBaseChange Hl
      ((Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).obj L.sheaf)) :=
    affineLineBaseChange_isIso Hl (L.pullback (f ⁻¹ᵁ U).ι)
  have ho : IsIso (cartesianBaseChange (Hl.paste_horiz Ho) L.sheaf) := by
    rw [← cartesianBaseChange_paste Ho Hl L.sheaf]
    infer_instance
  have ho' : IsIso (cartesianBaseChange (Hb.paste_horiz H) L.sheaf) :=
    (cartesianBaseChange_isIso_congr (Hl.paste_horiz Ho) (Hb.paste_horiz H)
      (Cartesian.OpenRestriction.restrictedCartesianFirst_comp_ι H U)
      (morphismRestrict_ι g U) L.sheaf).mp ho
  have : IsIso (cartesianBaseChange Hb ((Scheme.Modules.pullback a).obj L.sheaf)) :=
    openCartesianBaseChange_isIso b (g ⁻¹ᵁ U) ((Scheme.Modules.pullback a).obj L.sheaf)
  have hc : IsIso
      ((Scheme.Modules.pullbackComp (g ⁻¹ᵁ U).ι g).inv.app
          ((Scheme.Modules.pushforward f).obj L.sheaf) ≫
        (Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).map (cartesianBaseChange H L.sheaf) ≫
        cartesianBaseChange Hb ((Scheme.Modules.pullback a).obj L.sheaf) ≫
        (Scheme.Modules.pushforward (b ∣_ (g ⁻¹ᵁ U))).map
          ((Scheme.Modules.pullbackComp (b ⁻¹ᵁ (g ⁻¹ᵁ U)).ι a).hom.app L.sheaf)) := by
    rw [cartesianBaseChange_paste H Hb L.sheaf]
    exact ho'
  have hm : IsIso
      ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).map (cartesianBaseChange H L.sheaf) ≫
        cartesianBaseChange Hb ((Scheme.Modules.pullback a).obj L.sheaf) ≫
        (Scheme.Modules.pushforward (b ∣_ (g ⁻¹ᵁ U))).map
          ((Scheme.Modules.pullbackComp (b ⁻¹ᵁ (g ⁻¹ᵁ U)).ι a).hom.app L.sheaf)) :=
    (isIso_comp_left_iff _ _).mp hc
  exact (isIso_comp_right_iff _ _).mp hm

/-- Flat affine base change commutes with direct image of every line bundle. -/
theorem lineBaseChange_isIso [IsAffineHom f] [IsAffineHom g] [Flat g]
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) :
    IsIso (cartesianBaseChange H L.sheaf) := by
  apply Local.ModuleIsomorphisms.moduleMap_isIso_of_locally
  intro y
  obtain ⟨_, ⟨U : S.Opens, hU, rfl⟩, hy, _⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (g y)) isOpen_univ
  exact ⟨g ⁻¹ᵁ U, hy, lineBaseChange_preimage_isIso H L U hU⟩

/-- The actual line-bundle direct-image base-change isomorphism. -/
def lineBaseChangeIso [IsAffineHom f] [IsAffineHom g] [Flat g]
    (H : IsPullback a b f g) (L : Line.Bundles.LineBundle X) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj L.sheaf) ≅
      (Scheme.Modules.pushforward b).obj ((Scheme.Modules.pullback a).obj L.sheaf) := by
  have := lineBaseChange_isIso H L
  exact asIso (cartesianBaseChange H L.sheaf)

end SteinerGeometry
