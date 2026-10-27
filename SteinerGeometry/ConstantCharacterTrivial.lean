module

public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Constant.CharacterSheafSections

set_option backward.privateInPublic true
@[expose] public section

noncomputable section
namespace SteinerGeometry.ConstantCharacterTrivial
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
universe u

variable {K : Type u} [Field K] {S : Scheme.{u}}
    (c : K →+* Γ(S, ⊤)) (G : Type u) [CommGroup G] [Fintype G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (χ : G →* Kˣ) (hG : (Fintype.card G : K) ≠ 0)

/-- Evaluation at one component is an actual morphism of module sheaves. -/
def labelEvaluation (g : G) : Constant.StructureRepresentation.constantStructurePushforward S G ⟶
    Line.Bundles.structureModule S :=
  let i : Over.mk (𝟙 S) ⟶ ConstantScheme.Iff.constantScheme S G :=
    Over.homMk (Sigma.ι (fun _ : G => S) g) (ConstantScheme.Iff.constantScheme_ι_hom g)
  (Structure.PushforwardFunctor.structurePushforwardFunctor S).map i.op ≫
    (Scheme.Modules.pushforwardId S).hom.app (Line.Bundles.structureModule S)

omit [CommGroup G] [Fintype G] in
theorem labelEvaluation_app (g : G) (U : S.Opens)
    (s : Γ(Constant.StructureRepresentation.constantStructurePushforward S G, U)) :
    (labelEvaluation (S := S) G g).app U s =
      Constant.StructureSectionEquivalence.constantStructureSectionEquiv S G U s g := by
  let a := Sigma.ι (fun _ : G => S) g
  let f := (ConstantScheme.Iff.constantScheme S G).hom
  let h := Structure.PushforwardMorphism.overMorphism_preimage_le a (𝟙 S) f
    (ConstantScheme.Iff.constantScheme_ι_hom g) U
  have he : a.resLE (f ⁻¹ᵁ U) U h =
      Sigma.ι (fun _ : G => U.toScheme) g ≫
        (ConstantScheme.OpenFunctions.constantSchemeOpenIso S G U).hom := by
    apply (cancel_mono (f ⁻¹ᵁ U).ι).mp
    rw [Scheme.Hom.resLE_comp_ι, Category.assoc,
      ConstantScheme.OpenFunctions.constantSchemeOpenIso_label_inclusion]
  change (Structure.PushforwardMorphism.structurePushforwardOverMorphism a (𝟙 S) f
    (ConstantScheme.Iff.constantScheme_ι_hom g)).app U s = _
  rw [Structure.PushforwardMorphism.structurePushforwardOverMorphism_app]
  calc
    a.appLE (f ⁻¹ᵁ U) U h s =
        U.topIso.hom ((a.resLE (f ⁻¹ᵁ U) U h).appTop ((f ⁻¹ᵁ U).topIso.inv s)) := by
      rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
      simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
      exact congrArg (a.appLE (f ⁻¹ᵁ U) U h)
        (ConcreteCategory.congr_hom (f ⁻¹ᵁ U).topIso.inv_hom_id s).symm
    _ = U.topIso.hom ((Sigma.ι (fun _ : G => U.toScheme) g ≫
        (ConstantScheme.OpenFunctions.constantSchemeOpenIso S G U).hom).appTop
          ((f ⁻¹ᵁ U).topIso.inv s)) := by rw [he]
    _ = Constant.StructureSectionEquivalence.constantStructureSectionEquiv S G U s g := by
      rw [Scheme.Hom.comp_appTop]
      change U.topIso.hom ((Sigma.ι (fun _ : G => U.toScheme) g).appTop
        ((ConstantScheme.OpenFunctions.constantSchemeOpenIso S G U).hom.appTop
          ((f ⁻¹ᵁ U).topIso.inv s))) = _
      rw [← ConstantScheme.FunctionCoordinates.constantSchemeGlobalRingIso_apply]
      rfl

/-- The canonical rank-one coordinate is the inclusion followed by component evaluation. -/
def characterEvaluation : Constant.CharacterSheafSections.constantCharacterSheaf c G χ ⟶
    Line.Bundles.structureModule S :=
  IdempotentSheafSummands.idempotentSheafInclusion _ ≫ labelEvaluation G (1 : G)

theorem characterEvaluation_app (U : S.Opens)
    (s : Γ(Constant.CharacterSheafSections.constantCharacterSheaf c G χ, U)) :
    (characterEvaluation c G χ).app U s =
      Constant.CharacterSheafSections.constantCharacterSheafSectionsEquiv c G χ hG U s := by
  change (labelEvaluation (S := S) G (1 : G)).app U
    ((IdempotentSheafSummands.idempotentSheafInclusion _).app U s) = _
  rw [labelEvaluation_app]
  rfl

include hG in
theorem characterEvaluation_isIso : IsIso (characterEvaluation c G χ) := by
  have hcomp : ∀ U, IsIso (((Scheme.Modules.toPresheaf S).map (characterEvaluation c G χ)).app U) := by
    intro U
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun s => (characterEvaluation c G χ).app U.unop s)
    have he : (fun s => (characterEvaluation c G χ).app U.unop s) =
        Constant.CharacterSheafSections.constantCharacterSheafSectionsEquiv c G χ hG U.unop :=
      funext (characterEvaluation_app c G χ hG U.unop)
    rw [he]
    exact (Constant.CharacterSheafSections.constantCharacterSheafSectionsEquiv c G χ hG U.unop).bijective
  let _ := hcomp
  let _ := NatIso.isIso_of_isIso_app ((Scheme.Modules.toPresheaf S).map (characterEvaluation c G χ))
  exact isIso_of_reflects_iso (characterEvaluation c G χ) (Scheme.Modules.toPresheaf S)

def constantCharacterSheafIso : Constant.CharacterSheafSections.constantCharacterSheaf c G χ ≅
    Line.Bundles.structureModule S := by
  let _ := characterEvaluation_isIso c G χ hG
  exact asIso (characterEvaluation c G χ)

end SteinerGeometry.ConstantCharacterTrivial
