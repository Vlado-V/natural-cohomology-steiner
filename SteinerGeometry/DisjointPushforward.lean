import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! Direct image over a disjoint open cover is the product of the direct images
of the component restrictions. This statement concerns actual module sheaves. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open TopologicalSpace Opposite

namespace SteinerGeometry

universe u

variable {X : Scheme.{u}} {ι : Type u}

def openComponent (V : ι → X.Opens) (M : X.Modules) (i : ι) : X.Modules :=
  (Scheme.Modules.pushforward (V i).ι).obj (M.restrict (V i).ι)

def disjointRestrictionMap (V : ι → X.Opens) (M : X.Modules) :
    M ⟶ ∏ᶜ (openComponent V M) :=
  Pi.lift (fun i => (Scheme.Modules.restrictAdjunction (V i).ι).unit.app M)

private def openComponentPart (V : ι → X.Opens) (U : X.Opens) (i : ι) : X.Opens :=
  (V i).ι ''ᵁ ((V i).ι ⁻¹ᵁ U)

private theorem openComponentPart_eq (V : ι → X.Opens) (U : X.Opens) (i : ι) :
    openComponentPart V U i = V i ⊓ U := by
  simp [openComponentPart, Scheme.Hom.image_preimage_eq_opensRange_inf]

private theorem openComponentPart_cover (V : ι → X.Opens) (hV : iSup V = ⊤)
    (U : X.Opens) : U ≤ ⨆ i, openComponentPart V U i := by
  intro x hx
  have hxV : x ∈ iSup V := hV.symm ▸ Set.mem_univ x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxV
  exact Opens.mem_iSup.mpr ⟨i, (openComponentPart_eq V U i).symm ▸ ⟨hi, hx⟩⟩

private theorem openComponentPart_disjoint (V : ι → X.Opens)
    (hV : _root_.Pairwise (fun i j => Disjoint (V i) (V j))) (U : X.Opens) :
    _root_.Pairwise (fun i j => Disjoint (openComponentPart V U i) (openComponentPart V U j)) := by
  intro i j hij
  exact (hV hij).mono (by rw [openComponentPart_eq]; exact inf_le_left)
    (by rw [openComponentPart_eq]; exact inf_le_left)

private theorem component_family_compatible (V : ι → X.Opens)
    (hV : _root_.Pairwise (fun i j => Disjoint (V i) (V j))) (M : X.Modules) (U : X.Opens)
    (s : ∀ i, Γ(M, openComponentPart V U i)) :
    TopCat.Presheaf.IsCompatible M.presheaf (openComponentPart V U) s := by
  intro i j
  by_cases h : i = j
  · subst j
    rfl
  · let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
    have hi : openComponentPart V U i ⊓ openComponentPart V U j = ⊥ :=
      disjoint_iff.mp (openComponentPart_disjoint V hV U h)
    have : Subsingleton (Γ(M, openComponentPart V U i ⊓ openComponentPart V U j)) :=
      AddCommGrpCat.subsingleton_of_isZero (F.isTerminalOfEqEmpty hi).isZero
    exact Subsingleton.elim _ _

/-- Sections on disjoint pieces glue uniquely to a section of the original sheaf. -/
theorem existsUnique_component_sections (V : ι → X.Opens) (hcover : iSup V = ⊤)
    (hdisjoint : _root_.Pairwise (fun i j => Disjoint (V i) (V j))) (M : X.Modules) (U : X.Opens)
    (s : ∀ i, Γ(openComponent V M i, U)) :
    ∃! t : Γ(M, U), ∀ i,
      ((Scheme.Modules.restrictAdjunction (V i).ι).unit.app M).app U t = s i := by
  let F : TopCat.Sheaf AddCommGrpCat X := ⟨M.presheaf, M.isSheaf⟩
  exact F.existsUnique_gluing' (openComponentPart V U) U
    (fun i => homOfLE ((V i).ι.image_preimage_le U))
    (openComponentPart_cover V hcover U) s
    (component_family_compatible V hdisjoint M U s)

private def componentSectionsIso (V : ι → X.Opens) (M : X.Modules) (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj (∏ᶜ (openComponent V M)) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op U)) (∀ i, (SheafOfModules.evaluation X.ringCatSheaf (op U)).obj
        (openComponent V M i)) :=
  PreservesProduct.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) (openComponent V M) ≪≫
    ModuleCat.piIsoPi _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem componentSectionsIso_coordinate (V : ι → X.Opens) (M : X.Modules)
    (U : X.Opens) (i : ι) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).map (disjointRestrictionMap V M) ≫
        (componentSectionsIso V M U).hom ≫ ModuleCat.ofHom (LinearMap.proj (R := X.ringCatSheaf.obj.obj (op U)) i) =
      (SheafOfModules.evaluation X.ringCatSheaf (op U)).map
        ((Scheme.Modules.restrictAdjunction (V i).ι).unit.app M) := by
  simp only [componentSectionsIso, Iso.trans_hom, Category.assoc,
    ModuleCat.piIsoPi_hom_ker_subtype, PreservesProduct.iso_hom, piComparison_comp_π]
  rw [← Functor.map_comp]
  simp [disjointRestrictionMap]

/-- The unit maps to restrictions on a disjoint open covering form an isomorphism. -/
theorem disjointRestrictionMap_isIso (V : ι → X.Opens) (hcover : iSup V = ⊤)
    (hdisjoint : _root_.Pairwise (fun i j => Disjoint (V i) (V j))) (M : X.Modules) :
    IsIso (disjointRestrictionMap V M) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let f := F.map (disjointRestrictionMap V M) ≫ (componentSectionsIso V M U).hom
  have hf (t : Γ(M, U)) (i : ι) :
      f t i = ((Scheme.Modules.restrictAdjunction (V i).ι).unit.app M).app U t := by
    exact ConcreteCategory.congr_hom (componentSectionsIso_coordinate V M U i) t
  have hfb : Function.Bijective f := by
    constructor
    · intro a b hab
      obtain ⟨t, ht, huniq⟩ := existsUnique_component_sections V hcover hdisjoint M U
        (fun i => ((Scheme.Modules.restrictAdjunction (V i).ι).unit.app M).app U a)
      have hb : ∀ i, ((Scheme.Modules.restrictAdjunction (V i).ι).unit.app M).app U b =
          ((Scheme.Modules.restrictAdjunction (V i).ι).unit.app M).app U a := by
        intro i
        rw [← hf b i, ← hf a i, hab]
      exact (huniq a (fun _ => rfl)).trans (huniq b hb).symm
    · intro s
      obtain ⟨t, ht, _⟩ := existsUnique_component_sections V hcover hdisjoint M U s
      exact ⟨t, funext (fun i => (hf t i).trans (ht i))⟩
  have : IsIso f := (ConcreteCategory.isIso_iff_bijective f).mpr hfb
  have : IsIso (F.map (disjointRestrictionMap V M)) :=
    (isIso_comp_right_iff _ (componentSectionsIso V M U).hom).mp this
  exact (forget₂ (ModuleCat (X.ringCatSheaf.obj.obj (op U))) AddCommGrpCat).map_isIso (F.map (disjointRestrictionMap V M))

/-- An actual module sheaf is the product of its direct images from disjoint components. -/
def disjointRestrictionIso (V : ι → X.Opens) (hcover : iSup V = ⊤)
    (hdisjoint : _root_.Pairwise (fun i j => Disjoint (V i) (V j))) (M : X.Modules) :
    M ≅ ∏ᶜ (openComponent V M) := by
  have := disjointRestrictionMap_isIso V hcover hdisjoint M
  exact asIso (disjointRestrictionMap V M)

private def isoPushforwardPullback {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules) :
    (Scheme.Modules.pushforward e.inv).obj M ≅ (Scheme.Modules.pullback e.hom).obj M := by
  let r : Scheme.Modules.restrictFunctor e.inv ⋙ Scheme.Modules.restrictFunctor e.hom ≅
      𝟭 X.Modules :=
    (Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫ Scheme.Modules.restrictFunctorId
  exact (r.app ((Scheme.Modules.pushforward e.inv).obj M)).symm ≪≫
    (Scheme.Modules.restrictFunctor e.hom).mapIso
      ((Scheme.Modules.restrictFunctorAdjCounitIso e.inv).app M) ≪≫
    (Scheme.Modules.restrictFunctorIsoPullback e.hom).app M

/-- A component projecting isomorphically to the base contributes exactly the
pullback along its section to the direct image. -/
def sectionComponentPushforwardIso {X Y : Scheme.{u}} (p : Y ⟶ X)
    (j : X ⟶ Y) [IsOpenImmersion j] (hj : j ≫ p = 𝟙 X) (M : Y.Modules) :
    (Scheme.Modules.pushforward p).obj
      ((Scheme.Modules.pushforward j.opensRange.ι).obj (M.restrict j.opensRange.ι)) ≅
        (Scheme.Modules.pullback j).obj M := by
  have hp : j.opensRange.ι ≫ p = j.isoOpensRange.inv := by
    rw [← j.isoOpensRange_inv_comp, Category.assoc, hj, Category.comp_id]
  exact (Scheme.Modules.pushforwardComp j.opensRange.ι p).app (M.restrict j.opensRange.ι) ≪≫
    (Scheme.Modules.pushforwardCongr hp).app (M.restrict j.opensRange.ι) ≪≫
    isoPushforwardPullback j.isoOpensRange (M.restrict j.opensRange.ι) ≪≫
    (Scheme.Modules.pullback j.isoOpensRange.hom).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback j.opensRange.ι).app M) ≪≫
    (Scheme.Modules.pullbackComp j.isoOpensRange.hom j.opensRange.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr j.isoOpensRange_hom_ι).app M

/-- The direct image of any module sheaf on a disjoint union of sections is
canonically the product of the sheaves pulled back along those sections. -/
def splitProjectionPushforwardIso {X Y : Scheme.{u}} (p : Y ⟶ X)
    (j : ι → (X ⟶ Y)) [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ i, j i ≫ p = 𝟙 X)
    (hcover : ⨆ i, (j i).opensRange = ⊤)
    (hdisjoint : _root_.Pairwise (fun i k => Disjoint (j i).opensRange (j k).opensRange))
    (M : Y.Modules) :
    (Scheme.Modules.pushforward p).obj M ≅
      ∏ᶜ (fun i => (Scheme.Modules.pullback (j i)).obj M) :=
  (Scheme.Modules.pushforward p).mapIso
      (disjointRestrictionIso (fun i => (j i).opensRange) hcover hdisjoint M) ≪≫
    PreservesProduct.iso (Scheme.Modules.pushforward p)
      (openComponent (fun i => (j i).opensRange) M) ≪≫
    Pi.mapIso (fun i => sectionComponentPushforwardIso p (j i) (hj i) M)

/-- For finitely many sheets, the product is also the categorical direct sum. -/
def splitProjectionPushforwardCoproductIso {X Y : Scheme.{u}} [Finite ι]
    (p : Y ⟶ X) (j : ι → (X ⟶ Y)) [∀ i, IsOpenImmersion (j i)]
    (hj : ∀ i, j i ≫ p = 𝟙 X)
    (hcover : ⨆ i, (j i).opensRange = ⊤)
    (hdisjoint : _root_.Pairwise (fun i k => Disjoint (j i).opensRange (j k).opensRange))
    (M : Y.Modules) :
    (Scheme.Modules.pushforward p).obj M ≅
      ∐ (fun i => (Scheme.Modules.pullback (j i)).obj M) := by
  let B := fun i => (Scheme.Modules.pullback (j i)).obj M
  letI : HasBiproduct B := HasBiproduct.of_hasProduct B
  exact splitProjectionPushforwardIso p j hj hcover hdisjoint M ≪≫
    (biproduct.isoProduct B).symm ≪≫ biproduct.isoCoproduct B

/-- Disjoint-union coordinates commute with an isomorphism of the total space. -/
def splitIsoProjectionPushforwardCoproductIso {X Y : Scheme.{u}} [Finite ι]
    (p : Y ⟶ X) (e : (∐ (fun _ : ι => X)) ≅ Y)
    (he : e.hom ≫ p = Sigma.desc (fun _ : ι => 𝟙 X)) (M : Y.Modules) :
    (Scheme.Modules.pushforward p).obj M ≅
      ∐ (fun i => (Scheme.Modules.pullback (Sigma.ι (fun _ : ι => X) i ≫ e.hom)).obj M) := by
  let j : ι → (X ⟶ Y) := fun i => Sigma.ι (fun _ : ι => X) i ≫ e.hom
  have hj (i : ι) : j i ≫ p = 𝟙 X := by
    simp [j, Category.assoc, he]
  have hcover : (⨆ i, (j i).opensRange) = ⊤ := by
    simp only [j, Scheme.Hom.opensRange_comp]
    have hc : (⨆ i, (Sigma.ι (fun _ : ι => X) i).opensRange) = ⊤ := by
      apply top_unique
      intro x _
      obtain ⟨⟨i, y⟩, rfl⟩ := (sigmaMk (fun _ : ι => X)).surjective x
      apply Opens.mem_iSup.mpr
      refine ⟨i, y, ?_⟩
      exact (sigmaMk_mk (fun _ : ι => X) i y).symm
    rw [← Scheme.Hom.image_iSup, hc,
      Scheme.Hom.image_top_eq_opensRange, Scheme.Hom.opensRange_of_isIso]
  have hdisjoint : _root_.Pairwise (fun i k => Disjoint (j i).opensRange (j k).opensRange) := by
    intro i k hik
    apply disjoint_iff.mpr
    apply le_bot_iff.mp
    intro y hy
    rcases hy.1 with ⟨x, hx⟩
    rcases hy.2 with ⟨z, hz⟩
    have heq : Sigma.ι (fun _ : ι => X) i x = Sigma.ι (fun _ : ι => X) k z := by
      apply e.hom.homeomorph.injective
      exact hx.trans hz.symm
    have h := (sigmaι_eq_iff (fun _ : ι => X) i k x z).mp heq
    exact (hik (congrArg Sigma.fst h)).elim
  exact splitProjectionPushforwardCoproductIso p j hj hcover hdisjoint M

/-- Base-changed direct image on a split self-pullback is the direct sum of
the inverse images along its deck maps. This is valid for every module sheaf. -/
def splitSelfFiberPushforwardIso {X Y : Scheme.{u}} [Finite ι] (f : X ⟶ Y)
    (e : (∐ (fun _ : ι => X)) ≅ pullback f f)
    (he : e.hom ≫ pullback.fst f f = Sigma.desc (fun _ : ι => 𝟙 X))
    (M : X.Modules) :
    (Scheme.Modules.pushforward (pullback.fst f f)).obj
      ((Scheme.Modules.pullback (pullback.snd f f)).obj M) ≅
    ∐ (fun i => (Scheme.Modules.pullback
      ((Sigma.ι (fun _ : ι => X) i ≫ e.hom) ≫ pullback.snd f f)).obj M) :=
  splitIsoProjectionPushforwardCoproductIso (pullback.fst f f) e he
      ((Scheme.Modules.pullback (pullback.snd f f)).obj M) ≪≫
    Sigma.mapIso (fun i => (Scheme.Modules.pullbackComp
      (Sigma.ι (fun _ : ι => X) i ≫ e.hom) (pullback.snd f f)).app M)

end SteinerGeometry
