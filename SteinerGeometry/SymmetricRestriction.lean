module

public import SteinerGeometry.SectionTensorKernelGlobal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

set_option backward.privateInPublic true
@[expose] public section

/-! Explicit restriction compatibility of the monomial construction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
local instance symmetricRestrictionBiproducts (Z : Scheme.{u}) : HasFiniteBiproducts Z.Modules := HasFiniteBiproducts.of_hasFiniteProducts
private instance symmetricRestrictionRestrictionAdditive : (Scheme.Modules.restrictFunctor f).Additive where
  map_add := by intros; ext U x; rfl

/-- The literal restriction sheaf equipped with the pulled-back line-bundle structure. -/
def restrictionLineBundle (L : Line.Bundles.LineBundle Y) : Line.Bundles.LineBundle X where
  sheaf := L.sheaf.restrict f
  locallyTrivial x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := (L.pullback f).locallyTrivial x
    exact ⟨U, hx, ⟨(Scheme.Modules.pullback U.ι).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback f).app L.sheaf) ≪≫ e⟩⟩

/-- Finite biproducts commute with literal restriction, with fixed chosen biproducts. -/
def restrictBiproductIso {ι : Type} [Fintype ι] (G : ι → Y.Modules) :
    (⨁ G).restrict f ≅ ⨁ fun i => (G i).restrict f where
  hom := biproduct.lift (fun i => (Scheme.Modules.restrictFunctor f).map (biproduct.π G i))
  inv := biproduct.desc (fun i => (Scheme.Modules.restrictFunctor f).map (biproduct.ι G i))
  hom_inv_id := by
    rw [biproduct.lift_desc]
    simp only [← Functor.map_comp, ← Functor.map_sum, biproduct.total]
    exact (Scheme.Modules.restrictFunctor f).map_id _
  inv_hom_id := by
    classical
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      ← Functor.map_comp]
    by_cases h : i = j
    · subst j
      simp
    · simp [biproduct.ι_π_ne _ h]

/-- Restriction identifies the free monomial sheaf with the free monomial sheaf on the chart. -/
def freeMonomialRestrictIso (n d : ℕ) :
    (homogeneousFreeSheaf (X := Y) n d).restrict f ≅ homogeneousFreeSheaf (X := X) n d :=
  restrictBiproductIso f
      (fun _ : Sym (Fin (n+1)) d => Line.Bundles.structureModule Y) ≪≫
    biproduct.mapIso (fun _ => Scheme.Modules.restrictUnitIso f)

@[simp, reassoc] theorem freeMonomialRestrictIso_hom_π (n d : ℕ) (b : Sym (Fin (n+1)) d) :
    (freeMonomialRestrictIso f n d).hom ≫ biproduct.π _ b =
      (Scheme.Modules.restrictFunctor f).map (biproduct.π _ b) ≫
        (Scheme.Modules.restrictUnitIso f).hom := by
  simp only [freeMonomialRestrictIso, Iso.trans_hom, Category.assoc,
    biproduct.mapIso_hom, biproduct.map_π, restrictBiproductIso, biproduct.lift_π_assoc]

/-- Tensor coefficient multiplication commutes with actual restriction. -/
theorem tensorCoefficient_restrict (s : ℕ) (L : Fin s → Line.Bundles.LineBundle Y)
    (c : ∀ j, (L j).sheaf ⟶ Line.Bundles.structureModule Y) :
    (tensorFactorsRestrictIso f s (fun j => (L j).sheaf)).hom ≫
      (Scheme.Modules.restrictFunctor f).map (tensorCoefficient s (fun j => (L j).sheaf) c) ≫
      (Scheme.Modules.restrictUnitIso f).hom =
        tensorCoefficient s (fun j => (restrictionLineBundle f (L j)).sheaf)
          (fun j => (Scheme.Modules.restrictFunctor f).map (c j) ≫
            (Scheme.Modules.restrictUnitIso f).hom) := by
  apply tensorLineFactors_hom_ext s (fun j => restrictionLineBundle f (L j))
  intro U v
  change (f.appIso U).hom
    (structureMapValue (tensorCoefficient s (fun j => (L j).sheaf) c) (f ''ᵁ U)
      ((tensorFactorsRestrictIso f s (fun j => (L j).sheaf)).hom.app U
        (tensorGenerator s (fun j => (L j).sheaf.restrict f) U v))) = _
  rw [tensorFactorsRestrictIso_generator, tensorCoefficient_generator]
  change (f.appIso U).hom (∏ j, structureMapValue (c j) (f ''ᵁ U) (v j)) =
    structureMapValue (tensorCoefficient s (fun j => (restrictionLineBundle f (L j)).sheaf)
      (fun j => (Scheme.Modules.restrictFunctor f).map (c j) ≫
        (Scheme.Modules.restrictUnitIso f).hom)) U (tensorGenerator s _ U v)
  rw [tensorCoefficient_generator, map_prod]
  rfl

/-- Multiplication of the linear-form columns commutes with actual restriction. -/
theorem tensorMonomialMap_restrict {n s : ℕ} (L : Fin s → Line.Bundles.LineBundle Y)
    (c : ∀ j, Fin (n+1) → ((L j).sheaf ⟶ Line.Bundles.structureModule Y)) :
    (tensorFactorsRestrictIso f s (fun j => (L j).sheaf)).hom ≫
      (Scheme.Modules.restrictFunctor f).map (tensorMonomialMap (fun j => (L j).sheaf) c) ≫
      (freeMonomialRestrictIso f n s).hom =
        tensorMonomialMap (fun j => (restrictionLineBundle f (L j)).sheaf)
          (fun j i => (Scheme.Modules.restrictFunctor f).map (c j i) ≫
            (Scheme.Modules.restrictUnitIso f).hom) := by
  classical
  apply biproduct.hom_ext
  intro b
  simp only [Category.assoc, freeMonomialRestrictIso_hom_π]
  rw [← Category.assoc ((Scheme.Modules.restrictFunctor f).map
    (tensorMonomialMap (fun j => (L j).sheaf) c))
      ((Scheme.Modules.restrictFunctor f).map (biproduct.π _ b)),
    ← Functor.map_comp, tensorMonomialMap_component]
  simp only [Functor.map_sum, Preadditive.comp_sum, Preadditive.sum_comp]
  rw [tensorMonomialMap_component]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : wordMonomial w = b
  · simp only [ite_eq_left hw]
    exact tensorCoefficient_restrict f s L (fun j => c j (w j))
  · simp only [ite_eq_right hw, Functor.map_zero, comp_zero, zero_comp]

/-- The same naturality for columns presented as morphisms into the free linear-form sheaf. -/
theorem tensorMonomialMapOfColumns_restrict {n s : ℕ}
    (L : Fin s → Line.Bundles.LineBundle Y)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := Y) n 1) :
    (tensorFactorsRestrictIso f s (fun j => (L j).sheaf)).hom ≫
      (Scheme.Modules.restrictFunctor f).map (tensorMonomialMapOfColumns (fun j => (L j).sheaf) c) ≫
      (freeMonomialRestrictIso f n s).hom =
        tensorMonomialMapOfColumns (fun j => (restrictionLineBundle f (L j)).sheaf)
          (fun j => (Scheme.Modules.restrictFunctor f).map (c j) ≫
            (freeMonomialRestrictIso f n 1).hom) := by
  unfold tensorMonomialMapOfColumns
  rw [tensorMonomialMap_restrict]
  congr 1
  funext j i
  rw [Category.assoc, freeMonomialRestrictIso_hom_π, Functor.map_comp]
  rfl

/-- Restriction of one monomial line factor is the monomial of the restricted lines. -/
def monomialLineRestrictIso {m s : ℕ} (L : Fin m → Line.Bundles.LineBundle Y)
    (a : Sym (Fin m) s) :
    (monomialLineBundle L a).sheaf.restrict f ≅
      (monomialLineBundle (fun j => restrictionLineBundle f (L j)) a).sheaf :=
  (Scheme.Modules.restrictFunctor f).mapIso
      (eqToIso (tensorLineFactors_sheaf s (fun j => L (symmetricWord a j)))) ≪≫
    (tensorFactorsRestrictIso f s (fun j => (L (symmetricWord a j)).sheaf)).symm ≪≫
    (eqToIso (tensorLineFactors_sheaf s
      (fun j => restrictionLineBundle f (L (symmetricWord a j))))).symm

/-- All symmetric monomial line factors commute with actual restriction. -/
def splitMonomialSourceRestrictIso {m : ℕ} (L : Fin m → Line.Bundles.LineBundle Y) (s : ℕ) :
    (splitMonomialSource L s).restrict f ≅
      splitMonomialSource (fun j => restrictionLineBundle f (L j)) s :=
  restrictBiproductIso f
    (fun a : Sym (Fin m) s => (monomialLineBundle L a).sheaf) ≪≫
      biproduct.mapIso (monomialLineRestrictIso f L)

@[simp] theorem splitMonomialSourceRestrictIso_ι_inv {m s : ℕ}
    (L : Fin m → Line.Bundles.LineBundle Y) (a : Sym (Fin m) s) :
    biproduct.ι (fun a => (monomialLineBundle (fun j => restrictionLineBundle f (L j)) a).sheaf) a ≫
      (splitMonomialSourceRestrictIso f L s).inv =
        (monomialLineRestrictIso f L a).inv ≫
          (Scheme.Modules.restrictFunctor f).map
            (biproduct.ι (fun a => (monomialLineBundle L a).sheaf) a) := by
  change _ ≫ (biproduct.map (fun a => (monomialLineRestrictIso f L a).inv) ≫
    biproduct.desc (fun a => (Scheme.Modules.restrictFunctor f).map
      (biproduct.ι (fun a => (monomialLineBundle L a).sheaf) a))) = _
  rw [← Category.assoc, biproduct.ι_map, Category.assoc, biproduct.ι_desc]

private theorem monomialLineRestrictIso_inv_eq {m s : ℕ}
    (L : Fin m → Line.Bundles.LineBundle Y) (a : Sym (Fin m) s) :
    (monomialLineRestrictIso f L a).inv ≫ (Scheme.Modules.restrictFunctor f).map
      (eqToHom (tensorLineFactors_sheaf s (fun j => L (symmetricWord a j)))) =
        eqToHom (tensorLineFactors_sheaf s
          (fun j => restrictionLineBundle f (L (symmetricWord a j)))) ≫
          (tensorFactorsRestrictIso f s (fun j => (L (symmetricWord a j)).sheaf)).hom := by
  simp only [monomialLineRestrictIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, eqToIso.inv, eqToIso.hom, Category.assoc,
    ← Functor.map_comp, eqToHom_trans, eqToHom_refl]
  rw [(Scheme.Modules.restrictFunctor f).map_id]
  simp only [Category.comp_id]

/-- The global monomial morphism is compatible with restriction of its line factors and columns. -/
theorem splitMonomialMap_restrict {m n : ℕ} (L : Fin m → Line.Bundles.LineBundle Y)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := Y) n 1) (s : ℕ) :
    (splitMonomialSourceRestrictIso f L s).inv ≫
      (Scheme.Modules.restrictFunctor f).map (splitMonomialMap L c s) ≫
      (freeMonomialRestrictIso f n s).hom =
        splitMonomialMap (fun j => restrictionLineBundle f (L j))
          (fun j => (Scheme.Modules.restrictFunctor f).map (c j) ≫
            (freeMonomialRestrictIso f n 1).hom) s := by
  classical
  apply biproduct.hom_ext'
  intro a
  rw [← Category.assoc, splitMonomialSourceRestrictIso_ι_inv, Category.assoc,
    ← Functor.map_comp_assoc, splitMonomialMap_component, Functor.map_comp]
  rw [← Category.assoc, ← Category.assoc, monomialLineRestrictIso_inv_eq,
    Category.assoc, Category.assoc, tensorMonomialMapOfColumns_restrict,
    splitMonomialMap_component]

end SteinerGeometry
