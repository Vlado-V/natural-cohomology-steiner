import SteinerGeometry.CyclicSubgroup
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.FunctionCoordinates
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.ConstantScheme.Morphisms
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Open.FunctionsBaseChange
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

namespace SteinerGeometry.ConstantKernelCharacters

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open OAI.AlgebraicGeometry.AbelianScheme.FrobeniusKernel.EtaleSubgroups.Construction

universe u
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1500000

variable (S : Scheme.{u}) (G : Type u) [Group G]

abbrev groupScheme := ConstantScheme.Iff.constantScheme S G

instance constantKernelGroup : GrpObj (groupScheme S G) :=
  inferInstanceAs (GrpObj (etaleGroupScheme S G).X)

/-- Constant labels as actual points of the constant group scheme. -/
def labelPointHom : G →* (𝟙_ (Over S) ⟶ groupScheme S G) :=
  (((etaleGroupPointIso S G).app (.op (𝟙_ (Over S)))).groupIsoToMulEquiv.symm).toMonoidHom.comp
    { toFun := LocallyConstant.const S
      map_one' := rfl
      map_mul' _ _ := rfl }

theorem labelPointHom_eq (g : G) :
    labelPointHom S G g = ConstantScheme.Morphisms.constantSchemeLabelPoint S G g := by
  apply ((etaleGroupPointIso S G).app (.op (𝟙_ (Over S)))).groupIsoToMulEquiv.injective
  exact (((etaleGroupPointIso S G).app (.op (𝟙_ (Over S)))).groupIsoToMulEquiv.apply_symm_apply
    (LocallyConstant.const S g)).trans (by
    change LocallyConstant.const S g =
      ConstantScheme.Iff.constantSchemePoint _ (ConstantScheme.Morphisms.constantSchemeLabelPoint S G g)
    apply LocallyConstant.ext
    intro s
    exact (ConstantScheme.Iff.constantSchemeIndex_ι g s).symm)
/-- The regular unit on the constant group carrying a scalar label character. -/
def characterUnit (χ : G →* Γ(S, ⊤)ˣ) : Γ((groupScheme S G).left, ⊤)ˣ :=
  Units.map (ConstantScheme.GlobalFunctions.constantSchemeGlobalRingIso S G).inv.hom.toMonoidHom
    { val := fun g => (χ g).val
      inv := fun g => (χ g).inv
      val_inv := funext fun g => (χ g).val_inv
      inv_val := funext fun g => (χ g).inv_val }

theorem characterUnit_label (χ : G →* Γ(S, ⊤)ˣ) (g : G) :
    Units.map (labelPointHom S G g).left.appTop.hom.toMonoidHom (characterUnit S G χ) = χ g := by
  rw [labelPointHom_eq]
  apply Units.ext
  have h := ConstantScheme.FunctionCoordinates.constantSchemeGlobalRingIso_apply S G
    (characterUnit S G χ).val g
  change (Sigma.ι (fun _ : G => S) g).appTop (characterUnit S G χ).val = (χ g).val
  rw [← h]
  exact congrFun (ConcreteCategory.congr_hom
    (ConstantScheme.GlobalFunctions.constantSchemeGlobalRingIso S G).inv_hom_id
    (fun g => (χ g).val)) g

/-- Pulling back the actual regular unit is functorial on every test scheme. -/
def value (χ : G →* Γ(S, ⊤)ˣ) (T : Over S) (x : T ⟶ groupScheme S G) : Γ(T.left, ⊤)ˣ :=
  Units.map x.left.appTop.hom (characterUnit S G χ)

theorem value_natural (χ : G →* Γ(S, ⊤)ˣ) {T U : Over S}
    (t : U ⟶ T) (x : T ⟶ groupScheme S G) :
    Units.map t.left.appTop.hom.toMonoidHom (value S G χ T x) = value S G χ U (t ≫ x) := by
  apply Units.ext
  change t.left.appTop (x.left.appTop _) = (t.left ≫ x.left).appTop _
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem value_constant (χ : G →* Γ(S, ⊤)ˣ) (T : Over S) (g : G) :
    value S G χ T (toUnit T ≫ labelPointHom S G g) = Units.map T.hom.appTop.hom (χ g) := by
  rw [← characterUnit_label S G χ g]
  apply Units.ext
  change (T.hom ≫ (labelPointHom S G g).left).appTop _ =
    T.hom.appTop ((labelPointHom S G g).left.appTop _)
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem point_eq_constant (T : Over S) (x : T ⟶ groupScheme S G) (g : G)
    (hx : ∀ z, ConstantScheme.Iff.constantSchemePoint T x z = g) :
    x = toUnit T ≫ labelPointHom S G g := by
  apply Over.OverMorphism.ext
  rw [labelPointHom_eq]
  change x.left = T.hom ≫ Sigma.ι (fun _ : G => S) g
  have h := ConstantScheme.Iff.constantScheme_factor x.left g hx
  rw [x.w] at h
  exact h

theorem value_one (χ : G →* Γ(S, ⊤)ˣ) (T : Over S) :
    value S G χ T 1 = 1 := by
  have h : (1 : T ⟶ groupScheme S G) = toUnit T ≫ labelPointHom S G 1 := by
    rw [map_one, MonObj.comp_one]
  rw [h, value_constant, map_one, map_one]

private theorem units_ext_on_fibers {T : Scheme.{u}} {I : Type u}
    (c : LocallyConstant T I) (a b : Γ(T, ⊤)ˣ)
    (h : ∀ i, Units.map (ConstantScheme.Iff.locallyConstantFiber c i).ι.appTop.hom.toMonoidHom a =
      Units.map (ConstantScheme.Iff.locallyConstantFiber c i).ι.appTop.hom.toMonoidHom b) : a = b := by
  apply Units.ext
  refine T.sheaf.eq_of_locally_eq' (fun i => ConstantScheme.Iff.locallyConstantFiber c i)
    ⊤ (fun i => (ConstantScheme.Iff.locallyConstantFiber c i).leTop) ?_ a.val b.val ?_
  · intro z _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨c z, rfl⟩
  · intro i
    let U := ConstantScheme.Iff.locallyConstantFiber c i
    have ha := ConcreteCategory.congr_hom (Open.FunctionsBaseChange.openInclusion_appTop_topIso U) a.val
    have hb := ConcreteCategory.congr_hom (Open.FunctionsBaseChange.openInclusion_appTop_topIso U) b.val
    exact ha.symm.trans ((congrArg (fun z => U.topIso.hom z.val) (h i)).trans hb)

theorem value_mul (χ : G →* Γ(S, ⊤)ˣ) (T : Over S)
    (x y : T ⟶ groupScheme S G) :
    value S G χ T (x * y) = value S G χ T x * value S G χ T y := by
  let cx := ConstantScheme.Iff.constantSchemePoint T x
  let cy := ConstantScheme.Iff.constantSchemePoint T y
  let c : LocallyConstant T.left (G × G) :=
    ⟨fun z => (cx z, cy z), cx.isLocallyConstant.prodMk cy.isLocallyConstant⟩
  apply units_ext_on_fibers c
  intro i
  let U := ConstantScheme.Iff.locallyConstantFiber c i
  let P : Over S := Over.mk (U.ι ≫ T.hom)
  let t : P ⟶ T := Over.homMk U.ι
  have hx : t ≫ x = toUnit P ≫ labelPointHom S G i.1 := by
    apply point_eq_constant
    intro z
    exact congrArg Prod.fst z.property
  have hy : t ≫ y = toUnit P ≫ labelPointHom S G i.2 := by
    apply point_eq_constant
    intro z
    exact congrArg Prod.snd z.property
  change Units.map t.left.appTop.hom.toMonoidHom (value S G χ T (x * y)) =
    Units.map t.left.appTop.hom.toMonoidHom (value S G χ T x * value S G χ T y)
  rw [map_mul, value_natural, value_natural, value_natural, MonObj.comp_mul, hx, hy,
    ← MonObj.comp_mul, ← (labelPointHom S G).map_mul, value_constant, value_constant,
    value_constant, map_mul, map_mul]

/-- The scalar character acts on all test-scheme points as a genuine monoid homomorphism. -/
def valueHom (χ : G →* Γ(S, ⊤)ˣ) (T : Over S) :
    (T ⟶ groupScheme S G) →* Γ(T.left, ⊤)ˣ where
  toFun := value S G χ T
  map_one' := value_one S G χ T
  map_mul' := value_mul S G χ T

/-- Transport the regular unit characters through an actual group-scheme isomorphism. -/
def transportedValue {K : Over S} [GrpObj K]
    (e : groupScheme S G ≅ K) [IsMonHom e.inv]
    (χ : G →* Γ(S, ⊤)ˣ) (T : Over S) : (T ⟶ K) →* Γ(T.left, ⊤)ˣ :=
  (valueHom S G χ T).comp (IsMonHom.monoidHom e.inv T)

theorem transportedValue_natural {K : Over S} [GrpObj K]
    (e : groupScheme S G ≅ K) [IsMonHom e.inv] (χ : G →* Γ(S, ⊤)ˣ)
    {T U : Over S} (t : U ⟶ T) (x : T ⟶ K) :
    Units.map t.left.appTop.hom.toMonoidHom (transportedValue S G e χ T x) =
      transportedValue S G e χ U (t ≫ x) := by
  exact (value_natural S G χ t (x ≫ e.inv)).trans
    (congrArg (value S G χ U) (Category.assoc t x e.inv).symm)

theorem transportedValue_injective {K : Over S} [GrpObj K]
    (e : groupScheme S G ≅ K) [IsMonHom e.inv] :
    Function.Injective (fun χ : G →* Γ(S, ⊤)ˣ => transportedValue S G e χ) := by
  intro χ ψ h
  apply MonoidHom.ext
  intro g
  have hg := congrArg (fun v => v (𝟙_ (Over S)) (labelPointHom S G g ≫ e.hom)) h
  change value S G χ (𝟙_ (Over S)) ((labelPointHom S G g ≫ e.hom) ≫ e.inv) =
    value S G ψ (𝟙_ (Over S)) ((labelPointHom S G g ≫ e.hom) ≫ e.inv) at hg
  rw [Category.assoc, e.hom_inv_id, Category.comp_id] at hg
  exact (characterUnit_label S G χ g).symm.trans
    (hg.trans (characterUnit_label S G ψ g))

end
end SteinerGeometry.ConstantKernelCharacters
