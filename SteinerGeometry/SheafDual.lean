import OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-! The actual sheaf dual, with its finite-direct-sum comparison. -/
noncomputable section
namespace SteinerGeometry.SheafDual
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.Picard.Homomorphisms
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}

local instance sheafDualBiproducts : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

abbrev dual (M : X.Modules) : X.Modules :=
  InternalHom.Construction.moduleInternalHom M (Line.Bundles.structureModule X)

def dualMap {M N : X.Modules} (f : M ⟶ N) : dual N ⟶ dual M :=
  InternalHomMaps.Construction.moduleInternalHomMap f (𝟙 _)

@[simp] theorem dualMap_id (M : X.Modules) : dualMap (𝟙 M) = 𝟙 (dual M) :=
  InternalHomMaps.Construction.moduleInternalHomMap_id _ _

@[simp] theorem dualMap_comp {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    dualMap (f ≫ g) = dualMap g ≫ dualMap f := by
  symm
  simpa only [dualMap, Category.id_comp] using
    InternalHomMaps.Construction.moduleInternalHomMap_comp g f (𝟙 _) (𝟙 _)

@[simp] theorem dualMap_zero (M N : X.Modules) : dualMap (0 : M ⟶ N) = 0 := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro a
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro s
  change a.val.app V 0 = 0
  exact map_zero _

@[simp] theorem dualMap_add {M N : X.Modules} (f g : M ⟶ N) :
    dualMap (f + g) = dualMap f + dualMap g := by
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.ext
  intro a
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply AddCommGrpCat.ext
  intro s
  change a.val.app V (f.app V.unop.left s + g.app V.unop.left s) =
    a.val.app V (f.app V.unop.left s) + a.val.app V (g.app V.unop.left s)
  exact map_add _ _ _

@[simp] theorem dualMap_sum {M N : X.Modules} {ι : Type*} (s : Finset ι)
    (f : ι → (M ⟶ N)) : dualMap (∑ i ∈ s, f i) = ∑ i ∈ s, dualMap (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, ih]

def dualIso {M N : X.Modules} (e : M ≅ N) : dual M ≅ dual N where
  hom := dualMap e.inv
  inv := dualMap e.hom
  hom_inv_id := by rw [← dualMap_comp, e.hom_inv_id, dualMap_id]
  inv_hom_id := by rw [← dualMap_comp, e.inv_hom_id, dualMap_id]

def dualBiproductIso {ι : Type} [Fintype ι] (M : ι → X.Modules) :
    dual (⨁ M) ≅ ⨁ (fun i => dual (M i)) where
  hom := biproduct.lift (fun i => dualMap (biproduct.ι M i))
  inv := biproduct.desc (fun i => dualMap (biproduct.π M i))
  hom_inv_id := by
    rw [biproduct.lift_desc]
    simp only [← dualMap_comp]
    rw [← dualMap_sum, biproduct.total, dualMap_id]
  inv_hom_id := by
    apply biproduct.hom_ext
    intro j
    apply biproduct.hom_ext'
    intro i
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc,
      ← dualMap_comp]
    by_cases h : i = j
    · subst j
      simp
    · rw [biproduct.ι_π_ne _ (Ne.symm h), dualMap_zero, Category.id_comp,
        biproduct.ι_π_ne _ h]

end SteinerGeometry.SheafDual
