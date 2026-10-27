module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

set_option backward.privateInPublic true
@[expose] public section

/-! Natural transformations between additive functors respect finite direct sums. -/
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits
universe u v w u' v'

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A natural transformation which is invertible on each summand is invertible
on their finite biproduct. -/
theorem natTrans_isIso_biproduct
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (η : F ⟶ G)
    {ι : Type} [Fintype ι] (B : ι → C) (h : ∀ i, IsIso (η.app (B i))) :
    IsIso (η.app (⨁ B)) := by
  let (i : ι) := h i
  let : PreservesFiniteBiproducts F := Functor.preservesFiniteBiproductsOfAdditive F
  let : PreservesFiniteBiproducts G := Functor.preservesFiniteBiproductsOfAdditive G
  let eF : F.obj (⨁ B) ≅ (⨁ fun i => F.obj (B i)) :=
    biproduct.uniqueUpToIso _ (isBilimitOfPreserves F (biproduct.isBilimit B))
  let eG : G.obj (⨁ B) ≅ (⨁ fun i => G.obj (B i)) :=
    biproduct.uniqueUpToIso _ (isBilimitOfPreserves G (biproduct.isBilimit B))
  have eFπ (i : ι) : eF.hom ≫ biproduct.π (fun i => F.obj (B i)) i =
      F.map (biproduct.π B i) := biproduct.lift_π _ i
  have eGπ (i : ι) : eG.hom ≫ biproduct.π (fun i => G.obj (B i)) i =
      G.map (biproduct.π B i) := biproduct.lift_π _ i
  have he : η.app (⨁ B) ≫ eG.hom =
      eF.hom ≫ biproduct.map (fun i => η.app (B i)) := by
    apply biproduct.hom_ext
    intro i
    rw [Category.assoc, eGπ, Category.assoc, biproduct.map_π, ← Category.assoc, eFπ]
    exact (η.naturality (biproduct.π B i)).symm
  have heq : η.app (⨁ B) = eF.hom ≫
      (biproduct.mapIso (fun i => asIso (η.app (B i)))).hom ≫ eG.inv := by
    apply (cancel_mono eG.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id, biproduct.mapIso_hom, asIso_hom] using he
  rw [heq]
  infer_instance

/-- The same statement with the coproduct presentation of a finite free object. -/
theorem natTrans_isIso_finite_coproduct
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Preadditive C] [Preadditive D] [HasFiniteBiproducts C] [HasFiniteBiproducts D]
    (F G : C ⥤ D) [F.Additive] [G.Additive] (η : F ⟶ G)
    {ι : Type} [Fintype ι] (B : ι → C) [HasCoproduct B]
    (h : ∀ i, IsIso (η.app (B i))) : IsIso (η.app (∐ B)) := by
  have := natTrans_isIso_biproduct F G η B h
  let e := biproduct.isoCoproduct B
  have he := η.naturality e.hom
  have : IsIso (F.map e.hom ≫ η.app (∐ B)) := by
    rw [he]
    infer_instance
  exact (isIso_comp_left_iff (F.map e.hom) (η.app (∐ B))).mp inferInstance

end
end SteinerGeometry
