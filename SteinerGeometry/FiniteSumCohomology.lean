import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-! Vanishing under an actual finite direct-sum decomposition. -/

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SteinerGeometry

universe v u v' u' w
variable {C : Type u} [Category.{v} C] [Preadditive C]
  {D : Type u'} [Category.{v'} D] [Preadditive D]
  {ι : Type w} [Finite ι]

omit [Finite ι] in
theorem isZero_finite_biproduct (M : ι → D) [HasBiproduct M]
    (h : ∀ i, IsZero (M i)) : IsZero (⨁ M) := by
  rw [IsZero.iff_id_eq_zero]
  apply biproduct.hom_ext
  intro i
  exact (h i).eq_of_tgt _ _

set_option backward.isDefEq.respectTransparency false in
/-- An additive cohomology functor vanishes on a sheaf if an actual finite
direct-sum decomposition has vanishing cohomology on every summand. -/
theorem cohomology_vanishes_of_finite_split (F : C ⥤ D) [F.Additive]
    {E : C} (M : ι → C) [HasBiproduct M]
    (e : E ≅ ⨁ M) (h : ∀ i, IsZero (F.obj (M i))) : IsZero (F.obj E) := by
  let _ := Fintype.ofFinite ι
  have : PreservesBiproduct M F := by
    constructor
    intro b hb
    refine ⟨isBilimitOfTotal _ ?_⟩
    simp_rw [F.mapBicone_π, F.mapBicone_ι, ← F.map_comp]
    erw [← F.map_sum, ← F.map_id, IsBilimit.total hb]
  exact (isZero_finite_biproduct (F.obj ∘ M) h).of_iso
    (F.mapIso e ≪≫ F.mapBiproduct M)

end SteinerGeometry
