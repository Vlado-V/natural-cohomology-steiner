import OAI.AlgebraicGeometry.SheafCohomology.Projective.CycleHomologyDesc

/-! # Naturality of cohomology computed by coefficient projections

These lemmas identify an induced map from its actual action on cochains.
No dimension comparison or choice of an unrelated vector-space equivalence
is involved. -/

noncomputable section
namespace SteinerGeometry.LaurentTopNaturality

open CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.SheafCohomology.Projective.CycleHomologyDesc

universe u v
variable {R : Type u} [Ring R]

/-- A commuting square on degree `q` cochains descends to the corresponding
square on homology, provided the two coefficient maps are represented by
those cochain projections. -/
theorem homologyProjection_naturality
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L) (q : ℕ)
    {A B : ModuleCat.{v} R}
    (pK : K.X q ⟶ A) (pL : L.X q ⟶ B)
    (hK : K.homology q ⟶ A) (hL : L.homology q ⟶ B)
    (hpK : K.homologyπ q ≫ hK = K.iCycles q ≫ pK)
    (hpL : L.homologyπ q ≫ hL = L.iCycles q ≫ pL)
    (g : A ⟶ B) (hfg : f.f q ≫ pL = pK ≫ g) :
    HomologicalComplex.homologyMap f q ≫ hL = hK ≫ g := by
  apply (cancel_epi (K.homologyπ q)).1
  rw [← Category.assoc, HomologicalComplex.homologyπ_naturality,
    Category.assoc, hpL, ← Category.assoc,
    HomologicalComplex.cyclesMap_i, Category.assoc, hfg,
    ← Category.assoc, ← hpK, Category.assoc]

/-- The explicit quotient construction used by the Laurent coefficient
projection is natural for any commuting cochain-level coefficient map. -/
theorem positiveHomologyDesc_naturality
    {K L : CochainComplex (ModuleCat.{v} R) ℕ} (f : K ⟶ L) (n : ℕ)
    {A B : ModuleCat.{v} R}
    (pK : K.X (n + 1) ⟶ A) (pL : L.X (n + 1) ⟶ B)
    (hbK : K.toCycles n (n + 1) ≫ (K.iCycles (n + 1) ≫ pK) = 0)
    (hbL : L.toCycles n (n + 1) ≫ (L.iCycles (n + 1) ≫ pL) = 0)
    (g : A ⟶ B) (hfg : f.f (n + 1) ≫ pL = pK ≫ g) :
    HomologicalComplex.homologyMap f (n + 1) ≫
        positiveHomologyDesc L n (L.iCycles (n + 1) ≫ pL) hbL =
      positiveHomologyDesc K n (K.iCycles (n + 1) ≫ pK) hbK ≫ g := by
  exact homologyProjection_naturality f (n + 1) pK pL _ _
    (positiveHomologyDesc_homologyπ _ _ _ _)
    (positiveHomologyDesc_homologyπ _ _ _ _) g hfg

end SteinerGeometry.LaurentTopNaturality
