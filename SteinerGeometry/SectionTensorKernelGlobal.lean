module

public import SteinerGeometry.SectionTensorKernel
public import SteinerGeometry.TensorFactorRestriction
public import SteinerGeometry.CommonLineFrames
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.MapCoverEquality

set_option backward.privateInPublic true
@[expose] public section

/-! The split monomial map lands in the actual contraction kernel sheaf. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}
local instance sectionTensorKernelGlobalBiproducts : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- Actual sheaf morphisms from ordered tensors of line bundles are detected by
all their decomposable sections. The proof uses simultaneous local frames. -/
theorem tensorLineFactors_hom_ext (s : ℕ) (L : Fin s → Line.Bundles.LineBundle X)
    {P : X.Modules} (f g : tensorFactors s (fun j => (L j).sheaf) ⟶ P)
    (h : ∀ U : X.Opens, ∀ v : ∀ j, Γ((L j).sheaf, U),
      f.app U (tensorGenerator s (fun j => (L j).sheaf) U v) =
        g.app U (tensorGenerator s (fun j => (L j).sheaf) U v)) : f = g := by
  classical
  choose U hU frames using commonLineRestrictionFrames L
  apply Module.MapCoverEquality.moduleMap_eq_of_restrict_cover U (fun x => ⟨x, hU x⟩)
  intro x
  let E := tensorFactorsRestrictIso (U x).ι s (fun j => (L j).sheaf)
  apply (cancel_epi E.hom).mp
  apply tensorFactors_hom_ext_of_frames s (fun j => (L j).sheaf.restrict (U x).ι)
    (fun j => Classical.choice (frames x j))
  intro V v
  change ((Scheme.Modules.restrictFunctor (U x).ι).map f).app V
      (E.hom.app V (tensorGenerator s (fun j => (L j).sheaf.restrict (U x).ι) V v)) =
    ((Scheme.Modules.restrictFunctor (U x).ι).map g).app V
      (E.hom.app V (tensorGenerator s (fun j => (L j).sheaf.restrict (U x).ι) V v))
  rw [tensorFactorsRestrictIso_generator]
  exact h ((U x).ι ''ᵁ V) v

/-- If each line-factor column is in the evaluation kernel, multiplication of
its linear forms is annihilated by the actual symmetric contraction morphism. -/
theorem tensorMonomialMap_comp_contraction {n d : ℕ} {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N))
    (L : Fin (d+1) → Line.Bundles.LineBundle X)
    (c : ∀ j, Fin (n+1) → ((L j).sheaf ⟶ Line.Bundles.structureModule X))
    (hc : ∀ j, ∑ i, c j i ≫ e i = 0) :
    tensorMonomialMap (fun j => (L j).sheaf) c ≫ sectionContraction e d = 0 := by
  apply tensorLineFactors_hom_ext (d+1) L
  intro U v
  exact tensorMonomialMap_contraction_generator e (fun j => (L j).sheaf) c hc U v

set_option backward.isDefEq.respectTransparency false in
/-- Every monomial in a split evaluation kernel lands in the contraction kernel. -/
theorem splitMonomialMap_comp_contraction {m n d : ℕ} {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N))
    (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (hc : ∀ j, ∑ i, (c j ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ e i = 0) :
    splitMonomialMap L c (d+1) ≫ sectionContraction e d = 0 := by
  classical
  apply biproduct.hom_ext'
  intro a
  rw [← Category.assoc, splitMonomialMap_component, Category.assoc]
  change _ ≫ (tensorMonomialMap (fun j => (L (symmetricWord a j)).sheaf)
    (fun j i => c (symmetricWord a j) ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫
      sectionContraction e d) = _
  rw [tensorMonomialMap_comp_contraction e (fun j => L (symmetricWord a j)) _
    (fun j => hc (symmetricWord a j)), comp_zero]
  simp

/-- The canonical global map from monomial line factors to the actual kernel sheaf. -/
def splitMonomialKernelMap {m n d : ℕ} {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N))
    (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (hc : ∀ j, ∑ i, (c j ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ e i = 0) :
    splitMonomialSource L (d+1) ⟶ kernel (sectionContraction e d) :=
  kernel.lift _ (splitMonomialMap L c (d+1))
    (splitMonomialMap_comp_contraction e L c hc)

@[simp, reassoc] theorem splitMonomialKernelMap_ι {m n d : ℕ} {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N))
    (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (hc : ∀ j, ∑ i, (c j ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ e i = 0) :
    splitMonomialKernelMap e L c hc ≫ kernel.ι _ = splitMonomialMap L c (d+1) :=
  kernel.lift_ι _ _ _

end SteinerGeometry
