import SteinerGeometry.SplitMonomialFrames
import SteinerGeometry.DirectionalCoordinates

/-! Local-ring matrices of actual finite sums of the structure sheaf. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}
local instance sheafMatrixCoordinatesBiproducts : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

private instance sheafMatrixCoordinatesEvalAdditive (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive where
  map_add := by intros; rfl

/-- The literal local-ring coordinates on a finite sum of structure sheaves. -/
def structureSumCoordinates (U : X.Opens) (α : Type) [Fintype α] :
    Γ((⨁ fun _ : α => Line.Bundles.structureModule X), U) ≃ₗ[Γ(X, U)] (α → Γ(X, U)) := by
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let B : X.Modules := Line.Bundles.structureModule X
  let _ : F.Additive := sheafMatrixCoordinatesEvalAdditive U
  exact biproductCoordinates (C := X.Modules) F B α

private theorem structureMap_apply (f : Line.Bundles.structureModule X ⟶
    Line.Bundles.structureModule X) (U : X.Opens) (r : Γ(X, U)) :
    structureMapValue f U r = structureMapValue f U (1 : Γ(X, U)) * r := by
  have h := f.app_smul r (1 : Γ(X, U))
  change structureMapValue f U (r * (1 : Γ(X, U))) = r * structureMapValue f U (1 : Γ(X, U)) at h
  simpa only [mul_one, mul_comm] using h

/-- A morphism of structure-sheaf sums acts by its ordinary matrix over each ring of sections. -/
theorem structureSheafMatrix_apply {α β : Type} [Fintype α] [Fintype β]
    (f : (⨁ fun _ : α => Line.Bundles.structureModule X) ⟶
      ⨁ fun _ : β => Line.Bundles.structureModule X)
    (U : X.Opens) (x : α → Γ(X, U)) (b : β) :
    structureSumCoordinates U β (f.app U ((structureSumCoordinates U α).symm x)) b =
      ∑ a, structureMapValue (biproduct.ι _ a ≫ f ≫ biproduct.π _ b) U (1 : Γ(X, U)) * x a := by
  classical
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  change F.map (biproduct.π _ b) (F.map f (∑ a, F.map (biproduct.ι _ a) (x a))) = _
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [← ModuleCat.comp_apply, ← ModuleCat.comp_apply, ← F.map_comp, ← F.map_comp]
  change structureMapValue (biproduct.ι _ a ≫ f ≫ biproduct.π _ b) U (x a) = _
  exact structureMap_apply _ U _

/-- Coefficients of a framed kernel column, regarded as actual regular functions. -/
def kernelRowCoefficients {m n : ℕ} (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (U : X.Opens) (j : Fin m) (i : Fin (n+1)) : Γ(X, U) :=
  structureMapValue (c j ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) U
    ((frames j).inv.app U (1 : Γ(X, U)))

set_option backward.isDefEq.respectTransparency false in
/-- In line-bundle frames, the genuine global monomial map has the polynomial-product matrix. -/
theorem splitMonomialMap_coordinates {m n s : ℕ} (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (U : X.Opens) (x : Sym (Fin m) s → Γ(X, U)) (b : Sym (Fin (n+1)) s) :
    structureSumCoordinates U (Sym (Fin (n+1)) s)
      (((splitMonomialFrameIso L frames s).inv ≫ splitMonomialMap L c s).app U
        ((structureSumCoordinates U (Sym (Fin m) s)).symm x)) b =
      ∑ a, (∏ j, Steiner.SymmetricContraction.linearForm
        (kernelRowCoefficients L c frames U (symmetricWord a j))).coeff
          (Steiner.operatorExponent s b) * x a := by
  classical
  rw [structureSheafMatrix_apply]
  apply Finset.sum_congr rfl
  intro a _
  congr 1
  have he : biproduct.ι _ a ≫ (splitMonomialFrameIso L frames s).inv =
      (monomialFrameIso L frames a).inv ≫ biproduct.ι (fun a : Sym (Fin m) s => (monomialLineBundle L a).sheaf) a := by
    exact biproduct.ι_map (fun a : Sym (Fin m) s => (monomialFrameIso L frames a).inv) a
  rw [← Category.assoc, ← Category.assoc, he, Category.assoc, Category.assoc]
  exact splitMonomialMap_frame_entry L c frames a b U

/-- The polynomial map used by local exactness is the local matrix of the actual sheaf map. -/
theorem splitMonomialMap_coordinates_of_rows {n s : ℕ} (L : Fin n → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (U : X.Opens) (A : Matrix (Fin (n+1)) (Fin (n+1)) Γ(X, U))
    (hA : ∀ i : Fin n, A i.succ = kernelRowCoefficients L c frames U i)
    (x : Sym (Fin n) s → Γ(X, U)) :
    structureSumCoordinates U (Sym (Fin (n+1)) s)
      (((splitMonomialFrameIso L frames s).inv ≫ splitMonomialMap L c s).app U
        ((structureSumCoordinates U (Sym (Fin n) s)).symm x)) =
      splitPolynomialMap A s x := by
  funext b
  rw [splitMonomialMap_coordinates, splitPolynomialMap_apply]
  simp only [hA, smul_eq_mul]
  rfl

/-- An actual sheaf isomorphism gives linear coordinates on sections over each open. -/
def sheafIsoSections {M N : X.Modules} (e : M ≅ N) (U : X.Opens) :
    Γ(M, U) ≃ₗ[Γ(X, U)] Γ(N, U) where
  toFun := e.hom.app U
  invFun := e.inv.app U
  left_inv x := congrArg (fun f : M ⟶ M => f.app U x) e.hom_inv_id
  right_inv x := congrArg (fun f : N ⟶ N => f.app U x) e.inv_hom_id
  map_add' x y := (e.hom.app U).hom.map_add x y
  map_smul' r x := e.hom.app_smul r x

/-- Over a structure-sheaf frame the sheaf contraction is the genuine local-ring matrix. -/
theorem sectionContraction_structure_coordinates {n : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (d : ℕ) (U : X.Opens) (x : Sym (Fin (n+1)) (d+1) → Γ(X, U)) :
    structureSumCoordinates U (Sym (Fin (n+1)) d)
      ((sectionContraction e d).app U
        ((structureSumCoordinates U (Sym (Fin (n+1)) (d+1))).symm x)) =
      weightedContraction (fun i => structureMapValue (e i) U (1 : Γ(X, U))) d x := by
  classical
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : F.Additive := sheafMatrixCoordinatesEvalAdditive U
  funext b
  change biproductCoordinates F (Line.Bundles.structureModule X) _
    (F.map (sectionContraction e d) ((biproductCoordinates F
      (Line.Bundles.structureModule X) _).symm x)) b = _
  rw [sectionContraction_sections_weighted]
  change (∑ a, ∑ i, contractionMultiplicity d a b i • structureMapValue (e i) U (x a)) = _
  change (∑ a, ∑ i, contractionMultiplicity d a b i • structureMapValue (e i) U (x a)) =
    ∑ a, ∑ i, contractionMultiplicity d a b i •
      (structureMapValue (e i) U (1 : Γ(X, U)) * x a)
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro i _
  rw [structureMap_apply]

end SteinerGeometry
