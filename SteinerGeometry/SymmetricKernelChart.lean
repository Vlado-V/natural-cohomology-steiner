import SteinerGeometry.FirstKernelCoordinates
import SteinerGeometry.SplitKernelLocalIso

/-! The symmetric contraction kernel on an actual split, trivialized chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}
local instance symmetricKernelChartBiproducts : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- Degree-one symmetric labels are the original free coordinates. -/
def linearMonomialIso (n : ℕ) :
    (⨁ fun _ : Fin (n+1) => Line.Bundles.structureModule X) ≅
      homogeneousFreeSheaf (X := X) n 1 :=
  biproduct.whiskerEquiv
    (f := fun _ : Fin (n+1) => Line.Bundles.structureModule X)
    (g := fun _ : Sym (Fin (n+1)) 1 => Line.Bundles.structureModule X)
    (Sym.oneEquiv : Fin (n+1) ≃ Sym (Fin (n+1)) 1) (fun _ => Iso.refl _)

@[simp] theorem linearMonomialIso_hom_π (n : ℕ) (i : Fin (n+1)) :
    (linearMonomialIso (X := X) n).hom ≫
      biproduct.π _ (wordMonomial (fun _ : Fin 1 => i)) =
        biproduct.π (fun _ : Fin (n+1) => Line.Bundles.structureModule X) i := by
  have hi : wordMonomial (fun _ : Fin 1 => i) = (Sym.oneEquiv : Fin (n+1) ≃ _) i := by
    apply Sym.ext
    rfl
  rw [hi, linearMonomialIso, biproduct.whiskerEquiv_hom_eq_lift]
  simp only [biproduct.lift_π]
  exact congrArg (biproduct.π (fun _ : Fin (n+1) => Line.Bundles.structureModule X))
    ((Sym.oneEquiv : Fin (n+1) ≃ Sym (Fin (n+1)) 1).symm_apply_apply i)

/-- The columns used by the monomial map come directly from the first kernel inclusion. -/
def firstKernelColumns {n : ℕ} {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N))
    (L : Fin n → Line.Bundles.LineBundle X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e))
    (j : Fin n) : (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1 :=
  biproduct.ι (fun j => (L j).sheaf) j ≫ E.hom ≫ kernel.ι (structureEvaluation e) ≫ (linearMonomialIso n).hom

private theorem structureEvaluation_eq_sum {n : ℕ} {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N)) :
    (∑ i, biproduct.π (fun _ : Fin (n+1) => Line.Bundles.structureModule X) i ≫ e i) =
      structureEvaluation e := by
  classical
  calc
    _ = (∑ i, biproduct.π (fun _ : Fin (n+1) => Line.Bundles.structureModule X) i ≫
        biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule X) i) ≫ structureEvaluation e := by
      rw [Preadditive.sum_comp]
      apply Finset.sum_congr rfl
      intro i _
      rw [Category.assoc, show biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule X) i ≫ structureEvaluation e = e i from biproduct.ι_desc e i]
    _ = _ := by rw [biproduct.total, Category.id_comp]

/-- The canonical first-kernel columns satisfy the required evaluation relation. -/
theorem firstKernelColumns_relation {n : ℕ} {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N))
    (L : Fin n → Line.Bundles.LineBundle X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e)) (j : Fin n) :
    (∑ i, (firstKernelColumns e L E j ≫
      biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ e i) = 0 := by
  classical
  simp only [firstKernelColumns, Category.assoc, linearMonomialIso_hom_π]
  calc
    _ = (biproduct.ι (fun j => (L j).sheaf) j ≫ E.hom ≫ kernel.ι (structureEvaluation e)) ≫
        (∑ i, biproduct.π (fun _ : Fin (n+1) => Line.Bundles.structureModule X) i ≫ e i) := by
      simp only [Preadditive.comp_sum, Category.assoc]
    _ = 0 := by
      rw [structureEvaluation_eq_sum]
      simp only [Category.assoc, kernel.condition, comp_zero]

/-- The matrix rows of those columns are precisely the frame of the actual functional kernel. -/
theorem firstKernelColumns_rows {n : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (L : Fin n → Line.Bundles.LineBundle X)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e))
    (U : X.Opens) (i : Fin n) :
    (firstKernelFrameEquiv e L frames E U (Pi.single i (1 : Γ(X, U)))).val =
      kernelRowCoefficients L (firstKernelColumns e L E) frames U i := by
  rw [firstKernelFrameEquiv_single]
  funext j
  change (biproduct.π (fun _ : Fin (n+1) => Line.Bundles.structureModule X) j).app U
      ((biproduct.ι (fun j => (L j).sheaf) i ≫ E.hom ≫ kernel.ι (structureEvaluation e)).app U
        ((frames i).inv.app U (1 : Γ(X, U)))) = _
  unfold kernelRowCoefficients firstKernelColumns
  simp only [Category.assoc, linearMonomialIso_hom_π]
  rfl

/-- The symmetric contraction kernel of a split evaluation sequence is the
sum of its monomial line factors, on a chart with actual line frames. -/
theorem symmetricKernel_isIso_on_split_chart
    {K : Type u} [Field K] [CharZero K] (p : X ⟶ Spec (.of K)) {n d : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (L : Fin n → Line.Bundles.LineBundle X)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e))
    (j : Fin (n+1)) [IsIso (e j)] :
    IsIso (splitMonomialKernelMap (d := d) e L (firstKernelColumns e L E)
      (firstKernelColumns_relation e L E)) := by
  apply splitMonomialKernelMap_isIso_of_matrices p e L _ _ frames
  intro U
  obtain ⟨A, B, hAB, hBA, hRows, hA⟩ := firstKernelFrame_completed_matrices e L frames E j U
  refine ⟨A, B, hAB, hBA, ?_, hA⟩
  intro i
  exact (hRows i).trans (firstKernelColumns_rows e L frames E U i)

end SteinerGeometry
