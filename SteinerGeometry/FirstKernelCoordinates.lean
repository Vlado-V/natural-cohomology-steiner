module

public import SteinerGeometry.SheafMatrixCoordinates
public import SteinerGeometry.KernelFrameCompletion
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

set_option backward.privateInPublic true
@[expose] public section

/-! Coordinates on the actual first evaluation kernel, for completing local symmetric frames. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}
local instance firstKernelCoordinatesBiproducts : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts
private instance firstKernelCoordinatesEvalAdditive (U : X.Opens) :
    (SheafOfModules.evaluation X.ringCatSheaf (op U)).Additive where
  map_add := by intros; rfl

/-- A functional kernel transforms naturally under a coordinate equivalence on its source. -/
def functionalKernelCoordinates {R V W : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (ell : V →ₗ[R] R) (E : W ≃ₗ[R] V) : ell.ker ≃ₗ[R] (ell.comp E.toLinearMap).ker where
  toFun x := ⟨E.symm x.val, by
    change ell (E (E.symm x.val)) = 0
    rw [E.apply_symm_apply]
    exact x.property⟩
  invFun x := ⟨E x.val, x.property⟩
  left_inv x := by ext; exact E.apply_symm_apply x.val
  right_inv x := by ext; exact E.symm_apply_apply x.val
  map_add' x y := by ext; exact E.symm.map_add _ _
  map_smul' r x := by ext; exact E.symm.map_smul r _

/-- The actual evaluation of the chosen sections, with a literal finite free source. -/
def structureEvaluation {n : ℕ} {N : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N)) :
    (⨁ fun _ : Fin (n+1) => Line.Bundles.structureModule X) ⟶ N :=
  biproduct.desc e

/-- The functional on actual local-ring coordinates induced by evaluation. -/
def evaluationFunctional {n : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (U : X.Opens) : (Fin (n+1) → Γ(X, U)) →ₗ[Γ(X, U)] Γ(X, U) :=
  (Tensor.Powers.SheafMultilinearMap.homApp (structureEvaluation e) U).comp
    (structureSumCoordinates U (Fin (n+1))).symm.toLinearMap

/-- Sections of an actual kernel sheaf are the kernel of the actual section map. -/
def kernelSectionsEquiv {M N : X.Modules} (g : M ⟶ N) (U : X.Opens) :
    Γ(kernel g, U) ≃ₗ[Γ(X, U)]
      (Tensor.Powers.SheafMultilinearMap.homApp g U).ker := by
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : PreservesFiniteLimits F := SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  exact ((PreservesKernel.iso F g) ≪≫ ModuleCat.kernelIsoKer (F.map g)).toLinearEquiv

@[simp] theorem kernelSectionsEquiv_val {M N : X.Modules} (g : M ⟶ N) (U : X.Opens)
    (z : Γ(kernel g, U)) : (kernelSectionsEquiv g U z).val = (kernel.ι g).app U z := by
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : PreservesFiniteLimits F := SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  have h : (PreservesKernel.iso F g).hom ≫ (ModuleCat.kernelIsoKer (F.map g)).hom ≫
      ModuleCat.ofHom ((F.map g).hom.ker.subtype) = F.map (kernel.ι g) := by
    rw [ModuleCat.kernelIsoKer_hom_ker_subtype, PreservesKernel.iso_hom,
      kernelComparison_comp_ι]
  exact congrArg (fun q => q z) h

/-- The section coordinates induced by a finite family of line-bundle frames. -/
def lineSumSectionCoordinates {n : ℕ} (L : Fin n → Line.Bundles.LineBundle X)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X) (U : X.Opens) :
    Γ((⨁ fun j => (L j).sheaf), U) ≃ₗ[Γ(X, U)] (Fin n → Γ(X, U)) :=
  (sheafIsoSections (biproduct.mapIso frames) U).trans (structureSumCoordinates U (Fin n))

@[simp] theorem structureSumCoordinates_symm_single {m : ℕ} (U : X.Opens) (i : Fin m) :
    (structureSumCoordinates U (Fin m)).symm (Pi.single i (1 : Γ(X, U))) =
      (biproduct.ι (fun _ : Fin m => Line.Bundles.structureModule X) i).app U (1 : Γ(X, U)) := by
  classical
  change (∑ j : Fin m, (biproduct.ι (fun _ : Fin m => Line.Bundles.structureModule X) j).app U
    ((Pi.single i (1 : Γ(X, U)) : Fin m → Γ(X, U)) j)) = _
  simp only [Pi.single_apply, apply_ite, map_zero]
  rw [Finset.sum_ite_eq']
  simp

@[simp] theorem lineSumSectionCoordinates_symm_single {n : ℕ}
    (L : Fin n → Line.Bundles.LineBundle X)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X) (U : X.Opens) (i : Fin n) :
    (lineSumSectionCoordinates L frames U).symm (Pi.single i (1 : Γ(X, U))) =
      (biproduct.ι (fun j => (L j).sheaf) i).app U
        ((frames i).inv.app U (1 : Γ(X, U))) := by
  classical
  change (biproduct.mapIso frames).inv.app U
    ((structureSumCoordinates U (Fin n)).symm (Pi.single i (1 : Γ(X, U)))) = _
  rw [structureSumCoordinates_symm_single]
  have h := biproduct.ι_map (fun j => (frames j).inv) i
  exact congrArg (fun q => q.app U (1 : Γ(X, U))) h

/-- On a chart where the kernel splits into framed lines, it is a genuine
free module basis of the functional kernel, not an assumed dimension statement. -/
def firstKernelFrameEquiv {n : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (L : Fin n → Line.Bundles.LineBundle X)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e))
    (U : X.Opens) :
    (Fin n → Γ(X, U)) ≃ₗ[Γ(X, U)] (evaluationFunctional e U).ker := by
  let F : X.Modules ⥤ ModuleCat.{u} Γ(X, U) := SheafOfModules.evaluation X.ringCatSheaf (op U)
  let _ : PreservesFiniteLimits F := SheafOfModules.Finite.evaluationPreservesFiniteLimits _ _
  let source := lineSumSectionCoordinates L frames U
  let kerE := kernelSectionsEquiv (structureEvaluation e) U
  exact source.symm.trans ((sheafIsoSections E U).trans (kerE.trans
    (functionalKernelCoordinates (F.map (structureEvaluation e)).hom
      (structureSumCoordinates U (Fin (n+1))).symm)))

/-- The first-kernel frame is given by the actual inclusion into the free sheaf. -/
theorem firstKernelFrameEquiv_val {n : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (L : Fin n → Line.Bundles.LineBundle X)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e))
    (U : X.Opens) (v : Fin n → Γ(X, U)) :
    (firstKernelFrameEquiv e L frames E U v).val =
      structureSumCoordinates U (Fin (n+1))
        ((kernel.ι (structureEvaluation e)).app U
          (E.hom.app U ((lineSumSectionCoordinates L frames U).symm v))) := by
  change (structureSumCoordinates U (Fin (n+1)))
    (kernelSectionsEquiv (structureEvaluation e) U
      (E.hom.app U ((lineSumSectionCoordinates L frames U).symm v))).val = _
  rw [kernelSectionsEquiv_val]

/-- In particular the rows of the finite kernel frame are the coefficients of
the original sheaf inclusion on its chosen line generators. -/
theorem firstKernelFrameEquiv_single {n : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (L : Fin n → Line.Bundles.LineBundle X)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e))
    (U : X.Opens) (i : Fin n) :
    (firstKernelFrameEquiv e L frames E U (Pi.single i (1 : Γ(X, U)))).val =
      structureSumCoordinates U (Fin (n+1))
        ((biproduct.ι _ i ≫ E.hom ≫ kernel.ι (structureEvaluation e)).app U
          ((frames i).inv.app U (1 : Γ(X, U)))) := by
  rw [firstKernelFrameEquiv_val, lineSumSectionCoordinates_symm_single]
  rfl

@[simp] theorem evaluationFunctional_single {n : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (U : X.Opens) (i : Fin (n+1)) :
    evaluationFunctional e U (Pi.single i (1 : Γ(X, U))) =
      structureMapValue (e i) U (1 : Γ(X, U)) := by
  change (structureEvaluation e).app U
    ((structureSumCoordinates U (Fin (n+1))).symm (Pi.single i (1 : Γ(X, U)))) = _
  rw [structureSumCoordinates_symm_single]
  exact congrArg (fun q => q.app U (1 : Γ(X, U))) (biproduct.ι_desc e i)

/-- A coefficient which is an actual sheaf isomorphism supplies a unit-valued splitting vector. -/
theorem evaluationFunctional_has_splitter {n : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (j : Fin (n+1)) [IsIso (e j)] (U : X.Opens) :
    ∃ v : Fin (n+1) → Γ(X, U), evaluationFunctional e U v = 1 := by
  refine ⟨structureSumCoordinates U (Fin (n+1))
    ((biproduct.ι (fun _ : Fin (n+1) => Line.Bundles.structureModule X) j).app U
      ((inv (e j)).app U (1 : Γ(X, U)))), ?_⟩
  change (structureEvaluation e).app U
    ((structureSumCoordinates U (Fin (n+1))).symm
      (structureSumCoordinates U (Fin (n+1)) _)) = _
  rw [LinearEquiv.symm_apply_apply]
  have h := congrArg (fun q => q.app U ((inv (e j)).app U (1 : Γ(X, U))))
    (biproduct.ι_desc e j)
  change (structureEvaluation e).app U _ = (e j).app U _ at h
  exact h.trans (congrArg (fun q => q.app U (1 : Γ(X, U))) (IsIso.inv_hom_id (e j)))

/-- The completed local matrix is derived from the actual first-kernel isomorphism. -/
theorem firstKernelFrame_completed_matrices {n : ℕ}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X))
    (L : Fin n → Line.Bundles.LineBundle X)
    (frames : ∀ j, (L j).sheaf ≅ Line.Bundles.structureModule X)
    (E : (⨁ fun j => (L j).sheaf) ≅ kernel (structureEvaluation e))
    (j : Fin (n+1)) [IsIso (e j)] (U : X.Opens) :
    ∃ A B : Matrix (Fin (n+1)) (Fin (n+1)) Γ(X, U),
      A * B = 1 ∧ B * A = 1 ∧
      (∀ i : Fin n, A i.succ =
        (firstKernelFrameEquiv e L frames E U (Pi.single i (1 : Γ(X, U)))).val) ∧
      (∀ i, ∑ k, structureMapValue (e k) U (1 : Γ(X, U)) * A i k =
        if i = 0 then 1 else 0) := by
  obtain ⟨v0, hv0⟩ := evaluationFunctional_has_splitter e j U
  obtain ⟨A, B, hAB, hBA, _, hRows, hA⟩ :=
    exists_kernelFrame_matrices (evaluationFunctional e U) v0 hv0
      (firstKernelFrameEquiv e L frames E U)
  exact ⟨A, B, hAB, hBA, hRows, by simpa only [evaluationFunctional_single] using hA⟩

end SteinerGeometry
