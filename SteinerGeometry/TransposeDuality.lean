import SteinerGeometry.CoproductMatrix
import SteinerGeometry.DualModelComparison
import SteinerGeometry.ScalarDualTensor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Functor.EpiMono

/-! The dual of a finite matrix is its transpose of dual component maps. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.TransposeDuality
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u

section FunctorMatrix
variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
  [HasFiniteBiproducts C] [HasFiniteBiproducts D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesFiniteCoproducts F]

@[reassoc (attr := simp)]
theorem coproduct_iso_inv_map_projection {ι : Type} [Fintype ι]
    (M : ι → C) (i : ι) :
    (PreservesCoproduct.iso F M).inv ≫
        F.map (CoproductMatrixComponents.finiteCoproductProjection M i) =
      CoproductMatrixComponents.finiteCoproductProjection (fun j => F.obj (M j)) i := by
  apply Sigma.hom_ext
  intro j
  simp only [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison_assoc, ← F.map_comp]
  unfold CoproductMatrixComponents.finiteCoproductProjection
  simp only [biproduct.isoCoproduct_inv, Sigma.ι_comp_desc_assoc]
  by_cases h : j = i
  · subst i
    simp
  · simp [h]

@[reassoc (attr := simp)]
theorem coproduct_iso_hom_projection {ι : Type} [Fintype ι]
    (M : ι → C) (i : ι) :
    (PreservesCoproduct.iso F M).hom ≫
        CoproductMatrixComponents.finiteCoproductProjection (fun j => F.obj (M j)) i =
      F.map (CoproductMatrixComponents.finiteCoproductProjection M i) := by
  rw [← coproduct_iso_inv_map_projection F M i, Iso.hom_inv_id_assoc]

theorem map_matrix {ι κ : Type} [Fintype ι] [Fintype κ]
    (M : ι → C) (N : κ → C) (c : ∀ j i, M i ⟶ N j) :
    (PreservesCoproduct.iso F M).inv ≫ F.map (finiteCoproductFromMatrix M N c) ≫
      (PreservesCoproduct.iso F N).hom =
        finiteCoproductFromMatrix (fun i => F.obj (M i))
          (fun j => F.obj (N j)) (fun j i => F.map (c j i)) := by
  apply CoproductMatrixComponents.finiteCoproduct_matrix_ext
  intro i j
  simp only [Category.assoc, coproduct_iso_hom_projection, PreservesCoproduct.inv_hom,
    ι_comp_sigmaComparison_assoc, ← F.map_comp, finiteCoproductFromMatrix_component]

theorem epi_matrix_transport {ι κ : Type} [Fintype ι] [Fintype κ]
    [F.PreservesEpimorphisms]
    (M : ι → C) (N : κ → C) (c : ∀ j i, M i ⟶ N j)
    (P : ι → D) (Q : κ → D) (e : ∀ i, F.obj (M i) ≅ P i)
    (d : ∀ j, F.obj (N j) ≅ Q j)
    [Epi (finiteCoproductFromMatrix M N c)] :
    Epi (finiteCoproductFromMatrix P Q (fun j i => (e i).inv ≫ F.map (c j i) ≫ (d j).hom)) := by
  let a := (Sigma.mapIso e).symm ≪≫ (PreservesCoproduct.iso F M).symm
  let b := PreservesCoproduct.iso F N ≪≫ Sigma.mapIso d
  have heq : a.hom ≫ F.map (finiteCoproductFromMatrix M N c) ≫ b.hom =
      finiteCoproductFromMatrix P Q (fun j i => (e i).inv ≫ F.map (c j i) ≫ (d j).hom) := by
    apply CoproductMatrixComponents.finiteCoproduct_matrix_ext
    intro i j
    simp only [a, b, Iso.trans_hom, Iso.symm_hom, Category.assoc,
      Sigma.ι_mapIso_inv_assoc, PreservesCoproduct.inv_hom,
      ι_comp_sigmaComparison_assoc, finiteCoproductFromMatrix_component]
    have hd : (Sigma.mapIso d).hom ≫
        CoproductMatrixComponents.finiteCoproductProjection Q j =
      CoproductMatrixComponents.finiteCoproductProjection (fun j => F.obj (N j)) j ≫
        (d j).hom := by
      apply Sigma.hom_ext
      intro k
      unfold CoproductMatrixComponents.finiteCoproductProjection
      simp only [Category.assoc, Sigma.ι_mapIso_hom_assoc, biproduct.isoCoproduct_inv,
        Sigma.ι_comp_desc_assoc]
      by_cases h : k = j
      · subst j
        simp
      · simp [h]
    rw [hd, coproduct_iso_hom_projection_assoc, ← F.map_comp_assoc,
      ← F.map_comp_assoc]
    simp only [Category.assoc, finiteCoproductFromMatrix_component]
  rw [← heq]
  infer_instance
end FunctorMatrix

variable {X : Scheme.{u}}
local instance : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

def dualSumIso {ι : Type} [Fintype ι] (M : ι → X.Modules) :
    SheafDual.dual (∐ M) ≅ ∐ (fun i => SheafDual.dual (M i)) :=
  SheafDual.dualIso (biproduct.isoCoproduct M).symm ≪≫
    SheafDual.dualBiproductIso M ≪≫ biproduct.isoCoproduct _

@[reassoc (attr := simp)]
theorem dualSumIso_hom_projection {ι : Type} [Fintype ι]
    (M : ι → X.Modules) (i : ι) :
    (dualSumIso M).hom ≫
      CoproductMatrixComponents.finiteCoproductProjection (fun j => SheafDual.dual (M j)) i =
        SheafDual.dualMap (Sigma.ι M i) := by
  change SheafDual.dualMap (biproduct.isoCoproduct M).hom ≫
    (SheafDual.dualBiproductIso M).hom ≫ (biproduct.isoCoproduct _).hom ≫
      (biproduct.isoCoproduct _).inv ≫ biproduct.π _ i = _
  rw [Iso.hom_inv_id_assoc]
  change SheafDual.dualMap (biproduct.isoCoproduct M).hom ≫
    biproduct.lift (fun j => SheafDual.dualMap (biproduct.ι M j)) ≫ biproduct.π _ i = _
  rw [biproduct.lift_π, ← SheafDual.dualMap_comp]
  congr 1
  simp [biproduct.isoCoproduct_hom]

@[reassoc (attr := simp)]
theorem injection_dualSumIso_inv {ι : Type} [Fintype ι]
    (M : ι → X.Modules) (i : ι) :
    Sigma.ι (fun j => SheafDual.dual (M j)) i ≫ (dualSumIso M).inv =
      SheafDual.dualMap (CoproductMatrixComponents.finiteCoproductProjection M i) := by
  simp [dualSumIso, CoproductMatrixComponents.finiteCoproductProjection,
    SheafDual.dualIso, SheafDual.dualBiproductIso, ← SheafDual.dualMap_comp,
    biproduct.isoCoproduct_inv]

theorem dualMap_matrix {ι κ : Type} [Fintype ι] [Fintype κ]
    (M : ι → X.Modules) (N : κ → X.Modules)
    (c : ∀ j i, M i ⟶ N j) :
    (dualSumIso N).inv ≫ SheafDual.dualMap (finiteCoproductFromMatrix M N c) ≫
      (dualSumIso M).hom =
        finiteCoproductFromMatrix (fun j => SheafDual.dual (N j))
          (fun i => SheafDual.dual (M i)) (fun i j => SheafDual.dualMap (c j i)) := by
  apply CoproductMatrixComponents.finiteCoproduct_matrix_ext
  intro j i
  simp only [Category.assoc, injection_dualSumIso_inv_assoc,
    dualSumIso_hom_projection, ← SheafDual.dualMap_comp,
    finiteCoproductFromMatrix_component]

section Invertible
open MonoidalCategory
local instance : MonoidalCategory X.Modules := Monoidal.Scheme.Modules.monoidalCategory X

/-- A surjective matrix with entries in an invertible line has an epimorphic
dual transpose.  All maps are the actual sheaf morphisms, with no chosen frames. -/
theorem epi_dualMap_transpose {a b : ℕ} (L : X.Modules)
    (hL : Invertible.Scheme.Modules.IsInvertible L)
    (g : Fin a → Fin b → (L ⟶ Invertible.Scheme.Modules.unitObj X))
    (hf : Epi (finiteCoproductFromMatrix (fun _ : Fin b => L)
      (fun _ : Fin a => Invertible.Scheme.Modules.unitObj X) g)) :
    Epi (SheafDual.dualMap (finiteCoproductFromMatrix (fun _ : Fin a => L)
      (fun _ : Fin b => Invertible.Scheme.Modules.unitObj X) (fun j i => g i j))) := by
  letI := hf
  let O := Invertible.Scheme.Modules.unitObj X
  let D := Dual.Scheme.Modules.dualObj L
  let F := (InvertibleTensorEquivalence.invertibleRightTensorEquivalence D hL.dual).functor
  let e : F.obj L ≅ SheafDual.dual O :=
    InvertibleCancellationPairing.invertibleDualPairingIso L hL ≪≫
      (Dual.Scheme.Modules.dualUnitObjIso (X := X)).symm ≪≫ (SheafDual.nativeDualIso O).symm
  let d : F.obj O ≅ SheafDual.dual L :=
    ScalarDualTensor.unitLeftIso D ≪≫ (SheafDual.nativeDualIso L).symm
  have hcoeff (i : Fin a) (j : Fin b) :
      e.inv ≫ F.map (g i j) ≫ d.hom = SheafDual.dualMap (g i j) := by
    have hF : F.map (g i j) = (g i j) ⊗ₘ 𝟙 D := by
      change (g i j) ▷ D = _
      simp
    simp only [e, d, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv, Iso.symm_hom,
      Category.assoc, hF]
    change (SheafDual.nativeDualIso O).hom ≫
      (Dual.Scheme.Modules.dualUnitObjIso (X := X)).hom ≫
      (InvertibleCancellationPairing.invertibleDualPairingIso L hL).inv ≫
      ((g i j) ⊗ₘ 𝟙 D) ≫ (ScalarDualTensor.unitLeftIso D).hom ≫
      (SheafDual.nativeDualIso L).inv = _
    rw [ScalarDualTensor.scalarDual_tensor_bridge_assoc L hL]
    simp only [Iso.hom_inv_id_assoc]
    rw [← Category.assoc, ← SheafDual.nativeDualIso_natural]
    simp
  have hm : Epi (finiteCoproductFromMatrix (fun _ : Fin b => SheafDual.dual O)
      (fun _ : Fin a => SheafDual.dual L) (fun i j => SheafDual.dualMap (g i j))) := by
    have h := epi_matrix_transport F (fun _ : Fin b => L) (fun _ : Fin a => O) g
      (fun _ : Fin b => SheafDual.dual O) (fun _ : Fin a => SheafDual.dual L)
      (fun _ => e) (fun _ => d)
    simpa only [hcoeff] using h
  let i := finiteCoproductFromMatrix (fun _ : Fin a => L)
    (fun _ : Fin b => O) (fun j i => g i j)
  have hn : Epi ((dualSumIso (fun _ : Fin b => O)).inv ≫ SheafDual.dualMap i ≫
      (dualSumIso (fun _ : Fin a => L)).hom) := by
    dsimp only [i]
    rw [dualMap_matrix]
    exact hm
  haveI : Epi ((dualSumIso (fun _ : Fin b => O)).inv ≫ SheafDual.dualMap i) :=
    (epi_comp_iff_of_isIso _ (dualSumIso (fun _ : Fin a => L)).hom).mp
      (by simpa only [Category.assoc] using hn)
  exact epi_of_epi (dualSumIso (fun _ : Fin b => O)).inv (SheafDual.dualMap i)

end Invertible

end SteinerGeometry.TransposeDuality
