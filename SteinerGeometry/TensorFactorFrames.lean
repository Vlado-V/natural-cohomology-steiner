import SteinerGeometry.SectionTensorMonomials
import Mathlib.Algebra.Category.Grp.EpiMono

/-! Actual coordinate frames for ordered tensor products of trivialized line sheaves. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}

/-- Tensoring genuine coordinate isomorphisms gives a genuine coordinate isomorphism. -/
theorem tensorCoefficient_isIso (s : ℕ) (G : Fin s → X.Modules)
    (c : ∀ j, G j ⟶ Line.Bundles.structureModule X) (hc : ∀ j, IsIso (c j)) :
    IsIso (tensorCoefficient s G c) := by
  induction s with
  | zero => change IsIso (𝟙 _); infer_instance
  | succ s ih =>
    let _ := hc 0
    let _ := ih (fun j => G j.succ) (fun j => c j.succ) (fun j => hc j.succ)
    change IsIso (Tensor.Bifunctor.tensorModuleMap (c 0)
      (tensorCoefficient s (fun j => G j.succ) (fun j => c j.succ)) ≫ _)
    infer_instance

/-- Every section of a trivialized ordered tensor product is a scalar multiple
of the tensor of the coordinate-one sections. -/
theorem tensorGenerator_spans_of_frames (s : ℕ) (G : Fin s → X.Modules)
    (c : ∀ j, G j ≅ Line.Bundles.structureModule X) (U : X.Opens)
    (x : Γ(tensorFactors s G, U)) :
    ∃ r : Γ(X, U), x = r • tensorGenerator s G U
      (fun j => (c j).inv.app U (1 : Γ(X, U))) := by
  let t := tensorCoefficient s G (fun j => (c j).hom)
  have ht : IsIso t := tensorCoefficient_isIso s G _ (fun j => inferInstance)
  let _ := ht
  refine ⟨structureMapValue t U x, ?_⟩
  apply (AddCommGrpCat.mono_iff_injective (t.app U)).mp inferInstance
  rw [t.app_smul]
  have hg : structureMapValue t U (tensorGenerator s G U
      (fun j => (c j).inv.app U (1 : Γ(X, U)))) = 1 := by
    rw [tensorCoefficient_generator]
    have hi (j : Fin s) : structureMapValue (c j).hom U
        ((c j).inv.app U (1 : Γ(X, U))) = 1 := by
      have h := congrArg (fun f : Line.Bundles.structureModule X ⟶
        Line.Bundles.structureModule X => f.app U (1 : Γ(X, U))) (c j).inv_hom_id
      exact h
    simp only [hi, Finset.prod_const_one]
  change structureMapValue t U x = _
  rw [show t.app U (tensorGenerator s G U
    (fun j => (c j).inv.app U (1 : Γ(X, U)))) = (1 : Γ(X, U)) from hg]
  exact (mul_one _).symm

/-- Tensor generators detect sheaf morphisms on a chart with actual factor frames. -/
theorem tensorFactors_hom_ext_of_frames (s : ℕ) (G : Fin s → X.Modules)
    (c : ∀ j, G j ≅ Line.Bundles.structureModule X) {P : X.Modules}
    (f g : tensorFactors s G ⟶ P)
    (h : ∀ U : X.Opens, ∀ v : ∀ j, Γ(G j, U),
      f.app U (tensorGenerator s G U v) = g.app U (tensorGenerator s G U v)) : f = g := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro x
  obtain ⟨r, rfl⟩ := tensorGenerator_spans_of_frames s G c U x
  rw [f.app_smul, g.app_smul, h]

end SteinerGeometry
