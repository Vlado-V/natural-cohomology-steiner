import SteinerGeometry.SectionTensorKernelGlobal
import SteinerGeometry.SectionContractionTransport

/-! Changing the frame of the line-valued contraction target. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
variable {X : Scheme.{u}}
local instance contractionTargetIsoBiproducts : HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- An isomorphism of the target transports the genuine contraction kernel. -/
def contractionTargetKernelIso {n d : ℕ} {N N' : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N)) (q : N ≅ N') :
    kernel (sectionContraction e d) ≅ kernel (sectionContraction (fun i => e i ≫ q.hom) d) :=
  kernel.mapIso _ _ (Iso.refl _) (biproduct.mapIso (fun _ => q))
    (by simpa using sectionContraction_postcompose e q.hom d)

@[simp, reassoc] theorem contractionTargetKernelIso_hom_ι {n d : ℕ} {N N' : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N)) (q : N ≅ N') :
    (contractionTargetKernelIso (d := d) e q).hom ≫
      kernel.ι (sectionContraction (fun i => e i ≫ q.hom) d) =
        kernel.ι (sectionContraction e d) := by
  simp [contractionTargetKernelIso]

/-- The evaluation relation is preserved by changing the target frame. -/
theorem kernelColumns_postcompose {m n : ℕ} {N N' : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N)) (q : N ⟶ N')
    (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (hc : ∀ j, ∑ i, (c j ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ e i = 0) :
    ∀ j, ∑ i, (c j ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ (e i ≫ q) = 0 := by
  intro j
  simpa only [Preadditive.sum_comp, Category.assoc, zero_comp] using
    congrArg (fun a => a ≫ q) (hc j)

/-- The canonical monomial map itself is independent of the target's chosen frame. -/
theorem splitMonomialKernelMap_targetIso {m n d : ℕ} {N N' : X.Modules}
    (e : Fin (n+1) → (Line.Bundles.structureModule X ⟶ N)) (q : N ≅ N')
    (L : Fin m → Line.Bundles.LineBundle X)
    (c : ∀ j, (L j).sheaf ⟶ homogeneousFreeSheaf (X := X) n 1)
    (hc : ∀ j, ∑ i, (c j ≫ biproduct.π _ (wordMonomial (fun _ : Fin 1 => i))) ≫ e i = 0) :
    splitMonomialKernelMap (d := d) e L c hc ≫ (contractionTargetKernelIso e q).hom =
      splitMonomialKernelMap (d := d) (fun i => e i ≫ q.hom) L c
        (kernelColumns_postcompose e q.hom L c hc) := by
  apply (cancel_mono (kernel.ι (sectionContraction (fun i => e i ≫ q.hom) d))).mp
  simp only [Category.assoc, contractionTargetKernelIso_hom_ι, splitMonomialKernelMap_ι]

end SteinerGeometry
