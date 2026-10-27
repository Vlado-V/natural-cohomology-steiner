import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Additive functors preserve kernels of split epimorphisms -/
noncomputable section
namespace SteinerGeometry.SplitKernelFunctor
open CategoryTheory CategoryTheory.Limits

universe u₁ u₂ v₁ v₂
variable {C : Type u₁} [Category.{v₁} C] [Abelian C]
variable {D : Type u₂} [Category.{v₂} D] [Abelian D]
variable {X Y : C} (f : X ⟶ Y) [IsSplitEpi f]

/-- The projection onto the actual kernel determined by a splitting of `f`. -/
def retraction : X ⟶ kernel f :=
  kernel.lift f (𝟙 X - f ≫ section_ f) (by simp [Preadditive.sub_comp, Category.assoc])

@[simp, reassoc] theorem retraction_ι :
    retraction f ≫ kernel.ι f = 𝟙 X - f ≫ section_ f :=
  kernel.lift_ι _ _ _

@[simp, reassoc] theorem ι_retraction :
    kernel.ι f ≫ retraction f = 𝟙 (kernel f) := by
  apply (cancel_mono (kernel.ι f)).1
  rw [Category.assoc, retraction_ι, Preadditive.comp_sub]
  simp

/-- The mapped kernel fork remains a kernel because its explicit splitting
identities are preserved by an additive functor. -/
def mappedKernelIsLimit (F : C ⥤ D) [F.Additive] :
    IsLimit (KernelFork.ofι (F.map (kernel.ι f))
      (show F.map (kernel.ι f) ≫ F.map f = 0 by
        rw [← F.map_comp, kernel.condition, F.map_zero])) := by
  apply KernelFork.IsLimit.ofι _ _ (fun g _ => g ≫ F.map (retraction f))
  · intro W g hg
    rw [Category.assoc, ← F.map_comp, retraction_ι, F.map_sub, F.map_id, F.map_comp,
      Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hg, zero_comp, sub_zero]
  · intro W g hg m hm
    rw [← hm, Category.assoc, ← F.map_comp, ι_retraction, F.map_id, Category.comp_id]

/-- Every additive functor between abelian categories preserves the kernel
of a split epimorphism. -/
theorem preservesKernel (F : C ⥤ D) [F.Additive] :
    PreservesLimit (parallelPair f 0) F := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsKernel f)
  exact (isLimitMapConeForkEquiv' F (kernel.condition f)).symm (mappedKernelIsLimit f F)

/-- The canonical comparison, rather than merely an unrelated kernel
isomorphism, is invertible. -/
theorem kernelComparison_isIso (F : C ⥤ D) [F.Additive] :
    IsIso (kernelComparison f F) := by
  let := preservesKernel f F
  infer_instance

universe u₃ v₃
variable {E : Type u₃} [Category.{v₃} E] [Abelian E]

omit [IsSplitEpi f] in
/-- Canonical kernel comparisons compose exactly. -/
theorem kernelComparison_comp (F : C ⥤ D) [F.Additive]
    (G : D ⥤ E) [G.Additive] :
    G.map (kernelComparison f F) ≫ kernelComparison (F.map f) G =
      kernelComparison f (F ⋙ G) := by
  apply (cancel_mono (kernel.ι ((F ⋙ G).map f))).1
  change (G.map (kernelComparison f F) ≫ kernelComparison (F.map f) G) ≫
      kernel.ι (G.map (F.map f)) =
    kernelComparison f (F ⋙ G) ≫ kernel.ι ((F ⋙ G).map f)
  calc
    _ = G.map (kernelComparison f F) ≫ G.map (kernel.ι (F.map f)) := by
      rw [Category.assoc, kernelComparison_comp_ι]
    _ = G.map (kernelComparison f F ≫ kernel.ι (F.map f)) := (G.map_comp _ _).symm
    _ = G.map (F.map (kernel.ι f)) := by rw [kernelComparison_comp_ι]
    _ = _ := (kernelComparison_comp_ι f (F ⋙ G)).symm

omit [IsSplitEpi f] in
/-- If the second functor and the composite preserve the relevant kernel,
the second functor sends the first comparison to an isomorphism. -/
theorem map_kernelComparison_isIso (F : C ⥤ D) [F.Additive]
    (G : D ⥤ E) [G.Additive]
    [IsIso (kernelComparison (F.map f) G)]
    [IsIso (kernelComparison f (F ⋙ G))] :
    IsIso (G.map (kernelComparison f F)) := by
  have : IsIso (G.map (kernelComparison f F) ≫ kernelComparison (F.map f) G) := by
    rw [kernelComparison_comp f F G]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (kernelComparison (F.map f) G)

end SteinerGeometry.SplitKernelFunctor
