import SteinerGeometry.KernelLocalFreeness
import SteinerGeometry.KernelFiniteProjective
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Products

/-! Finite projective sections of the genuine sheaf kernel. -/
noncomputable section
namespace SteinerGeometry.KernelSheafSections
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
universe u

/-- Evaluation preserves kernels, so sections of the actual sheaf kernel
are exactly the algebraic kernel of the section map. -/
def sectionsKernelEquiv {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N) (U : X.Opens) :
    Γ(kernel f, U) ≃ₗ[Γ(X, U)]
      (show Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) from (f.val.app (op U)).hom).ker :=
by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op U)
  letI : F.Additive := { map_add := by intros; rfl }
  exact ((PreservesKernel.iso F f) ≪≫ ModuleCat.kernelIsoKer _).toLinearEquiv

theorem kernel_sections_finite {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) [Module.Finite Γ(X, U) Γ(M, U)]
    [Module.Projective Γ(X, U) Γ(N, U)]
    (hf : Function.Surjective (f.val.app (op U))) :
    Module.Finite Γ(X, U) Γ(kernel f, U) := by
  let fU : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) := (f.val.app (op U)).hom
  have : Module.Finite Γ(X, U) fU.ker :=
    KernelFiniteProjective.finite_ker_of_surjective fU hf
  exact Module.Finite.equiv (sectionsKernelEquiv f U).symm

theorem kernel_sections_projective {X : Scheme.{u}} {M N : X.Modules} (f : M ⟶ N)
    (U : X.Opens) [Module.Projective Γ(X, U) Γ(M, U)]
    [Module.Projective Γ(X, U) Γ(N, U)]
    (hf : Function.Surjective (f.val.app (op U))) :
    Module.Projective Γ(X, U) Γ(kernel f, U) := by
  let fU : Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) := (f.val.app (op U)).hom
  have : Module.Projective Γ(X, U) fU.ker :=
    KernelFiniteProjective.projective_ker_of_surjective fU hf
  exact Module.Projective.of_equiv (sectionsKernelEquiv f U).symm


/-- Global sections of a finite free sheaf are the expected finite free module. -/
def freeSectionsEquiv (X : Scheme.{u}) (I : Type u) [Finite I] :
    Γ((show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) I), ⊤) ≃ₗ[Γ(X, ⊤)] (I → Γ(X, ⊤)) := by
  let F := SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let U := fun _ : I => SheafOfModules.unit X.ringCatSheaf
  letI : F.Additive := { map_add := by intros; rfl }
  letI : HasBiproduct U := HasBiproduct.of_hasCoproduct U
  letI : PreservesLimit (Discrete.functor U) F := by dsimp [F]; infer_instance
  letI : PreservesBiproduct U F := preservesBiproduct_of_preservesProduct F
  let e : F.obj (SheafOfModules.free I) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op ⊤)) (∀ i, F.obj (U i)) :=
    F.mapIso (biproduct.isoCoproduct U).symm ≪≫ F.mapBiproduct U ≪≫
      biproduct.isoProduct (F.obj ∘ U) ≪≫ ModuleCat.piIsoPi (F.obj ∘ U)
  exact e.toLinearEquiv

/-- Finite free local frames give projective sections on the framed open. -/
theorem sections_projective_of_freeIso {X : Scheme.{u}} (M : X.Modules)
    (I : Type u) [Finite I] (e : M ≅ (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) I)) :
    Module.Projective Γ(X, ⊤) Γ(M, ⊤) := by
  let Γe := (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso e
  let eΓ : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)]
      Γ((show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) I), ⊤) :=
    Γe.toLinearEquiv
  exact Module.Projective.of_equiv' ((freeSectionsEquiv X I).symm ≪≫ₗ eΓ.symm)

theorem sections_finite_of_freeIso {X : Scheme.{u}} (M : X.Modules)
    (I : Type u) [Finite I] (e : M ≅ (show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) I)) :
    Module.Finite Γ(X, ⊤) Γ(M, ⊤) := by
  let Γe := (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso e
  let eΓ : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)]
      Γ((show X.Modules from SheafOfModules.free (R := X.ringCatSheaf) I), ⊤) :=
    Γe.toLinearEquiv
  exact Module.Finite.equiv ((freeSectionsEquiv X I).symm ≪≫ₗ eΓ.symm)

end SteinerGeometry.KernelSheafSections
