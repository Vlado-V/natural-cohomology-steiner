module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Finiteness.Basic

set_option backward.privateInPublic true
@[expose] public section

/-! Kernels of surjections from finite projective modules onto projective modules. -/
noncomputable section
namespace SteinerGeometry.KernelFiniteProjective
universe u v w
variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- A split surjection exhibits its kernel as an actual linear retract. -/
def kernelRetraction (f : M →ₗ[R] N) (s : N →ₗ[R] M) (hs : f.comp s = .id) :
    M →ₗ[R] f.ker :=
  (LinearMap.id - s.comp f).codRestrict f.ker (fun x => by
    change f (x - s (f x)) = 0
    rw [map_sub, ← LinearMap.comp_apply, hs, LinearMap.id_apply, sub_self])

@[simp] theorem kernelRetraction_subtype (f : M →ₗ[R] N) (s : N →ₗ[R] M)
    (hs : f.comp s = .id) :
    (kernelRetraction f s hs).comp f.ker.subtype = .id := by
  ext x
  change (x : M) - s (f x) = x
  rw [x.property, map_zero, sub_zero]

/-- No noetherian hypothesis is needed: splitting provides finite generation. -/
theorem finite_ker_of_surjective [Module.Finite R M] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Finite R f.ker := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  let p := kernelRetraction f s hs
  apply Module.Finite.of_surjective p
  intro x
  exact ⟨x, DFunLike.congr_fun (kernelRetraction_subtype f s hs) x⟩

/-- The kernel is a direct summand of its projective source. -/
theorem projective_ker_of_surjective [Module.Projective R M] [Module.Projective R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) : Module.Projective R f.ker := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  exact Module.Projective.of_split f.ker.subtype (kernelRetraction f s hs)
    (kernelRetraction_subtype f s hs)

end SteinerGeometry.KernelFiniteProjective
