module

public import SteinerGeometry.KernelFiniteProjective
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

set_option backward.privateInPublic true
@[expose] public section

/-! Rank of the kernel of an actual split surjection. -/
noncomputable section
namespace SteinerGeometry.KernelRank
open KernelFiniteProjective
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

def kernelProdEquiv (f : M →ₗ[R] N) (s : N →ₗ[R] M)
    (hs : f.comp s = .id) : (f.ker × N) ≃ₗ[R] M where
  toFun x := x.1 + s x.2
  invFun x := (kernelRetraction f s hs x, f x)
  map_add' x y := by simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add]; abel
  map_smul' r x := by
    change r • (x.1 : M) + s (r • x.2) = r • ((x.1 : M) + s x.2)
    rw [map_smul, smul_add]
  left_inv x := by
    apply Prod.ext
    · apply Subtype.ext
      change (x.1 : M) + s x.2 - s (f ((x.1 : M) + s x.2)) = x.1
      have hfs (y : N) : f (s y) = y := DFunLike.congr_fun hs y
      rw [map_add, x.1.property, zero_add, hfs]
      abel
    · change f ((x.1 : M) + s x.2) = x.2
      rw [map_add, x.1.property, zero_add]
      exact DFunLike.congr_fun hs x.2
  right_inv x := by
    change x - s (f x) + s (f x) = x
    abel

theorem rankAtStalk_kernel_add [Module.Finite R M] [Module.Projective R M]
    [Module.Projective R N]
    (f : M →ₗ[R] N) (s : N →ₗ[R] M) (hs : f.comp s = .id)
    (p : PrimeSpectrum R) :
    Module.rankAtStalk f.ker p + Module.rankAtStalk N p = Module.rankAtStalk M p := by
  have hf : Function.Surjective f := fun y => ⟨s y, DFunLike.congr_fun hs y⟩
  have := finite_ker_of_surjective f hf
  have := projective_ker_of_surjective f hf
  have : Module.Finite R N := Module.Finite.of_surjective f hf
  have h := congrFun (Module.rankAtStalk_eq_of_equiv (kernelProdEquiv f s hs)) p
  rw [Module.rankAtStalk_prod] at h
  exact h

theorem rankAtStalk_kernel_free_succ [Nontrivial R] {n : ℕ}
    (f : (Fin (n + 1) → R) →ₗ[R] (Fin n → R)) (hf : Function.Surjective f)
    (p : PrimeSpectrum R) : Module.rankAtStalk f.ker p = 1 := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have h := rankAtStalk_kernel_add f s hs p
  simp only [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fin_fun] at h
  change Module.rankAtStalk f.ker p + n = n + 1 at h
  omega

end SteinerGeometry.KernelRank
