import SteinerGeometry.KernelRank
import SteinerGeometry.KernelSheafSections
import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent

/-! # Rank one for sections of the genuine kernel of an affine epimorphism -/
noncomputable section
namespace SteinerGeometry.KernelSectionRankOne
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u

def freeSectionIso {X : Scheme.{u}} (M : X.Modules) (I : Type u) [Finite I]
    (e : M ≅ SheafOfModules.free I) :
    (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).obj M ≅
      ModuleCat.of Γ(X, ⊤) (I → Γ(X, ⊤)) :=
  (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).mapIso e ≪≫
    (KernelSheafSections.freeSectionsEquiv X I).toModuleIso

theorem kernel_sections_rank_one {X : Scheme} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] (n : ℕ)
    (eM : M ≅ SheafOfModules.free (Fin (n + 1)))
    (eN : N ≅ SheafOfModules.free (Fin n))
    (p : PrimeSpectrum Γ(X, ⊤)) :
    Module.rankAtStalk Γ(kernel f, ⊤) p = 1 := by
  let G : X.Modules ⥤ ModuleCat Γ(X, ⊤) :=
    SheafOfModules.evaluation X.ringCatSheaf (op ⊤)
  let : G.Additive := { map_add := by intros; rfl }
  let e₁ := freeSectionIso M (Fin (n + 1)) eM
  let e₂ := freeSectionIso N (Fin n) eN
  let f' : (Fin (n + 1) → Γ(X, ⊤)) →ₗ[Γ(X, ⊤)] (Fin n → Γ(X, ⊤)) :=
    (e₁.inv ≫ G.map f ≫ e₂.hom).hom
  have hs : Function.Surjective (G.map f).hom :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_surjective_of_epi f
  have hs' : Function.Surjective f' := by
    intro y
    obtain ⟨x, hx⟩ := hs (e₂.toLinearEquiv.symm y)
    refine ⟨e₁.toLinearEquiv x, ?_⟩
    change e₂.toLinearEquiv ((G.map f).hom
      (e₁.toLinearEquiv.symm (e₁.toLinearEquiv x))) = y
    rw [LinearEquiv.symm_apply_apply, hx, LinearEquiv.apply_symm_apply]
  let eker : Γ(kernel f, ⊤) ≃ₗ[Γ(X, ⊤)] f'.ker :=
    (KernelSheafSections.sectionsKernelEquiv f ⊤).trans
      (((ModuleCat.kernelIsoKer (G.map f)).symm ≪≫
        kernel.mapIso (G.map f) (ModuleCat.ofHom f') e₁ e₂ (by
          dsimp [f']
          simp) ≪≫ ModuleCat.kernelIsoKer (ModuleCat.ofHom f')).toLinearEquiv)
  have : Nontrivial Γ(X, ⊤) := nontrivial_of_ne (0 : Γ(X, ⊤)) 1 (by
    intro h
    apply p.isPrime.one_notMem
    rw [← h]
    exact p.asIdeal.zero_mem)
  exact (congrFun (Module.rankAtStalk_eq_of_equiv eker) p).trans
    (KernelRank.rankAtStalk_kernel_free_succ f' hs' p)

/-- The actual kernel sections are finite projective; the rank calculation
above therefore gives finite flat rank-one affine modules. -/
theorem kernel_sections_finite_projective {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] (I J : Type u) [Finite I] [Finite J]
    (eM : M ≅ SheafOfModules.free I) (eN : N ≅ SheafOfModules.free J) :
    Module.Finite Γ(X, ⊤) Γ(kernel f, ⊤) ∧
      Module.Projective Γ(X, ⊤) Γ(kernel f, ⊤) := by
  have := KernelSheafSections.sections_finite_of_freeIso M I eM
  have := KernelSheafSections.sections_projective_of_freeIso M I eM
  have := KernelSheafSections.sections_projective_of_freeIso N J eN
  have hs := Quasicoherent.Scheme.Modules.isQuasicoherent_surjective_of_epi f
  exact ⟨KernelSheafSections.kernel_sections_finite f ⊤ hs,
    KernelSheafSections.kernel_sections_projective f ⊤ hs⟩

end SteinerGeometry.KernelSectionRankOne
