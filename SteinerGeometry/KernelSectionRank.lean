import SteinerGeometry.KernelSectionRankOne

/-! Exact rank of sections of a kernel of an affine finite-free epimorphism. -/
noncomputable section
namespace SteinerGeometry.KernelSectionRank
open CategoryTheory AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u

theorem kernel_sections_rank_add {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] (I J : Type u) [Finite I] [Finite J]
    (eM : M ≅ SheafOfModules.free I) (eN : N ≅ SheafOfModules.free J)
    (p : PrimeSpectrum Γ(X,⊤)) :
    Module.rankAtStalk Γ(CategoryTheory.Limits.kernel f,⊤) p + Nat.card J = Nat.card I := by
  classical
  let : Fintype I := Fintype.ofFinite _
  let : Fintype J := Fintype.ofFinite _
  let R := Γ(X,⊤)
  let fΓ : Γ(M,⊤) →ₗ[R] Γ(N,⊤) := (f.val.app (op ⊤)).hom
  have : Nontrivial R := nontrivial_of_ne (0 : R) 1 (by
    intro h
    apply p.isPrime.one_notMem
    rw [← h]
    exact p.asIdeal.zero_mem)
  have := KernelSheafSections.sections_finite_of_freeIso M I eM
  have := KernelSheafSections.sections_projective_of_freeIso M I eM
  have := KernelSheafSections.sections_projective_of_freeIso N J eN
  have hs : Function.Surjective fΓ :=
    Quasicoherent.Scheme.Modules.isQuasicoherent_surjective_of_epi f
  obtain ⟨s, hs⟩ := Module.projective_lifting_property fΓ LinearMap.id hs
  have h := KernelRank.rankAtStalk_kernel_add fΓ s hs p
  have hk := congrFun (Module.rankAtStalk_eq_of_equiv
    (KernelSheafSections.sectionsKernelEquiv f ⊤)) p
  let em : Γ(M,⊤) ≃ₗ[R] (I → R) :=
    (KernelSectionRankOne.freeSectionIso M I eM).toLinearEquiv
  let en : Γ(N,⊤) ≃ₗ[R] (J → R) :=
    (KernelSectionRankOne.freeSectionIso N J eN).toLinearEquiv
  have hm := congrFun (Module.rankAtStalk_eq_of_equiv em) p
  have hn := congrFun (Module.rankAtStalk_eq_of_equiv en) p
  rw [← hk, hm, hn] at h
  simp only [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_fintype_fun_eq_card] at h
  change Module.rankAtStalk Γ(CategoryTheory.Limits.kernel f,⊤) p + Fintype.card J =
    Fintype.card I at h
  simpa only [Nat.card_eq_fintype_card] using h

end SteinerGeometry.KernelSectionRank
