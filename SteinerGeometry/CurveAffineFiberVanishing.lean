import SteinerGeometry.CurveMatrixRankOpen
import SteinerGeometry.SupportFieldFiber
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.GeometricSections
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.BasicOpenAnnihilation

namespace SteinerGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TensorProduct
open AlgebraicGeometry.Scheme.Modules
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

variable {K : Type} [Field K]

/-- Nakayama in actual affine sheaf coordinates: if a finite-type coherent
module has zero pullback at a field point, it vanishes near that point. -/
theorem affine_mem_vanishingOpen_of_pullback_isZero
    {X : Scheme} [IsAffine X] (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (a : Spec (.of K) ⟶ X) (hz : IsZero ((Scheme.Modules.pullback a).obj M)) :
    a (⊥ : PrimeSpectrum K) ∈ Module.VanishingOpen.moduleVanishingOpen M := by
  let R := Γ(X, ⊤)
  let S := Γ(Spec (.of K), ⊤)
  let : Field S := ((Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toMulEquiv.isField
    (Field.toIsField K)).toField
  let φ : R →+* S := a.appTop.hom
  let : Module.Finite R Γ(M, ⊤) :=
    Affine.QuasicoherentFiniteTypeSections.affine_quasicoherent_finiteType_sections_finite M
  have hs : Subsingleton Γ((Scheme.Modules.pullback a).obj M, ⊤) :=
    Affine.ModuleZeroCriterion.module_sections_subsingleton_of_isZero _ hz ⊤
  let : Subsingleton ((Affine.SectionAdjunction.AffineSectionAdjunction.sections
      (Spec (.of K))).obj ((Scheme.Modules.pullback a).obj M)) :=
    ⟨fun x y => hs.elim x y⟩
  have ht : Subsingleton ((ModuleCat.extendScalars φ).obj
      ((Affine.SectionAdjunction.AffineSectionAdjunction.sections X).obj M)) :=
    (Affine.GeometricSections.AffineGeometricSections.iso a M).toLinearEquiv.injective.subsingleton
  let : Algebra R S := φ.toAlgebra
  have ht' : Subsingleton (S ⊗[R] Γ(M, ⊤)) := ht
  have hnot : ¬ Module.annihilator R Γ(M, ⊤) ≤ RingHom.ker φ := by
    intro hle
    have hm : (⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩ : PrimeSpectrum R) ∈
        Module.support R Γ(M, ⊤) :=
      (Module.mem_support_iff_of_finite (R := R) (M := Γ(M, ⊤))
        (p := ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩)).mpr hle
    have hn := (SupportFieldFiber.mem_support_iff_nontrivial_fieldTensor Γ(M, ⊤) φ).mp hm
    exact (not_nontrivial_iff_subsingleton.mpr ht') hn
  obtain ⟨r, hr, hrφ⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have hx : a (⊥ : PrimeSpectrum K) ∈ X.basicOpen r :=
    (Matrix.RankLowerOpen.range_subset_basicOpen_iff a r).mpr
      (isUnit_iff_ne_zero.mpr hrφ) ⟨_, rfl⟩
  have hzero : IsZero (M.restrict (X.basicOpen r).ι) :=
    (Affine.BasicOpenAnnihilation.affineModule_basicOpen_isZero_iff_pow_annihilator M r).mpr
      ⟨1, by simpa using hr⟩
  exact (Module.VanishingOpen.mem_moduleVanishingOpen M _).mpr ⟨_, hx, hzero⟩

end
end SteinerGeometry
