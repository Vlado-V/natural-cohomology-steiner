import SteinerGeometry.AffineSplitting
import SteinerGeometry.KernelSheafSections

/-! # Local splittings of epimorphisms with finite free targets -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory AlgebraicGeometry
universe u

/-- On an affine scheme, an actual quasicoherent epimorphism with a finite
free target splits. There is no finiteness hypothesis on its source. -/
theorem isSplitEpi_of_affine_free_target
    {X : Scheme.{u}} [IsAffine X] {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] (J : Type u) [Finite J]
    (eN : N ≅ SheafOfModules.free J) : IsSplitEpi f := by
  have := KernelSheafSections.sections_projective_of_freeIso N J eN
  exact AffineSplitting.epi_split_of_projective_sections f

/-- Affine local free target frames make a quasicoherent epimorphism split
after pullback to every chart. -/
theorem locallySplit_of_epi_free_affine_cover
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] {I : Type u} (U : I → X.Opens)
    (hU : ∀ i, IsAffine (U i).toScheme) (J : I → Type u)
    (hJ : ∀ i, Finite (J i))
    (eN : ∀ i, (Scheme.Modules.pullback (U i).ι).obj N ≅ SheafOfModules.free (J i)) :
    ∀ i, IsSplitEpi ((Scheme.Modules.pullback (U i).ι).map f) := by
  intro i
  let := hU i
  let := hJ i
  have : ((Scheme.Modules.pullback (U i).ι).obj M).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app M) inferInstance
  have : ((Scheme.Modules.pullback (U i).ι).obj N).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (U i).toScheme.ringCatSheaf).prop_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app N) inferInstance
  exact isSplitEpi_of_affine_free_target _ (J i) (eN i)

/-- The same local splitting criterion with frames stated using ordinary
restriction instead of geometric pullback. -/
theorem locallySplit_of_epi_free_affine_restrict
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [Epi f] {I : Type u} (U : I → X.Opens)
    (hU : ∀ i, IsAffine (U i).toScheme) (J : I → Type u)
    (hJ : ∀ i, Finite (J i))
    (eN : ∀ i, N.restrict (U i).ι ≅ SheafOfModules.free (J i)) :
    ∀ i, IsSplitEpi ((Scheme.Modules.pullback (U i).ι).map f) :=
  locallySplit_of_epi_free_affine_cover f U hU J hJ (fun i =>
    ((Scheme.Modules.restrictFunctorIsoPullback (U i).ι).app N).symm ≪≫ eN i)

end SteinerGeometry
