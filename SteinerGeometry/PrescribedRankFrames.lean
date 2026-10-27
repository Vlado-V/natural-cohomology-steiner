module

public import SteinerGeometry.FiniteLocalFrames
public import Mathlib.Data.Fintype.EquivFin

set_option backward.privateInPublic true
@[expose] public section

/-! Finite-projective affine modules of a prescribed stalk rank have frames of that rank. -/
noncomputable section
namespace SteinerGeometry.PrescribedRankFrames
open CategoryTheory AlgebraicGeometry TopologicalSpace Module
open TildeFiniteProjective
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

theorem chooseLocalBasis_card {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] (p : PrimeSpectrum R) :
    Nat.card (chooseLocalBasis M p).Index = Module.rankAtStalk M p := by
  let S := p.asIdeal.primeCompl
  let Rₚ := Localization.AtPrime p.asIdeal
  let Mₚ := LocalizedModule S M
  let : Module.Finite Rₚ Mₚ :=
    Module.Finite.of_isLocalizedModule S (Rₚ := Rₚ) (LocalizedModule.mkLinearMap S M)
  let : Module.Free Rₚ Mₚ := Module.free_of_flat_of_isLocalRing
  let : Fintype (Module.Free.ChooseBasisIndex Rₚ Mₚ) := Fintype.ofFinite _
  change Nat.card (Module.Free.ChooseBasisIndex Rₚ Mₚ) = Module.finrank Rₚ Mₚ
  rw [Nat.card_eq_fintype_card]
  exact (Module.finrank_eq_card_basis (Module.Free.chooseBasis Rₚ Mₚ)).symm

/-- The principal-open basis used by the finite-projective construction can
be reindexed by the exact prescribed finite rank. -/
def tildeFrameCover {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.Projective R M] (r : ℕ)
    (hr : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) :
    FiniteGeometricFrameCover (tilde M) where
  I := PrimeSpectrum R
  U p := PrimeSpectrum.basicOpen (chooseLocalBasis M p).scalar
  covers := (finiteFramesTilde M).covers
  Q _ := ULift.{u} (Fin r)
  frame p := by
    let b := chooseLocalBasis M p
    letI : Finite b.Index := b.finite
    letI : Fintype b.Index := Fintype.ofFinite _
    have hc : Fintype.card b.Index = r := by
      rw [← Nat.card_eq_fintype_card]
      exact (chooseLocalBasis_card M p).trans (hr p)
    let e : b.Index ≃ ULift.{u} (Fin r) :=
      (Fintype.equivFinOfCardEq hc).trans Equiv.ulift.symm
    exact basicOpenFreeTrivialization M b.scalar b.Index b.basis.repr ≪≫
      (SheafOfModules.freeFunctor (R :=
        (Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen b.scalar)).ringCatSheaf)).mapIso e.toIso
  finite _ := inferInstance

/-- A quasi-coherent sheaf on an affine scheme inherits exact-rank finite
frames from its native module of global sections. -/
def affineFrameCover (X : Scheme.{u}) [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    [Module.Finite Γ(X,⊤) Γ(M,⊤)] [Module.Projective Γ(X,⊤) Γ(M,⊤)]
    (r : ℕ) (hr : ∀ p : PrimeSpectrum Γ(X,⊤), Module.rankAtStalk Γ(M,⊤) p = r) :
    FiniteGeometricFrameCover M := by
  let A := (Affine.SectionAdjunction.AffineSectionAdjunction.sections X).obj M
  have : Module.Finite Γ(X,⊤) A := inferInstanceAs (Module.Finite Γ(X,⊤) Γ(M,⊤))
  have : Module.Projective Γ(X,⊤) A := inferInstanceAs (Module.Projective Γ(X,⊤) Γ(M,⊤))
  exact ((tildeFrameCover A r hr).pullback X.toSpecΓ).mapIso
    (Affine.SectionCounit.AffineSectionAdjunction.counitIso X M)

theorem affineFrameCover_index (X : Scheme.{u}) [IsAffine X] (M : X.Modules) [M.IsQuasicoherent]
    [Module.Finite Γ(X,⊤) Γ(M,⊤)] [Module.Projective Γ(X,⊤) Γ(M,⊤)]
    (r : ℕ) (hr : ∀ p : PrimeSpectrum Γ(X,⊤), Module.rankAtStalk Γ(M,⊤) p = r)
    (i : (affineFrameCover X M r hr).I) :
    (affineFrameCover X M r hr).Q i = ULift.{u} (Fin r) := rfl

theorem affine_frame_of_sections_rank (X : Scheme.{u}) [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent]
    [Module.Finite Γ(X,⊤) Γ(M,⊤)] [Module.Projective Γ(X,⊤) Γ(M,⊤)]
    (r : ℕ) (hr : ∀ p : PrimeSpectrum Γ(X,⊤), Module.rankAtStalk Γ(M,⊤) p = r)
    (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin r))) := by
  let D := affineFrameCover X M r hr
  obtain ⟨i, hi⟩ := (IsOpenCover.mk D.covers).exists_mem x
  exact ⟨D.U i, hi, ⟨D.frame i⟩⟩

end SteinerGeometry.PrescribedRankFrames
