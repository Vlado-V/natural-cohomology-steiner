module

public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.SectionCounit
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

set_option backward.privateInPublic true
@[expose] public section

/-! Actual splittings of affine quasicoherent epimorphisms with projective sections. -/
noncomputable section
namespace SteinerGeometry.AffineSplitting
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {X : Scheme.{u}} [IsAffine X]
variable {M N P : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [P.IsQuasicoherent]

def lift (h : (Affine.SectionAdjunction.AffineSectionAdjunction.sections X).obj M ⟶
    (Affine.SectionAdjunction.AffineSectionAdjunction.sections X).obj N) : M ⟶ N :=
  (Affine.SectionCounit.AffineSectionAdjunction.counitIso X M).inv ≫
    (Affine.SectionAdjunction.AffineSectionAdjunction.left X).map h ≫
      (Affine.SectionCounit.AffineSectionAdjunction.counitIso X N).hom

@[simp] theorem lift_id : lift (𝟙 ((Affine.SectionAdjunction.AffineSectionAdjunction.sections X).obj M)) = 𝟙 M := by
  simp [lift]

@[simp] theorem lift_comp
    (h : (Affine.SectionAdjunction.AffineSectionAdjunction.sections X).obj M ⟶
      (Affine.SectionAdjunction.AffineSectionAdjunction.sections X).obj N)
    (j : (Affine.SectionAdjunction.AffineSectionAdjunction.sections X).obj N ⟶
      (Affine.SectionAdjunction.AffineSectionAdjunction.sections X).obj P) :
    lift (h ≫ j) = lift h ≫ lift j := by
  simp [lift, Category.assoc]

@[simp] theorem lift_map (f : M ⟶ N) :
    lift ((Affine.SectionAdjunction.AffineSectionAdjunction.sections X).map f) = f := by
  unfold lift
  have h := (Affine.SectionAdjunction.AffineSectionAdjunction.adjunction X).counit.naturality f
  change (Affine.SectionAdjunction.AffineSectionAdjunction.left X).map
      ((Affine.SectionAdjunction.AffineSectionAdjunction.sections X).map f) ≫
      (Affine.SectionCounit.AffineSectionAdjunction.counitIso X N).hom =
    (Affine.SectionCounit.AffineSectionAdjunction.counitIso X M).hom ≫ f at h
  change _ ≫ ((Affine.SectionAdjunction.AffineSectionAdjunction.left X).map
    ((Affine.SectionAdjunction.AffineSectionAdjunction.sections X).map f) ≫ _) = f
  rw [h]
  simp

theorem epi_split_of_projective_sections (f : M ⟶ N) [Epi f]
    [Module.Projective Γ(X, ⊤) Γ(N, ⊤)] : IsSplitEpi f := by
  let G := Affine.SectionAdjunction.AffineSectionAdjunction.sections X
  haveI : Module.Projective Γ(X, ⊤) (G.obj N) :=
    inferInstanceAs (Module.Projective Γ(X, ⊤) Γ(N, ⊤))
  have hf : Function.Surjective (G.map f).hom :=
    OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_surjective_of_epi f
  obtain ⟨s, hs⟩ := Module.projective_lifting_property (G.map f).hom LinearMap.id hf
  have he : ModuleCat.ofHom s ≫ G.map f = 𝟙 (G.obj N) := by
    apply ModuleCat.hom_ext
    exact hs
  refine ⟨⟨lift (ModuleCat.ofHom s), ?_⟩⟩
  rw [← lift_map f, ← lift_comp]
  change lift (ModuleCat.ofHom s ≫ G.map f) = 𝟙 N
  erw [he]
  exact lift_id

end SteinerGeometry.AffineSplitting

namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits

theorem first_split_of_last_split {C : Type*} [Category C] [Abelian C]
    (S : ShortComplex C) (hS : S.ShortExact) [IsSplitEpi S.g] : IsSplitMono S.f := by
  haveI : Mono S.f := hS.mono_f
  let d : S.X₂ ⟶ S.X₂ := 𝟙 _ - S.g ≫ section_ S.g
  have hd : d ≫ S.g = 0 := by
    simp [d, Category.assoc]
  let r := hS.exact.lift d hd
  refine ⟨⟨r, ?_⟩⟩
  apply (cancel_mono S.f).mp
  change (S.f ≫ hS.exact.lift d hd) ≫ S.f = (𝟙 _) ≫ S.f
  rw [Category.assoc, hS.exact.lift_f]
  simp [d, Category.assoc, S.zero]

end SteinerGeometry
