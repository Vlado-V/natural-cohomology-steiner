import SteinerGeometry.AffineSplitting
import SteinerGeometry.DualRestriction
import SteinerGeometry.DualEvaluation
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Module.RestrictionLimits
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence

/-! Duals of locally split affine presentations are epimorphic. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance dualAffinePresentationBiproducts (X : Scheme.{u}) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

theorem dualMap_epi_of_affine_presentation {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    (haff : ∀ i, IsAffine (U i).toScheme)
    (hproj : ∀ i, Module.Projective Γ((U i).toScheme, ⊤)
      Γ((Scheme.Modules.restrictFunctor (U i).ι).obj S.X₃, ⊤)) :
    Epi (SheafDual.dualMap S.f) := by
  apply SheafDual.dualMap_epi_of_local_split S.f U hU
  intro i
  let F := Scheme.Modules.restrictFunctor (U i).ι
  haveI : IsAffine (U i).toScheme := haff i
  haveI : Module.Projective Γ((U i).toScheme, ⊤) Γ(F.obj S.X₃, ⊤) := hproj i
  haveI : PreservesLimits F := Module.RestrictionLimits.moduleRestrictFunctor_preservesLimits (U i).ι
  haveI : Mono S.f := hS.mono_f
  haveI : Epi S.g := hS.epi_g
  have hm : (S.map F).ShortExact :=
    { exact := hS.exact.map_of_mono_of_preservesKernel F inferInstance inferInstance
      mono_f := by change Mono (F.map S.f); infer_instance
      epi_g := by change Epi (F.map S.g); infer_instance }
  haveI : IsSplitEpi (F.map S.g) := AffineSplitting.epi_split_of_projective_sections (F.map S.g)
  haveI : IsSplitEpi (S.map F).g := inferInstanceAs (IsSplitEpi (F.map S.g))
  exact first_split_of_last_split (S.map F) hm

theorem dualEvaluation_epi_of_affine_presentation {X : Scheme.{u}} {m : ℕ}
    (R : Line.Bundles.LineBundle X) {Q : X.Modules} [Q.IsQuasicoherent]
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (p : DualEvaluation.freeSheaf m ⟶ Q) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk i p w).ShortExact)
    {ι : Type*} (U : ι → X.Opens) (hU : ∀ x : X, ∃ j, x ∈ U j)
    (haff : ∀ j, IsAffine (U j).toScheme)
    (hproj : ∀ j, Module.Projective Γ((U j).toScheme, ⊤)
      Γ((Scheme.Modules.restrictFunctor (U j).ι).obj Q, ⊤)) :
    Epi (DualEvaluation.evaluation R i) := by
  haveI : (DualEvaluation.freeSheaf (X := X) m).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (biproduct.isoCoproduct (fun _ : Fin m => Line.Bundles.structureModule X)).symm
      (OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct
        _ (fun _ => (Line.Bundles.LineBundle.trivial X).isQuasicoherent))
  haveI := dualMap_epi_of_affine_presentation (ShortComplex.mk i p w) hS U hU haff hproj
  exact inferInstanceAs (Epi ((DualEvaluation.freeDualIso m).inv ≫ SheafDual.dualMap i))

end SteinerGeometry
