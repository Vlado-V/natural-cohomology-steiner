import SteinerGeometry.DualAffinePresentation

/-! Actual local splitting of the dual evaluation from a locally split presentation. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u

local instance dualEvaluationLocalSplitBiproducts (X : Scheme.{u}) :
    HasFiniteBiproducts X.Modules := HasFiniteBiproducts.of_hasFiniteProducts

/-- A split epimorphism remains split after the canonical restriction/pullback identification. -/
theorem openPullback_splitEpi_of_restrict_splitEpi {X Y : Scheme.{u}}
    (a : Y ⟶ X) [IsOpenImmersion a] {M N : X.Modules} (e : M ⟶ N)
    [IsSplitEpi ((Scheme.Modules.restrictFunctor a).map e)] :
    IsSplitEpi ((Scheme.Modules.pullback a).map e) := by
  let h := Scheme.Modules.restrictFunctorIsoPullback a
  have he : (h.inv.app M ≫ (Scheme.Modules.restrictFunctor a).map e) ≫ h.hom.app N =
      (Scheme.Modules.pullback a).map e := by
    rw [Category.assoc, h.hom.naturality e]
    simp only [Iso.inv_hom_id_app_assoc]
  rw [← he]
  infer_instance

/-- A local retraction of the original line inclusion gives a local section of evaluation. -/
theorem openPullback_evaluation_splitEpi {X Y : Scheme.{u}}
    (a : Y ⟶ X) [IsOpenImmersion a] {m : ℕ}
    (R : Line.Bundles.LineBundle X) (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    [IsSplitMono ((Scheme.Modules.restrictFunctor a).map i)] :
    IsSplitEpi ((Scheme.Modules.pullback a).map (DualEvaluation.evaluation R i)) := by
  have := SheafDual.restrict_dualMap_splitEpi a i
  have : IsSplitEpi ((Scheme.Modules.restrictFunctor a).map
      (DualEvaluation.evaluation R i)) := by
    change IsSplitEpi ((Scheme.Modules.restrictFunctor a).map
      ((DualEvaluation.freeDualIso m).inv ≫ SheafDual.dualMap i))
    rw [Functor.map_comp]
    infer_instance
  exact openPullback_splitEpi_of_restrict_splitEpi a (DualEvaluation.evaluation R i)

/-- The local splitting follows from the genuine short exact presentation and
    projectivity of its quotient on the given affine charts. -/
theorem evaluation_locallySplit_of_affine_presentation {X : Scheme.{u}} {m : ℕ}
    (R : Line.Bundles.LineBundle X) {Q : X.Modules} [Q.IsQuasicoherent]
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (p : DualEvaluation.freeSheaf m ⟶ Q) (w : i ≫ p = 0)
    (hS : (ShortComplex.mk i p w).ShortExact)
    {I : Type*} (U : I → X.Opens)
    (haff : ∀ j, IsAffine (U j).toScheme)
    (hproj : ∀ j, Module.Projective Γ((U j).toScheme, ⊤)
      Γ((Scheme.Modules.restrictFunctor (U j).ι).obj Q, ⊤)) :
    ∀ j, IsSplitEpi ((Scheme.Modules.pullback (U j).ι).map
      (DualEvaluation.evaluation R i)) := by
  have : (DualEvaluation.freeSheaf (X := X) m).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (biproduct.isoCoproduct (fun _ : Fin m => Line.Bundles.structureModule X)).symm
      (OAI.AlgebraicGeometry.SheafCohomology.Projective.Quasicoherent.Scheme.Modules.isQuasicoherent_coproduct
        _ (fun _ => (Line.Bundles.LineBundle.trivial X).isQuasicoherent))
  let S := ShortComplex.mk i p w
  intro j
  let F := Scheme.Modules.restrictFunctor (U j).ι
  have : IsAffine (U j).toScheme := haff j
  have : Module.Projective Γ((U j).toScheme, ⊤) Γ(F.obj S.X₃, ⊤) := hproj j
  have : PreservesLimits F :=
    Module.RestrictionLimits.moduleRestrictFunctor_preservesLimits (U j).ι
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  have hm : (S.map F).ShortExact :=
    { exact := hS.exact.map_of_mono_of_preservesKernel F inferInstance inferInstance
      mono_f := by change Mono (F.map S.f); infer_instance
      epi_g := by change Epi (F.map S.g); infer_instance }
  have : IsSplitEpi (F.map S.g) := AffineSplitting.epi_split_of_projective_sections (F.map S.g)
  have : IsSplitEpi (S.map F).g := inferInstanceAs (IsSplitEpi (F.map S.g))
  have : IsSplitMono (F.map i) := first_split_of_last_split (S.map F) hm
  exact openPullback_evaluation_splitEpi (U j).ι R i

end SteinerGeometry
