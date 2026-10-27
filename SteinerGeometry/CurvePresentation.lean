module

public import SteinerGeometry.CurveGeneratorsEpi
public import SteinerGeometry.KernelLineBundle
public import SteinerGeometry.DualAffinePresentation

set_option backward.privateInPublic true
@[expose] public section

/-! The actual rank-one relation and dual evaluation associated to a generated curve bundle. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance curvePresentationBiproducts (C : Scheme) : HasFiniteBiproducts C.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

structure CurvePresentationData {C : Scheme} (Q : C.Modules) (n : ℕ) where
  relationLine : Line.Bundles.LineBundle C
  inclusion : relationLine.sheaf ⟶ DualEvaluation.freeSheaf (n + 1)
  quotient : DualEvaluation.freeSheaf (n + 1) ⟶ Q
  zero : inclusion ≫ quotient = 0
  exact : (ShortComplex.mk inclusion quotient zero).ShortExact
  evaluation_epi : Epi (DualEvaluation.evaluation relationLine inclusion)

theorem exists_curvePresentationData {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
    {C : Scheme} [IsIntegral C] [IsNoetherian C]
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (hd : topologicalKrullDim C ≤ 1) (Q : C.Modules)
    [Q.IsQuasicoherent] [Q.IsFiniteType] (n : ℕ) (hn : 0 < n)
    (hframe : ∀ a : CurveRationalPoint p, ∃ U : C.Opens,
      a.val (⊥ : PrimeSpectrum K) ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj Q ≅
        ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf))
    (hgenerated : ∀ a : CurveRationalPoint p, Function.Surjective (curveSectionEvaluation p Q a.val))
    (hproj : ∀ U : C.Opens, IsAffineOpen U →
      Module.Projective Γ(U.toScheme, ⊤) Γ(Q.restrict U.ι, ⊤)) :
    Nonempty (CurvePresentationData Q n) := by
  obtain ⟨s, hs⟩ := exists_curve_generator_epimorphism p hd Q n hn hframe hgenerated
  haveI := hs
  let f : DualEvaluation.freeSheaf (n + 1) ⟶ Q :=
    (biproduct.isoCoproduct (fun _ : Fin (n + 1) => Line.Bundles.structureModule C)).hom ≫ Sigma.desc s
  haveI : Epi f := inferInstance
  let R := kernelLineBundleOfRationalBiproductFrames p Q n f hframe
  let i : R.sheaf ⟶ DualEvaluation.freeSheaf (n + 1) := kernel.ι f
  have hw : i ≫ f = 0 := kernel.condition f
  have hS : (ShortComplex.mk i f hw).ShortExact :=
    { exact := ShortComplex.kernelSequence_exact f
      mono_f := inferInstance
      epi_g := inferInstance }
  have he : Epi (DualEvaluation.evaluation R i) := by
    apply dualEvaluation_epi_of_affine_presentation R i f hw hS
      (fun U : C.affineOpens => U.1)
    · intro x
      exact (IsOpenCover.mk (iSup_affineOpens_eq_top C)).exists_mem x
    · intro U
      exact U.2
    · intro U
      exact hproj U.1 U.2
  exact ⟨⟨R, i, f, hw, hS, he⟩⟩

end SteinerGeometry
