module

public import SteinerGeometry.CurveBundleRankLocus
public import SteinerGeometry.CurveRationalPoints
public import SteinerGeometry.CurveSectionEvaluation
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections

set_option backward.privateInPublic true
@[expose] public section

/-! Fixed rank-plus-one generating tuples on integral algebraic curves. -/

namespace SteinerGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]
variable {C : Scheme} [IsIntegral C] [IsNoetherian C]

local instance curveGeneratorsBiproducts (Y : Scheme) : HasFiniteBiproducts Y.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- On a finite-type integral curve over an algebraically closed infinite field,
pointwise generation of an actual rank-n locally free module sheaf can be
achieved by one fixed n+1 tuple of its actual global sections. -/
theorem exists_curve_generators
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (hd : topologicalKrullDim C ≤ 1) (E : C.Modules)
    (n : ℕ) (hn : 0 < n)
    (hframe : ∀ a : CurveRationalPoint p, ∃ U : C.Opens, a.val (⊥ : PrimeSpectrum K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅
        ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf))
    (hgenerated : ∀ a : CurveRationalPoint p,
      Function.Surjective (curveSectionEvaluation p E a.val)) :
    ∃ s : Fin (n + 1) → CurveSectionSpace p E,
      ∀ a : CurveRationalPoint p,
        Submodule.span K (Set.range (fun i => curveSectionEvaluation p E a.val (s i))) = ⊤ := by
  exact exists_bundle_rank_succ_generators hd p E
    (fun a : CurveRationalPoint p => a.val) (fun a => a.property)
    (CurveRationalPoint.underlying_injective p) n hn
    hframe hgenerated

/-- The same tuple expressed as actual morphisms from the structure sheaf. -/
theorem exists_curve_generator_morphisms
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (hd : topologicalKrullDim C ≤ 1) (E : C.Modules)
    (n : ℕ) (hn : 0 < n)
    (hframe : ∀ a : CurveRationalPoint p, ∃ U : C.Opens, a.val (⊥ : PrimeSpectrum K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅
        ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf))
    (hgenerated : ∀ a : CurveRationalPoint p,
      Function.Surjective (curveSectionEvaluation p E a.val)) :
    ∃ s : Fin (n + 1) → (SheafOfModules.unit C.ringCatSheaf ⟶ E),
      ∀ a : CurveRationalPoint p,
        Submodule.span K (Set.range (fun i =>
          curveSectionEvaluation p E a.val
            (Scheme.Modules.Hom.app (s i) ⊤ (1 : Γ(C, ⊤))))) = ⊤ := by
  obtain ⟨s, hs⟩ := exists_curve_generators p hd E n hn hframe hgenerated
  let e := OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.Sections.moduleSectionHomEquiv E
  refine ⟨fun i => e.symm (s i), fun a => ?_⟩
  have he (i : Fin (n + 1)) :
      Scheme.Modules.Hom.app (e.symm (s i)) ⊤ (1 : Γ(C, ⊤)) = s i :=
    e.apply_symm_apply (s i)
  simpa only [he] using hs a

end
end SteinerGeometry
