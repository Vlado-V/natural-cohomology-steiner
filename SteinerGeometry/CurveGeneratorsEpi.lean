module

public import SteinerGeometry.CurveFiberVanishing
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.QuotientFiniteType
public import SteinerGeometry.CurvePointEpi
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Modules
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

variable {K : Type} [Field K] {C : Scheme}

local instance curveGeneratorsEpiBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Cokernel vanishing reduces an epimorphism to its actual rational fibers. -/
theorem epi_of_rational_pullback_epi [IsAlgClosed K]
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    {M N : C.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] [N.IsFiniteType]
    (f : M ⟶ N) (hf : ∀ a : CurveRationalPoint p, Epi ((Scheme.Modules.pullback a.val).map f)) : Epi f := by
  let Q := cokernel f
  let : Q.IsQuasicoherent := Quasicoherent.Cokernels.module_quasicoherent_cokernel f
  let : Q.IsFiniteType := Quasicoherent.QuotientFiniteType.quasicoherent_cokernel_finiteType f
  have hz : IsZero Q := isZero_of_rational_pullbacks p Q (fun a => by
    let := hf a
    exact (PreservesCokernel.iso (Scheme.Modules.pullback a.val) f).isZero_iff.mpr
      (isZero_cokernel_of_epi ((Scheme.Modules.pullback a.val).map f)))
  apply Abelian.epi_of_cokernel_π_eq_zero
  exact hz.eq_of_tgt _ _

/-- The fixed rank-plus-one tuple is an epimorphism of actual module sheaves. -/
theorem exists_curve_generator_epimorphism [Infinite K] [IsAlgClosed K]
    [IsIntegral C] [IsNoetherian C]
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (hd : topologicalKrullDim C ≤ 1) (E : C.Modules)
    [E.IsQuasicoherent] [E.IsFiniteType]
    (n : ℕ) (hn : 0 < n)
    (hframe : ∀ a : CurveRationalPoint p, ∃ U : C.Opens, a.val (⊥ : PrimeSpectrum K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj E ≅
        ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf))
    (hgenerated : ∀ a : CurveRationalPoint p,
      Function.Surjective (curveSectionEvaluation p E a.val)) :
    ∃ s : Fin (n + 1) → (SheafOfModules.unit C.ringCatSheaf ⟶ E), Epi (Sigma.desc s) := by
  obtain ⟨s, hs⟩ := exists_curve_generator_morphisms p hd E n hn hframe hgenerated
  refine ⟨s, ?_⟩
  have : (∐ fun _ : Fin (n + 1) => SheafOfModules.unit C.ringCatSheaf).IsQuasicoherent := by
    change (SheafOfModules.free (R := C.ringCatSheaf) (Fin (n + 1))).IsQuasicoherent
    infer_instance
  apply epi_of_rational_pullback_epi p (Sigma.desc s)
  intro a
  exact pullback_sectionFamily_epi_of_span p s a.val a.property (hs a)

end
end SteinerGeometry
