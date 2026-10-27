import SteinerGeometry.PresentationEulerCore
import SteinerGeometry.CurveEulerBiproduct
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyDimensionBalance

/-! Euler additivity on curves from the actual H0--H1 exact sequence. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.PresentationEuler
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

local instance presentationEulerCurveBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- A finite free bundle inherits finite cohomology from the structure sheaf. -/
theorem freeSheaf_cohomology_finite {X : Scheme} (p : X ⟶ Spec (.of ℂ))
    (m k : ℕ) [Module.Finite ℂ (H p (Line.Bundles.structureModule X) k)] :
    Module.Finite ℂ (H p (DualEvaluation.freeSheaf (X := X) m) k) := by
  let F := Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
    (Coefficient.ModulePresheaf.schemeCoefficientMap p) k
  let M := fun _ : Fin m => Line.Bundles.structureModule X
  have : ∀ j, Module.Finite ℂ (F.obj (M j)) := fun _ => inferInstance
  let E : F.obj (⨁ M) ≅ ModuleCat.of ℂ (∀ j, F.obj (M j)) :=
    F.mapBiproduct M ≪≫ biproduct.isoProduct (F.obj ∘ M) ≪≫ ModuleCat.piIsoPi (F.obj ∘ M)
  exact Module.Finite.equiv E.symm.toLinearEquiv

/-- On a curve, the free bundle has m times the structure Euler characteristic. -/
theorem freeSheaf_curve_euler {X : Scheme} [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1) (m : ℕ)
    [Module.Finite ℂ (H p (Line.Bundles.structureModule X) 0)]
    [Module.Finite ℂ (H p (Line.Bundles.structureModule X) 1)] :
    χ p (DualEvaluation.freeSheaf (X := X) m) =
      (m : ℤ) * χ p (Line.Bundles.structureModule X) := by
  change χ p (⨁ fun _ : Fin m => Line.Bundles.structureModule X) = _
  rw [curve_biproduct_euler p hd _ (fun _ => inferInstance) (fun _ => inferInstance)]
  simp

/-- The actual long exact sequence gives Euler additivity on a curve using
    only the five finite-dimensional terms entering H0 and H1. -/
theorem curve_shortExact_euler {X : Scheme} [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [Module.Finite ℂ (H p S.X₂ 0)] [Module.Finite ℂ (H p S.X₃ 0)]
    [Module.Finite ℂ (H p S.X₁ 1)] [Module.Finite ℂ (H p S.X₂ 1)]
    [Module.Finite ℂ (H p S.X₃ 1)] :
    χ p S.X₂ = χ p S.X₁ + χ p S.X₃ := by
  have h0 := CohomologyDimensionBalance.coefficientCohomology_dimension_balance_zero
    (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS
  have h1 := CohomologyDimensionBalance.coefficientCohomology_dimension_balance_succ
    (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS 0
  have : Subsingleton (H p S.X₁ 2) :=
    ModuleCat.isZero_iff_subsingleton.mp (curve_cohomology_above_one p hd S.X₁ 2 (by omega))
  have hr : Module.finrank ℂ (LinearMap.range
      (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap
        (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS 1).hom) = 0 :=
    Module.finrank_zero_of_subsingleton
  change Module.finrank ℂ (H p S.X₁ 0) + Module.finrank ℂ (H p S.X₃ 0) =
    Module.finrank ℂ (H p S.X₂ 0) + Module.finrank ℂ (LinearMap.range
      (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap
        (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS 0).hom) at h0
  change Module.finrank ℂ (H p S.X₁ 1) + Module.finrank ℂ (H p S.X₃ 1) =
    Module.finrank ℂ (H p S.X₂ 1) + Module.finrank ℂ (LinearMap.range
      (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap
        (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS 0).hom) +
      Module.finrank ℂ (LinearMap.range
        (Coefficient.ConnectingMap.ZariskiCohomology.coefficientConnectingMap
          (Coefficient.ModulePresheaf.schemeCoefficientMap p) hS 1).hom) at h1
  rw [hr, add_zero] at h1
  rw [curve_euler_eq_h0_sub_h1 p hd S.X₁,
    curve_euler_eq_h0_sub_h1 p hd S.X₂, curve_euler_eq_h0_sub_h1 p hd S.X₃]
  omega

/-- The relation-line arithmetic can be discharged by genuine finite H0/H1
    rather than by assuming an Euler-additivity formula. -/
theorem relation_euler_of_curve_cohomology {X : Scheme} [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1) {m : ℕ}
    (R : Line.Bundles.LineBundle X) {Q : X.Modules}
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (s : DualEvaluation.freeSheaf m ⟶ Q) (w : i ≫ s = 0)
    (hS : (ShortComplex.mk i s w).ShortExact)
    [Module.Finite ℂ (H p (DualEvaluation.freeSheaf (X := X) m) 0)]
    [Module.Finite ℂ (H p Q 0)] [Module.Finite ℂ (H p R.sheaf 1)]
    [Module.Finite ℂ (H p (DualEvaluation.freeSheaf (X := X) m) 1)]
    [Module.Finite ℂ (H p Q 1)]
    (hfree : χ p (DualEvaluation.freeSheaf (X := X) m) = 0)
    (r : ℤ) (hQ : χ p Q = r) : χ p R.sheaf = -r :=
  relation_euler_of_additivity p R Q r
    (curve_shortExact_euler p hd (ShortComplex.mk i s w) hS) hfree hQ

/-- The curve calculation discharges presentation additivity directly from
    finite cohomology of O, of the quotient, and of the relation H1. -/
theorem relation_euler_of_curve_finite {X : Scheme} [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1) {m : ℕ}
    (R : Line.Bundles.LineBundle X) {Q : X.Modules}
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (s : DualEvaluation.freeSheaf m ⟶ Q) (w : i ≫ s = 0)
    (hS : (ShortComplex.mk i s w).ShortExact)
    [Module.Finite ℂ (H p (Line.Bundles.structureModule X) 0)]
    [Module.Finite ℂ (H p (Line.Bundles.structureModule X) 1)]
    [Module.Finite ℂ (H p Q 0)] [Module.Finite ℂ (H p R.sheaf 1)]
    [Module.Finite ℂ (H p Q 1)]
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (r : ℤ) (hQ : χ p Q = r) : χ p R.sheaf = -r := by
  have := freeSheaf_cohomology_finite p m 0
  have := freeSheaf_cohomology_finite p m 1
  apply relation_euler_of_curve_cohomology p hd R i s w hS _ r hQ
  rw [freeSheaf_curve_euler p hd m, hO, mul_zero]

/-- Composition with the native line-dual and tensor Euler laws gives the
    two target degrees. The laws are explicit while their separate geometric
    implementation is imported by the final presentation wrapper. -/
theorem relationDual_tensor_euler_of_laws {X : Scheme} [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1) {m : ℕ}
    (R B : Line.Bundles.LineBundle X) {Q : X.Modules}
    (i : R.sheaf ⟶ DualEvaluation.freeSheaf m)
    (s : DualEvaluation.freeSheaf m ⟶ Q) (w : i ≫ s = 0)
    (hS : (ShortComplex.mk i s w).ShortExact)
    [Module.Finite ℂ (H p (Line.Bundles.structureModule X) 0)]
    [Module.Finite ℂ (H p (Line.Bundles.structureModule X) 1)]
    [Module.Finite ℂ (H p Q 0)] [Module.Finite ℂ (H p R.sheaf 1)]
    [Module.Finite ℂ (H p Q 1)]
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (hdual : ∀ L : Line.Bundles.LineBundle X,
      χ p (OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual L).sheaf =
        -χ p L.sheaf)
    (htensor : ∀ L M : Line.Bundles.LineBundle X,
      χ p (L.tensor M).sheaf = χ p L.sheaf + χ p M.sheaf)
    (r t : ℤ) (hQ : χ p Q = r) (hB : χ p B.sheaf = t) :
    χ p (OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual R).sheaf = r ∧
    χ p ((OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual R).tensor B).sheaf =
      r + t := by
  have hR := relation_euler_of_curve_finite p hd R i s w hS hO r hQ
  have hN : χ p (OAI.AlgebraicGeometry.Picard.Homomorphisms.LineBundleDual.Construction.lineBundleDual R).sheaf = r := by
    rw [hdual, hR, neg_neg]
  exact ⟨hN, by rw [htensor, hN, hB]⟩

end SteinerGeometry.PresentationEuler
