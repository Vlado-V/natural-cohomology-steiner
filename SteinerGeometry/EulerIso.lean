import SteinerGeometry.CurveCohomologyCore
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CoefficientCohomology.Additivity
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Classes
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CohomologyPullbackIso

/-! Euler invariance requires only functoriality of actual cohomology. -/
noncomputable section
namespace SteinerGeometry.EulerIso
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

theorem coefficientEulerCharacteristic_eq_of_sheafIso {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) {M N : X.Modules} (e : M ≅ N) : χ p M = χ p N := by
  apply finsum_congr
  intro q
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ))
    (((Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).mapIso e).toLinearEquiv.finrank_eq)

def lineBundleClassEuler {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ)) :
    Line.Bundles.LineBundle.IsoClass X → ℤ :=
  Quotient.lift (fun L : Line.Bundles.LineBundle X => χ p L.sheaf)
    (fun _ _ ⟨e⟩ => coefficientEulerCharacteristic_eq_of_sheafIso p e)

@[simp] theorem lineBundleClassEuler_classOf {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) (L : Line.Bundles.LineBundle X) :
    lineBundleClassEuler p (Line.Bundles.LineBundle.classOf L) = χ p L.sheaf := rfl

theorem coefficientEulerCharacteristic_pullback_iso {X Y : Scheme.{0}}
    [Y.IsSeparated] (f : X ⟶ Y) [IsIso f] (p : Y ⟶ Spec (.of ℂ))
    (L : Line.Bundles.LineBundle Y) :
    χ (f ≫ p) (L.pullback f).sheaf = χ p L.sheaf := by
  apply finsum_congr
  intro q
  exact congrArg (fun n : ℕ => (-1 : ℤ) ^ q * (n : ℤ))
    (CohomologyPullbackIso.lineBundleCohomologyPullbackIso f p L q).toLinearEquiv.finrank_eq

theorem coefficientEulerCharacteristic_overIso {A B : Over (Spec (.of ℂ))}
    [B.left.IsSeparated] (e : A ≅ B)
    (L : Line.Bundles.LineBundle B.left) (M : Line.Bundles.LineBundle A.left)
    (h : (L.pullback e.hom.left).sheaf ≅ M.sheaf) : χ A.hom M.sheaf = χ B.hom L.sheaf := by
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget (Spec (.of ℂ))).map e.hom))
  calc
    χ A.hom M.sheaf = χ A.hom (L.pullback e.hom.left).sheaf :=
      coefficientEulerCharacteristic_eq_of_sheafIso A.hom h.symm
    _ = χ (e.hom.left ≫ B.hom) (L.pullback e.hom.left).sheaf :=
      congrArg (fun p => χ p (L.pullback e.hom.left).sheaf) e.hom.w.symm
    _ = χ B.hom L.sheaf := coefficientEulerCharacteristic_pullback_iso e.hom.left B.hom L

theorem coefficientEulerCharacteristic_of_isZero {X : Scheme.{0}}
    (p : X ⟶ Spec (.of ℂ)) (M : X.Modules) (hM : CategoryTheory.Limits.IsZero M) :
    χ p M = 0 := by
  have he : ∀ q, IsZero (H p M q) := fun q =>
    (Zariski.CohomologyFunctor.ZariskiCohomology.coefficientCohomologyFunctor
      (Coefficient.ModulePresheaf.schemeCoefficientMap p) q).map_isZero hM
  apply finsum_eq_zero_of_forall_eq_zero
  intro q
  have := ModuleCat.isZero_iff_subsingleton.mp (he q)
  rw [Module.finrank_zero_of_subsingleton, Nat.cast_zero, mul_zero]
end SteinerGeometry.EulerIso
