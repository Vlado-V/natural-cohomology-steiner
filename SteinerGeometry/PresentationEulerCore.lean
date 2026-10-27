import SteinerGeometry.CurveCohomologyCore
import SteinerGeometry.DualEvaluation
import SteinerGeometry.CyclicLinePushforward
import SteinerGeometry.CyclicComplexBase
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.Quasicoherence
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.PushforwardEuler
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Affine.LineBundleSectionFiniteness
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.FiniteCoproducts
import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Quasicoherent.RestrictionFiniteType

/-! Coherence and arithmetic for an actual finite-free presentation. -/
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.PresentationEuler
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology

local instance presentationEulerCoreBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The finite free object in the presentation is an actual coherent sheaf. -/
theorem freeSheaf_coherent (X : Scheme) (m : ℕ) :
    (DualEvaluation.freeSheaf (X := X) m).IsQuasicoherent ∧
      (DualEvaluation.freeSheaf (X := X) m).IsFiniteType := by
  let M := fun _ : Fin m => Line.Bundles.structureModule X
  have hq : (∐ M).IsQuasicoherent :=
    Quasicoherent.Coproducts.module_quasicoherent_coproduct M
      (fun _ => (Line.Bundles.LineBundle.trivial X).isQuasicoherent)
  have ht : (∐ M).IsFiniteType :=
    Quasicoherent.FiniteCoproducts.module_finiteType_finite_coproduct M
      (fun _ => (Line.Bundles.LineBundle.trivial X).isQuasicoherent)
      (fun _ => (Line.Bundles.LineBundle.trivial X).isFiniteType)
  have hfq : (DualEvaluation.freeSheaf (X := X) m).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso (biproduct.isoCoproduct M).symm hq
  have : (∐ M).IsQuasicoherent := hq
  have : (∐ M).IsFiniteType := ht
  exact ⟨hfq, Quasicoherent.RestrictionFiniteType.quasicoherent_finiteType_of_iso
    (biproduct.isoCoproduct M).symm⟩

/-- The numerical consequence of genuine Euler additivity on the presentation. -/
theorem relation_euler_of_additivity {X : Scheme} (p : X ⟶ Spec (.of ℂ)) {m : ℕ}
    (R : Line.Bundles.LineBundle X) (Q : X.Modules) (r : ℤ)
    (hadd : χ p (DualEvaluation.freeSheaf (X := X) m) = χ p R.sheaf + χ p Q)
    (hfree : χ p (DualEvaluation.freeSheaf (X := X) m) = 0)
    (hQ : χ p Q = r) : χ p R.sheaf = -r := by
  omega

end SteinerGeometry.PresentationEuler

namespace SteinerGeometry.CyclicEtaleIsogeny
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open EllipticCohomology
variable {D : EllipticScheme} {n : ℕ} (q : CyclicEtaleIsogeny D n)

/-- Finite direct image preserves the source line's genuine Euler characteristic. -/
theorem linePushforward_euler (A : Line.Bundles.LineBundle D.scheme.left) :
    χ q.target.scheme.hom (q.linePushforward A) = χ D.scheme.hom A.sheaf := by
  have : A.sheaf.IsQuasicoherent := A.isQuasicoherent
  have : q.target.scheme.left.IsSeparated := ⟨by
    rw [← terminal.comp_from q.target.scheme.hom]
    infer_instance⟩
  have h := Affine.PushforwardEuler.coefficientEulerCharacteristic_affinePushforward
    q.map.hom.left q.target.scheme.hom A.sheaf
  change CohomologyEulerCharacteristic.coefficientEulerCharacteristic q.target.scheme.hom
    ((Scheme.Modules.pushforward q.map.hom.left).obj A.sheaf) =
      CohomologyEulerCharacteristic.coefficientEulerCharacteristic D.scheme.hom A.sheaf
  simpa only [q.map.hom.w] using h.symm

end SteinerGeometry.CyclicEtaleIsogeny
