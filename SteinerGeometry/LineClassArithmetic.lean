module

public import Mathlib.AlgebraicGeometry.Properties
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence

set_option backward.privateInPublic true
@[expose] public section

/-! Isomorphism-class arithmetic for actual invertible module sheaves. -/
noncomputable section
namespace SteinerGeometry.EulerDegree
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

/-- An invertible sheaf on a nonempty integral scheme is not the zero object. -/
theorem lineBundle_not_isZero {X : Scheme.{0}} [Nonempty X]
    (L : Line.Bundles.LineBundle X) : ¬ IsZero L.sheaf := by
  intro h
  let F := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L.reciprocalFrameBundle
  let e := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso
    L.reciprocalFrameBundle L.sheaf ≪≫ L.tensorReciprocalFrameIso
  have hL : (𝟙 L.sheaf) = 0 := (IsZero.iff_id_eq_zero _).mp h
  have hF : (𝟙 (F.functor.obj L.sheaf)) = 0 := by
    rw [← F.functor.map_id, hL, Functor.map_zero]
  have hOzero : IsZero (Line.Bundles.structureModule X) :=
    ((IsZero.iff_id_eq_zero _).mpr hF).of_iso e.symm
  have hO : (𝟙 (Line.Bundles.structureModule X)) = 0 :=
    (IsZero.iff_id_eq_zero _).mp hOzero
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  have hz := ConcreteCategory.congr_hom
    (congrArg (fun f : Line.Bundles.structureModule X ⟶ Line.Bundles.structureModule X =>
      f.app ⊤) hO) (1 : Γ(X, ⊤))
  change (1 : Γ(X, ⊤)) = 0 at hz
  exact one_ne_zero hz

/-- An inverse pairing identifies the second line's genuine isomorphism class
with the group inverse, independently of its particular construction. -/
theorem inversePair_class {X : Scheme.{0}} (L M : Line.Bundles.LineBundle X)
    (e : (L.tensor M).sheaf ≅ Line.Bundles.structureModule X) :
    Line.Bundles.LineBundle.classOf M = (Line.Bundles.LineBundle.classOf L)⁻¹ := by
  apply mul_left_cancel (a := Line.Bundles.LineBundle.classOf L)
  calc
    Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf M = 1 :=
      Quotient.sound ⟨e⟩
    _ = Line.Bundles.LineBundle.classOf L * (Line.Bundles.LineBundle.classOf L)⁻¹ :=
      (mul_inv_cancel _).symm

/-- A trivial tensor pairing is independent of the order of its line factors. -/
theorem inverse_pairing_swap {X : Scheme.{0}} (L M : Line.Bundles.LineBundle X)
    (h : Nonempty ((M.tensor L).sheaf ≅ Line.Bundles.structureModule X)) :
    Nonempty ((L.tensor M).sheaf ≅ Line.Bundles.structureModule X) := by
  have heq : Line.Bundles.LineBundle.classOf (L.tensor M) =
      Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.trivial X) := by
    rw [Line.Bundles.LineBundle.classOf_tensor, mul_comm]
    exact Quotient.sound h
  exact Quotient.exact heq

/-- Avoiding the primal line makes its inverse twist nontrivial, for any
actual inverse pairing, including an internal-Hom dual evaluation pairing. -/
theorem inverse_tensor_nontrivial_of_not_isomorphic {X : Scheme.{0}}
    (L M N : Line.Bundles.LineBundle X)
    (e : (L.tensor M).sheaf ≅ Line.Bundles.structureModule X)
    (hNL : ¬ Nonempty (N.sheaf ≅ L.sheaf)) :
    ¬ Nonempty ((M.tensor N).sheaf ≅ Line.Bundles.structureModule X) := by
  intro h
  apply hNL
  have hLM : Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf M = 1 :=
    Quotient.sound ⟨e⟩
  have hMN : Line.Bundles.LineBundle.classOf M * Line.Bundles.LineBundle.classOf N = 1 :=
    Quotient.sound h
  have heq : Line.Bundles.LineBundle.classOf N = Line.Bundles.LineBundle.classOf L := by
    calc
      Line.Bundles.LineBundle.classOf N = 1 * Line.Bundles.LineBundle.classOf N := (one_mul _).symm
      _ = (Line.Bundles.LineBundle.classOf L * Line.Bundles.LineBundle.classOf M) *
          Line.Bundles.LineBundle.classOf N := congrArg (fun a => a * Line.Bundles.LineBundle.classOf N) hLM.symm
      _ = Line.Bundles.LineBundle.classOf L *
          (Line.Bundles.LineBundle.classOf M * Line.Bundles.LineBundle.classOf N) := mul_assoc _ _ _
      _ = Line.Bundles.LineBundle.classOf L := by rw [hMN, mul_one]
  exact Quotient.exact heq

/-- Pullback carries the constructed reciprocal line to the inverse class of
the pulled-back line. -/
theorem pullback_reciprocal_class {X Y : Scheme.{0}} (f : X ⟶ Y)
    (L : Line.Bundles.LineBundle Y) :
    Line.Bundles.LineBundle.classOf (L.reciprocalFrameBundle.pullback f) =
      Line.Bundles.LineBundle.classOf (L.pullback f).reciprocalFrameBundle := by
  change (Line.Bundles.LineBundle.pullbackClassMonoidHom f)
    (Line.Bundles.LineBundle.classOf L.reciprocalFrameBundle) = _
  rw [Line.Bundles.LineBundle.classOf_reciprocalFrameBundle, map_inv,
    Line.Bundles.LineBundle.classOf_reciprocalFrameBundle]
  rfl

end SteinerGeometry.EulerDegree
