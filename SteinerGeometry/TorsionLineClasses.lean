module

public import SteinerGeometry.LineClassArithmetic
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.TensorPower.Classes
public import Mathlib.GroupTheory.Torsion

set_option backward.privateInPublic true
@[expose] public section

/-! Finite-order classes of actual invertible sheaves, with actual representatives. -/
noncomputable section
namespace SteinerGeometry.TorsionLineClasses
open AlgebraicGeometry CategoryTheory
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

universe u v

abbrev TorsionClass (X : Scheme.{u}) :=
  CommGroup.torsion (Line.Bundles.LineBundle.IsoClass X)

/-- Each torsion class is represented by a genuine locally free rank-one sheaf. -/
def representative {X : Scheme.{u}} (a : TorsionClass X) : Line.Bundles.LineBundle X :=
  Quotient.out a.val

@[simp] theorem representative_class {X : Scheme.{u}} (a : TorsionClass X) :
    Line.Bundles.LineBundle.classOf (representative a) = a.val := Quotient.out_eq a.val

theorem representative_class_injective {X : Scheme.{u}} :
    Function.Injective (fun a : TorsionClass X =>
      Line.Bundles.LineBundle.classOf (representative a)) := by
  intro a b h
  apply Subtype.ext
  simpa only [representative_class] using h

/-- Finite-order classes have a positive tensor power actually isomorphic to O. -/
theorem representative_torsion {X : Scheme.{u}} (a : TorsionClass X) :
    ∃ m : ℕ, 0 < m ∧ Nonempty (((representative a).tensorPower m).sheaf ≅
      Line.Bundles.structureModule X) := by
  obtain ⟨m, hm, he⟩ := a.property.exists_pow_eq_one
  refine ⟨m, hm, ?_⟩
  have hc : Line.Bundles.LineBundle.classOf ((representative a).tensorPower m) =
      Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.trivial X) := by
    simpa only [Line.Bundles.LineBundle.classOf_tensorPower,
      representative_class, Line.Bundles.LineBundle.classOf_trivial] using he
  exact Quotient.exact hc

/-- Any scheme pullback carries a torsion line class to a torsion line class. -/
def pullback {X Y : Scheme.{u}} (f : X ⟶ Y) (a : TorsionClass Y) : TorsionClass X :=
  ⟨Line.Bundles.LineBundle.pullbackClass f a.val,
    (Line.Bundles.LineBundle.pullbackClassMonoidHom f).isOfFinOrder a.property⟩

/-- Every element in a finite kernel of line-bundle pullback has finite order. -/
theorem torsion_of_finite_pullbackKernel {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Finite (Line.Bundles.LineBundle.pullbackClassMonoidHom f).ker]
    (L : Line.Bundles.LineBundle Y)
    (h : Nonempty ((L.pullback f).sheaf ≅ Line.Bundles.structureModule X)) :
    IsOfFinOrder (Line.Bundles.LineBundle.classOf L) := by
  let a : (Line.Bundles.LineBundle.pullbackClassMonoidHom f).ker :=
    ⟨Line.Bundles.LineBundle.classOf L, Quotient.sound h⟩
  have ht := isOfFinOrder_of_finite a
  exact (MonoidHom.isOfFinOrder ((Line.Bundles.LineBundle.pullbackClassMonoidHom f).ker.subtype) ht)

/-- An unbounded supply of distinct finite families proves infinitude. -/
theorem infinite_of_large_finite_families {T : Type v}
    (h : ∀ m : ℕ, ∃ f : Fin m → T, Function.Injective f) : Infinite T := by
  by_contra hn
  have : Finite T := not_infinite_iff_finite.mp hn
  let _ := Fintype.ofFinite T
  obtain ⟨f, hf⟩ := h (Fintype.card T + 1)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin] at hc
  omega

end SteinerGeometry.TorsionLineClasses
