module

public import SteinerGeometry.LineClassArithmetic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import SteinerGeometry.ElementaryCurveCohomology
public import SteinerGeometry.CurveEulerAdditivity
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Tensor.UnitRight
public import SteinerGeometry.CurveTensorCokernel
public import SteinerGeometry.EulerIso
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Global.ModuleSectionIdentity
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Base.PointTranslations
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.ClassGroup
public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.LineBundle.TensorEquivalence

set_option backward.privateInPublic true
@[expose] public section

/-!
# Euler degree on elliptic curves

All degrees below are the existing coefficient Euler characteristic.  The
finite-support cokernel comparison proves the tensor law directly for this
cohomology; it does not replace sheaf cohomology by a numerical model.
-/

noncomputable section

namespace SteinerGeometry.EulerDegree

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open EllipticCohomology
open scoped CategoryTheory.MonObj

private theorem euler_of_class_eq {X : Scheme.{0}} (p : X ⟶ Spec (.of ℂ))
    (L M : Line.Bundles.LineBundle X)
    (h : Line.Bundles.LineBundle.classOf L = Line.Bundles.LineBundle.classOf M) :
    χ p L.sheaf = χ p M.sheaf :=
  congrArg (EulerIso.lineBundleClassEuler p) h

/-- Twisting the finite-support cokernel of a nonzero line section does not
change its dimension of global sections. -/
def sectionCokernelSectionsEquiv {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) (hd : topologicalKrullDim X ≤ 1)
    (L M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (hs : s ≠ 0) :
    (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj
        (cokernel (LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s)) ≃ₗ[ℂ]
      (Coefficient.GlobalSectionsFunctor.schemeGlobalSectionsFunctor p).obj (cokernel s) := by
  rw [sectionMultiply_eq]
  let c := Coefficient.ModulePresheaf.schemeCoefficientMap p
  let Q := cokernel (OAI.MaximalSeshadri.Geometry.sectionMultiply
    (seshadriBundle L) (seshadriBundle M) s)
  let R := cokernel s
  let e := SteinerGeometry.CurveTensorCokernel.tensorCokernelGlobalEquiv hd
    (seshadriBundle L) (seshadriBundle M) s hs
  exact (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso c Q).trans
    (((ModuleCat.restrictScalars c).mapIso e.toModuleIso).toLinearEquiv.trans
      (Global.ModuleSectionIdentity.coefficientGlobalSectionsNativeIso c R).symm)

/-- The tensor-degree identity whenever the first line has a nonzero section. -/
theorem tensor_euler_add_of_section {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (L M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ L.sheaf) (hs : s ≠ 0) :
    χ p (L.tensor M).sheaf - χ p M.sheaf =
      χ p L.sheaf - χ p (Line.Bundles.structureModule X) := by
  have : Nonempty (Ample.LineBundles.sectionNonvanishing s) := section_nonvanishing_nonempty L s hs
  let O := Line.Bundles.LineBundle.trivial X
  have eM := CurveEulerAdditivity.sectionCokernel_euler p hd L M s
  have eO := CurveEulerAdditivity.sectionCokernel_euler p hd L O s
  have hM := CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing
    p _ (sectionCokernel_positive_vanish p hd L M s hs)
  have hO := CohomologyEulerCharacteristic.coefficientEulerCharacteristic_eq_sections_of_positive_vanishing
    p _ (sectionCokernel_positive_vanish p hd L O s hs)
  have he := ((sectionCokernelSectionsEquiv p hd L M s hs).trans
    (sectionCokernelSectionsEquiv p hd L O s hs).symm).finrank_eq
  have hu := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p
    (Tensor.UnitRight.tensorModuleUnitRightIso L.sheaf)
  change χ p (L.tensor O).sheaf = χ p L.sheaf at hu
  calc
    χ p (L.tensor M).sheaf - χ p M.sheaf =
        χ p (cokernel (LineBundle.SectionMultiplication.lineBundleSectionMultiply L M s)) := eM.symm
    _ = _ := hM
    _ = _ := by exact_mod_cast he
    _ = χ p (cokernel (LineBundle.SectionMultiplication.lineBundleSectionMultiply L O s)) := hO.symm
    _ = χ p (L.tensor O).sheaf - χ p O.sheaf := eO
    _ = χ p L.sheaf - χ p (Line.Bundles.structureModule X) := by rw [hu]; rfl

/-- A map from an invertible sheaf to the structure sheaf is a section of its
actual reciprocal line, obtained by tensoring the map with that reciprocal. -/
def reciprocalSection {X : Scheme.{0}} (L : Line.Bundles.LineBundle X)
    (s : L.sheaf ⟶ Line.Bundles.structureModule X) :
    Line.Bundles.structureModule X ⟶ L.reciprocalFrameBundle.sheaf :=
  let F := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L.reciprocalFrameBundle
  let e₁ := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso
    L.reciprocalFrameBundle L.sheaf ≪≫ L.tensorReciprocalFrameIso
  let e₂ := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso
    L.reciprocalFrameBundle (Line.Bundles.structureModule X) ≪≫
      Tensor.ProductSheaf.tensorModuleUnitLeftIso L.reciprocalFrameBundle.sheaf
  e₁.inv ≫ F.functor.map s ≫ e₂.hom

theorem reciprocalSection_ne_zero {X : Scheme.{0}} (L : Line.Bundles.LineBundle X)
    (s : L.sheaf ⟶ Line.Bundles.structureModule X) (hs : s ≠ 0) :
    reciprocalSection L s ≠ 0 := by
  let F := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L.reciprocalFrameBundle
  let e₁ := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso
    L.reciprocalFrameBundle L.sheaf ≪≫ L.tensorReciprocalFrameIso
  let e₂ := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso
    L.reciprocalFrameBundle (Line.Bundles.structureModule X) ≪≫
      Tensor.ProductSheaf.tensorModuleUnitLeftIso L.reciprocalFrameBundle.sheaf
  intro h
  have hm : F.functor.map s = 0 := by
    have he := congrArg (fun t => e₁.hom ≫ t ≫ e₂.inv) h
    simpa [reciprocalSection, F, e₁, e₂, Category.assoc] using he
  exact hs (F.functor.map_injective (by simpa using hm))

/-- A nonzero map between actual line bundles on an integral scheme is
injective. Tensoring by the reciprocal of its source reduces this to the
native theorem for a nonzero section. -/
theorem lineMap_mono_of_ne_zero {X : Scheme.{0}} [IsIntegral X]
    (L M : Line.Bundles.LineBundle X) (f : L.sheaf ⟶ M.sheaf) (hf : f ≠ 0) :
    Mono f := by
  let F := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence L.reciprocalFrameBundle
  let e₁ : F.functor.obj L.sheaf ≅ Line.Bundles.structureModule X := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso
    L.reciprocalFrameBundle L.sheaf ≪≫ L.tensorReciprocalFrameIso
  let e₂ : F.functor.obj M.sheaf ≅ (M.tensor L.reciprocalFrameBundle).sheaf := LineBundle.TensorEquivalence.lineBundleRightTensorEquivalence_objIso
    L.reciprocalFrameBundle M.sheaf
  let s : Line.Bundles.structureModule X ⟶ (M.tensor L.reciprocalFrameBundle).sheaf :=
    e₁.inv ≫ F.functor.map f ≫ e₂.hom
  have hs : s ≠ 0 := by
    intro h
    have hm : F.functor.map f = 0 := by
      apply (cancel_epi e₁.inv).mp
      apply (cancel_mono e₂.hom).mp
      change e₁.inv ≫ F.functor.map f ≫ e₂.hom = 0 at h
      simpa only [Category.assoc, comp_zero, zero_comp] using h
    exact hf (F.functor.map_injective (by simpa using hm))
  have : Nonempty (Ample.LineBundles.sectionNonvanishing s) :=
    section_nonvanishing_nonempty (M.tensor L.reciprocalFrameBundle) s hs
  have : Mono s := IntegralLineBundleMonomorphisms.lineBundle_section_mono
    (M.tensor L.reciprocalFrameBundle) s
  have hm : Mono (e₁.hom ≫ s ≫ e₂.inv) := inferInstance
  have hfac : e₁.hom ≫ s ≫ e₂.inv = F.functor.map f := by
    dsimp only [s]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hfac] at hm
  let _ := hm
  exact F.functor.mono_of_mono_map inferInstance

/-- A monomorphic pullback unit on the target module detects a nonzero map. -/
theorem pullback_map_ne_zero_of_mono_unit {X Y : Scheme.{0}} (q : Y ⟶ X)
    {M N : X.Modules} (f : M ⟶ N) (hf : f ≠ 0)
    [Mono ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app N)] :
    (Scheme.Modules.pullback q).map f ≠ 0 := by
  intro hz
  apply hf
  apply (cancel_mono ((Scheme.Modules.pullbackPushforwardAdjunction q).unit.app N)).mp
  rw [zero_comp]
  calc
    f ≫ (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app N =
        (Scheme.Modules.pullbackPushforwardAdjunction q).unit.app M ≫
          (Scheme.Modules.pushforward q).map ((Scheme.Modules.pullback q).map f) :=
      (Scheme.Modules.pullbackPushforwardAdjunction q).unit.naturality f
    _ = 0 := by rw [hz, Functor.map_zero, comp_zero]

/-- Inverse Euler characteristic with the structure-sheaf correction, requiring
only a nonzero map to the structure sheaf. -/
theorem reciprocal_euler_of_map_to_structure_general {X : Scheme.{0}}
    [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (L : Line.Bundles.LineBundle X)
    (s : L.sheaf ⟶ Line.Bundles.structureModule X) (hs : s ≠ 0) :
    χ p L.reciprocalFrameBundle.sheaf =
      2 * χ p (Line.Bundles.structureModule X) - χ p L.sheaf := by
  have he := tensor_euler_add_of_section p hd L.reciprocalFrameBundle L
    (reciprocalSection L s) (reciprocalSection_ne_zero L s hs)
  have hu := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p
    L.reciprocalFrameTensorIso
  omega

/-- Twisting repeatedly by an effective line adds its Euler difference from
O, on an arbitrary proper integral curve. -/
theorem effective_power_twist_euler_general {X : Scheme.{0}}
    [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (H M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ H.sheaf) (hs : s ≠ 0) (k : ℕ) :
    χ p ((H.tensorPower k).tensor M).sheaf =
      (k : ℤ) * (χ p H.sheaf - χ p (Line.Bundles.structureModule X)) + χ p M.sheaf := by
  induction k with
  | zero =>
    have hc : Line.Bundles.LineBundle.classOf ((H.tensorPower 0).tensor M) =
        Line.Bundles.LineBundle.classOf M := by
      simp only [Line.Bundles.LineBundle.classOf_tensor,
        Line.Bundles.LineBundle.classOf_tensorPower, pow_zero, one_mul]
    simpa using euler_of_class_eq p _ _ hc
  | succ k ih =>
    have he := tensor_euler_add_of_section p hd H ((H.tensorPower k).tensor M) s hs
    have hc : Line.Bundles.LineBundle.classOf ((H.tensorPower (k + 1)).tensor M) =
        Line.Bundles.LineBundle.classOf (H.tensor ((H.tensorPower k).tensor M)) := by
      simp only [Line.Bundles.LineBundle.classOf_tensor,
        Line.Bundles.LineBundle.classOf_tensorPower, pow_succ', mul_assoc]
    have hi := euler_of_class_eq p _ _ hc
    rw [ih] at he
    push_cast
    nlinarith

/-- Euler characteristic is additive under tensor product up to χ(O), without
assuming genus one. An effective positive-degree reference suffices. -/
theorem tensor_euler_add_general {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (H : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ H.sheaf) (hs : s ≠ 0)
    (hH : χ p (Line.Bundles.structureModule X) < χ p H.sheaf)
    (L M : Line.Bundles.LineBundle X) :
    χ p (L.tensor M).sheaf =
      χ p L.sheaf + χ p M.sheaf - χ p (Line.Bundles.structureModule X) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-χ p L.sheaf)
  have hpL := effective_power_twist_euler_general p hd H L s hs k
  have hpLM := effective_power_twist_euler_general p hd H (L.tensor M) s hs k
  have hp : 0 < χ p ((H.tensorPower k).tensor L).sheaf := by
    have hk0 : (0 : ℤ) ≤ k := Nat.cast_nonneg _
    have hH1 : 1 ≤ χ p H.sheaf - χ p (Line.Bundles.structureModule X) := by omega
    nlinarith
  obtain ⟨t, ht⟩ := positive_euler_has_section p hd ((H.tensorPower k).tensor L).sheaf hp
  have he := tensor_euler_add_of_section p hd ((H.tensorPower k).tensor L) M t ht
  have ha := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p
    ((H.tensorPower k).tensorAssocIso L M)
  omega

/-- The general tensor-power Euler formula keeps the structure correction. -/
theorem tensorPower_euler_general {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (H : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ H.sheaf) (hs : s ≠ 0)
    (hH : χ p (Line.Bundles.structureModule X) < χ p H.sheaf)
    (L : Line.Bundles.LineBundle X) (k : ℕ) :
    χ p (L.tensorPower k).sheaf =
      (k : ℤ) * (χ p L.sheaf - χ p (Line.Bundles.structureModule X)) +
        χ p (Line.Bundles.structureModule X) := by
  induction k with
  | zero =>
    simpa using (EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p
      L.tensorPowerZeroIso)
  | succ k ih =>
    have he := tensor_euler_add_general p hd H s hs hH L (L.tensorPower k)
    have hc : Line.Bundles.LineBundle.classOf (L.tensorPower (k + 1)) =
        Line.Bundles.LineBundle.classOf (L.tensor (L.tensorPower k)) := by
      simp only [Line.Bundles.LineBundle.classOf_tensor,
        Line.Bundles.LineBundle.classOf_tensorPower, pow_succ']
    rw [euler_of_class_eq p _ _ hc, he, ih]
    push_cast
    ring

/-- A finite-order line has the same Euler characteristic as O on any proper
integral curve, proved before any genus-one assumption. -/
theorem torsion_euler_eq_structure {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (H : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ H.sheaf) (hs : s ≠ 0)
    (hH : χ p (Line.Bundles.structureModule X) < χ p H.sheaf)
    (L : Line.Bundles.LineBundle X) (m : ℕ) (hm : 0 < m)
    (ht : Nonempty ((L.tensorPower m).sheaf ≅ Line.Bundles.structureModule X)) :
    χ p L.sheaf = χ p (Line.Bundles.structureModule X) := by
  have he := tensorPower_euler_general p hd H s hs hH L m
  have hu := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p ht.some
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  nlinarith

/-- The same torsion rule using intrinsic finite order in the line class group. -/
theorem isOfFinOrder_euler_eq_structure {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (H : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ H.sheaf) (hs : s ≠ 0)
    (hH : χ p (Line.Bundles.structureModule X) < χ p H.sheaf)
    (L : Line.Bundles.LineBundle X)
    (ht : IsOfFinOrder (Line.Bundles.LineBundle.classOf L)) :
    χ p L.sheaf = χ p (Line.Bundles.structureModule X) := by
  obtain ⟨m, hm, he⟩ := ht.exists_pow_eq_one
  apply torsion_euler_eq_structure p hd H s hs hH L m hm
  have hc : Line.Bundles.LineBundle.classOf (L.tensorPower m) =
      Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.trivial X) := by
    simpa only [Line.Bundles.LineBundle.classOf_tensorPower,
      Line.Bundles.LineBundle.classOf_trivial] using he
  exact Quotient.exact hc

/-- The inverse-degree rule for an invertible ideal follows from its nonzero
inclusion, without first requiring any positive-degree line bundle. -/
theorem reciprocal_euler_of_map_to_structure {X : Scheme.{0}}
    [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (L : Line.Bundles.LineBundle X)
    (s : L.sheaf ⟶ Line.Bundles.structureModule X) (hs : s ≠ 0) :
    χ p L.reciprocalFrameBundle.sheaf = -χ p L.sheaf := by
  have he := tensor_euler_add_of_section p hd L.reciprocalFrameBundle L
    (reciprocalSection L s) (reciprocalSection_ne_zero L s hs)
  have hu := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p
    L.reciprocalFrameTensorIso
  rw [hO] at hu he
  omega

/-- Repeated twisting by one effective positive-degree line changes Euler
characteristic by the predicted arithmetic progression. -/
theorem effective_power_twist_euler {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H M : Line.Bundles.LineBundle X)
    (s : Line.Bundles.structureModule X ⟶ H.sheaf) (hs : s ≠ 0) (k : ℕ) :
    χ p ((H.tensorPower k).tensor M).sheaf = (k : ℤ) * χ p H.sheaf + χ p M.sheaf := by
  induction k with
  | zero =>
    have hc : Line.Bundles.LineBundle.classOf ((H.tensorPower 0).tensor M) =
        Line.Bundles.LineBundle.classOf M := by
      simp only [Line.Bundles.LineBundle.classOf_tensor,
        Line.Bundles.LineBundle.classOf_tensorPower, pow_zero, one_mul]
    simpa using euler_of_class_eq p _ _ hc
  | succ k ih =>
    have he := tensor_euler_add_of_section p hd H ((H.tensorPower k).tensor M) s hs
    have hc : Line.Bundles.LineBundle.classOf ((H.tensorPower (k + 1)).tensor M) =
        Line.Bundles.LineBundle.classOf (H.tensor ((H.tensorPower k).tensor M)) := by
      simp only [Line.Bundles.LineBundle.classOf_tensor,
        Line.Bundles.LineBundle.classOf_tensorPower, pow_succ', mul_assoc]
    have hi := euler_of_class_eq p _ _ hc
    rw [hO, sub_zero, ih] at he
    push_cast
    nlinarith

/-- On a curve with structure Euler characteristic zero and one positive line,
Euler characteristic is additive under tensor product for all line bundles. -/
theorem tensor_euler_add {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    (L M : Line.Bundles.LineBundle X) :
    χ p (L.tensor M).sheaf = χ p L.sheaf + χ p M.sheaf := by
  obtain ⟨s, hs⟩ := positive_euler_has_section p hd H.sheaf hH
  obtain ⟨k, hk⟩ := exists_nat_gt (-χ p L.sheaf)
  have hpL := effective_power_twist_euler p hd hO H L s hs k
  have hpLM := effective_power_twist_euler p hd hO H (L.tensor M) s hs k
  have hp : 0 < χ p ((H.tensorPower k).tensor L).sheaf := by
    have hk0 : (0 : ℤ) ≤ k := Nat.cast_nonneg _
    have hH1 : 1 ≤ χ p H.sheaf := by omega
    nlinarith
  obtain ⟨t, ht⟩ := positive_euler_has_section p hd ((H.tensorPower k).tensor L).sheaf hp
  have he := tensor_euler_add_of_section p hd ((H.tensorPower k).tensor L) M t ht
  have ha := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p
    ((H.tensorPower k).tensorAssocIso L M)
  rw [hO, sub_zero] at he
  omega

/-- Tensor powers have integer degree equal to the exponent times the degree. -/
theorem tensorPower_euler {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    (L : Line.Bundles.LineBundle X) (k : ℕ) :
    χ p (L.tensorPower k).sheaf = (k : ℤ) * χ p L.sheaf := by
  induction k with
  | zero =>
    exact (EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p L.tensorPowerZeroIso).trans
      (by simpa using hO)
  | succ k ih =>
    have he := tensor_euler_add p hd hO H hH L (L.tensorPower k)
    have hc : Line.Bundles.LineBundle.classOf (L.tensorPower (k + 1)) =
        Line.Bundles.LineBundle.classOf (L.tensor (L.tensorPower k)) := by
      simp only [Line.Bundles.LineBundle.classOf_tensor,
        Line.Bundles.LineBundle.classOf_tensorPower, pow_succ']
    rw [euler_of_class_eq p _ _ hc, he, ih]
    push_cast
    ring

/-- The actual reciprocal frame line has the negative degree. -/
theorem reciprocal_euler {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    (L : Line.Bundles.LineBundle X) :
    χ p L.reciprocalFrameBundle.sheaf = -χ p L.sheaf := by
  have he := tensor_euler_add p hd hO H hH L L.reciprocalFrameBundle
  have hu := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p L.tensorReciprocalFrameIso
  rw [hO] at hu
  omega

/-- Euler degree changes sign for any actual inverse pairing. This applies
equally to an internal-Hom dual and to the reciprocal-frame construction. -/
theorem inversePair_euler {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    (L M : Line.Bundles.LineBundle X)
    (e : (L.tensor M).sheaf ≅ Line.Bundles.structureModule X) :
    χ p M.sheaf = -χ p L.sheaf := by
  have he := tensor_euler_add p hd hO H hH L M
  have hu := EulerIso.coefficientEulerCharacteristic_eq_of_sheafIso p e
  rw [hO] at hu
  omega

/-- Integer powers are represented by actual tensor powers and reciprocal
frame bundles. -/
def integerPower {X : Scheme.{0}} (L : Line.Bundles.LineBundle X) : ℤ → Line.Bundles.LineBundle X
  | .ofNat n => L.tensorPower n
  | .negSucc n => L.reciprocalFrameBundle.tensorPower (n + 1)

/-- Signed powers scale Euler degree by the signed exponent. -/
theorem integerPower_euler {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    (L : Line.Bundles.LineBundle X) (k : ℤ) :
    χ p (integerPower L k).sheaf = k * χ p L.sheaf := by
  cases k with
  | ofNat n => exact tensorPower_euler p hd hO H hH L n
  | negSucc n =>
    rw [integerPower, tensorPower_euler p hd hO H hH, reciprocal_euler p hd hO H hH]
    simp only [Int.negSucc_eq, Nat.cast_add, Nat.cast_one]
    ring

/-- Degree on actual line-bundle isomorphism classes is a group homomorphism. -/
def degreeHom {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf) :
    Line.Bundles.LineBundle.IsoClass X →* Multiplicative ℤ where
  toFun q := Multiplicative.ofAdd (EulerIso.lineBundleClassEuler p q)
  map_one' := congrArg Multiplicative.ofAdd hO
  map_mul' a b := by
    induction a using Quotient.inductionOn with
    | h L =>
      induction b using Quotient.inductionOn with
      | h M =>
        exact congrArg Multiplicative.ofAdd (tensor_euler_add p hd hO H hH L M)

/-- Finite products of arbitrary actual line classes have the sum of their degrees. -/
theorem degree_finset_product {X : Scheme.{0}} [IsIntegral X] [IsNoetherian X]
    (p : X ⟶ Spec (.of ℂ)) [CurveCohomologyFinite p] (hd : topologicalKrullDim X ≤ 1)
    (hO : χ p (Line.Bundles.structureModule X) = 0)
    (H : Line.Bundles.LineBundle X) (hH : 0 < χ p H.sheaf)
    {J : Type*} (s : Finset J) (f : J → Line.Bundles.LineBundle.IsoClass X) :
    EulerIso.lineBundleClassEuler p (∏ i ∈ s, f i) =
      ∑ i ∈ s, EulerIso.lineBundleClassEuler p (f i) := by
  change Multiplicative.toAdd ((degreeHom p hd hO H hH) (∏ i ∈ s, f i)) = _
  rw [map_prod, toAdd_prod]
  rfl

/-- Pullback by an actual group translation preserves degree. -/
theorem translation_euler {g : ℕ}
    (A : Abelian.Schemes.AbelianScheme g (Spec (.of ℂ)))
    (a : 𝟙_ (Over (Spec (.of ℂ))) ⟶ A.scheme)
    (L : Line.Bundles.LineBundle A.scheme.left) :
    χ A.scheme.hom (L.pullback (A.basePointTranslation a).left).sheaf =
      χ A.scheme.hom L.sheaf := by
  have : A.scheme.left.IsSeparated := ⟨by rw [← terminal.comp_from A.scheme.hom]; infer_instance⟩
  exact EulerIso.coefficientEulerCharacteristic_overIso (A.basePointTranslationIso a)
    L (L.pullback (A.basePointTranslation a).left) (Iso.refl _)

end SteinerGeometry.EulerDegree
