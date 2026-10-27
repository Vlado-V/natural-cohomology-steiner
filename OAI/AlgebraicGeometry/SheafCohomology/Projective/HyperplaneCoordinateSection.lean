module

/- Porting notice for the NaturalCohomologySteiner source package.
This file was modified from the upstream OpenAI math-main/lean source.
Original SHA-256: e3a03649fe202390f017c9644373e549b091b98a5109d944814d505af3b9d931
The packaged proof source is the local port; see OAI/PROVENANCE.json.
-/
/-
Copyright (c) 2026 The AINTLIB contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AINTLIB ModularCurves project
This file has been modified.
-/
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneFrames
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.IdealOverFrame
public import OAI.AlgebraicGeometry.SheafCohomology.Projective.DualFrameScalar

set_option backward.privateInPublic true
@[expose] public section

/-! # Hyperplane Coordinate Section -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial

noncomputable section

open _root_.MvPolynomial

open _root_.AlgebraicGeometry _root_.CategoryTheory
universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

-- Reuse the theorem's canonical instance to avoid converting the entire
-- dual sheaf between separately constructed commutativity proofs.
attribute [local instance] DualFrameScalar.schemeSectionsMulCommutative

noncomputable def coordinateHyperplaneIdealOverTrivialization
    (i j : σ) :
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).over
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) ≅
      SheafOfModules.unit
        ((Proj (homogeneousSubmodule σ R)).ringCatSheaf.over
          (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)) :=
  Invertible.Scheme.Modules.overTrivializationOfRestrictIso
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
    (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j).symm

/-- Keep the canonical frame comparison opaque before transporting it through module morphisms. -/
private theorem coordinateHyperplaneIdealModuleTrivialization_eq_canonical (i j : σ) :
    HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization (R := R) i j =
      (by
        letI : IsClosedImmersion (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) :=
          SpaceHyperplane.MvPolynomial.coordinateHyperplaneι_isClosedImmersion j
        letI : QuasiCompact (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) := inferInstance
        let U : (Proj (homogeneousSubmodule σ R)).affineOpens :=
          ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i,
            MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
        let r := CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j
        have hr : r ∈ (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j).ker.ideal U := by
          rw [CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_span]
          exact Ideal.mem_span_singleton_self r
        exact CanonicalIdealFrame.localIdealGeneratorIso
          (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) U r hr
            (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_span i j)
            (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_mem_nonZeroDivisors i j)) := rfl

theorem coordinateHyperplaneIdealOverTrivialization_inv_comp
    (i j : σ) :
    (coordinateHyperplaneIdealOverTrivialization (R := R) i j).inv ≫
        (IdealModule.idealModuleToUnit
          (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)).over
            (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i) =
      Dual.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
        (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j) := by
  let : IsClosedImmersion (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) :=
    SpaceHyperplane.MvPolynomial.coordinateHyperplaneι_isClosedImmersion j
  let : QuasiCompact (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) := inferInstance
  let U : (Proj (homogeneousSubmodule σ R)).affineOpens :=
    ⟨MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i, MvPolynomialClosure.MvPolynomial.coordinateOpen_isAffineOpen i⟩
  let r := CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j
  have hr : r ∈ (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j).ker.ideal U := by
    rw [CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_span]
    exact Ideal.mem_span_singleton_self r
  have hFrame := coordinateHyperplaneIdealModuleTrivialization_eq_canonical (R := R) i j
  dsimp only at hFrame
  have h := IdealOverFrame.localIdealGeneratorOverTrivialization_inv_comp
        (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j) U r hr
          (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_span i j)
          (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation_mem_nonZeroDivisors i j)
  simpa only [coordinateHyperplaneIdealOverTrivialization, hFrame] using h

/-- In a standard-chart frame, the canonical coordinate section of `O(1)` is
multiplication by the local equation of the coordinate hyperplane. -/
theorem coordinateHyperplanePoleUnitHom_over_comp_trivialization
    (i j : σ) :
    ((HyperplanePole.MvPolynomial.coordinateHyperplanePoleUnitHom (R := R) j).over
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)) ≫
        (Dual.SheafOfModules.dualOverIsoOfIso
          (Proj (homogeneousSubmodule σ R)).ringCatSheaf
          (IdealModule.idealModule
            (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
          (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
          (Invertible.Scheme.Modules.overTrivializationOfRestrictIso
    (IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j))
    (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
            (HyperplaneFrames.MvPolynomial.coordinateHyperplaneIdealModuleTrivialization
              (R := R) i j).symm)).hom =
      Dual.SheafOfModules.overUnitScalarEnd
        (Proj (homogeneousSubmodule σ R)).ringCatSheaf
        (MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i)
        (CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j) := by
  let X := Proj (homogeneousSubmodule σ R)
  let M := IdealModule.idealModule (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)
  let a : M ⟶ Invertible.Scheme.Modules.unitObj X :=
    IdealModule.idealModuleToUnit (SpaceHyperplane.MvPolynomial.coordinateHyperplaneι (R := R) j)
  let U := MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) i
  let e := coordinateHyperplaneIdealOverTrivialization (R := R) i j
  let r := CoordinateExtensions.MvPolynomial.coordinateHyperplaneLocalEquation (R := R) i j
  have h : e.inv ≫ a.over U = Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r :=
    coordinateHyperplaneIdealOverTrivialization_inv_comp (R := R) i j
  apply (Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).injective
  have hr : (Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U)
      (Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) = r := by
    change (Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U)
      ((Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U).symm r) = r
    exact (Dual.SheafOfModules.dualUnitSectionsEquiv
      X.ringCatSheaf U).apply_symm_apply r
  rw [hr]
  change
    (SheafOfModules.Hom.over ((Dual.Scheme.Modules.dualUnitObjIso (X := X)).inv ≫
        Dual.Scheme.Modules.dualMapObj a) U ≫
      (Dual.SheafOfModules.dualOverIsoOfIso
        X.ringCatSheaf M U e).hom).val.app (.op (Over.mk (𝟙 U)))
          (show (X.ringCatSheaf.over U).obj.obj
            (.op (Over.mk (𝟙 U))) from 1) = r
  erw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    ModuleCat.comp_apply]
  change Dual.SheafOfModules.dualTrivializationLinearEquiv
      X.ringCatSheaf M U e
        (Dual.SheafOfModules.dualPrecomp X.ringCatSheaf a U
          ((Dual.SheafOfModules.dualUnitLinearEquiv
            X.ringCatSheaf U).symm 1)) = r
  change Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (e.inv ≫ (a.over U ≫
        (Dual.SheafOfModules.dualUnitLinearEquiv
          X.ringCatSheaf U).symm 1)) = r
  let alpha := (Dual.SheafOfModules.dualUnitLinearEquiv
    X.ringCatSheaf U).symm 1
  have hcomp : (e.inv ≫ a.over U) ≫ alpha =
      Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r ≫ alpha :=
    congrArg (fun q ↦ q ≫ alpha) h
  have halpha : alpha = 𝟙 _ := by
    change Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U 1 = 𝟙 _
    exact (Dual.SheafOfModules.overUnitScalarEndRingHom
      X.ringCatSheaf U).map_one
  change Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (e.inv ≫ (a.over U ≫ alpha)) = r
  have h₁ : Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (e.inv ≫ (a.over U ≫ alpha)) =
      Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
        ((e.inv ≫ a.over U) ≫ alpha) :=
    congrArg _ (Category.assoc _ _ _).symm
  have h₂ : Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      ((e.inv ≫ a.over U) ≫ alpha) =
      Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
        (Dual.SheafOfModules.overUnitScalarEnd
          X.ringCatSheaf U r ≫ alpha) := congrArg _ hcomp
  have h₃ : Dual.SheafOfModules.dualUnitLinearEquiv X.ringCatSheaf U
      (Dual.SheafOfModules.overUnitScalarEnd
        X.ringCatSheaf U r ≫ alpha) = r := by
    rw [halpha, Category.comp_id]
    change (Dual.SheafOfModules.dualUnitSectionsEquiv X.ringCatSheaf U)
      (Dual.SheafOfModules.overUnitScalarEnd X.ringCatSheaf U r) = r
    exact hr
  exact h₁.trans (h₂.trans h₃)

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.HyperplaneCoordinateSection.MvPolynomial
