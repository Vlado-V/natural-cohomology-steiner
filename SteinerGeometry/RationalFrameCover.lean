module

public import SteinerGeometry.RankLocalFrames
public import SteinerGeometry.CurveRationalPoints

set_option backward.privateInPublic true
@[expose] public section

/-! # Rational-point frame neighborhoods cover a finite-type scheme

Over an algebraically closed field, a closed complement of the proposed
cover would have a closed point, hence a rational point. This turns the
actual rational-point frames into frames near every scheme point. -/
noncomputable section
namespace SteinerGeometry
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [IsAlgClosed K] {C : Scheme}

theorem rational_neighborhoods_cover
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p]
    (U : CurveRationalPoint p → C.Opens)
    (hU : ∀ a, a.val (⊥ : PrimeSpectrum K) ∈ U a) : iSup U = ⊤ := by
  let : JacobsonSpace C := LocallyOfFiniteType.jacobsonSpace p
  apply top_unique
  intro x _
  by_contra hx
  obtain ⟨y, hy, hyclosed⟩ := nonempty_inter_closedPoints
    (show (((iSup U : C.Opens) : Set C)ᶜ).Nonempty from ⟨x, hx⟩)
    (iSup U : C.Opens).isOpen.isClosed_compl.isLocallyClosed
  let a : CurveRationalPoint p :=
    ⟨pointOfClosedPoint p y hyclosed, pointOfClosedPoint_comp p y hyclosed⟩
  have hyU : y ∈ U a := by
    simpa only [a, pointOfClosedPoint_apply] using hU a
  exact hy (Opens.mem_iSup.mpr ⟨a, hyU⟩)

local instance rationalFrameCover_hasFiniteBiproducts (X : Scheme) : HasFiniteBiproducts X.Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- Actual rank-`n` rational-point frames extend to a finite free affine
frame neighborhood of every scheme point. -/
theorem affine_frame_at_of_rational_frames
    (p : C ⟶ Spec (.of K)) [LocallyOfFiniteType p] (M : C.Modules) (n : ℕ)
    (hframe : ∀ a : CurveRationalPoint p, ∃ U : C.Opens,
      a.val (⊥ : PrimeSpectrum K) ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅
        ⨁ fun _ : Fin n => SheafOfModules.unit U.toScheme.ringCatSheaf))
    (x : C) :
    ∃ U : C.Opens, IsAffineOpen U ∧ x ∈ U ∧
      Nonempty (M.restrict U.ι ≅ SheafOfModules.free (Fin n)) := by
  classical
  let U (a : CurveRationalPoint p) := (hframe a).choose
  have hU (a : CurveRationalPoint p) : a.val (⊥ : PrimeSpectrum K) ∈ U a :=
    (hframe a).choose_spec.1
  obtain ⟨a, ha⟩ := (IsOpenCover.mk (rational_neighborhoods_cover p U hU)).exists_mem x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset ha
  let j : V.toScheme ⟶ (U a).toScheme := C.homOfLE hVU
  let e : (Scheme.Modules.pullback (U a).ι).obj M ≅
      SheafOfModules.free (Fin n) :=
    Classical.choice (hframe a).choose_spec.2 ≪≫
      biproduct.isoCoproduct (C := (U a).toScheme.Modules)
        (fun _ : Fin n => SheafOfModules.unit (U a).toScheme.ringCatSheaf)
  refine ⟨V, hV, hxV, ⟨?_⟩⟩
  exact (Scheme.Modules.restrictFunctorIsoPullback V.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr (C.homOfLE_ι hVU).symm).app M ≪≫
    (Scheme.Modules.pullbackComp j (U a).ι).symm.app M ≪≫
    (Scheme.Modules.pullback j).mapIso e ≪≫ TildeFiniteProjective.pullbackFreeIso j (Fin n)

end SteinerGeometry
