import SteinerGeometry.ComplexProjectivity
import OAI.RepresentationTheory.Theta.Geometric.Torus.Data
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.Data.ZMod.QuotientGroup

namespace SteinerGeometry

open Module

noncomputable section

variable (n : ℕ) [NeZero n]

/-- The real basis `(n, i)` of the complex line. -/
def rectangularBasis : Basis (Fin 2) ℝ ℂ :=
  Complex.basisOneI.unitsSMul fun i =>
    if i = 0 then Units.mk0 (n : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne n)) else 1

@[simp] theorem rectangularBasis_zero : rectangularBasis n 0 = (n : ℂ) := by
  simp [rectangularBasis, Basis.unitsSMul_apply]

@[simp] theorem rectangularBasis_one : rectangularBasis n 1 = Complex.I := by
  simp [rectangularBasis, Basis.unitsSMul_apply]

/-- The period lattice `nℤ + iℤ`. -/
def rectangularLattice : Submodule ℤ ℂ :=
  Submodule.span ℤ (Set.range (rectangularBasis n))

instance rectangularLattice_discrete : DiscreteTopology (rectangularLattice n) := by
  unfold rectangularLattice
  infer_instance

instance rectangularLattice_full : IsZLattice ℝ (rectangularLattice n) := by
  unfold rectangularLattice
  infer_instance

instance rectangularTorus_compact :
    CompactSpace (ℂ ⧸ (rectangularLattice n).toAddSubgroup) := by
  apply isCompact_univ_iff.mp
  have hc := IsZLattice.isCompact_range_of_periodic (rectangularLattice n)
    (QuotientAddGroup.mk : ℂ → ℂ ⧸ (rectangularLattice n).toAddSubgroup)
    QuotientAddGroup.continuous_mk (by
      intro z w hw
      rw [QuotientAddGroup.mk_add, (QuotientAddGroup.eq_zero_iff w).mpr hw, add_zero])
  rwa [Set.range_eq_univ.mpr QuotientAddGroup.mk_surjective] at hc

theorem rectangularLattice_coordinates (z : ℂ) (hz : z ∈ rectangularLattice n) :
    (∃ a : ℤ, (n : ℝ) * (a : ℝ) = z.re) ∧ ∃ b : ℤ, (b : ℝ) = z.im := by
  have h := ((rectangularBasis n).mem_span_iff_repr_mem ℤ z).mp hz
  constructor
  · obtain ⟨a, ha⟩ := h 0
    have ha' : (a : ℝ) = (n : ℝ)⁻¹ * z.re := by
      simpa [rectangularBasis, Basis.repr_unitsSMul, Complex.coe_basisOneI_repr, Units.smul_def] using ha
    refine ⟨a, ?_⟩
    rw [ha']
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
    field_simp [hn]
  · simpa [rectangularBasis, Basis.repr_unitsSMul, Complex.coe_basisOneI_repr] using h 1

theorem mem_rectangularLattice_iff (z : ℂ) : z ∈ rectangularLattice n ↔
    (∃ a : ℤ, (n : ℝ) * (a : ℝ) = z.re) ∧ ∃ b : ℤ, (b : ℝ) = z.im := by
  constructor
  · exact rectangularLattice_coordinates n z
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have h0 : (n : ℂ) ∈ rectangularLattice n :=
      (rectangularBasis_zero n) ▸ Submodule.subset_span (Set.mem_range_self 0)
    have h1 : Complex.I ∈ rectangularLattice n :=
      (rectangularBasis_one n) ▸ Submodule.subset_span (Set.mem_range_self 1)
    have hsum := (rectangularLattice n).add_mem
      ((rectangularLattice n).smul_mem a h0) ((rectangularLattice n).smul_mem b h1)
    convert hsum using 1
    apply Complex.ext
    · simpa [mul_comm] using ha.symm
    · simpa using hb.symm

theorem rectangularLattice_le_square : rectangularLattice n ≤ squareLattice := by
  intro z hz
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := rectangularLattice_coordinates n z hz
  apply (Complex.basisOneI.mem_span_iff_repr_mem ℤ z).mpr
  intro i
  fin_cases i
  · exact ⟨(n : ℤ) * a, by simpa [Complex.coe_basisOneI_repr] using ha⟩
  · exact ⟨b, by simpa [Complex.coe_basisOneI_repr] using hb⟩

theorem nsmul_square_mem_rectangular (z : ℂ) (hz : z ∈ squareLattice) :
    n • z ∈ rectangularLattice n := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := squareLattice_coordinates z hz
  apply (mem_rectangularLattice_iff n _).mpr
  constructor
  · exact ⟨a, by simp [nsmul_eq_mul, ← ha]⟩
  · exact ⟨(n : ℤ) * b, by simp [nsmul_eq_mul, ← hb]⟩

theorem rectangularTorus_projective :
    OAI.NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus ℂ
      (rectangularLattice n).toAddSubgroup := by
  let : DiscreteTopology (rectangularLattice n).toAddSubgroup :=
    inferInstanceAs (DiscreteTopology (rectangularLattice n))
  apply (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion
    ℂ (rectangularLattice n).toAddSubgroup).mpr
  refine ⟨lineHermitian, lineHermitian_symm, lineHermitian_positive, ?_⟩
  intro u hu v hv
  exact lineHermitian_integral u (rectangularLattice_le_square n hu) v
    (rectangularLattice_le_square n hv)

/-- Actual projective period data for the rectangular elliptic torus. -/
def rectangularPeriodData : OAI.RepresentationTheory.Theta.Geometric.Torus.Data.CM.ProjectivePeriodData where
  space := ℂ
  periodIntegerLattice := rectangularLattice n
  projective := rectangularTorus_projective n

end
end SteinerGeometry
