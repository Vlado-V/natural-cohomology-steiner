import SteinerGeometry.RectangularKernel

namespace SteinerGeometry

noncomputable section

variable (k m : ℕ) [NeZero k] [NeZero m]

theorem rectangularLattice_mul_le : rectangularLattice (k * m) ≤ rectangularLattice k := by
  intro z hz
  obtain ⟨⟨a, ha⟩, hb⟩ := rectangularLattice_coordinates (k * m) z hz
  apply (mem_rectangularLattice_iff k z).mpr
  refine ⟨⟨(m : ℤ) * a, ?_⟩, hb⟩
  simpa [Nat.cast_mul, Int.cast_mul, mul_assoc] using ha

theorem nsmul_rectangular_mem_mul (z : ℂ) (hz : z ∈ rectangularLattice k) :
    m • z ∈ rectangularLattice (k * m) := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := rectangularLattice_coordinates k z hz
  apply (mem_rectangularLattice_iff (k * m) _).mpr
  constructor
  · refine ⟨a, ?_⟩
    simp [nsmul_eq_mul, ← ha, mul_assoc, mul_comm]
  · exact ⟨(m : ℤ) * b, by simp [nsmul_eq_mul, ← hb]⟩

/-- The identity induces a cyclic cover with arbitrary fixed rectangular target. -/
def rectangularRelativeProjection : RectangularTorus (k * m) →+ RectangularTorus k :=
  QuotientAddGroup.map (rectangularLattice (k * m)).toAddSubgroup
    (rectangularLattice k).toAddSubgroup (AddMonoidHom.id ℂ) (rectangularLattice_mul_le k m)

@[simp] theorem rectangularRelativeProjection_mk (z : ℂ) :
    rectangularRelativeProjection k m (QuotientAddGroup.mk z) = QuotientAddGroup.mk z := rfl

def rectangularRelativeInteger : ℤ →+ RectangularTorus (k * m) :=
  (QuotientAddGroup.mk' (rectangularLattice (k * m)).toAddSubgroup).comp
    (show ℤ →+ ℂ from
      { toFun := fun a => (k : ℂ) * (a : ℂ)
        map_zero' := by simp
        map_add' a b := by simp [mul_add] })

@[simp] theorem rectangularRelativeInteger_apply (a : ℤ) :
    rectangularRelativeInteger k m a = QuotientAddGroup.mk ((k : ℂ) * (a : ℂ)) := by
  rfl

theorem rectangularRelativeInteger_period : rectangularRelativeInteger k m m = 0 := by
  rw [rectangularRelativeInteger_apply]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply (mem_rectangularLattice_iff (k * m) _).mpr
  exact ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩

def rectangularRelativeCyclic : ZMod m →+ RectangularTorus (k * m) :=
  ZMod.lift m ⟨rectangularRelativeInteger k m, rectangularRelativeInteger_period k m⟩

@[simp] theorem rectangularRelativeCyclic_intCast (a : ℤ) :
    rectangularRelativeCyclic k m (a : ZMod m) = QuotientAddGroup.mk ((k : ℂ) * (a : ℂ)) := by
  rw [rectangularRelativeCyclic, ZMod.lift_coe, rectangularRelativeInteger_apply]

theorem rectangularRelativeCyclic_injective : Function.Injective (rectangularRelativeCyclic k m) := by
  apply (ZMod.lift_injective m).mpr
  intro a ha
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd a m).mpr
  rw [rectangularRelativeInteger_apply] at ha
  have hm := (QuotientAddGroup.eq_zero_iff ((k : ℂ) * (a : ℂ))).mp ha
  obtain ⟨⟨b, hb⟩, _⟩ := rectangularLattice_coordinates (k * m) _ hm
  have hkm : (k : ℝ) * ((m : ℝ) * b) = (k : ℝ) * a := by
    simpa [Nat.cast_mul, mul_assoc] using hb
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  have hmb := mul_left_cancel₀ hk hkm
  refine ⟨b, ?_⟩
  exact_mod_cast hmb.symm

theorem rectangularRelativeCyclic_projection (a : ZMod m) :
    rectangularRelativeProjection k m (rectangularRelativeCyclic k m a) = 0 := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  rw [rectangularRelativeCyclic_intCast, rectangularRelativeProjection_mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply (mem_rectangularLattice_iff k _).mpr
  exact ⟨⟨a, by simp⟩, ⟨0, by simp⟩⟩

theorem rectangularRelativeProjection_kernel_surjective (x : RectangularTorus (k * m))
    (hx : rectangularRelativeProjection k m x = 0) :
    ∃ a : ZMod m, rectangularRelativeCyclic k m a = x := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hz : z ∈ rectangularLattice k := (QuotientAddGroup.eq_zero_iff z).mp hx
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := rectangularLattice_coordinates k z hz
  refine ⟨(a : ZMod m), ?_⟩
  rw [rectangularRelativeCyclic_intCast]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply (mem_rectangularLattice_iff (k * m) _).mpr
  refine ⟨⟨0, ?_⟩, ⟨-b, ?_⟩⟩
  · simp [← ha]
  · simp [← hb]

def rectangularRelativeKernelEquiv : ZMod m ≃+ (rectangularRelativeProjection k m).ker :=
  AddEquiv.ofBijective
    (show ZMod m →+ (rectangularRelativeProjection k m).ker from
      { toFun := fun a => ⟨rectangularRelativeCyclic k m a, rectangularRelativeCyclic_projection k m a⟩
        map_zero' := Subtype.ext (map_zero _)
        map_add' a b := Subtype.ext (map_add _ a b) })
    ⟨fun a b h => rectangularRelativeCyclic_injective k m (congrArg Subtype.val h),
      fun x => by
        obtain ⟨a, ha⟩ := rectangularRelativeProjection_kernel_surjective k m x.val x.property
        exact ⟨a, Subtype.ext ha⟩⟩

theorem rectangularProjection_surjective : Function.Surjective (rectangularProjection k) := by
  intro x
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  exact ⟨QuotientAddGroup.mk z, rfl⟩

instance rectangularTorus_infinite : Infinite (RectangularTorus k) :=
  Infinite.of_surjective (rectangularProjection k) (rectangularProjection_surjective k)

end
end SteinerGeometry
