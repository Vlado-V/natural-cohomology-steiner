import SteinerGeometry.RectangularLattice

namespace SteinerGeometry

noncomputable section

variable (n : ℕ) [NeZero n]

abbrev RectangularTorus := ℂ ⧸ (rectangularLattice n).toAddSubgroup

/-- The identity map of the complex line descends to the rectangular cover. -/
def rectangularProjection : RectangularTorus n →+ SquareTorus :=
  QuotientAddGroup.map (rectangularLattice n).toAddSubgroup squareLattice.toAddSubgroup
    (AddMonoidHom.id ℂ) (rectangularLattice_le_square n)

@[simp] theorem rectangularProjection_mk (z : ℂ) :
    rectangularProjection n (QuotientAddGroup.mk z) = QuotientAddGroup.mk z := rfl

/-- Integral real points on the rectangular torus. -/
def rectangularIntegerPoint : ℤ →+ RectangularTorus n :=
  (QuotientAddGroup.mk' (rectangularLattice n).toAddSubgroup).comp (Int.castAddHom ℂ)

@[simp] theorem rectangularIntegerPoint_apply (a : ℤ) :
    rectangularIntegerPoint n a = QuotientAddGroup.mk (a : ℂ) := rfl

theorem rectangularIntegerPoint_period : rectangularIntegerPoint n n = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply (mem_rectangularLattice_iff n _).mpr
  exact ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩

/-- The cyclic subgroup induced by the real period. -/
def rectangularCyclicPoint : ZMod n →+ RectangularTorus n :=
  ZMod.lift n ⟨rectangularIntegerPoint n, rectangularIntegerPoint_period n⟩

@[simp] theorem rectangularCyclicPoint_intCast (a : ℤ) :
    rectangularCyclicPoint n (a : ZMod n) = QuotientAddGroup.mk (a : ℂ) :=
  ZMod.lift_coe n _ a

theorem rectangularCyclicPoint_injective : Function.Injective (rectangularCyclicPoint n) := by
  apply (ZMod.lift_injective n).mpr
  intro a ha
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd a n).mpr
  have hm := (QuotientAddGroup.eq_zero_iff (a : ℂ)).mp ha
  obtain ⟨⟨b, hb⟩, _⟩ := rectangularLattice_coordinates n (a : ℂ) hm
  refine ⟨b, ?_⟩
  exact_mod_cast hb.symm

theorem rectangularCyclicPoint_projection (a : ZMod n) :
    rectangularProjection n (rectangularCyclicPoint n a) = 0 := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective a
  rw [rectangularCyclicPoint_intCast, rectangularProjection_mk]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply (Complex.basisOneI.mem_span_iff_repr_mem ℤ (a : ℂ)).mpr
  intro i
  fin_cases i
  · exact ⟨a, by simp [Complex.coe_basisOneI_repr]⟩
  · exact ⟨0, by simp [Complex.coe_basisOneI_repr]⟩

theorem rectangularProjection_kernel_surjective (x : RectangularTorus n)
    (hx : rectangularProjection n x = 0) :
    ∃ a : ZMod n, rectangularCyclicPoint n a = x := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  have hz : z ∈ squareLattice := (QuotientAddGroup.eq_zero_iff z).mp hx
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := squareLattice_coordinates z hz
  refine ⟨(a : ZMod n), ?_⟩
  rw [rectangularCyclicPoint_intCast]
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  apply (mem_rectangularLattice_iff n _).mpr
  refine ⟨⟨0, ?_⟩, ⟨-b, ?_⟩⟩
  · simp [← ha]
  · simp [← hb]

/-- The kernel of the rectangular cover is precisely the cyclic group of order `n`. -/
def rectangularKernelEquiv : ZMod n ≃+ (rectangularProjection n).ker :=
  AddEquiv.ofBijective
    (show ZMod n →+ (rectangularProjection n).ker from
    { toFun := fun a => ⟨rectangularCyclicPoint n a, rectangularCyclicPoint_projection n a⟩
      map_zero' := Subtype.ext (map_zero _)
      map_add' a b := Subtype.ext (map_add _ a b) })
    ⟨fun a b h => rectangularCyclicPoint_injective n (congrArg Subtype.val h),
      fun x => by
        obtain ⟨a, ha⟩ := rectangularProjection_kernel_surjective n x.val x.property
        exact ⟨a, Subtype.ext ha⟩⟩

end
end SteinerGeometry
