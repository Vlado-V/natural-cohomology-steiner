import SteinerGeometry.RectangularKernel

/-! The four actual two-torsion points of the rectangular complex torus. -/
noncomputable section
namespace SteinerGeometry
variable (k : ℕ) [NeZero k]

/-- Doubling on the actual period quotient. -/
def rectangularDoubling : RectangularTorus k →+ RectangularTorus k :=
  2 • AddMonoidHom.id (RectangularTorus k)

@[simp] theorem rectangularDoubling_apply (x : RectangularTorus k) :
    rectangularDoubling k x = 2 • x := rfl

/-- Integral multiples of the real half-period. -/
def rectangularHalfRealInteger : ℤ →+ RectangularTorus k where
  toFun a := QuotientAddGroup.mk ((k : ℂ) * (a : ℂ) / 2)
  map_zero' := by simp
  map_add' a b := by simp only [Int.cast_add, mul_add, add_div, QuotientAddGroup.mk_add]

/-- Integral multiples of the imaginary half-period. -/
def rectangularHalfImagInteger : ℤ →+ RectangularTorus k where
  toFun a := QuotientAddGroup.mk ((a : ℂ) * Complex.I / 2)
  map_zero' := by simp
  map_add' a b := by simp only [Int.cast_add, add_mul, add_div, QuotientAddGroup.mk_add]

theorem rectangularHalfRealInteger_two : rectangularHalfRealInteger k 2 = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply (mem_rectangularLattice_iff k _).mpr
  exact ⟨⟨1, by simp⟩, ⟨0, by simp⟩⟩

theorem rectangularHalfImagInteger_two : rectangularHalfImagInteger k 2 = 0 := by
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply (mem_rectangularLattice_iff k _).mpr
  exact ⟨⟨0, by simp⟩, ⟨1, by simp⟩⟩

def rectangularHalfReal : ZMod 2 →+ RectangularTorus k :=
  ZMod.lift 2 ⟨rectangularHalfRealInteger k, rectangularHalfRealInteger_two k⟩

def rectangularHalfImag : ZMod 2 →+ RectangularTorus k :=
  ZMod.lift 2 ⟨rectangularHalfImagInteger k, rectangularHalfImagInteger_two k⟩

@[simp] theorem rectangularHalfReal_intCast (a : ℤ) :
    rectangularHalfReal k (a : ZMod 2) = QuotientAddGroup.mk ((k : ℂ) * (a : ℂ) / 2) :=
  ZMod.lift_coe 2 _ a

@[simp] theorem rectangularHalfImag_intCast (a : ℤ) :
    rectangularHalfImag k (a : ZMod 2) = QuotientAddGroup.mk ((a : ℂ) * Complex.I / 2) :=
  ZMod.lift_coe 2 _ a

/-- The four half-period classes, indexed additively by two binary coordinates. -/
def rectangularTwoTorsionPoint : ZMod 2 × ZMod 2 →+ RectangularTorus k :=
  (rectangularHalfReal k).comp (AddMonoidHom.fst _ _) +
    (rectangularHalfImag k).comp (AddMonoidHom.snd _ _)

@[simp] theorem rectangularTwoTorsionPoint_intCast (a b : ℤ) :
    rectangularTwoTorsionPoint k ((a : ZMod 2), (b : ZMod 2)) =
      QuotientAddGroup.mk ((k : ℂ) * (a : ℂ) / 2 + (b : ℂ) * Complex.I / 2) := by
  simp [rectangularTwoTorsionPoint, ← QuotientAddGroup.mk_add]

theorem rectangularTwoTorsionPoint_doubled (x : ZMod 2 × ZMod 2) :
    rectangularDoubling k (rectangularTwoTorsionPoint k x) = 0 := by
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective x.1
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective x.2
  obtain rfl : x = ((a : ZMod 2), (b : ZMod 2)) := Prod.ext ha.symm hb.symm
  rw [rectangularTwoTorsionPoint_intCast, rectangularDoubling_apply]
  change 2 • (QuotientAddGroup.mk'
    (rectangularLattice k).toAddSubgroup) _ = 0
  rw [← map_nsmul]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  apply (mem_rectangularLattice_iff k _).mpr
  constructor
  · exact ⟨a, by simp [nsmul_eq_mul]; ring⟩
  · exact ⟨b, by simp [nsmul_eq_mul]; ring⟩

theorem rectangularTwoTorsionPoint_injective :
    Function.Injective (rectangularTwoTorsionPoint k) := by
  apply (injective_iff_map_eq_zero (rectangularTwoTorsionPoint k)).mpr
  intro x hx
  obtain ⟨a, ha⟩ := ZMod.intCast_surjective x.1
  obtain ⟨b, hb⟩ := ZMod.intCast_surjective x.2
  obtain rfl : x = ((a : ZMod 2), (b : ZMod 2)) := Prod.ext ha.symm hb.symm
  rw [rectangularTwoTorsionPoint_intCast] at hx
  have hz := (QuotientAddGroup.eq_zero_iff _).mp hx
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := rectangularLattice_coordinates k _ hz
  have hcr : (k : ℝ) * (a : ℝ) / 2 = (k : ℝ) * (c : ℝ) := by
    simpa using hc.symm
  have hdr : (b : ℝ) / 2 = (d : ℝ) := by simpa using hd.symm
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  have hac : (a : ℝ) = 2 * (c : ℝ) := by
    apply (mul_left_cancel₀ hk)
    nlinarith [hcr]
  have hbd : (b : ℝ) = 2 * (d : ℝ) := by linarith [hdr]
  have ha0 : (a : ZMod 2) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd a 2).mpr
    exact ⟨c, by exact_mod_cast hac⟩
  have hb0 : (b : ZMod 2) = 0 := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd b 2).mpr
    exact ⟨d, by exact_mod_cast hbd⟩
  exact Prod.ext ha0 hb0

theorem rectangularDoubling_kernel_surjective (x : RectangularTorus k)
    (hx : rectangularDoubling k x = 0) :
    ∃ a : ZMod 2 × ZMod 2, rectangularTwoTorsionPoint k a = x := by
  obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [rectangularDoubling_apply] at hx
  change 2 • (QuotientAddGroup.mk'
    (rectangularLattice k).toAddSubgroup) z = 0 at hx
  rw [← map_nsmul] at hx
  have hz := (QuotientAddGroup.eq_zero_iff _).mp hx
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := rectangularLattice_coordinates k _ hz
  refine ⟨((a : ZMod 2), (b : ZMod 2)), ?_⟩
  rw [rectangularTwoTorsionPoint_intCast]
  congr 1
  apply Complex.ext
  · have ha' : (k : ℝ) * (a : ℝ) = 2 * z.re := by simpa [nsmul_eq_mul] using ha
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.mul_re,
      Complex.natCast_re, Complex.intCast_re, Complex.natCast_im, Complex.intCast_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_div, add_zero]
    linarith
  · have hb' : (b : ℝ) = 2 * z.im := by simpa [nsmul_eq_mul] using hb
    simp only [Complex.add_im, Complex.div_ofNat_im, Complex.mul_im,
      Complex.natCast_re, Complex.intCast_re, Complex.natCast_im, Complex.intCast_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, mul_one, add_zero, zero_add, zero_div]
    linarith

/-- Doubling has exactly the four half-period classes in its kernel. -/
def rectangularDoublingKernelEquiv : (ZMod 2 × ZMod 2) ≃+ (rectangularDoubling k).ker :=
  AddEquiv.ofBijective
    (show (ZMod 2 × ZMod 2) →+ (rectangularDoubling k).ker from
      { toFun := fun a => ⟨rectangularTwoTorsionPoint k a, rectangularTwoTorsionPoint_doubled k a⟩
        map_zero' := Subtype.ext (map_zero _)
        map_add' a b := Subtype.ext (map_add _ a b) })
    ⟨fun a b h => rectangularTwoTorsionPoint_injective k (congrArg Subtype.val h),
      fun x => by
        obtain ⟨a, ha⟩ := rectangularDoubling_kernel_surjective k x.val x.property
        exact ⟨a, Subtype.ext ha⟩⟩

/-- The actual analytic doubling kernel has four elements. -/
theorem rectangularDoubling_kernel_card : Nat.card (rectangularDoubling k).ker = 4 := by
  rw [← Nat.card_congr (rectangularDoublingKernelEquiv k).toEquiv]
  simp

end SteinerGeometry
