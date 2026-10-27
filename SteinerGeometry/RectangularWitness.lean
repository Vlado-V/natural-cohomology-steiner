import SteinerGeometry.RectangularIsogeny

namespace SteinerGeometry

noncomputable section

/-- A concrete projective elliptic source with a cyclic degree-`n` étale cover,
retaining both native rectangular models. -/
theorem exists_rectangularCyclicData (n : ℕ) [NeZero n] :
    ∃ (B : RectangularModel 1) (D : RectangularModel (1 * n))
      (q : CyclicEtaleIsogeny D.elliptic n), q.target = B.elliptic := by
  obtain ⟨B⟩ := exists_rectangularModel 1
  refine ⟨B, ?_⟩
  exact B.exists_cyclicEtaleCover n

end
end SteinerGeometry
