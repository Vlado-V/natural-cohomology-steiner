import SteinerGeometry.ComplexLattice
import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion
import OAI.NumberTheory.ArithmeticGroups.Data

namespace SteinerGeometry

noncomputable section

/-- The square torus is projective by its explicit positive integral Riemann form. -/
theorem squareTorus_projective :
    OAI.NumberTheory.ArithmeticGroups.Data.CongruenceLevel.IsProjectiveComplexTorus ℂ
      squareLattice.toAddSubgroup := by
  let : DiscreteTopology squareLattice.toAddSubgroup :=
    inferInstanceAs (DiscreteTopology squareLattice)
  exact (OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion.riemann_projectivity_criterion
    ℂ squareLattice.toAddSubgroup).mpr
    ⟨lineHermitian, lineHermitian_symm, lineHermitian_positive, lineHermitian_integral⟩

end
end SteinerGeometry
