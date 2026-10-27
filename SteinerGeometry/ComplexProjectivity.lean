module

public import SteinerGeometry.ComplexLattice
public import OAI.Geometry.ComplexTorus.RiemannProjectivity.ProjectivityCriterion
public import OAI.NumberTheory.ArithmeticGroups.Data

set_option backward.privateInPublic true
@[expose] public section

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
