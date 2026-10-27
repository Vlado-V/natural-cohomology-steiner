module

public import OAI.AlgebraicGeometry.SheafCohomology.CoherentVanishing
public import OAI.AlgebraicGeometry.SheafCohomology.AffineH

set_option backward.privateInPublic true
@[expose] public section

/-! # Affine Comparison -/

namespace OAI.AlgebraicGeometry.SheafCohomology.AffineComparison.Projective

noncomputable section

/-! Identification of ProjectiveCohomology's complex cohomology with the actual affine-development cohomology. -/

/-- Both developments use the same underlying sheaf; coefficient extension
identifies their actual Ext groups. -/
def coherentCohomologyEquivZariski (A : ComplexMultiplication.CMAbelianVariety.CM.AbelianVariety) (M : A.carrier.Modules) (n : ℕ) :
    Sheaves.Projective.coherentCohomology A M n ≃ AffineH.Projective.H M n :=
  CoherentVanishing.Projective.complexSheafCohomologyEquiv (TopCat.of A.carrier) (Sheaves.Projective.complexSheaf A M) n

end

end OAI.AlgebraicGeometry.SheafCohomology.AffineComparison.Projective
