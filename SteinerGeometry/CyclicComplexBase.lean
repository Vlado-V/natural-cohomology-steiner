import SteinerGeometry.CyclicSubgroup
import OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveSpace

namespace SteinerGeometry

noncomputable section

open OAI.AlgebraicGeometry

/-- The base field used to construct a single Steiner matrix. -/
abbrev complexBase := Foundations.Scheme.ProjectiveSpace.complexBase

/-- An actual smooth proper connected one-dimensional complex group scheme. -/
abbrev EllipticScheme := AbelianModuli.HilbertConstruction.Abelian.Schemes.AbelianScheme 1 complexBase

end
end SteinerGeometry
