module

public import OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.Finite.CharacterBasis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Pi

set_option backward.privateInPublic true
@[expose] public section

/-! # Character Algebra Basis -/

namespace OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterAlgebraBasis

noncomputable section

/-! The character basis persists over every algebra of the coefficient field, including rings with zero divisors. -/
universe u v w
variable (K : Type u) [Field K] (G : Type v) [CommGroup G] [Fintype G]
    [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (R : Type w) [CommRing R] [Algebra K R]

def finiteAbelianCharacterAlgebraBasis : Module.Basis (G →* Kˣ) R (G → R) := by
  classical
  exact ((Finite.CharacterBasis.finiteAbelianCharacterBasis K G).baseChange R).map (TensorProduct.piScalarRight K R R G)

@[simp]
theorem finiteAbelianCharacterAlgebraBasis_apply (χ : G →* Kˣ) (g : G) :
    finiteAbelianCharacterAlgebraBasis K G R χ g = algebraMap K R (χ g : K) := by
  classical
  simp only [finiteAbelianCharacterAlgebraBasis, Module.Basis.map_apply, Module.Basis.baseChange_apply,
    TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    Finite.CharacterBasis.finiteAbelianCharacterBasis_apply, Algebra.smul_def, mul_one]

end

end OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction.CharacterAlgebraBasis
