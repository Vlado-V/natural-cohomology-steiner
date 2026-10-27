import SteinerGeometry.LineClassArithmetic
import SteinerGeometry.SectionTensorMonomials

/-! Class arithmetic for the actual monomial lines in the symmetric kernel. -/
noncomputable section
namespace SteinerGeometry
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction

universe u

/-- The ordered tensor line represents the product of its actual factor classes. -/
theorem tensorLineFactors_class {X : Scheme.{u}} (s : ℕ)
    (L : Fin s → Line.Bundles.LineBundle X) :
    Line.Bundles.LineBundle.classOf (tensorLineFactors s L) =
      ∏ j, Line.Bundles.LineBundle.classOf (L j) := by
  induction s with
  | zero => simp [tensorLineFactors]
  | succ s ih =>
    simp only [tensorLineFactors, Line.Bundles.LineBundle.classOf_tensor, Fin.prod_univ_succ]
    rw [ih]

/-- Pointwise inverse pairings combine to an inverse pairing of the actual
ordered tensor lines. No choice of a particular dual construction is needed. -/
theorem tensorLineFactors_inverse_pairing {X : Scheme.{0}} (s : ℕ)
    (L M : Fin s → Line.Bundles.LineBundle X)
    (h : ∀ j, Nonempty (((L j).tensor (M j)).sheaf ≅ Line.Bundles.structureModule X)) :
    Nonempty (((tensorLineFactors s L).tensor (tensorLineFactors s M)).sheaf ≅
      Line.Bundles.structureModule X) := by
  have heq : Line.Bundles.LineBundle.classOf
      ((tensorLineFactors s L).tensor (tensorLineFactors s M)) =
      Line.Bundles.LineBundle.classOf (Line.Bundles.LineBundle.trivial X) := by
    rw [Line.Bundles.LineBundle.classOf_tensor, tensorLineFactors_class, tensorLineFactors_class,
      Line.Bundles.LineBundle.classOf_trivial, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j _
    exact Quotient.sound (h j)
  exact Quotient.exact heq

/-- An actual monomial of inverse lines is an inverse of the corresponding
primal monomial, using the same symmetric-word ordering. -/
theorem monomialLineBundle_inverse_pairing {X : Scheme.{0}} {m s : ℕ}
    (L M : Fin m → Line.Bundles.LineBundle X) (a : Sym (Fin m) s)
    (h : ∀ j, Nonempty (((L j).tensor (M j)).sheaf ≅ Line.Bundles.structureModule X)) :
    Nonempty (((monomialLineBundle L a).tensor (monomialLineBundle M a)).sheaf ≅
      Line.Bundles.structureModule X) :=
  tensorLineFactors_inverse_pairing s (fun j => L (symmetricWord a j))
    (fun j => M (symmetricWord a j)) (fun j => h (symmetricWord a j))

/-- Avoiding a primal monomial proves nontriviality of the inverse monomial
in the actual symmetric-kernel summand after twisting. -/
theorem monomialLineBundle_inverse_twist_nontrivial {X : Scheme.{0}} {m s : ℕ}
    (L M : Fin m → Line.Bundles.LineBundle X) (a : Sym (Fin m) s)
    (h : ∀ j, Nonempty (((L j).tensor (M j)).sheaf ≅ Line.Bundles.structureModule X))
    (N : Line.Bundles.LineBundle X)
    (hN : ¬ Nonempty (N.sheaf ≅ (monomialLineBundle L a).sheaf)) :
    ¬ Nonempty (((monomialLineBundle M a).tensor N).sheaf ≅
      Line.Bundles.structureModule X) :=
  EulerDegree.inverse_tensor_nontrivial_of_not_isomorphic
    (monomialLineBundle L a) (monomialLineBundle M a) N
    (monomialLineBundle_inverse_pairing L M a h).some hN

end SteinerGeometry
