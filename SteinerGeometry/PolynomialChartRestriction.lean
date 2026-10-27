import OAI.AlgebraicGeometry.SheafCohomology.Projective.StandardCech
import OAI.AlgebraicGeometry.SheafCohomology.Projective.PolynomialChartMap

/-! Dehomogeneous polynomial coordinates commute with passage to smaller
standard intersections which retain the initial chart. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SteinerGeometry.PolynomialChartRestriction
open CategoryTheory AlgebraicGeometry Opposite
open OAI.AlgebraicGeometry.SheafCohomology.Projective
universe u
variable {R : Type u} [CommRing R] {σ : Type} [Fintype σ] [LinearOrder σ]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem exponent_delete_succ {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n+1))
    (k : Fin (n+1)) (e : σ →₀ ℕ) :
    StandardCech.MvPolynomial.coordinateLaurentExponentDeleteAddMonoidHom a k
      (PolynomialChartMap.MvPolynomial.polynomialChartExponent
        (fun l => ((a.delete k.succ).1 l).down) e) =
    PolynomialChartMap.MvPolynomial.polynomialChartExponent (fun l => (a.1 l).down) e := by
  apply Subtype.ext
  ext i
  rfl

theorem polynomial_delete_succ {n : ℕ}
    (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) (n+1))
    (k : Fin (n+1)) (p : MvPolynomial σ Γ(Spec (.of R), ⊤)) :
    AddMonoidAlgebra.mapDomain
      (StandardCech.MvPolynomial.coordinateLaurentExponentDeleteAddMonoidHom a k)
      (PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤)
        (fun l => ((a.delete k.succ).1 l).down) p) =
    PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤)
      (fun l => (a.1 l).down) p := by
  induction p using MvPolynomial.induction_on with
  | C r =>
      change (AddMonoidAlgebra.mapDomainRingHom _ _)
        (PolynomialChartMap.MvPolynomial.polynomialChartRingHom _ _ (MvPolynomial.C r)) = _
      simp only [MvPolynomial.C_apply, PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial,
        AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single, exponent_delete_succ]
  | add p q hp hq =>
      simp only [map_add, AddMonoidAlgebra.mapDomain_add, hp, hq]
  | mul_X p j hp =>
      change (AddMonoidAlgebra.mapDomainRingHom _ _)
        (PolynomialChartMap.MvPolynomial.polynomialChartRingHom _ _ (p * MvPolynomial.X j)) = _
      simp only [map_mul]
      change AddMonoidAlgebra.mapDomain _ _ * AddMonoidAlgebra.mapDomain _ _ = _
      rw [hp]
      simp only [MvPolynomial.X, PolynomialChartMap.MvPolynomial.polynomialChartRingHom_monomial,
        AddMonoidAlgebra.mapDomain_single, exponent_delete_succ]

/-- A polynomial formula on the individual affine charts determines the same
formula on every ordered intersection, by the actual restriction maps. -/
theorem polynomial_on_intersections
    (c : ∀ j : σ, Γ(Proj (MvPolynomial.homogeneousSubmodule σ R),
      MvPolynomialClosure.MvPolynomial.coordinateOpen (R := R) j))
    (p : MvPolynomial σ Γ(Spec (.of R), ⊤))
    (hc : ∀ a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) 0,
      StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1
        ((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a.1 0)).op
          (c (a.1 0).down)) =
      PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤)
        (fun l => (a.1 l).down) p) :
    ∀ (n : ℕ) (a : OrderedBaseCech.Scheme.Modules.OrderedCechIndex (ULift.{u} σ) n),
      StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1
        ((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a.1 0)).op
          (c (a.1 0).down)) =
      PolynomialChartMap.MvPolynomial.polynomialChartRingHom Γ(Spec (.of R), ⊤)
        (fun l => (a.1 l).down) p := by
  intro n
  induction n with
  | zero => exact hc
  | succ n ih =>
      intro a
      let k : Fin (n+1) := Fin.last n
      let b := a.delete k.succ
      have h := StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv_naturality_delete_succ
        (R := R) a k
        ((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
          (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) b.1 0)).op
          (c (b.1 0).down))
      rw [ih b, polynomial_delete_succ] at h
      change StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv (R := R) a.1
        (((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
          (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a k.succ).op)
          (((Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
            (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) b.1 0)).op)
            (c (a.1 0).down))) = _ at h
      have hcomp :
          (Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
            (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) b.1 0)).op ≫
          (Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
            (StandardCech.MvPolynomial.coordinateOpenCechDelete (R := R) a k.succ).op =
          (Proj (MvPolynomial.homogeneousSubmodule σ R)).presheaf.map
            (homOfLE (StandardCech.MvPolynomial.coordinateOpenCechIntersection_le (R := R) a.1 0)).op := by
        rw [← Functor.map_comp]
        congr 1
      have hs := ConcreteCategory.congr_hom hcomp (c (a.1 0).down)
      exact (congrArg (StandardCech.MvPolynomial.coordinateOpenCechIntersectionBaseLaurentLinearEquiv
        (R := R) a.1) hs).symm.trans h

end SteinerGeometry.PolynomialChartRestriction
