module

public import OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorEquivalence
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

set_option backward.privateInPublic true
@[expose] public section

/-! # Invertible Tensor Exact -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorExact

noncomputable section

/-! Tensoring by an actual invertible module preserves short exact sequences. -/

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

theorem invertibleTensor_shortExact {X : Scheme.{u}} (M : X.Modules)
    (hM : Invertible.Scheme.Modules.IsInvertible M) (S : ShortComplex X.Modules)
    (hS : S.ShortExact) :
    (S.map (InvertibleTensorEquivalence.invertibleTensorEquivalence M hM).functor).ShortExact :=
  hS.map_of_exact (InvertibleTensorEquivalence.invertibleTensorEquivalence M hM).functor

end

end OAI.AlgebraicGeometry.SheafCohomology.Projective.InvertibleTensorExact
