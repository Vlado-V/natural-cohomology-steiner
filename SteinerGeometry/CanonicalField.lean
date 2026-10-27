import Mathlib.Algebra.Field.IsField

namespace SteinerGeometry

/-- Give a ring known to be a field its field structure while retaining the
literal original commutative-ring operations. -/
@[instance_reducible] noncomputable def canonicalField
    {A : Type*} [CommRing A] (h : IsField A) : Field A :=
  { h.toField with toCommRing := inferInstance }

end SteinerGeometry
