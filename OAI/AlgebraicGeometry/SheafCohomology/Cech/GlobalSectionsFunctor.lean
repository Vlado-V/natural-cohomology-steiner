module

/-
Derived from AINTLIB:
  projects/ModularCurves/ModularCurves/ForMathlib/SheafDerivedGlobalSections.lean
The upstream AINTLIB repository is licensed under Apache 2.0.
This file has been modified.
-/
public import Mathlib.CategoryTheory.Sites.GlobalSections
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Abelian

set_option backward.privateInPublic true
@[expose] public section

/-! # Global Sections Functor -/

namespace OAI.AlgebraicGeometry.SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf

noncomputable section

open _root_.TopCat

/-! Actual global sections of native additive sheaves on the opens site. -/

open _root_.CategoryTheory _root_.TopologicalSpace

open _root_.TopCat.Sheaf

universe u

/-- The global-sections functor for additive sheaves on a topological space. -/
abbrev globalSectionsFunctor (X : TopCat.{u}) :
    CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      AddCommGrpCat.{u} :=
  CategoryTheory.Sheaf.Γ (Opens.grothendieckTopology X) AddCommGrpCat.{u}

end

end OAI.AlgebraicGeometry.SheafCohomology.Cech.GlobalSectionsFunctor.TopCat.Sheaf
