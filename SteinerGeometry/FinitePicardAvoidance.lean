import SteinerGeometry.TorsionLineClasses
import OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterDetection
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteHopfPresentation
import OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGroupMaps

/-! Finite avoidance and torsion for actual pullback-trivial line classes.
No dual abelian variety or representability theorem is needed here. -/
noncomputable section
namespace SteinerGeometry.FinitePicardAvoidance
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open OAI.AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open OAI.AlgebraicGeometry.AbelianModuli.HilbertConstruction
universe u v

attribute [local instance] Over.cartesianMonoidalCategory

/-- Finite faithfully flat group morphisms have finite actual line-class
pullback kernels over a field. -/
theorem finite_lineKernel_of_finite_flat
    {k : Type u} [Field k] {A B : Over (Spec (.of k))}
    [GrpObj A] [GrpObj B] [IsCommMonObj A]
    (f : A ⟶ B) [IsMonHom f]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    [IsFinite f.left] [Flat f.left] [Surjective f.left] :
    Finite {q : AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.IsoClass B.left //
      AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.pullbackClass f.left q = AbelianModuli.HilbertConstruction.Line.Bundles.LineBundle.trivialClass A.left} := by
  have sq := (Picard.Homomorphisms.Kernel.Construction.kernelScheme_isPullback f).map (Over.forget (Spec (.of k)))
  have hfin : IsFinite (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) sq (inferInstanceAs (IsFinite f.left))
  have : IsAffine (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).left := isAffine_of_isAffineHom (Picard.Homomorphisms.Kernel.Construction.kernelScheme f).hom
  let G : Grp (Over (Spec (.of k))) := Grp.mk (Picard.Homomorphisms.Kernel.Construction.kernelScheme f)
  have : IsFinite G.X.hom := hfin
  have : IsCommMonObj G.X := Picard.Homomorphisms.KernelGroup.Construction.kernelSchemeGroup_commutative f
  obtain ⟨R, hR, _, ⟨i⟩⟩ := Picard.Homomorphisms.FiniteHopfPresentation.Construction.finite_commutative_hopfPresentation k G
  have : Module.Finite k R := hR
  let e : ((hopfSpec (.of k)).obj (.op R)).X ≅ Picard.Homomorphisms.Kernel.Construction.kernelScheme f :=
    (Grp.forget (Over (Spec (.of k)))).mapIso i
  have : IsMonHom e.hom := inferInstanceAs (IsMonHom i.hom.hom.hom)
  exact OAI.AlgebraicGeometry.AbelianScheme.CartierDuality.LineCharacterDetection.Construction.KernelCharacters.finite_pullbackKernel f R e

/-- A map with finite fibers cannot carry an infinite set into a finite set. -/
theorem exists_map_not_mem_of_finite_fibers {X : Type u} {Y : Type v}
    [Infinite X] (f : X → Y)
    (hf : ∀ y, Finite {x : X // f x = y}) (s : Set Y) (hs : s.Finite) :
    ∃ x, f x ∉ s := by
  classical
  have hpre : (f ⁻¹' s).Finite := by
    have hfi : ∀ y ∈ s, ({x : X | f x = y} : Set X).Finite := by
      intro y _
      change Finite {x : X // f x = y}
      exact hf y
    convert hs.biUnion hfi using 1
    ext x
    simp
  obtain ⟨x, hx⟩ := hpre.exists_notMem
  exact ⟨x, hx⟩

/-- The target of a map with finite fibers from an infinite type is infinite. -/
theorem infinite_of_finite_fibers {X : Type u} {Y : Type v} [Infinite X]
    (f : X → Y) (hf : ∀ y, Finite {x : X // f x = y}) : Infinite Y := by
  by_contra hn
  have : Finite Y := not_infinite_iff_finite.mp hn
  obtain ⟨x, hx⟩ := exists_map_not_mem_of_finite_fibers f hf Set.univ (Set.toFinite _)
  exact hx (Set.mem_univ _)

/-- An injective parameter family and a finite-fiber map can simultaneously
avoid any finite set in the target. -/
theorem exists_composite_not_mem {T : Type u} {X : Type v} {Y : Type*}
    [Infinite T] (family : T → X) (hinj : Function.Injective family)
    (f : X → Y) (hf : ∀ y, Finite {x : X // f x = y})
    (s : Set Y) (hs : s.Finite) : ∃ t, f (family t) ∉ s := by
  apply exists_map_not_mem_of_finite_fibers (fun t => f (family t)) ?_ s hs
  intro y
  have : Finite {x : X // f x = y} := hf y
  apply Finite.of_injective (fun t : {t : T // f (family t) = y} =>
    (⟨family t.val, t.property⟩ : {x : X // f x = y}))
  intro a b h
  apply Subtype.ext
  exact hinj (congrArg Subtype.val h)

/-- All actual line-class pullback fibers are finite under a finite flat
surjective homomorphism of smooth proper connected algebraic groups. -/
theorem finite_pullback_fiber {k : Type u} [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsCommMonObj A]
    (f : A ⟶ B) [IsMonHom f] [Smooth A.hom] [IsProper A.hom]
    [GeometricallyConnected A.hom] [IsFinite f.left] [Flat f.left] [Surjective f.left]
    (b : Line.Bundles.LineBundle.IsoClass A.left) :
    Finite {a : Line.Bundles.LineBundle.IsoClass B.left //
      Line.Bundles.LineBundle.pullbackClass f.left a = b} := by
  let p := Line.Bundles.LineBundle.pullbackClassMonoidHom f.left
  have : Finite p.ker :=
    finite_lineKernel_of_finite_flat f
  exact OAI.AlgebraicGeometry.Picard.Homomorphisms.FiniteGroupMaps.Construction.finite_monoidHom_fiber p b

/-- Tensoring a fixed actual line bundle preserves distinctness of a family. -/
theorem tensor_class_family_injective {X : Scheme.{u}} {T : Type v}
    (L : Line.Bundles.LineBundle X) (family : T → Line.Bundles.LineBundle X)
    (hinj : Function.Injective (fun t => Line.Bundles.LineBundle.classOf (family t))) :
    Function.Injective (fun t => Line.Bundles.LineBundle.classOf (L.tensor (family t))) := by
  intro a b h
  apply hinj
  exact mul_left_cancel (by simpa only [Line.Bundles.LineBundle.classOf_tensor] using h)

/-- A fixed-degree parameter family stays outside any finite list after
pullback along a finite-flat cover, for at least one parameter. -/
theorem exists_tensor_pullback_avoiding {k : Type u} [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsCommMonObj A]
    (f : A ⟶ B) [IsMonHom f] [Smooth A.hom] [IsProper A.hom]
    [GeometricallyConnected A.hom] [IsFinite f.left] [Flat f.left] [Surjective f.left]
    {T : Type v} [Infinite T]
    (L : Line.Bundles.LineBundle B.left) (family : T → Line.Bundles.LineBundle B.left)
    (hinj : Function.Injective (fun t => Line.Bundles.LineBundle.classOf (family t)))
    (forbidden : Set (Line.Bundles.LineBundle.IsoClass A.left)) (hforbidden : forbidden.Finite) :
    ∃ t, Line.Bundles.LineBundle.classOf ((L.tensor (family t)).pullback f.left) ∉ forbidden := by
  exact exists_composite_not_mem
    (fun t => Line.Bundles.LineBundle.classOf (L.tensor (family t)))
    (tensor_class_family_injective L family hinj)
    (Line.Bundles.LineBundle.pullbackClass f.left)
    (finite_pullback_fiber f) forbidden hforbidden


/-- A line trivialized by a finite faithfully flat group cover has finite order. -/
theorem pullback_trivial_isOfFinOrder {k : Type u} [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsCommMonObj A]
    (f : A ⟶ B) [IsMonHom f] [Smooth A.hom] [IsProper A.hom]
    [GeometricallyConnected A.hom] [IsFinite f.left] [Flat f.left] [Surjective f.left]
    (L : Line.Bundles.LineBundle B.left)
    (h : Nonempty ((L.pullback f.left).sheaf ≅ Line.Bundles.structureModule A.left)) :
    IsOfFinOrder (Line.Bundles.LineBundle.classOf L) := by
  have : Finite (Line.Bundles.LineBundle.pullbackClassMonoidHom f.left).ker :=
    finite_lineKernel_of_finite_flat f
  exact TorsionLineClasses.torsion_of_finite_pullbackKernel f.left L h

/-- An infinite supply of torsion classes lets a twist avoid any finite list
of pulled-back line classes, while keeping both Euler degrees fixed. -/
theorem exists_torsion_twist_avoiding {k : Type u} [Field k]
    {A B : Over (Spec (.of k))} [GrpObj A] [GrpObj B] [IsCommMonObj A]
    (f : A ⟶ B) [IsMonHom f] [Smooth A.hom] [IsProper A.hom]
    [GeometricallyConnected A.hom] [IsFinite f.left] [Flat f.left] [Surjective f.left]
    [Infinite (TorsionLineClasses.TorsionClass B.left)]
    (L : Line.Bundles.LineBundle B.left)
    (forbidden : Set (Line.Bundles.LineBundle.IsoClass A.left))
    (hforbidden : forbidden.Finite) :
    ∃ a : TorsionLineClasses.TorsionClass B.left,
      Line.Bundles.LineBundle.classOf
        ((L.tensor (TorsionLineClasses.representative a)).pullback f.left) ∉ forbidden :=
  exists_tensor_pullback_avoiding f L TorsionLineClasses.representative
    TorsionLineClasses.representative_class_injective forbidden hforbidden

end SteinerGeometry.FinitePicardAvoidance
