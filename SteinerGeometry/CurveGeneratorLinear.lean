import Mathlib.Algebra.Module.Submodule.Union
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Linear algebra used to complete a finite-defect section frame on a curve. -/

namespace SteinerGeometry

noncomputable section

open Module Submodule

variable {K : Type*} [Field K] [Infinite K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {X : Type*} {F : X → Type*}
variable [∀ x, AddCommGroup (F x)] [∀ x, Module K (F x)]

/-- One section can simultaneously avoid finitely many proper fiber subspaces. -/
theorem exists_section_avoiding_finite_fiber_subspaces
    (e : ∀ x, V →ₗ[K] F x) (he : ∀ x, Function.Surjective (e x))
    (Z : Set X) (hZ : Z.Finite) (W : ∀ x, Submodule K (F x))
    (hW : ∀ x ∈ Z, W x ≠ ⊤) :
    ∃ v : V, ∀ x ∈ Z, e x v ∉ W x := by
  let : Finite Z := hZ.to_subtype
  have hp (x : Z) : (W x).comap (e x) ≠ ⊤ := by
    intro htop
    apply hW x x.property
    apply top_unique
    intro w _
    obtain ⟨v, rfl⟩ := he x w
    have hv : v ∈ (W x).comap (e x) := by rw [htop]; trivial
    exact hv
  obtain ⟨v, hv⟩ := Submodule.exists_forall_notMem_of_forall_ne_top
    (fun x : Z => (W x).comap (e x)) hp
  exact ⟨v, fun x hx => hv ⟨x, hx⟩⟩

omit [Infinite K] in
/-- A vector outside a subspace of codimension at most one completes it. -/
theorem sup_span_singleton_eq_top_of_finrank_bound
    {E : Type*} [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (W : Submodule K E) (hW : finrank K E ≤ finrank K W + 1)
    {v : E} (hv : v ∉ W) :
    W ⊔ span K {v} = ⊤ := by
  apply Submodule.eq_top_of_finrank_eq
  apply le_antisymm (Submodule.finrank_le _)
  rw [Submodule.finrank_sup_span_singleton hv]
  exact hW

/-- A frame that spans outside finitely many points and has at most one missing
dimension at each remaining point can be completed by a single fixed section.
All evaluations are evaluations of the same section space `V`. -/
theorem exists_section_completing_finite_defect
    [∀ x, FiniteDimensional K (F x)]
    (e : ∀ x, V →ₗ[K] F x) (he : ∀ x, Function.Surjective (e x))
    (W : ∀ x, Submodule K (F x))
    (hfinite : {x | W x ≠ ⊤}.Finite)
    (hcodim : ∀ x, finrank K (F x) ≤ finrank K (W x) + 1) :
    ∃ v : V, ∀ x, W x ⊔ span K {e x v} = ⊤ := by
  obtain ⟨v, hv⟩ := exists_section_avoiding_finite_fiber_subspaces e he
    {x | W x ≠ ⊤} hfinite W (fun _ hx => hx)
  refine ⟨v, fun x => ?_⟩
  by_cases h : W x = ⊤
  · rw [h, top_sup_eq]
  · exact sup_span_singleton_eq_top_of_finrank_bound (W x) (hcodim x) (hv x h)

omit [Infinite K] in
/-- The set of scalars causing cancellation at a point contains at most one
scalar, provided the two sections do not both vanish at that point. -/
theorem cancellation_scalars_subsingleton
    (e : ∀ x, V →ₗ[K] F x) (s t : V) (x : X)
    (h : e x s ≠ 0 ∨ e x t ≠ 0) :
    Set.Subsingleton {a : K | e x (s + a • t) = 0} := by
  intro a ha b hb
  simp only [map_add, map_smul] at ha hb
  have ht : e x t ≠ 0 := by
    intro ht
    have hs : e x s = 0 := by simpa [ht] using ha
    exact h.elim (fun h => h hs) (fun h => h ht)
  apply smul_left_injective K ht
  exact add_left_cancel (ha.trans hb.symm)

/-- On a curve, once two sections have no common zero and their dependence
locus is finite, a constant linear combination is nowhere zero. This is the
finite-avoidance step of the rank-at-least-two section construction. -/
theorem exists_nowherezero_combination
    (e : ∀ x, V →ₗ[K] F x) (s t : V)
    (hcommon : ∀ x, e x s ≠ 0 ∨ e x t ≠ 0)
    (hdep : {x | e x s ∈ span K {e x t}}.Finite) :
    ∃ a : K, ∀ x, e x (s + a • t) ≠ 0 := by
  let Z : Set X := {x | e x s ∈ span K {e x t}}
  have hfinite : (⋃ x ∈ Z, {a : K | e x (s + a • t) = 0}).Finite :=
    hdep.biUnion fun x _ => (cancellation_scalars_subsingleton e s t x (hcommon x)).finite
  obtain ⟨a, ha⟩ := hfinite.exists_notMem
  refine ⟨a, fun x hx => ha ?_⟩
  have hz : x ∈ Z := by
    change e x s ∈ span K {e x t}
    apply Submodule.mem_span_singleton.mpr
    refine ⟨-a, ?_⟩
    have hh : e x s + a • e x t = 0 := by simpa only [map_add, map_smul] using hx
    rw [neg_smul]
    exact (eq_neg_of_add_eq_zero_left hh).symm
  exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨hz, hx⟩⟩

/-- A precise reduction of the nowhere-zero-section lemma to the two algebraic
curve facts: a section nonzero at a point has finitely many zeroes, and a pair
independent at a point has a finite dependence locus. No section-existence
conclusion is assumed by either finiteness hypothesis. -/
theorem exists_nowherezero_of_finite_zero_and_dependence_loci
    [∀ x, FiniteDimensional K (F x)]
    (e : ∀ x, V →ₗ[K] F x) (he : ∀ x, Function.Surjective (e x))
    (p : X) (hrank : ∀ x, 2 ≤ finrank K (F x))
    (hzero : ∀ s : V, e p s ≠ 0 → {x | e x s = 0}.Finite)
    (hdep : ∀ s t : V, e p t ≠ 0 → e p s ∉ span K {e p t} →
      {x | e x s ∈ span K {e x t}}.Finite) :
    ∃ s : V, ∀ x, e x s ≠ 0 := by
  classical
  have hrp := hrank p
  let : Nontrivial (F p) := Module.nontrivial_of_finrank_pos (by omega : 0 < finrank K (F p))
  obtain ⟨v, hv⟩ := exists_ne (0 : F p)
  obtain ⟨s, hs⟩ := he p v
  have hs0 : e p s ≠ 0 := hs ▸ hv
  let Z : Set X := {x | e x s = 0} ∪ {p}
  have hZ : Z.Finite := (hzero s hs0).union (Set.finite_singleton p)
  let W (x : X) : Submodule K (F x) :=
    if x = p then span K {e x s} else ⊥
  have hW : ∀ x ∈ Z, W x ≠ ⊤ := by
    intro x hxZ
    by_cases hxp : x = p
    · subst x
      simp only [W, ite_true]
      intro hh
      have hr : finrank K (span K {e p s}) = 1 := finrank_span_singleton hs0
      rw [hh, finrank_top] at hr
      omega
    · simp only [W, hxp, ite_false]
      intro hh
      have hrx := hrank x
      let : Nontrivial (F x) :=
        Module.nontrivial_of_finrank_pos (by omega : 0 < finrank K (F x))
      obtain ⟨w, hw⟩ := exists_ne (0 : F x)
      have : w ∈ (⊥ : Submodule K (F x)) := hh ▸ Submodule.mem_top
      exact hw this
  obtain ⟨t, ht⟩ := exists_section_avoiding_finite_fiber_subspaces e he Z hZ W hW
  have hts : e p t ∉ span K {e p s} := by
    simpa only [W, ite_true] using ht p (Or.inr rfl)
  have hst : e p s ∉ span K {e p t} := by
    intro hst
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hst
    have ha0 : a ≠ 0 := by intro h; simp [h] at ha; exact hs0 ha.symm
    apply hts
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a⁻¹, ?_⟩
    rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
  have ht0 : e p t ≠ 0 := by
    intro ht0
    apply hts
    rw [ht0]
    exact (span K {e p s}).zero_mem
  have hcommon (x : X) : e x s ≠ 0 ∨ e x t ≠ 0 := by
    by_cases hx : e x s = 0
    · right
      have htx := ht x (Or.inl hx)
      intro h
      apply htx
      rw [h]
      exact (W x).zero_mem
    · exact Or.inl hx
  obtain ⟨a, ha⟩ := exists_nowherezero_combination e s t hcommon (hdep s t ht0 hst)
  exact ⟨s + a • t, ha⟩

end
end SteinerGeometry
