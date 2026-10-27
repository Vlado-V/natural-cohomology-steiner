module

public import SteinerGeometry.CurveGeneratorLinear
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

set_option backward.privateInPublic true
@[expose] public section

namespace SteinerGeometry

noncomputable section

open Module Submodule

variable {K : Type*} [Field K] [Infinite K]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {X : Type*} {F : X → Type*}
variable [∀ x, AddCommGroup (F x)] [∀ x, Module K (F x)]
variable [∀ x, FiniteDimensional K (F x)]

/-- The curve rank-locus property for a space of sections: a tuple independent
at one point is dependent at only finitely many points. -/
def HasFiniteRankDrop (e : ∀ x, V →ₗ[K] F x) : Prop :=
  ∀ (k : ℕ) (s : Fin k → V),
    (∃ p : X, LinearIndependent K (fun i => e p (s i))) →
    {x | ¬ LinearIndependent K (fun i => e x (s i))}.Finite

omit [Infinite K] in
theorem quotient_mem_span_singleton_iff
    {E : Type*} [AddCommGroup E] [Module K E]
    (W : Submodule K E) (a b : E) :
    W.mkQ a ∈ span K {W.mkQ b} ↔ a ∈ W ⊔ span K {b} := by
  have he : span K {W.mkQ b} = (span K {b}).map W.mkQ := by
    rw [Submodule.map_span, Set.image_singleton]
  rw [he]
  change a ∈ ((span K {b}).map W.mkQ).comap W.mkQ ↔ _
  rw [Submodule.comap_map_mkQ]

omit [Infinite K] [∀ x, FiniteDimensional K (F x)] in
theorem span_evaluated_cons (e : ∀ x, V →ₗ[K] F x)
    {k : ℕ} (s : V) (v : Fin k → V) (x : X) :
    span K (Set.range (fun i => e x ((Fin.cons s v : Fin (k + 1) → V) i))) =
      span K {e x s} ⊔ span K (Set.range (fun i => e x (v i))) := by
  change span K (Set.range (e x ∘ Fin.cons s v)) = _
  rw [Fin.comp_cons, Fin.range_cons, Submodule.span_insert]
  rfl

omit [Infinite K] [∀ x, FiniteDimensional K (F x)] in
/-- Quotienting by an everywhere independent section tuple preserves the finite
zero/dependence conditions needed by the elementary nowhere-zero construction. -/
theorem quotient_finite_zero_and_dependence_loci
    (e : ∀ x, V →ₗ[K] F x) (hrank : HasFiniteRankDrop e)
    {k : ℕ} (v : Fin k → V)
    (hv : ∀ x, LinearIndependent K (fun i => e x (v i))) (p : X) :
    let W := fun x => span K (Set.range (fun i => e x (v i)))
    let q := fun x => (W x).mkQ.comp (e x)
    (∀ s : V, q p s ≠ 0 → {x | q x s = 0}.Finite) ∧
    (∀ s t : V, q p t ≠ 0 → q p s ∉ span K {q p t} →
      {x | q x s ∈ span K {q x t}}.Finite) := by
  dsimp only
  let W := fun x => span K (Set.range (fun i => e x (v i)))
  let q := fun x => (W x).mkQ.comp (e x)
  have hq (x : X) (s : V) : q x s = 0 ↔ e x s ∈ W x :=
    Submodule.Quotient.mk_eq_zero _
  constructor
  · intro s hs
    have hs' : LinearIndependent K (fun i => e p ((Fin.cons s v : Fin (k + 1) → V) i)) := by
      change LinearIndependent K (e p ∘ Fin.cons s v)
      rw [Fin.comp_cons, linearIndependent_finCons]
      exact ⟨hv p, fun h => hs ((hq p s).mpr h)⟩
    apply (hrank (k + 1) (Fin.cons s v) ⟨p, hs'⟩).subset
    intro x hx hli
    change LinearIndependent K (e x ∘ Fin.cons s v) at hli
    rw [Fin.comp_cons, linearIndependent_finCons] at hli
    exact hli.2 ((hq x s).mp hx)
  · intro s t ht hs
    have ht' : LinearIndependent K (fun i => e p ((Fin.cons t v : Fin (k + 1) → V) i)) := by
      change LinearIndependent K (e p ∘ Fin.cons t v)
      rw [Fin.comp_cons, linearIndependent_finCons]
      exact ⟨hv p, fun h => ht ((hq p t).mpr h)⟩
    have hs' : LinearIndependent K (fun i => e p ((Fin.cons s (Fin.cons t v) : Fin (k + 2) → V) i)) := by
      change LinearIndependent K (e p ∘ Fin.cons s (Fin.cons t v))
      rw [Fin.comp_cons, linearIndependent_finCons]
      refine ⟨ht', fun h => hs ?_⟩
      change (W p).mkQ (e p s) ∈ span K {(W p).mkQ (e p t)}
      rw [quotient_mem_span_singleton_iff]
      change e p s ∈ span K (Set.range (fun i => e p ((Fin.cons t v : Fin (k + 1) → V) i))) at h
      rw [span_evaluated_cons] at h
      simpa only [W, sup_comm] using h
    apply (hrank (k + 2) (Fin.cons s (Fin.cons t v)) ⟨p, hs'⟩).subset
    intro x hx hli
    change LinearIndependent K (e x ∘ Fin.cons s (Fin.cons t v)) at hli
    rw [Fin.comp_cons, linearIndependent_finCons] at hli
    apply hli.2
    change e x s ∈ span K (Set.range (fun i => e x ((Fin.cons t v : Fin (k + 1) → V) i)))
    rw [span_evaluated_cons]
    change (W x).mkQ (e x s) ∈ span K {(W x).mkQ (e x t)} at hx
    rw [quotient_mem_span_singleton_iff] at hx
    simpa only [W, sup_comm] using hx

/-- Below the bundle rank, all but the final frame vector can be chosen to be
pointwise independent using only finite rank-drop on the curve. -/
theorem exists_everywhere_independent_sections
    (e : ∀ x, V →ₗ[K] F x) (he : ∀ x, Function.Surjective (e x))
    {n : ℕ} (hdim : ∀ x, finrank K (F x) = n)
    (hrank : HasFiniteRankDrop e) (p : X) :
    ∀ k : ℕ, k < n →
      ∃ v : Fin k → V, ∀ x, LinearIndependent K (fun i => e x (v i)) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨fun i => Fin.elim0 i, fun _ => linearIndependent_empty_type⟩
  | succ k ih =>
    intro hk
    obtain ⟨v, hv⟩ := ih (by omega)
    let W := fun x => span K (Set.range (fun i => e x (v i)))
    let q := fun x => (W x).mkQ.comp (e x)
    have hW (x : X) : finrank K (W x) = k := by
      simpa only [W, Fintype.card_fin] using finrank_span_eq_card (hv x)
    have hqrank (x : X) : 2 ≤ finrank K (F x ⧸ W x) := by
      have h := (W x).finrank_quotient_add_finrank
      rw [hW x, hdim x] at h
      omega
    have hqsurj (x : X) : Function.Surjective (q x) :=
      (W x).mkQ_surjective.comp (he x)
    obtain ⟨hzero, hdep⟩ := quotient_finite_zero_and_dependence_loci e hrank v hv p
    obtain ⟨s, hs⟩ := exists_nowherezero_of_finite_zero_and_dependence_loci
      q hqsurj p hqrank hzero hdep
    refine ⟨Fin.cons s v, fun x => ?_⟩
    change LinearIndependent K (e x ∘ Fin.cons s v)
    rw [Fin.comp_cons, linearIndependent_finCons]
    refine ⟨hv x, fun hx => hs x ?_⟩
    exact (Submodule.Quotient.mk_eq_zero _).mpr hx

/-- The full rank-plus-one generator theorem for a curve evaluation family.
The single geometric hypothesis is finite rank-drop of nonzero minors; no
uniformly generating tuple or generic-parameter assertion is assumed. -/
theorem exists_rank_add_one_generators
    (e : ∀ x, V →ₗ[K] F x) (he : ∀ x, Function.Surjective (e x))
    (n : ℕ) (hdim : ∀ x, finrank K (F x) = n + 1)
    (hrank : HasFiniteRankDrop e) (p : X) :
    ∃ s : Fin (n + 2) → V,
      ∀ x, span K (Set.range (fun i => e x (s i))) = ⊤ := by
  classical
  obtain ⟨v, hv⟩ := exists_everywhere_independent_sections e he hdim hrank p n (by omega)
  let W := fun x => span K (Set.range (fun i => e x (v i)))
  let q := fun x => (W x).mkQ.comp (e x)
  have hW (x : X) : finrank K (W x) = n := by
    simpa only [W, Fintype.card_fin] using finrank_span_eq_card (hv x)
  have hqrank (x : X) : finrank K (F x ⧸ W x) = 1 := by
    have h := (W x).finrank_quotient_add_finrank
    rw [hW x, hdim x] at h
    omega
  let : Nontrivial (F p ⧸ W p) := Module.nontrivial_of_finrank_pos (by rw [hqrank]; omega)
  obtain ⟨w, hw⟩ := exists_ne (0 : F p ⧸ W p)
  obtain ⟨s, hs⟩ := ((W p).mkQ_surjective.comp (he p)) w
  have hs0 : q p s ≠ 0 := by
    change (W p).mkQ (e p s) ≠ 0
    exact fun h => hw (hs.symm.trans h)
  have hzero := (quotient_finite_zero_and_dependence_loci e hrank v hv p).1 s hs0
  let T := fun x => span K (Set.range (fun i => e x ((Fin.cons s v : Fin (n + 1) → V) i)))
  have hWT (x : X) : W x ≤ T x := by
    rw [show T x = span K {e x s} ⊔ W x from span_evaluated_cons e s v x]
    exact le_sup_right
  have hT (x : X) : finrank K (F x) ≤ finrank K (T x) + 1 := by
    have hh := Submodule.finrank_mono (hWT x)
    rw [hW x, hdim x] at *
    omega
  have hTfinite : {x | T x ≠ ⊤}.Finite := by
    apply hzero.subset
    intro x hx
    by_contra h
    apply hx
    have hsW : e x s ∉ W x := by
      intro hsW
      exact h ((Submodule.Quotient.mk_eq_zero _).mpr hsW)
    have hh := sup_span_singleton_eq_top_of_finrank_bound (W x)
      (by rw [hdim x, hW x]) hsW
    dsimp only [T]
    rw [span_evaluated_cons]
    exact (sup_comm _ _).trans hh
  obtain ⟨t, ht⟩ := exists_section_completing_finite_defect e he T hTfinite hT
  refine ⟨Fin.cons t (Fin.cons s v), fun x => ?_⟩
  rw [span_evaluated_cons]
  exact (sup_comm _ _).trans (ht x)

/-- Positive-rank form, indexed exactly as the rank-`n` bundle statement. -/
theorem exists_rank_succ_generators
    (e : ∀ x, V →ₗ[K] F x) (he : ∀ x, Function.Surjective (e x))
    (n : ℕ) (hn : 0 < n) (hdim : ∀ x, finrank K (F x) = n)
    (hrank : HasFiniteRankDrop e) (p : X) :
    ∃ s : Fin (n + 1) → V,
      ∀ x, span K (Set.range (fun i => e x (s i))) = ⊤ := by
  cases n with
  | zero => omega
  | succ n => exact exists_rank_add_one_generators e he n hdim hrank p

end
end SteinerGeometry
