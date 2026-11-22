import Mathlib
import GroundTheory.PAdicHodge.PerfectoidField
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.Bundle0001

-- bundled from GroundTheory.PAdicHodge.PerfectoidCriterion
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace IsPerfectoidField

section Norm

variable {F : Type*} [NormedField F] [IsUltrametricDist F] (p : ℕ)

theorem surjective_pow_of_norm
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖) :
    Function.Surjective (fun x : ModP (normInteger F) p => x ^ p) := by
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨y, hy1, hy⟩ := h x (mem_normInteger.1 x.2)
  refine ⟨Ideal.Quotient.mk _ ⟨y, mem_normInteger.2 hy1⟩, ?_⟩
  simp only [← map_pow]
  rw [Ideal.Quotient.eq]
  have hmem := (mem_span_singleton_pow_iff (K := F) (a := (p : normInteger F))
    (x := (⟨y, mem_normInteger.2 hy1⟩ : normInteger F) ^ p - x) 1).2
  have hle : ‖(((⟨y, mem_normInteger.2 hy1⟩ : normInteger F) ^ p - x : normInteger F) : F)‖ ≤
      ‖((p : normInteger F) : F)‖ ^ 1 := by
    rw [pow_one, AddSubgroupClass.coe_sub, SubmonoidClass.coe_pow, norm_sub_rev]
    simpa using hy
  have := hmem hle
  rwa [pow_one] at this

end Norm

section Perfectoid

private theorem norm_sub_le_max_of_ultrametric_field {E : Type*} [SeminormedAddCommGroup E] [IsUltrametricDist E]
    (a b : E) : ‖a - b‖ ≤ max ‖a‖ ‖b‖ := by
  simpa [sub_eq_add_neg] using IsUltrametricDist.norm_add_le_max a (-b)

variable {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F] (p : ℕ) [Fact p.Prime]

theorem exists_norm_sub_pow_le [IsPerfectoidField F p] {x : F} (hx : ‖x‖ ≤ 1) :
    ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖ := by
  obtain ⟨z, hz⟩ := IsPerfectoidField.surjective_pow (K := F) (p := p)
    (Ideal.Quotient.mk _ ⟨x, mem_normInteger.2 hx⟩)
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨y, mem_normInteger.1 y.2, ?_⟩
  have hz' : Ideal.Quotient.mk (Ideal.span {(p : normInteger F)}) (⟨x, mem_normInteger.2 hx⟩ - y ^ p)
      = 0 := by
    rw [map_sub, map_pow]
    exact sub_eq_zero.2 hz.symm
  rw [Ideal.Quotient.eq_zero_iff_mem] at hz'
  have hmem := (mem_span_singleton_pow_iff (K := F) (a := (p : normInteger F))
    (x := ⟨x, mem_normInteger.2 hx⟩ - y ^ p) 1).1 (by rwa [pow_one])
  simpa using hmem

theorem exists_norm_sub_pow_step {π : F} (hπ : ‖π‖ ≤ 1)
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖π‖ ^ p)
    {x z : F} (hz : ‖z‖ ≤ 1) {k : ℕ} (hxz : ‖x - z ^ p‖ ≤ ‖π‖ ^ (p * k)) :
    ∃ z' : F, ‖z'‖ ≤ 1 ∧ ‖z' - z‖ ≤ ‖π‖ ^ k ∧
      ‖x - z' ^ p‖ ≤ max (‖π‖ ^ (p * (k + 1))) (‖(p : F)‖ * ‖π‖ ^ k) := by
  have hp : p.Prime := Fact.out
  by_cases h0 : π ^ (p * k) = 0
  · refine ⟨z, hz, by simp [pow_nonneg (norm_nonneg π)], ?_⟩
    have : ‖x - z ^ p‖ ≤ 0 := by rwa [← norm_pow, h0, norm_zero] at hxz
    exact this.trans (le_max_of_le_left (pow_nonneg (norm_nonneg _) _))
  set w := (x - z ^ p) / π ^ (p * k) with hw
  have hw1 : ‖w‖ ≤ 1 := by
    rw [hw, norm_div, norm_pow]
    exact div_le_one_of_le₀ hxz (pow_nonneg (norm_nonneg _) _)
  obtain ⟨u, hu1, hu⟩ := h w hw1
  have hπk : ‖π ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hπ
  have hb1 : ‖π ^ k * u‖ ≤ 1 := by
    rw [norm_mul]; exact mul_le_one₀ hπk (norm_nonneg _) hu1
  refine ⟨z + π ^ k * u, ?_, ?_, ?_⟩
  · exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hz hb1)
  · rw [add_sub_cancel_left, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (pow_nonneg (norm_nonneg _) _) hu1
  · obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (⟨z, mem_normInteger.2 hz⟩ : normInteger F)
      ⟨π ^ k * u, mem_normInteger.2 hb1⟩
    have hr' := congrArg (fun t : normInteger F => (t : F)) hr
    simp only [Subring.coe_add, SubmonoidClass.coe_pow, Subring.coe_mul,
      SubringClass.coe_natCast] at hr'
    have hr1 : ‖(r : F)‖ ≤ 1 := mem_normInteger.1 r.2
    have hxw : x - z ^ p = π ^ (p * k) * w := by
      rw [hw, mul_div_cancel₀ _ h0]
    have key : x - (z + π ^ k * u) ^ p =
        π ^ (p * k) * (w - u ^ p) - (p : F) * z * (π ^ k * u) * r := by
      rw [hr']
      have : (π ^ k * u) ^ p = π ^ (p * k) * u ^ p := by
        rw [mul_pow, ← pow_mul, mul_comm k p]
      rw [this]
      linear_combination hxw
    rw [key]
    refine (norm_sub_le_max_of_ultrametric_field _ _).trans (max_le_max ?_ ?_)
    · rw [norm_mul, norm_pow, mul_add, mul_one, pow_add]
      exact mul_le_mul_of_nonneg_left hu (pow_nonneg (norm_nonneg _) _)
    · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow]
      have h1 : ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖ ≤ ‖π‖ ^ k := by
        calc ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖ ≤ 1 * (‖π‖ ^ k * 1) * 1 := by
              gcongr
          _ = ‖π‖ ^ k := by ring
      calc ‖(p : F)‖ * ‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖
          = ‖(p : F)‖ * (‖z‖ * (‖π‖ ^ k * ‖u‖) * ‖(r : F)‖) := by ring
        _ ≤ ‖(p : F)‖ * ‖π‖ ^ k := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

theorem of_norm_sub_pow_le {F : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
    [CompleteSpace F] (p : ℕ) [Fact p.Prime] (hp : ‖(p : F)‖ < 1)
    (hnd : ∀ r : ℝ, r < 1 → ∃ x : F, r < ‖x‖ ∧ ‖x‖ < 1) {π : F} (hπ : ‖π‖ < 1)
    (h : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖π‖ ^ p) : IsPerfectoidField F p := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  set c := ‖π‖ with hc
  have hc0 : 0 ≤ c := norm_nonneg _

  have key : ∀ x : F, ‖x‖ ≤ 1 → ∃ y : F, ‖y‖ ≤ 1 ∧ ‖x - y ^ p‖ ≤ ‖(p : F)‖ := by
    intro x hx
    by_cases hpz : (p : F) = 0
    ·
      have hstep : ∀ (k : ℕ) (z : F), ‖z‖ ≤ 1 → ‖x - z ^ p‖ ≤ c ^ (p * k) →
          ∃ z' : F, ‖z'‖ ≤ 1 ∧ ‖z' - z‖ ≤ c ^ k ∧ ‖x - z' ^ p‖ ≤ c ^ (p * (k + 1)) := by
        intro k z hz hxz
        obtain ⟨z', h1, h2, h3⟩ := exists_norm_sub_pow_step p hπ.le h hz hxz
        refine ⟨z', h1, h2, h3.trans (max_le le_rfl ?_)⟩
        rw [hpz, norm_zero, zero_mul]
        exact pow_nonneg hc0 _
      let S : ℕ → Type _ := fun k => {z : F // ‖z‖ ≤ 1 ∧ ‖x - z ^ p‖ ≤ c ^ (p * k)}
      let next : (k : ℕ) → S k → S (k + 1) := fun k z =>
        ⟨Classical.choose (hstep k z.1 z.2.1 z.2.2),
          (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).1,
          (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).2.2⟩
      have hnext : ∀ (k : ℕ) (z : S k), ‖(next k z).1 - z.1‖ ≤ c ^ k := fun k z =>
        (Classical.choose_spec (hstep k z.1 z.2.1 z.2.2)).2.1
      have base : ‖x - (0 : F) ^ p‖ ≤ c ^ (p * 0) := by
        rw [mul_zero, pow_zero, zero_pow hp0, sub_zero]; exact hx
      let s : (k : ℕ) → S k := fun k => Nat.rec ⟨0, by simp, base⟩ next k
      let z : ℕ → F := fun k => (s k).1
      have hdist : ∀ k, dist (z k) (z (k + 1)) ≤ 1 * c ^ k := by
        intro k
        rw [one_mul, dist_comm, dist_eq_norm]
        exact hnext k (s k)
      have hcau : CauchySeq z := cauchySeq_of_le_geometric c 1 hπ hdist
      obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
      have hL1 : ‖L‖ ≤ 1 := le_of_tendsto' hL.norm fun k => (s k).2.1
      refine ⟨L, hL1, ?_⟩
      have ht0 : Filter.Tendsto (fun k => c ^ (p * k)) Filter.atTop (nhds 0) := by
        simp_rw [pow_mul]
        exact tendsto_pow_atTop_nhds_zero_of_lt_one (pow_nonneg hc0 _)
          (pow_lt_one₀ hc0 hπ hp0)
      have h1 : Filter.Tendsto (fun k => ‖x - z k ^ p‖) Filter.atTop (nhds 0) :=
        squeeze_zero (fun _ => norm_nonneg _) (fun k => (s k).2.2) ht0
      have h2 : Filter.Tendsto (fun k => ‖x - z k ^ p‖) Filter.atTop (nhds ‖x - L ^ p‖) :=
        (tendsto_const_nhds.sub (hL.pow p)).norm
      rw [tendsto_nhds_unique h2 h1]
      exact norm_nonneg _
    ·
      have hpos : 0 < ‖(p : F)‖ := norm_pos_iff.2 hpz
      have hind : ∀ k : ℕ, ∃ z : F, ‖z‖ ≤ 1 ∧
          (‖x - z ^ p‖ ≤ ‖(p : F)‖ ∨ ‖x - z ^ p‖ ≤ c ^ (p * k)) := by
        intro k
        induction k with
        | zero =>
          refine ⟨0, by simp, Or.inr ?_⟩
          rw [mul_zero, pow_zero, zero_pow hp0, sub_zero]; exact hx
        | succ k ih =>
          obtain ⟨z, hz, hz'⟩ := ih
          rcases hz' with hz' | hz'
          · exact ⟨z, hz, Or.inl hz'⟩
          · obtain ⟨z', h1, -, h3⟩ := exists_norm_sub_pow_step p hπ.le h hz hz'
            refine ⟨z', h1, ?_⟩
            rcases le_total (c ^ (p * (k + 1))) (‖(p : F)‖ * c ^ k) with hle | hle
            · left
              refine h3.trans ((max_eq_right hle).le.trans ?_)
              exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ hc0 hπ.le)
            · right
              exact h3.trans (max_eq_left hle).le
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hπ
      obtain ⟨z, hz, hz'⟩ := hind n
      refine ⟨z, hz, hz'.elim id fun h' => h'.trans ?_⟩
      refine le_trans ?_ hn.le
      exact pow_le_pow_of_le_one hc0 hπ.le (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hp0))
  exact
    { complete := inferInstance
      norm_natCast_lt_one := hp
      exists_norm_mem_Ioo := hnd
      surjective_pow := surjective_pow_of_norm p key }

theorem of_ringEquiv {F F' : Type*} [NontriviallyNormedField F] [IsUltrametricDist F]
    [NontriviallyNormedField F'] [IsUltrametricDist F'] (p : ℕ) [Fact p.Prime]
    [IsPerfectoidField F p] (e : F ≃+* F') (he : ∀ x, ‖e x‖ = ‖x‖) : IsPerfectoidField F' p := by
  have := completeSpace (K := F) p
  have hiso : Isometry e := Isometry.of_dist_eq fun x y => by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub, he]
  let ie : F ≃ᵢ F' := { e.toEquiv with isometry_toFun := hiso }
  have he' : ∀ y, ‖e.symm y‖ = ‖y‖ := fun y => by
    conv_rhs => rw [← e.apply_symm_apply y]
    rw [he]
  have hpF : ‖(p : F')‖ = ‖(p : F)‖ := by rw [← map_natCast e p, he]
  exact
    { complete := ie.symm.completeSpace
      norm_natCast_lt_one := hpF ▸ norm_natCast_lt_one (K := F) (p := p)
      exists_norm_mem_Ioo := fun r hr => by
        obtain ⟨x, h1, h2⟩ := exists_norm_mem_Ioo (K := F) (p := p) r hr
        exact ⟨e x, by rwa [he], by rwa [he]⟩
      surjective_pow := surjective_pow_of_norm p fun y hy => by
        obtain ⟨x, hx1, hx⟩ := exists_norm_sub_pow_le p (x := e.symm y) (by rwa [he'])
        refine ⟨e x, by rwa [he], ?_⟩
        have hyx : y - e x ^ p = e (e.symm y - x ^ p) := by
          rw [map_sub, map_pow, e.apply_symm_apply]
        rw [hpF, hyx, he]
        exact hx }

end Perfectoid

end IsPerfectoidField

end GroundTheory.PAdicHodge
end
end

-- bundled from GroundTheory.PAdicHodge.SlopeCauchyBinet
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

open Matrix Finset Equiv

abbrev KSubset (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

def KSubset.emb {n k : ℕ} (s : KSubset n k) : Fin k ↪o Fin n := s.1.orderEmbOfFin s.2

theorem KSubset.range_emb {n k : ℕ} (s : KSubset n k) : Set.range s.emb = (s.1 : Set (Fin n)) :=
  Finset.range_orderEmbOfFin _ _

variable {R : Type*} [CommRing R]

section CauchyBinet

variable {k n : ℕ}

private theorem det_mul_eq_sum_fun (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det = ∑ p : Fin k → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
  simp only [det_apply', mul_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ,
    submatrix_apply, id, sum_mul, prod_mul_distrib, mul_assoc]
  rw [Finset.sum_comm]

theorem det_mul_eq_sum_minors (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    (A * B).det =
      ∑ s : KSubset n k, (A.submatrix id s.emb).det * (B.submatrix s.emb id).det := by
  classical
  set F : (Fin k → Fin n) → R := fun p => (A.submatrix id p).det * ∏ i, B (p i) i with hF
  have hzero : ∀ p, ¬ Function.Injective p → F p = 0 := by
    intro p hp
    obtain ⟨i, j, hij, hne⟩ : ∃ i j, p i = p j ∧ i ≠ j := by
      simp only [Function.Injective, not_forall] at hp
      obtain ⟨i, j, h, hne⟩ := hp
      exact ⟨i, j, h, hne⟩
    simp only [hF]
    rw [det_zero_of_column_eq hne (fun r => by simp [hij]), zero_mul]
  have hterm : ∀ (s : KSubset n k) (σ : Perm (Fin k)),
      F (s.emb ∘ σ) = (A.submatrix id s.emb).det * (Perm.sign σ * ∏ i, B (s.emb (σ i)) i) := by
    intro s σ
    simp only [hF]
    have : A.submatrix id (s.emb ∘ σ) = (A.submatrix id s.emb).submatrix id σ := rfl
    rw [this, det_permute']
    simp only [Function.comp_apply]
    ring
  have hs : ∀ s : KSubset n k, (A.submatrix id s.emb).det * (B.submatrix s.emb id).det =
      ∑ σ : Perm (Fin k), F (s.emb ∘ σ) := by
    intro s
    simp only [hterm, ← mul_sum]
    congr 1
    rw [det_apply']
    rfl
  have hprod := Fintype.sum_prod_type (fun x : KSubset n k × Perm (Fin k) => F (x.1.emb ∘ x.2))
  simp only at hprod
  rw [det_mul_eq_sum_fun, Finset.sum_congr rfl (fun s _ => hs s)]
  change ∑ p, F p = _
  rw [← hprod, ← Finset.sum_filter_of_ne (p := Function.Injective) (fun p _ h => by
      by_contra hp; exact h (hzero p hp))]
  symm
  refine Finset.sum_bij (fun x _ => x.1.emb ∘ x.2) ?_ ?_ ?_ ?_
  · intro x _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact x.1.emb.injective.comp x.2.injective
  · rintro ⟨s, σ⟩ _ ⟨t, τ⟩ _ h
    simp only at h
    have hst : s = t := by
      apply Subtype.ext
      have h1 : Set.range (s.emb ∘ σ) = Set.range (t.emb ∘ τ) := by rw [h]
      rw [Set.range_comp, Set.range_comp, σ.range_eq_univ, τ.range_eq_univ, Set.image_univ,
        Set.image_univ, KSubset.range_emb, KSubset.range_emb] at h1
      exact_mod_cast h1
    subst hst
    have : σ = τ := by
      ext i
      have := congrFun h i
      simp only [Function.comp_apply] at this
      exact congrArg Fin.val (s.emb.injective this)
    rw [this]
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    have hcard : (Finset.univ.image p).card = k := by
      rw [Finset.card_image_of_injective _ hp, Finset.card_univ, Fintype.card_fin]
    let s : KSubset n k := ⟨Finset.univ.image p, hcard⟩
    have hex : ∀ i, ∃ j, s.emb j = p i := by
      intro i
      have : p i ∈ (s.1 : Set (Fin n)) := by simp [s]
      rw [← KSubset.range_emb] at this
      exact this
    choose f hf using hex
    have hfinj : Function.Injective f := by
      intro i j hij
      apply hp
      rw [← hf i, ← hf j, hij]
    let σ : Perm (Fin k) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfinj)
    refine ⟨(s, σ), Finset.mem_univ _, ?_⟩
    funext i
    exact hf i
  · intro x _
    rfl

theorem det_mul_eq_zero_of_lt (A : Matrix (Fin k) (Fin n) R) (B : Matrix (Fin n) (Fin k) R)
    (h : n < k) : (A * B).det = 0 := by
  rw [det_mul_eq_sum_minors]
  refine Finset.sum_eq_zero fun s _ => ?_
  exfalso
  have := s.1.card_le_univ
  rw [Fintype.card_fin, s.2] at this
  omega

end CauchyBinet

section Minors

variable {m n k : ℕ}

def maxMinor (B : Matrix (Fin n) (Fin k) R) (s : KSubset n k) : R :=
  (B.submatrix s.emb id).det

def compound (k : ℕ) (P : Matrix (Fin m) (Fin n) R) : Matrix (KSubset m k) (KSubset n k) R :=
  Matrix.of fun s t => (P.submatrix s.emb t.emb).det

theorem compound_apply (k : ℕ) (P : Matrix (Fin m) (Fin n) R) (s : KSubset m k)
    (t : KSubset n k) : compound k P s t = (P.submatrix s.emb t.emb).det := rfl

theorem maxMinor_mul_right (B : Matrix (Fin n) (Fin k) R) (C : Matrix (Fin k) (Fin k) R)
    (s : KSubset n k) : maxMinor (B * C) s = maxMinor B s * C.det := by
  unfold maxMinor
  rw [← det_mul]
  congr 1

theorem maxMinor_mul_left (P : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset m k) :
    maxMinor (P * B) s = ∑ t : KSubset n k, compound k P s t * maxMinor B t := by
  unfold maxMinor
  have : (P * B).submatrix s.emb id = P.submatrix s.emb id * B := by
    ext i j; simp [mul_apply]
  rw [this, det_mul_eq_sum_minors]
  rfl

theorem maxMinor_mul_left_eq_mulVec (P : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin k) R) :
    maxMinor (P * B) = compound k P *ᵥ maxMinor B := by
  funext s
  rw [maxMinor_mul_left]
  rfl

theorem compound_mul {l : ℕ} (P : Matrix (Fin m) (Fin n) R) (Q : Matrix (Fin n) (Fin l) R) :
    compound k (P * Q) = compound k P * compound k Q := by
  ext s u
  rw [compound_apply, mul_apply]
  have : (P * Q).submatrix s.emb u.emb = P.submatrix s.emb id * Q.submatrix id u.emb := by
    ext i j; simp [mul_apply]
  rw [this, det_mul_eq_sum_minors]
  rfl

theorem maxMinor_map {S : Type*} [CommRing S] (f : R →+* S) (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) : maxMinor (B.map f) s = f (maxMinor B s) := by
  unfold maxMinor
  rw [RingHom.map_det]
  rfl

theorem compound_map {S : Type*} [CommRing S] (f : R →+* S) (P : Matrix (Fin m) (Fin n) R) :
    compound k (P.map f) = (compound k P).map f := by
  ext s t
  rw [compound_apply, map_apply, compound_apply, RingHom.map_det]
  rfl

theorem compound_mulVec_maxMinor_of_mul_eq (A : Matrix (Fin n) (Fin n) R)
    (B B' : Matrix (Fin n) (Fin k) R) (C : Matrix (Fin k) (Fin k) R) (h : A * B' = B * C) :
    compound k A *ᵥ maxMinor B' = C.det • maxMinor B := by
  rw [← maxMinor_mul_left_eq_mulVec, h]
  funext s
  rw [maxMinor_mul_right, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem compound_mulVec_map_maxMinor_of_mul_eq (φ : R →+* R) (A : Matrix (Fin n) (Fin n) R)
    (B : Matrix (Fin n) (Fin k) R) (C : Matrix (Fin k) (Fin k) R) (h : A * B.map φ = B * C) :
    compound k A *ᵥ (fun s => φ (maxMinor B s)) = C.det • maxMinor B := by
  rw [← compound_mulVec_maxMinor_of_mul_eq A B (B.map φ) C h]
  congr 1
  funext s
  rw [maxMinor_map]

end Minors

section Independence

variable {n k : ℕ}

theorem linearIndependent_col_iff_mulVec_eq_zero (B : Matrix (Fin n) (Fin k) R) :
    LinearIndependent R B.col ↔ ∀ v, B *ᵥ v = 0 → v = 0 := by
  rw [Fintype.linearIndependent_iff]
  have key : ∀ v : Fin k → R, ∑ j, v j • B.col j = B *ᵥ v := by
    intro v; ext i; simp [mulVec, dotProduct, Finset.sum_apply, col, mul_comm]
  constructor
  · intro h v hv
    funext j
    exact h v (by rw [key, hv]) j
  · intro h g hg j
    have := h g (by rw [← key, hg])
    exact congrFun this j

theorem linearIndependent_col_of_maxMinor_ne_zero [IsDomain R] (B : Matrix (Fin n) (Fin k) R)
    (s : KSubset n k) (hs : maxMinor B s ≠ 0) : LinearIndependent R B.col := by
  rw [linearIndependent_col_iff_mulVec_eq_zero]
  intro v hv
  apply eq_zero_of_mulVec_eq_zero hs
  have : B.submatrix s.emb id *ᵥ v = fun i => (B *ᵥ v) (s.emb i) := by
    ext i; simp [mulVec, dotProduct]
  rw [this, hv]
  rfl

theorem exists_maxMinor_ne_zero_of_linearIndependent [IsDomain R]
    (B : Matrix (Fin n) (Fin k) R) (hB : LinearIndependent R B.col) :
    ∃ s : KSubset n k, maxMinor B s ≠ 0 :=
  _root_.GroundTheory.Variant₂.N1.exists_maxMinor_ne_zero_of_linearIndependent_alt B hB

theorem exists_maxMinor_ne_zero_iff_linearIndependent [IsDomain R]
    (B : Matrix (Fin n) (Fin k) R) :
    (∃ s : KSubset n k, maxMinor B s ≠ 0) ↔ LinearIndependent R B.col :=
  ⟨fun ⟨s, hs⟩ => linearIndependent_col_of_maxMinor_ne_zero B s hs,
    exists_maxMinor_ne_zero_of_linearIndependent B⟩

theorem maxMinor_ne_zero_iff_linearIndependent [IsDomain R] (B : Matrix (Fin n) (Fin k) R) :
    maxMinor B ≠ 0 ↔ LinearIndependent R B.col := by
  rw [← exists_maxMinor_ne_zero_iff_linearIndependent, Ne, funext_iff, not_forall]
  rfl

end Independence

end GroundTheory.PAdicHodge
end

