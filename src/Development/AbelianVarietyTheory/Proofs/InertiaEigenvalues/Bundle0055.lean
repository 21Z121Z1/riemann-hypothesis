import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0014
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.TendstoPrimeIdealZetaSumUniv
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0016
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0018
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0019
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0020
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0021
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLinearMapOfTraceEq
section
namespace GlobalTheory.TraceConj

open IsLocalRing

theorem ker_le_ker_of_trace_eq {Γ R : Type} [Monoid Γ] [CommRing R] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) R) (h : ∀ g, (M g).trace = (N g).trace)
    (hN : Submodule.span R (Set.range N) = ⊤) :
    LinearMap.ker (Finsupp.linearCombination R (fun g => M g)) ≤
      LinearMap.ker (Finsupp.linearCombination R (fun g => N g)) := by
  classical
  set a := Finsupp.linearCombination R (fun g => M g) with ha
  set b := Finsupp.linearCombination R (fun g => N g) with hb
  have hab : ∀ c g, (a c * M g).trace = (b c * N g).trace := by
    intro c g
    induction c using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, map_add, add_mul, add_mul, Matrix.trace_add, Matrix.trace_add, hx, hy]
    | single x c =>
      simp only [ha, hb, Finsupp.linearCombination_single, Matrix.smul_mul, Matrix.trace_smul, ← map_mul, h]
  intro c hc
  rw [LinearMap.mem_ker] at hc ⊢
  have h1 : ∀ Y ∈ Submodule.span R (Set.range N), (b c * Y).trace = 0 := by
    intro Y hY
    induction hY using Submodule.span_induction with
    | mem Y hY => obtain ⟨g, rfl⟩ := hY; rw [← hab, hc]; simp
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, Matrix.trace_add, hx, hy, add_zero]
    | smul t x _ hx => rw [Matrix.mul_smul, Matrix.trace_smul, hx, smul_zero]
  ext p q
  have := h1 (Matrix.single q p 1) (hN ▸ Submodule.mem_top)
  rw [Matrix.trace_mul_single] at this
  simpa using this

theorem span_top_of_trace_eq {Γ K : Type} [Monoid Γ] [Field K] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) K) (h : ∀ g, (M g).trace = (N g).trace)
    (hN : Submodule.span K (Set.range N) = ⊤) : Submodule.span K (Set.range M) = ⊤ := by
  classical
  let a := Finsupp.linearCombination K (fun g => M g)
  let b := Finsupp.linearCombination K (fun g => N g)
  have hker : LinearMap.ker a ≤ LinearMap.ker b := ker_le_ker_of_trace_eq M N h hN
  have hb : LinearMap.range b = ⊤ := by rw [Finsupp.range_linearCombination]; exact hN
  let f : LinearMap.range a →ₗ[K] Matrix (Fin n) (Fin n) K :=
    ((LinearMap.ker a).liftQ b hker).comp a.quotKerEquivRange.symm.toLinearMap
  have hf : Function.Surjective f := by
    intro Y
    obtain ⟨c, rfl⟩ := LinearMap.range_eq_top.1 hb Y
    refine ⟨a.quotKerEquivRange (Submodule.Quotient.mk c), ?_⟩
    simp [f]
  have hle := LinearMap.finrank_le_finrank_of_surjective hf
  have := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le _) hle)
  rwa [Finsupp.range_linearCombination] at this

theorem span_top_of_residual {Γ O : Type} [CommRing O] [IsLocalRing O] {n : ℕ}
    (M : Γ → Matrix (Fin n) (Fin n) O)
    (h : Submodule.span (ResidueField O) (Set.range fun g => (M g).map (residue O)) = ⊤) :
    Submodule.span O (Set.range M) = ⊤ := by
  classical
  have lift : ∀ Z ∈ Submodule.span (ResidueField O) (Set.range fun g => (M g).map (residue O)),
      ∃ Y ∈ Submodule.span O (Set.range M), Y.map (residue O) = Z := by
    intro Z hZ
    induction hZ using Submodule.span_induction with
    | mem Z hZ => obtain ⟨g, rfl⟩ := hZ; exact ⟨M g, Submodule.subset_span ⟨g, rfl⟩, rfl⟩
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨y, hy, rfl⟩ := hy
      exact ⟨x + y, Submodule.add_mem _ hx hy, by ext; simp⟩
    | smul t x _ hx =>
      obtain ⟨x, hx, rfl⟩ := hx
      obtain ⟨t, rfl⟩ := residue_surjective t
      exact ⟨t • x, Submodule.smul_mem _ _ hx, by ext; simp⟩
  rw [eq_top_iff]
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal O) Module.Finite.fg_top
    (maximalIdeal_le_jacobson _) fun X _ => ?_
  obtain ⟨Y, hY, hYX⟩ := lift (X.map (residue O)) (h ▸ Submodule.mem_top)
  rw [← add_sub_cancel Y X]
  refine Submodule.add_mem_sup hY ?_
  rw [Matrix.matrix_eq_sum_single (X - Y)]
  refine Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ => ?_
  have e : Matrix.single i j ((X - Y) i j) = (X - Y) i j • Matrix.single i j (1 : O) := by
    rw [Matrix.smul_single, smul_eq_mul, mul_one]
  rw [e]
  refine Submodule.smul_mem_smul ?_ Submodule.mem_top
  rw [← residue_eq_zero_iff, Matrix.sub_apply, map_sub, sub_eq_zero]
  exact (congrFun (congrFun hYX i) j).symm

theorem exists_linearMap_of_trace_eq {Γ R : Type} [Monoid Γ] [CommRing R] {n : ℕ}
    (M N : Γ →* Matrix (Fin n) (Fin n) R) (h : ∀ g, (M g).trace = (N g).trace)
    (hM : Submodule.span R (Set.range M) = ⊤) (hN : Submodule.span R (Set.range N) = ⊤) :
    ∃ φ : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R, φ 1 = 1 ∧ ∀ g X, φ (M g * X) = N g * φ X := by
  classical
  let a := Finsupp.linearCombination R (fun g => M g)
  let b := Finsupp.linearCombination R (fun g => N g)
  have hker : LinearMap.ker a ≤ LinearMap.ker b := ker_le_ker_of_trace_eq M N h hN
  have ha : Function.Surjective a := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]; exact hM
  let φ : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R :=
    ((LinearMap.ker a).liftQ b hker).comp (a.quotKerEquivOfSurjective ha).symm.toLinearMap
  have hφ : ∀ c, φ (a c) = b c := fun c => by
    have : a c = a.quotKerEquivOfSurjective ha (Submodule.Quotient.mk c) := rfl
    rw [this]
    simp only [φ, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  have hφg : ∀ g, φ (M g) = N g := fun g => by
    simpa [a, b] using hφ (Finsupp.single g 1)
  refine ⟨φ, by simpa using hφg 1, fun g X => ?_⟩
  have hX : X ∈ Submodule.span R (Set.range M) := hM ▸ Submodule.mem_top
  induction hX using Submodule.span_induction with
  | mem X hX => obtain ⟨g', rfl⟩ := hX; rw [← map_mul, hφg, hφg, map_mul]
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add, map_add, map_add, mul_add, hx, hy]
  | smul t x _ hx => rw [Matrix.mul_smul, map_smul, map_smul, Matrix.mul_smul, hx]

theorem exists_gl_conj_of_trace_eq :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (Γ : Type) [Group Γ] (r : ℕ) (ρ ρ' : Γ →* GL (Fin r) O), Submodule.span (IsLocalRing.ResidueField O) (Set.range fun g => ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).map (IsLocalRing.residue O)) = ⊤ → (∀ g, ((ρ' g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).trace = ((ρ g : GL (Fin r) O) : Matrix (Fin r) (Fin r) O).trace) → ∃ U : GL (Fin r) O, ∀ g, ρ' g * U = U * ρ g := by
  intro O _ _ _ _ Γ _ r ρ ρ' hspan htr
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨1, fun g => Units.ext (Subsingleton.elim _ _)⟩
  let M : Γ →* Matrix (Fin r) (Fin r) O := (Units.coeHom _).comp ρ
  let N : Γ →* Matrix (Fin r) (Fin r) O := (Units.coeHom _).comp ρ'
  let π : Matrix (Fin r) (Fin r) O →* Matrix (Fin r) (Fin r) (ResidueField O) := (residue O).mapMatrix.toMonoidHom
  have hN' : Submodule.span (ResidueField O) (Set.range (π.comp N)) = ⊤ :=
    span_top_of_trace_eq (π.comp N) (π.comp M) (fun g => by
      change ((N g).map (residue O)).trace = ((M g).map (residue O)).trace
      rw [← AddMonoidHom.map_trace, ← AddMonoidHom.map_trace]
      exact congrArg _ (htr g)) hspan
  obtain ⟨φ, h1, hφ⟩ := exists_linearMap_of_trace_eq M N (fun g => (htr g).symm)
    (span_top_of_residual _ hspan) (span_top_of_residual _ hN')
  let k : Fin r := ⟨0, hr⟩
  obtain ⟨j, hj⟩ : ∃ j, residue O (φ (Matrix.single j j 1) k k) ≠ 0 := by
    by_contra hc
    push Not at hc
    have e : (1 : Matrix (Fin r) (Fin r) O) = ∑ j, Matrix.single j j 1 := (Matrix.sum_single_one).symm
    have := congrArg (fun X : Matrix (Fin r) (Fin r) O => residue O (X k k)) h1
    rw [e, map_sum, ← e] at this
    simp [Matrix.sum_apply, hc] at this
  let A : Matrix (Fin r) (Fin r) O := Matrix.of fun p q => φ (Matrix.single q j 1) p k
  have hA : ∀ g, N g * A = A * M g := by
    intro g
    ext p q
    have e : M g * Matrix.single q j 1 = ∑ t, M g t q • Matrix.single t j (1 : O) := by
      ext a b
      by_cases hb : j = b
      · subst hb; simp [Matrix.sum_apply, Matrix.single_apply]
      · simp [Matrix.sum_apply, Matrix.single_apply, Matrix.mul_apply, hb]
    have := congrFun (congrFun (hφ g (Matrix.single q j 1)) p) k
    rw [e, map_sum] at this
    simp only [map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply] at this
    simp only [Matrix.mul_apply, A, Matrix.of_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  refine GlobalTheory.exists_gl_intertwiner_of_residual_span_eq_top O Γ r ρ ρ' hspan ⟨A, fun h0 => ?_, hA⟩
  refine GlobalTheory.det_ne_zero_of_intertwines_of_span_eq_top _ (fun g => (N g).map (residue O)) hspan
    (A.map (residue O)) k j hj (fun g => ?_) ?_
  · rw [← Matrix.map_mul, hA, Matrix.map_mul]; rfl
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]

end GlobalTheory.TraceConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsOneLeNormPsumMultiset
section
open Finset MvPolynomial

namespace GlobalTheory.PowerSumDiv

variable {σ : Type} [Fintype σ]

theorem eval_esymm_card (f : σ → ℂ) :
    MvPolynomial.eval f (esymm σ ℂ (Fintype.card σ)) = ∏ i, f i := by
  rw [← Finset.card_univ, esymm, Finset.powersetCard_self]
  simp

theorem eval_psum (f : σ → ℂ) (r : ℕ) : MvPolynomial.eval f (psum σ ℂ r) = ∑ i, f i ^ r := by
  simp [psum]

theorem norm_eval_esymm_le (f : σ → ℂ) {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 1)
    (hp : ∀ r, 1 ≤ r → r ≤ Fintype.card σ → ‖∑ i, f i ^ r‖ ≤ c) :
    ∀ k, 1 ≤ k → k ≤ Fintype.card σ → ‖MvPolynomial.eval f (esymm σ ℂ k)‖ ≤ c := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hkn
    have hN := congrArg (MvPolynomial.eval f) (MvPolynomial.mul_esymm_eq_sum σ ℂ k)
    simp only [map_mul, map_pow, map_neg, map_one, map_sum, map_natCast] at hN
    have hsub : (antidiagonal k).filter (fun a => a.1 < k) ⊆ (range k).image (fun j => (j, k - j)) := by
      intro a ha
      simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
      simp only [mem_image, mem_range]
      exact ⟨a.1, ha.2, by ext <;> simp <;> omega⟩
    have hcard : ((antidiagonal k).filter (fun a => a.1 < k)).card ≤ k :=
      (card_le_card hsub).trans (card_image_le.trans (by simp))
    have hterm : ∀ a ∈ (antidiagonal k).filter (fun a => a.1 < k),
        ‖(-1 : ℂ) ^ a.1 * MvPolynomial.eval f (esymm σ ℂ a.1) * MvPolynomial.eval f (psum σ ℂ a.2)‖ ≤ c := by
      intro a ha
      simp only [mem_filter, Finset.HasAntidiagonal.mem_antidiagonal] at ha
      have he : ‖MvPolynomial.eval f (esymm σ ℂ a.1)‖ ≤ 1 := by
        rcases Nat.eq_zero_or_pos a.1 with h0 | h0
        · rw [h0, esymm_zero]; simp
        · exact (ih a.1 ha.2 h0 (by omega)).trans hc
      have hq : ‖MvPolynomial.eval f (psum σ ℂ a.2)‖ ≤ c := by
        rw [eval_psum]; exact hp _ (by omega) (by omega)
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
      calc _ ≤ 1 * c := mul_le_mul he hq (norm_nonneg _) zero_le_one
        _ = c := one_mul c
    have hk : (0 : ℝ) < k := by exact_mod_cast hk1
    have h1 : (k : ℝ) * ‖MvPolynomial.eval f (esymm σ ℂ k)‖ ≤ k * c := by
      have := congrArg norm hN
      rw [norm_mul, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, Complex.norm_natCast] at this
      rw [this]
      calc _ ≤ ∑ a ∈ (antidiagonal k).filter (fun a => a.1 < k), c := norm_sum_le_of_le _ hterm
        _ = ((antidiagonal k).filter (fun a => a.1 < k)).card * c := by rw [sum_const, nsmul_eq_mul]
        _ ≤ k * c := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc0
    exact le_of_mul_le_mul_left h1 hk

theorem exists_one_le_norm_psum (f : σ → ℂ) (hn : 1 ≤ Fintype.card σ) (hf : ‖∏ i, f i‖ = 1) :
    ∃ r, 1 ≤ r ∧ r ≤ Fintype.card σ ∧ 1 ≤ ‖∑ i, f i ^ r‖ := by
  by_contra h
  push_neg at h
  have hne : (Icc 1 (Fintype.card σ)).Nonempty := ⟨1, by simp [hn]⟩
  set c := (Icc 1 (Fintype.card σ)).sup' hne (fun r => ‖∑ i, f i ^ r‖)
  have hc1 : c < 1 := by
    rw [Finset.sup'_lt_iff]
    intro r hr
    rw [mem_Icc] at hr
    exact h r hr.1 hr.2
  have hle : ∀ r, 1 ≤ r → r ≤ Fintype.card σ → ‖∑ i, f i ^ r‖ ≤ c := fun r h1 h2 =>
    Finset.le_sup' (fun r => ‖∑ i, f i ^ r‖) (by rw [mem_Icc]; exact ⟨h1, h2⟩)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hle 1 le_rfl hn)
  have := norm_eval_esymm_le f hc0 hc1.le hle _ hn le_rfl
  rw [eval_esymm_card, hf] at this
  linarith

end GlobalTheory.PowerSumDiv

namespace GlobalTheory.PowerSumDiv

theorem exists_one_le_norm_psum_multiset (A : Multiset ℂ) (hA : 1 ≤ Multiset.card A) (h : ‖A.prod‖ = 1) :
    ∃ r, 1 ≤ r ∧ r ≤ Multiset.card A ∧ 1 ≤ ‖(A.map (· ^ r)).sum‖ := by
  set f : Fin A.toList.length → ℂ := A.toList.get
  have hA' : A = Finset.univ.val.map f := by
    rw [Fin.univ_val_map, List.ofFn_get, Multiset.coe_toList]
  have hc : Fintype.card (Fin A.toList.length) = Multiset.card A := by simp
  have hp : A.prod = ∏ i, f i := by rw [Finset.prod_eq_multiset_prod, ← hA']
  have hs : ∀ r, (A.map (· ^ r)).sum = ∑ i, f i ^ r := by
    intro r
    have e := congrArg (fun B : Multiset ℂ => (B.map (· ^ r)).sum) hA'
    rw [e, Finset.sum_eq_multiset_sum, Multiset.map_map]; rfl
  obtain ⟨r, h1, h2, h3⟩ := exists_one_le_norm_psum f (by rw [hc]; exact hA) (by rw [← hp]; exact h)
  exact ⟨r, h1, by rw [← hc]; exact h2, by rw [hs]; exact h3⟩

end GlobalTheory.PowerSumDiv

open NumberField IsDedekindDomain Filter Topology

namespace GlobalTheory.PowerSumDiv

theorem one_le_absNorm {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    (1 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by
  have : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr this

theorem not_summable_inv_absNorm {E : Type} [Field E] [NumberField E] (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ¬ Summable (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹) := by
  intro hS
  have hU : Summable (fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹) :=
    (Finset.summable_compl_iff (f := fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ)⁻¹) S).mp hS
  set M := ∑' w : HeightOneSpectrum (𝓞 E), (Ideal.absNorm w.asIdeal : ℝ)⁻¹
  have hb : ∀ s : ℝ, 1 < s → NumberField.Set.primeIdealZetaSum (Set.univ : Set (HeightOneSpectrum (𝓞 E))) s ≤ M := by
    intro s hs
    have hle : ∀ w : HeightOneSpectrum (𝓞 E), (Ideal.absNorm w.asIdeal : ℝ) ^ (-s) ≤ (Ideal.absNorm w.asIdeal : ℝ)⁻¹ := by
      intro w
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le (one_le_absNorm w) (by linarith)
    rw [NumberField.Set.primeIdealZetaSum_def,
      tsum_univ (fun w : HeightOneSpectrum (𝓞 E) => (Ideal.absNorm w.asIdeal : ℝ) ^ (-s))]
    exact Summable.tsum_le_tsum hle (hU.of_nonneg_of_le (fun _ => by positivity) hle) hU
  obtain ⟨s, hsM, hs1⟩ := (((ReciprocityTheory.Neutral.Bridge.tendsto_primeIdealZetaSum_univ E).eventually_gt_atTop M).and
    self_mem_nhdsWithin).exists
  exact absurd (hb s hs1) (not_le.mpr hsM)

theorem not_summable_psum_sq {E : Type} [Field E] [NumberField E] (N : ℕ) (hN : 1 ≤ N)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (A : HeightOneSpectrum (𝓞 E) → Multiset ℂ)
    (hcard : ∀ w ∉ S, Multiset.card (A w) = N) (hprod : ∀ w ∉ S, ‖(A w).prod‖ = 1) {x : ℝ} (hx : x ≤ 1 / N) :
    ¬ Summable (fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} × ℕ =>
      ‖((A p.1.1).map (· ^ (p.2 + 1))).sum‖ ^ 2 * (Ideal.absNorm p.1.1.asIdeal : ℝ) ^ (-(((p.2 : ℝ) + 1) * x)) /
        ((p.2 : ℝ) + 1)) := by
  intro hs
  have hex : ∀ w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S},
      ∃ r, 1 ≤ r ∧ r ≤ N ∧ 1 ≤ ‖((A w.1).map (· ^ r)).sum‖ := by
    intro w
    have := exists_one_le_norm_psum_multiset (A w.1) (by rw [hcard w.1 w.2]; exact hN) (hprod w.1 w.2)
    rwa [hcard w.1 w.2] at this
  choose r hr1 hrN hr using hex
  set F := fun p : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} × ℕ =>
      ‖((A p.1.1).map (· ^ (p.2 + 1))).sum‖ ^ 2 * (Ideal.absNorm p.1.1.asIdeal : ℝ) ^ (-(((p.2 : ℝ) + 1) * x)) /
        ((p.2 : ℝ) + 1) with hF
  have hinj : Function.Injective (fun w : {w : HeightOneSpectrum (𝓞 E) // w ∉ S} => (w, r w - 1)) :=
    fun a b h => congrArg Prod.fst h
  have h1 := hs.comp_injective hinj
  apply not_summable_inv_absNorm S
  refine (h1.mul_left (N : ℝ)).of_nonneg_of_le (fun _ => by positivity) (fun w => ?_)
  have hre : (((r w - 1 : ℕ) : ℝ) + 1) = (r w : ℝ) := by
    rw [Nat.cast_sub (hr1 w)]; push_cast; ring
  have hpow : r w - 1 + 1 = r w := Nat.sub_add_cancel (hr1 w)
  simp only [Function.comp_apply, hF, hre, hpow]
  have hq := one_le_absNorm w.1
  have hr0 : (0 : ℝ) < r w := by exact_mod_cast hr1 w
  have hrN' : (r w : ℝ) ≤ N := by exact_mod_cast hrN w
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hrx : (r w : ℝ) * x ≤ 1 := by
    calc (r w : ℝ) * x ≤ r w * (1 / N) := mul_le_mul_of_nonneg_left hx hr0.le
      _ = r w / N := by ring
      _ ≤ 1 := (div_le_one hN0).mpr hrN'
  have hqq : (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ ≤ (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x)) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hP : 1 ≤ ‖((A w.1).map (· ^ r w)).sum‖ ^ 2 := one_le_pow₀ (hr w)
  have hQ0 : 0 ≤ (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x)) := by positivity
  have hNr : 1 ≤ (N : ℝ) / r w := (one_le_div hr0).mpr hrN'
  calc (Ideal.absNorm w.1.asIdeal : ℝ)⁻¹ ≤ (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x)) := hqq
    _ ≤ ((N : ℝ) / r w) * (‖((A w.1).map (· ^ r w)).sum‖ ^ 2 * (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-((r w : ℝ) * x))) := by
        nlinarith [mul_le_mul hNr hP zero_le_one (by positivity : (0:ℝ) ≤ N / r w)]
    _ = _ := by field_simp

end GlobalTheory.PowerSumDiv

namespace GlobalTheory.PowerSumDiv

open NumberField IsDedekindDomain

end GlobalTheory.PowerSumDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntOfCompatibleZmodPowStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicInt_of_compatible_zmod_pow' : ∀ (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n)), (∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) → ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n := by
  first | exact @GlobalTheory.exists_padicInt_of_compatible_zmod_pow | exact GlobalTheory.exists_padicInt_of_compatible_zmod_pow | (intros; apply GlobalTheory.exists_padicInt_of_compatible_zmod_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowDescentCyclotomicStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_descent_cyclotomic' : ∀ (E : Type) [Field E] [NumberField E] (l r : ℕ), l.Prime → ∃ M : ℕ, 0 < M ∧ l ^ r ∣ M ∧
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (u : E) (w : Ω),
      w ∈ IntermediateField.adjoin E {ζ} → w ^ M = algebraMap E Ω u → ∃ v : E, v ^ (l ^ r) = u := by
  first | exact @GlobalTheory.exists_pow_descent_cyclotomic | exact GlobalTheory.exists_pow_descent_cyclotomic | (intros; apply GlobalTheory.exists_pow_descent_cyclotomic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimeDvdSubOneCyclotomicIrreducibleOverStatement
section
open NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_dvd_sub_one_cyclotomic_irreducible_over : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), n ≠ 0 → ∃ m : ℕ, m.Prime ∧ n ∣ m - 1 ∧ Irreducible (cyclotomic m K) := by
  first | exact @GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic | exact GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic | (intros; apply GlobalTheory.exists_prime_dvd_sub_one_irreducible_cyclotomic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRepresentativesTwoElementOrbitsInvolutionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_representatives_two_element_orbits_involution : ∀ (ι : Type) [Finite ι] (s : ι → ι), (∀ i, s (s i) = i) → ∃ (r : ℕ) (e : Fin r → ι), (∀ j k, e j = e k → j = k) ∧ (∀ j k, s (e j) ≠ e k) ∧ ∀ i, s i = i ∨ ∃ j, i = e j ∨ i = s (e j) := by
  first | exact @GlobalTheory.involution_pair_representatives | exact GlobalTheory.involution_pair_representatives | (intros; apply GlobalTheory.involution_pair_representatives <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsResidueAnnihilatorOfNotStandardColumnFormAStatement
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_residue_annihilator_of_not_standard_column_form_alt : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r t : ℕ) (ϖ : O), Irreducible ϖ → ∀ x : Matrix (Fin r ⊕ Fin t) (Fin r) O, (¬ ∃ (g : GL (Fin r) K) (z : Matrix (Fin r ⊕ Fin t) (Fin r) O), x.map (algebraMap O K) * (g : Matrix (Fin r) (Fin r) K) = ((Matrix.fromRows (1 : Matrix (Fin r) (Fin r) O) (0 : Matrix (Fin t) (Fin r) O)) + ϖ • z).map (algebraMap O K)) → ∃ a : Fin r → IsLocalRing.ResidueField O, a ≠ 0 ∧ ∀ u : Fin r ⊕ Fin t → O, (fun i => algebraMap O K (u i)) ∈ Submodule.span K (Set.range fun j => fun i => algebraMap O K (x i j)) → (∀ i, IsLocalRing.residue O (u (Sum.inr i)) = 0) → a ⬝ᵥ (fun i => IsLocalRing.residue O (u (Sum.inl i))) = 0 := by
  first | exact @GlobalTheory.exists_residue_annihilator_of_not_standard_column_form | exact GlobalTheory.exists_residue_annihilator_of_not_standard_column_form | (intros; apply GlobalTheory.exists_residue_annihilator_of_not_standard_column_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubfieldAdjoinRootsOfUnityEmbeddingComplexStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subfield_adjoin_rootsOfUnity_embedding_complex : ∀ {L0 K : Type} [Field L0] [Field K] (s : L0 →+* K) (t : L0 →+* ℂ) (Z : Set K), (∀ z ∈ Z, ∃ n : ℕ, 0 < n ∧ z ^ n = 1) → ∃ (E : Subfield K) (j : E →+* ℂ), (∀ x, s x ∈ E) ∧ Z ⊆ E ∧ ∀ x (hx : s x ∈ E), j ⟨s x, hx⟩ = t x := by
  first | exact @GlobalTheory.adjoin_roots_of_unity_embeds_complex | exact GlobalTheory.adjoin_roots_of_unity_embeds_complex | (intros; apply GlobalTheory.adjoin_roots_of_unity_embeds_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTensorIdempotentOfAlgHomToBaseStatement
section
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tensor_idempotent_of_algHom_to_base : ∀ (E K E' : Type) [Field E] [CharZero E] [Field K] [Field E'] [Algebra E K] [Algebra E E'] [FiniteDimensional E E'] (ψ : K ⊗[E] E' →ₐ[K] K), ∃ e : K ⊗[E] E', ψ e = 1 ∧ ∀ a, e * a = algebraMap K (K ⊗[E] E') (ψ a) * e := by
  first | exact @GlobalTheory.exists_tensor_idem_of_algHom | exact GlobalTheory.exists_tensor_idem_of_algHom | (intros; apply GlobalTheory.exists_tensor_idem_of_algHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitFrobeniusIterateProductEqStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_frobenius_iterate_product_eq : ∀ (A : Type) [CommRing A] (p : ℕ), IsAdicComplete (Ideal.span {(p : A)}) A → ∀ (φ : A →+* A) (u : A), IsUnit u → (∀ r : ℕ, ∃ M : ℕ, ∀ m ≥ M, (⇑φ)^[m] u - 1 ∈ Ideal.span {(p : A)} ^ r) → ∀ n : ℕ, 0 < n → ∃ c : A, IsUnit c ∧ (⇑φ)^[n] c * (⇑φ)^[n - 1] u = c := by
  first | exact @GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | exact GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq | (intros; apply GlobalTheory.FrobeniusProduct.exists_unit_iterate_mul_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlg
section
noncomputable section

open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma.HilbertNinety

theorem exists_unit_sigma (K : UQ) (B : InvAlg K) (u : B.A) (hu : u * B.σ u = 1) :
    ∃ β : B.Aˣ, B.σ (β : B.A) = β * u := by
  classical
  letI : Module ℚ B.A := Module.compHom B.A (algebraMap ℚ K.E)
  let b : B.A →+ B.A :=
    { toFun := fun a => a + B.σ a * B.σ u
      map_zero' := by simp
      map_add' := by intro x y; simp only [map_add]; ring }
  have hb : ∀ a, b a = a + B.σ a * B.σ u := fun a => rfl
  have hbσ : ∀ a, B.σ (b a) = b a * u := by
    intro a
    rw [hb, map_add, map_mul, B.σ_σ, B.σ_σ]
    linear_combination (-(B.σ a)) * hu
  obtain ⟨x, y, hxy, hne⟩ := K.c_res
  set e : K.E := algebraMap K.O K.E x with he
  have hce : K.c e - e ≠ 0 := by
    intro h
    rw [sub_eq_zero, he, hxy] at h
    have := IsFractionRing.injective K.O K.E h
    exact hne (by rw [this, sub_self]; exact Ideal.zero_mem _)
  have key : ∀ z : B.A, algebraMap K.E B.A (K.c e - e) * z =
      algebraMap K.E B.A (K.c e) * b z - b (algebraMap K.E B.A e * z) := by
    intro z
    rw [hb, hb, map_mul, B.σ_alg, map_sub]
    ring
  haveI : IsArtinianRing B.A := IsArtinianRing.of_finite K.E B.A
  haveI : Fintype (MaximalSpectrum B.A) := Fintype.ofFinite _
  let S : MaximalSpectrum B.A → Submodule ℚ B.A := fun m =>
    { carrier := {a | b a ∈ m.asIdeal}
      add_mem' := fun {a c} ha hc => by
        change b (a + c) ∈ m.asIdeal
        rw [map_add]; exact m.asIdeal.add_mem ha hc
      zero_mem' := by change b 0 ∈ m.asIdeal; rw [map_zero]; exact m.asIdeal.zero_mem
      smul_mem' := fun q a ha => by
        change b (q • a) ∈ m.asIdeal
        rw [map_rat_smul]
        change (algebraMap ℚ K.E q) • b a ∈ m.asIdeal
        rw [Algebra.smul_def]
        exact m.asIdeal.mul_mem_left _ ha }
  have hS : ⊤ ∉ Finset.univ.image S := by
    intro h
    obtain ⟨m, -, hm⟩ := Finset.mem_image.1 h
    have hall : ∀ a, b a ∈ m.asIdeal := fun a => by
      have : a ∈ S m := hm ▸ Submodule.mem_top
      exact this
    have h1 : algebraMap K.E B.A (K.c e - e) ∈ m.asIdeal := by
      have := key 1
      rw [mul_one] at this
      rw [this]
      exact m.asIdeal.sub_mem (m.asIdeal.mul_mem_left _ (hall 1)) (hall _)
    apply m.isMaximal.ne_top
    rw [Ideal.eq_top_iff_one]
    have h2 : algebraMap K.E B.A (K.c e - e)⁻¹ * algebraMap K.E B.A (K.c e - e) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hce, map_one]
    rw [← h2]
    exact m.asIdeal.mul_mem_left _ h1
  have h3 := Subspace.biUnion_ne_univ_of_top_notMem hS
  obtain ⟨a, ha⟩ := (Set.ne_univ_iff_exists_notMem _).1 h3
  have hunit : IsUnit (b a) := by
    by_contra hn
    obtain ⟨m, hm, hxm⟩ := exists_max_ideal_of_mem_nonunits hn
    apply ha
    exact Set.mem_biUnion (x := S ⟨m, hm⟩) (by simp) hxm
  exact ⟨hunit.unit, by rw [IsUnit.unit_spec]; exact hbσ a⟩

end GlobalTheory.UnitLemma.HilbertNinety
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsValuationSubringAlgClosedNotIsUnitStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuationSubring_algClosed_not_isUnit : ∀ (S : Type) [CommRing S] (u : S), ¬ IsUnit u → ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (V : ValuationSubring L) (f : S →+* ↥V), ¬ IsUnit (f u) ∧ ∀ s ∈ nonZeroDivisors S, f s ≠ 0 := by
  first | exact @GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | exact GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero | (intros; apply GlobalTheory.exists_valuationSubring_not_isUnit_and_nonZeroDivisors_ne_zero <;> assumption)
end

