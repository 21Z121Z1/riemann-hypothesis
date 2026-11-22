import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LogFactorialIndices.SignedSubspaceIndex.Bundle0001
import Mathlib
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SelectionLemmas
import Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundRows
import Formalism.LogFactorialBounds.LogFactorialProofs.PrimeSum

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula
section
open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

theorem sum_log_embeddings_eq (K : Type) [Field K] [NumberField K] (a : K) (ha : a ≠ 0) :
    ∑ σ : K →+* ℂ, Real.log ‖σ a‖ = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| := by
  have h := Algebra.norm_eq_prod_embeddings ℚ ℂ a
  have hq : (algebraMap ℚ ℂ) (Algebra.norm ℚ a) = ((Algebra.norm ℚ a : ℚ) : ℂ) := eq_ratCast _ _
  have hprod : ((Algebra.norm ℚ a : ℚ) : ℂ) = ∏ σ : K →+* ℂ, σ a := by
    rw [← hq, h]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom K ℂ).symm _ _ (fun _ => rfl)
  have hn : |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ σ : K →+* ℂ, ‖σ a‖ := by
    rw [← norm_prod, ← hprod]
    simp
  rw [hn, Real.log_prod (fun σ _ => by simpa using ha)]

theorem log_abs_norm_eq_two_sum (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (a : K) (ha : a ≠ 0) :
    Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| =
      2 * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖ := by
  have h := NumberField.InfinitePlace.prod_eq_abs_norm a
  have hm : ∀ w : InfinitePlace K, w.mult = 2 := fun w => by
    rw [InfinitePlace.mult, if_neg (InfinitePlace.not_isReal_iff_isComplex.mpr
      (IsTotallyComplex.isComplex w))]
  have hpos : ∀ w : InfinitePlace K, w a ≠ 0 := fun w => by
    rw [← InfinitePlace.norm_embedding_eq]
    simpa using ha
  rw [← Rat.cast_abs, ← h, Real.log_prod (fun w _ => pow_ne_zero _ (hpos w)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hm, Real.log_pow, InfinitePlace.norm_embedding_eq]
  push_cast
  ring

theorem prod_formula' : ProdFormula := by
  intro K _ _ _ _ a ha
  set I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K := FractionalIdeal.spanSingleton _ a with hIdef
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact ha
  have hfin : {w : HeightOneSpectrum (𝓞 K) | FractionalIdeal.count K w I ≠ 0}.Finite :=
    Filter.eventually_cofinite.mp (FractionalIdeal.finite_factors I)
  have hvw : ∀ w : HeightOneSpectrum (𝓞 K), vw w a = FractionalIdeal.count K w I := fun w => rfl
  have hsupp : (Function.support fun w : HeightOneSpectrum (𝓞 K) => lw w * (vw w a : ℝ)) ⊆
      (hfin.toFinset : Set (HeightOneSpectrum (𝓞 K))) := by
    intro w hw
    simp only [Function.mem_support, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hw ⊢
    intro h0
    apply hw
    simp [hvw, h0]
  refine ⟨hfin.subset (by simpa using hsupp), ?_⟩
  rw [finsum_eq_sum_of_support_subset _ hsupp]
  have hpos : ∀ w : HeightOneSpectrum (𝓞 K), (Ideal.absNorm w.asIdeal : ℝ) ≠ 0 := fun w => by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact w.ne_bot
  have hN : (|Algebra.norm ℚ a| : ℚ) = ∏ w ∈ hfin.toFinset,
      ((Ideal.absNorm w.asIdeal : ℚ)) ^ FractionalIdeal.count K w I := by
    rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), ← hIdef]
    conv_lhs => rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI]
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := hfin.toFinset) ?_, map_prod]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
    · intro w hw
      simp only [Function.mem_mulSupport, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hw ⊢
      intro h0
      apply hw
      rw [h0, zpow_zero]
  have hlog : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∑ w ∈ hfin.toFinset,
      (FractionalIdeal.count K w I : ℝ) * Real.log (Ideal.absNorm w.asIdeal : ℝ) := by
    have h1 : |((Algebra.norm ℚ a : ℚ) : ℝ)| = ∏ w ∈ hfin.toFinset,
        ((Ideal.absNorm w.asIdeal : ℝ)) ^ FractionalIdeal.count K w I := by
      rw [← Rat.cast_abs, hN]
      push_cast
      rfl
    rw [h1, Real.log_prod (fun w _ => zpow_ne_zero _ (hpos w))]
    exact Finset.sum_congr rfl fun w _ => Real.log_zpow _ _
  have hB := log_abs_norm_eq_two_sum K a ha
  have hn : (finrank ℚ K : ℝ) ≠ 0 := by
    have := Module.finrank_pos (R := ℚ) (M := K)
    positivity
  calc (2 / (finrank ℚ K : ℝ)) * ∑ v : InfinitePlace K, Real.log ‖v.embedding a‖
      = Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / finrank ℚ K := by
        rw [hB]
        field_simp
    _ = ∑ w ∈ hfin.toFinset, lw w * (vw w a : ℝ) := by
        rw [hlog, Finset.sum_div]
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [hvw, lw]
        ring

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
section
open Module NumberField IsDedekindDomain Matrix
open scoped Matrix

noncomputable section

namespace Formalism.DivisionValues

namespace ReductionFirst

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def Tw (w : HeightOneSpectrum (𝓞 K)) : Submonoid (𝓞 K) where
  carrier := {s | s ∉ w.asIdeal ∧ cO K s ∉ w.asIdeal}
  one_mem' := by
    have h1 : (1 : 𝓞 K) ∉ w.asIdeal := fun h => w.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
    exact ⟨h1, by simpa using h1⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha h, hb h]
    · rw [map_mul] at h
      rcases w.isPrime.mem_or_mem h with h | h
      exacts [ha' h, hb' h]

theorem cO_coe (x : 𝓞 K) : ((cO K x : 𝓞 K) : K) = star (x : K) := rfl

theorem cO_cO (x : 𝓞 K) : cO K (cO K x) = x := by
  apply RingOfIntegers.ext
  rw [cO_coe, cO_coe, star_star]

theorem cO_mem_Tw {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : cO K s ∈ Tw w :=
  ⟨hs.2, by rw [cO_cO]; exact hs.1⟩

theorem hcompl_le_Tw (w : HeightOneSpectrum (𝓞 K)) :
    Formalism.HermitianLatticesTheory.hcompl (K := K) w.asIdeal ≤ Tw w := by
  refine Submonoid.closure_le.2 ?_
  rintro s ⟨hs, hs'⟩
  exact ⟨hs, hs' (cO K s) rfl⟩

theorem smul_coe {m : Type*} (r : 𝓞 K) (v : m → K) : r • v = (r : K) • v :=
  (algebraMap_smul K r v).symm

def InS (w : HeightOneSpectrum (𝓞 K)) (x : K) : Prop :=
  ∃ s ∈ Tw w, ∃ r : 𝓞 K, (s : K) * x = r

theorem InS.star' {w : HeightOneSpectrum (𝓞 K)} {x : K} (h : InS w x) : InS w (star x) := by
  obtain ⟨s, hs, r, hr⟩ := h
  refine ⟨cO K s, cO_mem_Tw hs, cO K r, ?_⟩
  rw [cO_coe, cO_coe, ← hr, star_mul']

theorem common_den {w : HeightOneSpectrum (𝓞 K)} {ι : Type*} (S : Finset ι) (x : ι → K)
    (h : ∀ k ∈ S, InS w (x k)) : ∃ s ∈ Tw w, ∀ k ∈ S, ∃ r : 𝓞 K, (s : K) * x k = r := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, (Tw w).one_mem, by simp⟩
  | @insert a S ha ih =>
    obtain ⟨t, ht, hS⟩ := ih (fun k hk => h k (Finset.mem_insert_of_mem hk))
    obtain ⟨s, hs, r, hr⟩ := h a (Finset.mem_insert_self a S)
    refine ⟨s * t, (Tw w).mul_mem hs ht, ?_⟩
    intro k hk
    rcases Finset.mem_insert.1 hk with rfl | hk
    · exact ⟨t * r, by show (s : K) * (t : K) * x k = (t : K) * (r : K); linear_combination (t : K) * hr⟩
    · obtain ⟨r', hr'⟩ := hS k hk
      exact ⟨s * r', by show (s : K) * (t : K) * x k = (s : K) * (r' : K); linear_combination (s : K) * hr'⟩

theorem vw_zero (w : HeightOneSpectrum (𝓞 K)) : vw w (0 : K) = 0 := by
  simp [vw, FractionalIdeal.spanSingleton_zero, FractionalIdeal.count_zero]

theorem vw_one (w : HeightOneSpectrum (𝓞 K)) : vw w (1 : K) = 0 := by
  simp [vw, FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one]

theorem vw_mul (w : HeightOneSpectrum (𝓞 K)) {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) :
    vw w (a * b) = vw w a + vw w b := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K w (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 ha)
      (mt FractionalIdeal.spanSingleton_eq_zero_iff.1 hb)]

theorem vw_pow (w : HeightOneSpectrum (𝓞 K)) (a : K) (m : ℕ) :
    vw w (a ^ m) = (m : ℤ) * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

theorem vw_int_nonneg (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) : 0 ≤ vw w (r : K) := by
  unfold vw
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

theorem vw_unit (w : HeightOneSpectrum (𝓞 K)) (r : 𝓞 K) (hr : r ∉ w.asIdeal) :
    vw w (r : K) = 0 := by
  classical
  have hr0 : r ≠ 0 := fun h => hr (h ▸ w.asIdeal.zero_mem)
  have hJ : Ideal.span {r} ≠ (0 : Ideal (𝓞 K)) := by
    rw [Ne, Submodule.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr0
  unfold vw
  rw [show (r : K) = algebraMap (𝓞 K) K r from rfl, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe K w hJ]
  have h2 : ¬ w.asIdeal ∣ Ideal.span {r} := by
    rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]; exact hr
  have h3 := mt (Associates.count_ne_zero_iff_dvd hJ w.irreducible).1 h2
  rw [not_not] at h3
  simp [h3]

theorem Tw_ne_zero {w : HeightOneSpectrum (𝓞 K)} {s : 𝓞 K} (hs : s ∈ Tw w) : (s : K) ≠ 0 := by
  intro h
  apply hs.1
  have : s = 0 := RingOfIntegers.ext (by simpa using h)
  rw [this]; exact w.asIdeal.zero_mem

theorem hform_apply {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (y x : Fin n → K) :
    hform H y x = star y ⬝ᵥ (H *ᵥ x) := by
  rw [hform, Matrix.toLinearMapₛₗ₂'_apply]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply, starRingEnd_apply,
    RingHom.id_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem main {n D : ℕ} (H : Matrix (Fin n) (Fin n) K) (P : Matrix (Fin D) (Fin n) K)
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : M.FG) (l g : ℕ) (hl : 0 < l)
    (hdual : ∀ x ∈ Formalism.HermitianLatticesTheory.dual (hform H) M, ((l : 𝓞 K) ^ g) • x ∈ M)
    (w : HeightOneSpectrum (𝓞 K)) (e : Fin D → Fin D → K) (he : IsLocBasis (matLat P M) w e) :
    vw w (gramR (quotGram P H) e) ≤ (g : ℤ) * (D : ℤ) * vw w (l : K) :=
  _root_.UpperTheory.Reformulated.B.SelectionLemmas.main H P M hM l g hl hdual w e he

end ReductionFirst

theorem reduction_lemma_first : LemmaRa := by
  intro K _ _ _ _ K0 _ v0 _ n D H _ _ P _ M hM l g hl hdual w e he
  exact ReductionFirst.main H P M hM.fg l g hl hdual w e he

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionThirdStepMean
section
open Module NumberField
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace Formalism.DivisionValues

namespace NormSquareReduction

variable {Q E : Type} [NormedAddCommGroup Q] [InnerProductSpace ℂ Q]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem norm_sq_le (ι : Q →ₗ[ℂ] E) {Ix : Type} [Fintype Ix] (Qp : Ix → Submodule ℂ Q)
    (hsup : (⨆ p, Qp p) = ⊤) (s : Ix → ℝ) (smin : ℝ) (hs : ∀ p, smin ≤ s p)
    (hι : ∀ p, ∀ x ∈ Qp p, ∀ y : Q, ⟪ι x, ι y⟫_ℂ = (s p : ℂ) * ⟪x, y⟫_ℂ) (F : Q) :
    smin * ‖F‖ ^ 2 ≤ ‖ι F‖ ^ 2 := by
  classical
  have hF : F ∈ ⨆ p, Qp p := by rw [hsup]; exact Submodule.mem_top

  obtain ⟨y, hy, hFy⟩ : ∃ y : Ix → Q, (∀ p, y p ∈ Qp p) ∧ F = ∑ p, y p := by
    refine Submodule.iSup_induction
      (motive := fun z => ∃ y : Ix → Q, (∀ p, y p ∈ Qp p) ∧ z = ∑ p, y p) Qp hF ?_ ?_ ?_
    · intro i x hx
      refine ⟨Pi.single i x, fun p => ?_, ?_⟩
      · rcases eq_or_ne p i with rfl | h
        · simpa using hx
        · rw [Pi.single_eq_of_ne h]; exact (Qp p).zero_mem
      · rw [Finset.sum_pi_single']; simp
    · exact ⟨0, fun p => (Qp p).zero_mem, by simp⟩
    · rintro x1 x2 ⟨y1, hy1, h1⟩ ⟨y2, hy2, h2⟩
      refine ⟨y1 + y2, fun p => (Qp p).add_mem (hy1 p) (hy2 p), ?_⟩
      rw [h1, h2]; simp [Finset.sum_add_distrib]

  have horth : ∀ p q, s p ≠ s q → ⟪y p, y q⟫_ℂ = 0 := by
    intro p q hpq
    have h1 := hι p (y p) (hy p) (y q)
    have h2 := hι q (y q) (hy q) (y p)
    have h3 : ⟪ι (y p), ι (y q)⟫_ℂ = (s q : ℂ) * ⟪y p, y q⟫_ℂ := by
      rw [← inner_conj_symm, h2, map_mul, Complex.conj_ofReal, inner_conj_symm]
    have h4 : ((s p : ℂ) - (s q : ℂ)) * ⟪y p, y q⟫_ℂ = 0 := by
      rw [sub_mul, ← h1, ← h3, sub_self]
    have h5 : (s p : ℂ) - (s q : ℂ) ≠ 0 := by
      rw [sub_ne_zero]; exact_mod_cast hpq
    exact (mul_eq_zero.mp h4).resolve_left h5

  have hkey : ∀ p q, ⟪ι (y p), ι (y q)⟫_ℂ - (smin : ℂ) * ⟪y p, y q⟫_ℂ =
      ⟪((Real.sqrt (s p - smin) : ℝ) : ℂ) • y p, ((Real.sqrt (s q - smin) : ℝ) : ℂ) • y q⟫_ℂ := by
    intro p q
    rw [hι p (y p) (hy p) (y q), inner_smul_left, inner_smul_right, Complex.conj_ofReal,
      ← sub_mul, ← mul_assoc]
    by_cases hpq : s p = s q
    · congr 1
      have hc : Real.sqrt (s p - smin) * Real.sqrt (s q - smin) = s p - smin := by
        rw [hpq, Real.mul_self_sqrt (by linarith [hs q])]
      rw [← Complex.ofReal_mul, hc, Complex.ofReal_sub]
    · simp [horth p q hpq]
  have hsum : ⟪ι F, ι F⟫_ℂ - (smin : ℂ) * ⟪F, F⟫_ℂ =
      ⟪∑ p, ((Real.sqrt (s p - smin) : ℝ) : ℂ) • y p,
        ∑ p, ((Real.sqrt (s p - smin) : ℝ) : ℂ) • y p⟫_ℂ := by
    simp only [hFy, map_sum, sum_inner, inner_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    first
      | exact hkey a b
      | exact hkey b a
  obtain ⟨Z, hZ⟩ : ∃ Z : Q, ⟪ι F, ι F⟫_ℂ - (smin : ℂ) * ⟪F, F⟫_ℂ = ⟪Z, Z⟫_ℂ := ⟨_, hsum⟩
  have hn : ∀ {G : Type} [NormedAddCommGroup G] [InnerProductSpace ℂ G] (x : G),
      (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
    intro G _ _ x
    first
      | exact inner_self_eq_norm_sq (𝕜 := ℂ) x
      | exact (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm
      | simp
  have hre := congrArg Complex.re hZ
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hre
  rw [hn, hn, hn] at hre
  nlinarith [sq_nonneg ‖Z‖]

end NormSquareReduction

theorem reduction_third_step : StepC := by
  intro Φ Cs Q E _ _ _ _ _ _ _ _ _ ι hsurj Ix _ Qp hsup s smin hsmin hs hι col k hcol P p hP B hB hk hp
    φ e
  obtain ⟨F, rfl⟩ := hsurj e
  have hF := NormSquareReduction.norm_sq_le ι Qp hsup s smin hs hι F
  have hsq : 0 < Real.sqrt smin := Real.sqrt_pos.mpr hsmin
  have hFle : ‖F‖ ≤ ‖ι F‖ / Real.sqrt smin := by
    rw [le_div_iff₀ hsq]
    have h1 : (‖F‖ * Real.sqrt smin) ^ 2 ≤ ‖ι F‖ ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hsmin.le]; linarith
    nlinarith [norm_nonneg (ι F), mul_nonneg (norm_nonneg F) hsq.le]
  rw [hB φ F]
  have h1 := hP (col φ) F
  have h2 := hcol φ
  have hpk : p * ‖col φ‖ * ‖F‖ ≤ p * (k * ‖φ‖) * (‖ι F‖ / Real.sqrt smin) :=
    mul_le_mul (mul_le_mul_of_nonneg_left h2 hp) hFle (norm_nonneg _)
      (mul_nonneg hp (mul_nonneg hk (norm_nonneg _)))
  calc ‖P (col φ) F‖ ≤ p * ‖col φ‖ * ‖F‖ := h1
    _ ≤ p * (k * ‖φ‖) * (‖ι F‖ / Real.sqrt smin) := hpk
    _ = p * k / Real.sqrt smin * ‖φ‖ * ‖ι F‖ := by ring

end Formalism.DivisionValues
end
end

-- bundled from Formalism.QuotientMetricDivisors.HermitianTwistDivisors.WeightedPlaceLogSum
section
open Finset NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

namespace place_log_sum

lemma mean_le {E : Type} [Fintype E] [Nonempty E] (u : E → ℝ) (B : ℝ) (h : ∀ s, u s ≤ B) :
    (∑ s, u s) / (Fintype.card E : ℝ) ≤ B := by
  have hc : (0 : ℝ) < (Fintype.card E : ℝ) := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hc]
  calc ∑ s, u s ≤ ∑ _s : E, B := Finset.sum_le_sum fun s _ => h s
    _ = B * (Fintype.card E : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end place_log_sum

theorem WeightedPlaceLogSum : LPrimeBound := by
  intro x L b a rd La g nV L' Cg Cn hx hL hb ha hrd hLa hg hlg hnV hlnV hCg hCn hL'
  have hx0 : 0 < x := by linarith
  have hrd0 : 0 < rd := by linarith
  have hb0 : 0 < b := by rw [hb]; exact Real.exp_pos L
  have hlb : Real.log b = L := by rw [hb, Real.log_exp]
  have hlx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlrd : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have e1 : La = Real.log x + L + Real.log rd := by
    rw [hLa, ha, Real.log_mul (mul_pos hx0 hb0).ne' hrd0.ne', Real.log_mul hx0.ne' hb0.ne', hlb]
  have e2 : L' = L + Real.log rd + Real.log g + Real.log nV := by
    rw [hL', Real.log_mul (mul_pos (mul_pos hb0 hrd0) hg).ne' hnV.ne',
      Real.log_mul (mul_pos hb0 hrd0).ne' hg.ne', Real.log_mul hb0.ne' hrd0.ne', hlb]
  refine ⟨?_, by linarith⟩
  rw [e1, e2]
  nlinarith [mul_nonneg hCg hlx, mul_nonneg hCg hlrd, mul_nonneg hCn hL, mul_nonneg hCn hlrd]

theorem prime_log_sum_bound : PrimeLogSum := by
  intro Y hY s hs
  have hn : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hnR : (0 : ℝ) < (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn
  have hfl : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
  calc ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log (p : ℝ) / (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primesLE.2 ⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩
        · intro p _ _
          exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    _ ≤ Real.log (⌊Y⌋₊ : ℝ) + Real.log 4 := Formalism.LogFactorialBounds.sum_primesLE_log_div_le _ hn
    _ ≤ Real.log Y + Real.log 4 := by
        have := Real.log_le_log hnR hfl
        linarith

namespace place_log_sum

lemma lw_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ lw w :=
  div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)

lemma vw_nat_nonneg {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    0 ≤ vw w (n : K) := by
  have h : ((n : 𝓞 K) : K) = (n : K) := map_natCast _ n
  unfold vw
  rw [← h, ← FractionalIdeal.coeIdeal_span_singleton]
  exact FractionalIdeal.count_coe_nonneg K w _

end place_log_sum

namespace place_log_sum

end place_log_sum

end Formalism.DivisionValues
end
end

