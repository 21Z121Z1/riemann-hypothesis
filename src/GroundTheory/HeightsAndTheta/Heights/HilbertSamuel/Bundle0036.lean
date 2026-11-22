import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0025

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMetricMaxComparison
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem MetricMaxComparison.proof : MetricMaxComparison.Statement := by
  intro K _ ι _ A hA

  let blk : (k : K) → ((Σ k, ι k) → ℂ) → (ι k → ℂ) := fun k z i => z ⟨k, i⟩
  have hblkc : ∀ k, Continuous (blk k) := fun k => continuous_pi fun i => continuous_apply _
  let S : Set ((Σ k, ι k) → ℂ) := {z | ∀ k, ‖blk k z‖ = 1}
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · have hS : S = ⋂ k, (fun z => ‖blk k z‖) ⁻¹' {1} := by ext z; simp [S]
      rw [hS]
      exact isClosed_iInter fun k => isClosed_singleton.preimage (hblkc k).norm
    · refine (Metric.isBounded_closedBall (x := (0 : (Σ k, ι k) → ℂ)) (r := 1)).subset fun z hz => ?_
      rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
      intro p
      calc ‖z p‖ = ‖blk p.1 z p.2‖ := rfl
        _ ≤ ‖blk p.1 z‖ := norm_le_pi_norm _ _
        _ = 1 := hz p.1
  have hSU : S ⊆ {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := by
    intro z hz k
    by_contra h
    simp only [not_exists, not_not] at h
    have h0 : blk k z = 0 := funext h
    have h1 : ‖blk k z‖ = 1 := hz k
    rw [h0, norm_zero] at h1
    exact zero_ne_one h1
  obtain ⟨C0, hC0⟩ := hSc.exists_bound_of_continuousOn (hA.continuousOn.mono hSU)
  refine ⟨max C0 1, le_max_right _ _, fun z hz => ?_⟩
  have hn : ∀ k, 0 < ‖blk k z‖ := fun k => by
    obtain ⟨i, hi⟩ := hz k
    exact norm_pos_iff.mpr fun h0 => hi (congrFun h0 i)
  let c : K → ℂ := fun k => ((‖blk k z‖⁻¹ : ℝ) : ℂ)
  have hc0 : ∀ k, c k ≠ 0 := fun k => by
    simp only [c, ne_eq, Complex.ofReal_eq_zero, inv_eq_zero]
    exact (hn k).ne'
  have hcn : ∀ k, ‖c k‖ = ‖blk k z‖⁻¹ := fun k => by
    simp only [c, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (inv_pos.mpr (hn k))
  have hwS : (fun p : Σ k, ι k => c p.1 * z p) ∈ S := fun k => by
    have h1 : blk k (fun p : Σ k, ι k => c p.1 * z p) = c k • blk k z := rfl
    rw [h1, norm_smul, hcn, inv_mul_cancel₀ (hn k).ne']
  have hmax : (HermLine.ofMetrics (fun k => maxMetric ℂ (ι k)) A.a).h z = ∏ k, ‖blk k z‖ ^ A.a k := rfl
  have hprod : (∏ k, ‖blk k z‖ ^ A.a k) * (∏ k, ‖c k‖ ^ A.a k) = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun k _ => ?_
    rw [hcn, ← mul_zpow, mul_inv_cancel₀ (hn k).ne', one_zpow]
  have hz' : A.h z = (∏ k, ‖blk k z‖ ^ A.a k) * A.h (fun p : Σ k, ι k => c p.1 * z p) := by
    rw [A.smul c z hc0, ← mul_assoc, hprod, one_mul]
  have hpos : 0 ≤ ∏ k, ‖blk k z‖ ^ A.a k :=
    Finset.prod_nonneg fun k _ => zpow_nonneg (norm_nonneg _) _
  have hbw : A.h (fun p : Σ k, ι k => c p.1 * z p) ≤ max C0 1 := by
    have h1 := hC0 _ hwS
    rw [Real.norm_eq_abs] at h1
    exact (le_abs_self _).trans (h1.trans (le_max_left _ _))
  rw [hmax, hz', mul_comm (max C0 1)]
  exact mul_le_mul_of_nonneg_left hbw hpos

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultiDegreePositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

namespace MultiDegreePositive

theorem tendsto_diag (K : Type) [Fintype K] :
    Filter.Tendsto (fun n : ℤ => fun _ : K => n) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨∑ k, |b k|, fun a ha k => ?_⟩
  exact (le_abs_self _).trans
    ((Finset.single_le_sum (fun k _ => abs_nonneg (b k)) (Finset.mem_univ k)).trans ha)

theorem mixedDiff_succ {L : Type} [DecidableEq L] (b : L → ℤ) (H : (L → ℤ) → ℤ) (r : ℕ) :
    mixedDiff (fun _ : Fin (r + 1) => b) H = diffStep b (mixedDiff (fun _ : Fin r => b) H) := by
  simp only [mixedDiff, List.ofFn_succ, List.foldr_cons]

theorem mixedDiff_diag {K : Type} [DecidableEq K] (h : (K → ℤ) → ℤ) (g : (Unit → ℤ) → ℤ)
    (hg : ∀ n : ℤ, g (fun _ => n) = h (fun _ => n)) (r : ℕ) (n : ℤ) :
    mixedDiff (fun _ : Fin r => fun _ : Unit => (1 : ℤ)) g (fun _ => n) =
      mixedDiff (fun _ : Fin r => fun _ : K => (1 : ℤ)) h (fun _ => n) := by
  induction r generalizing n with
  | zero => simpa [mixedDiff] using hg n
  | succ r ih =>
    rw [mixedDiff_succ, mixedDiff_succ]
    have e1 : ∀ (L : Type), ((fun _ : L => n) - fun _ : L => (1 : ℤ)) = fun _ => n - 1 :=
      fun L => funext fun _ => rfl
    simp only [diffStep, e1, ih]

theorem pos_of_isEmpty {F : Type} [Field F] {K : Type} [Fintype K] [DecidableEq K] [IsEmpty K]
    {ι : K → Type} [∀ k, Fintype (ι k)] (q : Ideal (MRing ι F)) (e : ℕ) (hq : IsMultiProjPrime q)
    (hd : ringKrullDim (MRing ι F ⧸ q) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞)) :
    0 < intNum F q (fun _ : Fin e => fun _ : K => (1 : ℤ)) := by
  have hle := (ringKrullDim_quotient_le q).trans_eq
    (MvPolynomial.ringKrullDim_of_isNoetherianRing (R := F) (ι := Σ k, ι k))
  rw [hd, ringKrullDim_eq_zero_of_field, zero_add, Nat.card_of_isEmpty, Fintype.card_eq_zero,
    add_zero] at hle
  have he : e = 0 := by exact_mod_cast (nonpos_iff_eq_zero.mp (by exact_mod_cast hle) : (e : ℕ∞) = 0)
  subst he
  have hrel : FieldNumbers.relDim q = ((0 : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq q (0 + Fintype.card K) hd]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  obtain ⟨hA, -⟩ := FieldNumbers.MixedDiffConst.full F K ι q hq.multiHomog hq.relevant 0 hrel
  obtain ⟨m, hm⟩ := (hA (fun _ : Fin 0 => fun _ : K => (1 : ℤ))).exists
  rw [← hm]
  have hm0 : mixedDiff (fun _ : Fin 0 => fun _ : K => (1 : ℤ)) (hilbFn q) m = hilbFn q m := rfl
  rw [hm0]
  obtain ⟨hfin, hval⟩ := FieldNumbers.GradedFinite.full F K ι q (fun _ => 0)
  have hmm : m = fun k => ((fun _ : K => (0 : ℕ)) k : ℤ) := funext fun k => isEmptyElim k
  rw [hmm, hval]
  have hne : (⟨Ideal.Quotient.mkₐ F q 1, Submodule.mem_map_of_mem
      (mem_weightedHomogeneousSubmodule F _ _ _ |>.mpr (isWeightedHomogeneous_one F _))⟩ :
        gradedPiece q (fun _ : K => 0)) ≠ 0 := by
    intro h0
    have h1 := congrArg Subtype.val h0
    simp only [Submodule.coe_zero, map_one] at h1
    exact hq.isPrime.ne_top (Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using h1) |>
      (Ideal.eq_top_iff_one q).mpr)
  exact_mod_cast Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hne⟩

end MultiDegreePositive

theorem MultiDegreePositive.proof (hPrime : SegrePrime.Statement) (hHilb : SegreHilb.Statement)
    (hDim : SegreDimGe.Statement) : MultiDegreePositive.Statement := by
  intro F _ K _ _ ι _ q e hq hd
  rcases isEmpty_or_nonempty K with hK | hK
  · exact MultiDegreePositive.pos_of_isEmpty q e hq hd

  have hq' := hPrime F K ι q hq
  have hge := hDim F K ι q e hq hd
  have hle := (ringKrullDim_quotient_le (segrePrime F q)).trans_eq
    (MvPolynomial.ringKrullDim_of_isNoetherianRing (R := F)
      (ι := Σ _ : Unit, ∀ k, ι k))
  rw [ringKrullDim_eq_zero_of_field, zero_add] at hle

  obtain ⟨D, hD, heD⟩ : ∃ D : ℕ, ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸
      segrePrime F q) = ((D + 1 : ℕ) : WithBot ℕ∞) ∧ e ≤ D := by
    generalize ringKrullDim (MRing (fun _ : Unit => ∀ k, ι k) F ⧸ segrePrime F q) = x at hge hle ⊢
    induction x using WithBot.recBotCoe with
    | bot => exact absurd hge (by simp)
    | coe x =>
      induction x using ENat.recTopCoe with
      | top =>
        have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((Nat.card (Σ _ : Unit, ∀ k, ι k) : ℕ∞) : WithBot ℕ∞) := hle
        exact absurd (WithBot.coe_le_coe.mp h') (not_le.mpr (ENat.natCast_lt_top _))
      | coe m =>
        have hm : e + 1 ≤ m := by exact_mod_cast hge
        exact ⟨m - 1, by rw [Nat.sub_add_cancel (by omega)]; rfl, by omega⟩
  have hrel : FieldNumbers.relDim q = ((e : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq q (e + Fintype.card K) hd]
    simp only [Nat.cast_add, add_sub_cancel_right]
    rfl
  have hrel' : FieldNumbers.relDim (segrePrime F q) = ((D : ℕ) : WithBot (WithTop ℤ)) := by
    rw [FieldNumbers.relDim_of_ringKrullDim_eq (segrePrime F q) (D + 1) hD]
    simp only [Fintype.card_unit, Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
    rfl
  obtain ⟨hA, hB⟩ := FieldNumbers.MixedDiffConst.full F K ι q hq.multiHomog hq.relevant e hrel
  obtain ⟨hA', -⟩ := FieldNumbers.MixedDiffConst.full F Unit (fun _ => ∀ k, ι k) (segrePrime F q)
    hq'.multiHomog hq'.relevant D hrel'
  have hpos := DegreePositive.proof F (∀ k, ι k) (segrePrime F q) D hq' hD
  have hdiag := MultiDegreePositive.mixedDiff_diag (hilbFn q) (hilbFn (segrePrime F q))
    (fun n => hHilb F K ι q n)
  have hA'd := (MultiDegreePositive.tendsto_diag Unit).eventually
    (hA' (fun _ : Fin D => fun _ : Unit => (1 : ℤ)))

  have hDe : D = e := by
    by_contra hne
    have hBd := (MultiDegreePositive.tendsto_diag K).eventually
      (hB D (by omega) (fun _ : Fin D => fun _ : K => (1 : ℤ)))
    obtain ⟨n, h1, h2⟩ := (hA'd.and hBd).exists
    rw [hdiag] at h1
    omega
  subst hDe
  have hAd := (MultiDegreePositive.tendsto_diag K).eventually
    (hA (fun _ : Fin D => fun _ : K => (1 : ℤ)))
  obtain ⟨n, h1, h2⟩ := (hA'd.and hAd).exists
  rw [hdiag] at h1
  omega

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNmSectionsRational
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

namespace NmSectionsRationalProof

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_mul_prod_zpow (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) {d : K → ℕ} {g : MRing ι}
    (hg : IsMultiHomog g d) :
    aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) = aeval (fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) g := by
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  rw [map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
  have hsub : ∀ f : (Σ k, ι k) → Ω, ∏ p ∈ m.support, f p ^ m p = ∏ p, f p ^ m p := fun f =>
    Finset.prod_subset (Finset.subset_univ _) (fun p _ hp => by simp [Finsupp.notMem_support_iff.mp hp])
  have hden : ∏ p, y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ d k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, y ⟨k, c k⟩ ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  simp only [hsub, div_pow, Finset.prod_div_distrib, hden, zpow_neg, zpow_natCast, Finset.prod_inv_distrib]
  ring

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem chartRingZ_le [CharZero Ω] (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) :
    (chartRingZ y c : Set Ω) ⊆
      Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩) := by
  intro x hx
  have hle : chartRingZ y c ≤
      (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)).restrictScalars ℤ :=
    Algebra.adjoin_le Algebra.subset_adjoin
  exact hle hx

theorem isFractionRing_chart [CharZero Ω] (y : (Σ k, ι k) → Ω) (hbir : Birational y) (c : ∀ k, ι k)
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    IsFractionRing (Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)) Ω := by
  set A := Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
  have hmem : ∀ {d : K → ℕ} {g : MRing ι}, IsMultiHomog g d →
      aeval y g * ∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ)) ∈ A := by
    intro d g hg
    rw [aeval_mul_prod_zpow y c hg]
    refine chartRingZ_le y c ?_
    rw [chartRingZ, Algebra.adjoin_range_eq_range_aeval]
    exact ⟨g, rfl⟩
  refine IsFractionRing.of_field A Ω fun z => ?_
  obtain ⟨d, g, h, hg, hh, hh0, hgh⟩ := hbir z
  have hP : (∏ k, y ⟨k, c k⟩ ^ (-(d k : ℤ))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hc k)
  refine ⟨⟨_, hmem hg⟩, ⟨_, hmem hh⟩, ?_⟩
  change z = aeval y g * _ / (aeval y h * _)
  rw [hgh, mul_assoc, mul_div_assoc, div_self (mul_ne_zero hh0 hP), mul_one]

theorem exists_nat_mul_mem_adjoin_int [CharZero Ω] {S : Set Ω} {x : Ω} (hx : x ∈ Algebra.adjoin ℚ S) :
    ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * x ∈ Algebra.adjoin ℤ S := by
  have hnat : ∀ (n : ℕ) {z : Ω}, z ∈ Algebra.adjoin ℤ S → (n : Ω) * z ∈ Algebra.adjoin ℤ S :=
    fun n z hz => Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ n) hz
  induction hx using Algebra.adjoin_induction with
  | mem z hz => exact ⟨1, le_rfl, by simpa using Algebra.subset_adjoin hz⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_pos, ?_⟩
    have hq : (q.den : Ω) * algebraMap ℚ Ω q = (q.num : Ω) := by
      rw [eq_ratCast, Rat.cast_def, mul_div_cancel₀ _ (by exact_mod_cast q.den_ne_zero)]
    rw [hq]
    exact Subalgebra.intCast_mem _ _
  | add u v _ _ hu hv =>
    obtain ⟨n₁, h₁, hu⟩ := hu
    obtain ⟨n₂, h₂, hv⟩ := hv
    refine ⟨n₁ * n₂, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    have : ((n₁ * n₂ : ℕ) : Ω) * (u + v) = (n₂ : Ω) * ((n₁ : Ω) * u) + (n₁ : Ω) * ((n₂ : Ω) * v) := by
      push_cast; ring
    rw [this]
    exact add_mem (hnat _ hu) (hnat _ hv)
  | mul u v _ _ hu hv =>
    obtain ⟨n₁, h₁, hu⟩ := hu
    obtain ⟨n₂, h₂, hv⟩ := hv
    refine ⟨n₁ * n₂, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), ?_⟩
    have : ((n₁ * n₂ : ℕ) : Ω) * (u * v) = ((n₁ : Ω) * u) * ((n₂ : Ω) * v) := by
      push_cast; ring
    rw [this]
    exact Subalgebra.mul_mem _ hu hv

theorem exists_nat_mul_mem_chartRingZ [CharZero Ω] (y : (Σ k, ι k) → Ω) (hbir : Birational y)
    (hnorm : KH.NormalGenericFibre y) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) {x : Ω}
    (hx : x ∈ integralClosure (chartRingZ y c) Ω) :
    ∃ n : ℕ, 1 ≤ n ∧ (n : Ω) * x ∈ chartRingZ y c := by
  set A := Algebra.adjoin ℚ (Set.range fun p : Σ k, ι k => y p / y ⟨p.1, c p.1⟩)
  have := isFractionRing_chart y hbir c hc
  have : IsIntegrallyClosed A := hnorm c hc
  let φ : chartRingZ y c →+* A := (Subring.inclusion fun z hz => chartRingZ_le y c hz :
    (chartRingZ y c).toSubring →+* A.toSubring)
  have hxA : IsIntegral A x :=
    IsIntegral.map_of_comp_eq φ (RingHom.id Ω) (by ext; rfl) (hx : IsIntegral _ x)
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (K := Ω)).mp hxA
  have hxm : x ∈ A := hz ▸ z.2
  exact exists_nat_mul_mem_adjoin_int hxm

end NmSectionsRationalProof

open NmSectionsRationalProof in

theorem NmSectionsRational.proof (h : KH.SecEqStatement) : NmSectionsRational.Statement := by
  intro K _ ι _ Ω _ _ y a ha hy hbir hnorm
  obtain ⟨τ₀, hτ₀⟩ := h K ι Ω y a ha hy
  refine ⟨τ₀, fun τ hτ s hs => ?_⟩
  classical
  have hchart : ∀ c : ∀ k, ι k, ∃ m : ℕ, 1 ≤ m ∧ ((∀ k, y ⟨k, c k⟩ ≠ 0) →
      (m : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ)))) ∈ chartRingZ y c) := by
    intro c
    by_cases hc : ∀ k, y ⟨k, c k⟩ ≠ 0
    · obtain ⟨m, hm, hmem⟩ := exists_nat_mul_mem_chartRingZ y hbir hnorm c hc (hs c hc)
      exact ⟨m, hm, fun _ => hmem⟩
    · exact ⟨1, le_rfl, fun h' => absurd h' hc⟩
  choose m hm1 hm using hchart
  refine ⟨∏ c, m c, Nat.one_le_iff_ne_zero.mpr (Finset.prod_pos fun c _ => hm1 c).ne', ?_⟩
  rw [← hτ₀ τ hτ]
  intro c hc
  have hsplit : (∏ c', m c' : ℕ) = (∏ c' ∈ Finset.univ.erase c, m c') * m c :=
    (Finset.prod_erase_mul _ _ (Finset.mem_univ c)).symm
  have hval : ((∏ c', m c' : ℕ) : Ω) * s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ))) =
      ((∏ c' ∈ Finset.univ.erase c, m c' : ℕ) : Ω) *
        ((m c : Ω) * (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * (a k : ℤ))))) := by
    rw [hsplit]; push_cast; ring
  rw [hval]
  exact Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ _) (hm c hc)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNonvanishingDense
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

theorem NonvanishingDense.aeval_map_rat {σ : Type} (z : σ → ℂ) (g : MvPolynomial σ ℤ) :
    aeval z (map (Int.castRingHom ℚ) g) = eval z (map (Int.castRingHom ℂ) g) := by
  rw [aeval_def, eval₂_map, eval_map]
  congr 1

theorem NonvanishingDense.proof (h : RatPrimeDense.Statement) : NonvanishingDense.Statement := by
  intro K _ ι _ P d f hP hf z hz
  obtain ⟨_, ⟨hprime, -, -⟩, hhor, -⟩ := hP
  let _ : Algebra (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) := algebraMvPolynomial
  have hφ : ∀ g, algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ) g =
      map (Int.castRingHom ℚ) g := fun g => by
    change map (algebraMap ℤ ℚ) g = _
    congr 1
  have hdisj : Disjoint ((nonZeroDivisors ℤ).map (C (σ := Σ k, ι k)) : Set (MRing ι)) ↑P := by
    rw [Set.disjoint_left]
    rintro _ ⟨n, hn, rfl⟩ hnP
    have : n ∈ P.comap (C : ℤ →+* MRing ι) := hnP
    rw [hhor, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hn this
  set Pq := Ideal.map (algebraMap (MvPolynomial (Σ k, ι k) ℤ) (MvPolynomial (Σ k, ι k) ℚ)) P
  have hPq : Pq.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint ((nonZeroDivisors ℤ).map C) _ P hprime hdisj
  have hunder : Pq.comap (algebraMap _ _) = P :=
    IsLocalization.under_map_of_isPrime_disjoint ((nonZeroDivisors ℤ).map C) _ hprime hdisj
  have hfq : map (Int.castRingHom ℚ) f ∉ Pq := fun h' => hf (by
    rw [← hunder, Ideal.mem_comap, hφ]; exact h')

  have hzero : ∀ w : (Σ k, ι k) → ℂ, (∀ g ∈ P, eval w (map (Int.castRingHom ℂ) g) = 0) →
      ∀ g ∈ Pq, aeval w g = 0 := by
    intro w hw g hg
    have hle : Pq ≤ RingHom.ker (aeval w : MvPolynomial (Σ k, ι k) ℚ →ₐ[ℚ] ℂ).toRingHom := by
      refine Ideal.map_le_iff_le_comap.mpr fun g' hg' => ?_
      rw [Ideal.mem_comap, RingHom.mem_ker, hφ]
      change aeval w (map (Int.castRingHom ℚ) g') = 0
      rw [NonvanishingDense.aeval_map_rat]
      exact hw g' hg'
    exact hle hg
  have hz' : z ∈ closure {w : (Σ k, ι k) → ℂ | (∀ g ∈ Pq, aeval w g = 0) ∧
      aeval w (map (Int.castRingHom ℚ) f) ≠ 0} := h _ Pq _ hPq hfq (hzero z hz.2)
  have hU : IsOpen {w : (Σ k, ι k) → ℂ | ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0} := by
    simp only [Set.ofPred_forall, Set.ofPred_exists]
    exact isOpen_iInter_of_finite fun k => isOpen_iUnion fun i =>
      isOpen_ne_fun (continuous_apply _) continuous_const
  refine closure_mono ?_ (hU.inter_closure ⟨hz.1, hz'⟩)
  rintro w ⟨hwU, hwP, hwf⟩
  refine ⟨⟨hwU, fun g hg => ?_⟩, ?_⟩
  · rw [← NonvanishingDense.aeval_map_rat, ← hφ]
    exact hwP _ (Ideal.mem_map_of_mem _ hg)
  · rwa [← NonvanishingDense.aeval_map_rat]

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPointHeightFS
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

namespace PointHeightFSAux

abbrev fsOne : HermLine (GlobalTheory (Fin 1)) := HermLine.ofCone (fsMetric (Ix (Fin 1)))

abbrev x0 : MRing (GlobalTheory (Fin 1)) := X ⟨(), 0⟩

theorem isSmoothHerm_fsOne : IsSmoothHerm fsOne := by
  refine (ProjLine.isSmoothMetric_fs (J := Ix (Fin 1))).mono fun z hz h0 => ?_
  obtain ⟨i, hi⟩ := hz ()
  exact hi (congrFun h0 _)

theorem divisorSupport_coordinate_point : divSupp (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) x0 = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun W hW => ?_
  obtain ⟨i, hi⟩ := hW.2 ()
  have hle := hW.1.1.2
  have hi0 : i = 0 := Subsingleton.elim _ _
  subst hi0
  exact hi (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))

theorem logNorm_coordinate_point : logNorm fsOne x0 = fun _ => 0 := by
  funext z
  have hρ : fsOne.h z = ‖z ⟨(), 0⟩‖ := by
    let _ : Unique (Ix (Fin 1)) :=
      ⟨⟨⟨(), 0⟩⟩, fun p => by rcases p with ⟨⟨⟩, i⟩; rw [Subsingleton.elim i 0]; rfl⟩
    show ‖WithLp.toLp 2 z‖ = _
    rw [EuclideanSpace.norm_eq, Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]
    rfl
  simp only [logNorm, hρ, map_X, eval_X]
  rcases eq_or_ne (z ⟨(), 0⟩) 0 with h | h
  · simp [h]
  · rw [div_self (norm_ne_zero_iff.mpr h), Real.log_one]

theorem ptsIntegral_zero {e : ℕ} (P : Ideal (MRing (GlobalTheory (Fin 1))))
    (φ : Fin e → (Ix (Fin 1) → ℂ) → ℝ) : ptsIntegral P φ (fun _ => 0) = 0 := by
  classical
  unfold ptsIntegral
  split_ifs
  · simp [ptsIntegralAt, sheetDensity]
  · rfl

end PointHeightFSAux

open PointHeightFSAux in

theorem PointHeightFS.proof : PointHeightFS.Statement := by
  intro I hI
  classical
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) (0 + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot 0
  have hs : IsMultiHomog x0 fun _ => 1 := IndefiniteRowSideFullHecke.Inter.isMultiHomog_Xb 1 0
  have hx0 : x0 ∉ (⊥ : Ideal (MRing (GlobalTheory (Fin 1)))) := by
    rw [Ideal.mem_bot]
    exact X_ne_zero _
  have hR := (hI Unit (GlobalTheory (Fin 1))).2.2 ⊥ 0 Fin.elim0 fsOne x0 (fun _ => 1) hP (fun j => j.elim0)
    isSmoothHerm_fsOne (fun _ => rfl) hs hx0
  have hL : (Fin.snoc (Fin.elim0 : Fin 0 → HermLine (GlobalTheory (Fin 1))) fsOne : Fin 1 → _) =
      fun _ => fsOne := by
    funext j
    fin_cases j
    rfl
  rw [hL] at hR
  unfold hhOf
  rw [hR, recR, divisorSupport_coordinate_point, finsum_mem_empty, zero_sub, arInt, logNorm_coordinate_point, ptsIntegral_zero, neg_zero]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsGeneratedPow
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

def GeneratedPow.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type) [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] (V : Ideal (MRingOver S ι)) (n : K → ℤ) (t : ℕ),
    KH.GeneratedV S V n → KH.GeneratedV S V (t • n)

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

