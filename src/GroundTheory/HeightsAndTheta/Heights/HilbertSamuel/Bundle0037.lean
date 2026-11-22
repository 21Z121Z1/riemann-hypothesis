import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSecondVeroneseParts
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PReductionToProjective
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

namespace ReductionToProjective

theorem powLog_shift_le (D : ℕ) {n j : ℕ} (hj : j ≤ n) :
    ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1) ≤
      2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
  have h1 := powLog_mono D (show n + j ≤ 2 * n by omega)
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h2 : 2 * Real.log ((n : ℝ) + 1) = Real.log (((n : ℝ) + 1) ^ 2) := by
    rw [Real.log_pow]; push_cast; ring
  have hlog : Real.log (((2 * n : ℕ) : ℝ) + 1) ≤ 2 * Real.log ((n : ℝ) + 1) := by
    rw [h2]
    exact Real.log_le_log (by positivity) (by push_cast; nlinarith)
  have hp : ((2 * n : ℕ) : ℝ) ^ D = 2 ^ D * (n : ℝ) ^ D := by push_cast; rw [mul_pow]
  calc ((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)
      ≤ ((2 * n : ℕ) : ℝ) ^ D * Real.log (((2 * n : ℕ) : ℝ) + 1) := h1
    _ ≤ ((2 * n : ℕ) : ℝ) ^ D * (2 * Real.log ((n : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by rw [hp]; ring

theorem sub_chiP_isBigO (D k : ℕ) (δ C : ℝ) (hδ : 0 ≤ δ) (chi : ℕ → ℝ)
    (hlo : ∀ n : ℕ, k + 1 ≤ n → δ * chiP D (n - k) - C * (n : ℝ) ^ D * Real.log (n + 1) ≤ chi n)
    (hhi : ∀ n : ℕ, k + 1 ≤ n → chi n ≤ δ * chiP D (n + k) + C * (n : ℝ) ^ D * Real.log (n + 1)) :
    (fun n => chi n - δ * chiP D n) =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  obtain ⟨C', hC'⟩ := exists_chiP_succ_sub_le D
  refine IsBigO.of_bound (δ * (k * (|C'| * 2 ^ (D + 1))) + |C|) ?_
  filter_upwards [eventually_ge_atTop (k + 1)] with n hn
  have hP0 : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := powLog_nonneg D n
  have hCP : C * (n : ℝ) ^ D * Real.log (n + 1) ≤ |C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    rw [mul_assoc]; exact mul_le_mul_of_nonneg_right (le_abs_self C) hP0
  have hCP' : -(|C| * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := by
    rw [mul_assoc, ← neg_mul]; exact mul_le_mul_of_nonneg_right (neg_abs_le C) hP0
  have h2 : (1 : ℝ) ≤ 2 ^ (D + 1) := one_le_pow₀ (by norm_num)

  have hup : chiP D (n + k) - chiP D n ≤ k * (|C'| * 2 ^ (D + 1)) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    refine (chiP_add_sub_le D C' hC' k n (by omega)).trans ?_
    calc ∑ j ∈ Finset.range k, |C'| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range k, |C'| * (2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg C')
          exact powLog_shift_le D (by have := Finset.mem_range.1 hj; omega)
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

  have hdn : chiP D n - chiP D (n - k) ≤ k * (|C'| * 2 ^ (D + 1)) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by
    have h := chiP_add_sub_le D C' hC' k (n - k) (by omega)
    rw [Nat.sub_add_cancel (by omega : k ≤ n)] at h
    refine h.trans ?_
    calc ∑ j ∈ Finset.range k, |C'| * (((n - k + j : ℕ) : ℝ) ^ D * Real.log (((n - k + j : ℕ) : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range k, |C'| * (2 ^ (D + 1) * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))) := by
          refine Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_left ?_ (abs_nonneg C')
          have hj' := Finset.mem_range.1 hj
          refine (powLog_mono D (show n - k + j ≤ n by omega)).trans ?_
          exact le_mul_of_one_le_left hP0 h2
      _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hlo' := hlo n hn
  have hhi' := hhi n hn
  have hu := mul_le_mul_of_nonneg_left hup hδ
  have hd := mul_le_mul_of_nonneg_left hdn hδ
  rw [Real.norm_eq_abs, Real.norm_of_nonneg hP0, abs_le]
  constructor
  · nlinarith
  · nlinarith

theorem defect_pullFS (hPB : ProjectionBounds.Statement) (hTop : TopPullFS.Statement) {D : ℕ} {Ω : Type}
    [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ] (I : AllFam) (hI : I.IsFamily) (d : HSMDatum D Ω κ)
    (e : Fin (D + 1) → Ix κ) (hfr : IsProjFrame d.x e) (hFS : IsPullFS d.x e d.m) :
    (fun n => hsDefect D (resChi d) (top I d.x d.m D) n -
        (projDeg d.x e : ℝ) * hsDefect D (chiP D) (hhOf I D) n)
      =O[atTop] fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  obtain ⟨k, E, C, -, -, -, -, -, -, -, hs⟩ := hPB D Ω κ d e hfr hFS
  have ht := hTop D Ω κ I d.x d.m e hI d.arith d.smooth hfr hFS
  refine (sub_chiP_isBigO D k (projDeg d.x e) C (Nat.cast_nonneg _) (resChi d) (fun n hn => (hs n hn).1)
    (fun n hn => (hs n hn).2)).congr_left fun n => ?_
  simp only [hsDefect, ht]
  ring

theorem isLittleO_pow_pw (D : ℕ) : (fun n : ℕ => (n : ℝ) ^ D) =o[atTop] pw D :=
  (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) (Nat.lt_succ_self D)).comp_tendsto tendsto_natCast_atTop_atTop

theorem proof (hPB : ProjectionBounds.Statement) (hCL : ChangeOfLattice.Statement)
    (hTop : TopPullFS.Statement) (hDeg : ProjDegGenDeg.Statement) (hInv : GenDegMatAct.Statement)
    (hFC : FrameChange.Statement) (hMF : MetricToFS.Statement) : ReductionToProjective.Statement := by
  intro D Ω _ _ κ _ I d hI
  refine ⟨fun e hfr hFS => defect_pullFS hPB hTop I hI d e hfr hFS, ?_⟩
  obtain ⟨B, d', e, hB, hx', hm', hfr', hidx⟩ := hFC D Ω κ d
  obtain ⟨d₀, hx₀, hFS₀, hmet⟩ := hMF D Ω κ I d' e hI hfr'
  have hfr₀ : IsProjFrame d₀.x e := hx₀ ▸ hfr'
  have hFS₀' : IsPullFS d₀.x e d₀.m := hx₀ ▸ hFS₀
  have h1 := (defect_pullFS hPB hTop I hI d₀ e hfr₀ hFS₀').trans_isLittleO (isLittleO_pow_mul_log D)
  rw [hx₀] at h1
  have h2 := (hCL D Ω κ I d.x B d.m d'.m hI d.arith d.indep hB d.smooth hm').trans_isLittleO
    (isLittleO_pow_pw D)
  rw [← hx'] at h2
  have hg : (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ) = (projDeg d'.x e : ℝ) := by
    have hd := hDeg D Ω κ d'.x e d'.arith hfr'
    have hi := hInv D Ω κ d.x B hB
    rw [← hx', hd] at hi
    rw [← hi]
    push_cast
    rfl
  rw [hg]
  refine ((h1.sub hmet).sub (hidx.add h2)).congr_left fun n => ?_
  simp only [hsDefect]
  ring

end ReductionToProjective

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PResChiSymMeasure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace ResChiSymMeasure

variable {κ : Type} [Fintype κ]

theorem eval_smul_of_homog {J R : Type*} [Fintype J] [CommRing R] {φ : MvPolynomial J R} {d : ℕ}
    (hφ : φ.IsHomogeneous d) (c : R) (z : J → R) : eval (c • z) φ = c ^ d * eval z φ := by
  classical
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have := hφ (mem_support_iff.mp hm)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

theorem evalQ_smul {b : MvPolynomial (Ix κ) ℚ} {n : ℕ}
    (hb : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f) (c : ℂ)
    (z : Ix κ → ℂ) :
    eval (c • z) (map (algebraMap ℚ ℂ) b) = c ^ n * eval z (map (algebraMap ℚ ℂ) b) := by
  obtain ⟨f, hf, rfl⟩ := hb
  exact eval_smul_of_homog ((hf.map _).map _) c z

omit [Fintype κ] in

theorem continuous_evalQ (b : MvPolynomial (Ix κ) ℚ) :
    Continuous fun z : Ix κ → ℂ => eval z (map (algebraMap ℚ ℂ) b) :=
  (map (algebraMap ℚ ℂ) b).continuous_eval

theorem pairVal_bound {m : ConeMetric ℂ (Ix κ)} (hm : IsSmoothMetric m) {n : ℕ} {b b' : MvPolynomial (Ix κ) ℚ}
    (hb : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b = map (Int.castRingHom ℚ) f)
    (hb' : ∃ f : MvPolynomial (Ix κ) ℤ, f.IsHomogeneous n ∧ b' = map (Int.castRingHom ℚ) f) :
    Measurable (pairVal m n b b') ∧ ∃ C : ℝ, ∀ z, ‖pairVal m n b b' z‖ ≤ C := by
  set h := pairVal m n b b' with hh
  have hρ : ContinuousOn m.ρ {0}ᶜ := hm.continuousOn
  have hcont : ContinuousOn h {0}ᶜ := by
    refine (((continuous_evalQ b).continuousOn.mul (continuous_evalQ b').continuousOn.star).div
      (Complex.continuous_ofReal.comp_continuousOn (hρ.pow _)) fun z hz => ?_)
    exact Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (m.pos z hz).ne')
  have hnorm : ∀ z, ‖h z‖ = ‖eval z (map (algebraMap ℚ ℂ) b)‖ * ‖eval z (map (algebraMap ℚ ℂ) b')‖ / m.ρ z ^ (2 * n) := by
    intro z
    simp only [hh, pairVal, norm_div, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (pow_nonneg (m.nonneg z) _)]
  have hsm : ∀ (c : ℂ) (z : Ix κ → ℂ), c ≠ 0 → ‖h (c • z)‖ = ‖h z‖ := by
    intro c z hc
    rw [hnorm, hnorm, evalQ_smul hb, evalQ_smul hb', m.smul]
    have hc' : 0 < ‖c‖ := norm_pos_iff.mpr hc
    rw [norm_mul, norm_mul, norm_pow, mul_pow]
    have e : ‖c‖ ^ n * ‖c‖ ^ n = ‖c‖ ^ (2 * n) := by rw [← pow_add, ← two_mul]
    rw [show ‖c‖ ^ n * ‖eval z (map (algebraMap ℚ ℂ) b)‖ * (‖c‖ ^ n * ‖eval z (map (algebraMap ℚ ℂ) b')‖) =
      (‖c‖ ^ n * ‖c‖ ^ n) * (‖eval z (map (algebraMap ℚ ℂ) b)‖ * ‖eval z (map (algebraMap ℚ ℂ) b')‖) by ring, e,
      mul_div_mul_left _ _ (pow_ne_zero _ hc'.ne')]
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : Ix κ → ℂ) 1).exists_bound_of_continuousOn
    (hcont.mono fun z hz => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      rintro rfl
      simp at hz)
  refine ⟨measurable_of_continuousOn_compl_singleton 0 hcont, max C ‖h 0‖, fun z => ?_⟩
  by_cases hz : z = 0
  · rw [hz]; exact le_max_right _ _
  · have hz' : (‖z‖ : ℂ) ≠ 0 := by simpa using hz
    have hu : ((‖z‖ : ℂ)⁻¹ • z) ∈ Metric.sphere (0 : Ix κ → ℂ) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
    have : z = (‖z‖ : ℂ) • ((‖z‖ : ℂ)⁻¹ • z) := by rw [smul_smul, mul_inv_cancel₀ hz', one_smul]
    rw [this, hsm _ _ hz']
    exact (hC _ hu).trans (le_max_left _ _)

theorem measurable_conjPt : Measurable (conjPt : (Ix κ → ℂ) → Ix κ → ℂ) :=
  (continuous_pi fun i => Complex.continuous_conj.comp (continuous_apply i)).measurable

end ResChiSymMeasure

open ResChiSymMeasure in

theorem ResChiSymMeasure.full : ResChiSymMeasure.Statement := by
  intro D Ω _ _ κ _ d hf n
  have : IsProbabilityMeasure d.dV := d.vol.1
  have hmult : ∀ w : NumberField.InfinitePlace ℚ, (w.mult : ℝ) = 1 := by
    intro w
    have h1 := NumberField.totalWeight_eq_sum_mult ℚ
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self, Fintype.sum_unique] at h1
    rw [Subsingleton.elim w default, ← h1, Nat.cast_one]
  have hemb : ∀ w : NumberField.InfinitePlace ℚ, w.embedding = algebraMap ℚ ℂ :=
    fun w => Subsingleton.elim _ _
  have hw : (Height.totalWeight ℚ : ℝ) = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self, Nat.cast_one]
  have hg : Measurable (conjPt ∘ resPt d) := measurable_conjPt.comp hf
  unfold resChi chi
  by_cases h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Ix κ) ℚ), IsSecBasis d.x n p.2
  swap
  · rw [dif_neg h, dif_neg h]
  rw [dif_pos h, dif_pos h]
  have hp := h.choose_spec
  generalize h.choose = p at hp ⊢
  obtain ⟨r, b⟩ := p
  have hp' : IsSecBasis d.x n b := hp
  have hG : resGram d n b = realGram (K := ℚ) (fun _ => d.m)
      (fun _ => IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (resPt d) d.dV) n b := by
    ext k l
    obtain ⟨hmeas, C, hC⟩ := pairVal_bound d.smooth (hp'.1 k) (hp'.1 l)
    have hint : ∀ φ : d.R.X → Ix κ → ℂ, Measurable φ →
        Integrable (pairVal d.m n (b k) (b l)) (d.dV.map φ) := fun φ _ =>
      Integrable.of_bound hmeas.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
    simp only [realGram, hmult, hemb, one_mul, Fintype.sum_unique]
    change _ = (∫ z, pairVal d.m n (b k) (b l) z ∂IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure (resPt d) d.dV).re
    rw [IndefiniteRowSideFullHecke.HilbertSamuel.symMeasure, integral_smul_measure,
      integral_add_measure (hint _ hf) (hint _ hg), integral_map hf.aemeasurable hmeas.aestronglyMeasurable,
      integral_map hg.aemeasurable hmeas.aestronglyMeasurable]
    simp only [resGram, Function.comp_apply, ENNReal.toReal_inv, ENNReal.toReal_ofNat, Complex.real_smul,
      Complex.mul_re, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  rw [hG]
  simp only [l2Degree, hw, div_one]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSecondVeronese
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Veronese

theorem pair_eq {D : ℕ} {i j k l : Fin (D + 1)} (hij : i ≤ j) (hkl : k ≤ l)
    (h : (Finsupp.single i 1 + Finsupp.single j 1 : Fin (D + 1) →₀ ℕ) = Finsupp.single k 1 + Finsupp.single l 1) :
    i = k ∧ j = l := by
  have hm : ({i} + {j} : Multiset (Fin (D + 1))) = {k} + {l} := by
    have := congrArg Finsupp.toMultiset h
    simpa only [map_add, Finsupp.toMultiset_single, one_nsmul] using this
  have h1 : i = k ∨ i = l := by
    have : i ∈ ({k} + {l} : Multiset (Fin (D + 1))) := hm ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self i))
    simpa using this
  have h2 : j = k ∨ j = l := by
    have : j ∈ ({k} + {l} : Multiset (Fin (D + 1))) := hm ▸ Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self j))
    simpa using this
  have h3 : k = i ∨ k = j := by
    have : k ∈ ({i} + {j} : Multiset (Fin (D + 1))) := hm.symm ▸ Multiset.mem_add.2 (Or.inl (Multiset.mem_singleton_self k))
    simpa using this
  have h4 : l = i ∨ l = j := by
    have : l ∈ ({i} + {j} : Multiset (Fin (D + 1))) := hm.symm ▸ Multiset.mem_add.2 (Or.inr (Multiset.mem_singleton_self l))
    simpa using this
  rw [Fin.le_iff_val_le_val] at hij hkl
  simp only [Fin.ext_iff] at h1 h2 h3 h4 ⊢
  omega

theorem exponent_injective (D : ℕ) :
    Function.Injective fun q : Ix (Idx D) =>
      (Finsupp.single q.2.1.1 1 + Finsupp.single q.2.1.2 1 : Fin (D + 1) →₀ ℕ) := by
  intro q q' h
  obtain ⟨u, ⟨⟨i, j⟩, hij⟩⟩ := q
  obtain ⟨u', ⟨⟨k, l⟩, hkl⟩⟩ := q'
  obtain ⟨rfl, rfl⟩ := pair_eq hij hkl h
  cases u
  cases u'
  rfl

def polyMap (D : ℕ) : MvPolynomial (Fin (D + 1)) ℤ →+* Fld D :=
  (algebraMap (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)).comp (MvPolynomial.map (Int.castRingHom ℚ))

theorem polyMap_injective (D : ℕ) : Function.Injective (polyMap D) :=
  (IsFractionRing.injective (MvPolynomial (Fin (D + 1)) ℚ) (Fld D)).comp
    (MvPolynomial.map_injective _ (RingHom.injective_int (Int.castRingHom ℚ)))

theorem x_linearIndependent (D : ℕ) : LinearIndependent ℤ (x D) := by
  have hmono : LinearIndependent ℤ fun q : Ix (Idx D) =>
      (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ) := by
    have h := (basisMonomials (Fin (D + 1)) ℤ).linearIndependent.comp _ (exponent_injective D)
    have e : (fun q : Ix (Idx D) => (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ)) =
        ⇑(basisMonomials (Fin (D + 1)) ℤ) ∘ fun q : Ix (Idx D) =>
          (Finsupp.single q.2.1.1 1 + Finsupp.single q.2.1.2 1 : Fin (D + 1) →₀ ℕ) := by
      funext q
      simp only [Function.comp_apply, coe_basisMonomials, X, monomial_mul, mul_one]
    rw [e]
    exact h
  have h2 := hmono.map' (polyMap D).toAddMonoidHom.toIntLinearMap
    (LinearMap.ker_eq_bot.mpr (polyMap_injective D))
  have e2 : x D = ⇑(polyMap D).toAddMonoidHom.toIntLinearMap ∘ fun q : Ix (Idx D) =>
      (X q.2.1.1 * X q.2.1.2 : MvPolynomial (Fin (D + 1)) ℤ) := by
    funext q
    simp [x, t, polyMap, map_mul]
  rw [e2]
  exact h2

theorem isSmoothMetric_metric (D : ℕ) : IsSmoothMetric (metric D) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scale D) :=
    contDiff_pi.2 fun q => contDiff_const.mul (contDiff_apply ℝ ℂ q)
  exact (ProjLine.isSmoothMetric_fs (J := Ix (Idx D))).comp hs.contDiffOn fun z hz => scale_ne_zero hz

theorem isConjInvariant_metric (D : ℕ) : IsConjInvariant (metric D) := by
  intro z
  have h : scale D (fun q => conj (z q)) = fun q => conj (scale D z q) := by
    funext q
    simp [scale, map_mul, Complex.conj_ofReal]
  show (fsMetric (Ix (Idx D))).ρ (scale D _) = (fsMetric (Ix (Idx D))).ρ (scale D z)
  rw [h]
  exact ProjLine.isConjInvariant_fs (scale D z)

theorem eval_smul_homog {ι : Type*} {φ : MvPolynomial ι ℂ} {n : ℕ} (hφ : φ.IsHomogeneous n) (c : ℂ)
    (z : ι → ℂ) : eval (c • z) φ = c ^ n * eval z φ := by
  classical
  rw [eval_eq, eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : d.degree = n := by
    by_contra h
    exact (mem_support_iff.mp hd) (hφ.coeff_eq_zero h)
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hs : d.degree = ∑ i ∈ d.support, d i := rfl
  rw [← hdeg, hs]
  ring

theorem pairVal_smul {D n : ℕ} {b b' : MvPolynomial (Ix (Idx D)) ℚ}
    (hb : ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b = MvPolynomial.map (Int.castRingHom ℚ) f)
    (hb' : ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b' = MvPolynomial.map (Int.castRingHom ℚ) f)
    (c : ℂ) (z : Ix (Idx D) → ℂ) (hc : c ≠ 0) :
    pairVal (metric D) n b b' (c • z) = pairVal (metric D) n b b' z := by
  obtain ⟨f, hf, rfl⟩ := hb
  obtain ⟨f', hf', rfl⟩ := hb'
  unfold pairVal
  rw [eval_smul_homog ((hf.map _).map _), eval_smul_homog ((hf'.map _).map _), (metric D).smul]
  have key : c ^ n * conj (c ^ n) = (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) := by
    rw [map_pow, ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hK : (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc
    exact_mod_cast (pow_pos this _).ne'
  have hL : ∀ A B : ℂ, A * c ^ n * conj (B * c ^ n) = (((‖c‖ ^ (2 * n) : ℝ)) : ℂ) * (A * conj B) := by
    intro A B
    rw [← key, map_mul]
    ring
  rw [mul_comm (c ^ n), mul_comm (c ^ n), hL, mul_pow]
  push_cast
  exact mul_div_mul_left _ _ (by exact_mod_cast hK)

end Veronese

open Veronese

theorem SecondVeronese.proof (hA : VeroneseArith.Statement) (hS : VeroneseSemipos.Statement)
    (hR : VeroneseResolution.Statement) (hC : VeroneseChi.Statement) (hT : VeroneseTop.Statement)
    (hG : VeroneseGenDeg.Statement) : SecondVeronese.Statement := by
  intro D hD
  obtain ⟨J, R, meas, borel, dV, hvol, htr⟩ := hR D hD
  let d : HSMDatum D (Fld D) (Idx D) :=
    { x := x D, m := metric D, P0 := ⊥, J := J, R := R, meas := meas, borel := borel, dV := dV,
      one_le := hD, arith := hA D hD, indep := x_linearIndependent D, smooth := isSmoothMetric_metric D,
      conjInv := isConjInvariant_metric D, normalForm_baseLattice_le_dualSpan_sup_line := bot_le, semipos := hS D, vol := hvol }
  refine ⟨Fld D, inferInstance, inferInstance, Idx D, inferInstance, d, fun n => ?_,
    fun I hI => hT D hD I hI, hG D hD⟩

  have hgram : ∀ {r : ℕ} (b : Fin r → MvPolynomial (Ix (Idx D)) ℚ),
      (∀ k, ∃ f : MvPolynomial (Ix (Idx D)) ℤ, f.IsHomogeneous n ∧ b k = MvPolynomial.map (Int.castRingHom ℚ) f) →
      resGram d n b = gram D n b := by
    intro r b hb
    ext k l
    have e1 := htr (fun z => pairVal (metric D) n (b k) (b l) z)
      (fun c z hc => pairVal_smul (hb k) (hb l) c z hc)
    have e2 := htr (fun z => pairVal (metric D) n (b k) (b l) (conjPt z)) fun c z hc => by
      have : conjPt (c • z) = conj c • conjPt z := by
        funext q
        simp [conjPt]
      simp only [this]
      exact pairVal_smul (hb k) (hb l) _ _ ((map_ne_zero _).mpr hc)
    unfold resGram gram resPt
    rw [e1, e2]
  rw [← hC D hD n]
  unfold resChi Veronese.chi
  split_ifs with h1
  · rw [hgram _ h1.choose_spec.1]
  · rfl

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTheoremHSM
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics MeasureTheory

noncomputable section

variable {D : ℕ} {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem resolutionVolumeL2_le_sqrt_two_mul (d : HSMDatum D Ω κ) (n : ℕ) (f : MvPolynomial (Ix κ) ℤ) :
    resolutionVolumeL2 d n f ≤ Real.sqrt 2 * resolutionSectionL2Norm d n f := by
  unfold resolutionVolumeL2 resolutionSectionL2Norm
  rw [← Real.sqrt_mul (by norm_num)]
  apply Real.sqrt_le_sqrt
  have hb : 0 ≤ ∫ y, ptNorm d.m (Int.castRingHom ℂ) n f (conjPt (resPt d y)) ^ 2 ∂d.dV :=
    integral_nonneg fun y => sq_nonneg _
  linarith

theorem TheoremHSM.proof (h₁ : ReductionToProjective.Statement) (h₂ : HilbertSamuelProjective.Statement)
    (h₃ : ResolutionSupBound.Statement) : TheoremHSM.Statement := by
  intro D Ω _ _ κ _ I d hI
  refine ⟨?_, ?_⟩
  · have hA := (h₁ D Ω κ I d hI).2
    have hB := (h₂ D I hI).const_mul_left (genDeg (ι := GlobalTheory κ) (coordIdeal ℤ d.x) D 1 : ℝ)
    exact (hA.add hB).congr_left fun n => by ring
  · obtain ⟨C, hC⟩ := ResolutionSupBound.toInt h₃ D Ω κ d
    refine ⟨max C 0 * Real.sqrt 2, fun n hn f hf z hz => ?_⟩
    have hp : 0 ≤ (n : ℝ) ^ ((D : ℝ) / 2) := by positivity
    have hv : 0 ≤ resolutionVolumeL2 d n f := Real.sqrt_nonneg _
    calc ptNorm d.m (Int.castRingHom ℂ) n f z ≤ C * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2 d n f :=
          hC n hn f hf z hz
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionVolumeL2 d n f :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hp) hv
      _ ≤ max C 0 * (n : ℝ) ^ ((D : ℝ) / 2) * (Real.sqrt 2 * resolutionSectionL2Norm d n f) :=
          mul_le_mul_of_nonneg_left (resolutionVolumeL2_le_sqrt_two_mul d n f)
            (mul_nonneg (le_max_right _ _) hp)
      _ = max C 0 * Real.sqrt 2 * (n : ℝ) ^ ((D : ℝ) / 2) * resolutionSectionL2Norm d n f := by ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTheoremHSMBlock
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

theorem TheoremHSMBlock.proof (hR : ReductionToProjectiveBlock.Statement)
    (hP : HilbertSamuelProjective.Statement) (hS : SupBoundBlock.Statement) :
    TheoremHSMBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  refine ⟨?_, hS D K ι Ω d⟩
  have h1 := hR D K ι Ω I d hI
  have h2 := (hP D I hI).const_mul_left (genDeg (mCoordIdeal d.y) D d.A.a : ℝ)
  refine (h1.add h2).congr_left fun n => ?_
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

