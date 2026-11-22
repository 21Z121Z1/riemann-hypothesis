import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAlgClosedTiltFieldAndValuationRing
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0244
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0248
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0233
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0129
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0276
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisNormOfNonzero
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.GaussDefinite

theorem add_pow_split {R : Type} [CommRing R] (x p : R) (j m : ℕ) :
    ∃ u v : R, (x + p) ^ j = x ^ m * u + p ^ (j - m) * v := by
  induction j generalizing m with
  | zero => exact ⟨0, 1, by simp⟩
  | succ j ih =>
    rcases m with _ | m
    · exact ⟨(x + p) ^ (j + 1), 0, by simp⟩
    obtain ⟨u, v, h⟩ := ih m
    obtain ⟨u', v', h'⟩ := ih (m + 1)
    obtain ⟨d, hd⟩ : ∃ d, j - (m + 1) + 1 = j - m + d := ⟨j - (m + 1) + 1 - (j - m), by omega⟩
    refine ⟨u + p * u', x * v + p ^ d * v', ?_⟩
    rw [show j + 1 - (m + 1) = j - m by omega]
    have e : p * p ^ (j - (m + 1)) = p ^ (j - m) * p ^ d := by rw [← pow_add, ← hd, pow_succ']
    calc (x + p) ^ (j + 1) = x * (x + p) ^ j + p * (x + p) ^ j := by ring
      _ = x * (x ^ m * u + p ^ (j - m) * v) + p * (x ^ (m + 1) * u' + p ^ (j - (m + 1)) * v') := by
        rw [← h, ← h']
      _ = _ := by linear_combination v' * e

variable (l : ℕ) [hl : Fact l.Prime]

theorem exists_flat : ∃ x : Per.Fl l, x.untilt = (l : Per.OC l) := by
  have hr : ∀ a : Per.OC l, ∃ b : Per.OC l, b ^ l = a := by
    intro a
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (a : ℂ_[l]) hl.out.pos
    have h1 : ‖b‖ ^ l ≤ 1 := by rw [← norm_pow, hb]; exact (GlobalTheory.RingBasics.mem_OC _).1 a.2
    exact ⟨⟨b, (GlobalTheory.RingBasics.mem_OC _).2 ((pow_le_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h1)⟩,
      Subtype.ext hb⟩
  choose r hr using hr
  obtain ⟨e, he⟩ := zeta_exists_tilt (p := l) (O := Per.OC l) (fun n => r^[n] (l : Per.OC l)) (fun n => by
    rw [Function.iterate_succ_apply', hr])
  exact ⟨e, he 0⟩

theorem norm_l : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [GlobalTheory.RingBasics.norm_eq_val, PadicComplex.valuation_p]
  simp

theorem norm_root (x : Per.Fl l) (i : ℕ) :
    ‖((x.untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) =
      ‖(((((frobeniusEquiv (Per.Fl l) l).symm ^ i) x).untilt : Per.OC l) : ℂ_[l])‖ := by
  have h := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x i
  have e : ((frobeniusEquiv (Per.Fl l) l).symm ^ i) x = ((frobeniusEquiv (Per.Fl l) l).symm)^[i] x := by
    induction i with
    | zero => rfl
    | succ i ih => rw [pow_succ', Function.iterate_succ_apply', ← ih (PreTilt.untilt_iterate_frobeniusEquiv_symm_pow x i)]; rfl
  rw [← h, e]
  push_cast
  rw [norm_pow, one_div, ← Nat.cast_pow, Real.pow_rpow_inv_natCast (norm_nonneg _)
    (pow_ne_zero _ hl.out.ne_zero)]

theorem split_of_small (a : Per.Ainf l) (M m : ℕ)
    (h : ∀ i : ℕ, ‖(((a.coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) * ((l : ℝ)⁻¹) ^ i ≤
      ((l : ℝ)⁻¹) ^ M) :
    ∃ c : Per.Ainf l, a - (l : Per.Ainf l) ^ (M - m) * c ∈ RingHom.ker (Per.θ l) ^ m := by
  obtain ⟨w, hw⟩ := exists_flat l
  have hk : Per.tm w - (l : Per.Ainf l) ∈ RingHom.ker (Per.θ l) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, WittVector.fontaineTheta_teichmuller, hw, sub_self]
  have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by exact_mod_cast hl.out.pos)
  have key : ∀ i ∈ Finset.Iic M, ∃ c : Per.Ainf l,
      Per.tm (((frobeniusEquiv (Per.Fl l) l).symm ^ i) (a.coeff i)) * (l : Per.Ainf l) ^ i -
        (l : Per.Ainf l) ^ (M - m) * c ∈ RingHom.ker (Per.θ l) ^ m := by
    intro i hi
    rw [Finset.mem_Iic] at hi
    have h1 := h i
    rw [norm_root] at h1
    set y := ((frobeniusEquiv (Per.Fl l) l).symm ^ i) (a.coeff i)
    have h2 : ‖((y.untilt : Per.OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ ^ (M - i) := by
      rw [norm_l]
      refine le_of_mul_le_mul_right ?_ (pow_pos hl0 i)
      rwa [← pow_add, Nat.sub_add_cancel hi]
    rw [← GlobalTheory.RingBasics.mem_span_pow_OC, Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← hw,
      ← map_pow] at h2
    obtain ⟨z, hz⟩ := GlobalTheory.TiltAlgClosed.dvd_of_untilt_dvd h2
    obtain ⟨u, v, huv⟩ := add_pow_split (Per.tm w - (l : Per.Ainf l)) (l : Per.Ainf l) (M - i) m
    obtain ⟨d, hd⟩ : ∃ d, M - i - m + i = M - m + d := ⟨M - i - m + i - (M - m), by omega⟩
    have e : (l : Per.Ainf l) ^ (M - i - m) * (l : Per.Ainf l) ^ i =
        (l : Per.Ainf l) ^ (M - m) * (l : Per.Ainf l) ^ d := by rw [← pow_add, hd, pow_add]
    refine ⟨(l : Per.Ainf l) ^ d * v * Per.tm z, ?_⟩
    have e2 : Per.tm y * (l : Per.Ainf l) ^ i - (l : Per.Ainf l) ^ (M - m) * ((l : Per.Ainf l) ^ d * v * Per.tm z)
        = (Per.tm w - (l : Per.Ainf l)) ^ m * (u * Per.tm z * (l : Per.Ainf l) ^ i) := by
      rw [sub_add_cancel] at huv
      rw [hz, Per.tm, map_mul, map_pow]
      change Per.tm w ^ (M - i) * Per.tm z * _ - _ = _
      rw [huv]
      linear_combination (v * Per.tm z) * e
    rw [e2]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hk m)
  choose! c hc using key
  obtain ⟨t, ht⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff (p := l) a M
  obtain ⟨d, hd⟩ : ∃ d, M + 1 = M - m + d := ⟨M + 1 - (M - m), by omega⟩
  refine ⟨∑ i ∈ Finset.Iic M, c i + (l : Per.Ainf l) ^ d * t, ?_⟩
  have := Ideal.sum_mem _ hc
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
  rw [hd, pow_add] at ht
  convert this using 1
  linear_combination ht

theorem map_mem_kerP (a : Per.Ainf l) (m : ℕ) (h : a ∈ RingHom.ker (Per.θ l) ^ m) :
    algebraMap (Per.Ainf l) (Per.AinfP l) a ∈ Per.kerP l ^ m := by
  have h1 : RingHom.ker (Per.θ l) ≤ (Per.kerP l).comap (algebraMap (Per.Ainf l) (Per.AinfP l)) := by
    intro x hx
    exact Ideal.mem_comap.2 (GlobalTheory.RingIface.alg_mem_kerP l (RingHom.mem_ker.1 hx))
  exact Ideal.le_comap_pow _ m (Ideal.pow_right_mono h1 m h)

theorem term_le_one (a : Per.Ainf l) (i : ℕ) :
    ‖(((a.coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) * ((l : ℝ)⁻¹) ^ i ≤ 1 := by
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast hl.out.one_le
  rw [norm_root]
  exact mul_le_one₀ ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.property _)) (by positivity)
    (pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1))

theorem gauss_pow_le (k : ℕ) :
    ⨆ i : ℕ, ‖(((((l : Per.Ainf l) ^ k).coeff i).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ i) *
      ((l : ℝ)⁻¹) ^ i ≤ ((l : ℝ)⁻¹) ^ k := by
  refine ciSup_le fun i => ?_
  rw [norm_root]
  by_cases h : i = k
  · subst h
    exact mul_le_of_le_one_left (by positivity) ((GlobalTheory.RingBasics.mem_OC _).1 (Subtype.property _))
  · have h0 : (0 : Per.Fl l).untilt = 0 := by
      rw [← WittVector.fontaineTheta_teichmuller, WittVector.teichmuller_zero, map_zero]
    rw [WittVector.coeff_p_pow_eq_zero _ _ h, map_zero, h0]
    simp

theorem envelope_split (N : Per.Acris l → ℝ) (h0 : ∀ x, 0 ≤ N x) (hm : ∀ x y, N (x * y) = N x * N y)
    (hA : ∀ a : Per.Ainf l, N (algebraMap (Per.Ainf l) (Per.Acris l) a) =
      ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * ((l : ℝ)⁻¹) ^ n)
    (s : Per.Acris0 l) (k m : ℕ) (hs : N (algebraMap (Per.Acris0 l) (Per.Acris l) s) ≤ ((l : ℝ)⁻¹) ^ (k + m)) :
    ∃ c : Per.Ainf l, (s : Per.AinfP l) - algebraMap (Per.Ainf l) (Per.AinfP l) ((l : Per.Ainf l) ^ k * c) ∈
      Per.kerP l ^ m := by
  obtain ⟨K, a, ha⟩ := IsLocalization.Away.surj ((l : ℕ) : Per.Ainf l) (s : Per.AinfP l)
  have e0 : s * algebraMap (Per.Ainf l) (Per.Acris0 l) ((l : Per.Ainf l) ^ K) =
      algebraMap (Per.Ainf l) (Per.Acris0 l) a := Subtype.ext (by rw [← map_pow] at ha; exact ha)
  have hc : ∀ x, algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) x) =
      algebraMap (Per.Ainf l) (Per.Acris l) x := fun x => (GlobalTheory.RingIface.tower l x).symm
  have e1 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) e0
  rw [map_mul, hc, hc] at e1
  have hN : N (algebraMap (Per.Ainf l) (Per.Acris l) a) ≤ ((l : ℝ)⁻¹) ^ (k + m + K) := by
    rw [← e1, hm, pow_add]
    refine mul_le_mul hs ?_ (h0 _) (by positivity)
    rw [hA]
    exact gauss_pow_le l K
  rw [hA] at hN
  obtain ⟨c, hc⟩ := split_of_small l a (k + m + K) m fun i =>
    (le_ciSup (f := fun n : ℕ => ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) *
      ((l : ℝ)⁻¹) ^ n) ⟨1, by rintro _ ⟨i, rfl⟩; exact term_le_one l a i⟩ i).trans hN
  refine ⟨c, ?_⟩
  have h2 := map_mem_kerP l _ m hc
  rw [show k + m + K - m = k + K by omega, map_sub, ← ha, map_natCast] at h2
  rw [← Ideal.unit_mul_mem_iff_mem _ ((GlobalTheory.RingBasics.isUnit_l l).pow K)]
  convert h2 using 1
  simp only [map_mul, map_pow, map_natCast]
  ring

end GlobalTheory.MemLoc.GaussDefinite

namespace GlobalTheory.MemLoc

theorem gauss_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (N : ℝ → Per.Acris l → ℝ), (∀ r : ℝ, (l : ℝ)⁻¹ ≤ r → r < 1 → (∀ x, 0 ≤ N r x ∧ N r x ≤ 1) ∧ (∀ x y, N r (x + y) ≤ max (N r x) (N r y)) ∧ (∀ x, N r (-x) = N r x) ∧ (∀ x y, N r (x * y) = N r x * N r y) ∧ ∀ a : Per.Ainf l, N r (algebraMap (Per.Ainf l) (Per.Acris l) a) = ⨆ n : ℕ, ‖(((a.coeff n).untilt : Per.OC l) : ℂ_[l])‖ ^ ((1 : ℝ) / (l : ℝ) ^ n) * r ^ n) → ∀ b : Per.Acris l, b ≠ 0 → N (l : ℝ)⁻¹ b ≠ 0 := by
  intro l hl N hN b hb hb0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  obtain ⟨h01, hadd, hneg, hm, hA⟩ := hN _ le_rfl (inv_lt_one_of_one_lt₀ hl1)
  obtain ⟨j, hj⟩ := exists_isCrisP l
  refine hb (crisP_injective l j hj ?_)
  rw [map_zero]
  refine GlobalTheory.RingIface.ev_ext l _ _ fun m => ?_
  rw [map_zero]
  obtain ⟨N₀, hN₀⟩ := hj.bdd m
  obtain ⟨a, ha⟩ := hN₀ b
  have hu : IsUnit (Per.ev l m (((l : ℕ) : Per.BdRp l) ^ N₀)) := by
    have := ((GlobalTheory.RingBasics.isUnit_l l).pow N₀).map (Ideal.Quotient.mk (Per.kerP l ^ m))
    rw [map_pow, map_natCast] at this ⊢
    exact this
  rw [← hu.mul_right_eq_zero, ← map_mul, ha, Ideal.Quotient.eq_zero_iff_mem]
  refine image_kerP_pow_separated l m a fun k => ?_
  obtain ⟨s, z, hs⟩ := (acris_basic l).2.2.1 b (k + m)
  have hz : N (l : ℝ)⁻¹ (-((l : Per.Acris l) ^ (k + m) * z)) ≤ ((l : ℝ)⁻¹) ^ (k + m) := by
    rw [hneg, hm, ← map_natCast (algebraMap (Per.Ainf l) (Per.Acris l)), ← map_pow, hA]
    exact (mul_le_mul (GaussDefinite.gauss_pow_le l _) (h01 z).2 (h01 z).1 (by positivity)).trans
      (mul_one _).le
  have hs' : N (l : ℝ)⁻¹ (algebraMap (Per.Acris0 l) (Per.Acris l) s) ≤ ((l : ℝ)⁻¹) ^ (k + m) := by
    have e : algebraMap (Per.Acris0 l) (Per.Acris l) s = b + -((l : Per.Acris l) ^ (k + m) * z) := by
      rw [hs]; ring
    rw [e]
    refine (hadd _ _).trans (max_le ?_ hz)
    rw [hb0]
    positivity
  obtain ⟨c, hc⟩ := GaussDefinite.envelope_split l (N (l : ℝ)⁻¹) (fun x => (h01 x).1) hm hA s k m hs'
  obtain ⟨a', ha'⟩ := hN₀ z
  have hev : Per.ev l m (algebraMap (Per.AinfP l) (Per.BdRp l) (s : Per.AinfP l)) =
      Ideal.Quotient.mk _ (s : Per.AinfP l) := GlobalTheory.RingIface.ev_alg l m _
  refine ⟨(l : Per.Ainf l) ^ N₀ * c + (l : Per.Ainf l) ^ m * a', ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem] at hc ⊢
  rw [hs] at ha
  simp only [map_add, map_sub, map_mul, map_pow, map_natCast, hj.on0, hev] at ha ha' hc ⊢
  linear_combination -ha + (l : Per.AinfP l ⧸ Per.kerP l ^ m) ^ (k + m) * ha' +
    (l : Per.AinfP l ⧸ Per.kerP l ^ m) ^ N₀ * hc

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfCocycleSolutionTeichmullerEpsilonRootPow
section
noncomputable section

namespace GlobalTheory.ExpImage.EpsSolve

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem εroot_pow_eq (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ m ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply',
      frobeniusEquiv_symm_pow_p]
    exact ih

theorem epsT_pow (s : ℕ) : epsT AI s ^ (l ^ s) = 1 + AI.μ := by
  rw [epsT, ← map_pow, εroot_pow_eq, LocAinf.μ]
  ring

theorem epsT_zero : epsT AI 0 = 1 + AI.μ := by simpa using epsT_pow AI 0

theorem μ_not_unit : ¬ IsUnit AI.μ := by
  obtain ⟨θ, -, -, -, h, -⟩ := GlobalTheory.Cyc.exists_isTheta l P AI
  intro hu
  have h0 : θ AI.μ = 0 := (h _).mpr ⟨AI.π₁, by rw [AI.μ_eq, mul_comm]⟩
  have := hu.map θ
  rw [h0] at this
  exact not_isUnit_zero this

theorem actW_epsT (g : GQ l) (u : ℕ) (hu : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) (j : ℕ) :
    AI.actW g (epsT AI j) = epsT AI j ^ u := by
  rw [epsT, LocAinf.actW, WittVector.map_teichmuller, ← map_pow,
    ← GlobalTheory.ExpImage.actT_εroot_eq_pow l P AI g u hu j]
  rfl

theorem actW_μ (g : GQ l) (u : ℕ) (hu : (P.χQ g : ℚ_[l]) = (u : ℚ_[l])) :
    AI.actW g AI.μ = (1 + AI.μ) ^ u - 1 := by
  have h := actW_epsT AI g u hu 0
  rw [epsT_zero, map_add, map_one] at h
  linear_combination h

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (K : FinExt l) (s : ℕ),
    Lev l s → ∀ g : GQ l, (P.χQ g : ℚ_[l]) = ((1 + l ^ s : ℕ) : ℚ_[l]) → ∀ U : ℤ_[l],
    (l : ℤ_[l]) ^ s ∣ U - 1 → ∀ m : ℕ, ¬ l ∣ m → Solv AI K s g U (epsT AI s ^ m) := by
  intro l _ P AI K s hs g hg U hU m hm
  have hc := (GlobalTheory.Per.AinfComplete.main l AI.μ (μ_not_unit AI)).2
  obtain ⟨⟨ev, hev⟩, huniq⟩ := GlobalTheory.PowerSeriesAdicEval.exists_eval_and_unique ℤ_[l] (Ainf l) AI.μ hc
  obtain ⟨v, hv⟩ : (PowerSeries.X : PowerSeries ℤ_[l]) ∣ (1 + PowerSeries.X) ^ (1 + l ^ s) - 1 := by
    have := sub_dvd_pow_sub_pow (1 + PowerSeries.X : PowerSeries ℤ_[l]) 1 (1 + l ^ s)
    simpa using this
  have hsub : PowerSeries.HasSubst (PowerSeries.X * v : PowerSeries ℤ_[l]) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)
  let γ : PowerSeries ℤ_[l] →ₐ[ℤ_[l]] PowerSeries ℤ_[l] := PowerSeries.substAlgHom hsub
  have hγ : γ PowerSeries.X = PowerSeries.X * v := PowerSeries.substAlgHom_X hsub
  have hgμ : AI.actW g AI.μ = AI.μ * ev v := by
    have := congrArg ev hv
    simp only [map_sub, map_pow, map_add, map_one, map_mul, hev] at this
    rw [actW_μ AI g _ hg, this]
  have hgev : ∀ f, AI.actW g (ev f) = ev (γ f) := by
    have := huniq (((AI.actWHom g : Ainf l ≃ₐ[ℤ_[l]] Ainf l) : Ainf l →ₐ[ℤ_[l]] Ainf l).comp ev)
      (ev.comp γ) (by
        change AI.actW g (ev PowerSeries.X) = ev (γ PowerSeries.X)
        rw [hγ, map_mul, hev, hgμ]) (by
        change AI.μ ∣ AI.actW g (ev PowerSeries.X)
        rw [hev, hgμ]
        exact dvd_mul_right _ _)
    intro f
    exact DFunLike.congr_fun this f
  have hχ : ∀ h ∈ Hinf K, (P.χQ h : ℚ_[l]) = ((1 : ℕ) : ℚ_[l]) := by
    intro h hh
    have := ((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K h (Hinf_le_fix hh)).2.mp hh
    rw [this]
    simp
  have hhev : ∀ h ∈ Hinf K, ∀ f, AI.actW h (ev f) = ev f := by
    intro h hh
    have hμ : AI.actW h AI.μ = AI.μ := by
      rw [actW_μ AI h 1 (hχ h hh)]
      ring
    have := huniq (((AI.actWHom h : Ainf l ≃ₐ[ℤ_[l]] Ainf l) : Ainf l →ₐ[ℤ_[l]] Ainf l).comp ev)
      ev (by
        change AI.actW h (ev PowerSeries.X) = ev PowerSeries.X
        rw [hev, hμ]) (by
        change AI.μ ∣ AI.actW h (ev PowerSeries.X)
        rw [hev, hμ])
    intro f
    exact DFunLike.congr_fun this f
  have hgE : AI.actW g (epsT AI s) = epsT AI s * (1 + AI.μ) := by
    rw [actW_epsT AI g _ hg, pow_add, pow_one, epsT_pow]
  choose pp FF hpF using GlobalTheory.ExpImage.solve_mod_pow l s hs m hm U hU γ v hv.symm hγ
  let F : ℕ → PowerSeries ℤ_[l] := fun k => Nat.rec 1 (fun k f => FF (k + 1) f) k
  have hF : ∀ k, F (k + 1) = FF (k + 1) (F k) := fun _ => rfl
  refine ⟨fun k => epsT AI s ^ m * ev (pp (k + 1) (F k)), fun k => epsT AI s ^ m * ev (F k), ?_,
    fun k h hh => ?_, fun k => ?_⟩
  · change epsT AI s ^ m * ev 1 = _
    rw [map_one, mul_one]
  · rw [map_mul, map_pow, actW_epsT AI h 1 (hχ h hh), pow_one, hhev h hh]
  · have h1 := congrArg ev (hpF (k + 1) (F k))
    have hC : ev (PowerSeries.C U) = algebraMap ℤ_[l] (Ainf l) U := ev.commutes U
    simp only [map_sub, map_pow, map_add, map_one, map_mul, hev, hC, map_natCast] at h1
    unfold Step
    beta_reduce
    rw [hF, map_mul, map_pow, hgE, hgev, hgμ, mul_pow, mul_pow]
    linear_combination (epsT AI s ^ m * AI.μ ^ (k + 1)) * h1

end GlobalTheory.ExpImage.EpsSolve
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfFrobeniusUnitEigenvectorGaloisLineStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ainf_frobenius_unit_eigenvector_galois_line : ∀ (l : ℕ) [Fact l.Prime] (w : Per.Ainf l) (u : ℤ_[l]ˣ), IsUnit w → Per.φA l w = Per.zA l u * w → ∀ g : GQ l, ∃ z : ℤ_[l], Per.σB g (Per.aB l w) = Per.zB l z * Per.aB l w := by
  first | exact @GlobalTheory.UnitLine.sigma_unit_eigen | exact GlobalTheory.UnitLine.sigma_unit_eigen | (intros; apply GlobalTheory.UnitLine.sigma_unit_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfMuFrobeniusEquationSolvableAndTendsto
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage.Conv

section General

variable {A : Type*} [CommRing A]

theorem step_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A} (hc : c ∈ I) (n : ℕ)
    {y : A} (hy : y ∈ I ^ n) : c * φ y ∈ I ^ (n + 1) := by
  rw [pow_succ']
  refine Ideal.mul_mem_mul hc ?_
  have h : φ y ∈ (I ^ n).map φ := Ideal.mem_map_of_mem φ hy
  rw [Ideal.map_pow] at h
  exact Ideal.pow_right_mono hφ n h

theorem solve (I : Ideal A) [hI : IsAdicComplete I A] (φ : A →+* A) (hφ : I.map φ ≤ I) {c : A}
    (hc : c ∈ I) (q : A) : ∃ y, y - c * φ y = q := by
  let f : ℕ → A := fun n => (fun z => q + c * φ z)^[n] 0
  have hf : ∀ n, f (n + 1) = q + c * φ (f n) := fun n => Function.iterate_succ_apply' _ _ _
  have h1 : ∀ n, f n - f (n + 1) ∈ I ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := step_mem I φ hφ hc n ih
      rw [hf (n + 1)]
      nth_rewrite 1 [hf n]
      convert this using 1
      rw [map_sub]; ring
  have h2 : ∀ m n, m ≤ n → f m - f n ∈ I ^ m := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := add_mem ih (Ideal.pow_le_pow_right hmn (h1 n))
      rwa [sub_add_sub_cancel] at this
  obtain ⟨L, hL⟩ := hI.toIsPrecomplete.prec' f (by
    intro m n hmn
    simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem]
    exact h2 m n hmn)
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at hL
  refine ⟨L, ?_⟩
  rw [← sub_eq_zero]
  refine hI.toIsHausdorff.haus' _ fun n => ?_
  simp only [smul_eq_mul, Ideal.mul_top, SModEq.zero]
  refine Ideal.pow_le_pow_right (Nat.le_succ n) ?_
  have := sub_mem (step_mem I φ hφ hc n (hL n)) (hL (n + 1))
  convert this using 1
  rw [hf, map_sub]; ring

theorem geom_mem (p : ℕ) (e : A) :
    ∑ i ∈ Finset.range p, e ^ i ∈ Ideal.span {(p : A), e - 1} := by
  have h : ∑ i ∈ Finset.range p, e ^ i = (p : A) + ∑ i ∈ Finset.range p, (e ^ i - 1) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [h]
  refine add_mem (Ideal.subset_span (by simp)) (Ideal.sum_mem _ fun i _ => ?_)
  obtain ⟨d, hd⟩ : e - 1 ∣ e ^ i - 1 := by simpa using sub_dvd_pow_sub_pow e 1 i
  rw [hd]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))

theorem map_le (p : ℕ) (φ : A →+* A) {m c : A} (h : φ m = c * m) :
    (Ideal.span {(p : A), m}).map φ ≤ Ideal.span {(p : A), m} := by
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨x, rfl | rfl, rfl⟩
  · rw [map_natCast]; exact Ideal.subset_span (by simp)
  · rw [h]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))

theorem iterate_mem (I : Ideal A) (φ : A →+* A) (hφ : I.map φ ≤ I) {m c : A} (hc : c ∈ I)
    (h : φ m = c * m) (k : ℕ) : ∃ d ∈ I ^ k, φ^[k] m = d * m := by
  induction k with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨d, hd, e⟩ := ih
    refine ⟨c * φ d, step_mem I φ hφ hc k hd, ?_⟩
    rw [Function.iterate_succ_apply', e, map_mul, h]; ring

end General

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem frob_mu : WittVector.frobenius AI.μ =
    (∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i) * AI.μ := by
  have h : WittVector.frobenius (WittVector.teichmuller l AI.ε) =
      WittVector.teichmuller l AI.ε ^ l := by
    rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def, map_pow]
  rw [LocAinf.μ, map_sub, map_one, h, geom_sum_mul]

theorem mu_not_isUnit : ¬ IsUnit AI.μ := by
  intro h
  obtain ⟨θ, hθ⟩ := exists_isTheta l P AI
  have h0 : θ AI.μ = 0 := (hθ.2.2.2.1 _).2 ⟨AI.π₁, by rw [AI.μ_eq, mul_comm]⟩
  have := h.map θ
  rw [h0] at this
  exact not_isUnit_zero this

theorem main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), (∀ q : Ainf l, ∃ y : Ainf l, AI.μ * y - WittVector.frobenius (AI.μ * y) = AI.μ * q) ∧ ∀ M n : ℕ, ∃ k₀ : ℕ, ∀ k ≥ k₀, (WittVector.frobenius : Ainf l →+* Ainf l)^[k] AI.μ ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M} := by
  intro l _ P AI
  have hc : ∑ i ∈ Finset.range l, WittVector.teichmuller l AI.ε ^ i ∈
      Ideal.span {((l : ℕ) : Ainf l), AI.μ} := geom_mem l _
  have hφ := map_le l _ (frob_mu AI)
  refine ⟨fun q => ?_, fun M n => ⟨n + M, fun k hk => ?_⟩⟩
  · haveI := (GlobalTheory.Per.AinfComplete.main l AI.μ (mu_not_isUnit AI)).1
    obtain ⟨y, hy⟩ := solve _ _ hφ hc q
    refine ⟨y, ?_⟩
    rw [map_mul, frob_mu, ← hy]; ring
  · obtain ⟨d, hd, e⟩ := iterate_mem _ _ hφ hc (frob_mu AI) k
    rw [e]
    refine Ideal.mul_mem_right _ _ ?_
    have h1 : Ideal.span {((l : ℕ) : Ainf l), AI.μ} ≤ Ideal.span {((l : ℕ) : Ainf l), AI.ξ} := by
      rw [Ideal.span_le]
      rintro x (rfl | rfl)
      · exact Ideal.subset_span (by simp)
      · rw [AI.μ_eq]; exact Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))
    have h2 := Ideal.pow_le_pow_right hk (Ideal.pow_right_mono h1 k hd)
    rw [Ideal.span_insert] at h2
    rw [Ideal.span_insert, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow]
    exact Ideal.sup_pow_add_le_pow_sup_pow h2

end GlobalTheory.ExpImage.Conv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AxLemmaPadicComplexFixedElementApproximationStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.axLemma_padicComplex_fixed_element_approximation : ∀ (l : ℕ) [Fact l.Prime], ∃ c : ℝ, 0 < c ∧ ∀ (H : Subgroup (GQ l)) (y : ℂ_[l]) (r : ℝ), 0 < r → (∀ g ∈ H, ‖Per.σC g y - y‖ ≤ r) → ∃ z : Om l, (∀ g ∈ H, g z = z) ∧ ‖y - (z : ℂ_[l])‖ ≤ c * r := by
  first | exact @GlobalTheory.AxLemma.ax_lemma_complete | exact GlobalTheory.AxLemma.ax_lemma_complete | (intros; apply GlobalTheory.AxLemma.ax_lemma_complete <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisExistsTPowMulThetaNeZeroStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_exists_tPow_mul_theta_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (C : Core l) (b : Per.Bcris l), b ≠ 0 → ∃ (m n : ℕ) (b' : Per.Bcris l) (y : Per.BdRp l), b * C.tB ^ m = C.tB ^ n * b' ∧ C.ι b' = algebraMap (Per.BdRp l) (Per.BdR l) y ∧ Per.θD l y ≠ 0 := by
  first | exact @GlobalTheory.MemLoc.RegDivide.exists_divide | exact GlobalTheory.MemLoc.RegDivide.exists_divide | (intros; apply GlobalTheory.MemLoc.RegDivide.exists_divide <;> assumption)
end

