import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0244
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeOfAdelicPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0257
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0260
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesSupNormMulPadicComplex
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem exists_least_argmax_of_tendsto_zero (b : ℕ → ℝ) (h0 : ∀ i, 0 ≤ b i)
    (hb : Filter.Tendsto b Filter.atTop (nhds 0)) :
    ∃ i₀, (∀ i, b i ≤ b i₀) ∧ ∀ i < i₀, b i < b i₀ := by
  have hex : ∃ i, ∀ j, b j ≤ b i := by
    by_cases hpos : ∃ k, 0 < b k
    · obtain ⟨k, hk⟩ := hpos
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (hb.eventually (gt_mem_nhds hk))
      obtain ⟨i, hi, hmax⟩ := (Finset.range (max N (k + 1))).exists_max_image b
        ⟨k, Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))⟩
      refine ⟨i, fun j => ?_⟩
      by_cases hj : j < max N (k + 1)
      · exact hmax j (Finset.mem_range.2 hj)
      · have hjN : N ≤ j := le_trans (le_max_left _ _) (not_lt.1 hj)
        have hkmem : k ∈ Finset.range (max N (k + 1)) :=
          Finset.mem_range.2 (lt_of_lt_of_le (Nat.lt_succ_self k) (le_max_right _ _))
        exact (hN j hjN).le.trans (hmax k hkmem)
    · push Not at hpos
      exact ⟨0, fun j => (hpos j).trans (h0 0)⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, fun i hi => ?_⟩
  have hle : b i ≤ b (Nat.find hex) := Nat.find_spec hex i
  refine lt_of_le_of_ne hle fun heq => Nat.find_min hex hi ?_
  intro j
  rw [heq]
  exact Nat.find_spec hex j

theorem BddSer.tendsto_weighted {K : Type*} [NormedField K] {f : PowerSeries K} (hf : BddSer f)
    {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) :
    Filter.Tendsto (fun i => ‖PowerSeries.coeff i f‖ * ρ ^ i) Filter.atTop (nhds 0) := by
  obtain ⟨B, hB⟩ := hf
  have hlim : Filter.Tendsto (fun i : ℕ => B * ρ ^ i) Filter.atTop (nhds 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1).const_mul B
  exact squeeze_zero (fun i => by positivity)
    (fun i => mul_le_mul_of_nonneg_right (hB i) (pow_nonneg h0.le i)) hlim

private lemma norm_finset_sum_lt_of_ultrametric {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}
    (s : Finset ι) (x : ι → K) {D : ℝ} (hD : 0 < D) (hx : ∀ p ∈ s, ‖x p‖ < D) :
    ‖∑ p ∈ s, x p‖ < D := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hD
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt ?_ ?_)
    · exact hx a (Finset.mem_insert_self a s)
    · exact ih fun p hp => hx p (Finset.mem_insert_of_mem hp)

theorem norm_coeff_mul_weighted_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    (f g : PowerSeries K) (c : ℝ) (hf : BddSer f) (hg : BddSer g)
    (hc : ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1) (i j : ℕ) :
    (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j) ≤ c := by
  set A : ℕ → ℝ := fun k => ‖PowerSeries.coeff k f‖ * ρ ^ k with hAdef
  set B : ℕ → ℝ := fun k => ‖PowerSeries.coeff k g‖ * ρ ^ k with hBdef
  have hA0 : ∀ k, 0 ≤ A k := fun k => by positivity
  have hB0 : ∀ k, 0 ≤ B k := fun k => by positivity
  obtain ⟨i₀, hAi, hAlt⟩ := exists_least_argmax_of_tendsto_zero A hA0 (hf.tendsto_weighted h0 h1)
  obtain ⟨j₀, hBj, hBlt⟩ := exists_least_argmax_of_tendsto_zero B hB0 (hg.tendsto_weighted h0 h1)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0)
  have hstep : A i * B j ≤ A i₀ * B j₀ := mul_le_mul (hAi i) (hBj j) (hB0 j) (hA0 i₀)
  change A i * B j ≤ c
  refine hstep.trans ?_
  rcases (mul_nonneg (hA0 i₀) (hB0 j₀)).eq_or_lt with hz | hpos
  · rw [← hz]; exact hc0
  have hApos : 0 < A i₀ := lt_of_le_of_ne (hA0 i₀) fun h => by rw [← h, zero_mul] at hpos; exact lt_irrefl 0 hpos
  have hBpos : 0 < B j₀ := lt_of_le_of_ne (hB0 j₀) fun h => by rw [← h, mul_zero] at hpos; exact lt_irrefl 0 hpos
  set n := i₀ + j₀ with hn
  have hρn : 0 < ρ ^ n := pow_pos h0 n
  have hterm : ∀ p : ℕ × ℕ, p.1 + p.2 = n →
      A p.1 * B p.2 = ‖PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ * ρ ^ n := by
    intro p hp
    rw [← hp, norm_mul, pow_add]
    simp only [hAdef, hBdef]
    ring
  set D := PowerSeries.coeff i₀ f * PowerSeries.coeff j₀ g with hDdef
  have hDA : A i₀ * B j₀ = ‖D‖ * ρ ^ n := hterm (i₀, j₀) rfl
  have hDpos : 0 < ‖D‖ := by
    have : 0 < ‖D‖ * ρ ^ n := hDA ▸ hpos
    exact pos_of_mul_pos_left this hρn.le
  have hmem : (i₀, j₀) ∈ Finset.HasAntidiagonal.antidiagonal n := Finset.HasAntidiagonal.mem_antidiagonal.2 rfl
  have hrest : ‖∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
      PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g‖ < ‖D‖ := by
    refine norm_finset_sum_lt_of_ultrametric _ _ hDpos fun p hp => ?_
    obtain ⟨hne, hp⟩ := Finset.mem_erase.1 hp
    have hsum : p.1 + p.2 = n := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    have hlt : A p.1 * B p.2 < A i₀ * B j₀ := by
      rcases lt_trichotomy p.1 i₀ with h | h | h
      · calc A p.1 * B p.2 ≤ A p.1 * B j₀ := mul_le_mul_of_nonneg_left (hBj _) (hA0 _)
          _ < A i₀ * B j₀ := mul_lt_mul_of_pos_right (hAlt _ h) hBpos
      · exfalso
        apply hne
        ext
        · exact h
        · simp only; omega
      · have h2 : p.2 < j₀ := by omega
        calc A p.1 * B p.2 ≤ A i₀ * B p.2 := mul_le_mul_of_nonneg_right (hAi _) (hB0 _)
          _ < A i₀ * B j₀ := mul_lt_mul_of_pos_left (hBlt _ h2) hApos
    rw [hterm p hsum, hDA] at hlt
    exact lt_of_mul_lt_mul_right hlt hρn.le
  have hcoeff : PowerSeries.coeff n (f * g) =
      D + ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g := by
    rw [PowerSeries.coeff_mul, ← Finset.add_sum_erase _ _ hmem]
  have hDle : ‖D‖ ≤ ‖PowerSeries.coeff n (f * g)‖ := by
    by_contra hcon
    push Not at hcon
    have hD : D = PowerSeries.coeff n (f * g) + -(∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g) := by
      rw [hcoeff]; ring
    have := IsUltrametricDist.norm_add_le_max (PowerSeries.coeff n (f * g))
      (-(∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n).erase (i₀, j₀),
        PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g))
    rw [← hD, norm_neg] at this
    exact lt_irrefl _ (lt_of_le_of_lt this (max_lt hcon hrest))
  rw [hDA]
  calc ‖D‖ * ρ ^ n ≤ c * ρ ^ n := mul_le_mul_of_nonneg_right (hDle.trans (hc n)) hρn.le
    _ ≤ c * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h0.le h1.le) hc0
    _ = c := mul_one c

theorem norm_coeff_mul_norm_coeff_le {K : Type*} [NormedField K] [IsUltrametricDist K]
    (f g : PowerSeries K) (c : ℝ) (hf : BddSer f) (hg : BddSer g)
    (hc : ∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) (i j : ℕ) :
    ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  have ht : Filter.Tendsto
      (fun ρ : ℝ => (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j))
      (nhdsWithin 1 (Set.Iio 1))
      (nhds ((‖PowerSeries.coeff i f‖ * 1 ^ i) * (‖PowerSeries.coeff j g‖ * 1 ^ j))) :=
    ((Continuous.tendsto (by fun_prop) 1).mono_left nhdsWithin_le_nhds)
  have hev : ∀ᶠ ρ in nhdsWithin (1 : ℝ) (Set.Iio 1),
      (‖PowerSeries.coeff i f‖ * ρ ^ i) * (‖PowerSeries.coeff j g‖ * ρ ^ j) ≤ c := by
    filter_upwards [Ioo_mem_nhdsLT (show (0 : ℝ) < 1 by norm_num)] with ρ hρ
    exact norm_coeff_mul_weighted_le f g c hf hg hc hρ.1 hρ.2 i j
  simpa using le_of_tendsto ht hev

theorem sup_norm_mul_padicComplex : ∀ (p : ℕ) [Fact p.Prime] (f g : PowerSeries ℂ_[p]) (c : ℝ),
    BddSer f → BddSer g → (∀ n, ‖PowerSeries.coeff n (f * g)‖ ≤ c) →
      ∀ i j, ‖PowerSeries.coeff i f‖ * ‖PowerSeries.coeff j g‖ ≤ c := by
  intro p _ f g c hf hg hc i j
  exact norm_coeff_mul_norm_coeff_le f g c hf hg hc i j

end GlobalTheory.EvenTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RationalMatrixMulThetaLattices
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.RatEqui
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaStab

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem moves_one (D : D7) (N : ℕ) : Moves D ((1 : GA D N) : GL (Fin N) (AE D)) (stdL D N) := by
  obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
  exact h2 ▸ (h1 1).1

theorem mem_standardThetaLattice_iff_adelicIdeal (hcc : cc ≠ ⊥) (x : VC D N N') : x ∈ La0 D (tor0 D cc δ) N N' ↔
    ∃ z : Matrix (Fin N') (Fin N) D.host.E, x = pt D (tor0 D cc δ) δ z ∧ ∀ i j, inc D (z i j) ∈ IhE D cc := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  constructor
  · intro hx
    obtain ⟨z, hz, h⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hcc N N' 1 1 _ _
      (moves_one D N) (moves_one D N') x hx
    exact ⟨z, hz, fun i j => by simpa using h i j⟩
  · rintro ⟨z, rfl, h⟩
    exact GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hcc N N' 1 1 _ _
      (moves_one D N) (moves_one D N') z (fun i j => by simpa using h i j)

theorem inc_mem_of_isIntegral {e : D.host.E} (he : IsIntegral ℤ e) : inc D e ∈ OhE D :=
  GlobalTheory.NormSum.MovedTheta.inc_int (⟨e, he⟩ : 𝓞 D.host.E)

theorem mulV_mem (hcc : cc ≠ ⊥) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (h' : ∀ i j, IsIntegral ℤ (M' i j)) (h : ∀ i j, IsIntegral ℤ (M i j)) (x : VC D N N')
    (hx : x ∈ La0 D (tor0 D cc δ) N N') : mulV D M' M x ∈ La0 D (tor0 D cc δ) N N' := by
  obtain ⟨z, rfl, hz⟩ := (mem_standardThetaLattice_iff_adelicIdeal hcc x).1 hx
  refine (mem_standardThetaLattice_iff_adelicIdeal hcc _).2 ⟨_, mulV_pt D cc δ M' M z, fun i j => ?_⟩
  simp only [Matrix.mul_apply, map_sum, map_mul]
  refine sum_mem fun k _ => ?_
  rw [mul_comm]
  refine MovedTheta.mul_mem_IhE (inc_mem_of_isIntegral (h k j)) (sum_mem fun l _ => ?_)
  exact MovedTheta.mul_mem_IhE (inc_mem_of_isIntegral (h' i l)) (hz l k)

theorem exists_denom {n : ℕ} (M : Matrix (Fin n) (Fin n) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ ∀ i j, IsIntegral ℤ ((m • M) i j) := by
  obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ
    (Finset.univ.image fun p : Fin n × Fin n => M p.1 p.2)
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i j => ?_⟩
  have h1 := h (M i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
  rw [Matrix.smul_apply, ← natCast_zsmul]
  rcases Int.natAbs_eq y with e | e
  · rw [← e]; exact h1
  · have e' : ((y.natAbs : ℕ) : ℤ) = -y := by omega
    rw [e', neg_smul]; exact h1.neg

theorem mulV_nsmul (m' m : ℕ) (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E)
    (x : VC D N N') : mulV D (m' • M') (m • M) x = (m' * m) • mulV D M' M x := by
  funext τ
  have e : ∀ {n : ℕ} (k : ℕ) (A : Matrix (Fin n) (Fin n) D.host.E),
      (k • A).map (embT D τ) = k • A.map (embT D τ) := by
    intro n k A
    ext i j
    simp only [Matrix.map_apply, Matrix.smul_apply, map_nsmul]
  change (m' • M').map (embT D τ) * Matrix.of (x τ) * (m • M).map (embT D τ) =
    (m' * m) • (M'.map (embT D τ) * Matrix.of (x τ) * M.map (embT D τ))
  rw [e, e, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, mul_smul]

theorem inv_eq_adj {n : ℕ} {g : GA D n} {γ : Matrix (Fin n) (Fin n) D.host.E}
    (h : IsRat D (g : GL (Fin n) (AE D)) γ) :
    (((g : GL (Fin n) (AE D))⁻¹ : GL (Fin n) (AE D)) : Matrix (Fin n) (Fin n) (AE D)) = (adj D γ).map (inc D) := by
  have h1 : γ * adj D γ = 1 := (GlobalTheory.NormSum.mem_ratG_intG D n).2.2.2.1 g γ h
  apply Units.inv_eq_of_mul_eq_one_right
  unfold IsRat at h
  rw [h, ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mem_iff_moved (hcc : cc ≠ ⊥) (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E)
    (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (h : IsRat D (γA : GL (Fin N) (AE D)) γ)
    (h' : IsRat D (γA' : GL (Fin N') (AE D)) γ') (hL : Moves D (γA : GL (Fin N) (AE D)) L₁)
    (hL' : Moves D (γA' : GL (Fin N') (AE D)) L₁') (x : VC D N N') :
    x ∈ La0 D (tor0 D cc δ) N N' ↔ mulV D γ' (adj D γ) x ∈ La D (tor0 D cc δ) L₁ L₁' := by
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have h1 : adj D γ * γ = 1 := mul_eq_one_comm.1 ((GlobalTheory.NormSum.mem_ratG_intG D N).2.2.2.1 γA γ h)
  have h1' : adj D γ' * γ' = 1 := mul_eq_one_comm.1 ((GlobalTheory.NormSum.mem_ratG_intG D N').2.2.2.1 γA' γ' h')
  have key : ∀ z : Matrix (Fin N') (Fin N) D.host.E,
      (((γA' : GL (Fin N') (AE D))⁻¹ : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) * z.map (inc D) *
        ((γA : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) = (adj D γ' * z * γ).map (inc D) := by
    intro z
    have h2 := h
    unfold IsRat at h2
    rw [inv_eq_adj h', h2, Matrix.map_mul, Matrix.map_mul]
  constructor
  · intro hx
    obtain ⟨z, rfl, hz⟩ := (mem_standardThetaLattice_iff_adelicIdeal hcc x).1 hx
    rw [mulV_pt]
    refine GlobalTheory.NormSum.pt_mem_La_of_adelic D hG cc δ hcc N N' γA γA' _ _ hL hL' _ fun i j => ?_
    have e : adj D γ' * (γ' * z * adj D γ) * γ = z := by
      rw [Matrix.mul_assoc γ', ← Matrix.mul_assoc (adj D γ'), h1', Matrix.one_mul, Matrix.mul_assoc, h1,
        Matrix.mul_one]
    rw [key, e]
    exact hz i j
  · intro hx
    obtain ⟨w, hw, hz⟩ := GlobalTheory.NormSum.exists_pt_of_mem_La_moved D hG cc δ hcc N N' γA γA' _ _ hL hL' _ hx
    refine (mem_standardThetaLattice_iff_adelicIdeal hcc x).2 ⟨adj D γ' * w * γ, ?_, fun i j => ?_⟩
    · rw [← mulV_pt, ← hw, mulV_mulV, h1, h1', mulV_one]
    · have := hz i j
      rw [key] at this
      exact this

end GlobalTheory.ThetaStab

open GlobalTheory.ThetaStab in

theorem GlobalTheory.ThetaStab.mulV_theta_lattices : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ), (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), (∀ i j, IsIntegral ℤ (M' i j)) → (∀ i j, IsIntegral ℤ (M i j)) → ∀ x ∈ La0 D (tor0 D cc δ) N N', mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ (∀ (M' : Matrix (Fin N') (Fin N') D.host.E) (M : Matrix (Fin N) (Fin N) D.host.E), ∃ m : ℕ, 0 < m ∧ ∀ x ∈ La0 D (tor0 D cc δ) N N', m • mulV D M' M x ∈ La0 D (tor0 D cc δ) N N') ∧ ∀ (γA : GA D N) (γA' : GA D N') (γ : Matrix (Fin N) (Fin N) D.host.E) (γ' : Matrix (Fin N') (Fin N') D.host.E) (L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L₁' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsRat D (γA : GL (Fin N) (AE D)) γ → IsRat D (γA' : GL (Fin N') (AE D)) γ' → Moves D (γA : GL (Fin N) (AE D)) L₁ → Moves D (γA' : GL (Fin N') (AE D)) L₁' → ∀ x, x ∈ La0 D (tor0 D cc δ) N N' ↔ mulV D γ' (adj D γ) x ∈ La D (tor0 D cc δ) L₁ L₁' := by
  intro D cc δ hc N N'
  have hcc : cc ≠ ⊥ := hc.1.1
  refine ⟨fun M' M h' h x hx => mulV_mem hcc M' M h' h x hx, fun M' M => ?_,
    fun γA γA' γ γ' L₁ L₁' h h' hL hL' x => mem_iff_moved hcc γA γA' γ γ' L₁ L₁' h h' hL hL' x⟩
  obtain ⟨m', hm', h'⟩ := exists_denom M'
  obtain ⟨m, hm, h⟩ := exists_denom M
  refine ⟨m' * m, Nat.mul_pos hm' hm, fun x hx => ?_⟩
  rw [← mulV_nsmul]
  exact mulV_mem hcc _ _ h' h x hx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SqThD
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaTransl

def sqThD (Λ : AddSubgroup ℂ) (v z : ℂ) : ℂ :=
  sgStar Λ z * deriv (GlobalTheory.EvenTheta.sqTh Λ v) z - 2 * deriv (sgStar Λ) z * GlobalTheory.EvenTheta.sqTh Λ v z

end GlobalTheory.ThetaTransl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumCoeffMonomial
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.MinorBound

theorem card_strictMono_le (a d : ℕ) [Fintype {s : Fin a → Fin d // StrictMono s}] :
    Fintype.card {s : Fin a → Fin d // StrictMono s} ≤ 2 ^ d := by
  have h : Function.Injective
      (fun s : {s : Fin a → Fin d // StrictMono s} => (Set.range s.1 : Set (Fin d))) := by
    intro s t hst
    exact Subtype.ext ((s.2.range_inj t.2).1 hst)
  have := Fintype.card_le_of_injective _ h
  simpa using this

theorem sum_coeff_monomial {σ : Type} (w : (σ →₀ ℕ) → ℂ) :
    ∃ L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ, (∀ α c, L (MvPolynomial.monomial α c) = c * w α) ∧
      ∀ P, L P = ∑ α ∈ P.support, MvPolynomial.coeff α P * w α := by
  let L : MvPolynomial σ ℂ →ₗ[ℂ] ℂ := (MvPolynomial.basisMonomials σ ℂ).constr ℂ w
  have h1 : ∀ α c, L (MvPolynomial.monomial α c) = c * w α := by
    intro α c
    have : MvPolynomial.monomial α c = c • (MvPolynomial.basisMonomials σ ℂ) α := by
      simp [MvPolynomial.smul_monomial]
    rw [this, map_smul, Module.Basis.constr_basis, smul_eq_mul]
  refine ⟨L, h1, fun P => ?_⟩
  conv_lhs => rw [P.as_sum, map_sum]
  simp only [h1]

theorem prod_monomial {σ ι : Type} (s : Finset ι) (α : ι → σ →₀ ℕ) (c : ι → ℂ) :
    ∏ i ∈ s, MvPolynomial.monomial (α i) (c i) =
      MvPolynomial.monomial (∑ i ∈ s, α i) (∏ i ∈ s, c i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih,
      MvPolynomial.monomial_mul]

noncomputable def expo (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) : Mono D a d :=
  ∑ τ, ∑ j, ∑ i, Finsupp.single (τ, (T τ j).1 (p τ j i), i) 1

theorem minorPol_eq (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) :
    minorPol D T = ∑ p : (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)),
      MvPolynomial.monomial (expo D T p) (∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ)) := by
  unfold minorPol
  have hdet : ∀ τ (j : Fin (n τ)), (Matrix.of fun i i' : Fin a =>
      (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (GL3Theta.Idx D a d) ℂ)).det =
      ∑ σ : Equiv.Perm (Fin a), MvPolynomial.monomial
        (∑ i, Finsupp.single ((τ, (T τ j).1 (σ i), i) : GL3Theta.Idx D a d) 1)
        (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℂ) := by
    intro τ j
    rw [Matrix.det_apply']
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.of_apply, MvPolynomial.X]
    rw [prod_monomial, ← map_intCast (MvPolynomial.C : ℂ →+* MvPolynomial (GL3Theta.Idx D a d) ℂ),
      MvPolynomial.C_mul_monomial]
    simp
  simp only [hdet]
  simp only [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr (by convert rfl) fun p _ => ?_
  simp only [prod_monomial, expo]

theorem expo_le (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) (k : D.what₂.Tau × Fin d × Fin a) :
    expo D T p k ≤ n k.1 := by
  obtain ⟨τ0, r, c⟩ := k
  simp only [expo, Finsupp.coe_finset_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single τ0]
  · calc _ ≤ ∑ _j : Fin (n τ0), 1 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [Finset.sum_eq_single c]
          · rw [Finsupp.single_apply]; split_ifs <;> simp
          · intro i _ hi
            rw [Finsupp.single_apply, if_neg]
            simp [hi]
          · simp
      _ = n τ0 := by simp
  · intro τ _ hτ
    refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun i _ => ?_
    rw [Finsupp.single_apply, if_neg]
    simp [hτ]
  · simp

theorem expo_sum (D : D7) {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n)
    (p : ∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) :
    ((expo D T p).sum fun _ m => m) = a * ∑ τ, n τ := by
  have : ((expo D T p).sum fun _ m => m) = Finsupp.degree (expo D T p) := rfl
  rw [this]
  simp only [expo, map_sum, Finsupp.degree_single]
  simp [Finset.mul_sum, mul_comm]

theorem minor_bound : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ) (G : VC D a d → ℂ) (S A B : ℝ), 0 < A → 1 ≤ B → 0 ≤ S → (∀ τ, (n τ : ℝ) ≤ 2 * B) → Differentiable ℂ G → (∀ z, ‖G z‖ ^ 2 ≤ S * Real.exp (Real.pi * (∑ τ, ∑ i, ∑ j, ‖z τ i j‖ ^ 2) / A)) → (Fintype.card (Tup D a d n) ≤ 2 ^ (d * ∑ τ, n τ)) ∧ ∀ T : Tup D a d n, ‖GL3Theta.applyAt0 D (minorPol D T) G‖ ^ 2 ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ)) ^ 2 * (S * (2 * Real.exp 1 * Real.pi * B / A) ^ (a * ∑ τ, n τ)) := by
  intro D a d n G S A B hA hB hS hn hG hbd
  constructor
  · simp only [Fintype.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [pow_mul, ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod' fun τ _ => Nat.pow_le_pow_left (card_strictMono_le a d) _
  · intro T
    obtain ⟨L, hL1, hL2⟩ := sum_coeff_monomial
      (fun α : Mono D a d => (α.prod fun _ n => (n.factorial : ℂ)) * taylor D G α)
    have h0 : GL3Theta.applyAt0 D (minorPol D T) G = L (minorPol D T) := by
      rw [hL2]; simp only [GL3Theta.applyAt0, mul_assoc]
    set M := S * (2 * Real.exp 1 * Real.pi * B / A) ^ (a * ∑ τ, n τ) with hM
    have hM0 : 0 ≤ M := by
      have : (0:ℝ) < B := by linarith
      have := Real.pi_pos
      positivity
    have hterm : ∀ p : (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)),
        ‖L (MvPolynomial.monomial (expo D T p)
          (∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ)))‖ ≤ Real.sqrt M := by
      intro p
      rw [hL1, norm_mul]
      have hs : ‖(∏ τ, ∏ j, (((Equiv.Perm.sign (p τ j) : ℤˣ) : ℤ) : ℂ))‖ = 1 := by
        rw [norm_prod]
        refine Finset.prod_eq_one fun τ _ => ?_
        rw [norm_prod]
        refine Finset.prod_eq_one fun j _ => ?_
        rcases Int.units_eq_one_or (Equiv.Perm.sign (p τ j)) with h | h <;> simp [h]
      rw [hs, one_mul]
      apply Real.le_sqrt_of_sq_le
      have := GlobalTheory.T.monomialDeriv_cauchy_bound_gaussianGrowth D a d G S A B hA hB hS hG hbd (expo D T p) (fun k =>
        le_trans (by exact_mod_cast expo_le D T p k) (hn k.1))
      rwa [expo_sum] at this
    have hcard : (Fintype.card (∀ τ, Fin (n τ) → Equiv.Perm (Fin a)) : ℝ) =
        (a.factorial : ℝ) ^ (∑ τ, n τ) := by
      simp [Fintype.card_pi, Fintype.card_perm, Finset.prod_pow_eq_pow_sum]
    have hle : ‖L (minorPol D T)‖ ≤ (a.factorial : ℝ) ^ (∑ τ, n τ) * Real.sqrt M := by
      rw [minorPol_eq, map_sum]
      refine (norm_sum_le _ _).trans ?_
      refine (Finset.sum_le_sum fun p _ => hterm p).trans ?_
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    rw [h0]
    calc _ ≤ ((a.factorial : ℝ) ^ (∑ τ, n τ) * Real.sqrt M) ^ 2 := by gcongr
      _ = _ := by rw [mul_pow, Real.sq_sqrt hM0]

end GlobalTheory.MinorBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorConjugateTangentSpacePadZeroColumnsStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylorConjugate_tangentSpacePadZeroColumns : ∀ (D : D7) (N N' m : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D (N + m) N' → ℂ), Differentiable ℂ G → fnConj D M ρ (fun z : VC D N N' => G (pad D m z)) = fun z => fnConj D M ρ G (pad D m z) := by
  first | exact @GlobalTheory.ConjRestrict.fnConj_pad | exact GlobalTheory.ConjRestrict.fnConj_pad | (intros; apply GlobalTheory.ConjRestrict.fnConj_pad <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaIntertwinerPairEqSumCorrespondingRepresentaStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaIntertwiner_pair_eq_sum_corresponding_representatives : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (A₁ A₂ A₁' A₂' : AddSubgroup (VC D N N')) (F F' : VC D N N' → ℂ) (R : VC D N N' → VC D N N' → Prop), (A₁.addSubgroupOf A₂).FiniteIndex → RepInd D T A₁ A₂ F → RepInd D T' A₁' A₂' F' → (∀ x ∈ A₂, ∃ x' ∈ A₂', R x x') → (∀ x' ∈ A₂', ∃ x ∈ A₂, R x x') → (∀ x x' y y', R x x' → R y y' → (x - y ∈ A₁ ↔ x' - y' ∈ A₁')) → ∃ (n : ℕ) (x x' : Fin n → VC D N N'), (∀ i, x i ∈ A₂ ∧ x' i ∈ A₂' ∧ R (x i) (x' i)) ∧ Iop D T A₁ A₂ F = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T (x i) F z) ∧ Iop D T' A₁' A₂' F' = (fun z => ((Real.sqrt (n : ℝ) : ℝ) : ℂ)⁻¹ * ∑ i, aU D T' (x' i) F' z) := by
  first | exact @GlobalTheory.ThetaConj.IopRepr.iop_pair | exact GlobalTheory.ThetaConj.IopRepr.iop_pair | (intros; apply GlobalTheory.ThetaConj.IopRepr.iop_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaOddPrimePhaseConjInvariantStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaOddPrimePhase_conj_invariant : ∀ (D : D7) (T T' : Tor D) (N N' : ℕ) (x x' : VC D N N') (σ : (⊤ : IntermediateField ℚ ℂ) →ₐ[ℚ] ℂ) (p k : ℕ) (m : ℤ), p.Prime → p ≠ 2 → (p : ℝ) ^ k * qH D T x = (m : ℝ) → cj ⊤ σ (wdPh D T x) = wdPh D T' x' → wPh D T p x = (-1 : ℂ) ^ m ∧ wPh D T' p x' = (-1 : ℂ) ^ m := by
  first | exact @GlobalTheory.GalThetaSign.wPh_conj | exact GlobalTheory.GalThetaSign.wPh_conj | (intros; apply GlobalTheory.GalThetaSign.wPh_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationCombPeriodicTwiceLevelStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTranslation_comb_periodic_twice_level : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A : AddSubgroup (VC D N N')), (∀ x ∈ A, ∀ y ∈ A, ∃ m : ℤ, (Hf D T x y).im = m) → (∀ x ∈ A, ∃ m : ℤ, qH D T x = m) → ∀ (k : ℕ) (c : Fin k → ℂ) (t : Fin k → VC D N N') (e₀ : VC D N N' → ℂ) (x : VC D N N') (m₀ : ℕ), e₀ ∈ ThSp D T A → m₀ • x ∈ A → (∀ i, m₀ • t i ∈ A) → ∀ l ∈ A, U D T (x + (2 * m₀) • l) (comb D T c t e₀) = U D T x (comb D T c t e₀) ∧ wdPh D T (x + (2 * m₀) • l) = wdPh D T x := by
  first | exact @GlobalTheory.GalTheta.Period.period | exact GlobalTheory.GalTheta.Period.period | (intros; apply GlobalTheory.GalTheta.Period.period <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedTranslateClassInvariantOfMemThetaSpaceStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTranslateClassInvariant_of_mem_thetaSpace : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (A₁ A₂ : AddSubgroup (VC D N N')) (F : VC D N N' → ℂ), (∀ x ∈ A₂, ∃ m : ℤ, qH D T x = m) → (∀ x ∈ A₂, ∀ y ∈ A₂, ∃ m : ℤ, (Hf D T (w0 D • x) y).im = m) → F ∈ ThSp D T A₁ → RepInd D T A₁ A₂ F := by
  first | exact @GlobalTheory.ThetaConj.repInd_of_thSp | exact GlobalTheory.ThetaConj.repInd_of_thSp | (intros; apply GlobalTheory.ThetaConj.repInd_of_thSp <;> assumption)
end

