import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0044
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0168
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0127
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2303
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2204
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0502
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0453
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2455
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2488
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0135

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLocusExponentLeOscillationNonTypePrime
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RefAway

theorem vLa_nat_eq_zero {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {N : ℕ}
    (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) : vLa la (N : K) = 0 := by
  rw [vLa, ← map_natCast (algebraMap (𝓞 K) K) N, HeightOneSpectrum.valuation_of_algebraMap,
    (la.intValuation_eq_one_iff_mem_primeCompl _).2 hN]
  simp

theorem vLa_nat_pos {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {N : ℕ} (h0 : N ≠ 0)
    (hN : ((N : ℕ) : 𝓞 K) ∈ la.asIdeal) : 0 < vLa la (N : K) := by
  have h1 : la.valuation K (N : K) < 1 := by
    rw [← map_natCast (algebraMap (𝓞 K) K) N]
    exact (la.valuation_lt_one_iff_mem _).2 hN
  have h2 : la.valuation K (N : K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast h0
  have h3 := (WithZero.log_lt_log h2 one_ne_zero).2 h1
  rw [WithZero.log_one] at h3
  unfold vLa
  omega

theorem isUnit_nat {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (S : CDVR)
    (io : K →+* S.Fr) (e : ℕ) (ho : OverLa la S.V io e) (N : ℕ) (hN : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal) :
    IsUnit ((N : ℕ) : S.V) := by
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hN (by simp)
  have h3 := ho.2 (N : K)
  rw [vLa_nat_eq_zero la hN, mul_zero, map_natCast, ← map_natCast (algebraMap S.V S.Fr)] at h3
  have hx : algebraMap S.V S.Fr (N : S.V) ≠ 0 := by
    rw [Ne, IsFractionRing.to_map_eq_zero_iff]
    exact_mod_cast hN0
  have hne := valV_ne_zero (V := S.V) hx
  have h4 : valV S.V (algebraMap S.V S.Fr (N : S.V)) = 1 := by
    unfold vV at h3
    rw [← WithZero.exp_log hne, neg_eq_zero.1 h3, WithZero.exp_zero]
  unfold valV at h4
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl] at h4
  by_contra hu
  exact h4 ((IsLocalRing.mem_maximalIdeal _).2 hu)

theorem nat_not_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {p N : ℕ}
    (hp : ((p : ℕ) : 𝓞 K) ∈ la.asIdeal) (h : Nat.Coprime p N) : ((N : ℕ) : 𝓞 K) ∉ la.asIdeal := by
  intro hN
  obtain ⟨u, v, huv⟩ := (Nat.isCoprime_iff_coprime.2 h).map (Int.castRingHom (𝓞 K))
  simp only [eq_intCast, Int.cast_natCast] at huv
  exact la.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ la.asIdeal.add_mem (la.asIdeal.mul_mem_left _ hp) (la.asIdeal.mul_mem_left _ hN)))

theorem vV_nat_eq {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {S : CDVR}
    {io : K →+* S.Fr} {e : ℕ} (ho : OverLa la S.V io e) (p : ℕ) :
    vV S.V (p : S.Fr) = (e : ℤ) * vLa la (p : K) := by
  rw [← ho.2, map_natCast]

theorem le_nval_place {K : Type} [Field K] [NumberField K] {la : HeightOneSpectrum (𝓞 K)} {S : CDVR}
    {io : K →+* S.Fr} {e : ℕ} (ho : OverLa la S.V io e) {p : ℕ} (hp : 0 < vLa la (p : K)) (A : ℕ) (x : S.Fr)
    (h : ((A : ℝ) : EReal) ≤ nval S.V (vV S.V (p : S.Fr)).toNat x) :
    (((vLa la (p : K) * A : ℤ) : ℝ) : EReal) ≤ nval S.V e x := by
  by_cases hx : x = 0
  · rw [hx, nval_zero]; exact le_top
  have he : (0 : ℤ) < e := by exact_mod_cast ho.1
  have h1 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℝ) = (e : ℝ) * (vLa la (p : K) : ℝ) := by
    have h2 : (((vV S.V (p : S.Fr)).toNat : ℕ) : ℤ) = (e : ℤ) * vLa la (p : K) := by
      rw [Int.toNat_of_nonneg, vV_nat_eq ho]
      rw [vV_nat_eq ho]; positivity
    exact_mod_cast h2
  have he' : (0 : ℝ) < e := by exact_mod_cast ho.1
  have hp' : (0 : ℝ) < (vLa la (p : K) : ℝ) := by exact_mod_cast hp
  rw [nval_of_ne hx, EReal.coe_le_coe_iff] at h ⊢
  rw [h1, le_div_iff₀ (by positivity)] at h
  rw [le_div_iff₀ he']
  push_cast
  linarith

theorem coprime_type (D : D7) : Nat.Coprime (D.host.g 0 * D.host.g 1) (D.host.QS * D.host.q * D.host.d) := by
  have h (k : Fin 2) : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
    have hc := D.ntypes.g_cond k
    have h1 : Nat.Coprime (D.host.g k) (D.host.QS * D.host.q * D.host.d) := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hc, Nat.gcd_one_left]
    exact h1
  exact Nat.Coprime.mul_left (h 0) (h 1)

theorem err_le (R N ρ u Dg φ c r v g₀ g₁ : ℝ) (hR : 0 ≤ R) (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ N) (hu : 0 ≤ u) (hr : 0 < r)
    (hv : 0 < v) (hg₀ : 0 < g₀) (hg₁ : 1 ≤ g₁) (hφ : 0 ≤ φ) (hc : R * N ^ 3 * (u + 2 * Dg ^ 2) / g₀ ≤ c) :
    Dg ^ 2 * (R * ρ ^ 3 * (r * φ)) / (g₀ * g₁) / (r * v) ≤ c * φ / v := by
  have hN : 0 ≤ N := hρ0.trans hρ
  calc Dg ^ 2 * (R * ρ ^ 3 * (r * φ)) / (g₀ * g₁) / (r * v)
      ≤ Dg ^ 2 * (R * N ^ 3 * (r * φ)) / (g₀ * 1) / (r * v) := by gcongr
    _ = R * N ^ 3 * Dg ^ 2 / g₀ * φ / v := by field_simp
    _ ≤ R * N ^ 3 * (u + 2 * Dg ^ 2) / g₀ * φ / v := by
      gcongr
      nlinarith [sq_nonneg Dg]
    _ ≤ _ := by gcongr

theorem refExp_le_of_oscLe : ∀ (D : D7) (T : Core D), LawsM T → ∀ (_ : ErrX D) (j : ℕ), InR D j → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (cst : ℝ), Dom a n → LastPos (T.Q.Dw j) a → ∑ f : Lt1 (T.Q.Dw j), 2 * rk f ≤ n → 2 * D.R.r ≤ n → JetNum D (DF (T.Q.Dw j) a) cst → ∀ (q : ℕ) [Fact q.Prime], (∀ k, q ≠ D.host.g k) → ∀ b : ℝ, OscLe (T.Q.Xo j) T.Q.c q (gap (T.Q.Dw j) a) b → refExp_vp (T.U j) cst (wtZ a n) q ≤ (b : EReal) := by
  intro D T hL EX j hj a n cst hD hLP hs hr hJ q hq' hq b hO
  letI := T.Q.H.starRing
  have hqp : q.Prime := hq'.out
  refine (refExp_vp_le_iff _).2 fun la S io e ho y hy φ hφ => ?_
  obtain ⟨st, nab, hnab⟩ := GlobalTheory.CanonConn.exists_isNab_uncond _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c
  obtain rfl := GlobalTheory.PowGerm.starSt _ T.Q.H st hnab.1
  obtain ⟨A, hA⟩ := hO la
  obtain ⟨P₁, hP₁, hPB⟩ := GlobalTheory.T.exists_harmonicPolynomial_localDepth_between D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c q la a hD.1 n hs _ _ hA
  obtain ⟨S', io', y', r, C, P, hy', hr0, hC, hP, hφ', hov, hvm, hsc⟩ :=
    GlobalTheory.T.exists_finiteExtension_uniformisedChart_scale _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S io y hy φ hφ
  have ho' := hov la.1 e ho
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible S'.V
  obtain ⟨⟨Q, hQ⟩, -⟩ := GlobalTheory.PowData.exists_powData _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' C P ϖ hϖ
  obtain ⟨ρ, hρ, hSB⟩ := GlobalTheory.T.exists_short_periodLattice_basis_balanced_slope _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c S' io' y' _ hφ' C P ϖ hϖ Q hQ
  obtain ⟨⟨α, hα1, hα2⟩, -⟩ := GlobalTheory.HalfGen.half_principal_and_split D T hL EX
  obtain ⟨π, π', hsplit⟩ := GlobalTheory.SplitLevel.level_halfSplit D T hL EX
  have hM : T.Q.l.M = D.host.g 0 * D.host.g 1 := hL.pins.2.1.1
  have hcop : Nat.Coprime q T.Q.l.M := by
    rw [hM]
    exact Nat.Coprime.mul_right ((Nat.coprime_primes hqp (D.host.g_prime 0)).2 (hq 0))
      ((Nat.coprime_primes hqp (D.host.g_prime 1)).2 (hq 1))
  have hMu : IsUnit ((T.Q.l.M : ℕ) : S'.V) := isUnit_nat la.1 S' _ _ ho' _ (nat_not_mem la.1 la.2 hcop)
  have hr1 : 1 ≤ D.R.r := by
    have h1 := D.R.two_le_m
    have h2 := D.R.m_add_three_le_k
    unfold Ranks.r; omega
  have hn1 : 1 ≤ n := by omega
  have hρN : ρ ≤ 2 * D.R.f * D.R.m := by
    refine hρ.trans ?_
    rw [GlobalTheory.DepthLink.finrank_host D, (hL.pins.2.2.2 j hj).2.1]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)
  have hρN' : (ρ : ℝ) ≤ 2 * D.R.f * D.R.m := by exact_mod_cast hρN
  have hg0 : 2 ≤ D.host.g 0 := (D.host.g_prime 0).two_le
  have hg1 : 2 ≤ D.host.g 1 := (D.host.g_prime 1).two_le
  have hle : D.host.g 0 ≤ T.Q.l.M := hM ▸ Nat.le_mul_of_pos_right _ (by omega)
  have hg0' : (2 : ℝ) ≤ D.host.g 0 := by exact_mod_cast hg0
  have hg1' : (2 : ℝ) ≤ D.host.g 1 := by exact_mod_cast hg1
  have hle' : (D.host.g 0 : ℝ) ≤ (T.Q.l.M : ℕ) := by exact_mod_cast hle
  have hDM : (DF (T.Q.Dw j) a : ℝ) * (2 * Real.sqrt ρ) < (T.Q.l.M : ℕ) := by
    refine lt_of_le_of_lt ?_ ((hJ 0).2.1.trans_le hle')
    gcongr

  have hε : 0 < vLa la.1 (q : T.Q.c.F) := vLa_nat_pos la.1 hqp.ne_zero la.2
  have hv0 : 0 < vV S.V (q : S.Fr) := by
    rw [vV_nat_eq ho]
    exact mul_pos (by exact_mod_cast ho.1) hε
  obtain ⟨v, hv⟩ : ∃ v : ℕ, vV S.V (q : S.Fr) = v := ⟨_, (Int.toNat_of_nonneg hv0.le).symm⟩
  have hvpos : 0 < v := by omega
  have hv' : (vV S'.V (q : S'.Fr)).toNat = r * v := by
    rw [hvm q hqp.ne_zero, hv, ← Nat.cast_mul, Int.toNat_natCast]
  have hrv : ((r * v : ℕ) : ℤ) = ((r * e : ℕ) : ℤ) * vLa la.1 (q : T.Q.c.F) := by
    rw [← vV_nat_eq ho', hvm q hqp.ne_zero, hv, Nat.cast_mul]
  have hr0' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hvpos' : (0 : ℝ) < v := by exact_mod_cast hvpos

  have hup := GlobalTheory.RefSum.iInf_thRule_le_nuLocOf _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab S' io' y' C hC P hP hy' ϖ hϖ Q hQ ρ _ _ hSB
    α hα1 hα2 hMu a n (r * v) hn1 (Nat.mul_pos hr0 hvpos) ((hJ 0).1.trans hle) hDM P₁ hP₁
  have hloc := (hPB S' io' _ ho' y' hy' C T.Q.l.M).2
  rw [hv'] at hloc
  have hnum : (DF (T.Q.Dw j) a : ℝ) ^ 2 * (rr0 D * (ρ : ℝ) ^ 3 * (r * φ)) / (T.Q.l.M : ℕ) / ((r * v : ℕ) : ℝ) ≤
      cst * φ / v := by
    rw [hM, Nat.cast_mul, Nat.cast_mul]
    refine err_le (rr0 D) _ ρ _ _ φ cst r v _ _ ?_ (Nat.cast_nonneg _) hρN' ?_ hr0' hvpos' (by linarith) (by linarith)
      hφ.nonneg (hJ 0).2.2
    · unfold rr0; positivity
    · positivity
  have hinf := hup.trans (add_le_add hloc (EReal.coe_le_coe_iff.2 hnum))

  obtain ⟨m, hm, hmlow, -⟩ := GlobalTheory.ThetaLow.thetaRule_bounded_below D T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab _ _ π π' hsplit
    (coprime_type D) a n
  have hdep : depthAt_vp (T.U j) (wtZ a n) q y + ((A : ℝ) : EReal) ≤
      ⨅ (f : Rul (T.Q.Xo j) T.Q.c) (_ : ∃ x : Fin n → (T.Q.Dw j).La, IsThRule (T.Q.Xo j) T.Q.c nab x P₁ f),
        nval S'.V (r * v) (evI y' f) := by
    refine le_iInf₂ fun f ⟨x, hx⟩ => ?_
    have hf : f ∈ thGen (T.Q.Xo j) T.Q.c nab a n := ⟨x, P₁, hP₁, hx⟩
    have hcusp := (GlobalTheory.thetaRules_exist_and_cusp _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) hr1 (hL.unf j hj) nab hnab).2
      a n hD hLP f hf
    have hlow := GlobalTheory.RefSum.LowP.thRule_lower _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c nab hnab q hqp
      (hqp.coprime_iff_not_dvd.1 hcop) la a n P₁ hP₁ _ _ hPB x f hx
    obtain ⟨s, hs0, hsv, g, hg, hgs⟩ := GlobalTheory.T.cuspForm_clear_denominators_away_from_place _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r (T.U j) (wtZ a n)
      ⟨f, hcusp⟩ m hm (hmlow f hf) la.1 (vLa la.1 (q : T.Q.c.F) * A) (by
        rintro _ ⟨⟨_, S₁, io₁, e₁, ho₁, y₁, hy₁, η, hη, rfl⟩, rfl⟩
        exact le_nval_place ho₁ hε A _ (hlow S₁ io₁ e₁ ho₁ y₁ hy₁))
    have h1 : depthAt_vp (T.U j) (wtZ a n) q y ≤ nval S.V v (io s * evI y f) := by
      refine (iInf₂_le g hg).trans (le_of_eq ?_)
      show nval S.V (vV S.V (q : S.Fr)).toNat (evI y (g : Rul (T.Q.Xo j) T.Q.c)) = _
      rw [hv, Int.toNat_natCast, hgs, evI_smul]
    have h2 : nval S'.V (r * v) (io' s) = ((-(A : ℝ) : ℝ) : EReal) := by
      rw [nval_of_ne ((map_ne_zero io').2 hs0), ho'.2 s, hsv]
      congr 1
      have h3 : ((r * v : ℕ) : ℝ) = ((r * e : ℕ) : ℝ) * (vLa la.1 (q : T.Q.c.F) : ℝ) := by exact_mod_cast hrv
      have h4 : ((r * v : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (Nat.mul_pos hr0 hvpos).ne'
      rw [div_eq_iff h4, h3]
      push_cast
      ring
    rw [← hsc nab hnab a n v s f hf, nval_mul, h2] at h1
    refine (add_le_add h1 le_rfl).trans (le_of_eq ?_)
    rw [add_right_comm, ← EReal.coe_add, neg_add_cancel, EReal.coe_zero, zero_add]
  have hfin := hdep.trans hinf
  rw [hv, Int.cast_natCast]
  rw [← EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _)), ← EReal.coe_add,
    ← EReal.coe_sub] at hfin
  rw [← EReal.coe_add]
  exact hfin.trans (EReal.coe_le_coe_iff.2 (by linarith))

end GlobalTheory.RefAway

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDenominatorInOrder
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
namespace GlobalTheory.ConductorMult

theorem exists_natMul_mem_orderC : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (c : Ideal (OF E)), c ≠ ⊥ →
    ∀ x : E, ∃ n : ℕ, n ≠ 0 ∧ (n : E) * x ∈ orderC c := by
  intro E _ _ _ c hc x
  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {x}
  have hyx : IsIntegral ℤ ((y : E) * x) := by
    have := hy x (Finset.mem_singleton_self x)
    simpa [zsmul_eq_mul] using this
  have hyx' : IsIntegral ℤ ((y.natAbs : E) * x) := by
    rcases Int.natAbs_eq y with h | h
    · have : ((y.natAbs : ℕ) : E) = (y : E) := by rw [← Int.cast_natCast, ← h]
      rw [this]
      exact hyx
    · have h' : (y.natAbs : ℤ) = -y := by omega
      have : ((y.natAbs : ℕ) : E) = -(y : E) := by rw [← Int.cast_natCast, h', Int.cast_neg]
      rw [this, neg_mul]
      exact hyx.neg
  set z : 𝓞 E := ⟨(y.natAbs : E) * x, hyx'⟩ with hz
  have hN : Ideal.absNorm c ≠ 0 := mt Ideal.absNorm_eq_zero_iff.1 hc
  have hyn : y.natAbs ≠ 0 := Int.natAbs_ne_zero.2 hy0
  refine ⟨Ideal.absNorm c * y.natAbs, Nat.mul_ne_zero hN hyn, ?_⟩
  have h := GlobalTheory.EigenPair.natMul_mem_orderC c z
  have hzE : ((z : 𝓞 E) : E) = (y.natAbs : E) * x := rfl
  rw [hzE] at h
  rw [Nat.cast_mul, _root_.mul_assoc]
  exact h

end GlobalTheory.ConductorMult
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleWitnessConstantEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bundle_witness_constant_eq : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) (w : BWit q b), q.O.L.sc = K.s → w.x.R.C = b.R.T.n.cf := by
  first | exact @GlobalTheory.Mem.Top.Bl.bwit_cf_eq | exact GlobalTheory.Mem.Top.Bl.bwit_cf_eq | (intros; apply GlobalTheory.Mem.Top.Bl.bwit_cf_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleWitnessPlacesEqImageStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bundle_witness_places_eq_image : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) (w : BWit q b), q.O.L.sc = K.s → (open Classical in w.x.R.Pg = b.R.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap b.R.T.ker.seam.iE)) := by
  first | exact @GlobalTheory.Div.PgTie.pgEq_of_linked | exact GlobalTheory.Div.PgTie.pgEq_of_linked | (intros; apply GlobalTheory.Div.PgTie.pgEq_of_linked <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BundleWitnessZeroSectionEqLocalStatement
section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.Lev
open GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bundle_witness_zero_section_eq_local : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL), GlobalTheory.Fc.EvP fun _ K => ∀ (q : WPt p.s K) (c : ℝ) (b : GlobalTheory.Fc.Bundle (q.w.D q.Z) q.O c) (w : BWit q b), q.O.L.sc = K.s → HEq (w.a.Zsc (zsOf q.x.what₂.r.z.R q.x.what₂.r.z.F)).F0 (F0K K.s (q.w.D q.Z)) := by
  first | exact @GlobalTheory.Mem.Top.Bl.bundle_witness_zero_section_eq | exact GlobalTheory.Mem.Top.Bl.bundle_witness_zero_section_eq | (intros; apply GlobalTheory.Mem.Top.Bl.bundle_witness_zero_section_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalRigidifiedExtensionDeRhamClassAddSmulStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalRigidifiedExtension_deRhamClass_add_smul : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A), (∀ (c c' : primDR A) (x x' : G.RigExt), IsCan t c x → IsCan t c' x' → IsCan t (c + c') (x + x')) ∧ ∀ (r : R) (c : primDR A) (x : G.RigExt), IsCan t c x → IsCan t (r • c) (r • x) := by
  first | exact @GlobalTheory.PtExt.isCan_add_smul | exact GlobalTheory.PtExt.isCan_add_smul | (intros; apply GlobalTheory.PtExt.isCan_add_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivToWeilQDivisorAddOfEffectiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDivToWeilQDivisor_add_of_effective : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → letI := algebraΓOfHom p; ∀ (D E : CartierDiv X) (a b : ℕ), 0 < a → 0 < b → D.Eff → E.Eff → (b • D + a • E).Eff ∧ qWeil (b • D + a • E) (a * b) = qWeil D a + qWeil E b ∧ ∀ C : Closeds X, IsCompleteCurve ℂ C → (interNumRed ℂ C ![toLB (b • D + a • E)] : ℚ) / ((a * b : ℕ) : ℚ) = (interNumRed ℂ C ![toLB D] : ℚ) / a + (interNumRed ℂ C ![toLB E] : ℚ) / b := by
  first | exact @GlobalTheory.QDivSum.sum_eq | exact GlobalTheory.QDivSum.sum_eq | (intros; apply GlobalTheory.QDivSum.sum_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorPullbackSupportAndEffectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartierDivisorPullback_support_and_effective : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X), (∀ y : Y, y ∈ (pullCart s D).supp → s y ∈ D.supp) ∧ (D.Eff → (pullCart s D).Eff) := by
  first | exact @GlobalTheory.Discrepancy.pullCart_supp_and_eff | exact GlobalTheory.Discrepancy.pullCart_supp_and_eff | (intros; apply GlobalTheory.Discrepancy.pullCart_supp_and_eff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyAwayNatural
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechAway

theorem cech_one_away_natural : ∀ (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D] (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ → ∀ d : Fin n → Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E' (θ.comp ψ) = θ (d a b E ψ)) → (∀ (a b c : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → IsUnit (ψ (s c)) → d a b E ψ + d b c E ψ = d a c E ψ) → ∃ e : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → e a E' (θ.comp ψ) = θ (e a E ψ)) ∧ ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ = e b E ψ - e a E ψ := by
  first
  | exact @_root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary
  | exact _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary
  | (apply _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> assumption)
  | (intros; apply _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary ..)

end GlobalTheory.CechAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyAffineLatticeCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverHyp

theorem restrict_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op)) := by
  intro R _ X s J _ _ U hU hinf hcov
  classical
  haveI := Fintype.ofFinite J
  let B : Type := {V : X.affineOpens // ∃ i, V.1 ≤ (U i).1}
  have hne : ∀ V : B, (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).Nonempty := fun V => by
    obtain ⟨i, hi⟩ := V.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let σ : B → J := fun V => (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).inf' (hne V) id
  let u : J → B := fun i => ⟨U i, i, le_rfl⟩
  have hσ : ∀ V : B, V.1.1 ≤ (U (σ V)).1 := fun V =>
    Finset.inf'_induction (p := fun i => V.1.1 ≤ (U i).1) (hne V) id
      (fun a ha b hb => by rw [hinf]; exact le_inf ha hb) fun i hi => (Finset.mem_filter.1 hi).2
  have gc : GaloisConnection σ u := fun V i =>
    ⟨fun h => (hσ V).trans (hU h), fun h =>
      Finset.inf'_le (s := Finset.univ.filter fun i : J => V.1.1 ≤ (U i).1) (id : J → J)
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)⟩
  let incl : Bᵒᵖ ⥤ AffOp X := (Monotone.functor (f := (Subtype.val : B → X.affineOpens)) fun _ _ h ↦ h).op
  have b1 : Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) incl)) :=
    GlobalTheory.T.cech_hyper_cohomology_cover_refinement R X s J (fun i => (U i).1) hcov
  have b2 := GlobalTheory.T.hyper_cohomology_restrict_adjoint_bijective R Bᵒᵖ Jᵒᵖ (incl ⋙ OAff s) gc.monotone_u.functor.op gc.monotone_l.functor.op
    gc.adjunction.op
  have e : ∀ c, pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op) c =
      pullHyp1 (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op)
        (pullHyp1 (CoefMap.restrict (OAff s) incl) c) := fun c =>
    (pullHyp1_eq_of_natTrans (CoefMap.restrict (OAff s) hU.functor.op)
      ((CoefMap.restrict (OAff s) incl).comp (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op))
      (𝟙 _) (fun T b => mp_id (OAff s) _ b) c).trans (pullHyp1_comp _ _ c)
  have := b2.comp b1
  exact (funext e : _ = _) ▸ this

end GlobalTheory.CoverHyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerMatrixEqZeroOffConjBlocks
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LogPole

theorem ksMatrix_eq_zero_of_ne_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)), IsEigBasis TF U e v → ∀ (D : LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U) (Θ : Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1)), LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v D.1 Θ → ∀ a b, (e.symm a).1 ≠ conjEmb (e.symm b).1 → Θ a b = 0 := by
  intro E _ _ _ H Dw l Xo c TF U n e v hv D Θ hKS i k hik
  obtain ⟨htan, huq, heig⟩ := hv
  let A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(TF.Y.X, U.1) :=
    fun x => Matrix.diagonal fun j => algX TF.Y.s U.1 (embK c (e.symm j).1 x)
  have hA : ∀ x j, IsCombAtG TF.Y.t (LogKS.chart U) v (A x j) (v j ≫ (TF.Y.t.act.act x).left) := by
    intro x j
    have h := heig x (e.symm j).1 (e.symm j).2
    simp only [Sigma.eta, Equiv.apply_symm_apply] at h
    convert h using 2
    funext m
    simp only [A, Matrix.diagonal_apply, Pi.single_apply, eq_comm]
  obtain ⟨e', he'⟩ := TF.logKS U n v A htan huq hA
  have hmem : Θ ∈ LogKS.balanced H.bar A := by
    rw [(he' D Θ).1 hKS]
    exact (e' D).2
  have hd := ((LogKS.mem_balanced_diagonal H.bar
    (fun j x => algX TF.Y.s U.1 (embK c (e.symm j).1 x)) Θ).1 hmem).2
  obtain ⟨x, hx⟩ : ∃ x : 𝓞 E, embK c (e.symm i).1 x ≠ embK c ((starRingEnd ℂ).comp (e.symm k).1) x := by
    by_contra hcon
    push_neg at hcon
    apply hik
    apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
    ext y
    have h := congrArg (fun z : c.F => (z : ℂ)) (hcon y)
    simpa [embK_coe, conjEmb] using h
  have hu : IsUnit (algX TF.Y.s U.1 (embK c (e.symm i).1 x) -
      algX TF.Y.s U.1 (embK c (e.symm k).1 (H.bar x))) := by
    rw [GlobalTheory.LogKSDiv.GenKSProof.embK_bar', ← map_sub]
    exact (IsUnit.mk0 _ (sub_ne_zero.2 hx)).map _
  exact hu.mul_right_eq_zero.1 (hd x i k)

end GlobalTheory.LogPole
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeModLProjectiveStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_subscheme_mod_l_projective : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] (l : ℕ) [Fact l.Prime] [Algebra (ZMod l) Γ(Z, ⊤)], IsProjOver (strHom (ZMod l) Z) := by
  first | exact @GlobalTheory.VertProj.isProjOver_strHom_zmod | exact GlobalTheory.VertProj.isProjOver_strHom_zmod | (intros; apply GlobalTheory.VertProj.isProjOver_strHom_zmod <;> assumption)
end

