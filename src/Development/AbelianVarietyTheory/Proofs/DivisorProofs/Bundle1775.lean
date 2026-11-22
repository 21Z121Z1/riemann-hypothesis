import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Formalism.PairingDivisors.PairingDivisorProofs.Height
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.DepthTie
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1729
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0056
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0069
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0042
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0044
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0142
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1736
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricValueHeightBoundOfDenominatorsMeans
section
noncomputable section
open NumberField Polynomial IsDedekindDomain
open Formalism.DivisionValues (vw lw)
open GlobalTheory.FunObj.SqNum (IsMinPol meanVal_vw)

namespace GlobalTheory.HeightMeanValueBounds

variable {K : Type} [Field K] [NumberField K]

theorem exists_prime_mem (w : Formalism.PairingDivisionLocalBalance.Pl K) : ∃ l : ℕ, l.Prime ∧ (l : 𝓞 K) ∈ w.asIdeal := by
  set n := Ideal.absNorm w.asIdeal with hn
  have h0 : n ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hmem : (n : 𝓞 K) ∈ w.asIdeal := Ideal.absNorm_mem _
  have e : ((n : ℕ) : 𝓞 K) = ∏ p ∈ n.primeFactors, ((p : 𝓞 K)) ^ (n.factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self h0]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    push_cast; rfl
  rw [e] at hmem
  obtain ⟨p, hp, hpw⟩ := (Ideal.IsPrime.prod_mem_iff (hp := w.isPrime)).1 hmem
  exact ⟨p, Nat.prime_of_mem_primeFactors hp, w.isPrime.mem_of_pow_mem _ hpw⟩

theorem height_meanVal [StarRing K] [IsTotallyComplex K] (σ : K →+* ℂ) (β : ℂ) (p : K[X]) (n : ℕ → ℕ) (A B : ℝ)
    (hp : IsMinPol σ β p) (hβ : β ≠ 0) (halg : IsAlgebraic ℚ β)
    (hlow : ∀ l, l.Prime → GlobalTheory.CMVal.IntAt l ((l : ℂ) ^ ((12 * n l : ℕ) : ℤ) * β))
    (harch : Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| ≤ (minpoly ℚ β).natDegree * (12 * A))
    (hden : ∀ S : Finset ℕ, (∀ l ∈ S, l.Prime) → ∑ l ∈ S, (n l : ℝ) * Real.log l ≤ B) :
    (Function.support fun w : Formalism.PairingDivisionLocalBalance.Pl K => lw w * |meanVal_vw w p / 12|).Finite ∧
      ∑ᶠ w : Formalism.PairingDivisionLocalBalance.Pl K, lw w * |meanVal_vw w p / 12| ≤ A + 2 * B := by
  obtain ⟨ha0, hd0⟩ := hp.ne_zero hβ
  set a := p.coeff 0 with ha
  set d := p.natDegree with hd
  have hfin : {w : Formalism.PairingDivisionLocalBalance.Pl K | vw w a ≠ 0}.Finite := by
    have := Filter.eventually_cofinite.1
      (FractionalIdeal.finite_factors (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) a))
    simpa [vw] using this
  set S : Finset ℕ := (GlobalTheory.FunObj.SqNum.finite_primes_under (p := fun w => vw w a ≠ 0) hfin).toFinset with hSdef
  have hS : ∀ l ∈ S, l.Prime := fun l hl => by
    rw [hSdef, Set.Finite.mem_toFinset] at hl; exact hl.1
  set N0 : ℕ → ℝ := fun l => ((12 * n l * d : ℕ) : ℝ) with hN0
  have hwt : ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, 0 ≤ Formalism.PairingDivisionLocalBalance.wt S N0 w := fun w =>
    Finset.sum_nonneg fun l _ => mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l)
  have hlowv : ∀ w : Formalism.PairingDivisionLocalBalance.Pl K, -(Formalism.PairingDivisionLocalBalance.wt S N0 w) ≤ ((vw w a : ℤ) : ℝ) := by
    intro w
    by_cases h : vw w a = 0
    · rw [h]; simpa using hwt w
    · obtain ⟨l, hl, hlw⟩ := exists_prime_mem w
      have hlS : l ∈ S := by
        rw [hSdef, Set.Finite.mem_toFinset]; exact ⟨hl, w, h, hlw⟩
      have key := GlobalTheory.T.valuation_minpoly_coeff_zero_ge_of_pow_mul_integral K σ β p l (12 * n l) hp hl (hlow l hl) w hlw
      have h1 : N0 l * (vw w (l : K) : ℝ) ≤ Formalism.PairingDivisionLocalBalance.wt S N0 w :=
        Finset.single_le_sum (f := fun l => N0 l * (vw w (l : K) : ℝ))
          (fun l' _ => mul_nonneg (Nat.cast_nonneg _) (by exact_mod_cast Formalism.PairingDivisionLocalBalance.vw_natCast_nonneg w l')) hlS
      have h2 : -(N0 l * (vw w (l : K) : ℝ)) ≤ (vw w a : ℝ) := by
        have : (-(((12 * n l * d : ℕ) : ℤ) * vw w (l : K)) : ℝ) ≤ (vw w a : ℝ) := by exact_mod_cast key
        simpa [hN0] using this
      linarith
  have HC := Formalism.PairingDivisionLocalBalance.height_bound_essential K a 1 0 1 (fun _ => 0) (fun w => vw w a) S N0 ha0 one_ne_zero
    (fun w => by simp [vw, FractionalIdeal.count_one]) (fun w => by simp) (fun w => by simp) (fun l _ => by positivity) hlowv
  have hm : Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding (a ^ 12 * ((1 : K) ^ 0)⁻¹)‖) =
      12 * Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.log ‖v.embedding a‖) := by
    simp only [pow_zero, inv_one, mul_one, map_pow, norm_pow, Real.log_pow, Formalism.PairingDivisionLocalBalance.meanInf]
    rw [← Finset.mul_sum]; push_cast; ring
  rw [hm, GlobalTheory.T.meanInf_log_norm_embedding_eq_log_norm_div K a ha0] at HC

  set e := (minpoly ℚ β).natDegree with he
  have he0 : 0 < e := minpoly.natDegree_pos halg.isIntegral
  have hnorm := GlobalTheory.T.abs_norm_minpoly_coeff_zero_pow_numberField K σ β p hp halg
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hlogN : (e : ℝ) * Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| =
      ((d * Module.finrank ℚ K : ℕ) : ℝ) * Real.log |(((minpoly ℚ β).coeff 0 : ℚ) : ℝ)| := by
    have := congrArg (fun x : ℚ => Real.log (x : ℝ)) hnorm
    simpa [Real.log_pow] using this
  have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd0
  have harch' : Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| / Module.finrank ℚ K ≤ d * (12 * A) := by
    rw [div_le_iff₀ hK]
    have heR : (0 : ℝ) < e := by exact_mod_cast he0
    have : (e : ℝ) * Real.log |((Algebra.norm ℚ a : ℚ) : ℝ)| ≤ e * (d * (12 * A) * Module.finrank ℚ K) := by
      rw [hlogN]; push_cast
      have := mul_le_mul_of_nonneg_left harch (by positivity : (0 : ℝ) ≤ d * Module.finrank ℚ K)
      nlinarith
    exact le_of_mul_le_mul_left this heR
  have hsum : ∑ l ∈ S, N0 l * Real.log l = 12 * d * ∑ l ∈ S, (n l : ℝ) * Real.log l := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun l _ => ?_; simp [hN0]; ring
  have hB := hden S hS
  have hmain : ∑ᶠ w : Formalism.PairingDivisionLocalBalance.Pl K, lw w * |((vw w a : ℤ) : ℝ)| ≤ 12 * d * (A + 2 * B) := by
    have := HC.2
    rw [hsum] at this
    simp only [Nat.cast_zero, zero_mul, add_zero] at this
    nlinarith
  have efun : (fun w : Formalism.PairingDivisionLocalBalance.Pl K => lw w * |meanVal_vw w p / 12|) =
      fun w => (12 * d : ℝ)⁻¹ * (lw w * |((vw w a : ℤ) : ℝ)|) := by
    funext w
    simp only [meanVal_vw, ← ha, ← hd]
    rw [div_div, abs_div, abs_of_pos (by positivity : (0 : ℝ) < d * 12)]
    field_simp
  rw [efun]
  have hsupp : (Function.support fun w : Formalism.PairingDivisionLocalBalance.Pl K => (12 * d : ℝ)⁻¹ * (lw w * |((vw w a : ℤ) : ℝ)|)) =
      Function.support fun w : Formalism.PairingDivisionLocalBalance.Pl K => lw w * |((vw w a : ℤ) : ℝ)| :=
    by
      have h12 : (12 * d : ℝ)⁻¹ ≠ 0 := by positivity
      ext w; simp only [Function.mem_support, ne_eq, mul_eq_zero, h12, false_or]
  refine ⟨hsupp ▸ HC.1, ?_⟩
  rw [← mul_finsum]
  rw [inv_mul_le_iff₀ (by positivity)]
  exact hmain

theorem lw_nonneg [StarRing K] (w : Formalism.PairingDivisionLocalBalance.Pl K) : 0 ≤ lw w := by
  unfold lw
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have : (1 : ℝ) ≤ (Ideal.absNorm w.asIdeal : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.2 h0
  exact div_nonneg (Real.log_nonneg this) (Nat.cast_nonneg _)

theorem htLe_of_real [StarRing K] (g : Formalism.PairingDivisionLocalBalance.Pl K → ℤ) (y y' : Formalism.PairingDivisionLocalBalance.Pl K → ℝ) (z : K) (H : ℝ)
    (hg : ∀ w, g w = GlobalTheory.LeafRestExamples.truncZero (y w)) (hy' : ∀ w, y' w = vw w z + y w)
    (h1 : (Function.support fun w => lw w * |y w|).Finite) (h2 : (Function.support fun w => lw w * |y' w|).Finite)
    (s1 : ∑ᶠ w, lw w * |y w| ≤ H) (s2 : ∑ᶠ w, lw w * |y' w| ≤ H) :
    Formalism.PairingDivisionLocalBalance.HtLe g z (2 * H) := by
  have hb : ∀ w, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ lw w * |y' w| + lw w * |y w| := fun w => by
    rw [← mul_add, hg, hy']
    exact mul_le_mul_of_nonneg_left (GlobalTheory.LeafRestExamples.abs_truncZero_le (y w) (vw w z)).2 (lw_nonneg w)
  have hfin : (Function.support fun w => lw w * |y' w| + lw w * |y w|).Finite :=
    (h2.union h1).subset (Function.support_add _ _)
  refine ⟨hfin.subset fun w hw => ?_, ?_⟩
  · intro h; apply hw
    have := hb w
    have h0 : 0 ≤ lw w * |((vw w z + g w : ℤ) : ℝ)| := mul_nonneg (lw_nonneg w) (abs_nonneg _)
    simp only [Function.mem_support, ne_eq, not_not] at h ⊢
    linarith
  · calc ∑ᶠ w, lw w * |((vw w z + g w : ℤ) : ℝ)| ≤ ∑ᶠ w, (lw w * |y' w| + lw w * |y w|) :=
          finsum_le_finsum' (hfin.subset fun w hw => by
            intro h; apply hw
            have := hb w
            have h0 : 0 ≤ lw w * |((vw w z + g w : ℤ) : ℝ)| := mul_nonneg (lw_nonneg w) (abs_nonneg _)
            simp only [Function.mem_support, ne_eq, not_not] at h ⊢
            linarith) hfin (fun w => hb w)
      _ = ∑ᶠ w, lw w * |y' w| + ∑ᶠ w, lw w * |y w| := finsum_add_distrib h2 h1
      _ ≤ 2 * H := by linarith

end GlobalTheory.HeightMeanValueBounds

namespace GlobalTheory.SqTop
open GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.ChiGrid in

theorem thbSt_of_inputs : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ToricDenominator → FieldDat → TorEx → DenEx → DenSum → BetaArch → ThbSt := by
  intro hTD hFD hTor _ hDS hBA
  obtain ⟨F1, hF⟩ := hFD
  obtain ⟨F2, hT⟩ := hTor
  obtain ⟨F4, hS⟩ := hDS
  obtain ⟨F5, hB⟩ := hBA
  refine ⟨max F1 (max F2 (max F4 F5)), fun ε CF hCF => ?_⟩
  obtain ⟨hf1, hf2, hf4, hf5⟩ : F1 ≤ CF ∧ F2 ≤ CF ∧ F4 ≤ CF ∧ F5 ≤ CF := by simpa [max_le_iff] using hCF
  obtain ⟨C1, y1, h1⟩ := hF ε CF hf1
  obtain ⟨C2, y2, h2⟩ := hT ε CF hf2
  obtain ⟨C4, y4, h4⟩ := hS ε CF hf4
  obtain ⟨C5, y5, h5⟩ := hB ε CF hf5
  refine ⟨6 * max C1 (max C2 (max C4 C5)), max y1 (max y2 (max y4 y5)), fun C hC D large₂ hε hx hR T Lc μ₀ hμ G => ?_⟩
  have hC' : max C1 (max C2 (max C4 C5)) ≤ C / 6 := by linarith
  obtain ⟨hc1, hc2, hc4, hc5⟩ : C1 ≤ C / 6 ∧ C2 ≤ C / 6 ∧ C4 ≤ C / 6 ∧ C5 ≤ C / 6 := by simpa [max_le_iff] using hC'
  obtain ⟨hx1, hx2, hx4, hx5⟩ : y1 ≤ large₂.sc.x ∧ y2 ≤ large₂.sc.x ∧ y4 ≤ large₂.sc.x ∧ y5 ≤ large₂.sc.x := by simpa [max_le_iff] using hx
  have H1 := h1 (C / 6) hc1 D large₂ hε hx1 hR T Lc μ₀ hμ G
  have H2 := h2 (C / 6) hc2 D large₂ hε hx2 hR T Lc μ₀ hμ G
  have H4 := h4 (C / 6) hc4 D large₂ hε hx4 hR T Lc μ₀ hμ G
  have H5 := h5 (C / 6) hc5 D large₂ hε hx5 hR T Lc μ₀ hμ G
  dsimp only at H1 H2 H4 H5 ⊢
  intro i j s hs1 hs2 zd g hTV
  obtain ⟨hCM, hAb, hFDat, hBase, -⟩ := H1
  obtain ⟨z, hz, HD⟩ := hTD D.host.E D.what₂.Tau D.host.d (cmPhi D) s hFDat hs1
  obtain ⟨x, hx, hx0, hxc, Λ, p, hΛ, hp, hg⟩ := hTV
  set B' := bTH D (C / 6) large₂.sc.x large₂.sc.b with hB'
  have hB6 : bTH D C large₂.sc.x large₂.sc.b = 2 * (B' + 2 * B') := by rw [hB']; unfold bTH; ring
  set n : ℕ → ℕ := fun l => ⌈GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D (1 : ℝ) i j s) (condF G.pl) z l / 12⌉₊ with hn
  have hden : IsDenom G i j s (fun l => (n l : ℝ)) := ⟨z, hz, fun l _ => rfl⟩
  have hd0 : 0 < D.host.d := hFDat.1.pos
  have beta_ne : ∀ y : ℂ, y ≠ 0 → GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ y ≠ 0 := by
    intro y hy
    unfold GlobalTheory.CMVal.beta
    refine div_ne_zero (pow_ne_zero _ (mul_ne_zero ?_ hy)) (pow_ne_zero _ (Formalism.L2.Th1.F.discNeZero Λ))
    exact_mod_cast (GlobalTheory.CMVal.cmValueConst_pos D.host.E hd0 (by omega) _).ne'
  have tor_ne : ∀ c y, IsTor G i j s (fam G μ₀ i j c) y → y ≠ 0 ∧
      IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ y) := by
    intro c y hty
    obtain ⟨y', hy', hy'0, -, halg⟩ := H2 i j s hs1 hs2 c
    obtain rfl : y' = y := hy'.2.unique hty.2
    exact ⟨hy'0, halg Λ hΛ⟩
  have fam_bd : ∀ (c : Option Bool) (y : ℂ) (q : D.what₂.LL[X]), IsTor G i j s (fam G μ₀ i j c) y →
      IsMinPol D.what₂.embLL (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ y) q →
      (Function.support fun w => lw w * |meanVal_vw w q / 12|).Finite ∧
        ∑ᶠ w, lw w * |meanVal_vw w q / 12| ≤ B' + 2 * B' := by
    intro c y q hty hq
    obtain ⟨hy0, halg⟩ := tor_ne c y hty
    refine GlobalTheory.HeightMeanValueBounds.height_meanVal D.what₂.embLL _ q n B' B' hq (beta_ne y hy0) halg ?_
      (H5 i j s hs1 hs2 c y Λ hty hΛ) fun S hS => (H4 i j s hs1 hs2 _ hden S hS).2
    intro l hl
    have hT' : GlobalTheory.CMVal.IsToricSum (cmPhi D) s (kap D (1 : ℝ) i j s) (GlobalTheory.CMVal.condQ (condF G.pl) ∅)
        (fam G μ₀ i j c * 1) y := by
      simpa [GlobalTheory.CMVal.condQ] using hty.2
    have hv := ((HD (kap D (1 : ℝ) i j s) (condF G.pl) Λ (fam G μ₀ i j c) hBase hΛ hty.1 l hl ∅
      (by simp [GlobalTheory.CMVal.IsFinSetSplitPlacesCoprimeConductor]) (by simp)).2 1 y ⟨fun _ => rfl, fun _ _ => rfl⟩ hT')
    have hle : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D (1 : ℝ) i j s) (condF G.pl) z l ≤
        (((12 * n l : ℕ) : ℤ) : ℝ) / ((1 : ℕ) : ℝ) := by
      have := Nat.le_ceil (GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.betaBound_vp D.host.d s (kap D (1 : ℝ) i j s) (condF G.pl) z l / 12)
      simp only [hn] at *
      push_cast
      linarith
    simpa using hv ((12 * n l : ℕ) : ℤ) 1 one_pos hle
  obtain ⟨fin0, sum0⟩ := fam_bd none x p hx hp
  have hB0 : 0 ≤ B' := by
    have : 0 ≤ ∑ᶠ w, lw w * |meanVal_vw w p / 12| :=
      finsum_nonneg fun w => mul_nonneg (GlobalTheory.HeightMeanValueBounds.lw_nonneg w) (abs_nonneg _)
    linarith
  rw [hB6]
  refine ⟨GlobalTheory.HeightMeanValueBounds.htLe_of_real g _ _ 1 _ hg (fun w => by simp [vw, FractionalIdeal.count_one]) fin0 fin0 sum0 sum0,
    fun c => ?_⟩
  have hxc' : IsTor G i j s (fam G μ₀ i j (some c)) (D.what₂.embLL (zd c) * x) := hxc c
  obtain ⟨hy0, halg⟩ := tor_ne (some c) _ hxc'
  have hz0 : zd c ≠ 0 := fun h => hy0 (by simp [h])
  obtain ⟨qc, hqc⟩ := exists_isMinPol (σ := D.what₂.embLL) halg
  have e12 : GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ (D.what₂.embLL (zd c) * x) =
      D.what₂.embLL (zd c ^ 12) * GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D (1 : ℝ) i j s) Λ x := by
    unfold GlobalTheory.CMVal.beta; rw [map_pow]; ring
  have hqc' := hqc
  rw [e12] at hqc'
  have hmv := GlobalTheory.T.meanValuationNormOverDegree_smul_eq_add_valuation D.what₂.LL D.what₂.embLL _ (zd c ^ 12) p qc hp hqc' (beta_ne x hx0) (pow_ne_zero _ hz0)
  obtain ⟨finc, sumc⟩ := fam_bd (some c) _ qc hxc' hqc
  refine ⟨hz0, GlobalTheory.HeightMeanValueBounds.htLe_of_real g _ _ (zd c) _ hg (fun w => ?_) fin0 finc sum0 sumc⟩
  rw [hmv w, Formalism.PairingDivisionLocalBalance.vw_pow w _ hz0]
  push_cast; ring

end GlobalTheory.SqTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TriangularFrameChangeBasechangeIntegralAtComplet
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.Frames

namespace GlobalTheory.PtDegInt

open GlobalTheory.LamT

private theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

private theorem sab_comp' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {g : S₂ ⟶ S₁} (n : SABMap t₂ t₁ g)
    (m₁ : SABMap t₁ t f₁) (f₂ : S₂ ⟶ S) (h : f₂ = g ≫ f₁) : ∃ m : SABMap t₂ t f₂, m.φ = n.φ ≫ m₁.φ := by
  subst h
  exact sabComp pullCubComp E H _ _ _ t t₁ t₂ f₁ g m₁ n

private theorem sab_cancel' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S₁ S₂ : Scheme.{0}}
    {t : SAB H S} {t₁ : SAB H S₁} {t₂ : SAB H S₂} {f₁ : S₁ ⟶ S} {f₂ : S₂ ⟶ S} (m₁ : SABMap t₁ t f₁)
    (m₂ : SABMap t₂ t f₂) (g : S₂ ⟶ S₁) (h : f₂ = g ≫ f₁) : ∃ n : SABMap t₂ t₁ g, n.φ ≫ m₁.φ = m₂.φ :=
  (GlobalTheory.sabMap_cancel_and_comp_over E H S S₁ S₂ t t₁ t₂ f₁ f₂ g m₁ m₂ h).1

private theorem integral_of_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (T : CDVR) (io : c.F →+* T.Fr)
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} {x : Sp T.Fr ⟶ Xo.X} :
    letI := io.toAlgebra
    ∀ (y : FrPt Xo c T.Fr) (_ : y.x = x) (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
    LieInt T io m1 m2 y.u → SecInt T m1 m2 y.s → Integral T io y := by
  intro y hx
  subst hx
  exact integral_of T io y

theorem intPt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (𝔓 : HeightOneSpectrum (𝓞 K)) (T : CDVR) (iK : K →+* T.Fr), (∀ z : K, iK z ∈ Set.range (algebraMap T.V T.Fr) ↔ 𝔓.valuation K z ≤ 1) → letI := (iK.comp (algebraMap c.F K)).toAlgebra; ∀ (yT : FrPt Xo c T.Fr), FrMap ({ iK with commutes' := fun _ => rfl } : K →ₐ[c.F] T.Fr) y yT → ∃ (ρV : 𝓞 K →+* T.V) (_ : (algebraMap T.V T.Fr).comp ρV = iK.comp (algebraMap (𝓞 K) K)) (G : GlobalTheory.CM.PAT H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (n : SABMap G.t B.t (spMap ρV)) (n' : SABMap t' t₀ (spMap iK)) (m1' : SABMap t' Xo.univ.t yT.x) (m2' : SABMap t' G.t (spMap (algebraMap T.V T.Fr))) (_ : m1'.φ = n'.φ ≫ m1.φ) (_ : m2'.φ ≫ n.φ = n'.φ ≫ m2.φ) (C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr) (td : Ix Dw → T.Frˣ) (y' : FrPt Xo c T.Fr), (∀ σ i j, i < j → C σ i j = 0) ∧ (∀ σ i, C σ i i = (td (some ⟨σ, i⟩) : T.Fr)) ∧ FrChg C (td none : T.Fr) yT y' ∧ GlobalTheory.LamT.LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y'.u ∧ Integral T (iK.comp (algebraMap c.F K)) y' := by
  intro E _ _ _ H Dw l Xo c K _ _ _ y B t₀ m1 m2 𝔓 T iK hiK yT hyT
  letI := (iK.comp (algebraMap c.F K)).toAlgebra
  have hinj : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective _ _
  obtain ⟨ρV, hρV⟩ := exists_restrict_ringHom (algebraMap (𝓞 K) K) (algebraMap T.V T.Fr) hinj iK
    (fun r => (hiK _).2 (HeightOneSpectrum.valuation_le_one 𝔓 r))
  obtain ⟨G, n, -⟩ := (GlobalTheory.LamT.pat_pullback E H _ _ ρV B).1
  obtain ⟨_, _, _, _, _, n', -⟩ := sabPull ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (spMap iK) t₀
  have hx : yT.x = spMap iK ≫ y.x := hyT.1
  obtain ⟨m1', h1⟩ := sab_comp' n' m1 yT.x hx
  obtain ⟨k2, hk2⟩ := sab_comp' n' m2 _ rfl
  obtain ⟨m2', h2⟩ := sab_cancel' n k2 (spMap (algebraMap T.V T.Fr))
    (by rw [← spMap_comp', ← spMap_comp', hρV])
  obtain ⟨⟨g0, hg0u, hg0⟩, -⟩ := GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G.t _ yT.x m1' m2' yT rfl
  obtain ⟨a0, ha0⟩ := GlobalTheory.T.exists_unit_integral_generator_principal_local_model E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G _ yT.x m1' m2' yT rfl
  choose k hk using fun σ => GlobalTheory.T.exists_integral_unimodular_mul_lowerTriangular_of_det_ne_zero T.V T.Fr (Dw.mult σ) (g0 σ) (hg0u σ).ne_zero
  have hkdet : ∀ σ, IsUnit (((k σ).map (algebraMap T.V T.Fr))).det := fun σ => by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (hk σ).1.map _
  let C : ∀ σ : E →+* ℂ, Matrix (Fin (Dw.mult σ)) (Fin (Dw.mult σ)) T.Fr :=
    fun σ => (k σ).map (algebraMap T.V T.Fr) * g0 σ
  have hCdet : ∀ σ, IsUnit (C σ).det := fun σ => by
    simp only [C, Matrix.det_mul]
    exact (hkdet σ).mul (hg0u σ)
  have hlow : ∀ σ i j, i < j → C σ i j = 0 := fun σ i j hij => (hk σ).2 i j hij
  have hdiag : ∀ σ i, C σ i i ≠ 0 := fun σ i => by
    have hd : (C σ).det = ∏ j, C σ j j :=
      Matrix.det_of_lowerTriangular _ (fun a b hab => hlow σ a b hab)
    have hne : (C σ).det ≠ 0 := (hCdet σ).ne_zero
    rw [hd] at hne
    exact Finset.prod_ne_zero_iff.1 hne i (Finset.mem_univ _)
  let td : Ix Dw → T.Frˣ := fun o => o.elim a0 (fun p => Units.mk0 (C p.1 p.2 p.2) (hdiag p.1 p.2))
  obtain ⟨y', hy', hyu⟩ := existsUnique_frChg E H Dw l Xo c T.Fr yT C a0 hCdet
  obtain ⟨y0, hy0, -⟩ := existsUnique_frChg E H Dw l Xo c T.Fr yT g0 a0 hg0u
  obtain ⟨y1, hy1, -⟩ := existsUnique_frChg E H Dw l Xo c T.Fr y0 (fun σ => (k σ).map (algebraMap T.V T.Fr)) 1 hkdet
  have hc := (frChg_refl_and_comp E H Dw l Xo c T.Fr yT y0 y1).2 g0 _ (a0 : T.Fr) _ hy0 hy1
  have h1y : y1 = y' := hyu y1 (by simpa [C] using hc)
  have hL0 : LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y0.u := hg0 a0 y0 hy0
  have hL1 : LieInt T (iK.comp (algebraMap c.F K)) m1' m2' y1.u :=
    (GlobalTheory.T.exists_integralEigenbasis_of_frame_at_localModel E H Dw l Xo c T (iK.comp (algebraMap c.F K)) G.t _ yT.x m1' m2' y0 hy0.1).2 hL0 k _ y1
      (fun σ => (hk σ).1) hy1
  rw [h1y] at hL1
  refine ⟨ρV, hρV, G, _, n, n', m1', m2', h1, h2.trans hk2, C, td, y', hlow, fun σ i => rfl, hy', hL1, ?_⟩
  exact integral_of_eq T (iK.comp (algebraMap c.F K)) y' hy'.1 m1' m2' hL1 (ha0 C y' hy')

end GlobalTheory.PtDegInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistOnlyRamifiedPlacePrimeResidueDvdNorm
section
open NumberField IsDedekindDomain GlobalTheory.CMVal Formalism.BasicNotions Formalism.IndefR.Links GlobalTheory.ChiGrid GlobalTheory.FunObj.SqNum

namespace GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_quot_of_isConjPl {D : D7} {P P' : HeightOneSpectrum (𝓞 D.host.E)} (h : Formalism.IndefR.Lev.IsConjPl P P') :
    Nat.card (𝓞 D.host.E ⧸ P'.asIdeal) = Nat.card (𝓞 D.host.E ⧸ P.asIdeal) := by
  let σ : 𝓞 D.host.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv (starRingAut : D.host.E ≃+* D.host.E)
  have hle : P.asIdeal.map σ ≤ P'.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hc
    obtain ⟨c', h1, h2⟩ := h c hc
    have e : σ c = c' := RingOfIntegers.ext h2.symm
    show σ c ∈ P'.asIdeal
    rw [e]; exact h1
  have hmax : (P.asIdeal.map σ).IsMaximal := Ideal.map_isMaximal_of_equiv σ (hp := P.isMaximal)
  have e : P'.asIdeal = P.asIdeal.map σ := (hmax.eq_of_le P'.isPrime.ne_top hle).symm
  exact (Nat.card_congr (Ideal.quotientEquiv P.asIdeal P'.asIdeal σ e).toEquiv).symm

theorem twist_ram_prime_dvd_Qn : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ → ∀ (i j : Fin D.R.m) (t : T) (w : HeightOneSpectrum (𝓞 D.host.E)), ¬ (Lc.xiH t).UnrAt w → (nuH G μ₀ i j).UnrAt w → ∃ q : ℕ, q.Prime ∧ Nat.card (𝓞 D.host.E ⧸ w.asIdeal) = q ∧ q ∣ GlobalTheory.SqTop.Qn G t ∧ ∃ w' ∈ GlobalTheory.FunObj.locPl G t, Ideal.absNorm w'.asIdeal = q := by
  classical
  intro D T Lc sc G μ₀ hL i j t w hxi hnu

  have hS0 : w.under (𝓞 D.host.F) ∉ G.pl.S0 := by
    intro hS
    have hv := (Model.isValChar_nu hL G i j (s := 0) (Nat.zero_le _)).1
    have hE := hv.2.2.2 (w.under (𝓞 D.host.F)) w rfl
    have hexp := (hE.2 (Finset.notMem_empty _) 0).1 ((Formalism.L2.Host.HChar.unrAt_iff _ _).1 hnu)
    rw [Model.expIn_condF, if_pos hS, condExp] at hexp
    split_ifs at hexp <;> omega

  obtain ⟨PP, hPP, hw⟩ : ∃ PP ∈ Lc.Q t, w = PP ∨ Formalism.IndefR.Lev.IsConjPl PP w := by
    rcases (hL.Q_ram t w).1 hxi with h | ⟨PP, h, hc⟩
    · exact ⟨w, h, Or.inl rfl⟩
    · exact ⟨PP, h, Or.inr hc⟩
  have hunder : PP.under (𝓞 D.host.F) = w.under (𝓞 D.host.F) := by
    rcases hw with rfl | hc
    · rfl
    · exact GlobalTheory.LevelPlaces.under_eq_of_isConjPl hc
  have hW0 : PP ∉ G.pl.W0 := by
    intro h
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 h
    apply hS0
    rw [← hunder, G.pl.under_w hv]
    exact hv
  have hloc : PP ∈ GlobalTheory.FunObj.locPl G t := Finset.mem_union_right _ hPP
  have htw : PP ∈ twPl G t := Finset.mem_filter.2 ⟨hloc, hW0⟩
  obtain ⟨⟨q, hq, hcard, -, -⟩, -⟩ := hL.Q_pl t PP hPP
  have hnorm : Ideal.absNorm PP.asIdeal = q := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, ← hcard]
  refine ⟨q, hq, ?_, ?_, PP, hloc, hnorm⟩
  · rcases hw with rfl | hc
    · exact hcard
    · rw [card_quot_of_isConjPl hc]; exact hcard
  · rw [← hnorm]
    exact Finset.dvd_prod_of_mem _ htw

end GlobalTheory.SqTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceUnderNotNonSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.SqTop
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitTwistPlaces

theorem not_nonSplitAt : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T), Lc.Is μ₀ → ∀ (t : T) (v : HeightOneSpectrum (𝓞 D.host.F)) (e : AF D.host.F), IsPlaceIdem D v e → ∀ PP ∈ Lc.Q t, PP.under (𝓞 D.host.F) = v → ¬ GlobalTheory.WeilParts.NonSplitAt D v e := by
  intro D T Lc sc G μ₀ hμ t v e he PP hPP hv hns
  obtain ⟨f, hf⟩ := GlobalTheory.ParahoricLift.exists_isIdemAt ((hμ.Q_pl t PP hPP).2 PP hPP)
  exact GlobalTheory.AdTh.RecPair.under_ne hf hns hv

end GlobalTheory.SplitTwistPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlacesUnderPrimeNotMemOfNormCoprime
section
open NumberField IsDedekindDomain
open Classical

theorem GlobalTheory.twPl_under_not_mem_prime : ∀ {D : Formalism.BasicNotions.D7} {T : Type} {L : Formalism.IndefR.Links.LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} (G : GlobalTheory.ChiGrid.GridData L sc) (t : T) {l : ℕ}, l.Prime → ∀ {w : Formalism.PairingDivisionLocalBalance.Pl D.what₂.LL}, (l : 𝓞 D.what₂.LL) ∈ w.asIdeal → (GlobalTheory.SqTop.Qn G t : 𝓞 D.what₂.LL) ∉ w.asIdeal → ∀ q ∈ ((GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F)), (l : 𝓞 D.host.F) ∉ q.asIdeal := by
  intro D T L sc G t l hl w hlw hQ q hq hlq
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
  have hlP : ((l : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    have h := hlq
    simp only [HeightOneSpectrum.under] at h
    have : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (l : 𝓞 D.host.F) ∈ P.asIdeal := h
    simpa using this
  have hdvd : l ∣ Ideal.absNorm P.asIdeal := by
    have h1 := Ideal.absNorm_dvd_norm_of_mem hlP
    have h2 : ((l : ℕ) : 𝓞 D.host.E) = algebraMap ℤ (𝓞 D.host.E) (l : ℤ) := by simp
    rw [h2, Algebra.norm_algebraMap] at h1
    have h3 : Ideal.absNorm P.asIdeal ∣ l ^ Module.finrank ℤ (𝓞 D.host.E) := by
      have := Int.natAbs_dvd_natAbs.mpr h1
      simpa [Int.natAbs_pow] using this
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hl).mp h3
    have hne : Ideal.absNorm P.asIdeal ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact P.isPrime.ne_top
    rcases k with _ | k
    · rw [pow_zero] at hk; exact absurd hk hne
    · rw [hk]; exact dvd_pow_self l (Nat.succ_ne_zero k)
  have hQd : l ∣ GlobalTheory.SqTop.Qn G t :=
    dvd_trans hdvd (Finset.dvd_prod_of_mem _ hP)
  obtain ⟨k, hk⟩ := hQd
  apply hQ
  rw [hk, Nat.cast_mul]
  exact w.asIdeal.mul_mem_right _ hlw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitBlockCosetThetaVectorMemThetaFunctionsStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitBlockCosetThetaVector_mem_thetaFunctions : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (o a d : ℕ) (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → cosetV D δ 𝔪 o a d e0 ∈ TT D (tor0 D ⊤ δ) a d := by
  first | exact @GlobalTheory.FunObj.CosetTT.cosetV_mem_TT | exact GlobalTheory.FunObj.CosetTT.cosetV_mem_TT | (intros; apply GlobalTheory.FunObj.CosetTT.cosetV_mem_TT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicHeightBlockDiagonalEmbeddingLeMulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicHeight_blockDiagonalEmbedding_le_mul : ∀ {D : D7} (A B : HSp D) {d : ℕ} (e : Fin A.rank ⊕ Fin B.rank ≃ Fin d) {J : Matrix (Fin d) (Fin d) D.host.E}
    (hJ : J = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram A B e) (g : GA D A) (g₁ : GA D B),
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ht (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blkU A B e hJ (g, g₁)) : ℝ) ≤ GlobalTheory.Grow.height A g * GlobalTheory.Grow.height B g₁ := by
  first | exact @GlobalTheory.BlockHeight.ht_blkU_le | exact GlobalTheory.BlockHeight.ht_blkU_le | (intros; apply GlobalTheory.BlockHeight.ht_blkU_le <;> assumption)
end

