import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0089
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0111
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0019
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0112

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsSmallPrimeOff
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem NumberField

namespace GlobalTheory.EX.OB

theorem leastOff_prime_le {K : ℕ} (hK : 0 < K) : (leastOff K).Prime ∧ leastOff K ≤ K + 1 := by
  have hp : (K + 1).minFac.Prime := Nat.minFac_prime (by omega)
  have hm : (K + 1).minFac ∈ {r : ℕ | r.Prime ∧ ¬ r ∣ K} := by
    refine ⟨hp, fun h => hp.one_lt.ne' ?_⟩
    exact Nat.dvd_one.1 ((Nat.dvd_add_right h).1 (Nat.minFac_dvd _))
  exact ⟨(Nat.sInf_mem ⟨_, hm⟩).1, (Nat.sInf_le hm).trans (Nat.minFac_le (by omega))⟩

theorem exists_small_prime_off (h : SmallPrimeOne) (C8 : ℝ) (h8 : 1 ≤ C8) : ∃ C9 : ℝ, 1 ≤ C9 ∧ ∀ N p p' : ℕ, 2 ≤ N →
    p.Prime → p'.Prime → (p : ℝ) ≤ (N : ℝ) ^ C8 → (p' : ℝ) ≤ (N : ℝ) ^ C8 →
    ∃ q1 : ℕ, q1.Prime ∧ q1 % N = 1 ∧ q1 ≠ p ∧ q1 ≠ p' ∧ q1 % (leastOff (N * (p - 1) * (p' - 1)) * N) = 1 ∧
      (q1 : ℝ) ≤ (N : ℝ) ^ C9 := by
  obtain ⟨A, hA, h⟩ := h
  refine ⟨(2 * (1 + 2 * C8)) * A, by nlinarith, fun N p p' hN hp hp' hb hb' => ?_⟩
  have h2 := hp.two_le
  have h2' := hp'.two_le
  obtain ⟨x, rfl⟩ : ∃ x, p = x + 1 := ⟨p - 1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, p' = y + 1 := ⟨p' - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hK : 0 < N * x * y := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)
  obtain ⟨hr, hrle⟩ := leastOff_prime_le hK
  set r := leastOff (N * x * y) with hrdef
  have hr2 := hr.two_le
  have hrN : 1 < r * N := by nlinarith
  have hM : 2 ≤ r * N * (x + 1) * (y + 1) := by
    have : r * N ≤ r * N * (x + 1) * (y + 1) := by
      rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ (by positivity)
    omega
  obtain ⟨q1, hq, hmod, hle⟩ := h _ hM
  have key : ∀ m : ℕ, 1 < m → m ∣ r * N * (x + 1) * (y + 1) → q1 % m = 1 := fun m hm hdv => by
    rw [← Nat.mod_mod_of_dvd q1 hdv, hmod, Nat.mod_eq_of_lt hm]
  refine ⟨q1, hq, key N (by omega) ⟨r * (x + 1) * (y + 1), by ring⟩, ?_, ?_,
    key _ hrN ⟨(x + 1) * (y + 1), by ring⟩, hle.trans ?_⟩
  · rintro rfl
    have := key (x + 1) (by omega) ⟨r * N * (y + 1), by ring⟩
    simp at this
  · rintro rfl
    have := key (y + 1) (by omega) ⟨r * N * (x + 1), by ring⟩
    simp at this
  · have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    rw [Real.rpow_mul hN0.le]
    refine Real.rpow_le_rpow (by positivity) ?_ (by linarith)
    have e1 : r ≤ N * (x + 1) * (y + 1) := by nlinarith [Nat.zero_le (N * x), Nat.zero_le (N * y)]
    have e2 : ((N * (x + 1) * (y + 1) : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 + 2 * C8) := by
      rw [show 1 + 2 * C8 = 1 + C8 + C8 by ring, Real.rpow_add hN0, Real.rpow_add hN0, Real.rpow_one,
        Nat.cast_mul, Nat.cast_mul]
      gcongr
    have e3 : (r : ℝ) ≤ (N : ℝ) ^ (1 + 2 * C8) := le_trans (by exact_mod_cast e1) e2
    rw [two_mul, Real.rpow_add hN0,
      show r * N * (x + 1) * (y + 1) = r * (N * (x + 1) * (y + 1)) by ring, Nat.cast_mul]
    gcongr

theorem chOK_of_host_field : SmallPrimeOne → ∀ (eps C5 c6 Cb cD ch : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → H.CT2 = C.CT2 → HostGood s C.P.Cpde C5 c6 Cb H q0 → WinOK s C.GK H a b → M = ⌈3 * GamS C s R ^ 2 * s.x ^ C.P.CF⌉₊ → Function.Injective c → u0 < R.n → ∃ (H' : Host R) (q1 : ℕ) (hcW : Fin M → Tau R → HCParam R) (w0 : Fin M) (h1 : _) (h2 : _) (h3 : _) (h4 : _) (h5 : _) (h6 : _) (h7 : _) (h8 : _), ChOK s C cD ch (@PreCh.mk R H' h1 h2 h3 (Fin M) _ w0 hcW h4 h5 h6 h7 h8) q1 a b c ∧ H'.TT = H.TT ∧ H'.T2 = H.T2 ∧ H'.q = H.q ∧ H'.d = H.d ∧ H'.g = H.g ∧ H'.pde = H.pde ∧ H'.pde' = H.pde' ∧ H.levelPrimes ⊆ H'.levelPrimes ∧ H'.u0.val = u0 ∧ (∀ l, hPH H' l = hPH H l) ∧ H'.toHostAx = H.toHostAx := by
  intro hSP eps C5 c6 Cb cD ch C he he1 hC hcD hch
  have h8 : 1 ≤ C.P.Cpde := hC.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨C9, h9, hq1⟩ := exists_small_prime_off hSP _ h8
  obtain ⟨x1, hx1⟩ := small_prime_lt eps _ he h8
  obtain ⟨x2, hx2⟩ := small_prime_lt eps _ he h9
  obtain ⟨x3, hx3⟩ := exists_hc_family eps cD ch C.P.Cpde he he1 hcD hch
  refine ⟨max x1 (max x2 x3), fun s R H q0 a b M c u0 hs hx hR hT hH hW hM hc hu => ?_⟩
  simp only [max_le_iff] at hx
  obtain ⟨hv, har, hT2, hT3, -, -, hdl, -, -, hBB, hgn, hpde, ⟨hp0, hmod0, hq0le, -, -⟩, hlev⟩ := hH
  have hN2 : 2 ≤ H.QS * H.q * H.d :=
    H.hyp.2.1.two_le.trans (Nat.le_mul_of_pos_left _ (Nat.mul_pos H.QS_pos H.hyp.1.pos))
  have hcast : ((H.QS * H.q * H.d : ℕ) : ℝ) = (H.QS : ℝ) * H.q * H.d := by push_cast; ring
  have hNpos : (0 : ℝ) < (H.QS : ℝ) * H.q * H.d := by
    rw [← hcast]; exact_mod_cast (by omega : 0 < H.QS * H.q * H.d)
  have hlog := hv.log_cond_le
  obtain ⟨q1, hq, hqN, hqp, hqp', hqr, hqle⟩ := hq1 _ H.pde H.pde' hN2 H.pde_prime H.pde'_prime
    (by rw [hcast]; exact hv.2.2.2.1.1) (by rw [hcast]; exact hv.2.2.2.1.2)
  rw [hcast] at hqle
  have hqX : (q1 : ℝ) < s.X' := hx2 s _ _ hs hx.2.1 hNpos hlog hqle
  have hq0X : (q0 : ℝ) < s.X' := hx1 s _ _ hs hx.1 hNpos hlog hq0le
  have hpX : (H.pde : ℝ) < s.X' := hx1 s _ _ hs hx.1 hNpos hlog hv.2.2.2.1.1
  have hpX' : (H.pde' : ℝ) < s.X' := hx1 s _ _ hs hx.1 hNpos hlog hv.2.2.2.1.2
  have hqg : ∀ i, q1 ≠ H.g i := fun i hi => by
    have hg := (hv.2.2.2.2.1 i).1
    rw [← hi] at hg
    have hXb := X'_le_b s
    have hk : (1 : ℝ) ≤ R.k := by
      have := R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ R.k)
    have hb1 : 1 ≤ s.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [s.one_lt_alt]) _)
    have h5 : s.b ≤ (R.k : ℝ) * s.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (R.k : ℝ) * s.b ≤ ((R.k : ℝ) * s.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have hK : H.ccK = ⊤ := hv.2.2.2.2.2.2.1
  have hqS : q1.Coprime H.QS := by
    have h1 : q1.Coprime (H.QS * H.q * H.d) := by
      rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hqN, Nat.gcd_one_left]
    exact (h1.coprime_mul_right_right).coprime_mul_right_right
  let H' : Host R :=
    { H with
      u0 := R.ofNat u0
      levelPrimes := insert q1 H.levelPrimes
      g_level := fun i => Finset.mem_insert_of_mem (H.g_level i)
      level_coprimeS := fun p hp => (Finset.mem_insert.1 hp).elim (fun e => e ▸ hqS) (H.level_coprimeS p)
      pde_level := ⟨Finset.mem_insert_of_mem H.pde_level.1, Finset.mem_insert_of_mem H.pde_level.2⟩
      ccK_coprime := fun p _ => by rw [hK, Ideal.absNorm_top]; exact Nat.coprime_one_left p }
  have hv' : HostVal s C.P.Cpde H' := hv
  have hmem : ∀ p ∈ H'.levelPrimes, p = q1 ∨ p = H.g 0 ∨ p = H.g 1 ∨ p = H.pde ∨ p = H.pde' ∨ p = q0 := fun p hp => by
    have hp' : p ∈ insert q1 H.levelPrimes := hp
    rw [hlev] at hp'
    simpa using hp'
  have hcond : ∀ p ∈ H'.levelPrimes, p.Prime ∧ p % (H.QS * H.q * H.d) = 1 := fun p hp => by
    have h15 : ∀ z : ℕ, z % Nat.lcm 15 (H.QS * H.q * H.d) = 1 → z % (H.QS * H.q * H.d) = 1 := fun z hz => by
      rw [← Nat.mod_mod_of_dvd z (Nat.dvd_lcm_right 15 _), hz, Nat.mod_eq_of_lt hN2]
    rcases hmem p hp with h | h | h | h | h | h <;> rw [h]
    · exact ⟨hq, hqN⟩
    · exact ⟨H.g_prime 0, har.2.1 0⟩
    · exact ⟨H.g_prime 1, har.2.1 1⟩
    · exact ⟨H.pde_prime, h15 _ hpde.1⟩
    · exact ⟨H.pde'_prime, h15 _ hpde.2⟩
    · exact ⟨hp0, hmod0⟩
  obtain ⟨hcw, hc1, hc2, hc3, hc4⟩ := hx3 s R H' (fun t => a t) (fun t => b t) hs hx.2.2 hR hv'
    (fun t => ⟨(hW t t.2).1.1, (hW t t.2).2.1⟩) (Tau R) (Equiv.refl _)
  have hM0 : 0 < M := by
    rw [hM, Nat.ceil_pos]
    have hxp : 0 < s.x := by linarith [s.one_lt_alt]
    have : 0 < GamS C s R := Real.exp_pos _
    positivity
  refine ⟨H', q1, fun u => hcw (c u), ⟨0, hM0⟩, hK, hcond, hBB, fun u τ => (hc2 _ _ τ).1, fun u τ => (hc2 _ _ τ).2.1,
    fun u τ => (hc2 _ _ τ).2.2.1, fun u τ h => ((hc2 _ _ τ).2.2.2 h).1, fun u τ h => ((hc2 _ _ τ).2.2.2 h).2,
    ⟨hR, hT, hv', ⟨har.1, har.2.1, har.2.2.1, fun p hp => cls_eq_splitK_of_cond H' (hcond p hp).2⟩, ⟨hT2, hT3⟩, hdl, hgn,
      hpde, ⟨Finset.mem_insert_self _ _, hqp, hqp', hqg, hqr⟩, fun p hp => ?_, hW, ?_, hc, fun u => hc1 (c u),
      fun u => hc3 (c u), fun u => hc4 (c u)⟩,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, Finset.subset_insert _ _, ?_, fun l => rfl, rfl⟩
  · rcases hmem p hp with h | h | h | h | h | h
    · exact Or.inr (h ▸ hqX)
    · exact Or.inl ⟨0, h⟩
    · exact Or.inl ⟨1, h⟩
    · exact Or.inr (h ▸ hpX)
    · exact Or.inr (h ▸ hpX')
    · exact Or.inr (h ▸ hq0X)
  · exact (Fintype.card_fin M).trans hM
  · exact R.toFrame.val_ofNat_of_lt hu

theorem chOK_of_host : SmallPrimeOne → ∀ (eps C5 c6 Cb cD ch : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (R : Ranks) (H : Host R) (q0 : ℕ) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), s.eps = eps → x0 ≤ s.x → RankVal s R → H.CT2 = C.CT2 → HostGood s C.P.Cpde C5 c6 Cb H q0 → WinOK s C.GK H a b → M = ⌈3 * GamS C s R ^ 2 * s.x ^ C.P.CF⌉₊ → Function.Injective c → u0 < R.n → ∃ (H' : Host R) (q1 : ℕ) (hcW : Fin M → Tau R → HCParam R) (w0 : Fin M) (h1 : _) (h2 : _) (h3 : _) (h4 : _) (h5 : _) (h6 : _) (h7 : _) (h8 : _), ChOK s C cD ch (@PreCh.mk R H' h1 h2 h3 (Fin M) _ w0 hcW h4 h5 h6 h7 h8) q1 a b c ∧ H'.TT = H.TT ∧ H'.T2 = H.T2 ∧ H'.q = H.q ∧ H'.d = H.d ∧ H'.g = H.g ∧ H'.pde = H.pde ∧ H'.pde' = H.pde' ∧ H.levelPrimes ⊆ H'.levelPrimes ∧ H'.u0.val = u0 ∧ ∀ l, hPH H' l = hPH H l := by
  intro hSP eps C5 c6 Cb cD ch C he he1 hC hcD hch
  obtain ⟨x0, h⟩ := chOK_of_host_field hSP eps C5 c6 Cb cD ch C he he1 hC hcD hch
  refine ⟨x0, fun s R H q0 a b M c u0 hs hx hR hT hH hW hM hc hu => ?_⟩
  obtain ⟨H', q1, hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10, -⟩ :=
    h s R H q0 a b M c u0 hs hx hR hT hH hW hM hc hu
  exact ⟨H', q1, hcW, w0, k1, k2, k3, k4, k5, k6, k7, k8, hCh, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10⟩

end GlobalTheory.EX.OB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FibreMassConstOfNormEqOne
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem addHaar_map_eq_of_preimage_eq {G : Type} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] (T : G ≃+ G)
    (hT : Continuous T) (hT' : Continuous T.symm) {S : Set G} (hS : MeasurableSet S)
    (hpos : μ S ≠ 0) (hfin : μ S ≠ ⊤) (hpre : T ⁻¹' S = S) : Measure.map T μ = μ := by
  haveI : (Measure.map T μ).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map μ T hT hT'
  have hk := Measure.isAddLeftInvariant_eq_smul (Measure.map T μ) μ
  set k := Measure.addHaarScalarFactor (Measure.map T μ) μ
  have hm : Measure.map T μ S = μ S := by
    rw [Measure.map_apply hT.measurable hS, hpre]
  have hk1 : k = 1 := by
    rw [hk, Measure.smul_apply] at hm
    have h1 : (k : ENNReal) * μ S = 1 * μ S := by
      rw [one_mul]
      simpa [ENNReal.smul_def] using hm
    have := (ENNReal.mul_left_inj hpos hfin).1 h1
    exact_mod_cast this
  rw [hk, hk1, one_smul]

theorem fibre_mass_const_of_norm_eq_one {K : Type} [NormedField K] [ProperSpace K]
    [MeasurableSpace K] [BorelSpace K] (hU : IsOpen {u : K | ‖u‖ = 1})
    {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure K) [ν.IsAddHaarMeasure] (q : V → K)
    (hq : Continuous q) (fib : K → Measure V)
    (hfib : IsFibreFamily μ q id Set.univ ν {c | c ≠ 0} fib) (L : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hact : ∀ u : K, ‖u‖ = 1 → ∃ T : V ≃+ V, Continuous T ∧ Continuous T.symm ∧
      (∀ x, T x ∈ L ↔ x ∈ L) ∧ ∀ x, q (T x) = u * q x) (β : K) (hβ : ‖β‖ = 1) :
    fib β (L : Set V) ≠ ⊤ ∧
      (fib β).real (L : Set V) * ν.real {u | ‖u‖ = 1} = μ.real {x | x ∈ L ∧ ‖q x‖ = 1} := by
  obtain ⟨h1, h2, h3⟩ := hfib
  have hLcl : IsClopen (L : Set V) := ⟨L.isClosed_of_isOpen hLo, hLo⟩
  have hLm : MeasurableSet (L : Set V) := hLo.measurableSet
  have hφc : Continuous ((L : Set V).indicator (fun _ => (1 : ℝ))) :=
    hLcl.continuous_indicator continuous_const
  have hφs : HasCompactSupport ((L : Set V).indicator (fun _ => (1 : ℝ))) :=
    HasCompactSupport.intro hLc (fun x hx => Set.indicator_of_notMem hx _)
  obtain ⟨hI, hC⟩ := h3 _ hφc hφs (Set.subset_univ _)
  have hG : ∀ b, ∫ v, (L : Set V).indicator (fun _ => (1 : ℝ)) v ∂(fib b)
      = (fib b L).toReal := by
    intro b
    rw [integral_indicator hLm, setIntegral_const, smul_eq_mul, mul_one]
    rfl
  simp only [hG] at hC
  have hfin : ∀ b : K, b ≠ 0 → fib b L ≠ ⊤ := by
    intro b hb
    have := (integrable_indicator_iff hLm).mp (hI b hb)
    rcases (integrableOn_const_iff (by simp)).mp this with h | h
    · simp at h
    · exact h.ne
  have hne : ∀ b : K, ‖b‖ = 1 → b ≠ 0 := by
    rintro b hb rfl
    simp at hb
  have hμ : ∀ S : Set K, MeasurableSet S → μ (L ∩ q ⁻¹' S) = ∫⁻ b in S, fib b L ∂ν := by
    intro S hSm
    have hpm : MeasurableSet (q ⁻¹' S) := hq.measurable hSm
    have hfb : ∀ b, fib b (L ∩ q ⁻¹' S) = S.indicator (fun b => fib b L) b := by
      intro b
      have hae : ∀ᵐ v ∂(fib b), q v = b := by
        have := h1 b
        rw [Set.inter_univ] at this
        exact this
      by_cases hb : b ∈ S
      · rw [Set.indicator_of_mem hb]
        refine measure_congr ?_
        filter_upwards [hae] with v hv
        apply propext
        constructor
        · exact fun h => h.1
        · exact fun h => ⟨h, show q v ∈ S from hv ▸ hb⟩
      · rw [Set.indicator_of_notMem hb]
        refine measure_mono_null ?_ hae
        intro v hv hv'
        have e : q v = b := hv'
        exact hb (e ▸ hv.2)
    have := h2 (((L : Set V) ∩ q ⁻¹' S).indicator 1) (measurable_one.indicator (hLm.inter hpm))
    simp only [Measure.restrict_univ, lintegral_indicator_one (hLm.inter hpm), hfb] at this
    rw [this, lintegral_indicator hSm]
  set U : Set K := {u : K | ‖u‖ = 1} with hUdef
  have hUm : MeasurableSet U := hU.measurableSet
  have hUc : IsCompact U := by
    have : U = Metric.sphere (0 : K) 1 := by ext; simp [hUdef]
    rw [this]; exact isCompact_sphere _ _
  have hCU : ContinuousOn (fun b => (fib b L).toReal) U := hC.mono (fun b hb => hne b hb)
  have hR : ∀ S : Set K, MeasurableSet S → S ⊆ U →
      ∫ b in S, (fib b L).toReal ∂ν = (μ (L ∩ q ⁻¹' S)).toReal := by
    intro S hSm hSU
    rw [hμ S hSm, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => ENNReal.toReal_nonneg)
      ((hCU.integrableOn_compact hUc).mono_set hSU).aestronglyMeasurable]
    congr 1
    exact setLIntegral_congr_fun hSm (fun b hb => ENNReal.ofReal_toReal (hfin b (hne b (hSU hb))))
  have hconst : ∀ t : K, ‖t‖ = 1 → (fib t L).toReal = (fib β L).toReal := by
    intro t ht
    have hu : ‖t / β‖ = 1 := by rw [norm_div, ht, hβ, div_one]
    set u := t / β with hudef
    have hu0 : u ≠ 0 := hne u hu
    obtain ⟨T, hT, hT', hTL, hTq⟩ := hact u hu
    have hTμ : Measure.map T μ = μ :=
      addHaar_map_eq_of_preimage_eq μ T hT hT' hLm
        (hLo.measure_pos μ ⟨0, L.zero_mem⟩).ne' hLc.measure_lt_top.ne (Set.ext hTL)
    let M : K ≃+ K := AddAut.mulLeft (Units.mk0 u hu0)
    have hM : ∀ x, M x = u * x := fun x => rfl
    have hMc : Continuous M := continuous_const.mul continuous_id
    have hMc' : Continuous M.symm := continuous_const.mul continuous_id
    have hMU : M ⁻¹' U = U := by
      ext x
      simp [hUdef, hM, hu]
    have hMν : Measure.map M ν = ν :=
      addHaar_map_eq_of_preimage_eq ν M hMc hMc' hUm
        (hU.measure_pos ν ⟨1, by simp [hUdef]⟩).ne' hUc.measure_lt_top.ne hMU
    let H : K ≃ₜ K := { M.toEquiv with continuous_toFun := hMc, continuous_invFun := hMc' }
    have hMe : MeasurableEmbedding M := H.measurableEmbedding
    have hCM : ContinuousOn (fun b => (fib (M b) L).toReal) U :=
      hCU.comp hMc.continuousOn (fun x hx => by rw [← hMU] at hx; exact hx)
    have hint : ∀ S : Set K, MeasurableSet S → S ⊆ U →
        ∫ b in S, (fib (M b) L).toReal ∂ν = ∫ b in S, (fib b L).toReal ∂ν := by
      intro S hSm hSU
      have hS' : MeasurableSet (M '' S) := hMe.measurableSet_image.2 hSm
      have hSU' : M '' S ⊆ U := by
        rintro _ ⟨x, hx, rfl⟩
        have := hSU hx
        rw [← hMU] at this
        exact this
      have e1 := hMe.setIntegral_map (μ := ν) (fun b => (fib b L).toReal) (M '' S)
      rw [hMν, Set.preimage_image_eq _ M.injective] at e1
      rw [← e1, hR _ hS' hSU', hR _ hSm hSU]
      congr 1
      conv_lhs => rw [← hTμ]
      rw [Measure.map_apply hT.measurable (hLm.inter (hq.measurable hS'))]
      congr 1
      ext x
      simp only [Set.mem_preimage, Set.mem_inter_iff, SetLike.mem_coe, hTL, hTq, ← hM,
        M.injective.mem_set_image]
    have hae : (fun b => (fib (M b) L).toReal) =ᵐ[ν.restrict U] fun b => (fib b L).toReal := by
      refine Integrable.ae_eq_of_forall_setIntegral_eq _ _ (hCM.integrableOn_compact hUc)
        (hCU.integrableOn_compact hUc) (fun S hSm _ => ?_)
      rw [Measure.restrict_restrict hSm]
      exact hint _ (hSm.inter hUm) Set.inter_subset_right
    have := Measure.eqOn_open_of_ae_eq hae hU hCM hCU (show β ∈ U from hβ)
    simp only [hM] at this
    rwa [hudef, div_mul_cancel₀ _ (hne β hβ)] at this
  refine ⟨hfin β (hne β hβ), ?_⟩
  have := hR U hUm subset_rfl
  rw [setIntegral_congr_fun hUm (g := fun _ => (fib β L).toReal) (fun t ht => hconst t ht),
    setIntegral_const, smul_eq_mul, mul_comm] at this
  exact this

theorem fibre_mass_mul_units_eq : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (ν : Measure (Fv F v)) [ν.IsAddHaarMeasure] (q : V → Fv F v), Continuous q → ∀ (fib : Fv F v → Measure V), IsFibreFamily μ q id Set.univ ν {c | c ≠ 0} fib → ∀ (L : AddSubgroup V), IsCompact (L : Set V) → IsOpen (L : Set V) → (∀ u : Fv F v, Valued.v u = 1 → ∃ T : V ≃+ V, Continuous T ∧ Continuous T.symm ∧ (∀ x, T x ∈ L ↔ x ∈ L) ∧ ∀ x, q (T x) = u * q x) → ∀ β : Fv F v, Valued.v β = 1 → fib β (L : Set V) ≠ ⊤ ∧ (fib β).real (L : Set V) * ν.real {u | Valued.v u = 1} = μ.real {x | x ∈ L ∧ Valued.v (q x) = 1} := by
  intro F _ _ v V _ _ _ _ _ _ _ μ _ ν _ q hq fib hfib L hLc hLo hact β hβ
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hn : ∀ u : Fv F v, Valued.v u = 1 ↔ ‖u‖ = 1 := by
    intro u
    rw [le_antisymm_iff, le_antisymm_iff, Valued.toNormedField.norm_le_one_iff,
      Valued.toNormedField.one_le_norm_iff]
  have hU : IsOpen {u : Fv F v | ‖u‖ = 1} := by
    have := IsUltrametricDist.isOpen_sphere (0 : Fv F v) (r := 1) one_ne_zero
    convert this using 1
    ext
    simp
  simp only [hn] at hact hβ ⊢
  exact fibre_mass_const_of_norm_eq_one hU μ ν q hq fib hfib L hLc hLo hact β hβ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianSpaceOppositeFormSignatureCondition
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix

namespace GlobalTheory.NegSpace

theorem hasSignature_neg_swap {n : Type} [Fintype n] [DecidableEq n] {J : Matrix n n ℂ} {p q : ℕ}
    (h : Formalism.UG.HasSignature J p q) : Formalism.UG.HasSignature (-J) q p := by
  obtain ⟨e, P, hP⟩ := h
  let s := Equiv.sumComm (Fin p) (Fin q)
  refine ⟨e.trans s, Units.map (Matrix.reindexAlgEquiv ℂ ℂ s).toRingHom.toMonoidHom P, ?_⟩
  have e1 : Formalism.UG.Jpq q p = -(Formalism.UG.Jpq p q).submatrix s.symm s.symm := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Formalism.UG.Jpq, s]
  rw [e1, ← hP, ← submatrix_mul_equiv _ _ _ s.symm, ← submatrix_mul_equiv _ _ _ s.symm, ← Matrix.neg_mul, ← Matrix.mul_neg]
  rfl

theorem sigOK_neg : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), W.SigOK → (GlobalTheory.NegSpace.neg W).SigOK := by
  intro E _ _ _ W h τ
  have e : (neg W).gram.map τ = -W.gram.map τ := Matrix.ext fun i j => map_neg τ (W.gram i j)
  rw [e]
  exact hasSignature_neg_swap (h τ)

end GlobalTheory.NegSpace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IntegralClosureCompletedCMAlgebraCompactOpen
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.CompletedOrder

theorem eq_sum_trace {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    [Algebra.IsSeparable F E] {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι F E)
    (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    z = ∑ i, Algebra.trace R (R ⊗[F] E) (z * (1 : R) ⊗ₜ[F] b i) • ((1 : R) ⊗ₜ[F] b.traceDual i) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [add_mul, map_add, add_smul, Finset.sum_add_distrib]
    rw [← hx, ← hy]
  | tmul a e =>
    have h3 : ∀ e : E, Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] e) =
        a * algebraMap F R (Algebra.trace F E e) := by
      intro e
      have h1 : a ⊗ₜ[F] e = a • ((1 : R) ⊗ₜ[F] e) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [h1, map_smul, Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
        LinearMap.trace_baseChange, smul_eq_mul]
    conv_lhs => rw [← b.traceDual.sum_repr e, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, h3, Module.Basis.traceDual_repr_apply,
      Algebra.traceForm_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one,
      ← TensorProduct.smul_tmul, mul_comm a, Algebra.smul_def]

theorem isCompact_isOpen_integralClosure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ v : HeightOneSpectrum (𝓞 F), IsCompact (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) ∧ IsOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) : Set (Fv F v ⊗[F] E)) := by
  intro F E _ _ _ _ _ σ h v
  classical
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h.2.2.1
  haveI : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  obtain ⟨s, b, hb⟩ := FiniteDimensional.exists_is_basis_integral (𝓞 F) F E
  have hb' : ∀ i, IsIntegral (v.adicCompletionIntegers F) ((1 : Fv F v) ⊗ₜ[F] b i) := by
    intro i
    have h1 : IsIntegral ℤ (b i) := isIntegral_trans (b i) (hb i)
    exact h1.map_of_comp_eq (algebraMap ℤ _) (inclR (F := F) (E := E) (Fv F v))
      (RingHom.ext_int _ _)
  have hO : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hC : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) :=
    isCompact_iff_compactSpace.2 (AdelicUnitaryTop.compactSpace_adicCompletionIntegers F v)
  have hopen : IsOpen (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :
      Set (Fv F v ⊗[F] E)) := by
    let B := Algebra.TensorProduct.basis (Fv F v) b
    have hc : Continuous B.equivFun := IsModuleTopology.continuous_of_linearMap B.equivFun.toLinearMap
    refine AddSubgroup.isOpen_of_mem_nhds
      (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring.toAddSubgroup
      (g := 0) ?_
    refine Filter.mem_of_superset (((isOpen_set_pi Set.finite_univ fun _ _ => hO).preimage hc).mem_nhds ?_) ?_
    · intro i _
      simp
    · intro z hz
      show IsIntegral _ z
      rw [← B.sum_equivFun z]
      refine IsIntegral.sum _ fun i _ => ?_
      have := (hb' i).smul (⟨_, hz i (Set.mem_univ i)⟩ : v.adicCompletionIntegers F)
      rw [Algebra.TensorProduct.basis_apply]
      exact this
  refine ⟨?_, hopen⟩
  have hclosed : IsClosed (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :
      Set (Fv F v ⊗[F] E)) :=
    AddSubgroup.isClosed_of_isOpen
      (integralClosure (v.adicCompletionIntegers F) (Fv F v ⊗[F] E)).toSubring.toAddSubgroup hopen
  have hcont : Continuous fun x : s → Fv F v => ∑ i, x i • ((1 : Fv F v) ⊗ₜ[F] b.traceDual i) := by
    fun_prop
  refine IsCompact.of_isClosed_subset ((isCompact_univ_pi fun _ => hC).image hcont) hclosed ?_
  intro z hz
  refine ⟨_, ?_, (eq_sum_trace b (Fv F v) z).symm⟩
  intro i _
  have h1 : IsIntegral (v.adicCompletionIntegers F) (z * (1 : Fv F v) ⊗ₜ[F] b i) :=
    IsIntegral.mul hz (hb' i)
  have h2 : IsIntegral (v.adicCompletionIntegers F) (sigR (Fv F v) σ (z * (1 : Fv F v) ⊗ₜ[F] b i)) :=
    h1.map ((Algebra.TensorProduct.map (AlgHom.id (Fv F v) (Fv F v)) σ).restrictScalars
      (v.adicCompletionIntegers F))
  have h3 := h1.add h2
  rw [← SelfDualLatticeCompare.trace_tensor (Fv F v) h,
    isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective _ _)] at h3
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  beta_reduce
  rw [← hy]
  exact y.2

end GlobalTheory.CompletedOrder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MeasureEqOfMoments
section
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate

namespace GlobalTheory.MomN

theorem measure_eq_of_moments : ∀ (q : ℕ) [Fact q.Prime] (κ : Type) [Fintype κ]
    (μ μ' : C(κ → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] ℂ_[q]),
    (∀ (k : ℕ) (j : Fin k → κ) (f : C(κ → ℤ_[q], ℂ_[q])),
      (∀ a, f a = ∏ l, zc (a (j l))) → μ f = μ' f) → μ = μ' := by
  intro q _ κ _ μ μ' h
  let e := Fintype.equivFin κ
  let π : C(κ → ℤ_[q], Fin (Fintype.card κ) → ℤ_[q]) :=
    ⟨fun b i => b (e.symm i), by fun_prop⟩
  let π' : C(Fin (Fintype.card κ) → ℤ_[q], κ → ℤ_[q]) :=
    ⟨fun a i => a (e i), by fun_prop⟩
  let Φ : C(Fin (Fintype.card κ) → ℤ_[q], ℂ_[q]) →L[ℂ_[q]] C(κ → ℤ_[q], ℂ_[q]) :=
    { toFun := fun G => G.comp π
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      cont := ContinuousMap.continuous_precomp π }
  have hz : (μ - μ').comp Φ = 0 := by
    refine GlobalTheory.MonomialDense.eq_zero_of_monomials q _ _ fun m k g hg => ?_
    have := h m (fun l => e.symm (k l)) (Φ g) fun b => hg (π b)
    simp [this]
  ext F
  have hF : Φ (F.comp π') = F := by
    ext b
    change F (π' (π b)) = F b
    congr 1
    funext i
    simp [π, π']
  have := congrArg (fun ν => ν (F.comp π')) hz
  simp only [ContinuousLinearMap.comp_apply, hF, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.zero_apply] at this
  exact sub_eq_zero.mp this

end GlobalTheory.MomN
end

