import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.Bundle0001
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists
import Formalism.SharpRestriction.GlobalSchurBounds.ConclusionR7abs

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.DroppingPropositionHolds
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory

private theorem eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf {G : Type*} [AddCommGroup G] (a : G) (k : ℤ)
    (hk : k • a = 0) (hlt : |k| < (addOrderOf a : ℤ)) : k = 0 :=
  Int.eq_zero_of_abs_lt_dvd (addOrderOf_dvd_iff_zsmul_eq_zero.mpr hk) hlt

private theorem sub_zsmul_eq_of_two_eqs {G : Type*} [AddCommGroup G] (a h t u₀ : G) (i j : ℤ) (s s' : ℕ)
    (e : t + i • h = s • a + u₀) (e' : t + j • h = s' • a + u₀) :
    (j - i) • h = ((s' : ℤ) - s) • a := by
  rw [sub_zsmul, sub_zsmul, natCast_zsmul, natCast_zsmul, ← sub_eq_add_neg, ← sub_eq_add_neg]
  calc j • h - i • h = (t + j • h) - (t + i • h) := by abel
    _ = (s' • a + u₀) - (s • a + u₀) := by rw [e, e']
    _ = s' • a - s • a := by abel

private theorem false_of_three_distinct_in_window {G : Type*} [AddCommGroup G] (a t h u₀ : G) (T : Finset ℕ) (L : ℕ)
    (hT : ∀ s ∈ T, 4 * L * s < addOrderOf a) (hR : Formalism.FrobeniusOrbits.NoRel T L)
    (hh : 4 * L < addOrderOf h) (i₀ i1 i2 i3 : ℤ) (s1 s2 s3 : ℕ)
    (a1 : i₀ ≤ i1) (b1 : i1 < i₀ + L) (a2 : i₀ ≤ i2) (b2 : i2 < i₀ + L)
    (a3 : i₀ ≤ i3) (b3 : i3 < i₀ + L)
    (h12 : i1 ≠ i2) (h13 : i1 ≠ i3) (h23 : i2 ≠ i3) (hs1 : s1 ∈ T) (hs2 : s2 ∈ T) (hs3 : s3 ∈ T)
    (e1 : t + i1 • h = s1 • a + u₀) (e2 : t + i2 • h = s2 • a + u₀)
    (e3 : t + i3 • h = s3 • a + u₀) : False := by
  have hL : (4 * L : ℤ) < addOrderOf h := by exact_mod_cast hh
  have hdist : ∀ (i j : ℤ) (s s' : ℕ), i₀ ≤ i → i < i₀ + L → i₀ ≤ j → j < i₀ + L → i ≠ j →
      (j - i) • h = ((s' : ℤ) - s) • a → s ≠ s' := by
    intro i j s s' hi hi' hj hj' hij e hss
    subst hss
    rw [sub_self, zero_zsmul] at e
    have h0 := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf h (j - i) e (by rw [abs_lt]; constructor <;> omega)
    omega
  have k2 := sub_zsmul_eq_of_two_eqs a h t u₀ i1 i2 s1 s2 e1 e2
  have k3 := sub_zsmul_eq_of_two_eqs a h t u₀ i1 i3 s1 s3 e1 e3
  have k23 := sub_zsmul_eq_of_two_eqs a h t u₀ i2 i3 s2 s3 e2 e3
  have n12 := hdist i1 i2 s1 s2 a1 b1 a2 b2 h12 k2
  have n13 := hdist i1 i3 s1 s3 a1 b1 a3 b3 h13 k3
  have n23 := hdist i2 i3 s2 s3 a2 b2 a3 b3 h23 k23
  have hD : ((i3 - i1) * ((s2 : ℤ) - s1) - (i2 - i1) * ((s3 : ℤ) - s1)) • a = 0 := by
    rw [sub_zsmul, ← sub_eq_add_neg, ← smul_smul, ← smul_smul, ← k2, ← k3, smul_smul, smul_smul,
      mul_comm (i3 - i1), sub_self]
  have hN : ∀ s ∈ T, 4 * (L : ℤ) * s < addOrderOf a := fun s hs => by exact_mod_cast hT s hs
  have hb1 := hN s1 hs1
  have hb2 := hN s2 hs2
  have hb3 := hN s3 hs3
  have hLn : (0 : ℤ) ≤ L := by positivity
  have hs1n : (0 : ℤ) ≤ s1 := by positivity
  have hs2n : (0 : ℤ) ≤ s2 := by positivity
  have hs3n : (0 : ℤ) ≤ s3 := by positivity
  have hy2 : 4 * (L : ℤ) * |(s2 : ℤ) - s1| < addOrderOf a := by
    rcases abs_cases ((s2 : ℤ) - s1) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hs1n, mul_nonneg hLn hs2n]
  have hy3 : 4 * (L : ℤ) * |(s3 : ℤ) - s1| < addOrderOf a := by
    rcases abs_cases ((s3 : ℤ) - s1) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hs1n, mul_nonneg hLn hs3n]
  have hx : |i3 - i1| ≤ L := by rw [abs_le]; constructor <;> omega
  have hu : |i2 - i1| ≤ L := by rw [abs_le]; constructor <;> omega
  have hxy : 4 * |(i3 - i1) * ((s2 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_right hx (abs_nonneg ((s2 : ℤ) - s1))]
  have huv : 4 * |(i2 - i1) * ((s3 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_mul]; nlinarith [mul_le_mul_of_nonneg_right hu (abs_nonneg ((s3 : ℤ) - s1))]
  have hDb : |(i3 - i1) * ((s2 : ℤ) - s1) - (i2 - i1) * ((s3 : ℤ) - s1)| < addOrderOf a := by
    rw [abs_lt]
    constructor <;>
      linarith [le_abs_self ((i3 - i1) * ((s2 : ℤ) - s1)), neg_abs_le ((i3 - i1) * ((s2 : ℤ) - s1)),
        le_abs_self ((i2 - i1) * ((s3 : ℤ) - s1)), neg_abs_le ((i2 - i1) * ((s3 : ℤ) - s1)),
        abs_nonneg ((i3 - i1) * ((s2 : ℤ) - s1)), abs_nonneg ((i2 - i1) * ((s3 : ℤ) - s1))]
  have hD0 := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf a _ hD hDb
  exact hR s1 hs1 s2 hs2 s3 hs3 n12 n13 n23 (i2 - i1) (i3 - i1)
    (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h12))) hu
    (abs_pos.mpr (sub_ne_zero.mpr (Ne.symm h13))) hx
    (fun hc => h23 (by omega)) (sub_eq_zero.mp hD0)

private theorem eq_of_zsmul_eqs_of_small_orders {G : Type*} [AddCommGroup G] (a t h u₀ : G) (T : Finset ℕ) (L : ℕ)
    (hT : ∀ s ∈ T, 4 * L * s < addOrderOf a) (hpos : 0 < addOrderOf h)
    (hh : addOrderOf h ≤ 4 * L) (i j : ℤ) (s s' : ℕ) (hs : s ∈ T) (hs' : s' ∈ T)
    (e : t + i • h = s • a + u₀) (e' : t + j • h = s' • a + u₀) : s = s' := by
  have k := sub_zsmul_eq_of_two_eqs a h t u₀ i j s s' e e'
  have hm : ((addOrderOf h : ℤ) * ((s' : ℤ) - s)) • a = 0 := by
    rw [← smul_smul, ← k, smul_smul, mul_comm, ← smul_smul, natCast_zsmul,
      addOrderOf_nsmul_eq_zero, zsmul_zero]
  have hm0 : (0 : ℤ) ≤ (addOrderOf h : ℤ) := by positivity
  have hmL : (addOrderOf h : ℤ) ≤ 4 * L := by exact_mod_cast hh
  have hLn : (0 : ℤ) ≤ L := by positivity
  have hsn : (0 : ℤ) ≤ s := by positivity
  have hsn' : (0 : ℤ) ≤ s' := by positivity
  have hb := (show 4 * (L : ℤ) * s < addOrderOf a by exact_mod_cast hT s hs)
  have hb' := (show 4 * (L : ℤ) * s' < addOrderOf a by exact_mod_cast hT s' hs')
  have hy : 4 * (L : ℤ) * |(s' : ℤ) - s| < addOrderOf a := by
    rcases abs_cases ((s' : ℤ) - s) with ⟨hc, -⟩ | ⟨hc, -⟩ <;> rw [hc] <;>
      nlinarith [mul_nonneg hLn hsn, mul_nonneg hLn hsn']
  have hz := eq_zero_of_zsmul_eq_zero_of_abs_lt_addOrderOf a _ hm (by
    rw [abs_mul, abs_of_nonneg hm0]
    nlinarith [mul_le_mul_of_nonneg_right hmL (abs_nonneg ((s' : ℤ) - s))])
  rcases mul_eq_zero.mp hz with h0 | h0 <;> omega

theorem dropping_proposition_holds : ∃ C : ℝ, ∀ D : D7, Conclusion5 D C := by
  obtain ⟨C, -, hT⟩ := Formalism.FrobeniusOrbits.hostThickExists
  refine ⟨C, fun D Lw hLw => ?_⟩
  obtain ⟨T, hTs, hTR, hTc⟩ := hT D.R.n0 Lw hLw
  refine ⟨T, ?_, hTc, hTR, ?_⟩
  · intro s hs
    have h1 : ((4 * Lw * s : ℕ) : ℝ) < (D.R.n0 : ℝ) := by exact_mod_cast hTs s hs
    have hL : (2 : ℝ) ≤ Lw := by exact_mod_cast hLw
    rw [lt_div_iff₀ (by linarith)]
    push_cast at h1
    linarith
  · intro u₀ t h
    refine ⟨fun hh i₀ => ?_, fun hh => ?_⟩
    · by_contra hc
      push_neg at hc
      obtain ⟨i1, hi1, i2, hi2, i3, hi3, h12, h13, h23⟩ := Finset.two_lt_card.mp hc
      simp only [Finset.mem_filter, Finset.mem_Ico, transl, Set.mem_setOf_eq] at hi1 hi2 hi3
      obtain ⟨⟨a1, b1⟩, s1, hs1, e1⟩ := hi1
      obtain ⟨⟨a2, b2⟩, s2, hs2, e2⟩ := hi2
      obtain ⟨⟨a3, b3⟩, s3, hs3, e3⟩ := hi3
      exact false_of_three_distinct_in_window _ t h u₀ T Lw hTs hTR hh i₀ i1 i2 i3 s1 s2 s3 a1 b1 a2 b2 a3 b3
        h12 h13 h23 hs1 hs2 hs3 e1 e2 e3
    · haveI hfin : Finite (HH D) := by
        show Finite (Fin _)
        infer_instance
      have hpos : 0 < addOrderOf h := addOrderOf_pos h
      have hsub : (coset t h ∩ transl T u₀).Subsingleton := by
        rintro x ⟨⟨i, rfl⟩, s, hs, ex⟩ y ⟨⟨j, rfl⟩, s', hs', ey⟩
        have hss := eq_of_zsmul_eqs_of_small_orders _ t h u₀ T Lw hTs hpos hh i j s s' hs hs' ex ey
        subst hss
        rw [ex, ey]
      rcases hsub.eq_empty_or_singleton with hE | ⟨x, hx⟩
      · rw [hE, Set.ncard_empty]
        omega
      · rw [hx, Set.ncard_singleton]

end Formalism.MainNotions.UnusedSlot33

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.LemmaOneEightOfPolarisation
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open NumberField Formalism.FrobeniusOrbits Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory Formalism.TwoAdicCyclotomicDecomposition Ideal IntermediateField
open scoped Pointwise
open Formalism.MainNotions.UnusedSlot33.SlopeTestRemainingChoices

namespace CMIdealEquivalence

theorem map_KinE {L : Type} [Field L] [NumberField L] (ζ a b : L) :
    (KinE ζ a b).map (hostE ζ a b).val = Kd b := by
  have h := IntermediateField.adjoin_map (S := {bE ζ a b}) (f := (hostE ζ a b).val)
  rw [Set.image_singleton] at h
  exact h

def kEquiv {L : Type} [Field L] [NumberField L] (ζ a b : L) : KinE ζ a b ≃+* Kd b :=
  (((KinE ζ a b).equivMap (hostE ζ a b).val).trans
    (IntermediateField.equivOfEq (map_KinE ζ a b))).toRingEquiv

theorem mult_ring {M : Type} [Field M] [NumberField M]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) (hI : I ≠ 0) (x : M) :
    (∀ y ∈ I, x * y ∈ I) ↔ IsIntegral ℤ x := by
  constructor
  · intro h
    have hi : IsIntegral (𝓞 M) x :=
      isIntegral_of_smul_mem_submodule (I : Submodule (𝓞 M) M)
        (fun h0 => hI (FractionalIdeal.coeToSubmodule_eq_bot.1 h0))
        (FractionalIdeal.fg_of_isNoetherianRing le_rfl I) x (fun n hn => h n hn)
    obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · intro hx y hy
    have : (⟨x, hx⟩ : 𝓞 M) • y ∈ (I : Submodule (𝓞 M) M) :=
      Submodule.smul_mem (I : Submodule (𝓞 M) M) _ hy
    exact this

private theorem mem_one_iff'' {M : Type} [Field M] [NumberField M] (t : M) :
    t ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ↔ IsIntegral ℤ t := by
  rw [FractionalIdeal.mem_one_iff]
  constructor
  · rintro ⟨x', rfl⟩
    exact NumberField.RingOfIntegers.isIntegral_coe x'
  · intro h
    exact ⟨⟨t, h⟩, rfl⟩

private theorem integ_iff' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M) (t : M) :
    IsIntegral ℤ (σ t) ↔ IsIntegral ℤ t :=
  isIntegral_algEquiv (σ.restrictScalars ℤ)

private theorem smul_ne_bot' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M)
    (B : Ideal (𝓞 M)) (hB : B ≠ ⊥) : σ • B ≠ ⊥ := by
  intro h
  apply hB
  have h2 : σ⁻¹ • (σ • B) = σ⁻¹ • (⊥ : Ideal (𝓞 M)) := by rw [h]
  rwa [inv_smul_smul, Ideal.pointwise_smul_def, Ideal.map_bot] at h2

private theorem mem_inv_smul' {M : Type} [Field M] [NumberField M] (σ : M ≃ₐ[ℚ] M)
    (B : Ideal (𝓞 M)) (hB : B ≠ ⊥) (y : M) :
    σ y ∈ ((σ • B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M)⁻¹ ↔
      y ∈ ((B : FractionalIdeal (nonZeroDivisors (𝓞 M)) M))⁻¹ := by
  have hc : ∀ b : 𝓞 M, algebraMap (𝓞 M) M (σ • b) = σ (algebraMap (𝓞 M) M b) := fun b => rfl
  have h1 : ((σ • B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 (smul_ne_bot' σ B hB)
  have h2 : ((B : Ideal (𝓞 M)) : FractionalIdeal (nonZeroDivisors (𝓞 M)) M) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hB
  rw [FractionalIdeal.mem_inv_iff h1, FractionalIdeal.mem_inv_iff h2]
  constructor
  · intro h z hz
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have := h (σ (algebraMap (𝓞 M) M b)) ((FractionalIdeal.mem_coeIdeal _).2
      ⟨σ • b, Ideal.smul_mem_pointwise_smul σ b B hb, hc b⟩)
    rw [mem_one_iff'', ← map_mul, integ_iff'] at this
    rw [mem_one_iff'']
    exact this
  · intro h z hz
    obtain ⟨c, hc', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have hb : σ⁻¹ • c ∈ B := Ideal.mem_pointwise_smul_iff_inv_smul_mem.1 hc'
    have := h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hb, rfl⟩)
    rw [mem_one_iff''] at this ⊢
    have e : algebraMap (𝓞 M) M c = σ (algebraMap (𝓞 M) M (σ⁻¹ • c)) := by
      rw [← hc, smul_inv_smul]
    rw [e, ← map_mul, integ_iff']
    exact this

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  show (D.host.conj * D.host.conj) x = x
  rw [show D.host.conj * D.host.conj = 1 by
    simp only [Formalism.HC.HostRaw.conj, ← map_mul, Formalism.HC.Frame.cc_mul_cc, map_one]]
  rfl

theorem b_ne_bot (D : D7) : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h2 := D.host.𝔟_spec.2
  rw [h, Ideal.pointwise_smul_def, Ideal.map_bot, bot_sup_eq] at h2
  exact bot_ne_top h2

theorem ordinary (D : D7) : ∀ p : ℕ, p.Prime →
    (primesOver (span {(p : ℤ)}) (𝓞 D.host.K)).ncard = 2 →
      ∀ P : Ideal (𝓞 D.host.E), P.IsPrime → P.LiesOver (span {(p : ℤ)}) →
        ∀ σ τ : D.host.E ≃ₐ[ℚ] D.host.E, τ ∈ MulAction.stabilizer (D.host.E ≃ₐ[ℚ] D.host.E) P →
          (D.host.galE (σ * τ) ∈ D.R.Psi ↔
            D.host.galE σ ∈ D.R.Psi) := by
  intro p hp hK P hP hl σ τ hτ
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hP
  haveI := hl
  exact (D.host.der.ordinary p P).2 hK σ τ hτ

end CMIdealEquivalence

open CMIdealEquivalence

def PolPart (D : D7) : Prop :=
  ∀ cc : Ideal (𝓞 D.host.K), cc ≠ ⊥ →
    ∃ ξ : D.host.E, ξ ∈ D.host.K ∧ D.host.conj ξ = -ξ ∧ (∀ φ ∈ PhiEmb D, 0 < (φ ξ).im) ∧
      ∀ y : D.host.E,
        y ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0 ↔
        ∀ x ∈ ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
          FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0,
          Algebra.trace ℚ D.host.E (ξ * D.host.conj x * y) ∈ (algebraMap ℤ ℚ).range

theorem lemma_one_eight_of_polarisation (D : D7) (hPol : PolPart D) : Conclusion8 D := by
  have hb := b_ne_bot D
  have hσb : D.host.conj • D.host.𝔟 ≠ ⊥ := smul_ne_bot' D.host.conj _ hb
  have hb0 : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) :
      FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 hb
  refine ⟨D.host.AA0, ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) :
    FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹, ?_, ?_, ?_, ordinary D⟩
  · intro x
    have hσσ : D.host.conj • D.host.conj • D.host.𝔟 = D.host.𝔟 := by
      rw [smul_smul, show D.host.conj * D.host.conj = 1 from AlgEquiv.ext (conj_conj D), one_smul]
    have h := mem_inv_smul' D.host.conj (D.host.conj • D.host.𝔟) hσb x
    rw [hσσ] at h
    exact h.symm
  · rw [D.host.𝔟_spec.1, FractionalIdeal.coeIdeal_mul, mul_inv]
    try rfl
  · intro cc hcc
    have hm : Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc ≠ ⊥ :=
      Ideal.map_ne_bot_of_ne_bot hcc
    have hne : ((Ideal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) cc : Ideal (𝓞 D.host.E)) :
        FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) * D.host.AA0 ≠ 0 :=
      mul_ne_zero (FractionalIdeal.coeIdeal_ne_zero.2 hm) (inv_ne_zero hb0)
    exact ⟨fun x => mult_ring _ hne x, hPol cc hcc⟩

end Formalism.MainNotions.UnusedSlot33

end
end

-- bundled from Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.PairwiseIndependenceComplementHolds
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot33

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory

namespace BernoulliMarginals

variable {α : Type*} [Fintype α] [DecidableEq α]

end BernoulliMarginals

namespace UpperTriangularReduction

open Matrix Filter Topology Polynomial

section UT

variable {k : ℕ} {S : Type*} [CommRing S]

def UT (B : Matrix (Fin k) (Fin k) S) : Prop := B.BlockTriangular id ∧ ∀ i, B i i = 1

theorem diag_mul {A B : Matrix (Fin k) (Fin k) S} (hA : A.BlockTriangular id)
    (hB : B.BlockTriangular id) (i : Fin k) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro j _ hji
    rcases lt_or_gt_of_ne hji with h | h
    · rw [hA h, zero_mul]
    · rw [hB h, mul_zero]
  · simp

theorem UT.mul {A B : Matrix (Fin k) (Fin k) S} (hA : UT A) (hB : UT B) : UT (A * B) :=
  ⟨hA.1.mul hB.1, fun i => by rw [diag_mul hA.1 hB.1, hA.2, hB.2, one_mul]⟩

theorem UT.one : UT (1 : Matrix (Fin k) (Fin k) S) :=
  ⟨Matrix.blockTriangular_one, fun i => Matrix.one_apply_eq i⟩

def Uk (k : ℕ) (S : Type*) [CommRing S] : Subgroup (GL (Fin k) S) where
  carrier := {M | UT (M : Matrix (Fin k) (Fin k) S)}
  one_mem' := UT.one
  mul_mem' := fun {a b} ha hb => by
    show UT ((a * b : GL (Fin k) S) : Matrix (Fin k) (Fin k) S)
    rw [Units.val_mul]
    exact UT.mul ha hb
  inv_mem' := fun {a} ha => by
    show UT ((a⁻¹ : GL (Fin k) S) : Matrix (Fin k) (Fin k) S)
    have ha' : UT (a : Matrix (Fin k) (Fin k) S) := ha
    have : Invertible (a : Matrix (Fin k) (Fin k) S) := Units.invertible a
    have ht : ((a⁻¹ : GL (Fin k) S) : Matrix (Fin k) (Fin k) S).BlockTriangular id := by
      rw [Matrix.coe_units_inv]
      exact Matrix.blockTriangular_inv_of_blockTriangular ha'.1
    refine ⟨ht, fun i => ?_⟩
    have h1 := diag_mul ha'.1 ht i
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq, ha'.2, one_mul] at h1
    exact h1.symm

theorem UT.nilp {B : Matrix (Fin k) (Fin k) S} (hB : UT B) : (B - 1) ^ k = 0 := by
  have h := Matrix.aeval_self_charpoly B
  rw [Matrix.charpoly_of_isUpperTriangular B hB.1] at h
  simpa [hB.2] using h

end UT

variable (g k : ℕ) [Fact g.Prime]

theorem red_pow {B : Matrix (Fin k) (Fin k) (ZMod g)} (hB : UT B) : B ^ g ^ k = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Subsingleton.elim _ _
  · have : Nonempty (Fin k) := Fin.pos_iff_nonempty.1 hk
    have : CharP (Matrix (Fin k) (Fin k) (ZMod g)) g := Matrix.charP g
    have h1 : (B - 1) ^ g ^ k = B ^ g ^ k - 1 ^ g ^ k :=
      sub_pow_char_pow_of_commute g k (Commute.one_right B)
    have h2 : (B - 1) ^ g ^ k = 0 :=
      pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : g.Prime).one_lt).le hB.nilp
    rw [h2, one_pow] at h1
    exact (sub_eq_zero.1 h1.symm)

theorem lift_one (C : Matrix (Fin k) (Fin k) ℤ_[g])
    (hC : C.map (PadicInt.toZMod (p := g)) = 1) :
    ∃ Y : Matrix (Fin k) (Fin k) ℤ_[g], C = 1 + (g : Matrix (Fin k) (Fin k) ℤ_[g]) * Y := by
  have h : ∀ i j, ∃ y : ℤ_[g], (C - 1) i j = (g : ℤ_[g]) * y := by
    intro i j
    have h0 : PadicInt.toZMod ((C - 1) i j) = 0 := by
      have h1 : (PadicInt.toZMod (p := g)).mapMatrix (C - 1) = 0 := by
        rw [map_sub, map_one, RingHom.mapMatrix_apply, hC, sub_self]
      have h2 := congrFun (congrFun h1 i) j
      simpa [RingHom.mapMatrix_apply] using h2
    rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton] at h0
    exact h0
  choose Y hY using h
  refine ⟨Matrix.of Y, ?_⟩
  ext i j
  have h1 : ((g : Matrix (Fin k) (Fin k) ℤ_[g]) * Matrix.of Y) i j = (g : ℤ_[g]) * Y i j := by
    rw [← nsmul_eq_mul, Matrix.smul_apply, nsmul_eq_mul, Matrix.of_apply]
  rw [Matrix.add_apply, h1, ← hY i j, Matrix.sub_apply]
  ring

theorem pow_one_add (Y : Matrix (Fin k) (Fin k) ℤ_[g]) (b : ℕ) :
    ∃ Z : Matrix (Fin k) (Fin k) ℤ_[g],
      (1 + (g : Matrix (Fin k) (Fin k) ℤ_[g]) * Y) ^ g ^ b = 1 + (g ^ (b + 1)) • Z := by
  have hd : ((g : ℕ) : ℤ_[g][X]) ^ (b + 1) ∣
      (1 + ((g : ℕ) : ℤ_[g][X]) * X) ^ g ^ b - 1 ^ g ^ b :=
    dvd_sub_pow_of_dvd_sub ⟨X, by ring⟩ b
  obtain ⟨Q, hQ⟩ := hd
  refine ⟨aeval Y Q, ?_⟩
  have h := congrArg (aeval Y) hQ
  simp only [map_sub, map_pow, map_add, map_one, map_mul, map_natCast, aeval_X] at h
  rw [one_pow, sub_eq_iff_eq_add] at h
  rw [h, nsmul_eq_mul, add_comm]
  push_cast
  rfl

theorem tendsto_pow (A : Matrix (Fin k) (Fin k) ℤ_[g])
    (hA : UT (A.map (PadicInt.toZMod (p := g)))) :
    Tendsto (fun m => A ^ g ^ m) atTop (𝓝 1) := by
  obtain ⟨Y, hY⟩ := lift_one g k (A ^ g ^ k) (by rw [Matrix.map_pow]; exact red_pow g k hA)
  rw [← tendsto_add_atTop_iff_nat k]
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hg1 : (1 : ℝ) < g := by exact_mod_cast (Fact.out : g.Prime).one_lt
  have hlim : Tendsto (fun b : ℕ => ((g : ℝ)⁻¹) ^ (b + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hg1)).comp
      (tendsto_add_atTop_nat 1)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun b => ?_) hlim
  obtain ⟨Z, hZ⟩ := pow_one_add g k Y b
  have e : A ^ g ^ (b + k) = 1 + (g ^ (b + 1)) • Z := by
    rw [pow_add, mul_comm, pow_mul, hY, hZ]
  rw [e, Matrix.add_apply, add_sub_cancel_left, Matrix.smul_apply, nsmul_eq_mul, norm_mul]
  push_cast
  rw [norm_pow, PadicInt.norm_p]
  exact mul_le_of_le_one_right (by positivity) (PadicInt.norm_le_one _)

end UpperTriangularReduction

end Formalism.MainNotions.UnusedSlot33

end
end

