import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.Bundle0004
import ReciprocityTheory.GaloisValuations.ArithOfA

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTProd
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain MeasureTheory
open scoped ENNReal TensorProduct

theorem volTProdU_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (g r : ℕ)
    [SFinite (sdE (E := E) ψ v (UIdx r))]
    (hM : MeasurableSet (VolTUSet (E := E) v g r)) (hMO : MeasurableSet (VolTO (E := E) v (UIdx r)))
    (hA : VolTAff (E := E) ψ v g (UIdx r)) (hO : VolTOne (E := E) ψ v (UIdx r)) :
    VolTProdU (E := E) ψ v g r := by
  unfold VolTProdU
  rw [Measure.prod_apply hM]
  have hsec : ∀ x : UIdx r → Fv F v ⊗[F] E,
      sdE (E := E) ψ v (UIdx r) (Prod.mk x ⁻¹' VolTUSet (E := E) v g r) =
        (VolTO (E := E) v (UIdx r)).indicator (fun _ => ((g : ℝ≥0∞) ^ (2 * Fintype.card (UIdx r)))⁻¹) x := by
    intro x
    by_cases hx : x ∈ VolTO (E := E) v (UIdx r)
    · rw [Set.indicator_of_mem hx]
      have hpre : Prod.mk x ⁻¹' VolTUSet (E := E) v g r =
          {w | (fun i => (w i - x i) * sc (E := E) v (g : Fv F v)⁻¹) ∈ VolTO (E := E) v (UIdx r)} := by
        ext y
        simp only [Set.mem_preimage, VolTUSet, VolTO, Set.mem_ofPred_eq]
        exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
      rw [hpre, hA, hO, mul_one]
    · rw [Set.indicator_of_notMem hx]
      have hpre : Prod.mk x ⁻¹' VolTUSet (E := E) v g r = ∅ := by
        ext y
        simp only [Set.mem_preimage, VolTUSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        exact fun h => hx h.1
      rw [hpre, measure_empty]
  simp_rw [hsec]
  rw [lintegral_indicator_const hMO, mul_comm]

end Formalism.L2.SG.Pf.NcVal
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolTUnit
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.L2.SG.LocVol Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct

namespace VolTU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (v : HeightOneSpectrum (𝓞 F))

def OS : Submodule (v.adicCompletionIntegers F) (Fv F v ⊗[F] E) :=
  Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)

theorem mem_OEv (x : Fv F v ⊗[F] E) : x ∈ OEv (E := E) v ↔ x ∈ OS (E := E) v := Iff.rfl

theorem sc_mul (a b : Fv F v) : sc (E := E) v (a * b) = sc (E := E) v a * sc (E := E) v b := by
  simp [sc, Algebra.TensorProduct.tmul_mul_tmul]

theorem sc_one : sc (E := E) v (1 : Fv F v) = 1 := rfl

theorem sc_mul_eq_smul (c : Fv F v) (x : Fv F v ⊗[F] E) : sc (E := E) v c * x = c • x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sc, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.smul_tmul']
  | add x y hx hy => rw [mul_add, hx, hy, smul_add]

theorem sc_mul_mem {c : Fv F v} (hc : c ∈ v.adicCompletionIntegers F) {x : Fv F v ⊗[F] E}
    (hx : x ∈ OEv (E := E) v) : sc (E := E) v c * x ∈ OEv (E := E) v := by
  rw [mem_OEv] at hx ⊢
  rw [sc_mul_eq_smul]
  have := (OS (E := E) v).smul_mem (⟨c, hc⟩ : v.adicCompletionIntegers F) hx
  exact this

theorem val_le_one_mem {c : Fv F v} (hc : Valued.v c ≤ 1) : c ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) (v := v)).mpr hc

theorem unit_mul_mem_iff {c : Fv F v} (hc : Valued.v c = 1) (x : Fv F v ⊗[F] E) :
    sc (E := E) v c * x ∈ OEv (E := E) v ↔ x ∈ OEv (E := E) v := by
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  constructor
  · intro h
    have hi : Valued.v c⁻¹ ≤ 1 := by rw [map_inv₀, hc, inv_one]
    have := sc_mul_mem (E := E) v (val_le_one_mem v hi) h
    rwa [← mul_assoc, ← sc_mul, inv_mul_cancel₀ hc0, sc_one, one_mul] at this
  · intro h
    exact sc_mul_mem (E := E) v (val_le_one_mem v hc.le) h

theorem val_alp (hd : Valued.v (dV v) = 1) (r : ℕ) (a : Fin (r + 1)) : Valued.v (alp v r a) = 1 := by
  unfold alp
  split_ifs
  · rw [map_pow, map_inv₀, hd, inv_one, one_pow]
  · exact map_one _

theorem natCast_ne_zero {g : ℕ} (hg : g ≠ 0) : (g : Fv F v) ≠ 0 := Nat.cast_ne_zero.mpr hg

theorem natCast_memO (g : ℕ) : (g : Fv F v) ∈ v.adicCompletionIntegers F :=
  _root_.natCast_mem (v.adicCompletionIntegers F) g

theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := fun h => v.ne_bot (Ideal.absNorm_eq_zero_iff.mp h)
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := fun h => v.isPrime.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  omega

theorem val_eq_one_of_absV {x : Fv F v} (h : absV v x = 1) : Valued.v x = 1 := by
  unfold absV at h
  split_ifs at h with h0
  · exact absurd h zero_ne_one
  · have hN : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast one_lt_absNorm v
    have hk : Multiplicative.toAdd (WithZero.unzero h0) = 0 :=
      (zpow_eq_one_iff_right₀ (by positivity) hN.ne').mp h
    have hu : WithZero.unzero h0 = 1 := by
      rw [← ofAdd_toAdd (WithZero.unzero h0), hk, ofAdd_zero]
    rw [← WithZero.coe_unzero h0, hu, WithZero.coe_one]

end VolTU

open VolTU in

theorem volTUOEq_of {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (hd : Valued.v (dV v) = 1) {g : ℕ} (hg : g ≠ 0) (r : ℕ) :
    VolTUOEq (E := E) v g r := by
  have key : ∀ (q : UIdx r) (y : Fv F v ⊗[F] E),
      sc (E := E) v ((alp v r q.1.1)⁻¹ * alp v r q.1.2) * y ∈ OEv (E := E) v ↔ y ∈ OEv (E := E) v := by
    intro q y
    apply unit_mul_mem_iff
    rw [map_mul, map_inv₀, val_alp v hd, val_alp v hd, inv_one, one_mul]
  have e : ∀ (a b : Fv F v) (y : Fv F v ⊗[F] E),
      sc (E := E) v (a * b * (g : Fv F v)⁻¹) * y = sc (E := E) v (a * b) * (sc (E := E) v (g : Fv F v)⁻¹ * y) := by
    intro a b y
    rw [sc_mul, mul_assoc]
  have hg0 := natCast_ne_zero v hg
  have hgO := natCast_memO v g
  have sw : ∀ y : Fv F v ⊗[F] E,
      y * sc (E := E) v (g : Fv F v)⁻¹ ∈ OS (E := E) v ↔ sc (E := E) v (g : Fv F v)⁻¹ * (-y) ∈ OS (E := E) v := by
    intro y
    rw [mul_neg, Submodule.neg_mem_iff, mul_comm]
  ext p
  simp only [deepCongruenceVolume, VolTUSet, UO, Set.mem_setOf_eq, e, key]
  simp only [mem_OEv]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, fun q => ?_⟩
    rw [sw, neg_sub]
    exact h3 q
  · rintro ⟨h1, h3⟩
    have h3' : ∀ q, sc (E := E) v (g : Fv F v)⁻¹ * (p.1 q - p.2 q) ∈ OS (E := E) v := fun q => by
      rw [← neg_sub, ← sw]
      exact h3 q
    refine ⟨h1, fun q => ?_, h3'⟩
    have h4 := (OS (E := E) v).smul_mem (⟨(g : Fv F v), hgO⟩ : v.adicCompletionIntegers F) (h3' q)
    have h5 : p.1 q - p.2 q ∈ OS (E := E) v := by
      have h6 : (g : Fv F v) • (sc (E := E) v (g : Fv F v)⁻¹ * (p.1 q - p.2 q)) ∈ OS (E := E) v := h4
      rwa [← sc_mul_eq_smul, ← mul_assoc, ← sc_mul, mul_inv_cancel₀ hg0, sc_one, one_mul] at h6
    have h7 : p.2 q = p.1 q - (p.1 q - p.2 q) := by abel
    rw [h7]
    exact (OS (E := E) v).sub_mem (h1 q) h5

end Formalism.L2.SG.Pf.NcVal
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolUArith
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal.VolUAr

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Ideal

section V

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem val_natCast_of (g : ℕ) (hg1 : (g : 𝓞 F) ∈ v.asIdeal) (hg2 : (g : 𝓞 F) ∉ v.asIdeal ^ 2) :
    Valued.v (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) = WithZero.exp (-1 : ℤ) := by
  have e : (((g : v.adicCompletionIntegers F) : v.adicCompletion F)) = (((g : 𝓞 F) : F) : v.adicCompletion F) := by
    push_cast
    exact (map_natCast (algebraMap F (v.adicCompletion F)) g).symm
  rw [e, valuedAdicCompletion_eq_valuation', valuation_of_algebraMap]
  have hg0 : (g : 𝓞 F) ≠ 0 := by
    rintro h
    exact hg2 (h ▸ Ideal.zero_mem _)
  have h1 := (intValuation_le_pow_iff_dvd v (g : 𝓞 F) 1).mpr (by rwa [pow_one, Ideal.dvd_span_singleton])
  have h2 : ¬ v.intValuation (g : 𝓞 F) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := by
    rw [intValuation_le_pow_iff_dvd, Ideal.dvd_span_singleton]
    exact hg2
  rw [intValuation_eq_exp_neg_multiplicity v hg0] at h1 h2 ⊢
  rw [WithZero.exp_le_exp] at h1 h2
  congr 1
  omega

end V

theorem split_transport {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] (e : K ≃+* L)
    (l : ℕ) (h : {w : HeightOneSpectrum (𝓞 L) | ((l : ℕ) : 𝓞 L) ∈ w.asIdeal}.ncard = Module.finrank ℚ L) :
    {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K := by
  set φ : 𝓞 K ≃+* 𝓞 L := NumberField.RingOfIntegers.mapRingEquiv e with hφ
  rw [(e.toRatAlgEquiv).toLinearEquiv.finrank_eq, ← h]
  refine Set.ncard_congr
    (fun w _ => (⟨w.asIdeal.map φ, Ideal.map_isPrime_of_equiv φ,
      fun hb => w.ne_bot ((Ideal.map_eq_bot_iff_of_injective φ.injective).mp hb)⟩ : HeightOneSpectrum (𝓞 L)))
    ?_ ?_ ?_
  · intro w hw
    have h1 := Ideal.mem_map_of_mem φ hw
    rw [map_natCast] at h1
    exact h1
  · intro a b _ _ hab
    have h1 : a.asIdeal.map φ = b.asIdeal.map φ := congrArg HeightOneSpectrum.asIdeal hab
    have h2 := congrArg (Ideal.comap φ) h1
    rw [Ideal.comap_map_of_bijective φ φ.bijective, Ideal.comap_map_of_bijective φ φ.bijective] at h2
    exact HeightOneSpectrum.ext h2
  · intro w' hw'
    have hne : w'.asIdeal.comap φ ≠ ⊥ := by
      intro hb
      apply w'.ne_bot
      rw [← Ideal.map_comap_of_surjective φ φ.surjective w'.asIdeal, hb, Ideal.map_bot]
    refine ⟨⟨w'.asIdeal.comap φ, Ideal.IsPrime.comap φ, hne⟩, ?_, ?_⟩
    · show _ ∈ Ideal.comap φ w'.asIdeal
      rw [Ideal.mem_comap, map_natCast]
      exact hw'
    · exact HeightOneSpectrum.ext (Ideal.map_comap_of_surjective φ φ.surjective w'.asIdeal)

section K

variable {K : Type} [Field K] [NumberField K]

private theorem liesOver_span_of_natCast_mem' (l : ℕ) [Fact l.Prime] (w : Ideal (𝓞 K)) [w.IsPrime]
    (hw : ((l : ℕ) : 𝓞 K) ∈ w) : w.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := by
  refine ⟨(Int.ideal_span_isMaximal_of_prime l).eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ w)) ?_⟩
  rw [Ideal.span_le, Set.singleton_subset_iff]
  show _ ∈ Ideal.comap (algebraMap ℤ (𝓞 K)) w
  rw [Ideal.mem_comap]
  simpa using hw

theorem locDeg_one (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 K) | ((l : ℕ) : 𝓞 K) ∈ w.asIdeal}.ncard = Module.finrank ℚ K)
    (w : HeightOneSpectrum (𝓞 K)) (hw : ((l : ℕ) : 𝓞 K) ∈ w.asIdeal) :
    w.asIdeal.ramificationIdx ℤ = 1 ∧ w.asIdeal.inertiaDeg ℤ = 1 := by
  have hmaxl := Int.ideal_span_isMaximal_of_prime l
  have hl0 : ((l : ℕ) : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.mpr hl.out.ne_zero
  have hsum := Ideal.sum_ramification_inertia_eq_finrank (Ideal.span {((l : ℕ) : ℤ)}) (𝓞 K)
  rw [NumberField.RingOfIntegers.rank] at hsum
  have hcard : Fintype.card ((Ideal.span {((l : ℕ) : ℤ)}).primesOver (𝓞 K)) = Module.finrank ℚ K := by
    rw [← h, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
    symm
    refine Set.ncard_congr (fun w _ => w.asIdeal) (fun w hw => ⟨w.isPrime, liesOver_span_of_natCast_mem' l w.asIdeal hw⟩)
      (fun a b _ _ hab => HeightOneSpectrum.ext hab) ?_
    intro Q hQ
    haveI := hQ.1
    haveI := hQ.2
    have hmem : ((l : ℕ) : 𝓞 K) ∈ Q := by
      have h3 : ((l : ℕ) : ℤ) ∈ Q.under ℤ := by
        rw [← Ideal.over_def Q (Ideal.span {((l : ℕ) : ℤ)})]
        exact Ideal.mem_span_singleton_self _
      have h4 := Ideal.mem_comap.mp h3
      simpa using h4
    refine ⟨⟨Q, hQ.1, ?_⟩, hmem, rfl⟩
    intro hb
    rw [hb, Ideal.mem_bot] at hmem
    exact hl0 hmem
  have hpos : ∀ q ∈ (Finset.univ : Finset ((Ideal.span {((l : ℕ) : ℤ)}).primesOver (𝓞 K))),
      (fun _ => 1) q ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ := by
    intro q _
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (Ideal.ramificationIdx_pos q.1 ℤ).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  have hall := (Finset.sum_eq_sum_iff_of_le hpos).mp (by rw [hsum]; simp [hcard])
  have hw' := hall ⟨w.asIdeal, w.isPrime, liesOver_span_of_natCast_mem' l w.asIdeal hw⟩ (Finset.mem_univ _)
  exact mul_eq_one.mp hw'.symm

end K

section FE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem locDeg_one_below (l : ℕ) [hl : Fact l.Prime]
    (h : {w : HeightOneSpectrum (𝓞 E) | ((l : ℕ) : 𝓞 E) ∈ w.asIdeal}.ncard = Module.finrank ℚ E)
    (p : HeightOneSpectrum (𝓞 F)) (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) :
    p.asIdeal.ramificationIdx ℤ = 1 ∧ p.asIdeal.inertiaDeg ℤ = 1 := by
  haveI := p.isPrime
  obtain ⟨Q, -, hQ, hc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := 𝓞 E) p.asIdeal ⊥
    (by rw [Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)]; exact bot_le)
  haveI := hQ
  haveI : Q.LiesOver p.asIdeal := ⟨hc.symm⟩
  have hQ0 : Q ≠ ⊥ := by
    intro hb
    apply p.ne_bot
    rw [← hc, hb, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)]
  have hw : ((l : ℕ) : 𝓞 E) ∈ Q := by
    rw [← hc] at hp
    simpa using Ideal.mem_comap.mp hp
  obtain ⟨he, hf⟩ := locDeg_one (K := E) l h ⟨Q, hQ, hQ0⟩ hw
  have he' := Ideal.ramificationIdx_tower (R := ℤ) p.asIdeal Q
  have hf' := Ideal.inertiaDeg_tower (R := ℤ) p.asIdeal Q
  exact ⟨(mul_eq_one.mp (he'.symm.trans he)).1, (mul_eq_one.mp (hf'.symm.trans hf)).1⟩

end FE

section Arith

variable {F : Type} [Field F] [NumberField F]

theorem arith_of_loc (l : ℕ) [hl : Fact l.Prime] (p : HeightOneSpectrum (𝓞 F))
    (hp : ((l : ℕ) : 𝓞 F) ∈ p.asIdeal) (he : p.asIdeal.ramificationIdx ℤ = 1)
    (hf : p.asIdeal.inertiaDeg ℤ = 1) :
    Nat.card (𝓞 F ⧸ p.asIdeal) = l ∧ ((l : ℕ) : 𝓞 F) ∉ p.asIdeal ^ 2 := by
  have hmaxl := Int.ideal_span_isMaximal_of_prime l
  haveI := p.isMaximal
  have hunder : Ideal.span {((l : ℕ) : ℤ)} = p.asIdeal.under ℤ := by
    refine hmaxl.eq_of_le (Ideal.IsPrime.ne_top (Ideal.IsPrime.under ℤ p.asIdeal)) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show _ ∈ Ideal.comap (algebraMap ℤ (𝓞 F)) p.asIdeal
    rw [Ideal.mem_comap]
    simpa using hp
  haveI : p.asIdeal.LiesOver (Ideal.span {((l : ℕ) : ℤ)}) := ⟨hunder⟩
  constructor
  · have h := Ideal.cardQuot_pow_inertiaDeg (Ideal.span {((l : ℕ) : ℤ)}) p.asIdeal
    rw [hf, pow_one, Submodule.cardQuot_apply, Submodule.cardQuot_apply] at h
    rw [← h, Nat.card_congr (Int.quotientSpanNatEquivZMod l).toEquiv, Nat.card_zmod]
  · have hne : Ideal.span {((l : ℕ) : ℤ)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hl.out.ne_zero
    have h1 : (Ideal.span {((l : ℕ) : ℤ)}).ramificationIdx' p.asIdeal = 1 := by
      rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hne]
      exact he
    intro hmem
    have hle : Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {((l : ℕ) : ℤ)}) ≤ p.asIdeal ^ 2 := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
      simpa using hmem
    unfold Ideal.ramificationIdx' at h1
    have hbdd : BddAbove {n | Ideal.map (algebraMap ℤ (𝓞 F)) (Ideal.span {((l : ℕ) : ℤ)}) ≤ p.asIdeal ^ n} := by
      by_contra hb
      rw [Nat.sSup_of_not_bddAbove hb] at h1
      exact zero_ne_one h1
    have h2 := le_csSup hbdd hle
    omega

end Arith

end Formalism.L2.SG.Pf.NcVal.VolUAr
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.VolumeDeepCongruenceOfFubini
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
  NumberField IsDedekindDomain
open scoped ENNReal TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem volU_two_card_uidx (r : ℕ) : 2 * Fintype.card (UIdx r) = r * (r + 1) := by
  classical
  have hlt : Fintype.card (UIdx r) =
      (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 < p.2)).card :=
    Fintype.card_subtype _
  have hgt : (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 < p.2)).card =
      (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.2 < p.1)).card := by
    refine Finset.card_bij (fun p _ => (p.2, p.1)) ?_ ?_ ?_
    · intro p hp; simpa using hp
    · intro p _ q _ h
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.2 h.1
    · intro q hq
      exact ⟨(q.2, q.1), by simpa using hq, rfl⟩
  have heq : (Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2)).card = r + 1 := by
    have : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2) =
        Finset.univ.map ⟨fun a : Fin (r + 1) => (a, a), fun a b h => by simpa using h⟩ := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map]
      constructor
      · intro h; exact ⟨p.1, Prod.ext rfl h⟩
      · rintro ⟨a, rfl⟩; rfl
    rw [this, Finset.card_map, Finset.card_univ, Fintype.card_fin]
  have h1 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin (r + 1) × Fin (r + 1)))) (fun p => p.1 < p.2)
  have h2 := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2)) (fun p => p.2 < p.1)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  have e1 : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2 ∧ p.2 < p.1) =
      Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.2 < p.1) :=
    Finset.filter_congr (fun p _ => ⟨fun h => h.2, fun h => ⟨not_lt.mpr h.le, h⟩⟩)
  have e2 : Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => ¬ p.1 < p.2 ∧ ¬ p.2 < p.1) =
      Finset.univ.filter (fun p : Fin (r + 1) × Fin (r + 1) => p.1 = p.2) :=
    Finset.filter_congr (fun p _ => ⟨fun h => le_antisymm (not_lt.mp h.2) (not_lt.mp h.1),
      fun h => ⟨by rw [h]; exact lt_irrefl _, by rw [h]; exact lt_irrefl _⟩⟩)
  rw [e1, e2, heq] at h2
  rw [Finset.card_univ, Fintype.card_prod, Fintype.card_fin] at h1
  have hsq : (r + 1) * (r + 1) = r * (r + 1) + (r + 1) := by ring
  omega

section OfX

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

theorem volU_gAt_pos (v : PlX X) : 0 < gAt X v := by
  unfold gAt
  split_ifs
  · exact (D.host.g_prime 0).pos
  · exact (D.host.g_prime 1).pos

def VolUHyp : Prop :=
  IsCharAF X.B.I.F ψ ∧ IsStdChar ψ ∧ (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2]

theorem volU_ratio (v : PlX X) (hZ : VolTZZAt X u u' ψ v) (hU : VolumeDeepCongruenceSubgroup X ψ v) :
    localVolumeUnit X ψ v / ZZX X u u' ψ v = (gAt X v : ℝ) ^ ((D.R.rS + 1) * (2 * D.R.rS + 3)) := by
  rw [hU, hZ]
  have hg : (gAt X v : ℝ) ≠ 0 := by exact_mod_cast (volU_gAt_pos X v).ne'
  rw [← zpow_sub₀ hg, ← zpow_natCast]
  congr 1
  push_cast
  ring

theorem volTypV_of' (h : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolTZZAt X u u' ψ v ∧ VolumeDeepCongruenceSubgroup X ψ v) :
    VolTypV X u u' ψ := by
  intro h1 h2 h3 v hv
  obtain ⟨hZ, hU⟩ := h ⟨h1, h2, h3⟩ v hv
  exact volU_ratio X u u' ψ v hZ hU

theorem volUZZAt_of (v : PlX X) (hv : TypAt X v)
    (hA : VolTAff (E := X.B.I.E) ψ v (gAt X v) (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)))
    (hL : VolTLocPres (E := X.B.I.E) ψ v D.R.rS)
    (hH : VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS)
    (hC : VolTTFCong X u u' v) : VolTZZAt X u u' ψ v := by
  unfold VolTZZAt ZZX volS
  rw [if_pos hv]
  have hset : ZZTyp X.B.I.cm.sig v (gAt X v) D.R.rS (TFv X u v) (TFv X u' v) =
      {z | (fun p => locZ (E := X.B.I.E) v z p.1 p.2) ∈
        {w | (fun p => (w p - TFv X u v p.1 p.2) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹) ∈
          VolTW X.B.I.cm.sig v (gAt X v) D.R.rS
            (fun i j => (TFv X u' v i j - TFv X u v i j) * sc (E := X.B.I.E) v (gAt X v : Fv X.B.I.F v)⁻¹)}} := by
    rfl
  rw [hset, hL, hA, hH _ hC]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, zpow_neg, zpow_natCast, ← mul_inv, ← pow_add]
  congr 2
  ring

theorem volume_deep_congruence_of_fubini (v : PlX X) (hv : TypAt X v)
    (hE : VolTUOEq (E := X.B.I.E) v (gAt X v) D.R.rS)
    (hP : VolTProdU (E := X.B.I.E) ψ v (gAt X v) D.R.rS)
    (hO : VolTOne (E := X.B.I.E) ψ v (UIdx D.R.rS)) : VolumeDeepCongruenceSubgroup X ψ v := by
  unfold VolumeDeepCongruenceSubgroup localVolumeUnit volU
  rw [if_pos hv, hE, hP, hO, one_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    volU_two_card_uidx, zpow_neg, zpow_natCast]

def VolUSteps (v : PlX X) : Prop :=
  VolTAff (E := X.B.I.E) ψ v (gAt X v) (Fin (D.R.rS + 1) × Fin (D.R.rS + 1)) ∧
      VolTLocPres (E := X.B.I.E) ψ v D.R.rS ∧ VolTHermCnt X.B.I.cm.sig ψ v (gAt X v) D.R.rS ∧
      VolTTFCong X u u' v ∧ VolTUOEq (E := X.B.I.E) v (gAt X v) D.R.rS ∧
      VolTProdU (E := X.B.I.E) ψ v (gAt X v) D.R.rS ∧ VolTOne (E := X.B.I.E) ψ v (UIdx D.R.rS)

theorem volTypV_of_steps' (h : VolUHyp X u u' ψ → ∀ v, TypAt X v → VolUSteps X u u' ψ v) :
    VolTypV X u u' ψ :=
  volTypV_of' X u u' ψ fun hh v hv =>
    ⟨volUZZAt_of X u u' ψ v hv (h hh v hv).1 (h hh v hv).2.1 (h hh v hv).2.2.1 (h hh v hv).2.2.2.1,
      volume_deep_congruence_of_fubini X ψ v hv (h hh v hv).2.2.2.2.1 (h hh v hv).2.2.2.2.2.1 (h hh v hv).2.2.2.2.2.2⟩

end OfX

end Formalism.L2.SG.Pf.NcVal
end
end

