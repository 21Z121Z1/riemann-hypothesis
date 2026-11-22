import Mathlib
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePair
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0015
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0044
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0118
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.NegGram
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CardResidueFieldTotallyRealTypePrime
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.SplitResidueCard

theorem absNorm_eq_of_ncard {E : Type} [Field E] [NumberField E] {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    {w : Ideal (𝓞 E)} (hwp : w.IsPrime) (hw : ((p : ℕ) : 𝓞 E) ∈ w) :
    Ideal.absNorm w = p := by
  classical
  obtain ⟨hc, -⟩ := Formalism.MainNotions.ModuliIntegralCharts.H1.GSplit.split_of_ncard hp h
  set I : Ideal (𝓞 E) := Ideal.span {((p : ℕ) : 𝓞 E)} with hI
  have hI0 : I ≠ ⊥ := by
    rw [hI, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  set M := UniqueFactorizationMonoid.normalizedFactors I with hM
  have hN : Ideal.absNorm I = p ^ Module.finrank ℚ E := by
    rw [hI, Ideal.absNorm_span_singleton]
    have : ((p : ℕ) : 𝓞 E) = algebraMap ℤ (𝓞 E) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, RingOfIntegers.rank]
    simp
  have hprod : M.prod = I := Ideal.prod_normalizedFactors_eq_self hI0
  have hge : ∀ P ∈ M, p ≤ Ideal.absNorm P := by
    intro P hP
    obtain ⟨hPp, hIP⟩ := (Ideal.mem_normalizedFactors_iff hI0).1 hP
    have hd : Ideal.absNorm P ∣ p ^ Module.finrank ℚ E := hN ▸ Ideal.absNorm_dvd_absNorm_of_le hIP
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 hd
    have h1 : Ideal.absNorm P ≠ 1 := by rw [Ne, Ideal.absNorm_eq_one_iff]; exact hPp.ne_top
    rw [hj] at h1 ⊢
    exact Nat.le_self_pow (by rintro rfl; simp at h1) p
  have hwM : w ∈ M := (Ideal.mem_normalizedFactors_iff hI0).2
    ⟨hwp, by rw [hI, Ideal.span_singleton_le_iff_mem]; exact hw⟩
  refine le_antisymm ?_ (hge _ hwM)
  obtain ⟨M', hM'⟩ := Multiset.exists_cons_of_mem hwM
  have h2 : p ^ M'.card ≤ (M'.map Ideal.absNorm).prod := by
    have := Multiset.pow_card_le_prod (s := M'.map Ideal.absNorm) (a := p) (fun x hx => by
      obtain ⟨P, hP, rfl⟩ := Multiset.mem_map.1 hx
      exact hge P (hM' ▸ Multiset.mem_cons_of_mem hP))
    simpa using this
  have h3 : Ideal.absNorm w * (M'.map Ideal.absNorm).prod = p * p ^ M'.card := by
    rw [← pow_succ', ← Multiset.card_cons w, ← hM', hc, ← hN, ← hprod, hM', Multiset.prod_cons, map_mul,
      map_multiset_prod]
  by_contra hlt
  push Not at hlt
  have hpos : 0 < p ^ M'.card := pow_pos hp.pos _
  nlinarith

theorem card_quotient_of_ncard {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {p : ℕ} (hp : p.Prime)
    (h : {v : HeightOneSpectrum (𝓞 E) | ((p : ℕ) : 𝓞 E) ∈ v.asIdeal}.ncard = Module.finrank ℚ E)
    (v : HeightOneSpectrum (𝓞 F)) (hv : ((p : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    Nat.card (𝓞 F ⧸ v.asIdeal) = p := by
  have := v.isPrime
  have := v.isMaximal
  obtain ⟨w, hwm, hwo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hw : ((p : ℕ) : 𝓞 E) ∈ w := by
    have h1 : ((p : ℕ) : 𝓞 F) ∈ w.under (𝓞 F) := by rw [← hwo.over]; exact hv
    simpa using (show algebraMap (𝓞 F) (𝓞 E) (p : 𝓞 F) ∈ w from h1)
  have hN : Nat.card (𝓞 E ⧸ w) = p := by
    rw [← absNorm_eq_of_ncard hp h hwm.isPrime hw, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hd : Nat.card (𝓞 F ⧸ v.asIdeal) ∣ p := by
    rw [← hN]
    exact AddSubgroup.card_dvd_of_injective (algebraMap (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w)).toAddMonoidHom
      (FaithfulSMul.algebraMap_injective (𝓞 F ⧸ v.asIdeal) (𝓞 E ⧸ w))
  refine ((Nat.dvd_prime hp).1 hd).resolve_left fun h1 => ?_
  have := (Nat.card_eq_one_iff_unique.1 h1).1
  exact not_subsingleton (𝓞 F ⧸ v.asIdeal) this

theorem card_kv : ∀ (D : D7) (i : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g i : 𝓞 D.host.F) ∈ v.asIdeal → Nat.card (kv D.host.F v) = D.host.g i := by
  intro D i v hv
  rw [← card_quotient_of_ncard (D.host.g_prime i) (D.nd.g_split i) v hv]
  have h := Formalism.UG.P.tjcosets_card_residue v
  rw [h]
  simp [qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

end GlobalTheory.SplitResidueCard
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ComplexPadicNormKappaSplitPrime
section
noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

namespace GlobalTheory.KapSplitNorm

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_natCast_eq_one (q : ℕ) [Fact q.Prime] (n : ℕ) (hn : ¬ q ∣ n) : ‖((n : ℕ) : ℂ_[q])‖ = 1 := by
  have e : ((n : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (n : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by simp
  rw [e, PadicComplex.norm_extends']
  exact Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hn)

theorem norm_iota_le_one (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (z : ℂ) (hz : IsIntegral ℤ z) : ‖ι z‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by
    convert map_isIntegral_int (ι : ℂ →+* ℂ_[q]) hz using 1 <;> first | exact Subsingleton.elim _ _ | rfl)

theorem norm_iota_unit (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : ℕ) (hn : ¬ q ∣ n) {x w : ℂ} (hx : IsIntegral ℤ x)
    (hw : IsIntegral ℤ w) (hm : (n : ℂ) = x * w) : ‖ι x‖ = 1 := by
  have e1 := norm_iota_le_one q ι x hx
  have e2 := norm_iota_le_one q ι w hw
  have e3 : ‖ι x‖ * ‖ι w‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← hm, map_natCast, norm_natCast_eq_one q n hn]
  refine le_antisymm e1 ?_
  nlinarith [norm_nonneg (ι x), norm_nonneg (ι w)]

theorem norm_rt_eq_one {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (p : ℕ)
    (hp : p.Prime) (hs : SplitK D p) (hpq : p ≠ q) : ‖ι (k.rt p)‖ = 1 := by
  have hh := k.rt_pow p hp hs
  obtain ⟨w, hw⟩ : ∃ w : 𝓞 D.host.K, w * k.pi p = (p : 𝓞 D.host.K) ^ classNumber D.host.K := by
    have hmem : (p : 𝓞 D.host.K) ^ classNumber D.host.K ∈ (k.pp p).asIdeal ^ classNumber D.host.K :=
      Ideal.pow_mem_pow (k.pp_over p hp hs) _
    rw [k.pi_gen p hp hs, Ideal.mem_span_singleton'] at hmem
    exact hmem
  have hpq' : ¬ q ∣ p ^ classNumber D.host.K := by
    intro h
    have h1 : q ∣ p := (Fact.out : q.Prime).dvd_of_dvd_pow h
    exact hpq (((Nat.prime_dvd_prime_iff_eq Fact.out hp).1 h1).symm)
  have hwK : (w : D.host.K) * (k.pi p : D.host.K) = ((p ^ classNumber D.host.K : ℕ) : D.host.K) := by
    have := congrArg (algebraMap (𝓞 D.host.K) D.host.K) hw
    simpa using this
  let fK : D.host.K →+* ℂ := D.host.φ₀.comp (algebraMap D.host.K D.host.E)
  let fK' : D.host.K →+* ℂ := D.host.φ₀.comp ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E))
  have hint : ∀ (g : D.host.K →+* ℂ) (x : 𝓞 D.host.K), IsIntegral ℤ (g (x : D.host.K)) := fun g x =>
    map_isIntegral_int g (NumberField.RingOfIntegers.isIntegral_coe x)
  have e : ∀ g : D.host.K →+* ℂ, ((p ^ classNumber D.host.K : ℕ) : ℂ) = g (k.pi p : D.host.K) * g (w : D.host.K) := by
    intro g
    rw [← map_natCast g, ← hwK, map_mul, mul_comm]
  have h1 : ‖ι (D.host.φ₀ (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E))‖ = 1 :=
    norm_iota_unit q ι _ hpq' (hint fK (k.pi p)) (hint fK w) (e fK)
  have h2 : ‖ι (D.host.φ₀ (D.host.conj (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)))‖ = 1 :=
    norm_iota_unit q ι _ hpq' (hint fK' (k.pi p)) (hint fK' w) (e fK')
  have hpow : ‖ι (k.rt p)‖ ^ (2 * classNumber D.host.K) = 1 := by
    rw [← norm_pow, ← map_pow, hh, map_div₀, norm_div, h1, h2, div_one]
  have hc := NumberField.classNumber_pos D.host.K
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by omega)).1 hpow

theorem norm_kappa_split : ∀ (D : D7) (γ₀ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], SplitK D q →
    ∀ ι : ℂ ≃+* ℂ_[q], ‖ι k.kappa‖ = ‖ι (k.rt q)‖ ^ (-(k.yP q)) := by
  intro D γ₀ k q _ hsq ι
  have hfin := yFinite D γ₀ k
  have hfinS : (Function.mulSupport
      (fun p : {p : ℕ // p.Prime ∧ SplitK D p} => k.rt p ^ (-(k.yP p)))).Finite := by
    refine (hfin.preimage Subtype.val_injective.injOn).subset ?_
    intro p hp
    refine ⟨p.2.1, p.2.2, ?_⟩
    intro h0
    apply hp
    simp [h0]
  let F : ℂ →* ℝ :=
    { toFun := fun z => ‖ι z‖
      map_one' := by simp
      map_mul' := fun x y => by simp [norm_mul] }
  have hF : ∀ z, F z = ‖ι z‖ := fun _ => rfl
  rw [KapChoice.kappa, ← hF, MonoidHom.map_finprod F hfinS,
    finprod_eq_single _ (⟨q, Fact.out, hsq⟩ : {p : ℕ // p.Prime ∧ SplitK D p})]
  · rw [hF, map_zpow₀, norm_zpow]
  · intro p hp
    have hpq : (p : ℕ) ≠ q := fun h => hp (Subtype.ext h)
    rw [hF, map_zpow₀, norm_zpow, norm_rt_eq_one k q ι p p.2.1 p.2.2 hpq, one_zpow]

end GlobalTheory.KapSplitNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ConjugateEmbeddingsInduceDifferentPrimesSplit
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.ConjPlace

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_le_one_of_int {q : ℕ} [Fact q.Prime] {K : Type} [Field K] (j : K →+* ℂ_[q]) (y : 𝓞 K) :
    ‖j (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by convert map_isIntegral_int j (RingOfIntegers.isIntegral_coe y); exact Subsingleton.elim _ _)

theorem norm_intCast_eq (q : ℕ) [Fact q.Prime] (n : ℤ) : ‖((n : ℤ) : ℂ_[q])‖ = ‖((n : ℤ) : ℚ_[q])‖ := by
  have e : ((n : ℤ) : ℂ_[q]) = algebraMap ℚ_[q] ℂ_[q] ((n : ℤ) : ℚ_[q]) := (map_intCast _ n).symm
  rw [e]
  exact PadicComplex.norm_extends' (p := q) _

theorem norm_intCast_lt_one_iff (q : ℕ) [Fact q.Prime] (n : ℤ) : ‖((n : ℤ) : ℂ_[q])‖ < 1 ↔ (q : ℤ) ∣ n := by
  rw [norm_intCast_eq]
  exact Padic.norm_intCast_lt_one_iff

theorem exists_sq_add (q : ℕ) [Fact q.Prime] (d : ℕ) (h : jacobiSym (-(d : ℤ)) q = 1) :
    ¬ (q : ℤ) ∣ d ∧ ∃ t : ℤ, (q : ℤ) ∣ t ^ 2 + d := by
  have hl : legendreSym q (-(d : ℤ)) = 1 := by rw [jacobiSym.legendreSym.to_jacobiSym]; exact h
  have h0 : ((-(d : ℤ) : ℤ) : ZMod q) ≠ 0 := by
    intro h0
    rw [(legendreSym.eq_zero_iff q _).2 h0] at hl
    exact zero_ne_one hl
  obtain ⟨r, hr⟩ := (legendreSym.eq_one_iff q h0).1 hl
  refine ⟨?_, ⟨(r.val : ℤ), ?_⟩⟩
  · intro hd
    apply h0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (dvd_neg.2 hd)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast at hr ⊢
    rw [ZMod.natCast_zmod_val]
    linear_combination (-1 : ZMod q) * hr

theorem exists_small_not_conj {E : Type} [Field E] [CharZero E] (K : IntermediateField ℚ E) (φ : E →+* ℂ) (c : E ≃ₐ[ℚ] E)
    (d q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hj : jacobiSym (-(d : ℤ)) q = 1) (ι : ℂ ≃+* ℂ_[q])
    (s : K) (hs : s * s = -(d : K)) (hc : c (algebraMap K E s) = -algebraMap K E s) :
    ∃ y : 𝓞 K, ‖ι (φ ((y : K) : E))‖ < 1 ∧ 1 ≤ ‖ι (φ (c ((y : K) : E)))‖ := by
  obtain ⟨hnd, t, ht⟩ := exists_sq_add q d hj
  have hint : IsIntegral ℤ s :=
    ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℤ), Polynomial.monic_X_pow_add_C _ two_ne_zero, by simp [sq, hs]⟩
  let B : 𝓞 K := ⟨s, hint⟩
  let j : E →+* ℂ_[q] := ι.toRingHom.comp φ
  let jK : K →+* ℂ_[q] := j.comp (algebraMap K E)
  have hc' : c (s : E) = -(s : E) := hc
  have hsE : (s : E) * (s : E) = -(d : E) := by
    have := congrArg (fun x : K => (x : E)) hs
    simpa using this
  have hcoe : ∀ u : ℤ, (((B + u : 𝓞 K) : K) : E) = (s : E) + (u : E) := by
    intro u; push_cast; rfl
  have hle : ∀ y : 𝓞 K, ‖j ((y : K) : E)‖ ≤ 1 := fun y => norm_le_one_of_int jK y

  have hodd : ∀ u : ℤ, (q : ℤ) ∣ 2 * u → (q : ℤ) ∣ u := by
    intro u h
    rcases (Nat.prime_iff_prime_int.mp (Fact.out : q.Prime)).dvd_or_dvd h with h2 | h2
    · exfalso
      have : q ∣ 2 := by exact_mod_cast h2
      exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
    · exact h2
  have key : ∀ u : ℤ, (u = t ∨ u = -t) → ‖j (((B + u : 𝓞 K) : K) : E)‖ < 1 →
      1 ≤ ‖j (c (((B + u : 𝓞 K) : K) : E))‖ := by
    intro u hu h1
    by_contra h2
    push_neg at h2
    have e2 : c (((B + u : 𝓞 K) : K) : E) = -(s : E) + (u : E) := by
      rw [hcoe, map_add, map_intCast, hc']
    have hsum : j (((B + u : 𝓞 K) : K) : E) + j (c (((B + u : 𝓞 K) : K) : E)) = (((2 * u : ℤ)) : ℂ_[q]) := by
      rw [e2, hcoe, ← map_add]
      have : (s : E) + (u : E) + (-(s : E) + (u : E)) = ((2 * u : ℤ) : E) := by push_cast; ring
      rw [this, map_intCast]
    have hlt : ‖(((2 * u : ℤ)) : ℂ_[q])‖ < 1 := by
      rw [← hsum]
      exact lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt h1 h2)
    have hdu : (q : ℤ) ∣ u := hodd u ((norm_intCast_lt_one_iff q _).1 hlt)
    have hdt : (q : ℤ) ∣ t := by
      rcases hu with rfl | rfl
      · exact hdu
      · exact dvd_neg.1 hdu
    exact hnd ((dvd_add_right (dvd_pow hdt two_ne_zero)).1 ht)
  have hprod : j (((B + t : 𝓞 K) : K) : E) * j (((B + (-t : ℤ) : 𝓞 K) : K) : E) = ((-(t ^ 2 + d) : ℤ) : ℂ_[q]) := by
    rw [← map_mul, hcoe, hcoe]
    have : ((s : E) + (t : E)) * ((s : E) + ((-t : ℤ) : E)) = ((-(t ^ 2 + d) : ℤ) : E) := by
      push_cast
      linear_combination hsE
    rw [this, map_intCast]
  have hpl : ‖((-(t ^ 2 + d) : ℤ) : ℂ_[q])‖ < 1 := (norm_intCast_lt_one_iff q _).2 (dvd_neg.2 ht)
  by_cases h1 : ‖j (((B + t : 𝓞 K) : K) : E)‖ < 1
  · exact ⟨B + t, h1, key t (Or.inl rfl) h1⟩
  · push_neg at h1
    have h2 : ‖j (((B + (-t : ℤ) : 𝓞 K) : K) : E)‖ < 1 := by
      by_contra h2
      push_neg at h2
      rw [← hprod, norm_mul] at hpl
      nlinarith
    exact ⟨B + (-t : ℤ), h2, key (-t) (Or.inr rfl) h2⟩

theorem conj_place_ne : ∀ (D : D7) (q : ℕ) [Fact q.Prime], q ≠ 2 → jacobiSym (-(D.host.d : ℤ)) q = 1 →
    ∀ ι : ℂ ≃+* ℂ_[q], ∃ y : 𝓞 D.host.K, ‖ι (D.host.φ₀ ((y : D.host.K) : D.host.E))‖ < 1 ∧
      1 ≤ ‖ι (D.host.φ₀ (D.host.conj ((y : D.host.K) : D.host.E)))‖ := by
  intro D q _ hq2 hj ι
  obtain ⟨s, h1, h2⟩ := sqrtInK D
  exact exists_small_not_conj D.host.K D.host.φ₀ D.host.conj D.host.d q hq2 hj ι s h1 h2

end GlobalTheory.ConjPlace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAnalyticSetupPeriodLatticePairStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_analyticSetup_periodLatticePair : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), admitted D N N' L L' → ∃ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), S.d = D.host.d ∧ S.Ok ∧ (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') ∧ (∀ x y, JMB.hf S.Hm (e x) (e y) = Hf D B.tor x y) ∧ (∀ x y : Matrix (Fin N') (Fin N) D.host.E, JMB.beta S.d S.Hm (e (δ • embV D B.tor x)) (e (δ • embV D B.tor y)) = D.host.φ₀ ((hYY D x y : D.host.K) : D.host.E) / (Ideal.absNorm cc : ℂ)) ∧ (∀ x ∈ La D B.tor L L', ∃ (n : ℕ) (A : Matrix (Fin N') (Fin N) D.host.E), 0 < n ∧ x = δ • embV D B.tor A ∧ (n : D.host.E) • A ∈ YYl D L L') ∧ ∀ (q r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), Nat.Coprime (Ideal.absNorm cc) q → NNBasis D B.tor δ q L L' b → S.NNBasis q fun i => e (δ • embV D B.tor (b i)) := by
  first | exact @GlobalTheory.MomSetup.periodSetup | exact GlobalTheory.MomSetup.periodSetup | (intros; apply GlobalTheory.MomSetup.periodSetup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDenOfValLeOne
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint
open scoped Matrix

namespace GlobalTheory.HAtBasis

variable {K : Type} [Field K] [NumberField K]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in

theorem _root_.GlobalTheory.HAtBasis.isLattice_of_basisAt {n : ℕ} (w : HeightOneSpectrum (𝓞 K))
    {M : Submodule (𝓞 K) (Fin n → K)} (hM : M.FG)
    {B : GL (Fin n) K} (hB : _root_.Formalism.L2.DIV.IsBasisAt w M B) : Submodule.IsLattice K M := by
  refine ⟨hM, ?_⟩
  have hcol : ∀ j, (fun i => (B : Matrix (Fin n) (Fin n) K) i j) ∈
      Submodule.span K (M : Set (Fin n → K)) := by
    intro j
    have h1 : (fun i => (B : Matrix (Fin n) (Fin n) K) i j) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal M := by
      unfold _root_.Formalism.L2.DIV.IsBasisAt at hB
      rw [hB]
      apply _root_.Formalism.HermitianLatticesTheory.locBasic_le_locS
      exact Submodule.subset_span ⟨j, rfl⟩
    obtain ⟨s, hs, hsx⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff w.asIdeal M _).1 h1
    have hs0 : (s : K) ≠ 0 := by
      intro h0
      apply hs
      have hs' : s = 0 := by exact_mod_cast h0
      rw [hs']
      exact w.asIdeal.zero_mem
    have h2 := Submodule.smul_mem (Submodule.span K (M : Set (Fin n → K))) ((s : K)⁻¹)
      (Submodule.subset_span hsx)
    convert h2 using 1
    funext i
    simp [Algebra.smul_def, hs0]
  rw [eq_top_iff]
  intro x _
  have hx : x = ∑ j, ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x j •
      (fun i => (B : Matrix (Fin n) (Fin n) K) i j) := by
    have hBx : (B : Matrix (Fin n) (Fin n) K).mulVec
        (((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec]
      simp
    conv_lhs => rw [← hBx]
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hx]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hcol j)

variable {ι : Type} [Fintype ι] {a : ℕ}

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
omit [NumberField K] in

theorem _root_.GlobalTheory.HAtBasis.polyAction_invTranspose_inv (lam : ι → _root_.Formalism.BasicNotions.DomWeight a)
    (B : ι → GL (Fin a) K) (F : _root_.Formalism.L2.DIV.Pol K ι a) :
    _root_.Formalism.L2.DIV.actP lam (fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ))⁻¹ F =
      (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
        _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) F := by
  have hg : ∀ τ, (((fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ))⁻¹ τ : GL (Fin a) K) : Matrix (Fin a) (Fin a) K) =
      (B τ : Matrix (Fin a) (Fin a) K)ᵀ := fun τ => rfl
  simp only [_root_.Formalism.L2.DIV.actP, _root_.Formalism.L2.DIV.trAct, _root_.Formalism.L2.DIV.detTw_eq, LinearMap.smul_apply, AlgHom.toLinearMap_apply, hg,
    Matrix.det_transpose, Matrix.transpose_transpose]

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
private theorem valuation_coe_eq_one_of_notMem {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) {s : 𝓞 K} (hs : s ∉ w.asIdeal) : w.valuation K (s : K) = 1 := by
  rw [show (s : K) = algebraMap (𝓞 K) K s from rfl, HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w s).2 hs

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in
private theorem exists_notMem_mul_eq_integer_of_valuation_le_one {K : Type} [Field K] [NumberField K]
    (w : HeightOneSpectrum (𝓞 K)) (x : K) (hx : w.valuation K x ≤ 1) :
    ∃ s : 𝓞 K, s ∉ w.asIdeal ∧ ∃ c : 𝓞 K, (s : K) * x = (c : K) := by
  have h1 : x ∈ (w.valuation K).valuationSubring := hx
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring] at h1
  have h3 : x ∈ (HeightOneSpectrum.valuationSubringAtPrime K w).toSubring := h1
  rw [HeightOneSpectrum.valuationSubringAtPrime_toSubring] at h3
  have h2 : x ∈ _root_.GlobalTheory.LatBasisAt.locRing w := by
    unfold _root_.GlobalTheory.LatBasisAt.locRing
    exact h3
  obtain ⟨c, s, hs, rfl⟩ := (_root_.GlobalTheory.LatBasisAt.mem_locRing w x).1 h2
  refine ⟨s, hs, c, ?_⟩
  have hs0 : algebraMap (𝓞 K) K s ≠ 0 := _root_.GlobalTheory.LatBasisAt.algebraMap_ne_zero w hs
  change algebraMap (𝓞 K) K s * (algebraMap (𝓞 K) K c * (algebraMap (𝓞 K) K s)⁻¹) =
    algebraMap (𝓞 K) K c
  field_simp

open NumberField IsDedekindDomain MvPolynomial in
open scoped Matrix in
variable {K : Type} [Field K] [NumberField K] in
variable {ι : Type} [Fintype ι] {a : ℕ} in

theorem _root_.GlobalTheory.HAtBasis.mem_HAt_iff : ∀ (K : Type) [Field K]
    [NumberField K] (w : HeightOneSpectrum (𝓞 K)) (ι : Type) [Fintype ι] (a : ℕ)
    (lam : ι → _root_.Formalism.BasicNotions.DomWeight a) (M : ι → Submodule (𝓞 K) (Fin a → K)) (B : ι → GL (Fin a) K),
    _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.LatWithBasis w M B → ∀ F : _root_.Formalism.L2.DIV.VV K lam,
      F ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt w lam M ↔
        ∀ m, w.valuation K (((∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
          _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) (F : _root_.Formalism.L2.DIV.Pol K ι a)).coeff m) ≤ 1 := by
  intro K _ _ w ι _ a lam M B hMB F
  have hB' : ∀ τ, _root_.Formalism.L2.DIV.IsBasisAt w (_root_.Formalism.L2.DIV.dualFr (M τ)) (_root_.Formalism.BasicNotions.inside₂ K a (B τ)) :=
    fun τ => _root_.GlobalTheory.DualWeylDual.isBasisAt_dualFr w (hMB τ).1 (hMB τ).2
  have hlat : ∀ τ, Submodule.IsLattice K (_root_.Formalism.L2.DIV.dualFr (M τ)) := fun τ =>
    _root_.GlobalTheory.DualLat.isLattice_dualFr _ (_root_.GlobalTheory.HAtBasis.isLattice_of_basisAt w (hMB τ).1 (hMB τ).2)
  have hloc := (_root_.GlobalTheory.TransLoc.nabDelLoc_free_leVV.1 K ι a lam
    (fun τ => _root_.Formalism.L2.DIV.dualFr (M τ)) hlat w (fun τ => _root_.Formalism.BasicNotions.inside₂ K a (B τ)) hB').1
  have step1 : F ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt w lam M ↔
      (F : _root_.Formalism.L2.DIV.Pol K ι a) ∈ _root_.Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (_root_.Formalism.L2.DIV.nabP lam fun τ => _root_.Formalism.L2.DIV.dualFr (M τ)) := by
    unfold _root_.GlobalTheory.IndefiniteRowSideFullHecke.SubstitutionAdjoint.HAt _root_.Formalism.L2.DIV.nabK
    rw [_root_.PI.LocGlobInclWork.mem_localization_iff, _root_.PI.LocGlobInclWork.mem_localization_iff]
    rfl
  rw [step1, hloc, _root_.GlobalTheory.TransLoc.mem_map_actP, _root_.GlobalTheory.HAtBasis.polyAction_invTranspose_inv]
  set G : _root_.Formalism.L2.DIV.Pol K ι a := (∏ τ, (B τ : Matrix (Fin a) (Fin a) K).det ^ (lam τ).detShift) •
    _root_.Formalism.GradedWeylDivisibility.blockAct K (fun τ => (B τ : Matrix (Fin a) (Fin a) K)) (F : _root_.Formalism.L2.DIV.Pol K ι a) with hG
  have hcoeff : ∀ (s : 𝓞 K) m, coeff m (s • G) = (s : K) * coeff m G := by
    intro s m
    erw [Algebra.smul_def, MvPolynomial.algebraMap_apply, coeff_C_mul]
  constructor
  · intro hGm m
    obtain ⟨s, hs, hsG⟩ := (_root_.PI.LocGlobInclWork.mem_localization_iff _ _ _).1 hGm
    obtain ⟨P, hP⟩ := _root_.GlobalTheory.LocInt.exists_map_eq_of_mem_nabStd lam hsG
    have hc : coeff m (s • G) = ((coeff m P : 𝓞 K) : K) := by
      have h' : coeff m (_root_.Formalism.L2.DIV.toK K _ P) = coeff m (s • G) := congrArg (coeff m) hP
      rw [← h']
      simp [_root_.Formalism.L2.DIV.toK, coeff_map]
    rw [hcoeff] at hc
    have hs0 : (s : K) ≠ 0 := _root_.GlobalTheory.LatBasisAt.algebraMap_ne_zero w hs
    have e : coeff m G = (s : K)⁻¹ * ((coeff m P : 𝓞 K) : K) := by
      rw [← hc, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
    rw [e, map_mul, map_inv₀, valuation_coe_eq_one_of_notMem w hs, inv_one, one_mul]
    exact HeightOneSpectrum.valuation_le_one w _
  · intro hint
    choose sf hsf c hc using fun m => exists_notMem_mul_eq_integer_of_valuation_le_one w _ (hint m)
    refine (_root_.PI.LocGlobInclWork.mem_localization_iff _ _ _).2 ⟨∏ m ∈ G.support, sf m, ?_, ?_⟩
    · intro hmem
      obtain ⟨m, _, hm⟩ := Ideal.IsPrime.prod_mem_iff.1 hmem
      exact hsf m hm
    · have hGV : G ∈ _root_.Formalism.L2.DIV.VV K lam :=
        Submodule.smul_mem _ _ (_root_.Formalism.L2.DIV.ps_blockAct_mem_VV lam _ F.2)
      refine _root_.GlobalTheory.DetSat.mem_nabStd_of_det_mul_integral K ι a lam (fun _ => 0) _
        (Submodule.smul_of_tower_mem _ _ hGV) fun m => ?_
      simp only [pow_zero, Finset.prod_const_one, one_mul]
      change IsIntegral ℤ (coeff m ((∏ m ∈ G.support, sf m) • G))
      rw [hcoeff]
      by_cases hm : m ∈ G.support
      · rw [← Finset.mul_prod_erase _ _ hm]
        push_cast
        rw [mul_comm ((sf m : 𝓞 K) : K), mul_assoc, hc m]
        have hI := RingOfIntegers.isIntegral_coe ((∏ i ∈ G.support.erase m, sf i) * c m)
        convert hI using 1
        simp
      · rw [notMem_support_iff.1 hm, mul_zero]
        exact isIntegral_zero

end GlobalTheory.HAtBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLiftHalfLatticeRationalStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_halfLattice_rational : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (cA c : ℕ), A.AA.FG → A.AA ≠ ⊥ → (∀ P ∈ S, conjPrime₂ P ∉ S) → A.AAUnit S → IsSdLat N → IsSdLat N' → 0 < cA → 0 < c → ∀ x ∈ divLat cA (homAt S N N'), ∃ t ∈ halfAO S (per A N N') (cA * c), t - x ∈ mulLat c (homAt S N N') := by
  first | exact @GlobalTheory.MomT.exists_lift_halfAO | exact GlobalTheory.MomT.exists_lift_halfAO | (intros; apply GlobalTheory.MomT.exists_lift_halfAO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HermitianSpaceOppositeFormSignatureConditionStatement
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianSpaceOppositeForm_signatureCondition : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (W : HSpace E), W.SigOK → (GlobalTheory.NegSpace.neg W).SigOK := by
  first | exact @GlobalTheory.NegSpace.sigOK_neg | exact GlobalTheory.NegSpace.sigOK_neg | (intros; apply GlobalTheory.NegSpace.sigOK_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MomentsTranslateRationalPointUnitDenominatorStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moments_translate_rationalPoint_unitDenominator : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (ϖ : 𝓞 X.E) (p : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) [Fact p.Prime] (lam : TaylorLogMetric.Qbar →+* ℂ_[p]) (ι : X.K →+* ℂ_[p]) (un : X.Tau → ℂ_[p]), X.Ok → A.LaHyp a b ∅ → A.AA ≠ ⊥ → A.ESmooth a b → ϖ * X.conjO ϖ = (p : 𝓞 X.E) → IsCoprime ϖ (X.conjO ϖ) → IsSdLat N → IsSdLat N' → PtMom A a b lam ι un (star (ϖ : X.E) / (ϖ : X.E)) → ∀ (t : HomE X.E a b) (n : ℕ), Nat.Coprime n p → ((n : X.E) * (ϖ : X.E)) • t ∈ per A N N' → (∀ m, jetC A.cD (Wx A t (A.e a b N N')) m ∈ TaylorLogMetric.Qbar) ∧ InIntClosure (per A N N' : Set (HomE X.E a b)) (ptTab ι un) Set.univ fun m => TaylorLogMetric.lamC lam (jetC A.cD (Wx A t (A.e a b N N')) m) := by
  first | exact @GlobalTheory.MomT.UnitTr.moments_unit_translate | exact GlobalTheory.MomT.UnitTr.moments_unit_translate | (intros; apply GlobalTheory.MomT.UnitTr.moments_unit_translate <;> assumption)
end

