import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.AdelicDegreeTameRamification
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.EqOfLeOfAbsNormEq
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0707
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetOfMemNhds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0866
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticSubfieldRootDiscriminant
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke Polynomial

namespace GlobalTheory

theorem finrank_eq_two_of_adjoin_sqrt_eq_top (K : Type) [Field K] [NumberField K] (a : ℤ) (x : K)
    (hx : x ^ 2 = (a : K)) (hadj : IntermediateField.adjoin ℚ {x} = ⊤) (hsf : Squarefree a) (h1 : a ≠ 1) :
    Module.finrank ℚ K = 2 := by
  have hirr : Irreducible (X ^ 2 - C (a : ℚ)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (Formalism.HF.P.quad_not_sq_rat a hsf h1)
  have hmon : (X ^ 2 - C (a : ℚ)).Monic := monic_X_pow_sub_C _ two_ne_zero
  have hev : aeval x (X ^ 2 - C (a : ℚ)) = 0 := by simp [hx]
  have hmin : minpoly ℚ x = X ^ 2 - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hev hmon).symm
  have := IntermediateField.adjoin.finrank (K := ℚ) (x := x) (.of_finite ℚ x)
  rw [hmin, natDegree_X_pow_sub_C, hadj, IntermediateField.finrank_top'] at this
  exact this

theorem adjoin_gen_eq_top_rat {E : Type} [Field E] [NumberField E] (y : E) :
    IntermediateField.adjoin ℚ {IntermediateField.AdjoinSimple.gen ℚ y} = ⊤ := by
  apply IntermediateField.lift_injective
  exact (IntermediateField.lift_adjoin_simple ℚ _ (IntermediateField.AdjoinSimple.gen ℚ y)).trans
    (IntermediateField.lift_top ℚ (IntermediateField.adjoin ℚ {y})).symm

theorem rootDiscr_and_different_quadField :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
      rootDiscr (AdelicDegreeTameRamification.quadField H) = √(H.d : ℝ) ∧
      (differentIdeal ℤ (𝓞 (AdelicDegreeTameRamification.quadField H))).map (algebraMap (𝓞 (AdelicDegreeTameRamification.quadField H)) (𝓞 E)) =
        Ideal.span {H.rt} := by
  intro E _ _ _ H
  have hd16 := H.d_mod
  have hb2 : ((H.rt : 𝓞 E) : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  obtain ⟨x, hxdef, hadj⟩ : ∃ x : AdelicDegreeTameRamification.quadField H, (x : E) = (H.rt : E) ∧
      IntermediateField.adjoin ℚ {x} = ⊤ :=
    ⟨IntermediateField.AdjoinSimple.gen ℚ _, rfl, adjoin_gen_eq_top_rat _⟩
  have hx : x ^ 2 = ((-(H.d : ℤ) : ℤ) : AdelicDegreeTameRamification.quadField H) := by
    apply Subtype.ext
    push_cast
    rw [hxdef, hb2]
  have hint : IsIntegral ℤ x := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [hx, ← eq_intCast (algebraMap ℤ (AdelicDegreeTameRamification.quadField H))]
    exact isIntegral_algebraMap
  have hsf : Squarefree (-(H.d : ℤ)) := by
    rw [← Int.squarefree_natAbs, Int.natAbs_neg, Int.natAbs_natCast]
    exact H.d_prime.squarefree
  obtain ⟨x', hx'⟩ : ∃ x' : 𝓞 (AdelicDegreeTameRamification.quadField H), (x' : AdelicDegreeTameRamification.quadField H) = x := ⟨⟨x, hint⟩, rfl⟩
  have hdiff := Formalism.MainNotions.UnusedSlot33.HK.different_quad (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf
    (by omega) (by omega) x' hx'
  have h2 := finrank_eq_two_of_adjoin_sqrt_eq_top (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega)
  have hD := Formalism.HF.P.quadDiscr_ne_one (AdelicDegreeTameRamification.quadField H) (-(H.d : ℤ)) x hx hadj hsf (by omega) (by omega)
  refine ⟨?_, ?_⟩
  · rw [rootDiscr_def, h2, hD, Real.sqrt_eq_rpow]
    simp
  · rw [hdiff, Ideal.map_span, Set.image_singleton]
    congr 2
    apply RingOfIntegers.coe_injective
    show ((x' : AdelicDegreeTameRamification.quadField H) : E) = _
    rw [hx', hxdef]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmBasisLiftPdThickening
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BasisLift

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q] {σ ι : Type} [Fintype ι]

theorem comb_add (b c : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (b + c) e = comb b e + comb c e := by
  simp [comb, map_add, add_smul, Finset.sum_add_distrib]

theorem comb_sub (b c : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (b - c) e = comb b e - comb c e := by
  simp [comb, map_sub, sub_smul, Finset.sum_sub_distrib]

theorem comb_zero (e : ι → MvPowerSeries σ Q) : comb (0 : ι → B) e = 0 := by
  simp [comb]

theorem comb_mul (r : B) (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (fun i => r * b i) e = algebraMap B Q r • comb b e := by
  simp [comb, map_mul, mul_smul, Finset.smul_sum]

theorem comb_mul_right (r : B) (b : ι → B) (e : ι → MvPowerSeries σ Q) :
    comb (fun i => b i * r) e = algebraMap B Q r • comb b e := by
  simp only [mul_comm _ r]; exact comb_mul r b e

theorem coeff_comb (b : ι → B) (e : ι → MvPowerSeries σ Q) (α : σ →₀ ℕ) :
    coeff α (comb b e) = ∑ i, algebraMap B Q (b i) * coeff α (e i) := by
  simp only [comb, map_sum, coeff_smul]

end GlobalTheory.BasisLift

open GlobalTheory.BasisLift in

theorem GlobalTheory.basis_lift : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (C : Type) [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ Θ : Q →+* C, (∀ b, Θ (algebraMap B Q b) = algebraMap O C (θ b)) → ∀ (ι : Type) [Fintype ι] (e : ι → MvPowerSeries (Fin d) Q), (∀ i, QL μ ⊤ (e i)) → IsBasis (fun i => map θ (μ i)) (fun i => map Θ (e i)) → Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ (Ideal.span {(p : B)}) → IsBasis μ e := by
  intro p _ B O Q _ _ _ _ θ hF d μ hL C _ _ hC Θ hΘ ι _ e he hB hch
  obtain ⟨u, hu⟩ := hF.unit_p
  have hmapP : algebraMap B Q (p : B) = (p : Q) := map_natCast _ _
  have hconst : ∀ i, constantCoeff (up Q μ i) = 0 := fun i => by
    simp [up, constantCoeff_map, hL.const i]
  have ql0 : ∀ N : Ideal B, QL μ N (0 : MvPowerSeries (Fin d) Q) := by
    intro N
    refine ⟨by simp, fun i => ⟨0, N.zero_mem, by simp [lin]⟩, fun α => ⟨0, N.zero_mem, ?_⟩⟩
    have h0 := formalCoboundary_smul hconst (0 : Q) (0 : MvPowerSeries (Fin d) Q)
    simp only [zero_smul] at h0
    simp [h0]
  have hsm : ∀ n : ℕ, (Ideal.span {(p : B)} ^ n • ⊤ : Submodule B B) = Ideal.span {(p : B) ^ n} := by
    intro n; rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
  have key : ∀ t ∈ Ideal.span {(p : B)}, ∃ t' : B, (↑u⁻¹ : Q) * algebraMap B Q t = algebraMap B Q t' := by
    intro t ht
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 ht
    refine ⟨a, ?_⟩
    rw [map_mul, hmapP, ← hu, mul_comm, mul_assoc, Units.mul_inv, mul_one]

  have chainE : ∀ N, Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ N →
      ∀ f, QL μ ⊤ f → ∃ (b : ι → B) (s : MvPowerSeries (Fin d) Q),
        In (⊤ : Ideal B) s ∧ QL μ N (f - comb b e - s) := by
    intro N hN
    induction hN with
    | refl => intro f hf; exact ⟨0, 0, fun α => ⟨0, trivial, by simp⟩, by simpa [comb_zero] using hf⟩
    | tail _ hst ih =>
      intro f hf
      obtain ⟨b, s, hs, hq⟩ := ih f hf
      obtain ⟨b', s', -, hs', hq'⟩ := GlobalTheory.T.quasiLogarithm_devissage_generation_step p B O Q θ hF d μ hL C hC Θ hΘ ι e he hB _ _ hst _ hq
      refine ⟨b + b', s + s', ?_, ?_⟩
      · intro α
        obtain ⟨x, -, hx⟩ := hs α
        obtain ⟨y, -, hy⟩ := hs' α
        exact ⟨x + y, trivial, by rw [map_add, hx, hy, map_add]⟩
      · rw [comb_add]; convert hq' using 1; abel

  have divP : ∀ h : MvPowerSeries (Fin d) Q, QL μ (Ideal.span {(p : B)}) h →
      QL μ ⊤ ((↑u⁻¹ : Q) • h) ∧ h = (p : Q) • ((↑u⁻¹ : Q) • h) := by
    intro h ⟨h0, hl, hc⟩
    refine ⟨⟨?_, fun i => ?_, fun α => ?_⟩, ?_⟩
    · rw [← coeff_zero_eq_constantCoeff_apply, coeff_smul, coeff_zero_eq_constantCoeff_apply, h0, mul_zero]
    · obtain ⟨t, ht, he'⟩ := hl i
      obtain ⟨t', ht'⟩ := key t ht
      refine ⟨t', trivial, ?_⟩
      simp only [lin, coeff_smul] at he' ⊢
      rw [he', ht']
    · obtain ⟨t, ht, he'⟩ := hc α
      obtain ⟨t', ht'⟩ := key t ht
      refine ⟨t', trivial, ?_⟩
      rw [formalCoboundary_smul hconst, coeff_smul, he', ht']
    · rw [smul_smul, ← hu, Units.mul_inv, one_smul]
  have E1 : ∀ f : {f : MvPowerSeries (Fin d) Q // QL μ ⊤ f}, ∃ (b : ι → B) (s g : MvPowerSeries (Fin d) Q),
      In (⊤ : Ideal B) s ∧ QL μ ⊤ g ∧ f.1 = comb b e + s + (p : Q) • g := by
    intro ⟨f, hf⟩
    obtain ⟨b, s, hs, hq⟩ := chainE _ hch f hf
    obtain ⟨hg, hgq⟩ := divP _ hq
    exact ⟨b, s, _, hs, hg, by rw [← hgq]; abel⟩
  choose bF sF gF hsF hgF heqF using E1

  have V : ∀ α : Fin d →₀ ℕ, ∃ v : ℕ, ∀ g, QL μ ⊤ g → (p : Q) ^ v * coeff α g ∈ (algebraMap B Q).range := by
    intro α
    by_cases hα : α = 0
    · refine ⟨0, fun g hg => ⟨0, ?_⟩⟩
      rw [hα, coeff_zero_eq_constantCoeff_apply, hg.1]; simp
    · obtain ⟨i, hi⟩ : ∃ i, α i ≠ 0 := by
        by_contra h; push_neg at h; exact hα (Finsupp.ext fun i => by simp [h i])
      obtain ⟨v, n, hn, hαi⟩ := Nat.exists_eq_pow_mul_and_not_dvd hi p (Fact.out : p.Prime).one_lt.ne'
      have hcop : Nat.Coprime n p := Nat.Coprime.symm (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hn)
      obtain ⟨w, hw⟩ := hF.unit_coprime n hcop
      refine ⟨v, fun g hg => ?_⟩
      obtain ⟨t, -, ht⟩ := GlobalTheory.T.divided_in_of_quasi_logarithm p B O Q θ hF d μ hL ⊤ g hg α i
      refine ⟨↑w⁻¹ * t, ?_⟩
      rw [hαi] at ht
      push_cast at ht
      rw [map_mul, ← ht]
      have hw1 : algebraMap B Q (↑w⁻¹) * (n : Q) = 1 := by
        rw [← map_natCast (algebraMap B Q) n, ← map_mul, ← hw, Units.inv_mul, map_one]
      linear_combination ((p : Q) ^ v * coeff α g) * hw1

  have chainU : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), comb c e = s → ∀ N,
      Relation.ReflTransGen (fun N N' : Ideal B => IsStep p θ N' N) ⊤ N → In (⊤ : Ideal B) s →
        (∀ i, c i ∈ N) ∧ In N s := by
    intro c s hcs N hN hs
    induction hN with
    | refl => exact ⟨fun _ => trivial, hs⟩
    | tail _ hst ih =>
      exact GlobalTheory.T.quasiLogarithm_devissage_step_independent p B O Q θ hF d μ hL C hC Θ hΘ ι e he hB _ _ hst c s ih.1 ih.2
        (by rw [hcs, sub_self]; exact ql0 _)
  have U1 : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s →
      ∃ (c' : ι → B) (s' : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s' ∧ comb c' e = s' ∧
        ∀ i, c i = c' i * p := by
    intro c s hs hcs
    obtain ⟨hc, hsp⟩ := chainU c s hcs _ hch hs
    choose c' hc' using fun i => Ideal.mem_span_singleton'.1 (hc i)
    refine ⟨c', (↑u⁻¹ : Q) • s, ?_, ?_, fun i => (hc' i).symm⟩
    · intro α
      obtain ⟨t, ht, h1⟩ := hsp α
      obtain ⟨t', h2⟩ := key t ht
      exact ⟨t', trivial, by rw [coeff_smul, h1, h2]⟩
    · have hc2 : c = fun i => c' i * p := funext fun i => (hc' i).symm
      rw [← hcs, hc2, comb_mul_right, smul_smul, hmapP, ← hu, Units.inv_mul, one_smul]
  have U2 : ∀ K (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s →
      ∀ i, c i ∈ Ideal.span {(p : B) ^ K} := by
    intro K
    induction K with
    | zero => intro c s _ _ i; simp
    | succ K ih =>
      intro c s hs hcs i
      obtain ⟨c', s', hs', hcs', hc⟩ := U1 c s hs hcs
      rw [hc i, pow_succ]
      exact Ideal.mem_span_singleton.2 (mul_dvd_mul_right (Ideal.mem_span_singleton.1 (ih c' s' hs' hcs' i)) _)
  have U3 : ∀ (c : ι → B) (s : MvPowerSeries (Fin d) Q), In (⊤ : Ideal B) s → comb c e = s → c = 0 := by
    intro c s hs hcs; funext i
    refine hF.complete.toIsHausdorff.haus (c i) fun n => ?_
    rw [SModEq.sub_mem, sub_zero, hsm]; exact U2 n c s hs hcs i
  refine ⟨he, fun f hf => ?_⟩

  obtain ⟨Fs, hF0, hFs⟩ : ∃ Fs : ℕ → {f : MvPowerSeries (Fin d) Q // QL μ ⊤ f},
      Fs 0 = ⟨f, hf⟩ ∧ ∀ k, Fs (k + 1) = ⟨gF (Fs k), hgF (Fs k)⟩ :=
    ⟨fun k => Nat.rec ⟨f, hf⟩ (fun _ y => ⟨gF y, hgF y⟩) k, rfl, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℕ → ι → B, ∀ K i, x K i = ∑ k ∈ Finset.range K, (p : B) ^ k * bF (Fs k) i :=
    ⟨_, fun _ _ => rfl⟩
  have hrec : ∀ K, ∃ S, In (⊤ : Ideal B) S ∧ f = comb (x K) e + S + (p : Q) ^ K • (Fs K).1 := by
    intro K
    induction K with
    | zero =>
      have hx0 : x 0 = 0 := funext fun i => by simp [hx]
      refine ⟨0, fun α => ⟨0, trivial, by simp⟩, ?_⟩
      rw [hx0, comb_zero, hF0]; simp
    | succ K ih =>
      obtain ⟨S, hS, hfe⟩ := ih
      refine ⟨S + (p : Q) ^ K • sF (Fs K), ?_, ?_⟩
      · intro α
        obtain ⟨a, -, ha⟩ := hS α
        obtain ⟨c, -, hc⟩ := hsF (Fs K) α
        exact ⟨a + p ^ K * c, trivial, by simp [coeff_smul, ha, hc, map_add, map_mul, map_pow, map_natCast]⟩
      · have h1 : x (K + 1) = x K + fun i => (p : B) ^ K * bF (Fs K) i := by
          funext i; simp [hx, Finset.sum_range_succ]
        have h2 : (Fs (K + 1)).1 = gF (Fs K) := by rw [hFs]
        rw [h1, comb_add, comb_mul, h2, map_pow, map_natCast]
        conv_lhs => rw [hfe, heqF (Fs K)]
        simp only [smul_add, smul_smul, ← pow_succ]
        abel
  have hcau : ∀ m n, m ≤ n → ∀ i, x n i - x m i ∈ Ideal.span {(p : B) ^ m} := by
    intro m n hmn i
    rw [hx, hx, ← Finset.sum_range_add_sum_Ico _ hmn, add_sub_cancel_left]
    refine Ideal.sum_mem _ fun k hk => ?_
    exact Ideal.mem_span_singleton.2
      (dvd_mul_of_dvd_left (pow_dvd_pow _ (Finset.mem_Ico.1 hk).1) _)
  have hlim : ∀ i, ∃ L : B, ∀ n, x n i - L ∈ Ideal.span {(p : B) ^ n} := by
    intro i
    obtain ⟨L, hL'⟩ := hF.complete.toIsPrecomplete.prec (f := fun n => x n i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, hsm, ← neg_sub]; exact neg_mem (hcau m n hmn i))
    exact ⟨L, fun n => by have := hL' n; rwa [SModEq.sub_mem, hsm] at this⟩
  choose L hLx using hlim
  have hIn : In (⊤ : Ideal B) (f - comb L e) := by
    intro α
    obtain ⟨v, hv⟩ := V α
    obtain ⟨S, hS, hfe⟩ := hrec v
    choose c hc using fun i => Ideal.mem_span_singleton'.1 (hLx i v)
    have hmem : coeff α (f - comb L e) ∈ (algebraMap B Q).range := by
      rw [hfe]
      have e1 : comb (x v) e + S + (p : Q) ^ v • (Fs v).1 - comb L e =
          (comb (x v) e - comb L e) + S + (p : Q) ^ v • (Fs v).1 := by abel
      rw [e1, ← comb_sub, map_add, map_add, coeff_comb, coeff_smul]
      refine add_mem (add_mem (Subring.sum_mem _ fun i _ => ?_) ?_) (hv _ (Fs v).2)
      · rw [show (x v - L) i = c i * (p : B) ^ v from (hc i).symm,
          show algebraMap B Q (c i * (p : B) ^ v) * coeff α (e i) =
            algebraMap B Q (c i) * ((p : Q) ^ v * coeff α (e i)) by
              rw [map_mul, map_pow, map_natCast, mul_assoc]]
        exact Subring.mul_mem _ ⟨c i, rfl⟩ (hv _ (he i))
      · obtain ⟨a, -, ha⟩ := hS α; exact ⟨a, ha.symm⟩
    obtain ⟨b, hb⟩ := hmem
    exact ⟨b, trivial, hb.symm⟩
  refine ⟨L, hIn, fun y hy => ?_⟩
  have hs : In (⊤ : Ideal B) (comb (y - L) e) := by
    intro α
    obtain ⟨a, -, ha⟩ := hIn α
    obtain ⟨a', -, ha'⟩ := hy α
    refine ⟨a - a', trivial, ?_⟩
    rw [map_sub, ← ha, ← ha', ← map_sub, comb_sub]
    congr 1; abel
  exact sub_eq_zero.1 (U3 _ _ hs rfl)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealMapOneInjective
section
open Matrix
open scoped ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (hermForm)
open GlobalTheory.PELU
open GlobalTheory.PeriodCoord (realMap realMap_apply realMap_inj imForm imForm_apply herm_add_left herm_add_right
  herm_smul_left herm_smul_right herm_conj riemann_symm eq_zero_of_imForm det_ne_zero_of_pos colMat colMat_apply
  exists_finset_of_mem_nhds)

namespace GlobalTheory.PerCoordU

noncomputable section

variable {g : ℕ}

def Tsp {O : Type} [Ring O] (bar : O → O) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) :
    Submodule ℂ (Matrix (Fin g) (Fin g) ℂ) where
  carrier := {S | Sᵀ = S ∧ ∀ a, S * (ρ (bar a)).map star = (ρ a)ᴴ * S}
  zero_mem' := ⟨by simp, fun a => by simp⟩
  add_mem' := by
    rintro S T ⟨h1, h2⟩ ⟨h3, h4⟩
    exact ⟨by rw [transpose_add, h1, h3], fun a => by rw [Matrix.add_mul, Matrix.mul_add, h2, h4]⟩
  smul_mem' := by
    rintro c S ⟨h1, h2⟩
    exact ⟨by rw [transpose_smul, h1], fun a => by rw [Matrix.smul_mul, Matrix.mul_smul, h2]⟩

theorem star_mulVec_map (M : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : star (M *ᵥ z) = M.map star *ᵥ star z := by
  funext i; simp [mulVec, dotProduct]

theorem herm_mulVec_left (M A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M (A *ᵥ z) w = hermForm (Aᵀ * M) z w := by
  unfold hermForm
  rw [← mulVec_mulVec, dotProduct_comm, dotProduct_mulVec, dotProduct_comm, ← mulVec_transpose]

theorem herm_mulVec_right (M A : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    hermForm M z (A *ᵥ w) = hermForm (M * A.map star) z w := by
  unfold hermForm
  rw [star_mulVec_map, mulVec_mulVec]

theorem herm_single (M : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (i j : Fin g) :
    hermForm M (Pi.single i c) (Pi.single j 1) = c * M i j := by
  simp [hermForm, ← Pi.single_star, mulVec_single]

theorem sesq_ext {N N' : Matrix (Fin g) (Fin g) ℂ} (h : ∀ z w, (hermForm N z w).im = (hermForm N' z w).im) : N = N' := by
  ext i j
  have h1 := h (Pi.single i 1) (Pi.single j 1)
  have h2 := h (Pi.single i Complex.I) (Pi.single j 1)
  simp only [herm_single] at h1 h2
  simp at h1 h2
  apply Complex.ext <;> linarith

variable {O : Type} [Ring O] {bar : O → O} {D : PLat O bar} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}

theorem ext_per {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ρ P) {W : Type} [AddCommGroup W] [Module ℝ W]
    {f f' : (Fin g → ℂ) →ₗ[ℝ] W} (h : ∀ x, f (P x) = f' (P x)) : f = f' :=
  LinearMap.ext_on_range hP.2.2.2.1 h

theorem relation_per {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P) (c : D.La →₀ ℝ)
    (hc : Finsupp.linearCombination ℝ P₀ c = 0) : Finsupp.linearCombination ℝ P c = 0 := by
  obtain ⟨M₀, -, -, h₀⟩ := hP₀.2.2.2.2
  obtain ⟨M, -, hpos, h⟩ := hP.2.2.2.2
  refine eq_zero_of_imForm hpos (ext_per hP fun y => ?_)
  have := congrArg (fun u => imForm M₀ u (P₀ y)) hc
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, map_smul, LinearMap.sum_apply,
    LinearMap.smul_apply, imForm_apply, h, h₀, map_zero, LinearMap.zero_apply] at this ⊢
  exact this

theorem exists_colMat_per {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) :
    ∃ α β : Fin g → (D.La →₀ ℂ), ∀ P : D.La →+ (Fin g → ℂ), IsPeriod D ρ P →
      ∀ x, P x = realMap (colMat α P) (colMat β P) (P₀ x) := by
  have hs : ∀ z : Fin g → ℂ, ∃ c : D.La →₀ ℝ, Finsupp.linearCombination ℝ P₀ c = z := fun z => by
    have : z ∈ Submodule.span ℝ (Set.range P₀) := by rw [hP₀.2.2.2.1]; trivial
    rwa [← Finsupp.range_linearCombination] at this
  choose r hr using fun j => hs (Pi.single j 1)
  choose r' hr' using fun j => hs (Pi.single j Complex.I)
  let k : (D.La →₀ ℝ) → (D.La →₀ ℂ) := Finsupp.mapRange (fun t => (t : ℂ)) (by simp)
  have hk : ∀ (f : D.La → Fin g → ℂ) c, Finsupp.linearCombination ℂ f (k c) = Finsupp.linearCombination ℝ f c :=
    fun f c => by
      simp only [Finsupp.linearCombination_apply, k]
      rw [Finsupp.sum_mapRange_index (by simp)]
      rfl
  refine ⟨fun j => (1 / 2 : ℂ) • k (r j) - (Complex.I / 2) • k (r' j),
    fun j => (1 / 2 : ℂ) • k (r j) + (Complex.I / 2) • k (r' j), fun P hP x => ?_⟩
  have := relation_per hP₀ hP (Finsupp.single x 1 - ∑ j, ((P₀ x j).re • r j + (P₀ x j).im • r' j)) (by
    simp only [map_sub, map_sum, map_add, map_smul, hr, hr', Finsupp.linearCombination_single, one_smul]
    funext i
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_add_distrib])
  simp only [map_sub, map_sum, map_add, map_smul, Finsupp.linearCombination_single, one_smul, sub_eq_zero] at this
  rw [this]
  funext i
  simp only [realMap_apply, Pi.add_apply, mulVec, dotProduct, colMat_apply, map_sub, map_add, map_smul, hk,
    Finset.sum_apply, ← Finset.sum_add_distrib, Pi.smul_apply, Pi.sub_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  apply Complex.ext <;> simp <;> ring

theorem comm_realMap_per {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (a : O) :
    ρ a * A = A * ρ a ∧ ρ a * B = B * (ρ a).map star := by
  refine realMap_inj (ext_per hP₀ fun x => ?_)
  have := h (a • x)
  rw [hP.1, hP₀.1, h] at this
  simp only [realMap_apply, mulVec_add, mulVec_mulVec, star_mulVec_map] at this ⊢
  exact this

theorem comm_herm_per {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) {M : Matrix (Fin g) (Fin g) ℂ}
    (hM : ∀ x y, (hermForm M (P₀ x) (P₀ y)).im = D.EF x y) (a : O) :
    (ρ a)ᵀ * M = M * (ρ (bar a)).map star := by
  have key : (imForm M).compl₁₂ (realMap (ρ a) 0) LinearMap.id =
      (imForm M).compl₁₂ LinearMap.id (realMap (ρ (bar a)) 0) := by
    refine ext_per hP₀ fun x => ext_per hP₀ fun y => ?_
    simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
      ← hP₀.1, imForm_apply, hM, D.adj]
  refine sesq_ext fun z w => ?_
  have := LinearMap.congr_fun₂ key z w
  simp only [LinearMap.compl₁₂_apply, realMap_apply, zero_mulVec, add_zero, LinearMap.id_apply,
    imForm_apply] at this
  rw [← herm_mulVec_left, ← herm_mulVec_right]
  exact this

theorem map_star_transpose (M : Matrix (Fin g) (Fin g) ℂ) : (M.map star)ᵀ = Mᴴ := rfl

theorem mem_Tsp_of_period {P₀ P : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) (hP : IsPeriod D ρ P)
    {M₀ : Matrix (Fin g) (Fin g) ℂ} (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y)
    {A B : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, P x = realMap A B (P₀ x)) (hA : A.det ≠ 0) :
    (A⁻¹ * B)ᵀ * M₀ ∈ Tsp bar ρ := by
  have hu : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  refine ⟨?_, fun a => ?_⟩
  · obtain ⟨M, hM, -, hE⟩ := hP.2.2.2.2
    have key : (imForm M).compl₁₂ (realMap A B) (realMap A B) = imForm M₀ := by
      refine ext_per hP₀ fun x => ext_per hP₀ fun y => ?_
      simp only [LinearMap.compl₁₂_apply, ← h, imForm_apply, hE, hM₀]
    ext i j
    rw [transpose_apply]
    refine riemann_symm (M := Aᵀ * M * A.map star) ?_ (fun z w => ?_) j i
    · have := isHermitian_conjTranspose_mul_mul (A.map star) hM
      convert this using 3
      ext i j; simp
    · rw [GlobalTheory.PeriodConn.hermForm_conj_mul]
      simp only [mulVec_add, mulVec_mulVec, mul_nonsing_inv_cancel_left _ _ hu]
      exact LinearMap.congr_fun₂ key z w
  · obtain ⟨h1, h2⟩ := comm_realMap_per hP₀ hP h a
    have h3 : ρ a * (A⁻¹ * B) = A⁻¹ * B * (ρ a).map star := by
      rw [Matrix.mul_assoc, ← h2]
      have : A⁻¹ * (ρ a * A) * A⁻¹ = A⁻¹ * (A * ρ a) * A⁻¹ := by rw [h1]
      rw [nonsing_inv_mul_cancel_left _ _ hu, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hu] at this
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, this]
    rw [Matrix.mul_assoc, ← comm_herm_per hP₀ hM₀ a, ← Matrix.mul_assoc, ← transpose_mul, h3, transpose_mul,
      map_star_transpose, Matrix.mul_assoc]

theorem comm_of_mem_Tsp {P₀ : D.La →+ (Fin g → ℂ)} (hP₀ : IsPeriod D ρ P₀) {M₀ : Matrix (Fin g) (Fin g) ℂ}
    (hM₀ : ∀ x y, (hermForm M₀ (P₀ x) (P₀ y)).im = D.EF x y) (hdet : M₀.det ≠ 0) {C : Matrix (Fin g) (Fin g) ℂ}
    (hC : Cᵀ * M₀ ∈ Tsp bar ρ) (a : O) : ρ a * C = C * (ρ a).map star := by
  have hu : IsUnit M₀.det := isUnit_iff_ne_zero.mpr hdet
  have h := hC.2 a
  rw [Matrix.mul_assoc, ← comm_herm_per hP₀ hM₀ a, ← Matrix.mul_assoc, ← transpose_mul, ← map_star_transpose,
    ← Matrix.mul_assoc, ← transpose_mul] at h
  have := congrArg (· * M₀⁻¹) h
  simp only [mul_nonsing_inv_cancel_right _ _ hu] at this
  exact transpose_injective this

theorem realMap_one_injective {C : Matrix (Fin g) (Fin g) ℂ} (h : (1 - C * C.map star).det ≠ 0) :
    Function.Injective (realMap 1 C) := by
  refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
  rw [realMap_apply, one_mulVec] at hz
  have h1 : z = -(C *ᵥ star z) := eq_neg_of_add_eq_zero_left hz
  have h2 : star z = -(C.map star *ᵥ z) := by
    have := congrArg star hz
    rw [star_add, star_mulVec_map, star_star, star_zero] at this
    exact eq_neg_of_add_eq_zero_left this
  refine eq_zero_of_mulVec_eq_zero h ?_
  rw [sub_mulVec, one_mulVec, ← mulVec_mulVec, ← neg_neg (C.map star *ᵥ z), ← h2, mulVec_neg, ← h1, sub_self]

end

end GlobalTheory.PerCoordU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnitaryGroupEveryResidueOfLieStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitLemma_unitary_group_every_residue_of_lie : UnitLemmaLie → ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → InvAlg.Identity B₁ B₂ := by
  first | exact @GlobalTheory.UnitLemma.OrbitAll.identity_of_lie | exact GlobalTheory.UnitLemma.OrbitAll.identity_of_lie | (intros; apply GlobalTheory.UnitLemma.OrbitAll.identity_of_lie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialOfLocalStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelicCharacter_trivial_of_local : ∀ (D : D7) (V : HSp D) (ν : GA D V →* Circle), Continuous ν → (∀ g ∈ GinfC V, ν g = 1) → (∀ e, IsSplitIdem D e → ∀ g, SuppAt e V g → ν g = 1) → (∀ v ε, NonSplitAt D v ε → ∀ g, SuppPl ε V g → ν g = 1) → ∀ g, ν g = 1 := by
  first | exact @GlobalTheory.LocalGlobalChar.eq_one_of_local | exact GlobalTheory.LocalGlobalChar.eq_one_of_local | (intros; apply GlobalTheory.LocalGlobalChar.eq_one_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsLocalizationStrictHenselianEqConstMulUnitStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.units_localization_strictHenselian_eq_const_mul_unit : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [Algebra T O] [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)], (∀ f : Polynomial T, f.Monic → 0 < f.natDegree → ∃ x : T, f.eval x = 0) → (∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι) (Si : ι → Subalgebra (Polynomial T) O), Monotone Si ∧ (∀ s : O, ∃ i, s ∈ Si i) ∧ ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra (Polynomial T) A) (_ : Algebra.Etale (Polynomial T) A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[(Polynomial T)] Si i)) → ∀ u : (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T)))ˣ, ∃ (c d : T) (w : Oˣ), c ≠ 0 ∧ d ≠ 0 ∧ (u : Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O d) = algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (algebraMap T O c) * algebraMap O (Localization (Algebra.algebraMapSubmonoid O (nonZeroDivisors T))) (w : O) := by
  first | (exact @GlobalTheory.VertUnits.units_eq_const_mul_unit) | (exact GlobalTheory.VertUnits.units_eq_const_mul_unit) | (intros; apply GlobalTheory.VertUnits.units_eq_const_mul_unit <;> assumption)
end

