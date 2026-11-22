import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsPrimeIdemOfComp
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinPartOneMulInvMemHeckeSplitCongruence
import Formalism.HarderNarasimhan.StatementPl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1297
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1031

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvdPowOfZeros
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

namespace GlobalTheory.HSChoice.HyperplaneFactor

theorem eval_lin {K : Type} [Field K] {N : ℕ} (x : Fin 1 × Fin N → K) (y : Fin N → K) :
    eval x (lin y) = ∑ j, x (0, j) * y j := by
  simp [lin]

theorem coeff_lin {K : Type} [Field K] {N : ℕ} (y : Fin N → K) (j : Fin N) :
    coeff (Finsupp.single ((0 : Fin 1), j) 1) (lin y) = y j := by
  classical
  rw [lin, coeff_sum]
  simp only [mul_comm (X _) (C _), coeff_C_mul, coeff_X', Finsupp.single_left_inj (one_ne_zero' ℕ)]
  simp

theorem isHomogeneous_lin {K : Type} [Field K] {N : ℕ} (y : Fin N → K) : (lin y).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun _ _ => (isHomogeneous_X K _).mul (isHomogeneous_C _ _)

theorem irreducible_lin {K : Type} [Field K] {N : ℕ} {y : Fin N → K} (hy : y ≠ 0) : Irreducible (lin y) := by
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hy
  have h0 : lin y ≠ 0 := fun h => hj (by
    have := coeff_lin y j
    rw [h, coeff_zero] at this
    exact this.symm)
  refine irreducible_of_totalDegree_eq_one ((isHomogeneous_lin y).totalDegree h0) fun x hx => ?_
  have hd := hx (Finsupp.single (0, j) 1)
  rw [coeff_lin] at hd
  exact isUnit_of_dvd_unit hd (IsUnit.mk0 _ hj)

theorem exists_dvd_pow_of_zeros {K : Type} [Field K] [IsAlgClosed K] {N : ℕ} {a b : MvPolynomial (Fin 1 × Fin N) K}
    (h : ∀ x, eval x a = 0 → eval x b = 0) : ∃ n : ℕ, a ∣ b ^ n := by
  have hb : b ∈ (Ideal.span {a}).radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K)]
    intro x hx
    have h1 := hx a (Ideal.subset_span rfl)
    have e : ∀ p : MvPolynomial (Fin 1 × Fin N) K, aeval x p = eval x p := fun p =>
      DFunLike.congr_fun (coe_aeval_eq_eval x) p
    rw [e] at h1
    change aeval x b = 0
    rw [e]
    exact h x h1
  obtain ⟨n, hn⟩ := hb
  exact ⟨n, Ideal.mem_span_singleton.1 hn⟩

theorem eq_C_mul_prod_lin : ∀ (K : Type) [Field K] [IsAlgClosed K] (N δ m : ℕ) (g : MvPolynomial (Fin 1 × Fin N) K)
    (y : Fin m → Fin N → K), g.IsHomogeneous δ → NoSquare g → (∀ q, y q ≠ 0) →
    (∀ q q' (c : K), y q' = c • y q → q = q') →
    (∀ ξ : Fin N → K, eval (fun p => ξ p.2) g = 0 ↔ ∃ q, ∑ j, ξ j * y q j = 0) →
    m = δ ∧ ∃ c : K, c ≠ 0 ∧ g = C c * ∏ q, lin (y q) := by
  intro K _ _ N δ m g y hg hns hy hinj hz
  classical
  have hz' : ∀ x : Fin 1 × Fin N → K, eval x g = 0 ↔ ∃ q, eval x (lin (y q)) = 0 := by
    intro x
    have e : (fun p : Fin 1 × Fin N => x (0, p.2)) = x := by
      funext ⟨i, j⟩
      rw [Subsingleton.elim i 0]
    have h1 := hz fun j => x (0, j)
    simp only [e] at h1
    simpa only [eval_lin] using h1
  have irr : ∀ q, Irreducible (lin (y q)) := fun q => irreducible_lin (hy q)
  have dvdg : ∀ q, lin (y q) ∣ g := fun q => by
    obtain ⟨n, hn⟩ := exists_dvd_pow_of_zeros (a := lin (y q)) (b := g) fun x hx => (hz' x).2 ⟨q, hx⟩
    exact (irr q).prime.dvd_of_dvd_pow hn
  have nondvd : ∀ q q', q ≠ q' → ¬ lin (y q) ∣ lin (y q') := by
    intro q q' hne hd
    obtain ⟨a, ha⟩ := (irr q).associated_of_dvd (irr q') hd
    obtain ⟨t, -, ht⟩ := isUnit_iff_eq_C_of_isReduced.1 a.isUnit
    rw [ht, mul_comm] at ha
    refine hne (hinj q q' t (funext fun j => ?_))
    have h1 := congrArg (coeff (Finsupp.single ((0 : Fin 1), j) 1)) ha
    rw [coeff_C_mul, coeff_lin, coeff_lin] at h1
    simpa using h1.symm
  have Pdvd : (∏ q, lin (y q)) ∣ g := Finset.prod_dvd_of_isRelPrime
    (fun q _ q' _ hne => (irr q).isRelPrime_iff_not_dvd.2 (nondvd q q' hne)) fun q _ => dvdg q
  obtain ⟨h, hh⟩ := Pdvd
  have h0 : h ≠ 0 := fun e => hns.1 (by rw [hh, e, mul_zero])
  have hu : IsUnit h := by
    by_contra hu
    obtain ⟨p, pirr, pd⟩ := WfDvdMonoid.exists_irreducible_factor hu h0
    obtain ⟨n, hn⟩ := exists_dvd_pow_of_zeros (a := g) (b := ∏ q, lin (y q)) fun x hx => by
      obtain ⟨q, hq⟩ := (hz' x).1 hx
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ q) hq
    have pg : p ∣ g := hh ▸ pd.mul_left _
    obtain ⟨q, -, hq⟩ := (Prime.exists_mem_finset_dvd pirr.prime (pirr.prime.dvd_of_dvd_pow (pg.trans hn)))
    have hl : lin (y q) ∣ p := ((pirr.associated_of_dvd (irr q) hq).symm).dvd
    refine hns.2 (y q) (hy q) ?_
    rw [hh, pow_two]
    exact mul_dvd_mul (Finset.dvd_prod_of_mem _ (Finset.mem_univ q)) (hl.trans pd)
  obtain ⟨c, hc, hcC⟩ := isUnit_iff_eq_C_of_isReduced.1 hu
  have hgC : g = C c * ∏ q, lin (y q) := by rw [hh, hcC, mul_comm]
  have hP : (∏ q, lin (y q)).IsHomogeneous m := by
    simpa using IsHomogeneous.prod Finset.univ (fun q => lin (y q)) (fun _ => 1) fun q _ => isHomogeneous_lin (y q)
  have hgm : g.IsHomogeneous m := by
    rw [hgC]
    simpa using (isHomogeneous_C (Fin 1 × Fin N) c).mul hP
  exact ⟨(hgm.totalDegree hns.1).symm.trans (hg.totalDegree hns.1), c, hc.ne_zero, hgC⟩

end GlobalTheory.HSChoice.HyperplaneFactor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartEqOneMulInvMemSplitCongruenceIdeles
section
noncomputable section

namespace GlobalTheory.HeckeSplitGen.FinF

section Ports

open NumberField IsDedekindDomain HeckeCharacterZeroLocus.ThmBIn GlobalTheory.CMPrimeIdele
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {Φ : AE F E →+* FiniteAdeleRing (𝓞 E) E}

theorem ev_sub (a b : AE F E) (Q : HeightOneSpectrum (𝓞 E)) : Φ (a - b) Q = Φ a Q - Φ b Q := by
  rw [map_sub]; rfl

theorem ev_one (Q : HeightOneSpectrum (𝓞 E)) : Φ 1 Q = 1 := by rw [map_one]; rfl

theorem ev_inc (hΦ : Comp Φ) (y : E) (Q : HeightOneSpectrum (𝓞 E)) :
    Φ (incA F E y) Q = algebraMap E (Q.adicCompletion E) y := by rw [hΦ.2.2.1]; rfl

theorem isSplitIdem_of_delta (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {P : HeightOneSpectrum (𝓞 E)}
    (hc : cP hσ P ≠ P) {e : AE F E} (he : IsDelta Φ P e) : IsSplitIdem σ e := by
  obtain ⟨ε, hε⟩ := exists_placeIdem (F := F) (P.under (𝓞 F))
  obtain ⟨h0, h1, h2⟩ := place_comp (E := E) hΦ hε
  have he' := delta_conj hΦ hσ he
  refine ⟨delta_idem hΦ he, ?_, _, ε, hε, ?_⟩
  · refine hΦ.ext' (by rw [RingHom.map_mul, he.1, zero_mul, RingHom.map_zero]) fun Q => ?_
    rw [ev_mul, ev_zero]
    by_cases hQ : Q = P
    · subst hQ
      rw [he'.2.2 Q (Ne.symm hc), mul_zero]
    · rw [he.2.2 Q hQ, zero_mul]
  · refine hΦ.ext' (by rw [RingHom.map_add, he.1, he'.1, add_zero, h0]) fun Q => ?_
    rw [ev_add]
    by_cases hQ : Q = P
    · subst hQ
      rw [he.2.1, he'.2.2 Q (Ne.symm hc), add_zero, h1 Q rfl]
    · by_cases hQ' : Q = cP hσ P
      · subst hQ'
        rw [he.2.2 _ hQ, he'.2.1, zero_add, h1 _ (under_cP hσ P)]
      · rw [he.2.2 Q hQ, he'.2.2 Q hQ', add_zero, h2 Q fun h => (eq_or_eq_cP hσ h).elim hQ hQ']

theorem mem_modSet (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N) (x : (AE F E)ˣ) (h0 : infPart F E (x : AE F E) = 1)
    (h : ∀ Q, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) :
    x ∈ modSetF F E N := by
  have hN' : (N : E) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  refine ⟨h0, ⟨finPart F E (((x : AE F E) - 1) * incA F E (N : E)⁻¹), (hΦ.2.2.2.1 _).2 fun Q => ?_, ?_⟩,
    (hΦ.2.2.2.1 _).2 fun Q => ?_⟩
  · rw [HeightOneSpectrum.mem_adicCompletionIntegers, ev_mul, ev_sub, ev_one, ev_inc hΦ, map_inv₀, map_natCast,
      Valuation.map_mul, map_inv₀]
    exact mul_inv_le_one_of_le₀ (h Q).2 zero_le
  · have e : (N : AE F E) * incA F E (N : E)⁻¹ = 1 := by
      rw [← map_natCast (incA F E), ← map_mul, mul_inv_cancel₀ hN', map_one]
    have e2 : (x : AE F E) - 1 = N * (((x : AE F E) - 1) * incA F E (N : E)⁻¹) := by
      linear_combination (1 - (x : AE F E)) * e
    have e3 := congrArg (finPart F E) e2
    rwa [RingHom.map_sub, RingHom.map_one, RingHom.map_mul, map_natCast] at e3
  · have e : Φ x Q * Φ (x⁻¹ : (AE F E)ˣ) Q = 1 := by rw [← ev_mul, Units.mul_inv, ev_one]
    have e2 := congrArg Valued.v e
    rw [Valuation.map_mul, (h Q).1, one_mul, Valuation.map_one] at e2
    exact e2.le

theorem mem_grpH_of_good (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N)
    {B : Set (HeightOneSpectrum (𝓞 E))} (hB : B.Finite) : (∀ P ∈ B, cP hσ P ≠ P) → ∀ x : (AE F E)ˣ,
      infPart F E (x : AE F E) = 1 →
      (∀ Q ∉ B, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) →
      x ∈ grpHF σ N := by
  induction B, hB using Set.Finite.induction_on with
  | empty =>
    exact fun _ x h0 h => Subgroup.subset_closure (Or.inr (mem_modSet hΦ hN x h0 fun Q => h Q (Set.notMem_empty Q)))
  | @insert P B _ _ ih =>
    intro hB x h0 h
    obtain ⟨e, he⟩ := exists_delta hΦ P
    have hs := isSplitIdem_of_delta hσ hΦ (hB P (Set.mem_insert _ _)) he
    have h1 : GlobalTheory.HeckeSplitAll.Fin.part hs.1 x ∈ grpHF σ N := by
      refine Subgroup.subset_closure (Or.inl (Or.inr ⟨e, hs, ?_⟩))
      change (e + cA σ e) * (e * x + (1 - e) - 1) = e * x + (1 - e) - 1
      linear_combination ((x : AE F E) - 1) * hs.1 + ((x : AE F E) - 1) * hs.2.1
    have h2 : x * (GlobalTheory.HeckeSplitAll.Fin.part hs.1 x)⁻¹ ∈ grpHF σ N := by
      refine ih (fun Q hQ => hB Q (Set.mem_insert_of_mem _ hQ)) _ ?_ fun Q hQ => ?_
      · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv, RingHom.map_add, RingHom.map_mul, RingHom.map_sub,
          RingHom.map_one, he.1, h0]
        simp
      · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv, ev_add, ev_mul, ev_sub, ev_one]
        by_cases hQP : Q = P
        · subst hQP
          rw [he.2.1]
          simp
        · rw [he.2.2 Q hQP, zero_add, sub_zero, one_mul]
          exact h Q fun h' => h'.elim hQP hQ
    simpa using mul_mem h2 h1

theorem exists_fin_idem (hΦ : Comp Φ) :
    ∃ f : AE F E, f * f = f ∧ infPart F E f = 0 ∧ finPart F E f = 1 ∧ Φ f = 1 := by
  obtain ⟨e, he, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  have he1 : ∀ z, (e z).1 = infPart F E z := fun z => (he z).1
  have he2 : ∀ z, (e z).2 = finPart F E z := fun z => (he z).2
  obtain ⟨f, hf⟩ := e.surjective (0, 1)
  have hf0 : infPart F E f = 0 := by rw [← he1, hf]
  have hf1 : finPart F E f = 1 := by rw [← he2, hf]
  have key : ∀ g, infPart F E g = 0 → g * f = g := fun g hg => e.injective (Prod.ext
    (by rw [he1, he1, RingHom.map_mul, hg, zero_mul]) (by rw [he2, he2, RingHom.map_mul, hf1, mul_one]))
  refine ⟨f, key f hf0, hf0, hf1, ?_⟩
  obtain ⟨g, hg0, hg1⟩ := hΦ.2.1 1
  have h4 := congrArg Φ (key g hg0)
  rwa [map_mul, hg1, one_mul] at h4

theorem exists_of_good (hσ : IsCMExt F E σ) (hΦ : Comp Φ) {N : ℕ} (hN : 0 < N)
    {B : Set (HeightOneSpectrum (𝓞 E))} (hB : B.Finite) (hB1 : ∀ P ∈ B, cP hσ P ≠ P) (x : (AE F E)ˣ)
    (h : ∀ Q ∉ B, Valued.v (Φ x Q) = 1 ∧ Valued.v (Φ x Q - 1) ≤ Valued.v (N : Q.adicCompletion E)) :
    ∃ z : (AE F E)ˣ, finPart F E (z : AE F E) = 1 ∧ x * z⁻¹ ∈ grpHF σ N := by
  obtain ⟨f, hf, hf0, hf1, hf2⟩ := exists_fin_idem hΦ
  have h3 : GlobalTheory.HeckeSplitAll.Fin.part hf x ∈ grpHF σ N := by
    refine mem_grpH_of_good hσ hΦ hN hB hB1 _ (GlobalTheory.HeckeSplitAll.Fin.map_mix_zero _ hf0 _) fun Q hQ => ?_
    have : Φ (GlobalTheory.HeckeSplitAll.Fin.part hf x : (AE F E)ˣ) = Φ x :=
      (GlobalTheory.HeckeSplitAll.Fin.map_mix_one Φ hf2 _).1
    rw [this]
    exact h Q hQ
  refine ⟨x * (GlobalTheory.HeckeSplitAll.Fin.part hf x)⁻¹, ?_, ?_⟩
  · rw [GlobalTheory.HeckeSplitAll.Fin.mul_part_inv]
    exact (GlobalTheory.HeckeSplitAll.Fin.map_mix_one _ hf1 _).2
  · rwa [mul_inv, inv_inv, mul_inv_cancel_left]

theorem exists_not_fixed (hσ : IsCMExt F E σ) : ∃ δ : 𝓞 E, cO σ δ ≠ δ := by
  by_contra h
  push_neg at h
  have hs : Function.Surjective (algebraMap F E) := fun x => by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (𝓞 E) x
    have ha : σ (a : E) = a := congrArg (fun t : 𝓞 E => (t : E)) (h a)
    have hb : σ (b : E) = b := congrArg (fun t : 𝓞 E => (t : E)) (h b)
    exact exists_of_conj_eq hσ (by rw [map_div₀, ha, hb])
  have h1 : Module.finrank F E = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 ⟨(algebraMap F E).injective, hs⟩
  have h2 := hσ.2.2.1
  omega

theorem exists_finite_part_one_idele_split_congruence_quotient (hσ : IsCMExt F E σ) {N : ℕ} (hN : 0 < N) (x : (AE F E)ˣ) :
    ∃ z : (AE F E)ˣ, finPart F E (z : AE F E) = 1 ∧ x * z⁻¹ ∈ grpHF σ N := by
  obtain ⟨Φ, hΦ⟩ := exists_comp F E
  obtain ⟨δ, hδ⟩ := exists_not_fixed hσ
  obtain ⟨m, hm, hm'⟩ := GlobalTheory.HeckeSplitAll.Fin.exists_den (Φ x)
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hj : ∀ y : E, y ≠ 0 → ∃ u ∈ grpHF σ N, (u : AE F E) = incA F E y := fun y hy =>
    ⟨_, Subgroup.subset_closure (Or.inl (Or.inl ⟨Units.mk0 y hy, rfl⟩)), rfl⟩
  obtain ⟨a, ha, ha'⟩ := hj _ hm0
  have hx₁ : ∀ Q, Valued.v (Φ (a * x : (AE F E)ˣ) Q) ≤ 1 := fun Q => by
    rw [Units.val_mul, ha', ev_mul, ev_inc hΦ, map_natCast]
    exact hm' Q
  obtain ⟨y, hy, B, hB, hB1, hB2⟩ := GlobalTheory.HeckeSplitAll.Fin.approx_int
    ({ cO σ with invFun := cO σ, left_inv := fun t => cO_cO hσ t, right_inv := fun t => cO_cO hσ t } : 𝓞 E ≃+* 𝓞 E)
    (fun t => cO_cO hσ t) δ hδ N hN (Φ (a * x : (AE F E)ˣ))
    (Φ ((a * x)⁻¹ : (AE F E)ˣ)) (by rw [← map_mul, Units.mul_inv, map_one]) hx₁
  obtain ⟨b, hb, hb'⟩ := hj _ (inv_ne_zero hy)
  obtain ⟨z, hz, hz'⟩ := exists_of_good hσ hΦ hN hB
    (fun P hP h => hB1 P hP fun t ht => (mem_cP hσ P t).1 (h.symm ▸ ht)) (a * x * b) fun Q hQ => by
      rw [Units.val_mul, hb', ev_mul, ev_inc hΦ, map_inv₀]
      exact hB2 Q hQ
  exact ⟨z, hz, GlobalTheory.HeckeSplitAll.Fin.mem_of_mul_mem ha hb hz'⟩

end Ports

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF
open scoped TensorProduct

theorem exists_finPart_eq_one_mul_inv_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ), 0 < N → ∀ x : (AF F ⊗[F] E)ˣ, ∃ z : (AF F ⊗[F] E)ˣ, finPartF F E (z : AF F ⊗[F] E) = 1 ∧ x * z⁻¹ ∈ GlobalTheory.HeckeSplitGen.grpHF σ N := by
  intro F E _ _ _ _ _ σ hσ N hN x
  exact exists_finite_part_one_idele_split_congruence_quotient hσ hN x

end GlobalTheory.HeckeSplitGen.FinF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalCombinationOfLocalRegularIdeal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory

namespace GlobalTheory.HSCore.RegSeqKer

open GlobalTheory.Twist

variable {Y : Scheme.{0}} {L : LB Y} (hL : L.IsLB) (F : Y.Modules) (s : L.Sec)

theorem map_cutHom {l m : ℤ} (h : l + 1 = m) (h' : -1 + m = l) :
    Twist.map (lbZPow L m) (GlobalTheory.cutHom F hL s) =
      (twistZAddIso F hL h').hom ≫ mulSecOfEq F (zofSec s) h :=
  zhom_ext fun V u i => by
    change _ = zcoord ((mulSecOfEq F (zofSec s) h).app V ((twistZAddIso F hL h').hom.app V u)) i
    rw [zcoord_map_app, cutHom_app F hL s i inf_le_right, zcoord_mulSecOfEq_app, zcoord_twistZAddIso_hom_app,
      zchartEquiv_apply, zfun_zofSec]

theorem mul_comp_π {l m : ℤ} (h : l + 1 = m) :
    mulSecOfEq F (zofSec s) h ≫ Twist.map (lbZPow L m) (GlobalTheory.cutπ F hL s) = 0 := by
  have h' : -1 + m = l := by omega
  rw [← cancel_epi (twistZAddIso F hL h').hom, ← Category.assoc, ← map_cutHom hL F s h h', Limits.comp_zero]
  exact ((cutComplex F hL s).map (twistFunctor (lbZPow L m))).zero

def twistComplex {l m : ℤ} (h : l + 1 = m) : ShortComplex Y.Modules :=
  .mk (mulSecOfEq F (zofSec s) h) (Twist.map (lbZPow L m) (GlobalTheory.cutπ F hL s)) (mul_comp_π hL F s h)

theorem shortExact_twistComplex [Mono (GlobalTheory.cutHom F hL s)] {l m : ℤ} (h : l + 1 = m) :
    (twistComplex hL F s h).ShortExact := by
  have h' : -1 + m = l := by omega
  refine ShortComplex.shortExact_of_iso ?_
    (Twist.shortExact_map (isLB_lbZPow hL m) (shortExact_cutComplex F hL s))
  refine ShortComplex.isoMk (twistZAddIso F hL h') (Iso.refl _) (Iso.refl _) ?_ ?_
  · exact (map_cutHom hL F s h h').symm.trans (Category.comp_id _).symm
  · exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem vanishFrom_cut [Mono (GlobalTheory.cutHom F hL s)] {j₀ : ℤ} (hv : VanishFrom L F j₀) :
    VanishFrom L (GlobalTheory.cut F hL s) (j₀ + 1) := fun j hj q hq =>
  cohOn.subsingleton₃ (shortExact_twistComplex hL F s (l := j - 1) (m := j) (by omega)) ⊤ q
    (hv j (by omega) q hq) (hv (j - 1) (by omega) (q + 1) (by omega))

theorem exists_global (n : ℕ) : ∀ (t : Fin n → L.Sec) (F : Y.Modules) (j₀ l : ℤ), RegSeq hL F (List.ofFn t) →
    VanishFrom L F j₀ → j₀ + n ≤ l + 1 → ∀ f : Γ(GlobalTheory.twistZ F L (l + 1), ⊤),
    (∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin n → Γ(GlobalTheory.twistZ F L l, W)),
      (GlobalTheory.twistZ F L (l + 1)).presheaf.map (homOfLE le_top).op f =
        ∑ i, (mulSecOfEq F (zofSec (t i)) rfl).app W (m i)) →
    ∃ m : Fin n → Γ(GlobalTheory.twistZ F L l, ⊤), f = ∑ i, (mulSecOfEq F (zofSec (t i)) rfl).app ⊤ (m i) := by
  induction n with
  | zero =>
    intro t F j₀ l _ _ _ f hf
    refine ⟨fun i => i.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    refine section_eq_zero_of_germ _ fun x hx => ?_
    obtain ⟨W, hW, m, hm⟩ := hf x
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hm
    rw [← TopCat.Presheaf.germ_res_apply _ (homOfLE (le_top : W ≤ ⊤)) x hW, hm, map_zero]
  | succ n ih =>
    intro t F j₀ l hr hv hj f hf
    rw [List.ofFn_succ, regSeq_cons] at hr
    obtain ⟨hm0, hr⟩ := hr
    have nat : ∀ (a : L.Sec) (W : Y.Opens) (u : Γ(GlobalTheory.twistZ F L l, W)),
        (Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app W ((mulSecOfEq F (zofSec a) rfl).app W u) =
          (mulSecOfEq (cut F hL (t 0)) (zofSec a) rfl).app W
            ((Twist.map (lbZPow L l) (cutπ F hL (t 0))).app W u) := fun a W u => by
      rw [app_app, app_app, mulSecOfEq_naturality]
    have hS := shortExact_twistComplex hL F (t 0) (l := l) rfl
    have := hS.mono_f
    have hex : ∀ W : Y.Opens, Function.Exact ((mulSecOfEq F (zofSec (t 0)) (rfl : l + 1 = l + 1)).app W)
        ((Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app W) := exact_app_of_exact_of_mono hS.exact
    obtain ⟨m', hm'⟩ := ih (fun i => t i.succ) (cut F hL (t 0)) (j₀ + 1) l hr (vanishFrom_cut hL F (t 0) hv)
      (by push_cast at hj; omega) ((Twist.map (lbZPow L (l + 1)) (cutπ F hL (t 0))).app ⊤ f) fun y => by
        obtain ⟨W, hW, m, hm⟩ := hf y
        refine ⟨W, hW, fun i => (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app W (m i.succ), ?_⟩
        rw [← app_res, hm, Fin.sum_univ_succ, map_add, (hex W).apply_apply_eq_zero, zero_add, map_sum]
        exact Finset.sum_congr rfl fun i _ => nat _ _ _
    have hlift : ∀ i, ∃ u : Γ(GlobalTheory.twistZ F L l, ⊤),
        (Twist.map (lbZPow L l) (cutπ F hL (t 0))).app ⊤ u = m' i := fun i => by
      have hi := i.pos
      exact cohOn.app_surjective (shortExact_twistComplex hL F (t 0) (l := l - 1) (m := l) (by omega)) ⊤
        (hv (l - 1) (by push_cast at hj; omega) 1 one_pos) (m' i)
    choose u hu using hlift
    obtain ⟨v, hv'⟩ := (hex ⊤ (f - ∑ i, (mulSecOfEq F (zofSec (t i.succ)) rfl).app ⊤ (u i))).1 (by
      rw [map_sub, hm', map_sum, sub_eq_zero]
      exact Finset.sum_congr rfl fun i _ => by rw [nat, hu])
    refine ⟨Fin.cons v u, ?_⟩
    rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hv', sub_add_cancel]

end GlobalTheory.HSCore.RegSeqKer

theorem GlobalTheory.HSCore.exists_global_of_regSeq : ∀ (k : Type) [Field k] (Y : Scheme.{0}) [Algebra k Γ(Y, ⊤)], IsProjOver (GlobalTheory.strHom k Y) → ∀ (L : LB Y) (hL : L.IsLB) (n : ℕ) (t : Fin n → L.Sec) (F : Y.Modules) [IsFiniteQC F] (j₀ l : ℤ), RegSeq hL F (List.ofFn t) → VanishFrom L F j₀ → j₀ + n ≤ l + 1 → ∀ f : Γ(GlobalTheory.twistZ F L (l + 1), ⊤), (∀ y : Y, ∃ (W : Y.Opens) (_ : y ∈ W) (m : Fin n → Γ(GlobalTheory.twistZ F L l, W)), (GlobalTheory.twistZ F L (l + 1)).presheaf.map (homOfLE le_top).op f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app W (m i)) → ∃ m : Fin n → Γ(GlobalTheory.twistZ F L l, ⊤), f = ∑ i, (GlobalTheory.Twist.mulSecOfEq F (GlobalTheory.Twist.zofSec (t i)) rfl).app ⊤ (m i) :=
  fun _ _ _ _ _ _ hL n t F _ j₀ l => RegSeqKer.exists_global hL n t F j₀ l
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroOfTwistedOrbitalPointTermNeZeroStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_of_twistedOrbitalPointTerm_ne_zero : ∀ {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (f : G → ℂ) (y : G), GlobalTheory.EulerAbs.twTerm θ K δ f y ≠ 0 → ∃ k ∈ K, f ((y * k)⁻¹ * δ * θ (y * k)) ≠ 0 := by
  first | exact @GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero | exact GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero | (intros; apply GlobalTheory.EulerAbs.exists_ne_zero_of_twTerm_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCoveringChartsGenericallyFiniteFieldStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_covering_charts_generically_finite_field : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  first | exact @GlobalTheory.CoverDegField.exists_open_covering_charts | exact GlobalTheory.CoverDegField.exists_open_covering_charts | (intros; apply GlobalTheory.CoverDegField.exists_open_covering_charts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPrincipalUnitIdeleNormOneStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_one_of_principal_unitIdele_norm_one : ∀ (E : Type) [Field E] [NumberField E] (t : Eˣ), Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E →
    (∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1) → ∃ n : ℕ, 0 < n ∧ t ^ n = 1 := by
  first | exact @GlobalTheory.UnitTorsion.principal_unit_idele_torsion | exact GlobalTheory.UnitTorsion.principal_unit_idele_torsion | (intros; apply GlobalTheory.UnitTorsion.principal_unit_idele_torsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioMemValuationSubringAtGenericPoint
section
set_option autoImplicit false

noncomputable section

open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.Adelic.LinSys

theorem exists_ratio_mem_of_point {F K : Type} [Field F] [Field K] (S : LinSys F) (hS : S.IsVariety) (r e : ℕ)
    (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec) (hcov : ∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i)))
    (x : Sp K ⟶ S.Y) (V : ValuationSubring K) (hV : ∀ c, S.baseHom x c ∈ V) :
    ∃ i, S.val x (S.comb (u i)) ≠ 0 ∧ S.powVal x th / S.val x (S.comb (u i)) ^ e ∈ V := by
  have hpr : IsProper S.str := GlobalTheory.CommonModel.isProper_of_isProjOver hS.proj
  let φ : F →+* V := (S.baseHom x).codRestrict V hV
  have hsq : x ≫ S.str = specAlgebraMap V K ≫ spMap φ := by
    rw [S.comp_str x, ← Spec.map_comp]
    rfl
  obtain ⟨l, hl, -⟩ := exists_valuativeExtension S.str (spMap φ) x hsq
  have hx : spMap (algebraMap V K) ≫ l = x := hl
  obtain ⟨i, hi⟩ := hcov (l (IsLocalRing.closedPoint V))
  have hyc := S.mem_chartAt (l (IsLocalRing.closedPoint V))
  set c := S.chartAt (l (IsLocalRing.closedPoint V))
  have hU : ⊤ ≤ l ⁻¹ᵁ S.L.U c := (GlobalTheory.ZH.CrdCalc.top_le_iff l _).2 hyc
  have hB : ⊤ ≤ l ⁻¹ᵁ S.Y.basicOpen ((S.comb (u i)).f c) :=
    (GlobalTheory.ZH.CrdCalc.top_le_iff l _).2 ((mem_nonzeroLocus_iff_basicOpen _ hyc).1 hi)
  obtain ⟨w, hw⟩ := (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff l _ hU _).2 hB
  obtain ⟨hU', hval⟩ := GlobalTheory.ZH.CrdCalc.valR_spMap (algebraMap V K) l _ hU
  rw [hx] at hU' hval
  obtain ⟨c₀, hc₀, h₁, h₂⟩ := S.exists_frame_change x c ((le_iff_ptOf_mem x _).1 hU')
  have ha := (h₁ (S.comb (u i))).symm.trans (hval _)
  have ht := (h₂ e th).symm.trans (hval _)
  rw [← hw] at ha
  have hw₀ : algebraMap V K (w : V) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 w.ne_zero
  have hv : S.val x (S.comb (u i)) ≠ 0 := fun h => hw₀ (by rw [← ha, h, mul_zero])
  refine ⟨i, hv, ?_⟩
  have key : S.powVal x th / S.val x (S.comb (u i)) ^ e =
      algebraMap V K (valR l _ (Twist.zfun th c) * ((w⁻¹ : Vˣ) : V) ^ e) := by
    have hinv : algebraMap V K ((w⁻¹ : Vˣ) : V) = (algebraMap V K (w : V))⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])
    rw [map_mul, map_pow, ← ht, hinv, ← ha, zpow_natCast]
    rw [inv_pow, mul_pow]
    field_simp
  rw [key]
  exact (valR l _ (Twist.zfun th c) * ((w⁻¹ : Vˣ) : V) ^ e).2

theorem exists_ratio_mem_valuationSubring : ∀ (F : Type) [Field F] (S : LinSys F), S.IsVariety → ∀ (r e : ℕ) (u : Fin r → Fin S.N → F) (th : (lbPow S.L e).Sec), (∀ y : S.Y, ∃ i, y ∈ nonzeroLocus (S.comb (u i))) → ∀ η : S.Y, IsGenericPoint η Set.univ → ∀ V : ValuationSubring (S.Y.residueField η), (∀ c, S.baseHom (resPt η) c ∈ V) → ∃ i, S.val (resPt η) (S.comb (u i)) ≠ 0 ∧ S.powVal (resPt η) th / S.val (resPt η) (S.comb (u i)) ^ e ∈ V :=
  fun _ _ S hS r e u th hcov η _ V hV => exists_ratio_mem_of_point S hS r e u th hcov (resPt η) V hV

end GlobalTheory.Adelic.LinSys
end
end

