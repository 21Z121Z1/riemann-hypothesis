import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0822
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0839
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0837
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertClassFieldLatticeTransport
section
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport
open GlobalTheory.ToricTransport (coordIn coordIn_div)
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.TransportProof
theorem exists_sq_eq_neg : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (h2 : Module.finrank ℚ K = 2) (hd : discr K = -(d : ℤ)), ∃ δ : K, δ ^ 2 = -(d : K) := GlobalTheory.T.quadraticField_exists_sqrt_neg_discr

theorem nrm_eq_modF : ∀ {K : Type} [Field K] [NumberField K] (t : (Af K)ˣ) (𝔞 : FractionalIdeal (𝓞 K)⁰ K) (h : IsInvIdealOf t 𝔞), nrm 𝔞 = modF t := GlobalTheory.T.fractionalIdealNorm_eq_finiteIdeleModule

theorem modF_rat : ∀ {E : Type} [Field E] [NumberField E] (y : (Af E)ˣ), ∃ q : ℚ, modF y = q := GlobalTheory.T.finiteIdele_module_exists_rat

theorem modF_upIdele : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [Algebra K E] (t : (Af K)ˣ), modF (upIdele K E t) = modF t ^ Module.finrank K E := GlobalTheory.T.modF_finiteIdeleUpToExtension

theorem card_eq_finrank : ∀ {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (h2 : Module.finrank ℚ K = 2), Fintype.card I = Module.finrank K E := GlobalTheory.T.isCMTypeOfEmbeddings_card_eq_finrank

theorem norm_conj_finPart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (s : ℕ) (κ : I → ℕ) (c : Ideal (OF E)) (hc : c ≠ ⊥) (χ : HChar E) (hχ : HasInf χ φ (fun i => (κ i : ℤ) + s)) (hu : ∀ u ∈ hatOUnits c, finPart χ u = 1) (σ : ℂ ≃+* ℂ) (y : (Af E)ˣ), ‖σ (finPart χ y : ℂ)‖ = 1 := GlobalTheory.T.norm_galois_conj_heckeCharacter_finitePart_eq_one

theorem algebraic_coordIn_toric : ∀ (hA : LatAlg) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (Λ₀ : PeriodPair) (Ω₀ : ℂ) (hΛ : IsLatOf ι 1 Λ₀) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) (T : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T), IsAlgebraic ℚ (coordIn E d s κ Ω₀ T) := GlobalTheory.T.toricSum_coordinate_isAlgebraic

theorem conj_coordIn_toric : ∀ (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ) (h2 : Module.finrank ℚ K = 2) (hd : 0 < d) (hδ : δ ^ 2 = -(d : K)) (g : ℂ ≃+* ℂ) (t : (Af K)ˣ) (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) {E : Type} [Field E] [NumberField E] [IsCMField E] [Algebra K E] {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hE : UnramFin E) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = ι) (s : ℕ) (hs : 1 ≤ s) (κ κ' : I → ℕ) (hκ' : IsConjWt φ g κ κ') (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣) (Q : Finset (HeightOneSpectrum (OF E))) (χ χ' : HChar E) (T T' : ℂ) (hV : IsValSum φ s κ 𝔣 Q χ T) (hV' : IsConjSum φ s κ' 𝔣 Q g χ χ' T'), g (coordIn E d s κ Ω₀ T) = coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E t))⁻¹ * T') := GlobalTheory.T.conj_toricPeriodCoordinate_sum_over_classes

theorem equidistributed_of_j : ∀ (hH : GlobalTheory.Published.HilbertClassFieldJ) {K : Type} [Field K] [NumberField K] [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair) (hΛ : IsLatOf φK 1 ΛK) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (h𝔞 : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ Λ : PeriodPair, IsLatOf φK (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) Λ ∧ jLat Λ = σ (jLat ΛK)), Equidistributed φK (jLat ΛK) 𝔞 := GlobalTheory.T.equidistributed_idealClasses_of_hilbertClassFieldJ

theorem isTotallyComplex_of_discr_neg {K : Type} [Field K] [NumberField K] (h2 : Module.finrank ℚ K = 2)
    (h : discr K < 0) : IsTotallyComplex K := by
  have hs := sign_discr K
  rw [Int.sign_eq_neg_one_of_neg h] at hs
  have hr := InfinitePlace.card_add_two_mul_card_eq_rank K
  rw [h2] at hr
  have hc : InfinitePlace.nrComplexPlaces K = 1 := by
    rcases Nat.even_or_odd (InfinitePlace.nrComplexPlaces K) with he | ho
    · rw [he.neg_one_pow] at hs; norm_num at hs
    · obtain ⟨k, hk⟩ := ho; omega
  exact nrRealPlaces_eq_zero_iff.1 (by omega)

theorem disc_j_of_torsTransport {K : Type} [Field K] [NumberField K] {ι : K →+* ℂ} {g : ℂ ≃+* ℂ} {t : (Af K)ˣ}
    {Λ₀ Λ₁ : PeriodPair} {Ω₀ Ω₁ : ℂ} (hT : TorsTransport ι g t Λ₀ Λ₁ Ω₀ Ω₁) (hΩ : Ω₀ ^ 12 = latDisc Λ₀) :
    Ω₁ ^ 12 = latDisc Λ₁ ∧ jLat Λ₁ = g (jLat Λ₀) := by
  obtain ⟨h0, h1, -, -, -, ha, hb, -⟩ := hT
  have e0 : (Λ₀.g₂ / Ω₀ ^ 4) ^ 3 - 27 * (Λ₀.g₃ / Ω₀ ^ 6) ^ 2 = 1 := by
    have : latDisc Λ₀ / Ω₀ ^ 12 = 1 := by rw [← hΩ, div_self (pow_ne_zero _ h0)]
    rw [← this, latDisc]; field_simp
  have e1 : (Λ₁.g₂ / Ω₁ ^ 4) ^ 3 - 27 * (Λ₁.g₃ / Ω₁ ^ 6) ^ 2 = 1 := by
    rw [← ha, ← hb]
    have := congrArg g e0
    simpa [map_sub, map_pow, map_mul, map_ofNat] using this
  have hD : Ω₁ ^ 12 = latDisc Λ₁ := by
    rw [latDisc]; field_simp at e1; linear_combination -e1
  refine ⟨hD, ?_⟩
  have j0 : jLat Λ₀ = 1728 * (Λ₀.g₂ / Ω₀ ^ 4) ^ 3 := by
    rw [jLat, ← hΩ]; field_simp
  have j1 : jLat Λ₁ = 1728 * (Λ₁.g₂ / Ω₁ ^ 4) ^ 3 := by
    rw [jLat, ← hD]; field_simp
  rw [j0, j1, map_mul, map_pow, ha, map_ofNat]

theorem condQ_ne_bot {E : Type} [Field E] [NumberField E] {𝔣 : Ideal (OF E)} (h𝔣 : IsBaseCond 𝔣)
    (Q : Finset (HeightOneSpectrum (OF E))) : condQ 𝔣 Q ≠ ⊥ := by
  unfold condQ
  rw [← Ideal.zero_eq_bot]
  refine mul_ne_zero h𝔣.1 (Finset.prod_ne_zero_iff.2 fun q _ => q.ne_bot)

theorem norm_lamF_conj_up {K E : Type} [Field K] [NumberField K] [Field E] [NumberField E] [IsCMField E]
    [Algebra K E] {I : Type} [Fintype I] (h2 : Module.finrank ℚ K = 2) (φ : I → E →+* ℂ) (hE : UnramFin E)
    (hφ : IsCMType φ) (s : ℕ) (κ κ' : I → ℕ) (𝔣 : Ideal (OF E)) (h𝔣 : IsBaseCond 𝔣)
    (Q : Finset (HeightOneSpectrum (OF E))) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (χ χ' : HChar E) (hχ : IsValChar φ s κ 𝔣 Q χ)
    (σ : ℂ ≃+* ℂ) (hc : IsConjChar φ s κ' σ χ χ') (t : (Af K)ˣ) :
    ‖lamF s χ' (upIdele K E t)‖ = modF t ^ (s * Fintype.card I) := by
  have hu := GlobalTheory.CMVal.OrderUnits.finPart_eq_one E I φ hφ s κ 𝔣 Q χ hE h𝔣 hQ hχ
  have h1 := norm_conj_finPart φ hφ s κ (condQ 𝔣 Q) (condQ_ne_bot h𝔣 Q) χ hχ.2.2.1 hu σ (upIdele K E t)
  obtain ⟨q, hq⟩ := modF_rat (upIdele K E t)
  have hpos := GlobalTheory.CMVal.IdeleModule.modF_pos (upIdele K E t)
  rw [hc.1, lamF, map_mul, norm_mul, h1, one_mul]
  have e : (((modF (upIdele K E t)) ^ s : ℝ) : ℂ) = ((q ^ s : ℚ) : ℂ) := by rw [hq]; push_cast; rfl
  rw [e, map_ratCast, ← e]
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (pow_pos hpos _), modF_upIdele, ← card_eq_finrank φ hφ h2,
    ← pow_mul, mul_comm]

theorem beta_eq_coordIn_pow (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ)
    (Ω T : ℂ) (Λ : PeriodPair) (h : Ω ^ 12 = latDisc Λ) : beta E d s κ Λ T = coordIn E d s κ Ω T ^ 12 := by
  rw [beta_eq, coordIn, div_pow, ← h, ← pow_mul, ← pow_mul, mul_comm 12]

theorem transportFor_of (hA : LatAlg) (hC : LatConj) {K : Type} [Field K] [NumberField K] (d : ℕ) (hd : 0 < d)
    (δ : K) (hδ : δ ^ 2 = -(d : K)) (h2 : Module.finrank ℚ K = 2) (φK : K →+* ℂ) (ΛK : PeriodPair)
    (hΛ : IsLatOf φK 1 ΛK) (Ω₀ : ℂ) (hΩ₀ : Ω₀ ^ 12 = latDisc ΛK) (hΩ₀0 : Ω₀ ≠ 0)
    (t : (ℂ ≃+* ℂ) → (Af K)ˣ) (𝔞 : (ℂ ≃+* ℂ) → (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : (ℂ ≃+* ℂ) → PeriodPair)
    (Ω : (ℂ ≃+* ℂ) → ℂ)
    (hT : ∀ σ, Fixes φK σ →
      TorsTransport φK σ (t σ) ΛK (Λ σ) Ω₀ (Ω σ) ∧ IsInvIdealOf (t σ) (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K))
    (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (hE : UnramFin E)
    (I : Type) [Fintype I] (φ : I → E →+* ℂ) (hφ : IsCMType φ) (hφK : ∀ i, (φ i).comp (algebraMap K E) = φK)
    (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (hs : 1 ≤ s) (h𝔣 : IsBaseCond 𝔣) :
    TransportFor d φK ΛK t 𝔞 Λ φ s κ 𝔣 := by
  have hC0 : (C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (cmValueConst_pos E hd (by omega) κ).ne'
  have conj : ∀ σ, Fixes φK σ → ∀ κ', IsConjWt φ σ κ κ' → ∀ Q χ T χ' T', IsValSum φ s κ 𝔣 Q χ T →
      IsConjSum φ s κ' 𝔣 Q σ χ χ' T' →
      σ (coordIn E d s κ Ω₀ T) = coordIn E d s κ (Ω σ) ((((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^
        (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') := by
    intro σ hσ κ' hκ' Q χ T χ' T' hV hV'
    rw [nrm_eq_modF _ _ (hT σ hσ).2]
    exact conj_coordIn_toric hC d δ φK h2 hd hδ σ (t σ) ΛK (Λ σ) Ω₀ (Ω σ) hΩ₀ (hT σ hσ).1 φ hE hφ hφK s hs
      κ κ' hκ' 𝔣 h𝔣 Q χ χ' T T' hV hV'
  refine ⟨fun Q χ T hV => ⟨?_, fun σ hσ κ' hκ' χ' T' hV' => ?_⟩,
    fun Q₁ Q₂ χ₁ χ₂ T₁ T₂ hV₁ hV₂ hT₂ => ⟨?_, fun σ hσ κ' hκ' χ₁' χ₂' T₁' T₂' hV₁' hV₂' => ?_⟩⟩
  · rw [beta_eq_coordIn_pow E d s κ Ω₀ T ΛK hΩ₀]
    exact (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q χ T hV).pow 12
  · have hD := (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).1
    set N := nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) with hN
    have hN0 : N ≠ 0 := nrm_ne_zero _
    have hNpos : 0 < N := lt_of_le_of_ne (by rw [hN, nrm]; exact_mod_cast FractionalIdeal.absNorm_nonneg _) hN0.symm
    have e : σ (beta E d s κ ΛK T) = beta E d s κ (Λ σ)
        ((((N : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ * (lamF s χ' (upIdele K E (t σ)))⁻¹ * T') := by
      rw [beta_eq_coordIn_pow E d s κ Ω₀ T ΛK hΩ₀, map_pow, conj σ hσ κ' hκ' Q χ T χ' T' hV hV',
        beta_eq_coordIn_pow E d s κ (Ω σ) _ (Λ σ) hD]
    have hl := norm_lamF_conj_up h2 φ hE hφ s κ κ' 𝔣 h𝔣 Q hV.1 χ χ' hV.2.1 σ hV'.1 (t σ)
    rw [← nrm_eq_modF _ _ (hT σ hσ).2, ← hN] at hl
    refine ⟨by rw [e, beta_eq]; ring, ?_⟩
    rw [e, beta_eq, norm_div, norm_pow, norm_mul, norm_mul, norm_mul, norm_inv, norm_inv, hl, norm_pow, norm_pow,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hNpos,
      abs_of_pos (cmValueConst_pos E hd (by omega) κ)]
    have hDn : ‖latDisc (Λ σ)‖ ≠ 0 := norm_ne_zero_iff.2 (latDisc_ne_zero _)
    field_simp
    ring
  · rw [← coordIn_div E hd hs κ hΩ₀0 T₁ T₂, div_eq_mul_inv]
    exact (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q₁ χ₁ T₁ hV₁).mul
      (algebraic_coordIn_toric hA d δ φK h2 hd hδ ΛK Ω₀ hΛ hΩ₀ φ hE hφ hφK s hs κ 𝔣 h𝔣 Q₂ χ₂ T₂ hV₂).inv
  · have hΩσ : Ω σ ≠ 0 := (hT σ hσ).1.2.1
    set m : ℂ := (((nrm (𝔞 σ : FractionalIdeal (𝓞 K)⁰ K) : ℝ) : ℂ) ^ (∑ i, κ i)) with hm
    have hm0 : m ≠ 0 := pow_ne_zero _ (by exact_mod_cast nrm_ne_zero _)
    have c1 := conj σ hσ κ' hκ' Q₁ χ₁ T₁ χ₁' T₁' hV₁ hV₁'
    have c2 := conj σ hσ κ' hκ' Q₂ χ₂ T₂ χ₂' T₂' hV₂ hV₂'
    have hc2 : coordIn E d s κ Ω₀ T₂ ≠ 0 := by
      rw [coordIn]; exact div_ne_zero (mul_ne_zero hC0 hT₂) (pow_ne_zero _ hΩ₀0)
    have hT2' : T₂' ≠ 0 := by
      rintro rfl
      have := (map_ne_zero σ).2 hc2
      rw [c2, mul_zero, coordIn, mul_zero, zero_div] at this
      exact this rfl
    refine ⟨hT2', ?_⟩
    rw [← coordIn_div E hd hs κ hΩ₀0 T₁ T₂, map_div₀, c1, c2, coordIn_div E hd hs κ hΩσ, mul_assoc, mul_assoc,
      mul_div_mul_left _ _ (inv_ne_zero hm0)]

theorem transport_of (hH : GlobalTheory.Published.HilbertClassFieldJ) (hA : LatAlg) (hC : LatConj) : Transport := by
  intro K _ _ d hd h2 hdisc φK ΛK hΛ
  have hTC : IsTotallyComplex K := isTotallyComplex_of_discr_neg h2 (by rw [hdisc]; omega)
  obtain ⟨δ, hδ⟩ := exists_sq_eq_neg K d h2 hdisc
  obtain ⟨Ω₀, hΩ₀⟩ := IsAlgClosed.exists_pow_nat_eq (latDisc ΛK) (by norm_num : 0 < 12)
  have hΩ₀0 : Ω₀ ≠ 0 := by rintro rfl; exact latDisc_ne_zero ΛK (by rw [← hΩ₀]; norm_num)
  have key : ∀ σ : ℂ ≃+* ℂ, Fixes φK σ → ∃ (t : (Af K)ˣ) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (Λ : PeriodPair) (Ω : ℂ),
      TorsTransport φK σ t ΛK Λ Ω₀ Ω ∧ IsInvIdealOf t (𝔞 : FractionalIdeal (𝓞 K)⁰ K) ∧
        IsLatOf φK (𝔞 : FractionalIdeal (𝓞 K)⁰ K) Λ := by
    intro σ hσ
    letI : Algebra K ℂ := φK.toAlgebra
    obtain ⟨X, hX, ξ, hξ, hTr⟩ := GlobalTheory.LatVal.CurveTransport.exists_curve_torsTransport h2 φK ΛK Ω₀ hΛ hΩ₀0
    haveI := hX
    let σK : ℂ ≃ₐ[K] ℂ := AlgEquiv.ofRingEquiv (f := σ) hσ
    obtain ⟨t, ht⟩ := GlobalTheory.EllipticCM.exists_transports h2 σK one_ne_zero hξ
    obtain ⟨Λ₁, Ω₁, h1⟩ := hTr σK t ht
    obtain ⟨𝔞, h𝔞t, h𝔞Λ⟩ := h1.2.2.2.2.1
    have h𝔞0 : 𝔞 ≠ 0 := by
      rintro rfl
      have hm : Λ₁.ω₁ ∈ (Λ₁.lattice : Set ℂ) := PeriodPair.ω₁_mem_lattice Λ₁
      rw [h𝔞Λ] at hm
      obtain ⟨x, hx, hx'⟩ := hm
      have hx0 : x = 0 := by simpa using hx
      rw [hx0, map_zero] at hx'
      exact (by simpa using Λ₁.indep.ne_zero 0 : Λ₁.ω₁ ≠ 0) hx'.symm
    exact ⟨t, Units.mk0 𝔞 h𝔞0, Λ₁, Ω₁, h1, h𝔞t, h𝔞Λ⟩
  haveI : Nonempty PeriodPair := ⟨ΛK⟩
  choose! t 𝔞 Λ Ω hT using key
  refine ⟨t, 𝔞, Λ, fun σ hσ => ⟨(hT σ hσ).2.1, (hT σ hσ).2.2, (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).2⟩,
    equidistributed_of_j hH h2 φK ΛK hΛ 𝔞
      (fun σ hσ => ⟨Λ σ, (hT σ hσ).2.2, (disc_j_of_torsTransport (hT σ hσ).1 hΩ₀).2⟩), ?_⟩
  intro E _ _ _ _ _ hE I _ φ hcard hφ hφK s κ 𝔣 hs hκ h𝔣
  exact transportFor_of hA hC d (by omega) δ hδ h2 φK ΛK hΛ Ω₀ hΩ₀ hΩ₀0 t 𝔞 Λ Ω
    (fun σ hσ => ⟨(hT σ hσ).1, (hT σ hσ).2.1⟩) E hE I φ hφ hφK s κ 𝔣 hs h𝔣

end GlobalTheory.TransportProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HopfOrderPullbackAlongHom
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DenAway

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct

def intAfP (p : ℕ) : Set (AfP p) :=
  {a | ∀ v : AwayP p, AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ}

theorem isOpen_intAfP (p : ℕ) : IsOpen (intAfP p) :=
  RestrictedProduct.isOpen_forall_mem (fun _ => Valued.isOpen_valuationSubring _)

theorem natCast_mem (v : HeightOneSpectrum ℤ) (n : ℕ) :
    (n : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
  _root_.natCast_mem _ n

theorem exists_nat_local (v : HeightOneSpectrum ℤ) (x : v.adicCompletion ℚ) :
    ∃ n : ℕ, 0 < n ∧ (n : v.adicCompletion ℚ) * x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨b, hb, hbx⟩ := adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  refine ⟨b.natAbs, Int.natAbs_pos.2 hb0, ?_⟩
  have e : ((b.natAbs : ℕ) : v.adicCompletion ℚ) = algebraMap ℤ (v.adicCompletion ℚ) (|b|) := by
    rw [← Int.natCast_natAbs, map_natCast]
  rw [e]
  rcases abs_choice b with h | h
  · rw [h, mul_comm]; exact hbx
  · rw [h, map_neg, neg_mul, mul_comm]; exact neg_mem hbx

theorem eval_natCast_mul {p : ℕ} (v : AwayP p) (n : ℕ) (a : AfP p) :
    AfP.eval v ((n : AfP p) * a) = (n : v.1.adicCompletion ℚ) * AfP.eval v a := by
  rw [map_mul, map_natCast]

theorem exists_nat_adele {p : ℕ} (a : AfP p) : ∃ n : ℕ, 0 < n ∧ (n : AfP p) * a ∈ intAfP p := by
  choose m hm0 hm using fun v : AwayP p => exists_nat_local v.1 (AfP.eval v a)
  have hS : {v : AwayP p | ¬ AfP.eval v a ∈ v.1.adicCompletionIntegers ℚ}.Finite :=
    Filter.eventually_cofinite.mp (a : Πʳ v : AwayP p, [v.1.adicCompletion ℚ, v.1.adicCompletionIntegers ℚ]).2
  refine ⟨∏ v ∈ hS.toFinset, m v, Finset.prod_pos (fun v _ => hm0 v), fun w => ?_⟩
  rw [eval_natCast_mul]
  by_cases hw : w ∈ hS.toFinset
  · obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m hw
    rw [hk, Nat.cast_mul, mul_comm ((m w : ℕ) : w.1.adicCompletion ℚ), mul_assoc]
    exact mul_mem (natCast_mem w.1 k) (hm w)
  · have hw' : AfP.eval w a ∈ w.1.adicCompletionIntegers ℚ := by
      by_contra h
      exact hw (hS.mem_toFinset.mpr h)
    exact mul_mem (natCast_mem w.1 _) hw'

theorem exists_pow_of_integral_away (p : ℕ) [Fact p.Prime] (r : ℚ)
    (h : ∀ v : AwayP p, (v.1.valuation ℚ r) ≤ 1) : ∃ (k : ℤ) (e : ℕ), r * (p : ℚ) ^ e = k := by
  have hden : r.den = p ^ r.den.primeFactorsList.length := by
    refine Nat.eq_prime_pow_of_unique_prime_dvd r.den_nz fun {ℓ} hℓ hdvd => ?_
    by_contra hne
    have hℓ' : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.1 hℓ
    let v : HeightOneSpectrum ℤ := ⟨Ideal.span {(ℓ : ℤ)}, (Ideal.span_singleton_prime hℓ'.ne_zero).2 hℓ',
      by simpa using hℓ.ne_zero⟩
    have hv : v.asIdeal ≠ Ideal.span {(p : ℤ)} := by
      intro h'
      have h'' : Associated (ℓ : ℤ) (p : ℤ) := Ideal.span_singleton_eq_span_singleton.1 h'
      exact hne (by simpa using Int.natAbs_eq_iff_associated.2 h'')
    have h1 := Rat.valuation_le_one_iff_den.1 (h ⟨v, hv⟩)
    exact h1 (Ideal.mem_span_singleton.2 (by exact_mod_cast hdvd))
  refine ⟨r.num, r.den.primeFactorsList.length, ?_⟩
  have : ((p : ℚ) ^ r.den.primeFactorsList.length) = (r.den : ℚ) := by
    conv_rhs => rw [hden]
    push_cast; rfl
  rw [this, Rat.mul_den_eq_num]

theorem den_bounded_of_isCompact : ∀ (p : ℕ) [Fact p.Prime] (Ω : Set (AfP p)), IsCompact Ω → ∃ M : ℕ, 0 < M ∧
    ∀ q : ℚ, algebraMap ℚ (AfP p) q ∈ Ω → ∃ (k : ℤ) (e : ℕ), q * ((M : ℚ) * (p : ℚ) ^ e) = k := by
  intro p _ Ω hΩ
  choose m hm0 hm using fun a : AfP p => exists_nat_adele a
  obtain ⟨t, ht⟩ := hΩ.elim_finite_subcover
    (fun a => (fun x => (m a : AfP p) * x) ⁻¹' intAfP p)
    (fun a => (isOpen_intAfP p).preimage (continuous_const_mul _))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hm x⟩)
  refine ⟨∏ a ∈ t, m a, Finset.prod_pos (fun a _ => hm0 a), fun q hq => ?_⟩
  obtain ⟨a, ha, hqa⟩ := Set.mem_iUnion₂.mp (ht hq)
  obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem m ha
  have hqa' : (m a : AfP p) * algebraMap ℚ (AfP p) q ∈ intAfP p := hqa
  have hint : ∀ v : AwayP p, v.1.valuation ℚ (((∏ a ∈ t, m a : ℕ) : ℚ) * q) ≤ 1 := by
    intro v
    have h2 : AfP.eval v (algebraMap ℚ (AfP p) (((∏ a ∈ t, m a : ℕ) : ℚ) * q)) ∈
        v.1.adicCompletionIntegers ℚ := by
      have e : algebraMap ℚ (AfP p) (((∏ a ∈ t, m a : ℕ) : ℚ) * q) =
          (k : AfP p) * ((m a : AfP p) * algebraMap ℚ (AfP p) q) := by
        rw [map_mul, map_natCast, hk, Nat.cast_mul]; ring
      rw [e, eval_natCast_mul]
      exact mul_mem (natCast_mem v.1 k) (hqa' v)
    rw [AlgHom.commutes] at h2
    rw [← valuedAdicCompletion_eq_valuation', ← mem_adicCompletionIntegers]
    exact h2
  obtain ⟨z, e, hz⟩ := exists_pow_of_integral_away p _ hint
  exact ⟨z, e, by rw [← hz]; ring⟩

end GlobalTheory.DenAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyConeIdealEqFieldDegreeStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealQuotientHilbertPoly_coneIdeal_eq_field_degree : ∀ (K : Type) [Field K] (N : ℕ) (y : Fin N → AlgebraicClosure K) (j : Fin N), y j = 1 → GlobalTheory.idealHilbertPoly (coneIdeal K y) = Polynomial.C (Module.finrank K (IntermediateField.adjoin K (Set.range y)) : ℚ) := by
  first | exact @GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | exact GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin | (intros; apply GlobalTheory.CompHt.idealHilbertPoly_coneIdeal_eq_C_finrank_adjoin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdealQuotientHilbertPolyMapBaseChangeStatement
section
open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idealQuotientHilbertPoly_map_baseChange : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (N : ℕ) (P : Ideal (MvPolynomial (Fin N) K)), (∀ g ∈ P, ∀ n : ℕ, homogeneousComponent n g ∈ P) → (∀ g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L), ∀ n : ℕ, homogeneousComponent n g ∈ P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) ∧ GlobalTheory.idealHilbertPoly (P.map (MvPolynomial.map (algebraMap K L) : MvPolynomial (Fin N) K →+* MvPolynomial (Fin N) L)) = GlobalTheory.idealHilbertPoly P := by
  first | exact @GlobalTheory.HilbBaseChange.idealHilbertPoly_map | exact GlobalTheory.HilbBaseChange.idealHilbertPoly_map | (intros; apply GlobalTheory.HilbBaseChange.idealHilbertPoly_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentSumConjSumOrthogonalDvd
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IdemOrth

theorem idemAt_orth {D : D7} {a b : AE D} {i j : Formalism.L2.DIV.Pl D.host.E} {n : ℕ} (ha : Formalism.L2.NTheta.IsIdemAt a i)
    (hb : Formalism.L2.NTheta.IsIdemAt b j) (hi : ((n : ℕ) : 𝓞 D.host.E) ∈ i.asIdeal)
    (hj : ((n : ℕ) : 𝓞 D.host.E) ∉ j.asIdeal) : (a + cA D a) * (b + cA D b) = 0 := by
  obtain ⟨⟨a1, a2, v, ε, hε, a3⟩, a4⟩ := ha
  obtain ⟨⟨b1, b2, v', ε', hε', b3⟩, b4⟩ := hb
  by_cases hv : v = v'
  · exfalso
    rw [← hv] at hε'
    have hab : a + cA D a = b + cA D b := a3.trans (GlobalTheory.PlaceDatum.placeIdem_eq hε hε' ▸ b3.symm)
    have hn : ((n : ℕ) : 𝓞 D.host.E) ≠ 0 := fun h => hj (h ▸ zero_mem _)
    have h1 := not_not.1 (mt (b4 _ hn).2 hj)
    have h2 := GlobalTheory.MovedIdem.finPart_conj_mem h1
    have hs : star ((((n : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹) = (((n : ℕ) : 𝓞 D.host.E) : D.host.E)⁻¹ := by
      rw [star_inv₀]
      congr 1
      exact star_natCast (R := D.host.E) n
    rw [hs] at h2
    have h3 := not_not.1 (mt (a4 1 one_ne_zero).2 ((Ideal.ne_top_iff_one _).1 i.isPrime.ne_top))
    have h4 : incA D (((1 : 𝓞 D.host.E) : D.host.E)⁻¹) = 1 := by
      rw [show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, inv_one, RingHom.map_one]
    rw [h4, mul_one] at h3
    have h5 := GlobalTheory.SplitLatBasis.mul_mem_intAE D h3 (add_mem h1 h2)
    rw [← RingHom.map_add, ← RingHom.map_mul, ← add_mul, ← mul_assoc, ← hab, mul_add, a1, a2, add_zero] at h5
    exact (a4 _ hn).1 hi h5
  · rw [a3, b3, ← RingHom.map_mul, GlobalTheory.PlaceDatum.placeIdem_mul hε hε' hv, RingHom.map_zero]

theorem sum_orth {R ι : Type} [CommRing R] (c : R →+* R) (p q : ι → R) (s t : Finset ι)
    (h : ∀ i ∈ s, ∀ j ∈ t, (p i + c (p i)) * (q j + c (q j)) = 0) :
    (∑ i ∈ s, p i + c (∑ i ∈ s, p i)) * (∑ j ∈ t, q j + c (∑ j ∈ t, q j)) = 0 := by
  rw [map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj => h i hi j hj

theorem idemSum_orth : ∀ (D : D7) (e e' : AE D) (P P' : Finset (Formalism.L2.DIV.Pl D.host.E)) (n : ℕ), IsIdemSum e P → IsIdemSum e' P' → (∀ PP ∈ P, ((n : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ P', ((n : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → (e + cA D e) * (e' + cA D e') = 0 := by
  rintro D e e' P P' n ⟨⟨es, hes, rfl⟩, -⟩ ⟨⟨fs, hfs, rfl⟩, -⟩ hP hP'
  exact sum_orth (R := AE D) (cA D) es fs P P' fun i hi j hj =>
    idemAt_orth (hes i hi) (hfs j hj) (hP i hi) (hP' j hj)

end GlobalTheory.IdemOrth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsExtraExtra
section
namespace GlobalTheory.ClosingLemmaThird

theorem main : (let d1 : {F : Type} → [inst : Field F] → [inst_1 : NumberField F] → {κ : Type} → [Fintype κ] → ((v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) → (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) → ((κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) → Prop := @(fun {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ) (v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ) (Φ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ) ↦ ∃ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (φ : Fin m → (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ), Φ = ∑ k : Fin m, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f k) (φ k) ∧ (∀ (k : Fin m) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), φ k v ∈ GlobalTheory.WeilM.SB (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v)) ∧ (∀ (k : Fin m), ∀ᶠ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) in Filter.cofinite, φ k v = vac v) ∧ ∀ (k : Fin m), φ k v₁ = φ₀); ∀ {F : Type} [inst : Field F] [inst_1 : NumberField F] {κ : Type} [inst_2 : Fintype κ] {vac : (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) → (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) → ℂ} {v₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F} {φ₀ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v₁) → ℂ} {Φ Ψ : (κ → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F) → ℂ}, d1 vac v₁ φ₀ Φ → d1 vac v₁ φ₀ Ψ → d1 vac v₁ φ₀ (Φ + Ψ)) := by
  intro d1 F _ _ κ _ vac v₁ φ₀ Φ Ψ hΦ hΨ
  obtain ⟨m, f, φ, hΦe, h1, h2, h3⟩ := hΦ
  obtain ⟨m', g, ψ, hΨe, g1, g2, g3⟩ := hΨ
  refine ⟨m + m', Fin.append f g, Fin.append φ ψ, ?_, ?_, ?_, ?_⟩
  · rw [hΦe, hΨe, Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
  · intro k v
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h1 i v
    · simpa only [Fin.append_right] using g1 i v
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h2 i
    · simpa only [Fin.append_right] using g2 i
  · intro k
    refine Fin.addCases (fun i => ?_) (fun i => ?_) k
    · simpa only [Fin.append_left] using h3 i
    · simpa only [Fin.append_right] using g3 i

end GlobalTheory.ClosingLemmaThird
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerWordNeZeroReversedWordNeZeroStatement
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_word_ne_zero_reversedWord_ne_zero : ∀ (n : ℕ) (ε : Fin n → Bool) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V), IsUnitary ε E → ∀ (l : List (Fin n × Fin n)) (w x : V), ⟪w, (l.map fun p : Fin n × Fin n => E p.1 p.2).prod x⟫_ℂ ≠ 0 → ⟪x, ((l.reverse.map Prod.swap).map fun p : Fin n × Fin n => E p.1 p.2).prod w⟫_ℂ ≠ 0 := by
  first | exact @GlobalTheory.SignInnerAdjoint.main | exact GlobalTheory.SignInnerAdjoint.main | (intros; apply GlobalTheory.SignInnerAdjoint.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactGLOfCompactInvertibleMatricesStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Matrix MeasureTheory GlobalTheory.WhitBump
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_GL_of_compact_invertibleMatrices : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (T : Set (Lie E n)), IsCompact T → T ⊆ invSet E n → IsCompact {y : GL (Fin n) (Cinf E) | toL (y : Matrix (Fin n) (Fin n) (Cinf E)) ∈ T} := by
  first | exact @GlobalTheory.WhitBump.isCompact_GL_of_invSet | exact GlobalTheory.WhitBump.isCompact_GL_of_invSet | (intros; apply GlobalTheory.WhitBump.isCompact_GL_of_invSet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
section
noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.KFinLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {a a' : ℕ}

def FinMapsAt (B : Base F E) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : FinMaps F a a') (v : Pl F) : Prop :=
  (SB _).map (R.p v) = ⊤ ∧ (SB _).map (R.p' v) = ⊤ ∧ augAt om v ≤ LinearMap.ker (R.p v) ∧
    augAt om' v ≤ LinearMap.ker (R.p' v) ∧
    (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
      R.p v φ = R.p' v φ' → R.p v φ₁ = R.p' v φ₁') ∧
    Nontrivial (R.Pi v) ∧
    (∀ N : Submodule ℂ (R.Pi v), (∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ → R.p v φ ∈ N → R.p v φ₁ ∈ N) → N = ⊥ ∨ N = ⊤) ∧
    (v ∉ X.T → R.p v (G.M.vac v) = R.p' v (G.M'.vac v) ∧ R.p v (G.M.vac v) ≠ 0) ∧
    ∀ hv : v ∈ B.P, v ∈ X.T → IsZetaAt B G X R ⟨v, hv⟩

end GlobalTheory.KFinLoc

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinOpenSubBaseChange
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

open Matrix NumberField in
open scoped TensorProduct Classical in

theorem _root_.GlobalTheory.finite_monic_coeff_bdd_mul_isIntegral (K : Type) [Field K] [NumberField K]
    (d D : ℕ) (B : ℝ) (hD : 0 < D) :
    {P : Polynomial K | P.Monic ∧ P.natDegree ≤ d ∧ ∀ k, IsIntegral ℤ ((D : K) * P.coeff k) ∧
      ∀ φ : K →+* ℂ, ‖φ (P.coeff k)‖ ≤ B}.Finite := by
  have hT : {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}.Finite := by
    have h := NumberField.Embeddings.finite_of_norm_le K ℂ ((D : ℝ) * B)
    refine (h.image fun x => x / (D : K)).subset ?_
    intro c hc
    refine ⟨(D : K) * c, ⟨hc.1, fun φ => ?_⟩, ?_⟩
    · have := mul_le_mul_of_nonneg_left (hc.2 φ) (Nat.cast_nonneg (α := ℝ) D)
      simpa [norm_mul] using this
    · have hD' : (D : K) ≠ 0 := Nat.cast_ne_zero.mpr hD.ne'
      field_simp
  have hF : (Set.pi Set.univ fun _ : Fin (d + 1) =>
      {c : K | IsIntegral ℤ ((D : K) * c) ∧ ∀ φ : K →+* ℂ, ‖φ c‖ ≤ B}).Finite :=
    Set.Finite.pi fun _ => hT
  refine Set.Finite.of_finite_image
    (f := fun P : Polynomial K => fun i : Fin (d + 1) => P.coeff i) (hF.subset ?_) ?_
  · rintro _ ⟨P, hP, rfl⟩ i -
    exact ⟨(hP.2.2 i).1, (hP.2.2 i).2⟩
  · intro P hP Q hQ hPQ
    ext n
    by_cases hn : n ≤ d
    · exact congrFun hPQ ⟨n, Nat.lt_succ_of_le hn⟩
    · push_neg at hn
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.2.1.trans_lt hn),
        Polynomial.coeff_eq_zero_of_natDegree_lt (hQ.2.1.trans_lt hn)]

end GlobalTheory
end

