import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0122
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0123
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomToKernelSqCentralExtensionSlTwoZMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralBasisOfIntegralAlgebraicElements
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsConjLevelOneStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_qConj_level_one_invariant : ∀ (g : ℂ ≃+* ℂ) (w N : ℕ) (F : ℍ → ℂ), 0 < N → (∀ γ : SL(2, ℤ), F ∣[(w : ℤ)] γ = F) → (∃ a, HasQ N F a) → ∃ F' : ℍ → ℂ, (∀ γ : SL(2, ℤ), F' ∣[(w : ℤ)] γ = F') ∧ QConj g N F F' := by
  first | exact @GlobalTheory.FN.exists_conj_level_one | exact GlobalTheory.FN.exists_conj_level_one | (intros; apply GlobalTheory.FN.exists_conj_level_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDecompositionGroupCyclotomicCharacterZpowNStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_decompositionGroup_cyclotomicCharacter_zpow_ne_one : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (v : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω), ((l : ℕ) : 𝓞 F) ∈ v.asIdeal → IsPlaceOver A v → ∀ n : ℤ, n ≠ 0 → ∃ g : G F Ω, g ∈ Dec (F := F) A ∧ cycZ F Ω l g ^ n ≠ 1 := by
  first | exact @GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one | exact GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one | (intros; apply GlobalTheory.CycDec.exists_mem_Dec_cycZ_zpow_ne_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDeltaPowQExpansionIffLaurentSeriesStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_deltaPow_qExpansion_iff_laurentSeries : ∀ (E : Subring ℂ) (M : ℕ) (φ : ℍ → ℂ), 0 < M → ((∃ w : ℕ, QAll (· ∈ E) M fun τ => DD τ ^ w * φ τ) ↔ ∃ (c : ℤ → ℂ) (n₀ : ℤ), (∀ n, c n ∈ E) ∧ (∀ n < n₀, c n = 0) ∧ ∀ τ : ℍ, HasSum (fun n : ℤ => c n * Complex.exp (2 * Real.pi * Complex.I * (n : ℂ) * τ / M)) (φ τ)) := by
  first | exact @GlobalTheory.FN.laurent_iff | exact GlobalTheory.FN.laurent_iff | (intros; apply GlobalTheory.FN.laurent_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEichlerShimuraPotentialOfHomogeneousPolyCoStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eichlerShimuraPotential_of_homogeneousPolyCocycle : ∀ (R : Type) [CommRing R] (w N l : ℕ), 4 ≤ N → ∀ z : SL(2, ℤ) → MvPolynomial (Fin 2) R, IsCoc w (Gam N l) z → ∃ F ∈ Pot R w (Gam N l), ∀ γ ∈ Gam N l, ∀ τ ∈ Hs, slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (F (mob (ofSL γ) τ)) - F τ = z γ := by
  first | exact @GlobalTheory.KZ.H3.exists_pot_of_isCoc | exact GlobalTheory.KZ.H3.exists_pot_of_isCoc | (intros; apply GlobalTheory.KZ.H3.exists_pot_of_isCoc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePadicSpanOfPowPMulMemStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_padic_span_of_pow_p_mul_mem : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (d : ℕ) (E : Fin d → Ω), (∀ t, IsInt p (E t) ∧ IsAlgZp p (E t)) → ∀ v : ℕ, ∃ (m : ℕ) (f : Fin m → Ω), (∀ j, IsInt p (f j) ∧ IsAlgZp p (f j)) ∧ ∀ (l : Fin d → ℤ_[p]) (y : Ω), IsInt p y → (p : Ω) ^ v * y = ∑ t, zp Ω (l t) * E t → ∃ μ : Fin m → ℤ_[p], y = ∑ j, zp Ω (μ j) * f j := by
  first | exact @GlobalTheory.GeoFix.exists_fin_span_of_pow_mul | exact GlobalTheory.GeoFix.exists_fin_span_of_pow_mul | (intros; apply GlobalTheory.GeoFix.exists_fin_span_of_pow_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomToKernelSqCentralExtensionSlTwoZModStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_to_kernel_sq_centralExtension_slTwoZMod : ∀ (l n m : ℕ), l.Prime → 0 < m → Nat.Coprime m (6 * l) → ∀ (E : Type) [Group E] (π : E →* Matrix.SpecialLinearGroup (Fin 2) (ZMod m)), Function.Surjective π → π.ker ≤ Subgroup.center E → (∀ x ∈ π.ker, x ^ (l ^ n) = 1) → ∃ ψ : E →* E, (∀ e, ψ e ∈ π.ker) ∧ ∀ x ∈ π.ker, ψ x = x ^ 2 := by
  first | exact @GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 | exact GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 | (intros; apply GlobalTheory.CentralExt.exists_hom_to_kernel_eq_sq_on_kernel_of_central_ext_sl2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHomogeneousPolyCocycleEqOnCongruence
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem intCast_zmod_of_dvd {K K₁ : ℕ} (h : K₁ ∣ K) {x y : ℤ} (hx : (x : ZMod K) = y) :
    (x : ZMod K₁) = y := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hx ⊢
  exact dvd_trans (Int.natCast_dvd_natCast.mpr h) hx

theorem mem_Gamma_of_dvd {K K₁ : ℕ} (h : K₁ ∣ K) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma K) : δ ∈ CongruenceSubgroup.Gamma K₁ := by
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact_mod_cast intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h1)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h2)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 0) (by exact_mod_cast h3)
  · exact_mod_cast intCast_zmod_of_dvd h (y := 1) (by exact_mod_cast h4)

theorem mem_Gam_of_Gamma {N l K : ℕ} (hN : N ∣ K) (hl : l ∣ K) {δ : SL(2, ℤ)}
    (hδ : δ ∈ CongruenceSubgroup.Gamma K) : δ ∈ Gam N l := by
  have h1 := CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hN hδ)
  have h2 := CongruenceSubgroup.Gamma_mem.1 (mem_Gamma_of_dvd hl hδ)
  show δ ∈ CongruenceSubgroup.Gamma1 N ⊓ CongruenceSubgroup.Gamma0 l
  exact Subgroup.mem_inf.mpr ⟨(CongruenceSubgroup.Gamma1_mem N δ).mpr ⟨h1.1, h1.2.2.2, h1.2.2.1⟩,
    CongruenceSubgroup.Gamma0_mem.mpr h2.2.2.1⟩

theorem entries_eq_one_of_mem_Gamma {K : ℕ} {δ : SL(2, ℤ)} (hδ : δ ∈ CongruenceSubgroup.Gamma K)
    (i j : Fin 2) :
    (((δ : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) = (((1 : Matrix (Fin 2) (Fin 2) ℤ) i j : ℤ) : ZMod K) := by
  obtain ⟨h1, h2, h3, h4⟩ := CongruenceSubgroup.Gamma_mem.1 hδ
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply, h1, h2, h3, h4]

theorem exists_coc_near : ∀ (N l w : ℕ), 0 < N → l.Prime → l ≠ 2 → ¬ l ∣ N → Odd w → ∀ Φ,
    IsFam l w (Gam N l) Φ → ∀ n : ℕ, ∃ z : SL(2, ℤ) → MvPolynomial (Fin 2) (ZMod (l ^ n)),
      IsCoc w (Gam N l) z ∧ Near z (Φ n) := by
  intro N l w hN hl hl2 hlN hw Φ hΦ n
  obtain ⟨hhom, hadd, hinv, -⟩ := hΦ
  obtain ⟨M₁, hM₁, hadd₁⟩ := hadd n
  obtain ⟨M₂, hM₂, hinv₂⟩ :=
    GlobalTheory.T.uniform_congruence_level_gamma1CapGamma0 N l (ZMod (l ^ n)) (Φ n) hN hl.pos ⟨M₁, hM₁, hadd₁⟩ (hinv n)
  obtain ⟨b, M', hlM', hMeq⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (n := M₁ * M₂) (Nat.mul_pos hM₁ hM₂).ne' l hl.one_lt.ne'
  have hM'pos : 0 < M' := by
    rcases Nat.eq_zero_or_pos M' with h | h
    · exact absurd (h ▸ dvd_zero l) hlM'
    · exact h
  obtain ⟨c, hcΓ, hcomm, hcneg⟩ := GlobalTheory.T.exists_scalar_gamma1CapGamma0_mod_level N l (max b n) M' hN hl hl2 hlN hM'pos hlM'
  have hMK : M₁ * M₂ ∣ M' * N * l ^ (max b n) := by
    rw [hMeq]
    exact dvd_trans (mul_dvd_mul (pow_dvd_pow l (le_max_left b n)) (dvd_refl M')) ⟨N, by ring⟩
  have hM₁K : M₁ ∣ M' * N * l ^ (max b n) := dvd_trans (dvd_mul_right _ _) hMK
  have hM₂K : M₂ ∣ M' * N * l ^ (max b n) := dvd_trans (dvd_mul_left _ _) hMK
  have hnA : l ^ n ∣ l ^ (max b n) := pow_dvd_pow l (le_max_right b n)
  have hnK : l ^ n ∣ M' * N * l ^ (max b n) := dvd_trans hnA (dvd_mul_left _ _)
  obtain ⟨L1, L2, L3, -, -, L6, L7⟩ := GlobalTheory.T.twoVarPolySubstMatrix_basic_laws (ZMod (l ^ n))
  have hΔ : ((CongruenceSubgroup.Gamma (M' * N * l ^ (max b n))).subgroupOf (Gam N l)).Normal := by
    haveI := CongruenceSubgroup.Gamma_normal (M' * N * l ^ (max b n))
    exact Subgroup.normal_subgroupOf
  have h2 : IsUnit (2 : ZMod (l ^ n)) := by
    have hc : Nat.Coprime 2 (l ^ n) :=
      Nat.Coprime.pow_right n ((Nat.coprime_primes Nat.prime_two hl).mpr (Ne.symm hl2))
    simpa using (ZMod.isUnit_iff_coprime 2 (l ^ n)).mpr hc
  obtain ⟨z, hzS, hzc, hzΔ⟩ := GlobalTheory.T.exists_cocycle_extension_of_neg_central_element (Gam N l) (ZMod (l ^ n)) (MvPolynomial (Fin 2) (ZMod (l ^ n)))
    (fun g => (slP ((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).toLinearMap)
    (fun g h v => by simp [L1]) (fun v => by simp [L2]) h2
    (MvPolynomial.homogeneousSubmodule (Fin 2) (ZMod (l ^ n)) w)
    (fun g v hv => by
      rw [MvPolynomial.mem_homogeneousSubmodule] at hv ⊢
      exact L3 _ _ _ hv)
    _ hΔ
    (fun δ hδ v => by
      have hδ' : (δ : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma (l ^ n) :=
        mem_Gamma_of_dvd hnK (Subgroup.mem_subgroupOf.mp hδ)
      show slP _ v = v
      rw [L6 _ 1 v (entries_eq_one_of_mem_Gamma hδ'), L2])
    ⟨c, hcΓ⟩
    (fun v hv => by
      show slP _ v = -v
      rw [MvPolynomial.mem_homogeneousSubmodule] at hv
      rw [L6 _ (-1) v ?_, L7 w v hv, hw.neg_one_pow, neg_one_smul]
      intro i j
      have h := hcneg i j
      fin_cases i <;> fin_cases j <;> simp at h ⊢
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := 0) (by exact_mod_cast h)
      · exact_mod_cast intCast_zmod_of_dvd hnA (y := -1) (by exact_mod_cast h))
    (fun g => by
      rw [Subgroup.mem_subgroupOf]
      simpa using hcomm g)
    (fun g => Φ n g)
    (fun δ _ => (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (hhom n _))
    (fun δ hδ δ' hδ' => by
      have := hadd₁ _ (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ)) _
        (mem_Gamma_of_dvd hM₁K (Subgroup.mem_subgroupOf.mp hδ'))
      simpa using this)
    (fun g δ hδ => by
      have := hinv₂ g g.2 δ (mem_Gamma_of_dvd hM₂K (Subgroup.mem_subgroupOf.mp hδ))
      simpa using this)
  classical
  refine ⟨fun γ => if h : γ ∈ Gam N l then z ⟨γ, h⟩ else 0, ⟨?_, ?_⟩, ?_⟩
  · intro γ hγ
    simp only [dif_pos hγ]
    exact (MvPolynomial.mem_homogeneousSubmodule _ _).mp (hzS _)
  · intro γ hγ δ hδ
    simp only [dif_pos hγ, dif_pos hδ, dif_pos (mul_mem hγ hδ)]
    simpa using hzc ⟨γ, hγ⟩ ⟨δ, hδ⟩
  · refine ⟨M' * N * l ^ (max b n) * l,
      Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hM'pos hN) (pow_pos hl.pos _)) hl.pos, fun δ hδ => ?_⟩
    have hδG : δ ∈ Gam N l :=
      mem_Gam_of_Gamma (dvd_mul_of_dvd_left ⟨M' * l ^ (max b n), by ring⟩ _) (dvd_mul_left _ _) hδ
    have hδK : δ ∈ CongruenceSubgroup.Gamma (M' * N * l ^ (max b n)) :=
      mem_Gamma_of_dvd (dvd_mul_right _ _) hδ
    simp only [dif_pos hδG]
    exact hzΔ ⟨δ, hδG⟩ (Subgroup.mem_subgroupOf.mpr hδK)

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegralBasisOfIntegralAlgebraicElementsStatement
section
open scoped MatrixGroups NNReal
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_basis_of_integral_algebraic_elements : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (v : Valuation Ω ℝ≥0), (∀ x : Ω, v x ≤ 1 ↔ IsInt p x) → 0 < v (p : Ω) → v (p : Ω) < 1 → ∀ (d : ℕ) (e : Fin d → Ω), (∀ t, IsInt p (e t) ∧ IsAlgZp p (e t)) → ∃ (E F : ℕ) (π : Ω) (κ : Fin F → Ω) (lam : Fin d → Fin F → Fin E → ℤ_[p]), 1 ≤ E ∧ IsAlgZp p π ∧ v π ^ E = v (p : Ω) ∧ (∀ j, IsInt p (κ j) ∧ IsAlgZp p (κ j)) ∧ (∀ μ : Fin F → ℤ_[p], (∃ j, ¬ (p : ℤ_[p]) ∣ μ j) → v (∑ j, κ j * zp Ω (μ j)) = 1) ∧ ∀ t, e t = ∑ j, ∑ s : Fin E, κ j * π ^ (s : ℕ) * zp Ω (lam t j s) := by
  first | exact @GlobalTheory.K5.OkBasis.okbasis | exact GlobalTheory.K5.OkBasis.okbasis | (intros; apply GlobalTheory.K5.OkBasis.okbasis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsRootOfMemUn
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
open Filter Topology

noncomputable section

namespace GlobalTheory.KZ.H3.UnRoot

lemma isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

lemma isPreconnected_Hs : IsPreconnected Hs :=
  (convex_halfSpace_gt Complex.imLm.isLinear (0:ℝ)).isPreconnected

lemma eventually_of_germ_eq {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) {τ : ℂ} (hτ : τ ∈ Hs) :
    ∀ᶠ z in 𝓝[≠] τ, φ z = ψ z := by
  have h' : ∀ᶠ z in codiscreteWithin Hs, φ z = ψ z := Filter.Germ.coe_eq.mp h
  rw [Filter.eventually_iff, mem_codiscreteWithin] at h'
  have hd := Filter.disjoint_principal_right.mp (h' τ hτ)
  have hH : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [hH, hd] with z hz1 hz2
  by_contra hne
  exact hz2 ⟨hz1, hne⟩

lemma eq_nhds_of_punctured {F G : ℂ → ℂ} {τ : ℂ} (hF : ContinuousAt F τ) (hG : ContinuousAt G τ)
    (h : ∀ᶠ z in 𝓝[≠] τ, F z = G z) : F =ᶠ[𝓝 τ] G := by
  have hτ : F τ = G τ :=
    tendsto_nhds_unique (hF.tendsto.mono_left nhdsWithin_le_nhds)
      ((hG.tendsto.mono_left nhdsWithin_le_nhds).congr' (h.mono fun z hz => hz.symm))
  have h2 := eventually_nhdsWithin_iff.mp h
  filter_upwards [h2] with z hz
  by_cases hz' : z = τ
  · subst hz'; exact hτ
  · exact hz hz'

lemma order_ne_top {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (h0 : (a : Mero) ≠ 0) {τ : ℂ} (hτ : τ ∈ Hs) :
    analyticOrderAt a τ ≠ ⊤ := by
  intro htop
  apply h0
  have hA : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
  have hz := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hτ
    (analyticOrderAt_eq_top.mp htop)
  have : ∀ᶠ z in codiscreteWithin Hs, a z = (0 : ℂ → ℂ) z :=
    Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz' => hz hz'
  rw [← Filter.Germ.coe_zero]
  exact Filter.Germ.coe_eq.mpr this

lemma germ_eq_of_eqOn {φ ψ : ℂ → ℂ} (h : ∀ z ∈ Hs, φ z = ψ z) : (φ : Mero) = (ψ : Mero) :=
  Filter.Germ.coe_eq.mpr (Filter.mem_of_superset (self_mem_codiscreteWithin Hs) fun z hz => h z hz)

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

lemma num_ne_zero (X : Tower Ω ε) (f : X.Kˣ) {a b : ℂ → ℂ} (hb : (b : Mero) ≠ 0)
    (hf : X.an (f : X.K) * (b : Mero) = (a : Mero)) : (a : Mero) ≠ 0 := by
  intro h
  apply hb
  have e : X.an ((f⁻¹ : X.Kˣ) : X.K) * X.an (f : X.K) = 1 := by
    rw [← map_mul, Units.inv_mul, map_one]
  calc (b : Mero) = X.an ((f⁻¹ : X.Kˣ) : X.K) * (X.an (f : X.K) * b) := by rw [← mul_assoc, e, one_mul]
    _ = 0 := by rw [hf, h, mul_zero]

end GlobalTheory.KZ.H3.UnRoot

namespace GlobalTheory.KZ.H3.UnRoot

theorem exists_isRoot_of_mem_Un : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), JHol X →
    ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, IsRoot X m f a b := by
  intro Ω _ _ ε X hj m hm f hf
  obtain ⟨a0, b0, ha0, hb0, hb0ne, hf0⟩ := X.an_mero (f : X.K)
  have ha0ne : (a0 : Mero) ≠ 0 := num_ne_zero X f hb0ne hf0
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have hA : ∀ {c : ℂ → ℂ}, DifferentiableOn ℂ c Hs → ∀ τ ∈ Hs, AnalyticAt ℂ c τ :=
    fun hc τ hτ => hc.analyticOnNhd isOpen_Hs τ hτ
  have hord : ∀ τ ∈ Hs, ∃ k : ℕ, analyticOrderAt (a0 * b0 ^ m') τ = (((m' + 1) * k : ℕ) : ℕ∞) := by
    intro τ hτ
    obtain ⟨W, hW, hWmem⟩ := GlobalTheory.T.exists_tower_place_at_upperHalfPlane_point Ω ε X hj τ hτ
    obtain ⟨g, hg⟩ := hf W hW
    set u : X.K := (f : X.K) / (g : X.K) ^ (m' + 1) with hu
    have hgm : (g : X.K) ^ (m' + 1) ≠ 0 := pow_ne_zero _ g.ne_zero
    have hune : u ≠ 0 := div_ne_zero f.ne_zero hgm
    have huW : u ∈ W := (W.valuation_le_one_iff u).mp hg.le
    have huW' : u⁻¹ ∈ W := (W.valuation_le_one_iff u⁻¹).mp (by rw [map_inv₀, hg, inv_one])
    obtain ⟨φ, hφ, hφa⟩ := (hWmem u).mp huW
    obtain ⟨ψ, hψ, hψa⟩ := (hWmem u⁻¹).mp huW'

    have hφψ : ((φ * ψ : ℂ → ℂ) : Mero) = ((1 : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_mul, Filter.Germ.coe_one, ← hφ, ← hψ, ← map_mul, mul_inv_cancel₀ hune, map_one]
    have hφτ : φ τ ≠ 0 := by
      have e : φ τ * ψ τ = 1 := (eq_nhds_of_punctured (hφa.continuousAt.mul hψa.continuousAt) continuousAt_const
        (eventually_of_germ_eq hφψ hτ)).self_of_nhds
      intro h0
      rw [h0, zero_mul] at e
      exact zero_ne_one e

    obtain ⟨a1, b1, ha1, hb1, hb1ne, hg1⟩ := X.an_mero (g : X.K)
    have ha1ne : (a1 : Mero) ≠ 0 := num_ne_zero X g hb1ne hg1
    have hfu : X.an (f : X.K) = X.an u * X.an (g : X.K) ^ (m' + 1) := by
      rw [← map_pow, ← map_mul, hu, div_mul_cancel₀ _ hgm]
    have hgerm : ((a0 * b1 ^ (m' + 1) : ℂ → ℂ) : Mero) = ((φ * a1 ^ (m' + 1) * b0 : ℂ → ℂ) : Mero) := by
      simp only [Filter.Germ.coe_mul, Filter.Germ.coe_pow]
      rw [← hf0, ← hg1, hfu, hφ]
      ring
    have hev := eq_nhds_of_punctured
      ((hA ha0 τ hτ).continuousAt.mul ((hA hb1 τ hτ).continuousAt.pow _))
      ((hφa.continuousAt.mul ((hA ha1 τ hτ).continuousAt.pow _)).mul (hA hb0 τ hτ).continuousAt)
      (eventually_of_germ_eq hgerm hτ)
    have hcong := analyticOrderAt_congr hev
    rw [analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb1 τ hτ).pow _), analyticOrderAt_pow (hA hb1 τ hτ),
      analyticOrderAt_mul (hφa.mul ((hA ha1 τ hτ).pow _)) (hA hb0 τ hτ),
      analyticOrderAt_mul hφa ((hA ha1 τ hτ).pow _), analyticOrderAt_pow (hA ha1 τ hτ),
      hφa.analyticOrderAt_eq_zero.mpr hφτ] at hcong
    obtain ⟨oA0, orbitMap_conj_smul_zero⟩ := ENat.ne_top_iff_exists.mp (order_ne_top ha0 ha0ne hτ)
    obtain ⟨oB0, eB0⟩ := ENat.ne_top_iff_exists.mp (order_ne_top hb0 hb0ne hτ)
    obtain ⟨oA1, orbitMap_conj_smul_one⟩ := ENat.ne_top_iff_exists.mp (order_ne_top ha1 ha1ne hτ)
    obtain ⟨oB1, eB1⟩ := ENat.ne_top_iff_exists.mp (order_ne_top hb1 hb1ne hτ)
    rw [← orbitMap_conj_smul_zero, ← eB0, ← orbitMap_conj_smul_one, ← eB1] at hcong
    have heq : oA0 + (m' + 1) * oB1 = (m' + 1) * oA1 + oB0 := by
      simp only [nsmul_eq_mul, zero_add] at hcong
      exact_mod_cast hcong
    have hdvd : (m' + 1) ∣ oA0 + m' * oB0 :=
      Int.natCast_dvd_natCast.mp ⟨(oA1 : ℤ) + oB0 - oB1, by
        have := congrArg (fun n : ℕ => (n : ℤ)) heq
        push_cast at this ⊢
        linear_combination this⟩
    obtain ⟨k, hk⟩ := hdvd
    refine ⟨k, ?_⟩
    rw [analyticOrderAt_mul (hA ha0 τ hτ) ((hA hb0 τ hτ).pow _), analyticOrderAt_pow (hA hb0 τ hτ),
      ← orbitMap_conj_smul_zero, ← eB0, ← hk]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  obtain ⟨r, hr, hrm⟩ := GlobalTheory.T.exists_holomorphic_root_upperHalfPlane (a0 * b0 ^ m') (m' + 1) hm (ha0.mul (hb0.pow _)) hord
  refine ⟨r, b0, hr, hb0, hb0ne, ?_⟩
  have e1 : ((r ^ (m' + 1) : ℂ → ℂ) : Mero) = ((a0 * b0 ^ m' : ℂ → ℂ) : Mero) :=
    germ_eq_of_eqOn fun z hz => by simpa using hrm z hz
  simp only [Filter.Germ.coe_pow, Filter.Germ.coe_mul] at e1 ⊢
  rw [e1, ← hf0]
  ring

end GlobalTheory.KZ.H3.UnRoot
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterOfUpperHalfPlaneRoot
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct

namespace GlobalTheory.KZ.H3

theorem exp_val_natCast (m k : ℕ) (hm : 0 < m) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ZMod m).val : ℕ) : ℂ) / (m : ℂ)) =
    Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  rw [ZMod.val_natCast]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hk : 2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ) =
      2 * Real.pi * Complex.I * ((k % m : ℕ) : ℂ) / (m : ℂ) + ((k / m : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
    conv_lhs => rw [← Nat.mod_add_div k m]
    push_cast
    field_simp
  rw [hk, Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one]

theorem kum_of_isRoot : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime],
    ∀ n : ℕ, ∀ (x : X.Khat l) (f : X.Kˣ) (a b : ℂ → ℂ), AdicCompletion.eval (idl l) (X.Kl l) n x = X.cls l n f →
    IsRoot X (l ^ n) f a b → ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  intro Ω _ _ ε X l _ n x f a b hx hr
  obtain ⟨G1, -, G3, -, G5⟩ := GlobalTheory.T.upperHalfPlane_holomorphic_germ_properties
  obtain ⟨M1, -, -, M4, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  obtain ⟨ha, hb, hb0, hab0⟩ := hr
  have hm : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  obtain ⟨M, hM, hlev⟩ := X.level (f : X.K)
  obtain ⟨φ, hφ⟩ : ∃ φ : ℂ → ℂ, X.an (f : X.K) = (φ : Mero) :=
    Filter.Germ.inductionOn (X.an (f : X.K)) (fun φ => ⟨φ, rfl⟩)
  have hab : (φ : Mero) * (b : Mero) ^ (l ^ n) = (a : Mero) ^ (l ^ n) := by rw [← hφ]; exact hab0
  have key : ∀ δ ∈ CongruenceSubgroup.Gamma M, ∃ k : ℕ, ∀ z ∈ Hs,
      a (mob (ofSL δ) z) * b z =
        Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / ((l ^ n : ℕ) : ℂ)) * (a z * b (mob (ofSL δ) z)) := by
    intro δ hδ
    have hφg : ((fun z => φ (mob (ofSL δ) z) : ℂ → ℂ) : Mero) = (φ : Mero) := by
      rw [← X.an_sl (ofSL δ) (f : X.K) φ hφ, hlev δ hδ, hφ]
    have dag : DifferentiableOn ℂ (fun z => a (mob (ofSL δ) z)) Hs :=
      ha.comp (M4 _) (fun z hz => M1 _ z hz)
    have dbg : DifferentiableOn ℂ (fun z => b (mob (ofSL δ) z)) Hs :=
      hb.comp (M4 _) (fun z hz => M1 _ z hz)
    have h1 : ((φ * b ^ (l ^ n) : ℂ → ℂ) : Mero) = ((a ^ (l ^ n) : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow]; exact hab
    have h2 : (((fun z => φ (mob (ofSL δ) z)) * (fun z => b (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) =
        (((fun z => a (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) := G3 (ofSL δ) _ _ h1
    rw [Filter.Germ.coe_mul, Filter.Germ.coe_pow, Filter.Germ.coe_pow, hφg] at h2
    have h3 : ((((fun z => a (mob (ofSL δ) z)) * b) ^ (l ^ n) : ℂ → ℂ) : Mero) =
        (((a * fun z => b (mob (ofSL δ) z)) ^ (l ^ n) : ℂ → ℂ) : Mero) := by
      rw [Filter.Germ.coe_pow, Filter.Germ.coe_pow, Filter.Germ.coe_mul, Filter.Germ.coe_mul]
      linear_combination (-(b : Mero) ^ (l ^ n)) * h2 +
        ((fun z => b (mob (ofSL δ) z) : ℂ → ℂ) : Mero) ^ (l ^ n) * hab
    have h4 := (G1 _ _ ((dag.mul hb).pow _) ((ha.mul dbg).pow _)).1 h3
    obtain ⟨k, hk⟩ := G5 (l ^ n) ((fun z => a (mob (ofSL δ) z)) * b) (a * fun z => b (mob (ofSL δ) z)) hm
      (dag.mul hb) (ha.mul dbg) h4
    exact ⟨k, hk⟩
  classical
  let χ : SL(2, ℤ) → ZMod (l ^ n) := fun δ =>
    if h : δ ∈ CongruenceSubgroup.Gamma M then ((key δ h).choose : ZMod (l ^ n)) else 0
  refine ⟨χ, f, a, b, M, hM, hx, ⟨ha, hb, hb0, hab0⟩, fun δ hδ z hz => ?_⟩
  have hc : ((l : ℂ) ^ n) = ((l ^ n : ℕ) : ℂ) := by push_cast; rfl
  simp only [χ, dif_pos hδ]
  rw [hc, exp_val_natCast (l ^ n) _ hm]
  exact (key δ hδ).choose_spec z hz

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLaurentSeriesSumCongruentModPPowStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois GlobalTheory.GeoFix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_laurentSeries_sum_congruent_mod_p_pow : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω] (T : Tower p Ω) (n : ℕ) (ψ : O0 p →+* Ω), IsReb T n ψ → ∀ (d : ℕ) (e : Fin d → Ω) (b : Fin d → O0 p), (∀ t, IsInt p (e t)) → ∀ K : ℕ, ∃ a : Fin d → Lau p, Cong p K (∑ t, e t * ψ (b t)) (∑ t, e t * ψ (algebraMap (Lau p) (O0 p) (a t))) := by
  first | exact @GlobalTheory.GeoFix.exists_cong_lau | exact GlobalTheory.GeoFix.exists_cong_lau | (intros; apply GlobalTheory.GeoFix.exists_cong_lau <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalAutFixingTowerParamOfStabilizesStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_aut_fixing_tower_param_of_stabilizes : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (p : ℕ) [Fact p.Prime] (A : ValuationSubring Ω) (Ωl : Type) [Field Ωl] [Algebra (O0 p) Ωl], IsClo p Ωl → ∀ j : Ω →+* Ωl, (∀ x, x ∈ A ↔ IsInt p (j x)) → ∀ (T : GlobalTheory.K5.Tower p Ωl) (n : ℕ) (s : Ω ≃ₐ[ℚ] Ω), Stab A s → ∃ g : Gal p Ωl, g (T.qq n) = T.qq n ∧ ∀ x, g (j x) = j (s x) := by
  first | exact @GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab | exact GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab | (intros; apply GlobalTheory.Glue.CuspUp.exists_gal_fix_qq_of_stab <;> assumption)
end

