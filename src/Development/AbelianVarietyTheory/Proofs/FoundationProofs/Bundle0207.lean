import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0202
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.Chapter
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0188

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrablePeterssonIntegrandModerateGrowth
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem petInt_mp (γ : SL(2, ℤ)) : MeasurePreserving (fun z : ℍ => γ • z) volume volume := by
  have h := measurePreserving_smul ((γ : GL (Fin 2) ℝ)) (volume : Measure ℍ)
  convert h using 1
  ext z
  simp

theorem petInt_emb (γ : SL(2, ℤ)) : MeasurableEmbedding (fun z : ℍ => γ • z) := by
  have h := measurableEmbedding_const_smul (α := ℍ) ((γ : GL (Fin 2) ℝ))
  convert h using 1
  ext z
  simp

theorem petInt_fd_meas : MeasurableSet ModularGroup.fd := by
  unfold ModularGroup.fd
  apply IsClosed.measurableSet
  apply IsClosed.inter
  · exact isClosed_le continuous_const (Complex.continuous_normSq.comp UpperHalfPlane.continuous_coe)
  · exact isClosed_le (continuous_abs.comp (Complex.continuous_re.comp UpperHalfPlane.continuous_coe)) continuous_const

theorem petInt_im_bd (γ : SL(2, ℤ)) (σ : ℍ) (hσ : σ ∈ ModularGroup.fd) :
    (γ • σ).im ≤ 2 * σ.im ∧
      ((γ • σ).im)⁻¹ ≤ (3 * ((γ 1 0 : ℤ) : ℝ) ^ 2 + 8 * ((γ 1 1 : ℤ) : ℝ) ^ 2) * σ.im := by
  have hy : 3 ≤ 4 * σ.im ^ 2 := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hσ
  have hx : |σ.re| ≤ 1 / 2 := hσ.2
  have hyp : 0 < σ.im := σ.im_pos
  have hx2 : σ.re ^ 2 ≤ 1 / 4 := by nlinarith [abs_nonneg σ.re, sq_abs σ.re]
  have hdet : (γ 0 0 : ℤ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  have hcd : (1 : ℝ) ≤ ((γ 1 0 : ℤ) : ℝ) ^ 2 ∨ (((γ 1 0 : ℤ) : ℝ) = 0 ∧ ((γ 1 1 : ℤ) : ℝ) ^ 2 = 1) := by
    by_cases h0 : (γ 1 0 : ℤ) = 0
    · right
      rw [h0, mul_zero, sub_zero, mul_comm] at hdet
      rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h <;>
        simp [h0, h]
    · left
      have h1 : (1 : ℤ) ≤ (γ 1 0 : ℤ) ^ 2 := by
        rcases lt_or_gt_of_ne h0 with h | h <;> nlinarith
      exact_mod_cast h1
  have hN : Complex.normSq (UpperHalfPlane.denom (Matrix.SpecialLinearGroup.toGL
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) σ) =
      (((γ 1 0 : ℤ) : ℝ) * σ.re + ((γ 1 1 : ℤ) : ℝ)) ^ 2 + (((γ 1 0 : ℤ) : ℝ) * σ.im) ^ 2 := by
    rw [ModularGroup.denom_apply]
    simp [Complex.normSq_apply]
    ring
  rw [ModularGroup.im_smul_eq_div_normSq, hN]
  generalize ((γ 1 0 : ℤ) : ℝ) = c at *
  generalize ((γ 1 1 : ℤ) : ℝ) = d at *
  have hhalf : 1 / 2 ≤ (c * σ.re + d) ^ 2 + (c * σ.im) ^ 2 := by
    rcases hcd with h | ⟨hc, hd⟩
    · nlinarith [sq_nonneg (c * σ.re + d), mul_le_mul_of_nonneg_left hy (by positivity : (0:ℝ) ≤ c ^ 2)]
    · subst hc
      nlinarith
  have hNpos : 0 < (c * σ.re + d) ^ 2 + (c * σ.im) ^ 2 := by linarith
  constructor
  · rw [div_le_iff₀ hNpos]
    nlinarith
  · rw [inv_div, div_le_iff₀ hyp]
    nlinarith [sq_nonneg (c * σ.re - d), mul_le_mul_of_nonneg_left hx2 (sq_nonneg c),
      mul_le_mul_of_nonneg_left hy (sq_nonneg c), mul_le_mul_of_nonneg_left hy (sq_nonneg d)]

theorem petInt_real (k A : ℕ) (r q f t y C C' K δ : ℝ) (hr1 : r ≤ 1) (hq : 0 ≤ q) (hf : 0 ≤ f)
    (ht : 0 < t) (ht1 : t ≤ 2 * y) (ht2 : t⁻¹ ≤ K * y)
    (hdec : q ^ 2 * t ^ k ≤ C * Real.exp (-δ * y)) (hF : f ≤ C' * (t ^ A + (t ^ A)⁻¹)) :
    r * (q * f * t ^ k) ≤ C / 2 * (y ^ 0 * Real.exp (-(δ / 2) * y)) +
      (|C'| * (2 ^ A + K ^ A)) ^ 2 * 2 ^ k / 2 * (y ^ (2 * A + k) * Real.exp (-(δ / 2) * y)) := by
  have hy : 0 < y := by linarith
  have hKy : 0 < K * y := lt_of_lt_of_le (inv_pos.mpr ht) ht2
  set E := Real.exp (-(δ / 2) * y) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hE2 : Real.exp (-δ * y) = E * E := by
    rw [hE, ← Real.exp_add]
    ring_nf
  have htk : 0 < t ^ k := pow_pos ht k
  have hS : t ^ A + (t ^ A)⁻¹ ≤ (2 ^ A + K ^ A) * y ^ A := by
    have h1 : t ^ A ≤ (2 * y) ^ A := pow_le_pow_left₀ ht.le ht1 A
    have h2 : (t ^ A)⁻¹ ≤ (K * y) ^ A := by
      rw [← inv_pow]
      exact pow_le_pow_left₀ (by positivity) ht2 A
    rw [mul_pow] at h1 h2
    linarith
  have hSpos : 0 ≤ t ^ A + (t ^ A)⁻¹ := by positivity
  have hf' : f ≤ |C'| * ((2 ^ A + K ^ A) * y ^ A) :=
    le_trans hF (le_trans (mul_le_mul_of_nonneg_right (le_abs_self C') hSpos)
      (mul_le_mul_of_nonneg_left hS (abs_nonneg _)))
  have hf2 : f ^ 2 ≤ (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) := by
    calc f ^ 2 ≤ (|C'| * ((2 ^ A + K ^ A) * y ^ A)) ^ 2 := pow_le_pow_left₀ hf hf' 2
      _ = (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) := by
        rw [mul_comm 2 A, pow_mul]
        ring
  have htk2 : t ^ k ≤ 2 ^ k * y ^ k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ ht.le ht1 k
  have key : 2 * (q * f * t ^ k) * E ≤ (C * E + f ^ 2 * t ^ k * E) * E := by
    rw [hE2] at hdec
    nlinarith [mul_nonneg (sq_nonneg (q - f * E)) htk.le]
  have key2 : 2 * (q * f * t ^ k) ≤ C * E + f ^ 2 * t ^ k * E := le_of_mul_le_mul_right key hEpos
  have hft : f ^ 2 * t ^ k ≤ (|C'| * (2 ^ A + K ^ A)) ^ 2 * y ^ (2 * A) * (2 ^ k * y ^ k) :=
    mul_le_mul hf2 htk2 htk.le (by positivity)
  have hP : 0 ≤ q * f * t ^ k := by positivity
  refine le_trans (mul_le_of_le_one_left hP hr1) ?_
  rw [pow_zero, one_mul, pow_add]
  nlinarith [mul_le_mul_of_nonneg_right hft hEpos.le]

theorem integrable_pet_integrand : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (a : ℕ → ℂ) (ρ : ℍ → ℝ) (F : ℍ → ℂ), 1 ≤ k → 0 < L' → N ∣ L' → Wt L ρ → CF k L' (ch ε) a → AEStronglyMeasurable F → Mod F → Integrable (fun τ : ℍ => (ρ τ : ℂ) * (conj (qs a τ) * F τ * (τ.im : ℂ) ^ k)) := by
  intro k L L' N ε a ρ F hk hL' hN hW hCF hFm hMod
  set g : ℍ → ℂ := fun τ => (ρ τ : ℂ) * (conj (qs a τ) * F τ * (τ.im : ℂ) ^ k) with hg
  have hρ1 : ∀ τ, ρ τ ≤ 1 := by
    intro τ
    have h := le_hasSum (hW.sum τ) 1 (fun j _ => hW.nonneg _)
    simpa using h
  have hqc : Continuous (qs a) := (qs_summable_continuous a hCF.1.1).2
  have hgm : AEStronglyMeasurable g volume := by
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp hW.meas).aestronglyMeasurable
    · refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ hFm) ?_
      · exact (Complex.continuous_conj.comp hqc).aestronglyMeasurable
      · exact ((Complex.continuous_ofReal.comp UpperHalfPlane.continuous_im).pow k).aestronglyMeasurable
  obtain ⟨S, hS⟩ := hW.supp
  obtain ⟨C', A, hC'⟩ := hMod
  have hsupp : Function.support g ⊆ ⋃ γ ∈ S, {τ : ℍ | γ • τ ∈ ModularGroup.fd} := by
    intro τ hτ
    have hρ : ρ τ ≠ 0 := by
      intro h0
      apply hτ
      simp [hg, h0]
    obtain ⟨γ, hγS, hγ⟩ := hS τ hρ
    exact Set.mem_biUnion hγS hγ
  rw [← integrableOn_iff_integrable_of_support_subset hsupp, integrableOn_finset_iUnion]
  intro γ hγS
  have hpre : (fun σ : ℍ => γ⁻¹ • σ) ⁻¹' {τ : ℍ | γ • τ ∈ ModularGroup.fd} = ModularGroup.fd := by
    ext σ
    simp
  rw [← (petInt_mp γ⁻¹).integrableOn_comp_preimage (petInt_emb γ⁻¹), hpre]
  obtain ⟨C, δ, hδ, hdec⟩ := GlobalTheory.T.cuspForm_coeffSeq_exp_decay_at_every_cusp k L' N ε a γ⁻¹ hk hL' hN hCF
  set K : ℝ := 3 * (((γ⁻¹ : SL(2, ℤ)) 1 0 : ℤ) : ℝ) ^ 2 + 8 * (((γ⁻¹ : SL(2, ℤ)) 1 1 : ℤ) : ℝ) ^ 2 with hK
  refine Integrable.mono' (g := fun σ : ℍ => C / 2 * (σ.im ^ 0 * Real.exp (-(δ / 2) * σ.im)) +
      (|C'| * (2 ^ A + K ^ A)) ^ 2 * 2 ^ k / 2 * (σ.im ^ (2 * A + k) * Real.exp (-(δ / 2) * σ.im))) ?_ ?_ ?_
  · exact ((integrableOn_fd_im_pow_mul_exp (δ / 2) 0 (by positivity)).const_mul _).add
      ((integrableOn_fd_im_pow_mul_exp (δ / 2) (2 * A + k) (by positivity)).const_mul _)
  · exact (hgm.comp_measurePreserving (petInt_mp γ⁻¹)).restrict
  · refine (ae_restrict_iff' petInt_fd_meas).mpr (Filter.Eventually.of_forall fun σ hσ => ?_)
    have hy : 1 / 2 ≤ σ.im := by
      have := ModularGroup.three_le_four_mul_im_sq_of_mem_fd hσ
      nlinarith [σ.im_pos]
    obtain ⟨hb1, hb2⟩ := petInt_im_bd γ⁻¹ σ hσ
    have ht := (γ⁻¹ • σ).im_pos
    have hn : ‖g (γ⁻¹ • σ)‖ = ρ (γ⁻¹ • σ) * (‖qs a (γ⁻¹ • σ)‖ * ‖F (γ⁻¹ • σ)‖ * (γ⁻¹ • σ).im ^ k) := by
      simp only [hg, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, RCLike.norm_conj,
        abs_of_nonneg (hW.nonneg _), abs_of_pos ht]
    rw [Function.comp_apply, hn]
    exact petInt_real k A _ _ _ _ σ.im C C' K δ (hρ1 _) (norm_nonneg _) (norm_nonneg _) ht hb1 hb2
      (hdec σ hy) (hC' _)

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantInnerFormsProportionalWeightLineStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariant_inner_forms_proportional_weight_line : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j : M.V →ₗ[ℂ] H₁) (E₁ E₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j (M.act Z x)) (j y) = inner ℂ (j x) (j (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (E₁ (M.act Z x)) (E₂ y) = inner ℂ (E₁ x) (E₂ (M.act (adjZ Z) y))) → ∀ (μ : Ix p q → ℚ) (v : M.V), v ∈ wtSub M.act μ → (∀ x ∈ wtSub M.act μ, ∃ c : ℂ, x = c • v) → genSub M.act {v} = ⊤ → ‖j v‖ = 1 → ∀ x y, inner ℂ (E₁ x) (E₂ y) = inner ℂ (E₁ v) (E₂ v) * inner ℂ (j x) (j y) := by
  first | exact @GlobalTheory.FockForm.inner_eq_mul | exact GlobalTheory.FockForm.inner_eq_mul | (intros; apply GlobalTheory.FockForm.inner_eq_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantsFromFiniteLevel
section
open GlobalTheory.K5

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem charZero_of_tower (T : Tower p Ω) : CharZero Ω := by
  have hpp : p.Prime := Fact.out
  have hp : (p : Ω) ≠ 0 := by
    intro h0
    haveI : CharP Ω p := (CharP.charP_iff_prime_eq_zero hpp).mpr h0
    have hz := T.prim 1
    rw [pow_one] at hz
    have h1 : (T.ζ 1 - 1) ^ p = 0 := by rw [sub_pow_char, one_pow, hz.pow_eq_one, sub_self]
    have h2 : T.ζ 1 = 1 := sub_eq_zero.mp (pow_eq_zero_iff hpp.ne_zero |>.mp h1)
    rw [h2] at hz
    exact hpp.one_lt.ne' (hz.eq_orderOf.trans orderOf_one)
  let f : ℤ_[p] →+* Ω :=
    (algebraMap (O0 p) Ω).comp ((algebraMap (Lau p) (O0 p)).comp (algebraMap ℤ_[p] (Lau p)))
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra hn0
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 p hpp.one_lt.ne'
  have hu : IsUnit (((m : ℤ) : ℤ_[p])) := by
    refine PadicInt.isUnit_iff.mpr (le_antisymm (PadicInt.norm_le_one _) (not_lt.mp fun h => hm ?_))
    exact Int.natCast_dvd_natCast.mp ((PadicInt.norm_int_lt_one_iff_dvd _).mp h)
  have hmu : IsUnit (m : Ω) := by
    have := hu.map f
    simpa using this
  push_cast at hn
  rcases mul_eq_zero.mp hn with h | h
  · exact hp (pow_eq_zero_iff' |>.mp h).1
  · exact hmu.ne_zero h

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zeta_eq_pow (T : Tower p Ω) (i d : ℕ) : T.ζ i = T.ζ (i + d) ^ (p ^ d) := by
  induction d with
  | zero => simp
  | succ d ih => rw [ih, ← T.ζpow (i + d), ← pow_mul, ← pow_succ', add_assoc]

theorem qq_eq_pow (T : Tower p Ω) (i d : ℕ) : T.qq i = T.qq (i + d) ^ (p ^ d) := by
  induction d with
  | zero => simp
  | succ d ih => rw [ih, ← T.qpow (i + d), ← pow_mul, ← pow_succ', add_assoc]

def gens (T : Tower p Ω) (n : ℕ) : Set Ω :=
  Set.range (algebraMap (O0 p) Ω) ∪ T.ζ '' Set.Iic n ∪ T.qq '' Set.Iic n

theorem gens_mono (T : Tower p Ω) {m n : ℕ} (h : m ≤ n) : gens T m ⊆ gens T n := by
  unfold gens
  gcongr <;> exact Set.Iic_subset_Iic.mpr h

theorem fixes_gens (T : Tower p Ω) (n : ℕ) (g : Gal p Ω) (hg : g ∈ Gn T n) :
    ∀ a ∈ gens T n, g a = a := by
  have hz : g (T.ζ n) = T.ζ n := (Subgroup.mem_inf.mp hg).1
  have hq : g (T.qq n) = T.qq n := (Subgroup.mem_inf.mp hg).2
  rintro a ((⟨r, rfl⟩ | ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩)
  · exact g.commutes r
  · have hi' : i + (n - i) = n := Nat.add_sub_cancel' hi
    rw [zeta_eq_pow T i (n - i), hi', map_pow, hz]
  · have hi' : i + (n - i) = n := Nat.add_sub_cancel' hi
    rw [qq_eq_pow T i (n - i), hi', map_pow, hq]

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem exists_level_of_fixed (hClo : IsClo p Ω) (T : Tower p Ω) (y : Ω)
    (hy : ∀ h ∈ ⨅ n, Gn T n, h y = y) : ∃ n, ∀ g ∈ Gn T n, g y = y := by
  haveI := charZero_of_tower T
  let L : IntermediateField ℚ Ω := IntermediateField.adjoin ℚ (⋃ n, gens T n)
  have hmemL : ∀ a ∈ ⋃ n, gens T n, a ∈ L := fun a ha => IntermediateField.subset_adjoin ℚ _ ha
  have hO : ∀ r : O0 p, algebraMap (O0 p) Ω r ∈ L := fun r =>
    hmemL _ (Set.mem_iUnion.mpr ⟨0, Or.inl (Or.inl ⟨r, rfl⟩)⟩)
  let φ : O0 p →+* L := (algebraMap (O0 p) Ω).codRestrict L hO
  have hφ : ∀ r, algebraMap L Ω (φ r) = algebraMap (O0 p) Ω r := fun r => rfl
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply hClo.inj
    rw [← hφ a, ← hφ b, hab]
  haveI halg : Algebra.IsAlgebraic L Ω := by
    constructor
    intro z
    obtain ⟨P, hP0, hPz⟩ := hClo.alg.isAlgebraic z
    refine ⟨P.map φ, (Polynomial.map_ne_zero_iff hφinj).mpr hP0, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def] at hPz
    convert hPz using 2
    exact RingHom.ext hφ
  haveI : IsAlgClosure L Ω := ⟨hClo.clo, halg⟩
  haveI : IsGalois L Ω := IsAlgClosure.isGalois L Ω
  have hyL : y ∈ L := by
    have : y ∈ Set.range (algebraMap L Ω) := by
      rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
      intro f
      let g : Gal p Ω := AlgEquiv.ofRingEquiv (f := f.toRingEquiv) (fun r => f.commutes (φ r))
      have hg : g ∈ ⨅ n, Gn T n := by
        refine Subgroup.mem_iInf.mpr fun n => Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · show g (T.ζ n) = T.ζ n
          exact f.commutes ⟨T.ζ n, hmemL _ (Set.mem_iUnion.mpr ⟨n, Or.inl (Or.inr ⟨n, Set.mem_Iic.mpr le_rfl, rfl⟩)⟩)⟩
        · show g (T.qq n) = T.qq n
          exact f.commutes ⟨T.qq n, hmemL _ (Set.mem_iUnion.mpr ⟨n, Or.inr ⟨n, Set.mem_Iic.mpr le_rfl, rfl⟩⟩)⟩
      exact hy g hg
    obtain ⟨l, rfl⟩ := this
    exact l.2
  obtain ⟨S, hS, hyS⟩ := IntermediateField.exists_finset_of_mem_adjoin hyL
  have hex : ∀ t ∈ S, ∃ m, t ∈ gens T m := fun t ht => Set.mem_iUnion.mp (hS ht)
  choose! m hm using hex
  refine ⟨S.sup m, fun g hg => ?_⟩
  have hSN : (S : Set Ω) ⊆ gens T (S.sup m) := fun t ht =>
    gens_mono T (Finset.le_sup (f := m) ht) (hm t ht)
  have hyN : y ∈ IntermediateField.adjoin ℚ (gens T (S.sup m)) :=
    IntermediateField.adjoin.mono ℚ _ _ hSN hyS
  let gq : Ω ≃ₐ[ℚ] Ω := AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun q => by simp)
  have hle : Algebra.adjoin ℚ (gens T (S.sup m)) ≤ AlgHom.equalizer (gq : Ω →ₐ[ℚ] Ω) (AlgHom.id ℚ Ω) :=
    Algebra.adjoin_le fun a ha => fixes_gens T _ g hg a ha
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.mp hyN
  have hr' : g r = r := hle hr
  have hs' : g s = s := hle hs
  rw [map_div₀, hr', hs']

end GlobalTheory.K5.FinLevel

namespace GlobalTheory.K5.FinLevel

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem sum_fixed (H : Subgroup (Gal p Ω)) (E : Finset (Gal p Ω)) (y₀ x : Ω)
    (hEH : ∀ g ∈ E, g ∈ H)
    (huniq : ∀ h ∈ H, ∃! g, g ∈ E ∧ h y₀ = g y₀ ∧ ∀ s ∈ ({x} : Finset Ω), h s = g s) :
    ∀ h ∈ H, h (∑ g ∈ E, g (y₀ * x)) = ∑ g ∈ E, g (y₀ * x) := by
  classical
  simp only [Finset.mem_singleton, forall_eq] at huniq
  let rep : Gal p Ω → Gal p Ω := fun a => if ha : a ∈ H then (huniq a ha).exists.choose else 1
  have hrep : ∀ a ∈ H, rep a ∈ E ∧ a y₀ = rep a y₀ ∧ a x = rep a x := by
    intro a ha
    simp only [rep, dif_pos ha]
    exact (huniq a ha).exists.choose_spec
  have hun : ∀ a ∈ H, ∀ g ∈ E, a y₀ = g y₀ → a x = g x → rep a = g := by
    intro a ha g hg h1 h2
    exact ((huniq a ha).unique (hrep a ha) ⟨hg, h1, h2⟩)
  intro h hh
  rw [map_sum]
  have hmem : ∀ g ∈ E, h * g ∈ H := fun g hg => H.mul_mem hh (hEH g hg)
  have hmem' : ∀ g ∈ E, h⁻¹ * g ∈ H := fun g hg => H.mul_mem (H.inv_mem hh) (hEH g hg)
  refine Finset.sum_bij' (fun g _ => rep (h * g)) (fun g _ => rep (h⁻¹ * g))
    (fun g hg => (hrep _ (hmem g hg)).1) (fun g hg => (hrep _ (hmem' g hg)).1) ?_ ?_ ?_
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem g hg)
    refine hun _ (hmem' _ (hrep _ (hmem g hg)).1) g hg ?_ ?_
    · rw [AlgEquiv.mul_apply, ← h1, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
    · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.symm_apply_apply]
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem' g hg)
    refine hun _ (hmem _ (hrep _ (hmem' g hg)).1) g hg ?_ ?_
    · rw [AlgEquiv.mul_apply, ← h1, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
    · rw [AlgEquiv.mul_apply, ← h2, AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply]
  · intro g hg
    obtain ⟨_, h1, h2⟩ := hrep _ (hmem g hg)
    show (h * g) (y₀ * x) = _
    rw [map_mul, map_mul (rep (h * g)), h1, h2]

end GlobalTheory.K5.FinLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAdmissibleSmoothingFactorDividedIndices
section
open scoped UpperHalfPlane MatrixGroups
open GlobalTheory.KZ GlobalTheory.Sieg

noncomputable section

namespace GlobalTheory.KZDist

lemma isAdmissibleSmoothingFactor_divided_indices (c m : ℕ) (x : Fin 2 → ℚ) (a b : ℕ) (hA : admitted c x) (hm : 0 < m) :
    admitted c ![(x 0 + a) / m, (x 1 + b) / m] := by
  obtain ⟨hc1, hc6, hnot⟩ := hA
  refine ⟨hc1, hc6, ?_⟩
  rintro ⟨⟨k, hk⟩, ⟨l, hl⟩⟩
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hk hl
  apply hnot
  refine ⟨⟨m * k - c * a, ?_⟩, ⟨m * l - c * b, ?_⟩⟩
  · push_cast; rw [hk]; field_simp; ring
  · push_cast; rw [hl]; field_simp; ring

lemma isOpen_Hs' : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

lemma codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [← Filter.forall_mem_nonempty_iff_neBot]
  intro s hs
  have hI : Complex.I ∈ Hs := by simp [Hs]
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 hs) _ hI
  have h2 : Hs ∈ nhdsWithin Complex.I {Complex.I}ᶜ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs'.mem_nhds hI)
  obtain ⟨z, hz1, hz2⟩ := Filter.nonempty_of_mem (Filter.inter_mem h1 h2)
  rcases hz1 with h | h
  · exact ⟨z, h⟩
  · exact absurd hz2 h

theorem siegel_distribution : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Tower Ω ε)
    (c : ℕ) (m : ℕ) (x : Fin 2 → ℚ), admitted c x → 0 < m → Nat.Coprime c m →
    ∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, siegel T c ![(x 0 + a) / m, (x 1 + b) / m] = siegel T c x := by
  intro Ω _ _ _ ε T c m x hA hm hcm
  haveI := codiscreteWithin_Hs_neBot
  apply T.an.injective
  rw [map_prod, GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c x hA]
  simp_rw [map_prod]
  have h1 : ∀ a ∈ Finset.range m, ∏ b ∈ Finset.range m, T.an (siegel T c ![(x 0 + a) / m, (x 1 + b) / m])
      = Filter.Germ.coeRingHom _ (∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m]) := by
    intro a _
    rw [map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [GlobalTheory.T.siegelUnitInTower_an_eq_siegelUnitOnComplex Ω ε T c _ (isAdmissibleSmoothingFactor_divided_indices c m x a b hA hm)]
    rfl
  rw [Finset.prod_congr rfl h1, ← map_prod]
  show ((∏ a ∈ Finset.range m, ∏ b ∈ Finset.range m, sgC c ![(x 0 + a) / m, (x 1 + b) / m] : ℂ → ℂ) : Mero) = _
  congr 1
  funext z
  simp only [Finset.prod_apply]
  exact GlobalTheory.SiegDist.sg_distribution c m x _ hA hm hcm

end GlobalTheory.KZDist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsKilledByLowerNilradicalActBlockDiagonalStatement
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKilledByLowerNilradical_act_blockDiagonal : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ Z : Mat p q, IsKC Z → ∀ x : V, KilledByLower act x → KilledByLower act (act Z x) := by
  first | exact @GlobalTheory.KilledByLowerStable.killedByLower_act | exact GlobalTheory.KilledByLowerStable.killedByLower_act | (intros; apply GlobalTheory.KilledByLowerStable.killedByLower_act <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IterULevelValStable
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory

lemma ch_periodic_of_dvd {N L : ℕ} (ε : DirichletCharacter ℂ N) (h : N ∣ L) (d : ℤ) :
    ch ε (d + L) = ch ε d := by
  unfold ch
  have : ((L : ℤ) : ZMod N) = 0 := by
    rw [Int.cast_natCast]; exact (ZMod.natCast_eq_zero_iff L N).2 h
  rw [Int.cast_add, this, add_zero]

theorem iterU_level_val_stable : ∀ (k N l m : ℕ) (ε : DirichletCharacter ℂ N) (t : ℕ → ℂ) (α : ℂ) (B : ℕ) (c a : ℕ → ℂ),
    1 ≤ k → l.Prime → α ≠ 0 → MF k (N * l ^ (m + 1)) (ch ε) a → MF k (N * l) (ch ε) ((Uo l)^[m] a) ∧
      (EigF k N l ε t α B c → ∀ r, m ≤ r → val B c l α r a = val B c l α m a) := by
  intro k N l m ε t α B c a hk hl hα ha
  have lev : ∀ m (a : ℕ → ℂ), MF k (N * l ^ (m + 1)) (ch ε) a → MF k (N * l) (ch ε) ((Uo l)^[m] a) := by
    intro m
    induction m with
    | zero => intro a ha; simpa using ha
    | succ m ih =>
      intro a ha
      have hU : MF k (N * l ^ (m + 1)) (ch ε) (Uo l a) := by
        refine GlobalTheory.T.coeffHeckeUOperator_lowers_level k (N * l ^ (m + 1)) l (ch ε) a hk hl ?_ ?_ ?_
        · exact Dvd.dvd.mul_left (dvd_pow_self l (Nat.succ_ne_zero m)) N
        · exact ch_periodic_of_dvd ε (Dvd.intro _ rfl)
        · simpa [pow_succ, mul_assoc] using ha
      rw [Function.iterate_succ_apply]
      exact ih _ hU
  have hb := lev m a ha
  refine ⟨hb, fun hE r hr => ?_⟩
  have per : ∀ d, ch ε (d + ((N * l : ℕ) : ℤ)) = ch ε d := ch_periodic_of_dvd ε (Dvd.intro _ rfl)
  have mfj : ∀ j, MF k (N * l) (ch ε) ((Uo l)^[j] ((Uo l)^[m] a)) := by
    intro j
    induction j with
    | zero => simpa using hb
    | succ j ih =>
      rw [Function.iterate_succ_apply']
      exact (GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l (ch ε) _ hk hl (Dvd.intro_left _ rfl) per ih).1
  have lamj : ∀ j, lam B c ((Uo l)^[j] ((Uo l)^[m] a)) = α ^ j * lam B c ((Uo l)^[m] a) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', hE.U _ (mfj j), ih, pow_succ]
      ring
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hr
  unfold val
  rw [add_comm m j, Function.iterate_add_apply, lamj, pow_add]
  have hj : α ^ j ≠ 0 := pow_ne_zero _ hα
  field_simp

end GlobalTheory
end

