import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.BaseEx
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0072
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0125
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0038
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0032
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0127
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0004
import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeTranslationOperatorEqPhaseMulNegComp
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsOrthogonalFrameNormsCoprimeOfUnimodular
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ImagQuadraticMaximalOrderArithmeticAtSplitPrime
import Formalism.LocalToGlobal.HermitianForms.TiedSym
import Formalism.LocalToGlobal.GroupLattices.DownNaturalLevelZero
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0126
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0128
import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormKappaSqMulDetIsometryEqOne
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker GlobalTheory.MomN

namespace GlobalTheory.KapVal

open IsDedekindDomain

theorem norm_le_one_of_isIntegral {q : ℕ} [Fact q.Prime] {x : ℂ_[q]} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h1 : IsIntegral (NormedField.valuation (K := ℂ_[q])).integer x := hx.tower_top
  have h2 := (Valuation.integer.integers (NormedField.valuation (K := ℂ_[q]))).mem_of_integral h1
  have h3 : ‖x‖₊ ≤ 1 := h2
  exact_mod_cast h3

theorem norm_le_one_of_int {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [NumberField K] (j : K →+* ℂ_[q])
    (y : 𝓞 K) : ‖j (y : K)‖ ≤ 1 :=
  norm_le_one_of_isIntegral (by
    convert map_isIntegral_int j (RingOfIntegers.isIntegral_coe y)
    exact Subsingleton.elim _ _)

theorem norm_natCast_lt_one (q : ℕ) [Fact q.Prime] : ‖((q : ℕ) : ℂ_[q])‖ < 1 := by
  have e : ((q : ℕ) : ℂ_[q]) = ((algebraMap ℚ_[q] (PadicAlgCl q) (q : ℚ_[q]) : PadicAlgCl q) : ℂ_[q]) := by
    simp
  rw [e, PadicComplex.norm_extends']
  exact Padic.norm_p_lt_one

end GlobalTheory.KapVal

namespace GlobalTheory.KapVal

open IsDedekindDomain

variable {q : ℕ} [Fact q.Prime] {K : Type} [Field K] [NumberField K]

theorem exists_place (j : K →+* ℂ_[q]) :
    ∃ w : HeightOneSpectrum (𝓞 K), ((q : ℕ) : 𝓞 K) ∈ w.asIdeal ∧ ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1 := by
  let P : Ideal (𝓞 K) :=
    { carrier := {x | ‖j (x : K)‖ < 1}
      add_mem' := fun {x y} hx hy => by
        show ‖j ((x : K) + (y : K))‖ < 1
        rw [map_add]
        exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx hy)
      zero_mem' := by
        show ‖j (0 : K)‖ < 1
        simp
      smul_mem' := fun r x hx => by
        show ‖j ((r : K) * (x : K))‖ < 1
        rw [map_mul, norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right (norm_le_one_of_int j r) (norm_nonneg _) hx }
  have hP : ∀ x : 𝓞 K, x ∈ P ↔ ‖j (x : K)‖ < 1 := fun _ => Iff.rfl
  have hl : ((q : ℕ) : 𝓞 K) ∈ P := by
    rw [hP]
    have e : j (((q : ℕ) : 𝓞 K) : K) = ((q : ℕ) : ℂ_[q]) := by simp
    rw [e]
    exact norm_natCast_lt_one q
  have hprime : P.IsPrime := by
    refine ⟨?_, fun {x y} hxy => ?_⟩
    · rw [Ideal.ne_top_iff_one, hP]
      simp
    · rw [hP] at hxy
      have e : j ((x * y : 𝓞 K) : K) = j (x : K) * j (y : K) := by simp
      rw [e, norm_mul] at hxy
      rw [hP, hP]
      by_contra h
      rw [not_or, not_lt, not_lt] at h
      exact absurd (one_le_mul_of_one_le_of_one_le h.1 h.2) (not_le.2 hxy)
  refine ⟨⟨P, hprime, ?_⟩, hl, hP⟩
  intro h0
  rw [h0, Ideal.mem_bot] at hl
  exact (Fact.out : q.Prime).ne_zero (by exact_mod_cast hl)

theorem norm_le_one_of_val (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (x : K) (hx : w.valuation K x ≤ 1) :
    ‖j x‖ ≤ 1 := by
  obtain ⟨n, d, h⟩ := w.exists_primeCompl_mul_eq_of_integer x hx
  have hd : 1 ≤ ‖j ((d : 𝓞 K) : K)‖ := not_lt.1 fun hlt => d.2 ((hw _).2 hlt)
  have h2 : ‖j x‖ * ‖j ((d : 𝓞 K) : K)‖ = ‖j (n : K)‖ := by
    rw [← norm_mul, ← map_mul]; exact congrArg (fun z => ‖j z‖) h
  have h3 := norm_le_one_of_int j n
  nlinarith [norm_nonneg (j x)]

theorem norm_eq_one_of_val (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (x : K) (hx : w.valuation K x = 1) :
    ‖j x‖ = 1 := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have h1 := norm_le_one_of_val j w hw x hx.le
  have h2 := norm_le_one_of_val j w hw x⁻¹ (by rw [map_inv₀, hx, inv_one])
  have h3 : ‖j x‖ * ‖j x⁻¹‖ = 1 := by
    rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
  nlinarith [norm_nonneg (j x), norm_nonneg (j x⁻¹)]

theorem norm_pow_eq (j : K →+* ℂ_[q]) (w : HeightOneSpectrum (𝓞 K))
    (hw : ∀ y : 𝓞 K, y ∈ w.asIdeal ↔ ‖j (y : K)‖ < 1) (n : ℕ) (π : 𝓞 K)
    (hπ : w.valuation K (π : K) = WithZero.exp (-(n : ℤ))) (x : K) (hx : x ≠ 0) :
    ‖j x‖ ^ n = ‖j (π : K)‖ ^ (-WithZero.log (w.valuation K x)) := by
  set y := -WithZero.log (w.valuation K x) with hy
  have hv0 : w.valuation K x ≠ 0 := by simpa using hx
  have hvx : w.valuation K x = WithZero.exp (-y) := by
    rw [hy, neg_neg, WithZero.exp_log hv0]
  have hπ0 : (π : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  have hz : w.valuation K (x ^ n * (π : K) ^ (-y)) = 1 := by
    rw [map_mul, map_pow, map_zpow₀, hvx, hπ, ← WithZero.exp_nsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add]
    rw [← WithZero.exp_zero]
    congr 1
    simp only [smul_eq_mul, nsmul_eq_mul]
    ring
  have h1 := norm_eq_one_of_val j w hw _ hz
  rw [map_mul, map_pow, map_zpow₀, norm_mul, norm_pow, norm_zpow] at h1
  have hjπ : ‖j (π : K)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero j).2 hπ0
  have h2 : ‖j (π : K)‖ ^ (-y) * ‖j (π : K)‖ ^ y = 1 := by
    rw [← zpow_add₀ hjπ, neg_add_cancel, zpow_zero]
  calc ‖j x‖ ^ n = ‖j x‖ ^ n * (‖j (π : K)‖ ^ (-y) * ‖j (π : K)‖ ^ y) := by rw [h2, mul_one]
    _ = (‖j x‖ ^ n * ‖j (π : K)‖ ^ (-y)) * ‖j (π : K)‖ ^ y := by ring
    _ = ‖j (π : K)‖ ^ y := by rw [h1, one_mul]

end GlobalTheory.KapVal

namespace GlobalTheory.KapVal

open IsDedekindDomain

theorem norm_kappa_sq_mul_det : ∀ (D : D7) (γ₀ γ : IsoK D) (k : KapChoice γ₀) (q : ℕ) [Fact q.Prime], q ≠ 2 →
    jacobiSym (-(D.host.d : ℤ)) q = 1 → γ.AtP q → ∀ ι : ℂ ≃+* ℂ_[q],
    ‖ι k.kappa‖ ^ 2 * ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = 1 := by
  intro D γ₀ γ k q _ hq2 hj hat ι
  have hqp : q.Prime := Fact.out
  have hs : SplitK D q := Or.inr hj
  let jK : D.host.K →+* ℂ_[q] := ι.toRingHom.comp (D.host.φ₀.comp (algebraMap D.host.K D.host.E))
  let jK' : D.host.K →+* ℂ_[q] := ι.toRingHom.comp (D.host.φ₀.comp
    ((D.host.conj : D.host.E →+* D.host.E).comp (algebraMap D.host.K D.host.E)))
  have ejK : ∀ z : D.host.K, jK z = ι (D.host.φ₀ (z : D.host.E)) := fun z => rfl
  have ejK' : ∀ z : D.host.K, jK' z = ι (D.host.φ₀ (D.host.conj (z : D.host.E))) := fun z => rfl
  have hU := GlobalTheory.T.relativeDeterminant_isometry_norm_one D γ₀ γ
  set x : D.host.K := γ.detRel γ₀ with hxdef
  set h : ℕ := classNumber D.host.K with hh
  have hy : ordK (k.pp q) x = k.yP q :=
    yIndep D γ₀ q (k.pp q) γ (k.gaP q) hqp hs (k.pp_over q hqp hs) hat (k.gaP_at q hqp hs)
  have hπv : (k.pp q).valuation D.host.K ((k.pi q : 𝓞 D.host.K) : D.host.K) = WithZero.exp (-(h : ℤ)) :=
    GlobalTheory.T.valuation_eq_exp_neg_of_pow_eq_span_singleton D.host.K (k.pp q) h (k.pi q) (k.pi_gen q hqp hs)
  have hkap := GlobalTheory.T.complexPadic_norm_kappa_splitPrime D γ₀ k q hs ι
  have hrt := k.rt_pow q hqp hs
  have hrt0 := k.rt_ne_zero q hqp hs
  set y : ℤ := k.yP q with hydef
  set 𝔭 := k.pp q with h𝔭
  set π : 𝓞 D.host.K := k.pi q with hπdef
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0] at hU
    simp at hU
  have hxx : ‖jK x‖ * ‖jK' x‖ = 1 := by
    rw [← norm_mul, ejK, ejK', ← map_mul, ← map_mul, hU, map_one, map_one, norm_one]
  obtain ⟨w, hqw, hw⟩ := exists_place jK
  obtain ⟨w', hqw', hw'⟩ := exists_place jK'
  have hne : w ≠ w' := by
    intro heq
    obtain ⟨y0, h1, h2⟩ := GlobalTheory.T.conjugate_embeddings_induce_different_primes_split D q hq2 hj ι
    have a1 : y0 ∈ w.asIdeal := (hw y0).2 (by rw [ejK]; exact h1)
    rw [heq, hw', ejK'] at a1
    exact absurd a1 (not_lt.2 h2)
  have hq𝔭 : ((q : ℕ) : 𝓞 D.host.K) ∈ 𝔭.asIdeal := k.pp_over q hqp hs
  have hnot : ∀ v : HeightOneSpectrum (𝓞 D.host.K), v ≠ 𝔭 → π ∉ v.asIdeal := by
    intro v hv hπ
    apply hv
    have h1 : 𝔭.asIdeal ^ h ≤ v.asIdeal := by
      rw [hh, k.pi_gen q hqp hs, Ideal.span_singleton_le_iff_mem]
      exact hπ
    have h2 : 𝔭.asIdeal ≤ v.asIdeal := v.isPrime.le_of_pow_le h1
    have h3 : 𝔭.asIdeal = v.asIdeal := 𝔭.isMaximal.eq_of_le v.isPrime.ne_top h2
    exact (HeightOneSpectrum.ext h3).symm
  have hone : ∀ (j : D.host.K →+* ℂ_[q]) (v : HeightOneSpectrum (𝓞 D.host.K)),
      (∀ z : 𝓞 D.host.K, z ∈ v.asIdeal ↔ ‖j (z : D.host.K)‖ < 1) → v ≠ 𝔭 → ‖j (π : D.host.K)‖ = 1 := by
    intro j v hv hv𝔭
    exact le_antisymm (norm_le_one_of_int j π) (not_lt.1 fun hlt => hnot v hv𝔭 ((hv π).2 hlt))
  have key : ‖jK x‖ ^ h = (‖jK (π : D.host.K)‖ / ‖jK' (π : D.host.K)‖) ^ y := by
    rcases GlobalTheory.T.quadratic_field_at_most_two_primes_over_prime D.host.K (kQuad D) q hqp 𝔭 w w' hq𝔭 hqw hqw' with e | e | e
    · have h1 := norm_pow_eq jK w hw h π (by rw [← e]; exact hπv) x hx0
      have h2 : -WithZero.log (w.valuation D.host.K x) = y := by rw [← e]; exact hy
      rw [h2] at h1
      rw [h1, hone jK' w' hw' (fun e' => hne (e.symm.trans e'.symm)), div_one]
    · have h1 := norm_pow_eq jK' w' hw' h π (by rw [← e]; exact hπv) x hx0
      have h2 : -WithZero.log (w'.valuation D.host.K x) = y := by rw [← e]; exact hy
      rw [h2] at h1
      rw [hone jK w hw (fun e' => hne (e'.trans e)), one_div, inv_zpow', zpow_neg, ← h1]
      have hx' : ‖jK x‖ = ‖jK' x‖⁻¹ := eq_inv_of_mul_eq_one_left hxx
      rw [hx', inv_pow]
    · exact absurd e hne
  have hjx : ‖ι (D.host.φ₀ ((γ.detRel γ₀ : D.host.K) : D.host.E))‖ = ‖jK x‖ := rfl
  rw [hjx, hkap]
  rw [← hh] at hrt
  have hr0 : 0 < ‖ι (k.rt q)‖ := norm_pos_iff.2 ((map_ne_zero ι).2 hrt0)
  have hratio : ‖jK (π : D.host.K)‖ / ‖jK' (π : D.host.K)‖ = ‖ι (k.rt q)‖ ^ (2 * h) := by
    rw [ejK, ejK', ← norm_div, ← map_div₀, ← hrt, map_pow, norm_pow]
  rw [hratio] at key
  have hh0 : h ≠ 0 := by rw [hh]; exact (NumberField.classNumber_pos D.host.K).ne'
  have hxr : ‖jK x‖ = ‖ι (k.rt q)‖ ^ (2 * y) := by
    have e : (‖ι (k.rt q)‖ ^ (2 * h)) ^ y = (‖ι (k.rt q)‖ ^ (2 * y)) ^ h := by
      rw [← zpow_natCast, ← zpow_natCast (‖ι (k.rt q)‖ ^ (2 * y)), ← zpow_mul, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [e] at key
    exact (pow_left_inj₀ (norm_nonneg _) (zpow_nonneg hr0.le _) hh0).1 key
  rw [hxr, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hr0.ne']
  rw [show -y * ((2 : ℕ) : ℤ) + 2 * y = 0 by push_cast; ring, zpow_zero]

end GlobalTheory.KapVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeError
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

theorem sign_of_sq_eq_one {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (h : χ ^ 2 = 1) (b : ℕ)
    (hb : Nat.Coprime b M) (θ : ℤ) (hθ : χ (b : ZMod M) = (θ : ℂ)) : θ = 1 ∨ θ = -1 := by
  have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  have h1 : (χ ^ 2) (b : ZMod M) = 1 := by rw [h]; exact MulChar.one_apply hu
  rw [MulChar.pow_apply' χ (by norm_num), hθ] at h1
  have h2 : θ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : (θ - 1) * (θ + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h4 | h4
  · left; omega
  · right; omega

theorem primesRel_holds : GlobalTheory.Lin.PrimesRel := by
  obtain ⟨a, ha, hA⟩ := GlobalTheory.T.exceptionalDirichletZero_unique_zeroFreeRegion
  obtain ⟨a', ha', hA'⟩ := GlobalTheory.T.chebyshevPsiProgression_relative_error
  have hc₁ : 0 < min (1 / 8 : ℝ) (min a a') := lt_min (by norm_num) (lt_min ha ha')
  obtain ⟨c, hc, hE⟩ := hA _ hc₁ ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨c₂, c₃, C, h₂, h₃, hC, hP⟩ := hA' _ hc₁ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨c₂', c₃', C', h₂', h₃', hC', hQ⟩ := GlobalTheory.T.primeCount_relative_error_of_psi_relative_error c₂ c₃ C c h₂ h₃ hC hc
  refine ⟨_, c₂', c₃', C', c, hc₁, min_le_left _ _, h₂', h₃', hC', hc, fun M _ hM => ?_⟩
  obtain ⟨hU, hB, -⟩ := hE M hM
  refine ⟨hU, fun χ β h => (hB χ β h).2.2.2.2, fun b θ β hb hD X hX => ?_⟩
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hφ1 : (1 : ℝ) ≤ (M.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (by omega)
  have hφ2 : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hθ : θ = 0 ∨ ((θ = 1 ∨ θ = -1) ∧ 7 / 8 ≤ β ∧ c / (M : ℝ) ^ 3 ≤ 1 - β) := by
    rcases hD with h | ⟨χ, hχ, hb'⟩
    · exact Or.inl h.1
    · obtain ⟨-, h78, -, -, hS⟩ := hB χ β hχ
      refine Or.inr ⟨sign_of_sq_eq_one χ hχ.1 b hb θ hb', h78, le_trans ?_ hS⟩
      have hl : 0 < Real.log M := Real.log_pos (by linarith)
      have hl2 : Real.log M ≤ M := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      apply div_le_div_of_nonneg_left hc.le (by positivity)
      calc (M : ℝ) ^ 2 * Real.log M ≤ (M : ℝ) ^ 2 * M := by gcongr
        _ = (M : ℝ) ^ 3 := by ring
  have := hQ M M.totient β θ (fun n => n ≡ b [MOD M]) hM3 hφ1 hφ2 hθ
    (fun u hu => by
      have := hP M b θ β u hM hb hD hu
      unfold psiAP at this
      convert this) X hX
  convert this

end GlobalTheory.Lin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientIntegrationFormulaDiscreteSubgroupLeftStatement
section
open MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quotient_integration_formula_discrete_subgroup_left : DiscreteClause := by
  first | exact @GlobalTheory.QuotDiscrete.discreteClause | exact GlobalTheory.QuotDiscrete.discreteClause | (intros; apply GlobalTheory.QuotDiscrete.discreteClause <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RationalVectorsAdelesFundamentalDomainMassOneStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.SWQ
open scoped TensorProduct NNReal ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalVectors_adeles_fundamentalDomain_mass_one : ∀ (F : Type) [Field F] [NumberField F] (N : ℕ) (ν : Measure (AF F)), IsCov1 ν → (muV N ν).IsAddHaarMeasure ∧ (∀ u : (Fin N → AF F), u ∈ (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) ↔ ∃ ξ, u = rat ξ) ∧ Function.Injective (rat : (Fin N → F) → (Fin N → AF F)) ∧ (∃ K : Set (Fin N → AF F), IsCompact K ∧ ∀ u, ∃ ξ, u - rat ξ ∈ K) ∧ ∃ D : Set (Fin N → AF F), MeasurableSet D ∧ IsAddFundamentalDomain (AddSubgroup.closure (Set.range (rat : (Fin N → F) → (Fin N → AF F)))) D (muV N ν) ∧ muV N ν D = 1 := by
  first | exact @GlobalTheory.SWQ.rat_lattice_fundamentalDomain | exact GlobalTheory.SWQ.rat_lattice_fundamentalDomain | (intros; apply GlobalTheory.SWQ.rat_lattice_fundamentalDomain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TranslatePrimeToOrderPreservesThetaIntegrality
section
open GlobalTheory.MomN Formalism.L2.Ker.JMB
open scoped ComplexConjugate BigOperators

noncomputable section
namespace GlobalTheory.MomTrans

variable {g : ℕ}

theorem ok_natCast_mul {d : ℕ} (n : ℕ) {z : ℂ} (h : z ∈ OK d) : (n : ℂ) * z ∈ OK d := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨n * u, n * v, by push_cast; ring⟩

theorem nnBasis_of_frame (q : ℕ) (S : Setup g) (hO : S.Ok) (x : Fin g → Fin g → ℂ) (a : Fin g → ℕ)
    (hx : ∀ i, x i ∈ S.La) (hb : ∀ i j, beta S.d S.Hm (x i) (x j) = if i = j then (a i : ℂ) else 0)
    (ha : ∀ i, 0 < a i ∧ Nat.Coprime (a i) q) : S.NNBasis q x := by
  classical
  have key : ∀ (c : Fin g → ℂ) (j : Fin g), beta S.d S.Hm (∑ i, c i • x i) (x j) = c j * a j := by
    intro c j
    rw [GlobalTheory.MomOne.Translates.beta_sum_left]
    simp [hb]
  have hli : LinearIndependent ℂ x := by
    rw [Fintype.linearIndependent_iff]
    intro c hc j
    have h := key c j
    rw [hc] at h
    have h0 : beta S.d S.Hm 0 (x j) = 0 := by simp [beta, hf]
    rw [h0] at h
    have : (a j : ℂ) ≠ 0 := by exact_mod_cast (ha j).1.ne'
    exact (mul_eq_zero.1 h.symm).resolve_right this
  let B := Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (by simp)).ge
  have hB : ∀ i, B i = x i := fun i => by simp [B]
  refine ⟨hx, fun y hy => ?_, fun c _ hc i => ?_⟩
  · have hy' : y = ∑ i, B.repr y i • x i := by
      conv_lhs => rw [← B.sum_repr y]
      simp only [hB]
    have hr : ∀ i, beta S.d S.Hm y (x i) = B.repr y i * a i := by
      intro i; conv_lhs => rw [hy']
      exact key _ i
    refine ⟨∏ i, a i, Nat.Coprime.prod_left fun i _ => (ha i).2,
      fun i => ((∏ j ∈ Finset.univ.erase i, a j : ℕ) : ℂ) * beta S.d S.Hm y (x i), fun i => ?_, ?_⟩
    · exact ok_natCast_mul _ (hO.2.2.2.2.2.2.1 y hy (x i) (hx i))
    · conv_lhs => rw [hy']
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      dsimp only
      rw [smul_smul, hr i, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      push_cast
      congr 1
      ring
  · exact (Fintype.linearIndependent_iff.1 hli) c hc i

theorem latInt_translate : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (δ₀ : ℂ) (θ : ℂ → ℂ) (Ω : ℂ_[q]) (g : ℕ) (S : Setup g) (e : (Fin g → ℂ) → ℂ) (t : Fin g → ℂ), Per S.d ι δ₀ θ Ω → S.Ok → GlobalTheory.MomOne.Split S.d q → S.IsTheta e → S.AlgJets δ₀ e → S.PrimeTo q t → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup e → LatInt ι (Ω / ι δ₀) S.La.toAddSubgroup (opU S.Hm t e) := by
  intro q _ ι δ₀ θ Ω g S e t hPer hO hS hth halg ht hLe
  obtain ⟨hIsTh, -, hδ, hall, hΩ, hLaws, -⟩ := hPer
  have hp : S.d.Prime := hO.1
  have h7 : S.d % 16 = 7 := hO.2.1
  have hq : q.Prime := Fact.out
  let lam : Qbar →+* ℂ_[q] := (ι : ℂ →+* ℂ_[q]).comp (algebraMap Qbar ℂ)
  have hlam : ∀ z : Qbar, ι (z : ℂ) = lam z := fun z => rfl
  have hqd : ¬ q ∣ S.d := (GlobalTheory.MomOne.okArith S.d q ι hp h7 hS).2.2.2.2.2.2
  obtain ⟨x, a, hx, hb, ha⟩ := GlobalTheory.MomOne.exists_orthFrame q g S hq hO hqd
  have hNN := nnBasis_of_frame q S hO x a hx hb ha
  obtain ⟨N, hN⟩ := GlobalTheory.MomOne.Translates.moments_of_translates S.d q lam δ₀ θ ι Ω hp h7 hS hIsTh hδ hall hlam hΩ
    hLaws g S rfl hO g x hNN e hth halg
  have h0 : S.PrimeTo q 0 := ⟨1, one_pos, Nat.coprime_one_left q, by simp [S.La.zero_mem]⟩
  obtain ⟨μ0, hμ0, hM0⟩ := hN 0 h0
  obtain ⟨μt, hμt, hMt⟩ := hN t ht
  have hU0 : opU S.Hm 0 e = e := by funext z; simp [opU, hf]
  have b0 := GlobalTheory.T.momentMeasure_norm_le_one_iff_latticeIntegral q ι lam δ₀ Ω g S g x 0 (opU S.Hm 0 e) μ0 hlam hδ hΩ hO hS hNN h0
    (GlobalTheory.MomOne.Translates.contDiff_opU S.Hm 0 hth.1) hM0
  have bt := GlobalTheory.T.momentMeasure_norm_le_one_iff_latticeIntegral q ι lam δ₀ Ω g S g x t (opU S.Hm t e) μt hlam hδ hΩ hO hS hNN ht
    (GlobalTheory.MomOne.Translates.contDiff_opU S.Hm t hth.1) hMt
  rw [hU0] at b0
  have hN1 : N ≤ 1 := hμ0 ▸ b0.2 hLe
  exact bt.1 (hμt ▸ hN1)

end GlobalTheory.MomTrans
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentTypeLevelCharacterFiniteOrderRootsOfUni
section
open Formalism.BasicNotions Formalism.L2.Forms NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace GlobalTheory

theorem natCast_residueField_completion_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by
  rw [← map_natCast (IsLocalRing.residue (v.adicCompletionIntegers F)), IsLocalRing.residue_eq_zero_iff]
  refine (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))
    (a := (p : v.adicCompletionIntegers F))).2 ?_
  have h1 : ((p : v.adicCompletionIntegers F) : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) ((p : 𝓞 F) : F) := by
    simp
  rw [h1]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v ((p : 𝓞 F) : F)
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v (p : 𝓞 F)).2 h
  exact h2.trans_lt h3

theorem unipotent_type_character_finite_order : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E σ J T f bad) (gp : Fin 2 → ℕ) (G : GLoc F E σ gp) (a t skip fc : ℕ) (zl : Bool) (_ : GLev S G a t 0 skip fc zl) (K : Type) [Field K] (s : K →+* ℂ), (∀ i, (gp i).Prime) → (∀ i, ∃ ζ : K, IsPrimitiveRoot ζ (gp i)) → ∃ N : ℕ, 0 < N ∧ ∀ x : S.U, ((S.chi x : ℂˣ) : ℂ) ^ N = 1 ∧ ∃ r : K, s r = ((S.chi x : ℂˣ) : ℂ) := by
  intro F E _ _ _ _ _ σ n J T f bad S gp G a t skip fc zl L K _ s hp hζ
  refine ⟨gp 0 * gp 1, Nat.mul_pos (hp 0).pos (hp 1).pos, fun x => ?_⟩
  rw [L.chi_eq x]
  let P : ℂ → Prop := fun z => z ^ (gp 0 * gp 1) = 1 ∧ ∃ r : K, s r = z
  have h1 : P 1 := ⟨one_pow _, 1, map_one s⟩
  have hm : ∀ y z, P y → P z → P (y * z) := by
    rintro y z ⟨hy, r, rfl⟩ ⟨hz, q, rfl⟩
    exact ⟨by rw [mul_pow, hy, hz, one_mul], r * q, map_mul s r q⟩
  change P _
  refine Finset.prod_induction _ P hm h1 fun i _ => ?_
  refine finprod_induction P h1 hm fun v => ?_
  refine finprod_induction P h1 hm fun h => ?_
  obtain ⟨⟨r, hr⟩, hpow⟩ := GlobalTheory.T.level_character_no_blocks_pth_root_of_unity (kv F v) K s (gp i) (hp i)
    (natCast_residueField_completion_eq_zero F v (gp i) h) (hζ i) n (G.psi0 i v h) (G.chiB i v h) a t skip
    (redM F v (G.mat i v h (L.fr i v h) (bc (prV (E := E) v) x.1)))
  refine ⟨?_, r⁻¹, by rw [map_inv₀, hr]⟩
  have hd : gp i ∣ gp 0 * gp 1 := by
    fin_cases i
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  obtain ⟨c, hc⟩ := hd
  rw [inv_pow, hc, pow_mul, hpow, one_pow, inv_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryFourfoldLatticePreservesRationalVectorsStatement
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_fourfoldLattice_preserves_rationalVectors : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ), IsCurveIdeal D cc → ∀ (u : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)), Formalism.L2.Th1.H.relIdx (Formalism.L2.Th1.H.stdLat B.L (Fin 4 × D.what₂.Tau)) (Formalism.L2.Th1.H.imgLat (u : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (Formalism.L2.Th1.H.pow4 B.lamM))) ≠ 0 → ∀ v : Fin 4 × D.what₂.Tau → D.host.K, ∃ v' : Fin 4 × D.what₂.Tau → D.host.K, u (fun w => D.host.φ₀ ((v w : D.host.K) : D.host.E)) = fun w => D.host.φ₀ ((v' w : D.host.K) : D.host.E) := by
  first | exact @GlobalTheory.LatDesc.unitary_maps_rational | exact GlobalTheory.LatDesc.unitary_maps_rational | (intros; apply GlobalTheory.LatDesc.unitary_maps_rational <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnitaryRationalPointsCountableDiscreteFundDomainStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryHaarMeasure
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRationalPoints_countable_discrete_fundDomains_cm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsDiscreteWithDomains (ratPts (AF F) σ J) := by
  first | exact @GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts | exact GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts | (intros; apply GlobalTheory.RationalUnitaryDomains.isDiscreteWithDomains_ratPts <;> assumption)
end

