import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import Formalism.GL3MeanSquares.Bundle0001
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.CyclotomicNorms.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0148
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0149
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0135
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0144

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegersToCompletedUnramifiedCompositumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integers_to_completedUnramifiedCompositum : ∀ (l : ℕ) [Fact l.Prime] (K₀ L : Loc.FinExt l), ∃ f : ↥(Loc.OL K₀) →+* ↥(clC l (Kt l K₀ L)), ∀ y, (f y : ℂ_[l]) = algebraMap (PadicAlgCl l) ℂ_[l] ((y : ↥K₀.1) : PadicAlgCl l) := by
  first | exact @GlobalTheory.HeightCounting.ToClC.exists_toClC | exact GlobalTheory.HeightCounting.ToClC.exists_toClC | (intros; apply GlobalTheory.HeightCounting.ToClC.exists_toClC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalDomainValuationCenterStatement
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_domain_valuation_center : ∀ (A B k : Type) [CommRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B] [Field k] (φ : B →+* k) (V : ValuationSubring k) (C : Subalgebra A B), RingHom.ker φ = maximalIdeal B → Algebra.FiniteType A C → IsIntegrallyClosed C → (∀ c ∈ C, V.valuation (φ c) ≤ 1) → (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (_ : Algebra A D) (ι : D →ₐ[A] B), IsIntegrallyClosed D ∧ Algebra.EssFiniteType A D ∧ Function.Injective ι ∧ (∀ d, V.valuation (φ (ι d)) ≤ 1) ∧ (∀ d ∈ maximalIdeal D, V.valuation (φ (ι d)) < 1) ∧ ∀ b : B, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a := by
  first | exact @GlobalTheory.valuativeChart_localise | exact GlobalTheory.valuativeChart_localise | (intros; apply GlobalTheory.valuativeChart_localise <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalFiniteTypeOverStatement
section
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_normal_finite_type_over : ∀ (A B : Type) [CommRing A] [Algebra.EssFiniteType ℤ A] [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] (C : Subalgebra A B), Algebra.FiniteType A C → (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, s ≠ 0 ∧ s * b = a) → ∃ C' : Subalgebra A B, C ≤ C' ∧ Algebra.FiniteType A C' ∧ IsIntegrallyClosed C' ∧ ∀ x ∈ C', IsIntegral C x := by
  first | exact @GlobalTheory.exists_finiteType_isIntegrallyClosed_integral_over | exact GlobalTheory.exists_finiteType_isIntegrallyClosed_integral_over | (intros; apply GlobalTheory.exists_finiteType_isIntegrallyClosed_integral_over <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPrimeNormOneShortInterval
section
open Finset ArithmeticFunction NumberField IsDedekindDomain Filter Topology GlobalTheory.Mem.An Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.An.ShortWindow

theorem ev_log_le {a k : ℝ} (ha : 0 < a) (hk : 0 < k) (A D : ℝ) (hD : 0 < D) :
    ∀ᶠ x : ℝ in atTop, A + D * Real.log x ≤ k * x ^ a := by
  have h1 := (isLittleO_log_rpow_atTop ha).bound (c := k / 2 / D) (by positivity)
  have h2 := (tendsto_rpow_atTop ha).eventually_ge_atTop (A / (k / 2))
  filter_upwards [h1, h2, eventually_ge_atTop (0 : ℝ)] with x h1 h2 hx
  have hp : 0 ≤ x ^ a := Real.rpow_nonneg hx a
  rw [Real.norm_of_nonneg hp] at h1
  have h3 : Real.log x ≤ k / 2 / D * x ^ a := (le_abs_self _).trans h1
  have h4 : D * Real.log x ≤ k / 2 * x ^ a := by
    calc D * Real.log x ≤ D * (k / 2 / D * x ^ a) := by gcongr
      _ = k / 2 * x ^ a := by field_simp
  have h5 : A ≤ k / 2 * x ^ a := by
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  linarith

theorem exp_term_le {C x W y : ℝ} (hC : 0 < C) (hx : 0 < x) (hW : 1 ≤ W) (hWx : W ≤ x ^ (12 : ℝ))
    (hy : Real.log (200 * C) + 12 * Real.log x ≤ y) : C * Real.exp (-y) ≤ 1 / W / 200 := by
  have h1 : 200 * C * W ≤ Real.exp y := by
    calc 200 * C * W ≤ 200 * C * x ^ (12 : ℝ) := by gcongr
      _ = Real.exp (Real.log (200 * C) + 12 * Real.log x) := by
        rw [Real.exp_add, Real.exp_log (by positivity), Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
      _ ≤ _ := Real.exp_le_exp.2 hy
  have hW0 : 0 < W := by linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
  nlinarith

theorem exists_prime_normOne : GlobalTheory.Mem.An.QuadraticHeckeZeroEstimates → ∀ eps : ℝ, 0 < eps → eps < 1 / 52 → ∀ cs CY : ℝ, 0 < cs → 0 < CY → ∃ x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x → ∀ n q d g₁ g₂ m : ℕ, 1 ≤ n → Rowq x eps n q d → 1 ≤ g₁ → 1 ≤ g₂ → Real.log g₁ ≤ CY * x ^ eps → Real.log g₂ ≤ CY * x ^ eps → x ^ ((1 : ℝ) / 3) ≤ m → ∀ W Ts : ℝ, 1 ≤ W → W ≤ x ^ (12 : ℝ) → 0 < Ts → cs * m * x ^ eps ≤ Real.log Ts → ∃ T : ℕ, T.Prime ∧ Ts < T ∧ (T : ℝ) ≤ (1 + 1 / W) * Ts ∧ NormOne d (4 * n * q * d * (g₁ * g₂) ^ 2) T := by
  intro hTZ eps he _ cs CY hcs hCY
  obtain ⟨C₀, Cr, cr, c, hC₀, hCr, hcr, hc, H⟩ := GlobalTheory.T.norm_primes_short_interval_lower hTZ
  set CB : ℝ := 8 * CY + 6 with hCB
  have hCB0 : 0 < CB := by positivity
  have e1 := ev_log_le (a := 2 * eps / 5) (k := 1) (by positivity) one_pos 0 1 one_pos
  have e2 := ev_log_le (a := 1 / 3) (k := cs) (by positivity) hcs (C₀ * CB) 1 one_pos
  have e3 := ev_log_le (a := 1 / 3) (k := cr * cs / CB) (by positivity) (by positivity) (Real.log (200 * Cr)) 12 (by norm_num)
  have e4 := ev_log_le (a := 1 / 6) (k := cr * Real.sqrt cs) (by positivity) (by positivity) (Real.log (200 * Cr)) 12 (by norm_num)
  have e5 := ev_log_le (a := 1 / 3) (k := cs / 3) (by positivity) (by positivity) (7 * CB) 12 (by norm_num)
  have e6 := Real.tendsto_log_atTop.eventually_ge_atTop (100 : ℝ)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and (e6.and (eventually_ge_atTop (1 : ℝ))))))))
  refine ⟨x₀, fun x hx n q d g₁ g₂ m hn hR hg₁ hg₂ hl₁ hl₂ hm W Ts hW hWx hTs hT => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5, e6, hx1⟩ := hx₀ x hx
  obtain ⟨hq, -, -, -, hd, hd16, hdl, -, -, -, hN⟩ := hR
  have hx0 : 0 < x := by linarith
  have hW0 : 0 < W := by linarith
  set L : ℝ := x ^ eps with hL
  set u : ℝ := x ^ ((1 : ℝ) / 3) with hu
  have hL1 : 1 ≤ L := Real.one_le_rpow hx1 he.le
  have hu1 : 1 ≤ u := Real.one_le_rpow hx1 (by norm_num)
  have hlx : 0 ≤ Real.log x := by linarith
  have hd100 : 100 ≤ d := by
    have h1 : 1 ≤ x ^ (eps / 5) := Real.one_le_rpow hx1 (by positivity)
    have h2 : (10000 : ℝ) ≤ x ^ (eps / 5) * Real.log x ^ 2 := by
      calc (10000 : ℝ) = 1 * 100 ^ 2 := by norm_num
        _ ≤ _ := by gcongr
    have h3 : (100 : ℝ) ^ 2 ≤ GlobalTheoryTheory.X2 x eps := by
      have := Real.add_one_le_exp (x ^ (eps / 5) * Real.log x ^ 2)
      unfold GlobalTheoryTheory.X2
      linarith
    have h4 : (100 : ℝ) ≤ Real.sqrt (GlobalTheoryTheory.X2 x eps) := Real.le_sqrt_of_sq_le h3
    have h5 : (100 : ℝ) ≤ d := by linarith
    exact_mod_cast h5
  have hq1 : 1 ≤ q := hq.one_lt.le
  have hd1 : 1 ≤ d := hd.one_lt.le
  set M : ℕ := 4 * n * q * d * (g₁ * g₂) ^ 2 with hM
  have hM1 : 1 ≤ M := Nat.succ_le_of_lt (by positivity)
  set B : ℝ := 4 * (d : ℝ) * (M : ℝ) ^ 2 with hB
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hg₁R : (1 : ℝ) ≤ g₁ := by exact_mod_cast hg₁
  have hg₂R : (1 : ℝ) ≤ g₂ := by exact_mod_cast hg₂
  have hMR : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  have hB1 : 1 < B := by
    have : (1 : ℝ) ≤ (M : ℝ) ^ 2 := one_le_pow₀ hMR
    calc (1 : ℝ) < 4 * 1 * 1 := by norm_num
      _ ≤ 4 * (d : ℝ) * (M : ℝ) ^ 2 := by gcongr
  have hB0 : 0 < B := by linarith
  have hlB0 : 0 < Real.log B := Real.log_pos hB1
  have hNL : Real.log (4 * n * q * d) ≤ 2 * L := by
    have h1 : Real.log x ^ 2 ≤ (x ^ (2 * eps / 5)) ^ 2 := by
      gcongr; linarith
    have h2 : x ^ (eps / 5) * (x ^ (2 * eps / 5)) ^ 2 = L := by
      rw [hL, sq, ← Real.rpow_add hx0, ← Real.rpow_add hx0]; congr 1; ring
    have h3 : 0 ≤ x ^ (eps / 5) := by positivity
    calc _ ≤ 2 * x ^ (eps / 5) * Real.log x ^ 2 := hN
      _ ≤ 2 * x ^ (eps / 5) * (x ^ (2 * eps / 5)) ^ 2 := by gcongr
      _ = 2 * L := by rw [mul_assoc, h2]
  have hlB : Real.log B ≤ CB * L := by
    have h1 : B ≤ (4 * n * q * d : ℝ) ^ 3 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4 := by
      have h0 : (4 * d : ℝ) ≤ 4 * n * q * d := by
        calc (4 * d : ℝ) = 4 * 1 * 1 * d := by ring
          _ ≤ _ := by gcongr
      calc B = (4 * d : ℝ) * ((4 * n * q * d : ℝ) ^ 2 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4) := by
            rw [hB, hM]; push_cast; ring
        _ ≤ (4 * n * q * d : ℝ) * ((4 * n * q * d : ℝ) ^ 2 * (g₁ : ℝ) ^ 4 * (g₂ : ℝ) ^ 4) := by gcongr
        _ = _ := by ring
    have h2 := Real.log_le_log hB0 h1
    generalize Real.log B = lB at h2 ⊢
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow] at h2
    push_cast at h2
    rw [hCB]; linarith
  have hT' : cs * u * L ≤ Real.log Ts := le_trans (by gcongr) hT
  have hT0 : 0 < Real.log Ts := lt_of_lt_of_le (by positivity) hT'
  have a1 : B ^ C₀ ≤ Ts := by
    rw [Real.rpow_def_of_pos hB0, ← Real.le_log_iff_exp_le hTs]
    calc Real.log B * C₀ ≤ CB * L * C₀ := by gcongr
      _ = (C₀ * CB) * L := by ring
      _ ≤ cs * u * L := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      _ ≤ _ := hT'
  have a2 : 1 / W ≤ 1 := by rw [div_le_one hW0]; exact hW
  have a3 : Formalism.HermitianLattices.GL2PrimeSums.rhoErr Cr cr B Ts ≤ 1 / W / 100 := by
    unfold Formalism.HermitianLattices.GL2PrimeSums.rhoErr
    have b1 : Cr * Real.exp (-(cr * Real.log Ts / Real.log B)) ≤ 1 / W / 200 := by
      refine exp_term_le hCr hx0 hW hWx (e3.trans ?_)
      rw [le_div_iff₀ hlB0]
      calc cr * cs / CB * u * Real.log B ≤ cr * cs / CB * u * (CB * L) := by gcongr
        _ = cr * (cs * u * L) := by field_simp
        _ ≤ _ := by gcongr
    have b2 : Cr * Real.exp (-(cr * Real.sqrt (Real.log Ts))) ≤ 1 / W / 200 := by
      refine exp_term_le hCr hx0 hW hWx (e4.trans ?_)
      rw [mul_assoc]
      gcongr
      apply Real.le_sqrt_of_sq_le
      have : (x ^ ((1 : ℝ) / 6)) ^ 2 = u := by
        rw [hu, sq, ← Real.rpow_add hx0]; congr 1; norm_num
      rw [mul_pow, Real.sq_sqrt hcs.le, this]
      refine le_trans ?_ hT'
      exact le_mul_of_one_le_right (by positivity) hL1
    rw [neg_mul, neg_mul, neg_div]
    linarith
  have a4 : B ^ (7 : ℝ) ≤ 1 / W * Ts ^ ((1 : ℝ) / 3) := by
    have b1 : Real.log B * 7 + Real.log x * 12 ≤ Real.log Ts * (1 / 3) := by
      have c1 : Real.log x * 12 ≤ Real.log x * 12 * L := le_mul_of_one_le_right (by positivity) hL1
      have c2 : (7 * CB + 12 * Real.log x) * L ≤ cs / 3 * u * L := by gcongr
      linarith only [c1, c2, hlB, hT']
    have b2 := Real.exp_le_exp.2 b1
    rw [Real.exp_add, ← Real.rpow_def_of_pos hB0, ← Real.rpow_def_of_pos hx0, ← Real.rpow_def_of_pos hTs] at b2
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hW0]
    refine le_trans ?_ b2
    gcongr
  have key := H d M hd (by omega) hd100 hM1 Ts (1 / W) a1 a2 a3 a4
  have hpos : (0 : ℝ) < ((normPrimes d M Ts (Ts * (1 + 1 / W))).card : ℝ) :=
    lt_of_lt_of_le (by positivity) key
  obtain ⟨T, hTm⟩ := Finset.card_pos.1 (by exact_mod_cast hpos)
  unfold normPrimes at hTm
  simp only [Finset.mem_filter, Finset.mem_Ioc] at hTm
  obtain ⟨⟨t1, t2⟩, t3, t4⟩ := hTm
  refine ⟨T, t3, Nat.lt_of_floor_lt t1, ?_, t4⟩
  rw [mul_comm]
  exact (Nat.le_floor_iff (by positivity)).1 t2

end GlobalTheory.Mem.An.ShortWindow
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivAlgClosedOverNumberFieldCompEqStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringEquiv_algClosed_over_numberField_comp_eq : ∀ (K Ω₁ Ω₂ : Type) [Field K] [NumberField K] [Field Ω₁] [Field Ω₂] [IsAlgClosed Ω₁] [IsAlgClosed Ω₂] [CharZero Ω₁] [CharZero Ω₂] (a : K →+* Ω₁) (b : K →+* Ω₂), Cardinal.mk Ω₁ = Cardinal.mk Ω₂ → Cardinal.aleph0 < Cardinal.mk Ω₁ → ∃ ι : Ω₁ ≃+* Ω₂, ∀ x, ι (a x) = b x := by
  first | exact @GlobalTheory.AlgClosedIsoOverNumberField.exists_ringEquiv_comp_eq | exact GlobalTheory.AlgClosedIsoOverNumberField.exists_ringEquiv_comp_eq | (intros; apply GlobalTheory.AlgClosedIsoOverNumberField.exists_ringEquiv_comp_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingEquivFinExtIntegersPadicIntOf
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

noncomputable section

namespace GlobalTheory.IntOfFinExt

theorem mem_integer_iff_norm_le_one (l : ℕ) [Fact l.Prime] (x : PadicAlgCl l) :
    x ∈ (PadicAlgCl.valued l).v.integer ↔ ‖x‖ ≤ 1 := by
  rw [Valuation.mem_integer_iff]
  show ‖x‖₊ ≤ 1 ↔ ‖x‖ ≤ 1
  rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

theorem mem_intOf_iff (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l))
    (x : PadicAlgCl l) : x ∈ intOf l K ↔ x ∈ K ∧ ‖x‖ ≤ 1 := by
  unfold intOf
  rw [Subring.mem_inf, mem_integer_iff_norm_le_one]
  rfl

def toIntOf (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) : ↥(Loc.OL K) →+* ↥(intOf l K.1) :=
  RingHom.codRestrict ((K.1.val.toRingHom).comp (Loc.OL K).val.toRingHom) (intOf l K.1)
    (fun y => (mem_intOf_iff l K.1 _).2
      ⟨((y : ↥K.1)).2, (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K (y : ↥K.1)).1 y.2⟩)

theorem toIntOf_bijective (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) :
    Function.Bijective (toIntOf l K) := by
  constructor
  · intro a b h
    have h' : (((a : ↥K.1) : PadicAlgCl l)) = ((b : ↥K.1) : PadicAlgCl l) :=
      congrArg (fun w : ↥(intOf l K.1) => (w : PadicAlgCl l)) h
    exact Subtype.ext (Subtype.ext h')
  · intro z
    obtain ⟨hK, hn⟩ := (mem_intOf_iff l K.1 z).1 z.2
    refine ⟨⟨⟨(z : PadicAlgCl l), hK⟩,
      (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K ⟨(z : PadicAlgCl l), hK⟩).2 hn⟩, ?_⟩
    exact Subtype.ext rfl

theorem exists_ringEquiv_intOf : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l),
    ∃ e : ↥(Loc.OL K) ≃+* ↥(intOf l K.1), ∀ y, (e y : PadicAlgCl l) = ((y : ↥K.1) : PadicAlgCl l) :=
  fun l _ K => ⟨RingEquiv.ofBijective (toIntOf l K) (toIntOf_bijective l K), fun _ => rfl⟩

end GlobalTheory.IntOfFinExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRootOfUnityLiftFromResidueField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting

noncomputable section

namespace GlobalTheory.TameLift

theorem valuation_sub_lt_of_redThrough_eq {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {g : ℕ} [Fact g.Prime]
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) {x y : Ω} (hx : x ∈ A) (hy : y ∈ A)
    (h : redThrough A κ x = redThrough A κ y) : A.valuation (x - y) < 1 := by
  unfold redThrough at h
  rw [dif_pos hx, dif_pos hy] at h
  have h1 := κ.injective h
  have h2 : (⟨x, hx⟩ : A) - ⟨y, hy⟩ ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h1, sub_self]
  have := (A.valuation_lt_one_iff _).1 h2
  simpa using this

theorem exists_lift : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 E)), IsPlaceOver (F := E) A v → ∀ (g : ℕ) [Fact g.Prime],
    ((g : ℕ) : 𝓞 E) ∈ v.asIdeal → ∀ (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (m : ℕ), 0 < m → ¬ g ∣ m →
    ∀ c : Formalism.CyclotomicNorms.Fbar g, c ^ m = 1 → ∃ μ : Ω, μ ^ m = 1 ∧ redThrough A κ μ = c := by
  intro E Ω _ _ _ _ _ A v hA g hg hgv κ m hm hgm c hc
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : NeZero ((m : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hm.ne'⟩
  have : NeZero m := ⟨hm.ne'⟩

  have hvg : A.valuation (g : Ω) < 1 := by
    have := (hA (g : 𝓞 E)).2 hgv
    simpa using this

  have hvm : ¬ A.valuation (m : Ω) < 1 := by
    intro hlt
    have hcop : Nat.Coprime m g :=
      Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hg.out).mpr hgm)
    obtain ⟨u, w, huw⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    have e : ((u : Ω) * (m : Ω)) + (w : Ω) * (g : Ω) = 1 := by
      have := congrArg (fun z : ℤ => (z : Ω)) huw
      push_cast at this
      exact this
    have hu : A.valuation (u : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A u)
    have hw : A.valuation (w : Ω) ≤ 1 := (A.valuation_le_one_iff _).2 (intCast_mem A w)
    have h1 : A.valuation ((u : Ω) * (m : Ω)) < 1 := by
      rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' hu) hlt
    have h2 : A.valuation ((w : Ω) * (g : Ω)) < 1 := by
      rw [Valuation.map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left zero_le' hw) hvg
    have h3 := Valuation.map_add_lt A.valuation h1 h2
    rw [e, Valuation.map_one] at h3
    exact lt_irrefl _ h3
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω m
  have hζA : ζ ∈ A := mem_of_pow_eq_one A hm hζ.pow_eq_one
  have hr : IsPrimitiveRoot (redThrough A κ ζ) m := by
    refine IsPrimitiveRoot.mk_of_lt _ hm ?_ ?_
    · rw [← redThrough_pow A κ hζA, hζ.pow_eq_one, redThrough_one]
    · intro l hl hlm hrl
      rw [← redThrough_pow A κ hζA, ← redThrough_one A κ] at hrl
      have hv := valuation_sub_lt_of_redThrough_eq A κ (pow_mem hζA l) (one_mem A) hrl
      have heq : ζ ^ l = 1 := eq_of_pow_eq_one A hvm
        (by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]) (one_pow _) hv
      exact hζ.pow_ne_one_of_pos_of_lt hl.ne' hlm heq
  obtain ⟨i, -, hi⟩ := hr.eq_pow_of_pow_eq_one hc
  refine ⟨ζ ^ i, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  · rw [redThrough_pow A κ hζA, hi]

end GlobalTheory.TameLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTeichmullerReindexComplexPlace
section
open Polynomial

noncomputable section

namespace GlobalTheory.TeichAt

open Formalism.L2.NT GlobalTheory.ParRay

theorem orderOf_coprime {g : ℕ} [hg : Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : (orderOf x).Coprime g := by
  have hpos := (isOfFinOrder_fbar hx).orderOf_pos
  set n := orderOf x with hn
  refine (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hg.out).2 ?_))
  intro hdvd
  have hm : g ^ n.factorization g * (n / g ^ n.factorization g) = n := Nat.ordProj_mul_ordCompl_eq_self n g
  have h1 : x ^ (g ^ n.factorization g * (n / g ^ n.factorization g)) = 1 := by rw [hm, hn, pow_orderOf_eq_one]
  have h2 : x ^ (n / g ^ n.factorization g) = 1 := pow_eq_one_of_charP g x _ _ h1
  have h3 : n ∣ n / g ^ n.factorization g := orderOf_dvd_of_pow_eq_one h2
  exact Nat.not_dvd_ordCompl hg.out hpos.ne' (hdvd.trans h3)

theorem map_zero_of_inj {Ω : Type} [Field Ω] {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* Ω)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
  by_contra h0
  have h1 : t 0 = 1 := (mul_eq_left₀ h0).1 h
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  apply hx.2
  refine ht x 1 hx.1 one_ne_zero ?_
  have : t x = t x * t 0 := by rw [h1, mul_one]
  rw [this, ← map_mul, mul_zero, h1, map_one]

theorem exists_teich_reindex : ∀ (g : ℕ) [Fact g.Prime] (A : ValuationSubring ℂ)
    (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ),
    (∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) → ∃ t₀ : Formalism.CyclotomicNorms.Fbar g →* ℂ,
      Formalism.L2.NT.IsTeich A κ t₀ ∧ ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t₀ x = t₀ y → x = y := by
  intro g _ A κ t ht
  set s := redHom A κ t with hs_def
  have hs : ∀ x, s x = redThrough A κ (t x) := fun x => rfl
  have ht0 : t 0 = 0 := map_zero_of_inj t ht
  have hs0 : s 0 = 0 := by
    rw [hs, ht0]; unfold redThrough; rw [dif_pos (zero_mem A)]
    have : (⟨0, zero_mem A⟩ : A) = 0 := rfl
    rw [this, map_zero, map_zero]
  have hsne : ∀ x, x ≠ 0 → s x ≠ 0 := by
    intro x hx h0
    have hpos := (isOfFinOrder_fbar hx).orderOf_pos
    have : s x ^ orderOf x = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    rw [h0, zero_pow hpos.ne'] at this
    exact zero_ne_one this
  have hinj : Function.Injective s := by
    intro x y h
    rcases eq_or_ne x 0 with rfl | hx
    · rcases eq_or_ne y 0 with rfl | hy
      · rfl
      · exact absurd (h.symm.trans hs0) (hsne y hy)
    · rcases eq_or_ne y 0 with rfl | hy
      · exact absurd (h.trans hs0) (hsne x hx)
      · exact redHom_inj A κ t ht x y hx hy (orderOf_coprime hx) (orderOf_coprime hy) h
  have hsurj : Function.Surjective s := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · exact ⟨0, hs0⟩
    have hn := (isOfFinOrder_fbar hy).orderOf_pos
    set n := orderOf y
    have hmem : ∀ z : Formalism.CyclotomicNorms.Fbar g, z ∈ nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g) ↔ z ^ n = 1 :=
      fun z => mem_nthRootsFinset hn 1
    obtain ⟨a, -, ha⟩ := Finset.surj_on_of_inj_on_of_card_le (s := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g))
      (t := nthRootsFinset n (1 : Formalism.CyclotomicNorms.Fbar g)) (fun a _ => s a)
      (fun a ha => (hmem _).2 (by rw [← map_pow, (hmem a).1 ha, map_one]))
      (fun a₁ a₂ _ _ h => hinj h) le_rfl y ((hmem y).2 (pow_orderOf_eq_one y))
    exact ⟨a, ha.symm⟩
  let e : Formalism.CyclotomicNorms.Fbar g ≃* Formalism.CyclotomicNorms.Fbar g := MulEquiv.ofBijective s ⟨hinj, hsurj⟩
  have he : ∀ x, e x = s x := fun x => rfl
  refine ⟨t.comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro x
    refine ⟨mem_of_monoidHom A t _, ?_⟩
    have h1 : s (e.symm x) = x := by rw [← he, MulEquiv.apply_symm_apply]
    have h2 := hs (e.symm x)
    unfold redThrough at h2
    rw [dif_pos (mem_of_monoidHom A t _)] at h2
    exact h2.symm.trans h1
  · intro x y hx hy h
    have hx' : e.symm x ≠ 0 := fun h0 => hx (by rw [← e.apply_symm_apply x, h0, he, hs0])
    have hy' : e.symm y ≠ 0 := fun h0 => hy (by rw [← e.apply_symm_apply y, h0, he, hs0])
    exact e.symm.injective (ht _ _ hx' hy' h)

end GlobalTheory.TeichAt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwoPrimesSameNormOfTrivialFrobeniusStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_two_primes_same_norm_of_trivial_frobenius : ∀ (K F : Type) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F] (σ : F ≃ₐ[K] F), σ ≠ 1 → ∃ T : Set (HeightOneSpectrum (𝓞 K)), T.Finite ∧ ∀ v : HeightOneSpectrum (𝓞 K), v ∉ T → IsFrob F v 1 → ∃ P Q : HeightOneSpectrum (𝓞 F), P ≠ Q ∧ P.asIdeal.LiesOver v.asIdeal ∧ Q.asIdeal.LiesOver v.asIdeal ∧ Ideal.absNorm P.asIdeal = Ideal.absNorm v.asIdeal ∧ Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal := by
  first | exact @GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one | exact GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one | (intros; apply GlobalTheory.Mem.Fld.exists_two_primes_of_isFrob_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalKummerFieldOfPowerIdealRootsStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_kummerFieldOfPowerIdealRoots : ∀ (E : Type) [Field E] [NumberField E] (φ : E →+* ℂ) (h : ℕ), h ≠ 0 → FiniteDimensional ℚ (kummerField φ h) := by
  first | exact @GlobalTheory.Mem.FieldsEx.finiteDimensional_kummerField | exact GlobalTheory.Mem.FieldsEx.finiteDimensional_kummerField | (intros; apply GlobalTheory.Mem.FieldsEx.finiteDimensional_kummerField <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralMinorsIffBasisStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_minors_iff_basis_alt : ∀ (p : ℕ) [Fact p.Prime] (Lt : Type) [Fintype Lt] (N : ℕ) (nu : Lt → YoungDiagram)
    (hY : ∀ s, (nu s).colLen 0 ≤ N) (ι : Lt → Type) [∀ s, Fintype (ι s)]
    (b : ∀ s, ι s → MvPolynomial (Fin N × Fin N) ℚ)
    (c : ∀ s, GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ι s → ℤ) (d : ∀ s, ι s → GlobalTheory.WeylLatDualProof.IncreasingRowChoicePerColumn N (nu s) → ℤ),
    (∀ s J, GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J = ∑ k, (c s J k : ℚ) • b s k) →
    (∀ s k, b s k = ∑ J, (d s k J : ℚ) • GlobalTheory.WeylMinorDual.colProd ℚ N (nu s) (hY s) J) →
    ∀ φ : Module.Dual ℂ_[p] (MvPolynomial (Lt × ℕ × Fin N) ℂ_[p]),
      (∀ J : WeylLatticeDuality.ColChoice N nu,
          ‖φ (MvPolynomial.map (Int.castRingHom ℂ_[p]) (WeylLatticeDuality.nablaX N nu J))‖ ≤ 1) ↔
        ∀ κ : (∀ s, ι s), ‖φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
          (∏ s, MvPolynomial.rename (GlobalTheory.WeylLatDualProof.sig N s) (b s (κ s))))‖ ≤ 1 := by
  first | exact @GlobalTheory.WeylLatDualProof.integral_minors_iff_basis | exact GlobalTheory.WeylLatDualProof.integral_minors_iff_basis | (intros; apply GlobalTheory.WeylLatDualProof.integral_minors_iff_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LawsOfOkAlt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

set_option maxHeartbeats 1600000 in

theorem TDat.laws_of_ok : ∀ {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {S : GStep E K n}
    {ST : Finset (HeightOneSpectrum (𝓞 E))} (A : TDat S ST) (T : ℕ), S.Ok → A.Ok T → A.Laws T := by
  intro E K _ _ _ _ n S ST A T hS hA
  have h1 := GlobalTheory.T.primeLevelStructureData_ranks_mod_prime A T hS hA
  have h2 := GlobalTheory.T.levelFunctional_levelVector_laws A T hS hA
  have h3 := GlobalTheory.T.diamond_action_on_hermitianChartClasses A T hS hA
  have h4 := GlobalTheory.T.levelFunctional_dilated_class A T hS hA
  exact ⟨h1.1, h1.2, h2.2.1, h2.2.2, h3.1, h3.2.1, h4, h3.2.2⟩

end GlobalTheory.Mem.Col2
end

