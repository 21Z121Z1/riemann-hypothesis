import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0062
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefBoundOfCasselmanWallach
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimensionalPolyV
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0063
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AvgDerFamGrowthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.avg_derFam_growth_alt : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∃ C : ℝ, ∀ k : ↥(Formalism.REAL.KG ε), ∀ g ∈ UJset ε,
      ‖F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) g‖ ≤ C * (1 + hs g) ^ N) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ z ∈ UJset ε,
      MeasureTheory.AEStronglyMeasurable (fun k : ↥(Formalism.REAL.KG ε) =>
        F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k) (z * Formalism.REAL.toMK k)) (Formalism.REAL.muK ε)) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    GlobalTheory.TypeSum.IsDerFam ε (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) ∧
    GlobalTheory.TypeSum.FamGrowth ε N (fun l y => ∫ k, e k * F (l.map fun X => (Formalism.REAL.toMK k)⁻¹ * X * Formalism.REAL.toMK k)
                 (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) := by
  first | exact @GlobalTheory.KAvgDeriv.avg_derFam_growth | exact GlobalTheory.KAvgDeriv.avg_derFam_growth | (intros; apply GlobalTheory.KAvgDeriv.avg_derFam_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffSumSmoothRightDerivWordsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffSum_smooth_rightDerivWords : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∀ (d : ℕ) (L : Fin d → (H →ₗ[ℂ] ℂ)), (∀ a, Sobolev₂ (lieSet ε) σ (L a)) →
    ∀ x : Fin d → H, (∀ a, Sm ε σ (x a)) →
    CSm ε (fun y => ∑ a, L a (σ y (x a))) ∧ ∀ (u : List (Ltr ε)), ∀ y ∈ UJset ε,
      wordF u (fun y => ∑ a, L a (σ y (x a))) y = ∑ a, L a (σ y (wordV σ u (x a))) := by
  first | exact @GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF | exact GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF | (intros; apply GlobalTheory.TypeSum.CoefClos.coefSum_cSm_wordF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CoeffWordModerateGrowthBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TypeSum.CoefClos

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffWord_moderateGrowth_bound : ∀ (n : ℕ) (ε : Fin n → Bool) (N : ℕ) (f : Mx n → ℂ) (F : List (Mx n) → Mx n → ℂ),
    (∀ g ∈ UJset ε, F [] g = f g) → IsDerFam ε F → FamGrowth ε N F →
    ∀ u : List (Ltr ε), ∃ C : ℝ, ∀ g ∈ UJset ε, ‖wordF u f g‖ ≤ C * (1 + Formalism.REAL.hs g) ^ N := by
  first | exact @GlobalTheory.TypeSum.CoefClos.wordF_growth | exact GlobalTheory.TypeSum.CoefClos.wordF_growth | (intros; apply GlobalTheory.TypeSum.CoefClos.wordF_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryCoordFunMulEqSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem integral_conjK (ε : Fin n → Bool) (f : KG ε → ℂ) (a : KG ε) :
    ∫ k, f (a * k * a⁻¹) ∂(muK ε) = ∫ k, f k ∂(muK ε) := by
  haveI : Measure.IsMulRightInvariant (muK ε) := ⟨(compact_haar_holds n ε).2.2.1⟩
  have h1 := integral_mul_right_eq_self (μ := muK ε) (fun k => f (a * k)) a⁻¹
  have h2 := integral_mul_left_eq_self (μ := muK ε) f a
  simp only [mul_assoc] at h1 ⊢
  exact h1.trans h2

theorem integrable_of_continuousK {ε : Fin n → Bool} {f : KG ε → ℂ} (hf : Continuous f) :
    Integrable f (muK ε) := by
  haveI : IsFiniteMeasure (muK ε) := ⟨isCompact_univ.measure_lt_top⟩
  exact hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem lowV_le (ε : Fin n → Bool) (i : ℕ) : lowV ε i ≤ polyV ε i := by
  cases i with
  | zero => exact bot_le
  | succ j => exact polyV_mono ε (Nat.le_succ j)

theorem integral_sub_mulK {ε : Fin n → Bool} {f g h : KG ε → ℂ} (hf : Continuous f) (hg : Continuous g)
    (hh : Continuous h) :
    ∫ k, (f - g) k * h k ∂(muK ε) = ∫ k, f k * h k ∂(muK ε) - ∫ k, g k * h k ∂(muK ε) := by
  rw [← integral_sub (integrable_of_continuousK (f := fun k => f k * h k) (hf.mul hh))
    (integrable_of_continuousK (f := fun k => g k * h k) (hg.mul hh))]
  congr 1; funext k; simp [sub_mul]

theorem isKer_unique {ε : Fin n → Bool} {i : ℕ} {e e' : KG ε → ℂ} (he : IsKer ε i e) (he' : IsKer ε i e') :
    e = e' := by
  have hdmem : (e - e') ∈ polyV ε i := sub_mem he.1 he'.1
  have hc : Continuous (e - e') := continuous_of_mem hdmem
  have hce : Continuous e := continuous_of_mem he.1
  have hce' : Continuous e' := continuous_of_mem he'.1
  have hp : (fun k => star ((e - e') k)) ∈ polyV ε i := star_mem hdmem
  have horth : ∀ q ∈ lowV ε i, ∫ k, star (q k) * star ((e - e') k) ∂(muK ε) = 0 := by
    intro q hq
    have hqc : Continuous q := continuous_of_mem (lowV_le ε i hq)
    have h1 := he.2.1 q hq
    have h2 := he'.2.1 q hq
    have h3 : ∫ k, (e - e') k * q k ∂(muK ε) = 0 := by
      rw [integral_sub_mulK hce hce' hqc, h1, h2, sub_self]
    calc ∫ k, star (q k) * star ((e - e') k) ∂(muK ε)
        = ∫ k, (starRingEnd ℂ) ((e - e') k * q k) ∂(muK ε) := by
          congr 1; funext k; rw [map_mul, mul_comm]; rfl
      _ = (starRingEnd ℂ) (∫ k, (e - e') k * q k ∂(muK ε)) := integral_conj
      _ = 0 := by rw [h3, map_zero]
  have h0 : ∫ k, (e - e') k * star ((e - e') k) ∂(muK ε) = 0 := by
    have a1 := he.2.2 _ hp horth
    have a2 := he'.2.2 _ hp horth
    have hs : Continuous (fun k => star ((e - e') k)) := continuous_star.comp hc
    rw [integral_sub_mulK hce hce' hs, a1, a2, sub_self]
  have hns : Continuous (fun k => Complex.normSq ((e - e') k)) := Complex.continuous_normSq.comp hc
  have h1 : ∫ k, Complex.normSq ((e - e') k) ∂(muK ε) = 0 := by
    have : (fun k => (e - e') k * star ((e - e') k)) = fun k => ((Complex.normSq ((e - e') k) : ℝ) : ℂ) :=
      funext fun k => Complex.mul_conj _
    rw [this, integral_complex_ofReal] at h0
    exact_mod_cast h0
  have h2 : (fun k => Complex.normSq ((e - e') k)) =ᵐ[muK ε] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg _)
      ((integrable_of_continuousK (Complex.continuous_ofReal.comp hns)).re)).1 h1
  have h3 : (fun k => Complex.normSq ((e - e') k)) = 0 :=
    (Continuous.ae_eq_iff_eq (muK ε) hns continuous_const).1 h2
  funext k
  have := congrFun h3 k
  simp only [Pi.zero_apply, map_eq_zero, Pi.sub_apply] at this
  exact sub_eq_zero.1 this

theorem conj_mem {ε : Fin n → Bool} (a : KG ε) {d : ℕ} {φ : KG ε → ℂ} (h : φ ∈ polyV ε d) :
    (fun k => φ (a * k * a⁻¹)) ∈ polyV ε d := by
  have := mul_right_mem a⁻¹ (mul_left_mem a h)
  simpa only [mul_assoc] using this

theorem conj_mem_low {ε : Fin n → Bool} (a : KG ε) {i : ℕ} {φ : KG ε → ℂ} (h : φ ∈ lowV ε i) :
    (fun k => φ (a * k * a⁻¹)) ∈ lowV ε i := by
  cases i with
  | zero =>
    rw [lowV, Submodule.mem_bot] at h ⊢
    subst h
    rfl
  | succ j => exact conj_mem a h

theorem isKer_conj {ε : Fin n → Bool} {i : ℕ} {e : KG ε → ℂ} (he : IsKer ε i e) (a : KG ε) :
    IsKer ε i (fun k => e (a * k * a⁻¹)) := by
  have key : ∀ f g : KG ε → ℂ, ∫ k, f (a * k * a⁻¹) * g k ∂(muK ε) = ∫ k, f k * g (a⁻¹ * k * a) ∂(muK ε) := by
    intro f g
    rw [← integral_conjK ε (fun k => f k * g (a⁻¹ * k * a)) a]
    congr 1; funext k
    simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
  refine ⟨conj_mem a he.1, ?_, ?_⟩
  · intro q hq
    rw [key]
    have := conj_mem_low a⁻¹ hq
    simpa only [inv_inv] using he.2.1 _ this
  · intro p hp horth
    rw [key]
    have hp' : (fun k => p (a⁻¹ * k * a)) ∈ polyV ε i := by simpa only [inv_inv] using conj_mem a⁻¹ hp
    have horth' : ∀ q ∈ lowV ε i, ∫ k, star (q k) * p (a⁻¹ * k * a) ∂(muK ε) = 0 := by
      intro q hq
      rw [← integral_conjK ε (fun k => star (q k) * p (a⁻¹ * k * a)) a]
      have := horth _ (conj_mem_low a hq)
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using this
    rw [he.2.2 _ hp' horth']
    simp

theorem isKer_class : ∀ {n : ℕ} (ε : Fin n → Bool) (i : ℕ) (e : KG ε → ℂ), IsKer ε i e →
    ∀ a k : KG ε, e (a * k * a⁻¹) = e k := by
  intro n ε i e he a k
  have := isKer_unique (isKer_conj he a) he
  exact congrFun this k

end GlobalTheory.KFourier

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CompactUnitaryIntegralConjInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.KFourier

open MeasureTheory

variable {n : ℕ}

theorem integrable_of_continuous' {ε : Fin n → Bool} {E : Type*} [NormedAddCommGroup E] {f : KG ε → E} (hf : Continuous f) :
    Integrable f (muK ε) :=
  integrableOn_univ.1 (hf.continuousOn.integrableOn_compact isCompact_univ)

theorem eq_zero_of_integral_mul_star {ε : Fin n → Bool} {φ : KG ε → ℂ} (hc : Continuous φ)
    (h : ∫ k, φ k * star (φ k) ∂(muK ε) = 0) : φ = 0 := by
  have e : (fun k => φ k * star (φ k)) = fun k => ((Complex.normSq (φ k) : ℝ) : ℂ) := by
    funext k; exact Complex.mul_conj (φ k)
  rw [e, integral_complex_ofReal, Complex.ofReal_eq_zero] at h
  have hcs : Continuous fun k => Complex.normSq (φ k) := Complex.continuous_normSq.comp hc
  have hae := (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg (φ k))
    (integrable_of_continuous' hcs)).1 h
  have h2 : (fun k => Complex.normSq (φ k)) = 0 := (Continuous.ae_eq_iff_eq (muK ε) hcs continuous_const).1 hae
  funext k
  have := congrFun h2 k
  simpa using this

theorem exists_isKer (ε : Fin n → Bool) (i : ℕ) : ∃ e, IsKer ε i e := by
  classical
  have hlow : lowV ε i ≤ polyV ε i := by
    cases i with
    | zero => simp [lowV]
    | succ j => simpa [lowV] using polyV_mono ε (Nat.le_succ j)
  let W : Submodule ℂ (KG ε → ℂ) :=
    { carrier := {p | p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0}
      add_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨add_mem ha hb, fun q hq => ?_⟩
        have hq' := continuous_of_mem (hlow hq)
        have h1 := integral_add (μ := muK ε) (f := fun k => star (q k) * a k) (g := fun k => star (q k) * b k)
          (integrable_of_continuous' (hq'.star.mul (continuous_of_mem ha)))
          (integrable_of_continuous' (hq'.star.mul (continuous_of_mem hb)))
        simp only [Pi.add_apply, mul_add]
        rw [h1, ha' q hq, hb' q hq, add_zero]
      zero_mem' := ⟨Submodule.zero_mem _, fun q _ => by simp⟩
      smul_mem' := by
        rintro c a ⟨ha, ha'⟩
        refine ⟨Submodule.smul_mem _ c ha, fun q hq => ?_⟩
        simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        rw [integral_const_mul, ha' q hq, mul_zero] }
  have hW : ∀ p, p ∈ W ↔ p ∈ polyV ε i ∧ ∀ q ∈ lowV ε i, ∫ k, star (q k) * p k ∂(muK ε) = 0 :=
    fun p => Iff.rfl

  let B : polyV ε i →ₗ[ℂ] Module.Dual ℂ (polyV ε i) :=
    LinearMap.mk₂ ℂ (fun e p : polyV ε i => ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε))
      (fun e e' p => by
        have h1 := integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (g := fun k => (e' : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2)))
          (integrable_of_continuous' ((continuous_of_mem e'.2).mul (continuous_of_mem p.2)))
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
        exact h1)
      (fun c e p => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul c _)
      (fun e p p' => by
        have h1 := integral_add (μ := muK ε) (f := fun k => (e : KG ε → ℂ) k * (p : KG ε → ℂ) k)
          (g := fun k => (e : KG ε → ℂ) k * (p' : KG ε → ℂ) k)
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p.2)))
          (integrable_of_continuous' ((continuous_of_mem e.2).mul (continuous_of_mem p'.2)))
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        exact h1)
      (fun c e p => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        exact integral_const_mul c _)
  have hB : ∀ e p : polyV ε i, B e p = ∫ k, (e : KG ε → ℂ) k * (p : KG ε → ℂ) k ∂(muK ε) := fun _ _ => rfl
  have hinj : Function.Injective B := by
    rw [injective_iff_map_eq_zero]
    intro e he
    have h0 := hB e ⟨_, star_mem e.2⟩
    rw [he] at h0
    have hz : (e : KG ε → ℂ) = 0 := eq_zero_of_integral_mul_star (continuous_of_mem e.2) h0.symm
    exact Subtype.ext hz
  have hsurj : Function.Surjective B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).1 hinj

  let f : W →ₗ[ℂ] (KG ε → ℂ) ⧸ lowV ε i := (lowV ε i).mkQ ∘ₗ W.subtype
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hwl : (w : KG ε → ℂ) ∈ lowV ε i := (Submodule.Quotient.mk_eq_zero _).1 hw
    have h0 := ((hW w).1 w.2).2 _ hwl
    have hc : (fun k => star ((w : KG ε → ℂ) k) * (w : KG ε → ℂ) k) =
        fun k => (w : KG ε → ℂ) k * star ((w : KG ε → ℂ) k) := funext fun k => mul_comm _ _
    rw [hc] at h0
    exact Subtype.ext (eq_zero_of_integral_mul_star (continuous_of_mem ((hW w).1 w.2).1) h0)
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective f hker
  let g : (KG ε → ℂ) →ₗ[ℂ] ℂ := (LinearMap.proj 1 : (KG ε → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype ∘ₗ r ∘ₗ (lowV ε i).mkQ
  have hgW : ∀ w ∈ W, g w = w 1 := by
    intro w hw
    have := LinearMap.congr_fun hr ⟨w, hw⟩
    simp only [LinearMap.comp_apply, LinearMap.id_apply, f, Submodule.subtype_apply] at this
    simp only [g, LinearMap.comp_apply, Submodule.subtype_apply, this, LinearMap.proj_apply]
  have hgU : ∀ q ∈ lowV ε i, g q = 0 := by
    intro q hq
    simp only [g, LinearMap.comp_apply, (Submodule.Quotient.mk_eq_zero _).2 hq, Submodule.mkQ_apply, map_zero,
      LinearMap.proj_apply]
  obtain ⟨e, he⟩ := hsurj (g ∘ₗ (polyV ε i).subtype)
  refine ⟨e, e.2, fun q hq => ?_, fun p hp hpo => ?_⟩
  · have := LinearMap.congr_fun he ⟨q, hlow hq⟩
    rw [hB] at this
    rw [this]
    exact hgU q hq
  · have := LinearMap.congr_fun he ⟨p, hp⟩
    rw [hB] at this
    rw [this]
    exact hgW p ⟨hp, hpo⟩

end GlobalTheory.KFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ContinuousOnAvgRightTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuousOn_integral_mul_right_translate_toMK : ∀ (n : ℕ) (ε : Fin n → Bool) (f : GlobalTheory.TypeSum.Mx n → ℂ), ContinuousOn f (UJset ε) →
    ∀ e : ↥(Formalism.REAL.KG ε) → ℂ, Continuous e →
    ContinuousOn (fun y => ∫ k, e k * f (y * Formalism.REAL.toMK k) ∂(Formalism.REAL.muK ε)) (UJset ε) := by
  first | exact @GlobalTheory.AvgCont.continuousOn_avg_right_translates | exact GlobalTheory.AvgCont.continuousOn_avg_right_translates | (intros; apply GlobalTheory.AvgCont.continuousOn_avg_right_translates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.DerFamExpandWordsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory Filter Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derFam_ofFn_eq_sum_prod_coeff_of_expand : ∀ (n : ℕ) (ε : Fin n → Bool) (F : List (GlobalTheory.TypeSum.Mx n) → GlobalTheory.TypeSum.Mx n → ℂ), GlobalTheory.TypeSum.IsDerFam ε F →
    ∀ (d : ℕ) (b : Fin d → GlobalTheory.TypeSum.Mx n) (c : Fin d → GlobalTheory.TypeSum.Mx n → ℝ), (∀ i, b i ∈ lieSet ε) →
    (∀ l : List (GlobalTheory.TypeSum.Mx n), (∀ Y ∈ l, Y ∈ lieSet ε) → ∀ Z ∈ lieSet ε, ∀ g ∈ UJset ε,
      F (Z :: l) g = ∑ i, (c i Z : ℂ) * F (b i :: l) g) →
    ∀ (m : ℕ) (Y : Fin m → GlobalTheory.TypeSum.Mx n), (∀ j, Y j ∈ lieSet ε) → ∀ g ∈ UJset ε,
      F (List.ofFn Y) g = ∑ J : Fin m → Fin d, (∏ j, (c (J j) (Y j) : ℂ)) * F (List.ofFn fun j => b (J j)) g := by
  first | exact @GlobalTheory.TypeSum.derFam_expand_words | exact GlobalTheory.TypeSum.derFam_expand_words | (intros; apply GlobalTheory.TypeSum.derFam_expand_words <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ErrorDataOfNormGeneratorsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.EX GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.error_data_of_norm_generators : ∀ X : Stages, (∀ i, ∃ π : 𝓞 X.B.host.E, (π : X.B.host.E) ∈ X.B.host.K ∧ (π : X.B.host.E) * X.B.host.conj (π : X.B.host.E) = (X.B.host.g i : X.B.host.E)) → Nonempty (ErrX X.toD7) := by
  first | exact @GlobalTheory.SplitGen.nonempty_errX | exact GlobalTheory.SplitGen.nonempty_errX | (intros; apply GlobalTheory.SplitGen.nonempty_errX <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsFiniteRealSpanningCompactLieAlgebra
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KFourier MeasureTheory

namespace GlobalTheory.KSpan

def kSub {n : ℕ} (ε : Fin n → Bool) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | inK ε Y}
  add_mem' := by
    intro a b ha hb
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨?_, ?_⟩
    · unfold inG at *
      rw [conjTranspose_add, add_mul, mul_add]
      calc _ = (aᴴ * Jm ε + Jm ε * a) + (bᴴ * Jm ε + Jm ε * b) := by abel
        _ = 0 := by rw [ha1, hb1, add_zero]
    · rw [add_mul, mul_add, ha2, hb2]
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · simp [inG]
    · simp
  smul_mem' := by
    intro t Z hZ
    have h := inK_smul_real ε hZ t
    rwa [Complex.coe_smul] at h

theorem finite_real_span : ∀ {n : ℕ} (ε : Fin n → Bool), ∃ (r : ℕ) (X : Fin r → Mx n), (∀ j, inK ε (X j)) ∧ ∀ Y, inK ε Y → ∃ c : Fin r → ℝ, Y = ∑ j, (c j : ℂ) • X j := by
  intro n ε
  let b := Module.finBasis ℝ (kSub ε)
  refine ⟨Module.finrank ℝ (kSub ε), fun j => ((b j : kSub ε) : Matrix (Fin n) (Fin n) ℂ), fun j => (b j).2, ?_⟩
  intro Y hY
  refine ⟨fun j => b.repr ⟨Y, hY⟩ j, ?_⟩
  have h2 := congrArg Subtype.val (b.sum_repr ⟨Y, hY⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
  conv_lhs => rw [← h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.coe_smul]

end GlobalTheory.KSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsImagQuadraticHostStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_imag_quadratic_host : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R), ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K) (_ : IsTotallyComplex K), Module.finrank ℚ K = 2 ∧ discr K = -(H.d : ℤ) ∧ discr K < -4 ∧ K ≤ H.φ₀.toRatAlgHom.fieldRange ∧ (∀ z : ℂ, (∃ s : ℤ × ℤ, z = s.1 + s.2 * ((1 + H.φ₀ H.sqrtMinusD) / 2)) ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) ∧ Module.finrank ℚ H.E = 2 * R.f := by
  first | exact @GlobalTheory.FieldSize.exists_hostK | exact GlobalTheory.FieldSize.exists_hostK | (intros; apply GlobalTheory.FieldSize.exists_hostK <;> assumption)
end

