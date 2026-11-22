import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormDiagonalEntryDilationGeneratorLeOne
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0091
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0082
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0057
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0087
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0152
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0053
import Formalism.HermitianCurvature.StatementU
import Formalism.HermitianCurvature.StatementQ
import Formalism.HermitianCurvature.LetterProductDoubleDegreeCount
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0179
import Formalism.HermitianCurvature.Bundle0007
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0061
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0371
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0183

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSettingUniformConstant
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselNormSq

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsInner_sum_sum {m : ℕ} (A C : Fin m → (Wq →L[ℂ] Wp)) :
    B.hsInner (∑ i, A i) (∑ j, C j) = ∑ i, ∑ j, B.hsInner (A i) (C j) := by
  have h : ∀ A : Fin m → (Wq →L[ℂ] Wp), B.hsVec (∑ i, A i) = ∑ i, B.hsVec (A i) := by
    intro A
    ext t
    simp [B.hsVec, ContinuousLinearMap.sum_apply]
  unfold B.hsInner
  rw [h, h, inner_sum]
  exact Finset.sum_congr rfl fun i _ => sum_inner _ _ _

theorem Ph_sum [FiniteDimensional ℂ Wp] (D : B.RealPlaceData k r Wp Wq) {m : ℕ} (F : B.Mat k r → (Wq →L[ℂ] Wp))
    (f : Fin m → B.Mat k r → (Wq →L[ℂ] Wp)) (hF : ∀ g ∈ B.GV k r, F g = ∑ i, f i g) (p : B.SS k r)
    (hp : D.inSS p)
    (hint : ∀ i j, Integrable (fun g : Formalism.QuantumDeterminants.Mt k r =>
      B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g))) D.μG) :
    B.Ph D F F p = ∑ i, ∑ j, B.Ph D (f i) (f j) p := by
  have hae : ∀ᵐ g ∂D.μG, Matrix.of g ∈ B.GV k r := D.haarG.conc
  unfold B.Ph
  have e1 : ∀ i, ∑ j, ∫ g, B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g)) ∂D.μG =
      ∫ g, ∑ j, B.hsInner (B.rho D p (f i) (Matrix.of g)) (f j (Matrix.of g)) ∂D.μG :=
    fun i => (integral_finset_sum _ fun j _ => hint i j).symm
  simp only [e1]
  rw [← integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hint i j]
  refine integral_congr_ae (hae.mono fun g hg => ?_)
  have h1 : B.rho D p F (Matrix.of g) = ∑ i, B.rho D p (f i) (Matrix.of g) := by
    unfold B.rho
    rw [hF _ (Formalism.FourierDecayAlt.P.B6.conj_product_mem_unitary_group D hp hg)]
    ext v
    simp [ContinuousLinearMap.sum_apply]
  simp only
  rw [h1, hF _ hg, hsInner_sum_sum]

theorem normSq_coef : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq), ∃ c : ℝ, 0 < c ∧ ∀ (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (h : ℝ) (R : Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (dd : ℝ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → GapOK k r h → IsBeL R D.z D.π D.μW D.μN l → IsBeL R D.z' D.π' D.μW' D.μN l' → (∀ w, w ≠ 0 → PI.BesselPeriodGGP.fdegH D.μG R.σ w = dd) → ∀ F s, IsCoef R l l' F s → B.normSq D F = ENNReal.ofReal (c * ‖s‖ ^ 2 / dd) := by
  intro H k r Wp _ _ _ _ Wq _ _ _ _ D
  obtain ⟨c, hc, hnb⟩ := GlobalTheory.T.besselNormSq_eq_const_mul_archPairing k r Wp Wq D
  refine ⟨c, hc, ?_⟩
  intro ε mu h R l l' dd hDS hgap hok hl hl' hdd F s hF
  have hA := (GlobalTheory.T.decayThresholds_of_spectralGapCondition k r h hok).2.1
  have hcc := (GlobalTheory.T.smooth_and_inCC_of_isCoef_of_gap H k r ε mu h R Wp Wq l l' F s hDS hgap hok hF).2
  obtain ⟨m, x, y, X, hxy, hFg, hs⟩ := hF
  set f : Fin m → B.Mat k r → (Wq →L[ℂ] Wp) := fun i g => ⟪x i, R.σ g (y i)⟫_ℂ • X i with hf
  have hI := fun i j => GlobalTheory.T.bessel_formal_degree_pairing H k r ε mu h R Wp Wq D l l' dd hDS hgap hok hl hl' hdd
    (x i) (hxy i).1 (y i) (hxy i).2 (x j) (hxy j).1 (y j) (hxy j).2 (X i) (X j)
  have hPh : B.Ph D F F =ᵐ[D.μSS] fun p => ∑ i, ∑ j, B.Ph D (f i) (f j) p :=
    (Formalism.FourierDecayAlt.P.B6.ae_inSS D).mono fun p hp => Ph_sum D F f hFg p hp fun i j =>
      (GlobalTheory.T.bessel_formal_degree_identity H k r ε mu R Wp Wq D dd hDS hdd (x i) (y i) (x j) (y j) (X i) (X j) p hp).1
  have hint : Integrable (B.Ph D F F) D.μSS :=
    (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => (hI i j).1).congr hPh.symm
  have hxi : ∀ i j, Integrable (fun p => B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p) D.μSS := by
    intro i j
    refine Integrable.bdd_mul (c := 1) (hI i j).1 ?_ (Filter.Eventually.of_forall fun p => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have c1 : Continuous fun p : B.SS k r => B.lam k r D.z (Matrix.of p.1.2) :=
        (Formalism.FourierDecayAlt.P.B6.lam_continuous k r D.z).comp (continuous_snd.comp continuous_fst)
      have c2 : Continuous fun p : B.SS k r => B.lam k r D.z' (Matrix.of p.2.2) :=
        (Formalism.FourierDecayAlt.P.B6.lam_continuous k r D.z').comp (continuous_snd.comp continuous_snd)
      unfold B.xiTau
      exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
        ((continuous_const.mul c1).sub (continuous_const.mul c2))))
    · unfold B.xiTau
      rw [mul_comm, Complex.norm_exp_ofReal_mul_I]
  have hb : B.betaInf D F F = ((‖s‖ ^ 2 / dd : ℝ) : ℂ) := by
    rw [GlobalTheory.T.betaInf_eq_integral_of_integrable_coefficient k r Wp Wq D _ F hA (hcc 4) hint]
    have e0 : ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS =
        ∫ p, ∑ i, ∑ j, B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p ∂D.μSS := by
      refine integral_congr_ae (hPh.mono fun p hp => ?_)
      simp only [hp, Finset.mul_sum]
    rw [e0, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hxi i j]
    have e1 : ∀ i, ∫ p, ∑ j, B.xiTau D (1, 1) p * B.Ph D (f i) (f j) p ∂D.μSS =
        ∑ j, ⟪l (x i), X i (l' (y i))⟫_ℂ * star ⟪l (x j), X j (l' (y j))⟫_ℂ / (dd : ℂ) := by
      intro i
      rw [integral_finset_sum _ fun j _ => hxi i j]
      exact Finset.sum_congr rfl fun j _ => (hI i j).2
    simp only [e1]
    have e2 : ((‖s‖ ^ 2 / dd : ℝ) : ℂ) = s * star s / (dd : ℂ) := by
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    rw [e2, hs, star_sum, Finset.sum_mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_div]
  rw [hnb _ F hA (hcc 5), hb, ← Complex.ofReal_mul, Complex.ofReal_re, mul_div_assoc]

end GlobalTheory.BesselNormSq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliEigenSumLinearCombination
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Finset

namespace GlobalTheory

theorem capelli_eigenSum_linearCombination : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (lam : Fin (2 * r + k + 1) → ℝ) (d : ℕ) (A : ℝ) (ι : Type) (S : Finset ι) (co : ι → ℂ) (Fs : ι → B.Mat k r → (Wq →L[ℂ] Wp)) (F : B.Mat k r → (Wq →L[ℂ] Wp)), (∀ x ∈ S, ∃ (d' : ℕ) (A' : ℝ), d' ≤ d ∧ A ≤ A' ∧ (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d' : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A') m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (Fs x) g = ∑ i, Fi i g)) → (∀ g ∈ B.GV k r, F g = ∑ x ∈ S, co x • Fs x g) → (∃ (N₀ : ℕ) (Fi : Fin N₀ → B.Mat k r → (Wq →L[ℂ] Wp)) (ν : Fin N₀ → Fin (2 * r + k + 1) → ℤ), (∀ i s, |ν i s| ≤ ((d : ℕ) : ℤ)) ∧ (∀ i, (B.CkOn ⊤ (B.GV k r) (Fi i) ∧ ∀ m : ℕ, B.InCC (A) m (Fi i))) ∧ (∀ i, (∀ Y : ℝ, ∀ g ∈ B.GV k r, Q.CV k r (Y : ℂ) (Fi i) g = ((∏ s, (Y + lam s + (ν i s : ℝ)) : ℝ) : ℂ) • (Fi i) g)) ∧ ∀ g ∈ B.GV k r, (F) g = ∑ i, Fi i g) := by
  intro k r Wp Wq _ _ _ _ _ _ lam d A ι S co Fs F h hF
  classical
  have h' : ∀ x : S, _ := fun x => h x.1 x.2
  choose d' A' hd hA N Fi ν hν hC hE hS using h'
  let e := (Fintype.equivFin (Σ x : S, Fin (N x))).symm
  refine ⟨_, fun j g => co (e j).1 • Fi (e j).1 (e j).2 g, fun j => ν (e j).1 (e j).2, ?_, ?_, ?_, ?_⟩
  · intro j s
    exact (hν _ _ s).trans (by exact_mod_cast hd _)
  · intro j
    refine ⟨Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_smul _ (hC _ _).1, fun m => ?_⟩
    obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.BetaSesquilinearity.sInCC_mono (hA (e j).1) le_rfl ((hC _ (e j).2).2 m)
    exact ⟨_, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_smul _ hc⟩
  · intro j Y g hg
    have h1 := Formalism.FourierDecayAlt.P.CutMP.En.cV_smul (k := k) (r := r) (Y : ℂ) (co (e j).1) (Fi (e j).1 (e j).2)
    have h2 := congrFun h1 g
    have h3 : (fun g => co (e j).1 • Fi (e j).1 (e j).2 g) = co (e j).1 • Fi (e j).1 (e j).2 := rfl
    beta_reduce
    rw [h3, h2, Pi.smul_apply, hE _ _ Y g hg, smul_comm]
  · intro g hg
    rw [hF g hg, Equiv.sum_comp e (fun y : (Σ x : S, Fin (N x)) => co y.1 • Fi y.1 y.2 g),
      Fintype.sum_sigma, ← Finset.sum_coe_sort S]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hS x g hg, Finset.smul_sum]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingNormLe
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_capelliFold_norm_le : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∃ C : ℝ, 0 ≤ C ∧ ∀ (X Z : B.Mat k r → (Wq →L[ℂ] Wp)) (c c' : ℝ), B.CkOn ⊤ (B.GV k r) X → B.CCle A (5 + w.length * (2 * r + k + 1)) X c → B.CCle A 5 Z c' → ‖B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z‖ ≤ C * c * c' := by
  intro k r Wp Wq _ _ _ _ _ _ Bs s w A hA
  obtain ⟨_, _, _, ⟨C, hC⟩, _⟩ := Formalism.FourierDecayAlt.P.b_any_of_xi k r Wp Wq Bs A hA
  obtain ⟨K, hK0, hK⟩ := GlobalTheory.T.capelliWordProduct_decayBound_uniform k r Wp Wq s w 5
  refine ⟨|C| * K, mul_nonneg (abs_nonneg _) hK0, ?_⟩
  intro X Z c c' hX hc hc'
  have hc0 : 0 ≤ c := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc
  have hc0' : 0 ≤ c' := Formalism.FourierDecayAlt.P.JCx2.pd_ccle_nonneg hc'
  have hF := hK A c X hX hc
  have h := (hC _ _ _ _ ⟨_, hF⟩ ⟨_, hc'⟩ (Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (by norm_num) hF)
    (Formalism.FourierDecayAlt.P.JCx2.pd_ccle_mono le_rfl (by norm_num) hc')).2.2
  refine h.trans ?_
  rw [mul_assoc |C| K c]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (le_abs_self _) (mul_nonneg hK0 hc0)) hc0'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CapelliProductLevelZeroPairingSesquilinear
section
open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory

namespace GlobalTheory

theorem beta_foldCapelli_sesquilinear : ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (s : ℂ) (w : List (Bool × ℝ)) (A : ℝ), B.AB k r ≤ A → ∀ (a : ℂ) (X X' Z Z' : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) X → B.CkOn ⊤ (B.GV k r) X' → B.InCC A (5 + w.length * (2 * r + k + 1)) X → B.InCC A (5 + w.length * (2 * r + k + 1)) X' → B.InCC A 5 Z → B.InCC A 5 Z' → B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X + a • X') w) Z = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X') w) Z ∧ B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) (Z + a • Z') = B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z + (starRingEnd ℂ) a * B.beta Bs (List.foldr (fun (a : Bool × ℝ) G => s • Q.CV k r (a.2 : ℂ) G) (X) w) Z' := by
  intro k r Wp Wq _ _ _ _ _ _ Bs s w A hA a X X' Z Z' hX hX' hXc hX'c hZ hZ'
  obtain ⟨K, -, hK⟩ := GlobalTheory.T.capelliWordProduct_decayBound_uniform k r Wp Wq s w 5
  obtain ⟨c, hc⟩ := hXc
  obtain ⟨c', hc'⟩ := hX'c
  have h1 : B.InCC A 5 _ := ⟨_, hK A c X hX hc⟩
  have h2 : B.InCC A 5 _ := ⟨_, hK A c' X' hX' hc'⟩
  refine ⟨?_, (Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq Bs hA hZ hZ' h1 a).2⟩
  rw [← (Formalism.FourierDecayAlt.P.JCx2.sq_beta_sesq Bs hA h1 h2 hZ a).1]
  exact Formalism.FourierDecayAlt.P.JCx2.sq_beta_congr Bs (fun g hg => GlobalTheory.capelliFold_add_smul k r Wp Wq s w a X X' hX hX' g hg)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DecLowAndKFinDecayOfGapOfDecAll
section
namespace GlobalTheory.DecTransport

open Matrix Finset Formalism.FourierDecayAlt.ThreeDimData in
open scoped InnerProductSpace in

lemma decE_le {q : ℕ} (hq : 1 ≤ q) {h d : ℝ} (hh : 0 ≤ h) (hd : 0 ≤ d) :
    GlobalTheory.Count.decE q h d ≤ Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt q)) * d) := by
  unfold GlobalTheory.Count.decE
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hs : 1 ≤ Real.sqrt (q : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hq)

  have key : d / Real.sqrt q - min (2 * d ^ 2) (d / Real.sqrt q) ≤ 1 := by
    rcases le_total (2 * d ^ 2) (d / Real.sqrt q) with hm | hm
    · rw [min_eq_left hm]
      have : d / Real.sqrt q ≤ d := div_le_self hd hs
      nlinarith [sq_nonneg (d - 1 / 4)]
    · rw [min_eq_right hm]; linarith
  have e : -(h / (8 * Real.sqrt q)) * d = -(h / 8) * (d / Real.sqrt q) := by ring
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left key (by positivity : (0 : ℝ) ≤ h / 8)]

private lemma inv_mul_and_mul_inv_of_isCayleyU {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hP : PI.UpqRep.IsCayleyU k r ε P) :
    P⁻¹ * P = 1 ∧ P * P⁻¹ = 1 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).mp hP.1.1
  exact ⟨Matrix.nonsing_inv_mul P hd, Matrix.mul_nonsing_inv P hd⟩

private lemma conjTranspose_mem_Kset' {k r : ℕ} {ε : Fin (2 * r + k + 1) → Bool}
    {P Q : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hP : PI.UpqRep.IsCayleyU k r ε P) (hQ : PI.UpqRep.IsCayleyU k r ε Q) :
    P * Q⁻¹ ∈ PI.UpqRep.UJset ε := by
  obtain ⟨⟨-, hPJ⟩, -⟩ := hP
  obtain ⟨⟨-, hQJ⟩, hQu⟩ := hQ
  have hQi : Q⁻¹ = Q.conjTranspose := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hQu)
  have hQQ : Q * Q.conjTranspose = 1 := by
    rw [← Matrix.star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff.mp hQu
  show (P * Q⁻¹).conjTranspose * PI.UpqRep.Jm ε * (P * Q⁻¹) = PI.UpqRep.Jm ε
  rw [hQi, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc Q * P.conjTranspose * PI.UpqRep.Jm ε * (P * Q.conjTranspose)
        = Q * (P.conjTranspose * PI.UpqRep.Jm ε * P) * Q.conjTranspose := by
        simp only [Matrix.mul_assoc]
    _ = Q * (Q.conjTranspose * PI.UpqRep.Jm ε * Q) * Q.conjTranspose := by rw [hPJ, hQJ]
    _ = (Q * Q.conjTranspose) * PI.UpqRep.Jm ε * (Q * Q.conjTranspose) := by simp only [Matrix.mul_assoc]
    _ = PI.UpqRep.Jm ε := by rw [hQQ, Matrix.one_mul, Matrix.mul_one]

private lemma rpow_three_div_two_eq_mul_sqrt {x : ℝ} (hx : 0 ≤ x) : x ^ ((3 : ℝ) / 2) = x * Real.sqrt x := by
  rw [show ((3 : ℝ) / 2) = 1 + 1 / 2 by norm_num, Real.rpow_one_add' hx (by norm_num), Real.sqrt_eq_rpow]

open Matrix Finset GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.SideNormalisedGap Formalism.FourierDecayAlt.B in
open scoped InnerProductSpace in

theorem decLow_of_decGap (hA : GlobalTheory.DSId.DecGap) : Formalism.FourierDecayAlt.ThreeDimData.DecLow := by
  intro k r hk ε lam h H _ _ _ σ hl hσ hg h120 P hP w₁ w₂ h₁ h₂
  have hh : 0 ≤ h := by
    have : (0 : ℝ) ≤ 120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3 := by positivity
    linarith
  have hPu : P ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := hP.2
  have hPi : P⁻¹ = star P := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hPu)
  have hPP := inv_mul_and_mul_inv_of_isCayleyU hP

  obtain ⟨P0, hP0, hDS0⟩ := hσ
  have hP0P := inv_mul_and_mul_inv_of_isCayleyU hP0
  have hDS : PI.UpqRep.IsDS ε lam (fun g => σ (P⁻¹ * g * P)) := by
    have h0 := GlobalTheory.CayleyChoice.isDS_conj hDS0 (conjTranspose_mem_Kset' hP hP0) (conjTranspose_mem_Kset' hP0 hP)
      (by
        calc P * P0⁻¹ * (P0 * P⁻¹) = P * (P0⁻¹ * P0) * P⁻¹ := by simp only [Matrix.mul_assoc]
          _ = 1 := by rw [hP0P.1, Matrix.mul_one, hPP.2])
    have hfun : (fun g => σ (P⁻¹ * g * P)) =
        (fun g => σ (P0⁻¹ * (P0 * P⁻¹ * g * (P * P0⁻¹)) * P0)) := by
      funext g
      congr 1
      calc P⁻¹ * g * P = (P0⁻¹ * P0) * (P⁻¹ * g * P) * (P0⁻¹ * P0) := by
            rw [hP0P.1, Matrix.one_mul, Matrix.mul_one]
        _ = P0⁻¹ * (P0 * P⁻¹ * g * (P * P0⁻¹)) * P0 := by simp only [Matrix.mul_assoc]
    rw [hfun]
    exact h0

  have hq : rkR ε = r + 1 := rkR_eq hk hP
  have hgap : 120 * ((2 * r + k + 1 : ℕ) : ℝ) * ((rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [hq]
    have h1 := GlobalTheory.GapSizeCheck.decay_range k r h h120
    have e : (((r + 1 : ℕ) : ℝ)) ^ ((3 : ℝ) / 2) = ((r : ℝ) + 1) * Real.sqrt ((r : ℝ) + 1) := by
      push_cast
      exact rpow_three_div_two_eq_mul_sqrt (by positivity)
    rw [e]
    exact h1

  have ha : 0 ≤ h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))) := by positivity
  have hab : h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))) ≤ h / (8 * Real.sqrt ((r : ℝ) + 1)) := by
    apply div_le_div_of_nonneg_left hh (by positivity)
    have : (0 : ℝ) ≤ r := r.cast_nonneg
    gcongr
    linarith
  refine ⟨Real.exp (h / 8) * Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
    ‖w₁‖ * ‖w₂‖, fun x hx => ?_⟩

  have ex : P⁻¹ * (P * x * P⁻¹) * P = x := by
    calc P⁻¹ * (P * x * P⁻¹) * P = (P⁻¹ * P) * x * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = x := by rw [hPP.1, Matrix.one_mul, Matrix.mul_one]
  have hgU : P * x * P⁻¹ ∈ PI.UpqRep.UJset ε :=
    (GlobalTheory.UnitaryCayley.transport hP (P * x * P⁻¹)).1.mp (by rw [ex]; exact hx)
  have hb : ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ decE (r + 1) h (dOp (P * x * P⁻¹)) * ‖w₁‖ * ‖w₂‖ := by
    have h0 := (hA _ ε lam H (fun g => σ (P⁻¹ * g * P)) hl hDS h hg hgap (P * x * P⁻¹) hgU w₁ h₁ w₂ h₂).2
    rw [hq] at h0
    simpa only [ex] using h0
  have hd : 0 ≤ dOp (P * x * P⁻¹) := ((GlobalTheory.Dec.dFacts_holds _ ε).1 _ hgU).1
  have hdecE : decE (r + 1) h (dOp (P * x * P⁻¹)) ≤
      Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹)) := by
    have h0 := decE_le (q := r + 1) (by omega) hh hd
    push_cast at h0
    exact h0

  have hcl : Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ) (P * x * P⁻¹) =
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹)) := by
    first
      | rfl
      | (apply ContinuousLinearMap.coe_injective; simp [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin])
  have hGN : gN x ≤ Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) *
      ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ := by
    have h1 := hs_le_op x
    have h2 : ‖Matrix.toEuclideanCLM (n := Fin (2 * r + k + 1)) (𝕜 := ℂ) x‖ =
        ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ := by
      rw [← hcl, ← op_conj hPu x, hPi]
    rw [h2] at h1
    show Real.sqrt (∑ i, ∑ j, Complex.normSq (x i j)) ≤ _
    calc Real.sqrt (∑ i, ∑ j, Complex.normSq (x i j))
        ≤ Real.sqrt (((2 * r + k + 1 : ℕ) : ℝ) *
            ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (P * x * P⁻¹))‖ ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = _ := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]
  have hE : Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹)) ≤
      Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
        gN x ^ (-(h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))) :=
    exp_le_rpow ha hab (by positivity) hd (gN_pos hx) hGN
  calc ‖⟪w₂, σ x w₁⟫_ℂ‖ ≤ decE (r + 1) h (dOp (P * x * P⁻¹)) * ‖w₁‖ * ‖w₂‖ := hb
    _ ≤ (Real.exp (h / 8) * Real.exp (-(h / (8 * Real.sqrt ((r : ℝ) + 1))) * dOp (P * x * P⁻¹))) *
          ‖w₁‖ * ‖w₂‖ := by gcongr
    _ ≤ (Real.exp (h / 8) * (Real.sqrt ((2 * r + k + 1 : ℕ) : ℝ) ^ (h / (8 * Real.sqrt (2 * ((r : ℝ) + 1)))) *
          gN x ^ (-(h / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))))) * ‖w₁‖ * ‖w₂‖ := by gcongr
    _ = _ := by ring

theorem decLow_holds : Formalism.FourierDecayAlt.ThreeDimData.DecLow :=
  decLow_of_decGap GlobalTheory.Deep.ptBound_and_farBound_and_decGap.2.2

end GlobalTheory.DecTransport
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormActualOperatorsAlgebraicHypothesesStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalForm_actualOperators_algebraicHypotheses : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → HatHyp d ∧ Comparison₂ d L st (M.sgn P l0) := by
  first | exact @GlobalTheory.HatNF.hatHyp_and_tie_of_isNF | exact GlobalTheory.HatNF.hatHyp_and_tie_of_isNF | (intros; apply GlobalTheory.HatNF.hatHyp_and_tie_of_isNF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.QuantumMinorSumPolynomialOperator
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
open scoped ComplexConjugate

namespace GlobalTheory.HatNF.MinorPoly

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem qminor_words (k r m : ℕ) (a b : Fin m → Fin (2 * r + k + 1)) (u : ℂ) :
    ∃ L : List (ℂ × List (B.Mat k r)),
    (∀ cw ∈ L, (∀ X ∈ cw.2, B.inLie k r X) ∧ cw.2.length ≤ m) ∧
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (UU : Set (B.Mat k r)) (f : B.Mat k r → E),
      B.CkOn ⊤ UU f → ∀ g ∈ UU, g ∈ B.GV k r →
        qminorOp (EabH (Hpk k r)) a b u f g = (L.map fun cw => cw.1 • B.Rw cw.2 f g).sum := by
  let ts : Equiv.Perm (Fin m) → List (ℂ × Fin (2 * r + k + 1) × Fin (2 * r + k + 1)) :=
    fun σ => List.ofFn fun j : Fin m => (u - ((j : ℕ) : ℂ), a (σ j), b j)
  refine ⟨(Finset.univ : Finset (Equiv.Perm (Fin m))).toList.flatMap
      (fun σ => (Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand k r (ts σ)).map
        fun cw => (((Equiv.Perm.sign σ : ℤ) : ℂ) * cw.1, cw.2)), ?_, ?_⟩
  · intro cw hcw
    simp only [List.mem_flatMap, List.mem_map] at hcw
    obtain ⟨σ, _, cw', hm', rfl⟩ := hcw
    have := Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_words (k := k) (r := r) (ts σ) cw' hm'
    refine ⟨fun X hX => (this.1 X hX).1, this.2.trans ?_⟩
    simp [ts]
  · intro E _ _ UU f hf g hgU hg
    have hloc : ∀ σ, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.Loc ((ts σ).length : ℕ∞) f g := fun σ =>
      Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.loc_mono le_top (hf g hgU)
    have e1 : qminorOp (EabH (Hpk k r)) a b u f g =
        ∑ σ, (((Equiv.Perm.sign σ : ℤ) : ℂ)) • Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT (ts σ) f g := by
      simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]
      refine Finset.sum_congr rfl (fun σ _ => ?_)
      congr 1
      simp only [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.foldT, ts, List.map_ofFn]
      rfl
    rw [e1, Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.expand_eq (ts σ) f g hg (hloc σ), List.map_map,
      ← Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_map_mul_smul]
    rfl

section terms

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def scalarTerm (P : B.Mat k r → ℂ) (w : List (B.Mat k r)) (hw : ∀ X ∈ w, B.inLie k r X) : B.DTerm k r Wp Wq where
  coef := fun g => P g • ContinuousLinearMap.id ℂ _
  coefAdj := fun g => star (P g) • ContinuousLinearMap.id ℂ _
  word := w
  word_lie := hw
  adj_id := by
    intro x A B'
    simp only [_root_.smul_apply, ContinuousLinearMap.id_apply]
    rw [Formalism.FourierDecayAlt.P5.HerB.hs_smul_left, Formalism.FourierDecayAlt.P5.HerB.hs_smul_right]
    simp

theorem isPolyDeg_mul_const {N κ : ℕ} {P : Matrix (Fin N) (Fin N) ℂ → ℂ} (h : U.IsPolyDeg κ P) (c : ℂ) :
    U.IsPolyDeg κ fun g => P g * c := by
  obtain ⟨q, hq, he⟩ := h
  refine ⟨q * MvPolynomial.C c, ?_, fun g => by simp [he g]⟩
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simpa using hq

theorem exists_polyOp_words (m κ : ℕ) (P : B.Mat k r → ℂ) (hP : U.IsPolyDeg κ P)
    (L : List (ℂ × List (B.Mat k r))) (hL : ∀ cw ∈ L, (∀ X ∈ cw.2, B.inLie k r X) ∧ cw.2.length ≤ m) :
    ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F g,
      B.opApply Θ F g = P g • (L.map fun cw => cw.1 • B.Rw cw.2 F g).sum := by
  induction L with
  | nil => exact ⟨[], fun T hT => by simp at hT, fun F g => by simp [B.opApply]⟩
  | cons cw L ih =>
    obtain ⟨Θ, hΘ, he⟩ := ih fun cw' h => hL cw' (List.mem_cons_of_mem _ h)
    have h0 := hL cw List.mem_cons_self
    refine ⟨scalarTerm (fun g => P g * cw.1) cw.2 h0.1 :: Θ, ?_, fun F g => ?_⟩
    · intro T hT
      rcases List.mem_cons.1 hT with rfl | hT
      · exact ⟨h0.2, fun g => P g * cw.1, isPolyDeg_mul_const hP _, fun _ => rfl, fun _ => rfl⟩
      · exact hΘ T hT
    · have h1 := he F g
      simp only [B.opApply, List.map_cons, List.sum_cons] at h1 ⊢
      rw [h1, smul_add, smul_smul]
      rfl

end terms

theorem minor_polyOp : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r m κ : ℕ) (ι : Type) [Fintype ι] (a b : ι → Fin m → Fin (2 * r + k + 1)) (u : ℂ) (co : ι → B.Mat k r → ℂ), (∀ i, U.IsPolyDeg κ (co i)) → ∃ Θ : B.DiffOp k r Wp Wq, Formalism.FourierDecayAlt.P.CutMP.PolyOp m κ Θ ∧ ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), ∀ g ∈ B.GV k r, ∀ V : Set (B.Mat k r), IsOpen V → g ∈ V → B.CkOn ⊤ (B.GV k r ∩ V) F → B.opApply Θ F g = ∑ i, co i g • qminorOp (EabH (Hpk k r)) (a i) (b i) u F g := by
  intro Wp Wq _ _ _ _ _ _ k r m κ ι _ a b u co hco
  choose L hL hE using fun i => qminor_words k r m (a i) (b i) u
  choose Θ hΘ hA using fun i => exists_polyOp_words (Wp := Wp) (Wq := Wq) m κ (co i) (hco i) (L i) (hL i)
  refine ⟨(Finset.univ : Finset ι).toList.flatMap Θ, ?_, ?_⟩
  · intro T hT
    obtain ⟨i, _, hi⟩ := List.mem_flatMap.1 hT
    exact hΘ i T hi
  · intro F g hg V _ hgV hF
    unfold B.opApply
    rw [Formalism.FourierDecayAlt.P.CapelliWordSumExpansion.sum_flatMap, Finset.sum_map_toList]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hE i _ _ F hF g ⟨hg, hgV⟩ hg, ← hA i F g]
    rfl

end

end GlobalTheory.HatNF.MinorPoly
end

