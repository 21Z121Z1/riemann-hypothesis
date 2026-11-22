import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0015
import Formalism.SharpRestriction.CuspSpanNormBounds.AbsoluteAmplitudeSecondOfSource
import Formalism.SharpRestriction.CuspSpanNormBounds.PExtra
import Formalism.SharpRestriction.CuspSpanNormBounds.AmplitudeAndVolumeBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.BranchingAndRankConstants
import Formalism.SharpRestriction.CuspSpanNormBounds.MassAndBranchingHypotheses
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Statements.DiscreteSeriesShifts.ThmBpDS
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPlacesEqTrace
import Mathlib
import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0316
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0338
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0308
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0311
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.FamDefs
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0026
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.StepAnalyticConstantsP

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.JEqOrbInt
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.AmpTK

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S BranchingSupport GlobalTheory.CellAmp

variable {k r : ℕ}

def rep (L : LocBessel k r) : BranchingSupport.Rep k r := ⟨L.Hs, L.σ⟩

def BeTK (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq) : Prop :=
  (∀ x ∈ (rep L).sm, ∀ v ∈ (rep L).TK,
    Formalism.FourierDecayAlt.ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN x v = (innerSL ℂ (l v)).smulRight (l x)) ∧
  (∀ x ∈ (rep L).sm, ∀ v ∈ (rep L).TK,
    Formalism.FourierDecayAlt.ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN x v = (innerSL ℂ (l' v)).smulRight (l' x))

def SmCW (L : LocBessel k r) {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (l : L.Hs → V) : Prop :=
  (∀ v ∈ (rep L).sm, ∀ w ∈ (rep L).sm, l (v + w) = l v + l w) ∧ (∀ (a : ℂ), ∀ v ∈ (rep L).sm, l (a • v) = a • l v) ∧
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) L.σ l

def OneAt (L : LocBessel k r) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (ν : Measure (PairSp k r)) : Prop :=
  ∃ A : L.Wq →L[ℂ] L.Wp, ∀ F s, IsCoef (rep L) l l' F s → OrbInt L F g ν = s • A

theorem J_eq_orbInt (L : LocBessel k r)
    (F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : L.J F g = OrbInt L F g (pairMeas L) := rfl

end GlobalTheory.AmpTK
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocInOfUniqOfDecLow
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.LocalInputs

theorem hpk_det (k r : ℕ) : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem urep_of_ds {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (h : IsDSHpk k r ε lam σ) : IsURepOn (GG k r) σ := by
  obtain ⟨P, ⟨⟨hP, hH⟩, -⟩, -, -, ⟨⟨h1, hm⟩, hn, hc⟩, -⟩ := h
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hiP : P⁻¹ * P = 1 := nonsing_inv_mul _ hd
  have mem : ∀ g, g ∈ GG k r ↔ P * g * P⁻¹ ∈ UJset ε := uHConj _ ε _ P hd hH
  have back : ∀ g : Mat k r, P⁻¹ * (P * g * P⁻¹) * P = g := fun g => by
    calc P⁻¹ * (P * g * P⁻¹) * P = (P⁻¹ * P) * g * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = g := by rw [hiP]; simp
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · simpa [hiP] using h1
  · intro a ha b hb
    have := hm _ ((mem a).1 ha) _ ((mem b).1 hb)
    have e : P * a * P⁻¹ * (P * b * P⁻¹) = P * (a * b) * P⁻¹ := by
      calc P * a * P⁻¹ * (P * b * P⁻¹) = P * a * (P⁻¹ * P) * b * P⁻¹ := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [hiP]; simp only [Matrix.mul_assoc, Matrix.one_mul]
    simpa only [e, back] using this
  · intro g hg v
    have := hn _ ((mem g).1 hg) v
    simpa only [back] using this
  · intro v
    have hcont : Continuous fun g : Mat k r => P * g * P⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := (hc v).comp hcont.continuousOn (s := GG k r) (fun g hg => (mem g).1 hg)
    refine this.congr fun g _ => ?_
    simp only [Function.comp, back]

theorem opn_pos {k r : ℕ} {g : Mat k r} (hg : g ∈ GG k r) : 0 < opn g := by
  have hu := ((uHGroup _ _ (hpk_det k r)).2.2 g hg).1
  have h := opn_mul_le g⁻¹ g
  rw [nonsing_inv_mul _ hu, opn_one] at h
  rcases (opn_nonneg g).lt_or_eq with h0 | h0
  · exact h0
  · rw [← h0] at h; linarith

theorem coef_translate {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} (hσ : IsURepOn (GG k r) σ) {a b g : Mat k r} (ha : a ∈ GG k r)
    (hb : b ∈ GG k r) (hg : g ∈ GG k r) (u v : H) :
    coef σ (σ a u) (σ b v) g = coef σ u v (b⁻¹ * g * a) := by
  obtain ⟨-, hmul, hinv⟩ := uHGroup _ _ (hpk_det k r)
  have hx : b⁻¹ * g * a ∈ GG k r := hmul _ (hmul _ (hinv b hb).2 _ hg) _ ha
  have e : g * a = b * (b⁻¹ * g * a) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (hinv b hb).1, Matrix.one_mul]
  have e2 : σ g (σ a u) = σ b (σ (b⁻¹ * g * a) u) := by
    have h1 := hσ.1.2 g hg a ha
    have h2 := hσ.1.2 b hb _ hx
    rw [← e, h1] at h2
    exact congrArg (fun T : H →L[ℂ] H => T u) h2
  unfold coef
  rw [e2]
  exact (LinearIsometry.mk (σ b : H →ₗ[ℂ] H) (hσ.2.1 b hb)).inner_map_map v _

theorem decay_span {k r : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {σ : Mat k r → (H →L[ℂ] H)} {V : Set H} {a : ℝ} (ha : 0 ≤ a) (hσ : IsURepOn (GG k r) σ) (hV : Decay σ V a) :
    Decay σ (Submodule.span ℂ {v | ∃ g ∈ GG k r, ∃ u ∈ V, v = σ g u} : Submodule ℂ H) a := by
  obtain ⟨-, hmul, hinv⟩ := uHGroup _ _ (hpk_det k r)
  intro u hu v hv
  refine Submodule.span_induction₂ (p := fun u v _ _ => ∃ C : ℝ, ∀ g ∈ GG k r, ‖coef σ u v g‖ ≤ C * opn g ^ (-a))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hu hv
  · rintro _ _ ⟨x, hx, u, hu, rfl⟩ ⟨y, hy, v, hv, rfl⟩
    obtain ⟨C, hC⟩ := hV u hu v hv
    have hK : 0 < opn y * opn x⁻¹ := mul_pos (opn_pos hy) (opn_pos (hinv x hx).2)
    refine ⟨|C| * (opn y * opn x⁻¹) ^ a, fun g hg => ?_⟩
    have hm : y⁻¹ * g * x ∈ GG k r := hmul _ (hmul _ (hinv y hy).2 _ hg) _ hx
    rw [coef_translate hσ hx hy hg]
    have e : g = y * (y⁻¹ * g * x) * x⁻¹ := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, mul_nonsing_inv _ (hinv y hy).1, Matrix.one_mul,
        Matrix.mul_assoc, mul_nonsing_inv _ (hinv x hx).1, Matrix.mul_one]
    have h1 : opn g ≤ opn y * opn x⁻¹ * opn (y⁻¹ * g * x) := by
      calc opn g = opn (y * (y⁻¹ * g * x) * x⁻¹) := by rw [← e]
        _ ≤ opn (y * (y⁻¹ * g * x)) * opn x⁻¹ := opn_mul_le _ _
        _ ≤ opn y * opn (y⁻¹ * g * x) * opn x⁻¹ :=
          mul_le_mul_of_nonneg_right (opn_mul_le _ _) (opn_nonneg _)
        _ = _ := by ring
    have h2 := Real.rpow_le_rpow_of_nonpos (opn_pos hg) h1 (neg_nonpos.2 ha)
    rw [Real.mul_rpow hK.le (opn_nonneg _)] at h2
    have hp := opn_pos hm
    calc _ ≤ |C| * opn (y⁻¹ * g * x) ^ (-a) :=
          (hC _ hm).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
      _ = |C| * (opn y * opn x⁻¹) ^ a * ((opn y * opn x⁻¹) ^ (-a) * opn (y⁻¹ * g * x) ^ (-a)) := by
          rw [mul_assoc |C|, ← mul_assoc (_ ^ a), ← Real.rpow_add hK]; simp
      _ ≤ _ := by gcongr
  · exact fun y _ => ⟨0, fun g _ => by simp [coef]⟩
  · exact fun y _ => ⟨0, fun g _ => by simp [coef]⟩
  · rintro x y z - - - ⟨C, hC⟩ ⟨C', hC'⟩
    refine ⟨C + C', fun g hg => ?_⟩
    rw [coef_add_left, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC g hg) (hC' g hg))
  · rintro x y z - - - ⟨C, hC⟩ ⟨C', hC'⟩
    refine ⟨C + C', fun g hg => ?_⟩
    rw [coef_add_right, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hC g hg) (hC' g hg))
  · rintro c x y - - ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [coef_smul_left, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg _)
  · rintro c x y - - ⟨C, hC⟩
    refine ⟨‖c‖ * C, fun g hg => ?_⟩
    rw [coef_smul_right, norm_mul, norm_star, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC g hg) (norm_nonneg _)

theorem gap_of_nodes (D : D7) (τ : D.what₂.Tau) (h : ℝ) (hanti : StrictAnti (lamD D τ))
    (hb : ∀ j, 1 ≤ j → j + 1 ≤ D.R.m → h ≤ bOne D τ (j + 1) - bOne D τ j) :
    GapAtLeast (epsSH D.R) (lamD D τ) h := by
  have hd := dimS_eq D.R
  have hm := D.R.m_add_three_le_k
  have hr : D.R.r = D.R.k + D.R.m - 1 := rfl
  have step : ∀ (i : ℕ) (hi : i + 1 < 2 * D.R.rS + D.R.k + 1), D.R.k - 1 ≤ i →
      h ≤ lamD D τ ⟨i, by omega⟩ - lamD D τ ⟨i + 1, hi⟩ := by
    intro i hi hk
    have h0 := hb (i - (D.R.k - 1) + 1) (by omega) (by omega)
    unfold bOne at h0
    rw [dif_pos (by omega), dif_pos (by omega)] at h0
    unfold lamD lamSH lamS
    simp only [Fin.val_cast]
    rw [dif_neg (by omega), dif_pos (by omega), dif_neg (by omega), dif_pos (by omega)]
    have e : i + 1 - (D.R.k - 1) = i - (D.R.k - 1) + 1 := by omega
    simp only [e, Nat.add_sub_cancel] at h0 ⊢
    linarith
  have key : ∀ a b : Fin (2 * D.R.rS + D.R.k + 1), a < b → epsSH D.R a ≠ epsSH D.R b →
      h ≤ lamD D τ a - lamD D τ b := by
    intro a b hab hne
    have hab' : a.val < b.val := hab
    have hb' := b.isLt
    by_cases ha : D.R.k - 1 ≤ a.val
    · have h1 := step a.val (by omega) ha
      have h2 := hanti.antitone (show (⟨a.val + 1, by omega⟩ : Fin _) ≤ b from hab')
      simp only [Fin.eta] at h1
      linarith
    · have hbk : D.R.k ≤ b.val := by
        by_contra hc
        apply hne
        unfold epsSH epsS
        simp only [Fin.val_cast]
        rw [if_pos (by omega)]
        split_ifs
        · rfl
        · have : b.val - (D.R.k - 1) = 0 := by omega
          simp [this]
      have h1 := step (b.val - 1) (by omega) (by omega)
      have h2 := hanti.antitone (show a ≤ (⟨b.val - 1, by omega⟩ : Fin _) from by
        show a.val ≤ b.val - 1; omega)
      have e : (⟨b.val - 1 + 1, by omega⟩ : Fin (2 * D.R.rS + D.R.k + 1)) = b := Fin.ext (by simp only; omega)
      rw [e] at h1
      linarith
  intro a b hne
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact (key a b h1 hne).trans (le_abs_self _)
  · exact absurd (by rw [h1]) hne
  · rw [abs_sub_comm]; exact (key b a h1 hne.symm).trans (le_abs_self _)

theorem decay_low (hD : Formalism.FourierDecayAlt.ThreeDimData.DecLow) {k r : ℕ} (hk : 1 ≤ k) {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    {ε : Fin (2 * r + k + 1) → Bool} {lam : Fin (2 * r + k + 1) → ℝ} {σ : Mat k r → (H →L[ℂ] H)}
    (hl : IsHCParam lam) (hσ : IsDSHpk k r ε lam σ) (hg : GapAtLeast ε lam (((2 * r + k + 1 : ℕ) : ℝ) ^ 19))
    {P : Mat k r} (hP : IsCayleyU k r ε P) :
    Decay σ (lowKSub ε lam (fun g => σ (P⁻¹ * g * P))) (2 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 5) := by
  intro u hu v hv
  set n : ℝ := ((2 * r + k + 1 : ℕ) : ℝ) with hn
  have hr : 2 * ((r : ℝ) + 1) ≤ n := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    rw [hn]; push_cast; linarith
  have hn2 : 2 ≤ n := by have : (0 : ℝ) ≤ r := by positivity
                         linarith
  have h13 : (120 : ℝ) ≤ n ^ 13 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn2 13)
  have h16 : (120 : ℝ) ≤ n ^ 16 := le_trans (by norm_num) (pow_le_pow_left₀ (by norm_num) hn2 16)
  have hh : 120 * n ^ 3 ≤ n ^ 19 := by
    have : n ^ 19 = n ^ 16 * n ^ 3 := by ring
    rw [this]; gcongr
  obtain ⟨C, hC⟩ := hD k r hk ε lam (n ^ 19) H σ hl hσ hg hh P hP u v hu hv
  have hs : Real.sqrt (2 * ((r : ℝ) + 1)) ≤ n := Real.sqrt_le_iff.2 ⟨by linarith, by nlinarith⟩
  have hs0 : 0 < Real.sqrt (2 * ((r : ℝ) + 1)) := by positivity
  have he : 2 * n ^ 5 ≤ n ^ 19 / (8 * Real.sqrt (2 * ((r : ℝ) + 1))) := by
    rw [le_div_iff₀ (by positivity)]
    calc 2 * n ^ 5 * (8 * Real.sqrt (2 * ((r : ℝ) + 1))) ≤ 2 * n ^ 5 * (8 * n) := by gcongr
      _ = 16 * n ^ 6 := by ring
      _ ≤ n ^ 13 * n ^ 6 := by gcongr; linarith
      _ = _ := by ring
  obtain ⟨K, hK, hc⟩ := GlobalTheory.SOrb.CCBridge.opn_gN_compare k r
  refine ⟨|C| * K ^ |-(2 * n ^ 5)|, fun g hg => ?_⟩
  have h1 : 1 ≤ Formalism.FourierDecayAlt.B.gN g := Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_ge_one hg
  have h2 : Formalism.FourierDecayAlt.B.gN g ^ (-(2 * n ^ 5)) ≤ K ^ |-(2 * n ^ 5)| * opn g ^ (-(2 * n ^ 5)) :=
    GlobalTheory.SOrb.CCBridge.rpow_compare hK _ (by linarith) (opn_pos hg) (hc g).2 (hc g).1
  calc _ ≤ |C| * Formalism.FourierDecayAlt.B.gN g ^ (-(n ^ 19 / (8 * Real.sqrt (2 * ((r : ℝ) + 1))))) :=
        (hC g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    _ ≤ |C| * Formalism.FourierDecayAlt.B.gN g ^ (-(2 * n ^ 5)) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (abs_nonneg _)
    _ ≤ _ := by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)

end GlobalTheory.Amp.LocalInputs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalisedIwasawaIntegralSmallBallAsymptotics
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConst

theorem lintegral_triple_eq {α β γ : Type} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ₁ : Measure α) (μ₂ : Measure β) (μ₃ : Measure γ) [SFinite μ₂] [SFinite μ₃]
    (δ : β → ENNReal) (hδ : Measurable δ) (P : α × β × γ → ENNReal) (hP : Measurable P) :
    ∫⁻ u, ∫⁻ m, δ m * ∫⁻ k, P (u, m, k) ∂μ₃ ∂μ₂ ∂μ₁ = ∫⁻ x, δ x.2.1 * P x ∂(μ₁.prod (μ₂.prod μ₃)) := by
  symm
  rw [lintegral_prod (fun x => δ x.2.1 * P x)
    (show Measurable fun x : α × β × γ => δ x.2.1 * P x from (hδ.comp measurable_snd.fst).mul hP).aemeasurable]
  refine lintegral_congr fun u => ?_
  rw [lintegral_prod (fun y => δ y.1 * P (u, y))
    (show Measurable fun y : β × γ => δ y.1 * P (u, y) from
      (hδ.comp measurable_fst).mul (hP.comp measurable_prodMk_left)).aemeasurable]
  refine lintegral_congr fun m => ?_
  exact lintegral_const_mul (δ m)
    (show Measurable fun k : γ => P (u, m, k) from hP.comp (measurable_prodMk_left.comp measurable_prodMk_left))

theorem IsCut.sigmaFinite {n d : ℕ} {ε : Fin n → Bool} {S : Set (Formalism.REAL.UJ ε)}
    {E : Fin d → Matrix (Fin n) (Fin n) ℂ} (h : IsCut ε S E) {μ : Measure (Formalism.REAL.UJ ε)}
    (hμ : IsGaugeSub S d μ) : SigmaFinite μ := by
  obtain ⟨A, hA, hON, hspan, rfl⟩ := h
  exact (GlobalTheory.T.gaugeMeasure_matrixAlgebraSubgroup_local_asymptotics n ε A d E hA hON hspan μ hμ).1

theorem localised_iwasawa_asymptotics : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (dN dM dK dL : ℕ) (EN : Fin dN → Matrix (Fin n) (Fin n) ℂ) (EM : Fin dM → Matrix (Fin n) (Fin n) ℂ) (EK : Fin dK → Matrix (Fin n) (Fin n) ℂ) (EL : Fin dL → Matrix (Fin n) (Fin n) ℂ), IsCut ε (flagN ε W) EN → IsCut ε (flagM ε W) EM → IsCut ε (maxK ε) EK → IsON EL → (∀ v, gau EN EM EK EL v = 0 → v = 0) → volume {v | gau EN EM EK EL v ≤ 1} ≠ ⊤ → ∀ μN μM μK : Measure (Formalism.REAL.UJ ε), IsGaugeSub (flagN ε W) dN μN → IsGaugeSub (flagM ε W) dM μM → IsGaugeSub (maxK ε) dK μK → ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → Filter.Tendsto (fun r : ℝ => (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) * (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) / ENNReal.ofReal (r ^ (dN + (dM + dK)))) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (volume {v | gau EN EM EK EL v ≤ 1})) := by
  intro n ε a j W hW dN dM dK dL EN EM EK EL hN hM hK hL hgau hvol μN μM μK hμN hμM hμK
  have := hN.sigmaFinite hμN
  have := hM.sigmaFinite hμM
  have := hK.sigmaFinite hμK
  obtain ⟨C, hC, hCη⟩ := GlobalTheory.T.iwasawa_product_gauge_sandwich_near_one n ε _ _ _ dN dM dK dL EN EM EK EL hN hM hK hL hgau
  obtain ⟨t₀, ht₀, hasym⟩ :=
    GlobalTheory.T.tendsto_prod_gaugeMeasures_gaugeBody n ε _ _ _ dN dM dK dL EN EM EK EL hN hM hK hgau μN μM μK hμN hμM hμK
  obtain ⟨t₁, ht₁, h₁⟩ := hCη 1 one_pos
  obtain ⟨ts, hts, hts0, hts1⟩ : ∃ ts : ℝ, 0 < ts ∧ ts ≤ t₀ ∧ ts ≤ t₁ :=
    ⟨min t₀ t₁, lt_min ht₀ ht₁, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨ρ₀, hρ₀, hball⟩ := GlobalTheory.T.iwasawa_factors_near_one_of_product_near_one n ε a j W hW ts hts
  obtain ⟨hdltm, -, hdlt⟩ := GlobalTheory.T.leviFactorInverseModulus_properties n ε a j W

  have hae : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.1 ∈ flagN ε W ∧ x.2.1 ∈ flagM ε W ∧ x.2.2 ∈ maxK ε := by
    have h1 : (μN.prod (μM.prod μK)) ((flagN ε W)ᶜ ×ˢ Set.univ) = 0 := by
      rw [Measure.prod_prod, hμN.1, zero_mul]
    have h2 : (μN.prod (μM.prod μK)) (Set.univ ×ˢ ((flagM ε W)ᶜ ×ˢ Set.univ)) = 0 := by
      rw [Measure.prod_prod, Measure.prod_prod, hμM.1, zero_mul, mul_zero]
    have h3 : (μN.prod (μM.prod μK)) (Set.univ ×ˢ (Set.univ ×ˢ (maxK ε)ᶜ)) = 0 := by
      rw [Measure.prod_prod, Measure.prod_prod, hμK.1, mul_zero, mul_zero]
    have e1 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.1 ∈ flagN ε W := by
      rw [ae_iff]
      exact measure_mono_null (fun x hx => Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩) h1
    have e2 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.2.1 ∈ flagM ε W := by
      rw [ae_iff]
      exact measure_mono_null
        (fun x hx => Set.mem_prod.2 ⟨Set.mem_univ _, Set.mem_prod.2 ⟨hx, Set.mem_univ _⟩⟩) h2
    have e3 : ∀ᵐ x ∂(μN.prod (μM.prod μK)), x.2.2 ∈ maxK ε := by
      rw [ae_iff]
      exact measure_mono_null
        (fun x hx => Set.mem_prod.2 ⟨Set.mem_univ _, Set.mem_prod.2 ⟨Set.mem_univ _, hx⟩⟩) h3
    filter_upwards [e1, e2, e3] with x hx1 hx2 hx3
    exact ⟨hx1, hx2, hx3⟩
  refine ⟨ρ₀, hρ₀, fun ρ hρ hρρ₀ => ?_⟩
  have hPmeas : ∀ r : ℝ, Measurable fun x : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε × Formalism.REAL.UJ ε =>
      (hsBall ε r).indicator (1 : Formalism.REAL.UJ ε → ENNReal) (x.1 * x.2.1 * x.2.2) *
        (slab ε EL ρ r).indicator 1 x.2.2 := by
    intro r
    exact ((measurable_one.indicator (measurableSet_hsBall ε r)).comp
      ((measurable_fst.mul measurable_snd.fst).mul measurable_snd.snd)).mul
      ((measurable_one.indicator (measurableSet_slab ε EL ρ r)).comp measurable_snd.snd)

  have hF : ∀ r : ℝ, (∫⁻ u, ∫⁻ m, dlt j W m * ∫⁻ k, (hsBall ε r).indicator 1 (u * m * k) *
      (slab ε EL ρ r).indicator 1 k ∂μK ∂μM ∂μN) =
      ∫⁻ x, dlt j W x.2.1 * ((hsBall ε r).indicator 1 (x.1 * x.2.1 * x.2.2) *
        (slab ε EL ρ r).indicator 1 x.2.2) ∂(μN.prod (μM.prod μK)) := fun r =>
    GlobalTheory.IwConst.lintegral_triple_eq μN μM μK (dlt j W) hdltm _ (hPmeas r)
  have hc := continuous_nrm_uMat ε
  apply GlobalTheory.T.tendsto_small_ball_density_of_squeeze _ (dN + (dM + dK)) _ hvol
  intro η hη
  obtain ⟨t₂, ht₂, h₂⟩ := hCη η hη
  obtain ⟨t₃, ht₃, h₃⟩ := hdlt η hη
  obtain ⟨t, ht, htts, htρ, htt₂, htt₃⟩ : ∃ t : ℝ, 0 < t ∧ t ≤ ts ∧ t ≤ ρ ∧ t ≤ t₂ ∧ t ≤ t₃ :=
    ⟨min (min ts ρ) (min t₂ t₃), lt_min (lt_min hts hρ) (lt_min ht₂ ht₃),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      (min_le_right _ _).trans (min_le_left _ _), (min_le_right _ _).trans (min_le_right _ _)⟩
  have hBmeas : ∀ s : ℝ, MeasurableSet {x : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε × Formalism.REAL.UJ ε |
      (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧
        gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ s} := by
    intro s
    refine measurableSet_setOfPred.2
      (((measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_fst) measurable_const)).and
      ((measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_snd.fst) measurable_const)).and
        (measurableSet_setOfPred.1 (measurableSet_lt (hc.measurable.comp measurable_snd.snd) measurable_const)))).and
      (measurableSet_setOfPred.1 (measurableSet_le ?_ measurable_const)))
    exact (continuous_gau EN EM EK EL).measurable.comp
      (((continuous_crd_uMat ε EN).measurable.comp measurable_fst).prodMk
        (((continuous_crd_uMat ε EM).measurable.comp measurable_snd.fst).prodMk
          ((continuous_crd_uMat ε EK).measurable.comp measurable_snd.snd)))
  refine ⟨fun s => (μN.prod (μM.prod μK)) {x |
      (nrm (uMat x.1 - 1) < t ∧ nrm (uMat x.2.1 - 1) < t ∧ nrm (uMat x.2.2 - 1) < t) ∧
        gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1), crd EK (uMat x.2.2 - 1)) ≤ s},
    hasym t ht (htts.trans hts0), ?_⟩
  have hr₁ : 0 < min ρ₀ (t / (2 * C)) := lt_min hρ₀ (div_pos ht (by positivity))
  filter_upwards [Ioo_mem_nhdsGT hr₁] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hrρ₀ : r ≤ ρ₀ := (lt_of_lt_of_le hr1 (min_le_left _ _)).le
  have hrC : 2 * C * r < t := by
    have h := lt_of_lt_of_le hr1 (min_le_right _ _)
    rw [lt_div_iff₀ (by positivity)] at h
    linarith
  have hη1 : (0 : ℝ) < 1 + η := by linarith
  rw [hF r]
  constructor
  ·
    rw [← lintegral_indicator_one (hBmeas _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with x hx
    obtain ⟨hxN, hxM, hxK⟩ := hx
    rw [Set.indicator_apply]
    split_ifs with hB
    · obtain ⟨⟨hu, hm, hk⟩, hγ⟩ := hB
      obtain ⟨-, hσγ, -, -, -⟩ := h₂ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu htt₂)
        (lt_of_lt_of_le hm htt₂) (lt_of_lt_of_le hk htt₂) _ _ rfl rfl
      have hσ : max (nrm (uMat (x.1 * x.2.1 * x.2.2) - 1)) (len (crd EL (uMat x.2.2 - 1))) ≤ r := by
        refine hσγ.trans ?_
        calc (1 + η) * gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
              crd EK (uMat x.2.2 - 1)) ≤ (1 + η) * (r / (1 + η)) :=
              mul_le_mul_of_nonneg_left hγ hη1.le
          _ = r := by field_simp
      have hmem1 : x.1 * x.2.1 * x.2.2 ∈ hsBall ε r :=
        ((le_max_left _ _).trans hσ : nrm (uMat (x.1 * x.2.1 * x.2.2) - 1) ≤ r)
      have hmem2 : x.2.2 ∈ slab ε EL ρ r :=
        (⟨lt_of_lt_of_le hk htρ, (le_max_right _ _).trans hσ⟩ :
          nrm (uMat x.2.2 - 1) < ρ ∧ len (crd EL (uMat x.2.2 - 1)) ≤ r)
      rw [Set.indicator_of_mem hmem1, Set.indicator_of_mem hmem2]
      simp only [Pi.one_apply, mul_one]
      exact (h₃ x.2.1 hxM (lt_of_lt_of_le hm htt₃)).2
    · exact bot_le
  ·
    rw [← lintegral_indicator_one (hBmeas _), ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with x hx
    obtain ⟨hxN, hxM, hxK⟩ := hx
    by_cases hA : x.1 * x.2.1 * x.2.2 ∈ hsBall ε r
    swap
    · simp [Set.indicator_apply, hA]
    by_cases hS : x.2.2 ∈ slab ε EL ρ r
    swap
    · simp [Set.indicator_apply, hS]
    rw [Set.indicator_of_mem hA, Set.indicator_of_mem hS]
    simp only [Pi.one_apply, mul_one]
    have hA' : nrm (uMat (x.1 * x.2.1 * x.2.2) - 1) ≤ r := hA
    obtain ⟨hkρ, hL⟩ := (hS : nrm (uMat x.2.2 - 1) < ρ ∧ len (crd EL (uMat x.2.2 - 1)) ≤ r)
    obtain ⟨hu1, hm1, hk1⟩ :=
      hball x.1 hxN x.2.1 hxM x.2.2 (hA'.trans hrρ₀) (lt_of_lt_of_le hkρ hρρ₀)
    have hσ : max (nrm (uMat (x.1 * x.2.1 * x.2.2) - 1)) (len (crd EL (uMat x.2.2 - 1))) ≤ r :=
      max_le hA' hL
    obtain ⟨hγ1, -, hCu, hCm, hCk⟩ := h₁ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu1 hts1)
      (lt_of_lt_of_le hm1 hts1) (lt_of_lt_of_le hk1 hts1) _ _ rfl rfl
    have hγ2 : gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
        crd EK (uMat x.2.2 - 1)) ≤ 2 * r := by
      have := mul_le_mul_of_nonneg_left hσ (by norm_num : (0 : ℝ) ≤ 1 + 1)
      linarith
    have hCγ := mul_le_mul_of_nonneg_left hγ2 hC.le
    have hu : nrm (uMat x.1 - 1) < t := by linarith
    have hm : nrm (uMat x.2.1 - 1) < t := by linarith
    have hk : nrm (uMat x.2.2 - 1) < t := by linarith
    obtain ⟨hγη, -, -, -, -⟩ := h₂ x.1 hxN x.2.1 hxM x.2.2 hxK (lt_of_lt_of_le hu htt₂)
      (lt_of_lt_of_le hm htt₂) (lt_of_lt_of_le hk htt₂) _ _ rfl rfl
    have hγ : gau EN EM EK EL (crd EN (uMat x.1 - 1), crd EM (uMat x.2.1 - 1),
        crd EK (uMat x.2.2 - 1)) ≤ (1 + η) * r :=
      hγη.trans (mul_le_mul_of_nonneg_left hσ hη1.le)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
    rw [if_pos ⟨⟨hu, hm, hk⟩, hγ⟩, Pi.one_apply, mul_one]
    exact (h₃ x.2.1 hxM (lt_of_lt_of_le hm htt₃)).1

end GlobalTheory.IwConst
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowAnalyticFactsOfFourSteps
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting
  Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.FourierDecayAlt Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.NGCut Formalism.L2.SG.NGAnalytic
  GlobalTheory.NGRow

namespace GlobalTheory.NGRow

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem stepAnalyticP_of_steps : StepPinExists → StepVanishPinned → StepLocGenPinnedC → StepThmBPinnedP →
    StepAnalyticP := by
  intro hE hV hL hB Cg cb Cw cT CT C0 hcb hcT
  obtain ⟨C1, C0n, CSt, hCSt, a₀, b₀, hL2⟩ := hL Cg cb Cw cT CT C0
  obtain ⟨e₀, f₀, hE2⟩ := hE Cg cb Cw cT CT C0
  obtain ⟨v₀, w₀, hV2⟩ := hV Cg cb Cw cT CT C0
  refine ⟨C1, C0n, fun A => ?_⟩
  obtain ⟨CB, hCB, p₀, q₀, hB2⟩ := hB Cg cb Cw cT CT C0 hcb hcT A
  refine ⟨CB, CSt, hCB, hCSt, max a₀ (max e₀ (max v₀ p₀)), max b₀ (max f₀ (max w₀ q₀)),
    fun C' Cl h1 h2 D large₂ X Y u u' hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk => ?_⟩
  have ha1 : a₀ ≤ C' := le_trans (by simp) h1
  have ha2 : b₀ ≤ Cl := le_trans (by simp) h2
  have he1 : e₀ ≤ C' := le_trans (by simp) h1
  have he2 : f₀ ≤ Cl := le_trans (by simp) h2
  have hv1 : v₀ ≤ C' := le_trans (by simp) h1
  have hv2 : w₀ ≤ Cl := le_trans (by simp) h2
  have hp1 : p₀ ≤ C' := le_trans (by simp) h1
  have hp2 : q₀ ≤ Cl := le_trans (by simp) h2
  obtain ⟨ν, hν⟩ := hE2 C' Cl he1 he2 D large₂ X Y u u' hc
  obtain ⟨s, ng, e1, hs1, hs0, hsb, he0, he3, hLoc, hGen⟩ :=
    hL2 C' Cl ha1 ha2 D large₂ X Y u u' hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν
  have hb0 : 0 ≤ large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f) :=
    le_trans (sq_nonneg _) (hsb 1)
  exact ⟨sc s ν, ν, ng, large₂.sc.b ^ (CSt * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 3 * D.R.f), e1,
    nuQOK_sc u u' s hs1 hs0 ν hν.1, hν.1, hb0, le_rfl, he0, he3,
    ampVanish_sc Y u u' s hs0 ν (hV2 C' Cl hv1 hv2 D large₂ X Y u u' hc ν hν), hLoc, hGen,
    measureInput_sc Y u u' s ν _ hsb ng,
    hB2 C' Cl hp1 hp2 D large₂ X Y u u' hTi hc hb X0 ψ hT sd C Th F0 what₂ vR Q i0 i0' νq Irat Ire hBk ν hν (sc s ν) ng⟩

end GlobalTheory.NGRow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SlabMeasureSqueezeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.slab_measure_squeeze' : ∀ (n : ℕ) (ε : Fin n → Bool) (a : ℕ) (j : Fin a → ℕ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsIsoFlag ε j W → ∀ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ), IsCut ε (maxK ε ∩ flagM ε W) E → (∀ i, (E i)ᴴ = -E i) → ∀ ν : Measure (Formalism.REAL.UJ ε), ν (maxK ε ∩ flagM ε W)ᶜ = 0 → (∀ l ∈ maxK ε ∩ flagM ε W, ν.map (fun g => g * l) = ν) → ∀ ρ η : ℝ, 0 < ρ → ρ ≤ 1 / 8 → 0 < η → ∀ᶠ r in (nhdsWithin (0 : ℝ) (Set.Ioi 0)), ∀ u ∈ flagN ε W, ∀ m ∈ flagM ε W, ∀ k ∈ maxK ε, u * m * k ∈ hsBall ε r → ν (hsBall ε (r / (1 + η))) ≤ ν {l | l * k ∈ slab ε E ρ r} ∧ ν {l | l * k ∈ slab ε E ρ r} ≤ ν (hsBall ε ((1 + η) * r)) := by
  first | exact @GlobalTheory.IwConst.slab_measure_squeeze | exact GlobalTheory.IwConst.slab_measure_squeeze | (intros; apply GlobalTheory.IwConst.slab_measure_squeeze <;> assumption)
end

