import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0181
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0154
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLiftEmbeddedDatumOfTerm
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0173
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Formalism.FlagUnipotentLattices.MemOfOrthogonalAnisotropic
import Formalism.FormalDegreeBessel.StatementG
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0032
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0025

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeOneSideUnfolding
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.OnePiece

variable {k r : ℕ}

theorem continuous_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) := by
  unfold lmulM
  exact continuous_const.matrix_mul continuous_id.matrixOf

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) := by
  unfold conjM
  exact (continuous_const.matrix_mul continuous_id.matrixOf).matrix_mul continuous_const

theorem continuous_mulPair :
    Continuous fun p : Mt k r × Mt k r => lmulM (Matrix.of p.1) p.2 := by
  unfold lmulM
  exact continuous_fst.matrixOf.matrix_mul continuous_snd.matrixOf

def grp (k r : ℕ) : Set (Mt k r) := {x | Matrix.of x ∈ GG k r}

theorem measurableSet_grp : MeasurableSet (grp k r) := by
  have hc : Continuous fun x : Mt k r => (Matrix.of x : Mat k r)ᴴ * Hpk k r * Matrix.of x :=
    (continuous_id.matrixOf.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id.matrixOf
  exact (isClosed_eq hc continuous_const).measurableSet

private theorem continuous_matrix_of : Continuous fun x : Mt k r => (Matrix.of x : Mat k r) :=
  continuous_id.matrixOf

theorem measurable_indicator_grp {f : Mat k r → ℝ≥0∞} (hf : ContinuousOn f (GG k r)) :
    Measurable ((grp k r).indicator fun x => f (Matrix.of x)) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact ContinuousOn.measurable_piecewise
    (hf.comp continuous_matrix_of.continuousOn fun _ hx => hx) continuousOn_const measurableSet_grp

theorem mem_GG_of_mul {s x : Mat k r} (hs : s ∈ GG k r) (h : s * x ∈ GG k r) : x ∈ GG k r := by
  have hs' : sᴴ * Hpk k r * s = Hpk k r := hs
  have h' : (s * x)ᴴ * Hpk k r * (s * x) = Hpk k r := h
  show xᴴ * Hpk k r * x = Hpk k r
  calc xᴴ * Hpk k r * x = xᴴ * (sᴴ * Hpk k r * s) * x := by rw [hs']
    _ = (s * x)ᴴ * Hpk k r * (s * x) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := h'

theorem continuousOn_sq {X E : Type} [TopologicalSpace X] [NormedAddCommGroup E] {g : X → E} {s : Set X}
    (hg : ContinuousOn g s) : ContinuousOn (fun x => (‖g x‖₊ : ℝ≥0∞) ^ 2) s :=
  ((ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp continuous_nnnorm)).comp_continuousOn hg

private theorem mul_mem_UH_Hpk' {a b : Mat k r} (ha : a ∈ GG k r) (hb : b ∈ GG k r) : a * b ∈ GG k r := by
  have ha' : aᴴ * Hpk k r * a = Hpk k r := ha
  have hb' : bᴴ * Hpk k r * b = Hpk k r := hb
  show (a * b)ᴴ * Hpk k r * (a * b) = Hpk k r
  calc (a * b)ᴴ * Hpk k r * (a * b) = bᴴ * (aᴴ * Hpk k r * a) * b := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [ha', hb']

private theorem aemeasurable_comp_of_continuousOn_closed {S : Set (Mat k r)} (hS : IsClosed S) {μ : Measure (Mt k r)}
    (hμ : μ {x | Matrix.of x ∉ S} = 0) {g : Mat k r → ℝ≥0∞} (hg : ContinuousOn g S) :
    AEMeasurable (fun x => g (Matrix.of x)) μ := by
  classical
  have hm : MeasurableSet {x : Mt k r | Matrix.of x ∈ S} :=
    (hS.preimage continuous_matrix_of).measurableSet
  have h1 : Measurable ({x : Mt k r | Matrix.of x ∈ S}.piecewise (fun x => g (Matrix.of x)) 0) :=
    ContinuousOn.measurable_piecewise (hg.comp continuous_matrix_of.continuousOn fun _ hx => hx)
      continuousOn_const hm
  have hae : ∀ᵐ x ∂μ, Matrix.of x ∈ S := by rw [ae_iff]; exact hμ
  refine h1.aemeasurable.congr ?_
  filter_upwards [hae] with x hx
  exact Set.piecewise_eq_of_mem _ _ _ hx

private theorem ofReal_one_sq_mul_norm_sq_div {E : Type} [NormedAddCommGroup E] (v : E) (d : ℕ) (hd : 0 < d) :
    ENNReal.ofReal ((1 : ℝ) ^ 2 * ‖v‖ ^ 2 / d) = (d : ℝ≥0∞)⁻¹ * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  rw [one_pow, one_mul, div_eq_inv_mul, ENNReal.ofReal_mul (inv_nonneg.2 hd'.le),
    ENNReal.ofReal_inv_of_pos hd', ENNReal.ofReal_natCast, ← coe_nnnorm v, ← NNReal.coe_pow,
    ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow]

theorem one_piece : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)) (ψ : Mat k r → ℂ) (μG μW μN νS : Measure (Mt k r)) (Φ : Mat k r → Wp) (c : ℝ), OneSide z π ψ μG μW μN νS Φ c → ∀ (f : Mt k r → ℝ≥0∞) (Q : Set (Mt k r)) (Vol : ℝ≥0∞), Measurable f → MeasurableSet Q → (∀ s ∈ Sset k r z, ∀ x, Matrix.of x ∈ GG k r → (lmulM s x ∈ Q ↔ x ∈ Q)) → (∀ g ∈ GG k r, ∫⁻ n, f (rmulM g n) ∂μN ≤ Vol) → ∀ w : Wp, ‖w‖ = 1 → ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG ≤ Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS := by
  intro k r Wp _ _ _ z π ψ μG μW μN νS Φ c hOS f Q Vol hf hQ hQinv hVol w hw
  obtain ⟨hz, hT, hnt, hU, hI, hG, hW, hW1, hN, hQm, hψ, hE, hΦ, -, -⟩ := hOS
  haveI := hnt
  have hd : 0 < Module.finrank ℂ Wp := Module.finrank_pos
  have hinC : Continuous fun v : Wp => ⟪w, v⟫_ℂ := continuous_const.inner continuous_id
  set A : Mt k r → ℝ≥0∞ := (grp k r).indicator fun y => (‖⟪w, Φ (Matrix.of y)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2
    with hAdef
  set B : Mt k r → ℝ≥0∞ := (grp k r).indicator fun y => (‖Φ (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2
    with hBdef
  have hAm : Measurable A :=
    measurable_indicator_grp (f := fun g => (‖⟪w, Φ g⟫_ℂ‖₊ : ℝ≥0∞) ^ 2)
      (continuousOn_sq (hinC.comp_continuousOn hΦ))
  have hBm : Measurable B :=
    measurable_indicator_grp (f := fun g => (‖Φ g‖₊ : ℝ≥0∞) ^ 2) (continuousOn_sq hΦ)
  set F : Mt k r → ℝ≥0∞ := Q.indicator fun y => f y * A y with hFdef
  have hFm : Measurable F := (hf.mul hAm).indicator hQ
  have haeG : ∀ᵐ x ∂μG, Matrix.of x ∈ GG k r := by rw [ae_iff]; exact hG.2.2.1
  have haeW : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r z := by rw [ae_iff]; exact hW.2.2.1
  have haeN : ∀ᵐ n ∂μN, Matrix.of n ∈ Nset k r := by rw [ae_iff]; exact hN.2.2.1

  have step1 : ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG = ∫⁻ x, F x ∂μG := by
    rw [← lintegral_indicator hQ]
    refine lintegral_congr_ae ?_
    filter_upwards [haeG] with x hx
    have hxg : x ∈ grp k r := hx
    by_cases hxQ : x ∈ Q
    · rw [hFdef, hAdef]
      simp only [Set.indicator_of_mem hxQ, Set.indicator_of_mem hxg]
    · rw [hFdef]
      simp only [Set.indicator_of_notMem hxQ]

  have inner_le : ∀ x : Mt k r,
      ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ≤
        Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
    intro x
    have hit : ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ≤
        ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW :=
      calc ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN)
          ≤ ∫⁻ p, F (lmulM (Matrix.of p.1 * Matrix.of p.2) x) ∂(μW.prod μN) := lintegral_map_le _ _
        _ ≤ ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW := lintegral_prod_le _
    refine hit.trans ?_
    have zero_case : (∀ h : Mt k r, Matrix.of h ∈ UWset k r z → ∀ n : Mt k r,
        Matrix.of n ∈ Nset k r → F (lmulM (Matrix.of h * Matrix.of n) x) = 0) →
        ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW ≤
          Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
      intro h0
      refine le_trans ?_ (zero_le ..)
      calc ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW
          ≤ ∫⁻ _h, (0 : ℝ≥0∞) ∂μW := by
            refine lintegral_mono_ae ?_
            filter_upwards [haeW] with h hh
            calc ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ≤ ∫⁻ _n, (0 : ℝ≥0∞) ∂μN := by
                  refine lintegral_mono_ae ?_
                  filter_upwards [haeN] with n hn
                  exact (h0 h hh n hn).le
              _ = 0 := lintegral_zero
        _ = 0 := lintegral_zero
    by_cases hxg : x ∈ grp k r
    · by_cases hxQ : x ∈ Q
      · have hB : Q.indicator B x = (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 := by
          rw [hBdef]
          simp only [Set.indicator_of_mem hxQ, Set.indicator_of_mem hxg]
        have hmain : ∀ h : Mt k r, Matrix.of h ∈ UWset k r z → ∀ n : Mt k r,
            Matrix.of n ∈ Nset k r → F (lmulM (Matrix.of h * Matrix.of n) x) =
              f (lmulM (Matrix.of h * Matrix.of n) x) *
                (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 := by
          intro h hh n hn
          have hs : Matrix.of h * Matrix.of n ∈ Sset k r z := by
            show ∃ h' ∈ UWset k r z, ∃ m ∈ Nset k r, Matrix.of h * Matrix.of n = h' * m
            exact ⟨_, hh, _, hn, rfl⟩
          have hSQ : lmulM (Matrix.of h * Matrix.of n) x ∈ Q := (hQinv _ hs x hxg).2 hxQ
          have hSG : lmulM (Matrix.of h * Matrix.of n) x ∈ grp k r :=
            mul_mem_UH_Hpk' (mul_mem_UH_Hpk' hh.1 hn.1) hxg
          have hΦS : Φ (Matrix.of (lmulM (Matrix.of h * Matrix.of n) x)) =
              ψ (Matrix.of n) • π (Matrix.of h) (Φ (Matrix.of x)) := hE _ hh _ hn _ hxg
          have hψ1 : ‖ψ (Matrix.of n)‖₊ = 1 := by ext; simpa using hψ _ hn
          rw [hFdef, hAdef]
          simp only [Set.indicator_of_mem hSQ, Set.indicator_of_mem hSG, hΦS, inner_smul_right,
            nnnorm_mul, hψ1, one_mul]
        have hfib : ∀ h : Mt k r, Matrix.of h ∈ UWset k r z →
            ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ≤ Vol := by
          intro h hh
          have hdet : IsUnit (Matrix.of h : Mat k r).det := isUnit_det_of_mem_GG hh.1
          have key : ∀ n : Mt k r, lmulM (Matrix.of h * Matrix.of n) x =
              rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n) := by
            intro n
            show (Matrix.of h * Matrix.of n * Matrix.of x : Mat k r) =
              Matrix.of h * Matrix.of n * (Matrix.of h)⁻¹ * (Matrix.of h * Matrix.of x)
            rw [Matrix.mul_assoc (Matrix.of h * Matrix.of n) (Matrix.of h)⁻¹,
              ← Matrix.mul_assoc (Matrix.of h)⁻¹, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
          have hrc : Continuous (rmulM (Matrix.of h * Matrix.of x) : Mt k r → Mt k r) := by
            unfold rmulM
            exact continuous_matrix_of.matrix_mul continuous_const
          have hinv : μN.map (conjM (Matrix.of h)) = μN :=
            ((GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hz hT μN).2.1 hN).2 _ hh
          calc ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN
              = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) (conjM (Matrix.of h) n)) ∂μN :=
                lintegral_congr fun n => congrArg f (key n)
            _ = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) n) ∂(μN.map (conjM (Matrix.of h))) :=
                (lintegral_map (hf.comp hrc.measurable) (continuous_conj _).measurable).symm
            _ = ∫⁻ n, f (rmulM (Matrix.of h * Matrix.of x) n) ∂μN := by rw [hinv]
            _ ≤ Vol := hVol _ (mul_mem_UH_Hpk' hh.1 hxg)
        have hAEM : AEMeasurable (fun h : Mt k r =>
            (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2) μW :=
          aemeasurable_comp_of_continuousOn_closed (isClosedSub_UWset z).2.1 hW.2.2.1
            (g := fun g => (‖⟪w, π g (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2)
            (continuousOn_sq (hinC.comp_continuousOn (hU.2.2 (Φ (Matrix.of x)))))
        calc ∫⁻ h, ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN ∂μW
            ≤ ∫⁻ h, Vol * (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW := by
              refine lintegral_mono_ae ?_
              filter_upwards [haeW] with h hh
              calc ∫⁻ n, F (lmulM (Matrix.of h * Matrix.of n) x) ∂μN
                  = ∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) *
                      (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μN := by
                    refine lintegral_congr_ae ?_
                    filter_upwards [haeN] with n hn
                    exact hmain h hh n hn
                _ = (∫⁻ n, f (lmulM (Matrix.of h * Matrix.of n) x) ∂μN) *
                      (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
                    lintegral_mul_const' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)
                _ ≤ Vol * (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 :=
                    mul_le_mul_of_nonneg_right (hfib h hh) (zero_le ..)
          _ = Vol * ∫⁻ h, (‖⟪w, π (Matrix.of h) (Φ (Matrix.of x))⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW :=
              lintegral_const_mul'' _ hAEM
          _ = Vol * ENNReal.ofReal (‖w‖ ^ 2 * ‖Φ (Matrix.of x)‖ ^ 2 / Module.finrank ℂ Wp) := by
              rw [(GlobalTheory.T.hcTypeW_irreducible_and_schur_average k r z π hz hT).2 μW hU hI hW hW1 w (Φ (Matrix.of x))]
          _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x := by
              rw [hB, hw, ofReal_one_sq_mul_norm_sq_div _ _ hd, mul_assoc]
      · refine zero_case fun h hh n hn => ?_
        have hs : Matrix.of h * Matrix.of n ∈ Sset k r z := by
          show ∃ h' ∈ UWset k r z, ∃ m ∈ Nset k r, Matrix.of h * Matrix.of n = h' * m
          exact ⟨_, hh, _, hn, rfl⟩
        have hSQ : lmulM (Matrix.of h * Matrix.of n) x ∉ Q := fun h' => hxQ ((hQinv _ hs x hxg).1 h')
        rw [hFdef]
        simp only [Set.indicator_of_notMem hSQ]
    · refine zero_case fun h hh n hn => ?_
      have hS : lmulM (Matrix.of h * Matrix.of n) x ∉ grp k r := fun hS =>
        hxg (mem_GG_of_mul (s := Matrix.of h * Matrix.of n) (x := Matrix.of x)
          (mul_mem_UH_Hpk' hh.1 hn.1) hS)
      rw [hFdef, hAdef]
      by_cases hSQ : lmulM (Matrix.of h * Matrix.of n) x ∈ Q
      · simp only [Set.indicator_of_mem hSQ, Set.indicator_of_notMem hS, mul_zero]
      · simp only [Set.indicator_of_notMem hSQ]
  calc ∫⁻ x in Q, f x * (‖⟪w, Φ (Matrix.of x)⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μG = ∫⁻ x, F x ∂μG := step1
    _ = ∫⁻ x, ∫⁻ s, F (fun i j => (Matrix.of s * Matrix.of x) i j) ∂(muProd μW μN) ∂νS := hQm F hFm
    _ ≤ ∫⁻ x, Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * Q.indicator B x ∂νS := lintegral_mono inner_le
    _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x, Q.indicator B x ∂νS :=
        lintegral_const_mul _ (hBm.indicator hQ)
    _ = Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, B x ∂νS := by rw [lintegral_indicator hQ]
    _ ≤ Vol * (Module.finrank ℂ Wp : ℝ≥0∞)⁻¹ * ∫⁻ x in Q, (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS :=
        mul_le_mul_of_nonneg_left (lintegral_mono fun x => Set.indicator_le_self _ _ x) (zero_le ..)

end GlobalTheory.Amp.OnePiece
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BallMeanContinuousLinearFunctional
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SgInf

theorem ballMean_eLpNorm_two_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {ν : Measure α} {f : α → E} {C a : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a)
    (h : ∫⁻ x, (‖f x‖₊ : ENNReal) ^ 2 ∂ν ≤ ENNReal.ofReal (C * a ^ 2)) :
    eLpNorm f 2 ν ≤ ENNReal.ofReal (Real.sqrt C * a) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (∫⁻ x, ‖f x‖ₑ ^ (ENNReal.toReal 2) ∂ν) = ∫⁻ x, (‖f x‖₊ : ENNReal) ^ 2 ∂ν := by
    congr 1; funext x
    rw [show ENNReal.toReal 2 = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    rfl
  rw [h2]
  calc _ ≤ (ENNReal.ofReal (C * a ^ 2)) ^ (1 / (ENNReal.toReal 2)) := by gcongr
    _ = ENNReal.ofReal (Real.sqrt C * a) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      congr 1
      rw [show (1 / ENNReal.toReal 2 : ℝ) = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
        Real.sqrt_mul' _ (by positivity), Real.sqrt_sq ha]

theorem ballMean_norm_integral_le {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ν : Measure α} [IsFiniteMeasure ν] {f : α → E} {C a : ℝ} (hC : 0 ≤ C)
    (ha : 0 ≤ a) (hf : AEStronglyMeasurable f ν)
    (h : ∫⁻ x, (‖f x‖₊ : ENNReal) ^ 2 ∂ν ≤ ENNReal.ofReal (C * a ^ 2)) :
    Integrable f ν ∧ ‖∫ x, f x ∂ν‖ ≤ Real.sqrt C * (ν Set.univ).toReal ^ (1 / 2 : ℝ) * a := by
  have h2 := ballMean_eLpNorm_two_le hC ha h
  have hL2 : MemLp f 2 ν := ⟨hf, lt_of_le_of_lt h2 ENNReal.ofReal_lt_top⟩
  refine ⟨hL2.integrable (by norm_num), ?_⟩
  have h1 : eLpNorm f 1 ν ≤ eLpNorm f 2 ν * ν Set.univ ^ (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hf
  rw [eLpNorm_one_eq_lintegral_enorm] at h1
  have hexp : (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal : ℝ) = 1 / 2 := by norm_num
  rw [hexp] at h1
  have hmu : ν Set.univ ^ (1 / 2 : ℝ) = ENNReal.ofReal ((ν Set.univ).toReal ^ (1 / 2 : ℝ)) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal (measure_ne_top ν _)]
  have key : ‖∫ x, f x ∂ν‖ₑ ≤ ENNReal.ofReal (Real.sqrt C * (ν Set.univ).toReal ^ (1 / 2 : ℝ) * a) := by
    calc ‖∫ x, f x ∂ν‖ₑ ≤ ∫⁻ x, ‖f x‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ eLpNorm f 2 ν * ν Set.univ ^ (1 / 2 : ℝ) := h1
      _ ≤ ENNReal.ofReal (Real.sqrt C * a) * ENNReal.ofReal ((ν Set.univ).toReal ^ (1 / 2 : ℝ)) := by
          rw [hmu]; gcongr
      _ = _ := by
          rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  rw [← ofReal_norm_eq_enorm] at key
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 key

theorem ballMean_clm : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (T : H → Mat k r → Wp), IsHaarOn (GG k r) μG →
    (∀ u u' : H, (fun x : Mt k r => T (u + u') (Matrix.of x)) =ᵐ[μG]
      fun x => T u (Matrix.of x) + T u' (Matrix.of x)) →
    (∀ (b : ℂ) (u : H), (fun x : Mt k r => T (b • u) (Matrix.of x)) =ᵐ[μG] fun x => b • T u (Matrix.of x)) →
    (∀ K : Set (Mt k r), IsCompact K → ∃ C : ℝ, ∀ u : H,
      AEStronglyMeasurable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict K) ∧
      ∫⁻ x in K, (‖T u (Matrix.of x)‖₊ : ENNReal) ^ 2 ∂μG ≤ ENNReal.ofReal (C * ‖u‖ ^ 2)) →
    (∀ y ∈ GG k r, ∀ u : H, (fun x : Mt k r => T (σ y u) (Matrix.of x)) =ᵐ[μG]
      fun x => T u (Matrix.of x * y)) →
    ∀ j : ℕ, ∃ Λ : H →L[ℂ] Wp, ∀ (v : H) (x : Mt k r), Matrix.of x ∈ GG k r →
      Λ (σ (Matrix.of x) v) = avgR μG j (fun z : Mt k r => T v (Matrix.of z)) x := by
  intro k r H _ _ _ Wp _ _ _ σ μG T hμ hadd hsmul hL2 htr j
  have hBfin : μG (nbd k r j) < ⊤ := haar_compact_lt_top hμ (isCompact_nbd j)
  haveI : IsFiniteMeasure (μG.restrict (nbd k r j)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hBfin⟩
  obtain ⟨C, hC⟩ := hL2 (nbd k r j) (isCompact_nbd j)
  have hb : ∀ u : H, Integrable (fun x : Mt k r => T u (Matrix.of x)) (μG.restrict (nbd k r j)) ∧
      ‖∫ x in nbd k r j, T u (Matrix.of x) ∂μG‖ ≤
        Real.sqrt (max C 0) * ((μG.restrict (nbd k r j)) Set.univ).toReal ^ (1 / 2 : ℝ) * ‖u‖ := by
    intro u
    refine ballMean_norm_integral_le (le_max_right C 0) (norm_nonneg u) (hC u).1 ?_
    refine (hC u).2.trans (ENNReal.ofReal_le_ofReal ?_)
    gcongr
    exact le_max_left C 0
  set c : ℝ := ((μG (nbd k r j)).toReal)⁻¹ with hc
  have hc0 : 0 ≤ c := inv_nonneg.2 ENNReal.toReal_nonneg
  let L : H →ₗ[ℂ] Wp :=
    { toFun := fun v => c • ∫ x in nbd k r j, T v (Matrix.of x) ∂μG
      map_add' := fun u u' => by
        rw [integral_congr_ae (ae_restrict_of_ae (hadd u u')), integral_add (hb u).1 (hb u').1, smul_add]
      map_smul' := fun b u => by
        simp only [RingHom.id_apply]
        rw [integral_congr_ae (ae_restrict_of_ae (hsmul b u)), integral_smul, smul_comm] }
  refine ⟨L.mkContinuous (c * (Real.sqrt (max C 0) *
      ((μG.restrict (nbd k r j)) Set.univ).toReal ^ (1 / 2 : ℝ))) ?_, ?_⟩
  · intro v
    show ‖c • ∫ x in nbd k r j, T v (Matrix.of x) ∂μG‖ ≤ _
    rw [norm_smul, Real.norm_of_nonneg hc0, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb v).2 hc0
  · intro v x hx
    show c • ∫ y in nbd k r j, T (σ (Matrix.of x) v) (Matrix.of y) ∂μG = _
    unfold avgR
    rw [integral_congr_ae (ae_restrict_of_ae (htr _ hx v))]
    rfl

end GlobalTheory.SgInf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BiorthogonalBlockFramesTriangular
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov

theorem mul_eq_zero_of_mulVec_mulVec {p q n : ℕ} {A : Matrix (Fin p) (Fin n) ℂ}
    {B : Matrix (Fin n) (Fin q) ℂ} (h : ∀ x, A *ᵥ (B *ᵥ x) = 0) : A * B = 0 := by
  ext i j
  have hx := congrFun (h (Pi.single j 1)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at hx
  simpa using hx

theorem Biorth.col_mem {n m : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ}
    (hT : Biorth r m T T') (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (s k : ℕ) (hk : s < k) (x : Fin (r s) → ℂ) : T s *ᵥ x ∈ W k := by
  rw [hW]
  intro b hb
  rw [Matrix.mulVec_mulVec, hT.2.1 b s (by omega), Matrix.zero_mulVec]

theorem Biorth.mul_eq_block {n m p q : ℕ} {W : ℕ → Submodule ℂ (Fin n → ℂ)} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ}
    (hT : Biorth r m T T') (hW : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (b : ℕ) {A : Matrix (Fin p) (Fin n) ℂ} {B : Matrix (Fin n) (Fin q) ℂ}
    (hA : ∀ y ∈ W b, A *ᵥ y = 0) (hB : ∀ x, B *ᵥ x ∈ W (b + 1)) :
    A * B = (A * T b) * (T' b * B) := by
  have hAT : ∀ c, c < b → A * T c = 0 := fun c hc =>
    mul_eq_zero_of_mulVec_mulVec fun x => hA _ (Biorth.col_mem hT hW c b hc x)
  have hTB : ∀ c, b < c → T' c * B = 0 := fun c hc =>
    mul_eq_zero_of_mulVec_mulVec fun x => (hW (b + 1) _).1 (hB x) c (by omega)
  calc A * B = A * (∑ c ∈ Finset.range m, T c * T' c) * B := by rw [hT.2.2, Matrix.mul_one]
    _ = ∑ c ∈ Finset.range m, (A * T c) * (T' c * B) := by
      rw [Matrix.mul_sum, Matrix.sum_mul]
      simp only [Matrix.mul_assoc]
    _ = (A * T b) * (T' b * B) := by
      apply Finset.sum_eq_single b
      · intro c _ hcb
        rcases lt_or_gt_of_ne hcb with hc | hc
        · rw [hAT c hc, Matrix.zero_mul]
        · rw [hTB c hc, Matrix.mul_zero]
      · intro hb

        have hTb : T b = 0 := by
          rw [← Matrix.one_mul (T b), ← hT.2.2, Matrix.sum_mul]
          apply Finset.sum_eq_zero
          intro c hc
          rw [Matrix.mul_assoc, hT.2.1 c b (by rintro rfl; exact hb hc), Matrix.mul_zero]
        rw [hTb, Matrix.mul_zero, Matrix.zero_mul]

theorem blockFrames_triangular (n m : ℕ) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (r : ℕ → ℕ)
    (T U : ∀ b, Matrix (Fin n) (Fin (r b)) ℂ) (T' U' : ∀ b, Matrix (Fin (r b)) (Fin n) ℂ)
    (hT : Biorth r m T T') (hU : Biorth r m U U')
    (hWT : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → T' b *ᵥ y = 0)
    (hWU : ∀ k y, y ∈ W k ↔ ∀ b, k ≤ b → U' b *ᵥ y = 0) :
    (∀ b, (U' b * T b) * (T' b * U b) = 1) ∧ ∀ c, ∀ Y ∈ lowers W c, ∀ b,
      U' b * Y * U (b + c + 1) =
        (U' b * T b) * (T' b * Y * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) := by
  refine ⟨fun b => ?_, fun c Y hY b => ?_⟩
  · rw [← Biorth.mul_eq_block hT hWT b (fun y hy => (hWU b y).1 hy b le_rfl)
      (fun x => Biorth.col_mem hU hWU b (b + 1) (by omega) x)]
    exact hU.1 b
  · have hY' : ∀ b', ∀ y ∈ W (b' + c + 1), Y *ᵥ y ∈ W b' := mem_lowers.1 hY
    have e1 : U' b * (Y * U (b + c + 1)) = (U' b * T b) * (T' b * (Y * U (b + c + 1))) :=
      Biorth.mul_eq_block hT hWT b (fun y hy => (hWU b y).1 hy b le_rfl) (fun x => by
        rw [← Matrix.mulVec_mulVec]
        exact hY' (b + 1) _ (Biorth.col_mem hU hWU (b + c + 1) (b + 1 + c + 1) (by omega) x))
    have e2 : (T' b * Y) * U (b + c + 1) =
        ((T' b * Y) * T (b + c + 1)) * (T' (b + c + 1) * U (b + c + 1)) :=
      Biorth.mul_eq_block hT hWT (b + c + 1)
        (fun y hy => by
          rw [← Matrix.mulVec_mulVec]
          exact (hWT b _).1 (hY' b y hy) b le_rfl)
        (fun x => Biorth.col_mem hU hWU (b + c + 1) (b + c + 1 + 1) (by omega) x)
    calc U' b * Y * U (b + c + 1) = U' b * (Y * U (b + c + 1)) := Matrix.mul_assoc _ _ _
      _ = (U' b * T b) * (T' b * (Y * U (b + c + 1))) := e1
      _ = (U' b * T b) * ((T' b * Y) * U (b + c + 1)) := by rw [Matrix.mul_assoc (T' b)]
      _ = _ := by rw [e2]; simp only [Matrix.mul_assoc]

end GlobalTheory.RadCov
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnBlocksSpanFlagOfBlockTriangular
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem exists_sum_mulVec_of_triangular {n a : ℕ} {j : Fin a → ℕ} (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (hp : ∀ k i, i < k → p k i = 0)
    (hA : ∀ i, A i = ∑ k, B k * p k i) (l : Fin (a + 1)) (u : ∀ i, Fin (j i) → ℂ)
    (hu : ∀ i : Fin a, ¬ i.castSucc < l → u i = 0) :
    ∃ v : ∀ i, Fin (j i) → ℂ, (∀ i : Fin a, ¬ i.castSucc < l → v i = 0) ∧
      ∑ i, A i *ᵥ u i = ∑ i, B i *ᵥ v i := by
  refine ⟨fun k => ∑ i, p k i *ᵥ u i, ?_, ?_⟩
  · intro k hk
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases hik : i < k
    · rw [hp k i hik, Matrix.zero_mulVec]
    · have hki : k ≤ i := not_lt.mp hik
      have hi : ¬ i.castSucc < l := fun hi =>
        hk (lt_of_le_of_lt (Fin.castSucc_le_castSucc_iff.mpr hki) hi)
      rw [hu i hi, Matrix.mulVec_zero]
  · simp_rw [hA, Matrix.sum_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_sum]
    exact Finset.sum_comm

theorem spansFlag_of_triangular (n a : ℕ) (j : Fin a → ℕ) (A B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ)
    (p q : ∀ k i, Matrix (Fin (j k)) (Fin (j i)) ℂ) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ))
    (hpq : ∀ k i, i < k → p k i = 0 ∧ q k i = 0) (hA : ∀ i, A i = ∑ k, B k * p k i)
    (hB : ∀ i, B i = ∑ k, A k * q k i) (h : SpansFlag A W) : SpansFlag B W := by
  intro k y
  rw [h k y]
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact exists_sum_mulVec_of_triangular A B p (fun k i hik => (hpq k i hik).1) hA k u hu
  · rintro ⟨v, hv, rfl⟩
    obtain ⟨w, hw, he⟩ :=
      exists_sum_mulVec_of_triangular B A q (fun k i hik => (hpq k i hik).2) hB k v hv
    exact ⟨w, hw, he⟩

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteLiftEmbeddedDatumOfTermStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteLift_embedded_datum_of_term : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∃ H' : HermSpace K N.Wt, (∀ x y, H'.B x y = H.B x y) ∧ GlobalTheory.Mass.PD H'.B.flip ∧ GlobalTheory.Mass.IsIntLat H'.B.flip (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) ∧ (GlobalTheory.Mass.discN H'.B.flip (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) : ℝ) = N.NT ^ 2 ∧ GenBy (Formalism.HermitianLatticesTheory.dual H'.B.flip (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ))) (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) 1 ∧ IsDat H' g (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F N.F' Λ)) N.j (N.gI g Λ) (GlobalTheory.Mass.latIn N.Wt (flagPairDefinitePartLattice N.F' N.F Λ), (iotaGraph N.F N.F' Λ (g : 𝓞 K)).comap ((N.Wt.subtype.prodMap N.Wt.subtype).restrictScalars (𝓞 K))) := by
  first | exact @GlobalTheory.DegCnt.ToLift.main | exact GlobalTheory.DegCnt.ToLift.main | (intros; apply GlobalTheory.DegCnt.ToLift.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsBlockAntidiagonalScaledPairingMatrixStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockAntidiagonal_scaled_pairing_matrix : ∀ {K : Type} [Field K] {j r : ℕ} (hj : j ≤ r) (w : Formalism.MainNotions.S.Loc.Pt K j),
    ∃ β : Fin r → ℕ, Monotone β ∧ (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) ∧
      ∀ (σ : K →+* ℂ) (sgn : Fin j → ℤˣ) (ρ : ℝ), 0 < ρ →
      GlobalTheory.Amp.BlockAnti (fun a : Fin j => β (Fin.castLE hj a))
        (Matrix.of fun a b : Fin j => (((ρ ^ (r - b.val))⁻¹ * (ρ ^ (r - a.val))⁻¹ : ℝ) : ℂ) *
          σ (w.mat b a * ((sgn a : ℤ) : K))) := by
  first | exact @GlobalTheory.Amp.BlockFrame.blockAnti_scaled_pairing | exact GlobalTheory.Amp.BlockFrame.blockAnti_scaled_pairing | (intros; apply GlobalTheory.Amp.BlockFrame.blockAnti_scaled_pairing <;> assumption)
end

