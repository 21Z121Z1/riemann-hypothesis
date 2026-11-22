import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0460
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0351
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0293
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0392
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0272
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsGenericTermIffNoLocalDefectBaseFrames
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Formalism.HermitianCurvature.Bundle0007
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0183
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0377
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0270
import Formalism.FormalDegreeBessel.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0466
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumPairBdMulDatBdLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0400
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0315
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0334
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0346
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0413
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0456
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0386
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0102
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0337
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0338
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0465
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeightedTermPairsSumLeViaRowsGenusMeansStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0051

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SignedLocalTermDefectIffUnsignedLocalTerm
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SignDefect

theorem locBBne_iff_locU : ∀ {D : D7} (Z : LocDat D) (p : PlF D) (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E} (F : LFlag (VS D) D.R.rS T) (F' : LFlag (VS D) D.R.rS T') (Tn T'n : ℕ), locBBne Z p Λ F F' Tn T'n ↔ LocNG.BBne (H := locH Z p) (locU Z p Λ F F' Tn T'n) := by
  intro D Z p Λ T T' F F' Tn T'n
  exact (GlobalTheory.Unfold.GenLoc.locBBne_iff Z p Λ F F' Tn T'n).symm

end GlobalTheory.SignDefect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardBesselScaleBound
section
open Formalism.FourierDecayAlt Formalism.MainNotions.S GlobalTheory.ThA Formalism.QuantumDeterminants MeasureTheory Matrix
open Formalism.BasicNotions

namespace GlobalTheory.ThA.BpDict

theorem ptEntry_swap (bs : List (ℂ × ℕ)) : ∀ a b : ℕ,
    D.ptEntry (bs.map fun b => (b.2, b.1)) a b = ptEntry bs a b := by
  induction bs with
  | nil => intro a b; rfl
  | cons x bs ih =>
    intro a b
    obtain ⟨t, s⟩ := x
    rw [List.map_cons, D.ptEntry.eq_def, ptEntry.eq_def]
    simp only [ih]

theorem isLocPt_swap {i : ℕ} (γ : Point ℂ i) : D.IsLocPt (γ.1.map fun b => (b.2, b.1)) i := by
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
    exact ⟨(γ.2.1 c hc).2, (γ.2.1 c hc).1⟩
  · unfold D.ptSize
    rw [List.map_map]
    exact γ.2.2

theorem ptG_swap {r : ℕ} (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    D.ptG (T * T') r (γ.1.map fun b => (b.2, b.1)) = ThB.Gpt T T' γ := by
  have h : ∀ (l : ℕ) (hl : l ≤ r + 1), D.ptMatN (γ.1.map fun b => (b.2, b.1)) l =
      (ptMat γ).submatrix (Fin.castLE hl) (Fin.castLE hl) := by
    intro l hl
    ext a b
    exact ptEntry_swap γ.1 a b
  unfold D.ptG ThB.Gpt leadMinor
  rw [h (r + 1) le_rfl, h r (Nat.le_succ r)]

theorem weightFrom_swap (k r : ℕ) (hk : 1 ≤ k) (T T' GG : ℝ) (bs : List (ℂ × ℕ)) : ∀ x : ℕ,
    (∀ b ∈ bs, 1 ≤ b.2) → x + (bs.map Prod.snd).sum = r + 1 →
    (∀ b, bs.getLast? = some b → GG = Complex.normSq b.1 - T * T') →
    ptWeightFrom k r T T' x bs = C.nAux k r GG (fun _ _ => 1) (x + 1) (bs.map fun b => (b.2, b.1)) := by
  induction bs with
  | nil => intro x _ _ _; rfl
  | cons y bs ih =>
    intro x h1 h2 h3
    obtain ⟨t, s⟩ := y
    have hs : 1 ≤ s := h1 (t, s) (by simp)
    simp only [List.map_cons, List.sum_cons] at h2
    rw [List.map_cons, ptWeightFrom.eq_2, C.nAux.eq_2]
    have hrec : ptWeightFrom k r T T' (x + s) bs =
        C.nAux k r GG (fun _ _ => 1) (x + 1 + s) (bs.map fun b => (b.2, b.1)) := by
      rw [show x + 1 + s = x + s + 1 by omega]
      refine ih (x + s) (fun b hb => h1 b (List.mem_cons_of_mem _ hb)) (by omega) ?_
      intro b hb
      apply h3
      cases bs with
      | nil => simp at hb
      | cons z bs => rw [List.getLast?_cons_cons]; exact hb
    rw [hrec]
    congr 1
    by_cases hc : s = 1 ∧ x + 1 = r + 1
    · rw [if_pos hc, if_pos ⟨by omega, hc.1⟩]
      have hnil : bs = [] := by
        cases bs with
        | nil => rfl
        | cons z bs =>
          exfalso
          have := h1 z (by simp)
          simp only [List.map_cons, List.sum_cons] at h2
          omega
      subst hnil
      rw [h3 (t, s) rfl]
    · rw [if_neg hc, if_neg (by omega), one_mul, ← zpow_natCast]
      congr 1
      unfold Ml C.Mlev
      have e1 : x + 1 + s - 1 = x + s := by omega
      rw [e1]
      have e2 : x + s ≤ r + 1 := by omega
      have e3 : 3 ≤ 2 * (r + 1 - (x + s)) + k + 1 + s := by omega
      push_cast [Nat.cast_sub e2, Nat.cast_sub e3]
      ring

theorem ptWeight_swap (k r : ℕ) (hk : 1 ≤ k) (T T' : ℝ) (γ : Point ℂ (r + 1)) :
    ptWeight k r T T' γ = TBB.nPt k r (T * T') (γ.1.map fun b => (b.2, b.1)) := by
  unfold ptWeight TBB.nPt
  refine weightFrom_swap k r hk T T' _ γ.1 0 (fun b hb => (γ.2.1 b hb).2) (by rw [zero_add]; exact γ.2.2) ?_
  intro b hb
  unfold D.ptGG D.ptLast
  rw [List.getLast?_map, hb]
  rfl

theorem aT_one (k r : ℕ) : aT k r 1 = 1 := by
  unfold aT
  rw [← Matrix.diagonal_one]
  congr 1
  funext i
  simp

theorem conjF_one {k r : ℕ} {V : Type*} (F : B.Mat k r → V) : conjF 1 F = F := by
  funext x
  unfold conjF
  rw [aT_one]; simp

theorem gamLev_one (k r : ℕ) : D.GamLev k r 1 1 0 = 1 := by
  unfold D.GamLev
  simp

theorem const_le (r c n : ℕ) (b C₄ Cb G : ℝ) (hc : c ≤ (r + 1) ^ 2) (hb : 3 ≤ b) (hC : C₄ + 1 ≤ Cb)
    (hn : (n : ℝ) ≤ Cb * ((2 * r + 2 : ℕ) : ℝ) ^ 2) (hG : 0 < G) :
    (Real.pi ^ c) ^ 2 * (b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * G⁻¹ ^ n) ≤
      b ^ (Cb * ((2 * r + 2 : ℕ) : ℝ) ^ 4) * (max 1 (1 / G)) ^ (Cb * ((2 * r + 2 : ℕ) : ℝ) ^ 2) := by
  have hb1 : 1 ≤ b := by linarith
  have hb0 : 0 < b := by linarith
  have h1 : (Real.pi ^ c) ^ 2 ≤ b ^ (((2 * r + 2 : ℕ) : ℝ) ^ 4) := by
    have hpi : Real.pi ≤ b ^ 2 := by nlinarith [Real.pi_le_four]
    calc (Real.pi ^ c) ^ 2 ≤ ((b ^ 2) ^ c) ^ 2 := by gcongr
      _ = b ^ (4 * c) := by ring
      _ ≤ b ^ ((2 * r + 2) ^ 4) := by
        refine pow_le_pow_right₀ hb1 ?_
        have : (r + 1) ^ 2 ≤ (r + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
        have e : (2 * r + 2) ^ 4 = 16 * (r + 1) ^ 4 := by ring
        omega
      _ = _ := by rw [← Real.rpow_natCast]; push_cast; rfl
  have h2 : G⁻¹ ^ n ≤ (max 1 (1 / G)) ^ (Cb * ((2 * r + 2 : ℕ) : ℝ) ^ 2) := by
    calc G⁻¹ ^ n ≤ (max 1 (1 / G)) ^ n := by
          refine pow_le_pow_left₀ (by positivity) ?_ n
          rw [one_div]; exact le_max_right _ _
      _ = (max 1 (1 / G)) ^ (n : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (le_max_left _ _) hn
  rw [← mul_assoc]
  refine mul_le_mul ?_ h2 (by positivity) (by positivity)
  calc (Real.pi ^ c) ^ 2 * b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4)
      ≤ b ^ (((2 * r + 2 : ℕ) : ℝ) ^ 4) * b ^ (C₄ * ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by gcongr
    _ = b ^ ((C₄ + 1) * ((2 * r + 2 : ℕ) : ℝ) ^ 4) := by rw [← Real.rpow_add hb0]; congr 1; ring
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hb1 (by gcongr)

theorem hsNormSq_nonneg {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A : Wq →L[ℂ] Wp) : 0 ≤ hsNormSq A := by
  unfold hsNormSq hsInner
  rw [Complex.re_sum]
  exact Finset.sum_nonneg fun i _ => inner_self_nonneg (𝕜 := ℂ)

theorem orbSq_eq_zero {k r : ℕ} (L : LocBessel k r) (F : ThB.Mx k r → (L.Wq →L[ℂ] L.Wp)) (γ : Point ℂ (r + 1))
    (hG : ThB.Gpt (Tz k r L.z) (Tz k r L.z') γ < 0) : ThB.orbSq L F γ = 0 := by
  unfold ThB.orbSq
  simp only [ENNReal.iSup_eq_zero]
  intro g _ _ h
  exfalso
  have h0 := gNonneg k r L.z L.z' L.hz.1 L.hz'.1 L.hz.2 L.hz'.2 g h.1.1
  unfold Gf Dmin at h0
  rw [h.1.2] at h0
  exact absurd hG (not_lt.2 h0)

theorem card_rootPat_le {r : ℕ} (γ : Point ℂ (r + 1)) : (rootPat γ).card ≤ (r + 1) ^ 2 := by
  refine (Finset.card_le_univ _).trans ?_
  simp [sq]

theorem bpIneq_of_thmBpAt : ∃ c₃ : ℝ, ∀ (D : D7) (L : LocBessel D.R.k D.R.rS) (μsec : ℂ → Matrix (Fin (D.R.k + 1)) (Fin (D.R.k + 1)) ℂ) (U U' : ℕ → ℝ) (p : KB.Pl ⟨D.R.k, D.R.rS, Tz D.R.k D.R.rS L.z, Tz D.R.k D.R.rS L.z', U, U'⟩ L.Wp L.Wq) (f : B.Mat D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp)) (A b C₄ Cb : ℝ) (n₀ p₀ : ℕ), IsStdOf L μsec p.T.base → L.c = cStd → L.κN ≠ 0 → L.κN ≠ ⊤ → c₃ * ((D.R.rS : ℝ) + 1) ^ 2 * ((D.R.rS : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) + 1) ≤ A → B.InCC A 1 f → 3 ≤ b → C₄ + 1 ≤ Cb → ((2 * p₀ + n₀ : ℕ) : ℝ) ≤ Cb * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ 2 → TBB.ThmBpAt p f b C₄ n₀ p₀ → ∀ γ : Point ℂ (D.R.rS + 1), ThB.Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ ≠ 0 → ThB.BpIneq D Cb L f μsec b γ := by
  obtain ⟨c₃, hc₃⟩ := GlobalTheory.T.orbitalSquare_eq_hilbertSchmidt_normalisedVector
  refine ⟨c₃, ?_⟩
  intro D L μsec U U' p f A b C₄ Cb n₀ p₀ hstd hc hκ0 hκt hA hf hb hC hn hBp γ hγ
  unfold ThB.BpIneq
  rcases lt_or_gt_of_ne hγ with hG | hG
  · rw [orbSq_eq_zero L f γ hG, mul_zero]; exact zero_le
  obtain ⟨cN, hcN⟩ := GlobalTheory.T.exists_unipotentHaarMeasure_ratio D.R.k D.R.rS
  have hk : 1 ≤ D.R.k := p.T.base.k_pos
  have hc0 : (cStd : ℂ) ≠ 0 := by unfold cStd; simp
  have hcc : cStd / L.c = 1 := by rw [hc]; exact div_self hc0
  have horb := hc₃ D.R.k D.R.rS L μsec p.T.base cN A p.ν' p.m₀ f hstd hcN hc hκ0 hκt p.hF hA hf γ hG
  have hnorm := GlobalTheory.T.besselEnergy_normalised_frame_change D.R.k D.R.rS L μsec p.T.base cN f hk hstd hcN (hc ▸ hc0) hκ0 hκt
  have hj : ThB.jNorm2 L f μsec = ENNReal.ofReal ((L.κN.toReal * cN) ^ 4) * TBB.jN2 p f := by
    rw [GlobalTheory.jN2_eq_normSq_base.besselNormSq_eq_bigCellNormSq]
    unfold lamN at hnorm
    rw [hcc, conjF_one, norm_one, inv_one, gamLev_one, one_pow, mul_one, div_one] at hnorm
    refine Eq.trans ?_ hnorm
    unfold ThB.jNorm2 jNormSq
    refine lintegral_congr fun q => ?_
    rw [Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hsNormSq_nonneg _)]
  have hTT : TBB.TTp p = Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z' := by
    unfold TBB.TTp
    rw [hstd.1, hstd.2.1]
  have hGp : TBB.Gp p (γ.1.map fun b => (b.2, b.1)) = ThB.Gpt (Tz D.R.k D.R.rS L.z) (Tz D.R.k D.R.rS L.z') γ := by
    unfold TBB.Gp
    rw [hTT]
    exact ptG_swap _ _ γ
  have hB := hBp _ (isLocPt_swap γ) (hGp ▸ hG)
  rw [P.TBBx2.Tri.Ew_top p f (isLocPt_swap γ), hGp, hTT] at hB
  rw [horb, hj, ptWeight_swap _ _ hk]
  have hle := const_le D.R.rS (rootPat γ).card (2 * p₀ + n₀) b C₄ Cb _ (card_rootPat_le γ) hb hC hn hG
  unfold KB.Pl.V at hB
  dsimp only at hB
  set n := TBB.nPt D.R.k D.R.rS (Tz D.R.k D.R.rS L.z * Tz D.R.k D.R.rS L.z') (γ.1.map fun b => (b.2, b.1)) with hn'
  rcases le_total n 0 with h0 | h0
  · rw [ENNReal.ofReal_of_nonpos h0, zero_mul]; exact zero_le
  rw [Real.mul_self_sqrt h0] at hB
  set v := ‖B.hsVec (Formalism.FourierDecayAlt.D.vecV p.T.base p.ν' p.m₀ f (γ.1.map fun b => (b.2, b.1)))‖ ^ 2 with hv
  set K := (L.κN.toReal * cN) ^ 4 with hK
  set Q := (Real.pi ^ (rootPat γ).card) ^ 2 with hQ
  have hK0 : 0 ≤ K := by rw [hK]; positivity
  have hQ0 : 0 ≤ Q := by rw [hQ]; positivity
  have e1 : ENNReal.ofReal n * ENNReal.ofReal (K * Q * v) =
      ENNReal.ofReal K * (ENNReal.ofReal Q * ENNReal.ofReal (n * v)) := by
    rw [← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul hQ0, ← ENNReal.ofReal_mul hK0]
    congr 1; ring
  rw [e1, mul_left_comm _ (ENNReal.ofReal K)]
  refine mul_le_mul_right ?_ _
  refine (mul_le_mul_right hB _).trans ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul hQ0]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal hle) _

end GlobalTheory.ThA.BpDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermMovesToBaseFramesUpToUnitriangularStatement
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.term_moves_to_baseFrames_up_to_unitriangular : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ t₀ : TauC Y u u', t₀.toTerm.atPt w → ∃ (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' := by
  first | exact @GlobalTheory.HL.MoveTerm.term_moves_to_base | exact GlobalTheory.HL.MoveTerm.term_moves_to_base | (intros; apply GlobalTheory.HL.MoveTerm.term_moves_to_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermPairCountBoundOfSiegelMassRatios
section
noncomputable section
open scoped Classical ENNReal Pointwise
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.KappaEndpoints Formalism.L2.SG.RowsConc
namespace GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace PairsPf

theorem massC_nonneg {D : D7} {X : HidaSetting D} (Y : Full X) (u : D.what₂.Word) : 0 ≤ massC Y u := by
  show 0 ≤ ∑ Λ ∈ Y.what₂ u, wRow D (X.Fu u) Λ
  exact Finset.sum_nonneg fun Λ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem datBd_nonneg (K : Type) [Field K] [NumberField K] [StarRing K] (k r : ℕ) (Del Db NT x : ℝ) (hD : 0 ≤ Del)
    (hDb : 0 ≤ Db) (hN : 0 ≤ NT) (hx : 0 ≤ x) : 0 ≤ GlobalTheory.DegAsm.datBd K k r Del Db NT x := by
  unfold GlobalTheory.DegAsm.datBd
  positivity

theorem termPairBoundFactor_nonneg {D : D7} (large₂ : SizeData₂ D) (CH Ch Cp : ℝ) (j : ℕ) (δ : ℕ → D.host.E) : 0 ≤ k2e large₂ CH Ch Cp j δ := by
  have hb : 0 < large₂.sc.b := Real.exp_pos _
  have h1 : 0 ≤ k2Del D j δ := Rat.cast_nonneg.mpr (FractionalIdeal.absNorm_nonneg _)
  have h2 : 0 ≤ Hb large₂.sc.b Ch D.R.m D.R.f := Real.rpow_nonneg hb.le _
  have h3 : 0 ≤ k2S D (H1C large₂ CH) j δ := by
    unfold k2S k2sg
    exact Finset.prod_nonneg fun τ _ => le_trans zero_le_one ((Finset.le_fold_max 1).2 (Or.inl le_rfl))
  unfold k2e
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg h1 _) (Real.rpow_nonneg h2 _)) (Real.rpow_nonneg h3 _)
private lemma le_mul_sum_sum_of_ofReal_le_ennreal_sum (s s' : Finset ℕ) (f P : ℕ → ℕ → ℝ) (c L : ℝ) (hf : ∀ x x', 0 ≤ f x x')
    (hP : ∀ x x', 0 ≤ P x x') (hc : 0 ≤ c)
    (h : ENNReal.ofReal L ≤ ∑ x ∈ s, ∑ x' ∈ s', ENNReal.ofReal (f x x') * ENNReal.ofReal (c * P x x')) :
    L ≤ c * ∑ x ∈ s, ∑ x' ∈ s', P x x' * f x x' := by
  have hnn : ∀ x x', 0 ≤ f x x' * (c * P x x') := fun x x' => mul_nonneg (hf x x') (mul_nonneg hc (hP x x'))
  have e : ∑ x ∈ s, ∑ x' ∈ s', ENNReal.ofReal (f x x') * ENNReal.ofReal (c * P x x') =
      ENNReal.ofReal (∑ x ∈ s, ∑ x' ∈ s', f x x' * (c * P x x')) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => Finset.sum_nonneg fun x' _ => hnn x x')]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun x' _ => hnn x x')]
    refine Finset.sum_congr rfl fun x' _ => ?_
    rw [ENNReal.ofReal_mul (hf x x')]
  rw [e] at h
  have h' := (ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun x' _ => hnn x x')).1 h
  refine le_trans h' (le_of_eq ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x' _ => ?_
  ring

end PairsPf
open PairsPf in

theorem pair_count_bound_of_siegel_mass : GlobalTheory.Mass.MaxMass → Formalism.HermitianLatticesTheory.SiegelMassRatio → PairsP := by
  intro hMM hSR
  unfold PairsP
  intro Cg cb Cw cT CT C0 CH hCH

  obtain ⟨Ca, hCa1, hCaH, hCaT⟩ : ∃ Ca : ℝ, 1 ≤ Ca ∧ 2 * (CH + 1) ≤ Ca ∧ CT ≤ Ca :=
    ⟨max 1 (max (2 * (CH + 1)) CT), le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  obtain ⟨Ch, Cl', hCh, hsum⟩ := GlobalTheory.DegAsm.sum_pairBd_mul_datBd_le Ca hCa1
  refine ⟨Ch, 16, hCh, by norm_num, 1, max 1 Cl', ?_⟩
  intro C' Cl hC' hCl D large₂ X Y u hK2 _
  have hStd : GlobalTheory.TypeAsm.Std D large₂ :=
    show ∃ C' Cl Cg cb Cw cT CT C0 : ℝ, Formalism.MainNotions.NonGenericAndKTwoTheorems.KTwoHypotheses D large₂ C' Cl Cg cb Cw cT CT C0 from
      ⟨C', Cl, Cg, cb, Cw, cT, CT, C0, hK2⟩
  have hHost : HostC := GlobalTheory.T.unitaryHostFieldArithmeticConditions
  have hfD : Formalism.HermitianLatticesTheory.fDeg D.host.E = D.R.f := (hHost D large₂ hStd).2.2.2.2.1
  have hCl1 : 1 ≤ Cl := le_trans (le_max_left _ _) hCl
  have hClCl : Cl' ≤ Cl := le_trans (le_max_right _ _) hCl
  obtain ⟨hrk, hm, hClm, hm4, hm5, hClk, hlog, hb2, hv1, hvb, hg, hTu⟩ :=
    GlobalTheory.T.parameter_size_constraints Ca Cg cb Cw cT CT C0 C' Cl D large₂ hHost hK2 hC' hCl1 hCaT
  have hlb : 0 ≤ (D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b := mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
  have hClm' : Cl' ≤ (D.R.m : ℝ) := le_trans hClCl hClm
  have hClk' : Cl' * ((D.R.m : ℝ) ^ 2 * Real.log large₂.sc.b) ≤ D.R.k :=
    le_trans (mul_le_mul_of_nonneg_right hClCl hlb) hClk

  have hHb : Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f ≤
      large₂.sc.b ^ (Ca * (D.R.m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E) := by
    show large₂.sc.b ^ (2 * (CH + 1) * (D.R.m : ℝ) ^ 2 * D.R.f) ≤ _
    rw [hfD]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by gcongr)
  have hHb0 : 0 ≤ Hb large₂.sc.b (2 * (CH + 1)) D.R.m D.R.f := Real.rpow_nonneg (by linarith) _
  have hNT : NT D u = ((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E := by
    rw [hfD]
    rfl
  have hNT0 : 0 ≤ NT D u := by
    rw [hNT]
    positivity
  have hk2e : ∀ (j : ℕ) (δ : ℕ → D.host.E), k2e large₂ CH Ch 16 j δ =
      k2Del D j δ ^ ((D.R.k : ℝ) / 2) * (large₂.sc.b ^ (Ch * (D.R.m : ℝ) ^ 2 * Formalism.HermitianLatticesTheory.fDeg D.host.E)) ^ (Ch * (D.R.rS : ℝ) ^ 4) *
        k2S D (H1C large₂ CH) j δ ^ (16 * (D.R.k : ℝ)) := by
    intro j δ
    rw [hfD]
    rfl
  unfold PairsAt
  intro j' _ j'' _ δ' δ'' S hS
  rcases S.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
  · rw [Finset.sum_empty]
    exact mul_nonneg (massC_nonneg Y u) (mul_nonneg (termPairBoundFactor_nonneg large₂ CH Ch 16 j' δ') (termPairBoundFactor_nonneg large₂ CH Ch 16 j'' δ''))
  obtain ⟨hpp, hj1, hj2, hl1, hl2⟩ := hS p hp
  obtain ⟨hr1, hr2, -⟩ := hpp
  have hF := GlobalTheory.T.relevantTerm_norms_ge_one_and_bounded Cg cb Cw cT CT C0 CH C' Cl hCH D large₂ X Y u hHost GlobalTheory.T.exists_adaptedNormalForm_relevantTerm GlobalTheory.T.adaptedNormalForm_normsMinors_eq_label GlobalTheory.T.rowLattice_term_adaptedNormalForm hK2
  obtain ⟨hD1, hDb1, hDle, hDble⟩ := hF p.1 hr1
  obtain ⟨hD1', hDb1', hDle', hDble'⟩ := hF p.2 hr2
  rw [hj1, hl1] at hD1 hDb1 hDle hDble
  rw [hj2, hl2] at hD1' hDb1' hDle' hDble'
  have hS1 : 1 ≤ k2S D (H1C large₂ CH) j' δ' := by
    unfold k2S k2sg
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      (fun τ _ => (Finset.le_fold_max 1).2 (Or.inl le_rfl))
  have hS1' : 1 ≤ k2S D (H1C large₂ CH) j'' δ'' := by
    unfold k2S k2sg
    exact Finset.prod_induction _ (fun x : ℝ => 1 ≤ x) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl
      (fun τ _ => (Finset.le_fold_max 1).2 (Or.inl le_rfl))

  have hDA := le_trans hDle (mul_le_mul_of_nonneg_right hHb (sq_nonneg _))
  have hDA' := le_trans hDle' (mul_le_mul_of_nonneg_right hHb (sq_nonneg _))
  have hDbA := le_trans hDble (pow_le_pow_left₀ (mul_nonneg hHb0 (sq_nonneg _)) (mul_le_mul_of_nonneg_right hHb (sq_nonneg _)) _)
  have hDbA' := le_trans hDble' (pow_le_pow_left₀ (mul_nonneg hHb0 (sq_nonneg _)) (mul_le_mul_of_nonneg_right hHb (sq_nonneg _)) _)
  have hbound := hsum D.host.E D.R.k D.R.rS D.R.m (gS D) (Tu D u) large₂.sc.b (k2Del D j' δ') (k2Del D j'' δ'')
    (DbL D j' δ') (DbL D j'' δ'') (k2S D (H1C large₂ CH) j' δ') (k2S D (H1C large₂ CH) j'' δ'') hrk hm hClm' hm4 hm5 hClk'
    hlog hb2 hv1 hvb hg (hTu u).1 (hTu u).2 hS1 hS1' hD1 hD1' hDb1 hDb1' hDA hDA' hDbA hDbA'

  obtain ⟨W, HW, hemb, hrkW, hPD⟩ := GlobalTheory.T.definite_quotient_model_exists D large₂ X u hStd
  have hI := GlobalTheory.T.weightedTermPairs_sum_le_via_rows_genusMeans D large₂ X Y u hStd GlobalTheory.T.termsOverRow_compatible GlobalTheory.T.termPairs_rowLattice_counted_via_embeddings GlobalTheory.T.rowsMeanC_holds W HW hemb
    (fun s M x x' => GlobalTheory.T.isometricEmbeddedDatumPairs_encard_isometry_smul _ _ HW (gS D) D.R.rS x x' s M)
    (fun x x' => GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x')
    (fun x x' => GlobalTheory.DegAsm.pairBd_nonneg _ _ _ _ _ _ _)
    (fun Λ hΛ x x' hx hx' => GlobalTheory.T.genusMean_embeddedPairs_le_mass_mul_pairBound hMM hSR hHost GlobalTheory.T.base_lattice_construction_holds D large₂ X Y u hStd W HW hemb hrkW hPD Λ hΛ x x' hx hx')
    j' j'' δ' δ'' S hS
  rw [hNT] at hI
  have hstep := le_mul_sum_sum_of_ofReal_le_ennreal_sum _ _
    (fun x x' => GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j' δ') (DbL D j' δ')
        (((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E) x *
      GlobalTheory.DegAsm.datBd D.host.E D.R.k D.R.rS (k2Del D j'' δ'') (DbL D j'' δ'')
        (((Tu D u : ℕ) : ℝ) ^ Formalism.HermitianLatticesTheory.fDeg D.host.E) x')
    (fun x x' => GlobalTheory.DegAsm.pairBd D.host.E D.R.k (gS D) D.R.rS (Tu D u) x x') (massC Y u) _
    (fun x x' => mul_nonneg (datBd_nonneg _ _ _ _ _ _ _ (by linarith) (by linarith) (by positivity) (Nat.cast_nonneg _))
      (datBd_nonneg _ _ _ _ _ _ _ (by linarith) (by linarith) (by positivity) (Nat.cast_nonneg _)))
    (fun x x' => GlobalTheory.DegAsm.pairBd_nonneg _ _ _ _ _ _ _) (massC_nonneg Y u) hI
  refine le_trans hstep ?_
  rw [hk2e, hk2e]
  exact mul_le_mul_of_nonneg_left hbound (massC_nonneg Y u)

end GlobalTheory.TypeAsm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermRowEqIffMovedLatticeInnerDataEq
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.DatEq

theorem row_eq_iff_datOf_eq : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (F'0 : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), ∀ (t₀ : TauC Y u u') (ρ : ((VS D).V ≃ₗ[D.host.E] (VS D).V)) (U U' : Formalism.L2.SG.PairVal.MatR D), MovesTo F00 F'0 (lf D (X.Fu u)) t₀.frame ρ U U' → ∀ (t : TauC Y u u') n m, t.lam = t₀.lam → t.lam' = t₀.lam' → n ∈ NRat (lf D (X.Fu u)) ∧ m ∈ NRat (lf D (X.Fu u')) ∧ t.lin = n⁻¹ * t₀.lin * m → ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀ ↔ G.datOf (c.lat (ρ * n) t.lam) = G.datOf (c.lat ρ t₀.lam)) := by
  intro D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hA := GlobalTheory.T.doubleCoset_terms_same_innerLattices D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hI := GlobalTheory.T.identificationCompat_iff_localGraphs D X Y u u' hSt hk w F00 F'0 FP hZ hG hAt G c t₀ ρ U U' hMv t n m hl hl' hnm
  have hD := Formalism.L2.SG.Pf.iotaDictAllC_holds D X Y u u' t₀ t hl.symm hl'.symm
  have hrow : ((Y.tO u u').rowOf t = (Y.tO u u').rowOf t₀) ↔
      iotaOf Y.TR (Y.cs u) (Y.cs u') t₀ = iotaOf Y.TR (Y.cs u) (Y.cs u') t := by
    show ((⟨t.lam, t.mem⟩, ⟨t.lam', t.mem'⟩, iotaOf Y.TR (Y.cs u) (Y.cs u') t) : Rw _ _ Y.TR) =
        (⟨t₀.lam, t₀.mem⟩, ⟨t₀.lam', t₀.mem'⟩, iotaOf Y.TR (Y.cs u) (Y.cs u') t₀) ↔ _
    constructor
    · intro h
      exact (congrArg (fun r => r.2.2) h).symm
    · intro h
      rw [h]
      ext <;> simp [hl, hl']
  rw [hrow, hD, hI]
  constructor
  · intro h
    funext p
    exact Prod.ext (hA p).1 (Prod.ext (hA p).2 (h p))
  · intro h p
    exact congrArg (fun d => (d p).2.2) h

end GlobalTheory.HL.DatEq
end

