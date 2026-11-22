import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaPullbackConstantSqEqDet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsOrthonormalBasisFamily
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JetsTorsionTranslatesCmThetaProduct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumTranslateConjugateJetBound
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0279
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1912
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1764
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1395

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedTensorChosenPlaceCoeffValuationLossLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

noncomputable section

namespace GlobalTheory.UnfoldLoss.MovedChosen

section Local

variable {k : Type} [Field k] {G : Grid k}

theorem gdet_stair (hs : 1 ≤ G.s) (ϖ : kˣ) (e j : ℕ) :
    ∃ a : ℕ, gdet (stair G ϖ e j) = ϖ ^ a ∧ a ≤ G.rank (G.m, j) * (e * G.m) := by
  refine ⟨∑ a : Fin (G.rank (G.m, j)), e * (a.val + 1 - topRank G j), ?_, ?_⟩
  · rw [stair, gdet, det_diagGL, Finset.prod_pow_eq_pow_sum]
  · calc ∑ a : Fin (G.rank (G.m, j)), e * (a.val + 1 - topRank G j) ≤ ∑ _a : Fin (G.rank (G.m, j)), e * G.m :=
          Finset.sum_le_sum fun a _ => Nat.mul_le_mul_left _ (by have := topRank_add hs j; have := a.2; omega)
      _ = _ := by simp

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gdet_elt (hs : 1 ≤ G.s) (J : G.Level) (ϖ : kˣ) (e : ℕ) (X : ℕ × ℕ) :
    ∃ a : ℕ, gdet ((Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) X) = ϖ ^ a ∧
      a ≤ G.rank X * (e * G.m) := by
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    by_cases hj : j + 2 ≤ G.m
    · borelize k
      rw [through_elt _ hj]
      exact gdet_stair hs ϖ e j
    · cases j with
      | zero =>
        rw [Reps.elt, onColumn_apply]
        exact gdet_stair hs ϖ e 0
      | succ i =>
        refine ⟨0, ?_, Nat.zero_le _⟩
        rw [Reps.elt, onColumn_apply]
        simp [show ¬ i < G.m - 2 by omega]
  · refine ⟨0, ?_, Nat.zero_le _⟩
    simp [Reps.elt, onColumn, hi]

theorem apow_half {ϖ : kˣ} (hϖ : IsUnif ϖ) (a n : ℕ) :
    apow (ϖ ^ a)⁻¹ ((n : ℂ) / 2) = ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (a * n) := by
  rw [apow_inv, apow_pow, hϖ.apow_eq, neg_neg, mul_comm a n, pow_mul]
  congr 1
  rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow (Nat.cast_nonneg _), ← Complex.cpow_mul_nat]
  push_cast
  congr 1
  ring

end Local

section Val

variable {D : D7}

theorem lossLe_mul {w : PlL D} {z z' : ℂ} {a a' : ℝ} (h : LossLe w z a) (h' : LossLe w z' a') :
    LossLe w (z * z') (a + a') := by
  obtain ⟨y, rfl, hy⟩ := h
  obtain ⟨y', rfl, hy'⟩ := h'
  refine ⟨y * y', map_mul _ _ _, ?_⟩
  by_cases h0 : y = 0
  · exact Or.inl (by simp [h0])
  by_cases h0' : y' = 0
  · exact Or.inl (by simp [h0'])
  refine Or.inr ?_
  have h1 := hy.resolve_left h0
  have h2 := hy'.resolve_left h0'
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ h0 h0', Int.cast_add]
  linarith

theorem lossLe_list_prod {w : PlL D} {ι : Type} (f : ι → ℂ) (a : ℝ) (l : List ι) (h : ∀ b ∈ l, LossLe w (f b) a) :
    LossLe w (l.map f).prod (l.length * a) := by
  induction l with
  | nil => exact ⟨1, by simp, Or.inr (by simp [Formalism.DivisionValues.ValuationRepresentative.vw_one])⟩
  | cons b l ih =>
    rw [List.map_cons, List.prod_cons]
    refine (lossLe_mul (h b (by simp)) (ih fun c hc => h c (by simp [hc]))).mono (le_of_eq ?_)
    simp only [List.length_cons]
    push_cast
    ring

theorem lossLe_sqrt {w : PlL D} {q : ℕ} (hq : q ≠ 0) (hs : ((Real.sqrt q : ℝ) : ℂ) ∈ Set.range D.what₂.embLL) (n n' : ℕ) :
    LossLe w (((Real.sqrt q : ℝ) : ℂ) ^ n * (((Real.sqrt q : ℝ) : ℂ) ^ n')⁻¹) (n' * (vw w (q : D.what₂.LL) : ℝ) / 2) := by
  obtain ⟨y, hy⟩ := hs
  have h2 : y ^ 2 = (q : D.what₂.LL) := D.what₂.embLL.injective (by
    rw [map_pow, hy, map_natCast, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast])
  have hy0 : y ≠ 0 := by
    rintro rfl
    have : (q : D.what₂.LL) = 0 := by rw [← h2]; simp
    exact hq (by exact_mod_cast this)
  have hv : (vw w (q : D.what₂.LL) : ℝ) = 2 * vw w y := by
    rw [← h2, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0]
    push_cast
    ring
  have hv0 : (0 : ℝ) ≤ (vw w (q : D.what₂.LL) : ℝ) := by exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w q
  refine ⟨y ^ n * (y ^ n')⁻¹, by rw [map_mul, map_inv₀, map_pow, map_pow, hy], Or.inr ?_⟩
  rw [Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (pow_ne_zero _ hy0) (inv_ne_zero (pow_ne_zero _ hy0)), Formalism.DivisionValues.ValuationRepresentative.vw_inv,
    ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0, ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_npow w hy0, hv]
  rw [hv] at hv0
  have : (0 : ℝ) ≤ (n : ℝ) * vw w y := mul_nonneg (Nat.cast_nonneg _) (by linarith)
  push_cast
  linarith

theorem rank_le {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t : T) (P : Pl D.host.E) {i j : ℕ}
    (hi : i ≤ D.R.m) (hj : j ≤ D.R.m) : (locGrid G t P).rank (i, j) ≤ bigN D := by
  have h1 := Nat.mul_le_mul_right D.R.t hj
  have h2 := Nat.mul_le_mul_right (sLen D) hi
  have hr : D.R.r ≤ D.R.k + D.R.m := by
    have : D.R.r = D.R.k + D.R.m - 1 := rfl
    omega
  change D.R.r + j * D.R.t + i * sLen D ≤ D.R.k + D.R.m * (D.R.t + sLen D + 1)
  nlinarith

end Val

theorem moved_loss : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ),
    HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ∀ β ∈ ch.S.supp t Φ, ∀ (P : locPl ch.G t),
    (P : Pl D.host.E) ∈ ch.G.pl.W0 → ∀ (w : PlL D) (c : ℝ), 0 ≤ c → (∀ z, LossLe w (Tflip ch.W ch.S.B t Φ P z) c) →
    ∀ z, LossLe w (moved (locGrid ch.G t P) (keepAt ch.G P) ((repsAt ch.G t P).elt (β P)) (Tflip ch.W ch.S.B t Φ P) z)
      (c + (D.R.m : ℝ) ^ 2 * (bigN D : ℝ) ^ 2 * (cosExp ch.G P : ℝ) * (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ)) := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch large₂ F CF b hS _ _ hF t Φ β hβ P hW w c _ hT z
  classical
  have hL : R.toLevCh.Is A.μ0 := hS.core.lev
  have hde := Test.pde_ne_q hS
  have hc' : ∀ Q ∈ R.toLevCh.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal :=
    GlobalTheory.RowTest.guard_of_qGuard hS.guard t
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have hTT := isTensor_Tflip hL ch.W ch.S.B t Φ hde hc' P.2
  have hcond : HasConductor (psiAt ch.W P.1) 1 :=
    (((Good.locGrid_isGood hL ch.G ch.W t hde hc').1 P.1 P.2).square 0 hm 0 hm).cond
  haveI := (isUnitVol_unitVol P.1).1
  set e := cosExp ch.G P with he
  have hdep : depthAt ch.G P = e := by
    obtain ⟨v, hv, hvP⟩ := Finset.mem_image.1 hW
    have := depthAt_w ch.G hv
    rw [he, ← hvP, this.1, this.2]
  rw [hdep] at hTT
  have hkeep : keepAt ch.G P = false := by simp [keepAt, hW]
  have hO := oneCoset one_le_sLen (psiAt ch.W P.1) (unitVol P.1) (givenLevel ch.G t P) (Tflip ch.W ch.S.B t Φ P) (unifAt P.1) e
    D.R.m_even (isUnif_unifAt P.1) hcond hTT (fun j hj _ => ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.givenLevel_KO ch.G t P hj)
  have hb : β P ∈ unfSupport (psiAt ch.W P.1) (unitVol P.1) false
      (Reps.through one_le_sLen (givenLevel ch.G t P) (stair (locGrid ch.G t P) (unifAt P.1) e)) (Tflip ch.W ch.S.B t Φ P) := by
    have := hβ P
    rw [hkeep] at this
    exact this
  have hβ' := funext (hO _ hb)
  have hdet : ∀ X, ∃ a : ℕ, gdet ((repsAt ch.G t P).elt (β P) X) = unifAt P.1 ^ a ∧
      a ≤ (locGrid ch.G t P).rank X * (e * D.R.m) := fun X => by
    rw [hβ']
    exact gdet_elt (G := locGrid ch.G t P) one_le_sLen _ _ _ X
  generalize (repsAt ch.G t P).elt (β P) = g at hdet ⊢
  have hq := ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.resCard_ne P.1
  have hsq : ((Real.sqrt (resCard (Kw (P : Pl D.host.E)) : ℕ) : ℝ) : ℂ) ∈ Set.range D.what₂.embLL := by
    rw [ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.ResCardPlace.resCard_Kw]
    exact hF.sqrt P.1 (Or.inr ⟨t, P.2⟩)
  set v : ℝ := (vw w ((resCard (Kw (P : Pl D.host.E)) : ℕ) : D.what₂.LL) : ℝ) with hv
  have hv0 : 0 ≤ v := by rw [hv]; exact_mod_cast ResidueCardinalityNilpotence.GlobalTheory.CompanionTheory.VolVal.vw_nat_nonneg w _
  rw [hkeep, moved_false]
  have hP := lossLe_list_prod (w := w) (fun b : Edge => apow (gdet (g b.src))⁻¹ (((locGrid ch.G t P).rank b.tgt : ℂ) / 2) *
      apow (gdet (g b.tgt))⁻¹ (-((locGrid ch.G t P).rank b.src : ℂ) / 2))
      ((bigN D * (e * D.R.m) * bigN D : ℕ) * v / 2) (oppositePath (locGrid ch.G t P).m) (fun b hb => by
    have hr : (locGrid ch.G t P).rank b.src ≤ bigN D ∧ (locGrid ch.G t P).rank b.tgt ≤ bigN D := by
      change b ∈ oppositePath D.R.m at hb
      simp only [oppositePath, List.mem_append, List.mem_map, List.mem_range, List.mem_reverse] at hb
      rcases hb with ⟨i, hi, rfl⟩ | ⟨j, hj, rfl⟩
      · exact ⟨rank_le _ _ _ hi.le le_rfl, rank_le _ _ _ hi le_rfl⟩
      · exact ⟨rank_le _ _ _ le_rfl hj, rank_le _ _ _ le_rfl hj.le⟩
    obtain ⟨a, ha, -⟩ := hdet b.src
    obtain ⟨a', ha', hle⟩ := hdet b.tgt
    rw [ha, ha', neg_div, apow_neg, apow_half (isUnif_unifAt P.1), apow_half (isUnif_unifAt P.1)]
    refine (lossLe_sqrt hq hsq _ _).mono ?_
    have h1 : a' * (locGrid ch.G t P).rank b.src ≤ bigN D * (e * D.R.m) * bigN D :=
      Nat.mul_le_mul (hle.trans (Nat.mul_le_mul_right _ hr.2)) hr.1
    have h2 : ((a' * (locGrid ch.G t P).rank b.src : ℕ) : ℝ) ≤ (bigN D * (e * D.R.m) * bigN D : ℕ) := by exact_mod_cast h1
    have h3 := mul_le_mul_of_nonneg_right h2 hv0
    rw [← hv]
    linarith)
  refine (lossLe_mul hP (hT _)).mono (le_of_eq ?_)
  have hlen : (oppositePath (locGrid ch.G t P).m).length = 2 * D.R.m := by
    change (oppositePath D.R.m).length = _
    simp [oppositePath]; ring
  rw [hlen]
  push_cast
  ring

end GlobalTheory.UnfoldLoss.MovedChosen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedVacuaRatioAlgebraicUnitEveryPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

namespace GlobalTheory.VacRatio

theorem det_int {D : D7} {N N' r : ℕ} (p : ℕ) {b₁ b₂ : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    (hb₁ : OnB D b₁) (h₁ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₁)
    (h₂ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₂) :
    ∃ S : ℕ, Nat.Coprime S p ∧
      IsIntegral ℤ ((S : D.host.E) * (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E)) := by
  have key : ∀ j, ∃ t : ℕ, Nat.Coprime t p ∧ ∃ c : Fin r → 𝓞 D.host.K,
      ∀ i, (t : D.host.K) * hYY D (b₂ j) (b₁ i) = (c i : D.host.K) := by
    intro j
    obtain ⟨s, hs, hmem⟩ := h₂.2.1 j
    obtain ⟨s', hs', c, hc⟩ := h₁.2.2 _ hmem
    refine ⟨s' * s, Nat.Coprime.mul hs' hs, c, fun i => ?_⟩
    have e1 : hYY D ((s' : D.host.E) • (s : D.host.E) • b₂ j) (b₁ i) =
        ((s' * s : ℕ) : D.host.K) * hYY D (b₂ j) (b₁ i) := by
      rw [smul_smul, ← Nat.cast_mul, Nat.cast_smul_eq_nsmul]
      change GlobalTheory.NormSum.hYYLeft D (b₁ i) _ = _
      rw [map_nsmul, nsmul_eq_mul]
      rfl
    have e2 : hYY D (∑ k, (((c k : D.host.K) : D.host.E)) • b₁ k) (b₁ i) = (c i : D.host.K) := by
      change GlobalTheory.NormSum.hYYLeft D (b₁ i) _ = _
      rw [map_sum]
      have : ∀ k, GlobalTheory.NormSum.hYYLeft D (b₁ i) ((((c k : D.host.K) : D.host.E)) • b₁ k) =
          if k = i then (c i : D.host.K) else 0 := by
        intro k
        rw [show (((c k : D.host.K) : D.host.E)) • b₁ k = (c k : D.host.K) • b₁ k from
          algebraMap_smul D.host.E (c k : D.host.K) (b₁ k), map_smul]
        change (c k : D.host.K) • hYY D (b₁ k) (b₁ i) = _
        rw [hb₁.1 k i]
        split_ifs with h
        · subst h; simp
        · simp
      simp only [this]
      simp
    rw [← e1, hc, e2]
  choose t ht c hc using key
  refine ⟨∏ j, t j, Nat.Coprime.prod_left fun j _ => ht j, ?_⟩
  let M' : Matrix (Fin r) (Fin r) (𝓞 D.host.K) := Matrix.of fun i j => c j i
  have hM : (algebraMap (𝓞 D.host.K) D.host.K).mapMatrix M' =
      Matrix.of fun i j => (t j : D.host.K) * hYY D (b₂ j) (b₁ i) := by
    ext i j
    simp [M', hc]
  have hdet : ((∏ j, t j : ℕ) : D.host.K) * (Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det =
      algebraMap (𝓞 D.host.K) D.host.K M'.det := by
    rw [RingHom.map_det, hM]
    have h := Matrix.det_mul_row (fun j => ((t j : ℕ) : D.host.K)) (Matrix.of fun i j => hYY D (b₂ j) (b₁ i))
    simp only [Matrix.of_apply] at h
    rw [h, Nat.cast_prod]
  have hint : IsIntegral ℤ (((∏ j, t j : ℕ) : D.host.K) * (Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det) := by
    rw [hdet]
    exact M'.det.isIntegral_coe
  have := hint.algebraMap (B := D.host.E)
  simpa using this

theorem det_unit {D : D7} (hG : admG1 D) {N N' r : ℕ} (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p])
    {b₁ b₂ : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb₁ : OnB D b₁) (hb₂ : OnB D b₂)
    (h₁ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₁) (h₂ : LocBasis D p (YYl D (stdL D N) (stdL D N')) b₂) :
    D.host.φ₀ (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E) ∈ Qbar ∧
      ‖lamC lam (D.host.φ₀ (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E))‖ = 1 := by
  have hc : ∀ (φ : D.host.E →+* ℂ) (z : D.host.E), φ (D.host.conj z) = starRingEnd ℂ (φ z) :=
    fun φ z => D.host.conjE_apply φ z
  set y : D.host.E := (((Matrix.of fun i j => hYY D (b₂ j) (b₁ i)).det : D.host.K) : D.host.E) with hy
  obtain ⟨S, hS, hint⟩ := det_int p hb₁ h₁ h₂
  rw [← hy] at hint
  have hn : y * D.host.conj y = 1 := GlobalTheory.NormSum.det_onB_mul_conj D hG N N' r b₁ b₂ hb₁ hb₂
  set x : ℂ := D.host.φ₀ y
  have hx1 : x * starRingEnd ℂ x = 1 := by
    have := congrArg D.host.φ₀ hn
    rwa [map_mul, hc, map_one] at this
  have hi1 : IsIntegral ℤ ((S : ℂ) * x) := by
    have := hint.map (D.host.φ₀ : D.host.E →+* ℂ).toIntAlgHom
    simpa [x] using this
  have hi2 : IsIntegral ℤ ((S : ℂ) * starRingEnd ℂ x) := by
    have := hi1.map (starRingEnd ℂ : ℂ →+* ℂ).toIntAlgHom
    simpa using this
  have hS0 : (S : ℂ) ≠ 0 := by
    have : S ≠ 0 := by
      rintro rfl
      have := Nat.Prime.one_lt (Fact.out : p.Prime)
      simp at hS
      omega
    exact_mod_cast this
  have a1 : GlobalTheory.ProductJets.AlgLe lam x 1 := by
    have := (GlobalTheory.ProductJets.AlgLe.inv_natCast (lam := lam) hS).mul (GlobalTheory.ProductJets.AlgLe.of_isIntegral (lam := lam) hi1)
    rwa [← mul_assoc, inv_mul_cancel₀ hS0, one_mul, one_mul] at this
  have a2 : GlobalTheory.ProductJets.AlgLe lam (starRingEnd ℂ x) 1 := by
    have := (GlobalTheory.ProductJets.AlgLe.inv_natCast (lam := lam) hS).mul (GlobalTheory.ProductJets.AlgLe.of_isIntegral (lam := lam) hi2)
    rwa [← mul_assoc, inv_mul_cancel₀ hS0, one_mul, one_mul] at this
  refine ⟨a1.1, ?_⟩
  have hprod : lamC lam x * lamC lam (starRingEnd ℂ x) = 1 := by
    rw [← GlobalTheory.BotFormula.lamC_mul lam a1.1 a2.1, hx1]
    have := GlobalTheory.ProductJets.lamC_coe (lam := lam) (1 : Qbar)
    simpa using this
  have hn2 := congrArg norm hprod
  rw [norm_mul, norm_one] at hn2
  have u1 := a1.2
  have u2 := a2.2
  have h0 := norm_nonneg (lamC lam x)
  have h0' := norm_nonneg (lamC lam (starRingEnd ℂ x))
  nlinarith

theorem qbar_of_pow {x : ℂ} {n : ℕ} (hn : 0 < n) (h : x ^ n ∈ Qbar) : x ∈ Qbar :=
  mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow hn (mem_algebraicClosure_iff.1 h))

theorem ratio_local {D : D7} (hI : GlobalTheory.NormSum.Inp D) {δ t0 : ℂ} (hC : Crv D ⊤ δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0) {a d : ℕ} {e₁ e₂ : VC D a d → ℂ}
    (h₁ : oddE0 D ⊤ δ t0 a d e₁) (h₂ : oddE0 D ⊤ δ t0 a d e₂) (hne : e₁ ≠ 0) {κ : ℂ} (hκ : e₂ = κ • e₁)
    (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : κ ∈ Qbar ∧ ‖lamC lam κ‖ = 1 := by
  have hG : admG1 D := hI.g1
  have hcop : Nat.Coprime (Ideal.absNorm (⊤ : Ideal (𝓞 D.host.K))) p := by simp
  obtain ⟨b₁, ε₁, hb₁, hl₁, hε₁, hn₁, -, he₁⟩ := h₁.2.2.2.2 p lam hcop
  obtain ⟨b₂, ε₂, hb₂, hl₂, hε₂, hn₂, -, he₂⟩ := h₂.2.2.2.2 p lam hcop
  have hP : pullB D (tor0 D ⊤ δ) b₁ (GL3Theta.th0 (lamOf D ⊤ δ) t0) ∈
      ThSp D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) := by
    obtain ⟨hd, hth⟩ := GlobalTheory.RatEquiv.theta_signed_translation D hG ⊤ δ hC t0 ht
    obtain ⟨-, -, hpar, hmem, -⟩ := GlobalTheory.OnCoord.coords_of_orthonormal_basis D hG ⊤ δ a d _ b₁ hb₁
    exact GlobalTheory.ProdTheta.pullB_mem_ThSp D _ a d _ b₁ _ hpar hmem hd hth
  have hK1 : KLat D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) := Or.inl ⟨_, b₁, hb₁, rfl⟩
  have hK2 : KLat D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₂) := Or.inl ⟨_, b₂, hb₂, rfl⟩
  have hK0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D a, GlobalTheory.NormSum.VacInt.sd_std D d, rfl⟩
  obtain ⟨c, ζ, m, hm, hζ, hc, hpull⟩ := GlobalTheory.UnitaryTheta.const_sq_eq_det D ⊤ δ hC t0 ht a d _ b₁ b₂ hb₁ hb₂
  obtain ⟨μ, hμ, hIμ⟩ := hI.mu ⊤ δ hC a d _ _ _ hK1 hK2 hK0 _ hP
  have E2 : e₂ = fun z => ε₂ * (c * (μ * Iop D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) (La0 D (tor0 D ⊤ δ) a d)
      (pullB D (tor0 D ⊤ δ) b₁ (GL3Theta.th0 (lamOf D ⊤ δ) t0)) z)) := by
    rw [he₂, hpull, GlobalTheory.RatEquiv.Iop_smul, hIμ]
  obtain ⟨z, hz⟩ : ∃ z, e₁ z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hz' := hz
  rw [he₁] at hz'
  have hJ : Iop D (tor0 D ⊤ δ) (LaB D (tor0 D ⊤ δ) b₁) (La0 D (tor0 D ⊤ δ) a d)
      (pullB D (tor0 D ⊤ δ) b₁ (GL3Theta.th0 (lamOf D ⊤ δ) t0)) z ≠ 0 := right_ne_zero_of_mul hz'
  have hε0 : ε₁ ≠ 0 := left_ne_zero_of_mul hz'
  have key : κ * ε₁ = ε₂ * c * μ := by
    have h := congrFun hκ z
    rw [Pi.smul_apply, smul_eq_mul, E2, he₁] at h
    apply mul_right_cancel₀ hJ
    linear_combination -h
  have hκe : κ = ε₂ * c * μ / ε₁ := by rw [eq_div_iff hε0, key]

  obtain ⟨hxQ, hx1⟩ := det_unit hG p lam hb₁ hb₂ hl₁ hl₂
  have hζQ : ζ ∈ Qbar := qbar_of_pow hm (by rw [hζ]; exact one_mem _)
  have hcQ : c ∈ Qbar := qbar_of_pow two_pos (by rw [hc]; exact mul_mem hζQ hxQ)
  have hμQ : μ ∈ Qbar := qbar_of_pow (n := 8) (by norm_num) (by rw [hμ]; exact one_mem _)
  have hκQ : κ ∈ Qbar := by rw [hκe]; exact div_mem (mul_mem (mul_mem hε₂ hcQ) hμQ) hε₁
  refine ⟨hκQ, ?_⟩

  have L := fun {u v : ℂ} (hu : u ∈ Qbar) (hv : v ∈ Qbar) => GlobalTheory.BotFormula.lamC_mul lam hu hv
  have one : lamC lam 1 = 1 := by
    have := GlobalTheory.ProductJets.lamC_coe (lam := lam) (1 : Qbar)
    simpa using this
  have pw : ∀ {u : ℂ} (hu : u ∈ Qbar) (n : ℕ), lamC lam (u ^ n) = lamC lam u ^ n := by
    intro u hu n
    induction n with
    | zero => simpa using one
    | succ n ih => rw [pow_succ, L (pow_mem hu n) hu, ih, pow_succ]
  have nμ : ‖lamC lam μ‖ = 1 := by
    have := congrArg norm (pw hμQ 8)
    rw [hμ, one, norm_one, norm_pow, eq_comm] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this
  have nζ : ‖lamC lam ζ‖ = 1 := by
    have := congrArg norm (pw hζQ m)
    rw [hζ, one, norm_one, norm_pow, eq_comm] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 this
  have nc : ‖lamC lam c‖ = 1 := by
    have := congrArg norm (pw hcQ 2)
    rw [hc, L hζQ hxQ, norm_mul, nζ, hx1, one_mul, norm_pow] at this
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 this.symm
  have hk : ‖lamC lam (κ * ε₁)‖ = ‖lamC lam (ε₂ * c * μ)‖ := by rw [key]
  rw [L hκQ hε₁, L (mul_mem hε₂ hcQ) hμQ, L hε₂ hcQ, norm_mul, norm_mul, norm_mul, hn₁, hn₂, nc, nμ] at hk
  simpa using hk

theorem vacuum_ratio_isAlgUnit : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ}, Crv D ⊤ δ → GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D ⊤ δ) t0 →
    ∀ {a d : ℕ} {e₁ e₂ : VC D a d → ℂ},
    oddE0 D ⊤ δ t0 a d e₁ → oddE0 D ⊤ δ t0 a d e₂ → ∃ ζ : ℂ, IsAlgUnit ζ ∧ e₂ = ζ • e₁ := by
  intro D hI δ t0 hC ht a d e₁ e₂ h₁ h₂
  have hG : admG1 D := hI.g1
  have hne : e₁ ≠ 0 := by
    intro h
    have hn := h₁.2.2.1
    rw [h] at hn
    have h0 : TaylorLogMetric.normSq D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) 0 = 0 := by simp [TaylorLogMetric.normSq]
    rw [h0] at hn
    exact pow_ne_zero _ (GlobalTheory.ConjJet.thetaZeroNormSq_ne_zero_cmLattice D hG ⊤ δ t0 hC ht) hn.symm
  obtain ⟨κ, hκ1, hκ⟩ := GlobalTheory.VacuumUnique.vacuum_unique hI hC h₁ h₂ hne
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    simp at hκ1
  haveI : Algebra.IsAlgebraic ℚ Qbar := algebraicClosure.isAlgebraic ℚ ℂ
  let lam2 : Qbar →+* ℂ_[2] := (IsAlgClosed.lift (R := ℚ) (S := Qbar) (M := ℂ_[2])).toRingHom
  refine ⟨κ, ⟨hκ0, (ratio_local hI hC ht h₁ h₂ hne hκ 2 lam2).1, fun p _ lam => ?_⟩, hκ⟩
  exact (ratio_local hI hC ht h₁ h₂ hne hκ p lam).2

end GlobalTheory.VacRatio

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped GlobalTheory.VacAny

noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_unramified_away_different : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, ¬ differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → PsiUnr ψ v := by
  first | exact @GlobalTheory.StdCharUnrF.psiUnr_of_not_le | exact GlobalTheory.StdCharUnrF.psiUnr_of_not_le | (intros; apply GlobalTheory.StdCharUnrF.psiUnr_of_not_le <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPointsMixMaximalMinorFockVectorsUnitaryStatement
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPoints_mix_maximalMinorFockVectors_unitary : ∀ {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} (P : Pair D cc δ t0 Q) (X : Data P), IsDict P X →
  ∀ k ∈ GinfC X.B, ∃ U : Matrix (Tup D P.a P.d P.n) (Tup D P.a P.d P.n) ℂ, U ∈ Matrix.unitaryGroup (Tup D P.a P.d P.n) ℂ ∧
    ∀ T, X.om (1, k) (X.fock T) = ∑ T', U T T' • X.fock T' := by
  first | exact @GlobalTheory.NormDict.RealB.real_mix | exact GlobalTheory.NormDict.RealB.real_mix | (intros; apply GlobalTheory.NormDict.RealB.real_mix <;> assumption)
end

