import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqShift
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0300
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0305
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0309
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsAdmissibleSplittingCharPairMulTwist
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0297
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0310
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolTop
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0311

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqNF
section
namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP2 MeasureTheory
open scoped ENNReal

noncomputable section

section sh

variable {P : M.Par} {Wp Wq Wq' : Type}
  [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  [NormedAddCommGroup Wq'] [InnerProductSpace ℂ Wq'] [FiniteDimensional ℂ Wq']
  {u u' : ℕ → ℝ}

theorem fpmSh_eq_fpm (q : KB.Pl (shP P u u') Wp Wq') (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)) (p₀ : ℕ) :
    fpmSh q f A p₀ = TBBx4.fpm q (fun g => (f g).comp (A g)) (fun _ => ContinuousLinearMap.id ℂ Wq') p₀ := by
  first
  | rfl
  | (unfold fpmSh; rfl)
  | unfold fpmSh

theorem inCC_compSh (q : KB.Pl (shP P u u') Wp Wq') {f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)}
    {A : B.Mat P.k P.r → (Wq' →L[ℂ] Wq)} {A₀ : ℝ} {d : ℕ} (hf : ∀ m : ℕ, B.InCC A₀ m f) (hA : PolyOp d A) :
    ∀ m : ℕ, B.InCC (A₀ - d) m (fun g => (f g).comp (A g)) := by
  intro m
  have h := shifted_decay P Wp Wq Wq' u u' q f A A₀ d 0 hf hA m
  simp only [mul_zero, Nat.cast_zero, sub_zero] at h
  first
  | exact h
  | (convert h using 2; rw [fpmSh_eq_fpm]; simp [TBBx4.fpm])
  | (convert h using 2; rw [fpmSh_eq_fpm]; unfold TBBx4.fpm)

end sh

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem ptBound_main_limEvT (hA : P5.ThmPActual) (Cb : ℝ) : ∃ C₂ c₃ Cc Cc' : ℝ, 0 < C₂ ∧
    ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (q : KB.Pl P Wp Wq)
      (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Λ A : ℝ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      1 ≤ Λ → 3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P q.l0 q.T.base Cb q.Θ → B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      TBBx5.WaveGrid q nn Y Λ K N → TBBx5.LiftGrid q nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound q nn (apx (D.cutF q.T.base χ F ε) n) Y K N) →
      LimEvT q χ F Y N →
      LimBd q nn F Y N → TBB.PtBound q F (1 * (C₂ * Λ ^ 2) ^ (P.r + 1)) := by
  obtain ⟨C₂, hC₂, hPt⟩ := ptBound_dec_all hA
  obtain ⟨c₃, hc₃⟩ := limTopN_cut_of_inCC
  obtain ⟨Cc, hCc⟩ := limZeroN_of_formLimit Cb
  obtain ⟨Cc', hE⟩ := limE_of_limEvT hA Cb
  refine ⟨C₂, c₃, Cc, Cc', hC₂, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P q F Λ A χ nn Y K N hΛ hK hKN hχ hnn hCb hF hFA hth1 hth2 hth3 hWG hLG hI5 hLim hBd
  exact hPt Wp Wq P q F Λ 1 χ nn Y K N Cb hΛ one_pos hK hKN hχ hnn hCb hF hWG hLG hI5
    (hc₃ Wp Wq P q nn χ F A hth1 hχ hFA hF)
    (fun ε hε => hCc Wp Wq P q F χ ε A N nn Y hCb hχ hε hF hFA hth2)
    (hE Wp Wq P q F χ nn A N Y hCb hχ (fun y => (hnn y).le) hF hFA hth3 hLim hBd)
    (lemB_one q F)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_eq_limEvT (hA : P5.ThmPActual) (hN : NormAtShOfAmaps) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ)
    (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' : ℝ, ∀ (P : M.Par) (Wp Wq Wqp Wqm : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      [NormedAddCommGroup Wqp] [InnerProductSpace ℂ Wqp] [FiniteDimensional ℂ Wqp]
      [NormedAddCommGroup Wqm] [InnerProductSpace ℂ Wqm] [FiniteDimensional ℂ Wqm]
      (up up' um um' : ℕ → ℝ) (p : KB.Pl P Wp Wq) (pp : KB.Pl (shP P up up') Wp Wqp)
      (pm : KB.Pl (shP P um um') Wp Wqm) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
      (Ap : B.Mat P.k P.r → (Wqp →L[ℂ] Wq)) (Am : B.Mat P.k P.r → (Wqm →L[ℂ] Wq))
      (ApPt : C.LPt → (Wqp →L[ℂ] Wq)) (AmPt : C.LPt → (Wqm →L[ℂ] Wq)) (b Λ A₁ : ℝ) (n₀ p₀ : ℕ)
      (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      pp.T.base.z = p.T.base.z → pp.T.base.z' = p.T.base.z' →
      pm.T.base.z = p.T.base.z → pm.T.base.z' = p.T.base.z' →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P up up') pp.l0 pp.T.base Cb pp.Θ → KB.InDDplus2 (shP P um um') pm.l0 pm.T.base Cb pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → B.CkOn ⊤ (B.GV P.k P.r) Ap → B.CkOn ⊤ (B.GV P.k P.r) Am →
      (∀ m : ℕ, B.InCC A₁ m (fpmSh pp f Ap p₀)) → (∀ m : ℕ, B.InCC A₁ m (fpmSh pm f Am p₀)) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤ A₁ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₁ →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₁ →
      AmapsSh p pp pm f Ap Am ApPt AmPt b n₀ → BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid pp nnp Yp Λ K N → TBBx5.LiftGrid pp nnp Yp Λ K N →
      TBBx5.WaveGrid pm nnm Ym Λ K N → TBBx5.LiftGrid pm nnm Ym Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pp nnp (apx (D.cutF pp.T.base χ (fpmSh pp f Ap p₀) ε) n) Yp K N) →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound pm nnm (apx (D.cutF pm.T.base χ (fpmSh pm f Am p₀) ε) n) Ym K N) →
      LimEvT pp χ (fpmSh pp f Ap p₀) Yp N →
      LimEvT pm χ (fpmSh pm f Am p₀) Ym N →
      LimBd pp nnp (fpmSh pp f Ap p₀) Yp N → LimBd pm nnm (fpmSh pm f Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₂, c₃, Cc, Cc', hC₂, hPt⟩ := ptBound_main_limEvT hA Cb
  obtain ⟨C₄, hC₄⟩ := thmBpOfPartsSh C₃ CΛ C₀ C₂ 0 hC₃ hCΛ hC₀ hC₂
  refine ⟨C₄, c₃, Cc, Cc', ?_⟩
  intro P Wp Wq Wqp Wqm _ _ _ _ _ _ _ _ _ _ _ _ up up' um um' p pp pm f Ap Am ApPt AmPt b Λ A₁ n₀ p₀ χ nnp nnm
    Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hzp hzp' hzm hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf hAp hAm hdp hdm hth1 hth2
    hth3 hAms hexp hWGp hLGp hWGm hLGm hI5p hI5m hDp hDm hBdp hBdm
  have hNorm := hN P Wp Wq Wqp Wqm up up' um um' p pp pm f Ap Am ApPt AmPt b n₀ p₀ hzp hzp' hzm hzm' hAms
  have hReg := Formalism.FourierDecayAlt.P.regularity_at_place p f b C₃ (2 * p₀ + n₀) (by linarith) hexp
  have hPp := hPt Wp Wqp (shP P up up') pp (fpmSh pp f Ap p₀) Λ A₁ χ nnp Yp K N hΛ hK hKN hχ hnnp hDDp
    (ckOn_fpmSh pp p₀ hf hAp) hdp hth1 hth2 hth3 hWGp hLGp hI5p hDp hBdp
  have hPm := hPt Wp Wqm (shP P um um') pm (fpmSh pm f Am p₀) Λ A₁ χ nnm Ym K N hΛ hK hKN hχ hnnm hDDm
    (ckOn_fpmSh pm p₀ hf hAm) hdm hth1 hth2 hth3 hWGm hLGm hI5m hDm hBdm
  exact hC₄ P Wp Wq Wqp Wqm up up' um um' p pp pm f _ _ b Λ 1 n₀ p₀ hb hΛ hΛb one_pos (by simp) hT hn₀ hp₀
    (ttp_eq p pp hzp hzp') (ttp_eq p pm hzm hzm') hNorm hPp hPm hReg

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_eq_NF (hA : P5.ThmPActual) (h1 : NFTopFormAll) (h2 : NFTopPtwAll) (h3 : NFTopDomAll)
    (h4 : NFTopIdAll) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc Cc' Cc'' : ℝ, ∀ (P : M.Par) (Wp Wq : Type)
      [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
      [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
      (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) (n₀ : ℕ) (S : ShiftAt p f b n₀)
      (Λ A₀ : ℝ) (p₀ : ℕ) (χ nnp nnm : ℝ → ℝ) (Yp Ym : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ Tq p →
      n₀ ≤ 30 * (P.r + 1) ^ 2 + 6 → (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nnp y) → (∀ y, 0 < nnm y) →
      KB.InDDplus2 (shP P S.up S.up') S.pp.l0 S.pp.T.base Cb S.pp.Θ →
      KB.InDDplus2 (shP P S.um S.um') S.pm.l0 S.pm.T.base Cb S.pm.Θ →
      B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀ →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀ →
      Cc' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀ →
      Cc'' * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀ →
      N ≤ 2 * p₀ →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + n₀) →
      TBBx5.WaveGrid S.pp nnp Yp Λ K N → TBBx5.LiftGrid S.pp nnp Yp Λ K N →
      TBBx5.WaveGrid S.pm nnm Ym Λ K N → TBBx5.LiftGrid S.pm nnm Ym Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
        TBB.BlockGrowthBound S.pp nnp (apx (D.cutF S.pp.T.base χ (fpmSh S.pp f S.Ap p₀) ε) n) Yp K N) →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ,
        TBB.BlockGrowthBound S.pm nnm (apx (D.cutF S.pm.T.base χ (fpmSh S.pm f S.Am p₀) ε) n) Ym K N) →
      LimBd S.pp nnp (fpmSh S.pp f S.Ap p₀) Yp N → LimBd S.pm nnm (fpmSh S.pm f S.Am p₀) Ym N →
      ThmBpAt p f b C₄ n₀ p₀ := by
  obtain ⟨C₄, c₃, Cc, Cc', h⟩ :=
    thmBpAt_eq_limEvT hA Formalism.FourierDecayAlt.P.CutBP2.normaliser_across_places Cb C₃ CΛ C₀ hC₃ hCΛ hC₀
  obtain ⟨Cn, hn⟩ := limEvT_fpm_of_NF hA h1 h2 h3 h4 Cb
  refine ⟨C₄, c₃, Cc, Cc', Cn, ?_⟩
  intro P Wp Wq _ _ _ _ _ _ p f b n₀ S Λ A₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ hK hKN hχ hnnp hnnm hDDp
    hDDm hf hfA hth1 hth2 hth3 hth4 hN2 hexp hWGp hLGp hWGm hLGm hI5p hI5m hBdp hBdm
  have hth4' : Cn * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      (A₀ - n₀) - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) := by linarith
  have hLp : LimEvT S.pp χ (fpmSh S.pp f S.Ap p₀) Yp N := by
    have e := fpmSh_eq_fpm S.pp f S.Ap p₀
    have k := hn Wp S.Wqp (shP P S.up S.up') S.pp (fun g => (f g).comp (S.Ap g)) (A₀ - n₀) p₀ χ Yp N
      ⟨hχ, hDDp, ckOn_compSh hf (ckOn_of_polyOp S.polyP), inCC_compSh S.pp hfA S.polyP, hth4', hN2⟩
    exact Eq.mpr (congrArg (fun F => LimEvT S.pp χ F Yp N) e) k
  have hLm : LimEvT S.pm χ (fpmSh S.pm f S.Am p₀) Ym N := by
    have e := fpmSh_eq_fpm S.pm f S.Am p₀
    have k := hn Wp S.Wqm (shP P S.um S.um') S.pm (fun g => (f g).comp (S.Am g)) (A₀ - n₀) p₀ χ Ym N
      ⟨hχ, hDDm, ckOn_compSh hf (ckOn_of_polyOp S.polyM), inCC_compSh S.pm hfA S.polyM, hth4', hN2⟩
    exact Eq.mpr (congrArg (fun F => LimEvT S.pm χ F Ym N) e) k
  exact h P Wp Wq S.Wqp S.Wqm S.up S.up' S.um S.um' p S.pp S.pm f S.Ap S.Am S.ApPt S.AmPt b Λ
    (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - n₀) n₀ p₀ χ nnp nnm Yp Ym K N hb hΛ hΛb hT hn₀ hp₀ S.hzp S.hzp' S.hzm
    S.hzm' hK hKN hχ hnnp hnnm hDDp hDDm hf (ckOn_of_polyOp S.polyP) (ckOn_of_polyOp S.polyM)
    (shifted_decay P Wp Wq S.Wqp S.up S.up' S.pp f S.Ap A₀ n₀ p₀ hfA S.polyP)
    (shifted_decay P Wp Wq S.Wqm S.um S.um' S.pm f S.Am A₀ n₀ p₀ hfA S.polyM)
    hth1 hth2 hth3 S.amaps hexp hWGp hLGp hWGm hLGm hI5p hI5m hLp hLm hBdp hBdm

end

end Formalism.FourierDecayAlt.P.CutBPEq
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFBddPtw
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

theorem pointwise_bound_normal_form_holds : NFBddPtw := by
  intro P L hTT hL b hb
  obtain ⟨C, Mx, hSA, hC, hM⟩ := Formalism.FourierDecayAlt.P.MAx3.AD.SAB_closure (hTTp := hTT) (hL := hL)
    (hLaw := Formalism.FourierDecayAlt.P.analytic_laws P.r P.TT hTT.le) hb
  refine ⟨(Fintype.card (M.Ty P) : ℝ) * ((Fintype.card (M.Ty P) : ℝ) * C ^ 2), fun u q => ?_⟩
  have key : ∀ ρ, ‖MA.evQ P (MA.actA P b u ρ) q‖ ^ 2 ≤
      (Fintype.card (M.Ty P) : ℝ) * (C ^ 2 * ∑ ρ', ‖MA.evQ P (u ρ') q‖ ^ 2) := by
    intro ρ
    rw [hSA.1 u q ρ]
    have h1 : ‖∑ π', Mx q ρ π' * MA.evQ P (u π') q‖ ≤ ∑ π', C * ‖MA.evQ P (u π') q‖ := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun π' _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hM q ρ π') (norm_nonneg _)
    have h2 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (M.Ty P)))
      (f := fun π' => C * ‖MA.evQ P (u π') q‖)
    calc _ ≤ (∑ π', C * ‖MA.evQ P (u π') q‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ = _ := by
        rw [Finset.card_univ]
        simp only [mul_pow, ← Finset.mul_sum]
  calc _ ≤ ∑ ρ : M.Ty P, (Fintype.card (M.Ty P) : ℝ) * (C ^ 2 * ∑ ρ', ‖MA.evQ P (u ρ') q‖ ^ 2) :=
        Finset.sum_le_sum fun ρ _ => key ρ
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFCoreNExt
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

theorem nf_coef_unique {E : Type*} [AddCommGroup E] [Module ℂ E] (M : ℕ) (a : ℕ → E) (S : Set ℂ)
    (hS : S.Infinite) (h : ∀ s ∈ S, ∑ i ∈ Finset.range M, s ^ i • a i = 0) : ∀ i < M, a i = 0 := by
  intro i hi
  refine (Module.forall_dual_apply_eq_zero_iff ℂ (a i)).mp fun f => ?_
  have hp : (∑ j ∈ Finset.range M, Polynomial.C (f (a j)) * Polynomial.X ^ j) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ hS
    intro s hs
    have hfs := congrArg f (h s hs)
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at hfs
    simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_finset_sum, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    rw [← hfs]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hc := congrArg (fun q => Polynomial.coeff q i) hp
  simpa [Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Finset.mem_range.mpr hi] using hc

section scoef

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nf_sum_pad {E : Type*} [AddCommGroup E] [Module ℂ E] {Q M : ℕ} (hQ : Q + 1 ≤ M) (x : ℂ)
    (u : Fin (Q + 1) → E) :
    ∑ i ∈ Finset.range M, x ^ i • (if h : i < Q + 1 then u ⟨i, h⟩ else 0) = ∑ q : Fin (Q + 1), x ^ (q : ℕ) • u q := by
  have h1 : ∑ i ∈ Finset.range (Q + 1), x ^ i • (if h : i < Q + 1 then u ⟨i, h⟩ else 0) =
      ∑ q : Fin (Q + 1), x ^ (q : ℕ) • u q := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [q.isLt]
  rw [← h1]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ hi
    have hi' : ¬ i < Q + 1 := by simpa using hi
    rw [dif_neg hi', smul_zero]

theorem nf_scoef_unique (p : KB.Pl P Wp Wq) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) {Q Q' : ℕ}
    {L : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq} {L' : Fin (Q' + 1) → B.DiffOp P.k P.r Wp Wq}
    (hS : IsSCoef p w e Q L) (hS' : IsSCoef p w e Q' L') (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : B.CkOn ⊤ (B.GV P.k P.r) F) (g : B.Mat P.k P.r) (hg : g ∈ C6.domL p.T.base ∅) (qq : Fin (Q + 1)) :
    B.opApply (L qq) F g = if h : (qq : ℕ) ≤ Q' then B.opApply (L' ⟨qq, by omega⟩) F g else 0 := by
  have hq1 : Q + 1 ≤ max Q Q' + 1 := Nat.succ_le_succ (le_max_left _ _)
  have hq2 : Q' + 1 ≤ max Q Q' + 1 := Nat.succ_le_succ (le_max_right _ _)
  have key : ∀ s : ℝ, ∑ q : Fin (Q + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L q) F g =
      ∑ q : Fin (Q' + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L' q) F g := by
    intro s
    have h1 := hS s F hF g hg
    have h2 := hS' s F hF g hg
    rw [h1] at h2
    simpa [Complex.ofReal_pow] using h2
  have hz := nf_coef_unique (max Q Q' + 1)
    (fun i => (if h : i < Q + 1 then B.opApply (L ⟨i, h⟩) F g else 0) -
      (if h : i < Q' + 1 then B.opApply (L' ⟨i, h⟩) F g else 0))
    (Set.range (fun s : ℝ => (s : ℂ))) (Set.infinite_range_of_injective Complex.ofReal_injective) ?_ qq
    (lt_of_lt_of_le qq.isLt hq1)
  · simp only [sub_eq_zero] at hz
    rw [dif_pos qq.isLt] at hz
    by_cases hq : (qq : ℕ) ≤ Q'
    · rw [dif_pos hq]
      rw [dif_pos (by omega : (qq : ℕ) < Q' + 1)] at hz
      exact hz
    · rw [dif_neg hq]
      rw [dif_neg (by omega : ¬ (qq : ℕ) < Q' + 1)] at hz
      exact hz
  · rintro _ ⟨s, rfl⟩
    have e1 : ∑ i ∈ Finset.range (max Q Q' + 1),
        (s : ℂ) ^ i • (if h : i < Q + 1 then B.opApply (L ⟨i, h⟩) F g else 0) =
        ∑ q : Fin (Q + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L q) F g :=
      nf_sum_pad hq1 (s : ℂ) (fun q => B.opApply (L q) F g)
    have e2 : ∑ i ∈ Finset.range (max Q Q' + 1),
        (s : ℂ) ^ i • (if h : i < Q' + 1 then B.opApply (L' ⟨i, h⟩) F g else 0) =
        ∑ q : Fin (Q' + 1), (s : ℂ) ^ (q : ℕ) • B.opApply (L' q) F g :=
      nf_sum_pad hq2 (s : ℂ) (fun q => B.opApply (L' q) F g)
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [e1, e2, key s, sub_self]

end scoef

section extract

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem nf_xD_pow (b : ℕ) : xD (fun x : ℝ => x ^ b) = fun x => (b : ℝ) * x ^ b := by
  funext x
  show x * deriv (fun x : ℝ => x ^ b) x = (b : ℝ) * x ^ b
  rw [(hasDerivAt_pow b x).deriv]
  rcases b with _ | b
  · simp
  · simp only [Nat.add_sub_cancel]
    push_cast
    ring

theorem nf_xD_const_mul (c : ℝ) (φ : ℝ → ℝ) : xD (fun x => c * φ x) = fun x => c * xD φ x := by
  funext x
  show x * deriv (fun x => c * φ x) x = c * (x * deriv φ x)
  rw [deriv_const_mul_field]
  ring

theorem nf_xD_iter_pow (b q : ℕ) : xD^[q] (fun x : ℝ => x ^ b) = fun x => (b : ℝ) ^ q * x ^ b := by
  induction q with
  | zero => funext x; simp
  | succ q ih =>
    rw [Function.iterate_succ_apply', ih]
    have h1 := nf_xD_const_mul ((b : ℝ) ^ q) (fun x => x ^ b)
    rw [h1, nf_xD_pow]
    funext x
    push_cast
    ring

private theorem sum_pow_mul_choose_eq_add_pow (Q' p₀ : ℕ) (s : ℂ) (j : Fin (Q' + 1)) :
    ∑ q : Fin (Q' + 1), s ^ (q : ℕ) * ((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ) =
      ((p₀ : ℂ) + s) ^ (j : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range (fun q => s ^ q * ((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ)),
    show (p₀ : ℂ) + s = s + p₀ from add_comm _ _, add_pow]
  have hterm : ∀ m, s ^ m * ((Nat.choose j m * p₀ ^ ((j : ℕ) - m) : ℕ) : ℂ) =
      s ^ m * (p₀ : ℂ) ^ ((j : ℕ) - m) * (Nat.choose j m : ℂ) := by
    intro m
    push_cast
    ring
  simp only [hterm]
  symm
  apply Finset.sum_subset
  · intro i hi
    simp only [Finset.mem_range] at hi ⊢
    omega
  · intro i _ hi
    have hji : (j : ℕ) < i := by simpa using hi
    simp [Nat.choose_eq_zero_of_lt hji]

private theorem coeff_eq_zero_of_sum_pow_smul_eq_zero_nat {E : Type*} [AddCommGroup E] [Module ℂ E] {Q' : ℕ}
    (w : Fin (Q' + 1) → E) (h : ∀ s : ℕ, ∑ q : Fin (Q' + 1), ((s : ℂ) ^ (q : ℕ)) • w q = 0)
    (qq : Fin (Q' + 1)) : w qq = 0 := by
  have hS : (Set.range (Nat.cast : ℕ → ℂ)).Infinite :=
    Set.infinite_range_of_injective Nat.cast_injective
  have := nf_coef_unique (Q' + 1) (fun i => if hi : i < Q' + 1 then w ⟨i, hi⟩ else 0) _ hS
    (fun x hx => by
      obtain ⟨s, rfl⟩ := hx
      rw [nf_sum_pad le_rfl]
      exact h s) qq qq.isLt
  simpa [Nat.lt_succ_iff.mp qq.isLt] using this

theorem nf_vExtract (p : KB.Pl P Wp Wq) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) {Q' : ℕ}
    (L' : Fin (Q' + 1) → B.DiffOp P.k P.r Wp Wq) (CcL : ℝ)
    (hLe : ∀ φ : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ),
      B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
      CcL * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
      ∀ γ : C.LPt, D.IsLocPt γ (P.r + 1) → 0 < TBB.Gp p γ →
        p.V (p.Θ.Θ w e (fun g => ((φ (Gf P.k P.r p.T.base.z p.T.base.z' g) : ℝ) : ℂ) • F g)) γ =
          ∑ q : Fin (Q' + 1), (((xD^[(q : ℕ)] φ) (TBB.Gp p γ) : ℝ) : ℂ) • p.V (B.opApply (L' q) F) γ)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (hf : B.CkOn ⊤ (B.GV P.k P.r) f)
    (hcc : ∀ m : ℕ, B.InCC A₀ m f)
    (hthr : CcL * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
      A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ))
    (γ : C.LPt) (hl : D.IsLocPt γ (P.r + 1)) (hG : 0 < TBB.Gp p γ) (qq : Fin (Q' + 1)) :
    p.V (B.opApply (L' qq) (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀)) γ =
      ((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
        (((Nat.choose j qq * p₀ ^ ((j : ℕ) - qq) : ℕ) : ℂ)) • p.V (B.opApply (L' j) f) γ := by
  have hfp := fpm_id p f p₀
  rw [hfp]
  have hthr0 : CcL * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A₀ := hthr.trans (sub_le_self _ (Nat.cast_nonneg _))
  have hck : B.CkOn ⊤ (B.GV P.k P.r)
      (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g) :=
    ckOn_Gpow_smul _ _ p₀ hf
  have hcc' := inCC_fpm_id p p₀ hcc
  rw [hfp] at hcc'
  have hG0 : ((TBB.Gp p γ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hG.ne'
  have hsum_c : ∀ s : ℕ, ∑ q : Fin (Q' + 1), ((s : ℂ) ^ (q : ℕ)) •
      (((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
        (((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ)) • p.V (B.opApply (L' j) f) γ) =
      ((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
        (((p₀ : ℂ) + s) ^ (j : ℕ)) • p.V (B.opApply (L' j) f) γ := by
    intro s
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sum_pow_mul_choose_eq_add_pow Q' p₀ (s : ℂ) j, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun q _ => ?_
    congr 1
    ring
  have key : ∀ s : ℕ, ∑ q : Fin (Q' + 1), ((s : ℂ) ^ (q : ℕ)) •
      (p.V (B.opApply (L' q) (fun g => ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g)) γ -
        ((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) • ∑ j : Fin (Q' + 1),
          (((Nat.choose j q * p₀ ^ ((j : ℕ) - q) : ℕ) : ℂ)) • p.V (B.opApply (L' j) f) γ) = 0 := by
    intro s
    have e1 := hLe (fun x => x ^ s) (contDiff_id.pow s) _ _ hck hcc' hthr γ hl hG
    have e2 := hLe (fun x => x ^ (p₀ + s)) (contDiff_id.pow _) f A₀ hf hcc hthr0 γ hl hG
    simp only [nf_xD_iter_pow] at e1 e2
    have hH : (fun g => (((Gf P.k P.r p.T.base.z p.T.base.z' g) ^ s : ℝ) : ℂ) •
        ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ p₀ : ℝ) : ℂ) • f g) =
        (fun g => (((Gf P.k P.r p.T.base.z p.T.base.z' g) ^ (p₀ + s) : ℝ) : ℂ) • f g) := by
      funext g
      rw [smul_smul, ← Complex.ofReal_mul, ← pow_add, add_comm]
    rw [hH, e2] at e1
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [hsum_c s, sub_eq_zero]
    apply smul_right_injective _ (pow_ne_zero s hG0)
    simp only [Finset.smul_sum, smul_smul]
    have h3 : ∀ x : Fin (Q' + 1), ((TBB.Gp p γ : ℝ) : ℂ) ^ s * (s : ℂ) ^ (x : ℕ) =
        (((s : ℝ) ^ (x : ℕ) * TBB.Gp p γ ^ s : ℝ) : ℂ) := by
      intro x
      push_cast
      ring
    have h4 : ∀ x : Fin (Q' + 1), ((TBB.Gp p γ : ℝ) : ℂ) ^ s *
        (((TBB.Gp p γ ^ p₀ : ℝ) : ℂ) * ((p₀ : ℂ) + s) ^ (x : ℕ)) =
        (((((p₀ + s : ℕ) : ℝ)) ^ (x : ℕ) * TBB.Gp p γ ^ (p₀ + s) : ℝ) : ℂ) := by
      intro x
      push_cast
      ring
    simp only [h3, h4]
    exact e1.symm
  have := coeff_eq_zero_of_sum_pow_smul_eq_zero_nat _ key qq
  exact sub_eq_zero.mp this

end extract

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolAll
section
namespace Formalism.FourierDecayAlt.P.CutBP

theorem nfPolFormAll_of_top (hMeas : TopDMeasCpt) (hApx : NFApxDomAll) : NFPolFormAll :=
  nfPolFormAll_of (nfPolQuadAll_of hMeas hApx) pairing_middle_all_levels_holds top_middle_all_levels_holds

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopFormTDMAll
section
namespace Formalism.FourierDecayAlt.P.CutBP.TDM

theorem topDMeasCpt_of_typeNormMeas (h : TypeNormMeas) : TopDMeasCpt :=
  topDMeasCpt_of_parts h vector_positive_cone diff_operator_in_class_CC scalar_point_measurability_holds empty_list_measurability_holds

end Formalism.FourierDecayAlt.P.CutBP.TDM
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.NFModelNFg
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

def NFModelNFg : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ (l0 : ℕ) (Y : Finset ℝ) (w : List C.Letter), TBB.AdmW P l0 Y w → ∀ e : Wd.Ix (Fin w.length),
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (i i' : Fin m → ℕ) (h : Fin m → List (MA.A P (MA.DQ P))),
        (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ j, i j + i' j = w.length) ∧
        (∀ j, (h j).length = w.length ∧ ∀ a ∈ h j, a ∈ MA.hatSet P L) ∧
        ∑ e' : Wd.Ix (Fin w.length),
            (Fr.ofWord L (MA.startM P (MA.DQ P) l0) (D.positionted w)).F e e' *
              Wd.uw (MA.sites P (MA.DQ P)) (D.positionted w) e' =
          ∑ j, b j * L.Di ^ i j * L.Dbi ^ i' j * (h j).prod

end

end Formalism.FourierDecayAlt.P.CutBP
end

