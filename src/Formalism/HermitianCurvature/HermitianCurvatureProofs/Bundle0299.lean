import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0297
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0275
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormsJointContinuity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0112
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0249
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutDec
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0293

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopA
section
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

private theorem isLocPt_and_ptG_pos_of_vec_ne_zero {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Q : C.LPt) (hQ : p.V G Q ≠ 0) :
    D.IsLocPt Q (P.r + 1) ∧ 0 < D.ptG (TBB.TTp p) P.r Q := by
  by_contra hn
  exact hQ (by unfold KB.Pl.V D.vecV; exact dif_neg hn)

private theorem vecV_eq_zero_of_not_isLocPt {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (G : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (Q : C.LPt) (hQ : ¬ D.IsLocPt Q (P.r + 1)) :
    D.vecV p.T.base p.ν' p.m₀ G Q = 0 := by
  unfold D.vecV
  exact dif_neg fun hh => hQ hh.1

private theorem hsInner_zero_left_right_and_hsVec_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (X : Wq →L[ℂ] Wp) :
    B.hsInner 0 X = 0 ∧ B.hsInner X 0 = 0 ∧ B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  have h0 : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
    unfold B.hsVec
    rfl
  unfold B.hsInner
  rw [h0]
  exact ⟨inner_zero_right _, inner_zero_left _, rfl⟩

private theorem rr_succ_eq_ite_hsInner_else_leading {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (Q Q' : C.LPt) :
    p.RR F (P.r + 1) w Q Q' =
      if w = [] then B.hsInner (p.V F Q) (p.V F Q')
      else Top.topOf P p.l0 p.T p.ν' p.m₀ p.Θ p.TP F w Q Q' := by
  unfold KB.Pl.RR D.RRplace
  by_cases hl : D.IsLocPt Q (P.r + 1) ∧ D.IsLocPt Q' (P.r + 1)
  · rw [dif_pos hl, dif_neg (by omega), if_pos rfl]
    rfl
  · rw [dif_neg hl]
    have hz : ∀ G : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
        D.vecV p.T.base p.ν' p.m₀ G Q = 0 ∨ D.vecV p.T.base p.ν' p.m₀ G Q' = 0 := by
      intro G
      rcases not_and_or.mp hl with h | h
      · exact Or.inl (vecV_eq_zero_of_not_isLocPt p G Q h)
      · exact Or.inr (vecV_eq_zero_of_not_isLocPt p G Q' h)
    split_ifs with hw
    · rcases hz F with h | h
      · show (0 : ℂ) = B.hsInner (D.vecV p.T.base p.ν' p.m₀ F Q) (D.vecV p.T.base p.ν' p.m₀ F Q')
        rw [h, (hsInner_zero_left_right_and_hsVec_zero _).1]
      · show (0 : ℂ) = B.hsInner (D.vecV p.T.base p.ν' p.m₀ F Q) (D.vecV p.T.base p.ν' p.m₀ F Q')
        rw [h, (hsInner_zero_left_right_and_hsVec_zero _).2.1]
    · unfold Top.topOf
      symm
      refine Finset.sum_eq_zero fun e _ => Finset.sum_eq_zero fun ρ _ => ?_
      rcases hz (p.Θ.Θ w e F) with h | h
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).1, mul_zero]
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).2.1, mul_zero]

theorem top_level_gram : TopGram1 := by
  intro Wp Wq _ _ _ _ _ _ P p nn F w Cb hCb hF hw hnn
  have hnc : 0 < TBB.normC nn w := by
    unfold TBB.normC
    apply List.prod_pos
    intro a ha
    obtain ⟨l, -, rfl⟩ := List.mem_map.mp ha
    exact hnn l.2
  by_cases hw0 : w = []
  · subst hw0
    refine ⟨Unit, inferInstance, fun _ => 1 / TBB.normC nn [], fun _ => F,
      fun _ => GermRateSplit.hsLE (ContinuousLinearMap.id ℂ Wp), fun _ => by positivity, fun _ => hF, ?_⟩
    intro Q Q'
    rw [TBB.NP, rr_succ_eq_ite_hsInner_else_leading, if_pos rfl, Fintype.sum_unique, GermRateSplit.hsLE_apply, GermRateSplit.hsLE_apply,
      inner_smul_left, inner_smul_right, Complex.conj_ofReal]
    simp only [ContinuousLinearMap.id_comp, List.length_nil, omT, pow_zero, Real.sqrt_one, mul_one]
    unfold B.hsInner
    push_cast
    ring
  · have hT : ∀ e : Wd.Ix (Fin w.length), ∃ F', KB.CptCoef p.T.base F' ∧
        (∀ g ∈ C6.domL p.T.base ∅, p.Θ.Θ w e F g = F' g) ∧ ∀ a, p.V (p.Θ.Θ w e F) a = p.V F' a :=
      fun e => Formalism.FourierDecayAlt.P.theta_compact_support Wp Wq P p F w e Cb hCb hF hw
    choose G hG _ hGV using hT
    refine ⟨Wd.Ix (Fin w.length) × M.Ty P, inferInstance,
      fun i => √(Top.cW P p.l0 w i.1 i.2).re * √(Top.cW P p.l0 w i.1 i.2).re / TBB.normC nn w,
      fun i => G i.1, fun i => GermRateSplit.hsLE (p.TP.E i.2), fun i => by positivity, fun i => hG i.1, ?_⟩
    intro Q Q'
    rw [TBB.NP, rr_succ_eq_ite_hsInner_else_leading, if_neg hw0]
    unfold Top.topOf
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hV : ∀ a, D.vecV p.T.base p.ν' p.m₀ (p.Θ.Θ w e F) a = p.V (G e) a := hGV e
    rw [hV, hV, GermRateSplit.hsLE_apply, GermRateSplit.hsLE_apply, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    have key : ∀ R : C.LPt, p.V (G e) R ≠ 0 →
        √(TBB.nPt P.k P.r (TBB.TTp p) R) *
            Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w R e ρ =
          omT p w.length R * √(Top.cW P p.l0 w e ρ).re := by
      intro R hR
      have hpos := (isLocPt_and_ptG_pos_of_vec_ne_zero p (G e) R hR).2
      have hwp : 0 ≤ Top.wPt (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') P.r R :=
        div_nonneg (Complex.normSq_nonneg _) hpos.le
      unfold Top.dH omT
      rw [Real.sqrt_mul (pow_nonneg hwp _)]
      unfold TBB.TTp
      ring
    by_cases hz : p.V (G e) Q = 0 ∨ p.V (G e) Q' = 0
    · rcases hz with h | h
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).1, (hsInner_zero_left_right_and_hsVec_zero (0 : Wq →L[ℂ] Wp)).2.2,
          inner_zero_right]
        simp
      · rw [h, ContinuousLinearMap.comp_zero, (hsInner_zero_left_right_and_hsVec_zero _).2.1, (hsInner_zero_left_right_and_hsVec_zero (0 : Wq →L[ℂ] Wp)).2.2,
          inner_zero_left]
        simp
    · push Not at hz
      have hreal : √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(TBB.nPt P.k P.r (TBB.TTp p) Q') /
            TBB.normC nn w *
            (Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ *
              Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) =
          √(Top.cW P p.l0 w e ρ).re * √(Top.cW P p.l0 w e ρ).re / TBB.normC nn w *
            (omT p w.length Q' * omT p w.length Q) := by
        rw [div_mul_eq_mul_div,
          show √(TBB.nPt P.k P.r (TBB.TTp p) Q) * √(TBB.nPt P.k P.r (TBB.TTp p) Q') *
              (Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) =
              (√(TBB.nPt P.k P.r (TBB.TTp p) Q) *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q e ρ) *
              (√(TBB.nPt P.k P.r (TBB.TTp p) Q') *
                Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w Q' e ρ) by ring,
          key Q hz.1, key Q' hz.2]
        ring
      unfold B.hsInner
      have hc := congrArg (fun x : ℝ => (x : ℂ) *
        inner ℂ (B.hsVec ((p.TP.E ρ).comp (p.V (G e) Q'))) (B.hsVec ((p.TP.E ρ).comp (p.V (G e) Q)))) hreal
      push_cast at hc ⊢
      linear_combination hc

private theorem continuousAt_omT_append_last_of_ptG_pos {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (N m : ℕ) (h : C.LPt) (c0 : ℂ) (hc0 : c0 ≠ 0)
    (hG : 0 < D.ptG (TBB.TTp p) P.r (h ++ [(m, c0)])) :
    ContinuousAt (fun c : ℂ => omT p N (h ++ [(m, c)])) c0 := by
  have hgg : (fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) =
      fun c => (Complex.normSq c - TBB.TTp p, c) := by
    funext c
    simp [D.ptGG, D.ptLast]
  have hn : ContinuousAt (fun c : ℂ => TBB.nPt P.k P.r (TBB.TTp p) (h ++ [(m, c)])) c0 := by
    have h1 := (LastBlockContinuity.continuousOn_weight_product P.k P.r (fun _ _ => 1) (fun _ _ => one_pos) m h 1).continuousAt
      (x := (D.ptGG (TBB.TTp p) (h ++ [(m, c0)]), c0))
      ((isOpen_univ.prod isOpen_compl_singleton).mem_nhds ⟨trivial, hc0⟩)
    have h2 : ContinuousAt (fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) c0 := by
      rw [hgg]
      exact ((Complex.continuous_normSq.sub continuous_const).prodMk continuous_id).continuousAt
    exact h1.comp (f := fun c : ℂ => (D.ptGG (TBB.TTp p) (h ++ [(m, c)]), c)) h2
  have hw : ContinuousAt (fun c : ℂ => Top.wPt (TBB.TTp p) P.r (h ++ [(m, c)])) c0 := by
    unfold Top.wPt
    exact (Complex.continuous_normSq.comp (LastBlockContinuity.ptMatN_cont h m (P.r + 1)).matrix_det).continuousAt.div
      (LastBlockContinuity.ptG_cont (TBB.TTp p) P.r h m).continuousAt hG.ne'
  unfold omT
  exact (hn.sqrt).mul ((hw.pow N).sqrt)

theorem top_level_Y_continuity : YCont := by
  intro Wp Wq _ _ _ _ _ _ P p F' hF N m h hh hm hsz c0 hc0
  have hc0' : c0 ≠ 0 := hc0
  have hA := LastBlockContinuity.smulV_continuousAt P p F' hF h hh m hm hsz (fun c => omT p N (h ++ [(m, c)]))
    (ContinuousLinearMap.id ℂ Wp) c0 hc0' (fun hG => continuousAt_omT_append_last_of_ptG_pos p N m h c0 hc0' hG)
  simp only [ContinuousLinearMap.id_comp] at hA
  exact hA.continuousWithinAt

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopC
section
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem np_top_two (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (a a' : C.LPt)
    (ha : D.IsLocPt a P.r) (ha' : D.IsLocPt a' P.r) (w : List C.Letter) (c : ℂ) :
    ((√(C.nAux P.k P.r 0 (fun _ _ => 1) 1 a) * √(C.nAux P.k P.r 0 (fun _ _ => 1) 1 a') / TBB.normC nn w : ℝ) : ℂ) *
        ((KB.levW P (P.r + 1) c : ℂ) * p.RR F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])) =
      TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) := by
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a with hAdef
  set A' := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a' with hA'def
  have hA : 0 ≤ A := TBBx5.weighted_auxiliary_norm_nonneg P P.r le_rfl a ha
  have hA' : 0 ≤ A' := TBBx5.weighted_auxiliary_norm_nonneg P P.r le_rfl a' ha'
  have hn : ∀ (b : C.LPt), D.IsLocPt b P.r → TBB.nPt P.k P.r (TBB.TTp p) (b ++ [(1, c)]) =
      C.nAux P.k P.r 0 (fun _ _ => 1) 1 b *
        C.nAux P.k P.r (D.ptGG (TBB.TTp p) (b ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] := by
    intro b hb
    unfold TBB.nPt
    rw [Formalism.FourierDecayAlt.P.PBD.weight_product_append, hb.2,
      Formalism.FourierDecayAlt.P.PBD.weight_product_indep_of_real_parameter P.k P.r _ 0 (fun _ _ => 1) b 1 le_rfl (by rw [hb.2]; omega)]
  unfold TBB.NP
  rw [hn a ha, hn a' ha']
  by_cases hc2 : Complex.normSq c ≤ Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z'
  · have h0 : p.RR F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)]) = 0 :=
      Formalism.FourierDecayAlt.P.PBD.rrTop_zero P p.l0 p.T p.ν' p.m₀ p.Θ p.TP (M.sgn P p.l0) F w a (a' ++ [(1, c)]) c ha.2 hc2
    rw [h0]
    simp
  · push Not at hc2
    have hT : Tz P.k P.r p.T.base.z = P.T := p.hP.2.2.2.1
    have hT' : Tz P.k P.r p.T.base.z' = P.T' := p.hP.2.2.2.2.1
    have hlast : ∀ b : C.LPt, D.ptGG (TBB.TTp p) (b ++ [(1, c)]) = Complex.normSq c - TBB.TTp p := by
      intro b
      simp [D.ptGG, D.ptLast]
    have hTT : TBB.TTp p = P.T * P.T' := by
      unfold TBB.TTp
      rw [hT, hT']
    have hfac : ∀ b : C.LPt, C.nAux P.k P.r (D.ptGG (TBB.TTp p) (b ++ [(1, c)])) (fun _ _ => 1) (1 + P.r) [(1, c)] =
        KB.levW P (P.r + 1) c := by
      intro b
      rw [hlast, hTT]
      rw [hT, hT'] at hc2
      simp only [C.nAux, KB.levW, B2.zWeight, if_pos hc2.le]
      rw [if_pos ⟨by omega, trivial⟩]
      simp
    have hlev : 0 ≤ KB.levW P (P.r + 1) c := by
      rw [← hfac a, hlast]
      simp only [C.nAux]
      rw [if_pos ⟨by omega, trivial⟩]
      have : 0 ≤ Complex.normSq c - TBB.TTp p := by
        unfold TBB.TTp; linarith
      simpa using pow_nonneg this _
    rw [hfac a, hfac a', Real.sqrt_mul hA, Real.sqrt_mul hA']
    have hs : √(KB.levW P (P.r + 1) c) * √(KB.levW P (P.r + 1) c) = KB.levW P (P.r + 1) c :=
      Real.mul_self_sqrt hlev
    have : √A * √(KB.levW P (P.r + 1) c) * (√A' * √(KB.levW P (P.r + 1) c)) / TBB.normC nn w =
        √A * √A' / TBB.normC nn w * KB.levW P (P.r + 1) c := by
      have e : √A * √(KB.levW P (P.r + 1) c) * (√A' * √(KB.levW P (P.r + 1) c)) / TBB.normC nn w =
          √A * √A' / TBB.normC nn w * (√(KB.levW P (P.r + 1) c) * √(KB.levW P (P.r + 1) c)) := by ring
      rw [e, hs]
    rw [this]
    push_cast
    ring

end place

theorem top_level_fibre : FibreTop := by
  intro hA Wp Wq _ _ _ _ _ _ P p nn F w Cb hCb hF hw a a' ha ha'
  have hPS : KB.PStd := Formalism.FourierDecayAlt.P.standard_pairing_of_heads Formalism.FourierDecayAlt.P.radial_head Formalism.FourierDecayAlt.P.head_top
  set A := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a with hAdef
  set A' := C.nAux P.k P.r 0 (fun _ _ => 1) 1 a' with hA'def
  set κ : ℝ := √A * √A' / TBB.normC nn w with hκ
  constructor
  · obtain ⟨φ, -, hφi, hφ, -⟩ := hPS hA Wp Wq P p F P.r le_rfl w a a ha ha Cb hCb hF hw
    refine (hφi.const_mul ((√A * √A / TBB.normC nn w : ℝ) : ℂ)).congr ?_
    filter_upwards [PBL.ae_ne_zero_complex] with c hc
    rw [← np_top_two p nn F a a ha ha w c, hφ c hc]
  · obtain ⟨φ, -, -, hφ, hφs⟩ := hPS hA Wp Wq P p F P.r le_rfl w a a' ha ha' Cb hCb hF hw
    have h0 := hφs 0
    simp only [PBASM.waveG_zero_eq_self] at h0
    have hf0 : ∀ c : ℂ, P5.fsv 0 c = 1 := fun c => by simp [P5.fsv]
    simp only [hf0, one_mul] at h0
    rw [TBBx5.li_np p nn F P.r le_rfl w a a' ha ha', TBBx5.wv_nPt p P.r le_rfl a ha,
      TBBx5.wv_nPt p P.r le_rfl a' ha', ← h0, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [PBL.ae_ne_zero_complex] with c hc
    rw [← np_top_two p nn F a a' ha ha' w c, hφ c hc]

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGermTopVec
section
namespace Formalism.FourierDecayAlt.P.CutBP.GT

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate InnerProductSpace

noncomputable section

open Classical

abbrev HS (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Type :=
  PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp)

abbrev HT (I : Type) [Fintype I] (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : Type :=
  PiLp 2 (fun _ : I => HS Wp Wq)

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]

def vecT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q : C.LPt) : HT I Wp Wq :=
  WithLp.toLp 2 (fun i => ((√(c i) * omT p N Q : ℝ) : ℂ) • L i (p.V (Fi i) Q))

theorem vecT_apply (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q : C.LPt) (i : I) :
    vecT p N c Fi L Q i = ((√(c i) * omT p N Q : ℝ) : ℂ) • L i (p.V (Fi i) Q) := rfl

theorem inner_vecT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (hc : ∀ i, 0 ≤ c i)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (Q Q' : C.LPt) :
    ⟪vecT p N c Fi L Q, vecT p N c Fi L Q'⟫_ℂ =
      ∑ i, (c i : ℂ) * ⟪(omT p N Q : ℂ) • L i (p.V (Fi i) Q), (omT p N Q' : ℂ) • L i (p.V (Fi i) Q')⟫_ℂ := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : ((√(c i) : ℝ) : ℂ) * ((√(c i) : ℝ) : ℂ) = (c i : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hc i)]
  rw [vecT_apply, vecT_apply, inner_smul_left, inner_smul_right, inner_smul_left, inner_smul_right]
  simp only [Complex.conj_ofReal, Complex.ofReal_mul, map_mul]
  rw [← hs]
  ring

def utT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (x D : ℂ) : HT I Wp Wq :=
  ((‖x‖ ^ (s - 1) : ℝ) : ℂ) • vecT p N c Fi L (h ++ [(s - 1, x⁻¹), (1, x ^ (s - 1) * D)])

def btT (p : KB.Pl P Wp Wq) (N : ℕ) (c : I → ℝ) (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) (s : ℕ) (h : C.LPt) (u : ℂ) : HT I Wp Wq :=
  if u = 0 then 0 else ((Real.pi ^ (s - 1) * ((s : ℝ) * ‖u‖ ^ (s - 1))⁻¹ : ℝ) : ℂ) • vecT p N c Fi L (h ++ [(s, u)])

end place

structure VecHyp {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq) : Prop where
  hc : ∀ i, 0 ≤ c i
  hFi : ∀ i, KB.CptCoef p.T.base (Fi i)
  gram : ∀ Q Q' : C.LPt, TBB.NP p nn F (P.r + 1) w Q Q' =
    ∑ i, (c i : ℂ) * ⟪(omT p w.length Q' : ℂ) • L i (p.V (Fi i) Q'), (omT p w.length Q : ℂ) • L i (p.V (Fi i) Q)⟫_ℂ
  int : ∀ a : C.LPt, D.IsLocPt a P.r →
    Integrable (fun c : ℂ => TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a ++ [(1, c)]))
  fibre : ∀ a a' : C.LPt, D.IsLocPt a P.r → D.IsLocPt a' P.r →
    TBB.NP p nn F P.r w a a' = ∫ c : ℂ, TBB.NP p nn F (P.r + 1) w (a ++ [(1, c)]) (a' ++ [(1, c)])
  cont : ∀ i (m : ℕ) (h : C.LPt), (∀ q ∈ h, 1 ≤ q.1 ∧ q.2 ≠ 0) → 1 ≤ m → D.ptSize h + m = P.r + 1 →
    ContinuousOn (fun c : ℂ => (omT p w.length (h ++ [(m, c)]) : ℂ) • p.V (Fi i) (h ++ [(m, c)])) {0}ᶜ

def FieldMemU : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ x : ℂ, x ≠ 0 → MemLp (utT p w.length c Fi L s h x) 2 volume

def FieldSup : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ x : ℂ, x ≠ 0 → ∫ D, ‖utT p w.length c Fi L s h x D‖ ^ 2 = TBB.Ew p nn F P.r w (h ++ [(s - 1, x⁻¹)])

def FieldMeas : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    StronglyMeasurable (btT p w.length c Fi L s h)

def FieldLoc : Prop :=
  ∀ {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {I : Type} [Fintype I]
    (p : KB.Pl P Wp Wq) (nn : ℝ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) (c : I → ℝ)
    (Fi : I → B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (L : I → (Wq →L[ℂ] Wp) →L[ℂ] HS Wp Wq),
    VecHyp p nn F w c Fi L → ∀ (b s : ℕ), 1 ≤ b → 2 ≤ s → b + s = P.r + 2 → ∀ h : C.LPt, D.IsLocPt h (b - 1) →
    ∀ K : Set ℂ, IsCompact K → (0 : ℂ) ∉ K → IntegrableOn (fun z => ‖PBK.bz s (btT p w.length c Fi L s h) z‖ ^ 2) K

end

end Formalism.FourierDecayAlt.P.CutBP.GT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutMain
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem amaps_id (p : KB.Pl P Wp Wq) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b : ℝ) :
    Amaps p f (fun _ => ContinuousLinearMap.id ℂ Wq) (fun _ => ContinuousLinearMap.id ℂ Wq)
      (fun _ => ContinuousLinearMap.id ℂ Wq) (fun _ => ContinuousLinearMap.id ℂ Wq) b 0 := by
  refine ⟨fun γ _ _ => by simp, fun γ _ _ => by simp, fun γ _ _ v => ?_, fun γ _ _ => ?_, fun γ _ _ => ?_⟩
  · simp only [mul_zero, pow_zero, one_mul, ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_apply]
    nlinarith [sq_nonneg ‖v‖]
  · rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le
  · rw [pow_zero]
    exact pow_le_one₀ (norm_nonneg _) ContinuousLinearMap.norm_id_le

end place

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in

theorem thmBpAt_main (hA : P5.ThmPActual) (Cb C₃ CΛ C₀ Cκ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ κ₀ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 0 < κ₀ →
      κ₀ ≤ b ^ (Cκ * ((2 * P.r + 2 : ℕ) : ℝ) ^ 2) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimE p nn χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      LemB p (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) κ₀ →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, hC₄⟩ := thmBpAt_of_leaves_dec hA C₃ CΛ C₀ Cκ hC₃ hCΛ hC₀
  obtain ⟨c₃, hc₃⟩ := limTopN_cut_of_inCC
  obtain ⟨Cc, hCc⟩ := limZeroN_of_formLimit Cb
  refine ⟨C₄, c₃, Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ κ₀ A₀ p₀ χ nn Y K N hb hΛ hΛb hκ hκb hT hp₀ hK hKN hχ hnn hCb hf hfA hth1 hth2
    hexp hWG hLG hI5 hE hB
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hFd := inCC_fpm_id p p₀ hfA
  have hFck := ckOn_fpm p p₀ hf hid
  have hTN : ∀ ε : ℝ, 0 < ε → LimTopN p nn
      (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) :=
    hc₃ Wp Wq P p nn χ _ _ hth1 hχ hFd hFck
  have hZN : ∀ ε : ℝ, 0 < ε → LimZeroN p nn
      (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) Y N :=
    fun ε hε => hCc Wp Wq P p _ χ ε _ N nn Y hCb hχ hε hFck hFd hth2
  exact hC₄ Wp Wq P p f _ _ _ _ b Λ κ₀ 0 p₀ χ nn Y K N Cb hb hΛ hΛb hκ hκb hT (Nat.zero_le _) hp₀ hK hKN hχ hnn
    hCb hf hid hid (amaps_id p f b) hexp hWG hLG hI5 hI5 hTN hTN hZN hZN hE hE hB hB

theorem thmBpAt_main1 (hA : P5.ThmPActual) (Cb C₃ CΛ C₀ : ℝ) (hC₃ : 0 ≤ C₃) (hCΛ : 0 ≤ CΛ) (hC₀ : 1 / 2 ≤ C₀) :
    ∃ C₄ c₃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
      [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
      (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (b Λ A₀ : ℝ) (p₀ : ℕ) (χ nn : ℝ → ℝ) (Y : Finset ℝ) (K N : ℕ),
      3 ≤ b → 1 ≤ Λ → Λ ≤ b ^ (CΛ * ((2 * P.r + 2 : ℕ) : ℝ)) → 1 ≤ TBB.Tq p →
      (p₀ : ℝ) ≤ C₀ * (3 * ((P.r : ℝ) + 1)) + 1 →
      3 ≤ K → (P.r + 1) * K ≤ N → C6.IsCut0 χ → (∀ y, 0 < nn y) →
      KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → B.CkOn ⊤ (B.GV P.k P.r) f → (∀ m : ℕ, B.InCC A₀ m f) →
      c₃ * ((P.r : ℝ) + 1) ^ 2 * ((P.r : ℝ) * ((2 * P.r + P.k + 1 : ℕ) : ℝ) + 1) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤
        A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) →
      BigCellDerivativeExpansion p f b C₃ (2 * p₀ + 0) →
      TBBx5.WaveGrid p nn Y Λ K N → TBBx5.LiftGrid p nn Y Λ K N →
      (∀ ε : ℝ, 0 < ε → ∀ n : ℕ, TBB.BlockGrowthBound p nn
        (apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n) Y K N) →
      LimE p nn χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) Y N →
      TBB.ThmBpAt p f b C₄ 0 p₀ := by
  obtain ⟨C₄, c₃, Cc, h⟩ := thmBpAt_main hA Cb C₃ CΛ C₀ 0 hC₃ hCΛ hC₀
  refine ⟨C₄, c₃, Cc, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f b Λ A₀ p₀ χ nn Y K N h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 hE
  exact h Wp Wq P p f b Λ 1 A₀ p₀ χ nn Y K N h1 h2 h3 one_pos (by simp) h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 hE (lemB_one p _)

end

end Formalism.FourierDecayAlt.P.CutBP
end

