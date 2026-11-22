import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0306
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0179
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0297
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0208
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFId
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0305

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutBPEqDecay
section
namespace Formalism.FourierDecayAlt.P.CutBPEq

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TBB Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.CutBP2
open scoped ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section clm

variable {k r : ℕ} {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup E']
  [NormedSpace ℂ E']

theorem op_clm (Φ : E →L[ℂ] E') (b : Bool) {X : Mat k r} (hX : inLie k r X) {G : Mat k r → E}
    (hG : CkOn ((1 : ℕ) : ℕ∞) (GV k r) G) {g : Mat k r} (hg : g ∈ GV k r) :
    Formalism.FourierDecayAlt.P.B4.op b X (fun h => Φ (G h)) g = Φ (Formalism.FourierDecayAlt.P.B4.op b X G g) := by
  unfold Formalism.FourierDecayAlt.P.B4.op
  have hd : DifferentiableAt ℝ (fun t : ℝ => G (Formalism.FourierDecayAlt.P.B4.cv b X t g)) 0 :=
    Formalism.FourierDecayAlt.P.B4.ckOn_diff 0 b hG hX hg
  exact ((Φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd.hasDerivAt).deriv

theorem ckOn_clm {m : ℕ∞} (Φ : E →L[ℂ] E') {G : Mat k r → E} (hG : CkOn m (GV k r) G) :
    CkOn m (GV k r) (fun h => Φ (G h)) := by
  intro g₀ hg₀
  obtain ⟨U, f', hU, hg, hf', heq⟩ := hG g₀ hg₀
  refine ⟨U, fun h => Φ (f' h), hU, hg, ?_, fun g hgU hgV => by show Φ (G g) = Φ (f' g); rw [heq g hgU hgV]⟩
  exact (Φ.restrictScalars ℝ).contDiff.comp_contDiffOn hf'

theorem W_clm (Φ : E →L[ℂ] E') (w : List (Bool × Mat k r)) (hw : Formalism.FourierDecayAlt.P.B4.AllLie w) {G : Mat k r → E}
    (hG : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G) :
    ∀ g ∈ GV k r, Formalism.FourierDecayAlt.P.B4.W w (fun h => Φ (G h)) g = Φ (Formalism.FourierDecayAlt.P.B4.W w G g) := by
  induction w generalizing G with
  | nil =>
    intro g _
    rfl
  | cons x w ih =>
    intro g hg
    have hx : inLie k r x.2 := hw x List.mem_cons_self
    have hw' : Formalism.FourierDecayAlt.P.B4.AllLie w := fun y hy => hw y (List.mem_cons_of_mem _ hy)
    have hGw : CkOn ((w.length : ℕ) : ℕ∞) (GV k r) G := Formalism.FourierDecayAlt.P.B4.ckOn_mono (by simp) hG
    have hG1 : CkOn ((1 : ℕ) : ℕ∞) (GV k r) (Formalism.FourierDecayAlt.P.B4.W w G) :=
      Formalism.FourierDecayAlt.P.B4.smooth_on_of_word_derivatives w hw' 1 (by simpa [Nat.add_comm] using hG)
    rw [Formalism.FourierDecayAlt.P.B4.W_cons, Formalism.FourierDecayAlt.P.B4.W_cons,
      Formalism.FourierDecayAlt.P.B4.op_congr x.1 hx (fun h hh => ih hw' hGw h hh) g hg]
    exact op_clm Φ x.1 hx hG1 hg

theorem ccle_clm {A c : ℝ} {m : ℕ} (Φ : E →L[ℂ] E') {G : Mat k r → E} (hG : CCle A m G c) :
    CCle A m (fun h => Φ (G h)) (‖Φ‖ * c) := by
  obtain ⟨hk, hb⟩ := hG
  refine ⟨ckOn_clm Φ hk, fun u v hu hv hl g hg => ?_⟩
  have hw : Formalism.FourierDecayAlt.P.B4.AllLie (Formalism.FourierDecayAlt.P.B4.lr u v) :=
    Formalism.FourierDecayAlt.P.SliceLastLevel.allLie_lr' (fun X hX => (hu X hX).1) (fun X hX => (hv X hX).1)
  have hlen : (Formalism.FourierDecayAlt.P.B4.lr u v).length = u.length + v.length := by simp [Formalism.FourierDecayAlt.P.B4.lr]
  have hGk : CkOn (((Formalism.FourierDecayAlt.P.B4.lr u v).length : ℕ) : ℕ∞) (GV k r) G :=
    Formalism.FourierDecayAlt.P.B4.ckOn_mono (by omega) hk
  rw [Formalism.FourierDecayAlt.P.B4.dLR_eq, W_clm Φ _ hw hGk g hg, ← Formalism.FourierDecayAlt.P.B4.dLR_eq]
  have h1 := hb u v hu hv hl g hg
  have hgN : 0 ≤ gN g ^ A := Real.rpow_nonneg (Formalism.FourierDecayAlt.P.BetaSesquilinearity.gN_pos hg).le _
  calc gN g ^ A * ‖Φ (dLR u v G g)‖ ≤ gN g ^ A * (‖Φ‖ * ‖dLR u v G g‖) :=
        mul_le_mul_of_nonneg_left (Φ.le_opNorm _) hgN
    _ = ‖Φ‖ * (gN g ^ A * ‖dLR u v G g‖) := by ring
    _ ≤ ‖Φ‖ * c := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

end clm

section sum

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem rw_zero_fnE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] :
    ∀ v : List (B.Mat k r), B.Rw v (0 : B.Mat k r → E) = 0
  | [] => rfl
  | X :: v => by
    show Formalism.REAL.RdV X (B.Rw v 0) = 0
    rw [rw_zero_fnE v]
    funext g
    simp [Formalism.REAL.RdV]

theorem dLR_zero_fnE {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (v : List (B.Mat k r)) :
    ∀ u : List (B.Mat k r), B.dLR u v (0 : B.Mat k r → E) = 0
  | [] => rw_zero_fnE v
  | X :: u => by
    show B.LdV X (B.dLR u v 0) = 0
    rw [dLR_zero_fnE v u]
    funext g
    simp [B.LdV]

theorem inCC_zero_fnE (A : ℝ) (m : ℕ) : B.InCC A m (0 : B.Mat k r → (Wq →L[ℂ] Wp)) := by
  refine ⟨0, fun g₀ _ => ⟨Set.univ, 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun g _ _ => rfl⟩,
    fun u v _ _ _ g _ => ?_⟩
  rw [dLR_zero_fnE v u]
  simp

theorem inCC_finsum {A : ℝ} {m : ℕ} : ∀ {n : ℕ} (F : Fin n → Mat k r → (Wq →L[ℂ] Wp)),
    (∀ i, InCC A m (F i)) → InCC A m (fun g => ∑ i, F i g)
  | 0, F, _ => by
    have e : (fun g => ∑ i : Fin 0, F i g) = (0 : Mat k r → (Wq →L[ℂ] Wp)) := by funext g; simp
    rw [e]; exact inCC_zero_fnE A m
  | n + 1, F, h => by
    have e : (fun g => ∑ i : Fin (n + 1), F i g) = fun g => F 0 g + ∑ i : Fin n, F i.succ g := by
      funext g; exact Fin.sum_univ_succ _
    rw [e]
    obtain ⟨c₁, h₁⟩ := h 0
    obtain ⟨c₂, h₂⟩ := inCC_finsum (fun i : Fin n => F i.succ) (fun i => h i.succ)
    exact ⟨c₁ + c₂, Formalism.FourierDecayAlt.P.BetaSesquilinearity.CCle_add h₁ h₂⟩

end sum

theorem shifted_decay : FpmShDecay := by
  intro P Wp Wq Wq' _ _ _ _ _ _ _ _ _ u u' q f A A₀ d p₀ hf hA m
  obtain ⟨n, c, L, hc, hAe⟩ := hA
  set Gp : B.Mat P.k P.r → ℂ := fun g => ((Gf P.k P.r q.T.base.z q.T.base.z' g ^ p₀ : ℝ) : ℂ) with hGp
  have e : fpmSh q f A p₀ = fun g => ∑ i, (Gp g * c i g) • (f g).comp (L i) := by
    funext g
    ext v
    simp [fpmSh, hAe g, map_sum, map_smul, Finset.smul_sum, smul_smul, hGp]
  rw [e]
  refine inCC_finsum _ fun i => ?_
  set Φ : (Wq →L[ℂ] Wp) →L[ℂ] (Wq' →L[ℂ] Wp) := (ContinuousLinearMap.compL ℂ Wq' Wq Wp).flip (L i)
  have hΦ : ∀ x, Φ x = x.comp (L i) := fun x => rfl
  have hgood : Formalism.FourierDecayAlt.P.JCx2.pdGood Wp Wq' ((2 * P.r + 2) * p₀ + d) (fun g => Gp g * c i g) :=
    Formalism.FourierDecayAlt.P.JCx2.pd_good_mul le_rfl (Formalism.FourierDecayAlt.P.CutBP.pd_good_Gpow q.T.base.z q.T.base.z' p₀)
      (Formalism.FourierDecayAlt.P.CutBP.pd_good_of_poly (hc i))
  obtain ⟨K, -, hK⟩ := hgood.2 (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d) m
  obtain ⟨b, hb⟩ := hf m
  have hb' := ccle_clm Φ hb
  have hA' : A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) - d + (((2 * P.r + 2) * p₀ + d : ℕ) : ℝ) = A₀ := by
    push_cast; ring
  rw [← hA'] at hb'
  exact ⟨K * (‖Φ‖ * b), hK _ _ hb'⟩

end

end Formalism.FourierDecayAlt.P.CutBPEq
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFApxDom
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def DominatedL2TruncationBound : Prop :=
  ∀ Cb C₁ : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A₀ : ℝ) (p₀ : ℕ) (χ : ℝ → ℝ) (N : ℕ),
    NFHyp Cb Cc p f A₀ p₀ χ N → ∀ Th : B.DiffOp P.k P.r Wp Wq, NFOpOK C₁ p N Th →
      ∃ h : (Fin (P.r + 1) → ℂ) → ℝ, Integrable h ∧ ∀ n : ℕ, ∀ᵐ c : Fin (P.r + 1) → ℂ,
        ‖TBB.Gp p (TBB.bigPt P.r c)‖ ^ (2 * p₀ - N) *
          TBB.Ew p (fun _ => 1) (B.opApply Th (fun g => cutN P.k P.r n g • f g)) (P.r + 1) [] (TBB.bigPt P.r c) ≤ h c

section cutn

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem apx_cutF_fpm {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]
    (p : KB.Pl P Wp Wq) (χ : ℝ → ℝ) (f : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (p₀ : ℕ) (ε : ℝ) (n : ℕ) :
    apx (D.cutF p.T.base χ (TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε) n =
      D.cutF p.T.base χ (TBBx4.fpm p (fun g => cutN P.k P.r n g • f g) (fun _ => ContinuousLinearMap.id ℂ Wq) p₀) ε := by
  funext g
  simp only [apx, D.cutF, TBBx4.fpm, ContinuousLinearMap.smul_comp, smul_smul]
  congr 1
  ring

theorem cutN_ckOn {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : B.Mat k r → E}
    (hf : B.CkOn (⊤ : ℕ∞) (B.GV k r) f) (n : ℕ) :
    B.CkOn (⊤ : ℕ∞) (B.GV k r) (fun g => cutN k r n g • f g) := by
  have hN : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => Complex.normSq z) := by
    simp_rw [Complex.normSq_apply]
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (cutN k r n) := by
    unfold cutN
    refine Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp ?_)
    refine ContDiff.div_const (contDiff_const.sub ?_) _
    refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    exact hN.comp ((contDiff_apply_apply ℝ ℂ i j).comp (contDiff_const_smul _))
  intro g₀ hg₀
  obtain ⟨U, f', hU, hgU, hf', hff⟩ := hf g₀ hg₀
  refine ⟨U, fun g => cutN k r n g • f' g, hU, hgU, hc.contDiffOn.smul hf', fun g hg hgv => ?_⟩
  show cutN k r n g • f g = cutN k r n g • f' g
  rw [hff g hg hgv]

theorem cutN_ccle_unif {k r : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (f : B.Mat k r → E) (A : ℝ)
    (m : ℕ) (bf : ℝ) (hbf : B.CCle A m f bf) :
    ∃ b : ℝ, ∀ n : ℕ, B.CCle (A - 1) m (fun g => cutN k r n g • f g) b := by
  obtain ⟨Kp, hKp0, hKp⟩ := JCx2.pd_cut_ccle (k := k) (r := r) (E := E) m
  have hbf0 : 0 ≤ bf := JCx2.pd_ccle_nonneg hbf
  have hbf' : B.CCle (A - 1) m f bf := BetaSesquilinearity.CCle_mono_A (by linarith) hbf
  refine ⟨bf + Kp * bf, fun n => ?_⟩
  have hψ : B.CCle (A - 1) m (fun g => JCx2.pdPsi ((n : ℝ) + 1) g • f g) (Kp * bf / ((n : ℝ) + 1)) :=
    hKp _ (by positivity) A f bf hbf
  have e : (fun g => cutN k r n g • f g) = fun g => f g + (-1 : ℂ) • (JCx2.pdPsi ((n : ℝ) + 1) g • f g) := by
    funext g
    rw [PBE.cut_eq (fun n g => cutN k r n g) (fun n g => rfl) n g]
    rw [sub_smul, one_smul, neg_one_smul, sub_eq_add_neg]
  rw [e]
  refine JCx2.pd_ccle_mono_c (BetaSesquilinearity.CCle_add hbf' (BetaSesquilinearity.CCle_smul (-1) hψ)) ?_
  have h1 : Kp * bf / ((n : ℝ) + 1) ≤ Kp * bf := div_le_self (by positivity) (by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith)
  simp only [norm_neg, norm_one, one_mul]
  linarith

end cutn

theorem nfApxDomAll_of_cut (hZ : NFDomZero) (hP : NFDomPtw) (hU : DominatedL2TruncationBound) : NFApxDomAll := by
  intro Cb
  obtain ⟨C1, C₁, H1⟩ := hP Cb
  obtain ⟨C2, H2⟩ := hU Cb C₁
  refine ⟨max C1 C2 + 1, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  obtain ⟨hχ, hCb, hf, hfA, hth, hN2⟩ := hH
  set X : ℝ := ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3)
    with hX
  have hX1 : 1 ≤ X := by
    have h1 : (1 : ℝ) ≤ 2 * (P.r : ℝ) + P.k + 1 := by
      have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      linarith
    have h3 : 1 ≤ (2 * (P.r : ℝ) + P.k + 1) ^ 3 := one_le_pow₀ h1
    have h2 : 0 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 := by positivity
    have h4 : 1 ≤ ((P.r : ℝ) + 1) ^ 4 := one_le_pow₀ (by have : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _; linarith)
    have h5 : 1 ≤ (N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3 := by linarith
    rw [hX]
    nlinarith
  have e : ∀ x : ℝ, x * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 +
      (2 * (P.r : ℝ) + P.k + 1) ^ 3) = x * X := fun x => by rw [hX]; ring
  rw [e] at hth
  have hunif : ∀ m : ℕ, ∃ b : ℝ, ∀ n, B.CCle (A₀ - 1) m (fun g => cutN P.k P.r n g • f g) b := fun m => by
    obtain ⟨bf, hbf⟩ := hfA m
    exact cutN_ccle_unif f A₀ m bf hbf
  have h2 : (max C1 C2 + 1) * X = max C1 C2 * X + X := by ring
  have hyp : ∀ c, c ≤ max C1 C2 → ∀ n : ℕ,
      NFHyp Cb c p (fun g => cutN P.k P.r n g • f g) (A₀ - 1) p₀ χ N := fun c hc n => by
    refine ⟨hχ, hCb, cutN_ckOn hf n, fun m => ?_, ?_, hN2⟩
    · obtain ⟨b, hb⟩ := hunif m
      exact ⟨b, hb n⟩
    · rw [e]
      have h1 : c * X ≤ max C1 C2 * X := mul_le_mul_of_nonneg_right hc (by linarith)
      linarith
  have hyp0 : NFHyp Cb C2 p f A₀ p₀ χ N := by
    refine ⟨hχ, hCb, hf, hfA, ?_, hN2⟩
    rw [e]
    have h1 : C2 * X ≤ max C1 C2 * X := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)
    linarith
  obtain ⟨m, Th, Mb, hMb, hok, hb⟩ := H1 Wp Wq P p p₀ χ Y N w hw hN
  choose hh hhi hhb using fun t => H2 Wp Wq P p f A₀ p₀ χ N hyp0 (Th t) (hok t)
  refine ⟨fun c => Mb * ∑ t, |hh t c|, (integrable_finsetSum Finset.univ fun t _ => (hhi t).abs).const_mul Mb,
    fun n => ?_⟩
  filter_upwards [ae_all_iff.2 fun t => hhb t n] with c hc
  rw [apx_cutF_fpm]
  by_cases hc' : D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) ∧ 0 < TBB.Gp p (TBB.bigPt P.r c)
  · exact le_trans (hb (fun g => cutN P.k P.r n g • f g) (A₀ - 1) (hyp C1 (le_max_left _ _) n) ε hε c hc'.1 hc'.2)
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => (hc t).trans (le_abs_self _)) hMb)
  · rw [hZ Wp Wq P p _ w c hc', norm_zero]
    exact mul_nonneg hMb (Finset.sum_nonneg fun t _ => abs_nonneg _)

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdBetaLim
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hsVec_ofReal_smul {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (c : ℝ) (X : Wq →L[ℂ] Wp) :
    B.hsVec ((c : ℂ) • X) = (c : ℂ) • B.hsVec X := by
  unfold B.hsVec
  rfl

theorem nfBetaLim_thr (R K Nn A : ℝ) (hR : 0 ≤ R) (hK : 0 ≤ K) (hN : 0 ≤ Nn)
    (h : 10 * (R + 1) ^ 4 * (Nn * (2 * R + K + 1) ^ 2 + (2 * R + K + 1) ^ 3) ≤ A) :
    2 * (K + R) * (R + 1) + 1 ≤ A ∧ (2 * R + K + 1) ^ 2 < A / (9 * (R + 1)) := by
  set n := 2 * R + K + 1 with hn
  have hn1 : 1 ≤ n := by rw [hn]; linarith
  have h4 : R + 1 ≤ (R + 1) ^ 4 := le_self_pow₀ (by linarith) (by norm_num)
  have hn3 : n ^ 2 ≤ n ^ 3 := pow_le_pow_right₀ hn1 (by norm_num)
  have a1 : (R + 1) * n ^ 2 ≤ (R + 1) ^ 4 * n ^ 3 := mul_le_mul h4 hn3 (by positivity) (by positivity)
  have a2 : (R + 1) ^ 4 * n ^ 3 ≤ (R + 1) ^ 4 * (Nn * n ^ 2 + n ^ 3) :=
    mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg n]) (by positivity)
  have key : 10 * ((R + 1) * n ^ 2) ≤ A := by
    have e : 10 * (R + 1) ^ 4 * (Nn * n ^ 2 + n ^ 3) = 10 * ((R + 1) ^ 4 * (Nn * n ^ 2 + n ^ 3)) := by ring
    rw [e] at h
    linarith
  have hpos : 0 < (R + 1) * n ^ 2 := by positivity
  refine ⟨?_, ?_⟩
  · have hnn : n ≤ n ^ 2 := by nlinarith
    have b1 : 2 * (K + R) * (R + 1) + 1 ≤ 2 * n * (R + 1) := by rw [hn]; nlinarith
    have b2 : 2 * n * (R + 1) ≤ 2 * ((R + 1) * n ^ 2) := by nlinarith
    linarith
  · rw [lt_div_iff₀ (by positivity)]
    nlinarith

section place

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem truncated_pairing_eq_integral (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (χ : ℝ → ℝ) (ε : ℝ)
    (w : List C.Letter) :
    pair0 p F (D.cutF p.T.base χ F ε) w =
      ∫ q, ((χ (Gf P.k P.r p.T.base.z p.T.base.z' (bigCell P.k P.r q.1 (p.T.base.μsec q.2)) / ε) : ℝ) : ℂ) *
        levelZeroRadialIntegral p w F q := by
  unfold pair0 B.beta betaBig
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  show (bcWeight P.k P.r (Tz P.k P.r p.T.base.z) (Tz P.k P.r p.T.base.z') q : ℂ) *
      inner ℂ (B.hsVec (B.JF p.T.base (D.cutF p.T.base χ F ε) (bigCell P.k P.r q.1 (p.T.base.μsec q.2))))
        (B.hsVec (B.JF p.T.base (w.foldr (fun a H => M.sgn P p.l0 • Q.CV P.k P.r (a.2 : ℂ) H) F)
          (bigCell P.k P.r q.1 (p.T.base.μsec q.2)))) = _
  rw [Formalism.FourierDecayAlt.P.JCTx2.JF_cutF, hsVec_ofReal_smul, inner_smul_left, Complex.conj_ofReal]
  unfold levelZeroRadialIntegral
  ring

theorem self_pairing_eq_integral (p : KB.Pl P Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (w : List C.Letter) :
    pair0 p F F w = ∫ q, levelZeroRadialIntegral p w F q := by
  unfold pair0 B.beta betaBig
  rfl

end place

theorem beta_limit_all_levels_holds : NFBetaLimAll := by
  intro Cb
  refine ⟨10, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN
  obtain ⟨hχ, -, -, hfA, hth, -⟩ := hH
  obtain ⟨δ, hδ, hχ0⟩ := hχ.2.1
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  set A := A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ) with hAdef
  have hCC : ∀ m : ℕ, B.InCC A m F' := inCC_fpm_id p p₀ hfA
  obtain ⟨hAB', hT'⟩ := nfBetaLim_thr (P.r : ℝ) (P.k : ℝ) (N : ℝ) A (by positivity) (by positivity) (by positivity) hth
  have hAB : B.AB P.k P.r ≤ A := by unfold B.AB; exact hAB'
  have hT : JF.TransportedAlt P.k P.r A 0 := by
    unfold JF.TransportedAlt
    push_cast
    simpa using hT'
  set Ds := p.T.base with hDs
  have hI : Integrable (levelZeroRadialIntegral p w F') := rr0Int_integrable p w hAB hT fun j _ => hCC j

  obtain ⟨Cχ, hCχ⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hχ.1.continuous.continuousOn
  set Mχ := max Cχ 1 with hMdef
  have hM : ∀ x, ‖χ x‖ ≤ Mχ := by
    intro x
    rcases lt_or_ge x 0 with h | h
    · rw [hχ0 x (by linarith), norm_zero]; exact le_max_of_le_right zero_le_one
    rcases le_or_gt x 1 with h' | h'
    · exact (hCχ x ⟨h, h'⟩).trans (le_max_left _ _)
    · rw [hχ.2.2 x h'.le, norm_one]; exact le_max_right _ _

  set K := Formalism.FourierDecayAlt.P.CutMP.En.foldCV P.k P.r (M.sgn P p.l0) w F' with hK
  have hK0 : B.InCC A 0 K :=
    Formalism.FourierDecayAlt.P.CutMP.En.inCC_fold Formalism.FourierDecayAlt.P.CutMP.En.coefficient_vector_in_L2_class A (M.sgn P p.l0) F' w 0 (hCC _)
  have cH' := jgq_continuousOn Ds hT (hCC 0)
  have cK' := jgq_continuousOn Ds hT hK0
  have hcv := Formalism.FourierDecayAlt.P.CutMP.En.hsVec_contDiff (V := Wp) (W := Wq)
  have ca : ContinuousOn (fun q => B.hsVec (B.JF Ds F' (B.gq Ds q))) (JF.QDom P.k P.r Ds.z Ds.z') :=
    hcv.continuous.comp_continuousOn cH'
  have cb : ContinuousOn (fun q => B.hsVec (B.JF Ds K (B.gq Ds q))) (JF.QDom P.k P.r Ds.z Ds.z') :=
    hcv.continuous.comp_continuousOn cK'
  have hgq : ContinuousOn (fun q => B.gq Ds q) (JF.QDom P.k P.r Ds.z Ds.z') :=
    (Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn Ds 0).continuousOn
  have hmeas : ∀ ε : ℝ, AEStronglyMeasurable (fun q =>
      ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) * levelZeroRadialIntegral p w F' q) volume := by
    intro ε
    have cχ : ContinuousOn (fun q => ((χ (Gf P.k P.r Ds.z Ds.z' (B.gq Ds q) / ε) : ℝ) : ℂ))
        (JF.QDom P.k P.r Ds.z Ds.z') :=
      Complex.continuous_ofReal.comp_continuousOn (hχ.1.continuous.comp_continuousOn
        (((Formalism.FourierDecayAlt.P.JCx1.contDiff_Gf Ds.z Ds.z').continuous.comp_continuousOn hgq).div_const ε))
    have := aesm_weight_smul Ds (cχ.mul (ca.inner cb))
    refine this.congr (Eventually.of_forall fun q => ?_)
    show (bcWeight P.k P.r (Tz P.k P.r Ds.z) (Tz P.k P.r Ds.z') q : ℝ) • (((χ (Gf P.k P.r Ds.z Ds.z' (B.gq Ds q) / ε) : ℝ) : ℂ) *
      inner ℂ (B.hsVec (B.JF Ds F' (B.gq Ds q))) (B.hsVec (B.JF Ds K (B.gq Ds q)))) = _
    rw [Complex.real_smul]
    show _ = ((χ (Gf P.k P.r Ds.z Ds.z' (B.gq Ds q) / ε) : ℝ) : ℂ) *
      ((bcWeight P.k P.r (Tz P.k P.r Ds.z) (Tz P.k P.r Ds.z') q : ℂ) *
        inner ℂ (B.hsVec (B.JF Ds F' (B.gq Ds q))) (B.hsVec (B.JF Ds K (B.gq Ds q))))
    ring

  have hlim : ∀ᵐ q : (Fin P.r → ℂ) × ℂ, Tendsto (fun ε : ℝ =>
      ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) * levelZeroRadialIntegral p w F' q) (𝓝[>] 0)
      (𝓝 (levelZeroRadialIntegral p w F' q)) := by
    refine Eventually.of_forall fun q => ?_
    by_cases hq : bcWeight P.k P.r (Tz P.k P.r Ds.z) (Tz P.k P.r Ds.z') q = 0
    · have h0 : levelZeroRadialIntegral p w F' q = 0 := by unfold levelZeroRadialIntegral; rw [hq]; simp
      simp only [h0, mul_zero]
      exact tendsto_const_nhds
    obtain ⟨-, hG⟩ := bigCell_pos p q hq
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT hG] with ε hε
    have h1 : 1 ≤ Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε := by
      rw [le_div_iff₀ hε.1]; linarith [hε.2]
    rw [hχ.2.2 _ h1]
    simp
  have hT2 : Tendsto (fun ε : ℝ => ∫ q, ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) *
      levelZeroRadialIntegral p w F' q) (𝓝[>] 0) (𝓝 (∫ q, levelZeroRadialIntegral p w F' q)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun q => Mχ * ‖levelZeroRadialIntegral p w F' q‖)
      (Eventually.of_forall hmeas) (Eventually.of_forall fun ε => Eventually.of_forall fun q => ?_)
      (hI.norm.const_mul Mχ) hlim
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)
  have e1 : (fun ε : ℝ => (pair0 p F' (D.cutF p.T.base χ F' ε) w).re) =
      fun ε => (∫ q, ((χ (Gf P.k P.r Ds.z Ds.z' (bigCell P.k P.r q.1 (Ds.μsec q.2)) / ε) : ℝ) : ℂ) *
        levelZeroRadialIntegral p w F' q).re := funext fun ε => by rw [truncated_pairing_eq_integral]
  rw [e1, self_pairing_eq_integral]
  exact (Complex.continuous_re.tendsto _).comp hT2

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFOpOKMulG
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants

noncomputable section

def NFOpOKMulG : Prop :=
  ∀ C : ℝ, ∃ C' : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (N : ℕ) (Th : B.DiffOp P.k P.r Wp Wq), NFOpOK C p N Th →
      ∃ Th' : B.DiffOp P.k P.r Wp Wq, NFOpOK C' p N Th' ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (g : B.Mat P.k P.r),
          B.opApply Th' F g = ((Gf P.k P.r p.T.base.z p.T.base.z' g ^ N : ℝ) : ℂ) • B.opApply Th F g

end

end Formalism.FourierDecayAlt.P.CutBP
end

