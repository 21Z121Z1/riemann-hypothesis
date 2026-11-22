import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0308
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0297
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutLimBdPf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0219
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplyContinuousOn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HasFDerivAtFsvOther
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OpApplySub
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopForm
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0224
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ListSumSplittings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0057
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0293

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFCutSup
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Filter Topology

noncomputable section

theorem xD_dil (φ : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    xD (fun y => φ (y / ε)) = fun x => xD φ (x / ε) := by
  funext x
  simp only [xD]
  have h : (fun y => φ (y / ε)) = fun y => φ (ε⁻¹ * y) := by
    funext y
    rw [div_eq_inv_mul]
  rw [h, deriv_comp_mul_left, smul_eq_mul, div_eq_inv_mul]
  ring

theorem xD_iter_dil (φ : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) (q : ℕ) :
    xD^[q] (fun y => φ (y / ε)) = fun x => (xD^[q] φ) (x / ε) := by
  induction q with
  | zero => rfl
  | succ q ih =>
    rw [Function.iterate_succ_apply', ih, xD_dil _ hε]
    funext x
    rw [Function.iterate_succ_apply']

theorem xD_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD φ) := by
  have hd := (contDiff_infty_iff_deriv.mp hφ).2
  exact contDiff_id.mul hd

theorem xD_iter_contDiff {φ : ℝ → ℝ} (hφ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ) (q : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[q] φ) := by
  induction q with
  | zero => simpa using hφ
  | succ q ih =>
    rw [Function.iterate_succ_apply']
    exact xD_contDiff ih

theorem xD_zero_of_const {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (c : ℝ) (hφ : ∀ y ∈ U, φ y = c) :
    ∀ y ∈ U, xD φ y = 0 := by
  intro y hy
  have h : φ =ᶠ[nhds y] fun _ => c := Filter.eventually_of_mem (hU.mem_nhds hy) hφ
  show y * deriv φ y = 0
  rw [h.deriv_eq]
  simp

private theorem xD_iterate_eq_ite_of_const_on_open {φ : ℝ → ℝ} {U : Set ℝ} (hU : IsOpen U) (c : ℝ)
    (hφ : ∀ y ∈ U, φ y = c) : ∀ q : ℕ, ∀ y ∈ U, (xD^[q] φ) y = if q = 0 then c else 0 := by
  intro q
  induction q with
  | zero => intro y hy; simpa using hφ y hy
  | succ q ih =>
    intro y hy
    rw [Function.iterate_succ_apply']
    simp only [Nat.succ_ne_zero, if_false]
    exact xD_zero_of_const hU _ ih y hy

theorem truncated_supremum_bound_holds : NFCutSup := by
  unfold NFCutSup
  intro χ hχ q
  obtain ⟨hs, -, h1⟩ := hχ
  have hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (xD^[q] χ) := xD_iter_contDiff hs q
  obtain ⟨K0, hK0⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuous.continuousOn
  refine ⟨max K0 1, fun ε hε x hx => ?_⟩
  rw [xD_iter_dil χ hε q]
  show |(xD^[q] χ) (x / ε)| ≤ max K0 1
  have hy : 0 < x / ε := div_pos hx hε
  rcases le_or_gt (x / ε) 1 with hy1 | hy1
  · have hb := hK0 (x / ε) ⟨hy.le, hy1⟩
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (le_max_left _ _)
  · rw [xD_iterate_eq_ite_of_const_on_open isOpen_Ioi 1 (fun z hz => h1 z (le_of_lt hz)) q (x / ε) hy1]
    refine le_trans ?_ (le_max_right _ _)
    split_ifs <;> simp

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolPair
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory
open scoped ComplexConjugate

noncomputable section

section lin

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem cv_smul' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (Y α : ℂ) (f : B.Mat k r → E) :
    Q.CV k r Y (α • f) = α • Q.CV k r Y f :=
  Formalism.FourierDecayAlt.P5.qminorOp_smulC (Formalism.FourierDecayAlt.P5.eH_smulC (k := k) (r := r)) _ _ _ α f

theorem cv_add_GV (D : B.RealPlaceData k r Wp Wq) (Y : ℂ) {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : B.CkOn ⊤ (B.GV k r) H₁) (h₂ : B.CkOn ⊤ (B.GV k r) H₂) :
    ∀ g ∈ B.GV k r, Q.CV k r Y (fun x => H₁ x + H₂ x) g = Q.CV k r Y H₁ g + Q.CV k r Y H₂ g := by
  intro g hg
  obtain ⟨-, -, -, -, hApp⟩ := CutMP.ER.capacity_theta_facts k r Wp Wq D 1 Y 1 0
  have hn : ∀ {H : B.Mat k r → (Wq →L[ℂ] Wp)}, B.CkOn ⊤ (B.GV k r) H →
      B.CkOn ((2 * r + k + 1 : ℕ) : ℕ∞) (B.GV k r) H := fun h => Formalism.FourierDecayAlt.P.B5.ckOn_mono le_top h
  have h₂' : B.CkOn ⊤ (B.GV k r) ((-1 : ℂ) • H₂) := JCx2.ckOn_smul' (-1 : ℂ) h₂
  have e : (fun x => H₁ x + H₂ x) = fun x => H₁ x - ((-1 : ℂ) • H₂) x := by
    funext x; simp
  have hs : B.CkOn ⊤ (B.GV k r) (fun x => H₁ x - ((-1 : ℂ) • H₂) x) := by
    rw [← e]; exact JCx2.ckOn_add' h₁ h₂
  have a1 := hApp _ (hn hs) g hg
  have a2 := hApp _ (hn h₁) g hg
  have a3 := hApp _ (hn h₂') g hg
  have hsub := PBE.opApply_sub (CutMP.ER.capTh k r Wp Wq 1 Y) h₁ h₂' g hg
  rw [one_smul] at a1 a2 a3
  rw [e, ← a1, hsub, a2, a3, cv_smul']
  simp [sub_eq_add_neg]

theorem cv_lin_GV (D : B.RealPlaceData k r Wp Wq) (Y a b : ℂ) {H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)}
    (h₁ : B.CkOn ⊤ (B.GV k r) H₁) (h₂ : B.CkOn ⊤ (B.GV k r) H₂) :
    ∀ g ∈ B.GV k r, Q.CV k r Y (fun x => a • H₁ x + b • H₂ x) g = a • Q.CV k r Y H₁ g + b • Q.CV k r Y H₂ g := by
  intro g hg
  have h := cv_add_GV D Y (JCx2.ckOn_smul' a h₁) (JCx2.ckOn_smul' b h₂) g hg
  have e : (fun x => a • H₁ x + b • H₂ x) = fun x => (a • H₁) x + (b • H₂) x := rfl
  rw [e, h, cv_smul', cv_smul']
  rfl

theorem fold_lin (D : B.RealPlaceData k r Wp Wq) (s a b : ℂ) : ∀ (w : List (Bool × ℝ))
    (H₁ H₂ : B.Mat k r → (Wq →L[ℂ] Wp)), B.CkOn ⊤ (B.GV k r) H₁ → B.CkOn ⊤ (B.GV k r) H₂ →
    ∀ g ∈ B.GV k r, w.foldr (CutMP.ER.opL k r s) (fun x => a • H₁ x + b • H₂ x) g =
      a • w.foldr (CutMP.ER.opL k r s) H₁ g + b • w.foldr (CutMP.ER.opL k r s) H₂ g
  | [], _, _, _, _ => fun _ _ => rfl
  | x :: w, H₁, H₂, h₁, h₂ => by
    intro g hg
    have ih := fold_lin D s a b w H₁ H₂ h₁ h₂
    have s1 := CutMP.ER.fold_smooth CutMP.ER.coefficient_vector_smoothness s w H₁ h₁
    have s2 := CutMP.ER.fold_smooth CutMP.ER.coefficient_vector_smoothness s w H₂ h₂
    have h12 : B.CkOn ⊤ (B.GV k r) (fun x => a • H₁ x + b • H₂ x) :=
      JCx2.ckOn_add' (JCx2.ckOn_smul' a h₁) (JCx2.ckOn_smul' b h₂)
    have s12 := CutMP.ER.fold_smooth CutMP.ER.coefficient_vector_smoothness s w _ h12
    have sK : B.CkOn ⊤ (B.GV k r) (fun y => a • w.foldr (CutMP.ER.opL k r s) H₁ y +
        b • w.foldr (CutMP.ER.opL k r s) H₂ y) :=
      JCx2.ckOn_add' (JCx2.ckOn_smul' a s1) (JCx2.ckOn_smul' b s2)
    simp only [List.foldr_cons, CutMP.ER.opL]
    rw [CutMP.ER.coefficient_vector_congr k r Wp Wq s (x.2 : ℂ) _ _ s12 sK ih g hg]
    simp only [Pi.smul_apply]
    rw [cv_lin_GV D _ a b s1 s2 g hg, smul_add, smul_comm s a, smul_comm s b]

theorem beta_form_linear_left (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A) (a b : ℂ)
    {X Y Z : B.Mat k r → (Wq →L[ℂ] Wp)} (hX : B.InCC A 5 X) (hY : B.InCC A 5 Y) (hZ : B.InCC A 5 Z) :
    B.beta D (fun g => a • X g + b • Y g) Z = a * B.beta D X Z + b * B.beta D Y Z := by
  have h := beta_sum_left D hA ![a, b] ![X, Y] (fun i => by fin_cases i <;> assumption) hZ Finset.univ
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h
  exact h

theorem beta_form_conj_linear_right (D : B.RealPlaceData k r Wp Wq) {A : ℝ} (hA : B.AB k r ≤ A) (a b : ℂ)
    {X Y Z : B.Mat k r → (Wq →L[ℂ] Wp)} (hX : B.InCC A 5 X) (hY : B.InCC A 5 Y) (hZ : B.InCC A 5 Z) :
    B.beta D Z (fun g => a • X g + b • Y g) = conj a * B.beta D Z X + conj b * B.beta D Z Y := by
  rw [CutMP.ER.beta_conj D Z, beta_form_linear_left D hA a b hX hY hZ, map_add, map_mul, map_mul,
    ← CutMP.ER.beta_conj D Z X, ← CutMP.ER.beta_conj D Z Y]

end lin

section main

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem pairing_middle_all_levels_holds : NFPairMidAll := by
  intro Cb
  refine ⟨100, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH χ' hχ' w hw hN ε hε
  obtain ⟨hχ, -, hf, hfA, hA5, -⟩ := hH
  have hχc := hχ
  have hχ'c := hχ'
  set Bs := p.T.base with hBs
  set s : ℂ := M.sgn P p.l0 with hsdef
  have hs : conj s = s := by rw [hsdef]; unfold M.sgn; simp
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  set F' := TBBx4.fpm p f (fun _ => ContinuousLinearMap.id ℂ Wq) p₀ with hF'
  have hF's : B.CkOn ⊤ (B.GV P.k P.r) F' := ckOn_fpm p p₀ hf hid
  have hF'A := inCC_fpm_id p p₀ hfA
  set nn : ℕ := w.length * (2 * P.r + P.k + 1) + (2 * P.r + P.k + 1 + 5) with hnn
  have hbound := CutMP.ER.bound_aux P.r P.k w.length N (A₀ - (((2 * P.r + 2) * p₀ : ℕ) : ℝ)) hN hA5
  obtain ⟨-, ⟨δ₁, hδ₁, hz₁⟩, -⟩ := hχ'
  obtain ⟨-, ⟨δ₂, hδ₂, hz₂⟩, -⟩ := hχ
  set c₀ : ℝ := min δ₁ δ₂ * ε with hc₀
  have hc₀p : 0 < c₀ := mul_pos (lt_min hδ₁ hδ₂) hε
  have hgood : ∀ ψ : ℝ → ℝ, C6.IsCut0 ψ → (∀ x, x < min δ₁ δ₂ → ψ x = 0) →
      CutMP.ER.Good Bs (B.AB P.k P.r) nn c₀ (D.cutF Bs ψ F' ε) := by
    intro ψ hψ hz
    refine ⟨Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF Bs hψ hF's ε,
      Formalism.FourierDecayAlt.P.PBE.cutF_inCC Bs hψ hF'A hε _ _ hbound, fun g _ hg => ?_⟩
    by_contra hlt
    push Not at hlt
    apply hg
    have h0 : ψ (Gf P.k P.r Bs.z Bs.z' g / ε) = 0 := hz _ (by rw [div_lt_iff₀ hε]; exact hlt)
    simp only [D.cutF, h0, Complex.ofReal_zero, zero_smul]
  have gu := hgood χ' hχ'c (fun x hx => hz₁ x (lt_of_lt_of_le hx (min_le_left _ _)))
  have gv := hgood χ hχc (fun x hx => hz₂ x (lt_of_lt_of_le hx (min_le_right _ _)))
  have gm := hgood (midCut χ' χ) (isCut0_midCut hχ'c hχc) (fun x hx => by
    simp only [midCut, hz₁ x (lt_of_lt_of_le hx (min_le_left _ _)), hz₂ x (lt_of_lt_of_le hx (min_le_right _ _))]
    norm_num)
  set u := D.cutF Bs χ' F' ε with hu
  set v := D.cutF Bs χ F' ε with hv
  set m := D.cutF Bs (midCut χ' χ) F' ε with hm
  have hm_eq : m = fun g => (1 / 2 : ℂ) • u g + (1 / 2 : ℂ) • v g := by
    funext g
    simp only [hm, hu, hv, D.cutF, midCut]
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
    push_cast
    ring
  have pe : ∀ X Z : B.Mat P.k P.r → (Wq →L[ℂ] Wp),
      pair0 p X Z w = B.beta Bs (w.foldr (CutMP.ER.opL P.k P.r s) X) Z := fun _ _ => rfl
  set fu := w.foldr (CutMP.ER.opL P.k P.r s) u with hfu
  set fv := w.foldr (CutMP.ER.opL P.k P.r s) v with hfv
  have n5 : 5 ≤ nn := le_trans (by omega : 5 ≤ 2 * P.r + P.k + 1 + 5) (Nat.le_add_left _ _)
  have gfold : ∀ H, CutMP.ER.Good Bs (B.AB P.k P.r) nn c₀ H →
      B.InCC (B.AB P.k P.r) 5 (w.foldr (CutMP.ER.opL P.k P.r s) H) := by
    intro H hG
    have h := CutMP.ER.fold_good CutMP.ER.coefficient_vector_smoothness CutMP.ER.coefficient_vector_in_class CutMP.ER.coefficient_vector_support s w
      (2 * P.r + P.k + 1 + 5) H (CutMP.ER.good_mono (le_of_eq (Nat.add_comm _ _)) hG)
    exact CutMP.ER.inCC_mono (by omega) h.2.1
  have iu := CutMP.ER.inCC_mono n5 gu.2.1
  have iv := CutMP.ER.inCC_mono n5 gv.2.1
  have im := CutMP.ER.inCC_mono n5 gm.2.1
  have ifu := gfold u gu
  have ifv := gfold v gv
  have hAB : B.AB P.k P.r ≤ B.AB P.k P.r := le_rfl

  have hfm : ∀ g ∈ B.GV P.k P.r, w.foldr (CutMP.ER.opL P.k P.r s) m g =
      (1 / 2 : ℂ) • fu g + (1 / 2 : ℂ) • fv g := by
    rw [hm_eq]
    exact fold_lin Bs s _ _ w u v gu.1 gv.1
  have Pmm : pair0 p m m w = (1 / 2 : ℂ) * ((1 / 2 : ℂ) * B.beta Bs fu u + (1 / 2 : ℂ) * B.beta Bs fu v) +
      (1 / 2 : ℂ) * ((1 / 2 : ℂ) * B.beta Bs fv u + (1 / 2 : ℂ) * B.beta Bs fv v) := by
    have hc : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
    rw [pe, CutMP.ER.beta_form_congr_holds P.k P.r Wp Wq Bs _ (fun g => (1 / 2 : ℂ) • fu g + (1 / 2 : ℂ) • fv g) m m hfm
      (fun _ _ => rfl), beta_form_linear_left Bs hAB _ _ ifu ifv im, hm_eq, beta_form_conj_linear_right Bs hAB _ _ iu iv ifu,
      beta_form_conj_linear_right Bs hAB _ _ iu iv ifv, hc]

  have capA : CutMP.ER.CapAdj :=
    CutMP.ER.capAdj_of_int (CutMP.ER.capAdjInt_of_scalar CutMP.ER.capacity_adjoint_scalar)
  have hvu : B.beta Bs fv u = (starRingEnd ℂ) (B.beta Bs fu v) := by
    have h1 := CutMP.ER.fold_adj capA CutMP.ER.capacity_theta_facts CutMP.ER.beta_form_congr_holds CutMP.ER.coefficient_vector_smoothness
      CutMP.ER.coefficient_vector_in_class CutMP.ER.coefficient_vector_support Bs hAB hc₀p hs w v u gv gu
    have h2 := CutMP.ER.beta_form_congr_holds P.k P.r Wp Wq Bs v v (w.reverse.foldr (CutMP.ER.opL P.k P.r s) u) fu
      (fun _ _ => rfl) (CutMP.ER.fold_rev CutMP.ER.coefficient_vector_smoothness CutMP.ER.coefficient_vector_congr CutMP.ER.coefficient_vector_commutation s w u gu.1)
    rw [h1, h2, CutMP.ER.beta_conj Bs v fu]
  rw [Pmm, pe u u, pe v v, pe u v, hvu]
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; ring]
  simp only [Complex.add_re, Complex.re_ofReal_mul, Complex.conj_re]
  ring

end main

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFIdPolQuad
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem nfPolQuadAll_of (hMeas : TopDMeasCpt) (hApx : NFApxDomAll) : NFPolQuadAll := by
  intro hA Cb
  obtain ⟨C1, H1⟩ := nFTopFormAll_of hMeas hApx hA Cb
  obtain ⟨C2, H2⟩ := nFTopInt_of hMeas hApx Cb
  refine ⟨max C1 C2, ?_⟩
  intro Wp Wq _ _ _ _ _ _ P p f A₀ p₀ χ Y N hH w hw hN ε hε
  have hH1 := nfHyp_mono hH (le_max_left C1 C2) hH.1
  have hH2 := nfHyp_mono hH (le_max_right C1 C2) hH.1
  refine ⟨H2 Wp Wq P p f A₀ p₀ χ Y N hH2 w hw hN ε hε, ?_⟩
  have hid : B.CkOn ⊤ (B.GV P.k P.r) (fun _ : B.Mat P.k P.r => ContinuousLinearMap.id ℂ Wq) := fun g₀ _ =>
    ⟨Set.univ, fun _ => ContinuousLinearMap.id ℂ Wq, isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩
  have hF := ckOn_fpm p p₀ hH.2.2.1 hid
  have hc := Formalism.FourierDecayAlt.P.JCTx6.Link2.ckOn_cutF p.T.base hH.1 hF ε
  rw [← residual_pairing_eq_self_pairing p hc hw.1]
  exact H1 Wp Wq P p f A₀ p₀ χ Y N hH1 w hw hN ε hε

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFLeib
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants Filter Topology MeasureTheory

noncomputable section

def ThChain (Ψ : ℕ → ℝ → ℝ) : Prop := ∀ (n : ℕ) (x : ℝ), 0 < x → HasDerivAt (Ψ n) (Ψ (n + 1) x / x) x

section leibterm

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def LeibTerm (Bs : B.RealPlaceData k r Wp Wq) (Dop : B.DiffOp k r Wp Wq) (T' : B.DTerm k r Wp Wq) : Prop :=
  ∃ T ∈ Dop, ∃ (P : B.Mat k r → ℂ) (j : ℕ), ListSumSplittings.PolyClass ((2 * r + 2) * T.word.length) P ∧
    T'.word.Sublist T.word ∧
    ∀ g ∈ C6.domL Bs ∅, T'.coef g = (P g * ((Gf k r Bs.z Bs.z' g : ℝ) : ℂ)⁻¹ ^ j) • T.coef g

end leibterm

def NFLeibExp : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (w : List (B.Mat k r)), (∀ X ∈ w, B.inLie k r X) →
    ∃ terms : List (ℕ × (B.Mat k r → ℂ) × ℕ × List (B.Mat k r)),
      (∀ t ∈ terms, t.1 ≤ w.length ∧ ListSumSplittings.PolyClass ((2 * r + 2) * w.length) t.2.1 ∧ t.2.2.2.Sublist w) ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.Rw w (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            (terms.map fun t => ((((Ψ t.1 (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) * t.2.1 x *
              ((Gf k r Bs.z Bs.z' x : ℝ) : ℂ)⁻¹ ^ t.2.2.1) • B.Rw t.2.2.2 F x)).sum

def NFLeibOps : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (Dop : B.DiffOp k r Wp Wq),
    B.SmoothCoef (C6.domL Bs ∅) Dop →
    ∃ (Q : ℕ) (L : Fin (Q + 1) → B.DiffOp k r Wp Wq),
      (∀ q, B.SmoothCoef (C6.domL Bs ∅) (L q)) ∧ (∀ q, ∀ T' ∈ L q, LeibTerm Bs Dop T') ∧
      ∀ Ψ : ℕ → ℝ → ℝ, ThChain Ψ → ∀ F : B.Mat k r → (Wq →L[ℂ] Wp), B.CkOn ⊤ (B.GV k r) F →
        ∀ x ∈ C6.domL Bs ∅,
          B.opApply Dop (fun y => ((Ψ 0 (Gf k r Bs.z Bs.z' y) : ℝ) : ℂ) • F y) x =
            ∑ q : Fin (Q + 1), ((Ψ q (Gf k r Bs.z Bs.z' x) : ℝ) : ℂ) • B.opApply (L q) F x

def NFLeibBd : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq) (nf : ℕ)
    (fib : Fin nf → B.Mat k r → C6.EndH Wp Wq) (o κ : ℕ) (Dop : B.DiffOp k r Wp Wq),
    (∀ j, C6.FibBound Bs (fib j)) → C6.InDDPlus Bs fib ∅ o κ Dop →
    ∀ L : B.DiffOp k r Wp Wq, (∀ T' ∈ L, LeibTerm Bs Dop T') →
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 ≤ K ∧ ∀ (F : B.Mat k r → (Wq →L[ℂ] Wp)) (A b : ℝ), B.CCle A o F b →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g →
        ‖B.opApply L F g‖ ≤ K * b * B.gN g ^ ((κ : ℝ) + 3 * ((r : ℝ) + 1) * o + (2 * (r : ℝ) + 2) * o - A)

def NFVLin : Prop :=
  ∃ c₃ : ℝ, ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq)
    (ν' : Fin (2 * r + k + 1) → ℂ) (m₀ : B.Mat k r) (Q : ℕ) (c : Fin (Q + 1) → ℝ → ℂ)
    (H : B.Mat k r → (Wq →L[ℂ] Wp)) (Hq : Fin (Q + 1) → B.Mat k r → (Wq →L[ℂ] Wp)) (A : ℝ),
    c₃ * ((r : ℝ) + 1) ^ 2 * ((r : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) + 1) ≤ A →
    (∀ q, ContinuousOn (Hq q) (B.GPos Bs)) →
    (∀ q, ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ g ∈ B.GV k r, ε ≤ Gf k r Bs.z Bs.z' g → ‖Hq q g‖ ≤ C * B.gN g ^ (-A)) →
    (∀ g ∈ B.GPos Bs, H g = ∑ q, c q (Gf k r Bs.z Bs.z' g) • Hq q g) →
    ∀ γ : C.LPt, D.IsLocPt γ (r + 1) → 0 < D.ptG (Tz k r Bs.z * Tz k r Bs.z') r γ →
      D.vecV Bs ν' m₀ H γ = ∑ q, c q (D.ptG (Tz k r Bs.z * Tz k r Bs.z') r γ) • D.vecV Bs ν' m₀ (Hq q) γ

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutNFTopDomCore
section
namespace Formalism.FourierDecayAlt.P.CutBP

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory

noncomputable section

section kb

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def trJKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (J : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) :
    M.Ty P → MA.SmQ P.r P.TT :=
  fun ρ => MA.toSm P fun q =>
    ((Real.sqrt (MA.wq P.k q.1 P.TT) : ℝ) : ℂ) * inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (J (B.gq p.T.base q.1)))

def IsFrameKB (p : KB.Pl P Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (e ρ) {ζ : ℂ | P.TT < Complex.normSq ζ}) ∧
  ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
    (∀ ρ, e ρ ζ ∈ NF.Fib P.k P.r p.T.base.z p.T.base.z' p.T.base.μsec p.T.base.π p.T.base.π' ζ) ∧
    (∀ ρ ρ', inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e ρ' ζ)) = if ρ = ρ' then (1 : ℂ) else 0) ∧
    ∀ X ∈ NF.Fib P.k P.r p.T.base.z p.T.base.z' p.T.base.μsec p.T.base.π p.T.base.π' ζ,
      X = ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec X) • e ρ ζ

end kb

def NFModelNF : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ (l0 : ℕ) (Y : Finset ℝ) (w : List C.Letter), TBB.AdmW P l0 Y w → ∀ e : Wd.Ix (Fin w.length),
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (i i' : Fin m → ℕ) (h : Fin m → List (MA.A P (MA.DQ P))),
        (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ j, i j + i' j = w.length) ∧
        (∀ j, (h j).length = w.length ∧ ∀ a ∈ h j, a ∈ MA.hatSet P L) ∧
        (Fr.ofWord L (MA.startM P (MA.DQ P) l0) (D.positionted w)).F e (fun _ => 0) =
          ∑ j, b j * L.Di ^ i j * L.Dbi ^ i' j * (h j).prod

def NFTieHat : Prop :=
  ∀ Cb : ℝ, ∃ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq),
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ →
    ∃ (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r),
      IsFrameKB p e ∧ MA.IsModelLevel P (MA.DQ P) L ∧
      ∀ (Y : Finset ℝ) (w : List C.Letter), TBB.AdmW P p.l0 Y w →
      ∀ (ee : Wd.Ix (Fin w.length)) (Q : ℕ) (Lq : Fin (Q + 1) → B.DiffOp P.k P.r Wp Wq), IsSCoef p w ee Q Lq →
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (u : Fin m → List (MA.A P (MA.DQ P))) (C : ℝ),
        (∀ j, b j ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ j, (u j).length = w.length ∧ ∀ a ∈ u j, a ∈ MA.hatSet P L) ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((w.length : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          ∀ (qq : Fin (Q + 1)) (ρ : M.Ty P) (c : Fin (P.r + 1) → ℂ) (q : MA.Qp P.r P.TT),
            q.1 = ((fun l => c l.castSucc), c (Fin.last P.r)) →
            D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
            Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
                Real.sqrt (TBB.nPt P.k P.r (TBB.TTp p) (TBB.bigPt P.r c)) *
                (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) *
              (Top.dH P p.l0 (TBB.TTp p) w (TBB.bigPt P.r c) ee ρ ^ 2 *
                ‖B.hsVec ((p.TP.E ρ).comp (p.V (B.opApply (Lq qq) F) (TBB.bigPt P.r c)))‖ ^ 2) ≤
              C * TBB.Gp p (TBB.bigPt P.r c) ^ (-(w.length : ℤ)) *
                ∑ j, ∑ ρ' : M.Ty P, ‖MA.evQ P (MA.actA P (b j * (u j).prod) (trJKB p e (B.JF p.T.base F)) ρ') q‖ ^ 2

def NFHatProdKB : Prop :=
  ∃ C₁ Cc : ℝ, ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (L : R.LevelData (MA.A P (MA.DQ P)) P.r),
    IsFrameKB p e → MA.IsModelLevel P (MA.DQ P) L → ∀ (N : ℕ) (u : List (MA.A P (MA.DQ P))), u.length ≤ N →
      (∀ a ∈ u, a ∈ MA.hatSet P L) →
      ∃ (m : ℕ) (b : Fin m → MA.A P (MA.DQ P)) (Th : Fin m → B.DiffOp P.k P.r Wp Wq),
        (∀ k, b k ∈ Submonoid.closure (MA.bddSet P L)) ∧ (∀ k, NFOpOK C₁ p N (Th k)) ∧
        ∀ (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (A : ℝ), B.CkOn ⊤ (B.GV P.k P.r) F → (∀ m : ℕ, B.InCC A m F) →
          Cc * ((P.r : ℝ) + 1) ^ 4 * ((N : ℝ) * (2 * (P.r : ℝ) + P.k + 1) ^ 2 + (2 * (P.r : ℝ) + P.k + 1) ^ 3) ≤ A →
          MA.actA P u.prod (trJKB p e (B.JF p.T.base F)) =
            ∑ k, MA.actA P (b k) (trJKB p e (B.JF p.T.base (B.opApply (Th k) F)))

def NFBddPtw : Prop :=
  ∀ (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r), 0 < P.TT → MA.IsModelLevel P (MA.DQ P) L →
    ∀ b ∈ Submonoid.closure (MA.bddSet P L), ∃ C : ℝ, ∀ (u : M.Ty P → MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT),
      ∑ ρ, ‖MA.evQ P (MA.actA P b u ρ) q‖ ^ 2 ≤ C * ∑ ρ, ‖MA.evQ P (u ρ) q‖ ^ 2

def NFTrNormKB : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq)
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)), IsFrameKB p e → ∃ C : ℝ, ∀ (H : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (c : Fin (P.r + 1) → ℂ) (q : MA.Qp P.r P.TT), q.1 = ((fun l => c l.castSucc), c (Fin.last P.r)) →
      D.IsLocPt (TBB.bigPt P.r c) (P.r + 1) → 0 < TBB.Gp p (TBB.bigPt P.r c) →
      ∑ ρ, ‖MA.evQ P (trJKB p e (B.JF p.T.base H) ρ) q‖ ^ 2 ≤
        C * (∏ l : Fin P.r, Complex.normSq (c l.castSucc)) * TBB.Ew p (fun _ => 1) H (P.r + 1) [] (TBB.bigPt P.r c)

end

end Formalism.FourierDecayAlt.P.CutBP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutTypeNormMeas
section
namespace Formalism.FourierDecayAlt.P.CutBP.TNM

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants Filter Topology MeasureTheory Matrix

noncomputable section

def TypeComm : Prop :=
  ∀ (P : M.Par) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
    (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp)) (z e : Fin (2 * P.r + P.k + 1) → ℂ) (TP : Top.TypeProj P π z e),
    IsCRepOn (UWset P.k P.r z) π → ContinuousOn π (UWset P.k P.r z) →
    (∀ h ∈ UWset P.k P.r z, ∀ v, ‖π h v‖ = ‖v‖) →
    1 ≤ P.k → inWb P.k P.r z → 0 < Tz P.k P.r z → inWb P.k P.r e → herm (Hpk P.k P.r) e z = 0 →
    herm (Hpk P.k P.r) e e = 1 →
    ∀ g ∈ UWset P.k P.r z, ∀ l : ℂ, g *ᵥ e = l • e → ∀ ρ, (TP.E ρ).comp (π g) = (π g).comp (TP.E ρ)

def HouseMeas : Prop :=
  ∀ (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ), inWb k r z → (herm (Hpk k r) z z).re < 0 →
    inWb k r e → herm (Hpk k r) e z = 0 → herm (Hpk k r) e e = 1 →
    ∃ h : (Fin (2 * r + k + 1) → ℂ) → B.Mat k r, Measurable h ∧ (∀ u, h u ∈ UWset k r z) ∧
      ∀ u, inWb k r u → herm (Hpk k r) u z = 0 → u ≠ 0 → ∃ l : ℂ, h u *ᵥ u = l • e

end

end Formalism.FourierDecayAlt.P.CutBP.TNM
end

