import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHB2
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsCompactCutoffCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0212
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBGLet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0246
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ComponentFamilySettingOfSettingBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0043
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0265
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0268
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceAtApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PbGermRateLowBOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermConstant
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0179
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0206
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHBCutOff
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates Formalism.FourierDecayAlt.P.PBQ

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def CutOffStep : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j)
    (γ : B.Mat P.k (P.r - (j + 1))),
    γ ∈ B.GV P.k (P.r - (j + 1)) →
    γ ∈ Q.OmPlus P.k (P.r - (j + 1)) (p.T.bs (j + 1)).z (p.T.bs (j + 1)).z' →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length))
      (Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp)), KB.CptCoef p.T.base Fc →
      (∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t →
        Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g) →
      B.JF (p.T.bs (j + 1)) (KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e) γ =
        B.JF (p.T.bs j) (KB.slv p.T Fc j (by omega) [] h hh.2 (fun a => a.elim0)) (mLev P j hj t γ)

def CutOffExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (j : ℕ) (hj : j + 1 ≤ P.r) (w : List C.Letter) (h : C.LPt) (hh : D.IsLocPt h j),
    KB.CptCoef p.T.base F →
    ∀ (t : ℂ) (ht : D.IsLocPt (h ++ [(1, t)]) (j + 1)) (e : Wd.Ix (Fin w.length)),
      ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef p.T.base Fc ∧
        ∀ g, Dmin P.k P.r p.T.base.z p.T.base.z' g ⟨j + 1, by omega⟩ = (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t →
          Fc g = D.uwG P.k P.r p.T.base.z p.T.base.z' F (j + 1) hj w e g

section proofs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

theorem det_hMat_app (h : C.LPt) (t : ℂ) :
    (U.hMat (D.ptPerm (h ++ [(1, t)])) (D.ptDiag (h ++ [(1, t)]))).det =
      (U.hMat (D.ptPerm h) (D.ptDiag h)).det * t := by
  rw [Formalism.FourierDecayAlt.P.PBI.det_hMat_pt, Formalism.FourierDecayAlt.P.PBI.det_hMat_pt h]
  have hsz : D.ptSize (h ++ [(1, t)]) = D.ptSize h + 1 := by
    simp [D.ptSize]
  rw [hsz, (Formalism.FourierDecayAlt.P.PBD.det_ptMatN_app t h (D.ptSize h) rfl).1, mul_comm]

theorem uwG_zero_of_G {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → (Wq →L[ℂ] Wp)) (ε : ℝ)
    (hε : ∀ g ∈ B.GV k r, F g ≠ 0 → ε ≤ Gf k r z z' g) (i : ℕ) (hi : i ≤ r) :
    ∀ (w : List C.Letter) (e : Wd.Ix (Fin w.length)), ∀ g ∈ B.GV k r,
      D.uwG k r z z' F i hi w e g ≠ 0 → ε ≤ Gf k r z z' g
  | [], _, g, hg, hne => hε g hg hne
  | l :: w, e, g, hg, hne => by
    by_contra hlt
    push Not at hlt
    apply hne
    show D.vLet k r z z' i hi l (e 0) (D.uwG k r z z' F i hi w fun a => e a.succ) g = 0
    refine Formalism.FourierDecayAlt.P.PBG.vLet_zero_near z z' i hi l (e 0) _ (V := {x | Gf k r z z' x < ε})
      (isOpen_lt (Formalism.FourierDecayAlt.P.DifferentialOperatorClasses.gf_cont k r z z') continuous_const) (fun x hx hxG => ?_) g hlt hg
    by_contra h0
    exact absurd (uwG_zero_of_G z z' F ε hε i hi w _ x hxG h0) (not_le.2 hx)

def cutW {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) (χ : ℂ → ℝ) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)) (i : ℕ)
    (hi : i ≤ P.r) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) : B.Mat P.k P.r → (Wq →L[ℂ] Wp) :=
  fun g => χ (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) • D.uwG P.k P.r Bs.z Bs.z' F i hi w e g

theorem cutW_exists {P : M.Par} (Bs : B.RealPlaceData P.k P.r Wp Wq) (F : B.Mat P.k P.r → (Wq →L[ℂ] Wp))
    (hF : KB.CptCoef Bs F) (i : ℕ) (hi : i ≤ P.r) (w : List C.Letter) (e : Wd.Ix (Fin w.length)) (a : ℂ)
    (ha : a ≠ 0) :
    ∃ Fc : B.Mat P.k P.r → (Wq →L[ℂ] Wp), KB.CptCoef Bs Fc ∧
      ∀ g, Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ = a → Fc g = D.uwG P.k P.r Bs.z Bs.z' F i hi w e g := by
  obtain ⟨hck, ⟨R, hR⟩, ε, hε, hεG⟩ := hF
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr ha
  let b : ContDiffBump a := ⟨‖a‖ / 4, ‖a‖ / 2, by positivity, by linarith⟩
  have hD : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat P.k P.r => Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) :=
    Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin Bs.z Bs.z' _
  have hbD : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat P.k P.r => b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩)) :=
    b.contDiff.comp hD
  have hne : ∀ g, cutW Bs b F i hi w e g ≠ 0 → D.uwG P.k P.r Bs.z Bs.z' F i hi w e g ≠ 0 := by
    intro g hg h0
    apply hg
    simp [cutW, h0]
  refine ⟨cutW Bs b F i hi w e, ⟨?_, ⟨R, fun g hg h1 => Formalism.FourierDecayAlt.P.PBG.uwG_supp Bs.z Bs.z' F R hR i hi w e g hg
      (hne g h1)⟩, ε, hε, fun g hg h1 => uwG_zero_of_G Bs.z Bs.z' F ε hεG i hi w e g hg (hne g h1)⟩, ?_⟩
  · intro g₀ hg₀
    by_cases h0 : Dmin P.k P.r Bs.z Bs.z' g₀ ⟨i, by omega⟩ = 0
    · refine ⟨{g | ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ < ‖a‖ / 2}, fun _ => 0,
        isOpen_lt (continuous_norm.comp hD.continuous) continuous_const, by simp [h0]; positivity,
        contDiffOn_const, fun g hg _ => ?_⟩
      have hb0 : b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) = 0 := by
        apply Function.notMem_support.1
        rw [b.support_eq, Metric.mem_ball, dist_eq_norm]
        intro hlt
        have h1 : ‖a‖ ≤ ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ - a‖ + ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ := by
          have := norm_sub_le (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩ - a)
          simp at this
          linarith
        have h2 : b.rOut = ‖a‖ / 2 := rfl
        have h3 : ‖Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩‖ < ‖a‖ / 2 := hg
        linarith
      simp [cutW, hb0]
    · obtain ⟨U, f', hU, hgU, hf', hE⟩ :=
        Formalism.FourierDecayAlt.P.PBG.uwG_mem Bs.z Bs.z' i hi hck w e g₀ h0 hg₀
      refine ⟨U, fun g => b (Dmin P.k P.r Bs.z Bs.z' g ⟨i, by omega⟩) • f' g, hU, hgU,
        (hbD.contDiffOn.of_le le_rfl).smul hf', fun g hg hgG => ?_⟩
      simp only [cutW]
      rw [hE g hg hgG]
  · intro g hg
    simp only [cutW]
    rw [hg, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le), one_smul]

end proofs

theorem truncation_off_exists_formula : CutOffExists := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh hF t ht e
  have ht0 : t ≠ 0 := (ht.1 (1, t) (List.mem_append_right _ (List.mem_singleton_self _))).2
  have hH : (U.hMat (D.ptPerm h) (D.ptDiag h)).det ≠ 0 := by
    rw [Formalism.FourierDecayAlt.P.PBI.det_hMat_pt, hh.2]
    exact Formalism.FourierDecayAlt.P.PBI.det_ptMatN_ne h j hh
  exact cutW_exists p.T.base F hF (j + 1) hj w e _ (mul_ne_zero hH ht0)

theorem truncation_off_induction : CutOffStep := by
  intro Wp Wq _ _ _ _ _ _ P p F j hj w h hh γ hγ hΩ t ht e Fc hFc hag
  have hs : KB.slv p.T F (j + 1) hj w (h ++ [(1, t)]) ht.2 e =
      KB.slv p.T Fc (j + 1) hj [] (h ++ [(1, t)]) ht.2 (fun a => a.elim0) := by
    unfold KB.slv
    congr 1
    apply Formalism.FourierDecayAlt.P.PBI.sliceAt_congr_Dr _ _ _ (by rw [ht.2]; exact hj)
    intro x hx
    symm
    show Fc x = _
    apply hag
    have e1 : (⟨j + 1, by omega⟩ : Fin (P.r + 2)) = ⟨D.ptSize (h ++ [(1, t)]), by rw [ht.2]; omega⟩ :=
      Fin.ext ht.2.symm
    rw [e1, hx, det_hMat_app]
  rw [hs, Formalism.FourierDecayAlt.P.slice_induction_level Wp Wq P p Fc j hj h t hh ht hFc γ hγ hΩ]
  rfl

end Formalism.FourierDecayAlt.P.CutHB
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLFrozen
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

section comm

variable {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}

theorem comm_Tm (Eu : Fin n → Fin n → A) (hG : GlRel Eu) (p a b : Fin n) (ha : a ≠ p) (hb : b ≠ p) (v : ℂ) :
    Commute (Eu p p) (Tm Eu v a b) := by
  unfold Tm
  refine Commute.add_right ?_ ?_
  · split_ifs
    · exact (Algebra.commutes v (Eu p p)).symm
    · exact Commute.zero_right _
  · have h := hG p p a b
    rw [if_neg (Ne.symm ha), if_neg hb, sub_zero] at h
    exact sub_eq_zero.mp h

theorem comm_qminor (Eu : Fin n → Fin n → A) (hG : GlRel Eu) {t : ℕ} (a b : Fin t → Fin n) (u : ℂ) (p : Fin n)
    (ha : ∀ i, a i ≠ p) (hb : ∀ i, b i ≠ p) : Commute (Eu p p) (qminor Eu a b u) := by
  unfold qminor
  refine Commute.sum_right _ _ _ (fun σ _ => ?_)
  refine Commute.mul_right (Int.cast_commute _ _).symm ?_
  refine Commute.list_prod_right _ _ (fun x hx => ?_)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
  exact comm_Tm Eu hG p _ _ (ha _) (hb i) _

end comm

section aa

variable {A : Type} [Ring A] [Algebra ℂ A] {k r : ℕ}

theorem AAx_congr_rows (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (xi xi' : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (u : ℂ)
    (h : ∀ a : Fin r, a.val < m → xi a = xi' a) : C3.AAx k r Eu xi m hm u = C3.AAx k r Eu xi' m hm u := by
  unfold C3.AAx
  simp only [show ∀ a : Fin m, xi (Fin.castLE hm a) = xi' (Fin.castLE hm a) from fun a => h _ a.isLt]

theorem AAv_congr_rows (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A)
    (y y' : Fin r → Fin (2 * r + k + 1) → ℂ) (m : ℕ) (hm : m ≤ r) (ℓ : ℂ)
    (h : ∀ a : Fin r, a.val < m → y a = y' a) : C3.AAv k r Eu y m hm ℓ = C3.AAv k r Eu y' m hm ℓ := by
  unfold C3.AAv
  simp only [show ∀ a : Fin m, y (Fin.castLE hm a) = y' (Fin.castLE hm a) from fun a => h _ a.isLt]

theorem comm_AAx (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : GlRel Eu)
    (xi : Fin r → Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j + 1 ≤ r) (u : ℂ)
    (h0 : ∀ a : Fin r, a.val < j → xi a (eI k r ⟨j, by omega⟩) = 0) :
    Commute (Eu (eI k r ⟨j, by omega⟩) (eI k r ⟨j, by omega⟩)) (C3.AAx k r Eu xi j (by omega) u) := by
  unfold C3.AAx
  refine Commute.sum_right _ _ _ (fun c _ => ?_)
  split_ifs with hc
  · by_cases hp : ∃ l, c l = eI k r ⟨j, by omega⟩
    · obtain ⟨l, hl⟩ := hp
      have hdet : (of fun (a l : Fin j) => xi (Fin.castLE (by omega) a) (c l)).det = 0 := by
        apply Matrix.det_eq_zero_of_column_eq_zero l
        intro a
        simp only [of_apply, hl]
        exact h0 _ a.isLt
      simp only [hdet, zero_smul]
      exact Commute.zero_right _
    · push_neg at hp
      refine Commute.smul_right ?_ _
      refine comm_qminor Eu hG _ _ u _ (fun i => ?_) hp
      have := i.isLt
      simp only [C3.xR, eI, ne_eq, Fin.ext_iff, Fin.coe_castLE]
      omega
  · exact Commute.zero_right _

theorem comm_AAv (Eu : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → A) (hG : GlRel Eu)
    (y : Fin r → Fin (2 * r + k + 1) → ℂ) (j : ℕ) (hj : j + 1 ≤ r) (ℓ : ℂ)
    (h0 : ∀ a : Fin r, a.val < j → y a (esI k r ⟨j, by omega⟩) = 0) :
    Commute (Eu (esI k r ⟨j, by omega⟩) (esI k r ⟨j, by omega⟩)) (C3.AAv k r Eu y j (by omega) ℓ) := by
  unfold C3.AAv
  refine Commute.sum_right _ _ _ (fun c _ => ?_)
  split_ifs with hc
  · by_cases hp : ∃ l, c l = esI k r ⟨j, by omega⟩
    · obtain ⟨l, hl⟩ := hp
      have hdet : (of fun (a l : Fin j) => y (Fin.castLE (by omega) a) (c l)).det = 0 := by
        apply Matrix.det_eq_zero_of_column_eq_zero l
        intro a
        simp only [of_apply, hl]
        exact h0 _ a.isLt
      simp only [hdet, zero_smul]
      exact Commute.zero_right _
    · push_neg at hp
      refine Commute.smul_right ?_ _
      refine comm_qminor Eu hG _ _ _ _ hp (fun i => ?_)
      have := i.isLt
      simp only [C3.sR, esI, ne_eq, Fin.ext_iff, Fin.coe_castLE]
      omega
  · exact Commute.zero_right _

end aa

section what₂

variable {k r j : ℕ}

private theorem x0_esI_apply_eq_dite_Z {k r j : ℕ} (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ)
    (γ : B.Mat k (r - (j + 1))) (a : Fin r) (ha : a.val < j) (q : Fin (2 * r + k + 1)) :
    x0 k r j hj Z τ γ (esI k r a) q = if h : q.val < j then Z ⟨a.val, ha⟩ ⟨q.val, h⟩ else 0 := by
  simp only [x0, Dx2.Split.castM_apply, U.mMap, U.blk3, reindex_apply, submatrix_apply]
  have he : (U.eB k (j + 1) (r - (j + 1))).symm (Fin.cast (by omega) (esI k r a)) =
      Sum.inr ⟨j - a.val, by omega⟩ := by
    rw [Equiv.symm_apply_eq]
    simp [U.eB, esI, Fin.ext_iff]
    omega
  rw [he]
  rcases hq : (U.eB k (j + 1) (r - (j + 1))).symm (Fin.cast (by omega) q) with (l | l) | l
  all_goals rw [Equiv.symm_apply_eq] at hq
  all_goals have hv := congrArg Fin.val hq
  all_goals simp [U.eB] at hv
  · rw [fromBlocks_apply₂₁, fromCols_apply_inl, StandardCharacterExists.wMat_mul_apply]
    have hr : (⟨j - a.val, by omega⟩ : Fin (j + 1)).rev = Fin.castAdd 1 ⟨a.val, ha⟩ := by
      ext
      simp
      omega
    rw [hr]
    simp only [zfull, U.blk2, reindex_apply, submatrix_apply, finSumFinEquiv_symm_apply_castAdd]
    by_cases hl : l.val < j
    · have hl' : l = Fin.castAdd 1 ⟨l.val, hl⟩ := by
        ext
        simp
      rw [hl', finSumFinEquiv_symm_apply_castAdd, fromBlocks_apply₁₁, dif_pos (by omega)]
      congr 1
      ext
      simp [hv]
    · have hl' : l = Fin.natAdd j 0 := by
        ext
        simp
        omega
      rw [hl', finSumFinEquiv_symm_apply_natAdd, fromBlocks_apply₁₂, dif_neg (by omega)]
      rfl
  · rw [fromBlocks_apply₂₁, fromCols_apply_inr, dif_neg (by omega)]
    rfl
  · rw [fromBlocks_apply₂₂, dif_neg (by omega)]
    rfl

private theorem xi0_apply_eq_esI_apply {k r : ℕ} (g : B.Mat k r) (a : Fin r) (p : Fin (2 * r + k + 1)) :
    PBG.xi0 g a p = g (esI k r a) p := by
  have hH : ∀ s, Hpk k r (eI k r a) s = if s = esI k r a then 1 else 0 := by
    intro s
    have := a.isLt
    have := s.isLt
    simp only [Hpk, eI, esI, Fin.ext_iff, Fin.val_mk]
    have hd : 2 * r + k - (a : ℕ) + a = 2 * r + k := Nat.sub_add_cancel (by omega)
    generalize 2 * r + k - (a : ℕ) = d at *
    split_ifs <;> first | rfl | omega
  simp [PBG.xi0, herm, bvec, mulVec, dotProduct, Pi.single_apply, hH]

private theorem sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV {k r : ℕ} (g : B.Mat k r) (hg : g ∈ B.GV k r) (a : Fin r)
    (p : Fin (2 * r + k + 1)) :
    GBasic.sgn k r (GBasic.sig k r p) * PBG.y0 g a p = star (g (esI k r a) (GBasic.sig k r p)) := by
  have hs : GBasic.sig k r (GBasic.sig k r p) = p := by
    have := p.isLt
    ext
    simp only [GBasic.sig]
    split_ifs with h1 h2 h2 <;> simp only [Fin.val_mk] at * <;> omega
  have hn : GBasic.sgn k r (eI k r a) = 1 := by
    have := a.isLt
    rw [GBasic.sgn, if_neg]
    simp only [eI, Fin.val_mk]
    omega
  have he : GBasic.sig k r (eI k r a) = esI k r a := by
    have := a.isLt
    ext
    simp [GBasic.sig, eI, esI]
  have hu := B2x5.isUnit_det_GV hg
  have h1 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
    calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg']
      _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc (gᴴ * Hpk k r), Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have h2 := congrFun (congrFun h1 (GBasic.sig k r p)) (eI k r a)
  rw [C2x6.Hpk_mul_apply, C2x6.mul_Hpk_apply] at h2
  rw [hs, he, hn, mul_one, conjTranspose_apply] at h2
  have hy : PBG.y0 g a p = g⁻¹ p (eI k r a) := by
    simp [PBG.y0, bvec, mulVec, dotProduct, Pi.single_apply]
  rw [hy, h2]

theorem xi0_row_independent_of_tau (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ τ' : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a : Fin r) (ha : a.val < j) : PBG.xi0 (x0 k r j hj Z τ' γ) a = PBG.xi0 (x0 k r j hj Z τ γ) a := by
  funext p
  rw [xi0_apply_eq_esI_apply, xi0_apply_eq_esI_apply, x0_esI_apply_eq_dite_Z hj Z τ' γ a ha, x0_esI_apply_eq_dite_Z hj Z τ γ a ha]

theorem xi0_x0_eI_j_eq_zero (hj : j + 1 ≤ r) (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (γ : B.Mat k (r - (j + 1)))
    (a : Fin r) (ha : a.val < j) : PBG.xi0 (x0 k r j hj Z τ γ) a (eI k r ⟨j, by omega⟩) = 0 := by
  rw [xi0_apply_eq_esI_apply, x0_esI_apply_eq_dite_Z hj Z τ γ a ha, dif_neg]
  simp [eI]

theorem y0_row_independent_of_tau (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ τ' : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    (hτ' : τ' ≠ 0) {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1))) (a : Fin r) (ha : a.val < j) :
    PBG.y0 (x0 k r j hj Z τ' γ) a = PBG.y0 (x0 k r j hj Z τ γ) a := by
  funext p
  have hs : GBasic.sgn k r (GBasic.sig k r p) ≠ 0 := by
    unfold GBasic.sgn
    split_ifs <;> norm_num
  apply mul_left_cancel₀ hs
  rw [sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV _ (LevelPointCoordinates.x0_GV hj hZ hτ' hγ), sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV _ (LevelPointCoordinates.x0_GV hj hZ hτ hγ),
    x0_esI_apply_eq_dite_Z hj Z τ' γ a ha, x0_esI_apply_eq_dite_Z hj Z τ γ a ha]

theorem y0_x0_esI_j_eq_zero_of_det_ne_zero (hj : j + 1 ≤ r) {Z : Matrix (Fin j) (Fin j) ℂ} {τ : ℂ} (hZ : Z.det ≠ 0) (hτ : τ ≠ 0)
    {γ : B.Mat k (r - (j + 1))} (hγ : γ ∈ B.GV k (r - (j + 1))) (a : Fin r) (ha : a.val < j) :
    PBG.y0 (x0 k r j hj Z τ γ) a (esI k r ⟨j, by omega⟩) = 0 := by
  have hs : GBasic.sgn k r (GBasic.sig k r (esI k r ⟨j, by omega⟩)) ≠ 0 := by
    unfold GBasic.sgn
    split_ifs <;> norm_num
  apply mul_left_cancel₀ hs
  rw [sgn_sig_mul_y0_eq_star_esI_apply_of_mem_GV _ (LevelPointCoordinates.x0_GV hj hZ hτ hγ), x0_esI_apply_eq_dite_Z hj Z τ γ a ha, dif_neg, mul_zero, star_zero]
  have : j + 1 ≤ r := hj
  have hse : (GBasic.sig k r (esI k r ⟨j, by omega⟩)).val = j := by
    unfold GBasic.sig
    rw [if_pos (Or.inr (by simp only [esI]; omega))]
    simp only [esI]
    omega
  rw [hse]
  omega

end what₂

theorem frozen_X_identity : FrozenX := by
  intro A _ _ k r j hj Eu Z τ τ' u γ hG hZ hτ hτ' hγ
  exact ⟨AAx_congr_rows Eu _ _ j _ u (fun a ha => xi0_row_independent_of_tau hj Z τ τ' γ a ha),
    comm_AAx Eu hG _ j hj u (fun a ha => xi0_x0_eI_j_eq_zero hj Z τ γ a ha)⟩

theorem frozen_V_identity : FrozenV := by
  intro A _ _ k r j hj Eu Z τ τ' ℓ γ hG hZ hτ hτ' hγ
  exact ⟨AAv_congr_rows Eu _ _ j _ ℓ (fun a ha => y0_row_independent_of_tau hj hZ hτ hτ' hγ a ha),
    comm_AAv Eu hG _ j hj ℓ (fun a ha => y0_x0_esI_j_eq_zero_of_det_ne_zero hj hZ hτ hγ a ha)⟩

end Formalism.FourierDecayAlt.P.CutHL
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutHLNf
section
open Matrix
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutHL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

theorem zfull_zb {j : ℕ} (Z : Matrix (Fin j) (Fin j) ℂ) (τ : ℂ) (a b : Fin (j + 1)) :
    zfull Z τ a b = C3.Zb j 1 Z τ a.val b.val := by
  rw [zfull_apply]
  unfold C3.Zb
  have := a.isLt; have := b.isLt
  by_cases h1 : a.val < j ∧ b.val < j
  · rw [dif_pos h1, dif_pos h1.1, dif_pos h1.2]
  · rw [dif_neg h1]
    by_cases ha : a.val < j
    · have hb : ¬ b.val < j := fun hb => h1 ⟨ha, hb⟩
      rw [dif_pos ha, dif_neg hb, if_neg (fun h => by omega)]
    · rw [dif_neg ha]
      by_cases h2 : a.val = j ∧ b.val = j
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)]

theorem normal_form_x0 : NormalFormsAtBasePoint := by
  intro k r j hj Z τ γ hZ hτ hγ
  refine ⟨fun a p ha => ?_, fun a p ha => ?_⟩
  · rw [upper_minor_of_level_point hj Z τ γ a p ha]
    by_cases hp : p.val < j + 1
    · rw [dif_pos hp, if_pos hp]
      exact zfull_zb Z τ _ _
    · rw [dif_neg hp, if_neg hp]
  · rw [lower_minor_of_level_point hj hZ hτ hγ a p ha]
    by_cases hp : r + k < p.val ∧ 2 * r + k - p.val < j + 1
    · rw [dif_pos hp, if_pos hp]
      exact congrArg star (zfull_zb Z τ _ _)
    · rw [dif_neg hp, if_neg hp]

theorem leading_minors_at_base_point : LeadingMinorsAtBasePoint := by
  intro k r j hj z z' Z τ γ hZ hτ hγ
  have hnf := (normal_form_x0 k r j hj Z τ γ hZ hτ hγ).1
  have hd := Formalism.FourierDecayAlt.P.SignAntidiagonal.derivative_leading_zb j 1 Z τ
  refine ⟨?_, ?_⟩
  · rw [PBG.dmin_nf z z' _ j 1 Z τ hj hnf j (by omega), hd.1]
  · rw [PBG.dmin_nf z z' _ j 1 Z τ hj hnf (j + 1) le_rfl, hd.2]
    simp [C3.sgnW]

theorem first_component_of_parts : Comp1OfParts := by
  intro hNf k r j hj z z' E _ _ Dm Φ Z γ τ hH Y
  obtain ⟨hz, hz', hD, hDs, hR, hZ, hτ, hγ, hx⟩ := hH
  obtain ⟨hnf, hnfy⟩ := hNf k r j hj Z τ γ hZ hτ hγ
  have hxG : x0 k r j hj Z τ γ ∈ B.GV k r := x0_GV hj hZ hτ hγ
  have hx1 : x0 k r j hj Z τ γ ∈ Q.Glev k r 0 ∩ Dm := ⟨⟨hxG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hx⟩
  have hK : Q.SmoothLev k r 0 Dm Φ := hR.1
  have hRule : ∀ g ∈ Q.Glev k r 0 ∩ Dm, ∀ p q, C3.InNp k r p q → Q.EH k r p q Φ g = C3.dpsiP k r z' p q • Φ g :=
    fun g hg p q hpq => Formalism.FourierDecayAlt.P.rule_of_eq E k r z' Φ g hz' (fun n hn => (hR.2.1 g hg n hn).2) p q hpq
  refine ⟨?_, ?_⟩
  · have h := PBG.letter_plus_component_one_eq_smul_component_zero hD z z' j 1 le_rfl hj Z τ hZ hτ _ hx1 hnf Φ hK hRule Y
    rw [show ((-1 : ℂ) ^ (1 - 1) * τ⁻¹) = τ⁻¹ by simp] at h
    exact h
  · have h := PBG.letter_minus_component_one_eq_smul_component_zero hD z z' j 1 le_rfl hj Z τ hZ hτ _ hx1 hxG hnf hnfy Φ hK hRule Y
    rw [show ((-1 : ℂ) ^ (1 - 1) * (conj τ)⁻¹) = (conj τ)⁻¹ by simp] at h
    exact h

theorem headLetter_of_open (hL : LeftActionRuleAtBasePoint) (hT : TorusDirectionAtBasePoint) (hSL : ConjugateActionRuleAtBasePoint) (hST : ConjugateTorusDirectionAtBasePoint)
    (hFX : FrozenX) (hFV : FrozenV) (hPP : PlusPosOfParts) (hPZ : PlusZeroOfParts) (hMP : MinusPosOfParts)
    (hMZ : MinusZeroOfParts) : LevelPointCoordinates.HeadLetter :=
  headLetter_of_leaves normal_form_x0 leading_minors_at_base_point hL hT hSL hST hFX hFV first_component_of_parts hPP hPZ hMP hMZ

end Formalism.FourierDecayAlt.P.CutHL
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateLowerBound
section
namespace Formalism.FourierDecayAlt.P

theorem germ_at_place : FormNormSumIdentities.GermPlace :=
  FormNormSumIdentities.germPlace_of slice_integral_cutoff slice_germ_points form_model

theorem germ_rate_lower_bound : GermRateSplit.GermRateLowB :=
  FormNormSumIdentities.germRateLowB_of germ_at_place germ_null_set_compact germ_constant

end Formalism.FourierDecayAlt.P
end

