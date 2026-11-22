import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTConnCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0076
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPIntegralOfPlaces
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0037
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CapelliTwoByTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0032

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def SSLoc (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')))
    (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ) : Prop :=
  ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P),
    trR P Bs e ((d.SS l).1 Φ) ρ' = ∑ ρ, fnZ P (s l ρ' ρ) * trR P Bs e Φ ρ ∧
    trR P Bs e ((star (d.SS l)).1 Φ) ρ' = ∑ ρ, fnZ P (t l ρ' ρ) * trR P Bs e Φ ρ

def SmST (P : M.Par) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ) : Prop :=
  ∀ l ρ' ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (s l ρ' ρ) (Ann P) ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (t l ρ' ρ) (Ann P)

end preds

def GTSSLocal : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∃ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t ∧ SSLoc P Bs d e s t

def GTRadAdj : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ (Y : ℂ) (a b : Fin 2) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    ∀ Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∃ K : Set ℂ, IsCompact K ∧ K ⊆ Ann P ∧ ∀ ζ ∈ Ann P, ζ ∉ K →
        (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = 0 ∧
          (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = 0) →
      ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((X.t Y a b Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))) =
        ∫ ζ in Ann P, (((wR P.k P.TT ζ) ^ 2 : ℝ) : ℂ) *
          inner ℂ (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))
            (B.hsVec ((X.t (star Y) b a Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))

def GTSSAdjPt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t → SSLoc P Bs d e s t →
        ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, ∀ ζ ∈ Ann P, t l ρ ρ' ζ = star (s l ρ' ρ ζ)

def GTSSConst : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t → SSLoc P Bs d e s t →
        ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ' ρ : M.Ty P, ∃ C D : ℂ, ∀ ζ ∈ Ann P, s l ρ' ρ ζ = C ∧ t l ρ' ρ ζ = D

def GTSSPhase : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e → NabF P Bs d e →
      ∀ s t : ℕ → M.Ty P → M.Ty P → ℂ, SSLoc P Bs d e (fun l ρ' ρ _ => s l ρ' ρ) (fun l ρ' ρ _ => t l ρ' ρ) →
        (∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ ρ ρ' : M.Ty P, t l ρ ρ' = star (s l ρ' ρ)) →
        ∃ e' : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e' ∧ KapF P Bs d e' ∧ NabF P Bs d e' ∧ SSF P Bs d e'

theorem fnZ_congr (P : M.Par) {f g : ℂ → ℂ} (h : ∀ ζ ∈ Ann P, f ζ = g ζ) : fnZ P f = fnZ P g := by
  unfold fnZ
  congr 1
  funext q
  exact h _ q.2.2

theorem ann_pt (P : M.Par) (hTT : 0 < P.TT) : ((Real.sqrt P.TT + 1 : ℝ) : ℂ) ∈ Ann P := by
  show P.TT < Complex.normSq (((Real.sqrt P.TT + 1 : ℝ)) : ℂ)
  rw [Complex.normSq_ofReal]
  have h1 := Real.sq_sqrt hTT.le
  have h2 := Real.sqrt_nonneg P.TT
  nlinarith

def GTSSOfCut : Prop := GTSSLocal → GTSSAdjPt → GTSSConst → GTSSPhase → GTSS

theorem gTSS_of_cut : GTSSOfCut := by
  intro hL hA hC hP
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk hn
  obtain ⟨s, t, hst, hSL⟩ := hL Wp Wq P Bs X d hH e he hk
  have hc := hC Wp Wq P Bs X d hH e he hk hn s t hst hSL
  choose! C D hCD using hc
  have hζ0 : (((|P.TT| + 1 : ℝ)) : ℂ) ∈ Ann P := by
    show P.TT < Complex.normSq (((|P.TT| + 1 : ℝ)) : ℂ)
    rw [Complex.normSq_ofReal]
    nlinarith [abs_nonneg P.TT, le_abs_self P.TT]
  apply hP Wp Wq P Bs X d hH e he hk hn C D
  · intro l hl Φ ρ'
    obtain ⟨h1, h2⟩ := hSL l hl Φ ρ'
    refine ⟨h1.trans ?_, h2.trans ?_⟩
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [fnZ_congr P (f := s l ρ' ρ) (g := fun _ => C l ρ' ρ) (fun ζ hζ => (hCD l hl ρ' ρ ζ hζ).1)]
    · refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [fnZ_congr P (f := t l ρ' ρ) (g := fun _ => D l ρ' ρ) (fun ζ hζ => (hCD l hl ρ' ρ ζ hζ).2)]
  · intro l hl ρ ρ'
    have h := hA Wp Wq P Bs X d hH e he hk s t hst hSL l hl ρ ρ' _ hζ0
    rw [(hCD l hl ρ ρ' _ hζ0).2, (hCD l hl ρ' ρ _ hζ0).1] at h
    exact h

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreKLLieGrpGeo
section
open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.QrD

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

namespace KLG

open Formalism.FourierDecayAlt.P.HermitianFormRankFour

variable {k r : ℕ}

def cvec2 (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ) : JJ r ⊕ Unit → Fin (2 * r + k + 1) → ℂ :=
  Sum.elim (cvec k r z) (fun _ => e)

def cvec2' (k r : ℕ) (z e : Fin (2 * r + k + 1) → ℂ) : JJ r ⊕ Unit → Fin (2 * r + k + 1) → ℂ :=
  Sum.elim (cvec' k r z) (fun _ => e)

theorem sum_unitB {m : ℕ} (Bs : Fin m → Fin (2 * r + k + 1) → ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    colM Bs * B * ((colM Bs)ᴴ * Hpk k r) = ∑ p : Fin m × Fin m, B p.1 p.2 • unitB (Hpk k r) Bs p.1 p.2 := by
  ext i j
  have hu : ∀ a b, unitB (Hpk k r) Bs a b i j = Bs a i * ∑ q, star (Bs b q) * Hpk k r q j := by
    intro a b
    simp only [unitB, Matrix.of_apply, herm, dotProduct, Matrix.mulVec, bvec, Pi.star_apply]
    congr 1
    refine Finset.sum_congr rfl fun q _ => ?_
    simp [Pi.single_apply]
  rw [Matrix.sum_apply]
  simp only [Matrix.smul_apply, smul_eq_mul, hu, Matrix.mul_apply, colM, Matrix.of_apply,
    Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, b]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro q _
  ring

theorem stab_exp {z e : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (he : inWb k r e)
    (hez : herm (Hpk k r) e z = 0) (hee : herm (Hpk k r) e e = 1) {Bs : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ}
    (hB : IsFrameOf k r [z, e] Bs) {h : Mx k r} (hh : h ∈ UWset k r z) (hhe : h *ᵥ e = e) :
    ∃ B : Matrix (Fin (k - 1)) (Fin (k - 1)) ℂ, Bᴴ = -B ∧
      NormedSpace.exp (colM Bs * B * ((colM Bs)ᴴ * Hpk k r)) = h := by
  have hzz : herm (Hpk k r) z z ≠ 0 := by
    intro e0
    unfold Tz at hT
    rw [e0] at hT
    simp at hT
  have hBz : IsFrameOf k r [z] Bs := ⟨hB.1, hB.2.1, fun a v hv => hB.2.2 a v (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢; exact Or.inl hv)⟩
  have hE : IsFrameOf k r [z] (fun _ : Fin 1 => e) := ⟨fun _ => he, fun a b => by
    simp [Subsingleton.elim a b, hee], fun _ v hv => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    subst hv
    exact hez⟩
  have hBe : ∀ a, herm (Hpk k r) (Bs a) e = 0 := fun a => hB.2.2 a e (by simp)
  have hBe' : ∀ a, herm (Hpk k r) e (Bs a) = 0 := fun a => by rw [← Qx2.herm_star, hBe a, star_zero]
  have g1 : (colM Bs)ᴴ * Hpk k r * colM Bs = 1 := by
    ext a b
    rw [gramM_apply, hB.2.1, Matrix.one_apply]
    simp [eq_comm]
  have g2 : (colM Bs)ᴴ * Hpk k r * colM (cvec2 k r z e) = 0 := by
    ext a j
    rw [gramM_apply]
    rcases j with j | _
    · exact gram_VC hBz a j
    · exact hBe' a
  have g3 : (colM (cvec2' k r z e))ᴴ * Hpk k r * colM Bs = 0 := by
    ext j a
    rw [gramM_apply]
    rcases j with j | _
    · exact gram_CV hBz a j
    · exact hBe a
  have g4 : (colM (cvec2' k r z e))ᴴ * Hpk k r * colM (cvec2 k r z e) = 1 := by
    ext i j
    rw [gramM_apply, Matrix.one_apply]
    rcases i with i | _ <;> rcases j with j | _
    · simp only [cvec2, cvec2', Sum.elim_inl, Sum.inl.injEq]
      exact gram_CC hz hzz i j
    · simp only [cvec2, cvec2', Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact gram_CV hE 0 i
    · simp only [cvec2, cvec2', Sum.elim_inl, Sum.elim_inr, reduceCtorEq, if_false]
      exact gram_VC hE 0 j
    · simp [cvec2, cvec2', hee]
  have hJ : Fintype.card (JJ r ⊕ Unit) ≤ Fintype.card (Fin (2 * r + k + 1)) := by
    have h1 := Matrix.rank_mul_le_right ((colM (cvec2' k r z e))ᴴ * Hpk k r) (colM (cvec2 k r z e))
    rw [g4, Matrix.rank_one] at h1
    exact h1.trans (Matrix.rank_le_card_height _)
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit] at hJ
  have hc := complete (Fintype.equivOfCardEq (by simp; omega)) g1 g2 g3 g4
  have hC : h * colM (cvec2 k r z e) = colM (cvec2 k r z e) := by
    rw [mul_colM]
    congr 1
    funext j
    rcases j with j | _
    · exact fix_c hh j
    · exact hhe
  have hC' : h * colM (cvec2' k r z e) = colM (cvec2' k r z e) := by
    rw [mul_colM]
    congr 1
    funext j
    rcases j with j | _
    · exact fix_c' hh j
    · exact hhe
  have hCd := dual_fix hh.1 hC'
  obtain ⟨e1, e2⟩ := decomp hc g3 h hC hCd
  obtain ⟨B, hBs, hBe⟩ := unitary_log _ (unitary_of Qx8.hpk_herm hh.1 g1 e1)
  refine ⟨B, hBs, ?_⟩
  rw [exp_lift hc g1 g2 B, hBe, ← e2]

end KLG

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddScalBound
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA

noncomputable section

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.BetaSesquilinearity PI.UnitaryCorollaryDerivatives.CRH Formalism.FourierDecayAlt.P.AdmissibleLieWords

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

def regE (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) : Set (B.Mat k r) :=
  {g | g ∈ B.GV k r ∧ ε ≤ Gf k r D.z D.z' g}

theorem regE_sub (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) : regE D ε ⊆ B.GV k r := fun _ hg => hg.1

theorem scal_bound_of_ubl (D : B.RealPlaceData k r Wp Wq) (φ : B.Mat k r → ℂ) (e γ : ℕ) (Bg : ℝ)
    (hBg : (e : ℝ) + γ ≤ Bg) (ε : ℝ)
    (h0 : ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖φ g‖ ≤ C0) (hU : ∀ n : ℕ, UBL φ (regE D ε) n e γ) (m : ℕ) :
    ∃ C : ℝ, ∀ u w : List (B.Mat k r),
      (∀ X ∈ u, B.unitLie k r X) → (∀ X ∈ w, B.unitLie k r X) → u.length + w.length ≤ m →
      ∀ g ∈ B.GV k r, ε ≤ Gf k r D.z D.z' g → ‖B.dLR u w φ g‖ ≤ C * B.gN g ^ (Bg * m) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    obtain ⟨C0, hC0⟩ := h0
    refine ⟨C0, fun u w _ _ hl g hg hgε => ?_⟩
    have hu : u = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hw : w = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hu hw
    simp only [Nat.cast_zero, mul_zero, Real.rpow_zero, mul_one]
    exact hC0 g ⟨hg, hgε⟩
  · obtain ⟨⟨C, hC0, hUB⟩, -⟩ := hU m
    refine ⟨C, fun u w hu hw hl g hg hgε => ?_⟩
    have hA : admitted m (wL u ++ wR w) := ⟨u, w, hu, hw, hl, rfl⟩
    have hb := hUB _ hA g ⟨hg, hgε⟩
    rw [dLR_eq]
    refine hb.trans (mul_le_mul_of_nonneg_left ?_ hC0)
    have h1 : 1 ≤ B.gN g := gN_ge_one hg
    rw [← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le h1
    rw [len_LR]
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hl' : ((u.length + w.length : ℕ) : ℝ) ≤ m := by exact_mod_cast hl
    have he : (0 : ℝ) ≤ e := Nat.cast_nonneg _
    have hγ : (0 : ℝ) ≤ γ := Nat.cast_nonneg _
    push_cast at hl' ⊢
    nlinarith [mul_le_mul_of_nonneg_left hl' hγ, mul_le_mul_of_nonneg_left hm1 he,
      mul_le_mul_of_nonneg_right hBg (by linarith : (0 : ℝ) ≤ m)]

theorem dlast_pos (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) {g : B.Mat k r} (hg : ε ≤ Gf k r D.z D.z' g) :
    ε ≤ Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1))) :=
  Formalism.FourierDecayAlt.P.gram_function_last_minor k r D.z D.z' D.T_pos.le D.T'_pos.le g ε hg

theorem dlast_ne (D : B.RealPlaceData k r Wp Wq) {g : B.Mat k r} (hg : g ∈ B.GPos D) :
    Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0 := by
  intro h
  have := dlast_pos D hg.2 (le_refl _)
  rw [h, map_zero] at this
  linarith [hg.2]

theorem open_dlast (z z' : Fin (2 * r + k + 1) → ℂ) :
    IsOpen {g : B.Mat k r | Dmin k r z z' g (Fin.last (r + 1)) ≠ 0} :=
  isOpen_ne_fun (Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin z z' _).continuous continuous_const

theorem ckOn_phiR (D : B.RealPlaceData k r Wp Wq) : B.CkOn ⊤ (B.GPos D) (phiR k r D.z D.z') := by
  intro g₀ hg₀
  refine ⟨{g : B.Mat k r | Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0}, phiR k r D.z D.z', open_dlast D.z D.z',
    dlast_ne D hg₀, ?_, fun _ _ _ => rfl⟩
  have h0 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' ⟨r, by omega⟩
  have h1 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' (Fin.last (r + 1))
  refine (h0.contDiffOn.mul (h1.contDiffOn.inv (fun x hx => hx))).congr (fun x _ => ?_)
  simp [phiR, div_eq_mul_inv]

theorem ckOn_phiD (D : B.RealPlaceData k r Wp Wq) : B.CkOn ⊤ (B.GPos D) (phiD k r D.z D.z') := by
  intro g₀ hg₀
  refine ⟨{g : B.Mat k r | Dmin k r D.z D.z' g (Fin.last (r + 1)) ≠ 0}, phiD k r D.z D.z', open_dlast D.z D.z',
    dlast_ne D hg₀, ?_, fun _ _ _ => rfl⟩
  have h1 := Formalism.FourierDecayAlt.P.JCx1.contDiff_Dmin (k := k) (r := r) D.z D.z' (Fin.last (r + 1))
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun g : B.Mat k r => (starRingEnd ℂ) (Dmin k r D.z D.z' g (Fin.last (r + 1)))) :=
    Complex.conjCLE.contDiff.comp h1
  refine (h1.contDiffOn.mul (h2.contDiffOn.inv (fun x hx => by simpa using hx))).congr (fun x _ => ?_)
  simp [phiD, div_eq_mul_inv]

theorem phiR_le (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) :
    ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖phiR k r D.z D.z' g‖ ≤ C0 := by
  set T := Tz k r D.z * Tz k r D.z' with hT
  have hT0 : 0 < T := mul_pos D.T_pos D.T'_pos
  refine ⟨1 + 1 / T, fun g hg => ?_⟩
  have hG := hg.2
  have h1 := dlast_pos D hε hG
  have hpos : 0 < Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1))) := lt_of_lt_of_le hε h1
  unfold Gf at hG
  set a := Complex.normSq (Dmin k r D.z D.z' g ⟨r, by omega⟩)
  set b := Complex.normSq (Dmin k r D.z D.z' g (Fin.last (r + 1)))
  have hsq : ‖phiR k r D.z D.z' g‖ ^ 2 = a / b := by
    rw [← Complex.normSq_eq_norm_sq]
    simp only [phiR, Complex.normSq_div]
    rfl
  have hle : a / b ≤ 1 / T := by
    rw [div_le_div_iff₀ hpos hT0]
    nlinarith
  have hx := norm_nonneg (phiR k r D.z D.z' g)
  nlinarith [sq_nonneg (‖phiR k r D.z D.z' g‖ - 1)]

theorem phiD_le (D : B.RealPlaceData k r Wp Wq) (ε : ℝ) :
    ∃ C0 : ℝ, ∀ g ∈ regE D ε, ‖phiD k r D.z D.z' g‖ ≤ C0 := by
  refine ⟨1, fun g _ => ?_⟩
  simp only [phiD, norm_div, Complex.norm_conj]
  exact div_self_le_one _

theorem ubl_phiR (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    UBL (phiR k r D.z D.z') (regE D ε) n r (r + 1) := by
  have hP0 : U.IsPolyDeg r (fun g : B.Mat k r => Dmin k r D.z D.z' g ⟨r, by omega⟩) :=
    Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' ⟨r, by omega⟩
  have hP1 : U.IsPolyDeg (r + 1) (fun g : B.Mat k r => Dmin k r D.z D.z' g (Fin.last (r + 1))) := by
    have := Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' (Fin.last (r + 1))
    simpa using this
  have ha := ubl_poly hP0 (regE D ε) (regE_sub D ε) n (r + 1)
  have hb := ubl_invpow hP1 (regE_sub D ε) hε (fun g hg => dlast_pos D hε hg.2) 1 n
  have hm := ubl_mul (regE_sub D ε) ha hb
  have e : phiR k r D.z D.z' = fun g => Dmin k r D.z D.z' g ⟨r, by omega⟩ *
      (Dmin k r D.z D.z' g (Fin.last (r + 1)))⁻¹ ^ 1 := by
    funext g; simp [phiR, div_eq_mul_inv]
  rw [e]
  simpa using hm

theorem ubl_phiD (D : B.RealPlaceData k r Wp Wq) {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    UBL (phiD k r D.z D.z') (regE D ε) n (r + 1) (r + 1) := by
  have hP1 : U.IsPolyDeg (r + 1) (fun g : B.Mat k r => Dmin k r D.z D.z' g (Fin.last (r + 1))) := by
    have := Formalism.FourierDecayAlt.P.minor_polynomial_property k r D.z D.z' (Fin.last (r + 1))
    simpa using this
  have hP2 := Formalism.FourierDecayAlt.P.CutMP.jdh_pd_star hP1
  have ha := ubl_poly hP1 (regE D ε) (regE_sub D ε) n (r + 1)
  have hb := ubl_invpow hP2 (regE_sub D ε) hε
    (fun g hg => by simpa [Complex.star_def] using dlast_pos D hε hg.2) 1 n
  have hm := ubl_mul (regE_sub D ε) ha hb
  have e : phiD k r D.z D.z' = fun g => Dmin k r D.z D.z' g (Fin.last (r + 1)) *
      (star (Dmin k r D.z D.z' g (Fin.last (r + 1))))⁻¹ ^ 1 := by
    funext g; simp [phiD, div_eq_mul_inv]
  rw [e]
  simpa using hm

end

theorem scalar_transfer_bound_holds : JAScalBound := by
  refine ⟨2, by norm_num, ?_⟩
  intro k r Wp Wq _ _ _ _ D Bg hBg
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  refine ⟨⟨ckOn_phiR D, fun ε hε m => ?_⟩, ⟨ckOn_phiD D, fun ε hε m => ?_⟩⟩
  · exact scal_bound_of_ubl D _ r (r + 1) Bg (by push_cast; linarith) ε (phiR_le D hε)
      (fun n => ubl_phiR D hε n) m
  · exact scal_bound_of_ubl D _ (r + 1) (r + 1) Bg (by push_cast; linarith) ε (phiD_le D ε)
      (fun n => ubl_phiD D hε n) m

end

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAPRho
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.PRho

noncomputable section

def nrmW (k r : ℕ) (z a : Fin (2 * r + k + 1) → ℂ) : ℝ :=
  (herm (Hpk k r) (SSn.prWv k r z a) (SSn.prWv k r z a)).re

section spec

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

def PRhoSpec (P : M.Par) (z : Fin (2 * P.r + P.k + 1) → ℂ) (π : B.Mat P.k P.r → (Wp →L[ℂ] Wp))
    (Pr : M.Ty P → (Fin (2 * P.r + P.k + 1) → ℂ) → (Wp →L[ℂ] Wp)) : Prop :=
  (∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Pr ρ) {a | 1 / 4 < nrmW P.k P.r z a}) ∧
  (∀ h ∈ UWset P.k P.r z, ∀ ρ a, Pr ρ (h *ᵥ a) = (π h).comp ((Pr ρ a).comp (π h⁻¹))) ∧
  ∀ a, 0 < nrmW P.k P.r z a →
    (∀ ρ (c : ℂ), c ≠ 0 → Pr ρ (c • a) = Pr ρ a) ∧
    (∀ ρ x y, inner ℂ (Pr ρ a x) y = inner ℂ x (Pr ρ a y)) ∧
    (∀ ρ ρ', (Pr ρ a).comp (Pr ρ' a) = if ρ = ρ' then Pr ρ a else 0) ∧
    ∀ ρ (x : Wp), Pr ρ a x = x ↔
      ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ, Q.IsFrameOf P.k P.r [z, SSn.prWv P.k P.r z a] Fr →
        ∀ w : ℂ, Q.capRep P.k P.r π Fr w x = M.xC P ρ (w - ((P.k : ℂ) - 2) / 2) • x

end spec

def PRhoExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k → ∃ Pr, PRhoSpec P Bs.z Bs.π Pr

section ctx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def Hyp (Cc : ℝ) (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) : Prop :=
  BuiltOW Cc S T f χ ν' m₀ top A₀ ∧ IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e

end ctx

def GaugeLines : Prop :=
  ∀ (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))),
    Hyp Cc S T f χ ν' m₀ top A₀ v e → 2 ≤ S.G.k →
    ∀ ζ : ℂ, (D.parOf S v).TT < Complex.normSq ζ → ∀ (ρ : M.Ty (D.parOf S v))
      (Fr : Fin (S.G.k - 1) → Fin (2 * S.G.r + S.G.k + 1) → ℂ),
      Q.IsFrameOf S.G.k S.G.r [(T v).base.z, SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec ζ] Fr →
      ∀ (w : ℂ) (x : Wq (S.pl v)),
        Q.capRep S.G.k S.G.r (T v).base.π Fr w (e ρ ζ x) =
          M.xC (D.parOf S v) ρ (w - ((S.G.k : ℂ) - 2) / 2) • e ρ ζ x

end

end Formalism.FourierDecayAlt.P.CutMP.JA.PRho
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.RadialDecompositionSpectralOfBranching
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem radialDecompositionSpectral_of_branching : Branching → RadialDecompositionSpectral := fun hB =>
  q_radial_decomposition_of_pieces second_contraction_adapted contractions_covariant capelli_two_by_two
    right_type_action hB qnTPres

end Formalism.FourierDecayAlt.P
end

