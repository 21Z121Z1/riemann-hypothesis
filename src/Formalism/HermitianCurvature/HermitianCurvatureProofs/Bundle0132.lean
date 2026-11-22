import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0057
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0090
import Formalism.HermitianCurvature.HermitianCurvatureProofs.OrbitalMeasurabilityWeakThreshold
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0047
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0127
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BetaSesquilinearity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0128
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelIntegrandAestronglyMeasurable
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InsertUnitMatrixZeroApply
import Formalism.HermitianCurvature.StatementTL
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0126
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0122
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0121

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDJDJComm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

open NumberField

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section gen

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem jdc_thrW (o : ℕ) (A d : ℝ) (hd : 0 ≤ d)
    (h : 12 * ((r : ℝ) + 1) * nDim k r ^ 2 + 6 * (r : ℝ) * (o : ℝ) + d ≤ A) :
    Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold k r A o := by
  unfold Formalism.FourierDecayAlt.P.WeakThresholdClauses.WeakDominationThreshold
  have hn : nDim k r = 2 * (r : ℝ) + k + 1 := by unfold nDim; push_cast; ring
  rw [hn] at h
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have key : (r : ℝ) * (4 * (r : ℝ) + 2 * (k : ℝ) - 1) * (6 * (r : ℝ) + 1) <
      12 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by
    nlinarith [pow_nonneg hr 3, mul_nonneg hr (mul_nonneg hk hk), mul_nonneg (mul_nonneg hr hr) hk,
      mul_nonneg hr hr, mul_nonneg hr hk, mul_nonneg hk hk]
  have hpos : 0 < 12 * ((r : ℝ) + 1) * (2 * (r : ℝ) + k + 1) ^ 2 := by positivity
  constructor <;> linarith

theorem jdc_om_sub_gpos (Db : B.RealPlaceData k r Wp Wq) : JF.Om k r Db.z Db.z' ⊆ B.GPos Db := by
  intro g hg
  unfold JF.Om Q.OmPlus at hg
  unfold B.GPos
  exact ⟨hg.1, hg.2.2⟩

theorem jdc_om_of (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ B.GV k r)
    (h : 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧ ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0) :
    g ∈ JF.Om k r z z' := by
  refine ⟨hg, ?_, h.1⟩
  intro l hl
  rcases Nat.eq_zero_or_pos l.val with h0 | h0
  · have e : l = ⟨0, by omega⟩ := Fin.ext h0
    rw [e]
    unfold Formalism.QuantumDeterminants.Dmin
    rw [Matrix.det_isEmpty]
    exact one_ne_zero
  · have e : l = ⟨((⟨l.val - 1, by omega⟩ : Fin r) : ℕ) + 1, by omega⟩ := Fin.ext (by simp; omega)
    rw [e]
    exact h.2 _

theorem jdc_of_om (z z' : Fin (2 * r + k + 1) → ℂ) {g : B.Mat k r} (hg : g ∈ JF.Om k r z z') :
    0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧ ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0 := by
  unfold JF.Om Q.OmPlus at hg
  obtain ⟨_, hD, hG⟩ := hg
  exact ⟨hG, fun a => hD _ (show (a : ℕ) + 1 ≤ r from a.isLt)⟩

end gen

section gen2

variable {k r : ℕ} {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℂ E₁] [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]

theorem jdc_ckOn_mono {m : ℕ∞} {UU VV : Set (B.Mat k r)} (h : UU ⊆ VV) {f : B.Mat k r → E₁} (hf : B.CkOn m VV f) :
    B.CkOn m UU f := by
  intro g₀ hg₀
  exact hf g₀ (h hg₀)

theorem jdc_ckOn_ap {UU : Set (B.Mat k r)} {a : B.Mat k r → (E₁ →L[ℂ] E₂)} {Φ : B.Mat k r → E₁}
    (ha : B.CkOn ⊤ UU a) (hΦ : B.CkOn ⊤ UU Φ) : B.CkOn ⊤ UU (fun g => a g (Φ g)) := by
  unfold B.CkOn at *
  intro g₀ hg₀
  obtain ⟨U₁, a', hU₁, hg₁, ha', hea⟩ := ha g₀ hg₀
  obtain ⟨U₂, Φ', hU₂, hg₂, hΦ', heΦ⟩ := hΦ g₀ hg₀
  refine ⟨U₁ ∩ U₂, fun g => a' g (Φ' g), hU₁.inter hU₂, ⟨hg₁, hg₂⟩, ?_, ?_⟩
  · have hr : ContDiffOn ℝ _ (fun g => (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ) (a' g)) (U₁ ∩ U₂) :=
      (ContinuousLinearMap.restrictScalarsL ℂ E₁ E₂ ℝ ℝ).contDiff.comp_contDiffOn (ha'.mono Set.inter_subset_left)
    exact hr.clm_apply (hΦ'.mono Set.inter_subset_right)
  · intro g hg hgG
    simp only [hea g hg.1 hgG, heΦ g hg.2 hgG]

theorem jdc_ckOn_Rw {UU : Set (B.Mat k r)} {w : List (B.Mat k r)} (hw : ∀ X ∈ w, B.inLie k r X)
    {f : B.Mat k r → E₁} (hf : B.CkOn ⊤ UU f) : B.CkOn ⊤ UU (B.Rw w f) := by
  rw [← Formalism.FourierDecayAlt.P.BetaSesquilinearity.Dw_wR]
  apply Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_Dw (fun x hx => Formalism.FourierDecayAlt.P.BetaSesquilinearity.lie_LR (u := []) (by simp) hw x
    (by simpa [Formalism.FourierDecayAlt.P.BetaSesquilinearity.wL] using hx))
  have e : ((⊤ : ℕ∞) + ((Formalism.FourierDecayAlt.P.BetaSesquilinearity.wR w).length : ℕ∞)) = ⊤ := top_add _
  rw [e]; exact hf

end gen2

section gen3

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem jdc_ckOn_opApply {UU : Set (B.Mat k r)} {J : B.Mat k r → (Wq →L[ℂ] Wp)} (hJ : B.CkOn ⊤ UU J) :
    ∀ Θ : B.DiffOp k r Wp Wq, (∀ T ∈ Θ, B.CkOn ⊤ UU T.coef) → B.CkOn ⊤ UU (B.opApply Θ J)
  | [], _ => by
    have e : B.opApply ([] : B.DiffOp k r Wp Wq) J = fun _ => 0 := by funext g; simp [B.opApply]
    rw [e]; exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_zero
  | T :: Θ, h => by
    have e : B.opApply (T :: Θ) J = fun g => T.coef g (B.Rw T.word J g) + B.opApply Θ J g := by
      funext g; simp [B.opApply]
    rw [e]
    exact Formalism.FourierDecayAlt.P.BetaSesquilinearity.CkOn_add (jdc_ckOn_ap (h T (by simp)) (jdc_ckOn_Rw T.word_lie hJ))
      (jdc_ckOn_opApply hJ Θ (fun T' hT' => h T' (by simp [hT'])))

theorem jdc_ckOn_om (z z' : Fin (2 * r + k + 1) → ℂ) {J : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : Q.SmoothLev k r 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} J) :
    B.CkOn ⊤ (JF.Om k r z z') J := by
  unfold B.CkOn
  unfold Q.SmoothLev at hJ
  intro g₀ hg₀
  unfold JF.Om Q.OmPlus at hg₀
  obtain ⟨hgG, hD, hG⟩ := hg₀
  have hmem : g₀ ∈ Q.Glev k r 0 ∩ {g | 0 < Formalism.QuantumDeterminants.Gf k r z z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r z z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} :=
    ⟨⟨hgG, fun a ha => absurd ha (Nat.not_lt_zero _)⟩, hG, fun a => hD _ (show (a : ℕ) + 1 ≤ r from a.isLt)⟩
  obtain ⟨U, F, hU, hgU, hF, hJF⟩ := hJ g₀ hmem
  refine ⟨U, F, hU, hgU, hF, ?_⟩
  intro g hg hgV
  exact hJF g hg ⟨hgV, fun a ha => absurd ha (Nat.not_lt_zero _)⟩

variable [FiniteDimensional ℂ Wp]

theorem jdc_ffl (Db : B.RealPlaceData k r Wp Wq) (Θ : B.DiffOp k r Wp Wq) (hSC : B.SmoothCoef (B.GPos Db) Θ)
    {J : B.Mat k r → (Wq →L[ℂ] Wp)}
    (hJ : J ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r Db.z Db.z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Db.z Db.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0})
    (H : B.Mat k r → (Wq →L[ℂ] Wp)) (hH : ∀ g ∈ JF.Om k r Db.z Db.z', B.opApply Θ J g = B.JF Db H g) :
    B.JF Db H ∈ Q.FFl k r Db.z Db.z' Db.π Db.π' 0 {g | 0 < Formalism.QuantumDeterminants.Gf k r Db.z Db.z' g ∧
      ∀ a : Fin r, Formalism.QuantumDeterminants.Dmin k r Db.z Db.z' g ⟨(a : ℕ) + 1, by omega⟩ ≠ 0} := by
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarN
  have := Formalism.FourierDecayAlt.P.B5.haar_sigmaFinite Db.haarW'
  have hN := bessel_unipotent_equiv_holds Wp Wq k r Db.z Db.z' cStd Db.π Db.π' Db.μW Db.μN Db.μW' H Db.z_mem Db.z'_mem
    Db.haarN.conc (fun n₀ h => Db.haarN.left n₀ h)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    have hg₀O : g₀ ∈ JF.Om k r Db.z Db.z' := jdc_om_of _ _ hg₀.1.1 hg₀.2
    have hck := jdc_ckOn_opApply (jdc_ckOn_om Db.z Db.z' hJ.1) Θ
      (fun T hT => jdc_ckOn_mono (jdc_om_sub_gpos Db) (hSC T hT).1)
    obtain ⟨U, f', hU, hgU, hc, he⟩ := hck g₀ hg₀O
    refine ⟨U ∩ Q.OmPlus k r Db.z Db.z', f', hU.inter (Formalism.FourierDecayAlt.P.PositiveOrbitOpen.omPlus_open _ _), ⟨hgU, hg₀O.2⟩,
      hc.mono Set.inter_subset_left, ?_⟩
    intro g hg hgG
    have hgO : g ∈ JF.Om k r Db.z Db.z' := ⟨hgG.1, hg.2⟩
    rw [← hH g hgO]
    exact he g hg.1 hgG.1
  · intro g _ n hn
    have e := hN g n hn.1 1 WeylGroupFacts.mem_n_one
    rw [Matrix.mul_one, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z'_mem, mul_one] at e
    exact e
  · intro g _ n hn
    have e := hN g 1 WeylGroupFacts.mem_n_one n hn.1
    rw [Matrix.one_mul, Formalism.FourierDecayAlt.P.BesselCapelliCommutation.psi_one Db.z_mem, one_mul] at e
    exact e
  · intro g _ h hh h' hh'
    exact Formalism.FourierDecayAlt.P5.jf_uEquiv Db H g hh hh'

end gen3

theorem transfer_commutation_holds : JDJComm := by
  refine ⟨12, ?_⟩
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v Θ d A hd hSC hC _hG hA F _hCk hCC hJF
  have hT := jdc_thrW (k := S.G.k) (r := S.G.r) (B.opOrder Θ) A d hd hA
  have hCOm : B.Commutes (T v).base (JF.Om S.G.k S.G.r (T v).base.z (T v).base.z') Θ :=
    fun p hp f' hf' g hg => hC p hp f' hf' g (jdc_om_sub_gpos _ hg)
  have hth := Formalism.FourierDecayAlt.P.orbital_commutes_on_open_set _ _ _ _ (T v).base A (B.opOrder Θ) F Θ _ subset_rfl le_rfl hT (hCC _) hCOm
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hTT : (D.parOf S v).TT = Tz S.G.k S.G.r (T v).base.z * Tz S.G.k S.G.r (T v).base.z' := by
    rw [hPl.2.2.2.1, hPl.2.2.2.2.1]; rfl
  refine ⟨jdc_ffl (T v).base Θ hSC hJF _ hth, ?_⟩
  intro x hx
  have hq : x ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := ⟨hx.1, by rw [← hTT]; exact hx.2⟩
  exact hth _ (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base hq)

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FormSplit
section
open MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5

section Split

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]
  {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S] [DecidableEq S]

theorem form_split (μ : Measure (Mt k r)) (l : Fin r) (x y : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ)
    (hint : Integrable (fun c' : Cf r l.castSucc =>
      ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c'))) :
    form μ l.castSucc x y c =
      ∫ t : ℂ, ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * form μ l.succ x y (Function.update c l t) := by
  set f : Cf r l.castSucc → ℂ := fun c' =>
    ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (x a) (y a) (glue l.castSucc c c') with hf
  have hmp := coordinate_split_measurePreserving (r := r) l
  have hform : form μ l.castSucc x y c = ∫ c', f c' := rfl
  have h1 : ∫ c', f c' = ∫ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) := by
    rw [← hmp.integral_comp' (fun p => f ((coordinateSplit (r := r) l).symm p))]
    simp only [MeasurableEquiv.symm_apply_apply]
  have hval : ∀ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) = ((‖p.1‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      (((∏ j, ‖p.2 j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (x a) (y a) (glue l.succ (Function.update c l p.1) p.2)) := by
    intro p
    have hw := weight_coordinate_split (r := r) l ((coordinateSplit (r := r) l).symm p)
    have hg := glue_coordinate_split (r := r) l c ((coordinateSplit (r := r) l).symm p)
    simp only [MeasurableEquiv.apply_symm_apply] at hw hg
    simp only [hf]
    rw [hw, hg, Complex.ofReal_mul, mul_assoc]
  have hF : Integrable (fun p : ℂ × Cf r l.succ => f ((coordinateSplit (r := r) l).symm p)) (volume.prod volume) := by
    have := (hmp.symm.integrable_comp_emb (coordinateSplit (r := r) l).symm.measurableEmbedding (g := f)).mpr hint
    exact this
  rw [hform, h1, show (volume : Measure (ℂ × Cf r l.succ)) = volume.prod volume from rfl,
    integral_prod _ hF]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  simp only [hval]
  rw [integral_const_mul]
  rfl

end Split

end Formalism.FourierDecayAlt.P5.HerA
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.FubiniRightIntegral
section
open Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBN

open Finset Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.PBF

section slots

variable {A : Type} [Ring A] [StarRing A] [Algebra ℂ A] {n r : ℕ}

theorem liftM_star (M : SlopeTestRemainingChoices (Fin n) A) : liftM (star M) = star (liftM M) := by
  ext z z'
  simp only [Matrix.star_apply, liftM_apply]
  by_cases h : z 0 = z' 0
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (Ne.symm h), star_zero]

theorem liftM_neg (M : SlopeTestRemainingChoices (Fin n) A) : liftM (-M) = -liftM M := by
  rw [← liftRingHom_apply_eq_liftM, map_neg, liftRingHom_apply_eq_liftM]

theorem liftM_sub (M N : SlopeTestRemainingChoices (Fin n) A) : liftM (M - N) = liftM M - liftM N := by
  rw [← liftRingHom_apply_eq_liftM, map_sub, liftRingHom_apply_eq_liftM, liftRingHom_apply_eq_liftM]

theorem liftM_pow (M : SlopeTestRemainingChoices (Fin n) A) (m : ℕ) : liftM (M ^ m) = liftM M ^ m := by
  rw [← liftRingHom_apply_eq_liftM, map_pow, liftRingHom_apply_eq_liftM]

theorem matrix_two_map_lift (a b c d : SlopeTestRemainingChoices (Fin n) A) :
    (!![a, b; c, d] : M2 (SlopeTestRemainingChoices (Fin n) A)).map liftM = !![liftM a, liftM b; liftM c, liftM d] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

structure Lifted (f : FrameData (Fin n) A) (f' : FrameData (Fin (n + 1)) A) : Prop where
  F : f'.F = liftM f.F
  ee : ∀ Y, f'.ee Y = liftM (f.ee Y)
  x : ∀ Y, f'.x Y = liftM (f.x Y)
  xi : ∀ Y, f'.xi Y = liftM (f.xi Y)
  c : f'.c = liftM f.c
  ci : f'.ci = liftM f.ci
  q : f'.q = f.q
  N : f'.N = f.N

variable (L : LevelData A r)

theorem io_lift (x : A) : (io x : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (io x) := io_succ x

theorem lifted_l {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y : ℂ) :
    f'.l L Y = liftM (f.l L Y) := by
  simp only [FrameData.l, kapL, liftM_add, liftM_mul, hf.ee Y, io_lift]

theorem lifted_m {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y : ℂ) :
    f'.m L Y = liftM (f.m L Y) := by
  simp only [FrameData.m, FrameData.d, FrameData.di, wt, wti, liftM_mul, liftM_pow, hf.N, hf.c, hf.ci,
    lifted_l L hf, liftM_star, io_lift]

theorem lifted_DD {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (Y Ya : ℂ) :
    f'.DD Y Ya = liftM (f.DD Y Ya) := by
  simp only [FrameData.DD, liftM_smul, liftM_sub, hf.ee]

theorem tz_lift : (tz L : SlopeTestRemainingChoices (Fin (n + 1)) A) = liftM (tz L) := io_succ _

theorem lifted_plus {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (a : Fin n)
    (Ya : ℂ) : Lifted (f.plus L a Ya) (f'.plus L a.succ Ya) := by
  refine ⟨?_, fun Y => ?_, fun Y => ?_, fun Y => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [FrameData.plus]
    rw [hf.F, liftM_mul, ← ins_succ, map_mul_liftM, matrix_two_map_lift, matrix_two_map_lift, lifted_l L hf]
    simp only [liftM_mul, liftM_zero, liftM_one, io_lift]
  · simp only [FrameData.plus]
    rw [← ins_succ, matrix_two_map_lift]
    simp only [liftM_add, liftM_sub, liftM_mul, liftM_neg, liftM_smul, liftM_zero, liftM_one, hf.ee, hf.x, hf.xi,
      lifted_DD hf, tz_lift]
  · simp only [FrameData.plus]
    rw [hf.x, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.plus]
    rw [hf.xi, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.plus]
    rw [hf.c, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.plus]
    rw [hf.ci, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.plus, hf.q]
  · simp only [FrameData.plus, hf.N]

theorem lifted_minus {f : FrameData (Fin n) A} {f' : FrameData (Fin (n + 1)) A} (hf : Lifted f f') (b : Fin n)
    (Yb : ℂ) : Lifted (f.minus L b Yb) (f'.minus L b.succ Yb) := by
  refine ⟨?_, fun Y => ?_, fun Y => ?_, fun Y => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [FrameData.minus]
    rw [hf.F, liftM_mul, ← ins_succ, map_mul_liftM, matrix_two_map_lift, matrix_two_map_lift, lifted_m L hf]
    simp only [liftM_mul, liftM_zero, liftM_one, io_lift]
  · simp only [FrameData.minus]
    rw [← ins_succ, matrix_two_map_lift]
    simp only [liftM_add, liftM_sub, liftM_mul, liftM_neg, liftM_smul, liftM_zero, liftM_one, hf.ee, hf.x, hf.xi,
      hf.q, lifted_DD hf, tz_lift]
  · simp only [FrameData.minus]
    rw [hf.x, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.minus]
    rw [hf.xi, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, liftM_one]
  · simp only [FrameData.minus]
    rw [hf.c, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.minus]
    rw [hf.ci, liftM_mul, ← ins_succ, matrix_two_map_lift]
    simp only [liftM_smul, liftM_zero, hf.q, hf.x, hf.xi]
  · simp only [FrameData.minus, hf.q]
  · simp only [FrameData.minus, hf.N]

theorem lifted_ofWord (st : Start A) :
    ∀ u : List (Letter ℂ (Fin n)), Lifted (ofWord L st u) (ofWord L st (u.map upL))
  | [] => ⟨by simp [ofWord, Start.frame, liftM_one], fun Y => io_succ _, fun Y => io_succ _, fun Y => io_succ _,
      by simp [ofWord, Start.frame, liftM_one], by simp [ofWord, Start.frame, liftM_one], rfl, rfl⟩
  | l :: u => by
    have ih := lifted_ofWord st u
    rw [List.map_cons]
    by_cases hp : l.plus
    · have e1 : ofWord L st (l :: u) = (ofWord L st u).plus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      have e2 : ofWord L st (upL l :: u.map upL) = (ofWord L st (u.map upL)).plus L l.intersection_update_fsHerm_neg_one.succ l.pt := by
        simp [ofWord, upL, hp]
      rw [e1, e2]
      exact lifted_plus L ih l.intersection_update_fsHerm_neg_one l.pt
    · have e1 : ofWord L st (l :: u) = (ofWord L st u).minus L l.intersection_update_fsHerm_neg_one l.pt := by simp [ofWord, hp]
      have e2 : ofWord L st (upL l :: u.map upL) = (ofWord L st (u.map upL)).minus L l.intersection_update_fsHerm_neg_one.succ l.pt := by
        simp [ofWord, upL, hp]
      rw [e1, e2]
      exact lifted_minus L ih l.intersection_update_fsHerm_neg_one l.pt

theorem bT_lift (σ : Site A) : ∀ u : List (Letter ℂ (Fin n)), bT σ (u.map upL) = liftM (bT σ u)
  | [] => by simp [bT, liftM_one]
  | l :: u => by
    rw [List.map_cons, bT, bT, bT_lift σ u, liftM_mul]
    congr 1
    show ins l.intersection_update_fsHerm_neg_one.succ (lift0 (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star)) =
      liftM (ins l.intersection_update_fsHerm_neg_one (lift0 (if l.plus then Ts σ l.pt else (Ts σ l.pt).map star)))
    rw [liftZero_succ_eq_map, ins_succ]

theorem bTA_lift (u : List (Letter ℂ (Fin n))) : TL.bTA L (u.map upL) = liftM (TL.bTA L u) := by
  simp only [TL.bTA, bT_lift]
  rw [← liftRingHom_apply_eq_liftM, map_list_prod, List.map_map]
  rfl

end slots

end Formalism.FourierDecayAlt.P.PBN
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadTypesAtOfWeight
section
noncomputable section

open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.Topx1
open scoped ComplexConjugate

namespace Formalism.FourierDecayAlt.P.PBI

variable {P : M.Par} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem exAt (p : KB.Pl P Wp Wq) {ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ}
    {m₀r : B.Mat P.k (P.r - P.r)} (hLev : LevFrame p ν'r m₀r)
    (Ψ : Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π
      (p.T.bs P.r).π')
    (x : (Fin (JC.parLev P P.r).r → ℂ) × Q.Mx (JC.parLev P P.r).k (JC.parLev P P.r).r)
    (hx : x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z')
    {γ₀ : B.Mat P.k (P.r - P.r)} (hγG : γ₀ ∈ B.GV P.k (P.r - P.r))
    (hζ : Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)
    (hγF : D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀) :
    ∑ ρ : M.Ty P, (p.TP.E ρ).comp ((Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀) =
      (Ψ : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ := by
  classical
  have hV := grpInt_at_dframe p hLev Ψ x hx hγG hζ hγF
  have hPl : Q.IsPlace (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' :=
    Formalism.FourierDecayAlt.P.JCTx5.isPlace_lev P p.T ⟨P.r, by omega⟩ p.hP
  have hn : P.r + (P.r - P.r) = P.r := by omega
  have hz : D.castV hn (liftVec P.k P.r (P.r - P.r) (p.T.bs P.r).z) = p.T.base.z := p.T.z_lev P.r le_rfl
  have hν : D.castV hn (liftVec P.k P.r (P.r - P.r) (m₀r *ᵥ ν'r)) = p.m₀ *ᵥ p.ν' := by
    rw [← Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.castV_mulVec_lift hn, hLev.1, hLev.2.1]
  have hπ : (p.T.bs P.r).π = fun y => p.T.base.π (D.castM hn (ιLev P.k P.r (P.r - P.r) y)) :=
    funext fun y => p.T.π_lev P.r le_rfl y
  have hcap : ∀ (Bs : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ) (w : ℂ) (v : Wp),
      Q.capRep P.k (P.r - P.r) (p.T.bs P.r).π Bs w v =
        Q.capRep P.k P.r p.T.base.π (fun c => D.castV hn (liftVec P.k P.r (P.r - P.r) (Bs c))) w v := by
    intro Bs w v
    rw [Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.capRep_lift_cast hn, hπ]
  have hfr : ∀ Bs : Fin (P.k - 1) → Fin (2 * (P.r - P.r) + P.k + 1) → ℂ,
      Q.IsFrameOf P.k (P.r - P.r) [(p.T.bs P.r).z, m₀r *ᵥ ν'r] Bs →
        Q.IsFrameOf P.k P.r [p.T.base.z, p.m₀ *ᵥ p.ν'] (fun c => D.castV hn (liftVec P.k P.r (P.r - P.r) (Bs c))) := by
    intro Bs hB
    have h := Formalism.FourierDecayAlt.P.DiagonalScalarMatrices.frame_lift_cast hn _ Bs hB
    simpa only [List.map_cons, List.map_nil, hz, hν] using h
  let TP' : Top.TypeProj (JC.parLev P P.r) (p.T.bs P.r).π (p.T.bs P.r).z (m₀r *ᵥ ν'r) :=
    { E := p.TP.E
      idem := p.TP.idem
      orth := p.TP.orth
      selfAdj := p.TP.selfAdj
      eigen := fun Bs hB ρ w v => (hcap Bs w _).trans (p.TP.eigen _ (hfr Bs hB) ρ w v)
      full := fun Bs hB ρ v h => p.TP.full _ (hfr Bs hB) ρ v fun w => (hcap Bs w v).symm.trans (h w) }
  exact types_of_grpInt (JC.parLev P P.r) (p.T.bs P.r) ν'r m₀r TP' hPl hLev.2.2 _ hV

def HeadWeightAt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (p : KB.Pl P Wp Wq) (F)
    (w : List C.Letter)
    (X : Q.ActualOps (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π')
    (μ : Measure (Mt P.k (P.r - P.r)))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π')) (JC.parLev P P.r).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z'
      (p.T.bs P.r).π (p.T.bs P.r).π'))) (Cb : ℝ) (ν'r : Fin (2 * (P.r - P.r) + P.k + 1) → ℂ)
    (m₀r : B.Mat P.k (P.r - P.r)),
    P5.IsData (JC.parLev P P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π' X μ L st p.l0 →
    KB.InDDplus2 P p.l0 p.T.base Cb p.Θ → KB.CptCoef p.T.base F → KB.CutWord P p.l0 w → LevFrame p ν'r m₀r →
    ∀ x ∈ Q.DomR (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z (p.T.bs P.r).z',
    ∀ γ₀ ∈ B.GV P.k (P.r - P.r),
      Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) γ₀ =
        Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2 →
      D.IsDFrame (p.T.bs P.r) ν'r m₀r γ₀ →
    (∀ h : C.LPt, D.IsLocPt h P.r →
        ∀ (y : Wd.Ix (Fin w.length) → Q.RadSp (JC.parLev P P.r).k (JC.parLev P P.r).r (p.T.bs P.r).z
          (p.T.bs P.r).z' (p.T.bs P.r).π (p.T.bs P.r).π') e,
        (P5.act ((Fr.ofWord L st (D.positionted w)).d L) y e :
            Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀ =
          ∑ ρ : M.Ty P, ((Top.dH P p.l0 (Tz P.k P.r p.T.base.z * Tz P.k P.r p.T.base.z') w
              (h ++ [(1, Q.zetaL P.k (P.r - P.r) (p.T.bs P.r).z (p.T.bs P.r).z' (Fin.last _) x.2)]) e ρ ^ 2 : ℝ) : ℂ) •
            (p.TP.E ρ).comp ((y e : Q.Fn (JC.parLev P P.r).k (JC.parLev P P.r).r (Wq →L[ℂ] Wp)) x.1 γ₀))

end Formalism.FourierDecayAlt.P.PBI

namespace Formalism.FourierDecayAlt.P

theorem head_types_at_of_weight : PBI.HeadWeightAt → PBI.HeadTypesAt := by
  intro hW Wp Wq _ _ _ _ _ _ P p F w X μ L st Cb ν'r m₀r hD hI hC hCut hLev x hx γ₀ hγG hζ hγF
  exact ⟨fun Ψ => PBI.exAt p hLev Ψ x hx hγG hζ hγF,
    hW Wp Wq P p F w X μ L st Cb ν'r m₀r hD hI hC hCut hLev x hx γ₀ hγG hζ hγF⟩

end Formalism.FourierDecayAlt.P
end
end

