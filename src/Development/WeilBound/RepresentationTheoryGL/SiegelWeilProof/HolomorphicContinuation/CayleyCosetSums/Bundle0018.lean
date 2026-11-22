import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0014
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0005
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AnalyticDeterminants.Bundle0003
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0002
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.Bundle0017

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AsmCore
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal ContDiff

namespace PositivityTheory.Rg.Sw.HSt

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.AbsSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ExpLie : Prop := ∀ (n : ℕ) (x Z : M2 n) (t : ℝ), InG x →
  InG (x * NormedSpace.exp ((t : ℂ) • ((1 / 2 : ℂ) • (Z + sig Z)))) ∧
  InG (x * NormedSpace.exp ((t : ℂ) • ((1 / (2 * Complex.I)) • (Z - sig Z))))

theorem lift_mR' (φ : GR n → ℂ) (y : GR n) : lift φ (mR y) = φ y := by
  have h : IsUnit (mR y) ∧ InG (mR y) := ⟨y.1.isUnit, y.2⟩
  unfold lift
  rw [dif_pos h]
  congr 1
  ext : 2
  rfl

theorem isUnit_of_inG {x : M2 n} (hx : InG x) : IsUnit x :=
  (Matrix.isUnit_iff_isUnit_det x).2 (PositivityTheory.Rg.Sw.Glob.DenseP.isUnit_det_of_inG hx)

def toGR (x : M2 n) (hx : InG x) : GR n := ⟨(isUnit_of_inG hx).unit, hx⟩

theorem mR_toGR (x : M2 n) (hx : InG x) : mR (toGR x hx) = x := rfl

theorem rC_const_mul (Z : M2 n) (a : ℂ) (F : M2 n → ℂ) (x : M2 n) :
    rC Z (fun x => a * F x) x = a * rC Z F x := by
  unfold rC
  rw [deriv_const_mul_field', deriv_const_mul_field']
  ring

theorem rC_zero (Z : M2 n) (x : M2 n) : rC Z (fun _ => (0 : ℂ)) x = 0 := by
  unfold rC
  simp

def Van (j : ℕ) (h : ℂ → ℂ) (s : ℂ) : Prop := ∀ k ≤ j, iteratedDeriv k h s = 0

theorem van_mul {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {q h : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hh : DifferentiableOn ℂ h U) {j : ℕ} (hv : Van j h s) : Van j (fun z => q z * h z) s := by
  intro k hk
  rw [leib hU k q h hq hh s hs]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [hv (k - i) (by omega)]
  simp

theorem van_sum {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {ι : Type} (S : Finset ι) (h : ι → ℂ → ℂ)
    (hd : ∀ l, DifferentiableOn ℂ (h l) U) {j : ℕ} (hv : ∀ l, Van j (h l) s) : Van j (fun z => ∑ l ∈ S, h l z) s := by
  classical
  induction S using Finset.induction_on with
  | empty => intro k _; simp
  | insert a S ha ih =>
    intro k hk
    have e : (fun z => ∑ l ∈ insert a S, h l z) = (fun z => h a z) + (fun z => ∑ l ∈ S, h l z) := by
      funext z; simp [Finset.sum_insert ha]
    have hds : DifferentiableOn ℂ (fun z => ∑ l ∈ S, h l z) U := by
      exact DifferentiableOn.fun_sum (fun l _ => hd l)
    rw [e, iteratedDeriv_add (((hd a).contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top)
      ((hds.contDiffOn hU).contDiffAt (hU.mem_nhds hs) |>.of_le le_top), hv a k hk, ih k hk, add_zero]

theorem iter_mul_low {U : Set ℂ} (hU : IsOpen U) {s : ℂ} (hs : s ∈ U) {q h : ℂ → ℂ} (hq : DifferentiableOn ℂ q U)
    (hh : DifferentiableOn ℂ h U) {j : ℕ} (hv : ∀ i < j, iteratedDeriv i h s = 0) :
    iteratedDeriv j (fun z => q z * h z) s = q s * iteratedDeriv j h s ∧
      ∀ i < j, iteratedDeriv i (fun z => q z * h z) s = 0 := by
  refine ⟨?_, fun i hi => ?_⟩
  · rw [leib hU j q h hq hh s hs, Finset.sum_eq_single 0]
    · simp
    · intro b hbm hb
      have := Finset.mem_range.1 hbm
      rw [hv (j - b) (by omega)]
      simp
    · intro h0; exact absurd (Finset.mem_range.2 (Nat.succ_pos j)) h0
  · rw [leib hU i q h hq hh s hs]
    refine Finset.sum_eq_zero fun b hb => ?_
    have : b < i + 1 := Finset.mem_range.1 hb
    rw [hv (i - b) (by omega)]
    simp

theorem asmH_of (hF : FarId) (hS : SmoothX) (hT : TopHol) (hR : RcCongr) (hE : ExpLie) : AsmH := by
  intro hLT hSec hCR
  intro m n e hm hmn G _ _ _ _ _ _ Pp Γ ι s₀ Ht f hι hsplit U d Ê t hU hRU hs0 hhol hcont hfar j hlow hsing g
  have hD : HD m n e G Pp Γ ι s₀ Ht f U d Ê t := ⟨hι, hsplit, hU, hRU, hs0, hhol, hcont, hfar⟩
  haveI : CompactSpace (KR n) := kRCpt n
  letI : MeasurableSpace (KR n) := borel _
  haveI : BorelSpace (KR n) := ⟨rfl⟩
  let μ : Measure (KR n) := Measure.haarMeasure ⊤
  haveI : μ.IsHaarMeasure := Measure.isHaarMeasure_haarMeasure _
  haveI : IsProbabilityMeasure μ := ⟨by simpa [μ] using Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts (KR n)))⟩

  obtain ⟨Φs, Ω, c, hΩo, hΩG, hcd, hc0, hΦG, -, hΦj, hΦd, hΦrC⟩ := hS m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD g
  set φ : GR n → ℂ := fun y => iteratedDeriv j (Ê · (g * ι y)) s₀ with hφ
  set Ψ : ℕ → M2 n → ℂ := fun r x => iteratedDeriv r (Φs · x) s₀ with hΨ

  have hΨG : ∀ (y : GR n), Ψ j (mR y) = c s₀ * φ y ∧ ∀ i < j, Ψ i (mR y) = 0 := by
    intro y
    have hev : (Φs · (mR y)) =ᶠ[𝓝 s₀] fun z => c z * Ê z (g * ι y) := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hΦG z hz y
    have hlow' : ∀ i < j, iteratedDeriv i (Ê · (g * ι y)) s₀ = 0 := fun i hi => hlow i hi (g * ι y)
    obtain ⟨h1, h2⟩ := iter_mul_low hU hs0 hcd (hhol (g * ι y)) hlow'
    refine ⟨?_, fun i hi => ?_⟩
    · simp only [hΨ]
      rw [iteratedDeriv_eq_of_eventuallyEq hev j, h1]
    · simp only [hΨ]
      rw [iteratedDeriv_eq_of_eventuallyEq hev i, h2 i hi]
  have hΨ0 : ∀ i < j, ∀ x', InG x' → Ψ i x' = 0 := by
    intro i hi x' hx'
    have := (hΨG (toGR x' hx')).2 i hi
    rwa [mR_toGR] at this

  have hιKc : Continuous (ιK n) := by
    unfold ιK
    exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hιKiff : ∀ x, InK x ↔ ∃ k, ιK n k = x := by
    intro x
    constructor
    · intro hx
      exact ⟨⟨toGR x hx.1, hx⟩, rfl⟩
    · rintro ⟨k, rfl⟩
      exact k.2

  obtain ⟨N₀, ρ₀, ψ₀, a₀, b₀, D₀, M₀, hρ₀, hψ₀, hab₀, hDd₀, -, hMd₀, hid₀⟩ := hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff 0
  obtain ⟨-, hK⟩ := hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ 0 N₀ ρ₀ ψ₀ a₀ b₀ D₀ M₀ hρ₀ hψ₀ hab₀ hDd₀ hMd₀ hid₀
  refine hCR n m e φ (fun x => (c s₀)⁻¹ * Ψ j x) Ω hΩo hΩG (contDiffOn_const.mul (hΦj j)) ?_ ?_ ?_
  · intro y
    simp only [(hΨG y).1]
    field_simp
  · intro y k hk
    have hev : (Ê · (g * ι (y * k))) =ᶠ[𝓝 s₀] fun z => Ê z (g * ι y) * F0 m 0 e k := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hK z hz g y k hk
    simp only [hφ]
    rw [iteratedDeriv_eq_of_eventuallyEq hev j, iteratedDeriv_mul_const_field]
  · intro y Q
    rw [rC_const_mul]
    suffices h : rC (lowQ Q) (Ψ j) (mR y) = 0 by rw [h, mul_zero]
    obtain ⟨N, ρ, ψ, a, b, D, M, hρ, hψ, hab, hDd, hD0, hMd, hid⟩ := hLT n m e hmn (KR n) μ (ιK n) hιKc hιKiff Q
    obtain ⟨⟨t', hfarId⟩, -⟩ := hF m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD hSec μ Q N ρ ψ a b D M hρ hψ hab hDd hMd hid
    set L : ℂ → ℂ := fun z => rC (lowQ Q) (Φs z) (mR y) with hL
    set T : Fin N → ℂ → ℂ := fun l z => tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (Ê z) g) (mR y) with hTdef
    set R : ℂ → ℂ := fun z => c z * ∑ l, M l (z - s₀) * T l z with hRdef
    have hTH : ∀ l, DifferentiableOn ℂ (T l) U ∧ ∀ r : ℕ, iteratedDeriv r (T l) s₀ =
        tOp μ (ιK n) (ρ l) (ψ l) (a l) (b l) (resG ι (fun x => iteratedDeriv r (Ê · x) s₀) g) (mR y) := fun l =>
      hT m n e hm hmn G Pp Γ ι s₀ Ht f U d Ê t hD μ (ρ l) (ψ l) (a l) (b l) (hρ l) (hψ l).1 (hψ l).2.1 (hab l).1 (hab l).2 g y
    have hDs : Differentiable ℂ fun z => D (z - s₀) := hDd.comp (differentiable_id.sub_const s₀)
    have hMs : ∀ l, Differentiable ℂ fun z => M l (z - s₀) := fun l => (hMd l).comp (differentiable_id.sub_const s₀)
    have hLd : DifferentiableOn ℂ L U := (hΦrC Q y).1
    have hsumd : DifferentiableOn ℂ (fun z => ∑ l, M l (z - s₀) * T l z) U :=
      DifferentiableOn.fun_sum fun l _ => (hMs l).differentiableOn.mul (hTH l).1
    have hRd : DifferentiableOn ℂ R U := hcd.mul hsumd

    have hEq : EqOn (fun z => D (z - s₀) * L z) R U := by
      obtain ⟨σ, hσ⟩ := hRU.1
      set z₁ : ℂ := ((max t' σ + 1 : ℝ) : ℂ) with hz₁
      have hz₁U : z₁ ∈ U := hσ (GlobalTheory.Cont.mem_rightOf.2 (by rw [hz₁, Complex.ofReal_re]; linarith [le_max_right t' σ]))
      refine (hDs.differentiableOn.mul hLd).analyticOnNhd hU |>.eqOn_of_preconnected_of_eventuallyEq
        (hRd.analyticOnNhd hU) (rightConn U hU hRU) hz₁U ?_
      have hopen : IsOpen {z : ℂ | max t' σ < z.re} := isOpen_lt continuous_const Complex.continuous_re
      filter_upwards [hopen.mem_nhds (show max t' σ < z₁.re by rw [hz₁, Complex.ofReal_re]; linarith)] with z hz
      have hzt : t' < z.re := lt_of_le_of_lt (le_max_left _ _) hz
      have hzU : z ∈ U := hσ (GlobalTheory.Cont.mem_rightOf.2 (lt_of_le_of_lt (le_max_right _ _) hz))
      have hcong : L z = rC (lowQ Q) (fun x => c z * resG ι (Ê z) g x) (mR y) := by
        refine hR n (Φs z) _ (lowQ Q) (mR y) y.2 (fun x' hx' => ?_) (fun s => (hE n (mR y) (lowQ Q) s y.2).1)
          (fun s => (hE n (mR y) (lowQ Q) s y.2).2)
        have e1 := hΦG z hzU (toGR x' hx')
        rw [mR_toGR] at e1
        have e2 := lift_mR' (fun y => Ê z (g * ι y)) (toGR x' hx')
        rw [mR_toGR] at e2
        simp only [resG]
        rw [e1, e2]
      show D (z - s₀) * L z = c z * ∑ l, M l (z - s₀) * T l z
      rw [hcong, rC_const_mul, mul_left_comm, hfarId z hzt g y]
    have hev : (fun z => D (z - s₀) * L z) =ᶠ[𝓝 s₀] R := by
      filter_upwards [hU.mem_nhds hs0] with z hz
      exact hEq hz
    have hLlow : ∀ i < j, iteratedDeriv i L s₀ = 0 := by
      intro i hi
      rw [(hΦrC Q y).2 i, hR n _ (fun _ => 0) (lowQ Q) (mR y) y.2 (fun x' hx' => hΨ0 i hi x' hx')
        (fun s => (hE n (mR y) (lowQ Q) s y.2).1) (fun s => (hE n (mR y) (lowQ Q) s y.2).2), rC_zero]
    obtain ⟨hL1, -⟩ := iter_mul_low hU hs0 hDs.differentiableOn hLd hLlow
    have hnb : ∀ t, InG (nU (herm t) : M2 n) := fun t => PositivityTheory.Rg.Sw.LVs.HolB.inG_upper (PositivityTheory.Rg.Sw.AbsSt.LocOpA.herm_isHermitian t).eq
    have hRv : Van j R s₀ := by
      apply van_mul hU hs0 hcd hsumd
      apply van_sum hU hs0 Finset.univ (fun l z => M l (z - s₀) * T l z)
        (fun l => (hMs l).differentiableOn.mul (hTH l).1)
      intro l
      apply van_mul hU hs0 (hMs l).differentiableOn (hTH l).1
      intro k hk
      rw [(hTH l).2 k]
      rcases lt_or_eq_of_le hk with hk' | hkj
      · have hz0 : resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g = fun _ => 0 := by
          funext x
          unfold resG lift
          split_ifs <;> simp [hlow k hk']
        rw [hz0]
        simp [tOp]
      · subst hkj
        have hin : ∀ k' : KR n, (∫ t : Fin n → Fin n → ℝ, resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g
            (mR y * ιK n k' * a l * nU (herm t) * b l) * ψ l t) = 0 := by
          intro k'
          let nb : (Fin n → Fin n → ℝ) → GR n := fun t => toGR (nU (herm t)) (hnb t)
          have key := hsing (ψ l) (hψ l) nb (fun t => rfl) g (y * (k' : GR n) * toGR (a l) (hab l).1)
            (toGR (b l) (hab l).2)
          refine (integral_congr_ae (Eventually.of_forall fun t => ?_)).trans key
          show resG ι (fun x => iteratedDeriv k (Ê · x) s₀) g
              (mR (y * (k' : GR n) * toGR (a l) (hab l).1 * nb t * toGR (b l) (hab l).2)) * ψ l t = _
          simp only [resG]
          rw [lift_mR']
        unfold tOp
        simp_rw [hin, mul_zero, integral_zero]
    have hRj := hRv j le_rfl
    have h0 : D 0 * iteratedDeriv j L s₀ = 0 := by
      have h1 := iteratedDeriv_eq_of_eventuallyEq hev j
      rw [hL1, hRj, sub_self] at h1
      exact h1
    have hLj : iteratedDeriv j L s₀ = 0 := (mul_eq_zero.1 h0).resolve_left hD0
    rw [(hΦrC Q y).2 j] at hLj
    exact hLj

end PositivityTheory.Rg.Sw.HSt
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CurveHasDerivAt
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped ContDiff

namespace PositivityTheory.Rg.Sw.HSt.FL

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt
open PositivityTheory.Rg.Sw.LVs.II (cE cE_hasDerivAt0 cE_add cE_zero cE_continuous mulL mulL_apply)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

private theorem cd_det_lemma {ι : Type} [Fintype ι] [DecidableEq ι] :
    ContDiff ℂ ∞ (fun x : Matrix ι ι ℂ => x.det) := by
  have he : ∀ i j : ι, ContDiff ℂ ∞ (fun x : Matrix ι ι ℂ => x i j) := fun i j =>
    contDiff_apply_apply ℂ ℂ i j
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum (fun σ _ => contDiff_const.mul (contDiff_prod (fun i _ => he _ _)))

theorem cd_det : ContDiff ℂ ∞ (fun x : M2 n => x.det) := by
  exact cd_det_lemma

theorem cd_detu1 : ContDiff ℂ ∞ (fun x : M2 n => (u1 x).det) := by
  exact cd_det_lemma.comp contDiff_first_cayley_block

theorem curve_hasDerivAt (X x : M2 n) : HasDerivAt (fun s : ℝ => x * cE X s) (x * X) 0 := by
  have h := (mulL x).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (cE_hasDerivAt0 X)
  simp only [Function.comp_def, mulL_apply] at h
  exact h

theorem curve_deriv (Ψ : M2 n → ℂ) (hΨ : ContDiff ℂ ∞ Ψ) (X x : M2 n) :
    HasDerivAt (fun s : ℝ => Ψ (x * cE X s)) (fderiv ℂ Ψ x (x * X)) 0 := by
  have hd : HasFDerivAt Ψ (fderiv ℂ Ψ x) (x * cE X 0) := by
    rw [cE_zero, Matrix.mul_one]
    exact (hΨ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h := (hd.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) (curve_hasDerivAt X x)
  simp only [Function.comp_def, ContinuousLinearMap.coe_restrictScalars'] at h
  exact h

theorem continuous_mR' : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem det_mR_ne' (g : GR n) : (mR g).det ≠ 0 := by
  show ((g : GL (Fin n ⊕ Fin n) ℂ) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ).det ≠ 0
  exact ((Matrix.isUnit_iff_isUnit_det _).mp (g : GL (Fin n ⊕ Fin n) ℂ).isUnit).ne_zero

def rD (X x : M2 n) : ℂ := fderiv ℂ (fun x : M2 n => x.det) x (x * X) / x.det

def rA (X x : M2 n) : ℂ := fderiv ℂ (fun x : M2 n => (u1 x).det) x (x * X) / (u1 x).det

private theorem rD_mul_left_eq_of_det_ne_zero (P A X : M2 n) (hP : P.det ≠ 0) : rD X (P * A) = rD X A := by
  unfold rD
  let L : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ P)
  have hL : ∀ y, L y = P * y := fun y => rfl
  have hdet : ∀ B : M2 n, HasFDerivAt (fun x : M2 n => x.det) (fderiv ℂ (fun x : M2 n => x.det) B) B :=
    fun B => ((cd_det (n := n)).differentiable (by simp) B).hasFDerivAt
  have h1 : HasFDerivAt (fun y : M2 n => (P * y).det)
      ((fderiv ℂ (fun x : M2 n => x.det) (P * A)).comp L) A := by
    have := (hdet (P * A)).comp A (L.hasFDerivAt (x := A))
    simp only [Function.comp_def, hL] at this
    exact this
  have h2 : HasFDerivAt (fun y : M2 n => (P * y).det)
      (P.det • fderiv ℂ (fun x : M2 n => x.det) A) A := by
    simp_rw [Matrix.det_mul]
    exact (hdet A).const_mul P.det
  have h4 := congrArg (fun T => T (A * X)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hL] at h4
  rw [Matrix.mul_assoc, h4, Matrix.det_mul, mul_div_mul_left _ _ hP]

theorem rD_up (X : M2 n) (p k : GR n) : rD X (mR p * mR k) = rD X (mR k) := by
  exact rD_mul_left_eq_of_det_ne_zero _ _ X (det_mR_ne' p)

private theorem rA_mul_left_eq_of_u1_mul (D : Matrix (Fin n) (Fin n) ℂ) (P A X : M2 n) (hD : D.det ≠ 0)
    (hu : ∀ y, u1 (P * y) = D * u1 y) : rA X (P * A) = rA X A := by
  unfold rA
  let L : M2 n →L[ℂ] M2 n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℂ P)
  have hL : ∀ y, L y = P * y := fun y => rfl
  have hdet : ∀ B : M2 n, HasFDerivAt (fun x : M2 n => (u1 x).det) (fderiv ℂ (fun x : M2 n => (u1 x).det) B) B :=
    fun B => ((cd_detu1 (n := n)).differentiable (by simp) B).hasFDerivAt
  have h1 : HasFDerivAt (fun y : M2 n => (u1 (P * y)).det)
      ((fderiv ℂ (fun x : M2 n => (u1 x).det) (P * A)).comp L) A := by
    have := (hdet (P * A)).comp A (L.hasFDerivAt (x := A))
    simp only [Function.comp_def, hL] at this
    exact this
  have h2 : HasFDerivAt (fun y : M2 n => (u1 (P * y)).det)
      (D.det • fderiv ℂ (fun x : M2 n => (u1 x).det) A) A := by
    simp_rw [hu, Matrix.det_mul]
    exact (hdet A).const_mul D.det
  have h4 := congrArg (fun T => T (A * X)) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hL] at h4
  rw [Matrix.mul_assoc, h4, hu, Matrix.det_mul, mul_div_mul_left _ _ hD]

theorem rA_up (X : M2 n) (p k : GR n) (hp : IsUp p) : rA X (mR p * mR k) = rA X (mR k) := by
  have hD : (toBlocks₂₂ (mR p)).det ≠ 0 := by
    rw [← first_block_of_upper p hp]
    exact det_first_cayley_block_ne_zero p.2
  exact rA_mul_left_eq_of_u1_mul _ _ _ X hD (fun y => first_block_upper_mul p y hp)

theorem continuous_rD (X : M2 n) : Continuous fun k : GR n => rD X (mR k) := by
  unfold rD
  refine Continuous.div ?_ (cd_det.continuous.comp continuous_mR') (fun k => det_mR_ne' k)
  exact ((cd_det.continuous_fderiv (by simp)).comp continuous_mR').clm_apply
    (continuous_mR'.mul continuous_const)

theorem continuous_rA (X : M2 n) : Continuous fun k : GR n => rA X (mR k) := by
  unfold rA
  refine Continuous.div ?_ (cd_detu1.continuous.comp continuous_mR')
    (fun k => (det_u_ne (x := mR k) k.2).1)
  exact ((cd_detu1.continuous_fderiv (by simp)).comp continuous_mR').clm_apply
    (continuous_mR'.mul continuous_const)

end PositivityTheory.Rg.Sw.HSt.FL
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DetNeZeroOfInG
section
noncomputable section

open Matrix Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.HSt.CR

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.HSt

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem inG_mul {x y : M2 n} (hx : InG x) (hy : InG y) : InG (x * y) := by
  unfold InG at *
  rw [Matrix.conjTranspose_mul]
  calc yᴴ * xᴴ * JJ n * (x * y) = yᴴ * (xᴴ * JJ n * x) * y := by simp only [Matrix.mul_assoc]
    _ = JJ n := by rw [hx, hy]

theorem det_ne_zero_of_inG {x : M2 n} (hx : InG x) : x.det ≠ 0 := by
  intro h
  have h1 := congrArg Matrix.det hx
  rw [Matrix.det_mul, Matrix.det_mul, h, mul_zero] at h1
  have h2 : (JJ n).det ≠ 0 := by
    have := congrArg Matrix.det (JJ_mul_JJ (n := n))
    rw [Matrix.det_mul, Matrix.det_neg] at this
    intro h3
    rw [h3, zero_mul] at this
    simp at this
  exact h2 h1.symm

def toGR (x : M2 n) (hx : InG x) : GR n := ⟨(Matrix.isUnit_iff_isUnit_det _ |>.2 (isUnit_iff_ne_zero.2
  (det_ne_zero_of_inG hx))).unit, hx⟩

theorem mR_toGR (x : M2 n) (hx : InG x) : mR (toGR x hx) = x := rfl

end PositivityTheory.Rg.Sw.HSt.CR
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.DirSeries
section
noncomputable section

open MeasureTheory Matrix Set Filter Topology
open scoped NNReal

namespace PositivityTheory.Rg.Sw.HSt.FarP

open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LVs PositivityTheory.Rg.Sw.AbsSt PositivityTheory.Rg.Sw.HSt

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {m n : ℕ} {e : ℤ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {Pp Γ : Subgroup G} {ι : GR n →* G} {s₀ : ℂ} {Ht : G → ℝ≥0} {f : G → ℂ} {U : Set ℂ} {d : Polynomial ℂ}
  {Ê : ℂ → G → ℂ} {t : ℝ}

theorem dirSeries (hC : CurveGR) (hF : FzDer) (h : HD m n e G Pp Γ ι s₀ Ht f U d Ê t) {z : ℂ} (hz : t < z.re)
    (Z : M2 n) (b : Bool) (g : G) (y : GR n) (y₀ : GlobalTheory.Eis.Cosets Pp Γ → GR n) (C : GlobalTheory.Eis.Cosets Pp Γ → ℂ)
    (hyC : ∀ q y', trm Ht f s₀ z (((q.out : Γ) : G) * g * ι y') = C q * fz m e (z - s₀) (mR (y₀ q * y'))) :
    Summable (fun q => C q * deriv (fun s : ℝ => fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0) ∧
    deriv (fun s : ℝ => resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 =
      d.eval z * ∑' q, C q * deriv (fun s : ℝ => fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 := by
  obtain ⟨γ, hγc, hγ0, hγadd, hγe⟩ := hC n Z b
  obtain ⟨Cd, hCd0, hR⟩ := hF n m e (z - s₀) Z b
  choose Rf hRf using hR
  have hfzγ : ∀ (y₁ : GR n) (s : ℝ), fz m e (z - s₀)
      (mR y₁ * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) =
      fz m e (z - s₀) (mR (y₁ * γ s)) := by
    intro y₁ s
    rw [mR_mul, hγe]
  have hderiv : ∀ (y₁ : GR n) (s : ℝ), HasDerivAt (fun u : ℝ => fz m e (z - s₀)
      (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) (Rf (y₁ * γ s)) s := by
    intro y₁ s
    have h1 := HasDerivAt.comp_sub_const s s (by rw [sub_self]; exact (hRf (y₁ * γ s)).1)
    have hfe : (fun u : ℝ => fz m e (z - s₀)
        (mR y₁ * NormedSpace.exp ((u : ℂ) • (if b then dir1 Z else dir2 Z)))) =
        fun x : ℝ => fz m e (z - s₀)
          (mR (y₁ * γ s) * NormedSpace.exp (((x - s : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z))) := by
      funext u
      rw [hfzγ, ← hγe, ← mR_mul, mul_assoc, ← hγadd, add_sub_cancel]
    rw [hfe]
    exact h1
  have hK : IsCompact ((fun s : ℝ => g * ι (y * γ s)) '' Icc (-1) 1) :=
    isCompact_Icc.image (continuous_const.mul (h.ιc.comp (continuous_const.mul hγc)))
  obtain ⟨u, hu, hbound⟩ := (h.far z hz).1 _ hK
  have hterm : ∀ q (s : ℝ), s ∈ Icc (-1 : ℝ) 1 →
      ‖C q * fz m e (z - s₀) (mR (y₀ q * y * γ s))‖ ≤ u q := by
    intro q s hs
    have hb := hbound (g * ι (y * γ s)) ⟨s, hs, rfl⟩ q
    rw [mul_assoc (y₀ q), ← hyC q (y * γ s)]
    simpa only [GlobalTheory.Eis.term, trm, mul_assoc] using hb
  have hbd : ∀ q, ∀ s ∈ Ioo (-1 : ℝ) 1, ‖C q * Rf (y₀ q * y * γ s)‖ ≤ Cd * u q := by
    intro q s hs
    have h1 := (hRf (y₀ q * y * γ s)).2
    have h2 := hterm q s (Ioo_subset_Icc_self hs)
    rw [norm_mul] at h2 ⊢
    calc ‖C q‖ * ‖Rf (y₀ q * y * γ s)‖
        ≤ ‖C q‖ * (Cd * ‖fz m e (z - s₀) (mR (y₀ q * y * γ s))‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = Cd * (‖C q‖ * ‖fz m e (z - s₀) (mR (y₀ q * y * γ s))‖) := by ring
      _ ≤ Cd * u q := mul_le_mul_of_nonneg_left h2 hCd0
  have h0mem : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have hg0 : Summable (fun q => C q * fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp (((0 : ℝ) : ℂ) • (if b then dir1 Z else dir2 Z)))) :=
    hu.of_norm_bounded fun q => by
      simpa only [hfzγ] using hterm q 0 ⟨by norm_num, by norm_num⟩
  have hsum := hasDerivAt_tsum_of_isPreconnected (hu.mul_left Cd) isOpen_Ioo isPreconnected_Ioo
    (g := fun q (s : ℝ) => C q * fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))))
    (g' := fun q s => C q * Rf (y₀ q * y * γ s))
    (fun q s _ => (hderiv (y₀ q * y) s).const_mul (C q)) hbd h0mem hg0 h0mem
  rw [hγ0] at hsum
  simp only [mul_one] at hsum
  have hRfd : ∀ q, deriv (fun s : ℝ => fz m e (z - s₀)
      (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) 0 = Rf (y₀ q * y) :=
    fun q => (hRf (y₀ q * y)).1.deriv
  have hfun : (fun s : ℝ => resG ι (Ê z) g
      (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z)))) =
      fun s : ℝ => d.eval z * ∑' q, C q * fz m e (z - s₀)
        (mR (y₀ q * y) * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) := by
    funext s
    have hl : resG ι (Ê z) g (mR y * NormedSpace.exp ((s : ℂ) • (if b then dir1 Z else dir2 Z))) =
        Ê z (g * ι (y * γ s)) := by
      rw [← hγe, ← mR_mul, resG_mR]
    rw [hl, (h.far z hz).2]
    simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
    congr 1
    refine tsum_congr fun q => ?_
    rw [hfzγ, mul_assoc (y₀ q), ← hyC q (y * γ s), trm, mul_assoc]
  simp only [hRfd]
  refine ⟨(hu.mul_left Cd).of_norm_bounded fun q => ?_, ?_⟩
  · simpa only [hγ0, mul_one] using hbd q 0 h0mem
  · rw [hfun, (hsum.const_mul (d.eval z)).deriv]

end PositivityTheory.Rg.Sw.HSt.FarP
end
end

