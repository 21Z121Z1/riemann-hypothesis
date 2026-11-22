import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0146
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0081
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSFSS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0125
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0075
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0147
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0120
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0101
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsMeasurableSection
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AutomorphicInSphericalLevel
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0136

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolConnUniq
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem connection_uniqueness_holds : GTCConnUniq := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e he A B A' B' hAB hAB' hC hC' ρ ζ hζ
  obtain ⟨Φ, hΦ, -⟩ := SSTr.exists_tr P Bs hyp.1 hyp.2.1 e he (fun _ => (1 : MA.SmQ P.r P.TT))
  have h1 := (hC Φ ρ).1
  have h2 := (hC' Φ ρ).1
  rw [hΦ] at h1 h2
  simp only [mul_one] at h1 h2
  have h3 : fnZ P (A ρ) = fnZ P (A' ρ) := by
    have := h1.symm.trans h2
    exact add_left_cancel this
  rw [fnZ_eq_mk P (hAB ρ).1, fnZ_eq_mk P (hAB' ρ).1] at h3
  have hq : ((fun _ => (1 : ℂ), ζ) : (Fin P.r → ℂ) × ℂ) ∈ MA.Qset P.r P.TT :=
    ⟨fun _ => one_ne_zero, hζ⟩
  have := congrFun (congrArg Subtype.val h3) ⟨_, hq⟩
  exact this

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolPhaseRel
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def qOne (P : M.Par) (ζ : ℂ) (hζ : ζ ∈ Ann P) : MA.Qp P.r P.TT :=
  ⟨(fun _ => (1 : ℂ), ζ), ⟨fun _ => one_ne_zero, hζ⟩⟩

theorem kap_orth (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hyp : GTHyp P Bs X d)
    (e e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (he0 : IsFrameB P Bs e0) (hk0 : KapF P Bs d e0) (ρ σ : M.Ty P) (hσ : σ ≠ ρ) (ζ : ℂ) (hζ : ζ ∈ Ann P) :
    inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (e0 ρ ζ)) = 0 := by
  have hpl := hyp.1
  have hk2 := hyp.2.1
  let F : M.Ty P → MA.SmQ P.r P.TT := fun τ => if τ = ρ then fnZ P (fun _ => (1 : ℂ)) else 0
  obtain ⟨Φ, hΦ, hΦv⟩ := SSTr.exists_tr P Bs hpl hk2 e0 he0 F
  let f : M.Ty P → ℂ := fun τ => if τ = ρ then 1 else 0
  have hfix : (d.κ f).1 Φ = Φ := by
    apply SSTr.trR_inj P Bs hpl hk2 e0 he0
    rw [hk0 f Φ, hΦ]
    funext τ
    rw [actA_kap]
    by_cases h : τ = ρ
    · simp [f, h]
    · simp [f, F, h]
  have hz : trR P Bs e Φ σ = 0 := by
    have h := congrFun (hk f Φ) σ
    rw [hfix, actA_kap] at h
    rw [h]
    simp [f, hσ]
  have hq := congrArg (fun g : MA.SmQ P.r P.TT => (g : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) hz
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply] at hq
  rw [SSTr.trR_apply P Bs hpl hk2 e he Φ σ, rawR, hΦv] at hq
  have h1 : ((F ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ) = 1 := by
    simp only [F, if_pos rfl, fnZ_eq_mk P (contDiffOn_const (c := (1 : ℂ)))]
  have hsum : inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (∑ τ, ((((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) *
      ((F τ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) • e0 τ ζ)) =
      (((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (e0 ρ ζ)) := by
    rw [SSTr.hsVec_sum, inner_sum, Finset.sum_eq_single ρ]
    · rw [hsVec_smul, inner_smul_right, h1, mul_one]
    · intro τ _ hτ
      simp only [F, if_neg hτ, ZeroMemClass.coe_zero, Pi.zero_apply, mul_zero, zero_smul]
      rw [← zero_smul ℂ (0 : Wq →L[ℂ] Wp), hsVec_smul, zero_smul, inner_zero_right]
    · intro h; exact absurd (Finset.mem_univ ρ) h
  have hw := SSTr.wR_pos P (ζ := ζ) hζ
  change ((wR P.k P.TT ζ : ℝ) : ℂ) * inner ℂ (B.hsVec (e σ ζ)) (B.hsVec (∑ τ, ((((wR P.k P.TT ζ)⁻¹ : ℝ) : ℂ) *
      ((F τ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) (qOne P ζ hζ)) • e0 τ ζ)) = 0 at hq
  rw [hsum, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hw.ne', Complex.ofReal_one, one_mul] at hq
  exact hq

def hsCLM : (Wq →L[ℂ] Wp) →L[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) :=
  (LinearMap.toContinuousLinearMap (SSTr.hsL (Wp := Wp) (Wq := Wq))).restrictScalars ℝ

theorem hsCLM_apply (A : Wq →L[ℂ] Wp) : hsCLM A = B.hsVec A := rfl

theorem e0_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hyp : GTHyp P Bs X d)
    (e e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e) (hk : KapF P Bs d e)
    (he0 : IsFrameB P Bs e0) (hk0 : KapF P Bs d e0) (ρ : M.Ty P) (ζ : ℂ) (hζ : ζ ∈ Ann P) :
    e0 ρ ζ = inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec (e0 ρ ζ)) • e ρ ζ := by
  obtain ⟨hfib0, -, -⟩ := (he0.2 ζ hζ)
  obtain ⟨-, -, hexp⟩ := he.2 ζ hζ
  conv_lhs => rw [hexp (e0 ρ ζ) (hfib0 ρ)]
  rw [Finset.sum_eq_single ρ]
  · intro σ _ hσ
    rw [kap_orth P Bs X d hyp e e0 he hk he0 hk0 ρ σ hσ ζ hζ, zero_smul]
  · intro h; exact absurd (Finset.mem_univ ρ) h

end

theorem phase_relation_holds : GTCPhaseRel := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hyp e e0 he hk he0 hk0
  refine ⟨fun ρ ζ => inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec (e ρ ζ)), fun ρ => ⟨?_, ?_⟩, ?_⟩
  · have h1 := (hsCLM (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn (he0.1 ρ)
    have h2 := (hsCLM (Wp := Wp) (Wq := Wq)).contDiff.comp_contDiffOn (he.1 ρ)
    have h3 := h1.inner ℂ h2
    simp only [Function.comp_def, hsCLM_apply] at h3
    exact h3
  · intro ζ hζ
    have hrel := e0_eq P Bs X d hyp e0 e he0 hk0 he hk ρ ζ hζ
    have hn := ((he.2 ζ hζ).2.1 ρ ρ)
    rw [if_pos rfl] at hn
    set c := inner ℂ (B.hsVec (e0 ρ ζ)) (B.hsVec (e ρ ζ)) with hc
    have hn0 := ((he0.2 ζ hζ).2.1 ρ ρ)
    rw [if_pos rfl] at hn0
    rw [hrel, hsVec_smul, inner_smul_left, inner_smul_right, hn0, mul_one] at hn
    have h2 : ((‖c‖ ^ 2 : ℝ) : ℂ) = 1 := by
      rw [← hn, Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]
    have h3 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h2
    have h4 : 0 ≤ ‖c‖ := norm_nonneg c
    nlinarith [h3, h4]
  · intro ρ ζ hζ
    exact e0_eq P Bs X d hyp e0 e he0 hk0 he hk ρ ζ hζ

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSAdjH
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt MeasureTheory

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdjH

open Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.NFx4

noncomputable section

section pt

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hsVec_zero' : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsVec
  ext i
  simp

theorem rawR_smul (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (a : ℂ) (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P μsec e (a • Z) ρ q = a * rawR P μsec e Z ρ q := by
  have hs : ∀ A : Wq →L[ℂ] Wp, B.hsVec (a • A) = a • B.hsVec A := by
    intro A
    unfold B.hsVec
    ext i
    simp
  simp only [rawR, Pi.smul_apply, hs, inner_smul_right]
  ring

theorem rawR_zero (P : M.Par) (μsec : ℂ → Matrix (Fin (P.k + 1)) (Fin (P.k + 1)) ℂ) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (ρ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P μsec e (0 : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q = 0 := by
  simp only [rawR, Pi.zero_apply, hsVec_zero', inner_zero_right, mul_zero]

theorem smQ_sum_apply (P : M.Par) (x : M.Ty P → MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((∑ σ, x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = ∑ σ, ((x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q := by
  simp only [AddSubmonoidClass.coe_finset_sum, Finset.sum_apply]

variable (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk2 : 2 ≤ P.k)
  (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)

include hpl hk2 he

theorem kap_pt (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hk : KapF P Bs d e)
    (f : M.Ty P → ℂ) (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e (((d.κ f).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q =
      f σ * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  have h := congrArg (fun x : M.Ty P → MA.SmQ P.r P.TT => ((x σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) (hk f Z)
  simp only [actA_kap] at h
  rw [← SSTr.trR_apply P Bs hpl hk2 e he, h, ← SSTr.trR_apply P Bs hpl hk2 e he]
  rfl

theorem ss_pt (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ)
    (hst : SmST P s t) (hL : SSLoc P Bs d e s t) {l : ℕ} (hl : l ∈ Finset.Icc 1 (P.k - 1))
    (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P) (q : MA.Qp P.r P.TT) :
    rawR P Bs.μsec e (((d.SS l).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q =
        ∑ σ, s l ρ' σ q.1.2 * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q ∧
      rawR P Bs.μsec e (((star (d.SS l)).1 Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ' q =
        ∑ σ, t l ρ' σ q.1.2 * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  obtain ⟨h1, h2⟩ := hL l hl Z ρ'
  constructor
  · rw [← SSTr.trR_apply P Bs hpl hk2 e he, h1, smQ_sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P (hst l ρ' σ).1, SSTr.trR_apply P Bs hpl hk2 e he]
  · rw [← SSTr.trR_apply P Bs hpl hk2 e he, h2, smQ_sum_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P (hst l ρ' σ).2, SSTr.trR_apply P Bs hpl hk2 e he]

theorem sec_expand (Z : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
      ∑ σ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) * rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) •
        e σ q.1.2 := by
  have hq : (q.1 : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := (SSTr.qr_iff P Bs hpl _).2 q.2
  have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (SSTr.radBase P Bs hpl)
    (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) Z.2
  have hF := hmem.2.1 _ hq
  simp only [NF.radR, Set.indicator_of_mem hq] at hF
  have hζ : P.TT < Complex.normSq q.1.2 := q.2.2
  obtain ⟨-, -, hexp⟩ := he.2 q.1.2 hζ
  conv_lhs => rw [hexp _ hF]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  have hw := SSTr.wR_pos P hζ
  simp only [rawR]
  rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hw.ne', Complex.ofReal_one, one_mul]

theorem hs_pair (Z W : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : MA.Qp P.r P.TT) :
    (((wR P.k P.TT q.1.2 ^ 2 : ℝ)) : ℂ) *
        inner ℂ (B.hsVec ((Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)))
          (B.hsVec ((W : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) =
      ∑ σ, star (rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) *
        rawR P Bs.μsec e (W : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q := by
  rw [sec_expand P Bs hpl hk2 e he W q, SSTr.hsVec_sum, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hw := (SSTr.wR_pos P (q.2.2 : P.TT < Complex.normSq q.1.2)).ne'
  rw [hsVec_smul, inner_smul_right]
  have hc : star (rawR P Bs.μsec e (Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q) =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) *
        inner ℂ (B.hsVec ((Z : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) (B.hsVec (e σ q.1.2)) := by
    simp only [rawR]
    rw [star_mul', Complex.star_def, Complex.conj_ofReal, inner_conj_symm]
  rw [hc]
  have hw' : ((wR P.k P.TT q.1.2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
  push_cast
  field_simp

theorem exists_proj (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (hk : KapF P Bs d e)
    (f : ℂ → ℂ) (hf : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f (Ann P)) (ρ : M.Ty P) :
    ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      (∀ σ (q : MA.Qp P.r P.TT), rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q =
        (if σ = ρ then 1 else 0) * f q.1.2) ∧ (NO.Pj d ρ).1 Φ = Φ := by
  obtain ⟨Φ0, hΦ0, -⟩ := SSTr.exists_tr P Bs hpl hk2 e he (fun _ => fnZ P f)
  refine ⟨(NO.Pj d ρ).1 Φ0, fun σ q => ?_, ?_⟩
  · show rawR P Bs.μsec e
        (((d.κ (fun ρ' => if ρ' = ρ then (1 : ℂ) else 0)).1 Φ0 : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
          Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ q = _
    rw [kap_pt P Bs hpl hk2 e he d hk, ← SSTr.trR_apply P Bs hpl hk2 e he, hΦ0, fnZ_val P hf]
  · show ((NO.Pj d ρ) * (NO.Pj d ρ)).1 Φ0 = _
    rw [NO.Pj_idem]

end pt

theorem pt_of_tests {U : Set ℂ} (hU : IsOpen U) {H : ℂ → ℂ} (hH : ContinuousOn H U)
    (h : ∀ φ : ℂ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ ζ, φ ζ • H ζ = 0) :
    ∀ ζ0 ∈ U, H ζ0 = 0 := by
  have hae := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (μ := volume) (hH.locallyIntegrableOn hU.measurableSet) h
  intro ζ0 hζ0
  by_contra hne
  have hc : ContinuousAt H ζ0 := hH.continuousAt (hU.mem_nhds hζ0)
  have hev : ∀ᶠ x in nhds ζ0, H x ≠ 0 ∧ x ∈ U := (hc.eventually_ne hne).and (hU.mem_nhds hζ0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hpos := Metric.measure_ball_pos (volume : Measure ℂ) ζ0 hδ
  rw [ae_iff] at hae
  apply hpos.ne'
  apply measure_mono_null _ hae
  intro x hx
  have := hball x hx
  simp only [Set.mem_setOf_eq, not_forall, exists_prop]
  exact ⟨this.2, this.1⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSAdjH
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJAGQQSSF
section
namespace Formalism.FourierDecayAlt.P.CutMP.JA

theorem quadratic_second_shift_form : SSn.Rep.Core.GQQSSF :=
  SSn.Rep.Core.GQ.gQQSSF_of_cut SSn.Rep.Core.GQ.quadratic_transfer_identity SSn.Rep.Core.GQ.quadratic_kappa_identity SSn.Rep.Core.GQ.quadratic_shift_identity

end Formalism.FourierDecayAlt.P.CutMP.JA
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDGaugeQQCore
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem jdg_gauge_of_core {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : Gauge.IsFrameB P Bs e)
    (hcore : ∀ (Dc : (Fin P.r → ℂ) → Set (Q.Mx P.k P.r)) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)), Gauge.FamR P Bs Dc Φ →
        ∀ (Y : ℝ) (a b : Fin 2) (ρ : M.Ty P),
          MA.toSm P (Gauge.rawR P Bs.μsec e (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b Φ) ρ) =
            MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b) (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ')) ρ) :
    ∀ J ∈ Q.FFl P.k P.r Bs.z Bs.z' Bs.π Bs.π' 0 (Gauge.OmB Bs), ∀ Y : ℝ,
      Gauge.trJB P Bs e (Q.CV P.k P.r (Y : ℂ) J) =
        MA.actA P (Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) (Y : ℂ)) (Gauge.trJB P Bs e J) := by
  intro J hJ Y
  obtain ⟨hF, hres, hcv⟩ := Gauge.gauge_transition_chain_holds Wp Wq P Bs hpl hk J hJ
  set Φ := Q.resG P.k P.r (Fin.last P.r) J with hΦ
  have hJe : Gauge.trJB P Bs e J = fun ρ => MA.toSm P (Gauge.rawR P Bs.μsec e Φ ρ) := by
    funext ρ
    exact congrArg (MA.toSm P) (hres e ρ)
  have hpair : ∀ a b : Fin 2,
      (∀ ρ, Gauge.rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ))) ρ ∈ MA.smSub P.r P.TT) ∧
      ∀ ρ, MA.toSm P (Gauge.rawR P Bs.μsec e (Q.crd (Q.cmp (Q.vABs P.r (Y : ℂ) P.r) a)
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ))) ρ) =
        MA.actA P (star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a) * MA.QQr P (MA.DQ P) (Y : ℂ) a b *
          Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J) ρ := by
    intro a b
    obtain ⟨hF1, hV1⟩ := Gauge.gauge_vector_transition_holds Wp Wq P Bs hpl hk e he _ Φ hF Y b
    have hF2 := Gauge.quadratic_local_family_holds Wp Wq P Bs hpl hk _ _ hF1 Y a b
    obtain ⟨hF3, hV2⟩ := Gauge.gauge_conj_vector_transition Wp Wq P Bs hpl hk e he _ _ hF2 Y a
    refine ⟨fun ρ => Gauge.raw_gauge_smoothness_holds Wp Wq P Bs hpl hk e he _ _ hF3 ρ, fun ρ => ?_⟩
    have hin : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ) ρ')) =
        MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J) := by
      funext ρ'
      rw [hV1 ρ', hJe]
    have hmid : (fun ρ' => MA.toSm P (Gauge.rawR P Bs.μsec e
        (Q.QL P.k P.r Bs.z Bs.z' (Fin.last P.r) (Y : ℂ) a b
          (Q.crd (Q.cmp (Q.vAB P.r (Y : ℂ) P.r) b) Φ)) ρ')) =
        MA.actA P (MA.QQr P (MA.DQ P) (Y : ℂ) a b)
          (MA.actA P (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b) (Gauge.trJB P Bs e J)) := by
      funext ρ'
      rw [hcore _ _ hF1 Y a b ρ', hin]
    rw [hV2 ρ, Gauge.actA_mul, Gauge.actA_mul, hmid]
  funext ρ
  show MA.toSm P (Gauge.rawJ P Bs e (Q.CV P.k P.r (Y : ℂ) J) ρ) = _
  rw [hcv e ρ Y]
  rw [show Wd.C0 (MA.QQr P (MA.DQ P)) (MA.sites P (MA.DQ P)) (Y : ℂ) =
      ∑ a, ∑ b, star (Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) a) * MA.QQr P (MA.DQ P) (Y : ℂ) a b *
        Wd.v0 (MA.sites P (MA.DQ P)) (Y : ℂ) b from rfl]
  simp only [Gauge.actA_sum, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ((hpair a b).2 ρ).symm]
  rw [Gauge.toSm_of_mem P (Subalgebra.sum_mem _ fun a _ => Subalgebra.sum_mem _ fun b _ => (hpair a b).1 ρ)]
  apply Subtype.ext
  simp only [AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Gauge.toSm_of_mem P ((hpair a b).1 ρ)]

theorem jdg_exists_of_gCore (hK : Gauge.GCore) (Cc : ℝ) (E : Type) [Field E] [NumberField E] [IsCMField E]
    (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ) (hB : BuiltOW Cc S T f χ ν' m₀ top A₀) (v : Fin S.f) :
    ∃ e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v)),
      IsFrame S T v e ∧ IsGauge S T v e ∧ IsGaugeQQ S T v e := by
  obtain ⟨hBP, -, -, -⟩ := hB
  obtain ⟨-, -, -, hIB, -, -, -, -, -, -, hk2, -, -⟩ := hBP
  obtain ⟨-, -, -, hpl, -, -⟩ := hIB.2 v
  obtain ⟨e, he, hc⟩ := hK (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hpl hk2
  exact ⟨e, he, jdg_gauge_of_core (D.parOf S v) (T v).base hpl hk2 e he hc, hc⟩

end

end Formalism.FourierDecayAlt.P.CutMP
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.GaXiSplit
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.LeftFubiniLemmas

open Formalism.FourierDecayAlt Formalism.REAL Formalism.QuantumDeterminants

def rcAct {k p ρ : ℕ} (y : B.Mat k ρ) (x : U.RC k p ρ) : U.RC k p ρ := (fun v a => (y * Matrix.of x.1) v a, x.2)

def lhOf {p : ℕ} (σ : Equiv.Perm (Fin p)) (v : U.LW σ → ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  U.wP σ * U.lowW σ v * (U.wP σ)⁻¹

def MMapEmbG : Prop := ∀ (k p ρ : ℕ) (Z : Matrix (Fin p) (Fin p) ℂ) (γ y₁ y₂ : B.Mat k ρ),
  U.mMap k p ρ Z (y₁ * γ * y₂) = U.embG k p ρ y₁ * U.mMap k p ρ Z γ * U.embG k p ρ y₂

def MMapLZU : Prop := ∀ (k p ρ : ℕ) (l Z u : Matrix (Fin p) (Fin p) ℂ) (γ : B.Mat k ρ), IsUnit l.det →
  U.mMap k p ρ (l * Z * u) γ = U.muP k p ρ (lᴴ)⁻¹ * U.mMap k p ρ Z γ * U.muP k p ρ u

def EmbGMuP : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ) (q : Matrix (Fin p) (Fin p) ℂ),
  U.embG k p ρ y * U.muP k p ρ q = U.muP k p ρ q * U.embG k p ρ y

def EmbGRn : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ) (x : U.RC k p ρ), yᴴ * Hpk k ρ * y = Hpk k ρ →
  U.embG k p ρ y * U.Rn k p ρ x = U.Rn k p ρ (rcAct y x) * U.embG k p ρ y

def HeadHEq : Prop := ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (v : U.LW σ → ℂ) (u : G.UT p → ℂ),
  U.headH σ d v u = lhOf σ v * U.hMat σ d * G.upper u ∧ G.IsLowerUni (lhOf σ v)

def ZjHZero : Prop := ∀ (p : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (η : U.XiH p 0 σ) (Z : G.Mat 0),
  U.ZjH σ d η Z = U.headH σ d η.2.1 η.2.2

def GaXiSplit : Prop := ∀ (k p ρ : ℕ) (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ) (ξ : U.Xi k p 0 ρ σ) (Z : G.Mat 0)
  (h ν h' ν' g : B.Mat k ρ), IsUnit h.det → IsUnit ν.det → h'ᴴ * Hpk k ρ * h' = Hpk k ρ →
  U.gaXi k ρ σ d ξ Z (h⁻¹ * ν⁻¹ * g * ν' * h') =
    (U.Rn k p ρ (-ξ.1.1) * U.muP k p ρ (lhOf σ ξ.2.2.1)ᴴ⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹)) *
      U.mMap k p ρ (U.hMat σ d) g *
      (U.embG k p ρ ν' * U.muP k p ρ (G.upper ξ.2.2.2) * U.Rn k p ρ (rcAct h' ξ.1.2)) * U.embG k p ρ h'

def LeftMem : Prop := ∀ (k p ρ : ℕ) (z : Fin (2 * ρ + k + 1) → ℂ) (x : U.RC k p ρ) (l : Matrix (Fin p) (Fin p) ℂ)
  (h ν : B.Mat k ρ), inWb k ρ z → G.IsLowerUni l → h ∈ UWset k ρ z → ν ∈ Nset k ρ →
  U.Rn k p ρ x * U.muP k p ρ (lᴴ)⁻¹ * U.embG k p ρ (h⁻¹ * ν⁻¹) ∈ Sset k (p + ρ) (liftVec k p ρ z)

def PsiRight : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (ν' : B.Mat k ρ) (u : G.UT p → ℂ)
  (x : U.RC k p ρ), inWb k ρ z' → ν' ∈ Nset k ρ →
  psi k (p + ρ) (liftVec k p ρ z') cStd (U.embG k p ρ ν' * U.muP k p ρ (G.upper u) * U.Rn k p ρ x) =
    psi k ρ z' cStd ν' * psi k (p + ρ) (liftVec k p ρ z') cStd (U.muP k p ρ (G.upper u)) *
      psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)

def PsiRnAct : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (h' : B.Mat k ρ) (x : U.RC k p ρ),
  inWb k ρ z' → h' ∈ UWset k ρ z' →
  psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ (rcAct h' x)) = psi k (p + ρ) (liftVec k p ρ z') cStd (U.Rn k p ρ x)

def PsiMuP : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (u : G.UT p → ℂ), inWb k ρ z' →
  star (psi k (p + ρ) (liftVec k p ρ z') cStd (U.muP k p ρ (G.upper u))) = G.psi U.betaU (U.supS (G.upper u))

def MuNLeft : Prop := ∀ (k p ρ : ℕ),
  D.muN k (p + ρ) = ((U.muRC k p ρ).prod ((volume : Measure (G.UT p → ℂ)).prod (D.muN k ρ))).map
    (fun x => Matrix.of.symm (U.embG k p ρ (Matrix.of x.2.2) * U.muP k p ρ (G.upper x.2.1) * U.Rn k p ρ x.1))

def RcActMP : Prop := ∀ (k p ρ : ℕ) (y : B.Mat k ρ), ‖y.det‖ = 1 →
  MeasurePreserving (rcAct (p := p) y) (U.muRC k p ρ) (U.muRC k p ρ)

def RightMP : Prop := ∀ (k p ρ : ℕ) (z' : Fin (2 * ρ + k + 1) → ℂ) (μj : Measure (Mt k ρ)) (μ0' : Measure (Mt k (p + ρ))),
  B.IsHaarOn (UWset k ρ z') μj → μj Set.univ = 1 → μ0' = μj.map (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl) →
  MeasurePreserving
    (fun y : (Mt k ρ × Mt k ρ) × (U.RC k p ρ × (G.UT p → ℂ)) =>
      (Formalism.FourierDecayAlt.P.PBM.levMt p ρ rfl y.1.1,
        Matrix.of.symm (U.embG k p ρ (Matrix.of y.1.2) * U.muP k p ρ (G.upper y.2.2) *
          U.Rn k p ρ (rcAct (Matrix.of y.1.1) y.2.1))))
    ((μj.prod (D.muN k ρ)).prod ((U.muRC k p ρ).prod volume)) (μ0'.prod (D.muN k (p + ρ)))

end Formalism.FourierDecayAlt.P.LeftFubiniLemmas
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.PBTAsm
section
namespace Formalism.FourierDecayAlt.P

theorem phi_zero_hermitian_curvature : Formalism.FourierDecayAlt.KB.PhiZero :=
  phi_zero_of_parts pbi_sectionExists_proof fibre_integral_smooth fibre_integral_cells

theorem density_constant : Formalism.FourierDecayAlt.KB.DensC :=
  pb_densC_of phi_zero_hermitian_curvature vector_vanishes_big_cell

end Formalism.FourierDecayAlt.P
end

