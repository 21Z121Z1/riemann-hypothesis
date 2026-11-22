import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0088
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0108
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0176
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NormalFormOrderZeroOfParts
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddSSn
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0097
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0034
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0051
import Formalism.HermitianCurvature.HermitianCurvatureProofs.IsOpenAdelicUnipotentTimesIntegralOutsideSet
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedS
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0151
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0175

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLMat
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem wRc_smooth (P : M.Par) : ContDiffOn ℝ ∞ (fun ζ : ℂ => ((wR P.k P.TT ζ : ℝ) : ℂ)) (Ann P) := by
  have h1 : ContDiffOn ℝ ∞ (fun ζ : ℂ => (Complex.normSq ζ - P.TT) ^ (P.k - 1)) (Ann P) := by
    have h2 : ContDiff ℝ ∞ (fun ζ : ℂ => Complex.normSq ζ) := by
      have h3 : (fun ζ : ℂ => Complex.normSq ζ) = fun ζ : ℂ => ‖ζ‖ ^ 2 := by
        funext ζ
        rw [Complex.normSq_eq_norm_sq]
      rw [h3]
      exact contDiff_norm_sq ℝ
    exact ((h2.sub contDiff_const).pow _).contDiffOn
  have h4 : ContDiffOn ℝ ∞ (fun ζ : ℂ => wR P.k P.TT ζ) (Ann P) := by
    unfold wR
    refine h1.sqrt fun ζ hζ => ?_
    have h5 : P.TT < Complex.normSq ζ := hζ
    exact (pow_pos (by linarith) _).ne'
  exact Complex.ofRealCLM.contDiff.comp_contDiffOn h4

theorem wRc_ne (P : M.Par) {ζ : ℂ} (hζ : ζ ∈ Ann P) : ((wR P.k P.TT ζ : ℝ) : ℂ) ≠ 0 := by
  have h5 : P.TT < Complex.normSq ζ := hζ
  have h6 : 0 < wR P.k P.TT ζ := by
    unfold wR
    exact Real.sqrt_pos.mpr (pow_pos (by linarith) _)
  exact_mod_cast h6.ne'

section mat

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem tz_TT (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
  rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
  rfl

theorem radBase_of (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') :
    NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
  exact ⟨Bs.k_pos, Bs.z_mem, Bs.z'_mem, Bs.T_pos, Bs.T'_pos, Bs.sec, Bs.π_rep, Bs.π'_rep, Bs.π_cont,
    Bs.π'_cont⟩

theorem slice_smooth (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ : M.Ty P) {c : Fin P.r → ℂ} (hc : c ∈ OmX P.r) :
    ContDiffOn ℝ ∞ (fun ζ => inner ℂ (B.hsVec (e ρ ζ))
      (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ)))) (Ann P) := by
  have hm : ContDiffOn ℝ ∞ (MA.ext (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)) (MA.Qset P.r P.TT) :=
    radial_space_smoothness Wp Wq P Bs hpl hk e he Φ ρ
  have h1 : ContDiffOn ℝ ∞ (fun ζ : ℂ => MA.ext (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) (c, ζ))
      (Ann P) :=
    hm.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun ζ hζ => ⟨hc, hζ⟩)
  refine (Formalism.FourierDecayAlt.P.NFRadRedLocSec.cd_div h1 (wRc_smooth P) fun ζ hζ => wRc_ne P hζ).congr fun ζ hζ => ?_
  have hq : ((c, ζ) : MA.E P.r) ∈ MA.Qset P.r P.TT := ⟨hc, hζ⟩
  simp only [MA.ext, dif_pos hq, rawR]
  rw [mul_div_cancel_left₀ _ (wRc_ne P hζ)]

theorem key_slice (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hk : 2 ≤ P.k) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (he : IsFrameB P Bs e)
    (Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = e ρ ζ)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hT : SliceLoc P Bs T)
    (hC : ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute T W)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') {c c0 : Fin P.r → ℂ} (hc : c ∈ OmX P.r) (hc0 : c0 ∈ OmX P.r)
    {ζ : ℂ} (hζ : ζ ∈ Ann P) :
    (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      ∑ ρ, inner ℂ (B.hsVec (e ρ ζ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ))) •
        (T (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ) := by
  have hTz := tz_TT P Bs hpl
  have hRB := radBase_of P Bs hpl
  let F : M.Ty P → ℂ → ℂ := fun ρ ζ' => inner ℂ (B.hsVec (e ρ ζ'))
    (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ')))
  have hFs : ∀ ρ, ContDiffOn ℝ ∞ (F ρ) {ζ | P.TT < Complex.normSq ζ} := fun ρ =>
    slice_smooth P Bs hpl hk e he Φ ρ hc
  choose W hW using fun ρ => Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (F ρ) (hFs ρ)
  have hQR : ∀ c' ∈ OmX P.r, ∀ ζ' ∈ Ann P, ((c', ζ') : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
    fun c' hc' ζ' hζ' => ⟨hc', by rw [hTz]; exact hζ'⟩
  have hmul : ∀ (ρ : M.Ty P) (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), ∀ c' ∈ OmX P.r, ∀ ζ' ∈ Ann P,
      ((W ρ Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ') =
        F ρ ζ' • (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ') := by
    intro ρ Θ c' hc' ζ' hζ'
    have hq := hQR c' hc' ζ' hζ'
    rw [hW ρ Θ]
    have h := Formalism.FourierDecayAlt.P.NFRO.radR_mulZ hRB (F ρ) Θ.2 hq
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  let Φc : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := ∑ ρ, W ρ (Ψ ρ)
  have hsumv : ∀ (G : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c' : Fin P.r → ℂ) (g : Q.Mx P.k P.r),
      ((∑ ρ, G ρ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' g =
        ∑ ρ, (G ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' g := by
    intro G c' g
    rw [Submodule.coe_sum, Finset.sum_apply, Finset.sum_apply]
  have hΦv : ∀ ζ' ∈ Ann P, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ') =
      (Φc : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ') := by
    intro ζ' hζ'
    have hq := hQR c hc ζ' hζ'
    rw [hsumv]
    have hmem := (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ Φ.2).2.1 (c, ζ') hq
    simp only [NF.radR, Set.indicator_of_mem hq] at hmem
    rw [(he.2 ζ' hζ').2.2 _ hmem]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [hmul ρ (Ψ ρ) c hc ζ' hζ', hΨ ρ c hc ζ' hζ']
  rw [hT Φ Φc c c hc hc hΦv ζ hζ, map_sum, hsumv]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hcomm : T (W ρ (Ψ ρ)) = W ρ (T (Ψ ρ)) := by
    have h := (hC (F ρ) (hFs ρ) (W ρ) (hW ρ)).eq
    exact LinearMap.congr_fun h (Ψ ρ)
  rw [hcomm, hmul ρ (T (Ψ ρ)) c hc ζ hζ]
  congr 1
  exact hT (Ψ ρ) (Ψ ρ) c c0 hc hc0 (fun ζ' hζ' => by rw [hΨ ρ c hc ζ' hζ', hΨ ρ c0 hc0 ζ' hζ']) ζ hζ

end mat

theorem second_shift_matrix_form : GTSSLMat := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hSL
  obtain ⟨hpl, hk, -, hL, hS, hRel, hQQ⟩ := hH
  have hTz := tz_TT P Bs hpl
  have hRB := radBase_of P Bs hpl
  let c0 : Fin P.r → ℂ := fun _ => 1
  have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
  have hsec : ∀ ρ, ((NF.QR P.k P.r Bs.z Bs.z').indicator fun q : (Fin P.r → ℂ) × ℂ => e ρ q.2) ∈
      NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
    intro ρ
    refine ⟨((he.1 ρ).comp contDiff_snd.contDiffOn fun q hq => ?_).congr fun q hq => ?_, fun q hq => ?_,
      fun q hq => ?_⟩
    · show P.TT < Complex.normSq q.2
      rw [← hTz]; exact hq.2
    · simp [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_mem hq]
      exact (he.2 q.2 (by rw [← hTz]; exact hq.2)).1 ρ
    · simp [Set.indicator_of_notMem hq]
  choose Ψ0 hΨ0 hΨr using fun ρ =>
    Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _ (hsec ρ)
  let Ψ : M.Ty P → Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := fun ρ => ⟨Ψ0 ρ, hΨ0 ρ⟩
  have hΨ : ∀ ρ, ∀ c ∈ OmX P.r, ∀ ζ ∈ Ann P,
      (Ψ ρ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) = e ρ ζ := by
    intro ρ c hc ζ hζ
    have hq : ((c, ζ) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc, by rw [hTz]; exact hζ⟩
    have h := congrFun (hΨr ρ) (c, ζ)
    simp only [NF.radR, Set.indicator_of_mem hq] at h
    exact h
  have hCom : ∀ l ∈ Finset.Icc 1 (P.k - 1), ∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
      ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f →
        Commute (d.SS l).1 W ∧ Commute (star (d.SS l)).1 W := by
    intro l hl f hf W hW
    obtain ⟨W₁, hW₁⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZ f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZ_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    obtain ⟨W₂, hW₂⟩ := Formalism.FourierDecayAlt.P.multiplication_zeta_exists Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl (NF.dZb f)
      (Formalism.FourierDecayAlt.P.NFx4.NO.dZb_smooth (Formalism.FourierDecayAlt.P.NFx4.NO.isOpen_U _) hf)
    exact (Formalism.FourierDecayAlt.P.normal_form_order_zero Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl X d hL hS hRel hQQ f hf W W₁ W₂
      hW hW₁ hW₂).2.1 l hl
  let ent : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') → M.Ty P → M.Ty P → ℂ → ℂ := fun T ρ' ρ ζ =>
    inner ℂ (B.hsVec (e ρ' ζ)) (B.hsVec ((T (Ψ ρ) : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0 (NF.muZ P.k P.r Bs.μsec ζ)))
  have hent : ∀ T ρ' ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (ent T ρ' ρ) (Ann P) := fun T ρ' ρ =>
    slice_smooth P Bs hpl hk e he (T (Ψ ρ)) ρ' hc0
  have hmain : ∀ (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), SliceLoc P Bs T →
      (∀ f : ℂ → ℂ, ContDiffOn ℝ ∞ f {ζ | P.TT < Complex.normSq ζ} →
        ∀ W : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), NF.IsMulZ W f → Commute T W) →
      ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (ρ' : M.Ty P),
        trR P Bs e (T Φ) ρ' = ∑ ρ, fnZ P (ent T ρ' ρ) * trR P Bs e Φ ρ := by
    intro T hT hC Φ ρ'
    have hv : ∀ (Θ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (σ : M.Ty P),
        ((trR P Bs e Θ σ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) =
          rawR P Bs.μsec e (Θ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) σ := fun Θ σ =>
      Formalism.FourierDecayAlt.P.CutMP.En.toSm_val_of_mem P (radial_space_smoothness Wp Wq P Bs hpl hk e he Θ σ)
    apply Subtype.ext
    funext q
    rw [hv]
    rw [show (((∑ ρ, fnZ P (ent T ρ' ρ) * trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) =
        ∑ ρ, ent T ρ' ρ q.1.2 * rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q by
      rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun ρ _ => ?_
      rw [MulMemClass.coe_mul, Pi.mul_apply, hv, fnZ_eq_mk P (hent T ρ' ρ)]]
    have hc : q.1.1 ∈ OmX P.r := q.2.1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    simp only [rawR]
    rw [key_slice P Bs hpl hk e he Ψ hΨ T hT hC Φ hc hc0 hζ, Formalism.FourierDecayAlt.P.CutMP.En.hsVec_sum_smul, inner_sum,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [inner_smul_right]
    ring
  refine ⟨fun l => ent (d.SS l).1, fun l => ent (star (d.SS l)).1,
    fun l ρ' ρ => ⟨hent _ ρ' ρ, hent _ ρ' ρ⟩, ?_⟩
  intro l hl Φ ρ'
  exact ⟨hmain _ (hSL l hl).1 (fun f hf W hW => (hCom l hl f hf W hW).1) Φ ρ',
    hmain _ (hSL l hl).2 (fun f hf W hW => (hCom l hl f hf W hW).2) Φ ρ'⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddGen
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.CutMP.JA.BStar Formalism.QuantumDeterminants
open scoped ComplexConjugate Matrix

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

noncomputable section

section gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

def orderZeroDifferentialOperator (S : C.HidaSetting E Wp Wq) (v : Fin S.f) (c ca : Coef S v)
    (hadj : ∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')) :
    B.DiffOp S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)) :=
  [⟨c, ca, [], fun X hX => by simp at hX, hadj⟩]

variable {S : C.HidaSetting E Wp Wq} {v : Fin S.f} {c ca : Coef S v}
  {hadj : ∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')}

theorem order_zero_operator_apply (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    B.opApply (orderZeroDifferentialOperator S v c ca hadj) J = fun g => c g (J g) := by
  funext g
  simp only [B.opApply, orderZeroDifferentialOperator, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  first
    | rfl
    | simp [B.Rw]

theorem order_zero_operator_adjoint (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) :
    B.opAdj (orderZeroDifferentialOperator S v c ca hadj) J = fun g => ca g (J g) := by
  funext g
  first
    | (simp [B.opAdj, orderZeroDifferentialOperator]; done)
    | (simp [B.opAdj, orderZeroDifferentialOperator]; rfl)
    | rfl

theorem order_zero_operator_order : B.opOrder (orderZeroDifferentialOperator S v c ca hadj) = 0 := by
  first
    | rfl
    | simp [B.opOrder, orderZeroDifferentialOperator]

end gen

section eqv

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]
  {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))} {v : Fin S.f}

theorem eqv_left {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {n : B.Mat S.G.k S.G.r} (hn : n ∈ Nset S.G.k S.G.r) (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (n * g) X = c g X := by
  have hp : (T v).base.inSS ((Matrix.of.symm 1, Matrix.of.symm n⁻¹), (Matrix.of.symm 1, Matrix.of.symm 1)) :=
    ⟨by simpa using P.BigCellZetaMinors.one_uw (T v).base.z, by simpa using WeylGroupFacts.mem_n_inv hn,
      by simpa using P.BigCellZetaMinors.one_uw (T v).base.z', by simpa using WeylGroupFacts.mem_n_one⟩
  have h := he _ hp g hg X
  have hu : IsUnit n.det := WeylGroupFacts.isUnit_of_uh hn.1
  simp only [Equiv.apply_symm_apply, inv_one, (T v).base.π_rep.1, (T v).base.π'_rep.1, B.sgs,
    Matrix.nonsing_inv_nonsing_inv n hu, Matrix.one_mul, Matrix.mul_one] at h
  simpa [ContinuousLinearMap.one_def] using h.symm

theorem eqv_right {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {n : B.Mat S.G.k S.G.r} (hn : n ∈ Nset S.G.k S.G.r) (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (g * n) X = c g X := by
  have hp : (T v).base.inSS ((Matrix.of.symm 1, Matrix.of.symm 1), (Matrix.of.symm 1, Matrix.of.symm n)) :=
    ⟨by simpa using P.BigCellZetaMinors.one_uw (T v).base.z, by simpa using WeylGroupFacts.mem_n_one,
      by simpa using P.BigCellZetaMinors.one_uw (T v).base.z', by simpa using hn⟩
  have h := he _ hp g hg X
  simp only [Equiv.apply_symm_apply, inv_one, (T v).base.π_rep.1, (T v).base.π'_rep.1, B.sgs,
    Matrix.one_mul, Matrix.mul_one] at h
  simpa [ContinuousLinearMap.one_def] using h.symm

theorem eqv_uw {c : Coef S v} (he : EqvC S T v c) {g : B.Mat S.G.k S.G.r} (hg : g ∈ B.GV S.G.k S.G.r)
    {h h' : B.Mat S.G.k S.G.r} (hh : h ∈ UWset S.G.k S.G.r (T v).base.z) (hh' : h' ∈ UWset S.G.k S.G.r (T v).base.z')
    (X : Wq (S.pl v) →L[ℂ] Wp (S.pl v)) :
    c (h * g * h') (((T v).base.π h).comp (X.comp ((T v).base.π' h'))) =
      ((T v).base.π h).comp ((c g X).comp ((T v).base.π' h')) := by
  have hp : (T v).base.inSS ((Matrix.of.symm h, Matrix.of.symm 1), (Matrix.of.symm h'⁻¹, Matrix.of.symm 1)) :=
    ⟨by simpa using hh, by simpa using WeylGroupFacts.mem_n_one,
      by simpa using P.BigCellInversePair.uw_inv hh', by simpa using WeylGroupFacts.mem_n_one⟩
  have hg' : h * g * h' ∈ B.GV S.G.k S.G.r := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul hh.1 hg) hh'.1
  have e := he _ hp (h * g * h') hg' X
  have hu' : IsUnit h'.det := WeylGroupFacts.isUnit_of_uh hh'.1
  have hs : B.sgs ((Matrix.of.symm h, Matrix.of.symm 1), (Matrix.of.symm h'⁻¹, Matrix.of.symm 1)) (h * g * h') = g := by
    simp only [B.sgs, Equiv.apply_symm_apply, inv_one, Matrix.mul_one]
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu', Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (WeylGroupFacts.isUnit_of_uh hh.1), Matrix.one_mul]
  rw [hs] at e
  simpa only [Equiv.apply_symm_apply, Matrix.nonsing_inv_nonsing_inv h' hu'] using e

theorem equivariant_coefficient_preserves_forms {c : Coef S v} (hc : B.CkOn ⊤ (B.GPos (T v).base) c) (he : EqvC S T v c)
    {J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} (hJ : J ∈ smoothFormsPositiveCone S T v) :
    (fun g => c g (J g)) ∈ smoothFormsPositiveCone S T v := by
  obtain ⟨hS, hL, hR, hU⟩ := hJ
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g₀ hg₀
    obtain ⟨U1, J', hU1, hg1, hJ', hJeq⟩ := hS g₀ hg₀
    obtain ⟨U2, c', hU2, hg2, hc', hceq⟩ := hc g₀ ⟨hg₀.1.1, hg₀.2.1⟩
    have h2 : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun g => ContinuousLinearMap.restrictScalarsL ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v))
          (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) ℝ ℝ (c' g)) (U1 ∩ U2) :=
      (ContinuousLinearMap.restrictScalarsL ℂ (Wq (S.pl v) →L[ℂ] Wp (S.pl v))
          (Wq (S.pl v) →L[ℂ] Wp (S.pl v)) ℝ ℝ).contDiff.comp_contDiffOn (hc'.mono Set.inter_subset_right)
    refine ⟨U1 ∩ U2, fun g => c' g (J' g), hU1.inter hU2, ⟨hg1, hg2⟩,
      h2.clm_apply (hJ'.mono Set.inter_subset_left), ?_⟩
    intro g hg hgl
    simp only
    rw [hJeq g hg.1 hgl, hceq g hg.2 hgl.1]
  · intro g hg n hn
    simp only
    rw [hL g hg n hn, ContinuousLinearMap.map_smul, eqv_left he hg.1.1 hn.1]
  · intro g hg n hn
    simp only
    rw [hR g hg n hn, ContinuousLinearMap.map_smul, eqv_right he hg.1.1 hn.1]
  · intro g hg h hh h' hh'
    simp only
    rw [hU g hg h hh h' hh', eqv_uw he hg.1.1 hh hh']

end eqv

section transfer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
  [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem trJ_of_fibMat (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π')
    (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hFr : IsFrame S T v e) (c : Coef S v)
    (V : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)
    (hV : FibMat S T v e c V) (b : A (D.parOf S v) (DQ (D.parOf S v)))
    (β : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → (DQ (D.parOf S v)).R)
    (hβ : ∀ ρ π, b ρ π = (DQ (D.parOf S v)).fnP (β ρ π) (cjD (D.parOf S v) (β ρ π)))
    (hβV : ∀ ρ π q, evD (D.parOf S v) q (β ρ π) = V ρ π q)
    (J : B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (hJ : J ∈ smoothFormsPositiveCone S T v) :
    actA (D.parOf S v) b (trJ S T v e J) = trJ S T v e (fun g => c g (J g)) := by
  funext ρ
  set X := actA (D.parOf S v) b (trJ S T v e J) ρ with hXdef
  have hsm : ∀ π (q : Qp (D.parOf S v).r (D.parOf S v).TT), evQ (D.parOf S v) (trJ S T v e J π) q =
      ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) := fun π q =>
    congrFun (En.toSm_val_of_mem (D.parOf S v) (En.trace_smoothness E Wp Wq S T v hPl e hFr J hJ π)) q
  have hw : (fun q : Qp (D.parOf S v).r (D.parOf S v).TT =>
      ((Real.sqrt (MA.wq S.G.k q.1 (D.parOf S v).TT) : ℝ) : ℂ) *
        inner ℂ (B.hsVec (e ρ q.1.2)) (B.hsVec (c (B.gq (T v).base q.1) (J (B.gq (T v).base q.1))))) =
      (X : Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) := by
    funext q
    have hX := actA_fm_apply (D.parOf S v) hβ (trJ S T v e J) ρ q
    change _ = evQ (D.parOf S v) X q
    rw [hX]
    simp only [hsm, hβV]
    have hfib := En.fibre_membership_holds E Wp Wq S T v hPl J hJ q.1 q.2
    have hspan := (hFr.2 q.1.2 q.2.2).2.2 _ hfib
    have hcJ : c (B.gq (T v).base q.1) (J (B.gq (T v).base q.1)) =
        ∑ π, inner ℂ (B.hsVec (e π q.1.2)) (B.hsVec (J (B.gq (T v).base q.1))) •
          c (B.gq (T v).base q.1) (e π q.1.2) := by
      conv_lhs => rw [hspan]
      rw [map_sum]
      simp only [ContinuousLinearMap.map_smul]
    rw [hcJ, En.hsVec_sum_smul, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [inner_smul_right, hV q.1 q.2 ρ π]
    ring
  unfold trJ
  beta_reduce
  rw [hw]
  unfold MA.toSm
  rw [dif_pos X.2]

theorem real_to_bounded_holds : RealToBdd := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hPl e Cb c ca V b hFr hR hb
  obtain ⟨hadj, hc, hca, he, hea, hbc, hbca, hV⟩ := hR
  choose β hβ hβV using hb
  refine ⟨orderZeroDifferentialOperator S v c ca hadj, order_zero_operator_order, ⟨?_, ?_⟩, ?_, fun J hJ => ⟨?_, ?_, ?_⟩⟩
  · intro Tm hTm
    simp only [orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    exact ⟨hc, hca⟩
  · intro p hp f _ g hg
    rw [order_zero_operator_apply, order_zero_operator_apply]
    exact he p hp g hg.1 _
  · intro Tm hTm ε hε m
    simp only [orderZeroDifferentialOperator, List.mem_singleton] at hTm
    subst hTm
    obtain ⟨C1, h1⟩ := hbc ε hε m
    obtain ⟨C2, h2⟩ := hbca ε hε m
    refine ⟨max C1 C2, fun u w hu hw hl g hg hG => ⟨?_, ?_⟩⟩
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h1 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow)
    · have hpow : 0 ≤ B.gN g ^ (Cb * ((S.G.r : ℝ) + 1) * m) := Real.rpow_nonneg (Real.sqrt_nonneg _) _
      rw [zero_add]
      exact (h2 u w hu hw hl g hg hG).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpow)
  · rw [order_zero_operator_apply]; exact equivariant_coefficient_preserves_forms hc he hJ
  · rw [order_zero_operator_adjoint]; exact equivariant_coefficient_preserves_forms hca hea hJ
  · rw [order_zero_operator_apply]
    exact trJ_of_fibMat S T v hPl e hFr c V hV b β hβ hβV J hJ

end transfer

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHatJDCapRModelV
section
open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP

noncomputable section

theorem site_vector_eq_tensor_product (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (b : Fin 2) : Wd.v0 (MA.sites P (MA.DQ P)) y b = L.Tprod y b 0 := by
  obtain ⟨hp, -, hc, hci, -⟩ := hL
  have hT : (fun σ => Wd.Ts σ y) ∘ MA.siteA P (MA.DQ P) = L.Tl y := by
    funext l
    simp only [Function.comp_apply]
    unfold R.LevelData.Tl
    rw [hp, hc, hci]
    rfl
  unfold Wd.v0 MA.sites R.LevelData.Tprod
  rw [List.map_reverse, List.map_ofFn, hT]

theorem star_site_vector_eq_tensor (P : M.Par) (L : R.LevelData (MA.A P (MA.DQ P)) P.r) (hL : MA.IsModelLevel P (MA.DQ P) L)
    (y : ℂ) (a : Fin 2) :
    star (Wd.v0 (MA.sites P (MA.DQ P)) y a) = L.Tvprod (starRingEnd ℂ y) a 0 := by
  have hL' := hL
  obtain ⟨hp, hpb, hc, hci, hcb, hcbi, -⟩ := hL'
  have sp : ∀ l, star (L.p l) = -L.pb l := fun l => by
    rw [hp, hpb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).pP l)) = -MA.sc P (MA.DQ P) ((MA.DQ P).pbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc, Formalism.FourierDecayAlt.P.MAx3.F.star_pP]
    unfold MA.sc
    simp
  have sc : ∀ l, star (L.c l) = L.cb l := fun l => by
    rw [hc, hcb]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).cP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have sci : ∀ l, star (L.ci l) = L.cbi l := fun l => by
    rw [hci, hcbi]
    show star (MA.sc P (MA.DQ P) ((MA.DQ P).ciP l)) = MA.sc P (MA.DQ P) ((MA.DQ P).cbiP l)
    rw [Formalism.FourierDecayAlt.P.MAx3.F.star_sc]
    rfl
  have h := congrArg (fun M => M 0 a) (Formalism.FourierDecayAlt.P.TLB.star_Tprod_gen L sp sc sci y)
  simp only [Matrix.conjTranspose_apply, Matrix.transpose_apply] at h
  rw [site_vector_eq_tensor_product P L hL y a]
  exact h

theorem mirror_residue_model_holds : JDRModelV := by
  intro P L hL y
  refine ⟨fun b => site_vector_eq_tensor_product P L hL (y : ℂ) b, fun a => ?_⟩
  rw [star_site_vector_eq_tensor P L hL (y : ℂ) a, Complex.conj_ofReal]

end

end Formalism.FourierDecayAlt.P.CutMP
end

