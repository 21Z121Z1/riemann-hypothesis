import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0080
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NfRadOrder0OfRadRed
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0081
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0066
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LieBracketMultiplication
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0078
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianFormRankFour
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ExistsFrameTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameCompletion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0065
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0067

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadTCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def ZJ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (k r N : ℕ) (f : Q.Mx k r → E) (g₀ : Q.Mx k r) : Prop :=
  ∃ (U : Set (Q.Mx k r)) (F : Q.Mx k r → E), IsOpen U ∧ g₀ ∈ U ∧ ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F U ∧
    (∀ g ∈ U, g ∈ Q.Glev k r (Fin.last r) → f g = F g) ∧ ∀ j ≤ N, iteratedFDeriv ℝ j F g₀ = 0

def GTCLRJetT : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ)
    (a b : Fin 2), ∃ N : ℕ, ∀ (f : Q.Mx k r → E) (g₀ : Q.Mx k r), g₀ ∈ Q.Glev k r (Fin.last r) →
      ZJ k r N f g₀ → Q.tL k r z z' (Fin.last r) Y a b f g₀ = 0

def GTCLRJetRad : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' → 2 ≤ P.k →
    ∀ (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (q : (Fin P.r → ℂ) × ℂ), q ∈ NF.QR P.k P.r Bs.z Bs.z' →
    ∀ N : ℕ, (∀ j ≤ N, iteratedFDeriv ℝ j
        (fun ζ => NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) (q.1, ζ)) q.2 = 0) →
      ZJ P.k P.r N ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1) (NF.muZ P.k P.r Bs.μsec q.2)

def GTCLRTaylor : Prop :=
  ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (ψ : ℂ → V) (U : Set ℂ) (ζ₀ : ℂ) (N : ℕ),
    IsOpen U → ζ₀ ∈ U → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ U →
    ∀ i ≤ N, iteratedFDeriv ℝ i (fun ζ => ψ ζ - ∑ j ∈ Finset.range (N + 1),
        ((j.factorial : ℝ)⁻¹) • iteratedFDeriv ℝ j ψ ζ₀ (fun _ => ζ - ζ₀)) ζ₀ = 0

def GTCLRadTOfCut : Prop := GTCLRJetT → GTCLRJetRad → GTCLRTaylor → GTCLRadT

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLocalFrameA
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem gcl_slice_iter {r : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : (Fin r → ℂ) × ℂ → V) (s : Set ((Fin r → ℂ) × ℂ)) (hs : IsOpen s)
    (hF : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F s) (q : (Fin r → ℂ) × ℂ) (hq : q ∈ s) (j : ℕ) :
    iteratedFDeriv ℝ j (fun ζ => F (q.1, ζ)) q.2 =
      (iteratedFDeriv ℝ j F q).compContinuousLinearMap (fun _ => ContinuousLinearMap.inr ℝ (Fin r → ℂ) ℂ) := by
  let a : (Fin r → ℂ) × ℂ := (q.1, 0)
  let L : ℂ →L[ℝ] (Fin r → ℂ) × ℂ := ContinuousLinearMap.inr ℝ (Fin r → ℂ) ℂ
  let G : (Fin r → ℂ) × ℂ → V := fun p => F (a + p)
  let s' : Set ((Fin r → ℂ) × ℂ) := (fun p => a + p) ⁻¹' s
  have hs' : IsOpen s' := hs.preimage (continuous_const.add continuous_id)
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) G s' :=
    hF.comp ((contDiff_const.add contDiff_id).contDiffOn) (fun p hp => hp)
  have hslice : (fun ζ : ℂ => F (q.1, ζ)) = G ∘ L := by
    funext ζ
    simp [G, a, L]
  have hq' : L q.2 ∈ s' := by
    show a + L q.2 ∈ s
    simpa [a, L] using hq
  have hpre : IsOpen (L ⁻¹' s') := hs'.preimage L.continuous
  have hmem : q.2 ∈ L ⁻¹' s' := hq'
  rw [hslice, ← iteratedFDerivWithin_of_isOpen j hpre hmem,
    L.iteratedFDerivWithin_comp_right hG hs'.uniqueDiffOn hpre.uniqueDiffOn hq'
      (by exact_mod_cast (le_top : ((j : ℕ∞)) ≤ ⊤)),
    iteratedFDerivWithin_of_isOpen j hs' hq']
  have hGq : iteratedFDeriv ℝ j G (L q.2) = iteratedFDeriv ℝ j F q := by
    show iteratedFDeriv ℝ j (fun p => F (a + p)) (L q.2) = _
    rw [iteratedFDeriv_comp_add_left']
    show iteratedFDeriv ℝ j F (a + L q.2) = _
    congr 1
    ext <;> simp [a, L]
  rw [hGq]

theorem gcl_isRadDiff {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π')
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) (hT : RadDZ P Bs T) :
    NF.IsRadDiff P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' T := by
  obtain ⟨n, A, hA, hT'⟩ := hT
  have hmem : ∀ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (NF.radR P.k P.r Bs.z Bs.z' Bs.μsec (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp))) (NF.QR P.k P.r Bs.z Bs.z') :=
    fun Φ => (Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB Φ Φ.2).1
  have hopen : IsOpen (NF.QR P.k P.r Bs.z Bs.z') := by
    have h1 : IsOpen (Formalism.QuantumDeterminants.OmX P.r) := by
      have h2 : Formalism.QuantumDeterminants.OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by
        ext x
        simp [Formalism.QuantumDeterminants.OmX]
      rw [h2]
      exact isOpen_iInter_of_finite (fun l => isOpen_ne_fun (continuous_apply l) continuous_const)
    exact (h1.preimage continuous_fst).inter
      (isOpen_lt continuous_const (Complex.continuous_normSq.comp continuous_snd))
  refine ⟨n, fun j q => (A j q.2).comp (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin j => ContinuousLinearMap.inr ℝ (Fin P.r → ℂ) ℂ)), ?_, ?_⟩
  · intro j
    have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun q : (Fin P.r → ℂ) × ℂ => A j q.2)
        (NF.QR P.k P.r Bs.z Bs.z') :=
      (hA j).comp contDiff_snd.contDiffOn (fun q hq => hq.2)
    exact hA'.clm_comp contDiffOn_const
  · intro Φ q hq
    rw [hT' Φ q hq]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [gcl_slice_iter _ _ hopen (hmem Φ) q hq j]
    simp only [ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.compContinuousLinearMapL_apply]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCRefCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

def dTy (P : M.Par) (ρ : M.Ty P) : M.Ty P → ℂ := fun σ => if σ = ρ then 1 else 0

def GTCCurvId : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ ρ : M.Ty P,
      (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
        algebraMap ℂ (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) *
          (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)

def GTCCurvTr : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e → KapF P Bs d e →
      ∀ A B : M.Ty P → ℂ → ℂ, SmAB P A B → ConnF P Bs d e A B → (∀ ρ, ∀ ζ ∈ Ann P, B ρ ζ = star (A ρ ζ)) →
        (∀ ρ : M.Ty P, (d.L.nabs * d.L.nab - d.L.nab * d.L.nabs) * d.κ (dTy P ρ) =
          algebraMap ℂ (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) ((2 * M.aC P ρ * P.TT : ℝ) : ℂ) *
            (d.L.GGi * d.L.GGi) * d.κ (dTy P ρ)) →
        ∀ ρ, ∀ ζ ∈ Ann P, (NF.dZb (fun w => modA P ρ w - A ρ w) ζ).re = 0

def GTCRefTrace : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∃ e0 : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e0 ∧ KapF P Bs d e0 ∧
      ∃ A0 B0 : M.Ty P → ℂ → ℂ, SmAB P A0 B0 ∧ ConnF P Bs d e0 A0 B0 ∧
        ∀ ρ, ∃ n : ℤ, ∀ ζ ∈ Ann P, (ζ * (modA P ρ ζ - A0 ρ ζ)).re = (n : ℝ) / 2

def GTCRefAn : Prop :=
  ∀ (TT : ℝ) (α : ℂ → ℂ) (c : ℝ), 0 ≤ TT →
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) α {ζ : ℂ | TT < Complex.normSq ζ} →
    (∀ ζ : ℂ, TT < Complex.normSq ζ → (ζ * α ζ).re = c) →
    ∀ R : ℝ, 0 < R → TT < R ^ 2 → (circleIntegral α 0 R).im = 2 * Real.pi * c

def GTCRefOfCut : Prop := GTCReal → GTCCurvId → GTCCurvTr → GTCRefTrace → GTCRefAn → GTCRef

private theorem contDiffOn_modA_ann (P : M.Par) (ρ : M.Ty P) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := by
  have hs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun ζ : ℂ => star ζ) := by
    first
    | exact contDiff_id.star
    | exact Complex.conjCLE.contDiff
    | simpa using (Complex.conjCLE.contDiff (n := ((⊤ : ℕ∞) : WithTop ℕ∞)))
  have h : modA P ρ = fun ζ : ℂ => (M.aC P ρ : ℂ) * star ζ * (ζ * star ζ - (P.TT : ℂ))⁻¹ := by
    funext ζ
    simp only [modA, div_eq_mul_inv]
    rw [← Complex.mul_conj]
    rfl
  rw [h]
  apply ContDiffOn.mul
  · exact (contDiff_const.mul hs).contDiffOn
  · apply ContDiffOn.inv
    · exact ((contDiff_id.mul hs).sub contDiff_const).contDiffOn
    · intro ζ hζ
      have hz : ζ * star ζ = ((Complex.normSq ζ : ℝ) : ℂ) := Complex.mul_conj ζ
      rw [hz, ← Complex.ofReal_sub]
      exact Complex.ofReal_ne_zero.mpr (sub_pos.mpr hζ).ne'

theorem gTCRef_of_cut : GTCRefOfCut := by
  intro hReal hCurvId hCurvTr hTrace hAn Wp Wq _ _ _ _ _ _ P Bs X d hH
  obtain ⟨e0, he0, hk0, A0, B0, hAB, hC, hn⟩ := hTrace Wp Wq P Bs X d hH
  have hB : ∀ ρ, ∀ ζ ∈ Ann P, B0 ρ ζ = star (A0 ρ ζ) := hReal Wp Wq P Bs X d hH e0 he0 hk0 A0 B0 hAB hC
  refine ⟨e0, he0, hk0, A0, B0, hAB, hC,
    hCurvTr Wp Wq P Bs X d hH e0 he0 hk0 A0 B0 hAB hC hB (hCurvId Wp Wq P Bs X d hH), ?_⟩
  intro ρ R hR hR2
  obtain ⟨n, hn'⟩ := hn ρ
  refine ⟨n, ?_⟩
  have hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (modA P ρ) (Ann P) := contDiffOn_modA_ann P ρ
  have key := hAn (max P.TT 0) (fun w => modA P ρ w - A0 ρ w) ((n : ℝ) / 2) (le_max_right _ _)
    ((hsm.sub (hAB ρ).1).mono (fun ζ hζ => show P.TT < Complex.normSq ζ from
      lt_of_le_of_lt (le_max_left _ _) (show max P.TT 0 < Complex.normSq ζ from hζ)))
    (fun ζ hζ => hn' ζ (show P.TT < Complex.normSq ζ from lt_of_le_of_lt (le_max_left _ _) hζ)) R hR (max_lt hR2 (pow_pos hR 2))
  rw [key]; ring

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGauge
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

theorem mulQ_zbP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P (MA.DQ P).zbP f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = star q.1.2 * (f : MA.Qp P.r P.TT → ℂ) q := mul_conjCoordinate_apply P f q

theorem mulQ_zP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P (MA.DQ P).zP f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q = q.1.2 * (f : MA.Qp P.r P.TT → ℂ) q := algebraMap_comp_ofPadicInt_apply P f q

theorem mulQ_ggiP (P : M.Par) (f : MA.SmQ P.r P.TT) (q : MA.Qp P.r P.TT) :
    ((mulQ P ((MA.DQ P).ggiP P.TT) f : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      ((Complex.normSq q.1.2 : ℂ) - (P.TT : ℂ))⁻¹ * (f : MA.Qp P.r P.TT → ℂ) q := ggiP_apply P f q

section main

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem nabF_phase (P : M.Par) (hTT : 0 ≤ P.TT) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (A B u : M.Ty P → ℂ → ℂ) (hAB : SmAB P A B) (hC : ConnF P Bs d e A B) (hu : PhaseEq P A B u) :
    NabF P Bs d (fun ρ ζ => u ρ ζ • e ρ ζ) := by
  have hu' : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 :=
    fun ρ => ⟨(hu ρ).1, fun ζ hζ => ((hu ρ).2 ζ hζ).1⟩
  intro Φ
  constructor
  · funext ρ
    rw [actA_nabA, trR_phase P Bs e u hu', trR_phase P Bs e u hu', (hC Φ ρ).1]
    apply Subtype.ext
    funext q
    have hv := conj_smooth (hu ρ).1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    obtain ⟨_, hA, _⟩ := (hu ρ).2 q.1.2 hζ
    have hdc := (dZ_conj_unit P (hu ρ).1 (fun ζ hζ => ((hu ρ).2 ζ hζ).1) hζ).1
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Pi.add_apply, Pi.mul_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [mulQ_zbP, mulQ_ggiP, dzQ_apply P hTT, dzQ_apply P hTT, wirtQ_mul, wirtinger_derivative_fibre_function P hv, fnZ_val P hv,
      fnZ_val P (hAB ρ).1, hdc]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P hv]
    unfold modA at hA
    linear_combination (star (u ρ q.1.2) * ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) * hA
  · funext ρ
    rw [actA_nabsA, trR_phase P Bs e u hu', trR_phase P Bs e u hu', (hC Φ ρ).2]
    apply Subtype.ext
    funext q
    have hv := conj_smooth (hu ρ).1
    have hζ : q.1.2 ∈ Ann P := q.2.2
    obtain ⟨_, _, hB⟩ := (hu ρ).2 q.1.2 hζ
    have hdc := (dZ_conj_unit P (hu ρ).1 (fun ζ hζ => ((hu ρ).2 ζ hζ).1) hζ).2
    simp only [Subalgebra.coe_add, Subalgebra.coe_mul, Subalgebra.coe_smul, Subalgebra.coe_neg, Pi.add_apply,
      Pi.mul_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    rw [mulQ_zP, mulQ_ggiP, dzbQ_apply P hTT, dzbQ_apply P hTT, wirtQ_mul, wirt_fnZ_zb P hv, fnZ_val P hv,
      fnZ_val P (hAB ρ).2, hdc]
    simp only [Subalgebra.coe_mul, Pi.mul_apply, fnZ_val P hv]
    unfold modB at hB
    linear_combination (star (u ρ q.1.2) * ((trR P Bs e Φ ρ : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) * hB

end main

theorem gauge_transform_holds : GTCGauge := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e he hk A B' u hAB hC hu
  have hTT : 0 ≤ P.TT := torus_parameter Wp Wq P Bs X d hH
  have hu' : ∀ ρ, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (u ρ) (Ann P) ∧ ∀ ζ ∈ Ann P, ‖u ρ ζ‖ = 1 :=
    fun ρ => ⟨(hu ρ).1, fun ζ hζ => ((hu ρ).2 ζ hζ).1⟩
  exact ⟨isFrameB_phase P Bs e u he hu', kapF_phase P Bs d e u hu' hk,
    nabF_phase P hTT Bs d e A B' u hAB hC hu⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSLocalCut
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

def SliceLoc (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')) : Prop :=
  ∀ (Φ Φ' : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (c c' : Fin P.r → ℂ), c ∈ OmX P.r → c' ∈ OmX P.r →
    (∀ ζ ∈ Ann P, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      (Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ)) →
    ∀ ζ ∈ Ann P, (T Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ) =
      (T Φ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c' (NF.muZ P.k P.r Bs.μsec ζ)

end preds

def GTSSLSliceDZ : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq),
    Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' →
    ∀ T : Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'), RadDZ P Bs T → SliceLoc P Bs T

def GTSSLSliceSS : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → (∀ (Y : ℂ) (a b : Fin 2), SliceLoc P Bs (X.t Y a b)) →
    ∀ l ∈ Finset.Icc 1 (P.k - 1), SliceLoc P Bs (d.SS l).1 ∧ SliceLoc P Bs (star (d.SS l)).1

def GTSSLMat : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ e : M.Ty P → ℂ → (Wq →L[ℂ] Wp), IsFrameB P Bs e →
    (∀ l ∈ Finset.Icc 1 (P.k - 1), SliceLoc P Bs (d.SS l).1 ∧ SliceLoc P Bs (star (d.SS l)).1) →
      ∃ s t : ℕ → M.Ty P → M.Ty P → ℂ → ℂ, SmST P s t ∧ SSLoc P Bs d e s t

def GTSSLocalOfCut : Prop := GTCLRadT → GTSSLSliceDZ → GTSSLSliceSS → GTSSLMat → GTSSLocal

theorem gTSSLocal_of_cut : GTSSLocalOfCut := by
  intro hRT hDZ hSS hMat Wp Wq _ _ _ _ _ _ P Bs X d hH e he _
  have hT := hRT Wp Wq P Bs hH.1 hH.2.1 hH.2.2.1 X
  have hSl : ∀ (Y : ℂ) (a b : Fin 2), SliceLoc P Bs (X.t Y a b) := fun Y a b =>
    hDZ Wp Wq P Bs hH.1 _ (hT Y a b)
  exact hMat Wp Wq P Bs X d hH e he (hSS Wp Wq P Bs X d hH hSl)

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTSSPhaseA
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.M Finset

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh

def height (P : M.Par) (ρ : M.Ty P) : ℕ := ∑ i, ((ρ i : Fin _) : ℕ)

theorem sum_ind (P : M.Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) :
    ∑ i : Fin (P.k - 1), (if (i : ℕ) + 1 = l then 1 else 0) = 1 := by
  rw [Finset.mem_Icc] at hl
  rw [Finset.sum_eq_single ⟨l - 1, by omega⟩]
  · rw [if_pos (by simp; omega)]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    ext
    simp
    omega
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem up_height (P : M.Par) (l : ℕ) (hl : l ∈ Icc 1 (P.k - 1)) (ρ ρ' : M.Ty P) (hU : M.Up P l ρ ρ') :
    height P ρ' = height P ρ + 1 := by
  unfold height
  rw [Finset.sum_congr rfl (fun i _ => hU i), Finset.sum_add_distrib, sum_ind P l hl]

theorem pred_exists (P : M.Par) (ρ' : M.Ty P) (h : height P ρ' ≠ 0) :
    ∃ l ∈ Icc 1 (P.k - 1), ∃ ρ, M.Up P l ρ ρ' := by
  obtain ⟨i, hi⟩ : ∃ i, ((ρ' i : Fin _) : ℕ) ≠ 0 := by
    by_contra hall
    push_neg at hall
    apply h
    unfold height
    exact Finset.sum_eq_zero fun i _ => hall i
  refine ⟨(i : ℕ) + 1, ?_, fun j => if hj : j = i then ⟨((ρ' j : Fin _) : ℕ) - 1,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (ρ' j).isLt⟩ else ρ' j, ?_⟩
  · rw [Finset.mem_Icc]
    have := i.isLt
    omega
  · intro j
    by_cases hj : j = i
    · subst hj
      simp
      omega
    · simp only [hj, dif_neg, not_false_eq_true]
      rw [if_neg]
      · simp
      · intro h2
        apply hj
        ext
        omega

theorem phase_exists (P : M.Par) (w : ℕ → M.Ty P → M.Ty P → ℂ)
    (hw1 : ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → ‖w l ρ ρ'‖ = 1)
    (hcoc : ∀ l ∈ Icc 1 (P.k - 1), ∀ j ∈ Icc 1 (P.k - 1), j ≠ l → ∀ ρ ρl ρj ρlj : M.Ty P,
      M.Up P l ρ ρl → M.Up P j ρ ρj → M.Up P j ρl ρlj → M.Up P l ρj ρlj →
        w j ρl ρlj * w l ρ ρl = w l ρj ρlj * w j ρ ρj) :
    ∃ u : M.Ty P → ℂ, (∀ ρ, ‖u ρ‖ = 1) ∧
      ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → u ρ' = w l ρ ρ' * u ρ := by
  classical
  have key : ∀ n : ℕ, ∃ u : M.Ty P → ℂ, (∀ ρ, ‖u ρ‖ = 1) ∧
      ∀ l ∈ Icc 1 (P.k - 1), ∀ ρ ρ', M.Up P l ρ ρ' → height P ρ' ≤ n → u ρ' = w l ρ ρ' * u ρ := by
    intro n
    induction n with
    | zero =>
      refine ⟨fun _ => 1, fun _ => by simp, fun l hl ρ ρ' hU hh => ?_⟩
      rw [up_height P l hl ρ ρ' hU] at hh
      omega
    | succ n ih =>
      obtain ⟨u, hu1, hu⟩ := ih
      let u' : M.Ty P → ℂ := fun ρ' =>
        if hh : height P ρ' = n + 1 then
          (let hp := pred_exists P ρ' (by omega)
           w hp.choose hp.choose_spec.2.choose ρ' * u hp.choose_spec.2.choose)
        else u ρ'
      have hu'1 : ∀ ρ, ‖u' ρ‖ = 1 := by
        intro ρ'
        simp only [u']
        split_ifs with hh
        · have hp := pred_exists P ρ' (by omega)
          rw [norm_mul, hw1 _ (pred_exists P ρ' (by omega)).choose_spec.1 _ _
            (pred_exists P ρ' (by omega)).choose_spec.2.choose_spec, hu1, one_mul]
        · exact hu1 ρ'
      refine ⟨u', hu'1, fun l hl ρ ρ' hU hh => ?_⟩
      have hhρ := up_height P l hl ρ ρ' hU
      have hρ : u' ρ = u ρ := by
        simp only [u']
        rw [dif_neg (by omega)]
      rw [hρ]
      by_cases hn : height P ρ' = n + 1
      · simp only [u']
        rw [dif_pos hn]
        set hp := pred_exists P ρ' (by omega) with hpdef
        set l0 := hp.choose with hl0
        have hl0m : l0 ∈ Icc 1 (P.k - 1) := hp.choose_spec.1
        set ρ0 := hp.choose_spec.2.choose with hρ0
        have hU0 : M.Up P l0 ρ0 ρ' := hp.choose_spec.2.choose_spec
        show w l0 ρ0 ρ' * u ρ0 = w l ρ ρ' * u ρ
        by_cases hll : l0 = l
        · have e : ρ0 = ρ := Formalism.FourierDecayAlt.P.Mx4.up_inj P l ρ' ρ0 ρ (hll ▸ hU0) hU
          rw [e, hll]
        · obtain ⟨σ, hσ1, hσ2⟩ := Formalism.FourierDecayAlt.P.Mx4.up_mixed1 P l0 l (Ne.symm hll) ρ ρ' ρ0 hU hU0

          have h0 := up_height P l0 hl0m ρ0 ρ' hU0
          have e1 : u ρ0 = w l σ ρ0 * u σ := hu l hl σ ρ0 hσ2 (by omega)
          have e2 : u ρ = w l0 σ ρ * u σ := hu l0 hl0m σ ρ hσ1 (by omega)
          have hc' := hcoc l0 hl0m l hl (Ne.symm hll) σ ρ ρ0 ρ' hσ1 hσ2 hU hU0
          rw [e1, e2, ← mul_assoc, ← mul_assoc, hc']
      · have hle : height P ρ' ≤ n := by omega
        simp only [u']
        rw [dif_neg hn]
        exact hu l hl ρ ρ' hU hle
  obtain ⟨u, hu1, hu⟩ := key (Finset.univ.sup (height P))
  exact ⟨u, hu1, fun l hl ρ ρ' hU => hu l hl ρ ρ' hU (Finset.le_sup (Finset.mem_univ ρ'))⟩

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.SSPh
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.DifferentialOperatorBracket
section
namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q

theorem differential_operator_linear : Qr.DOpLin := qr_dOpLin_of trotter_product_formula trotter_product_matrices representation_exp

theorem differential_operator_bracket : Qr.DOpBracket := qr_dOpBracket_of representation_exp differential_operator_linear differential_operator_adjoint

theorem elementary_lie_elements : Qr.EcLie := qr_ecLie_of differential_operator_linear differential_operator_bracket

theorem frame_general_linear : Qr.FrameGl := qr_frameGl_of elementary_lie_elements

theorem lie_stabilizer : Qr.LieStab := qr_lieStab_of exp_generates representation_exp elementary_lie_elements

theorem qr_frameChange_proof : Qr.FrameChange := qr_frameChange_of elementary_lie_elements frame_general_linear

theorem branching_compact : Qr.BranchingK :=
  qr_branchingK_of branching_algebraic frame_general_linear lie_stabilizer stabilizer_lie_algebra qr_frameChange_proof
    exists_frame_two

theorem branching_proof : Branching := qr_branching_of branching_compact

theorem spectral_two_by_two : RadialDecompositionSpectral := radialDecompositionSpectral_of_branching branching_proof

end Formalism.FourierDecayAlt.P
end

