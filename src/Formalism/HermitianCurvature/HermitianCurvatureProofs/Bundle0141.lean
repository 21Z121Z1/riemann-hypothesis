import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0064
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGaugeVLem
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0059
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ChainRecursionFromSingleDescent
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0137
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0093
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0124
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0069
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0079
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0113

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCFamLocal
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

open Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem family_locality_holds : FamLocal := by
  intro Wp Wq _ _ _ _ _ _ P Bs hpl hk X Dc Φ hΦ q
  have hk1 : 1 ≤ P.k := by omega
  have hz := hpl.2.1
  have hz' := hpl.2.2.1
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hpl.2.2.2.1]; exact hpl.1.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos
  have hsec := Bs.sec
  obtain ⟨hOpen, hIsDom, hMu, hFF⟩ := hΦ

  have hdom : ∀ x ∈ Q.DomR P.k P.r Bs.z Bs.z', x.2 ∈ Dc x.1 := by
    intro x hx
    obtain ⟨h, hh, h', hh', hg⟩ := Formalism.FourierDecayAlt.P.NFRadRedA.decomp hk1 hz hz' hT hT' hsec hx.2.1 hx.2.2
    set ζ := Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) x.2 with hζ
    have hζT : P.TT < Complex.normSq ζ := by
      have h1 := hx.2.2
      unfold Q.GGl at h1
      show P.T * P.T' < _
      rw [← hpl.2.2.2.1, ← hpl.2.2.2.2.1]
      linarith
    let q' : MA.Qp P.r P.TT := ⟨(x.1, ζ), hx.1, hζT⟩
    have hmu : NF.muZ P.k P.r Bs.μsec ζ ∈ Dc x.1 := hMu q'
    have hmuG : NF.muZ P.k P.r Bs.μsec ζ ∈ Q.Glev P.k P.r (Fin.last P.r) :=
      Formalism.FourierDecayAlt.P.CutMP.Gauge.VLem.muZ_glev hpl q'
    have hS : ∀ {w : Fin (2 * P.r + P.k + 1) → ℂ} {s : Q.Mx P.k P.r}, s ∈ UWset P.k P.r w →
        s ∈ Q.Slev P.k P.r w (Fin.last P.r) := by
      intro w s hs
      exact ⟨s, hs, 1, Formalism.FourierDecayAlt.P.Qx6.one_nlev _, by simp⟩
    rw [hg]
    exact (hIsDom x.1 hx.1).2 _ ⟨hmuG, hmu⟩ h (hS hh) h' (hS hh')

  let Φt : Q.Fn P.k P.r (Wq →L[ℂ] Wp) := fun c g => if (c, g) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ c g else 0
  have hΦt_mem : Φt ∈ Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π' := by
    refine ⟨fun x hx => ?_, fun x₀ hx₀ => ?_, fun x hx h hh h' hh' => ?_⟩
    · show (if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0) = 0
      rw [if_neg hx]
    · obtain ⟨U, F, hU, hx₀U, hF, hΦF⟩ := hFF.1 x₀ ⟨hx₀.1, hdom x₀ hx₀⟩ hx₀.2.1
      have hO : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r ∧ 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} := by
        have h1 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | x.1 ∈ OmX P.r} := by
          have : IsOpen (OmX P.r) := by
            have e : OmX P.r = ⋂ l, {x : Fin P.r → ℂ | x l ≠ 0} := by ext x; simp [OmX]
            rw [e]
            exact isOpen_iInter_of_finite fun l => isOpen_ne_fun (continuous_apply l) continuous_const
          exact this.preimage continuous_fst
        have h2 : IsOpen {x : (Fin P.r → ℂ) × Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2} :=
          isOpen_lt continuous_const ((Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z').comp continuous_snd)
        exact h1.inter h2
      refine ⟨U ∩ {x | x.1 ∈ OmX P.r ∧ 0 < Q.GGl P.k P.r Bs.z Bs.z' x.2}, F, hU.inter hO, ⟨hx₀U, hx₀.1, hx₀.2.2⟩,
        hF.mono Set.inter_subset_left, fun x hx hxG => ?_⟩
      have hxD : x ∈ Q.DomR P.k P.r Bs.z Bs.z' := ⟨hx.2.1, hxG, hx.2.2⟩
      show (if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0) = F x
      rw [if_pos hxD]
      exact hΦF x hx.1 hxG
    · have hxD' := Formalism.FourierDecayAlt.P.Qx5.DomR_inv hh hh' hx
      show (if (x.1, h * x.2 * h') ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 (h * x.2 * h') else 0) =
        (Bs.π h).comp ((if (x.1, x.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ x.1 x.2 else 0).comp (Bs.π' h'))
      rw [if_pos hxD', if_pos hx]
      exact (hFF.2 x.1 hx.1).2.2.2 x.2 ⟨hx.2.1, hdom x hx⟩ h hh h' hh'
  refine ⟨⟨Φt, hΦt_mem⟩, {ζ' | Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ'}, ?_, fun ζ' hζ' => ?_⟩
  · refine (isOpen_lt continuous_const Complex.continuous_normSq).mem_nhds ?_
    show Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact q.2.2
  have hqD : (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hz hz' hsec (q := (q.1.1, ζ')) ⟨q.2.1, hζ'⟩
  have hval : Φt q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') = Φ q.1.1 (NF.muZ P.k P.r Bs.μsec ζ') := by
    show (if (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') ∈ Q.DomR P.k P.r Bs.z Bs.z' then _ else 0) = _
    rw [if_pos hqD]
  refine ⟨hval, fun Y a b => ?_⟩
  rw [X.t_apply Y a b ⟨Φt, hΦt_mem⟩ (q.1.1, NF.muZ P.k P.r Bs.μsec ζ') hqD]
  show Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (Φt q.1.1) (NF.muZ P.k P.r Bs.μsec ζ') =
    Q.tL P.k P.r Bs.z Bs.z' (Fin.last P.r) Y a b (Φ q.1.1) (NF.muZ P.k P.r Bs.μsec ζ')
  have hDo : IsOpen {g : Q.Mx P.k P.r | 0 < Q.GGl P.k P.r Bs.z Bs.z' g} :=
    isOpen_lt continuous_const (Formalism.FourierDecayAlt.P.Qx5.GGl_continuous P.k P.r Bs.z Bs.z')
  refine (Formalism.FourierDecayAlt.P.Qx2.ll_tL (i := Fin.last P.r) hDo Bs.z Bs.z' Y a b).1 (Φt q.1.1) (Φ q.1.1) (fun x hx => ?_)
    _ ⟨hqD.2.1, hqD.2.2⟩
  show (if (q.1.1, x) ∈ Q.DomR P.k P.r Bs.z Bs.z' then Φ q.1.1 x else 0) = Φ q.1.1 x
  rw [if_pos ⟨q.2.1, hx.1, hx.2⟩]

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCLRadT
section
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

theorem radial_torus_local_holds : GTCLRadT :=
  radial_torus_of_jets_taylor jet_finite_order_along_level jet_radial_holds taylor_expansion_holds

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferFn
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

section sm

variable {r : ℕ} {TT : ℝ}

theorem smInv_mem (f : MA.SmQ r TT) (hf : ∀ q, (f : MA.Qp r TT → ℂ) q ≠ 0) :
    (fun q => ((f : MA.Qp r TT → ℂ) q)⁻¹) ∈ MA.smSub r TT := by
  have hsm : ContDiffOn ℝ MA.sm (MA.ext (f : MA.Qp r TT → ℂ)) (MA.Qset r TT) := f.2
  have hne : ∀ x ∈ MA.Qset r TT, MA.ext (f : MA.Qp r TT → ℂ) x ≠ 0 := by
    intro x hx
    simp only [MA.ext, dif_pos hx]
    exact hf _
  show ContDiffOn ℝ MA.sm (MA.ext (fun q => ((f : MA.Qp r TT → ℂ) q)⁻¹)) (MA.Qset r TT)
  exact (hsm.inv hne).congr fun x hx => by simp only [Pi.inv_apply, MA.ext, dif_pos hx]

theorem inverse_apply (f : MA.SmQ r TT) (hf : ∀ q, (f : MA.Qp r TT → ℂ) q ≠ 0) (q : MA.Qp r TT) :
    ((Ring.inverse f : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = ((f : MA.Qp r TT → ℂ) q)⁻¹ := by
  obtain ⟨g, hg⟩ : ∃ g : MA.SmQ r TT, ∀ q, (g : MA.Qp r TT → ℂ) q = ((f : MA.Qp r TT → ℂ) q)⁻¹ :=
    ⟨⟨_, smInv_mem f hf⟩, fun _ => rfl⟩
  have hfg : f * g = 1 := by
    apply Subtype.ext
    funext q'
    show (f : MA.Qp r TT → ℂ) q' * (g : MA.Qp r TT → ℂ) q' = 1
    rw [hg, mul_inv_cancel₀ (hf q')]
  have hu : IsUnit f := ⟨⟨f, g, hfg, by rw [mul_comm]; exact hfg⟩, rfl⟩
  have hinv : Ring.inverse f = g := by
    calc Ring.inverse f = Ring.inverse f * (f * g) := by rw [hfg, mul_one]
      _ = g := by rw [← mul_assoc, Ring.inverse_mul_cancel f hu, one_mul]
  rw [hinv, hg]

theorem coordQ_vz (q : MA.Qp r TT) : ((MA.coordQ (r := r) (TT := TT) M.vz : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = q.1.2 := by
  show MA.coordE (M.vz (r := r)) q.1 = q.1.2
  simp [MA.coordE, MA.zE, M.vz]

theorem coordQ_vzb (q : MA.Qp r TT) :
    ((MA.coordQ (r := r) (TT := TT) M.vzb : MA.SmQ r TT) : MA.Qp r TT → ℂ) q = (starRingEnd ℂ) q.1.2 := by
  show MA.coordE (M.vzb (r := r)) q.1 = (starRingEnd ℂ) q.1.2
  simp [MA.coordE, MA.zE, M.vzb]

end sm

def ggS (P : M.Par) : MA.SmQ P.r P.TT := (MA.DQ P).gg P.TT

section tr

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem trR_unit (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp))
    (Φ Ψ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (φ : MA.SmQ P.r P.TT) (hφ : ∀ q, (φ : MA.Qp P.r P.TT → ℂ) q ≠ 0)
    (hΨ : ∀ q : MA.Qp P.r P.TT, (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
      (φ : MA.Qp P.r P.TT → ℂ) q • (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)) :
    trR P Bs e Ψ = fun ρ => φ * trR P Bs e Φ ρ := by
  have hsm : ∀ (c : ℂ) (A : Wq →L[ℂ] Wp), B.hsVec (c • A) = c • B.hsVec A := by
    intro c A
    unfold B.hsVec
    ext i
    simp
  funext ρ
  have hraw : rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
      fun q => (φ : MA.Qp P.r P.TT → ℂ) q * rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ q := by
    funext q
    simp only [rawR]
    rw [hΨ q, hsm, inner_smul_right]
    ring
  show MA.toSm P (rawR P Bs.μsec e (Ψ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) =
    φ * MA.toSm P (rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ)
  rw [hraw]
  generalize rawR P Bs.μsec e (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ = u
  unfold MA.toSm
  by_cases hu : u ∈ MA.smSub P.r P.TT
  · have hmul : (fun q => (φ : MA.Qp P.r P.TT → ℂ) q * u q) ∈ MA.smSub P.r P.TT :=
      (MA.smSub P.r P.TT).mul_mem φ.2 hu
    rw [dif_pos hmul, dif_pos hu]
    rfl
  · have hmul : (fun q => (φ : MA.Qp P.r P.TT → ℂ) q * u q) ∉ MA.smSub P.r P.TT := by
      intro hm
      apply hu
      have h2 := (MA.smSub P.r P.TT).mul_mem (smInv_mem φ hφ) hm
      convert h2 using 1
      funext q
      simp [hφ q]
    rw [dif_neg hmul, dif_neg hu, mul_zero]

theorem sec_pt (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (q : MA.Qp P.r P.TT) :
    (q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2) ∈ Q.DomR P.k P.r Bs.z Bs.z' ∧
      Q.zetaL P.k P.r Bs.z Bs.z' (Fin.last P.r) (NF.muZ P.k P.r Bs.μsec q.1.2) = q.1.2 := by
  have hζ : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq q.1.2 := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]
    exact q.2.2
  have hq : (q.1.1, q.1.2) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨q.2.1, hζ⟩
  exact ⟨Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hpl.2.1 hpl.2.2.1 Bs.sec hq,
    Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hpl.2.1 hpl.2.2.1 Bs.sec hζ⟩

theorem tt_pos (P : M.Par) (hP : P.OK) : 0 < P.TT := by
  show 0 < P.T * P.T'
  exact mul_pos hP.T_pos hP.T'_pos

theorem zeta_ne (P : M.Par) (hP : P.OK) (q : MA.Qp P.r P.TT) : q.1.2 ≠ 0 := by
  have h2 : P.TT < Complex.normSq q.1.2 :=
    (q.2 : (∀ l, q.1.1 l ≠ 0) ∧ P.TT < Complex.normSq q.1.2).2
  intro h
  rw [h, map_zero] at h2
  linarith [tt_pos P hP]

theorem gg_ne (P : M.Par) (q : MA.Qp P.r P.TT) : (q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ)) ≠ 0 := by
  have h2 : P.TT < Complex.normSq q.1.2 :=
    (q.2 : (∀ l, q.1.1 l ≠ 0) ∧ P.TT < Complex.normSq q.1.2).2
  rw [Complex.mul_conj]
  intro h
  have h3 : ((Complex.normSq q.1.2 - P.TT : ℝ) : ℂ) = 0 := by
    push_cast
    exact h
  rw [Complex.ofReal_eq_zero] at h3
  linarith

theorem trR_fn (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (e : M.Ty P → ℂ → (Wq →L[ℂ] Wp)) (j : Fin 6)
    (φ : MA.SmQ P.r P.TT) (hφ : ∀ q, (φ : MA.Qp P.r P.TT → ℂ) q ≠ 0)
    (hv : ∀ q : MA.Qp P.r P.TT, Q.fnVal P.k P.r Bs.z Bs.z' j (NF.muZ P.k P.r Bs.μsec q.1.2) = (φ : MA.Qp P.r P.TT → ℂ) q)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') :
    trR P Bs e (X.fn j Φ) =
      fun ρ => φ * trR P Bs e Φ ρ := by
  refine trR_unit P Bs e Φ (X.fn j Φ) φ hφ fun q => ?_
  have h := X.fn_apply j Φ _ (sec_pt P Bs hpl q).1
  dsimp only at h
  rw [h, hv q]

end tr

theorem gauge_function_holds : GTFn := by
  intro Wp Wq _ _ _ _ _ _ P Bs X d hH e Φ
  obtain ⟨hpl, -, -, hL, -, -, -⟩ := hH
  have hP : P.OK := hpl.1
  have hz := fun q => (sec_pt P Bs hpl q).2
  have hzv : ∀ q : MA.Qp P.r P.TT, ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) q ≠ 0 := fun q => by rw [coordQ_vz]; exact zeta_ne P hP q
  have hzbv : ∀ q : MA.Qp P.r P.TT, ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) :
      MA.Qp P.r P.TT → ℂ) q ≠ 0 := fun q => by
    rw [coordQ_vzb]; exact (map_ne_zero _).2 (zeta_ne P hP q)
  have hgg : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    show ((MA.coordQ (r := P.r) (TT := P.TT) M.vz : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q *
        ((MA.coordQ (r := P.r) (TT := P.TT) M.vzb : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q - (P.TT : ℂ) = _
    rw [coordQ_vz, coordQ_vzb]
  have hggv : ∀ q : MA.Qp P.r P.TT, ((ggS P : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q ≠ 0 :=
    fun q => by rw [hgg]; exact gg_ne P q
  have hGG : ∀ q : MA.Qp P.r P.TT, ((Q.GGl P.k P.r Bs.z Bs.z' (NF.muZ P.k P.r Bs.μsec q.1.2) : ℝ) : ℂ) =
      q.1.2 * (starRingEnd ℂ) q.1.2 - (P.TT : ℂ) := fun q => by
    rw [Complex.mul_conj]
    unfold Q.GGl
    rw [hz q, hpl.2.2.2.1, hpl.2.2.2.2.1]
    have hT : ((P.TT : ℝ) : ℂ) = (P.T : ℂ) * (P.T' : ℂ) := by
      show (((P.T * P.T' : ℝ)) : ℂ) = _
      push_cast; ring
    rw [hT]
    push_cast
    ring
  have hsc : ∀ (w : (MA.DQ P).Pr) (f : M.Ty P → MA.SmQ P.r P.TT),
      MA.actA P (MA.sc P (MA.DQ P) w) f = fun ρ => w.1 (f ρ) := VLem.actA_sc P
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hL.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 0 _ hzv (fun q => by rw [coordQ_vz]; exact hz q) Φ).trans ?_
    exact (hsc ((MA.DQ P).zP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 1 (Ring.inverse (MA.coordQ M.vz))
      (fun q => by rw [inverse_apply _ hzv]; exact inv_ne_zero (hzv q))
      (fun q => by rw [inverse_apply _ hzv, coordQ_vz]; show (Q.zetaL _ _ _ _ _ _)⁻¹ = _; rw [hz q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ziP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 2 _ hzbv (fun q => by
      rw [coordQ_vzb]; show star (Q.zetaL _ _ _ _ _ _) = _; rw [hz q]; rfl) Φ).trans ?_
    exact (hsc ((MA.DQ P).zbP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 3 (Ring.inverse (MA.coordQ M.vzb))
      (fun q => by rw [inverse_apply _ hzbv]; exact inv_ne_zero (hzbv q))
      (fun q => by
        rw [inverse_apply _ hzbv, coordQ_vzb]; show (star (Q.zetaL _ _ _ _ _ _))⁻¹ = _; rw [hz q]; rfl) Φ).trans ?_
    exact (hsc ((MA.DQ P).zbiP) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 4 _ hggv (fun q => by rw [hgg]; exact hGG q) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggP P.TT) (trR P Bs e Φ)).symm
  · rw [hL.2.2.2.2.2.2.2.2.2.2.2.1]
    refine (trR_fn P Bs hpl X e 5 (Ring.inverse (ggS P))
      (fun q => by rw [inverse_apply _ hggv]; exact inv_ne_zero (hggv q))
      (fun q => by rw [inverse_apply _ hggv, hgg]; show ((Q.GGl _ _ _ _ _ : ℝ) : ℂ)⁻¹ = _; rw [hGG q]) Φ).trans ?_
    exact (hsc ((MA.DQ P).ggiP P.TT) (trR P Bs e Φ)).symm

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GT
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGenTransferKAsm
section
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK

noncomputable section

open Formalism.FourierDecayAlt.P.CutMP.Gauge

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

theorem hs_expand (A C : Wq →L[ℂ] Wp) :
    inner ℂ (B.hsVec A) (B.hsVec C) =
      ∑ i, inner ℂ (A (stdOrthonormalBasis ℂ Wq i)) (C (stdOrthonormalBasis ℂ Wq i)) := by
  simp only [B.hsVec, PiLp.inner_apply, PiLp.toLp_apply]

theorem hs_comp_right (A C : Wq →L[ℂ] Wp) (Q : Wq →L[ℂ] Wq) (hQ : ∀ v w, inner ℂ (Q v) w = inner ℂ v (Q w)) :
    inner ℂ (B.hsVec A) (B.hsVec (C.comp Q)) = inner ℂ (B.hsVec (A.comp Q)) (B.hsVec C) := by
  rw [hs_expand, hs_expand]
  set b := stdOrthonormalBasis ℂ Wq
  have hQe : ∀ i, Q (b i) = ∑ j, inner ℂ (b j) (Q (b i)) • b j := fun i => (b.sum_repr' _).symm
  simp only [ContinuousLinearMap.comp_apply]
  conv_lhs => arg 2; ext i; rw [hQe i, map_sum, inner_sum]
  conv_rhs => arg 2; ext j; rw [hQe j, map_sum, sum_inner]
  simp only [map_smul, inner_smul_right, inner_smul_left]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [inner_conj_symm, hQ]

theorem hs_comp_sum {ι : Type} [Fintype ι] (A C : Wq →L[ℂ] Wp) (Q : ι → (Wq →L[ℂ] Wq)) (f : ι → ℂ) :
    inner ℂ (B.hsVec A) (B.hsVec (C.comp (∑ σ, f σ • Q σ))) =
      ∑ σ, f σ * inner ℂ (B.hsVec A) (B.hsVec (C.comp (Q σ))) := by
  simp only [hs_expand, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_smul, inner_sum, inner_smul_right, Finset.mul_sum]
  exact Finset.sum_comm

theorem comp_sum_eq {ι : Type} [Fintype ι] (C : Wq →L[ℂ] Wp) (Q : ι → (Wq →L[ℂ] Wq)) :
    C.comp (∑ σ, Q σ) = ∑ σ, C.comp (Q σ) := by
  ext v
  simp [ContinuousLinearMap.sum_apply, map_sum]

end hs

theorem gauge_kappa_of_point_line : GTKapOfCut := by
  intro hPt hLine Wp Wq _ _ _ _ _ _ P Bs X d hH
  obtain ⟨Qr, hQ⟩ := hPt Wp Wq P Bs X d hH
  have hQQ := hQ.1
  have hQ1 := hQ.2.1
  have hQs := hQ.2.2.1
  have hQk := hQ.2.2.2
  have hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π' := hH.1
  have hcs : CSec P.k P.r Bs.z Bs.z' Bs.μsec := hH.2.2.1
  have hTz : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' = P.TT := by
    rw [hpl.2.2.2.1, hpl.2.2.2.2.1]; rfl

  set ζ0 : ℂ := ((Real.sqrt P.TT + 1 : ℝ) : ℂ) with hζ0def
  have hTT : 0 < P.TT := mul_pos hpl.1.T_pos hpl.1.T'_pos
  have hζ0 : P.TT < Complex.normSq ζ0 := by
    rw [hζ0def, Complex.normSq_ofReal]
    have hs := Real.sq_sqrt hTT.le
    nlinarith [Real.sqrt_nonneg P.TT]

  have hFib : ∀ ζ : ℂ, P.TT < Complex.normSq ζ →
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ = NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro ζ hζ
    have hS : NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ = NF.Stab P.k P.r Bs.z Bs.z' Bs.μsec ζ0 :=
      hcs.2 ζ ζ0 (by rw [hTz]; exact hζ) (by rw [hTz]; exact hζ0)
    unfold NF.Fib
    rw [hS]
  choose E hEF hEQ hE1 hEu using fun ρ => hLine Wp Wq P Bs X d hH Qr hQ ζ0 hζ0 ρ

  have hRB : NF.RadBase P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' :=
    ⟨hpl.1.k_pos, hpl.2.1, hpl.2.2.1, by rw [hpl.2.2.2.1]; exact hpl.1.T_pos,
      by rw [hpl.2.2.2.2.1]; exact hpl.1.T'_pos, Bs.sec, hpl.2.2.2.2.2.1.2.1, hpl.2.2.2.2.2.2.2.1,
      hpl.2.2.2.2.2.1.2.2.1, hpl.2.2.2.2.2.2.2.2.1⟩
  have hcomp : ∀ Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0, ∀ ρ,
      Z.comp (Qr ρ) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by
    intro Z hZ ρ
    let φ : (Fin P.r → ℂ) × ℂ → (Wq →L[ℂ] Wp) := (NF.QR P.k P.r Bs.z Bs.z').indicator fun _ => Z
    have hφ : φ ∈ NF.RadSec P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' := by
      refine ⟨(contDiffOn_const (c := Z)).congr fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
      · simp [φ, Set.indicator_of_mem hx]
      · simp only [φ, Set.indicator_of_mem hx]
        rw [hFib x.2 (by rw [← hTz]; exact hx.2)]; exact hZ
      · simp [φ, Set.indicator_of_notMem hx]
    obtain ⟨Φ, hΦ, hrad⟩ := Formalism.FourierDecayAlt.P.radical_reduction_surjective Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB φ hφ
    let c0 : Fin P.r → ℂ := fun _ => 1
    have hc0 : c0 ∈ OmX P.r := fun _ => one_ne_zero
    have hq0 : ((c0, ζ0) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' := ⟨hc0, by rw [hTz]; exact hζ0⟩
    have hval : Φ c0 (NF.muZ P.k P.r Bs.μsec ζ0) = Z := by
      have h := congrFun hrad (c0, ζ0)
      simp only [NF.radR, Set.indicator_of_mem hq0, φ] at h
      exact h
    let q0 : MA.Qp P.r P.TT := ⟨(c0, ζ0), ⟨hc0, hζ0⟩⟩
    let f : M.Ty P → ℂ := fun σ => if σ = ρ then 1 else 0
    have hk := hQk f ⟨Φ, hΦ⟩ q0
    have hsum : (∑ σ, f σ • Qr σ) = Qr ρ := by
      simp [f, Finset.sum_ite_eq']
    rw [hsum] at hk
    have hmem := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hRB _
      ((d.κ f).1 ⟨Φ, hΦ⟩).2
    have h2 := hmem.2.1 (c0, ζ0) hq0
    simp only [NF.radR, Set.indicator_of_mem hq0] at h2
    have hk' : (((d.κ f).1 ⟨Φ, hΦ⟩ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c0
        (NF.muZ P.k P.r Bs.μsec ζ0) = Z.comp (Qr ρ) := by
      rw [← hval]; exact hk
    rw [hk'] at h2
    exact h2
  refine ⟨fun ρ _ => E ρ, ⟨fun ρ => contDiffOn_const, fun ζ hζ => ⟨fun ρ => ?_, fun ρ ρ' => ?_, fun Z hZ => ?_⟩⟩, ?_⟩
  · rw [hFib ζ hζ]; exact hEF ρ
  · split_ifs with h
    · subst h; exact hE1 ρ
    · calc inner ℂ (B.hsVec (E ρ)) (B.hsVec (E ρ'))
          = inner ℂ (B.hsVec (E ρ)) (B.hsVec ((E ρ').comp (Qr ρ'))) := by rw [hEQ ρ']
        _ = inner ℂ (B.hsVec ((E ρ).comp (Qr ρ'))) (B.hsVec (E ρ')) := hs_comp_right _ _ _ (hQs ρ')
        _ = 0 := by
          have h0 : (E ρ).comp (Qr ρ') = 0 := by
            rw [← hEQ ρ, ContinuousLinearMap.comp_assoc, hQQ ρ ρ', if_neg h, ContinuousLinearMap.comp_zero]
          rw [h0, VLem.hsV_zero, inner_zero_left]
  · have hZ0 : Z ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ0 := by rw [← hFib ζ hζ]; exact hZ
    have hdec : Z = ∑ ρ, Z.comp (Qr ρ) := by
      rw [← comp_sum_eq, hQ1]; rfl
    conv_lhs => rw [hdec]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    have hfix : (Z.comp (Qr ρ)).comp (Qr ρ) = Z.comp (Qr ρ) := by
      rw [ContinuousLinearMap.comp_assoc, hQQ ρ ρ, if_pos rfl]
    rw [hEu ρ _ (hcomp Z hZ0 ρ) hfix, hs_comp_right _ _ _ (hQs ρ), hEQ ρ]
  · intro f Φ
    funext ρ
    have hraw : rawR P Bs.μsec (fun ρ _ => E ρ)
        (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ =
        f ρ • rawR P Bs.μsec (fun ρ _ => E ρ) (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ := by
      funext q
      simp only [rawR, Pi.smul_apply, smul_eq_mul]
      rw [hQk f Φ q, hs_comp_sum]
      have hterm : ∀ σ, f σ * inner ℂ (B.hsVec (E ρ))
          (B.hsVec (((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2)).comp (Qr σ))) =
          if σ = ρ then f ρ * inner ℂ (B.hsVec (E ρ))
            (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2))) else 0 := by
        intro σ
        rw [hs_comp_right _ _ _ (hQs σ)]
        split_ifs with h
        · subst h; rw [hEQ σ]
        · have h0 : (E ρ).comp (Qr σ) = 0 := by
            rw [← hEQ ρ, ContinuousLinearMap.comp_assoc, hQQ ρ σ, if_neg (Ne.symm h), ContinuousLinearMap.comp_zero]
          rw [h0, VLem.hsV_zero, inner_zero_left, mul_zero]
      simp only [hterm, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring
    show MA.toSm P (rawR P Bs.μsec (fun ρ _ => E ρ)
        (((d.κ f).1 Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) ρ) = _
    rw [hraw, VLem.toSm_smul]
    have hkap : MA.kap P (MA.DQ P) f = Matrix.diagonal fun σ => algebraMap ℂ (MA.DQ P).Pr (f σ) := rfl
    rw [hkap, VLem.actA_diag]
    rfl

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.GTK
end

