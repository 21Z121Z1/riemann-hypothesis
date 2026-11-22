import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0068
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0030
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0014
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0036
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0067
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeNC
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0022
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0013
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RealHermitianForms

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarPinCellB
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.MainNotions.FrameBoundFromBesselTorus Formalism.MainNotions.S.Pv.Frames Formalism.L2.S.Pv.AmpNZTie
open Formalism.BasicNotions Formalism.L2.SG.LocWSOf Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.Carrier.CarPinTor

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {k r : ℕ}

theorem isRelStab_of_turn (L : LocBessel k r) (ka : ℝ) (hc : L.c = ((2 * ka : ℝ) : ℂ)) {g : Mx k r}
    (h : IsRelStab (turnL L ka) (tTi k r * g * tT k r)) : IsRelStab L g := by
  have hc' : cOfDpsi (ka : ℂ) * Complex.I = L.c := by rw [hc]; exact turn_c ka
  intro a ha
  have ha' : tTi k r * a * tT k r ∈ RStab k r (tTi k r * g * tT k r) := (conjI_mem_RStab_iff g a).mpr ha
  have e2 : (tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r) =
      tTi k r * (g⁻¹ * a * g) * tT k r := by
    rw [← conjI_inv, ← conjI_mul, ← conjI_mul]
  have := h _ ha'
  change psi k r L.z (cOfDpsi (ka : ℂ)) (tTi k r * a * tT k r) =
    psi k r L.z' (cOfDpsi (ka : ℂ)) ((tTi k r * g * tT k r)⁻¹ * (tTi k r * a * tT k r) * (tTi k r * g * tT k r)) at this
  rw [e2, psi_conjI L.hz.1 hc', psi_conjI L.hz'.1 hc'] at this
  exact this

theorem orbQuot_exists (L : LocBessel k r) {g : Mx k r} (hg : g ∈ UH (Hpk k r)) {μR : Measure (Mt k r)}
    (hμ : IsHaarOn (RStab k r g) μR) : ∃ ν : Measure (PairSp k r), IsOrbQuot L g μR ν := by
  have hν := Formalism.MainNotions.BridgeCSB.haarLieN k r 1 one_ne_zero ENNReal.one_ne_top
  have : SigmaFinite (haarLie (Nset k r) 1) := hν.1
  have hs := PI.AmpOrbQuot.muN_smul L
  have : SFinite L.μN := by rw [hs]; infer_instance
  have hN : ∀ s ∈ Nset k r, L.μN.map (lmulM s) = L.μN := by
    intro s hs'
    rw [hs, Measure.map_smul, hν.2.2.2 s hs']
  have hc : L.μN (PI.AmpOrbQuot.NS k r)ᶜ = 0 := by
    rw [hs, Measure.smul_apply, smul_eq_mul]
    have : haarLie (Nset k r) 1 (PI.AmpOrbQuot.NS k r)ᶜ = 0 := hν.2.2.1
    rw [this, mul_zero]
  exact PI.AmpOrbQuot.exists_isOrbQuot_of_isHaarOn L g μR hg hμ hN hc

end Gen

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {θ : ℝ} (C : Choice X θ) (hB : WuBessel C)

theorem trHyp_C (u : D.what₂.Word) (τ : D.what₂.Tau) :
    Formalism.L2.SG.Pf.Bridge.TrHyp (Formalism.L2.SG.RealObj.InfCut.PtRepPf.frU X u (vOf X τ)) (C.Q τ) (C.Qi τ)
      (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) :=
  ⟨(C.isT τ).1, (C.isT τ).2.1, (C.isT τ).2.2.1, fun a => ((C.isT τ).2.2.2 a a rfl).1,
    fun a => ((C.isT τ).2.2.2 a a rfl).2⟩

theorem gB_mem (u : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    gB C τ γ ∈ UH (Hpk D.R.k D.R.rS) :=
  Formalism.L2.SG.Pf.Bridge.delta_GV (trHyp_C C u τ) (Formalism.L2.SG.Pf.Carrier.uMat_unitary γ)

theorem relStab_of_relevant (u u' : D.what₂.Word) (τ : D.what₂.Tau)
    (hW : GoodW D τ u u' θ (locW C u u' τ)) (hA : GoodS D (lamD D τ) (locS hB u u' τ))
    (hT : 0 < Tr D u) (hT' : 0 < Tr D u') (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : Formalism.FourierDecayAlt.C6.IsRelevant (baseOf X C u u' (vOf X τ)) (trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ)) :
    IsRelStab (toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT') (gB C τ γ) := by
  set L := toBessel D τ u u' θ (locW C u u' τ) (lamD D τ) (locS hB u u' τ) hW hA hT hT' with hL
  have hκ : (0 : ℝ) < (kaB D)⁻¹ := inv_pos.mpr (kaB_pos D)
  have hc : L.c = ((2 * kaB D : ℝ) : ℂ) := by
    show ((2 * D.host.ka / ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) : ℝ) : ℂ) = _
    unfold kaB; congr 1; ring
  apply isRelStab_of_turn L (kaB D) hc
  rw [← isRelStab_iff hκ one_pos (turnL L (kaB D)) (stdL L (kaB D) (kaB_pos D)) L.hz.1 L.hz'.1 rfl rfl rfl]
  have hz : (baseOf X C u u' (vOf X τ)).z = (stdL L (kaB D) (kaB_pos D)).z := zc_vOf_eq_zB_of_inWb C u u' τ L.hz.1
  have hz' : (baseOf X C u u' (vOf X τ)).z' = (stdL L (kaB D) (kaB_pos D)).z' := zc_vOf_eq_zB_of_inWb C u' u τ L.hz'.1
  have hcs : (stdL L (kaB D) (kaB_pos D)).c = cStd := stdL_c L (kaB D) (kaB_pos D)
  show IsRelStab (stdL L (kaB D) (kaB_pos D)) (gStd (kaB D) (gB C τ γ))
  have hγ : gStd (kaB D) (gB C τ γ) = trG (Qc X C (vOf X τ)) (Qic X C (vOf X τ)) γ := gStd_eq C τ γ
  intro a ha
  rw [hγ] at ha ⊢
  have h2 := h.2 a ha
  rw [hz, hz'] at h2
  show psi D.R.k D.R.rS (stdL L (kaB D) (kaB_pos D)).z (stdL L (kaB D) (kaB_pos D)).c a =
    psi D.R.k D.R.rS (stdL L (kaB D) (kaB_pos D)).z' (stdL L (kaB D) (kaB_pos D)).c _
  rw [hcs]
  exact h2

section Scale

theorem det_sub_diag {m n : ℕ} (s l : Fin m → ℂ) (Z : Matrix (Fin m) (Fin m) ℂ) (h : n ≤ m) :
    ((Matrix.diagonal s * Z * Matrix.diagonal l).submatrix (Fin.castLE h) (Fin.castLE h)).det =
      (∏ i : Fin n, s (Fin.castLE h i) * l (Fin.castLE h i)) * (Z.submatrix (Fin.castLE h) (Fin.castLE h)).det := by
  have e : (Matrix.diagonal s * Z * Matrix.diagonal l).submatrix (Fin.castLE h) (Fin.castLE h) =
      Matrix.diagonal (s ∘ Fin.castLE h) * Z.submatrix (Fin.castLE h) (Fin.castLE h) *
        Matrix.diagonal (l ∘ Fin.castLE h) := by
    ext i j; simp [Matrix.diagonal_mul, Matrix.mul_diagonal]
  rw [e, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, Finset.prod_mul_distrib]
  simp only [Function.comp]
  ring

theorem mono_scale {m : ℕ} {Z : Matrix (Fin m) (Fin m) ℂ} (hZ : Formalism.FourierDecayAlt.C2.IsMonomial Z) {s l : Fin m → ℂ}
    (hs : ∀ i, s i ≠ 0) (hl : ∀ i, l i ≠ 0) :
    Formalism.FourierDecayAlt.C2.IsMonomial (Matrix.diagonal s * Z * Matrix.diagonal l) := by
  obtain ⟨w, d, hd, rfl⟩ := hZ
  refine ⟨w, fun a => s (w a) * d a * l a, fun a => mul_ne_zero (mul_ne_zero (hs _) (hd a)) (hl a), ?_⟩
  ext i a
  simp only [Formalism.FourierDecayAlt.C2.monoP, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply]
  split_ifs with h
  · rw [h]
  · simp

end Scale

theorem zhat_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ) =
      Matrix.diagonal (fun a => star (Formalism.L2.SG.Pf.Bridge.lam (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) 1 a)) *
        Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ) *
        Matrix.diagonal (Formalism.L2.SG.Pf.Bridge.lam (fun a : Fin D.R.rS => frS D ^ (D.R.rS - (a : ℕ))) 1) :=
  Formalism.L2.SG.Pf.Bridge.zhat_cs (trHyp_C C u τ) (trHyp_C C u' τ) one_ne_zero (uMat γ)

theorem mono_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : Formalism.FourierDecayAlt.C2.IsMonomial (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ))) :
    Formalism.FourierDecayAlt.C2.IsMonomial (Formalism.QuantumDeterminants.Zhat D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ)) := by
  rw [zhat_B C u u' τ γ]
  exact mono_scale h (fun i => star_ne_zero.mpr (Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_C C u τ) one_ne_zero i))
    (fun i => Formalism.L2.SG.Pf.Bridge.lam_ne (trHyp_C C u τ) one_ne_zero i)

section GfTr

open Formalism.L2.SG.RealObj.InfCut

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F F' : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem gf_pos_tr (hT : Formalism.L2.SG.Pf.Bridge.TrHyp F Qm Qim c) (hT' : Formalism.L2.SG.Pf.Bridge.TrHyp F' Qm Qim c)
    (A : Matrix (Fin n) (Fin n) ℂ)
    (h : 0 < Gv F.T F'.T (Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A)) :
    0 < Formalism.QuantumDeterminants.Gf k r (Qim *ᵥ F.z) (Qim *ᵥ F'.z) (Qim * A * Qm) := by
  have hz := Formalism.L2.SG.Pf.Bridge.zhat_cs hT hT' one_ne_zero A
  unfold Formalism.QuantumDeterminants.Gf Formalism.QuantumDeterminants.Dmin
  rw [hz, det_sub_diag, det_sub_diag, Formalism.L2.SG.Pf.Bridge.tz_Qi' hT, Formalism.L2.SG.Pf.Bridge.tz_Qi' hT']
  have hsq : ∀ x : ℂ, star x * x = ((Complex.normSq x : ℝ) : ℂ) := fun x => by
    rw [Complex.normSq_eq_conj_mul_self, Complex.star_def]
  simp only [hsq, ← Complex.ofReal_prod, Complex.normSq_mul, Complex.normSq_ofReal]
  have hp : (∏ x : Fin ((Fin.last (r + 1) : Fin (r + 2)) : ℕ),
      Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_of_lt_succ (Fin.last (r + 1)).isLt) x))) =
        ∏ x : Fin ((⟨r, by omega⟩ : Fin (r + 2)) : ℕ), Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1
          (Fin.castLE (Nat.le_of_lt_succ (⟨r, by omega⟩ : Fin (r + 2)).isLt) x)) := by
    show (∏ x : Fin (r + 1), Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (le_refl (r + 1)) x))) =
      ∏ x : Fin r, Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_succ r) x))
    rw [Fin.prod_univ_castSucc]
    have e1 : Fin.castLE (le_refl (r + 1)) (Fin.last r) = Fin.last r := Fin.ext rfl
    rw [e1, Formalism.L2.SG.Pf.Bridge.lam_last, map_one, mul_one]
    rfl
  rw [hp]
  set Λ : ℝ := ∏ x : Fin r, Complex.normSq (Formalism.L2.SG.Pf.Bridge.lam c 1 (Fin.castLE (Nat.le_of_lt_succ
    (⟨r, by omega⟩ : Fin (r + 2)).isLt) x)) with hΛ
  have hΛpos : 0 < Λ := Finset.prod_pos fun i _ => Complex.normSq_pos.mpr
    (Formalism.L2.SG.Pf.Bridge.lam_ne hT one_ne_zero _)
  unfold Gv Formalism.L2.SG.RealObj.Dl at h
  rw [dif_pos le_rfl, dif_pos (Nat.le_succ r)] at h
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq] at h
  have hΛ2 : 0 < Λ * Λ := mul_pos hΛpos hΛpos
  have key := mul_pos hΛ2 h
  show 0 < Λ * Λ * Complex.normSq ((Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A).submatrix
      (Fin.castLE (le_refl (r + 1))) (Fin.castLE (le_refl (r + 1)))).det -
    F.T * F'.T * (Λ * Λ * Complex.normSq ((Zhat ε (famSc 1 F.e F.z) (famSc 1 F'.e F'.z) A).submatrix
      (Fin.castLE (Nat.le_succ r)) (Fin.castLE (Nat.le_succ r))).det)
  linarith [key]

end GfTr

theorem gf_B (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (h : 0 < Gv (Tw (D := D) u) (Tw (D := D) u')
      (Zhat (X.B.I.ε (vOf X τ)) (frm X u 1 (vOf X τ)) (frm X u' 1 (vOf X τ)) (uMat γ))) :
    0 < Formalism.QuantumDeterminants.Gf D.R.k D.R.rS (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u' τ) (gB C τ γ) :=
  gf_pos_tr (trHyp_C C u τ) (trHyp_C C u' τ) (uMat γ) h

end Formalism.L2.SG.Pf.Carrier.CarPinTor
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierTPinWrap
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped Matrix

namespace Formalism.L2.SG.Pf.CarrierT

open Formalism.L2.SG.Pf.Carrier Formalism.L2.SG.Pf.BaseOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {θ : ℝ} (C : Choice X θ)

theorem pinCovE_carrierInTc (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀)))
    (Hj : ∀ j : Fin (nfE D), ∃ lam : ℂ, lam ≠ 0 ∧
      ∀ (γ : Formalism.REAL.UJ (X.B.I.ε (tauE X e j))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (tauE X e j)))),
        Formalism.L2.SG.Pf.Carrier.JointPin.PinHyp
          (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo)
          (tauE X e j) γ μRv ν →
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (tauE X e j));
          Jv ν (X.Wloc u (tauE X e j)) (X.Wloc u' (tauE X e j)) γ) =
          lam • Formalism.FourierDecayAlt.D.orbJ (baseOf X C u u' (tauE X e j)) (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ)
            (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) x)))
            (Formalism.L2.SG.Pf.Carrier.CarPinTor.fcAt C u u' (e (plE D j)) (a j) (b j) (ξ j) (ξ' j) (cc j))) :
    Formalism.L2.SG.Pf.Carrier.CarPin.PinCovE
      (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo) := by
  choose lam hlam hJ using Hj
  refine ⟨fun v => lam ((tauE X e).symm v), fun v => hlam _, ?_⟩
  intro v γ μRv ν hH
  obtain ⟨j, rfl⟩ := (tauE X e).surjective v
  have key : ∀ (j' : Fin (nfE D)) (h' : X.pl.symm (e (plE D j')) = tauE X e j),
      (haveI := FiniteDimensional.complete ℂ (X.Vloc u (tauE X e j));
        Jv ν (X.Wloc u (tauE X e j)) (X.Wloc u' (tauE X e j)) γ) =
        lam j' • ((castLoc X u h').toContinuousLinearEquiv.toContinuousLinearMap :
            X.Vloc u (tauE X e j') →L[ℂ] X.Vloc u (tauE X e j)).comp
          ((Formalism.FourierDecayAlt.D.orbJ (towersOf X C u u' e j').base (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ)
              (μRv.map (fun x => Matrix.of.symm (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) x)))
              (fcT X C e u u' a b ξ ξ' cc j')).comp
            ((castLoc X u' h').symm.toContinuousLinearEquiv.toContinuousLinearMap :
              X.Vloc u' (tauE X e j) →L[ℂ] X.Vloc u' (tauE X e j'))) := by
    intro j' h'
    have hj : j' = j := (tauE X e).injective h'
    subst hj
    rw [towersOf_base, hJ j' γ μRv ν hH]
    ext x
    rfl
  exact key _ (tauE_symm X e (tauE X e j))

theorem pinHyp_at (u u' : D.what₂.Word) (e : InfinitePlace D.host.E ≃ D.what₂.Tau) (he : PlaceTie X e)
    (hv : D.host.v = Formalism.FourierDecayAlt.S6.rd D.host.E / 2) (CA : ℝ) (de de' : ℕ → ℝ) (l : ℕ)
    (grid : Fin (nfE D) → ℕ → Finset ℝ) (grid1 : Fin (nfE D) → Finset ℝ)
    (a b : ∀ j : Fin (nfE D), X.B.H (tauE X e j)) (ξ : ∀ j : Fin (nfE D), X.Vloc u (tauE X e j))
    (ξ' : ∀ j : Fin (nfE D), X.Vloc u' (tauE X e j)) (cc : Fin (nfE D) → ℂ)
    (c : Formalism.FourierDecayAlt.LE.Cut) (ν' : Fin (nfE D) → Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (m₀ : Fin (nfE D) → Formalism.FourierDecayAlt.B.Mat D.R.k D.R.rS)
    (Θ : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TopLift D.R.k D.R.rS (X.Vloc u (tauE X e j)) (X.Vloc u' (tauE X e j)))
    (TP : ∀ j : Fin (nfE D), Formalism.FourierDecayAlt.Top.TypeProj (parE e u u' de de' j) (towersOf X C u u' e j).base.π
      (towersOf X C u u' e j).base.z (m₀ j *ᵥ ν' j)) (A₀ : ℝ)
    (Mo : ModelsFor (sOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀)))
    (j : Fin (nfE D)) (γ : Formalism.REAL.UJ (X.B.I.ε (tauE X e j))) (μRv ν : Measure (Formalism.REAL.UJ (X.B.I.ε (tauE X e j))))
    (hH : Formalism.L2.SG.Pf.Carrier.JointPin.PinHyp
      (CarrierOf (carrierInTc X C u u' e he hv CA de de' l grid grid1 a b ξ ξ' cc c ν' m₀ Θ TP A₀) Mo)
      (tauE X e j) γ μRv ν) :
    Formalism.L2.SG.Pf.Carrier.CarPinTor.PinHypAt C u u' (e (plE D j)) γ μRv ν := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hH
  refine ⟨h1, h2, ?_, h4, h5⟩
  have key : ∀ j' : Fin (nfE D), j' = (tauE X e).symm (tauE X e j) →
      Formalism.FourierDecayAlt.C6.IsRelevant (towersOf X C u u' e j').base (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ) →
      Formalism.FourierDecayAlt.C6.IsRelevant (baseOf X C u u' (tauE X e j)) (trG (Qc X C (tauE X e j)) (Qic X C (tauE X e j)) γ) := by
    intro j' hj' h
    rw [Equiv.symm_apply_apply] at hj'
    subst hj'
    rw [towersOf_base] at h
    exact h
  exact key _ rfl h3

end Formalism.L2.SG.Pf.CarrierT
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EPerpMid
section
noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj.InfCut

section Fwd

variable {n : ℕ} {ε : Fin n → Bool} {r k : ℕ} {F : PtRepPf.Fr ε r k}
  {Qm : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ} {Qim : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ} {c : Fin r → ℂ}

theorem Qi_spanLt (hT : TrHyp F Qm Qim c) {a : ℕ} {v : Fin n → ℂ} (hv : v ∈ spanLt F.e a) :
    ∀ i : Fin (2 * r + k + 1), a ≤ i.val → (Qim *ᵥ v) i = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, hb, rfl⟩ := hx
    intro i hi
    rw [Qi_e hT b]
    have hne : i ≠ Formalism.QuantumDeterminants.eI k r b := fun h => by
      have := congrArg Fin.val h; simp only [Formalism.QuantumDeterminants.eI] at this; simp only [Set.mem_setOf_eq] at hb; omega
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply, hne]
  | zero => intro i _; simp
  | add x y _ _ hx hy => intro i hi; rw [Matrix.mulVec_add, Pi.add_apply, hx i hi, hy i hi, add_zero]
  | smul d x _ hx => intro i hi; rw [Matrix.mulVec_smul, Pi.smul_apply, hx i hi, smul_zero]

theorem e_perp_mid (hT : TrHyp F Qm Qim c) (a : Fin r) (j : Fin (2 * r + k + 1)) (hj1 : r ≤ j.val)
    (hj2 : j.val ≤ r + k) : hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := by
  have he : F.e a = (c a)⁻¹ • (Qm *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r a)) := by
    rw [hT.he, smul_smul, inv_mul_cancel₀ (c_ne hT a), one_smul]
  rw [he, PtRepPf.hJ_smul_left, ← herm_Q hT, Formalism.L2.SG.Pf.CarrierBase.herm_bvec]
  have h0 : (Formalism.QuantumDeterminants.Hpk k r *ᵥ Formalism.QuantumDeterminants.bvec j) (Formalism.QuantumDeterminants.eI k r a) = 0 := by
    simp only [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one, Matrix.col_apply]
    unfold Formalism.QuantumDeterminants.Hpk
    have ha := a.2
    have hv : (Formalism.QuantumDeterminants.eI k r a).val = a.val := rfl
    rw [if_neg (fun h => by have h' := h.2; rw [hv] at h'; omega),
      if_neg (fun h => by have h' := h.1; omega),
      if_neg (fun h => by have h' := h.1; rw [hv] at h'; omega)]
  rw [h0, mul_zero]

theorem fwd_N (hT : TrHyp F Qm Qim c) {g : Matrix (Fin n) (Fin n) ℂ} {z : Fin n → ℂ}
    (hgU : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε) (hg : InN ε F.e z g) :
    Qim * g * Qm ∈ Formalism.QuantumDeterminants.Nset k r := by
  have hQQ : Qimᴴ * Qmᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hT.h2, Matrix.conjTranspose_one]
  have hcol : ∀ (j i : Fin (2 * r + k + 1)), (Qim * g * Qm) i j = (Qim *ᵥ (g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j))) i := by
    intro j i
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Matrix.mulVec_single_one]
  refine ⟨?_, fun a i hi => ?_, fun i j hj1 hj2 hi => ?_⟩
  · show (Qim * g * Qm)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qim * g * Qm) = Formalism.QuantumDeterminants.Hpk k r
    rw [← hT.hH]
    calc (Qim * g * Qm)ᴴ * (Qmᴴ * Formalism.REAL.Jm ε * Qm) * (Qim * g * Qm)
        = Qmᴴ * gᴴ * (Qimᴴ * Qmᴴ) * Formalism.REAL.Jm ε * (Qm * Qim) * g * Qm := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Qmᴴ * (gᴴ * Formalism.REAL.Jm ε * g) * Qm := by
          rw [hQQ, hT.h2]; simp only [Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by rw [hgU]
  · rw [hcol, hT.he, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply]
    have hsplit : g *ᵥ F.e a = F.e a + (g - 1) *ᵥ F.e a := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.1.1 a) i hi, add_zero, Qi_e hT a,
      Pi.smul_apply, smul_smul, mul_inv_cancel₀ (c_ne hT a), one_smul]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]
  · rw [hcol]
    have hw : ∀ a, hJ ε (F.e a) (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = 0 := fun a => e_perp_mid hT a j hj1 hj2
    have hsplit : g *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) = Qm *ᵥ Formalism.QuantumDeterminants.bvec j + (g - 1) *ᵥ (Qm *ᵥ Formalism.QuantumDeterminants.bvec j) := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
    rw [hsplit, Matrix.mulVec_add, Pi.add_apply, Qi_spanLt hT (hg.2 _ hw) i hi, add_zero, Matrix.mulVec_mulVec,
      hT.h1, Matrix.one_mulVec]
    simp [Formalism.QuantumDeterminants.bvec, Pi.single_apply]

end Fwd

end Formalism.L2.SG.Pf.Bridge
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalDoubleCoset
section
noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.TermTieOf Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.LocalDoubleCoset

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Move {k r : ℕ} (z z' : Fin (2 * r + k + 1) → ℂ) (γ γ' : Formalism.MainNotions.S.MatKR k r) : Prop :=
  ∃ n ∈ Formalism.QuantumDeterminants.Nset k r, ∃ s ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ s' ∈ Formalism.QuantumDeterminants.UWset k r z', ∃ n' ∈ Formalism.QuantumDeterminants.Nset k r,
    γ' = (s * n) * γ * (n' * s')

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (hB : WuBessel C) (u u' : D.what₂.Word)

def JMove : Prop :=
  ∀ (τ : D.what₂.Tau) (γ γ' : Formalism.MainNotions.S.MatKR D.R.k D.R.rS) (ν ν' : Measure (Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)),
    Move (locW C u u' τ).z (locW C u u' τ).z' γ γ' → (∃ p, RelPt D (locW C u u' τ).z (locW C u u' τ).z' γ p) →
    RMeas D (locW C u u' τ) γ 1 ν → RMeas D (locW C u u' τ) γ' 1 ν' →
    hsNormSq ((locS hB u u' τ).J ν' γ') = hsNormSq ((locS hB u u' τ).J ν γ)

def DecR : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    Move (locW C u u' τ).z (locW C u u' τ).z'
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' (Formalism.L2.SG.Pf.AmpWinJF.wt hI t) τ) (Formalism.L2.SG.LoopTerm.gamR hI C t τ) ∧
    ∃ p, RelPt D (locW C u u' τ).z (locW C u u' τ).z'
      (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' (Formalism.L2.SG.Pf.AmpWinJF.wt hI t) τ) p

def RMeasExT : Prop :=
  ∀ t : D.s.Term u u', D.s.Gterm t ≠ 0 → D.s.relevant t → ∀ τ,
    ∃ ν, RMeas D (locW C u u' τ) (Formalism.L2.SG.Pf.JointAmplitudePoints.gamP C u u' (Formalism.L2.SG.Pf.AmpWinJF.wt hI t) τ) 1 ν

end Formalism.L2.SG.Pf.LocalDoubleCoset
end
end

