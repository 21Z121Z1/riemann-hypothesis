import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0011
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0023
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataConc
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.InfCut
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuBesselLoc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0021
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0013
import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0017

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeVIndep
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier

open Formalism.L2.SG.RealObj Formalism.L2.SG.DataInst

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

theorem signFlip_involutive {K : Type} [Ring K] (r : ℕ) : ∀ (b : ℕ) (x : Formalism.FourierDecayAlt.TB.Pt K),
    signAux r b (signAux r b x) = x
  | _, [] => rfl
  | b, (s, t) :: rest => by
    simp only [signAux, signFlip_involutive r (b + s) rest, List.cons.injEq, Prod.mk.injEq, true_and, and_true]
    rw [← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

variable {D : D7}

theorem exists_pt (w : Point D.host.E (D.R.rS + 1)) :
    ∃ p : Formalism.FourierDecayAlt.TB.Pt D.host.E, ptOfL (D := D) (D.R.rS + 1) p = some w := by
  set y := Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1) w with hy
  have hinv : Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.SG.DataInst.signPt D.R.rS y.1) = y.1 :=
    signFlip_involutive _ _ _
  refine ⟨Formalism.L2.SG.DataInst.signPt D.R.rS y.1, ?_⟩
  have hcond : Formalism.L2.S.IsPtL
      (Formalism.L2.SG.DataInst.signPt D.R.rS (Formalism.L2.SG.DataInst.signPt D.R.rS y.1)) (D.R.rS + 1) := by
    rw [hinv]
    exact y.2
  unfold ptOfL Formalism.L2.SG.DataInst.ptOfList
  rw [dif_pos hcond]
  congr 1
  apply (Formalism.L2.S.ptEquiv D.host.E (D.R.rS + 1)).symm_apply_eq.mpr
  exact Subtype.ext hinv

variable (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)

def VIndepAt (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) :
    Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h₁ h₁' h₂ h₂', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₁ h₁' →
      IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h₂ h₂' →
      (X.piU u h₁⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₁')) =
        (X.piU u h₂⁻¹).comp ((haveI := FiniteDimensional.complete ℂ (X.Vpi u)
          Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w)).comp
          (X.piU u' h₂'))

theorem vIndepAt_of {X} {u u'} (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (hJT : P.JointTensor sc i0 i0' νq) : VIndepAt X u u' sc i0 i0' νq := by
  intro w hw hG h₁ h₁' h₂ h₂' hd₁ hd₂
  obtain ⟨p, hp⟩ := exists_pt (D := D) w
  apply ContinuousLinearMap.coe_injective
  refine LinearMap.ext_on_range (X.tensU_span u') fun x => ?_
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  rw [hJT p w hp hw hG h₁ h₁' hd₁ x, hJT p w hp hw hG h₂ h₂' hd₂ x]

end Formalism.L2.SG.Pf.Carrier
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierEnergyPf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal

namespace Formalism.L2.SG.Pf.Carrier.EnergyPf

open Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.EnergyCut Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def IntNX (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ) : ℝ :=
  (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ /
            (((Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p) *
              (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP) *
    ((Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP * (IntC X u u' 1 / Formalism.L2.SG.MassDataConc.kapN D))

def LocRep (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word)
    (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ) : Prop :=
  (∀ v, Measurable (L v) ∧ ∀ cv, 0 ≤ L v cv) ∧
    ∀ c ∈ Good X u u', ∀ v, hs2 (JvX X u u' v ((hOf X u u' 1 c) v)) = L v (c v)

def PlaceEnergy (P : Parts X u u') (L : InfinitePlace X.B.I.F → (Fin (D.R.rS + 1) → ℂ) → ℝ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  ∀ v, Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v)) ≠ ⊤ ∧
    ∫⁻ cv in GoodV u u', ENNReal.ofReal (wtV u u' cv * L v cv) ∂(dcV (D := D)) =
      ENNReal.ofReal (K v * (Formalism.FourierDecayAlt.B.normSq (P.T (P.τ.symm v)).base (P.f (P.τ.symm v))).toReal)

def ConstPin (P : Parts X u u') (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    (K : InfinitePlace X.B.I.F → ℝ) : Prop :=
  (∀ v, 0 ≤ K v) ∧
    (Formalism.L2.SG.LocVol.locOf X u u' ψ).volZZ /
              (((Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeArchimedean * ∏ p, (Formalism.L2.SG.LocVol.locOf X u u' ψ).localVolumeAtPlace p) *
                (Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP) *
      ((Formalism.L2.SG.LocVol.locOf X u u' ψ).volPP * ((∏ v, K v) / Formalism.L2.SG.MassDataConc.kapN D)) =
      (P.Gam0 ^ P.S.f)⁻¹

end Formalism.L2.SG.Pf.Carrier.EnergyPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.CarrierJointPf
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S

namespace Formalism.L2.SG.Pf.Carrier.JointPf

open Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.Carrier

attribute [local instance] Formalism.BasicNotions.Host.cmStar instCM

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}

def OOQuot (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u u' : D.what₂.Word) (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ w : Point D.host.E (D.R.rS + 1), (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) → ∀ y : ∀ v, X.Vloc u' v,
      (haveI := FiniteDimensional.complete ℂ (X.Vpi u);
        Formalism.L2.SG.TermOp.OO (νq (gamW X u u' w)) Set.univ (X.Wu u) (X.Wu u') (gamW X u u' w))
          (X.tensU u' y) =
      X.tensU u (fun v => (haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
        Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v)) (y v))

def PlaceJ (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v))) : Prop :=
  ∀ (p : Formalism.FourierDecayAlt.TB.Pt D.host.E) (w : Point D.host.E (D.R.rS + 1)),
    ptOfL (D := D) (D.R.rS + 1) p = some w → (∃ γ, IsPtRep X u u' w γ) →
    (∀ v, 0 < GX X u u' D.host.rdE (gamW X u u' w) v) →
    ∀ h h', IsDFrameX X u u' sc i0 i0' (gamW X u u' w) h h' →
    ∀ (v : InfinitePlace X.B.I.F) (y : X.Vloc u' v),
      X.piLoc u v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u v) v h⁻¹)
        ((haveI := FiniteDimensional.complete ℂ (X.Vloc u v);
          Jv (νl w v) (X.Wloc u v) (X.Wloc u' v) ((gamW X u u' w) v))
          (X.piLoc u' v (Formalism.L2.SG.HidaSetting.matW X.B.I (X.wfr u' v) v h') y)) =
      P.eP v
        (((((Formalism.FourierDecayAlt.D.bSt (Formalism.FourierDecayAlt.D.kapG (P.S.g : ℝ) (Formalism.FourierDecayAlt.S6.rd D.host.E))
            (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p))⁻¹ : ℝ) : ℂ) •
          Formalism.FourierDecayAlt.D.vecV (P.T (P.τ.symm v)).base (P.ν' (P.τ.symm v)) (P.m₀ (P.τ.symm v)) (P.f (P.τ.symm v))
            (Formalism.FourierDecayAlt.D.toStd P.S.G.r P.S.g 1 (Formalism.FourierDecayAlt.C.loc (P.S.emb (P.τ.symm v)) p)))
          ((P.eQ v).symm y))

theorem jointTensor_of_steps (P : Parts X u u') (sc : ℝ) (i0 i0' : ∀ _ : InfinitePlace X.B.I.F, Fin D.R.k)
    (νq : X.B.I.Ginf → Measure X.B.I.Ginf)
    (νl : Point D.host.E (D.R.rS + 1) → ∀ v : InfinitePlace X.B.I.F, Measure (Formalism.REAL.UJ (X.B.I.ε v)))
    (hQ : OOQuot X u u' νq νl) (hP : PlaceJ P sc i0 i0' νl) : P.JointTensor sc i0 i0' νq := by
  unfold Formalism.L2.SG.Pf.Carrier.Parts.JointTensor
  intro p w hpw hγ hG h h' hF x
  rw [X.tensU_equiv, hQ w hγ hG, X.tensU_equiv]
  · exact congrArg (fun f => X.tensU u f) (funext fun v => hP p w hpw hγ hG h h' hF v (x v))
  all_goals
    first
    | exact hF.2.1
    | (intro v y hy
       have h1 := hF.1 v y hy
       nth_rewrite 1 [← h1]
       rw [Matrix.mulVec_mulVec, Pi.inv_apply]
       simp only [uMat]
       rw [← Units.val_mul, ← MulMemClass.coe_mul, inv_mul_cancel, OneMemClass.coe_one, Units.val_one,
         Matrix.one_mulVec])

end Formalism.L2.SG.Pf.Carrier.JointPf
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.L2RightTranslationThm
section
noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace Formalism.L2.SG.Pf.WuBL

theorem l2RightTranslation_thm : L2RightTranslation := by
  classical
  intro k r z hz hT μG μS ν hG hS hq Vp _ W hWc hW0 hWS y hy
  obtain ⟨hGg, hSg, hSG, hRG, hRS⟩ := quotient_measure_unitary_group k r z hz hT
  have hset : PI.QuotientSetting (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) (Formalism.QuantumDeterminants.Sset k r z) μG μS ν :=
    ⟨hGg, hSg, hSG, hG, hS, hRG μG hG, hRS μS hS, hq⟩
  let G : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)}
  have hGc : IsClosed G := hGg.1.preimage continuous_id
  let F : Formalism.QuantumDeterminants.Mt k r → ℝ≥0∞ := fun x => ((‖W (Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2
  have hFG : F = G.piecewise F (fun _ => 0) := by
    funext x
    by_cases hx : x ∈ G
    · simp [Set.piecewise, hx]
    · simp [Set.piecewise, hx, F, hW0 (Matrix.of x) hx]
  have hcont : ContinuousOn F G := by
    have hW' : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => W (Matrix.of x)) G :=
      hWc.comp continuous_id.continuousOn (fun x hx => hx)
    exact (ENNReal.continuous_pow 2).comp_continuousOn (ENNReal.continuous_coe.comp_continuousOn hW'.nnnorm)
  have hmeas : Measurable F := by
    rw [hFG]
    exact hcont.measurable_piecewise continuousOn_const hGc.measurableSet
  have hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x : Formalism.QuantumDeterminants.Mt k r,
      Matrix.of x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) →
      F (fun i j => (s * Matrix.of x) i j) = F x := by
    intro s hs x hx
    have h2 : ‖W (s * Matrix.of x)‖₊ = ‖W (Matrix.of x)‖₊ := NNReal.eq (hWS s hs (Matrix.of x) hx)
    change ((‖W (s * Matrix.of x)‖₊ : ℝ≥0∞)) ^ 2 = _
    rw [h2]
  exact quotient_invariant (2 * r + k + 1) _ _ μG μS ν hset F hmeas hinv y hy

end Formalism.L2.SG.Pf.WuBL
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocJEqMeas
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.RealObj

namespace Formalism.L2.SG.Pf.LocJEq

variable {D : D7} {X : HidaSetting D} {θ : ℝ} (C : Choice X θ)

private theorem isUnit_y_det (τ : D.what₂.Tau) : IsUnit (C.y τ).det := by
  obtain ⟨hQiQ, hQQi, hH, -⟩ := C.isT τ
  have hJJ : Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) * Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) = 1 := by
    rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> norm_num
  generalize Formalism.REAL.Jm (X.B.I.ε (vOf X τ)) = J at hH hJJ
  have hHinv : (C.Qi τ * J * (C.Qi τ)ᴴ) * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS = 1 := by
    rw [← hH]
    calc C.Qi τ * J * (C.Qi τ)ᴴ * ((C.Q τ)ᴴ * J * C.Q τ)
        = C.Qi τ * J * (C.Q τ * C.Qi τ)ᴴ * J * C.Q τ := by
          rw [Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = 1 := by
          rw [hQQi, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.mul_assoc (C.Qi τ), hJJ, Matrix.mul_one, hQiQ]
  have hy' : (C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * C.y τ = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS := C.y_mem τ
  have h1 : (C.Qi τ * J * (C.Qi τ)ᴴ * ((C.y τ)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) * C.y τ = 1 := by
    rw [Matrix.mul_assoc, hy', hHinv]
  exact Matrix.isUnit_det_of_left_inverse h1

private theorem conj_lemma_2 (τ : D.what₂.Tau) (w : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) :
    C.Q τ * (C.Qi τ * w * C.Q τ * (C.y τ)⁻¹) * C.y τ * C.Qi τ = w := by
  obtain ⟨hQiQ, hQQi, -, -⟩ := C.isT τ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQQi, Matrix.one_mul, ← Matrix.mul_assoc (C.y τ)⁻¹ (C.y τ),
    Matrix.nonsing_inv_mul _ (isUnit_y_det C τ), Matrix.one_mul, hQQi, Matrix.mul_one]

private theorem Qi_mul_Q_conj_mul_y_inv_eq (τ : D.what₂.Tau) (x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    C.Qi τ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) * C.Q τ * (C.y τ)⁻¹ = Matrix.of x := by
  obtain ⟨hQiQ, hQQi, -, -⟩ := C.isT τ
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Qi τ) (C.Q τ), hQiQ, Matrix.one_mul, ← Matrix.mul_assoc (C.Qi τ) (C.Q τ), hQiQ,
    Matrix.one_mul, Matrix.mul_nonsing_inv _ (isUnit_y_det C τ), Matrix.mul_one]

theorem mem_of_range (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (x : Set.range (Smap C τ γ)) :
    umat γ * (C.Q τ * Matrix.of x.1 * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ)) := by
  obtain ⟨z, hz⟩ := x.2
  rw [← hz]
  unfold Smap
  simp only [Equiv.apply_symm_apply]
  rw [conj_lemma_2 C τ]
  unfold umat UJset
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.mul_inv_cancel_left]
  exact z.2

def smapInv (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) (x : Set.range (Smap C τ γ)) :
    Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) :=
  ujOf' (umat γ * (C.Q τ * Matrix.of x.1 * C.y τ * C.Qi τ)) (mem_of_range C τ γ x)

theorem smapInv_cont (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : Continuous (smapInv C τ γ) := by
  unfold smapInv ujOf'
  apply Continuous.subtype_mk
  have hx : Continuous fun x : Set.range (Smap C τ γ) => (Matrix.of (x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) :=
    continuous_subtype_val
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · dsimp only [Function.comp_def]
    fun_prop
  · dsimp only [Units.inv_mk]
    fun_prop

theorem smap_measEmb (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) : MeasurableEmbedding (Smap C τ γ) := by
  have hu : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => umat (γ⁻¹ * z) := by
    unfold umat
    exact Units.continuous_val.comp (continuous_subtype_val.comp (continuous_const.mul continuous_id))
  have hc : Continuous (Smap C τ γ) := by
    have h2 : Continuous fun z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)) => C.Qi τ * umat (γ⁻¹ * z) * C.Q τ * (C.y τ)⁻¹ :=
      ((continuous_const.matrix_mul hu).matrix_mul continuous_const).matrix_mul continuous_const
    exact h2
  refine MeasurableEmbedding.of_measurable_inverse_on_range hc.measurable ?_ (smapInv_cont C τ γ).measurable ?_
  · have hS : Set.range (Smap C τ γ) =
        {x | umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ))} := by
      ext x
      constructor
      · intro hx
        exact mem_of_range C τ γ ⟨x, hx⟩
      · intro hx
        have hx' : umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) ∈ UJset (X.B.I.ε (vOf X τ)) := hx
        refine ⟨ujOf' _ hx', ?_⟩
        unfold Smap umat ujOf'
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.val_mk, Units.inv_mul_cancel_left]
        rw [Qi_mul_Q_conj_mul_y_inv_eq C τ]
        simp
    rw [hS]
    apply IsClosed.measurableSet
    have hof : Continuous fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => Matrix.of x := continuous_id
    have hf : Continuous fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS => umat γ * (C.Q τ * Matrix.of x * C.y τ * C.Qi τ) :=
      continuous_const.matrix_mul (((continuous_const.matrix_mul hof).matrix_mul continuous_const).matrix_mul
        continuous_const)
    unfold UJset Formalism.REAL.inUJ
    exact isClosed_eq ((hf.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul hf) continuous_const
  · intro z
    apply Subtype.ext
    apply Units.ext
    unfold smapInv ujOf' Set.rangeFactorization Smap
    simp only [Equiv.apply_symm_apply, Units.val_mk]
    rw [conj_lemma_2 C τ]
    unfold umat
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Units.mul_inv_cancel_left]

variable (hB : WuBessel C)

theorem integrand_S (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ z : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of (Smap C τ γ z)))).smulRight
      ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of (Smap C τ γ z))) =
      sclOf hB u u' τ • Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z)) := by
  rw [phi'_S, phi_S]
  unfold Formalism.L2.SG.TermOp.rk1
  have hc : (starRingEnd ℂ) (sclOf hB u u' τ) = sclOf hB u u' τ := by
    unfold sclOf
    exact Complex.conj_ofReal _
  change (innerSL ℂ (sclOf hB u u' τ • X.Wloc u' (vOf X τ) (γ⁻¹ * z))).smulRight
      (X.Wloc u (vOf X τ) z) =
    sclOf hB u u' τ • (innerSL ℂ (X.Wloc u' (vOf X τ) (γ⁻¹ * z))).smulRight (X.Wloc u (vOf X τ) z)
  rw [map_smulₛₗ, hc]
  ext v
  simp [smul_smul]

theorem rank_one_continuous {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
    [InnerProductSpace ℂ V'] {T : Type*} [TopologicalSpace T] {a : T → V} {b : T → V'} (ha : Continuous a)
    (hb : Continuous b) : Continuous fun t => Formalism.L2.SG.TermOp.rk1 (a t) (b t) := by
  unfold Formalism.L2.SG.TermOp.rk1
  have h1 : Continuous fun t => innerSL ℂ (b t) := (innerSL ℂ).continuous.comp hb
  exact (ContinuousLinearMap.smulRightL ℂ V' V).continuous₂.comp₂ h1 ha

theorem integrand_aesm (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) :
    AEStronglyMeasurable (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) (ν.map (Smap C τ γ)) := by
  have hw : ∀ w : D.what₂.Word, Continuous (X.Wloc w (vOf X τ)) := fun w => by
    first
      | exact X.W.Wloc_cont w _
      | exact X.Wloc_cont w _
      | exact X.toWBlk.Wloc_cont w _
  rw [(smap_measEmb C τ γ).aestronglyMeasurable_map_iff]
  have he : (fun x : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS =>
      (innerSL ℂ ((locS hB u u' τ).Φ' (Matrix.of x))).smulRight
        ((locS hB u u' τ).Φ (trG (C.Q τ) (C.Qi τ) γ * Matrix.of x))) ∘ Smap C τ γ =
      fun z => sclOf hB u u' τ •
        Formalism.L2.SG.TermOp.rk1 (X.Wloc u (vOf X τ) z) (X.Wloc u' (vOf X τ) (γ⁻¹ * z)) := by
    funext z
    exact integrand_S C hB u u' τ γ z
  rw [he]
  apply Continuous.aestronglyMeasurable
  exact (rank_one_continuous (hw u) ((hw u').comp (continuous_const.mul continuous_id))).const_smul (sclOf hB u u' τ)

theorem locJ_map_eq' (u u' : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))
    (ν : Measure (Formalism.REAL.UJ (X.B.I.ε (vOf X τ)))) :
    (locS hB u u' τ).J (ν.map (Smap C τ γ)) (trG (C.Q τ) (C.Qi τ) γ) =
      ((((cOf hB u τ : ℝ) : ℂ))⁻¹ * sclOf hB u u' τ) •
        (haveI := FiniteDimensional.complete ℂ (X.Vloc u (vOf X τ)); Jv ν (X.Wloc u (vOf X τ)) (X.Wloc u' (vOf X τ)) γ) :=
  locJ_map_eq (C := C) (hB := hB) u u' τ γ ν (integrand_aesm (C := C) (hB := hB) u u' τ γ ν)

end Formalism.L2.SG.Pf.LocJEq
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.OneBesselTor
section
open MeasureTheory Matrix Finset

noncomputable section

namespace Formalism.L2.SG.Pf.OBT

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions Formalism.MainNotions.OnePlaceEstimates Formalism.MainNotions.FrameBoundFromBesselTorus

section Defs

variable {k r : ℕ}

def coefH (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) :
    Mx k r → (L.Wq →L[ℂ] L.Wp) :=
  fun x => P.comp ((L.σ x).comp Q)

def IsKFinPair (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) : Prop :=
  (∀ w, IsKFinHpk (k := k) (r := r) L.σ (Q w)) ∧
    (∀ x, IsKFinHpk (k := k) (r := r) L.σ (ContinuousLinearMap.adjoint P x))

def HasBData (L : LocBessel k r) (F : Mx k r → (L.Wq →L[ℂ] L.Wp)) (Λ : ℂ)
    (Φ : Mx k r → (L.Wq →L[ℂ] L.Wp)) (Ψ : Mx k r → Measure (PairSp k r) → (L.Wq →L[ℂ] L.Wp)) : Prop :=
  (∀ (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ), (∀ a, c a ≠ 0) →
      μᴴ * Hb k * μ = Hb k → L.J F (bigCell k r c μ) = Λ • Φ (bigCell k r c μ)) ∧
    (∀ (γ : Point ℂ (r + 1)) (g : Mx k r) (μR : Measure (Mt k r)) (ν : Measure (PairSp k r)),
      Gpt (Tz k r L.z) (Tz k r L.z') γ ≠ 0 → IsPtRep L γ g → IsRelStab L g → IsRootMeas L γ g μR →
      IsOrbQuot L g μR ν → OrbInt L F g ν = Λ • Ψ g ν)

end Defs

def RankOneTor (D : D7) (Cgf : ℝ) : Prop :=
  ∀ (L : LocBessel D.R.k D.R.rS) (κ₀ : ℝ),
    0 < κ₀ → L.c = cOfDpsi (κ₀ : ℂ) → 0 < L.κN → L.κN ≠ ⊤ → L.ε = epsSH D.R →
    GapAtLeast L.ε L.lam (Cgf * ((2 * D.R.rS + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (D.R.rS + 1) : ℕ) : ℝ) * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 2 +
        ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) ^ 3)) →
    ∃ (Φ : Mx D.R.k D.R.rS → (L.Wq →L[ℂ] L.Wp))
      (Ψ : Mx D.R.k D.R.rS → Measure (PairSp D.R.k D.R.rS) → (L.Wq →L[ℂ] L.Wp))
      (Λ₀ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℂ)
      (Λ : (L.Hs →L[ℂ] L.Wp) → (L.Wq →L[ℂ] L.Hs) → ℝ → ℝ → ℂ),
      (∀ P Q, IsKFinPair L P Q → HasBData L (coefH L P Q) (Λ₀ P Q) Φ Ψ) ∧
      (∀ P Q (κ τ : ℝ), 0 < κ → 0 < τ → IsKFinPair L P Q →
        HasBData L (fun x => coefH L P Q (cj D.R.k D.R.rS κ τ x)) (Λ P Q κ τ) Φ Ψ) ∧
      (∀ (κ τ : ℝ), 0 < κ → 0 < τ → ∀ P Q, IsKFinPair L P Q → Λ₀ P Q ≠ 0 →
        ∃ P₁ Q₁, IsKFinPair L P₁ Q₁ ∧ Λ P₁ Q₁ κ τ ≠ 0)

section Zero

variable {k r : ℕ}

theorem isKFinHpk_zero (L : LocBessel k r) : IsKFinHpk (k := k) (r := r) L.σ (0 : L.Hs) := by
  exact ⟨⊥, inferInstance, Submodule.zero_mem _, fun g _ x hx => by
    rw [Submodule.mem_bot] at hx
    simp [hx]⟩

theorem J_zero (L : LocBessel k r) (g : Mx k r) : L.J (fun _ => 0) g = 0 := by
  simp [LocBessel.J, Formalism.QuantumDeterminants.besselJ]

theorem orbInt_zero (L : LocBessel k r) (g : Mx k r) (ν : Measure (PairSp k r)) :
    OrbInt L (fun _ => 0) g ν = 0 := by
  simp [OrbInt, besselIntg]

end Zero

theorem oneBesselTor_of_rankOne (D : D7) (Cgf : ℝ) (h : RankOneTor D Cgf) : OneBesselTor D Cgf := by
  intro L f κ₀ κ τ hκ₀ hκ hτ hc hN hN' hε hgap hf
  obtain ⟨Φ, Ψ, Λ₀, Λ, h1, h2, h3⟩ := h L κ₀ hκ₀ hc hN hN' hε hgap
  obtain ⟨P, Q, hQ, hP, hfPQ⟩ := hf
  have hfeq : f = coefH L P Q := funext fun g => hfPQ g
  subst hfeq
  have hPQ : IsKFinPair L P Q := ⟨hQ, hP⟩
  by_cases h0 : Λ₀ P Q = 0
  · refine ⟨fun _ => 0, 1, one_ne_zero, ⟨0, 0, fun w => by simpa using isKFinHpk_zero L,
      fun x => by simpa using isKFinHpk_zero L, fun g => by simp⟩, ?_, ?_⟩
    · intro c μ hc0 hμ
      show L.J (fun _ => 0) _ = _
      rw [(h1 P Q hPQ).1 c μ hc0 hμ, h0, J_zero]
      simp
    · intro γ g μR ν hG hrep hst hroot hq
      show OrbInt L (fun _ => 0) g ν = _
      rw [(h1 P Q hPQ).2 γ g μR ν hG hrep hst hroot hq, h0, orbInt_zero]
      simp
  · obtain ⟨P₁, Q₁, hPQ₁, hΛ⟩ := h3 κ τ hκ hτ P Q hPQ h0
    refine ⟨coefH L P₁ Q₁, Λ P₁ Q₁ κ τ / Λ₀ P Q, div_ne_zero hΛ h0,
      ⟨P₁, Q₁, hPQ₁.1, hPQ₁.2, fun g => rfl⟩, ?_, ?_⟩
    · intro c μ hc0 hμ
      rw [(h2 P₁ Q₁ κ τ hκ hτ hPQ₁).1 c μ hc0 hμ, (h1 P Q hPQ).1 c μ hc0 hμ, smul_smul,
        div_mul_cancel₀ _ h0]
    · intro γ g μR ν hG hrep hst hroot hq
      rw [(h2 P₁ Q₁ κ τ hκ hτ hPQ₁).2 γ g μR ν hG hrep hst hroot hq,
        (h1 P Q hPQ).2 γ g μR ν hG hrep hst hroot hq, smul_smul, div_mul_cancel₀ _ h0]

end Formalism.L2.SG.Pf.OBT
end
end

