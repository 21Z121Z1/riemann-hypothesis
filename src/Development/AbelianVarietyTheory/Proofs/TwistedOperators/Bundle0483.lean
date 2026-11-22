import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0182
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepVectorLiftPairFlagLevelRealizedChain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0479
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjointHalfDatumStabilizerPairMove
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0209
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0170
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.RowHighestLeSpanColWordComplex
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0061
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.RealSmulSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0836
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0009
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0471
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0171
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0435
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeThetaTraceValuesAtComplexPoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0458
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0058
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0466

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumVectorTransformsByLevelCharacter
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ZetaLaw

open GlobalTheory.AdjDatumMove

variable {D : D7}

open Matrix in
open scoped ComplexOrder in

theorem isCartanInv_one_of_onb {k : ℕ} {G B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis G 1 B k) : IsCartanInv G 1 := by
  obtain ⟨e, he, h1, -⟩ := h
  have h2 : Bᴴ * G * B = 1 := by
    rw [h1, ← Matrix.diagonal_one]
    congr 1
    funext a
    rcases he a with h | h
    · simp [h.1]
    · exact absurd a.2 (not_lt.2 h.2)
  have hu : IsUnit B := IsUnit.of_mul_eq_one_right _ h2
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have h3 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  have h4 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]
  have hG : G = (B⁻¹)ᴴ * B⁻¹ := by
    calc G = ((B⁻¹)ᴴ * Bᴴ) * G * (B * B⁻¹) := by rw [h3, h4, Matrix.one_mul, Matrix.mul_one]
      _ = (B⁻¹)ᴴ * (Bᴴ * G * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one]
  refine ⟨by simp, by simp, ?_⟩
  rw [Matrix.mul_one, hG]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.2 hu))

theorem topL_mul_right {κ : Type} [CommRing κ] {a b : ℕ} (y : Matrix (Fin b) (Fin a) κ) (γ : Matrix (Fin a) (Fin a) κ) :
    topL a (y * γ) = topL a y * γ := by
  ext i j
  by_cases hi : i.val < b
  · simp [topL, Matrix.mul_apply, hi]
  · simp [topL, Matrix.mul_apply, hi]

theorem lowZero_mul_right {κ : Type} [CommRing κ] {a b : ℕ} {y : Matrix (Fin b) (Fin a) κ} (hy : LowZero a y)
    (γ : Matrix (Fin a) (Fin a) κ) : LowZero a (y * γ) := by
  intro i j hi _
  rw [Matrix.mul_apply]
  exact Finset.sum_eq_zero fun l _ => by rw [hy i l hi l.2, zero_mul]

abbrev GCond {a b : ℕ} (L : LevDat D.host.E ℂ a) (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) : Prop :=
  (∀ PP ∈ L.Pg, LowZero a (y PP)) ∧ ∃ g : ∀ PP : ↥L.Pg, GL (Fin a) (kP PP.1),
    (∀ PP : ↥L.Pg, ((g PP : GL (Fin a) _) : Matrix (Fin a) (Fin a) _) = topL a (y PP.1)) ∧
    (∀ PP : ↥L.Pg, g PP ∈ blockTri (blkOf L.r L.t)) ∧ (fun PP => upperLeftBlock L.hr (g PP)) ∈ L.P.H

theorem gCond_mul {a b : ℕ} (L : LevDat D.host.E ℂ a) (γ : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP))
    (hγ : ∀ PP ∈ L.Pg, γ PP ∈ blockTri (blkOf L.r L.t)) (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) ∈ L.P.H)
    (y z : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) (hz : ∀ PP, z PP = y PP * (γ PP).val)
    (h : GCond L y) : GCond L z := by
  obtain ⟨h1, g, h2, h3, h4⟩ := h
  refine ⟨fun PP hP' => (hz PP).symm ▸ lowZero_mul_right (h1 PP hP') _, fun PP => g PP * γ PP.1, fun PP => ?_,
    fun PP => mul_mem (h3 PP) (hγ PP.1 PP.2), ?_⟩
  · rw [Units.val_mul, h2, hz, topL_mul_right]
  · have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (g PP * γ PP.1)) =
        (fun PP => upperLeftBlock L.hr (g PP)) * (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) := by
      funext PP
      exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (h3 PP)) (blockTri_blkOf_le _ _ (hγ PP.1 PP.2))
    rw [e]
    exact mul_mem h4 hP

theorem omegaG_mul_right {a b : ℕ} (L : LevDat D.host.E ℂ a) (hs : L.s = 0)
    (χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (γ : ∀ PP : Pl D.host.E, GL (Fin a) (kP PP))
    (hγ : ∀ PP ∈ L.Pg, γ PP ∈ blockTri (blkOf L.r L.t)) (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)) ∈ L.P.H)
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaG L χj (fun PP => y PP * (γ PP).val) =
      ((L.P.chi ⟨_, hP⟩ : ℂˣ) : ℂ) * (∏ PP ∈ L.Pg, ((χj PP (Matrix.GeneralLinearGroup.det (γ PP)) : ℂˣ) : ℂ)⁻¹) *
        omegaG L χj y := by
  have hγi : ∀ PP ∈ L.Pg, (γ PP)⁻¹ ∈ blockTri (blkOf L.r L.t) := fun PP h => inv_mem (hγ PP h)
  have hPi : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)⁻¹) ∈ L.P.H := by
    have e : (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1)⁻¹) = (fun PP : ↥L.Pg => upperLeftBlock L.hr (γ PP.1))⁻¹ := by
      funext PP
      exact extendOne_inv _ (blockTri_blkOf_le _ _ (hγ PP.1 PP.2))
    rw [e]
    exact inv_mem hP
  unfold omegaG
  by_cases hy : GCond L y
  · have hy' : GCond L (fun PP => y PP * (γ PP).val) := gCond_mul L γ hγ hP y _ (fun _ => rfl) hy
    rw [dif_pos hy', dif_pos hy]
    have key : ∀ PP : ↥L.Pg, hy'.2.choose PP = hy.2.choose PP * γ PP.1 := fun PP => Units.ext (by
      rw [Units.val_mul, hy'.2.choose_spec.1 PP, hy.2.choose_spec.1 PP, topL_mul_right])
    have hc : (⟨fun PP => upperLeftBlock L.hr (hy'.2.choose PP), hy'.2.choose_spec.2.2⟩ : L.P.H) =
        ⟨fun PP => upperLeftBlock L.hr (hy.2.choose PP), hy.2.choose_spec.2.2⟩ * ⟨_, hP⟩ :=
      Subtype.ext (funext fun PP => by
        show upperLeftBlock L.hr (hy'.2.choose PP) = upperLeftBlock L.hr (hy.2.choose PP) * upperLeftBlock L.hr (γ PP.1)
        rw [key]
        exact extendMatrixByIdentityAlongIndices_mul _ (blockTri_blkOf_le _ _ (hy.2.choose_spec.2.1 PP)) (blockTri_blkOf_le _ _ (hγ PP.1 PP.2)))
    rw [hc, map_mul]
    simp only [hs, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one, mul_one, key, map_mul, Units.val_mul, mul_inv]
    rw [Finset.prod_mul_distrib, ← Finset.prod_coe_sort L.Pg (fun PP => ((χj PP (Matrix.GeneralLinearGroup.det (γ PP)) : ℂˣ) : ℂ)⁻¹)]
    ring
  · have hy' : ¬ GCond L (fun PP => y PP * (γ PP).val) := fun h => hy (gCond_mul L (fun PP => (γ PP)⁻¹) hγi hPi _ y
      (fun PP => by rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]) h)
    rw [dif_neg hy', dif_neg hy, mul_zero]

theorem omegaQ_mul_right {n r : ℕ} (hr : r ≤ n) (Q : Finset (Pl D.host.E)) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (γ : ∀ PP : Pl D.host.E, GL (Fin r) (kP PP)) (u : ∀ PP : Pl D.host.E, Matrix (Fin n) (Fin r) (kP PP)) :
    omegaQ Q r ξ (-1) (fun PP => u PP * (γ PP).val) =
      (∏ PP ∈ Q, ((ξ PP (Matrix.GeneralLinearGroup.det (γ PP)) : ℂˣ) : ℂ)⁻¹) * omegaQ Q r ξ (-1) u := by
  have h := omegaQ_mul hr Q ξ (fun PP => (1 : GL (Fin n) (kP PP))) (fun PP => (γ PP)⁻¹) (fun _ _ => one_mem _) u
  simp only [inv_inv, Units.val_one, Matrix.one_mul] at h
  rw [h]
  congr 1
  refine Finset.prod_congr rfl fun PP _ => ?_
  have e1 : upperLeftBlock hr (1 : GL (Fin n) (kP PP)) = 1 := blockDiagonalExtendByOnePrimeField_one _ _
  rw [e1, map_one, map_one, inv_one, one_mul, map_inv, map_inv, Units.val_inv_eq_inv_val]

open Formalism.IndefR.Lev (finE) in

theorem levDatum_actO (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (L : LevDat D.host.E ℂ T.rank) (hs : L.s = 0) (Q : Finset (Pl D.host.E)) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (e : AE D) (hr : T.rank ≤ S.rank) (h : GA D T) (sh : finE T h ∈ St βT)
    (hγ : ∀ PP ∈ L.Pg, redFn βT PP (finE T h) ∈ blockTri (blkOf L.r L.t))
    (hP : (fun PP : ↥L.Pg => upperLeftBlock L.hr (redFn βT PP.1 (finE T h))) ∈ L.P.H) (x : WO S T) :
    levDatum S T βS βT L Q m e (actO S T 1⁻¹ h⁻¹ x) =
      ((L.P.chi ⟨_, hP⟩ : ℂˣ) : ℂ) *
        (∏ PP ∈ L.Pg, ((m PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)⁻¹) *
        (∏ PP ∈ Q, ((m PP (Matrix.GeneralLinearGroup.det (redFn βT PP (finE T h))) : ℂˣ) : ℂ)⁻¹) *
        levDatum S T βS βT L Q m e x := by
  have s1 : finE S (1 : GA D S) ∈ St βS := by rw [map_one]; exact one_mem _
  have s1' : finE S (1 : GA D S)⁻¹ ∈ St βS := by rw [inv_one]; exact s1
  have sh' : finE T h⁻¹ ∈ St βT := by rw [map_inv]; exact inv_mem sh
  have hG1 : ∀ PP, redFn βS PP (finE S (1 : GA D S)⁻¹) = 1 := fun PP => by rw [inv_one, map_one, redFn_one]
  have hH : ∀ PP, (redFn βT PP (finE T h⁻¹))⁻¹ = redFn βT PP (finE T h) := fun PP => by
    rw [map_inv, redFn_inv sh, inv_inv]
  unfold levDatum
  by_cases hx : IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x)
  · have h1 := red_actO S T βS βT s1' sh' hx.2
    have h2 : ∀ PP, redM PP (frMapAdj S T βS βT (actO S T 1⁻¹ h⁻¹ x)) =
        redM PP (frMapAdj S T βS βT x) * (redFn βT PP (finE T h)).val := fun PP => by
      rw [h1.2 PP, hG1 PP, hH PP, Units.val_one, Matrix.one_mul]
    rw [if_pos hx, if_pos ⟨isHalf_actO' _ _ hx.1, h1.1⟩, funext h2,
      omegaG_mul_right L hs m (fun PP => redFn βT PP (finE T h)) hγ hP, omegaQ_mul_right hr Q m]
    ring
  · rw [if_neg hx, if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    have e' := GlobalTheory.AdelicLatMove.actO_actO_inv S T (1 : GA D S) h x
    have h3 := isHalf_actO' (1 : GA D S) h h1
    have h4 := (red_actO S T βS βT s1 sh h2).1
    rw [e'] at h3 h4
    exact hx ⟨h3, h4⟩

open Formalism.IndefR.Lev (finE) in
set_option maxHeartbeats 1000000 in

theorem zeta_law : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ k ∈ levG (Wc D i) (R.βW i) (R.datWp i P), ω (1, k) f = levChi (Wc D i) (R.βW i) (R.datWp i P) k • f := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h k hk
  classical
  obtain ⟨hC, -, -, -, hch, hW, -, hlv, -, -, -⟩ := h
  rw [GlobalTheory.FinZeta.isLevelVec_iff] at hlv
  obtain ⟨hvac, e, he, hth⟩ := hlv
  have hL := hC.lev
  have hkG : k ∈ GfC (Wc D i) := (Subgroup.mem_inf.1 hk).1
  have hkL : finE (Wc D i) k ∈ lev D.sp.cm (Wc D i).gram (R.βW i) (R.datWp i P) := (Subgroup.mem_inf.1 hk).2
  have sW : finE (Wc D i) k ∈ St (R.βW i) := parLev_St hkL.1
  have sV : finE (Vc D i) 1 ∈ St (R.βV i) := by rw [map_one]; exact one_mem _
  have dV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i)
  have dW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)
  have fV := (hL.βV i).choose_spec.1
  have fW := (hL.βW i).choose_spec.1
  have hch' := GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification R hL i t s cμ cη m hch
  have hres : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t, GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP) :=
    fun PP hP => hch'.1 PP (Finset.mem_union.1 hP)
  have hun := hch'.2.1 ((R.datWp i P).Pg ∪ R.Q t) (fun PP h => Finset.mem_union.2 h)
  have hvac1 := GlobalTheory.StepVecLaw.om_vac hW (D.sp.V_sig _) (D.sp.W_sig _)
    (fun τ => isCartanInv_one_of_onb (hC.models.BV i τ)) (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)) dV dW fV fW hvac he
    (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) hun.1 hun.2 (one_mem _) hkG sV sW
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : (Wc D i).rank ≤ (Vc D i).rank := by omega
  have hlaw := levDatum_actO (Vc D i) (Wc D i) (R.βV i) (R.βW i) (R.datWp i P) rfl (R.Q t) m e hr k sW
    (fun PP hP => parLev_g hkL.1 hP) hkL.2
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hfin := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hW (cA D e) _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) dV dW (cA D e) hcc hinf f₀ hvac.2.theta) hth 1 k
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) dV dW fV fW 1 k sV sW) _ _ (Units.ne_zero _)
    hvac1 hlaw
  rw [hfin]
  congr 1
  have hd : Disjoint (R.datWp i P).Pg (R.Q t) := (GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T R.toLevCh A.μ0 hL t).1
  have hone : ∀ PP, redFn (R.βV i) PP (finE (Vc D i) 1) = 1 := fun PP => by rw [map_one, redFn_one]
  unfold levChi levFn
  rw [extendOne_of_mem _ hkL.2]
  have hs0 : (R.datWp i P).s = 0 := rfl
  have hQ0 : (R.datWp i P).Q = ∅ := rfl
  simp only [map_one, redFn_one, inv_one, one_mul, hs0, hQ0, Finset.range_zero, Finset.prod_empty, Finset.prod_const_one,
    mul_one, Finset.prod_union hd, Units.val_mul, Units.coe_prod]
  have hne : ∀ s : Finset (Pl D.host.E),
      (∏ PP ∈ s, ((m PP (Matrix.GeneralLinearGroup.det (redFn (R.βW i) PP (finE (Wc D i) k))) : ℂˣ) : ℂ)) ≠ 0 :=
    fun s => Finset.prod_ne_zero_iff.2 fun _ _ => Units.ne_zero _
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib]
  field_simp
  rw [mul_comm (_ * _), mul_div_assoc, div_self (mul_ne_zero (hne _) (hne _)), mul_one]
  rfl

end GlobalTheory.ZetaLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockPolynomialVectorInjectiveNonzeroVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockPolyInj

open GlobalTheory.FockVecInj GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7}

theorem pureTensorO_injective_of_on (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D)
    (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (sV BV : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (s BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (pV pW : D.what₂.Tau → ℕ)
    (hBV : ∀ τ, IsONBasis (gramAt D V τ) (sV τ) (BV τ) (pV τ))
    (hBW : ∀ τ, IsONBasis (gramAt D W τ) (s τ) (BW τ) (pW τ)) (f : WO V W → ℂ) (hf : IsThetaFunO ψ V W f)
    (hvac : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (sV τ) (s τ)) f) (hf0 : f ≠ 0) :
    Function.Injective (pureTensorO ψ θ V W sV s BV BW f) := by
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  choose ε hε hG hs using hBV
  choose ε' hε' hG' hs' using hBW
  have sq : ∀ τ a, (ε τ a : ℂ) * ε τ a = 1 := fun τ a => by
    rcases hε τ a with h | h <;> simp [h.1]
  have sq' : ∀ τ a, (ε' τ a : ℂ) * ε' τ a = 1 := fun τ a => by
    rcases hε' τ a with h | h <;> simp [h.1]
  have hdet : ∀ τ, IsUnit (BV τ).det := fun τ => by
    have e : (diagonal (fun a => (ε τ a : ℂ)) * ((BV τ)ᴴ * gramAt D V τ)) * BV τ = 1 := by
      rw [Matrix.mul_assoc, hG, Matrix.diagonal_mul_diagonal]
      simp only [sq, Matrix.diagonal_one]
    exact Matrix.isUnit_det_of_left_inverse e
  have hE : ∀ τ z g, Formalism.IndefR.Datum.dRho (heisO ψ V W) θ τ z g = hD (iotaW σ W V) (piW θ W V) (omO V W)
      (Pi.single τ z : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) g := fun τ z g => by
    rw [← pi_lineAt hθ]
    exact dLine_eq_hD h hψ (isRealDir_lineAt hθ τ z) g
  let M : Submodule ℂ (WO V W → ℂ) :=
    { carrier := {g | Sm (iotaW σ W V) g}
      add_mem' := fun ha hb w => (ha w).add (hb w)
      zero_mem' := fun w => contDiff_const
      smul_mem' := fun c g hg w => contDiff_const.mul (hg w) }
  have hform := fun g hg u w => hD_eq_fderiv (iotaW σ W V) (piW θ W V) (omO V W) g hg u w
  obtain ⟨Dop, hD1, -⟩ := exists_heisenberg_operators _ _ (iotaW σ W V) (piW θ W V) (omO V W) (h.pi_iota W V) hform M
    (fun _ hg => hg) fun u g hg => (hD_formula_smooth _ _ _ _ _ (h.pi_iota W V) g hg u).2
  have sk : ∀ u v, omO V W v u = -omO V W u v := fun u v => by
    have h1 := omO_self h (S := V) (T := W) (u + v)
    simp only [LinearMap.map_add, LinearMap.add_apply, omO_self h] at h1
    linarith
  have hcomm : ∀ u v g, Dop u (Dop v g) = Dop v (Dop u g) + (-(2 * Real.pi * I) * (omO V W u v : ℝ)) • g :=
    fun u v g => by
    apply Subtype.ext
    rw [Submodule.coe_add, Submodule.coe_smul, hD1, hD1, hD1, hD1]
    exact eq_add_of_sub_eq' (heisenberg_derivative_commutator _ _ _ _ _ (h.pi_iota W V) hform sk g g.2 u v)
  let η : FVar D W.rank V.rank → ℝ := fun k => ε' k.1 k.2.1 * ε k.1 k.2.2
  have hη : ∀ k, η k = 1 ∨ η k = -1 := fun k => by
    rcases hε k.1 k.2.2 with h | h <;> rcases hε' k.1 k.2.1 with h' | h' <;> simp [η, h.1, h'.1]
  let u : ℂ → FVar D W.rank V.rank → RW W V := fun c k =>
    (Pi.single k.1 (c • unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) : D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ)
  have hom : ∀ c c' k l, omO V W (u c k) (u c' l) =
      if k = l then 2 * (tauE D k.1 D.host.xi0 * (c * conj c' * η k)).re else 0 := by
    rintro c c' ⟨τ, i, j⟩ ⟨τ', k, l⟩
    refine (omO_single V W τ τ' _ _).trans ?_
    by_cases hτ : τ = τ'
    · subst hτ
      rw [if_pos rfl, Matrix.conjTranspose_smul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul,
        Matrix.trace_smul, Matrix.trace_smul, trace_unitMap (sq τ) (hG τ) (hG' τ)]
      by_cases hk : i = k ∧ j = l
      · rw [if_pos hk, if_pos (by rw [hk.1, hk.2])]
        simp only [η, smul_eq_mul, Complex.ofReal_mul, mul_assoc]
        rfl
      · rw [if_neg hk, if_neg (by simpa using hk)]
        simp
    · rw [if_neg hτ, if_neg fun hh => hτ (congrArg Prod.fst hh)]
  have hJ : ∀ k : FVar D W.rank V.rank, cplxO (sV k.1) (s k.1) (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) =
      (I * η k) • unitMap (BV k.1) (BW k.1) k.2.1 k.2.2 := fun k => by
    rw [cplxO_unitMap (hdet _) (hs _) (hs' _)]
    simp only [η, Complex.ofReal_mul]
  have h1 : ∀ k : FVar D W.rank V.rank, u 1 k = (Pi.single k.1 (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2) :
      D.what₂.Tau → Matrix (Fin W.rank) (Fin V.rank) ℂ) := fun k => congrArg (Pi.single k.1) (one_smul _ _)
  have hξ : ∀ τ, tauE D τ D.host.xi0 ≠ 0 := fun τ => (_root_.map_ne_zero _).2 (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D)
  have hre := fun τ => GlobalTheory.OrientedRealForm.realPlace_imaginaryGenerator_re_eq_zero (D := D) τ
  have him : ∀ τ, (tauE D τ D.host.xi0).im ≠ 0 := fun τ hh => hξ τ (Complex.ext (hre τ) hh)
  have hsc : ∀ τ, (fockScale D τ : ℂ) ≠ 0 := fun τ => by
    have := norm_pos_iff.2 (hξ τ)
    have h2 : 0 < fockScale D τ := by unfold fockScale; positivity
    exact Complex.ofReal_ne_zero.2 h2.ne'
  refine injective_of_canonicalCommutation M _ (fun k => (fockScale D k.1 : ℂ)⁻¹ • (Dop (u 1 k) - I • Dop (u (I * η k) k)))
    (fun k => Dop (u 1 k) + I • Dop (u (I * η k) k))
    (fun k => (fockScale D k.1 : ℂ)⁻¹ * (-8 * Real.pi * (tauE D k.1 D.host.xi0).im)) (fun k g => ?_) (fun k l g => ?_)
    (fun k l g => ?_) (fun k => ?_) ⟨f, theta_sm h hf⟩ (fun k => ?_) (fun hh => hf0 (congrArg Subtype.val hh))
  · simp only [aPlusAll, aPlus, crea, LinearMap.smul_apply, LinearMap.sub_apply, Submodule.coe_smul, Submodule.coe_sub,
      hD1, hE, hJ]
    rw [h1]
  · rw [(ccr_of_comm Dop _ hcomm _ _ _ _ _ _ g).1]
    refine add_eq_left.2 (smul_eq_zero.2 (Or.inl ?_))
    simp only [hom]
    split_ifs with hh
    · subst hh
      rcases hη k with e | e <;> simp [e, hre]
    · simp
  · rw [(ccr_of_comm Dop _ hcomm _ _ _ _ 0 _ g).2]
    refine congrArg (fun c : ℂ => _ + c • g) ?_
    by_cases hh : k = l
    · subst hh
      simp only [hom, if_true]
      refine congrArg _ ?_
      rcases hη k with e | e <;> simp [e, hre] <;> ring_nf <;> simp only [I_sq] <;> ring1
    · simp [hom, hh]
  · exact mul_ne_zero (inv_ne_zero (hsc _)) (mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)) (Complex.ofReal_ne_zero.2 (him _)))
  · apply Subtype.ext
    have := hvac k.1 (unitMap (BV k.1) (BW k.1) k.2.1 k.2.2)
    simp only [annih, hE, hJ] at this
    simp only [LinearMap.smul_apply, LinearMap.add_apply, Submodule.coe_smul, Submodule.coe_add, hD1]
    rw [h1]
    exact this

theorem isONBasis_one {V : HSp D} (hV : V.gram = 1) (τ : D.what₂.Tau) :
    IsONBasis (gramAt D V τ) 1 1 V.rank := by
  have hg : gramAt D V τ = 1 := by
    unfold gramAt
    rw [hV]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  refine ⟨fun _ => 1, fun a => Or.inl ⟨rfl, a.isLt⟩, ?_, ?_⟩ <;>
    simp [hg, Matrix.diagonal_one]

theorem fvec_injective : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ f, C.IsTh f → C.IsFock B f → f ≠ 0 → Function.Injective (C.fvec B f) := by
  intro D S T C B hB f hf hvac hf0
  have hT := ((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.1
  exact pureTensorO_injective_of_on C.ψ C.θ S T C.std C.inf (fun _ => 1) (fun _ => 1) (C.sB B) B
    (fun _ => S.rank) (fun _ => C.X.p0) (isONBasis_one C.m.gS) (fun τ => (hT τ).2) f hf hvac hf0

end GlobalTheory.FockPolyInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelEqOfUnipotentFrameChangeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeKernel_eq_of_unipotent_frameChange : ∀ {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), IsUnf U →
    ∀ (P : Ideal (𝓞 E)) (p i : ℕ), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.IsHeckePrime l P p → ∀ (k : U.Comp) (x : (U.X k).dom),
      letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      ∀ (C C' : hkKer (Xo := Xo) P p i (CAt σ) (U.un k x)) (z z' w : FrPt Xo c (CAt σ)) (t t' : Ix Dw → (CAt σ)ˣ),
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C z →
        hkRelFr P p i (GlobalTheory.ThetaTrace.hkTr Xo c p) (CAt σ) (U.un k x) C' z' →
        (∀ j, j ≠ none → t j = 1) → (∀ j, j ≠ none → t' j = 1) → FrBor t w z → FrBor t' w z' → C = C' := by
  first | exact @GlobalTheory.HeckeInj.eq_of_hkRelFr_frBor | exact GlobalTheory.HeckeInj.eq_of_hkRelFr_frBor | (intros; apply GlobalTheory.HeckeInj.eq_of_hkRelFr_frBor <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeKernelSumEqCardTorsionMulTraceStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeKernel_sum_eq_card_torsion_mul_trace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x x' : Sp Ω ⟶ Xo.X) (Ψ : Gx x ⟶ Gx x') (p n : ℕ) (s : LB.Sec (PPx x)) (s' : LB.Sec (PPx x')) (β : LB.Gen (isoLB Xo.univ.t.G Xo.univ.t.PP Ψ ((p : ℤ) ^ 2))) (s₁ : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((p : ℤ) ^ 2) (Over.mk x))) (e : Fin n ≃ transKer Xo.univ.t.G Ψ), IsHeckeIsog p (transKer Xo.univ.t.G Ψ) Ψ → IsThGen x' s' → IsThetaTrace Xo.univ.t.G Xo.univ.t.PP Ψ p s s' → IsRigIso Xo.univ.t.G Xo.univ.t.PP Ψ _ β → IsMulPull Xo.univ.t.G Xo.univ.t.PP p s s₁ → ∀ (Z : Scheme.{0}) (r : Z ⟶ Gx x) (z : Z) (J : (Z ⟶ Xo.univ.t.G.left) → Xo.univ.t.PP.L.ι), Good Xo.univ.t.PP.L z J → (Nat.card {a : Over.mk x ⟶ Xo.univ.t.G // a ∈ transKer Xo.univ.t.G Ψ ∧ a ^ p = 1} : Z.presheaf.stalk z) * sv Xo.univ.t.G Xo.univ.t.PP s' (r ≫ Ψ) z J = ∑ j, ((val β (r ≫ (translT Xo.univ.t.G (e j).1).left) z J)⁻¹).val * sv Xo.univ.t.G Xo.univ.t.PP s₁ (r ≫ (translT Xo.univ.t.G (e j).1).left) z J := by
  first | exact @GlobalTheory.KernelSum.sum_ker_eq_card_mul | exact GlobalTheory.KernelSum.sum_ker_eq_card_mul | (intros; apply GlobalTheory.KernelSum.sum_ker_eq_card_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeLiftEqSmul
section
open NumberField AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.HeckeEx
open GlobalTheory.Dict (castFr)
open GlobalTheory.FrameNorm (IsUnitFr)
open scoped Matrix
open GlobalTheory.HkFam (admitted)
noncomputable section

set_option autoImplicit false

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeckeLiftScalar

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.MoveValues GlobalTheory.HeckeValues

set_option maxHeartbeats 1000000 in

theorem hkPtC_values_lie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (p : ℕ) (y z : FrPt Xo c (CAt σ)) (C : Subgroup (Over.mk y.x ⟶ Xo.univ.t.G)),
  HkPtC p y C z →
  ∃ (ψ : pullback Xo.univ.t.G.hom y.x ⟶ pullback Xo.univ.t.G.hom z.x)
    (ψp : (Over.mk y.x ⟶ Xo.univ.t.G) →* (Over.mk z.x ⟶ Xo.univ.t.G)) (n : ℕ)
    (cr : Fin n → (Over.mk y.x ⟶ Xo.univ.t.G)) (b : Xo.univ.t.PP.L.ι → Xo.univ.t.PP.L.ι → (Over.mk y.x ⟶ Xo.univ.t.G) → ℂ),
    @IsHkIsog E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) (algClosedCAt σ) p y.x z.x C ψ ψp ∧
    (∀ τ j, @IsLieImageH E _ _ _ H Dw l Xo (CAt σ) (fieldCAt σ) p y.x z.x ψ (y.u τ j) (z.u τ j)) ∧ GlobalTheory.ThetaTrace.IsRepsModTors C p cr ∧
    (∀ i j (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i → ⊤ ≤ (a ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j → b i j a ≠ 0) ∧
    (∀ i j i' j' (a : Over.mk y.x ⟶ Xo.univ.t.G), ⊤ ≤ (ψp a).left ⁻¹ᵁ (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') →
      ⊤ ≤ (a ^ p).left ⁻¹ᵁ (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') →
      b i j a * valAt' (a ^ p).left (Xo.univ.t.PP.L.U j ⊓ Xo.univ.t.PP.L.U j') (Xo.univ.t.PP.L.g j j').val =
        valAt' (ψp a).left (Xo.univ.t.PP.L.U i ⊓ Xo.univ.t.PP.L.U i') (Xo.univ.t.PP.L.g i i').val * b i' j' a) ∧
    (∀ i j, ⊤ ≤ (1 : Over.mk z.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      ⊤ ≤ (1 : Over.mk y.x ⟶ Xo.univ.t.G).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      valAt' z.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => i)) (Xo.univ.t.PP.rig.s (fun _ => i)).val =
        b i j 1 * valAt' y.x ((Xo.univ.t.PP.L.pull (eSec Xo.univ.t.G)).U (fun _ => j)) (Xo.univ.t.PP.rig.s (fun _ => j)).val) ∧
    (∀ (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y.x ⟶ Xo.univ.t.G)), IsHolTo Set.univ (fun w => (e w).left) →
      ∀ i j, DifferentiableOn ℂ (fun w => b i j (e w))
        {w | ⊤ ≤ (ψp (e w)).left ⁻¹ᵁ Xo.univ.t.PP.L.U i ∧ ⊤ ≤ (e w ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U j}) ∧
    (∀ (a : Over.mk y.x ⟶ Xo.univ.t.G) i (jm : Fin n → Xo.univ.t.PP.L.ι), ⊤ ≤ (ψp a).left ⁻¹ᵁ Xo.univ.t.PP.L.U i →
      (∀ m, ⊤ ≤ ((cr m * a) ^ p).left ⁻¹ᵁ Xo.univ.t.PP.L.U (jm m)) →
      valAt' (lift (𝟙 (Over.mk z.x)) (ψp a)).left ((PPx z.x).U (fun _ => i)) (z.s.f (fun _ => i)) =
        ∑ m, b i (jm m) (cr m * a) *
          valAt' (lift (𝟙 (Over.mk y.x)) ((cr m * a) ^ p)).left ((PPx y.x).U (fun _ => jm m)) (y.s.f (fun _ => jm m))) := by
  intro E _ _ _ H Dw l Xo c σ p y z C hk
  letI := fieldCAt σ
  haveI := algClosedCAt σ
  obtain ⟨ψ, ψp, hiso, hL, htr⟩ := hk
  obtain ⟨β, s₁, n, cr, hβ, hs, hr, hv⟩ := isThetaTrace_iff.1 htr
  obtain ⟨β₀, hβ₀, hc₀⟩ := hs.exists_isRigIso
  have hK := transKer_of_isHkIsog hiso
  have hΨ : ∀ a, rpt a ≫ conj y.x z.x ψ = rpt (ψp a) := fun a => (sends_conj_iff ψ _ _).2 (hiso.2.2.1 a)
  refine ⟨ψ, ψp, n, cr, fun i j a => bv Xo.univ.t.PP β β₀ i j a, hiso, hL, hK ▸ hr, fun i j a _ _ => bv_ne i j a,
    fun i j i' j' a hi hj => ?_, fun i j hi hj => ?_, fun g e he i j => ?_, fun a i jm hi hj => ?_⟩
  · have mi := (mem_iff _ _).2 hi
    have mj := (mem_iff _ _).2 hj
    exact bv_trans hβ.2.1 hβ₀.2.1 a (ψp a) (hΨ a) mi.1 mi.2 mj.1 mj.2
  · have h1 : rpt (1 : Over.mk y.x ⟶ Xo.univ.t.G) ≫ conj y.x z.x ψ = rpt (1 : Over.mk z.x ⟶ Xo.univ.t.G) := by
      exact (hΨ 1).trans (congrArg (fun q => rpt q) (map_one ψp))
    exact bv_rig hβ hβ₀ h1 i j ((mem_iff _ _).2 hi) ((mem_iff _ _).2 hj)
  · have hfun : (fun w => rpt (e w)) = fun w => fibPt Xo.univ.t.G (e w) ≫ (swap y.x).inv :=
      funext fun w => (Iso.eq_comp_inv _).2 (fibPt_swap (e w))
    have hh : IsHolTo Set.univ (fun w => rpt (e w)) := by
      rw [hfun]
      exact (GlobalTheory.HolFibre.isHolTo_fibPt_and_comp _ Xo.univ.t.G y.x g e he).2 _ (swap y.x).inv
    exact bv_hol hβ.2.1 hβ₀.2.1 ψp hΨ e hh i j
  · exact bv_values hβ.2.1 hβ₀.2.1 hc₀ cr (fun m => hr.1 m) hv a (ψp a) (hΨ a) i jm ((mem_iff _ _).2 hi)
      (fun m => (mem_iff _ _).2 (hj m))

end GlobalTheory.HeckeLiftScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLaws
section
set_option autoImplicit false

namespace GlobalTheory.HeckePointLaw

theorem heckePointLaws : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws :=
  heckePointLaws_of_transport GlobalTheory.T.heckeIsogeny_thetaGenerator_transport

end GlobalTheory.HeckePointLaw
end

