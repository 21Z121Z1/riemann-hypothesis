import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HalfLinearCocycle
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LocalIntegralGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0483
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0485
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1271
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1687
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumSourceLevelCharacterLaw
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SourceLaw
variable {D : D7}

theorem omegaG_levelDatum_zero_indep_chars (a r t : ℕ) (ha : r ≤ a) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ)
    (χ χ' : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ' χj : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) {b : ℕ}
    (y : ∀ PP : Pl D.host.E, Matrix (Fin b) (Fin a) (kP PP)) :
    omegaG (Lev.datY a r t 0 ha Pg ∅ P χ ξ Lev.Frm.B) χj y = omegaG (Lev.datY a r t 0 ha Pg ∅ P χ' ξ' Lev.Frm.B) χj y := by
  unfold omegaG
  rfl

open GlobalTheory.AdjDatumMove in

theorem levelDatum_target_under_sourceLevel_element (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (r t : ℕ) (ha : r ≤ T.rank) (hb : r ≤ S.rank) (hTS : T.rank ≤ S.rank) (ea : T.rank = r + 0 * t)
    (eb : S.rank = r + (0 + 1) * t)
    (Pg Q : Finset (Pl D.host.E)) (P : LevelP Pg r ℂ) (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (e : AE D)
    (g : GA D S) (sg : finE S g ∈ St βS)
    (hG : ∀ PP ∈ Pg, redFn βS PP (finE S g) ∈ blockTri (blkOf r t))
    (hP : (fun PP : ↥Pg => upperLeftBlock hb (redFn βS PP.1 (finE S g))) ∈ P.H)
    (hQ : ∀ PP ∈ Q, redFn βS PP (finE S g) ∈ blockTri (blk2 T.rank)) (x : WO S T) :
    GlobalTheory.FinZeta.levDatum S T βS βT (Lev.datY T.rank r t 0 ha Pg ∅ P (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) Q m e
                 (actO S T g⁻¹ 1⁻¹ x) =
      ((((P.chi ⟨_, hP⟩ * ∏ PP ∈ Pg, ∏ i ∈ Finset.range (0 + 1),
            m PP (dBlk (blkOf r t) (i + 1) (redFn βS PP (finE S g))))⁻¹ *
          ∏ PP ∈ Pg, m PP (Matrix.GeneralLinearGroup.det (redFn βS PP (finE S g))) : ℂˣ) : ℂ) *
        ∏ PP ∈ Q, (((m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hTS (redFn βS PP (finE S g))⁻¹)))⁻¹ : ℂˣ) : ℂ)) *
      GlobalTheory.FinZeta.levDatum S T βS βT (Lev.datY T.rank r t 0 ha Pg ∅ P (fun _ _ => 1) (fun _ => 1) Lev.Frm.B) Q m e x := by
  have sg' : finE S g⁻¹ ∈ St βS := by rw [map_inv]; exact inv_mem sg
  have s1 : finE T (1 : GA D T)⁻¹ ∈ St βT := by rw [inv_one, map_one]; exact one_mem _
  have hγ : ∀ PP, redFn βS PP (finE S g⁻¹) = (redFn βS PP (finE S g))⁻¹ := fun PP => by rw [map_inv, redFn_inv sg]
  have h1' : ∀ PP, (redFn βT PP (finE T (1 : GA D T)⁻¹))⁻¹ = 1 := fun PP => by
    rw [inv_one, map_one, redFn_one, inv_one]
  unfold GlobalTheory.FinZeta.levDatum
  by_cases hx : IsHalf (cA D e) x ∧ IsIntM (frMapAdj S T βS βT x)
  · have h1 := red_actO S T βS βT sg' s1 hx.2
    have h2 : ∀ PP, redM PP (frMapAdj S T βS βT (actO S T g⁻¹ 1⁻¹ x)) =
        ((redFn βS PP (finE S g))⁻¹).val * redM PP (frMapAdj S T βS βT x) := fun PP => by
      rw [h1.2 PP, hγ PP, h1' PP, Units.val_one, Matrix.mul_one]
    have hq := omegaQ_mul hTS Q m (fun PP => (redFn βS PP (finE S g))⁻¹) (fun _ => 1) (fun PP hP => inv_mem (hQ PP hP))
      (fun PP => redM PP (frMapAdj S T βS βT x))
    simp only [inv_one, Units.val_one, Matrix.mul_one, map_one, mul_one] at hq
    have hm := GlobalTheory.ChainOnto.omegaG_levelP_move D T.rank S.rank r t 0 ha hb ea eb Pg P (fun _ => m) (fun _ => 1)
      (fun PP => redFn βS PP (finE S g)) hG hP (fun PP => redM PP (frMapAdj S T βS βT x))
    rw [if_pos hx, if_pos ⟨isHalf_actO' _ _ hx.1, h1.1⟩, funext h2, hq,
      omegaG_levelDatum_zero_indep_chars T.rank r t ha Pg P (fun _ _ => 1) (fun _ => m) (fun _ => 1) (fun _ => 1) m
        (fun PP => ((redFn βS PP (finE S g))⁻¹).val * redM PP (frMapAdj S T βS βT x)),
      omegaG_levelDatum_zero_indep_chars T.rank r t ha Pg P (fun _ _ => 1) (fun _ => m) (fun _ => 1) (fun _ => 1) m
        (fun PP => redM PP (frMapAdj S T βS βT x)), hm]
    ring
  · rw [if_neg hx, if_neg, mul_zero]
    rintro ⟨h1, h2⟩
    have e' := GlobalTheory.AdelicLatMove.actO_actO_inv S T g (1 : GA D T) x
    have h3 := isHalf_actO' g (1 : GA D T) h1
    have h4 := (red_actO S T βS βT sg (by rw [map_one]; exact one_mem _) h2).1
    rw [e'] at h3 h4
    exact hx ⟨h3, h4⟩

end GlobalTheory.SourceLaw

namespace GlobalTheory.SourceLaw

open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues in
set_option maxHeartbeats 1000000 in

theorem om_src_law {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (i : Fin D.R.m) (t : T) (σ : D.what₂.LL →+* ℂ) (s : ℂ ≃+* ℂ) (P : LevelP R.Pg D.R.r ℂ) (cμ cη : (AE D)ˣ →* Circle)
    (m : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (Datum.WO (Vc D i) (Wc D i) → ℂ))
    (BW : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f₀ f : Datum.WO (Vc D i) (Wc D i) → ℂ)
    (c : CoefA (Vc D i)) (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (h : IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io) (κ : GA D (Vc D i))
    (hκ : κ ∈ Lev.levA (Vc D i) (levV R i t P m)) :
    ω (κ, 1) f = (Lev.levChi (Vc D i) (R.βV i) (datV i R.Pg (R.Q t) P m) κ)⁻¹ • f := by
  classical
  obtain ⟨hC, -, -, -, hch, hW, -, hlv, -, -, -⟩ := h
  rw [GlobalTheory.FinZeta.isLevelVec_iff] at hlv
  obtain ⟨hvac, e, he, hth⟩ := hlv
  have hL := hC.lev
  have hκG : κ ∈ GfC (Vc D i) := (Subgroup.mem_inf.1 hκ).1
  have hκL : finE (Vc D i) κ ∈ lev D.sp.cm (Vc D i).gram (R.βV i) (datV i R.Pg (R.Q t) P m) := (Subgroup.mem_inf.1 hκ).2
  have sV : finE (Vc D i) κ ∈ St (R.βV i) := parLev_St hκL.1
  have sW : finE (Wc D i) 1 ∈ St (R.βW i) := by rw [map_one]; exact one_mem _
  have dV := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βV i)
  have dW := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βW i)
  have fV := (hL.βV i).choose_spec.1
  have fW := (hL.βW i).choose_spec.1
  have hch' := GlobalTheory.T.conjugatedThetaCharacters_restriction_ramification R hL i t s cμ cη m hch
  have hres : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t, GlobalTheory.StepLaw.ResAt cμ PP (m PP) ∧ GlobalTheory.StepLaw.ResAt (cμ * cη⁻¹) PP (m PP) :=
    fun PP hP => hch'.1 PP (Finset.mem_union.1 hP)
  have hun := hch'.2.1 ((R.datWp i P).Pg ∪ R.Q t) (fun PP h => Finset.mem_union.2 h)
  have hvac1 := GlobalTheory.StepVecLaw.om_vac hW (D.sp.V_sig _) (D.sp.W_sig _)
    (fun τ => GlobalTheory.ZetaLaw.isCartanInv_one_of_onb (hC.models.BV i τ)) (GlobalTheory.Chain.VacVec.cart_isCartanInv (R.MW i σ)) dV dW
    fV fW hvac he (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) hun.1 hun.2 hκG (one_mem _) sV sW
  have rV : (Vc D i).rank = D.R.r + D.R.t := D.sp.V_rank _ (Nat.le_add_left _ _) i.2
  have rW : (Wc D i).rank = D.R.r := D.sp.W_rank _ (Nat.le_add_left _ _) i.2
  have hr : (Wc D i).rank ≤ (Vc D i).rank := by omega
  have hb : D.R.r ≤ (Vc D i).rank := (datV i R.Pg (R.Q t) P m).hr
  have hQ : ∀ PP ∈ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) ∈ blockTri (blk2 (Wc D i).rank) := fun PP hP => by
    rw [rW]; exact parLev_q hκL.1 hP
  have hlaw := levelDatum_target_under_sourceLevel_element (Vc D i) (Wc D i) (R.βV i) (R.βW i) D.R.r D.R.t (r_le_rank_Wc i) hb hr (by rw [rW]; ring)
    (by rw [rV]; ring) R.Pg (R.Q t) P m e κ sV (fun PP hP => parLev_g hκL.1 hP) hκL.2 hQ
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he
  have hcc : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hinf := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hfin := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D R.ψ (Vc D i) (Wc D i) cμ (cμ * cη⁻¹) ω hW (cA D e) _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D R.ψ hW.std (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) dV dW (cA D e) hcc hinf f₀ hvac.2.theta) hth κ 1
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i) dV dW fV fW κ 1 sV sW) _ _ (Units.ne_zero _)
    hvac1 hlaw
  rw [hfin]
  congr 1
  have hd : Disjoint (R.datWp i P).Pg (R.Q t) := (GlobalTheory.T.levelCharacters_unramified_off_levelPlaces D T R.toLevCh A.μ0 hL t).1
  have hQf : ∀ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ *
      (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹ =
      (m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ := fun PP hP => by
    have h1 := (GlobalTheory.VecInv.TwoBlockDet.det_blocks (kP PP) _ _ 0 hr (redFn (R.βV i) PP (finE (Vc D i) κ))).1 (hQ PP hP)
    have e1 : dBlk (blk2 (Wc D i).rank) 1 (redFn (R.βV i) PP (finE (Vc D i) κ)) =
        dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ)) := by rw [rW]
    have e2 : upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹ = (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ)))⁻¹ :=
      extendOne_inv _ (hQ PP hP)
    rw [e2, map_inv, map_inv, inv_inv, h1, e1, map_mul, mul_inv, mul_comm, ← mul_assoc, mul_inv_cancel,
      one_mul]
  have hone : ∀ PP, m PP (Matrix.GeneralLinearGroup.det (redFn (R.βW i) PP (finE (Wc D i) 1))) = 1 := fun PP => by
    rw [map_one, redFn_one, map_one, map_one]
  unfold Lev.levChi levFn
  rw [extendOne_of_mem _ hκL.2]
  have hchi : (datV i R.Pg (R.Q t) P m).P.chi ⟨rTup (R.βV i) (datV i R.Pg (R.Q t) P m) (finE (Vc D i) κ), hκL.2⟩ =
      P.chi ⟨fun PP => upperLeftBlock hb (redFn (R.βV i) PP.1 (finE (Vc D i) κ)), hκL.2⟩ := rfl
  rw [hchi]
  simp only [IndefiniteRowSideFullHecke.TwistedLevelValues.datV, hone, mul_one]
  rw [← Units.coe_prod, ← Units.val_mul, ← Units.val_mul, ← Units.val_inv_eq_inv_val]
  congr 1
  rw [Finset.prod_union hd]
  have hX2 : (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹) *
      ∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹ =
      (∏ PP ∈ R.Q t, m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ := by
    rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl hQf, Finset.prod_inv_distrib]
  generalize (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹) = X2 at hX2 ⊢
  generalize (∏ PP ∈ R.Q t, (m PP (Matrix.GeneralLinearGroup.det (upperLeftBlock hr (redFn (R.βV i) PP (finE (Vc D i) κ))⁻¹)))⁻¹) = Z at hX2 ⊢
  obtain rfl : X2 = (∏ PP ∈ R.Q t, m PP (dBlk (blk2 D.R.r) 1 (redFn (R.βV i) PP (finE (Vc D i) κ))))⁻¹ * Z⁻¹ := by
    rw [← hX2, mul_inv_cancel_right]
  rw [Finset.prod_inv_distrib]
  simp only [zero_add]
  rw [show (R.datWp i P).Pg = R.Pg from rfl]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end GlobalTheory.SourceLaw

namespace GlobalTheory.SourceLaw

theorem sourceLevelLaw : GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL.LocalIntegralSingleBlock → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.PlaceModels D → SourceLevelLawC R F := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F _ i t σ s P cμ cη m ω BW f₀ f c io h κ hκ Q
  have hf := om_src_law R F i t σ s P cμ cη m ω BW f₀ f c io h κ hκ
  obtain ⟨hC, -, -, -, -, hW, -, -, hpt, -, -⟩ := h
  exact GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ ω hC.models.inf hW _ _ _ _ f hpt κ
    (Subgroup.mem_inf.1 hκ).1 1 (one_mem _) _ hf Q

end GlobalTheory.SourceLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockCreationOperatorMultiplierAntilinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem map_inv_ringHom {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ} (M : Matrix (Fin n) (Fin n) K) :
    (M⁻¹).map f = (M.map f)⁻¹ := by
  have h1 : M.adjugate.map f = (M.map f).adjugate := by
    have := RingHom.map_adjugate f M; simpa [RingHom.mapMatrix_apply] using this
  have h2 : (M.map f).det = f M.det := by
    have := RingHom.map_det f M; simpa [RingHom.mapMatrix_apply] using this.symm
  rw [Matrix.inv_def, Matrix.inv_def, Matrix.map_smul' _ _ _ (map_mul f), h1, h2, Ring.inverse_eq_inv',
    Ring.inverse_eq_inv', map_inv₀]

theorem formAt_eq_omAt (S T : HSp D) (τ : D.what₂.Tau) (x y : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    GlobalTheory.OrientedHeis.formAt S T τ x y = GlobalTheory.VacUnique.omAt S T τ x y := by
  unfold GlobalTheory.OrientedHeis.formAt GlobalTheory.VacUnique.omAt GlobalTheory.VacUnique.hAt
  congr 3
  rw [gramAt, gramAt, ← map_inv_ringHom]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.map_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

theorem omF_eq {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B z e = GlobalTheory.VacUnique.omO S T (fmR A B z) (fmR A B e) := by
  rw [GlobalTheory.VacUnique.omO_apply]
  exact Finset.sum_congr rfl fun τ _ => formAt_eq_omAt S T τ _ _

theorem cplxO_smulC' {m n : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ) (c : ℂ)
    (x : Matrix (Fin m) (Fin n) ℂ) : cplxO s t (c • x) = c • cplxO s t x := by
  simp only [cplxO, Matrix.mul_smul, Matrix.smul_mul]
  exact smul_comm _ _ _

theorem cplxO_sum' {m n p q : ℕ} (s : Matrix (Fin n) (Fin n) ℂ) (t : Matrix (Fin m) (Fin m) ℂ)
    (x : Fin p → Fin q → Matrix (Fin m) (Fin n) ℂ) :
    cplxO s t (∑ i, ∑ j, x i j) = ∑ i, ∑ j, cplxO s t (x i j) := by
  simp only [cplxO, Matrix.mul_sum, Matrix.sum_mul, Finset.smul_sum]

theorem fmR_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (I • z) = GlobalTheory.VacUnique.jO S T A.cart B.cart (fmR A B z) := by
  funext τ
  show fockMat A B τ ((I • z) τ) = cplxO (A.cart τ) (B.cart τ) (fockMat A B τ (z τ))
  have hs := (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ).1
  have ht := (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B τ).1
  unfold fockMat
  rw [cplxO_sum']
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.VacUnique.cplxO_add, cplxO_smulC', cplxO_smulC', GlobalTheory.RealSymplForm.cplxO_cplxO hs ht]
  have e1 : ((I • z) τ i j).re = -(z τ i j).im := by simp
  have e2 : ((I • z) τ i j).im = (z τ i j).re := by simp
  rw [e1, e2]
  simp only [smul_neg, Complex.ofReal_neg, neg_smul]
  abel

theorem fmR_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z w : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (z + w) = fmR A B z + fmR A B w := by
  funext τ
  show fockMat A B τ (z τ + w τ) = fockMat A B τ (z τ) + fockMat A B τ (w τ)
  simp only [fockMat, Pi.add_apply, Complex.add_re, Complex.add_im, Complex.ofReal_add, add_smul,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  abel

theorem fmR_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (c : ℝ) (z : VCx D.what₂.Tau S.rank T.rank) :
    fmR A B (c • z) = c • fmR A B z := by
  funext τ
  show fockMat A B τ (c • z τ) = c • fockMat A B τ (z τ)
  simp only [fockMat, Pi.smul_apply, Complex.smul_re, Complex.smul_im, smul_eq_mul, Complex.ofReal_mul,
    mul_smul, Finset.smul_sum, smul_add]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.coe_smul]

theorem omF_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z w e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (z + w) e = omF A B z e + omF A B w e := by
  rw [omF_eq, omF_eq, omF_eq, fmR_add, map_add, LinearMap.add_apply]

theorem omF_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (c : ℝ) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (c • z) e = c * omF A B z e := by
  rw [omF_eq, omF_eq, fmR_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem omF_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (I • z) e = -omF A B z (I • e) := by
  obtain ⟨hJJ, -, hinv, -⟩ := GlobalTheory.RealSymplForm.form_alt_inv_def D S T A.cart B.cart
    (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A) (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)
  rw [omF_eq, omF_eq, fmR_I, fmR_I]
  set J := GlobalTheory.VacUnique.jO S T A.cart B.cart
  set x := fmR A B z
  set y := fmR A B e
  have hy : y = -J (J y) := by rw [hJJ, neg_neg]
  conv_lhs => rw [hy]
  rw [map_neg, hinv]

theorem omF_I_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (z e : VCx D.what₂.Tau S.rank T.rank) :
    omF A B (I • z) (I • e) = omF A B z e := by
  rw [omF_I, smul_smul, I_mul_I, neg_one_smul, omF_eq, omF_eq]
  have : fmR A B (-e) = -fmR A B e := by
    have h := fmR_smul A B (-1) e
    rw [neg_one_smul, neg_one_smul] at h
    exact h
  rw [this, map_neg, neg_neg]

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem gD_add (c : ι → ℝ) (z w e : VCx ι a b) : gD c (z + w) e = gD c z e + gD c w e := by
  simp only [gD, Pi.add_apply, add_mul, Complex.add_re, mul_add, Finset.sum_add_distrib]

theorem gD_smul (c : ι → ℝ) (r : ℝ) (z e : VCx ι a b) : gD c (r • z) e = r * gD c z e := by
  simp only [gD, Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, Complex.real_smul, mul_assoc, Complex.re_ofReal_mul]
  ring

theorem gD_I (c : ι → ℝ) (z e : VCx ι a b) : gD c (I • z) e = -gD c z (I • e) := by
  simp only [gD, ← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

theorem gD_I_I (c : ι → ℝ) (z e : VCx ι a b) : gD c (I • z) (I • e) = gD c z e := by
  simp only [gD]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
  ring

end GlobalTheory.FockTransl.Jet

namespace GlobalTheory.FockTransl.Jet

open Complex

variable {D : D7}

theorem lamF_add {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z w : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (z + w) = lamF A B l z + lamF A B l w := by
  simp only [lamF, omF_add, gD_add]
  push_cast
  ring

theorem lamF_smul {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (r : ℝ) (z : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (r • z) = r * lamF A B l z := by
  simp only [lamF, omF_smul, gD_smul]
  push_cast
  ring

theorem lamF_I {S T : HSp D} (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank)
    (z : VCx D.what₂.Tau S.rank T.rank) : lamF A B l (I • z) = -I * lamF A B l z := by
  simp only [lamF]
  rw [omF_I_I, omF_I, gD_I_I, gD_I]
  push_cast
  linear_combination (-(1 / 2 : ℂ) * (Real.pi : ℂ) * (omF A B z (Formalism.L2.Ker.coordX l) : ℂ) +
    (1 / 4 : ℂ) * (gD (fw D) z (I • Formalism.L2.Ker.coordX l) : ℂ)) * Complex.I_sq

theorem lamF_antilinear : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (l : DVar D.what₂.Tau S.rank T.rank), (∀ a b, GlobalTheory.FockTransl.Jet.lamF A B l (a + b) = GlobalTheory.FockTransl.Jet.lamF A B l a + GlobalTheory.FockTransl.Jet.lamF A B l b) ∧ ∀ (t : ℂ) a, GlobalTheory.FockTransl.Jet.lamF A B l (t • a) = conj t * GlobalTheory.FockTransl.Jet.lamF A B l a := by
  intro D S T A B l
  refine ⟨fun a b => lamF_add A B l a b, fun t a => ?_⟩
  have e : t • a = (t.re : ℝ) • a + (t.im : ℝ) • (I • a) := by
    funext τ i j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul]
    conv_lhs => rw [← Complex.re_add_im t]
    ring
  have hc : conj t = (t.re : ℂ) - t.im * I := by apply Complex.ext <;> simp
  rw [e, lamF_add, lamF_smul, lamF_smul, lamF_I, hc]
  ring

end GlobalTheory.FockTransl.Jet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodSplitPlaceOfFamilyPrimeBaseTuple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

namespace GlobalTheory.GoodSplitFam

theorem good_split_pl : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3), R.WeakCharacterisation F → R.toRealDat.ExAt → ∀ P, GlobalTheory.Hk3.Good R.toRealDat A3.A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∃ P0 ∈ A3.A.ok A3.A.μ0, R.pl P0 = P ∧ A3.A.q P0 ≠ 0 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F hW e P hG hP
  obtain ⟨hC, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW e
  obtain ⟨hQ0, -, -, hfam⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R.toRealDat F.lv2 hC.lev
  have hSb : R.Sb = R.Pg := hW.allPl
  have hci : Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal = (Formalism.DivisionValues.conjPl P).asIdeal :=
    GlobalTheory.InertValLab.conjIdeal_eq_conjPl P
  have hsplit : Formalism.IndefR.Bridge.SplitOff P (R.Sb : Set (Pl D.host.E)) := by
    refine ⟨?_, ?_, ?_⟩
    · rw [hci]
      intro h
      exact hP (HeightOneSpectrum.ext h)
    · intro hm
      have hm' : P ∈ R.Pg := by rw [← hSb]; exact hm
      exact (hG P (Or.inl hm')).1 rfl
    · intro Q hQ h
      rw [hci] at h
      have hQ' : Q ∈ R.Pg := by rw [← hSb]; exact hQ
      have hQe : Q = Formalism.DivisionValues.conjPl P := HeightOneSpectrum.ext h
      apply (hG Q (Or.inl hQ')).2
      rw [GlobalTheory.GoodPrimes.isConjPl_iff, hQe, Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl]
  obtain ⟨P0, hP0⟩ := hC.fam.pl_onto P hsplit
  obtain ⟨gramR, c0R, c0L, htie⟩ := hC.fam.tie
  have hok : P0 ∈ A3.A.ok A3.A.μ0 := by
    rw [htie.ok, hQ0, hP0]
    simpa using hsplit
  refine ⟨P0, hok, hP0, ?_⟩
  rw [(hfam hC.fam A3.A.μ0 P0 hok).2.2]
  intro h0
  exact (R.pl P0).ne_bot (Ideal.absNorm_eq_zero_iff.mp h0)

end GlobalTheory.GoodSplitFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeEigenvaluesEqOfDualEnlargingLabelsSplit
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.Hk3.LabDetRows

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem dual_eq_of_split : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ SF, GlobalTheory.Hk3.IsSF R SF → ∀ (c c' : Pl D.host.E → List ℤ → ℂ), GlobalTheory.Hk3.EEc R SF c ≠ ⊥ → GlobalTheory.Hk3.EEc R SF c' ≠ ⊥ → (∀ P, GlobalTheory.Hk3.Good R A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ k ≤ (Yc D 0).rank, c P (dualLab (splitLab (Yc D 0).rank k)) = c' P (dualLab (splitLab (Yc D 0).rank k))) → ∀ P, GlobalTheory.Hk3.Good R A.μ0 P → Formalism.DivisionValues.conjPl P ≠ P → ∀ d, GlobalTheory.Hk3.IsLab (Yc D 0) P d → c P (dualLab d) = c' P (dualLab d) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC SF hSF c c' hc hc' hs P hP hcP
  obtain ⟨-, hgood, hoff, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  obtain ⟨n, hβ⟩ := hC.lev.βY 0 (by have := D.R.two_le_m; omega)
  have hlev := fun (P : Pl D.host.E) (hP : Good R A.μ0 P) =>
    GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) ((D.host.g 0 * D.host.g 1) ^ n) (R.dat0 R.triv) hβ P
      (by
        rw [Nat.cast_pow]
        exact fun h => (hgood A.μ0 P hP).1 (P.isPrime.mem_of_pow_mem _ h))
      (by
        intro PP hPP
        refine hP PP (hPP.imp id ?_)
        intro h
        exact absurd h (Finset.notMem_empty _))
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  obtain ⟨x', hx', hx0'⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc'
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hu : R.HE.e x ≠ 0 := fun h => hx0 (inj (by rw [h, map_zero]))
  have hu' : R.HE.e x' ≠ 0 := fun h => hx0' (inj (by rw [h, map_zero]))
  have hp := (LabDet.mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_comap.1 hx)
  have hp' := (LabDet.mem_partFull _ _ _ _ _ _ _).1 (Submodule.mem_comap.1 hx')
  have hP' : Good R A.μ0 (Formalism.DivisionValues.conjPl P) := (hgood _ P hP).2.1
  have hcc : Formalism.DivisionValues.conjPl (Formalism.DivisionValues.conjPl P) = P := Formalism.DivisionValues.ValuationRepresentative.conjPl_conjPl P
  exact eq_of_split (rRep (R.MY 0)) P hcP _ _ hu hu'
    (fun k hk => mult_lev _ _ _ _ _ hp.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2)
    (fun k hk => mult_lev _ _ _ _ _ hp'.1 k ((hlev P hP).1 k hk).1 ((hlev P hP).1 k hk).2)
    (fun d => c P (dualLab d)) (fun d => c' P (dualLab d))
    (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d)) (fun d => c' (Formalism.DivisionValues.conjPl P) (dualLab d))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp'.2 _ _ _ (((hlev P hP).2.1 SF d _).2 ⟨(hoff SF hSF P).2 hP, sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩))
    (fun d hd => by
      rw [opOf_single, sum_rRep]
      exact hp'.2 _ _ _ (((hlev _ hP').2.1 SF d _).2 ⟨(hoff SF hSF _).2 hP', sphOp_rep hd⟩))
    (hs P hP hcP) (hs _ hP' (by rw [hcc]; exact fun h => hcP h.symm))

end GlobalTheory.Hk3.LabDetRows

end
end

