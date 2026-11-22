import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0855
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0741
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.StandardHermitianSpace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0378
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepVectorTwoLevelLaw
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto.StepVecLawBoth

set_option maxHeartbeats 1000000 in
open Classical in

theorem stepLevLawT (D : D7) (c : Com D) (hc : c.Is) (k : ℕ) (hk : k < D.R.m) (s s' : PiLocalization₂ D) (hs : s.Is c k)
    (hs' : s'.Is c (k + 1)) (ω : GA D s.V × GA D s'.V →* Module.End ℂ (WO s.V s'.V → ℂ))
    (hW : IsWeilDatumO c.ψ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) ω) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (f₀ f : WO s.V s'.V → ℂ)
    (hv : IsStepVecOf c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) s.Λ s'.Λ s.β s'.β s.L (c.chi (k + 1)) ∅ ξ f₀ f) :
    ∀ κ ∈ Lev.levG s'.V s'.β s'.L, ω (1, κ) f = (Lev.levChi s'.V s'.β s'.L κ)⁻¹ • f := by
  intro κ hκ
  obtain ⟨hr, ξ1, hL⟩ := hs.lev
  obtain ⟨hr', ξ2, hL'⟩ := hs'.lev
  rw [hL] at hv
  rw [hL'] at hκ ⊢
  have ea : s.V.rank = D.R.r + k * D.R.t := hs.rank
  have eb : s'.V.rank = D.R.r + (k + 1) * D.R.t := hs'.rank
  obtain ⟨hf, e, he, hΘ⟩ := hv
  have he' : IsIdemSum e c.Pg := by rw [← Finset.union_empty c.Pg]; exact he
  obtain ⟨hres, uS, uT⟩ := GlobalTheory.T.thetaLiftChain_splittingCharacters_residue_unramified D c hc k hk
  have hlev : Lev.finE s'.V κ ∈ lev D.sp.cm s'.V.gram s'.β
      (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B) := hκ.2
  have sg : Lev.finE s.V 1 ∈ St s.β := by rw [map_one]; exact Subgroup.one_mem _
  have sh : Lev.finE s'.V κ ∈ St s'.β := parLev_St hlev.1
  have h1 := GlobalTheory.StepVecLaw.om_vac hW hs.sigOK hs'.sigOK (GlobalTheory.Chain.VacVec.cart_isCartanInv s.M)
    (GlobalTheory.Chain.VacVec.cart_isCartanInv s'.M) hs.selfDual hs'.selfDual hs.frame hs'.frame hf he'
    (fun PP hP => (hres PP hP).1) (fun PP hP => (hres PP hP).2) uS uT (Subgroup.one_mem _) hκ.1 sg sh
  set H : ∀ PP : Pl D.host.E, GL (Fin s'.V.rank) (kP PP) := fun PP => redFn s'.β PP (Lev.finE s'.V κ) with hH
  have hPeq : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).P = c.P := by simp [Lev.datY]
  have hcg : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).cg = c.chi := by simp [Lev.datY]
  have hP : (fun PP : ↥c.Pg => upperLeftBlock hr' (H PP.1)) ∈ c.P.H := by
    have := hlev.2
    rw [hPeq] at this
    exact this
  have hBT : ∀ PP ∈ c.Pg, H PP ∈ blockTri (blkOf D.R.r D.R.t) := fun PP hPP => parLev_g hlev.1 hPP
  have h1' : ω (1, κ) f₀ = ((∏ PP ∈ c.Pg, (c.chi (k + 1) PP (GeneralLinearGroup.det (H PP)))⁻¹ : ℂˣ) : ℂ) • f₀ := by
    rw [h1]
    congr 2
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [map_one, redFn_one, MonoidHom.inv_apply, inv_one, one_mul, hH]
  have hoT := GlobalTheory.T.levelPlacesDatum_inv_left_mul_target_level D s.V.rank s'.V.rank D.R.r D.R.t k hr hr' ea eb c.Pg c.P c.chi ξ1 H hBT hP
  have h2 := GlobalTheory.T.weilRep_theta_datum_half_eq_smul D c.ψ s.V s'.V _ _ ω hW e _ f₀ _ f
    (GlobalTheory.T.schrodingerIntertwiner_schwartzBruhat_isTheta D c.ψ hW.std s.V s'.V s.Λ s'.Λ hs.selfDual hs'.selfDual e (GlobalTheory.PlaceDatum.idemSum_mul_self he)
      (GlobalTheory.PlaceDatum.infPart_idemSum he) f₀ hf.2.theta) hΘ 1 κ
    (GlobalTheory.T.mem_homLattice_iff_frameStabilizer_act_mem D s.V s'.V s.Λ s'.Λ s.β s'.β hs.selfDual hs'.selfDual hs.frame hs'.frame 1 κ sg sh) _
    ((((c.P.chi ⟨_, hP⟩ * ∏ PP ∈ c.Pg, ∏ i ∈ Finset.range (k + 1),
        c.chi (i + 1) PP (dBlk (blkOf D.R.r D.R.t) (i + 1) (H PP)))⁻¹ *
      ∏ PP ∈ c.Pg, c.chi (k + 1) PP (GeneralLinearGroup.det (H PP)) : ℂˣ) : ℂ)) (Units.ne_zero _) h1' (fun x => by
      obtain ⟨i1, i2⟩ := GlobalTheory.T.frameMatrix_movedHom_integral_reductions D s.V s'.V s.β s'.β 1 κ sg sh x
      have i0 : IsHalf e (actO s.V s'.V 1⁻¹ κ⁻¹ x) ↔ IsHalf e x :=
        ⟨fun H' => GlobalTheory.AdelicLatMove.actO_actO_inv s.V s'.V 1 κ x ▸ GlobalTheory.SplitHecke.isHalf_actO 1 κ H',
          fun H' => GlobalTheory.SplitHecke.isHalf_actO _ _ H'⟩
      by_cases hx : IsHalf e x ∧ IsIntM (frMapO s.V s'.V s.β s'.β x)
      · beta_reduce
        rw [if_pos hx, if_pos ⟨i0.2 hx.1, i1.2 hx.2⟩, funext (i2 hx.2), StepLevLaw.omegaQ_empty, StepLevLaw.omegaQ_empty,
          mul_one, mul_one]
        simp only [map_one, redFn_one, Units.val_one, Matrix.mul_one]
        exact hoT (fun PP => redM PP (frMapO s.V s'.V s.β s'.β x))
      · beta_reduce
        rw [if_neg hx, if_neg fun H' => hx ⟨i0.1 H'.1, i1.1 H'.2⟩, mul_zero])
  rw [h2]
  congr 1
  have hchi : (Lev.datY s'.V.rank D.R.r D.R.t (k + 1) hr' c.Pg ∅ c.P c.chi ξ2 Lev.Frm.B).P.chi ⟨_, hlev.2⟩ =
      c.P.chi ⟨_, hP⟩ := rfl
  unfold Lev.levChi levFn
  rw [extendOne_of_mem _ hlev.2, hchi]
  simp only [Lev.datY, ↓reduceIte, Finset.prod_empty, mul_one]
  rw [Finset.prod_inv_distrib, ← Units.val_mul, ← Units.val_inv_eq_inv_val]
  congr 1
  rw [mul_comm _ (∏ PP ∈ c.Pg, c.chi (k + 1) PP (GeneralLinearGroup.det (H PP))), inv_mul_cancel_left]

theorem vecLaw : ∀ D : D7, ForStep D fun _ _ s s' p => VecLaw p.ω (Lev.levG s.V s.β s.L) (Lev.levChi s.V s.β s.L)
    (Lev.levG s'.V s'.β s'.L) (fun κ => (Lev.levChi s'.V s'.β s'.L κ)⁻¹) p.f := by
  intro D _ c hc k hk s s' hs hs' p hp
  obtain ⟨ξ, f₀, hv⟩ := hp.vec
  refine ⟨fun κ hκ => (StepLevLaw.stepLevLaw D c hc ⟨k, hk⟩ s s' hs hs' p.ω hp.weil ξ f₀ p.f hv κ hκ).2, ?_⟩
  exact stepLevLawT D c hc k hk s s' hs hs' p.ω hp.weil ξ f₀ p.f hv

end GlobalTheory.ChainOnto.StepVecLawBoth

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaFourierSumEqSumHeisenbergTranslates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfFourier

theorem thetaAt_eq_sum_heis_translates : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T)) (f₀ Φ f : WO S T → ℂ) (ι : Type) (s : Finset ι) (K : ι → ℂ) (xs ys : ι → WO S T) (k : ℕ), 0 < k → IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ 1 f₀ Φ f → (∀ i ∈ s, IsHalf e (xs i)) → (∀ i ∈ s, IsHalf (cA D e) (ys i)) → (∀ i ∈ s, ∀ u ∈ Λ, ψ (symplO S T (k • u) (ys i)) = 1) → (∀ t, Φ t = ∑ i ∈ s, K i * (ψ (symplO S T (t + xs i) (ys i)) * halfInd e Λ (t + xs i))) → f = ∑ i ∈ s, K i • heisO ψ S T (xs i) (heisO ψ S T (ys i) f₀) := by
  intro D ψ S T e Λ f₀ Φ f ι s K xs ys k hk hθ hx hy hΛ hΦ
  classical
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hθ
  have hvac : Tm (halfInd e Λ) = f₀ := by simpa using hTm.vac

  set g : ι → WO S T → ℂ := fun i t => ψ (symplO S T t (ys i)) * halfInd e Λ t with hg
  have hhalf : ∀ t, halfInd e Λ t ≠ 0 → t ∈ Λ ∧ IsHalf e t := by
    intro t ht
    by_contra h
    exact ht (by simp [halfInd, h])
  have hSB : ∀ i ∈ s, IsSBHalf e Λ (g i) := by
    intro i hi
    refine ⟨fun t ht => ?_, k, hk, fun u hu hh t => ?_, fun t ht => ?_⟩
    · exact (hhalf t (right_ne_zero_of_mul ht)).2
    · have hku : k • u ∈ Λ := Λ.nsmul_mem hu k
      have hkh : IsHalf e (k • u) := by
        intro a b
        change e * ((k • u : Matrix _ _ (AE D)) a b) = (k • u : Matrix _ _ (AE D)) a b
        rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hh a b]
      have hind : halfInd e Λ (t + k • u) = halfInd e Λ t := by
        have : (t + k • u ∈ Λ ∧ IsHalf e (t + k • u)) ↔ (t ∈ Λ ∧ IsHalf e t) := by
          rw [Λ.add_mem_cancel_right hku]
          refine and_congr_right fun _ => forall_congr' fun a => forall_congr' fun b => ?_
          rw [Matrix.add_apply, mul_add, hkh a b, add_left_inj]
        simp only [halfInd, this]
      simp only [hg, hind, GlobalTheory.LatVac.symplO_add_left, AddChar.map_add_eq_mul, hΛ i hi u hu, mul_one]
    · exact Λ.nsmul_mem (hhalf t (right_ne_zero_of_mul ht)).1 k
  have hΦ' : Φ = ∑ i ∈ s, K i • fun t => g i (t + xs i) := by
    funext t
    rw [hΦ t, Finset.sum_apply]
    rfl
  rw [hall Tm hTm, hΦ', map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_smul, hTm.trans _ (hSB i hi) (xs i) (hx i hi)]
  congr 2
  have : g i = fun t => ψ (symplO S T t (ys i)) * halfInd e Λ t := rfl
  rw [this, hTm.modul _ (GlobalTheory.isSBHalf_halfInd e Λ) (ys i) (hy i hi), hvac]

end GlobalTheory.HalfFourier
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftDatumIsNonzeroFockVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftFockVac

theorem levVec_fockVac : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), ∀ i t σ s P cμ cη m ω BW f₀ f c io, IsLiftDataC R F i t σ s P cμ cη m ω BW f₀ f c io → ∀ (μ : Measure (WO (Vc D i) (Wc D i))) (𝓧 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓧 → l2 μ 𝓧 f f ≠ 0 ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) f ∧ (∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1) ∧ ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i σ) τ)) f := by
  classical
  intro D G _ _ Pl0 T A Ks _ _ _ R F i t σ s P cμ cη m ω BW f₀ f c io h μ 𝓧 hμ
  have hθf := (GlobalTheory.FinZeta.levVec_vacFin R F i t σ s P cμ cη m ω BW f₀ f c io h).1
  obtain ⟨hC, -, -, -, -, hW, -, hlv, -, -, -⟩ := h
  obtain ⟨⟨hψ, hv⟩, e, he, hth⟩ := hlv
  have hinf : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.PlaceVec.idemSum_infPart he)
  have hinf' : infPart D (cA D (cA D e)) = 0 := by
    rw [GlobalTheory.DualPairCheck.cA_cA]; exact GlobalTheory.PlaceVec.idemSum_infPart he
  have hS := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have hT := GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hr : (Wc D i).rank ≤ (Vc D i).rank := (D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)
  have hf0 : f ≠ 0 := by
    have h00 : f₀ ≠ 0 := by
      rintro rfl
      obtain ⟨⟨p, hp⟩, h2⟩ := hv.norm
      have := h2 p hp
      simp [nrm2] at this
    obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
    rw [hall Tm hTm]
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum he
    have hee : e * e = e := ho.idem
    obtain ⟨-, hFS, -⟩ := hC.lev.βV i
    obtain ⟨-, hFT, -⟩ := hC.lev.βW i
    have hSB := GlobalTheory.FinZeta.isSBHalf_levDatum D _ _ _ _ _ _ (R.datWp i P) (R.Q t) m _ e hS hT hFS hFT he
    refine GlobalTheory.PlaceModelInj.placeModel_ne_zero D R.ψ _ _ _ _ (cA D e) f₀ _ Tm hψ hS hT ho.conj.idem
      (by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he.2]) hinf hTm h00 hSB ?_
    obtain ⟨x, hx, hx'⟩ := GlobalTheory.AdjDatumNe.exists_half_frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) hee
      (GlobalTheory.AdjDatumNe.rectOne _ _ _)
    obtain ⟨hi, hres⟩ := GlobalTheory.AdjDatumNe.idemSum_res he
    have hint : IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) := by
      rw [hx']; exact GlobalTheory.AdjDatumNe.isIntM_smul_rectOne hi _ _
    have hred : ∀ PP ∈ (R.datWp i P).Pg ∪ R.Q t,
        redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) = GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _ := by
      intro PP hPP
      rw [hx', GlobalTheory.AdjDatumNe.redM_smul_rectOne hi PP (hres PP hPP)]
      rfl
    intro hz
    have := congrFun hz x
    rw [if_pos ⟨hx, hint⟩, GlobalTheory.PlaceDatum.omegaG_congr _ m _ (fun PP => GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _)
      fun PP hP => hred PP (Finset.mem_union_left _ hP),
      GlobalTheory.PlaceVec.omegaQ_congr _ _ _ _ (y' := fun PP => GlobalTheory.Chain.StepVac.rectOne (kP PP) _ _)
      fun PP hP => hred PP (Finset.mem_union_right _ hP)] at this
    exact mul_ne_zero (GlobalTheory.Chain.StepVac.omegaG_rectOne hr _ m) (GlobalTheory.Chain.StepVac.omegaQ_rectOne le_rfl hr _ m _) this
  refine ⟨?_, hθf, fun τ => GlobalTheory.RawLift.isCartanInv_one_of_onb (hC.models.BV i τ), fun τ => ?_⟩
  · have h1 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hW.std hθf hf0 hμ
    have e1 : l2 μ 𝓧 f f = GlobalTheory.RawLift.thetaIP μ 𝓧 f f := by
      show (∫ w in 𝓧, f w * starRingEnd ℂ (f w) ∂μ) = ∫ w in 𝓧, star (f w) * f w ∂μ
      congr 1
      funext w
      rw [mul_comm]
      rfl
    rw [e1]
    exact h1
  · exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hv.inf hinf hinf' hth hv.theta hθf (hv.fock τ)

end GlobalTheory.LiftFockVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftFockVectorsSphericalPrincipalFixed
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

noncomputable section

namespace GlobalTheory.ThPFock

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem redFn_of_mem_prin (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (hκ : κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) :
    κ ∈ GfC (Vc D i) ∧ finE (Vc D i) κ ∈ UA D.sp.cm (Vc D i).gram ∧ finE (Vc D i) κ ∈ St (R.βV i) ∧
      ∀ PP ∈ R.Pg ∪ R.Q t, redFn (R.βV i) PP (finE (Vc D i) κ) = 1 := by
  have h := mem_levA.1 hκ
  have hP : (prinDat (Vc D i) (R.Pg ∪ R.Q t)).P.H = ⊥ := by
    rfl
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.PrincipalLevel.mem_lev_whole _ _ _ rfl rfl hP _).1 h.2
  exact ⟨h.1, h1, h2, h3⟩

theorem is_lift_of_mem_principal_congruence (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (hκ : κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) : IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 κ := by
  obtain ⟨h0, h1, h2, h3⟩ := redFn_of_mem_prin R i t hκ
  refine ⟨h0, mem_parLev.2 ⟨h1, h2, fun PP hPP => ?_, fun PP hPP => ?_⟩, ?_⟩
  · rw [h3 PP (Finset.mem_union_left _ hPP)]
    exact Subgroup.one_mem _
  · rw [h3 PP (Finset.mem_union_right _ hPP)]
    exact Subgroup.one_mem _
  · funext PP
    show upperLeftBlock _ (redFn (R.βV i) PP.1 (finE (Vc D i) κ)) = 1
    rw [h3 PP.1 (Finset.mem_union_left _ PP.2)]
    exact blockDiagonalExtendByOnePrimeField_one _ _

theorem levChi_flag_of_mem_prin (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) {κ : GA D (Vc D i)}
    (hκ : κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t)) : levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ = 1 := by
  obtain ⟨-, -, -, h3⟩ := redFn_of_mem_prin R i t hκ
  have e : levFn (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) = levFn (R.βV i) (flagL (R.datVt i t)) 1 := by
    have hr : rTup (R.βV i) (flagL (R.datVt i t)) (finE (Vc D i) κ) = rTup (R.βV i) (flagL (R.datVt i t)) 1 := by
      funext PP
      show upperLeftBlock _ (redFn (R.βV i) PP.1 (finE (Vc D i) κ)) = upperLeftBlock _ (redFn (R.βV i) PP.1 1)
      rw [h3 PP.1 (Finset.mem_union_left _ PP.2), redFn_one]
    unfold levFn
    rw [hr]
    congr 1
    · congr 1
      exact Finset.prod_congr rfl fun PP hPP => Finset.prod_congr rfl fun c _ => by
        rw [h3 PP (Finset.mem_union_left _ hPP), redFn_one]
    · exact Finset.prod_congr rfl fun PP hPP => by
        rw [h3 PP (Finset.mem_union_right _ hPP), redFn_one]
  have h1 := GlobalTheory.RawLift.LevelFix.levChi_flag_one R i t
  unfold levChi at h1 ⊢
  rw [e]
  rw [(finE (Vc D i)).map_one] at h1
  exact h1

theorem is_lift_one_principal_level (R : RealDat D A Ks) (i : Fin D.R.m) : IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
  ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact rTup_one⟩

end GlobalTheory.ThPFock

open GlobalTheory.ThPFock in

theorem GlobalTheory.ThPFock.fock_sph_prin : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t P, (∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ)) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ptP i t P) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff R.ψ (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i)) (GlobalTheory.AdelicU.frameLat (Wc D i)) (under (R.Pg ∪ R.Q t)) (R.ptP i t P) ∧ ∀ κ ∈ prin (Vc D i) (R.βV i) (R.Pg ∪ R.Q t), R.ωP i t (κ, 1) (R.ptP i t P) = R.ptP i t P := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t P
  have hC := hG.core
  have hθ : IsInfFam R.θ := hC.models.inf
  have hψ : IsStdChar D R.ψ (-1) := (hC.thP.ωP i t).std
  have cS : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1 := fun τ => GlobalTheory.RawLift.isCartanInv_one_of_onb (hC.models.BV i τ)
  have cT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) :=
    fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart (R.MW i (sg0 D A)) τ
  have hpt : ∀ φ, IsThetaFunO R.ψ (Vc D i) (Wc D i) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1)
      (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t) φ) := hC.thP.pt_theta i t
  have hvθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hC.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hvv : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t) :=
    GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hC.thP.vP i t) hvθ
  refine ⟨cT, ?_, ?_, ?_⟩
  · exact GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ cS cT (R.BV i) (onb (R.MW i (sg0 D A))) hvθ hvv P
  · obtain ⟨hvac, e, he, hth⟩ := hC.thP.vP i t
    have hV : (R.ΛV i : Set (Fin (Vc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) := by
      rw [GlobalTheory.IndefiniteRowSideFullHecke.StandardHermitianSpace.baseLat_eq hC.lev i, GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
    have hW : (R.ΛW i : Set (Fin (Wc D i).rank → D.host.E)) = (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _) := by
      rw [← GlobalTheory.AdelicU.hermitianSpaceBaseLattice_eq_frameLattice]
      obtain ⟨c, -, -, -, h1, h2⟩ := hC.lev.βW i
      ext x
      constructor
      · intro hx
        simpa using h2 x hx
      · intro hx
        simpa using h1 x hx
    have hle : latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _)
        (fun v => v ∉ under (R.Pg ∪ R.Q t)) ≤ latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
      rw [hV, hW]
      exact GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
    have hz : ∀ u ∈ latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _)
        (fun v => v ∉ under (R.Pg ∪ R.Q t)), ∀ a b, cA D (cA D e) * u a b = 0 ∧ cA D e * u a b = 0 := by
      intro u hu a b
      obtain ⟨h1, h2⟩ := GlobalTheory.FockSph.idemSum_mul_of (P := fun v => v ∉ under (R.Pg ∪ R.Q t)) he
        (fun PP hPP hn => hn (Finset.mem_image_of_mem _ hPP)) hu a b
      rw [Formalism.L2.Theta.cA_cA]
      exact ⟨h1, h2⟩
    have hlat := hvac.2.lat
    have fix : ∀ u ∈ latO (Vc D i) (Wc D i) (GlobalTheory.AdelicU.frameLat (Vc D i) : Set _) (GlobalTheory.AdelicU.frameLat (Wc D i) : Set _)
        (fun v => v ∉ under (R.Pg ∪ R.Q t)), heisO R.ψ (Vc D i) (Wc D i) u (R.vacP i) = R.vacP i →
        heisO R.ψ (Vc D i) (Wc D i) u (R.ptP i t P) = R.ptP i t P := fun u hu h0 =>
      GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) hθ (fun _ => 1) (cart (R.MW i (sg0 D A)))
        (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t) hpt u (GlobalTheory.VacGood.infPart_latO (hle hu))
        (GlobalTheory.Hk3.heisO_fix_thetaAt_off R.ψ (Vc D i) (Wc D i) (cA D e) _ 1 (R.vacP i) _ (R.vP i t) hth u
          (fun a b => ⟨(hz u hu a b).2, (hz u hu a b).1⟩) h0) P
    exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hlat.1 u (hle hu)),
      fun e' he' u hu hh => fix u hu (hlat.2 e' he' u (hle hu) hh)⟩
  · intro κ hκ
    have hl := is_lift_of_mem_principal_congruence R i t hκ
    have hv : R.ωP i t (κ, 1) (R.vP i t) = (1 : ℂ) • R.vP i t := by
      rw [GlobalTheory.T.weilAction_liftPair_stepVector_invLevelChar R hC.lev hC.models.inf hC.thP.ωP hC.thP.vP i t 1 κ 1 hl (is_lift_one_principal_level R i),
        levChi_flag_of_mem_prin R i t hκ, inv_one]
    have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hθ
      (hC.thP.ωP i t) _ _ _ _ _ hpt κ hl.1 1 (Subgroup.one_mem _) 1 hv P
    exact this.trans (one_smul ℂ _)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueChainKernelEqClassSumJetsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueChainKernel_eq_classSum_jets : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : TwDat I l Z u a Ch), A.Is → ∀ (i : ℕ) (hi : i + 1 ≤ B.R.m) (hab : B.R.N i ≤ B.R.N (i + 1)) (φ : ColT I l u a i) (Fc : (I.chain l u a).cls i → PY (I.rec7 l Z).what₂.Tau (B.R.N i)), (∀ c y, φ c y = evalAt y.1 (Fc c) * ∏ τ, (y.1 τ).det ^ (-(I.chain l u a).sSharp i τ)) → ∀ c' y', (I.chain l u a).K i φ c' y' = ∑ᶠ c, ((Nat.card ((I.chain l u a).stab i c) : ℕ) : ℂ)⁻¹ * A.abelian₂ i c c' (subY hab y'.1 (Fc c)) * ∏ τ, (y'.1 τ).det ^ (-(I.chain l u a).sDiv i τ) := by
  first | exact @GlobalTheory.AdForm.KerVal.kernel_classSum | exact GlobalTheory.AdForm.KerVal.kernel_classSum | (intros; apply GlobalTheory.AdForm.KerVal.kernel_classSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnStepsAreStandardHermitianPairsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumnSteps_are_standardHermitianPairs : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ → (∀ (i : ℕ), i + 1 ≤ B.R.m → StdPair θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) I.A.δ I.A.sc ψ) ∧ (I.rec7 l Z).sp.X'.gram = 1 ∧ (∀ τ, B.fields.embC I.A.σ₀ τ = tauE (I.rec7 l Z) τ) ∧ (∀ τ, I.J.cD τ ≠ 0) ∧ ∀ (V : HSp (I.rec7 l Z)) (g : GA (I.rec7 l Z) V), ∃ x, IsDetRoot V g x := by
  first | exact @GlobalTheory.AdForm.StdStepsT.stdPair_steps_all | exact GlobalTheory.AdForm.StdStepsT.stdPair_steps_all | (intros; apply GlobalTheory.AdForm.StdStepsT.stdPair_steps_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryPairMapsCompletedHomLatticeOntoTranslateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryPair_maps_completedHomLattice_onto_translate : ∀ (D : D7) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b), S.gram = 1 → T.gram = 1 → ∀ g ∈ GfC S, ∀ h ∈ GfC T, ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), Moves S hS g N → Moves T hT h N' → ∀ u' ∈ latO S T (latFr S hS N) (latFr T hT N') (fun _ => True), ∃ u ∈ latO S T (intVec D _) (intVec D _) (fun _ => True), actO S T g h u = u' := by
  first | exact @GlobalTheory.LatMoveStd.latO_moved_onto | exact GlobalTheory.LatMoveStd.latO_moved_onto | (intros; apply GlobalTheory.LatMoveStd.latO_moved_onto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumMatrixCoefficientSourceInertPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_matrixCoefficient_source_inert_place_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), IsInertAt D.host.F D.host.E v w → UnrAt χS w → UnrAt χT w → ∀ c ϖ e, IsUnramInv ϖ c (qV D.host.F v) → IsInertChart D.sp.cm.sig S.gram (frameLat S) h c e → ∃ φ : GU c S.rank → ℂ, KerU ϖ (qV D.host.F v) T.rank ((-1) ^ T.rank) φ ∧ ∀ (g : GU c S.rank) (f₁ f₂ : WO S T → ℂ), VacFin ψ S T v f₁ → VacFin ψ S T v f₂ → Lift.pet μ 𝓕 (om (embV S v (e.symm g), 1) f₁) f₂ = φ g * Lift.pet μ 𝓕 f₁ f₂ := by
  first | exact @GlobalTheory.VacSource.vacuum_matrixCoefficient_source_inert_place | exact GlobalTheory.VacSource.vacuum_matrixCoefficient_source_inert_place | (intros; apply GlobalTheory.VacSource.vacuum_matrixCoefficient_source_inert_place <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValueZeroParabolic
section
open scoped Matrix NNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.SiegelLaw

theorem value_zero_parabolic : ∀ (D : D7) (n : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (θ : InfFam D) (μ : Measure (Mx D V.rank n)) (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)), IsWeilSch ψ χ θ V μ ω → ∀ (Φ : schwartzA θ V.rank n), ∀ p ∈ P D n, ∀ a : GL (Fin n) (AE D), blkA (mat p) = a.1 → ∀ g : G D n, (ω (p * g) Φ).1 0 = (χ (Matrix.GeneralLinearGroup.det a) : ℂ) * npow (absA D (Matrix.GeneralLinearGroup.det a)) (s0 V n + (n : ℂ) / 2) * (ω g Φ).1 0 := by
  intro D n V ψ χ θ μ ω hω Φ p hp a ha g
  obtain ⟨m, v, b, e, hm, hv⟩ := GlobalTheory.StdUnn.LeftInvSect.exists_levi_unip hp a ha
  have e' : ω (p * g) Φ = ω m (ω v (ω g Φ)) := by
    rw [e, map_mul, map_mul]; rfl
  have z1 : ((0 : Mx D V.rank n) ⬝ a.1 : Mx D V.rank n) = 0 := Matrix.zero_mul _
  have z2 : GlobalTheory.StdUnn.inner V (0 : Mx D V.rank n) 0 = 0 := by
    rw [GlobalTheory.StdUnn.inner, adj_zero, Matrix.zero_mul]
  have hs : s0 V n + (n : ℂ) / 2 = (V.rank : ℂ) / 2 := by rw [s0]; ring
  rw [e', hω.levi m _ hm, z1, hω.unip v b hv, z2, hs]
  simp [halfTr]

end GlobalTheory.StdUnn.SiegelLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionEqSmulOfKeepsLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_eq_smul_of_keeps_lattice : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (μ : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T μ μ om → ∀ e (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ vac Φ w, IsVacO ψ θ S T (fun _ => 1) (fun _ => 1) (intVec D _) (intVec D _) vac → IsSBHalf e (stdHom S T) Φ → IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 vac Φ w → ∀ k ∈ GfC S, ∀ k' ∈ GfC T, (∀ x, x ∈ stdHom S T ↔ actO S T k k' x ∈ stdHom S T) → ∀ p q : ℂ, om (k, k') vac = p • vac → (∀ z, IsHalf e z → p * Φ (actO S T k⁻¹ k'⁻¹ z) = q * Φ z) → om (k, k') w = q • w := by
  first | exact @GlobalTheory.LevLaw.omega_eq_smul | exact GlobalTheory.LevLaw.omega_eq_smul | (intros; apply GlobalTheory.LevLaw.omega_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilActionLeviOriginEqCharScalarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilAction_levi_origin_eq_charScalar : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∃ (α : GL (Fin ρ) (AE D) →* Circle) (ξ : GA D S₀ →* Circle), Continuous α ∧ (∀ a : GL (Fin ρ) D.host.E, α (Matrix.GeneralLinearGroup.map (incA D) a) = 1) ∧ Continuous ξ ∧ (∀ γ ∈ GQ S₀, ξ γ = 1) ∧ ∀ a g f, IsThetaFunO ψ S T f → d.mixS T ψ μ 𝓕 (om (d.levi a * d.emb0 g, 1) f) 0 = ((α a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ) * (ξ g : ℂ)) • om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0) := by
  first | exact @GlobalTheory.Unf.levi_origin_scalar | exact GlobalTheory.Unf.levi_origin_scalar | (intros; apply GlobalTheory.Unf.levi_origin_scalar <;> assumption)
end

