import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0560
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0359
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0657
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0664
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0602
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0604
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0622
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumSplitPlaceIndicatorDualPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0712
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0767
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0772

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingFamilyExtendsByTwistedRow
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.SepRows GlobalTheory.PairLift GlobalTheory.ChainFr GlobalTheory.Chain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.RowArrow
variable {D : D7}
end GlobalTheory.RowArrow
open GlobalTheory.RowArrow in
theorem GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx → RowModels → RowStep := by
  intro pr hE _ D _ hS T L μ0 hL sc hc G W M hM i hi S S' MA MB e e' cA cB
  obtain ⟨X, hX, -, -, h3, h4, h5⟩ :=
    GlobalTheory.RealPlaceTheta.exists_record_theta_all pr.discreteSeriesCover pr.harishChandraModules
  have I := GlobalTheory.PairLift.inputs_of_chosenSeries pr.discreteSeriesCover pr.harishChandraModules pr.cuspRapidDecay pr.casselmanWallach D X hX
  have hP := GlobalTheory.PairLift.RuleLift.pairLifts D X I (GlobalTheory.PairLift.cuspAll_of_lowAll D X I
    (GlobalTheory.PairLift.lowAll_of_lowFock D X I (GlobalTheory.LowerMembersRule.lowFock D X I)))
  have rA : (Node.grid i 0).InRange D.R.m := ⟨hi.le, Nat.zero_le _⟩
  have rB : (Node.grid (i + 1) 0).InRange D.R.m := ⟨hi, Nat.zero_le _⟩
  obtain ⟨FA, a1, a2⟩ := exists_frame _ _ _ (W.onb_is _ rA)
  obtain ⟨FB, b1, b2⟩ := exists_frame _ _ _ (W.onb_is _ rB)
  have b3 : (frSgn true FB).cart = G.cartS W.cart (.chi i 0) := funext fun τ => by
    rw [cart_frSgn, b1]; rfl
  have b4 : (frSgn true FB).onb = G.onS W.onb (.chi i 0) := b2
  have hR : ∀ τ, PairPar (GlobalTheory.SignedHC.flip (S' τ)) (S τ)
      (att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D (i + 1) 0)) (att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D i 0)) :=
    fun τ => by
      rw [e, e', hc, parRow_eq, parRow_eq]
      exact GlobalTheory.GridParD.pairPar_X D hS i 0 τ hi (Nat.zero_le _)
  have hη : ∀ τ, HasInfExp D L.eta τ (1 / 2) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ hL.eta
      (StepVac.hasInfQ_tau (a := fun _ => 1 / 2) ⟨_, fun _ => by norm_num, L.C.isEta.inf⟩) τ
  have hχ : ∀ τ, HasInfExp D (G.ch.chi (D.R.m - i)) τ (GlobalTheory.Grid.cen D τ (D.R.m - i)) := fun τ =>
    GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun τ => GlobalTheory.Grid.cen D τ (D.R.m - i)) (G.ch.chi_eq _ (by omega) (by omega))
      ⟨_, fun τ => by simp only [cen_eq, hc]; push_cast; rfl, G.ch.inf _ (by omega) (by omega)⟩ τ
  have hω : IsWeilExp W.ψ (GlobalTheory.Grid.sgn true (G.V (.grid (i + 1) 0))) (G.V (.grid i 0))
      (fun τ => att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D (i + 1) 0))
      (fun τ => att (GlobalTheory.Grid.cen D τ (D.R.m - i)) (GlobalTheory.Grid.rkV D i 0)) (W.om (.chi i 0)) := by
    refine ⟨_, _, W.om_is (.chi i 0) rB, fun τ => ⟨?_, ?_⟩⟩
    · have r : (G.pS (.chi i 0)).rank = GlobalTheory.Grid.rkV D (i + 1) 0 := (node_isV G hL rB).rank
      rw [GridData.chrS, r]
      exact exp_att (hχ τ) (hη τ) _
    · have r : (G.pT (.chi i 0)).rank = GlobalTheory.Grid.rkV D i 0 := (node_isV G hL rA).rank
      rw [GridData.chrT, r]
      exact exp_att (hχ τ) (hη τ) _
  have hv := (W.vac_is i hi).2
  have v0 : IsVacF W.ψ W.θ (frSgn true FB) FA (W.vac i) := ⟨hv.theta, fun τ => by rw [b3, a1]; exact hv.fock τ⟩
  have n0 : W.vac i ≠ 0 := fun h => by
    obtain ⟨⟨p, hp⟩, h2⟩ := hv.norm
    have := h2 p hp
    simp [nrm2, h] at this
  have v1 : ∀ κ, IsVacF W.ψ W.θ (frSgn true FB) FA (W.cosVec i κ) := fun κ => by
    obtain ⟨u, hu, h⟩ := W.cosVec_is
    have th := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is (h i hi κ) hv.theta
    have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hu
    refine ⟨th, fun τ => ?_⟩
    rw [b3, a1]
    exact GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt W.ψ_std.1.1 W.θ_is ho.infPart_eq ho.conj.infPart_eq (h i hi κ) hv.theta th
      (hv.fock τ)
  obtain ⟨hν, h𝓕⟩ := (hM.row i hi.le).haar_fund
  obtain ⟨It, hIt⟩ := lifts_neg h3 h4 h5 hP hE W.θ_is W.ψ_std MA MB hR FA FB (cA.trans a1.symm) (cB.trans b1.symm) hω v0 n0 hν h𝓕
  refine ⟨It, fun F hF κ => ?_⟩
  obtain ⟨F', hF', h⟩ := hIt _ (v1 κ) F hF
  have ef : ∀ P, ptF W.ψ W.θ (frSgn true FB) FA (W.cosVec i κ) P = W.fock (.chi i 0) (W.cosVec i κ) P := fun P => by
    unfold ptF
    rw [b3, b4, a1, a2]
    rfl
  simp only [ef] at h
  exact ⟨F', hF', fun P v => ⟨fun g => (h P v g).1, funext fun g => (h P v g).2⟩⟩
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separating_family_extend_by_twist : _root_.GlobalTheory.FunPr.ThetaLocalInputs → PairEx → RowModels → RowStep := by
  first | exact @_root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row | exact _root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row | (intros; apply _root_.GlobalTheory.RowArrow.separatingFamily_extends_by_twisted_row <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SeparatingModelsOfSeparatingData
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.SepRows
open Matrix
theorem separating_models_of_separating_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowModels := by
  intro hP D _ _ T L μ0 _ sc hsc G W M _ i hi
  have hDS := hP.discreteSeriesUpqExists
  classical
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  ·
    rw [parRow_zero]
    have hV : (G.V (.grid 0 0)).SigOK := D.sp.Y_sig (min 0 D.R.m)
    refine exists_model_of_enum hDS hV (W.onb (.grid 0 0)) (W.cart (.grid 0 0)) (fun τ => ?_)
      (W.onb_is (.grid 0 0) ⟨Nat.zero_le _, Nat.zero_le _⟩)
    obtain ⟨lam, ε, hE, hH, -, hq⟩ := GlobalTheory.ChainModels.goodPar_parB D (min 0 D.R.m) (min_le_right _ _) τ
    have e : parB (Ptw D) (min 0 D.R.m) τ = parB (Ptw D) 0 τ := by rw [Nat.zero_min]
    rw [e] at hE
    exact ⟨lam, ε, hE, hH, hq⟩
  · rw [hsc]
    have hX : (Node.grid i 0).InRange D.R.m := ⟨hi, Nat.zero_le _⟩
    have hv := G.isV hX (fun j e => by cases e; omega)
    refine exists_model_of_enum hDS hv.sigOK (W.onb (.grid i 0)) (W.cart (.grid i 0)) (fun τ => ?_) (W.onb_is _ hX)
    obtain ⟨hr, hc, hm⟩ := GlobalTheory.GridJoin.dualPar_shift_counts (if Odd (i + 0) then -(1 / 2) else 0)
      (GlobalTheory.GridParDCount.isRegular_parD D 1 τ hi (Nat.zero_le D.R.m))
    have hc' : (parRow D 1 i τ).card = (G.V (.grid i 0)).rank :=
      hc.trans ((GlobalTheory.GridParDCount.card_parD D 1 τ hi (Nat.zero_le _)).trans hv.rank.symm)
    obtain ⟨lam, ε, hE, hcount⟩ := GlobalTheory.GridJoin.exists_isEnum_of_regular hr hc'
    refine ⟨lam, ε, hE, isHCParam_dual_parV D i 0 τ lam ε hv.rank hE, ?_⟩
    rw [hcount, hv.sig]
    exact hm.trans (GlobalTheory.SignedHC.Model.nMinus_parD _ i 0)
end GlobalTheory.SepRows
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_models_of_separating_data : _root_.GlobalTheory.FunPr.ThetaLocalInputs → RowModels := by
  first | exact @_root_.GlobalTheory.SepRows.separating_models_of_separating_data | exact _root_.GlobalTheory.SepRows.separating_models_of_separating_data | (intros; apply _root_.GlobalTheory.SepRows.separating_models_of_separating_data <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SmoothOfThetaLiftFiniteSum
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.ColFockRed
open GlobalTheory.Grid
theorem theta_lift_finite_sum_smooth : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    ∀ (n : ℕ) (F : Fin n → (G.Xp j).Cusp R.θ) (w : Fin n → SmT (G.Xp j).M),
    (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g) (G.measX j).fd (G.measX j).ν) →
    ∃ (k : ℕ) (F' : Fin k → (G.Xp (j + 1)).Cusp R.θ) (z : Fin k → SmT (G.Xp (j + 1)).M),
      (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g ∂(G.measX j).ν) = ∑ i, (F' i).1 (z i) := by
  intro hL _hPr D hSz G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t j hj Φ hΦ n F w hint
  have hCA := hL D hSz G₀ Pl0 T A Ks R G hRB hG
  have hθ : IsInfFam R.θ := hRB.inf
  obtain ⟨νS, PS, hS⟩ := xp_is hG j hj.le
  obtain ⟨νT, PT, hT⟩ := xp_is hG (j + 1) hj
  obtain ⟨hsig, hdef⟩ := GlobalTheory.ColTypeLift.xp_definite hG j hj.le
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_realCentralCharacter_definiteVertexMultiplicity D R.θ hθ (G.Xp j) νS PS hS
  have hψc : GlobalTheory.SeeSaw.HasCen (G.Xp j).V χ (∑ i, (F i).1 (w i)) := fun z hz hc h => by
    simp only [Finset.sum_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => hχ (F i) (w i) z hz hc h
  have hψa : GlobalTheory.Unf.IsContAut (G.Xp j).V (∑ i, (F i).1 (w i)) := by
    refine ⟨fun γ hγ g => ?_, by rw [Finset.sum_fn]; exact continuous_finset_sum _ fun i _ => (isContAut_cusp (F i) (w i)).2⟩
    simp only [Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (isContAut_cusp (F i) (w i)).1 γ hγ g
  obtain ⟨hν, hfd⟩ := measX_haar_fd hG j hj.le
  have hA := hG.arrows.col t j hj
  obtain ⟨Φ', hΦ', heig, heq⟩ := GlobalTheory.T.exists_thetaLift_realCentre_average_eigenvector D R.ψ _ _ _ _ (G.col t j).ω hA.weil hsig hdef _ _ hν hfd χ _ hψc hψa Φ hΦ hint
  obtain ⟨k, f, p, hf, hsum⟩ := GlobalTheory.T.centreEigen_thetaFunction_finite_sum_fockPolynomials D R.ψ R.θ hθ (G.Xp j) (G.Xp (j + 1)) νS νT PS PT hS hT (G.col t j) _ _ hA
    (fun z => (χ z)⁻¹) Φ' hΦ' heig
  have hcol := hCA.col t j hj
  choose F' hF' hI using fun (l : Fin k) (i : Fin n) => hcol (f l) (hf l) (F i).1 (F i).2
  refine ⟨k * n, fun q => ⟨F' (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2, hF' _ _⟩,
    fun q => (G.col t j).It (p (finProdFinEquiv.symm q).1) (w (finProdFinEquiv.symm q).2), ?_⟩
  funext h
  rw [heq h, hsum]
  have key : ∀ g, thetaKO (G.col t j).ω g h (∑ l, fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
      (∑ i, (F i).1 (w i)) g = ∑ l, ∑ i, thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
        (F i).1 (w i) g := fun g => by
    simp only [thetaKO, map_sum, Finset.sum_apply, Finset.sum_mul_sum]
  rw [integral_congr_ae (Filter.Eventually.of_forall key)]
  rw [integral_finset_sum _ fun l _ => integrable_finset_sum _ fun i _ => (hI l i (p l) (w i) h).1]
  simp_rw [integral_finset_sum _ fun i _ => (hI _ i _ (w i) h).1]
  have e2 : ∀ l i, ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h (fock R.ψ R.θ false (G.Xp j) (G.Xp (j + 1)) (f l) (p l)) *
      (F i).1 (w i) g ∂(G.measX j).ν = F' l i ((G.col t j).It (p l) (w i)) h := fun l i => (hI l i (p l) (w i) h).2
  simp_rw [e2]
  rw [← Fintype.sum_prod_type']
  rw [Finset.sum_apply]
  exact (finProdFinEquiv.symm.sum_comp (fun x : Fin k × Fin n => F' x.1 x.2 ((G.col t j).It (p x.1) (w x.2)) h)).symm
end GlobalTheory.ColFockRed
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_of_theta_lift_finite_sum : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t j, j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.Xp j).V (G.Xp (j + 1)).V Φ →
    ∀ (n : ℕ) (F : Fin n → (G.Xp j).Cusp R.θ) (w : Fin n → SmT (G.Xp j).M),
    (∀ h, IntegrableOn (fun g => thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g) (G.measX j).fd (G.measX j).ν) →
    ∃ (k : ℕ) (F' : Fin k → (G.Xp (j + 1)).Cusp R.θ) (z : Fin k → SmT (G.Xp (j + 1)).M),
      (fun h => ∫ g in (G.measX j).fd, thetaKO (G.col t j).ω g h Φ * (∑ i, (F i).1 (w i)) g ∂(G.measX j).ν) = ∑ i, (F' i).1 (z i) := by
  first | exact @_root_.GlobalTheory.ColFockRed.theta_lift_finite_sum_smooth | exact _root_.GlobalTheory.ColFockRed.theta_lift_finite_sum_smooth | (intros; apply _root_.GlobalTheory.ColFockRed.theta_lift_finite_sum_smooth <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitCharValueSplitCharacters
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.SplitCharValue
theorem splitCharValue_split_characters : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ x₀ : (Formalism.L2.Theta.AE D)ˣ,
    (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) →
    (Mod1All ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ Mod1All ((ch.G.chrT p x₀ : Circle) : ℂ)) ∧
    ∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q →
      GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrT p x₀ : Circle) : ℂ) := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ p hp e he x₀ hx
  have hW := ch.W.om_is p (defPair_inRange hp)
  obtain ⟨e', he', hoff, a, hx'⟩ : ∃ e' : Formalism.L2.Theta.AE D, IsSplitIdem D e' ∧
      (∀ q, GlobalTheory.MovedKappaEx.OffPrime e q → GlobalTheory.MovedKappaEx.OffPrime e' q) ∧
      ∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e' * a + (1 - e') := by
    obtain ⟨a, ha | ha⟩ := hx
    · exact ⟨e, he, fun _ h => h, a, ha⟩
    · exact ⟨cA D e, GlobalTheory.ConjAdjWeil.isSplitIdem_conj he, fun _ h => offPrime_conj h, a, ha⟩
  have hS := char_split_value D _ _ hW.hecS hW.resS e' he' x₀ a hx'
  have hT := char_split_value D _ _ hW.hecT hW.resT e' he' x₀ a hx'
  exact ⟨⟨hS.1, hT.1⟩, fun q _ hq => ⟨hS.2 q (hoff q hq), hT.2 q (hoff q hq)⟩⟩
end GlobalTheory.SplitCharValue
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_split_character_values : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (e : Formalism.L2.Theta.AE D), IsSplitIdem D e → ∀ x₀ : (Formalism.L2.Theta.AE D)ˣ,
    (∃ a : Formalism.L2.Theta.AE D, (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e) ∨ (x₀ : Formalism.L2.Theta.AE D) = cA D e * a + (1 - cA D e)) →
    (Mod1All ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ Mod1All ((ch.G.chrT p x₀ : Circle) : ℂ)) ∧
    ∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q →
      GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrS p x₀ : Circle) : ℂ) ∧ GlobalTheory.MovedKappaEx.UnitAt q ((ch.G.chrT p x₀ : Circle) : ℂ) := by
  first | exact @_root_.GlobalTheory.SplitCharValue.splitCharValue_split_characters | exact _root_.GlobalTheory.SplitCharValue.splitCharValue_split_characters | (intros; apply _root_.GlobalTheory.SplitCharValue.splitCharValue_split_characters <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitDetCharacterTrivial
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
noncomputable section
namespace GlobalTheory.SplitDetChr
open GlobalTheory.LFun GlobalTheory.Doubling
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
end GlobalTheory.SplitDetChr
theorem GlobalTheory.SplitDetChr.split_det_character_eq_one : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ hvT _ _ _ t ht
  obtain ⟨ht1, ht2⟩ := ht
  have e1 := GlobalTheory.InertDetChr.eq_ideleAt (GlobalTheory.InertDetChr.at_det_sub_one v t ht1)
  haveI : Submodule.IsLattice E G.W.L := hTr.geo.hW.lat
  obtain ⟨P0, h1, h2⟩ := GlobalTheory.AdelicU.Frames.exists_rational_frame G.W.L v
  have hP := GlobalTheory.AdelicU.Frames.frame_of_rational P0 h1 h2
  set T := Formalism.UG.bc (compFin F E v) t with hTdef
  have hT : ∀ y ∈ latLoc F G.W.L v, T.1 *ᵥ y ∈ latLoc F G.W.L v :=
    GlobalTheory.SplitDetChr.mulVec_mem_latLoc G.W v _ (fun z hz => (ht2 z hz).1)
  have hT' : ∀ y ∈ latLoc F G.W.L v, (T⁻¹).1 *ᵥ y ∈ latLoc F G.W.L v := by
    rw [hTdef, ← map_inv]
    exact GlobalTheory.SplitDetChr.mulVec_mem_latLoc G.W v _ (fun z hz => (ht2 z hz).2)
  have hd : GlobalTheory.Doubling.unitFin F E v (Matrix.GeneralLinearGroup.det t) = Matrix.GeneralLinearGroup.det T := by
    refine Units.ext ?_
    show compFin F E v ((Matrix.GeneralLinearGroup.det t : (AE F E)ˣ) : AE F E) = _
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, RingHom.map_det]
    rfl
  have hy := GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T hT
  have hy' := GlobalTheory.SplitDetChr.det_mem_intLoc _ hP T⁻¹ hT'
  rw [e1]
  show GlobalTheory.Doubling.charAt X.α v _ = 1
  rw [hd]
  refine GlobalTheory.LFun.charAt_eq_one_of_unrAt X.α v _ hy (by rwa [← map_inv]) (fun w hw => hTr.chars.unrα w ?_)
  show ¬ (w.under (𝓞 F) ∈ (X.T : Set (Pl F)))
  rw [hw]; exact_mod_cast hvT
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_det_character_trivial : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ t : GL (Fin (a + a')) (AE F E), (At (evFin F v) ((t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) - 1) ∧
      ∀ z ∈ GlobalTheory.InertSph.latAt G.W v, (t : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v ∧
        ((t⁻¹ : GL (Fin (a + a')) (AE F E)) : Matrix (Fin (a + a')) (Fin (a + a')) (AE F E)) *ᵥ z ∈ GlobalTheory.InertSph.latAt G.W v) →
      X.α (Matrix.GeneralLinearGroup.det t) = 1 := by
  first | exact @_root_.GlobalTheory.SplitDetChr.split_det_character_eq_one | exact _root_.GlobalTheory.SplitDetChr.split_det_character_eq_one | (intros; apply _root_.GlobalTheory.SplitDetChr.split_det_character_eq_one <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplitParallelDerivativeLeftFixed
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix GlobalTheory.VacAny
noncomputable section
namespace GlobalTheory.SplitParLeft
open GlobalTheory.DblVacLine
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
theorem splitParallel_derivative_fixes_left : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
      (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.W.J) (dbl (incM F G.V'.J)) dd (X.α / X.β) (diagCols (Fin a')) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.V' v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hTr v _ hT hunr _ _ d' hd' dd omd hdc hws R hR0 hRv p hp
  set Ψ := tens (evFin F v) (G.M'.vac v) R with hΨdef
  have hΨ : Ψ ∈ schA F _ := hRv.2
  have hΦ : GlobalTheory.InertDbl.dblFun Ψ ∈ schA F _ :=
    GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ Ψ hΨ _ (GlobalTheory.SchAConj.star_mem_schA F _ Ψ hΨ)
  have hV := hTr.geo.hM'.vac v
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hV.2.1
  have hΨne : Ψ ≠ 0 := by
    intro h0
    let x : Fin a' × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (y i)
    have hRx : R x = R 0 := by
      have := hRv.1 0 x (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
      simpa using this
    have h1 := congrFun h0 x
    simp only [hΨdef, tens, x, GlobalTheory.LatVac.evFin_liftV, hRx, Pi.zero_apply] at h1
    exact mul_ne_zero hy hR0 h1
  obtain ⟨c, hc⟩ := dblFun_eigen_left hTr.base hTr.geo v hunr d' hd' dd omd hdc hws.2.1 R hRv p hp.1
  obtain ⟨l, hl, hinv, hl0⟩ := GlobalTheory.DblDiagForm.exists_form F _ Ψ hΨ hΨne
  obtain ⟨t, ht⟩ := hp.2
  have hS := hws.2.2 l hl (fun z φ hφ => hinv φ hφ _ _ (GlobalTheory.WeilM.SiegelModel.rho_diag B.ψ hdc z φ)) p t ht _ hΦ
  have htp := GlobalTheory.InertDbl.parD_diag_action F E σ G.V' v p hp t ht
  have hw : ∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → w ∉ above E (X.T : Set (Pl F)) :=
    fun w h hm => hT (h ▸ hm)
  have ha : (X.α / X.β) (Matrix.GeneralLinearGroup.det t) = 1 := by
    rw [MonoidHom.div_apply,
      chr_det_eq_one G.V' hTr.geo.hV'.lat v X.α (fun w h => hTr.chars.unrα w (hw w h)) t htp.1 htp.2,
      chr_det_eq_one G.V' hTr.geo.hV'.lat v X.β (fun w h => hTr.chars.unrβ w (hw w h)) t htp.1 htp.2, div_one]
  have hb := GlobalTheory.IntegralDetModule.modu_norm_det G.V' hTr.geo.hV'.lat v t htp.1 htp.2
  rw [ha, hb] at hS
  rw [hc, map_smul, smul_eq_mul] at hS
  simp only [Circle.coe_one, NNReal.coe_one, Real.one_rpow, Complex.ofReal_one, one_mul] at hS
  have h1 : c = 1 := (mul_eq_right₀ hl0).mp hS
  rw [hc, h1, one_smul]
end GlobalTheory.SplitParLeft
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_parallel_derivative_left_fixed : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F), Formalism.MainNotions.SchurIrreducible.IsSplit (E := E) v → v ∉ X.T → PsiUnr B.ψ v → (2 : 𝓞 F) ∉ v.asIdeal →
    G.M'.vac v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 →
    ∀ (d' : Darboux (symp (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J)) (Fin a' × Fin (a + a'))),
      (∀ x : Matrix (Fin a') (Fin (a + a')) (AE F E), d'.e xᵀ = G.M'.co.e x) →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.W.J) (dbl (incM F G.V'.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.V'.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.W.J) (incM F G.V'.J) d' dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.W.J) (dbl (incM F G.V'.J)) dd (X.α / X.β) (diagCols (Fin a')) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, R 0 ≠ 0 → Rest (evFin F v) (G.M'.vac v) R →
    ∀ p ∈ GlobalTheory.InertDbl.ParD σ G.V' v, omd p (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  first | exact @_root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left | exact _root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left | (intros; apply _root_.GlobalTheory.SplitParLeft.splitParallel_derivative_fixes_left <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SquareAgreeStabilizerCompactWeyl
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
namespace GlobalTheory.SquareAgree.StabKW
theorem stabilizer_compact_weyl_eq : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (1, k) ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
  intro _hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB _hθ _hTr _hO hT Pi rf rl p p' _hm k hk ΦD hΦD
  have hdet : Γ.V.J.det ≠ 0 ∧ Γ.W.J.det ≠ 0 :=
    ⟨GlobalTheory.FinUniq.det_ne_zero_herm hT.geo.hV, GlobalTheory.FinUniq.det_ne_zero_skew hT.geo.hW⟩
  have key := GlobalTheory.T.compactUnitary_preserves_polynomialFock D.host.F D.host.E D.sp.cm.sig hT.base.cm W.rank (W.rank + W₁.rank) Γ.V Γ.W Γ.M Bs.ψ Xc.β
    (Xc.β / Xc.α) om hT.base.std hT.geo.hV.herm hdet.1 hT.geo.hW.skew hdet.2 hT.chars.resβ
    (GlobalTheory.ThKRatInv.resEtaPow_div hT.chars.resβ hT.chars.resα) hT.chars.heckeβ
    (GlobalTheory.ThKRatInv.isHecke_div hT.chars.heckeβ hT.chars.heckeα) hT.weil Bs.emb hT.geo.hV.cartan hT.geo.hW.cartan k hk
  have hgen : {Φ | ∃ f φ, f ∈ Γ.M.Pol Bs.ψ Bs.emb ∧ (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) ∧
      (∀ᶠ v in Filter.cofinite, φ v = Γ.M.vac v) ∧ Φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ} ⊆
      ((algD Γ.M Bs.ψ Bs.emb).comap (om (1, k)) : Set _) := by
    rintro _ ⟨f, φ, hf, hSB, hcof, rfl⟩
    obtain ⟨⟨f₁, hf₁⟩, hpol⟩ := key f hf
    have hstd : ∀ᶠ v in Filter.cofinite,
        φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers D.host.F} 1 :=
      (hcof.and hT.geo.hM.std).mono fun v hv => hv.1.trans hv.2
    have hrest : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI D.host.F) (⇑f) (GlobalTheory.EvZeroInf.finPart φ) :=
      ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add φ x z hz, GlobalTheory.TensUniq.pure_mem_schA f φ hSB hstd⟩
    have h := hf₁ _ hrest
    rw [← GlobalTheory.EvZeroInf.pure_eq_tens, ← GlobalTheory.EvZeroInf.pure_eq_tens] at h
    show om (1, k) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) ∈ algD Γ.M Bs.ψ Bs.emb
    rw [h]
    exact Submodule.subset_span ⟨f₁, φ, hpol f₁ hf₁, hSB, hcof, rfl⟩
  exact (Submodule.span_le.2 hgen) hΦD
end GlobalTheory.SquareAgree.StabKW
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.square_agree_stabilizer_compact_weyl : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (1, k) ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
  first | exact @_root_.GlobalTheory.SquareAgree.StabKW.stabilizer_compact_weyl_eq | exact _root_.GlobalTheory.SquareAgree.StabKW.stabilizer_compact_weyl_eq | (intros; apply _root_.GlobalTheory.SquareAgree.StabKW.stabilizer_compact_weyl_eq <;> assumption)
end
end

