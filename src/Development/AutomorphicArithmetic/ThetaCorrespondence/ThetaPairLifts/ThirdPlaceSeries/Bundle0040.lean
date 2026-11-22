import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0323
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0018
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0037
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0900
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0002
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0318
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0017
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0320
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0036
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0033
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0035
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0024
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0027
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0030

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.EWCastSymmWt
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.ThetaTri
open scoped TensorProduct
open MeasureTheory Formalism.IndefR.Datum Formalism.IndefR.Links GlobalTheory.ThetaLoc Formalism.L2.Theta
variable {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D} {X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp}
theorem eW_cast_symm_wt_rho_eq (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h' : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (γ : GA D (Vc D j))
    (hγ : γ ∈ GQ (Vc D j)) (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h' * A.a j)))
    (k : ℕ) (hk : j.1 + 1 = k) (p1 : 1 ≤ k) (p2 : k ≤ D.R.m) (w : (P.M (D.nd.mu i) k p1 p2).wt.W) :
    (Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W) (fun _ _ => A.eW (D.nd.mu i) hμ j) hk p1 p2).symm
        ((P.M (D.nd.mu i) k p1 p2).wt.ρ h' w) =
      (X.R.cV j).ρ γ ((Eq.ndrec (motive := fun k => (p1 : 1 ≤ k) → (p2 : k ≤ D.R.m) →
        (X.R.cV j).W ≃ₗ[ℂ] (P.M (D.nd.mu i) k p1 p2).wt.W) (fun _ _ => A.eW (D.nd.mu i) hμ j) hk p1 p2).symm w) := by
  subst hk
  apply (A.eW _ hμ j).injective
  simp only [LinearEquiv.apply_symm_apply]
  rw [A.wt _ hμ j h' γ hγ he]
  simp
theorem eWloc_symm_wt_rho_eq_cV_rho (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h' : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) (γ : GA D (Vc D j))
    (hγ : γ ∈ GQ (Vc D j)) (he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ * h' * A.a j)))
    (w : (P.M.loc i).wt.W) :
    (_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((P.M.loc i).wt.ρ h' w) = (X.R.cV j).ρ γ ((_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm w) :=
  _root_.GlobalTheory.ThetaTri.eW_cast_symm_wt_rho_eq A i j hμ h' γ hγ he (D.nd.j i) hj _ _ w
theorem formToVectorMap_rt_eq_mul_psi (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (hcv : (X.R.cV j).Is) (h : Formalism.AUTREP.GAf D.host.E D.R.nV)
    (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (hF : (F' : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F)
    (x : GA D (Vc D j)) : _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F' x = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (x * (A.PV j).ψ h) := by
  show (X.R.cV j).ext _ x = (X.R.cV j).ext _ (x * (A.PV j).ψ h)
  rw [GlobalTheory.DefLiftHecke.ext_mul _ hcv _ ((A.PV j).into h) x]
  show (X.R.cV j).ρ x⁻¹ _ = _
  simp only [LinearMap.coe_mk, AddHom.coe_mk, preF_mul, hF, NG.rt, mul_assoc]
theorem formToVectorMap_mul_of_mem_GQ (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i)
    (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (F : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ))
    (γ : GA D (Vc D j)) (hγ : γ ∈ GQ (Vc D j)) (x : GA D (Vc D j)) :
    _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (γ * x) = _root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F x := by
  obtain ⟨y, hy⟩ := fin_frame_surj (A.PV j) ((finHom (Vc D j)).rangeRestrict γ)
  obtain ⟨z, hz⟩ := fin_frame_surj (A.PV j) ((finHom (Vc D j)).rangeRestrict x)
  have hh' : A.a j * y * (A.a j)⁻¹ ∈ ReciprocityTheory.Aut.GQ D.host.E D.R.nV := by
    refine (A.rat j _).2 ⟨γ, hγ, ?_⟩
    have : (A.a j)⁻¹ * (A.a j * y * (A.a j)⁻¹) * A.a j = y := by group
    rw [this]
    exact (congrArg Subtype.val hy).symm
  have he : finHom (Vc D j) γ = finHom (Vc D j) ((A.PV j).ψ ((A.a j)⁻¹ *
      ((⟨_, hh'⟩ : ReciprocityTheory.Aut.GQ D.host.E D.R.nV) : Formalism.AUTREP.GAf D.host.E D.R.nV) * A.a j)) := by
    have : (A.a j)⁻¹ * (A.a j * y * (A.a j)⁻¹) * A.a j = y := by group
    simp only [this]
    exact (congrArg Subtype.val hy).symm
  show (X.R.cV j).ρ (γ * x)⁻¹ ((_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
      (A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict (γ * x))))) =
    (X.R.cV j).ρ x⁻¹ ((_root_.GlobalTheory.ThetaTri.eWloc_alt A i j hj hμ).symm ((F : Formalism.AUTREP.GAf D.host.E D.R.nV → (P.M.loc i).wt.W)
      (A.a j * preF (A.PV j) ((finHom (Vc D j)).rangeRestrict x))))
  have hprod : (finHom (Vc D j)).rangeRestrict γ * (finHom (Vc D j)).rangeRestrict x =
      (finHom (Vc D j)).rangeRestrict ((A.PV j).ψ (y * z)) :=
    (congrArg₂ (· * ·) hy.symm hz.symm).trans
      ((map_mul (finHom (Vc D j)).rangeRestrict _ _).symm.trans
        (congrArg (finHom (Vc D j)).rangeRestrict (map_mul (A.PV j).ψ y z).symm))
  have key : preF (A.PV j) ((finHom (Vc D j)).rangeRestrict (γ * x)) = y * z :=
    (congrArg (preF (A.PV j)) ((map_mul (finHom (Vc D j)).rangeRestrict γ x).trans hprod)).trans (preF_frame _ _)
  have hz' : preF (A.PV j) ((finHom (Vc D j)).rangeRestrict x) = z :=
    (congrArg (preF (A.PV j)) hz.symm).trans (preF_frame _ _)
  rw [key, hz']
  have e1 : A.a j * (y * z) = (A.a j * y * (A.a j)⁻¹) * (A.a j * z) := by group
  rw [e1, F.2.1 ⟨_, hh'⟩ (A.a j * z), _root_.GlobalTheory.ThetaTri.eWloc_symm_wt_rho_eq_cV_rho A i j hj hμ ⟨_, hh'⟩ γ hγ he, _root_.mul_inv_rev,
    map_mul, Module.End.mul_apply, ← Module.End.mul_apply ((X.R.cV j).ρ γ⁻¹), ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply]
theorem thetaEvaluationMap_apply {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (x : GA D (Wc D j)) :
    _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y x = PiTensorProduct.lift (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A)) (PiTensorProduct.map
      (fun τ => (lowT (X.R.MW j (sg0 D X.A)) τ).subtype) (kUnit (X.R.MW j (sg0 D X.A)))) x := rfl
theorem thetaEvaluationMap_rho_eq_mul_psi {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (g : Formalism.AUTREP.GAf D.host.E D.R.r) (y y' : ↥Y.C) (hy : (y' : Y.A) = Y.ρ g y) (x : GA D (Wc D j)) :
    _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y' x = _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y (x * (X.PW j).ψ g) := by
  have he : _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y' : Y.A) = Formalism.IndefR.principalLevelFrame.actM (X.PW j) (X.R.MW j (sg0 D X.A)) g (_root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A)) := by
    rw [hy]; exact (Classical.choose_spec (Classical.choose_spec hc)).2.2.2.1 g y
  rw [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply, _root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply, he, lift_actM]
theorem thetaEvaluationMap_mul_of_mem_GQ {j : Fin D.R.m} {j' : ℕ} {hj : j.1 + 1 = j'} {Y : RowMod D P.rep j'} (hc : GlobalTheory.NJoin.IsCanon X j hj Y)
    (y : ↥Y.C) (γ : GA D (Wc D j)) (hγ : γ ∈ GQ (Wc D j)) (x : GA D (Wc D j)) :
    _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y (γ * x) = _root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y x := by
  have hm : _root_.GlobalTheory.ThetaTri.canonicalEmbedding' hc (y : Y.A) ∈ LeftInvM (X.R.MW j (sg0 D X.A)) := by
    apply minf_le_leftInv X.R.θ (X.PW j)
    rw [← (Classical.choose_spec (Classical.choose_spec hc)).2.2.1]
    exact Submodule.mem_map_of_mem y.2
  rw [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply, _root_.GlobalTheory.ThetaTri.thetaEvaluationMap_apply]
  exact lift_left _ _ hm _ γ hγ x
theorem lamI_inv_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (A : GlobalTheory.NJoin.Agree X P.M P.rep) (i : D.nd.Loc) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (Y : RowMod D P.rep (D.nd.j i)) (hc : GlobalTheory.NJoin.IsCanon X j hj Y) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (h : GAf D.host.E D.R.nV) (g : GAf D.host.E D.R.r) (φ : (X.R.cV j).W →ₗ[ℂ] (Formalism.IndefR.Datum.WO (Formalism.IndefR.Links.Vc D j) (Formalism.IndefR.Links.Wc D j) → ℂ)), φ ∈ _root_.GlobalTheory.ThetaTri.OmegaSubmoduleAtLocal A i j hj hc hμ → ∀ (F F' : ↥(NG.AFall D.host.E D.R.nV (P.M.loc i).wt.ρ)) (y y' : ↥Y.C), (F' : GAf D.host.E D.R.nV → (P.M.loc i).wt.W) = NG.rt D.host.E D.R.nV h F → (y' : Y.A) = Y.ρ g y → _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ (GlobalTheory.ThetaTri.valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' y' = _root_.GlobalTheory.ThetaTri.canonicalPairingValue A i j hj hc hμ φ F y := by
  intro hL D P X A i j hj Y hc hμ h g φ hφ F F' y y' hF hy
  have hcore := X.given.core
  have hW := hcore.thP.ωP j (X.tupT (D.nd.mu i))
  have hcv : (X.R.cV j).Is := hcore.models.cV j
  have hth : ∀ v, IsThetaFunO X.R.ψ (Vc D j) (Wc D j) (φ v) := by
    intro v
    have := (hφ 1).1 v
    simpa [valAct1_apply] using this
  have hV := hcore.models.νV j (X.tupT (D.nd.mu i))
  have hWm := hcore.models.νW j
  haveI : (X.R.νV j (X.tupT (D.nd.mu i))).IsHaarMeasure := hV.1.1
  haveI : (X.R.νV j (X.tupT (D.nd.mu i))).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hV.1.1
  haveI : (X.R.νW j).IsHaarMeasure := hWm.1.1
  haveI : (X.R.νW j).IsMulRightInvariant :=
    GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ _ hWm.1.1
  haveI : Countable (GQ (Vc D j)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Vc D j).gram
  haveI : Countable (GQ (Wc D j)) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig (Wc D j).gram
  have inner : ∀ g₀, thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (X.R.νV j (X.tupT (D.nd.mu i)))
      (X.R.fdV j (X.tupT (D.nd.mu i))) (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' g₀ =
      thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ) (X.R.νV j (X.tupT (D.nd.mu i)))
      (X.R.fdV j (X.tupT (D.nd.mu i))) φ F (g₀ * (X.PW j).ψ g) := by
    intro g₀
    unfold thIn
    have e1 : ∀ h₀, thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h₀ g₀
        (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F' h₀)) =
        thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) (h₀ * (A.PV j).ψ h) (g₀ * (X.PW j).ψ g)
          (φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F (h₀ * (A.PV j).ψ h))) := by
      intro h₀
      rw [valAct1_apply, _root_.GlobalTheory.ThetaTri.formToVectorMap_rt_eq_mul_psi A i j hj hμ hcv h F F' hF h₀]
      exact thetaKO_act _ _ _ _ _
    simp only [e1]
    refine (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Vc D j)) _ _ hV.2
      (fun h₁ => thetaKO (X.R.ωP j (X.tupT (D.nd.mu i))) h₁ (g₀ * (X.PW j).ψ g) (φ (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h₁))) ?_ _).2
    intro γ hγ h₁
    rw [_root_.GlobalTheory.ThetaTri.formToVectorMap_mul_of_mem_GQ A i j hj hμ F γ hγ h₁]
    have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h₁))).1 γ hγ 1
      (one_mem _) h₁ (g₀ * (X.PW j).ψ g)
    rwa [one_mul] at this
  unfold _root_.GlobalTheory.ThetaTri.canonicalPairingValue lamV
  congr 1
  have e2 : ∀ g₀, star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y' g₀) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i)))
      (valAct1 (_root_.GlobalTheory.ThetaTri.standardWeilRepresentation A j (X.tupT (D.nd.mu i))) (h, g) φ) F' g₀ =
      star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y (g₀ * (X.PW j).ψ g)) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i))) φ F (g₀ * (X.PW j).ψ g) := by
    intro g₀
    rw [inner, _root_.GlobalTheory.ThetaTri.thetaEvaluationMap_rho_eq_mul_psi hc g y y' hy]
  simp only [e2]
  refine (Formalism.IndefR.Eqv.rightInv_holds _ (GQ (Wc D j)) _ _ hWm.2
    (fun g₁ => star (_root_.GlobalTheory.ThetaTri.thetaEvaluationMap hc y g₁) * thIn (X.R.ωP j (X.tupT (D.nd.mu i))) (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ)
      (X.R.νV j (X.tupT (D.nd.mu i))) (X.R.fdV j (X.tupT (D.nd.mu i))) φ F g₁) ?_ _).2
  intro γ hγ g₁
  rw [_root_.GlobalTheory.ThetaTri.thetaEvaluationMap_mul_of_mem_GQ hc y γ hγ g₁]
  congr 1
  unfold thIn
  congr 1
  funext h₁
  have := (GlobalTheory.thetaKO_rat_left_and_eigen_right _ _ _ _ _ _ hW _ (hth (_root_.GlobalTheory.ThetaTri.formToVectorMap A i j hj hμ F h₁))).1 1 (one_mem _) γ hγ
    h₁ g₁
  rwa [one_mul] at this
end GlobalTheory.ThetaTri
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsExtraFurther
section
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Cut
namespace GlobalTheory.UnrNoChi
variable {D : D7} (i : D.nd.Loc)
end GlobalTheory.UnrNoChi
theorem GlobalTheory.UnrNoChi.main_alt_alt : ∀ (D : D7) (L : SizeData₂ D) (nch : NChoice D) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (π : D.nd.X i) (ρ : GE D.nd →* GL (Fin D.R.r) (D.nd.O i)), _root_.GlobalTheory.NFacts.NormChoiceFacts D nch → LevelStarExponents.lStar L < (D.nd.l i : ℝ) → (∀ k, D.nd.l i ≠ D.host.g k) → HG D.nd D.naut i → GoodR D.nd i r → π ∈ D.nd.Z i → GlobalTheory.IndefiniteRowSideFullHecke.BaseSizes.IsRankRPart D i (r π) ρ → NoChiOff i r Set.univ ∧ UnrOut i r Set.univ := by
  intro D L nch i r π ρ hF _ _ hHG hr _ hρ
  have hUnr := _root_.Formalism.MainNotions.N.admG4_of_goodR D i r hF.Conclusion1.1 hr
  have hSub := Formalism.MainNotions.N.galois_condition_six_of D i r hF.Conclusion2.2.1 hHG hr
  refine ⟨?_, ?_⟩
  · intro x _ hxZ u hu
    by_contra hu0
    refine hxZ (hSub x ⟨u, hu0, fun g => ?_⟩)
    have h := hu g
    rw [rTwO, GlobalTheory.UnrNoChi.mapM_twistM', Matrix.smul_mulVec] at h
    conv_rhs => rw [← h]
    rw [smul_smul, ← map_mul, MonoidHom.inv_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one,
      one_smul]
  · intro v hvl hvS hvQ x _ γ hγ
    have hχ := GlobalTheory.UnrNoChi.chi_one_eq_one i r π ρ hρ (hUnr π v hvl hvS hvQ γ hγ)
    have hx : rO D.nd i r x γ = 1 := by simp [rO, hUnr x v hvl hvS hvQ γ hγ]
    rw [rTwO, twistM]
    simp [hx, hχ]
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerExtra
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
noncomputable section
namespace GlobalTheory.LocEigAgree
theorem main_alt_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (i : D.nd.Loc) (Q Q' : D.naut.AV i) (sp : SplitPlace D.host.E), (∀ κ : GAf D.host.E D.R.nV, TrivOutside {sp.v} κ → (κ ∈ (P.M.loc i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ hκ : κ ∈ (P.M.loc i).J, (P.M.loc i).χ ⟨κ, hκ⟩ = 1) → ∀ Ds : Set (GAf D.host.E D.R.nV), (∀ x ∈ Ds, TrivOutside {sp.v} x) → (∀ x ∈ Ds, ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → x * κ ∈ Ds ∧ κ * x ∈ Ds) → {c : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J | ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c}.Finite → (∀ σ σ', IsLocS (P.H.av.S i Q) sp σ → IsLocS (P.H.av.S i Q') sp σ' → GlobalTheory.LocLanglands.cls σ = GlobalTheory.LocLanglands.cls σ') → ∀ F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F ≠ 0 → ∀ F' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q'), F' ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ → F' ≠ 0 → ∀ c c' : ℂ, NG.heckeD (P.M.loc i).J Ds F = c • F → NG.heckeD (P.M.loc i).J Ds F' = c' • F' → c = c' := by
  intro _hAF hL D P i Q Q' sp hJ Ds hDs hbi hfin hcls F hF hFT hF0 F' hF' hF'T hF'0 c c' hc hc'
  classical
  have hK : ∀ f ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ,
      ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ f = f := by
    intro f hf κ hκ
    obtain ⟨h1, h2⟩ := hJ κ hκ.2
    have hJκ : κ ∈ (P.M.loc i).J := h1.2 hκ.1
    have e := hf.2 ⟨κ, hJκ⟩
    rw [h2 hJκ] at e
    simpa using e
  have hJU : ∀ x ∈ Ds, ∀ x' ∈ Ds, (x⁻¹ * x' ∈ (P.M.loc i).J ↔ x⁻¹ * x' ∈ Umax D.host.E D.R.nV) :=
    fun x hx x' hx' => (hJ _ (GlobalTheory.HeckeScalarAll.trivOutside_mul (GlobalTheory.HeckeScalarAll.trivOutside_inv (hDs x hx))
      (hDs x' hx'))).1
  have hfinU : ((fun x : GAf D.host.E D.R.nV => (x : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV)) '' Ds).Finite := by
    let φ : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J → GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV := fun c =>
      if hc : ∃ x ∈ Ds, (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = c then (hc.choose : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV) else ((1 : GAf D.host.E D.R.nV) : GAf D.host.E D.R.nV ⧸ Umax D.host.E D.R.nV)
    refine (hfin.image φ).subset ?_
    rintro _ ⟨x, hx, rfl⟩
    have hc : ∃ y ∈ Ds, (y : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) = (x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J) := ⟨x, hx, rfl⟩
    refine ⟨(x : GAf D.host.E D.R.nV ⧸ (P.M.loc i).J), ⟨x, hx, rfl⟩, ?_⟩
    simp only [φ, dif_pos hc]
    have h1 := hc.choose_spec.2
    rw [QuotientGroup.eq] at h1
    exact QuotientGroup.eq.2 ((hJU _ hc.choose_spec.1 _ hx).1 h1)
  obtain ⟨R, hR1, hR2⟩ := GlobalTheory.HeckeScalarSph.exists_reps (Umax D.host.E D.R.nV) Ds hfinU
  have hH : ∀ f : GAf D.host.E D.R.nV → (P.M.loc i).wt.W, (∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ f = f) →
      NG.heckeD (P.M.loc i).J Ds f = ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ f := by
    intro f hf
    have hf' : ∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {sp.v} κ → NG.rt D.host.E D.R.nV κ f = f :=
      fun κ hκ ht => hf κ ⟨hκ, ht⟩
    have e1 : NG.heckeD (P.M.loc i).J Ds f = NG.heckeD (Umax D.host.E D.R.nV) Ds f := by
      funext g
      simp only [NG.heckeD]
      refine GlobalTheory.HeckeScalarAll.finsum_cosets_eq (P.M.loc i).J (Umax D.host.E D.R.nV) Ds (fun x => f (g * x)) hJU ?_
      intro x hx x' hx' hu
      have ht := GlobalTheory.HeckeScalarAll.trivOutside_mul (GlobalTheory.HeckeScalarAll.trivOutside_inv (hDs x hx)) (hDs x' hx')
      have h1 := congrFun (hf' _ hu ht) (g * x)
      simp only [NG.rt, LinearMap.coe_mk, AddHom.coe_mk] at h1
      rw [mul_assoc, mul_inv_cancel_left] at h1
      exact h1.symm
    rw [e1]
    exact GlobalTheory.HeckeScalarSph.heckeD_eq_sum (v := sp.v) hDs hR1 hR2 hf'
  obtain ⟨cX, hcX⟩ := GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) sp Ds hDs hbi R hR1 hR2
  obtain ⟨cX', hcX'⟩ := GlobalTheory.T.biInvariant_heckeOp_scalar_on_spherical_irreducible D.host.E D.R.nV _ _ _ (P.H.av.irr i Q') sp Ds hDs hbi R hR1 hR2
  have hcI := GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) _ R cX hcX
  have hcI' := GlobalTheory.T.rightTranslationSum_scalar_on_isotypicPart D.host.E D.R.nV _ _ _ (P.H.av.irr i Q') _ R cX' hcX'
  have hc1 : c = cX := by
    have e1 := hc
    rw [hH F (hK F hFT), hcI F hF (hK F hFT)] at e1
    exact smul_left_injective ℂ hF0 e1.symm
  have hc2 : c' = cX' := by
    have e1 := hc'
    rw [hH F' (hK F' hF'T), hcI' F' hF' (hK F' hF'T)] at e1
    exact smul_left_injective ℂ hF'0 e1.symm
  rw [hc1, hc2]
  let π : NG.AutRep D.host.E D.R.nV := ⟨(P.M.loc i).wt, P.H.av.S i Q, P.H.av.irr i Q⟩
  let π' : NG.AutRep D.host.E D.R.nV := ⟨(P.M.loc i).wt, P.H.av.S i Q', P.H.av.irr i Q'⟩
  obtain ⟨σ, hσ⟩ := GlobalTheory.LocCompSplit.exists_isLocS π sp
  obtain ⟨σ', hσ'⟩ := GlobalTheory.LocCompSplit.exists_isLocS π' sp
  have hcl := hcls σ σ' hσ hσ'
  obtain ⟨E⟩ : Nonempty (σ.ρ.Equiv σ'.ρ) := by
    have h2 : σ.cl = σ'.cl := eq_of_heq (Sigma.mk.inj hcl).2
    exact GlobalTheory.SmGL.IrrRep.cl_eq_iff.1 h2
  have hσ0 := hσ
  obtain ⟨ι, T0, hι, hιc, hT0i, hT0S, hT0e⟩ := hσ
  obtain ⟨ι', T0', hι', hιc', hT0i', hT0S', hT0e'⟩ := hσ'
  obtain rfl := GlobalTheory.splitPlace_completion_equiv_unique _ sp ι ι' hι hι' hιc hιc'
  obtain ⟨a, ha0, hafix⟩ := GlobalTheory.T.splitLocalComponent_has_fixedVector_of_isotypic D.host.E D.R.nV _ _ _ (P.H.av.irr i Q) sp σ hσ0 ι hι hιc F hF hF0 (hK F hFT)
  have hT0H : ∀ v, T0 (∑ γ ∈ R, σ.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) v) =
      ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ (T0 v) := by
    intro v
    rw [map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hT0e γ (hDs γ (hR1 γ hγ)) v
  have hT0H' : ∀ v, T0' (∑ γ ∈ R, σ'.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) v) =
      ∑ γ ∈ R, NG.rt D.host.E D.R.nV γ (T0' v) := by
    intro v
    rw [map_sum]
    exact Finset.sum_congr rfl fun γ hγ => hT0e' γ (hDs γ (hR1 γ hγ)) v
  have hT0fix : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v, NG.rt D.host.E D.R.nV κ (T0 a) = T0 a := by
    intro κ hκ
    rw [← hT0e κ hκ.2 a, hafix κ hκ]
  have hHa : ∑ γ ∈ R, σ.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) a = cX • a := by
    apply hT0i
    rw [hT0H, map_smul]
    exact hcX (T0 a) (hT0S a) hT0fix
  have hE : ∀ g v, E.toLinearEquiv (σ.ρ g v) = σ'.ρ g (E.toLinearEquiv v) := fun g v =>
    LinearMap.congr_fun (E.isIntertwining' g) v
  have ha'0 : E.toLinearEquiv a ≠ 0 := fun h => ha0 (E.toLinearEquiv.injective (by rw [h, map_zero]))
  have hHa' : ∑ γ ∈ R, σ'.ρ (Matrix.GeneralLinearGroup.map ι.toRingHom (sp.loc D.R.nV γ)) (E.toLinearEquiv a) =
      cX • E.toLinearEquiv a := by
    simp only [← hE, ← map_sum, hHa, map_smul]
  have hT0fix' : ∀ κ ∈ GlobalTheory.HeckeScalarSph.locK D.R.nV sp.v,
      NG.rt D.host.E D.R.nV κ (T0' (E.toLinearEquiv a)) = T0' (E.toLinearEquiv a) := by
    intro κ hκ
    rw [← hT0e' κ hκ.2, ← hE, hafix κ hκ]
  have key := hcX' (T0' (E.toLinearEquiv a)) (hT0S' _) hT0fix'
  rw [← hT0H', hHa', map_smul] at key
  have hne : T0' (E.toLinearEquiv a) ≠ 0 := fun h => ha'0 (hT0i' (by rw [h, map_zero]))
  exact smul_left_injective ℂ hne key
end GlobalTheory.LocEigAgree
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ImportsTerFurtherStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operator_eigen_good_place_second_alt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D), ∀ (X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp) (_ : GlobalTheory.NJoin.Agree X P.M P.rep), _root_.Formalism.MainNotions.SumRepresentations.provisionFortyOne D → _root_.Formalism.MainNotions.SumRepresentations.adm7_alt D → Formalism.MainNotions.SumRepresentations.tieLab D → ∀ (i : D.nd.Loc) (hμ : Formalism.IndefR.RecTie.Used0 D (D.nd.mu i)) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i), ∀ h, GlobalTheory.Hk3.IsOpsV X.R j (X.tupT (D.nd.mu i)) h → ∀ Pp, GlobalTheory.Hk3.Good X.R (X.tupT (D.nd.mu i)) Pp → Formalism.UG.IsInertAt D.host.F D.host.E (Pp.under (𝓞 D.host.F)) Pp → ∀ d, GlobalTheory.Hk3.IsLab (Formalism.IndefR.Links.Vc D j) Pp d → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E))) (Dv : InertDatum D.host.E D.R.nV v Pp), NG.OverPl Pp v → ∃ h0 : Formalism.UG.GU Dv.σw D.R.nV → ℂ, h0 ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw D.R.nV) ∧ ∀ (f' : D.what₂.Mt (D.nd.mu i) (j.1 + 1)) (y' : (X.R.HV j (X.tupT (D.nd.mu i))).H) (c : ℂ), X.R.extV j (X.tupT (D.nd.mu i)) y' = X.fn hμ j f' → (∀ κ ∈ Umax D.host.E D.R.nV, TrivOutside {v} κ → NG.rt D.host.E D.R.nV κ ((P.M.loc i).real (hj ▸ f')) = (P.M.loc i).real (hj ▸ f')) → heckeFunI D.host.E D.R.nV (Umax D.host.E D.R.nV) Dv h0 ((P.M.loc i).real (hj ▸ f')) = c • (P.M.loc i).real (hj ▸ f') → h Pp (Finsupp.single d 1) y' = c • y' := by
  first | exact @_root_.GlobalTheory.InertTransport.main_alt_alt | exact _root_.GlobalTheory.InertTransport.main_alt_alt | (intros; apply _root_.GlobalTheory.InertTransport.main_alt_alt <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealPins
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
open Classical in
structure IndefiniteRealisationNormalisation {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
    {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
    {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop where
  cfEq : Q.Rl.C = Rc.T.n.cf
  qGuard : Formalism.IndefR.FWT.QGuard Q.Rl.toRealDat
  hF : D.host.F = maximalRealSubfield D.host.E
  phsOne : ∀ i, Q.Rl.phs i = 1
  prXunit : Formalism.IndefR.Seed.PrIso Q.Rl.MX Q.Rl.cX Q.Rl.prX
  grpRecPin : ∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ Q.Rl.toRealDat.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ kv, ((plg kv : Q.Rl.toRealDat.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧
    (∀ g, D.what₂.embLL ((idemOf P.A3.A.X).coeff g) = D.ntypes.e0.coeff ((Q.Rl.eG.trans Q.cG) g)) ∧
    (∀ kv, Q.Rl.toRealDat.C.P.Div kv.1 (plg kv).1) ∧
    ∀ g kv, Q.Rl.toRealDat.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((Q.Rl.eG.trans Q.cG) g kv)
  fdiag : ∀ i, IsFDiag (Wc D i) ∧ IsFDiag (Vc D i)
  pgEq : Q.Rl.Pg = Rc.T.ker.Pr.vGs.image (Formalism.L2.Host.CT.plMap Rc.T.ker.seam.iE)
  tSfin : Q.tS ∈ Formalism.L2.Theta.GfC (Yc D 0)
  tSpin : (∃ t ∈ Formalism.L2.Theta.GfC (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq t) →
    Formalism.IndefR.AutomorphicEvaluation.ConjLevel Q.tS⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq Q.tS
  eGtie : P.I.eG = Q.Rl.eG.trans Q.cG
  betaStd : (∀ i, Q.Rl.βV i = 1) ∧ Q.Rl.βX = 1
  bR_read : ∀ x i, Q.bR x i = D.eMu (Q.wdD x) (D.jN (Q.wdD x) (P.I.eNu (Q.wdD x)
    (Pi.single (Fin.cast (congrArg P.Dc.a (Q.wU_wdD x)).symm i) 1)))
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
def IndefiniteRealisationExtends (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Prop :=
  (∃ t ∈ Formalism.L2.Theta.GfC (Yc D 0), Formalism.IndefR.AutomorphicEvaluation.ConjLevel t⁻¹ (levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true))) (Q.ιS ⁻¹' seeKS S.X) (fun k => seeChiS S.X (Q.ιS k)) ∧
      Formalism.L2.SG.RowLevelMatch.RowLevelMatchAt Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 S.X Q.instEq t) ∧
    ∃ c' : ℝ, Formalism.IndefR.AutomorphicEvaluation.EvalTieT (Q.Rl.MY 0) Q.Rl.ν0 Q.Rl.fd0 (Q.Rl.toRealDat.EEat (Q.Rl.toRealDat.levR (faceT P Dcf Spf Zscf).lv2 true)) S.X S.G Q.ιS Q.tS c'
end Formalism.IndefR
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IndefRRealRec
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR.Links Formalism.IndefR.Cx
namespace Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC} {ex : Extra D L hT Gi Gl K Y cX}
variable {Rc : _root_.Formalism.L2.RecTAlt ex} {P : RowSideFamily ex} {Dcf : ∀ Zs : DefSub P.A3.fam3.amb3, DefCols (P.A3.side3 P.Ps P.ψs Zs)}
  {Spf : ∀ Zs : DefSub P.A3.fam3.amb3, SPer (Dcf Zs)} {Zscf : DefSub P.A3.fam3.amb3 → IndefScale P.A3.fam3.base3}
  {S : _root_.Formalism.L2.SG.SpectralTiesReal.STiesRAlt Rc} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
theorem finrank_WL_eq_dW (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) :
    Module.finrank D.what₂.LL (Q.Rl.toRealDat.WL Q.F.lv2 false i) = (P.A3.indefDown P.S0).dW i :=
  congrFun (dW_of_heq (congrArg (fun Z => P.A3.side3 P.P0 P.ψ0 Z) Q.zs) Q.s0) i
def indefiniteDownJoin (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) (i : Fin D.R.m) (y : Fin ((P.A3.indefDown P.S0).dW i) → D.what₂.LL) :
    Fin (Q.Rl.nW i) → D.what₂.LL :=
  Formalism.IndefR.NX.jDL Q.Rl Q.F.lv2 i (y ∘ Fin.cast (_root_.Formalism.IndefR.finrank_WL_eq_dW Q i))
set_option genInjectivity false in
set_option genSizeOfSpec false in
structure IndefiniteRealisationRecursion (Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks) : Type 1 where
  tupT : D.what₂.Tup → P.T
  hm : 0 < D.R.m
  hTop : Formalism.IndefR.RecTie.TopMultH Q.Rl.toRealDat
  hinj : ∀ i t, Function.Injective (Q.Rl.toRealDat.extV i t)
  Ish : Formalism.IndefR.RecTie.RowIds (Formalism.BasicNotions.RowSide.sharp D) (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) true
  I0 : Formalism.IndefR.RecTie.RowIds ex.p0.s (Formalism.IndefR.RecTie.toChainReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop) false
  IL : Formalism.IndefR.RecTie.LiftIds (Formalism.IndefR.RecTie.toLiftReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj)
  Kc : Formalism.IndefR.RecTie.ColReal D
  E : EigIdx D Y
  labPi : E.Pi → P.A3.A.fam.base.Ix
  PY : Formalism.IndefR.principalLevelFrame.RowPsi (Yc D 0) D.R.r
  PW : ∀ i, Formalism.IndefR.principalLevelFrame.RowPsi (Wc D i) D.R.r
  eFT : D.what₂.FT ≃ Formalism.IndefR.principalLevelFrame.FTR Q.Rl.θ PY (Q.Rl.MY 0)
    (fun b => levS _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b)))
    (fun b => Formalism.IndefR.Lev.levChi _ (Q.Rl.βY 0) (Q.Rl.dat0 (Q.Rl.levR (faceT P Dcf Spf Zscf).lv2 b))) (fun _ => Q.Rl.e0)
  piOf : E.Pi → HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ
  ιW : ∀ i, ↥(Formalism.L2.Theta.GfC (Yc D 0)) →* ↥(Formalism.L2.Theta.GfC (Wc D i))
  Tp : Formalism.L2.Host.TupTied D Q.Rl.C ex.nch
  recR : Formalism.IndefR.RecTie.RecReal Q.Rl.toRealDat (faceT P Dcf Spf Zscf).lv2 tupT hm hTop hinj ex.p0 Ish I0 IL Kc E labPi PY PW eFT piOf ιW ex.nch Tp
  tpEq : HEq Tp Rc.T.n.tp
  tupTie : ∀ μ, Formalism.IndefR.RecTie.Used0 D μ → P.I.tup (tupT μ) = μ
  tupT_tup : ∀ t, tupT (P.I.tup t) = t
  muEq : Q.Rl.mu = P.S0.μ
  mtRead : Formalism.IndefR.RecTie.MtRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (twPOf P tupT tupTie)
  mjRead : Formalism.IndefR.RecTie.MjRead Q.Rl.toRealDat Q.F.lv2 tupT hm hTop hinj IL (fun i => (P.A3.indefDown P.S0).dW i)
    (fun i y => P.I.jW i y) (_root_.Formalism.IndefR.indefiniteDownJoin Q)
namespace RealRec
variable {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks} (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q)
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tupT_inj_used {μ μ' : D.what₂.Tup} (hμ : Formalism.IndefR.RecTie.Used0 D μ) (hμ' : Formalism.IndefR.RecTie.Used0 D μ')
    (h : Qr.tupT μ = Qr.tupT μ') : μ = μ' := by
  apply Qr.Tp.xi_inj
  rw [← Qr.recR.tupXi μ hμ, ← Qr.recR.tupXi μ' hμ', h]
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tupleRead_baseTuple_eq_family : Qr.tupT D.what₂.mu0 = P.A3.A.μ0 :=
  Q.charW.base.lev.xi_inj (by rw [Qr.recR.tupXi D.what₂.mu0 (Or.inl rfl), Qr.Tp.trueColumnChoices_heckeChar_reference_eq_one, Q.charW.base.lev.xi_base])
theorem _root_.Formalism.IndefR.IndefiniteRealisationRecursion.tw_iff (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) (w : D.what₂.places.Pl) : D.plEq w ∈ Q.Rl.twPl ↔ D.what₂.muAt w ≠ D.what₂.mu0 := by
  have h0 := Qr.tupleRead_baseTuple_eq_family
  constructor
  · intro hw he
    apply Q.charW.tup.mu_ne (D.plEq w) hw
    rw [← Qr.recR.tupAt w, he, h0]
  · intro hne
    by_contra hw
    apply hne
    apply Qr.tupT_inj_used (Or.inr ⟨w, rfl⟩) (Or.inl rfl)
    rw [Qr.recR.tupAt w, Q.charW.tup.mu_off (D.plEq w) hw, h0]
end RealRec
namespace RealRec
variable {Q : _root_.Formalism.IndefR.IndefiniteRealisation Rc P Dcf Spf Zscf S Ks}
def _root_.Formalism.IndefR.IndefiniteRealisationRecursion.PartsRow (Qr : _root_.Formalism.IndefR.IndefiniteRealisationRecursion Q) : Prop :=
  Formalism.IndefR.RecTie.PartsRec Q.Rl.toRealDat Q.F.lv2 Qr.tupT Qr.hm Qr.PY Qr.PW Qr.eFT Qr.E Qr.labPi Qr.piOf Qr.Ish.prt Qr.IL.prtW
end RealRec
end Formalism.IndefR
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsTameMuPlGwStatement
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_weil_mu_tame_of_is_true : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D : D7) (P : _root_.GlobalTheory.NPin.CharacterChoiceData hL D) (S : Reading P.T), _root_.GlobalTheory.NPin.IsFaithfulReading P S → ∀ (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (hw : IsSplitPl D.host (D.naut.plGw k v)), GlobalTheory.SplitWeil.IsTame (S i _ hw).mu := by
  first | exact @_root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw | exact _root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw | (intros; apply _root_.GlobalTheory.PendOf.isTame_reading_mu_at_split_plGw <;> assumption)
end
end

