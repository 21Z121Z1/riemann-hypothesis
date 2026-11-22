import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0243
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0220
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0216
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0204
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0221
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0244
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModelsOfCoversRealPlace

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitTorusRefinedFlagStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_torus_refined_flag : ∀ {n a b : ℕ} {ε : Fin n → Bool} {j : Fin a → ℕ} {W : Flag n a} {W' : Flag n b} {β : Fin b → Fin a} {p : Fin (a + 1) → Fin (b + 1)}, IsIsoFlag ε j W → IsIsoFlag ε (fun _ => 1) W' → (∀ i, W' (p i) = W i) → W' (Fin.last b) = W (Fin.last a) → (∀ l i, β l = i ↔ p i.castSucc ≤ l.castSucc ∧ l.castSucc < p i.succ) → ∀ {x : Fin a → ℝ} {t : UJ ε}, IsSplit ε W x t → IsSplit ε W' (x ∘ β) t := by
  first | exact @GlobalTheory.RealInd.Stages.isSplit_of_refine | exact GlobalTheory.RealInd.Stages.isSplit_of_refine | (intros; apply GlobalTheory.RealInd.Stages.isSplit_of_refine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StageFunctionContinuousStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_function_continuous : ∀ {n : ℕ} {ε : Fin n → Bool} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Subgroup (UJ ε)) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (μ : Measure ↥(KG ε ⊓ M)) [IsProbabilityMeasure μ], (∀ f : Fsp, ‖ι f‖ ^ 2 = ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ) → ∀ {F : UJ ε → U}, Continuous F → (∀ g, restr M F g ∈ Fsp) → Continuous (stageFun M Fsp ι F) := by
  first | exact @GlobalTheory.RealInd.Stages.stageFun_continuous | exact GlobalTheory.RealInd.Stages.stageFun_continuous | (intros; apply GlobalTheory.RealInd.Stages.stageFun_continuous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StageFunctionNormIntegralStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_function_norm_integral : ∀ {n : ℕ} {ε : Fin n → Bool} {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] [NormedAddCommGroup V] [InnerProductSpace ℂ V] (M : Subgroup (UJ ε)) (Fsp : Submodule ℂ (UJ ε → U)) (ι : Fsp →ₗ[ℂ] V) (μ : Measure ↥(KG ε ⊓ M)) [IsProbabilityMeasure μ], (∀ f : Fsp, ‖ι f‖ ^ 2 = ∫ k : ↥(KG ε ⊓ M), ‖f.1 k‖ ^ 2 ∂μ) → ∀ {F : UJ ε → U}, Continuous F → (∀ g, restr M F g ∈ Fsp) → ∫ k : KG ε, ‖stageFun M Fsp ι F k‖ ^ 2 ∂muK ε = ∫ k : KG ε, ‖F k‖ ^ 2 ∂muK ε := by
  first | exact @GlobalTheory.RealInd.Stages.stageFun_normSq_integral | exact GlobalTheory.RealInd.Stages.stageFun_normSq_integral | (intros; apply GlobalTheory.RealInd.Stages.stageFun_normSq_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.StageParameterPairingShiftStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
open PI.DSInfCharCap (actU Egl)
open GlobalTheory.RealInd.Stages Finset GlobalTheory.FlagMeas Formalism.REAL

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stage_parameter_pairing_shift : ∀ {a b : ℕ} (n : ℕ) (j : Fin a → ℕ) (β : Fin b → Fin a) (s : Fin a → ℂ) (y : Fin b → ℝ), (∀ i, 1 ≤ j i) → (∀ i, #{l | β l = i} = j i) → (∀ i, ∑ l with β l = i, rho n (fun _ => 1) l = (j i : ℂ) * rho n j i) → (∀ x : Fin a → ℝ, pairing (fun _ => 1) (stageS j β s y + rho n fun _ => 1) (x ∘ β) = pairing j (s + rho n j) x) ∧ ∀ x : Fin b → ℝ, (∀ i, ∑ l with β l = i, x l = 0) → pairing (fun _ => 1) (stageS j β s y) x = pairing (fun _ => 1) (fun l => Complex.I * y l) x := by
  first | exact @GlobalTheory.RealInd.Stages.stageS_pairings | exact GlobalTheory.RealInd.Stages.stageS_pairings | (intros; apply GlobalTheory.RealInd.Stages.stageS_pairings <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SuppAtUnitaryGroupLocalToAdelicEmbeddingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.SplitHecke GlobalTheory.LFun.ConjPlace GlobalTheory.AdelicU GlobalTheory.LFun.SplitTie

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.suppAt_unitaryGroupLocalToAdelicEmbedding : ∀ (D : D7) (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)), w.under (𝓞 D.host.F) = v → ∀ ε : AE D, Formalism.L2.NTheta.IsIdemAt ε w → ∀ g : Gv V v, SuppAt ε V (embV V v g) := by
  first | exact @GlobalTheory.SuppAtPlace.suppAt_embV | exact GlobalTheory.SuppAtPlace.suppAt_embV | (intros; apply GlobalTheory.SuppAtPlace.suppAt_embV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Formalism.L2.SG.AdBridge

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes in

theorem map_thetaV_eq_one (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) (AF I.F ⊗[I.F] I.E))
    (hM : M.map (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E)) = 1) : M.map (thetaV I v) = 1 := by
  letI : Algebra I.F ℂ := v.embedding.toAlgebra
  let evI : Ainf I.F →ₐ[I.F] ℂ :=
    { toRingHom := (InfinitePlace.Completion.extensionEmbedding v).comp
        (Pi.evalRingHom (fun w : InfinitePlace I.F => w.Completion) v)
      commutes' := fun c => evV_algebraMap I v c }
  let φA : I.E →ₐ[I.F] ℂ := { I.φ v with commutes' := I.φ_over v }
  let θ' := Algebra.TensorProduct.lift evI φA (fun _ _ => Commute.all _ _)
  have key : ∀ z : AF I.F ⊗[I.F] I.E, thetaV I v z =
      θ' (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E) z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero, map_zero]
    | tmul a x =>
      rw [thetaV_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lift_tmul]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  have e : M.map (thetaV I v) = (M.map (Algebra.TensorProduct.map (fstA I.F) (AlgHom.id I.F I.E))).map θ' := by
    ext i j; simp only [Matrix.map_apply]; exact key _
  rw [e, hM]
  exact Matrix.map_one _ (map_zero θ') (map_one θ')

theorem fst_eq_one_of_bridge (I : AutInst) (e : I.GA ≃ₜ* HAd I) (hB : IsBridge I e) (x : I.GA) (z : HAd I)
    (hz : e x = z) (hx : (hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.fstA I.F) (AlgHom.id I.F I.E)) = 1) :
    x.1 = 1 := by
  funext v
  apply Subtype.ext
  apply Units.ext
  have h1 := (hB x).1 v
  have hP : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v)
  show uMat (x.1 v) = 1
  rw [h1]
  unfold ofHAInf
  rw [hz]
  rw [map_thetaV_eq_one I v _ hx, Matrix.mul_one, Matrix.nonsing_inv_mul _ hP]

theorem iota_fst_eq_one {D : D7} (y : GA D (D.sp.Y 0)) (hy : y ∈ GfC (D.sp.Y 0)) :
    (Formalism.IndefR.RationalEmbedding.iota D y).1 = 1 := by
  refine fst_eq_one_of_bridge _ _ (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) _ y
    ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply y) ?_
  have h := congrArg (fun g : GL (Fin (D.sp.Y 0).rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Ainf D.host.F ⊗[D.host.F] D.host.E) =>
    g.val) (MonoidHom.mem_ker.1 hy)
  exact h

theorem castGA_fst {I I' : AutInst} (h : I = I') (x : I.GA) (hx : x.1 = 1) : (castGA h x).1 = 1 := by
  subst h; exact hx

theorem real_one {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (y : GA D (D.sp.Y 0)) (hy : y ∈ GfC (D.sp.Y 0)) : (iotaX X h y).1 = 1 :=
  castGA_fst h.symm _ (iota_fst_eq_one y hy)

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix

section Frame

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mulVec_mem_intAf (U : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hU : ∀ i j, U i j ∈ Formalism.L2.Herm.intAf F E) (w : Fin n → E ⊗[F] Formalism.L2.Herm.Af F)
    (hw : ∀ i, w i ∈ Formalism.L2.Herm.intAf F E) (i : Fin n) : (U *ᵥ w) i ∈ Formalism.L2.Herm.intAf F E := by
  rw [Matrix.mulVec, dotProduct]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hU i j) (hw j)

theorem mem_hatL_iff_of_St {β M : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {Λ : Submodule (𝓞 E) (Fin n → E)}
    (hF : Formalism.L2.DIV.IsFrame β Λ) (hM : M ∈ Formalism.L2.DIV.St β) (x : Fin n → E ⊗[F] Formalism.L2.Herm.Af F) :
    x ∈ Formalism.L2.Herm.hatL (F := F) Λ ↔ M.val *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  obtain ⟨u, rfl⟩ := hM
  have hint : ∀ v : GL (Fin n) (Formalism.L2.Herm.intAf F E), ∀ i j,
      (Formalism.L2.DIV.intGL F E n v).val i j ∈ Formalism.L2.Herm.intAf F E :=
    fun v i j => (v.val i j).2
  have e : (β⁻¹).val *ᵥ ((Formalism.L2.DIV.frGL β u).val *ᵥ x) =
      (Formalism.L2.DIV.intGL F E n u).val *ᵥ ((β⁻¹).val *ᵥ x) := by
    have : Formalism.L2.DIV.frGL β u = β * Formalism.L2.DIV.intGL F E n u * β⁻¹ := rfl
    rw [this, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  rw [hF, hF, e]
  constructor
  · intro hw i
    exact mulVec_mem_intAf _ (hint u) _ hw i
  · intro hw i
    have e2 : (β⁻¹).val *ᵥ x = (Formalism.L2.DIV.intGL F E n u⁻¹).val *ᵥ
          ((Formalism.L2.DIV.intGL F E n u).val *ᵥ ((β⁻¹).val *ᵥ x)) := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one,
        Matrix.one_mulVec]
    rw [e2]
    exact mulVec_mem_intAf _ (hint u⁻¹) _ hw i

end Frame

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix Formalism.L2.SG.AdBridge

theorem ofHAFin_eq (I : AutInst) (z : HAd I) :
    ofHAFin I z = ((hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F) (AlgHom.id I.F I.E))).map
      (Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E) := by
  unfold ofHAFin
  ext i j
  simp only [Matrix.map_apply]
  induction (hmat I z i j) using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [tauF_tmul, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.comm_tmul]
    rfl
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]

theorem fmat_eq_of_bridge (I : AutInst) (e : I.GA ≃ₜ* HAd I) (hB : IsBridge I e) (x : I.GA) (z : HAd I)
    (hz : e x = z) : I.fmat x.2 =
      ((hmat I z).map (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA I.F) (AlgHom.id I.F I.E))).map
        (Algebra.TensorProduct.comm I.F (Formalism.MainNotions.S.Af I.F) I.E) := by
  rw [(hB x).2, hz, ofHAFin_eq]

theorem Lv_iff {D : D7} (z : Fin (D.sp.Y 0).rank → D.host.E) :
    z ∈ Formalism.L2.SG.InstExistsPf.Lv D ↔ z ∈ Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0 := by
  constructor
  · intro hz
    exact ⟨_, hz, (D.sp.Y 0).frame.equivFun.apply_symm_apply z⟩
  · rintro ⟨w, hw, rfl⟩
    show (D.sp.Y 0).frame.equivFun.symm ((D.sp.Y 0).frame.equivFun w) ∈ (D.sp.Y 0).L0
    simpa using hw

theorem Lf_eq {D : D7} :
    @Eq (Submodule (Formalism.MainNotions.S.IntAf (Formalism.L2.SG.InstExistsPf.instOf D).F (Formalism.L2.SG.InstExistsPf.instOf D).E)
      (Fin (Formalism.L2.SG.InstExistsPf.instOf D).n → (Formalism.L2.SG.InstExistsPf.instOf D).E ⊗[(Formalism.L2.SG.InstExistsPf.instOf D).F]
        Formalism.MainNotions.S.Af (Formalism.L2.SG.InstExistsPf.instOf D).F))
      (Formalism.L2.SG.InstExistsPf.instOf D).Lf
      (Formalism.L2.Herm.hatL (F := D.host.F) (E := D.host.E) (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0)) := by
  show Submodule.span _ _ = Submodule.span _ _
  congr 1
  ext w
  constructor
  · rintro ⟨⟨z, hz⟩, rfl⟩
    exact ⟨z, (Lv_iff z).1 hz, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, (Lv_iff z).2 hz⟩, rfl⟩

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

open scoped TensorProduct
open Matrix Formalism.L2.SG.AdBridge

theorem conj_mem_St {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {β a M : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} (hM : M ∈ Formalism.L2.DIV.St β) :
    a * M * a⁻¹ ∈ Formalism.L2.DIV.St (a * β) := by
  obtain ⟨u, rfl⟩ := hM
  refine ⟨u, ?_⟩
  show a * β * Formalism.L2.DIV.intGL F E n u * (a * β)⁻¹ = a * (β * Formalism.L2.DIV.intGL F E n u * β⁻¹) * a⁻¹
  group

theorem iota_snd_mem_Kset {D : D7} (β : GL (Fin (D.sp.Y 0).rank) (EAf D))
    (hF : Formalism.L2.DIV.IsFrame β (Formalism.L2.Herm.crdLat (D.sp.Y 0) (D.sp.Y 0).L0)) (y : GA D (D.sp.Y 0))
    (hy : finE (D.sp.Y 0) y ∈ Formalism.L2.DIV.St β) :
    (Formalism.IndefR.RationalEmbedding.iota D y).2 ∈ (Formalism.IndefR.RationalEmbedding.inst D).Kset := by
  have hfm := fmat_eq_of_bridge _ _ (Formalism.IndefR.RationalEmbedding.iota_symm_isBridge D) (Formalism.IndefR.RationalEmbedding.iota D y) y
    ((Formalism.IndefR.RationalEmbedding.iota D).symm_apply_apply y)
  intro x
  show x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf ↔
    ((Formalism.L2.SG.InstExistsPf.instOf D).fmat (Formalism.IndefR.RationalEmbedding.iota D y).2) *ᵥ x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Lf
  rw [hfm, Lf_eq]
  exact mem_hatL_iff_of_St hF hy x

theorem castGA_snd_Kset {I I' : AutInst} (h : I = I') (x : I.GA) (hx : x.2 ∈ I.Kset) : (castGA h x).2 ∈ I'.Kset := by
  subst h; exact hx

end GlobalTheory.SeeMatchOnto

namespace GlobalTheory.SeeMatchOnto

theorem onto : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ γ : G0g D.nd, ∃ k ∈ X.B.I.Kset, cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = γ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h hLev hGrp hMod cG t hιE hpin hE0 ht hConj hFrame γ
  obtain ⟨κ, hκf, hκp, hκr⟩ := GlobalTheory.LevelRowsObj.liftsExist hLev (cG.symm γ)
  set y : GA D (Yc D 0) := t * κ * t⁻¹ with hydef
  have hy : y ∈ GfC (Yc D 0) := (GfC _).mul_mem ((GfC _).mul_mem ht hκf) ((GfC _).inv_mem ht)
  have h1 := real_one X h y hy
  have hy' : (iotaX X h).symm (1, (iotaX X h y).2) = y := by
    rw [← h1]; exact (iotaX X h).symm_apply_apply y
  refine ⟨(iotaX X h y).2, ?_, ?_⟩
  · have hS : finE (Yc D 0) y ∈ Formalism.L2.DIV.St (finE (Yc D 0) t * R.βY 0) := by
      rw [hydef, map_mul, map_mul, map_inv]
      exact conj_mem_St (Formalism.L2.DIV.parLev_St hκp)
    exact castGA_snd_Kset h.symm _ (iota_snd_mem_Kset _ hFrame y hS)
  · have hk : kap X h t (iotaX X h y).2 = κ := by
      unfold kap
      rw [hy']
      show (t⁻¹ * (t * κ * t⁻¹) * t : GA D (Yc D 0)) = κ
      group
    rw [hk, hκr, MulEquiv.apply_symm_apply]

end GlobalTheory.SeeMatchOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoModerateGrowthSizeDifferenceQuotient
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Grow GlobalTheory.Size GlobalTheory.Mem.AutSpace Filter
open scoped ENNReal NNReal Topology

namespace GlobalTheory.Size.DiffQuot

theorem norm_taylor_le {f f₁ f₂ : ℝ → ℂ} (d1 : ∀ s, HasDerivAt f (f₁ s) s) (d2 : ∀ s, HasDerivAt f₁ (f₂ s) s)
    {B t : ℝ} (hB0 : 0 ≤ B) (hB : ∀ s ∈ Set.Icc (-|t|) |t|, ‖f₂ s‖ ≤ B) :
    ‖f t - f 0 - (t : ℂ) * f₁ 0‖ ≤ B * |t| * |t| := by
  have hI : Convex ℝ (Set.Icc (-|t|) |t|) := convex_Icc _ _
  have h0 : (0 : ℝ) ∈ Set.Icc (-|t|) |t| := ⟨neg_nonpos.mpr (abs_nonneg t), abs_nonneg t⟩
  have ht : t ∈ Set.Icc (-|t|) |t| := ⟨neg_abs_le t, le_abs_self t⟩

  have h1 : ∀ s ∈ Set.Icc (-|t|) |t|, ‖f₁ s - f₁ 0‖ ≤ B * |t| := by
    intro s hs
    have hmv := hI.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f₁) (f' := f₂)
      (fun x _ => (d2 x).hasDerivWithinAt) hB h0 hs
    refine hmv.trans ?_
    rw [sub_zero, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨hs.1, hs.2⟩) hB0

  have hg : ∀ s ∈ Set.Icc (-|t|) |t|, HasDerivWithinAt (fun u : ℝ => f u - (u : ℂ) * f₁ 0) (f₁ s - f₁ 0)
      (Set.Icc (-|t|) |t|) s := by
    intro s _
    have hc : HasDerivAt (fun u : ℝ => (u : ℂ) * f₁ 0) (f₁ 0) s := by
      simpa using ((hasDerivAt_id s).ofReal_comp).mul_const (f₁ 0)
    exact ((d1 s).sub hc).hasDerivWithinAt
  have hmv := hI.norm_image_sub_le_of_norm_hasDerivWithin_le hg h1 h0 ht
  have e : f t - f 0 - (t : ℂ) * f₁ 0 = (f t - (t : ℂ) * f₁ 0) - (f 0 - ((0 : ℝ) : ℂ) * f₁ 0) := by
    push_cast; ring
  rw [e]
  refine hmv.trans (le_of_eq ?_)
  rw [sub_zero, Real.norm_eq_abs]

theorem tendsto_growthSize_diffQuot : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau) (N : ℕ), ∀ X ∈ lieAt V τ, ∀ φ ∈ GlobalTheory.Mem.AutSpace.SmFun θ V, GlobalTheory.Size.growthSob θ V 2 N φ ≠ ⊤ → Filter.Tendsto (fun t : ℝ => GlobalTheory.Size.growthSize V N (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
  intro D θ hθ V τ N X hX φ hφ hS
  have hφ1 : Rder θ V τ X φ ∈ SmFun θ V := Rder_mem hφ hX

  have hw : growthSize V N (Rder θ V τ X (Rder θ V τ X φ)) ≠ ⊤ := by
    have hl : IsLieWord V [(τ, X), (τ, X)] := by
      intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> exact hX
    have h2 := growthSize_rWord_ne_top_of_le hθ hφ hS hl (by simp)
    simpa only [rWord, wordAct_cons, wordAct_nil] using h2
  obtain ⟨C, hC⟩ := modGrowthExp_iff.2 hw
  have hC0 : 0 ≤ C := nonneg_of_growth hC

  obtain ⟨K, hK⟩ := exists_height_le_of_isCompact V
    (isCompact_Icc.image (GlobalTheory.Mem.Lift.continuous_oneP hθ hX) :
      IsCompact (oneP θ V τ X '' Set.Icc (-1 : ℝ) 1))
  have hK1 : 1 ≤ K := (one_le_height V _).trans (hK _ ⟨0, ⟨by norm_num, by norm_num⟩, rfl⟩)
  have hK0 : 0 ≤ K := by linarith

  have key : ∀ t : ℝ, |t| ≤ 1 → t ≠ 0 → ∀ g,
      ‖(((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) g‖ ≤
        C * K ^ N * |t| * height V g ^ N := by
    intro t ht1 ht0 g
    have d1 : ∀ s, HasDerivAt (fun s => φ (g * oneP θ V τ X s)) (Rder θ V τ X φ (g * oneP θ V τ X s)) s :=
      fun s => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hφ hX g') g s
    have d2 : ∀ s, HasDerivAt (fun s => Rder θ V τ X φ (g * oneP θ V τ X s))
        (Rder θ V τ X (Rder θ V τ X φ) (g * oneP θ V τ X s)) s :=
      fun s => GlobalTheory.Mem.Lift.hasDerivAt_oneP hθ hX (fun g' => GlobalTheory.Mem.Lift.hasDerivAt_Rder hφ1 hX g') g s
    have hg0 : 0 ≤ height V g := (height_pos V g).le
    have hB0 : 0 ≤ C * (height V g * K) ^ N := mul_nonneg hC0 (pow_nonneg (mul_nonneg hg0 hK0) N)
    have hB : ∀ s ∈ Set.Icc (-|t|) |t|,
        ‖Rder θ V τ X (Rder θ V τ X φ) (g * oneP θ V τ X s)‖ ≤ C * (height V g * K) ^ N := by
      intro s hs
      have hs1 : s ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith [hs.1], by linarith [hs.2]⟩
      refine (hC _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_pos V _).le ?_ N) hC0)
      exact (height_mul_le V _ _).trans (mul_le_mul_of_nonneg_left (hK _ ⟨s, hs1, rfl⟩) hg0)
    have hT := norm_taylor_le d1 d2 hB0 hB
    have e0 : oneP θ V τ X 0 = 1 := GlobalTheory.Mem.Lift.oneP_zero (V := V) (τ := τ) (X := X) hθ
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
    have hval : (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) g =
        (t : ℂ)⁻¹ * (φ (g * oneP θ V τ X t) - φ (g * oneP θ V τ X 0) -
          (t : ℂ) * Rder θ V τ X φ (g * oneP θ V τ X 0)) := by
      simp only [e0, mul_one, rTr, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
    have hta : 0 < |t| := abs_pos.mpr ht0
    rw [hval, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    calc |t|⁻¹ * ‖φ (g * oneP θ V τ X t) - φ (g * oneP θ V τ X 0) -
          (t : ℂ) * Rder θ V τ X φ (g * oneP θ V τ X 0)‖
        ≤ |t|⁻¹ * (C * (height V g * K) ^ N * |t| * |t|) :=
          mul_le_mul_of_nonneg_left hT (inv_nonneg.mpr hta.le)
      _ = C * K ^ N * |t| * height V g ^ N := by
          field_simp
          ring

  have hev : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ, |t| ≤ 1 ∧ t ∈ ({0}ᶜ : Set ℝ) := by
    refine (eventually_nhdsWithin_of_eventually_nhds ?_).and eventually_mem_nhdsWithin
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) one_pos] with t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    exact ht.le
  have hle : ∀ᶠ t : ℝ in nhdsWithin (0 : ℝ) {0}ᶜ,
      GlobalTheory.Size.growthSize V N (((t : ℂ)⁻¹) • (rTr V (oneP θ V τ X t) φ - φ) - Rder θ V τ X φ) ≤
        ENNReal.ofReal (C * K ^ N * |t|) := by
    filter_upwards [hev] with t ht
    have ht0 : t ≠ 0 := by simpa using ht.2
    exact (growthSize_le_iff (mul_nonneg (mul_nonneg hC0 (pow_nonneg hK0 N)) (abs_nonneg t))).2
      (key t ht.1 ht0)
  have hlim : Filter.Tendsto (fun t : ℝ => ENNReal.ofReal (C * K ^ N * |t|)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
    have h0 : Filter.Tendsto (fun t : ℝ => C * K ^ N * |t|) (nhds 0) (nhds 0) := by
      simpa using (continuous_abs.tendsto (0 : ℝ)).const_mul (C * K ^ N)
    simpa using (ENNReal.tendsto_ofReal h0).mono_left nhdsWithin_le_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Filter.Eventually.of_forall fun _ => zero_le) hle

end GlobalTheory.Size.DiffQuot

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStepCentredBlockParametersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaChainStep_centred_block_parameters : ∀ (D : D7) (k : Fin D.R.m) (τ : D.what₂.Tau), ∃ al be ga de : List ℚ, Centred D al be ga de ∧ parA (Ptw D) k τ = signed (al ++ be) (ga ++ de) (alT D k τ) ∧ parA (Ptw D) (k + 1) τ = signed (al ++ block D.R.t ++ de) (ga ++ be) (alS D k τ) := by
  first | exact @GlobalTheory.ArchRec.ParChain.parChain | exact GlobalTheory.ArchRec.ParChain.parChain | (intros; apply GlobalTheory.ArchRec.ParChain.parChain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModelsOfCoversRealPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCorrespondence_models_of_covers_realPlace : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (W : HSp D) (S' : D.what₂.Tau → SPar) (N : DSModel W S') (τ : D.what₂.Tau) (ι σ Z : Type) (A : Mn V.rank → (Z → ℂ) → (Z → ℂ)) (B : Mn W.rank → (Z → ℂ) → (Z → ℂ)) (pt : MvPolynomial ι ℂ → (Z → ℂ)) (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (p q r s : ℕ) (T₁ : GrpData p q) (T₂ : GrpData r s) (R₁ : DSRep T₁) (R₂ : DSRep T₂) (a₁ : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (a₂ : Mat r s →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ)) (l₁ : Ix p q → ℚ) (l₂ : Ix r s → ℚ) (c₁ c₂ : ℚ) (b₁ b₂ : Bool) (e₁ : Ix p q ≃ Fin V.rank) (e₂ : Ix r s ≃ Fin W.rank) (u₁ : kfin M τ → R₁.HK.V) (u₂ : kfin N τ → R₂.HK.V), KTie R₁ M τ l₁ c₁ b₁ true e₁ u₁ → KTie R₂ N τ l₂ c₂ b₂ false e₂ u₂ → Side A pt κ (phiFr (M.fr τ) b₁ e₁) c₁ a₁ → Side B pt κ (phiFr (N.fr τ) b₂ e₂) c₂ a₂ → (∀ Φ, IsJoint M τ A pt N B Φ ↔ CJoint a₁ a₂ (blattner l₁) (blattner l₂) (κ Φ)) → PairLaw a₁ a₂ R₁ R₂ (blattner l₁) (blattner l₂) → LiftLaw M τ A pt N B := by
  first | exact @GlobalTheory.ArchRec.Lift.liftLaw_of_pairLaw | exact GlobalTheory.ArchRec.Lift.liftLaw_of_pairLaw | (intros; apply GlobalTheory.ArchRec.Lift.liftLaw_of_pairLaw <;> assumption)
end

