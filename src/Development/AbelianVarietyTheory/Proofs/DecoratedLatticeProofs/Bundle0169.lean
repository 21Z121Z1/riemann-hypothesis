import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.HermitianETransportInvariant
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FockSignTransposeExchangesLocalGlActions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Chain.RealIt.SwapFock

open MvPolynomial

lemma sg_mul_self (e : Bool) : GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e = 1 := by
  cases e <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn]

lemma conj_sg (e : Bool) : starRingEnd ℂ (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) = GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e := by
  cases e <;> simp [GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn]

variable {a b : ℕ}

def swSign (ε : Fin a → Bool) (ε' : Fin b → Bool) (n : Fin b × Fin a) : ℂ :=
  GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' n.1) * GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε n.2)

variable (ε : Fin a → Bool) (ε' : Fin b → Bool)

lemma swSign_mul_self (n : Fin b × Fin a) : swSign ε ε' n * swSign ε ε' n = 1 := by
  unfold swSign
  rw [mul_mul_mul_comm, sg_mul_self, sg_mul_self, one_mul]

lemma conj_swSign (n : Fin b × Fin a) : starRingEnd ℂ (swSign ε ε' n) = swSign ε ε' n := by
  unfold swSign
  rw [map_mul, conj_sg, conj_sg]

lemma swSign_swap (n : Fin b × Fin a) : swSign ε' ε n.swap = swSign ε ε' n := by
  unfold swSign
  exact mul_comm _ _

lemma C_swSign_mul_self {σ : Type*} (n : Fin b × Fin a) :
    (C (swSign ε ε' n) : MvPolynomial σ ℂ) * C (swSign ε ε' n) = 1 := by
  rw [← map_mul, swSign_mul_self, map_one]

lemma C_sg_mul_self {σ : Type*} (e : Bool) :
    (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) : MvPolynomial σ ℂ) * C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn e) = 1 := by
  rw [← map_mul, sg_mul_self, map_one]

def swapHom : LPol b a →+* LPol a b :=
  eval₂Hom ((C : ℂ →+* LPol a b).comp (starRingEnd ℂ)) fun n => C (swSign ε ε' n) * X n.swap

@[simp] lemma swapHom_C (c : ℂ) : swapHom ε ε' (C c) = C (starRingEnd ℂ c) := by
  simp [swapHom]

@[simp] lemma swapHom_X (n : Fin b × Fin a) : swapHom ε ε' (X n) = C (swSign ε ε' n) * X n.swap := by
  simp [swapHom]

lemma swapHom_smul (c : ℂ) (P : LPol b a) : swapHom ε ε' (c • P) = starRingEnd ℂ c • swapHom ε ε' P := by
  rw [smul_eq_C_mul, map_mul, swapHom_C, smul_eq_C_mul]

lemma swapHom_comp : (swapHom ε' ε).comp (swapHom ε ε') = RingHom.id _ := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro n
    rw [RingHom.comp_apply, swapHom_X, map_mul, swapHom_C, swapHom_X, conj_swSign, swSign_swap,
      Prod.swap_swap, ← mul_assoc, C_swSign_mul_self, one_mul, RingHom.id_apply]

lemma swapHom_pderiv (n : Fin b × Fin a) (Q : LPol b a) :
    swapHom ε ε' (pderiv n Q) = C (swSign ε ε' n) * pderiv n.swap (swapHom ε ε' Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => rw [map_add, map_add, hp, hq, map_add, map_add, mul_add]
  | mul_X p m hp =>
    have hs := C_swSign_mul_self (σ := Fin a × Fin b) ε ε' n
    by_cases h : n = m
    · subst h
      simp only [pderiv_mul, pderiv_X_self, map_add, map_mul, hp, swapHom_X, pderiv_C, mul_one, zero_mul, zero_add]
      linear_combination (-(swapHom ε ε' p)) * hs
    · have h' : m.swap ≠ n.swap := fun e => h (Prod.swap_injective e).symm
      simp only [pderiv_mul, pderiv_X_of_ne (Ne.symm h), pderiv_X_of_ne h', map_mul, hp, swapHom_X,
        pderiv_C, mul_zero, zero_mul, add_zero, zero_add]
      ring

lemma swapHom_rai (i : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' (rai ε ε' i j Q) = rai ε' ε j i (swapHom ε ε' Q) := by
  unfold rai
  have hs := C_sg_mul_self (σ := Fin a × Fin b) (ε j)
  by_cases h : ε' i = ε j
  · rw [if_pos h, if_pos h.symm]
    simp only [LinearMap.smul_apply, LinearMap.mulLeft_apply, swapHom_smul, swapHom_C, map_mul, swapHom_X, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * X (j, i) * swapHom ε ε' Q) * hs
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [LinearMap.smul_apply, LinearMap.neg_apply, Derivation.coeFn_coe, map_neg, swapHom_smul, swapHom_C,
      swapHom_pderiv, map_mul, conj_sg, swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (-(C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * pderiv (j, i) (swapHom ε ε' Q))) * hs

lemma swapHom_low (i : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' (low ε ε' i j Q) = low ε' ε j i (swapHom ε ε' Q) := by
  unfold low
  have hs := C_sg_mul_self (σ := Fin a × Fin b) (ε j)
  by_cases h : ε' i = ε j
  · rw [if_pos h, if_pos h.symm]
    simp only [LinearMap.smul_apply, Derivation.coeFn_coe, swapHom_smul, swapHom_C, swapHom_pderiv, map_mul, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * pderiv (j, i) (swapHom ε ε' Q)) * hs
  · rw [if_neg h, if_neg (Ne.symm h)]
    simp only [LinearMap.smul_apply, LinearMap.mulLeft_apply, swapHom_smul, swapHom_C, map_mul, swapHom_X, conj_sg,
      swSign, smul_eq_C_mul, Prod.swap_prod_mk]
    linear_combination (C (GlobalTheory.IndefiniteRowSideFullHecke.RaisingLoweringOperators.sgn (ε' i)) * X (j, i) * swapHom ε ε' Q) * hs

lemma swapHom_half (c : Prop) [Decidable c] (Q : LPol b a) :
    swapHom ε ε' ((if c then (1 / 2 : ℂ) • (1 : Module.End ℂ (LPol b a)) else 0) Q) =
      (if c then (1 / 2 : ℂ) • (1 : Module.End ℂ (LPol a b)) else 0) (swapHom ε ε' Q) := by
  split_ifs
  · rw [LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply, Module.End.one_apply, swapHom_smul]
    rw [map_div₀, map_one, map_ofNat]
  · rw [LinearMap.zero_apply, LinearMap.zero_apply, map_zero]

lemma swapHom_termT (i l : Fin b) (j : Fin a) (Q : LPol b a) :
    swapHom ε ε' ((rai ε ε' i j * low ε ε' l j + if i = l then (1 / 2 : ℂ) • 1 else 0) Q) =
      (rai ε' ε j i * low ε' ε j l + if i = l then (1 / 2 : ℂ) • 1 else 0) (swapHom ε ε' Q) := by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add, Module.End.mul_apply, Module.End.mul_apply, swapHom_rai,
    swapHom_low, swapHom_half]

lemma swapHom_termS (i : Fin b) (j k : Fin a) (Q : LPol b a) :
    swapHom ε ε' ((rai ε ε' i j * low ε ε' i k + if j = k then (1 / 2 : ℂ) • 1 else 0) Q) =
      (rai ε' ε j i * low ε' ε k i + if j = k then (1 / 2 : ℂ) • 1 else 0) (swapHom ε ε' Q) := by
  rw [LinearMap.add_apply, LinearMap.add_apply, map_add, Module.End.mul_apply, Module.End.mul_apply, swapHom_rai,
    swapHom_low, swapHom_half]

def swapEquiv : LPol b a ≃+ LPol a b :=
  { toFun := swapHom ε ε'
    invFun := swapHom ε' ε
    left_inv := fun P => RingHom.congr_fun (swapHom_comp ε ε') P
    right_inv := fun P => RingHom.congr_fun (swapHom_comp ε' ε) P
    map_add' := map_add _ }

lemma swapEquiv_apply (P : LPol b a) : swapEquiv ε ε' P = swapHom ε ε' P := rfl

theorem locS_locT_exchange : ∀ (a b : ℕ) (ε : Fin a → Bool) (ε' : Fin b → Bool), ∃ j : LPol b a ≃+ LPol a b,
    (∀ (c : ℂ) P, j (c • P) = conj c • j P) ∧ ∀ P : LPol b a,
      (∀ Y : Matrix (Fin b) (Fin b) ℂ, j (locT ε ε' Y P) = locS ε' ε (Y.map (starRingEnd ℂ)) (j P)) ∧
        ∀ X : Matrix (Fin a) (Fin a) ℂ, j (locS ε ε' (X.map (starRingEnd ℂ)) P) = locT ε' ε X (j P) := by
  intro a b ε ε'
  refine ⟨swapEquiv ε ε', fun c P => ?_, fun P => ⟨fun Y => ?_, fun X => ?_⟩⟩
  · rw [swapEquiv_apply, swapEquiv_apply, swapHom_smul]
  · rw [swapEquiv_apply, swapEquiv_apply]
    unfold locT locS
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, swapHom_smul, swapHom_termT, Matrix.map_apply]
  · rw [swapEquiv_apply, swapEquiv_apply]
    unfold locT locS
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, swapHom_smul, swapHom_termS, Matrix.map_apply,
      starRingEnd_self_apply]

end GlobalTheory.Chain.RealIt.SwapFock

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierCoefficientBessel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Mi.PhCol

variable {D : D7}

theorem one_le_level (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos

theorem one_mem_level (X : HidaSetting D) : (1 : X.B.I.Gf) ∈ X.B.I.Kg X.B.g := by
  refine ⟨(Formalism.UG.stabGL X.B.I.Lf).one_mem, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
  have h1 : X.B.I.fmat 1 = 1 := rfl
  rw [h1, sub_self, Matrix.zero_mulVec, smul_zero]

theorem psiInfU_of_mem_Hinf (X : HidaSetting D) (u : D.what₂.Word) (η : X.B.I.Ginf) (hη : η ∈ Hinf X u) :
    X.psiInfU u η = 1 := by
  have e := Formalism.L2.SG.PoincareInHH.Cut.psiInf_mul_H X u 1 η hη
  rw [one_mul] at e
  rw [e]
  exact Formalism.L2.SG.CovariantRepresentation.psiInfU_one X u

theorem castGA_mem_rat {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA) :
    x ∈ I.GFset ↔ castGA e x ∈ I'.GFset := by
  subst e; rfl

theorem iotaX_mem_rat (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (g : GA D (D.sp.Y 0))
    (hg : g ∈ GQ (D.sp.Y 0)) : iotaX X h g ∈ X.B.I.GFset := by
  have e : iotaX X h g = castGA h.symm (Formalism.IndefR.RationalEmbedding.iota D g) := rfl
  rw [e]
  exact (castGA_mem_rat h.symm _).1 ((Formalism.IndefR.RationalEmbedding.iota_rat D g).1 hg)

theorem Ph_of_dec (X : HidaSetting D) (u : D.what₂.Word) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (y : X.B.I.GA)
    (n : X.B.I.Gf) (hh : Hfin X u) (k : X.B.I.Gf) (hd : IsDec X u y.2 n hh k) :
    Ph X u hK T y = phVal X u hK T y.1 n hh k := by
  have hex : ∃ n h k, IsDec X u y.2 n h k := ⟨n, hh, k, hd⟩
  unfold Ph
  rw [dif_pos hex]
  exact Formalism.L2.SG.Pf.phWellDef_holds X u T y.1 y.2 _ n _ k _ hh hex.choose_spec.choose_spec.choose_spec hd

variable {X : HidaSetting D} {h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D} {u : D.what₂.Word}
  {ψ : AddChar (AF D.host.F) ℂ} {A : HSp D}

theorem continuous_toH (B : SBes X h u ψ A) : Continuous B.toH := by
  have he : Continuous (embA B.d B.o) := by
    have e : (embA B.d B.o : GA D A → GA D (D.sp.Y 0)) = fun a => B.d.emb0 (B.o.emb (a, 1)) := rfl
    rw [e]
    exact B.d.continuous_embed.comp (B.o.continuous_emb.comp (continuous_id.prodMk continuous_const))
  have hc : Continuous fun a => iotaX X h (embA B.d B.o a) := (iotaX X h).continuous.comp he
  unfold SBes.toH
  exact (hc.fst.subtype_mk _).prodMk (hc.snd.subtype_mk _)

theorem continuous_col (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (ξ : X.Vpi u) :
    Continuous fun p : Hinf X u × Hfin X u => (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ p := by
  obtain ⟨hT1, hT2⟩ := T.2
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  rw [continuous_iff_continuousAt]
  intro p0
  have hπ : Continuous fun η : Hinf X u => X.piU u η ξ :=
    ((X.piU_rep u).2.2.2.2 ξ).comp_continuous continuous_subtype_val (fun η => hinf_le_sinf X u _ η.2)
  let L : X.Vpi u →ₗ[ℂ] ℂ :=
    (LinearMap.proj (R := ℂ) (φ := fun _ : Hinf X u × Hfin X u => ℂ) ((1 : Hinf X u), p0.2)).comp
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ))
  have hG : Continuous fun p : Hinf X u × Hfin X u => L (X.piU u p.1 ξ) :=
    L.continuous_of_finiteDimensional.comp (hπ.comp continuous_fst)
  have hUo : IsOpen {p : Hinf X u × Hfin X u |
      (X.xu u)⁻¹ * ((p0.2⁻¹ * p.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g} := by
    refine (X.B.I.topf_open X.B.g (one_le_level X)).preimage ?_
    exact (continuous_const.mul (continuous_subtype_val.comp (continuous_const.mul continuous_snd))).mul
      continuous_const
  have hp0 : p0 ∈ {p : Hinf X u × Hfin X u |
      (X.xu u)⁻¹ * ((p0.2⁻¹ * p.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g} := by
    show (X.xu u)⁻¹ * ((p0.2⁻¹ * p0.2 : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g
    rw [inv_mul_cancel]
    simpa using one_mem_level X
  refine hG.continuousAt.congr (Filter.eventually_of_mem (hUo.mem_nhds hp0) fun p hp => ?_)
  obtain ⟨η, k⟩ := p
  have hp' : (X.xu u)⁻¹ * ((p0.2⁻¹ * k : Hfin X u) : X.B.I.Gf) * X.xu u ∈ X.B.I.Kg X.B.g := hp
  obtain ⟨hK2, hχ⟩ := hL.1 _ hp'
  let κ : Ku X u hK := ⟨p0.2⁻¹ * k, hK2⟩
  have e1 : ((η, k) : Hinf X u × Hfin X u) = (η, p0.2) * (1, ((κ : Hfin X u))) := by
    ext
    · simp
    · simp [κ]
  have e2 : ((η, p0.2) : Hinf X u × Hfin X u) = (1, p0.2) * (η, 1) := by
    ext <;> simp
  have hψ : ((psiK X u hK κ : ℂˣ) : ℂ) = 1 := hχ
  show L (X.piU u η ξ) = (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (η, k)
  rw [e1, (hT1 ξ).2 (η, p0.2) κ, hψ, one_mul, e2, ← hT2 η ξ (1, p0.2)]
  rfl

end GlobalTheory.Core.Mi.PhCol

namespace GlobalTheory.Core.Mi.PhCol

theorem ph_colForm : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (T : Cu X u hK),
    (∀ ξ, IsContAut A (B.colForm T.1 ξ)) ∧ ∀ n ∈ flagN B.d, ∀ (a : GA D A) (y : X.B.I.Ginf),
      Ph X u hK T (iotaX X h (n * embA B.d B.o a) * (y, X.xu u)) =
        star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) * B.colForm T.1 (X.Wu u y) a := by
  intro D X h u ψ A B hK T
  obtain ⟨hT1, hT2⟩ := T.2
  refine ⟨fun ξ => ⟨fun γ hγ g => ?_, ?_⟩, fun n hn a y => ?_⟩
  ·
    have hrat : embA B.d B.o γ ∈ GQ (D.sp.Y 0) := by
      have e : embA B.d B.o γ = B.d.emb0 (B.o.emb (γ, 1)) := rfl
      rw [e]
      exact B.d.wittDecomp_anisotropicEmbedding_mem_rationalPoints (B.o.emb_mem_GQ hγ (one_mem _))
    have hr := iotaX_mem_rat X h _ hrat
    have hH := (B.tieH (embA B.d B.o γ)).1 ⟨γ, rfl⟩
    let γ' : Gam X u := ⟨iotaX X h (embA B.d B.o γ), Subgroup.mem_inf.2 ⟨hr, Subgroup.mem_prod.2 hH⟩⟩
    have e : B.toH (γ * g) = (iotaI X u γ', iotaF X u γ') * B.toH g := by
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext
      · show (iotaX X h (embA B.d B.o (γ * g))).1 = (iotaX X h (embA B.d B.o γ)).1 * (iotaX X h (embA B.d B.o g)).1
        rw [map_mul, map_mul, Prod.fst_mul]
      · show (iotaX X h (embA B.d B.o (γ * g))).2 = (iotaX X h (embA B.d B.o γ)).2 * (iotaX X h (embA B.d B.o g)).2
        rw [map_mul, map_mul, Prod.snd_mul]
    show (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (B.toH (γ * g)) =
      (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (B.toH g)
    rw [e]
    exact (hT1 ξ).1 γ' (B.toH g)
  ·
    exact (continuous_col hK T ξ).comp (continuous_toH B)
  ·
    obtain ⟨hn1, hn2⟩ := (B.tieN n).1 hn
    obtain ⟨ha1, ha2⟩ := (B.tieH (embA B.d B.o a)).1 ⟨a, rfl⟩
    set m := iotaX X h n with hm
    set b := iotaX X h (embA B.d B.o a) with hb
    have e : iotaX X h (n * embA B.d B.o a) * (y, X.xu u) = (m.1 * b.1 * y, m.2 * b.2 * X.xu u * 1) := by
      rw [map_mul, ← hm, ← hb]
      ext <;> simp [mul_assoc]
    have hd : IsDec X u (m.1 * b.1 * y, m.2 * b.2 * X.xu u * 1).2 m.2 ⟨b.2, ha2⟩ 1 :=
      ⟨hn2, one_mem_level_subgroup X, rfl⟩
    rw [e, Ph_of_dec X u hK T _ _ _ _ hd]
    unfold phVal
    have hm1S : m.1 ∈ X.SinfU u := fun v => (hn1 v).1
    have hb1S : b.1 ∈ X.SinfU u := hinf_le_sinf X u _ ha1
    have hW : X.Wu u (m.1 * b.1 * y) = X.psiInfU u m.1 • X.piU u b.1 (X.Wu u y) := by
      rw [mul_assoc, (X.Wu_spec u).1 m.1 hm1S, (X.piU_rep u).2.2.2.1 m.1 hn1, ContinuousLinearMap.one_apply,
        (X.Wu_spec u).1 b.1 hb1S]
      have hpsi : X.psiInfU u b.1 = 1 := psiInfU_of_mem_Hinf X u b.1 ha1
      change X.psiInfU u m.1 • (X.psiInfU u b.1 • X.piU u b.1 (X.Wu u y)) = _
      rw [hpsi, one_smul]
    have hC : (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.piU u b.1 (X.Wu u y)) (1, ⟨b.2, ha2⟩) =
        B.colForm T.1 (X.Wu u y) a := by
      have := hT2 ⟨b.1, ha1⟩ (X.Wu u y) (1, ⟨b.2, ha2⟩)
      refine this.trans ?_
      show (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y) ((1, ⟨b.2, ha2⟩) * (⟨b.1, ha1⟩, 1)) =
        (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y) (B.toH a)
      refine congrArg ((T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u y)) ?_
      refine Prod.ext ?_ ?_ <;> apply Subtype.ext
      · show (1 : X.B.I.Ginf) * b.1 = (iotaX X h (embA B.d B.o a)).1
        rw [one_mul]
      · show b.2 * (1 : X.B.I.Gf) = (iotaX X h (embA B.d B.o a)).2
        rw [mul_one]
    rw [hW, map_smul, Pi.smul_apply, smul_eq_mul, hC, chi2_apply_one X hK, B.tieψ n hn]
    ring

end GlobalTheory.Core.Mi.PhCol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDerivAtSobolevThetaFormHeisenbergAlongRealLin
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff Topology

noncomputable section

namespace GlobalTheory.MatCoeffDeriv

open GlobalTheory.FockCompare

theorem hasDerivAt_form_heisO_line : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ (S T : HSp D) (ℓ : (WO S T → ℂ) → ℂ), IsSobForm ψ θ S T ℓ → ∀ f, IsThetaFunO ψ S T f → ∀ M : ℝ →+ WO S T, Continuous M → (∀ s, (M s).map (finPart D) = 0) → ∀ w : WO S T, HasDerivAt (fun s : ℝ => ℓ (heisO ψ S T (w + M s) f)) (ℓ (heisO ψ S T w (fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0)) - deriv (fun s : ℝ => ψ (symplOH S T w (M s))) 0 * ℓ (heisO ψ S T w f)) 0 := by
  intro D ψ hψ θ hθ S T ℓ hℓ f hf M hM hMf w
  have hL : IsRealDir T S M := ⟨hM, hMf⟩
  have hg : IsThetaFunO ψ S T (heisO ψ S T w f) := GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf w
  set g := heisO ψ S T w f with hg_def
  set c : ℝ → ℂ := fun s => ψ (symplOH S T w (M s)) with hc_def

  have lsub : ∀ a b, IsThetaFunO ψ S T a → IsThetaFunO ψ S T b → ℓ (a - b) = ℓ a - ℓ b := by
    intro a b ha hb
    have := hℓ.add (a - b) b (GlobalTheory.OrientedHeis.theta_sub ha hb) hb
    rw [sub_add_cancel] at this
    rw [this]; ring

  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  have hce : c = fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) *
      (Complex.ofRealCLM (s * GlobalTheory.OrientedHeis.omO S T (piW θ T S w) (piW θ T S (M 1))))) := by
    funext s
    show ψ (symplOH S T w (M s)) = _
    rw [(smooth_iff_sm_and_real_lines D θ σ h T S).2.1 M hL s, GlobalTheory.OrientedHeis.psi_symplOH h hψ, map_smul]
    rfl
  have hcd : HasDerivAt c (deriv c 0) 0 := by
    refine DifferentiableAt.hasDerivAt ?_
    have h2 : ContDiff ℝ ∞ fun s : ℝ => Complex.exp (-(Real.pi * Complex.I) *
        (Complex.ofRealCLM (s * GlobalTheory.OrientedHeis.omO S T (piW θ T S w) (piW θ T S (M 1))))) :=
      Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
        (contDiff_id.mul contDiff_const)))
    rw [hce]
    exact h2.differentiable (by simp) 0
  have hc0 : c 0 = 1 := by
    show ψ (symplOH S T w (M 0)) = 1
    rw [M.map_zero, GlobalTheory.FinTranslate.symplOH_zero_right, ψ.map_zero_eq_one]
  have hcne : ∀ s, c s ≠ 0 := by
    intro s; rw [hce]; exact Complex.exp_ne_zero _

  have hF : ∀ s, heisO ψ S T (w + M s) f = c s • heisO ψ S T (M s) g := by
    intro s
    rw [hg_def, GlobalTheory.OrientedHeis.heisO_heisO, smul_smul, ← AddChar.map_add_eq_mul,
      GlobalTheory.FinTranslate.symplOH_skew (S := S) (T := T) w (M s), add_neg_cancel, ψ.map_zero_eq_one, one_smul, add_comm]

  obtain ⟨U, hUo, hUl⟩ := hg.level
  obtain ⟨d, C, hC⟩ := hℓ.bound U hUo
  have key := ((GlobalTheory.T.heisenbergTranslate_theta_continuous_differentiable_sobolev D ψ hψ θ hθ S T d g hg).2 M hM hMf).2
  have hmemM : ∀ t, heisO ψ S T (M t) g ∈ GlobalTheory.Size.thetaLevel ψ S T U := fun t =>
    ⟨GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hg (M t),
      fun u hu h0 => GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (hMf t) (hUl u hu h0)⟩
  have hmemg : g ∈ GlobalTheory.Size.thetaLevel ψ S T U := ⟨hg, hUl⟩
  have hmemd : GlobalTheory.OrientedHeis.dLine ψ S T M g ∈ GlobalTheory.Size.thetaLevel ψ S T U := by
    refine ⟨GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL hg, fun u hu h0 => ?_⟩
    funext p
    have : (fun t => heisO ψ S T (M t) g p) = fun t => heisO ψ S T u (heisO ψ S T (M t) g) p := by
      funext t; rw [GlobalTheory.OrientedHeis.heisO_comm_fin_real h0 (hMf t) (hUl u hu h0)]
    conv_rhs => unfold GlobalTheory.OrientedHeis.dLine; rw [this]
    unfold GlobalTheory.OrientedHeis.dLine
    rw [heisO, ← deriv_const_mul_field]
    rfl
  have hG : HasDerivAt (fun s : ℝ => ℓ (heisO ψ S T (M s) g)) (ℓ (GlobalTheory.OrientedHeis.dLine ψ S T M g)) 0 := by
    rw [hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff, tendsto_iff_edist_tendsto_0]
    have hφ : ∀ t : ℝ, (t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) - GlobalTheory.OrientedHeis.dLine ψ S T M g ∈
        GlobalTheory.Size.thetaLevel ψ S T U := fun t =>
      Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmemM t) hmemg)) hmemd
    have he : ∀ t : ℝ, edist (slope (fun s : ℝ => ℓ (heisO ψ S T (M s) g)) 0 t - ℓ (GlobalTheory.OrientedHeis.dLine ψ S T M g)) 0
        = ‖ℓ ((t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) - GlobalTheory.OrientedHeis.dLine ψ S T M g)‖ₑ := by
      intro t
      rw [edist_zero_right, lsub _ _ (Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmemM t) hmemg)).1 hmemd.1,
        hℓ.smul _ _ (Submodule.sub_mem _ (hmemM t) hmemg).1, lsub _ _ (hmemM t).1 hg, slope_def_module,
        sub_zero, M.map_zero, GlobalTheory.WeilVacMove.heisO_zero, Complex.real_smul, Complex.ofReal_inv]
    simp_rw [he]
    have hT : Filter.Tendsto (fun t : ℝ => (C : ℝ≥0∞) * supSob ψ θ d ((t⁻¹ : ℂ) • (heisO ψ S T (M t) g - g) -
        GlobalTheory.OrientedHeis.dLine ψ S T M g)) (nhdsWithin 0 {0}ᶜ) (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (a := (C : ℝ≥0∞)) key (Or.inr ENNReal.coe_ne_top)
      rwa [mul_zero] at this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hT (fun _ => bot_le)
      (fun t => hC _ (hφ t))

  set f' : WO S T → ℂ := fun p => deriv (fun s : ℝ => heisO ψ S T (M s) f p) 0 with hf'_def
  have hf'θ : IsThetaFunO ψ S T f' := GlobalTheory.OrientedHeis.theta_dLine hθ hψ hL hf
  have hdl : GlobalTheory.OrientedHeis.dLine ψ S T M g = heisO ψ S T w f' - (2 * deriv c 0) • g := by
    funext p
    set H : ℝ → ℂ := fun s => heisO ψ S T w (heisO ψ S T (M s) f) p with hH_def
    have hHd : HasDerivAt H (heisO ψ S T w f' p) 0 := by
      have hd := (GlobalTheory.OrientedHeis.hasDerivAt_heisO hθ hψ hL hf (p + w) 0).differentiableAt.hasDerivAt
      exact hd.const_mul (ψ (symplOH S T p w))
    have hH0 : H 0 = g p := by
      show heisO ψ S T w (heisO ψ S T (M 0) f) p = heisO ψ S T w f p
      rw [M.map_zero, GlobalTheory.WeilVacMove.heisO_zero]
    have hEq : (fun s : ℝ => heisO ψ S T (M s) g p) = fun s => (c s)⁻¹ * ((c s)⁻¹ * H s) := by
      funext s
      have e1 : H s = c s * heisO ψ S T (w + M s) f p := by
        show heisO ψ S T w (heisO ψ S T (M s) f) p = _
        rw [GlobalTheory.OrientedHeis.heisO_heisO]; rfl
      rw [e1, hF s, Pi.smul_apply, smul_eq_mul]
      field_simp [hcne s]
    have hci := hcd.inv (by rw [hc0]; exact one_ne_zero)
    have hD := hci.mul (hci.mul hHd)
    have hD' : HasDerivAt (fun s : ℝ => heisO ψ S T (M s) g p) _ 0 :=
      hD.congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => congrFun hEq s)
    show deriv (fun s : ℝ => heisO ψ S T (M s) g p) 0 = _
    rw [hD'.deriv]
    simp only [Pi.mul_apply, Pi.inv_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hc0, hH0]
    ring

  have hfun : (fun s : ℝ => ℓ (heisO ψ S T (w + M s) f)) = fun s => c s * ℓ (heisO ψ S T (M s) g) := by
    funext s
    rw [hF s, hℓ.smul _ _ (hmemM s).1]
  rw [hfun]
  have hP := hcd.mul hG
  refine hP.congr_deriv ?_
  rw [hdl, lsub _ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf'θ w) (GlobalTheory.OrientedHeis.theta_smul _ hg),
    hℓ.smul _ _ hg, hc0]
  simp only [M.map_zero, GlobalTheory.WeilVacMove.heisO_zero]
  ring

end GlobalTheory.MatCoeffDeriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasDiscreteSeriesKTypesCoverOfFactorsThroughCoveStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDiscreteSeriesKTypes_cover_of_factorsThroughCovering : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar → ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (P : SignedPar n) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e P.sgn → Factors R.U e σ → IsDSPar P σ → HasTypes R (blockPar P e) := by
  first | exact @GlobalTheory.CoverDS.hasTypes_of_factors | exact GlobalTheory.CoverDS.hasTypes_of_factors | (intros; apply GlobalTheory.CoverDS.hasTypes_of_factors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistParahoricChainLastStepsAgreeColumnsStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistParahoricChain_lastSteps_agree_columns : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → LastAgree Ch sel mu cst σ₀ P ι s W ν L := by
  first | exact @GlobalTheory.TwLast.lastAgree | exact GlobalTheory.TwLast.lastAgree | (intros; apply GlobalTheory.TwLast.lastAgree <;> assumption)
end

