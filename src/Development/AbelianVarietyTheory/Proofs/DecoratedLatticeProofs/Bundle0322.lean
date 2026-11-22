import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0311
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralForm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Formalism.LocalToGlobal.Divisibility.DefGroupLemmas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0312
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaCentreLinear
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.ZcComm

variable {D : D7} {S T : HSp D}

def IsCarried (ψ : AddChar (AF D.host.F) ℂ) (om : WRep S T) (L : (GA D T → ℂ) → (GA D T → ℂ)) : Prop :=
  ∃ Δ : (WO S T → ℂ) → (WO S T → ℂ), (∀ f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (Δ f)) ∧
    (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Δ (f + f') = Δ f + Δ f') ∧
    (∀ (c : ℂ) f, IsThetaFunO ψ S T f → Δ (c • f) = c • Δ f) ∧
    ∀ f, IsThetaFunO ψ S T f → ∀ g w, L (fun h => om (g, h) f w) = fun h => om (g, h) (Δ f) w

variable {ψ : AddChar (AF D.host.F) ℂ} (om : WRep S T)

theorem isCarried_id : IsCarried ψ om fun φ => φ :=
  ⟨fun f => f, fun _ hf => hf, fun _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem isCarried_zero : IsCarried ψ om fun _ => 0 := by
  refine ⟨fun _ => 0, fun _ _ => (GlobalTheory.RealWeil.thetaSub ψ S T).zero_mem, fun _ _ _ _ => by simp,
    fun c _ _ => by simp, fun f _ g w => ?_⟩
  funext h
  simp

theorem isCarried_comp {L₁ L₂ : (GA D T → ℂ) → (GA D T → ℂ)} (h₁ : IsCarried ψ om L₁)
    (h₂ : IsCarried ψ om L₂) : IsCarried ψ om fun φ => L₁ (L₂ φ) := by
  obtain ⟨Δ₁, t₁, a₁, s₁, e₁⟩ := h₁
  obtain ⟨Δ₂, t₂, a₂, s₂, e₂⟩ := h₂
  refine ⟨fun f => Δ₁ (Δ₂ f), fun f hf => t₁ _ (t₂ f hf), fun f f' hf hf' => ?_, fun c f hf => ?_,
    fun f hf g w => ?_⟩
  · beta_reduce
    rw [a₂ f f' hf hf', a₁ _ _ (t₂ f hf) (t₂ f' hf')]
  · beta_reduce
    rw [s₂ c f hf, s₁ c _ (t₂ f hf)]
  · beta_reduce
    rw [e₂ f hf g w, e₁ _ (t₂ f hf) g w]

theorem isCarried_add {L₁ L₂ : (GA D T → ℂ) → (GA D T → ℂ)} (h₁ : IsCarried ψ om L₁)
    (h₂ : IsCarried ψ om L₂) : IsCarried ψ om fun φ => L₁ φ + L₂ φ := by
  obtain ⟨Δ₁, t₁, a₁, s₁, e₁⟩ := h₁
  obtain ⟨Δ₂, t₂, a₂, s₂, e₂⟩ := h₂
  refine ⟨fun f => Δ₁ f + Δ₂ f, fun f hf => (GlobalTheory.RealWeil.thetaSub ψ S T).add_mem (t₁ f hf) (t₂ f hf),
    fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf g w => ?_⟩
  · beta_reduce
    rw [a₁ f f' hf hf', a₂ f f' hf hf']
    abel
  · beta_reduce
    rw [s₁ c f hf, s₂ c f hf, smul_add]
  · beta_reduce
    rw [e₁ f hf g w, e₂ f hf g w]
    funext h
    simp only [Pi.add_apply, map_add]

theorem isCarried_smul (c : ℂ) {L : (GA D T → ℂ) → (GA D T → ℂ)} (hL : IsCarried ψ om L) :
    IsCarried ψ om fun φ => c • L φ := by
  obtain ⟨Δ, t, a, s, e⟩ := hL
  refine ⟨fun f => c • Δ f, fun f hf => (GlobalTheory.RealWeil.thetaSub ψ S T).smul_mem c (t f hf),
    fun f f' hf hf' => ?_, fun c' f hf => ?_, fun f hf g w => ?_⟩
  · beta_reduce
    rw [a f f' hf hf', smul_add]
  · beta_reduce
    rw [s c' f hf, smul_comm c c']
  · beta_reduce
    rw [e f hf g w]
    funext h
    simp only [Pi.smul_apply, map_smul]

theorem isCarried_sum {ι : Type*} (s : Finset ι) (L : ι → (GA D T → ℂ) → (GA D T → ℂ))
    (hL : ∀ i ∈ s, IsCarried ψ om (L i)) : IsCarried ψ om fun φ => ∑ i ∈ s, L i φ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using isCarried_zero (ψ := ψ) om
  | insert a s ha ih =>
    have := isCarried_add om (hL a (Finset.mem_insert_self a s))
      (ih fun i hi => hL i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.sum_insert ha] using this

theorem isCarried_foldr {ι : Type*} (A : ι → (GA D T → ℂ) → (GA D T → ℂ)) (l : List ι)
    (hA : ∀ i ∈ l, IsCarried ψ om (A i)) : IsCarried ψ om fun φ => l.foldr (fun i g => A i g) φ := by
  induction l with
  | nil => simpa only [List.foldr_nil] using isCarried_id (ψ := ψ) om
  | cons i l ih =>
    have := isCarried_comp om (hA i (List.mem_cons.2 (Or.inl rfl)))
      (ih fun j hj => hA j (List.mem_cons.2 (Or.inr hj)))
    simpa only [List.foldr_cons] using this

theorem isCarried_gelf (θ : InfFam D) (τ : D.what₂.Tau)
    (hR : ∀ Z, IsCarried ψ om (Formalism.L2.Theta.RderC θ T τ Z)) (k : ℕ) :
    IsCarried ψ om (Formalism.L2.Theta.gelf θ T τ k) := by
  refine isCarried_sum om Finset.univ _ fun idx _ => ?_
  refine isCarried_foldr om (fun L => L) _ fun L hL => ?_
  obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hL
  exact hR _

theorem isCarried_centreAct (θ : InfFam D) (τ : D.what₂.Tau)
    (hR : ∀ Z, IsCarried ψ om (Formalism.L2.Theta.RderC θ T τ Z)) (z : MvPolynomial ℕ ℂ) :
    IsCarried ψ om (centreAct θ τ T z) := by
  refine isCarried_sum om z.support _ fun k _ => isCarried_smul om _ ?_
  exact isCarried_foldr om _ _ fun i _ => isCarried_gelf om θ τ hR i

end GlobalTheory.Core.Rk.ZcComm

open GlobalTheory.Core.Rk.ZcComm in

theorem GlobalTheory.Core.Rk.ZcComm.omCentreT_comm : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (τ : D.what₂.Tau) (z : MvPolynomial ℕ ℂ), (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → omCentreT om θ τ z (f + f') = omCentreT om θ τ z f + omCentreT om θ τ z f') ∧ (∀ (c : ℂ) f, IsThetaFunO ψ S T f → omCentreT om θ τ z (c • f) = c • omCentreT om θ τ z f) ∧ ∀ f, IsThetaFunO ψ S T f → ∀ g h, thetaKO om g h (omCentreT om θ τ z f) = centreAct θ τ T z (fun h' => thetaKO om g h' f) h := by
  intro D ψ θ S T χS χT om hθ hω τ z
  have hR : ∀ Z, IsCarried ψ om (Formalism.L2.Theta.RderC θ T τ Z) := fun Z =>
    GlobalTheory.Core.Rk.ZcDer.rderC_om D ψ θ S T χS χT om hθ hω τ Z
  obtain ⟨Δ, -, ha, hs, he⟩ := isCarried_centreAct om θ τ hR z
  have key : ∀ f, IsThetaFunO ψ S T f → omCentreT om θ τ z f = Δ f := by
    intro f hf
    funext w
    show centreAct θ τ T z (fun h => om (1, h) f w) 1 = Δ f w
    rw [he f hf 1 w]
    show om (1, 1) (Δ f) w = Δ f w
    rw [show ((1 : GA D S), (1 : GA D T)) = 1 from rfl, map_one]
    rfl
  refine ⟨fun f f' hf hf' => ?_, fun c f hf => ?_, fun f hf g h => ?_⟩
  · rw [key _ ((GlobalTheory.RealWeil.thetaSub ψ S T).add_mem hf hf'), key f hf, key f' hf', ha f f' hf hf']
  · rw [key _ ((GlobalTheory.RealWeil.thetaSub ψ S T).smul_mem c hf), key f hf, hs c f hf]
  · rw [key f hf]
    show om (g, h) (Δ f) 0 = centreAct θ τ T z (fun h' => om (g, h') f 0) h
    rw [he f hf g 0]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairsAmplitudeBoundOfTypeBoundStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairsAmplitudeBound_of_typeBound : GlobalTheory.Core.Deg.PairsDegOfType := by
  first | exact @GlobalTheory.Core.Deg.pairsDegOfType_holds | exact GlobalTheory.Core.Deg.pairsDegOfType_holds | (intros; apply GlobalTheory.Core.Deg.pairsDegOfType_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RamifiedLevelStabilizerIffAllData
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.KJInf Formalism.L2.Forms GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSaw

theorem ramIff_all : ∀ D : D7, RamIff D := by
  intro D k _ _ _ _ p n _ _ S β P g hg φ
  letI := Fintype.ofFinite 𝓀[k]ˣ
  have rp : ∀ x (F : GA D S → ℂ), β.rep x F = rTrans (β.gl x) F := fun _ _ => rfl
  rw [finsum_eq_sum_of_fintype]
  constructor
  · rintro ⟨Φ, ⟨he, hr, hc⟩, rfl⟩
    refine ⟨hc P, fun x hx => ?_, ?_⟩
    · rw [← rp, ← he x P, hx]
    · rw [← (mem_Mram Φ).1 hr P]
      exact Finset.sum_congr rfl fun s _ => by rw [← rp, ← he, hg]
  · rintro ⟨hc, hs, h0⟩
    let v : levelVec β.rep P := ⟨φ, fun x hx => hs x hx⟩
    have hv : ∀ x : GL n k, formOf β.rep P v (x • P) = β.rep x φ := formOf_smul β.rep P v
    refine ⟨formOf β.rep P v, ⟨formOf_mem _ _ _, (mem_Mram _).2 fun Q => ?_, fun Q => ?_⟩, by simpa using hv 1⟩
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      have : ∀ s : 𝓀[k]ˣ, formOf β.rep P v (s • h • P) = β.rep h (rTrans (β.gl (g s)) φ) := by
        intro s
        rw [← smul_comm h s P, ← hg, smul_smul, hv, map_mul, Module.End.mul_apply, rp (g s)]
      rw [Finset.sum_congr rfl fun s _ => this s, ← map_sum, h0, map_zero]
    · obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq (GL n k) P Q
      rw [hv, rp]
      exact ⟨fun γ hγ y => by simp only [rTrans]; rw [mul_assoc, hc.1 γ hγ], hc.2.comp (continuous_id.mul continuous_const)⟩

end GlobalTheory.SeeSaw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealIntertwinerValuesKFinite
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ItKFin

theorem inclT_mapFactor {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau)
    (g : Module.End ℂ (M.sm τ)) (A : M.H τ →ₗ[ℂ] M.H τ) (hg : ∀ w, ((g w : M.sm τ) : M.H τ) = A w) (y : SmT M) :
    inclT M (GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ g y) =
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ A) (inclT M y) := by
  rw [inclT, GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
    ← PiTensorProduct.map_comp]
  congr 2
  funext ρ
  by_cases e : ρ = τ
  · subst e
    ext w
    simp [hg]
  · ext w
    simp [e]

theorem itKFin : ∀ (D : D7) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ) (aS aT : D.what₂.Tau → ℚ) (ω : (GA D V × GA D W →* Module.End ℂ (WO V W → ℂ))) (f : WO V W → ℂ) (It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M), IsInfFam θ → IsWeilExp ψ V W aS aT ω → IsVacVec ψ θ M M' f → IsItW θ M M' ω (ptOf ψ θ M M' f) It → ∀ P v, It P v ∈ (Submodule.span ℂ {w : SmT M | ∃ v : (M).Vec, (∀ τ, (v τ : (M).H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) ∧ w = PiTensorProduct.tprod ℂ v}) := by
  intro D V W S S' M M' θ ψ aS aT ω f It hθ hW hf hIt P v
  obtain ⟨χS, χT, hWD, hexp⟩ := hW
  have hp : ptOf ψ θ M M' f = ⇑(pureTensorO ψ θ V W (cart M) (cart M') (onb M) (onb M') f) := rfl
  have hA : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∃ P' : PolF D W.rank V.rank, P'.totalDegree ≤ P.totalDegree ∧
      inclT M (It P' v) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M (It P v)) := by
    intro τ h hh
    obtain ⟨a, b, -, -, hc⟩ := GlobalTheory.CompactFockAction.compactFockAll D V W (Fr.ofModel M) (Fr.ofModel M') θ ψ χS χT ω f τ
      (aS τ) (aT τ) hθ hWD (hexp τ).1 (hexp τ).2 ⟨hf.theta, hf.vac⟩ hf.ne
    have h1 : (1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) ∈ Formalism.REAL.Kset (M'.ε τ) := ⟨one_mem _, by simp⟩
    have := hc h hh 1 h1 P
    have e1 : (Fr.ofModel M').elt θ τ 1 = 1 := by
      have hd' := (Matrix.isUnit_iff_isUnit_det _).1 (M'.fr_unit τ)
      show atTau θ W τ ((M'.fr τ)⁻¹ * 1 * M'.fr τ) = 1
      rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ hd']
      exact GlobalTheory.PointAtPlaceHom.atTau_one hθ W τ
    rw [e1, ptF_ofModel, hp, ← map_smul, ← hp] at this
    refine ⟨_, ?_, hIt.eqK τ _ (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt_subset M τ (GlobalTheory.Chain.IoLift.frame_mem M τ hh)) P _ this.symm v⟩
    exact (MvPolynomial.totalDegree_smul_le _ _).trans (GlobalTheory.Chain.RealIt.SubstDeg.totalDegree_subst_le _ _ _ _ _ _ _ _ _)
  have hJ := fun τ => (Formalism.REAL.maximal_compact_facts _ (M.ε τ)).1
  have hsm : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), ∀ w ∈ M.sm τ, (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) w ∈ M.sm τ :=
    fun τ h hh w hw => (GlobalTheory.MultGelf.mem_sm M τ).2 (GlobalTheory.SmVec.sigma_mem (M.fr_unit τ) (M.fr_gram τ) (M.ds τ).2.2.1
      ((GlobalTheory.MultGelf.mem_sm M τ).1 hw) (hJ τ h hh))
  let fK : ∀ τ, ∀ h ∈ Formalism.REAL.Kset (M.ε τ), Module.End ℂ (M.sm τ) := fun τ h hh =>
    (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ).restrict (hsm τ h hh)
  have hconj : ∀ τ (h : Matrix (Fin V.rank) (Fin V.rank) ℂ), M.fr τ * ((M.fr τ)⁻¹ * h * M.fr τ) * (M.fr τ)⁻¹ = h :=
    fun τ h => by
      have hd := (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
      rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd, Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  have hact : ∀ τ h (hh : h ∈ Formalism.REAL.Kset (M.ε τ)) (y : SmT M),
      inclT M (GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ h hh) y) = actT M τ ((M.fr τ)⁻¹ * h * M.fr τ) (inclT M y) := by
    intro τ h hh y
    rw [inclT_mapFactor M τ _ (M.σ τ h : M.H τ →ₗ[ℂ] M.H τ) (fun w => rfl)]
    simp only [actT, DSModel.rep, hconj]
  have hx := GlobalTheory.Chain.IoLift.mem_range_map_subtype_of_contr D.what₂.Tau (fun τ => M.sm τ)
    (fun τ => (GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ).comap (M.sm τ).subtype) (It P v) fun τ L hL => by
      show IsKFin (M.ε τ) (M.σ τ) ((L (It P v) : M.sm τ) : M.H τ)
      let E : Submodule ℂ (SmT M) := (MvPolynomial.restrictTotalDegree _ ℂ P.totalDegree).map (It.flip v)
      have hle : Submodule.span ℂ ((fun k => M.σ τ k ((L (It P v) : M.sm τ) : M.H τ)) '' Formalism.REAL.Kset (M.ε τ)) ≤
          (E.map L).map (M.sm τ).subtype := by
        rw [Submodule.span_le]
        rintro _ ⟨k, hk, rfl⟩
        obtain ⟨P', hP', e⟩ := hA τ k hk
        have e2 : It P' v = GlobalTheory.Chain.IoLift.intersection_update_fsHerm_neg_one τ (fK τ k hk) (It P v) :=
          (tensorLaw D V S M).inj (by rw [e, hact τ k hk])
        have e3 := LinearMap.congr_fun (hL (fK τ k hk)) (It P v)
        simp only [LinearMap.comp_apply] at e3
        refine ⟨L (It P' v), ⟨It P' v, ⟨P', (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hP', rfl⟩, rfl⟩, ?_⟩
        rw [e2, e3]
        rfl
      have hσ := (M.ds τ).2.2.1
      refine ⟨_, Submodule.finiteDimensional_of_le hle, Submodule.subset_span ⟨1, ⟨one_mem _, by simp⟩, ?_⟩,
        fun g hg w hw => ?_⟩
      · simp only [hσ.1.1]; rfl
      · refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (M.σ τ g : M.H τ →ₗ[ℂ] M.H τ) _)).2 ?_ hw)
        rintro _ ⟨k, hk', rfl⟩
        refine Submodule.subset_span ⟨g * k, Formalism.REAL.Kset_mul _ hg hk', ?_⟩
        simp only [hσ.1.2 g (hJ τ g hg) k (hJ τ k hk')]; rfl
  obtain ⟨z, hz⟩ := hx
  rw [← hz]
  clear hz
  induction z using PiTensorProduct.induction_on with
  | smul_tprod r n =>
    rw [map_smul, PiTensorProduct.map_tprod]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨fun τ => (n τ : M.sm τ), fun τ => Submodule.subset_span (n τ).2, rfl⟩)
  | add a b ha hb => rw [map_add]; exact add_mem ha hb

end GlobalTheory.ItKFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResidueSupportSinglePlaceToConjugatePairPosition
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.DIV Formalism.L2.SG.InstExistsPf GlobalTheory.FlagBasis
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjSlot

theorem resS_sigInt_eq_zero_iff (D : D7) (PP : Pl D.host.E) (s : Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F PP (sigInt (instOf D) s) = 0 ↔ resS D.host.F (conjPl PP) s = 0 :=
  resS_sigS_eq_zero_iff (instOf D).cm (isConjPl_conjPl PP).symm s

theorem mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (PP : Pl E) (a : 𝓞 E) :
    a ∈ (conjPl PP).asIdeal ↔ starO a ∈ PP.asIdeal := Iff.rfl

theorem natCast_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (PP : Pl E) (N : ℕ) :
    (N : 𝓞 E) ∈ (conjPl PP).asIdeal ↔ (N : 𝓞 E) ∈ PP.asIdeal := by
  show starOHom (N : 𝓞 E) ∈ PP.asIdeal ↔ _
  rw [map_natCast]

theorem isConjPl_conjPl_lev (D : D7) (PP : Pl D.host.E) : Formalism.IndefR.Lev.IsConjPl (D := D) PP (conjPl PP) :=
  fun c hc => ⟨starO c, by rw [mem_conjPl, starO_starO]; exact hc, rfl⟩

theorem intersection_update_fsHerm_neg_one : ∀ (D : D7) (Pg : Finset (Pl D.host.E)), (∀ PP ∈ Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → (∀ PP ∈ Pg, ∀ PP' ∈ Pg, ¬ Formalism.IndefR.Lev.IsConjPl (D := D) PP PP') → ∀ R : Formalism.L2.Herm.intAf D.host.F D.host.E → Prop, (∀ Q : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q.asIdeal → ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ Q' : Pl D.host.E, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ Q'.asIdeal → Q' ≠ Q → resS D.host.F Q' s = 0) ∧ R s) → ∀ PP ∈ Pg, (∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, (PP' ≠ PP → resS D.host.F PP' s = 0) ∧ resS D.host.F PP' (sigInt (instOf D) s) = 0) ∧ R s) ∧ ∃ s : Formalism.L2.Herm.intAf D.host.F D.host.E, (∀ PP' ∈ Pg, resS D.host.F PP' s = 0 ∧ (PP' ≠ PP → resS D.host.F PP' (sigInt (instOf D) s) = 0)) ∧ R s := by
  intro D Pg hg hconj R hR PP hPP
  have hne : ∀ P ∈ Pg, ∀ P' ∈ Pg, conjPl P ≠ P' := fun P hP P' hP' h =>
    hconj P hP P' hP' (h ▸ isConjPl_conjPl_lev D P)
  constructor
  · obtain ⟨s, hs, hRs⟩ := hR PP (hg PP hPP)
    refine ⟨s, fun P hP => ⟨fun h => hs P (hg P hP) h, ?_⟩, hRs⟩
    rw [resS_sigInt_eq_zero_iff]
    exact hs _ ((natCast_mem_conjPl P _).2 (hg P hP)) (hne P hP PP hPP)
  · obtain ⟨s, hs, hRs⟩ := hR (conjPl PP) ((natCast_mem_conjPl PP _).2 (hg PP hPP))
    refine ⟨s, fun P hP => ⟨hs P (hg P hP) (hne PP hPP P hP).symm, fun h => ?_⟩, hRs⟩
    rw [resS_sigInt_eq_zero_iff]
    refine hs _ ((natCast_mem_conjPl P _).2 (hg P hP)) fun e => h ?_
    rw [← conjPl_conjPl P, e, conjPl_conjPl]

end GlobalTheory.ConjSlot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeUnipotentHaarIntegralPointsEqOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance high] GlobalTheory.SplitWeil.matrixMeasurableSpace
open GlobalTheory.HaarR

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rootExchangeUnipotentHaar_integralPoints_eq_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ), 1 ≤ p → p ≤ c → ∀ (ν : Measure k), IsUnitVol ν → volN ν n c p {u : N k n c p | (u : GL (n ⊕ Fin c) k) ∈ KO k (n ⊕ Fin c)} = 1 := by
  first | exact @GlobalTheory.HaarR.volN_KO_eq_one | exact GlobalTheory.HaarR.volN_KO_eq_one | (intros; apply GlobalTheory.HaarR.volN_KO_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RowsOfPartHavePartParamsFirstChainMemberStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_of_part_have_part_params_first_chain_member : GlobalTheory.Published.CuspRapidDecay → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → (∀ h : RangeX R, RChain R h) → RangeX R → RowPar R := by
  first | exact @GlobalTheory.ChainTw.rowPar_of_chain | exact GlobalTheory.ChainTw.rowPar_of_chain | (intros; apply GlobalTheory.ChainTw.rowPar_of_chain <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerModelSmoothInGroup
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.SchCen

open GlobalTheory.IndefiniteRowSideFullHecke.RapidDecayLift (dOmS)
open Filter Topology

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))
  (θ : InfFam D)

def Adapted (L : (WO S T → ℂ) → ℂ) : Prop :=
  (∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → L (f + f') = L f + L f') ∧
  (∀ (c : ℂ) f, IsThetaFunO ψ S T f → L (c • f) = c * L f) ∧
  ∀ f, IsThetaFunO ψ S T f → ∀ τ, ∀ X ∈ lieAt S τ, ∀ g,
    HasDerivAt (fun t : ℝ => L (om (g * oneP θ S τ X t, 1) f)) (L (om (g, 1) (dOmS θ om τ X f))) 0

def Induced (R : (GA D S → ℂ) → (GA D S → ℂ)) : Prop :=
  ∀ f, IsThetaFunO ψ S T f → ∃ f', IsThetaFunO ψ S T f' ∧
    ∀ L, Adapted ψ om θ L → R (fun g => L (om (g, 1) f)) = fun g => L (om (g, 1) f')

variable {ψ om θ} {χS χT : (AE D)ˣ →* Circle}

theorem Induced.comp {R R' : (GA D S → ℂ) → (GA D S → ℂ)} (h : Induced ψ om θ R) (h' : Induced ψ om θ R') :
    Induced ψ om θ fun F => R (R' F) := fun f hf => by
  obtain ⟨f₁, h₁, e₁⟩ := h' f hf
  obtain ⟨f₂, h₂, e₂⟩ := h f₁ h₁
  exact ⟨f₂, h₂, fun L hL => by beta_reduce; rw [e₁ L hL, e₂ L hL]⟩

theorem Induced.smul (hω : IsWeilDatumO ψ S T χS χT om) (c : ℂ) {R : (GA D S → ℂ) → (GA D S → ℂ)}
    (h : Induced ψ om θ R) : Induced ψ om θ fun F => c • R F := fun f hf => by
  obtain ⟨f₁, h₁, e₁⟩ := h f hf
  refine ⟨c • f₁, GlobalTheory.OrientedHeis.theta_smul c h₁, fun L hL => ?_⟩
  beta_reduce
  rw [e₁ L hL]
  funext g
  rw [map_smul, hL.2.1 c _ (hω.om_pres _ _ h₁)]
  rfl

theorem Induced.add (hω : IsWeilDatumO ψ S T χS χT om) {R R' : (GA D S → ℂ) → (GA D S → ℂ)}
    (h : Induced ψ om θ R) (h' : Induced ψ om θ R') : Induced ψ om θ fun F => R F + R' F := fun f hf => by
  obtain ⟨f₁, h₁, e₁⟩ := h f hf
  obtain ⟨f₂, h₂, e₂⟩ := h' f hf
  refine ⟨f₁ + f₂, GlobalTheory.OrientedHeis.theta_add h₁ h₂, fun L hL => ?_⟩
  beta_reduce
  rw [e₁ L hL, e₂ L hL]
  funext g
  rw [map_add, hL.1 _ _ (hω.om_pres _ _ h₁) (hω.om_pres _ _ h₂)]
  rfl

section Mix

variable {S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ)

variable {μ : Measure (Mx D T.rank ρ)} {𝓕 : Set (Mx D T.rank ρ)}

end Mix

end GlobalTheory.Core.Rk.SchCen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatAdelicMatrixContinuousLeMajorantStatement
section
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhatAdelicMatrix_continuous_le_majorant : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n : ℕ) (φ : Mx D m n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → Continuous φ ∧ ∃ K : Set (Mx D m n), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ x, ‖φ x‖ ≤ C * GlobalTheory.Unf.maj θ K N x := by
  first | exact @GlobalTheory.SchwartzMaj.continuous_and_le_maj | exact GlobalTheory.SchwartzMaj.continuous_and_le_maj | (intros; apply GlobalTheory.SchwartzMaj.continuous_and_le_maj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFlatMapContractionSupportAtLevelPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSaw_flatMap_contraction_support_at_level_place : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → GlobalTheory.LocMod.GSupp2 D → ∀ (t : Tup c), t.Is → ∀ (Gi : GLoc v), Gi.Chars t → ∀ (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (F₁ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F₁ → ∀ (F₂ : WO (c.V (j + 1)) (c.V (j + 1 + 1)) → ℂ), Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· = Gi.q.v) F₂ → ∀ (x : GA D (c.V (j + 1 + 1))), SuppAt Gi.q.e (c.V (j + 1 + 1)) x → c.ctr j σ h (t.sBF j (σ + 1) h) (t.sFB j σ h) (comb c.ψ _ _ (Gi.eg j) F₁) (t.om (j + 1) (1, x) (comb c.ψ _ _ (Gi.eg (j + 1)) F₂)) ≠ 0 → ∃ r ∈ besGrp (c.bes (j + 1 + 1) σ (idx_step h)).d (c.bes (j + 1 + 1) σ (idx_step h)).o, SuppAt Gi.q.e (c.V (j + 1 + 1)) r ∧ ∃ u uk, (GlobalTheory.LocMod.ofSplit Gi.q).IsLoc (Gi.FY (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)) u uk ∧ uk ∈ ((Gi.S.T (Fin D.R.t)).lev (j + 1 + 1) (2 * σ + 1) (by have := Gi.hs; omega)).J ∧ x = r * u := by
  first | exact @GlobalTheory.SeeSaw.PlaceSupp.supp_ctr | exact GlobalTheory.SeeSaw.PlaceSupp.supp_ctr | (intros; apply GlobalTheory.SeeSaw.PlaceSupp.supp_ctr <;> assumption)
end

