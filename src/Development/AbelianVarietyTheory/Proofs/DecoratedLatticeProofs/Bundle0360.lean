import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0346
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0330
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0215
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsPlacesSingleton
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0163
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0686
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0918
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1317
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilTensorRuleScalarEqOne
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0348
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillWittDecomposition
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

namespace GlobalTheory.Core.Rk.RegKill

variable {D : D7}

theorem foldr_ops_zero {X : Type} (l : List ((X → ℂ) → (X → ℂ))) (hl : ∀ f ∈ l, f 0 = 0) :
    l.foldr (fun f acc => f acc) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons f l ih =>
    rw [List.foldr_cons, ih (fun g hg => hl g (List.mem_cons_of_mem _ hg))]
    exact hl f List.mem_cons_self

theorem opPow_zero {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (hA : ∀ i, A i 0 = 0) (k : ι →₀ ℕ) :
    opPow A k 0 = 0 := by
  unfold opPow
  induction (Multiset.toList (Finsupp.toMultiset k)) with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, ih, hA]

theorem centreAct_zero (θ : InfFam D) (τ : D.what₂.Tau) (T : HSp D) (p : MvPolynomial ℕ ℂ) :
    centreAct θ τ T p (0 : GA D T → ℂ) = 0 := by
  have hR : ∀ Z, RderC θ T τ Z (0 : GA D T → ℂ) = 0 := by
    intro Z
    funext g
    simp [RderC, Rder]
  have hg : ∀ k, gelf θ T τ k (0 : GA D T → ℂ) = 0 := by
    intro k
    funext g
    simp only [gelf]
    rw [Finset.sum_apply]
    refine Finset.sum_eq_zero fun idx _ => ?_
    rw [foldr_ops_zero]
    · rfl
    · intro f hf
      obtain ⟨a, rfl⟩ := List.mem_ofFn.1 hf
      exact hR _
  unfold centreAct polyAct
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [opPow_zero _ hg, smul_zero]

theorem laurent_zero (s₀ : ℂ) (n : ℤ) : laurent (fun _ : ℂ => (0 : ℂ)) s₀ n = 0 :=
  CoeffAt.laurent_eq ⟨_, isExtAt_const 0 s₀, laurentConst_of_tendsto (by simpa using tendsto_const_nhds)⟩

section
variable {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ))

theorem thetaKO_one_om (g : GA D S) (h : GA D T) (f : WO S T → ℂ) :
    thetaKO om 1 h (om (g, 1) f) = thetaKO om g h f := by
  unfold thetaKO
  have e : (((1 : GA D S), h) : GA D S × GA D T) * (g, 1) = (g, h) := by ext <;> simp
  rw [← Module.End.mul_apply, ← map_mul, e]

theorem thetaKO_rat {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} (hω : IsWeilDatumO ψ S T χS χT om)
    {γ : GA D S} (hγ : γ ∈ GQ S) (g : GA D S) (h : GA D T) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    thetaKO om (γ * g) h f = thetaKO om g h f := by
  unfold thetaKO
  have e : ((γ * g, h) : GA D S × GA D T) = (γ, 1) * (g, h) := by ext <;> simp
  rw [e, map_mul, Module.End.mul_apply]
  exact hω.om_aut γ hγ 1 (one_mem _) _ (hω.om_pres _ _ hf)

end

theorem dblInt_regRes_eq_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W W₀ : HSp D) (r' : ℕ) (d₀ : HypDec W W₀ r') (b' : GL (Fin W.rank) (AE D)) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ (m : Measure (GA D A)) (mW : Measure (GA D W)), m.IsHaarMeasure → mW.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → Kills ψ χ omh m u → EisensteinContinues d₀ b' → ∀ (τ : D.what₂.Tau) (zH : MvPolynomial ℕ ℂ) (P : Polynomial ℂ), P ≠ 0 → (∀ φ', IsThetaFunO ψ (dblSp A) W φ' → RegIntProps ψ omh mW θ τ d₀ b' zH P φ') → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → GlobalTheory.Eis.dblInt A χ⁻¹ m (regRes omh mW θ τ d₀ b' zH P φ) (fun g => conj (u g)) (fun g => conj (u g)) = 0 := by
  intro D ψ θ A cA a hDef W W₀ r' d₀ b' χ omh hW m mW hm hmW u hu hinv hK hAux τ zH P hP hReg φ hφ hfin
  obtain ⟨φ', hφ', hcol⟩ := GlobalTheory.T.theta_kernel_exists_for_continuous D ψ θ A cA a hDef W χ omh hW φ hφ hfin m hm u hu hinv
  have hZ := GlobalTheory.T.omega_centre_linear D ψ θ (dblSp A) W 1 χ omh hDef.inf hW τ zH
  have hzero : ∀ h, thetaKO omh 1 h φ' = 0 := by
    intro h
    have e := hcol (fun f => thetaKO omh 1 h f)
      (fun f f' _ _ => by simp [thetaKO, map_add])
      (fun c f _ => by simp [thetaKO, map_smul])
      (fun γ hγ g => by
        simp only [thetaKO_one_om]
        exact thetaKO_rat omh hW hγ g h hφ)
    rw [← e]
    simp only [thetaKO_one_om]
    exact hK φ hφ h
  have hshift : ∀ f, IsThetaFunO ψ (dblSp A) W f → ∀ g,
      regRes omh mW θ τ d₀ b' zH P (omh (g, 1) f) 1 = regRes omh mW θ τ d₀ b' zH P f g := by
    intro f hf g
    have hf1 := hW.om_pres (g, 1) f hf
    unfold regRes
    congr 1
    funext s
    unfold regInt thetaPair
    congr 2
    funext q
    unfold AutomorphicL2Unitary.descend
    beta_reduce
    congr 1
    rw [hZ.2.2 _ hf1, hZ.2.2 _ hf]
    simp only [thetaKO_one_om]
  have hrat : ∀ f, IsThetaFunO ψ (dblSp A) W f → ∀ γ ∈ GQ (dblSp A), ∀ g,
      regRes omh mW θ τ d₀ b' zH P f (γ * g) = regRes omh mW θ τ d₀ b' zH P f g := by
    intro f hf γ hγ g
    have hF := (hReg f hf).1
    unfold regRes
    congr 1
    funext s
    unfold regInt thetaPair
    congr 2
    funext q
    unfold AutomorphicL2Unitary.descend
    beta_reduce
    rw [thetaKO_rat omh hW hγ g _ hF]
  have hlin := GlobalTheory.T.regularised_integral_linear_properties D ψ θ (dblSp A) W W₀ r' d₀ b' 1 χ omh hDef.inf hW mW hAux τ zH P hReg
  have e := hcol (fun f => regRes omh mW θ τ d₀ b' zH P f 1)
    (fun f f' hf hf' => hlin.1 f f' hf hf' 1)
    (fun c f hf => hlin.2 c f hf 1)
    (fun γ hγ g => by
      rw [hshift _ hφ, hshift _ hφ, hrat _ hφ γ hγ])
  have hfun : (fun g => regRes omh mW θ τ d₀ b' zH P (omh (g, 1) φ) 1) = regRes omh mW θ τ d₀ b' zH P φ :=
    funext (hshift φ hφ)
  rw [hfun] at e
  rw [e]
  have hI : regInt omh mW θ τ d₀ b' zH P φ' 1 = fun _ => 0 := by
    funext s
    unfold regInt thetaPair
    have hint : (fun h => thetaKO omh 1 h (omCentreT omh θ τ zH φ') * sphericalEisenstein d₀ b' h s) = fun _ => (0 : ℂ) := by
      funext h
      rw [hZ.2.2 _ hφ']
      have h0 : (fun h' => thetaKO omh 1 h' φ') = (0 : GA D W → ℂ) := funext hzero
      rw [h0, centreAct_zero]
      simp
    rw [hint]
    simp [AutomorphicL2Unitary.descend]
  show laurent (regInt omh mW θ τ d₀ b' zH P φ' 1) (rhoH W r') (-1) = 0
  rw [hI]
  exact laurent_zero _ _

end GlobalTheory.Core.Rk.RegKill

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftChainStepExactInnerProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

namespace GlobalTheory.ChainTw.ExactNS

variable {D : D7}

theorem petersson_conj (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) (X : Set (GA D V))
    (hX : IsFundamentalDomain (GQ V) X ν)
    (f g : GA D V → ℂ) (hf : ∀ γ ∈ GQ V, ∀ h, f (γ * h) = f h) (hg : ∀ γ ∈ GQ V, ∀ h, g (γ * h) = g h) :
    GlobalTheory.Cusp.petersson V ν (fun h => conj (f h)) (fun h => conj (g h)) = conj (Lift.pet ν X f g) := by
  haveI := hν
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) (fun h => conj (f h) * conj (conj (g h))) := fun γ hγ h => by
    simp only [hf γ hγ, hg γ hγ]
  change ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ V) (fun h => conj (f h) * conj (conj (g h))) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _
  rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]
  unfold Lift.pet
  rw [← integral_conj]
  simp only [map_mul]

theorem up_conj {c : Com D} {s s' : PiLocalization₂ D} {w : Twist D} {k : ℕ} (p : Step c s s') (hp : IsStep w (k + 1) p)
    (hν : s.ν.IsHaarMeasure) (hX : IsFundamentalDomain (GQ s.V) s.fd s.ν) (φ : PolF D s'.V.rank s.V.rank)
    (F : GA D s.V → ℂ) (hF : ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g) :
    GlobalTheory.Core.Rk.IP.up p.ω s.ν (p.pt φ) (fun x => conj (F x)) = fun h => conj (p.up φ F h) := by
  haveI := hν
  funext h
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := hp.theta φ
  have hθl : ∀ γ ∈ GQ s.V, ∀ g, thetaKO p.ω (γ * g) h (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro γ hγ g
    have e : ((γ * g, h) : GA D s.V × GA D s'.V) = (γ, 1) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut γ hγ 1 (one_mem _) _ (hp.weil.om_pres _ _ hΦ)
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ s.V) (fun g => thetaKO p.ω g h (p.pt φ) * conj (F g)) := fun γ hγ x => by
    simp only [hθl γ hγ, hF γ hγ]
  simp only [GlobalTheory.Core.Rk.IP.up, Step.up]
  change ∫ q, GlobalTheory.AutomorphicL2Unitary.descend (GQ s.V) _ q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ s.V) s.ν = _
  rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure hX]
  simp only [hL.descend_mk]
  rw [← integral_conj]
  simp only [map_mul, Complex.conj_conj]

theorem up_leftInv {c : Com D} {s s' : PiLocalization₂ D} {w : Twist D} {k : ℕ} (p : Step c s s') (hp : IsStep w (k + 1) p)
    (φ : PolF D s'.V.rank s.V.rank) (F : GA D s.V → ℂ) : ∀ γ ∈ GQ s'.V, ∀ h, p.up φ F (γ * h) = p.up φ F h := by
  have hΦ : IsThetaFunO c.ψ s.V s'.V (p.pt φ) := hp.theta φ
  have hθr : ∀ g, ∀ γ ∈ GQ s'.V, ∀ h, thetaKO p.ω g (γ * h) (p.pt φ) = thetaKO p.ω g h (p.pt φ) := by
    intro g γ hγ h
    have e : ((g, γ * h) : GA D s.V × GA D s'.V) = (1, γ) * (g, h) := by simp
    simp only [thetaKO, e, map_mul, Module.End.mul_apply]
    exact hp.weil.om_aut 1 (one_mem _) γ hγ _ (hp.weil.om_pres _ _ hΦ)
  intro γ hγ h
  simp only [Step.up, hθr _ γ hγ]

theorem stepExactNS : ∀ D : D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D → SoftQ D → QPeel D → LevInt D → StepExactNS D := by
  intro D hHF hSoft hPeel hLev hgap c w hw k hk s s' hs hs' p hp ipD ip hMet m X hmX mR hmR φ v hRC u₁ u₂ B hB hQ hNS l hl
  have hc : c.Is := hw.com
  obtain ⟨hr, -, hsF⟩ := id hs
  obtain ⟨hr', -, hs'F⟩ := id hs'
  have hv : PiTensorProduct.tprod ℂ v ∈ s.KF := Submodule.subset_span ⟨v, hRC.1, rfl⟩
  by_cases h0 : PiTensorProduct.tprod ℂ v = 0
  · have hz : ∀ g, zReal p m X φ v g = 0 := by
      intro g
      have hp0 := hMet.pure v v
      simp only [h0, map_zero, LinearMap.zero_apply] at hp0
      obtain ⟨τ, -, hτ⟩ := Finset.prod_eq_zero_iff.1 hp0.symm
      have h0τ : ((v τ : s.M.sm τ) : s.M.H τ) = 0 := inner_self_eq_zero.1 hτ
      simp only [zReal]
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by rw [h0τ, inner_zero_left])]
      simp
    simp [h0, hz, Step.up, Lift.pet]
  have hF₁ : PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v) ≠ 0 := fun h =>
    hB.1 ((hSoft c w hw k hk.le s hs).2.2.1 u₁ _ h0 h)
  have hparF : ParFun c s (PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v)) B := hB.2 _ hF₁
  have hFlat := GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level D c w hw k hk.le s hs hr
  obtain ⟨cA, a, hcA, hcart, hJ, hmaj, hmaj_eq, hA0⟩ := GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc k hk.le _ hsF
  obtain ⟨-, -, -, hcartB, -, -, -, -⟩ := GlobalTheory.ChainOnto.conj_stage_val_mem_A0_and_cartan_frame D c hc (k + 1) hk _ hs'F
  obtain ⟨hwitt, htwo⟩ := GlobalTheory.ChainOnto.WittTwo.wittIndex_lt_and_two_split D c (k + 1) _ hk hs'F
  obtain ⟨hfock, -, hunrT⟩ := GlobalTheory.T.twistedChainStep_fockVectors_spherical_offS D hgap c w hw k hk s s' hs hs' p hp
  set F₁ := PiLocalization₂.val u₁ (PiTensorProduct.tprod ℂ v) with hF₁def
  set F₂ := PiLocalization₂.val u₂ (PiTensorProduct.tprod ℂ v) with hF₂def
  have hu1 : (fun g => conj (F₁ g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 ⟨u₁.1, hFlat u₁.2⟩ _ hv
  have hu2 : (fun g => conj (F₂ g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := hA0 ⟨u₂.1, hFlat u₂.2⟩ _ hv
  have hrk0 : s.V.rank = D.R.rankY k := hsF.rank
  have hrk1 : s'.V.rank = D.R.rankY (k + 1) := hs'F.rank
  have hr1 : 1 ≤ s.V.rank := by
    rw [hrk0]; simp only [Ranks.rankY, Ranks.r]; have := D.R.two_le_m; omega
  have ht2 : 2 ≤ D.R.t := by have := D.R.rank_add_five_le; omega
  have hrk : s'.V.rank = s.V.rank + D.R.t := by rw [hrk1, hrk0]; simp only [Ranks.rankY]; ring
  have hPair : GlobalTheory.Core.Rk.IP.Pair c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
      m X :=
    { setting := ⟨hr1, by omega, hrk, hc.inf, hsF.sigOK, hcA, hcart, hcartB, hJ⟩
      maj := hmaj
      maj_eq := hmaj_eq
      weil := hp.weil
      covol := hmX }
  have hUnr : GlobalTheory.Core.Rk.IP.Unram c.ψ s.V s'.V (c.chT (k + 1)) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) :=
    ⟨hsF.selfDual, hs'F.selfDual, fun w _ h2 => htwo w h2, hunrT, (hfock φ).2.1, (hfock φ).2.1⟩
  have hsph : GlobalTheory.Core.Rk.IP.SphFun s.V s.Λ c.S (fun g => conj (F₂ g)) := by
    obtain ⟨-, hoffS, -⟩ := GlobalTheory.ChainOnto.LevelFacts.levFacts D c hc k hk.le _ hsF
    have hT := (GlobalTheory.MultMem.mem_mult_iff ..).1 ((mem_multT ..).1 (hFlat u₂.2))
    intro v' hv' κ hκ g
    obtain ⟨hκL, hκχ⟩ := hoffS v' hv' κ hκ
    have e : F₂ = PiTensorProduct.lift.symm (u₂ : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) v := by
      rw [PiTensorProduct.lift_symm]; rfl
    simp only [e]
    have hlev := hT.lev v _ hκL g
    rw [hκχ, one_mul] at hlev
    exact congrArg (starRingEnd ℂ) hlev
  have hIM : IsMajOf c s a := ⟨hmaj, hmaj_eq⟩
  obtain ⟨s₁, hs₁, hLI⟩ := hLev hgap c w hw k hk s s' hs hs' p hp ipD ip hMet m X hmX mR hmR φ v hRC a hIM
  obtain ⟨hLint, hLeq⟩ := hLI u₁ u₂
  have hint : ∃ z : ℝ, z < (D.R.t : ℝ) / 2 ∧ IntegrableOn (GlobalTheory.Core.Rk.IP.integrand p.ω s.ν m X s.Λ a (p.pt φ)
      (p.pt φ) (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) z) (GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S) s.ν := by
    refine ⟨max s₁ ((D.R.t : ℝ) / 2 - 1 / 2), max_lt hs₁ (by linarith), ?_⟩
    exact (hPeel hgap c w hw k hk s s' hs hs' p hp m X hmX a hIM u₁ u₂ φ hQ _ hv _ hv _
      (lt_of_lt_of_le (by linarith) (le_max_right _ _)) (hLint _ (le_max_left _ _))).1
  have hPt := hPeel hgap c w hw k hk s s' hs hs' p hp m X hmX a hIM u₁ u₂ φ hQ _ hv _ hv ((D.R.t : ℝ) / 2)
    (by linarith) (hLint _ hs₁.le)
  obtain ⟨-, -, -, hval⟩ := hHF c.ψ c.θ s.V s'.V (c.chS (k + 1)) (c.chT (k + 1)) (cart s.M) (cart s'.M) D.R.t cA a p.ω
    m X hPair ht2 (Or.inr hwitt) s.Λ s'.Λ c.S (p.pt φ) (p.pt φ) (hfock φ).1 (hfock φ).1 hUnr s.ν s'.ν hsF.haar hs'F.haar
    _ hu1 _ hu2 B hparF hsph hNS hint
  have key := hval l hl
  have hsZ : GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero s.V s'.V = (((D.R.t : ℝ) / 2 : ℝ) : ℂ) := by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero.sZero, hrk]; push_cast; ring
  have hI : ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) g *
      GlobalTheory.Core.Rk.IP.rcoef s.ν (fun x => conj (F₁ x)) (fun x => conj (F₂ x)) g ∂s.ν =
      locQ c w k * ((∫ g, zReal p m X φ v g ∂mR) * conj (ip u₁ u₂)) := by
    rw [← hLeq, ← hPt.2 rfl]
    change _ = ∫ g in GlobalTheory.Core.Rk.IP.openOff s.V s.Λ c.S, flatInt p m X a φ F₁ F₂ (((D.R.t : ℝ) / 2 : ℝ) : ℂ) g ∂s.ν
    congr 1
    funext g
    simp only [flatInt]
    rw [← hsZ]
    exact (GlobalTheory.Core.Rk.IP.integrand_sZero (A := s.V) (B := s'.V) p.ω s.ν m X s.Λ a (p.pt φ) (p.pt φ) _ _ g).symm
  have hFl : ∀ F : GA D s.V → ℂ, (fun g => conj (F g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA →
      ∀ γ ∈ GQ s.V, ∀ g, F (γ * g) = F g := fun F hF γ hγ g => by
    simpa using congrArg (starRingEnd ℂ) (hF.1.1.left γ hγ g)
  rw [ExactNS.up_conj p hp hsF.haar hsF.fund φ F₁ (hFl F₁ hu1), ExactNS.up_conj p hp hsF.haar hsF.fund φ F₂ (hFl F₂ hu2),
    ExactNS.petersson_conj s'.V s'.ν hs'F.haar s'.fd hs'F.fund _ _ (ExactNS.up_leftInv p hp φ F₁)
      (ExactNS.up_leftInv p hp φ F₂), hI] at key
  have key' := congrArg (starRingEnd ℂ) key
  rw [Complex.conj_conj] at key'
  change Lift.pet s'.ν s'.fd _ _ = _
  rw [key']
  simp only [dS, map_mul, Complex.conj_conj]
  ring

end GlobalTheory.ChainTw.ExactNS

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairDefinitePlaceCharacterData
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift GlobalTheory.Core.Rk.Exh

namespace GlobalTheory.DownPair

theorem pair_data : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T), (∃ cA a, Defin R.θ (Vc D i) cA a) ∧ Places (Vc D i) (R.βV i) (R.Pg ∪ R.Q t) ∧ under (R.Pg ∪ R.Q t) = GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.badPl R t ∧ GlobalTheory.LFun.UnrOff (F := D.host.F) (E := D.host.E) (chiV R i t) (↑(under (D := D) (R.Pg ∪ R.Q t))) ∧ (∃ η, GlobalTheory.WeilParts.IsEtaTilde D η) ∧ (Wc D i).SigOK ∧ (Wc D i).rank = D.R.r ∧ 0 < D.R.r ∧ (Vc D i).rank = D.R.r + D.R.t ∧ D.R.r + 5 ≤ D.R.t ∧ R.ΛV i = GlobalTheory.AdelicU.frameLat (Vc D i) ∧ R.ΛW i = GlobalTheory.AdelicU.frameLat (Wc D i) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hF i t
  have hc := hG.core
  have hV := hc.lev.βV i
  have hW := hc.lev.βW i
  have hΛ : ∀ {V : Formalism.BasicNotions.HSpace D.host.E} {β Λ}, Formalism.IndefR.Links.IsSDFrame (D := D) V β Λ 1 → Λ = GlobalTheory.AdelicU.frameLat V := by
    intro V β Λ h
    obtain ⟨c, hf, -, -, h1, h2⟩ := h
    ext x
    rw [GlobalTheory.AdelicU.mem_frameLat]
    constructor
    · intro hx; have := h2 x hx; simp only [one_pow, Nat.cast_one, one_smul] at this; exact this
    · intro hx; simpa using h1 x hx
  have hΛV := hΛ hV
  have hΛW := hΛ hW
  have hEta : ∃ η, GlobalTheory.WeilParts.IsEtaTilde D η := by
    have hω := hc.thP.ωP i t
    refine ⟨R.eta, GlobalTheory.EtaTildeOddParity.isEtaTilde_of_odd D R.eta R.C.eta hc.lev.eta R.C.isEta _ (Vc D i).rank (Wc D i).rank hω.resS hω.resT ?_⟩
    · rw [D.sp.V_rank _ (by omega) (by omega), D.sp.W_rank _ (by omega) (by omega)]
      unfold Formalism.BasicNotions.Ranks.nV
      have := D.R.t_odd
      obtain ⟨k, hk⟩ := this
      exact ⟨D.R.r + k, by omega⟩
  have hUnr : GlobalTheory.LFun.UnrOff (F := D.host.F) (E := D.host.E) (chiV R i t) (↑(under (D := D) (R.Pg ∪ R.Q t))) := by
    intro w hw
    have hgood : GlobalTheory.Hk3.Good R t w := by
      intro PP hPP
      constructor
      · rintro rfl
        exact hw (Finset.mem_coe.2 (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, rfl⟩))
      · intro hcj
        exact hw (Finset.mem_coe.2 (Finset.mem_image.2 ⟨PP, Finset.mem_union.2 hPP, GlobalTheory.RawLift.Small.under_eq_of_conj hcj⟩))
    have hg := ((GlobalTheory.GoodPrimes.good_primes R F hc.lev).2.1 t w hgood).1
    have hnotover : ∀ k, ¬ Formalism.L2.Host.OverP D.host (D.host.g k) w := by
      intro k hk
      apply hg
      push_cast
      fin_cases k
      · exact Ideal.mul_mem_right _ _ hk
      · exact Ideal.mul_mem_left _ _ hk
    have hmu : (R.C.mu0 i).UnrAt w := (R.C.isMu0 i).unr w hnotover
    have hxi : (R.xiH t).UnrAt w := by
      by_contra h
      rcases (hc.lev.Q_ram t w).1 h with h1 | ⟨PP', h1, h2⟩
      · exact (hgood w (Or.inr h1)).1 rfl
      · exact (hgood PP' (Or.inr h1)).2 h2
    have heta : R.C.eta.UnrAt w := R.C.isEta.unr w
    have a1 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hc.lev.mu0 i) w).2 hmu
    have a2 := (GlobalTheory.LFun.unrAt_iff_of_chrEq (hc.lev.xi t) w).2 hxi
    have a3 := (GlobalTheory.LFun.unrAt_iff_of_chrEq hc.lev.eta w).2 heta
    exact (a1.mul a2).mul a3.inv
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  refine ⟨GlobalTheory.Core.Rk.Exh.Model.exists_defin hc.models.inf (D.sp.V_sig _) (hc.models.vpos i), ⟨?_, ?_, fun v h2 => GlobalTheory.Core.Rk.IP.Model.isSplit_two v h2⟩, rfl, hUnr, hEta, D.sp.W_sig _, D.sp.W_rank _ (by omega) (by omega), hr, ?_, D.R.rank_add_five_le, hΛV, hΛW⟩
  · obtain ⟨c, hf, -⟩ := hV
    rw [← hΛV]; exact hf
  · obtain ⟨-, e, he, -⟩ := hc.thP.vP i t
    exact ⟨e, he⟩
  · rw [D.sp.V_rank _ (by omega) (by omega)]
    unfold Formalism.BasicNotions.Ranks.nV
    rfl

end GlobalTheory.DownPair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotient
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker

namespace GlobalTheory.WeilChange

theorem weilData_differ_by_splitFac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om om' : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om' → ∀ g h x y, IsDetRoot S g x → IsDetRoot T h y → ∀ f, IsThetaFunO ψ S T f → om' (g, h) f = ((splitFacO χS' χT' x y : ℂ) * (splitFacO χS χT x y : ℂ)⁻¹) • om (g, h) f := by
  intro D ψ S T χS χT χS' χT' om om' H H' g h x y hx hy f hf
  have rS : ResEta D (χS⁻¹ * χS') 0 :=
    resEta_parity (resEta_mul (resEta_inv H.resS) H'.resS) (by omega)
  have rT : ResEta D (χT⁻¹ * χT') 0 :=
    resEta_parity (resEta_mul (resEta_inv H.resT) H'.resT) (by omega)
  obtain ⟨om₂, H₂, h₂⟩ := exists_weilDatum_twist D ψ H.std S T χS χT (χS⁻¹ * χS') (χT⁻¹ * χT') om H
    (hecke_mul (hecke_inv H.hecS) H'.hecS) (hecke_mul (hecke_inv H.hecT) H'.hecT) rS rT
  rw [mul_inv_cancel_left, mul_inv_cancel_left] at H₂
  rw [GlobalTheory.WeilUniq.weilDatum_unique D ψ H.std S T χS' χT' om' om₂ H' H₂ (g, h) f hf, h₂ g h x y hx hy, LinearMap.smul_apply]
  congr 1
  rw [← Circle.coe_inv, ← Circle.coe_mul]
  congr 1
  simp only [splitFacO, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv]
  generalize (χT' x)⁻¹ = a, (χS y)⁻¹ = b, χS' y = c, χT x = d
  apply Circle.ext
  simp only [Circle.coe_mul]
  ring

end GlobalTheory.WeilChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilTensorRuleScalarEqOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilTensorRule_scalar_eq_one : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χA χB χT : (AE D)ˣ →* Circle) (omS : Om S T) (omA : Om A T) (omB : Om B T), IsWeilDatumO ψ S T (χA * χB) χT omS → IsWeilDatumO ψ A T χA χT omA → IsWeilDatumO ψ B T χB χT omB → ∀ a b h f, IsThetaFunO ψ S T f → ∀ u v, omS (o.emb (a, b), h) f ((o.resS T).symm (u, v)) = omA (a, h) (fun u' => omB (b, h) (fun v' => f ((o.resS T).symm (u', v'))) v) u := by
  first | exact @GlobalTheory.TensorScalarOne.tensor_scalar_one | exact GlobalTheory.TensorScalarOne.tensor_scalar_one | (intros; apply GlobalTheory.TensorScalarOne.tensor_scalar_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittMixedCoordinateWeilTranslateCompactMajorantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittMixedCoordinate_weilTranslate_compact_majorant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → ∀ (S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → ∀ Kp : Set (GA D S × GA D T), IsCompact Kp → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ N : ℕ, ∃ C : ℝ, ∀ p ∈ Kp, ∀ x w, ‖d.mixS T ψ v.μ v.𝓕 (om p f) x w‖ ≤ C * maj θ K N x := by
  first | exact @GlobalTheory.Unf.mixS_om_compact_maj | exact GlobalTheory.Unf.mixS_om_compact_maj | (intros; apply GlobalTheory.Unf.mixS_om_compact_maj <;> assumption)
end

