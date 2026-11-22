import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0044
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0494
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0513
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0821
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0803
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0974
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0975
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0981
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OfFirstStepLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ToUnitsCompToCircle
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0894
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBound
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0977
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0090
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.Bundle0002
import Formalism.SharpRestriction.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0011
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodReductionCondition
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCuspParamGoodRow
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.RowCuspFromLift

theorem isoInf_append (D : D7) (L L' : List (Part D.naut.CG)) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut (L ++ L') τ = isoInf D.nd D.naut L τ + isoInf D.nd D.naut L' τ := by
  unfold isoInf
  rw [List.map_append, List.sum_append]

theorem isoInf_perm (D : D7) {L L' : List (Part D.naut.CG)} (h : L.Perm L') (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut L τ = isoInf D.nd D.naut L' τ := by
  unfold isoInf
  exact (h.map _).sum_eq

theorem eta_emb (s : Multiset ℂ) (h : s = {1 / 2} ∨ s = {-(1 / 2)}) :
    (s.map (fun z => -z) = {-(1 / 2)} → s = {1 / 2}) ∧ (s.map (fun z => -z) = {1 / 2} → s = {-(1 / 2)}) := by
  rcases h with rfl | rfl
  · refine ⟨fun _ => rfl, fun h' => ?_⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'
  · refine ⟨fun h' => ?_, fun _ => rfl⟩
    rw [Multiset.map_singleton, Multiset.singleton_inj] at h'
    norm_num at h'

theorem isoInf_one (D : D7) {a : ℕ} (ρ : D.naut.CG a) (τ : D.host.E →+* ℂ) :
    isoInf D.nd D.naut [⟨a, ρ, 1⟩] τ = D.naut.infG ρ τ := by
  simp [isoInf]

theorem cuspParam_of_lift : ∀ (D : D7) (Rw : RowSide D), ParLaws D → ∀ j σ π μ Pa, LiftAt D Rw j σ π μ → RowLoc D Rw σ →
    SphericalInertData.IsBC D.nd D.naut D.nbc j π Pa → (⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ : Part D.naut.CG) ∈ Pa →
    D.nd.goodRow σ → ∃ π', GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.IsCuspParam D Rw σ π' := by
  intro D Rw hP j σ π μ Pa hL hR hB hm hg
  have hLP : SumRepresentations.At.TieLP D.nd D.naut := hP.tie0.1
  have hAut : SumRepresentations.At.TieAut D.nd D.naut := hP.tie0.2.1
  have hC := hP.cancel
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hm
  set m : Part D.naut.CG := ⟨1, D.naut.tw μ D.naut.etaTinv, D.R.t⟩ with hmdef
  set L := l₁ ++ l₂ with hLdef
  have hperm : (l₁ ++ m :: l₂).Perm (L ++ [m]) :=
    List.perm_middle.trans (List.perm_append_singleton _ _).symm
  have hLmem : ∀ p ∈ L, p ∈ l₁ ++ m :: l₂ := fun p hp => by
    rcases List.mem_append.1 hp with h | h
    · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)
  obtain ⟨hB1, -, hB3, hB4, hB5, hB6⟩ := hB

  have hpos : ∀ p ∈ twistIso D.nd D.naut L D.naut.etaT, 1 ≤ p.a ∧ 1 ≤ p.d := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    exact ⟨(hB1 q (hLmem q hq)).1, (hB1 q (hLmem q hq)).2.1⟩
  have hrank : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = D.R.r := by
    have e1 : rankIso D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) = rankIso D.nd D.naut L := by
      unfold rankIso twistIso
      rw [List.map_map]
      rfl
    rw [e1]
    have hr : rankIso D.nd D.naut (L ++ [m]) = D.R.nV := by
      rw [← hB3]; unfold rankIso; exact ((hperm.map _).sum_eq).symm
    unfold rankIso at hr ⊢
    rw [List.map_append, List.sum_append] at hr
    simp only [hmdef, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero] at hr
    have : D.R.nV = D.R.r + D.R.t := rfl
    omega
  have hloc : ∀ w, IsSplitPl D.host w →
      isoLoc D.nd D.naut (twistIso D.nd D.naut L D.naut.etaT) w = Rw.locR σ w := by
    intro w hw
    have e1 := hB4 w hw
    rw [hL.loc w hw, GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append,
      (hLP w (Rw.locR σ w) (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w)
        (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaTinv w) 0 (D.naut.locG_dim _ w)
        (D.naut.locG_dim _ w)).1] at e1
    have e2 : isoLoc D.nd D.naut [m] w =
        D.naut.lpChar (spehLoc D.nd D.naut ⟨1, μ, D.R.t⟩ w) (D.naut.locG D.naut.etaTinv w) := by
      rw [GlobalTheory.RowThetaParam.isoLoc_cons, GlobalTheory.RowThetaParam.isoLoc_nil, D.naut.lpSum_zero]
      exact GlobalTheory.RowThetaParam.spehLoc_tw D.nd D.naut hLP hC ⟨1, μ, D.R.t⟩ D.naut.etaTinv w
    rw [e2] at e1
    have e3 := hC w _ _ _ e1
    rw [GlobalTheory.RowThetaParam.isoLoc_twistIso D.nd D.naut hLP hC, e3,
      (GlobalTheory.RowThetaParam.lpChar_eta_inv D.nd D.naut hLP _).2]
  obtain ⟨π', hπ'⟩ := GlobalTheory.RowCuspLabels.cusp_of_goodRow D Rw hP.lab σ hg _ hpos hrank hloc
  obtain ⟨q, hLq, hq⟩ := List.map_eq_singleton_iff.1 (show L.map _ = _ from hπ')
  obtain ⟨a, ρ, d⟩ := q
  simp only [Formalism.BasicNotions.Part.mk.injEq] at hq
  obtain ⟨rfl, h2, rfl⟩ := hq
  have h2' := eq_of_heq h2
  subst h2'
  have hmemq : (⟨D.R.r, ρ, 1⟩ : Part D.naut.CG) ∈ l₁ ++ m :: l₂ := hLmem _ (by rw [hLq]; exact List.mem_singleton_self _)
  have hsplit : ∀ w, IsSplitPl D.host w → D.naut.locG (D.naut.tw ρ D.naut.etaT) w = Rw.locR σ w := by
    intro w hw
    have hs := hloc w hw
    rw [hπ', SphericalInertData.isoLoc_single] at hs
    exact hs
  have hinf : ∀ τ : D.what₂.Tau, D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ) =
        GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ) ∧
      D.naut.infG (D.naut.tw ρ D.naut.etaT) (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ) =
        (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.hcSigma (D.hc τ)).map (fun z => -z) := by
    intro τ
    have eA := hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)
    have eB := hB6 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)
    rw [isoInf_perm D hperm, isoInf_append, (hL.inf τ).1] at eA
    rw [isoInf_perm D hperm, isoInf_append, (hL.inf τ).2] at eB
    have fA := add_right_cancel eA
    have fB := add_right_cancel eB
    rw [hLq, isoInf_one] at fA fB
    have gA := (eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).1).1
      (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTau D τ)).2).symm.trans (hL.eta τ).1)
    have gB := (eta_emb _ (hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).1).2
      (((hAut.2.1 (GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.embTauBar D τ)).2).symm.trans (hL.eta τ).2)
    rw [D.naut.infG_tw _ _ _ _ gA, D.naut.infG_tw _ _ _ _ gB, fA, fB]
    simp [Multiset.map_map, Function.comp_def]
  refine ⟨D.naut.tw ρ D.naut.etaT, D.naut.csd_tw ρ D.naut.etaT hAut.1.1 (hB1 _ hmemq).2.2, GlobalTheory.RowRegAlg.ralg_of_infG D _ hinf, hsplit,
    fun w hw => ?_, fun w hw hw' => ?_, hinf⟩
  · have hu := (hB5 w hw).1
    rw [GlobalTheory.RowThetaParam.isoLoc_perm D.nd D.naut hperm, GlobalTheory.RowThetaParam.isoLoc_append, D.naut.unr_sum, hLq,
      SphericalInertData.isoLoc_single] at hu
    rw [D.naut.locG_tw]
    exact D.naut.unr_char _ _ (D.naut.locG_dim _ w) hu.1 (D.naut.etaT_unr w)
  · rw [hsplit w hw]
    exact (hR w hw hw').1

end GlobalTheory.RowCuspFromLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLevelSeriesTranslateBoundedDenominator
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries

set_option maxHeartbeats 1600000 in

theorem exists_move_denomAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ l : ℕ, l.Prime → ∀ s ∈ GfC V, ∃ c : ℕ, ∀ z ∈ GfC V, OneAt V l z → ∀ M bad : ℕ, M ≠ 0 → bad ≠ 0 → l ∣ bad → ∃ (γ h a : GA D V) (γ' : GL (Fin V.rank) D.host.E), γ ∈ GQ V ∧ GlobalTheory.Member.IsRat V γ γ' ∧ a ∈ GinfC V ∧ γ * a ∈ GfC V ∧ SplitOffBad V bad h ∧ DenomAt l c γ' ∧ ∀ (e : AE D) (O : Subring ℂ), ∀ f ∈ trSp ψ V W ΛV ΛW f₀ e M O, ∀ (BW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (Q : MvPolynomial (FVar D W.rank V.rank) ℂ) (g : GA D W), thetaKO om (s * z) g (stdF ψ θ V W sW BW f Q) = thetaKO om h g (om (a, 1) (stdF ψ θ V W sW BW f Q)) := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP l hl s hs
  have hstd : Bridge.hLat V 1 = Formalism.L2.Pj.stdLat D.host.E V.rank := by
    apply SetLike.coe_injective
    rw [GlobalTheory.Equiv.StdSpace.identityClassLattice_eq_selfDualFrameLattice, ← hP.2.2.1, hP.2.2.2.2.2.2.1]
  obtain ⟨c, hc⟩ := GlobalTheory.T.rationalPart_denominator_bounded_by_prime_power D V hstd l hl s
  refine ⟨c, fun z hz hOne M bad hM hbad hlb => ?_⟩
  obtain ⟨J₁, hJ₁o, hJ₁⟩ := GlobalTheory.T.exists_open_subgroup_hermitianLattice_eq_standard D V hstd
  obtain ⟨J₂, hJ₂o, hJ₂⟩ := GlobalTheory.T.exists_open_subgroup_fix_vacuum_translates D ψ θ V W χV χW om ΛV ΛW sW f₀ hP M hM
  have hJo : IsOpen ((J₁ ⊓ J₂ : Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := hJ₁o.inter hJ₂o
  obtain ⟨γ, h, kJ, hsp, e⟩ := GlobalTheory.SplitRepsOpen.exists_rep_splitOffBad D V (J₁ ⊓ J₂) bad hbad hJo (fin V (s * z))
  obtain ⟨k', hk', ek⟩ := Formalism.IndefR.TopMult.exists_lift (kJ : Bridge.Gf V)
  obtain ⟨a, ha_def⟩ : ∃ a : GA D V, a = h⁻¹ * ((γ : GA D V)⁻¹ * (s * z) * k'⁻¹) := ⟨_, rfl⟩
  have hfa : finHom V a = 1 := by
    have e' := congrArg Subtype.val e
    have ek' := congrArg Subtype.val ek
    simp only [MonoidHom.coe_rangeRestrict, Bridge.ratF, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Subgroup.coe_mul] at e' ek'
    rw [ha_def, map_mul, map_inv, map_mul, map_mul, map_inv, map_inv, ek', e']
    group
  have ha : a ∈ GinfC V := hfa
  have hγa : (γ : GA D V) * a ∈ GfC V := by
    have h1 : infHom V h = 1 := hsp.1
    have h2 : infHom V (s * z) = 1 := mul_mem hs hz
    have h3 : infHom V k' = 1 := hk'
    show infHom V ((γ : GA D V) * a) = 1
    rw [ha_def, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, map_inv, h1, h2, h3]
    group
  have hs' : s * z = (γ : GA D V) * (h * a) * k' := by
    rw [ha_def]; group
  obtain ⟨γ', -, hγ'⟩ := γ.2
  have hrat : GlobalTheory.Member.IsRat V (γ : GA D V) γ' := hγ'.symm
  have hkJ : (kJ : Bridge.Gf V) ∈ J₁ := (kJ.2 : (kJ : Bridge.Gf V) ∈ J₁ ⊓ J₂).1
  have hkJ' : ((kJ : Bridge.Gf V))⁻¹ ∈ J₁ := inv_mem hkJ
  have hden : DenomAt l c γ' := hc z hOne (γ : GA D V) h γ' kJ bad hrat hlb hsp (hJ₁ _ hkJ) (hJ₁ _ hkJ') e
  refine ⟨γ, h, a, γ', γ.2, hrat, ha, hγa, hsp, hden, fun e O f hf BW Q g => ?_⟩
  have hω := hP.1.weil
  have hθ : IsInfFam θ := hP.1.inf
  have hfix : om (k', 1) f = f := by
    have hk2 : fin V k' ∈ J₂ := by
      have ek2 : fin V k' = kJ := ek
      rw [ek2]; exact (kJ.2 : (kJ : Bridge.Gf V) ∈ J₁ ⊓ J₂).2
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, -, hy, rfl⟩ := hx
      exact hJ₂ k' hk' hk2 y hy
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul r x _ hx =>
      change om (k', 1) ((r : ℂ) • x) = (r : ℂ) • x
      rw [map_smul, hx]
  have hthf : IsThetaFunO ψ V W f := GlobalTheory.T.isThetaFunction_of_mem_span_vacuumTranslates D ψ θ V W χV χW om ΛV ΛW sW f₀ hP e M O f hf
  have hT : ∀ P, IsThetaFunO ψ V W (stdF ψ θ V W sW BW f P) := fun P =>
    GlobalTheory.Chain.InnerSteps.theta_pureTensorO hω.std hθ _ _ _ _ hthf P
  have hk1 : om (k', 1) (stdF ψ θ V W sW BW f Q) = stdF ψ θ V W sW BW f Q := by
    have := GlobalTheory.FiniteFock.om_pureTensorO_of_finite ψ θ V W χV χW om hθ hω (fun _ => 1) sW (fun _ => 1) BW f hT k' hk' 1
      (one_mem _) 1 (by rw [one_smul]; exact hfix) Q
    rw [one_smul] at this
    exact this
  have hp : ((s * z, g) : GA D V × GA D W) = ((γ : GA D V), 1) * ((h, g) * (a, 1)) * (k', 1) := by
    rw [hs']; simp [Prod.mk_mul_mk]
  have e1 : om (s * z, g) = om ((γ : GA D V), 1) * (om (h, g) * om (a, 1)) * om (k', 1) := by
    rw [hp, map_mul, map_mul, map_mul]
  have hth := hω.om_pres ((h, g) : GA D V × GA D W) _ (hω.om_pres ((a, 1) : GA D V × GA D W) _ (hT Q))
  show om (s * z, g) (stdF ψ θ V W sW BW f Q) 0 = om (h, g) (om (a, 1) (stdF ψ θ V W sW BW f Q)) 0
  rw [e1, Module.End.mul_apply, Module.End.mul_apply, hk1, Module.End.mul_apply,
    hω.om_aut _ γ.2 1 (one_mem _) _ hth]

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.PlaceRead

variable {D : D7}

abbrev Amb (D : D7) (j : Fin D.R.m) : Type := Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank

section Choice

variable (c : NChoice D) (w : D.what₂.places.Pl)

abbrev KE : Type := FractionRing (c.Oe w)

abbrev chr : G D.host.E D.nd.Om →* (D.ntw.Ok (c.twI w) (c.k' w))ˣ := (c.psi' w).comp (D.ntw.art (c.twI w) (c.Q w))

variable {c w}

def viaOk (ι : KE c w →+* ℂ) : D.ntw.Ok (c.twI w) (c.k' w) →+* ℂ := ι.comp (algebraMap _ _)

def ringOf (ι : KE c w →+* ℂ) : Subring ℂ := (ι.comp (algebraMap (c.Oe w) _)).range

def twVia (ρ : Setup D.ntw) (ι : KE c w →+* ℂ) : Twist D Circle :=
  twistOf ρ.rc (viaOk ι) (ρ.ch (c.twI w)) (c.Q w) (chr c w)

def Extends (ρ : Setup D.ntw) (ε : KE c w →+* ℂ) : Prop := viaOk ε = ρ.eOk (c.twI w) (c.sd w) (c.k' w)

theorem Extends.twVia_eq {ρ : Setup D.ntw} {ε : KE c w →+* ℂ} (h : Extends ρ ε) :
    twVia ρ ε = ρ.tw (c.twI w) (c.sd w) (c.k' w) (c.Q w) (chr c w) := by
  rw [twVia, h]; rfl

theorem Extends.apply {ρ : Setup D.ntw} {ε : KE c w →+* ℂ} (h : Extends ρ ε) (a : D.ntw.Ok (c.twI w) (c.k' w)) :
    ε (algebraMap _ _ a) = ρ.eOk (c.twI w) (c.sd w) (c.k' w) a := RingHom.congr_fun h a

variable {ρ : Setup D.ntw} {hρ : ρ.Good} {j : Fin D.R.m} {rd : Rd ρ D.nexp (c.twI w) j (c.sd w)}

def rdE (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) : Tgt c w (j.1 + 1) →ₛₗ[ε] Amb D j :=
  let φ : Tgt c w (j.1 + 1) →+ Amb D j := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ε a)).comp (T.rdV (c.k' w) (c.Q w) (chr c w)).toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun s a f => by
      change ε (s • a) • T.rdV _ _ _ f = ε a • T.rdV _ _ _ (s • f)
      rw [← algebraMap_smul (FractionRing (D.ntw.Ok (c.twI w) (c.k' w))) s f, LinearMap.map_smulₛₗ, Algebra.smul_def s a, map_mul, hε.apply,
        smul_smul, mul_comm]
      rfl
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun s x => by
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul a f =>
        change ε (s • a) • T.rdV _ _ _ f = ε s • ε a • T.rdV _ _ _ f
        rw [smul_eq_mul, map_mul, mul_smul] }

theorem rdE_tmul (T : CellTie hρ D.nexp rd) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (a : KE c w) (f) :
    rdE T hε (a ⊗ₜ f) = ε a • T.rdV (c.k' w) (c.Q w) (chr c w) f := rfl

variable (rd) in

def rdF (hρ : ρ.Good) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) :
    KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w) →ₛₗ[ε] (GA D (Wc D j) → ℂ) :=
  let φ : KE c w ⊗[D.ntw.O (c.twI w)] D.nexp.Fm (c.twI w) (j.1 + 1) (c.sd w) →+ (GA D (Wc D j) → ℂ) := TensorProduct.liftAddHom
    { toFun := fun a => (DistribSMul.toAddMonoidHom _ (ε a)).comp rd.toAddMonoidHom
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp [add_mul] }
    fun s a f => by
      change ε (s • a) • rd f = ε a • rd (s • f)
      rw [rd_smul, Algebra.smul_def s a, map_mul, IsScalarTower.algebraMap_apply _ (D.ntw.Ok (c.twI w) (c.k' w)) (KE c w), hε.apply,
        hρ.ek_e, smul_smul, mul_comm]
  { toFun := φ
    map_add' := φ.map_add
    map_smul' := fun s x => by
      induction x using TensorProduct.induction_on with
      | zero => rw [smul_zero, map_zero, smul_zero]
      | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
      | tmul a f =>
        change ε (s • a) • rd f = ε s • ε a • rd f
        rw [smul_eq_mul, map_mul, mul_smul] }

theorem rdF_tmul (hρ : ρ.Good) {ε : KE c w →+* ℂ} (hε : Extends ρ ε) (a : KE c w) (f) :
    rdF rd hρ hε (a ⊗ₜ f) = ε a • rd f := rfl

end Choice

def ConjAt {j : Fin D.R.m} (Φ : VsV D j ℂ →ₗ[ℂ] PolF D (Wc D j).rank (Vc D j).rank) (κ : ℂ) (τ : ℂ ≃+* ℂ) (F F' : Amb D j) : Prop :=
  ∀ h, ∃ x x' : VsV D j ℂ, ConjVec j τ x x' ∧ F h = Φ x ∧ F' h = Φ ((τ κ / κ) • x')

def intLL (D : D7) : Subring ℂ := (D.what₂.embLL.comp (algebraMap (𝓞 D.what₂.LL) D.what₂.LL)).range

theorem used_of_tw {w : D.what₂.places.Pl} (h : D.what₂.muAt w ≠ D.what₂.mu0) : Used0 D (D.what₂.muTw w) :=
  Or.inr ⟨w, ((D.what₂.muAt_or w).resolve_left h).symm⟩

section Rows

variable {X : RealSide D} {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0)

def formOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) : D.what₂.Mt μ (j.1 + 1) →ₗ[ℂ] (X.R.HV j (Y.tupT μ)).H :=
  (LinearEquiv.ofInjective _ (Y.hinj j (Y.tupT μ))).symm.toLinearMap ∘ₗ Submodule.inclusion inf_le_left ∘ₗ
    (Y.IL.jMt μ hμ j).toLinearMap

theorem extV_formOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (x : D.what₂.Mt μ (j.1 + 1)) :
    X.R.toRealDat.extV j (Y.tupT μ) (formOf Y hμ j x) = (Y.IL.jMt μ hμ j x).1 :=
  congrArg Subtype.val ((LinearEquiv.ofInjective _ (Y.hinj j (Y.tupT μ))).apply_symm_apply _)

def fockOf {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) :
    D.what₂.Mt μ (j.1 + 1) →ₗ[ℂ] Amb D j :=
  (X.R.ioP j (PiTensorProduct.tprod ℂ u)).compLeft _ ∘ₗ (X.R.HV j (Y.tupT μ)).e ∘ₗ formOf Y hμ j

theorem fockOf_apply {μ : D.what₂.Tup} (hμ : Used0 D μ) (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) (x h) :
    fockOf Y hμ j u x h = X.R.ioP j (PiTensorProduct.tprod ℂ u) ((X.R.HV j (Y.tupT μ)).e (formOf Y hμ j x) h) := rfl

variable (X) in

def IsLow (j : Fin D.R.m) (u : ∀ τ, lowT (X.R.MW j (sg0 D X.A3.A)) τ) : Prop :=
  ∀ τ, (u τ : (X.R.MW j (sg0 D X.A3.A)).sm τ) = X.geo.v₀ j (sg0 D X.A3.A) τ

variable {S : NX.RatDat D.ntw} {YS : NX.NExpRealS X.R X.cG S} (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl)
  (j : Fin D.R.m)

abbrev baseOf : Base (Vc D j) (Wc D j) := Z.ρ.B (c.twI w) j (c.sd w)

structure AtPlace : Prop where
  pins : GlobalTheory.Mem.R3.Pins X.R X.F X.cG
  intersectionNumber_baseChange : GlobalTheory.Mem.R3.Holds X.R X.F
  field : FieldOk X
  tw : D.what₂.muAt w ≠ D.what₂.mu0
  ok : TwOK (c.twI w) (c.k' w) (c.Q w) (chr c w)
  cls : ClsQ (D := D) (c.Q w)
  emb : ∀ ε : KE c w →+* ℂ, Extends Z.ρ ε → ∀ x : D.LL0, ε (c.embW w (x : D.what₂.LL)) = embLL0 D x
  val : ∀ σ, ∃ y : D.what₂.LL, c.embW w y = algebraMap _ (KE c w) ((chr c w σ : (D.ntw.Ok (c.twI w) (c.k' w))ˣ) : D.ntw.Ok (c.twI w) (c.k' w))
  U_eq : ∀ g : X.Γ, X.cG (X.R.eG g) ∈ D.nexp.U ↔ g ∈ X.F.P0
  psi_eq : ∀ i b (g : X.F.P0) (h : X.cG (X.R.eG g) ∈ D.nexp.U),
    Z.ρ.e i b (D.nexp.psiU i b ⟨_, h⟩ : (FractionRing (D.ntw.O i))ˣ) = (D.what₂.embLL (X.F.ψ0 g : D.what₂.LLˣ))⁻¹
  ks : (S.A (j.1 + 1)).IsKsForm
  rat : RatRow YS X.geo.v₀ Z.good (c.twI w) j (c.sd w)
  tup : ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
    IsTupOf X.R.toRealDat (baseOf Z c w j) (twVia Z.ρ ι) (Y.tupT (D.what₂.muTw w))

end Rows

end GlobalTheory.PlaceRead

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GroupAlgebraCentreKeepsTypeSpacesAtLocalisations
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CenKeepsTypeLoc

theorem main : ∀ (D : D7) (M : MtFam D), AVTied D M → GlobalTheory.HeightCounting.Up.CenLoc D M → OnMtPreservesTypeV D := by
  intro D M A hC i PI z F hF
  by_cases hz : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))
  · obtain ⟨L, -, hL⟩ := hC i
    rw [NTypes.onMt, dif_pos hz]
    rw [A.typeV, Submodule.mem_comap] at hF ⊢
    have e : (M.loc i).real (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i) ⟨z, hz⟩ F) =
        actSum D L z ((M.loc i).real F) := hL ⟨z, hz⟩ F
    rw [e]
    unfold actSum Finsupp.sum
    exact Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (GlobalTheory.CenKeepsType.rt_mem_isoTyp _ _ _ _ hF)
  · rw [NTypes.onMt, dif_neg hz]
    exact Submodule.zero_mem _

end GlobalTheory.CenKeepsTypeLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_sum_self_dual_frames_bound : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → (∀ PP ∈ P, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ t : WO S T, IsHalf (cA D e) t → IsIntM (frMapAdj S T βS βT t) → t ∈ latO S T ΛS ΛT (fun _ => True) := by
  first | exact @GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int | exact GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int | (intros; apply GlobalTheory.HalfAdjLattice.mem_latO_of_adj_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowClosureLinkingStatement
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.row_closure_linking : Hypotheses₂ → ∀ (Q : GlobalTheory.Mem.Top.V4.Slot) (Lk : GlobalTheory.Fc.LkT GlobalTheory.Fc.Bundle) (C : ℝ) (CT : ℕ), 0 ≤ C → GlobalTheory.Fc.RowE Q Lk (fun _ D O _ _ => GlobalTheory.NFacts.Facts D O.ex.nch ∧ Extra D C CT) → GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => BoundAtTwoAndThreeForFamily Fm) → GlobalTheory.Fc.R1.PredicateAtBundlePoints Q Lk (fun 𝒞 => Closed 𝒞 fun Fm _ => Formalism.MainNotions.LinkN Fm) := by
  first | exact @GlobalTheory.NLink.linkN_row | exact GlobalTheory.NLink.linkN_row | (intros; apply GlobalTheory.NLink.linkN_row <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnfoldedThetaIntegralEqMulPartialRankinSelbergLStatement
section
open NumberField IsDedekindDomain MeasureTheory GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.RSJ Filter Topology Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedThetaIntegral_eq_mul_partialRankinSelbergL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (σ σ' : CG E a), 1 ≤ a → σ.IsUnitary → σ'.IsUnitary → ∀ T : Finset (HeightOneSpectrum (𝓞 E)), (∀ w ∈ T, ∀ w' : HeightOneSpectrum (𝓞 E), Ideal.comap (algebraMap ℤ (𝓞 E)) w'.asIdeal = Ideal.comap (algebraMap ℤ (𝓞 E)) w.asIdeal → w' ∈ T) → (∀ w ∉ T, ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, GlobalTheory.JSW.psiLoc w (x * y) = 1) ↔ x ∈ Ov E w) → UnrOutside T σ → UnrOutside T σ' → ∃ (N : ℕ) (Φ : (Fin a → Cinf E) → ℂ) (π π' : CuspSub E a) (φ φ' : GA E a → ℂ), CG.mk π = σ ∧ CG.mk π' = σ' ∧ φ ∈ GlobalTheory.JSW.mspanR π ∧ φ' ∈ GlobalTheory.JSW.mspanR π' ∧ φ ≠ 0 ∧ φ' ≠ 0 ∧ 0 < N ∧ ContDiff ℝ (⊤ : ℕ∞) Φ ∧ HasCompactSupport Φ ∧ (∀ ℓ : Fin a, (ℓ : ℕ) + 1 = a → tsupport Φ ⊆ {u | ∀ w, u ℓ w ≠ 0}) ∧ ∀ (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → ∃ H : ℂ → ℂ, Differentiable ℂ H ∧ (∀ x : ℝ, 0 < (H x).re ∧ (H x).im = 0) ∧ ∀ x : ℝ, 1 < x → GlobalTheory.RSJ.Zint μ 𝓕 φ φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ φ Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ w.1) ((sat σ w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) ∧ GlobalTheory.RSJ.Zint μ 𝓕 φ' φ' Φ N x = H x * ∏' w : {w : HeightOneSpectrum (𝓞 E) // w ∉ T}, locL (Ideal.absNorm w.1.asIdeal) (sat σ' w.1) ((sat σ' w.1).map (Units.map (starRingEnd ℂ).toMonoidHom)) (x : ℂ) := by
  first
  | exact @GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth
  | exact GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth
  | (intros; apply GlobalTheory.ZEul.Smooth.zint_eq_mul_partialL_smooth <;> assumption)
end

