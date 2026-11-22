import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0516
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0017
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0279
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0314
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0270
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0077
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0456
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0288
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0292
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0445
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0462
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0511
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0463
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0512
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RowsRestWordColumnUnitBaseTupleAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesFormTrueChains
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainComparisonTransferOtherLaterStages
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw

set_option maxHeartbeats 4000000 in

theorem chT_tr : ∀ (B : Base) (C : Cols B) (a b : Late B C) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (Ks : Type) [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL] (A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m) (R : RealDat a.D A Ks) (F : Face a.D A) (y : Hd R) (y' : HdB b R), Same b y y' → ∀ (bb : Bool) (Φ : Type) (rep : Φ → _) (Top : C.Tup → Hs) (c : ChD C.Tup Φ B.R.m Top) jA (t : ChT y F bb rep (Top := Top) jA c) jA', HEq jA' jA → ∃ t' : @ChT b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) y' (face b F) bb Φ ((rep)) Top jA' c, letI := alg b iK; HEq t'.jE t.jE ∧ HEq t'.jM t.jM ∧ HEq t'.jX t.jX := by
  intro B C a b G _ _ Pl0 T Ks _ _ iK A R F y y' hS bb Φ rep Top c jA t jA' hjA
  have hP := (GlobalTheory.T.typeRepresentativesParts_otherLaterStages B C a b G Pl0 T Ks A R F y y' hS).2.1
  obtain ⟨htup, htupT, hPY, hPW⟩ := hS
  rcases y' with ⟨tup', tupT', tupT_tup', tup0', hm', hTop', hinj', PY', PW', ιW', isomFin', frameMatch', hF', stdPsi'⟩
  have e1 : tup' = (y.tup) := eq_of_heq ((htup))
  have e2 : tupT' = (y.tupT) := eq_of_heq ((htupT))
  subst e1 e2
  have e3 : jA' = (jA) := eq_of_heq ((hjA))
  subst e3
  have hCC := chain_CC b F y.tupT y.hm y.hTop
  have hCCX := chain_CCX b F y.tupT y.hm y.hTop
  have hCCP := chain_CCP b F y.tupT y.hm y.hTop
  have hCCXP := chain_CCXP b F y.tupT y.hm y.hTop
  have hEEc := chain_EEc b F y.tupT y.hm y.hTop
  letI := alg b iK
  refine ⟨{
    jE := (t.jE)
    jM := (t.jM)
    jX := (t.jX)
    jE_inj := (t.jE_inj)
    jE_range := by
      have e : LinearMap.range t.jE = _ := t.jE_range.trans (congrFun hEEc bb)
      exact (e)
    jE_ip := (t.jE_ip)
    jM_inj := (t.jM_inj)
    jM_range := fun μ hU j h1 h2 => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have h2a : j ≤ a.D.R.m - 1 := (h2)
      have e : LinearMap.range (t.jM μa j) = _ := (t.jM_range μa hUa j h1 h2a).trans (congrFun (congrFun (congrFun hCCP bb) μa) j)
      exact (e)
    jM_ip := (t.jM_ip)
    jX_inj := (t.jX_inj)
    jX_range := fun μ hU => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have e : LinearMap.range (t.jX μa) = _ := (t.jX_range μa hUa).trans (congrFun (congrFun hCCXP bb) μa)
      exact (e)
    jX_ip := (t.jX_ip)
    io0 := fun μ hU x v h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      let va : (c.Mult μa 1).T := (v)
      have e := congrFun (congrFun (congrFun hCC bb) μa) 1
      have h0 : t.jM μa 1 va ∈ (y.C F).CC bb μa 1 := cast (congrArg (t.jM μa 1 va ∈ ·) e.symm) ((h))
      have hv := chain_ioC b (R := R) (y.tupT μa) 0 (t.jM μa 1 va) ((h)) h0
      have e' := (t.io0 μa hUa x va h0).trans (congrArg (fun z => (y.C F).ipE bb (t.jE x) z) hv.symm)
      kexactB e'
    io := fun μ hU j h1 h2 x v h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      have h2a : j + 1 ≤ a.D.R.m - 1 := (h2)
      let va : (c.Mult μa (j + 1)).T := (v)
      have e := congrFun (congrFun (congrFun hCC bb) μa) (j + 1)
      have h0 : t.jM μa (j + 1) va ∈ (y.C F).CC bb μa (j + 1) := cast (congrArg (t.jM μa (j + 1) va ∈ ·) e.symm) ((h))
      have hv := chain_ioC b (R := R) (y.tupT μa) j (t.jM μa (j + 1) va) ((h)) h0
      have e' := (t.io μa hUa j h1 h2a x va h0).trans (congrArg (fun z => (y.C F).ipP bb μa j (t.jM μa j x) z) hv.symm)
      kexactB e'
    ioTop := fun μ hU x v v' hvv h => by
      let μa : a.D.what₂.Tup := (μ)
      have hUa : y.Us μa := (hU)
      let va : (c.Mult μa a.D.R.m).T := (v)
      let va' : (c.Mult μa (a.D.R.m - 1 + 1)).T := (v')
      have hvva : HEq va' va := (hvv)
      have e := congrFun (congrFun hCCX bb) μa
      have h0 : t.jX μa (c.multTop μa va) ∈ (y.C F).CCX bb μa := cast (congrArg (t.jX μa (c.multTop μa va) ∈ ·) e.symm) ((h))
      have hv := chain_ioX b (R := R) y.hm y.hTop (y.tupT μa) (t.jX μa (c.multTop μa va)) ((topMult_tr b y.hTop)) ((h)) h0
      have e' := (t.ioTop μa hUa x va va' hvva h0).trans
        (congrArg (fun z => (y.C F).ipP bb μa (a.D.R.m - 1) (t.jM μa (a.D.R.m - 1) x) z) hv.symm)
      exact (e')
    junk := (t.junk)
    ft := fun π => by
      rw [eq_of_heq (hP bb (rep π))]
      exact (t.ft π)
    disj := fun π π' hne => by
      rw [eq_of_heq (hP bb (rep π)), eq_of_heq (hP bb (rep π'))]
      exact (t.disj π π' hne)
    top := (t.top) }, (HEq.refl t.jE), (HEq.refl t.jM), (HEq.refl t.jX)⟩

end GlobalTheory.Mem.R3.Rw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartsTupleTrivQ
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

set_option maxHeartbeats 8000000 in

theorem match_base_trivQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 B.host.F))) (i : ℕ), i ≤ B.R.m → ∀ (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (Lb0 : Ch0 → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)) (U0 : Ch0 → Subgroup (GA B (B.R.N i))) (chi0 : ∀ β, U0 β →* ℂˣ) (y0 : (I.stp u I.mu0 i).Cl → GA B (B.R.N i)) (st0 : ∀ c, (I.stp u I.mu0 i).Stab c → GL (Fin (B.R.N i)) B.host.E) (k0 : Ch0 → GA B (B.R.N i)), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.Reads u I.mu0 i chOf0 Lb0 U0 chi0 y0 st0 k0 → ∃ (g : Chart I u a i → Ch0) (k : Chart I u a i → GA B (B.R.N i)), AdmK I u a i k ∧ (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) ∧ ∀ β, ∃ c, chartOf I u a i c = β ∧ ∃ c0, chOf0 c0 = g β ∧ ∀ x : GA B (B.R.N i), (∀ v ∈ Q, bc (prV (E := B.host.E) v) x = 1) → (∀ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ → ∃ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 ∧ (I.stp u a i).chr c.1 κ = (I.stp u I.mu0 i).chr c0.1 κ0) ∧ (∀ κ0, LocMv I u I.mu0 i c0 ((k0 (g β))⁻¹ * x * k0 (g β)) κ0 → ∃ κ, LocMv I u a i c ((k β)⁻¹ * x * k β) κ) := by
  intro B X I hI hP l u a Q i hi Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 h1 h2 hQ hR0
  obtain ⟨c0f, t, ht1, ht2, ht3, hM⟩ := GlobalTheory.Mem.Col2.TC.ChTw.Match.match_idx I hI hP l u a Q i hi h1 h2 hQ
  refine ⟨fun β => chOf0 (c0f β), fun β => k0 (chOf0 (c0f β)) * t β,
    GlobalTheory.Mem.Col2.TC.ChTw.admissibleBasePoint_chart_mul_twist I hI u a i Ch0 chOf0 Lb0 U0 chi0 y0 st0 k0 hR0 _ t ht1 ht2 ht3, ?_, ?_⟩
  · intro β v hv
    obtain ⟨hT, hg⟩ := GlobalTheory.Mem.Col2.TC.underQ_prime_to_bad I hI l u a v hv
    show bc (prV (E := B.host.E) v) (k0 (chOf0 (c0f β)) * t β) = 1
    rw [map_mul, hR0.k_off (chOf0 (c0f β)) v hT (GlobalTheory.Mem.Col2.TC.not_underQ_mu0 I hI v) (Or.inl rfl), ht2 β v (Or.inr hg), mul_one]
  intro β
  obtain ⟨c, hc, hs⟩ := hM β
  refine ⟨c, hc, c0f β, rfl, ?_⟩
  intro x hx
  have e : (k0 (chOf0 (c0f β)) * t β)⁻¹ * x * (k0 (chOf0 (c0f β)) * t β) =
      (t β)⁻¹ * ((k0 (chOf0 (c0f β)))⁻¹ * x * k0 (chOf0 (c0f β))) * t β := by group
  rw [e]
  refine hs _ fun v hv => ?_
  rw [map_mul, map_mul, hx v hv, mul_one, map_inv, inv_mul_cancel]

set_option maxHeartbeats 8000000 in

theorem charts_match_trivQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (g : Chart I u a i → Ch0) (k : Chart I u a i → GA B (B.R.N i)), AdmK I u a i k ∧ (∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) ∧ ∀ (K : ∀ β : Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.Reads u a i (chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k → ∀ β, (∀ κ : (K β).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → ∃ h' : κ.1 ∈ (K0 (g β)).lev.U, (K β).lev.chi κ = (K0 (g β)).lev.chi ⟨κ.1, h'⟩) ∧ ∀ κ' : (K0 (g β)).lev.U, (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ'.1 = 1) → κ'.1 ∈ (K β).lev.U := by
  intro B X I hI hP l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR0
  obtain ⟨k0, hk0⟩ := hR0
  obtain ⟨g, k, hk, hkQ, hM⟩ := match_base_trivQ I hI hP l u a Q i hi Ch0 chOf0 _ _ _ _ _ k0 h1 h2 hQ hk0
  refine ⟨g, k, hk, hkQ, ?_⟩
  intro K hK β
  obtain ⟨c, hc, c0, hc0, hx⟩ := hM β
  subst hc
  have hgram := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have huni : ∀ {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))} (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (B.T u) (I.rec7 l Z).R.f bad) (x : GA B (B.R.N i)), x ∈ S.U → x ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i) := by
    intro bad S x hx
    have h := ((S.U_eq x).1 hx).1
    rw [hgram] at h
    exact h
  have hnQ0 : ∀ v, ¬ I.UnderQ I.mu0 v := by
    rintro v ⟨P, hP, -⟩
    rw [ColIn.twistPrimes_reference_tuple_eq_empty] at hP
    exact absurd hP (Finset.notMem_empty _)
  refine ⟨fun κ hκ => ?_, fun κ' hκ' => ?_⟩
  · obtain ⟨κ1, hl1⟩ := GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem I hI l u a i hi _ _ _ _ _ _ k hK c κ.1 (huni _ κ.1 κ.2)
      (fun v hv => hκ v ((hQ v).2 hv)) κ.2
    obtain ⟨κ0, hl0, hchr⟩ := (hx κ.1 hκ).1 κ1 hl1
    obtain ⟨hm0, hc0'⟩ := reads_of_locMv I hI hk0 c0 κ.1 κ0 (by rw [hc0]; exact hl0)
    obtain ⟨hm, hcc⟩ := reads_of_locMv I hI hK c κ.1 κ1 hl1
    have key : ∀ β0 (e : chOf0 c0 = β0), ∃ h' : κ.1 ∈ (K0 β0).lev.U,
        (((K0 β0).lev.chi ⟨κ.1, h'⟩ : ℂˣ) : ℂ) = B.embLL (((I.stp u I.mu0 i).chr c0.1 κ0 : B.LLˣ) : B.LL) := by
      intro β0 e
      subst e
      exact ⟨hm0, hc0'⟩
    obtain ⟨h', e'⟩ := key _ hc0
    refine ⟨h', Units.ext ?_⟩
    rw [e', ← hchr]
    exact hcc
  · have hm0 : κ'.1 ∈ (K0 (chOf0 c0)).lev.U := by rw [hc0]; exact κ'.2
    obtain ⟨κ0, hl0⟩ := GlobalTheory.Mem.Col2.TC.ChTw.locMv_of_mem I hI l u I.mu0 i hi _ _ _ _ _ _ k0 hk0 c0 κ'.1 (huni _ κ'.1 hm0)
      (fun v hv => absurd hv (hnQ0 v)) hm0
    rw [hc0] at hl0
    obtain ⟨κ, hl⟩ := (hx κ'.1 hκ').2 κ0 hl0
    exact (reads_of_locMv I hI hK c κ'.1 κ hl).1

set_option maxHeartbeats 8000000 in

theorem charts_tuple_trivQ : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m) (Ch0 : Type) (chOf0 : (I.stp u I.mu0 i).Cl → Ch0) (K0 : ∀ β : Ch0, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) i hi (fun c : {c // chOf0 c = β} => (I.chain l u I.mu0).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c.1))), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → I.ReadsK l Z u I.mu0 i hi chOf0 K0 → ∃ (Ch : Type) (_ : Finite Ch) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (g : Ch → Ch0), (∃ k : Ch → GA B (B.R.N i), I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β (v : HeightOneSpectrum (𝓞 B.host.F)), I.UnderQ a v → bc (prV (E := B.host.E) v) (k β) = 1) ∧ ∀ β, (∀ v, v ∉ Q → (K β).lev.Uloc v = (K0 (g β)).lev.Uloc v) ∧ (∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) ∧ ∀ (κ : (K β).lev.U) (κ' : (K0 (g β)).lev.U), κ.1 = κ'.1 → (∀ v ∈ Q, bc (prV (E := (I.rec7 l Z).host.E) v) κ.1 = 1) → (K β).lev.chi κ = (K0 (g β)).lev.chi κ' := by
  intro B X I hok hpins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR
  obtain ⟨g, k, hk, hkQ, hC⟩ := charts_match_trivQ I hok hpins l Z u a Q i hi Ch0 chOf0 K0 h1 h2 hQ hR
  obtain ⟨K, hKB⟩ := GlobalTheory.Mem.Col2.ChExM.exists_charts I hok hpins l Z u a Q i hi h1 h2 hQ k hk
  have hK := hKB.1
  have hfin := hKB.2
  have hCK := hC K hK
  haveI := finite_chart I l u a i
  refine ⟨Chart I u a i, inferInstance, chartOf I u a i, K, g, ⟨k, hK, hkQ⟩, fun β => ⟨?_, hfin β, ?_⟩⟩
  · intro v hv
    refine GlobalTheory.stepLevel_uloc_eq_of_agree (K β).lev (K0 (g β)).lev (Q : Set _) (fun x hx => ⟨fun hxK => ?_, fun hx0 => ?_⟩) v hv
    · exact ((hCK β).1 ⟨x, hxK⟩ hx).1
    · exact (hCK β).2 ⟨x, hx0⟩ hx
  · intro κ κ' he hq
    obtain ⟨h', e⟩ := (hCK β).1 κ hq
    exact e.trans (congrArg (K0 (g β)).lev.chi (Subtype.ext he))

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjLevelConjCharacterSymmetricLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ConcreteSettingExists MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem GlobalTheory.Mem.SymFrame.conj_symLevel : ∀ (D : D7) (G' : Type) [Group G'] [Fintype G'] (Pl0 T : Type) (A : FamIn D.what₂.LL G' Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (eR : G' ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ x : X.B.I.E, HEq (X.ιE x) x) → R.toLevCh.Is A.μ0 → (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) → (∀ kv, R.C.P.Div kv.1 (plg kv).1) → (∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)) → ∀ (ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ), IsGenericPsi R.Pg ψ0 → ∀ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π → ∀ (red : X.B.I.Gf → G0g D.nd) (b : (Σ k : Fin 2, D.nd.PlG k) → Fin D.R.r → Fin X.B.I.n → X.B.I.E), IsRedHom X red → FixRed X red b → (∀ kv : (Σ k : Fin 2, D.nd.PlG k), ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ (D.naut.plGw kv.1 kv.2).asIdeal) → ∃ c : G0g D.nd, ∀ k ∈ X.B.I.Kset, (k ∈ X.K2 ↔ reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧ ∀ hk : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H, (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hk⟩ : ℂˣ) : ℂ) = star (X.chi2 k) := by
  intro D G' _ _ Pl0 T A Ks _ _ _ R X h eR plg iso hpin hIs hplg hDiv heG ψ0 hψ0 π hπ red b hred hfix hw
  classical
  obtain ⟨P, hP⟩ := GlobalTheory.T.symmetricFrame_reduces_to_basis_mod_place D X h hpin b (fun kv => (hfix kv).1) hw π
  obtain ⟨ψ', a, hψ'1, hchi⟩ := GlobalTheory.T.star_character_eq_prod_additive_characters_root_alt D X h hpin hw
  have hsc : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ∃ d : Fin D.R.r → (ZMod (D.host.g kv.1))ˣ,
      ∀ u : GL (Fin D.R.r) (ZMod (D.host.g kv.1)), u ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k →
        ψ' kv (∑ i, ∑ j, if symEdge D.R.rS D.R.k i j then (a kv i j : ZMod (D.host.g kv.1)) * u.val i j else 0) =
          (ψ0 (plg kv)).compAddMonoidHom (iso kv).toAddMonoidHom
            (edgeSum (symEdge D.R.rS D.R.k) ((GlobalTheory.SeeConjRead.diagGL d)⁻¹ * u * GlobalTheory.SeeConjRead.diagGL d)) := by
    intro kv
    haveI := Fact.mk (D.host.g_prime kv.1)
    refine GlobalTheory.SeeConjScale.scale_conj (Field.toIsField _) D.R.rS D.R.k (ψ' kv) _ (hψ'1 kv) ?_ (a kv)
    intro h1
    apply hψ0 _ (plg kv).2
    ext y
    have := DFunLike.congr_fun h1 ((iso kv).symm y)
    simpa using this
  choose d hd using hsc
  let c : G0g D.nd := fun kv => P kv * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j))
  refine ⟨c, fun k hk => ?_⟩
  let Ns : G0g D.nd := fun kv => Units.map (Matrix.reindexAlgEquiv (ZMod (D.host.g kv.1)) (ZMod (D.host.g kv.1)) π.symm).toMonoidHom
    ((P kv)⁻¹ * red k kv * P kv)
  have hNs : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) = (((((P kv)⁻¹ * red k kv * P kv) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))).submatrix π π := by
    intro kv
    ext i j
    simp [Ns, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
  have hMat : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), GlobalTheory.Mem.SymFrame.IsMatIn X (D.naut.plGw kv.1 kv.2)
      (GlobalTheory.Mem.SymFrame.symVec X (D.naut.plGw kv.1 kv.2)) k (((Ns kv : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1)))) := by
    intro kv
    rw [hNs kv]
    exact GlobalTheory.Mem.SymFrame.isMatIn_perm _ k _ π (GlobalTheory.T.matrixModPlace_basisChange_eq_conj D X red b hfix kv (hw kv) (P kv) _ (hP kv) k hk)
  have hval : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), reord π (R.eG (eR.symm (c⁻¹ * red k * c))) (plg kv) =
      Formalism.UG.bc ((iso kv : ZMod (D.host.g kv.1) ≃+* kP (plg kv).1) : ZMod (D.host.g kv.1) →+* kP (plg kv).1)
        ((GlobalTheory.SeeConjRead.diagGL (d kv))⁻¹ * Ns kv * GlobalTheory.SeeConjRead.diagGL (d kv)) := by
    intro kv
    have e1 : (c⁻¹ * red k * c) kv = (GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)))⁻¹ *
        ((P kv)⁻¹ * red k kv * P kv) * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)) := by
      simp only [c, Pi.mul_apply, Pi.inv_apply, mul_inv_rev, mul_assoc]
    have e2 := heG (eR.symm (c⁻¹ * red k * c)) kv
    rw [MulEquiv.apply_symm_apply, e1] at e2
    apply Units.ext
    ext i j
    have e3 : ((reord π (R.eG (eR.symm (c⁻¹ * red k * c))) (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) :
        Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)) i j =
        ((R.eG (eR.symm (c⁻¹ * red k * c)) (plg kv) : GL (Fin D.R.r) (kP (plg kv).1)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (kP (plg kv).1)) (π i) (π j) := by
      simp [reord, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply]
    rw [e3, e2]
    show (iso kv) ((((GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)))⁻¹ *
        ((P kv)⁻¹ * red k kv * P kv) * GlobalTheory.SeeConjRead.diagGL (fun j => d kv (π.symm j)) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) (π i) (π j)) =
      (iso kv) (((((GlobalTheory.SeeConjRead.diagGL (d kv))⁻¹ * Ns kv * GlobalTheory.SeeConjRead.diagGL (d kv)) : GL (Fin D.R.r) (ZMod (D.host.g kv.1))) :
          Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g kv.1))) i j)
    rw [GlobalTheory.SeeConjRead.diagGL_conj_apply, GlobalTheory.SeeConjRead.diagGL_conj_apply, hNs kv]
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  have hmemiff : reord π (R.eG (eR.symm (c⁻¹ * red k * c))) ∈ (PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).H ↔
      ∀ kv : (Σ k : Fin 2, D.nd.PlG k), Ns kv ∈ unipSym (ZMod (D.host.g kv.1)) D.R.r D.R.rS D.R.k := by
    show _ ∈ Subgroup.pi Set.univ _ ↔ _
    rw [Subgroup.mem_pi]
    constructor
    · intro H kv
      have h1 := H (plg kv) (Set.mem_univ _)
      rw [hval kv, GlobalTheory.Mem.SymFrame.mem_unipSym_bc] at h1
      exact (GlobalTheory.SeeConjRead.unipSym_conj_iff _ _ _ _).2 h1
    · intro H PP _
      obtain ⟨kv, rfl⟩ := plg.surjective PP
      rw [hval kv, GlobalTheory.Mem.SymFrame.mem_unipSym_bc]
      exact (GlobalTheory.SeeConjRead.unipSym_conj_iff _ _ _ _).1 (H kv)
  have hK2 := GlobalTheory.T.mem_deeperLevel_iff_matrices_mod_place_symmetric D X h hpin hw k hk Ns hMat
  refine ⟨hK2.trans hmemiff.symm, fun hx => ?_⟩
  have hU := hmemiff.1 hx
  have hk2 : k ∈ X.K2 := hK2.2 hU
  rw [hchi k hk2 Ns hMat hU]
  have hchiv : (((PsharpSym R.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨_, hx⟩ : ℂˣ) : ℂ) =
      ∏ PP : R.Pg, ψ0 PP.1 (edgeSum (symEdge D.R.rS D.R.k) (reord π (R.eG (eR.symm (c⁻¹ * red k * c))) PP)) := by
    unfold PsharpSym LevelP.ofLocal
    rw [MonoidHom.finset_prod_apply, Units.coe_prod]
    rfl
  rw [hchiv]
  refine (Fintype.prod_equiv plg _ _ (fun _ => rfl)).symm.trans (Finset.prod_congr rfl fun kv _ => ?_)
  rw [hval kv, GlobalTheory.Mem.SymFrame.edgeSum_bc, hd kv _ (hU kv)]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetReductionFixedIffResiduesStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_reduction_fixed_iff_residues : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}, j + 1 = R.m → ∀ (p p' : PtAt R sel mu cst u j) (h : GLG X.E (R.N j) Pr.vGs), p'.1.1 = ((1 : UF X.E (R.N j)), h, (1 : GLQ X.E (R.N j) (QE sel (mu : Chr X.F X.E X.K)))) • p.1.1 → p'.1.2 = p.1.2 → ∀ (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P.1 → (cosetIn p' P = cosetIn p P ↔ ((h ⟨P.1, hP⟩ : GL (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) : Matrix (Fin (R.N j)) (Fin (R.N j)) (𝓞 X.E ⧸ P.1.asIdeal)) *ᵥ GlobalTheory.Mem.Col2.TypeRead.cvec p P = GlobalTheory.Mem.Col2.TypeRead.cvec p P) := by
  first | exact @GlobalTheory.Mem.Col2.TypeRead.cosetIn_smul_eq_iff | exact GlobalTheory.Mem.Col2.TypeRead.cosetIn_smul_eq_iff | (intros; apply GlobalTheory.Mem.Col2.TypeRead.cosetIn_smul_eq_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspFormTypeEqAtCorrespondingLifts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.R3.Rw

open Classical in

noncomputable def wtPre (P : Pre) (j : ℕ) (aP : Tau P.R → Fin (P.R.sigW j).1 → ℕ) (aM : Tau P.R → Fin (P.R.sigW j).2 → ℕ)
    (x : (P.host.E →+* ℂ) × ℕ) : ℕ :=
  ∑ t : Tau P.R, ((if x.1 = P.host.emb t.1 then Formalism.L2.Pj.ext0 (aP t) x.2 else 0) +
    if x.1 = ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (P.host.emb t.1) then Formalism.L2.Pj.ext0 (aM t) x.2 else 0)

theorem cusp_type_congr {P₁ P₂ : Pre} (hP : P₂ = P₁)
    {H₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host P₁.host.E} {H₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host P₂.host.E}
    {l₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₁} {l₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H₂}
    {c₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₁} {c₂ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l₂}
    {Dw₁ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₁} {Dw₂ : ℕ → ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H₂}
    {Xo₁ : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (Dw₁ j) l₁} {Xo₂ : ∀ j, ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli (Dw₂ j) l₂}
    {U₁ : ∀ j (σ : c₁.F →+* ℂ), Formalism.L2.Pj.Unf (Xo₁ j) c₁ σ P₁.R.r}
    {U₂ : ∀ j (σ : c₂.F →+* ℂ), Formalism.L2.Pj.Unf (Xo₂ j) c₂ σ P₂.R.r}
    {j₁ j₂ : ℕ} (hj : j₁ = j₂)
    {aP₁ : Tau P₁.R → Fin (P₁.R.sigW j₁).1 → ℕ} {aP₂ : Tau P₂.R → Fin (P₂.R.sigW j₂).1 → ℕ}
    {aM₁ : Tau P₁.R → Fin (P₁.R.sigW j₁).2 → ℕ} {aM₂ : Tau P₂.R → Fin (P₂.R.sigW j₂).2 → ℕ}
    {n₁ n₂ : ℕ} (hn : n₂ = n₁)
    (hH : HEq H₂ H₁) (hl : HEq l₂ l₁) (hc : HEq c₂ c₁) (hDw : HEq Dw₂ Dw₁) (hXo : HEq Xo₂ Xo₁) (hU : HEq U₂ U₁)
    (haP : HEq aP₂ aP₁) (haM : HEq aM₂ aM₁) :
    ↥(Formalism.L2.Pj.cusp (Xo₂ j₂) c₂ (U₂ j₂) (wtPre P₂ j₂ aP₂ aM₂) n₂) =
      ↥(Formalism.L2.Pj.cusp (Xo₁ j₁) c₁ (U₁ j₁) (wtPre P₁ j₁ aP₁ aM₁) n₁) := by
  subst hP hj hn
  cases hH; cases hl; cases hc; cases hDw; cases hXo; cases hU; cases haP; cases haM
  rfl

end GlobalTheory.Mem.R3.Rw

namespace GlobalTheory.Mem.R3.Rw

set_option maxHeartbeats 4000000 in

theorem Ext.cuspA_type_eq : ∀ {B₁ B₂ : Base} {f₁ : Fr B₁.toPre} {f₂ : Fr B₂.toPre} {T₁ : TwDat B₁} {T₂ : TwDat B₂} {w₁ : ColW B₁ f₁ T₁} {w₂ : ColW B₂ f₂ T₂} {Z₁ : w₁.Lt} {Z₂ : w₂.Lt} {h₁ : B₁.fields.Ok} {h₂ : B₂.fields.Ok} {W₁ : Set B₁.places.Pl} {W₂ : Set B₂.places.Pl} (z₁ : Dat (w₁.st Z₁) w₁.I h₁ T₁ W₁) (z₂ : Dat (w₂.st Z₂) w₂.I h₂ T₂ W₂), Enl B₁ B₂ → Ext z₁ z₂ → ∀ (i₁ : Fin (w₁.st Z₁).toD7.R.m) (i₂ : Fin (w₂.st Z₂).toD7.R.m), (i₁ : ℕ) = i₂ → ↥(z₂.core.cuspA ((i₂ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₂.geo.κ i₂)) (z₂.geo.κ i₂).n) = ↥(z₁.core.cuspA ((i₁ : ℕ) + 1) (Formalism.L2.Pj.wtA (z₁.geo.κ i₁)) (z₁.geo.κ i₁).n) := by
  intro B₁ B₂ f₁ f₂ T₁ T₂ w₁ w₂ Z₁ Z₂ h₁ h₂ W₁ W₂ z₁ z₂ hE hX i₁ i₂ hi
  have hk := hX.κ i₁ i₂ hi
  exact (cusp_type_congr hE.left (congrArg (fun x ↦ x + 1) hi) hk.right.right hX.H hX.l hX.c hX.Dw hX.Xo hX.U hk.left hk.right.left)

end GlobalTheory.Mem.R3.Rw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleStepsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteOrder_charts_middle_steps : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (i : ℕ) (hi : i ≤ B.R.m), 1 ≤ i → i < B.R.m → (∀ v, v ∈ Q ↔ I.UnderQ a v) → ∀ k : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → GA B (B.R.N i), GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k → ∃ K : ∀ β : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i, LevelChart (I.rec7 l Z) (B.T u) (badQ (I.rec7 l Z) Q) i hi (fun c : {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)), I.Reads u a i (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i) (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi) (fun c => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1) (fun c s => ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1) k ∧ ∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1 := by
  first | exact @GlobalTheory.Mem.Col2.ChExM.exists_charts | exact GlobalTheory.Mem.Col2.ChExM.exists_charts | (intros; apply GlobalTheory.Mem.Col2.ChExM.exists_charts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntermediateCoefficientPlaceBetween
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

namespace GlobalTheory.Mem.Top.Bl

theorem exists_below_between : ∀ (D₁ D₂ D₃ : Formalism.BasicNotions.D7), Set.range D₂.what₂.embLL ⊆ Set.range D₃.what₂.embLL → ∀ (v₁ : D₁.what₂.places.Pl) (v₃ : D₃.what₂.places.Pl), GlobalTheory.Mem.Top.Bl.Below D₁ D₃ v₁ v₃ → ∃ v₂ : D₂.what₂.places.Pl, GlobalTheory.Mem.Top.Bl.Below D₁ D₂ v₁ v₂ ∧ GlobalTheory.Mem.Top.Bl.Below D₂ D₃ v₂ v₃ := by
  intro D₁ D₂ D₃ hR v₁ v₃ h13

  have hmem : ∀ x : D₂.what₂.LL, D₂.what₂.embLL x ∈ D₃.what₂.embLL.fieldRange := fun x => by
    obtain ⟨y, hy⟩ := hR ⟨x, rfl⟩
    exact ⟨y, hy⟩
  let ι : D₂.what₂.LL →+* D₃.what₂.LL :=
    (D₃.what₂.embLL.rangeRestrictFieldEquiv).symm.toRingHom.comp (D₂.what₂.embLL.codRestrict _ hmem)
  have hι : ∀ x, D₃.what₂.embLL (ι x) = D₂.what₂.embLL x := fun x => by
    have := (D₃.what₂.embLL.rangeRestrictFieldEquiv).apply_symm_apply ⟨D₂.what₂.embLL x, hmem x⟩
    exact congrArg Subtype.val this
  let ιO : 𝓞 D₂.what₂.LL →+* 𝓞 D₃.what₂.LL := RingOfIntegers.mapRingHom ι
  have hιO : ∀ x : 𝓞 D₂.what₂.LL, ((ιO x : 𝓞 D₃.what₂.LL) : D₃.what₂.LL) = ι (x : D₂.what₂.LL) := fun x => rfl
  set Q := (D₃.plEq v₃).asIdeal with hQ
  let P : Ideal (𝓞 D₂.what₂.LL) := Q.comap ιO
  have hPprime : P.IsPrime := Ideal.comap_isPrime ιO Q
  have hQne : Q ≠ ⊥ := (D₃.plEq v₃).ne_bot
  have hn : Ideal.absNorm Q ≠ 0 := by
    intro h; exact hQne (Ideal.absNorm_eq_zero_iff.mp h)
  have hPne : P ≠ ⊥ := by
    intro h
    have hin : ((Ideal.absNorm Q : ℕ) : 𝓞 D₂.what₂.LL) ∈ P := by
      show ιO _ ∈ Q
      rw [map_natCast]; exact Ideal.absNorm_mem Q
    rw [h, Ideal.mem_bot] at hin
    exact hn (by exact_mod_cast hin)
  refine ⟨D₂.plEq.symm ⟨P, hPprime, hPne⟩, ?_, ?_⟩
  · intro x₁ x₂ hx
    rw [Equiv.apply_symm_apply]
    show x₁ ∈ (D₁.plEq v₁).asIdeal ↔ ιO x₂ ∈ Q
    exact h13 x₁ (ιO x₂) (by rw [hιO, hι]; exact hx)
  · intro x₂ x₃ hx
    rw [Equiv.apply_symm_apply]
    show ιO x₂ ∈ Q ↔ x₃ ∈ Q
    have : ιO x₂ = x₃ := by
      apply Subtype.ext
      apply D₃.what₂.embLL.injective
      show D₃.what₂.embLL (ι (x₂ : D₂.what₂.LL)) = _
      rw [hι]; exact hx
    rw [this]

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelChainOverTopSpacesStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelChain_over_top_spaces : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (b : Bool) (m : D.what₂.Tup → Mat1 D.what₂.LL G) (s : D.what₂.Tup → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tA : ∀ μ, Tie1 D.what₂.embLL (m μ) (s μ)) (hA : ∀ t, m (y.tup t) = rMat A3.A (levP F.lv2 b).1 (levP F.lv2 b).2 t), ∃ c : ChD D.what₂.Tup Φ D.R.m fun μ => (s μ).A, Nonempty (ChT y F.lv2 b rep (Top := fun μ => (s μ).A) (fun t x => ((tA (y.tup t)).cast (hA t)).j x) c) := by
  first | exact @GlobalTheory.Mem.R3.Rw.ChainLevel.chain_exists | exact GlobalTheory.Mem.R3.Rw.ChainLevel.chain_exists | (intros; apply GlobalTheory.Mem.R3.Rw.ChainLevel.chain_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLevelElementSameCharacterNearBadStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_levelElement_same_character_near_bad : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl), ChiFin I l Z (K (chOf c)).lev → ∀ κ : (K (chOf c)).lev.U, ∃ x : (K (chOf c)).lev.U, (K (chOf c)).lev.chi x = (K (chOf c)).lev.chi κ ∧ (∃ q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i, PtOf ((show GA B (B.R.N i) from ((K (chOf c)).y ⟨c, rfl⟩).1) * (show GA B (B.R.N i) from x.1) * k (chOf c)) q) ∧ ∀ P : SBof I a, GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((I.cst a).D P) (κ.1⁻¹ * x.1) := by
  first | exact @GlobalTheory.Mem.Col2.AdT.LevelElt.exists_level_elt | exact GlobalTheory.Mem.Col2.AdT.LevelElt.exists_level_elt | (intros; apply GlobalTheory.Mem.Col2.AdT.LevelElt.exists_level_elt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLiftSpacesOverDefiniteFormsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_spaces_over_definite_forms : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd), (∀ o : D.what₂.O, ∃ k : Ks, algebraMap Ks D.what₂.LL k = D.what₂.OtoLL o) → Inputs D → Pins R F cG → Holds R F → ∀ (y : Hd R.toRealDat), ∀ (Φ : Type) (rep : Φ → Formalism.L2.NG.FinTyp D.host.E D.R.r), Reps y F.lv2 rep → ∀ (m : D.what₂.Tup → ℕ → Mat1 D.what₂.LL G) (s : D.what₂.Tup → ℕ → Sp1 D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) G) (tL : ∀ μ j, Tie1 D.what₂.embLL (m μ j) (s μ j)) (hL : ∀ (i : Fin D.R.m) t, m (y.tup t) ((i : ℕ) + 1) = lMat A3.A F.lv2.P0 F.lv2.ψ0 i t), ∃ l : LfD D.what₂.O (D.what₂.embLL.comp D.what₂.OtoLL) D.what₂.Tup Φ fun μ j => (s μ j).A, Nonempty (LfT y F.lv2 rep (Mt := fun μ j => (s μ j).A) (fun i t x => ((tL (y.tup t) ((i : ℕ) + 1)).cast (hL i t)).j x) l) := by
  first | exact @GlobalTheory.LiftSpaces.exists_lift_spaces | exact GlobalTheory.LiftSpaces.exists_lift_spaces | (intros; apply GlobalTheory.LiftSpaces.exists_lift_spaces <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStandardFormComparisonSymmetricLevelMemberStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_standardFormComparison_symmetricLevel_members : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∃ (Ch : B.Word → ℕ → Type) (chOf : ∀ u i, ((I.rec7 l Z).mem u).C.cls i → Ch u i) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (Ch u) (chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) ∧ (∀ u i, Finite (Ch u i)) ∧ (∀ u, Nonempty (Unique (Ch u B.R.m))) ∧ (∀ u u', (F u).gl = (F u').gl) ∧ CharacterCompatible (F B.u₀).gl B.R.m := by
  first | exact @GlobalTheory.Mem.FormSym.formsTiedSym_std | exact GlobalTheory.Mem.FormSym.formsTiedSym_std | (intros; apply GlobalTheory.Mem.FormSym.formsTiedSym_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KernelEntriesFormTrueChainsStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelEntries_form_true_chains : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ (c : ((I.rec7 l Z).chTw u μ).cls i) (c' : ((I.rec7 l Z).chTw u μ).cls (i + 1)) (v : ValQ O u μ i) (v' : ValQ O u μ (i + 1)), evC O u μ (i + 1) v' = ((I.rec7 l Z).chTw u μ).Kmap i c c' (evC O u μ i v) → ∀ J, prTC Pl O Bs u μ w i c' v' J = unC Pl O Bs u μ w i c c' * prSC Pl O Bs u μ w i c v (KM.applyAt0 ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) ((I.rec7 l Z).what₂.places.resChar w) (thAtW Pl O Bs u μ w i c c') (KM.Gxz ((I.rec7 l Z).R.N i) ((I.rec7 l Z).R.N (i + 1)) (nuD (I.rec7 l Z) u i) J)) := by
  first | exact @GlobalTheory.Mem.Col2.TC.kerEnt_kform_true | exact GlobalTheory.Mem.Col2.TC.kerEnt_kform_true | (intros; apply GlobalTheory.Mem.Col2.TC.kerEnt_kform_true <;> assumption)
end

