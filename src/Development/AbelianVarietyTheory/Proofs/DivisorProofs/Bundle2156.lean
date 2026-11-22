import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2145
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2140
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1969
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1834
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemRangeSrcForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2088
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2131
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactDefiniteUnitaryRestrictedProductStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_definiteUnitary_restricted_product : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ C : ∀ w : Pl E, Set (UL n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w = KL n w) → IsCompact {x : finU E n | ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) ∈ C w} := by
  first | exact @GlobalTheory.BCT.LocCpt.loc_cpt | exact GlobalTheory.BCT.LocCpt.loc_cpt | (intros; apply GlobalTheory.BCT.LocCpt.loc_cpt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHeckeProductOfLocalTestFunctionsSection
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.GlobHecke

theorem isHecke_globFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n →
    ∀ (S : Set (Pl E)), IsSection S → ∀ (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f →
    IsHecke (globLev S K') (globFn S f) := by
  intro E _ _ _ hU n _ S hS K' hK' f hf
  refine ⟨?_, globFn_inv S K' f fun w => (hf.1 w).2⟩
  have hC : ∀ᶠ w in cofinite, tsupport (f w) = (KL n w : Set (UL n w)) := by
    filter_upwards [hK'.2, hf.2] with w h1 h2
    have ho : IsOpen (KL n w : Set (UL n w)) := h1 ▸ (hK'.1 w).1
    have hc : IsClosed (KL n w : Set (UL n w)) := Subgroup.isClosed_of_isOpen _ ho
    rw [h2, tsupport, Set.support_indicator]
    have : Function.support (1 : UL n w → ℂ) = Set.univ := by
      ext x; simp
    rw [this, Set.inter_univ, hc.closure_eq]
  have hcpt := GlobalTheory.BCT.LocCpt.loc_cpt E hU n S hS (fun w => tsupport (f w)) (fun w => (hf.1 w).1) hC
  refine HasCompactSupport.intro hcpt fun x hx => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨w, hw, hxw⟩ := hx
  have hfin : (S ∩ Function.mulSupport fun w : Pl E => f w (toSub (UL n w) (cLoc w (x : UA E n)))).Finite := by
    have h := (GlobalTheory.BCT.LocAE.eventually_mem_KL E hU n x).and hf.2
    rw [Filter.eventually_cofinite] at h
    refine h.subset ?_
    rintro u ⟨-, hu⟩ ⟨h1, h2⟩
    apply hu
    show f u _ = 1
    rw [h2, Set.indicator_of_mem (show _ ∈ (KL n u : Set (UL n u)) from h1)]
    rfl
  unfold globFn
  rw [finprod_mem_eq_prod _ hfin]
  have h0 : f w (toSub (UL n w) (cLoc w (x : UA E n))) = 0 := image_eq_zero_of_notMem_tsupport hxw
  refine Finset.prod_eq_zero (i := w) ?_ h0
  rw [Set.Finite.mem_toFinset]
  refine ⟨hw, ?_⟩
  show f w _ ≠ 1
  rw [h0]
  exact zero_ne_one

end GlobalTheory.BCT.GlobHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelComponentTransportCompStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLevelComponentTransport_comp : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ γ' : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k₁ k₂ : (uAt r v i).Comp) (a a' : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ' k k₁ a' → IsTransp p r i v ψ γ k₁ k₂ a → IsTransp p r i v ψ (γ' * γ) k k₂ (a * a') := by
  first | exact @GlobalTheory.ShareOn.isTransp_comp | exact GlobalTheory.ShareOn.isTransp_comp | (intros; apply GlobalTheory.ShareOn.isTransp_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelAtFittedPoints
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain
open Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim

namespace GlobalTheory.BigTop.Fun
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem ker_eq_of_formula {p : PtAt ex Csz} (hp : p.Rows) (hD : 0 < (Df p).dQ p.P.A3.fam3.base3.μ0)
    (hPq : Function.Surjective ((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec)
    {CF : ℝ} (d : FunIn p CF) (a : SlopeTestRemainingChoices p d.G d.W d.n) (h : TieAt d a)
    (hI : ∀ u, (∀ i, psiK a.ch i u = 0) → u = 0) (hC : ∀ i j t, a.ch.c i j t ≠ 0)
    (hF : ∃ κ ze, FormulaAt a.ch κ ze) :
    LinearMap.ker (d.V p.P.A3.fam3.base3.μ0).mulVecLin = (Df p).U p.P.A3.fam3.base3.μ0 := by
  obtain ⟨κ, ze, hz, hf⟩ := hF
  have hc : cTot a.ch p.P.A3.fam3.base3.μ0 ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => Finset.prod_ne_zero_iff.2 fun j _ => hC i j _
  have hze : D.what₂.embLL (ze p.P.A3.fam3.base3.μ0) ≠ 0 := by
    obtain ⟨n, hn, e⟩ := hz p.P.A3.fam3.base3.μ0
    refine (map_ne_zero _).2 fun z => ?_
    rw [z, zero_pow hn.ne'] at e
    exact zero_ne_one e
  have hinj := (GlobalTheory.T.injective_iC_rows p hp).1
  have key : ∀ y, p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) = 0 ↔
      ((Df p).Pq p.P.A3.fam3.base3.μ0).mulVec y = 0 := by
    intro y
    have e := GlobalTheory.T.theta_eV0_eq_iC_Pq_rows p hp p.P.A3.fam3.base3.μ0 y
    change p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) = _ at e
    rw [e]
    constructor
    · intro h0
      have h1 := hinj (h0.trans (map_zero _).symm)
      funext i
      exact p.P.A3.fam3.base3.v0.embedding.injective (by simpa [cpt] using congrFun h1 i)
    · intro h0
      rw [h0]
      have : cpt p.P.A3.fam3.base3.v0.embedding (0 : Fin ((Df p).dQ p.P.A3.fam3.base3.μ0) → D.what₂.LL) = 0 := by
        funext i; simp [cpt]
      rw [this, map_zero]
      rfl
  have hκ : κ ≠ 0 := by
    obtain ⟨y, hy⟩ := hPq (Pi.single ⟨0, hD⟩ 1)
    have hne : p.R.Th p.P.A3.fam3.base3.μ0 (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y)) ≠ 0 := fun h0 => by
      have h2 := congrFun ((key y).1 h0) ⟨0, hD⟩
      rw [hy] at h2
      simp at h2
    obtain ⟨i, hi⟩ : ∃ i, psiK a.ch i (p.R.Th p.P.A3.fam3.base3.μ0
        (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y))) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hne (hI _ hall)
    exact FormulaAt.ne_zero ⟨hz, hf⟩ hc (GlobalTheory.T.eV0_mem_goodF_rows p hp _ y) hi
  ext y
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, DefSide.U]
  rw [← key y]
  constructor
  · intro h0
    apply hI
    intro i
    have e := hf p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) (GlobalTheory.T.eV0_mem_goodF_rows p hp _ y) i
    have hs := h.sums p.P.A3.fam3.base3.μ0 (Or.inl rfl) y i
    have hv : vK a.ch p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) i = 0 :=
      hs.symm.trans (by rw [h0]; exact map_zero _)
    have e2 := e.trans (by rw [hv, mul_zero])
    exact ((mul_eq_zero.1 e2).resolve_left (mul_ne_zero hze hc))
  · intro h0
    funext i
    have e := hf p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y) (GlobalTheory.T.eV0_mem_goodF_rows p hp _ y) i
    have hs := h.sums p.P.A3.fam3.base3.μ0 (Or.inl rfl) y i
    have hz0 : psiK a.ch i (p.R.Th p.P.A3.fam3.base3.μ0
        (p.R.jX p.P.A3.fam3.base3.μ0 (eV0 p p.P.A3.fam3.base3.μ0 y))) = 0 := by
      rw [h0]; exact psiK_zero _ _
    rw [hz0, mul_zero, ← hs] at e
    have h3 := (mul_eq_zero.1 e.symm).resolve_left hκ
    exact D.what₂.embLL.injective (by rw [h3]; exact (map_zero _).symm)

theorem ker_tie : Bundle → SetAt → LinK → InjK → ConstK → Formula2K → Ker @Comparison₂ := by
  intro hB hS _ hI hC hF
  obtain ⟨CF0, hA⟩ := hS.atPt (hI.and (hC.and hF))
  refine ⟨CF0, fun CF hCF => (hA CF hCF).imp fun Fm CH _ e _ => ⟨0, fun C _ => evPt_imp e fun x hx i p hp b d hd => ?_⟩⟩
  obtain ⟨-, a, ha⟩ := hd
  obtain ⟨q1, q2, q3⟩ := b d.G d.W d.n a ha.ok
  obtain ⟨wf, R0, hR⟩ := hB p hp
  have h0 : 0 < (p.S false).D := hR ▸ R0.D_pos
  have v : d.O.vmu p.P.A3.fam3.base3.μ0 = d.V p.P.A3.fam3.base3.μ0 := by
    show (1 : _)⁻¹ • _ = _
    rw [inv_one]
    exact one_smul _ _
  show LinearMap.ker (d.O.vmu _).mulVecLin = _
  rw [v]
  exact ker_eq_of_formula hp h0 (wf.Pq_surj _) d a ha q1 (fun i j t => (q2 i j t).2) (q3 ha.ok.field)

end GlobalTheory.BigTop.Fun
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLinkOfSurvivingSimpleSubquotientStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latticeLink_of_surviving_simple_subquotient : ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω], GlobalTheory.Published.ChebotarevDegreeOne → ∀ (l : ℕ) [Fact l.Prime] (ι : Type) [Fintype ι] [DecidableEq ι] (inc : ι → (E →+* PadicAlgCl l)) (fr : ℕ → ι → ι) (cjj : ℕ → ι → Bool) (P : Par) (W : Wts ι), (∀ mu : ι → ℕ → ℕ, Linked l P.Nr W.lam mu → BlockFor Ω inc P W mu → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ))) → ∀ (F : Frame l ι P.Nr), F.Ok → ∀ (Bk : (F.I → PadicAlgCl l) → Prop), GalSide Ω inc P W F Bk → ∀ (jK : F.K →* alg F.O P.Nr W.lam), F.IsJ W.lam jK → ∀ (ϖ : F.O), Irreducible ϖ → ϖ ∣ ((l : ℕ) : F.O) → (∀ τ, Antitone (res P.Nr (W.lam τ))) → ∀ (Gm : Type) [AddCommGroup Gm] [Module F.O Gm] [Module (alg F.O P.Nr W.lam) Gm] [IsScalarTower F.O (alg F.O P.Nr W.lam) Gm] [Module F.T (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)], F.IsHecke W.lam jK Gm → IsSimpleModule (alg F.O P.Nr W.lam) Gm → SubQ F.O P.Nr W.lam ϖ Gm → ∀ (mu : ι → ℕ → ℕ), (∀ τ, Antitone (res P.Nr (mu τ)) ∧ ∑ a : Fin P.Nr, mu τ a = ∑ a : Fin P.Nr, W.lam τ a ∧ (∀ a : Fin P.Nr, W.lam τ (P.Nr - 1) ≤ mu τ a ∧ mu τ a ≤ W.lam τ 0)) → Embeds F.O P.Nr W.lam mu ϖ Gm → ∀ (m : Ideal F.T) [m.IsMaximal] (θ0 : F.I → PadicAlgCl l), F.IsEig W.lam θ0 → Bk θ0 → F.Over θ0 m → ¬ Subsingleton (LocalizedModule m.primeCompl (Forms F.O (A := alg F.O P.Nr W.lam) F.Γ jK Gm)) → ∀ τ, LatticeLink P (reFr W fr cjj) l τ (res P.Nr (mu τ)) := by
  first | exact @GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving | exact GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving | (intros; apply GlobalTheory.ExpFrame.LinkQ.latticeLink_of_surviving <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeVacuumEqSmulIndicatorSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.VacShape

theorem vacuum_eq_smul_indicator : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om')
    (L₁ : Submodule (𝓞 D.host.E) (Fin a' → D.host.E)) (L₂ : Submodule (𝓞 D.host.E) (Fin (a + a') → D.host.E))
    (θ : 𝓞 D.host.E) (hθ : (θ : D.host.E) + D.sp.cm.sig θ = 1)
    (φ₀ : (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) (h0 : φ₀ ∈ GlobalTheory.WeilM.SB _) (hne : φ₀ ≠ 0)
    (hfix : (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) φ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • φ₀)))
    (huniq : ∀ ψ₀ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁), (∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV {Γ.V' with L := L₁} {Γ.W with L := L₂} Bs.v₁,
          GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (evFin D.host.F Bs.v₁) (Γ.M'.co.rho Bs.ψ γ) ψ₀
            (Bs.ψ (⅟(2 : AF D.host.F) * symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (inclR (F := D.host.F) (AF D.host.F) (θ : D.host.E))
              (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.V'.J) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM D.host.F Γ.W.J) γ γ) • ψ₀)) → ∃ c : ℂ, ψ₀ = c • φ₀),
    ∃ (ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ))
      (P : GL (Fin a') (Fv D.host.F Bs.v₁)) (Λ : Submodule 𝒪[Fv D.host.F Bs.v₁] (Fin (a + a') → Fv D.host.F Bs.v₁)) (c : ℂ),
      Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι ∧ ∀ Y, ι φ₀ Y = c * (matLat (Fin a') Λ : Set _).indicator 1 (P.val * Y) := by
  intro D a a' Bs Γ X om om' hTr L₁ L₂ θ hθ φ₀ h0 hne hfix huniq
  obtain ⟨ι, hι⟩ := GlobalTheory.T.exists_linearModel_intertwiner_goodSplitPlace Bs Γ X om om' hTr
  have hfSB : ι φ₀ ∈ GlobalTheory.WeilM.SB _ := hι.bij.mapsTo h0
  have hf0 : ι φ₀ ≠ 0 := by
    intro h
    apply hne
    refine hι.bij.injOn h0 (zero_mem _) ?_
    rw [h, map_zero]
  have hinv : ∀ s ∈ GlobalTheory.VacShape.Sa Bs Γ L₁ L₂, ∀ Y, ι φ₀ (Y + s) = ι φ₀ Y := by
    rintro _ ⟨u, hu, hu0, rfl⟩ Y
    have hat := (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1 u hu
    have hA := hfix u hu
    rw [GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hat (Or.inl hu0), mul_zero, AddChar.map_zero_eq_one, one_smul] at hA
    exact (hι.trans u hat hu0 φ₀ h0 φ₀ h0 hA Y).symm
  have hsupp : ∀ Y ∉ GlobalTheory.VacShape.Bd Bs Γ L₁ L₂, ι φ₀ Y = 0 := by
    intro Y hY
    simp only [GlobalTheory.VacShape.Bd, Set.mem_setOf_eq, not_forall] at hY
    obtain ⟨x, hx, hx0, rfl, u, hu, hu0, hne1⟩ := hY
    have hat := (GlobalTheory.LatVac.latAtV_at_stable _ _ _).1 u hu
    have hB := hfix u hu
    rw [GlobalTheory.T.traceSymplectic_self_zero_splitSupported Bs Γ X om om' hTr u hat (Or.inr hu0), mul_zero, AddChar.map_zero_eq_one, one_smul] at hB
    have hm := hι.mult u hat hu0 φ₀ h0 φ₀ h0 hB x hx hx0
    by_contra h
    exact hne1 ((mul_eq_right₀ h).mp hm.symm)
  obtain ⟨c, hc, hop, hcp⟩ := GlobalTheory.T.schwartzBruhat_matrices_invariant_supported_eq_smul Bs.v₁ _ _ (GlobalTheory.T.latticePairingTrivialMatrices_sub_mem Bs Γ X om om' hTr L₁ L₂) (ι φ₀) hfSB hf0 hinv hsupp
    (GlobalTheory.T.schwartzBruhat_invariant_supported_eq_smul_vacuum Bs Γ X om om' hTr L₁ L₂ θ hθ ι hι φ₀ h0 hne hfix huniq)
  obtain ⟨P, Λ, hPΛ⟩ := GlobalTheory.T.closure_vanishing_lattice_eq_row_lattice_matrices Bs Γ X om om' hTr L₁ L₂ hop hcp
  refine ⟨ι, P, Λ, c, hι, fun Y => ?_⟩
  have hY := congrFun hc Y
  rw [Pi.smul_apply, smul_eq_mul] at hY
  rw [hY]
  congr 1
  by_cases h : Y ∈ closure (GlobalTheory.VacShape.Sa Bs Γ L₁ L₂ : Set _)
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show P.val * Y ∈ (matLat (Fin a') Λ : Set _) from (hPΛ Y).1 h)]
    rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show P.val * Y ∉ (matLat (Fin a') Λ : Set _) from fun h' => h ((hPΛ Y).2 h'))]

end GlobalTheory.VacShape

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelComponentTransportReadsCuspFormsConstMulStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelComponentTransport_reads_cuspForms_const_mul : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' : (uAt r v i).Comp) (a : GL (Fin D.R.r) D.host.E), IsTransp p r i v ψ γ k k' a → ∃ c : ℂˣ, ∀ (F : (recB (h.laws v).p.toLawsCore).Cusp ((i : ℕ) + 1) (p.κ i)) (x : Frame ((uAt r v i).X k).Ψ D.R.r), x ∈ ((uAt r v i).X k).dom → ∀ (h2 : ((uAt r v i).X k).Ψ = ((uAt r v i).X k').Ψ), rdU (uAt r v i) (actLev (Xo := p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c (levFull (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) γ F.1) k x = (c : ℂ) * rdU (uAt r v i) F.1 k' (castFrame h2 (lact a x)) := by
  first | exact @GlobalTheory.ShareOn.transp_reads_const_mul | exact GlobalTheory.ShareOn.transp_reads_const_mul | (intros; apply GlobalTheory.ShareOn.transp_reads_const_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelZeroLiftExists
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TieLift

theorem lift_principal : AtTw fun Fm x hx i p w j => ∀ g0 : G0 (R2 p).Pg (Fm.D x i).R.r,
    ∃ κ', Formalism.IndefR.Lev.IsLevelLift (Wc (Fm.D x i) j) ((R2 p).βW j) ((R2 p).datWp j (R2 p).triv) g0 κ' :=
  AtTw.of_forall fun Fm x hx i p hr hm w hw j g0 =>
    GlobalTheory.GalLift.Transl.lifts (R2 p) j (GlobalTheory.BigOn.links2_of_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1).1.lev g0

end GlobalTheory.TieLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelCompactIntertwines
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.DblScal in
theorem GlobalTheory.DblScal.scalW_main : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), ∀ ι, M.IsLinW B.ψ t b c ι →
    ∀ κ : UA σ W.J → ℂ, (∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB (Fin n × Fin d → Fv F v), ∀ φ₁ ∈ SB (Fin n × Fin d → Fv F v),
      Acts (evFin F v) (om (1, h)) φ φ₁ → ι φ₁ = κ h • fun Y => ι φ (Y * (GlobalTheory.SplitFlip.invT (locMat t c h)).val)) →
    ∀ h ∈ UAt σ W (evFin F v), κ h = (chrW χX t (GlobalTheory.SplitFlip.gdet (locMat t c h)) : ℂ) *
      GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet (locMat t c h)) (-(n : ℂ) / 2) := by
  intro hPr F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP v t b c ι hι κ hκ h hh
  obtain ⟨⟨-, dd, omd, hdc, hws, hbox⟩, -, -⟩ := hP.weil
  have hspl := hws.2.1
  have hloc := GlobalTheory.T.double_splitting_pair_identity hPr F E σ B n d X W M χX χW om r s r' s' hP dd omd hspl v
  obtain ⟨ιd, hιd, hprod⟩ := GlobalTheory.T.linear_model_double_splitting hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c ι hι dd hdc
  obtain ⟨cd, hcd⟩ := GlobalTheory.T.double_scaling_local_identity hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hspl hloc ιd hιd
  obtain ⟨χd, hχd⟩ := GlobalTheory.T.double_scaling_local_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hspl hloc ιd hιd cd hcd
  obtain ⟨gd, hgd⟩ := exists_diag_one h
  have hgdAt : gd ∈ UDAt σ W.J (evFin F v) := by
    intro u hu
    change u • (((gd : GL (Fin d ⊕ Fin d) (AE F E)) : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) (AE F E)) - 1) = 0
    have h1 : u • (mat h - 1) = 0 := hh u hu
    rw [hgd, fromBlocks_sub_one, Matrix.fromBlocks_smul, h1]
    simp
  have e1 : κ h = cd gd := GlobalTheory.T.linear_model_compact_equivariance hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c ι hι κ hκ dd omd hdc hspl
    (fun g gd' hg φ₁ hφ₁ φ₂ hφ₂ => hbox g gd' hg φ₁ hφ₁ φ₂ hφ₂) hloc ιd hιd hprod cd hcd h hh gd hgd
  obtain ⟨p, hpAt, hp⟩ := GlobalTheory.T.double_scaling_iwasawa_decomposition F E σ B n d X W M χX χW om r s r' s' hP v t c (fixDiag (locMat t c h))
  have e5 := GlobalTheory.T.double_scaling_local_vanishing hPr F E σ B n d X W M χX χW om r s r' s' hP v t b c dd omd hdc hws hloc ιd hιd cd hcd p hpAt
    ⟨1, by rw [hp]; exact fixDiag_diag _⟩
  rw [hp, gdet_fixDiag] at e5
  have f1 : cd gd = χd (GlobalTheory.SplitFlip.gdet (locMat t c h)) := by rw [hχd gd hgdAt, gdet_locMatD_diag t c h gd hgd]
  have f2 : cd p = χd (GlobalTheory.SplitFlip.gdet (locMat t c h)) := by rw [hχd p hpAt, hp, gdet_fixDiag]
  rw [e1, f1, ← f2]
  exact e5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisDualBasisEmbeddedLatticeStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBasis_dualBasis_embeddedLattice : ∀ (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] (ι : Type) [Fintype ι] (n : ℕ) (emb : ι → E →+* K) (τ : ι) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ), l.Prime → ((l : ℕ) : 𝓞 K) ∈ w.asIdeal → ∀ (M : Submodule (𝓞 E) (Fin n → E)), Submodule.IsLattice E M → (∃ B, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B) ∧ Submodule.IsLattice K (dualFr (tauLat emb τ M)) ∧ ∀ B : GL (Fin n) E, Formalism.L2.Forms.IsLocBasis l (M : Set (Fin n → E)) B → IsBasisAt w (dualFr (tauLat emb τ M)) (inside₂ K n (Matrix.GeneralLinearGroup.map (emb τ) B)) := by
  first | exact @GlobalTheory.LocBasisDual.basisAt_dualFr_tauLat | exact GlobalTheory.LocBasisDual.basisAt_dualFr_tauLat | (intros; apply GlobalTheory.LocBasisDual.basisAt_dualFr_tauLat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalBasisIntegralRelativeAdelicPointStatement
section
open NumberField IsDedekindDomain
open scoped TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.FrameOf
open Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LD Formalism.GradedWeylDivisibility MvPolynomial
open GlobalTheory.FrameRead
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localBasis_integral_relative_adelicPoint : ∀ {D : D7} (V : Formalism.BasicNotions.TH.HSp D) (l : ℕ) [Fact l.Prime] (inc : D.host.E →+* PadicAlgCl l) (ev : FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E →+* PadicAlgCl l), EvOk inc ev → V.L0 = Submodule.span (𝓞 D.host.E) (Set.range V.frame) → ∀ (y : Bridge.Gf V) (B : GL (Fin V.rank) D.host.E), Formalism.L2.Forms.IsLocBasis l (Bridge.hLat V y : Set (Fin V.rank → D.host.E)) B → ∀ a b, ‖((Matrix.GeneralLinearGroup.map ev (y : GL (Fin V.rank) (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E)))⁻¹ * Matrix.GeneralLinearGroup.map inc B).val a b‖ ≤ 1 := by
  first | exact @GlobalTheory.LocBasisInt.locBasis_integral | exact GlobalTheory.LocBasisInt.locBasis_integral | (intros; apply GlobalTheory.LocBasisInt.locBasis_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixRowSubstitutionPolyDiagonalEqSumComponentsStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility GlobalTheory.GenCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrixRowSubstitutionPoly_diagonal_eq_sum_components : ∀ (O : Type) [CommRing O] (N : ℕ) (R : Type) [CommRing R] [Algebra O R] (d : Fin N → R) (D : ℕ) (f : MvPolynomial (Fin N × Fin N) O), f.totalDegree ≤ D → rowSubst O N R (Matrix.diagonal d) f = ∑ w ∈ Fintype.piFinset (fun _ : Fin N => Finset.range (D + 1)), (∏ a, d a ^ w a) • MvPolynomial.map (algebraMap O R) (weightedHomogeneousComponent (rowW N N) w f) := by
  first | exact @GlobalTheory.DiagRowSubst.rowSubst_diagonal_eq_sum_components | exact GlobalTheory.DiagRowSubst.rowSubst_diagonal_eq_sum_components | (intros; apply GlobalTheory.DiagRowSubst.rowSubst_diagonal_eq_sum_components <;> assumption)
end

