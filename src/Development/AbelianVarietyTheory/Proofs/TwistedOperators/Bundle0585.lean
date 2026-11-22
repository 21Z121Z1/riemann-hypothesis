import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0490
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSquareProductRouteBEqExternalProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1871
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1553
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0376
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0019
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VGeIffExtended
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsPullByEndOfPullRel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0566
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRouteKernelEqCharMulThetaKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.SquareDict

theorem isThetaFunO_small_of_isMatched {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hM : IsMatched B t ρ i j Θ Θ') :
    ∀ d ∈ Θ'.support, IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 ∧
      IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hM
  intro d hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hd)
  obtain ⟨d₀, hd₀, hd₁⟩ := Finset.mem_biUnion.mp (Finsupp.support_sum hP)
  obtain rfl := Finset.mem_singleton.mp (Finsupp.support_single_subset hd₁)
  obtain ⟨hA, hB⟩ := hloc d₀ hd₀
  have hv₁ := (ρ.vT_is t i j i.2.le j.2).2.theta
  have hv₂ := (ρ.vX_is i j i.2 j.2.le).2.theta
  have hf₁ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hA.2 hv₁
  have hf₂ := GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is hB.2 hv₂
  exact ⟨GlobalTheory.FockTheta.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ _ P.1.2 hf₁,
    GlobalTheory.FockTheta.ptStable D W.ψ W.θ W.ψ_std W.θ_is _ _ _ _ _ _ _ P.2 hf₂⟩

theorem kerSmall_eq_thetaKO : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωB : GlobalTheory.Grid.WRep (G.V (.grid ↑i ↑j)) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ false _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ωB →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerSmall W Θ' g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωB u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumB W Θ') := by
  intro D T L sc G μ₀ hL W t i j ωB hωB B ρ Θ Θ' hM g g₁ u
  have hth := isThetaFunO_small_of_isMatched W B ρ t i j Θ Θ' hM
  have hω := (GlobalTheory.Grid.isWeil_false W.ψ _ _ _ _ ωB).mp hωB
  have key : ∀ d ∈ Θ'.support, W.kerA (.down t i j) d.1.2 g u * W.kerA (.right i j) d.2 u g₁ =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
        ωB (u, GlobalTheory.SquareComm.blk _ _ (g, g₁))
          (box2 (S := G.V (.grid i j)) (A := G.V (.grid i (j + 1))) (B := G.V (.grid (i + 1) j)) d.1.2
            (fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y))) 0 := by
    intro d hd
    have h := (GlobalTheory.SeesawSmall.seesaw_small hL W t i.2 j.2 ωB hω d.1.2 d.2 (hth d hd).1 (hth d hd).2).2 g u g₁
    have hadj : GlobalTheory.SeesawSmall.adjFn (G.V (.grid i j)) (G.V (.grid (i + 1) j)) d.2 =
        fun y => d.2 (adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y) := by
      funext y
      exact congrArg d.2 (GlobalTheory.AdjSwap.dagger_eq_adjM (G.V (.grid i j)) (negSp (G.V (.grid (i + 1) j))) y)
    rw [hadj] at h
    exact h
  simp only [kerSmall, GlobalTheory.SquareDict.datumB, thetaKO, Finsupp.sum, map_sum, Finset.sum_apply, map_smul,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [key d hd]
  ring

end GlobalTheory.SquareDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitIdempotentUnitDecomposition
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

theorem values_of_rel (D : D7) (z : ℂ) (K : ℕ) (b : D.host.Eˣ) (m : D.what₂.Tau → ℤ) (hK : 0 < K)
    (h : z ^ K * ∏ τ, (tauE D τ (b : D.host.E) / (‖tauE D τ (b : D.host.E)‖ : ℂ)) ^ m τ = 1) :
    Mod1All z ∧ ∀ (q : ℕ) [Fact q.Prime], (∀ P : HeightOneSpectrum (𝓞 D.host.E), ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      P.valuation D.host.E (b : D.host.E) = 1) → GlobalTheory.MovedKappaEx.UnitAt q z := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨hz, H⟩ := GlobalTheory.HeckeVal.root_value (tauE D) m b z K hK h
  refine ⟨⟨hz, fun σ => H ℂ σ fun τ => ?_⟩, fun q hq hb lam => ?_⟩
  · have := IsCMField.complexEmbedding_complexConj D.host.E (σ.comp τ) (b : D.host.E)
    simp only [RingHom.comp_apply] at this
    rw [this, Complex.norm_conj]
  · obtain ⟨M, hM, i1⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hq.out (b : D.host.E)
      fun P hP => (hb P hP).le
    obtain ⟨M', hM', i2⟩ := GlobalTheory.KerTie.MuqUnit.exists_coprime_mul_isIntegral hq.out (b : D.host.E)⁻¹
      fun P hP => by rw [map_inv₀, hb P hP, inv_one]
    have key : ∀ ψ : D.host.E →+* ℂ_[q], ‖ψ (b : D.host.E)‖ = 1 := fun ψ => by
      have j1 := GlobalTheory.HeckeVal.norm_le_one_of_denom ψ hM i1
      have j2 := GlobalTheory.HeckeVal.norm_le_one_of_denom ψ hM' i2
      rw [map_inv₀, norm_inv] at j2
      have h0 : 0 < ‖ψ b‖ := norm_pos_iff.2 ((map_ne_zero _).2 b.ne_zero)
      exact le_antisymm j1 ((inv_le_one₀ h0).1 j2)
    rw [Formalism.MainNotions.TaylorLogMetric.lamC, dif_pos hz]
    refine H _ lam fun τ => ?_
    exact (key (lam.comp τ)).trans
      (key ((lam.comp τ).comp (IsCMField.complexConj D.host.E : D.host.E →+* D.host.E))).symm

theorem inf_val (D : D7) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ) (hc : Formalism.L2.Theta.IsHeckeChar D c)
    (hr : Formalism.L2.Theta.ResEta D c n) : ∃ m : D.what₂.Tau → ℤ, ∀ (k : D.host.Eˣ) (x : (Formalism.L2.Theta.AE D)ˣ),
      Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D) = 1 →
      Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E)) →
      ((c x : Circle) : ℂ) = ∏ τ, (tauE D τ (k : D.host.E) / (‖tauE D τ (k : D.host.E)‖ : ℂ)) ^ m τ := by
  classical
  obtain ⟨θ, hθ⟩ : ∃ θ : InfFam D, IsInfFam θ := GlobalTheory.DualPairCompare.exists_infFam D
  have H : ∀ τ, ∃ m : ℤ, ∀ x : (Formalism.L2.Theta.AE D)ˣ, Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D) = 1 →
      (∀ τ', τ' ≠ τ → θ τ' (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D)) = 1) →
        ((c x : Circle) : ℂ) = (θ τ (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D)) / (‖θ τ (Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D))‖ : ℂ)) ^ m := fun τ => by
    obtain ⟨a, m, -, -, h⟩ := GlobalTheory.SplitCharExp.exists_hasInfExp D θ c n τ hθ hc hr
    exact ⟨m, h θ hθ⟩
  choose m hm using H
  refine ⟨m, fun k x hx1 hx2 => ?_⟩
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  let z : D.what₂.Tau → ℂˣ := fun τ => Units.map (tauE D τ).toMonoidHom k
  let f : ∀ _ : D.what₂.Tau, ℂ →* Formalism.L2.Theta.AE D := fun τ => e.comp (MonoidHom.mulSingle (fun _ : D.what₂.Tau => ℂ) τ)
  have hθk : ∀ τ, θ τ (Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E))) = tauE D τ k := fun τ => (hθ τ).1 k
  have ex : x = ∏ τ, Units.map (f τ) (z τ) := by
    apply Units.ext
    rw [Units.coe_prod]
    have e3 : (∏ τ, ((Units.map (f τ) (z τ) : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D)) = e (fun τ => tauE D τ k) := by
      change ∏ τ, e (Pi.mulSingle τ (tauE D τ k)) = _
      rw [← map_prod, Finset.univ_prod_mulSingle]
    rw [e3]
    exact GlobalTheory.SplitCharExp.ext_of_chart h (hx1.trans (e1 _).symm) fun τ => by rw [hx2, hθk, e2]
  rw [ex, map_prod]
  refine (map_prod Circle.coeHom _ _).trans (Finset.prod_congr rfl fun τ _ => ?_)
  have f2 : ∀ τ', θ τ' (Formalism.L2.Theta.infPart D ((Units.map (f τ) (z τ) : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D)) =
      (Pi.mulSingle τ (tauE D τ k) : D.what₂.Tau → ℂ) τ' := fun τ' => e2 _ τ'
  have := hm τ (Units.map (f τ) (z τ)) (e1 _) fun τ' ht => by rw [f2, Pi.mulSingle_eq_of_ne ht]
  rw [f2, Pi.mulSingle_eq_same] at this
  exact this

def finIso (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E :=
  (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).toRingEquiv.trans (GlobalTheory.Mem.Col2.afIso D.host.F D.host.E)

theorem finIso_one_tmul (D : D7) (x : D.host.E) : finIso D ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
    algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x := GlobalTheory.Mem.Col2.afIso_tmul_one _ _ x

theorem mem_intAE_iff (D : D7) (y : Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (finIso D y P) ≤ 1 :=
  (GlobalTheory.HostAdeleIso.mem_intAE_iff_comm D y).trans (GlobalTheory.Mem.Col2.mem_rInt_iff _ _ _)

set_option maxHeartbeats 800000 in

theorem exists_pow_rel (D : D7) (x : (Formalism.L2.Theta.AE D)ˣ) (hx : Formalism.L2.Theta.infPart D (x : Formalism.L2.Theta.AE D) = 1) :
    ∃ (h : ℕ) (k : D.host.Eˣ) (y w : (Formalism.L2.Theta.AE D)ˣ), 0 < h ∧ Formalism.L2.Pj.FinUnit w ∧ Formalism.L2.Theta.finPart D (y : Formalism.L2.Theta.AE D) = 1 ∧
      Formalism.L2.Theta.infPart D (y : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (Formalism.L2.Theta.incA D (k : D.host.E)) ∧
      x ^ h * y = w * Units.map (Formalism.L2.Theta.incA D).toMonoidHom k ∧
      ∀ P : HeightOneSpectrum (𝓞 D.host.E), finIso D (Formalism.L2.Theta.finPart D (x : Formalism.L2.Theta.AE D)) P = 1 →
        P.valuation D.host.E (k : D.host.E) = 1 := by
  obtain ⟨Φ, -, -, h1, -, h3⟩ := GlobalTheory.DetRootRead.exists_adele_equiv_fin D (finIso D) (finIso_one_tmul D) (mem_intAE_iff D)
  obtain ⟨s, hs, -⟩ := GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hs1 : ∀ z : Formalism.L2.Theta.AE D, (s z).1 = Formalism.L2.Theta.infPart D z := fun z => (hs z).1
  have hs2 : ∀ z : Formalism.L2.Theta.AE D, (s z).2 = Formalism.L2.Theta.finPart D z := fun z => (hs z).2
  have hfi := GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup D.host.E
  obtain ⟨u, hu, _, ⟨k, rfl⟩, e⟩ := Subgroup.mem_sup.1 ((GlobalTheory.Mem.Chr.unitIdl D.host.E ⊔
    (Neutral.B1.diagUnits D.host.E).range).pow_index_mem (Units.map Φ.toRingHom.toMonoidHom x))
  generalize hh : (GlobalTheory.Mem.Chr.unitIdl D.host.E ⊔ (Neutral.B1.diagUnits D.host.E).range).index = h at e
  have h0 : 0 < h := hh ▸ Nat.pos_of_ne_zero hfi.index_ne_zero
  let Ψ : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ →* (Formalism.L2.Theta.AE D)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hΨ : ∀ a, Φ ((Ψ a : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = a := fun a => Φ.apply_symm_apply _
  let K : (Formalism.L2.Theta.AE D)ˣ := Units.map (Formalism.L2.Theta.incA D).toMonoidHom k
  have e' : Ψ u * K = x ^ h := by
    have a1 : Ψ (Neutral.B1.diagUnits D.host.E k) = K := Units.ext (Φ.symm_apply_eq.2 (h1 k).symm)
    have a2 : Ψ (Units.map Φ.toRingHom.toMonoidHom x) = x := Units.ext (Φ.symm_apply_apply _)
    rw [← a1, ← map_mul, e, map_pow, a2]
  let g : Formalism.L2.Theta.AE D →* Formalism.L2.Theta.AE D := s.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inl _ (Af D.host.F ⊗[D.host.F] D.host.E)).comp (Formalism.L2.Theta.infPart D).toMonoidHom)
  have g1 : ∀ a, Formalism.L2.Theta.infPart D (g a) = Formalism.L2.Theta.infPart D a := fun a =>
    (hs1 _).symm.trans (congrArg Prod.fst (s.apply_symm_apply (Formalism.L2.Theta.infPart D a, 1)))
  have g2 : ∀ a, Formalism.L2.Theta.finPart D (g a) = 1 := fun a =>
    (hs2 _).symm.trans (congrArg Prod.snd (s.apply_symm_apply (Formalism.L2.Theta.infPart D a, 1)))
  have hint : ∀ a ∈ GlobalTheory.Mem.Chr.unitIdl D.host.E, ∀ b : (Formalism.L2.Theta.AE D)ˣ,
      Formalism.L2.Theta.finPart D ((Ψ a * Units.map g b : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) ∈ intAE D := fun a ha b => by
    have : Formalism.L2.Theta.finPart D ((Units.map g b : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = 1 := g2 _
    rw [Units.val_mul, RingHom.map_mul, this, mul_one, mem_intAE_iff, ← (h3 _).2, hΨ]
    exact fun P => (ha P).le
  refine ⟨h, k, Units.map g K, Ψ u * Units.map g K, h0, ⟨?_, hint u hu K, ?_⟩, g2 _, g1 _, ?_, fun P hP => ?_⟩
  · have a1 : Formalism.L2.Theta.infPart D ((Units.map g K : (Formalism.L2.Theta.AE D)ˣ) : Formalism.L2.Theta.AE D) = Formalism.L2.Theta.infPart D (K : Formalism.L2.Theta.AE D) := g1 _
    rw [Units.val_mul, RingHom.map_mul, a1, ← RingHom.map_mul, ← Units.val_mul, e', Units.val_pow_eq_pow_val,
      RingHom.map_pow, hx, one_pow]
  · rw [mul_inv, ← Ψ.map_inv u, ← (Units.map g).map_inv K]
    exact hint u⁻¹ ((GlobalTheory.Mem.Chr.unitIdl D.host.E).inv_mem hu) K⁻¹
  · rw [← e', mul_right_comm]
  · have a1 : (u : AdeleRing (𝓞 D.host.E) D.host.E).2 P * algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E) =
        ((Φ (x : Formalism.L2.Theta.AE D)).2 P) ^ h :=
      congrArg (fun a : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ => (a : AdeleRing (𝓞 D.host.E) D.host.E).2 P) e
    rw [(h3 _).2, hP, one_pow] at a1
    have a2 := congrArg (Valued.v : Valuation (P.adicCompletion D.host.E) _) a1
    rw [map_mul, hu P, one_mul, map_one] at a2
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P (k : D.host.E)).symm.trans a2

theorem finIso_idem (D : D7) {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {q : ℕ} (hq : GlobalTheory.MovedKappaEx.OffPrime e q)
    (P : HeightOneSpectrum (𝓞 D.host.E)) (hP : ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) : finIso D (Formalism.L2.Theta.finPart D e) P = 0 := by
  obtain ⟨h1, h2, v, ε, hε, h4⟩ := he
  have hv := hq v ε hε h4
  obtain ⟨α, rfl, -, hα⟩ := hε
  have hne : P.under (𝓞 D.host.F) ≠ v := by
    rintro rfl
    apply hv
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) (q : 𝓞 D.host.F) ∈ P.asIdeal
    rwa [map_natCast]
  have h5 : finIso D (Formalism.L2.Theta.finPart D (e + cA D e)) P = 0 := by
    rw [h4]
    refine (GlobalTheory.SplitProj.afIso_one_tmul_apply α P).trans ?_
    have : α (P.under (𝓞 D.host.F)) = 0 := hα _ hne
    rw [GlobalTheory.AdeleBaseChange.adMap_apply, this, map_zero]
  have h6 : e = e * (e + cA D e) := by rw [mul_add, h1, h2, add_zero]
  rw [h6, RingHom.map_mul, RingEquiv.map_mul]
  show finIso D (Formalism.L2.Theta.finPart D e) P * finIso D (Formalism.L2.Theta.finPart D (e + cA D e)) P = 0
  rw [h5, mul_zero]

theorem char_split_value (D : D7) (c : (Formalism.L2.Theta.AE D)ˣ →* Circle) (n : ℕ) (hc : Formalism.L2.Theta.IsHeckeChar D c)
    (hr : Formalism.L2.Theta.ResEta D c n) (e : Formalism.L2.Theta.AE D) (he : IsSplitIdem D e) (x₀ : (Formalism.L2.Theta.AE D)ˣ)
    (a : Formalism.L2.Theta.AE D) (hx : (x₀ : Formalism.L2.Theta.AE D) = e * a + (1 - e)) :
    Mod1All ((c x₀ : Circle) : ℂ) ∧ ∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.OffPrime e q →
      GlobalTheory.MovedKappaEx.UnitAt q ((c x₀ : Circle) : ℂ) := by
  obtain ⟨m, hm⟩ := inf_val D c n hc hr
  obtain ⟨-, -, -, M, hM, hMu⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D c hc.1
  have hinf : Formalism.L2.Theta.infPart D (x₀ : Formalism.L2.Theta.AE D) = 1 := by
    rw [hx, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one,
      GlobalTheory.SplitScalar.infPart_splitIdem he, zero_mul, sub_zero, zero_add]
  obtain ⟨h, k, y, w, hh, hw, hy1, hy2, e1, hk⟩ := exists_pow_rel D x₀ hinf
  have e2 : c x₀ ^ (h * M) * c y ^ M = 1 := by
    rw [pow_mul, ← mul_pow, ← map_pow, ← map_mul, e1, map_mul, hc.2 k, mul_one, hMu w hw]
  have e3 : ((c x₀ : Circle) : ℂ) ^ (h * M) *
      ∏ τ, (tauE D τ (k : D.host.E) / (‖tauE D τ (k : D.host.E)‖ : ℂ)) ^ (m τ * M) = 1 := by
    simp only [zpow_mul, zpow_natCast]
    rw [Finset.prod_pow, ← hm k y hy1 hy2, ← Circle.coe_pow, ← Circle.coe_pow, ← Circle.coe_mul, e2, Circle.coe_one]
  obtain ⟨h1, h2⟩ := values_of_rel D _ (h * M) k (fun τ => m τ * M) (Nat.mul_pos hh hM) e3
  refine ⟨h1, fun q _ hq => h2 q fun P hP => hk P ?_⟩
  rw [hx, RingHom.map_add, RingHom.map_sub, RingHom.map_mul, RingHom.map_one, RingEquiv.map_add, RingEquiv.map_sub,
    RingEquiv.map_mul, RingEquiv.map_one]
  show finIso D (Formalism.L2.Theta.finPart D e) P * finIso D (Formalism.L2.Theta.finPart D a) P + (1 - finIso D (Formalism.L2.Theta.finPart D e) P) = 1
  rw [finIso_idem D he hq P hP, zero_mul, sub_zero, zero_add]

theorem offPrime_conj {D : D7} {e : Formalism.L2.Theta.AE D} {q : ℕ} (h : GlobalTheory.MovedKappaEx.OffPrime e q) :
    GlobalTheory.MovedKappaEx.OffPrime (cA D e) q := fun v ε hv hε =>
  h v ε hv (by rw [← hε, GlobalTheory.MovedIdem.cA_cA, add_comm])

theorem defPair_inRange {T : Type} {m : ℕ} {p : Pair T} (h : DefPair m p) : p.InRange m := by
  cases p <;> simp only [DefPair, Pair.InRange, Pair.big, Node.InRange] at h ⊢ <;> omega

theorem split_chars : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
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

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumSymmetricTranslatesThetaPullbackExtends
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.HkIntegral.RegSum

def secSum {X : Scheme.{0}} {N : LB X} {n : ℕ} (F : Fin n → LB.Sec N) : LB.Sec N :=
  ⟨fun j => ∑ i, (F i).f j, fun a b => by
    simp only [map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => (F i).compat a b⟩

theorem sval_sum {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {n : ℕ}
    {a : LB.Sec (LB.LinComb L φ ε)} {F : Fin n → LB.Sec (LB.LinComb L φ ε)} (h : ∀ j, a.f j = ∑ i, (F i).f j)
    (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) : sval a r z J = ∑ i, sval (F i) r z J := by
  have hm := hJ.mem φ r
  refine (congrArg (gs r z _) (h _)).trans ((gs_eq r z _ hm _).trans ?_)
  exact ((congrArg _ (map_sum _ _ _)).trans (map_sum _ _ _)).trans
    (Finset.sum_congr rfl fun i _ => (gs_eq r z _ hm _).symm)

theorem zCast_sum {S : Scheme.{0}} (A : Over S) {L : LB A.left} {T : Over S} {a b : ℤ} (e : a = b) {n : ℕ}
    {t : LB.Sec (LPow A L a T)} {F : Fin n → LB.Sec (LPow A L a T)} (h : ∀ j, t.f j = ∑ i, (F i).f j) (j) :
    (PullbackSections.zCast A e t).f j = ∑ i, (PullbackSections.zCast A e (F i)).f j := by
  subst e
  exact h j

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem reg_sum (I : IntData Xo c T io y.1) (M : ℕ) {n : ℕ}
    {t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))}
    {F : Fin n → LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))}
    (h : ∀ j, t.f j = ∑ i, (F i).f j) (hF : ∀ i, Reg I M (F i)) : Reg I M t := by
  choose σ σt h1 h2 using hF
  refine ⟨secSum σ, secSum σt, fun Z r zp e1 e2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · refine (sval_sum (zCast_sum _ _ h) zp z hJ).trans ?_
    rw [sval_sum (a := secSum σt) (F := σt) (fun _ => rfl) r z hJ', Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => h1 i Z r zp e1 e2 z J J' hJ hJ'
  · rw [sval_sum (a := secSum σt) (F := σt) (fun _ => rfl) r z hJ',
      sval_sum (a := secSum σ) (F := σ) (fun _ => rfl) _ z hJ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => h2 i Z r z J J' hJ hJ'

theorem reg_of_isTransl (I : IntData Xo c T io y.1) (M : ℕ)
    (F : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y))))
    (P : PELUnif (IsLocalRing.maximalIdeal T.V) I.G) (hP : P.TorsionIso) (hM : IsUnit (M : T.V))
    (hF : letI := io.toAlgebra; IsTransl M y.1.s F) : Reg I M F := by
  let _ := io.toAlgebra
  obtain ⟨a, hVt⟩ := hF
  obtain ⟨θ, hθ, θK, hθ1, hθ2⟩ := PullbackSections.thetaTie _ _ _ _ _ _ T io y.1 I
  obtain ⟨ttK, FK, hVK, hFK⟩ := PullbackSections.VtMove.vtMoveSt _ _ _ _ _ y.1.x I.t' I.m1 I.w1 I.rig1 M _ y.1.s _ F hVt
    (fun u hu => hu) θK hθ1
  obtain ⟨σ, hσ⟩ := PullbackSections.regUnif_of' PullbackSections.thetaNu GlobalTheory.EndPullNu.main.2 GlobalTheory.FiniteLiftNu.finNu _ _ T.V I.G P hP θ hθ M hM
    I.t' I.m2 I.w2 I.rig2 θK hθ2 ttK FK hVK
  obtain ⟨σt, hσt⟩ := PullbackSections.exists_restrict I.t' _ (PullbackSections.zCast I.t'.G (PullbackSections.natCast_sq M) FK)
  have hg : ∀ {Z : Scheme.{0}} (r : Z ⟶ I.t'.G.left),
      (r ≫ PullbackSections.gsec I.t'.G) ≫ (snd (𝟙_ (Over (Sp T.Fr))) I.t'.G).left = r := fun r => by
    rw [Category.assoc, PullbackSections.gsec_snd, Category.comp_id]
  refine ⟨σ, σt, fun Z r zp h1 h2 z J J' hJ hJ' => ?_, fun Z r z J J' hJ hJ' => ?_⟩
  · rw [hσt Z r z J' hJ']
    exact hFK Z r zp (r ≫ PullbackSections.gsec I.t'.G) h1 h2 (hg r) z J J' hJ hJ'
  · rw [hσt Z r z J' hJ']
    exact hσ Z r (r ≫ PullbackSections.gsec I.t'.G) (hg r) z J J' hJ hJ'

theorem reg_of_isTranslSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (I : IntData Xo c T io y.1) (M : ℕ) (t : LB.Sec (LPow Xo.univ.t.G Xo.univ.t.PP.L ((M : ℤ) ^ 2) (Over.mk (xOf y)))), (∃ U : PELUnif (IsLocalRing.maximalIdeal T.V) I.G, U.TorsionIso) → IsUnit (M : T.V) → letI := io.toAlgebra; IsTranslSum M y.1.s t → Reg I M t := by
  intro E _ _ _ H Dw l Xo c T io y I M t ⟨P, hP⟩ hM ⟨n, F, hF, h⟩
  exact reg_sum I M h fun i => reg_of_isTransl I M (F i) P hP hM (hF i)

end GlobalTheory.HkIntegral.RegSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormOffIdempotentPartOrthogonalHalfStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticForm_offIdempotentPart_orthogonal_half : ∀ (D : D7) (S T : HSp D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ w x : WO S T, (IsHalf e x ∨ IsHalf (cA D e) x) → symplO S T ((1 - e - cA D e) • w) x = 0 := by
  first | exact @GlobalTheory.IdemOffOrth.symplO_compl_half | exact GlobalTheory.IdemOffOrth.symplO_compl_half | (intros; apply GlobalTheory.IdemOffOrth.symplO_compl_half <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TestGridStageLatticesPropertiesProofStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.testGridStageLatticesProperties_proof : StageOK := by
  first | exact @GlobalTheory.CoreOnto.StageProof.stageOK | exact GlobalTheory.CoreOnto.StageProof.stageOK | (intros; apply GlobalTheory.CoreOnto.StageProof.stageOK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGridRouteKernelEqDetCharactersMulThetaKerneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.RouteSeesaw GlobalTheory.ChainFr
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGridRouteKernel_eq_detCharacters_mul_thetaKernel : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (t : T) (i j : Fin D.R.m)
    (ωA : GlobalTheory.Grid.WRep (G.V (.grid (↑i + 1) (↑j + 1))) (GlobalTheory.Doubling.hsum (G.V (.grid ↑i (↑j + 1))) (G.V (.grid (↑i + 1) ↑j)))),
    GlobalTheory.Grid.IsWeil W.ψ true _ _ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) ωA →
    ∀ (B : Frames G) (ρ : RealMatch W) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)), IsMatched B t ρ i j Θ Θ' →
    ∀ g g₁ u, kerBig W Θ g g₁ u = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV G i j g * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.xiV₁ G t i j g₁ *
      thetaKO ωA u (GlobalTheory.SquareComm.blk _ _ (g, g₁)) (GlobalTheory.SquareDict.datumA W Θ) := by
  first | exact @GlobalTheory.SquareDict.ExactBig.kerBig_eq | exact GlobalTheory.SquareDict.ExactBig.kerBig_eq | (intros; apply GlobalTheory.SquareDict.ExactBig.kerBig_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_kernel_algebraic_expansion : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∀ t : T, ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → WO (GlobalTheory.Grid.neg A) WW), (∀ p, IsAlgebraic ℚ (c p)) ∧
      (∀ p, (w p).map (infPart D) = 0) ∧ X.f t = ∑ p, c p • heisO W.ψ (GlobalTheory.Grid.neg A) WW (w p) X.vac := by
  first | exact @GlobalTheory.BotFourier.finDatum_eq_sum_heis | exact GlobalTheory.BotFourier.finDatum_eq_sum_heis | (intros; apply GlobalTheory.BotFourier.finDatum_eq_sum_heis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalExistsCoeffsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_horizontal_exists_coeffs : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ Φ, IsThetaFunO R.ψ (G.V i j).V (G.V i (j + 1)).V Φ → ∃ a b : ℕ, ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (fs : Fin n → (WO (G.V i j).V (G.V i (j + 1)).V → ℂ)) (ps : Fin n → PolF D (G.V i (j + 1)).V.rank (G.V i j).V.rank), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l)) ∧ ∀ h g, ‖thetaKO (G.th t i j).ω h g (∑ l, GlobalTheory.Grid.fock R.ψ R.θ false (G.V i j) (G.V i (j + 1)) (fs l) (ps l)) - thetaKO (G.th t i j).ω h g Φ‖ ≤ ε * GlobalTheory.Grow.quotHeight (G.V i j).V h ^ a * GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b := by
  first | exact @GlobalTheory.ThetaArrowApprox.thetaKO_approx_fock | exact GlobalTheory.ThetaArrowApprox.thetaKO_approx_fock | (intros; apply GlobalTheory.ThetaArrowApprox.thetaKO_approx_fock <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftUniformFiniteBoundStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_lift_uniform_finite_bound : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i, i < D.R.m → ∃ N : ℕ, ∀ (K : Finset ℕ) (F : ℕ → (G.P (i + 1)).Maps) (v : ℕ → SmT (G.P (i + 1)).M), (∀ k ∈ K, F k ∈ (G.P (i + 1)).Cusp R.θ) → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.P (i + 1)).V) (G.P i).V Φ → ∀ ε : ENNReal, 0 < ε → ∃ (J : Finset ℕ) (f : ℕ → WO (G.P (i + 1)).V (G.P i).V → ℂ) (p : ℕ → GlobalTheory.Grid.Pol (G.P (i + 1)) (G.P i)), (∀ j ∈ J, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j)) ∧ GlobalTheory.Size.growthSize (G.P i).V N (fun h => (∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (Φ) * (F k (v k)) g ∂(G.mP (i + 1)).ν) - ∑ j ∈ J, ∑ k ∈ K, ∫ g in (G.mP (i + 1)).fd, thetaKO (G.dn i).ω g h (GlobalTheory.Grid.fock R.ψ R.θ true (G.P (i + 1)) (G.P i) (f j) (p j)) * (F k (v k)) g ∂(G.mP (i + 1)).ν) < ε := by
  first | exact @GlobalTheory.DownGrowth.growth_approx | exact GlobalTheory.DownGrowth.growth_approx | (intros; apply GlobalTheory.DownGrowth.growth_approx <;> assumption)
end

