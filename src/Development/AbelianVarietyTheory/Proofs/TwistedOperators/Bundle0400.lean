import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
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
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.KTypesAboveOfDsClass
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasurableEmbeddingEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0314
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0384
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftVanishesSingleCoefficientOfKernelKills
import Formalism.LocalToGlobal.IndefiniteReal.TopMult
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalOperatorsRowsNormalEigenspaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RealizationFamilyNormalOperators
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwoSidedHeckePartnerInertPrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeHeckeTransferCompositeLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0193
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0189
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0255

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspMultiplicitySpaceSpanSphericalEigenPartsEqTo
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EvenOntoDecomp

theorem cc_span_partFull : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, FinDim D → ForStage D fun c _ s => Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e} = ⊤ := by
  classical
  intro hP D hfd c hc j hj s hs
  have hmul : ∀ k ∈ s.J, ∀ k' ∈ s.J, (1 : GA D s.V → ℂ) (k * k') = (1 : GA D s.V → ℂ) k * (1 : GA D s.V → ℂ) k' :=
    fun _ _ _ _ => by simp
  have hops := GlobalTheory.SphericalOps.spherical_ops s.V c.θ s.M s.J (1 : GA D s.V → ℂ) c.S
    GlobalTheory.ChainOntoSph.exists_unif_of_F hc.inf hmul hs.split
  obtain ⟨hLU, -, hH⟩ := hops
  by_cases hsm : ∀ τ, s.M.sm τ ≠ ⊥
  swap
  · push_neg at hsm
    obtain ⟨τ, hτ⟩ := hsm
    refine Submodule.eq_top_iff'.2 fun u => ?_
    have h0 : PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = 0 := by
      refine MultilinearMap.ext fun v => ?_
      rw [MultilinearMap.zero_apply]
      have hv : ((v τ : s.M.sm τ) : s.M.H τ) = 0 := (Submodule.eq_bot_iff _).1 hτ _ (v τ).2
      exact MultilinearMap.map_coord_zero (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))) τ
        (Subtype.ext hv)
    have h1 := LinearEquiv.apply_symm_apply PiTensorProduct.lift (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ))
    rw [h0, map_zero] at h1
    have : u = 0 := Subtype.ext h1.symm
    rw [this]
    exact zero_mem _
  have hschur := GlobalTheory.MultFinite.schurMult (θ := c.θ) (M := s.M) (J := (s.J : Set (GA D s.V)))
    (χ := (1 : GA D s.V → ℂ)) hP s.ν s.fd
  haveI := hs.haar
  have hright : s.ν.IsMulRightInvariant := Formalism.IndefR.Eqv.unimodGA_holds s.V s.ν hs.haar
  obtain ⟨hlin, hpos⟩ := GlobalTheory.SchurConst.ipM_posDef D c.θ s.V s.par s.M (s.J : Set (GA D s.V))
    (1 : GA D s.V → ℂ) s.ν s.fd hc.inf hs.haar hs.fund hschur hsm
  obtain ⟨v0, hv0⟩ := GlobalTheory.SchurConst.exists_vec s.M hsm
  have hspec : ∀ T ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      ∀ T' ∈ Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      IsMultIP s.M s.ν s.fd T T' (ipM s.M s.ν s.fd T T') := fun T hT T' hT' =>
    ipM_spec _ _ _ _ _ (hschur hc.inf hs.haar hs.fund T hT T' hT')
  let φ := Submodule.equivMapOfInjective (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap
    (LinearEquiv.injective _) (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ))
  haveI : FiniteDimensional ℂ ((Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)).map
      (PiTensorProduct.lift : MMap s.M ≃ₗ[ℂ] _).toLinearMap) := hfd c hc j hj s hs
  haveI : FiniteDimensional ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)) :=
    LinearEquiv.finiteDimensional φ.symm
  let I := {t : HeightOneSpectrum (𝓞 D.host.E) × List ℤ × Finset (GA D s.V) //
    Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S t.1 t.2.1 t.2.2}
  let op : I → Module.End ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ)) := fun t =>
    (heckeOn s.M t.1.2.2).restrict fun T hT => (hH _ _ _ t.2).1 T hT
  have hcomm : ∀ i j, Commute (op i) (op j) := fun i j => by
    refine LinearMap.ext fun T => Subtype.ext ?_
    exact (hH _ _ _ i.2).2.1 _ _ _ j.2 T T.2
  have hadj : ∀ i, ∃ i', ∀ x y : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ),
      ipM s.M s.ν s.fd (op i x : MMap s.M) y = ipM s.M s.ν s.fd x (op i' y : MMap s.M) := fun i => by
    obtain ⟨R', h', hip⟩ := (hH _ _ _ i.2).2.2
    refine ⟨⟨(i.1.1, dualLab i.1.2.1, R'), h'⟩, fun x y => ?_⟩
    have h1 := hspec _ ((hH _ _ _ i.2).1 x x.2) y y.2
    have h2 := (hip s.ν s.fd hs.haar hright hs.fund hschur x x.2 y y.2 _).1 h1
    have h3 := hspec x x.2 _ ((hH _ _ _ h').1 y y.2)
    exact hasPeterssonInner_unique s.M s.ν s.fd _ _ v0 hv0 h2 h3
  have htop := GlobalTheory.OntoDecomp.iSup_jointEigenspace_eq_top
    (fun x y : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) => ipM s.M s.ν s.fd x y)
    (fun x y z a => (hlin x x.2 y y.2 z z.2 a).1) (fun x y => (hlin x x.2 y y.2 y y.2 0).2)
    (fun x hx => hpos x x.2 fun h => hx (Subtype.ext h)) op hcomm hadj
  have hsub : ∀ x : I → ℂ, ∀ T ∈ ⨅ i, (op i).eigenspace (x i), ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      (T : MMap s.M) ∈ partFull c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S e := by
    classical
    intro x T hT
    refine ⟨fun P d => if h : ∃ R, Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S P d R
      then x ⟨(P, d, h.choose), h.choose_spec⟩ else 0, ?_⟩
    rw [mem_partFull]
    refine ⟨T.2, fun P d R hR v => ?_⟩
    have hex : ∃ R, Hecke₂ s.V (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) c.S P d R := ⟨R, hR⟩
    rw [dif_pos hex]
    have hlevT := ((GlobalTheory.MultMem.mem_mult_iff ..).1 T.2).lev v
    rw [hLU P d R hex.choose hR hex.choose_spec _ hlevT]
    have h1 := (Submodule.mem_iInf _).1 hT ⟨(P, d, hex.choose), hex.choose_spec⟩
    rw [Module.End.mem_eigenspace_iff] at h1
    exact congrArg (fun U : Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ) => (U : MMap s.M) v) h1
  rw [eq_top_iff]
  rintro u -
  obtain ⟨T, rfl⟩ := φ.surjective u
  have hT : T ∈ (⊤ : Submodule ℂ (Mult c.θ s.M (s.J : Set (GA D s.V)) (1 : GA D s.V → ℂ))) := trivial
  rw [← htop] at hT
  refine Submodule.iSup_induction (fun x : I → ℂ => ⨅ i, (op i).eigenspace (x i))
    (motive := fun T => φ T ∈ Submodule.span ℂ {u : s.CC c | ∃ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ,
      PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) ∈
        partFull c.θ s.M (s.J : Set (GA D s.V)) 1 c.S e}) hT ?_ ?_ ?_
  · intro x T hT
    obtain ⟨e, he⟩ := hsub x T hT
    refine Submodule.subset_span ⟨e, ?_⟩
    have : ((φ T : s.CC c) : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)) = PiTensorProduct.lift (T : MMap s.M) := rfl
    rw [this, LinearEquiv.symm_apply_apply]
    exact he
  · rw [map_zero]; exact zero_mem _
  · intro a b ha hb; rw [map_add]; exact add_mem ha hb

end GlobalTheory.EvenOntoDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesCharacterFormula
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S GlobalTheory.RealInd
open GlobalTheory.Dec (IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep IsUnitEquiv IsCharFn IsRegSS)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.LowestKTypeDetermines

namespace GlobalTheory.DSCharLowest

theorem isDS_of_cone {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} (hl : Formalism.QuantumDeterminants.IsHCParam lam) {V : Type}
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] {σ : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)} (h : IsSqIntIrr ε σ)
    (h1 : ∃ S : Submodule ℂ V, IsKTypeOf ε σ (Formalism.QuantumDeterminants.lowK ε lam) S)
    (h2 : ∀ (ν : Fin n → ℝ) (S : Submodule ℂ V), IsKTypeOf ε σ ν S → ∃ c : Fin n → Fin n → ℕ,
      (∀ a b, c a b ≠ 0 → a < b) ∧ ν = Formalism.QuantumDeterminants.lowK ε lam + ∑ a, ∑ b, (c a b : ℝ) • root a b) :
    IsDS ε lam σ := by
  obtain ⟨c1, c2, c3, c4, c5⟩ := h
  refine ⟨c1, c2, c3, c4, c5, h1, fun μ S hS => ?_⟩
  obtain ⟨c, hc, rfl⟩ := h2 μ S hS
  unfold vNormSq
  rw [add_right_comm, lowK_add]
  have := nsq_add_cone (strictAnti_add_rho hl.1).antitone hc
  linarith [nsq_nonneg (∑ a, ∑ b, (c a b : ℝ) • root a b)]

theorem discreteSeriesCharacter_of_parameter : GlobalTheory.Published.IrreducibleUnitaryAdmissible →
    GlobalTheory.Published.KFiniteCoefficientsAnalytic → GlobalTheory.Published.CharacterRegularityFiniteLength →
    GlobalTheory.Published.DiscreteSeriesCharacterOfParameter → GlobalTheory.Dec.DSUnique → GlobalTheory.Published.DiscreteSeriesCharacter := by
  intro hadm han hreg hpar huniq n ε μ _ V _ _ _ lam σ hl hσ hU
  have hA : IsAdmRep ε σ := GlobalTheory.T.admissible_unitary_K_finite.1 hadm n ε V σ hU hσ.2.2.2.1
  have hF := (GlobalTheory.T.irreducible_admissible_finite_length han n ε V σ ⟨hσ.2.1, hA, hσ.2.2.2.1⟩).2
  obtain ⟨Θ, hΘ⟩ := hreg n ε μ V σ hA hF
  obtain ⟨V₀, _, _, _, σ₀, h₀, h1, h2, Θ₀, hΘ₀, hval⟩ := hpar n ε μ lam hl
  obtain ⟨T, hT⟩ := huniq n ε lam V₀ σ₀ V σ hl (isDS_of_cone hl h₀ h1 h2) hσ
  have he : IsUnitEquiv (ujRep h₀.2.2.1) (ujRep hU) := ⟨T, fun g v => hT _ g.2 v⟩
  refine ⟨Θ, hΘ, fun θ hθ => ?_⟩
  rw [← hval θ hθ]
  exact IsCharFn.unique isInducing_matCoord hΘ.1 (hΘ₀.of_isUnitEquiv he) hθ

end GlobalTheory.DSCharLowest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesSpectralSideStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.discrete_series_spectral_side : GlobalTheory.Published.DiscreteSeriesClassification → GlobalTheory.Published.FlathFactorisation → GlobalTheory.Published.HarishChandraCharacters → GlobalTheory.IndefiniteRowSideFullHecke.PseudoCoefficientSeparation.PseudoCoeffSeparation → ∀ (D : D7) (V : HSp D) (lam : D.what₂.Tau → Fin V.rank → ℤ) (S : D.what₂.Tau → SPar) (M : DSModel V S) (T : TypeDataG V) (U : AuxiliaryPlaceHermitianSpace V) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), IsTestData V lam M T U μa μf μ fa ff → ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : GA D V →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ c : ℂ, HasTrace (repOp π μ (tensor D.sp.cm.sig V.gram fa ff)) c → c ≠ 0 → HasDSComp M π := by
  first | exact @GlobalTheory.hasDSComp_of_trace_ne_zero | exact GlobalTheory.hasDSComp_of_trace_ne_zero | (intros; apply GlobalTheory.hasDSComp_of_trace_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubledVacuumLatticeStabilizerBlocksKeepLattice
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVac.BlocksPreserved

theorem blocks_keep {R : Type} [CommRing R] {d : ℕ} (S : AddSubgroup (Fin d → R))
    (M : Matrix (Fin d ⊕ Fin d) (Fin d ⊕ Fin d) R)
    (h : ∀ z : Fin d ⊕ Fin d → R, z ∘ Sum.inl ∈ S → z ∘ Sum.inr ∈ S →
      (M *ᵥ z) ∘ Sum.inl ∈ S ∧ (M *ᵥ z) ∘ Sum.inr ∈ S) :
    (∀ z ∈ S, M.toBlocks₁₁ *ᵥ z ∈ S) ∧ (∀ z ∈ S, M.toBlocks₁₂ *ᵥ z ∈ S) ∧
    (∀ z ∈ S, M.toBlocks₂₁ *ᵥ z ∈ S) ∧ (∀ z ∈ S, M.toBlocks₂₂ *ᵥ z ∈ S) := by
  have eL : ∀ z : Fin d → R, (Sum.elim z 0 : Fin d ⊕ Fin d → R) ∘ Sum.inl = z := fun z => rfl
  have eR : ∀ z : Fin d → R, (Sum.elim z 0 : Fin d ⊕ Fin d → R) ∘ Sum.inr = 0 := fun z => rfl
  have fL : ∀ z : Fin d → R, (Sum.elim 0 z : Fin d ⊕ Fin d → R) ∘ Sum.inl = 0 := fun z => rfl
  have fR : ∀ z : Fin d → R, (Sum.elim 0 z : Fin d ⊕ Fin d → R) ∘ Sum.inr = z := fun z => rfl
  have a11 : ∀ z : Fin d → R, (M *ᵥ Sum.elim z 0) ∘ Sum.inl = M.toBlocks₁₁ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₁]
  have a21 : ∀ z : Fin d → R, (M *ᵥ Sum.elim z 0) ∘ Sum.inr = M.toBlocks₂₁ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₁]
  have a12 : ∀ z : Fin d → R, (M *ᵥ Sum.elim 0 z) ∘ Sum.inl = M.toBlocks₁₂ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₁₂]
  have a22 : ∀ z : Fin d → R, (M *ᵥ Sum.elim 0 z) ∘ Sum.inr = M.toBlocks₂₂ *ᵥ z := by
    intro z; funext i; simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.toBlocks₂₂]
  refine ⟨fun z hz => ?_, fun z hz => ?_, fun z hz => ?_, fun z hz => ?_⟩
  · have := (h (Sum.elim z 0) (by rw [eL]; exact hz) (by rw [eR]; exact S.zero_mem)).1
    rwa [a11] at this
  · have := (h (Sum.elim 0 z) (by rw [fL]; exact S.zero_mem) (by rw [fR]; exact hz)).1
    rwa [a12] at this
  · have := (h (Sum.elim z 0) (by rw [eL]; exact hz) (by rw [eR]; exact S.zero_mem)).2
    rwa [a21] at this
  · have := (h (Sum.elim 0 z) (by rw [fL]; exact S.zero_mem) (by rw [fR]; exact hz)).2
    rwa [a22] at this

end GlobalTheory.DblVac.BlocksPreserved

namespace GlobalTheory.DblVac

theorem KD_blocks_keep : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {d : ℕ} (W : Spc F E d) (v : Pl F), ∀ g ∈ GlobalTheory.DblVac.KD σ W v,
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₁₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₁ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) ∧
  (∀ z ∈ GlobalTheory.InertSph.latAt W v, (GlobalTheory.DblVac.matD g⁻¹).toBlocks₂₂ *ᵥ z ∈ GlobalTheory.InertSph.latAt W v) := by
  intro F E _ _ _ _ _ σ d W v g hg
  have h1 := BlocksPreserved.blocks_keep (GlobalTheory.InertSph.latAt W v) (matD g)
    (fun z h1 h2 => (hg.2 z ⟨h1, h2⟩).1)
  have h2 := BlocksPreserved.blocks_keep (GlobalTheory.InertSph.latAt W v) (matD g⁻¹)
    (fun z h1 h2 => (hg.2 z ⟨h1, h2⟩).2)
  exact ⟨h1.1, h1.2.1, h1.2.2.1, h1.2.2.2, h2.1, h2.2.1, h2.2.2.1, h2.2.2.2⟩

end GlobalTheory.DblVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DualIrreducibleCoefficientSpaceRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Matrix

namespace GlobalTheory.DualIrr

theorem dual_irr : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V), IsInfFam θ → c.Is → ∀ N : Submodule ℂ (Module.Dual ℂ c.W), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ f ∈ N, (c.ρ (atTau θ V τ g)⁻¹).dualMap f ∈ N) → N = ⊥ ∨ N = ⊤ := by
  intro D V θ c hθ hc N hN

  have hinv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∃ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      (atTau θ V τ g')⁻¹ = atTau θ V τ g := by
    intro τ g hg
    have hu : IsUnit (gramAt D V τ).det := by
      have : (gramAt D V τ).det = tauE D τ V.gram.det := (RingHom.map_det (tauE D τ) V.gram).symm
      rw [this]
      exact ((_root_.map_ne_zero _).2 (Formalism.L2.Theta.gram_det_ne V)).isUnit
    have h1 : gᴴ * gramAt D V τ * g = gramAt D V τ := hg
    set gi := (gramAt D V τ)⁻¹ * gᴴ * gramAt D V τ with hgi
    have h2 : gi * g = 1 := by
      rw [hgi, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc gᴴ, h1, Matrix.nonsing_inv_mul _ hu]
    have h3 : g * gi = 1 := mul_eq_one_comm.1 h2
    have hgi' : gi ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
      show giᴴ * gramAt D V τ * gi = gramAt D V τ
      calc giᴴ * gramAt D V τ * gi = giᴴ * (gᴴ * gramAt D V τ * g) * gi := by rw [h1]
        _ = (g * gi)ᴴ * gramAt D V τ * (g * gi) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = gramAt D V τ := by rw [h3]; simp
    refine ⟨gi, hgi', ?_⟩
    have e : atTau θ V τ g * atTau θ V τ gi = 1 := by
      rw [← GlobalTheory.PointAtPlaceHom.atTau_mul hθ V τ hg hgi', h3, GlobalTheory.PointAtPlaceHom.atTau_one hθ V τ]
    rw [eq_inv_of_mul_eq_one_right e, inv_inv]
  set U := N.dualCoannihilator with hUdef
  have hstab : ∀ a ∈ GinfC V, ∀ v ∈ U, c.ρ a v ∈ U := by
    intro a ha
    refine Submonoid.closure_induction (motive := fun a _ => ∀ v ∈ U, c.ρ a v ∈ U) ?_ ?_ ?_
      (Formalism.IndefR.TopMult.ginf_mem_closure hθ ha)
    · rintro x ⟨τ, g, hg, rfl⟩ v hv
      obtain ⟨g', hg', e⟩ := hinv τ g hg
      rw [Submodule.mem_dualCoannihilator] at hv ⊢
      intro f hf
      have := hv _ (hN τ g' hg' f hf)
      rw [e] at this
      simpa [LinearMap.dualMap_apply] using this
    · intro v hv; simpa using hv
    · intro x y _ _ hx hy v hv
      rw [map_mul, Module.End.mul_apply]
      exact hx _ (hy v hv)
  have hU : ∀ u ∈ GinfC V, U.map (c.ρ u) ≤ U := by
    rintro u hu _ ⟨v, hv, rfl⟩
    exact hstab u hu v hv
  have hN' : U.dualAnnihilator = N := Subspace.dualCoannihilator_dualAnnihilator_eq
  rcases GlobalTheory.GenRealSchur.irr_real c hc U hU with h | h
  · right; rw [← hN', h, Submodule.dualAnnihilator_bot]
  · left; rw [← hN', h, Submodule.dualAnnihilator_top]

end GlobalTheory.DualIrr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EigSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.EigSpan

theorem eig_span : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → ∀ P, GlobalTheory.Hk3.Good R t P → ∀ (a : List ℤ → ℂ) (w : R.HE.H) (s : Set (List ℤ →₀ ℂ)), (∀ c ∈ s, h P c w = GlobalTheory.Hk3.evC (Yc D 0) P a c • w) → ∀ c ∈ Submodule.span ℂ s, h P c w = GlobalTheory.Hk3.evC (Yc D 0) P a c • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh P hP a w s hs c hc
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hkAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.hk (Yc D 0) P (c + c') = GlobalTheory.Hk3.hk (Yc D 0) P c + GlobalTheory.Hk3.hk (Yc D 0) P c' :=
    fun c c' => by
      unfold GlobalTheory.Hk3.hk
      exact Finsupp.sum_add_index' (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)
  have hkSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.hk (Yc D 0) P (z • c) = z • GlobalTheory.Hk3.hk (Yc D 0) P c :=
    fun z c => by
      unfold GlobalTheory.Hk3.hk
      rw [Finsupp.sum_smul_index', Finsupp.smul_sum]
      · simp only [smul_eq_mul, mul_smul]
      · intro; exact zero_smul _ _
  have hkZero : GlobalTheory.Hk3.hk (Yc D 0) P 0 = 0 := by
    unfold GlobalTheory.Hk3.hk; exact Finsupp.sum_zero_index
  have evAdd : ∀ c c' : List ℤ →₀ ℂ, GlobalTheory.Hk3.evC (Yc D 0) P a (c + c') = GlobalTheory.Hk3.evC (Yc D 0) P a c + GlobalTheory.Hk3.evC (Yc D 0) P a c' :=
    fun c c' => by
      unfold GlobalTheory.Hk3.evC
      exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> ring)
  have evSmul : ∀ (z : ℂ) (c : List ℤ →₀ ℂ), GlobalTheory.Hk3.evC (Yc D 0) P a (z • c) = z * GlobalTheory.Hk3.evC (Yc D 0) P a c :=
    fun z c => by
      unfold GlobalTheory.Hk3.evC
      rw [Finsupp.sum_smul_index', Finsupp.mul_sum]
      · exact Finsupp.sum_congr fun d _ => by split_ifs <;> simp [mul_assoc]
      · intro; simp
  have evZero : GlobalTheory.Hk3.evC (Yc D 0) P a 0 = 0 := by
    unfold GlobalTheory.Hk3.evC; exact Finsupp.sum_zero_index
  have pAdd : ∀ L L' x, postOn (R.MY 0) (L + L') x = postOn (R.MY 0) L x + postOn (R.MY 0) L' x := by
    intro L L' x; ext v; simp [postOn]
  have pSmul : ∀ (z : ℂ) L x, postOn (R.MY 0) (z • L) x = z • postOn (R.MY 0) L x := by
    intro z L x; ext v; simp [postOn]
  have pZero : ∀ x, postOn (R.MY 0) 0 x = 0 := by
    intro x; ext v; simp [postOn]
  have hAdd : ∀ c c', h P (c + c') w = h P c w + h P c' w := fun c c' =>
    inj (by rw [hh P hP, map_add, hh P hP, hh P hP, hkAdd, pAdd])
  have hSmul : ∀ (z : ℂ) c, h P (z • c) w = z • h P c w := fun z c =>
    inj (by rw [hh P hP, map_smul, hh P hP, hkSmul, pSmul])
  have hZero : h P 0 w = 0 := inj (by rw [hh P hP, hkZero, pZero, map_zero])
  induction hc using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => rw [hZero, evZero, zero_smul]
  | add x y _ _ hx hy => rw [hAdd, hx, hy, evAdd, add_smul]
  | smul z x _ hx => rw [hSmul, hx, evSmul, mul_smul]

end GlobalTheory.EigSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqOfSplitVec
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.LiftRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.SplitLabels

open GlobalTheory.Hk3 GlobalTheory.Hk3.LabDet

theorem evC_single_lab {D : D7} (V : HSp D) (P : Pl D.host.E) (a : List ℤ → ℂ) (d : List ℤ) (hd : IsLab V P d) :
    evC V P a (Finsupp.single d 1) = a d := by
  unfold evC
  rw [Finsupp.sum_single_index (by simp), if_pos hd, one_mul]

theorem eq_of_split_vec : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (t : T) (h : Pl D.host.E → (List ℤ →₀ ℂ) → Module.End ℂ R.HE.H), (∀ P, GlobalTheory.Hk3.Good R t P → ∀ c x, R.HE.e (h P c x) = postOn (R.MY 0) (GlobalTheory.Hk3.hk (Yc D 0) P c) (R.HE.e x)) → ∀ P, GlobalTheory.Hk3.Good R t P → Formalism.DivisionValues.conjPl P ≠ P → ∀ (c : Pl D.host.E → List ℤ → ℂ) (x w : R.HE.H), x ≠ 0 → (∀ P', GlobalTheory.Hk3.Good R t P' → ∀ cc, h P' cc x = GlobalTheory.Hk3.evC (Yc D 0) P' (fun d => c P' (dualLab d)) cc • x) → (∀ k ≤ (Yc D 0).rank, h P (Finsupp.single (splitLab (Yc D 0).rank k) 1) w = GlobalTheory.Hk3.evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) • w ∧ h (Formalism.DivisionValues.conjPl P) (Finsupp.single (splitLab (Yc D 0).rank k) 1) w = GlobalTheory.Hk3.evC (Yc D 0) (Formalism.DivisionValues.conjPl P) (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1) • w) → ∀ d, GlobalTheory.Hk3.IsLab (Yc D 0) P d → h P (Finsupp.single d 1) w = c P (dualLab d) • w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC t h hh P hP hcP c x w hx0 hxe hw d hd
  obtain ⟨-, hgood, -, -⟩ := GlobalTheory.T.theta_lift_levels_good_primes_properties R F hC.lev
  have hPA : Good R A.μ0 P := (hgood t P hP).2.2
  have hPc : Good R t (Formalism.DivisionValues.conjPl P) := (hgood t P hP).2.1
  obtain ⟨n, hβ⟩ := hC.lev.βY 0 (lt_of_lt_of_le two_pos D.R.two_le_m)
  have hlev := GlobalTheory.T.level_operators_at_prime_off_level_datum (Yc D 0) (R.βY 0) (R.ΛY 0) _ (R.dat0 R.triv) hβ P
    (by rw [Nat.cast_pow]; exact fun hm => (hgood _ P hPA).1 (P.isPrime.mem_of_pow_mem n hm))
    (fun PP hPP => hPA PP (hPP.imp id fun h => absurd h (Finset.notMem_empty _)))
  have inj : Function.Injective R.HE.e := hC.models.HE.1
  have hmem : ∀ y, R.HE.e y ∈ Mult R.θ (R.MY 0) (levG _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) :=
    fun y => goodPart_le _ _ _ _ _ (hC.models.HE.2.1 ▸ LinearMap.mem_range_self _ y)
  have hfix : ∀ y, ∀ k ∈ hyp (Yc D 0) P, rRep (R.MY 0) k (R.HE.e y) = R.HE.e y := fun y k hk =>
    mult_lev _ _ _ _ _ (hmem y) k (hlev.1 k hk).1 (hlev.1 k hk).2
  have hop : ∀ P', Good R t P' → ∀ e y, opOf (rRep (R.MY 0)) P' (Finsupp.single e 1) (R.HE.e y) =
      R.HE.e (h P' (Finsupp.single e 1) y) := by
    intro P' hP' e y
    rw [opOf_single, sum_rRep, hh P' hP', GlobalTheory.Hk3.OpsRows.hk_single]
    rfl
  have hu : R.HE.e x ≠ 0 := fun h0 => hx0 (inj (by rw [h0, map_zero]))
  obtain ⟨a, ha, hae⟩ := GlobalTheory.SplitGen.gen_split (Yc D 0) P hcP (MMap (R.MY 0)) (rRep (R.MY 0)) d
  obtain ⟨l, h1, h2⟩ := adjoin_common _ (R.HE.e x) (R.HE.e w) (by
    rintro y ⟨k, hk, rfl | rfl⟩
    · refine ⟨evC (Yc D 0) P (fun d => c P (dualLab d)) (Finsupp.single (splitLab (Yc D 0).rank k) 1), ?_, ?_⟩
      · rw [hop P hP, hxe P hP, map_smul]
      · rw [hop P hP, (hw k hk).1, map_smul]
    · have hc := (GlobalTheory.T.sphericalHecke_conjPlace_eq_dualLabel (Yc D 0) P).2.2 (Finsupp.single (splitLab (Yc D 0).rank k) 1) _ (rRep (R.MY 0))
      have hdc : dualC (Finsupp.single (splitLab (Yc D 0).rank k) 1) =
          Finsupp.single (dualLab (splitLab (Yc D 0).rank k)) 1 := by
        unfold dualC
        rw [Finsupp.mapDomain_single]
      rw [hdc] at hc
      rw [← hc _ (hfix x), ← hc _ (hfix w)]
      refine ⟨evC (Yc D 0) (Formalism.DivisionValues.conjPl P) (fun d => c (Formalism.DivisionValues.conjPl P) (dualLab d))
        (Finsupp.single (splitLab (Yc D 0).rank k) 1), ?_, ?_⟩
      · rw [hop _ hPc, hxe _ hPc, map_smul]
      · rw [hop _ hPc, (hw k hk).2, map_smul]) a ha
  rw [hae _ (hfix x), hop P hP, hxe P hP, evC_single_lab _ _ _ _ hd, map_smul] at h1
  have hl : l = c P (dualLab d) := (smul_left_injective ℂ hu h1).symm
  rw [hae _ (hfix w), hop P hP, hl, ← map_smul] at h2
  exact inj h2

end GlobalTheory.Hk3.SplitLabels

end
end

