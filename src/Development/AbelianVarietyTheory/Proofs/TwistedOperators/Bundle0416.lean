import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHilbertSchmidtOfFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0402
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0366
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0302
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0291
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0338
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0038
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0324
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0403
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0317
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0377
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0399
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
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

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorTraceEqConstMulLocalTrace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.PureTensorTrace

theorem isIntegralOp_smoothOp {G X : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [IsFiniteMeasureOnCompacts μ]
    [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X} (hρ : GlobalTheory.PRep.IsSmooth ρ) {f : G → ℂ}
    (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ ρ f (smoothOp ρ μ f) := by
  intro v l
  have hi := hρ.smoothOp_integrand hf hc v
  refine ⟨?_, ?_⟩
  · have := integrable_map (μ := μ) hi.1 hi.2 l l.map_zero
    simpa only [map_smul, smul_eq_mul] using this
  · rw [hρ.map_smoothOp (μ := μ) hf hc l v]
    simp only [smul_eq_mul]

theorem hasTrace_update_eq_const_mul : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), IsAdmissible σ → ∀ (N : Type) [AddCommGroup N] [Module ℂ N] (π : Representation ℂ (Gv V u) N), π.IsIrreducible → IsAdmissible π → FinHasLocComp V u π σ → ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∃ c : ℂ, ∀ f ∈ CcLoc D.sp.cm.sig V.gram u, (∃ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf u) π f b) ∧ ∀ b, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace (μf u) π f b → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasTrace ν σ (finFn V (Function.update ff u f)) (c * b) := by
  intro D V u μf hμ hK1 ν hν W _ _ σ hσ N _ _ π hπi hπa hloc ff hff
  haveI : (μf u).IsHaarMeasure := hμ u
  obtain ⟨H, K, hKo, hHc, hHf, hHop⟩ := GlobalTheory.T.pureTensorOperator_eq_offPlace_mul_atPlace D V u μf hμ hK1 ν hν W σ hσ.1 ff hff
  have hcont : Continuous (locFin V u) := (continuous_emb _ _ u).subtype_mk _
  have hρ : GlobalTheory.PRep.IsSmooth (σ.comp (locFin V u)) := fun x => (hσ.1 x).preimage hcont
  obtain ⟨s, hs⟩ := GlobalTheory.T.exists_finset_localComponent_copies_fixed_away D V u W σ hσ N π hπi hπa hloc K hKo
  have hrange : ∃ s : Finset (π.IntertwiningMap (σ.comp (locFin V u))),
      LinearMap.range H ≤ ⨆ φ ∈ s, LinearMap.range φ.toLinearMap := by
    refine ⟨s, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact hs _ fun k hk hk1 => hHf x k hk hk1
  have hschur : ∀ φ : π.IntertwiningMap π, ∃ c : ℂ, φ.toLinearMap = c • LinearMap.id := fun φ =>
    GlobalTheory.T.schur_admissible_alt (Gv V u) (Kv V u) (isOpen_stabLoc _ _ _ u) (isCompact_stabLoc _ _ _ u) N π hπi hπa
      φ.toLinearMap fun g x => Representation.IntertwiningMap.isIntertwining _ _ φ g x
  obtain ⟨c, hc⟩ := GlobalTheory.T.trace_mul_endomorphism_isotypicRep (Gv V u) N W π (σ.comp (locFin V u)) hπi hschur hloc H
    (fun g x => hHc g x) hrange
  refine ⟨c, fun f hf => ⟨?_, ?_⟩⟩
  · have hfd := hπa.finiteDimensional_range_smoothOp (μ := μf u) hf.1 hf.2 (isOpen_stabLoc _ _ _ u)
      (isCompact_stabLoc _ _ _ u) (K := Kv V u)
    exact ⟨_, _, isIntegralOp_smoothOp hπa.1 hf.1 hf.2, hfd, rfl⟩
  · rintro b ⟨A, hA, hAb⟩
    obtain rfl := hA.unique (isIntegralOp_smoothOp hπa.1 hf.1 hf.2)
    have hB := isIntegralOp_smoothOp (μ := μf u) hρ hf.1 hf.2
    refine ⟨_, hHop f hf _ hB, hc _ _ (fun φ => ?_) b hAb⟩
    ext x
    exact (hπa.1.map_smoothOp_of_intertwining hρ hf.1 hf.2 φ.toLinearMap
      (fun g v => Representation.IntertwiningMap.isIntertwining _ _ φ g v) x).symm

end GlobalTheory.PureTensorTrace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedThetaCoefficientEqIsotropicIntegral
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CoefUnfold

theorem isoPart_add' {D : D7} (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (y z : Mx D W.rank r) :
    isoPart V W C (y + z) = isoPart V W C y + isoPart V W C z := by
  unfold isoPart
  rw [Matrix.add_mul]

private theorem symplOH_eq_zero_of_symplO_eq_zero {D : D7} (S T : HSp D) (a b : WO S T) (h : symplO S T a b = 0) :
    symplOH S T a b = 0 := by
  have h2 : (2 : AF D.host.F) * symplOH S T a b = 0 := by
    rw [two_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 a b, h]
  have hu : IsUnit (2 : AF D.host.F) := by
    have e : (algebraMap D.host.F (AF D.host.F)) 2 = 2 := map_ofNat _ 2
    rw [← e]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  exact hu.mul_right_eq_zero.1 h2

theorem sum_translates_eq : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∀ κ : ℝ, (∀ H : WO V W → ℂ, Continuous H → (∃ b : ℝ, ∀ w, ‖H w‖ ≤ b) → (∀ γ ∈ ratL W V, ∀ w, H (γ + w) = H w) → ∫ w in 𝓕V, H w ∂μV = κ • ∫ t in 𝓨, ∫ y in 𝓨, ∫ x in 𝓕', H (isoPart V W C' t + isoPart V W C y + midPart V V' W B x) ∂μ' ∂μ ∂μ) → ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ y : Mx D W.rank r, Summable (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV‖) → ∑' a : Matrix (Fin W.rank) (Fin r) D.host.E, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) = κ • ∫ y' in 𝓨, ∫ x in 𝓕', F (isoPart V W C (y + y') + midPart V V' W B x) * star (G (isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ := by
  intro D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ F G hF hG y hs
  have hY' := hY
  obtain ⟨hμH, hYF, hY1⟩ := hY'
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  haveI : IsTopologicalAddGroup (Mx D W.rank r) := i1
  haveI : LocallyCompactSpace (Mx D W.rank r) := i2
  haveI : SecondCountableTopology (Mx D W.rank r) := i3
  haveI : T2Space (Mx D W.rank r) := i4
  haveI : DiscreteTopology (ratMx D W.rank r) := i5
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI : Countable D.host.E := Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin W.rank) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin W.rank → Fin r → D.host.E))
  have hsp := GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal D V V' W r C B hCB C' h1 h2 h3
  have hiso0 : isoPart V W C' (0 : Mx D W.rank r) = 0 := by
    have e := isoPart_add' V W C' (0 : Mx D W.rank r) 0
    rw [add_zero] at e
    have e' : isoPart V W C' (0 : Mx D W.rank r) + isoPart V W C' 0 = isoPart V W C' 0 + 0 := by
      rw [add_zero]; exact e.symm
    exact add_left_cancel e'
  have hpt : ∀ (y' : Mx D W.rank r) (x : WO V' W),
      heisO ψ V W (isoPart V W C y) F (isoPart V W C y' + midPart V V' W B x) =
        F (isoPart V W C (y + y') + midPart V V' W B x) := by
    intro y' x
    have z1 : symplOH V W (isoPart V W C y') (isoPart V W C y) = 0 :=
      symplOH_eq_zero_of_symplO_eq_zero V W _ _ (hsp.1 y' y)
    have z2 : symplOH V W (midPart V V' W B x) (isoPart V W C y) = 0 := by
      rw [GlobalTheory.MixModel.symplOH_skew, symplOH_eq_zero_of_symplO_eq_zero V W _ _ (hsp.2.1 y x), neg_zero]
    show ψ (symplOH V W (isoPart V W C y' + midPart V V' W B x) (isoPart V W C y)) *
        F (isoPart V W C y' + midPart V V' W B x + isoPart V W C y) = _
    rw [(GlobalTheory.OrientedFormLaws.symplOH_laws D V W).1, z1, z2, add_zero, AddChar.map_zero_eq_one, one_mul,
      isoPart_add']
    congr 1
    abel
  have hP : IsThetaFunO ψ V W (heisO ψ V W (isoPart V W C y) F) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1 _ _ hF
  let χ : Matrix (Fin W.rank) (Fin r) D.host.E → Mx D W.rank r → ℂ :=
    fun a t => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))
  let Φ : Mx D W.rank r → ℂ := fun t => κ • ∫ y' in 𝓨, ∫ x in 𝓕',
    heisO ψ V W (isoPart V W C y) F (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x) *
      star (G (isoPart V W C' t + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ
  have hterm : ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E,
      (∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV) =
        ∫ t in 𝓨, χ a t * Φ t ∂μ := fun a =>
    GlobalTheory.T.matrixCoeff_isotropicTranslates_eq_fourierCoeffs D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ F G hF hG y a
  obtain ⟨hχc, hχx, hχa, hχΓ, hχ0⟩ := GlobalTheory.T.isotropic_part_rational_characters_adelic_matrices D V V' W r C B hCB C' h1 h2 h3 ψ hψ
  obtain ⟨hΦc, hΦp⟩ := GlobalTheory.T.thetaProductMean_continuous_periodic_dualVariable D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μ' 𝓕' hμ' hF' _ G hP hG
  have hsum : Summable (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ t in 𝓨, χ a t * Φ t ∂μ‖) := by
    have e : (fun a : Matrix (Fin W.rank) (Fin r) D.host.E => ‖∫ t in 𝓨, χ a t * Φ t ∂μ‖) =
        fun a => ‖∫ w in 𝓕V, heisO ψ V W (isoPart V W C (y + a.map (incA D))) F w * star (G w) ∂μV‖ :=
      funext fun a => by rw [hterm a]
    rw [e]
    exact hs
  have key := GlobalTheory.T.fourier_inversion_zero_compact_quotient (Mx D W.rank r) (ratMx D W.rank r) K hK hKc (Matrix (Fin W.rank) (Fin r) D.host.E) χ
    hχc (fun a t s => hχx a t s) (fun a b t => hχa a b t) (fun a t => hψ.1.2.1 _) hχΓ hχ0 μ 𝓨 hμH hYF hY1 Φ
    (hΦc.const_smul κ) (fun γ hγ t => congrArg (fun z : ℂ => κ • z) (hΦp γ hγ t)) hsum
  rw [tsum_congr hterm, ← key]
  show κ • (∫ y' in 𝓨, ∫ x in 𝓕',
    heisO ψ V W (isoPart V W C y) F (isoPart V W C' 0 + isoPart V W C y' + midPart V V' W B x) *
      star (G (isoPart V W C' 0 + isoPart V W C y' + midPart V V' W B x)) ∂μ' ∂μ) = _
  simp only [hiso0, zero_add]
  simp_rw [hpt]

private theorem symplOH_eq_zero_of_symplO_eq_zero' {D : D7} (S T : HSp D) (a b : WO S T) (h : symplO S T a b = 0) :
    symplOH S T a b = 0 := by
  have h2 : (2 : AF D.host.F) * symplOH S T a b = 0 := by
    rw [two_mul, (GlobalTheory.OrientedFormLaws.symplOH_laws D S T).2.2.2.1 a b, h]
  have hu : IsUnit (2 : AF D.host.F) := by
    have e : (algebraMap D.host.F (AF D.host.F)) 2 = 2 := map_ofNat _ 2
    rw [← e]
    exact (IsUnit.mk0 (2 : D.host.F) two_ne_zero).map _
  exact hu.mul_right_eq_zero.1 h2

theorem coef_unfold : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (μV : Measure (WO V W)) (𝓕V : Set (WO V W)), μV.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕V μV → ∀ (μ' : Measure (WO V' W)) (𝓕' : Set (WO V' W)), μ'.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V') 𝓕' μ' → ∃ ν : Measure (Mx D W.rank r), ν.IsAddHaarMeasure ∧ ∀ F G, IsThetaFunO ψ V W F → IsThetaFunO ψ V W G → ∀ x : WO V' W, ∫ w in 𝓕', heisO ψ V' W x (res V V' W C B μ 𝓨 F) w * star (res V V' W C B μ 𝓨 G w) ∂μ' = ∫ y, (∫ w in 𝓕V, heisO ψ V W (isoPart V W C y + midPart V V' W B x) F w * star (G w) ∂μV) ∂ν := by
  intro D V V' W r C B hCB ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding D V V' r C B hCB
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.integral_hom_fundamental_domain_isotropic_split_coords D V V' W r C B hCB C' h1 h2 h3 μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF'
  have hY' := hY
  obtain ⟨hμH, hYF, -⟩ := hY'
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.MixModel.lattice_Mx D W.rank r
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Mx D W.rank r) := ⟨rfl⟩
  haveI := hμH
  have hc0 : ENNReal.ofReal κ⁻¹ ≠ 0 := (ENNReal.ofReal_pos.2 (inv_pos.2 hκ0)).ne'
  refine ⟨ENNReal.ofReal κ⁻¹ • μ, MeasureTheory.Measure.IsAddHaarMeasure.smul μ hc0 ENNReal.ofReal_ne_top, ?_⟩
  intro F G hF hG x
  have hsp := GlobalTheory.T.isotropicDualMiddleParts_symplectic_orthogonal D V V' W r C B hCB C' h1 h2 h3
  have hF₁ := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).1 (midPart V V' W B x) F hF
  have he : ∀ y : Mx D W.rank r, heisO ψ V W (isoPart V W C y) (heisO ψ V W (midPart V V' W B x) F) =
      heisO ψ V W (isoPart V W C y + midPart V V' W B x) F := by
    intro y
    rw [(GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ V W).2.1, symplOH_eq_zero_of_symplO_eq_zero' V W _ _ (hsp.2.1 y x),
      AddChar.map_zero_eq_one, one_smul]
  rw [← ((GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hCB ψ hψ μ 𝓨 hY).1 F hF).2.2.1 x,
    ← GlobalTheory.T.isotropicMean_thetaProduct_conj_eq_restrictionProduct D V V' W r C B hCB ψ hψ μ 𝓨 hY μ' 𝓕' hμ' hF' _ G hF₁ hG]
  simp_rw [← he]
  obtain ⟨hsum, hint⟩ := GlobalTheory.T.integral_eq_setIntegral_tsum_rationalTranslates D W.rank r μ 𝓨 hμH hYF
    (fun y => ∫ w in 𝓕V, heisO ψ V W (isoPart V W C y) (heisO ψ V W (midPart V V' W B x) F) w * star (G w) ∂μV)
    (GlobalTheory.T.integrable_matrixCoeff_adelicIsotropicPart D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ hμH μV 𝓕V hμV hFV _ G hF₁ hG)
  beta_reduce at hsum hint
  rw [MeasureTheory.integral_smul_measure, ENNReal.toReal_ofReal (inv_pos.2 hκ0).le, hint,
    ← MeasureTheory.integral_smul]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [hsum] with y hy
  rw [sum_translates_eq D V V' W r C B hCB C' h1 h2 h3 ψ hψ μ 𝓨 hY μV 𝓕V hμV hFV μ' 𝓕' hμ' hF' κ hκ _ G hF₁ hG y hy,
    smul_smul, inv_mul_cancel₀ hκ0.ne', one_smul]

end GlobalTheory.CoefUnfold

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictionWeilDataTwistCharacterTrivialSplitPla
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HalfAverage
variable {D : D7}
theorem mt_mul'' (V : HSp D) (g h : GA D V) :
    Formalism.L2.Theta.mt V (g * h) = Formalism.L2.Theta.mt V g * Formalism.L2.Theta.mt V h := by
  unfold Formalism.L2.Theta.mt; rw [map_mul]; rfl

theorem mt_one'' (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  unfold Formalism.L2.Theta.mt; rw [map_one]; rfl
end GlobalTheory.HalfAverage

namespace GlobalTheory.HalfAverage

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

variable {D : D7}

theorem res_add {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    {F G : WO V W → ℂ} (hF : ∀ x, IntegrableOn (fun y => F (isoPart V W C y + midPart V V' W B x)) 𝓨 μ)
    (hG : ∀ x, IntegrableOn (fun y => G (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) :
    res V V' W C B μ 𝓨 (F + G) = res V V' W C B μ 𝓨 F + res V V' W C B μ 𝓨 G :=
  funext fun x => integral_add (hF x) (hG x)

theorem res_smul {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)}
    (a : ℂ) (F : WO V W → ℂ) : res V V' W C B μ 𝓨 (a • F) = a • res V V' W C B μ 𝓨 F :=
  funext fun x => integral_const_mul a _

theorem res_zero {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
    {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E} {μ : Measure (Mx D W.rank r)} {𝓨 : Set (Mx D W.rank r)} :
    res V V' W C B μ 𝓨 (0 : WO V W → ℂ) = 0 :=
  funext fun x => integral_zero _ _

theorem heisO_add' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) (f g : WO S T → ℂ) :
    heisO ψ S T w (f + g) = heisO ψ S T w f + heisO ψ S T w g := (GlobalTheory.SplitScalar.heisL ψ S T w).map_add f g

theorem heisO_zero' (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (w : WO S T) :
    heisO ψ S T w (0 : WO S T → ℂ) = 0 := (GlobalTheory.SplitScalar.heisL ψ S T w).map_zero

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem charTwist_eq_one_at_split : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT χT' : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V W χS χT ω → IsWeilDatumO ψ V' W χS χT' ω' → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ c : GA D W →* Circle, (∀ h f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (1, h) f) = (c h : ℂ) • ω' (1, h) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f)) → ∀ e, IsSplitIdem D e → ∀ g, Formalism.L2.Theta.SuppAt e W g → c g = 1 := by
  intro D V V' W r C B hs ψ χS χT χT' ω ω' hω hω' μ 𝓨 hμ c hc e he g hg
  have hψ := hω.std
  obtain ⟨K, hKC, hKB⟩ := GlobalTheory.T.exists_leftInverse_isotropicFrame_killing_embedding D V V' r C B hs
  have hR := (GlobalTheory.T.thetaRestrictIsotropicQuotient_wittTower_properties D V V' W r C B hs ψ hψ μ 𝓨 hμ).1
  obtain ⟨ℓ', hℓ', f₀, hf₀, hA⟩ := GlobalTheory.T.exists_halfInvariantForm_isotropicAverage_ne_zero D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC hKB e he
  have hth : ∀ {f : WO V W → ℂ}, IsThetaFunO ψ V W f → ∀ u, IsThetaFunO ψ V W (heisO ψ V W u f) :=
    fun hf u => GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u
  have hee : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA]; exact he.2.1
  have hadd : ∀ u w : WO V W, IsHalf (cA D e) u → IsHalf (cA D e) w → ∀ f,
      heisO ψ V W (u + w) f = heisO ψ V W u (heisO ψ V W w f) := fun u w hu hw f =>
    GlobalTheory.SplitScalar.heisO_add_of_orth ψ V W (GlobalTheory.SplitScalar.symplO_eq_zero V W hee hu hw) f

  have hint : ∀ f, IsThetaFunO ψ V W f → Integrable (fun t : halfMx (cA D e) W.rank r =>
      ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f))) (haarHalf (cA D e) W.rank r) := by
    intro f hf
    obtain ⟨L, Kc, hL, hKc, h0, hloc⟩ := GlobalTheory.T.thetaRestriction_complement_translates_locallyConstant D ψ hψ V V' W r C B hs μ 𝓨 hμ K hKC hKB e he f hf
    refine Continuous.integrable_of_hasCompactSupport ?_
      (HasCompactSupport.intro hKc fun t ht => by rw [h0 t ht, map_zero])
    refine IsLocallyConstant.continuous ?_
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hn : {s : halfMx (cA D e) W.rank r | s - t ∈ L} ∈ nhds t := by
      refine IsOpen.mem_nhds (hL.preimage (continuous_id.sub continuous_const)) ?_
      show t - t ∈ L
      rw [sub_self]; exact L.zero_mem
    filter_upwards [hn] with s hs
    have h1 := hloc t (s - t) hs
    rw [show t + (s - t) = s by abel] at h1
    simp only [h1]

  let P : Submodule ℂ (WO V W → ℂ) :=
    { carrier := {f | (∀ (t : halfMx (cA D e) W.rank r) x, IntegrableOn
          (fun y => heisO ψ V W (restEmb V W K t) f (isoPart V W C y + midPart V V' W B x)) 𝓨 μ) ∧
        Integrable (fun t : halfMx (cA D e) W.rank r =>
          ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) f))) (haarHalf (cA D e) W.rank r)}
      add_mem' := by
        rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
        refine ⟨fun t x => ?_, ?_⟩
        · rw [heisO_add']; exact (hf1 t x).add (hg1 t x)
        · refine (hf2.add hg2).congr (Filter.Eventually.of_forall fun t => ?_)
          simp only [Pi.add_apply, heisO_add', res_add (hf1 t) (hg1 t), map_add]
      zero_mem' := by
        refine ⟨fun t x => ?_, ?_⟩
        · rw [heisO_zero']; exact integrableOn_zero
        · simp only [heisO_zero', res_zero, map_zero]; exact integrable_zero _ _ _
      smul_mem' := by
        rintro a f ⟨hf1, hf2⟩
        refine ⟨fun t x => ?_, ?_⟩
        · rw [GlobalTheory.SplitScalar.heisO_smul]; exact (hf1 t x).const_mul a
        · refine (hf2.const_mul a).congr (Filter.Eventually.of_forall fun t => ?_)
          simp only [GlobalTheory.SplitScalar.heisO_smul, res_smul, map_smul, smul_eq_mul] }
  have hP : ∀ f, IsThetaFunO ψ V W f → f ∈ P := fun f hf => ⟨fun t x => (hR _ (hth hf _)).1 x, hint f hf⟩
  let ℓ₀ : P →ₗ[ℂ] ℂ :=
    { toFun := fun f => avgForm ψ V V' W C B μ 𝓨 K e ℓ' f.1
      map_add' := by
        rintro ⟨f, hf1, hf2⟩ ⟨g, hg1, hg2⟩
        show avgForm ψ V V' W C B μ 𝓨 K e ℓ' (f + g) = avgForm ψ V V' W C B μ 𝓨 K e ℓ' f + avgForm ψ V V' W C B μ 𝓨 K e ℓ' g
        unfold avgForm
        rw [← integral_add hf2 hg2]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [heisO_add', res_add (hf1 t) (hg1 t), map_add]
      map_smul' := by
        rintro a ⟨f, hf1, hf2⟩
        show avgForm ψ V V' W C B μ 𝓨 K e ℓ' (a • f) = a • avgForm ψ V V' W C B μ 𝓨 K e ℓ' f
        unfold avgForm
        rw [smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        simp only [GlobalTheory.SplitScalar.heisO_smul, res_smul, map_smul, smul_eq_mul] }
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hℓP : ∀ f, f ∈ P → ℓ f = avgForm ψ V V' W C B μ 𝓨 K e ℓ' f := fun f hf =>
    LinearMap.congr_fun hℓ ⟨f, hf⟩

  have hsum : ∀ {p q : WO V W}, IsHalf (cA D e) p → IsHalf (cA D e) q → IsHalf (cA D e) (p + q) :=
    fun hp hq => (halfMx (cA D e) W.rank V.rank).add_mem hp hq
  have hinv : ∀ u : WO V W, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ V W f →
      ℓ (heisO ψ V W u f) = ℓ f := by
    intro u hu f hf
    rw [hℓP _ (hP _ (hth hf u)), hℓP _ (hP f hf)]
    obtain ⟨y, x, t₀, hy, hx, ht₀, rfl⟩ := GlobalTheory.T.halfAdelicHom_decompose_isotropic_middle_complement D V V' W r C B hs K hKC hKB (cA D e) u hu
    unfold avgForm
    let t₀' : halfMx (cA D e) W.rank r := ⟨t₀, ht₀⟩
    have h1 : IsHalf (cA D e) (isoPart V W C y) := isHalf_mul hy _
    have h2 : IsHalf (cA D e) (midPart V V' W B x) := isHalf_mul hx _
    have h3 : IsHalf (cA D e) (restEmb V W K t₀) := isHalf_mul ht₀ _
    have key : ∀ t : halfMx (cA D e) W.rank r,
        ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t)
          (heisO ψ V W (isoPart V W C y + midPart V V' W B x + restEmb V W K t₀) f))) =
        ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑(t + t₀')) f)) := by
      intro t
      have h4 : IsHalf (cA D e) (restEmb V W K ↑t) := isHalf_mul t.2 _
      have h5 : IsHalf (cA D e) (restEmb V W K ↑(t + t₀')) := isHalf_mul (t + t₀').2 _
      rw [← hadd _ _ h4 (hsum (hsum h1 h2) h3)]
      have e1 : restEmb V W K ↑t + (isoPart V W C y + midPart V V' W B x + restEmb V W K t₀) =
          isoPart V W C y + (midPart V V' W B x + restEmb V W K ↑(t + t₀')) := by
        rw [show ((t + t₀' : halfMx (cA D e) W.rank r) : Mx D W.rank r) = ↑t + t₀ from rfl, restEmb_add]
        abel
      rw [e1, hadd _ _ h1 (hsum h2 h5), hadd _ _ h2 h5]
      have g1 := hth hf (restEmb V W K ↑(t + t₀'))
      have g2 := hth g1 (midPart V V' W B x)
      rw [(hR _ g2).2.2.2 y, (hR _ g1).2.2.1 x]
      exact hℓ' x hx _ (hR _ g1).2.1
    rw [integral_congr_ae (Filter.Eventually.of_forall key)]
    exact integral_add_right_eq_self (fun t : halfMx (cA D e) W.rank r =>
      ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑t) f))) t₀'

  have hmi : mt W g * mt W g⁻¹ = 1 := by rw [← mt_mul'', mul_inv_cancel, mt_one'']
  have him : mt W g⁻¹ * mt W g = 1 := by rw [← mt_mul'', inv_mul_cancel, mt_one'']
  have hdet : IsUnit (mt W g).det := Matrix.isUnit_det_of_right_inverse hmi
  set s : AE D := ((hdet.unit : (AE D)ˣ) : AE D) with hs_def
  set s' : AE D := (((hdet.unit)⁻¹ : (AE D)ˣ) : AE D) with hs'_def
  have hss : s * s' = 1 := hdet.unit.mul_inv
  have hss' : s' * s = 1 := hdet.unit.inv_mul
  have he1 : e * e = e := he.1
  let y : (AE D)ˣ := ⟨e * s + (1 - e), e * s' + (1 - e),
    by linear_combination (s * s' - s - s' + 1) * he1 + e * hss,
    by linear_combination (s' * s - s' - s + 1) * he1 + e * hss'⟩
  have hy : IsDetAt e W g y := by
    show e * s + (1 - e) = e * (mt W g).det + (1 - e)
    rw [hs_def, IsUnit.unit_spec]
  have hV1 : ∀ X : HSp D, SuppAt e X 1 := fun X i j => by
    rw [mt_one'', sub_self]; simp
  have hD1 : ∀ X : HSp D, IsDetAt e X 1 1 := fun X => by
    show (1 : AE D) = e * (mt X 1).det + (1 - e)
    rw [mt_one'', Matrix.det_one]; ring
  obtain ⟨r₁, hr₁, hsp⟩ := hω.om_split e he 1 g (hV1 V) hg 1 y (hD1 V) hy
  obtain ⟨r₂, hr₂, hsp'⟩ := hω'.om_split e he 1 g (hV1 V') hg 1 y (hD1 V') hy
  have E1 := hsp ℓ hinv f₀ hf₀
  obtain ⟨κ, hκ, hscale⟩ := GlobalTheory.T.exists_pos_integral_halfAdelicMatrix_leftMul_eq D (cA D e) W.rank r (mt W g⁻¹) (mt W g) him hmi
  have E2 : ℓ (ω (1, g) f₀) = ((c g : ℂ) * r₂ * splitFacO χS χT' 1 y * κ) * ℓ f₀ := by
    rw [hℓP _ (hP _ (hω.om_pres _ _ hf₀)), hℓP _ (hP _ hf₀)]
    unfold avgForm
    have key2 : ∀ t : halfMx (cA D e) W.rank r,
        ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K t) (ω (1, g) f₀))) =
        ((c g : ℂ) * r₂ * splitFacO χS χT' 1 y) *
          ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑(leftMul (cA D e) (mt W g⁻¹) t)) f₀)) := by
      intro t
      have hG := hth hf₀ (restEmb V W K ↑(leftMul (cA D e) (mt W g⁻¹) t))
      have hcomm : ω (1, g) (heisO ψ V W (restEmb V W K ↑(leftMul (cA D e) (mt W g⁻¹) t)) f₀) =
          heisO ψ V W (restEmb V W K ↑t) (ω (1, g) f₀) := by
        rw [hω.om_heis 1 g _ f₀ hf₀]
        congr 1
        show HMul.hMul (HMul.hMul (mt W g) (HMul.hMul (HMul.hMul (mt W g⁻¹) (t : Mx D W.rank r)) (K.map (incA D))))
          (mt V 1⁻¹) = HMul.hMul (t : Mx D W.rank r) (K.map (incA D))
        rw [inv_one, mt_one'', Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hmi, Matrix.one_mul]
      rw [← hcomm, hc g _ hG, map_smul, hsp' ℓ' hℓ' _ (hR _ hG).2.1, smul_eq_mul]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall key2), integral_const_mul,
      hscale (fun t => ℓ' (res V V' W C B μ 𝓨 (heisO ψ V W (restEmb V W K ↑t) f₀)))]
    ring

  have hχ : ((χS y : Circle) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hL : ℓ f₀ ≠ 0 := by rw [hℓP _ (hP _ hf₀)]; exact hA
  have hsf : ∀ χ' : (AE D)ˣ →* Circle, (splitFacO χS χ' 1 y : ℂ) = (χS y : ℂ) := fun χ' => by
    simp [splitFacO]
  rw [E1, hsf, hsf] at E2
  have h1 : ((r₁ : ℂ) * (χS y : ℂ)) = (c g : ℂ) * r₂ * (χS y : ℂ) * κ := mul_right_cancel₀ hL E2
  have h2 : ((c g : ℂ) * ((r₂ : ℂ) * κ)) * (χS y : ℂ) = (r₁ : ℂ) * (χS y : ℂ) := by linear_combination -h1
  have h3 := mul_right_cancel₀ hχ h2
  have hpos : (0 : ℝ) < r₂ * κ := mul_pos hr₂ hκ
  have h4 : (c g : ℂ) = ((r₁ / (r₂ * κ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, eq_div_iff (by exact_mod_cast hpos.ne'), h3]
  have hn : ‖(c g : ℂ)‖ = 1 := by
    first | exact Circle.norm_coe (c g) | exact Circle.abs_coe (c g) | exact mem_sphere_zero_iff_norm.1 (c g).2
  rw [h4, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (div_pos hr₁ hpos)] at hn
  have h5 : (c g : ℂ) = 1 := by rw [h4, hn, Complex.ofReal_one]
  exact Circle.ext (by rw [h5, Circle.coe_one])

end GlobalTheory.HalfAverage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaChainStageCartanFrameConjValuesCuspForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto

theorem conj_stage_val_mem_A0_and_cartan_frame : ∀ D : D7, ForStage D fun c _ s => ∃ (cA : GlobalTheory.Mem.Th.CptF s.V) (a : GL (Fin s.V.rank) (AE D)), GlobalTheory.Cusp.IsCartanFrame s.V cA ∧ (∀ τ, IsCartanInv (gramAt D s.V τ) (cart s.M τ)) ∧ (∀ τ, cA τ * cart s.M τ = Formalism.UG.Jpq (s.V.sig (tauE D τ)).1 (s.V.sig (tauE D τ)).2 * cA τ) ∧ GlobalTheory.Doubling.IsMaj s.V a ∧ (∀ τ, (compAt c.θ τ a.1)ᴴ * (gramAt D s.V τ * cart s.M τ) * compAt c.θ τ a.1 = 1) ∧ ∀ (u : s.CC c), ∀ v ∈ s.KF, (fun g => conj (PiLocalization₂.val u v g)) ∈ GlobalTheory.Cusp.A0 c.θ s.V cA := by
  intro D c hc j _ s hs
  obtain ⟨a, ha, hmaj⟩ := GlobalTheory.ChainOnto.RealData.exists_maj_cart c.θ hc.inf s.M
  exact ⟨GlobalTheory.ChainOnto.RealData.sortedFrame s.M hs.sigOK, a, GlobalTheory.ChainOnto.RealData.isCartanFrame_sortedFrame _ _,
    fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart _ τ, fun τ => GlobalTheory.ChainOnto.RealData.sortedFrame_cart _ _ τ, ha, hmaj,
    fun u v hv => GlobalTheory.ChainOnto.RealData.conj_multiplicityValue_mem_cuspFormsArchimedeanKFinite c.θ hc.inf s.M hs.sigOK u.1 u.2 v hv⟩

end GlobalTheory.EvenOnto

end
end

