import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0062
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingArchimedeanComponents
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemUnipOfArchFrame
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0061
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0027
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0350
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.WeilBound.CoreStatements.MeasureExistence.ExistsMeas
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0385
import Development.AutomorphicSpectrum.Definitions.TwistedFlags.OneMemOffK
import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0937
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0051
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0043
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.Bundle0070
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleOfJhMultEqOne
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsClassificationCuspidalSupport
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LanglandsDistinctCuspidalPairEmbedding
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsIrreducibleOfClsGLEqSingle
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0424
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0044

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdelicCharacterOrthogonalIsRationalStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_character_orthogonal_is_rational : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ x : AF F, (∀ t : F, ψ (algebraMap F (AF F) t * x) = 1) → ∃ c : F, x = algebraMap F (AF F) c := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Ann.annihilator_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsConjMemMajCptFrame
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.GoodPos

theorem exists_conj_mem_majCpt_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ c : (∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E)), (∀ w, ∃ ε : Fin n → Bool, Formalism.UG.cT (sigR _ σ) (c w).1 * JR w.Completion J * (c w).1 =
        Matrix.diagonal fun i => if ε i then 1 else -1) →
    ∀ (S : Finset (Fin r)) (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      1 ≤ d → (∀ j : Fin r, l ≤ j.val → j.val + 1 < l + d → j ∉ S) → (∃ k ∈ S, k.val + 1 = l + d) →
      (l = 0 ∨ ∃ p ∈ S, p.val + 1 = l) →
      ∃ u ∈ GlobalTheory.StdPar.unip σ J Xf S, u ∈ infPts σ J ∧ ∃ y : GL (Fin d) (GlobalTheory.CuspRep.Cinf E),
        ∀ k : GlobalTheory.CuspRep.Kinf E d, (u * ι (GlobalTheory.CuspRep.infGL E d y)) * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) *
          (u * ι (GlobalTheory.CuspRep.infGL E d y))⁻¹ ∈ majCpt σ J c := by
  intro F E _ _ _ _ _ _ σ hCM n J hJ r Xf Yf hW c hc S l d h ι hι hd hS1 hS2 hS3
  obtain ⟨ρ, hρs, hρlift, hρι⟩ := GlobalTheory.BlockForms.exists_archComp_of_isBlockEmb F E σ hCM n J r Xf Yf l d h ι hι
  have loc := fun w => stab_of_frame F E σ hCM n J hJ r Xf Yf hW w (c w) (hc w) l d h
  choose uw N hN hNX hNv y₀ hy₀ using loc
  set u : GAd σ J := ofInf σ J (embArchPi σ J uw) with hu
  have hu_arch : ∀ w, projArch σ J w u = uw w := fun w => by
    rw [hu, projArch_ofInf, projInfArch_embArchPi]
  have hu_inf : u ∈ infPts σ J := mem_infPts.2 (projFin_ofInf _ _ _)
  obtain ⟨y, hy⟩ := hρlift y₀
  obtain ⟨k₀, hk₀S, hk₀⟩ := hS2
  refine ⟨u, mem_unip_of_arch_frame F E σ n J r Xf S u hu_inf fun w => ⟨N w, by rw [hu_arch]; exact hN w, fun i j hij => ?_,
    fun v hv => ?_⟩, hu_inf, y, fun k => ?_⟩
  · rcases hNX w i j hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hS3 with h0 | ⟨p, hpS, hp⟩
      · omega
      · exact ⟨p, hpS, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩
    · exact ⟨k₀, hk₀S, by rw [Fin.le_def]; omega, by rw [Fin.lt_def]; omega⟩
  · obtain ⟨a, ha, hav⟩ := hNv w v fun i hi => hv i ⟨k₀, hk₀S, by rw [Fin.le_def]; omega⟩
    exact ⟨a, fun i hi => ⟨k₀, hk₀S, by have := ha i hi; rw [Fin.le_def]; omega⟩, by rw [hu_arch]; exact hav⟩
  · have e : (u * ι (GlobalTheory.CuspRep.infGL E d y)) * ι (GlobalTheory.CuspRep.infGL E d (Unitary.toUnits k)) *
        (u * ι (GlobalTheory.CuspRep.infGL E d y))⁻¹ = u * ι (GlobalTheory.CuspRep.infGL E d (y * Unitary.toUnits k * y⁻¹)) * u⁻¹ := by
      simp only [map_mul, map_inv]; group
    rw [e, mem_majCpt]
    refine ⟨mul_mem (mul_mem hu_inf (hρι _).1) (inv_mem hu_inf), fun w => ?_⟩
    rw [map_mul, map_mul, map_inv, hu_arch]
    refine hy₀ w (Matrix.GeneralLinearGroup.map (ρ w) (Unitary.toUnits k)) ?_ _ ?_
    · have hk : star (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) * (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)) = 1 :=
        Unitary.star_mul_self_of_mem k.2
      have e1 : Formalism.UG.cT (sigR w.Completion σ) ((Matrix.GeneralLinearGroup.map (ρ w) (Unitary.toUnits k)).1) =
          (star (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E))).map (ρ w) := by
        ext i j
        simp [Formalism.UG.cT, Matrix.star_apply, hρs]
      rw [e1]
      change _ * (k : Matrix (Fin d) (Fin d) (GlobalTheory.CuspRep.Cinf E)).map (ρ w) = 1
      rw [← Matrix.map_mul, hk, Matrix.map_one _ (map_zero _) (map_one _)]
    · rw [(hρι _).2 w]
      simp only [map_mul, map_inv, hy w]

end GlobalTheory.CompanionTheory.GoodPos
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSchwartzBruhatCompactSupportNonzeroStatement
section
open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartzBruhat_compact_support_nonzero : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι], ∃ f ∈ schwartzBruhatPi F ι, HasCompactSupport f ∧ f 0 ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero | exact GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CompactTest.exists_compactSupport_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteDimensionalOfEmbedding
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR.Mult MeasureTheory NumberField Matrix
open scoped TensorProduct Topology InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspFin

open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.Cusp GlobalTheory.AutMult GlobalTheory.DiscreteSum GlobalTheory.Orb GlobalTheory.AdelicU GlobalTheory.SplitWeil

theorem le_re_inner_of_isRepOp {G H : Type} [Group G] [MeasurableSpace G] [TopologicalSpace G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : G →* (H →L[ℂ] H)} {μ : Measure G} {φ : G → ℝ} {T : H →L[ℂ] H}
    (hT : IsRepOp π μ (fun g => (φ g : ℂ)) T) (hφ : Integrable φ μ) (h0 : 0 ≤ φ) {N : Set G}
    (hs : Function.support φ ⊆ N) (u : H) (c : ℝ) (hc : ∀ g ∈ N, c ≤ (⟪u, π g u⟫_ℂ).re) :
    c * ∫ g, φ g ∂μ ≤ (⟪u, T u⟫_ℂ).re := by
  have hi := (hT u).1
  have hin : Integrable (fun g => ⟪u, (φ g : ℂ) • π g u⟫_ℂ) μ := hi.const_inner u
  have e : (⟪u, T u⟫_ℂ).re = ∫ g, (⟪u, (φ g : ℂ) • π g u⟫_ℂ).re ∂μ := by
    rw [(hT u).2, ← integral_inner hi u]
    exact (integral_re hin).symm
  rw [e, ← integral_const_mul]
  refine integral_mono (hφ.const_mul c) hin.re fun g => ?_
  simp only [inner_smul_right, Complex.re_ofReal_mul]
  by_cases hg : φ g = 0
  · simp [hg]
  · rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hc g (hs hg)) (h0 g)

variable {D : D7} {V : HSp D}

theorem exists_bump (μ : Measure (GA D V)) [μ.IsHaarMeasure] {N : Set (GA D V)} (hN : N ∈ 𝓝 (1 : GA D V)) :
    ∃ φ : GA D V → ℝ, (fun g => (φ g : ℂ)) ∈ CcGA V ∧ 0 ≤ φ ∧ Function.support φ ⊆ N ∧ Integrable φ μ ∧
      0 < ∫ g, φ g ∂μ := by
  obtain ⟨φ, hφ, h0, h1, hs⟩ : ∃ φ : GA D V → ℝ, (fun g => (φ g : ℂ)) ∈ CcGA V ∧ 0 ≤ φ ∧ φ 1 = 1 ∧
      Function.support φ ⊆ N := GlobalTheory.CuspSpectrum.exists_bump_ccAd (isCMExt_host D) hN
  have hc := continuous_of_mem_ccAd hφ
  have hφc : Continuous φ := Complex.continuous_re.comp hc.1
  have hφs : HasCompactSupport φ := hc.2.comp_left (g := Complex.re) rfl
  exact ⟨φ, hφ, h0, hs, hφc.integrable_of_hasCompactSupport hφs,
    hφc.integral_pos_of_hasCompactSupport_nonneg_nonzero hφs h0 (x := 1) (by rw [h1]; exact one_ne_zero)⟩

theorem finiteDimensional_of_coercive (hP : GlobalTheory.Published.CuspDecayBound) (μ : Measure (GA D V)) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (Sb : Submodule ℂ (L2cusp V μ)) {N : Set (GA D V)} (hN : N ∈ 𝓝 (1 : GA D V))
    (h : ∀ g ∈ N, ∀ u ∈ Sb, (1 / 2 : ℝ) * ‖u‖ ^ 2 ≤ (⟪u, Rcusp V μ g u⟫_ℂ).re) : FiniteDimensional ℂ Sb := by
  obtain ⟨φ, hf, h0, hs, hi, hpos⟩ := exists_bump μ hN
  have hrep := GlobalTheory.CuspSpectrum.isRepOp_RcuspOp (μ := μ) hf
  refine GlobalTheory.T.finiteDimensional_of_isCompactOperator_coercive (L2cusp V μ) (RcuspOp V μ _)
    (isCompactOperator_of_isHilbertSchmidt (GlobalTheory.CuspHS.isHilbertSchmidt_RcuspOp hP hf)) Sb
    ((1 / 2) * ∫ g, φ g ∂μ) (by positivity) fun u hu => ?_
  have := le_re_inner_of_isRepOp hrep hi h0 hs u ((1 / 2 : ℝ) * ‖u‖ ^ 2) fun g hg => h g hg u hu
  calc _ = (1 / 2 : ℝ) * ‖u‖ ^ 2 * ∫ g, φ g ∂μ := by ring
    _ ≤ _ := this

end GlobalTheory.CompanionTheory.CuspFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
section
namespace GlobalTheory.CompanionTheory.GeoLink

theorem geometricLemma : GlobalTheory.Published.GeometricLemma := by
  intro k _ _ _ _
  have h := GlobalTheory.T.induced_cell_semisimplification k
  have hloc := GlobalTheory.T.jacquetOfInducedFiltration' k
  first
    | exact h hloc
    | exact h.mpr hloc
    | exact ⟨h, hloc⟩
    | exact ⟨hloc, h⟩
    | exact hloc.mpr h
    | exact hloc h
    | exact hloc

end GlobalTheory.CompanionTheory.GeoLink
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MemAnnihilatorSmallBallEventuallyStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_annihilator_box_product : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ S : Finset (HeightOneSpectrum (𝓞 F)), (∀ v, v ∉ S → annV ψ v (v.adicCompletionIntegers F : Set (Fv F v)) = (v.adicCompletionIntegers F : Set (Fv F v))) → ∀ U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v), (∀ v, (0 : Fv F v) ∈ U v) → annF ψ (Coef.boxA S U) = Coef.boxA S (fun v => annV ψ v (U v)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | exact GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Test.annF_boxA <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TotallyDisjointProductIrreducibleOfPolynomialRin
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TDZ

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.JHMult
open GlobalTheory.CompanionTheory.Hypotheses₂.TD

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem commute_pair (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hZ : ZelevinskyPolynomialRing) (g : Fin 2 → IrrGL k) (h0 : (g 0).IsCusp) (h1 : (g 1).IsCusp)
    (hU : ∀ j : ℤ, |j| ≤ 1 → g 0 ≠ (g 1).nu (j : ℂ)) {n : Type} [Fintype n] [DecidableEq n]
    (f : (Σ i, Fin (g i).1) ≃ n) (f' : (Σ i, Fin (g (Equiv.swap 0 1 i)).1) ≃ n) :
    Nonempty ((multiProd f fun i => (g i).rep).Equiv (multiProd f' fun i => (g (Equiv.swap 0 1 i)).rep)) := by
  let σ : ∀ i, Irr k (g i).1 := fun i => Irr.ofIrrRep (g i).2.rep
  have hc : ∀ i, (g i).IsCusp := fun i => by
    fin_cases i
    · exact h0
    · exact h1
  have i1 : (multiProd f fun i => (σ i).π).IsIrreducible :=
    isIrreducible_multiProd_of_prod₂ (fun i => (g i).1) σ
      (GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.isIrreducible_prod₂_of_polynomialRing hG hBZ hZ k (g 0) (g 1) h0 h1 hU) f
  have g0 : g (Equiv.swap 0 1 0) = g 1 := by simp
  have g1 : g (Equiv.swap 0 1 1) = g 0 := by simp
  have i2 : (multiProd f' fun i => (σ (Equiv.swap 0 1 i)).π).IsIrreducible :=
    isIrreducible_multiProd_of_prod₂ (fun i => (g (Equiv.swap 0 1 i)).1) (fun i => σ (Equiv.swap 0 1 i))
      (GlobalTheory.CompanionTheory.Hypotheses₂.RankOne.isIrreducible_prod₂_of_polynomialRing hG hBZ hZ k _ _ (hc _) (hc _) (by
        rw [g0, g1]
        exact unlinked_symm hU)) f'
  refine GlobalTheory.CompanionTheory.Hypotheses₂.TDSwap.swap_equiv_of_irreducible hG hBZ k n (fun i => (g i).1) σ
    (fun i => ⟨(hc i).1, (hc i).2⟩) ?_ f f' i1 i2
  show IrrGL.of (g 0).rep (g 0).2.rep.smooth (g 0).2.rep.irr ≠ IrrGL.of (g 1).rep (g 1).2.rep.smooth (g 1).2.rep.irr
  rw [IrrGL.of_rep, IrrGL.of_rep]
  have := hU 0 (by simp)
  simpa using this

theorem occurs (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hZ : ZelevinskyPolynomialRing) {d : Fin 2 → ℕ}
    (p : ∀ i, Irr k (d i)) {A : Fin 2 → Multiset (IrrGL k)} (hA : ∀ i, HasSupport (p i).π (A i))
    (hAB : ∀ x ∈ A 0, x ∉ A 1) (hU : ∀ x ∈ A 0, ∀ y ∈ A 1, ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ))
    (e : (Σ i, Fin (d i)) ≃ Fin (d 0 + d 1)) (Q : Irr k (d 0 + d 1))
    (hQ : IsSubquotient Q.π (multiProd e fun i => (p i).π)) :
    IsSubquotient (piTensor fun i => (p i).π) (jac e Q.π) := by
  classical
  obtain ⟨s, u, e₃, hc, φ, hφ⟩ := GlobalTheory.CompanionTheory.CuspEmbed.main hBZ hG k _ Q
  have hS₁ : HasSupport Q.π (Finset.univ.val.map u) :=
    ⟨s, u, rfl, Q.irr, fun a => ⟨(hc a).1, (u a).2.rep.irr, (hc a).2⟩, e₃, .of_injective φ hφ⟩
  have hd : ∑ i, d i = d 0 + d 1 := Fin.sum_univ_two d
  have hS₂ : HasSupport Q.π (A 0 + A 1) := by
    obtain ⟨φ'⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ e (stdBlocks d hd) _).1
      (piTensor fun i => (p i).π)
    let ψ := φ'.trans (prodIrrEquiv hd (fun i => (p i).π) (fun i => (p i).smooth) fun i => (p i).irr)
    have h := hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (p i).π (p i).smooth (p i).irr)
      (fun i => (hA i).of_equiv (IrrGL.equivOf _ _ _)) Q.irr
      (hQ.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
    rwa [Fin.sum_univ_two] at h
  have hm : Finset.univ.val.map u = A 0 + A 1 := hasSupport_unique hG hBZ hS₁ hS₂
  let S : Finset (Fin s) := Finset.univ.filter fun a => u a ∈ A 1
  let σ : ∀ a, Irr k (u a).1 := fun a => Irr.ofIrrRep (u a).2.rep
  have mem : ∀ a, u a ∈ A 0 ∨ u a ∈ A 1 := fun a =>
    Multiset.mem_add.1 (hm ▸ Multiset.mem_map_of_mem u (Finset.mem_univ a))
  have mem1 : ∀ a, a ∈ S → u a ∈ A 1 := fun a ha => (Finset.mem_filter.1 ha).2
  have mem0 : ∀ a, a ∉ S → u a ∈ A 0 := fun a ha =>
    (mem a).resolve_right fun h => ha (Finset.mem_filter.2 ⟨Finset.mem_univ _, h⟩)
  have mS : S.val.map u = A 1 := by
    have h : S.val.map u = (Finset.univ.val.map u).filter (· ∈ A 1) := by
      rw [Multiset.filter_map]
      rfl
    rw [h, hm, Multiset.filter_add, Multiset.filter_eq_nil.2 (fun x hx => hAB x hx),
      Multiset.filter_eq_self.2 (fun x hx => hx), zero_add]
  have mC : Sᶜ.val.map u = A 0 := by
    have h : Sᶜ.val.map u = (Finset.univ.val.map u).filter (· ∉ A 1) := by
      rw [Multiset.filter_map, Finset.compl_filter]
      rfl
    rw [h, hm, Multiset.filter_add, Multiset.filter_eq_self.2 (fun x hx => hAB x hx),
      Multiset.filter_eq_nil.2 (fun x hx h => h hx), add_zero]
  have deg : ∀ (T : Finset (Fin s)) (C : Multiset (IrrGL k)), T.val.map u = C →
      ∑ a : Fin T.card, (u (T.orderEmbOfFin rfl a)).1 = (C.map Sigma.fst).sum := by
    intro T C h
    rw [← h, ← map_orderEmb T u, Multiset.map_map]
    rfl
  have c₁ : Fintype.card (Σ a : Fin Sᶜ.card, Fin (u (Sᶜ.orderEmbOfFin rfl a)).1) = Fintype.card (Fin (d 0)) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [deg _ _ mC, (hA 0).sum_fst, Fintype.card_fin]
  have c₂ : Fintype.card (Σ a : Fin S.card, Fin (u (S.orderEmbOfFin rfl a)).1) = Fintype.card (Fin (d 1)) := by
    rw [Fintype.card_sigma]
    simp only [Fintype.card_fin]
    rw [deg _ _ mS, (hA 1).sum_fst, Fintype.card_fin]
  let e₁ := Fintype.equivOfCardEq c₁
  let e₂ := Fintype.equivOfCardEq c₂
  obtain ⟨Φ⟩ := GlobalTheory.T.parabolicProduct_equiv_product_of_partition k s (fun a => (u a).1) σ S (d 0) (d 1) e₃ e₁ e₂
    (fun a b ha hb n _ _ f f' => commute_pair hG hBZ hZ (fun i => u (![a, b] i)) (hc a) (hc b)
      (hU _ (mem0 a ha) _ (mem1 b hb)) f f')
  have hsupp : ∀ (T : Finset (Fin s)) (C : Multiset (IrrGL k)), T.val.map u = C → ∀ (n : ℕ)
      (f : (Σ a : Fin T.card, Fin (u (T.orderEmbOfFin rfl a)).1) ≃ Fin n)
      (y : IrrRep (GL (Fin n) k)), IsSubquotient y.ρ (multiProd f fun a => (σ (T.orderEmbOfFin rfl a)).π) →
      HasSupport y.ρ C := by
    intro T C hT n f y hy
    refine ⟨T.card, fun a => u (T.orderEmbOfFin rfl a), ?_, y.irr,
      fun a => ⟨(hc _).1, (u _).2.rep.irr, (hc _).2⟩, f, hy⟩
    rw [map_orderEmb, hT]
  exact occurs_of_prod₂ hG hBZ p hA hAB e Q hQ
    ⟨_, multiProd e₁ fun a => (σ (Sᶜ.orderEmbOfFin rfl a)).π, isSmooth_parInd _ _⟩
    ⟨_, multiProd e₂ fun a => (σ (S.orderEmbOfFin rfl a)).π, isSmooth_parInd _ _⟩
    (hsupp _ _ mC _ e₁) (hsupp _ _ mS _ e₂) (Φ.toIntertwiningMap.comp φ) (Φ.toLinearEquiv.injective.comp hφ)

theorem isIrreducible_prod₂ (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness)
    (hZ : ZelevinskyPolynomialRing) {r t : ℕ} (π₁ : Irr k r) (π₂ : Irr k t)
    {A₀ A₁ : Multiset (IrrGL k)} (H₁ : HasSupport π₁.π A₀) (H₂ : HasSupport π₂.π A₁)
    (hU : ∀ x ∈ A₀, ∀ y ∈ A₁, ∀ j : ℤ, |j| ≤ 1 → x ≠ y.nu (j : ℂ)) :
    (prod₂ π₁.π π₂.π).IsIrreducible := by
  have hAB : ∀ x ∈ A₀, x ∉ A₁ := fun x hx hx' => hU x hx x hx' 0 (by simp) (by simp)
  let dd : Fin 2 → ℕ := ![r, t]
  let p : ∀ i, Irr k (dd i) := fun i =>
    Fin.cases (motive := fun i => Irr k (dd i)) π₁
      (fun j => Fin.cases (motive := fun j : Fin 1 => Irr k (dd j.succ)) π₂ (fun l => l.elim0) j) i
  let A : Fin 2 → Multiset (IrrGL k) := ![A₀, A₁]
  have hA : ∀ i, HasSupport (p i).π (A i) := by
    intro i
    fin_cases i
    · exact H₁
    · exact H₂
  have hd : ∑ i, dd i = dd 0 + dd 1 := Fin.sum_univ_two dd
  have hirr := isIrreducible_of_occurs hG hBZ p hA hAB (stdBlocks dd hd)
    (fun Q hQ => occurs hG hBZ hZ p hA hAB hU (stdBlocks dd hd) Q hQ)
  obtain ⟨E⟩ := GlobalTheory.LocGL.nonempty_prod₂_equiv_multiProd hd fun i => (p i).π
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E.symm hirr

end GlobalTheory.CompanionTheory.Hypotheses₂.TDZ

theorem GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_polynomialRing :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness →
      GlobalTheory.Published.ZelevinskyPolynomialRing → GlobalTheory.Published.TotallyDisjointProductIrreducible := by
  intro hG hBZ hZ k _ _ _ _ r t s s' π₁ π₂ d d' σ σ' h₁ h₂ hdis
  refine GlobalTheory.CompanionTheory.Hypotheses₂.TDZ.isIrreducible_prod₂ hG hBZ hZ π₁ π₂ (GlobalTheory.LocGL.hasSupport_of_isCuspSupport h₁)
    (GlobalTheory.LocGL.hasSupport_of_isCuspSupport h₂) ?_
  intro x hx y hy j hj heq
  obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
  obtain ⟨b, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨hpq, hn⟩ := GlobalTheory.CompanionTheory.Hypotheses₂.TD.exists_equiv_of_eq_nu (σ a) (σ' b) j heq
  exact hdis a b hpq j hj hn

theorem GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_parts :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.SegmentRepresentation →
      GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.TotallyDisjointProductIrreducible :=
  fun hG hS hP => GlobalTheory.CompanionTheory.Hypotheses₂.totallyDisjointProductIrreducible_of_polynomialRing hG
    GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness
    (GlobalTheory.zelevinskyPolynomialRing_of_parts GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness hS hP)

end
end

