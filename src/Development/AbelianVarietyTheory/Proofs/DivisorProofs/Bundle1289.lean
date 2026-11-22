import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1258
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0999
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VecMulMapEqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1253
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1241
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfBlockDetIntegralGLInvariantStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.absHalf_blockDet_integralGL_invariant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m k : GLw a w × GLw b w),
    k.1 ∈ GlobalTheory.LFun.KGL w a → k.2 ∈ GlobalTheory.LFun.KGL w b →
    absHalf w ((k * m).1.val.det ^ b / (k * m).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) ∧
      absHalf w ((m * k).1.val.det ^ b / (m * k).2.val.det ^ a) = absHalf w (m.1.val.det ^ b / m.2.val.det ^ a) := by
  first | exact @GlobalTheory.BCT.absHalf_blockDet_KGL_invariant | exact GlobalTheory.BCT.absHalf_blockDet_KGL_invariant | (intros; apply GlobalTheory.BCT.absHalf_blockDet_KGL_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicLineDegreeInvariantFiniteExtension
section
open NumberField IsDedekindDomain Module GlobalTheory.FlatLine Formalism.BasicNotions

namespace GlobalTheory.FlatLine

section Descent

variable {k k' : Type} [Field k] [NumberField k] [Field k'] [NumberField k'] [Algebra k k']

theorem exp_ne_zero_of_valuation_pow {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (𝔓 : HeightOneSpectrum (𝓞 k')) : ε 𝔓 ≠ 0 := by
  intro h0
  have hmem : ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 k') ∈ 𝔓.asIdeal := Ideal.absNorm_mem _
  have h2 : 𝔓.valuation k' (algebraMap (𝓞 k') k' ((Ideal.absNorm 𝔓.asIdeal : ℕ) : 𝓞 k')) < 1 := by
    rwa [HeightOneSpectrum.valuation_lt_one_iff_mem]
  have h1 := hv 𝔓 (Ideal.absNorm 𝔓.asIdeal : k)
  rw [h0, pow_zero, map_natCast] at h1
  rw [map_natCast, h1] at h2
  exact lt_irrefl _ h2

theorem mem_iff_of_valuation_pow {π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (𝔓 : HeightOneSpectrum (𝓞 k')) (x : 𝓞 k) :
    x ∈ (π 𝔓).asIdeal ↔ 𝔓.valuation k' (algebraMap k k' (x : k)) < 1 := by
  rw [hv, pow_lt_one_iff (exp_ne_zero_of_valuation_pow hv 𝔓), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := k)]

theorem eq_of_valuation_pow {π π' : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)}
    {ε ε' : HeightOneSpectrum (𝓞 k') → ℕ}
    (hv : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓)
    (hv' : ∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π' 𝔓).valuation k z ^ ε' 𝔓) :
    π = π' ∧ ε = ε' := by
  have hπ : π = π' := by
    funext 𝔓
    apply HeightOneSpectrum.ext
    ext x
    rw [mem_iff_of_valuation_pow hv, mem_iff_of_valuation_pow hv']
  refine ⟨hπ, ?_⟩
  funext 𝔓
  obtain ⟨z, hz⟩ := (π 𝔓).valuation_exists_uniformizer k
  have h := (hv 𝔓 z).symm.trans (hv' 𝔓 z)
  rw [← hπ, hz, ← WithZero.exp_nsmul, ← WithZero.exp_nsmul, WithZero.exp_inj] at h
  simpa using h

theorem lineDeg_descent : ∀ (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] [Algebra k k']
    (π : HeightOneSpectrum (𝓞 k') → HeightOneSpectrum (𝓞 k)) (ε : HeightOneSpectrum (𝓞 k') → ℕ),
    (∀ 𝔓 (z : k), 𝔓.valuation k' (algebraMap k k' z) = (π 𝔓).valuation k z ^ ε 𝔓) →
    ∀ (r : (k →+* ℂ) → ℝ) (ρ : HeightOneSpectrum (𝓞 k) → ℝ),
    (Function.support fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)).Finite →
    (Function.support ρ).Finite ∧
      lineDeg r ρ = lineDeg (fun s : k' →+* ℂ => r (s.comp (algebraMap k k'))) (fun 𝔓 => (ε 𝔓 : ℝ) * ρ (π 𝔓)) := by
  intro k k' _ _ _ _ _ π ε hv r ρ hfin
  classical
  obtain ⟨π₀, ε₀, hv₀, hsum⟩ :=
    GlobalTheory.FlatDegreeCompare.exists_under_valuation_sum_log_absNorm k k' (algebraMap k k')
  obtain ⟨hπ, hε'⟩ := eq_of_valuation_pow hv hv₀
  rw [← hπ, ← hε'] at hsum
  choose s hs hne hid using hsum
  have hε : ∀ 𝔓, ε 𝔓 ≠ 0 := exp_ne_zero_of_valuation_pow hv
  have hk : (0 : ℝ) < finrank ℚ k := by exact_mod_cast Module.finrank_pos
  have hk' : (0 : ℝ) < finrank ℚ k' := by exact_mod_cast Module.finrank_pos

  have hρ : (Function.support ρ).Finite := by
    refine (hfin.image π).subset ?_
    intro 𝔭 h𝔭
    obtain ⟨𝔓, h𝔓⟩ := hne 𝔭
    have he : π 𝔓 = 𝔭 := (hs 𝔭 𝔓).1 h𝔓
    refine ⟨𝔓, ?_, he⟩
    simp only [Function.mem_support, he]
    exact mul_ne_zero (by exact_mod_cast hε 𝔓) h𝔭
  refine ⟨hρ, ?_⟩

  have harch := GlobalTheory.finrank_mul_sum_embeddings_comp k k' (algebraMap k k') (fun σ => Real.log (r σ))
  have hA : (∑ σ : k' →+* ℂ, Real.log (r (σ.comp (algebraMap k k')))) / (finrank ℚ k' : ℝ)
      = (∑ σ : k →+* ℂ, Real.log (r σ)) / (finrank ℚ k : ℝ) := by
    rw [div_eq_div_iff hk'.ne' hk.ne']
    linarith [harch]

  have hdisj : ((hρ.toFinset : Finset (HeightOneSpectrum (𝓞 k))) : Set (HeightOneSpectrum (𝓞 k))).PairwiseDisjoint s := by
    intro a _ b _ hab
    exact Finset.disjoint_left.2 fun 𝔓 ha hb => hab (((hs a 𝔓).1 ha).symm.trans ((hs b 𝔓).1 hb))
  unfold lineDeg lw
  beta_reduce
  have h1 : Function.support (fun la : HeightOneSpectrum (𝓞 k) =>
      ρ la * (Real.log (Ideal.absNorm la.asIdeal) / (finrank ℚ k : ℝ))) ⊆ ↑hρ.toFinset := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    simp only [Finset.mem_coe, Set.Finite.mem_toFinset, Function.mem_support, not_not] at hx
    simp [hx]
  have h2 : Function.support (fun la : HeightOneSpectrum (𝓞 k') =>
      (ε la : ℝ) * ρ (π la) * (Real.log (Ideal.absNorm la.asIdeal) / (finrank ℚ k' : ℝ)))
      ⊆ ↑(hρ.toFinset.biUnion s) := by
    refine Function.support_subset_iff'.2 fun x hx => ?_
    have h0 : ρ (π x) = 0 := by
      by_contra h
      apply hx
      simp only [Finset.coe_biUnion, Set.mem_iUnion, Finset.mem_coe, Set.Finite.mem_toFinset,
        Function.mem_support]
      exact ⟨π x, h, (hs _ _).2 rfl⟩
    simp [h0]
  rw [finsum_eq_sum_of_support_subset _ h1, finsum_eq_sum_of_support_subset _ h2, hA,
    Finset.sum_biUnion hdisj]
  congr 1
  refine Finset.sum_congr rfl fun 𝔭 _ => ?_
  have e1 : ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * ρ (π 𝔓) * (Real.log (Ideal.absNorm 𝔓.asIdeal) / (finrank ℚ k' : ℝ))
      = ρ 𝔭 / (finrank ℚ k' : ℝ) * ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun 𝔓 h => ?_
    rw [(hs 𝔭 𝔓).1 h]
    ring
  have hS : ∑ 𝔓 ∈ s 𝔭, (ε 𝔓 : ℝ) * Real.log (Ideal.absNorm 𝔓.asIdeal)
      = (finrank ℚ k' : ℝ) * Real.log (Ideal.absNorm 𝔭.asIdeal) / (finrank ℚ k : ℝ) := by
    rw [eq_div_iff hk.ne']
    linarith [hid 𝔭]
  rw [e1, hS]
  field_simp

end Descent

end GlobalTheory.FlatLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorOfAnnihilatorLe
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory

theorem LKMid.Pair.term_one_eq_pointSum : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (Kf : Subgroup G.GAf) (f : G.GAf → ℂ) (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), (∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g) → (∀ k ∈ K', ∀ g, f' (k⁻¹ * g * sigG G 1 k) = f' g) → ∀ (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t), P.term Kf f 1 K' f' = pointSum (P.toAf x t hx) (P.toQr 1 1) (MonoidHom.id (Gr G 1)) Kf K' (P.toAf x t hx P.self) (inclG G 1 P.atP) f f' := by
  intro p _ G P Kf f K' f' hf hf' x t hx
  have hN : IsNrm G 1 P.atP (inclG G 1 P.atP) 1 := (GlobalTheory.nrm_exact p G).2 P.atP
  have hsig : sigG G 1 = MonoidHom.id (Gr G 1) := by
    ext1 g
    exact (GlobalTheory.LKMid.SigIter.main p G 1 Nat.one_pos).1 g
  rw [GlobalTheory.T.kottwitzPair_term_eq_pointSum_any_trivialisation p G P Kf f 1 K' f' Nat.one_pos hf hf' x t hx (inclG G 1 P.atP) 1 hN]
  unfold Pair.termAt
  rw [hsig]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanNormSquareBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.CM GlobalTheory.FlatDegreeCompare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_norm_square_base_change : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k k' : Type) [Field k] [NumberField k] [Field k'] [NumberField k'] (i : k →+* k') (t : SAB H (Sp k)) (t' : SAB H (Sp k')) (n : SABMap t' t (spMap i)) (m : ℕ) (x : Fin m → (epsR k ⟶ t.G)) (x' : Fin m → (epsR k' ⟶ t'.G)) (σ : k' →+* ℂ) (N : ℝ), (∀ a, IsVecOver i n.φ (x a) (x' a)) → AdelicDegreeTameRamification.IsArchNormSq t x (σ.comp i) N → AdelicDegreeTameRamification.IsArchNormSq t' x' σ N := by
  first | exact @GlobalTheory.FlatDegreeCompare.isArchNormSq_up | exact GlobalTheory.FlatDegreeCompare.isArchNormSq_up | (intros; apply GlobalTheory.FlatDegreeCompare.isArchNormSq_up <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithHeightsAndFormsOfIntersectionAndInductiveStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithHeightsAndForms_of_intersection_and_inductive : GlobalTheory.Published.ArFormExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.ArExists := by
  first | exact @GlobalTheory.Published.arExists_of_form_of_mix | exact GlobalTheory.Published.arExists_of_form_of_mix | (intros; apply GlobalTheory.Published.arExists_of_form_of_mix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterChangeOfMetricOfMixedInductiveStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithInterChangeOfMetric_of_mixedInductive : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArMix → GlobalTheory.Published.ArMetric := by
  first | exact @GlobalTheory.Published.arMetric_of_arMix | exact GlobalTheory.Published.arMetric_of_arMix | (intros; apply GlobalTheory.Published.arMetric_of_arMix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithSelfInterConstantShiftOfTrivialWeightFormulStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithSelfInter_constantShift_of_trivialWeightFormula : GlobalTheory.Published.ArExists → GlobalTheory.Published.ArChange → GlobalTheory.Published.ArShift := by
  first | exact @GlobalTheory.Published.arShift_of_arChange | exact GlobalTheory.Published.arShift_of_arChange | (intros; apply GlobalTheory.Published.arShift_of_arChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AsymptoticRiemannRochAmpleCoherentStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.asymptotic_riemannRoch_ample_coherent : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, IsAmpleLB L → ∃ C m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → |(d.factorial : ℤ) * (hdim k (twist F (lbPow L m)) 0 : ℤ) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  first | exact @GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB | exact GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB | (intros; apply GlobalTheory.abs_factorial_mul_hdim_zero_twist_sub_le_of_isAmpleLB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockLevelsEqIntegralGLOfUnramifiedStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockLevels_eq_integralGL_of_unramified : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (μ : (w.adicCompletion E)ˣ →* ℂˣ), (∀ u ∈ GlobalTheory.LFun.KGL w 1, μ (GeneralLinearGroup.det u) = 1) →
    lev₁ h w (GlobalTheory.LFun.KGL w n) μ = GlobalTheory.LFun.KGL w a ∧ lev₂ h w (GlobalTheory.LFun.KGL w n) μ = GlobalTheory.LFun.KGL w b := by
  first | exact @GlobalTheory.BCT.CtLevel.lev_KGL_of_unram | exact GlobalTheory.BCT.CtLevel.lev_KGL_of_unram | (intros; apply GlobalTheory.BCT.CtLevel.lev_KGL_of_unram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockUpperTimesUnipotentMulBlockDiagonalStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blockUpperTimesUnipotent_mul_blockDiagonal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (m k : GLw a w × GLw b w) (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)),
    blk h w (k * m) X = dgM h w k * blk h w m X ∧
      blk h w (m * k) X = blk h w m (k.1.val * X * (k.2⁻¹).val) * dgM h w k := by
  first | exact @GlobalTheory.BCT.CtLevel.blk_mul_dgM | exact GlobalTheory.BCT.CtLevel.blk_mul_dgM | (intros; apply GlobalTheory.BCT.CtLevel.blk_mul_dgM <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerInfConjIntegralGLProdLeCptPartStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_inf_conj_integralGLProd_le_cptPart : ∀ (E : Type) [Field E] [NumberField E] (a b : ℕ) (w : Pl E) (m q : GLw a w × GLw b w), twCent (MonoidHom.id _) m ⊓ ((GlobalTheory.LFun.KGL w a).prod (GlobalTheory.LFun.KGL w b)).map (MulAut.conj q).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) m) := by
  first | exact @GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart | exact GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart | (intros; apply GlobalTheory.CentCpt.twCent_inf_conjKK_le_cptPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralizerRegularRationalPointFiniteAdelicCommStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralizer_regular_rationalPoint_finiteAdelic_comm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (γ : UE E n), γ.1.val.charpoly.Separable → ∀ a ∈ twCent (MonoidHom.id (finU E n)) (finPt γ), ∀ b ∈ twCent (MonoidHom.id (finU E n)) (finPt γ), a * b = b * a := by
  first | exact @GlobalTheory.BCT.finCent_comm | exact GlobalTheory.BCT.finCent_comm | (intros; apply GlobalTheory.BCT.finCent_comm <;> assumption)
end

