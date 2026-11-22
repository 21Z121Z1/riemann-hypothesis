import Mathlib
import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FdOfCharts
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NatCastMemOfPlace
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepComb
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PeriodLatticeFinitelyGenerated
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.SelfDualLatticeNorms.SelfDualComap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0167
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0168
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalLabelOperatorsOnHyperspecialFixedVector
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0106
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0158
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0102
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0169
import Formalism.LocalToGlobal.KernelLattices.KerStd
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.PeriodRelations.ConjCls
import Formalism.LocalToGlobal.GlobalTheory.GL3.CubicFields.WeierstrassUniqueness.Bundle0001
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.Bundle0005
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.ParConsts
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.LocalLevelIsKOneAtT
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0004
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PadicNormTwoHundredSixteenEqOneOfFiveLe

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCommonScaleLatticePairsSplitPrime
section
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G.Pend Formalism.L2.Ker Formalism.L2.PairingIndexBounds.F GlobalTheory.TwU TensorProduct
open Formalism.L2.Th1.H Formalism.L2.KerInert.RepComb

noncomputable section

namespace GlobalTheory.CommonScale

theorem conj_star (D : D7) (x : D.host.E) : (letI := D.host.cmStar; star x) = D.host.conj x := by
  apply D.host.φ₀.injective
  have := D.host.isCMField_hostE
  exact (IsCMField.complexEmbedding_complexConj _ D.host.φ₀ x).trans
    (D.host.conjE_apply D.host.φ₀ x).symm

theorem coprime_of_ne {R : Type} [CommRing R] {P Q : Ideal R} (hP : P.IsMaximal) (hQ : Q.IsMaximal)
    (h : P ≠ Q) : IsCoprime P Q := by
  rw [Ideal.isCoprime_iff_sup_eq]
  exact Ideal.IsMaximal.coprime_of_ne hP hQ h

theorem coprime_span {R : Type} [CommRing R] {P : Ideal R} (hP : P.IsMaximal) {c : R} (hc : c ∉ P) :
    IsCoprime P (Ideal.span {c}) := by
  rw [Ideal.isCoprime_iff_sup_eq]
  by_contra H
  have h1 : P ⊔ Ideal.span {c} = P := (hP.eq_of_le H le_sup_left).symm
  exact hc (h1 ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self c))

theorem exists_split_one {R : Type} [CommRing R] {κ : Type} (P : Ideal R) (hP : P.IsMaximal) (c : R) (hc : c ∉ P)
    (S : Finset κ) (f g : κ → Ideal R) (hf : ∀ q ∈ S, (f q).IsMaximal ∧ P ≠ f q)
    (hg : ∀ q ∈ S, (g q).IsMaximal ∧ P ≠ g q) (M : ℕ) :
    ∃ x ∈ P ^ M, ∃ j : R, x + j = 1 ∧ j ∈ Ideal.span {c} ∧ (∀ q ∈ S, j ∈ f q) ∧ (∀ q ∈ S, j ∈ g q) := by
  have hcop : IsCoprime (P ^ M) (Ideal.span {c} * (∏ q ∈ S, f q) * ∏ q ∈ S, g q) := by
    apply IsCoprime.pow_left
    refine IsCoprime.mul_right (IsCoprime.mul_right (coprime_span hP hc) ?_) ?_
    · exact IsCoprime.prod_right fun q hq => coprime_of_ne hP (hf q hq).1 (hf q hq).2
    · exact IsCoprime.prod_right fun q hq => coprime_of_ne hP (hg q hq).1 (hg q hq).2
  rw [Ideal.isCoprime_iff_sup_eq] at hcop
  have h1 : (1 : R) ∈ P ^ M ⊔ (Ideal.span {c} * (∏ q ∈ S, f q) * ∏ q ∈ S, g q) := by
    rw [hcop]; exact Submodule.mem_top
  obtain ⟨x, hx, j, hj, hxj⟩ := Submodule.mem_sup.1 h1
  refine ⟨x, hx, j, hxj, Ideal.mul_le_left (Ideal.mul_le_left hj), fun q hq => ?_, fun q hq => ?_⟩
  · exact (Ideal.prod_le_inf.trans (Finset.inf_le (f := f) hq)) (Ideal.mul_le_right (Ideal.mul_le_left hj))
  · exact (Ideal.prod_le_inf.trans (Finset.inf_le (f := g) hq)) (Ideal.mul_le_right hj)

theorem scale : letI := fun D : D7 => D.host.cmStar; ∀ (D : D7) (P : HeightOneSpectrum (𝓞 D.host.E)) (SS : Finset (HeightOneSpectrum (𝓞 D.host.E))) (cl : ℕ), P ∉ SS → Formalism.L2.Col.conjPrime₂ P ∉ SS → ((cl : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal → ∀ (ι : Type) [Fintype ι] (a b : ℕ) (N : ι → Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N₀ : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : ι → Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (N₀' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)), (∀ i, GL3Theta.EqOff D P (N i) N₀ ∧ GL3Theta.EqOff D P (N' i) N₀') → ∃ g : 𝓞 D.host.E, (∃ k : 𝓞 D.host.E, g = 1 + (cl : 𝓞 D.host.E) * k) ∧ (∀ Q ∈ SS, g ∉ Q.asIdeal) ∧ ∀ i, ((∀ x ∈ N i, g • x ∈ N₀) ∧ ∀ x ∈ N₀, g • x ∈ N i) ∧ ((∀ x ∈ N' i, g • x ∈ N₀') ∧ ∀ x ∈ N₀', g • x ∈ N' i) := by
  intro D P SS cl hP hPc hcl ι _ na nb N N₀ N' N₀' h
  choose m₁ hm₁ using fun i => (h i).1
  choose m₂ hm₂ using fun i => (h i).2
  have hle₁ : ∀ i, m₁ i ≤ ∑ i, (m₁ i + m₂ i) := fun i =>
    le_trans (Nat.le_add_right _ _) (Finset.single_le_sum (f := fun i => m₁ i + m₂ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have hle₂ : ∀ i, m₂ i ≤ ∑ i, (m₁ i + m₂ i) := fun i =>
    le_trans (Nat.le_add_left _ _) (Finset.single_le_sum (f := fun i => m₁ i + m₂ i) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  have cc : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), Formalism.L2.Col.conjPrime₂ (Formalism.L2.Col.conjPrime₂ Q) = Q := by
    intro Q
    apply HeightOneSpectrum.ext
    ext r
    rw [Formalism.L2.Col.mem_conjP, Formalism.L2.Col.mem_conjP, Formalism.L2.Col.cO_cO]
  obtain ⟨x, hx, j, hxj, hjcl, hjQ, hjQ'⟩ := exists_split_one P.asIdeal P.isMaximal _ hcl SS
    (fun Q => Q.asIdeal) (fun Q => (Formalism.L2.Col.conjPrime₂ Q).asIdeal)
    (fun Q hQ => ⟨Q.isMaximal, fun e => hP (HeightOneSpectrum.ext e ▸ hQ)⟩)
    (fun Q hQ => ⟨(Formalism.L2.Col.conjPrime₂ Q).isMaximal, fun e => hPc (by rw [HeightOneSpectrum.ext e, cc]; exact hQ)⟩)
    (∑ i, (m₁ i + m₂ i))
  have hxQ : ∀ Q : HeightOneSpectrum (𝓞 D.host.E), j ∈ Q.asIdeal → x ∉ Q.asIdeal := fun Q hj' hx' =>
    Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by rw [← hxj]; exact Q.asIdeal.add_mem hx' hj'))
  have hy : ((Formalism.L2.Col.cO D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) :=
    conj_star D (x : D.host.E)
  refine ⟨x * Formalism.L2.Col.cO D.host.E x, ?_, ?_, ?_⟩
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.1 hjcl
    have hx1 : x = 1 - (cl : 𝓞 D.host.E) * t := by rw [← ht, ← hxj]; ring
    refine ⟨-t - Formalism.L2.Col.cO D.host.E t + (cl : 𝓞 D.host.E) * t * Formalism.L2.Col.cO D.host.E t, ?_⟩
    rw [hx1, map_sub, map_one, map_mul, map_natCast]; ring
  · intro Q hQ hg
    rcases Q.isPrime.mem_or_mem hg with h1 | h1
    · exact hxQ Q (hjQ Q hQ) h1
    · exact hxQ (Formalism.L2.Col.conjPrime₂ Q) (hjQ' Q hQ) ((Formalism.L2.Col.mem_conjP Q x).2 h1)
  · intro i
    exact ⟨hm₁ i x _ hy (Ideal.pow_le_pow_right (hle₁ i) hx), hm₂ i x _ hy (Ideal.pow_le_pow_right (hle₂ i) hx)⟩

end GlobalTheory.CommonScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSphericalCombinationOfFixedLocalTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sphericalCombination_of_fixed_localTranslates : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E), ∀ e f, IsPrimeIdem P e f → ∀ a : GA D V →₀ ℂ, (∀ g ∈ a.support, SuppF V f g) → ∃ c : List ℤ →₀ ℂ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (π : GA D V →* Module.End ℂ M) (u : M), (∀ k ∈ hyp V P, π k u = u) → (∀ k ∈ hyp V P, π k (a.sum fun g z => z • π g u) = a.sum fun g z => z • π g u) → (a.sum fun g z => z • π g u) = opOf π P c u := by
  first | exact @GlobalTheory.SphAvg.fixed_comb_eq_opOf | exact GlobalTheory.SphAvg.fixed_comb_eq_opOf | (intros; apply GlobalTheory.SphAvg.fixed_comb_eq_opOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSplitPrimeGLChartOfUnitaryGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_splitPrime_GL_chart_of_unitaryGroup : ∀ {D : D7} (V : HSp D) (P : Pl D.host.E) (e : AE D), Formalism.L2.NTheta.IsIdemAt e P → ∀ ϖ : 𝓞 D.host.E, ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∃ ρ : GA D V →* GL (Fin V.rank) (P.adicCompletion D.host.E), (∀ M : GL (Fin V.rank) (P.adicCompletion D.host.E), ∃ g, Formalism.L2.Theta.SuppAt e V g ∧ ρ g = M) ∧ (∀ k ∈ KsphC V ∅, ρ k ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P)) ∧ ∀ (g : GA D V) (a : Fin V.rank → ℤ), ∀ k₁ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ∀ k₂ ∈ Formalism.UG.GLint (Fin V.rank) (Formalism.UG.Ov D.host.E P), ((ρ g : GL (Fin V.rank) (P.adicCompletion D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) = (k₁ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) * Formalism.UG.diagPow D.host.E P (algebraMap D.host.E (P.adicCompletion D.host.E) (ϖ : D.host.E)) a * (k₂ : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion D.host.E)) → DivAt V e (ϖ : D.host.E) (List.ofFn a) g := by
  first | exact @GlobalTheory.SplitPrimeChart.exists_chart | exact GlobalTheory.SplitPrimeChart.exists_chart | (intros; apply GlobalTheory.SplitPrimeChart.exists_chart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTorusEigenformOfCompactTorusEigenvectorStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torusEigenform_of_compactTorus_eigenvector : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (Fin n → kˣ) V) (x : V) (θ : Fin n → kˣ →* ℂˣ), IsSmooth ρ → HasFiniteLength ρ → (∀ i, IsSmoothChar (θ i)) → x ≠ 0 → (∀ t ∈ torusO k (Fin n), ρ t x = (torusChar θ t : ℂ) • x) → ∃ (ψ : Fin n → kˣ →* ℂˣ) (l : V →ₗ[ℂ] ℂ), l ≠ 0 ∧ (∀ t y, l (ρ t y) = (torusChar ψ t : ℂ) * l y) ∧ ∀ i (u : kˣ), valuation k (u : k) = 1 → ψ i u = θ i u := by
  first | exact @GlobalTheory.TorusEigenform.main | exact GlobalTheory.TorusEigenform.main | (intros; apply GlobalTheory.TorusEigenform.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryElementaryDivisorsInertPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_elementaryDivisors_inertPrime : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (x : 𝓞 D.host.F) (ϖ : 𝓞 D.host.E) (d : List ℤ), IsPrimeIdem P e e → (ϖ : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → dualLab d = d → ∃ g : GA D V, SuppF V e g ∧ DivAt V e (ϖ : D.host.E) d g := by
  first | exact @GlobalTheory.InertExist.exists_suppF_divAt | exact GlobalTheory.InertExist.exists_suppF_divAt | (intros; apply GlobalTheory.InertExist.exists_suppF_divAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUnitaryElementaryDivisorsSplitPrimeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_elementaryDivisors_splitPrime : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (d : List ℤ), Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → d.length = V.rank → ∃ g : GA D V, SuppF V (e + cA D e) g ∧ DivAt V e (ϖ : D.host.E) d g := by
  first | exact @GlobalTheory.SplitExist.split_exist | exact GlobalTheory.SplitExist.split_exist | (intros; apply GlobalTheory.SplitExist.split_exist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodModelTwoScaleOne
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

noncomputable section

namespace GlobalTheory.ThLoc

theorem goodModelTwo_scaleOne : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc →
    TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0),
    CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ →
    ∀ ι : ℂ ≃+* ℂ_[2], ∃ W : WeierstrassCurve ℂ_[2], Unif 2 (cmL a₀ b₀ D.host.d ha hd lam hlam) ι W ∧ IntCurve W ∧
      ‖W.a₁‖ = 1 := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hok hlat ι
  set L := cmL a₀ b₀ D.host.d ha hd lam hlam with hLdef
  obtain ⟨hsq, -, hcm⟩ := LocJets.data ha hd lam hlam hok
  have h8 : D.host.d % 8 = 7 := by have := D.host.hyp.2.2.2.1; omega
  obtain ⟨c, hc, W', ⟨e2, e3⟩, ⟨h1, h2, h3, h4, h6, hΔ⟩, ha1⟩ := hIn.modelTwo D.host.d L hsq h8 hcm ι
  have hL1 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 1 := by
    have hL' : (L.lattice : Set ℂ) = TaylorLogMetric.lamOf D cc δ := by rw [← hlat]; rfl
    obtain ⟨f2, f3⟩ := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.g2_g3_eq_periodPair _ L hL'
    rw [← f2, ← f3]
    exact Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.B5.br_discr_lamOf D cc hcc δ hδ
  have hh := Formalism.L2.Th1.F.homogeneity L c hc
  have s2 : (Formalism.L2.Th1.F.scalePair L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := hh.2.2.2.2.2.2.2.2.2.1
  have s3 : (Formalism.L2.Th1.F.scalePair L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := hh.2.2.2.2.2.2.2.2.2.2
  have g2W : W'.c₄ / 12 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₂ := e2
  have g3W : W'.c₆ / 216 = ι (Formalism.L2.Th1.F.scalePair L c hc).g₃ := e3
  set u : ℂ_[2] := ι c with hu
  have hu0 : u ≠ 0 := by simpa [hu] using hc

  have hW'Δ : W'.Δ = (u ^ 12)⁻¹ := by
    have hrel := W'.c_relation
    have hc4 : W'.c₄ = 12 * ((u ^ 4)⁻¹ * ι L.g₂) := by
      rw [← map_pow, ← map_inv₀, ← map_mul, ← s2, ← g2W]; ring
    have hc6 : W'.c₆ = 216 * ((u ^ 6)⁻¹ * ι L.g₃) := by
      rw [← map_pow, ← map_inv₀, ← map_mul, ← s3, ← g3W]; ring
    have hι1 : ι L.g₂ ^ 3 - 27 * ι L.g₃ ^ 2 = 1 := by
      rw [← map_pow, ← map_pow, ← map_ofNat ι 27, ← map_mul, ← map_sub, hL1, map_one]
    rw [hc4, hc6] at hrel
    have h1728 : (1728 : ℂ_[2]) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h1728
    rw [hrel]
    field_simp
    linear_combination (1728 : ℂ_[2]) * hι1
  have hun : ‖u‖ = 1 := by
    rw [hW'Δ, norm_inv, norm_pow] at hΔ
    have h12 : ‖u‖ ^ 12 = 1 := by
      have hpos : 0 < ‖u‖ ^ 12 := pow_pos (norm_pos_iff.2 hu0) _
      field_simp at hΔ; linarith
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h12
  let C : WeierstrassCurve.VariableChange ℂ_[2] := ⟨(Units.mk0 u hu0)⁻¹, 0, 0, 0⟩
  have hCu : ((C.u⁻¹ : ℂ_[2]ˣ) : ℂ_[2]) = u := by simp [C]
  refine ⟨C • W', ⟨?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · show (C • W').c₄ / 12 = ι L.g₂
    rw [WeierstrassCurve.variableChange_c₄, hCu, mul_div_assoc, g2W, s2, map_mul, map_inv₀, map_pow, ← hu]
    field_simp
  · show (C • W').c₆ / 216 = ι L.g₃
    rw [WeierstrassCurve.variableChange_c₆, hCu, mul_div_assoc, g3W, s3, map_mul, map_inv₀, map_pow, ← hu]
    field_simp
  · rw [WeierstrassCurve.variableChange_a₁, hCu]
    simp only [C, mul_zero, add_zero, norm_mul, hun, one_mul]; exact h1
  · rw [WeierstrassCurve.variableChange_a₂, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_pow two_ne_zero, norm_mul, norm_pow, hun, one_pow,
      one_mul]; exact h2
  · rw [WeierstrassCurve.variableChange_a₃, hCu]
    simp only [C, zero_mul, mul_zero, add_zero, norm_mul, norm_pow, hun, one_pow, one_mul]; exact h3
  · rw [WeierstrassCurve.variableChange_a₄, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, norm_mul, norm_pow, hun,
      one_pow, one_mul]; exact h4
  · rw [WeierstrassCurve.variableChange_a₆, hCu]
    simp only [C, zero_mul, mul_zero, sub_zero, add_zero, zero_add, zero_pow two_ne_zero, zero_pow three_ne_zero,
      norm_mul, norm_pow, hun, one_pow, one_mul]; exact h6
  · rw [WeierstrassCurve.variableChange_Δ, hCu, norm_mul, norm_pow, hun, one_pow, one_mul]; exact hΔ
  · rw [WeierstrassCurve.variableChange_a₁, hCu]
    simp only [C, mul_zero, add_zero, norm_mul, hun, one_mul]; exact ha1

end GlobalTheory.ThLoc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasSubstCoordZA
section
noncomputable section

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits Classical Formalism.L2.KerInert.Loc

theorem resV_subst_two {ι κ σ τ R : Type} [CommRing R] [Finite ι] [Finite σ]
    {f : κ → ι} (hf : Function.Injective f) {g : τ → σ} (hg : Function.Injective g)
    {a : σ → MvPowerSeries ι R} (ha : MvPowerSeries.HasSubst a)
    {a' : τ → MvPowerSeries κ R} (ha' : MvPowerSeries.HasSubst a')
    (h1 : ∀ k, resV f (a (g k)) = a' k) (h0 : ∀ i, (∀ k, g k ≠ i) → resV f (a i) = 0)
    (T : MvPowerSeries σ R) :
    resV f (MvPowerSeries.subst a T) = MvPowerSeries.subst a' (resV g T) := by
  rw [resV_subst hf ha, resV_eq_subst hg T, MvPowerSeries.subst_comp_subst_apply (hasSubst_resFam g) ha']
  congr 1
  funext i
  by_cases h : ∃ k, g k = i
  · obtain ⟨k, rfl⟩ := h
    rw [h1, resFam_apply hg, MvPowerSeries.subst_X ha']
  · push_neg at h
    rw [h0 i h, resFam_off g i h, ← MvPowerSeries.coe_substAlgHom ha', map_zero]

theorem resV_CX {ι κ R : Type} [CommRing R] [Finite ι] {f : κ → ι} (hf : Function.Injective f) (c : R) (k : κ) :
    resV f (MvPowerSeries.C c * MvPowerSeries.X (f k) : MvPowerSeries ι R) = MvPowerSeries.C c * MvPowerSeries.X k := by
  rw [resV_mul hf, resV_X hf]
  congr 1
  ext n
  rw [resV_coeff, MvPowerSeries.coeff_C, MvPowerSeries.coeff_C]
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, if_neg]
    intro h0
    apply hn
    have := congrArg Finsupp.degree h0
    rw [degree_mapDomain] at this
    exact (Finsupp.degree_eq_zero_iff n).1 (by simpa using this)

theorem resV_CX_off {ι κ R : Type} [CommRing R] [Finite ι] {f : κ → ι} (hf : Function.Injective f) (c : R) (i : ι)
    (hi : ∀ k, f k ≠ i) :
    resV f (MvPowerSeries.C c * MvPowerSeries.X i : MvPowerSeries ι R) = 0 := by
  rw [resV_mul hf, resV_X_off hf i hi, mul_zero]

theorem inj_at {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) :
    Function.Injective (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) :=
  fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2

theorem inE_inj {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) : Function.Injective (inE X j v) := by
  have hg : Function.Injective (fun e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, e⟩ : X.EA j)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj_iff.1 h).2
  exact hg.sumMap hg

end GlobalTheory.TwU

namespace GlobalTheory.TwU

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits Classical Formalism.L2.KerInert.Loc

theorem hasSubst_coordZA {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) :
    MvPowerSeries.HasSubst (X.coordZA (K0 p) j) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    rintro (⟨w, r, a, b⟩ | ⟨w, r, a, b⟩) <;> simp [Sys.coordZA])

theorem hasSubst_coordZ {p : ℕ} [Fact p.Prime] {n' r0 r1 : ℕ} (B : OmBasis p n') :
    MvPowerSeries.HasSubst (coordZ (r0 := r0) (r1 := r1) B (K0 p) 1) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    rintro (⟨r, a, b⟩ | ⟨r, a, b⟩) <;> simp [coordZ])

theorem resV_ThZA {p : ℕ} [Fact p.Prime] (X : Sys p) (j : ℕ) (v : X.Pl) (T : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)) :
    resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j)) (X.ThZA (K0 p) j T) =
      ThZ (X.om v) (K0 p) 1 (resV (inE X j v) T) := by
  have hE := inE_inj X j v
  have hZ := inj_at X j v
  unfold Sys.ThZA ThZ
  refine resV_subst_two hZ hE (hasSubst_coordZA X j) (hasSubst_coordZ _) ?_ ?_ T
  · rintro (⟨r, a, b⟩ | ⟨r, a, b⟩)
    · show resV _ (X.coordZA (K0 p) j (Sum.inl ⟨v, (r, a, b)⟩)) = _
      simp only [Sys.coordZA, coordZ]
      rw [resV_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [one_mul, Algebra.algebraMap_self, RingHom.id_apply]
      exact resV_CX hZ _ (s, a, b)
    · show resV _ (X.coordZA (K0 p) j (Sum.inr ⟨v, (r, a, b)⟩)) = _
      simp only [Sys.coordZA, coordZ]
      rw [resV_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [one_mul, Algebra.algebraMap_self, RingHom.id_apply]
      exact resV_CX hZ _ (s, a, b)
  · rintro (⟨w, r, a, b⟩ | ⟨w, r, a, b⟩) hi
    · have hw : w ≠ v := by
        rintro rfl
        exact hi (Sum.inl (r, a, b)) rfl
      simp only [Sys.coordZA]
      rw [resV_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      exact resV_CX_off hZ _ _ (fun z h => hw (congrArg Sigma.fst h).symm)
    · have hw : w ≠ v := by
        rintro rfl
        exact hi (Sum.inr (r, a, b)) rfl
      simp only [Sys.coordZA]
      rw [resV_sum]
      refine Finset.sum_eq_zero fun s _ => ?_
      exact resV_CX_off hZ _ _ (fun z h => hw (congrArg Sigma.fst h).symm)

theorem resV_phAt {p : ℕ} [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl) :
    resV (inE X j v) (phAt X be j v) =
      ∑ e : Eidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)),
        sub2 p be (MvPowerSeries.X (Sum.inl e)) (MvPowerSeries.X (Sum.inr e)) := by
  have hE := inE_inj X j v
  unfold phAt
  rw [resV_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [restrict_formalSum hE be (by simp) (by simp)]
  exact congrArg₂ (sub2 p be) (resV_X hE (Sum.inl e)) (resV_X hE (Sum.inr e))

theorem restr_onePlace : ∀ (p : ℕ) [Fact p.Prime] (X : Sys p) (be : MvPowerSeries (Fin 2) (K0 p)) (j : ℕ) (v : X.Pl)
    (U : MvPowerSeries (X.EA j ⊕ X.EA j) (K0 p)), MvPowerSeries.constantCoeff be = 0 → IntS p (inParam p U) →
    IntS p (inParam p (resV (inE X j v) U)) ∧
      resV (fun z : Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)) => (⟨v, z⟩ : X.ZA j))
        (X.ThZA (K0 p) j (expS p (-phAt X be j v) * U)) = thOne (X.om v) be (resV (inE X j v) U) := by
  intro p _ X be j v U _ hU
  have hE := inE_inj X j v
  refine ⟨?_, ?_⟩
  · obtain ⟨g, hg⟩ := hU
    exact ⟨resV (inE X j v) g, by rw [← resV_inParam hE, hg, resV_map]⟩
  · rw [resV_ThZA, resV_mul hE, resV_expS hE, resV_neg, resV_phAt]
    rfl

end GlobalTheory.TwU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralPreimageAddImageEqLatticeStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_preimage_add_image_eq_lattice : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n n' : ℕ) (x : Matrix (Fin n') (Fin n) L) (y : Matrix (Fin n) (Fin n') L),
    ∃ a : GL (Fin n) L, ∀ v : Fin n → L,
      (∃ u : Fin n → L, ∃ w : Fin n' → L, (∀ i, u i ∈ Formalism.UG.intL L) ∧ (∀ i, (x *ᵥ u) i ∈ Formalism.UG.intL L) ∧ (∀ i, w i ∈ Formalism.UG.intL L) ∧ v = u + y *ᵥ w) ↔
        ∃ t : Fin n → L, (∀ i, t i ∈ Formalism.UG.intL L) ∧ v = (a : Matrix (Fin n) (Fin n) L) *ᵥ t := by
  first | exact @GlobalTheory.Hk3.HoweG.latA_basis | exact GlobalTheory.Hk3.HoweG.latA_basis | (intros; apply GlobalTheory.Hk3.HoweG.latA_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InverseSeriesFormalGroupIsoIntegral
section
noncomputable section

namespace GlobalTheory.InverseSeriesIntegral

open Formalism.MainNotions.GL3Theta (G1)
open Formalism.L2.G.Pend (wToC LTIso)
open Formalism.InvariantFactorPaths.G7 (lgF)
open Formalism.L2.KerInert.BeCob (vLT eLT)
open GlobalTheory.CurveDictionary (cc_lgF' lgF_eq_logF)

theorem exists_witt_series_inverse_formalGroup_iso {l : ℕ} [Fact l.Prime] {g : G1 l} (hOk : g.Ok) (hLT : LTIso g) :
    ∃ w : PowerSeries (Formalism.MainNotions.FormalGroupSystem.WW l), PowerSeries.map (wToC l) w = vLT hLT := by
  have hex := hOk.2.2.1
  have hinv := hOk.2.2.2
  set e := eLT hLT with he
  have he1 : ‖e‖ = 1 := Formalism.L2.G.Pend.norm_wToC_unit l _
  have hene : e ≠ 0 := by intro h; rw [h, norm_zero] at he1; exact zero_ne_one he1
  set th0 := Formalism.L2.G.Pend.thOf hLT with hth0
  have h00 : PowerSeries.constantCoeff th0 = 0 := Formalism.L2.G.Pend.thOf_zero hLT
  have hu : IsUnit (PowerSeries.coeff 1 th0) := Formalism.L2.G.Pend.thOf_unit hLT
  set i0 := th0.substInvOfIsUnit hu with hi0
  have hi00 : PowerSeries.constantCoeff i0 = 0 := PowerSeries.constantCoeff_substInvOfIsUnit _ _
  have hR : PowerSeries.subst i0 th0 = PowerSeries.X := PowerSeries.subst_substInvOfIsUnit_right _ h00 hu
  set thC := PowerSeries.map (wToC l) th0 with hthC
  set iC := PowerSeries.map (wToC l) i0 with hiC
  have hthC0 : PowerSeries.constantCoeff thC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hthC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h00, map_zero]
  have hiC0 : PowerSeries.constantCoeff iC = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, hiC, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, hi00, map_zero]
  have hRC : PowerSeries.subst iC thC = PowerSeries.X := by
    have h := congrArg (MvPowerSeries.map (wToC l)) hR
    rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero' hi00)] at h
    exact h.trans (MvPowerSeries.map_X _ _)
  have hv0 : PowerSeries.constantCoeff (PowerSeries.C e⁻¹ * lgF ℂ_[l] l) = 0 := by
    rw [map_mul, cc_lgF', mul_zero]
  have hlog : PowerSeries.subst thC (lgF ℂ_[l] l) = PowerSeries.C e * g.l := by
    have h := Formalism.L2.G.Pend.thOf_log hLT
    rw [lgF_eq_logF] at h
    exact h
  have hVT : PowerSeries.subst thC (vLT hLT) = PowerSeries.X := by
    unfold vLT
    rw [PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hv0)
      (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0),
      PowerSeries.subst_mul (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0), PowerSeries.subst_C, hlog]
    have e1 : (MvPowerSeries.C e⁻¹ : PowerSeries ℂ_[l]) * (PowerSeries.C e * g.l) = g.l := by
      rw [← mul_assoc]
      show PowerSeries.C e⁻¹ * PowerSeries.C e * g.l = g.l
      rw [← map_mul, inv_mul_cancel₀ hene, map_one, one_mul]
    rw [e1]
    exact Formalism.L2.G.Pend.ex_l g hex hinv
  refine ⟨i0, ?_⟩
  show iC = vLT hLT
  symm
  calc vLT hLT = PowerSeries.subst (PowerSeries.X : PowerSeries ℂ_[l]) (vLT hLT) := (PowerSeries.X_subst _).symm
    _ = PowerSeries.subst (PowerSeries.subst iC thC) (vLT hLT) := by rw [hRC]
    _ = PowerSeries.subst iC (PowerSeries.subst thC (vLT hLT)) :=
        (PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' hthC0)
          (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0) _).symm
    _ = PowerSeries.subst iC (PowerSeries.X : PowerSeries ℂ_[l]) := by rw [hVT]
    _ = iC := PowerSeries.subst_X (PowerSeries.HasSubst.of_constantCoeff_zero' hiC0)

theorem v_integral : ∀ (l : ℕ) [Fact l.Prime] (g : G1 l), g.Ok → ∀ (hLT : LTIso g) (n : ℕ),
    ‖PowerSeries.coeff n (vLT hLT)‖ ≤ 1 := by
  intro l _ g hOk hLT n
  obtain ⟨w, hw⟩ := exists_witt_series_inverse_formalGroup_iso hOk hLT
  rw [← hw, PowerSeries.coeff_map]
  have := Formalism.L2.G.Pend.norm_wToC_pow_mul l 0 (PowerSeries.coeff n w)
  simpa using this

end GlobalTheory.InverseSeriesIntegral
end
end

