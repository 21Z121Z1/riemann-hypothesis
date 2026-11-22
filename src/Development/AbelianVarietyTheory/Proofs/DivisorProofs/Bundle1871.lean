import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1689
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0415
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1734
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1825
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1779
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistPlaceStepCharacterConductorExponentOne
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TwistCond

theorem condExp_twist_eq_one : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) {μ₀ : T}, Lc.Is μ₀ →
    ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ Lc.Q t → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) = 1 := by
  intro D T Lc sc G μ₀ hL i j t v τ hmu hchi hQ
  set w := GlobalTheory.AdelicU.splitPrime τ with hw
  have hfun : chrW (GlobalTheory.SqStep.chs G i j t).ν τ =
      ((nuH G t i j).loc w).comp (Units.map (GlobalTheory.LFun.complMap (GlobalTheory.AdelicU.splitPrime_under τ)).toMonoidHom) :=
    MonoidHom.ext fun x => GlobalTheory.SqStepArith.chrW_chs G hL i j t τ x
  have hloc : ∀ x, (nuH G t i j).loc w x =
      (Lc.C.mu0 j).loc w x * (Lc.xiH t).loc w x * ((G.ch.chiH (D.R.m - i)).loc w x)⁻¹ := by
    intro x
    show ((Lc.C.mu0 j * Lc.xiH t) * (G.ch.chiH (D.R.m - i))⁻¹).loc w x = _
    rw [Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_mul, Formalism.L2.Host.HChar.loc_inv]
  have h1 : GlobalTheory.SplitFlip.CondLE (unifAt v) 1 (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) := by
    rw [hfun, GlobalTheory.CondLESplit.condLE_iff]
    intro x hx hx1
    rw [hloc, hmu x hx, hchi x hx, hL.xi_tame t w x hx hx1]
    simp
  have h0 : ¬ GlobalTheory.SplitFlip.CondLE (unifAt v) 0 (chrW (GlobalTheory.SqStep.chs G i j t).ν τ) := by
    rw [hfun, GlobalTheory.CondLESplit.condLE_iff]
    intro h
    apply (hL.Q_ram t w).2 (Or.inl hQ)
    intro x hx
    have hle : Valued.v ((x : w.adicCompletion D.host.E) - 1) ≤ WithZero.exp (-((0 : ℕ) : ℤ)) := by
      simp only [Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact Valuation.map_sub_le _ (le_of_eq hx) (by simp)
    have := h x hx hle
    rw [hloc, hmu x hx, hchi x hx] at this
    simpa using this
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.condExp
  have hne : ({c | GlobalTheory.SplitFlip.CondLE (unifAt v) c (chrW (GlobalTheory.SqStep.chs G i j t).ν τ)} : Set ℕ).Nonempty := ⟨1, h1⟩
  apply le_antisymm (Nat.sInf_le h1)
  rw [Nat.one_le_iff_ne_zero]
  intro h
  have := Nat.sInf_mem hne
  rw [h] at this
  exact h0 this

end GlobalTheory.TwistCond
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformSchwartzSeminormBound
section
open Filter Topology
open scoped SchwartzMap Uniformity

namespace GlobalTheory

theorem schwartz_family_uniform_bound : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (I : Type)
    (lam : I → SchwartzMap V ℂ →L[ℂ] ℂ) (w : I → ℝ), (∀ i, 0 ≤ w i) →
    (∀ f, ∃ (N : ℕ) (C : ℝ), ∀ i, ‖lam i f‖ ≤ C * w i ^ N) →
    ∃ (N : ℕ) (C : ℝ) (T : Finset (ℕ × ℕ)), ∀ i f,
      ‖lam i f‖ ≤ C * (T.sup (schwartzSeminormFamily ℂ V ℂ)) f * w i ^ N := by
  intro V _ _ _ I lam w hw hb
  haveI : (𝓤 𝓢(V, ℂ)).IsCountablyGenerated := IsUniformAddGroup.uniformity_countably_generated
  haveI : BaireSpace 𝓢(V, ℂ) := inferInstance
  let S : ℕ × ℕ → Set 𝓢(V, ℂ) := fun p => {f | ∀ i, ‖lam i f‖ ≤ (p.2 : ℝ) * w i ^ p.1}
  have hS : ∀ p, IsClosed (S p) := by
    intro p
    simp only [S, Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le (continuous_norm.comp (lam i).continuous) continuous_const
  have hU : ⋃ p, S p = Set.univ := by
    refine Set.eq_univ_of_forall fun f => ?_
    obtain ⟨N, C, hC⟩ := hb f
    obtain ⟨M, hM⟩ := exists_nat_ge C
    exact Set.mem_iUnion.2 ⟨(N, M), fun i =>
      (hC i).trans (mul_le_mul_of_nonneg_right hM (pow_nonneg (hw i) _))⟩
  obtain ⟨p, f₀, hf₀⟩ := nonempty_interior_of_iUnion_of_closed hS hU
  have hn : interior (S p) ∈ 𝓝 f₀ := isOpen_interior.mem_nhds hf₀
  have hn' : (fun g => f₀ + g) ⁻¹' interior (S p) ∈ 𝓝 (0 : 𝓢(V, ℂ)) := by
    have h : Tendsto (fun g : 𝓢(V, ℂ) => f₀ + g) (𝓝 0) (𝓝 f₀) := by
      simpa using (continuous_const_add f₀).tendsto 0
    exact h hn
  obtain ⟨⟨T, ε⟩, hε, hT⟩ := ((schwartz_withSeminorms ℂ V ℂ).hasBasis_zero_ball).mem_iff.1 hn'
  simp only at hε hT
  set q := T.sup (schwartzSeminormFamily ℂ V ℂ) with hq
  have hball : ∀ g, q g < ε → ∀ i, ‖lam i g‖ ≤ 2 * (p.2 : ℝ) * w i ^ p.1 := by
    intro g hg i
    have h1 : f₀ + g ∈ S p := interior_subset (hT (by simpa [Seminorm.mem_ball] using hg))
    have h2 : f₀ ∈ S p := interior_subset hf₀
    have h3 : lam i g = lam i (f₀ + g) - lam i f₀ := by simp
    rw [h3]
    calc ‖lam i (f₀ + g) - lam i f₀‖ ≤ ‖lam i (f₀ + g)‖ + ‖lam i f₀‖ := norm_sub_le _ _
      _ ≤ (p.2 : ℝ) * w i ^ p.1 + (p.2 : ℝ) * w i ^ p.1 := add_le_add (h1 i) (h2 i)
      _ = 2 * (p.2 : ℝ) * w i ^ p.1 := by ring
  refine ⟨p.1, 2 * (p.2 : ℝ) / ε, T, fun i f => ?_⟩
  set A := 2 * (p.2 : ℝ) * w i ^ p.1 / ε with hA
  have hA0 : 0 ≤ A := by
    have := pow_nonneg (hw i) p.1
    positivity
  have hq0 : 0 ≤ q f := apply_nonneg _ _
  have hscale : ∀ t, q f < t → ‖lam i f‖ ≤ t * A := by
    intro t ht
    have htpos : 0 < t := lt_of_le_of_lt hq0 ht
    have hc : ‖((ε / t : ℝ) : ℂ)‖ = ε / t := by
      rw [Complex.norm_real, Real.norm_of_nonneg (div_pos hε htpos).le]
    have hg : q (((ε / t : ℝ) : ℂ) • f) < ε := by
      rw [map_smul_eq_mul, hc]
      calc ε / t * q f < ε / t * t := mul_lt_mul_of_pos_left ht (div_pos hε htpos)
        _ = ε := by field_simp
    have h := hball _ hg i
    rw [map_smul, norm_smul, hc] at h
    rw [hA, show t * (2 * (p.2 : ℝ) * w i ^ p.1 / ε) = (t / ε) * (2 * (p.2 : ℝ) * w i ^ p.1) by ring]
    have : ‖lam i f‖ = (t / ε) * (ε / t * ‖lam i f‖) := by
      field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_left h (div_pos htpos hε).le
  have hfin : ‖lam i f‖ ≤ q f * A := by
    rcases hA0.lt_or_eq with hApos | hAz
    · refine le_of_forall_gt_imp_ge_of_dense fun a ha => ?_
      have : q f < a / A := (lt_div_iff₀ hApos).2 ha
      calc ‖lam i f‖ ≤ a / A * A := hscale _ this
        _ = a := by field_simp
    · rw [← hAz, mul_zero]
      have := hscale (q f + 1) (by linarith)
      rwa [← hAz, mul_zero] at this
  calc ‖lam i f‖ ≤ q f * A := hfin
    _ = 2 * (p.2 : ℝ) / ε * q f * w i ^ p.1 := by rw [hA]; ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilDatumAdjointNegSourceKernelsAgree
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV GlobalTheory.RouteSeesaw

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.AdjSwap

theorem dagger_eq_adjM {D : D7} (S B : HSp D) (y : Mx D B.rank S.rank) :
    GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B y = adjM S B y := by
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger, adjM]
  rw [← Matrix.mul_assoc]
  rfl

theorem weil_adjoint_negSource : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S B : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (ω₂ : GA D B × GA D S →* Module.End ℂ (WO B S → ℂ)), IsWeilDatumO ψ B S χS χT ω₂ →
    ∃ (ω : GA D (negSp S) × GA D B →* Module.End ℂ (WO (negSp S) B → ℂ)) (χ χ' : (AE D)ˣ →* Circle),
      IsWeilDatumO ψ (negSp S) B χ χ' ω ∧ ∀ f : WO B S → ℂ, IsThetaFunO ψ B S f →
        IsThetaFunO ψ (negSp S) B (fun y => f (adjM S B y)) ∧
        ∀ g₁ u, thetaKO ω (negGA S u) g₁ (fun y => f (adjM S B y)) = thetaKO ω₂ g₁ u f := by
  intro D ψ hψ S B χS χT ω₂ H
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂), χT⁻¹, χS⁻¹,
    GlobalTheory.ConjWeil.weil_conjSource D ψ S B _ _ _ (GlobalTheory.ConjAdjWeil.isWeilDatumO_conjAdjoint D ψ B S _ _ ω₂ H),
    fun f hf => ?_⟩
  have e : (fun y : WO (negSp S) B => f (adjM S B y)) =
      GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) := by
    funext y; simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_eq_adjM]
  rw [e]
  have h1 : IsThetaFunO ψ S B (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S B) f) :=
    ((GlobalTheory.AdjointPair.adjoint_clauses D ψ hψ B S).2.2.1 f).2 hf
  refine ⟨((GlobalTheory.CjNeg.theta_heis_neg D ψ hψ S B).1 _).2.2 h1, fun g₁ u => ?_⟩
  show GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjAdjoint ω₂) (negGA S u, g₁) _ 0 = ω₂ (g₁, u) f 0
  rw [GlobalTheory.ConjWeil.conjSource_apply]
  simp only [MulEquiv.symm_apply_apply, GlobalTheory.ConjWeil.cj_id_cj_id]
  rw [GlobalTheory.TensorTargetRule.conjAdjoint_cj]
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_eq_adjM, adjM_zero]

end GlobalTheory.AdjSwap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorFixesCosetVector
section
noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.FunObj.CosetFix

variable {D : D7}

theorem zeroAt_zero (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left _, 0, zero_mem _, by simp⟩

theorem trivAt_one {N : ℕ} (q : ℕ) : TrivAt D q ((1 : GA D N) : GL (Fin N) (AE D)) := fun i j => by
  simpa using zeroAt_zero (D := D) q

set_option maxHeartbeats 1000000 in

theorem fix_of_prop {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (hT : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d) {g' : GA D P.d}
    {H : VC D P.a P.d → ℂ} {c : ℂ} (hc' : P.W.Om 1 g' P.e0 = c • H) :
    H ∈ TT D (tor0 D ⊤ δ) P.a P.d ∧ ∀ k : GA D P.a, P.W.Om k 1 P.e0 = P.e0 → P.W.Om k 1 H = H := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply P.W.nz
    have h0 : P.W.Om 1 g' P.e0 = 0 := by rw [hc', zero_smul]
    have e := P.W.mul 1 1 g'⁻¹ g' P.e0 hT
    have e1 : (1 : GA D P.a) * 1 = 1 := mul_one 1
    have e2 : g'⁻¹ * g' = 1 := inv_mul_cancel g'
    rw [e1, e2, P.W.one _ hT, h0] at e
    have z := P.W.smul 1 g'⁻¹ (0 : ℂ) (0 : VC D P.a P.d → ℂ) (NormUniq.tt_zero _)
    have z0 : (0 : ℂ) • (0 : VC D P.a P.d → ℂ) = 0 := zero_smul ℂ _
    rw [z0] at z
    rw [e, z]
    exact zero_smul ℂ _
  have hHT : H ∈ TT D (tor0 D ⊤ δ) P.a P.d := by
    have e : H = c⁻¹ • P.W.Om 1 g' P.e0 := by rw [hc', smul_smul, inv_mul_cancel₀ hc0, one_smul]
    have hm : P.W.Om 1 g' P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d := P.W.maps 1 g' P.e0 hT
    rw [e]
    exact NormUniq.tt_smul hm c⁻¹
  refine ⟨hHT, fun k he => ?_⟩
  have e1 := P.W.mul k 1 1 g' P.e0 hT
  have e2 := P.W.mul 1 k g' 1 P.e0 hT
  have f1 : k * (1 : GA D P.a) = k := mul_one k
  have f2 : (1 : GA D P.d) * g' = g' := one_mul g'
  have f3 : (1 : GA D P.a) * k = k := one_mul k
  have f4 : g' * (1 : GA D P.d) = g' := mul_one g'
  rw [f1, f2] at e1
  rw [f3, f4] at e2
  have e3 : P.W.Om k 1 (P.W.Om 1 g' P.e0) = P.W.Om 1 g' P.e0 := by rw [← e1, e2, he]
  rw [hc', P.W.smul _ _ _ _ hHT] at e3
  exact smul_right_injective _ hc0 e3

theorem iop_facts (hI : Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) :
    Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 ∈
      TT D (tor0 D ⊤ δ) P.a P.d ∧
    ∀ k : GA D P.a, P.W.Om k 1 P.e0 = P.e0 →
      P.W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d)
        (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0) =
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 := by
  obtain ⟨g', hg'⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D P.d _ (GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d)
  obtain ⟨c, hc⟩ := VacMove.exists_scalar hI P.crv P.vac.1 P.W 1 g' (VacMove.moves_one D P.a) hg'
  exact fix_of_prop P (VacMove.vac_TT hI.g1 P.crv P.vac.1) (c := c) (by rw [hc]; funext z; rfl)

variable {T : Type} {L : LevCh D T} {sc : Consts}

theorem vac_fix_split (G : GridData L sc) (i j : Fin D.R.m) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) (hs : SuppSplit D (k : GL (Fin P.a) (AE D))) : P.W.Om k 1 P.e0 = P.e0 := by
  obtain ⟨x, hxu, hxi, hx, h1, h2⟩ := GlobalTheory.FunObj.NormUniq.SplitDet.exists_splitComp_det hk hk' hs
  have hm : Moves D (k : GL (Fin P.a) (AE D)) (stdL D P.a) := by
    simpa using VacMove.moves_mul_int hk (VacMove.moves_one D P.a)
  have e := P.W.split k 1 x 1 (stdL D P.a) (stdL D P.d) hs (fun q _ _ => trivAt_one q)
    (fun q hq hi => ⟨hxi q hq hi, by simpa using zeroAt_zero (D := D) q⟩) hx (by simp) hm (VacMove.moves_one D P.d)
  have hc : P.W.chV'.f x ^ P.W.ep' = 1 := by
    rw [h.chars.2 x]
    show ((nuH G μ₀ i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x))⁻¹ = 1
    rw [GlobalTheory.NuTrivSq.nuH_finIdl_eq_one G i j hL x hxu h1 h2, inv_one]
  rw [e, map_one, one_zpow, hc, one_mul,
    show La D (tor0 D ⊤ δ) (stdL D P.a) (stdL D P.d) = La0 D (tor0 D ⊤ δ) P.a P.d from rfl,
    VacMove.iop_self D _ (La0 D (tor0 D ⊤ δ) P.a P.d) P.vac.1]
  funext z
  simp

theorem vac_fix (G : GridData L sc) (i j : Fin D.R.m) (hI : Inp D) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) : P.W.Om k 1 P.e0 = P.e0 := by
  obtain ⟨ks, ki, rfl, hs, hi, hs', hss, hii⟩ := GlobalTheory.CongSplitFactor.exists_split_inert_factor hk hk'
  have hT := VacMove.vac_TT hI.g1 P.crv P.vac.1
  have h1 : P.W.Om ki 1 P.e0 = P.e0 :=
    P.W.inert ki 1 ((mem_intG ki).1 hi) ((mem_intG 1).1 (one_mem _)) hii (fun q _ _ => trivAt_one q)
  have e := P.W.mul ks ki 1 1 P.e0 hT
  rw [mul_one] at e
  rw [e, h1, vac_fix_split G i j hL h hs hs' hss]

theorem cosetVec_fix (G : GridData L sc) (i j : Fin D.R.m) (hI : Inp D) {μ₀ : T} (hL : L.Is μ₀) {δ t0 : ℂ} {Q : ℕ}
    {P P' : Pair D ⊤ δ t0 Q} (h : IsBottom G μ₀ i j (condE G.pl) P P') {k : GA D P.a} (hk : k ∈ intG D P.a)
    (hk' : CongOne D (condE G.pl) k) : P.W.Om k 1 (cosetVec P (condE G.pl) 0) = cosetVec P (condE G.pl) 0 := by
  obtain ⟨hHT, hfix⟩ := iop_facts hI P (condE_ne_bot G.pl)
  have hH := hfix k (vac_fix G i j hI hL h hk hk')
  have hW := GlobalTheory.HeisFix.heis_fix hI P (condE_ne_bot G.pl) 0 hk hk' hHT hH
  have hWT := GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT P.crv one_pos (by rw [one_smul]; exact pt_unitBlock_mem δ 0 P.a P.d) hHT
  unfold cosetVec
  rw [P.W.smul _ _ _ _ hWT, hW]

example : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m), Inp D → ∀ {μ₀ : T}, L.Is μ₀ → ∀ {δ t0 : ℂ} {Q : ℕ} {P P' : Pair D ⊤ δ t0 Q}, IsBottom G μ₀ i j (condE G.pl) P P' → ∀ {k : GA D P.a}, k ∈ intG D P.a → CongOne D (condE G.pl) k → P.W.Om k 1 (cosetVec P (condE G.pl) 0) = cosetVec P (condE G.pl) 0 := @cosetVec_fix

end GlobalTheory.FunObj.CosetFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorNormalisingVectorNeZero
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NormExact

theorem om_normalising_ne_zero : ∀ {D : D7} (cc : Ideal (𝓞 D.host.K)) (δ t0 : ℂ) {a d : ℕ} (e0 : VC D a d → ℂ) (W : WeilO D cc δ a d e0),
  Formalism.MainNotions.StandardLatticesGL3.Crv D cc δ → oddE0 D cc δ t0 a d e0 →
  ∀ (x : Formalism.MainNotions.StandardLatticesGL3.GA D a) (y : Formalism.MainNotions.StandardLatticesGL3.GA D d), W.Om x y e0 ≠ 0 := by
  intro D cc δ t0 a d e0 W hC hodd x y h0
  have he0 := hodd.1
  have hSD0 : ∀ N : ℕ, Formalism.MainNotions.StandardLatticesGL3.SD D (stdL D N) := by
    intro N
    obtain ⟨Lt, h1, h2, -⟩ := GlobalTheory.NormSum.exists_lattice_of_adelic_point D N
    rw [← h2]; exact (h1 1).2
  obtain ⟨-, hWL, -, -⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC a d
    (Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d) (Or.inr ⟨_, _, hSD0 _, hSD0 _, rfl⟩)
  have hfix : ∀ v ∈ Formalism.MainNotions.StandardLatticesGL3.La0 D (tor0 D cc δ) a d, Formalism.MainNotions.StandardLatticesGL3.Wd D (tor0 D cc δ) v e0 = e0 := by
    intro v hv
    rw [hWL v hv]; funext w; exact he0.2 v hv w
  have heT : e0 ∈ TT D (tor0 D cc δ) a d :=
    ⟨he0.1, 1, one_pos, fun v hv => by rw [one_nsmul]; exact hfix v hv⟩
  have h1 := W.mul x⁻¹ x y⁻¹ y e0 heT
  rw [inv_mul_cancel, inv_mul_cancel, W.one _ heT, h0] at h1
  have h2 := W.smul x⁻¹ y⁻¹ 0 e0 heT
  rw [zero_smul, zero_smul] at h2
  exact W.nz (h1.trans h2)

end GlobalTheory.NormExact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepLatticeScalarAction
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.FinComm.VacLaw

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem eq_atPlace_of_at (v : Pl F) {z : κ → AF F} (hz : At (evFin F v) z) (i : κ) :
    z i = GlobalTheory.EmbChart.atPlace v (evFin F v (z i)) := by
  have h0 : evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
    rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have h := congrFun (hz _ h0) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, one_mul, sub_eq_zero] at h
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul] at h
  exact h

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_atPlace (v : Pl F) (a : Fv F v) : evI F (GlobalTheory.EmbChart.atPlace v a) = 0 := by
  rw [GlobalTheory.EmbChart.atPlace_apply]
  exact map_zero _

theorem evFin_atPlace_ne {v u : Pl F} (h : u ≠ v) (a : Fv F v) : evFin F u (GlobalTheory.EmbChart.atPlace v a) = 0 := by
  rw [GlobalTheory.EmbChart.atPlace_apply]
  exact evalV_singleFin_ne h a

theorem eventually_int (x : κ → AF F) :
    ∀ᶠ u in cofinite, ∀ i, evFin F u (x i) ∈ u.adicCompletionIntegers F :=
  Filter.eventually_all.mpr fun i => (x i).2.2

theorem finite_mulSupport (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (x : κ → AF F) : (Function.mulSupport fun u => φ u (fun i => evFin F u (x i))).Finite := by
  have h : ∀ᶠ u in cofinite, φ u (fun i => evFin F u (x i)) = 1 := by
    filter_upwards [hφ, eventually_int x] with u hu hx
    rw [hu]
    simp [indO, Set.indicator, hx]
  exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp

theorem tens_update (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) : tens (evFin F v) (φ v) (pure f (Function.update φ v fun _ => 1)) = pure f φ := by
  funext x
  have hfin := finite_mulSupport φ hφ x
  unfold tens GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [← mul_finprod_cond_ne v hfin]
  have : (∏ᶠ u, Function.update φ v (fun _ => 1) u (fun i => evFin F u (x i))) =
      ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i)) := by
    have hfin' : (Function.mulSupport fun u =>
        Function.update φ v (fun _ => (1 : ℂ)) u (fun i => evFin F u (x i))).Finite := by
      refine hfin.subset fun u hu => ?_
      by_cases e : u = v
      · subst e; simp at hu
      · simpa [Function.update_of_ne e] using hu
    rw [← mul_finprod_cond_ne v hfin', Function.update_self, one_mul]
    exact finprod_congr fun u => finprod_congr fun hu => by rw [Function.update_of_ne hu]
  rw [this]
  ring

theorem pure_update_add_at (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x z : κ → AF F)
    (hz : At (evFin F v) z) :
    pure f (Function.update φ v fun _ => 1) (x + z) = pure f (Function.update φ v fun _ => 1) x := by
  have hI : (fun i => evI F ((x + z) i)) = fun i => evI F (x i) := by
    funext i
    rw [Pi.add_apply, evI_add, eq_atPlace_of_at v hz i, evI_atPlace, add_zero]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [hI]
  congr 1
  refine finprod_congr fun u => ?_
  by_cases e : u = v
  · subst e; simp
  · rw [Function.update_of_ne e]
    congr 1
    funext i
    rw [Pi.add_apply, map_add, eq_atPlace_of_at v hz i, evFin_atPlace_ne e, add_zero]

end GlobalTheory.FinComm.VacLaw

namespace GlobalTheory.FinComm

open GlobalTheory.FinComm.VacLaw

theorem vac_law : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ →
    ∃ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ, ∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d),
      M.co.rho ψ γ (pure f M.vac) = c v γ • pure f M.vac := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM
  have hvacO : ∀ᶠ u in cofinite, M.vac u = indO u := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  have hvacSB : ∀ u, M.vac u ∈ SB _ := fun u => (hM.vac u).1
  refine ⟨fun v γ => ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (((hM.vac v).2.2.choose : 𝓞 E) : E))
    (incM F X.J) (incM F W.J) γ γ), fun v γ hγ f => ?_⟩
  have hact := ((hM.vac v).2.2.choose_spec.2) γ hγ
  have hpv : pure f M.vac ∈ schA F _ := GlobalTheory.T.pure_tensor_mem_schwartz_adelic f M.vac hvacSB hvacO
  have hten := tens_update f M.vac hvacO v
  have hrest : Rest (evFin F v) (M.vac v) (pure f (Function.update M.vac v fun _ => 1)) :=
    ⟨fun x z hz => pure_update_add_at f M.vac v x z hz, hten ▸ hpv⟩
  have h := hact _ hrest
  rw [hten] at h
  rw [h, ← hten]
  funext x
  simp [tens, mul_assoc]

end GlobalTheory.FinComm
end
end

