import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1829
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1886
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1179
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0354
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeUnitNormSqNonneg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaVacuaConjugatesCmPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1856
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormIteratedFDerivRemCompLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1892
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0269
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1866
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1483

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvSmulMemRationalHomLatticeScaledOfNormScale
section
noncomputable section

open NumberField

namespace GlobalTheory.VacRead

theorem int_of_mem_bInv (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {γ : D.host.E} (hγ : γ ∈ cE D D.host.ccK) {c : 𝓞 D.host.K} (hcc : c ∈ cc) {y : D.host.E} (hy : y ∈ bInv D cc r) :
    GlobalTheory.InertSign.IntE D (D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ * y /
      (Ideal.absNorm D.host.ccK : D.host.E)) := by
  have hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  have hN : (Ideal.absNorm cc : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact hc
  have hcE : ((c : D.host.K) : D.host.E) ∈ cE D cc := Submodule.subset_span ⟨c, hcc, rfl⟩
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨α, hα, γ₂, hγ₂, rfl⟩ := hy
    obtain ⟨o₁, h₁⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).1 γ hγ γ₂ hγ₂
    obtain ⟨o₂, h₂⟩ := (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D cc).1 α hα _ hcE
    refine ⟨o₁ * o₂, ?_⟩
    have e : D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ * (r * D.host.conj α * γ₂ / (Ideal.absNorm cc : D.host.E)) /
        (Ideal.absNorm D.host.ccK : D.host.E) =
        (D.host.conj γ * γ₂ / (Ideal.absNorm D.host.ccK : D.host.E)) *
          (D.host.conj α * ((c : D.host.K) : D.host.E) / (Ideal.absNorm cc : D.host.E)) := by
      field_simp
    rw [e, h₁, h₂, mul_div_cancel_left₀ _ hN0, mul_div_cancel_left₀ _ hN]
    simp
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨u, hu⟩ := hx
    obtain ⟨v, hv⟩ := hy
    exact ⟨u + v, by rw [map_add, hu, hv]; ring⟩
  | smul o x _ hx =>
    obtain ⟨u, hu⟩ := hx
    refine ⟨o * u, ?_⟩
    rw [map_mul, hu, Algebra.smul_def]
    ring

theorem mul_mem_Iid (D : Formalism.BasicNotions.D7) {ε α : D.host.E} (hε : ε ∈ cE D D.host.ccK)
    (hα : α ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)) : ε * α ∈ GlobalTheory.InertSign.Iid D D.host.ccK := by
  induction hε using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨c₀, hc₀, rfl⟩ := hx
    exact Submodule.subset_span ⟨c₀, hc₀, α, hα, rfl⟩
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ o hx

theorem smul_mem_homL (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {γ : D.host.E} (hγ : γ ∈ cE D D.host.ccK) {c : 𝓞 D.host.K} (hcc : c ∈ cc)
    {A : Matrix (Fin d) (Fin a) D.host.E} (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d)) :
    (D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ / (Ideal.absNorm D.host.ccK : D.host.E)) • A ∈
      Formalism.MainNotions.TaylorLogMetric.homL D (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  have hA' := GlobalTheory.ThetaLatImage.mem_homL.1 hA
  have hint : ∀ i j, GlobalTheory.InertSign.IntE D (A i j) := by
    intro i j
    have h1 : Pi.single j (1 : D.host.E) ∈ Formalism.MainNotions.StandardLatticesGL3.stdL D a := by
      rw [GlobalTheory.ThetaLatImage.mem_stdL]
      intro k
      refine ⟨if k = j then 1 else 0, ?_⟩
      by_cases h : k = j
      · subst h; simp
      · simp [h]
    have h2 := GlobalTheory.ThetaLatImage.mem_stdL.1 (hA' _ h1) i
    have hcol : A.mulVec (Pi.single j 1) i = A i j := by
      simp [Matrix.mulVec, dotProduct, Pi.single_apply]
    rwa [hcol] at h2
  rw [GlobalTheory.ThetaLatImage.mem_homL]
  intro x hx
  rw [GlobalTheory.ThetaLatImage.mem_stdL]
  intro i
  have hy : A.mulVec x i ∈ bInv D cc r := by
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    obtain ⟨o, ho⟩ := hint i j
    rw [← ho, ← Algebra.smul_def]
    exact Submodule.smul_mem _ o (mem_lsB.1 hx j)
  have := int_of_mem_bInv D cc r hc hr hγ hcc hy
  rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  convert this using 1
  ring

theorem gen_mem_RL (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ) (hc : cc ≠ ⊥) (hr : r ≠ 0)
    {c : 𝓞 D.host.K} (hcc : c ∈ cc) {α : D.host.E} (hα : α ∈ (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E))
    {A : Matrix (Fin d) (Fin a) D.host.E} (hA : A ∈ Formalism.MainNotions.TaylorLogMetric.homL D (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d)) :
    (r⁻¹ * (((c : D.host.K) : D.host.E) * α)) • A ∈
      GlobalTheory.InertSign.RL D D.host.ccK (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  have hN0 : (Ideal.absNorm D.host.ccK : D.host.E) ≠ 0 := by
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]; exact D.host.ccK_ne_bot
  set X := r⁻¹ * (((c : D.host.K) : D.host.E) * α) with hX
  have key : ∀ t ∈ Submodule.span (𝓞 D.host.E) {t | ∃ γ ∈ cE D D.host.ccK, ∃ ε ∈ cE D D.host.ccK,
      t = D.host.conj γ * ε},
      (t * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A ∈
        GlobalTheory.InertSign.RL D D.host.ccK (lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
    intro t ht
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨γ, hγ, ε, hε, rfl⟩ := ht
      have e : (D.host.conj γ * ε * ((Ideal.absNorm D.host.ccK : D.host.E)⁻¹ * X)) • A =
          (ε * α) • ((D.host.conj γ * ((c : D.host.K) : D.host.E) * r⁻¹ /
            (Ideal.absNorm D.host.ccK : D.host.E)) • A) := by
        rw [smul_smul, hX]
        congr 1
        ring
      rw [e]
      exact Submodule.subset_span ⟨ε * α, mul_mem_Iid D hε hα, _, smul_mem_homL D cc r a d hc hr hγ hcc hA, rfl⟩
    | zero => rw [zero_mul, zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [add_mul, add_smul]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx => rw [smul_mul_assoc, smul_assoc]; exact Submodule.smul_mem _ o hx
  have h := key _ (GlobalTheory.T.idealExtend_conj_mul_eq_absNorm D D.host.ccK).2
  rwa [mul_inv_cancel_left₀ hN0] at h

theorem rl_div_scale : ∀ (D : Formalism.BasicNotions.D7) (cc : Ideal (𝓞 D.host.K)) (r : D.host.E) (a d : ℕ), cc ≠ ⊥ →
    GlobalTheory.NormExact.IsScale D cc r → ∀ z ∈ GlobalTheory.InertSign.RL D cc (Formalism.MainNotions.StandardLatticesGL3.stdL D a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d),
      r⁻¹ • z ∈ GlobalTheory.InertSign.RL D D.host.ccK (GlobalTheory.VacRead.lsB D cc r a) (Formalism.MainNotions.StandardLatticesGL3.stdL D d) := by
  intro D cc r a d hc hs z hz
  have hr : r ≠ 0 := GlobalTheory.NormExact.IsScale.ne_zero hc hs
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨t, ht, A, hA, rfl⟩ := hz
    rw [smul_smul]
    induction ht using Submodule.span_induction with
    | mem t ht =>
      obtain ⟨c, hcc, α, hα, rfl⟩ := ht
      exact gen_mem_RL D cc r a d hc hr hcc hα hA
    | zero => rw [mul_zero, zero_smul]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add, add_smul]; exact Submodule.add_mem _ hx hy
    | smul o x _ hx => rw [mul_smul_comm, smul_assoc]; exact Submodule.smul_mem _ o hx
  | zero => rw [smul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact Submodule.add_mem _ hx hy
  | smul o x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ o hx

end GlobalTheory.VacRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPolynomialFockThetaVectorDefiniteBottom
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexConjugate Matrix NNReal
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (sZero)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP (Pair Unram SphFun openOff integrand wcoef rcoef up)

noncomputable section

namespace GlobalTheory.BottomIPData

theorem isFockVec_bottom : GBig fun {D} T Lc _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m) (A A' WW : HSp D) (X : Tri T A A' WW),
  IsBottomTri W i j X → ∀ t : T, ∀ P : PolF D WW.rank A.rank, IsFockVec W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ _ T Lc μ₀ _ G => ?_⟩⟩
  intro W i j A A' WW X hX t P
  have h := isBottomTri_is hX
  have hψ : IsStdChar D W.ψ (-1) := h.isVac.1
  have hθ : IsInfFam W.θ := h.isVac.2.inf
  have cS : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (h.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (h.rigW.2.2 τ).1
  have hf : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hψ hθ (h.fst t) h.isVac.2.theta
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (h.idem t)
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (GlobalTheory.Grid.neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (h.fst t)
      h.isVac.2.theta hf (h.isVac.2.fock τ)
  exact GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ cS cT X.rA.B X.rW.B hf hv P

end GlobalTheory.BottomIPData

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
section
open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.ResW GlobalTheory.Published
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ResW

theorem nu_zero_isUnitary (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] : (nu E 0).IsUnitary := by
  intro x
  simp [nu, GlobalTheory.HeckeGal.Model.absPow, GlobalTheory.Mem.Chr.CharModel.absHom_val]

theorem isUnitarisable_of_twRep {G X : Type} [Group G] [AddCommGroup X] [Module ℂ X] {ρ : Representation ℂ G X}
    {χ : G →* ℂˣ} (hχ : ∀ g, ‖((χ g : ℂˣ) : ℂ)‖ = 1) (h : GlobalTheory.SmGL.IsUnitarisable (twRep ρ χ)) :
    GlobalTheory.SmGL.IsUnitarisable ρ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨B, h1, h2, fun g v w => ?_⟩
  have e := h3 g v w
  simp only [twRep_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at e
  have hc : ((χ g : ℂˣ) : ℂ) * starRingEnd ℂ ((χ g : ℂˣ) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hχ g]; simp
  rw [← e]
  linear_combination (-(B (ρ g v) (ρ g w))) * hc

theorem isUnitarisable_of_isLocComp_cusp : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (x : CuspSub E a), 1 ≤ a → x.IsUnitary → ∀ (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin a) (w.adicCompletion E))), x.IsLocComp w σ → GlobalTheory.SmGL.IsUnitarisable σ.ρ := by
  intro E _ _ _ a x ha hu w σ hσ
  have hcex := (GlobalTheory.T.cuspidalLetter_centralExponent_properties E ⟨a, x⟩).1
  have hr : rexp (⟨a, x⟩ : Letter E) = 0 := ((GlobalTheory.T.cuspidalLetterRealExponent_eq_zero_iff_isUnitary E ⟨a, x⟩ ha).1).2 hu
  have hd : (0 : ℝ) < (a : ℝ) * Module.finrank ℚ E := by
    have := Module.finrank_pos (R := ℚ) (M := E)
    have : (1 : ℝ) ≤ a := by exact_mod_cast ha
    positivity
  have hre : (cex (⟨a, x⟩ : Letter E)).re = 0 := by
    have h := hr
    unfold rexp at h
    rcases div_eq_zero_iff.1 h with h | h
    · exact h
    · exact absurd h hd.ne'
  have hdc : ((a : ℂ) * (Module.finrank ℚ E : ℂ)) = (((a : ℝ) * Module.finrank ℚ E : ℝ) : ℂ) := by push_cast; ring
  obtain ⟨χ, hz, -, hn, -⟩ := GlobalTheory.T.exists_idelic_absValue_cpow_character E (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ)))
  have hzre : (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ))).re = 0 := by
    rw [hdc, Complex.div_ofReal_re, Complex.neg_re, hre]; simp
  have hχu : χ.IsUnitary := fun y => by rw [hn y, hzre]; exact nu_zero_isUnitary E y
  have hnorm : IsNormalised (x.twist χ) := by
    have h4 := GlobalTheory.T.cuspidalLetter_centralExponent_properties E ⟨a, x.twist χ⟩
    refine h4.2.2.2.1.1 (h4.2.2.2.2 0 ?_)
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 x.ne_bot
    refine ⟨mulChi a χ φ, ⟨φ, hφ, rfl⟩, fun h => h0 ((mulChi a χ).map_eq_zero_iff.1 h), ?_⟩
    have e1 : zc E a φ = cex (⟨a, x⟩ : Letter E) • φ := hcex φ hφ
    have e2 : cex (⟨a, x⟩ : Letter E) + (a : ℂ) * (Module.finrank ℚ E : ℂ) *
        (-(cex (⟨a, x⟩ : Letter E)) / ((a : ℂ) * (Module.finrank ℚ E : ℂ))) = 0 := by
      have : ((a : ℂ) * (Module.finrank ℚ E : ℂ)) ≠ 0 := by
        rw [hdc]; exact_mod_cast hd.ne'
      rw [mul_div_cancel₀ _ this]; ring
    change zc E a (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ
    rw [hz, e1, ← add_smul, e2, zero_smul, map_zero, zero_smul]
  have hdisc := (GlobalTheory.T.cuspForm_sqIntegrable_and_isDiscrete_splitCentre E a).2 _ hnorm
  obtain ⟨f, h0, hf⟩ := hσ.twist χ
  have hgl : IsLocCompGL (x.twist χ).V w (σ.twist (CuspSub.locDet a χ w) (CuspSub.isOpen_ker_locDet χ w)) :=
    ⟨(x.twist χ).V.subtype ∘ₗ f, fun h => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun h v)),
      fun v => (f v).2, fun g v => congrArg Subtype.val (hf g v)⟩
  have hU := GlobalTheory.DiscreteUnit.isUnitarisable_of_isLocCompGL E a _ hdisc w _ hgl
  exact isUnitarisable_of_twRep (χ := CuspSub.locDet a χ w) (fun g => hχu _) hU

end GlobalTheory.ResW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIdempotentGivesDualStableSubspacesStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropicIdempotent_gives_dual_stable_subspaces : ∀ {D : D7} {V : HSp D} (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg γ.1.1 → ε * ε = ε → ε ≠ 0 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ε * V.gram * ε = 0 → ∃ X X' : Submodule D.host.E V.V, X ≠ ⊥ ∧ X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X ∧ X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' ∧ (∀ x ∈ X, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X) ∧ (∀ x ∈ X', GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X') ∧ (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) ∧ (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) := by
  first | exact @GlobalTheory.IdemIsotropic.idem_isotropic_pair | exact GlobalTheory.IdemIsotropic.idem_isotropic_pair | (intros; apply GlobalTheory.IdemIsotropic.idem_isotropic_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetOperatorRationalFormConjEqConjTableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jetOperator_rationalForm_conj_eq_conjTable : ∀ {D : D7} {a b : ℕ} (lam : D.what₂.Tau → DomWeight a) (lam' : D.what₂.Tau → DomWeight b) (n : D.what₂.Tau → ℕ)
    (J : (Formalism.L2.Ker.DVar D.what₂.Tau a b →₀ ℕ) → ℂ) (σ : D.what₂.LL →+* ℂ) (ρ' : Qbar →ₐ[ℚ] ℂ)
    (f : VV D.what₂.LL lam →ₗ[D.what₂.LL] VV D.what₂.LL lam'), Formalism.L2.Ker.JetInVV ℂ lam lam' n → (∀ m, J m ∈ Qbar) →
    (∀ x, Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (D.what₂.embLL x) = σ x) →
    (∀ u, Formalism.L2.Ker.jetOp lam lam' J n (GlobalTheory.CoefModel.mapVV D.what₂.embLL lam u) = GlobalTheory.CoefModel.mapVV D.what₂.embLL lam' (f u)) →
    ∀ u, GlobalTheory.CoefModel.mapVV σ lam' (f u) =
      Formalism.L2.Ker.jetOp lam lam' (fun m => Formalism.MainNotions.StandardLatticesGL3.cj Qbar ρ' (J m)) n (GlobalTheory.CoefModel.mapVV σ lam u) := by
  first | exact @GlobalTheory.JetDescent.mapVV_rational_form_conj | exact GlobalTheory.JetDescent.mapVV_rational_form_conj | (intros; apply GlobalTheory.JetDescent.mapVV_rational_form_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LagrangianColumnsLinearParametrisationFinitePlacStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lagrangianColumns_linear_parametrisation_finitePlace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (v : Pl F)
    (m : ℕ) (C : Matrix (Fin d) (Fin m) (AE F E)), IsLagrAt σ W v C →
    d = 2 * m ∧ ∃ (N : ℕ) (j : (Fin N → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))
      (ζ : (Fin N → Fv F v) → Matrix (Fin n) (Fin m) (AE F E)), Function.Injective j ∧
      (∀ y, At (evFin F v) (ζ y) ∧ locCo M.co v (ζ y * Cᵀ) = j y) ∧
      (∀ z : Matrix (Fin n) (Fin m) (AE F E), At (evFin F v) z → ∃ y, ζ y = z) ∧
      ∀ s : GL (Fin n) (AE F E), ∃ T : GL (Fin N) (Fv F v), (∀ y, ζ (T.val *ᵥ y) = s.val * ζ y) ∧
        T.val.det = Algebra.norm (Fv F v) (compFin F E v s.val.det) ^ m := by
  first | exact @GlobalTheory.InertLagParam.param | exact GlobalTheory.InertLagParam.param | (intros; apply GlobalTheory.InertLagParam.param <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInvariantDistributionCharacters
section
namespace GlobalTheory.LatticeComb
open scoped SchwartzMap

theorem comb_unique : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (P : LinearMap.BilinForm ℝ V), P.Nondegenerate →
    ∀ (Λ : Submodule ℤ V) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (a : V) (T : SchwartzMap V ℂ →L[ℂ] ℂ),
    (∀ l ∈ Λ, ∀ f f' : SchwartzMap V ℂ, (∀ x, f' x = f (x + l)) → T f' = T f) →
    (∀ μ : V, (∀ l ∈ Λ, ∃ k : ℤ, P l μ = k) → ∀ f f' : SchwartzMap V ℂ,
      (∀ x, f' x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * f x) →
      T f' = Complex.exp (2 * Real.pi * Complex.I * (P a μ : ℂ)) * T f) →
    ∃ c : ℂ, ∀ f : SchwartzMap V ℂ, T f = c * ∑' l : Λ, f (a + l) := by
  intro V _ _ _ P hP Λ _ _ a T htr hmod
  obtain ⟨h, hhc, hh1⟩ := GlobalTheory.T.exists_schwartz_partition_of_unity_lattice Λ
  refine ⟨T h, fun f => ?_⟩
  have hth : ∀ l : Λ, (fun x => h (x + (l : V))).HasTemperateGrowth := fun l =>
    HasCompactSupport.hasTemperateGrowth (hhc.comp_homeomorph (Homeomorph.addRight (l : V)))
      ((h.smooth ⊤).comp (contDiff_id.add contDiff_const))
  have hh : (⇑h).HasTemperateGrowth := HasCompactSupport.hasTemperateGrowth hhc (h.smooth ⊤)
  let u : Λ → 𝓢(V, ℂ) := fun l => SchwartzMap.smulLeftCLM ℂ (fun x => h (x + (l : V))) f
  have hu : ∀ (l : Λ) (x : V), u l x = h (x + l) * f x := fun l x => by
    simp [u, SchwartzMap.smulLeftCLM_apply_apply (hth l)]
  obtain ⟨F1, hF1p, hF1T⟩ := GlobalTheory.T.summable_schwartz_series u (GlobalTheory.T.lattice_translates_cutoff_summable Λ h f hhc u hu)
  have hF1 : F1 = f := by
    ext x
    refine (hF1p x).unique ?_
    simpa [hu] using (hh1 x).mul_right (f x)
  let w : Λ → 𝓢(V, ℂ) := fun l => SchwartzMap.smulLeftCLM ℂ (⇑h) (SchwartzMap.compSubConstCLM ℂ (l : V) f)
  have hw : ∀ (l : Λ) (x : V), w l x = h x * f (x - l) := fun l x => by
    simp [w, SchwartzMap.smulLeftCLM_apply_apply hh]
  have huw : ∀ l, T (u l) = T (w l) := fun l =>
    htr l l.2 (w l) (u l) (fun x => by rw [hu, hw]; simp)
  obtain ⟨G, hGp, hGT⟩ := GlobalTheory.T.summable_schwartz_series w (GlobalTheory.T.lattice_shifted_cutoff_summable Λ h f hhc w hw)
  have h1 : T f = T G := by
    have := hF1T T
    rw [hF1] at this
    simp_rw [huw] at this
    exact this.unique (hGT T)
  obtain ⟨c, hcs, hcP⟩ := GlobalTheory.T.lattice_dual_fourier_expansion_schwartz P hP Λ f
  have hch : ∀ μ : V, (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))).HasTemperateGrowth := by
    intro μ
    have e : (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) =
        fun x : V => Complex.exp ((Complex.I * ((2 * Real.pi : ℝ) : ℂ)) *
          ((LinearMap.toContinuousLinearMap (P.flip μ) x : ℝ) : ℂ)) := by
      funext x
      simp only [LinearMap.coe_toContinuousLinearMap']
      show _ = Complex.exp (Complex.I * ((2 * Real.pi : ℝ) : ℂ) * ((P x μ : ℝ) : ℂ))
      push_cast; ring_nf
    rw [e]
    exact GlobalTheory.CharFormDeriv.hasTemperateGrowth_char (LinearMap.toContinuousLinearMap (P.flip μ)) (2 * Real.pi)
  let v0 : V → 𝓢(V, ℂ) := fun μ => SchwartzMap.smulLeftCLM ℂ (fun x : V => Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) h
  have hv0 : ∀ μ x, v0 μ x = Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ)) * h x := fun μ x => by
    simp [v0, SchwartzMap.smulLeftCLM_apply_apply (hch μ)]
  let v : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} → 𝓢(V, ℂ) := fun μ => c μ • v0 μ
  have hvs : ∀ k n : ℕ, Summable (fun μ => SchwartzMap.seminorm ℂ k n (v μ)) := by
    intro k n
    obtain ⟨C, hC⟩ := GlobalTheory.T.modulated_schwartz_seminorm_polynomial P h v0 hv0 k n
    refine Summable.of_nonneg_of_le (fun μ => apply_nonneg _ _) (fun μ => ?_) ((hcs n).mul_left C)
    simp only [v, map_smul_eq_mul]
    calc ‖c μ‖ * SchwartzMap.seminorm ℂ k n (v0 μ) ≤ ‖c μ‖ * (C * (1 + ‖(μ : V)‖) ^ n) :=
          mul_le_mul_of_nonneg_left (hC μ) (norm_nonneg _)
      _ = C * (‖c μ‖ * (1 + ‖(μ : V)‖) ^ n) := by ring
  obtain ⟨G', hG'p, hG'T⟩ := GlobalTheory.T.summable_schwartz_series v hvs
  have hGG : G = G' := by
    ext x
    refine (hGp x).unique ?_
    have e1 : HasSum (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => v μ x)
        (h x * ∑' l : Λ, f (x + l)) := by
      have := (hcP x).mul_left (h x)
      have hfun : (fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => v μ x) =
          fun μ : {μ : V // ∀ l ∈ Λ, ∃ k : ℤ, P l μ = k} => h x * (c μ * Complex.exp (2 * Real.pi * Complex.I * (P x μ : ℂ))) := by
        funext μ
        simp only [v, SchwartzMap.smul_apply, hv0, smul_eq_mul]
        ring
      rw [hfun]; exact this
    have e2 : h x * ∑' l : Λ, f (x + l) = G' x := e1.unique (hG'p x)
    rw [← e2]
    have hsum : Summable (fun l : Λ => h x * f (x - l)) := by simpa [hw] using (hGp x).summable
    have e3 : ∑' l : Λ, f (x + l) = ∑' l : Λ, f (x - l) := by
      rw [← (Equiv.neg Λ).tsum_eq]
      simp [sub_eq_add_neg]
    rw [e3, ← tsum_mul_left]
    simpa [hw] using hsum.hasSum
  have hTv : ∀ μ, T (v μ) = c μ * Complex.exp (2 * Real.pi * Complex.I * (P a μ : ℂ)) * T h := by
    intro μ
    simp only [v, map_smul, smul_eq_mul]
    rw [hmod μ μ.2 h (v0 μ) (hv0 μ)]
    ring
  have h2 := hG'T T
  simp_rw [hTv] at h2
  rw [h1, hGG, ← h2.tsum_eq, tsum_mul_right, (hcP a).tsum_eq, mul_comm]

end GlobalTheory.LatticeComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieEigenLatticeLeSpanCmHomImagesStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieEigenLattice_le_span_cmHom_images : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0), ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ → ∀ τE : E →+* K, (∀ x : 𝓞 E, τE x = ((τ x : 𝓞 K) : K)) →
          FB.eigLat X.B.t.act τ ≤ Submodule.span (𝓞 K)
            {w | ∃ c ∈ GlobalTheory.FlatCM.HomLat.lat X, ∃ e ∈ FP.eigLat (X.A true).t.act τ, w = ∑ a, τE (c a) • MP a e} := by
  first | exact @GlobalTheory.FlatCM.HomLat.LieSpan.eigLat_le_span | exact GlobalTheory.FlatCM.HomLat.LieSpan.eigLat_le_span | (intros; apply GlobalTheory.FlatCM.HomLat.LieSpan.eigLat_le_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhatStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearForm_eq_zero_of_kills_productSchwartzBruhat : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ κ' : Type) [Fintype κ] [Fintype κ'] (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ Λ : ((κ ⊕ κ' → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
      (∀ φ₁ ∈ SB (κ → Fv F v), ∀ φ₂ ∈ SB (κ' → Fv F v), Λ (boxFun φ₁ φ₂) = 0) → ∀ Φ ∈ SB (κ ⊕ κ' → Fv F v), Λ Φ = 0 := by
  first | exact @GlobalTheory.BoxSpan.boxSpan_ker | exact GlobalTheory.BoxSpan.boxSpan_ker | (intros; apply GlobalTheory.BoxSpan.boxSpan_ker <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOperatorRightPartialPure
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.DblEval

namespace GlobalTheory.DblEval.BlockSwap

theorem partR_pureA {F : Type} [Field F] [NumberField F] {κ κ' κ₁' : Type} [Fintype κ]
    [Fintype κ'] [Fintype κ₁']
    (e : ((κ' → AF F) → ℂ) →ₗ[ℂ] (κ₁' → AF F) → ℂ) (he : IsLocOp e) :
    ∃ P : SInf F (κ ⊕ κ') →L[ℂ] SInf F (κ ⊕ κ₁'), ∀ g ∈ SB (κ ⊕ κ' → Af F),
      ∃ g₁ ∈ SB (κ ⊕ κ₁' → Af F), ∀ f : SInf F (κ ⊕ κ'),
        partR e (pureA F f g) = pureA F (P f) g₁ :=
  GlobalTheory.DblEval.BlockSwap.partR_of_partL e (GlobalTheory.T.local_operator_left_partial_pure e he)

end GlobalTheory.DblEval.BlockSwap
end

