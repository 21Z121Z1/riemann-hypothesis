import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2454
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2060
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0670
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1681
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1709
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0734
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0011
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0012
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0740
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0643
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BottomThetaKernelFiniteDimensional
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
namespace GlobalTheory.KerFin
theorem bottomTheta_kernel_finite : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            ∀ T, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y = Ω₀ * u * starRingEnd ℂ (P.term x h T) := by
  intro hPr hTI hLM hInp hBS
  refine gbig_comb (_root_.GlobalTheory.T.theta_parameters_match hPr hTI hLM hInp hBS) GlobalTheory.BotWeights.weights_const ?_
  intro D T Lc sc G μ₀ C x b q2 q3 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨r, rc, κ, hr, hrc, hκ, H2⟩ := q2 W hW i j A A' WW X δ t0 hX hβ
  obtain ⟨n₀, H3⟩ := q3 i j δ t0
  obtain ⟨Ω, hΩ, H1⟩ := GlobalTheory.T.bottomTriple_thetaKernel_minors_eq_const_conjJet G W hW i j A A' WW X hX r rc hr hrc n₀
  refine ⟨Ω * starRingEnd ℂ κ, mul_ne_zero hΩ ((map_ne_zero _).2 hκ), fun s Q P P' hB => ?_⟩
  obtain ⟨u, hu0, huQ, huU, hEq⟩ := H2 s Q P P' hB
  refine ⟨u, hu0, huQ, huU, fun ea ed h g x y hg hy Tu => ?_⟩
  have hne : κ * starRingEnd ℂ u ≠ 0 := mul_ne_zero hκ ((map_ne_zero _).2 hu0)
  rw [H1 P.a P.d P.n ea ed (H3 s Q P P' hB) s g y hg.1 hy.1 Tu, hEq ea ed h g x y hg hy,
    GlobalTheory.FunObj.NormUniq.applyAt0_smul _ hne]
  simp only [GlobalTheory.NormSum.Pair.term, map_mul, Complex.conj_conj]
  ring
end GlobalTheory.KerFin
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bottomTheta_kernel_finiteDimensional : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
    (∀ D, GlobalTheory.NormSum.Inp D) → GlobalTheory.SqTop.BotSmall →
    GlobalTheory.SqTop.GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil), IsStdChar D W.ψ (-1) → ∀ (i j : Fin D.R.m) (A A' WW : HSp D)
      (X : Tri T A A' WW) (δ t0 : ℂ), IsBottomTri W i j X → X.rW.β = 1 →
      ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧ ∀ (s : T) (Q : ℕ) (P P' : Pair D ⊤ δ t0 Q), IsBottom G s i j (GlobalTheory.SqTop.modT G s) P P' →
        ∃ u : ℂ, u ≠ 0 ∧ u ∈ Qbar ∧ (∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ GlobalTheory.SqTop.Qn G s → ∀ lam : Qbar →+* ℂ_[p], ‖lamC lam u‖ = 1) ∧
          ∀ (ea : P.a = A.rank) (ed : P.d = WW.rank) (h : GA D P.d) (g : GA D WW) (x : GA D P.a) (y : GA D A),
            GlobalTheory.BotFormula.IsFinPt WW g h → GlobalTheory.BotFormula.IsFinPt A y x →
            ∀ T, X.ker W.ψ W.θ s (GlobalTheory.BotFormula.minorF ea ed T) g y = Ω₀ * u * starRingEnd ℂ (P.term x h T) := by
  first | exact @_root_.GlobalTheory.KerFin.bottomTheta_kernel_finite | exact _root_.GlobalTheory.KerFin.bottomTheta_kernel_finite | (intros; apply _root_.GlobalTheory.KerFin.bottomTheta_kernel_finite <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConjLinearFunctionalSphericalVectorIndicator
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped Matrix
noncomputable section
namespace GlobalTheory.SplitBarVac
theorem conjLinearFunctional_sphericalVector_indicator : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ b₁ : GL (Fin n) (Fv F v), (PsiUnr B.ψ v → b₁ = b) ∧ ∃ ι, M.IsLinBar B.ψ t b₁ c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair v t b c hb hc
  have hcm : IsCMExt F E σ := hPair.base.cm
  have hσσ : ∀ x, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [hcm.2.2.2, hcm.2.2.2, star_star]
  have htt : (t.comp σ).comp σ = t := AlgHom.ext fun x => by simp [hσσ]
  have hJX : IsHermND σ X.Jᵀ := ⟨fun i j => by simp [Matrix.transpose_apply, hPair.herm.herm],
    by rw [Matrix.det_transpose]; exact GlobalTheory.HermSelfDualLoc.det_ne_zero_of_isHerm σ B hPair.herm⟩
  have hL := GlobalTheory.HermSelfDualLoc.isSelfDualAt_transpose F E σ B n X r s hPair.base hPair.herm v
  have hb2 := hb.dual hcm hJX hL
  obtain ⟨z, c₂, hz1, hc2v, hc2⟩ := GlobalTheory.T.skewHermitianLattice_splitPlace_components_dual F E σ B d W r' s' hPair.base hPair.skew v t c hc
  have hc3 : IsSplitBasis (t.comp σ) W.L (-c₂) := fun u => by
    have := hc2 (-u)
    simp only [Pi.neg_apply, neg_mem_iff, Matrix.mulVec_neg] at this
    simpa [Units.val_neg, Matrix.neg_mulVec, Matrix.mulVec_neg] using this
  refine ⟨Units.map (Matrix.scalar (Fin n) : Fv F v →+* Matrix (Fin n) (Fin n) (Fv F v)).toMonoidHom z * b,
    fun hu => by simp [hz1 hu], ?_⟩
  obtain ⟨ι, hι, hvac⟩ := _root_.GlobalTheory.T.linearFunctional_sphericalVector_ne_zero hP F E σ B n d X W M χX χW om r s r' s' hPair v (t.comp σ) _ _ hb2 hc3
  refine ⟨ι, ?_, hvac⟩
  unfold Model.IsLinW at hι
  rw [htt] at hι
  unfold Model.IsLinBar
  convert hι using 1
  have e1 : ((dualConj 1 (splitGram hJX t * b))⁻¹).1 = b.1ᵀ * X.J.map t := by
    rw [← map_inv, dualConj_val]
    simp [Matrix.transpose_mul, Matrix.transpose_map]
  have e2 : ((-c₂)⁻¹).1 = -((z : Fv F v) • (c.1ᵀ * W.J.map t)) := by
    first
    | (rw [← hc2v]; simp)
    | (rw [← hc2v, Units.neg_inv]; rfl)
    | (rw [← hc2v]; exact congrArg Units.val (neg_inv c₂))
  ext Y i j
  rw [e1, e2]
  simp only [Units.val_mul, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, Matrix.transpose_mul, Matrix.scalar_apply,
    Matrix.transpose_neg, Matrix.transpose_smul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.diagonal_transpose, Matrix.mul_assoc, neg_neg]
  simp [Matrix.mul_assoc, ← Matrix.smul_eq_diagonal_mul, Matrix.mul_smul, Matrix.smul_mul]
end GlobalTheory.SplitBarVac
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_sphericalVector_indicator_value : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (v : Pl F) (t : E →ₐ[F] Fv F v) (b : GL (Fin n) (Fv F v)) (c : GL (Fin d) (Fv F v)), IsSplitBasis t X.L b → IsSplitBasis t W.L c →
    ∃ b₁ : GL (Fin n) (Fv F v), (PsiUnr B.ψ v → b₁ = b) ∧ ∃ ι, M.IsLinBar B.ψ t b₁ c ι ∧ ι (M.vac v) = Set.indicator {Y | ∀ i j, Y i j ∈ v.adicCompletionIntegers F} 1 := by
  first | exact @_root_.GlobalTheory.SplitBarVac.conjLinearFunctional_sphericalVector_indicator | exact _root_.GlobalTheory.SplitBarVac.conjLinearFunctional_sphericalVector_indicator | (intros; apply _root_.GlobalTheory.SplitBarVac.conjLinearFunctional_sphericalVector_indicator <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CuspFormsEqISupIrreducibleGK
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
noncomputable section
namespace GlobalTheory.CuspGK
variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)
theorem cuspForm_mem_iSup_irreducible_gK : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ψ ∈ ⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ GlobalTheory.CuspGK.gkGen θ M ψ ∧ GlobalTheory.CuspGK.IsIrrGKSub θ M A), A := by
  intro hP D θ V S M hθ ψ hA hC hW
  obtain ⟨b, hpos, hherm, hK, hL⟩ := _root_.GlobalTheory.T.cusp_form_petersson_nonvanishing_gelfandKirillov hP θ V S M hθ ψ hA hC hW
  obtain ⟨e, he1, he2, he3, he4, he5⟩ := _root_.GlobalTheory.T.kType_projection_of_kFinite hP θ V S M hθ ψ hA hC hW b hpos hherm hK hL
  refine GlobalTheory.T.mem_iSup_irreducible_of_fixed_projector (IsGKSub θ M) (isGKSub_sInf θ M) (gkGen θ M ψ) (isGKSub_gkGen θ M ψ) b
    hpos hherm (fun A hAle hAP => ?_) e he2 he3 he4 he5 ψ (mem_gkGen θ M ψ) he1
  have hperp : ∀ f ∈ gkGen θ M ψ ⊓ ⨅ a ∈ A, LinearMap.ker (b a),
      f ∈ gkGen θ M ψ ∧ ∀ a ∈ A, b a f = 0 := fun f hf => by
    rw [Submodule.mem_inf] at hf
    exact ⟨hf.1, fun a ha => LinearMap.mem_ker.1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hf.2 a) ha)⟩
  have hmk : ∀ f, f ∈ gkGen θ M ψ → (∀ a ∈ A, b a f = 0) → f ∈ gkGen θ M ψ ⊓ ⨅ a ∈ A, LinearMap.ker (b a) :=
    fun f h1 h2 => Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun a => (Submodule.mem_iInf _).2 fun ha =>
      LinearMap.mem_ker.2 (h2 a ha)⟩
  refine ⟨fun τ g hg f hf => ?_, fun τ X hX f hf => ?_⟩
  · obtain ⟨hfN, hf0⟩ := hperp f hf
    refine hmk _ ((isGKSub_gkGen θ M ψ).k τ g hg f hfN) fun a ha => ?_
    rw [hK τ g hg a (hAle ha) f hfN]
    exact hf0 _ (hAP.k τ g⁻¹ hg.inv a ha)
  · obtain ⟨hfN, hf0⟩ := hperp f hf
    refine hmk _ ((isGKSub_gkGen θ M ψ).lie τ X hX f hfN) fun a ha => ?_
    rw [hL τ X hX a (hAle ha) f hfN, hf0 _ (hAP.lie τ X hX a ha), neg_zero]
end GlobalTheory.CuspGK
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForms_eq_iSup_irreducible_gK : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S), IsInfFam (D := D) θ →
    ∀ ψ : GA D V → ℂ, IsAutFunSm θ V ψ → IsCuspFun V ψ →
    (∃ W : Submodule ℂ (GA D V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ),
      M.fr τ * g * (M.fr τ)⁻¹ ∈ Formalism.REAL.Kset (M.ε τ) → ∀ f ∈ W, rTr V (atTau θ V τ g) f ∈ W) →
    ψ ∈ ⨆ (A : Submodule ℂ (GA D V → ℂ)) (_ : A ≤ GlobalTheory.CuspGK.gkGen θ M ψ ∧ GlobalTheory.CuspGK.IsIrrGKSub θ M A), A := by
  first | exact @_root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK | exact _root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK | (intros; apply _root_.GlobalTheory.CuspGK.cuspForm_mem_iSup_irreducible_gK <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EvLgGFieldOfSmallField
section
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain
namespace GlobalTheory.TwInputs.SmallField
end GlobalTheory.TwInputs.SmallField
namespace GlobalTheory.TwInputs.SmallField
end GlobalTheory.TwInputs.SmallField
namespace GlobalTheory.TwInputs.SmallField
end GlobalTheory.TwInputs.SmallField
namespace GlobalTheory.TwInputs.SmallField
end GlobalTheory.TwInputs.SmallField
namespace GlobalTheory.TwInputs.SmallField
open Formalism.MainNotions.N Formalism.L2 Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
theorem evLgG_field_of_small_field : _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayer → EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt),
    (∀ X : GlobalTheory.TwInputs.RealSide (w.st Z).toD7, X.R.C = (TC.cf w.I w.l Z) → GlobalTheory.TwInputs.FieldOk X) ∧
    ∃ L : GlobalTheory.LamTie.LamDat (w.st Z).toD7, L.C = (TC.cf w.I w.l Z) ∧ L.Ok ∧ L.Teich ∧ L.q0 = AbsolutelyIrreducibleSpan.q0 (w.st Z).toD7 ∧
      ∀ a, (L.chi a).ValuesIn 0 (embLL0 (w.st Z).toD7) := by
  intro hP
  refine evG_good.imp fun K C5 c6 Cb hG _ => ?_
  refine (lg_fieldOk hP.rayF K).imp fun B f _ hO h _ T w Z => ?_
  obtain ⟨-, h1, h2⟩ := h w.C Z.W Z.V Z.S Z.N Z.G
  rw [cf_eq_at]
  obtain ⟨L, a, b, c, d, e⟩ := h2 (auxiliary_prime_ne_type_prime K C5 c6 Cb hG B.toPre hO)
  exact ⟨h1, L, c, a, b, d, e⟩
end GlobalTheory.TwInputs.SmallField
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsGenericRepresentation
section
section
noncomputable section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
namespace GlobalTheory.GenRep
open scoped Classical in
theorem exists_generic_representation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DerEx → VacLine →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    ∃ (ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) ∧
      (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ActsBy τ C ω₀ Φ (fockAct2 P Q R S) c₀ := by
  intro hP hD hV F E _ _ _ _ _ σ α β κ _ _ _ _ _ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ρ, c₀, hR, hcont, hder⟩ := _root_.GlobalTheory.T.archimedean_component_discreteSeries hP hD hV F E σ α β κ P Q R S ψ τ JA JB d a b A C Φ hCM hψ hFr hΦ
  obtain ⟨ω₀, hω⟩ := GlobalTheory.T.exists_adelicRep_extending_archimedeanSchwartzRep F κ (UG (cA σ) JB) ρ
  have hgen : ∀ g, ∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ := by
    intro g φ hφ
    unfold schA at hφ ⊢
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      rw [hω]
      exact Submodule.subset_span ⟨ρ g f, h, hh, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx
  have h1m : At (evI F) (((1 : UG (cA σ) JB).1 : Matrix β β (AE F E)) - 1) := fun u _ => by simp
  have hact1 : ∀ x : Matrix α β (AE F E), actB (cA σ) (1 : UG (cA σ) JB) x = x := fun x => by simp [actB]
  refine ⟨ω₀, c₀, fun g hg => ⟨hgen g, fun w φ hφ => ?_, fun μ hμ φ hφ =>
    GlobalTheory.T.weil_operator_unitary_adelic_L2 F κ (ρ g).toLinearMap (ω₀ g) (hω g) (hR g hg).2 μ hμ φ hφ⟩, fun l hl φ hφ => ?_, ?_⟩
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨u, H, hu, hsplit⟩ := GlobalTheory.T.heisenbergRho_split_archimedean_finite F E σ α β κ ψ JA JB d w
      obtain ⟨f₁, hf₁⟩ := GlobalTheory.T.heisenbergRho_archimedean_adelicPureTensor F E σ α β κ ψ JA JB d hψ u hu f
      have e1 : d.rho ψ w (pureA F f h) = pureA F f₁ (H h) := by
        have := hsplit 1 h1m f f₁ h (by simpa only [hact1] using hf₁)
        simpa only [hact1] using this
      rw [e1, hω, hω]
      exact (hsplit g hg (ρ g f) (ρ g f₁) h ((hR g hg).1 u hu f f₁ hf₁)).symm
    | zero => rw [rho_zero', map_zero, rho_zero']
    | add x y _ _ hx hy => rw [rho_add', map_add, map_add, hx, hy, rho_add']
    | smul c x _ hx => rw [rho_smul', map_smul, map_smul, hx, rho_smul']
  · unfold schA at hφ
    induction hφ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, h, hh, rfl⟩ := hx
      obtain ⟨T, hT⟩ := hl h hh
      have e : (fun g => l (ω₀ g (pureA F f h))) = fun g => T (ρ g f) := funext fun g => by rw [hω, hT]
      rw [e]
      exact hcont T f
    | zero => simp only [map_zero]; exact continuousOn_const
    | add x y _ _ hx hy => simp only [map_add]; exact hx.add hy
    | smul c x _ hx => simp only [map_smul, smul_eq_mul]; exact continuousOn_const.mul hx
  · intro γ hγ Y hY T h hh l hl
    obtain ⟨L, hL⟩ := hl h hh
    show HasDerivAt (fun t : ℝ => l (ω₀ (γ (Multiplicative.ofAdd t)) (pureA F (Φ T) h))) _ 0
    simp only [hω, hL]
    exact hder γ hγ Y hY T L
end GlobalTheory.GenRep
end
end

section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGeneric_localComponent : _root_.GlobalTheory.FunPr.ThetaLocalInputs → DerEx → VacLine →
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → IsStd ψ →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    ∃ (ω₀ : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (c₀ : InfinitePlace F → ℂ),
      (∀ g : UG (cA σ) JB, At (evI F) ((g.1 : Matrix β β (AE F E)) - 1) →
        (∀ φ ∈ schA F κ, ω₀ g φ ∈ schA F κ) ∧
        (∀ w, ∀ φ ∈ schA F κ, ω₀ g (d.rho ψ w φ) = d.rho ψ (actB (cA σ) g w) (ω₀ g φ)) ∧
        ∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
          ∀ φ ∈ schA F κ, ∫⁻ x, ‖ω₀ g φ x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) ∧
      (∀ l ∈ (adeleClass F).adm κ, ∀ φ ∈ schA F κ,
        ContinuousOn (fun g => l (ω₀ g φ)) {g : UG (cA σ) JB | At (evI F) ((g.1 : Matrix β β (AE F E)) - 1)}) ∧
      ActsBy τ C ω₀ Φ (fockAct2 P Q R S) c₀ := by
  first | exact @_root_.GlobalTheory.GenRep.exists_generic_representation | exact _root_.GlobalTheory.GenRep.exists_generic_representation | (intros; apply _root_.GlobalTheory.GenRep.exists_generic_representation <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsKFiniteApproxOfCuspForm
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.KFinCuspApprox
theorem exists_kFinite_approx_of_cusp_form : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ ψ : GA D (G.V i j).V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ ∧ (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) ∧ ∀ g, ‖φ g - ψ g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  intro hP D G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG i j hi hj φ hφ a δ hδ
  have hθ : IsInfFam R.θ := hR.inf
  have hS : (G.V i j).V.SigOK := GlobalTheory.ThetaLiftTypeTh.sigOK_vert G hG hi hj
  have hA : ∀ τ (e : Formalism.REAL.KG ((G.V i j).M.ε τ) → ℂ), Continuous e → GlobalTheory.TypeSum.KFinFun ((G.V i j).M.ε τ) e →
      ∀ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ →
        GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) (GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ) := by
    intro τ e he hK ψ hψ
    refine ⟨?_, _root_.GlobalTheory.T.kFinite_cuspForm_average_approx R.θ hθ hP (G.V i j) τ e he ψ hψ.1 hψ.2.1, fun τ' => ?_⟩
    · exact GlobalTheory.T.isSmoothAutomorphicFunction_compactFamily_average D R.θ hθ (G.V i j).V τ (Formalism.REAL.KG ((G.V i j).M.ε τ)) (Formalism.REAL.muK ((G.V i j).M.ε τ)) _
        GlobalTheory.SeriesToClosure.continuous_conjK
        (fun k => GlobalTheory.Published.AutFin.conj_mem_UH ((G.V i j).M.fr_unit τ) ((G.V i j).M.fr_gram τ) k) e he ψ hψ.1
    · by_cases h : τ' = τ
      · subst h
        exact _root_.GlobalTheory.T.kFinite_cusp_average_hasKType hP R.θ hθ (G.V i j) hS τ' e he hK ψ hψ
      · exact _root_.GlobalTheory.T.kType_preserved_average_other_place hP R.θ hθ (G.V i j) hS τ τ' h e he hK ψ hψ
  have hlin : ∀ τ (e : Formalism.REAL.KG ((G.V i j).M.ε τ) → ℂ), Continuous e → ∀ f f' : GA D (G.V i j).V → ℂ,
      Continuous f → Continuous f' → ∀ g, GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e f g -
        GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e f' g = GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e (f - f') g := by
    intro τ e he f f' hf hf' g
    have hk : Continuous fun k : Formalism.REAL.KG ((G.V i j).M.ε τ) =>
        atTau R.θ (G.V i j).V τ (((G.V i j).M.fr τ)⁻¹ * Formalism.REAL.toMK k * (G.V i j).M.fr τ) :=
      (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ (G.V i j).V τ).comp_continuous GlobalTheory.SeriesToClosure.continuous_conjK
        fun k => GlobalTheory.Published.AutFin.conj_mem_UH ((G.V i j).M.fr_unit τ) ((G.V i j).M.fr_gram τ) k
    have c1 : Continuous fun k : Formalism.REAL.KG ((G.V i j).M.ε τ) =>
        e k * f (g * atTau R.θ (G.V i j).V τ (((G.V i j).M.fr τ)⁻¹ * Formalism.REAL.toMK k * (G.V i j).M.fr τ)) :=
      he.mul (hf.comp (continuous_const.mul hk))
    have c2 : Continuous fun k : Formalism.REAL.KG ((G.V i j).M.ε τ) =>
        e k * f' (g * atTau R.θ (G.V i j).V τ (((G.V i j).M.fr τ)⁻¹ * Formalism.REAL.toMK k * (G.V i j).M.fr τ)) :=
      he.mul (hf'.comp (continuous_const.mul hk))
    have i1 := GlobalTheory.ExpansionAverage.integrable_K c1
    have i2 := GlobalTheory.ExpansionAverage.integrable_K c2
    simp only [GlobalTheory.KFinCuspApprox.avgN, GlobalTheory.SeriesToClosure.avg, Pi.sub_apply, mul_sub]
    exact (integral_sub i1 i2).symm
  have key : ∀ l : List D.what₂.Tau, l.Nodup → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ δ : ℝ, 0 < δ →
      ∃ ψ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ ∧ ∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ),
        FiniteDimensional ℂ W ∧ ψ ∈ W ∧ (∀ f ∈ W, Continuous f) ∧ GlobalTheory.KFinCuspApprox.KStab R.θ (G.V i j) {τ | τ ∈ l} W ∧
        ∀ g, ‖φ g - ψ g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
    intro l
    induction l with
    | nil =>
      intro _ φ hφ δ hδ
      refine ⟨φ, hφ, Submodule.span ℂ {φ}, inferInstance, Submodule.mem_span_singleton_self φ, fun f hf => ?_,
        by simpa using GlobalTheory.KFinCuspApprox.kStab_empty R.θ (G.V i j) _, fun g => by simpa using hδ.le⟩
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hf
      exact hφ.1.cont.const_smul c
    | cons τ l ih =>
      intro hnd φ hφ δ hδ
      rw [List.nodup_cons] at hnd
      obtain ⟨e, he, hK, happ⟩ := _root_.GlobalTheory.T.cuspForm_approximation_single_place hP R.θ hθ (G.V i j) φ hφ τ a (δ / 2) (by linarith)
      obtain ⟨C, hC0, hC⟩ := GlobalTheory.T.avgOverMaximalCompact_weighted_supNorm_bound R.θ hθ (G.V i j) τ e he a
      obtain ⟨ψ', hψ', W', hW'f, hψW', hW'c, hW's, hb⟩ := ih hnd.2 φ hφ (δ / (2 * (C + 1))) (by positivity)
      obtain ⟨W, hWf, hWc, hWs, hWm⟩ :=
        GlobalTheory.T.exists_finiteDim_stable_space_maxCompactAverages R.θ hθ (G.V i j) τ e hK {τ | τ ∈ l} hnd.1 W' hW'f hW'c hW's
      refine ⟨_, hA τ e he hK ψ' hψ', W, hWf, hWm ψ' hψW', hWc, by simpa [Set.insert_def] using hWs, fun g => ?_⟩
      have h1 := happ g
      have h2 := hC (φ - ψ') _ hb g
      rw [← hlin τ e he φ ψ' hφ.1.cont hψ'.1.cont g] at h2
      have hq : 0 ≤ GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a := pow_nonneg (GlobalTheory.Grow.quotHeight_pos _ g).le a
      have e1 : φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g =
          (φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g) +
            (GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g) := by ring
      have h3 : C * (δ / (2 * (C + 1))) ≤ δ / 2 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      calc ‖φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a
          ≤ (‖φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g‖ +
              ‖GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e φ g - GlobalTheory.KFinCuspApprox.avgN R.θ (G.V i j) τ e ψ' g‖) *
              GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a := by
            rw [e1]; exact mul_le_mul_of_nonneg_right (norm_add_le _ _) hq
        _ ≤ δ / 2 + δ / 2 := by rw [add_mul]; linarith
        _ = δ := by ring
  obtain ⟨ψ, hψ, W, hWf, hψW, -, hWs, hb⟩ := key Finset.univ.toList (Finset.nodup_toList _) φ hφ δ hδ
  refine ⟨ψ, hψ, ⟨W, hWf, hψW, fun τ g hg hk f hf => hWs τ (Finset.mem_toList.2 (Finset.mem_univ τ)) g hg hk f hf⟩, hb⟩
end GlobalTheory.KFinCuspApprox
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kFinite_cusp_forms_dense : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ i j, i ≤ D.R.m → j ≤ D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → ∀ (a : ℕ) (δ : ℝ), 0 < δ → ∃ ψ : GA D (G.V i j).V → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) ψ ∧ (∃ W : Submodule ℂ (GA D (G.V i j).V → ℂ), FiniteDimensional ℂ W ∧ ψ ∈ W ∧ ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.V i j).V τ), (G.V i j).M.fr τ * g * ((G.V i j).M.fr τ)⁻¹ ∈ Formalism.REAL.Kset ((G.V i j).M.ε τ) → ∀ f ∈ W, Formalism.L2.Theta.rTr (G.V i j).V (Formalism.L2.Theta.atTau R.θ (G.V i j).V τ g) f ∈ W) ∧ ∀ g, ‖φ g - ψ g‖ * GlobalTheory.Grow.quotHeight (G.V i j).V g ^ a ≤ δ := by
  first | exact @_root_.GlobalTheory.KFinCuspApprox.exists_kFinite_approx_of_cusp_form | exact _root_.GlobalTheory.KFinCuspApprox.exists_kFinite_approx_of_cusp_form | (intros; apply _root_.GlobalTheory.KFinCuspApprox.exists_kFinite_approx_of_cusp_form <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsWeilRepArchimedeanSmoothOrbit
section
section
open scoped Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
theorem GlobalTheory.WeilArchSmooth.exists_weilRep_archimedean_smooth_orbit : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∀ f : SInf F (Fin n × Fin d), ∃ (c : ℝ → SInf F (Fin n × Fin d)) (c' : SInf F (Fin n × Fin d)),
      c 0 = f ∧ Filter.Tendsto (fun t : ℝ => t⁻¹ • (c t - f)) (nhdsWithin 0 {0}ᶜ) (nhds c') ∧
      ∀ t : ℝ, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) (⇑f) (⇑(c t)) := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hcm hψ hw γ hγ f
  obtain ⟨l, _, _, Φ, g, T, hgc, hg0, hgm, hgs, hT0, hTm, hTi, hTu, hTc, hTa⟩ :=
    _root_.GlobalTheory.T.archimedean_line_spanned_by_weil_vector hP M ψ χX χW om hcm hψ hw γ hγ
  obtain ⟨Z, hZ, hgZ⟩ := GlobalTheory.T.exists_symplecticLie_eq_exp_oneParam l g hgc hg0 hgm hgs
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.T.metaplectic_lift_scalar_derivative_eq hP l Z hZ T hT0 hTm
    (fun t w h h₁ e => by rw [← hgZ t]; exact hTi t w h h₁ e) hTu hTc
  refine ⟨fun t => Φ.symm (T t (Φ f)), Φ.symm (a • Φ f + GlobalTheory.RealWeil.quad Z (Φ f)), ?_, ?_, fun t => hTa t f⟩
  · simp [hT0]
  · have h := (Φ.symm.continuous.tendsto _).comp (ha (Φ f))
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, ← Complex.coe_smul, map_smul, map_sub, ContinuousLinearEquiv.symm_apply_apply]
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Hypotheses3
section
section
namespace GlobalTheory.PrimIn
structure PublishedThetaConditionTheorems : Prop where
  q1 : GlobalTheory.Hk3.HoweUnram
  q2 : GlobalTheory.Published.CuspRapidDecay
  q3 : GlobalTheory.Published.HarishChandraFinite
  q4 : GlobalTheory.Published.HarishChandraModules
  q5 : GlobalTheory.Published.DiscreteSeriesCover
  q6 : GlobalTheory.Published.CasselmanWallach
  q7 : GlobalTheory.Published.WeilSiegelFormulaUnitary
  sw : GlobalTheory.Published.SiegelWeilUnitaryConvergent
  q9 : _root_.GlobalTheory.Published.DoublingMethodLocalZetaIntegrals
  q10 : GlobalTheory.Published.UnramifiedDoublingGL
  q11 : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  q12 : GlobalTheory.Published.GreenCuspidal
  q13 : GlobalTheory.Published.WeilRepresentationUnitaryPair
  q14 : GlobalTheory.Published.SchurOrthogonalitySquareIntegrable
theorem PublishedThetaConditionTheorems.q8 (h : _root_.GlobalTheory.PrimIn.PublishedThetaConditionTheorems) : ∀ D : Formalism.BasicNotions.D7, GlobalTheory.Core.Rk.SW.HeckeFormNS D := fun D =>
  GlobalTheory.Core.Rk.SW.heckeFormNS_of_heckeForm
    (_root_.GlobalTheory.Core.Rk.IP.heckeForm_of_doubling' h.q13 h.q2 h.q7 h.sw h.q9 h.q10 D)
end GlobalTheory.PrimIn
end
end

