import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0591
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1918
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0592
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0572
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0593
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0511
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteUnfSupportOfNeOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentStepsInvariantVertex

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLieWordExpansionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lie_word_expansion : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (τ : D.what₂.Tau) (f : GA D N.V → ℂ), IsAutFunSm θ N.V f → IsTypeAt θ N.V τ (N.S τ) f → ∀ x : GA D N.V, ∃ (S : List (List (Mx N.V.rank))) (v : ℕ → N.M.H τ) (ℓ : ℕ → (N.M.H τ →ₗ[ℂ] ℂ)) (C : ℕ → ℝ), Words (lieSet (N.M.ε τ)) S ∧ Ctrl (lieSet (N.M.ε τ)) (UJset (N.M.ε τ)) (N.M.σ τ) S ∧ Expn (N.M.ε τ) (N.M.σ τ) S v ℓ C (res θ N.V τ (N.M.fr τ) f x) := by
  first | exact @GlobalTheory.PlaceDecomp.exists_expn_model | exact GlobalTheory.PlaceDecomp.exists_expn_model | (intros; apply GlobalTheory.PlaceDecomp.exists_expn_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPartialFourierColumnBlockSchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_partialFourier_columnBlock_schwartzBruhat : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∃ 𝓕 : (Matrix A C k → ℂ) →ₗ[ℂ] (Matrix A C k → ℂ), Set.BijOn 𝓕 (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) (GlobalTheory.WeilM.SB (Matrix A C k) : Set _) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∈ P, T r s = 0) → (∀ r, ∀ s ∉ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => 𝓕 Ξ (Z + (T + R))) ∧
      (∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ T R : Matrix A C k, (∀ r, ∀ s ∉ P, T r s = 0) → (∀ r, ∀ s ∈ P, R r s = 0) →
        𝓕 (fun S => (ψ (pairM S R) : ℂ) * Ξ (S + T)) = fun Z => (ψ (pairM Z R - pairM Z T) : ℂ) * 𝓕 Ξ Z) ∧
      ∀ Ξ ∈ GlobalTheory.WeilM.SB (Matrix A C k), ∀ n, IsNatDatum ϖ n (𝓕 Ξ) → fourierSum ψ⁻¹ ϖ n P (𝓕 Ξ) = Ξ := by
  first | exact @GlobalTheory.ColFourier.exists_blockFourier | exact GlobalTheory.ColFourier.exists_blockFourier | (intros; apply GlobalTheory.ColFourier.exists_blockFourier <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPerfectPairingCoefficientSpaceTensorModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoefPairTens

open GlobalTheory.DefLift GlobalTheory.DefiniteMult Formalism.IndefR.Mult

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem sigma_one (M : DSModel V S) (τ : D.what₂.Tau) : M.σ τ 1 = 1 := (M.ds τ).2.2.1.1.1

theorem sigma_mul (hp : AllPlus M) (τ : D.what₂.Tau) (a b : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    M.σ τ ((a : Matrix (Fin V.rank) (Fin V.rank) ℂ) * b) = (M.σ τ a).comp (M.σ τ b) := by
  have hm : ∀ x : Matrix.unitaryGroup (Fin V.rank) ℂ,
      (x : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᴴ * Formalism.REAL.Jm (M.ε τ) * x = Formalism.REAL.Jm (M.ε τ) := fun x => by
    rw [hp.jm τ, Matrix.mul_one]
    exact Matrix.mem_unitaryGroup_iff'.1 x.2
  exact (M.ds τ).2.2.1.1.2 _ (hm a) _ (hm b)

theorem sigma_comp_inv (hp : AllPlus M) (τ : D.what₂.Tau) (v : Matrix.unitaryGroup (Fin V.rank) ℂ) :
    ((M.σ τ v : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) ∘ₗ
      ((M.σ τ (v⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ) = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  show M.σ τ v (M.σ τ (v⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) x) = x
  rw [← ContinuousLinearMap.comp_apply, ← sigma_mul hp, ← Submonoid.coe_mul, mul_inv_cancel, OneMemClass.coe_one,
    sigma_one]
  rfl

theorem unfr_one (M : DSModel V S) (τ : D.what₂.Tau) : unfr M τ 1 = 1 := by
  unfold unfr
  rw [Matrix.mul_one, Matrix.nonsing_inv_mul _ (fr_det M τ)]

theorem pairEquiv_realAll : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : Formalism.IndefR.Mult.DSModel V S) (θ : InfFam D) (c : CoefA V) (pr : c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ), IsInfFam θ → GlobalTheory.DefLift.AllPlus M → c.Is → IsDualPair θ M c pr → ∃ E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ), ∀ (u : UG D.what₂.Tau V.rank) (w : c.W), E (c.ρ (realAll θ V (fun τ => GlobalTheory.DefLift.unfr M τ (u τ))) w) = E w ∘ₗ PiTensorProduct.map (fun τ => ((M.σ τ ((u τ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)) := by
  intro D V S M θ c pr hθ hp hc hpr
  classical
  have m := AllPlus.finite_smooth_irreducible D V S M hp
  obtain ⟨-, inj, π, hπ, -⟩ := tensor_irreducible D V S M m hp
  have key := pair_tens hp (fun τ => (m τ).2.1) inj hπ hpr
  have hb := pair_bijective hθ hp hc hpr
  let e : SmT M ≃ₗ[ℂ] ⨂[ℂ] τ, M.H τ := PiTensorProduct.congr fun τ => LinearEquiv.ofTop (M.sm τ) (m τ).2.1
  have he : ∀ x, e x = inclT M x := fun x => rfl
  let E : c.W ≃ₗ[ℂ] Module.Dual ℂ (⨂[ℂ] τ, M.H τ) := (LinearEquiv.ofBijective pr hb).trans e.symm.dualMap
  have hE : ∀ w y, E w y = pr w (e.symm y) := fun w y => rfl
  let F : ∀ τ, Matrix.unitaryGroup (Fin V.rank) ℂ → (M.H τ →ₗ[ℂ] M.H τ) := fun τ v =>
    ((M.σ τ v : M.H τ →L[ℂ] M.H τ) : M.H τ →ₗ[ℂ] M.H τ)
  have hact : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ), actT M τ (unfr M τ v) =
      PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v)) := by
    intro τ v
    unfold actT
    rw [rep_unfr]
  have hπe : ∀ τ v x, π τ v x = e.symm (actT M τ (unfr M τ v) (e x)) := fun τ v x => by
    apply e.injective
    rw [LinearEquiv.apply_symm_apply, he, he, hπ]
  have hinv : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ) x, π τ v (π τ v⁻¹ x) = x := by
    intro τ v x
    rw [hπe, hπe, LinearEquiv.apply_symm_apply, hact, hact, ← LinearMap.comp_apply (PiTensorProduct.map _),
      ← PiTensorProduct.map_comp]
    have : (fun ρ => Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v) ρ ∘ₗ
        Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v⁻¹) ρ) = fun ρ => LinearMap.id := by
      funext ρ
      by_cases h : ρ = τ
      · subst h
        simp only [Function.update_self]
        exact GlobalTheory.CoefPairTens.sigma_comp_inv hp ρ v
      · simp only [Function.update_of_ne h, LinearMap.id_comp]
    rw [this, PiTensorProduct.map_id, LinearMap.id_apply, LinearEquiv.symm_apply_apply]
  have one : ∀ τ (v : Matrix.unitaryGroup (Fin V.rank) ℂ) w,
      E (c.ρ (atTau θ V τ (unfr M τ v)) w) =
        E w ∘ₗ PiTensorProduct.map (Function.update (fun ρ => (LinearMap.id : M.H ρ →ₗ[ℂ] M.H ρ)) τ (F τ v⁻¹)) := by
    intro τ v w
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearMap.comp_apply, hE, hE, ← hact, ← hπe, LinearEquiv.symm_apply_apply]
    have h1 := key τ v (c.ρ (atTau θ V τ (unfr M τ v)) w) (π τ v⁻¹ x)
    rw [hinv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h1
    exact h1
  refine ⟨E, fun u w => ?_⟩
  let us : Finset D.what₂.Tau → UG D.what₂.Tau V.rank := fun s ρ => if ρ ∈ s then u ρ else 1
  have hM : ∀ (s : Finset D.what₂.Tau) ρ, unfr M ρ (us s ρ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V ρ) := fun s ρ =>
    hp.unfr_mem ρ _
  have ind : ∀ s : Finset D.what₂.Tau, ∀ w, E (c.ρ (realAll θ V (fun ρ => unfr M ρ (us s ρ))) w) =
      E w ∘ₗ PiTensorProduct.map (fun ρ => F ρ (us s ρ)⁻¹) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro w
      have h0 : (fun ρ => unfr M ρ (us ∅ ρ)) = 1 := by
        funext ρ
        have : us ∅ ρ = 1 := if_neg (Finset.notMem_empty ρ)
        rw [this, OneMemClass.coe_one, Pi.one_apply]
        exact GlobalTheory.CoefPairTens.unfr_one M ρ
      have h1 : (fun ρ => F ρ (us ∅ ρ)⁻¹) = fun ρ => LinearMap.id := by
        funext ρ
        have : us ∅ ρ = 1 := if_neg (Finset.notMem_empty ρ)
        show ((M.σ ρ ((us ∅ ρ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) : M.H ρ →L[ℂ] M.H ρ) : M.H ρ →ₗ[ℂ] M.H ρ) = _
        rw [this, inv_one, OneMemClass.coe_one, GlobalTheory.CoefPairTens.sigma_one]
        rfl
      rw [h0, realAll_one hθ, map_one, Module.End.one_apply, h1, PiTensorProduct.map_id, LinearMap.comp_id]
    | insert τ s hτ ih =>
      intro w
      have hs : us s τ = 1 := if_neg hτ
      have h3 : us (insert τ s) τ = u τ := if_pos (Finset.mem_insert_self τ s)
      have h4 : ∀ ρ, ρ ≠ τ → us (insert τ s) ρ = us s ρ := fun ρ h => by
        simp only [us, Finset.mem_insert, h, false_or]
      rw [realAll_eq_atTau_mul hθ (hM (insert τ s)) τ]
      have h2 : Function.update (fun ρ => unfr M ρ (us (insert τ s) ρ)) τ 1 = fun ρ => unfr M ρ (us s ρ) := by
        funext ρ
        by_cases h : ρ = τ
        · rw [h, Function.update_self, hs, OneMemClass.coe_one, GlobalTheory.CoefPairTens.unfr_one]
        · rw [Function.update_of_ne h, h4 ρ h]
      rw [h2, map_mul, Module.End.mul_apply, h3, one, ih, LinearMap.comp_assoc, ← PiTensorProduct.map_comp]
      congr 2
      funext ρ
      by_cases h : ρ = τ
      · subst h
        rw [Function.update_self, hs, h3]
        show ((M.σ ρ ((1 : Matrix.unitaryGroup (Fin V.rank) ℂ)⁻¹ : Matrix.unitaryGroup (Fin V.rank) ℂ) :
          M.H ρ →L[ℂ] M.H ρ) : M.H ρ →ₗ[ℂ] M.H ρ) ∘ₗ F ρ (u ρ)⁻¹ = F ρ (u ρ)⁻¹
        rw [inv_one, OneMemClass.coe_one, GlobalTheory.CoefPairTens.sigma_one]
        rfl
      · rw [Function.update_of_ne h, h4 ρ h, LinearMap.comp_id]
  have huniv : us Finset.univ = u := funext fun ρ => if_pos (Finset.mem_univ ρ)
  have := ind Finset.univ w
  rw [huniv] at this
  exact this

end GlobalTheory.CoefPairTens

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceIsoReadingComponentsCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

noncomputable section

namespace GlobalTheory.FlipMatch

open GlobalTheory.LFun GlobalTheory.LFun.SplitTie

section Place

variable {D : D7} {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)

theorem complMap_apply_under {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {v : Pl F} {w : Pl E} (h : w.under (𝓞 F) = v) (b : Af F) :
    complMap h (b v) = GlobalTheory.AdeleBaseChange.locMap F w (b (w.under (𝓞 F))) := by
  subst h; rfl

theorem piW_tmul (b : AF D.host.F) (x : D.host.E) : piW τ (b ⊗ₜ[D.host.F] x) = evFin D.host.F v b * τ x := by
  show splitProj τ (compFin D.host.F D.host.E v (b ⊗ₜ[D.host.F] x)) = _
  rw [compFin, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.map_tmul]
  rfl

theorem cpt_tmul (w : Pl D.host.E) (b : AF D.host.F) (x : D.host.E) :
    cpt (D := D) w (toEAf D (b ⊗ₜ[D.host.F] x)) =
      algebraMap D.host.E _ x * GlobalTheory.AdeleBaseChange.locMap D.host.F w (b.2 (w.under (𝓞 D.host.F))) := by
  have e : toEAf D (b ⊗ₜ[D.host.F] x) = x ⊗ₜ[D.host.F] b.2 := rfl
  rw [e]
  show (toAd D (x ⊗ₜ[D.host.F] b.2)) w = _
  rw [toAd_spec]
  rfl

theorem isPlaceIso_complEquiv : IsPlaceIso τ (splitPrime τ) (complEquiv τ (splitPrime_under τ)) := by
  intro a
  induction a using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | tmul b x =>
    rw [piW_tmul, cpt_tmul, complEquiv_apply, map_mul, complMap_apply_emb, mul_comm]
    congr 1
    exact complMap_apply_under (splitPrime_under τ) b.2
  | add x y hx hy =>
    rw [RingHom.map_add (piW τ), RingEquiv.map_add, RingHom.map_add (toEAf D), RingHom.map_add (cpt _), hx, hy]

theorem isEquiv_Fv {F : Type} [Field F] [NumberField F] (v : Pl F) :
    (ValuativeRel.valuation (Fv F v)).IsEquiv (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))) :=
  haveI : (Valued.v : Valuation (Fv F v) (WithZero (Multiplicative ℤ))).Compatible := Valuation.Compatible.ofValuation _
  ValuativeRel.isEquiv _ _

theorem valued_complEquiv_symm (y : Kw (D := D) (splitPrime τ)) :
    Valued.v ((complEquiv τ (splitPrime_under τ)).symm y) = Valued.v y := by
  conv_rhs => rw [← (complEquiv τ (splitPrime_under τ)).apply_symm_apply y]
  rw [complEquiv_apply, SplitTie.valued_complMap]

theorem continuous_complEquiv_symm : Continuous (complEquiv τ (splitPrime_under τ)).symm := by
  refine continuous_of_continuousAt_zero (complEquiv τ (splitPrime_under τ)).symm ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_right_iff]
  intro γ _
  have h0 : MonoidWithZeroHom.ValueGroup₀.embedding γ.1 ≠ 0 := by simp
  obtain ⟨k, hk⟩ : ∃ k : ℤ, MonoidWithZeroHom.ValueGroup₀.embedding γ.1 = WithZero.exp k :=
    ⟨_, (WithZero.exp_log h0).symm⟩
  filter_upwards [(GlobalTheory.Idele.isOpen_valued_le (K := D.host.E) (splitPrime τ) (-((k.natAbs + 1 : ℕ) : ℤ))).mem_nhds
    (by simp)] with a ha
  rw [Valuation.restrict_lt_iff_lt_embedding, hk, valued_complEquiv_symm]
  exact ha.trans_lt (WithZero.exp_lt_exp.2 (by omega))

theorem isLocIso_complEquiv : IsLocIso (complEquiv τ (splitPrime_under τ)) := by
  refine ⟨SplitChart.continuous_complMap _, continuous_complEquiv_symm τ, fun x => ?_⟩
  rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, (Good.isEquiv_Kw (D := D) _).le_one_iff_le_one,
    (isEquiv_Fv v).le_one_iff_le_one, complEquiv_apply, SplitTie.valued_complMap]

end Place

section Chars

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem chrW_nu {μ₀ : T} (hL : L.Is μ₀) (t : T) (i j : Fin D.R.m) (X : Chars D.host.F D.host.E)
    (hα : X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j) (hβ : X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j)
    {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : (Fv D.host.F v)ˣ) :
    chrW X.ν τ x = (locGrid G t (splitPrime τ)).nu i j
      (Units.map ((complEquiv τ (splitPrime_under τ) : Fv D.host.F v →* Kw (splitPrime τ))) x) := by
  have e1 : X.ν = G.nu t i (j + 1) := by
    show X.α / X.β = _
    rw [hα, hβ]
    exact mul_div_mul_right_eq_div _ _ _
  have e2 : chrW X.ν τ x = locChar X.ν (splitPrime τ)
      (Units.map ((complEquiv τ (splitPrime_under τ) : Fv D.host.F v →* Kw (splitPrime τ))) x) := rfl
  rw [e2, e1, locChar_eq_of_chrEq (SqNum.chrEq_nu G t i j hL)]
  have hj : (j : ℕ) < D.R.m := j.2
  simp only [SqNum.nuH, Grid.nu, locGrid, muBase, dif_pos hj, MonoidHom.div_apply, Formalism.L2.Host.HChar.loc_mul,
    Formalism.L2.Host.HChar.loc_inv, div_eq_mul_inv]
  rfl

end Chars

section Psi

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem at_atPl {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (y : Kw (D := D) (splitPrime τ)) :
    At (evFin D.host.F v) (atPl (splitPrime τ) y) := by
  classical
  intro u hu
  refine ae_ext ?_ fun Q => ?_
  · rw [Algebra.smul_def, RingHom.map_mul, (atPl_spec _ y).1, mul_zero, map_zero]
  · rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, (atPl_spec _ y).2, map_zero, map_zero]
    by_cases h : Q = splitPrime τ
    · subst h
      have h1 : cpt (D := D) (splitPrime τ) (toEAf D (algebraMap (AF D.host.F) (AE D) u)) =
          GlobalTheory.AdeleBaseChange.locMap D.host.F (splitPrime τ) (u.2 ((splitPrime τ).under (𝓞 D.host.F))) :=
        (comp_toAd D).base u (splitPrime τ)
      rw [h1, ← complMap_apply_under (splitPrime_under τ)]
      have h2 : u.2 v = 0 := hu
      rw [h2, map_zero, zero_mul]
    · rw [Pi.single_eq_of_ne h, mul_zero]

theorem psiLoc_eq_psiAt (W : G.Weil) {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : Fv D.host.F v) :
    psiLoc W.ψ v x = psiAt W (splitPrime τ) ((xiAt (splitPrime τ))⁻¹ * complEquiv τ (splitPrime_under τ) x) := by
  classical
  set w := splitPrime τ with hw
  set jj := complEquiv τ (splitPrime_under τ) with hjj
  have hξ : xiAt (D := D) w ≠ 0 := (map_ne_zero _).2 cmHost_imaginaryGenerator_ne_zero
  have hz : incA D D.host.xi0 * atPl w ((xiAt w)⁻¹ * jj x) = atPl w (jj x) := by
    rw [← Good.atPl_mul]
    congr 1
    rw [← mul_assoc]
    change xiAt w * (xiAt w)⁻¹ * jj x = jj x
    rw [mul_inv_cancel₀ hξ, one_mul]
  have hcm := isCMExt_host D
  have hp1 : piW τ (atPl w (jj x)) = x :=
    jj.injective (by rw [isPlaceIso_complEquiv τ, (atPl_spec w _).2, Pi.single_eq_same])
  have hp2 : piW (τ.comp D.sp.cm.sig) (atPl w (jj x)) = 0 :=
    (complEquiv (τ.comp D.sp.cm.sig) (splitPrime_under _)).injective (by
      rw [isPlaceIso_complEquiv (τ.comp D.sp.cm.sig), (atPl_spec w _).2, Pi.single_eq_of_ne (splitPrime_comp_ne hcm τ),
        map_zero])
  show psiLoc W.ψ v x = W.ψ (Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * atPl w ((xiAt w)⁻¹ * jj x)))
  rw [hz, GlobalTheory.T.adelicTrace_supportedAtSplitPlace hcm v τ _ (at_atPl τ _), hp1, hp2, add_zero]
  rfl

end Psi

theorem exists_placeIso_chars : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (t : T) (i j : Fin D.R.m) (X : Chars D.host.F D.host.E), X.α = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j → X.β = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j →
    ∀ {v : Pl D.host.F} (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (w : Pl D.host.E), splitPrime τ = w →
    ∃ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso τ w jj ∧ IsLocIso jj ∧
      (∀ x, chrW X.ν τ x = (locGrid G t w).nu i j (Units.map (jj : Fv D.host.F v →* Kw w) x)) ∧
      ∀ x, psiLoc W.ψ v x = psiAt W w ((xiAt w)⁻¹ * jj x) := by
  intro D T L sc G μ₀ hL W t i j X hα hβ v τ w hw
  subst hw
  exact ⟨complEquiv τ (splitPrime_under τ), isPlaceIso_complEquiv τ, isLocIso_complEquiv τ,
    fun x => chrW_nu hL t i j X hα hβ τ x, fun x => psiLoc_eq_psiAt W τ x⟩

end GlobalTheory.FlipMatch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryCoordinateOfRationalPointDefiniteVeStatement
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

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open GlobalTheory.RatMoveJets

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitaryCoordinate_of_rationalPoint_definiteVertex : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc} {W : G.Weil}
    (S : GridChoice W Set.univ) (X : Node), DefNode D.R.m X → ∀ r : FinPt G X, GlobalTheory.MovedKappaEx.RatFin (G.V X) r →
    ∃ U : Matrix.unitaryGroup (Fin (G.V X).rank) D.host.E, GlobalTheory.RatMoveJets.RatCoord (G.V X) (S.N.fr X) r U := by
  first | exact @GlobalTheory.RatMoveJets.exists_unitary_ratCoord | exact GlobalTheory.RatMoveJets.exists_unitary_ratCoord | (intros; apply GlobalTheory.RatMoveJets.exists_unitary_ratCoord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowArgumentConjugateMoveLeftMulInvComponentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstRowArgument_conjugateMove_left_mul_inv_component : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T},
    t ∈ U → ∀ w ∈ locPl G t, ∀ (k : FinPt G (.grid 0 D.R.m))
      (ys : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
      S.rowAt t w (Function.update ys (GlobalTheory.FirstRowVertex.firstIx D) (actO (G.pS (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T)) (G.pT (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T))
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).1⁻¹
        (G.toPair (.chi (GlobalTheory.FirstRowVertex.firstIx D) D.R.m : Pair T) ((S.N.u (.grid 0 D.R.m))⁻¹ * k * S.N.u (.grid 0 D.R.m)).1 1).2⁻¹ (ys (GlobalTheory.FirstRowVertex.firstIx D)))) =
      Function.update (S.rowAt t w ys) 0 (((GlobalTheory.FirstRowTermLaw.kapAt S t w k)⁻¹ : GL (Fin ((locGrid G t w).rank (0, (locGrid G t w).m))) (Kw w)).val * S.rowAt t w ys 0) := by
  first | exact @GlobalTheory.FirstRowCoord.rowAt_first_move | exact GlobalTheory.FirstRowCoord.rowAt_first_move | (intros; apply GlobalTheory.FirstRowCoord.rowAt_first_move <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockComponentTransportedPointsEqJetOperatorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockComponent_transportedPoints_eq_jetOperator : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (x : FinPt G (.top j)) (y : FinPt G (.top (j + 1))),
      fockComp W S.N.frC (.top t j) (S.Z.vec d) (x * S.N.u _) (y * S.N.u _) =
        Formalism.L2.Ker.jetOp (wt G (.top j)) (wt G (.top (j + 1)))
          (fun m => W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j (MvPolynomial.monomial m 1)))
            (x : GA D (G.V (.top j))) (y : GA D (G.V (.top (j + 1)))))
          (nuEnd G (.top t j)) := by
  first | exact @GlobalTheory.AvgColJet.fockComp_frC_eq_jetOp | exact GlobalTheory.AvgColJet.fockComp_frC_eq_jetOp | (intros; apply GlobalTheory.AvgColJet.fockComp_frC_eq_jetOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentInnerStepsInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
open GlobalTheory.FunObj.FiniteSupport
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiPhase_adjacentInnerSteps_invariant : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {Γ : Grid k} (j : ℕ) (hA : j + 2 < Γ.m) (x x' : ColArgs Γ) (e e' : Vars Γ),
    (∀ i, i ≠ j → i ≠ j + 1 → x' i = x i) → (∀ i : Fin (Γ.m - 1), i.val ≠ j → i.val ≠ j + 1 → e' i = e i) →
    ch (stepPt (x' j) (e' ⟨j, by omega⟩)) + ch (stepPt (x' (j + 1)) (e' ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x' e' (j + 1) r * colVar x' e' ⟨j, by omega⟩ r else 0) =
      ch (stepPt (x j) (e ⟨j, by omega⟩)) + ch (stepPt (x (j + 1)) (e ⟨j + 1, by omega⟩)) +
        (if Even (Γ.m - 2 - j) then ∑ r, rowVar x e (j + 1) r * colVar x e ⟨j, by omega⟩ r else 0) →
    (Odd (Γ.m - 2 - j) → ∀ s : Fin (topRank Γ j), rowVar x' e' j s = rowVar x e j s) →
    (Odd (Γ.m - 2 - j) → ∀ r : Fin (topRank Γ (j + 1 + 1)), colVar x' e' ⟨j + 1, by omega⟩ r = colVar x e ⟨j + 1, by omega⟩ r) →
    phase x e = phase x' e' := by
  first | exact @GlobalTheory.TopLevelInv.phase_eq_of_two_steps | exact GlobalTheory.TopLevelInv.phase_eq_of_two_steps | (intros; apply GlobalTheory.TopLevelInv.phase_eq_of_two_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiPhaseAdjacentStepsInvariantVertexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiPhase_adjacentSteps_invariant_vertex : ∀ {k : Type} [Field k] {n₀ n n₂ : Type} [Fintype n₀] [DecidableEq n₀] [Fintype n] [DecidableEq n] [Fintype n₂] [DecidableEq n₂] {c : ℕ},
    ∀ v ∈ symN k n (c + 1), ∀ (κ : GL n k) (x₀ : Matrix n n₀ k) (e₀ : StepVar n (c + 1) n₀ → k) (x₁ : Matrix n₂ n k) (e₁ : StepVar n₂ c n → k)
      (d₀ : Matrix (n ⊕ Fin (c + 1)) (n₀ ⊕ Fin (c + 1 + 1)) k) (d₁ : Matrix (n₂ ⊕ Fin c) (n ⊕ Fin (c + 1)) k),
      d₀ = ((v * embX (c + 1) κ)⁻¹).val * stepPt x₀ e₀ → d₁ = stepPt x₁ e₁ * (v * embX (c + 1) κ).val →
      (ch d₀ + ch d₁ + (if Even (c + 1) then ∑ r : n, (∑ l : Fin c, if l.val = c / 2 then d₁ (.inr l) (.inl r) else 0) *
          d₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0) =
        ch (stepPt x₀ e₀) + ch (stepPt x₁ e₁) + (if Even (c + 1) then ∑ r : n,
          (∑ l : Fin c, if l.val = c / 2 then stepPt x₁ e₁ (.inr l) (.inl r) else 0) *
            stepPt x₀ e₀ (.inl r) (.inr ⟨(c + 1) / 2, by omega⟩) else 0)) ∧
      (Odd (c + 1) → (∀ s : n₀, d₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s) = stepPt x₀ e₀ (.inr ⟨(c + 1) / 2, by omega⟩) (.inl s)) ∧
        ∀ r : n₂, d₁ (.inl r) (.inr ⟨c / 2, by omega⟩) = stepPt x₁ e₁ (.inl r) (.inr ⟨c / 2, by omega⟩)) := by
  first | exact @GlobalTheory.PhaseStep.phase_step_inv | exact GlobalTheory.PhaseStep.phase_step_inv | (intros; apply GlobalTheory.PhaseStep.phase_step_inv <;> assumption)
end

