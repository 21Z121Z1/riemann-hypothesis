import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0165
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0060
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilPairLevelTrivialMapsLevelVectorStatement
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0066
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0073
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0062
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0051
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompAtOfFin
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0052
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsOrthonormalisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaKernelOrthonormalFrameInDomainPeriodLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0267
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0139
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0450
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DomainFrameEqRealTranslateMulBorel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameDecomp

theorem hermC_mulVec {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r → ℂ) :
    hermC τ G (x *ᵥ a) (x *ᵥ b) = ∑ i, ∑ j, a i * FD.gram τ G x i j * conj (b j) := by
  unfold hermC
  calc ∑ p, ∑ q, (x *ᵥ a) p * τ (G p q) * conj ((x *ᵥ b) q)
      = ∑ p, ∑ q, ∑ i, ∑ j, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        rw [Finset.sum_mul, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ p, ∑ i, ∑ q, ∑ j, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ j, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ p, ∑ j, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ p, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, a i * FD.gram τ G x i j * conj (b j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [FD.gram, Matrix.of_apply, FD.col, hermC, Finset.mul_sum, Finset.sum_mul]

theorem isometry_of_gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x y : Matrix (Fin r) (Fin r) ℂ) (hy : y.det ≠ 0) (h : FD.gram τ G x = FD.gram τ G y) (v w : Fin r → ℂ) :
    hermC τ G ((x * y⁻¹) *ᵥ v) ((x * y⁻¹) *ᵥ w) = hermC τ G v w := by
  have hyu : IsUnit y.det := isUnit_iff_ne_zero.mpr hy
  have hback : ∀ c : Fin r → ℂ, y *ᵥ (y⁻¹ *ᵥ c) = c := fun c => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hyu, Matrix.one_mulVec]
  calc hermC τ G ((x * y⁻¹) *ᵥ v) ((x * y⁻¹) *ᵥ w)
      = hermC τ G (x *ᵥ (y⁻¹ *ᵥ v)) (x *ᵥ (y⁻¹ *ᵥ w)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = hermC τ G (y *ᵥ (y⁻¹ *ᵥ v)) (y *ᵥ (y⁻¹ *ᵥ w)) := by
        rw [hermC_mulVec, hermC_mulVec, h]
    _ = hermC τ G v w := by rw [hback, hback]

theorem exists_real_point {D : D7} {S T : HSp D} (C : Ctx S T)
    (u : C.X.Ψ → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hu : ∀ (σ : C.X.Ψ) v w, hermC σ.1 C.X.Gm (u σ *ᵥ v) (u σ *ᵥ w) = hermC σ.1 C.X.Gm v w) :
    ∃ a ∈ GinfC T, (fun σ => (compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T a)).map conj) = u := by
  obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf
  obtain ⟨k, hk, hkτ⟩ := GlobalTheory.FockCompare.LiftUnitary.lift_unitary D C.θ σ₀ hσ₀ T
    (fun τ => (u (C.m.e τ)).map conj) (fun τ => by
      have hcc : ((u (C.m.e τ)).map conj).map conj = u (C.m.e τ) := by
        ext i j
        simp
      simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq]
      rw [GlobalTheory.StabProper.unitary_iff_form, hcc]
      intro v w
      have hform := hu (C.m.e τ) v w
      rw [GlobalTheory.StabProper.hermC_eq, GlobalTheory.StabProper.hermC_eq, Equiv.symm_apply_apply] at hform
      exact hform)
  refine ⟨k, hk, ?_⟩
  funext σ
  have hcomp : compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T k) = (u σ).map conj := by
    rw [GlobalTheory.StabProper.compAt_eq, ← GlobalTheory.FockCompare.RealAction.infMat_eq, hkτ, Equiv.apply_symm_apply]
  rw [hcomp]
  ext i j
  simp

theorem frame_decomp : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ x ∈ C.X.dom, ∃ a ∈ GinfC T, ∃ b ∈ Bor C.X.Ψ T.rank, x = rmul (C.xB (C.mvB a B)) b := by
  intro D S T C B hB x hx
  obtain ⟨o, b, -, -, hob, -⟩ := GlobalTheory.Ker.exists_orthonormalisation D.host.E T.rank C.X
  obtain ⟨hon, hbB, hxeq, -, -⟩ := hob x hx
  have hz : IsONFr C.X (C.xB B) := GlobalTheory.Ker.ONBasis.isONFr_xB C hB
  have hzdom : C.xB B ∈ C.X.dom := GlobalTheory.Ker.ONBasis.mem_dom C.X hz
  have hdet : ∀ σ, (FD.mat (C.xB B) σ).det ≠ 0 := fun σ => (hzdom σ).1
  obtain ⟨a, ha, hau⟩ := exists_real_point C
    (fun σ => FD.mat (o x) σ * (FD.mat (C.xB B) σ)⁻¹)
    (fun σ v w => isometry_of_gram_eq σ.1 C.X.Gm (FD.mat (o x) σ) (FD.mat (C.xB B) σ) (hdet σ)
      (by rw [hon σ, hz σ]) v w)
  refine ⟨a, ha, b x, hbB, ?_⟩
  have hmove : C.xB (C.mvB a B) = o x := by
    funext σ
    have hσ := congrFun hau σ
    have hstep : FD.mat (C.xB (C.mvB a B)) σ
        = (compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T a)).map conj * FD.mat (C.xB B) σ := by
      ext i j
      simp [GlobalTheory.Ker.Ctx.xB, GlobalTheory.Ker.Ctx.mvB, FD.mat, Matrix.mul_apply, map_sum]
    rw [hσ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet σ)),
      Matrix.mul_one] at hstep
    exact hstep
  rw [hmove]
  exact hxeq

end GlobalTheory.FrameDecomp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColIntertwiner
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.CompactHowe

noncomputable section

namespace GlobalTheory.GridJoin.ColIt

open GlobalTheory.CompactIntertwiner in

theorem exists_isIntw {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {σ Xs : Type} [Finite σ]
    (θ : InfFam D) (M : DSModel V S) (M' : DSModel W S')
    (I : MvPolynomial σ ℂ →ₗ[ℂ] (⨂[ℂ] τ, M'.H τ) →ₗ[ℂ] ⨂[ℂ] τ, M.H τ)
    (ρ : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ → MvPolynomial σ ℂ → MvPolynomial σ ℂ)
    (ρ' : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ → MvPolynomial σ ℂ → MvPolynomial σ ℂ)
    (hθ : IsInfFam θ) (hM : ∀ τ, FiniteDimensional ℂ (M.H τ) ∧ M.sm τ = ⊤)
    (hM' : ∀ τ, FiniteDimensional ℂ (M'.H τ) ∧ M'.sm τ = ⊤) (hI : I ≠ 0)
    (hd : ∀ τ g φ, (ρ τ g φ).totalDegree ≤ φ.totalDegree) (hd' : ∀ τ h φ, (ρ' τ h φ).totalDegree ≤ φ.totalDegree)
    (hρ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ x, I (ρ τ g φ) x = actT M τ g (I φ x))
    (hρ' : ∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ x, I (ρ' τ h φ) (actT M' τ h x) = I φ x) :
    ∃ It : MvPolynomial σ ℂ →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ (ω : GA D V × GA D W →* Module.End ℂ (Xs → ℂ))
      (pt : MvPolynomial σ ℂ →ₗ[ℂ] (Xs → ℂ)), Function.Injective pt →
      (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ φ, ω (atTau θ V τ g, 1) (pt φ) = pt (ρ τ g φ)) →
      (∀ τ, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ), ∀ φ, ω (1, atTau θ W τ h) (pt φ) = pt (ρ' τ h φ)) →
      GlobalTheory.Grid.IsIntw θ M M' ω pt It := by
  have fM := finite_tensor M fun τ => (hM τ).1
  have fM' := finite_tensor M' fun τ => (hM' τ).1
  let e := LinearEquiv.ofBijective (inclT M) (inclT_bij M fun τ => (hM τ).2)
  let e' := LinearEquiv.ofBijective (inclT M') (inclT_bij M' fun τ => (hM' τ).2)
  have he : ∀ x, inclT M (e.symm x) = x := fun x => e.apply_symm_apply x
  have he' : ∀ x, inclT M' (e'.symm x) = x := fun x => e'.apply_symm_apply x
  let It : MvPolynomial σ ℂ →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M := (I.compl₂ (inclT M')).compr₂ e.symm.toLinearMap
  have hIt : ∀ φ v, inclT M (It φ v) = I φ (inclT M' v) := fun φ v => he _
  have hinj : Function.Injective (inclT M) := e.injective
  refine ⟨It, fun ω pt hpt hω hω' => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro h0
    refine hI (LinearMap.ext fun φ => LinearMap.ext fun x => ?_)
    have := hIt φ (e'.symm x)
    rw [he', h0] at this
    simpa using this.symm
  · intro φ w
    haveI := fun τ => (hM' τ).1
    let m : MultilinearMap ℂ (fun τ => M'.H τ) ℂ :=
      (ellT M w ∘ₗ I φ).compMultilinearMap (PiTensorProduct.tprod ℂ)
    obtain ⟨c, -, hc⟩ := m.exists_bound_of_continuous (continuous_tprod M' this (ellT M w ∘ₗ I φ))
    refine ⟨c, fun v => ?_⟩
    rw [hIt]
    have := hc fun τ => (v τ : M'.H τ)
    simpa [m, inclT] using this
  · intro τ g hg φ φ' h v
    rw [hω τ g hg] at h
    rw [hpt h, hIt, hIt, hρ τ g hg]
  · intro τ X hX φ φ' h v w
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (isUnit_gram M τ) hX t
    simp only [oneP, hω τ _ (hm _)] at h
    have := hasDerivAt_pol pt hpt (fun t : ℝ => ρ τ (NormedSpace.exp (t • X)) φ) _ (fun t => hd τ _ φ) φ' h
      (ellT M w ∘ₗ I.flip (inclT M' v))
    simp only [hIt, ← hρ τ _ (hm _)]
    exact this
  · intro τ g hg φ φ' v v' h h'
    rw [hω' τ g hg] at h
    apply hinj
    rw [hpt h, hIt, hIt, h', hρ' τ g hg]
  · intro τ X hX φ φ' v v' h h'
    have hm : ∀ t : ℝ, NormedSpace.exp (t • X) ∈ Formalism.QuantumDeterminants.UH (gramAt D W τ) :=
      fun t => GlobalTheory.GardingVec.exp_mem (isUnit_gram M' τ) hX t
    simp only [oneP, hω' τ _ (hm _)] at h
    have h1 : ∀ ψ, ρ' τ 1 ψ = ψ := fun ψ => hpt (by
      rw [← hω' τ 1 (one_mem_UH _), GlobalTheory.PointAtPlaceHom.atTau_one hθ]
      exact congrArg (fun f : Module.End ℂ (Xs → ℂ) => f (pt ψ)) (map_one ω))
    apply hinj
    rw [map_add, hIt, hIt, map_zero]
    refine ellT_sep M (fun τ => (hM τ).1) _ fun w => ?_
    have hB := hasDerivAt_bilin (I.compr₂ (ellT M w)) (fun t : ℝ => ρ' τ (NormedSpace.exp (t • X)) φ) φ'
      (fun t : ℝ => actT M' τ (NormedSpace.exp (t • X)) (inclT M' v)) (inclT M' v')
      (hasDerivAt_pol pt hpt _ _ (fun t => hd' τ _ φ) φ' h)
      (hasDerivAt_dual_of_sep (ellT M') (ellT_sep M' fun τ => (hM' τ).1) _ _ h')
    simp only [LinearMap.compr₂_apply, hρ' τ _ (hm _), zero_smul, NormedSpace.exp_zero, h1] at hB
    have h2 := hρ' τ 1 (one_mem_UH _) φ' (inclT M' v)
    rw [h1] at h2
    rw [h2] at hB
    rw [map_add]
    exact hB.unique (hasDerivAt_const _ _)

open GlobalTheory.CompactHowe.LastStep in

theorem om_ptOf_exp {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    (hθ : IsInfFam θ) (hV : V.SigOK) (hW : W.SigOK)
    (M : DSModel V S) (M' : DSModel W S') (hε : ∀ τ, M.ε τ = allPos V.rank) (hε' : ∀ τ, M'.ε τ = allPos W.rank)
    (a b : D.what₂.Tau → ℚ) (x₁ x₃ : D.what₂.Tau → ℤ) (h1 : ∀ τ, (x₁ τ : ℚ) = a τ + (V.rank : ℚ) / 2)
    (h3 : ∀ τ, (x₃ τ : ℚ) = -((W.rank : ℚ) / 2 + b τ))
    {χS χT : (AE D)ˣ →* Circle} {ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hω : IsWeilDatumO ψ V W χS χT ω) (ha : ∀ τ, HasInfExp D χS τ (a τ)) (hb : ∀ τ, HasInfExp D χT τ (b τ))
    {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ V W) θ τ (cplxO (cart M τ) (cart M' τ)) f)
    {g : GA D V} (hg : g ∈ GinfC V) {h : GA D W} (hh : h ∈ GinfC W) (φ : PolF D W.rank V.rank) :
    ω (g, h) (GlobalTheory.Chain.ptOf ψ θ M M' f φ) = GlobalTheory.Chain.ptOf ψ θ M M' f
      (polAct M M' x₁ x₃ (fun τ => compAt θ τ (Formalism.L2.Theta.mt V g)) (fun τ => compAt θ τ (Formalism.L2.Theta.mt W h)) φ) := by
  unfold GlobalTheory.Chain.ptOf
  rw [cart_eq_one M hε, cart_eq_one M' hε'] at hv ⊢
  have e1 := GlobalTheory.T.vacuum_character_positive_definite_source D ψ θ V W χS χT ω hω hθ hV hW (fun _ => 1) (isCartan_one M hε) (isCartan_one M' hε')
    _ _ ha hb x₁ (fun τ => x₁ τ - V.rank) x₃ h1
    (fun τ => by push_cast; rw [h1]; ring)
    (fun τ => by
      have := congrArg (fun q : ℚ => (q : ℂ)) (h3 τ)
      simp only [Matrix.trace_one, Fintype.card_fin]
      push_cast at this
      exact this)
    f hf hv g hg h hh (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
  have e2 := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χS χT ω hω hθ (fun _ => 1) (fun _ => 1) (onb M)
    (fun τ => onb M τ * inFr M τ (compAt θ τ (Formalism.L2.Theta.mt V g))) (fun _ => 1) (fun _ => 1) (onb M')
    (fun τ => onb M' τ * inFr M' τ (compAt θ τ (Formalism.L2.Theta.mt W h))) g h
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one]) (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by
      rw [onb, inFr, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (fr_det M τ)])
    (fun τ => by
      rw [onb, inFr, Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ (fr_det M' τ)]) f hf φ).2
  rw [e2, e1, GlobalTheory.FiniteFock.pureTensorO_smul, GlobalTheory.T.fockPolynomialVector_basisChange_eq_substitution D ψ θ V W hω.std hθ _ _ _ _ f hf, polAct, map_smul]
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have a1 : (1 / 2 : ℂ) • ((1 : Matrix (Fin W.rank) (Fin W.rank) ℂ) + 1) = 1 := by module
  rw [det_inFr, det_inFr, a1, sub_self, smul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, Matrix.det_one,
    _root_.one_zpow, mul_one]

theorem hasInfExp_mu {D : D7} {T0 : Type} (L : LevCh D T0) {μ0 : T0} (hL : L.Is μ0) (t : T0) (k : Fin D.R.m)
    (τ : D.what₂.Tau) : HasInfExp D (L.mu t ((k : ℕ) + 1)) τ (-(D.hc τ).e k) := by
  have h1 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 k) (GlobalTheory.InnerSteps.hasInfQ_tauE (L.C.isMu0 k).inf) τ
  simp only [Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at h1
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  haveI : IsTotallyComplex D.host.E := by infer_instance
  have h3 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ (fun _ => 0) (hL.xi t)
    ⟨fun _ => 0, fun _ => by norm_num, fun x => by
      rw [GlobalTheory.TypeValues.inf_eq_one _ hn ho x]; simp⟩ τ
  exact GlobalTheory.InnerSteps.hasInfExp_mul_zero h1 h3

theorem isVacVec_of_isVac {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : GlobalTheory.Grid.Node D}
    {f : WO S.V T.V → ℂ} (hf : GlobalTheory.Grid.IsVac ψ θ false S T f) : GlobalTheory.Chain.IsVacVec ψ θ S.M T.M f := by
  refine ⟨hf.2.theta, ?_, hf.2.fock⟩
  rintro rfl
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have := hn p hp
  simp [Formalism.IndefR.Datum.nrm2] at this

open GlobalTheory.CompactHowe.LastStep in

theorem exists_col_intertwiner : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : GlobalTheory.ChiGrid.Consts}, GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → HostHyp D → ∀ {F : Face D A}, GlobalTheory.Hk3.Core R F → sc.cGap = 1 → ∀ {G' : GlobalTheory.ChiGrid.GridData R.toLevCh sc} (W : G'.Weil), W.Over R → ∀ G : GlobalTheory.Grid.GridPre R, G.IsSpaces → G.IsChars → SpAgree G W → (∀ i, i < D.R.m → ∀ κ : G'.CosAt i, IsThetaAt W.ψ (symplO _ _) (heisO W.ψ _ _) G.idem (latO (G'.pS (.chi i 0)) (G'.pT (.chi i 0)) (G'.latS (.chi i 0) : Set _) (G'.latT (.chi i 0) : Set _) fun _ => True) 1 (W.vac i) (cosInd G.idem κ) (W.cosVec i κ)) → ∀ j, j < D.R.m → ∀ (ω : T → GlobalTheory.Grid.WRep (G.Xp j).V (G.nX j).V) (f : WO (G.Xp j).V (G.nX j).V → ℂ), (∀ t, GlobalTheory.Grid.IsWeil R.ψ false (G.Xp j).V (G.nX j).V (R.toLevCh.mu t (j + 1)) (R.toLevCh.mu t (j + 1)) (ω t)) → GlobalTheory.Grid.IsVac R.ψ R.θ false (G.Xp j) (G.nX j) f → ∃ It : GlobalTheory.Grid.Pol (G.Xp j) (G.nX j) →ₗ[ℂ] SmT (G.Xp j).M →ₗ[ℂ] SmT (G.nX j).M, ∀ t, GlobalTheory.Grid.IsIntw R.θ (G.nX j).M (G.Xp j).M (ω t).swap (GlobalTheory.Grid.fock R.ψ R.θ false (G.Xp j) (G.nX j) f) It := by
  intro D Γ _ _ Pl0 T A Ks _ _ _ R sc _hDS _hHC _hHost F hC _hgap G' W _hW G hsp _hch _hag _hcos j hj ω f hω hf
  classical
  have hθ : IsInfFam R.θ := hC.models.inf

  have hS : (G.Xp j).V.SigOK ∧ (G.Xp j).S = parXp D j := by
    cases j with
    | zero => exact ⟨(hsp.P _ le_rfl).sigOK, (hsp.P _ le_rfl).par.trans (parP_m D)⟩
    | succ k => exact ⟨(hsp.X k (by omega)).sigOK, (hsp.X k (by omega)).par⟩
  have hT : (G.nX j).V.SigOK ∧ (G.nX j).S = parXp D (j + 1) :=
    ⟨(hsp.X j (by omega)).sigOK, (hsp.X j (by omega)).par⟩
  have en : ∀ τ, IsEnum (parXp D j τ) ((G.Xp j).M.lam τ) ((G.Xp j).M.ε τ) := fun τ => hS.2 ▸ (G.Xp j).M.enum τ
  have en' : ∀ τ, IsEnum (parXp D (j + 1) τ) ((G.nX j).M.lam τ) ((G.nX j).M.ε τ) := fun τ => hT.2 ▸ (G.nX j).M.enum τ
  have hp := fun τ => GlobalTheory.T.gridRowRealParameter_succ_allPlus_lowestWeights D j hj τ (G.Xp j).V.rank (G.nX j).V.rank _ _ _ _ (en τ) (en' τ)
  have hε := fun τ => (hp τ).1
  have hε' := fun τ => (hp τ).2.1
  choose x₁ x₃ h1 h3 hn ν n1 n2 n3 n4 using fun τ => (hp τ).2.2
  have m := fun τ => GlobalTheory.T.allPositive_model_finiteDimensional_compactType D (G.Xp j).V _ (G.Xp j).M τ (hε τ)
  have m' := fun τ => GlobalTheory.T.allPositive_model_finiteDimensional_compactType D (G.nX j).V _ (G.nX j).M τ (hε' τ)
  have hl := fun τ =>
    haveI := (m τ).1
    haveI := (m' τ).1
    GlobalTheory.T.exists_howeDuality_intertwiner_unitaryPair_local (G.nX j).V.rank (G.Xp j).V.rank (hn τ) (ν τ) (x₁ τ) (x₃ τ) _ _ ((G.Xp j).M.H τ) ((G.Xp j).M.σ τ) ((G.nX j).M.H τ) ((G.nX j).M.σ τ)
      (n1 τ) (n2 τ) (n3 τ) (n4 τ) (m τ).2.2.1 (m τ).2.2.2 (m' τ).2.2.1 (m' τ).2.2.2
  choose I I0 hI using hl
  obtain ⟨J, J0, hJ⟩ := GlobalTheory.T.exists_equivariant_piTensor_polynomialBilinear D.what₂.Tau (G.nX j).V.rank (G.Xp j).V.rank (G.Xp j).M.H (G.nX j).M.H I I0
  have key : ∀ (g : D.what₂.Tau → Matrix (Fin (G.Xp j).V.rank) (Fin (G.Xp j).V.rank) ℂ)
      (h : D.what₂.Tau → Matrix (Fin (G.nX j).V.rank) (Fin (G.nX j).V.rank) ℂ),
      (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.Xp j).V τ)) → (∀ τ, h τ ∈ Formalism.QuantumDeterminants.UH (gramAt D (G.nX j).V τ)) → ∀ φ x,
      J (polAct (G.Xp j).M (G.nX j).M x₁ x₃ g h φ) (PiTensorProduct.map (fun τ => ((G.Xp j).M.σ τ (inFr (G.Xp j).M τ (g τ)) : (G.Xp j).M.H τ →ₗ[ℂ] (G.Xp j).M.H τ)) x) =
        PiTensorProduct.map (fun τ => ((G.nX j).M.σ τ (inFr (G.nX j).M τ (h τ)) : (G.nX j).M.H τ →ₗ[ℂ] (G.nX j).M.H τ)) (J φ x) := fun g h hg hh =>
    hJ _ _ _ _ _ fun τ P v => hI τ _ (hε' τ ▸ inFr_mem (G.nX j).M τ (hh τ)) _ (hε τ ▸ inFr_mem (G.Xp j).M τ (hg τ)) P v
  obtain ⟨It, hIt⟩ := exists_isIntw (Xs := WO (G.Xp j).V (G.nX j).V) R.θ (G.nX j).M (G.Xp j).M J
    (fun τ g => polAct (G.Xp j).M (G.nX j).M x₁ x₃ (fun _ => 1) (Function.update (fun _ => 1) τ g))
    (fun τ h => polAct (G.Xp j).M (G.nX j).M x₁ x₃ (Function.update (fun _ => 1) τ h) fun _ => 1) hθ
    (fun τ => ⟨(m' τ).1, (m' τ).2.1⟩) (fun τ => ⟨(m τ).1, (m τ).2.1⟩) J0
    (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _) (fun _ _ _ => totalDegree_polAct _ _ _ _ _ _ _)
    (fun τ g hg φ x => by
      have := key (fun _ => 1) _ (fun _ => GlobalTheory.PointAtPlaceHom.one_mem_UH _) (update_mem τ hg) φ x
      rwa [map_update, GlobalTheory.CompactHowe.LastStep.map_one'] at this)
    (fun τ h hh φ x => by
      have := key _ (fun _ => 1) (update_mem τ hh) (fun _ => GlobalTheory.PointAtPlaceHom.one_mem_UH _) φ x
      rwa [map_update, GlobalTheory.CompactHowe.LastStep.map_one'] at this)
  have hvv := isVacVec_of_isVac hf
  have hstd : IsStdChar D R.ψ (-1) := hf.1
  have hinj := GlobalTheory.T.fockVectorsOfThetaDatum_injective D (G.Xp j).V (G.nX j).V _ _ R.ψ R.θ (G.Xp j).M (G.nX j).M f hstd hθ hvv
  have hmu := fun t τ => hasInfExp_mu R.toLevCh hC.lev t ⟨j, hj⟩ τ
  refine ⟨It, fun t => hIt ((ω t).swap) (GlobalTheory.Grid.fock R.ψ R.θ false (G.Xp j) (G.nX j) f) hinj (fun τ g hg φ => ?_) fun τ h hh φ => ?_⟩
  · rw [WRep.swap_apply]
    have := om_ptOf_exp hθ hS.1 hT.1 (G.Xp j).M (G.nX j).M hε hε' _ _ x₁ x₃ h1 h3 (hω t) (hmu t) (hmu t) hvv.theta hvv.vac
      (one_mem _) (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := R.θ) (G.nX j).V τ g) φ
    rwa [compAt_atTau hθ τ hg, compAt_one] at this
  · rw [WRep.swap_apply]
    have := om_ptOf_exp hθ hS.1 hT.1 (G.Xp j).M (G.nX j).M hε hε' _ _ x₁ x₃ h1 h3 (hω t) (hmu t) (hmu t) hvv.theta hvv.vac
      (GlobalTheory.PointAtPlaceHom.atTau_mem (θ := R.θ) (G.Xp j).V τ h) (one_mem _) φ
    rwa [compAt_atTau hθ τ hh, compAt_one] at this

end GlobalTheory.GridJoin.ColIt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDiagonalConjEdgeSumAddCharFiniteField
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SeeConjRead

noncomputable section

namespace GlobalTheory.SeeConjScale

open Classical in

noncomputable def forestLift {G : Type} [Group G] {r : ℕ} (Ed : Fin r → Fin r → Prop) (hlt : ∀ i j, Ed i j → i < j)
    (w : Fin r → Fin r → G) (j : Fin r) : G :=
  if h : ∃ i, Ed i j then forestLift Ed hlt w (Classical.choose h) * w (Classical.choose h) j else 1
termination_by j.val
decreasing_by all_goals (try simp_wf); exact hlt _ _ (Classical.choose_spec h)

theorem forestLift_edge {G : Type} [Group G] {r : ℕ} (Ed : Fin r → Fin r → Prop) (hlt : ∀ i j, Ed i j → i < j)
    (huniq : ∀ i i' j, Ed i j → Ed i' j → i = i') (w : Fin r → Fin r → G) {i j : Fin r} (h : Ed i j) :
    (forestLift Ed hlt w i)⁻¹ * forestLift Ed hlt w j = w i j := by
  have hex : ∃ i, Ed i j := ⟨i, h⟩
  have hc : Classical.choose hex = i := huniq _ _ _ (Classical.choose_spec hex) h
  have e : forestLift Ed hlt w j = forestLift Ed hlt w i * w i j := by
    rw [forestLift, dif_pos hex, hc]
  rw [e, inv_mul_cancel_left]

theorem symEdge_lt {r : ℕ} (ρ k : ℕ) : ∀ i j : Fin r, symEdge ρ k i j → i < j := by
  intro i j h
  show i.val < j.val
  unfold symEdge at h
  omega

theorem symEdge_uniq {r : ℕ} (ρ k : ℕ) : ∀ i i' j : Fin r, symEdge ρ k i j → symEdge ρ k i' j → i = i' := by
  intro i i' j h h'
  apply Fin.ext
  unfold symEdge at h h'
  omega

theorem scale_conj : ∀ {κf : Type} [CommRing κf] [Finite κf], IsField κf → ∀ {r : ℕ} (ρ k : ℕ) (ψ' ψ0 : AddChar κf ℂ), ψ' ≠ 1 → ψ0 ≠ 1 → ∀ a : Fin r → Fin r → κfˣ, ∃ d : Fin r → κfˣ, ∀ u : GL (Fin r) κf, u ∈ unipSym κf r ρ k → ψ' (∑ i, ∑ j, if symEdge ρ k i j then (a i j : κf) * u.val i j else 0) = ψ0 (edgeSum (symEdge ρ k) ((diagGL d)⁻¹ * u * diagGL d)) := by
  intro κf _ _ hF r ρ k ψ' ψ0 h1 h0 a
  let _ : Field κf := hF.toField
  have := Fintype.ofFinite κf
  have hprim : ψ0.IsPrimitive := AddChar.IsPrimitive.of_ne_one h0
  have hinj : Function.Injective ψ0.mulShift := AddChar.to_mulShift_inj_of_isPrimitive hprim
  have hbij : Function.Bijective ψ0.mulShift := by
    classical
    rw [Fintype.bijective_iff_injective_and_card]
    exact ⟨hinj, (AddChar.card_eq).symm⟩
  obtain ⟨c, hc⟩ := hbij.2 ψ'
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply h1
    rw [← hc]
    exact AddChar.mulShift_zero ψ0
  let w : Fin r → Fin r → κfˣ := fun i j => Units.mk0 c hc0 * a i j
  refine ⟨forestLift (symEdge ρ k) (symEdge_lt ρ k) w, fun u _ => ?_⟩
  rw [← hc, AddChar.mulShift_apply]
  congr 1
  unfold edgeSum
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rw [diagGL_conj_apply]
    have e := congrArg Units.val (forestLift_edge (symEdge ρ k) (symEdge_lt ρ k) (symEdge_uniq ρ k) w h)
    rw [Units.val_mul] at e
    have e2 : (((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) *
        ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf) = c * (a i j : κf) := by
      rw [e]; rfl
    symm
    calc (((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) * u.val i j *
          ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf)
        = ((((forestLift (symEdge ρ k) (symEdge_lt ρ k) w i)⁻¹ : κfˣ) : κf) *
          ((forestLift (symEdge ρ k) (symEdge_lt ρ k) w j : κfˣ) : κf)) * u.val i j := by ring
      _ = c * ((a i j : κf) * u.val i j) := by rw [e2]; ring
  · rw [mul_zero]

end GlobalTheory.SeeConjScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivHeckeKernelSchemePointsHeckeKernels
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.HeckeEx

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {P : Ideal (𝓞 E)} {p i : ℕ}

theorem exists_carried (Z : KerScheme Xo P p i) {k : Type} [Field k] [IsAlgClosed k] (w : Sp k ⟶ Z.Hk)
    (y : Sp k ⟶ Xo.X) (hw : w ≫ Z.π₁ = y) :
    ∃ C : Subgroup (Over.mk y ⟶ Xo.univ.t.G), Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C ∧
      ∀ C', Z.Carries w y C' ↔ C' = C := by
  subst hw
  obtain ⟨C₀, hC₀, hk⟩ := Z.hecke k w
  obtain ⟨ρ, e₀⟩ := GlobalTheory.HkSetPull.exists_equiv Z.m₁.cart (Over.mk w)
  have hh : ∀ (u : Over.mk w ⟶ Z.o₁.t.G) (v : Over.mk (w ≫ Z.π₁) ⟶ Xo.univ.t.G),
      v.left = u.left ≫ Z.m₁.toSABMap.φ → (u ∈ C₀ ↔ v ∈ Subgroup.comap ρ.symm.toMonoidHom C₀) := fun u v e => by
    rw [show v = ρ u from Over.OverMorphism.ext (e.trans (e₀ u).symm)]
    show _ ↔ ρ.symm (ρ u) ∈ C₀
    rw [ρ.symm_apply_apply]
  refine ⟨Subgroup.comap ρ.symm.toMonoidHom C₀,
    (GlobalTheory.HkSetPull.heckeKer_iff Dw P p i Z.m₁.toSABMap (Over.mk w) C₀ _ hh).1 hk, fun C' => ⟨fun h => ?_, ?_⟩⟩
  · ext v
    obtain ⟨u, rfl⟩ := ρ.surjective v
    exact (h.2 u _ (e₀ u)).symm.trans ((hC₀ u).symm.trans (hh u _ (e₀ u)))
  · rintro rfl
    exact ⟨rfl, fun u v e => (hC₀ u).symm.trans (hh u v e)⟩

theorem exists_equiv_carries : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (P : Ideal (𝓞 E)) (p i : ℕ) (Z : KerScheme Xo P p i), admitted l P p → ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Xo.X), ∃ e : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} ≃ {C : Subgroup (Over.mk y ⟶ Xo.univ.t.G) // Xo.univ.t.HeckeKer (Over.mk y) Dw P p i C}, ∀ w C, Z.Carries w.1 y C ↔ C = (e w).1 := by
  intro E _ _ _ H Dw l Xo P p i Z hA k _ _ y
  choose c hc hcc using fun w : {w : Sp k ⟶ Z.Hk // w ≫ Z.π₁ = y} => exists_carried Z w.1 y w.2
  refine ⟨Equiv.ofBijective (fun w => ⟨c w, hc w⟩) ⟨fun w w' e => ?_, fun C => ?_⟩, hcc⟩
  · exact Subtype.ext (((GlobalTheory.kerScheme_points E H Dw l Xo P p i Z hA).1 k y (c w) (hc w)).unique
      ((hcc w _).2 rfl) ((hcc w' _).2 (congrArg Subtype.val e)))
  · obtain ⟨z, hz, -⟩ := (GlobalTheory.kerScheme_points E H Dw l Xo P p i Z hA).1 k y C.1 C.2
    exact ⟨⟨z, hz.1⟩, Subtype.ext ((hcc ⟨z, hz.1⟩ _).1 hz).symm⟩

end GlobalTheory.HeckeEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSelfDualFrameOfStandardSelfDualLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory
namespace SDFrameCompletion

theorem exists_isSDFrame_of_isSelfDualC : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (Λ : Set (Fin V.rank → D.host.E)) = L0c D V → IsSelfDualC V Λ → ∃ β, IsSDFrame V β Λ 1 := by
  intro D V Λ hΛ hsd
  exact GlobalTheory.AdelicFrame.exists_isSDFrame D V Λ hΛ (GlobalTheory.AdIsom.dualL_eq hsd)

end SDFrameCompletion
end GlobalTheory
end

