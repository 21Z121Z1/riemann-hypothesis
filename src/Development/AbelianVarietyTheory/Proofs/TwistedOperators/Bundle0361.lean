import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasDerivAtZeroAndIsTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0232
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0332
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0188
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0343
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorLinearInFactorAndHeisenbergDerivReal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder

namespace GlobalTheory.PureLinear

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem finite_of_eq_off {ι : Type} {a b : ι → ℂ} (q : ι) (ha : (Function.mulSupport a).Finite)
    (h : ∀ p, p ≠ q → b p = a p) : (Function.mulSupport b).Finite := by
  refine (ha.union (Set.finite_singleton q)).subset fun p hp => ?_
  by_cases hpq : p = q
  · exact Or.inr hpq
  · left
    rw [Function.mem_mulSupport] at hp ⊢
    rwa [h p hpq] at hp

theorem exists_cofactor {ι : Type} {a : ι → ℂ} (q : ι) (ha : (Function.mulSupport a).Finite) :
    ∃ C : ℂ, ∀ b : ι → ℂ, (∀ p, p ≠ q → b p = a p) → ∏ᶠ p, b p = b q * C := by
  refine ⟨∏ᶠ (p) (_ : p ≠ q), a p, fun b hb => ?_⟩
  rw [← mul_finprod_cond_ne q (finite_of_eq_off q ha hb)]
  congr 1
  exact finprod_congr fun p => finprod_congr fun hp => hb p hp

private theorem lineAt_fin_eq_zero_and_inf_other_eq_zero {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau)
    (z : Matrix (Fin m) (Fin n) ℂ) (t : ℝ) (i : Fin m) (j : Fin n) :
    finPart D (lineAt θ τ z t i j) = 0 ∧ ∀ ρ, ρ ≠ τ → θ ρ (infPart D (lineAt θ τ z t i j)) = 0 := by
  obtain ⟨-, hfin, hcomp⟩ := GlobalTheory.WeilVacMove.isLineAt_lineAt hθ τ z
  refine ⟨by simpa using congrFun (congrFun (hfin t) i) j, fun ρ hρ => ?_⟩
  have h := congrFun (congrFun (hcomp t ρ) i) j
  simp only [hρ, if_false] at h
  simpa [compAt] using h

private theorem ae_eq_zero_of_fin_zero_of_theta_inf_zero {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (a : AE D) (h1 : finPart D a = 0)
    (h2 : ∀ ρ, θ ρ (infPart D a) = 0) : a = 0 := by
  obtain ⟨σ, hσ⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  exact hσ.ext a h1 h2

variable {D : D7}

theorem wAt_lineAt_self {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) : wAt (.inr τ) (lineAt θ τ z t) = lineAt θ τ z t := by
  funext i j
  obtain ⟨hf, hr⟩ := lineAt_fin_eq_zero_and_inf_other_eq_zero hθ τ z t i j
  have hid := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  simp only [wAt]
  rw [← sub_eq_zero]
  apply ae_eq_zero_of_fin_zero_of_theta_inf_zero hθ
  · simp [map_sub, map_mul, hf]
  · intro ρ
    rw [map_sub, map_sub, map_mul, map_mul]
    by_cases hρ : ρ = τ
    · subst hρ
      rw [(hid.2.2.2.2.2.2 θ hθ ρ).1, one_mul, sub_self]
    · rw [hr ρ hρ, mul_zero, sub_zero]

theorem wAt_lineAt_ne {θ : InfFam D} (hθ : IsInfFam θ) {m n : ℕ} (τ : D.what₂.Tau) (z : Matrix (Fin m) (Fin n) ℂ)
    (t : ℝ) {p : Place D} (hp : p ≠ .inr τ) : wAt p (lineAt θ τ z t) = 0 := by
  funext i j
  obtain ⟨hf, hr⟩ := lineAt_fin_eq_zero_and_inf_other_eq_zero hθ τ z t i j
  have hid := GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D
  simp only [wAt, Matrix.zero_apply, Pi.zero_apply]
  apply ae_eq_zero_of_fin_zero_of_theta_inf_zero hθ
  · simp [map_mul, hf]
  · intro ρ
    rw [map_mul, map_mul]
    rcases p with v | τ'
    · rw [(hid.2.2.2.1 v).1, map_zero, zero_mul]
    · have hτ' : τ' ≠ τ := fun h => hp (by rw [h])
      by_cases hρ : ρ = τ'
      · subst hρ
        rw [hr ρ hτ', mul_zero]
      · rw [(hid.2.2.2.2.2.2 θ hθ ρ).2 τ' (Ne.symm hρ), zero_mul]

theorem finite_ne_of_eq_off {ι X : Type} {x y : ι → X} {f₀ : X} (q : ι) (hx : {p | x p ≠ f₀}.Finite)
    (h : ∀ p, p ≠ q → y p = x p) : {p | y p ≠ f₀}.Finite := by
  refine (hx.union (Set.finite_singleton q)).subset fun p hp => ?_
  by_cases hpq : p = q
  · exact Or.inr hpq
  · left
    simp only [Set.mem_setOf_eq] at hp ⊢
    rwa [h p hpq] at hp

theorem isPure_linear_and_dRho : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → (∀ (x y z : Place D → WO S T → ℂ) (f g : WO S T → ℂ) (q : Place D) (c : ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ y g → (∀ p, p ≠ q → y p = x p) → (∀ p, p ≠ q → z p = x p) → z q = c • x q + y q → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ z (c • f + g)) ∧ ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → (∀ p, p ≠ .inr τ → x' p = x p) → x' (.inr τ) = Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (x (.inr τ)) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f) := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ
  have hψ := base_std hB
  have hθ := base_inf hB
  have hf₀ := base_theta hB
  have hthH : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  refine ⟨fun x y z f g q c hx hy hyx hzx hzq => ?_, fun x x' f τ z hx hx' hxτ => ?_⟩
  · unfold IsPure IsRestricted at hx hy ⊢
    obtain ⟨⟨hxl, hxfin⟩, hfθ, hxw⟩ := hx
    obtain ⟨⟨hyl, -⟩, hgθ, hyw⟩ := hy
    have hzl : ∀ p, IsLocal ψ θ S T sS sT ΛS ΛT p (z p) := by
      intro p
      by_cases hp : p = q
      · rw [hp, hzq]
        exact ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x q) (hxl q).1).2 q (hxl q)).2.1 c (y q) (hyl q)
      · rw [hzx p hp]
        exact hxl p
    refine ⟨⟨hzl, finite_ne_of_eq_off q hxfin hzx⟩,
      GlobalTheory.WeilVacMove.isTheta_add (GlobalTheory.WeilVacMove.isTheta_smul c hfθ) hgθ, fun w => ?_⟩
    obtain ⟨hxs, hxe⟩ := hxw w
    obtain ⟨-, hye⟩ := hyw w
    obtain ⟨C, hC⟩ := exists_cofactor q hxs
    have ha := hC (fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) (fun _ _ => rfl)
    have hb := hC (fun p => ipO μ 𝓕 (y p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hyx p hp])
    have hd := hC (fun p => ipO μ 𝓕 (z p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hzx p hp])
    beta_reduce at ha hb hd
    refine ⟨finite_of_eq_off q hxs (fun p hp => by simp only [hzx p hp]), ?_⟩
    have hG := hthH w f₀ hf₀
    have hGq := hthH (wAt q w) f₀ hf₀
    have e1 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (c • f) (heisO ψ S T w f₀) (GlobalTheory.WeilVacMove.isTheta_smul c hfθ) hG
    have e2 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ f (heisO ψ S T w f₀) hfθ hG
    have e3 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (c • x q) (heisO ψ S T (wAt q w) f₀)
      (GlobalTheory.WeilVacMove.isTheta_smul c (hxl q).1) hGq
    have e4 := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 hψ hμ (x q) (heisO ψ S T (wAt q w) f₀) (hxl q).1 hGq
    rw [hd, hzq, (e3.2.2.2.1 (y q) (hyl q).1).1, (e4.2.2.1 c).1, (e1.2.2.2.1 g hgθ).1, (e2.2.2.1 c).1,
      hxe, hye, ha, hb]
    ring
  · have hx1 := hx
    unfold IsPure IsRestricted at hx1 ⊢
    obtain ⟨⟨hxl, hxfin⟩, hfθ, hxw⟩ := hx1
    have hx'l : ∀ p, IsLocal ψ θ S T sS sT ΛS ΛT p (x' p) := by
      intro p
      by_cases hp : p = .inr τ
      · rw [hp, hxτ]
        exact ((GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ hθ (x (.inr τ)) (hxl _).1).2 (.inr τ) (hxl _)).2.2 τ rfl z
      · rw [hx' p hp]
        exact hxl p
    refine ⟨⟨hx'l, finite_ne_of_eq_off (.inr τ) hxfin hx'⟩,
      GlobalTheory.WeilVacMove.isTheta_dRho hψ hθ τ z hfθ, fun w => ?_⟩
    obtain ⟨hxs, -⟩ := hxw w
    obtain ⟨C, hC⟩ := exists_cofactor (.inr τ) hxs
    have key : ∀ t : ℝ, ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) (heisO ψ S T w f₀) =
        ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) (x (.inr τ))) (heisO ψ S T (wAt (.inr τ) w) f₀) * C := by
      intro t
      have hP := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hx (lineAt θ τ z t)
      unfold IsPure at hP
      have e := hC (fun p => ipO μ 𝓕 (heisO ψ S T (wAt p (lineAt θ τ z t)) (x p)) (heisO ψ S T (wAt p w) f₀))
        (fun p hp => by simp only [wAt_lineAt_ne hθ τ z t hp, GlobalTheory.WeilVacMove.heisO_zero])
      beta_reduce at e
      rw [(hP.2.2 w).2, e, wAt_lineAt_self hθ τ z t]
    have hG := hthH w f₀ hf₀
    have h1 := (GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ f (heisO ψ S T w f₀) hfθ hG τ z).1
    have h2 := ((GlobalTheory.T.hasDerivAt_heisenbergMatrixCoeff_realLine_skew D ψ θ S T μ 𝓕 hψ hθ hμ (x (.inr τ)) (heisO ψ S T (wAt (.inr τ) w) f₀)
      (hxl _).1 (hthH _ _ hf₀) τ z).1).mul_const C
    have h3 : HasDerivAt (fun t : ℝ => ipO μ 𝓕 (heisO ψ S T (lineAt θ τ z t) f) (heisO ψ S T w f₀))
        (ipO μ 𝓕 (Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z (x (.inr τ))) (heisO ψ S T (wAt (.inr τ) w) f₀) * C) 0 := by
      simpa only [key] using h2
    have hd := hC (fun p => ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)) (fun p hp => by simp only [hx' p hp])
    beta_reduce at hd
    refine ⟨finite_of_eq_off (.inr τ) hxs (fun p hp => by simp only [hx' p hp]), ?_⟩
    rw [hd, hxτ, h1.unique h3]

end GlobalTheory.PureLinear

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorOperatorEqOffPlaceMulAtPlace
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.OffOp

section General

variable {G A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group A] [TopologicalSpace A]
  [IsTopologicalGroup A]

def splitEquiv (ι : A →* G) (π : G →* A) (hπι : ∀ a, π (ι a) = a) (hc : ∀ a g, π g = 1 → Commute (ι a) g) :
    π.ker × A ≃* G where
  toFun p := p.1 * ι p.2
  invFun g := (⟨g * (ι (π g))⁻¹, by simp [MonoidHom.mem_ker, hπι]⟩, π g)
  left_inv p := by
    have h : π p.1 = 1 := p.1.2
    ext <;> simp [hπι, h]
  right_inv g := by simp
  map_mul' p q := by
    have := (hc p.2 q.1 q.1.2).eq
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, map_mul, mul_assoc]
    rw [← mul_assoc (q.1 : G), ← this, mul_assoc]

variable [T2Space A] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [LocallyCompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]

theorem exists_op (ι : A →* G) (π : G →* A) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ a, π (ι a) = a)
    (hc : ∀ a g, π g = 1 → Commute (ι a) g) (μ : Measure A) [μ.IsHaarMeasure] (ν : Measure G) [ν.IsHaarMeasure]
    {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (hσ : GlobalTheory.PRep.IsSmooth σ)
    {φ : G → ℂ} (hφ : φ ∈ GlobalTheory.SplitWeil.SB G) :
    ∃ H : W →ₗ[ℂ] W, (∀ g x, H (σ (ι g) x) = σ (ι g) (H x)) ∧
      (∀ x, ∀ k ∈ leftStabilizer φ, π k = 1 → σ k (H x) = H x) ∧
      ∀ f ∈ GlobalTheory.SplitWeil.SB A, ∀ B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ (σ.comp ι) f B →
        ∀ Ψ : G → ℂ, (∀ h a, π h = 1 → Ψ (h * ι a) = φ h * f a) → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ Ψ (H ∘ₗ B) := by
  classical
  have hφ' : IsLocallyConstant φ ∧ HasCompactSupport φ := hφ
  have hNc : IsClosed (π.ker : Set G) := by
    have hset : (π.ker : Set G) = π ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hNc.locallyCompactSpace
  let e : π.ker × A ≃ₜ* G :=
    { splitEquiv ι π hπι hc with
      continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (hι.comp continuous_snd)
      continuous_invFun := by
        refine Continuous.prodMk ?_ hπ
        exact (continuous_id.mul (hι.comp hπ).inv).subtype_mk _ }
  have he : ∀ p : π.ker × A, e p = (p.1 : G) * ι p.2 := fun p => rfl
  let μN : Measure π.ker := Measure.haar
  let P : Measure (π.ker × A) := μN.prod μ
  have hE : MeasurableEmbedding e := e.toHomeomorph.isClosedEmbedding.measurableEmbedding
  haveI : (P.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map P e
  obtain ⟨c, hν⟩ : ∃ c : NNReal, ν = c • P.map e := ⟨_, Measure.isMulLeftInvariant_eq_smul ν (P.map e)⟩
  let σN : Representation ℂ π.ker W := σ.comp π.ker.subtype
  have hσN : GlobalTheory.PRep.IsSmooth σN := fun x => (hσ x).preimage continuous_subtype_val
  let φN : π.ker → ℂ := fun h => φ h
  have hφN1 : IsLocallyConstant φN := hφ'.1.comp_continuous continuous_subtype_val
  have hφN2 : HasCompactSupport φN := hφ'.2.comp_isClosedEmbedding hNc.isClosedEmbedding_subtypeVal
  let T : W →ₗ[ℂ] W := smoothOp σN μN φN
  have hT : ∀ (l : Module.Dual ℂ W) (y : W), l (T y) = ∫ h, φN h * l (σN h y) ∂μN := by
    intro l y
    simpa [smul_eq_mul] using hσN.map_smoothOp (μ := μN) hφN1 hφN2 l y
  refine ⟨((c : ℝ) : ℂ) • T, ?_, ?_, ?_⟩
  · intro g x
    simp only [LinearMap.smul_apply, map_smul]
    congr 1
    refine (hσN.map_smoothOp_of_intertwining (μ := μN) hσN hφN1 hφN2 (σ (ι g)) (fun h y => ?_) x).symm
    show σ (ι g) (σ h y) = σ h (σ (ι g) y)
    rw [← Module.End.mul_apply, ← map_mul, (hc g h h.2).eq, map_mul, Module.End.mul_apply]
  · intro x k hk hk1
    have hmem := hσN.smoothOp_mem_fixed (μ := μN) hφN1 hφN2
      (K := (leftStabilizer φ).comap π.ker.subtype) (fun k' hk' g => hk' g) x
    have hfix := (mem_fixed.1 hmem) ⟨k, MonoidHom.mem_ker.2 hk1⟩ hk
    simp only [LinearMap.smul_apply, map_smul]
    congr 1
  · intro f hf B hB Ψ hΨ v l
    have hf' : IsLocallyConstant f ∧ HasCompactSupport f := hf
    let F : π.ker × A → ℂ := fun p => φN p.1 * f p.2 * l (σ (e p) v)
    have hFe : ∀ p, Ψ (e p) * l (σ (e p) v) = F p := by
      intro p
      show Ψ (e p) * l (σ (e p) v) = φ p.1 * f p.2 * l (σ (e p) v)
      rw [he p, hΨ _ _ p.1.2]
    have hFlc : IsLocallyConstant F := by
      have h1 : IsLocallyConstant fun p : π.ker × A => φN p.1 := hφN1.comp_continuous continuous_fst
      have h2 : IsLocallyConstant fun p : π.ker × A => f p.2 := hf'.1.comp_continuous continuous_snd
      have h3 : IsLocallyConstant fun p : π.ker × A => l (σ (e p) v) :=
        ((hσ.isLocallyConstant_orbit v).comp_continuous e.continuous).comp l
      exact (h1.mul h2).mul h3
    have hFcs : HasCompactSupport F := by
      refine IsCompact.of_isClosed_subset (IsCompact.prod hφN2 hf'.2) (isClosed_tsupport F) ?_
      refine closure_minimal ?_ ((isClosed_tsupport _).prod (isClosed_tsupport _))
      intro p hp
      refine ⟨subset_tsupport _ ?_, subset_tsupport _ ?_⟩
      · intro h0
        apply hp
        show φN p.1 * f p.2 * l (σ (e p) v) = 0
        rw [h0, zero_mul, zero_mul]
      · intro h0
        apply hp
        show φN p.1 * f p.2 * l (σ (e p) v) = 0
        rw [h0, mul_zero, zero_mul]
    have hFi : Integrable F P := hFlc.continuous.integrable_of_hasCompactSupport hFcs
    refine ⟨?_, ?_⟩
    · rw [hν]
      refine Integrable.smul_measure_nnreal ?_
      rw [hE.integrable_map_iff]
      exact hFi.congr (Filter.Eventually.of_forall fun p => (hFe p).symm)
    · have hin : ∀ a, ∫ h, F (h, a) ∂μN = f a * l (T (σ (ι a) v)) := by
        intro a
        rw [hT, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun h => ?_)
        show φN h * f a * l (σ (e (h, a)) v) = f a * (φN h * l (σ h (σ (ι a) v)))
        rw [he, map_mul, Module.End.mul_apply]
        ring
      have hB2 := (hB v (l ∘ₗ T)).2
      simp only [LinearMap.comp_apply, MonoidHom.comp_apply] at hB2
      rw [hν, integral_smul_nnreal_measure, hE.integral_map,
        integral_congr_ae (Filter.Eventually.of_forall hFe), integral_prod_symm F hFi,
        show (fun a => ∫ h, F (h, a) ∂μN) = fun a => f a * l (T (σ (ι a) v)) from funext hin, ← hB2]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, smul_eq_mul, NNReal.smul_def,
        Complex.real_smul]

end General

variable {D : D7}

theorem isFinFamily_update {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (u : HeightOneSpectrum (𝓞 D.host.F))
    {f : GLoc D.sp.cm.sig V.gram u → ℂ} (hf : f ∈ CcLoc D.sp.cm.sig V.gram u) :
    IsFinFamily D.sp.cm.sig V.gram (frameLat V) (Function.update ff u f) := by
  refine ⟨fun v => ?_, ?_⟩
  · by_cases hv : v = u
    · subst hv
      simpa using hf
    · rw [Function.update_of_ne hv]
      exact hff.1 v
  · filter_upwards [hff.2, Filter.eventually_cofinite_ne u] with v hv hne
    rw [Function.update_of_ne hne]
    exact hv

theorem finite_mulSupport {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (g : GfC V) :
    (Function.mulSupport fun v => ff v (finLoc V v g)).Finite := by
  have hev := GlobalTheory.AdelicU.eventually_proj_mem_stabLoc (σ := D.sp.cm.sig) (J := V.gram) (L := frameLat V)
    (g := (g : GA D V))
  refine (Filter.eventually_cofinite.1 (hff.2.and hev)).subset fun v hv => ?_
  rintro ⟨h1, h2⟩
  apply hv
  show ff v (proj D.sp.cm.sig V.gram v (g : GA D V)) = 1
  rw [h1]
  exact (Set.indicator_of_mem h2 1).trans rfl

theorem finFn_update_mul {V : HSp D} {ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ}
    (hff : IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff) (u : HeightOneSpectrum (𝓞 D.host.F))
    {f : GLoc D.sp.cm.sig V.gram u → ℂ} (hf : f ∈ CcLoc D.sp.cm.sig V.gram u) (h : GfC V) (a : Gv V u)
    (hh : finLoc V u h = 1) :
    finFn V (Function.update ff u f) (h * locFin V u a) =
      finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u)) h * f a := by
  have hu : unitLoc D.sp.cm.sig V.gram (frameLat V) u ∈ CcLoc D.sp.cm.sig V.gram u := unitLoc_mem u
  have m1 := finite_mulSupport (isFinFamily_update hff u hf) (h * locFin V u a)
  have m2 := finite_mulSupport (isFinFamily_update hff u hu) h
  have hfin : ∀ (ff' : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ) (g : GfC V),
      finFn V ff' g = ∏ᶠ v, ff' v (finLoc V v g) := fun _ _ => rfl
  have hloc : ∀ v, finLoc V v (locFin V u a) = proj D.sp.cm.sig V.gram v (emb D.sp.cm.sig V.gram u a) :=
    fun _ => rfl
  rw [hfin, hfin, ← mul_finprod_cond_ne u m1, ← mul_finprod_cond_ne u m2]
  have hoff : (∏ᶠ (v) (_ : v ≠ u), Function.update ff u f v (finLoc V v (h * locFin V u a))) =
      ∏ᶠ (v) (_ : v ≠ u), Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u) v (finLoc V v h) := by
    refine finprod_congr fun v => finprod_congr fun hv => ?_
    rw [Function.update_of_ne hv, Function.update_of_ne hv, map_mul, hloc, proj_emb_ne D.sp.cm.sig V.gram hv, mul_one]
  rw [hoff, Function.update_self, Function.update_self, map_mul, hh, hloc, proj_emb_self, one_mul]
  have h1 : unitLoc D.sp.cm.sig V.gram (frameLat V) u 1 = 1 :=
    (Set.indicator_of_mem (one_mem _) 1).trans rfl
  rw [h1, one_mul, mul_comm]

theorem exists_offOp : ∀ (D : D7) (V : HSp D) (u : HeightOneSpectrum (𝓞 D.host.F)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)), (∀ v, (μf v).IsHaarMeasure) → (∀ᶠ v in cofinite, μf v (Kv V v) = 1) → ∀ ν, IsFinMeas V μf ν → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ ff, IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∃ (H : W →ₗ[ℂ] W) (K : Subgroup (GfC V)), IsOpen (K : Set (GfC V)) ∧ (∀ g x, H (σ (locFin V u g) x) = σ (locFin V u g) (H x)) ∧ (∀ x, ∀ k ∈ K, finLoc V u k = 1 → σ k (H x) = H x) ∧ ∀ f ∈ CcLoc D.sp.cm.sig V.gram u, ∀ B, GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp (μf u) (σ.comp (locFin V u)) f B → GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp ν σ (finFn V (Function.update ff u f)) (H ∘ₗ B) := by
  intro D V u μf hμf hK ν hν W _ _ σ hσ ff hff
  haveI := hμf u
  haveI : LocallyCompactSpace (GfC V) := GlobalTheory.AdelicU.locallyCompactSpace_finPts D.sp.cm.sig V.gram
  haveI : ν.IsHaarMeasure := hν.1
  have hu : unitLoc D.sp.cm.sig V.gram (frameLat V) u ∈ CcLoc D.sp.cm.sig V.gram u := unitLoc_mem u
  have hfam := isFinFamily_update hff u hu
  have hφ := (GlobalTheory.TrConv.conv_finFn D V μf hμf hK ν hν _ _ hfam hfam).2.2
  have hφ' : IsLocallyConstant (finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u))) ∧
      HasCompactSupport (finFn V (Function.update ff u (unitLoc D.sp.cm.sig V.gram (frameLat V) u))) := hφ
  have hι : Continuous (locFin V u) := continuous_induced_rng.2 (continuous_emb D.sp.cm.sig V.gram u)
  have hπ : Continuous (finLoc V u) := (continuous_proj D.sp.cm.sig V.gram u).comp continuous_subtype_val
  have hπι : ∀ a, finLoc V u (locFin V u a) = a := fun a => proj_emb_self D.sp.cm.sig V.gram u a
  have hc : ∀ a g, finLoc V u g = 1 → Commute (locFin V u a) g := fun a g hg =>
    Subtype.ext (commute_emb D.sp.cm.sig V.gram a hg).eq
  obtain ⟨H, h1, h2, h3⟩ := exists_op (locFin V u) (finLoc V u) hι hπ hπι hc (μf u) ν σ hσ hφ
  exact ⟨H, leftStabilizer _, isOpen_leftStabilizer hφ'.1 hφ'.2, h1, h2,
    fun f hf B hB => h3 f hf B hB _ fun h a hh => finFn_update_mul hff u hf h a hh⟩

end GlobalTheory.OffOp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PureTensorUpdateFactorFromBaseVector
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PlaceTensorStep

theorem wAt_wAt_ne {D : D7} {m n : ℕ} {p q : Place D} (h : p ≠ q) (w : Mx D m n) : wAt p (wAt q w) = 0 := by
  have h0 : idem D p * idem D q = 0 := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q h
  funext i j
  show idem D p * (idem D q * w i j) = (0 : Mx D m n) i j
  rw [← mul_assoc, h0, zero_mul]
  rfl

theorem wAt_wAt_self {D : D7} {m n : ℕ} (p : Place D) (w : Mx D m n) : wAt p (wAt p w) = wAt p w := by
  have h1 : idem D p * idem D p = idem D p := (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p
  funext i j
  show idem D p * (idem D p * w i j) = idem D p * w i j
  rw [← mul_assoc, h1]

theorem change_factor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → ∀ (x x' : Place D → WO S T → ℂ) (f : WO S T → ℂ) (q : Place D), IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x f → x q = f₀ → (∀ p, p ≠ q → x' p = x p) → IsLocal ψ θ S T sS sT ΛS ΛT q (x' q) → ∃ f', IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x' f' ∧ ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → (∀ w : WO S T, ipO μ 𝓕 (heisO ψ S T (wAt q w) f) g = c * ipO μ 𝓕 (heisO ψ S T (wAt q w) f₀) g') → ipO μ 𝓕 f' g = c * ipO μ 𝓕 (x' q) g' := by
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x x' f q hf hxq hx' hloc

  have hop : IsLocOp ψ S T μ 𝓕 f₀ q (x' q) := by
    rcases q with v | τ
    · exact GlobalTheory.T.local_factor_finite_place_heisenberg_sum_base_vector D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ v _ hloc
    · exact GlobalTheory.T.localFactorRealPlace_eq_heisenbergIntegral_base D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ τ _ hloc
  obtain ⟨L, hL, himg, hx'L⟩ := hop
  have hfpure := hf
  obtain ⟨hres, hfth, hprod⟩ := hf

  obtain ⟨f', hf'th, hf'⟩ := himg f hfth
  have hstd := GlobalTheory.PlaceTensor.base_std hB
  have hlaws := GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hstd S T
  have hthw : ∀ u, IsThetaFunO ψ S T (heisO ψ S T u f₀) := fun u => hlaws.1 u f₀ (GlobalTheory.PlaceTensor.base_theta hB)
  refine ⟨f', ⟨⟨?_, ?_⟩, hf'th, ?_⟩, ?_⟩
  · intro p
    by_cases hp : p = q
    · subst hp; exact hloc
    · rw [hx' p hp]; exact hres.1 p
  · refine (hres.2.union (Set.finite_singleton q)).subset ?_
    intro p hp
    by_cases hpq : p = q
    · exact Or.inr hpq
    · left
      have hp' : x' p ≠ f₀ := hp
      rw [hx' p hpq] at hp'
      exact hp'
  · intro w
    have hfin := (hprod w).1
    have hsupp : (Function.mulSupport fun p => ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)).Finite := by
      refine (hfin.union (Set.finite_singleton q)).subset ?_
      intro p hp
      by_cases hpq : p = q
      · exact Or.inr hpq
      · left
        rw [Function.mem_mulSupport] at hp ⊢
        rw [hx' p hpq] at hp
        exact hp
    refine ⟨hsupp, ?_⟩

    have hrest : (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x' p) (heisO ψ S T (wAt p w) f₀)) =
        ∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀) :=
      finprod_congr fun p => finprod_congr fun hp => by rw [hx' p hp]

    have key : ∀ u, ipO μ 𝓕 (heisO ψ S T (wAt q u) f) (heisO ψ S T w f₀) =
        (∏ᶠ (p) (_ : p ≠ q), ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) *
          ipO μ 𝓕 (heisO ψ S T (wAt q u) f₀) (heisO ψ S T (wAt q w) f₀) := by
      intro u
      obtain ⟨-, -, hpu⟩ := GlobalTheory.T.heisenberg_operator_pure_tensor_place_by_place D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 hB hμ x f hfpure (wAt q u)
      obtain ⟨hfinu, hequ⟩ := hpu w
      rw [hequ, ← mul_finprod_cond_ne q hfinu]
      dsimp only
      rw [hxq, wAt_wAt_self, mul_comm]
      congr 1
      exact finprod_congr fun p => finprod_congr fun hp => by rw [wAt_wAt_ne hp, WeilVacMove.heisO_zero]
    rw [← mul_finprod_cond_ne q hsupp, hrest, hf' _ (hthw w)]
    simp_rw [key]
    rw [hL, hx'L _ (hthw _), mul_comm]
  · intro g g' c hg hg' hcoef
    rw [hf' g hg, hx'L g' hg']
    simp_rw [hcoef]
    exact hL c _

end GlobalTheory.PlaceTensorStep

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionConjugatedUnitaryElementEqOneIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reduction_conjugated_unitary_element_eq_one_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = 1 ↔ k ∈ X.B.I.Kg X.B.g) := by
  first | exact @GlobalTheory.KapRed.red_kap_eq_one_iff | exact GlobalTheory.KapRed.red_kap_eq_one_iff | (intros; apply GlobalTheory.KapRed.red_kap_eq_one_iff <;> assumption)
end

