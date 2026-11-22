import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0039
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SubQRMemIntegers
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

open Formalism.L2.SG.LocVol Formalism.L2.SG.Pf.NcS.KfOrbPf Formalism.L2.SG.Pf.NcS.IntWittPf

theorem trace_one_tmul_len {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

theorem sub_qR_mem_integers : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (t : F),
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ X ∈ (latV b v : Set (Fin 1 → Fin M → Fv F v ⊗[F] E)),
        algebraMap F (Fv F v) t - qR (Fv F v) σ J (X 0) ∈ v.adicCompletionIntegers F := by
  intro F E _ _ _ _ _ σ _ M J _ d b t
  haveI : FiniteDimensional F E := Module.Finite.of_basis b
  have hb : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ k, inclR (F := F) (Fv F v) (b k) ∈ OEv (E := E) v :=
    Filter.eventually_all.2 fun k => ev_oev (b k)
  have hJ : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, inclR (F := F) (Fv F v) (J i j) ∈ OEv (E := E) v :=
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ev_oev (J i j)
  have htr : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ k, algebraMap F (Fv F v) (Algebra.trace F E (b k)) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun k => ev_int (Algebra.trace F E (b k))
  filter_upwards [ev_int (F := F) t, ev_int (F := F) (1 / 2), hb, hJ, htr, ev_crd_oev (E := E) b]
    with v ht hh hbv hJv htrv hc X hX
  have hrepr : ∀ z : Fv F v ⊗[F] E,
      z = ∑ k, (Algebra.TensorProduct.basis (Fv F v) b).repr z k • ((1 : Fv F v) ⊗ₜ[F] b k) := by
    intro z
    conv_lhs => rw [← (Algebra.TensorProduct.basis (Fv F v) b).sum_repr z]
    simp only [Algebra.TensorProduct.basis_apply]
  have hx : ∀ i, X 0 i ∈ oevRing (E := E) v := by
    intro i
    rw [hrepr (X 0 i)]
    refine Subring.sum_mem _ fun k _ => ?_
    exact oev_smul' v (hX 0 i k) (hbv k)
  have hh' : hR (Fv F v) σ J (X 0) (X 0) ∈ oevRing (E := E) v := by
    show ∑ i, ∑ j, sigR (Fv F v) σ (X 0 i) * JR (Fv F v) J i j * X 0 j ∈ oevRing (E := E) v
    refine sum_mem fun i _ => sum_mem fun j _ => ?_
    exact mul_mem (mul_mem (oev_sigR v σ (hx i)) (hJv i j)) (hx j)
  have htrace : Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (hR (Fv F v) σ J (X 0) (X 0)) ∈
      v.adicCompletionIntegers F := by
    rw [hrepr (hR (Fv F v) σ J (X 0) (X 0)), map_sum]
    refine sum_mem fun k _ => ?_
    rw [map_smul, trace_one_tmul_len, smul_eq_mul]
    exact mul_mem (hc _ hh' k) (htrv k)
  exact sub_mem ht (mul_mem hh htrace)

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ValueFormula
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Eis
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn GlobalTheory.SiegelFormula

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

def IndepT (D : D7) (m r : ℕ) : Type :=
  {ξ : Matrix (Fin m) (Fin r) D.host.E // Function.Injective ξ.mulVec}

def HermQ (D : D7) (r : ℕ) : Type :=
  {b : Matrix (Fin r) (Fin r) D.host.E // ∀ i j, D.sp.cm.sig (b j i) = b i j}

variable {D : D7}

def indTheta (V : HSp D) {r : ℕ} (Φ : Mx D V.rank r → ℂ) (h : GA D V) : ℂ :=
  ∑' ξ : IndepT D V.rank r, Φ (invPt V h ξ.1)

def cellTerm (ψ : AddChar (AF D.host.F) ℂ) (V : HSp D) {r : ℕ} (μ : Measure (Mx D V.rank r)) (Φ : Mx D V.rank r → ℂ)
    (b : HermQ D r) : ℂ :=
  ∫ y, Φ y * ψ (halfTr (Matrix.trace (HMul.hMul (b.1.map (incA D)) (inner V y y) : Mx D r r))) ∂μ

end GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

namespace GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

def CoreFormula : Prop :=
  ∀ (D : D7) (r : ℕ) (V : HSp D), 1 ≤ r → 2 * r < V.rank →
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsCharAF D.host.F ψ →
  ∀ θ : InfFam D, IsInfFam θ →
  ∀ (μ : Measure (Mx D V.rank r)) (𝓕 : Set (Mx D V.rank r)), IsCovolOne (ratMx D V.rank r) μ 𝓕 →
  ∀ ν : Measure (GA D V), ν.IsHaarMeasure → ∀ Φ : schwartzA θ V.rank r,
    Summable (fun b : HermQ D r => ‖cellTerm ψ V μ Φ.1 b‖) ∧
      ⨍ q, AutomorphicL2Unitary.descend (GQ V) (indTheta V Φ.1) q ∂autMeasure V ν = ∑' b : HermQ D r, cellTerm ψ V μ Φ.1 b

def ValueFormula : Prop :=
  ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → 2 * A.rank < B.rank →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ (dblSp A) B 1 χ ω → ∀ f, IsThetaFunO ψ (dblSp A) B f →
  ∀ (ν : Measure (Mx D B.rank A.rank)) (𝓖 : Set (Mx D B.rank A.rank)), IsCovolOne (ratL B A) ν 𝓖 →
    CosetConv (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) 1 →
    cosetSum (siegel A) (GQ (dblSp A)) (swSection A B ν 𝓖 ω f) 1 =
      ⨍ q, AutomorphicL2Unitary.descend (GQ B) (fun h => thetaKO ω 1 h f) q ∂autMeasure B m

end GlobalTheory.CompanionTheory.Hypotheses₂.WeilU

end
end

