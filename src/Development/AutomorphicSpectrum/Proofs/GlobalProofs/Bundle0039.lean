import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0038
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
import Mathlib
import GroundTheory.GlobalFields.TateThesis.AdeleMeasure
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0027
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.AdeleHaarProductDecomposition
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM

def splitVec (F : Type) [Field F] [NumberField F] (ι : Type) :
    (ι → AF F) ≃ₜ+ (ι → Ainf F) × (ι → Af F) where
  toFun y := (fun i => (y i).1, fun i => (y i).2)
  invFun p := fun i => (p.1 i, p.2 i)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  continuous_toFun := by
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun i => continuous_fst.comp (continuous_apply i)
    · exact continuous_pi fun i => continuous_snd.comp (continuous_apply i)
  continuous_invFun := by
    refine continuous_pi fun i => Continuous.prodMk ?_ ?_
    · exact (continuous_apply i).comp continuous_fst
    · exact (continuous_apply i).comp continuous_snd

theorem map_split_eq_smul_prod : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι]
    (m : Measure (ι → AF F)) (μ₁ : Measure (ι → Ainf F)) (μ₂ : Measure (ι → Af F)),
    m.IsAddHaarMeasure → μ₁.IsAddHaarMeasure → μ₂.IsAddHaarMeasure →
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧
      m.map (fun y : ι → AF F => ((fun i => (y i).1, fun i => (y i).2) : (ι → Ainf F) × (ι → Af F))) =
        c • μ₁.prod μ₂ := by
  intro F _ _ ι _ m μ₁ μ₂ hm h₁ h₂
  haveI : SecondCountableTopology (Af F) := Formalism.IndefR.Eqv.G5.af_secondCountable
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  haveI : SecondCountableTopology (AF F) :=
    inferInstanceAs (SecondCountableTopology (Ainf F × Af F))
  have hH : (m.map (splitVec F ι)).IsAddHaarMeasure :=
    ContinuousAddEquiv.isAddHaarMeasure_map m (splitVec F ι)
  have hc := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (m.map (splitVec F ι)) (μ₁.prod μ₂)
  refine ⟨(Measure.addHaarScalarFactor (m.map (splitVec F ι)) (μ₁.prod μ₂) : ENNReal), ?_, ENNReal.coe_ne_top, ?_⟩
  · exact_mod_cast hc.ne'
  · have h := Measure.isAddLeftInvariant_eq_smul (m.map (splitVec F ι)) (μ₁.prod μ₂)
    exact h

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.ProdM
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def boxF {M : ℕ} (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E)) :
    Set (Fin 1 → Fin M → Af F ⊗[F] E) :=
  {X | ∀ v, projV v X ∈ A v}

def pureC {M : ℕ} (φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℂ)
    (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin M → Fv F v ⊗[F] E))
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ℂ :=
  φ (projInf X) * (boxF A).indicator (fun _ => (1 : ℂ)) (projFin X)

def intF (S : Finset (HeightOneSpectrum (𝓞 F))) : Set (Af F) :=
  {y | ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}

def coefS (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (ψ : AddChar (AF F) ℂ)
    (dx : Measure (Fin 1 → Fin M → AF F ⊗[F] E)) (db : Measure (AF F))
    (Φ : (Fin 1 → Fin M → AF F ⊗[F] E) → ℂ) (t : F) (S : Finset (HeightOneSpectrum (𝓞 F))) : ℂ :=
  ∫ b, (intF S).indicator (fun _ => (1 : ℂ)) (sndA F b) *
    (starT σ J ψ dx Φ b * ψ (-(algebraMap F (AF F) t * b))) ∂db

def boxA (S : Finset (HeightOneSpectrum (𝓞 F))) (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) : Set (Af F) :=
  {y | (∀ v ∈ S, y v ∈ U v) ∧ ∀ v, v ∉ S → y v ∈ v.adicCompletionIntegers F}

def testT (ρ : Ainf F → ℝ) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (U : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)) (y : AF F) : ℂ :=
  (ρ (fstA F y) : ℂ) * (boxA S U).indicator (fun _ => (1 : ℂ)) (sndA F y)

def fouA (ψ : AddChar (AF F) ℂ) (db : Measure (AF F)) (T : AF F → ℂ) (b : AF F) : ℂ :=
  ∫ y, T y * ψ (y * b) ∂db

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsAdelicHaarCovolumeOne
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV

theorem exists_isCovolOne : ∀ (F : Type) [Field F] [NumberField F], ∃ db : Measure (AF F), IsCovolOne db := by
  intro F _ _
  have e : (measAF : MeasurableSpace (AF F)) = GroundTheory.Global.measurableSpace_adeleRing F :=
    (GroundTheory.Global.borelSpace_adeleRing F).measurable_eq.symm
  unfold IsCovolOne
  rw [e]
  refine ⟨GroundTheory.Global.adeleMeasure F, inferInstance, GroundTheory.Global.fundamentalSet F, ?_,
    GroundTheory.Global.adeleMeasure_fundamentalSet F⟩
  exact GroundTheory.Global.isAddFundamentalDomain_fundamentalSet F

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.TupOfCv
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth

section Gen
open NumberField IsDedekindDomain MeasureTheory
open GroundTheory.Global GroundTheory.Automorphic.GJMatrix GroundTheory.Heights₂.Theta
open scoped TensorProduct ENNReal Matrix NumberField.AdeleRing

variable {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] [DecidableEq ι]

def chiG (G : Matrix ι ι F) (u v : ι → 𝔸[F]) : ℂ :=
  (adelicChar F (u ⬝ᵥ (G.map (algebraMap F 𝔸[F]) *ᵥ v)) : ℂ)

def mulHomeo (A B : Matrix ι ι 𝔸[F]) (hAB : A * B = 1) (hBA : B * A = 1) : (ι → 𝔸[F]) ≃ₜ (ι → 𝔸[F]) where
  toFun u := A *ᵥ u
  invFun u := B *ᵥ u
  left_inv u := by simp only [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
  right_inv u := by simp only [Matrix.mulVec_mulVec, hAB, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

end Gen

section Link
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.CompanionTheory.SW.BB
open scoped TensorProduct ENNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def tupOf {M d : ℕ} (b : Module.Basis (Fin d) F E) (u : Fin M × Fin d → AF F) :
    Fin 1 → Fin M → AF F ⊗[F] E :=
  fun _ i => ∑ k, u (i, k) • ((1 : AF F) ⊗ₜ[F] b k)

theorem cv_tupOf {M d : ℕ} (b : Module.Basis (Fin d) F E) (u : Fin M × Fin d → AF F) :
    cv (AF F) b (tupOf b u 0) = u := by
  funext p
  have h : (tupOf b u 0 p.1) = ∑ k, u (p.1, k) • (Algebra.TensorProduct.basis (AF F) b) k := by
    simp only [tupOf, Algebra.TensorProduct.basis_apply]
  simp only [cv]
  rw [h, Module.Basis.repr_sum_self]

theorem tupOf_cv {M d : ℕ} (b : Module.Basis (Fin d) F E) (X : Fin 1 → Fin M → AF F ⊗[F] E) :
    tupOf b (cv (AF F) b (X 0)) = X := by
  funext u i
  obtain rfl : u = 0 := Subsingleton.elim _ _
  simp only [tupOf, cv]
  conv_rhs => rw [← (Algebra.TensorProduct.basis (AF F) b).sum_repr (X 0 i)]
  simp only [Algebra.TensorProduct.basis_apply]

end Link

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Fth
end
end

