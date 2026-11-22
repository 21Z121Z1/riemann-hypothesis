import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0053
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0088
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0109
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0117
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0140
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesAndLevelPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0113
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0120
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0072
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0065
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0081

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AutomorphicFormUniformLimitDiscreteSeriesSeries
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClosureSeries

open GlobalTheory.TypeSum

theorem coef_of_gkMap : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau), IsInfFam (D := D) θ → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
      (σ : Matrix (Fin V.rank) (Fin V.rank) ℂ → (H →L[ℂ] H)) (lam : Fin V.rank → ℝ) (ε : Fin V.rank → Bool)
      (P : Matrix (Fin V.rank) (Fin V.rank) ℂ) (T : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ →ₗ[ℂ] (GA D V → ℂ)),
    Formalism.QuantumDeterminants.IsHCParam lam → IsDS ε lam σ → IsUnit P → Pᴴ * Formalism.REAL.Jm ε * P = gramAt D V τ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.IsGKMap θ V τ ε σ P T →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.kFin ε σ) (x : GA D V), ∃ ℓ : H →ₗ[ℂ] ℂ,
      Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ ∧ SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v : H) ∧
      ∀ y ∈ UJset ε, T v (x * atTau θ V τ (P⁻¹ * y * P)) = ℓ (σ y v) := GlobalTheory.T.discreteSeries_gKMap_values_eq_generalisedCoefficients

theorem coef_transport : GlobalTheory.Published.DiscreteSeriesUpqUnique → ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ),
    Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H H' : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')),
    IsDS ε lam σ → IsDS ε lam σ' →
    ∀ (P P' G : Matrix (Fin n) (Fin n) ℂ), IsUnit P → IsUnit P' → Pᴴ * Formalism.REAL.Jm ε * P = G →
      P'ᴴ * Formalism.REAL.Jm ε * P' = G →
    ∀ (F : Matrix (Fin n) (Fin n) ℂ → ℂ) (ℓ : H' →ₗ[ℂ] ℂ) (v : H'), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ' ℓ →
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ' v → (∀ y ∈ UJset ε, F (P'⁻¹ * y * P') = ℓ (σ' y v)) →
    ∃ (ℓ' : H →ₗ[ℂ] ℂ) (v' : H), Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ ℓ' ∧
      SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ v' ∧ ∀ y ∈ UJset ε, F (P⁻¹ * y * P) = ℓ' (σ y v') := GlobalTheory.T.matrix_coefficient_frame_change_discrete_series

theorem closure_model : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsDS ε lam σ → ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.TypeSum.lieOf (Formalism.REAL.Jm ε)) (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ f := GlobalTheory.T.hasAllKTypes_of_closure_discreteSeriesCoefficients

theorem isClosed_UJset {n : ℕ} (ε : Fin n → Bool) : IsClosed (UJset ε) := by
  have : UJset ε = {g : Matrix (Fin n) (Fin n) ℂ | gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε} := rfl
  rw [this]
  exact isClosed_eq ((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul continuous_id)
    continuous_const

theorem continuous_mul_left_GA {D : D7} (V : HSp D) (x : GA D V) : Continuous fun y : GA D V => x * y := by
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := inferInstance
  refine continuous_induced_rng.2 ?_
  exact (continuous_mul_left _).comp continuous_induced_dom

theorem closure_to_series : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (τ : D.what₂.Tau) (S : SPar) (φ : GA D V → ℂ),
    GlobalTheory.Published.DiscreteSeriesUpqExists → GlobalTheory.Published.DiscreteSeriesUpqUnique → GlobalTheory.Published.HarishChandraModules →
    GlobalTheory.Published.CasselmanWallach → IsInfFam (D := D) θ → V.SigOK →
    GoodPar V.rank (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 S → IsAutFunSm θ V φ →
    GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.HasTypeAt θ V τ S φ → IsTypeAt θ V τ S φ := by
  intro D θ V τ S φ hEx hUn hHC hCW hθ hV hS hφ hT
  obtain ⟨lam₀, ε₀, hE₀, hP₀, hp, hq⟩ := hS
  obtain ⟨H, i1, i2, σ, hc, hnt, hU, hI, hL2, hK, hmin⟩ := hEx _ ε₀ lam₀ hP₀
  have hσ : IsDS ε₀ lam₀ σ := ⟨hc, hnt, hU, hI, hL2, hK, hmin⟩
  obtain ⟨P, hPu, hPG⟩ := GlobalTheory.Published.exists_frame_of_hasSignature (hV (tauE D τ)) ε₀ hp hq
  refine ⟨H, i1, i2, σ, lam₀, ε₀, P, hE₀, hσ, hPu, hPG, fun x => ?_⟩

  have hfin : ∀ ψ ∈ GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.finPartOfType θ V τ S, ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H),
      (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε₀) σ (ℓ j)) ∧ (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε₀) σ (v j)) ∧
      ∀ y ∈ UJset ε₀, ψ (x * atTau θ V τ (P⁻¹ * y * P)) = ∑ j, ℓ j (σ y (v j)) := by
    intro ψ hψ
    rw [GlobalTheory.IndefiniteRowSideFullHecke.FinitePartTypes.finPartOfType, sSup_eq_iSup'] at hψ
    refine Submodule.iSup_induction (motive := fun ψ : GA D V → ℂ => ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ))
      (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε₀) σ (ℓ j)) ∧
      (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε₀) σ (v j)) ∧
      ∀ y ∈ UJset ε₀, ψ (x * atTau θ V τ (P⁻¹ * y * P)) = ∑ j, ℓ j (σ y (v j))) _ hψ ?_ ⟨0, Fin.elim0, Fin.elim0, fun j => j.elim0, fun j => j.elim0,
      fun y _ => by simp⟩ ?_
    · rintro ⟨W, H', j1, j2, σ', lam, ε, P', T, hE, hHC', hD', hP', hJ', hGK, rfl⟩ ψ ⟨w, rfl⟩
      obtain ⟨rfl, rfl⟩ := GlobalTheory.SignedParTest.isEnum_unique hE hE₀
      obtain ⟨ℓ, hℓ, hv, he⟩ := coef_of_gkMap θ V τ hθ hHC hCW H' σ' lam ε P' T hHC' hD' hP' hJ' hGK w x
      obtain ⟨ℓ', v', hℓ', hv', he'⟩ := coef_transport hUn _ ε lam hHC' H H' σ σ' hσ hD' P P' _ hPu hP' hPG hJ'
        (fun y => T w (x * atTau θ V τ y)) ℓ w hℓ hv he
      exact ⟨1, fun _ => ℓ', fun _ => v', fun _ => hℓ', fun _ => hv', fun y hy => by simpa using he' y hy⟩
    · rintro a b ⟨m, ℓ, v, h1, h2, h3⟩ ⟨m', ℓ', v', h1', h2', h3'⟩
      refine ⟨m + m', Fin.append ℓ ℓ', Fin.append v v', fun j => ?_, fun j => ?_, fun y hy => ?_⟩
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa using h1 i
        · simpa using h1' i
      · refine Fin.addCases (fun i => ?_) (fun i => ?_) j
        · simpa using h2 i
        · simpa using h2' i
      · show a _ + b _ = _
        rw [h3 y hy, h3' y hy, Fin.sum_univ_add]
        simp
  set f : Matrix (Fin V.rank) (Fin V.rank) ℂ → ℂ := fun y => φ (x * atTau θ V τ (P⁻¹ * y * P)) with hf
  have hcont : ContinuousOn (fun y : Matrix (Fin V.rank) (Fin V.rank) ℂ => x * atTau θ V τ (P⁻¹ * y * P))
      (UJset ε₀) := by
    refine (continuous_mul_left_GA V x).comp_continuousOn ?_
    refine (GlobalTheory.PointAtPlaceHom.continuousOn_atTau hθ V τ).comp
      ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).continuousOn ?_
    intro y hy
    exact GlobalTheory.LowTypeDetermined.conj_inv_mem hPu hPG hy
  have hfc : ContinuousOn f (UJset ε₀) := hφ.cont.comp_continuousOn hcont
  have hB := closure_model hHC hCW _ ε₀ lam₀ hP₀ H σ hσ f hfc
    (GlobalTheory.TypeSum.GrowthAtPlace.umg_atTau D θ hθ V τ φ hφ ε₀ P hPu hPG x) (by
      intro C hC δ hδ
      have hK : IsCompact ((fun y => x * atTau θ V τ (P⁻¹ * y * P)) '' (C ∩ UJset ε₀)) :=
        (hC.inter_right (isClosed_UJset ε₀)).image_of_continuousOn (hcont.mono Set.inter_subset_right)
      obtain ⟨ψ, hψ, happ⟩ := hT _ hK δ hδ
      obtain ⟨m, ℓ, v, h1, h2, h3⟩ := hfin ψ hψ
      refine ⟨m, ℓ, v, h1, h2, fun y hyC hy => ?_⟩
      rw [← h3 y hy]
      exact happ _ ⟨y, ⟨hyC, hy⟩, rfl⟩)
  have hd := (Matrix.isUnit_iff_isUnit_det _).1 hPu
  have a1 := Matrix.mul_nonsing_inv _ hd
  have a2 := Matrix.nonsing_inv_mul _ hd
  have hi : P⁻¹⁻¹ = P := Matrix.nonsing_inv_nonsing_inv _ hd
  have t3 := GlobalTheory.TypeSum.hasTypeAll_transport _ H H σ (fun g => σ (P * g * P⁻¹)) (Formalism.REAL.Jm ε₀)
    (gramAt D V τ) P⁻¹ (GlobalTheory.TypeSum.isUnit_Jm ε₀) (IsUnit.of_mul_eq_one _ a2) (by
      rw [show gramAt D V τ = Pᴴ * Formalism.REAL.Jm ε₀ * P from hPG.symm]
      calc (P⁻¹)ᴴ * (Pᴴ * Formalism.REAL.Jm ε₀ * P) * P⁻¹ = (P * P⁻¹)ᴴ * Formalism.REAL.Jm ε₀ * (P * P⁻¹) := by
            simp only [conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [a1]; simp) (LinearIsometryEquiv.refl ℂ H) (fun g _ v => by
      have e : P * (P⁻¹ * g * P⁻¹⁻¹) * P⁻¹ = g := by
        rw [hi]
        calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
          _ = g := by rw [a1, Matrix.one_mul, Matrix.mul_one]
      show σ g v = σ (P * (P⁻¹ * g * P⁻¹⁻¹) * P⁻¹) v
      rw [e]) f hB
  have e' : (fun y => f (P⁻¹⁻¹ * y * P⁻¹)) = fun y => φ (x * atTau θ V τ y) := by
    funext y
    show φ (x * atTau θ V τ (P⁻¹ * (P⁻¹⁻¹ * y * P⁻¹) * P)) = φ (x * atTau θ V τ y)
    rw [hi]
    congr 3
    calc P⁻¹ * (P * y * P⁻¹) * P = (P⁻¹ * P) * y * (P⁻¹ * P) := by simp only [Matrix.mul_assoc]
      _ = y := by rw [a2, Matrix.one_mul, Matrix.mul_one]
  rw [e'] at t3
  exact GlobalTheory.TypeSum.hasTypeAll_iff.1 t3

end GlobalTheory.ClosureSeries
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayFieldAny
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize GlobalTheory.FieldSize.RayExistCurve
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurveAny

theorem curveOver_of_rayField_any : GlobalTheory.NT.RayField → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (ι : AlgebraicClosure ℚ →ₐ[ℚ] ℂ) (K : IntermediateField ℚ (AlgebraicClosure ℚ)), K.map ι = ℚ⟮H.rt0⟯ → ∀ n : ℕ, 3 ≤ n → ∀ F : IntermediateField ℚ ℂ, (∀ M : IntermediateField ℚ (AlgebraicClosure ℚ), (K ≤ M ∧ FiniteDimensional ℚ M ∧ ∀ p : ℕ, (p.Prime ∧ ∃ π : AlgebraicClosure ℚ, π ∈ K ∧ IsIntegral ℤ π ∧ IsIntegral ℤ ((π - 1) / (n : AlgebraicClosure ℚ)) ∧ ∃ σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ, π * σ π = (p : AlgebraicClosure ℚ)) → {v : HeightOneSpectrum (𝓞 M) | ((p : ℕ) : 𝓞 M) ∈ v.asIdeal}.ncard = Module.finrank ℚ M) → M.map ι ≤ F) → GlobalTheory.CompRat.CurveOver H F n := by
  intro hRF E _ _ _ H ι K hK n hn F hF
  have hdm := H.d_mod
  have hd0 : 0 < H.d := H.d_prime.pos
  obtain ⟨hfin, h2⟩ := finrank_adjoin hd0 H.sqrt_neg_disc_sq
  have hconj := conj_eq_neg hd0 H.sqrt_neg_disc_sq
  have hr0 : H.rt0 ∈ ℚ⟮H.rt0⟯ := IntermediateField.mem_adjoin_simple_self ℚ H.rt0
  generalize ℚ⟮H.rt0⟯ = K₀ at hK hfin h2 hr0
  have hNF : NumberField K₀ := NumberField.mk
  have hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  have hD : discr K₀ = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr
  have hTC : IsTotallyComplex K₀ := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ) := by
      rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd0
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]
  obtain ⟨w, hw, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr
  let φ : K₀ →+* ℂ := algebraMap K₀ ℂ
  have hw' : φ w = (1 + H.rt0) / 2 := by
    have := congrArg φ hw
    rw [map_mul, map_add, map_one, map_ofNat] at this
    change _ = 1 + H.rt0 at this
    linear_combination this / 2
  have hc : ∀ a b : ℤ, φ ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2) := fun a b => by
    rw [← hw']
    simp
  have hn0 : (n : 𝓞 K₀) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  obtain ⟨L, _, _, _, hL⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hRF K₀ (Ideal.span {(n : 𝓞 K₀)})
    (by rwa [Ne, Ideal.span_singleton_eq_bot])
  let ψ : L →ₐ[K₀] ℂ := IsAlgClosed.lift
  let e₀ : L ≃ₐ[K₀] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  have hfR : FiniteDimensional K₀ ψ.fieldRange := e₀.toLinearEquiv.finiteDimensional
  have hLR := fun (_ : NumberField ψ.fieldRange) => hL.of_algEquiv e₀
  generalize ψ.fieldRange = R at hfR hLR
  have hNR : NumberField R := NumberField.of_module_finite K₀ R
  obtain ⟨hab, hR⟩ := hLR hNR
  change IsRay R (Ideal.span {(n : 𝓞 K₀)}) at hR
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) := (R.restrictScalars ℚ).comap ι
  have hM : M.map ι = R.restrictScalars ℚ := by
    refine IntermediateField.map_comap_eq_self fun z hz => ?_
    have hi : IsIntegral ℚ z :=
      (IsIntegral.of_finite ℚ (⟨z, hz⟩ : R)).map (algebraMap R ℂ).toRatAlgHom
    exact hi.mem_range_algHom_of_minpoly_splits (IsAlgClosed.splits _) ι
  let e : M ≃ₐ[ℚ] R := (M.equivMap ι).trans (IntermediateField.equivOfEq hM)
  have hfM : FiniteDimensional ℚ M := e.symm.toLinearEquiv.finiteDimensional
  have hNM : NumberField M := NumberField.mk
  have hRle : R.restrictScalars ℚ ≤ F := by
    rw [← hM]
    refine hF M ⟨fun x hx => ?_, hfM, ?_⟩
    · have : ι x ∈ K₀ := hK ▸ ⟨x, hx, rfl⟩
      exact R.algebraMap_mem (⟨ι x, this⟩ : K₀)
    rintro p ⟨hp, π, hπ, -, hπ1, σ, hσ⟩
    rw [ncard_congr e.toRingEquiv p, e.toLinearEquiv.finrank_eq]
    obtain ⟨r, -, hrr⟩ : H.rt0 ∈ K.map ι := hK ▸ hr0
    change ι r = H.rt0 at hrr
    have hn1 : (n : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hcK : ι ((π - 1) / n) ∈ K₀ := hK ▸ ⟨_, K.div_mem (K.sub_mem hπ K.one_mem) (natCast_mem K n), rfl⟩
    have hci : IsIntegral ℤ (⟨_, hcK⟩ : K₀) :=
      (isIntegral_algHom_iff φ.toIntAlgHom φ.injective).1 (hπ1.map (ι : AlgebraicClosure ℚ →+* ℂ).toIntAlgHom)
    obtain ⟨x, y, hxy⟩ := hgen ⟨_, hci⟩
    have h3 : ι ((π - 1) / n) = x + y * ((1 + H.rt0) / 2) := by
      rw [← hc, ← hxy]; rfl
    have h4 : π = 1 + n * (x + y * ((1 + r) / 2)) := by
      have : (π - 1) / n = x + y * ((1 + r) / 2) := ι.injective (by
        change ι _ = ι _
        rw [h3]; simp [hrr, map_ofNat])
      rw [← this]; field_simp; ring
    have hr2 : r ^ 2 = -(H.d : AlgebraicClosure ℚ) := ι.injective (by
      change ι _ = ι _
      rw [map_pow, hrr, H.sqrt_neg_disc_sq]; simp)
    have h5 : σ π = 1 + n * (x + y * ((1 + σ r) / 2)) := by
      rw [h4]; simp [map_ofNat]
    have h6 : ι π * ι (σ π) = p := by rw [← map_mul, hσ, map_natCast]
    have h7 : ι π = φ (1 + n * (x + y * w) : 𝓞 K₀) := by
      rw [h4]; simp [hrr, map_ofNat, hw']
    have hinj : ∀ a b : 𝓞 K₀, φ a = φ b → a = b := fun a b h => RingOfIntegers.coe_injective (φ.injective h)
    have hs : σ r = r ∨ σ r = -r := sq_eq_sq_iff_eq_or_eq_neg.1 (by rw [← map_pow, hr2]; simp)
    rcases hs with hs | hs
    · rw [hs, ← h4] at h5
      rw [h5, h7] at h6
      exact absurd (hinj _ _ (by simpa using h6)) (sq_ne_prime h2 hD φ hp (1 + n * (x + y * w)))
    · have h8 : ι (σ π) = φ (1 + n * (x + y * (1 - w)) : 𝓞 K₀) := by
        rw [h5, hs]
        simp only [map_add, map_mul, map_sub, map_neg, map_div₀, map_one, map_ofNat, map_natCast, map_intCast, hrr, hw']
        ring
      rw [h7, h8] at h6
      refine ncard_eq_finrank h2 hD φ hn R hR hp (c := x + y * w) (c' := x + y * (1 - w)) ?_
        (hinj _ _ (by simpa using h6))
      rw [← Complex.norm_conj (φ (1 + n * (x + y * w) : 𝓞 K₀))]
      congr 1
      simp only [map_add, map_mul, map_sub, map_div₀, map_one, map_ofNat, map_natCast, map_intCast, hconj, hw']
      ring
  refine (GlobalTheory.FinalJoin.CurveField.curveOver_of_weberIn E H F n (by omega)).1
    (hRle (R.algebraMap_mem (⟨H.rt0, hr0⟩ : K₀))) fun P hP => ?_
  have hW := GlobalTheory.T.weberInvariantTorsionValues_subset_rayClassField K₀ h2 (by omega) P (fun z => ?_) n hn R hR
  · exact ⟨hRle (hW (Set.mem_insert _ _)), fun s hs => hRle (hW (Set.mem_insert_of_mem _
      ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩))⟩
  · rw [hP]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, hc s.1 s.2⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a, b, rfl⟩ := hgen a
      exact ⟨(a, b), hc a b⟩

end GlobalTheory.FieldSize.RayExistCurveAny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRecordOverChoices
section
noncomputable section

namespace GlobalTheory.FinalJoin2

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField
open GlobalTheory.FieldSize GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 Formalism.L2.Pj Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons GlobalTheory.RunJoin
open GlobalTheory.Mem
open GlobalTheory.EX.OB

theorem exists_window_start (N y G : ℝ) (hN : 0 < N) (hG : 0 < G) : ∃ Ds : ℝ, 0 < Ds ∧
    y ≤ Real.log ((Ds / ((1 : ℕ) : ℝ)) ^ ((1 : ℝ) / N) * G ^ (-(2 : ℝ) / N)) := by
  refine ⟨Real.exp (N * y + 2 * Real.log G), Real.exp_pos _, le_of_eq ?_⟩
  rw [Nat.cast_one, div_one, ← Real.exp_mul, Real.rpow_def_of_pos hG, ← Real.exp_add, Real.log_exp]
  field_simp
  ring

set_option maxHeartbeats 1000000 in

theorem exists_record_over_choices (hR : GlobalTheory.NT.RayField) (eps cD ch : ℝ) (C : FC) (h0 : 0 < eps) (h1 : eps < 1 / 52)
    (hC : Std C) (hcD : 0 ≤ cD) (hch : 402 ≤ ch) : ∃ x0 : ℝ, ∀ (s : Scale) (P : PreCh) (q1 : ℕ)
      (a b : P.R.A → ℤ) (c : P.Word → Fin (P.R.k - 2) → Bool) (Lv : LevCh P), s.eps = eps → x0 ≤ s.x →
      ChOK s C cD ch P q1 a b c → Lv.GamP = GamS C s P.R →
      ∃ D : D7, JointQ D ∧ Nonempty (ErrX D) ∧ DV.KapDef D ∧ HostArith D.host ∧
        ∃ L : SizeData₂ D, L.sc = s ∧ Val C cD ch L := by
  obtain ⟨x0, hx0⟩ := GlobalTheory.EX.exists_sizeData_explicit eps C cD ch h0 h1 hC hcD hch
  refine ⟨x0, ?_⟩
  intro s P q1 a b c Lv hs hx hP hG
  obtain ⟨F, hfd, hrich, hsz⟩ := exists_rich_small_of_rayField hR (StdFrameObj.coordPre P Lv)
  obtain ⟨B, hB, hF, -⟩ := exists_base_of_rich _ F hfd hrich ∅ ∅ (by simp) (by simp)
  have hxp : 0 < s.x := by linarith [s.one_lt_alt]
  have hDel : (0 : ℚ) < (Delv s cD : ℚ) := by
    have : 0 < Delv s cD := Nat.ceil_pos.2 (by positivity)
    exact_mod_cast this
  have hlev : ∀ p ∈ Lv.host.levelPrimes, Lv.host.cls p = .splitK := (StdFrameObj.coordPre P Lv).level_split
  have key : ∀ Q : Pre, Q = StdFrameObj.coordPre P Lv → ∃ letter : Q.Word → Fin (Q.R.k - 2) → Bool, Function.Injective letter ∧
      (∀ w τ (l : ℕ) (h : l + 1 < Q.R.k - 1),
        (Q.hcW w τ).v ⟨l, by omega⟩ - (Q.hcW w τ).v ⟨l + 1, h⟩ = 4 * (Delv s cD : ℚ)) ∧
      ∀ w τ (l : ℕ) (h : l < Q.R.k - 2), (Q.hcW w τ).u ⟨l + 1, by omega⟩ =
        (Q.hcW w τ).v ⟨l, by omega⟩ - 1 / 2 - (if letter w ⟨l, h⟩ then (Delv s cD : ℚ) else 0) := by
    rintro Q rfl
    refine ⟨c, hP.inj, fun w τ l h => ?_, fun w τ l h => hP.code w τ l h⟩
    have h' : l + 1 < P.R.k - 1 := h
    have a1 := (hP.hc w).1 τ ⟨l, by omega⟩
    have a2 := (hP.hc w).1 τ ⟨l + 1, h'⟩
    refine (congrArg₂ (· - ·) a1 a2).trans ?_
    have : P.R.k - 2 - l = (P.R.k - 2 - (l + 1)) + 1 := by omega
    simp only [this]
    push_cast
    ring
  obtain ⟨letter, k1, k2, k3⟩ := key B.toPre hB
  obtain ⟨X, rfl, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_stages_with_delta B (Delv s cD : ℚ) letter (6 * s.x ^ (-C.P.CF)) hDel (by positivity) k1 k2 k3
  clear key k1 k2 k3 letter
  have hJ : JointQ X.toD7 := jointQ_of_small_field X F (hB ▸ hrich)
    ((congrArg (fun Q : Pre => ∀ L : ℝ, HostSz Q.host L → Sz F (poR Q.R L) (poR Q.R L)) hB).mpr hsz) hF
  have hE : Nonempty (ErrX X.toD7) := GlobalTheory.T.error_data_of_norm_generators X
    ((congrArg (fun Q : Pre => ∀ i, ∃ π : 𝓞 Q.host.E, (π : Q.host.E) ∈ Q.host.K ∧
      (π : Q.host.E) * Q.host.conj (π : Q.host.E) = (Q.host.g i : Q.host.E)) hB).mpr hP.arith.1)
  clear hF hrich hsz
  obtain ⟨B, Cc, W, V, S, N, Gj⟩ := X
  cases B
  dsimp only at hB
  subst hB
  set D := Stages.toD7 _ with hD
  refine ⟨D, hJ, hE, e3, ⟨hP.arith.1, hP.arith.2.1, hP.arith.2.2.1, hlev⟩, ?_⟩
  obtain ⟨L, l1, -, -, l4⟩ := hx0 s D (fun t => a t.1) (fun t => b t.1) hs hx hP.rank hP.val (hP.hc P.u₀) hP.dlog e1 hP.ct2
    hP.card e2 (fun u => by
      have e : (D.mem u).A.GamP = Lv.GamP := Cc.A_GamP u
      rw [e, hG, GamS, Real.log_exp]; rfl)
    (fun t => hP.win t.1 t.2) (fun τ t h ht => hP.top P.u₀ τ t h ht) e4
  exact ⟨L, l1, l4⟩

end GlobalTheory.FinalJoin2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberValuesMemOfContainsRayField
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberTransport

theorem absNorm_comap {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (e : 𝓞 K ≃+* 𝓞 K')
    (I : Ideal (𝓞 K')) : Ideal.absNorm (I.comap e) = Ideal.absNorm I := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact Nat.card_congr (Ideal.quotientEquiv (I.comap e) I e
    (Ideal.map_comap_of_surjective _ e.surjective I).symm).toEquiv

theorem containsRayField_congr {K L K' L' : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Field K'] [NumberField K'] [Field L'] [NumberField L'] (φ : K →+* L) (φ' : K' →+* L') (eK : K ≃+* K') (eL : L ≃+* L')
    (hc : ∀ x, φ' (eK x) = eL (φ x)) (n : ℕ) (h : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n) :
    GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ' n := by
  intro P hP
  let oK := RingOfIntegers.mapRingEquiv eK
  let oL := RingOfIntegers.mapRingEquiv eL
  let Q : HeightOneSpectrum (𝓞 L) := (HeightOneSpectrum.equivOfRingEquiv oL).symm P
  have hQ : Q.asIdeal = P.asIdeal.comap oL := rfl
  obtain ⟨f, α, h1, h2, h3⟩ := h Q (by rw [hQ, Ideal.mem_comap, map_natCast]; exact hP)
  have hcm : Q.asIdeal.comap (RingOfIntegers.mapRingHom φ) =
      (P.asIdeal.comap (RingOfIntegers.mapRingHom φ')).comap oK := by
    ext x
    rw [hQ]
    simp only [Ideal.mem_comap]
    have : RingOfIntegers.mapRingHom φ' (oK x) = oL (RingOfIntegers.mapRingHom φ x) :=
      RingOfIntegers.ext (hc x)
    rw [this]
  rw [hcm, absNorm_comap, hQ, absNorm_comap] at h1
  rw [hcm] at h2
  refine ⟨f, oK α, h1, ?_, ?_⟩
  · have := congrArg (Ideal.map oK) h2
    rwa [Ideal.map_pow, Ideal.map_comap_of_surjective _ oK.surjective, Ideal.map_span, Set.image_singleton] at this
  · have := map_dvd oK h3
    rwa [map_natCast, map_sub, map_one] at this

theorem weberIn_of_containsRayField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] (φ : K →+* L) (ψ : L →+* ℂ), Module.finrank ℚ K = 2 → (∃ a : K, a ^ 2 = -(H.d : K)) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField φ n → GlobalTheory.FinalJoin.WeberIn H ψ.toRatAlgHom.fieldRange n ∧ H.rt0 ∈ ψ.toRatAlgHom.fieldRange := by
  intro E _ _ _ H K L _ _ _ _ φ ψ h2 ⟨a, ha⟩ n hn hC
  have hdm := H.d_mod
  have hd0 : 0 < H.d := H.d_prime.pos
  let eK : K ≃ₐ[ℚ] (ψ.comp φ).toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField (ψ.comp φ).toRatAlgHom
  let eL : L ≃ₐ[ℚ] ψ.toRatAlgHom.fieldRange := AlgEquiv.ofInjectiveField ψ.toRatAlgHom
  have heK : ∀ x, ((eK x : (ψ.comp φ).toRatAlgHom.fieldRange) : ℂ) = ψ (φ x) := fun _ => rfl
  have heL : ∀ x, ((eL x : ψ.toRatAlgHom.fieldRange) : ℂ) = ψ x := fun _ => rfl
  have hr0 : H.rt0 ∈ (ψ.comp φ).toRatAlgHom.fieldRange := by
    have h1 : (ψ (φ a)) ^ 2 = H.rt0 ^ 2 := by
      rw [H.sqrt_neg_disc_sq, ← map_pow, ← map_pow, ha]; simp
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h
    · exact ⟨a, h⟩
    · exact ⟨-a, by
        change ψ (φ (-a)) = _
        rw [map_neg, map_neg, h, neg_neg]⟩
  have hle : (ψ.comp φ).toRatAlgHom.fieldRange ≤ ψ.toRatAlgHom.fieldRange := by
    rintro _ ⟨x, rfl⟩
    exact ⟨φ x, rfl⟩
  clear_value eK eL
  generalize (ψ.comp φ).toRatAlgHom.fieldRange = K₀ at eK heK hr0 hle
  generalize ψ.toRatAlgHom.fieldRange = F at eL heL hle ⊢
  have hfK : FiniteDimensional ℚ K₀ := eK.toLinearEquiv.finiteDimensional
  have hfF : FiniteDimensional ℚ F := eL.toLinearEquiv.finiteDimensional
  have hNK : NumberField K₀ := NumberField.mk
  have hNF : NumberField F := NumberField.mk
  replace h2 : Module.finrank ℚ K₀ = 2 := by rw [← eK.toLinearEquiv.finrank_eq, h2]
  have hC' : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion hle).toRingHom n :=
    containsRayField_congr φ _ eK.toRingEquiv eL.toRingEquiv
      (fun x => Subtype.ext ((heK x).trans (heL (φ x)).symm)) n hC
  have hr : (⟨H.rt0, hr0⟩ : K₀) ^ 2 = -(H.d : K₀) := Subtype.ext (by simpa using H.sqrt_neg_disc_sq)
  have hD : discr K₀ = -(H.d : ℤ) := discr_eq_neg_of_sq_eq h2 H.d_prime.squarefree (by omega) hr
  have hTC : IsTotallyComplex K₀ := by
    refine ⟨fun v => ?_⟩
    rw [← InfinitePlace.not_isReal_iff_isComplex]
    intro hv
    have h1 : InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩ ^ 2 = -(H.d : ℝ) := by
      rw [← map_pow, hr, map_neg, map_natCast]
    have h3 : (0 : ℝ) < H.d := by exact_mod_cast hd0
    nlinarith [sq_nonneg (InfinitePlace.embedding_of_isReal hv ⟨H.rt0, hr0⟩)]
  obtain ⟨w, hw, hgen⟩ := exists_integer_generator_of_sq_eq_neg h2 H.d_prime.squarefree (by omega) hr
  let j : K₀ →+* ℂ := algebraMap K₀ ℂ
  have hw' : j w = (1 + H.rt0) / 2 := by
    have := congrArg j hw
    rw [map_mul, map_add, map_one, map_ofNat] at this
    change _ = 1 + H.rt0 at this
    linear_combination this / 2
  have hc : ∀ a b : ℤ, j ((a : 𝓞 K₀) + b * w : 𝓞 K₀) = a + b * ((1 + H.rt0) / 2) := fun a b => by
    rw [← hw']
    simp
  refine ⟨fun P hP => ?_, hle hr0⟩
  have hW := GlobalTheory.T.weberInvariantTorsionValues_subset_of_containsRayField K₀ F hle h2 (by omega) P (fun z => ?_) n hn hC'
  · exact ⟨hW (Set.mem_insert _ _), fun s hs => hW (Set.mem_insert_of_mem _
      ⟨_, (hP _).2 ⟨s, rfl⟩, hs, rfl⟩)⟩
  · rw [hP]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨_, hc s.1 s.2⟩
    · rintro ⟨a, rfl⟩
      obtain ⟨a, b, rfl⟩ := hgen a
      exact ⟨(a, b), hc a b⟩

end GlobalTheory.FieldSize.WeberTransport
end

