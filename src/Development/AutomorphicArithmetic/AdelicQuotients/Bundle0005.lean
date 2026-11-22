import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.SelmerRankBounds.EllipticityFromProductFormula
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Action
import GroundTheory.GlobalFields.IdeleGroups.GaloisOnAdeles.Places
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0002
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.AdelicGLGaloisBaseChangeDiagonalCompat
section
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

private theorem galAd_alg (σ : E ≃ₐ[F] E) (x : E) :
    galAd σ (algebraMap E 𝔸[E] x) = algebraMap E 𝔸[E] (σ x) := by
  have h : (adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] x) = x ⊗ₜ[F] 1 := by
    rw [AlgEquiv.symm_apply_eq, adeleTensorEquiv_tmul, map_one, mul_one]
  change adeleTensorEquiv F E (Algebra.TensorProduct.map (σ : E →ₐ[F] E) (AlgHom.id F 𝔸[F])
    ((adeleTensorEquiv F E).symm (algebraMap E 𝔸[E] x))) = _
  rw [h, Algebra.TensorProduct.map_tmul, adeleTensorEquiv_tmul, map_one, map_one, mul_one]
  rfl

private theorem rat_of_map (a : 𝔸[F]) (x : E) (h : adeleMap F E a = algebraMap E 𝔸[E] x) :
    ∃ y : F, algebraMap F 𝔸[F] y = a := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap F E)
    (LinearMap.ker_eq_bot.2 (algebraMap F E).injective)
  have h1 : φ 1 = 1 := by simpa using LinearMap.congr_fun hφ 1
  have h2 : (1 : E) ⊗ₜ[F] a = x ⊗ₜ[F] (1 : 𝔸[F]) := by
    apply (adeleTensorEquiv F E).injective
    rw [adeleTensorEquiv_tmul, adeleTensorEquiv_tmul, map_one, map_one, one_mul, mul_one, h]
  have h3 := congrArg (fun z => TensorProduct.lid F 𝔸[F] (LinearMap.rTensor 𝔸[F] φ z)) h2
  simp only [LinearMap.rTensor_tmul, TensorProduct.lid_tmul, h1, one_smul] at h3
  exact ⟨φ x, by rw [h3, Algebra.algebraMap_eq_smul_one]⟩

private theorem mat_rat {n : ℕ} (t : AdelicGLn.AdelicGL F n) (h : GL (Fin n) E)
    (e : mapGL n (adeleMap F E) t = AdelicGLn.diagonal E n h) :
    ∃ M : Matrix (Fin n) (Fin n) F, (algebraMap F 𝔸[F]).mapMatrix M = (t : Matrix (Fin n) (Fin n) 𝔸[F]) := by
  have : ∀ i j, ∃ y : F, algebraMap F 𝔸[F] y = (t : Matrix (Fin n) (Fin n) 𝔸[F]) i j := fun i j =>
    rat_of_map _ ((h : Matrix (Fin n) (Fin n) E) i j)
      (congrArg (fun u : AdelicGLn.AdelicGL E n => (u : Matrix (Fin n) (Fin n) 𝔸[E]) i j) e)
  choose M hM using this
  exact ⟨Matrix.of M, Matrix.ext hM⟩
end

theorem UpperTheory.adelicGL_galois_baseChange_diagonal_compat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E ≃ₐ[F] E) (n : ℕ),
        (∀ h : GL (Fin n) E, mapGL n (galAd σ) (AdelicGLn.diagonal E n h) = AdelicGLn.diagonal E n (sigmaGL σ h)) ∧
        (∀ g : GL (Fin n) F, mapGL n (adeleMap F E) (AdelicGLn.diagonal F n g) = AdelicGLn.diagonal E n (incl g)) ∧
        ∀ (t : AdelicGLn.AdelicGL F n) (h : GL (Fin n) E), mapGL n (adeleMap F E) t = AdelicGLn.diagonal E n h →
          ∃ g : GL (Fin n) F, t = AdelicGLn.diagonal F n g := by
  intro F E _ _ _ _ _ σ n
  refine ⟨fun h => ?_, fun g => ?_, fun t h e => ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    exact galAd_alg σ (h.1 i j)
  · refine Units.ext (Matrix.ext fun i j => ?_)
    exact adeleMap_algebraMap (K := F) (L := E) (g.1 i j)
  · obtain ⟨M, hM⟩ := mat_rat t h e
    obtain ⟨N, hN⟩ := mat_rat t⁻¹ h⁻¹ (by rw [map_inv, map_inv, e])
    have hinj : Function.Injective ((algebraMap F 𝔸[F]).mapMatrix : Matrix (Fin n) (Fin n) F →+* _) :=
      Matrix.map_injective (AdeleRing.algebraMap_injective (𝓞 F) F)
    refine ⟨⟨M, N, hinj ?_, hinj ?_⟩, Units.ext hM.symm⟩
    · rw [map_mul, hM, hN, map_one, Units.mul_inv]
    · rw [map_mul, hM, hN, map_one, Units.inv_mul]
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.CharpolyEqOfNormEqOfTwistedConj
section
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.charpoly_eq_of_norm_eq_of_twisted_conj :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ (δ δ' h : GL (Fin n) E) (γ γ' : GL (Fin n) F), normGL σ δ = incl γ → normGL σ δ' = incl γ' →
        δ' = h⁻¹ * δ * sigmaGL σ h → (γ : Matrix (Fin n) (Fin n) F).charpoly = (γ' : Matrix (Fin n) (Fin n) F).charpoly := by
  intro F E _ _ _ _ _ _ σ _ n _ δ δ' h γ γ' hγ hγ' hδ
  have hℓ : σ ^ Module.finrank F E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank F E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have h1 : normGL σ δ' = h⁻¹ * normGL σ δ * h := by
    rw [hδ]
    exact twNorm_twConj_of_pow_eq_one (sigmaGL σ) hθ h δ
  rw [hγ, hγ'] at h1
  have hv : ∀ g : GL (Fin n) F, ((incl g : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      (g : Matrix (Fin n) (Fin n) F).map (algebraMap F E) := fun _ => rfl
  apply Polynomial.map_injective (algebraMap F E) (algebraMap F E).injective
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, ← hv, ← hv, h1, Units.val_mul, Units.val_mul,
    Matrix.coe_units_inv, Matrix.charpoly_units_conj']
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.CharpolyLocalAdelicConjDiagonalEq
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.charpoly_local_adelic_conj_diagonal_eq :
    ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (γ : GL (Fin n) E) (x : AdelicGLn.AdelicGL E n),
        (∀ w : HeightOneSpectrum (𝓞 E), ((finAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x) : GL (Fin n) (w.adicCompletion E)) :
          Matrix (Fin n) (Fin n) (w.adicCompletion E)).charpoly = (γ : Matrix (Fin n) (Fin n) E).charpoly.map (algebraMap E (w.adicCompletion E))) ∧
        ∀ w : InfinitePlace E, ((infAt w (x⁻¹ * AdelicGLn.diagonal E n γ * x) : GL (Fin n) w.Completion) :
          Matrix (Fin n) (Fin n) w.Completion).charpoly = (γ : Matrix (Fin n) (Fin n) E).charpoly.map (algebraMap E w.Completion) := by
  intro E _ _ n γ x
  refine ⟨fun w => ?_, fun w => ?_⟩
  · have h : ((finAt w (AdelicGLn.diagonal E n γ) : GL (Fin n) (w.adicCompletion E)) :
        Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
        (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E (w.adicCompletion E)) := by
      ext a b
      rfl
    rw [finAt_mul, finAt_mul, finAt_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj', h, Matrix.charpoly_map]
  · have h : ((infAt w (AdelicGLn.diagonal E n γ) : GL (Fin n) w.Completion) :
        Matrix (Fin n) (Fin n) w.Completion) =
        (γ : Matrix (Fin n) (Fin n) E).map (algebraMap E w.Completion) := by
      ext a b
      rfl
    rw [infAt_mul, infAt_mul, infAt_inv, Units.val_mul, Units.val_mul, Matrix.coe_units_inv,
      Matrix.charpoly_units_conj', h, Matrix.charpoly_map]
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.EqOneOfSmulPlaceEqOfCompletionMapSurjective
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.eq_one_of_smul_place_eq_of_completionMap_surjective :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : HeightOneSpectrum (𝓞 F)) (w : PlacesOver E q), Function.Surjective (completionMap q w.1) →
        ∀ σ : E ≃ₐ[F] E, σ • w = w → σ = 1 := by
  intro F E _ _ _ _ _ q w hs σ hσ
  have h : w.1 = σ • w.1 := (congrArg Subtype.val hσ).symm
  haveI : w.1.asIdeal.LiesOver q.asIdeal := w.2
  have hid : ∀ y, galHom σ w.1 w.1 h y = y := by
    intro y
    obtain ⟨a, rfl⟩ := hs y
    exact galHom_completionMap q σ w.1 w.1 h a
  refine AlgEquiv.ext fun x ↦ ?_
  have h2 := galHom_algebraMap σ w.1 w.1 h x
  rw [hid] at h2
  exact (algebraMap E (w.1.adicCompletion E)).injective h2.symm
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.ExistsClosedEmbeddingNormOneAdelicGLBaseChange
section
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.exists_closedEmbedding_normOneAdelicGL_baseChange :
    N5 → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∃ j : G1 F n →* G1 E n, Topology.IsClosedEmbedding j ∧
        (∀ t : G1 F n, ((j t : G1 E n) : AdelicGLn.AdelicGL E n) = mapGL n (adeleMap F E) (t : AdelicGLn.AdelicGL F n)) ∧
        ∀ t : AdelicGLn.AdelicGL F n, mapGL n (adeleMap F E) t ∈ normOneGL E n → t ∈ normOneGL F n := by
  intro h5 F E _ _ _ _ _ _ σ hσ n hn
  obtain ⟨hemb, hdet, -⟩ := h5 F E σ hσ n hn
  have hpos : Module.finrank F E ≠ 0 := by
    haveI : FiniteDimensional F E := Module.Finite.right ℚ F E
    exact Module.finrank_pos.ne'
  have key : ∀ t : AdelicGLn.AdelicGL F n,
      mapGL n (adeleMap F E) t ∈ normOneGL E n ↔ t ∈ normOneGL F n := by
    intro t
    rw [mem_normOneGL_iff_detModule, mem_normOneGL_iff_detModule, Subtype.ext_iff, Subtype.ext_iff]
    rw [hdet t]
    exact pow_eq_one_iff_of_nonneg (detModule F n t).2.le hpos
  let j : normOneGL F n →* normOneGL E n :=
    MonoidHom.codRestrict ((mapGL n (adeleMap F E) : AdelicGLn.AdelicGL F n →* AdelicGLn.AdelicGL E n).comp
      (normOneGL F n).subtype) (normOneGL E n) (fun t => (key t.1).2 t.2)
  refine ⟨j, ?_, fun t => rfl, fun t ht => (key t).1 ht⟩
  have hF : Topology.IsClosedEmbedding (Subtype.val : normOneGL F n → AdelicGLn.AdelicGL F n) :=
    (isClosed_normOneGL (K := F) (n := n)).isClosedEmbedding_subtypeVal
  have hE : Topology.IsEmbedding (Subtype.val : normOneGL E n → AdelicGLn.AdelicGL E n) :=
    Topology.IsEmbedding.subtypeVal
  have hc : Topology.IsClosedEmbedding ((Subtype.val : normOneGL E n → AdelicGLn.AdelicGL E n) ∘ j) :=
    hemb.comp hF
  exact Topology.IsClosedEmbedding.of_comp hE hc
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.ExistsCompactConjMemCentralizerMulOfSeparableCha
section
open PositivityTheory.Rg.Tf.Geo

private def piGL {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (g : ∀ w, GL (Fin n) (K w)) :
    GL (Fin n) (∀ w, K w) where
  val := Matrix.of fun i j w => (g w : Matrix (Fin n) (Fin n) (K w)) i j
  inv := Matrix.of fun i j w => ((g w)⁻¹ : GL (Fin n) (K w)).val i j
  val_inv := by
    ext i j w
    have h := congrFun (congrFun (g w).mul_inv i) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [h]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  inv_val := by
    ext i j w
    have h := congrFun (congrFun (g w).inv_mul i) j
    simp only [Matrix.mul_apply, Matrix.of_apply, Finset.sum_apply, Pi.mul_apply] at h ⊢
    rw [h]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

private def prGL {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (w : W) :
    GL (Fin n) (∀ w, K w) →* GL (Fin n) (K w) :=
  Matrix.GeneralLinearGroup.map (Pi.evalRingHom K w)

private theorem prGL_piGL {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (g : ∀ w, GL (Fin n) (K w)) (w : W) :
    prGL K n w (piGL K n g) = g w := by
  ext i j
  rfl

private theorem prGL_ext {W : Type} (K : W → Type) [∀ w, CommRing (K w)] (n : ℕ) (a b : GL (Fin n) (∀ w, K w))
    (h : ∀ w, prGL K n w a = prGL K n w b) : a = b := by
  ext i j w
  exact congrArg (fun g : GL (Fin n) (K w) => (g : Matrix (Fin n) (Fin n) (K w)) i j) (h w)

private theorem prGL_cont {W : Type} (K : W → Type) [∀ w, CommRing (K w)] [∀ w, TopologicalSpace (K w)] (n : ℕ) (w : W) :
    Continuous (prGL K n w) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp
      (Units.continuous_val (M := Matrix (Fin n) (Fin n) (∀ w, K w)))))
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    exact (continuous_apply w).comp ((continuous_apply j).comp ((continuous_apply i).comp
      (Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (∀ w, K w)))))

private theorem piGL_cont {W : Type} (K : W → Type) [∀ w, CommRing (K w)] [∀ w, TopologicalSpace (K w)] (n : ℕ) :
    Continuous (piGL K n) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun w => ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((Units.continuous_val (M := Matrix (Fin n) (Fin n) (K w))).comp (continuous_apply w)))
  · refine continuous_pi fun i => continuous_pi fun j => continuous_pi fun w => ?_
    exact (continuous_apply j).comp ((continuous_apply i).comp
      ((Units.continuous_coe_inv (M := Matrix (Fin n) (Fin n) (K w))).comp (continuous_apply w)))

theorem UpperTheory.exists_compact_conj_mem_centralizer_mul_of_separable_charpoly :
    P1 → ∀ (W : Type) [Finite W] (K : W → Type) [∀ w, NontriviallyNormedField (K w)] [∀ w, LocallyCompactSpace (K w)] [∀ w, CharZero (K w)] (n : ℕ) (γ : GL (Fin n) (∀ w, K w)), (γ : Matrix (Fin n) (Fin n) (∀ w, K w)).charpoly.Separable → ∀ D : Set (GL (Fin n) (∀ w, K w)), IsCompact D → ∃ C : Set (GL (Fin n) (∀ w, K w)), IsCompact C ∧ ∀ x, x⁻¹ * γ * x ∈ D → ∃ t, t * γ = γ * t ∧ ∃ y ∈ C, x = t * y := by
  intro hP W _ K _ _ _ n γ hγ D hD
  have hsep : ∀ w, ((prGL K n w γ : GL (Fin n) (K w)) : Matrix (Fin n) (Fin n) (K w)).charpoly.Separable := by
    intro w
    have h : ((prGL K n w γ : GL (Fin n) (K w)) : Matrix (Fin n) (Fin n) (K w))
        = (γ : Matrix (Fin n) (Fin n) (∀ w, K w)).map (Pi.evalRingHom K w) := rfl
    rw [h, Matrix.charpoly_map]
    exact hγ.map
  choose C hC hCx using fun w => hP (K w) n (prGL K n w γ) (hsep w) (prGL K n w '' D) (hD.image (prGL_cont K n w))
  refine ⟨piGL K n '' Set.pi Set.univ C, (isCompact_univ_pi hC).image (piGL_cont K n), fun x hx => ?_⟩
  choose t ht y hy hxy using fun w => hCx w (prGL K n w x) ⟨_, hx, by simp only [map_mul, map_inv]⟩
  refine ⟨piGL K n t, prGL_ext K n _ _ fun w => ?_, piGL K n y, ⟨y, fun w _ => hy w, rfl⟩, prGL_ext K n _ _ fun w => ?_⟩
  · simp only [map_mul, prGL_piGL, ht w]
  · simp only [map_mul, prGL_piGL, hxy w]
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.ExistsCompactFundamentalSetOfHeightLe
section
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.exists_compact_fundamental_set_of_height_le :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (R : ℝ), ∃ C : Set (G1 K n), IsCompact C ∧
        ∀ x : G1 K n, qht x ≤ R → ∃ g ∈ Gam K n, ∃ y ∈ C, x = g * y := by
  intro K _ _ n R
  obtain ⟨c, N, hc, h⟩ := UpperTheory.adelicNorm_vecMul_ge_of_height K n
  have hR : 0 < max 1 R + 1 := by positivity
  obtain ⟨C, hC, hC'⟩ := Reduction.exists_isCompact_forall_of_pos_le_height (K := K) (n := n)
    (ε := (c * (max 1 R + 1) ^ N)⁻¹) (by positivity)
  refine ⟨Subtype.val ⁻¹' C, isClosed_normOneGL.isClosedEmbedding_subtypeVal.isCompact_preimage hC, fun x hx => ?_⟩
  obtain ⟨γ, hγ⟩ := exists_lt_of_ciInf_lt (hx.trans_lt ((le_max_right 1 R).trans_lt (lt_add_one _)))
  obtain ⟨δ, hδ, y, hy, e⟩ := hC' ((γ : G1 K n) * x : G1 K n) ((γ : G1 K n) * x).2 fun v hv => by
      rw [inv_le_iff_one_le_mul₀' (by positivity)]
      have h0 := h ((γ : G1 K n) * x : G1 K n) v hv
      have hq := AutomorphicForm.height_pos (K := K) ((γ : G1 K n) * x : G1 K n).1
      have hp : 0 ≤ Reduction.height ((γ : G1 K n) * x : G1 K n).1 v := by
        by_contra hn
        have : 0 ≤ c * AutomorphicForm.height (K := K) ((γ : G1 K n) * x : G1 K n).1 ^ N := by
          positivity
        nlinarith [not_le.1 hn]
      exact h0.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hq.le hγ.le N) hc.le) hp)
  let d : G1 K n := ⟨δ, rationalGL_le_normOneGL hδ⟩
  have hd : d ∈ Gam K n := hδ
  refine ⟨(γ : G1 K n)⁻¹ * d, mul_mem (inv_mem γ.2) hd, d⁻¹ * ((γ : G1 K n) * x), ?_, by group⟩
  have e' : δ * y = ((γ : G1 K n) * x : G1 K n).1 := e
  change δ⁻¹ * ((γ : G1 K n) * x : G1 K n).1 ∈ C
  rw [← e', inv_mul_cancel_left]
  exact hy
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.ExistsHeightBoundOfTwistedEllipticSupport
section
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

private theorem finsum_norm_ne_zero {X : Type*} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    (Γ : Subgroup X) [DiscreteTopology Γ] (f : X → ℂ) (hf : HasCompactSupport f) (a b δ : X) (hδ : δ ∈ Γ)
    (h : f (a * δ * b) ≠ 0) : ∑ᶠ γ : Γ, ((‖f (a * γ * b)‖ : ℝ) : ℂ) ≠ 0 := by
  have hc : IsCompact ((fun y => a⁻¹ * y * b⁻¹) '' tsupport f) := hf.isCompact.image (by fun_prop)
  have hfin : ((fun γ : Γ => (γ : X)) ⁻¹' ((fun y => a⁻¹ * y * b⁻¹) '' tsupport f)).Finite := by
    have := Γ.tendsto_coe_cofinite_of_discrete ⟨inferInstance⟩ hc.compl_mem_cocompact
    simpa [Filter.mem_map, Filter.mem_cofinite] using this
  have hs : (Function.support fun γ : Γ => ‖f (a * γ * b)‖).Finite := by
    refine hfin.subset fun γ hγ => ⟨a * γ * b, subset_tsupport _ ?_, by group⟩
    simpa using hγ
  have h1 : ∑ᶠ γ : Γ, ((‖f (a * γ * b)‖ : ℝ) : ℂ) = ((∑ᶠ γ : Γ, ‖f (a * γ * b)‖ : ℝ) : ℂ) :=
    (Complex.ofRealHom.toAddMonoidHom.map_finsum hs).symm
  rw [h1, Complex.ofReal_ne_zero]
  exact (finsum_pos (f := fun γ : Γ => ‖f (a * γ * b)‖) (fun _ => norm_nonneg _) ⟨⟨δ, hδ⟩, norm_pos_iff.2 h⟩ hs).ne'

theorem UpperTheory.exists_height_bound_of_twistedElliptic_support :
    G2 → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ (μ : Measure (G1 E n)) [μ.IsHaarMeasure] (θ : Twist μ), IsGalTwist σ θ →
        ∀ f : CC E n, Ell σ f → ∃ R : ℝ, ∀ x : G1 E n, ∀ δ ∈ Gam E n, f (x⁻¹ * δ * θ.e x) ≠ 0 → qht x ≤ R := by
  intro h2 F E _ _ _ _ _ _ σ hσ n hn μ _ θ hθ f hf
  obtain ⟨C, c, hC⟩ := h2 F E σ hσ n hn
  have hcs : HasCompactSupport (f : G1 E n → ℂ) := f.hasCompactSupport
  obtain ⟨M, hM⟩ := GroundTheory.Automorphic.CuspidalSpectrum.exists_height_le_of_isCompact
    (hcs.isCompact.image (continuous_subtype_val (p := fun g => g ∈ normOneGL E n)))
  let f' : PositivityTheory.Rg.Tf.Core.CC E n :=
    { toFun := fun g => ((‖f g‖ : ℝ) : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp (map_continuous f).norm
      hasCompactSupport' := hcs.comp_left (g := fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) (by simp) }
  have hne : ∀ g, f' g ≠ 0 → f g ≠ 0 := fun g hg h0 => hg (by
    show ((‖f g‖ : ℝ) : ℂ) = 0
    simp [h0])
  refine ⟨C * (max 1 M) ^ c, fun x δ hδ hx => ?_⟩
  refine hC μ θ hθ f' (max 1 M) (le_max_left _ _) (fun g hg => ?_) (fun δ x y hy hg => hf δ x y hy (hne y hg)) x ?_
  · exact (hM _ ⟨g, subset_tsupport _ (hne g hg), rfl⟩).trans (le_max_right _ _)
  · exact finsum_norm_ne_zero (Gam E n) f hcs x⁻¹ (θ.e x) δ hδ hx
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.ExistsIrreducibleCharpolyNormMatchOfTwistedEllip
section
open MeasureTheory NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace GroundTheory.Global GroundTheory.Global.SemiLocal
open GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped ENNReal NumberField.AdeleRing TensorProduct

theorem UpperTheory.exists_irreducible_charpoly_norm_match_of_twistedElliptic :
    N1 → N2 → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsGalois F E] (σ : E ≃ₐ[F] E),
        (∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) → ∀ n : ℕ, 0 < n → ∀ δ : GL (Fin n) E, EllElt σ δ →
        ∃ γ : GL (Fin n) F, Irreducible (γ : Matrix (Fin n) (Fin n) F).charpoly ∧
          ∀ γ' : GL (Fin n) F, (γ' : Matrix (Fin n) (Fin n) F).charpoly = (γ : Matrix (Fin n) (Fin n) F).charpoly →
            (∃ δ' : GL (Fin n) E, normGL σ δ' = incl γ') ∧
            ∀ δ' : GL (Fin n) E, normGL σ δ' = incl γ' → ∃ h : GL (Fin n) E, δ = h⁻¹ * δ' * sigmaGL σ h := by
  intro hN1 hN2 F E _ _ _ _ _ _ σ hgen n _ δ hδ
  obtain ⟨p, hp, hpm⟩ := hδ
  have hℓ : σ ^ Module.finrank F E = 1 := by
    rw [← IsGalois.card_aut_eq_finrank]; exact pow_card_eq_one'
  have hθ : (sigmaGL σ : Monoid.End (GL (Fin n) E)) ^ Module.finrank F E = 1 := by
    rw [← sigmaGL_pow, hℓ, sigmaGL_one]
  have hc : ∀ d h : GL (Fin n) E, normGL σ (h⁻¹ * d * sigmaGL σ h) = h⁻¹ * normGL σ d * h :=
    fun d h => twNorm_twConj_of_pow_eq_one (sigmaGL σ) hθ h d
  have hreg : IsTwRegSemisimple σ δ := by
    unfold IsTwRegSemisimple
    rw [← hpm]
    exact hp.separable.map
  obtain ⟨h, γ, hγ⟩ := hN1 F E σ hgen n δ hreg
  have hv : ((incl γ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F E) := rfl
  have hγp : (γ : Matrix (Fin n) (Fin n) F).charpoly = p := by
    apply Polynomial.map_injective (algebraMap F E) (algebraMap F E).injective
    rw [hpm, ← Matrix.charpoly_map, ← hv, ← hγ, hc, Units.val_mul, Units.val_mul,
      Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  refine ⟨γ, hγp ▸ hp, fun γ' hγ' => ?_⟩
  have hr : IsRegSemisimple γ := by
    unfold IsRegSemisimple
    rw [hγp]; exact hp.separable
  have hr' : IsRegSemisimple γ' := by
    unfold IsRegSemisimple
    rw [hγ', hγp]; exact hp.separable
  obtain ⟨g, hg⟩ := (hN2 F E σ hgen n).2 γ γ' hr hγ'.symm
  have h0 : normGL σ ((incl g : GL (Fin n) E)⁻¹ * (h⁻¹ * δ * sigmaGL σ h) * sigmaGL σ (incl g)) = incl γ' := by
    rw [hc, hγ, hg, map_mul, map_mul, map_inv]
  refine ⟨⟨_, h0⟩, fun δ' hδ' => ?_⟩
  obtain ⟨k, hk⟩ := (hN2 F E σ hgen n).1 δ' _ γ' hr' hδ' h0
  refine ⟨k * (incl g)⁻¹ * h⁻¹, ?_⟩
  rw [map_mul, map_mul, map_inv, map_inv]
  calc δ = h * incl g * ((incl g : GL (Fin n) E)⁻¹ * (h⁻¹ * δ * sigmaGL σ h) * sigmaGL σ (incl g)) *
        (sigmaGL σ (incl g))⁻¹ * (sigmaGL σ h)⁻¹ := by group
    _ = _ := by rw [hk]; group
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.NormAlgebraMapBaseLeOneOfPlacesOver
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

theorem UpperTheory.norm_algebraMap_base_le_one_of_placesOver :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (q : HeightOneSpectrum (𝓞 F)) (w w' : PlacesOver E q) (a : F),
        ‖algebraMap E (w.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 → ‖algebraMap E (w'.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 := by
  intro F E _ _ _ _ _ q w w' a
  have key : ∀ u : PlacesOver E q,
      ‖algebraMap E (u.1.adicCompletion E) (algebraMap F E a)‖ ≤ 1 ↔
        Valued.v (algebraMap F (q.adicCompletion F) a) ≤ 1 := by
    intro u
    rw [Valued.toNormedField.norm_le_one_iff,
      ← IsScalarTower.algebraMap_apply F E (u.1.adicCompletion E),
      ← completionMap_algebraMap q u.1, valued_completionMap]
    exact pow_le_one_iff (Ideal.ramificationIdx_pos u.1.asIdeal (𝓞 F)).ne'
  exact fun h => (key w').2 ((key w).1 h)
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.NormCoeffZeroDvdCharpolyLeAdicCompletion
section
open NumberField IsDedekindDomain Polynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Loc PositivityTheory.Rg.Tf.Geo
open scoped NumberField.AdeleRing

private theorem charpoly_scale {K : Type} [Field K] [Infinite K] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [Polynomial.scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly,
    Matrix.eval_charpoly, ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

private theorem coeff_zero_mem {K : Type} [Field K] (O : ValuationSubring K) {n : ℕ}
    (N : Matrix (Fin n) (Fin n) K) (hN : ∀ i j, N i j ∈ O) (q : K[X]) (hq : q.Monic)
    (hd : q ∣ N.charpoly) : q.coeff 0 ∈ O := by
  let N' : Matrix (Fin n) (Fin n) O := fun i j => ⟨N i j, hN i j⟩
  have hmap : N'.map (algebraMap O K) = N := by
    ext i j
    rfl
  have hd' : q ∣ (N'.charpoly).map (algebraMap O K) := by
    rw [← Matrix.charpoly_map, hmap]
    exact hd
  obtain ⟨g, hg⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd K (Matrix.charpoly_monic N') hd'
  rw [hq.leadingCoeff, map_one, mul_one] at hg
  rw [← hg, coeff_map]
  exact (g.coeff 0).2

theorem UpperTheory.norm_coeff_zero_dvd_charpoly_le_adicCompletion :
    ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (M : Matrix (Fin n) (Fin n) (w.adicCompletion E)) (R : ℝ), 1 ≤ R →
        (∀ i j, ‖M i j‖ ≤ R) → ∀ p : (w.adicCompletion E)[X], p.Monic → p ∣ M.charpoly → ‖p.coeff 0‖ ≤ R ^ n := by
  intro E _ _ w n M R hR hM p hp hd
  classical
  haveI : Infinite (w.adicCompletion E) :=
    Infinite.of_injective _ (algebraMap E (w.adicCompletion E)).injective

  let S : Finset (w.adicCompletion E) :=
    insert 1 (Finset.univ.image fun ij : Fin n × Fin n => M ij.1 ij.2)
  obtain ⟨c, hcS, hcmax⟩ := Finset.exists_max_image S (fun x => ‖x‖) ⟨1, Finset.mem_insert_self _ _⟩
  have hc1 : 1 ≤ ‖c‖ := by
    have := hcmax 1 (Finset.mem_insert_self _ _)
    simpa using this
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp at hc1
    linarith
  have hcR : ‖c‖ ≤ R := by
    rcases Finset.mem_insert.1 hcS with rfl | h
    · simpa using hR
    · obtain ⟨ij, -, rfl⟩ := Finset.mem_image.1 h
      exact hM _ _
  have hent : ∀ i j, ‖M i j‖ ≤ ‖c‖ := fun i j =>
    hcmax _ (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩))
  have hinv : c⁻¹ ≠ 0 := inv_ne_zero hc0
  have hint : ∀ x : w.adicCompletion E, ‖x‖ ≤ 1 → x ∈ w.adicCompletionIntegers E := fun x hx =>
    (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).2 (Valued.toNormedField.norm_le_one_iff.1 hx)
  have hint' : ∀ x : w.adicCompletion E, x ∈ w.adicCompletionIntegers E → ‖x‖ ≤ 1 := fun x hx =>
    Valued.toNormedField.norm_le_one_iff.2 ((HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 E) E w).1 hx)
  have hN : ∀ i j, (c⁻¹ • M) i j ∈ w.adicCompletionIntegers E := by
    intro i j
    apply hint
    rw [Matrix.smul_apply, smul_eq_mul, norm_mul, norm_inv]
    exact inv_mul_le_one_of_le₀ (hent i j) (norm_nonneg _)
  have hq : (p.scaleRoots c⁻¹).Monic := (Polynomial.monic_scaleRoots_iff _).2 hp
  have hdq : p.scaleRoots c⁻¹ ∣ (c⁻¹ • M).charpoly := by
    rw [charpoly_scale M hinv]
    obtain ⟨r, hr⟩ := hd
    rw [hr, Polynomial.mul_scaleRoots_of_noZeroDivisors]
    exact dvd_mul_right _ _
  have hmem := hint' _ (coeff_zero_mem _ _ hN _ hq hdq)
  rw [Polynomial.coeff_scaleRoots, Nat.sub_zero, norm_mul, norm_pow, norm_inv, inv_pow] at hmem
  have hcpos : 0 < ‖c‖ ^ p.natDegree := by positivity
  have h1 : ‖p.coeff 0‖ ≤ ‖c‖ ^ p.natDegree := by
    rwa [← div_eq_mul_inv, div_le_one hcpos] at hmem
  have hdeg : p.natDegree ≤ n := by
    have := Polynomial.natDegree_le_of_dvd hd (Matrix.charpoly_monic M).ne_zero
    simpa [Matrix.charpoly_natDegree_eq_dim] using this
  calc ‖p.coeff 0‖ ≤ ‖c‖ ^ p.natDegree := h1
    _ ≤ R ^ p.natDegree := pow_le_pow_left₀ (norm_nonneg _) hcR _
    _ ≤ R ^ n := pow_le_pow_right₀ hR hdeg
end

