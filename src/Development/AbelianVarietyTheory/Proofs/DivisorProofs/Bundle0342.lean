import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0315
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0300

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleQuasiSectionOfSmoothSchemeHom
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory

open Polynomial in

theorem exists_etale_subset_range_of_isPrime {A : Type} [CommRing A] (q : Ideal A) [q.IsPrime]
    {K : Type} [Field K] [Algebra A K] [Algebra q.ResidueField K]
    [IsScalarTower A q.ResidueField K] [Algebra.IsSeparable q.ResidueField K]
    {ι : Type} [Finite ι] (b : ι → K) :
    ∃ (E : Type) (_ : CommRing E) (_ : Algebra A E) (_ : Algebra.Etale A E) (ε : E →ₐ[A] K),
      ∀ i, b i ∈ Set.range ε := by
  classical
  let k := q.ResidueField
  let L := IntermediateField.adjoin k (Set.range b)
  have : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element k L
  have hi : IsIntegral k θ := Algebra.IsIntegral.isIntegral θ
  have hr : ∀ i, ∃ r : k[X], aeval θ r = (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) := by
    intro i
    have h₁ : (⟨b i, IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩⟩ : L) ∈ Algebra.adjoin k {θ} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hi.isAlgebraic, hθ]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at h₁
    obtain ⟨g, hg⟩ := h₁
    exact ⟨g, hg⟩
  choose r hr using hr
  have := Fintype.ofFinite ι
  let T : Finset k := (minpoly k θ).coeffs ∪ Finset.univ.biUnion fun i => (r i).coeffs
  obtain ⟨⟨d, hd⟩, hdT⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (A ⧸ q)) T
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective d
  have hs : algebraMap A k s ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply A (A ⧸ q) k]
    exact (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hd)
  let As := Localization.Away s
  let ρ : As →+* k := IsLocalization.Away.lift s (Ne.isUnit hs)
  have hρ : ∀ a : A, ρ (algebraMap A As a) = algebraMap A k a := IsLocalization.Away.lift_eq s _
  letI : Algebra As k := ρ.toAlgebra
  letI : Algebra As K := ((algebraMap k K).comp ρ).toAlgebra
  have : IsScalarTower As k K := .of_algebraMap_eq' rfl
  have : IsScalarTower A As K := .of_algebraMap_eq fun a => by
    change algebraMap A K a = algebraMap k K (ρ (algebraMap A As a))
    rw [hρ, ← IsScalarTower.algebraMap_apply]
  have hT : ∀ c ∈ T, c ∈ Set.range ρ := by
    intro c hc
    obtain ⟨a, ha⟩ := hdT c hc
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    refine ⟨IsLocalization.mk' As a (⟨s, 1, by simp⟩ : Submonoid.powers s), ?_⟩
    have e1 : ρ (IsLocalization.mk' As a (⟨s, 1, by simp⟩ : Submonoid.powers s)) * algebraMap A k s =
        algebraMap A k a := by
      rw [← hρ, ← hρ, ← map_mul, IsLocalization.mk'_spec]
    have e2 : c * algebraMap A k s = algebraMap A k a := by
      rw [IsScalarTower.algebraMap_apply A (A ⧸ q) k s, IsScalarTower.algebraMap_apply A (A ⧸ q) k a]
      erw [ha]
      rw [Algebra.smul_def, mul_comm]
      rfl
    exact mul_right_cancel₀ hs (e1.trans e2.symm)
  have hlift : ∀ g : k[X], (∀ c ∈ g.coeffs, c ∈ Set.range ρ) → ∃ g' : As[X], g'.map ρ = g := by
    intro g hg
    rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
    intro n
    by_cases h : g.coeff n = 0
    · exact ⟨0, by simp [h]⟩
    · exact hg _ (Polynomial.coeff_mem_coeffs h)
  obtain ⟨μ, hμ, -, hμm⟩ := lifts_and_natDegree_eq_and_monic (f := algebraMap As k)
    (p := minpoly k θ) (Polynomial.mem_lifts _ |>.mpr
      (hlift _ fun c hc => hT c (Finset.mem_union_left _ hc))) (minpoly.monic hi)
  let P : StandardEtalePair As := ⟨μ, hμm, derivative μ, 1, 0, 1, by simp⟩
  have key : ∀ g : As[X], aeval (θ : K) g = (aeval θ (g.map (algebraMap As k)) : L) := fun g => by
    rw [← aeval_map_algebraMap k]
    exact aeval_algHom_apply L.val θ _
  have hP : P.HasMap (θ : K) := by
    refine ⟨by rw [key, hμ, minpoly.aeval]; rfl, Ne.isUnit ?_⟩
    rw [key, ← derivative_map, hμ]
    exact fun h => (Algebra.IsSeparable.isSeparable k θ).aeval_derivative_ne_zero
      (minpoly.aeval k θ) (Subtype.ext h)
  let ε₀ : P.Ring →ₐ[As] K := P.lift _ hP
  letI : Algebra A P.Ring := ((algebraMap As P.Ring).comp (algebraMap A As)).toAlgebra
  have : IsScalarTower A As P.Ring := .of_algebraMap_eq' rfl
  refine ⟨P.Ring, inferInstance, inferInstance, Algebra.Etale.comp A As P.Ring,
    ε₀.restrictScalars A, fun i => ?_⟩
  obtain ⟨g, hg⟩ := hlift (r i) fun c hc =>
    hT c (Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hc⟩))
  refine ⟨aeval P.X g, ?_⟩
  change ε₀ (aeval P.X g) = b i
  rw [← aeval_algHom_apply, StandardEtalePair.lift_X, key]
  change ((aeval θ (g.map ρ) : L) : K) = b i
  rw [hg, hr i]

theorem exists_etale_prime_of_smooth {A C : Type} [CommRing A] [CommRing C] [Algebra A C]
    [Algebra.Smooth A C] (p : Ideal C) [p.IsPrime] :
    ∃ (W : Type) (_ : CommRing W) (_ : Algebra A W) (_ : Algebra.Etale A W) (_ : C →ₐ[A] W)
      (P : Ideal W), P.IsPrime ∧ P.comap (algebraMap A W) = p.comap (algebraMap A C) := by
  set q := p.comap (algebraMap A C) with hq
  let K := SeparableClosure q.ResidueField
  letI : Algebra A K := ((algebraMap q.ResidueField K).comp (algebraMap A q.ResidueField)).toAlgebra
  have : IsScalarTower A q.ResidueField K := .of_algebraMap_eq' rfl
  have hker : RingHom.ker (algebraMap A K) = q := by
    rw [IsScalarTower.algebraMap_eq A q.ResidueField K, ← RingHom.comap_ker,
      (RingHom.injective_iff_ker_eq_bot _).mp (algebraMap q.ResidueField K).injective]
    exact Ideal.ker_algebraMap_residueField q
  obtain ⟨φ⟩ := nonempty_algHom_of_smooth_of_isSepClosed (R := A) (K := K) p hker.symm
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime _
  obtain ⟨f, hf, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := A)
    (p := RingHom.ker φ)
  let S := Localization.Away f
  let P := MvPolynomial (Fin n) A
  let φ' : S →ₐ[A] K := IsLocalization.Away.liftAlgHom f (Ne.isUnit hf)
  obtain ⟨E, _, _, _, ε, hε⟩ := exists_etale_subset_range_of_isPrime q
    fun i : Fin n => φ' (algebraMap P S (MvPolynomial.X i))
  choose c hc using hε
  let χ : P →ₐ[A] K := φ'.comp (IsScalarTower.toAlgHom A _ _)
  have hχ : ε.comp (MvPolynomial.aeval c) = χ := by
    refine MvPolynomial.algHom_ext fun i => ?_
    exact (congrArg ε (MvPolynomial.aeval_X (R := A) c i)).trans (hc i)
  letI := (MvPolynomial.aeval (R := A) c).toAlgebra
  have : IsScalarTower A P E := .of_algebraMap_eq fun r => ((MvPolynomial.aeval (R := A) c).commutes r).symm
  letI := χ.toAlgebra
  letI := ε.toAlgebra
  have : IsScalarTower A E K := .of_algebraMap_eq fun r => (ε.commutes r).symm
  have : IsScalarTower P E K := .of_algebraMap_eq fun r => congr($hχ r).symm
  let φ'' : S →ₐ[P] K := ⟨φ', fun r => rfl⟩
  let W := E ⊗[P] S
  let ε' : W →ₐ[E] K := Algebra.TensorProduct.lift (Algebra.ofId E K) φ'' fun _ _ => .all _ _
  have hcomm : ∀ r : A, (1 : E) ⊗ₜ[P] algebraMap A S r = algebraMap A W r := fun r => by
    change (1 : E) ⊗ₜ[P] algebraMap A S r = (algebraMap A E r) ⊗ₜ[P] (1 : S)
    rw [IsScalarTower.algebraMap_apply A P S, IsScalarTower.algebraMap_apply A P E]
    exact (Algebra.TensorProduct.tmul_one_eq_one_tmul _).symm
  refine ⟨W, inferInstance, inferInstance, Algebra.Etale.comp A E W,
    ⟨(Algebra.TensorProduct.includeRight (R := P) (A := E) (B := S)).toRingHom.comp
      (algebraMap C S), fun r => ?_⟩, RingHom.ker ε', RingHom.ker_isPrime _, ?_⟩
  · change (1 : E) ⊗ₜ[P] algebraMap C S (algebraMap A C r) = algebraMap A W r
    rw [← IsScalarTower.algebraMap_apply]
    exact hcomm r
  · ext r
    rw [Ideal.mem_comap, RingHom.mem_ker,
      show ε' (algebraMap A W r) = algebraMap A K r from (ε'.restrictScalars A).commutes r,
      ← RingHom.mem_ker, hker]

theorem exists_etale_quasiSection_of_smooth : ∀ {Y X : Scheme.{0}} (f : Y ⟶ X) [Smooth f] (x : X),
    x ∈ Set.range f → ∃ (V : Scheme.{0}) (s : V ⟶ Y), Etale (s ≫ f) ∧ x ∈ Set.range (s ≫ f) := by
  intro Y X f _ x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨U, V, hU, hV, hVU, -, hyV⟩ := exists_isAffineOpen_pair f y (O := ⊤) trivial
  obtain ⟨p, rfl⟩ : y ∈ Set.range hV.fromSpec := by rwa [hV.range_fromSpec]
  have := f.smooth_appLE hU hV hVU
  have := p.isPrime
  algebraize [(f.appLE U V hVU).hom]
  obtain ⟨W, _, _, _, ψ, P, hP, hPq⟩ :=
    exists_etale_prime_of_smooth (A := Γ(X, U)) (C := Γ(Y, V)) p.asIdeal
  have hs : (Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W)) ≫ hU.fromSpec := by
    rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc]
    congr 2
    ext a
    exact ψ.commutes a
  have : Etale (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W))) :=
    HasRingHomProperty.Spec_iff.mpr (RingHom.etale_algebraMap.mpr ‹_›)
  refine ⟨Spec (.of W), Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hV.fromSpec, ?_, ⟨⟨P, hP⟩, ?_⟩⟩
  · rw [hs]
    infer_instance
  have e : Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) W)) ⟨P, hP⟩ =
      Spec.map (f.appLE U V hVU) p := PrimeSpectrum.ext hPq
  rw [hs]
  exact (congrArg hU.fromSpec e).trans congr($(hU.SpecMap_appLE_fromSpec f hV hVU) p)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGLDiagonalCongruentHermitianStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_GL_diagonal_congruent_hermitian : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (b : Matrix ν ν E), (b.map c)ᵀ = b → b.det ≠ 0 → ∃ (a : GL ν E) (D : ν → Fˣ), b = (a : Matrix ν ν E) * diagonal (fun j => algebraMap F E (D j)) * ((a : Matrix ν ν E).map c)ᵀ := by
  first | exact @GlobalTheory.KSp.exists_gl_diagonal_hermitian | exact GlobalTheory.KSp.exists_gl_diagonal_hermitian | (intros; apply GlobalTheory.KSp.exists_gl_diagonal_hermitian <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericJacobianDataIteratedStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_jacobian_data_iterated_alt : ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsRegularRing Λ] [PerfectField (FractionRing Λ)] (σ τ : Type) [Finite σ] [Finite τ] (Q : Ideal (MvPolynomial τ (MvPolynomial σ Λ))) [Q.IsPrime], (∀ a : Λ, MvPolynomial.C (MvPolynomial.C a) ∈ Q → a = 0) → ∀ d : τ ⊕ σ → Derivation ℤ (MvPolynomial τ (MvPolynomial σ Λ)) (MvPolynomial τ (MvPolynomial σ Λ)), (∀ t x, d (Sum.inl t) x = MvPolynomial.pderiv t x) → (∀ s x, d (Sum.inr s) (MvPolynomial.C x) = MvPolynomial.C (MvPolynomial.pderiv s x)) → (∀ s t, d (Sum.inr s) (MvPolynomial.X t) = 0) → ∃ (h : ℕ) (f : Fin h → MvPolynomial τ (MvPolynomial σ Λ)) (s : Fin h → τ ⊕ σ) (g : MvPolynomial τ (MvPolynomial σ Λ)), g ∉ Q ∧ (∀ j, f j ∈ Q) ∧ (∀ x ∈ Q, g * x ∈ Ideal.span (Set.range f)) ∧ (Matrix.of fun i j => d (s i) (f j)).det ∉ Q := by
  first | exact @GlobalTheory.exists_generic_jacobian_data_iterated | exact GlobalTheory.exists_generic_jacobian_data_iterated | (intros; apply GlobalTheory.exists_generic_jacobian_data_iterated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianSplitUnitaryLowerBlockInvertibleStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_splitUnitary_lowerBlock_invertible : ∀ (F : Type) [Field F] [CharZero F] (E : Type) [Field E] [Algebra F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (g : UG c (stdJ ν E)), ∃ t : Matrix ν ν E, (t.map c)ᵀ = t ∧ ((mat c g).toBlocks₂₁ + (mat c g).toBlocks₂₂ * t).det ≠ 0 := by
  first | exact @GlobalTheory.KSp.exists_herm_transverse | exact GlobalTheory.KSp.exists_herm_transverse | (intros; apply GlobalTheory.KSp.exists_herm_transverse <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicParamOfDegZeroCompatibleStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_param_of_degZero_compatible : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ G : C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) → ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p := by
  first | exact @GlobalTheory.AnPer.Charts.exists_param_of_deg_zero | exact GlobalTheory.AnPer.Charts.exists_param_of_deg_zero | (intros; apply GlobalTheory.AnPer.Charts.exists_param_of_deg_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfBigCellGenericRelationsStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_of_bigCell_generic_relations : ∀ (G H : Type) [Group G] [Group H] (P : Subgroup G) (w : G) (ρ : P →* H) (W : H), (∀ p q : P, w * p = q * w → W * ρ p = ρ q * W) → (∀ p : P, (∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂) → ∃ p₁ p₂ : P, w * p * w = p₁ * w * p₂ ∧ W * ρ p * W = ρ p₁ * W * ρ p₂) → (∀ s : Finset G, ∃ u : G, ∀ g ∈ s, ∃ p₁ p₂ : P, g * u = p₁ * w * p₂) → ∃ Φ : G →* H, (∀ p : P, Φ p = ρ p) ∧ Φ w = W := by
  first | exact @GlobalTheory.bigCell_hom | exact GlobalTheory.bigCell_hom | (intros; apply GlobalTheory.bigCell_hom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralClosedBallAddCharEqZeroStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_closedBall_addChar_eq_zero : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (lam : Measure F) [lam.IsAddHaarMeasure] (ψ : AddChar F ℂ) (hψ : Continuous ψ) (_ : ∀ t, ‖ψ t‖ = 1) (_ : ψ ≠ 1), ∃ s₀ : Fˣ, ∀ s : Fˣ, (s₀ : F) ∈ GlobalTheory.SplitWeil.cball s → ∫ x in GlobalTheory.SplitWeil.cball s, ψ x ∂lam = 0 := by
  first | exact @GlobalTheory.KSp.exists_integral_cball_char_eq_zero | exact GlobalTheory.KSp.exists_integral_cball_char_eq_zero | (intros; apply GlobalTheory.KSp.exists_integral_cball_char_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsColimitPushoutUnder
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.BaseChangeColim

variable {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) (j : J) {B' : CommRingCat.{0}}
  (g' : D.obj j ⟶ B')

noncomputable def mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout g' (D.map k.hom) ⟶ pushout g' (D.map k'.hom) :=
  pushout.desc (pushout.inl g' (D.map k'.hom)) (D.map f.right ≫ pushout.inr g' (D.map k'.hom))
    (by rw [pushout.condition, ← Category.assoc, ← D.map_comp, Under.w f])

@[reassoc]
lemma inl_mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout.inl g' (D.map k.hom) ≫ mapPush D j g' f = pushout.inl g' (D.map k'.hom) :=
  pushout.inl_desc _ _ _

@[reassoc]
lemma inr_mapPush {k k' : Under j} (f : k ⟶ k') :
    pushout.inr g' (D.map k.hom) ≫ mapPush D j g' f = D.map f.right ≫ pushout.inr g' (D.map k'.hom) :=
  pushout.inr_desc _ _ _

@[simps]
noncomputable def diag : Under j ⥤ CommRingCat.{0} where
  obj k := pushout g' (D.map k.hom)
  map f := mapPush D j g' f
  map_id k := by
    apply pushout.hom_ext
    · rw [inl_mapPush, Category.comp_id]
    · rw [inr_mapPush, Category.comp_id, Under.id_right, D.map_id, Category.id_comp]
  map_comp f f' := by
    apply pushout.hom_ext
    · rw [inl_mapPush, inl_mapPush_assoc, inl_mapPush]
    · rw [inr_mapPush, inr_mapPush_assoc, inr_mapPush, Under.comp_right, D.map_comp,
        Category.assoc]

noncomputable def inrNat : Under.forget j ⋙ D ⟶ diag D j g' where
  app k := pushout.inr g' (D.map k.hom)
  naturality k k' f := by
    show D.map f.right ≫ pushout.inr g' (D.map k'.hom) = pushout.inr g' (D.map k.hom) ≫ mapPush D j g' f
    rw [inr_mapPush]

noncomputable def inlNat : (Functor.const _).obj B' ⟶ diag D j g' where
  app k := pushout.inl g' (D.map k.hom)
  naturality k k' f := by
    show 𝟙 B' ≫ pushout.inl g' (D.map k'.hom) = pushout.inl g' (D.map k.hom) ≫ mapPush D j g' f
    rw [inl_mapPush, Category.id_comp]

noncomputable def toB (c : Cocone D) {B : CommRingCat.{0}} (h : B' ⟶ B) (g : c.pt ⟶ B)
    (sq : g' ≫ h = c.ι.app j ≫ g) : diag D j g' ⟶ (Functor.const _).obj B where
  app k := pushout.desc h (c.ι.app k.right ≫ g) (by rw [sq, ← c.w k.hom, Category.assoc])
  naturality k k' f := by
    show mapPush D j g' f ≫ pushout.desc h (c.ι.app k'.right ≫ g) _ =
      pushout.desc h (c.ι.app k.right ≫ g) _ ≫ 𝟙 B
    apply pushout.hom_ext
    · rw [inl_mapPush_assoc, pushout.inl_desc, pushout.inl_desc_assoc, Category.comp_id]
    · rw [inr_mapPush_assoc, pushout.inr_desc, pushout.inr_desc_assoc, Category.comp_id,
        ← Category.assoc, c.w]

theorem exists_isColimit_pushout_under : ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D), IsColimit c → ∀ (j : J) (B' B : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B) (g : c.pt ⟶ B), IsPushout g' (c.ι.app j) h g → ∃ (D' : Under j ⥤ CommRingCat.{0}) (ι : D' ⟶ (Functor.const _).obj B) (u : Under.forget j ⋙ D ⟶ D') (v : (Functor.const _).obj B' ⟶ D'), Nonempty (IsColimit (Cocone.mk B ι)) ∧ ∀ k : Under j, IsPushout g' (D.map k.hom) (v.app k) (u.app k) ∧ v.app k ≫ ι.app k = h ∧ u.app k ≫ ι.app k = c.ι.app k.right ≫ g := by
  intro J _ _ D c hc j B' B g' h g hsq
  refine ⟨diag D j g', toB D j g' c h g hsq.w, inrNat D j g', inlNat D j g', ⟨?_⟩,
    fun k => ⟨IsPushout.of_hasPushout _ _, pushout.inl_desc _ _ _, pushout.inr_desc _ _ _⟩⟩
  have hc' : IsColimit (c.whisker (Under.forget j)) :=
    (Functor.Final.isColimitWhiskerEquiv _ _).symm hc
  let k0 : Under j := Under.mk (𝟙 j)

  let e : ∀ (s : Cocone (diag D j g')) (k : Under j), pushout g' (D.map k.hom) ⟶ s.pt :=
    fun s k => s.ι.app k
  have he : ∀ (s : Cocone (diag D j g')) {k k' : Under j} (f : k ⟶ k'),
      mapPush D j g' f ≫ e s k' = e s k := fun s _ _ f => s.w f
  let r : Cocone (diag D j g') → Cocone (Under.forget j ⋙ D) := fun s =>
    { pt := s.pt, ι := inrNat D j g' ≫ s.ι }
  have hl : ∀ (s : Cocone (diag D j g')) (k : Under j),
      pushout.inl g' (D.map k.hom) ≫ e s k = pushout.inl g' (D.map k0.hom) ≫ e s k0 := by
    intro s k
    rw [← he s (Under.homMk k.hom (Category.id_comp k.hom) : k0 ⟶ k), inl_mapPush_assoc]
  have hfr : ∀ (s : Cocone (diag D j g')) (k : Under j),
      c.ι.app k.right ≫ hc'.desc (r s) = pushout.inr g' (D.map k.hom) ≫ e s k :=
    fun s k => hc'.fac (r s) k
  have hw : ∀ s : Cocone (diag D j g'),
      g' ≫ (pushout.inl g' (D.map k0.hom) ≫ e s k0) = c.ι.app j ≫ hc'.desc (r s) := by
    intro s
    rw [show c.ι.app j = c.ι.app k0.right from rfl, hfr, ← Category.assoc, pushout.condition,
      Category.assoc]
    exact (congrArg (· ≫ (pushout.inr g' (D.map k0.hom) ≫ e s k0)) (D.map_id j)).trans
      (Category.id_comp _)
  exact
    { desc := fun s => hsq.desc _ _ (hw s)
      fac := fun s k => by
        change pushout.desc _ _ _ ≫ _ = e s k
        apply pushout.hom_ext
        · rw [pushout.inl_desc_assoc, hsq.inl_desc, hl s k]
        · rw [pushout.inr_desc_assoc, Category.assoc, hsq.inr_desc, hfr]
      uniq := fun s m hm => by
        have hm' : ∀ k : Under j, pushout.desc h (c.ι.app k.right ≫ g)
            (by rw [hsq.w, ← c.w k.hom, Category.assoc]) ≫ m = e s k := hm
        apply hsq.hom_ext
        · rw [hsq.inl_desc, ← hm' k0, pushout.inl_desc_assoc]
        · rw [hsq.inr_desc]
          apply hc'.hom_ext
          intro k
          change c.ι.app k.right ≫ g ≫ m = c.ι.app k.right ≫ hc'.desc (r s)
          rw [hfr, ← hm' k, pushout.inr_desc_assoc, Category.assoc] }

end GlobalTheory.BaseChangeColim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsModelOfUnitaryStatement
section
open GlobalTheory.UnitLemma Polynomial Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isModel_of_unitary_charpoly_eq : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E), (γ.map K.c)ᵀ * γ = 1 → B.g * B.σ B.g = 1 → B.P.Separable → γ.charpoly = B.P → ∃ (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by
  first | exact @GlobalTheory.InertUnitOrb.exists_isModel_of_unitary | exact GlobalTheory.InertUnitOrb.exists_isModel_of_unitary | (intros; apply GlobalTheory.InertUnitOrb.exists_isModel_of_unitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicGraphUnitaryIsUnitLowerBlock
section
open scoped Matrix

namespace GlobalTheory

theorem exists_isotropic_graph_isUnit_lowerRow : ∀ (O : Type) [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    (∃ x : O, IsUnit (c x - x)) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) O), (∀ i j, c (J j i) = J i j) → IsUnit J.det →
    ∀ g : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) O, IsUnit g.det →
      gᵀ * Matrix.fromBlocks 0 J J 0 * g.map c = Matrix.fromBlocks 0 J J 0 →
      ∃ Z : Matrix (Fin n) (Fin n) O, Zᵀ * J + J * Z.map c = 0 ∧ IsUnit (g.toBlocks₂₁ * Z + g.toBlocks₂₂).det := by
  have hfield := GlobalTheory.T.exists_isotropic_graph_det_ne_zero
  have hlift := GlobalTheory.T.exists_skew_lift_mod_maximalIdeal

  intro O _ _ c hc h2 hx0 n J hJ hJdet g hg hgu
  obtain ⟨x, hx⟩ := hx0
  haveI : IsLocalHom c := ⟨fun a ha => by simpa [hc] using ha.map c⟩
  set π := IsLocalRing.residue O with hπ
  set σ : IsLocalRing.ResidueField O →+* IsLocalRing.ResidueField O := IsLocalRing.ResidueField.map c with hσ
  have hσπ : ∀ a, σ (π a) = π (c a) := fun a => IsLocalRing.ResidueField.map_residue c a
  have hσσ : ∀ y, σ (σ y) = y := by
    intro y; obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y; rw [hσπ, hσπ, hc]
  have hε : ∃ ε, ε ≠ 0 ∧ σ ε = -ε := ⟨π (c x - x), (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hx, by
    rw [hσπ, map_sub, hc, ← neg_sub, map_neg]⟩
  have hmapc : ∀ {m : Type} (M : Matrix m m O), (M.map c).map π = (M.map π).map σ := by
    intro m M; ext i j; simp [hσπ]
  have hJ' : ∀ i j, σ (J.map π j i) = J.map π i j := by intro i j; simp [hσπ, hJ]
  have hJdet' : (J.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hJdet
  have hg' : (g.map π).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]; exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hg
  have hgu' : (g.map π)ᵀ * Matrix.fromBlocks 0 (J.map π) (J.map π) 0 * (g.map π).map σ
      = Matrix.fromBlocks 0 (J.map π) (J.map π) 0 := by
    have := congrArg (fun M => M.map π) hgu
    simpa only [Matrix.map_mul, Matrix.transpose_map, hmapc, Matrix.fromBlocks_map,
      Matrix.map_zero _ (map_zero π)] using this
  obtain ⟨Zb, hZb, hdet⟩ := hfield _ σ hσσ hε n _ hJ' hJdet' _ hg' hgu'
  obtain ⟨Z₀, hZ₀⟩ : ∃ Z₀ : Matrix (Fin n) (Fin n) O, Z₀.map π = Zb :=
    ⟨fun i j => (IsLocalRing.residue_surjective (Zb i j)).choose, by
      ext i j; exact (IsLocalRing.residue_surjective (Zb i j)).choose_spec⟩
  have hZ₀m : ∀ i j, (Z₀ᵀ * J + J * Z₀.map c) i j ∈ IsLocalRing.maximalIdeal O := by
    intro i j
    rw [← IsLocalRing.residue_eq_zero_iff]
    have := congrArg (fun M => M i j) hZb
    simp only [Matrix.zero_apply] at this
    rw [← this, ← hZ₀, ← hmapc, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add _ (map_add π)]
    rfl
  obtain ⟨Z, hZ, hZm⟩ := hlift O c hc h2 n J hJ hJdet Z₀ hZ₀m
  refine ⟨Z, hZ, ?_⟩
  have hZπ : Z.map π = Zb := by
    rw [← hZ₀]; ext i j
    simp only [Matrix.map_apply]
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]; exact hZm i j
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← hπ, RingHom.map_det, RingHom.mapMatrix_apply,
    Matrix.map_add _ (map_add π), Matrix.map_mul, hZπ]
  exact hdet

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJetMorphismExtendingTranslation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace

namespace GlobalTheory.AnPer.Charts

theorem tsze_expand_fst_snd {g : ℕ} {O : Type} [CommRing O] (h : O) (v : Fin g → O) :
    (TrivSqZeroExt.inl h + ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) :
        TrivSqZeroExt O (Fin g → O)).fst = h ∧
    ∀ b, (TrivSqZeroExt.inl h + ∑ a, TrivSqZeroExt.inl (v a) * TrivSqZeroExt.inr (Pi.single a (1 : O)) :
        TrivSqZeroExt O (Fin g → O)).snd b = v b := by
  rw [← tsze_expand]
  exact ⟨by simp, fun b ↦ by simp⟩

theorem jet_sh : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {l : Λ}
    {k k' : K.K} (e : K.le l k' k), ∃ χ : K.jet k ⟶ K.jet k', χ.deg = l ∧
      jet0 k ≫ χ = ptHom (K.triv k') e ≫ jet0 k' ∧ jet1 k ≫ χ = ptHom (K.triv k') e ≫ jet1 k' ∧
      ∀ x : TrivSqZeroExt (Hol (K.W k)) (Fin g → Hol (K.W k)),
        (TrivSqZeroExt.fst (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) = sh e x.fst) ∧
        ∀ a, TrivSqZeroExt.snd (R := Hol (K.W k')) (M := Fin g → Hol (K.W k')) (χ.φ x) a = sh e (x.snd a) := by
  intro I _ g Λ _ F K l k k' e
  have hf1 : ∀ y : Hol (K.W k), (ptHom (K.triv k') e ≫ jet0 k').φ y = TrivSqZeroExt.inl (sh e y) := fun y ↦ by
    change TrivSqZeroExt.inl (sh (K.le_refl k') (sh e y)) = _
    rw [sh_refl]
  have hf2 : ∀ y : Hol (K.W k), (ptHom (K.triv k') e ≫ jet1 k').φ y =
      TrivSqZeroExt.inl (sh e y) + TrivSqZeroExt.inr (fun a ↦ dw a (sh e y)) := fun y ↦ rfl
  obtain ⟨χ, hdeg, h0, h1, hφ⟩ := GlobalTheory.T.exists_jet_extension_square_zero K (T := K.jet k') (ptHom (K.triv k') e ≫ jet0 k')
    (ptHom (K.triv k') e ≫ jet1 k') (fun a ↦ TrivSqZeroExt.inr (Pi.single a 1)) rfl (fun _ ↦ rfl)
    (fun a b ↦ TrivSqZeroExt.inr_mul_inr _ _ _) (fun x ↦ by
      rw [hf2, hf1]
      simp only [hf1]
      rw [tsze_expand]
      simp only [dw_sh])
  refine ⟨χ, hdeg.trans (add_zero l), h0, h1, fun x ↦ ?_⟩
  have hx : χ.φ x = TrivSqZeroExt.inl (sh e x.fst) +
      ∑ a, TrivSqZeroExt.inl (sh e (x.snd a)) * TrivSqZeroExt.inr (Pi.single a 1) := by
    rw [hφ, hf1]
    simp only [hf1]
  rw [hx]
  exact tsze_expand_fst_snd (sh e x.fst) (fun a ↦ sh e (x.snd a))

end GlobalTheory.AnPer.Charts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearSplittingUnitFaithfullyFlatStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linear_splitting_unit_faithfullyFlat : ∀ (R D : Type) [CommRing R] [CommRing D] [Algebra R D], Module.Finite R D →
    Module.Projective R D → Module.FaithfullyFlat R D → ∃ τ : D →ₗ[R] R, τ 1 = 1 := by
  first | (exact @GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (exact GlobalTheory.unit_splits_of_projective_faithfullyFlat) | (intros; apply GlobalTheory.unit_splits_of_projective_faithfullyFlat  <;> assumption)
end

