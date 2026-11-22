import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0025
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0015
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneRightInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalPrimitiveVectorCompactRescale
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRingStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_is_local_ring : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), IsLocR (Fv F v) := by
  first | exact @GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv | exact GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv | (intros; apply GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HermitianFormsIntegrallyEquivalentAlmostAll
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GoodIso

theorem exists_gl_to_one (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det) :
    ∃ h : GL (Fin m) A,
      cT σ (h : Matrix (Fin m) (Fin m) A) * J * (h : Matrix (Fin m) (Fin m) A) = 1 := by
  obtain ⟨g, d, hg, hdd, hgJ⟩ := GlobalTheory.T.hermitian_unit_form_diagonalizes A σ hσ
    (fun m J hJ hu => GlobalTheory.T.hermitian_unit_form_represents_unit A σ hσ h2 hδ m J hJ hu) m J hJ hd
  choose a ha using fun i => hN (d i) (hdd i).1 (hdd i).2
  have hau : ∀ i, IsUnit (a i) := fun i =>
    isUnit_of_mul_isUnit_left (y := σ (a i)) (by rw [ha i]; exact (hdd i).1)
  choose c hc using fun i => (hau i).exists_right_inv
  have hcu : ∀ i, IsUnit (c i) := fun i => IsUnit.of_mul_eq_one (a i) (by rw [mul_comm]; exact hc i)
  have hdet : IsUnit (g * Matrix.diagonal c).det := by
    rw [Matrix.det_mul, Matrix.det_diagonal]
    exact hg.mul (IsUnit.prod_univ_iff.2 hcu)
  refine ⟨((Matrix.isUnit_iff_isUnit_det _).2 hdet).unit, ?_⟩
  rw [IsUnit.unit_spec, cT_mul]
  have hD : cT σ (Matrix.diagonal c) = Matrix.diagonal (fun i => σ (c i)) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp [cT]
    · simp [cT, Matrix.diagonal_apply, hij, Ne.symm hij]
  calc cT σ (Matrix.diagonal c) * cT σ g * J * (g * Matrix.diagonal c)
      = cT σ (Matrix.diagonal c) * (cT σ g * J * g) * Matrix.diagonal c := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
        rw [hgJ, hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        congr 1
        funext i
        have h1 : σ (c i) * σ (a i) = 1 := by rw [← map_mul, mul_comm, hc i, map_one]
        rw [← ha i]
        calc σ (c i) * (a i * σ (a i)) * c i = (σ (c i) * σ (a i)) * (a i * c i) := by ring
          _ = 1 := by rw [h1, hc i, one_mul]

theorem exists_gl_equiv (A : Type) [CommRing A] [Finite (MaximalSpectrum A)] (σ : A →+* A)
    (hσ : ∀ y, σ (σ y) = y) (h2 : IsUnit (2 : A)) (hδ : ∃ δ : A, IsUnit δ ∧ σ δ = -δ)
    (hN : ∀ β : A, IsUnit β → σ β = β → ∃ a : A, a * σ a = β)
    (m : ℕ) (J J' : Matrix (Fin m) (Fin m) A) (hJ : ∀ i j, σ (J j i) = J i j) (hd : IsUnit J.det)
    (hJ' : ∀ i j, σ (J' j i) = J' i j) (hd' : IsUnit J'.det) :
    ∃ G : GL (Fin m) A,
      J' = cT σ (G : Matrix (Fin m) (Fin m) A) * J * (G : Matrix (Fin m) (Fin m) A) := by
  obtain ⟨h, hh⟩ := exists_gl_to_one A σ hσ h2 hδ hN m J hJ hd
  obtain ⟨k, hk⟩ := exists_gl_to_one A σ hσ h2 hδ hN m J' hJ' hd'
  refine ⟨h * k⁻¹, ?_⟩
  have hkk : (k : Matrix (Fin m) (Fin m) A) * ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hck : cT σ ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) * cT σ (k : Matrix (Fin m) (Fin m) A) = 1 := by
    rw [← cT_mul, hkk, cT_one]
  set K : Matrix (Fin m) (Fin m) A := (k : Matrix (Fin m) (Fin m) A)
  set L : Matrix (Fin m) (Fin m) A := ((k⁻¹ : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)
  set H : Matrix (Fin m) (Fin m) A := (h : Matrix (Fin m) (Fin m) A)
  have e1 : J' = cT σ L * (cT σ K * J' * K) * L := by
    calc J' = (cT σ L * cT σ K) * J' * (K * L) := by rw [hck, hkk, Matrix.one_mul, Matrix.mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  have e2 : cT σ (H * L) * J * (H * L) = cT σ L * (cT σ H * J * H) * L := by
    rw [cT_mul]; simp only [Matrix.mul_assoc]
  rw [Units.val_mul]
  change J' = cT σ (H * L) * J * (H * L)
  rw [e2, hh, ← hk, ← e1]

theorem exists_gl_sub {R : Type} [CommRing R] (s : R →+* R) (hs : ∀ y, s (s y) = y) (O : Subring R)
    (hO : ∀ y ∈ O, s y ∈ O) [Finite (MaximalSpectrum O)] (h2 : IsUnit (2 : O))
    (hδ : ∃ δ : O, IsUnit δ ∧ s (δ : R) = -(δ : R))
    (hN : ∀ β : O, IsUnit β → s (β : R) = β → ∃ a : O, (a : R) * s a = β)
    (m : ℕ) (K K' : Matrix (Fin m) (Fin m) R)
    (hK : ∀ i j, s (K j i) = K i j) (hK' : ∀ i j, s (K' j i) = K' i j)
    (iK : ∀ i j, K i j ∈ O) (iK' : ∀ i j, K' i j ∈ O)
    (wK : ∃ w ∈ O, K.det * w = 1) (wK' : ∃ w ∈ O, K'.det * w = 1) :
    ∃ g : GL (Fin m) R, K' = cT s (g : Matrix (Fin m) (Fin m) R) * K * (g : Matrix (Fin m) (Fin m) R) ∧
      (∀ i j, (g : Matrix (Fin m) (Fin m) R) i j ∈ O) ∧
      ∀ i j, ((g⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j ∈ O := by
  let σO : O →+* O := (s.comp O.subtype).codRestrict O (fun y => hO y y.2)
  have hσO : ∀ y : O, ((σO y : O) : R) = s (y : R) := fun y => rfl
  have lift : ∀ (P : Matrix (Fin m) (Fin m) R) (iP : ∀ i j, P i j ∈ O), (∃ w ∈ O, P.det * w = 1) →
      ∃ Q : Matrix (Fin m) (Fin m) O, Q.map O.subtype = P ∧ IsUnit Q.det := by
    intro P iP ⟨w, hw, hPw⟩
    refine ⟨Matrix.of fun i j => ⟨P i j, iP i j⟩, by ext i j; rfl, ?_⟩
    have hdet : ((Matrix.of fun i j => (⟨P i j, iP i j⟩ : O)).det : O).1 = P.det := by
      have := RingHom.map_det O.subtype (Matrix.of fun i j => (⟨P i j, iP i j⟩ : O))
      exact this
    refine IsUnit.of_mul_eq_one ⟨w, hw⟩ (Subtype.ext ?_)
    simpa [hdet] using hPw
  obtain ⟨Q, rfl, uQ⟩ := lift K iK wK
  obtain ⟨Q', rfl, uQ'⟩ := lift K' iK' wK'
  have herm : ∀ (Q : Matrix (Fin m) (Fin m) O), (∀ i j, s ((Q.map O.subtype) j i) = (Q.map O.subtype) i j) →
      ∀ i j, σO (Q j i) = Q i j := fun Q h i j => Subtype.ext (h i j)
  obtain ⟨G, hG⟩ := exists_gl_equiv O σO (fun y => Subtype.ext (hs _)) h2
    (by obtain ⟨δ, h1, h3⟩ := hδ; exact ⟨δ, h1, Subtype.ext h3⟩)
    (fun β hβ hβ' => by
      obtain ⟨a, ha⟩ := hN β hβ (congrArg Subtype.val hβ')
      exact ⟨a, Subtype.ext ha⟩)
    m Q Q' (herm Q hK) uQ (herm Q' hK') uQ'
  have hcT : ∀ P : Matrix (Fin m) (Fin m) O,
      cT s (P.map O.subtype) = (cT σO P).map O.subtype := fun P => by ext i j; rfl
  refine ⟨bc O.subtype G, ?_, ?_, ?_⟩
  · have hv : ((bc O.subtype G : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) =
        (G : Matrix (Fin m) (Fin m) O).map O.subtype := rfl
    rw [hv, hcT, hG, Matrix.map_mul, Matrix.map_mul]
  · intro i j
    exact (G.val i j).2
  · intro i j
    rw [← map_inv]
    exact ((G⁻¹).val i j).2

theorem sigma_sigma {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2]
  simp

theorem sigR_sigR {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (h : ∀ x, σ (σ x) = x) (y : R ⊗[F] E) : sigR R σ (sigR R σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e => simp [sigR, h]
  | add a b ha hb => simp only [map_add, ha, hb]

theorem mulVec_mem {R : Type} [CommRing R] (O : Subring R) {m : ℕ} (P : Matrix (Fin m) (Fin m) R)
    (hP : ∀ i j, P i j ∈ O) (x : Fin m → R) (hx : ∀ i, x i ∈ O) (i : Fin m) : P.mulVec x i ∈ O := by
  change ∑ j, P i j * x j ∈ O
  exact O.sum_mem fun j _ => O.mul_mem (hP i j) (hx j)

theorem good_iso : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∃ g : GL (Fin M) (Fv F v ⊗[F] E), JR (Fv F v) J' = cT (sigR (Fv F v) σ) (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * JR (Fv F v) J * (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actTup (Fv F v) g X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ hCM M J hJ J' hJ' d b
  have h1 := (GlobalTheory.T.integral_almost_all_places F E σ hCM d b).1
  have ent : ∀ P : Matrix (Fin M) (Fin M) E, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (P i j)) k ∈
        v.adicCompletionIntegers F := fun P =>
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => h1 (P i j)
  filter_upwards [GlobalTheory.T.tensor_integer_ring_almost_all_places F E σ hCM d b, ent J, ent J', h1 (J.det)⁻¹, h1 (J'.det)⁻¹]
    with v hv eJ eJ' dJ dJ'
  obtain ⟨O, hmem, hst, hfin, h2, hδ, -, hN⟩ := hv
  have wit : ∀ P : Matrix (Fin M) (Fin M) E, P.det ≠ 0 →
      (∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (P.det)⁻¹) k ∈
        v.adicCompletionIntegers F) → ∃ w ∈ O, (JR (Fv F v) P).det * w = 1 := by
    intro P hP hk
    refine ⟨inclR (F := F) (Fv F v) (P.det)⁻¹, (hmem _).2 hk, ?_⟩
    have : (JR (Fv F v) P).det = inclR (F := F) (Fv F v) P.det := (RingHom.map_det (inclR (F := F) (Fv F v)) P).symm
    rw [this, ← map_mul, mul_inv_cancel₀ hP, map_one]
  obtain ⟨g, hg, ig, ig'⟩ := exists_gl_sub (sigR (Fv F v) σ)
    (sigR_sigR (Fv F v) σ (sigma_sigma σ hCM)) O hst h2 hδ hN M (JR (Fv F v) J) (JR (Fv F v) J')
    (map_mem_HermR (Fv F v) σ J hJ.1) (map_mem_HermR (Fv F v) σ J' hJ'.1)
    (fun i j => (hmem _).2 (eJ i j)) (fun i j => (hmem _).2 (eJ' i j))
    (wit J hJ.2 dJ) (wit J' hJ'.2 dJ')
  refine ⟨g, hg, fun n X => ?_⟩
  have lat : ∀ Y : Fin n → Fin M → Fv F v ⊗[F] E, Y ∈ latV b v ↔ ∀ a i, Y a i ∈ O := fun Y =>
    ⟨fun h a i => (hmem _).2 (h a i), fun h a i => (hmem _).1 (h a i)⟩
  rw [lat, lat]
  constructor
  · intro h a i
    have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)).mulVec
        (actTup (Fv F v) g X a) := by
      simp only [actTup, Matrix.mulVec_mulVec]
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem O _ ig' _ (h a) i
  · intro h a i
    exact mulVec_mem O _ ig _ (h a) i

end GlobalTheory.CompanionTheory.SW.GoodIso
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeGramScalarAlmostAllStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_gram_scalar_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x y : Fin 1 → Fin M → Fv F v ⊗[F] E, x ∈ latV b v → y ∈ latV b v → gramR (Fv F v) σ J x = (hermScal (Fv F v) σ (algebraMap F _ t) : HermR (Fv F v) σ 1) → gramR (Fv F v) σ J y = gramR (Fv F v) σ J x → ∃ h : HA (Fv F v) σ J, actW (Fv F v) σ J h x = y ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actW (Fv F v) σ J h X ∈ latV b v ↔ X ∈ latV b v := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodTrans.good_trans | exact GlobalTheory.CompanionTheory.SW.GoodTrans.good_trans | (intros; apply GlobalTheory.CompanionTheory.SW.GoodTrans.good_trans <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalMeasuresOrthogonalSumAlmostAllPlaces
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageGood

theorem gram_first {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) :
    gramR R σ (blockOne (algebraMap F E t) J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
  funext a c
  have h1 : (algebraMap F R t) ⊗ₜ[F] (1 : E) = (1 : R) ⊗ₜ[F] (algebraMap F E t) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  simp only [gramR, hR, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, map_one, map_zero,
    zero_mul, mul_zero, Finset.sum_const_zero, add_zero, one_mul, mul_one, JR, Matrix.map_apply]
  show inclR R (blockOne (algebraMap F E t) J 0 0) = (algebraMap F R t) ⊗ₜ[F] (1 : E)
  rw [h1]
  rfl

theorem first_mem {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA (Fv F v) σ J)
    (X : Fin n → Fin M → Fv F v ⊗[F] E)
    (hX : actW (Fv F v) σ J h (consTup X) ∈ latV b v) :
    actW (Fv F v) σ J h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) ∈ latV b v := by
  intro a i k
  exact hX 0 i k

theorem stage_good : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (μ : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (ν : Measure (HermR (Fv F v) σ n)) m, μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Fv F v) σ J n μ ν m → ∀ h : HA (Fv F v) σ (blockOne (algebraMap F E t) J), m (hermOf (Fv F v) σ T hT) {X | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = (latV b v).indicator (fun _ => m (hermOf (Fv F v) σ T hT) (latV b v)) (actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT _ d b
  obtain ⟨hdet, hherm, -, -⟩ := BlockAlg.block_alg F E σ hCM M J t
  have hND : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hherm hJ.1, by
      rw [hdet]
      exact mul_ne_zero (by simpa using ht) hJ.2⟩
  filter_upwards [GoodTrans.good_trans F E σ hCM (M + 1) _ hND t ht d b,
    (LatRat.latV_rational F E σ hCM d b n M).2.2, (LatRat.latV_rational F E σ hCM d b 0 M).2.2]
    with v hv hv1 hv0
  intro μ ν m hμ hν hm h
  have hLoc := LocFv.isLocR_Fv F v
  obtain ⟨i1, i2, i3, i4, -⟩ := id hLoc
  have : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hBorel, -, -⟩ := TopK.topTens_props F E σ hCM (Fv F v)
  have := hBorel n M
  have hOpen := ((GlobalTheory.T.adelic_tuple_projections F E σ hCM d b n M).2.2.2.1 v).2
  obtain ⟨-, -, -, -, -, hact⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) _ hND (Fv F v)
  obtain ⟨-, -, -, -, -, hactJ⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ (Fv F v)
  obtain ⟨-, hone, hmul, hgram⟩ := hact 1
  by_cases he : actW (Fv F v) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) ∈ latV b v
  · rw [Set.indicator_of_mem he]
    have he0 : (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) ∈ latV b v := by
      have h0 := (hv0 (fun a : Fin 0 => a.elim0)).2 (fun a => a.elim0)
      have hc : consTup (fun a : Fin 0 => a.elim0) =
          (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) := by
        funext a
        exact Fin.cases rfl (fun j => j.elim0) a
      rwa [hc] at h0
    obtain ⟨k, hk, hkl⟩ := hv _ _ he0 he (gram_first (Fv F v) σ J t) (hgram h _)
    obtain ⟨ι, -, -, hrange, -, hcons⟩ := StabFirst.stab_first F E σ hCM M J hJ t ht (Fv F v)
    have hg : actW (Fv F v) σ _ (k⁻¹ * h) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) =
        (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) := by
      rw [hmul, ← hk, ← hmul, inv_mul_cancel, hone]
    obtain ⟨u, hu⟩ := (hrange _).2 hg
    have hh : h = k * ι u := by rw [hu]; group
    have hset : {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} =
        actW (Fv F v) σ J u ⁻¹' latV b v := by
      ext X
      rw [Set.mem_ofPred_eq, Set.mem_preimage, hh]
      have := (hact (n + 1)).2.2.1 k (ι u) (consTup X)
      rw [this, hkl, hcons, hv1]
    have hcont : Continuous (actW (Fv F v) σ J u : (Fin n → Fin M → Fv F v ⊗[F] E) → _) :=
      (hactJ n).1.comp (Continuous.prodMk continuous_const continuous_id)
    rw [hset, ← Measure.map_apply hcont.measurable hOpen.measurableSet,
      GlobalTheory.T.gram_fiber_measures_invariant F E σ hCM M J hJ (Fv F v) hLoc n μ ν m hμ hν hm u]
  · rw [Set.indicator_of_notMem he]
    have hempty : {X : Fin n → Fin M → Fv F v ⊗[F] E | actW (Fv F v) σ _ h (consTup X) ∈ latV b v} = ∅ := by
      ext X
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hX => he (first_mem b v σ _ h X hX)
    rw [hempty, measure_empty]

end GlobalTheory.CompanionTheory.SW.StageGood
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalPrimitiveVectorCompactRescaleStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_primitive_vector_compact_rescale : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (v : HeightOneSpectrum (𝓞 F)), ∃ Ω : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), IsCompact Ω ∧ ∀ y : Fin 1 → Fin M → Fv F v ⊗[F] E, (∃ z : Fin M → Fv F v ⊗[F] E, z ⬝ᵥ y 0 = 1) → ∃ (a : (Fv F v ⊗[F] E)ˣ) (z : Fin 1 → Fin M → Fv F v ⊗[F] E), (a : Fv F v ⊗[F] E) • y ∈ Ω ∧ z ∈ Ω ∧ z 0 ⬝ᵥ ((a : Fv F v ⊗[F] E) • y) 0 = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.PrimV.exists_compact_unimodular_vectors_mod_units | exact GlobalTheory.CompanionTheory.SW.PrimV.exists_compact_unimodular_vectors_mod_units | (intros; apply GlobalTheory.CompanionTheory.SW.PrimV.exists_compact_unimodular_vectors_mod_units <;> assumption)
end

