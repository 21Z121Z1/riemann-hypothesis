import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0017
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsDerivAt0OfIsPullback
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionPointsFieldExtension
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.TorsionFieldExt

variable {S : Scheme.{0}}

theorem comp_injective {K Ω : Type} [Field K] [Field Ω] {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S}
    (u : Over.mk x' ⟶ Over.mk x) (A : Over S) : Function.Injective (fun y : Over.mk x ⟶ A => u ≫ y) := by
  let v : Sp Ω ⟶ Sp K := u.left
  have : Surjective v := ⟨fun z => ⟨(default : PrimeSpectrum Ω), Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩
  have : Epi v := Flat.epi_of_flat_of_surjective v
  intro a b h
  have h' : v ≫ a.left = v ≫ b.left := congrArg (fun q => q.left) h
  exact Over.OverMorphism.ext ((cancel_epi v).1 h')

theorem card_torsion (hL : Out.Laws) (P : Out.PolAV S) {K : Type} [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) {n : ℕ}
    (hn : (n : K) ≠ 0) : Nat.card {y : Over.mk x ⟶ P.A // y ^ n = 1} = n ^ (2 * P.g) := by
  have hn' : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact hn Nat.cast_zero)
  obtain ⟨P', g, hg, hdim, hmul, -⟩ := hL.polBaseChange S _ x P
  have c := (hL.mulN _ P' n hn').2.2.2.2 K (𝟙 _) hn
  let Φ : (Over.mk (𝟙 (Sp K)) ⟶ P'.A) →* (Over.mk (𝟙 _ ≫ x) ⟶ P.A) :=
    MonoidHom.mk' (fun y => Out.toBase hg.w y) (hmul _)
  have hΦ : Function.Bijective Φ :=
    ⟨fun a b e => Over.OverMorphism.ext
      (hg.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun z =>
      ⟨Over.homMk (hg.lift z.left (𝟙 _) (Over.w z)) (hg.lift_snd _ _ _), Over.OverMorphism.ext (hg.lift_fst _ _ _)⟩⟩
  have e : Nat.card {y : Over.mk (𝟙 (Sp K)) ⟶ P'.A // y ^ n = 1} =
      Nat.card {y : Over.mk (𝟙 _ ≫ x) ⟶ P.A // y ^ n = 1} :=
    Nat.card_congr ((Equiv.ofBijective Φ hΦ).subtypeEquiv fun y => by
      show _ ↔ Φ y ^ n = 1
      rw [← map_pow, map_eq_one_iff Φ hΦ.1])
  rw [Category.id_comp] at e
  rw [← e, ← hdim]
  exact c

theorem exists_of_isAlgClosed (hL : Out.Laws) (P : Out.PolAV S) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K]
    [IsAlgClosed Ω] {x : Sp K ⟶ S} {x' : Sp Ω ⟶ S} (u : Over.mk x' ⟶ Over.mk x) {n : ℕ} (hK : (n : K) ≠ 0)
    (hΩ : (n : Ω) ≠ 0) (z : Over.mk x' ⟶ P.A) (hz : z ^ n = 1) :
    ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ u ≫ y = z := by
  have hn' : 0 < n := Nat.pos_of_ne_zero (by rintro rfl; exact hK Nat.cast_zero)
  have c₁ := card_torsion hL P x hK
  have c₂ := card_torsion hL P x' hΩ
  have : Finite {y : Over.mk x' ⟶ P.A // y ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  let F : {y : Over.mk x ⟶ P.A // y ^ n = 1} → {y : Over.mk x' ⟶ P.A // y ^ n = 1} := fun a =>
    ⟨u ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun a b h => Subtype.ext (comp_injective u _ (congrArg Subtype.val h)), c₁.trans c₂.symm⟩
  obtain ⟨a, ha⟩ := hF.2 ⟨z, hz⟩
  exact ⟨a.1, a.2, congrArg Subtype.val ha⟩

end GlobalTheory.TorsionFieldExt

namespace GlobalTheory

open TorsionFieldExt in

theorem torsion_points_field_extension : Out.Laws → ∀ (S : Scheme.{0}) (P : Out.PolAV S) (K Ω : Type) [Field K] [Field Ω] [IsAlgClosed K] (i : K →+* Ω) (x : Sp K ⟶ S), Function.Injective (fun y : Over.mk x ⟶ P.A => (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y) ∧ ∀ (n : ℕ) (z : Over.mk (spMap i ≫ x) ⟶ P.A), (n : K) ≠ 0 → z ^ n = 1 → ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x) ≫ y = z := by
  intro hL S P K Ω _ _ _ i x
  refine ⟨comp_injective _ _, fun n z hn hz => ?_⟩
  let j : Ω →+* AlgebraicClosure Ω := algebraMap _ _
  let v : Over.mk (spMap j ≫ spMap i ≫ x) ⟶ Over.mk (spMap i ≫ x) := Over.homMk (spMap j) rfl
  have hn' : (n : AlgebraicClosure Ω) ≠ 0 := by
    rw [← map_natCast (j.comp i)]
    exact (map_ne_zero _).2 hn
  obtain ⟨y, hy, e⟩ := exists_of_isAlgClosed hL P
    (v ≫ (Over.homMk (spMap i) rfl : Over.mk (spMap i ≫ x) ⟶ Over.mk x)) hn hn' (v ≫ z)
    (by rw [← MonObj.comp_pow, hz, MonObj.comp_one])
  exact ⟨y, hy, comp_injective v _ ((Category.assoc _ _ _).symm.trans e)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.TwoMulEqOfIsTypeFn
section
open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

namespace GlobalTheory.PeriodDatum

noncomputable section

lemma lattice_equiv {La : Type} [AddCommGroup La] {g : ℕ} (P : La →+ (Fin g → ℂ)) (hinj : Function.Injective P)
    (hdisc : DiscreteTopology P.range) (hspan : Submodule.span ℝ (Set.range P) = ⊤) :
    Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g ∧
      ∃ e : ℝ ⊗[ℤ] La ≃ₗ[ℝ] (Fin g → ℂ), ∀ x, e (1 ⊗ₜ x) = P x := by
  let L : Submodule ℤ (Fin g → ℂ) := LinearMap.range P.toIntLinearMap
  haveI : DiscreteTopology L := hdisc
  haveI : IsZLattice ℝ L := ⟨hspan⟩
  let f : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective P.toIntLinearMap hinj
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ La := Module.Finite.equiv f.symm
  haveI : Module.Free ℤ La := Module.Free.of_equiv f.symm
  have hr : Module.finrank ℤ La = Module.finrank ℝ (Fin g → ℂ) := by
    rw [f.finrank_eq, ZLattice.rank ℝ L]
  have hg : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, Module.finrank_fin_fun]
  let φ : ℝ ⊗[ℤ] La →ₗ[ℝ] (Fin g → ℂ) := P.toIntLinearMap.liftBaseChange ℝ
  have hφ : ∀ x, φ (1 ⊗ₜ x) = P x := fun x => by simp [φ]
  have hs : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, hφ x⟩
  have hd : Module.finrank ℝ (ℝ ⊗[ℤ] La) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_baseChange, hr]
  exact ⟨inferInstance, hr.trans hg, LinearEquiv.ofBijective φ
    ⟨(LinearMap.injective_iff_surjective_of_finrank_eq_finrank hd).2 hs, hs⟩, hφ⟩

lemma hermForm_smul_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm (c • z) w = c * hermForm Hm z w := by
  simp [hermForm]

lemma hermForm_smul_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (c : ℂ) (z w : Fin g → ℂ) :
    hermForm Hm z (c • w) = starRingEnd ℂ c * hermForm Hm z w := by
  simp [hermForm, Matrix.mulVec_smul]

lemma hermForm_add_left {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z z' w : Fin g → ℂ) :
    hermForm Hm (z + z') w = hermForm Hm z w + hermForm Hm z' w := by
  simp [hermForm]

lemma hermForm_add_right {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w w' : Fin g → ℂ) :
    hermForm Hm z (w + w') = hermForm Hm z w + hermForm Hm z w' := by
  simp [hermForm, Matrix.mulVec_add]

lemma hermForm_self_im {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z : Fin g → ℂ) :
    (hermForm Hm z z).im = 0 := by
  have := h.im_star_dotProduct_mulVec_self (star z)
  simpa [hermForm] using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

lemma two_mul_eq_of_isTypeFn (H : Host E) {p q g : ℕ} {ty : Fin g → (E →+* ℂ)} (hty : IsTypeFn H p q ty) :
    2 * g = Module.finrank ℚ E * (p + q) := by
  classical
  let e := (Fintype.equivFin (E →+* ℂ)).symm
  have he : IsTypeFn H 1 1 e := fun τ => by
    have : Nat.card {i // e i = τ} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext (e.injective (a.2.trans b.2.symm))⟩, ⟨⟨e.symm τ, by simp⟩⟩⟩
    exact ⟨fun _ => this, fun _ => this⟩
  have h1 := PeriodNonempty.sum_type H hty 1
  have h2 := PeriodNonempty.sum_type H he 1
  simp only [map_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
    Embeddings.card, Nat.cast_one] at h1 h2
  have : (2 * g : ℂ) = Module.finrank ℚ E * (p + q) := by rw [h1, h2]; ring
  exact_mod_cast this

theorem exists_datum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (La : Type)
    [AddCommGroup La] [Module (𝓞 E) La] (EF : LinearMap.BilinForm ℤ La) (p q g : ℕ) (ty : Fin g → (E →+* ℂ))
    (P : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), IsTypeFn H p q ty → Function.Bijective EF →
    (∀ (a : 𝓞 E) x y, EF (a • x) y = EF x (H.bar a • y)) →
    (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) → Function.Injective P → DiscreteTopology P.range →
    Submodule.span ℝ (Set.range P) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ x y, (hermForm Hm (P x) (P y)).im = EF x y) →
    ∃ (D' : Datum H) (e : D'.La ≃ₗ[𝓞 E] La), D'.p = p ∧ D'.q = q ∧ ∀ x y, D'.EF x y = EF (e x) (e y) := by
  intro E _ _ _ H La _ _ EF p q g ty P Hm hty hbij hadj hlin hinj hdisc hspan hH hpos him
  classical
  obtain ⟨hfin, hrk, e, he⟩ := lattice_equiv P hinj hdisc hspan
  haveI : Module.Finite (𝓞 E) La := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) La
  have htor : Submodule.torsion (𝓞 E) La = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨a, ha⟩, hx⟩
    have ha0 : (a : E) ≠ 0 := by
      simpa using nonZeroDivisors.ne_zero ha
    rw [Submodule.mem_bot]
    apply hinj
    funext i
    have h1 := hlin a x i
    have h2 : a • x = 0 := hx
    rw [h2, map_zero] at h1
    rw [map_zero]
    exact (mul_eq_zero.1 h1.symm).resolve_left ((map_ne_zero (ty i)).2 ha0)
  haveI : Module.Flat (𝓞 E) La := IsDedekindDomain.flat_iff_torsion_eq_bot.2 htor
  haveI : Module.FinitePresentation (𝓞 E) La := Module.finitePresentation_of_finite _ _
  have hproj : Module.Projective (𝓞 E) La := Module.Flat.projective_of_finitePresentation
  have hrank : Module.finrank (𝓞 E) La = p + q := by
    have h1 := finrank_int_eq_mul_of_finite (O := 𝓞 E) (M := La)
    rw [hrk, two_mul_eq_of_isTypeFn H hty, RingOfIntegers.rank] at h1
    exact (Nat.eq_of_mul_eq_mul_left Module.finrank_pos h1).symm
  have het : ∀ (r : ℝ) x, e (r ⊗ₜ x) = (r : ℂ) • P x := fun r x => by
    rw [← he, Complex.coe_smul, ← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  have hB : ∀ x y, EF.baseChange ℝ x y = (hermForm Hm (e x) (e y)).im := fun x y => by
    induction x using TensorProduct.induction_on with
    | zero => simp [hermForm]
    | add x x' h h' => simp only [map_add, LinearMap.add_apply, h, h', hermForm_add_left, Complex.add_im]
    | tmul r x =>
      induction y using TensorProduct.induction_on with
      | zero => simp [hermForm]
      | add y y' h h' => simp only [map_add, h, h', hermForm_add_right, Complex.add_im]
      | tmul r' y =>
        rw [het, het, hermForm_smul_left, hermForm_smul_right, LinearMap.BilinForm.baseChange_tmul]
        simp [him]
        ring
  let d : (Fin g → ℂ) → Module.End ℂ (Fin g → ℂ) := fun c => Matrix.toLin' (Matrix.diagonal c)
  have hd : ∀ c z i, d c z i = c i * z i := fun c z i => by simp [d, Matrix.mulVec_diagonal]
  have hdt : ∀ c, LinearMap.trace ℝ _ (e.symm.conj ((d c).restrictScalars ℝ)) = 2 * (∑ i, c i).re := fun c => by
    rw [LinearMap.trace_conj', PeriodNonempty.trace_real]
    simp [d]
  let J : ℝ ⊗[ℤ] La →ₗ[ℝ] ℝ ⊗[ℤ] La := e.symm.conj ((d fun _ => Complex.I).restrictScalars ℝ)
  have hJ : ∀ x, e (J x) = Complex.I • e x := fun x => by
    funext i
    simp [J, LinearEquiv.conj_apply, hd]
  refine ⟨{ La := La, fin := inferInstance, proj := hproj, EF := EF, alt := fun x => ?_, unimod := hbij,
            adj := hadj, p := p, q := q, rank := hrank, dom := ⟨J, fun x => ?_, fun x y => ?_, fun x hx => ?_, ?_⟩ },
    LinearEquiv.refl _ _, rfl, rfl, fun _ _ => rfl⟩
  · have := him x x
    rw [hermForm_self_im hH] at this
    exact_mod_cast this.symm
  · apply e.injective
    rw [hJ, hJ, smul_smul, Complex.I_mul_I, map_neg, neg_smul, one_smul]
  · rw [hB, hB, hJ, hJ, hermForm_smul_left, hermForm_smul_right]
    simp
  · rw [hB, hJ, hermForm_smul_left]
    simpa using hpos (e x) (by simpa using hx)
  · intro a A t hA ht
    rw [← PeriodNonempty.sum_type H hty] at ht
    have hAe : ∀ x i, e (A x) i = ty i (a : E) * e x i := fun x i => by
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x x' h h' => simp only [map_add, Pi.add_apply, h, h', mul_add]
      | tmul r x =>
        have : (r ⊗ₜ[ℤ] x : ℝ ⊗[ℤ] La) = r • (1 ⊗ₜ[ℤ] x) := by
          rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        rw [this, map_smul, hA, map_smul, map_smul, he, he]
        simp only [Pi.smul_apply, hlin, Complex.real_smul]
        ring
    have h1 : A = e.symm.conj ((d fun i => ty i (a : E)).restrictScalars ℝ) := by
      refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp [LinearEquiv.conj_apply, hd, hAe]
    have h2 : J ∘ₗ A = e.symm.conj ((d fun i => Complex.I * ty i (a : E)).restrictScalars ℝ) := by
      refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp [LinearEquiv.conj_apply, hd, hAe, hJ, mul_assoc]
    refine ⟨?_, ?_, ?_⟩
    · refine LinearMap.ext fun x => e.injective (funext fun i => ?_)
      simp only [LinearMap.comp_apply, hJ, hAe, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [h1, hdt, ht]
    · rw [h2, hdt, ht, ← Finset.mul_sum]
      simp

end

end GlobalTheory.PeriodDatum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.UnimodularSymplecticCoordinatesAndLatticeRank
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem hermForm_self_im_eq_zero {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (z : Fin g → ℂ) : (hermForm Hm z z).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  simp only [hermForm, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul,
    Pi.star_apply, Complex.star_def, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [← h.apply j k, Complex.star_def]
  ring

theorem free_finite_finrank_of_discrete_span {La : Type} [AddCommGroup La] {g : ℕ}
    (Q : La →+ (Fin g → ℂ)) (hinj : Function.Injective Q) (hd : DiscreteTopology Q.range)
    (hsp : Submodule.span ℝ (Set.range Q) = ⊤) :
    Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g := by
  set L : Submodule ℤ (Fin g → ℂ) := LinearMap.range Q.toIntLinearMap with hL
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨by
    rw [hL, LinearMap.coe_range]
    exact hsp⟩
  let e : La ≃ₗ[ℤ] L := LinearEquiv.ofInjective Q.toIntLinearMap hinj
  haveI : Module.Free ℤ L := ZLattice.module_free ℝ L
  haveI : Module.Finite ℤ L := ZLattice.module_finite ℝ L
  refine ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm, ?_⟩
  rw [e.finrank_eq, ZLattice.rank ℝ L, Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem unimodular_symplectic_coordinates_and_lattice_rank :
    (∀ (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ), Function.Bijective EF → (∀ x, EF x x = 0) → Module.finrank ℤ La = 2 * g → ∃ bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] La, ∀ a b, EF (bas a) (bas b) = omegaStd a b) ∧ ∀ (La : Type) [AddCommGroup La] (EF : LinearMap.BilinForm ℤ La) (g : ℕ) (Q : La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ), (Function.Injective Q ∧ DiscreteTopology (Q).range ∧ Submodule.span ℝ (Set.range Q) = ⊤ ∧ (Hm).IsHermitian ∧ (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) ∧ ∀ x y, (hermForm Hm (Q x) (Q y)).im = EF x y) → Module.Free ℤ La ∧ Module.Finite ℤ La ∧ Module.finrank ℤ La = 2 * g ∧ ∀ x, EF x x = 0 := by
  refine ⟨fun La _ _ _ EF g hbij halt hrk => ?_,
    fun La _ EF g Q Hm ⟨hinj, hd, hsp, hH, _, hIm⟩ => ?_⟩
  · obtain ⟨b, hb⟩ := exists_isSymplecticBasis_of_finrank (B := EF) halt hbij hrk
    have hf : IsSymplecticFamily EF (fun i => b (Sum.inl i)) (fun i => b (Sum.inr i))
        (fun _ => 1) := hb
    classical
    refine ⟨b.equivFun.symm, fun x y => ?_⟩
    simp only [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, map_add, LinearMap.add_apply,
      map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    simp only [hf.left_left, hf.right_right, hf.left_right, hf.right_left halt, mul_zero,
      Finset.sum_const_zero, add_zero, zero_add, mul_ite, _root_.mul_one, mul_neg,
      Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_neg_distrib, omegaStd]
    rw [neg_add_eq_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  · obtain ⟨h1, h2, h3⟩ := free_finite_finrank_of_discrete_span Q hinj hd hsp
    exact ⟨h1, h2, h3, fun x => by
      have e : ((EF x x : ℤ) : ℝ) = 0 := by rw [← hIm x x]; exact hermForm_self_im_eq_zero hH _
      exact_mod_cast e⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.VerticalDerivativeInCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory.VerticalDeriv

open GlobalTheory.FibreDeriv

variable {g : ℕ} {X Z : Scheme.{0}}

theorem isDerivAt0_unique {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} {w : Fin g → ℂ} {v v' : Sp (DualNumber ℂ) ⟶ Z}
    (H : IsDerivAt0 e w v) (H' : IsDerivAt0 e w v') : v = v' := by
  rw [isDerivAt0_iff] at H H'
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have h := (top_le_preimage_eps v _ H.1 U).2 h0
  have h' := (top_le_preimage_eps v' _ H'.1 U).2 h0
  exact TangentOrigin.ext_evalPt hU h h' (RingHom.ext fun f => (H.2 U h f).trans (H'.2 U h' f).symm)

theorem exists_isDerivAt0 {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (hol : IsHolTo Set.univ e) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber ℂ) ⟶ Z, IsDerivAt0 e w v := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have hd := LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0
  let J : Γ(Z, U) →+* DualNumber ℂ :=
    { toFun := fun f => jet w (fun z => valAt' (e z) U f)
      map_one' := by
        have : (fun z => valAt' (e z) U 1) =ᶠ[nhds 0] fun _ => 1 := by
          filter_upwards [LocalLift.hol_eventually_mem hol (Set.mem_univ _) h0] with z hz
          exact valAt'_one _ hz.2
        rw [jet_congr w this, jet_const, map_one]
      map_zero' := by
        simp only [valAt'_zero]
        rw [jet_const, map_zero]
      map_add' := fun f f' => by
        simp only [valAt'_add]
        exact jet_add w (hd f) (hd f')
      map_mul' := fun f f' => by
        simp only [valAt'_mul]
        exact jet_mul w (hd f) (hd f') }
  obtain ⟨v, hv, hve⟩ := TangentOrigin.exists_evalPt_eq hU J
  refine ⟨v, isDerivAt0_of_affine ?_ hU hv fun a => ⟨hd a, DFunLike.congr_fun hve a⟩⟩
  refine TangentOrigin.ext_evalPt hU ((TangentOrigin.top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)
  refine (TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC v U hv _ f).trans ?_
  rw [hve, ← TangentOrigin.valAt'_eq_evalPt]
  exact fst_jet w (fun z => valAt' (e z) U f)

theorem isDerivAt0_vertical (p : Z ⟶ X) (x : Sp ℂ ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (he : ∀ z, e z ≫ p = x)
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z} (H : IsDerivAt0 e w v) :
    v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x := by
  have h1 := isDerivAt0_comp H p
  simp only [he] at h1
  exact isDerivAt0_unique h1 (LocalLift.isDerivAt0_const (fun _ => x) w fun U f _ => by simp)

theorem isDerivAt0_snd {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (hol : IsHolTo Set.univ e) {U : Z.Opens} {n : ℕ}
    (t : Fin n → Γ(Z, U)) (h0 : ⊤ ≤ e 0 ⁻¹ᵁ U) {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z}
    (H : IsDerivAt0 e w v) (h : ⊤ ≤ v ⁻¹ᵁ U) (i : Fin n) :
    (TangentOrigin.evalPt v U h (t i)).snd = fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0 w i := by
  rw [fderiv_pi fun i => LocalLift.hol_differentiableAt hol (Set.mem_univ _) h0 (t i)]
  exact H.2 U h (t i)

theorem bijective_iff_injective (p : Z ⟶ X) (x : Sp ℂ ⟶ X) {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)} (he : ∀ z, e z ≫ p = x)
    (hol : IsHolTo Set.univ e) (U : Z.Opens) (t : Fin g → Γ(Z, U)) (h0 : ⊤ ≤ e 0 ⁻¹ᵁ U)
    (hun : ∀ (v v' : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ p = v' ≫ p →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' →
      (∀ i, TangentOrigin.evalPt v U h (t i) = TangentOrigin.evalPt v' U h' (t i)) → v = v') :
    (∀ v : Sp (DualNumber ℂ) ⟶ Z, v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → ∃! w, IsDerivAt0 e w v) ↔
      Function.Injective (fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0) := by
  set T := fderiv ℂ (fun z i => valAt' (e z) U (t i)) 0 with hT
  have key : ∀ (v : Sp (DualNumber ℂ) ⟶ Z) (h : ⊤ ≤ v ⁻¹ᵁ U), v ≫ p = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ x →
      spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = e 0 → ∀ w,
      (IsDerivAt0 e w v ↔ T w = fun i => (TangentOrigin.evalPt v U h (t i)).snd) := by
    intro v h hv hv0 w
    refine ⟨fun H => funext fun i => (isDerivAt0_snd hol t h0 H h i).symm, fun H => ?_⟩
    obtain ⟨v', H'⟩ := exists_isDerivAt0 hol w
    have h' := (top_le_preimage_eps v' _ H'.1 U).2 h0
    rw [hun v v' h h' (hv.trans (isDerivAt0_vertical p x he H').symm) (hv0.trans H'.1.symm) fun i => ?_]
    · exact H'
    · refine TrivSqZeroExt.ext ((fst_evEps v _ hv0 U h _).trans (fst_evEps v' _ H'.1 U h' _).symm) ?_
      rw [isDerivAt0_snd hol t h0 H' h' i]
      exact (congrFun H i).symm
  constructor
  · intro H w w' hw
    obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol w
    have h := (top_le_preimage_eps v _ Hv.1 U).2 h0
    have hv := isDerivAt0_vertical p x he Hv
    exact (H v hv Hv.1).unique Hv ((key v h hv Hv.1 w').2 (hw.symm.trans ((key v h hv Hv.1 w).1 Hv)))
  · intro H v hv hv0
    have h := (top_le_preimage_eps v _ hv0 U).2 h0
    simp only [key v h hv hv0]
    have hs : Function.Surjective T := (LinearMap.injective_iff_surjective (f := T.toLinearMap)).1 H
    exact (Function.bijective_iff_existsUnique T).1 ⟨H, hs⟩ _

end GlobalTheory.VerticalDeriv

namespace GlobalTheory

open VerticalDeriv in

theorem vertical_derivative_in_coordinates :
    ∀ (X : Scheme.{0}) (G : Over X) (x : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk x ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → (∀ w, ∃! v : epsPt x ⟶ G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧ ∀ (U : G.left.Opens) (t : Fin g → Γ(G.left, U)), ⊤ ≤ (show Sp ℂ ⟶ G.left from (e 0).left) ⁻¹ᵁ U → (∀ (v v' : Sp (DualNumber ℂ) ⟶ G.left) (h : ⊤ ≤ v ⁻¹ᵁ U) (h' : ⊤ ≤ v' ⁻¹ᵁ U), v ≫ G.hom = v' ≫ G.hom → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v = spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v' → (∀ i, GlobalTheory.TangentOrigin.evalPt v U h (t i) = GlobalTheory.TangentOrigin.evalPt v' U h' (t i)) → v = v') → ((∀ v : epsPt x ⟶ G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left → ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left) ↔ Function.Injective (fderiv ℂ (fun z i => valAt' (e z).left U (t i)) 0)) := by
  intro X G x g e hol
  have he : ∀ z, (show Sp ℂ ⟶ G.left from (e z).left) ≫ G.hom = x := fun z => Over.w (e z)
  refine ⟨fun w => ?_, fun U t h0 hun => ?_⟩
  · obtain ⟨v, Hv⟩ := exists_isDerivAt0 hol w
    exact ⟨Over.homMk v (isDerivAt0_vertical G.hom x he Hv), Hv,
      fun v' Hv' => Over.OverMorphism.ext (isDerivAt0_unique Hv' Hv)⟩
  · refine Iff.trans ?_ (bijective_iff_injective G.hom x he hol U t h0 hun)
    exact ⟨fun H v hv hv0 => H (Over.homMk v hv) hv0, fun H v hv0 => H v.left (Over.w v) hv0⟩

end GlobalTheory
end
end

