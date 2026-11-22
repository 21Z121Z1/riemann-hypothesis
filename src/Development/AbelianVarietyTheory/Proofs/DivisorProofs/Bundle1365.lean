import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import ReciprocityTheory.SemistableReduction.Bundle0025
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1335
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmUnitPowFourIdempotentModEight
import Development.AutomorphicArithmetic.WeightCongruences.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1339
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1173
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThreeLeScaleOfPowBound
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0008
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsPageRunRecord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1342
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalDegreePencilLineDiscriminantLe
section
set_option autoImplicit false

noncomputable section

open MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.HSChoice GlobalTheory.PencilDisc

namespace GlobalTheory.PencilDiscDeg

variable {F : Type} [Field F] {σ : Type}

def CoeffDeg (e : ℕ) (P : Polynomial (MvPolynomial σ F)) : Prop :=
  ∀ k, (P.coeff k).totalDegree ≤ e

theorem CoeffDeg.mono {e e' : ℕ} {P : Polynomial (MvPolynomial σ F)} (h : CoeffDeg e P) (he : e ≤ e') :
    CoeffDeg e' P := fun k => (h k).trans he

theorem coeffDeg_C {e : ℕ} {a : MvPolynomial σ F} (ha : a.totalDegree ≤ e) :
    CoeffDeg e (Polynomial.C a) := by
  intro k
  rw [Polynomial.coeff_C]
  split_ifs
  · exact ha
  · simp

theorem coeffDeg_one : CoeffDeg 0 (1 : Polynomial (MvPolynomial σ F)) := by
  rw [← Polynomial.C_1]
  exact coeffDeg_C (by simp)

theorem coeffDeg_X : CoeffDeg 0 (Polynomial.X : Polynomial (MvPolynomial σ F)) := by
  intro k
  rw [Polynomial.coeff_X]
  split_ifs <;> simp

theorem CoeffDeg.add {e : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (hQ : CoeffDeg e Q) :
    CoeffDeg e (P + Q) := by
  intro k
  rw [Polynomial.coeff_add]
  exact (totalDegree_add _ _).trans (max_le (hP k) (hQ k))

theorem CoeffDeg.mul {e e' : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P)
    (hQ : CoeffDeg e' Q) : CoeffDeg (e + e') (P * Q) := by
  intro k
  rw [Polynomial.coeff_mul]
  exact totalDegree_finsetSum_le fun x _ => (totalDegree_mul _ _).trans (add_le_add (hP _) (hQ _))

theorem coeffDeg_sum {ι : Type} (s : Finset ι) {e : ℕ} (P : ι → Polynomial (MvPolynomial σ F))
    (h : ∀ i ∈ s, CoeffDeg e (P i)) : CoeffDeg e (∑ i ∈ s, P i) := by
  intro k
  rw [Polynomial.finset_sum_coeff]
  exact totalDegree_finsetSum_le fun i hi => h i hi k

theorem coeffDeg_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (e : ι → ℕ)
    (P : ι → Polynomial (MvPolynomial σ F)) (h : ∀ i ∈ s, CoeffDeg (e i) (P i)) :
    CoeffDeg (∑ i ∈ s, e i) (∏ i ∈ s, P i) := by
  induction s using Finset.induction_on with
  | empty => simpa using coeffDeg_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem CoeffDeg.pow {e : ℕ} {P : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) (n : ℕ) :
    CoeffDeg (n * e) (P ^ n) := by
  induction n with
  | zero => simpa using coeffDeg_one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hP

theorem CoeffDeg.derivative {e : ℕ} {P : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P) :
    CoeffDeg e (Polynomial.derivative P) := by
  intro k
  rw [Polynomial.coeff_derivative]
  have h1 : ((k : MvPolynomial σ F) + 1) = C ((k : F) + 1) := by simp
  rw [h1]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, add_zero]
  exact hP (k + 1)

theorem totalDegree_resultant_le {e : ℕ} {P Q : Polynomial (MvPolynomial σ F)} (hP : CoeffDeg e P)
    (hQ : CoeffDeg e Q) (m n : ℕ) : (Polynomial.resultant P Q m n).totalDegree ≤ (m + n) * e := by
  have hH : ∀ i j, (Polynomial.sylvester P Q m n i j).totalDegree ≤ e := by
    intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
      split_ifs
      · exact hQ _
      · simp
    | right j =>
      simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
      split_ifs
      · exact hP _
      · simp
  rw [Polynomial.resultant, Matrix.det_apply]
  refine totalDegree_finsetSum_le fun s _ => ?_
  refine (totalDegree_smul_le _ _).trans ((totalDegree_finsetProd _ _).trans ?_)
  simpa using Finset.sum_le_card_nsmul Finset.univ _ e fun i _ => hH (s i) i

theorem coeffDeg_line {D N δ : ℕ} (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (ξ₀ ξ₁ : Fin N → F) :
    CoeffDeg (D * δ) (line (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (ξ₀ j)) (fun j => C (ξ₁ j)) f) := by
  rw [line, aeval_def, eval₂_eq']
  refine coeffDeg_sum _ _ fun d hd => ?_
  have hc : CoeffDeg 0 (algebraMap F (Polynomial (MvPolynomial (Fin D × Fin N) F)) (coeff d f)) := by
    rw [Polynomial.algebraMap_apply]
    exact coeffDeg_C (by rw [MvPolynomial.algebraMap_eq, totalDegree_C])
  have hw : ∀ p : Fin (D + 1) × Fin N, CoeffDeg (if p.1 = Fin.last D then 0 else 1)
      (join (fun i j => Polynomial.C (X (i, j) : MvPolynomial (Fin D × Fin N) F))
        (fun j => Polynomial.C (C (ξ₀ j)) + Polynomial.C (C (ξ₁ j)) * Polynomial.X) p) := by
    rintro ⟨i, j⟩
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [join, Fin.lastCases_last, if_true]
      exact (coeffDeg_C (totalDegree_C _).le).add ((coeffDeg_C (e := 0) (totalDegree_C _).le).mul coeffDeg_X)
    · simp only [join, Fin.lastCases_castSucc, if_neg (Fin.castSucc_ne_last i)]
      exact coeffDeg_C (totalDegree_X _).le
  refine (hc.mul (coeffDeg_prod Finset.univ _ _ fun p _ => (hw p).pow (d p))).mono (le_of_eq ?_)
  rw [zero_add, Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  have h := hf d hd
  simp [Fin.castSucc_ne_last, h]

theorem totalDegree_disc_le (F : Type) [Field F] (D N δ : ℕ) (f : MvPolynomial (Fin (D + 1) × Fin N) F)
    (hf : IsMultiHomogeneous (fun _ => δ) f) (ξ₀ ξ₁ : Fin N → F) :
    (disc δ (fun i j => (X (i, j) : MvPolynomial (Fin D × Fin N) F))
      (fun j => C (ξ₀ j)) (fun j => C (ξ₁ j)) f).totalDegree ≤ 2 * D * δ ^ 2 := by
  have h := coeffDeg_line f hf ξ₀ ξ₁
  refine (totalDegree_resultant_le h h.derivative δ (δ - 1)).trans ?_
  calc (δ + (δ - 1)) * (D * δ) ≤ (2 * δ) * (D * δ) := Nat.mul_le_mul_right _ (by omega)
    _ = 2 * D * δ ^ 2 := by ring

end GlobalTheory.PencilDiscDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceW0PowFourEven
section
open NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AdaptedDet

namespace GlobalTheory.AdaptedDetSign

theorem det_interp_gen {E : Type} [Field E] [NumberField E] {r : ℕ} (n : ℕ) (hn : n ≠ 0)
    (e t δ : 𝓞 E) (he0 : e ≠ 0) (he : e * e - e = n * t)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, g *ᵥ v ∈ Λ) (hdet : g.det = (δ : E)) :
    ∃ y : 𝓞 E, ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det =
      ((e * δ + (1 - e) + n * y : 𝓞 E) : E) := by
  classical
  let K := AlgebraicClosure E
  have hinj := (algebraMap E K).injective
  have hn' : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hint : ∀ x : 𝓞 E, IsIntegral ℤ (algebraMap E K (x : E)) := fun x =>
    x.isIntegral_coe.algebraMap
  have hroots : ∀ μ ∈ (g.map (algebraMap E K)).charpoly.roots, IsIntegral ℤ μ := by
    intro μ hμ
    have := CongruenceDet.isIntegral_root (R := 𝓞 E) (M := 1) one_ne_zero Λ g hfg hspan
      (fun v hv => ⟨g *ᵥ v - v, sub_mem (hg v hv) hv, by simp⟩) μ
      (Polynomial.isRoot_of_mem_roots hμ)
    have h2 : IsIntegral ℤ ((μ - 1) / ((1 : ℕ) : K)) := isIntegral_trans (A := 𝓞 E) _ this
    simpa using h2.add isIntegral_one
  obtain ⟨y, hy, h⟩ := prod_interp (n : K) (algebraMap E K e) (algebraMap E K t)
    (by
      have := congrArg (fun x : 𝓞 E => algebraMap E K (x : E)) he
      simpa using this) (hint e) (hint t) _ hroots
  rw [← det_smul_add _ _ _ (by simpa using he0), ← Matrix.det_eq_prod_roots_charpoly,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det, hdet] at h
  set d := ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E)).det with hd
  have hd' : algebraMap E K d = algebraMap E K ((e : E) * (δ : E) + (1 - (e : E))) + n * y := by
    rw [hd, RingHom.map_det]
    have : (algebraMap E K).mapMatrix ((e : E) • g + (1 - (e : E)) • (1 : Matrix (Fin r) (Fin r) E))
        = algebraMap E K e • (algebraMap E K).mapMatrix g + (1 - algebraMap E K e) • 1 := by
      generalize (e : E) = x
      ext i j
      by_cases h : i = j <;> simp [h, -algebraMap_smul]
    rw [this, h, map_add, map_mul, map_sub, map_one]
  have hy' : IsIntegral ℤ ((d - ((e : E) * (δ : E) + (1 - (e : E)))) / n) := by
    rw [← isIntegral_algebraMap_iff hinj, map_div₀, map_sub, map_natCast, hd',
      add_sub_cancel_left, mul_div_cancel_left₀ _ hn']
    exact hy
  obtain ⟨z, hz⟩ : ∃ z : 𝓞 E, (z : E) = (d - ((e : E) * (δ : E) + (1 - (e : E)))) / n := ⟨⟨_, hy'⟩, rfl⟩
  refine ⟨z, ?_⟩
  have hn'' : (n : E) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have h1 : ((e * δ + (1 - e) + n * z : 𝓞 E) : E) =
      (e : E) * (δ : E) + (1 - (e : E)) + n * (z : E) := by simp
  rw [h1, hz]
  field_simp
  ring

theorem norm_one_add_two {E : Type} [Field E] [NumberField E] (u : 𝓞 E) :
    (4 : ℤ) ∣ Algebra.norm ℤ (1 + 2 * u : 𝓞 E) - (1 + 2 * Algebra.trace ℤ (𝓞 E) u) := by
  classical
  have h2 : (2 * u : 𝓞 E) = (2 : ℤ) • u := by simp
  rw [Algebra.norm_eq_matrix_det (RingOfIntegers.basis E), map_add, map_one, h2, map_smul,
    Matrix.det_one_add_smul, Algebra.trace_eq_matrix_trace (RingOfIntegers.basis E)]
  generalize Polynomial.eval (2 : ℤ) _ = c
  exact ⟨c, by ring⟩

theorem det_interp_pm {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    (D : Datum H) {r : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℤ D.La)
    (gam : D.La ≃ₗ[𝓞 E] D.La) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (A : Matrix (Fin r) (Fin r) E)
    (hinj : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hA : ∀ x, φ (gam x) = A *ᵥ φ x)
    (hdet : A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E))
    (T : D.La →ₗ[ℤ] D.La) (hT : ∀ x, T x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x)) :
    (4 : ℤ) ∣ (LinearMap.toMatrix b b T).det - 1 := by
  have hsm : ∀ (a : 𝓞 E) (x : D.La), φ (a • x) = (a : E) • φ x := fun a x => by
    rw [map_smul]; rfl
  haveI := D.fin
  have hfg : (LinearMap.range φ).FG := by
    rw [LinearMap.range_eq_map]
    exact Module.Finite.fg_top.map φ
  obtain ⟨he0, t, ht⟩ := cmUnit_pow_four_idempotent_mod_eight H
  have h := det_eq_norm b φ hinj hspan T
    (((H.w0 ^ 4 : 𝓞 E) : E) • A + (1 - ((H.w0 ^ 4 : 𝓞 E) : E)) • 1) (by
      intro x
      rw [hT, map_add, map_sub, hsm, hsm, Matrix.add_mulVec, Matrix.smul_mulVec,
        Matrix.smul_mulVec, hA, Matrix.one_mulVec, sub_smul, one_smul])
  have hst : ∀ v ∈ LinearMap.range φ, A *ᵥ v ∈ LinearMap.range φ := by
    rintro _ ⟨x, rfl⟩
    exact ⟨gam x, hA x⟩
  rcases hdet with hdet | ⟨hdet, h4⟩
  · obtain ⟨y, hy⟩ := det_interp_gen 8 (by norm_num) _ t 1 he0 ht (LinearMap.range φ) A hfg hspan
      hst (by simpa using hdet)
    rw [hy, ← Algebra.coe_norm_int] at h
    have h1 : (H.w0 ^ 4 * 1 + (1 - H.w0 ^ 4) + (8 : ℕ) * y : 𝓞 E) = 1 + 2 * ((4 : ℤ) • y) := by
      rw [zsmul_eq_mul]
      push_cast
      ring
    have h2 := norm_one_add_two ((4 : ℤ) • y)
    rw [Int.cast_injective h, h1]
    rw [map_zsmul, smul_eq_mul] at h2
    omega
  · obtain ⟨m, hm, hpow⟩ := hdet
    have hi : IsIntegral ℤ A.det := IsIntegral.of_pow hm (hpow ▸ isIntegral_one)
    obtain ⟨δ, hδ⟩ : ∃ δ : 𝓞 E, (δ : E) = A.det := ⟨⟨_, hi⟩, rfl⟩
    obtain ⟨y, hy⟩ := det_interp_gen 8 (by norm_num) _ t δ he0 ht (LinearMap.range φ) A hfg hspan hst hδ.symm
    rw [hy, ← Algebra.coe_norm_int] at h
    have hrt : (H.rt : E) ^ 2 = -(H.d : E) := by
      have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
      simpa using this
    have hN := UpperTheory.norm_root_of_unity_quadratic_subfield E (H.rt : E) H.d H.d_prime (by have := H.d_mod; omega) hrt h4 (δ : E)
      ⟨m, hm, by rw [hδ, hpow]⟩
    have hw : ((H.w0 ^ 4 : 𝓞 E) : E) ∈ IntermediateField.adjoin ℚ {(H.rt : E)} := by
      have h2 : (H.w0 : E) = (1 + (H.rt : E)) / ((2 : ℕ) : E) := by
        have h3 : (2 : E) * (H.w0 : E) = 1 + (H.rt : E) := by
          have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
          rwa [map_mul, map_add, map_one, map_ofNat] at this
        rw [← h3]
        push_cast
        ring
      have h4' : ((H.w0 ^ 4 : 𝓞 E) : E) = (H.w0 : E) ^ 4 := by push_cast; rfl
      rw [h4', h2]
      exact pow_mem (div_mem (add_mem (one_mem _) (IntermediateField.mem_adjoin_simple_self _ _)) (natCast_mem _ 2)) 4
    have h8 := UpperTheory.dvd_norm_sub_one_of_idempotent_interpolation_relNorm_one E _ 8 _ t δ y hw ht hN
    rw [Int.cast_injective h]
    exact (show (4 : ℤ) ∣ ((8 : ℕ) : ℤ) by norm_num).trans h8

theorem blocks_det_mod_four : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (g r : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] D.La) (gam : D.La ≃ₗ[𝓞 E] D.La) (N : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℤ) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (A : Matrix (Fin r) (Fin r) E), (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inl k) 1) = bas (Pi.single (Sum.inl k) 1) + (8 : ℕ) • e) ∧ (∀ k, ∃ e, H.w0 ^ 4 • bas (Pi.single (Sum.inr k) 1) = (8 : ℕ) • e) → Function.Injective φ → Submodule.span E (Set.range φ) = ⊤ → (∀ a, φ (gam a) = A *ᵥ φ a) → (A.det = 1 ∨ ((∃ m : ℕ, 0 < m ∧ A.det ^ m = 1) ∧ 4 ∣ Module.finrank ℚ E)) → (∀ u v, N u v = bas.symm (gam (bas (Pi.single v 1))) u) → (∀ i j, (8 : ℤ) ∣ N (Sum.inl i) (Sum.inr j) ∧ (8 : ℤ) ∣ N (Sum.inr i) (Sum.inl j)) ∧ (4 : ℤ) ∣ N.toBlocks₁₁.det - 1 := by
  intro E _ _ _ H D g r bas gam N φ A ⟨hl, hr⟩ hinj hspan hA hdet hN
  classical
  let π : D.La →+ (Fin g ⊕ Fin g → ZMod 8) :=
    { toFun := fun x u => ((bas.symm x u : ℤ) : ZMod 8)
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp }
  have hπ : ∀ x u, π x u = ((bas.symm x u : ℤ) : ZMod 8) := fun _ _ => rfl
  have h8 : ∀ x, π ((8 : ℕ) • x) = 0 := fun x => by
    rw [map_nsmul]
    ext u
    rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul, Pi.zero_apply]
  have hπb : ∀ v u, π (bas (Pi.single v 1)) u = if u = v then 1 else 0 := fun v u => by
    simp [hπ, Pi.single_apply]

  have he : ∀ x u, π (H.w0 ^ 4 • x) u = Sum.elim (fun _ => π x u) (fun _ => 0) u := by
    intro x u
    obtain ⟨c, rfl⟩ := bas.surjective x
    induction c using Pi.single_induction with
    | zero => cases u <;> simp
    | add a b ha hb => rw [map_add, smul_add, map_add, map_add, Pi.add_apply, ha, hb]; cases u <;> simp
    | single v n =>
      have : (Pi.single v n : Fin g ⊕ Fin g → ℤ) = n • Pi.single v 1 := by
        rw [← Pi.single_smul, smul_eq_mul, mul_one]
      rw [this, map_zsmul, smul_comm, map_zsmul, map_zsmul, Pi.smul_apply, Pi.smul_apply]
      cases v with
      | inl k =>
        obtain ⟨e, h⟩ := hl k
        rw [h, map_add, h8, add_zero]
        cases u <;> simp [hπb]
      | inr k =>
        obtain ⟨e, h⟩ := hr k
        rw [h, h8]
        cases u <;> simp [hπb]
  have hN' : ∀ u v, ((N u v : ℤ) : ZMod 8) = π (gam (bas (Pi.single v 1))) u := fun u v => by
    rw [hN, hπ]
  constructor
  · intro i j
    constructor
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
      obtain ⟨e, h⟩ := hr j
      have h1 := he (gam (bas (Pi.single (Sum.inr j) 1))) (Sum.inl i)
      rw [← map_smul, h, map_nsmul, h8] at h1
      rw [hN']
      exact h1.symm
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
      obtain ⟨e, h⟩ := hl j
      have h1 := he (gam (bas (Pi.single (Sum.inl j) 1))) (Sum.inr i)
      rw [← map_smul, h, map_add, map_nsmul, map_add, h8, add_zero] at h1
      rw [hN']
      exact h1
  · let b : Module.Basis (Fin g ⊕ Fin g) ℤ D.La := (Pi.basisFun ℤ _).map bas
    let T : D.La →ₗ[𝓞 E] D.La :=
      H.w0 ^ 4 • gam.toLinearMap + (LinearMap.id - H.w0 ^ 4 • LinearMap.id)
    have hT : ∀ x, T.restrictScalars ℤ x = H.w0 ^ 4 • gam x + (x - H.w0 ^ 4 • x) := fun x => rfl
    have h := det_interp_pm D b gam φ A hinj hspan hA hdet (T.restrictScalars ℤ) hT
    suffices h8 : (8 : ℤ) ∣ N.toBlocks₁₁.det - (LinearMap.toMatrix b b (T.restrictScalars ℤ)).det by
      omega
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 8).mp
    rw [Int.cast_sub, sub_eq_zero, ← eq_intCast (Int.castRingHom (ZMod 8)),
      ← eq_intCast (Int.castRingHom (ZMod 8)), RingHom.map_det, RingHom.map_det]
    have hent : ∀ u v, (Int.castRingHom (ZMod 8)).mapMatrix
        (LinearMap.toMatrix b b (T.restrictScalars ℤ)) u v =
        π (T.restrictScalars ℤ (bas (Pi.single v 1))) u := fun u v => by
      simp [LinearMap.toMatrix_apply, b, hπ]
    have hblk : (Int.castRingHom (ZMod 8)).mapMatrix
        (LinearMap.toMatrix b b (T.restrictScalars ℤ)) =
        Matrix.fromBlocks ((Int.castRingHom (ZMod 8)).mapMatrix N.toBlocks₁₁)
          (Matrix.of fun i j => (Int.castRingHom (ZMod 8)).mapMatrix
            (LinearMap.toMatrix b b (T.restrictScalars ℤ)) (Sum.inl i) (Sum.inr j)) 0 1 := by
      ext u v
      rcases u with i | i <;> rcases v with j | j
      · rw [hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [Matrix.toBlocks₁₁, hN']
      · rfl
      · rw [hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [hπb]
      · rw [hent, hT, map_add, map_sub, Pi.add_apply, Pi.sub_apply, he, he]
        simp [hπb, Matrix.one_apply]
    rw [hblk, Matrix.det_fromBlocks_zero₂₁, det_one, mul_one]

end GlobalTheory.AdaptedDetSign
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedFinitenessSeparableNorm
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.TwFinGL

theorem twFin_generic : ∀ {H : Type} [Group H] (θ : H →* H) (K₀ : Subgroup H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ k ∈ K₀, θ k ∈ K₀) → (∀ g : H, Subgroup.Commensurable (K₀.map (MulAut.conj g).toMonoidHom) K₀) →
    (∀ a ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, ∀ b ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}, a * b = b * a) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ}) ∧
      Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} ≤
        Subgroup.closure ((G : Set H) ∪ ((Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} ⊓ K₀ : Subgroup H) : Set H))) →
    GlobalTheory.TwFin.TwFin θ K₀ δ (GlobalTheory.LKMid.nrmG θ r δ) := by
  intro H _ θ K₀ δ r hr hθr hθK hcomm hZc hfg
  obtain ⟨hτZ, hτr⟩ := GlobalTheory.T.twisted_centralizer_norm_invariant θ δ r hr hθr
  obtain ⟨U, hUZ, hUK, hUτ, hUfg, hUcov⟩ :=
    GlobalTheory.T.twisted_norm_fixed_decomposition θ K₀ δ r hr hθr hθK hcomm _ hτZ hτr hfg
  intro E
  choose! F hF using hUcov
  obtain ⟨S, hS⟩ := GlobalTheory.T.twisted_fixed_coset_decomposition _ U ((MulAut.conj δ).toMonoidHom.comp θ) r hr hτZ hτr hZc hUZ hUτ hUfg
    (E.biUnion fun e => F e δ⁻¹)
  refine ⟨S, ?_⟩
  intro t htN hE
  obtain ⟨e, he, k, hk, hek⟩ := hE
  have htZ : t ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]; exact htN.symm
  have hτt : ((MulAut.conj δ).toMonoidHom.comp θ) t = δ * θ t * δ⁻¹ := rfl
  have hc : t⁻¹ * ((MulAut.conj δ).toMonoidHom.comp θ) t ∈ Subgroup.centralizer {GlobalTheory.LKMid.nrmG θ r δ} :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ htZ) (hτZ t htZ)
  have hc' : t⁻¹ * ((MulAut.conj δ).toMonoidHom.comp θ) t = e * k * δ⁻¹ := by
    rw [hτt, ← mul_assoc, ← mul_assoc, hek]
  obtain ⟨f, hf, u, hu, hfu⟩ := hF e δ⁻¹ _ hc k hk hc'
  obtain ⟨b, -, hbτ, s, hs, u', hu', hbt⟩ :=
    hS t htZ ⟨f, Finset.mem_biUnion.2 ⟨e, he, hf⟩, u, hu, hfu⟩
  refine ⟨b, ?_, s, hs, u', hUK hu', hbt⟩
  change b * δ = δ * θ b
  have h1 : δ * θ b * δ⁻¹ = b := hbτ
  calc b * δ = δ * θ b * δ⁻¹ * δ := by rw [h1]
    _ = δ * θ b := by rw [inv_mul_cancel_right]

theorem main : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)), FiniteDimensional ℚ_[p] K → ∀ (n r : ℕ), 0 < r → ∀ δ : GL (Fin n) (KQ p K r), (nrmRes p K n r δ).val.charpoly.Separable → GlobalTheory.TwFin.TwFin (sigRes p K n r) (Kres p K n r) δ (nrmRes p K n r δ) := by
  intro p _ K hK n r hr δ hsep
  haveI := hK
  exact twFin_generic (sigRes p K n r) (Kres p K n r) δ r hr (sigRes_iterate_eq_self p K n r hr)
    (sigRes_mem_Kres p K n r) (fun g => GlobalTheory.HeckeP.Kres_commensurable p K n r hr g)
    (GlobalTheory.T.separable_centralizer_commutative p K hK n r hr _ hsep) (GlobalTheory.T.centralizer_finitely_generated_mod_open p K hK n r hr _ hsep)

end GlobalTheory.TwFinGL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoPiMulWeightLengthLeMaxWeightDegreeSq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj

namespace GlobalTheory.TopDegLower

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

theorem lR_last_ge (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau)
    (i : Fin (D.R.sigW j).1) (hi : i.1 + 1 = (D.R.sigW j).1) :
    Tp.TO ≤ (lR Tp hK j).aP τ i + 1 := by
  have hn : ¬ i.1 + 1 < (D.R.sigW j).1 := by omega
  have hk := GlobalTheory.DepthBoundProbe.kappa_last Tp hK hj τ i hi
  show Tp.TO ≤ ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn τ) i + 1
  rw [ofGaps_last _ _ hn]
  unfold lGapP
  rw [if_neg hn]
  have hp : (0 : ℤ) < (WeightAlgebra.Tp D j Tp.TO : ℤ) := by unfold WeightAlgebra.Tp; push_cast; omega
  rw [Int.fdiv_eq_ediv_of_nonneg _ hp.le]
  have h1 : ((Tp.Dp : ℤ) + 2) * Tp.nWn + 2 * D.R.r ≤ Tp.TO := by exact_mod_cast Tp.TO_nW
  have h40 : 40 * ((Tp.Dp : ℤ) + 2) ≤ Tp.TO := by exact_mod_cast Tp.TO_40
  have : (Tp.TO : ℤ) - 1 ≤ (((kaR Tp hK j).aP τ i : ℤ) - ((WeightFamilies.dimY D j : ℤ) + 2) * Tp.nWn - 2 * D.R.r) /
      (WeightAlgebra.Tp D j Tp.TO : ℤ) := by
    rw [Int.le_ediv_iff_mul_le hp]
    unfold WeightAlgebra.Tp
    rw [GlobalTheory.DepthBoundProbe.dimY_eq Tp hj]
    push_cast
    have hD : (0 : ℤ) ≤ Tp.Dp := Int.natCast_nonneg _
    have h2 : ((Tp.TO : ℤ) - 1) * ((Tp.Dp : ℤ) + 2) ≤ ((Tp.TO : ℤ) - 1) * Tp.TO :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    nlinarith
  omega

theorem DF_ge (Tp : ParamsT D L P) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau) :
    Tp.TO ≤ WeightAlgebra.DF (lR Tp hK j) + 1 := by
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h1 := lR_last_ge Tp hK hj τ ⟨(D.R.sigW j).1 - 1, by omega⟩ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  refine h1.trans (Nat.add_le_add_right ?_ 1)
  unfold WeightAlgebra.DF WeightAlgebra.degP
  refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, (lR Tp hK j).aP τ i) + ∑ i, (lR Tp hK j).aM τ i)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ τ))
  exact le_trans (Finset.single_le_sum (f := fun i => (lR Tp hK j).aP τ i) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ _)) (Nat.le_add_right _ _)

theorem two_pi_nW_le_topDeg_sq : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D),
    2 * Real.pi * (Tp.nWn : ℝ) ≤ (GlobalTheory.IndexAssembly.topDeg Tp hK : ℝ) ^ 2 := by
  intro D L Pm Tp hK
  have hj : InR D 1 := ⟨le_rfl, by have := D.R.two_le_m; omega⟩
  obtain ⟨τ, -⟩ := GlobalTheory.FinalJoin.RecordRun.exists_thick L
  have h1 := DF_ge Tp hK hj τ
  have h2 : WeightAlgebra.DF (lR Tp hK 1) ≤ GlobalTheory.IndexAssembly.topDeg Tp hK := GlobalTheory.IndexAssembly.le_topDeg Tp hK hj
  have h3 : 2 * Tp.nWn ≤ Tp.TO := by
    have := Tp.TO_nW
    nlinarith [Nat.zero_le (Tp.Dp * Tp.nWn)]
  have h4 : 40 ≤ Tp.TO := by have := Tp.TO_40; omega
  have a : (Tp.TO : ℝ) ≤ (GlobalTheory.IndexAssembly.topDeg Tp hK : ℝ) + 1 := by
    exact_mod_cast h1.trans (Nat.add_le_add_right h2 1)
  have b : 2 * (Tp.nWn : ℝ) ≤ Tp.TO := by exact_mod_cast h3
  have c : (40 : ℝ) ≤ Tp.TO := by exact_mod_cast h4
  have hpi := Real.pi_le_four
  have hn : (0 : ℝ) ≤ Tp.nWn := Nat.cast_nonneg _
  have d : 2 * Real.pi * (Tp.nWn : ℝ) ≤ 4 * Tp.TO := by nlinarith
  nlinarith

end GlobalTheory.TopDegLower
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCuspidalSatakeParameterStarEqInvStatement
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_cuspidal_satake_parameter_star_eq_inv : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (H : π.V →ₗ⋆[ℂ] π.V →ₗ[ℂ] ℂ), (∀ φ ψ, starRingEnd ℂ (H φ ψ) = H ψ φ) → (∀ φ, φ ≠ 0 → 0 < (H φ φ).re) → (∀ k φ ψ, H (π.op (.fin k) φ) (π.op (.fin k) ψ) = H φ ψ) → ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w (π.locRep w) B → B.map star = B.map (·⁻¹) := by
  first | exact @GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form | exact GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form | (intros; apply GlobalTheory.CuspRep.UnitaryParam.map_star_eq_map_inv_of_form <;> assumption)
end

