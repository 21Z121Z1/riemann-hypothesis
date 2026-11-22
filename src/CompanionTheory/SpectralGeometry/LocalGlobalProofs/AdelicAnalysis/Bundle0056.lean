import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0054
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0053
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0025
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0045
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0037

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GramCoordinatesMeasurableStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_coordinates_measurable : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (e : Ainf F ≃+* (InfinitePlace F → ℝ)), IsHomeomorph e → (∀ w p q, Measurable fun ω => ginf e σ J b ω w p q) ∧ (∀ p q, Measurable fun ω => gfin σ J b ω p q) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable | exact GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable | (intros; apply GlobalTheory.CompanionTheory.SW.BB.ginf_gfin_measurable <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarScalingUnderFlow
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Flow

theorem map_eq_of_conj {G H : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [MeasurableSpace G] [BorelSpace G] [AddCommGroup H] [TopologicalSpace H] [IsTopologicalAddGroup H]
    [MeasurableSpace H] [BorelSpace H] (e : G ≃+ H) (he : Continuous e) (hs : Continuous e.symm)
    (L : G → G) (L' : H → H) (hL' : Continuous L') (hc : ∀ X, e (L X) = L' (e X)) (c : ℝ≥0∞)
    (hH : ∀ ν : Measure H, ν.IsAddHaarMeasure → ν.map L' = c • ν)
    (μ : Measure G) [μ.IsAddHaarMeasure] : μ.map L = c • μ := by
  have hL : Continuous L := by
    have : L = fun X => e.symm (L' (e X)) := by
      funext X; rw [← hc, AddEquiv.symm_apply_apply]
    rw [this]
    exact hs.comp (hL'.comp he)
  have hν := hH (μ.map e) (e.isAddHaarMeasure_map μ he hs)
  have h1 : (μ.map L).map e = (c • μ).map e := by
    rw [Measure.map_map he.measurable hL.measurable, Measure.map_smul, ← hν,
      Measure.map_map hL'.measurable he.measurable]
    congr 1
    funext X
    exact hc X
  have h2 : ((μ.map L).map e).map e.symm = ((c • μ).map e).map e.symm := by rw [h1]
  rw [Measure.map_map hs.measurable he.measurable, Measure.map_map hs.measurable he.measurable] at h2
  have hid : (e.symm ∘ e : G → G) = id := by funext X; simp
  rwa [hid, Measure.map_id, Measure.map_id] at h2

section Coord

variable {F E A : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [Algebra F A]

def coordEquiv {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) :
    (Fin n → Fin M → A ⊗[F] E) ≃+ (Fin n × Fin M × Fin d → A) where
  toFun X p := (Algebra.TensorProduct.basis A b).repr (X p.1 p.2.1) p.2.2
  invFun Y a i := (Algebra.TensorProduct.basis A b).equivFun.symm (fun k => Y (a, i, k))
  left_inv X := by
    funext a i
    have := (Algebra.TensorProduct.basis A b).equivFun.symm_apply_apply (X a i)
    simpa using this
  right_inv Y := by
    funext ⟨a, i, k⟩
    have := (Algebra.TensorProduct.basis A b).equivFun.apply_symm_apply (fun k => Y (a, i, k))
    exact congrFun this k
  map_add' X Y := by
    funext p
    simp

theorem coordEquiv_smul {d : ℕ} (b : Module.Basis (Fin d) F E) (n M : ℕ) (a : A)
    (X : Fin n → Fin M → A ⊗[F] E) :
    coordEquiv b n M ((a ⊗ₜ[F] (1 : E)) • X) = fun p => a * coordEquiv b n M X p := by
  funext p
  have h : (a ⊗ₜ[F] (1 : E)) * X p.1 p.2.1 = a • X p.1 p.2.1 := by
    rw [Algebra.smul_def]; rfl
  simp [coordEquiv, h]

end Coord

theorem modulus_flow : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ x : ℝ, μ.map (fun X => ((τ (Multiplicative.ofAdd (x)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • X) = ENNReal.ofReal (Real.exp (-(2 * Module.finrank ℚ F * n * M * x))) • μ := by
  intro F E _ _ _ _ _ σ hcm τ hτ n M μ hμ x
  obtain ⟨⟨hAlc, hAsc, hAt2⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := hAlc
  haveI := hAsc
  haveI := hAt2
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  obtain ⟨hTR, -, -, -, -, -, hHom, hBor, -, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  haveI := hTR
  haveI := hBor n M
  have hd : Module.finrank F E = 2 := hcm.2.2.1
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  let b : Module.Basis (Fin 2) F E := Module.finBasisOfFinrankEq F E hd
  obtain ⟨-, θ, hθ, hτx⟩ := hτ
  have hh := hHom 2 b
  let hm := hh.homeomorph
  have he : Continuous (coordEquiv (A := AF F) b n M) := by
    refine continuous_pi fun p => ?_
    have h1 : Continuous fun X : Fin n → Fin M → AF F ⊗[F] E => X p.1 p.2.1 :=
      (continuous_apply p.2.1).comp (continuous_apply p.1)
    exact (continuous_apply p.2.2).comp (hh.continuous.comp h1)
  have hs : Continuous (coordEquiv (A := AF F) b n M).symm := by
    refine continuous_pi fun a => continuous_pi fun i => ?_
    have h1 : Continuous fun Y : Fin n × Fin M × Fin 2 → AF F => fun k => Y (a, i, k) :=
      continuous_pi fun k => continuous_apply _
    have h2 : (fun Y : Fin n × Fin M × Fin 2 → AF F => (coordEquiv (A := AF F) b n M).symm Y a i) =
        fun Y => hm.symm (fun k => Y (a, i, k)) := by
      funext Y
      apply hm.injective
      rw [Homeomorph.apply_symm_apply]
      funext k
      have := (Algebra.TensorProduct.basis (AF F) b).equivFun.apply_symm_apply (fun k => Y (a, i, k))
      exact congrFun this k
    rw [h2]
    exact hm.symm.continuous.comp h1
  have ht : 0 < Real.exp x := Real.exp_pos x
  refine map_eq_of_conj (coordEquiv (A := AF F) b n M) he hs _
    (fun y p => (show AF F from (θ (Real.exp x), 1)) * y p) ?_ ?_ _ ?_ μ
  · exact continuous_pi fun p => continuous_const.mul (continuous_apply p)
  · intro X
    rw [hτx x]
    exact coordEquiv_smul b n M _ X
  · intro ν hν
    have := GlobalTheory.CompanionTheory.AdelicFlow.map_scalar F hcm.1 θ hθ (Fin n × Fin M × Fin 2) ν (Real.exp x) ht
    rw [this]
    congr 2
    rw [← Real.exp_nat_mul, ← Real.exp_neg]
    congr 1
    simp only [Fintype.card_prod, Fintype.card_fin]
    push_cast
    ring

end GlobalTheory.CompanionTheory.SW.Flow
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LinearChangeEulerProductStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addHaar_map_mulVec_eq_smul_at_all_places : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.det ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ μ : Measure (ι → Ainf F), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Ainf F)) *ᵥ x) = cinf • μ) ∧ ∀ v : HeightOneSpectrum (𝓞 F), (∀ μ : Measure (ι → Fv F v), μ.IsAddHaarMeasure → μ.map (fun x => A.map (algebraMap F (Fv F v)) *ᵥ x) = c v • μ) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ProdFormula.modulus_matrix | exact GlobalTheory.CompanionTheory.SW.ProdFormula.modulus_matrix | (intros; apply GlobalTheory.CompanionTheory.SW.ProdFormula.modulus_matrix <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensitiesBlockOneAlmostAll
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.GoodStep

theorem blockOne_zero_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    blockOne t A 0 0 = t := rfl

theorem blockOne_zero_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) (j : Fin M) :
    blockOne t A 0 j.succ = 0 := rfl

theorem blockOne_succ_zero {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) (i : Fin M) :
    blockOne t A i.succ 0 = 0 := rfl

theorem blockOne_succ_succ {K : Type} [Zero K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) (i j : Fin M) :
    blockOne t A i.succ j.succ = A i j := rfl

theorem det_blockOne {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  have hs : (blockOne t A).submatrix Fin.succ (Fin.succAbove 0) = A := by
    ext i j
    simp [blockOne_succ_succ]
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ, hs]
  simp [blockOne_zero_zero, blockOne_zero_succ]

theorem isHermND_blockOne {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (t : F) (ht : t ≠ 0) :
    IsHermND σ (blockOne (algebraMap F E t) J) := by
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockOne_zero_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simp [blockOne_zero_succ, blockOne_succ_zero]
    · simpa [blockOne_succ_succ] using hJ.1 i j
  · rw [det_blockOne]
    exact mul_ne_zero (by simpa using ht) hJ.2

theorem gram_mulVec_e0 {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) :
    gramR R σ (blockOne (algebraMap F E t) J)
        (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
  ext a c
  show hR R σ _ _ _ = algebraMap F R t ⊗ₜ[F] (1 : E)
  simp only [hR, hform, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, map_one, map_zero, one_mul,
    mul_zero, zero_mul, mul_one, Finset.sum_const_zero, add_zero, JR, Matrix.map_apply,
    blockOne_zero_zero]
  show (1 : R) ⊗ₜ[F] (algebraMap F E t) = _
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
    TensorProduct.smul_tmul']

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem consTup_mem_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k ∈
      v.adicCompletionIntegers F) {n M : ℕ} (X : Fin n → Fin M → Fv F v ⊗[F] E) :
    consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro h a i k
    exact h a.succ i.succ k
  · intro h a i k
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun i => ?_) i
    · exact h1 k
    · show (Algebra.TensorProduct.basis (Fv F v) b).repr (0 : Fv F v ⊗[F] E) k ∈ _
      simp [zero_mem]
    · show (Algebra.TensorProduct.basis (Fv F v) b).repr (0 : Fv F v ⊗[F] E) k ∈ _
      simp [zero_mem]
    · exact h a i k

theorem e0_mem_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (h1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k ∈
      v.adicCompletionIntegers F) {M : ℕ} :
    (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → Fv F v ⊗[F] E)) ∈ latV b v := by
  intro a i k
  refine Fin.cases ?_ (fun i => ?_) i
  · exact h1 k
  · show (Algebra.TensorProduct.basis (Fv F v) b).repr (0 : Fv F v ⊗[F] E) k ∈ _
    simp [zero_mem]

theorem incl_mul_eq_smul (R : Type) [CommRing R] [Algebra F R] (t : F) (y : R ⊗[F] E) :
    inclR R (algebraMap F E t) * y = algebraMap F R t • y := by
  have : inclR R (algebraMap F E t) = algebraMap F R t • (1 : R ⊗[F] E) := by
    show (1 : R) ⊗ₜ[F] (algebraMap F E t) = _
    rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    simp
  rw [this, smul_mul_assoc, one_mul]

theorem coordK_map_unit [NumberField E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ)
    (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (hlam : IsStdV v lam) (t : F) (ht : t ≠ 0)
    (htv : Valued.v (algebraMap F (Fv F v) t) = 1) (d : ℕ) (b : Module.Basis (Fin d) F E) :
    (coordK (Fv F v) b lam).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) =
      (1 : ℝ≥0) • coordK (Fv F v) b lam := by
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨i1, i2, i3, i4, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
  haveI := i1
  haveI := i2
  haveI := i3
  haveI := i4
  haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩
  haveI := hlam.1
  haveI := (GlobalTheory.T.coordinate_haar_measure F E σ hCM (Fv F v) d b lam hlam.1).1
  have hinv : inclR (F := F) (Fv F v) (algebraMap F E t) * inclR (F := F) (Fv F v) (algebraMap F E t⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, mul_inv_cancel₀ ht, map_one, map_one]
  let e : (Fv F v ⊗[F] E) ≃+ (Fv F v ⊗[F] E) :=
    { toFun := fun y => inclR (F := F) (Fv F v) (algebraMap F E t) * y
      invFun := fun y => inclR (F := F) (Fv F v) (algebraMap F E t⁻¹) * y
      left_inv := fun y => by
        show _ * (_ * y) = y
        rw [← mul_assoc, mul_comm (inclR (F := F) (Fv F v) (algebraMap F E t⁻¹)), hinv, one_mul]
      right_inv := fun y => by
        show _ * (_ * y) = y
        rw [← mul_assoc, hinv, one_mul]
      map_add' := fun x y => mul_add _ x y }
  have he : Continuous e := continuous_const.mul continuous_id
  have he' : Continuous e.symm := continuous_const.mul continuous_id
  let L : Set (Fv F v ⊗[F] E) := {y | ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈
    v.adicCompletionIntegers F}
  obtain ⟨c1, c2, c3, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b 1 1 v
  have hLc : IsCompact L := by
    have : L = (fun X : Fin 1 → Fin 1 → Fv F v ⊗[F] E => X 0 0) '' latV b v := by
      ext y
      constructor
      · intro hy
        exact ⟨fun _ _ => y, fun _ _ k => hy k, rfl⟩
      · rintro ⟨X, hX, rfl⟩
        exact fun k => hX 0 0 k
    rw [this]
    exact c1.image (by fun_prop)
  have hLo : IsOpen L := by
    have : L = (fun (y : Fv F v ⊗[F] E) (_ : Fin 1) (_ : Fin 1) => y) ⁻¹' latV b v := by
      ext y
      exact ⟨fun hy _ _ k => hy k, fun hy k => hy 0 0 k⟩
    rw [this]
    exact c2.preimage (by fun_prop)
  have hL0 : L.Nonempty := ⟨0, fun k => c3 0 0 k⟩
  have hmem : ∀ x : Fv F v, algebraMap F (Fv F v) t * x ∈ v.adicCompletionIntegers F ↔
      x ∈ v.adicCompletionIntegers F := by
    intro x
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, HeightOneSpectrum.mem_adicCompletionIntegers,
      map_mul, htv, one_mul]
  have hL : ∀ y, e y ∈ L ↔ y ∈ L := by
    intro y
    have hk : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (e y) k =
        algebraMap F (Fv F v) t * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
      intro k
      show (Algebra.TensorProduct.basis (Fv F v) b).repr (inclR (F := F) (Fv F v) (algebraMap F E t) * y) k = _
      rw [incl_mul_eq_smul, map_smul, Finsupp.smul_apply, smul_eq_mul]
    constructor
    · intro h k
      exact (hmem _).1 (hk k ▸ h k)
    · intro h k
      exact hk k ▸ (hmem _).2 (h k)
  have := (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open _ _ (coordK (Fv F v) b lam) (coordK (Fv F v) b lam) e he he').2 L L hLc hLo hL0 hL rfl
  rw [one_smul]
  exact this

end Place

theorem blockFibre_mass : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m₁ m', IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → m (hermOf (Fv F v) σ _ hT') (latV b v) = m₁ (hermScal (Fv F v) σ (algebraMap F _ t)) (latV b v) * m' (hermOf (Fv F v) σ T hT) (latV b v) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hdet hT' d b
  have hJ' := isHermND_blockOne σ J hJ t ht
  filter_upwards [GlobalTheory.T.lattice_gram_scalar_almost_all F E σ hCM (M + 1) _ hJ' t ht d b,
    (GlobalTheory.T.integral_almost_all_places F E σ hCM d b).1 1, (GlobalTheory.T.integral_almost_all_places F E σ hCM d b).2 t ht] with v hgt h1' htv
  intro lam hlam m m₁ m' hm hm₁ hm'
  have h1 : ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr (1 : Fv F v ⊗[F] E) k ∈
      v.adicCompletionIntegers F := by
    intro k
    simpa using h1' k
  have hlocR := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨r1, r2, r3, r4, -⟩ := id hlocR
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, -, -, -, -, hB, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Fv F v)
  have hmeas : ∀ p q : ℕ, MeasurableSet (latV (M := q) (n := p) b v) := by
    intro p q
    haveI := hB p q
    exact (GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hCM d b p q v).2.1.measurableSet
  have hc := coordK_map_unit σ hCM v lam hlam t ht htv d b
  let φ : (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞ := (latV b v).indicator 1
  have hφ : Measurable φ := measurable_one.indicator (hmeas _ _)
  obtain ⟨Ψ, -, hΨ, hint⟩ := GlobalTheory.T.local_density_block_one_product F E σ hCM M J hJ t ht n T hT hdet hT' (Fv F v) hlocR d b lam
    hlam.1 m m₁ m' hm hm₁ hm' 1 hc φ hφ
  have hae : Ψ =ᵐ[m₁ (hermScal (Fv F v) σ (algebraMap F _ t))]
      (latV b v).indicator (fun _ => m' (hermOf (Fv F v) σ T hT) (latV b v)) := by
    filter_upwards [mem_ae_iff.2 (hm₁.1 (hermScal (Fv F v) σ (algebraMap F _ t)))] with y hy
    have hg : gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y =
        (hermScal (Fv F v) σ (algebraMap F _ t) : HermR (Fv F v) σ 1) := hy.1
    have hu : IsUnit (gramR (Fv F v) σ (blockOne (algebraMap F E t) J) y).det := hy.2
    have hg0 := gram_mulVec_e0 (Fv F v) σ J t
    by_cases hyL : y ∈ latV b v
    · obtain ⟨h, hh, hpres⟩ := hgt _ y (e0_mem_latV b v h1) hyL hg0 (hg.trans hg0.symm)
      rw [Set.indicator_of_mem hyL, ← hh, hΨ h]
      have : (fun X => φ (actW (Fv F v) σ _ h (consTup X))) = (latV b v).indicator 1 := by
        funext X
        by_cases hX : X ∈ latV b v
        · rw [Set.indicator_of_mem hX]
          exact Set.indicator_of_mem ((hpres _ _).2 ((consTup_mem_latV b v h1 X).2 hX)) _
        · rw [Set.indicator_of_notMem hX]
          exact Set.indicator_of_notMem (fun hc' => hX ((consTup_mem_latV b v h1 X).1 ((hpres _ _).1 hc'))) _
      rw [this, lintegral_indicator_one (hmeas _ _)]
    · obtain ⟨h, hh⟩ := GlobalTheory.T.witt_extension_artinian_ring F E σ hCM (M + 1) _ hJ' (Fv F v) 1 _ y (hg0.trans hg.symm)
        (by rw [hg0, ← hg]; exact hu)
      rw [Set.indicator_of_notMem hyL, ← hh, hΨ h]
      have : (fun X => φ (actW (Fv F v) σ _ h (consTup X))) = 0 := by
        funext X
        refine Set.indicator_of_notMem (fun hc' => hyL ?_) _
        intro a i k
        have ha : a = 0 := Subsingleton.elim _ _
        subst ha
        rw [← hh]
        exact hc' 0 i k
      rw [this, lintegral_zero_fun]
  have e1 : ∫⁻ X, φ X ∂(m (hermOf (Fv F v) σ _ hT')) = m (hermOf (Fv F v) σ _ hT') (latV b v) :=
    lintegral_indicator_one (hmeas _ _)
  rw [← e1, hint, lintegral_congr_ae hae, lintegral_indicator_const (hmeas _ _)]
  simp [mul_comm]

end GlobalTheory.CompanionTheory.SW.GoodStep
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalDensityBlockOneEventuallyStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_block_one_eventually : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b), T.det ≠ 0 → ∀ (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b) (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam : Measure (Fv F v), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) (n + 1) (coordW (Fv F v) b lam (n + 1) (M + 1)) (coordHerm (Fv F v) σ b lam (n + 1)) m → IsGramFib (Fv F v) σ (blockOne (algebraMap F E t) J) 1 (coordW (Fv F v) b lam 1 (M + 1)) (coordHerm (Fv F v) σ b lam 1) m₁ → IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ c : ℝ≥0, (coordK (Fv F v) b lam).map (fun y => inclR (Fv F v) (algebraMap F E t) * y) = c • coordK (Fv F v) b lam → m (hermOf (Fv F v) σ _ hT') (latV b v) = (c : ℝ≥0∞) ^ n * (m' (hermOf (Fv F v) σ T hT) (latV b v) * m₁ (hermScal (Fv F v) σ (algebraMap F (Fv F v) t)) (latV b v)) := by
  first | exact @GlobalTheory.CompanionTheory.SW.GoodMass.good_mass | exact GlobalTheory.CompanionTheory.SW.GoodMass.good_mass | (intros; apply GlobalTheory.CompanionTheory.SW.GoodMass.good_mass <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalGramFiberMeasuresAgreeAlmostAll
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem lattice_mass_fibre_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (J' : Matrix (Fin M) (Fin M) E), IsHermND σ J' → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ n : ℕ, ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ lam, IsStdV v lam → ∀ m m', IsGramFib (Fv F v) σ J n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m → IsGramFib (Fv F v) σ J' n (coordW (Fv F v) b lam n M) (coordHerm (Fv F v) σ b lam n) m' → ∀ S, m S (latV b v) = m' S (latV b v) := by
  intro F E _ _ _ _ _ σ hσ M J hJ J' hJ' d b n
  filter_upwards [GlobalTheory.T.hermitian_forms_integrally_equivalent_almost_all F E σ hσ M J hJ J' hJ' d b] with v hv
  intro lam hlam m m' hm hm' S
  obtain ⟨g, hg, hlat⟩ := hv
  have hL := GlobalTheory.T.completion_is_local_ring F v
  obtain ⟨h1, h2, h3, h4, -⟩ := id hL
  haveI := h1
  haveI := h2
  haveI := h3
  haveI := h4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨t1, t2, t3, t4, -, -, -, t8, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)
  haveI := t1
  haveI := t2
  haveI := t3
  haveI := t4
  haveI := t8 n M
  haveI := hlam.1
  obtain ⟨-, c2, c3⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hσ (Fv F v) d b lam hlam.1
  haveI := c2 n M
  obtain ⟨a1, a2, a3, -⟩ := GlobalTheory.T.local_lattice_compact_open_unit_volume F E σ hσ d b n M v
  have hcont : ∀ k : GL (Fin M) (Fv F v ⊗[F] E),
      Continuous (actTup (Fv F v) (n := n) k) := by
    intro k
    refine continuous_pi fun a => ?_
    exact Continuous.matrix_mulVec continuous_const ((continuous_apply a))
  have hinv : ∀ (k l : GL (Fin M) (Fv F v ⊗[F] E)), k * l = 1 → ∀ X : Fin n → Fin M → Fv F v ⊗[F] E,
      actTup (Fv F v) k (actTup (Fv F v) l X) = X := by
    intro k l hkl X
    funext a
    have h : (k : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) * (l : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) = 1 := by
      rw [← Units.val_mul, hkl, Units.val_one]
    simp only [actTup, Matrix.mulVec_mulVec, h, Matrix.one_mulVec]
  let e : (Fin n → Fin M → Fv F v ⊗[F] E) ≃+ (Fin n → Fin M → Fv F v ⊗[F] E) :=
    { toFun := actTup (Fv F v) g
      invFun := actTup (Fv F v) g⁻¹
      left_inv := hinv g⁻¹ g (inv_mul_cancel g)
      right_inv := hinv g g⁻¹ (mul_inv_cancel g)
      map_add' := by
        intro X Y
        funext a
        simp only [actTup, Pi.add_apply, Matrix.mulVec_add] }
  have hmap : (coordW (Fv F v) b lam n M).map e = coordW (Fv F v) b lam n M :=
    (GlobalTheory.T.map_addHaar_addEquiv_eq_smul_and_eq_of_compact_open _ _ (coordW (Fv F v) b lam n M) (coordW (Fv F v) b lam n M) e (hcont g)
      (hcont g⁻¹)).2 (latV b v) (latV b v) a1 a2 ⟨0, a3⟩ (hlat n) rfl
  have hfib := GlobalTheory.T.gram_fiber_measures_change_of_form F E σ hσ M J hJ J' hJ' (Fv F v) hL n (coordW (Fv F v) b lam n M)
    (coordHerm (Fv F v) σ b lam n) m (c2 n M) (c3 n) hm (coordW (Fv F v) b lam n M) m' (c2 n M) hm' g hg 1
    (by rw [one_smul]; exact hmap) S
  have hval := congrArg (fun μ => μ (latV b v)) hfib
  simp only [one_smul] at hval
  rw [Measure.map_apply (hcont g).measurable a2.measurableSet] at hval
  have hpre : actTup (Fv F v) (n := n) g ⁻¹' latV (M := M) (n := n) b v = latV b v := by
    ext X
    exact hlat n X
  rw [hpre] at hval
  exact hval.symm

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.UnitaryGroupFiniteVolumeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_group_finite_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → FinVol F E σ M J := by
  first | exact @GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup | exact GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup | (intros; apply GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup <;> assumption)
end

