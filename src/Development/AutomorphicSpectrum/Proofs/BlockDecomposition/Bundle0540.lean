import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0529
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianHaarSplitsArchTimesFinite
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm

open Topology

section Tensor

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

abbrev tm (E : Type) [Field E] [Algebra F E] (f : R →ₐ[F] R') : R ⊗[F] E →ₐ[F] R' ⊗[F] E :=
  Algebra.TensorProduct.map f (AlgHom.id F E)

theorem repr_tm (f : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (tm E f y) k =
      f ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp [hx, hy]

theorem tm_sig (f : R →ₐ[F] R') (σ : E →ₐ[F] E) (y : R ⊗[F] E) :
    tm E f (sigR R σ y) = sigR R' σ (tm E f y) := by
  simp only [sigR, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply]
  congr 1
  ext <;> simp

end Tensor

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def joinT {d : ℕ} (b : Module.Basis (Fin d) F E) (x : Ainf F ⊗[F] E) (y : Af F ⊗[F] E) : AF F ⊗[F] E :=
  (Algebra.TensorProduct.basis (AF F) b).repr.symm
    (Finsupp.equivFunOnFinite.symm fun k =>
      pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr x k)
        ((Algebra.TensorProduct.basis (Af F) b).repr y k))

theorem repr_joinT {d : ℕ} (b : Module.Basis (Fin d) F E) (x : Ainf F ⊗[F] E) (y : Af F ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (AF F) b).repr (joinT b x y) k =
      pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr x k)
        ((Algebra.TensorProduct.basis (Af F) b).repr y k) := by
  simp [joinT]

theorem tm_fst_joinT {d : ℕ} (b : Module.Basis (Fin d) F E) (x : Ainf F ⊗[F] E) (y : Af F ⊗[F] E) :
    tm E (fstA F) (joinT b x y) = x := by
  apply (Algebra.TensorProduct.basis (Ainf F) b).repr.injective
  ext k
  rw [repr_tm, repr_joinT]
  rfl

theorem tm_snd_joinT {d : ℕ} (b : Module.Basis (Fin d) F E) (x : Ainf F ⊗[F] E) (y : Af F ⊗[F] E) :
    tm E (sndA F) (joinT b x y) = y := by
  apply (Algebra.TensorProduct.basis (Af F) b).repr.injective
  ext k
  rw [repr_tm, repr_joinT]
  rfl

theorem tm_ext {d : ℕ} (b : Module.Basis (Fin d) F E) {u v : AF F ⊗[F] E}
    (h1 : tm E (fstA F) u = tm E (fstA F) v) (h2 : tm E (sndA F) u = tm E (sndA F) v) : u = v := by
  apply (Algebra.TensorProduct.basis (AF F) b).repr.injective
  ext k
  have e1 := congrArg (fun w => (Algebra.TensorProduct.basis (Ainf F) b).repr w k) h1
  have e2 := congrArg (fun w => (Algebra.TensorProduct.basis (Af F) b).repr w k) h2
  simp only [repr_tm] at e1 e2
  exact Prod.ext e1 e2

def hermJoin {d : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) {n : ℕ}
    (p : HermR (Ainf F) σ n × HermR (Af F) σ n) : HermR (AF F) σ n :=
  ⟨Matrix.of fun i j => joinT b ((p.1 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j)
      ((p.2 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j), by
    intro i j
    apply tm_ext b
    · simp only [Matrix.of_apply]
      rw [tm_sig, tm_fst_joinT, tm_fst_joinT]
      exact p.1.2 i j
    · simp only [Matrix.of_apply]
      rw [tm_sig, tm_snd_joinT, tm_snd_joinT]
      exact p.2.2 i j⟩

def hermSplit {d : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E) (n : ℕ) :
    HermR (AF F) σ n ≃+ HermR (Ainf F) σ n × HermR (Af F) σ n where
  toFun x := (hermInf σ x, hermFin σ x)
  invFun := hermJoin b σ
  left_inv x := by
    apply Subtype.ext
    ext i j
    apply tm_ext b
    · exact tm_fst_joinT b _ _
    · exact tm_snd_joinT b _ _
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext i j
      exact tm_fst_joinT b _ _
    · ext i j
      exact tm_snd_joinT b _ _
  map_add' x y := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · ext i j
      simp [hermInf]
    · ext i j
      simp [hermFin]

end Adelic

section Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem finite_of_cm {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) : Module.Finite F E :=
  Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)

theorem continuous_tm {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {R R' : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    [CommRing R'] [Algebra F R'] [TopologicalSpace R'] [IsTopologicalRing R'] [LocallyCompactSpace R']
    [SecondCountableTopology R'] [T2Space R'] (f : R →ₐ[F] R') (hf : Continuous f) :
    Continuous (tm E f) := by
  haveI := finite_of_cm hCM
  have h1 := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R).2.2.2.2.2.2.1 _ (Module.finBasis F E)
  have h2 := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R').2.2.2.2.2.2.1 _ (Module.finBasis F E)
  rw [h2.isEmbedding.continuous_iff]
  refine continuous_pi fun k => ?_
  simp only [Function.comp_def, repr_tm]
  exact hf.comp ((continuous_apply k).comp h1.continuous)

theorem continuous_joinT {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E)
    {X : Type} [TopologicalSpace X] {f : X → Ainf F ⊗[F] E} {g : X → Af F ⊗[F] E}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => joinT b (f x) (g x) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  have h0 := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (AF F)).2.2.2.2.2.2.1 _ b
  have h1 := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)).2.2.2.2.2.2.1 _ b
  have h2 := (GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Af F)).2.2.2.2.2.2.1 _ b
  rw [h0.isEmbedding.continuous_iff]
  refine continuous_pi fun k => ?_
  simp only [Function.comp_def, repr_joinT]
  exact (((continuous_apply k).comp h1.continuous).comp hf).prodMk
    (((continuous_apply k).comp h2.continuous).comp hg)

theorem herm_facts {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (n : ℕ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R] :
    IsTopologicalAddGroup (HermR R σ n) ∧ LocallyCompactSpace (HermR R σ n) ∧
      SecondCountableTopology (HermR R σ n) ∧ T2Space (HermR R σ n) := by
  obtain ⟨h1, h2, h3, h4, -, -, -, -, h9, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  haveI : IsTopologicalRing (R ⊗[F] E) := h1
  haveI : LocallyCompactSpace (R ⊗[F] E) := h2
  haveI : SecondCountableTopology (R ⊗[F] E) := h3
  haveI : T2Space (R ⊗[F] E) := h4
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → R ⊗[F] E))
  haveI : T2Space (Matrix (Fin n) (Fin n) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin n → Fin n → R ⊗[F] E))
  have hc : IsClosed (HermR R σ n : Set (Matrix (Fin n) (Fin n) (R ⊗[F] E))) := h9 n
  exact ⟨inferInstance, hc.isClosedEmbedding_subtypeVal.locallyCompactSpace,
    hc.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology, inferInstance⟩

theorem continuous_hermInf {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (n : ℕ) :
    Continuous (hermInf σ : HermR (AF F) σ n → HermR (Ainf F) σ n) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  have c1 := continuous_tm (E := E) hCM (fstA F) continuous_fst
  refine continuous_induced_rng.2 ?_
  change Continuous fun x : HermR (AF F) σ n =>
    (x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (tm E (fstA F))
  exact Continuous.matrix_map continuous_subtype_val c1

theorem continuous_hermFin {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) (n : ℕ) :
    Continuous (hermFin σ : HermR (AF F) σ n → HermR (Af F) σ n) := by
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  have c1 := continuous_tm (E := E) hCM (sndA F) continuous_snd
  refine continuous_induced_rng.2 ?_
  change Continuous fun x : HermR (AF F) σ n =>
    (x : Matrix (Fin n) (Fin n) (AF F ⊗[F] E)).map (tm E (sndA F))
  exact Continuous.matrix_map continuous_subtype_val c1

theorem continuous_hermJoin {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) :
    Continuous (hermJoin b σ : HermR (Ainf F) σ n × HermR (Af F) σ n → HermR (AF F) σ n) := by
  refine continuous_induced_rng.2 ?_
  refine continuous_matrix fun i j => ?_
  change Continuous fun p : HermR (Ainf F) σ n × HermR (Af F) σ n =>
    joinT b ((p.1 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j) ((p.2 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j)
  have g1 : Continuous fun p : HermR (Ainf F) σ n × HermR (Af F) σ n =>
      (p.1 : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) i j :=
    (continuous_id.matrix_elem i j).comp (continuous_subtype_val.comp continuous_fst)
  have g2 : Continuous fun p : HermR (Ainf F) σ n × HermR (Af F) σ n =>
      (p.2 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j :=
    (continuous_id.matrix_elem i j).comp (continuous_subtype_val.comp continuous_snd)
  exact continuous_joinT hCM b g1 g2

def hermHomeo {σ : E →ₐ[F] E} (hCM : IsCMExt F E σ) {d : ℕ} (b : Module.Basis (Fin d) F E) (n : ℕ) :
    HermR (AF F) σ n ≃ₜ HermR (Ainf F) σ n × HermR (Af F) σ n where
  toEquiv := (hermSplit b σ n).toEquiv
  continuous_toFun := (continuous_hermInf hCM n).prodMk (continuous_hermFin hCM n)
  continuous_invFun := continuous_hermJoin hCM b n

end Top

theorem map_eq_smul_prod : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
  IsCMExt F E σ → ∀ (n : ℕ) (db : Measure (HermR (AF F) σ n)), db.IsAddHaarMeasure →
  ∃ (ν₁ : Measure (HermR (Ainf F) σ n)) (ν₂ : Measure (HermR (Af F) σ n)) (c : ℝ≥0∞),
    ν₁.IsAddHaarMeasure ∧ ν₂.IsAddHaarMeasure ∧ SFinite ν₁ ∧ SFinite ν₂ ∧ c ≠ ⊤ ∧
    MeasurableEmbedding (fun b : HermR (AF F) σ n => (hermInf σ b, hermFin σ b)) ∧
    db.map (fun b => (hermInf σ b, hermFin σ b)) = c • ν₁.prod ν₂ := by
  intro F E _ _ _ _ _ σ hCM n db hdb
  haveI := finite_of_cm hCM
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  obtain ⟨a1, a2, a3, a4⟩ := herm_facts hCM n (AF F)
  obtain ⟨b1, b2, b3, b4⟩ := herm_facts hCM n (Ainf F)
  obtain ⟨c1, c2, c3, c4⟩ := herm_facts hCM n (Af F)
  let b := Module.finBasis F E
  let e := hermHomeo hCM b n
  have he : (e : HermR (AF F) σ n → _) = fun b => (hermInf σ b, hermFin σ b) := rfl
  haveI hmap : (db.map e).IsAddHaarMeasure :=
    (hermSplit b σ n).isAddHaarMeasure_map db e.continuous e.symm.continuous
  let ν₁ : Measure (HermR (Ainf F) σ n) := Measure.addHaar
  let ν₂ : Measure (HermR (Af F) σ n) := Measure.addHaar
  haveI : SFinite ν₁ := inferInstance
  haveI : SFinite ν₂ := inferInstance
  refine ⟨ν₁, ν₂, ((db.map e).addHaarScalarFactor (ν₁.prod ν₂) : ℝ≥0), inferInstance, inferInstance,
    inferInstance, inferInstance, ENNReal.coe_ne_top, ?_, ?_⟩
  · rw [← he]
    exact e.measurableEmbedding
  · rw [← he]
    exact Measure.isAddLeftInvariant_eq_smul (db.map e) (ν₁.prod ν₂)

end GlobalTheory.CompanionTheory.SiegelND.Integ.MapHerm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureData
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.StageF

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.WeilSiegel.Frame NumberField MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]

def BsetF (σ : E →ₐ[F] E) {n : ℕ} (B₀ : Set R) : Set (HermR R σ (n + 1)) :=
  {S | s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) ∈ B₀}

end Alg

section Meas

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) {n : ℕ}
  {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
  (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
  (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
  (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
  (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0)

def fibSF (S : HermR R σ (n + 1)) : Measure (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  (BsetF R σ B₀).indicator (fun S : HermR R σ (n + 1) =>
    (κ₁ (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) *
        cm (a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)))) ^ n) •
      ((m₁ (hermScal R σ (algebraMap F R t))).prod (m' (schur R σ t a S))).map (fun p =>
        actW R σ (blockOne (algebraMap F E t) J) (s p.1)
          (vec (((a (s0 R (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E))) : Rˣ) : R) ⊗ₜ[F] (1 : E))
            (cvec R t a S) p.2))) S

def UsetF (B₀ : Set R) : Set (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) :=
  gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' BsetF R σ B₀) ∩
    {X | LinearIndependent (R ⊗[F] E) X}

def MidF {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ x in B₀, (κ₁ (a x) : ℝ≥0∞) * ∫⁻ c : Fin n → R ⊗[F] E, ∫⁻ S',
    Pint σ J t m₁ m' s φ ((a x : Rˣ) : R) c S' ∂(coordHerm R σ b lam n)
    ∂(Measure.pi fun _ => coordK R b lam) ∂lam

end Meas

section Data

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

structure HermitianMeasureData (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ)
    {R : Type} [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R)
    (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E))
    (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E))
    (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J))
    (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0) : Prop where
  hCM : IsCMExt F E σ
  hJ : IsHermND σ J
  ht : t ≠ 0
  hR : IsLocR R
  hlam : lam.IsAddHaarMeasure
  hm₁ : IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁
  hm' : IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m'
  hs : Measurable s
  hsec : ∀ y, gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) →
    actW R σ _ (s y) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) = y
  hcpt : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
    ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
      gramR R σ (blockOne (algebraMap F E t) J) y = (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C'
  hB₀ : IsOpen B₀
  htB : algebraMap F R t ∈ B₀
  hac : ContinuousOn a B₀
  hoff : ∀ x, x ∉ B₀ → a x = 1
  hsq : ∀ x ∈ B₀, x = ((a x : Rˣ) : R) ^ 2 * algebraMap F R t
  ha1 : a (algebraMap F R t) = 1
  hκc : Continuous κ₁
  hκ1 : κ₁ 1 = 1
  hscale : ∀ u : Rˣ, m₁ (hermScal R σ ((u : R) ^ 2 * algebraMap F R t)) =
    κ₁ u • (m₁ (hermScal R σ (algebraMap F R t))).map (scl ((u : R) ⊗ₜ[F] (1 : E)))
  hcmc : Continuous cm
  hmod : ∀ u : Rˣ, (coordK R b lam).map (fun y => ((u : R) ⊗ₜ[F] (algebraMap F E t)) * y) = cm u • coordK R b lam

end Data

end GlobalTheory.CompanionTheory.SW.StageF
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianO1PullbackFubiniStudyMetric
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.Inhab

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem val_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) :
    ((blockUnit i j h : Γ(MP ℤ m n, W)ˣ) : Γ(MP ℤ m n, W)) =
      pullRatio (prB n k) W i (h.trans ((prB n k).preimage_mono inf_le_left)) j := by
  rw [← appLE_ratioOn (φ := prB n k) (W := W) (U := chart ℤ (n k) i ⊓ chart ℤ (n k) j)
    (i := i) (j := j) inf_le_left h]
  rfl

theorem res_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W V : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (e : V ≤ W) :
    res e (blockUnit i j h) = blockUnit i j (e.trans h) := by
  refine Units.ext ?_
  rw [val_blockUnit]
  exact (congrArg (resG _ e) (val_blockUnit i j h)).trans (resG_pullRatio e)

theorem blockUnit_mul {k : Fin (m + 1)} (i j l : Bk n k) {W : (MP ℤ m n).Opens}
    (h₁ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j))
    (h₂ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) j ⊓ chart ℤ (n k) l))
    (h₃ : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) l)) :
    blockUnit i j h₁ * blockUnit j l h₂ = blockUnit i l h₃ := by
  refine Units.ext ?_
  rw [Units.val_mul, val_blockUnit, val_blockUnit, val_blockUnit]
  exact pullRatio_mul_pullRatio

theorem valR_pullRatio (x : Sp ℂ ⟶ MP ℤ m n) {k : Fin (m + 1)} (i j : Bk n k)
    (h : ⊤ ≤ x ⁻¹ᵁ blockChart n k i) :
    valR x (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) =
      valR (x ≫ prB n k) (chart ℤ (n k) i) (ratio ℤ (n k) i j) := by
  have h' : ⊤ ≤ (x ≫ prB n k) ⁻¹ᵁ chart ℤ (n k) i := h
  rw [valR, valR, dif_pos h, dif_pos h', pullRatio,
    ← Scheme.Hom.appLE_comp_appLE x (prB n k) (chart ℤ (n k) i) (blockChart n k i) ⊤ le_rfl h]
  rfl

theorem norm_eq_fs {ι : Type} [Fintype ι] (w : ι → ℂ) (i c : ι) (hi : w i ≠ 0) (hc : w c ≠ 0) :
    ‖WithLp.toLp 2 w‖ =
      ‖w c‖ * ‖w i / w c‖ * Real.exp (Real.log (∑ a, ‖w a / w i‖ ^ 2) / 2) := by
  have hi' : 0 < ‖w i‖ := norm_pos_iff.2 hi
  have hc' : 0 < ‖w c‖ := norm_pos_iff.2 hc
  have hS : ∑ a, ‖w a / w i‖ ^ 2 = (∑ a, ‖w a‖ ^ 2) / ‖w i‖ ^ 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun a _ => by rw [norm_div, div_pow]
  have hT : 0 < ∑ a, ‖w a‖ ^ 2 :=
    Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by positivity⟩
  have hpos : 0 < ∑ a, ‖w a / w i‖ ^ 2 := by rw [hS]; positivity
  have hexp : Real.exp (Real.log (∑ a, ‖w a / w i‖ ^ 2) / 2) = √(∑ a, ‖w a / w i‖ ^ 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
    congr 1
    ring
  rw [hexp, hS, Real.sqrt_div hT.le, Real.sqrt_sq hi'.le, norm_div, EuclideanSpace.norm_eq]
  simp only [PiLp.toLp_apply]
  field_simp

theorem pullback_O1_transition_eq_blockUnit (k : Fin (m + 1)) (i j : PUnit → Fin (n k + 1))
    (h : ((O1 ℤ (n k)).pull (prB n k)).U i ⊓ ((O1 ℤ (n k)).pull (prB n k)).U j ≤
      prB n k ⁻¹ᵁ (chart ℤ (n k) (i PUnit.unit) ⊓ chart ℤ (n k) (j PUnit.unit))) :
    ((O1 ℤ (n k)).pull (prB n k)).g i j = blockUnit (i PUnit.unit) (j PUnit.unit) h := by
  refine (linComb_punit_g (O1 ℤ (n k)) (prB n k) 1 i j).trans ?_
  rw [zpow_one]
  rfl

theorem prod_blockUnit_single {W : (MP ℤ m n).Opens} (k : Fin (m + 1)) (c c' : ∀ k, Bk n k)
    (h : ∀ k', W ≤ prB n k' ⁻¹ᵁ (chart ℤ (n k') (c k') ⊓ chart ℤ (n k') (c' k'))) :
    (∏ k', blockUnit (c k') (c' k') (h k') ^ (Pi.single k (1 : ℤ) : Fin (m + 1) → ℤ) k') =
      blockUnit (c k) (c' k) (h k) := by
  refine (Finset.prod_eq_single k (fun b _ hb => ?_) (fun hk => (hk (Finset.mem_univ _)).elim)).trans ?_
  · rw [Pi.single_eq_of_ne hb, zpow_zero]
  · rw [Pi.single_eq_same, zpow_one]

theorem ev_blockUnit {k : Fin (m + 1)} (i j : Bk n k) {W : (MP ℤ m n).Opens}
    (h : W ≤ prB n k ⁻¹ᵁ (chart ℤ (n k) i ⊓ chart ℤ (n k) j)) (e : W ≤ blockChart n k i)
    {y : CxPts (mpStr ℤ m n) σ₀} (hy : y ∈ ptsIn (mpStr ℤ m n) σ₀ W) :
    CxPts.ev (mpStr ℤ m n) σ₀ W (blockUnit i j h : Γ(MP ℤ m n, W)ˣ).val y =
      CxPts.ev (mpStr ℤ m n) σ₀ (blockChart n k i) (pullRatio (prB n k) _ i le_rfl j) y := by
  rw [val_blockUnit, ← resG_pullRatio (hi := le_rfl) e, CxPts.ev_res _ hy]

theorem ofMetrics_single_h (k : Fin (m + 1)) (z : (Σ k, Bk n k) → ℂ) :
    (Geo.HermLine.ofMetrics (fun k => Geo.fsMetric (Bk n k)) (Pi.single k 1)).h z =
      ‖WithLp.toLp 2 fun a => z ⟨k, a⟩‖ := by
  refine (Finset.prod_eq_single k (fun b _ hb => ?_) (fun hk => (hk (Finset.mem_univ _)).elim)).trans ?_
  · rw [Pi.single_eq_of_ne hb, zpow_zero]
  · rw [Pi.single_eq_same, zpow_one]
    rfl

theorem prod_norm_single (k : Fin (m + 1)) (c : ∀ k, Bk n k) (z : (Σ k, Bk n k) → ℂ) :
    (∏ k', ‖z ⟨k', c k'⟩‖ ^ (Pi.single k (1 : ℤ) : Fin (m + 1) → ℤ) k') = ‖z ⟨k, c k⟩‖ := by
  refine (Finset.prod_eq_single k (fun b _ hb => ?_) (fun hk => (hk (Finset.mem_univ _)).elim)).trans ?_
  · rw [Pi.single_eq_of_ne hb, zpow_zero]
  · rw [Pi.single_eq_same, zpow_one]

end GlobalTheory.CompanionTheory.MPDict.Inhab

open GlobalTheory.CompanionTheory.MPDict.Inhab in

theorem GlobalTheory.CompanionTheory.MPDict.isHermRep_pullback_hermitian_O1 : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (k : Fin (m + 1)), IsHermRep ((hermitianTwistingSheaf ℤ (n k)).pull (prB n k) (pr_toSpecBase ℤ m n k)) (Geo.HermLine.ofMetrics (fun k => Geo.fsMetric (Bk n k)) (Pi.single k 1)) := by
  intro m n k
  have hU (i : PUnit → Fin (n k + 1)) : ((O1 ℤ (n k)).pull (prB n k)).U i ≤ blockChart n k (i PUnit.unit) :=
    LB.wchart_le (O1 ℤ (n k)) (fun _ => prB n k) i PUnit.unit
  refine ⟨fun i c => blockUnit (c k) (i PUnit.unit) (le_inf (inf_le_right.trans (mchart_le c k))
    (inf_le_left.trans (hU i))), ?_, ?_, ?_⟩
  · intro i j c
    change Semi.res _ _ = Semi.res _ (((O1 ℤ (n k)).pull (prB n k)).g i j) * Semi.res _ _
    beta_reduce
    rw [pullback_O1_transition_eq_blockUnit k i j (fun x hx => ⟨hU i hx.1, hU j hx.2⟩)]
    refine (res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (res_blockUnit _ _ _ _) (res_blockUnit _ _ _ _)).symm)
    rw [mul_comm]
    exact (blockUnit_mul _ _ _ _ _ _).symm
  · intro i c c'
    beta_reduce
    refine (res_blockUnit _ _ _ _).trans (Eq.trans ?_
      (congrArg₂ (· * ·) (res_blockUnit _ _ _ _) (prod_blockUnit_single k c c' _)).symm)
    rw [mul_comm]
    exact (blockUnit_mul _ _ _ _ _ _).symm
  · intro i c y z hz hy
    have hy₁ : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (i PUnit.unit)) :=
      ptsIn_mono (inf_le_left.trans (hU i)) hy
    have hy₂ : y ∈ ptsIn (mpStr ℤ m n) σ₀ (blockChart n k (c k)) :=
      ptsIn_mono (inf_le_right.trans (mchart_le c k)) hy
    have hi : z ⟨k, i PUnit.unit⟩ ≠ 0 := ((hz k _).1).1 hy₁
    have hc : z ⟨k, c k⟩ ≠ 0 := ((hz k _).1).1 hy₂
    have hφ : (((hermitianTwistingSheaf ℤ (n k)).pull (prB n k) (pr_toSpecBase ℤ m n k)).φ σ₀).φ i y =
        Real.log (∑ a, ‖z ⟨k, a⟩ / z ⟨k, i PUnit.unit⟩‖ ^ 2) := by
      refine (Weight.pull_φ (ProjAn.fsO1 ℤ σ₀ (n k)) (prB n k) (pr_toSpecBase ℤ m n k) i y).trans ?_
      refine (Weight.fsBasis_φ _ _ _ _ _ _ _).trans (congrArg _ (Finset.sum_congr rfl fun a _ => ?_))
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
        if_true]
      refine congrArg (‖·‖ ^ 2) (Eq.trans ?_ ((hz k (i PUnit.unit)).2 a hy₁))
      exact (valR_pullRatio y.1 (i PUnit.unit) a hy₁).symm
    have hev : CxPts.ev (mpStr ℤ m n) σ₀ (((hermitianTwistingSheaf ℤ (n k)).pull (prB n k) (pr_toSpecBase ℤ m n k)).B.U i ⊓ mchart c)
        (blockUnit (c k) (i PUnit.unit) (le_inf (inf_le_right.trans (mchart_le c k))
          (inf_le_left.trans (hU i))) : Γ(MP ℤ m n, _)ˣ).val y =
        z ⟨k, i PUnit.unit⟩ / z ⟨k, c k⟩ := by
      exact (ev_blockUnit _ _ _ (inf_le_right.trans (mchart_le c k)) hy).trans ((hz k (c k)).2 _ hy₂)
    refine (ofMetrics_single_h k z).trans ?_
    refine (norm_eq_fs (fun a => z ⟨k, a⟩) (i PUnit.unit) (c k) hi hc).trans ?_
    rw [hφ]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (prod_norm_single k c z).symm (congrArg _ hev.symm)) rfl
end
end

