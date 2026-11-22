import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.JetUniquenessAlgebraic
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.FirstSlotSliceSlotMixedCasimirZero
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0195
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermDef
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0189
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0202
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0193
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieEntriesUnipotentBesselNCharacterization
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0133
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagUnipotentEqStabilizerTimesSection
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0200
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.JetUniquenessAlgebraicStatement
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.Jet
open scoped InnerProductSpace ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_uniqueness_algebraic : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (lam : Fin n → ℝ) (g : ℝ) (u : V), GlRel E → IsUnitary ε E → KHighest ε E (LamOf ε lam) u → FiniteDimensional ℂ (kSpan ε E u) → (∀ a b : Fin n, a < b → ε a ≠ ε b → g ≤ lam a - lam b) → 2 * (n : ℝ) < g → ∀ (V' : Type) [AddCommGroup V'] [Module ℂ V'] (E' : Fin n → Fin n → Module.End ℂ V') (ι : V →ₗ[ℂ] V') (ev : V' →ₗ[ℂ] V), GlRel E' → (∀ c d, ε c = ε d → ∀ x ∈ kSpan ε E u, ι (E c d x) = E' c d (ι x)) → (∀ y, ev y ∈ kSpan ε E u) → (∀ c d, ε c = ε d → ∀ y, ev (E' c d y) = E c d (ev y)) → (∀ G ∈ Vminus ε E (LamOf ε lam) u, ∑ a, ∑ b, E' a b (ι (at1 G a b)) = 0) → (∀ x ∈ kSpan ε E u, ev (ι x) = 0) → ∀ (w : List (Fin n × Fin n)), ∀ x ∈ kSpan ε E u, ev (ew E' w (ι x)) = 0 := by
  first | exact @GlobalTheory.Jet.UniqAlg.uniqAlg | exact GlobalTheory.Jet.UniqAlg.uniqAlg | (intros; apply GlobalTheory.Jet.UniqAlg.uniqAlg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatDetHMapInjectiveIsometry
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.DetMap

section General

variable {R K U V : Type*} [CommRing R] [Field K] [Algebra R K]
  [AddCommGroup U] [Module K U] [Module R U] [IsScalarTower R K U]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem length_quot_map (f : U →ₗ[R] V) (hf : Function.Injective f) (A B : Submodule R U) :
    Module.length R ((A.map f) ⧸ (B.map f).comap (A.map f).subtype) =
      Module.length R (A ⧸ B.comap A.subtype) := by
  let e : A ≃ₗ[R] A.map f := Submodule.equivMapOfInjective f hf A
  have he : (B.comap A.subtype).map (e : A →ₗ[R] A.map f) = (B.map f).comap (A.map f).subtype := by
    ext z
    constructor
    · rintro ⟨⟨a, ha⟩, haB, rfl⟩
      exact ⟨a, haB, rfl⟩
    · intro hz
      obtain ⟨b, hb, hbz⟩ := hz
      obtain ⟨a, ha, haz⟩ := z.2
      obtain rfl : a = b := hf (haz.trans hbz.symm)
      exact ⟨⟨a, ha⟩, hb, Subtype.ext haz⟩
  exact (Submodule.Quotient.equiv _ _ e he).length_eq.symm

theorem localization_map₂ (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A : Submodule R U) :
    Formalism.HermitianLatticesTheory.localization₂ p (A.map (i.restrictScalars R)) = (Formalism.HermitianLatticesTheory.localization₂ p A).map (i.restrictScalars R) := by
  ext x
  constructor
  · rintro ⟨s, hs, a, ha, hax⟩
    have hs0 : algebraMap R K s ≠ 0 := by
      intro h0
      apply hs
      have : s = 0 := hRK (by rw [h0, map_zero])
      rw [this]
      exact p.zero_mem
    refine ⟨(algebraMap R K s)⁻¹ • a, ⟨s, hs, ?_⟩, ?_⟩
    · rw [← algebraMap_smul K s ((algebraMap R K s)⁻¹ • a), smul_smul, mul_inv_cancel₀ hs0, one_smul]
      exact ha
    · rw [LinearMap.restrictScalars_apply] at hax ⊢
      rw [map_smul, hax, ← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  · rintro ⟨y, ⟨s, hs, hsy⟩, rfl⟩
    exact ⟨s, hs, s • y, hsy, LinearMap.map_smul _ s y⟩

theorem locLen_map (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A B : Submodule R U) :
    Formalism.HermitianLatticesTheory.locLen p (A.map (i.restrictScalars R)) (B.map (i.restrictScalars R)) =
      Formalism.HermitianLatticesTheory.locLen p A B := by
  unfold Formalism.HermitianLatticesTheory.locLen
  rw [localization_map₂ hRK i hi p A, localization_map₂ hRK i hi p B,
    length_quot_map (i.restrictScalars R) (by simpa using hi)]

theorem lidx_map (hRK : Function.Injective (algebraMap R K)) (i : U →ₗ[K] V)
    (hi : Function.Injective i) (p : Ideal R) [p.IsPrime] (A B : Submodule R U) :
    Formalism.HermitianLatticesTheory.lidx p (A.map (i.restrictScalars R)) (B.map (i.restrictScalars R)) =
      Formalism.HermitianLatticesTheory.lidx p A B := by
  have hi' : Function.Injective (i.restrictScalars R) := by simpa using hi
  unfold Formalism.HermitianLatticesTheory.lidx
  rw [← Submodule.map_inf _ hi', locLen_map hRK i hi, locLen_map hRK i hi]

end General

section NumberField

variable {K U V : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem genIdxH_map (i : U →ₗ[K] V) (hi : Function.Injective i) (A B : Submodule (𝓞 K) U) :
    genIdxH (A.map (i.restrictScalars (𝓞 K))) (B.map (i.restrictScalars (𝓞 K))) = genIdxH A B := by
  have hRK : Function.Injective (algebraMap (𝓞 K) K) := IsFractionRing.injective (𝓞 K) K
  unfold genIdxH
  refine finprod_congr fun P => ?_
  haveI := P.isPrime
  rw [lidx_map hRK i hi]

theorem mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf]

theorem dualInH_map (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V)
    (hiso : ∀ x y, hV (i x) (i y) = hU x y) (N : Submodule (𝓞 K) U) :
    dualInH hV (N.map (i.restrictScalars (𝓞 K))) =
      (dualInH hU N).map (i.restrictScalars (𝓞 K)) := by
  have hspan : (Submodule.span K ((N.map (i.restrictScalars (𝓞 K)) : Submodule (𝓞 K) V) : Set V)) =
      (Submodule.span K (N : Set U)).map i := by
    rw [Submodule.map_coe, LinearMap.coe_restrictScalars, Submodule.span_image]
  ext x
  simp only [dualInH, Submodule.mem_inf, Submodule.restrictScalars_mem, hspan, mem_dual,
    Submodule.mem_map, LinearMap.coe_restrictScalars]
  constructor
  · rintro ⟨hx, y, hy, rfl⟩
    refine ⟨y, ⟨fun n hn => ?_, hy⟩, rfl⟩
    rw [← hiso]
    exact hx (i n) ⟨n, hn, rfl⟩
  · rintro ⟨y, ⟨hy, hys⟩, rfl⟩
    refine ⟨?_, y, hys, rfl⟩
    rintro _ ⟨n, hn, rfl⟩
    rw [hiso]
    exact hy n hn

end NumberField

theorem latDetH_map : ∀ (K U V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup U] [Module K U] [Module (𝓞 K) U] [IsScalarTower (𝓞 K) K U] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (hU : U →ₗ⋆[K] U →ₗ[K] K) (hV : V →ₗ⋆[K] V →ₗ[K] K) (i : U →ₗ[K] V), Function.Injective i → (∀ x y, hV (i x) (i y) = hU x y) → ∀ N : Submodule (𝓞 K) U, latDetH hV (N.map (i.restrictScalars (𝓞 K))) = latDetH hU N := by
  intro K U V _ _ _ _ _ _ _ _ _ _ _ hU hV i hi hiso N
  unfold latDetH
  rw [dualInH_map hU hV i hiso, genIdxH_map i hi]

end GlobalTheory.LoopC.DetMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LayerCovolumeProductPowTwoSidedBoundsStatement
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.layer_covolume_product_pow_two_sided_bounds : ∀ (v : ℝ) (f k r m a b : ℕ) (x : ℝ≥0∞), 1 ≤ v → m ≤ r → a ≤ r ^ 2 → b ≤ r ^ 2 → ENNReal.ofReal ((8 * v) ^ (-(f : ℝ))) ^ m ≤ x → x ≤ ENNReal.ofReal ((8 * v) ^ (f : ℝ)) ^ m → ENNReal.ofReal (v ^ (k * m * f) / (8 * v) ^ (2 * (r + 1) ^ 2 * f)) ≤ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ∧ ENNReal.ofReal (v ^ f) ^ a * (ENNReal.ofReal ((v ^ f) ^ (k + 1)) ^ m * (ENNReal.ofReal (v ^ f) ^ b * x)) ≤ ENNReal.ofReal (v ^ (k * m * f) * (8 * v) ^ (2 * (r + 1) ^ 2 * f)) := by
  first | exact @GlobalTheory.DegVol.RefCov.prod_pow_bounds | exact GlobalTheory.DegVol.RefCov.prod_pow_bounds | (intros; apply GlobalTheory.DegVol.RefCov.prod_pow_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeadMinorGramMatrixConstDoubleCosetStatement
section
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadMinor_gramMatrix_const_doubleCoset : ∀ (D : D7) (Λ : Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V) (T T' : D.host.E) (F : LFlag (VS D) D.R.rS T) (F₁ F₂ : LFlag (VS D) D.R.rS T'), Formalism.L2.SG.TermDef.DCRel Λ F F₁ F₂ → ∀ l : ℕ, leadMinorE (ZhatL F F₂) l = leadMinorE (ZhatL F F₁) l := by
  first | exact @GlobalTheory.leadMinorE_zhatL_dcrel | exact GlobalTheory.leadMinorE_zhatL_dcrel | (intros; apply GlobalTheory.leadMinorE_zhatL_dcrel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeftQuotientCovolumeWithDensityDetNormSq
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.DetSlab

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

theorem detNorm_mul (x y : MatInf E j) : detNorm E j (x * y) = detNorm E j x * detNorm E j y := by
  unfold detNorm
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have : Matrix.of ((x * y) w) = Matrix.of (x w) * Matrix.of (y w) := rfl
  rw [this, Matrix.det_mul, norm_mul, mul_pow]

theorem detNorm_nonneg (x : MatInf E j) : 0 ≤ detNorm E j x :=
  Finset.prod_nonneg fun _ _ => sq_nonneg _

theorem detNorm_aut (hE : IsTotallyComplex E) (Λ : Submodule (𝓞 E) (Fin j → E)) (hΛ : Submodule.IsLattice E Λ)
    {x : MatInf E j} (hx : x ∈ autGL E j Λ) : detNorm E j x = 1 := by
  obtain ⟨γ, hγ, hx⟩ := hx
  have h1 : IsIntegral ℤ (γ : Matrix (Fin j) (Fin j) E).det :=
    GlobalTheory.Mem.StabDet.isIntegral_det Λ hΛ.fg hΛ.span_eq_top _ fun v hv => (hγ v).2 hv
  have h2 : IsIntegral ℤ ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).det :=
    GlobalTheory.Mem.StabDet.isIntegral_det Λ hΛ.fg hΛ.span_eq_top _ fun v hv => (hγ _).1 (by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]; exact hv)
  have h3 : (γ : Matrix (Fin j) (Fin j) E).det * ((γ⁻¹ : GL (Fin j) E) : Matrix (Fin j) (Fin j) E).det = 1 := by
    rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  let u : (𝓞 E)ˣ := Units.mkOfMulEqOne ⟨_, h1⟩ ⟨_, h2⟩ (RingOfIntegers.ext h3)
  have h4 := InfinitePlace.prod_eq_abs_norm ((u : 𝓞 E) : E)
  rw [NumberField.Units.norm] at h4
  have hu : ((u : 𝓞 E) : E) = (γ : Matrix (Fin j) (Fin j) E).det := rfl
  rw [hu] at h4
  unfold detNorm
  rw [Rat.cast_one] at h4
  rw [← h4]
  refine Finset.prod_congr rfl fun w _ => ?_
  have h5 : Matrix.of (x w) = w.embedding.mapMatrix (γ : Matrix (Fin j) (Fin j) E) := by
    ext a b
    simpa using hx w a b
  rw [h5, ← RingHom.map_det, InfinitePlace.norm_embedding_eq, (IsTotallyComplex.isComplex w).mult_eq_two]

theorem continuous_detNorm :
    Continuous (fun x : InfinitePlace E → Fin j → Fin j → ℂ => detNorm E j x) := by
  unfold detNorm
  refine continuous_finset_prod _ fun w _ => ?_
  refine (Continuous.norm ?_).pow 2
  exact Continuous.matrix_det (continuous_apply w)

theorem measurable_detNorm : Measurable (detNorm E j) := (continuous_detNorm E j).measurable

def scal (t : ℝ) (x : MatInf E j) : MatInf E j := fun w a b => (t : ℂ) * x w a b

theorem scal_eq (t : ℝ) (x : InfinitePlace E → Fin j → Fin j → ℂ) : scal E j t x = t • x := rfl

theorem measurable_scal (t : ℝ) : Measurable (scal E j t) :=
  (continuous_const_smul t : Continuous fun x : InfinitePlace E → Fin j → Fin j → ℂ => t • x).measurable

theorem detNorm_scal (t : ℝ) (x : MatInf E j) :
    detNorm E j (scal E j t x) = |t| ^ (2 * j * Fintype.card (InfinitePlace E)) * detNorm E j x := by
  unfold detNorm
  have : ∀ w, Matrix.of (scal E j t x w) = (t : ℂ) • Matrix.of (x w) := fun w => rfl
  simp only [this, Matrix.det_smul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow,
    Finset.prod_mul_distrib, Finset.prod_const, Fintype.card_fin, Finset.card_univ, ← pow_mul]
  rw [mul_comm j 2]

theorem isAddHaar_volume : (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)).IsAddHaarMeasure := by
  haveI h1 : (volume : Measure (Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  haveI h2 : (volume : Measure (Fin j → Fin j → ℂ)).IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  exact Measure.pi.isAddHaarMeasure _

theorem lintegral_scal (t : ℝ) (ht : t ≠ 0) (f : MatInf E j → ENNReal) (hf : Measurable f) :
    ∫⁻ x, f (scal E j t x) ∂(haarGL E j) = ∫⁻ x, f x ∂(haarGL E j) := by
  have hd : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((measurable_detNorm E j).inv).pow_const j).ennreal_ofReal
  have hf' : Measurable (fun x : InfinitePlace E → Fin j → Fin j → ℂ => f x) := hf
  have hf'' : Measurable (fun x : InfinitePlace E → Fin j → Fin j → ℂ => f (t • x)) :=
    hf.comp (measurable_scal E j t)
  have e1 := lintegral_withDensity_eq_lintegral_mul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) hd hf'
  have e2 := lintegral_withDensity_eq_lintegral_mul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) hd hf''
  refine e2.trans (Eq.trans ?_ e1.symm)
  haveI := isAddHaar_volume E j
  have hm := Measure.map_addHaar_smul (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) ht
  have hrk : Module.finrank ℝ (InfinitePlace E → Fin j → Fin j → ℂ) =
      2 * j * Fintype.card (InfinitePlace E) * j := by
    simp only [Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    ring
  have e3 := lintegral_map (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ))) (hd.mul hf')
    (measurable_const_smul t)
  rw [hm, lintegral_smul_measure, hrk, smul_eq_mul] at e3
  set N := 2 * j * Fintype.card (InfinitePlace E) with hN
  have hpos : 0 < |t| ^ (N * j) := pow_pos (abs_pos.2 ht) _
  have e4 : ∀ x : InfinitePlace E → Fin j → Fin j → ℂ, ENNReal.ofReal ((detNorm E j (t • x))⁻¹ ^ j) =
      ENNReal.ofReal |(t ^ (N * j))⁻¹| * ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) := by
    intro x
    have h : detNorm E j (t • x) = |t| ^ N * detNorm E j x := detNorm_scal E j t x
    rw [← ENNReal.ofReal_mul (abs_nonneg _), h, abs_inv, abs_pow, mul_inv, mul_pow,
      inv_pow, ← pow_mul]
  have e5 := lintegral_const_mul (μ := (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)))
    (ENNReal.ofReal |(t ^ (N * j))⁻¹|) (hd.mul hf'')
  replace e3 := e3.trans ((lintegral_congr fun x => (congrArg (· * f (scal E j t x)) (e4 x)).trans
    (mul_assoc _ _ _)).trans e5)
  have hne : ENNReal.ofReal |(t ^ (N * j))⁻¹| ≠ 0 := by
    rw [Ne, ENNReal.ofReal_eq_zero, not_le, abs_inv, abs_pow]; exact inv_pos.2 hpos
  exact ((ENNReal.mul_right_inj hne ENNReal.ofReal_ne_top).1 e3).symm

theorem restrict_pos (hj : 1 ≤ j) : (haarGL E j).restrict {g | 0 < detNorm E j g} = haarGL E j := by
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have hd : Measurable fun x : InfinitePlace E → Fin j → Fin j → ℂ => ENNReal.ofReal ((detNorm E j x)⁻¹ ^ j) :=
    (((measurable_detNorm E j).inv).pow_const j).ennreal_ofReal
  refine (ae_withDensity_iff hd).2 (Filter.Eventually.of_forall fun x hx => ?_)
  refine lt_of_le_of_ne (detNorm_nonneg E j x) fun h => hx ?_
  rw [← h, _root_.inv_zero, zero_pow (by omega), ENNReal.ofReal_zero]

theorem sFinite_haarGL : SFinite (haarGL E j) := by
  haveI := isAddHaar_volume E j
  exact (Measure.withDensity.instSFinite :
    SFinite (Measure.withDensity (volume : Measure (InfinitePlace E → Fin j → Fin j → ℂ)) _))

theorem lintegral_exp (F : ℝ → ENNReal) :
    ∫⁻ u, F (Real.exp u) = ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  have h := lintegral_image_eq_lintegral_abs_deriv_mul (s := Set.univ) (f := Real.exp) (f' := Real.exp)
    MeasurableSet.univ (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn
    (fun t => F t / ENNReal.ofReal t)
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  refine lintegral_congr fun u => ?_
  rw [abs_of_pos (Real.exp_pos u), ENNReal.mul_div_cancel
    (by simpa using Real.exp_pos u) ENNReal.ofReal_ne_top]

theorem lintegral_cone (hj : 1 ≤ j) (D : Set (MatInf E j)) (hD : MeasurableSet D)
    (hpos : D ⊆ {g | 0 < detNorm E j g}) (hsc : ∀ g ∈ D, ∀ t : ℝ, 0 < t → scal E j t g ∈ D)
    (F : ℝ → ENNReal) (hF : Measurable F) :
    ∫⁻ g in D, F (detNorm E j g) ∂(haarGL E j) =
      haarGL E j ({x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ∩ D) *
        ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  haveI := sFinite_haarGL E j
  have hl : Measurable fun g => Real.log (detNorm E j g) := Real.measurable_log.comp (measurable_detNorm E j)
  set ν : Measure ℝ := ((haarGL E j).restrict D).map fun g => Real.log (detNorm E j g) with hν
  have hνa : ∀ s, MeasurableSet s → ν s = haarGL E j ((fun g => Real.log (detNorm E j g)) ⁻¹' s ∩ D) :=
    fun s hs => by rw [hν, Measure.map_apply hl hs, Measure.restrict_apply (hl hs)]
  set N := 2 * j * Fintype.card (InfinitePlace E) with hN
  have hN0 : (N : ℝ) ≠ 0 := by
    have : 0 < N := Nat.mul_pos (by omega) Fintype.card_pos
    exact_mod_cast this.ne'
  haveI : ν.IsAddLeftInvariant := by
    refine ⟨fun c => ?_⟩
    ext s hs
    have hc : Measurable fun u : ℝ => c + u := measurable_const_add c
    rw [Measure.map_apply hc hs, hνa _ (hc hs), hνa _ hs]
    have hA : MeasurableSet ((fun g => Real.log (detNorm E j g)) ⁻¹' s ∩ D) := (hl hs).inter hD
    have hB : MeasurableSet ((fun g => Real.log (detNorm E j g)) ⁻¹' ((fun u => c + u) ⁻¹' s) ∩ D) :=
      (hl (hc hs)).inter hD
    have ht : 0 < Real.exp (c / N) := Real.exp_pos _
    rw [← lintegral_indicator_one hA, ← lintegral_indicator_one hB,
      ← lintegral_scal E j _ ht.ne' _ (measurable_one.indicator hA)]
    refine lintegral_congr fun x => ?_
    have hback : scal E j (Real.exp (c / N))⁻¹ (scal E j (Real.exp (c / N)) x) = x := by
      funext w a b
      simp only [scal]
      rw [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ ht.ne', Complex.ofReal_one, one_mul]
    have hlog : x ∈ D → Real.log (detNorm E j (scal E j (Real.exp (c / N)) x)) =
        c + Real.log (detNorm E j x) := fun hx => by
      have h0 : 0 < detNorm E j x := hpos hx
      rw [detNorm_scal, abs_of_pos ht, Real.log_mul (pow_pos ht _).ne' h0.ne', Real.log_pow, Real.log_exp, ← hN,
        mul_div_cancel₀ _ hN0]
    refine (Set.indicator_const_eq_indicator_const (c := (1 : ENNReal)) ⟨fun h => ⟨?_, hsc _ h.2 _ ht⟩, fun h => ?_⟩)
    · have := h.1
      simp only [Set.mem_preimage] at this ⊢
      rwa [hlog h.2]
    · have hx : x ∈ D := hback ▸ hsc _ h.2 _ (inv_pos.2 ht)
      refine ⟨?_, hx⟩
      have := h.1
      simp only [Set.mem_preimage] at this ⊢
      rwa [hlog hx] at this
  have hv : (volume : Measure ℝ) (Set.Ico 0 1) = 1 := by simp
  have hFe : Measurable fun u => F (Real.exp u) := hF.comp Real.measurable_exp
  have h1 := measure_add_lintegral_eq volume ν (s := Set.Ico 0 1) measurableSet_Ico _ hFe
  simp only [measure_preimage_add_right] at h1
  rw [hv, one_mul, lintegral_const_mul _ (f := fun u => F (Real.exp (-u))) (hFe.comp measurable_neg), lintegral_neg_eq_self (fun u => F (Real.exp u)),
    hνa _ measurableSet_Ico] at h1
  have hset : (fun g => Real.log (detNorm E j g)) ⁻¹' Set.Ico 0 1 ∩ D =
      {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} ∩ D := by
    ext x
    refine and_congr_left fun hx => ?_
    have h0 : 0 < detNorm E j x := hpos hx
    simp only [Set.mem_preimage, Set.mem_Ico, Set.mem_setOf_eq]
    rw [Real.log_nonneg_iff h0, Real.log_lt_iff_lt_exp h0]
  rw [hset] at h1
  have h2 : ∫⁻ u, F (Real.exp u) ∂ν = ∫⁻ g in D, F (detNorm E j g) ∂(haarGL E j) := by
    rw [hν, lintegral_map hFe hl]
    refine setLIntegral_congr_fun hD fun x hx => ?_
    simp only [Real.exp_log (hpos hx)]
  rw [← h2, h1, lintegral_exp]

theorem covol_withDensity_detNorm : ∀ (E : Type) [Field E] [NumberField E], IsTotallyComplex E → ∀ (j : ℕ), 1 ≤ j → ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → ∀ F : ℝ → ENNReal, Measurable F → covol (autGL E j Λ) ((haarGL E j).withDensity fun x => F (detNorm E j x)) {x | 0 < detNorm E j x} = covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} * ∫⁻ t in Set.Ioi (0 : ℝ), F t / ENNReal.ofReal t := by
  intro E _ _ hE j hj Λ hΛ F hF
  obtain ⟨D, hD, hpos, -, hsc, hcov⟩ := GlobalTheory.T.exists_scalarStable_latticeAutomorphismFundamentalDomain E hE j Λ hΛ
  have hm := measurable_detNorm E j
  have hP : MeasurableSet {g : MatInf E j | 0 < detNorm E j g} := measurableSet_lt measurable_const hm
  have hS : MeasurableSet {x : MatInf E j | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1} :=
    (measurableSet_le measurable_const hm).inter (measurableSet_lt hm measurable_const)
  have hinv : ∀ γ ∈ autGL E j Λ, ∀ g, detNorm E j (γ * g) = detNorm E j g := fun γ hγ g => by
    rw [detNorm_mul, detNorm_aut E j hE Λ hΛ hγ, one_mul]
  have h1 := hcov (fun x => F (detNorm E j x)) _ ((hF.comp hm).indicator hP)
    (fun γ hγ g _ => by simp only [hinv γ hγ g]) hP subset_rfl
    (fun γ hγ g hg => by simpa only [Set.mem_setOf_eq, hinv γ hγ g] using hg)
  have h2 := hcov (fun _ => 1) _ (measurable_const.indicator hP) (fun _ _ _ _ => rfl) hS
    (fun g hg => lt_of_lt_of_le one_pos hg.1)
    (fun γ hγ g hg => by simpa only [Set.mem_setOf_eq, hinv γ hγ g] using hg)
  rw [restrict_pos E j hj] at h1 h2
  rw [withDensity_const, one_smul, setLIntegral_one] at h2
  rw [h1, h2, Set.inter_eq_right.2 hpos]
  exact lintegral_cone E j hj D hD hpos hsc F hF

end GlobalTheory.DetSlab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LeviChartMapHaarCarriedInvariant
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso

theorem isClosed_flagM {n a : ℕ} (ε : Fin n → Bool) (W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)) :
    IsClosed (flagM ε W) := by
  have hc : Continuous fun g : Formalism.REAL.UJ ε => uMat g := Units.continuous_val.comp continuous_subtype_val
  have hc' : Continuous fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ := hc.matrix_conjTranspose
  have hset : flagM ε W = ⋂ i, ⋂ y ∈ W i,
      ((fun g : Formalism.REAL.UJ ε => uMat g *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ)) ∩
        (fun g : Formalism.REAL.UJ ε => (uMat g)ᴴ *ᵥ y) ⁻¹' (W i : Set (Fin n → ℂ))) := by
    ext g
    simp [flagM]
  rw [hset]
  refine isClosed_iInter fun i => isClosed_biInter fun y _ => ?_
  have hW : IsClosed (W i : Set (Fin n → ℂ)) := (W i).closed_of_finiteDimensional
  exact (hW.preimage (hc.matrix_mulVec continuous_const)).inter (hW.preimage (hc'.matrix_mulVec continuous_const))

theorem ae_det_ne_zero {a : ℕ} (j : Fin a → ℕ) (d : Fin a → ℝ) {Y : Type} [MeasurableSpace Y] (ν : Measure Y)
    [SFinite ν] :
    ∀ᵐ z ∂((Measure.pi fun i => ENNReal.ofReal (d i) • haarLoc (j i)).prod ν), ∀ i, (Matrix.of (z.1 i)).det ≠ 0 := by
  have h1 : ∀ᵐ x ∂(Measure.pi fun i => ENNReal.ofReal (d i) • haarLoc (j i)), ∀ i, (Matrix.of (x i)).det ≠ 0 := by
    rw [ae_all_iff]
    intro i
    have h0 : ∀ᵐ y ∂(ENNReal.ofReal (d i) • haarLoc (j i)), (Matrix.of y).det ≠ 0 := by
      have hn := (haarLoc_conj_and_null (j i)).2
      rw [ae_iff, Measure.smul_apply]
      simp [hn]
    exact (Measure.tendsto_eval_ae_ae (μ := fun i => ENNReal.ofReal (d i) • haarLoc (j i)) (i := i)).eventually
      (p := fun y => (Matrix.of y).det ≠ 0) h0
  exact Measure.quasiMeasurePreserving_fst.ae h1

private theorem measurePreserving_smul_measure {X : Type} [MeasurableSpace X] {μ : Measure X} {f : X → X}
    (hf : MeasurePreserving f μ μ) (c : ENNReal) : MeasurePreserving f (c • μ) (c • μ) :=
  ⟨hf.measurable, by rw [Measure.map_smul, hf.map_eq]⟩

theorem map_chart_carried_and_invariant : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ θ : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → Formalism.REAL.UJ ε, Measurable θ → (∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → uMat (θ z) = lev ε B B₀ (fun i => Matrix.of (z.1 i)) (uMat z.2)) → ∀ c : ℝ, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) (flagM ε W)ᶜ = 0 ∧ ∀ s ∈ flagM ε W, (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ).map (fun g => s * g) = (((Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i)).prod (ENNReal.ofReal c • Formalism.REAL.muG ε₀)).map θ) := by
  intro n n₀ a j ε ε₀ B B₀ hB W hW θ hθ hθl c
  set P := Measure.pi fun i => ENNReal.ofReal (2 ^ (j i ^ 2)) • haarLoc (j i) with hP
  set ν := ENNReal.ofReal c • Formalism.REAL.muG ε₀ with hν
  have hdet : ∀ᵐ z ∂(P.prod ν), ∀ i, (Matrix.of (z.1 i)).det ≠ 0 :=
    ae_det_ne_zero j (fun i => 2 ^ (j i ^ 2)) ν
  have hmem : ∀ z : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀,
      (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → θ z ∈ flagM ε W := fun z hz =>
    (Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW (θ z)).2 ⟨fun i => Matrix.of (z.1 i), z.2, hz, hθl z hz⟩
  have hM : MeasurableSet (flagM ε W) := (isClosed_flagM ε W).measurableSet
  refine ⟨?_, fun s hs => ?_⟩
  · have h : ∀ᵐ m ∂((P.prod ν).map θ), m ∈ flagM ε W :=
      (ae_map_iff hθ.aemeasurable hM).2 (hdet.mono hmem)
    exact measure_mono_null (fun m hm => hm) (ae_iff.1 h)
  · obtain ⟨x, g, hx, hs'⟩ := (Range.mem_flagM_iff n n₀ a j ε ε₀ B B₀ hB W hW s).1 hs
    let T : (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ → (∀ i, Fin (j i) → Fin (j i) → ℂ) × Formalism.REAL.UJ ε₀ :=
      Prod.map (fun (y : ∀ i, Fin (j i) → Fin (j i) → ℂ) (i : Fin a) (r t : Fin (j i)) =>
        (x i * Matrix.of (y i) * (1 : Matrix (Fin (j i)) (Fin (j i)) ℂ)) r t) (fun u => g * u)
    have hT : MeasurePreserving T (P.prod ν) (P.prod ν) := by
      refine MeasurePreserving.prod ?_ ?_
      · exact measurePreserving_pi _ _ fun i =>
          measurePreserving_smul_measure (GlobalTheory.HaarMul.measurePreserving_mul_mul (j i) (x i) 1 (hx i) (by simp)) _
      · exact measurePreserving_smul_measure (measurePreserving_mul_left (Formalism.REAL.muG ε₀) g) _
    have hcomm : ∀ z, (∀ i, (Matrix.of (z.1 i)).det ≠ 0) → s * θ z = θ (T z) := by
      intro z hz
      have hz' : ∀ i, (Matrix.of ((T z).1 i)).det ≠ 0 := by
        intro i
        have : Matrix.of ((T z).1 i) = x i * Matrix.of (z.1 i) := by
          ext r t
          simp [T]
        rw [this, Matrix.det_mul]
        exact mul_ne_zero (hx i) (hz i)
      apply Subtype.ext
      apply Units.ext
      change uMat s * uMat (θ z) = uMat (θ (T z))
      rw [hs', hθl z hz, hθl (T z) hz', ← hB.lev_mul]
      congr 1
      · funext i
        ext r t
        simp [T]
    have hmul : Measurable fun m : Formalism.REAL.UJ ε => s * m := measurable_const_mul s
    calc ((P.prod ν).map θ).map (fun m => s * m)
        = (P.prod ν).map (fun z => s * θ z) := by rw [Measure.map_map hmul hθ]; rfl
      _ = (P.prod ν).map (fun z => θ (T z)) := Measure.map_congr (hdet.mono fun z hz => hcomm z hz)
      _ = ((P.prod ν).map T).map θ := by rw [Measure.map_map hθ hT.measurable]; rfl
      _ = (P.prod ν).map θ := by rw [hT.map_eq]

end GlobalTheory.LeviIso
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LieEntriesUnipotentBesselNCharacterizationStatement
section
open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.CellDens
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieEntries_unipotentBesselN_characterization : ∀ (k r : ℕ) (x : EuclideanSpace ℝ (Fin (2 * r + k + 1) × Fin (2 * r + k + 1) × Bool)), (x ∈ lieE (Nset k r) ↔ ((unrealify x)ᴴ * Hpk k r + Hpk k r * unrealify x = 0 ∧ ∀ i j : Fin (2 * r + k + 1), lev k r j ≤ lev k r i → unrealify x i j = 0)) ∧ (x ∈ lieE (Nset k r) → NormedSpace.exp (unrealify x) ∈ Nset k r) := by
  first | exact @GlobalTheory.CellDens.LieN.lieE_Nset | exact GlobalTheory.CellDens.LieN.lieE_Nset | (intros; apply GlobalTheory.CellDens.LieN.lieE_Nset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralFlagUnipotentEqStabilizerTimesSectionStatement
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_flagUnipotent_eq_stabilizer_times_section : ∀ (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → ∀ f : Mt k r → ℝ≥0∞, Measurable f → ∫⁻ n, f n ∂(lebN k r) = ∫⁻ q : PSec k r j × (UToff β → ℂ), ∫⁻ ρ, f (rmulM (sEl k r j β q) ρ) ∂(lebR0 k r j β) := by
  first | exact @GlobalTheory.Amp.RadConj.lebN_split | exact GlobalTheory.Amp.RadConj.lebN_split | (intros; apply GlobalTheory.Amp.RadConj.lebN_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralIoiCompConstDivChangeOfVarStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_Ioi_comp_const_div_change_of_var : ∀ (κ : ℝ), 0 < κ → ∀ w : ℝ → ENNReal, Measurable w → ∫⁻ t in Set.Ioi (0 : ℝ), w (κ / t) * ENNReal.ofReal t / ENNReal.ofReal t = ENNReal.ofReal κ * ∫⁻ t in Set.Ioi (0 : ℝ), w t / ENNReal.ofReal (t ^ 2) := by
  first | exact @GlobalTheory.lintegral_Ioi_comp_const_div_mul_div | exact GlobalTheory.lintegral_Ioi_comp_const_div_mul_div | (intros; apply GlobalTheory.lintegral_Ioi_comp_const_div_mul_div <;> assumption)
end

