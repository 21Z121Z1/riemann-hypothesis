import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.CalcSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0224
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusJointCurve
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0370
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0218
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0241
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0369
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0060
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0043
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0022
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.WeilBound.CoreStatements.ThetaDilations.ThetaLint
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0371
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0320
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0372
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.LeibnizDerivatives.GenericProdIff

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RightWordLaplacianPowerBound
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty ENNReal
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.FcSmooth.WordBd

open GlobalTheory.CompanionTheory.CurveJ (sob_comb)
open GlobalTheory.CompanionTheory.SobOpsPf (sob_bs sob_congr sob_smul sob_sum)
open GlobalTheory.CompanionTheory.SecBd (cls_sum cls_congr cls_eq cls_sub)

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem Rw_zero (w : List (Bool × Fin n × Fin n)) : Rw w (0 : Mat n → V) = 0 := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    show Rd (bs p) (Rw w (0 : Mat n → V)) = 0
    rw [ih]
    funext g
    simp [Rd]

theorem sob_zero : Sob μ (0 : Mat n → V) :=
  ⟨contDiffOn_const, fun w => by rw [Rw_zero]; exact MemLp.zero⟩

theorem cls_zero : cls μ (0 : Mat n → V) = 0 := by
  have h : MemLp (fun y : G n => (0 : Mat n → V) y.val) 2 μ := MemLp.zero
  rw [cls_eq μ h]
  exact MemLp.toLp_zero h

theorem cls_mem {f : Mat n → V} (hf : Sob μ f) : cls μ f ∈ Msob μ V :=
  Submodule.subset_span ⟨f, hf, rfl⟩

theorem exists_rep (x : Lp V 2 μ) (hx : x ∈ Msob μ V) : ∃ f : Mat n → V, Sob μ f ∧ cls μ f = x := by
  induction hx using Submodule.span_induction with
  | mem x h => exact h
  | zero => exact ⟨0, sob_zero, cls_zero⟩
  | add x y _ _ hx hy =>
    obtain ⟨f, hf, rfl⟩ := hx
    obtain ⟨f', hf', rfl⟩ := hy
    have h := sob_comb 1 hf hf'
    refine ⟨_, h.1, ?_⟩
    simpa [Rw] using h.2 []
  | smul a x _ hx =>
    obtain ⟨f, hf, rfl⟩ := hx
    have h := sob_comb a hf (sob_zero (μ := μ) (V := V))
    refine ⟨_, h.1, ?_⟩
    simpa [Rw, cls_zero] using h.2 []

def rp (x : Msob μ V) : Mat n → V := Classical.choose (exists_rep x.1 x.2)

theorem rp_sob (x : Msob μ V) : Sob μ (rp x) := (Classical.choose_spec (exists_rep x.1 x.2)).1

theorem rp_cls (x : Msob μ V) : cls μ (rp x) = x := (Classical.choose_spec (exists_rep x.1 x.2)).2

def Uniq (μ : Measure (G n)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] : Prop :=
  ∀ f f' : Mat n → V, Sob μ f → Sob μ f' → cls μ f = cls μ f' → ∀ g ∈ GLs n, f g = f' g

def Xf (p : Bool × Fin n × Fin n) (x : Msob μ V) : Msob μ V :=
  ⟨cls μ (Rd (bs p) (rp x)), cls_mem (sob_bs p (rp_sob x))⟩

theorem Xf_cls (hu : Uniq μ V) (p : Bool × Fin n × Fin n) {f : Mat n → V} (hf : Sob μ f) (x : Msob μ V)
    (hx : (x : Lp V 2 μ) = cls μ f) : (Xf p x : Lp V 2 μ) = cls μ (Rd (bs p) f) := by
  have e : Set.EqOn (rp x) f (GLs n) := fun g hg =>
    hu _ _ (rp_sob x) hf ((rp_cls x).trans hx) g hg
  exact cls_congr μ ((sob_bs p (rp_sob x)).2 [])
    fun g hg => GlobalTheory.CompanionTheory.RCalc.Rd_congr (bs p) e hg

theorem Xf_comb (hu : Uniq μ V) (p : Bool × Fin n × Fin n) (a : ℂ) (x y : Msob μ V) :
    Xf p (a • x + y) = a • Xf p x + Xf p y := by
  have h := sob_comb a (rp_sob x) (rp_sob y)
  apply Subtype.ext
  have e : ((a • x + y : Msob μ V) : Lp V 2 μ) = cls μ (fun z => a • rp x z + rp y z) := by
    have := h.2 []
    simp only [Rw, id] at this
    rw [this, rp_cls, rp_cls]
    rfl
  rw [Xf_cls hu p h.1 _ e]
  exact h.2 [p]

def X (hu : Uniq μ V) (p : Bool × Fin n × Fin n) : Module.End ℂ (Msob μ V) where
  toFun := Xf p
  map_add' x y := by simpa using Xf_comb hu p 1 x y
  map_smul' a x := by
    have h0 : Xf p (0 : Msob μ V) = 0 := by simpa using Xf_comb hu p 1 0 0
    simpa [h0] using Xf_comb hu p a x 0

theorem X_cls (hu : Uniq μ V) (p : Bool × Fin n × Fin n) {f : Mat n → V} (hf : Sob μ f) :
    (X hu p ⟨cls μ f, cls_mem hf⟩ : Msob μ V) = ⟨cls μ (Rd (bs p) f), cls_mem (sob_bs p hf)⟩ :=
  Subtype.ext (Xf_cls hu p hf _ rfl)

theorem X_skew (hu : Uniq μ V) (hI : ∀ f f' : Mat n → V, Sob μ f → Sob μ f' → ∀ Y : Mat n,
      ⟪cls μ (Rd Y f), cls μ f'⟫_ℂ = -⟪cls μ f, cls μ (Rd Y f')⟫_ℂ)
    (p : Bool × Fin n × Fin n) (u v : Msob μ V) : ⟪X hu p u, v⟫_ℂ = -⟪u, X hu p v⟫_ℂ := by
  obtain ⟨f, hf, hfu⟩ := exists_rep u.1 u.2
  obtain ⟨f', hf', hfv⟩ := exists_rep v.1 v.2
  have eu : u = ⟨cls μ f, cls_mem hf⟩ := Subtype.ext hfu.symm
  have ev : v = ⟨cls μ f', cls_mem hf'⟩ := Subtype.ext hfv.symm
  rw [eu, ev, X_cls hu p hf, X_cls hu p hf']
  exact hI f f' hf hf' (bs p)

theorem memS {f : Mat n → V} (hf : Sob μ f) : MemLp (fun y : G n => f y.val) 2 μ := hf.2 []

theorem cls_smul (a : ℂ) {f : Mat n → V} (h : MemLp (fun y : G n => f y.val) 2 μ) :
    cls μ (fun g => a • f g) = a • cls μ f := by
  rw [cls_eq μ h, cls_eq μ (f := fun g => a • f g) (h.const_smul a)]
  exact MemLp.toLp_const_smul a h

theorem X_bracket (hu : Uniq μ V)
    (hB : ∀ f : Mat n → V, Sob μ f → ∀ Y Z, ∀ g ∈ GLs n,
      Rd Y (Rd Z f) g - Rd Z (Rd Y f) g = Rd (Y * Z - Z * Y) f g)
    (i j : Bool × Fin n × Fin n) (c : Bool × Fin n × Fin n → ℝ)
    (hc : bs i * bs j - bs j * bs i = ∑ k, c k • bs k) :
    X hu i * X hu j - X hu j * X hu i = ∑ k, (c k : ℂ) • X hu k := by
  refine LinearMap.ext fun u => ?_
  obtain ⟨f, hf, hfu⟩ := exists_rep u.1 u.2
  have eu : u = ⟨cls μ f, cls_mem hf⟩ := Subtype.ext hfu.symm
  rw [eu]
  apply Subtype.ext
  have hm : ∀ k, MemLp (fun y : G n => (c k : ℂ) • Rd (bs k) f y.val) 2 μ := fun k =>
    ((sob_bs k hf).2 []).const_smul _
  have h1 := cls_sum μ Finset.univ (fun k g => (c k : ℂ) • Rd (bs k) f g) fun k _ => hm k
  have hij : ∀ a b, ((X hu a * X hu b) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 =
      cls μ (Rd (bs a) (Rd (bs b) f)) := fun a b => by
    rw [Module.End.mul_apply, X_cls hu b hf, X_cls hu a (sob_bs b hf)]
  have hs : ∀ k, (((c k : ℂ) • X hu k) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 =
      cls μ (fun g => (c k : ℂ) • Rd (bs k) f g) := fun k => by
    rw [LinearMap.smul_apply, X_cls hu k hf, cls_smul _ (memS (sob_bs k hf))]
    rfl
  rw [LinearMap.sub_apply, Submodule.coe_sub, hij, hij, LinearMap.sum_apply, Submodule.coe_sum]
  simp only [hs]
  rw [← h1.2, ← cls_sub μ (memS (sob_bs i (sob_bs j hf))) (memS (sob_bs j (sob_bs i hf)))]
  refine cls_congr μ ((memS (sob_bs i (sob_bs j hf))).sub (memS (sob_bs j (sob_bs i hf)))) fun g hg => ?_
  rw [hB f hf _ _ g hg, GlobalTheory.CompanionTheory.FcCalc.Ibp.Rd_expand f hc g]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact (Complex.coe_smul _ _).symm

theorem word_apply (hu : Uniq μ V) (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : Sob μ f) :
    (((w.map (X hu)).prod ⟨cls μ f, cls_mem hf⟩ : Msob μ V) : Lp V 2 μ) = cls μ (Rw w f) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    have hw := GlobalTheory.CompanionTheory.SobOpsPf.sob_Rw w hf
    have e : (w.map (X hu)).prod ⟨cls μ f, cls_mem hf⟩ = ⟨cls μ (Rw w f), cls_mem hw⟩ := Subtype.ext ih
    rw [List.map_cons, List.prod_cons, Module.End.mul_apply, e, X_cls hu p hw]
    rfl

theorem sob_Lap {f : Mat n → V} (hf : Sob μ f) : Sob μ (Lap f) := by
  refine sob_congr (sob_smul (-1 : ℂ) (sob_sum Finset.univ hf fun p => sob_bs p (sob_bs p hf))) fun g _ => ?_
  simp [Lap]

theorem lap_apply (hu : Uniq μ V) {f : Mat n → V} (hf : Sob μ f) :
    (-∑ i, X hu i * X hu i) ⟨cls μ f, cls_mem hf⟩ = (⟨cls μ (Lap f), cls_mem (sob_Lap hf)⟩ : Msob μ V) := by
  apply Subtype.ext
  have hm : ∀ p, MemLp (fun y : G n => Rd (bs p) (Rd (bs p) f) y.val) 2 μ := fun p =>
    (sob_bs p (sob_bs p hf)).2 []
  have h1 := cls_sum μ Finset.univ (fun p g => Rd (bs p) (Rd (bs p) f) g) fun p _ => hm p
  have e : cls μ (Lap f) = -∑ p, cls μ (Rd (bs p) (Rd (bs p) f)) := by
    have e1 : Lap f = fun g => (-1 : ℂ) • ∑ p, Rd (bs p) (Rd (bs p) f) g := by
      funext g; simp [Lap]
    rw [e1, cls_smul _ h1.1, h1.2]
    simp
  show ((-∑ i, X hu i * X hu i) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 = cls μ (Lap f)
  rw [e, LinearMap.neg_apply, LinearMap.sum_apply, Submodule.coe_neg, Submodule.coe_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Module.End.mul_apply, X_cls hu p hf, X_cls hu p (sob_bs p hf)]

theorem sob_Lap_iter (j : ℕ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Lap^[j] f) := by
  induction j generalizing f with
  | zero => exact hf
  | succ j ih => exact ih (sob_Lap hf)

theorem pow_apply (hu : Uniq μ V) (j : ℕ) {f : Mat n → V} (hf : Sob μ f) :
    (((-∑ i, X hu i * X hu i) ^ j) ⟨cls μ f, cls_mem hf⟩ : Msob μ V).1 = cls μ (Lap^[j] f) := by
  induction j generalizing f with
  | zero => rfl
  | succ j ih =>
    rw [pow_succ, Module.End.mul_apply, lap_apply hu hf, ih (sob_Lap hf)]
    rfl

theorem word_bound : ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V],
    LgFacts → Unimod → RCalc → AlgEst → ClsFacts → IbpSob →
    ∀ w : List (Bool × Fin n × Fin n), ∃ C : ℝ, ∀ f : Mat n → V, Sob μ f →
      ‖cls μ (Rw w f)‖ ≤ C * ∑ j ∈ range (w.length + 1), ‖cls μ (GlobalTheory.CompanionTheory.FcSmooth.Lap^[j] f)‖ := by
  intro n _ _ μ _ V _ _ _ hL hU hR hA hC hI w
  have hu : Uniq μ V := fun f f' hf hf' e g hg =>
    (hC n μ V hU).1 f f' hf.1.continuousOn hf'.1.continuousOn (hf.2 []) (hf'.2 []) e g hg
  choose c hc using fun ij : (Bool × Fin n × Fin n) × (Bool × Fin n × Fin n) =>
    GlobalTheory.CompanionTheory.FcCalc.Ibp.exists_coeff (bs ij.1 * bs ij.2 - bs ij.2 * bs ij.1)
  obtain ⟨C, hCb⟩ := hA (Msob μ V) (Bool × Fin n × Fin n) (X hu) (fun i j k => c (i, j) k)
    (X_skew hu fun f f' hf hf' Y => hI n μ V hL hU hR f f' hf hf' Y)
    (fun i j => X_bracket hu (fun f hf Y Z g hg => ((hR n).1 V f hf.1).2.1 Y Z g hg) i j _ (hc (i, j))) w
  refine ⟨C, fun f hf => ?_⟩
  have h := hCb ⟨cls μ f, cls_mem hf⟩
  have e1 : ‖cls μ (Rw w f)‖ = ‖(w.map (X hu)).prod ⟨cls μ f, cls_mem hf⟩‖ := by
    rw [← word_apply hu w hf]; rfl
  rw [e1]
  refine h.trans_eq ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← pow_apply hu j hf]
  rfl

end GlobalTheory.CompanionTheory.FcSmooth.WordBd
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeScalingHermitianMeasure
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

theorem map_eq_sqrt_smul {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ+ G) (ν : Measure G) [ν.IsAddHaarMeasure] (c : ℝ≥0)
    (h : ν.map (e ∘ e) = c • ν) : ν.map e = NNReal.sqrt c • ν := by
  haveI : (ν.map e).IsAddHaarMeasure := ContinuousAddEquiv.isAddHaarMeasure_map ν e
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, ν.map e = b • ν :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (ν.map e) ν⟩
  have he : Measurable e := e.continuous.measurable
  have h2 : ν.map (e ∘ e) = (b * b) • ν := by
    rw [← Measure.map_map he he, hb, Measure.map_smul, hb, smul_smul]
  obtain ⟨K, hK, hK0⟩ := exists_compact_mem_nhds (0 : G)
  have hpos : ν K ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hK0).ne'
  have hfin : ν K ≠ ∞ := hK.measure_lt_top.ne
  have hbc : b * b = c := by
    have h3 : ((b * b : ℝ≥0) • ν) K = (c • ν) K := by rw [← h2, h]
    simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h3
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3
  rw [hb, ← hbc, NNReal.sqrt_mul_self]

theorem scalH_scalH {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (a b : R) (S : HermR R σ n) :
    scalH R σ a (scalH R σ b S) = scalH R σ (a * b) S := by
  apply Subtype.ext
  simp only [scalH_coe, smul_smul, map_mul]

theorem scalH_one {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (S : HermR R σ n) : scalH R σ 1 S = S := by
  apply Subtype.ext
  simp only [scalH_coe, map_one, one_smul]

def scalEquiv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R]
    (n : ℕ) (l : F) (hl : l ≠ 0) : HermR R σ n ≃ₜ+ HermR R σ n :=
  have hc : ∀ a : R, Continuous (scalH R σ (n := n) a) := fun a => by
    obtain ⟨iTR, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
    haveI := iTR
    exact Continuous.subtype_mk ((continuous_const_smul _).comp continuous_subtype_val) _
  have hm : algebraMap F R l * algebraMap F R l⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hl, map_one]
  { toFun := scalH R σ (algebraMap F R l)
    invFun := scalH R σ (algebraMap F R l⁻¹)
    left_inv := fun S => by rw [scalH_scalH, mul_comm, hm, scalH_one]
    right_inv := fun S => by rw [scalH_scalH, hm, scalH_one]
    map_add' := fun S T => by
      apply Subtype.ext
      simp [scalH_coe]
    continuous_toFun := hc _
    continuous_invFun := hc _ }

def oneByOne {F E : Type} [Field F] [Field E] [Algebra F E] (l : F) : Matrix (Fin 1) (Fin 1) E :=
  Matrix.of fun _ _ => algebraMap F E l

theorem action_eq {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (l : F) (S : HermR R σ 1) :
    ((scalH R σ (algebraMap F R l) (scalH R σ (algebraMap F R l) S) : HermR R σ 1) :
        Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R) := by
  have h1 : inclR R (algebraMap F E l) = algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes l
  have h2 : sigR R σ (algebraMap R (R ⊗[F] E) (algebraMap F R l)) =
      algebraMap R (R ⊗[F] E) (algebraMap F R l) := by
    simp [sigR, Algebra.TensorProduct.algebraMap_apply]
  ext i j
  simp only [scalH_coe, cT, oneByOne, Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.transpose_apply,
    Matrix.of_apply, Finset.univ_unique, Finset.sum_singleton, smul_eq_mul, h1, h2]
  have hi : i = default := Subsingleton.elim _ _
  have hj : j = default := Subsingleton.elim _ _
  subst hi hj
  ring

theorem local_scal {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hcm : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (l : F) (hl : l ≠ 0) (c : ℝ≥0)
    (ν : Measure (HermR R σ 1)) (hν : ν.IsAddHaarMeasure)
    (h : ∀ τ : HermR R σ 1 → HermR R σ 1, (∀ S, (τ S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) =
      cT (sigR R σ) ((oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) *
        (S : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) *
        (oneByOne l : Matrix (Fin 1) (Fin 1) E).map (inclR R)) → ν.map τ = c • ν) :
    ν.map (scalH R σ (algebraMap F R l)) = NNReal.sqrt c • ν := by
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hR
  haveI := hTR
  haveI := hLC
  haveI := hSC
  haveI := hT2
  obtain ⟨iTR, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm R
  haveI := iTR
  obtain ⟨jLC, jSC, jT2, jB, -⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hcm R 1
  haveI := jLC
  haveI := jSC
  haveI := jT2
  haveI := jB
  exact map_eq_sqrt_smul (scalEquiv σ hcm R 1 l hl) ν c (h _ (action_eq R σ l))

theorem scal_module : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ l : F, l ≠ 0 → ∃ (cinf : ℝ≥0) (c : HeightOneSpectrum (𝓞 F) → ℝ≥0), IsUnitProd cinf c ∧ (∀ ν : Measure (HermR (Ainf F) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Ainf F) σ (algebraMap F (Ainf F) l)) = cinf • ν) ∧ ∀ v : HeightOneSpectrum (𝓞 F), ∀ ν : Measure (HermR (Fv F v) σ 1), ν.IsAddHaarMeasure → ν.map (GlobalTheory.CompanionTheory.SW.MassSimil.scalH (Fv F v) σ (algebraMap F (Fv F v) l)) = c v • ν := by
  intro F E _ _ _ _ _ σ hcm l hl
  have hdet : (oneByOne l : Matrix (Fin 1) (Fin 1) E).det ≠ 0 := by
    rw [Matrix.det_fin_one]
    exact (map_ne_zero (algebraMap F E)).2 hl
  obtain ⟨ci, c, hu, hi, hv⟩ := GlobalTheory.T.hermitian_matrix_euler_product F E σ hcm 1 (oneByOne l) hdet
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  refine ⟨NNReal.sqrt ci, fun v => NNReal.sqrt (c v), (PositivityTheory.PlacePermOperatorBicommutantSpan.up_alg F ci ci c c hu hu).2.2.2.2.2.1, ?_, ?_⟩
  · intro ν hν
    exact local_scal σ hcm (Ainf F) (GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hcm.1) l hl ci ν hν (hi ν hν)
  · intro v ν hν
    exact local_scal σ hcm (Fv F v) (GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v) l hl (c v) ν hν (hv v ν hν)

end GlobalTheory.CompanionTheory.SW.MassSimil.ScalModule

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictAntiOfTwoExceptionsStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strict_anti_of_two_exceptions : ∀ (l : ℕ) (hl : 3 ≤ l) (w : Fin l → ℕ) (hw : ∀ a, w a < l) (i j : Fin l) (hi : w i = 0) (hj : w j = l - 1) (h1 : ∀ a b, a < b → a ≠ i → b ≠ i → w b < w a) (h2 : ∀ a b, a < b → a ≠ j → b ≠ j → w b < w a), StrictAnti w := by
  first | exact @GlobalTheory.CompanionTheory.Segments.shufcomb | exact GlobalTheory.CompanionTheory.Segments.shufcomb | (intros; apply GlobalTheory.CompanionTheory.Segments.shufcomb <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureIndependentChoicesStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_independent_choices : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ μ' : Measure (HA (AF F) σ J)) (𝓕 𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → IsHaarH F E σ M J μ' → IsFDH F E σ M J μ' 𝓕' → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), thetaMeas σ J μ 𝓕 {X | gramE σ J X = T} = thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T} := by
  first | exact @GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | exact GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep | (intros; apply GlobalTheory.CompanionTheory.SW.ThetaIndep.thetaMeas_gram_indep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaMeasureSimilitudeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_measure_similitude : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ → IsFDH F E σ M J μ 𝓕 → ∀ (γ : GL (Fin M) E) (l : F), l ≠ 0 → cT (σ : E →+* E) (γ : Matrix (Fin M) (Fin M) E) * J * (γ : Matrix (Fin M) (Fin M) E) = (algebraMap F E l) • J → ∃ (μ' : Measure (HA (AF F) σ J)) (𝓕' : Set (HA (AF F) σ J)), IsHaarH F E σ M J μ' ∧ IsFDH F E σ M J μ' 𝓕' ∧ ∀ (n : ℕ) (T T' : Matrix (Fin n) (Fin n) E), T' = (algebraMap F E l) • T → (thetaMeas σ J μ' 𝓕' {X | gramE σ J X = T}).map (actTup (AF F) (bc (inclR (AF F)) γ)) = thetaMeas σ J μ 𝓕 {X | gramE σ J X = T'} := by
  first | exact @GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil | exact GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil | (intros; apply GlobalTheory.CompanionTheory.SW.SimTheta.theta_simil <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedSectionsUniformGeneratorsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_sections_uniform_generators : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsNoetherian X] (H : ReciprocityTheory.ChartRestriction.G.Semi.LB X), GlobalTheory.IsAmpleLB H → ∀ {P : X.Modules}, IsCoherent P → ∀ S : ℕ → Subobject P, ClosedSys I P S → ∀ (n₁ : ℤ) (W : ∀ n : ℤ, Set Γ(GlobalTheory.twistZ P H n, ⊤)), (∀ n e, W n ⊆ twSecs H n (S e)) → (∀ n, n₁ ≤ n → ∀ e, ∀ x ∈ twSecs H n (S e), ∃ b ∈ W n, x - b ∈ twPow I H n P (e + 1)) → ∃ B : Subobject P, (B : X.Modules).IsQuasicoherent ∧ ∀ e, B ⊔ powSub I P (e + 1) = S e := by
  first | exact @GlobalTheory.CompanionTheory.GE.TwGen.exists_alg_of_twSecs | exact GlobalTheory.CompanionTheory.GE.TwGen.exists_alg_of_twSecs | (intros; apply GlobalTheory.CompanionTheory.GE.TwGen.exists_alg_of_twSecs <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformLiftingOfSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_line_bundle_very_ample_system : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → (∀ e, IsProper (Y e).hom) → ∀ (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))), (∀ e, (N e).IsLB ∧ (v e).IsGen) → ∀ (d : ℕ), 1 ≤ d → ∀ (m : ℕ) (s : Fin (m + 1) → LB.Sec (pw (N 0) (d : ℤ))), VeryAmpleBy (Y 0).hom (pw (N 0) (d : ℤ)) s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ D : ℤ, D = d * t → ∀ (e : ℕ) (σ : LB.Sec (pw (N e) D)), ∃ σ' : LB.Sec (pw (N (e + 1)) D), SecMaps (pullPow (v e) D) σ (secPull σ' (β e)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_lift | exact GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_lift | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.Lift.exists_uniform_lift <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishingOfGradedNoetherianStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniform_vanishing_of_graded_noetherian : GradedNoeth → UniformVanishing := by
  first | exact @GlobalTheory.CompanionTheory.GE.UV.uniformVanishing | exact GlobalTheory.CompanionTheory.GE.UV.uniformVanishing | (intros; apply GlobalTheory.CompanionTheory.GE.UV.uniformVanishing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentConjugationMeasureInvariant
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib GlobalTheory.CompanionTheory.Rodier
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.HaarConj

theorem conj_measurePreserving : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] (U N : Subgroup G), IsClosed (U : Set G) → (∀ n ∈ N, ∀ u ∈ U, n * u * n⁻¹ ∈ U) → (∀ n ∈ N, ∃ L : Subgroup G, n ∈ L ∧ L ≤ N ∧ IsCompact (L : Set G)) → ∀ [MeasurableSpace U] [BorelSpace U] (μ : MeasureTheory.Measure U) [μ.IsHaarMeasure], ∀ n ∈ N, ∀ c : U → U, (∀ u, (c u : G) = n * u * n⁻¹) → MeasureTheory.MeasurePreserving c μ μ := by
  intro G _ _ _ _ _ _ U N hU hN hL _ _ μ _ n hn c hc
  have hninv : n⁻¹ ∈ N := N.inv_mem hn
  let d : U → U := fun u => ⟨n⁻¹ * u * n⁻¹⁻¹, hN _ hninv _ u.2⟩
  have hdc : ∀ u, d (c u) = u := fun u => Subtype.ext (by simp [d, hc, mul_assoc])
  have hcd : ∀ u, c (d u) = u := fun u => Subtype.ext (by simp [d, hc, mul_assoc])
  have hcmul : ∀ u v, c (u * v) = c u * c v := fun u v => Subtype.ext (by simp [hc, mul_assoc])
  have hcc : Continuous c := by
    refine Topology.IsEmbedding.subtypeVal.continuous_iff.2 ?_
    have : (Subtype.val ∘ c) = fun u : U => n * (u : G) * n⁻¹ := funext hc
    rw [this]
    fun_prop
  have hdc' : Continuous d := by
    refine Continuous.subtype_mk ?_ _
    fun_prop
  let e : U ≃* U :=
    { toFun := c, invFun := d, left_inv := hdc, right_inv := hcd, map_mul' := hcmul }
  haveI hH : (μ.map c).IsHaarMeasure := e.isHaarMeasure_map μ hcc hdc'
  haveI : LocallyCompactSpace U := hU.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology U := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  obtain ⟨L, hnL, -, hLc⟩ := hL n hn
  obtain ⟨Q, hQc, hQn⟩ := exists_compact_mem_nhds (1 : U)
  let K : Set G := (fun p : G × G => p.1 * p.2 * p.1⁻¹) '' ((L : Set G) ×ˢ (Subtype.val '' Q))
  have hK : IsCompact K := (hLc.prod (hQc.image continuous_subtype_val)).image (by fun_prop)
  let Q' : Set U := Subtype.val ⁻¹' K
  have hQ'c : IsCompact Q' := hU.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  have hQQ' : Q ⊆ Q' := fun q hq =>
    ⟨(1, (q : G)), ⟨L.one_mem, ⟨q, hq, rfl⟩⟩, by simp⟩
  have hpos : 0 < μ Q' :=
    (MeasureTheory.Measure.measure_pos_of_mem_nhds μ hQn).trans_le (MeasureTheory.measure_mono hQQ')
  have hfin : μ Q' ≠ ⊤ := hQ'c.measure_lt_top.ne
  have hpre : c ⁻¹' Q' = Q' := by
    ext u
    constructor
    · rintro ⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩
      refine ⟨(n⁻¹ * l, q), ⟨L.mul_mem (L.inv_mem hnL) hl, hq⟩, ?_⟩
      have h' : l * q * l⁻¹ = n * (u : G) * n⁻¹ := by
        rw [← hc]
        exact h
      change n⁻¹ * l * q * (n⁻¹ * l)⁻¹ = (u : G)
      calc n⁻¹ * l * q * (n⁻¹ * l)⁻¹ = n⁻¹ * (l * q * l⁻¹) * n := by group
        _ = (u : G) := by rw [h']; group
    · rintro ⟨⟨l, q⟩, ⟨hl, hq⟩, h⟩
      refine ⟨(n * l, q), ⟨L.mul_mem hnL hl, hq⟩, ?_⟩
      have h' : l * q * l⁻¹ = (u : G) := h
      change n * l * q * (n * l)⁻¹ = (c u : G)
      rw [hc, ← h']
      group
  have hmeas : MeasurableSet Q' := hQ'c.measurableSet
  have h1 : μ.map c Q' = μ Q' := by
    rw [MeasureTheory.Measure.map_apply hcc.measurable hmeas, hpre]
  have heq := MeasureTheory.Measure.isMulLeftInvariant_eq_smul (μ.map c) μ
  have h2 : ((MeasureTheory.Measure.haarScalarFactor (μ.map c) μ : NNReal) : ENNReal) * μ Q'
      = 1 * μ Q' := by
    have h3 := congrArg (fun ν : MeasureTheory.Measure U => ν Q') heq
    simp only [MeasureTheory.Measure.smul_apply, h1] at h3
    rw [one_mul]
    exact h3.symm.trans (by simp [ENNReal.smul_def])
  have hκ : MeasureTheory.Measure.haarScalarFactor (μ.map c) μ = 1 := by
    have := (ENNReal.mul_left_inj hpos.ne' hfin).1 h2
    exact_mod_cast this
  refine ⟨hcc.measurable, ?_⟩
  rw [heq, hκ, one_smul]

end GlobalTheory.CompanionTheory.HaarConj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerHeredityGenericProductStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_heredity_generic_product : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], WhitHeredity k → GenericProdIff k := by
  first | exact @GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | exact GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity | (intros; apply GlobalTheory.CompanionTheory.Leib.genericProdIff_of_whitHeredity <;> assumption)
end

