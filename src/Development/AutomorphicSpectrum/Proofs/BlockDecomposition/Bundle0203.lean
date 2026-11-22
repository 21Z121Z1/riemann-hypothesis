import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Formalism.RealPlaceAnalysis.Bundle0004
import Formalism.PeriodIntegrals.Bundle0022
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0132
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0198
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.Theta2Integral
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0176
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0194
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0032
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0195
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinHalfPlane.MirabolicGenerators.SideUnfold
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsOfPrimePowerRootOfUnity
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterion
import GroundTheory.ProfiniteCohomology.LocalTateDuality.KummerCup
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0196
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.HeisenbergTheta.HeisenbergThetaConstant.ThetaC

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DifferentiableAtOfSmooth
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiffOn_fderiv_field {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (A : E →L[ℝ] E) :
    ContDiffOn ℝ ∞ (fun g => fderiv ℝ f g (A g)) U := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  exact h1.clm_apply A.contDiff.contDiffOn

theorem fderiv_field_bracket {U : Set E} (hU : IsOpen U) {f : E → F} (hf : ContDiffOn ℝ ∞ f U) (A B : E →L[ℝ] E)
    {g : E} (hg : g ∈ U) :
    fderiv ℝ (fun y => fderiv ℝ f y (B y)) g (A g) - fderiv ℝ (fun y => fderiv ℝ f y (A y)) g (B g) =
      fderiv ℝ f g (B (A g) - A (B g)) := by
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ f) U := hf.fderiv_of_isOpen hU (by simp)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) g :=
    ((h1.contDiffAt (hU.mem_nhds hg)).differentiableAt (by simp))
  have hs : IsSymmSndFDerivAt ℝ f g :=
    (hf.contDiffAt (hU.mem_nhds hg)).isSymmSndFDerivAt (by simp; exact ENat.LEInfty.out)
  have hA := (h2.hasFDerivAt.clm_apply A.hasFDerivAt).fderiv
  have hB := (h2.hasFDerivAt.clm_apply B.hasFDerivAt).fderiv
  rw [hA, hB]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, map_sub]
  rw [hs.eq (A g) (B g)]
  abel

theorem fderiv_add_apply' {f h : E → F} {g : E} (hf : DifferentiableAt ℝ f g) (hh : DifferentiableAt ℝ h g) (v : E) :
    fderiv ℝ (f + h) g v = fderiv ℝ f g v + fderiv ℝ h g v := by
  rw [fderiv_add hf hh]; rfl

end General

theorem fderiv_csmul_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {f : E → F} {g : E} (hf : DifferentiableAt ℝ f g) (c : ℂ) (v : E) :
    fderiv ℝ (c • f) g v = c • fderiv ℝ f g v := by
  rw [fderiv_const_smul (R := ℂ) hf c]; rfl

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : Continuous fun g : Mat n => g.det := Continuous.matrix_det continuous_id
  exact isOpen_ne.preimage this

def mulR (X : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X)

def mulL (x : Mat n) : Mat n →L[ℝ] Mat n := LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ x)

@[simp] theorem mulR_apply (X g : Mat n) : mulR X g = g * X := rfl
@[simp] theorem mulL_apply (x g : Mat n) : mulL x g = x * g := rfl

theorem differentiableAt_of_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    DifferentiableAt ℝ f g :=
  ((hf.contDiffAt (isOpen_GLs.mem_nhds hg)).differentiableAt (by simp))

theorem Rd_contDiffOn (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Rd X f) (GLs n) :=
  contDiffOn_fderiv_field isOpen_GLs hf (mulR X)

theorem Rd_bracket (X Y : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Rd Y f) g - Rd Y (Rd X f) g = Rd (X * Y - Y * X) f g := by
  have := fderiv_field_bracket isOpen_GLs hf (mulR X) (mulR Y) hg
  have e : (mulR Y) ((mulR X) g) - (mulR X) ((mulR Y) g) = g * (X * Y - Y * X) := by
    show g * X * Y - g * Y * X = _
    simp [mul_sub, mul_assoc]
  exact this.trans (congrArg (fderiv ℝ f g) e)

theorem Rd_congr (X : Mat n) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) : Set.EqOn (Rd X f) (Rd X h) (GLs n) := by
  intro g hg
  have : f =ᶠ[nhds g] h := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) e
  simp [Rd, this.fderiv_eq]

theorem Rd_add_left (X Y : Mat n) (f : Mat n → V) : Rd (X + Y) f = Rd X f + Rd Y f := by
  funext g; simp [Rd, mul_add]

theorem Rd_smul_left (r : ℝ) (X : Mat n) (f : Mat n → V) : Rd (r • X) f = r • Rd X f := by
  funext g
  simp only [Rd, Pi.smul_apply, mul_smul_comm, map_smul]

theorem Rd_add {f h : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n)) (hh : ContDiffOn ℝ ∞ h (GLs n)) :
    Set.EqOn (Rd X (f + h)) (Rd X f + Rd X h) (GLs n) := by
  intro g hg
  exact fderiv_add_apply' (differentiableAt_of_smooth hf hg) (differentiableAt_of_smooth hh hg) _

theorem Rd_smul (c : ℂ) (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rd X (c • f)) (c • Rd X f) (GLs n) := by
  intro g hg
  exact fderiv_csmul_apply (differentiableAt_of_smooth hf hg) c _

def IBP : Prop :=
  ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (V : Type)
    [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (f : Mat n → V), ContDiffOn ℝ ∞ f (GLs n) → Cpt f →
    ∀ X, ∫ y : G n, Rd X f y.val ∂μ = 0

end GlobalTheory.CompanionTheory.RCalc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DwCons
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.SobGL

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

abbrev Idx (n : ℕ) := Bool × Fin n × Fin n

def cm {n : ℕ} (t : Idx n → ℝ) : Mat n := ∑ p, t p • bs p

def pd {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List ι → ((ι → ℝ) → V) → ((ι → ℝ) → V) :=
  fun L F => L.foldr (fun i H t => fderiv ℝ H t (Pi.single i 1)) F

def Dw {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] :
    List (Idx n) → (Mat n → V) → (Mat n → V) :=
  fun L f => L.foldr (fun p H y => fderiv ℝ H y (bs p)) f

theorem pd_nil {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : (ι → ℝ) → V) : pd [] F = F := rfl

theorem pd_cons {ι V : Type} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (i : ι) (L : List ι) (F : (ι → ℝ) → V) :
    pd (i :: L) F = fun t => fderiv ℝ (pd L F) t (Pi.single i 1) := rfl

theorem Dw_nil {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (f : Mat n → V) :
    Dw [] f = f := rfl

theorem Dw_cons {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (p : Idx n)
    (L : List (Idx n)) (f : Mat n → V) :
    Dw (p :: L) f = fun y => fderiv ℝ (Dw L f) y (bs p) := rfl

end GlobalTheory.CompanionTheory.SobGL
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EwordCoef
section
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.CoefWord

theorem eword_coef : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (hσ : Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset ε) σ) (v : GlobalTheory.SmoothVecMod.smoothVec ε σ) (w : H) (l : List (Fin n × Fin n)), ∀ g ∈ Formalism.MainNotions.S.UJset ε, Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ) g = ⟪w, σ g (((l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v : GlobalTheory.SmoothVecMod.smoothVec ε σ) : H)⟫_ℂ := by
  intro n ε H _ _ σ hσ v w l
  induction l with
  | nil =>
    intro g _
    rfl
  | cons p l ih =>
    intro g hg
    have hg' : Formalism.REAL.inUJ ε g := hg
    set u : GlobalTheory.SmoothVecMod.smoothVec ε σ :=
      (l.map fun ab => GlobalTheory.SmoothVecMod.unitAct hσ ab.1 ab.2).prod v with hu
    have h1 : Formalism.REAL.Eword ε (p :: l) (fun x => ⟪w, σ x (v : H)⟫_ℂ) g =
        Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g := rfl
    have h2 : Formalism.REAL.EabV ε p.1 p.2 (Formalism.REAL.Eword ε l (fun x => ⟪w, σ x (v : H)⟫_ℂ)) g =
        Formalism.REAL.EabV ε p.1 p.2 (fun x => innerSL ℂ w (σ x (u : H))) g :=
      GlobalTheory.SmoothVecMod.eabV_congr (fun x hx => ih x hx) p.1 p.2 hg'
    have h3 := GlobalTheory.CapelliCoef.eabV_pair (innerSL ℂ w) (f := fun x => σ x (u : H)) u.2 p.1 p.2 hg'
    have h4 := GlobalTheory.SmoothVecMod.rep_eabV hσ u.2 p.1 p.2 hg'
    rw [h1, h2, ← h3, ← h4]
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rfl

end GlobalTheory.CompanionTheory.CoefWord
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsNormTheta2TailLeOfLeOne
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing SchwartzMap ContDiff
open PositivityTheory.EisRk1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

namespace GlobalTheory.CompanionTheory.EisRk1

section Majorant

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_iteratedFDeriv_dilate_le (f : 𝓢(E, ℝ)) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (n : ℕ)
    (x : E) :
    ‖iteratedFDeriv ℝ n (fun y ↦ f (a • y)) x‖ ≤ ‖iteratedFDeriv ℝ n f (a • x)‖ := by
  have hg : (fun y ↦ f (a • y)) = f ∘ (a • ContinuousLinearMap.id ℝ E) := rfl
  have hle : ‖a • ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
    refine (norm_smul_le _ _).trans ?_
    rw [Real.norm_of_nonneg ha0]
    exact mul_le_one₀ ha1 (norm_nonneg _) ContinuousLinearMap.norm_id_le
  rw [hg, ContinuousLinearMap.iteratedFDeriv_comp_right _ (f.smooth ⊤) x
    (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _) fun _ _ ↦ hle

theorem exists_schwartz_majorant [FiniteDimensional ℝ E] (φ : 𝓢(E, ℂ)) :
    ∃ Φ : 𝓢(E, ℂ), ∃ r : E → ℝ, (∀ y, Φ y = (r y : ℂ)) ∧ ∀ y, ‖φ y‖ ≤ r y := by
  let b : ContDiffBump (0 : E) := ⟨1, 2, one_pos, by norm_num⟩
  let χ : 𝓢(E, ℝ) := b.hasCompactSupport.toSchwartzMap b.contDiff
  have hχ0 : ∀ y, 0 ≤ χ y := fun y ↦ b.nonneg
  have hχ1 : ∀ y, χ y ≤ 1 := fun y ↦ b.le_one
  have hχb : ∀ y, ‖y‖ ≤ 1 → χ y = 1 := fun y hy ↦
    b.one_of_mem_closedBall (by simpa [b] using hy)
  have hAex : ∀ m : ℕ, ∃ A : ℝ, ∀ y, (1 + ‖y‖) ^ m * ‖φ y‖ ≤ A := fun m ↦
    ⟨_, fun y ↦ by
      simpa using SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (m, 0)) le_rfl le_rfl
        φ y⟩
  choose A hA using hAex
  have hA0 : ∀ m, 0 ≤ A m := fun m ↦
    (by positivity : 0 ≤ (1 + ‖(0 : E)‖) ^ m * ‖φ 0‖).trans (hA m 0)
  let c : ℕ → ℝ := fun k ↦ ⨅ m : ℕ, A m / ((2 : ℝ) ^ k) ^ m
  have hbdd : ∀ k : ℕ, BddBelow (Set.range fun m : ℕ ↦ A m / ((2 : ℝ) ^ k) ^ m) := fun k ↦
    ⟨0, by rintro _ ⟨m, rfl⟩; exact div_nonneg (hA0 m) (by positivity)⟩
  have hc0 : ∀ k, 0 ≤ c k := fun k ↦ le_ciInf fun m ↦ div_nonneg (hA0 m) (by positivity)
  have hcle : ∀ k m, c k ≤ A m / ((2 : ℝ) ^ k) ^ m := fun k m ↦ ciInf_le (hbdd k) m
  have hsum : ∀ m : ℕ, Summable fun k : ℕ ↦ c k * ((2 : ℝ) ^ (k + 1)) ^ m := by
    intro m
    refine Summable.of_nonneg_of_le (fun k ↦ mul_nonneg (hc0 k) (by positivity)) (fun k ↦ ?_)
      (summable_geometric_two.mul_left (A (m + 1) * 2 ^ m))
    have e1 : ((2 : ℝ) ^ (k + 1)) ^ m = ((2 : ℝ) ^ k) ^ m * 2 ^ m := by
      rw [pow_succ, mul_pow]
    have e2 : ((2 : ℝ) ^ k) ^ (m + 1) = ((2 : ℝ) ^ k) ^ m * 2 ^ k := by rw [pow_succ]
    calc c k * ((2 : ℝ) ^ (k + 1)) ^ m
        ≤ A (m + 1) / ((2 : ℝ) ^ k) ^ (m + 1) * ((2 : ℝ) ^ (k + 1)) ^ m := by
          gcongr
          exact hcle k (m + 1)
      _ = A (m + 1) * 2 ^ m * (1 / 2) ^ k := by
          rw [e1, e2, one_div, inv_pow]
          field_simp
  let a : ℕ → ℝ := fun k ↦ ((2 : ℝ) ^ (k + 1))⁻¹
  have ha0 : ∀ k, 0 ≤ a k := fun k ↦ by positivity
  have ha1 : ∀ k, a k ≤ 1 := fun k ↦ inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  let f : ℕ → E → ℝ := fun k y ↦ c k * χ (a k • y)
  have hfsm : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (f k) := fun k ↦
    contDiff_const.mul ((χ.smooth ⊤).comp (contDiff_const.smul contDiff_id))
  choose D hD using fun (m n : ℕ) ↦ χ.decay' m n
  have hfd : ∀ (k m n : ℕ) (x : E),
      ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (f k) x‖ ≤ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n := by
    intro k m n x
    have e1 : iteratedFDeriv ℝ n (f k) x =
        c k • iteratedFDeriv ℝ n (fun y ↦ χ (a k • y)) x :=
      iteratedFDeriv_const_smul_apply (a := c k) (f := fun y ↦ χ (a k • y))
        (((χ.smooth ⊤).comp (contDiff_const.smul contDiff_id)).contDiffAt.of_le
          (by exact_mod_cast le_top))
    have e2 : ‖x‖ = (2 : ℝ) ^ (k + 1) * ‖a k • x‖ := by
      rw [norm_smul, Real.norm_of_nonneg (ha0 k), ← mul_assoc, mul_inv_cancel₀ (by positivity),
        one_mul]
    rw [e1, norm_smul, Real.norm_of_nonneg (hc0 k)]
    calc ‖x‖ ^ m * (c k * ‖iteratedFDeriv ℝ n (fun y ↦ χ (a k • y)) x‖)
        ≤ ‖x‖ ^ m * (c k * ‖iteratedFDeriv ℝ n χ (a k • x)‖) := by
          have := norm_iteratedFDeriv_dilate_le χ (ha0 k) (ha1 k) n x
          have := hc0 k
          gcongr
      _ = c k * ((2 : ℝ) ^ (k + 1)) ^ m *
            (‖a k • x‖ ^ m * ‖iteratedFDeriv ℝ n χ (a k • x)‖) := by
          rw [e2, mul_pow]
          ring
      _ ≤ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n := by
          exact mul_le_mul_of_nonneg_left (hD m n (a k • x))
            (mul_nonneg (hc0 k) (by positivity))
  have hfv : ∀ (n k : ℕ) (x : E), ‖iteratedFDeriv ℝ n (f k) x‖ ≤ c k * D 0 n := by
    intro n k x
    simpa using hfd k 0 n x
  have hsv : ∀ n : ℕ, Summable fun k ↦ c k * D 0 n := fun n ↦ by
    simpa using (hsum 0).mul_right (D 0 n)
  have hsmooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun y ↦ ∑' k, f k y :=
    contDiff_tsum (v := fun n k ↦ c k * D 0 n) hfsm (fun n _ ↦ hsv n) fun n k x _ ↦ hfv n k x
  let Φr : 𝓢(E, ℝ) :=
    { toFun := fun y ↦ ∑' k, f k y
      smooth' := hsmooth
      decay' := by
        intro m n
        refine ⟨(∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m) * D m n, fun x ↦ ?_⟩
        rw [iteratedFDeriv_tsum_apply (v := fun n k ↦ c k * D 0 n) hfsm (fun n _ ↦ hsv n)
          (fun n k x _ ↦ hfv n k x) (by exact_mod_cast le_top) x]
        have hs1 : Summable fun k ↦ ‖iteratedFDeriv ℝ n (f k) x‖ :=
          Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ hfv n k x) (hsv n)
        have hs2 : Summable fun k ↦ c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n :=
          (hsum m).mul_right _
        calc ‖x‖ ^ m * ‖∑' k, iteratedFDeriv ℝ n (f k) x‖
            ≤ ‖x‖ ^ m * ∑' k, ‖iteratedFDeriv ℝ n (f k) x‖ := by
              gcongr
              exact norm_tsum_le_tsum_norm hs1
          _ = ∑' k, ‖x‖ ^ m * ‖iteratedFDeriv ℝ n (f k) x‖ := tsum_mul_left.symm
          _ ≤ ∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m * D m n :=
              (hs1.mul_left _).tsum_le_tsum (fun k ↦ hfd k m n x) hs2
          _ = (∑' k, c k * ((2 : ℝ) ^ (k + 1)) ^ m) * D m n := tsum_mul_right }
  refine ⟨SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM Φr, Φr, fun y ↦ rfl, fun y ↦ ?_⟩
  have hf0 : ∀ k, 0 ≤ f k y := fun k ↦ mul_nonneg (hc0 k) (hχ0 _)
  have hfs : Summable fun k ↦ f k y := by
    refine Summable.of_nonneg_of_le hf0 (fun k ↦ ?_) (by simpa using hsum 0)
    exact mul_le_of_le_one_right (hc0 k) (hχ1 _)
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near (x := 1 + ‖y‖) (y := (2 : ℝ))
    (by linarith [norm_nonneg y]) (by norm_num)
  have h1 : ‖φ y‖ ≤ c k := by
    refine le_ciInf fun m ↦ ?_
    rw [le_div_iff₀ (by positivity), mul_comm]
    refine le_trans ?_ (hA m y)
    gcongr
  have h2 : f k y = c k := by
    have : χ (a k • y) = 1 := by
      refine hχb _ ?_
      rw [norm_smul, Real.norm_of_nonneg (ha0 k), inv_mul_le_iff₀ (by positivity), mul_one]
      linarith
    simp only [f, this, mul_one]
  calc ‖φ y‖ ≤ f k y := h2 ▸ h1
    _ ≤ ∑' k, f k y := hfs.le_tsum k fun j _ ↦ hf0 j

end Majorant

set_option maxSynthPendingDepth 1
set_option synthInstance.maxSize 1000

variable {K : Type _} [Field K] [NumberField K]

noncomputable def contragredient (h : GL (Fin 2) 𝔸[K]) : GL (Fin 2) 𝔸[K] :=
  ⟨((h⁻¹ : GL (Fin 2) 𝔸[K]) : Matrix (Fin 2) (Fin 2) 𝔸[K])ᵀ,
    (h : Matrix (Fin 2) (Fin 2) 𝔸[K])ᵀ,
    by rw [← transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, transpose_one],
    by rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one]⟩

end GlobalTheory.CompanionTheory.EisRk1
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationDividedPowerStructures
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.PerfFil

variable {l : ℕ} [Fact l.Prime] (A : PAlg l)

theorem exists_natCast_mul_eq_l_pow {n k : ℕ} (hn : n ≠ 0) (hk : n.factorization l ≤ k) :
    ∃ w : A.Acr0, (n : A.Acr0) * w = (l : A.Acr0) ^ k := by
  obtain ⟨w, hw⟩ := ACris.exists_natCast_mul_eq_pow (K := ℂ_[l]) (p := l) hn hk
  refine ⟨algebraMap A.W A.Acr0 (A.sW w), ?_⟩
  have h := congrArg (fun t => algebraMap A.W A.Acr0 (A.sW t)) hw
  simpa using h

theorem exists_divided_power_of_dividedXi {j k : ℕ} (hj : j ≠ 0) (hk : k ≠ 0) :
    ∃ y ∈ A.Fil0 1, (k.factorial : A.Acr0) * y = A.dxi0 j ^ k := by
  obtain ⟨-, -, hf, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  refine ⟨(Nat.uniformBell k j : A.Acr0) * A.dxi0 (k * j),
    Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨k * j, Nat.mul_pos (Nat.pos_of_ne_zero hk)
      (Nat.pos_of_ne_zero hj), rfl⟩), ?_⟩
  have hnz := A.acris_torsion_free (j.factorial ^ k) (pow_ne_zero k j.factorial_ne_zero)
  refine (mul_cancel_left_mem_nonZeroDivisors hnz).1 ?_
  have h1 : ((j.factorial ^ k : ℕ) : A.Acr0) *
      ((k.factorial : A.Acr0) * ((Nat.uniformBell k j : A.Acr0) * A.dxi0 (k * j))) =
      ((k * j).factorial : A.Acr0) * A.dxi0 (k * j) := by
    rw [← Nat.uniformBell_mul_eq k hj]
    push_cast
    ring
  rw [h1, hf, pow_mul', ← hf j]
  push_cast
  ring

theorem exists_l_pow {k : ℕ} (hk : k ≠ 0) :
    ∃ y ∈ Ideal.span {(l : A.Acr0)}, (k.factorial : A.Acr0) * y = (l : A.Acr0) ^ k := by
  have hv : k.factorial.factorization l ≤ k - 1 := by
    rw [Nat.factorization_def _ Fact.out]
    have h := sub_one_mul_padicValNat_factorial_lt_of_ne_zero (p := l) hk
    have h2 : 1 ≤ l - 1 := Nat.le_sub_of_add_le (Fact.out : l.Prime).two_le
    have h3 : padicValNat l k.factorial ≤ (l - 1) * padicValNat l k.factorial :=
      Nat.le_mul_of_pos_left _ h2
    omega
  obtain ⟨w, hw⟩ := exists_natCast_mul_eq_l_pow A k.factorial_ne_zero hv
  refine ⟨(l : A.Acr0) * w, Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _), ?_⟩
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  rw [mul_left_comm, hw]
  simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
  ring

theorem filtration_one_eq_span_dividedXi : A.Fil0 1 = Ideal.span {z | ∃ k, 1 ≤ k ∧ z = A.dxi0 k} := rfl

theorem pFil0_eq : A.PFil0 = Ideal.span ({(l : A.Acr0)} ∪ {z | ∃ k, 1 ≤ k ∧ z = A.dxi0 k}) := by
  rw [Ideal.span_union]
  rfl

theorem filtration_one_has_divided_powers : R.PdI (A.Fil0 1) := by
  rw [filtration_one_eq_span_dividedXi]
  refine GlobalTheory.CompanionTheory.DivPow.pdI_span A.acris_torsion_free _ ?_
  rintro _ ⟨j, hj, rfl⟩ k hk
  exact exists_divided_power_of_dividedXi A (by omega) hk

theorem pdI_pFil0 : R.PdI A.PFil0 := by
  rw [pFil0_eq]
  refine GlobalTheory.CompanionTheory.DivPow.pdI_span A.acris_torsion_free _ ?_
  rw [← pFil0_eq]
  rintro x (rfl | ⟨j, hj, rfl⟩) k hk
  · obtain ⟨y, hy, e⟩ := exists_l_pow A hk
    exact ⟨y, (le_sup_left : _ ≤ A.PFil0) hy, e⟩
  · obtain ⟨y, hy, e⟩ := exists_divided_power_of_dividedXi A (by omega : j ≠ 0) hk
    exact ⟨y, (le_sup_right : _ ≤ A.PFil0) hy, e⟩

theorem pow_mem_filtration_of_mem_one {x : A.Acr0} (hx : x ∈ A.Fil0 1) (k : ℕ) : x ^ k ∈ A.Fil0 k := by
  obtain ⟨h0, -, -, hm, -⟩ := GlobalTheory.T.crystalline_filtration_multiplicative A
  induction k with
  | zero => rw [h0]; exact Submodule.mem_top
  | succ k ih => rw [pow_succ]; exact hm k 1 (Ideal.mul_mem_mul ih hx)

theorem mem_filtration_of_prime_pow_mul_mem (r N : ℕ) (z : A.Acr0) (h : (l : A.Acr0) ^ N * z ∈ A.Fil0 r) :
    z ∈ A.Fil0 r := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    refine ih (GlobalTheory.T.crystalline_filtration_saturated A r _ ?_)
    rw [← mul_assoc, ← pow_succ']
    exact h

theorem mem_filtration_of_factorial_mul_eq_pow {x : A.Acr0} (hx : x ∈ A.Fil0 1) (k : ℕ) (y : A.Acr0)
    (e : (k.factorial : A.Acr0) * y = x ^ k) : y ∈ A.Fil0 k := by
  obtain ⟨w, hw⟩ := exists_natCast_mul_eq_l_pow A k.factorial_ne_zero le_rfl
  refine mem_filtration_of_prime_pow_mul_mem A k (k.factorial.factorization l) y ?_
  rw [← hw, mul_right_comm, e, mul_comm]
  exact Ideal.mul_mem_left _ _ (pow_mem_filtration_of_mem_one A hx k)

theorem pdI_main : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.PdI (A.Fil0 1) ∧ R.PdI A.PFil0 ∧
    ∀ x ∈ A.Fil0 1, ∀ (k : ℕ) (y : A.Acr0), (k.factorial : A.Acr0) * y = x ^ k → y ∈ A.Fil0 k :=
  fun A => ⟨filtration_one_has_divided_powers A, pdI_pFil0 A, fun _ hx k y e => mem_filtration_of_factorial_mul_eq_pow A hx k y e⟩

end GlobalTheory.CompanionTheory.PerfFil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightTermGoodStatement
section
open PositivityTheory.RgEis PositivityTheory.RgEis.MG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_term_good : HGood := by
  first | exact @GlobalTheory.CompanionTheory.RgEisHGood.hGood | exact GlobalTheory.CompanionTheory.RgEisHGood.hGood | (intros; apply GlobalTheory.CompanionTheory.RgEisHGood.hGood <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdempotentsOfPrimePowerRootOfUnityStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotents_of_prime_power_root_of_unity : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l), R.Val (l : A.U) → ∀ (n : ℕ) (ζ : OC l), IsPrimitiveRoot ζ (l ^ n) → ∀ z : A.U, z ^ l ^ n = 1 → ∃ e : ZMod (l ^ n) → A.A, (haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩; CompleteOrthogonalIdempotents e) ∧ ∀ c, A.sharp (e c) * (z - A.oC ζ ^ c.val) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RootsLC.exists_idempotents_of_root_of_unity | exact GlobalTheory.CompanionTheory.RootsLC.exists_idempotents_of_root_of_unity | (intros; apply GlobalTheory.CompanionTheory.RootsLC.exists_idempotents_of_root_of_unity <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsDSSkImpUpqRep
section
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiscreteSeries

theorem isDS_sk_imp_upqRep (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    Formalism.MainNotions.S.IsDS ε lam σ → PI.UpqRep.IsDS ε lam σ :=
  fun h => h

end GlobalTheory.CompanionTheory.DiscreteSeries
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KummerCocycleNormCriterionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_cocycle_norm_criterion : ∀ {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (N : ℕ), 0 < N → ∀ ζ : Ω, IsPrimitiveRoot ζ N → ∀ c0 : (Ω ≃ₐ[K] Ω) → ZMod N, (∀ g : Ω ≃ₐ[K] Ω, g ζ = ζ ^ (c0 g).val) → ∀ ψ : (Ω ≃ₐ[K] Ω) →* Multiplicative (ZMod N), IsOpen (ψ.ker : Set (Ω ≃ₐ[K] Ω)) → ∀ U : Kˣ, (∃ y : IntermediateField.fixedField ψ.ker, Algebra.norm K y = (U : K)) → ∀ (T : Ω) (κ : (Ω ≃ₐ[K] Ω) → ZMod N), T ^ N = algebraMap K Ω (U : K) → (∀ g : Ω ≃ₐ[K] Ω, g T = ζ ^ (κ g).val * T) → ∃ c : (Ω ≃ₐ[K] Ω) → ZMod N, IsLocallyConstant c ∧ ∀ g h : Ω ≃ₐ[K] Ω, c0 g * c h - c (g * h) + c g = κ g * Multiplicative.toAdd (ψ h) := by
  first | exact @GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary | exact GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary | (intros; apply GlobalTheory.CompanionTheory.KummerCup.kummerCup_eq_coboundary <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearChangeMemSchwartzBruhatPiStatement
section
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.He2M1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix IdeleGroup PositivityTheory.RgEis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearChange_mem_schwartzBruhatPi : ∀ {k : Type} [Field k] [NumberField k], ∀ {ι : Type} [Fintype ι] [DecidableEq ι], ∀ {F : (ι → 𝔸[k]) → ℂ} (hF : F ∈ schwartzBruhatPi k ι) (A : GL ι 𝔸[k]), ltr A F ∈ schwartzBruhatPi k ι := by
  first | exact @GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | exact GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem | (intros; apply GlobalTheory.CompanionTheory.LinearChangeSchwartzBruhat.ltr_mem <;> assumption)
end

