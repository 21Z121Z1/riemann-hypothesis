import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0207
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0203
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveSolutionExistence
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0204
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0213
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.JointGeneralisedEigenvectors.CasselmanStrictlyDominantExample
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0034
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0218
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IteratedDerivTwoSmul
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff Topology
open PositivityTheory.RgBcC GlobalTheory.CompanionTheory.WaveK GlobalTheory.CompanionTheory.WaveK.Base
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveK.Lin

variable {n : ℕ}

section Ops

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Eu_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) := by
  have h := fun X : Mat n => GlobalTheory.CompanionTheory.RCalc.Rd_contDiffOn X hf
  unfold Eu
  exact ((h _).add (contDiffOn_const.smul (h _))).const_smul _

theorem Epow_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simp only [Epow, if_neg hab]
      exact contDiffOn_const (c := (0 : V))
  | succ m ih =>
    intro a b
    have e : Epow s (m + 1) a b f = fun x => ∑ c, Eu s a c (Epow s m c b f) x := by
      ext x
      simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun c _ => Eu_smooth (ih c b) s a c

theorem Eu_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) (s : Bool)
    (a b : Fin n) : Set.EqOn (Eu s a b (f + f')) (Eu s a b f + Eu s a b f') (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, GlobalTheory.CompanionTheory.RCalc.Rd_add _ hf hf' hx, smul_add]
  abel

theorem Eu_smul (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (a b : Fin n) :
    Set.EqOn (Eu s a b (c • f)) (c • Eu s a b f) (GLs n) := by
  intro x hx
  simp only [Eu, Pi.smul_apply, Pi.add_apply, GlobalTheory.CompanionTheory.RCalc.Rd_smul c _ hf hx]
  module

theorem Epow_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : ∀ a b : Fin n, Set.EqOn (Epow s m a b (f + f')) (Epow s m a b f + Epow s m a b f') (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_add (Epow_smooth hf s m c b) (Epow_smooth hf' s m c b) s a c hx

theorem Epow_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    ∀ a b : Fin n, Set.EqOn (Epow s m a b (k • f)) (k • Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b x hx
    by_cases hab : a = b <;> simp [Epow, hab]
  | succ m ih =>
    intro a b x hx
    simp only [Epow, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [GlobalTheory.CompanionTheory.WaveAll.Eu_congr GlobalTheory.CompanionTheory.WaveAll.isOpen_GLs (ih c b) s a c hx]
    exact Eu_smul k (Epow_smooth hf s m c b) s a c hx

theorem gel_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    (s : Bool) (m : ℕ) : Set.EqOn (gel s m (f + f')) (gel s m f + gel s m f') (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => Epow_add hf hf' s m a a hx

theorem gel_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (s : Bool) (m : ℕ) :
    Set.EqOn (gel s m (k • f)) (k • gel s m f) (GLs n) := by
  intro x hx
  simp only [gel, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_congr rfl fun a _ => Epow_smul k hf s m a a hx

theorem Om_add {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n)) :
    Set.EqOn (Om (f + f')) (Om f + Om f') (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_add hf hf' _ _ hx, smul_add]
  abel

theorem Om_smul (k : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Om (k • f)) (k • Om f) (GLs n) := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_smul k hf _ _ hx]
  module

theorem iterated_integral_add {w w' : ℝ → V} (hw : ContDiff ℝ ∞ w) (hw' : ContDiff ℝ ∞ w') (t : ℝ) :
    iteratedDeriv 2 (fun s => w s + w' s) t = iteratedDeriv 2 w t + iteratedDeriv 2 w' t := by
  have h2 : ∀ φ : ℝ → V, iteratedDeriv 2 φ = deriv (deriv φ) := fun φ => by
    rw [iteratedDeriv_eq_iterate]; rfl
  have hd : deriv (fun s => w s + w' s) = fun s => deriv w s + deriv w' s :=
    funext fun s => deriv_fun_add (hw.differentiable (by simp) s) (hw'.differentiable (by simp) s)
  have e1 : Differentiable ℝ (deriv w) := (contDiff_infty_iff_deriv.1 hw).2.differentiable (by simp)
  have e2 : Differentiable ℝ (deriv w') := (contDiff_infty_iff_deriv.1 hw').2.differentiable (by simp)
  rw [h2, h2, h2, hd]
  exact deriv_fun_add (e1 t) (e2 t)

theorem iteratedDeriv_two_smul (k : ℂ) {w : ℝ → V} (hw : ContDiff ℝ ∞ w) (t : ℝ) :
    iteratedDeriv 2 (fun s => k • w s) t = k • iteratedDeriv 2 w t := by
  have h2 : ∀ φ : ℝ → V, iteratedDeriv 2 φ = deriv (deriv φ) := fun φ => by
    rw [iteratedDeriv_eq_iterate]; rfl
  have hd : deriv (fun s => k • w s) = fun s => k • deriv w s :=
    funext fun s => deriv_fun_const_smul k (hw.differentiable (by simp) s)
  have e1 : Differentiable ℝ (deriv w) := (contDiff_infty_iff_deriv.1 hw).2.differentiable (by simp)
  rw [h2, h2, hd]
  exact deriv_fun_const_smul k (e1 t)

end Ops

theorem wave_add {E : KMod n} {u v : ℝ → Mat n → E.V} (hu : IsWave E u) (hv : IsWave E v) :
    IsWave E fun t y => u t y + v t y := by
  refine ⟨hu.1.add hv.1, fun t => ⟨(hu.2.1 t).1.add (hv.2.1 t).1, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · intro g hg k
    simp only [(hu.2.1 t).2 g hg k, (hv.2.1 t).2 g hg k, map_add]
  · rw [iterated_integral_add (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg) (GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg), hu.2.2.1 t g hg, hv.2.2.1 t g hg]
    exact (Om_add (hu.2.1 t).1 (hv.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    have h2 : DifferentiableAt ℝ (fun s => v s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hv hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_add h1 h2, hu.2.2.2 g hg, hv.2.2.2 g hg, add_zero]

theorem wave_smul (k : ℂ) {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) :
    IsWave E fun t y => k • u t y := by
  refine ⟨hu.1.const_smul k, fun t => ⟨(hu.2.1 t).1.const_smul k, ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · intro g hg k'
    simp only [(hu.2.1 t).2 g hg k', map_smul]
  · rw [iteratedDeriv_two_smul k (GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg), hu.2.2.1 t g hg]
    exact (Om_smul k (hu.2.1 t).1 hg).symm
  · have h1 : DifferentiableAt ℝ (fun s => u s g) 0 :=
      ((GlobalTheory.CompanionTheory.WaveAll.wave_line hu hg).differentiable (by simp)).differentiableAt
    rw [deriv_fun_const_smul k h1, hu.2.2.2 g hg, smul_zero]

end GlobalTheory.CompanionTheory.WaveK.Lin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelMultiplierOnEigenfunction
section
noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.EigAct

variable {n : ℕ}

section Ops
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rd_smul (b : ℂ) (X : Mat n) (f : Mat n → V) : Rd X (b • f) = b • Rd X f := by
  funext g
  have : fderiv ℝ (b • f) = b • fderiv ℝ f := fderiv_const_smul_field b
  simp only [Rd, this, Pi.smul_apply]
  rfl

theorem Eu_smul (b : ℂ) (s : Bool) (a c : Fin n) (f : Mat n → V) : Eu s a c (b • f) = b • Eu s a c f := by
  simp only [Eu, Rd_smul]
  module

theorem Epow_smul (b : ℂ) (s : Bool) (m : ℕ) (a c : Fin n) (f : Mat n → V) :
    Epow s m a c (b • f) = b • Epow s m a c f := by
  induction m generalizing a c with
  | zero =>
    simp only [Epow]
    split_ifs <;> simp
  | succ m ih =>
    simp only [Epow, ih, Eu_smul, Finset.smul_sum]

theorem gel_smul (b : ℂ) (s : Bool) (m : ℕ) (f : Mat n → V) : gel s m (b • f) = b • gel s m f := by
  simp only [gel, Epow_smul, Finset.smul_sum]

theorem Om_smul (b : ℂ) (f : Mat n → V) : Om (b • f) = b • Om f := by
  simp only [Om, gel_smul]
  module

theorem zOp_smul (b : ℂ) (w : List (Bool × ℕ)) (f : Mat n → V) : zOp w (b • f) = b • zOp w f := by
  induction w with
  | nil => rfl
  | cons p w ih => simp only [zOp, ih, gel_smul]

theorem zOp_eig {χ : Inf n} {f : Mat n → V} (hf : IsEig χ f) (w : List (Bool × ℕ)) :
    ∀ x ∈ GLs n, zOp w f x = zVal w χ • f x := by
  induction w with
  | nil => intro x _; simp [zOp, zVal]
  | cons p w ih =>
    intro x hx
    have h := GlobalTheory.CompanionTheory.WaveMult.zOp_agree_GLs n [p] (zOp w f) (zVal w χ • f) (fun g hg => by simpa using ih g hg) x hx
    have h1 : zOp (p :: w) f x = gel p.1 p.2 (zVal w χ • f) x := by simpa [zOp] using h
    rw [h1, gel_smul, Pi.smul_apply, hf p.1 p.2 x hx, smul_smul]
    simp [zVal, mul_comm]

theorem Om_eig {χ : Inf n} {f : Mat n → V} (hf : IsEig χ f) : ∀ x ∈ GLs n, Om f x = cas χ • f x := by
  intro x hx
  simp only [Om, Pi.smul_apply, Pi.add_apply, hf _ _ x hx, cas]
  module

end Ops

theorem hasDerivAt_cosh_mul (a : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.cosh (r * a)) (Complex.sinh (s * a) * a) s := by
  have e : HasDerivAt (fun r : ℝ => (r : ℂ) * a) a s := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const a
  exact (Complex.hasDerivAt_cosh ((s : ℂ) * a)).comp s e

theorem hasDerivAt_sinh_mul (a : ℂ) (s : ℝ) :
    HasDerivAt (fun r : ℝ => Complex.sinh (r * a)) (Complex.cosh (s * a) * a) s := by
  have e : HasDerivAt (fun r : ℝ => (r : ℂ) * a) a s := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const a
  exact (Complex.hasDerivAt_sinh ((s : ℂ) * a)).comp s e

theorem isWave_cosh (E : KMod n) {χ : Inf n} {f : Mat n → E.V} (hf : f ∈ CE E) (he : IsEig χ f) {a : ℂ}
    (ha : a ^ 2 = cas χ) : IsWave E (fun t x => Complex.cosh (t * a) • f x) := by
  have d1 : ∀ (v : E.V) (s : ℝ), HasDerivAt (fun r : ℝ => Complex.cosh (r * a) • v)
      ((Complex.sinh (s * a) * a) • v) s := fun v s => (hasDerivAt_cosh_mul a s).smul_const v
  have d2 : ∀ (v : E.V) (s : ℝ), HasDerivAt (fun r : ℝ => (Complex.sinh (r * a) * a) • v)
      ((Complex.cosh (s * a) * a * a) • v) s := fun v s =>
    ((hasDerivAt_sinh_mul a s).mul_const a).smul_const v
  refine ⟨?_, fun t => ⟨?_, fun g hg k => ?_⟩, fun t g hg => ?_, fun g _ => ?_⟩
  · have hc : ContDiff ℝ ∞ (fun t : ℝ => Complex.cosh (t * a)) :=
      (Complex.contDiff_cosh.restrict_scalars ℝ).comp (Complex.ofRealCLM.contDiff.mul contDiff_const)
    have h1 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => Complex.cosh (p.1 * a)) (Set.univ ×ˢ GLs n) :=
      (hc.comp contDiff_fst).contDiffOn
    have h2 : ContDiffOn ℝ ∞ (fun p : ℝ × Mat n => f p.2) (Set.univ ×ˢ GLs n) :=
      hf.1.comp contDiff_snd.contDiffOn (fun p hp => hp.2)
    exact h1.smul h2
  · exact contDiffOn_const.smul hf.1
  · simp only [hf.2 g hg k, map_smul]
  · have hOm : Om (fun x => Complex.cosh (t * a) • f x) g = Complex.cosh (t * a) • Om f g :=
      congrFun (Om_smul (Complex.cosh (t * a)) f) g
    have D1 : deriv (fun r : ℝ => Complex.cosh (r * a) • f g) = fun r : ℝ => (Complex.sinh (r * a) * a) • f g :=
      funext fun s => (d1 (f g) s).deriv
    rw [hOm, Om_eig he g hg, iteratedDeriv_succ, iteratedDeriv_one, D1, (d2 (f g) t).deriv, ← ha, smul_smul]
    congr 1
    ring
  · rw [(d1 (f g) 0).deriv]
    simp

section Ker
variable [MeasurableSpace (G n)] (μ : Measure (G n)) (E : KMod n)

theorem act_of_isKer {w : List (Bool × ℕ)} {g : ℝ → ℝ} {ks : Mat n → (E.V →L[ℂ] E.V)}
    (hK : IsKer μ E w g ks) {χ : Inf n} {f : Mat n → E.V} (hf : f ∈ CE E) (he : IsEig χ f) {x : Mat n}
    (hx : x ∈ GLs n) : act μ E ks f x = (zVal w χ * coshT g (cas χ)) • f x := by
  have := FiniteDimensional.complete ℂ E.V
  have ha : ((cas χ) ^ (1 / 2 : ℂ)) ^ 2 = cas χ := by
    have := Complex.cpow_nat_inv_pow (cas χ) (n := 2) two_ne_zero
    simpa [one_div] using this
  have hw := hK.2.2.2 _ (isWave_cosh E hf he ha) x hx
  have h0 : (fun x' => Complex.cosh (((0 : ℝ) : ℂ) * (cas χ) ^ (1 / 2 : ℂ)) • f x') = f := by
    funext x'
    simp
  have h1 : (fun x' => ∫ t : ℝ, (g t : ℂ) • (fun t' x'' => Complex.cosh ((t' : ℂ) * (cas χ) ^ (1 / 2 : ℂ)) • f x'') t x') =
      coshT g (cas χ) • f := by
    funext x'
    simp only [smul_smul, Pi.smul_apply, coshT]
    exact integral_smul_const _ _
  rw [h0, h1, zOp_smul, Pi.smul_apply, zOp_eig he w x hx, smul_smul, mul_comm] at hw
  exact hw

end Ker

end GlobalTheory.CompanionTheory.WaveMult.EigAct

namespace GlobalTheory.CompanionTheory.WaveMult

theorem act_eq_val_of_isMult : LgFacts → ∀ (n : ℕ) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (k : Mat n → (E.V →L[ℂ] E.V)) (val : Inf n → ℂ) (T : ℝ), IsMult μ E k val T → ∀ χ, ∀ f ∈ CE E, IsEig χ f → ∀ x ∈ GLs n, act μ E k f x = val χ • f x := by
  rintro hL n _ _ μ _ E k val T ⟨m, c, w, g, ks, h1, h2, h3⟩ χ f hf he x hx
  have h := GlobalTheory.CompanionTheory.WaveMult.act_eq_sum_of_kernel hL n μ E c ks k f (fun i => ⟨(h1 i).2.1.continuousOn, (h1 i).2.2.1⟩) h2
    hf.1.continuousOn x hx
  rw [h, h3 χ, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [EigAct.act_of_isKer μ E (h1 i).2 hf he hx, smul_smul, mul_assoc]

end GlobalTheory.CompanionTheory.WaveMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemIwGLOfDiag
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
open scoped Pointwise

namespace GlobalTheory.CompanionTheory.EigTorus

theorem exists_common_eigenvector : ∀ (d : ℕ) (E : Type) [AddCommGroup E] [Module ℂ E] [FiniteDimensional ℂ E]
    {I : Type} (T : I → Module.End ℂ E), (∀ a b, Commute (T a) (T b)) → Module.finrank ℂ E = d → 0 < d →
    ∃ w : E, w ≠ 0 ∧ ∃ c : I → ℂ, ∀ i, T i w = c i • w :=
  _root_.UpperTheory.Reformulated.B.Ygb8.main

theorem diag_commute {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} {g h : GL (Fin n) L}
    (hg : IsDiagM g) (hh : IsDiagM h) : g * h = h * g := by
  have key : ∀ a : GL (Fin n) L, IsDiagM a →
      (a : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => (a : Matrix (Fin n) (Fin n) L) i i) := by
    intro a ha
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.diagonal_apply_ne _ hij, ha i j hij]
  apply Units.ext
  simp only [Units.val_mul]
  rw [key g hg, key h hh, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  congr 1
  ext i
  exact mul_comm _ _

theorem mem_latK_iff {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (a : GL (Fin n) L)
    (ha : IsDiagM a) (hv : ∀ i, Valued.v ((a : Matrix (Fin n) (Fin n) L) i i) = 1) (k : ℕ) (x : Fin n → L) :
    (a : Matrix (Fin n) (Fin n) L).mulVec x ∈ latK L n k ↔ x ∈ latK L n k := by
  have hc : ∀ i, (a : Matrix (Fin n) (Fin n) L).mulVec x i = (a : Matrix (Fin n) (Fin n) L) i i * x i := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    rw [Finset.sum_eq_single i]
    · intro j _ hj
      rw [ha i j (Ne.symm hj), zero_mul]
    · simp
  have hvv : ∀ i, Valued.v ((a : Matrix (Fin n) (Fin n) L).mulVec x i) = Valued.v (x i) := by
    intro i
    rw [hc, map_mul, hv, one_mul]
  simp only [latK, Set.mem_setOf_eq, hvv]

theorem mem_iwGL_of_diag {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {n : ℕ} (a : GL (Fin n) L)
    (ha : IsDiagM a) (hv : ∀ i, Valued.v ((a : Matrix (Fin n) (Fin n) L) i i) = 1) : a ∈ IwGL L n := by
  unfold IwGL
  rw [Subgroup.mem_iInf]
  intro k
  rw [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_latK_iff a ha hv k y).2 hy
  · intro hx
    refine ⟨((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec x, ?_, ?_⟩
    · rw [← mem_latK_iff a ha hv k, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
      simpa using hx
    · show (a : Matrix (Fin n) (Fin n) L).mulVec (((a⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).mulVec x) = x
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel]
      simp

theorem mem_iwU_of_diag {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}
    (k : GU σ n) (hk : k ∈ KU σ n) (hd : IsDiagM (k : GL (Fin n) L)) : k ∈ IwU σ n := by
  refine Subgroup.mem_subgroupOf.2 (mem_iwGL_of_diag _ hd fun i => ?_)
  obtain ⟨-, r, hr⟩ := Subgroup.mem_subgroupOf.1 hk
  have hint : ∀ (s : GL (Fin n) (intL L)) (i j : Fin n),
      Valued.v (((Formalism.UG.bc (n := Fin n) (intL L).subtype s : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j) ≤ 1 := by
    intro s i j
    exact ((s : Matrix (Fin n) (Fin n) (intL L)) i j).2
  have h1 := hint r i i
  have h2 := hint r⁻¹ i i
  rw [map_inv, hr] at h2
  rw [hr] at h1
  have hmul : ((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i *
      ((((k : GL (Fin n) L))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = 1 := by
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) L => M i i) (Units.mul_inv (k : GL (Fin n) L))
    simp only [Matrix.mul_apply, Matrix.one_apply_eq] at h
    rw [Finset.sum_eq_single i] at h
    · simpa using h
    · intro j _ hj
      rw [hd i j (Ne.symm hj), zero_mul]
    · simp
  have hm := congrArg Valued.v hmul
  rw [map_mul, map_one] at hm
  refine le_antisymm h1 ?_
  by_contra hlt
  push_neg at hlt
  have : Valued.v (((k : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) *
      Valued.v (((((k : GL (Fin n) L))⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i) < 1 :=
    mul_lt_one_of_lt_of_le hlt h2
  exact absurd hm (ne_of_lt this)

theorem eigU_of (hIw : IwahoriU) (hDom : DomU) (hKU : KUFacts)
    (hA4 : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], A4 G) :
    ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q n : ℕ)
    (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GU σ n) V),
    IsUnramInv ϖ σ q → IsAdmissible ρ → ∀ y : V, y ∉ jacU ρ →
    (∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ρ k y - y ∈ jacU ρ) →
    ∃ (y' : V) (ξ : GU σ n → ℂ), y' ∉ jacU ρ ∧ (∀ t : GU σ n, IsDiagM (t : GL (Fin n) L) → ρ t y' - ξ t • y' ∈ jacU ρ) ∧
      ∀ k ∈ KU σ n, IsDiagM (k : GL (Fin n) L) → ξ k = 1 := by
  intro L _ _ _ ϖ σ q n V _ _ ρ hu hadm y hy hfix
  obtain ⟨D, hJ, hN, hNm, hT⟩ := hIw L ϖ σ q hu n
  obtain ⟨-, -, hIK, t₀, ht₀d, ht₀s⟩ := hKU L ϖ σ q n hu
  have hstr : D.IsStrDom ⟨t₀, (hT _).2 ht₀d⟩ :=
    (hDom L ϖ σ q hu n D hJ hN hNm hT ⟨t₀, (hT _).2 ht₀d⟩).2 ht₀s
  obtain ⟨-, honto⟩ := hA4 (GU σ n) D V ρ hadm ⟨_, hstr⟩
  have hker : twKer ρ D.N 1 = jacU ρ := twKer_eq_jacSub D _ hN ρ
  have hpi : ∀ (t : D.T) (v : V), D.piN ρ t (D.proj ρ v) = D.proj ρ (ρ (t : GU σ n) v) := fun _ _ => rfl
  have hproj0 : ∀ v : V, D.proj ρ v = 0 ↔ v ∈ jacU ρ := by
    intro v
    rw [← hker]
    exact Submodule.Quotient.mk_eq_zero _
  have hprojeq : ∀ v v' : V, D.proj ρ v = D.proj ρ v' ↔ v - v' ∈ jacU ρ := by
    intro v v'
    rw [← hker]
    exact Submodule.Quotient.eq _
  have hfd : FiniteDimensional ℂ (fixed ρ D.J) := hadm.2 D.J D.isOpen_J D.isCompact_J
  let S : Submodule ℂ (Jacquet ρ D.N) := fixed (D.piN ρ) D.JT
  let p : fixed ρ D.J →ₗ[ℂ] Jacquet ρ D.N := (twKer ρ D.N 1).mkQ ∘ₗ (fixed ρ D.J).subtype
  have hSle : S ≤ LinearMap.range p := by
    intro w hw
    obtain ⟨v, hv⟩ := honto w hw
    exact ⟨v, hv⟩
  have hSfd : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSle
  have hmemS : ∀ w : Jacquet ρ D.N, w ∈ S ↔ ∀ s : D.JT, D.piN ρ (s : D.T) w = w := by
    intro w
    refine ⟨fun h s => by simpa using h s, fun h s => by simpa using h s⟩
  have hw₀ : D.proj ρ y ∈ S := by
    refine (hmemS _).2 fun s => ?_
    rw [hpi, hprojeq]
    have hsJ : ((s : D.T) : GU σ n) ∈ D.J := s.2
    exact hfix _ (hIK (hJ ▸ hsJ)) ((hT _).1 (s : D.T).2)
  have hw₀0 : D.proj ρ y ≠ 0 := fun h => hy ((hproj0 y).1 h)
  have hcomm : ∀ a b : D.T, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    exact diag_commute ((hT _).1 a.2) ((hT _).1 b.2)
  have hst : ∀ t : D.T, ∀ w ∈ S, D.piN ρ t w ∈ S := by
    intro t w hw
    refine (hmemS _).2 fun s => ?_
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, (hmemS w).1 hw s]
  have hpos : 0 < Module.finrank ℂ S := by
    have : Nontrivial S := ⟨⟨⟨_, hw₀⟩, 0, fun h => hw₀0 (congrArg Subtype.val h)⟩⟩
    exact Module.finrank_pos
  obtain ⟨w, hw0, c, hc⟩ := exists_common_eigenvector _ S (fun t : D.T => (D.piN ρ t).restrict (hst t))
    (fun a b => by
      ext x
      have h : D.piN ρ a (D.piN ρ b x) = D.piN ρ b (D.piN ρ a x) := by
        rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
      simpa [Module.End.mul_apply, LinearMap.restrict_apply] using h) rfl hpos
  have hc' : ∀ t : D.T, D.piN ρ t (w : Jacquet ρ D.N) = c t • (w : Jacquet ρ D.N) := fun t => by
    simpa [LinearMap.restrict_apply] using congrArg Subtype.val (hc t)
  have hwne : (w : Jacquet ρ D.N) ≠ 0 := fun h => hw0 (Subtype.ext h)
  obtain ⟨y', hy'⟩ : ∃ y' : V, D.proj ρ y' = (w : Jacquet ρ D.N) := Submodule.Quotient.mk_surjective _ _
  classical
  refine ⟨y', fun g => if h : g ∈ D.T then c ⟨g, h⟩ else 1, fun h => hwne (hy' ▸ (hproj0 y').2 h), ?_, ?_⟩
  · intro t ht
    have htT : t ∈ D.T := (hT t).2 ht
    beta_reduce
    rw [dif_pos htT, ← hproj0]
    have h1 := hc' ⟨t, htT⟩
    rw [← hy', hpi] at h1
    show D.proj ρ (ρ t y' - c ⟨t, htT⟩ • y') = 0
    have hsub : D.proj ρ (ρ t y' - c ⟨t, htT⟩ • y') = D.proj ρ (ρ t y') - c ⟨t, htT⟩ • D.proj ρ y' := rfl
    rw [hsub, h1, sub_self]
  · intro k hk hkd
    have hkT : k ∈ D.T := (hT k).2 hkd
    beta_reduce
    rw [dif_pos hkT]
    have hkJ : k ∈ D.J := hJ ▸ mem_iwU_of_diag k hk hkd
    have h1 := hc' ⟨k, hkT⟩
    have h2 := (hmemS _).1 w.2 ⟨⟨k, hkT⟩, hkJ⟩
    have h3 : c ⟨k, hkT⟩ • (w : Jacquet ρ D.N) = (1 : ℂ) • (w : Jacquet ρ D.N) := by
      rw [← h1, one_smul]
      exact h2
    exact smul_left_injective ℂ hwne h3

end GlobalTheory.CompanionTheory.EigTorus
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevIntegrationByPartsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_integration_by_parts : PositivityTheory.RgBcC.Fc.IbpSob := by
  first | exact @GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob | exact GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob | (intros; apply GlobalTheory.CompanionTheory.FcCalc.Ibp.ibpSob <;> assumption)
end

