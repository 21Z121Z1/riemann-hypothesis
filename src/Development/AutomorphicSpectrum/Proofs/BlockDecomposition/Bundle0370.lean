import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.FriedrichsKernels.Friedrichs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0363
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0225
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryMemGLs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0208
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0240
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0241
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0236
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0237
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0239
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0245
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0247
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0331
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0248
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0226
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.SFunOf

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevOperatorFacts
section
noncomputable section

open MeasureTheory Matrix
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.SobOpsPf

open GlobalTheory.CompanionTheory.RCalc (Rd_congr Rd_add Rd_smul Rd_contDiffOn differentiableAt_of_smooth gel_contDiffOn Rd_gel gel_right
  gel_post fderiv_comp_clm fderiv_post mulR mapsTo_mulR)
open GlobalTheory.CompanionTheory.SobSecK (Rw_congr Rw_smooth Rw_append Rd_sum_cf)

variable {n : ℕ}

section Words

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem Rw_add (w : List (Bool × Fin n × Fin n)) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) : Set.EqOn (Rw w (f + f')) (Rw w f + Rw w f') (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_add (bs p) (Rw_smooth w hf) (Rw_smooth w hf') hx)

theorem Rw_smul (w : List (Bool × Fin n × Fin n)) (c : ℂ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rw w (c • f)) (c • Rw w f) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_smul c (bs p) (Rw_smooth w hf) hx)

theorem Om_smooth {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Om f) (GLs n) :=
  ((gel_contDiffOn true 2 hf).add (gel_contDiffOn false 2 hf)).const_smul (2 : ℂ)

theorem Rd_Om (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Om f) g = Om (Rd X f) g := by
  have h1 := gel_contDiffOn true 2 hf
  have h2 := gel_contDiffOn false 2 hf
  have h3 : ContDiffOn ℝ ∞ (gel true 2 f + gel false 2 f) (GLs n) := h1.add h2
  have e1 := Rd_smul (2 : ℂ) X h3 hg
  have e2 := Rd_add X h1 h2 hg
  simp only [Pi.smul_apply, Pi.add_apply] at e1 e2
  simp only [Om, Pi.smul_apply, Pi.add_apply]
  rw [e1, e2, Rd_gel X true 2 hf hg, Rd_gel X false 2 hf hg]

theorem Rw_Om (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Rw w (Om f)) (Om (Rw w f)) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_Om (bs p) (Rw_smooth w hf) hx)

theorem Rd_translate (X : Mat n) {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (fun y => f (y * x)) g = Rd (x⁻¹ * X * x) f (g * x) := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have hd := differentiableAt_of_smooth hf (mapsTo_mulR hx hg)
  have e : g * x * (x⁻¹ * X * x) = g * X * x := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have := fderiv_comp_clm (mulR x) hd (g * X)
  simp only [Rd, e]
  exact this

theorem Rd_post (X : Mat n) (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Rd X (fun y => A (f y)) g = A (Rd X f g) :=
  fderiv_post A (differentiableAt_of_smooth hf hg) _

theorem post_smooth (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => A (f y)) (GLs n) :=
  (A.restrictScalars ℝ).contDiff.comp_contDiffOn hf

theorem Rw_post (w : List (Bool × Fin n × Fin n)) (A : V →L[ℂ] V) {f : Mat n → V}
    (hf : ContDiffOn ℝ ∞ f (GLs n)) : Set.EqOn (Rw w (fun y => A (f y))) (fun y => A (Rw w f y)) (GLs n) := by
  induction w with
  | nil => intro x _; rfl
  | cons p w ih =>
    intro x hx
    exact (Rd_congr (bs p) ih hx).trans (Rd_post (bs p) A (Rw_smooth w hf) hx)

theorem Om_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Om (fun y => A (f y)) g = A (Om f g) := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_post A _ _ hf hg, map_smul, map_add]

theorem Om_translate {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : Om (fun y => f (y * x)) g = Om f (g * x) := by
  simp only [Om, Pi.smul_apply, Pi.add_apply, gel_right _ _ hx hf hg]

theorem translate_smooth {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (fun y => f (y * x)) (GLs n) :=
  hf.comp (mulR x).contDiff.contDiffOn (mapsTo_mulR hx)

end Words

section Sob

variable [MeasurableSpace (G n)] {μ : Measure (G n)} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem val_mem (y : G n) : y.val ∈ GLs n := GlobalTheory.CompanionTheory.RCalc.ByParts.val_mem_GLs y

theorem sob_congr {f h : Mat n → V} (hf : Sob μ f) (e : Set.EqOn f h (GLs n)) : Sob μ h :=
  ⟨hf.1.congr fun _ hx => (e hx).symm, fun w =>
    MemLp.ae_eq (ae_of_all _ fun y => Rw_congr w e (val_mem y)) (hf.2 w)⟩

theorem sob_add {f h : Mat n → V} (hf : Sob μ f) (hh : Sob μ h) : Sob μ (f + h) :=
  ⟨hf.1.add hh.1, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_add w hf.1 hh.1 (val_mem y)).symm)
    ((hf.2 w).add (hh.2 w))⟩

theorem sob_smul (c : ℂ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (c • f) :=
  ⟨hf.1.const_smul c, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_smul w c hf.1 (val_mem y)).symm)
    ((hf.2 w).const_smul c)⟩

theorem sob_zero {f : Mat n → V} (hf : Sob μ f) : Sob μ (0 : Mat n → V) := by
  simpa using sob_smul (0 : ℂ) hf

theorem sob_sum {ι : Type} (s : Finset ι) {f₀ : Mat n → V} (h₀ : Sob μ f₀) {F : ι → Mat n → V}
    (hF : ∀ i, Sob μ (F i)) : Sob μ (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using sob_zero h₀
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact sob_add (hF a) ih

theorem sob_Rw (w : List (Bool × Fin n × Fin n)) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rw w f) :=
  ⟨Rw_smooth w hf.1, fun w' => by rw [Rw_append]; exact hf.2 _⟩

theorem sob_bs (p : Bool × Fin n × Fin n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rd (bs p) f) :=
  sob_Rw [p] hf

theorem sob_Rd (X : Mat n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Rd X f) := by
  refine sob_congr (f := ∑ p : Bool × Fin n × Fin n, ((GlobalTheory.CompanionTheory.SobSecK.cf X p : ℝ) : ℂ) • Rd (bs p) f)
    (sob_sum _ hf fun p => sob_smul _ (sob_bs p hf)) fun g _ => ?_
  rw [Rd_sum_cf X f g]
  simp only [Finset.sum_apply, Pi.smul_apply]

theorem sob_Eu (s : Bool) (a b : Fin n) {f : Mat n → V} (hf : Sob μ f) : Sob μ (Eu s a b f) :=
  sob_smul _ (sob_add (sob_Rd _ hf) (sob_smul _ (sob_Rd _ hf)))

theorem sob_Epow (s : Bool) (m : ℕ) {f : Mat n → V} (hf : Sob μ f) : ∀ a b, Sob μ (Epow s m a b f) := by
  induction m with
  | zero =>
    intro a b
    by_cases hab : a = b
    · simpa [Epow, hab] using hf
    · simpa [Epow, hab] using sob_zero hf
  | succ m ih =>
    intro a b
    exact sob_sum _ hf fun c => sob_Eu s a c (ih c b)

theorem sob_gel (s : Bool) (m : ℕ) {f : Mat n → V} (hf : Sob μ f) : Sob μ (gel s m f) :=
  sob_sum _ hf fun a => sob_Epow s m hf a a

theorem sob_Om {f : Mat n → V} (hf : Sob μ f) : Sob μ (Om f) :=
  sob_smul _ (sob_add (sob_gel _ _ hf) (sob_gel _ _ hf))

theorem sob_post (A : V →L[ℂ] V) {f : Mat n → V} (hf : Sob μ f) : Sob μ (fun y => A (f y)) :=
  ⟨post_smooth A hf.1, fun w => MemLp.ae_eq (ae_of_all _ fun y => (Rw_post w A hf.1 (val_mem y)).symm)
    (A.comp_memLp' (hf.2 w))⟩

variable [BorelSpace (G n)] [μ.IsHaarMeasure]

theorem memLp_translate (hU : Unimod) (h : G n) {F : Mat n → V} (hF : MemLp (fun y : G n => F y.val) 2 μ) :
    MemLp (fun y : G n => F (y.val * h.val)) 2 μ := by
  haveI := (hU n μ).1
  exact hF.comp_measurePreserving (measurePreserving_mul_right μ h)

theorem translate_memLp (hU : Unimod) (h : G n) (w : List (Bool × Fin n × Fin n)) :
    ∀ F : Mat n → V, Sob μ F → MemLp (fun y : G n => Rw w (fun z => F (z * h.val)) y.val) 2 μ := by
  induction w using List.reverseRecOn with
  | nil => exact fun F hF => memLp_translate hU h (hF.2 [])
  | append_singleton w p ih =>
    intro F hF
    rw [← Rw_append [p] w]
    have e : Set.EqOn (Rw [p] fun z => F (z * h.val)) (fun z => Rd (h.val⁻¹ * bs p * h.val) F (z * h.val)) (GLs n) :=
      fun g hg => Rd_translate (bs p) (val_mem h) hF.1 hg
    exact MemLp.ae_eq (ae_of_all _ fun y => (Rw_congr w e (val_mem y)).symm) (ih _ (sob_Rd _ hF))

theorem sob_translate (hU : Unimod) (h : G n) {F : Mat n → V} (hF : Sob μ F) : Sob μ (fun y => F (y * h.val)) :=
  ⟨translate_smooth (val_mem h) hF.1, fun w => translate_memLp hU h w F hF⟩

end Sob

theorem sobOps : SobOps := by
  intro n _ _ μ _ V _ _ _ hU _ f hf
  refine ⟨sob_Om hf, fun w => sob_Rw w hf, fun w g hg => Rw_Om w hf.1 hg, fun a f' hf' => ⟨sob_add (sob_smul a hf) hf', ?_⟩,
    fun h A => ⟨sob_post A (sob_translate hU h hf), fun g hg => ?_⟩⟩
  · intro g hg
    have hs : ContDiffOn ℝ ∞ (a • f) (GLs n) := hf.1.const_smul a
    have e1 := GlobalTheory.CompanionTheory.WaveK.Lin.Om_add hs hf'.1 hg
    have e2 := GlobalTheory.CompanionTheory.WaveK.Lin.Om_smul a hf.1 hg
    simp only [Pi.add_apply, Pi.smul_apply] at e1 e2
    rw [e1, e2]
  · rw [Om_post A (translate_smooth (val_mem h) hf.1) hg, Om_translate (val_mem h) hf.1 hg]

end GlobalTheory.CompanionTheory.SobOpsPf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SobolevSpacePreserved
section
open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc GlobalTheory.CompanionTheory.PresSobA
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
noncomputable section

namespace GlobalTheory.CompanionTheory.PresSobA

variable {n : ℕ} [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

theorem rR_one (hU : Unimod) (y : Lp V 2 μ) : rR μ V 1 y = y := by
  apply Lp.ext
  filter_upwards [rR_coe μ hU 1 y] with z hz
  simpa using hz

theorem lT_one (y : Lp V 2 μ) : lT μ V 1 y = y := by
  apply Lp.ext
  filter_upwards [lT_coe μ 1 y] with z hz
  simpa using hz

theorem orbit_deriv (hU : Unimod) {f : Mat n → V} (X : Mat n) (hf : ContDiffOn ℝ ∞ f (GLs n))
    (h0 : MemLp (fun y : G n => f y.val) 2 μ) (h1 : MemLp (fun y : G n => Rd X f y.val) 2 μ) :
    HasDerivAt (fun t : ℝ => rR μ V (expC X t) (cls μ f)) (cls μ (Rd X f)) 0 := by
  have hc : Continuous (fun s : ℝ => rR μ V (expC X s) (cls μ (Rd X f))) :=
    (GlobalTheory.T.regular_representation_continuous n μ V hU _).1.comp (GlobalTheory.T.matrix_exp_curve_derivative n X).1
  have hd := intervalIntegral.integral_hasDerivAt_right (a := (0 : ℝ)) (b := 0)
    (hc.intervalIntegrable _ _) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt
  simp only [expC_zero, rR_one hU] at hd
  have he : (fun t : ℝ => rR μ V (expC X t) (cls μ f)) =
      fun t : ℝ => (∫ s in (0 : ℝ)..t, rR μ V (expC X s) (cls μ (Rd X f))) + cls μ f := by
    funext t
    rw [← GlobalTheory.T.right_translate_derivative_integral n μ V hU f X hf h0 h1 t]
    abel
  rw [he]
  exact hd.add_const _

theorem mol_family (hU : Unimod) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ)
    (hx : ∀ w p, HasDerivAt (fun t : ℝ => rR μ V (expC (bs p) t) (x w)) (x (p :: w)) 0)
    {φ : Mat n → ℝ} (hφ : IsTest φ) :
    (∀ w, ContDiffOn ℝ ∞ (Mol μ φ (⇑(x w))) (GLs n)) ∧
      ∀ w p, ∀ z ∈ GLs n, Rd (bs p) (Mol μ φ (⇑(x w))) z = Mol μ φ (⇑(x (p :: w))) z := by
  have hd : ∀ w p, ∀ z ∈ GLs n, Rd (bs p) (Mol μ φ (⇑(x w))) z = Mol μ φ (⇑(x (p :: w))) z := by
    intro w p z hz
    obtain ⟨Lz, hL⟩ := GlobalTheory.T.mollification_evaluation_continuous n μ V hU φ hφ z hz
    have h1 : HasDerivAt (fun t : ℝ => Lz (rR μ V (expC (bs p) t) (x w))) (Lz (x (p :: w))) 0 :=
      Lz.hasFDerivAt.comp_hasDerivAt 0 (hx w p)
    have hcur : HasDerivAt (fun t : ℝ => z * (expC (bs p) t).val) (z * bs p) 0 := by
      have h0 := (GlobalTheory.T.matrix_exp_curve_derivative n (bs p)).2 0
      rw [expC_zero] at h0
      simp only [Units.val_one, one_mul] at h0
      exact (LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ z) : Mat n →L[ℝ] Mat n).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
    have hdiff := (GlobalTheory.T.mollification_differentiable n μ V hU φ hφ (x w) z hz).hasFDerivAt
    have h2 : HasDerivAt (fun t : ℝ => Mol μ φ (⇑(x w)) (z * (expC (bs p) t).val))
        (fderiv ℝ (Mol μ φ (⇑(x w))) z (z * bs p)) 0 := by
      have hz0 : z * (expC (bs p) 0).val = z := by simp [expC_zero]
      have hdiff' : HasFDerivAt (Mol μ φ (⇑(x w))) (fderiv ℝ (Mol μ φ (⇑(x w))) z)
          (z * (expC (bs p) 0).val) := by rw [hz0]; exact hdiff
      exact hdiff'.comp_hasDerivAt 0 hcur
    have h3 : (fun t : ℝ => Lz (rR μ V (expC (bs p) t) (x w))) =
        fun t : ℝ => Mol μ φ (⇑(x w)) (z * (expC (bs p) t).val) := by
      funext t
      rw [hL, GlobalTheory.T.mollification_right_translate n μ V hU]
    rw [h3] at h1
    rw [← hL]
    exact h2.unique h1
  refine ⟨fun w => ?_, hd⟩
  exact GlobalTheory.T.closed_derivative_system_smooth n V (List (Bool × Fin n × Fin n)) (fun w => Mol μ φ (⇑(x w))) (fun p w => p :: w)
    (fun w z hz => GlobalTheory.T.mollification_differentiable n μ V hU φ hφ (x w) z hz) (fun w p z hz => hd w p z hz) w

theorem limit_sob (hS : SobG) (g : ℕ → Mat n → V) (x : List (Bool × Fin n × Fin n) → Lp V 2 μ)
    (hg : ∀ k, ContDiffOn ℝ ∞ (g k) (GLs n)) (hm : ∀ k w, MemLp (fun y : G n => Rw w (g k) y.val) 2 μ)
    (hx : ∀ w, Tendsto (fun k => cls μ (Rw w (g k))) atTop (𝓝 (x w))) :
    ∃ f', Sob μ f' ∧ ∀ w, cls μ (Rw w f') = x w := by
  obtain ⟨Gf, hu, hc, hw⟩ := GlobalTheory.T.uniform_limit_right_derivatives n V g hg (GlobalTheory.T.sobolev_sequence_uniform_cauchy hS n μ V g x hg hm hx)
  have key : ∀ w, MemLp (fun y : G n => Rw w (Gf []) y.val) 2 μ ∧ cls μ (Rw w (Gf [])) = x w := by
    intro w
    refine GlobalTheory.T.l2_limit_eq_pointwise_limit_holds n μ V (fun k => Rw w (g k)) (Rw w (Gf [])) (x w) (fun k => hm k w) (hx w) ?_
    intro z hz
    rw [hw w z hz]
    exact (hu w).tendsto_at hz
  exact ⟨Gf [], ⟨hc, fun w => (key w).1⟩, fun w => (key w).2⟩

end GlobalTheory.CompanionTheory.PresSobA

open GlobalTheory.CompanionTheory.PresSobA in

theorem GlobalTheory.CompanionTheory.PresSobA.presSob : PresSob := by
  intro n _ _ μ _ V _ _ _ S hLg hU hRC hS hcomm f hf
  have hsob : ∀ w, ContDiffOn ℝ ∞ (Rw w f) (GLs n) := fun w => GlobalTheory.CompanionTheory.SobGL.Smooth.Rw_contDiffOn' hf.1 w
  set x : List (Bool × Fin n × Fin n) → Lp V 2 μ := fun w => S (cls μ (Rw w f)) with hxdef
  have hx : ∀ w p, HasDerivAt (fun t : ℝ => rR μ V (expC (bs p) t) (x w)) (x (p :: w)) 0 := by
    intro w p
    have h1 := orbit_deriv (μ := μ) hU (bs p) (hsob w) (hf.2 w) (hf.2 (p :: w))
    have h2 : HasDerivAt (fun t : ℝ => (S.restrictScalars ℝ) (rR μ V (expC (bs p) t) (cls μ (Rw w f))))
        ((S.restrictScalars ℝ) (cls μ (Rd (bs p) (Rw w f)))) 0 :=
      (S.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h1
    have h3 : (fun t : ℝ => rR μ V (expC (bs p) t) (x w)) =
        fun t : ℝ => (S.restrictScalars ℝ) (rR μ V (expC (bs p) t) (cls μ (Rw w f))) := by
      funext t
      exact (DFunLike.congr_fun (hcomm (expC (bs p) t)) _).symm
    rw [h3]
    exact h2
  obtain ⟨φ, hφ, hφ0, hφ1, hφs⟩ := GlobalTheory.T.approximate_identity_exists n μ
  have hfam := fun k => mol_family (μ := μ) hU x hx (hφ k)
  have hRw : ∀ k w, ∀ z ∈ GLs n, Rw w (Mol μ (φ k) (⇑(x []))) z = Mol μ (φ k) (⇑(x w)) z := by
    intro k w
    induction w with
    | nil => exact fun z _ => rfl
    | cons p w ih =>
      intro z hz
      exact (Rd_congr ih (bs p) z hz).trans ((hfam k).2 w p z hz)
  have hae : ∀ k w, (fun y : G n => Rw w (Mol μ (φ k) (⇑(x []))) y.val) =ᵐ[μ] lConv μ V (φ k) (x w) := by
    intro k w
    have h0 : (fun y : G n => Rw w (Mol μ (φ k) (⇑(x []))) y.val) = fun y : G n => Mol μ (φ k) (⇑(x w)) y.val :=
      funext fun y => hRw k w y.val (by
        have := (Matrix.isUnit_iff_isUnit_det _).1 y.isUnit
        exact this.ne_zero)
    rw [h0]
    exact GlobalTheory.T.mollification_ae_eq_convolution n μ V hU (φ k) (hφ k) (x w)
  have hlim : ∀ w, Tendsto (fun k => cls μ (Rw w (Mol μ (φ k) (⇑(x []))))) atTop (𝓝 (x w)) := by
    intro w
    have : (fun k => cls μ (Rw w (Mol μ (φ k) (⇑(x []))))) = fun k => lConv μ V (φ k) (x w) :=
      funext fun k => (cls_of_ae μ (hae k w)).2
    rw [this, Metric.tendsto_nhds]
    intro ε hε
    have hc : Continuous (fun y : G n => lT μ V y (x w)) := (GlobalTheory.T.regular_representation_continuous n μ V hU _).2
    have h1 : {y : G n | dist (lT μ V y (x w)) (x w) < ε / 2} ∈ 𝓝 (1 : G n) := by
      have h2 := (hc.tendsto (1 : G n))
      rw [lT_one] at h2
      exact h2 (Metric.ball_mem_nhds _ (half_pos hε))
    filter_upwards [hφs _ h1] with k hk
    have h3 := GlobalTheory.T.left_convolution_approximation n μ V hU (φ k) (hφ k) (hφ0 k) (hφ1 k) (x w) (ε / 2)
      (fun y hy => by
        have h4 := hk y hy
        rw [dist_eq_norm] at h4
        exact h4.le)
    rw [dist_eq_norm]
    linarith
  obtain ⟨f', hf', hcl⟩ := limit_sob (μ := μ) hS (fun k => Mol μ (φ k) (⇑(x []))) x (fun k => (hfam k).1 [])
    (fun k w => (cls_of_ae μ (hae k w)).1) hlim
  exact ⟨f', hf', hcl [], hcl⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumMulSqLe
section
open MeasureTheory
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1 PositivityTheory.Rg.BcB.E1
open scoped ENNReal

noncomputable section

namespace GlobalTheory.CompanionTheory.DualVectorFamily

theorem sum_mul_sq_le {κ : Type} (s : Finset κ) (p q : κ → ℝ≥0∞) (t : ℝ≥0∞) (h : ∀ l ∈ s, q l ^ 2 ≤ t) :
    (∑ l ∈ s, p l * q l) ^ 2 ≤ (∑ l ∈ s, p l) ^ 2 * t := by
  have hs : (t ^ (1 / 2 : ℝ)) ^ 2 = t := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hq : ∀ l ∈ s, q l ≤ t ^ (1 / 2 : ℝ) := by
    intro l hl
    have := h l hl
    rw [← hs] at this
    exact (ENNReal.pow_le_pow_left_iff (by norm_num)).1 this
  calc (∑ l ∈ s, p l * q l) ^ 2 ≤ ((∑ l ∈ s, p l) * t ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun l hl => by gcongr; exact hq l hl
    _ = (∑ l ∈ s, p l) ^ 2 * t := by rw [mul_pow, hs]

theorem abs_vecs (hKB : KerBasic) (hKL : KerLin) (hCB : CntBasic) (hVE : VecEx) (hVN : VecNorm)
    (hVI : VecInner) (hPt : PtEq) (X : Ctx) (th : X.G → X.G) (hth : Continuous th)
    (hcnt : ∀ (Ω : Set X.G) x, cnt X.Γ Ω (th x) = cnt X.Γ (th '' Ω) x)
    {ι : Type} [Fintype ι] (Φ₁ Φ₂ : Matrix ι ι (X.G → ℂ)) (T₁ T₂ : X.Hs ι →L[ℂ] X.Hs ι)
    (M : Matrix ι ι ℂ) (t₁ : ∀ i j, Tst (Φ₁ i j)) (t₂ : ∀ i j, Tst (Φ₂ i j))
    (o₁ : X.IsOp Φ₁ T₁) (o₂ : X.IsOp Φ₂ T₂) :
    ∃ k₁ k₂ : X.G → ι → X.Hs ι,
      (∀ i, Continuous (fun x => k₁ x i) ∧ Continuous fun x => k₂ x i) ∧
      (∀ x i (u : X.Hs ι), inner ℂ (k₁ x i) u = ∑ j, ∫ y, ker X.Γ (Φ₁ i j) x y * (u j : X.G → ℂ) y ∂X.ν) ∧
      (∀ x i (u : X.Hs ι), inner ℂ u (k₂ x i) =
        ∑ j, ∑ l, ∫ y, starRingEnd ℂ ((u j : X.G → ℂ) y) * ker X.Γ (Φ₂ j l) y (th x) * M l i ∂X.ν) ∧
      (∃ (C : ℝ≥0∞) (Ω : Set X.G), C ≠ ⊤ ∧ IsCompact Ω ∧ ∀ x i,
        ‖k₁ x i‖ₑ ^ 2 ≤ C * cnt X.Γ Ω x ∧ ‖k₂ x i‖ₑ ^ 2 ≤ C * cnt X.Γ Ω x) ∧
      (∀ (U : X.Hs ι →L[ℂ] X.Hs ι) (Φ : Matrix ι ι (X.G → ℂ)), (∀ i j, Tst (Φ i j)) →
        X.IsOp Φ (T₁ * U * T₂) → ∀ x,
          ker X.Γ (fun y => ∑ i, ∑ j, Φ i j y * M j i) x (th x) =
            ∑ i, inner ℂ (k₁ x i) (U (k₂ x i))) := by
  have tA : ∀ i j, Tst ((fun i j => adj (Φ₁ j i) : Matrix ι ι (X.G → ℂ)) i j) :=
    fun i j => (hKB X _ (t₁ j i)).2.2.2.1
  obtain ⟨k₁, c₁, v₁⟩ := hVE X ι (fun i j => adj (Φ₁ j i)) tA
  obtain ⟨k, c, v⟩ := hVE X ι Φ₂ t₂
  obtain ⟨C₁, Ω₁, C₁t, Ω₁c, n₁⟩ := hVN X ι (fun i j => adj (Φ₁ j i)) tA
  obtain ⟨C₂, Ω₂, C₂t, Ω₂c, n₂⟩ := hVN X ι Φ₂ t₂
  refine ⟨k₁, fun x i => ∑ l, M l i • k (th x) l, fun i => ⟨c₁ i, ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact continuous_finset_sum _ fun l _ => ((c l).comp hth).const_smul (M l i)
  · intro x i u
    exact (hVI X ι Φ₁ x i (k₁ x i) u t₁).2 (v₁ x i)
  · intro x i u
    rw [inner_sum]
    simp only [inner_smul_right, (hVI X ι Φ₂ (th x) _ (k (th x) _) u t₂).1 (v _ _), Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [integral_mul_const, mul_comm]
  · set P : ℝ≥0∞ := ∑ i, (∑ l, ‖M l i‖ₑ) ^ 2 with hP
    have Pt : P ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ =>
      ENNReal.pow_ne_top (ENNReal.sum_ne_top.2 fun l _ => enorm_ne_top)
    refine ⟨C₁ + P * C₂, Ω₁ ∪ th '' Ω₂, ENNReal.add_ne_top.2 ⟨C₁t, ENNReal.mul_ne_top Pt C₂t⟩,
      Ω₁c.union (Ω₂c.image hth), fun x i => ⟨?_, ?_⟩⟩
    · calc ‖k₁ x i‖ₑ ^ 2 ≤ C₁ * cnt X.Γ Ω₁ x := n₁ x i _ (v₁ x i)
        _ ≤ (C₁ + P * C₂) * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
          gcongr
          · exact le_self_add
          · exact (hCB X).2.2.1 _ _ Set.subset_union_left x
    · have hb : ∀ l ∈ (Finset.univ : Finset ι), ‖k (th x) l‖ₑ ^ 2 ≤ C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
        intro l _
        calc ‖k (th x) l‖ₑ ^ 2 ≤ C₂ * cnt X.Γ Ω₂ (th x) := n₂ _ l _ (v _ l)
          _ = C₂ * cnt X.Γ (th '' Ω₂) x := by rw [hcnt]
          _ ≤ _ := by
            gcongr
            exact (hCB X).2.2.1 _ _ Set.subset_union_right x
      have hsum : ‖∑ l, M l i • k (th x) l‖ₑ ≤ ∑ l, ‖M l i‖ₑ * ‖k (th x) l‖ₑ := by
        refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [enorm_smul]
      calc ‖∑ l, M l i • k (th x) l‖ₑ ^ 2 ≤ (∑ l, ‖M l i‖ₑ * ‖k (th x) l‖ₑ) ^ 2 := by gcongr
        _ ≤ (∑ l, ‖M l i‖ₑ) ^ 2 * (C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x) := sum_mul_sq_le _ _ _ _ hb
        _ ≤ P * (C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x) := by
          gcongr
          exact Finset.single_le_sum (f := fun i => (∑ l, ‖M l i‖ₑ) ^ 2) (fun _ _ => zero_le) (Finset.mem_univ i)
        _ = P * C₂ * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by rw [mul_assoc]
        _ ≤ (C₁ + P * C₂) * cnt X.Γ (Ω₁ ∪ th '' Ω₂) x := by
          gcongr
          exact le_add_self
  · intro U Φ tΦ oΦ x
    have hfun : (fun y => ∑ i, ∑ j, Φ i j y * M j i) =
        fun y => ∑ p : ι × ι, Φ p.1 p.2 y * M p.2 p.1 := by
      funext y
      rw [Fintype.sum_prod_type]
    rw [hfun, (hKL X (ι × ι) (fun p => Φ p.1 p.2) (fun p => M p.2 p.1) fun p => tΦ _ _).2,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum, inner_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, inner_smul_right,
      hPt X ι Φ₁ Φ₂ Φ T₁ T₂ U t₁ t₂ tΦ o₁ o₂ oΦ x (th x) i l (k₁ x i) (k (th x) l) (v₁ x i) (v _ l),
      mul_comm]

theorem vecsEx_of : RatProper → KerBasic → KerLin → CntBasic → CntPair → VecEx → VecNorm → VecInner → PtEq →
    VecsEx := by
  intro hR hKB hKL hCB hCP hVE hVN hVI hPt E _ _ _ a b D ι _ Φ₁ Φ₂ T₁ T₂ M h₁ h₂ o₁ o₂
  obtain ⟨k₁, k₂, c, r₁, r₂, n, d⟩ := abs_vecs hKB hKL hCB hVE hVN hVI hPt (ctx hR D) th
    (hCP E a b).2.1 (hCP E a b).1 Φ₁ Φ₂ T₁ T₂ M h₁ h₂ o₁ o₂
  refine ⟨k₁, k₂, ⟨c, r₁, r₂, n, ?_⟩⟩
  intro U Φ hΦ hop x
  rw [(hCP E a b).2.2]
  exact d U Φ hΦ hop x

end GlobalTheory.CompanionTheory.DualVectorFamily

end
end

