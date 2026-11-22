import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0223
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalCalculusFirstAssumption
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveRepresentation
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc
open PositivityTheory.RgTw (Mat G)
open GlobalTheory.CompanionTheory.WaveFc.Asm

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.KerFc

variable {n : ℕ}

section Main

variable [MeasurableSpace (G n)] [BorelSpace (G n)] {μ : Measure (G n)} [μ.IsHaarMeasure]

theorem coreRep (E : KMod n) [CompleteSpace E.V] {Ω : Msob μ E.V →ₗ[ℂ] Msob μ E.V} {T : Lp E.V 2 μ →L[ℂ] Lp E.V 2 μ}
    (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hSG : SobG)
    (hAC : AbsCut) (hFc : Fcurve) (hW : WvAlg) (hC : ClsFacts) (hO : SobOps) (hCp : CptSob) (hP : PresSob)
    (hCJ : CurveJoint)
    (F : FCalc (Lp E.V 2 μ) (Msob μ E.V) Ω T) (hrep : ∀ x ∈ Msob μ E.V, ∃ f, Sob μ f ∧ cls μ f = x)
    (hΩ : ∀ (f : Mat n → E.V) (hf : cls μ f ∈ Msob μ E.V), Sob μ f → (Ω ⟨cls μ f, hf⟩ : Lp E.V 2 μ) = cls μ (Om f))
    (hT : ∀ x : Msob μ E.V, T ((x : Lp E.V 2 μ) + (Ω (Ω x) : Lp E.V 2 μ)) = x) (c : ℝ)
    (hc : ∀ f : Mat n → E.V, Sob μ f → IsSec E f → (⟪cls μ (Om f), cls μ f⟫_ℂ).re ≤ c * ‖cls μ f‖ ^ 2)
    {f : Mat n → E.V} (hf : f ∈ CE E) (hcf : Cpt f) :
    ∃ (N : ℕ) (b : Lp E.V 2 μ) (U : ℝ → Mat n → E.V), 1 ≤ N ∧ (T ^ N) b = cls μ f ∧ IsWave E U ∧
      (∀ x ∈ GLs n, U 0 x = f x) ∧ ∀ t, Sob μ (U t) ∧ cls μ (U t) = F.Φ (toC0 (wv c N 0 t)) b := by
  have hbp := fun N => Bn_props μ hL hR hCp E hf hcf N
  have hbS : ∀ N, Sob μ (Bn f N) := fun N => (hCp n μ E.V hL hR _ (hbp N).1.1 (hbp N).2).1
  have hbE : ∀ N, IsSec E (Bn f N) := fun N => (hbp N).1.2
  have hC0 : ∀ N j t, j + 2 ≤ 4 * N → (Continuous (wv c N j t) ∧ Tendsto (wv c N j t) (cocompact ℝ) (𝓝 0)) :=
    fun N j t hj => (hFc c N j hj t).1
  have hstep : ∀ N j t, j + 2 ≤ 4 * N →
      F.Φ (toC0 (wv c (N + 1) j t)) (cls μ (Bn f (N + 1))) = F.Φ (toC0 (wv c N j t)) (cls μ (Bn f N)) := by
    intro N j t hj
    rw [wv_step hW F (hC0 N j t hj) (hC0 (N + 1) j t (by omega)), ContinuousLinearMap.mul_apply]
    exact congrArg _ (T_B hC hO hL hU hR hΩ hT (hbS N))
  have hpres := fun g (N : ℕ) => pres hC hO hL hU hR hSG hP F hrep hΩ g (hbS N)
  have hex : ∀ (j : ℕ) (t : ℝ), ∃ u, Sob μ u ∧ IsSec E u ∧
      cls μ u = F.Φ (toC0 (wv c (j + 2) j t)) (cls μ (Bn f (j + 2))) ∧
      ∀ w, cls μ (Rw w u) = F.Φ (toC0 (wv c (j + 2) j t)) (cls μ (Rw w (Bn f (j + 2)))) := by
    intro j t
    obtain ⟨u, h1, h2, h3⟩ := hpres (toC0 (wv c (j + 2) j t)) (j + 2)
    exact ⟨u, h1, sec_pres E hC hO hL hU hR F hrep hΩ _ (hbS _) (hbE _) h1 h2, h2, h3⟩
  choose U hUS hUE hUc hUw using hex
  have hd : ∀ j w t, HasDerivAt (fun s => cls μ (Rw w (U j s))) (cls μ (Rw w (U (j + 1) t))) t := by
    intro j w t
    have e : (fun s => cls μ (Rw w (U j s))) =
        fun s => F.Φ (toC0 (wv c (j + 2) j s)) (cls μ (Rw w (Bn f (j + 2)))) := funext fun s => hUw j s w
    rw [e]
    have hd := curve_deriv hFc F c (N := j + 2) (j := j) (by omega) t (cls μ (Rw w (Bn f (j + 2))))
    obtain ⟨f'', hf'', hc'', hw''⟩ := hpres (toC0 (wv c (j + 2) (j + 1) t)) (j + 2)
    have e2 : cls μ (Rw w (U (j + 1) t)) = F.Φ (toC0 (wv c (j + 2) (j + 1) t)) (cls μ (Rw w (Bn f (j + 2)))) := by
      rw [← hw'' w]
      refine cls_congr hC hU (Rw_congr w (cls_eq_of_sob hC hU (hUS (j + 1) t) hf'' ?_))
      rw [hUc, hc'']
      exact hstep (j + 2) (j + 1) t (by omega)
    rw [e2]
    exact hd
  obtain ⟨hjoint, hder⟩ := hCJ n μ E.V U hL hR hSG hUS hd
  have hT2 : (T ^ 2) (cls μ (Bn f 2)) = cls μ f := by
    rw [pow_two, ContinuousLinearMap.mul_apply]
    have a1 : T (cls μ (Bn f 2)) = cls μ (Bn f 1) := T_B hC hO hL hU hR hΩ hT (hbS 1)
    have a2 : T (cls μ (Bn f 1)) = cls μ (Bn f 0) := T_B hC hO hL hU hR hΩ hT (hbS 0)
    rw [a1, a2]
    rfl
  refine ⟨2, cls μ (Bn f 2), U 0, by norm_num, hT2, ⟨hjoint, fun t => ⟨(hUS 0 t).1, hUE 0 t⟩, ?_, ?_⟩, ?_,
    fun t => ⟨hUS 0 t, hUc 0 t⟩⟩
  · intro t g hg
    have d1 : deriv (fun s => U 0 s g) = fun s => U 1 s g := funext fun s => (hder 0 s g hg).deriv
    have d2 : iteratedDeriv 2 (fun s => U 0 s g) t = U 2 t g := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, d1]
      exact (hder 1 t g hg).deriv
    rw [d2]
    have hOmS := (hO n μ E.V hL hU hR _ (hUS 0 t)).1
    have h0 : cls μ (U 0 t) = F.Φ (toC0 (wv c 4 0 t)) (cls μ (Bn f 4)) := by
      rw [hUc, hstep 3 0 t (by omega), hstep 2 0 t (by omega)]
    have hom := F.omega (toC0 (wv c 4 0 t)) (toC0 (wv c 4 2 t))
      (fun y => by
        rw [coe_toC0 (hC0 4 0 t (by omega)), coe_toC0 (hC0 4 2 t (by omega))]
        exact (hW c 4 t y).1)
      (cls μ (Bn f 4)) ⟨cls μ (U 0 t), cls_mem μ (hUS 0 t)⟩ h0
    rw [hΩ _ _ (hUS 0 t)] at hom
    exact cls_eq_of_sob hC hU (hUS 2 t) hOmS ((hUc 2 t).trans hom.symm) g hg
  · intro g hg
    rw [(hder 0 0 g hg).deriv]
    have hz : toC0 (wv c 3 1 0) = 0 := by
      ext y
      rw [coe_toC0 (hC0 3 1 0 (by omega))]
      exact (hW c 3 0 y).2.1
    have h1 : cls μ (U 1 0) = cls μ (0 : Mat n → E.V) := by
      rw [hUc, cls_zero]
      show F.Φ (toC0 (wv c 3 1 0)) _ = 0
      rw [hz, map_zero]
      rfl
    exact (hC n μ E.V hU).1 _ 0 (sob_cont (hUS 1 0)) continuousOn_const (sob_memLp (hUS 1 0)) MemLp.zero h1 g hg
  · have hcut : F.Φ (toC0 rf * toC0 rf - toC0 (wv c 2 0 0)) (cls μ (Bn f 2)) = 0 := by
      refine hAC (Lp E.V 2 μ) (Msob μ E.V) Ω T F c _ (fun g => ?_) _ (fun y hy => ?_)
      · obtain ⟨u, h1, h2, -⟩ := hpres g 2
        refine ⟨⟨cls μ u, cls_mem μ h1⟩, h2, ?_⟩
        rw [hΩ _ _ h1]
        exact hc u h1 (sec_pres E hC hO hL hU hR F hrep hΩ _ (hbS _) (hbE _) h1 h2)
      · have e1 := (hW c 2 0 y).2.2.1
        rw [cut_eq_one hy] at e1
        have e2 : (toC0 rf * toC0 rf - toC0 (wv c 2 0 0)) y = rf y * rf y - wv c 2 0 0 y := by
          rw [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.mul_apply, coe_toC0 resolvent_function_vanishes_at_infinity,
            coe_toC0 (hC0 2 0 0 (by omega))]
        rw [e2, e1, rf, ← Complex.ofReal_mul, sub_eq_zero]
        congr 1
        rw [one_mul, pow_two (1 + y ^ 2), mul_inv]
    have hr : F.Φ (toC0 rf * toC0 rf) (cls μ (Bn f 2)) = cls μ f := by
      rw [F.map_mul, F.res (toC0 rf) (fun y => by rw [coe_toC0 resolvent_function_vanishes_at_infinity]; rfl), ContinuousLinearMap.mul_apply]
      have a1 : T (cls μ (Bn f 2)) = cls μ (Bn f 1) := T_B hC hO hL hU hR hΩ hT (hbS 1)
      have a2 : T (cls μ (Bn f 1)) = cls μ (Bn f 0) := T_B hC hO hL hU hR hΩ hT (hbS 0)
      rw [a1, a2]
      rfl
    have hw : F.Φ (toC0 (wv c 2 0 0)) (cls μ (Bn f 2)) = cls μ f := by
      rw [map_sub, ContinuousLinearMap.sub_apply, hr, sub_eq_zero] at hcut
      exact hcut.symm
    exact cls_eq_of_sob hC hU (hUS 0 0) (hbS 0) ((hUc 0 0).trans hw)

end Main

theorem waveRep : WaveRep := by
  intro n _ _ μ _ E _ Ω T F c hStd f hf hcf
  obtain ⟨hL, hU, hR, hSG, -, -, -, hCS, -, -, hrep, -, -, hT, hΩ, hc⟩ := hStd
  obtain ⟨-, hAC, hFc, hW, hC, hO, hCp, -, hP, -, hCJ, -, -, -, -⟩ := hCS
  exact coreRep E hL hU hR hSG hAC hFc hW hC hO hCp hP hCJ F hrep hΩ hT c hc hf hcf

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveUniqueness
section
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace ZeroAtInfty

namespace GlobalTheory.CompanionTheory.KerFc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Fc

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Uniq

variable {n : ℕ}

theorem isOpen_GLs : IsOpen (GLs n) := by
  have : GLs n = (fun g : Mat n => g.det) ⁻¹' {0}ᶜ := rfl
  rw [this]
  exact isOpen_compl_singleton.preimage (Continuous.matrix_det continuous_id)

section Rd

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem rd_congr (X : Mat n) {f f' : Mat n → V} (h : ∀ y ∈ GLs n, f y = f' y) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X f g = Rd X f' g := by
  have e : f =ᶠ[𝓝 g] f' := Filter.eventuallyEq_of_mem (isOpen_GLs.mem_nhds hg) h
  simp only [Rd, e.fderiv_eq]

theorem rd_sub (X : Mat n) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) (hf' : ContDiffOn ℝ ∞ f' (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : Rd X (f - f') g = Rd X f g - Rd X f' g := by
  have ho := isOpen_GLs.mem_nhds hg
  have d1 : DifferentiableAt ℝ f g := (hf.contDiffAt ho).differentiableAt (by simp)
  have d2 : DifferentiableAt ℝ f' g := (hf'.contDiffAt ho).differentiableAt (by simp)
  have e := (d1.hasFDerivAt.sub d2.hasFDerivAt).fderiv
  exact DFunLike.congr_fun e (g * X)

theorem rd_rd_sub (hR : RCalc) (X Y : Mat n) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (Rd Y (f - f')) g = Rd X (Rd Y f) g - Rd X (Rd Y f') g := by
  rw [rd_congr X (f' := Rd Y f - Rd Y f') (fun y hy => rd_sub Y hf hf' hy) hg]
  exact rd_sub X (((hR n).1 V f hf).1 Y) (((hR n).1 V f' hf').1 Y) hg

theorem om_sub (hO : OmFormula) (hR : RCalc) {f f' : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    (hf' : ContDiffOn ℝ ∞ f' (GLs n)) {g : Mat n} (hg : g ∈ GLs n) : Om (f - f') g = Om f g - Om f' g := by
  have hs : ContDiffOn ℝ ∞ (f - f') (GLs n) := hf.sub hf'
  rw [hO n V _ hs g hg, hO n V f hf g hg, hO n V f' hf' g hg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [rd_rd_sub hR _ _ hf hf' hg, rd_rd_sub hR _ _ hf hf' hg]
  abel

end Rd

theorem wave_line {E : KMod n} {u : ℝ → Mat n → E.V} (hu : IsWave E u) {g : Mat n} (hg : g ∈ GLs n) :
    ContDiff ℝ ∞ (fun s => u s g) := by
  have h := hu.1.comp (contDiff_prodMk_left (𝕜 := ℝ) (n := ∞) g).contDiffOn (s := Set.univ)
    (fun s _ => ⟨trivial, hg⟩)
  exact contDiffOn_univ.1 h

theorem wave_sub (hO : OmFormula) (hR : RCalc) {E : KMod n} {u u' : ℝ → Mat n → E.V} (hu : IsWave E u)
    (hu' : IsWave E u') : IsWave E (fun t => u t - u' t) := by
  refine ⟨hu.1.sub hu'.1, fun t => ⟨(hu.2.1 t).1.sub (hu'.2.1 t).1, fun g hg k => ?_⟩, fun t g hg => ?_, fun g hg => ?_⟩
  · show u t (g * k.1) - u' t (g * k.1) = E.ρ k⁻¹ (u t g - u' t g)
    rw [(hu.2.1 t).2 g hg k, (hu'.2.1 t).2 g hg k, map_sub]
  · have l := wave_line hu hg
    have l' := wave_line hu' hg
    have e : (fun s => (u s - u' s) g) = (fun s => u s g) - (fun s => u' s g) := rfl
    rw [e, iteratedDeriv_sub (contDiff_infty.1 l 2).contDiffAt (contDiff_infty.1 l' 2).contDiffAt,
      om_sub hO hR (hu.2.1 t).1 (hu'.2.1 t).1 hg, hu.2.2.1 t g hg, hu'.2.2.1 t g hg]
  · have d := (wave_line hu hg).differentiable (by simp)
    have d' := (wave_line hu' hg).differentiable (by simp)
    have e : (fun s => (u s - u' s) g) = (fun s => u s g) - (fun s => u' s g) := rfl
    rw [e, deriv_sub (d 0) (d' 0), hu.2.2.2 g hg, hu'.2.2.2 g hg, sub_zero]

end Uniq

theorem waveUniq : WaveUniq := by
  intro hS hC hR n E u u' hu hu' h0 t x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hO, -, -⟩ := hC
  obtain ⟨c, hc⟩ := hS n
  have h := hc E _ (Uniq.wave_sub hO hR hu hu') t x hx (fun y hy _ => by
    have hxy : x * y ∈ GLs n := by
      show (x * y).det ≠ 0
      rw [Matrix.det_mul]
      exact mul_ne_zero hx hy
    exact sub_eq_zero.2 (h0 _ hxy))
  exact sub_eq_zero.1 h

end GlobalTheory.CompanionTheory.KerFc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSymmetry
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.WhSymProof

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem wh_eq_of_equiv (f : GL ι K ≃ GL κ K) (Φ : ι → ι → Prop) (Φ' : κ → κ → Prop) (E : ι → ι → K)
    (E' : κ → κ → K) (ψ₀ : AddChar K ℂ) (χ : GL ι K → ℂ) (χ' : GL κ K → ℂ)
    (hm : ∀ x, f x ∈ patSet K Φ' ↔ x ∈ patSet K Φ)
    (hc : ∀ x, patChar E' ψ₀ (f x) = patChar E ψ₀ x)
    (hχ : ∀ x, χ' (f x) = χ x) :
    wh Φ E ψ₀ χ = wh Φ' E' ψ₀ χ' := by
  classical
  have himg : patSet K Φ' = f '' patSet K Φ := by
    ext y
    constructor
    · intro hy
      exact ⟨f.symm y, (hm _).1 (by simpa using hy), by simp⟩
    · rintro ⟨x, hx, rfl⟩
      exact (hm x).2 hx
  unfold wh
  rw [himg, Set.ncard_image_of_injective _ f.injective, ← himg]
  congr 1
  refine Fintype.sum_equiv f _ _ fun x => ?_
  by_cases hx : x ∈ patSet K Φ
  · rw [if_pos hx, if_pos ((hm x).2 hx), hc, hχ]
  · rw [if_neg hx, if_neg (fun h => hx ((hm x).1 h))]

theorem glEquiv_entry (e : ι ≃ κ) (x : GL ι K) (i j : ι) :
    ((glEquiv K e x : GL κ K) : Matrix κ κ K) (e i) (e j) = (x : Matrix ι ι K) i j := by
  rw [Formalism.L2.PT.coe_glEquiv]
  simp

theorem glEquiv_mem_patSet (Φ : κ → κ → Prop) (e : ι ≃ κ) (x : GL ι K) :
    glEquiv K e x ∈ patSet K Φ ↔ x ∈ patSet K (fun i j => Φ (e i) (e j)) := by
  constructor
  · intro h i j
    have h' := h (e i) (e j)
    rw [glEquiv_entry] at h'
    exact ⟨fun hij => h'.1 (congrArg e hij), fun hij => h'.2 (fun h2 => hij (e.injective h2))⟩
  · intro h i j
    obtain ⟨i, rfl⟩ := e.surjective i
    obtain ⟨j, rfl⟩ := e.surjective j
    have h' := h i j
    rw [glEquiv_entry]
    exact ⟨fun hij => h'.1 (e.injective hij), fun hij => h'.2 (fun h2 => hij (congrArg e h2))⟩

theorem patChar_glEquiv (E : κ → κ → K) (ψ₀ : AddChar K ℂ) (e : ι ≃ κ) (x : GL ι K) :
    patChar E ψ₀ (glEquiv K e x) = patChar (fun i j => E (e i) (e j)) ψ₀ x := by
  unfold patChar
  congr 1
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [glEquiv_entry]

theorem wh_renumber (Φ : κ → κ → Prop) (E : κ → κ → K) (ψ₀ : AddChar K ℂ) (χ : GL κ K → ℂ) (e : ι ≃ κ) :
    wh (fun i j => Φ (e i) (e j)) (fun i j => E (e i) (e j)) ψ₀ (fun x => χ (glEquiv K e x)) =
      wh Φ E ψ₀ χ :=
  wh_eq_of_equiv (glEquiv K e).toEquiv _ _ _ _ ψ₀ _ _ (fun x => glEquiv_mem_patSet Φ e x)
    (fun x => patChar_glEquiv E ψ₀ e x) (fun _ => rfl)

theorem glEquiv_trans_perm (e e' : ι ≃ κ) (x : GL ι K) :
    glEquiv K e' x = glEquiv K (e.symm.trans e') (glEquiv K e x) := by
  apply Units.ext
  ext a b
  obtain ⟨i, rfl⟩ := e'.surjective a
  obtain ⟨j, rfl⟩ := e'.surjective b
  have hs : ∀ i, (e.symm.trans e') (e i) = e' i := fun i => by simp
  rw [glEquiv_entry e' x i j, ← hs i, ← hs j, glEquiv_entry, glEquiv_entry]

theorem class_renumber (χ : GL κ K → ℂ) (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) (e e' : ι ≃ κ) (x : GL ι K) :
    χ (glEquiv K e x) = χ (glEquiv K e' x) := by
  rw [glEquiv_trans_perm e e' x, GlobalTheory.SerOSys.TranspLabel.glEquiv_perm, hχ]

def diagGL (t : κ → Kˣ) : GL κ K :=
  ⟨Matrix.diagonal fun i => (t i : K), Matrix.diagonal fun i => (((t i)⁻¹ : Kˣ) : K),
    by simp [Matrix.diagonal_mul_diagonal], by simp [Matrix.diagonal_mul_diagonal]⟩

omit [Fintype K] [DecidableEq K] in

theorem diagGL_conj_entry (t : κ → Kˣ) (u : GL κ K) (i j : κ) :
    ((diagGL t * u * (diagGL t)⁻¹ : GL κ K) : Matrix κ κ K) i j =
      (t i : K) * (u : Matrix κ κ K) i j * ((t j)⁻¹ : Kˣ) := by
  have hinv : (((diagGL t)⁻¹ : GL κ K) : Matrix κ κ K) = Matrix.diagonal fun i => (((t i)⁻¹ : Kˣ) : K) := rfl
  rw [Units.val_mul, Units.val_mul, hinv]
  show ((Matrix.diagonal (fun i => (t i : K)) * (u : Matrix κ κ K)) *
    Matrix.diagonal (fun i => (((t i)⁻¹ : Kˣ) : K)) : Matrix κ κ K) i j = _
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem wh_torus (Φ : κ → κ → Prop) (E : κ → κ → K) (ψ₀ : AddChar K ℂ) (χ : GL κ K → ℂ)
    (hχ : ∀ x g, χ (x * g * x⁻¹) = χ g) (t : κ → Kˣ) :
    wh Φ (fun i j => (t i : K) * E i j * ((t j)⁻¹ : Kˣ)) ψ₀ χ = wh Φ E ψ₀ χ := by
  refine wh_eq_of_equiv (MulAut.conj (diagGL t)).toEquiv _ _ _ _ ψ₀ _ _ (fun x => ?_) (fun x => ?_)
    (fun x => ?_)
  · show diagGL t * x * (diagGL t)⁻¹ ∈ patSet K Φ ↔ x ∈ patSet K Φ
    constructor
    · intro h i j
      have h' := h i j
      rw [diagGL_conj_entry] at h'
      refine ⟨fun hij => ?_, fun hij hn => ?_⟩
      · subst hij
        have h1 := h'.1 rfl
        have h2 : (t i : K) ≠ 0 := (t i).ne_zero
        have h3 : (((t i)⁻¹ : Kˣ) : K) = (t i : K)⁻¹ := by simp
        rw [h3] at h1
        field_simp at h1
        exact h1
      · have h1 := h'.2 hij hn
        simpa using h1
    · intro h i j
      have h' := h i j
      rw [diagGL_conj_entry]
      refine ⟨fun hij => ?_, fun hij hn => ?_⟩
      · subst hij
        rw [h'.1 rfl]
        simp
      · rw [h'.2 hij hn]
        simp
  · show patChar E ψ₀ (diagGL t * x * (diagGL t)⁻¹) = patChar _ ψ₀ x
    unfold patChar
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [diagGL_conj_entry]
    ring
  · show χ (diagGL t * x * (diagGL t)⁻¹) = χ x
    exact hχ _ _

theorem whSym : ReciprocityTheory.Ty.Fin.St.WhSym := by
  intro K _ _ _ ι κ _ _ _ _ Φ E ψ₀ χ
  exact ⟨fun e => wh_renumber Φ E ψ₀ χ e, fun hχ =>
    ⟨fun e e' x => class_renumber χ hχ e e' x, fun t => wh_torus Φ E ψ₀ χ hχ t⟩⟩

end GlobalTheory.CompanionTheory.TyFin.WhSymProof
end
end

