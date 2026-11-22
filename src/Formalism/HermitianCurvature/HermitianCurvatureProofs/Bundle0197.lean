import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0188
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0190
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0054
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0077
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BlockOfChoices
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0183
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0084
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelFormSesquilinearFiniteClass

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.HermitianSquareIntegrableAll
section
open MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Meas

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

def glueMapI (i : Fin (r + 1)) (c : Fin r → ℂ) (q : Cf r i × Mt k r) : (Fin r → ℂ) × Mx k r :=
  (glue i c q.1, Matrix.of q.2)

theorem glueMapI_continuous (i : Fin (r + 1)) (c : Fin r → ℂ) : Continuous (glueMapI (k := k) i c) := by
  refine Continuous.prodMk ?_ continuous_snd
  refine continuous_pi fun l => ?_
  by_cases h : i.val ≤ l.val
  · have e : (fun q : Cf r i × Mt k r => glue i c q.1 l) = fun q => q.1 ⟨l, h⟩ := by
      funext q; simp [glue, h]
    rw [e]; exact (continuous_apply _).comp continuous_fst
  · have e : (fun q : Cf r i × Mt k r => glue i c q.1 l) = fun _ => c l := by
      funext q; simp [glue, h]
    rw [e]; exact continuous_const

theorem measurableSet_glueMapI_DomR (i : Fin (r + 1)) (c : Fin r → ℂ) :
    MeasurableSet (glueMapI (k := k) i c ⁻¹' DomR k r z z') := by
  rw [DomR_eq, Set.preimage_inter]
  exact ((Formalism.FourierDecayAlt.P.Qx5.isOpen_OpR k r z z').preimage (glueMapI_continuous i c)).measurableSet.inter
    (((Formalism.FourierDecayAlt.P.Qx5.Glev_closed (Fin.last r)).preimage continuous_snd).preimage
      (glueMapI_continuous i c)).measurableSet

theorem pair_measurableI (i : Fin (r + 1)) (c : Fin r → ℂ) (Φ Ψ : RadSp k r z z' π π') :
    Measurable (fun q : Cf r i × Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2))) := by
  have hmaps : Set.MapsTo (glueMapI (k := k) i c) (glueMapI (k := k) i c ⁻¹' DomR k r z z') (DomR k r z z') :=
    fun q hq => hq
  have hΦc := (radSp_continuousOn Φ).comp (glueMapI_continuous i c).continuousOn hmaps
  have hΨc := (radSp_continuousOn Ψ).comp (glueMapI_continuous i c).continuousOn hmaps
  refine measurable_of_continuousOn_zero (measurableSet_glueMapI_DomR i c)
    ((Formalism.FourierDecayAlt.P.B6.hsInner_continuous (Wp := Wp) (Wq := Wq)).comp_continuousOn (hΦc.prodMk hΨc)) ?_
  intro q hq
  have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2) = 0 := radSp_zero_off Φ hq
  show B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) (glue i c q.1) (Matrix.of q.2)) _ = 0
  rw [h0, Formalism.FourierDecayAlt.P.B6.hilbert_schmidt_inner_basis_sum]
  simp

theorem pairAt_measI (μ : Measure (Mt k r)) [SFinite μ] (i : Fin (r + 1)) (u v : RadSp k r z z' π π')
    (c : Fin r → ℂ) : StronglyMeasurable (fun c' : Cf r i => pairAt μ u v (glue i c c')) :=
  (pair_measurableI i c u v).stronglyMeasurable.integral_prod_right'

def wtI (i : Fin (r + 1)) (c' : Cf r i) : ℂ := ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ)

theorem wtI_measurable (i : Fin (r + 1)) : Measurable (wtI i) := by
  unfold wtI
  have e : ∀ x : ℝ, x ^ (-2 : ℤ) = (x ^ 2)⁻¹ := fun x => by rw [zpow_neg]; norm_cast
  simp_rw [e]
  exact Complex.measurable_ofReal.comp
    (Finset.measurable_prod _ fun l _ => ((measurable_norm.comp (measurable_pi_apply l)).pow_const 2).inv)

def LevelSquareIntegrable (μ : Measure (Mt k r)) (i : Fin (r + 1)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) : Prop :=
  Integrable (fun c' : Cf r i => wtI i c' * pairAt μ u u (glue i c c'))

theorem hsInner_self_ofRealI (A : Wq →L[ℂ] Wp) : B.hsInner A A = ((‖B.hsVec A‖ ^ 2 : ℝ) : ℂ) := by
  unfold B.hsInner
  rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (B.hsVec A)]
  push_cast
  rfl

theorem norm_pairAt_selfI (μ : Measure (Mt k r)) (u : RadSp k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u u c‖ = ∫ g : Mt k r, ‖B.hsInner ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((u : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))‖ ∂μ := by
  unfold pairAt
  simp_rw [hsInner_self_ofRealI]
  rw [integral_complex_ofReal, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg fun g => by positivity)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]

theorem norm_pairAt_leI (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ)
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    ‖pairAt μ u v c‖ ≤ ‖pairAt μ u u c‖ + ‖pairAt μ v v c‖ := by
  rw [norm_pairAt_selfI, norm_pairAt_selfI]
  unfold pairAt
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add (int_lc μ hμ hu hu c).norm (int_lc μ hμ hv hv c).norm]
  exact integral_mono (int_lc μ hμ hu hv c).norm ((int_lc μ hμ hu hu c).norm.add (int_lc μ hμ hv hv c).norm)
    fun g => norm_hs_le _ _

theorem int_crossI (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (i : Fin (r + 1))
    {u v : RadSp k r z z' π π'} (hu : u ∈ lcSub k r z z' π π') (hv : v ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : LevelSquareIntegrable μ i u c) (Iv : LevelSquareIntegrable μ i v c) :
    Integrable (fun c' : Cf r i => wtI i c' * pairAt μ u v (glue i c c')) := by
  refine (Iu.norm.add Iv.norm).mono'
    ((wtI_measurable i).aestronglyMeasurable.mul (pairAt_measI μ i u v c).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun c' => ?_)
  show ‖wtI i c' * pairAt μ u v (glue i c c')‖ ≤
    ‖wtI i c' * pairAt μ u u (glue i c c')‖ + ‖wtI i c' * pairAt μ v v (glue i c c')‖
  rw [norm_mul, norm_mul, norm_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_pairAt_leI μ hμ hu hv _) (norm_nonneg _)

end Meas

section Red

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formIntOuter_of_l2I {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Mx k r → (Wq →L[ℂ] Wq)} (μ : Measure (Mt k r)) [SFinite μ]
    (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (i : Fin (r + 1)) (u v : Ix S → RadSp k r z z' π π')
    (hu : ∀ a, u a ∈ lcSub k r z z' π π') (hv : ∀ a, v a ∈ lcSub k r z z' π π') (c : Fin r → ℂ)
    (Iu : ∀ a, LevelSquareIntegrable μ i (u a) c) (Iv : ∀ a, LevelSquareIntegrable μ i (v a) c) :
    Integrable (fun c' : Cf r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      ∑ a, pairAt μ (u a) (v a) (glue i c c')) := by
  simp_rw [Finset.mul_sum]
  exact integrable_finsetSum _ fun a _ => int_crossI μ hμ i (hu a) (hv a) c (Iu a) (Iv a)

def HermitianSquareIntegrableAt (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (i : Fin (P.r + 1)) : Prop :=
  ∀ c ∈ OmX P.r, (∀ u ∈ herKc S P z z' π π' L st l0 D i, LevelSquareIntegrable μ i u c) ∧
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ x : Ix S → RadSp P.k P.r z z' π π',
      InK (herKc S P z z' π π' L st l0 D i) x → ∀ a, LevelSquareIntegrable μ i (act (RRi L st i w) x a) c

def HermitianSquareIntegrableAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ i : Fin (P.r + 1), i.val < P.r → HermitianSquareIntegrableAt (S := S) P z z' π π' μ L st l0 D i

theorem outer_form_compact_of_square (h : HermitianSquareIntegrableAll) : FormIntOuterCpt := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw i c hc x y hx hy
  by_cases hi : i.val < P.r
  · have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
    have hle := herKc_le_lc (S := S) (st := st) (l0 := l0) X hD.2.2.1
      (fun F Φ hF hΦ => jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ) i
    have hRR := RRi_lc X μ L st l0 hD i w hw.1.2.1
    have hu : ∀ a, act (RRi L st i w) x a ∈ lcSub P.k P.r z z' π π' := fun a =>
      (lcSub P.k P.r z z' π π').sum_mem fun b _ => (hRR a b).1 _ (hle (hx b))
    obtain ⟨hK, hR⟩ := h Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' i hi c hc
    exact formIntOuter_of_l2I μ hD.2.1 i _ y hu (fun a => hle (hy a)) c (hR w hw x hx) (fun a => hK _ (hy a))
  · have e : i = Fin.last P.r := Fin.ext (by have := i.isLt; simp only [Fin.val_last]; omega)
    subst e
    exact integrable_cf_last _

end Red

end Formalism.FourierDecayAlt.P5.HerD
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LiftDegreeLemmas
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open scoped ComplexConjugate ComplexOrder

noncomputable section

section nice

variable {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq]

def NV {S : Type} (Bs : B.RealPlaceData k ρ Wp Wq) (ε : ℝ) (x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ e, JC.NiceCoef Bs ε (x e)

variable {S : Type} {Bs : B.RealPlaceData k ρ Wp Wq} {ε : ℝ}

theorem nv_zero : NV (S := S) Bs ε 0 := fun _ => JCx2.mn_nice_zero

theorem nv_add {x y : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : NV Bs ε x) (hy : NV Bs ε y) : NV Bs ε (x + y) :=
  fun e => JCx2.mn_nice_add (hx e) (hy e)

theorem nv_smul (c : ℂ) {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (hx : NV Bs ε x) : NV Bs ε (c • x) :=
  fun e => JCx2.mn_nice_smul c (hx e)

theorem nice_mono {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : JC.NiceCoef Bs ε F) (h' : ε' ≤ ε) :
    JC.NiceCoef Bs ε' F :=
  ⟨h.1, h.2.1, fun g hg hne => h'.trans (h.2.2 g hg hne)⟩

theorem nv_mono {x : Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)} {ε ε' : ℝ} (h : NV Bs ε x) (h' : ε' ≤ ε) : NV Bs ε' x :=
  fun e => nice_mono (h e) h'

theorem nice_of_cpt {F : B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : KB.CptCoef Bs F) : ∃ ε, 0 < ε ∧ JC.NiceCoef Bs ε F := by
  obtain ⟨hs, ⟨R, hR⟩, ⟨ε, hε, hG⟩⟩ := h
  refine ⟨ε, hε, hs, fun A m => JFxG.cptInCC_G hs (PBE.isCompact_gN_le k ρ R) (fun g hg hgC => ?_) A m, hG⟩
  by_contra h0
  exact hgC (hR g hg h0)

end nice

section forms

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {P : M.Par}

theorem nv_common {α S : Type} {k ρ : ℕ} {Bs : B.RealPlaceData k ρ Wp Wq} (Y : Finset α)
    (u : α → Wd.Ix S → B.Mat k ρ → (Wq →L[ℂ] Wp)) (h : ∀ a ∈ Y, ∃ ε, 0 < ε ∧ NV Bs ε (u a)) :
    ∃ ε, 0 < ε ∧ ∀ a ∈ Y, NV Bs ε (u a) := by
  obtain ⟨ε, hε, hall⟩ := common_eps (ι := Y) (fun a ε => NV Bs ε (u a)) (fun a ε ε' h h0 h' => nv_mono h h')
    (fun a => h a a.2)
  exact ⟨ε, hε, fun a ha => hall ⟨a, ha⟩⟩

theorem slv_nv (p : KB.Pl P Wp Wq) {F : B.Mat P.k P.r → (Wq →L[ℂ] Wp)} (hF : KB.CptCoef p.T.base F) (j : ℕ)
    (hj : j ≤ P.r) (w : List C.Letter) (a : C.LPt) (ha : D.IsLocPt a j) :
    ∃ ε, 0 < ε ∧ NV (p.T.bs j) ε (KB.slv p.T F j hj w a ha.2) := by
  have h := fun e => nice_of_cpt (Formalism.FourierDecayAlt.P.slice_compact_support_coefficient Wp Wq P p F j hj w a ha hF e)
  obtain ⟨ε, hε, hall⟩ := common_eps (fun e ε => JC.NiceCoef (p.T.bs j) ε (KB.slv p.T F j hj w a ha.2 e))
    (fun e ε ε' h h0 h' => nice_mono h h') h
  exact ⟨ε, hε, hall⟩

theorem form_eq' (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) :
    p.form j hj w = D.formLev p.T (M.sgn P p.l0) ⟨j, by omega⟩ w := rfl

theorem form_sl (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) {ε : ℝ}
    (x₁ x₂ y : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (h₁ : NV (p.T.bs j) ε x₁) (h₂ : NV (p.T.bs j) ε x₂) (hy : NV (p.T.bs j) ε y) :
    p.form j hj w (x₁ + c • x₂) y = p.form j hj w x₁ y + c * p.form j hj w x₂ y :=
  PBG.form_sesq_left P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x₁ x₂ y c (PBG.decV_of_nice h₁) (PBG.decV_of_nice h₂)
    (PBG.decV_of_nice hy)

theorem form_sr (p : KB.Pl P Wp Wq) (j : ℕ) (hj : j ≤ P.r) (w : List C.Letter) {ε : ℝ}
    (x y₁ y₂ : Wd.Ix (Fin w.length) → B.Mat P.k (P.r - j) → (Wq →L[ℂ] Wp)) (c : ℂ)
    (hx : NV (p.T.bs j) ε x) (h₁ : NV (p.T.bs j) ε y₁) (h₂ : NV (p.T.bs j) ε y₂) :
    p.form j hj w x (y₁ + c • y₂) = p.form j hj w x y₁ + conj c * p.form j hj w x y₂ :=
  PBG.form_sesq_right P p.T (M.sgn P p.l0) ⟨j, by omega⟩ w x y₁ y₂ c (PBG.decV_of_nice hx) (PBG.decV_of_nice h₁)
    (PBG.decV_of_nice h₂)

end forms

end

end Formalism.FourierDecayAlt.P.PBL
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.LoeZeroOfPsd
section
namespace Formalism.FourierDecayAlt.P.PBL

open Formalism.FourierDecayAlt Finset
open scoped ComplexConjugate ComplexOrder InnerProductSpace

noncomputable section

section gram

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {α : Type}

def gramH (h : α → H) : α → α → ℂ := fun P Q => ⟪h Q, h P⟫_ℂ

theorem qf_gramH (Y : Finset α) (h : α → H) (c : α → ℂ) :
    PBA.qf Y (gramH h) c = ⟪∑ P ∈ Y, conj (c P) • h P, ∑ P ∈ Y, conj (c P) • h P⟫_ℂ := by
  unfold PBA.qf gramH
  rw [sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, Complex.conj_conj]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring

theorem psd_gramH (Y : Finset α) (h : α → H) : TB.PSDOn Y (gramH h) := by
  rw [PBA.psd_iff_qf]
  refine ⟨fun P _ Q _ => (inner_conj_symm (𝕜 := ℂ) (h P) (h Q)).symm, fun c => ?_⟩
  rw [qf_gramH]
  exact inner_self_nonneg (𝕜 := ℂ)

def Loe (Y : Finset α) (A B : α → α → ℂ) : Prop := TB.PSDOn Y fun P Q => B P Q - A P Q

theorem loe_iff (Y : Finset α) (A B : α → α → ℂ) :
    Loe Y A B ↔ (∀ x ∈ Y, ∀ y ∈ Y, B y x - A y x = conj (B x y - A x y)) ∧
      ∀ c, (PBA.qf Y A c).re ≤ (PBA.qf Y B c).re := by
  unfold Loe
  rw [PBA.psd_iff_qf]
  have e : ∀ c, PBA.qf Y (fun P Q => B P Q - A P Q) c = PBA.qf Y B c - PBA.qf Y A c := by
    intro c; unfold PBA.qf; simp only [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun Q _ => by ring
  simp only [e, Complex.sub_re, sub_nonneg]

theorem loe_trans {Y : Finset α} {A B C : α → α → ℂ} (h1 : Loe Y A B) (h2 : Loe Y B C) : Loe Y A C := by
  rw [loe_iff] at h1 h2 ⊢
  refine ⟨fun x hx y hy => ?_, fun c => (h1.2 c).trans (h2.2 c)⟩
  have a := h1.1 x hx y hy
  have b := h2.1 x hx y hy
  have : C y x - A y x = (C y x - B y x) + (B y x - A y x) := by ring
  rw [this, a, b, ← map_add]; ring_nf

theorem loe_zero_of_psd {Y : Finset α} {B : α → α → ℂ} (h : TB.PSDOn Y B) : Loe Y (fun _ _ => 0) B := by
  unfold Loe; simpa using h

theorem psd_of_loe_zero {Y : Finset α} {B : α → α → ℂ} (h : Loe Y (fun _ _ => 0) B) : TB.PSDOn Y B := by
  unfold Loe at h; simpa using h

theorem qf_mix {N : Type} [Fintype N] (Y : Finset α) (A : N → α → α → ℂ) (θ : N → ℝ) (M : ℝ) (c : α → ℂ) :
    PBA.qf Y (fun p q => (M : ℂ) * ∑ n, (θ n : ℂ) * A n p q) c = (M : ℂ) * ∑ n, (θ n : ℂ) * PBA.qf Y (A n) c := by
  unfold PBA.qf
  have e' : ∀ x y, conj (c x) * ((M : ℂ) * ∑ n, (θ n : ℂ) * A n x y) * c y =
      ∑ n, (M : ℂ) * ((θ n : ℂ) * (conj (c x) * A n x y * c y)) := by
    intro x y
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun n _ => by ring
  simp_rw [e']
  rw [swap3, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]

theorem norm_mix_sq {N : Type} [Fintype N] (lam : N → ℂ) (W : N → H) :
    ‖∑ n, lam n • W n‖ ^ 2 ≤ (∑ n, ‖lam n‖) * ∑ n, ‖lam n‖ * ‖W n‖ ^ 2 := by
  have h1 : ‖∑ n, lam n • W n‖ ≤ ∑ n, ‖lam n‖ * ‖W n‖ :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_smul _ _).le)
  have h2 : (∑ n, ‖lam n‖ * ‖W n‖) ^ 2 ≤ (∑ n, ‖lam n‖) * ∑ n, ‖lam n‖ * ‖W n‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun n => Real.sqrt ‖lam n‖)
      (fun n => Real.sqrt ‖lam n‖ * ‖W n‖)
    have e1 : ∀ n, Real.sqrt ‖lam n‖ * (Real.sqrt ‖lam n‖ * ‖W n‖) = ‖lam n‖ * ‖W n‖ := fun n => by
      rw [← mul_assoc, Real.mul_self_sqrt (norm_nonneg _)]
    have e2 : ∀ n, Real.sqrt ‖lam n‖ ^ 2 = ‖lam n‖ := fun n => Real.sq_sqrt (norm_nonneg _)
    have e3 : ∀ n, (Real.sqrt ‖lam n‖ * ‖W n‖) ^ 2 = ‖lam n‖ * ‖W n‖ ^ 2 := fun n => by
      rw [mul_pow, e2]
    simp only [e1, e2, e3] at this
    exact this
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem loe_convex {N : Type} [Fintype N] (Y : Finset α) (lam : N → ℂ) (h : N → α → H) :
    Loe Y (gramH fun P => ∑ n, lam n • h n P)
      (fun P Q => ((∑ n, ‖lam n‖ : ℝ) : ℂ) * ∑ n, ((‖lam n‖ : ℝ) : ℂ) * gramH (h n) P Q) := by
  rw [loe_iff]
  constructor
  · intro x _ y _
    simp only [gramH, map_sub, map_mul, map_sum, Complex.conj_ofReal, inner_conj_symm]
  · intro c
    have eW : ∑ P ∈ Y, conj (c P) • ∑ n, lam n • h n P = ∑ n, lam n • ∑ P ∈ Y, conj (c P) • h n P := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun P _ => by rw [mul_comm]
    rw [qf_gramH, eW, qf_mix]
    simp only [qf_gramH]
    have hre : ∀ x : H, (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := fun x => by
      have := inner_self_eq_norm_sq (𝕜 := ℂ) x; simpa using this
    rw [Complex.re_ofReal_mul, Complex.re_sum, hre]
    simp only [Complex.re_ofReal_mul, hre]
    exact norm_mix_sq lam _

theorem loe_congr {Y : Finset α} {A A' B B' : α → α → ℂ} (hA : ∀ x ∈ Y, ∀ y ∈ Y, A x y = A' x y)
    (hB : ∀ x ∈ Y, ∀ y ∈ Y, B x y = B' x y) (h : Loe Y A B) : Loe Y A' B' :=
  psd_congr (fun x hx y hy => by rw [hA x hx y hy, hB x hx y hy]) h

theorem loe_refl (Y : Finset α) (A : α → α → ℂ) : Loe Y A A := by
  unfold Loe
  refine psd_congr (k := fun _ _ => (0 : ℂ)) (fun x _ y _ => by ring) ?_
  rw [PBA.psd_iff_qf]; exact ⟨fun _ _ _ _ => by simp, fun c => by simp [PBA.qf]⟩

theorem loe_add {Y : Finset α} {A B A' B' : α → α → ℂ} (h : Loe Y A B) (h' : Loe Y A' B') :
    Loe Y (fun x y => A x y + A' x y) (fun x y => B x y + B' x y) := by
  rw [loe_iff] at h h' ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy; have b := h'.1 x hx y hy
    have : B y x + B' y x - (A y x + A' y x) = (B y x - A y x) + (B' y x - A' y x) := by ring
    rw [this, a, b, ← map_add]; ring_nf
  · have e : ∀ K K' : α → α → ℂ, PBA.qf Y (fun x y => K x y + K' x y) c = PBA.qf Y K c + PBA.qf Y K' c := by
      intro K K'; unfold PBA.qf; simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, e, Complex.add_re, Complex.add_re]
    linarith [h.2 c, h'.2 c]

theorem loe_smul {Y : Finset α} {A B : α → α → ℂ} (r : ℝ) (hr : 0 ≤ r) (h : Loe Y A B) :
    Loe Y (fun x y => (r : ℂ) * A x y) (fun x y => (r : ℂ) * B x y) := by
  rw [loe_iff] at h ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy
    rw [← mul_sub, ← mul_sub, a, map_mul, Complex.conj_ofReal]
  · have e : ∀ K : α → α → ℂ, PBA.qf Y (fun x y => (r : ℂ) * K x y) c = (r : ℂ) * PBA.qf Y K c := by
      intro K; unfold PBA.qf; simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [e, e, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
    exact mul_le_mul_of_nonneg_left (h.2 c) hr

theorem loe_sum {ι : Type} (s : Finset ι) {Y : Finset α} {A B : ι → α → α → ℂ} (h : ∀ i ∈ s, Loe Y (A i) (B i)) :
    Loe Y (fun x y => ∑ i ∈ s, A i x y) (fun x y => ∑ i ∈ s, B i x y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using loe_refl Y (fun _ _ => (0 : ℂ))
  | insert b t hb ih =>
    have h1 := loe_add (h b (Finset.mem_insert_self _ _)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    refine loe_congr (fun x _ y _ => ?_) (fun x _ y _ => ?_) h1
    · rw [Finset.sum_insert hb]
    · rw [Finset.sum_insert hb]

theorem loe_diag {Y : Finset α} {A B : α → α → ℂ} (ω : α → ℝ) (h : Loe Y A B) :
    Loe Y (fun x y => (ω x : ℂ) * (ω y : ℂ) * A x y) (fun x y => (ω x : ℂ) * (ω y : ℂ) * B x y) := by
  rw [loe_iff] at h ⊢
  refine ⟨fun x hx y hy => ?_, fun c => ?_⟩
  · have a := h.1 x hx y hy
    have : (ω y : ℂ) * (ω x : ℂ) * B y x - (ω y : ℂ) * (ω x : ℂ) * A y x = (ω y : ℂ) * (ω x : ℂ) * (B y x - A y x) := by
      ring
    rw [this, a]; simp only [map_mul, map_sub, Complex.conj_ofReal]; ring
  · have e : ∀ K : α → α → ℂ, PBA.qf Y (fun x y => (ω x : ℂ) * (ω y : ℂ) * K x y) c =
        PBA.qf Y K (fun x => (ω x : ℂ) * c x) := by
      intro K; unfold PBA.qf
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by
        simp only [map_mul, Complex.conj_ofReal]; ring
    rw [e, e]
    exact h.2 _

theorem loe_scale {Y : Finset α} {K : α → α → ℂ} (hK : TB.PSDOn Y K) {r r' : ℝ} (hr : 0 ≤ r' - r) :
    Loe Y (fun x y => (r : ℂ) * K x y) (fun x y => (r' : ℂ) * K x y) := by
  have h := loe_smul (r' - r) hr (loe_zero_of_psd hK)
  unfold Loe at h ⊢
  refine psd_congr (fun x _ y _ => ?_) h
  push_cast; ring

theorem gramH_smul (c : ℂ) (h : α → H) :
    gramH (fun P => c • h P) = fun P Q => ((‖c‖ ^ 2 : ℝ) : ℂ) * gramH h P Q := by
  funext P Q
  unfold gramH
  rw [inner_smul_left, inner_smul_right, ← mul_assoc, mul_comm (conj c) c, Complex.mul_conj']
  push_cast; ring

end gram

end

end Formalism.FourierDecayAlt.P.PBL
end

