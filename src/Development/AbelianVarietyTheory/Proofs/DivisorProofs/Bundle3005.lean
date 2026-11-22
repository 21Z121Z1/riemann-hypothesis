import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.DiagValExtTraceNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2918
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DualGramInterpGram
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0573
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0314
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2931
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2920
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2661

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineHeightStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_height : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ, (hY.atlas σ).part α ε {y | v y = 1} = 0 := by
  first | exact @GlobalTheory.LineNull.part_cosSq_one | exact GlobalTheory.LineNull.part_cosSq_one | (intros; apply GlobalTheory.LineNull.part_cosSq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineIntegral
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CosSqSmooth

open TopologicalSpace Filter Topology
open scoped ComplexOrder ContDiff

def ratio (M : Fin 2 → Fin 2 → ℂ) : ℝ := ‖M 0 1‖ ^ 2 / ((M 1 1).re * (M 0 0).re)

theorem contDiffAt_ratio {M : Fin 2 → Fin 2 → ℂ} (hM : (M 1 1).re * (M 0 0).re ≠ 0) :
    ContDiffAt ℝ ∞ ratio M := by
  have a : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun N : Fin 2 → Fin 2 → ℂ => N i j) := fun i j =>
    (contDiff_apply ℝ ℂ j).comp (contDiff_apply ℝ (Fin 2 → ℂ) i)
  have re : ∀ i j : Fin 2, ContDiff ℝ ∞ (fun N : Fin 2 → Fin 2 → ℂ => (N i j).re) := fun i j =>
    Complex.reCLM.contDiff.comp (a i j)
  exact ((contDiff_norm_sq ℝ).comp (a 0 1)).contDiffAt.div
    ((re 1 1).mul (re 0 0)).contDiffAt hM

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

theorem vInfAt_of_isCosSq {V L L' : X.Modules} {r : ℕ} {m : Met p σ V r} (H : m.IsCInf)
    {l : L ⟶ V} {l' : L' ⟶ V} {v : CxPts p σ → ℝ} (hv : CurveDens.IsCosSq m l l' v)
    {U₁ U₂ : X.Opens} (t₁ : Γ(L, U₁)) (t₂ : Γ(L', U₂)) {y : CxPts p σ}
    (hy₁ : y ∈ ptsIn p σ U₁) (hy₂ : y ∈ ptsIn p σ U₂)
    (hp₁ : 0 < (m.form (l.app U₁ t₁) (l.app U₁ t₁) y).re)
    (hp₂ : 0 < (m.form (l'.app U₂ t₂) (l'.app U₂ t₂) y).re) :
    VInfAt v y ∧ 0 ≤ v y ∧ v y ≤ 1 := by
  have hy : y ∈ ptsIn p σ (U₁ ⊓ U₂) := mem_ptsIn_inf.2 ⟨hy₁, hy₂⟩
  set u₁ := Twist.resM _ (inf_le_left : U₁ ⊓ U₂ ≤ U₁) t₁
  set u₂ := Twist.resM _ (inf_le_right : U₁ ⊓ U₂ ≤ U₂) t₂
  set s₁ := l.app _ u₁
  set s₂ := l'.app _ u₂
  have e₁ : m.form s₁ s₁ y = m.form (l.app U₁ t₁) (l.app U₁ t₁) y := by
    simp only [s₁, u₁]; rw [Twist.app_resM, m.form_resM _ _ _ hy]
  have e₂ : m.form s₂ s₂ y = m.form (l'.app U₂ t₂) (l'.app U₂ t₂) y := by
    simp only [s₂, u₂]; rw [Twist.app_resM, m.form_resM _ _ _ hy]
  have q₁ : 0 < (m.form s₁ s₁ y).re := by rw [e₁]; exact hp₁
  have q₂ : 0 < (m.form s₂ s₂ y).re := by rw [e₂]; exact hp₂
  have hG := H.gram ![s₂, s₁] hy
  have c₁ : ContinuousAt (fun z => (m.form s₁ s₁ z).re) y :=
    Complex.continuous_re.continuousAt.comp (hG 1 1).continuousAt
  have c₂ : ContinuousAt (fun z => (m.form s₂ s₂ z).re) y :=
    Complex.continuous_re.continuousAt.comp (hG 0 0).continuousAt
  have key : v =ᶠ[𝓝 y] fun z => ratio (fun a b => m.gram ![s₂, s₁] z a b) := by
    filter_upwards [(isOpen_ptsIn _).mem_nhds hy, c₁.eventually (lt_mem_nhds q₁),
      c₂.eventually (lt_mem_nhds q₂)] with z hz h₁ h₂
    have e := hv _ u₁ u₂ z hz
    show v z = ‖m.form s₂ s₁ z‖ ^ 2 / ((m.form s₁ s₁ z).re * (m.form s₂ s₂ z).re)
    rw [e, mul_assoc, mul_div_cancel_right₀ _ (mul_pos h₁ h₂).ne']
  have hT : IsOpen {M : Fin 2 → Fin 2 → ℂ | (M 1 1).re * (M 0 0).re ≠ 0} :=
    isOpen_ne_fun (((Complex.continuous_re.comp ((continuous_apply 1).comp (continuous_apply 1))).mul
      (Complex.continuous_re.comp ((continuous_apply 0).comp (continuous_apply 0))))) continuous_const
  have hmem : m.gram ![s₂, s₁] y ∈ {M : Fin 2 → Fin 2 → ℂ | (M 1 1).re * (M 0 0).re ≠ 0} := by
    show (m.form s₁ s₁ y).re * (m.form s₂ s₂ y).re ≠ 0
    exact (mul_pos q₁ q₂).ne'
  refine ⟨(hG.comp (Ψ := ratio) hT hmem fun M hM => contDiffAt_ratio hM).congr key, ?_⟩
  have e := hv _ u₁ u₂ y hy
  have cs := CurveDens.normSq_form_le m s₂ s₁ y
  have hn : 0 ≤ ‖m.form s₂ s₁ y‖ ^ 2 := sq_nonneg _
  change ‖m.form s₂ s₁ y‖ ^ 2 = v y * (m.form s₁ s₁ y).re * (m.form s₂ s₂ y).re at e
  have hpp := mul_pos q₁ q₂
  constructor
  · by_contra hneg
    push_neg at hneg
    nlinarith
  · by_contra hbig
    push_neg at hbig
    nlinarith

theorem cosSq_smooth : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    (∀ y, 0 ≤ v y ∧ v y ≤ 1) ∧ Continuous v ∧ (hY.atlas σ).SmoothOn Set.univ (fun y => (v y : ℂ)) := by
  intro k _ B Y _ _ q p d _ hY π w E h H flB fl _ _ σ v hv
  have Hm : ((h.pull π w).met σ).IsCInf := H.pull π w σ
  have loc : ∀ y, VInfAt v y ∧ 0 ≤ v y ∧ v y ≤ 1 := fun y => by
    obtain ⟨U₁, t₁, hy₁, hp₁⟩ := CosSqMeas.exists_sec_form_pos ((h.pull π w).met σ) (fl.ι 1)
      (fl.isVB 1) (fl.isSubbundle 1) y
    obtain ⟨U₂, t₂, hy₂, hp₂⟩ := CosSqMeas.exists_sec_form_pos ((h.pull π w).met σ)
      ((Scheme.Modules.pullback π).map (flB.ι 1)) ((flB.isVB 1).pullback π)
      (SubPull.isSubbundle_pullback B Y π _ E (flB.ι 1) 1 (flB.isVB 1) (flB.isSubbundle 1)) y
    exact vInfAt_of_isCosSq Hm hv t₁ t₂ hy₁ hy₂ hp₁ hp₂
  refine ⟨fun y => (loc y).2, continuous_iff_continuousAt.2 fun y => (loc y).1.continuousAt, ?_⟩
  exact hY.smoothOn (G := fun z (_ _ : Unit) => (v z : ℂ))
    (fun y _ _ _ => (loc y).1.comp_contDiff Complex.ofRealCLM.contDiff) () ()

end GlobalTheory.CosSqSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLinePullbackFormStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_pullback_form : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    Measurable v := by
  first | exact @GlobalTheory.CosSqMeas.measurable_cosSq | exact GlobalTheory.CosSqMeas.measurable_cosSq | (intros; apply GlobalTheory.CosSqMeas.measurable_cosSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagMat
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB GlobalTheory.ShFam GlobalTheory.TrueGeo Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ArLieBase
open GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCls

section Bundle

def Adapted {Y : Scheme.{0}} {N : Y.Modules} {r : ℕ} (fl : Vert.Flag N r) {W : Y.Opens} (s : Fin r → Γ(N, W)) : Prop :=
  IsFrame s ∧ ∀ k : Fin (r + 1), ∃ t : Fin k → Γ(fl.F k, W), IsFrame t ∧
    ∀ i : Fin k, (fl.ι k).app W (t i) = s (Fin.castLE (Nat.lt_succ_iff.1 k.2) i)

variable {B Y : Scheme.{0}} {M : B.Modules} {r : ℕ} (hM : IsVB M r) (π : Y ⟶ B)

def coordAt {V : B.Opens} {f : Fin r → Γ(M, V)} (hf : IsFrame f) {K : Type} [CommRing K] (y : Sp K ⟶ Y) {W : Y.Opens}
    (hWV : W ≤ π ⁻¹ᵁ V) (hy : ⊤ ≤ y ⁻¹ᵁ W) (s : Γ((Scheme.Modules.pullback π).obj M, W)) : Fin r → K :=
  haveI := hM.isQuasicoherent
  fun b => TangentOrigin.evalPt y W hy (((hf.pullback π).basis hWV).repr s b)

def FlagMat (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) {V : B.Opens} {f : Fin r → Γ(M, V)} (hf : IsFrame f)
    {K : Type} [CommRing K] (y : Sp K ⟶ Y) (A : Matrix (Fin r) (Fin r) K) : Prop :=
  IsUnit A.det ∧ ∀ (k : Fin (r + 1)) (W : Y.Opens) (hWV : W ≤ π ⁻¹ᵁ V) (t : Γ(fl.F k, W)) (hy : ⊤ ≤ y ⁻¹ᵁ W),
    ∃ cf : Fin r → K, (∀ l : Fin r, (k : ℕ) ≤ l → cf l = 0) ∧
      coordAt hM π hf y hWV hy ((fl.ι k).app W t) = Matrix.vecMul cf A

def StepIso (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) {T : Scheme.{0}} {x : T ⟶ B}
    (fl' : Vert.Flag ((Scheme.Modules.pullback x).obj M) r) (y : T ⟶ Y) (w : y ≫ π = x) : Prop :=
  ∀ i, ∃ e : (Scheme.Modules.pullback y).obj (fl.F i) ≅ fl'.F i,
    e.hom ≫ fl'.ι i = (Scheme.Modules.pullback y).map (fl.ι i) ≫
      (Scheme.Modules.pullbackComp y π).hom.app M ≫ (Scheme.Modules.pullbackCongr w).hom.app M

variable {hM π}

theorem FlagMat.mul {fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r} {V : B.Opens} {f : Fin r → Γ(M, V)}
    {hf : IsFrame f} {K : Type} [CommRing K] {y : Sp K ⟶ Y} {A T : Matrix (Fin r) (Fin r) K}
    (h : FlagMat hM π fl hf y A) (hT : IsUnit T.det) (hT' : ∀ i j, i < j → T i j = 0) :
    FlagMat hM π fl hf y (T * A) := by
  refine ⟨by rw [Matrix.det_mul]; exact hT.mul h.1, fun k W hWV t hy => ?_⟩
  obtain ⟨cf, h1, h2⟩ := h.2 k W hWV t hy
  have := T.invertibleOfIsUnitDet hT
  have hb : T.BlockTriangular OrderDual.toDual := fun a b hab => hT' a b hab
  have hi := Matrix.blockTriangular_inv_of_blockTriangular hb
  refine ⟨Matrix.vecMul cf T⁻¹, fun l hl => ?_, ?_⟩
  · rw [Matrix.vecMul, dotProduct]
    refine Finset.sum_eq_zero fun m _ => ?_
    rcases lt_or_ge m l with hm | hm
    · rw [show T⁻¹ m l = 0 from hi hm, mul_zero]
    · rw [h1 m (hl.trans hm), zero_mul]
  · rw [h2, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hT, Matrix.one_mul]

end Bundle

def lieMat (dual : Bool) {r : ℕ} {K : Type} [CommRing K] (d : Matrix (Fin r) (Fin r) K) : Matrix (Fin r) (Fin r) K :=
  cond dual ((Matrix.transpose d⁻¹).submatrix Fin.rev id) d

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H}
  {Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l} {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {Oz : Type} [CommRing Oz]
  {β : Oz →+* c.F} (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β)

def AgreeAt {Bs Bg Y : Scheme.{0}} {M : Bs.Modules} {r : ℕ} (hM : IsVB M r) (jB : Bg ⟶ Bs) (u : FrAssign Z M r jB)
    (π : Y ⟶ Bs) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj M) r) (dual : Bool) {K : Type} [CommRing K]
    (y : Sp K ⟶ Y) (xb : Sp K ⟶ Bg) (x : Sp K ⟶ Z.X) (v : Fin r → (Sp (DualNumber K) ⟶ Z.t.G.left)) : Prop :=
  ∀ (V : Bs.Opens) (f : Fin r → Γ(M, V)) (hf : IsFrame f) (hx : ⊤ ≤ (xb ≫ jB) ⁻¹ᵁ V) (d : Matrix (Fin r) (Fin r) K),
    (∀ i, IsCombAtG Z.t x (u V f hf K xb hx) (d i) (v i)) → FlagMat hM π fl hf y (lieMat dual d)

def Bears {ι : Type} {rk : ι → ℕ} (emb : ι → (E →+* ℂ)) (dual : ι → Bool) (hr : ∀ a, rk a = Dw.mult (emb a))
    {Bs Bg Y : Scheme.{0}} {M : ι → Bs.Modules} (hM : ∀ a, IsVB (M a) (rk a)) (jB : Bg ⟶ Bs) (πB : Bg ⟶ gen Z)
    (u : ∀ a, FrAssign Z (M a) (rk a) jB) (π : Y ⟶ Bs)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (M a)) (rk a)) {K : Type} [CommRing K]
    (y : Sp K ⟶ Y) (xb : Sp K ⟶ Bg) {χ : c.F →+* K} {x : Sp K ⟶ Z.X} (g : EigFrame Z χ x) : Prop :=
  y ≫ π = xb ≫ jB ∧ x = xb ≫ πB ≫ genι Z ∧ xb ≫ πB ≫ genStr Z = spMap χ ∧
    ∀ a, AgreeAt Z (hM a) jB (u a) π (fl a) (dual a) y xb x fun i => g.v (emb a) (Fin.cast (hr a) i)

end Lie

end GlobalTheory.FlagCls

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormRealStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_omega_form_real : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), (hX.atlas σ).IsRealForm 1 (fld _ (omF hX σ h fl)) := by
  first | exact @GlobalTheory.LineForm.isRealForm_omF | exact GlobalTheory.LineForm.isRealForm_omF | (intros; apply GlobalTheory.LineForm.isRealForm_omF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagOmegaFormSqZeroStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_omega_form_sq_zero : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2), omF hX σ h fl * omF hX σ h fl = 0 := by
  first | exact @GlobalTheory.LineForm.omF_mul_self | exact GlobalTheory.LineForm.omF_mul_self | (intros; apply GlobalTheory.LineForm.omF_mul_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.VarFlag
open GlobalTheory.FlagMod (FlagCover FlagModel Frames)
open GlobalTheory.ShFam (EigFrame FlagCpt)
open ReciprocityTheory.AnForm.R.FinalTheorems (Snc)
open GlobalTheory.Toroidal (gen genι genStr genBd genBdIdeal)
open GlobalTheory.CompHS (Y₀ inc₀ str₀ barComp U₀ IsVariety₀ TorFlag dense_U₀ flagStr flagOpen)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)}

theorem Rel.over (X : FlagCover Y) (C : FlagCpt Y (RingEquiv.refl c.F)) {K : Type} [Field K] {z : Sp K ⟶ X.YY} {p : Sp K ⟶ C.Y.X}
    (h : Rel X.F C z p) : z ≫ X.π = p ≫ C.π ≫ genι Y := by
  obtain ⟨φ, k, hz, g, -, -, y, ψ, φ₁, f, t, t', hp, -, hT⟩ := h
  rw [hT.1, hp]
  simp only [Category.assoc]

theorem barComp_iff (Z : Formalism.L2.Pj.Comp Xo c) (B : Formalism.L2.Pj.Comp Xo c → GlobalTheory.ProjVar.Var c.F) (j : ∀ i, (B i).X ⟶ gen Y)
    (h1 : ∀ i, IsOpenImmersion (j i)) (h2 : ∀ i, ∀ p ∈ i.1, Y.jQ p ∈ Set.range (j i))
    (h3 : ∀ z : gen Y, ∃! i, z ∈ Set.range (j i)) (w : gen Y) :
    genι Y w ∈ barComp Y Z ↔ w ∈ Set.range (j Z) := by
  have hY : ∀ p : Xo.XF c, Y.j p = genι Y (Y.jQ p) := fun p => rfl
  have hc : ∀ p : Xo.XF c, ∃ i : Formalism.L2.Pj.Comp Xo c, p ∈ i.1 := fun p => by
    obtain ⟨u, hu, hs⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible _ (isIrreducible_singleton (x := p))
    exact ⟨⟨u, hu⟩, hs rfl⟩
  have key : ∀ p : Xo.XF c, Y.jQ p ∈ Set.range (j Z) → p ∈ Z.1 := fun p hp => by
    obtain ⟨i, hi⟩ := hc p
    obtain ⟨i', -, hu'⟩ := h3 (Y.jQ p)
    have e : i = Z := (hu' i (h2 i p hi)).trans (hu' Z hp).symm
    exact e ▸ hi
  obtain ⟨i, hi, -⟩ := h3 w
  constructor
  · intro hw
    by_contra hn
    have hiZ : i ≠ Z := fun e => hn (e ▸ hi)
    apply hw
    rw [mem_closure_iff]
    intro O hO hwO
    have := h1 i
    obtain ⟨_, hp, ⟨p, rfl⟩⟩ := Y.jQ_dense.inter_open_nonempty _
      ((hO.preimage (genι Y).continuous).inter (j i).isOpenEmbedding.isOpen_range) ⟨w, hwO, hi⟩
    refine ⟨Y.j p, hp.1, p, fun hpZ => ?_, rfl⟩
    obtain ⟨i', -, hu'⟩ := h3 (Y.jQ p)
    exact hiZ ((hu' i hp.2).trans (hu' Z (h2 Z p hpZ)).symm)
  · rintro ⟨b, rfl⟩ hw
    have := h1 Z
    rw [mem_closure_iff] at hw
    obtain ⟨_, ⟨w', hw', he⟩, ⟨p, hpZ, hp⟩⟩ := hw (genι Y '' Set.range (j Z))
      ((genι Y).isOpenEmbedding.isOpenMap _ (j Z).isOpenEmbedding.isOpen_range) ⟨_, ⟨b, rfl⟩, rfl⟩
    have e : w' = Y.jQ p := (genι Y).isOpenEmbedding.injective (he.trans (hp.symm.trans (hY p)))
    exact hpZ (key p (e ▸ hw'))

theorem genStr_eq : genStr Y = genι Y ≫ Y.s := by
  have h : spMap (RingHom.id c.F) = 𝟙 _ := Spec.map_id _
  exact ((Category.comp_id _).symm.trans (congrArg (genStr Y ≫ ·) h.symm)).trans pullback.condition.symm

theorem smooth_iso {A B S : Scheme.{0}} (e : A ⟶ B) [IsIso e] (g : B ⟶ S) {d : ℕ} (h : SmoothOfRelativeDimension d g) :
    SmoothOfRelativeDimension d (e ≫ g) := by
  have := smoothOfRelativeDimension_comp 0 d e g
  rwa [Nat.zero_add] at this

theorem smooth_gen {d : ℕ} (h : SmoothOfRelativeDimension d Y.s) : SmoothOfRelativeDimension d (genStr Y) := by
  rw [genStr_eq]
  exact smooth_iso _ _ h

theorem isVariety_of_iso (X : FlagCover Y) (Z : Formalism.L2.Pj.Comp Xo c) (C : FlagCpt Y (RingEquiv.refl c.F))
    (e : Y₀ X Z ⟶ C.Y.X) [IsIso e] (he : e ≫ C.Y.str = str₀ X Z) (hd : C.Y.dim = GlobalTheory.FlagTan.dimFlag Dw) : IsVariety₀ X Z := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← he, ← hd]
    exact smooth_iso _ _ inferInstance
  · obtain ⟨N, i, hi, hs⟩ := C.Y.isProjOver
    exact ⟨N, e ≫ i, inferInstance, by rw [Category.assoc, hs, he]⟩
  · rw [← he]
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected)
      (IsPullback.of_horiz_isIso ⟨by simp⟩ : IsPullback e (e ≫ C.Y.str) C.Y.str (𝟙 _)) inferInstance

theorem dim_eq (Dw : Datum H) : Dw.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 = GlobalTheory.FlagTan.dimFlag Dw := by
  rw [GlobalTheory.FlagDimSum.dim_add_sum_choose, GlobalTheory.FlagTan.dimFlag, Nat.choose_two_right]

theorem isVariety₀_flag : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → IsVariety₀ T.X Z := by
  intro E _ _ _ H Dw l Xo c T Z hF
  have hsm := smooth_gen T.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have := (hB Z).1
  obtain ⟨C, f, hπ, hdim, hl⟩ := GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1
  have hJ : ∀ w : gen T.Y, genι T.Y w ∈ barComp T.Y Z ↔ w ∈ Set.range (j Z) :=
    barComp_iff Z B j (fun i => (hB i).1) (fun i => (hB i).2.2.2) hcov
  have hX := GlobalTheory.T.flagChartFrames_eigenFrames_localRing T.X
  have hC := GlobalTheory.T.flagBundlePointFramesTriangular_component C

  have hspid : spMap (RingEquiv.refl c.F).toRingHom = 𝟙 _ := Spec.map_id _
  have hCs : C.π ≫ genStr T.Y = C.Y.str := by
    have := C.π_str
    rwa [hspid, Category.comp_id] at this
  have hps : (C.π ≫ genι T.Y) ≫ T.Y.s = C.Y.str := by rw [Category.assoc, ← genStr_eq, hCs]
  have : IsProper T.Y.s := projProper _ _ _ T.Y.proj
  have : IsProper ((C.π ≫ genι T.Y) ≫ T.Y.s) := by rw [hps]; infer_instance
  have : IsProper (C.π ≫ genι T.Y) := IsProper.of_comp _ T.Y.s

  have hcl : IsClosed (barComp T.Y Z : Set T.Y.X) := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    obtain ⟨w, rfl⟩ : ∃ w, genι T.Y w = y :=
      ⟨inv (genι T.Y) y, by rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]; rfl⟩
    obtain ⟨i, hi, -⟩ := hcov w
    have := (hB i).1
    refine ⟨genι T.Y '' Set.range (j i), ?_, ?_, ⟨w, hi, rfl⟩⟩
    · rintro _ ⟨w', hw', rfl⟩ hb
      obtain ⟨i', -, hu'⟩ := hcov w'
      have e : i = Z := (hu' i hw').trans (hu' Z ((hJ w').1 hb)).symm
      subst e
      exact hy ((hJ w).2 hi)
    · exact (genι T.Y).isOpenEmbedding.isOpenMap _ (j i).isOpenEmbedding.isOpen_range
  have : IsClosedImmersion (inc₀ T.X Z) := IsClosedImmersion.of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]
    exact hcl.preimage T.X.π.continuous)
  have : IsProper T.X.π := T.X.proper
  have : IsNormalScheme T.X.YY := GlobalTheory.IsNormalScheme.of_pred T.X.normal
  have : IsLocallyNoetherian T.X.YY := LocallyOfFiniteType.isLocallyNoetherian (T.X.π ≫ T.Y.s)
  have : CompactSpace T.Y.X := QuasiCompact.compactSpace_of_compactSpace T.Y.s
  have : CompactSpace T.X.YY := QuasiCompact.compactSpace_of_compactSpace T.X.π
  have : CompactSpace (Y₀ T.X Z) := QuasiCompact.compactSpace_of_compactSpace (inc₀ T.X Z)
  have : IsNoetherian (Y₀ T.X Z) := {}
  have hU : ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ T.X Z), ∃! p : Sp K ⟶ C.Y.X, Rel T.X.F C (z ≫ inc₀ T.X Z) p :=
    GlobalTheory.T.flagModel_point_carries_unique_flagBundle_point T.X Z hX C hC (B Z) (j Z) f hπ hl hJ
  obtain ⟨h, hh, hR⟩ := GlobalTheory.T.exists_hom_of_fieldPoint_relation_proper (Y₀ T.X Z) C.Y.X T.Y.X (inc₀ T.X Z ≫ T.X.π) (C.π ≫ genι T.Y)
    (fun K _ z w => Rel T.X.F C (z ≫ inc₀ T.X Z) w)
    (fun K _ z w hw => by rw [← Category.assoc]; exact Rel.over T.X C hw)
    (fun K _ z => hU K z)
    (fun K K' _ _ ι z w hw => by
      have := GlobalTheory.T.flagModel_carriesSameFlags_fieldExtension T.X hX C K K' ι _ _ hw
      rwa [← Category.assoc] at this)
    (fun A _ _ _ u v huv hr => by
      have := GlobalTheory.T.flagModel_carriesSameFlags_specialise_valuationRing T.X hX C hC A (u ≫ inc₀ T.X Z) v (by simpa only [Category.assoc] using huv)
        (by simpa only [Category.assoc] using hr)
      simpa only [Category.assoc] using this)
  have : IsProper (inc₀ T.X Z ≫ T.X.π) := inferInstance
  have : IsProper (h ≫ C.π ≫ genι T.Y) := by rw [hh]; infer_instance
  have : IsProper h := IsProper.of_comp h (C.π ≫ genι T.Y)
  have := GlobalTheory.T.flagModel_to_flagBundle_locallyQuasiFinite T.flag C hC Z h hR
  have hiso := GlobalTheory.T.isIso_flagModel_flagBundle_over_moduli T.X Z hX C hC (B Z) (j Z) f hπ hJ h hU hR
  have hVo : Nonempty (Vo C) := by
    refine ⟨⟨genericPoint C.Y.X, ?_⟩⟩
    show C.π (genericPoint C.Y.X) ∈ Set.range T.Y.jQ
    letI := (GlobalTheory.ShFam.constF (RingEquiv.refl c.F) C.Y).toAlgebra
    have e1 := Scheme.Hom.comp_apply (GlobalTheory.ShFam.genericPt C.Y) C.π (IsLocalRing.closedPoint C.Y.Fn)
    have e2 := Scheme.Hom.comp_apply (GlobalTheory.AllWt.ptF C.y0) T.Y.jQ (IsLocalRing.closedPoint C.Y.Fn)
    rw [C.y0_x] at e2
    have h1 := e1.symm.trans e2
    have h2 : (GlobalTheory.ShFam.genericPt C.Y) (IsLocalRing.closedPoint C.Y.Fn) = genericPoint C.Y.X :=
      Scheme.fromSpecStalk_closedPoint
    rw [h2] at h1
    exact ⟨_, h1.symm⟩
  have hpre : (U₀ T.X Z : Set (Y₀ T.X Z)) ⊆ h ⁻¹ᵁ Vo C := by
    intro y hy
    show C.π (h y) ∈ Set.range T.Y.jQ
    have e : genι T.Y (C.π (h y)) = T.X.π (inc₀ T.X Z y) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    obtain ⟨x, hx⟩ : T.X.π (inc₀ T.X Z y) ∈ Set.range T.Y.j := hy
    refine ⟨x, (genι T.Y).isOpenEmbedding.injective ?_⟩
    rw [e, ← hx, Model.j, Scheme.Hom.comp_apply]
  have : Nonempty (h ⁻¹ᵁ Vo C) := by
    obtain ⟨v⟩ := hVo
    exact ⟨inv (h ∣_ Vo C) v⟩
  have : IsIntegral (h ⁻¹ᵁ Vo C).toScheme := isIntegral_of_isOpenImmersion (h ∣_ Vo C)
  have hirr : IsIrreducible ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) := by
    rw [← Scheme.Opens.range_ι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (h ⁻¹ᵁ Vo C).ι.continuous.continuousOn
  have hdense : closure ((h ⁻¹ᵁ Vo C : (Y₀ T.X Z).Opens) : Set (Y₀ T.X Z)) = Set.univ :=
    ((dense_U₀ T.X Z).mono hpre).closure_eq
  have : IrreducibleSpace (Y₀ T.X Z) := (irreducibleSpace_def _).2 (by
    have := hirr.closure
    rw [hdense] at this
    exact this)
  have : IsIntegral (Y₀ T.X Z) := isIntegral_of_irreducibleSpace_of_isReduced _
  have := C.Y.isNormalScheme
  have : IsIso h := GlobalTheory.isIso_of_isProper_of_quasiFinite_of_birational h
    (fun y => inferInstance) (Vo C) hVo
  refine isVariety_of_iso T.X Z C h ?_ (by rw [hdim, (hB Z).2.1, dim_eq])
  rw [← hps, ← Category.assoc, hh, Category.assoc]

end GlobalTheory.VarFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagsSameFrameIsoStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flags_same_frame_iso : ∀ (X : Scheme.{0}) (F : X.Modules) (m : ℕ) (fl₁ fl₂ : Vert.Flag F m) (v : Fin m → Γ(F, ⊤)), Spans fl₁ ⊤ v → Spans fl₂ ⊤ v → ∀ i, ∃ e : fl₁.F i ≅ fl₂.F i, e.hom ≫ fl₂.ι i = fl₁.ι i := by
  first | exact @GlobalTheory.FlagCell.steps_iso_of_spans_top | exact GlobalTheory.FlagCell.steps_iso_of_spans_top | (intros; apply GlobalTheory.FlagCell.steps_iso_of_spans_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatNormalFibersOpenExtensionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_normal_fibers_open_extension : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (R₀ : Type) [CommRing R₀] (k : ℕ)
    (s t : Rule (unitObj 𝔠 6) R₀ k) (N : ℕ) (M : Scheme.{0}) (sM : M ⟶ Sp (Localization.Away (N : ℤ)))
    (U : Obj F 𝔠 M) (V : M.Opens), Flat sM →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))), Geo.Tor.IsNormalScheme (pullback sM t)) →
    (∀ (K : Type) [Field K] (t : Sp K ⟶ Sp (Localization.Away (N : ℤ))) (y : ↥(pullback sM t)),
      pullback.fst sM t y ∉ V → 2 ≤ ringKrullDim ((pullback sM t).presheaf.stalk y)) →
    ∀ (W : M.Opens) (hW : IsAffineOpen W),
    (∀ (W' : M.Opens) (hW' : IsAffineOpen W'), W' ≤ W ⊓ V → ∀ (Y' : Obj F 𝔠 (Sp Γ(M, W')))
      (φ' : Y'.A.left ⟶ U.A.left), Y'.IsPullBy U hW'.fromSpec φ' → (∀ (B : Type) [CommRing B] [Algebra R₀ B] (σ : Γ(M, W') →+* B) (Y'' : Obj F 𝔠 (Sp B)) (φ'' : Y''.A.left ⟶ Y'.A.left),
    Y''.IsPullBy Y' (spMap σ) φ'' → ∀ (h : IsUnit ((6 : ℕ) : B)) (δ : Y''.DetGen), s.val B Y'' h δ = t.val B Y'' h δ)) →
    ∀ (Y : Obj F 𝔠 (Sp Γ(M, W))) (φ : Y.A.left ⟶ U.A.left), Y.IsPullBy U hW.fromSpec φ →
    ∀ (YC : Obj F 𝔠 (Sp (R₀ ⊗[ℤ] Γ(M, W)))) (ψ : YC.A.left ⟶ Y.A.left),
      YC.IsPullBy Y (spMap (Algebra.TensorProduct.includeRight : Γ(M, W) →ₐ[ℤ] R₀ ⊗[ℤ] Γ(M, W)).toRingHom) ψ →
      ∀ (h : IsUnit ((6 : ℕ) : R₀ ⊗[ℤ] Γ(M, W))) (δ : YC.DetGen), s.val _ YC h δ = t.val _ YC h δ := by
  first | exact @GlobalTheory.RealMult.rule_eq_on_extend_chart | exact GlobalTheory.RealMult.rule_eq_on_extend_chart | (intros; apply GlobalTheory.RealMult.rule_eq_on_extend_chart <;> assumption)
end

