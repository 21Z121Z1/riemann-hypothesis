import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToVInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1085
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0215
import ReciprocityTheory.ClassFieldTheory.LocalClassField.RecCyclic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1050
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1130
import GroundTheory.AutomorphicForms.Anisotropic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0239
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1881
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCurvatureAtPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3099
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2669
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1207
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2281
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2184
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2556
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteOrbitsCxFNeZero
section
noncomputable section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.CxUnfold

variable {p : ℕ} [Fact p.Prime] {G : HTGroup p} {v : InfinitePlace G.F} {β : G.Cˣ} {x : (AfP p ⊗[ℚ] G.C)ˣ}
  {t : (AfP p)ˣ} {hx : Triv G (AfP p) β x t} {Kf : Subgroup G.GAf} {K' : Subgroup (Gr G 1)}

theorem posV_val_ne_zero (z : PosV G v β) : z.1 ≠ 0 := by
  intro h
  have hz := z.2
  rw [h] at hz
  simp at hz

theorem fixL_smul_vec_iff (y : grp G β) (z : Fin G.n → ℂ) {c : ℂ} (hc : c ≠ 0) :
    FixL G v β y (c • z) ↔ FixL G v β y z := by
  unfold FixL
  simp only [Matrix.mulVec_smul]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e, ?_⟩
    rw [smul_comm e c z] at he
    exact smul_right_injective _ hc he
  · rintro ⟨e, he⟩
    exact ⟨e, by rw [he, smul_comm]⟩

variable (G v β x t hx Kf K')

def orbOfDat (d : Dat G v β) : MulAction.orbitRel.Quotient (grp G β) (Ys G v β x t hx Kf K') :=
  Quotient.mk'' (LeftCosets.mk _ _ d.1, (Projectivization.mk ℂ d.2.1 (posV_val_ne_zero d.2) : PLv G v β))

theorem orbOfDat_eq_of_same {a b : Dat G v β} (h : Same G v β x t hx Kf K' a b) :
    orbOfDat G v β x t hx Kf K' a = orbOfDat G v β x t hx Kf K' b := by
  obtain ⟨g, k, c, hk1, hk2, hc, h1, h2⟩ := h
  symm
  apply Quotient.sound
  refine ⟨g, Prod.ext ?_ ?_⟩
  · change g • LeftCosets.mk ((toAfF G β x t hx).prod (toP1 G β)) (Kf.prod K') a.1 = LeftCosets.mk _ _ b.1
    rw [LeftCosets.smul_mk, LeftCosets.mk_eq_mk, h1, MonoidHom.prod_apply, inv_mul_cancel_left]
    exact Subgroup.mem_prod.2 ⟨hk1, hk2⟩
  · change Projectivization.map (Matrix.toLin' (toV G v β g : Matrix (Fin G.n) (Fin G.n) ℂ))
      (toV_injective G v β g) (Projectivization.mk ℂ a.2.1 (posV_val_ne_zero a.2)) =
      Projectivization.mk ℂ b.2.1 (posV_val_ne_zero b.2)
    rw [Projectivization.map_mk, Projectivization.mk_eq_mk_iff']
    refine ⟨c⁻¹, ?_⟩
    rw [h2, smul_smul, inv_mul_cancel₀ hc, one_smul, Matrix.toLin'_apply]

def DatWt (f : G.GAf → ℂ) (f' : Gr G 1 → ℂ) (d : Dat G v β) : Prop :=
  ∃ y : grp G β, FixL G v β y d.2.1 ∧
    f (d.1.1⁻¹ * toAfF G β x t hx y * d.1.1) * f' (d.1.2⁻¹ * toP1 G β y * d.1.2) ≠ 0

theorem datWt_iff_of_same {f : G.GAf → ℂ} {f' : Gr G 1 → ℂ} (hf : ∀ k ∈ Kf, ∀ g, f (k⁻¹ * g * k) = f g)
    (hf' : ∀ k ∈ K', ∀ g, f' (k⁻¹ * g * k) = f' g) {a b : Dat G v β} (h : Same G v β x t hx Kf K' a b) :
    DatWt G v β x t hx f f' a ↔ DatWt G v β x t hx f f' b := by
  obtain ⟨g, k, c, hk1, hk2, hc, h1, h2⟩ := h
  have e1 : ∀ y : grp G β, b.1.1⁻¹ * toAfF G β x t hx (g * y * g⁻¹) * b.1.1 =
      k.1⁻¹ * (a.1.1⁻¹ * toAfF G β x t hx y * a.1.1) * k.1 := by
    intro y; rw [h1]; simp only [Prod.fst_mul, map_mul, map_inv]; group
  have e2 : ∀ y : grp G β, b.1.2⁻¹ * toP1 G β (g * y * g⁻¹) * b.1.2 =
      k.2⁻¹ * (a.1.2⁻¹ * toP1 G β y * a.1.2) * k.2 := by
    intro y; rw [h1]; simp only [Prod.snd_mul, map_mul, map_inv]; group
  have efix : ∀ y : grp G β, FixL G v β (g * y * g⁻¹) b.2.1 ↔ FixL G v β y a.2.1 := by
    intro y
    rw [h2, fixL_smul_vec_iff _ _ hc]
    exact (fixL_conj_iff p G v β y g a.2.1).symm
  constructor
  · rintro ⟨y, hy, hne⟩
    refine ⟨g * y * g⁻¹, (efix y).2 hy, ?_⟩
    rwa [e1, e2, hf _ hk1, hf' _ hk2]
  · rintro ⟨y', hy', hne⟩
    obtain ⟨y, rfl⟩ : ∃ y, y' = g * y * g⁻¹ := ⟨g⁻¹ * y' * g, by group⟩
    refine ⟨y, (efix y).1 hy', ?_⟩
    rwa [e1, e2, hf _ hk1, hf' _ hk2] at hne

end GlobalTheory.CxUnfold
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernRealClosed
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

namespace GlobalTheory.LineForm.FirstChern

open Filter Topology GlobalTheory.HermFrame GlobalTheory.Points
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ContDiff ComplexOrder ComplexConjugate

theorem dz_mul_dzb {n : ℕ} (a b : Fin n) : ∃ ε : ℤˣ, dz a * dzb b =
    ((ε : ℤ) : ℂ) • bas n ({finSumFinEquiv (.inl a)} ∪ {finSumFinEquiv (.inr b)}) := by
  obtain ⟨ε, h⟩ := bas_mul (S := {finSumFinEquiv (.inl a)}) (T := {finSumFinEquiv (.inr b)})
    (Finset.disjoint_singleton.2 (finSumFinEquiv.injective.ne Sum.inl_ne_inr))
  exact ⟨ε, by rw [dz, dzb, ← bas_singleton, ← bas_singleton, h, Units.smul_def, Int.cast_smul_eq_zsmul ℂ]⟩

theorem coe_ofValues {n : ℕ} (α : V n → V n → ℂ) :
    (ofValues α : Alt n) = ∑ a, ∑ b, α (coordVec a) (coordVec b) • (dz a * dzb b) := by
  simp only [ofValues, AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul, sym]

theorem isType_ofValues {n : ℕ} (α : V n → V n → ℂ) : IsType 1 1 (ofValues α : Alt n) := by
  intro S hS
  rw [coe_ofValues, map_sum, Finsupp.finsetSum_apply] at hS
  obtain ⟨a, -, ha⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  rw [map_sum, Finsupp.finsetSum_apply] at ha
  obtain ⟨b, -, hb⟩ := Finset.exists_ne_zero_of_sum_ne_zero ha
  obtain ⟨ε, h⟩ := dz_mul_dzb a b
  obtain rfl : ({finSumFinEquiv (.inl a)} ∪ {finSumFinEquiv (.inr b)} : Finset (Fin (n + n))) = S := by
    by_contra hne
    rw [h] at hb
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply, if_neg hne, smul_zero,
      ne_eq, not_true_eq_false] at hb
  have := a.isLt
  constructor
  · rw [Finset.card_eq_one]
    refine ⟨finSumFinEquiv (.inl a), ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, Fin.ext_iff, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]
    omega
  · rw [Finset.card_eq_one]
    refine ⟨finSumFinEquiv (.inr b), ?_⟩
    ext i
    simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_singleton, Fin.ext_iff, finSumFinEquiv_apply_left,
      finSumFinEquiv_apply_right, Fin.val_castAdd, Fin.val_natAdd]
    omega

theorem isReal_ofValues {n : ℕ} {α : V n → V n → ℂ} (hα : ∀ ξ η, conj (α ξ η) = -α η ξ) :
    IsReal (ofValues α : Alt n) := by
  intro S
  have h1 (a b : Fin n) : swap (dz a * dzb b) = -(dz b * dzb a) := by
    rw [map_mul, (swap_dz a).1, (swap_dz b).2, dz, dzb,
      eq_neg_of_add_eq_zero_right (ExteriorAlgebra.ι_add_mul_swap _ _)]
  have h2 (a b : Fin n) : conj ((bas n).repr (dz a * dzb b) S) = (bas n).repr (dz a * dzb b) S := by
    obtain ⟨ε, h⟩ := dz_mul_dzb a b
    rw [h]
    simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
    split_ifs <;> simp
  rw [coe_ofValues]
  simp only [map_sum, map_smul, h1, map_neg, Finsupp.finsetSum_apply, Finsupp.smul_apply, Finsupp.neg_apply,
    smul_eq_mul]
  simp only [map_mul (starRingEnd ℂ), h2, hα]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem conj_ddc {n : ℕ} {u : V n → ℝ} {v : V n} (hu : ContDiffAt ℝ 2 u v) (ξ η : V n) :
    conj (ddc u v ξ η) = -ddc u v η ξ := by
  have hk : conj kappa = -kappa := by
    simp [kappa, neg_div, map_ofNat]
  rw [ddc, ddc, map_mul, hk, leviForm_conj_symm hu, neg_mul]

theorem chernAt_exp_neg {n : ℕ} {u : V n → ℝ} {v : V n} (hu : ContDiffAt ℝ 2 u v) :
    chernAt (fun x => (Matrix.of fun _ _ : Unit => ((Real.exp (-u x) : ℝ) : ℂ))) v 1 = ofValues (ddc u v) := by
  have h1 (G : V n → Matrix Unit Unit ℂ) : chernAt G v 1 = ofValues (chernOne G v) := by
    unfold chernAt ofValues GlobalTheory.GoodMetric.chernPoly chernOne
    rw [Matrix.coeff_charpolyRev_eq_neg_trace, Matrix.trace_neg, neg_neg, pow_one]
    simp only [Matrix.trace, Matrix.diag, GlobalTheory.GoodMetric.curvPoly, Matrix.of_apply, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.aeval_X, ← Algebra.smul_def, mul_smul, ← Finset.smul_sum, Finset.sum_smul]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  rw [h1]
  congr 1
  funext ξ η
  rw [chernOne_line (f := fun x => Real.exp (-u x)) (Real.contDiff_exp.contDiffAt.comp v hu.neg) (Real.exp_ne_zero _)
    (Eventually.of_forall fun _ => rfl)]
  simp only [Real.log_exp, ddc, leviForm_neg]
  simp

theorem c1F_isRealForm_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ)
    (hX : IsRegVar p D) (σ : k →+* ℂ),
    ∀ L : HermLB p, (hX.atlas σ).IsRealForm 1 (fld _ (c1F hX σ L)) ∧ (hX.atlas σ).del (fld _ (c1F hX σ L)) = 0 ∧
      (hX.atlas σ).dbar (fld _ (c1F hX σ L)) = 0 := by
  intro k _ X _ p D hX σ L
  have hφ : ∀ a (x : (hX.atlas σ).Pt), x.pt ∈ ptsIn p σ (L.B.U a) →
      ContDiffAt ℝ 2 (fun v => (L.φ σ).φ a (x.ch.symm v)) x.crd := by
    intro a x hx
    exact ((vInfAt_iff_cInfAt.2 (L.cInf σ a _ hx)).contDiffAt_chart x.1.1 x.2).of_le (by norm_cast)
  obtain ⟨hfr, hP⟩ := GlobalTheory.T.chernForms_frame_independent_closed (hX.atlas σ) (ι := Unit) (fun a => ptsIn p σ (L.B.U a)) (fun _ => isOpen_ptsIn _)
    (fun y => ⟨_, mem_pick L.isLB y⟩) (fun a b y => Matrix.of fun _ _ => gv p σ L.B a b y)
    (fun a b _ _ c => (AlgChart.holo c _ _).mono fun _ hv => ⟨hv.1, mem_ptsIn_inf.2 ⟨hv.2.1, hv.2.2⟩⟩)
    (fun a y => Matrix.of fun _ _ => ((Real.exp (-(L.φ σ).φ a y) : ℝ) : ℂ))
    (fun a => hX.smoothOn fun y hy _ _ => (vInfAt_iff_cInfAt.2 (L.cInf σ a y hy)).comp_contDiff
      (Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_neg)))
    (fun a y _ => by
      have : (Matrix.of fun _ _ : Unit => ((Real.exp (-(L.φ σ).φ a y) : ℝ) : ℂ)) =
          Matrix.diagonal fun _ => ((Real.exp (-(L.φ σ).φ a y) : ℝ) : ℂ) := by
        ext; simp
      rw [this, Matrix.posDef_diagonal_iff]
      exact fun _ => Complex.zero_lt_real.2 (Real.exp_pos _))
    (fun a b y hy => by
      ext
      have h0 : 0 < ‖gv p σ L.B a b y‖ ^ 2 := by have := gv_ne_zero hy.1 hy.2; positivity
      rw [(L.φ σ).trans a b y hy.1 hy.2, neg_sub, sub_eq_add_neg, Real.exp_add, Real.exp_log h0]
      simp only [chg, Matrix.mul_apply, Matrix.of_apply, Matrix.transpose_apply, Matrix.conjTranspose_apply,
        Fintype.sum_unique, Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', Complex.star_def]
      ring) 1
  obtain ⟨h1, h2, h3⟩ := hP (fld _ (c1F hX σ L)) fun a x hx => by
    rw [hfr a _ x hx (mem_pick (L.φ σ).isLB x.pt)]
    exact congrArg Subtype.val (chernAt_exp_neg (hφ _ x (mem_pick _ _))).symm
  exact ⟨⟨h1, fun x => ⟨isType_ofValues _, isReal_ofValues (conj_ddc (hφ _ x (mem_pick _ _)))⟩⟩, h2, h3⟩

end GlobalTheory.LineForm.FirstChern
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleCurvatureAtPointStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_curvature_at_point : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (σ : k →+* ℂ) (v : CxPts p σ → ℝ),
    GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ y : CxPts p σ, ∃ (c : AlgChart p σ (d + 1)) (G : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (s : Bool)
      (O : Set (ReciprocityTheory.L2DbarEstimates.V (d + 1))), y ∈ c.e.source ∧ IsOpen O ∧ c.e y ∈ O ∧ O ⊆ c.e.target ∧
      ContinuousOn (fun z => G (GlobalTheory.LineCos.base z)) O ∧
      ∀ z ∈ O, (G (GlobalTheory.LineCos.base z)).PosDef ∧
        v (c.e.symm z) = GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base z)) (GlobalTheory.LineCos.fib z) := by
  first | exact @GlobalTheory.LineChart.exists_chart_cosSq | exact GlobalTheory.LineChart.exists_chart_cosSq | (intros; apply GlobalTheory.LineChart.exists_chart_cosSq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointsIrreducibleConnectedStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_points_irreducible_connected : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → ∀ (L : Type) [Field L] (q₁ q₂ : Spec (CommRingCat.of L) ⟶ Y), q₁ ≫ π = q₂ ≫ π → ∃ (T : Scheme.{0}) (t₁ t₂ : Spec (CommRingCat.of L) ⟶ T) (f : T ⟶ Y), IrreducibleSpace T ∧ t₁ ≫ f = q₁ ∧ t₂ ≫ f = q₂ := by
  first | exact @GlobalTheory.FlagConnect.exists_irreducible_through | exact GlobalTheory.FlagConnect.exists_irreducible_through | (intros; apply GlobalTheory.FlagConnect.exists_irreducible_through <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellPointsExistsUniqueUnitriangular
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2

theorem det_upU {K : Type} [Field K] {s : ℕ} (y : Low s → K) : (upU y).det = 1 := by
  have hb : (upU y).BlockTriangular id := fun a b (hab : b < a) => by
    simp only [upU, Matrix.of_apply, dif_neg (not_lt.2 hab.le), if_neg (ne_of_gt hab)]
  rw [Matrix.det_of_upperTriangular hb]
  exact Finset.prod_eq_one fun a _ => by simp [upU]

theorem pts_of {F : Type} [Field F] {X Y : Var F} {ι : Type} [Fintype ι] {m : ι → ℕ} {E : Fr (ratOf X) m 0}
    {E' : Fr (ratOf Y) m m} {φ : X.Fn →ₐ[F] Y.Fn} {f : Y.X ⟶ X.X} (hR : Refines E E' φ f) {A : Mat m X.Fn}
    {u : Cell m → Y.Fn} (hg : InCell E E' φ f A u (genericPoint Y.X)) {K : Type} [Field K] (x : Sp K ⟶ X.X)
    (hA : A ∈ E.S (x (IsLocalRing.closedPoint K))) (y₀ : Cell m → K)
    (hbears : ∀ p : Sp K ⟶ Y.X, A ∈ E.S (f (p (IsLocalRing.closedPoint K))) →
      (Bears E' φ A (upM y₀) p ↔ ∃ u' : Cell m → Y.Fn, upM u' * A.map φ ∈ E'.S (p (IsLocalRing.closedPoint K)) ∧
        ∀ j, (ratOf Y).val p (u' j) = y₀ j))
    (huniq : ∀ (s : ℕ) (y y' : Low s → Y.Fn) (b : Matrix (Fin s) (Fin s) Y.Fn), (∀ i j, i < j → b i j = 0) →
      upU y = b * upU y' → y = y') :
    ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧
      ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  have hPar : Par 0 ⊤ (upM y₀) := fun τ =>
    ⟨fun _ _ => trivial, by simp [upM, det_upU], trivial, fun _ _ hi => absurd hi (Nat.not_lt_zero _)⟩
  obtain ⟨p, ⟨hpf, hpB⟩, huq⟩ := hR.lifts K x A hA (upM y₀) hPar
  have hfz : f (p (IsLocalRing.closedPoint K)) = x (IsLocalRing.closedPoint K) := by
    rw [← hpf]; rfl
  have hA' : A ∈ E.S (f (p (IsLocalRing.closedPoint K))) := hfz ▸ hA
  obtain ⟨u', hu'S, hu'v⟩ := (hbears p hA').1 hpB
  have huu : u' = u := by
    have h1 := Fr.mem_genericPoint hu'S
    have hdA : ∀ τ, (A.map φ τ).det ≠ 0 := fun τ => by
      have := Mat.det_map A φ.toRingHom τ
      rw [show A.map φ.toRingHom = A.map φ from rfl] at this
      rw [this]; exact (map_ne_zero _).2 (Fr.det_ne hg.1 τ)
    have hdu : ∀ τ, (upM u τ).det ≠ 0 := fun τ => by simp [upM, det_upU]
    have hP := (Fr.mem_iff hg.2).1 h1
    rw [Mat.mul_inv_rev, ← mul_assoc, mul_assoc (upM u'), Mat.mul_inv hdA, mul_one] at hP
    have he : upM u' = (upM u' * (upM u)⁻¹) * upM u := by rw [mul_assoc, Mat.inv_mul hdu, mul_one]
    funext ⟨τ, s⟩
    have := huniq (m τ) (fun s => u' ⟨τ, s⟩) (fun s => u ⟨τ, s⟩) ((upM u' * (upM u)⁻¹) τ)
      (fun i j hij => (hP τ).2.2.2 i j i.2 hij) (congrFun he τ)
    exact congrFun this s
  subst huu
  refine ⟨p, ⟨hpf, ⟨hA', hu'S⟩, hu'v⟩, fun p' ⟨hp'f, ⟨h1, h2⟩, hv⟩ => huq p' ⟨hp'f, (hbears p' h1).2 ⟨u', h2, hv⟩⟩⟩

theorem cell_points_existsUnique : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (K : Type) [Field K] (x : Sp K ⟶ X.X), A ∈ E.S (x (IsLocalRing.closedPoint K)) → ∀ y₀ : Cell m → K, ∃! p : Sp K ⟶ Y.X, p ≫ f = x ∧ InCell E E' φ f A u (p (IsLocalRing.closedPoint K)) ∧ ∀ j, (ratOf Y).val p (u j) = y₀ j := by
  intro F _ X Y ι _ m E E' φ f hR A u hg K _ x hA y₀
  exact pts_of hR hg x hA y₀ (fun p hp => GlobalTheory.T.bearsFlag_unitriangular_iff_mem_cell F X Y ι m E E' φ f hR A K p hp y₀)
    (fun s y y' b hb h => upU_unique_of_lower Y.Fn s y y' b hb h)

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagVarietyLiftExistsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_variety_lift_exists : ∀ (ι : Type) [Fintype ι] (N : ℕ) (T : Scheme.{0}) (g : T ⟶ Sp ℤ) (fl' : ι → Vert.Flag ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N))) N), ∃ g', Lifts g fl' g' := by
  first | exact @GlobalTheory.FlagZ.Univ.exists_lifts | exact GlobalTheory.FlagZ.Univ.exists_lifts | (intros; apply GlobalTheory.FlagZ.Univ.exists_lifts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlaggedBundleMetricGradedWeightFrameIndependentStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flaggedBundleMetric_graded_weight_frame_independent : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) (m : ι → ℕ) (E : Fr (ratOf X) m m)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ B ∈ E.S (genericPoint X.X), ∀ (y : CxPts X.str σ),
    ∀ A ∈ E.S (under y), ∀ A' ∈ E.S (under y), ∀ (x : Root m) (f : X.Fn), UnitAt (under y) ((B * A'⁻¹) x.1 x.2 x.2 / f) →
      -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2) =
        -Real.log (‖ratVal ((B * A'⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A' y x.1) x.2) := by
  first | exact @GlobalTheory.ChernCalc.grWeight_frame_indep | exact GlobalTheory.ChernCalc.grWeight_frame_indep | (intros; apply GlobalTheory.ChernCalc.grWeight_frame_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineThetaRootTwistTwistingSection
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects

noncomputable section

namespace GlobalTheory.FlatRootTwist

theorem intOff_nsmul {K : Type} [Field K] [NumberField K] {B : Finset ℕ} {ρ : HeightOneSpectrum (𝓞 K) → ℝ}
    (h : IntOff B ρ) (n : ℕ) : IntOff B (n • ρ) := by
  intro v hv
  obtain ⟨k, hk⟩ := h v hv
  refine ⟨n * k, ?_⟩
  simp [hk]

theorem twSec_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    {x : ℝ} {Z : Comp Xo c} {G G' : WTZ E} (hG : G = G') (s : TwSec U x Z G) :
    ∃ t : TwSec U x Z G', t.lo = s.lo ∧ t.degLo = s.degLo := by
  subst hG
  exact ⟨s, rfl, rfl⟩

theorem flat_root_twist : GlobalTheory.Published.AbelianDeRham → ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → FlatExists U (xiR D) → UnramPts Xo c (badPrimes H l) → ∀ (w : Psi H → ℤ) (m : ℕ), (∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m), IntOff (badPrimes H l) t.lo ∧ (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) ≤ t.degLo) ∧ ∀ (u : GlobalTheory.AllWt.Weight Dw) (n : ℤ), (∀ Z : Comp Xo c, GoodOn U (xiR D) V dict Z (wtOf Dw u n) → GoodOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankOn U Z (wtOf Dw (u + parWt Dw w) (n + m)) = rankOn U Z (wtOf Dw u n) ∧ degOn U (xiR D) V dict Z (wtOf Dw u n) + (rankOn U Z (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m))) ∧ (GoodW U (xiR D) V dict (wtOf Dw u n) → GoodW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankW U (wtOf Dw (u + parWt Dw w) (n + m)) = rankW U (wtOf Dw u n) ∧ degW U (xiR D) V dict (wtOf Dw u n) + (rankW U (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m))) := by
  intro _ D H Dw l Xo c r U V dict hC hF hpq hg hflat hB w m
  have hU : ∀ σ, GoodEmb c σ → IsUnf (U σ) := fun σ hσ => (hC.2 σ hσ).1
  have hξ : ∀ σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D :=
    fun σ hσ => (hC.2 σ hσ).2.2.2
  obtain ⟨hK, hroot⟩ :=
    GlobalTheory.KeyRootTw.exists_twSec_keyRoot _ H Dw l Xo c r U (xiR D) hU hξ hF hpq hg hB

  set b : ℝ := (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) -
    (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) *
      (Real.log (2 * Real.pi) / 2 + lrd D.host.E) with hb

  have hW : wtOf Dw (parWt Dw w) 0 + m • wtOf Dw 0 1 = wtOf Dw (parWt Dw w) m := by
    rw [GlobalTheory.CompHt.nsmul_wtOf, ← wtOf_add]
    simp
  have hsec : ∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m),
      IntOff (badPrimes H l) t.lo ∧ b ≤ t.degLo := by
    intro Z
    obtain ⟨t₁, h₁I, -, h₁d⟩ :=
      (GlobalTheory.FlatTwisting.twSec_of_flat _ H Dw l Xo c r U (xiR D) (badPrimes H l) hK hU hpq hB).2 hflat Z w
        (GlobalTheory.FlatLine.hasPts U hpq hg hU Z)
    obtain ⟨t₂, h₂I, h₂d⟩ := hroot Z
    have hmp := GlobalTheory.FlatTw.twSec_mul_pow _ H Dw l Xo c r U (xiR D) Z
    obtain ⟨t₃, h₃lo, h₃d⟩ := hmp.2 _ t₂ m
    obtain ⟨t₄, -, -, h₄lo, h₄d⟩ := hmp.1 _ _ t₁ t₃
    obtain ⟨t, htlo, htd⟩ := twSec_congr hW t₄
    refine ⟨t, ?_, ?_⟩
    · rw [htlo, h₄lo, h₃lo]
      exact h₁I.add (intOff_nsmul h₂I m)
    · rw [htd, h₄d, h₃d]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      have := mul_le_mul_of_nonneg_left h₂d hm
      rw [hb]
      nlinarith
  choose s hsI hsd using hsec
  have hBp : ∀ p ∈ badPrimes H l, p.Prime := fun p hp => badPrimes_prime p hp
  have hadd : ∀ (u : GlobalTheory.AllWt.Weight Dw) (n : ℤ),
      wtOf Dw u n + wtOf Dw (parWt Dw w) m = wtOf Dw (u + parWt Dw w) (n + m) :=
    fun u n => (wtOf_add u (parWt Dw w) n m).symm
  refine ⟨fun Z => ⟨s Z, hsI Z, hsd Z⟩, fun u n => ⟨fun Z hZ => ?_, fun hW' => ?_⟩⟩
  · obtain ⟨hgood, hrank⟩ := GlobalTheory.FlatTw.Good.twist_goodOn _ H Dw l Xo c r U (xiR D) D V dict Z _ (s Z)
      (wtOf Dw u n) hU (even_wtOf u n) hZ
    have hdeg := GlobalTheory.FlatTw.degOn_add_rank_mul_degLo_le _ H Dw l Xo c r U (xiR D) D V dict Z _ (s Z)
      (wtOf Dw u n) (badPrimes H l) hU (even_wtOf u n) hBp (hsI Z) hZ
    rw [hadd] at hgood hrank hdeg
    refine ⟨hgood, hrank, ?_⟩
    have hr : (0 : ℝ) ≤ (rankOn U Z (wtOf Dw u n) : ℝ) := Nat.cast_nonneg _
    have := mul_le_mul_of_nonneg_left (sub_le_sub_right (hsd Z) (logSum (badPrimes H l))) hr
    linarith
  · obtain ⟨hgood, hrank, hdeg⟩ := GlobalTheory.Proof.TwistedWeightDegree.degW_twist D H Dw l Xo c r U V dict hC _ (wtOf Dw u n) s
      (badPrimes H l) b (even_wtOf u n) hBp hsI hsd hW'
    rw [hadd] at hgood hrank hdeg
    exact ⟨hgood, hrank, hdeg⟩

end GlobalTheory.FlatRootTwist
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameCarriedDescendFiniteEtaleExtensionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frameCarried_descend_finiteEtale_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hB : Base R) (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R') (hF : FinExt ρ) (hG : IsGal ρ) (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (hS' : IsSemiAbelian G') (U' : Unif (maximalIdeal R') D' A' G') (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left) (hS : IsSemiAbelian G) (hβ : IsGrpPullback G' G (spMap ρ) β) (hact : ∀ σ, a.act σ ≫ β = β) (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁), FinExt ρ₁ → ρ₁.Etale → ∀ (V₀ : G.left.Opens) (y : G.left), y ∈ V₀ → ∀ τ : ∀ k : U'.LG.L.ι, Γ(pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀) ⊓ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ U'.LG.L.U k)ˣ, FrameAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ → (∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → ∀ f' : (pullback (G'.hom ≫ spMap ρ) (spMap ρ₁) : Scheme.{0}) ⟶ pullback (G'.hom ≫ spMap ρ) (spMap ρ₁), f' ≫ (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ≫ a.act σ → f' ≫ (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) = (pullback.snd (G'.hom ≫ spMap ρ) (spMap ρ₁)) → FrameCarriedAlong U'.LG.L (pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ((pullback.fst (G'.hom ≫ spMap ρ) (spMap ρ₁)) ⁻¹ᵁ (β ⁻¹ᵁ V₀)) τ _ (Classical.choose hP.lg) f') → ∃ V : G.left.Opens, y ∈ V ∧ ∃ T : ∀ k : U'.LG.L.ι, Γ(G'.left, β ⁻¹ᵁ V ⊓ U'.LG.L.U k)ˣ, IsFrameOver U'.LG.L (β ⁻¹ᵁ V) T ∧ ∀ (σ : Gal ρ) (h : IsPullDeg (Gal.hom σ) D'.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (Gal.hom σ))).obj G'), bc.hom.left ≫ pullback.fst G'.hom (specOf (Gal.hom σ)) = a.act σ → ∀ hP : IsPullUnif (Gal.hom σ) h bc U' U', PullOver hD h → FrameCarried U'.LG.L (β ⁻¹ᵁ V) T _ (Classical.choose hP.lg) := by
  first | exact @GlobalTheory.Mum.FrameCarried.descend_finiteEtale | exact GlobalTheory.Mum.FrameCarried.descend_finiteEtale | (intros; apply GlobalTheory.Mum.FrameCarried.descend_finiteEtale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusEndomorphismUniqueStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frobenius_endomorphism_unique : ∀ (K : Type) [Field K] [Fintype K] (A : AbVar K), IsFrob (frob A) ∧ ∀ π : End A, IsFrob π → π = frob A := by
  first | exact @GlobalTheory.AV.AbVar.frob_isFrob_unique | exact GlobalTheory.AV.AbVar.frob_isFrob_unique | (intros; apply GlobalTheory.AV.AbVar.frob_isFrob_unique <;> assumption)
end

