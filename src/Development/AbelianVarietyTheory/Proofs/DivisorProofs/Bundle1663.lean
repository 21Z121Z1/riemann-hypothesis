import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0307
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0451
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1602
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1635
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1636
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1268
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1631
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.EigenspaceCyclicDensity.LowKMultOneP
import CompanionTheory.HarishChandraModules.LowKTypeMultiplicity.DiscreteSeriesCharacters.DiscreteSeriesInfinitesimalCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HolomorphicDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HarishChandraModulesIndefiniteUnitaryGroup
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSubOfIsForm
section
set_option autoImplicit false

noncomputable section

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder ENNReal
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.CxForm.HolAtlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

def reDens (α : A.Fld) (i : A.ι) (v : V n) : ℝ := (dens (A.loc α i v)).re

theorem loc_sub (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α - β) i v = A.loc α i v - A.loc β i v := by
  unfold loc; split_ifs
  · rfl
  · exact (sub_zero 0).symm

theorem dens_sub' (x y : Alt n) : dens (x - y) = dens x - dens y := by
  simp only [dens, map_sub, Finsupp.sub_apply, sub_div]

theorem reDens_sub (α β : A.Fld) (i : A.ι) (v : V n) : A.reDens (α - β) i v = A.reDens α i v - A.reDens β i v := by
  simp only [reDens, loc_sub, dens_sub', Complex.sub_re]

theorem reDens_compat {α : A.Fld} (hα : A.IsForm α) (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source)
    (hj : y ∈ (A.e j).source) :
    A.reDens α i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * A.reDens α j (A.e j y) := by
  have h1 := A.loc_crd α (⟨(i, y), hi⟩ : A.Pt)
  have h2 := A.loc_crd α (⟨(j, y), hj⟩ : A.Pt)
  have h3 := hα.compat (⟨(i, y), hi⟩ : A.Pt) ⟨(j, y), hj⟩ rfl
  simp only [reDens]
  erw [h1, h2, h3, GlobalTheory.T.topDegreeDensity_pullback_eq_normSq_det_mul]
  rw [Complex.re_ofReal_mul]
  rfl

theorem continuousOn_reDens {α : A.Fld} (hα : A.IsForm α) (i : A.ι) :
    ContinuousOn (A.reDens α i) (A.e i).target := by
  have := (hα.smooth i Finset.univ).continuousOn
  exact Complex.continuous_re.comp_continuousOn (this.div_const _)

theorem aemeasurable_ofReal_chart [MeasurableSpace M] (e : OpenPartialHomeomorph M (V n)) (r : V n → ℝ)
    (hr : ContinuousOn r e.target) :
    AEMeasurable (fun v => ENNReal.ofReal (r (e (e.symm v)))) (volume.restrict (e.target ∩ e.symm ⁻¹' univ)) := by
  rw [preimage_univ, inter_univ]
  have h := (ENNReal.continuous_ofReal.comp_continuousOn hr).aemeasurable (μ := volume) e.open_target.measurableSet
  refine h.congr ((ae_restrict_iff' e.open_target.measurableSet).2 (Filter.Eventually.of_forall fun v hv => ?_))
  simp [e.right_inv hv]

theorem ofReal_compat (r : A.ι → V n → ℝ)
    (hc : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y))
    (i j : A.ι) (y : M) (hi : y ∈ (A.e i).source) (hj : y ∈ (A.e j).source) :
    ENNReal.ofReal (r i (A.e i y)) =
      ENNReal.ofReal (‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2) * ENNReal.ofReal (r j (A.e j y)) := by
  rw [hc i j y hi hj, ENNReal.ofReal_mul (by positivity)]

theorem glueMeas_add_three [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] (r₁ r₂ r₃ : A.ι → V n → ℝ)
    (hr₁ : ∀ i, ContinuousOn (r₁ i) (A.e i).target) (hr₂ : ∀ i, ContinuousOn (r₂ i) (A.e i).target)
    (hc₁ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₁ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₁ j (A.e j y))
    (hc₂ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₂ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₂ j (A.e j y))
    (hc₃ : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      r₃ i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r₃ j (A.e j y)) :
    ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)) +
      ENNReal.ofReal (r₃ i (A.e i y))) univ =
    ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) univ +
      ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₂ i (A.e i y))) univ +
      ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (r₃ i (A.e i y))) univ := by
  have c₁ := A.ofReal_compat r₁ hc₁
  have c₂ := A.ofReal_compat r₂ hc₂
  have c₃ := A.ofReal_compat r₃ hc₃
  rw [ChartGlue.glueMeas_add_of_compat_on A.e A.holo A.cover MeasurableSet.univ
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i y => ENNReal.ofReal (r₃ i (A.e i y)))
      (fun i j y _ hi hj => by rw [c₁ i j y hi hj, c₂ i j y hi hj, mul_add])
      (fun i j y _ hi hj => c₃ i j y hi hj)
      (fun i => (aemeasurable_ofReal_chart (A.e i) _ (hr₁ i)).add (aemeasurable_ofReal_chart (A.e i) _ (hr₂ i))),
    ChartGlue.glueMeas_add_of_compat_on A.e A.holo A.cover MeasurableSet.univ
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) (fun i y => ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i j y _ hi hj => c₁ i j y hi hj) (fun i j y _ hi hj => c₂ i j y hi hj)
      (fun i => aemeasurable_ofReal_chart (A.e i) _ (hr₁ i))]

theorem ofReal_posNeg (x y : ℝ) :
    ENNReal.ofReal (x - y) + ENNReal.ofReal (-x) + ENNReal.ofReal y =
      ENNReal.ofReal (-(x - y)) + ENNReal.ofReal x + ENNReal.ofReal (-y) := by
  have m : ∀ t : ℝ, ENNReal.ofReal t = ENNReal.ofReal (max t 0) := fun t => by
    rcases le_total t 0 with h | h
    · simp [h, ENNReal.ofReal_of_nonpos h]
    · simp [h]
  have k : max (x - y) 0 + max (-x) 0 + max y 0 = max (-(x - y)) 0 + max x 0 + max (-y) 0 := by
    simp only [max_def]; split_ifs <;> linarith
  rw [m (x - y), m (-x), m y, m (-(x - y)), m x, m (-y),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
    ← ENNReal.ofReal_add (by positivity) (le_max_right _ _), k]

theorem integral_sub [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    (α β : A.Fld) (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.integral (α - β) = A.integral α - A.integral β := by
  have hF := A.reDens_compat hα
  have hG := A.reDens_compat hβ
  have cF := A.continuousOn_reDens hα
  have cG := A.continuousOn_reDens hβ

  let lin (c d : ℝ) : A.ι → V n → ℝ := fun i v => c * A.reDens α i v + d * A.reDens β i v
  have hlin (c d : ℝ) : ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
      lin c d i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * lin c d j (A.e j y) := by
    intro i j y hi hj
    simp only [lin, hF i j y hi hj, hG i j y hi hj]
    ring
  have clin (c d : ℝ) (i : A.ι) : ContinuousOn (lin c d i) (A.e i).target :=
    (continuousOn_const.mul (cF i)).add (continuousOn_const.mul (cG i))
  let P (c d : ℝ) : ℝ≥0∞ := ChartGlue.glueMeas A.e (fun i y => ENNReal.ofReal (lin c d i (A.e i y))) univ
  have fin (c d : ℝ) : P c d ≠ ∞ :=
    GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn A.e A.cover A.holo (lin c d) (clin c d) (hlin c d)
  have part_eq (γ : A.Fld) (ε : ℤˣ) (c d : ℝ) (h : ∀ i v, ((ε : ℤ) : ℝ) * A.reDens γ i v = lin c d i v) :
      A.part γ ε univ = P c d := by
    simp only [part, P]
    congr 2
    funext i y
    rw [← h]
    rfl
  have e1 := part_eq (α - β) 1 1 (-1) fun i v => by simp [lin, reDens_sub]; ring
  have e2 := part_eq (α - β) (-1) (-1) 1 fun i v => by simp [lin, reDens_sub]; ring
  have e3 := part_eq α 1 1 0 fun i v => by simp [lin]
  have e4 := part_eq α (-1) (-1) 0 fun i v => by simp [lin]
  have e5 := part_eq β 1 0 1 fun i v => by simp [lin]
  have e6 := part_eq β (-1) 0 (-1) fun i v => by simp [lin]
  have key : P 1 (-1) + P (-1) 0 + P 0 1 = P (-1) 1 + P 1 0 + P 0 (-1) := by
    simp only [P]
    rw [← A.glueMeas_add_three _ _ _ (clin _ _) (clin _ _) (hlin _ _) (hlin _ _) (hlin _ _),
      ← A.glueMeas_add_three _ _ _ (clin _ _) (clin _ _) (hlin _ _) (hlin _ _) (hlin _ _)]
    congr 2
    funext i y
    have := ofReal_posNeg (A.reDens α i (A.e i y)) (A.reDens β i (A.e i y))
    simp only [lin]
    convert this using 3 <;> ring_nf
  have key' := congrArg ENNReal.toReal key
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨fin _ _, fin _ _⟩) (fin _ _),
    ENNReal.toReal_add (fin _ _) (fin _ _),
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨fin _ _, fin _ _⟩) (fin _ _),
    ENNReal.toReal_add (fin _ _) (fin _ _)] at key'
  simp only [integral, Measure.real, e1, e2, e3, e4, e5, e6]
  linarith

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory.CxForm.HolAtlas

theorem integral_sub_of_isForm : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld),
    A.IsForm α → A.IsForm β → A.integral (α - β) = A.integral α - A.integral β :=
  fun A α β hα hβ => A.integral_sub α β hα hβ

end GlobalTheory.CxForm.HolAtlas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagCh2FlagPull
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB

namespace GlobalTheory.FlagPull

open VMetric

theorem isFlagCh2_flag_pull : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) [IsIntegral X] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsArithVar p 1 → IsArithVar q 1 → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (E : X.Modules) (r : ℕ) (h : VMetric p E r) (H : h.IsCInf) (fl : Vert.Flag E r) (a : ℝ), VMetric.IsFlagCh2 H fl a ↔ VMetric.IsFlagCh2 (H.pull π hπ) (fl.pull π) (π.residueDegree (genericPoint Y) * a) := by
  intro hA k _ X p _ Y _ q hp hq π hπ hg hd E r h H fl a
  set d := π.residueDegree (genericPoint Y) with hd'
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₀ : (d : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hd
  have hdE₁ : (d : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top d
  have hm := fun i σ => bcMeas_pullStep hp hq π hπ hg hd H fl i σ
  have hfin : h.FlagBcFinite fl ↔ (h.pull π hπ).FlagBcFinite (fl.pull π) := by
    have key (x : ENNReal) : x ≠ ⊤ ↔ (d : ENNReal) * x ≠ ⊤ := by
      simp [ENNReal.mul_eq_top, hdE₀, hdE₁]
    refine forall_congr' fun i => forall_congr' fun σ => ?_
    rw [hm i σ]
    exact key _
  have := hp.finite_emb
  have := Fintype.ofFinite (k →+* ℂ)
  have hbc : (h.pull π hπ).flagBc (fl.pull π) = d * h.flagBc fl := by
    rw [flagBc, flagBc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [bcInt, bcInt, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [hm i σ, ENNReal.toReal_mul, ENNReal.toReal_natCast]
  have hx : ∀ (i : Fin r) (x : ℝ), (grLB fl i H).IsSelfInter x →
      (grLB (fl.pull π) i (H.pull π hπ)).IsSelfInter (d * x) := fun i x hx =>
    (GlobalTheory.T.graded_metric_pullback_isometric k X Y p q E r h H fl π hπ i).symm.isSelfInter hq ((hA.arProj k X Y p q 1 hp hq π hπ hg hd).1 _ x hx)
  refine ⟨?_, ?_⟩
  · rintro ⟨h₁, x, h₂, rfl⟩
    refine ⟨hfin.1 h₁, fun i => d * x i, fun i => hx i _ (h₂ i), ?_⟩
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [mul_div_assoc]
  · rintro ⟨h₁, x', h₂, e⟩
    choose x hx₀ using fun i => exists_isSelfInter hA hp (grLB fl i H)
    refine ⟨hfin.2 h₁, x, hx₀, mul_left_cancel₀ hd0 (e.trans ?_)⟩
    have e' (i) : x' i = d * x i := (h₂ i).unique hq (hx i _ (hx₀ i))
    rw [hbc, mul_sub, Finset.mul_sum]
    simp only [e', mul_div_assoc]

end GlobalTheory.FlagPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFormMulStatement
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isForm_mul_of_isForm_of_isForm : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α β : A.Fld), A.IsForm α → A.IsForm β → A.IsForm (α * β) := by
  first | exact @GlobalTheory.CxForm.FormMul.isForm_mul | exact GlobalTheory.CxForm.FormMul.isForm_mul | (intros; apply GlobalTheory.CxForm.FormMul.isForm_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyOfDegreeTorsionCoprimeIdealsProductStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIsogenyOfDegree_torsion_coprime_ideals_product : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (O : Type) [CommRing O] (ρ : ReciprocityTheory.ChartRestriction.G.Out.RingAct A O) (𝔞 𝔟 : Ideal O), 𝔞 ⊔ 𝔟 = ⊤ → ∀ (K₁ K₂ K₃ : Over S) (i₁ : K₁ ⟶ A) (i₂ : K₂ ⟶ A) (i₃ : K₃ ⟶ A), Mono i₁ → Mono i₂ → Mono i₃ → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₁ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔞 x) → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₂ x ↔ GlobalTheory.IwLevel.KilledBy ρ 𝔟 x) → (∀ (T : Over S) (x : T ⟶ A), GlobalTheory.IwLevel.InSub i₃ x ↔ GlobalTheory.IwLevel.KilledBy ρ (𝔞 * 𝔟) x) → ∀ (d e : ℕ), 0 < e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₃) (d * e) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₂) e → GlobalTheory.IwLevel.IsIsogDeg (toUnit K₁) d := by
  first | (exact @GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime) | (exact GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime) | (intros; apply GlobalTheory.IwLevel.CoprimeTors.isIsogDeg_of_coprime  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKSIffKsRel
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.TangentOrigin GlobalTheory.Vanishing
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag psiSet TIx IsTanFrame)
open GlobalTheory.AllWt (exOf)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (dimFlag Dw))

abbrev ksOpen (i : M.K.bundle.ι) (k : X.F.J) : M.X.Opens :=
  M.off ⊓ (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)

def KSRel (i : M.K.bundle.ι) (k : X.F.J) {K : Type} [Field K] (z : Sp K ⟶ M.X) (x : K) : Prop :=
  ∀ [Algebra c.F K] (P Q : FrPt Xo c K) (t : Ix Dw → Kˣ) (v : TIx Dw (psiSet H) → FrPt Xo c (DualNumber K))
    (zv : TIx Dw (psiSet H) → (Sp (DualNumber K) ⟶ M.X)) (O : M.X.Opens) (hO : O ≤ M.K.bundle.U i)
    (g : Fin (dimFlag Dw) → Γ(M.X, O)) (hz : ⊤ ≤ z ⁻¹ᵁ O) (hzv : ∀ b, ⊤ ≤ zv b ⁻¹ᵁ O)
    (hk : ⊤ ≤ (z ≫ toFlag M) ⁻¹ᵁ X.F.U k),
    X.F.ChartFr k (z ≫ toFlag M) hk Q → FrBor t Q P → IsTanFrame (psiSet H) P v →
    (∀ b, zv b ≫ toFlag M = X.ptY (v b)) →
    x * (Matrix.of fun a b =>  (evalPt (zv (tanOrd Dw b)) O (hzv _) (g a)).snd).det =
      (∏ ix, t ix ^ exOf Dw (FlagTan.kap Dw) 0 ix).val * evalPt z O hz (M.K.jacobian i hO g)

theorem isKS_iff_ksRel (ω : H0 M.str (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) M.off) :
    IsKS M ω ↔ ∀ (K : Type) [Field K] (z : Sp K ⟶ M.X) (i : M.K.bundle.ι) (k : X.F.J) (ho : ⊤ ≤ z ⁻¹ᵁ M.off)
      (hi : ⊤ ≤ z ⁻¹ᵁ (LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)).U (i, flagIdx M _ k)),
      KSRel M i k z (H0.val (B := LB.div M.K.bundle ((L₀ X Z (FlagTan.kap Dw)).pull M.σ)) z (i, flagIdx M _ k) ho hi ω) :=
  ⟨fun h K _ z i k ho hi _ P Q t v zv O hO g hz hzv hk hQ ht hv hl =>
      h K P Q t v z zv i k O hO g hz hzv hk ho hi hQ ht hv hl,
    fun h K _ _ P Q t v z zv i k O hO g hz hzv hk ho hi hQ ht hv hl =>
      h K z i k ho hi P Q t v zv O hO g hz hzv hk hQ ht hv hl⟩

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsKerTorusExtension
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.CurveRootGeometry GlobalTheory.NeronCurve GlobalTheory.SS GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusPart

def GoodCover {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (u : splitTorus S X ⟶ G) : Prop :=
  ∀ x : G.left, ∃ V, x ∈ V ∧ GoodOpen u V

def IsKer {S : Scheme.{0}} {T G B : Over S} [GrpObj G] [GrpObj B] (u : T ⟶ G) (q : G ⟶ B) : Prop :=
  IsMonHom q ∧ Flat q.left ∧ Surjective q.left ∧ QuasiCompact q.left ∧ IsPullback u (toUnit _) q η[B]

def TorPol {O : Type} [CommRing O] (c : O →+* O) {S : Scheme.{0}} {G : Over S} [GrpObj G] (i : OAct O G) {X : Type}
    [AddCommGroup X] (u : splitTorus S X ⟶ G) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∃ (G' : Over (Sp K)) (_ : GrpObj G') (i' : OAct O G') (φ : G'.left ⟶ G.left) (u' : splitTorus (Sp K) X ⟶ G')
    (P : Out.PolAV (Sp K)) (q : G' ⟶ P.A) (j : OAct O P.A),
    IsActPull i' i x φ ∧ TorusCompat x φ u' u ∧ IsKer u' q ∧ (∀ a, i'.act a ≫ q = q ≫ j.act a) ∧ IsRosati c P j

def QFin {S : Scheme.{0}} (Z : Over S) : Prop :=
  Flat Z.hom ∧ LocallyOfFiniteType Z.hom ∧ QuasiCompact Z.hom ∧ LocallyQuasiFinite Z.hom

def RatOver {S : Scheme.{0}} (Z : Over S) {K : Type} [Field K] (x : Sp K ⟶ S) : Prop :=
  ∀ (Ω : Type) [Field Ω] (β : K →+* Ω) (y : Sp Ω ⟶ Z.left), y ≫ Z.hom = spMap β ≫ x →
    ∃ y₁ : Sp K ⟶ Z.left, y₁ ≫ Z.hom = x ∧ spMap β ≫ y₁ = y

def WtGeneric : Prop :=
  ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (X : Type) [AddCommGroup X] (u : splitTorus S X ⟶ G),
    IsIntegral (splitTorus S X ⊗ G).left → ∀ (V : G.left.Opens) (f : Γ(G.left, V)) (χ : X) (Z : Over S)
      (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), IsDominant (lift t g).left →
      ∀ (h₁ : ⊤ ≤ ((t ≫ u) * g).left ⁻¹ᵁ V) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V),
        (((t ≫ u) * g).left.appLE _ ⊤ h₁).hom f =
          t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom f → Wt u V f χ

theorem isKer_of_isQuot {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsQuot u q) : IsKer u q :=
  have := h.2.2.2.2.1
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, inferInstance, h.2.2.2.2.2.1⟩

theorem isKer_torusExtension {K : Type} [Field K] {G : Over (Sp K)} [GrpObj G] (T : TorusExtension G) :
    letI := T.addCommGroup; letI := T.grpB; IsKer T.i T.q :=
  ⟨T.q_hom, T.q_flat, T.q_surjective, T.q_quasiCompact, T.isKernel⟩

theorem IsKer.comp_iso {S : Scheme.{0}} {T G B B' : Over S} [GrpObj G] [GrpObj B] [GrpObj B'] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsKer u q) (e : B ≅ B') (he : IsMonHom (q ≫ e.hom)) : IsKer u (q ≫ e.hom) := by
  obtain ⟨h₁, h₂, h₃, h₄, h₅⟩ := h
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).map e.hom))
  refine ⟨he, by rw [Over.comp_left]; infer_instance, by rw [Over.comp_left]; infer_instance,
    by rw [Over.comp_left]; infer_instance, h₅.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _) e (by simp) (by simp)
      (by simp) ?_⟩
  rw [Iso.refl_hom, Category.id_comp, ← IsMonHom.one_hom q, Category.assoc, IsMonHom.one_hom]

theorem IsKer.baseChange {S S' : Scheme.{0}} {f : S' ⟶ S} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G]
    [GrpObj B] {G' B' : Over S'} [GrpObj G'] [GrpObj B'] {φ : G'.left ⟶ G.left} {ψ : B'.left ⟶ B.left}
    (hφ : IsGrpPullback G' G f φ) (hψ : IsGrpPullback B' B f ψ) {u : splitTorus S X ⟶ G} {u' : splitTorus S' X ⟶ G'}
    (hT : TorusCompat f φ u' u) {q : G ⟶ B} (h : IsKer u q) :
    ∃ q' : G' ⟶ B', IsKer u' q' ∧ IsPullback φ q'.left q.left ψ := by
  obtain ⟨e, he, heF⟩ := grpPullback_iso hφ (isGrpPullback_pullback G f)
  obtain ⟨d, hd, hdF⟩ := grpPullback_iso (isGrpPullback_pullback B f) hψ
  obtain ⟨_, _, _, _, h₅⟩ := h
  have sq := isPullback_pullback_map_left f q
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S').map e.hom))
  have hi : u' ≫ e.hom = (SplitTorus.bcIso f X).hom ≫ (Over.pullback f).map u := by
    refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have a := (isPullback_pullback_map_left f u).w
    have b := SplitTorus.bcIso_hom_fst f X
    exact ((Category.assoc _ _ _).trans ((congrArg (u'.left ≫ ·) heF).trans (torusCompat_iff.1 hT).symm)).trans
      ((congrArg (· ≫ u.left) b.symm).trans ((Category.assoc _ _ _).trans
        ((congrArg (_ ≫ ·) a).trans (Category.assoc _ _ _).symm)))
  have hk : IsPullback u' (toUnit _) (e.hom ≫ (Over.pullback f).map q) (η[(Over.pullback f).obj B]) := by
    refine (isPullback_kernel_baseChange f h₅).of_iso (SplitTorus.bcIso f X).symm e.symm (Iso.refl _)
      (Iso.refl _) ?_ (toUnit_unique _ _) (by simp) (by simp)
    rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hi, Iso.inv_hom_id_assoc]
  have h₁ : Flat ((Over.pullback f).map q).left := MorphismProperty.of_isPullback (P := @Flat) sq inferInstance
  have h₂ : Surjective ((Over.pullback f).map q).left :=
    MorphismProperty.of_isPullback (P := @Surjective) sq inferInstance
  have h₃ : QuasiCompact ((Over.pullback f).map q).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have hK : IsKer u' (e.hom ≫ (Over.pullback f).map q) := ⟨inferInstance, by rw [Over.comp_left]; infer_instance,
    by rw [Over.comp_left]; infer_instance, by rw [Over.comp_left]; infer_instance, hk⟩
  refine ⟨_, hK.comp_iso d inferInstance, ?_⟩
  refine IsPullback.of_bot (v₂₁ := B'.hom) (v₂₂ := B.hom) ?_ ?_ hψ.1
  · rw [Over.w, Over.w]
    exact hφ.1
  · rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hdF, ← heF, Category.assoc]
    exact congrArg (_ ≫ ·) sq.w

theorem IsKer.exists_oAct {S : Scheme.{0}} {T G B : Over S} [GrpObj G] [GrpObj B] {u : T ⟶ G} {q : G ⟶ B}
    (h : IsKer u q) {O : Type} [CommRing O] (i : OAct O G) (hu : ∀ a, u ≫ i.act a ≫ q = toUnit _ ≫ η[B]) :
    ∃ j : OAct O B, ∀ a, i.act a ≫ q = q ≫ j.act a := by
  obtain ⟨_, _, _, _, h₅⟩ := h
  have := i.hom
  have : Epi q := FlatQuotient.epi_of_flat_surjective q
  choose fB hm hfB using fun a => FlatQuotient.exists_desc q u (i.act a ≫ q) h₅ (hu a)
  refine ⟨⟨fB, hm, ?_, fun a b => ?_, fun a b => ?_⟩, fun a => (hfB a).symm⟩
  · rw [← cancel_epi q, hfB, i.one, Category.comp_id, Category.id_comp]
  · rw [← cancel_epi q, hfB, i.mul, Category.assoc, ← hfB, reassoc_of% hfB]
  · rw [← cancel_epi q, hfB, MonObj.comp_mul, hfB, hfB, i.add, MonObj.mul_comp]

theorem exists_isActPull {O : Type} [CommRing O] {S S' : Scheme.{0}} (f : S' ⟶ S) {G : Over S} [GrpObj G]
    [IsCommMonObj G] (i : OAct O G) : IsActPull (OAct.pullback f G i) i f (pullback.fst G.hom f) :=
  ⟨isGrpPullback_pullback G f, fun _ => pullback.lift_fst _ _ _⟩

end GlobalTheory.TorusPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackGluedQuotientKernelPairOfCoverStatement
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_gluedQuotient_kernelPair_of_cover : ∀ (S : Scheme.{0}) (𝒰 : S.OpenCover.{0}) (A H G : Over S) [GrpObj A] [GrpObj H] (i : H ⟶ A) (Q : A ⟶ G)
    (B : ∀ j, Over (𝒰.X j)) (ψ : ∀ j, (B j).left ⟶ G.left) (q : ∀ j, (Over.pullback (𝒰.f j)).obj A ⟶ B j),
    (∀ j, IsPullback (ψ j) (B j).hom G.hom (𝒰.f j)) → (∀ j, (q j).left ≫ ψ j = pullback.fst A.hom (𝒰.f j) ≫ Q.left) → (∀ j, IsPullback ((fst ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A) ≫ (Over.pullback (𝒰.f j)).map i) * snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (snd ((Over.pullback (𝒰.f j)).obj H) ((Over.pullback (𝒰.f j)).obj A)) (q j) (q j)) → IsPullback ((fst H A ≫ i) * snd H A) (snd H A) Q Q := by
  first | exact @GlobalTheory.GlueQuotPB.isPullback_translation_of_cover | exact GlobalTheory.GlueQuotPB.isPullback_translation_of_cover | (intros; apply GlobalTheory.GlueQuotPB.isPullback_translation_of_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaFunOfSmoothRealHeisenbergLevelStatement
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaFun_of_smooth_real_heisenberg_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (hψ : IsCharAF F B.ψ) (f : BBF σ JS JT ξ₀ B.ψ), Sm (rhoVF σ JS JT ξ₀ B.ψ hψ ι) f →
        (∃ U : AddSubgroup (WOF F E nS nT), IsOpen (U : Set (WOF F E nS nT)) ∧
          ∀ u ∈ U, u.map (infPartF F E) = 0 → heisOF σ JS JT ξ₀ B.ψ u f.1 = f.1) →
        IsThetaFunOF σ JS JT ξ₀ B.ψ f.1 := by
  first | exact @GlobalTheory.ThetaOfSmF.theta_of_smF | exact GlobalTheory.ThetaOfSmF.theta_of_smF | (intros; apply GlobalTheory.ThetaOfSmF.theta_of_smF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeOfFibreRank
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_degree_of_fibre_rank : ∀ (k : Type) [Field k] [IsAlgClosed k] (A : Over (Sp k)) [GrpObj A], IsAbelianScheme A →
    ∀ (φ : A ⟶ A), IsMonHom φ → IsFinite φ.left → ∀ d : ℕ,
    φ.left.finrank ((1 : Over.mk (𝟙 (Sp k)) ⟶ A).left (IsLocalRing.closedPoint k)) = d →
    GlobalTheory.IwLevel.IsIsogDeg φ d := by
  first | (exact @GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin) | (exact GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin) | (intros; apply GlobalTheory.IwLevel.isIsogDeg_of_isFinite_of_finrank_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeOfPointCount
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogeny_degree_of_point_count : ∀ {S : Scheme.{0}} (A K : Over S) (i : K ⟶ A), Mono i → IsFinite K.hom → Etale K.hom → ∀ (d : ℕ), 1 ≤ d → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Nat.card {y : Over.mk t ⟶ A // GlobalTheory.IwLevel.InSub i y} = d) → GlobalTheory.IwLevel.IsIsogDeg (toUnit K) d := by
  first | (exact @GlobalTheory.FinEtRank.isIsogDeg_of_card) | (exact GlobalTheory.FinEtRank.isIsogDeg_of_card) | (intros; apply GlobalTheory.FinEtRank.isIsogDeg_of_card <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFiniteSmoothVecOfIrreducibleUnitaryRep
section
open Matrix GlobalTheory.HolDS
open Formalism.REAL (GlRel IsUnitary IsWeight KHighest root Jm inG)
open Formalism.QuantumDeterminants (lowK IsHCParam)
open Formalism.MainNotions.S (IsURepOn IsIrredOn UJset IsKFin IsKTypeOf IsKStableOn IsDS lowKSub vNormSq)
open CompanionTheory.D.DSIC (KRel KUnit KStab IsSmMod)
open CompanionTheory.D.LK (IsKMod IsMin)
open scoped InnerProductSpace

namespace GlobalTheory.HdSmooth

theorem kFinite_smoothVec : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [Nontrivial H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UJset ε) σ → IsIrredOn (UJset ε) σ → ∀ v, IsKFin ε σ v → Formalism.L2.Theta.SmoothVec {X | inG ε X} σ v := by
  intro n ε H _ _ _ _ σ hU hI v hv
  have h := (GlobalTheory.HcPort.kFiniteVectors_analytic_indefiniteUnitary n ε H σ hU hI v hv).smoothVec (P := 1)
    (G := Formalism.REAL.Jm ε) isUnit_one (by simp)
  simpa [inG] using h

end GlobalTheory.HdSmooth
end

