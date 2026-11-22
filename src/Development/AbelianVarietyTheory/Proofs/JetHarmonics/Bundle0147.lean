import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0145
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0034
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0102
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValueAtZeroLinearCombinationIntegralSections
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenOfTop
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SurjectiveAppTop
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0105
import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0132
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0128
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Jets.CubWeilOneIffPairOne
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0088
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0004
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AddCurveStableOfIntegralGaugedFormalGroupLaw
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0079
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0146
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselDatumBothSidesAreSidesStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselDatum_both_sides_are_sides : ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (u u' : ℕ → ℝ), Q.IsType k r D.z D.π u → Q.IsType k r D.z' D.π' u' → ∃ νq νq', SideG k r D.z D.π u D.μW D.μN D.μG νq ∧ SideG k r D.z' D.π' u' D.μW' D.μN D.μG νq' := by
  first | exact @GlobalTheory.exists_sideG_both_of_isType | exact GlobalTheory.exists_sideG_both_of_isType | (intros; apply GlobalTheory.exists_sideG_both_of_isType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmEvenThetaSeriesChartCoeffIntegralStatement
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_even_theta_series_chart_coeff_integral : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → Bd 1 (hat M.ι (C ω * logS) θ) := by
  first | exact @GlobalTheory.MomOne.theta_series_integral | exact GlobalTheory.MomOne.theta_series_integral | (intros; apply GlobalTheory.MomOne.theta_series_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthBoundFromCharactersPointDatum
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS FB ev Dof)
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)
open GlobalTheory GlobalTheory.FamGerm GlobalTheory.DepthBound
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DepthFromChars

theorem depth_bound_of_chars : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → (∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ a : 𝓞 E, a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → (∀ t, τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ∃ lam : Fin (rk t) → Fin y.d → TWO.Ov y.v, ∀ i i', ∑ s, lam i s * e ⟨t, i'⟩ s = if i = i' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ c : TWO.Ov y.v, (p - 1) • y.v (c : F) = y.v (p : F) → ∀ (n : ℕ) (col : ∀ t, Fin (rk t) → Fin n), (∀ t, Function.Injective (col t)) → ∃ yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v, (∀ b, y.CharAt a p e (fun l => yy (l, b))) ∧ ∀ t (s : Fin (rk t)), y.v (((Matrix.of fun a i : Fin (s.val + 1) => yy (⟨t, Fin.castLE s.isLt a⟩, col t (Fin.castLE s.isLt i))).det : TWO.Ov y.v) : F) ≤ (s.val + 1) • y.v (c : F)) → ∀ (p : ℕ) [Fact p.Prime], ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (F : Type) [Field F] [IsAlgClosed F] [CharZero F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F] (y : FamGerm.Pt1 E H V F), letI := H.starRing; IsAdicComplete (Ideal.span {(p : TWO.Ov y.v)}) (TWO.Ov y.v) → ¬ IsUnit (p : TWO.Ov y.v) → ∀ (Dw : Datum H) (_I : TateIso Dw F (TFK (R := V) F ⟶ y.P.A.A) (fun a g => g ≫ y.P.oA.act a) (fun n g g' c => WeilIs y.P.A.A y.P.A.L n g g' (unitOn c))), ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ y.P.D.toPre.X) (Cc M₀ : ℝ), y.Red r b Cc M₀ → ∀ (a : 𝓞 E) (k : ℕ), a * star a = (p : 𝓞 E) → (∃ u u' : 𝓞 E, u * a + u' * star a = 1) → Nat.Coprime p k → ∀ (T : Type) [Fintype T] [DecidableEq T] (rk : T → ℕ) (τ : T → 𝓞 E →+* TWO.Ov y.v) (e : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v), (∀ (c : 𝓞 E) l, (dAct F y.B c).mulVec (fun i => (e l i : F)) = (τ l.1 c : F) • fun i => (e l i : F)) → ∀ (isV : T → Prop) [DecidablePred isV], (∀ t, isV t → τ t a ∈ Ideal.span {(p : TWO.Ov y.v)}) → (∀ t, ¬ isV t → IsUnit (τ t a)) → (∃ lam : (Σ t, Fin (rk t)) → Fin y.d → TWO.Ov y.v, ∀ l l', ∑ s, lam l s * e l' s = if l = l' then 1 else 0) → (∃ ε : T → 𝓞 E, ∀ t t', τ t' (ε t) - (if t = t' then 1 else 0) ∈ Ideal.span {(p : TWO.Ov y.v)}) → ∀ (n : ℕ) (S : Finset (Fin n)) (col : ∀ t, Fin (rk t) → Fin n) (m : ∀ t, Fin (rk t) → ℕ), (∀ t, Function.Injective (col t)) → (∀ t i, col t i ∈ S ↔ isV t) → ∀ D : ℕ, D = ∑ t, ∑ s : Fin (rk t), m t s * (s.val + 1) → D < p - 1 → 4 * D + 4 ≤ k → (D : ℝ) * M₀ < k → ∀ h : PS F 2 y.d, y.B.IsCanonGauge F h → ∀ ep : ℚ, y.v (p : F) = (ep : ℚ) → ∃ (s : Fin n → Fam y.P.D.toPre F k) (s' t : Fin n → Fam y.P.D.toPre F (k * p)) (f : Fin n → PS F 1 y.d) (gm : ℚ), (∀ b, NuGe y.P.D y.Q F y.v (k) (s b) 0 ∧ PullAl y.P.D F y.P.oD a k p (s b) (s' b) ∧ y.Transl (k * p) (star a) (s' b) (t b) ∧ y.Germ (k * p) (t b) (f b)) ∧ y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (FamGerm.minorsP F col m) f) = (gm : ℚ) ∧ (gm : ℝ) ≤ (D : ℝ) * ep / (p - 1) + S.card * r * Cc / (4 * k) + (D : ℝ) ^ 2 * Cc / k := by
  intro hL _ hL4 hTB hC p hp E _ _ _ H V _ _ _ F _ _ _ _ _ _ y hcomp hpu Dw I r bs Cc M₀ hred a k
    haa hcop hpk T _ _ rk τ e he isV _ hV hU ⟨lam, hlam⟩ ⟨ε, hε⟩ n S col m hcol hS D hD hDp hk hM h hh ep hep
  have hTW : TwistBCSpanStatement := twistBCSpan_of hTB
  have hVR : TWM.VRatioGtStatement := GlobalTheory.RatioVal.main
  have hUU : UUStatement := GlobalTheory.UnitBallFree.main hL.globalFns hTB
  obtain ⟨jA, jR, -, -, -, -, -, jS, jX, -, -, -, -, jB⟩ := GlobalTheory.JetRoad.jetRoad
  have hG : FamGerm.GermExSt := GlobalTheory.FamGermExist.germ_exists_unique_linear hL hL4 hTW jA jR jS jX
  have hGV : GermValSt := GlobalTheory.GermValuation.main hL hL4 hTW jA jR jS jX hG
  have hJ : JetsSt := GlobalTheory.GermJets.jets hL hL4 hTW jA jR jS jX hG
  have hP : PullGermSt := GlobalTheory.PullGerm.germ_pullback hL hL4 hTW jA jR jS jX GlobalTheory.JetRoad.rosIdSt hG
  have hE : EigGermSt := GlobalTheory.T.derivative_congruence_germ_integral_translate hL hL4 hTW jA jR jS jX GlobalTheory.JetRoad.rosIdSt jB hG
  classical
  let _ := H.starRing
  have hp' : p.Prime := hp.out
  have hp2 : 2 ≤ p := hp'.two_le
  have hpF : ((p : TWO.Ov y.v) : F) = p := map_natCast (TWO.Ov y.v).subtype p
  have hep0 : 0 < ep := by
    by_contra hle
    refine hpu (Ideal.span_singleton_eq_top.1 ((Ideal.eq_top_iff_one _).2 (mem_span_of_val_le y.v _ 1 ?_ ?_)))
    · rw [hpF]; exact_mod_cast hp'.ne_zero
    · rw [hpF, hep, OneMemClass.coe_one, y.v.map_one]
      exact_mod_cast not_lt.1 hle
  have hp1 : (0 : ℚ) < (p : ℚ) - 1 := by
    have : (2 : ℚ) ≤ p := by exact_mod_cast hp2
    linarith
  set θ : ℚ := ep / ((p : ℚ) - 1) with hθ
  have hθ0 : 0 < θ := div_pos hep0 hp1
  obtain ⟨c, hc⟩ := ExactTerm.exists_val_eq_of_nonneg y.hv hθ0.le
  obtain ⟨ω, hω1, hω⟩ := FramePull.exists_integral_frame_pullback V y.d (𝓞 E) F y.B h hh H.w0 a p haa

  let m₁ : ∀ t, Fin (rk t) → ℕ := fun t s => if isV t then m t s else 0
  let m₂ : ∀ t, Fin (rk t) → ℕ := fun t s => if isV t then 0 else m t s
  have hm : m = fun t s => m₁ t s + m₂ t s := by
    funext t s
    by_cases ht : isV t <;> simp [m₁, m₂, ht]
  have hm₁ : ∀ t, ¬ isV t → ∀ s, m₁ t s = 0 := fun t ht s => if_neg ht
  have hm₂ : ∀ t, ¬ ¬ isV t → ∀ s, m₂ t s = 0 := fun t ht s => if_pos (not_not.1 ht)
  have hDD : ∑ t, ∑ s : Fin (rk t), m₁ t s * (s.val + 1) + ∑ t, ∑ s : Fin (rk t), m₂ t s * (s.val + 1) = D := by
    rw [hD, hm]
    simp only [add_mul, Finset.sum_add_distrib]

  obtain ⟨y₁, hy₁, hy₂⟩ := hC p E H V F y hcomp hpu a haa hcop {t // isV t} (fun t => rk t.1) (fun t => τ t.1)
    (fun l => e ⟨l.1.1, l.2⟩) (fun c l => he c ⟨l.1.1, l.2⟩) (fun t => hV t.1 t.2)
    (fun t => ⟨fun i => lam ⟨t.1, i⟩, fun i i' => by simpa using hlam ⟨t.1, i⟩ ⟨t.1, i'⟩⟩)
    ⟨fun t => ε t.1, fun t t' => by simpa only [Subtype.ext_iff] using hε t.1 t'.1⟩
    ⟨c, by rw [TWO.mem_Ov, hc]; exact_mod_cast hθ0.le⟩
    (by
      change (p - 1) • y.v c = _
      rw [hc, hep, ← WithTop.coe_nsmul, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one, hθ,
        mul_div_cancel₀ _ hp1.ne'])
    n (fun t => col t.1) (fun t => hcol t.1)
  let yy : (Σ t, Fin (rk t)) × Fin n → TWO.Ov y.v := fun x =>
    if hx : isV x.1.1 then y₁ (⟨⟨x.1.1, hx⟩, x.1.2⟩, x.2) else 0
  choose s₁ s₁' t₁ c₁ f₁ r₁ h₁ hc₁ hr₁ hf₁ hf₁' using fun b => exists_eigen_column y hL hTW hVR hUU hG hGV hE Dw I r bs
    Cc M₀ hred a p k hp' (by omega) haa hcop hpk (Σ t : {t // isV t}, Fin (rk t.1)) (fun l => e ⟨l.1.1, l.2⟩)
    (fun l => y₁ (l, b)) (fun l => τ l.1.1 a) (fun l => hV _ l.1.2) (fun l => he a ⟨l.1.1, l.2⟩) (hy₁ b) h hh ω hω1 hω
  have hD₁ : ((∑ t, ∑ s : Fin (rk t), m₁ t s * (s.val + 1) : ℕ) : ℚ) * θ ≤ D * θ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega)) hθ0.le
  have hF₁ := val_eigen_columns y.v _ (fO_comp_eq y) y.B h hh H.w0 a p k hp'.ne_zero hpu hcop ω hω1 hω τ e he isV hV
    S col m₁ (fun t i ht => (hS t i).2 ht) hm₁ yy f₁ (fun b _ => hf₁ b)
    (fun b _ l hl mo => by
      simp only [yy, dif_pos hl]
      exact hf₁' b ⟨⟨l.1, hl⟩, l.2⟩ mo)
    θ ep hep
    (fun t ht s => by
      simp only [yy, dif_pos ht]
      refine (hy₂ ⟨t, ht⟩ s).trans (le_of_eq ?_)
      change (s.val + 1) • y.v c = _
      rw [hc, ← WithTop.coe_nsmul, nsmul_eq_mul, Nat.cast_succ])
    (hD₁.trans_lt (by
      have : (D : ℚ) < (p : ℚ) - 1 := by
        have h1 : D + 1 < p := by omega
        have h2 : (D : ℚ) + 1 < p := by exact_mod_cast h1
        linarith
      calc (D : ℚ) * θ < ((p : ℚ) - 1) * θ := mul_lt_mul_of_pos_right this hθ0
        _ = ep := by rw [hθ, mul_div_cancel₀ _ hp1.ne']))

  obtain ⟨g, nb, hg, hnb, hF₂⟩ := val_unit_columns y.v y.B h hh H.w0 a p k hp' hpu ω hω τ e (he a) (fun t => ¬ isV t)
    hU lam hlam Sᶜ col m₂ hcol (fun t i ht => Finset.mem_compl.2 fun h' => ht ((hS t i).1 h')) hm₂ (by omega)
  have hnbD : ∑ b, nb b ≤ D := by omega
  have hnbD' : ∀ b, nb b ≤ D := fun b =>
    (Finset.single_le_sum (f := nb) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)).trans hnbD
  choose s₂ s₂' t₂ c₂ f₂ r₂ h₂ hc₂ hr₂ hf₂ using fun b => exists_jet_column y hL hG hJ hP r bs Cc M₀ hred a p k (nb b)
    (by omega) haa (by have := hnbD' b; omega)
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_right (by exact_mod_cast hnbD' b) hred.2.1) hM) h hh ω hω (g b) (hg b)
  have hF₂' := hF₂ f₂ fun b _ => hf₂ b
  let f : Fin n → PS F 1 y.d := fun b =>
    if b ∈ S then MvPowerSeries.C (c₁ b) * (FB.toK F (f₁ b) * FB.toK F ω ^ k)
    else MvPowerSeries.C (c₂ b) * (ev (n := 1) ![y.B.actK F a] (f₂ b) * FB.toK F ω ^ k)
  have hval : y.v (y.colVal h (k * p) (fun l i => (e l i : F)) (minorsP F col m) f) ≤
      ((∑ b ∈ S, r₁ b + D * θ + ∑ b ∈ Sᶜ, r₂ b : ℚ) : WithTop ℚ) := by
    have e₁ := colValue_mul_of_disjoint_columns F _ n (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
      (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) S (minorsP F col m₁) (minorsP F col m₂)
      (fun mo hmo l b hb => by
        obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m₁ isV hm₁ hmo l b hb
        exact (hS _ i).2 hz)
      (fun mo hmo l b hb => by
        obtain ⟨hz, i, rfl⟩ := minorMonomial_support col m₂ (fun t => ¬ isV t) hm₂ hmo l b hb
        exact fun h' => hz ((hS _ i).1 h'))
    rw [← minorMonomial_add, ← hm, sum_prod_const_mul S _ (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
        (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) (fun b mo => y.B.nabVal F h H.w0 (k * p)
        (FB.toK F (f₁ b) * FB.toK F ω ^ k) (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) c₁
        (fun b hb mo => by simp only [f, if_pos hb]; exact nabVal_C_mul _ _ _ _ _ _ _ _),
      sum_prod_const_mul Sᶜ _ (fun b mo => y.B.nabVal F h H.w0 (k * p) (f b)
        (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) (fun b mo => y.B.nabVal F h H.w0 (k * p)
        (ev (n := 1) ![y.B.actK F a] (f₂ b) * FB.toK F ω ^ k) (fun l i => (e l i : F)) (MvPolynomial.monomial mo 1)) c₂
        (fun b hb mo => by simp only [f, if_neg (Finset.mem_compl.1 hb)]; exact nabVal_C_mul _ _ _ _ _ _ _ _)] at e₁
    refine (congrArg y.v e₁).trans_le ?_
    rw [y.v.map_mul, y.v.map_mul, y.v.map_mul, hF₂', add_zero, WithTop.coe_add, WithTop.coe_add]
    exact add_le_add (add_le_add (val_prod_le y.v _ _ _ fun b _ => (hc₁ b).le)
      (hF₁.trans (WithTop.coe_le_coe.2 hD₁))) (val_prod_le y.v _ _ _ fun b _ => (hc₂ b).le)
  obtain ⟨gm, hgm⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hval)
  refine ⟨fun b => if b ∈ S then s₁ b else s₂ b, fun b => if b ∈ S then s₁' b else s₂' b,
    fun b => if b ∈ S then t₁ b else t₂ b, f, gm, fun b => ?_, hgm.symm, ?_⟩
  · by_cases hb : b ∈ S
    · simp only [f, if_pos hb]; exact h₁ b
    · simp only [f, if_neg hb]; exact h₂ b
  · rw [← hgm, WithTop.coe_le_coe] at hval
    have h1 : (gm : ℝ) ≤ ∑ b ∈ S, (r₁ b : ℝ) + D * (ep / (p - 1)) + ∑ b ∈ Sᶜ, (r₂ b : ℝ) := by
      rw [hθ] at hval
      exact_mod_cast hval
    have h2 : ∑ b ∈ S, (r₁ b : ℝ) ≤ S.card * r * Cc / (4 * k) := by
      refine (Finset.sum_le_card_nsmul _ _ _ fun b _ => hr₁ b).trans (le_of_eq ?_)
      rw [nsmul_eq_mul]; ring
    have hCk : 0 ≤ Cc / k := div_nonneg hred.1 (Nat.cast_nonneg _)
    have h3 : ∑ b ∈ Sᶜ, (r₂ b : ℝ) ≤ (D : ℝ) ^ 2 * Cc / k := by
      have h4 : ∑ b ∈ Sᶜ, nb b ^ 2 ≤ D ^ 2 :=
        calc ∑ b ∈ Sᶜ, nb b ^ 2 ≤ ∑ b, nb b ^ 2 := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
          _ ≤ ∑ b, nb b * D := Finset.sum_le_sum fun b _ => by
            rw [sq]; exact Nat.mul_le_mul_left _ (hnbD' b)
          _ ≤ D ^ 2 := by rw [← Finset.sum_mul, sq]; exact Nat.mul_le_mul_right _ hnbD
      refine (Finset.sum_le_sum fun b _ => hr₂ b).trans ?_
      simp only [mul_div_assoc]
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast h4) hCk
    rw [mul_div_assoc (D : ℝ) (ep : ℝ)]
    linarith

end GlobalTheory.DepthFromChars
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.DepthTableGoodPrimeLeaf
section
set_option autoImplicit false

namespace GlobalTheory.GoodDepth

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.DIV Formalism.L2.Pj Formalism.BasicNotions NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond

theorem thl_nonneg_leaf (k l : ℕ) : 0 ≤ thl k l := by
  unfold thl
  apply Real.sSup_nonneg
  rintro t ⟨i, -, -, -, rfl⟩
  positivity

theorem err_mono_leaf (Cc C k m f w Se Se' th l T X : ℝ) (hCc : 0 < Cc) (hC : Cc ≤ C) (hk : 1 ≤ k) (hm : 1 ≤ m) (hf : 8 ≤ f)
    (hw : 0 ≤ w) (hS : Se' ≤ Se) (hS0 : 0 ≤ Se) (hth : 0 ≤ th) (hl : 0 ≤ l) :
    Cc * (Real.log k * m * w / l + f * k * Se' / l + k * th * w + if X < l then k * w / l ^ 2 else 0) ≤
      C * (Real.log k * m * w + f * k * Se) / l + C * k * w * th + T * 0 + if X < l then C * k * w / l ^ 2 else 0 := by
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk
  have hk0 : 0 ≤ k := by linarith
  have hm0 : 0 ≤ m := by linarith
  have hf0 : 0 ≤ f := by linarith
  have h1 : f * k * Se' / l ≤ f * k * Se / l :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hS (by positivity)) hl
  have hI : 0 ≤ (if X < l then k * w / l ^ 2 else 0) := by split_ifs <;> positivity
  have hR : C * (Real.log k * m * w + f * k * Se) / l + C * k * w * th + T * 0 + (if X < l then C * k * w / l ^ 2 else 0) =
      C * (Real.log k * m * w / l + f * k * Se / l + k * th * w + if X < l then k * w / l ^ 2 else 0) := by
    split_ifs <;> ring
  rw [hR]
  have h0 : 0 ≤ Real.log k * m * w / l + f * k * Se / l + k * th * w + if X < l then k * w / l ^ 2 else 0 := by
    positivity
  calc _ ≤ Cc * (Real.log k * m * w / l + f * k * Se / l + k * th * w + if X < l then k * w / l ^ 2 else 0) :=
        mul_le_mul_of_nonneg_left (by linarith) hCc.le
    _ ≤ _ := mul_le_mul_of_nonneg_right hC h0

theorem leafGood : LeafGoodSt := by
  intro C1 hC1
  obtain ⟨Cc, hCc, hnu⟩ := GlobalTheory.T.goodPlaceDepthBound_proof C1 hC1
  refine ⟨max Cc 20, ?_⟩
  intro E _ _ _ H lv Dw Xo c _ Dd K _ _ _ _ _ _ Bs Df S P _ _ oc O ι Nm N pl hC0 hE hσ hT hpr hsp hlev hstar hEx hPk hPl hj
    hN hPg tF tP
  have hCcC : Cc ≤ O.C := le_trans (le_max_left _ _) hC0
  have h20 : (20 : ℝ) ≤ O.C := le_trans (le_max_right _ _) hC0
  have hPg' := hPg
  obtain ⟨hC, hk, hm, hf, -, hSc, heta, -, -, -, pg1, pg2, -⟩ := hPg'
  have hb : 0 < O.b := Real.exp_pos _
  have hkN : 1 ≤ N.R.k := by
    have := hN.k_eq ▸ hk
    exact_mod_cast this
  refine ⟨fun l => ⟨?_, ?_⟩, fun Q hQ => ?_, fun Q _ => ?_, fun w _ hw j => ?_⟩
  · rw [hN.th_eq]; exact thl_nonneg_leaf _ _
  · rw [hN.ad_eq]
  · simp only [hN.th_eq]
    refine (GlobalTheory.T.sum_level_tail_mul_log_primes_le.2 N.R.k Q hkN hQ).trans ?_
    rw [hN.k_eq]
    exact div_le_div_of_nonneg_right h20 (Nat.cast_nonneg _)
  · simp only [hN.ad_eq, zero_mul, Finset.sum_const_zero, mul_zero]
    have : 0 ≤ O.m := by linarith
    have : 0 ≤ O.C := by linarith
    positivity
  · obtain ⟨j1, j2, jp, jq, jD, jG⟩ := hj j
    obtain ⟨t1, t2, t3, t4, t5⟩ := tP
    have hp : (Formalism.EigenvalueLevelCeiling.plc w).Prime := Formalism.EigenvalueLevelCeiling.plc_prime w
    have hw' := hw
    simp only [not_or] at hw'
    obtain ⟨n2, nq, nd, ng1, ng2⟩ := hw'
    have hF : Nm.F0 w j = N.FjP (ι j) (Formalism.EigenvalueLevelCeiling.plc w) := tF w j
    have key : ∀ v : HeightOneSpectrum (𝓞 K), Formalism.EigenvalueLevelCeiling.plc v = Formalism.EigenvalueLevelCeiling.plc w →
        O.e0 v j ≤ Nm.F0 w j + O.aE j (Formalism.EigenvalueLevelCeiling.plc w) + 1 ∧ (O.Y < (Formalism.EigenvalueLevelCeiling.plc w : ℝ) → O.e0 v j = 0) := by
      intro v hv
      have hr : resCharOf (placeBelow (K := c.F) v) = Formalism.EigenvalueLevelCeiling.plc w := (DepthTie.resChar_below (F := c.F) v).trans hv
      obtain ⟨e1, e2⟩ := GlobalTheory.T.onObj_exponent_eq_rounded_depth E H lv Dw Xo c Dd K Bs Df S P oc O ι hE hσ hpr hsp hPg v j (by rw [hv]; exact hw)
      have hM : ¬ Formalism.EigenvalueLevelCeiling.plc w ∣ lv.M := by
        intro hd
        have hl : (lv.M : ℕ) = Dd.Q.g1 * Dd.Q.g2 := hlev
        rw [hl, ← hpr.1, ← hpr.2.1] at hd
        rcases (Nat.Prime.dvd_mul hp).1 hd with h | h
        · exact ng1 ((Nat.prime_dvd_prime_iff_eq hp pg1).1 h)
        · exact ng2 ((Nat.prime_dvd_prime_iff_eq hp pg2).1 h)
      obtain ⟨-, b1, b2⟩ := hnu E H (Dw (ι j)) lv (Xo (ι j)) c hstar (hEx j) (hPk j) N (ι j) pl (Dd.aL (ι j)) (Dd.nW (ι j))
        Dd.Q.T O.b O.L (O.wt j) j1 j2 hPl jp jq jD jG (hN.wt_sum j) (hN.wt_b j) (placeBelow (K := c.F) v)
        (by rw [hr, ← t5]; exact n2) (by rw [hr, ← t3]; exact nq) (by rw [hr, ← t4]; exact nd) (by rw [hr, ← t1]; exact ng1)
        (by rw [hr, ← t2]; exact ng2) (by rw [hr]; exact hM)
      rw [hr] at b1 b2
      constructor
      · have hm' := err_mono_leaf Cc O.C O.k O.m O.f (O.wt j) O.Se (N.Sc + N.eta) (O.th (Formalism.EigenvalueLevelCeiling.plc w))
          (Formalism.EigenvalueLevelCeiling.plc w) O.T O.X2 hCc hCcC hk hm hf (hb.le.trans (hN.wt_b j)) hN.Se_ge (add_nonneg hSc heta)
          (by rw [hN.th_eq]; exact thl_nonneg_leaf _ _) (Nat.cast_nonneg _)
        rw [← hN.th_eq, ← hN.k_eq, ← hN.m_eq, ← hN.f_eq, ← hN.depthNumbers_threshold_eq] at b1
        unfold nuWAt at e1
        unfold OnObj.aE OnObj.A1 OnObj.Akw
        rw [hF, hN.ad_eq]
        linarith
      · intro hY
        apply e2
        apply b2
        have h1 := hN.DF_ge j
        have h0 : (0 : ℝ) ≤ O.DF := le_trans (Nat.cast_nonneg _) h1
        have h2 : O.DF ≤ O.Y := by
          unfold OnObj.Y
          nlinarith
        have : ((DF (Dw (ι j)) (Dd.aL (ι j)) : ℕ) : ℝ) < (Formalism.EigenvalueLevelCeiling.plc w : ℝ) := lt_of_le_of_lt (h1.trans h2) hY
        exact_mod_cast this
    have k1 := key w rfl
    have k2 := key (Formalism.DivisionValues.conjPl w) (Formalism.EigenvalueLevelCeiling.plc_conjPl w)
    refine ⟨fun _ => ⟨k1.1, k2.1⟩, fun hY => ⟨k1.2 hY, k2.2 hY, ?_⟩⟩
    rw [hF]
    obtain ⟨θ0, hdeg⟩ := jG.deg
    exact (GlobalTheory.T.forcedContent_bounds_programmeValue_goodPrime N (ι j) _ hp (t5 ▸ n2) (t3 ▸ nq) (t4 ▸ nd) (t1 ▸ ng1) (t2 ▸ ng2) (fun z => (hdeg.w_pos z).le) jG.ratio).1

end GlobalTheory.GoodDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulAFiniteFlatSurjective
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.FormalSeriesBounds GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PairKernel

open GlobalTheory.KerPow

theorem mulA_finite_flat_surjective (S : Scheme.{0}) (P : PolAV S) (n : ℕ) (hn : 1 ≤ n) :
    IsFinite (mulA P.A n).left ∧ Flat (mulA P.A n).left ∧ Surjective (mulA P.A n).left := by
  have gi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
  have hf : IsFinite (mulA P.A n).left := GlobalTheory.MulFinite.isFinite_mulA
    (GlobalTheory.MulPull.mulPull_of_cube_of_symm GlobalTheory.AbLaw.CubeAssembly.cube_gen
      (GlobalTheory.exists_gen_negLB GlobalTheory.laws_without_cohomology.1)).1 GlobalTheory.laws_without_cohomology.2.2.1 gi S P n hn
  have hc := P.isAb.comm
  have hsm := P.isAb.smooth
  have hm := GlobalTheory.AbLaw.MulN.isMonHom_mulA P.A n
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S),
      Flat ((Over.pullback t).map (mulA P.A n)).left ∧
        Surjective ((Over.pullback t).map (mulA P.A n)).left := fun K _ _ t =>
    GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd gi K _ (TLinPf.isAb_pullback t P.A P.isAb) _ inferInstance
      (MorphismProperty.of_isPullback (P := @IsFinite) (GlobalTheory.AbLaw.MulN.isPullback_baseChange t _) hf)
  exact ⟨hf, GlobalTheory.flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S _ _ _ inferInstance inferInstance
    inferInstance hf fun K _ _ t => (hgeo K t).1,
    GlobalTheory.AbLaw.MulN.surjective_of_geomFibres _ fun K _ _ t => (hgeo K t).2⟩

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

end Alg

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)

end GlobalTheory.PairKernel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NonDegenerateAndRowConditionTwoPairsOfPlaces
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.NonDegPair

section

open scoped BigOperators
open MvPowerSeries Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.RowLawSquare GlobalTheory.RowLawPair
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] {dd : ℕ}

theorem coeff_mvExp_of_van {τ : Type} {T : Set τ} {H : MvPowerSeries τ C} [CharZero C] (hH : Van T H)
    (ν : τ →₀ ℕ) (hν : ∀ w ∈ ν.support, w ∉ T) (t : τ) :
    coeff (ν + Finsupp.single t 1) (mvExp H) = coeff (ν + Finsupp.single t 1) H := by
  have h := GlobalTheory.RowLaw.AddCurve.van_pderiv_mvExp hH t ν hν
  rw [map_sub, coeff_pderiv, coeff_pderiv, ← sub_mul, mul_eq_zero] at h
  rcases h with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h (Nat.cast_add_one_ne_zero _)

theorem van_add {τ : Type} {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g) : Van T (f + g) :=
  fun ν hν => by rw [map_add, hf ν hν, hg ν hν, add_zero]

theorem van_sub {τ : Type} {T : Set τ} {f g : MvPowerSeries τ C} (hf : Van T f) (hg : Van T g) : Van T (f - g) :=
  fun ν hν => by rw [map_sub, hf ν hν, hg ν hν, sub_zero]

theorem zc_cvAt {V : VF C} {γ : Fin dd → PowerSeries C} (hγ : IsCv V γ) (s : Fin 2) :
    Zc fun j => cvAt (X s : MvPowerSeries (Fin 2) C) (γ j) := fun j =>
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) (hγ j).1

def toOne (b : MvPowerSeries (Fin dd) C) : PS C 1 dd := subst (pt C dd (0 : Fin 1)) b

theorem sb_toOne {τ : Type} {a : Fin dd → MvPowerSeries τ C} (ha : Zc a) (b : MvPowerSeries (Fin dd) C) :
    sb ![a] (toOne b) = subst a b := by
  unfold toOne sb
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero (zc_pt 0)) (hasSubst_sb (zc1 ha))]
  congr 1
  funext i
  exact sb_pt (zc1 ha) 0 i

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd)
  {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] (p : PairData Y d I)

theorem van_h {n : ℕ} (j : Fin n) {b : Fin dd → PS C n dd} (hb : Zc b) :
    Van {s : Fin n × Fin dd | s.1 = j} (sb ![gp C (Fin dd) j, b] Y.h) := by
  classical
  refine Van.subst {s : Fin 2 × Fin dd | s.1 = 0} (fun s => zc2 (GlobalTheory.RowLawPair.zc_gp j) hb s.1 s.2) ?_ (h_axes Y 0)
  rintro ⟨s, x⟩ hs ν hν
  obtain rfl : s = 0 := hs
  show coeff ν (X (j, x) : PS C n dd) = 0
  rw [coeff_X, if_neg]
  rintro rfl
  exact hν (j, x) (by simp) rfl

theorem sb_gp_three (f : PS C 3 dd) : sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1, gp C (Fin dd) 2] f = f := by
  have e : (fun q : Fin 3 × Fin dd => ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1, gp C (Fin dd) 2] q.1 q.2) = X := by
    funext ⟨s, x⟩
    fin_cases s <;> rfl
  unfold sb
  rw [e, subst_self]
  rfl

theorem formalGroupCocycleLinearTerm_eq_chartLinear (u : Fin dd → C) : c2 (Y.raw p) u = Y.chartLinearTerm u := by
  have z := fun j : Fin 3 => GlobalTheory.RowLawPair.zc_gp (C := C) (dd := dd) j
  have hv : Van {s : Fin 3 × Fin dd | s.1 = 0}
      (sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 1] Y.h + sb ![gp C (Fin dd) (0 : Fin 3), gp C (Fin dd) 2] Y.h -
        sb ![gp C (Fin dd) (0 : Fin 3), law Y (gp C (Fin dd) 1) (gp C (Fin dd) 2)] Y.h) :=
    van_sub (van_add (van_h Y 0 (z 1)) (van_h Y 0 (z 2))) (van_h Y 0 (zc_law Y (z 1) (z 2)))
  have e := exp_gauge_cocycle_second_variable Y (z 0) (z 1) (z 2)
  rw [sb_gp_three, ← mvExp_eq hv.const] at e
  funext μ
  unfold c2 FBChart.chartLinearTerm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [formalAdd_eq_law Y p (z 1) (z 2), hAt_eq_sb, hAt_eq_sb, hAt_eq_sb, ← e, coeff_mvExp_of_van hv]
  intro w hw
  classical
  obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hw)
  exact Fin.succ_ne_zero _

theorem cob_eq (b : MvPowerSeries (Fin dd) C) : cob (Y.raw p) b =
    ev (n := 2) ![addOf Y.B.G.F (pt C dd 0) (pt C dd 1)] (toOne b) - ev (n := 2) ![pt C dd 0] (toOne b) -
      ev (n := 2) ![pt C dd 1] (toOne b) := by
  unfold cob
  rw [formalAdd_eq_law Y p (GlobalTheory.RowLawPair.zc_gp 0) (GlobalTheory.RowLawPair.zc_gp 1),
    ← sb_toOne (zc_law Y (GlobalTheory.RowLawPair.zc_gp 0) (GlobalTheory.RowLawPair.zc_gp 1)),
    ← sb_toOne (GlobalTheory.RowLawPair.zc_gp 0), ← sb_toOne (GlobalTheory.RowLawPair.zc_gp 1)]
  rfl

theorem nonDeg_raw (h : NDG Y) : NonDeg (Y.raw p) V := by
  rintro γ hγ hu hadd ⟨b, hb, hcob⟩
  refine h γ hγ hu (fun i μ h0 h1 => ?_) ⟨toOne b, intS_subst V (zc_pt 0) (fun _ => intS_X V _) hb, fun μ => ?_⟩
  · have e := hadd i μ h0 h1
    rw [formalAdd_eq_law Y p (zc_cvAt hγ 0) (zc_cvAt hγ 1)] at e
    have e2 : (fun q : Fin 2 × Fin dd => cvAt (X q.1 : MvPowerSeries (Fin 2) C) (γ q.2)) =
        fun q : Fin 2 × Fin dd => ![fun j => cvAt (X 0 : MvPowerSeries (Fin 2) C) (γ j),
          fun j => cvAt (X 1 : MvPowerSeries (Fin 2) C) (γ j)] q.1 q.2 := by
      funext ⟨s, x⟩
      fin_cases s <;> rfl
    rw [e2]
    exact e
  · have e := hcob μ
    rwa [formalGroupCocycleLinearTerm_eq_chartLinear, cob_eq] at e

end

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem nonDegenerate_and_rowConditionTwo_pairsOfPlaces : (∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (p : PairData Y d I), NDG Y → NonDeg (Y.raw p) V) ∧ RankMaximalOfNondegenerate :=
  ⟨fun _ _ _ _ _ _ _ _ Y _ _ _ _ p h => nonDeg_raw Y p h,
    fun C _ _ V O _ _ dd Y d _ I _ p h _ Hc =>
      GlobalTheory.T.rawChart_tangent_maximalIdeal_of_nonDegenerate C V d I (Fin dd) (Y.raw p) (GlobalTheory.RowLawPair.rLaw_raw Y p) (GlobalTheory.T.hasGaugeAdjointLieProjectors_pairData C V O dd Y d I p)
        (nonDeg_raw Y p h) Hc⟩

end GlobalTheory.NonDegPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceWeightRowGapMulBoundsSizeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlaceWeightRowGap_mul_bounds_size : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z →
  (1 - ((Tp.Dp : ℝ) + 4) / Tp.TO) * (numOf D L).w j z ≤ (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ∧
  (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ≤ (numOf D L).w j z + 100 * ((numOf D L).Sc + (numOf D L).eta) := by
  first | exact @GlobalTheory.GoodDepth.Gap.gap_bounds | exact GlobalTheory.GoodDepth.Gap.gap_bounds | (intros; apply GlobalTheory.GoodDepth.Gap.gap_bounds <;> assumption)
end

