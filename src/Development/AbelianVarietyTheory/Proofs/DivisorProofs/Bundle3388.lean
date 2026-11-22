import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateUnique
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2230
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0066
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.TrivPullCompIff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeTorusCompare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SplitsAt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianLocusOpenFamilyOverLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0609
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3369

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartFunctionEqValueMulUnitPowFractionField
section
set_option autoImplicit false

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.FracPt

theorem stalkIso_gs {K : Type} [CommRing K] [IsLocalRing K] {X : Scheme.{0}} (f : Sp K ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ U) (a : Γ(X, U)) :
    (stalkClosedPointIso (CommRingCat.of K)).hom.hom (gs f (closedPoint K) U a) = valR f U a := by
  have e1 : gs f (closedPoint K) U a = (Sp K).presheaf.germ ⊤ (closedPoint K) trivial ((f.appLE U ⊤ h).hom a) := by
    erw [gs_eq f _ U (h trivial)]
    rw [← TopCat.Presheaf.germ_res_apply (Sp K).presheaf (homOfLE h) (closedPoint K) trivial]
    rfl
  erw [e1]
  rw [valR, dif_pos h]
  rw [← ΓSpecIso_hom_stalkClosedPointIso_inv (CommRingCat.of K)]
  simp only [CommRingCat.comp_apply]
  rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]

end GlobalTheory.FracPt

namespace GlobalTheory.FracPt

theorem valR_spMap_const {Ω K : Type} [CommRing Ω] [CommRing K] (f : Ω →+* K) (ω : Ω) :
    valR (spMap f) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) = f ω := by
  have h : ⊤ ≤ spMap f ⁻¹ᵁ ⊤ := le_rfl
  rw [valR, dif_pos h]
  calc _ = ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom ≫ CommRingCat.ofHom f).hom
        ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) := by
          rw [← Scheme.ΓSpecIso_naturality]; rfl
    _ = f ω := by
          have e : (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω) = ω := by
            rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]
          rw [CommRingCat.hom_comp, RingHom.comp_apply, e, CommRingCat.hom_ofHom]

theorem chart_eq_value_mul_pow : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (Ω : Type) [CommRing Ω] [IsDomain Ω]
    (x : Sp Ω ⟶ X) (g : GlobalTheory.RayEv.Transport.Frame L (x ≫ 𝟙 X)) (j : L.ι) (O : X.Opens), O ≤ L.U j →
    ⊤ ≤ (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) ⁻¹ᵁ O → ∃ e₀ : (FractionRing Ω)ˣ,
      ∀ (k : ℕ) (σ : SecM (𝟙 X) L k) (ω : Ω), IsValue (𝟙 _) L x g k σ ω →
        valR (spMap (algebraMap Ω (FractionRing Ω)) ≫ x) O (rsT (σ.f fun _ => j) O) =
          algebraMap Ω (FractionRing Ω) ω * (e₀ : FractionRing Ω) ^ k := by
  intro X L hL Ω _ _ x g j O hO hxO
  let ηF := spMap (algebraMap Ω (FractionRing Ω))
  let z : Sp (FractionRing Ω) := closedPoint (FractionRing Ω)
  have hz : ((ηF ≫ x) ≫ 𝟙 X) z ∈ L.U j := by
    rw [Category.comp_id]; exact hO (hxO trivial)
  obtain ⟨J, hJ, hJj⟩ := exists_good L hL z (K := PUnit) (fun _ => (ηF ≫ x) ≫ 𝟙 X) (fun _ => j)
    (fun _ _ _ => rfl) (fun _ => hz)
  let φ := (stalkClosedPointIso (CommRingCat.of (FractionRing Ω))).hom.hom
  refine ⟨Units.map φ.toMonoidHom (val g ηF z J), fun k σ ω hv => ?_⟩
  have e := congrArg φ (hv _ ηF z J hJ)
  have hOW : O ≤ (LB.LinComb L (fun _ : Fin 1 => 𝟙 X) (fun _ => (k : ℤ))).U (fun _ => j) :=
    fun y hy => Set.mem_iInter.2 fun _ => hO hy
  rw [sval_of σ (ηF ≫ x) z J (fun _ => j) (fun _ => hJj PUnit.unit)] at e
  erw [← gs_res (ηF ≫ x) z hOW (hxO trivial) (σ.f fun _ => j)] at e
  rw [map_mul, Units.val_pow_eq_pow_val, map_pow] at e
  have e1 := stalkIso_gs (ηF ≫ x) O hxO ((X.presheaf.map (homOfLE hOW).op).hom (σ.f fun _ => j))
  have e2 := stalkIso_gs ηF ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom ω)
  rw [valR_spMap_const] at e2
  erw [e1, e2] at e
  rw [GlobalTheory.KS.rsT, dif_pos hOW]
  exact e

end GlobalTheory.FracPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartUniformBound
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.MetFam

open MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V cHess wd wdb)
open scoped ContDiff ENNReal

theorem contDiffAt_fderiv_snd {D : ℕ} {Θ : ℝ × V D → ℂ} {x₀ : ℝ × V D} {m n : WithTop ℕ∞} (h : ContDiffAt ℝ n Θ x₀)
    (hmn : m + 1 ≤ n) (e : V D) :
    ContDiffAt ℝ m (fun x : ℝ × V D => fderiv ℝ (fun v => Θ (x.1, v)) x.2 e) x₀ := by
  have h₁ : ContDiffAt ℝ n (Function.uncurry fun (x : ℝ × V D) (v : V D) => Θ (x.1, v)) (x₀, x₀.2) :=
    ContDiffAt.comp (g := Θ) (f := fun w : (ℝ × V D) × V D => (w.1.1, w.2)) (x₀, x₀.2) h
      ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd).contDiffAt
  exact (h₁.fderiv contDiffAt_snd hmn).clm_apply contDiffAt_const

theorem continuousAt_cHess_snd {D : ℕ} {Θ : ℝ × V D → ℂ} {x₀ : ℝ × V D} (h : ContDiffAt ℝ 2 Θ x₀) :
    ContinuousAt (fun x : ℝ × V D => cHess D (fun v => Θ (x.1, v)) x.2) x₀ := by
  refine continuousAt_pi.2 fun j => continuousAt_pi.2 fun l => ?_
  have h₁ : ContDiffAt ℝ 1 (fun x : ℝ × V D => wdb D l (fun v => Θ (x.1, v)) x.2) x₀ :=
    ((contDiffAt_fderiv_snd h (by norm_num) _).add
      (contDiffAt_const.mul (contDiffAt_fderiv_snd h (by norm_num) _))).div_const 2
  have h₂ : ContDiffAt ℝ 0 (fun x : ℝ × V D =>
      wd D j (fun v => wdb D l (fun w => Θ (x.1, w)) v) x.2) x₀ :=
    ((contDiffAt_fderiv_snd h₁ (by norm_num) _).sub
      (contDiffAt_const.mul (contDiffAt_fderiv_snd h₁ (by norm_num) _))).div_const 2
  exact h₂.continuousAt

theorem FamAt.exists_bound_chernDens {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}
    {t : ℝ → ℝ} (ht : Tendsto t atTop (𝓝 0)) {B : LB X} {φ : Weight p σ B} (hφ : φ.IsCInf)
    {u : ℝ → CxPts p σ → ℝ} (hu : ∀ R y, CInfAt (u R) y) {u₀ : CxPts p σ → ℝ} {y : CxPts p σ} (h : FamAt t u u₀ y)
    (c : AlgChart p σ D) (hy : y ∈ c.e.source) :
    ∃ K : ℝ, ∀ᶠ x : ℝ × CxPts p σ in atTop ×ˢ 𝓝 y, |c.chernDens (φ.addFn (u x.1)) x.2| ≤ K := by
  obtain ⟨ι, _, f, Φ, O, h₁, h₂, h₃, h₄, -, h₆⟩ := h
  have hi := mem_pick φ.isLB y
  set i := pick φ.isLB y
  set Θ : ℝ × V D → ℂ := fun x => ((φ.φ i (c.e.symm x.2) + Φ (x.1, f (c.e.symm x.2)) : ℝ) : ℂ) with hΘ
  have hΘd : ContDiffAt ℝ 2 Θ (0, c.e y) := by
    have a₁ : ContDiffAt ℝ 2 (fun x : ℝ × V D => φ.φ i (c.e.symm x.2)) (0, c.e y) :=
      ContDiffAt.comp (g := fun v => φ.φ i (c.e.symm v)) (0, c.e y) (hφ.contDiffAt c hy hi) contDiffAt_snd
    have a₂ : ContDiffAt ℝ 2 (fun x : ℝ × V D => f (c.e.symm x.2)) (0, c.e y) :=
      ContDiffAt.comp (g := fun v => f (c.e.symm v)) (0, c.e y)
        ((h₁.contDiffAt_chart c hy).of_le (by norm_cast)) contDiffAt_snd
    have a₃ : ContDiffAt ℝ 2 Φ (0, f (c.e.symm (c.e y))) := by
      rw [c.e.left_inv hy]
      exact (h₄.contDiffAt (h₂.mem_nhds h₃)).of_le (by norm_cast)
    have a₄ : ContDiffAt ℝ 2 (fun x : ℝ × V D => Φ (x.1, f (c.e.symm x.2))) (0, c.e y) :=
      ContDiffAt.comp (g := Φ) (f := fun x : ℝ × V D => (x.1, f (c.e.symm x.2))) (0, c.e y) a₃
        (contDiffAt_fst.prodMk a₂)
    exact Complex.ofRealCLM.contDiff.contDiffAt.comp _ (a₁.add a₄)
  set G : ℝ × V D → ℝ := fun x => D.factorial / Real.pi ^ D * (cHess D (fun v => Θ (x.1, v)) x.2).det.re with hG
  have hGc : ContinuousAt G (0, c.e y) :=
    continuousAt_const.mul (Complex.continuous_re.continuousAt.comp
      ((continuous_id.matrix_det).continuousAt.comp (continuousAt_cHess_snd hΘd)))
  have hT : Tendsto (fun x : ℝ × CxPts p σ => G (t x.1, c.e x.2)) (atTop ×ˢ 𝓝 y) (𝓝 (G (0, c.e y))) :=
    hGc.tendsto.comp ((ht.comp tendsto_fst).prodMk_nhds ((c.e.continuousAt hy).tendsto.comp tendsto_snd))
  refine ⟨|G (0, c.e y)| + 1, ?_⟩
  obtain ⟨pa, ha, pb, hb, hab⟩ := eventually_prod_iff.1 h₆
  filter_upwards [hT.abs.eventually (ge_mem_nhds (lt_add_one _)), tendsto_fst.eventually ha,
    tendsto_snd.eventually hb.eventually_nhds, tendsto_snd.eventually (c.e.open_source.mem_nhds hy),
    tendsto_snd.eventually ((isOpen_ptsIn (B.U i)).mem_nhds hi)] with x hx hxa hxb hxs hxi
  have e : (fun v => ((φ.addFn (u x.1)).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e x.2)] fun v => Θ (t x.1, v) := by
    have hc := c.e.continuousAt_symm (c.e.map_source hxs)
    rw [ContinuousAt, c.e.left_inv hxs] at hc
    filter_upwards [hc.eventually hxb] with v hv
    simp only [hΘ, Weight.addFn, hab hxa hv]
  rw [c.chernDens_eq (hφ.addFn (hu x.1)) hxs hxi, AlgChart.hess, ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr e]
  exact hx

theorem exists_bound_chernPart_univ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ t : ℝ → ℝ, Tendsto t atTop (𝓝 0) → ∀ (σ : k →+* ℂ) (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ u : ℝ → CxPts p σ → ℝ, (∀ R y, CInfAt (u R) y) → (∀ y, FamAt t u (fun _ => 0) y) → ∃ C : NNReal, ∀ᶠ R in atTop, ∀ ε : ℤˣ, (φ.addFn (u R)).chernPart D ε Set.univ ≤ (C : ENNReal) := by
  intro k _ X _ p D hX hS t ht σ B φ hφ u hu hF
  have := hX.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨A⟩ := hS σ
  have hloc : ∀ y : CxPts p σ, ∃ U : Set (CxPts p σ), IsOpen U ∧ y ∈ U ∧ ∃ C : NNReal,
      ∀ᶠ R in atTop, ∀ ε : ℤˣ, (φ.addFn (u R)).chernPart D ε U ≤ (C : ENNReal) := by
    intro y
    obtain ⟨a, hy⟩ := A.cover y
    set c := A.chart a
    obtain ⟨K, hK⟩ := (hF y).exists_bound_chernDens ht hφ hu c hy
    obtain ⟨pa, ha, pb, hb, hab⟩ := eventually_prod_iff.1 hK
    have hball : ∀ᶠ z in 𝓝 y, c.e z ∈ Metric.closedBall (c.e y) 1 :=
      (c.e.continuousAt hy).eventually (Metric.closedBall_mem_nhds _ one_pos)
    obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.1 (hb.and (hball.and (c.e.open_source.mem_nhds hy)))
    have hUs : U ⊆ c.e.source := fun z hz => (hU z hz).2.2
    have hfin : ENNReal.ofReal K * volume (Metric.closedBall (c.e y) 1) ≠ ⊤ :=
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top).ne
    refine ⟨U, hUo, hyU, (ENNReal.ofReal K * volume (Metric.closedBall (c.e y) 1)).toNNReal, ?_⟩
    filter_upwards [ha] with R hR ε
    rw [ENNReal.coe_toNNReal hfin, Weight.chernPart_apply (hφ.addFn (hu R)) ε c hUo.measurableSet hUs]
    have hm := GlobalTheory.ChartGlue.measurableSet_image c.e hUo.measurableSet hUs
    calc _ ≤ ∫⁻ _ in c.e '' U, ENNReal.ofReal K := by
          refine setLIntegral_mono' hm ?_
          rintro _ ⟨z, hz, rfl⟩
          refine ENNReal.ofReal_le_ofReal ((le_abs_self _).trans ?_)
          rw [c.e.left_inv (hUs hz), abs_mul]
          have := hab hR (hU z hz).1
          rcases Int.units_eq_one_or ε with rfl | rfl <;> simpa using this
      _ = ENNReal.ofReal K * volume (c.e '' U) := setLIntegral_const _ _
      _ ≤ _ := by
          gcongr
          rintro _ ⟨z, hz, rfl⟩
          exact (hU z hz).2.1
  choose U hUo hyU C hC using hloc
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUo (fun y _ => Set.mem_iUnion.2 ⟨y, hyU y⟩)
  refine ⟨∑ y ∈ s, C y, ?_⟩
  filter_upwards [(eventually_all_finset s).2 fun y _ => hC y] with R hR ε
  refine (measure_mono hs).trans ((measure_biUnion_finset_le s U).trans ?_)
  rw [ENNReal.coe_finset_sum]
  exact Finset.sum_le_sum fun y hy => hR y hy ε

end GlobalTheory.MetFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreIsAbelianSchemeRelDimOfFrame
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.FibreAbDim

theorem exists_isLieBasis_of_frame {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}
    (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X) {G' : Over (Sp R)} [GrpObj G'] {φ : G'.left ⟶ t.G.left}
    (h : IsGrpPullback G' t.G x φ) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t.G.left))
    (hv : ∀ a, IsTanAtG t x (v a))
    (hb : ∀ w, IsTanAtG t x w → ∃! cf : Fin n → R, IsCombAtG t x v cf w) :
    ∃ v' : Fin n → (epsR R ⟶ G'), IsLieBasis v' := by
  obtain ⟨ρ, hρ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv h (epsR R) (spMap (algebraMap R (DualNumber R)) ≫ x) rfl
  obtain ⟨σ, hσ⟩ := GlobalTheory.HeckePoint.exists_ptsEquiv h (𝟙_ (Over (Sp R))) x (Category.id_comp _)
  have h1 : η[G'].left ≫ φ = (1 : Over.mk x ⟶ t.G).left := by
    have := hσ 1
    rw [map_one] at this
    rw [this]
    congr 2
  have tan : ∀ w : epsR R ⟶ G', IsTangent w ↔ IsTanAtG t x (ρ w).left := by
    intro w
    constructor
    · intro hw
      refine ⟨Over.w (ρ w), ?_⟩
      rw [hρ, ← Category.assoc, hw, h1]
    · intro hw
      apply h.1.hom_ext
      · rw [Category.assoc, ← hρ, hw.2, h1]
      · rw [Category.assoc, Over.w w, Over.w η[G']]
        show spMap _ ≫ spMap _ = 𝟙 _
        unfold spMap
        rw [← Spec.map_comp, ← Spec.map_id]
        congr 1
  let v' : Fin n → (epsR R ⟶ G') := fun a => ρ.symm (Over.homMk (v a) (hv a).1)
  have hv' : ∀ a, (v' a).left ≫ φ = v a := fun a => by
    rw [← hρ]
    simp [v']
  have comb : ∀ (c : Fin n → R) (w : epsR R ⟶ G'), IsLieComb c v' w ↔ IsCombAtG t x v c (ρ w).left := by
    intro c w
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨fun i => ρ (u i), fun i => ?_, ?_⟩
      · rw [hρ, hu, Category.assoc, hv']
        rfl
      · rw [map_list_prod, List.map_ofFn]
        rfl
    · rintro ⟨u, hu, e⟩
      refine ⟨fun i => ρ.symm (u i), fun i => ?_, ?_⟩
      · apply h.1.hom_ext
        · rw [← hρ, MulEquiv.apply_symm_apply, hu, Category.assoc, hv']
          rfl
        · rw [Category.assoc, Over.w, Over.w]
          show spMap _ = spMap _ ≫ spMap _
          unfold spMap
          rw [← Spec.map_comp]
          congr 1
          ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
      · apply ρ.injective
        rw [map_list_prod, List.map_ofFn]
        refine (Over.OverMorphism.ext ?_)
        rw [← e]
        congr 3
        funext i
        simp
  refine ⟨v', fun a => (tan _).2 ?_, fun w hw => ?_⟩
  · rw [hρ, hv']
    exact hv a
  · simpa only [comb] using hb _ ((tan w).1 hw)

theorem isAbelianScheme_and_relDim : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X), IsProper t.G.hom → ∀ (U : X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ a, IsTanAtG t (chart U) (v a)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ (m : Ideal Γ(X, U.1)), m.IsMaximal → ∀ (A : Over (Sp (Γ(X, U.1) ⧸ m))) [GrpObj A] (j : A.left ⟶ t.G.left), IsGrpPullback A t.G (spMap (Ideal.Quotient.mk m) ≫ chart U) j → IsAbelianScheme A ∧ SmoothOfRelativeDimension n A.hom := by
  intro E _ _ _ H X t hp U n v hv hb m hm A _ j hj
  have hG := GlobalTheory.HeckePoint.isAbelianScheme_of_proper t hp
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG hj
  refine ⟨hA, ?_⟩
  have h₀ := isGrpPullback_pullback t.G (chart U)
  have hG' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hG h₀
  obtain ⟨v', hv'⟩ := exists_isLieBasis_of_frame t (chart U) h₀ v hv hb
  have w : j ≫ t.G.hom = (A.hom ≫ spMap (Ideal.Quotient.mk m)) ≫ chart U := by
    rw [hj.1.w, Category.assoc]
  have h₁ := IsGrpPullback.cancel h₀ (hj.congr rfl (h₀.1.lift_fst _ _ w).symm) (h₀.1.lift_snd _ _ w)
  have := hG'.comm
  have := hA.comm
  have := hG.comm
  obtain ⟨v₁, hv₁, -⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ _ _ A _ h₁ hG'.smooth n v' hv'
  have : IsLocalRing (Γ(X, U.1) ⧸ m) := by
    letI := Ideal.Quotient.field m
    infer_instance
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim _ A hA
  obtain ⟨v₂, hv₂⟩ := GlobalTheory.KeyPow.exists_isLieBasis A hg
  rw [GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis hj hv₁ hv₂]
  exact hg

end GlobalTheory.FibreAbDim
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeSignatureSumEqTwiceDimension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BalProj

theorem signature_count : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (p q : ℕ),
    ∑ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) *
      (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) =
      2 * (Module.finrank ℚ E / 2 * p * q) := by
  intro E _ _ _ H p q
  have hdpos : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h0 := H.sqrt_neg_disc_sq
  have hre : H.rt0.re = 0 := by
    have e1 := congrArg Complex.re h0
    have e2 := congrArg Complex.im h0
    have e3 : H.rt0.re * H.rt0.im = 0 := by
      simp only [pow_two, Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at e2
      linarith
    simp only [pow_two, Complex.mul_re, Complex.neg_re, Complex.natCast_re] at e1
    rcases mul_eq_zero.mp e3 with h | h
    · exact h
    · exfalso
      rw [h] at e1
      nlinarith [sq_nonneg H.rt0.re]
  have hne : H.rt0 ≠ 0 := by
    intro h
    rw [h] at h0
    have : (H.d : ℂ) = 0 := by simpa using h0
    exact hdpos.ne' (by exact_mod_cast this)
  have hconj : (starRingEnd ℂ) H.rt0 = -H.rt0 := by
    apply Complex.ext <;> simp [hre]
  have hnn : H.rt0 ≠ -H.rt0 := by
    intro h
    apply hne
    have : (2 : ℂ) * H.rt0 = 0 := by rw [two_mul]; nth_rewrite 2 [h]; ring
    simpa using this
  have key : ∀ τ : E →+* ℂ, (if τ (H.rt : E) = H.rt0 then p else q) *
      (if NumberField.ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0 then p else q) = p * q := by
    intro τ
    have hsq : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
      have hrtE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
        have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
        simpa using this
      rw [← map_pow, hrtE, h0]
      simp
    have hor : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := sq_eq_sq_iff_eq_or_eq_neg.mp hsq
    rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
    rcases hor with h | h
    · rw [if_pos h, h, hconj, if_neg (Ne.symm hnn)]
    · rw [if_neg (by rw [h]; exact Ne.symm hnn), h, map_neg, hconj, neg_neg, if_pos rfl, mul_comm]
  rw [Finset.sum_congr rfl (fun τ _ => key τ), Finset.sum_const, Finset.card_univ,
    NumberField.Embeddings.card E ℂ, smul_eq_mul, NumberField.IsTotallyComplex.finrank]
  rw [Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  ring

end GlobalTheory.BalProj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpOfIsCocycle
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CatCoh GlobalTheory.CechDR

namespace GlobalTheory.CechCmp

variable {R : Type} [CommRing R] {Z : Scheme.{0}} (s : Z ⟶ Sp R) {J : Type} (W : J → Z.Opens)

abbrev Bas : Type := {V : Z.affineOpens // ∃ i, V.1 ≤ W i}

abbrev incl : (Bas W)ᵒᵖ ⥤ AffOp Z :=
  (Monotone.functor (f := (Subtype.val : Bas W → Z.affineOpens)) fun _ _ h ↦ h).op

def resEquiv (hW : ⨆ i, W i = ⊤) : HO1 s ≃ₗ[R] CatCoh.H1 (incl W ⋙ OAff s) :=
  LinearEquiv.ofBijective (CoefMap.restrict (OAff s) (incl W)).pull1
    (GlobalTheory.CoverO.restrict_cover_affine_pull1_bijective R Z s J W hW)

def idx {W : J → Z.Opens} (V : Bas W) : J := V.2.choose

theorem le_idx {W : J → Z.Opens} (V : Bas W) : V.1.1 ≤ W (idx V) := V.2.choose_spec

theorem le_of_hom {W : J → Z.Opens} {V V' : (Bas W)ᵒᵖ} (a : V ⟶ V') : V'.unop.1.1 ≤ V.unop.1.1 :=
  leOfHom a.unop

def IsCocycle (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : Prop :=
  ∀ i i' i'', resG Z (inf_le_left : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i') (c i i') +
    resG Z (le_inf (inf_le_left.trans inf_le_right) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i' ⊓ W i'')
      (c i' i'') =
    resG Z (le_inf (inf_le_left.trans inf_le_left) inf_le_right : W i ⊓ W i' ⊓ W i'' ≤ W i ⊓ W i'')
      (c i i'')

def fc (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : CatCoh.C1 (incl W ⋙ OAff s) :=
  fun V V' a ↦ resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
    (c (idx V.unop) (idx V'.unop))

theorem fc_apply (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) {V V' : (Bas W)ᵒᵖ} (a : V ⟶ V') :
    fc s W c V V' a =
      resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
        (c (idx V.unop) (idx V'.unop)) := rfl

theorem resG_resG' {U V V' : Z.Opens} (h : V ≤ U) (h' : V' ≤ V) (x : Γ(Z, U)) :
    resG Z h' (resG Z h x) = resG Z (h'.trans h) x := by
  simp only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem fc_mem {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')} (hc : IsCocycle W c) : fc s W c ∈ Z1 (incl W ⋙ OAff s) := by
  intro V V' V'' a b
  have hV'' : V''.unop.1.1 ≤ W (idx V.unop) ⊓ W (idx V'.unop) ⊓ W (idx V''.unop) :=
    le_inf (le_inf ((le_of_hom b).trans ((le_of_hom a).trans (le_idx V.unop)))
      ((le_of_hom b).trans (le_idx V'.unop))) (le_idx V''.unop)
  have e := congrArg (resG Z hV'') (hc (idx V.unop) (idx V'.unop) (idx V''.unop))
  simp only [map_add, resG_resG'] at e
  have key : resG Z (le_inf ((le_of_hom (a ≫ b)).trans (le_idx V.unop)) (le_idx V''.unop))
      (c (idx V.unop) (idx V''.unop)) =
      resG Z (le_of_hom b) (resG Z (le_inf ((le_of_hom a).trans (le_idx V.unop)) (le_idx V'.unop))
        (c (idx V.unop) (idx V'.unop))) +
      resG Z (le_inf ((le_of_hom b).trans (le_idx V'.unop)) (le_idx V''.unop))
        (c (idx V'.unop) (idx V''.unop)) := by
    rw [resG_resG']
    exact e.symm
  exact key

def cmp (hW : ⨆ i, W i = ⊤) (c : ∀ i i' : J, Γ(Z, W i ⊓ W i')) : HO1 s := by
  classical
  exact if h : fc s W c ∈ Z1 (incl W ⋙ OAff s) then
    (resEquiv s W hW).symm (H1.mk _ ⟨fc s W c, h⟩) else 0

theorem cmp_of_isCocycle (hW : ⨆ i, W i = ⊤) {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCocycle W c) :
    cmp s W hW c = (resEquiv s W hW).symm (H1.mk _ ⟨fc s W c, fc_mem s W hc⟩) := by
  unfold cmp
  rw [dif_pos (fc_mem s W hc)]

theorem restrict_cmp (hW : ⨆ i, W i = ⊤) {c : ∀ i i' : J, Γ(Z, W i ⊓ W i')}
    (hc : IsCocycle W c) :
    (CoefMap.restrict (OAff s) (incl W)).pull1 (cmp s W hW c) =
      H1.mk _ ⟨fc s W c, fc_mem s W hc⟩ := by
  rw [cmp_of_isCocycle s W hW hc]
  exact (resEquiv s W hW).apply_symm_apply _

end GlobalTheory.CechCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePolynomialDefectBilinearAdditivePartsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cocycle_polynomialDefect_bilinear_additive_parts : ∀ (R X : Type) [CommRing R] [IsDomain R] [CharZero R] [AddCommGroup X] (w : X → X →+ R) (π π' : X → R), (∀ (k : ℕ), 1 ≤ k → ∀ mu mu' α : X, 2 * (k : R) * w (mu + mu') α + 2 * (k : R) ^ 2 * π (mu + mu') + 2 * (k : R) * π' (mu + mu') = (2 * (k : R) * w mu α + 2 * (k : R) ^ 2 * π mu + 2 * (k : R) * π' mu) + (2 * (k : R) * w mu' (α + k • mu) + 2 * (k : R) ^ 2 * π mu' + 2 * (k : R) * π' mu')) → (∀ mu mu' α, w (mu + mu') α = w mu α + w mu' α) ∧ (∀ mu mu', w mu mu' = w mu' mu) ∧ (∀ mu mu', π' (mu + mu') = π' mu + π' mu') ∧ ∀ mu mu', π (mu + mu') = π mu + π mu' + w mu' mu := by
  first | exact @GlobalTheory.cocycle_polynomial_defect | exact GlobalTheory.cocycle_polynomial_defect | (intros; apply GlobalTheory.cocycle_polynomial_defect <;> assumption)
end

