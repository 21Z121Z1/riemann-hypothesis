import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LabelSigBijective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0009
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0209
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0210
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0104
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0208
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0015
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpan
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.YBrLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0006
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0175
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0158
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0206
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0071
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0211
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FormOffSpecializationRing
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem mh_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mh_neg {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) : IsMultiHomog (-f) a := by
  intro m hm k
  rw [MvPolynomial.support_neg] at hm
  exact hf m hm k

theorem mh_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem mh_C (r : ℤ) : IsMultiHomog (MvPolynomial.C r : MRing ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C] at hm
    by_contra hne
    exact hm (if_neg (Ne.symm hne))
  subst hm0
  simp

private theorem isMultiHomog_mul_of_mRing {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g b) :
    IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, h1, m2, h2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib, hf m1 h1 k, hg m2 h2 k]

theorem mh_prod {I : Type} (S : Finset I) {f : I → MRing ι} {d : I → K → ℕ}
    (h : ∀ i ∈ S, IsMultiHomog (f i) (d i)) : IsMultiHomog (∏ i ∈ S, f i) (∑ i ∈ S, d i) := by
  classical
  revert h
  refine Finset.induction_on S ?_ ?_
  · intro _
    simpa using mh_C (ι := ι) 1
  · intro i S hi ih h
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact isMultiHomog_mul_of_mRing (h i (Finset.mem_insert_self i S)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Forms

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] {𝕜 : Type} [Field 𝕜]
  {y : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → 𝕜}

theorem hv_zero : Small.HasVal y (0 : K → ℤ) (0 : Ω) z (0 : 𝕜) := by
  refine ⟨0, 0, 0, 1, mh_zero 0, by simpa using mh_C (ι := ι) 1, fun k => by simp, by simp, by simp, by simp⟩

theorem hv_add {s s' : Ω} {w w' : 𝕜} (h : Small.HasVal y (0 : K → ℤ) s z w)
    (h' : Small.HasVal y (0 : K → ℤ) s' z w') : Small.HasVal y (0 : K → ℤ) (s + s') z (w + w') := by
  obtain ⟨dg, dh, g, hp, hg, hh, e, ey, hz, ez⟩ := h
  obtain ⟨dg', dh', g', hp', hg', hh', e', ey', hz', ez'⟩ := h'
  have hd : dg = dh := funext fun k => by
    have := e k
    simp only [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  have hd' : dg' = dh' := funext fun k => by
    have := e' k
    simp only [Pi.zero_apply, add_zero] at this
    exact_mod_cast this
  subst hd hd'
  refine ⟨dg + dg', dg + dg', g * hp' + g' * hp, hp * hp', mh_add (isMultiHomog_mul_of_mRing hg hh') ?_,
    isMultiHomog_mul_of_mRing hh hh', fun k => by simp, ?_, ?_, ?_⟩
  · rw [add_comm dg dg']
    exact isMultiHomog_mul_of_mRing hg' hh
  · simp only [map_add, map_mul, ey, ey']
    ring
  · rw [map_mul]
    exact mul_ne_zero hz hz'
  · simp only [map_add, map_mul, ez, ez']
    ring

theorem hv_neg {s : Ω} {w : 𝕜} (h : Small.HasVal y (0 : K → ℤ) s z w) :
    Small.HasVal y (0 : K → ℤ) (-s) z (-w) := by
  obtain ⟨dg, dh, g, hp, hg, hh, e, ey, hz, ez⟩ := h
  exact ⟨dg, dh, -g, hp, mh_neg hg, hh, e, by rw [map_neg, ey, neg_mul], hz, by rw [map_neg, ez, neg_mul]⟩

theorem hv_quot {d : K → ℕ} {g h : MRing ι} (hg : IsMultiHomog g d) (hh : IsMultiHomog h d)
    {s : Ω} (e : MvPolynomial.aeval y g = s * MvPolynomial.aeval y h) (hz : MvPolynomial.aeval z h ≠ 0) :
    Small.HasVal y (0 : K → ℤ) s z (MvPolynomial.aeval z g / MvPolynomial.aeval z h) := by
  exact ⟨d, d, g, h, hg, hh, fun k => by simp, e, hz, (div_mul_cancel₀ _ hz).symm⟩

theorem hv_natInv [CharZero Ω] [CharZero 𝕜] {n : ℕ} (hn : n ≠ 0) :
    Small.HasVal y (0 : K → ℤ) ((n : Ω))⁻¹ z ((n : 𝕜))⁻¹ := by
  refine ⟨0, 0, 1, MvPolynomial.C (n : ℤ), by simpa using mh_C (ι := ι) 1, mh_C (n : ℤ), fun k => by simp,
    ?_, ?_, ?_⟩
  · simp [hn]
  · simpa using hn
  · simp [hn]

def valRing (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → 𝕜) : Subring Ω where
  carrier := {s | ∃ w, Small.HasVal y (0 : K → ℤ) s z w}
  mul_mem' := by
    rintro a b ⟨w, hw⟩ ⟨w', hw'⟩
    have := hv_mul hw hw'
    rw [add_zero] at this
    exact ⟨_, this⟩
  one_mem' := ⟨1, hv_one⟩
  add_mem' := by
    rintro a b ⟨w, hw⟩ ⟨w', hw'⟩
    exact ⟨_, hv_add hw hw'⟩
  zero_mem' := ⟨0, hv_zero⟩
  neg_mem' := by
    rintro a ⟨w, hw⟩
    exact ⟨_, hv_neg hw⟩

def valMap (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) : valRing y z →+* 𝕜 where
  toFun x := x.2.choose
  map_one' := GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (valRing y z).one_mem.choose_spec hv_one
  map_mul' a b := by
    have := hv_mul a.2.choose_spec b.2.choose_spec
    rw [add_zero] at this
    exact GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (a * b).2.choose_spec this
  map_zero' := GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (valRing y z).zero_mem.choose_spec hv_zero
  map_add' a b :=
    GlobalTheory.CompanionTheory.Ar.Small.ReadFinTest.hasVal_unique hz (a + b).2.choose_spec
      (hv_add a.2.choose_spec b.2.choose_spec)

theorem hasVal_valMap (hz : z ∈ Small.ptsOver 𝕜 (mCoordIdeal y)) (x : valRing y z) :
    Small.HasVal y (0 : K → ℤ) (x : Ω) z (valMap hz x) := by
  exact x.2.choose_spec

end Values

theorem exists_subring_val : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω), Birational y → ∀ B : Finset Ω, ∃ u : MRing ι, Small.IsFormOff (mCoordIdeal y) u ∧ ∀ (𝕜 : Type) [Field 𝕜] [CharZero 𝕜] (z : (Σ k, ι k) → 𝕜), z ∈ Small.ptsOver 𝕜 (mCoordIdeal y) → MvPolynomial.aeval z u ≠ 0 → ∃ (A : Subring Ω) (ev : A →+* 𝕜), (↑B : Set Ω) ⊆ A ∧ (∀ n : ℕ, n ≠ 0 → ((n : Ω))⁻¹ ∈ A) ∧ ∀ x : A, Small.HasVal y 0 (x : Ω) z (ev x) := by
  intro K _ ι _ Ω _ _ y hbir B
  have hb' : ∀ s : Ω, ∃ (d : K → ℕ) (g h : MRing ι), IsMultiHomog g d ∧ IsMultiHomog h d ∧
      MvPolynomial.aeval y h ≠ 0 ∧ MvPolynomial.aeval y g = s * MvPolynomial.aeval y h := hbir
  choose d g hq hg hh hyne e using hb'
  have key : ∀ f : MRing ι, MvPolynomial.eval (fun _ => (1 : Ω)) (mConeMap y f) = MvPolynomial.aeval y f := by
    intro f
    induction f using MvPolynomial.induction_on
    · simp [mConeMap]
    · rename_i hp hq
      simp only [map_add, hp, hq]
    · rename_i hp
      simp only [map_mul, hp]
      simp [mConeMap]
  refine ⟨∏ b ∈ B, hq b, ⟨⟨∑ b ∈ B, d b, mh_prod B fun b _ => hh b⟩, ?_⟩, ?_⟩
  · intro hu
    have h0 : MvPolynomial.aeval y (∏ b ∈ B, hq b) = 0 := by
      rw [← key, show mConeMap y (∏ b ∈ B, hq b) = 0 from hu, map_zero]
    rw [map_prod, Finset.prod_eq_zero_iff] at h0
    obtain ⟨b, _, hb⟩ := h0
    exact hyne b hb
  · intro 𝕜 _ _ z hz hzu
    rw [map_prod] at hzu
    refine ⟨valRing y z, valMap hz, ?_, ?_, fun x => hasVal_valMap hz x⟩
    · intro b hb
      exact ⟨_, hv_quot (hg b) (hh b) (e b) (Finset.prod_ne_zero_iff.mp hzu b hb)⟩
    · intro n hn
      exact ⟨_, hv_natInv hn⟩

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.ValSub
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeGeo

theorem exists_factor_XF_of_genericPoint : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y.X), GlobalTheory.CompanionTheory.Ar.genPt ξ ∈ genericPoints Y.X →
      ∃ y₀ : Sp Ω ⟶ Xo.XF c, ξ = y₀ ≫ Y.j := by
  intro E _ _ _ H D l Xo c Y Ω _ ξ hξ
  obtain ⟨K, _, _, n, x, y, ht, -, he⟩ := GlobalTheory.T.generic_point_normal_coords E H D l Xo c Y _ hξ
  obtain ⟨i, hi⟩ := GlobalTheory.CompanionTheory.Ar.TowerOfTest.factor (y ≫ Y.j) ht.gen ξ he.symm
  exact ⟨Spec.map (CommRingCat.ofHom i) ≫ y, by rw [hi, Category.assoc]⟩

end GlobalTheory.CompanionTheory.Ar.ChangeGeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GermFrobeniusTorsionSectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Coc
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.germ_frobenius_torsion_section : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (X0 : Scheme.{0}) (t : SAB H X0) (k : Type) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] (x : Sp k ⟶ X0) (d : ℕ) (g : GermAt t x d) (w : Fin d → k) (m : ℕ), (homAt x (jetSubstP p fun q : Fin 1 × Fin d => MvPolynomial.C (w q.2) * MvPolynomial.X ()) ≫ g.x p : overAt x (Jet k Unit p) ⟶ t.G) ^ p = 1 → ∀ (z : Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p)) (J : (Sp (Jet (Jet k (Fin 1 × Fin d) m) Unit p) ⟶ t.G.left) → t.PP.L.ι), Good t.PP.L z J → val (peG t x d g.x g.e (p + m + 1) ![fun j => psIn d (p + m + 1) (![0] : Fin 1 → Fin 2) (g.B.A.act (p : 𝓞 E) j), fun j => MvPolynomial.X ((1 : Fin 2), j)]) (homAt x (jq w p m)).left z J = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Coc.Pf.peG_act_one | exact GlobalTheory.CompanionTheory.Ar.Coc.Pf.peG_act_one | (intros; apply GlobalTheory.CompanionTheory.Ar.Coc.Pf.peG_act_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GoodOriginRootWeightBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_origin_root_weight_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [DecidableEq (CMType H)] (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : Top.GoodOrigin Y T) (B : ℕ) (b₀ : T.Comp) (lam : Top.Wt (CMType H) (Dw.p + Dw.q)) (n' : Option (RootIx Dw) → ℤ), (∀ j, (n' j : ℝ) = (T.M B b₀).coef lam 0 j) → Top.RegDominant lam → ∃ (q₀ : ℕ) (n₀ : Option (RootIx Dw) → ℤ) (ε : (T.M B b₀).Ω) (u : MRing (T.M B b₀).ι) (C s₀ : ℝ), 0 < q₀ ∧ (∀ j, (n₀ j : ℝ) = q₀ * (T.M B b₀).coef T.nu (-1) j) ∧ ε ≠ 0 ∧ ε ∈ chartLatNm (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a 1 ∧ Small.IsFormOff (mCoordIdeal (T.M B b₀).y) u ∧ 0 ≤ C ∧ 0 < s₀ ∧ ∀ s : ℝ, 0 < s → s ≤ s₀ → ∀ z ∈ mcPts (mCoordIdeal (T.M B b₀).y), MvPolynomial.aeval z u ≠ 0 → ∀ x : ℂ, Small.HasVal (T.M B b₀).y (Top.combLine ((T.M B b₀).line 1) n₀).a ε z x → x ≠ 0 → s / q₀ * Real.log ‖x‖ + (T.M B b₀).weight (Top.scale s) (lam - s • T.nu) s z ≤ C * s + Real.log (∏ r, ((o.toTowerOrigin.Or B b₀).sing r).h z ^ n' (some r)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.good_origin_root_coefficients | exact GlobalTheory.CompanionTheory.Ar.Small.good_origin_root_coefficients | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.good_origin_root_coefficients <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeComponentTwistEigenCompatStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_component_twist_eigen_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F)
    (Y : Model Xo c β) (Y' : Model Xo c β') (g : HostAut H) (Φ : Xo.X ≅ Xo.X)
    (n : SABMap (twistSAB Xo.univ.t g) Xo.univ.t Φ.hom) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K]
    (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (A' : HodgeCpt Y' S y)
    (e : A'.X ≅ A.X) (x x' : Sp Ω ⟶ Xo.XF c),
    Mono (spMap β) → Mono (spMap β') → Φ.hom ≫ Xo.s = Xo.s → A'.ξ ≫ e.hom = A.ξ → A.ξ ≫ A.f = x ≫ Y.j → A'.ξ ≫ A'.f = x' ≫ Y'.j →
    x' ≫ pullback.fst _ _ = x ≫ pullback.fst _ _ ≫ Φ.hom → x' ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ →
    A.cst = A'.cst → x ≫ pullback.snd _ _ = spMap A.cst → (∀ p ∈ S, A'.R p = A.R p) →
    ∀ (t : SAB H A'.X) (tΩ : SAB H (Sp Ω)) (k : SABMap t A.t e.hom) (m : SABMap tΩ t A'.ξ)
      (mA' : SABMap (twistSAB tΩ g) A'.t A'.ξ) (u : SABMap tΩ Y.oF.t x)
      (u' : SABMap (twistSAB tΩ g) Y'.oF.t x') (M₁ : LieModel t.G A'.ξ A.Li) (φ : A.Li ≃ₗ[Ω] A'.Li),
      m.φ ≫ k.φ ≫ A.m.φ = u.φ ≫ Y.m.φ → mA'.φ ≫ A'.m.φ = u'.φ ≫ Y'.m.φ →
      u'.φ ≫ Y'.m0.toSABMap.φ = u.φ ≫ Y.m0.toSABMap.φ ≫ n.φ →
      (∀ v, (M₁.pt v).left ≫ k.φ = (A.M.pt v).left) → (∀ v, ∃ w : epsAt (𝟙 (Sp Ω)) ⟶ tΩ.G, w.left ≫ m.φ = (M₁.pt v).left ∧ w.left ≫ mA'.φ = (A'.M.pt (φ v)).left) → (∀ N, FullTorsion A.t.G A.ξ N → FullTorsion t.G A'.ξ N) → (∀ (q : Cpt A'.ξ) (h : genPt A.ξ ⤳ e.hom q.1), regAt A'.ξ q = regAt A.ξ ⟨e.hom q.1, h⟩ ∧
        (M₁.lat q : Set A.Li) = A.M.lat ⟨e.hom q.1, h⟩ ∧
        ∀ N, (M₁.htOm t.PP.L N q : Set (Module.Dual Ω A.Li)) = A.M.htOm A.t.PP.L N ⟨e.hom q.1, h⟩) →
      ∀ z : Sp ℂ ⟶ A'.X, A'.Interior z → ∀ (r : ℕ) (b : Fin r → A.Li) (Γ : Matrix (Fin r) (Fin r) ℂ),
        M₁.GramAt t.PP.L z b Γ ↔ A'.M.GramAt A'.t.PP.L z (fun i => φ (b i)) Γ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.hodge_component_twist_eigen_compat | exact GlobalTheory.CompanionTheory.Relay.hodge_component_twist_eigen_compat | (intros; apply GlobalTheory.CompanionTheory.Relay.hodge_component_twist_eigen_compat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeInnerProductOnSpanStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_inner_product_on_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S' S : Scheme.{0}) (t₀ : SAB H S') (t : SAB H S) (f : S' ⟶ S) (_ : SABMap t₀ t f) (z₀ : Sp ℂ ⟶ S') (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel t.G (z₀ ≫ f) V) (core : InnerProductSpace.Core ℂ V) (W : Set V), (0 : V) ∈ W → Submodule.span ℂ W = ⊤ → (∀ a ∈ W, ∀ b ∈ W, HodgeIP t.G t.PP.L (z₀ ≫ f) (Mz.pt a) (Mz.pt b) (core.inner a b)) → ∀ a b : V, HodgeIP t.G t.PP.L (z₀ ≫ f) (Mz.pt a) (Mz.pt b) (core.inner a b) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span | exact GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span | (intros; apply GlobalTheory.CompanionTheory.Ar.HodgeExt.hodgeInnerProduct_of_span <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

open AlgebraicGeometry CategoryTheory

abbrev gen {X : Scheme.{0}} (T : CDVR) (zV : Spec (CommRingCat.of T.V) ⟶ X) : Spec (CommRingCat.of T.Fr) ⟶ X :=
  Spec.map (CommRingCat.ofHom (algebraMap T.V T.Fr)) ≫ zV

def ReadsPt {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (A : Subring Ω) (T : CDVR)
    (evT : A →+* T.Fr) (zV : Spec (CommRingCat.of T.V) ⟶ X) : Prop :=
  ∀ a : A, ValAt ξ (gen T zV) (a : Ω) (evT a)

def TriIn {F EC : Type} [Field F] [AddCommGroup EC] [Module F EC] {r : ℕ} (u : Fin r → EC) (d : Fin r → F)
    (v : Fin r → EC) : Prop :=
  ∀ i, ∃ cf : Fin r → F, cf i = d i ∧ (∀ j, i < j → cf j = 0) ∧ v i = ∑ j, cf j • u j

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β}
  {SS : Finset ℕ} {RM : Top.RootModel (CMType H) (Dw.p + Dw.q)}
  {Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))} {Fx : FixedData Y Sys}

def IsFrameVec (Or : RootOrigin Y SS RM Fx) {T : CDVR} (io : c.F →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr)
    {zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X} {EC : Type} [AddCommGroup EC] [Module T.Fr EC]
    (MC : LieModel Or.𝔐.t.G (gen T zV) EC) (w : EC) (s : CMType H ⊕ CMType H) (i : Fin (labelRk Dw s)) : Prop :=
  letI := io.toAlgebra
  (MC.pt w).left ≫ Or.𝔐.m.φ = Small.tanY Y zT (Small.labelC s) (Small.labelFin Dw s i)

def lieEig (Or : RootOrigin Y SS RM Fx) {T : CDVR} {zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X} {EC : Type}
    [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] (MC : LieModel Or.𝔐.t.G (gen T zV) EC)
    [IsScalarTower T.V T.Fr EC] (ρC : 𝓞 E →+* Module.End T.Fr EC) (σ : 𝓞 E →+* T.V) : Submodule T.V EC :=
  Or.𝔐.M.fibAt Or.𝔐.M.lat zV MC ⊓ (eigSp ρC ((algebraMap T.V T.Fr).comp σ)).restrictScalars T.V

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSectionsCuspLaws
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.lattice_sections_cusp_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (a : WZ E) (x : ℝ), (Lat.secZ Xo c a 0 = secZ Xo c a ∧ Lat.cuspZ U a 0 = cuspZ Xo c U a ∧ Lat.lieZ Dw x a = lieFacZ Dw x a ∧ ∀ f, f ∈ Lat.latZ U a 0 ↔ f ∈ cuspZ Xo c U a ∧ ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) ∧ ∀ b, WEq Dw a b → secZ Xo c a = secZ Xo c b ∧ cuspZ Xo c U a = cuspZ Xo c U b ∧ lieFacZ Dw x a = lieFacZ Dw x b ∧ towerWt Dw a = towerWt Dw b ∧ (∀ σ, GoodEmb c σ → laZ (U σ) a = laZ (U σ) b) ∧ ∀ Z, cuspOn U h a Z = cuspOn U h b Z ∧ latOn U h a Z = latOn U h b Z := by
  first | exact @PositivityTheory.UnitarySelfGeneration.y_br_lat | exact PositivityTheory.UnitarySelfGeneration.y_br_lat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelCoverStHolds
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.XR

theorem genPt_spMap_comp {X : Scheme.{0}} {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω) (ξ : Sp K ⟶ X) :
    genPt (spMap i ≫ ξ) = genPt ξ := by
  unfold genPt
  show ξ ((spMap i) (closedPoint Ω)) = ξ (closedPoint K)
  congr 1
  first
  | exact Subsingleton.elim _ _
  | exact IsLocalRing.comap_closedPoint i
  | exact (IsLocalRing.PrimeSpectrum.comap_closedPoint i)

theorem finite_descResidueField_spMap_comp {X : Scheme.{0}} {K Ω : Type} [Field K] [Field Ω] (i : K →+* Ω)
    (hi : i.Finite) (ξ : Sp K ⟶ X) (hξ : Function.Surjective (Scheme.stalkClosedPointTo ξ).hom) :
    (Scheme.descResidueField (Scheme.stalkClosedPointTo (spMap i ≫ ξ))).hom.Finite := by
  have hA : ∀ p : Sp K, (ξ.stalkMap p).hom.Finite := by
    intro p
    obtain rfl : p = closedPoint K := Subsingleton.elim _ _
    apply RingHom.Finite.of_surjective
    have e : Scheme.stalkClosedPointTo ξ =
        ξ.stalkMap (closedPoint K) ≫ (stalkClosedPointIso (CommRingCat.of K)).hom := by
      first
      | rfl
      | simp [Scheme.stalkClosedPointTo]
    intro y
    obtain ⟨a, ha⟩ := hξ ((stalkClosedPointIso (CommRingCat.of K)).hom y)
    refine ⟨a, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of K)).hom).1
    rw [← ha, e]
    rfl
  have hB : (Scheme.stalkClosedPointTo (spMap i)).hom.Finite := by
    change (Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i))).hom.Finite
    have h := Scheme.germ_stalkClosedPointTo_Spec (CommRingCat.ofHom i)
    refine RingHom.Finite.of_comp_finite
      (f := ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (Spec (CommRingCat.of K)).presheaf.germ ⊤
        ((Spec.map (CommRingCat.ofHom i)) (closedPoint Ω)) trivial).hom) ?_
    rw [← CommRingCat.hom_comp, Category.assoc, h, Iso.inv_hom_id_assoc]
    simpa using hi
  have hC : (Scheme.stalkClosedPointTo (spMap i ≫ ξ)).hom.Finite := by
    have e2 := Scheme.stalkClosedPointTo_comp (R := CommRingCat.of Ω) (spMap i) ξ
    have h3 := hB.comp (hA ((spMap i) (closedPoint Ω)))
    rw [← CommRingCat.hom_comp] at h3
    first
    | exact e2 ▸ h3
    | exact (congrArg (fun φ => (CommRingCat.Hom.hom φ).Finite) e2).mpr h3
    | (rw [e2]; exact h3)
  refine RingHom.Finite.of_comp_finite (f := (X.residue _).hom) ?_
  rw [← CommRingCat.hom_comp, Scheme.residue_descResidueField]
  exact hC

theorem levelCover : LevelCoverSt := by
  intro E _ _ _ H D l Xo c Y e he N hN
  obtain ⟨K, _, _, n0, x0, y0, htie, -, hgen⟩ := GlobalTheory.T.generic_point_normal_coords E H D l Xo c Y e he
  obtain ⟨Ω, _, _, z, ev, hfd, hfull⟩ := GlobalTheory.T.exists_full_level_finite_extension E H D l Xo c _ _ Y K y0 N hN
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  haveI : NumberField c.F :=
    { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hproj : IsProjOver (Y.s ≫ spMap (Int.castRingHom (𝓞 c.F))) :=
    GlobalTheory.T.projective_over_restrict_int _ Y.X Y.s Y.proj
  have hsurj : Function.Surjective (Scheme.stalkClosedPointTo (y0 ≫ Y.j)).hom := by
    obtain ⟨hg, -, -, -⟩ := htie
    obtain ⟨hb, -⟩ := hg
    exact hb.2
  have hi : (algebraMap K Ω).Finite := by
    first
    | exact RingHom.finite_algebraMap.mpr hfd
    | exact hfd
  have hfin := finite_descResidueField_spMap_comp (algebraMap K Ω) hi (y0 ≫ Y.j) hsurj
  obtain ⟨n, x, M, π, hMn, hπ, hMπ⟩ :=
    GlobalTheory.T.exists_finite_normal_model_of_residue_finite Y.X _ hproj Ω (spMap (algebraMap K Ω) ≫ (y0 ≫ Y.j)) hfin
  have hMg : IsCptGen M.ξ := by
    obtain ⟨hg, -, -, -⟩ := M.tie
    exact hg
  obtain ⟨t, hx, ev', h1, h2, h3⟩ :=
    GlobalTheory.T.full_level_generic_cover E H D l Xo c Y K Ω (algebraMap K Ω) y0 N z ev hN hfull M.X M.ξ hMg hMn π hMπ
  refine ⟨Ω, inferInstance, inferInstance, n, x, M, π, spMap (algebraMap K Ω) ≫ y0, t, hx, z, ev',
    hMn, hπ, ?_, ?_, h1, h2, h3⟩
  · show genPt (M.ξ ≫ π) = e
    rw [hMπ, genPt_spMap_comp, hgen]
  · rw [hMπ, Category.assoc]

end GlobalTheory.CompanionTheory.Ar.XR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalPointSpecializesComponentStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_point_specializes_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (U : Set (Xo.XF c)) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (Z : CptOver Y U) (T : Type) [CommRing T] [IsLocalRing T] (y : Sp T ⟶ Xo.XF c) (c₀ : c.F →+* T), y ≫ pullback.snd _ _ = spMap c₀ → centre y ∈ U → ∃ (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (κ : c.F →+* Y.X.presheaf.stalk (centre (y ≫ Y.j))), (genMap (Z.ξ₀ ≫ Y.j) ⟨_, h⟩).comp κ = Z.inc ∧ (Scheme.stalkClosedPointTo (y ≫ Y.j)).hom.comp κ = c₀ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef | exact GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef | (intros; apply GlobalTheory.CompanionTheory.Ar.LocFn.Coef.exists_coef <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingEssFiniteTypeStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_ring_ess_finite_type : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (w : (Σ k, J k) → K) (W : Ideal (MRing J)) (c : ∀ k, J k), (mCoordIdeal w).IsPrime → W.IsPrime → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → ∀ [Algebra (ZMod p) (locRing (mCoordIdeal w) W)], Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.essFiniteType_locRing | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.essFiniteType_locRing | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.essFiniteType_locRing <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogPrimeMemDivisorSupportStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multihomog_prime_mem_divisor_support : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K), Birational w → ∀ (W : Ideal (MRing J)) (c : ∀ k, J k), W.IsPrime → IsMultiHomogIdeal W → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) → ∀ (k : B) (c₀ : J k), w ⟨k, c₀⟩ ≠ 0 → (X ⟨k, c₀⟩ : MRing J) ∈ W → W ∈ (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)}).minimalPrimes := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord | exact GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord | (intros; apply GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin.mem_minimalPrimes_of_coord <;> assumption)
end

