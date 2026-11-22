import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0311
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0013
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Formalism.LocalRingCardinality.Bundle0004
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0461
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0542
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralZpowOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LUnifOfRhoGeoEquivAll
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2171
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0600
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0602
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MajPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0096

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FromModelNeg
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LineNorm

namespace GlobalTheory.LineNorm.Neg

theorem pull_dual_g {X Y : Scheme.{0}} (L : LB X) (f : Y ⟶ X) (i j : (L.pull f).ι) :
    ((CechPic.dual L).pull f).g i j = ((L.pull f).g i j)⁻¹ := by
  have key {A B C : Type} [CommGroup A] [CommGroup B] [CommGroup C] (p : B →* C) (q : A →* B) (a : A) :
      ∏ _k : PUnit.{1}, p (q a⁻¹) ^ (1 : ℤ) = (∏ _k : PUnit.{1}, p (q a) ^ (1 : ℤ))⁻¹ := by
    simp
  exact key _ _ (L.g (i PUnit.unit) (j PUnit.unit))

theorem presents_neg {X Y : Scheme.{0}} [IsIntegral Y] {L : LB X} (hL : L.IsLB) (f : Y ⟶ X)
    {D : CartierDiv Y} {r : (L.pull f).ι → Y.functionFieldˣ} (h : Presents D (L.pull f) r) :
    Presents (-D) ((CechPic.dual L).pull f) (fun i => (r i)⁻¹) := by
  refine ⟨LB.isLB_pull (CechPic.isLB_dual hL) f, fun i j hij => ?_, fun i x hx => (h.isEqn i x hx).neg⟩
  have e := h.isRatSec i j hij
  have e' : fnOf _ hij (((CechPic.dual L).pull f).g i j).val = (fnOf _ hij ((L.pull f).g i j).val)⁻¹ :=
    (congrArg (fun u : Γ(Y, (L.pull f).U i ⊓ (L.pull f).U j)ˣ => fnOf _ hij u.val)
      (pull_dual_g L f i j)).trans (map_units_inv _ _)
  refine Eq.trans ?_ (congrArg (· * _) e').symm
  rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, e, mul_inv]
  rfl

theorem valAt_inv {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] {y : Sp K ⟶ Z}
    {f : Z.functionField} (hf : UnitAt (below y) f) : valAt y f⁻¹ = (valAt y f)⁻¹ := by
  obtain ⟨_, ⟨a, rfl⟩, rfl⟩ := hf
  rw [← map_units_inv, SmallSec.valAt_algebraMap, SmallSec.valAt_algebraMap, map_units_inv]

theorem fromModel_neg (F : Type) [Field F] [NumberField F] (Y : Var F) (Δ : Y.Dv) (t : Y.X → Y.Fnˣ)
    (φ : PtFn Y) (ht : ∀ y, Δ.IsEqn y (t y)) (h : FromModel Y Δ t φ) :
    FromModel Y (-Δ) (fun y => (t y)⁻¹) (fun v e y => -φ v e y) := by
  obtain ⟨M, L, m, r, hL, hP, hφ⟩ := h
  refine ⟨M, CechPic.dual L, m, fun i => (r i)⁻¹, CechPic.isLB_dual hL, ?_, fun v e y yt i hy hi => ?_⟩
  · rw [smul_neg]
    exact presents_neg hL M.j hP
  · have hmem : below y.1 ∈ (L.pull M.j).U i := by
      have h1 : (y.1 ≫ M.j) (IsLocalRing.closedPoint _) ∈ L.U (i PUnit.unit) := by
        rw [← hy]
        exact hi (Set.mem_univ _)
      exact Set.mem_iInter.2 fun _ => h1
    have hu : UnitAt (below y.1) (((t (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn) := by
      have := ((ht (below y.1)).nsmul m).iff_unitAt.1 (hP.isEqn i _ hmem)
      rwa [← Units.val_div_eq_div_val, div_eq_inv_mul, ← inv_pow] at this
    have e1 : (((t (below y.1))⁻¹⁻¹ ^ (m : ℕ) * (r i)⁻¹ : Y.Fnˣ) : Y.Fn) =
        (((t (below y.1))⁻¹ ^ (m : ℕ) * r i : Y.Fnˣ) : Y.Fn)⁻¹ := by
      rw [← Units.val_inv_eq_inv_val, mul_inv, ← inv_pow]
    change ((m : ℕ) : ℝ) * -φ v e y = Real.log (e.w (valAt y.1
      (((t (below y.1))⁻¹⁻¹ ^ (m : ℕ) * (r i)⁻¹ : Y.Fnˣ) : Y.Fn)))
    rw [e1, valAt_inv hu, map_inv₀, Real.log_inv, mul_neg, hφ v e y yt i hy hi]

end GlobalTheory.LineNorm.Neg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeometricHalfCoreFormsUniformisationIntegral
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RealGeo
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RealGeoIn

section

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}

set_option maxHeartbeats 1000000 in

theorem mkStable_of_rhoGeo (t : FWTie T R κ v₀) (hp : ∀ i, OMPins T R κ v₀ O i) (hr : RhoGeo t O) (i : Fin D.R.m) :
    (R.FW i).MKStable := by
  have hact : ActLev (Xo := T.Q.Xo ((i : ℕ) + 1)) T.Q.c (O i).lev2 := (hp i).2.act.1
  by_cases hk : ActKeeps (κ := κ) O i
  · have h0 := (hr i).1 hk
    intro g x
    have key : ∀ hx : x ∈ (R.FW i).WK, (R.FW i).ρ g x ∈ (R.FW i).WK ∧ (x ∈ (R.FW i).MK → (R.FW i).ρ g x ∈ (R.FW i).MK) := by
      intro hx
      obtain ⟨f, hf⟩ := (t.e i).surjective ⟨x, hx⟩
      have hfx : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = x := congrArg Subtype.val hf
      subst hfx
      obtain ⟨h1, h2⟩ := h0 g f
      rw [← h2]
      refine ⟨(t.e i _).2, fun hm => (t.mem_MK i _).2 ?_⟩
      exact GlobalTheory.LevActInt.intAll_actLev T κ i (O i).lev2 t.laws hact g f ⟨_, h1⟩ rfl ((t.mem_MK i f).1 hm)
    exact ⟨fun hx => (key hx).1, fun hx => (key hx.1).2 hx⟩
  · intro g x
    rw [(hr i).2 hk g]
    exact ⟨id, id⟩

end

set_option maxHeartbeats 1000000 in

theorem inGeo_and_lUnif_and_lIntegral : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (ph : Fin D.R.m → ℂ) (B : GeoHalf T R ph), PreChar R → R.grp_chiW → T.pb = R.C.P.pb → 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → InGeo B ∧ R.LUnif ∧ R.LIntegral := by
  intro hP D G _ _ Pl0 T0 A T _ R ph B hC hχ hp hn
  have ht : TieIn T R B.κ B.v₀ := ⟨B.fw.laws, B.fw.alg_eq, B.fw.kap, B.fw.hv₀, B.fw.chiR, B.fw.x0⟩
  have hJ := GlobalTheory.CuspValues.jEvExists_and_jEvBar D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hI := GlobalTheory.MemberEvalInj.evInj_of_tieIn D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hU := GlobalTheory.ReadingSpan.jUnif hP D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp hJ.1 hJ.2 hI hn
  have hL := GlobalTheory.MemberLatFull.latFull_of_tieIn D G Pl0 T0 A T R B.κ B.v₀ hC.lev hC.models ht hp
  have hG := GlobalTheory.geoAct_of_ties_of_equivAll T R B.κ B.v₀ B.O hC.lev hC.models.inf hC.models.HW ht hp B.pins B.equivAll
  have hx := GlobalTheory.T.exists_equivariant_unit_constants_goodEmbedding T R B.κ B.v₀ B.O hC.lev ht hp B.pins
  refine ⟨⟨hJ.1, hJ.2, hI, hU, hG, hL, B.fw.dimMatch⟩, fun i σ => ?_, fun i => ?_⟩
  · exact ⟨(GlobalTheory.TiedUnif.indep_span_of_tie B.fw hC.models.HW B.bar hU i σ).1,
      (GlobalTheory.TiedUnif.indep_span_of_tie B.fw hC.models.HW B.bar hU i σ).2,
      GlobalTheory.TiedUnif.rhoIs_of_eqAt B.fw hC.models.HW hC.models.gW hχ B.bar B.rhoGeo hU i σ
        (fun h hV => B.equivAll i _ h hV (hx i _ h hV))
        fun h hV => B.equivAll i _ (good_resC T h) hV (hx i _ (good_resC T h) hV)⟩
  · exact ⟨B.fw.ks i, GlobalTheory.GoodLat.mkFull_of_tie B.fw hL i, mkStable_of_rhoGeo B.fw B.pins B.rhoGeo i⟩

end GlobalTheory.RealGeoIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO SCF)

namespace GlobalTheory.HTLine

attribute [local instance] Over.cartesianMonoidalCategory

section Lattice

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X) {R : Type} [CommRing R] (x : Sp R ⟶ X)

def Pres (p : ℕ) (b : Bool) {g M : ℕ} (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left))
    (h : Fin (M + 1) → Fin g → R) : Prop :=
  (∃ N : ℕ, ∀ i, Pi.single i ((p : R) ^ N) ∈ Submodule.span R (Set.range h)) ∧
  ∀ (C : SCF p) (φ : R →+* ↥(intO ↥C.S)) (cf : Fin g → ↥C.S) (w : Sp (DualNumber ↥C.S) ⟶ t.G.left),
    IsCombAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x)
      (fun i => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ e i) cf w →
    (w ∈ lat t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) b ↔ ∀ j, ‖∑ i, ((φ (h j i) : ↥(intO ↥C.S)) : ↥C.S) * cf i‖ ≤ 1)

end Lattice

section Ratio

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def RatioAt (Z : Mdl Y i₀) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) (U : Z.X.Opens) {m m' : ℕ} (A : Fin m → Γ(Z.X, U))
    (B : Fin m' → Γ(Z.X, U)) : Prop :=
  (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range A)).radical ∧ (p : Γ(Z.X, U)) ∈ (Ideal.span (Set.range B)).radical ∧
  ∀ (y : Z.Pt) a (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen → ⊤ ≤ y.z ⁻¹ᵁ U →
    lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p true st - lnStep (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ) p false st =
      Real.log ‖fun j => valF y.gen U (A j)‖ - Real.log ‖fun j => valF y.gen U (B j)‖

def HasRatio (Z : Mdl Y i₀) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : Prop :=
  ∀ z : Z.X, ∃ (U : Z.X.Opens) (m m' : ℕ) (A : Fin m → Γ(Z.X, U)) (B : Fin m' → Γ(Z.X, U)),
    z ∈ U ∧ IsAffineOpen U ∧ RatioAt Z st U A B

def HasPRatio (Z : Mdl Y i₀) (st : ((E →+* ℂ) × ℕ) ⊕ ℕ) : Prop :=
  ∀ z : Z.X, ∃ (U : Z.X.Opens) (A B : Γ(Z.X, U)), z ∈ U ∧ IsAffineOpen U ∧ RatioAt Z st U ![A] ![B]

end Ratio

end GlobalTheory.HTLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameOrbitIsotropicVectorShort
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)

namespace GlobalTheory.OrbitShort

theorem quad_bound {V : Type} [AddCommGroup V] [Module ℂ V] (m : ℂ → V → ℝ) (T : ℝ) (M : ℕ) (hM : 0 < M) (b ξ : V)
    (h0 : ∀ w : ℂ, T < w.im → ∀ v, 0 ≤ m w v)
    (hsm : ∀ (w : ℂ) (k : ℕ) (v : V), m w ((k : ℂ) • v) = (k : ℝ) ^ 2 * m w v)
    (hpar : ∀ (w : ℂ) (u v : V), m w (u + v) + m w (u - v) = 2 * m w u + 2 * m w v)
    (hH : ∀ w w' : ℂ, T < w.im → T < w'.im → ∀ v,
      m w' v ≤ (2 + ‖w - w'‖ ^ 2 / ((w.im - T) * (w'.im - T))) * m w v)
    (hξ : ∀ w : ℂ, T < w.im → m (w + M) ξ = m w ξ)
    (hb : ∀ w : ℂ, T < w.im → ∀ k : ℕ, m (w + M) (b + ((k + 1 : ℕ) : ℂ) • ξ) = m w (b + (k : ℂ) • ξ)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, T + 1 < w.im → m w ξ * (w.im - T) ≤ A := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hξk : ∀ (k : ℕ) (w : ℂ), T < w.im → m (w + k * M) ξ = m w ξ := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      have e : w + ((k + 1 : ℕ) : ℂ) * M = (w + k * M) + M := by push_cast; ring
      rw [e, hξ _ (by simpa using hw), ih]
  have hbk : ∀ (k : ℕ) (w : ℂ), T < w.im → m (w + k * M) (b + (k : ℂ) • ξ) = m w b := by
    intro k w hw
    induction k with
    | zero => simp
    | succ k ih =>
      have e : w + ((k + 1 : ℕ) : ℂ) * M = (w + k * M) + M := by push_cast; ring
      rw [e, hb _ (by simpa using hw), ih]
  set w0 : ℂ := ((T + 1 : ℝ) : ℂ) * Complex.I with hw0
  have hw0im : w0.im = T + 1 := by simp [hw0]
  have hw0re : w0.re = 0 := by simp [hw0]
  have hm0 : 0 ≤ m w0 b := h0 _ (by rw [hw0im]; linarith) _
  refine ⟨(M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * m w0 b)), by positivity, ?_⟩
  have strip : ∀ w : ℂ, T + 1 < w.im → 0 ≤ w.re → w.re < M → m w ξ * (w.im - T) ≤
      (M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * m w0 b)) := by
    intro w hw hr0 hr1
    have hw' : T < w.im := by linarith
    obtain ⟨y, hy⟩ : ∃ y, y = w.im - T := ⟨_, rfl⟩
    have hy1 : 1 < y := by linarith
    have hy0 : 0 < y := by linarith
    rw [← hy]

    have g1 : m w b ≤ (3 + (M : ℝ) ^ 2) * y * m w0 b := by
      refine (hH w0 w (by rw [hw0im]; linarith) hw' b).trans (mul_le_mul_of_nonneg_right ?_ hm0)
      have e1 : ‖w0 - w‖ ^ 2 = w.re ^ 2 + (y - 1) ^ 2 := by
        rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, hw0im, hw0re, hy]; ring
      rw [e1, hw0im, ← hy, show (T + 1 - T) * y = y by ring]
      have : (w.re ^ 2 + (y - 1) ^ 2) / y ≤ (1 + (M : ℝ) ^ 2) * y := by
        rw [div_le_iff₀ hy0]
        have a1 : w.re ^ 2 ≤ (M : ℝ) ^ 2 := by nlinarith
        have a2 : (M : ℝ) ^ 2 * 1 ≤ (M : ℝ) ^ 2 * (y * y) := mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
        nlinarith
      nlinarith
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℕ, y ≤ k * M ∧ (k : ℝ) * M ≤ y + M := by
      refine ⟨⌈y / M⌉₊, ?_, ?_⟩
      · rw [← div_le_iff₀ hMr]; exact Nat.le_ceil _
      · have := (Nat.ceil_lt_add_one (a := y / M) (by positivity)).le
        have h2 := mul_le_mul_of_nonneg_right this hMr.le
        rwa [add_mul, div_mul_cancel₀ _ hMr.ne', one_mul] at h2
    have hwk : T < (w + k * M).im := by simpa using hw'
    have hmb : 0 ≤ m w b := h0 _ hw' _
    have g2 : m (w + k * M) b ≤ (2 + (1 + (M : ℝ)) ^ 2) * m w b := by
      refine (hH w (w + k * M) hw' hwk b).trans (mul_le_mul_of_nonneg_right ?_ hmb)
      have e1 : ‖w - (w + k * M)‖ ^ 2 = ((k : ℝ) * M) ^ 2 := by
        rw [show w - (w + k * M) = -(k * M) by ring, norm_neg, norm_mul]; simp
      have e2 : (w + k * M).im = w.im := by simp
      rw [e1, e2, ← hy]
      have : ((k : ℝ) * M) ^ 2 / (y * y) ≤ (1 + (M : ℝ)) ^ 2 := by
        rw [div_le_iff₀ (by positivity)]
        have a1 : (k : ℝ) * M ≤ (1 + M) * y := by nlinarith
        have a2 := pow_le_pow_left₀ (by positivity) a1 2
        nlinarith
      linarith
    have g3 : (k : ℝ) ^ 2 * m w ξ ≤ (6 + 2 * (1 + (M : ℝ)) ^ 2) * m w b := by
      have p := hpar (w + k * M) (b + (k : ℂ) • ξ) b
      rw [show b + (k : ℂ) • ξ - b = (k : ℂ) • ξ by abel, hsm, hξk k w hw', hbk k w hw'] at p
      have := h0 _ hwk (b + (k : ℂ) • ξ + b)
      linarith
    have hmξ : 0 ≤ m w ξ := h0 _ hw' _
    have g4 : y ^ 2 * m w ξ ≤ ((k : ℝ) * M) ^ 2 * m w ξ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hy0.le hk1 2) hmξ
    have g5 : (M : ℝ) ^ 2 * ((k : ℝ) ^ 2 * m w ξ) ≤
        (M : ℝ) ^ 2 * ((6 + 2 * (1 + (M : ℝ)) ^ 2) * ((3 + (M : ℝ) ^ 2) * y * m w0 b)) :=
      mul_le_mul_of_nonneg_left (g3.trans (mul_le_mul_of_nonneg_left g1 (by positivity))) (by positivity)
    refine le_of_mul_le_mul_left ?_ hy0
    nlinarith
  intro w hw
  have hper : Function.Periodic (fun s : ℝ => m ((s : ℂ) + (w.im : ℂ) * Complex.I) ξ) (M : ℝ) := by
    intro s
    have e : ((s + (M : ℝ) : ℝ) : ℂ) + (w.im : ℂ) * Complex.I = ((s : ℂ) + (w.im : ℂ) * Complex.I) + M := by
      push_cast; ring
    show m _ ξ = m _ ξ
    rw [e, hξ _ (by simp; linarith)]
  obtain ⟨s, hs, hse⟩ := hper.exists_mem_Ico₀ hMr w.re
  simp only [Complex.re_add_im] at hse
  have := strip ((s : ℂ) + (w.im : ℂ) * Complex.I) (by simpa using hw) (by simpa using hs.1) (by simpa using hs.2)
  rw [hse]
  simpa using this

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ} (X : Data E N)

open ReciprocityTheory.ChartRestriction.G.FD in

theorem maj_natCast_smul (x : Frame X.Ψ N) (τ : X.Ψ) (k : ℕ) (v : Fin N → ℂ) :
    X.maj x τ ((k : ℂ) • v) = (k : ℝ) ^ 2 * X.maj x τ v := by
  unfold Data.maj Data.posPart
  have e : ∀ a b c : ℂ, (k : ℂ) * a * b * ((k : ℂ) * c) = (((k : ℝ) ^ 2 : ℝ) : ℂ) * (a * b * c) := by
    intro a b c; push_cast; ring
  have e' : ∀ a : ℂ, (k : ℂ) * ((k : ℂ) * a) = (((k : ℝ) ^ 2 : ℝ) : ℂ) * a := by
    intro a; push_cast; ring
  simp only [hermC_smul_left, hermC_smul_right, map_mul, map_natCast, e, e', ← Finset.mul_sum,
    Complex.re_ofReal_mul]
  ring

open ReciprocityTheory.ChartRestriction.G.FD in

theorem maj_parallelogram (x : Frame X.Ψ N) (τ : X.Ψ) (u v : Fin N → ℂ) :
    X.maj x τ (u + v) + X.maj x τ (u - v) = 2 * X.maj x τ u + 2 * X.maj x τ v := by
  have hs : u - v = u + (-1 : ℂ) • v := by simp [sub_eq_add_neg]
  have hp : X.posPart x τ (u + v) + X.posPart x τ (u - v) = 2 * X.posPart x τ u + 2 * X.posPart x τ v := by
    unfold Data.posPart
    rw [two_mul, two_mul]
    simp only [← Complex.add_re, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    simp only [hs, hermC_add_left, hermC_smul_left, map_add, map_mul, map_neg, map_one]
    ring
  have hh : hermC τ.1 X.Gm (u + v) (u + v) + hermC τ.1 X.Gm (u - v) (u - v) =
      hermC τ.1 X.Gm u u + hermC τ.1 X.Gm u u + (hermC τ.1 X.Gm v v + hermC τ.1 X.Gm v v) := by
    simp only [hs, hermC_add_left, hermC_add_right, hermC_smul_left, hermC_smul_right, map_neg, map_one]
    ring
  have hh' := congrArg Complex.re hh
  simp only [Complex.add_re] at hh'
  unfold Data.maj
  linarith

end GlobalTheory.OrbitShort

open GlobalTheory.OrbitShort in

theorem GlobalTheory.orbit_unipotent_short : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (X : Data E N) (T : ℝ) (M : ℕ) (γ : GL (Fin N) E) (x : ℂ → Frame X.Ψ N), IsOrbit X T M γ x → ((γ : Matrix (Fin N) (Fin N) E) - 1) ^ 2 = 0 → γ ≠ 1 → ∃ (ξ : Fin N → E) (c : ℝ), X.IsIso ξ ∧ 0 < c ∧ ∀ w : ℂ, T + 1 < w.im → ∀ τ, c * (w.im - T) ≤ X.tt ξ (x w) τ := by
  intro E _ _ _ N X T M γ x ⟨hM, hγ, hd, hdom, hsh⟩ hsq hne
  have hst := X.Γ_stab γ hγ
  obtain ⟨b, hbΛ, hb⟩ : ∃ b ∈ X.Λ, Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) b ≠ 0 := by
    by_contra hc
    push_neg at hc
    apply hne
    have hz : Matrix.toLin' ((γ : Matrix (Fin N) (Fin N) E) - 1) = 0 := by
      refine LinearMap.ext_on X.Λ_span fun v hv => ?_
      rw [Matrix.toLin'_apply, hc v hv]; rfl
    have hz' : (γ : Matrix (Fin N) (Fin N) E) - 1 = 0 := Matrix.toLin'.map_eq_zero_iff.1 hz
    exact Units.ext (sub_eq_zero.1 hz')
  obtain ⟨ξ, hξ⟩ : ∃ ξ, ξ = Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) b := ⟨_, rfl⟩
  rw [← hξ] at hb
  have hγb : Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) b = b + ξ := by
    rw [hξ, Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  have hγξ : Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) ξ = ξ := by
    have : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E) - 1) ξ = 0 := by
      rw [hξ, Matrix.mulVec_mulVec, ← sq, hsq, Matrix.zero_mulVec]
    rwa [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
  have hξΛ : ξ ∈ X.Λ := by
    have h1 := (hst.2 b).1 hbΛ
    rw [hγb] at h1
    simpa using X.Λ.sub_mem h1 hbΛ
  have hiso : ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ ξ = 0 := by
    have h1 := hst.1 ξ b
    rw [hγb, hγξ] at h1
    have h2 : ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ (b + ξ) =
        ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ b + ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ ξ := by
      simp [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, mul_add, Finset.sum_add_distrib]
    rw [h2] at h1
    simpa using h1
  have hemb : ∀ (τ : X.Ψ) (v : Fin N → E),
      Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 v) =
        Data.emb τ.1 (Matrix.mulVec (γ : Matrix (Fin N) (Fin N) E) v) := by
    intro τ v
    funext i
    simp [Data.emb, Matrix.mulVec, dotProduct]
  have hshift : ∀ w : ℂ, T < w.im → ∀ (τ : X.Ψ) (v : Fin N → ℂ),
      X.maj (x (w + M)) τ (Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) v) = X.maj (x w) τ v := by
    intro w hw τ v
    obtain ⟨β, hβ, -, he⟩ := hsh w hw
    rw [he, GlobalTheory.MajInv.maj_rmul X (GlobalTheory.MajInv.lact_mem_dom X hst (hdom w hw)) hβ, GlobalTheory.MajInv.maj_lact X hst]
  have hA : ∀ τ : X.Ψ, ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, T + 1 < w.im →
      X.maj (x w) τ (Data.emb τ.1 ξ) * (w.im - T) ≤ A := by
    intro τ
    have eξ : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 ξ) = Data.emb τ.1 ξ := by
      rw [hemb, hγξ]
    have eb : Matrix.mulVec ((γ : Matrix (Fin N) (Fin N) E).map τ.1) (Data.emb τ.1 b) =
        Data.emb τ.1 b + Data.emb τ.1 ξ := by
      rw [hemb, hγb]; funext i; simp [Data.emb]
    refine quad_bound (fun w v => X.maj (x w) τ v) T M hM (Data.emb τ.1 b) (Data.emb τ.1 ξ) ?_
      (fun w k v => maj_natCast_smul X _ τ k v) (fun w u v => maj_parallelogram X _ τ u v)
      (fun w w' hw hw' v => GlobalTheory.T.majorant_harnack_holomorphic_half_plane E N X T x hd hdom w w' hw hw' τ v) ?_ ?_
    · intro w hw v
      by_cases hv : v = 0
      · have := maj_natCast_smul X (x w) τ 0 v
        subst hv
        rw [smul_zero, Nat.cast_zero, sq, zero_mul, zero_mul] at this
        exact this.ge
      · exact (X.maj_pos (hdom w hw) τ hv).le
    · intro w hw
      have := hshift w hw τ (Data.emb τ.1 ξ)
      rwa [eξ] at this
    · intro w hw k
      have := hshift w hw τ (Data.emb τ.1 b + (k : ℂ) • Data.emb τ.1 ξ)
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, eξ, eb] at this
      rw [← this]
      congr 1
      push_cast
      rw [add_smul, one_smul]; abel
  choose A hA0 hA using hA
  have hc : ∀ τ : X.Ψ, 0 < X.c τ := fun τ => by
    have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero_iff τ.1 τ.1.injective).2 X.ξ0_ne
    unfold Data.c
    positivity
  have hK0 : 0 ≤ ∑ τ, X.c τ * A τ := Finset.sum_nonneg fun τ _ => mul_nonneg (hc τ).le (hA0 τ)
  refine ⟨ξ, 1 / (1 + ∑ τ, X.c τ * A τ), ⟨hξΛ, hiso, hb⟩, by positivity, fun w hw τ => ?_⟩
  have hv : Data.emb τ.1 ξ ≠ 0 := fun h => hb (funext fun a =>
    (map_eq_zero_iff τ.1 τ.1.injective).1 (congrFun h a))
  have hp := X.maj_pos (hdom w (by linarith)) τ hv
  have hle : X.c τ * A τ ≤ ∑ τ, X.c τ * A τ :=
    Finset.single_le_sum (f := fun τ => X.c τ * A τ) (fun τ _ => mul_nonneg (hc τ).le (hA0 τ)) (Finset.mem_univ τ)
  have h1 := mul_le_mul_of_nonneg_left (hA τ w hw) (hc τ).le
  unfold Data.tt
  rw [one_div_mul_eq_div, div_le_div_iff₀ (by positivity) (mul_pos (hc τ) hp)]
  nlinarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinateLatticeIsometryDetOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontalCoordinate_lattice_isometry_det_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (Q : Di.La →+ (Letter Dw → ℂ)) (gm : Di.La ≃ₗ[𝓞 E] Di.La), IsPerBasis Di x hm → GoodPer c σ τ x hm Q → IsIsom Di gm → GoodPer c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) ∧ ‖perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom)‖ = ‖perVal c σ τ x hm Q‖ ∧ ((∀ p : ℕ, p.Prime → l.GoodAt p) → IsLev l Di gm → perVal c σ τ x hm (Q.comp gm.toLinearMap.toAddMonoidHom) = perVal c σ τ x hm Q) := by
  first | exact @GlobalTheory.ShFam.HorIso.perVal_isom | exact GlobalTheory.ShFam.HorIso.perVal_isom | (intros; apply GlobalTheory.ShFam.HorIso.perVal_isom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HorizontalCoordinatePolynomialBoundStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.horizontalCoordinate_polynomial_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (σ : c.F →+* ℂ) (Di : Datum H) (τ : E →+* ℂ) (x : Idx Dw τ → Di.La) (hm : Matrix (Idx Dw τ) (Idx Dw τ) E) (g r : ℕ) (T₀ : Di.La ≃+ (Fin r → ℤ)) (ρ : Fin g → Fin r → ℂ), IsPerBasis Di x hm → ∃ (C : ℝ) (k : ℕ), ∀ (Q : Di.La →+ (Letter Dw → ℂ)) (W : Matrix (Letter Dw) (Fin g) ℂ) (Wi : Matrix (Fin g) (Letter Dw) ℂ) (lam : Fin r → Fin g → ℂ) (A : ℝ), GoodPer c σ τ x hm Q → W * Wi = 1 → Wi * W = 1 → (∀ v, ∑ z, Q v z • W z = ∑ m, T₀ v m • lam m) → (∀ j, ∑ m, ρ j m • lam m = Pi.single j 1) → 1 ≤ A → (∀ z j, ‖W z j‖ ≤ A) → (∀ j z, ‖Wi j z‖ ≤ A) → (∀ m j, ‖lam m j‖ ≤ A) → ‖perVal c σ τ x hm Q‖ ≤ C * A ^ k ∧ ‖(perVal c σ τ x hm Q)⁻¹‖ ≤ C * A ^ k := by
  first | exact @GlobalTheory.ShFam.Hor.PolyBd.perVal_bound | exact GlobalTheory.ShFam.Hor.PolyBd.perVal_bound | (intros; apply GlobalTheory.ShFam.Hor.PolyBd.perVal_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntStepZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tau tau_le spMap_ev ev_res ev_spMap le_preimage_inf le_preimage_map le_preimage_mono le_preimage_comp tanPull initSpan mem_initSpan)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlas_integral_at_index_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : ValuationSubring c.F) [IsDiscreteValuationRing V] (M : Model Xo c V.subtype) (X : Scheme.{0}) (π : X ⟶ M.X) (ty : (E →+* ℂ) → Finset ℕ) (A : Atlas M π ty) (σ : E →+* ℂ), IntStep A σ 0 := by
  first | exact @GlobalTheory.DRFlag.intStep_zero | exact GlobalTheory.DRFlag.intStep_zero | (intros; apply GlobalTheory.DRFlag.intStep_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAmpleLBOfFibres
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.AmpleFibres

theorem relAmple_restrict {S : Scheme.{0}} (U : S.Opens) [IsAffine U.toScheme] (B : Over S) {L : LB B.left}
    (hL : L.IsLB)
    (h : ReciprocityTheory.ChartRestriction.G.Out.RelAmple ((Over.pullback U.ι).obj B) (L.pull (pullback.fst B.hom U.ι))) :
    ReciprocityTheory.ChartRestriction.G.Out.RelAmple (Over.mk (B.hom ∣_ U)) (L.pull (B.hom ⁻¹ᵁ U).ι) := by
  have hφ : (pullbackRestrictIsoRestrict B.hom U).inv ≫ pullback.fst B.hom U.ι = (B.hom ⁻¹ᵁ U).ι :=
    pullbackRestrictIsoRestrict_inv_fst B.hom U
  have hsq : IsPullback (pullbackRestrictIsoRestrict B.hom U).inv (Over.mk (B.hom ∣_ U)).hom
      ((Over.pullback U.ι).obj B).hom (𝟙 U.toScheme) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    simp [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  have hL₁ : (L.pull (pullback.fst B.hom U.ι)).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _
  have hL₂ : (L.pull (B.hom ⁻¹ᵁ U).ι).IsLB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.pull_isLB hL _
  have hw : LBIso (L.pull (B.hom ⁻¹ᵁ U).ι)
      ((L.pull (pullback.fst B.hom U.ι)).pull (pullbackRestrictIsoRestrict B.hom U).inv) := by
    exact GenSpread.lbIso_pull_pull hL (pullbackRestrictIsoRestrict B.hom U).inv hφ.symm
  exact GlobalTheory.AmpleLocalBase.relAmple_baseChange hsq hL₁ hL₂ hw h

end GlobalTheory.AmpleFibres
end

