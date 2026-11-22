import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeIsMaximalOfIsFractionRing
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0015
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0208
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingEssFiniteType
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart (chartMono_notMem)
open GroundTheory.Heights₂.Heights.HilbertSamuel.SmallSectionsNonzero (chartMono isMultiHomog_chartMono aeval_chartMono)
open GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds (homog_X mem_locRing_iff div_mem_locRing fracHom fracHom_eq_zero_iff isUnit_iff)

theorem aeval_ratio_mul_chartMono {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]
    (φ : MRing J →+* Ω) (c : ∀ k, J k) (hc : ∀ k, φ (X ⟨k, c k⟩) ≠ 0) (S : Subring Ω) (x : (Σ k, J k) → S)
    (hx : ∀ q, (x q : Ω) = φ (X q) / φ (X ⟨q.1, c q.1⟩)) {g : MRing J} {e : B → ℕ} (hg : IsMultiHomog g e) :
    ((aeval x g : S) : Ω) * φ (chartMono c e) = φ g := by
  classical
  let ψ : MRing J →+* Ω := S.subtype.comp (aeval x : MRing J →ₐ[ℤ] S).toRingHom
  have hψX : ∀ q, ψ (X q) = φ (X q) / φ (X ⟨q.1, c q.1⟩) := fun q => by
    show ((aeval x (X q) : S) : Ω) = _
    rw [aeval_X]
    exact hx q
  have hψC : ∀ a : ℤ, ψ (C a) = φ (C a) := fun a =>
    RingHom.congr_fun (RingHom.ext_int (ψ.comp C) (φ.comp C)) a
  show ψ g * φ (chartMono c e) = φ g
  rw [g.as_sum, map_sum, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∀ k, ∑ i, m ⟨k, i⟩ = e k := hg m hm
  have hchart : φ (chartMono c e) = ∏ q : (Σ k, J k), φ (X ⟨q.1, c q.1⟩) ^ m q := by
    rw [Fintype.prod_sigma]
    simp only [Finset.prod_pow_eq_pow_sum, hdeg]
    show φ (∏ k, X ⟨k, c k⟩ ^ e k) = _
    rw [map_prod]
    simp only [map_pow]
  have hne : ∏ q : (Σ k, J k), φ (X ⟨q.1, c q.1⟩) ^ m q ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun q _ => pow_ne_zero _ (hc q.1)
  rw [hchart, monomial_eq, map_mul, map_mul, hψC, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [map_prod, map_pow, hψX, div_pow, Finset.prod_div_distrib]
  rw [mul_assoc, div_mul_cancel₀ _ hne]

theorem essFiniteType_locRing : ∀ (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] (w : (Σ k, J k) → K) (W : Ideal (MRing J)) (c : ∀ k, J k),
    (mCoordIdeal w).IsPrime → W.IsPrime → mCoordIdeal w ≤ W → (∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) →
    ∀ [Algebra (ZMod p) (locRing (mCoordIdeal w) W)],
      Algebra.EssFiniteType (ZMod p) (locRing (mCoordIdeal w) W) := by
  intro B _ J _ p _ K _ w W c hP hW hle hcW _
  classical
  haveI : (mCoordIdeal w).IsPrime := hP
  haveI : W.IsPrime := hW
  have hXP : ∀ k, fracHom (mCoordIdeal w) (X ⟨k, c k⟩) ≠ 0 := fun k h =>
    hcW k (hle (fracHom_eq_zero_iff.1 h))
  have hchartP : ∀ a : B → ℕ, fracHom (mCoordIdeal w) (chartMono c a) ≠ 0 := fun a h =>
    chartMono_notMem hW hcW a (hle (fracHom_eq_zero_iff.1 h))
  let xS : (Σ k, J k) → locRing (mCoordIdeal w) W := fun q =>
    ⟨fracHom (mCoordIdeal w) (X q) / fracHom (mCoordIdeal w) (X ⟨q.1, c q.1⟩),
      div_mem_locRing hle (homog_X q.1 q.2) (homog_X q.1 (c q.1)) (hcW q.1)⟩
  let s : Finset (locRing (mCoordIdeal w) W) := Finset.univ.image xS
  have hsub : Set.range xS ⊆ (s : Set (locRing (mCoordIdeal w) W)) := by
    rintro _ ⟨q, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_image_of_mem xS (Finset.mem_univ q))
  have hmem : ∀ g : MRing J, aeval xS g ∈ Algebra.adjoin (ZMod p) (s : Set (locRing (mCoordIdeal w) W)) := by
    intro g
    refine Algebra.adjoin_mono hsub ?_
    induction g using MvPolynomial.induction_on
    next a =>
      rw [aeval_C, algebraMap_int_eq, Int.coe_castRingHom]
      exact intCast_mem _ a
    next f g hf hg =>
      rw [map_add]
      exact add_mem hf hg
    next f q hf =>
      rw [map_mul, aeval_X]
      exact mul_mem hf (Algebra.subset_adjoin ⟨q, rfl⟩)
  refine ⟨⟨s, ?_⟩⟩
  constructor
  constructor
  · intro y
    exact y.2
  · intro z
    obtain ⟨u, v, a, hu, hv, hvW, hz⟩ := (mem_locRing_iff hle).1 z.2
    have hA := aeval_ratio_mul_chartMono (fracHom (mCoordIdeal w)) c hXP _ xS (fun q => rfl) hu
    have hB := aeval_ratio_mul_chartMono (fracHom (mCoordIdeal w)) c hXP _ xS (fun q => rfl) hv
    have hBu : IsUnit (aeval xS v) :=
      (isUnit_iff hle (aeval xS v) hv (isMultiHomog_chartMono c a) (chartMono_notMem hW hcW a) hB).2 hvW
    refine ⟨(⟨aeval xS u, hmem u⟩, ⟨⟨aeval xS v, hmem v⟩, hBu⟩), ?_⟩
    apply Subtype.ext
    apply mul_right_cancel₀ (hchartP a)
    show ((z : FractionRing (MRing J ⧸ mCoordIdeal w)) * (aeval xS v : FractionRing (MRing J ⧸ mCoordIdeal w))) *
        fracHom (mCoordIdeal w) (chartMono c a) =
      (aeval xS u : FractionRing (MRing J ⧸ mCoordIdeal w)) * fracHom (mCoordIdeal w) (chartMono c a)
    rw [mul_assoc, hB, hA, hz]
  · intro x y h
    exact ⟨1, by rw [Subtype.ext h]⟩

end GlobalTheory.CompanionTheory.Ar.GeoDeg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.MultihomogPrimeMemDivisorSupport
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.FunctionField GroundTheory.Heights₂.Heights.Inter IsLocalRing GlobalTheory.CompanionTheory.Ar.GeoDeg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin

open GroundTheory.Heights₂.Heights.Targets.CurveVerticalPointChart

variable {B : Type} [Fintype B] {J : B → Type} [∀ k, Fintype (J k)] {K : Type} [Field K]

def chartIdeal (w : (Σ k, J k) → K) (c : ∀ k, J k) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (U : Ideal (MRing J)) :
    Ideal (chartRingZ w c) where
  carrier := {r | (r : K) ∈ chartPrime w c U}
  add_mem' ha hb := chartPrime_add w ha hb
  zero_mem' := ⟨0, 0, fun m hm => by simp at hm, U.zero_mem, by simp⟩
  smul_mem' a _ hb := chartPrime_mul w hc a.2 hb

theorem mem_chartIdeal {w : (Σ k, J k) → K} {c : ∀ k, J k} {hc : ∀ k, w ⟨k, c k⟩ ≠ 0} {U : Ideal (MRing J)}
    {r : chartRingZ w c} : r ∈ chartIdeal w c hc U ↔ (r : K) ∈ chartPrime w c U :=
  Iff.rfl

theorem chartIdeal_mono {w : (Σ k, J k) → K} {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    {U U' : Ideal (MRing J)} (h : U ≤ U') : chartIdeal w c hc U ≤ chartIdeal w c hc U' := by
  rintro r ⟨e, g, hg, hgU, hr⟩
  exact ⟨e, g, hg, h hgU, hr⟩

theorem chartIdeal_isPrime (w : (Σ k, J k) → K) {c : ∀ k, J k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    {U : Ideal (MRing J)} (hVU : mCoordIdeal w ≤ U) (hU : U.IsPrime)
    (hXU : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ U) : (chartIdeal w c hc U).IsPrime := by
  refine ⟨?_, ?_⟩
  · rw [Ideal.ne_top_iff_one]
    intro h
    have h1 := (mem_chartPrime_iff w hVU hU hXU (r := ((1 : chartRingZ w c) : K)) (e := 0) (k := 1)
      GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_one (by simp)).mp (mem_chartIdeal.mp h)
    exact hU.ne_top ((Ideal.eq_top_iff_one U).mpr h1)
  · intro a b hab
    obtain ⟨e, k, hk, ha⟩ := exists_rep w hc a.2
    obtain ⟨e', k', hk', hb⟩ := exists_rep w hc b.2
    have hkk : k * k' ∈ U := (mem_chartPrime_iff w hVU hU hXU (r := ((a * b : chartRingZ w c) : K))
      (GroundTheory.Heights₂.Heights.Inter.AvoidRing.isMultiHomog_mul hk hk') (by
        rw [MulMemClass.coe_mul, map_mul, prod_pow_add]
        linear_combination ((b : K) * ∏ k, w ⟨k, c k⟩ ^ e' k) * ha + (aeval w k) * hb)).mp
      (mem_chartIdeal.mp hab)
    rcases hU.mem_or_mem hkk with h | h
    · exact Or.inl ⟨e, k, hk, h, ha⟩
    · exact Or.inr ⟨e', k', hk', h, hb⟩

theorem mem_minimalPrimes_of_coord (B : Type) [Fintype B] (J : B → Type) [∀ k, Fintype (J k)] (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Algebra (ZMod p) K] [IsFunctionField (ZMod p) K] (w : (Σ k, J k) → K)
    (hbir : Birational w) (W : Ideal (MRing J)) (c : ∀ k, J k) (hWp : W.IsPrime) (hWh : IsMultiHomogIdeal W)
    (hVW : mCoordIdeal w ≤ W) (hXc : ∀ k, (X ⟨k, c k⟩ : MRing J) ∉ W) (k : B) (c₀ : J k)
    (hw : w ⟨k, c₀⟩ ≠ 0) (hx : (X ⟨k, c₀⟩ : MRing J) ∈ W) :
    W ∈ (mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)}).minimalPrimes := by
  classical
  have hIW : mCoordIdeal w ⊔ Ideal.span {(X ⟨k, c₀⟩ : MRing J)} ≤ W :=
    sup_le hVW ((Ideal.span_singleton_le_iff_mem _).2 hx)
  refine ⟨⟨hWp, hIW⟩, ?_⟩
  rintro Q ⟨hQp, hIQ⟩ hQW
  have hwc : ∀ j, w ⟨j, c j⟩ ≠ 0 := fun j h => hXc j (hVW ((X_mem_iff w j (c j)).2 h))
  have hVQ : mCoordIdeal w ≤ Q := le_sup_left.trans hIQ
  have hxQ : (X ⟨k, c₀⟩ : MRing J) ∈ Q := hIQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hXQ : ∀ j, (X ⟨j, c j⟩ : MRing J) ∉ Q := fun j h => hXc j (hQW h)

  have hpW := chartIdeal_isPrime w hwc hVW hWp hXc
  have hpQ := chartIdeal_isPrime w hwc hVQ hQp hXQ

  let r : chartRingZ w c := ⟨w ⟨k, c₀⟩ / w ⟨k, c k⟩, Algebra.subset_adjoin ⟨⟨k, c₀⟩, rfl⟩⟩
  have hr : r ∈ chartIdeal w c hwc Q := by
    refine ⟨Pi.single k 1, X ⟨k, c₀⟩, GroundTheory.Heights₂.Heights.Inter.regularityLocalFlat_holds.homog_X k c₀, hxQ, ?_⟩
    have hprod : ∏ j, w ⟨j, c j⟩ ^ (Pi.single k 1 : B → ℕ) j = w ⟨k, c k⟩ := by
      rw [Fintype.prod_eq_single k (fun j hj => by simp [Pi.single_eq_of_ne hj])]
      simp
    rw [hprod, aeval_X]
    exact div_mul_cancel₀ _ (hwc k)
  have hne : chartIdeal w c hwc Q ≠ ⊥ := by
    intro h0
    have h1 : r = 0 := by simpa [h0] using hr
    exact div_ne_zero hw (hwc k) (congrArg Subtype.val h1)
  have hmax := chart_prime_isMaximal (p := p) w hbir c hwc _ hpQ hne
  have heq := hmax.eq_of_le hpW.ne_top (chartIdeal_mono hwc hQW)

  obtain ⟨S, hS, hSe⟩ := hWh
  have hSW : Ideal.span S ≤ W := hSe.ge
  rw [hSe, Ideal.span_le]
  intro g hg
  obtain ⟨e, he⟩ := hS g hg
  have hprod : (∏ j, w ⟨j, c j⟩ ^ e j) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun j _ => pow_ne_zero _ (hwc j)
  have hrep : aeval w g * (∏ j, w ⟨j, c j⟩ ^ e j)⁻¹ * ∏ j, w ⟨j, c j⟩ ^ e j = aeval w g :=
    inv_mul_cancel_right₀ hprod _
  let t : chartRingZ w c := ⟨_, form_div_mem_chart w c he⟩
  have htW : t ∈ chartIdeal w c hwc W := ⟨e, g, he, hSW (Ideal.subset_span hg), hrep⟩
  rw [← heq] at htW
  exact (mem_chartPrime_iff w hVQ hQp hXQ he hrep).1 (mem_chartIdeal.1 htW)

end GlobalTheory.CompanionTheory.Ar.GeoDeg.ChartMin

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointValuesInValueSet
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.Ar.Rec

theorem val_mem_valSet_of_uniformised : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (y : (Ref.pjSys Xo c).Pt la), (fun f => (Ref.pjSys Xo c).val y f) ∈ valSet Xo c (algCls Xo c) la := by
  intro E _ _ _ H Dw l Xo c la y
  obtain ⟨q, T, io, e, ho, z, hz, t, ht, rfl⟩ := y
  exact ⟨PtV.mk (cls := algCls Xo c) (PY := Unit) (lies := fun _ _ _ _ => True) la ho z hz () trivial, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Rec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPointLineBundleUnit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

open GlobalTheory.CompanionTheory.Ar.Sl.Transl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.Reg

theorem valF_comp_valR {O C : Type} [CommRing O] [Field C] [Algebra O C] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ a ⁻¹ᵁ U) (f : Γ(X, U)) :
    valF (spMap (algebraMap O C) ≫ a) U f = algebraMap O C (valR a U h f) := by
  have h' : ⊤ ≤ (spMap (algebraMap O C) ≫ a) ⁻¹ᵁ U := fun x _ => h (x := spMap (algebraMap O C) x) trivial
  have e₀ : (spMap (algebraMap O C)).appLE ⊤ ⊤ (by first | exact le_rfl | simp) = (spMap (algebraMap O C)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  have e : (spMap (algebraMap O C) ≫ a).appLE U ⊤ h' = a.appLE U ⊤ h ≫ (spMap (algebraMap O C)).appTop := by
    rw [← e₀]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (algebraMap O C)) a U ⊤ ⊤ h _).symm
  have n := congrArg (fun φ => φ.hom ((a.appLE U ⊤ h).hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap O C)))
  rw [valF, dif_pos h', e]
  exact n

theorem valR_unit {O : Type} [CommRing O] {X : Scheme.{0}} (a : Sp O ⟶ X) (U : X.Opens) (h : ⊤ ≤ a ⁻¹ᵁ U)
    (f : Γ(X, U)ˣ) : IsUnit (valR a U h f.val) :=
  f.isUnit.map (valR a U h)

theorem unit_alg {O : Type} [CommRing O] (t r0 r2 r1 : O) (u0 u1 u2 : Oˣ) (e0 : u0.val = r0) (e1 : u1.val = r1)
    (e2 : u2.val = r2) (M n : ℕ) :
    t ^ M * (u1 ^ n * ((u0 * u2 ^ M) ^ n)⁻¹ : Oˣ).val * (r0 * r2 ^ M) ^ n = t ^ M * r1 ^ n := by
  subst e0 e1 e2
  have : ((u1 ^ n * ((u0 * u2 ^ M) ^ n)⁻¹ * (u0 * u2 ^ M) ^ n : Oˣ)).val = (u1 ^ n : Oˣ).val := by
    rw [inv_mul_cancel_right]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at this ⊢
  rw [_root_.mul_assoc, this]

theorem torsVal_eq_unit_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (O C : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field C] [Algebra O C] [FaithfulSMul O C] (ρ : 𝓞 L →+* O) (y : Over.mk (spMap ρ) ⟶ D.t.G) (N : ℕ), 1 ≤ N → y ^ N = 1 → ∀ (i : D.t.PP.L.ι) (h : ⊤ ≤ (show Sp O ⟶ D.t.G.left from y.left) ⁻¹ᵁ (LB.LinComb D.t.PP.L (K := Fin 1) (fun _ => 𝟙 _) (fun _ => (n : ℤ))).U (fun _ => i)) (b : Sp C ⟶ Sp (𝓞 L)), b = spMap (algebraMap O C) ≫ spMap ρ → ∀ (yC : Over.mk b ⟶ D.t.G), yC.left = spMap (algebraMap O C) ≫ y.left → ∀ T : C, TorsVal D.t.PP s yC N T → ∃ ε : Oˣ, T = algebraMap O C (valR (show Sp O ⟶ D.t.G.left from y.left) _ h (s.f fun _ => i) ^ (N ^ 2) * ε) := by
  intro E _ _ _ H L _ _ D n s O C _ _ _ _ _ _ ρ y N hN hy i h b hb yC hyC T hT
  subst hb
  obtain ⟨-, hyCN, w, -, -, hw, -, -, -⟩ := id hT
  let e : Sp O ⟶ D.t.G.left := (1 : Over.mk (spMap ρ) ⟶ D.t.G).left
  obtain ⟨i₀, h₀⟩ := exists_chart D.t.PP.isLB (e (IsLocalRing.closedPoint O))
  have he : ⊤ ≤ e ⁻¹ᵁ D.t.PP.L.U i₀ := top_le_of_closedPoint _ h₀
  have eN : (show Sp O ⟶ D.t.G.left from y.left) ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left = e := by
    show y.left ≫ _ = _
    rw [left_pow, hy]
  have e1 : e ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left = e := by
    show (1 : Over.mk (spMap ρ) ⟶ D.t.G).left ≫ _ = _
    rw [left_pow, one_pow]
  have hrig : spMap ρ ≫ eSec D.t.G = e := (one_left (Over.mk (spMap ρ))).symm
  have hi : ⊤ ≤ (show Sp O ⟶ D.t.G.left from y.left) ⁻¹ᵁ D.t.PP.L.U i := fun x _ =>
    Set.mem_iInter.1 (h (x := x) trivial) 0
  have hY : ⊤ ≤ (show Sp O ⟶ D.t.G.left from y.left) ⁻¹ᵁ
      LB.wchart D.t.PP.L (![((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left, 𝟙 D.t.G.left] : Fin 2 → _) ![i₀, i] := by
    intro x _
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show (((show Sp O ⟶ D.t.G.left from y.left) ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left) x) ∈ D.t.PP.L.U i₀
      rw [eN]; exact he (x := x) trivial
    · exact hi (x := x) trivial
  have hZ : ⊤ ≤ e ⁻¹ᵁ
      LB.wchart D.t.PP.L (![((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left, 𝟙 D.t.G.left] : Fin 2 → _) ![i₀, i₀] := by
    intro x _
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show ((e ≫ ((𝟙 D.t.G : D.t.G ⟶ D.t.G) ^ N).left) x) ∈ D.t.PP.L.U i₀
      rw [e1]; exact he (x := x) trivial
    · exact he (x := x) trivial
  have hR : ⊤ ≤ (show Sp O ⟶ (𝟙_ (Over (Sp (𝓞 L)))).left from spMap ρ) ⁻¹ᵁ
      LB.wchart D.t.PP.L (K := PUnit) (fun _ => eSec D.t.G) (fun _ => i₀) := by
    intro x _
    refine Set.mem_iInter.2 fun _ => ?_
    show (spMap ρ ≫ eSec D.t.G) x ∈ D.t.PP.L.U i₀
    rw [hrig]; exact he (x := x) trivial
  obtain ⟨u1, e1'⟩ := valR_unit _ _ hY (w.s ![i₀, i])
  obtain ⟨u0, e0'⟩ := valR_unit _ _ hZ (w.s ![i₀, i₀])
  obtain ⟨u2, e2'⟩ := valR_unit (X := (𝟙_ (Over (Sp (𝓞 L)))).left) _ _ hR (D.t.PP.rig.s fun _ => i₀)
  have hone : (1 : Over.mk (spMap (algebraMap O C) ≫ spMap ρ) ⟶ D.t.G).left = spMap (algebraMap O C) ≫ e := by
    show _ = spMap (algebraMap O C) ≫ (1 : Over.mk (spMap ρ) ⟶ D.t.G).left
    rw [one_left, one_left]
    simp
  refine ⟨u1 ^ n * ((u0 * u2 ^ (N ^ 2)) ^ n)⁻¹, ?_⟩
  have hT' : TorsVal D.t.PP s yC N (algebraMap O C (valR (show Sp O ⟶ D.t.G.left from y.left) _ h (s.f fun _ => i) ^ (N ^ 2) *
      (u1 ^ n * ((u0 * u2 ^ (N ^ 2)) ^ n)⁻¹ : Oˣ).val)) := by
    refine ⟨hN, hyCN, w, i₀, i, hw, ?_, ?_, ?_⟩
    · rw [hone]
      exact fun x _ => he (x := spMap (algebraMap O C) x) trivial
    · rw [hyC]
      exact fun x _ => hi (x := spMap (algebraMap O C) x) trivial
    · rw [hone, hyC]
      erw [valF_comp_valR e _ hZ, valF_comp_valR (X := (𝟙_ (Over (Sp (𝓞 L)))).left) _ _ hR,
        valF_comp_valR _ _ h, valF_comp_valR _ _ hY]
      have key := congrArg (algebraMap O C) (unit_alg (valR (show Sp O ⟶ D.t.G.left from y.left) _ h (s.f fun _ => i)) _ _ _
        u0 u1 u2 e0' e1' e2' (N ^ 2) n)
      simp only [map_mul, map_pow] at key ⊢
      exact key
  exact (GlobalTheory.T.torsion_value_unique_base_change E H L D n s C _ yC N hN hyCN).1.unique hT hT'

end GlobalTheory.CompanionTheory.Ar.Sl.Reg
end
end

