import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0101
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.TowerOrigin
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0036
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0052
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0096
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0091
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.MetricStatements.ExistsFlagModelBaseMetric
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0125

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemMcPtsOfOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen

open GlobalTheory.CompanionTheory.Ar.Cmp.SncRes GlobalTheory.CompanionTheory.Ar.PB.Proj

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

abbrev PtsOf (P : Ideal (MRing ι)) : Type := ↥(Pts (pC P))

theorem proj_eq_of_orbit {z w : (Σ k, ι k) → ℂ} (h : SameOrbit z w) : proj z = proj w := by
  obtain ⟨c, hc, rfl⟩ := h
  exact Top.proj_smul c hc w

theorem orbit_of_proj {z w : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0)
    (h : proj z = proj w) : SameOrbit z w := by
  refine orbit_of_cross hz hw fun k i i' => ?_
  obtain ⟨j, hj⟩ := hz k
  have hN : ((∑ l, ‖z ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Top.normSq_pos (hz k)).ne'
  have hM : ((∑ l, ‖w ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Top.normSq_pos (hw k)).ne'
  have hj' : starRingEnd ℂ (z ⟨k, j⟩) ≠ 0 := by simpa using hj
  have h1 := congrFun h ⟨k, (i, j)⟩
  have h2 := congrFun h ⟨k, (i', j)⟩
  simp only [proj] at h1 h2
  rw [div_eq_div_iff hN hM] at h1 h2
  have : (z ⟨k, i⟩ * w ⟨k, i'⟩ - z ⟨k, i'⟩ * w ⟨k, i⟩) *
      (starRingEnd ℂ (z ⟨k, j⟩) * ((∑ l, ‖w ⟨k, l⟩‖ ^ 2 : ℝ) : ℂ)) = 0 := by
    linear_combination (w ⟨k, i'⟩) * h1 - (w ⟨k, i⟩) * h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right (mul_ne_zero hj' hM))

variable {P : Ideal (MRing ι)} {e : ℕ}

theorem rep_mem_mcPts (x : PtsOf P) : rep x ∈ mcPts P :=
  (mem_mcPts_iff_conePts_pC P _).2 (rep_mem x)

theorem pts_eq_of_orbit {x y : PtsOf P} (h : SameOrbit (rep x) (rep y)) : x = y := by
  apply Subtype.ext
  rw [← proj_rep x, ← proj_rep y]
  exact proj_eq_of_orbit h

def cls (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) : PtsOf P :=
  ⟨proj z, z, (mem_mcPts_iff_conePts_pC P z).1 hz, rfl⟩

theorem rep_cls_orbit (z : (Σ k, ι k) → ℂ) (hz : z ∈ mcPts P) : SameOrbit (rep (cls z hz)) z :=
  orbit_of_proj (rep_mem_mcPts _).1 hz.1 (proj_rep (cls z hz))

theorem mem_mcPts_of_orbit (hP : IsMultiHomogIdeal P) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (h : SameOrbit z' z) : z' ∈ mcPts P := by
  have hz' := (mem_mcPts_iff_conePts_pC P z).1 hz
  refine (mem_mcPts_iff_conePts_pC P z').2 ⟨fun k => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hz.1 k
    exact ⟨i, fun h0 => hi (by
      obtain ⟨c, hc, rfl⟩ := h
      have : c k * z ⟨k, i⟩ = 0 := h0
      exact (mul_eq_zero.1 this).resolve_left (hc k))⟩
  · obtain ⟨c, hc, rfl⟩ := h
    exact ReciprocityTheory.AnForm.R.eval_eq_zero_of_smul (isMultiHomogIdeal_pC hP) c z hz'.2

theorem orbit_aff (p : (k : K) → ι k) {x : PtsOf P} (hx : x ∈ src (pC P) p) :
    SameOrbit (affCoord p (rep x)) (rep x) := by
  refine ⟨fun k => (rep x ⟨k, p k⟩)⁻¹, fun k => inv_ne_zero (hx k), ?_⟩
  funext q
  simp [affCoord, div_eq_inv_mul]

theorem exists_alt_variant (x : PtsOf P) : ∃ p : (k : K) → ι k, x ∈ src (pC P) p := by
  choose p hp using (rep_mem_mcPts x).1
  exact ⟨p, hp⟩

theorem continuousOn_aff (p : (k : K) → ι k) :
    ContinuousOn (fun x : PtsOf P => affCoord p (rep x)) (src (pC P) p) :=
  continuousOn_iff_continuous_restrict.2 (Top.isEmbedding_affCoord p).continuous

def srcOf (C : OrbitChart P e) : Set (PtsOf P) := {x | rep x ∈ C.O}

theorem mem_O_of_orbit (C : OrbitChart P e) (hP : IsMultiHomogIdeal P) {z z' : (Σ k, ι k) → ℂ} (hz : z ∈ C.O)
    (h : SameOrbit z' z) (hzP : z ∈ mcPts P) : z' ∈ C.O :=
  C.O_orbit z hz z' (mem_mcPts_of_orbit hP hzP h) h

theorem isOpen_srcOf (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) : IsOpen (srcOf C) := by
  obtain ⟨O', hO', hO⟩ := C.O_open
  refine isOpen_iff_mem_nhds.2 fun x hx => ?_
  obtain ⟨p, hp⟩ := exists_alt_variant x
  have hS : src (pC P) p ∈ 𝓝 x := (Top.isOpen_alt_bis p).mem_nhds hp
  have hc : ContinuousAt (fun y : PtsOf P => affCoord p (rep y)) x := (continuousOn_aff p).continuousAt hS
  have hax : affCoord p (rep x) ∈ C.O :=
    mem_O_of_orbit C hP hx (orbit_aff p hp) (rep_mem_mcPts x)
  have hax' : affCoord p (rep x) ∈ O' := by rw [hO] at hax; exact hax.1
  filter_upwards [hS, hc (hO'.mem_nhds hax')] with y hy hy'
  have h1 : affCoord p (rep y) ∈ mcPts P := mem_mcPts_of_orbit hP (rep_mem_mcPts y) (orbit_aff p hy)
  have h2 : affCoord p (rep y) ∈ C.O := by rw [hO]; exact ⟨hy', h1⟩
  exact mem_O_of_orbit C hP h2 (Proj.orbit_symm (orbit_aff p hy)) h1

theorem continuousOn_rho (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) :
    ContinuousOn (fun x : PtsOf P => C.ρ (rep x)) (srcOf C) := by
  intro x hx
  apply ContinuousAt.continuousWithinAt
  obtain ⟨p, hp⟩ := exists_alt_variant x
  have hS : src (pC P) p ∈ 𝓝 x := (Top.isOpen_alt_bis p).mem_nhds hp
  have hO : srcOf C ∈ 𝓝 x := (isOpen_srcOf hP C).mem_nhds hx
  have hc : ContinuousAt (fun y : PtsOf P => affCoord p (rep y)) x := (continuousOn_aff p).continuousAt hS
  have hmem : ∀ y ∈ src (pC P) p, y ∈ srcOf C → affCoord p (rep y) ∈ C.O := fun y hy hy' =>
    mem_O_of_orbit C hP hy' (orbit_aff p hy) (rep_mem_mcPts y)
  have ht : Tendsto (fun y : PtsOf P => affCoord p (rep y)) (𝓝 x) (𝓝[C.O] (affCoord p (rep x))) := by
    refine tendsto_nhdsWithin_iff.2 ⟨hc, ?_⟩
    filter_upwards [hS, hO] with y hy hy' using hmem y hy hy'
  have h1 := (C.ρ_cont _ (hmem x hp hx)).tendsto.comp ht
  have e1 : C.ρ (affCoord p (rep x)) = C.ρ (rep x) :=
    C.ρ_orbit _ hx _ (hmem x hp hx) (orbit_aff p hp)
  rw [e1] at h1
  refine h1.congr' ?_
  filter_upwards [hS, hO] with y hy hy'
  exact C.ρ_orbit _ hy' _ (hmem y hy hy') (orbit_aff p hy)

def clsT (x₀ : PtsOf P) (z : (Σ k, ι k) → ℂ) : PtsOf P := if h : z ∈ mcPts P then cls z h else x₀

theorem clsT_of_mem (x₀ : PtsOf P) {z : (Σ k, ι k) → ℂ} (h : z ∈ mcPts P) : clsT x₀ z = cls z h := dif_pos h

theorem continuousOn_cls (C : OrbitChart P e) (x₀ : PtsOf P) :
    ContinuousOn (fun w => clsT x₀ (C.φ w)) C.D := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  have hφ : ContinuousOn C.φ C.D := continuousOn_pi.2 fun q => (C.holo q).continuousOn
  have h1 : ContinuousOn (fun w => proj (C.φ w)) C.D :=
    Top.continuousOn_proj.comp hφ fun w hw => (C.mem w hw).1
  refine h1.congr fun w hw => ?_
  simp only [Function.comp, clsT_of_mem x₀ (C.mem w hw), cls]

def orbChart (hP : IsMultiHomogIdeal P) (C : OrbitChart P e) (x₀ : PtsOf P) :
    OpenPartialHomeomorph (PtsOf P) (Fin e → ℂ) where
  toFun x := C.ρ (rep x)
  invFun w := clsT x₀ (C.φ w)
  source := srcOf C
  target := C.D
  map_source' _ hx := C.ρ_mem _ hx
  map_target' w hw := by
    rw [clsT_of_mem x₀ (C.mem w hw)]
    exact mem_O_of_orbit C hP (C.φ_mem_O w hw) (rep_cls_orbit _ _) (C.mem w hw)
  left_inv' x hx := by
    have hm := C.mem _ (C.ρ_mem _ hx)
    show clsT x₀ (C.φ (C.ρ (rep x))) = x
    rw [clsT_of_mem x₀ hm]
    exact pts_eq_of_orbit (Proj.orbit_trans (rep_cls_orbit _ hm) (C.φ_ρ _ hx))
  right_inv' w hw := by
    show C.ρ (rep (clsT x₀ (C.φ w))) = w
    rw [clsT_of_mem x₀ (C.mem w hw)]
    have h1 := mem_O_of_orbit C hP (C.φ_mem_O w hw) (rep_cls_orbit _ (C.mem w hw)) (C.mem w hw)
    rw [C.ρ_orbit _ (C.φ_mem_O w hw) _ h1 (rep_cls_orbit _ (C.mem w hw)), C.ρ_φ w hw]
  open_source := isOpen_srcOf hP C
  open_target := C.isOpen_D
  continuousOn_toFun := continuousOn_rho hP C
  continuousOn_invFun := continuousOn_cls C x₀

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Gen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemOpenOfForms
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Small.Fund
open AlgebraicGeometry CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Small.FormsVal

section Val

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {z : Spec (CommRingCat.of ℂ) ⟶ X}

def valRing (ξ : Spec (CommRingCat.of Ω) ⟶ X) (z : Spec (CommRingCat.of ℂ) ⟶ X) (h : genPt ξ ⤳ centre z) :
    Subring (Ω × ℂ) :=
  ((genMap ξ ⟨centre z, h⟩).prod (Scheme.stalkClosedPointTo z).hom).range

theorem mem_valRing_of_valAt (h : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (hv : ValAt ξ z a r) :
    (a, r) ∈ valRing ξ z h := by
  obtain ⟨h', s, hs, hr⟩ := hv
  exact ⟨s, Prod.ext hs hr⟩

theorem valAt_of_mem_valRing (h : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (hv : (a, r) ∈ valRing ξ z h) :
    ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := hv
  exact ⟨h, s, congrArg Prod.fst hs, congrArg Prod.snd hs⟩

theorem aeval_mem_valRing (h : genPt ξ ⤳ centre z) {σ : Type} {a : σ → Ω} {r : σ → ℂ}
    (hv : ∀ i, (a i, r i) ∈ valRing ξ z h) (f : MvPolynomial σ ℤ) :
    (aeval a f, aeval r f) ∈ valRing ξ z h := by
  induction f using MvPolynomial.induction_on with
  | C n =>
    have e : (aeval a (C n : MvPolynomial σ ℤ), aeval r (C n : MvPolynomial σ ℤ)) = ((n : Ω × ℂ)) :=
      Prod.ext (by simp) (by simp)
    rw [e]
    exact intCast_mem _ n
  | add f g hf hg =>
    have := add_mem hf hg
    simpa using this
  | mul_X f i hf =>
    have := mul_mem hf (hv i)
    simpa using this

theorem unitAt_of_mem_valRing (h : genPt ξ ⤳ centre z) {a : Ω} {r : ℂ} (hv : (a, r) ∈ valRing ξ z h) (hr : r ≠ 0) :
    unitAt ξ ⟨centre z, h⟩ a := by
  obtain ⟨s, hs⟩ := hv
  have hs1 : genMap ξ ⟨centre z, h⟩ s = a := congrArg Prod.fst hs
  have hs2 : (Scheme.stalkClosedPointTo z).hom s = r := congrArg Prod.snd hs
  have hl : IsLocalHom (Scheme.stalkClosedPointTo z).hom := Scheme.isLocalHom_stalkClosedPointTo z
  have hu : IsUnit s := hl.map_nonunit s ((congrArg IsUnit hs2).mpr hr.isUnit)
  obtain ⟨t, ht⟩ := hu.exists_right_inv
  have h1 : a * genMap ξ ⟨centre z, h⟩ t = 1 := by rw [← hs1, ← map_mul, ht, map_one]
  have ha0 : a ≠ 0 := left_ne_zero_of_mul_eq_one h1
  exact ⟨ha0, ⟨s, hs1⟩, ⟨t, eq_inv_of_mul_eq_one_right h1⟩⟩

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {y : (Σ k, ι k) → Ω}
  {w : (Σ k, ι k) → ℂ}

theorem ratio_mem_valRing (h : genPt ξ ⤳ centre z) (hc : CoordsAt ξ y z w) (c : (k : K) → ι k)
    (hu : ∀ k, w ⟨k, c k⟩ ≠ 0) (p : Σ k, ι k) :
    ((y ⟨p.1, c p.1⟩)⁻¹ * y p, (w ⟨p.1, c p.1⟩)⁻¹ * w p) ∈ valRing ξ z h := by
  obtain ⟨k, i⟩ := p
  obtain ⟨-, hr⟩ := hc.2 k (c k) (hu k).isUnit
  obtain ⟨r, hv, hw⟩ := hr i
  have e1 : (w ⟨k, c k⟩)⁻¹ * w ⟨k, i⟩ = r := by rw [hw]; field_simp [hu k]
  have e2 : (y ⟨k, c k⟩)⁻¹ * y ⟨k, i⟩ = y ⟨k, i⟩ / y ⟨k, c k⟩ := by rw [div_eq_mul_inv, mul_comm]
  show ((y ⟨k, c k⟩)⁻¹ * y ⟨k, i⟩, (w ⟨k, c k⟩)⁻¹ * w ⟨k, i⟩) ∈ _
  rw [e1, e2]
  exact mem_valRing_of_valAt h hv

theorem unitAt_form (h : genPt ξ ⤳ centre z) (hc : CoordsAt ξ y z w) (c : (k : K) → ι k)
    (hu : ∀ k, w ⟨k, c k⟩ ≠ 0) {G : MRing ι} {d : K → ℕ} (hG : IsMultiHomog G d) (hw : aeval w G ≠ 0) :
    unitAt ξ ⟨centre z, h⟩ (aeval y G / ∏ k, y ⟨k, c k⟩ ^ d k) := by
  have hm := aeval_mem_valRing h (ratio_mem_valRing h hc c hu) G
  rw [aeval_scale hG (fun k => (y ⟨k, c k⟩)⁻¹) y, aeval_scale hG (fun k => (w ⟨k, c k⟩)⁻¹) w] at hm
  have e : (∏ k, (y ⟨k, c k⟩)⁻¹ ^ d k) * aeval y G = aeval y G / ∏ k, y ⟨k, c k⟩ ^ d k := by
    simp only [inv_pow, Finset.prod_inv_distrib]
    rw [div_eq_mul_inv, mul_comm]
  rw [e] at hm
  refine unitAt_of_mem_valRing h hm (mul_ne_zero ?_ hw)
  exact Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (inv_ne_zero (hu k))

end Val

section Field

variable {Ω : Type} [Field Ω]

theorem zpow_sum_eq_prod_zpow {R : Type} (Y : Ω) (hY : Y ≠ 0) (s : Finset R) (f : R → ℤ) :
    Y ^ (∑ r ∈ s, f r) = ∏ r ∈ s, Y ^ f r := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert r s hr ih => rw [Finset.sum_insert hr, Finset.prod_insert hr, zpow_add₀ hY, ih]

theorem mono_identity {K R : Type} [Fintype K] [Fintype R] (Y : K → Ω) (hY : ∀ k, Y k ≠ 0) (e : R → Ω)
    (he : ∀ r, e r ≠ 0) (x : R → K → ℤ) (Aa : K → ℤ) (n : R → ℤ) (q : ℕ) (k₀ : K)
    (hA : Aa k₀ = 1 ∧ ∀ k, k ≠ k₀ → Aa k = 0) (a : K → ℤ)
    (ha : ∀ k, a k = -(q : ℤ) * Aa k + ∑ r, -n r * x r k) :
    (∏ k, Y k ^ a k)⁻¹ * ∏ r, e r ^ n r = Y k₀ ^ q / ∏ r, ((∏ k, Y k ^ x r k) • e r) ^ (-n r) := by
  classical
  have h1 : ∏ k, Y k ^ Aa k = Y k₀ := by
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by rw [hA.2 k hk, zpow_zero]) (by simp), hA.1, zpow_one]
  have h2 : ∏ k, Y k ^ a k = (Y k₀ ^ q)⁻¹ * ∏ r, (∏ k, Y k ^ x r k) ^ (-n r) := by
    have e1 : ∀ k, Y k ^ a k = (Y k ^ Aa k) ^ (-(q : ℤ)) * ∏ r, (Y k ^ x r k) ^ (-n r) := fun k => by
      rw [ha k, zpow_add₀ (hY k), zpow_sum_eq_prod_zpow _ (hY k), ← zpow_mul, mul_comm (Aa k)]
      congr 1
      refine Finset.prod_congr rfl fun r _ => ?_
      rw [← zpow_mul, mul_comm (x r k)]
    simp only [e1, Finset.prod_mul_distrib]
    rw [Finset.prod_comm]
    congr 1
    · rw [Finset.prod_zpow, h1, zpow_neg, zpow_natCast]
    · refine Finset.prod_congr rfl fun r _ => ?_
      rw [Finset.prod_zpow]
  have h3 : ∏ r, ((∏ k, Y k ^ x r k) • e r) ^ (-n r) =
      (∏ r, (∏ k, Y k ^ x r k) ^ (-n r)) * (∏ r, e r ^ n r)⁻¹ := by
    rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun r _ => ?_
    rw [smul_eq_mul, mul_zpow, zpow_neg (e r)]
  have h4 : ∏ r, (∏ k, Y k ^ x r k) ^ (-n r) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _
      (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hY k))
  have h5 : ∏ r, e r ^ n r ≠ 0 := Finset.prod_ne_zero_iff.2 fun r _ => zpow_ne_zero _ (he r)
  have h6 : Y k₀ ^ q ≠ 0 := pow_ne_zero _ (hY k₀)
  rw [h2, h3]
  field_simp

end Field

theorem mem_open_of_forms : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (RM : RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (Or : RootOrigin Y S RM Fx) (n₀ : Option (RootIx D) → ℤ) (N₀ : ℕ), (∀ r, n₀ (some r) = -Fx.n r) → n₀ none = -(Fx.q' : ℤ) → ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) ≠ 0 → ∀ (x : Or.Re.R.X) (dg dh : RM.K → ℕ) (G Hf : MRing RM.ι), IsMultiHomog G dg → IsMultiHomog Hf dh → (∀ k, (dg k : ℤ) = dh k + (combLine (RM.line 1) n₀).a k) → aeval RM.y G = ((N₀ : RM.Ω) * Or.g Fx.sE * ∏ r, Or.e r ^ Fx.n r) * aeval RM.y Hf → aeval (Or.Re.R.lift x x) G ≠ 0 → aeval (Or.Re.R.lift x x) Hf ≠ 0 → Or.Re.π x ∈ Sys.open' := by
  intro E _ _ _ H D l Xo c O _ β Y S RM Sys Fx Or n₀ N₀ hn hnone hε x dg dh G Hf hG hH hdeg hy hwG hwH
  classical
  have hmem : Or.Re.R.lift x x ∈ mcPts (mCoordIdeal RM.y) := Or.Re.R.mem x x (Or.Re.R.mem_U x)
  obtain ⟨z, hz, hc⟩ := (mem_mcPts_iff_exists_coordsAt _ _ Or.𝔐.ξ _ _ RM.y Or.𝔐.tie _).1 hmem
  refine (Or.interior x z hc).1 ?_
  by_contra hnab
  choose b hb using hc.1
  have hbw : ∀ k, Or.Re.R.lift x x ⟨k, b k⟩ ≠ 0 := fun k => (hb k).ne_zero
  let p : Cpt Or.𝔐.ξ := ⟨centre z, hz⟩
  have hyc : ∀ k, RM.y ⟨k, b k⟩ ≠ 0 := fun k => (hc.2 k (b k) (hb k)).1
  have hrat : ∀ k i, RM.y ⟨k, i⟩ / RM.y ⟨k, b k⟩ ∈ regAt Or.𝔐.ξ p := by
    intro k i
    obtain ⟨r, ⟨h', s, hs, -⟩, -⟩ := (hc.2 k (b k) (hb k)).2 i
    exact ⟨s, hs⟩
  have hch : InChart Or.𝔐.ξ (fun c' : (k : RM.K) → RM.ι k => ∏ k, RM.y ⟨k, c' k⟩) b p := by
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => hyc k, fun c' => ?_⟩
    show (∏ k, RM.y ⟨k, c' k⟩) / ∏ k, RM.y ⟨k, b k⟩ ∈ _
    rw [← Finset.prod_div_distrib]
    exact prod_mem fun k _ => hrat k (c' k)
  have he0 : ∀ r, Or.e r ≠ 0 := fun r => (Or.lines r).1
  have hgen : ∀ r, (Or.Fl.rootLat r).IsGenAt p ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) := fun r =>
    ⟨smul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)) (he0 r),
      (Or.lines r).2 _ trivial b hch⟩
  have ht := GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.tens_isGenAt (fun r => -Fx.n r) hgen
  have ya : Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) = RM.y ⟨Or.k₀, b Or.k₀⟩ := by
    rw [← Or.y_eq, Equiv.apply_symm_apply]
  have hch' : InChart Or.𝔐.ξ (fun i' => Or.g (Fx.yf i')) (Or.ix.symm (b Or.k₀)) p := by
    refine ⟨?_, fun j => ?_⟩
    · show Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ≠ 0
      rw [ya]; exact hyc _
    · show Or.g (Fx.yf j) / Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ∈ _
      rw [ya, ← Or.y_eq]
      exact hrat _ _
  have hnat : ∀ m : ℕ, m ≠ 0 → unitAt Or.𝔐.ξ p (m : RM.Ω) := by
    intro m hm
    have e : (((m : RM.Ω), (m : ℂ)) : RM.Ω × ℂ) = ((m : RM.Ω × ℂ)) := Prod.ext (by simp) (by simp)
    have h2 : (((m : RM.Ω), (m : ℂ)) : RM.Ω × ℂ) ∈ valRing Or.𝔐.ξ z hz := by
      rw [e]
      exact natCast_mem _ m
    exact unitAt_of_mem_valRing hz h2 (Nat.cast_ne_zero.2 hm)
  have hp0 : ∀ r : ℕ, r.Prime → ¬ InFibre Or.𝔐.ξ r p := fun r hr hf => hf (hnat r hr.ne_zero)
  obtain ⟨-, hnu⟩ := Or.eff p hp0 _ _ hch' ht
  have hN₀ : N₀ ≠ 0 := by
    rintro rfl
    exact hε (by simp)
  have hA := unitAt_form hz hc b hbw hG hwG
  have hB := unitAt_form hz hc b hbw hH hwH
  have hAB : unitAt Or.𝔐.ξ p ((aeval RM.y G / ∏ k, RM.y ⟨k, b k⟩ ^ dg k) /
      (aeval RM.y Hf / ∏ k, RM.y ⟨k, b k⟩ ^ dh k)) :=
    ⟨div_ne_zero hA.1 hB.1, by rw [div_eq_mul_inv]; exact mul_mem hA.2.1 hB.2.2,
      by rw [inv_div, div_eq_mul_inv]; exact mul_mem hB.2.1 hA.2.2⟩
  have hid := mono_identity (fun k => RM.y ⟨k, b k⟩) hyc Or.e he0 RM.xdeg RM.A.a Fx.n Fx.q' Or.k₀ Or.A_deg
    (combLine (RM.line 1) n₀).a (fun k => by
      simp [combLine, Finset.sum_apply, Fintype.sum_option, RootModel.line, RM.x_deg, hn, hnone])
  have hHf0 : aeval RM.y Hf ≠ 0 := fun h0 => hB.1 (by rw [h0, zero_div])
  have hMh : ∏ k, RM.y ⟨k, b k⟩ ^ dh k ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hyc k)
  have hPa : ∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hyc k)
  have hMg : ∏ k, RM.y ⟨k, b k⟩ ^ dg k =
      (∏ k, RM.y ⟨k, b k⟩ ^ dh k) * ∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← zpow_natCast, hdeg k, zpow_add₀ (hyc k), zpow_natCast]
  have hfin : (aeval RM.y G / ∏ k, RM.y ⟨k, b k⟩ ^ dg k) / (aeval RM.y Hf / ∏ k, RM.y ⟨k, b k⟩ ^ dh k) =
      (Or.g Fx.sE * Or.g (Fx.yf (Or.ix.symm (b Or.k₀))) ^ Fx.q' /
        ∏ r, ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r)) * (N₀ : RM.Ω) := by
    have hid' : (∏ k, RM.y ⟨k, b k⟩ ^ (combLine (RM.line 1) n₀).a k)⁻¹ * ∏ r, Or.e r ^ Fx.n r =
        RM.y ⟨Or.k₀, b Or.k₀⟩ ^ Fx.q' / ∏ r, ((∏ k, RM.y ⟨k, b k⟩ ^ RM.xdeg r k) • Or.e r) ^ (-Fx.n r) := hid
    rw [hy, hMg, ya, mul_div_assoc (Or.g Fx.sE), ← hid']
    field_simp
  rw [hfin] at hAB
  exact hnu hnab (GlobalTheory.CompanionTheory.Ar.Chg.CoverEff.unitAt_of_mul hAB (hnat N₀ hN₀))

end GlobalTheory.CompanionTheory.Ar.Small.FormsVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.NefPolarization
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.PB.NefPolProof

theorem exists_ne_zero_of_relevant {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : IsRelevant (mCoordIdeal y)) :
    ∀ k, ∃ i, y ⟨k, i⟩ ≠ 0 := by
  intro k
  obtain ⟨i, hi⟩ := h k
  refine ⟨i, fun h0 => hi ?_⟩
  show (X ⟨k, i⟩ : MRing ι) ∈ RingHom.ker (mConeMap y)
  rw [RingHom.mem_ker]
  simp [mConeMap, h0]

theorem fin_one_const {α : Type} (a : α) : (fun _ : Fin 1 => a) = ![a] := by
  funext j
  fin_cases j
  rfl

end GlobalTheory.CompanionTheory.Ar.PB.NefPolProof

namespace GlobalTheory.CompanionTheory.Ar.PB

open GlobalTheory.CompanionTheory.Ar.PB.NefPolProof in

theorem nefPol : NefPol := by
  intro hIn D σ _ S Fl hFl K _ ι _ Ω _ _ y Re hJ hBir I hI n hn
  have hK : Nonempty K := Re.arith.1
  have hRe := GlobalTheory.T.realisation_potential_degree_compatibility hIn.resExists K ι D σ S (mCoordIdeal y) Re
  have hsm : IsSmoothHerm (combLine Re.ref n) := (hRe.2.2.2 n).1
  have hnef : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.NefOnF I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) (combLine Re.ref n).a := by
    intro W hW hle
    obtain ⟨hW', hWmap⟩ := (GlobalTheory.T.arithmetic_variety_generic_fibre_projective K ι 1).1 W hK hW
    have hPW : mCoordIdeal y ≤ W.comap (MvPolynomial.map (Int.castRingHom ℚ)) :=
      (Ideal.le_comap_map).trans (Ideal.comap_mono hle)
    have h0 := GlobalTheory.T.geometric_degree_nonnegative_psh hIn K ι D σ S (mCoordIdeal y) Re Fl hFl hJ n hn _ hW' hPW
    have h1 := GlobalTheory.T.generic_intersection_equals_points_integral hIn K ι I hI 1 (W.comap (MvPolynomial.map (Int.castRingHom ℚ)))
      (fun _ => combLine Re.ref n) hW' (fun _ => hsm)
    rw [hWmap] at h1
    have h2 : (0 : ℝ) ≤ (I W 1 fun _ => (combLine Re.ref n).a : ℤ) := by
      rw [← h1]; exact h0
    rw [← fin_one_const]
    exact_mod_cast h2
  refine ⟨hnef, ?_⟩
  intro hpos β dβ _ _
  have hdeg := (hRe.2.2.2 n).2
  have hgp : 0 < geomDeg (mCoordIdeal y) (combLine Re.ref n) D := by
    rw [hdeg]
    exact mul_pos (by exact_mod_cast Re.deg_pos) hpos
  have h1 := GlobalTheory.T.generic_intersection_equals_points_integral hIn K ι I hI D (mCoordIdeal y) (fun _ => combLine Re.ref n) Re.arith (fun _ => hsm)
  have hI0 : 0 < I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) D (fun _ => (combLine Re.ref n).a) := by
    have : (0 : ℝ) < (I (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal y) D (fun _ => (combLine Re.ref n).a) : ℤ) := by
      rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.genIdeal, ← h1]; exact hgp
    exact_mod_cast this
  have hsec := hIn.siuZ K ι Ω y D (combLine Re.ref n).a I hI Re.arith hBir hnef hI0
  exact GlobalTheory.T.chart_lattice_shift_nonzero K ι Ω y (combLine Re.ref n).a dβ
    (exists_ne_zero_of_relevant y Re.arith.2.1.2.2) hsec

end GlobalTheory.CompanionTheory.Ar.PB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.BMx

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi

def blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : Matrix (Fin (p + q)) (Fin (p + q)) ℂ :=
  (Matrix.fromBlocks (omBlock Γ)ᵀ⁻¹ 0 0 (wBlock Γ)).submatrix (blockEquiv p q).symm (blockEquiv p q).symm

theorem wBlock_blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) : wBlock (blockG Γ) = wBlock Γ := by
  ext a b
  simp [wBlock, blockG, ← blockEquiv_inr]

theorem omBlock_blockG {p q : ℕ} (Γ : Matrix (Fin (p + q)) (Fin (p + q)) ℂ) :
    omBlock (blockG Γ) = (omBlock Γ)ᵀ⁻¹ := by
  ext a b
  simp [omBlock, blockG, ← blockEquiv_inl]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {M : FlagModel y (CMType H) (D.p + D.q) D.p} {𝔐 : HodgeCpt Y S M.x}

open Classical in

def dualFam (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin D.q → 𝔐.Vgen (.inr τ) :=
  if h : ∃ v : Fin D.q → 𝔐.Vgen (.inr τ), ∀ a b, tie.omFrame F τ a (v b) = if a = b then 1 else 0 then h.choose
  else 0

theorem wFrame_mem (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H)
    (a : Fin D.p) : tie.wFrame F τ a ∈ 𝔐.Vgen (.inl τ) := by
  unfold FlagTie.wFrame colFrame
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (tie.eW τ b).2

def gbS (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin (D.p + D.q) → ↥(𝔐.Vgen (.inl τ) ⊔ 𝔐.Vgen (.inr τ)) := fun i =>
  Sum.elim (fun a => ⟨(dualFam tie F τ a : 𝔐.Li), Submodule.mem_sup_right (dualFam tie F τ a).2⟩)
    (fun a => ⟨tie.wFrame F τ a, Submodule.mem_sup_left (wFrame_mem tie F τ a)⟩) ((blockEquiv D.p D.q).symm i)

def gb (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) :
    Fin (D.p + D.q) → 𝔐.Li := fun i => (gbS tie F τ i : 𝔐.Li)

def baseGram (tie : FlagTie M 𝔐) (F : FrameData ι (CMType H) (D.p + D.q) M.Ω M.blk) (τ : CMType H) {n : ℕ}
    (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (x : Rb.X) : Matrix (Fin (D.p + D.q)) (Fin (D.p + D.q)) ℂ :=
  HodgeMetric.gramFn 𝔐 (gb tie F τ) (Rb.lift x x)

end GlobalTheory.CompanionTheory.Ar.PB.BMx
end
end

