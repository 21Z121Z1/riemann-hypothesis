import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeDominantCompat
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0144
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0061
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0024
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0050
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
import GroundTheory.HeightsAndTheta.Heights.Intersections.PtsIntegralLogNormRat
import GroundTheory.HeightsAndTheta.Heights.SemipositiveHeights.PtsIntegrable
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0021
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0023
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsFlagsLieCompactDominated
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.FlagsLieBaseChange

theorem bc {S : Scheme.{0}} {G : Over S} [GrpObj G] (hs : Smooth G.hom) {R R' : Type} [Field R] [Field R']
    (f : R →+* R') (x : Spec (CommRingCat.of R) ⟶ S) (y : Spec (CommRingCat.of R') ⟶ S)
    (hy : Spec.map (CommRingCat.ofHom f) ≫ x = y) {E E' : Type} [AddCommGroup E] [Module R E] [AddCommGroup E']
    [Module R' E'] (M : LieModel G x E) (M' : LieModel G y E') :
    ∃ j : E →+ E', (∀ e, (M'.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap f)) ≫ (M.pt e).left) ∧
      IsExtOver f j ∧ Submodule.span R' (Set.range j) = ⊤ ∧ Module.Finite R E := by
  subst hy
  let _ := f.toAlgebra
  obtain ⟨j, hj, hl, hb⟩ := PositivityTheory.HtPt.Htat.lie_bc S G R R' x E E' M M'
  haveI := hs
  haveI : Module.Finite R E := (PositivityTheory.HtPt.Htat.lie_fin S G R x E M).1
  let b₁ := Module.finBasis R E
  refine ⟨j, hj, ⟨hl, fun n b h => LiePull.indep_of_bases b₁ j (fun m B => (hb hs m B).1) b h⟩, ?_, inferInstance⟩
  refine top_le_iff.1 ((hb hs _ b₁).2.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨_, rfl⟩

theorem basis {F Ω V W : Type} [Field F] [Field Ω] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module Ω W]
    [Module.Finite F V] {i : F →+* Ω} {j : V →+ W} (hj : IsExtOver i j) (U : Submodule F V) (U' : Submodule Ω W)
    (h : U' = Submodule.span Ω (j '' (U : Set V))) {n : ℕ} (B : Module.Basis (Fin n) Ω U') :
    ∃ b : Fin n → V, LinearIndependent F b ∧ Submodule.span F (Set.range b) = U := by
  let b := Module.finBasis F U
  have h1 : LinearIndependent F (fun k => (b k : V)) := b.linearIndependent.map' U.subtype U.ker_subtype
  have h2 : Submodule.span F (Set.range fun k => (b k : V)) = U := by
    have := congrArg (Submodule.map U.subtype) b.span_eq
    rwa [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at this
  have h3 := hj.2 _ _ h1
  have h4 : Submodule.span Ω (Set.range fun k => j (b k : V)) = U' := by
    rw [h]
    refine le_antisymm (Submodule.span_mono ?_) (Submodule.span_le.2 ?_)
    · rintro _ ⟨k, rfl⟩
      exact ⟨_, (b k).2, rfl⟩
    · rintro _ ⟨e, he, rfl⟩
      rw [← h2] at he
      obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun F).1 he
      rw [map_sum]
      refine Submodule.sum_mem _ fun k _ => ?_
      rw [hj.1]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have h5 : Module.finrank F U = n := by
    have := finrank_span_eq_card h3
    rw [h4, Module.finrank_eq_card_basis B, Fintype.card_fin, Fintype.card_fin] at this
    exact this.symm
  subst h5
  exact ⟨_, h1, h2⟩

end PositivityTheory.Xgp.FlagsLieBaseChange

open PositivityTheory.Xgp.FlagsLieBaseChange in
theorem PositivityTheory.Xgp.exists_flags_lie_compact_dominated : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) (x : (Σ k, J k) → Ω) (A : HodgeCpt Y S x) (F₀ : Type) [Field F₀] (ξ₀ : Spec (CommRingCat.of F₀) ⟶ Y.X) (ι : F₀ →+* Ω), IsCptGen ξ₀ → GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f ι → ∃ (Li₀ : Type) (_ : AddCommGroup Li₀) (_ : Module F₀ Li₀) (M₀ : LieModel Y.t.G ξ₀ Li₀) (j₁ : Li₀ →+ A.Li) (V₀ : CMType H ⊕ CMType H → Submodule F₀ Li₀) (b : ∀ s, Fin (labelRk D s) → Li₀), (∀ e, (A.M.pt (j₁ e)).left ≫ A.m.φ = spMap (dualMap ι) ≫ (M₀.pt e).left) ∧ IsExtOver ι j₁ ∧ (∀ s e, e ∈ V₀ s ↔ j₁ e ∈ A.Vgen s) ∧ ∀ s, LinearIndependent F₀ (b s) ∧ Submodule.span F₀ (Set.range (b s)) = V₀ s := by
  intro E _ _ _ H D l Xo c Y S Ω _ _ K _ J x A F₀ _ ξ₀ ι hgen hd
  obtain ⟨Li₀, _, _, ⟨M₀⟩⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists _ Y.t.G F₀ ξ₀
  obtain ⟨ρ₀, hact₀, -⟩ := GlobalTheory.CompanionTheory.Ar.lieModel_exists_unique_act _ Y.t.G F₀ ξ₀ Li₀ M₀ (𝓞 E) Y.t.act.act
    Y.t.act.hom Y.t.act.one Y.t.act.mul Y.t.act.add
  obtain ⟨j, hj, hext, hsp, hfin⟩ := bc Y.t.semi.smooth ι ξ₀ (A.ξ ≫ A.f) (Eq.symm hd) M₀
    (LieMove.pushModel A.m.cart A.M)
  have hj' : ∀ e, (A.M.pt (j e)).left ≫ A.m.φ = spMap (dualMap ι) ≫ (M₀.pt e).left := hj
  have hint := FlagStep.lieMap_act_pull E H Y.X A.X Y.t A.t A.f A.m F₀ Ω ξ₀ A.ξ ι Li₀ A.Li M₀ A.M ρ₀ A.ρ j hd hact₀
    A.act hj'
  have hjinj : Function.Injective j := by
    refine (injective_iff_map_eq_zero j).2 fun e he => ?_
    by_contra hne
    have h1 := hext.2 1 (fun _ => e) (LinearIndependent.of_subsingleton (0 : Fin 1) hne)
    exact h1.ne_zero (0 : Fin 1) he
  let a : 𝓞 c.F →+* F₀ := (Spec.preimage (ξ₀ ≫ Y.s)).hom
  have ha : spMap a = ξ₀ ≫ Y.s := by
    simp only [spMap, a, CommRingCat.ofHom_hom, Spec.map_preimage]
  have hfa : ι.comp a = A.cst.comp (algebraMap (𝓞 c.F) c.F) := by
    have h1 : spMap (ι.comp a) = spMap (A.cst.comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← A.cst_over]
      have hd' : A.ξ ≫ A.f = spMap ι ≫ ξ₀ := hd
      calc spMap (ι.comp a) = spMap ι ≫ spMap a := by
            simp only [spMap, ← Spec.map_comp]; rfl
        _ = A.ξ ≫ A.f ≫ Y.s := by rw [ha, ← Category.assoc, ← hd', Category.assoc]
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  have : NumberField c.F := { to_charZero := inferInstance, to_finiteDimensional := c.fin }
  have hainj : Function.Injective a := by
    have : Function.Injective (ι.comp a) := by
      rw [hfa]
      exact A.cst.injective.comp (IsFractionRing.injective (𝓞 c.F) c.F)
    exact Function.Injective.of_comp (f := ι) this
  let a' : c.F →+* F₀ := IsFractionRing.lift hainj
  have ha' : ι.comp a' = A.cst := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 c.F)) ?_
    rw [← hfa]
    refine RingHom.ext fun o => ?_
    exact congrArg ι (IsFractionRing.lift_algebraMap hainj o)
  haveI : CharZero F₀ := ι.charZero
  let σ : CMType H ⊕ CMType H → (𝓞 E →+* F₀) := fun s => a'.comp (labelEmb c s)
  have hσ : ∀ s, A.emb s = ι.comp (σ s) := fun s => by
    rw [← RingHom.comp_assoc, ha']
    rfl
  have hV : ∀ s, A.Vgen s = Submodule.span Ω (j '' (eigSp ρ₀ (σ s) : Set Li₀)) := fun s => by
    unfold HodgeCpt.Vgen
    rw [hσ]
    exact EigExt.eigSp_ext E F₀ Ω ι Li₀ A.Li j ρ₀ A.ρ (σ s) hext hsp fun a e => (hint a e).symm
  have hb := fun s => basis hext _ _ (hV s) (nonempty_basis_Vgen A s).some
  choose b hb using hb
  refine ⟨Li₀, inferInstance, inferInstance, M₀, j, fun s => eigSp ρ₀ (σ s), b, hj', hext, fun s e => ?_, hb⟩
  unfold HodgeCpt.Vgen
  rw [hσ]
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]
  refine forall_congr' fun a => ?_
  rw [← hint a e, RingHom.comp_apply ι, ← hext.1]
  exact hjinj.eq_iff.symm
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XReBridge
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.re_bridge

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  refine potSmoothAt A Q h x j ⟨(A.chart j).map_source hj, ?_⟩
  show (A.chart j).symm (A.chart j x) ∈ Q.U x
  rw [(A.chart j).left_inv hj]
  exact Q.mem_U x

theorem isNull_union {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X} {N N' : Set X}
    (h : IsNull A N) (h' : IsNull A N') : IsNull A (N ∪ N') := by
  intro j
  rw [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (h j) (h' j)

theorem isNull_zeros {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {D : ℕ}
    (R : AnLogRes P J D) (hP : IsArithVar P (D + 1)) {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    (hsP : s ∉ P) : IsNull R.A {x | eval (R.lift x x) (map (Int.castRingHom ℂ) s) = 0} := by
  obtain ⟨Ψ, hΨ⟩ := goodProjExists K ι P D hP
  exact fun j => GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.zeros_null R Ψ hP hΨ hs hsP j

end PositivityTheory.Xgp.re_bridge

theorem PositivityTheory.Xgp.t_re_bridge : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P J : Ideal (MRing ι)) (D : ℕ) (R : AnLogRes P J D) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R.X → X) (hπ : HoloMap R.A A π) (dg : ℕ) (br : Set X), IsArithVar P (D + 1) → IsDegreeOff A R.A π dg br → ∀ (L : Fin D → HermLine ι) (Φ : Fin D → LocPot X), (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPotential A (Φ j)) → (∀ j, SamePot R.A Set.univ (potOf R (L j)) ((Φ j).pullback π hπ.1)) → ∀ (Am : HermLine ι) (f g : MRing ι) (u : X → ℝ) (N : Set R.X), IsSmoothHerm Am → IsRatSectionOn P Am f g → IsNull R.A N → (∀ x ∉ N, logNormRat Am f g (R.lift x x) = u (π x)) → MIntegrable A Φ u → ptsIntegral P (pot L) (logNormRat Am f g) = dg * mInt A Φ u := by
  intro hE K _ ι _ P J D R X _ _ _ A π hπ dg br hP hdeg L Φ hL hΦ hS Am f g u N hAm hfg hN hu hI
  obtain ⟨α, β, hf, hg, hfP, hgP, hαβ⟩ := hfg
  have hB : IsSmoothHerm (HermLine.sqMetric (ι := ι) β) := isSmoothHerm_sqMetric β
  have hAB := ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_tensor hAm hB
  have hsf : IsSectionOn P (Am.tensor (HermLine.sqMetric β)) f := by
    refine ⟨α, fun k => ?_, hf, hfP⟩
    show Am.a k + (β k : ℤ) = α k
    rw [← hαβ k]
    ring
  have hsg : IsSectionOn P (HermLine.sqMetric (ι := ι) β) g := ⟨β, fun k => rfl, hg, hgP⟩
  have hQ : ∀ j, IsPotential R.A (potOf R (L j)) := fun j => isPotential_potOf R (hL j)
  rw [GroundTheory.Heights₂.Heights.Inter.ArithmeticIntersectionIntegral.ptsIntegral_logNormRat
      (GroundTheory.Heights₂.Heights.ForSecondHalf.PtsIntegrable.of_resExists hE) hP hL hAm hB hsf hsg,
    ptsIntegral_eq_mInt' hE resBridge R hP hL hAB hsf, ptsIntegral_eq_mInt' hE resBridge R hP hL hB hsg,
    ← (degreeFormulaInt A R.A π hπ dg br hdeg Φ hΦ u hI).2]
  have hlin := mIntLinear R.A _ hQ (-1) _ _ (brIntegrable R L _ g hP hL hB hsg)
    (brIntegrable R L _ f hP hL hAB hsf)
  have hnull := PositivityTheory.Xgp.re_bridge.isNull_union hN (PositivityTheory.Xgp.re_bridge.isNull_union
    (PositivityTheory.Xgp.re_bridge.isNull_zeros R hP hf hfP) (PositivityTheory.Xgp.re_bridge.isNull_zeros R hP hg hgP))
  have key := (mInt_congr_samePot D R.X R.A
    (N ∪ ({x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0} ∪
      {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) = 0}))ᶜ
    (fun j => potOf R (L j)) (fun j => (Φ j).pullback π hπ.1)
    (fun x => -1 * logNorm (HermLine.sqMetric β) g (R.lift x x) +
      logNorm (Am.tensor (HermLine.sqMetric β)) f (R.lift x x)) (u ∘ π)
    (by rwa [compl_compl]) (fun j x _ => hS j x (Set.mem_univ x))
    (fun j x _ => PositivityTheory.Xgp.re_bridge.isC2At_of_isPotential R.A
      (isPotentialPullback A R.A π hπ _ (hΦ j)) x) ?_).1
  · rw [← key, hlin]
    ring
  · intro x hx
    simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at hx
    obtain ⟨hxN, hxf, hxg⟩ := hx
    have hz := (R.mem x x (R.mem_U x)).1
    have hf0 := norm_pos_iff.mpr hxf
    have hg0 := norm_pos_iff.mpr hxg
    have hA0 := Am.pos _ hz
    have hB0 := (HermLine.sqMetric (ι := ι) β).pos _ hz
    show _ = u (π x)
    rw [← hu x hxN]
    show -1 * Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖ / (HermLine.sqMetric β).h (R.lift x x)) +
      Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) f)‖ /
        (Am.h (R.lift x x) * (HermLine.sqMetric β).h (R.lift x x))) =
      Real.log (‖eval (R.lift x x) (map (Int.castRingHom ℂ) f)‖ /
        ‖eval (R.lift x x) (map (Int.castRingHom ℂ) g)‖ / Am.h (R.lift x x))
    rw [Real.log_div hf0.ne' (mul_pos hA0 hB0).ne', Real.log_mul hA0.ne' hB0.ne',
      Real.log_div hg0.ne' hB0.ne', Real.log_div (div_pos hf0 hg0).ne' hA0.ne',
      Real.log_div hf0.ne' hg0.ne']
    ring
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XSqLimit
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.sq_limit

open scoped ContDiff

section Gen

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem continuousOn_of_smoothOn (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {f : X → ℝ}
    (hf : A.SmoothOn U f) : ContinuousOn f U := by
  intro x hx
  obtain ⟨j, hj⟩ := A.cover x
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).isOpen_inter_preimage_symm hU
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (hf j).continuousOn.continuousAt (hO.mem_nhds hmem)
  have h2 : ContinuousAt (A.chart j) x := (A.chart j).continuousAt hj
  have h3 : ContinuousAt (fun y => (f ∘ (A.chart j).symm) (A.chart j y)) x := h1.comp h2
  refine (h3.congr ?_).continuousWithinAt
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem member_unif (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {ph : X → ℝ} {phT : ℝ → X → ℝ}
    (hC2 : ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, IsCompact K →
      TendstoUniformlyOn (fun t => phT t ∘ (A.chart j).symm) (ph ∘ (A.chart j).symm) (𝓝[>] 0) K)
    {x : X} (hx : x ∈ U) {δ : ℝ} (hδ : 0 < δ) :
    ∃ V ∈ 𝓝 x, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ y ∈ V, |phT t y - ph y| < δ := by
  obtain ⟨j, hj⟩ := A.cover x
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U) :=
    (A.chart j).isOpen_inter_preimage_symm hU
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hO _ hmem
  have hK : Metric.closedBall (A.chart j x) (r / 2) ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hu := Metric.tendstoUniformlyOn_iff.1 (hC2 j _ hK (isCompact_closedBall _ _)) δ hδ
  refine ⟨(A.chart j).source ∩ (A.chart j) ⁻¹' Metric.ball (A.chart j x) (r / 2), ?_, ?_⟩
  · exact Filter.inter_mem ((A.chart j).open_source.mem_nhds hj)
      ((A.chart j).continuousAt hj (Metric.ball_mem_nhds _ (by linarith)))
  · filter_upwards [hu] with t ht y hy
    have h1 := ht (A.chart j y) (Metric.ball_subset_closedBall hy.2)
    simp only [Function.comp, (A.chart j).left_inv hy.1, Real.dist_eq] at h1
    rwa [abs_sub_comm] at h1

theorem sum_unif (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U) {ι : Type} [Fintype ι]
    (ph : ι → X → ℝ) (phT : ι → ℝ → X → ℝ) (c : ι → ℝ) (cst : ℝ)
    (hC2 : ∀ i, ∀ j, ∀ K ⊆ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, IsCompact K →
      TendstoUniformlyOn (fun t => phT i t ∘ (A.chart j).symm) (ph i ∘ (A.chart j).symm) (𝓝[>] 0) K)
    (t₀ : ℝ) (ht₀ : 0 < t₀) :
    TendstoLocallyUniformlyOn
      (fun t x => if 0 < t ∧ t ≤ t₀ then cst + ∑ i, c i * phT i t x else cst + ∑ i, c i * ph i x)
      (fun x => cst + ∑ i, c i * ph i x) (𝓝[>] 0) U := by
  rw [Metric.tendstoLocallyUniformlyOn_iff]
  intro ε hε x hx
  have hM0 : 0 ≤ ∑ i, |c i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have hδ : 0 < ε / (∑ i, |c i| + 1) := div_pos hε (by linarith)
  choose V hV hev using fun i => member_unif A hU (hC2 i) hx hδ
  refine ⟨⋂ i, V i, mem_nhdsWithin_of_mem_nhds (Filter.iInter_mem.2 hV), ?_⟩
  filter_upwards [Filter.eventually_all.2 hev, Ioc_mem_nhdsGT ht₀] with t ht htt y hy
  rw [if_pos ⟨htt.1, htt.2⟩, Real.dist_eq]
  have hy' : ∀ i, y ∈ V i := Set.mem_iInter.1 hy
  have e1 : cst + ∑ i, c i * ph i y - (cst + ∑ i, c i * phT i t y) = ∑ i, c i * (ph i y - phT i t y) := by
    rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [e1]
  calc |∑ i, c i * (ph i y - phT i t y)| ≤ ∑ i, |c i * (ph i y - phT i t y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |c i| * (ε / (∑ i, |c i| + 1)) := Finset.sum_le_sum fun i _ => by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (by rw [abs_sub_comm]; exact (ht i y (hy' i)).le) (abs_nonneg _)
    _ = (∑ i, |c i|) * (ε / (∑ i, |c i| + 1)) := by rw [Finset.sum_mul]
    _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith

theorem abs_lin_le {ι : Type} [Fintype ι] (c : ι → ℝ) (cst : ℝ) (f : ι → ℝ) {B l : ℝ}
    (hf : ∀ i, |f i| ≤ B * l) (hl : 1 ≤ l) :
    |cst + ∑ i, c i * f i| ≤ (|cst| + ∑ i, |c i| * B) * l := by
  have h1 : |cst + ∑ i, c i * f i| ≤ |cst| + ∑ i, |c i| * |f i| := by
    refine (abs_add_le _ _).trans (add_le_add le_rfl ?_)
    refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    exact Finset.sum_congr rfl fun i _ => abs_mul _ _
  have h2 : ∑ i, |c i| * |f i| ≤ ∑ i, |c i| * (B * l) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hf i) (abs_nonneg _)
  have h3 : |cst| ≤ |cst| * l := le_mul_of_one_le_right (abs_nonneg _) hl
  have h4 : (|cst| + ∑ i, |c i| * B) * l = |cst| * l + ∑ i, |c i| * (B * l) := by
    rw [add_mul, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h4]
  linarith

end Gen

theorem regular (hC : ConvergenceSignedStatement) {e : ℕ} {τ : Type} (S : AnSys e τ) (w : Fin e → τ)
    {ι : Type} [Fintype ι] (mm : ι → τ) (c : ι → ℝ) (cst : ℝ) (ht₀ : 0 < S.t₀) :
    MIntegrable S.A (fun r => S.potH (w r)) (fun x => cst + ∑ i, c i * S.ph (mm i) x) ∧
      Tendsto (fun t => mInt S.A (fun r => S.potT (w r) t) (fun x => cst + ∑ i, c i * S.phT (mm i) t x))
        (𝓝[>] 0) (𝓝 (mInt S.A (fun r => S.potH (w r)) (fun x => cst + ∑ i, c i * S.ph (mm i) x))) := by
  letI : MeasurableSpace S.X := borel S.X
  haveI : BorelSpace S.X := ⟨rfl⟩
  obtain ⟨hopen, -, -, -, hrW⟩ := GlobalTheory.CompanionTheory.Ar.PB.anSys_open_basics e τ S
  have hU : IsOpen (bdry S.s)ᶜ := hopen
  have hl : ∀ y, y ∉ bdry S.s → 1 ≤ Real.log (rW S.L S.s y) := fun y hy => by
    have h := hrW y hy
    have h1 := Real.log_le_log (Real.exp_pos 1) h
    rwa [Real.log_exp] at h1
  have hph : ∀ o y, y ∉ bdry S.s → |S.ph o y| ≤ (|S.C| + |S.C₅|) * Real.log (rW S.L S.s y) := by
    intro o y hy
    obtain ⟨h1, h2⟩ := (S.sing o).2.2.2 y hy
    have := hl y hy
    refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [abs_nonneg S.C, abs_nonneg S.C₅, le_abs_self S.C₅,
      neg_abs_le S.C₅, le_abs_self S.C]
  have hphT : ∀ o t, 0 < t → t ≤ S.t₀ → ∀ y, y ∉ bdry S.s →
      |S.phT o t y| ≤ (|S.C| + |S.C₅|) * Real.log (rW S.L S.s y) := by
    intro o t h0 h1 y hy
    obtain ⟨-, hle, hge, -⟩ := (S.reg o).2.2 t h0 h1
    have a1 := hle y
    have a2 := hge y hy
    obtain ⟨b1, -⟩ := (S.sing o).2.2.2 y hy
    have := hl y hy
    refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith [abs_nonneg S.C, abs_nonneg S.C₅, le_abs_self S.C₅,
      neg_abs_le S.C₅, le_abs_self S.C]
  have hgc : ∀ t, ContinuousOn (fun x => if 0 < t ∧ t ≤ S.t₀ then cst + ∑ i, c i * S.phT (mm i) t x
      else cst + ∑ i, c i * S.ph (mm i) x) (bdry S.s)ᶜ := by
    intro t
    by_cases ht : 0 < t ∧ t ≤ S.t₀
    · simp only [ht, and_self, if_true]
      refine continuousOn_const.add (continuousOn_finset_sum _ fun i _ => continuousOn_const.mul ?_)
      exact (continuousOn_of_smoothOn S.A isOpen_univ ((S.reg (mm i)).2.2 t ht.1 ht.2).1).mono
        (Set.subset_univ _)
    · simp only [ht, if_false]
      exact continuousOn_const.add (continuousOn_finset_sum _ fun i _ => continuousOn_const.mul
        (continuousOn_of_smoothOn S.A hU (S.sing (mm i)).2.1))
  have hgb : ∀ t y, y ∉ bdry S.s → |(fun x => if 0 < t ∧ t ≤ S.t₀ then cst + ∑ i, c i * S.phT (mm i) t x
      else cst + ∑ i, c i * S.ph (mm i) x) y| ≤
      (|cst| + ∑ i, |c i| * (|S.C| + |S.C₅|)) * Real.log (rW S.L S.s y) := by
    intro t y hy
    by_cases ht : 0 < t ∧ t ≤ S.t₀
    · simp only [ht, and_self, if_true]
      exact abs_lin_le c cst _ (fun i => hphT (mm i) t ht.1 ht.2 y hy) (hl y hy)
    · simp only [ht, if_false]
      exact abs_lin_le c cst _ (fun i => hph (mm i) y hy) (hl y hy)
  have hlim := sum_unif S.A hU (fun i => S.ph (mm i)) (fun i => S.phT (mm i)) c cst
    (fun i j K hK hKc => ((S.c2 (mm i)) j K hK hKc).1) S.t₀ ht₀
  have h := hC S.A S.Θ S.L S.s S.m S.W S.potΘ S.posΘ S.potL S.sec S.snc S.norm_le
    (fun r => S.th (w r)) (fun r => S.ph (w r)) (fun r => S.phT (w r)) S.C₅ S.C S.t₀
    (fun r => S.sing (w r)) (fun r => S.reg (w r)) (fun r => S.c2 (w r))
    (fun x => cst + ∑ i, c i * S.ph (mm i) x) _ _ hgc hgb hlim
  refine ⟨h.1, h.2.congr' ?_⟩
  filter_upwards [Ioc_mem_nhdsGT ht₀] with t ht
  have e1 : (fun x => if 0 < t ∧ t ≤ S.t₀ then cst + ∑ i, c i * S.phT (mm i) t x
      else cst + ∑ i, c i * S.ph (mm i) x) = fun x => cst + ∑ i, c i * S.phT (mm i) t x := by
    funext x
    rw [if_pos ⟨ht.1, ht.2⟩]
  rw [e1]
  rfl

section Lin

variable {e : ℕ} {X : Type} [TopologicalSpace X]

theorem mIntegrable_add' (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) {f g : X → ℝ}
    (hf : MIntegrable A Φ f) (hg : MIntegrable A Φ g) : MIntegrable A Φ (fun x => f x + g x) := by
  intro j K hK hKc
  refine ((hf j K hK hKc).add (hg j K hK hKc)).congr_fun (fun y _ => ?_) hKc.measurableSet
  simp only [Pi.add_apply]
  ring

theorem mInt_add' [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) {f g : X → ℝ}
    (hf : MIntegrable A Φ f) (hg : MIntegrable A Φ g) :
    mInt A Φ (fun x => f x + g x) = mInt A Φ f + mInt A Φ g := by
  unfold mInt
  split_ifs with h
  · unfold integralWith
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← integral_add (ReciprocityTheory.AnForm.M.integrableOn_weight A h.some Φ f hf j)
      (ReciprocityTheory.AnForm.M.integrableOn_weight A h.some Φ g hg j)]
    congr 1
    funext y
    ring
  · simp

theorem mIntegrable_of_continuous (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) {g : X → ℝ} (hg : Continuous g) : MIntegrable A Φ g := by
  intro j K hK hKc
  exact ((hg.comp_continuousOn ((A.chart j).continuousOn_symm.mono hK)).mul
    ((ReciprocityTheory.AnForm.M.locDensCont A Φ hΦ j).mono hK)).integrableOn_compact hKc

end Lin

end PositivityTheory.Xgp.sq_limit
end

