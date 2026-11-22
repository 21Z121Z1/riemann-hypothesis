import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
import ReciprocityTheory.AnalyticForms.LeviForms.UnifInt
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0031
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0054
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0029
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0003

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsomorphicLinesPotentialDifference
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cmp.OneModel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
  GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open scoped ContDiff

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_pair_ne {P : Ideal (MRing ι)} {f g : MRing ι} (h : UnitRatio P f g) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts P) : ∃ u v : MRing ι, u * f - v * g ∈ P ∧ evC z u ≠ 0 ∧ evC z v ≠ 0 := by
  let ρ : MRing ι →+* ℂ := (eval z).comp (map (Int.castRingHom ℂ))
  have hprime : (RingHom.ker ρ).IsPrime := RingHom.ker_isPrime ρ
  have hle : P ≤ RingHom.ker ρ := fun q hq => hz.2 q hq
  have hrel : IsRelevant (RingHom.ker ρ) := fun k => by
    obtain ⟨i, hi⟩ := hz.1 k
    refine ⟨i, fun hm => hi ?_⟩
    simpa [ρ] using (RingHom.mem_ker.1 hm)
  obtain ⟨u, v, hu, hv, huv⟩ := h.2.2 _ hprime hle hrel
  exact ⟨u, v, huv, fun h0 => hu (RingHom.mem_ker.2 h0), fun h0 => hv (RingHom.mem_ker.2 h0)⟩

theorem log_line_of_orbit {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (a : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) (x : Re.R.X) (z : (Σ k, ι k) → ℂ) (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ho : SameOrbit (Re.R.lift x x) z) :
    Real.log ((Re.line a t).h z) = Real.log ((Re.ref a).h z) + S.phT a t (Re.π x) := by
  obtain ⟨c, hc, e⟩ := ho
  have h := Re.line_eq a t h0 h1 x
  rw [e, (Re.line a t).smul c z hc, (Re.ref a).smul c z hc, Re.line_deg] at h
  have hp : (∏ k, ‖c k‖ ^ (Re.ref a).a k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (norm_ne_zero_iff.2 (hc k))
  rw [Real.log_mul hp ((Re.line a t).pos z hz).ne', Real.log_mul hp ((Re.ref a).pos z hz).ne'] at h
  linarith

theorem samePot_line {D : ℕ} {σ : Type} {S : AnSys D σ} {P : Ideal (MRing ι)} (Re : Realis S P) (c : σ) (t : ℝ)
    (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    SamePot Re.R.A Set.univ (potOf Re.R (Re.line c t)) ((S.potT c t).pullback Re.π Re.holo.1) := by
  intro x _
  obtain ⟨V, hV, hxV, G, hG, hVG⟩ := Re.ref_pot c x (Set.mem_univ x)
  refine ⟨V ∩ Re.R.U x, hV.inter (Re.R.isOpen_U x), ⟨hxV, Re.R.mem_U x⟩, G, ?_, ?_⟩
  · intro j
    exact (hG j).mono fun y hy => ⟨hy.1, hy.2.1⟩
  · rintro y ⟨hyV, hyU⟩
    have hm := Re.R.mem x y hyU
    have ho : SameOrbit (Re.R.lift y y) (Re.R.lift x y) := Re.R.compat y x y ⟨Re.R.mem_U y, hyU⟩
    have e1 := log_line_of_orbit Re c t h0 h1 y _ hm.1 ho
    have e2 : Real.log ((Re.ref c).h (Re.R.lift x y)) - (S.th c).φ (Re.π x) (Re.π y) = (G y).re := hVG y hyV
    show Real.log ((Re.line c t).h (Re.R.lift x y)) -
      ((S.th c).φ (Re.π x) (Re.π y) + S.phT c t (Re.π y)) = (G y).re
    linarith

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x) :=
    (A.chart j).isOpen_inter_preimage_symm (Q.isOpen_U x)
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Q.U x :=
    ⟨(A.chart j).map_source hj, by
      show (A.chart j).symm (A.chart j x) ∈ Q.U x
      rw [(A.chart j).left_inv hj]
      exact Q.mem_U x⟩
  exact ((h.1 x j).contDiffAt (hopen.mem_nhds hmem)).of_le (by
    have h2 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top
    exact h2)

theorem continuous_of_smooth {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {f : X → ℝ}
    (h : A.Smooth f) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨j, hj⟩ := A.cover x
  have hmem : A.chart j x ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ :=
    ⟨(A.chart j).map_source hj, Set.mem_univ _⟩
  have hopen : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Set.univ) := by
    simpa using (A.chart j).open_target
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j x) :=
    (h j).continuousOn.continuousAt (hopen.mem_nhds hmem)
  have h2 : ContinuousAt ((f ∘ (A.chart j).symm) ∘ A.chart j) x :=
    ContinuousAt.comp h1 ((A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with y hy
  simp [(A.chart j).left_inv hy]

theorem step_eq (hR : RatRStatement) (hB : ResBridgeStatement) (hG : GoodProjExistsStatement) (hA : AvoidStatement)
    (II : IntersectionSystem) (hI : IsIntersectionFamily (II K ι)) {P : Ideal (MRing ι)} {D : ℕ} {τ : Type}
    {S : AnSys D τ} (Re : Realis S P) (a₁ a₂ : τ) (f g : MRing ι) (d : S.X → ℝ)
    (hiso : IsLineIso P (Re.ref a₁).a (Re.ref a₂).a f g) (hd : S.A.Smooth d)
    (hlog : ∀ x, ∀ u v : MRing ι, u * f - v * g ∈ P → evC (Re.R.lift x x) u ≠ 0 →
      d (Re.π x) = Real.log (‖evC (Re.R.lift x x) v‖ / ‖evC (Re.R.lift x x) u‖ *
        (Re.ref a₂).h (Re.R.lift x x) / (Re.ref a₁).h (Re.R.lift x x)))
    (u : Fin D → τ) (t : ℝ) (h0 : 0 < t) (h1 : t ≤ S.t₀) :
    II K ι P (D + 1) (Fin.snoc (fun j => Re.line (u j) t) (Re.line a₁ t)) -
        II K ι P (D + 1) (Fin.snoc (fun j => Re.line (u j) t) (Re.line a₂ t)) =
      Re.deg * mInt S.A (fun j => S.potT (u j) t) (fun x => S.phT a₁ t x - S.phT a₂ t x - d x) := by
  have hl₁ := Re.line_smooth a₁ t h0 h1
  have hl₂ := Re.line_smooth a₂ t h0 h1
  have hIso : IsLineIso P (Re.line a₁ t).a (Re.line a₂ t).a f g := by
    rw [Re.line_deg, Re.line_deg]
    exact hiso
  obtain ⟨w, hw, -, -⟩ := GlobalTheory.T.line_isomorphism_defect_function K ι P Re.J D Re.R (Re.line a₁ t) (Re.line a₂ t) f g Re.arith.2.1 hIso hl₁ hl₂
  have h := GlobalTheory.T.intersection_family_defect_formula hR hB hG hA K ι (II K ι) hI P Re.J D Re.R (fun j => Re.line (u j) t) (Re.line a₁ t)
    (Re.line a₂ t) f g w Re.arith (fun j => Re.line_smooth _ t h0 h1) hl₁ hl₂ hIso hw
  rw [h]
  have hval : ∀ x, w (Re.R.lift x x) = -(S.phT a₁ t (Re.π x) - S.phT a₂ t (Re.π x) - d (Re.π x)) := by
    intro x
    have hz := Re.R.mem x x (Re.R.mem_U x)
    obtain ⟨p, q, hpq, hp, hq⟩ := exists_pair_ne hiso.2 hz
    have e0 := hw _ hz p q hpq hp
    have e1 := hlog x p q hpq hp
    have r₁ := Re.line_eq a₁ t h0 h1 x
    have r₂ := Re.line_eq a₂ t h0 h1 x
    have hc : 0 < ‖evC (Re.R.lift x x) q‖ / ‖evC (Re.R.lift x x) p‖ :=
      div_pos (norm_pos_iff.2 hq) (norm_pos_iff.2 hp)
    have l₁ := (Re.line a₁ t).pos _ hz.1
    have l₂ := (Re.line a₂ t).pos _ hz.1
    have f₁ := (Re.ref a₁).pos _ hz.1
    have f₂ := (Re.ref a₂).pos _ hz.1
    rw [Real.log_div (mul_pos hc l₂).ne' l₁.ne', Real.log_mul hc.ne' l₂.ne'] at e0
    rw [Real.log_div (mul_pos hc f₂).ne' f₁.ne', Real.log_mul hc.ne' f₂.ne'] at e1
    linarith
  have hpot : ∀ j, IsPotential S.A (S.potT (u j) t) := fun j =>
    isPotentialAdd S.A _ _ (S.sing (u j)).1 (isPotential_ofFun S.A _ ((S.reg (u j)).2.2 t h0 h1).1)
  have hcont : Continuous fun x => -(S.phT a₁ t x - S.phT a₂ t x - d x) :=
    (((continuous_of_smooth S.A ((S.reg a₁).2.2 t h0 h1).1).sub
      (continuous_of_smooth S.A ((S.reg a₂).2.2 t h0 h1).1)).sub (continuous_of_smooth S.A hd)).neg
  have hcongr := (GlobalTheory.CompanionTheory.Ar.PB.mInt_congr_samePot D Re.R.X Re.R.A Set.univ
    (fun j => potOf Re.R (Re.line (u j) t)) (fun j => (S.potT (u j) t).pullback Re.π Re.holo.1)
    (fun x => w (Re.R.lift x x))
    ((fun x => -(S.phT a₁ t x - S.phT a₂ t x - d x)) ∘ Re.π)
    (by simp [IsNull]) (fun j => samePot_line Re (u j) t h0 h1)
    (fun j x _ => isC2At_of_isPotential Re.R.A (isPotentialPullback S.A Re.R.A Re.π Re.holo _ (hpot j)) x)
    (fun x _ => hval x)).1
  rw [hcongr, degreeFormula S.A Re.R.A Re.π Re.holo Re.deg Re.br Re.degree (fun j => S.potT (u j) t) hpot _ hcont,
    mInt_neg_integrand]
  ring

theorem cmp_one : Inputs → AvoidStatement → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (σ : Type) (S : AnSys D (σ ⊕ σ)) (Re : Realis S P) (f g : σ → MRing ι) (d : σ → S.X → ℝ), (∀ a, IsLineIso P (Re.ref (Sum.inl a)).a (Re.ref (Sum.inr a)).a (f a) (g a)) → (∀ a, S.A.Smooth (d a)) → (∀ a, ∀ y ∈ S.open', S.ph (Sum.inl a) y = S.ph (Sum.inr a) y + d a y) → (∀ a x, ∀ u v : MRing ι, u * f a - v * g a ∈ P → evC (Re.R.lift x x) u ≠ 0 → d a (Re.π x) = Real.log (‖evC (Re.R.lift x x) v‖ / ‖evC (Re.R.lift x x) u‖ * (Re.ref (Sum.inr a)).h (Re.R.lift x x) / (Re.ref (Sum.inl a)).h (Re.R.lift x x))) → ∀ w : Fin (D + 1) → σ, Tendsto (fun t => Re.num II t (fun j => Sum.inl (w j)) - Re.num II t (fun j => Sum.inr (w j))) (𝓝[>] 0) (𝓝 0) := by
  intro hIn hA II hII K _ ι _ P D σ S Re f g d hiso hd hph hlog w
  have hI : IsIntersectionFamily (II K ι) := hII.1 K ι
  have ht : 0 < S.t₀ := (S.reg (Sum.inl (w 0))).1
  have hdeg : (Re.deg : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Re.deg_pos.ne'
  have hstep : ∀ i : Fin (D + 1), Tendsto (fun t =>
      Re.num II t (fun j => if j < i then Sum.inr (w j) else Sum.inl (w j)) -
        Re.num II t (fun j => if j ≤ i then Sum.inr (w j) else Sum.inl (w j))) (𝓝[>] 0) (𝓝 0) := by
    intro i
    let c : Fin (D + 1) → σ ⊕ σ := fun j => if j < i then Sum.inr (w j) else Sum.inl (w j)
    let c' : Fin (D + 1) → σ ⊕ σ := fun j => if j ≤ i then Sum.inr (w j) else Sum.inl (w j)
    let u : Fin D → σ ⊕ σ := fun j => c (i.succAbove j)
    have hT := GlobalTheory.T.monge_ampere_difference_tendsto_zero hIn.convergenceSigned D σ S d hd hph (w i) u
    refine hT.congr' ?_
    filter_upwards [Ioc_mem_nhdsGT ht] with t ht'
    have h0 := ht'.1
    have h1 := ht'.2
    have hci : c i = Sum.inl (w i) := by simp [c]
    have hci' : c' i = Sum.inr (w i) := by simp [c']
    have hcc : ∀ j : Fin D, c' (i.succAbove j) = u j := by
      intro j
      have hne : i.succAbove j ≠ i := Fin.succAbove_ne i j
      have hiff : i.succAbove j ≤ i ↔ i.succAbove j < i := ⟨fun h => lt_of_le_of_ne h hne, le_of_lt⟩
      simp only [c', u, c, hiff]
    have s₁ := GlobalTheory.T.intersection_family_symmetric K ι (II K ι) hI P D (fun j => Re.line (c j) t) i Re.arith
      (fun j => Re.line_smooth _ t h0 h1)
    have s₂ := GlobalTheory.T.intersection_family_symmetric K ι (II K ι) hI P D (fun j => Re.line (c' j) t) i Re.arith
      (fun j => Re.line_smooth _ t h0 h1)
    simp only [hci, hci', hcc] at s₁ s₂
    have hs := step_eq hIn.ratR (GlobalTheory.T.resolution_statement_holds) GlobalTheory.CompanionTheory.Ar.Link.goodProjExistsStatement_holds hA II hI Re
      (Sum.inl (w i)) (Sum.inr (w i)) (f (w i)) (g (w i)) (d (w i)) (hiso (w i)) (hd (w i)) (hlog (w i)) u t h0 h1
    show mInt S.A _ _ = Re.num II t c - Re.num II t c'
    simp only [Realis.num]
    rw [s₁, s₂, ← sub_div, hs, mul_div_cancel_left₀ _ hdeg]
  have hsum := tendsto_finset_sum Finset.univ fun i (_ : i ∈ Finset.univ) => hstep i
  simp only [Finset.sum_const_zero] at hsum
  refine hsum.congr fun t => ?_
  exact (GlobalTheory.T.telescoping_coordinate_difference (σ ⊕ σ) (D + 1) (Re.num II t) _ _).symm

end GlobalTheory.CompanionTheory.Ar.Cmp.OneModel
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MaMeasureEqOfConst
section
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem maMeasure_eq_of_const {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (A : FinHolAtlas e X) (Φ Ψ : Fin e → LocPot X) (c : Fin e → ℝ)
    (h : ∀ i x y, (Ψ i).φ x y = (Φ i).φ x y + c i) : maMeasure A Ψ = maMeasure A Φ := by
  have hH : ∀ (F : (Fin e → ℂ) → ℝ) (a : ℝ) (y : Fin e → ℂ),
      hessC (fun z => F z + a) y = hessC F y := by
    intro F a y
    have h1 : fderiv ℝ (fun z => F z + a) = fderiv ℝ F := funext fun z => fderiv_add_const a
    unfold hessC
    rw [h1]
  have hD : ∀ j, locDens A Ψ j = locDens A Φ j := by
    intro j
    funext y
    unfold locDens maDens
    have hk : (fun k => hessC (fun y' => (Ψ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y) =
        fun k => hessC (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) y := by
      funext k
      simp only [h k]
      exact hH _ _ y
    rw [hk]
  unfold maMeasure
  simp only [hD]

theorem exists_pos_le_all {e : ℕ} (f : Fin e → ℝ) (hf : ∀ i, 0 < f i) (a : ℝ) (ha : 0 < a) :
    ∃ b : ℝ, 0 < b ∧ b ≤ a ∧ ∀ i, b ≤ f i := by
  have hne : (insert a (Finset.univ.image f)).Nonempty := Finset.insert_nonempty _ _
  refine ⟨_, (Finset.lt_min'_iff _ hne).2 fun x hx => ?_,
    Finset.min'_le _ _ (Finset.mem_insert_self _ _),
    fun i => Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem f (Finset.mem_univ i)))⟩
  rcases Finset.mem_insert.1 hx with rfl | hx
  · exact ha
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hx
    exact hf i

theorem tail_uniform : TailBoundStatement → ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (A : FinHolAtlas e X) (Θ L : LocPot X) (s : X → X → ℂ) {n : ℕ} (m : Fin n → ℕ) (W : Fin n → Set X), IsPotential A Θ → IsPosPot A Θ → IsPotential A L → IsSection A L s → IsSNC A L s m W → (∀ y, logNormSec L s y ≤ 0) → ∀ (th : Fin e → LocPot X) (ph : Fin e → X → ℝ) (phT : Fin e → ℝ → X → ℝ) (C₅ C t₀ : ℝ), (∀ i, IsSingWeight A L s (th i) (ph i) C₅) → (∀ i, IsRegFamily A Θ L s (th i) (ph i) (phT i) C t₀) → ∃ K t₁ : ℝ, 0 < t₁ ∧ (0 < t₀ → t₁ ≤ t₀) ∧ ∀ τ : Fin e → ℝ, (∀ i, 0 < τ i ∧ τ i ≤ t₁) → (∀ i, IsPotential A (th i + LocPot.ofFun (phT i (τ i)) + Θ) ∧ IsPsh A (th i + LocPot.ofFun (phT i (τ i)) + Θ)) ∧ ∀ R : ℝ, Real.exp 1 ≤ R → maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) (bdry s ∪ {y | R ≤ rW L s y}) ≤ ENNReal.ofReal (K * Real.log R / R) ∧ ∫⁻ y in (bdry s)ᶜ ∩ {y | R ≤ rW L s y}, ENNReal.ofReal (Real.log (rW L s y)) ∂maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) ≤ ENNReal.ofReal (K * Real.log R ^ 2 / R) := by
  intro hTB e X _ _ _ _ _ A Θ L s n m W hΘ hpos hL hS hSNC hnorm th ph phT C₅ C t₀ hW hR
  choose t₂ ht₂ ht₂₀ hfix using fun i =>
    fixedMember_base A Θ L s (th i) (ph i) (phT i) C₅ C t₀ hΘ hpos hnorm (hW i) (hR i)
  obtain ⟨a, ha, hε⟩ := epsT_small C
  obtain ⟨t₁, ht₁, ht₁a, ht₁0, ht₁2⟩ : ∃ t₁ : ℝ, 0 < t₁ ∧ t₁ ≤ a ∧ (0 < t₀ → t₁ ≤ t₀) ∧
      ∀ i, t₁ ≤ t₂ i := by
    obtain ⟨b, hb, hba, hbf⟩ := exists_pos_le_all t₂ ht₂ a ha
    by_cases h0 : 0 < t₀
    · exact ⟨min b t₀, lt_min hb h0, (min_le_left _ _).trans hba, fun _ => min_le_right _ _,
        fun i => (min_le_left _ _).trans (hbf i)⟩
    · exact ⟨b, hb, hba, fun h => absurd h h0, hbf⟩
  have hB := fun i => hfix i t₁ ht₁ (ht₁2 i)
  obtain ⟨Ct, hCt⟩ := hTB A (fun i => th i + LocPot.ofFun (phT i t₁) + Θ) L s m W
    (fun i => (hB i).1) (fun i => (hB i).2.2.1) hL hS hSNC hnorm
  have hC₁ : 0 ≤ |C₅| + |C| + 1 := by positivity
  refine ⟨Ct * (|C₅| + |C| + 1 + 3), t₁, ht₁, ht₁0, fun τ hτ => ⟨fun i => ?_, fun R hRe => ?_⟩⟩
  · have hτ0 : τ i ≤ t₀ := ((hτ i).2.trans (ht₁2 i)).trans (ht₂₀ i)
    obtain ⟨hsm, -, -, -, hpsh, -, -, -⟩ := (hR i).2.2 (τ i) (hτ i).1 hτ0
    have hth := (hW i).1
    have hεi := (abs_le.1 (hε (τ i) (hτ i).1 ((hτ i).2.trans ht₁a)).1).2
    refine ⟨isPotentialAdd A _ _ (isPotentialAdd A _ _ hth (isPotential_ofFun A _ hsm)) hΘ,
      isPsh_of_le A Θ (th i) (phT i (τ i)) hΘ hpos hth hsm (epsT C (τ i)) 1 0 (by linarith) hpsh _
        (fun x z hz => ⟨hz.1.1, hz.2⟩) (fun x z => ?_)⟩
    show (th i).φ x z + phT i (τ i) z + Θ.φ x z = _
    ring
  · have hL' := fun i => (hB i).2.2.2 (τ i) (hτ i).1 (hτ i).2
    have hm : maMeasure A (fun i => th i + LocPot.ofFun (phT i (τ i)) + Θ) =
        maMeasure A (fun i => (th i + LocPot.ofFun (phT i t₁) + Θ) +
          LocPot.ofFun (fun y => phT i (τ i) y - phT i t₁ y - C * epsT C t₁)) :=
      maMeasure_eq_of_const A _ _ (fun _ => C * epsT C t₁) fun i x y => by
        show (th i).φ x y + phT i (τ i) y + Θ.φ x y =
          (th i).φ x y + phT i t₁ y + Θ.φ x y +
            (phT i (τ i) y - phT i t₁ y - C * epsT C t₁) + C * epsT C t₁
        ring
    rw [hm]
    exact hCt (|C₅| + |C| + 1) (fun i y => phT i (τ i) y - phT i t₁ y - C * epsT C t₁) hC₁
      (fun i => (hL' i).1) (fun i => (hL' i).2.1)
      (fun i y hy => ⟨(hL' i).2.2.2 y hy, (hL' i).2.2.1 y⟩) R hRe

end GlobalTheory.CompanionTheory.Ar.Giv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.MemChartWOfContinuousPeriod
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] {L : Flat.LogPeriods n a g Λ}
  {bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ} {A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
  {B : Fin a → Matrix (Fin g) (Fin g) ℤ} {c ρ : ℝ}

theorem exists_ball_det (h : IsChart L bas A T0 B c ρ) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ', (A z).det ≠ 0 := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  obtain ⟨ρ₂, K, hρ₂, -, hinv⟩ := GlobalTheory.CompanionTheory.Ar.RiemannLimit.inv n g A
    (h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)) h.A_det
  exact ⟨min ρ₂ ρ, lt_min hρ₂ h.ρ_pos, min_le_right _ _,
    fun z hz => (hinv z (Metric.ball_subset_ball (min_le_left _ _) hz)).1⟩

theorem A_tendsto (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) : Tendsto (fun m => A (zs m)) atTop (𝓝 (A 0)) := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  exact ((h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)).tendsto).comp hz

theorem T_tendsto (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) : Tendsto (fun m => T0 (zs m)) atTop (𝓝 (T0 0)) := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  exact ((h.T_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)).tendsto).comp hz

theorem inv_period (h : IsChart L bas A T0 B c ρ) {ρ' : ℝ}
    (hdet : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ', (A z).det ≠ 0) (w : Fin n → ℂ)
    (hw : w ∈ logCover L.a_le) (hz : expCover a w ∈ Metric.ball (0 : Fin n → ℂ) ρ') (x : Λ) :
    ((A (expCover a w))ᵀ)⁻¹ *ᵥ L.P w x =
      cst (uCo bas x) + tauAt L.a_le T0 B w *ᵥ cst (vCo bas x) := by
  rw [h.per w hw x, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (Ne.isUnit (by rw [det_transpose]; exact hdet _ hz)),
    Matrix.one_mulVec]

theorem tendsto_inv_mulVec (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) {q : ℕ → Fin g → ℂ} {p : Fin g → ℂ}
    (hq : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun m => ((A (zs m))ᵀ)⁻¹ *ᵥ q m) atTop (𝓝 (((A 0)ᵀ)⁻¹ *ᵥ p)) := by
  have hinv := tendsto_inv_transpose (A_tendsto h hz) h.A_det
  have hy := (((continuous_fst.matrix_mulVec continuous_snd :
    Continuous fun q : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => q.1 *ᵥ q.2)).tendsto
      (((A 0)ᵀ)⁻¹, p)).comp (hinv.prodMk_nhds hq)
  exact hy.congr fun m => rfl

theorem ker_each (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℝ)
    (hv : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) (j : Fin a) :
    (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 := by
  have hR : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have h0 : v ⬝ᵥ ((∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v) = 0 := by rw [hv]; simp
  rw [hR, Matrix.sum_mulVec, dotProduct_sum] at h0
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ v ⬝ᵥ ((B i).map (fun x : ℤ => (x : ℝ)) *ᵥ v) := fun i _ => by
    simpa using (hB i).dotProduct_mulVec_nonneg v
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
  exact ((hB j).dotProduct_mulVec_zero_iff v).1 (by simpa using h1)

theorem lower_at_centre (h : IsChart L bas A T0 B c ρ) (v : Fin g → ℝ)
    (hv : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) :
    c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((T0 0).map Complex.im) *ᵥ v) := by
  have := GlobalTheory.CompanionTheory.ChartBlockLower.im_lower_on_kernel n a g L.a_le (Metric.ball 0 ρ) T0 B c
    Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball h.ρ_le)) h.B_psd h.c_pos h.im_lower
    0 (Metric.mem_ball_self h.ρ_pos) (fun _ => 0) (fun j hj => (hj rfl).elim) (fun _ _ => rfl) v
    (fun j _ => ker_each h.B_psd v hv j)
  simpa using this

theorem exp_cast (ha : a ≤ n) (w : Fin n → ℂ) (j : Fin a) :
    Complex.exp (w (Fin.castLE ha j)) = expCover a w (Fin.castLE ha j) := by
  have hj : (Fin.castLE ha j).val < a := j.2
  simp only [expCover, if_pos hj]

theorem extend_mem (h : IsChart L bas A T0 B c ρ) (x : Λ) (t : (Fin n → ℂ) → Fin g → ℂ)
    (ht : ContinuousAt t 0) (hP : ∀ w ∈ logCover L.a_le, L.P w x = t (expCover a w)) :
    x ∈ chartW bas B := by
  classical
  obtain ⟨ρ', hρ', hρle, hdet⟩ := exists_ball_det h
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  set r : ℕ → ℝ := fun m => ρ'⁻¹ + m with hr
  set tm : ℕ → ℂ := fun m => ((r m / (2 * Real.pi) : ℝ) : ℂ) * Complex.I with htm
  set ws : ℕ → Fin n → ℂ := fun m k => if k.val < a then -(r m : ℂ) else 0 with hws
  have hrpos : ∀ m, 0 < r m := fun m => by
    have : 0 < ρ'⁻¹ := inv_pos.2 hρ'
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp only [hr]; linarith
  have hexpr : ∀ m, Real.exp (-(r m)) < ρ' := by
    intro m
    have h1 : r m + 1 ≤ Real.exp (r m) := Real.add_one_le_exp _
    have h3 : ρ'⁻¹ ≤ r m := by
      have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [hr]; linarith
    rw [Real.exp_neg]
    have h4 : ρ'⁻¹ < Real.exp (r m) := by linarith
    exact inv_lt_of_inv_lt₀ hρ' h4
  have hws_cast : ∀ m (j : Fin a), ws m (Fin.castLE L.a_le j) = -(r m : ℂ) := by
    intro m j
    have hj : (Fin.castLE L.a_le j).val < a := j.2
    simp only [hws, if_pos hj]
  have hws_mem : ∀ m, ws m ∈ logCover L.a_le := by
    intro m
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · rw [hws_cast]
      simp [hrpos m]
    · have hk' : ¬ k.val < a := not_lt.2 hk
      simp only [hws, if_neg hk']
      simp
  set zs : ℕ → Fin n → ℂ := fun m => expCover a (ws m) with hzs
  have hzs_k : ∀ m k, zs m k = if k.val < a then ((Real.exp (-(r m)) : ℝ) : ℂ) else 0 := by
    intro m k
    simp only [hzs, expCover, hws]
    by_cases hk : k.val < a
    · simp [hk]
    · simp [hk]
  have hzs_ball : ∀ m, zs m ∈ Metric.ball (0 : Fin n → ℂ) ρ' := by
    intro m
    rw [mem_ball_zero_iff, pi_norm_lt_iff hρ']
    intro k
    rw [hzs_k]
    split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]; exact hexpr m
    · simpa using hρ'
  have hrtop : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hzs_lim : Tendsto zs atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro k
    simp only [hzs_k]
    by_cases hk : k.val < a
    · simp only [hk, if_true]
      have h1 : Tendsto (fun m => Real.exp (-(r m))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hrtop)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa only [Function.comp_def, Complex.ofReal_zero, Pi.zero_apply] using h2
    · simp only [hk, if_false]
      exact tendsto_const_nhds
  have hdiv : ∀ m, (-(r m : ℂ)) / (2 * Real.pi * Complex.I) = tm m := by
    intro m
    rw [div_eq_iff h2pi]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [htm]
    push_cast
    field_simp
    simp
  have hC : (∑ j, B j).map (fun x : ℤ => (x : ℂ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℂ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have hdec : ∀ m, tauAt L.a_le T0 B (ws m) =
      T0 (zs m) + tm m • (∑ j, B j).map (fun x : ℤ => (x : ℂ)) := by
    intro m
    have hsum : ∑ j, (ws m (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ)) = tm m • (∑ j, B j).map (fun x : ℤ => (x : ℂ)) := by
      rw [hC, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hws_cast, hdiv]
    simp only [tauAt]
    rw [hsum]
  have him : Tendsto (fun m => (tm m).im) atTop atTop := by
    have h1 : ∀ m, (tm m).im = r m / (2 * Real.pi) := fun m => by
      simp only [htm, Complex.mul_I_im, Complex.ofReal_re]
    simp only [h1]
    exact hrtop.atTop_div_const (by positivity)
  have hYm : ∀ m, ((tauAt L.a_le T0 B (ws m)).map Complex.im -
      c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef := fun m =>
    h.im_lower _ (Metric.ball_subset_ball hρle (hzs_ball m))
      (fun j => ws m (Fin.castLE L.a_le j)) (fun j => exp_cast L.a_le (ws m) j)
  have hq := tendsto_inv_mulVec h hzs_lim (ht.tendsto.comp hzs_lim)
  have hy' : Tendsto (fun m => (fun k => ((uCo bas x k : ℤ) : ℂ)) +
      tauAt L.a_le T0 B (ws m) *ᵥ (fun k => ((vCo bas x k : ℤ) : ℂ))) atTop
      (𝓝 (((A 0)ᵀ)⁻¹ *ᵥ t 0)) := hq.congr fun m => by
    have := inv_period h hdet (ws m) (hws_mem m) (hzs_ball m) x
    rw [hP _ (hws_mem m)] at this
    exact this
  obtain ⟨u, v, hv, -, hev⟩ := GlobalTheory.T.siegel_limit_imag_bound g (∑ j, B j) (T0 0) (fun m => T0 (zs m))
    (fun m => tauAt L.a_le T0 B (ws m)) tm c (fun _ => uCo bas x) (fun _ => vCo bas x) _ h.c_pos
    (T_tendsto h hzs_lim) him hdec hYm (lower_at_centre h) hy'
  obtain ⟨m, hm⟩ := hev.exists
  have hvx : vCo bas x = v := hm.2
  rw [chartW, LinearMap.mem_ker, LinearMap.comp_apply, hvx, Matrix.mulVecLin_apply]
  exact hv

theorem limit_mem (h : IsChart L bas A T0 B c ρ) (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ)
    (hws : ∀ k, ws k ∈ logCover L.a_le)
    (hz : Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0))
    (hp : Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p)) :
    ∃ x₀ : chartW bas B, p = chartPer bas A T0 B x₀ := by
  obtain ⟨ρ', hρ', hρle, hdet⟩ := exists_ball_det h
  have hU : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ' := Metric.mem_ball_self hρ'
  have hq := tendsto_inv_mulVec h hz hp
  have key := GlobalTheory.CompanionTheory.PeriodLimit.limit_period n a g L.a_le (Metric.ball 0 ρ') T0 B c
    Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball (hρle.trans h.ρ_le))) h.B_psd h.c_pos
    (fun z hz => h.im_lower z (Metric.ball_subset_ball hρle hz)) 0 hU (fun _ => 0)
    (fun j hj => (hj rfl).elim) (fun _ _ => rfl) (((A 0)ᵀ)⁻¹ *ᵥ p)
  obtain ⟨u, v, hv, hw⟩ := key (mem_closure_of_tendsto (hz.prodMk_nhds hq) (by
    filter_upwards [hz.eventually (Metric.isOpen_ball.mem_nhds hU)] with k hk
    exact ⟨hk, fun j => ws k (Fin.castLE L.a_le j), uCo bas (x k), vCo bas (x k),
      fun j => exp_cast L.a_le (ws k) j, inv_period h hdet _ (hws k) hk (x k)⟩))
  simp only [zero_div, zero_smul, Finset.sum_const_zero, add_zero] at hw
  have hw' : ((A 0)ᵀ)⁻¹ *ᵥ p = cst u + T0 0 *ᵥ cst v := hw
  refine ⟨⟨mk bas u v, ?_⟩, ?_⟩
  · rw [chartW, LinearMap.mem_ker, LinearMap.comp_apply, vCo_mk, Matrix.mulVecLin_apply,
      Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun j _ => hv j rfl
  · show p = (A 0)ᵀ *ᵥ (cst (uCo bas (mk bas u v)) + T0 0 *ᵥ cst (vCo bas (mk bas u v)))
    rw [uCo_mk, vCo_mk, ← hw', Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Ne.isUnit (by rw [det_transpose]; exact h.A_det)),
      Matrix.one_mulVec]

theorem periods_at_centre : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (t : (Fin n → ℂ) → Fin g → ℂ), ContinuousAt t 0 → (∀ w ∈ logCover L.a_le, L.P w x = t (expCover a w)) → x ∈ chartW bas B) ∧ ∀ (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ), (∀ k, ws k ∈ logCover L.a_le) → Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) → Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p) → ∃ x₀ : chartW bas B, p = chartPer bas A T0 B x₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h =>
    ⟨fun x t ht hP => extend_mem h x t ht hP, fun ws x p hws hz hp => limit_mem h ws x p hws hz hp⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods
end

