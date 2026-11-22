import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0076
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0069
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0064
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0058
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0061
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.VolumeInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.RegularFunctionInBlockField
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField

private theorem aeval_mul_scale_of_homog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {S : Type} [CommRing S] [Algebra ℤ S] (f : MvPolynomial (Σ k, ι k) ℤ) (d : K → ℕ)
    (hf : ∀ m ∈ f.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) (t : K → S) (w : (Σ k, ι k) → S) :
    MvPolynomial.aeval (fun q : Σ k, ι k => t q.1 * w q) f = (∏ k, t k ^ d k) * MvPolynomial.aeval w f := by
  conv_lhs => rw [MvPolynomial.as_sum f]
  conv_rhs => rw [MvPolynomial.as_sum f]
  rw [map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
  have key : (m.prod fun q e => (t q.1 * w q) ^ e) = (∏ k, t k ^ d k) * m.prod fun q e => w q ^ e := by
    simp_rw [mul_pow]
    rw [Finsupp.prod_mul]
    congr 1
    rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _), Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ i, t k ^ m ⟨k, i⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf m hm k]
  rw [key]
  ring

private theorem mConeMap_eq_prod_X_pow_mul_C {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {Ω : Type} [Field Ω] (y : (Σ k, ι k) → Ω) (h : MvPolynomial (Σ k, ι k) ℤ) (d : K → ℕ)
    (hh : ∀ m ∈ h.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) :
    mConeMap y h = (∏ k, (MvPolynomial.X k : MvPolynomial K Ω) ^ d k) * MvPolynomial.C (MvPolynomial.aeval y h) := by
  have e : (fun p : Σ k, ι k => MvPolynomial.C (y p) * (MvPolynomial.X p.1 : MvPolynomial K Ω)) =
      fun p => (MvPolynomial.X p.1 : MvPolynomial K Ω) * MvPolynomial.C (y p) := by
    funext p
    ring
  show MvPolynomial.aeval _ h = _
  rw [e, aeval_mul_scale_of_homog h d hh (fun k => (MvPolynomial.X k : MvPolynomial K Ω))
    (fun p => MvPolynomial.C (y p))]
  congr 1
  exact MvPolynomial.aeval_algebraMap_apply (MvPolynomial K Ω) y h

theorem algebraMap_mem_blockFnField :
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] [CharZero Φ]
      (y : (Σ k, ι k) → Φ) (Ψ : Type) (N j : ℕ) (M : FlagModel y Ψ N j) (zb : (Σ k, baseIdx ι M.blk k) → ℂ) (s : M.Ω),
      zb ∈ mcPts (mCoordIdeal M.x) → RegAt M.x (mCoordIdeal zb) s → algebraMap M.Ω Φ s ∈ blockFnField y := by
  intro K _ ι _ Φ _ _ y Ψ N j M zb s hzb hreg
  obtain ⟨d, g, h, hg, hh, hQ, hgs⟩ := hreg
  obtain ⟨-, hzv⟩ := hzb
  have hxh : MvPolynomial.aeval M.x h ≠ 0 := by
    intro h0
    apply hQ
    have hker : h ∈ mCoordIdeal M.x := by
      rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_prod_X_pow_mul_C M.x h d hh, h0, map_zero, mul_zero]
    have hz := hzv h hker
    have hz' : MvPolynomial.aeval zb h = 0 := by
      rw [MvPolynomial.aeval_def, algebraMap_int_eq, ← MvPolynomial.eval_map]
      exact hz
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap_eq_prod_X_pow_mul_C zb h d hh, hz', map_zero, mul_zero]
  have hs : s = MvPolynomial.aeval M.x g / MvPolynomial.aeval M.x h := eq_div_of_mul_eq hxh hgs.symm
  rw [hs, map_div₀, ← MvPolynomial.aeval_algebraMap_apply, ← MvPolynomial.aeval_algebraMap_apply]
  have hne : ∀ k, ∃ i, (⇑(algebraMap M.Ω Φ) ∘ M.x) ⟨k, i⟩ ≠ 0 := fun k => by
    obtain ⟨i, hi⟩ := M.x_ne k
    exact ⟨i, (map_ne_zero _).mpr hi⟩
  choose c hc using hne
  have hYy : ∀ q, (⇑(algebraMap M.Ω Φ) ∘ M.x) q = y ⟨q.1.val, q.2⟩ := fun q => (M.y_base q).symm
  generalize (⇑(algebraMap M.Ω Φ) ∘ M.x) = Y at hYy hc ⊢
  have hsc : ∀ p : MvPolynomial (Σ k, baseIdx ι M.blk k) ℤ, (∀ m ∈ p.support, ∀ k, ∑ i, m ⟨k, i⟩ = d k) →
      MvPolynomial.aeval Y p =
        (∏ k, Y ⟨k, c k⟩ ^ d k) * MvPolynomial.aeval (fun q => Y q / Y ⟨q.1, c q.1⟩) p := by
    intro p hp
    have eY : Y = fun q : Σ k, baseIdx ι M.blk k => Y ⟨q.1, c q.1⟩ * (Y q / Y ⟨q.1, c q.1⟩) := by
      funext q
      rw [mul_comm, div_mul_cancel₀ _ (hc q.1)]
    conv_lhs => rw [eY]
    exact aeval_mul_scale_of_homog p d hp (fun k => Y ⟨k, c k⟩) (fun q => Y q / Y ⟨q.1, c q.1⟩)
  have hP : (∏ k, Y ⟨k, c k⟩ ^ d k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k)
  rw [hsc g hg, hsc h hh, mul_div_mul_left _ _ hP]
  have hw : ∀ q, Y q / Y ⟨q.1, c q.1⟩ ∈ blockFnField y := by
    intro q
    rw [hYy, hYy]
    apply IntermediateField.subset_adjoin
    exact ⟨⟨q.1.val, q.2⟩, ⟨q.1.val, c q.1⟩, rfl, rfl⟩
  have hmem : ∀ p : MvPolynomial (Σ k, baseIdx ι M.blk k) ℤ,
      MvPolynomial.aeval (fun q => Y q / Y ⟨q.1, c q.1⟩) p ∈ blockFnField y := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a =>
      rw [MvPolynomial.aeval_C, algebraMap_int_eq, eq_intCast]
      exact intCast_mem _ a
    | add p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    | mul_X p n hp =>
      rw [map_mul, MvPolynomial.aeval_X]
      exact mul_mem hp (hw n)
  exact div_mem (hmem g) (hmem h)

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegField
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedAtlasCompatibility
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem basePart_orbit {σ : Type} (blk : σ → Option K) {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    SameOrbit (basePart blk z) (basePart blk z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c k.1, fun k => hc k.1, rfl⟩

theorem blocks_of_orbit {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') (h' : ∀ k, ∃ i, z' ⟨k, i⟩ ≠ 0) :
    ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  intro k
  obtain ⟨i, hi⟩ := h' k
  exact ⟨i, mul_ne_zero (hc k) hi⟩

theorem fstPt_blocks {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0) :
    ∀ k, ∃ i, fstPt k₀ z ⟨k, i⟩ ≠ 0 := fun k => h (some k)

theorem sndPt_blocks {k₀ : K} {z : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : ∀ o, ∃ i, z ⟨o, i⟩ ≠ 0) :
    ∀ k, ∃ i, sndPt k₀ z ⟨k, i⟩ ≠ 0 := by
  intro k
  by_cases e : k = k₀
  · subst e
    obtain ⟨i, hi⟩ := h none
    refine ⟨i, ?_⟩
    change z (v₁ k ⟨k, i⟩) ≠ 0
    rw [v₁_self]
    exact hi
  · obtain ⟨i, hi⟩ := h (some k)
    refine ⟨i, ?_⟩
    change z (v₁ k₀ ⟨k, i⟩) ≠ 0
    rw [v₁_ne (p := ⟨k, i⟩) e]
    exact hi

theorem basePart_snd_eq_fst {σ : Type} (blk : σ → Option K) {k₀ : K} (p : σ) (hp : blk p = some k₀)
    (z : (Σ o : Option K, ι (o.getD k₀)) → ℂ) :
    basePart blk (sndPt k₀ z) = basePart blk (fstPt k₀ z) := by
  funext q
  obtain ⟨⟨k, hk⟩, i⟩ := q
  have e : k ≠ k₀ := by
    rintro rfl
    exact hk p hp
  change z (v₁ k₀ ⟨k, i⟩) = z (v₀ k₀ ⟨k, i⟩)
  rw [v₁_ne (p := ⟨k, i⟩) e]
  rfl

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → ∀ (x : RW.X) (z₀ z₁ : (Σ k, ι k) → ℂ), SameOrbit z₀ (fstPt k₀ (RW.lift x x)) → SameOrbit z₁ (sndPt k₀ (RW.lift x x)) → basePart M.blk z₀ ∈ mcPts (mCoordIdeal M.x) ∧ SameOrbit (basePart M.blk z₁) (basePart M.blk z₀) ∧ (∀ k, ∃ i, z₀ ⟨k, i⟩ ≠ 0) ∧ ∀ k, ∃ i, z₁ ⟨k, i⟩ ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr hb hW x z₀ z₁ h₀ h₁
  have hL : ∀ o, ∃ i, RW.lift x x ⟨o, i⟩ ≠ 0 := (RW.mem x x (RW.mem_U x)).1
  have hbase : SameOrbit (basePart M.blk z₀) (Rb.lift (pr x) (pr x)) :=
    orbit_trans (basePart_orbit M.blk h₀) (orbit_symm (hW.2.1 x))
  refine ⟨?_, ?_, blocks_of_orbit h₀ (fstPt_blocks hL), blocks_of_orbit h₁ (sndPt_blocks hL)⟩
  · obtain ⟨c, hc, e⟩ := hbase
    rw [e]
    exact ((GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.main _ _ _ M.x _ c hc).2 (Rb.mem (pr x) (pr x) (Rb.mem_U _))).1
  · have h₁' := basePart_orbit M.blk h₁
    rw [basePart_snd_eq_fst M.blk (τ, a) hb] at h₁'
    exact orbit_trans h₁' (orbit_symm (basePart_orbit M.blk h₀))

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.PtBase
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartCoordinatesRegular
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.diagSec_isSNC_diagSet : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsSNC RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) (diagSec ψ i₀ u) ![1] ![diagSet k₀ RW] := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c x
  obtain ⟨⟨F, H, hW⟩, hVo, hxV, hVs, -, hu, hu0, hd, -⟩ := hL x
  have hsrc : ((ψ x).restrOpen (V x) hVo).source = V x := by
    rw [OpenPartialHomeomorph.restrOpen_source]
    exact Set.inter_eq_right.mpr hVs
  refine ⟨(ψ x).restrOpen (V x) hVo, pa_compat_restr RW.A (ψ x) hW.1 (V x) hVo, by rw [hsrc]; exact hxV, ?_,
    fun _ => some (i₀ x), ?_, ?_, u x, ?_, ?_, ?_⟩
  · rw [hsrc]; exact subset_rfl
  · intro k k' _ _ _
    exact Subsingleton.elim k k'
  · intro k
    obtain rfl : k = 0 := Subsingleton.elim k 0
    rw [hsrc]
    ext w
    constructor
    · rintro ⟨hw, hwV⟩
      exact ⟨hwV, i₀ x, rfl, (hd w hwV).2 hw⟩
    · rintro ⟨hwV, i, hi, hw⟩
      obtain rfl : i₀ x = i := Option.some.inj hi
      exact ⟨(hd w hwV).1 hw, hwV⟩
  · rw [hsrc]; exact hu
  · rw [hsrc]; exact hu0
  · rw [hsrc]
    intro w _
    simp [diagSec]
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartHolomorphic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

private theorem isPotential_secPot_of_isSmoothHerm {κ : Type} [Fintype κ] {ρ : κ → Type} [∀ k, Fintype (ρ k)]
    {P J : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ρ)} {e : ℕ} (R : ReciprocityTheory.ChartRestriction.G.Geo.AnLogRes P J e)
    (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ρ) (hA : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm A)
    (V : R.X → Set R.X) (hV : ∀ x, IsOpen (V x)) (hm : ∀ x, x ∈ V x) (hVU : ∀ x, V x ⊆ R.U x)
    (c : ℝ) : ReciprocityTheory.AnForm.M.IsPotential R.A (secPot R A V hV hm c) := by
  have hA' : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) A.h {z | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hA
  have hol : ∀ (x : R.X) (p : (k : κ) × ρ k) (j : Fin R.A.n) (t : Fin e → ℂ),
      t ∈ (R.A.chart j).target → (R.A.chart j).symm t ∈ R.U x →
      AnalyticAt ℂ (fun s => R.lift x ((R.A.chart j).symm s) p) t :=
    fun x p j t ht hu => R.holo x p j t ⟨ht, hu⟩
  have memNZ : ∀ (z0 y0 : R.X), y0 ∈ R.U z0 → ∀ k, ∃ i, R.lift z0 y0 ⟨k, i⟩ ≠ 0 := by
    intro z0 y0 h
    have h' := R.mem z0 y0 h
    simp only [ReciprocityTheory.ChartRestriction.G.Geo.mcPts, Set.mem_ofPred_eq] at h'
    exact h'.1
  unfold ReciprocityTheory.AnForm.M.IsPotential ReciprocityTheory.AnForm.M.FinHolAtlas.SmoothOn
    ReciprocityTheory.AnForm.M.FinHolAtlas.HoloOn
  dsimp only [secPot]
  refine ⟨fun x j => ?_, fun x x' y hy => ?_⟩
  · have hlift : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => R.lift x ((R.A.chart j).symm t))
        ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x) := by
      rw [contDiffOn_pi]
      intro p
      have h1 : ContDiffOn ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun t => R.lift x ((R.A.chart j).symm t) p)
          ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x) :=
        fun t ht => (hol x p j t ht.1 (hVU x ht.2)).contDiffAt.contDiffWithinAt
      exact h1.restrict_scalars ℝ
    have hmem : ∀ t ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x,
        (∀ k, ∃ i, R.lift x ((R.A.chart j).symm t) ⟨k, i⟩ ≠ 0) :=
      fun t ht => memNZ x _ (hVU x ht.2)
    have hh := hA'.comp hlift (fun t ht => hmem t ht)
    have hne : ∀ t ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' V x,
        A.h (R.lift x ((R.A.chart j).symm t)) ≠ 0 :=
      fun t ht => (A.pos _ (hmem t ht)).ne'
    exact (hh.log hne).add contDiffOn_const
  · obtain ⟨hyx, hyx'⟩ := hy
    have hyU : y ∈ R.U x := hVU x hyx
    have hyU' : y ∈ R.U x' := hVU x' hyx'
    choose i hi using memNZ x' y hyU'
    obtain ⟨r, hr⟩ : ∃ r : κ → R.X → ℂ,
        ∀ k z, r k z = R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩ :=
      ⟨fun k z => R.lift x z ⟨k, i k⟩ / R.lift x' z ⟨k, i k⟩, fun _ _ => rfl⟩
    have hry : ∀ k, r k y ≠ 0 := by
      intro k
      obtain ⟨cy, hcy, hly⟩ := R.compat x x' y ⟨hyU, hyU'⟩
      have h1 := congrFun hly ⟨k, i k⟩
      rw [hr, h1]
      exact div_ne_zero (mul_ne_zero (hcy k) (hi k)) (hi k)
    obtain ⟨j, hj⟩ := R.A.cover y
    have hD : IsOpen ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U x')) :=
      (R.A.chart j).isOpen_inter_preimage_symm ((R.isOpen_U x).inter (R.isOpen_U x'))
    obtain ⟨O, hOdef⟩ : ∃ O : Set (Fin e → ℂ), O = {t | t ∈ (R.A.chart j).target ∧
        (R.A.chart j).symm t ∈ R.U x ∩ R.U x' ∧
        (∀ k, R.lift x' ((R.A.chart j).symm t) ⟨k, i k⟩ ≠ 0) ∧
        ∀ k, r k ((R.A.chart j).symm t) / r k y ∈ Complex.slitPlane} := ⟨_, rfl⟩
    have memO : ∀ t, t ∈ O ↔ (t ∈ (R.A.chart j).target ∧
        (R.A.chart j).symm t ∈ R.U x ∩ R.U x' ∧
        (∀ k, R.lift x' ((R.A.chart j).symm t) ⟨k, i k⟩ ≠ 0) ∧
        ∀ k, r k ((R.A.chart j).symm t) / r k y ∈ Complex.slitPlane) := by
      intro t; rw [hOdef]; rfl
    have hO : IsOpen O := by
      rw [isOpen_iff_mem_nhds]
      intro t ht
      obtain ⟨htT, htU, htne, htsl⟩ := (memO t).1 ht
      have hDn : (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' (R.U x ∩ R.U x') ∈ 𝓝 t :=
        hD.mem_nhds ⟨htT, htU⟩
      have hca : ∀ (z0 : R.X) (p : (k : κ) × ρ k), (R.A.chart j).symm t ∈ R.U z0 →
          ContinuousAt (fun s => R.lift z0 ((R.A.chart j).symm s) p) t :=
        fun z0 p hz => (hol z0 p j t htT hz).continuousAt
      have e1 : ∀ᶠ s in 𝓝 t, ∀ k, R.lift x' ((R.A.chart j).symm s) ⟨k, i k⟩ ≠ 0 := by
        rw [Filter.eventually_all]
        intro k
        exact (hca x' _ htU.2).eventually_ne (htne k)
      have e2 : ∀ᶠ s in 𝓝 t, ∀ k, r k ((R.A.chart j).symm s) / r k y ∈ Complex.slitPlane := by
        rw [Filter.eventually_all]
        intro k
        have hc0 : ContinuousAt (fun s => r k ((R.A.chart j).symm s)) t := by
          simp only [hr]
          exact (hca x _ htU.1).div (hca x' _ htU.2) (htne k)
        have hc : ContinuousAt (fun s => r k ((R.A.chart j).symm s) / r k y) t :=
          hc0.div_const _
        exact hc.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds (htsl k))
      filter_upwards [hDn, e1, e2] with s hs1 hs2 hs3
      exact (memO s).2 ⟨hs1.1, hs1.2, hs2, hs3⟩
    have hWopen : IsOpen ((R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O) :=
      (R.A.chart j).isOpen_inter_preimage hO
    have hsy : (R.A.chart j).symm ((R.A.chart j) y) = y := (R.A.chart j).left_inv hj
    have hyW : y ∈ (R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O := by
      refine ⟨hj, (memO _).2 ?_⟩
      rw [hsy]
      refine ⟨(R.A.chart j).map_source hj, ⟨hyU, hyU'⟩, hi, fun k => ?_⟩
      rw [div_self (hry k)]
      exact Complex.one_mem_slitPlane
    have condW : ∀ z ∈ (R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O, z ∈ R.U x ∧ z ∈ R.U x' ∧
        (∀ k, R.lift x' z ⟨k, i k⟩ ≠ 0) ∧ ∀ k, r k z / r k y ∈ Complex.slitPlane := by
      intro z hz
      have h2 := (memO ((R.A.chart j) z)).1 hz.2
      rw [(R.A.chart j).left_inv hz.1] at h2
      exact ⟨h2.2.1.1, h2.2.1.2, h2.2.2.1, h2.2.2.2⟩
    refine ⟨(R.A.chart j).source ∩ (R.A.chart j) ⁻¹' O, hWopen, hyW,
      fun z => (∑ k, ((A.a k : ℝ) : ℂ) * Complex.log (r k z / r k y)) +
        ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ), ?_, ?_⟩
    · intro j' t ht
      obtain ⟨hUx, hUx', hne, hsl⟩ := condW _ ht.2
      have hra : ∀ k, AnalyticAt ℂ (fun s => r k ((R.A.chart j').symm s)) t := by
        intro k
        simp only [hr]
        exact (hol x _ j' t ht.1 hUx).div (hol x' _ j' t ht.1 hUx') (hne k)
      show AnalyticAt ℂ (fun s => (∑ k, ((A.a k : ℝ) : ℂ) *
          Complex.log (r k ((R.A.chart j').symm s) / r k y)) +
        ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ)) t
      refine AnalyticAt.add ?_ analyticAt_const
      have hs : ∀ k ∈ (Finset.univ : Finset κ), AnalyticAt ℂ (fun s => ((A.a k : ℝ) : ℂ) *
          Complex.log (r k ((R.A.chart j').symm s) / r k y)) t :=
        fun k _ => analyticAt_const.mul (((hra k).div analyticAt_const (hry k)).clog (hsl k))
      have h3 := Finset.analyticAt_sum Finset.univ hs
      rw [Finset.sum_fn] at h3
      exact h3
    · intro z hz
      obtain ⟨hUx, hUx', hne, -⟩ := condW z hz.1.1
      obtain ⟨cz, hcz, hlz⟩ := R.compat x x' z ⟨hUx, hUx'⟩
      have hrz : ∀ k, r k z = cz k := by
        intro k
        rw [hr]
        have h1 := congrFun hlz ⟨k, i k⟩
        rw [h1]
        exact mul_div_cancel_right₀ _ (hne k)
      have hhz : A.h (R.lift x z) = (∏ k, ‖cz k‖ ^ A.a k) * A.h (R.lift x' z) := by
        rw [hlz]; exact A.smul cz _ hcz
      have hhpos : 0 < A.h (R.lift x' z) := A.pos _ (memNZ x' z hUx')
      have hczn : ∀ k, ‖cz k‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hcz k)
      have hryn : ∀ k, ‖r k y‖ ≠ 0 := fun k => norm_ne_zero_iff.2 (hry k)
      have lhs : (Real.log (A.h (R.lift x z)) + c) - (Real.log (A.h (R.lift x' z)) + c) =
          ∑ k, (A.a k : ℝ) * Real.log ‖cz k‖ := by
        rw [hhz, Real.log_mul (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hczn k))
          hhpos.ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hczn k))]
        simp only [Real.log_zpow]
        ring
      show (Real.log (A.h (R.lift x z)) + c) - (Real.log (A.h (R.lift x' z)) + c) =
        ((∑ k, ((A.a k : ℝ) : ℂ) * Complex.log (r k z / r k y)) +
          ((∑ k, (A.a k : ℝ) * Real.log ‖r k y‖ : ℝ) : ℂ)).re
      rw [lhs]
      simp only [Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul, Complex.ofReal_re,
        Complex.log_re, norm_div, hrz]
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Real.log_div (hczn k) (hryn k)]
      ring

theorem isPotential_secPot : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (ψ : RW.X → OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb : RW.X → Fin Rb.A.n) (σ : RW.X → Fin n ↪ Fin e) (i₀ : RW.X → Fin e) (V : RW.X → Set RW.X) (u : RW.X → RW.X → ℂ) (hL : ∀ x, IsLocSec M Rb τ a k₀ ca cb RW pr x (ψ x) (kb x) (σ x) (i₀ x) (V x) (u x)), ∀ c : ℝ, IsPotential RW.A (secPot RW (potA M τ a k₀) V (fun x => (hL x).2.1) (fun x => (hL x).2.2.1) c) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr ψ kb σ i₀ V u hL c
  have hS : ReciprocityTheory.ChartRestriction.G.Geo.IsSmoothHerm (potA M τ a k₀) := by
    unfold GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec.potA
    exact GlobalTheory.CompanionTheory.Ar.PB.StepW.fsHerm_isSmoothHerm _ _ _
  exact isPotential_secPot_of_isSmoothHerm RW (potA M τ a k₀) hS V _ _ (fun x => (hL x).2.2.2.2.1) c

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwistedChartTransitionAnalytic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec

theorem locSec_norm_eq : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n e : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ e) (pr : RW.X → Rb.X) (x x' : RW.X) (ψ ψ' : OpenPartialHomeomorph RW.X (Fin e → ℂ)) (kb kb' : Fin Rb.A.n) (σ σ' : Fin n ↪ Fin e) (i₀ i₀' : Fin e) (V V' : Set RW.X) (u u' : RW.X → ℂ), M.blk (τ, a) = some k₀ → IsWAtlas M Rb τ a k₀ ca cb RW pr → IsLocSec M Rb τ a k₀ ca cb RW pr x ψ kb σ i₀ V u → IsLocSec M Rb τ a k₀ ca cb RW pr x' ψ' kb' σ' i₀' V' u' → ∀ w ∈ V ∩ V', ‖u w * ψ w i₀‖ / (potA M τ a k₀).h (RW.lift x w) = ‖u' w * ψ' w i₀'‖ / (potA M τ a k₀).h (RW.lift x' w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n e Rb τ a k₀ ca cb RW pr x x' ψ ψ' kb kb' σ σ' i₀ i₀' V V' u u' _ _ hs hs' w hw
  obtain ⟨⟨F, H, hc⟩, -, -, hVs, hVU, -, hu, hd, hn⟩ := hs
  obtain ⟨-, -, -, -, hVU', -, hu', hd', hn'⟩ := hs'
  by_cases h0 : ψ w i₀ = 0
  · have h0' : ψ' w i₀' = 0 := (hd' w hw.2).2 ((hd w hw.1).1 h0)
    simp [h0, h0']
  have h0' : ψ' w i₀' ≠ 0 := fun h => h0 ((hd w hw.1).2 ((hd' w hw.2).1 h))
  obtain ⟨-, hF, -, -, -, hp⟩ := hc
  obtain ⟨hH, hG, z₀, z₁, hz₀, hz₁, hex⟩ := hp w (hVs hw.1)
  have hG' : M.GoodAt F (mCoordIdeal (basePart M.blk z₀)) := by
    obtain ⟨c, hc0, hzc⟩ := hz₀
    have e₀ : basePart M.blk z₀ = fun q : Σ k, baseIdx ι M.blk k =>
        (fun k : NonPluckerBlocks M.blk => c k.1) q.1 * basePart M.blk (fstPt k₀ (RW.lift w w)) q := by
      rw [hzc]; rfl
    rw [e₀, GlobalTheory.CompanionTheory.Ar.PB.StepW.TorusAct.mCoordIdeal_torus (K := NonPluckerBlocks M.blk) (ι := baseIdx ι M.blk)
      (fun k : NonPluckerBlocks M.blk => c k.1) (fun k => hc0 k.1) (basePart M.blk (fstPt k₀ (RW.lift w w)))]
    exact hG
  have hD : IsPtData M τ a k₀ ca cb RW w z₀ z₁ F (H τ (ψ w)) (ψ w i₀) :=
    ⟨hF, hG', hz₀, hz₁, (hH τ).1, (hH τ).2, h0, fun i => (hex τ i).1, fun i => by
      simpa using (hex τ i).2⟩
  have e₁ := hn w hw.1 h0 z₀ z₁ F _ _ hD
  have e₂ := hn' w hw.2 h0' z₀ z₁ F _ _ hD
  have hA : 0 < (potA M τ a k₀).h (RW.lift x w) := (potA M τ a k₀).pos _ (RW.mem x w (hVU hw.1)).1
  have hA' : 0 < (potA M τ a k₀).h (RW.lift x' w) := (potA M τ a k₀).pos _ (RW.mem x' w (hVU' hw.2)).1
  have hN : 0 < ‖u w * ψ w i₀‖ := norm_pos_iff.2 (mul_ne_zero (hu w hw.1) h0)
  have hN' : 0 < ‖u' w * ψ' w i₀'‖ := norm_pos_iff.2 (mul_ne_zero (hu' w hw.2) h0')
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (div_pos hN hA)) (Set.mem_Ioi.2 (div_pos hN' hA')) ?_
  rw [Real.log_div hN.ne' hA.ne', Real.log_div hN'.ne' hA'.ne', e₁, e₂]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Sec
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TwoPointFibreChartFifthStatement
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_point_fibre_chart_fifth : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (X : Type) (q : Fin 2 → X → FA.S.X) (Un : Set (Fin d → ℂ)) (Gn : (Fin d → ℂ) → Matrix (Fin 2) (Fin 2) ℂ) (ΦYn : (Fin (d + 1) → ℂ) → FA.S.X) (ΦWn : (Fin (d + 2) → ℂ) → X) (l : Fin BM.q) (H : Ψ → (Fin d → ℂ) → Matrix (Fin N) (Fin N) ℂ) (bp : (Fin d → ℂ) → BM.Rb.X), IsOpen Un → IsFibreData FA τ a ca cb q Un Gn ΦYn ΦWn l H bp → ∀ (p : Ψ × Fin N) (z : Fin (d + 1) → ℂ), Fin.tail z ∈ Un → ∃ Hh : (Fin (d + 1) → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, ((FA.S.comap some).potH p).φ (ΦYn z) (ΦYn z') = potAt BM l p (bp (Fin.tail z')) (flagAt H τ ca cb (z' 0) (Fin.tail z') p.1) + (Hh z').re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_member_potential | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_member_potential | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.fibre_member_potential <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightThresholdLimitCoefficientsStatement
section
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.Small Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_threshold_limit_coefficients : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem) (B : ℕ) (u : Wt Ψ N) (g : ℝ) (c : T.Comp) (s : ℕ → ℝ) (q : ℕ → ℕ) (m : ℕ → Option (Ψ × Fin N) → ℤ), IsFullIntersectionSystem II → T.T1 II → WeightHyp T.j u g → bigB0 u g < B + 1 → (∀ n, 0 < s n) → Tendsto s atTop (𝓝 0) → (∀ n, 0 < q n) → (∀ n j, (m n j : ℝ) = q n * (T.M B c).coef (T.lamS u (s n)) (s n) j) → (∀ᶠ n in atTop, IsNefH (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n))) ∧ Tendsto (fun n => geomDeg (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / (q n : ℝ) ^ dimFl Ψ N) atTop (𝓝 ((T.M B c).δ * (T.vol c * flagDeg u))) ∧ Tendsto (fun n => normHt II (T.M B c).P (combLine ((T.M B c).line (scale (s n))) (m n)) (dimFl Ψ N) / q n) atTop (𝓝 (T.slope II B c u)) ∧ 0 < T.vol c * flagDeg u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Small.tower_seq | exact GlobalTheory.CompanionTheory.Ar.Small.tower_seq | (intros; apply GlobalTheory.CompanionTheory.Ar.Small.tower_seq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.YvEqSumMinorsGMatStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.yv_eq_sum_minors_gMat : ∀ (Ψ : Type) [Fintype Ψ] (p q : ℕ) (Ω : Type) [Field Ω] (n : Ψ ⊕ Ψ → ℕ) (A : ∀ s, Matrix (Fin (n s)) (Fin (rk Ψ p q s)) Ω) (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω), ∀ r k, blkF Ψ p q K₀ r = some k → ∀ i : idx J₀ n k, yv A x₀ ⟨k, i⟩ = ∑ I, algebraMap Ω (GenField Ω (rk Ψ p q)) (coefF A ⟨k, i⟩ I) * minorIJ (gMat p q Ω r.1) I (stepCols (p + q) p r.2) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings.yv_step | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings.yv_step | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.BlockEmbeddings.yv_step <;> assumption)
end

