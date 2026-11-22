import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0018

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.AnResBridgeProj
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge

open ReciprocityTheory.ChartRestriction.G.Geo

open MvPolynomial MeasureTheory ReciprocityTheory.AnForm.M

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {P J : Ideal (MRing ι)} {e : ℕ}

def brQ (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    Fin e → ℂ :=
  fun i => Ψ (segre (R.lift x x)) i.succ / Ψ (segre (R.lift x x)) 0

def brBad (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) : Set R.X :=
  {x | R.lift x x ∈ mcPts J} ∪ {x | Ψ (segre (R.lift x x)) 0 = 0} ∪
    {x | ∃ j, x ∈ (R.A.chart j).source ∧
      ¬ (AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
        LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0)}

def brW (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.X) :
    ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.lift x x)) 0)⁻¹ • segre (R.lift x x)

variable (R : AnRes P J e) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ))

theorem brGood : ∀ x ∉ brBad R Ψ, ∀ j, x ∈ (R.A.chart j).source →
    AnalyticAt ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) ∧
      LinearMap.det (fderiv ℂ (brQ R Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
        (Fin e → ℂ) →ₗ[ℂ] (Fin e → ℂ)) ≠ 0 := by
  intro x hx j hj
  by_contra h
  exact hx (Or.inr ⟨j, hj, h⟩)

theorem notMemB_of_notMem_brBad {x : R.X} (hx : x ∉ brBad R Ψ) : R.lift x x ∉ mcPts J :=
  fun h => hx (Or.inl (Or.inl h))

theorem projection_zero_ne_of_notMem_bridgeBadSet {x : R.X} (hx : x ∉ brBad R Ψ) :
    Ψ (segre (R.lift x x)) 0 ≠ 0 :=
  fun h => hx (Or.inl (Or.inr h))

theorem brW_mem_fibre (hK : Nonempty K) (hPh : IsMultiHomogIdeal P) {x : R.X}
    (h0 : Ψ (segre (R.lift x x)) 0 ≠ 0) : brW R Ψ x ∈ fibre P Ψ (brQ R Ψ x) := by
  classical
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre (R.lift x x)) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre (R.lift x x)) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * R.lift x x p, mcPts_smul hPh c hc (R.mem x x (R.mem_U x)), ?_, ?_⟩
  · rw [segre_smul, hpc]; rfl
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [brW, h0]
    · simp only [brW, map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ, brQ]
      rw [div_eq_inv_mul]

theorem brW_injOn : Set.InjOn (brW R Ψ) {x | R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  refine R.inj x x' hx.1 ?_
  refine sameOrbit_of_segre (R.mem x' x' (R.mem_U x')).1
    (Ψ (segre (R.lift x x)) 0 * (Ψ (segre (R.lift x' x')) 0)⁻¹) (by simp [hx.2, hx'.2]) ?_
  have := congrArg (fun v => Ψ (segre (R.lift x x)) 0 • v) hw
  simp only [brW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
  exact this

theorem brFib_finite (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (y : Fin e → ℂ) :
    (brQ R Ψ ⁻¹' {y} \ brBad R Ψ).Finite := by
  refine Set.Finite.of_finite_image (f := brW R Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_)
    ((brW_injOn R Ψ).mono fun x hx => show _ ∧ _ from
      ⟨notMemB_of_notMem_brBad R Ψ hx.2, projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2⟩)
  rintro _ ⟨x, hx, rfl⟩
  have := brW_mem_fibre R Ψ hP.1 hP.2.1.2.1 (projection_zero_ne_of_notMem_bridgeBadSet R Ψ hx.2)
  rwa [show brQ R Ψ x = y from hx.1] at this

theorem exists_of_mem_fibre {y : Fin e → ℂ} {w : ((k : K) → ι k) → ℂ} (hw : w ∈ fibre P Ψ y)
    (hy : ¬ ∃ z ∈ mcPts P, z ∈ mcPts J ∧ Ψ (segre z) = Fin.cons 1 y) :
    ∃ x, R.lift x x ∉ mcPts J ∧ Ψ (segre (R.lift x x)) 0 ≠ 0 ∧ brQ R Ψ x = y ∧ brW R Ψ x = w := by
  obtain ⟨z, hz, rfl, hΨz⟩ := hw
  have hzJ : z ∉ mcPts J := fun h => hy ⟨z, hz, h, hΨz⟩
  obtain ⟨x, c, hc, hxc⟩ := R.surj z hz hzJ
  have hseg : segre (R.lift x x) = (∏ k, c k) • segre z := by rw [hxc, segre_smul]
  have hpc : ∏ k, c k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc k
  have hΨx : Ψ (segre (R.lift x x)) = (∏ k, c k) • Fin.cons 1 y := by rw [hseg, map_smul, hΨz]
  have h0 : Ψ (segre (R.lift x x)) 0 = ∏ k, c k := by simp [hΨx]
  refine ⟨x, fun h => hzJ ?_, by rw [h0]; exact hpc, ?_, ?_⟩
  · refine mem_mcPts_of_sameOrbit R.homog ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩ h
    funext p
    rw [hxc]
    field_simp [hc p.1]
  · funext i
    simp only [brQ, hΨx, h0, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
    field_simp
  · rw [brW, h0, hseg, smul_smul, inv_mul_cancel₀ hpc, one_smul]

end GroundTheory.Heights₂.Heights.HilbertSamuel.AnResBridge
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BlockResolutionMetricObjects
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

variable {D : ℕ} {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {Ω : Type} [Field Ω] [CharZero Ω]

def blockCGram (d : HSMBlockDatum D K ι Ω) (n : ℕ) {r : ℕ} (b : Fin r → MvPolynomial (Σ k, ι k) ℚ) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun k l => ∫ x, pairValH d.A n (b k) (b l) (blockPt d x) ∂d.dV

open Classical in

def blockCChi (d : HSMBlockDatum D K ι Ω) (n : ℕ) : ℝ :=
  if h : ∃ p : (Σ r : ℕ, Fin r → MvPolynomial (Σ k, ι k) ℚ), IsSecBasisM d.y d.k₀ n p.2 then
    -(1 / 2) * Real.log (blockCGram d n h.choose.2).det.re
  else 0

def blockInterpPot (d : HSMBlockDatum D K ι Ω) (A A' : HermLine ι) (t : ℝ) : LocPot d.R.X where
  U := d.R.U
  isOpen_U := d.R.isOpen_U
  mem_U := d.R.mem_U
  φ x y := (1 - t) * Real.log (A.h (d.R.lift x y)) + t * Real.log (A'.h (d.R.lift x y))

def blockMetricInt (d : HSMBlockDatum D K ι Ω) (A' : HermLine ι) : ℝ :=
  ∫ t in (0 : ℝ)..1, mInt d.R.A (fun _ => blockInterpPot d d.A A' t)
    fun x => Real.log (A'.h (blockPt d x) / d.A.h (blockPt d x))

def blockMixPot (A A' : HermLine ι) (D i : ℕ) : Fin D → ((Σ k, ι k) → ℂ) → ℝ :=
  fun j z => if j.val < i then Real.log (A'.h z) else Real.log (A.h z)

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.CharacterNondegenerate
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter

noncomputable section

namespace NormCountBounded

section Coords

variable {Ω : Type} [Field Ω] {κ : Type} [Fintype κ]

theorem exists_coord_ne_zero {x : Ix κ → Ω} {d : ℕ} (h : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) d) :
    ∃ c : κ, x ⟨(), c⟩ ≠ 0 := by
  obtain ⟨i, hi⟩ := h.2.1.2.2 ()
  refine ⟨i, fun h0 => hi ?_⟩
  rw [mCoordIdeal, RingHom.mem_ker]
  simp [mConeMap, h0]

theorem aeval_mul_zpow_mem (x : Ix κ → Ω) (c : κ) {τ : ℕ} {g : MRing (GlobalTheory κ)}
    (hg : IsMultiHomog g (fun _ => τ)) :
    aeval x g * x ⟨(), c⟩ ^ (-(τ : ℤ)) ∈ chartRingZ (ι := GlobalTheory κ) x (fun _ => c) := by
  have hsum : ∀ m ∈ g.support, ∑ p ∈ m.support, m p = τ := by
    intro m hm
    rw [Finset.sum_subset (Finset.subset_univ m.support) (fun p _ hp => by simpa using hp),
      Fintype.sum_sigma]
    simpa using hg m hm ()
  have key : aeval x g * x ⟨(), c⟩ ^ (-(τ : ℤ)) =
      aeval (fun p : Ix κ => x p / x ⟨(), c⟩) g := by
    conv_lhs => rw [g.as_sum]
    conv_rhs => rw [g.as_sum]
    rw [map_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [aeval_monomial, aeval_monomial, Finsupp.prod, Finsupp.prod]
    simp only [div_eq_mul_inv, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hsum m hm,
      zpow_neg, zpow_natCast]
    ring
  rw [key, chartRingZ, Algebra.adjoin_range_eq_range_aeval]
  exact ⟨g, rfl⟩

theorem secM_le_chartLat (x : Ix κ → Ω) (τ : ℕ) :
    secM (ι := GlobalTheory κ) x (fun _ => τ) ≤ chartLat (ι := GlobalTheory κ) x 1 τ := by
  intro s hs
  have hle : Submodule.span ℤ {s | ∃ g : MRing (GlobalTheory κ), IsMultiHomog g (fun _ => τ) ∧ aeval x g = s} ≤
      (chartLat (ι := GlobalTheory κ) x 1 τ).toIntSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨g, hg, rfl⟩ c _
    have hc : c = fun _ => c () := rfl
    rw [hc]
    simpa using aeval_mul_zpow_mem x (c ()) hg
  exact hle hs

end Coords

section Counts

variable {Ω : Type} [Field Ω]

theorem smallSectionCount_mono_lattice {P : ℕ → Ω → Prop} {La La' : ℕ → AddSubgroup Ω} {τ : ℕ} (hle : La τ ≤ La' τ)
    (hfin : {s : La' τ | P τ (s : Ω)}.Finite) : smallSectionCount P La τ ≤ smallSectionCount P La' τ := by
  unfold smallSectionCount
  have : Finite {s : La' τ // P τ (s : Ω)} := hfin.to_subtype
  have hcard : Nat.card {s : La τ // P τ (s : Ω)} ≤ Nat.card {s : La' τ // P τ (s : Ω)} :=
    Nat.card_le_card_of_injective (fun s => ⟨⟨s.1.1, hle s.1.2⟩, s.2⟩) fun s t h => by
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
  rcases Nat.eq_zero_or_pos (Nat.card {s : La τ // P τ (s : Ω)}) with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_natCast_nonneg _
  · exact Real.log_le_log (by exact_mod_cast hpos) (by exact_mod_cast hcard)

theorem smallSectionCount_nonneg (P : ℕ → Ω → Prop) (La : ℕ → AddSubgroup Ω) (τ : ℕ) : 0 ≤ smallSectionCount P La τ :=
  Real.log_natCast_nonneg _

theorem liminf_le_limsup_of_le {f g : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (hfg : ∀ n, f n ≤ g n)
    (hg : ∃ B, ∀ᶠ n in atTop, g n ≤ B) : liminf f atTop ≤ limsup g atTop := by
  obtain ⟨B, hB⟩ := hg
  have hfb : IsBoundedUnder (· ≤ ·) atTop f := ⟨B, by simpa using hB.mono fun n hn => (hfg n).trans hn⟩
  have hfb' : IsBoundedUnder (· ≥ ·) atTop f := isBoundedUnder_of ⟨0, fun n => hf n⟩
  have hgb : IsBoundedUnder (· ≤ ·) atTop g := ⟨B, by simpa using hB⟩
  exact (liminf_le_limsup hfb hfb').trans
    (limsup_le_limsup (Eventually.of_forall hfg) hfb'.isCoboundedUnder_flip hgb)

theorem norm_count_bounded {h : ℕ → ℝ} {C : ℝ} (D : ℕ) (hC : ∀ τ, h τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1)) :
    ∃ B, ∀ᶠ τ in atTop, h τ / ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) ≤ B := by
  refine ⟨|C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ), eventually_atTop.2 ⟨1, fun τ hτ => ?_⟩⟩
  have hτ' : (1 : ℝ) ≤ τ := by exact_mod_cast hτ
  have hfac : (0 : ℝ) < (D + 1).factorial := by exact_mod_cast Nat.factorial_pos _
  have hden : 0 < (τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ) := by positivity
  rw [div_le_iff₀ hden]
  have h1 : ((τ : ℝ) + 1) ^ (D + 1) ≤ 2 ^ (D + 1) * (τ : ℝ) ^ (D + 1) := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc h τ ≤ C * ((τ : ℝ) + 1) ^ (D + 1) := hC τ
    _ ≤ |C| * ((τ : ℝ) + 1) ^ (D + 1) := mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 ^ (D + 1) * (τ : ℝ) ^ (D + 1)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg C)
    _ = |C| * 2 ^ (D + 1) * ((D + 1).factorial : ℝ) * ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)) := by
      field_simp

end Counts

end NormCountBounded

namespace NormCountBounded

theorem semipositiveH_of_rel {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P0 P : Ideal (MRing ι)} {A : HermLine ι} (hle : P0 ≤ P) (h : IsSemipositiveRel P0 P A) :
    IsSemipositiveH P A :=
  ⟨h.1, fun z hz w hw => h.2 z hz w fun f hf => hw f (hle hf)⟩

end NormCountBounded

open NormCountBounded in

theorem G6.proof (hA : ArithmeticVolumeResolution.Statement) (hRE : ResExistsStatement) (hRB : ResBridgeStatement)
    (hP : PackingStatement) (hC : BirationalCoordinates.Statement) (hG : ArithmeticVolumeBig.Statement) :
    G6.Statement := by
  refine ⟨?_, G6.statementB_of_G6Prime hG⟩
  intro D Ω _ _ κ _ x m II hII hg
  have harx : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hg.arith
  obtain ⟨c, hc⟩ := exists_coord_ne_zero harx
  obtain ⟨Ω', _, _, x', hI, hbir, hcount⟩ := hC Ω κ x c hc
  obtain ⟨P0, hP0, hsemi⟩ := hg.semipos
  rw [coordIdeal_eq_mCoordIdeal, ← hI] at hP0 hsemi
  have har' : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x') (D + 1) := hI ▸ harx
  have hsm : IsSmoothHerm (HermLine.ofCone m) := hsemi.1
  have key := hA hRE hRB κ Ω' (fun i => x' ⟨(), i⟩) D (HermLine.ofCone m) II hg.one_le hII rfl har' hbir
    (semipositiveH_of_rel hP0 hsemi) (fun z => hg.conjInv z)
  have hpack := hP Unit (GlobalTheory κ) Ω' x' D (HermLine.ofCone m) (chartLat (ι := GlobalTheory κ) x' (HermLine.ofCone m).a)
    har' hbir hsm (fun τ s hs c hc => isIntegral_algebraMap (x := (⟨_, hs c hc⟩ : chartRingZ (ι := GlobalTheory κ) x' c)))
  obtain ⟨C, hCb⟩ := hpack.2
  have htop : top II x m D = II Unit (GlobalTheory κ) (mCoordIdeal (ι := GlobalTheory κ) x') (D + 1)
      (fun _ => HermLine.ofCone m) := by
    change II Unit (GlobalTheory κ) (coordIdeal ℤ x) (D + 1) (fun _ => HermLine.ofCone m) = _
    rw [coordIdeal_eq_mCoordIdeal, hI]
  have hvol : arVolP (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x) x (HermLine.ofCone m))
        (chartLat (ι := GlobalTheory κ) x (HermLine.ofCone m).a) 1 D =
      limsup (fun τ : ℕ => smallSectionCount (IsSmallH (mCoordIdeal (ι := GlobalTheory κ) x') x' (HermLine.ofCone m))
        (chartLat (ι := GlobalTheory κ) x' (HermLine.ofCone m).a) τ / ((τ : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)))
        atTop := by
    simp only [arVolP, one_mul, hcount]
  rw [htop, hvol]
  refine key.trans (liminf_le_limsup_of_le (fun τ => div_nonneg (smallSectionCount_nonneg _ _ _) (by positivity))
    (fun τ => div_le_div_of_nonneg_right (smallSectionCount_mono_lattice (secM_le_chartLat x' τ) (hpack.1 τ)) (by positivity))
    (norm_count_bounded D hCb))

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.EvalEqZeroOfAevalEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory

noncomputable section

set_option linter.unusedSectionVars false

section Block

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem hermLine_eq_of_a_h {A B : HermLine ι} (ha : A.a = B.a) (hh : A.h = B.h) : A = B := by
  obtain ⟨a, h, _, _⟩ := A
  obtain ⟨a', h', _, _⟩ := B
  subst ha
  subst hh
  rfl

theorem hpow.equiv (A B : HermLine ι) (j : ℕ) :
    IndefiniteRowSideFullHecke.HilbertSamuel.hpow A j = HermLine.zcomb A B (j : ℤ) 0 := by
  refine hermLine_eq_of_a_h ?_ ?_
  · show (j : ℤ) • A.a = (j : ℤ) • A.a + (0 : ℤ) • B.a
    simp
  · funext z
    show A.h z ^ j = A.h z ^ (j : ℤ) * B.h z ^ (0 : ℤ)
    simp

theorem hpow_a_apply (A : HermLine ι) (τ : ℕ) (k : K) :
    (IndefiniteRowSideFullHecke.HilbertSamuel.hpow A τ).a k = τ * A.a k := by
  simp [IndefiniteRowSideFullHecke.HilbertSamuel.hpow]

theorem SupLE.equiv (P : Ideal (MRing ι)) (y : (Σ k, ι k) → Ω) (A : HermLine ι) (τ : ℕ) (c : ℝ) (s : Ω) :
    IsBoundedH P y A τ c s ↔
      IndefiniteRowSideFullHecke.HilbertSamuel.SupLE P y (IndefiniteRowSideFullHecke.HilbertSamuel.hpow A τ).a (IndefiniteRowSideFullHecke.HilbertSamuel.hpow A τ).h c s := by
  simp only [IsBoundedH, IndefiniteRowSideFullHecke.HilbertSamuel.SupLE, hpow_a_apply]
  rfl

theorem eval_eq_zero_of_aeval_eq_zero {y : (Σ k, ι k) → Ω} {h : MRing ι} {d : K → ℕ}
    (hh : IsMultiHomog h d) (h0 : aeval y h = 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) :
    eval z (map (Int.castRingHom ℂ) h) = 0 := by
  have hmem : h ∈ mCoordIdeal y := by
    show mConeMap y h = 0
    rw [ProjLine.mConeMap_eq_of_isMultiHomog y hh, h0, map_zero, zero_mul]
  exact hz.2 h hmem

theorem PtDominated.of_ptBoundOn {y : (Σ k, ι k) → Ω} {M L' : HermLine ι} {n : ℕ}
    {U : Set ((Σ k, ι k) → ℂ)} {c : ℝ} {f f' : Ω} (hB : PtBoundOn y M L' n U c f f') :
    ∀ z ∈ U, IndefiniteRowSideFullHecke.HilbertSamuel.PtDominated y (IndefiniteRowSideFullHecke.HilbertSamuel.hpow M n).a
      (IndefiniteRowSideFullHecke.HilbertSamuel.hpow L' n).a (IndefiniteRowSideFullHecke.HilbertSamuel.hpow M n).h (IndefiniteRowSideFullHecke.HilbertSamuel.hpow L' n).h
      c f f' z := by
  intro z hz g h g' h' ⟨dg, dh, hg, hh, hd, _, he⟩ ⟨dg', dh', hg', hh', hd', _, he'⟩ h0 h0'
  exact hB dg dh dg' dh' g h g' h' hg hh (fun k ↦ by rw [hd k, hpow_a_apply]) he hg' hh'
    (fun k ↦ by rw [hd' k, hpow_a_apply]) he' z hz h0 h0'

theorem PtDominated.equiv {y : (Σ k, ι k) → Ω} {M L' : HermLine ι} {n : ℕ}
    {U : Set ((Σ k, ι k) → ℂ)} (hU : U ⊆ mcPts (mCoordIdeal y)) (c : ℝ) (f f' : Ω) :
    PtBoundOn y M L' n U c f f' ↔
      ∀ z ∈ U, IndefiniteRowSideFullHecke.HilbertSamuel.PtDominated y (IndefiniteRowSideFullHecke.HilbertSamuel.hpow M n).a
        (IndefiniteRowSideFullHecke.HilbertSamuel.hpow L' n).a (IndefiniteRowSideFullHecke.HilbertSamuel.hpow M n).h (IndefiniteRowSideFullHecke.HilbertSamuel.hpow L' n).h
        c f f' z := by
  refine ⟨PtDominated.of_ptBoundOn, fun hT ↦ ?_⟩
  intro dg dh dg' dh' g h g' h' hg hh hd he hg' hh' hd' he' z hz h0 h0'
  have hy : aeval y h ≠ 0 := fun hy ↦ h0 (eval_eq_zero_of_aeval_eq_zero hh hy (hU hz))
  have hy' : aeval y h' ≠ 0 := fun hy ↦ h0' (eval_eq_zero_of_aeval_eq_zero hh' hy (hU hz))
  exact hT z hz g h g' h' ⟨dg, dh, hg, hh, fun k ↦ by rw [hd k, hpow_a_apply], hy, he⟩
    ⟨dg', dh', hg', hh', fun k ↦ by rw [hd' k, hpow_a_apply], hy', he'⟩ h0 h0'

theorem hHat0.equiv (y : (Σ k, ι k) → Ω) (A : HermLine ι) (n : ℕ) :
    IndefiniteRowSideFullHecke.HilbertSamuel.hHat0 y A n = smallSectionCount (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) n :=
  rfl

theorem volHat.equiv (y : (Σ k, ι k) → Ω) (A : HermLine ι) (D : ℕ) :
    IndefiniteRowSideFullHecke.HilbertSamuel.volHat y A D = arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D :=
  rfl

end Block

section OneBlock

variable {Ω : Type} [Field Ω] [CharZero Ω] {κ : Type} [Fintype κ]

theorem blockNonzero_eq_ne_zero :
    {z : Ix κ → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} = {z | z ≠ 0} := by
  ext z
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro h rfl
    obtain ⟨i, hi⟩ := h ()
    exact hi rfl
  · intro hz k
    obtain ⟨⟨⟨⟩, i⟩, hp⟩ := Function.ne_iff.mp hz
    cases k
    exact ⟨i, hp⟩

theorem IsHSDatum.equiv (D : ℕ) (x : Ix κ → Ω) (m : ConeMetric ℂ (Ix κ)) :
    IsGoodDatum D x m ↔ ∃ P₀, IndefiniteRowSideFullHecke.HilbertSamuel.IsHSDatum D x m P₀ := by
  constructor
  · rintro ⟨h1, ha, hi, _, hc, P₀, hle, hsp⟩
    exact ⟨P₀, ⟨h1, ha, hi, hle, hsp, hc⟩⟩
  · rintro ⟨P₀, ⟨h1, ha, hi, hle, hsp, hc⟩⟩
    refine ⟨h1, ha, hi, ?_, hc, P₀, hle, hsp⟩
    have hs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m.ρ {z : Ix κ → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} := hsp.1
    rw [blockNonzero_eq_ne_zero] at hs
    exact hs

end OneBlock

section Volume

@[reducible] def chartedSpaceOfAtlas {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) :
    ChartedSpace (Fin e → ℂ) X where
  atlas := Set.range A.chart
  chartAt x := A.chart (Classical.choose (A.cover x))
  mem_chart_source x := Classical.choose_spec (A.cover x)
  chart_mem_atlas _ := ⟨_, rfl⟩

theorem IsSmoothVolume.equiv {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] (A : FinHolAtlas e X)
    (dV : Measure X) :
    IsSmoothVolume A dV ↔ @IndefiniteRowSideFullHecke.HilbertSamuel.IsSmoothVolume e X _ (chartedSpaceOfAtlas A) _ dV := by
  unfold IsSmoothVolume IndefiniteRowSideFullHecke.HilbertSamuel.IsSmoothVolume
  refine and_congr_right fun _ ↦ ⟨fun h c hc ↦ ?_, fun h j ↦ ?_⟩
  · obtain ⟨j, rfl⟩ := hc
    obtain ⟨ν, h1, h2, h3⟩ := h j
    exact ⟨ν, h1, h2, fun S hS hsub ↦ by
      rw [h3 S hS hsub, (A.chart j).image_eq_target_inter_inv_preimage hsub]⟩
  · obtain ⟨ν, h1, h2, h3⟩ := h (A.chart j) ⟨j, rfl⟩
    exact ⟨ν, h1, h2, fun S hS hsub ↦ by
      rw [h3 S hS hsub, (A.chart j).image_eq_target_inter_inv_preimage hsub]⟩

end Volume

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.IsSemipositiveRelTrivLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter

noncomputable section

def ArithmeticVolumeDegreeZero.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (A : HermLine ι) (P0 : Ideal (MRing ι)) (II : IntersectionSystem),
    1 ≤ D → IsIntersectionSystem II → IsArithVar (mCoordIdeal y) (D + 1) → Birational y →
    P0 ≤ mCoordIdeal y → IsSemipositiveRel P0 (mCoordIdeal y) A → NefOnFibres (mCoordIdeal y) A.a →
    IsConjInvariantH A → genDeg (mCoordIdeal y) D A.a ≤ 0 →
    II K ι (mCoordIdeal y) (D + 1) (fun _ => A) ≤ arVolP (IsSmallH (mCoordIdeal y) y A) (chartLat y A.a) 1 D

namespace ArithmeticVolumeDegreeZero

def trivLine {K : Type} [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] : HermLine ι where
  a := 0
  h _ := 1
  pos _ _ := one_pos
  smul c z hc := by simp

end ArithmeticVolumeDegreeZero

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLiftPrime
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem LiftPrime.proof (h : Lift.Statement) : LiftPrime.Statement := h

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

