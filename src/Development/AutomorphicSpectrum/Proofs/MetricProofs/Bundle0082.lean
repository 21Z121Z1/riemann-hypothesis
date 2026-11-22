import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0042
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0038
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0043
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0075
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0068
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeDeterminant
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0074
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameMinorValuation

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointInPoints
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt

section General

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}

theorem mConeMap_rename {Ω : Type} [Field Ω] (hv : IsBlockMap κ v) (y : (Σ k, ι' k) → Ω) (g : MRing ι) :
    mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp, rename_X]
    congr 1
    simp [mConeMap, hv.2.2.1 n]

theorem rename_mem_iff {Ω : Type} [Field Ω] (hv : IsBlockMap κ v) (y : (Σ k, ι' k) → Ω) (g : MRing ι) :
    rename v g ∈ mCoordIdeal y ↔ g ∈ mCoordIdeal (y ∘ v) := by
  change mConeMap y (rename v g) = 0 ↔ mConeMap (y ∘ v) g = 0
  rw [mConeMap_rename hv]
  exact map_eq_zero_iff _ (rename_injective κ hv.1)

theorem mConeMap_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    mConeMap (φ ∘ x) g = map φ (mConeMap x g) := by
  induction g using MvPolynomial.induction_on with
  | C a => simp [mConeMap]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p n hp =>
    simp only [map_mul, hp]
    congr 1
    simp [mConeMap]

theorem mCoordIdeal_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) :
    mCoordIdeal (φ ∘ x) = mCoordIdeal x := by
  ext g
  change mConeMap (φ ∘ x) g = 0 ↔ mConeMap x g = 0
  rw [mConeMap_comp]
  exact map_eq_zero_iff _ (map_injective φ φ.injective)

theorem eval_rename_eq (z : (Σ k, ι' k) → ℂ) (g : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename v g)) = eval (z ∘ v) (map (Int.castRingHom ℂ) g) := by
  rw [map_rename, eval_rename]

theorem sum_mapDomain_block (hv : ∀ p, (v p).1 = κ p.1) [DecidableEq K'] (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  classical
  induction m using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add]
    simp only [Finsupp.add_apply, Finset.sum_add_distrib, hf, hg]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  | single p n =>
    have hR : (∑ q : Σ k, ι k, if κ q.1 = k' then (Finsupp.single p n) q else 0) =
        if κ p.1 = k' then n else 0 := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq
        simp [Finsupp.single_apply, Ne.symm hq]
      · simp
    have hL : ∀ q : Σ k, ι' k, ∑ i, (Finsupp.single q n) ⟨k', i⟩ = if q.1 = k' then n else 0 := by
      rintro ⟨kq, iq⟩
      by_cases h : kq = k'
      · subst h
        simp [Finsupp.single_apply]
      · simp [Finsupp.single_apply, h]
    rw [Finsupp.mapDomain_single, hL, hR, hv]

theorem isMultiHomog_rename_block (hb : IsBlockMap κ v) {f : MRing ι} {b : K → ℕ} (hf : IsMultiHomog f b) :
    IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  classical
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m₀, hm₀, rfl⟩ := hm
  rw [sum_mapDomain_block hb.2.2.1, Fintype.sum_sigma]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, Finset.sum_eq_single k]
    · simpa using hf m₀ hm₀ k
    · intro k₂ _ hne
      exact Finset.sum_eq_zero fun i _ => if_neg (hb.1.ne hne)
    · simp
  · rw [Function.extend_apply' _ _ _ hk]
    exact Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun i _ => if_neg fun h => hk ⟨k, h⟩

theorem comp_mem_mcPts {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x')) : z ∘ v ∈ mcPts (mCoordIdeal x) := by
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz.1 (κ k)
    obtain ⟨⟨k₀, i⟩, hp⟩ := hv.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have hk : k₀ = k := hv.1 ((hv.2.2.1 ⟨k₀, i⟩).symm.trans (congrArg Sigma.fst hp))
    subst hk
    exact ⟨i, by simpa [hp] using hi'⟩
  · have h1 : rename v f ∈ mCoordIdeal x' := by
      rw [rename_mem_iff hv, show x' ∘ v = φ ∘ x from funext hx, mCoordIdeal_comp]
      exact hf
    rw [← eval_rename_eq]
    exact hz.2 _ h1

theorem aeval_rename_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'}
    (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q)) (f : MRing ι) :
    aeval x' (rename v f) = φ (aeval x f) := by
  rw [aeval_rename, show x' ∘ v = φ ∘ x from funext hx, aeval_def, aeval_def, algebraMap_int_eq,
    algebraMap_int_eq, eval₂_comp_left φ, RingHom.ext_int (φ.comp (Int.castRingHom Ω)) (Int.castRingHom Ω')]

theorem regAt_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} {s : Ω} (hs : RegAt x (mCoordIdeal (z ∘ v)) s) :
    RegAt x' (mCoordIdeal z) (φ s) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  refine ⟨_, rename v g, rename v h, isMultiHomog_rename_block hv hg, isMultiHomog_rename_block hv hh,
    fun hm => hn ((rename_mem_iff hv z h).1 hm), ?_⟩
  rw [aeval_rename_pull φ hx, aeval_rename_pull φ hx, heq, map_mul]

theorem isValueAt_pull {Ω Ω' : Type} [Field Ω] [Field Ω'] (hv : IsBlockMap κ v)
    {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (φ : Ω →+* Ω') (hx : ∀ q, x' (v q) = φ (x q))
    {z : (Σ k, ι' k) → ℂ} {s : Ω} {w : ℂ} (hs : IsValueAt x s (z ∘ v) w) : IsValueAt x' (φ s) z w := by
  obtain ⟨d, g, h, hg, hh, hy, heq, h0, rfl⟩ := hs
  have hpull := aeval_rename_pull (v := v) φ hx
  refine ⟨_, rename v g, rename v h, isMultiHomog_rename_block hv hg, isMultiHomog_rename_block hv hh, ?_, ?_, ?_, ?_⟩
  · rw [hpull]; exact (map_ne_zero φ).2 hy
  · rw [hpull, hpull, heq, map_mul]
  · rwa [eval_rename_eq]
  · rw [eval_rename_eq, eval_rename_eq]

end General

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ), zb ∈ mcPts (mCoordIdeal M'.x) → zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) ∧ ∀ s : M.Ω, RegAt M.x (mCoordIdeal (zb ∘ Cv.v)) s → RegAt M'.x (mCoordIdeal zb) (Cv.φ s) ∧ valAt M'.x (Cv.φ s) zb = valAt M.x s (zb ∘ Cv.v) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb hzb
  have hz := comp_mem_mcPts Cv.block Cv.φ Cv.x_eq hzb
  refine ⟨hz, fun s hs => ?_⟩
  obtain ⟨w, hw⟩ := ValRing.exists_isValueAt hz hs
  have hw' := isValueAt_pull Cv.block Cv.φ Cv.x_eq hw
  exact ⟨regAt_pull Cv.block Cv.φ Cv.x_eq hs, by rw [valAt_eq hzb hw', valAt_eq hz hw]⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverBasePointRegular
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegPhi

section Forms

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem sum_mapDomain_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hv : ∀ p, (v p).1 = κ p.1)
    (m : (Σ k, ι k) →₀ ℕ) (k' : K') :
    ∑ i, (Finsupp.mapDomain v m) ⟨k', i⟩ = ∑ p : Σ k, ι k, if κ p.1 = k' then m p else 0 := by
  have e1 : ∀ q : (Σ k, ι' k) →₀ ℕ, ∑ i, q ⟨k', i⟩ = q.sum (fun r x => if r.1 = k' then x else 0) := by
    intro q
    rw [Finsupp.sum_fintype _ _ (fun r => by simp), Fintype.sum_sigma,
      Finset.sum_eq_single k' (fun b _ hb => by simp [hb]) (by simp)]
    simp
  have e2 : ∑ p : Σ k, ι k, (if κ p.1 = k' then m p else 0) = m.sum (fun p x => if κ p.1 = k' then x else 0) := by
    rw [Finsupp.sum_fintype _ _ (fun r => by simp)]
  rw [e1, e2, Finsupp.sum_mapDomain_index (fun r => by simp) (fun r a b => by split_ifs <;> simp)]
  simp only [hv]

theorem isMultiHomog_rename_block {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v) {f : MRing ι}
    {b : K → ℕ} (hf : IsMultiHomog f b) : IsMultiHomog (rename v f) (Function.extend κ b 0) := by
  intro m hm k'
  rw [support_rename_of_injective hb.2.1, Finset.mem_image] at hm
  obtain ⟨m0, hm0, rfl⟩ := hm
  rw [sum_mapDomain_block hb.2.2.1]
  by_cases hk : ∃ k, κ k = k'
  · obtain ⟨k, rfl⟩ := hk
    rw [hb.1.extend_apply, ← hf m0 hm0 k]
    simp only [hb.1.eq_iff]
    rw [Fintype.sum_sigma, Finset.sum_eq_single k (fun b _ hb' => by simp [hb']) (by simp)]
    simp
  · rw [Function.extend_apply' _ _ _ hk, Pi.zero_apply]
    apply Finset.sum_eq_zero
    intro p _
    rw [if_neg (fun h => hk ⟨p.1, h⟩)]

theorem mConeMap_rename {Ω : Type} [Field Ω] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    (y : (Σ k, ι' k) → Ω) (g : MRing ι) : mConeMap y (rename v g) = rename κ (mConeMap (y ∘ v) g) := by
  simp only [mConeMap]
  rw [aeval_rename]
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp [hp, hq]
  | mul_X p i hp =>
    simp [hp, hb.2.2.1 i]

theorem mConeMap_comp {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    mConeMap (φ ∘ x) g = map φ (mConeMap x g) := by
  simp only [mConeMap]
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul]
    rw [hp]
    simp only [aeval_X, Function.comp_apply, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

theorem aeval_comp_ringHom {Ω Ω' : Type} [Field Ω] [Field Ω'] (φ : Ω →+* Ω') (x : (Σ k, ι k) → Ω) (g : MRing ι) :
    aeval (φ ∘ x) g = φ (aeval x g) := by
  induction g using MvPolynomial.induction_on with
  | C a =>
    simp
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp, aeval_X, Function.comp_apply]

theorem eval_rename_block (v : (Σ k, ι k) → Σ k, ι' k) (z : (Σ k, ι' k) → ℂ) (f : MRing ι) :
    eval z (map (Int.castRingHom ℂ) (rename v f)) = eval (z ∘ v) (map (Int.castRingHom ℂ) f) := by
  rw [map_rename, eval_rename]

theorem rename_notMem {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k} (hb : IsBlockMap κ v)
    {z : (Σ k, ι' k) → ℂ} {h : MRing ι} (hn : h ∉ mCoordIdeal (z ∘ v)) : rename v h ∉ mCoordIdeal z := by
  intro hmem
  apply hn
  rw [mCoordIdeal, RingHom.mem_ker] at hmem ⊢
  rw [mConeMap_rename hb] at hmem
  exact rename_injective κ hb.1 (by rw [hmem, map_zero])

theorem comp_mem_mcPts {Ω Ω' : Type} [Field Ω] [Field Ω'] {κ : K → K'} {v : (Σ k, ι k) → Σ k, ι' k}
    (hb : IsBlockMap κ v) (φ : Ω →+* Ω') {x : (Σ k, ι k) → Ω} {x' : (Σ k, ι' k) → Ω'} (hx : x' ∘ v = φ ∘ x)
    {z : (Σ k, ι' k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x')) : z ∘ v ∈ mcPts (mCoordIdeal x) := by
  unfold mcPts at hz ⊢
  simp only [Set.mem_ofPred_eq] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  refine ⟨fun k => ?_, fun f hf => ?_⟩
  · obtain ⟨i', hi'⟩ := hz1 (κ k)
    obtain ⟨⟨k0, i⟩, hp⟩ := hb.2.2.2 ⟨κ k, i'⟩ ⟨k, rfl⟩
    have h0 := hb.2.2.1 ⟨k0, i⟩
    rw [hp] at h0
    have hk0 : k0 = k := hb.1 h0.symm
    subst hk0
    refine ⟨i, ?_⟩
    show z (v ⟨k0, i⟩) ≠ 0
    rw [hp]
    exact hi'
  · rw [← eval_rename_block v z f]
    apply hz2
    rw [mCoordIdeal, RingHom.mem_ker] at hf ⊢
    rw [mConeMap_rename hb, hx, mConeMap_comp, hf, map_zero, map_zero]

end Forms

private theorem isHecke_div_and_resEtaPow_div {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) {g : MRing ι} {d : K → ℕ} (hg : IsMultiHomog g d) :
    mConeMap y g = C (aeval y g) * ∏ k, X k ^ d k := by
  have key : ∀ m ∈ g.support, (m.prod fun p e => (X p.1 : MvPolynomial K Ω) ^ e) = ∏ k, X k ^ d k := by
    intro m hm
    rw [Finsupp.prod_fintype _ _ (fun p => pow_zero _), Fintype.prod_sigma]
    refine Finset.prod_congr rfl (fun k _ => ?_)
    dsimp only
    rw [Finset.prod_pow_eq_pow_sum, hg m hm k]
  conv_lhs => rw [g.as_sum]
  conv_rhs => rw [g.as_sum]
  simp only [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [← key m hm]
  simp only [mConeMap, aeval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_mul, map_prod,
    map_pow, algebraMap_int_eq, eq_intCast, map_intCast]
  ring

private theorem isPair_and_isPair_of_isTriple {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) {v1 v2 : ℂ}
    (H1 : IsValueAt y s z v1) (H2 : IsValueAt y s z v2) : v1 = v2 := by
  obtain ⟨d1, g1, h1, hg1, hh1, -, he1, hz1, rfl⟩ := H1
  obtain ⟨d2, g2, h2, hg2, hh2, -, he2, hz2, rfl⟩ := H2
  have hmem : g1 * h2 - g2 * h1 ∈ mCoordIdeal y := by
    rw [mCoordIdeal, RingHom.mem_ker, map_sub, map_mul, map_mul, isHecke_div_and_resEtaPow_div y hg1, isHecke_div_and_resEtaPow_div y hh2, isHecke_div_and_resEtaPow_div y hg2,
      isHecke_div_and_resEtaPow_div y hh1, he1, he2]
    simp only [map_mul]
    ring
  unfold mcPts at hz
  obtain ⟨-, hzP⟩ := hz
  have h0 := hzP _ hmem
  simp only [map_sub, map_mul] at h0
  rw [div_eq_div_iff hz1 hz2]
  linear_combination h0

theorem regAt_φ_valAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ) (s : M.Ω), zb ∈ mcPts (mCoordIdeal M'.x) → RegAt M.x (mCoordIdeal (zb ∘ Cv.v)) s → RegAt M'.x (mCoordIdeal zb) (Cv.φ s) ∧ valAt M'.x (Cv.φ s) zb = valAt M.x s (zb ∘ Cv.v) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb s hzb hreg
  obtain ⟨d, g, h, hg, hh, hhn, he⟩ := hreg
  have hb := Cv.block
  have hxv : M'.x ∘ Cv.v = Cv.φ ∘ M.x := funext Cv.x_eq
  have hz' : zb ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := comp_mem_mcPts hb Cv.φ hxv hzb
  have hg' := isMultiHomog_rename_block hb hg
  have hh' := isMultiHomog_rename_block hb hh
  have hhn' := rename_notMem hb hhn
  have hae : ∀ f : MRing (baseIdx ι M.blk), aeval M'.x (rename Cv.v f) = Cv.φ (aeval M.x f) := by
    intro f
    rw [aeval_rename, hxv, aeval_comp_ringHom]
  have he' : aeval M'.x (rename Cv.v g) = Cv.φ s * aeval M'.x (rename Cv.v h) := by
    rw [hae, hae, he, map_mul]
  refine ⟨⟨_, _, _, hg', hh', hhn', he'⟩, ?_⟩
  have hcast : ∀ (w : (Σ k, baseIdx ι M.blk k) → ℂ) (f : MRing (baseIdx ι M.blk)),
      eval w (map (Int.castRingHom ℂ) f) = aeval w f := by
    intro w f
    rw [eval_map, aeval_def, algebraMap_int_eq]
  have hev : eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h) ≠ 0 := by
    intro h0
    apply hhn
    rw [mCoordIdeal, RingHom.mem_ker, isHecke_div_and_resEtaPow_div _ hh, ← hcast, h0, map_zero, zero_mul]
  have hax : aeval M.x h ≠ 0 := by
    intro h0
    have hmem : h ∈ mCoordIdeal M.x := by
      rw [mCoordIdeal, RingHom.mem_ker, isHecke_div_and_resEtaPow_div _ hh, h0, map_zero, zero_mul]
    have hz2 := hz'
    unfold mcPts at hz2
    exact hev (hz2.2 _ hmem)
  have hv1 : IsValueAt M.x s (zb ∘ Cv.v)
      (eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) / eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h)) :=
    ⟨d, g, h, hg, hh, hax, he, hev, rfl⟩
  have hv2 : IsValueAt M'.x (Cv.φ s) zb
      (eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) / eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h)) := by
    refine ⟨_, _, _, hg', hh', ?_, he', ?_, ?_⟩
    · rw [hae]
      exact (map_ne_zero Cv.φ).2 hax
    · rw [eval_rename_block]
      exact hev
    · rw [eval_rename_block, eval_rename_block]
  have hex1 : ∃ v, IsValueAt M.x s (zb ∘ Cv.v) v := ⟨_, hv1⟩
  have hex2 : ∃ v, IsValueAt M'.x (Cv.φ s) zb v := ⟨_, hv2⟩
  unfold valAt
  rw [dif_pos hex1, dif_pos hex2, isPair_and_isPair_of_isTriple hzb hex2.choose_spec hv2, isPair_and_isPair_of_isTriple hz' hex1.choose_spec hv1]

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph.RegPhi
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesValueAtPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg

theorem stepCols_ne_empty {N j : ℕ} (hj : j ≤ N) {i : Fin N} : stepCols N j i ≠ ∅ := by
  intro e
  by_cases hi : (i : ℕ) + 1 ≤ j
  · have h0 : N - j < N := by omega
    have : (⟨N - j, h0⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hi]
      omega
    rw [e] at this
    simp at this
  · have h0 : 0 < N := by have := i.2; omega
    have : (⟨0, h0⟩ : Fin N) ∈ stepCols N j i := by
      simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hi]
      omega
    rw [e] at this
    simp at this

theorem img_form : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk) (h : Ψ → Matrix (Fin N) (Fin N) ℂ), basePart M'.blk z ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → (∀ τ, IsBlockDiag j (h τ)) → (∀ (p : Ψ × Fin N) (k' : K'), M'.blk p = some k' → ∃ a : ℂ, a ≠ 0 ∧ ∀ m' : ι' k', z ⟨k', m'⟩ = a * CovMap.LocImg.plk M' F' (basePart M'.blk z) p.2 ⟨k', m'⟩ (h p.1)) → ∀ (p : Ψ × Fin N) (k : K), M.blk p = some k → ∃ a : ℂ, a ≠ 0 ∧ ∀ m : ι k, CovMap.LocImg.img Cv F' F z ⟨k, m⟩ = a * CovMap.LocImg.plk M F (basePart M'.blk z ∘ Cv.v) p.2 ⟨k, m⟩ (Cv.trans F' F (basePart M'.blk z) p.1 * h p.1) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z F' F h hb hF' hF hG' hG hh hyp p k hp
  obtain ⟨k', hk'⟩ := exists_blk_cover M' hp
  obtain ⟨a, ha, hz⟩ := hyp p k' hk'
  have hCB := GlobalTheory.T.block_diagonal_minor_vanishing ℂ N j p.2 M.j_le
  have hoff : ∀ J, ¬ IsStepRows N j p.2 J → minorIJ (h p.1) J (stepCols N j p.2) = 0 := fun J hJ =>
    (hCB.2.1 (h p.1) J (hh p.1) hJ).resolve_right (stepCols_ne_empty M.j_le)
  have hdelta : ∀ I' J, IsStepRows N j p.2 I' → IsStepRows N j p.2 J →
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) *
        valAt M'.x (F'.u ⟨k', m'⟩ J) (basePart M'.blk z) = if I' = J then 1 else 0 := by
    intro I' J hI hJ
    have hu' := fun m' : ι' k' => (hG'.2.1 ⟨k', m'⟩ I').2
    have hu := fun m' : ι' k' => (hG'.2.1 ⟨k', m'⟩ J).1
    have e1 := (reg_sum hb Finset.univ (fun m' : ι' k' => F'.u' I' ⟨k', m'⟩ * F'.u ⟨k', m'⟩ J)
      fun m' _ => (reg_mul hb (hu' m') (hu m')).1).2
    rw [hF'.2.2.1 p k' hk' I' J hI hJ] at e1
    rw [Finset.sum_congr rfl fun m' _ => ((reg_mul hb (hu' m') (hu m')).2).symm, ← e1]
    split_ifs
    · exact map_one (regVal M'.x hb)
    · exact map_zero (regVal M'.x hb)
  have hread : ∀ I', IsStepRows N j p.2 I' →
      ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ =
        a * minorIJ (h p.1) I' (stepCols N j p.2) := by
    intro I' hI
    have e1 : ∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) * z ⟨k', m'⟩ =
        a * ∑ J, (∑ m' : ι' k', valAt M'.x (F'.u' I' ⟨k', m'⟩) (basePart M'.blk z) *
          valAt M'.x (F'.u ⟨k', m'⟩ J) (basePart M'.blk z)) * minorIJ (h p.1) J (stepCols N j p.2) := by
      simp_rw [hz, plk, Finset.mul_sum, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun J _ => Finset.sum_congr rfl fun m' _ => ?_
      ring
    rw [e1]
    congr 1
    rw [Finset.sum_eq_single I']
    · rw [hdelta I' I' hI hI, if_pos rfl, one_mul]
    · intro J _ hne
      by_cases hJ : IsStepRows N j p.2 J
      · rw [hdelta I' J hI hJ, if_neg hne.symm, zero_mul]
      · rw [hoff J hJ, mul_zero]
    · simp
  refine ⟨a, ha, fun m => ?_⟩
  rw [img_step Cv F' F z hp hk' m]
  unfold stepCoord plk
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [hCB.1, mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I' _ => ?_
  by_cases hI : IsStepRows N j p.2 I'
  · rw [if_pos hI, hread I' hI]; ring
  · rw [if_neg hI, hoff I' hI, mul_zero, mul_zero]

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptBasesLinearIndependentSpanStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_bases_linearIndependent_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐), ∀ s, LinearIndependent Ω (cc 𝔐 bW bO s) ∧ Submodule.span Ω (Set.range (cc 𝔐 bW bO s)) = VV 𝔐 s := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.GenBases.cc_basis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameChangeDeterminantStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_change_determinant : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.Graph.coordTie_base <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameDegreeFormulaStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_degree_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∀ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → (∀ q : Z, genPt ξ' ⤳ q) → GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) → Smooth f → IsNormalScheme Z := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.flag_total_normal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameLeadingTermStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_leading_term : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → ∃ (Z : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ Z) (f : Z ⟶ 𝔐.X), @CoordTie Z _ _ ℤ _ (Ring.toIntAlgebra _) ξ' _ (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) ∧ (∀ q : Z, genPt ξ' ⤳ q) ∧ GlobalTheory.CompanionTheory.Ar.Dominates ξ' 𝔐.ξ f (algebraMap Ω (GenField Ω (rk (CMType H) D.p D.q))) ∧ Smooth f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.exists_flagTotal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HodgeCptFrameMinorValuationStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeCpt_frame_minor_valuation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n m : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)), FormsOK 𝔐 bW bO m φ → CoordTie ℤ 𝔐.ξ (seg (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → ∀ h : ModelOK (aOf 𝔐 bW bO φ) x₀ m, ∀ (q : Cpt 𝔐.ξ) (F : FrameData (idx (p := D.p) (q := D.q) J₀ n) (CMType H) (D.p + D.q) Ω (blkF (CMType H) D.p D.q K₀)), (model (aOf 𝔐 bW bO φ) x₀ m h).IsFrame F → (model (aOf 𝔐 bW bO φ) x₀ m h).GoodAt F (ptIdeal 𝔐.ξ (xb (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀) q) → ∀ τ, (𝔐.V (.inl τ)).IsFrameAt (colFrame (fun a => (bW τ a : 𝔐.Li)) (wBlock (F.T τ))) q ∧ (omBundle 𝔐 τ).IsFrameAt (colFrame (bO τ) (omBlock (F.T τ))) q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt | exact GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.FMX.FrameAt.isFrameAt_of_goodAt <;> assumption)
end

