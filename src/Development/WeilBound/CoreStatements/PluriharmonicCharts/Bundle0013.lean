import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0012
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkSpecializesBijective
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0005
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0005
import Development.WeilBound.CoreStatements.PluriharmonicCharts.IsBlockMapOmitV
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0104
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.AdjoinLow
section
open Matrix
open GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.GenFam

variable {G : Type} [Field G] {S : Type} {r : S → ℕ}

theorem adjoin_low (F : Type) [Field F] [Algebra F G] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G)
    (h1 : ∀ s a, u s a a = 1) (h0 : ∀ s a b, a < b → u s a b = 0) :
    IntermediateField.adjoin F (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2) =
      IntermediateField.adjoin F
        (Set.range fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) := by
  refine le_antisymm (IntermediateField.adjoin_le_iff.2 ?_) (IntermediateField.adjoin.mono _ _ _ ?_)
  · rintro _ ⟨⟨s, a, b⟩, rfl⟩
    show u s a b ∈ IntermediateField.adjoin F _
    rcases lt_trichotomy a b with h | h | h
    · rw [h0 s a b h]; exact zero_mem _
    · rw [h, h1]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨s, (a, b), h⟩, rfl⟩
  · rintro _ ⟨⟨s, ⟨a, b⟩, h⟩, rfl⟩
    exact ⟨⟨s, a, b⟩, rfl⟩

variable {Ω : Type} [Field Ω] [Algebra Ω G]

theorem of_gen [Finite S] {u v : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G} (hu : IsGenFam Ω G u)
    (h1 : ∀ s a, v s a a = 1) (h0 : ∀ s a b, a < b → v s a b = 0)
    (h : ∀ s a b, u s a b ∈
      IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => v q.1 q.2.1 q.2.2)) :
    IsGenFam Ω G v := by
  have htop : IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => v q.1 q.2.1 q.2.2) = ⊤ := by
    rw [eq_top_iff, ← hu.2.2.2]
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨q, rfl⟩
    exact h _ _ _
  refine ⟨h1, h0, ?_, htop⟩
  rw [adjoin_low Ω v h1 h0] at htop
  haveI : Algebra.IsAlgebraic (Algebra.adjoin Ω (Set.range
      fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => v q.1 q.2.1.1 q.2.1.2)) G := by
    refine IntermediateField.isAlgebraic_adjoin_iff_top.1 ⟨fun x => ?_⟩
    exact isAlgebraic_algebraMap (⟨x, by rw [htop]; trivial⟩ : IntermediateField.adjoin Ω _)
  exact (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω _ hu.2.2.1.cardinalMk_le_trdeg).1

theorem inv_mem {n : ℕ} (F : IntermediateField Ω G) (M : Matrix (Fin n) (Fin n) G) (hd : IsUnit M.det)
    (h : ∀ a b, M a b ∈ F) (a b : Fin n) : M⁻¹ a b ∈ F := by
  let M' : Matrix (Fin n) (Fin n) F := fun a b => ⟨M a b, h a b⟩
  have e : M = M'.map (algebraMap F G) := rfl
  have hd' : IsUnit M'.det := by
    rw [isUnit_iff_ne_zero] at hd ⊢
    intro h0
    apply hd
    rw [e, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero]
  have : M⁻¹ = (M'⁻¹).map (algebraMap F G) := by
    apply Matrix.inv_eq_right_inv
    rw [e, ← Matrix.map_mul, Matrix.mul_nonsing_inv _ hd', Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact (M'⁻¹ a b).2

end PositivityTheory.Xgp.GenFam
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.IsValueAtZpow
section
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

section Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
  {x : (Σ k, ι k) → Ω} {w : (Σ k, ι k) → ℂ}

theorem isValueAt_zpow (hw : w ∈ mcPts (mCoordIdeal x)) {s : Ω} {v : ℂ} (h : IsValueAt x s w v) (hv : v ≠ 0)
    (n : ℤ) : IsValueAt x (s ^ n) w (v ^ n) := by
  have hs : s ≠ 0 := fun h0 => hv (isValueAt_zero hw (h0 ▸ h))
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa using isValueAt_pow h m
  · simpa using isValueAt_pow (isValueAt_inv h hs hv) m

theorem isValueAt_prod {α : Type} (S : Finset α) (f : α → Ω) (v : α → ℂ)
    (h : ∀ i ∈ S, IsValueAt x (f i) w (v i)) : IsValueAt x (∏ i ∈ S, f i) w (∏ i ∈ S, v i) := by
  induction S using Finset.induction_on with
  | empty => simpa using isValueAt_one_self x w
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact isValueAt_mul (h a (Finset.mem_insert_self a S)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem isValueAt_mon (hw : w ∈ mcPts (mCoordIdeal x)) {c c' : ∀ k, ι k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    (hc' : ∀ k, w ⟨k, c' k⟩ ≠ 0) (b : K → ℤ) :
    IsValueAt x ((∏ k, x ⟨k, c k⟩ ^ b k) / ∏ k, x ⟨k, c' k⟩ ^ b k) w (∏ k, (w ⟨k, c k⟩ / w ⟨k, c' k⟩) ^ b k) := by
  rw [← Finset.prod_div_distrib]
  refine isValueAt_prod _ _ _ fun k _ => ?_
  rw [← div_zpow]
  exact isValueAt_zpow hw (isValueAt_ratio (coord_ne hw (hc' k)) (hc' k)) (div_ne_zero (hc k) (hc' k)) _

theorem log_mon {c c' : ∀ k, ι k} (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (hc' : ∀ k, w ⟨k, c' k⟩ ≠ 0) (b : K → ℤ) :
    Real.log ‖∏ k, (w ⟨k, c k⟩ / w ⟨k, c' k⟩) ^ b k‖ =
      ∑ k, (b k : ℝ) * Real.log ‖w ⟨k, c k⟩‖ - ∑ k, (b k : ℝ) * Real.log ‖w ⟨k, c' k⟩‖ := by
  rw [norm_prod, Real.log_prod fun k _ => norm_ne_zero_iff.2 (zpow_ne_zero _ (div_ne_zero (hc k) (hc' k))),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [norm_zpow, Real.log_zpow, norm_div, Real.log_div (norm_ne_zero_iff.2 (hc k)) (norm_ne_zero_iff.2 (hc' k))]
  ring

theorem ne_of_notMem {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal w) : w q ≠ 0 := fun h0 => h (by
  show mConeMap w (X q) = 0
  rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

theorem eval_conj (z : (Σ k, ι k) → ℂ) (f : MRing ι) :
    eval (conjVec z) (map (Int.castRingHom ℂ) f) = starRingEnd ℂ (eval z (map (Int.castRingHom ℂ) f)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  exact congrArg (fun g => MvPolynomial.eval₂ g _ f) (RingHom.ext_int _ _)

theorem isValueAt_conj {s : Ω} {v : ℂ} (h : IsValueAt x s w v) : IsValueAt x s (conjVec w) (starRingEnd ℂ v) := by
  obtain ⟨d, g, f, hg, hf, hy, heq, hz0, rfl⟩ := h
  refine ⟨d, g, f, hg, hf, hy, heq, ?_, ?_⟩
  · rw [eval_conj]; exact (map_ne_zero _).2 hz0
  · rw [eval_conj, eval_conj, map_div₀]

theorem valAt_conj (hw : w ∈ mcPts (mCoordIdeal x)) (hw' : conjVec w ∈ mcPts (mCoordIdeal x)) {s : Ω}
    (hs : RegAt x (mCoordIdeal w) s) : valAt x s (conjVec w) = starRingEnd ℂ (valAt x s w) := by
  obtain ⟨v, hv⟩ := exists_isValueAt hw hs
  rw [valAt_eq hw hv, valAt_eq hw' (isValueAt_conj hv)]

end Val

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} (M : FlagModel y Ψ N j)

theorem change_gen {F F' : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) (hF' : M.IsFrame F') {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) (m : ι k) {I' : Finset (Fin N)} (hI : IsStepRows N j p.2 I') :
    detFac j p.2 ((F.T p.1)⁻¹ * F'.T p.1) * (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') *
      ∑ I, F.u ⟨k, m⟩ I * minorIJ ((F.T p.1)⁻¹ * F'.T p.1) I I' =
      (∏ k', M.x ⟨k', F'.c k'⟩ ^ M.b p k') * F'.u ⟨k, m⟩ I' := by
  obtain ⟨h, bh, hh⟩ := exists_selector M.Ω M.j_le p.2 hI
  have hu : IsUnit (F.T p.1).det := (hF.1 p.1).2.isUnit
  set R := (F.T p.1)⁻¹ * F'.T p.1 with hR
  have bR : IsBlockDiag j R := ((hF.1 p.1).1.inv hu).mul (hF'.1 p.1).1
  have eT : F'.T p.1 = F.T p.1 * R := by rw [hR, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have e1 := hF.2.1 p k hp m (R * h) (bR.mul bh)
  have e2 := hF'.2.1 p k hp m h bh
  have e3 : ∀ I, minorIJ (R * h) I (stepCols N j p.2) = minorIJ R I I' := fun I => by
    rw [minorIJ_mul]; simp [hh]
  simp only [e3] at e1
  rw [eT, detFac_mul _ bR, Matrix.mul_assoc] at e2
  simp only [hh, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at e2
  linear_combination e2 - detFac j p.2 R * e1

theorem change_base {F F' : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) (hF' : M.IsFrame F') {p : Ψ × Fin N}
    (hp : M.blk p = none) :
    detFac j p.2 ((F.T p.1)⁻¹ * F'.T p.1) * (∏ k', M.x ⟨k', F.c k'⟩ ^ M.b p k') * F.υ p =
      (∏ k', M.x ⟨k', F'.c k'⟩ ^ M.b p k') * F'.υ p := by
  have hu : IsUnit (F.T p.1).det := (hF.1 p.1).2.isUnit
  set R := (F.T p.1)⁻¹ * F'.T p.1 with hR
  have bR : IsBlockDiag j R := ((hF.1 p.1).1.inv hu).mul (hF'.1 p.1).1
  have eT : F'.T p.1 = F.T p.1 * R := by rw [hR, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  have e1 := hF.2.2.2 p hp
  have e2 := hF'.2.2.2 p hp
  rw [eT, detFac_mul _ bR] at e2
  linear_combination e2 - detFac j p.2 R * e1

theorem left_inv_val {F : FrameData ι Ψ N M.Ω M.blk} (hF : M.IsFrame F) {w : (Σ k, baseIdx ι M.blk k) → ℂ}
    (hw : w ∈ mcPts (mCoordIdeal M.x)) (hG : M.GoodAt F (mCoordIdeal w)) {p : Ψ × Fin N} {k : K}
    (hp : M.blk p = some k) {f : Matrix (Fin N) (Fin N) ℂ} (bf : IsBlockDiag j f) {I : Finset (Fin N)}
    (hI : IsStepRows N j p.2 I) :
    ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) w * ∑ I', valAt M.x (F.u ⟨k, m⟩ I') w * minorIJ f I' (stepCols N j p.2) =
      minorIJ f I (stepCols N j p.2) := by
  let uA : (Σ k, ι k) → Finset (Fin N) → regRing M.x w := fun q I => ⟨F.u q I, exists_isValueAt hw (hG.2.1 q I).1⟩
  let vA : Finset (Fin N) → (Σ k, ι k) → regRing M.x w := fun I q => ⟨F.u' I q, exists_isValueAt hw (hG.2.1 q I).2⟩
  have rel : ∀ I', IsStepRows N j p.2 I' →
      ∑ m : ι k, valAt M.x (F.u' I ⟨k, m⟩) w * valAt M.x (F.u ⟨k, m⟩ I') w = if I = I' then 1 else 0 := fun I' hI' => by
    have e : ∑ m : ι k, vA I ⟨k, m⟩ * uA ⟨k, m⟩ I' = if I = I' then 1 else 0 := by
      apply Subtype.ext
      have := hF.2.2.1 p k hp I I' hI hI'
      split_ifs at this ⊢ <;> simpa [uA, vA] using this
    have e' := congrArg (regVal hw) e
    rw [map_sum] at e'
    simp only [map_mul] at e'
    refine e'.trans ?_
    split_ifs <;> simp
  simp only [Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul]
  rw [Finset.sum_eq_single I]
  · rw [rel I hI, if_pos rfl, one_mul]
  · intro I' _ hne
    by_cases h : IsStepRows N j p.2 I'
    · rw [rel I' h, if_neg hne.symm, zero_mul]
    · rw [minor_stepCols_eq_zero M.j_le f I' bf h, mul_zero]
  · simp

def Rel (Gr : FrameData ι Ψ N M.Ω M.blk → Ψ → ((Σ k, baseIdx ι M.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop)
    (p : Ψ × Fin N) (z : (Σ k, ι k) → ℂ) (r : ℝ) : Prop :=
  ∃ F G, Gr F p.1 (basePart M.blk z) G ∧ ∃ h : Matrix (Fin N) (Fin N) ℂ, IsBlockDiag j h ∧ h.det ≠ 0 ∧ ∃ t : ℝ,
    ((∃ k a, M.blk p = some k ∧ a ≠ 0 ∧ (∀ m : ι k, z ⟨k, m⟩ =
        a * ∑ I, valAt M.x (F.u ⟨k, m⟩ I) (basePart M.blk z) * minorIJ h I (stepCols N j p.2)) ∧ t = Real.log ‖a‖) ∨
      (M.blk p = none ∧ t = -Real.log ‖valAt M.x (F.υ p) (basePart M.blk z)‖)) ∧
    r = t + blockPot j p.2 G h - ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk z ⟨k', F.c k'⟩‖

variable {M}
variable {Gr : FrameData ι Ψ N M.Ω M.blk → Ψ → ((Σ k, baseIdx ι M.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop}

theorem Rel.unique
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (hcomp : ∀ F F' τ w G G', Gr F τ w G → Gr F' τ w G' → ∃ Rz : Matrix (Fin N) (Fin N) ℂ,
      (∀ a b, IsValueAt M.x (((F.T τ)⁻¹ * F'.T τ) a b) w (Rz a b)) ∧ Rz.det ≠ 0 ∧ G' = Rzᴴ * G * Rz)
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r r' : ℝ} (h1 : Rel M Gr p z r) (h2 : Rel M Gr p z r') : r = r' := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨F', G', hG', h', bh', dh', t', ht', rfl⟩ := h2
  obtain ⟨Rz, hRz, dR, rfl⟩ := hcomp _ _ _ _ _ _ hG hG'
  obtain ⟨hF, hw, gd, bG, pG⟩ := hgood _ _ _ _ hG
  obtain ⟨hF', -, gd', -, -⟩ := hgood _ _ _ _ hG'
  generalize basePart M.blk z = w at *
  have hc : ∀ k, w ⟨k, F.c k⟩ ≠ 0 := fun k => ne_of_notMem (gd.1 k)
  have hc' : ∀ k, w ⟨k, F'.c k⟩ ≠ 0 := fun k => ne_of_notMem (gd'.1 k)
  have hμ := isValueAt_mon hw hc hc' (M.b p)
  have lμ := log_mon hc hc' (M.b p)
  have μ0 : (∏ k, (w ⟨k, F.c k⟩ / w ⟨k, F'.c k⟩) ^ M.b p k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (div_ne_zero (hc k) (hc' k))
  have m0 : (∏ k, M.x ⟨k, F'.c k⟩ ^ M.b p k) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (coord_ne hw (hc' k))
  generalize (∏ k, (w ⟨k, F.c k⟩ / w ⟨k, F'.c k⟩) ^ M.b p k) = μ at *
  let RA : Matrix (Fin N) (Fin N) (regRing M.x w) := Matrix.of fun a b => ⟨_, _, hRz a b⟩
  let μA : regRing M.x w := ⟨_, _, hμ⟩
  have eμ : regVal hw μA = μ := valAt_eq hw hμ
  have e1 : RA.map (regRing M.x w).subtype = (F.T p.1)⁻¹ * F'.T p.1 := by ext a b; rfl
  have e2 : RA.map (regVal hw) = Rz := by ext a b; exact valAt_eq hw (hRz a b)
  have bR : IsBlockDiag j Rz := by
    have : IsBlockDiag j RA := fun a b hab =>
      Subtype.ext ((((hF.1 p.1).1.inv (hF.1 p.1).2.isUnit).mul (hF'.1 p.1).1) a b hab)
    exact e2 ▸ this.map _
  rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩ <;> rcases ht' with ⟨k', a', hk', ha', hz', rfl⟩ | ⟨hk', rfl⟩
  · obtain rfl : k = k' := Option.some.inj (hk.symm.trans hk')
    have hi : IsProperStep N j p.2 := by
      by_contra hn
      rw [(M.blk_none p).2 hn] at hk
      cases hk
    have ch : ∀ m I', IsStepRows N j p.2 I' → detFac j p.2 Rz * μ *
        ∑ I, valAt M.x (F.u ⟨k, m⟩ I) w * minorIJ Rz I I' = valAt M.x (F'.u ⟨k, m⟩ I') w := by
      intro m I' hI'
      let uA : Finset (Fin N) → regRing M.x w := fun I => ⟨F.u ⟨k, m⟩ I, exists_isValueAt hw (gd.2.1 _ I).1⟩
      let vA : regRing M.x w := ⟨F'.u ⟨k, m⟩ I', exists_isValueAt hw (gd'.2.1 _ I').1⟩
      have e : detFac j p.2 RA * μA * ∑ I, uA I * minorIJ RA I I' = vA := by
        apply (regRing M.x w).subtype_injective
        simp only [map_mul, map_sum, ← detFac_map, ← minorIJ_map, e1]
        have := change_gen M hF hF' hk m hI'
        show _ * (_ / _) * ∑ I, F.u ⟨k, m⟩ I * _ = F'.u ⟨k, m⟩ I'
        rw [← mul_div_assoc, div_mul_eq_mul_div, this, mul_div_cancel_left₀ _ m0]
      have e' := congrArg (regVal hw) e
      simp only [map_mul, map_sum, ← detFac_map, ← minorIJ_map, e2, eμ] at e'
      exact e'
    have ch2 : ∀ m, ∑ I, valAt M.x (F'.u ⟨k, m⟩ I) w * minorIJ h' I (stepCols N j p.2) = detFac j p.2 Rz * μ *
        ∑ I, valAt M.x (F.u ⟨k, m⟩ I) w * minorIJ (Rz * h') I (stepCols N j p.2) := by
      intro m
      simp only [minorIJ_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun I' _ => ?_
      by_cases hs : IsStepRows N j p.2 I'
      · rw [← ch m I' hs, Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun I _ => by ring
      · simp [minor_stepCols_eq_zero M.j_le h' I' bh' hs]
    have fin : ∀ I, a * minorIJ h I (stepCols N j p.2) =
        a' * detFac j p.2 Rz * μ * minorIJ (Rz * h') I (stepCols N j p.2) := by
      intro I
      by_cases hs : IsStepRows N j p.2 I
      · rw [← left_inv_val M hF hw gd hk bh hs, ← left_inv_val M hF hw gd hk (bR.mul bh') hs, Finset.mul_sum,
          Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        have := (hz m).symm.trans (hz' m)
        rw [ch2] at this
        linear_combination (valAt M.x (F.u' I ⟨k, m⟩) w) * this
      · rw [minor_stepCols_eq_zero M.j_le h I bh hs, minor_stepCols_eq_zero M.j_le _ I (bR.mul bh') hs]
        simp
    have := pot_step M.j_le p.2 hi pG bG bR dR dh dh' ha ha' μ0 fin
    linarith
  · rw [hk] at hk'; cases hk'
  · rw [hk] at hk'; cases hk'
  · have hi := (M.blk_none p).1 hk
    obtain ⟨v, hv⟩ := exists_isValueAt hw (gd.2.2 p hk).2.1
    obtain ⟨v', hv'⟩ := exists_isValueAt hw (gd.2.2 p hk).2.2
    have v0 : v ≠ 0 := by
      have := isValueAt_mul hv hv'
      rw [mul_inv_cancel₀ (gd.2.2 p hk).1] at this
      have e := (valAt_eq hw this).symm.trans (valAt_eq hw (isValueAt_one_self M.x w))
      exact left_ne_zero_of_mul_eq_one e
    let uA : regRing M.x w := ⟨F.υ p, v, hv⟩
    let vA : regRing M.x w := ⟨F'.υ p, exists_isValueAt hw (gd'.2.2 p hk).2.1⟩
    have e : detFac j p.2 RA * μA * uA = vA := by
      apply (regRing M.x w).subtype_injective
      simp only [map_mul, ← detFac_map, e1]
      have := change_base M hF hF' hk
      show _ * (_ / _) * F.υ p = F'.υ p
      rw [← mul_div_assoc, div_mul_eq_mul_div, this, mul_div_cancel_left₀ _ m0]
    have e' := congrArg (regVal hw) e
    simp only [map_mul, ← detFac_map, e2, eμ] at e'
    have e'' : detFac j p.2 Rz * μ * v = valAt M.x (F'.υ p) w := by
      rw [← valAt_eq hw hv]; exact e'
    have d0 := detFac_ne_zero M.j_le p.2 bR dR
    rw [pot_base M.j_le p.2 hi h h' pG bG bR dR, ← e'', valAt_eq hw hv, norm_mul, norm_mul,
      Real.log_mul (mul_ne_zero (norm_ne_zero_iff.2 d0) (norm_ne_zero_iff.2 μ0)) (norm_ne_zero_iff.2 v0),
      Real.log_mul (norm_ne_zero_iff.2 d0) (norm_ne_zero_iff.2 μ0)]
    linarith

end PositivityTheory.Xgp.c_bm_exists_hom
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsCharts
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

private theorem stalkClosedPointTo_specMap_comp_eq {X : Scheme.{0}} {Ω G : Type} [Field Ω] [Field G]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* G) :
    ∃ e : (Spec.map (CommRingCat.ofHom i) ≫ ξ) (IsLocalRing.closedPoint G) = ξ (IsLocalRing.closedPoint Ω),
      Scheme.stalkClosedPointTo (Spec.map (CommRingCat.ofHom i) ≫ ξ) =
        (X.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i := by
  have hξ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have hi : IsLocalHom i := ⟨fun a ha => isUnit_iff_ne_zero.mpr (fun h0 => by simp [h0] at ha)⟩
  have hloc : IsLocalHom (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i).hom := by
    rw [CommRingCat.hom_comp]
    infer_instance
  have key := (SpecToEquivOfLocalRing X (CommRingCat.of G)).right_inv
    ⟨_, Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i, hloc⟩
  rw [SpecToEquivOfLocalRing_eq_iff] at key
  obtain ⟨h1, h2⟩ := key
  change (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) (IsLocalRing.closedPoint G) = ξ (IsLocalRing.closedPoint Ω) at h1
  change Scheme.stalkClosedPointTo (Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω))) = (X.presheaf.stalkCongr (Inseparable.of_eq h1)).hom ≫
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i at h2
  have hg : Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
      X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = Spec.map (CommRingCat.ofHom i) ≫ ξ := by
    rw [Spec.map_comp, Category.assoc, hξ]
  revert h1 h2
  generalize Spec.map (Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom i) ≫
    X.fromSpecStalk (ξ (IsLocalRing.closedPoint Ω)) = k at hg
  subst hg
  intro h1 h2
  exact ⟨h1, h2⟩

private theorem stalkClosedPointTo_stalkSpecializes_comp {X : Scheme.{0}} {Ω G : Type} [Field Ω] [Field G]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (i : Ω →+* G) (g : Spec (CommRingCat.of G) ⟶ X)
    (hg : g = Spec.map (CommRingCat.ofHom i) ≫ ξ) (y : X) (hy : g (IsLocalRing.closedPoint G) ⤳ y)
    (h : ξ (IsLocalRing.closedPoint Ω) ⤳ y) (s : X.presheaf.stalk y) :
    (Scheme.stalkClosedPointTo g).hom ((X.presheaf.stalkSpecializes hy).hom s) =
      i ((Scheme.stalkClosedPointTo ξ).hom ((X.presheaf.stalkSpecializes h).hom s)) := by
  subst hg
  obtain ⟨e, he⟩ := stalkClosedPointTo_specMap_comp_eq ξ i
  rw [he]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, TopCat.Presheaf.stalkCongr_hom, CommRingCat.hom_ofHom]
  congr 2
  have hh := TopCat.Presheaf.stalkSpecializes_comp X.presheaf (Inseparable.of_eq e.symm).specializes hy
  exact congrArg (fun k => CommRingCat.Hom.hom k s) hh

theorem PositivityTheory.Xgp.inChart_iff_inChart_map_of_dominates : ∀ (X X' : Scheme.{0}) (Ω G : Type) [Field Ω] [Field G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ξ' : Spec (CommRingCat.of G) ⟶ X') (f : X' ⟶ X) (i : Ω →+* G) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → ∀ (p' : Cpt ξ') (c₁ : κ) (h : genPt ξ ⤳ f p'.1), InChart ξ x c₁ ⟨f p'.1, h⟩ ↔ InChart ξ' (fun k => i (x k)) c₁ p' := by
  intro X X' Ω G _ _ ξ ξ' f i κ x hT hG' hD p' c₁ h
  set q : Cpt ξ := ⟨f p'.1, h⟩ with hq
  have K : ∀ s : X.presheaf.stalk (f p'.1), genMap ξ' p' ((f.stalkMap p'.1).hom s) = i (genMap ξ q s) := by
    intro s
    have e1 := stalkClosedPointTo_stalkSpecializes_comp ξ i (ξ' ≫ f) hD (f p'.1) (f.base.hom.map_specializes p'.2) h s
    rw [Scheme.stalkClosedPointTo_comp] at e1
    exact (congrArg (Scheme.stalkClosedPointTo ξ').hom
      (Scheme.Hom.stalkSpecializes_stalkMap_apply f _ _ p'.2 s).symm).trans e1
  have F1 : ∀ a, a ∈ regAt ξ q → i a ∈ regAt ξ' p' := by
    intro a ha
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    exact RingHom.mem_range.mpr ⟨_, K s⟩
  have F2 : ∀ a, a ∈ regAt ξ q → (i a)⁻¹ ∈ regAt ξ' p' → a⁻¹ ∈ regAt ξ q := by
    intro a ha hinv
    obtain ⟨s, rfl⟩ := RingHom.mem_range.mp ha
    obtain ⟨t, ht⟩ := RingHom.mem_range.mp hinv
    by_cases h0 : genMap ξ q s = 0
    · rw [h0, _root_.inv_zero]
      exact zero_mem _
    have hu : IsUnit ((f.stalkMap p'.1).hom s) := by
      have hm : (f.stalkMap p'.1).hom s * t = 1 := by
        apply hG'.inj p'
        rw [map_mul, map_one, K, ht, mul_inv_cancel₀ ((map_ne_zero i).mpr h0)]
      exact isUnit_iff_exists_inv.mpr ⟨t, hm⟩
    obtain ⟨v, hv⟩ := (isUnit_map_iff (f.stalkMap p'.1).hom s).mp hu
    refine RingHom.mem_range.mpr ⟨↑v⁻¹, ?_⟩
    rw [← hv, map_units_inv]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(map_ne_zero i).mpr h1, fun c' => ?_⟩
    show i (x c') / i (x c₁) ∈ regAt ξ' p'
    rw [← map_div₀]
    exact F1 _ (h2 c')
  · rintro ⟨h1, h2⟩
    have h1' : x c₁ ≠ 0 := fun h0 => h1 (by simp [h0])
    obtain ⟨c, hc⟩ := hT.cover q
    obtain ⟨hc0, hc⟩ := hc
    refine ⟨h1', fun c' => ?_⟩
    have hinv : (i (x c₁ / x c))⁻¹ ∈ regAt ξ' p' := by
      rw [map_div₀, inv_div]
      exact h2 c
    have hw := F2 _ (hc c₁) hinv
    have e : x c' / x c₁ = (x c' / x c) * (x c₁ / x c)⁻¹ := by
      field_simp
    rw [e]
    exact mul_mem (hc c') hw
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsField
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω Ω' : Type) [Field Ω] [Field Ω'] (K K' : Type) [Fintype K] [Fintype K'] (J : K → Type) (J' : K' → Type) (x : (Σ k, J k) → Ω) (x' : (Σ k, J' k) → Ω') (A : HodgeCpt Y S x) (A' : HodgeCpt Y S x') (h : A'.X ⟶ A.X) (i : Ω →+* Ω') (j : A.Li →+ A'.Li) (d : ℕ), HodgeOver A' A h i j → A.IsCover d → ∃ ι : A'.Ω₀ →+* Ω, i.comp ι = A'.fn ∧ GlobalTheory.CompanionTheory.Ar.Dominates A.ξ A'.ξ₀ A.f ι ∧ letI := ι.toAlgebra; Module.finrank A'.Ω₀ Ω = d := by
  intro E _ _ _ H D l Xo c Y S Ω Ω' _ _ K K' _ _ J J' x x' A A' h i j d hov hcov
  obtain ⟨hd, hf, -⟩ := hov
  have hgen : genPt A'.ξ₀ = genPt A.ξ₀ := by
    have h1 := RegAtDom.map_genPt hd
    have h2 := RegAtDom.map_genPt A.fn_over
    have h3 := RegAtDom.map_genPt A'.fn_over
    rw [← h2, ← h3, ← h1, hf]
    rfl
  obtain ⟨ψ, hψ⟩ := FlagPull.exists_iso A'.gen₀ A.gen₀ hgen
  have e1 : spMap A'.fn ≫ A'.ξ₀ = A'.ξ ≫ A'.f := A'.fn_over.symm
  have e2 : spMap A.fn ≫ A.ξ₀ = A.ξ ≫ A.f := A.fn_over.symm
  have e3 : A'.ξ ≫ h = spMap i ≫ A.ξ := hd
  have e5 : spMap (A.fn.comp ψ.toRingHom) ≫ A'.ξ₀ = A.ξ ≫ A.f := by
    rw [FlagPull.spMap_comp, Category.assoc, hψ, e2]
  refine ⟨A.fn.comp ψ.toRingHom, ?_, e5.symm, ?_⟩
  · haveI := FlagPull.mono_of_isCptGen A'.gen₀
    have e4 : spMap (i.comp (A.fn.comp ψ.toRingHom)) = spMap A'.fn := by
      refine (cancel_mono A'.ξ₀).1 ?_
      rw [FlagPull.spMap_comp, Category.assoc, e5, e1, hf, ← Category.assoc, ← e3, Category.assoc]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective e4)
  · letI := A.fn.toAlgebra
    letI := (A.fn.comp ψ.toRingHom).toAlgebra
    exact (Algebra.finrank_eq_of_equiv_equiv ψ (RingEquiv.refl Ω) (RingHom.ext fun _ => rfl)).trans hcov.2
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsTie
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_tie : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K₀ : Type) [Fintype K₀] (J₀ : K₀ → Type) [∀ k, Fintype (J₀ k)] (x₀ : (Σ k, J₀ k) → Ω) (𝔐 : HodgeCpt Y S x₀) (bW : WBases 𝔐) (bO : OmBases 𝔐) (n : CMType H ⊕ CMType H → ℕ) (φ : ∀ s, Fin (n s) → Module.Dual Ω (EE 𝔐)) (X' : Scheme.{0}) (ξ' : Spec (CommRingCat.of (GenField Ω (rk (CMType H) D.p D.q))) ⟶ X'), CoordTie ℤ ξ' (seg (yv (p := D.p) (q := D.q) (aOf 𝔐 bW bO φ) x₀)) → CoordTie ℤ ξ' (flagCoord ((k : K₀) → J₀ k) (seg x₀) φ (cc 𝔐 bW bO)) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K₀ _ J₀ _ x₀ 𝔐 bW bO n φ X' ξ' h
  let e : FlagIx ((k : K₀) → J₀ k) n (rk (CMType H) D.p D.q) ≃
      ((k : K₀ ⊕ StepIx (CMType H) D.p D.q) → idx J₀ n k) :=
    (Equiv.sumPiEquivProdPi (idx J₀ n)).symm
  have h2 := coordTie_comp_equiv h e
  convert h2 using 1
  funext cJ
  obtain ⟨c0, c1⟩ := cJ
  change _ = seg (yv (aOf 𝔐 bW bO φ) x₀) (e (c0, c1))
  simp only [seg, flagCoord, Fintype.prod_sum_type, map_prod]
  congr 1
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XTopFlh
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_top_flh : FlagHeight := by
  intro hI II hII Ψ _ _ _ N hN
  exact ⟨(GlobalTheory.CompanionTheory.Ar.PB.formPoly_isHomogeneous_and_eval _ _ _).1, PositivityTheory.Xgp.block_hermitian_pullback.flZero_main hI II hII Ψ N hN,
    PositivityTheory.Xgp.block_hermitian_pullback.flHeight_nonneg_dominant hI II hII Ψ N hN⟩
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.X_deg_generic
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_deg_generic : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : IFamily ℚ ι), IsFieldIntersection I → ∀ (D : ℕ) (P : Ideal (MRing ι)) (L : Fin D → HermLine ι), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (pot L) (fun _ => 1) = (I (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D fun j => (L j).a : ℤ) := by
  intro hI K _ ι _ I hF D P L hP hL
  classical
  obtain ⟨I₀, -, hu⟩ := GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full ℚ ι
  have hQ := GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hP
  have h1 := hu I hF _ D (fun j => (L j).a) hQ
  have h2 := hu _ (GroundTheory.Heights₂.Heights.NumbersDVR.IntNumIsFieldIntersection.full ℚ K ι) _ D (fun j => (L j).a) hQ
  rw [h1, ← h2]
  exact GlobalTheory.CompanionTheory.Ar.Giv.degreeGeneric_of_degree hI.degree K ι P D L hP hL
end

