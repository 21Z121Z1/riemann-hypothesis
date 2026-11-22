import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0057
import Development.WeilBound.CoreStatements.PluriharmonicCharts.Bundle0013
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ColFlags
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0109
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0104
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0006

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.RefNorm
section
open MvPolynomial Matrix ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc GlobalTheory.CompanionTheory.Ar.PB.CPts GlobalTheory.CompanionTheory.Ar.PB.ValRing
open scoped ComplexOrder Classical

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_hom

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {M : FlagModel y Ψ N j}
variable {Gr : FrameData ι Ψ N M.Ω M.blk → Ψ → ((Σ k, baseIdx ι M.blk k) → ℂ) → Matrix (Fin N) (Fin N) ℂ → Prop}

theorem sum_dy (p : Ψ × Fin N) (L : K → ℝ) :
    ∑ k, (M.dy p k : ℝ) * L k = (M.blk p).elim 0 L - ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * L k'.1 := by
  have e1 : ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * L k'.1 =
      ∑ k, if h : ∀ p', M.blk p' ≠ some k then (M.b p ⟨k, h⟩ : ℝ) * L k else 0 :=
    Fintype.sum_of_injective Subtype.val Subtype.val_injective _ _
      (fun k hk => dif_neg fun h => hk ⟨⟨k, h⟩, rfl⟩) (fun k => by rw [dif_pos k.2])
  have e2 : (M.blk p).elim 0 L = ∑ k, if M.blk p = some k then L k else 0 := by
    cases M.blk p with
    | none => simp
    | some k => simp
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold FlagModel.dy
  by_cases h : ∀ p', M.blk p' ≠ some k
  · rw [dif_pos h, dif_pos h, if_neg (h p)]; simp
  · rw [dif_neg h, dif_neg h]; split_ifs <;> simp

theorem Rel.smul
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (htor : ∀ F τ w G (c : NonPluckerBlocks M.blk → ℂ), (∀ k, c k ≠ 0) → Gr F τ w G → Gr F τ (torusSmul c w) G)
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r : ℝ} (h1 : Rel M Gr p z r) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) :
    Rel M Gr p (torusSmul c z) (r + ∑ k, (M.dy p k : ℝ) * Real.log ‖c k‖) := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨hF, hw, gd, -, -⟩ := hgood _ _ _ _ hG
  have hG' := htor _ _ _ _ (fun k => c k.1) (fun k => hc _) hG
  have eb : basePart M.blk (torusSmul c z) = torusSmul (fun k => c k.1) (basePart M.blk z) := rfl
  have ev : ∀ s, valAt M.x s (basePart M.blk (torusSmul c z)) = valAt M.x s (basePart M.blk z) := fun s =>
    GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.valAt_eq_of_sameOrbit _ _ _ M.x s _ _ (hgood _ _ _ _ hG').2.1
      ⟨fun k => c k.1, fun k => hc _, rfl⟩
  have el : ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk (torusSmul c z) ⟨k', F.c k'⟩‖ =
      ∑ k' : NonPluckerBlocks M.blk, (M.b p k' : ℝ) * Real.log ‖c k'.1‖ +
        ∑ k', (M.b p k' : ℝ) * Real.log ‖basePart M.blk z ⟨k', F.c k'⟩‖ := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eb, torusSmul, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 (ne_of_notMem (gd.1 k)))]
    ring
  refine ⟨F, G, hG', h, bh, dh, t + (M.blk p).elim 0 (fun k => Real.log ‖c k‖), ?_, ?_⟩
  · rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩
    · refine Or.inl ⟨k, c k * a, hk, mul_ne_zero (hc k) ha, fun m => ?_, ?_⟩
      · simp only [ev]
        rw [torusSmul, hz m, mul_assoc]
      · rw [hk, norm_mul, Real.log_mul (norm_ne_zero_iff.2 (hc _)) (norm_ne_zero_iff.2 ha), Option.elim_some, add_comm]
    · refine Or.inr ⟨hk, ?_⟩
      rw [hk, ev, Option.elim_none, add_zero]
  · rw [el, sum_dy]
    ring

theorem Rel.conj
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (hconj : ∀ F τ w G, Gr F τ w G → Gr F τ (conjVec w) (G.map (starRingEnd ℂ)))
    {p : Ψ × Fin N} {z : (Σ k, ι k) → ℂ} {r : ℝ} (h1 : Rel M Gr p z r) : Rel M Gr p (conjVec z) r := by
  obtain ⟨F, G, hG, h, bh, dh, t, ht, rfl⟩ := h1
  obtain ⟨hF, hw, gd, -, -⟩ := hgood _ _ _ _ hG
  have hG' := hconj _ _ _ _ hG
  have hw' := (hgood _ _ _ _ hG').2.1
  have eb : basePart M.blk (conjVec z) = conjVec (basePart M.blk z) := rfl
  refine ⟨F, _, hG', h.map (starRingEnd ℂ), bh.map _, ?_, t, ?_, ?_⟩
  · rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero _).2 dh
  · rcases ht with ⟨k, a, hk, ha, hz, rfl⟩ | ⟨hk, rfl⟩
    · refine Or.inl ⟨k, starRingEnd ℂ a, hk, (map_ne_zero _).2 ha, fun m => ?_, by simp⟩
      rw [conjVec, hz m, map_mul, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun I _ => ?_
      rw [map_mul, eb, valAt_conj hw hw' (gd.2.1 _ I).1, minorIJ_map]
    · refine Or.inr ⟨hk, ?_⟩
      rw [eb, valAt_conj hw hw' (gd.2.2 p hk).2.1, RCLike.norm_conj]
  · rw [pot_conj]
    simp only [eb, conjVec, RCLike.norm_conj]

theorem exists_hom
    (hgood : ∀ F τ w G, Gr F τ w G → M.IsFrame F ∧ w ∈ mcPts (mCoordIdeal M.x) ∧ M.GoodAt F (mCoordIdeal w) ∧
      IsBlockDiag j G ∧ G.PosDef)
    (htor : ∀ F τ w G (c : NonPluckerBlocks M.blk → ℂ), (∀ k, c k ≠ 0) → Gr F τ w G → Gr F τ (torusSmul c w) G)
    (hconj : ∀ F τ w G, Gr F τ w G → Gr F τ (conjVec w) (G.map (starRingEnd ℂ)))
    (hcomp : ∀ F F' τ w G G', Gr F τ w G → Gr F' τ w G' → ∃ Rz : Matrix (Fin N) (Fin N) ℂ,
      (∀ a b, IsValueAt M.x (((F.T τ)⁻¹ * F'.T τ) a b) w (Rz a b)) ∧ Rz.det ≠ 0 ∧ G' = Rzᴴ * G * Rz)
    (p : Ψ × Fin N) : ∃ A : HermLine ι, A.a = M.dy p ∧
      (∀ F w G, Gr F p.1 w G → M.IsInducedAt F w p G A) ∧ ∀ z, A.h (conjVec z) = A.h z := by
  let f : ((Σ k, ι k) → ℂ) → ℝ := fun z =>
    if h : ∃ r, Rel M Gr p z r then Real.exp h.choose else refNorm (M.dy p) z
  have fr : ∀ z r, Rel M Gr p z r → f z = Real.exp r := fun z r h => by
    have hex : ∃ r, Rel M Gr p z r := ⟨r, h⟩
    simp only [f, dif_pos hex]
    rw [Rel.unique hgood hcomp hex.choose_spec h]
  refine ⟨⟨M.dy p, f, fun z hz => ?_, fun c z hc => ?_⟩, rfl, fun F w G hG z hz ho hn h bh dh => ?_, fun z => ?_⟩
  · simp only [f]
    split_ifs
    exacts [Real.exp_pos _, refNorm_pos _ hz]
  · change f (torusSmul c z) = _
    by_cases h : ∃ r, Rel M Gr p z r
    · obtain ⟨r, h⟩ := h
      rw [fr _ _ h, fr _ _ (h.smul hgood htor hc), Real.exp_add, mul_comm, Real.exp_sum]
      congr 1
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Real.log_zpow, Real.exp_log (zpow_pos (norm_pos_iff.2 (hc k)) _)]
    · have h' : ¬ ∃ r, Rel M Gr p (torusSmul c z) r := by
        rintro ⟨r, hr⟩
        have := hr.smul hgood htor (c := fun k => (c k)⁻¹) fun k => inv_ne_zero (hc k)
        have e : torusSmul (fun k => (c k)⁻¹) (torusSmul c z) = z := by
          funext q; simp [torusSmul, hc]
        rw [e] at this
        exact h ⟨_, this⟩
      simp only [f, dif_neg h, dif_neg h']
      exact refNorm_smul _ _ _
  · obtain ⟨c, hc, e⟩ := ho
    have hG' : Gr F p.1 (basePart M.blk z) G := by
      rw [e]; exact htor _ _ _ _ c hc hG
    refine ⟨fun k hk hz => ?_, fun hk => ?_⟩
    · show Real.log (f z) = _
      rw [fr z _ ⟨F, G, hG', h, bh, dh, _, Or.inl ⟨k, 1, hk, one_ne_zero, fun m => by rw [one_mul, hz m], rfl⟩, rfl⟩,
        Real.log_exp]
      simp [hn]
    · show Real.log (f z) = _
      rw [fr z _ ⟨F, G, hG', h, bh, dh, _, Or.inr ⟨hk, rfl⟩, rfl⟩, Real.log_exp]
      simp only [hn, norm_one, Real.log_one, mul_zero, Finset.sum_const_zero]
      ring
  · show f _ = f z
    by_cases h : ∃ r, Rel M Gr p z r
    · obtain ⟨r, h⟩ := h
      rw [fr _ _ h, fr _ _ (h.conj hgood hconj)]
    · have h' : ¬ ∃ r, Rel M Gr p (conjVec z) r := by
        rintro ⟨r, hr⟩
        have := hr.conj hgood hconj
        have e : conjVec (conjVec z) = z := by
          funext q; simp [conjVec]
        rw [e] at this
        exact h ⟨_, this⟩
      simp only [f, dif_neg h, dif_neg h']
      simp [refNorm, conjVec]

end PositivityTheory.Xgp.c_bm_exists_hom
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsChgbasis
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

namespace PositivityTheory.Xgp.c_fm_exists_flags_chgbasis

variable {N : ℕ} {R R' : Type} [CommRing R] [CommRing R']

def Mn (M : Matrix (Fin N) (Fin N) R) : Prop :=
  ∀ (P : Fin N → Prop) (_ : DecidablePred P), (∀ a c, a ≤ c → P c → P a) →
    (M.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val).det ≠ 0

theorem Mn.of_map {M : Matrix (Fin N) (Fin N) R} (f : R →+* R') (h : Mn (M.map f)) : Mn M := fun P i hP h0 =>
  h P i hP (by rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero])

theorem Mn.map {M : Matrix (Fin N) (Fin N) R} (f : R →+* R') (hf : Function.Injective f) (h : Mn M) :
    Mn (M.map f) := fun P i hP h0 => by
  rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det] at h0
  exact h P i hP ((map_eq_zero_iff f hf).1 h0)

theorem Mn.lowerUni [Nontrivial R] {M : Matrix (Fin N) (Fin N) R} (h : IsLowerUni M) : Mn M := fun P _ _ => by
  rw [h.det_submatrix P]
  exact one_ne_zero

theorem Mn.mul [IsDomain R] {M B : Matrix (Fin N) (Fin N) R} (h : Mn M) (hB : B.BlockTriangular id)
    (hd : B.det ≠ 0) : Mn (M * B) := fun P i hP => by
  have e : (M * B).submatrix (Subtype.val : {a // P a} → Fin N) (Subtype.val : {a // P a} → Fin N) =
      M.submatrix (Subtype.val : {a // P a} → Fin N) (Subtype.val : {a // P a} → Fin N) *
        B.submatrix (Subtype.val : {a // P a} → Fin N) (Subtype.val : {a // P a} → Fin N) := by
    ext a b
    rw [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply,
      ← Finset.sum_filter_add_sum_filter_not Finset.univ P,
      Finset.sum_eq_zero (s := Finset.univ.filter fun c => ¬ P c) (fun c hc => by
        rw [hB (show b.1 < c from not_le.1 fun e => (Finset.mem_filter.1 hc).2 (hP _ _ e b.2)), mul_zero]), add_zero,
      Finset.sum_subtype (p := P) _ (by simp)]
    rfl
  rw [e, det_mul]
  refine mul_ne_zero (h P i hP) ?_
  rw [det_of_upperTriangular hB, Finset.prod_ne_zero_iff] at hd
  rw [det_of_upperTriangular (M := B.submatrix (Subtype.val : {a // P a} → Fin N) Subtype.val) fun a b e => hB e,
    Finset.prod_ne_zero_iff]
  exact fun a _ => hd _ (Finset.mem_univ _)

theorem Mn.upper {F : Type} [Field F] {M : Matrix (Fin N) (Fin N) F} (h : Mn M) :
    ∃ B, B.BlockTriangular id ∧ B.det ≠ 0 ∧ IsLowerUni (M * B) := by
  have hb : IsBlockDiag 0 M := fun a b e => absurd (iff_of_true a.2 b.2) e
  obtain ⟨B, -, h1, h2⟩ := hb.exists_upper fun b =>
    (h _ _ fun a c hac hc => ⟨hac.trans hc.1, iff_of_true a.2 b.2⟩).isUnit
  refine ⟨B, h1, fun h0 => ?_, h2⟩
  have := h2.det
  rw [det_mul, h0, mul_zero] at this
  exact zero_ne_one this

theorem exists_low {Ω : Type} [Field Ω] (A : Matrix (Fin N) (Fin N) Ω) (hA : IsUnit A.det) :
    ∃ l : Matrix (Fin N) (Fin N) (FractionRing (Polynomial Ω)), IsLowerUni l ∧
      Mn (A.map (algebraMap Ω (FractionRing (Polynomial Ω))) * l) := by
  let t : Polynomial Ω := Polynomial.X
  let Z : Matrix (Fin N) (Fin N) (Polynomial Ω) := t • (A⁻¹).map Polynomial.C + (1 - t) • (1 : Matrix _ _ _)
  let f := algebraMap (Polynomial Ω) (FractionRing (Polynomial Ω))
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have h1 : Mn Z := by
    refine Mn.of_map (Polynomial.evalRingHom 0) ?_
    have : Z.map (Polynomial.evalRingHom 0) = 1 := by
      ext a b
      by_cases e : a = b <;> simp [Z, t, Matrix.one_apply, e]
    rw [this]
    exact Mn.lowerUni isLowerUni_one
  have h2 : Mn (A.map Polynomial.C * Z) := by
    refine Mn.of_map (Polynomial.evalRingHom 1) ?_
    have e1 : Z.map (Polynomial.evalRingHom 1) = A⁻¹ := by
      ext a b
      simp [Z, t]
    have e2 : (A.map Polynomial.C).map (Polynomial.evalRingHom 1) = A := by
      ext a b
      simp
    rw [Matrix.map_mul, e1, e2, Matrix.mul_nonsing_inv _ hA]
    exact Mn.lowerUni isLowerUni_one
  obtain ⟨B, hB, hd, hl⟩ := (h1.map f hf).upper
  refine ⟨_, hl, ?_⟩
  have := (h2.map f hf).mul hB hd
  rw [Matrix.map_mul, Matrix.mul_assoc] at this
  exact this

variable {S : Type} {r : S → ℕ}

noncomputable def gen (Ω : Type) [Field Ω] (r : S → ℕ) (s : S) : Matrix (Fin (r s)) (Fin (r s))
    (MvPolynomial (Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1}) Ω) := fun a b =>
  if h : b < a then MvPolynomial.X ⟨s, (a, b), h⟩ else if a = b then 1 else 0

theorem gen_map {Ω : Type} [Field Ω] [Algebra Ω R] (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) R)
    (hu : ∀ s, IsLowerUni (u s)) (A : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω) (s : S) :
    ((A s).map MvPolynomial.C * gen Ω r s).map (MvPolynomial.aeval (R := Ω)
      (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2)).toRingHom =
      (A s).map (algebraMap Ω R) * u s := by
  rw [Matrix.map_mul]
  congr 1
  · ext a b
    exact MvPolynomial.aeval_C _ _
  · ext a b
    rw [Matrix.map_apply, gen]
    split_ifs with h e
    · exact MvPolynomial.aeval_X _ _
    · rw [map_one, e, (hu s).1]
    · rw [map_zero, (hu s).2 a b (lt_of_le_of_ne (not_lt.1 h) e)]

end PositivityTheory.Xgp.c_fm_exists_flags_chgbasis

open PositivityTheory.Xgp.c_fm_exists_flags_chgbasis in
theorem PositivityTheory.Xgp.t_c_fm_exists_flags_chgbasis : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (A : ∀ s, Matrix (Fin (r s)) (Fin (r s)) Ω), IsGenFam Ω G u → (∀ s, IsUnit (A s).det) → ∃ u' B : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G, IsGenFam Ω G u' ∧ (∀ s, IsUnit (B s).det) ∧ (∀ s a b, b < a → B s a b = 0) ∧ ∀ s, (A s).map (algebraMap Ω G) * u s = u' s * B s := by
  intro Ω G _ _ _ S _ r u A hu hA
  have hL : ∀ s, IsLowerUni (u s) := fun s => ⟨hu.1 s, hu.2.1 s⟩
  choose l hl hm using fun s => exists_low (A s) (hA s)
  have h1 : ∀ s, Mn ((A s).map (algebraMap Ω G) * u s) := fun s => by
    rw [← gen_map u hL A s]
    refine Mn.map _ hu.2.2.1 ?_
    have := hm s
    rw [← gen_map l hl A s] at this
    exact this.of_map _
  choose B hB hd hl' using fun s => (h1 s).upper
  refine ⟨fun s => (A s).map (algebraMap Ω G) * u s * B s, fun s => (B s)⁻¹, ?_,
    fun s => Matrix.isUnit_nonsing_inv_det _ (hd s).isUnit, fun s a b h => ?_,
    fun s => (Matrix.mul_nonsing_inv_cancel_right _ _ (hd s).isUnit).symm⟩
  · refine PositivityTheory.Xgp.GenFam.of_gen hu (fun s => (hl' s).1) (fun s => (hl' s).2) fun s => ?_
    generalize hF : IntermediateField.adjoin Ω (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) =>
      ((A q.1).map (algebraMap Ω G) * u q.1 * B q.1) q.2.1 q.2.2) = F
    have hmem : ∀ a b, ((A s).map (algebraMap Ω G) * u s * B s) a b ∈ F := fun a b =>
      hF ▸ IntermediateField.subset_adjoin _ _ ⟨⟨s, a, b⟩, rfl⟩
    have e : u s * B s = (A s)⁻¹.map (algebraMap Ω G) * ((A s).map (algebraMap Ω G) * u s * B s) := by
      rw [Matrix.mul_assoc _ (u s), ← Matrix.mul_assoc, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (hA s),
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    have hmem' : ∀ a b, (u s * B s) a b ∈ F := fun a b => by
      rw [e, Matrix.mul_apply]
      exact sum_mem fun c _ => mul_mem (F.algebraMap_mem _) (hmem c b)
    let X₁ : Matrix (Fin (r s)) (Fin (r s)) F := fun a b => ⟨(u s * B s) a b, hmem' a b⟩
    have eX : X₁.map (algebraMap F G) = u s * B s := rfl
    have hX : Mn X₁ := Mn.of_map (algebraMap F G) (eX ▸ (Mn.lowerUni (hL s)).mul (hB s) (hd s))
    obtain ⟨B₁, hB₁, -, hl₁⟩ := hX.upper
    have e₁ : (X₁ * B₁).map (algebraMap F G) = u s * (B s * B₁.map (algebraMap F G)) := by
      rw [Matrix.map_mul, eX, Matrix.mul_assoc]
    have h2 := hl₁.map (algebraMap F G)
    rw [e₁] at h2
    rw [(hL s).eq_one ((hB s).mul (hB₁.map _)) h2, Matrix.mul_one] at e₁
    intro a b
    rw [← e₁]
    exact ((X₁ * B₁) a b).2
  · letI := Matrix.invertibleOfIsUnitDet _ (hd s).isUnit
    exact blockTriangular_inv_of_blockTriangular (hB s) h
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsDegree
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

set_option synthInstance.maxHeartbeats 400000 in
attribute [local instance] MvPolynomial.algebraMvPolynomial in
theorem PositivityTheory.Xgp.c_fm_exists_flags_degree.core {F₀ Ω G I : Type} [Field F₀] [Field Ω] [Field G] [Algebra F₀ Ω]
    [Algebra Ω G] [Algebra F₀ G] [IsScalarTower F₀ Ω G] [Algebra.IsAlgebraic F₀ Ω] (x : I → G)
    (hx : AlgebraicIndependent Ω x) (hx₀ : AlgebraicIndependent F₀ x)
    (ht : IntermediateField.adjoin Ω (Set.range x) = ⊤) :
    Module.finrank (IntermediateField.adjoin F₀ (Set.range x)) G = Module.finrank F₀ Ω := by
  letI : Algebra (FractionRing (MvPolynomial I F₀)) (FractionRing (MvPolynomial I Ω)) :=
    FractionRing.liftAlgebra _ _
  haveI : IsScalarTower (MvPolynomial I F₀) (FractionRing (MvPolynomial I F₀)) (FractionRing (MvPolynomial I Ω)) :=
    FractionRing.isScalarTower_liftAlgebra _ _
  have h := Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial (R := F₀) (S := Ω) I
  rw [Cardinal.lift_id] at h
  have h' : Module.finrank (FractionRing (MvPolynomial I F₀)) (FractionRing (MvPolynomial I Ω)) =
      Module.finrank F₀ Ω := congrArg Cardinal.toNat h
  rw [← h']
  let j : FractionRing (MvPolynomial I Ω) ≃ₐ[Ω] G :=
    hx.aevalEquivField.trans ((IntermediateField.equivOfEq ht).trans IntermediateField.topEquiv)
  have hj : ∀ a, j (algebraMap (MvPolynomial I Ω) _ a) = MvPolynomial.aeval x a :=
    fun a => hx.aevalEquivField_algebraMap_apply_coe a
  refine (Algebra.finrank_eq_of_equiv_equiv hx₀.aevalEquivField.toRingEquiv j.toRingEquiv ?_).symm
  refine IsLocalization.ringHom_ext (nonZeroDivisors (MvPolynomial I F₀)) (RingHom.ext fun a => ?_)
  show ((hx₀.aevalEquivField (algebraMap _ _ a) : _) : G) =
    j (algebraMap (FractionRing (MvPolynomial I F₀)) _ (algebraMap (MvPolynomial I F₀) _ a))
  rw [hx₀.aevalEquivField_algebraMap_apply_coe, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply (MvPolynomial I F₀) (MvPolynomial I Ω), hj]
  exact (MvPolynomial.aeval_map_algebraMap Ω x a).symm

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_degree : ∀ (F₀ Ω G : Type) [Field F₀] [Field Ω] [Field G] [Algebra F₀ Ω] [Algebra Ω G] [Algebra F₀ G] [IsScalarTower F₀ Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (d : ℕ), 0 < d → Module.finrank F₀ Ω = d → IsGenFam Ω G u → AlgebraicIndependent F₀ (fun q : Σ σ, {lk : Fin (r σ) × Fin (r σ) // lk.2 < lk.1} => u q.1 q.2.1.1 q.2.1.2) ∧ Module.finrank (IntermediateField.adjoin F₀ (Set.range fun q : Σ σ, Fin (r σ) × Fin (r σ) => u q.1 q.2.1 q.2.2)) G = d := by
  intro F₀ Ω G _ _ _ _ _ _ _ S _ r u d hd hr hu
  haveI : Module.Finite F₀ Ω := Module.finite_of_finrank_pos (hr ▸ hd)
  have h₀ := hu.2.2.1.restrictScalars (R := F₀) (algebraMap F₀ Ω).injective
  refine ⟨h₀, ?_⟩
  rw [PositivityTheory.Xgp.GenFam.adjoin_low F₀ u hu.1 hu.2.1, ← hr]
  refine PositivityTheory.Xgp.c_fm_exists_flags_degree.core _ hu.2.2.1 h₀ ?_
  rw [← PositivityTheory.Xgp.GenFam.adjoin_low Ω u hu.1 hu.2.1]
  exact hu.2.2.2
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFmExistsFlagsRevgen
section
open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.FMX GlobalTheory.CompanionTheory.Ar.FlagBun GlobalTheory.CompanionTheory.Ar.PB.FMX.GenFl

private theorem revInv_unitriangular_and_mem_of_unitriangular {Ω G : Type} [Field Ω] [Field G] [Algebra Ω G] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) G) (hd : ∀ a, M a a = 1) (hl : ∀ a b, a < b → M a b = 0) :
    (∀ a, revInv M a a = 1) ∧ (∀ a b, a < b → revInv M a b = 0) ∧
      ∀ F : IntermediateField Ω G, (∀ a b, revInv M a b ∈ F) → ∀ a b, M a b ∈ F := by
  classical
  have hup : (Mᵀ).BlockTriangular id := by
    intro i j hij
    rw [Matrix.transpose_apply]
    exact hl j i hij
  have hunit : IsUnit (Mᵀ).det := by
    rw [Matrix.det_of_isUpperTriangular hup]
    simp [Matrix.transpose_apply, hd]
  letI : Invertible (Mᵀ) := Matrix.invertibleOfIsUnitDet _ hunit
  have hup' : (Mᵀ)⁻¹.BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hup
  have hdiag : ∀ i, (Mᵀ)⁻¹ i i = 1 := by
    intro i
    have h1 : ((Mᵀ)⁻¹ * Mᵀ) i i = 1 := by
      rw [Matrix.nonsing_inv_mul _ hunit, Matrix.one_apply_eq]
    rw [Matrix.mul_apply, Finset.sum_eq_single i] at h1
    · simpa [Matrix.transpose_apply, hd] using h1
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hup' h, zero_mul]
      · rw [hup h, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hrev : ∀ a b, revInv M a b = (Mᵀ)⁻¹ a.rev b.rev := fun a b => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rw [hrev]
    exact hdiag _
  · intro a b hab
    rw [hrev]
    exact hup' (Fin.rev_lt_rev.mpr hab)
  · intro F hF a b
    have hmem : ∀ x y, (Mᵀ)⁻¹ x y ∈ F := by
      intro x y
      have := hF x.rev y.rev
      rwa [hrev, Fin.rev_rev, Fin.rev_rev] at this
    have hdet' : IsUnit ((Mᵀ)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hunit
    have := PositivityTheory.Xgp.GenFam.inv_mem F ((Mᵀ)⁻¹) hdet' hmem b a
    rwa [Matrix.nonsing_inv_nonsing_inv _ hunit, Matrix.transpose_apply] at this

theorem PositivityTheory.Xgp.t_c_fm_exists_flags_revgen : ∀ (Ω G : Type) [Field Ω] [Field G] [Algebra Ω G] (S : Type) [Finite S] (r : S → ℕ) (u : ∀ s, Matrix (Fin (r s)) (Fin (r s)) G) (P : S → Prop) [DecidablePred P], IsGenFam Ω G u → IsGenFam Ω G (fun s => if P s then revInv (u s) else u s) := by
  intro Ω G _ _ _ S _ r u P _ hu
  have hu' := hu
  obtain ⟨hd, hl, -, -⟩ := hu'
  have key := fun s => revInv_unitriangular_and_mem_of_unitriangular (Ω := Ω) (u s) (hd s) (hl s)
  refine PositivityTheory.Xgp.GenFam.of_gen hu ?_ ?_ ?_
  · intro s a
    by_cases h : P s
    · rw [if_pos h]
      exact (key s).1 a
    · rw [if_neg h]
      exact hd s a
  · intro s a b hab
    by_cases h : P s
    · rw [if_pos h]
      exact (key s).2.1 a b hab
    · rw [if_neg h]
      exact hl s a b hab
  · intro s a b
    have hsub : ∀ x y, (if P s then revInv (u s) else u s) x y ∈
        IntermediateField.adjoin Ω (Set.range fun (q : (σ : S) × Fin (r σ) × Fin (r σ)) =>
          (if P q.fst then revInv (u q.fst) else u q.fst) q.snd.1 q.snd.2) :=
      fun x y => IntermediateField.subset_adjoin _ _ ⟨⟨s, x, y⟩, rfl⟩
    by_cases h : P s
    · rw [if_pos h] at hsub
      exact (key s).2.2 _ hsub a b
    · rw [if_neg h] at hsub
      exact hsub a b
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XContract
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

theorem PositivityTheory.Xgp.t_contract : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (n : ℕ), (∀ V : Ideal (MRingOver ℚ ι), Nonempty K → IsProjVarF V n → IsArithVar (V.comap (MvPolynomial.map (Int.castRingHom ℚ))) (n + 1) ∧ (V.comap (MvPolynomial.map (Int.castRingHom ℚ))).map (MvPolynomial.map (Int.castRingHom ℚ)) = V) ∧ ∀ P : Ideal (MRing ι), IsArithVar P (n + 1) → IsProjVarF (P.map (MvPolynomial.map (Int.castRingHom ℚ))) n ∧ (P.map (MvPolynomial.map (Int.castRingHom ℚ))).comap (MvPolynomial.map (Int.castRingHom ℚ)) = P := by
  intro K _ ι _ n
  refine ⟨fun V hK hV => ?_, fun P hP => ⟨?_, ?_⟩⟩
  · exact GroundTheory.Heights₂.Heights.HilbertSamuel.NefAmpleGeneric.isArithVar_comap_of_isProjVarF hV
  · exact GroundTheory.Heights₂.Heights.HilbertSamuel.isProjVarF_map_of_isArithVar hP
  · haveI : P.IsPrime := hP.2.1.1
    apply ReciprocityTheory.AnForm.R.IntegerToRational.comap_map_eq
    intro m hm
    have h2 : m ∈ Ideal.comap (C : ℤ →+* MRing ι) P := hm
    rw [hP.2.2.1] at h2
    simpa using h2
end

