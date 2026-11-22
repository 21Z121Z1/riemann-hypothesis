import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0403
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0511
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0933
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0688
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0423
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0452
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0406
import Development.AutomorphicArithmetic.CyclotomicBounds.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0907
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0915
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0928
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0927
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0929
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CocycleExtensionTwistedWeilCoefficientsAdmissibl
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SecEqZeroOfComplex
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MarkedIsometryHalf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0935
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0934

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TheoremBOfAdmittedHypotheses
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TheoremB

theorem placesOver_finite (E : Type) [Field E] [NumberField E] (p : ℕ) (hp : p ≠ 0) :
    (placesOver E p).Finite := by
  have h0 : Ideal.span {((p : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  show v.asIdeal ∣ _
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

theorem declNoColumns : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∃ dc : TruncatedSeriesCountingIdentities.Decl D i, dc.col = ∅ := by
  intro D i _
  have hf := placesOver_finite D.host.E (D.nd.l i) (D.nd.lPrime i).out.ne_zero
  exact ⟨⟨hf.toFinset, ∅, Finset.disjoint_empty_right _, fun v => by simp⟩, rfl⟩

theorem localDelta_le_cuspTwistDepth : ∀ (D : D7) (i : D.nd.Loc), (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.vdel i ≤ (D.R.t : ℚ) := by
  intro D i hl
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have htr : D.R.t ≤ D.R.t * D.R.r := Nat.le_mul_of_pos_right _ hr1
  have h4 : 4 * D.R.t * D.R.r = 4 * (D.R.t * D.R.r) := by ring
  have hlt : D.R.t < D.nd.l i := by
    rcases hl with h | h <;> rw [h]
    · have := D.host.qd_big.1; rw [h4] at this; omega
    · have := D.host.qd_big.2; rw [h4] at this; omega
  have hl2 : D.nd.l i ≠ 2 := by have := D.R.rank_add_five_le; omega
  unfold NData.vdel
  rw [UpperTheory.Small.localLevel_eq_one_of_not_mem_smallPrimes D.nd i (UpperTheory.Small.not_mem_of_qd D.host hl)]
  have hk : ∀ k ∈ Finset.Ioo 0 D.R.t, ((1 : ℕ) : ℚ) + (padicValNat (D.nd.l i) k : ℚ) = 1 := by
    intro k hk
    rw [Finset.mem_Ioo] at hk
    rw [padicValNat.eq_zero_of_not_dvd (Nat.not_dvd_of_pos_of_lt hk.1 (by omega))]
    simp
  rw [Finset.sum_congr rfl hk]
  simp

theorem rowBound : ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA : ℝ), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∀ dc : TruncatedSeriesCountingIdentities.Decl D i, ∃ lenRow : HeightOneSpectrum (𝓞 D.host.E) → ℚ, TruncatedSeriesCountingIdentities.LengthBoundAtPlaces i (r i) (ρ i) π dc lenRow ∧ ∀ w ∈ dc.row, (lenRow w : ℝ) ≤ max CA 0 * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * (4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ)) + 3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * (2 * large₂.sc.b + 1)) + 1 := GlobalTheory.T.rowPlaces_satisfy_rowHypothesis_at_q_and_d

theorem tbConst : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool), EmbeddingTypeJumps.Conclusion0 D → EmbeddingTypeJumps.Conclusion1 D → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, ∃ cB : ℕ, TruncatedSeriesCountingIdentities.admTB i (r i) π cB ∧ (cB : ℝ) ≤ 60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b := GlobalTheory.T.blockBound_qd_places_uniformConst

theorem bkAt : ∀ (D : D7), EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.admBK i := GlobalTheory.T.blochKatoHypothesis_globalStep_at_qd

theorem cycDegree_gt : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.R.t * D.R.r < Module.finrank D.host.E (CyclotomicField (D.nd.l i) D.host.E) := GlobalTheory.T.mul_lt_finrank_cyclotomic_at_q_and_d

theorem ne_typePrimes : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → D.nd.l i ≠ D.host.g 0 ∧ D.nd.l i ≠ D.host.g 1 := GlobalTheory.T.theoremB_ramifiedPrimes_ne_typePrimes

theorem degBounds : ∀ (D : D7), EmbeddingTypeJumps.Conclusion1 D → ∀ i : D.nd.Loc, (D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) → ∀ s : Finset (HeightOneSpectrum (𝓞 D.host.E)), (∀ w ∈ s, w ∈ placesOver D.host.E (D.nd.l i)) → (∑ w ∈ s, locDeg D.host.E w) ≤ 2 * D.R.f ∧ 2 * s.card ≤ ∑ w ∈ s, locDeg D.host.E w := GlobalTheory.T.theoremB_localDegree_sum_bounds

theorem closingIneq : ∀ (CA C b l S η Rw Tb Vd : ℝ) (f r t m p : ℕ), 13 * max CA 0 ≤ C → 260 * f ^ 2 * t ^ 2 * (r + t) ≤ p → 1 ≤ t → 1 ≤ f → m ≤ r → 3 ≤ l → 0 ≤ S → 0 ≤ η → 0 < b → 1 < Real.log b → Rw ≤ max CA 0 * (3 * (f : ℝ) * r * (4 * b / l + 2 * S + 2 * Real.logb l (2 * b) + 1 + η + t) + 6 * (f : ℝ) * m * (2 * b + 1)) + f → Tb ≤ 240 * (t : ℝ) ^ 2 * (f : ℝ) ^ 2 * ((r : ℝ) + t) * Real.log b → Vd ≤ 4 * ((r : ℝ) + t) * t → Rw + Tb + Vd ≤ C * f * (r * (b / l + S + t + η + Real.log b) + m * b) + (p : ℝ) * Real.log b := GlobalTheory.T.closing_numerical_inequality_theoremB

theorem theoremB_of_admitted : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (CA C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 13 * max CA 0 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.admW (D := D) HW F → EmbeddingTypeJumps.admA (D := D) CA → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.admTB (D := D) HW F → EmbeddingTypeJumps.admBK (D := D) → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → EmbeddingTypeJumps.LiteratureHypotheses (D := D) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  intro D HW F r ρ large₂ ep CA C Qp hC hP hW hA hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hTB hBK hKill hJump hFon hLit hPar
  obtain ⟨h0, h1⟩ := GlobalTheory.T.local_fields_at_auxiliary_primes D
  intro i hl tw hbig π hπ hsF hsha
  have hQ : EmbeddingTypeJumps.AtQD i := ⟨⟨hl, tw⟩, ⟨π, (D.Zgood_tie i π).1 hπ⟩⟩
  obtain ⟨dc, hcol⟩ := declNoColumns D i hl
  obtain ⟨lenRow, hROW, hRowB⟩ := rowBound D r ρ large₂ ep CA h0 h1 hA hJump hFon hG2 hSet hLit hPar i hQ π hπ dc
  obtain ⟨cB, hTBi, hcB⟩ := tbConst D HW F r ρ large₂ ep h0 h1 hW hTB hJump hFon hG2 hSet hLit hPar i hQ π hπ
  have hAdm : TruncatedSeriesCountingIdentities.admitted i (r i) (ρ i) π dc lenRow (fun _ => 0) cB := by
    refine ⟨hG1 i hQ, hG2 i hQ π hπ, hG3 i hQ π hπ, hG4 i hQ, hG5 i hQ, (hLit i hQ).1, hG6 i hQ,
      bkAt D hBK hLit i hQ, hTBi, hROW, ?_, (hSet i hQ π hπ).1, (hSet i hQ π hπ).2.1,
      (hSet i hQ π hπ).2.2.1, (hSet i hQ π hπ).2.2.2, (hLit i hQ).2.2.1, (GlobalTheory.admissible_shape_and_epsilon_at_every_localisation.main D i).1,
      (hLit i hQ).2.2.2.1, (hLit i hQ).2.2.2.2.1, (hLit i hQ).2.2.2.2.2⟩
    intro w hw hwc
    simp [hcol] at hwc
  obtain ⟨hg0, hg1⟩ := ne_typePrimes D h1 i hl
  have key := hN5 i π dc lenRow (fun _ => 0) cB hAdm hg0 hg1 (LargeLevelLemmas.zgoodSubsetZ i hπ) hsF hsha
  have hlw : ∀ w ∈ dc.row, TruncatedSeriesCountingIdentities.lenW i (ρ i) π dc lenRow (fun _ => 0) w = lenRow w := by
    intro w _
    unfold TruncatedSeriesCountingIdentities.lenW
    rw [dif_neg (by simp [hcol])]
  rw [hcol] at key
  simp only [Finset.union_empty] at key
  rw [Finset.sum_congr rfl hlw] at key
  simp only [Finset.card_empty, Nat.cast_zero, zero_add, mul_one, mul_zero, zero_mul, add_zero] at key
  have keyR := (Rat.cast_le (K := ℝ)).2 key
  push_cast at keyR
  have ht1 : 1 ≤ D.R.t := D.R.t_odd.pos
  have hmr : D.R.m ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; omega
  have hr1 : 1 ≤ D.R.r := by unfold Ranks.r; have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hf1 : 1 ≤ D.R.f := by unfold Ranks.f Ranks.n; have := And.intro (Nat.one_le_two_pow (n := D.R.e)) (show 0 < D.R.ord by positivity); omega
  have hl3 : 3 ≤ D.nd.l i := by
    have htr : 1 ≤ D.R.t * D.R.r := Nat.mul_pos ht1 hr1
    rcases hl with h | h <;> rw [h]
    · have := D.host.qd_big.1; nlinarith
    · have := D.host.qd_big.2; nlinarith
  have hnV : (D.R.nV : ℝ) = D.R.r + D.R.t := by unfold Ranks.nV; push_cast; ring
  have hL0 : 0 < large₂.sc.L := by unfold Scale.L; exact Real.rpow_pos_of_pos (by linarith [large₂.sc.one_lt_alt]) _
  have hb1 : 1 < large₂.sc.b := by unfold Scale.b; have := Real.add_one_lt_exp (ne_of_gt hL0); linarith
  have hb0 : 0 < large₂.sc.b := by linarith
  have hLb : 1 < Real.log large₂.sc.b := by
    unfold Scale.b; rw [Real.log_exp]; unfold Scale.L
    exact Real.one_lt_rpow large₂.sc.one_lt_alt large₂.sc.eps_pos
  have hrowP : ∀ w ∈ dc.row, w ∈ placesOver D.host.E (D.nd.l i) := fun w hw => (dc.cover w).1 (Or.inl hw)
  obtain ⟨hSD, hSC⟩ := degBounds D h1 i hl dc.row hrowP
  have hSDr : ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) ≤ 2 * D.R.f := by exact_mod_cast hSD
  have hSCr : 2 * (dc.row.card : ℝ) ≤ ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) := by exact_mod_cast hSC
  set SD : ℝ := ((∑ w ∈ dc.row, locDeg D.host.E w : ℕ) : ℝ) with hSDdef
  set K := max CA 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  set X := 4 * large₂.sc.b / (D.nd.l i : ℝ) + 2 * large₂.Sc + 2 * Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) + 1 + large₂.etaSz + (D.R.t : ℝ) with hX
  have hl3r : (3 : ℝ) ≤ D.nd.l i := by exact_mod_cast hl3
  have hX0 : 0 ≤ X := by
    have : 0 ≤ Real.logb (D.nd.l i : ℝ) (2 * large₂.sc.b) := Real.logb_nonneg (by linarith) (by linarith)
    have := large₂.Sc_pos; have := large₂.etaSz_pos
    have : 0 ≤ 4 * large₂.sc.b / (D.nd.l i : ℝ) := by positivity
    positivity
  set Y := 2 * large₂.sc.b + 1 with hY
  have hY0 : 0 ≤ Y := by positivity
  have hRw : (∑ w ∈ dc.row, (lenRow w : ℝ)) ≤
      K * (3 * (D.R.f : ℝ) * D.R.r * X + 6 * (D.R.f : ℝ) * D.R.m * Y) + D.R.f := by
    have hcard : (dc.row.card : ℝ) ≤ D.R.f := by linarith
    have hsum : (∑ w ∈ dc.row, (K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
        3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1)) =
        (K * D.R.r * X + 3 * K * D.R.m * Y) * SD + dc.row.card * (K * D.R.r * X + 1) := by
      have : ∀ w ∈ dc.row, K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
          3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1 =
          (K * D.R.r * X + 3 * K * D.R.m * Y) * ((locDeg D.host.E w : ℕ) : ℝ) + (K * D.R.r * X + 1) := by
        intro w _; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hSDdef]
      push_cast; ring
    have e1 : (K * D.R.r * X + 3 * K * D.R.m * Y) * SD ≤ (K * D.R.r * X + 3 * K * D.R.m * Y) * (2 * D.R.f) :=
      mul_le_mul_of_nonneg_left hSDr (by positivity)
    have e2 : (dc.row.card : ℝ) * (K * D.R.r * X + 1) ≤ D.R.f * (K * D.R.r * X + 1) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    calc (∑ w ∈ dc.row, (lenRow w : ℝ)) ≤ ∑ w ∈ dc.row, (K * (((locDeg D.host.E w : ℕ) + 1 : ℝ) * (D.R.r : ℝ) * X +
          3 * ((locDeg D.host.E w : ℕ) : ℝ) * (D.R.m : ℝ) * Y) + 1) := Finset.sum_le_sum hRowB
      _ = (K * D.R.r * X + 3 * K * D.R.m * Y) * SD + dc.row.card * (K * D.R.r * X + 1) := hsum
      _ ≤ (K * D.R.r * X + 3 * K * D.R.m * Y) * (2 * D.R.f) + D.R.f * (K * D.R.r * X + 1) := add_le_add e1 e2
      _ = K * (3 * (D.R.f : ℝ) * D.R.r * X + 6 * (D.R.f : ℝ) * D.R.m * Y) + D.R.f := by ring
  have hTb : (D.R.t : ℝ) * ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ) ≤
      240 * (D.R.t : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * ((D.R.r : ℝ) + D.R.t) * Real.log large₂.sc.b := by
    have hs : ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ) = (SD + 2 * dc.row.card) * cB := by
      rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, hSDdef]
      push_cast; ring
    rw [hs]
    have h4 : SD + 2 * (dc.row.card : ℝ) ≤ 4 * D.R.f := by linarith
    have hc0 : (0 : ℝ) ≤ cB := by positivity
    have hS0 : (0 : ℝ) ≤ SD + 2 * (dc.row.card : ℝ) := by positivity
    calc (D.R.t : ℝ) * ((SD + 2 * dc.row.card) * cB) ≤ (D.R.t : ℝ) * ((4 * D.R.f) *
          (60 * (D.R.t : ℝ) * (D.R.f : ℝ) * ((D.R.r : ℝ) + (D.R.t : ℝ)) * Real.log large₂.sc.b)) := by
          gcongr
      _ = 240 * (D.R.t : ℝ) ^ 2 * (D.R.f : ℝ) ^ 2 * ((D.R.r : ℝ) + D.R.t) * Real.log large₂.sc.b := by ring
  have hVd : 4 * (D.R.nV : ℝ) * ((D.nd.vdel i : ℚ) : ℝ) ≤ 4 * ((D.R.r : ℝ) + D.R.t) * D.R.t := by
    rw [hnV]
    have h1' : ((D.nd.vdel i : ℚ) : ℝ) ≤ D.R.t := by exact_mod_cast localDelta_le_cuspTwistDepth D i hl
    have : (0 : ℝ) ≤ D.R.r + D.R.t := by positivity
    nlinarith
  have hK2 := (hKill i hl tw (Or.inr (cycDegree_gt D h1 i hl)) π hπ).2
  simp only [EmbeddingTypeJumps.vZeta] at hK2
  push_cast at hK2
  have har := closingIneq CA C large₂.sc.b (D.nd.l i) large₂.Sc large₂.etaSz (∑ w ∈ dc.row, (lenRow w : ℝ))
    ((D.R.t : ℝ) * ∑ w ∈ dc.row, (((locDeg D.host.E w : ℕ) : ℝ) + 2) * (cB : ℝ))
    (4 * (D.R.nV : ℝ) * ((D.nd.vdel i : ℚ) : ℝ)) D.R.f D.R.r D.R.t D.R.m (EmbeddingTypeJumps.polyVal Qp D.R.f D.R.r D.R.t)
    hC (hP _ _ _) ht1 hf1 hmr hl3r large₂.Sc_pos.le large₂.etaSz_pos.le hb0 hLb hRw hTb hVd
  unfold EmbeddingTypeJumps.bndB
  push_cast
  linarith [keyR, hK2, har]

end GlobalTheory.TheoremB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedEnlargementCutCocyclesBlochKato
section
noncomputable section

open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pass
  GlobalTheory.Cut GlobalTheory.UseLoc Module TensorProduct GlobalTheory.UseLoc.Cases

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.UseLoc.Cases

set_option maxHeartbeats 8000000 in
theorem partW : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π))) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (WpO D.nd i ρ π) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_integralTensorTorsion_cocycle_of_torsion_localCocycle D i w hw C lam hlam (locOC C (WpO D.nd i ρ π)) θ a
    (fun g => liftQ C.le D.R.r (z g)) hZ hk
  have hz'' : ∀ g, iotaW ↥C.LL.1 lam a D.R.r (z' g) = liftQ C.le D.R.r (z g) := hz'
  have hadm := GlobalTheory.T.cocycleExtension_twistedWeilCoefficients_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont z hz a z' hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).1 (repV C (locOC C (WpO D.nd i ρ π)))
    (latC C (locOC C (WpO D.nd i ρ π))) (GlobalTheory.T.representationOfIntegralMatrices_eq_inv_twistedChar_smul D i w hw C (locOC C (WpO D.nd i ρ π)) θ) rfl z' hcoc).1 hadm
  have hr := GlobalTheory.T.isBlochKato_read_of_tensor_selmer_add_coboundary D i w hw C lam (locOC C (WpO D.nd i ρ π)) θ a z' hin
  have e : (fun g => liftQ C.le D.R.r (z g)) = fun g => iotaW ↥C.LL.1 lam a D.R.r (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

set_option maxHeartbeats 8000000 in
theorem partC : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c))) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont c hc z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (chiRatO D.nd i c) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle D i w hw C lam hlam θ c a (fun g => liftQ C.le 1 (z g)) hZ hk
  have hz'' : ∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g) := hz'
  have hc1 : c ∈ Finset.Icc 1 D.R.t :=
    Finset.mem_Icc.2 ⟨by have := (Finset.mem_Icc.1 hc).1; omega, (Finset.mem_Icc.1 hc).2⟩
  have hadm := GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont c hc1 z hz a z'
    hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).2.1 c hc (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ c)) z'
    hcoc).1 hadm
  have hr := GlobalTheory.T.isCoboundary_read_of_twistedCharacter_coboundary D i w hw C lam θ c a z' hin
  have e : (fun g => liftQ C.le 1 (z g)) = fun g => iotaC ↥C.LL.1 lam a (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

set_option maxHeartbeats 8000000 in
theorem partU : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →

    ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont z hz
  have h5' : 5 ≤ (Br.PD D.loc D.nbr i w hw).p := by rw [Br.PD_p]; exact h5
  have hT := hTop h5' D.R.t h w' η typ U (Fin D.R.r → ↥C.LL.1) (repV C (twistM (locOC C (WpO D.nd i ρ π)) θ))
    (latC C (twistM (locOC C (WpO D.nd i ρ π)) θ)) (chiT C θ) hSet.1
  obtain ⟨a, hZ, hk⟩ := GlobalTheory.T.cutCocycles_locallyConstant_killed_by_uniformiserPow D i r w hw C lam hlam hGood hCont (chiRatO D.nd i 1) z hz
  haveI := GlobalTheory.T.finite_lambdaPowerTorsionFieldModInt C.LL lam hlam a
  obtain ⟨z', hcoc, hz'⟩ := GlobalTheory.T.exists_twistedCharacter_cocycle_of_torsion_localCocycle D i w hw C lam hlam θ 1 a (fun g => liftQ C.le 1 (z g)) hZ hk
  have hz'' : ∀ g, iotaC ↥C.LL.1 lam a (z' g) = liftQ C.le 1 (z g) := hz'
  have hc1 : 1 ∈ Finset.Icc 1 D.R.t := Finset.mem_Icc.2 ⟨le_rfl, hSet.1.1⟩
  have hadm := GlobalTheory.T.cocycleExtension_conductorTwistedCharacter_admissible D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hSet hGood hπ hDec hCont 1 hc1 z hz a z'
    hcoc hz''
  have hin := ((hT ↥(Xq ↥C.LL.1 lam a)).2.2 (latOne (LL := ↥C.LL.1) Subtype.val_injective (chiT C θ 1)) z'
    hcoc).1 hadm
  have hr := GlobalTheory.T.isUnramified_read_of_trivialTwist_coboundary_on_subgroup D i w hw C lam θ a _ z' hin
  have e : (fun g => liftQ C.le 1 (z g)) = fun g => iotaC ↥C.LL.1 lam a (z' g) :=
    funext fun g => (hz'' g).symm
  rw [e]
  exact hr

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (C : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hA : CaseA (D.nbr i w hw).Kw C.LL) (lam : ↥(OL C.LL)), Irreducible lam →
    ∀ (θ : Br.G D.nbr i w hw →* (↥(OL C.LL))ˣ)
      (h w' η : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → ℕ)
      (typ : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Bool)
      (U : ZMod (finrank ℚ_[D.nd.l i] ↥(K0 (D.nbr i w hw).Kw)) → Multiset ℤ),
    tableLineDegreeTwo.TopCore (Br.PD D.loc D.nbr i w hw) (embC HW C hA) lam (IK (D.nbr i w hw).Kw) → 5 ≤ D.nd.l i →
    SetC HW r ρ π C hA lam θ h w' η typ U → GoodR D.nd i r → π ∈ D.nd.Z i → TruncatedSeriesCountingIdentities.SemisimpleDecomposition i r ρ π →
    TruncatedSeriesCountingIdentities.FamilyContinuous i r →
    (∀ z ∈ cutCoc i w hw r Set.univ (WpO D.nd i ρ π),
      (fun g => liftQ C.le D.R.r (z g)) ∈ HfD (Br.PD D.loc D.nbr i w hw) (latC C (locOC C (WpO D.nd i ρ π)))) ∧
    (∀ c ∈ Finset.Icc 2 D.R.t, ∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i c),
      (fun g => liftQ C.le 1 (z g)) ∈ BD (latC C (locOC C (chiRatO D.nd i c)))) ∧
    (∀ z ∈ cutCoc i w hw r Set.univ (chiRatO D.nd i 1),
      (fun g => liftQ C.le 1 (z g)) ∈ Z1urD (latC C (locOC C (chiRatO D.nd i 1))) (IK (D.nbr i w hw).Kw)) := by
  intro D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont
  exact ⟨partW D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont,
    partC D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont,
    partU D HW i r ρ π w hw C hA lam hlam θ h w' η typ U hTop h5 hSet hGood hπ hDec hCont⟩

end GlobalTheory.UseLoc.Cases

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeightZeroSectionValueOnMarkedPeriodSpace
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.MarkVal

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH
  Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in

theorem val_at_mark {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {n r : ℕ} (V : HSp D) (hr : V.rank = r) (σ0 : c.F →+* ℂ) (d : DeltaDat Xo c n)
    (U₂ : Unf d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) r)
    (dict₂ : GA D V → Σ k, Frame (U₂.X k).Ψ r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E))
    (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (C : GlobalTheory.Member.Ctx d.Xo₂ d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) V r) (hC : C.OK) (hι : C.ι = ι)
    (hx : C.x₀ = x₀) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ) (hf : d.cδ ∈ sec d.Xo₂ d.c₂ 0 0)
    (hxi1 : ∀ u : GA D V, gLat V u = latHat V → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)),
      ((Matrix.GeneralLinearGroup.det (finHom V u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) :
        (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = (d.l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom V u)) = 1)
    (hxi2 : ∀ γ ∈ GQ V, xi (Matrix.GeneralLinearGroup.det (finHom V γ)) = 1)
    (hv : GlobalTheory.OneMapAll.CXiAt V hr σ0 d U₂ dict₂ ι x₀ xi c0)
    (y : FrPt d.Xo₂ d.c₂ (CAt (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)))) (k : Fin C.F.n) (P : (C.F.Di k).La →+ (Fin C.g → ℂ))
    (hP : IsPeriod (C.F.Di k) (fun j => relab d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (C.e j).1) P)
    (hy : y.x = C.F.u k P) (h γ : GA D V) (hM : C.Mark h k γ) :
    toC (evR d.Xo₂ d.c₂ d.cδ y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom V (γ * h))) : ℂˣ) : ℂ) := by
  classical
  subst hr hι hx
  obtain ⟨hU, hW, g₀, e₀, F, ik, φ, th, hth, hD, hval⟩ := hv
  have hσ : GoodEmb d.c₂ (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) := hC.good
  have hor : ∀ j, IsOrthogonalFrame (U₂.X j) C.x₀ := by
    intro j τ hτ
    have h1 := hC.orth k
    have hG : (U₂.X j).Gm = (C.M.X k).Gm := by rw [(hW j).1, (hC.modelW k).1]
    have hp : (U₂.X j).p0 = (C.M.X k).p0 := ((hU.2.1 j).1).trans (hC.base.type k).1.symm
    have hΨ : τ ∈ (C.M.X k).Ψ := ((hC.base.type k).2 τ).2 (((hU.2.1 j).2 τ).1 hτ)
    rw [hG, hp]
    exact h1 τ hΨ

  have hdom := GlobalTheory.T.latticeDictionary_frame_mem_open_frames V U₂ dict₂ C.ι e₀ F ik φ th C.x₀ hσ hC.lA hU hW hD hth hor
  obtain ⟨h', hh'⟩ := GlobalTheory.TwistTie.exists_dict_over V U₂ dict₂ C.ι e₀ F ik φ th C.x₀ hσ hC.lA hC.pos hU hW hD hC.iota
    hth hor hdom y
  obtain ⟨P', -, hP', hy', -⟩ := hD.1.2 (dict₂ h').1 ⟨_, hdom h'⟩
  have hpt : C.F.u k P = F.u (ik (dict₂ h').1) P' := hy.symm.trans (hh'.trans hy')
  have hg : (σ0.comp (d.eF.symm : d.c₂.F →+* c.F)) (IntermediateField.inclusion d.c₂.le (baseKA d.l₂).ρ) = H.rt0 := hC.good
  obtain ⟨gam, hgE, hgm⟩ := GlobalTheory.T.familyUniformisation_points_eq_marked_isometry C.F F hC.pos hg
    ((GlobalTheory.Relab.relab_good _ H d.l₂ d.c₂ _ hσ).2.2.2 Dw C.g C.e)
    ((GlobalTheory.Relab.relab_good _ H d.l₂ d.c₂ _ hσ).2.2.2 Dw g₀ e₀) (C.e.trans e₀.symm)
    (fun j => by simp) k (ik (dict₂ h').1) P P' hP hP' hpt
  obtain ⟨γ', hγ', hΛ', hm', -⟩ := hD.2 h'
  have hxe := GlobalTheory.T.detCharacter_eq_of_marked_lattice_isometry d.l₂ V C.ι hC.iota.emb.2 (C.F.Di k) (F.Di (ik (dict₂ h').1)) (C.F.t k) (F.t (ik (dict₂ h').1))
    (C.M.X k) (U₂.X (dict₂ h').1) (C.M.φ k) (φ (dict₂ h').1) (γ * h) (γ' * h') (hC.modelW k) (hW _)
    (hC.base.ef k) (hD.1.1 _) hM.2.1 hΛ' hM.2.2 hm' gam hgE hgm xi hxi1 hxi2
  have hv := hval h' γ' ⟨hγ', hΛ', hm'⟩
  rw [GlobalTheory.WeightZeroValue.evR_eq_of_same_point hf hh', ← hxe, ← hv]
  show _ = (if h'' : (dict₂ h').2 ∈ (U₂.X (dict₂ h').1).dom then toC (evR d.Xo₂ d.c₂ d.cδ (U₂.un _ ⟨_, h''⟩)) else 0)
  rw [dif_pos (hdom h')]

end GlobalTheory.MarkVal

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.MarkVal

set_option maxHeartbeats 4000000 in

theorem val_on_marked_space : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (C : GlobalTheory.Member.Ctx (M.dδ a).Xo₂ (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (Wc D i) D.R.r), C.OK → C.ι = iotaW T i → C.x₀ = T.x₀ ((i : ℕ) + 1) M.s0 → ∀ (f : Rul (M.dδ a).Xo₂ (M.dδ a).c₂) (xi : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ →* ℂˣ) (c0 : ℂ), f ∈ sec (M.dδ a).Xo₂ (M.dδ a).c₂ 0 0 → (∀ u : GA D (Wc D i), gLat (Wc D i) u = latHat (Wc D i) → (∃ w ∈ GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)), ((Matrix.GeneralLinearGroup.det (finHom (Wc D i) u) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) - 1 = ((M.dδ a).l₂.M : ℕ) • w) → xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) u)) = 1) → (∀ γ ∈ GQ (Wc D i), xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) γ)) = 1) → GlobalTheory.OneMapAll.CXiAt (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) xi c0 → ∀ (y : FrPt (M.dδ a).Xo₂ (M.dδ a).c₂ (CAt ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)))) (k : Fin C.F.n) P, IsPeriod (C.F.Di k) (fun j => relab (M.dδ a).c₂ ((inC M.c').comp ((M.dδ a).eF.symm : (M.dδ a).c₂.F →+* M.c'.F)) (C.e j).1) P → y.x = C.F.u k P → ∀ h γ : GA D (Wc D i), C.Mark h k γ → toC (evR (M.dδ a).Xo₂ (M.dδ a).c₂ f y) = c0 * ((xi (Matrix.GeneralLinearGroup.det (finHom (Wc D i) (γ * h))) : ℂˣ) : ℂ) := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hcore hfw i Tp tup M hM a C hOK hι hx f xi c0 hf hxi1 hxi2 hCX y k P hPer hy h γ hmk
  exact val_at_mark (Wc D i) (rank_Wc i) (inC M.c') { M.dδ a with cδ := f } (M.U₂ a) (M.dict₂ a) (iotaW T i)
    (T.x₀ ((i : ℕ) + 1) M.s0) C hOK hι hx xi c0 hf hxi1 hxi2 hCX y k P hPer hy h γ hmk

end GlobalTheory.MarkVal
end
end

