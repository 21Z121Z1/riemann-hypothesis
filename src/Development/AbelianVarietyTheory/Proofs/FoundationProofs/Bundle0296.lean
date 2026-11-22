import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0288
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0283
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0255
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0248
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryHeckeCharacterValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0289
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0240
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0291
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0277
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0293
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0013
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LeafBounds.MeanMaxLeaf.LeafMMFree
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0292
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0250

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.TwoTorsionPt

theorem not_integral_half {N : ℕ} (hN : Odd N) {x : ℂ} (hx : IsIntegral ℤ x)
    (h : x + (starRingEnd ℂ) x = (N : ℂ) / 2) : False := by
  have h1 : IsIntegral ℤ ((starRingEnd ℂ) x) := hx.map (starRingEnd ℂ).toIntAlgHom
  have h2 : IsIntegral ℤ (algebraMap ℚ ℂ ((N : ℚ) / 2)) := by
    have : algebraMap ℚ ℂ ((N : ℚ) / 2) = (N : ℂ) / 2 := by simp
    rw [this, ← h]; exact hx.add h1
  have h3 : IsIntegral ℤ ((N : ℚ) / 2) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective).1 h2
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
  have h4 : (N : ℚ) = 2 * (m : ℚ) := by
    have : (m : ℚ) = (N : ℚ) / 2 := by simpa using hm
    rw [this]; ring
  have h5 : (N : ℤ) = 2 * m := by exact_mod_cast h4
  obtain ⟨k, hk⟩ := hN
  omega

theorem isTwoTorsionCMPoint_of_odd_multiple (D : D7) (Λ : AddSubgroup ℂ) {δ : ℂ} (hδ : δ ≠ 0) {N : ℕ} (hN : Odd N)
    (hmem : δ * N ∈ Λ) (hint : ∀ w ∈ Λ, ∃ x : ℂ, IsIntegral ℤ x ∧ w = δ * x) :
    GL3Theta.IsTwoTorsionPointUnkilled D Λ (δ * N / 2) := by
  refine ⟨?_, ?_, ?_⟩
  · have : 2 * (δ * N / 2) = δ * N := by ring
    rw [this]; exact hmem
  · intro h
    obtain ⟨x, hx, e⟩ := hint _ h
    have e' : x = ((1 + Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * (N / 2) := by
      apply mul_left_cancel₀ hδ
      rw [← e]; ring
    refine not_integral_half hN hx ?_
    rw [e']
    simp only [map_mul, map_div₀, map_add, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring
  · intro h
    obtain ⟨x, hx, e⟩ := hint _ h
    have e' : x = ((1 - Complex.I * (Real.sqrt D.host.d : ℂ)) / 2) * (N / 2) := by
      apply mul_left_cancel₀ hδ
      rw [← e]; ring
    refine not_integral_half hN hx ?_
    rw [e']
    simp only [map_mul, map_div₀, map_sub, map_one, Complex.conj_I, Complex.conj_ofReal,
      map_natCast, map_ofNat]
    ring

theorem lamOf_integral (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    ∀ w ∈ lamOf D cc δ, ∃ x : ℂ, IsIntegral ℤ x ∧ w = δ * x := by
  intro w hw
  unfold lamOf at hw
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, -, rfl⟩ := hw
    refine ⟨_, ?_, rfl⟩
    have h0 : IsIntegral ℤ (c : D.host.K) := c.2
    exact h0.map (D.host.φ₀.comp (algebraMap D.host.K D.host.E)).toIntAlgHom
  | zero => exact ⟨0, isIntegral_zero, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    exact ⟨x + y, hx.add hy, by ring⟩
  | neg a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨-x, hx.neg, by ring⟩

theorem norm_mem_lamOf (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    δ * (Ideal.absNorm cc : ℕ) ∈ lamOf D cc δ := by
  refine AddSubgroup.subset_closure ⟨((Ideal.absNorm cc : ℕ) : 𝓞 D.host.K), Ideal.absNorm_mem cc, ?_⟩
  simp

theorem odd_norm {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) :
    Odd (Ideal.absNorm cc) :=
  Nat.coprime_two_right.1 (Nat.Coprime.coprime_mul_right_right h.1.2)

theorem delta_ne {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) : δ ≠ 0 :=
  (GlobalTheory.T.idealPeriodLattice_of_curveDatum D (GlobalTheory.T.inducedType_thetaGenusOne_permutes D).1 cc δ h).2.1

theorem exists_lamOf {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) :
    ∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0 :=
  ⟨_, isTwoTorsionCMPoint_of_odd_multiple D _ (delta_ne h) (odd_norm h) (norm_mem_lamOf D cc δ) (lamOf_integral D cc δ)⟩

theorem exists_bar {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (h : Crv D cc δ) (Λ : AddSubgroup ℂ)
    (hΛ : Λ.map (starRingEnd ℂ).toAddMonoidHom = lamOf D cc δ) :
    ∃ t0, GL3Theta.IsTwoTorsionPointUnkilled D Λ t0 := by
  have hδ : (starRingEnd ℂ) δ ≠ 0 := by simpa using delta_ne h
  refine ⟨_, isTwoTorsionCMPoint_of_odd_multiple D Λ hδ (odd_norm h) ?_ ?_⟩
  · have h1 := norm_mem_lamOf D cc δ
    rw [← hΛ] at h1
    obtain ⟨w, hw, e⟩ := h1
    have e1 : (starRingEnd ℂ) w = δ * (Ideal.absNorm cc : ℕ) := e
    have e2 : w = (starRingEnd ℂ) δ * (Ideal.absNorm cc : ℕ) := by
      rw [← Complex.conj_conj w, e1, map_mul, map_natCast]
    rw [← e2]; exact hw
  · intro w hw
    have h1 : (starRingEnd ℂ) w ∈ lamOf D cc δ := by
      rw [← hΛ]; exact ⟨w, hw, rfl⟩
    obtain ⟨x, hx, e⟩ := lamOf_integral D cc δ _ h1
    refine ⟨(starRingEnd ℂ) x, hx.map (starRingEnd ℂ).toIntAlgHom, ?_⟩
    rw [← Complex.conj_conj w, e, map_mul]

theorem exists_extension (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) :
    ∃ (M' : IntermediateField ℚ ℂ) (ρ' : M' →ₐ[ℚ] ℂ), (∀ x : ℂ, IsAlgebraic ℚ x → x ∈ M') ∧
      ∀ x ∈ M, x ∈ M' ∧ ρ' (TaylorLogMetric.liftM M' x) = ρ (TaylorLogMetric.liftM M x) := by
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_restrictDomain_of_isAlgebraic (K := ℚ) (L := M) (M := ℂ)
    (E := algebraicClosure M ℂ) ρ
  refine ⟨(algebraicClosure M ℂ).restrictScalars ℚ, φ, ?_, ?_⟩
  · intro x hx
    exact mem_algebraicClosure_iff.2 (hx.extendScalars (algebraMap ℚ M).injective)
  · intro x hx
    have hx' : x ∈ (algebraicClosure M ℂ).restrictScalars ℚ :=
      (algebraicClosure M ℂ).algebraMap_mem (⟨x, hx⟩ : M)
    refine ⟨hx', ?_⟩
    unfold TaylorLogMetric.liftM
    rw [dif_pos hx', dif_pos hx, ← hφ]
    rfl

theorem exists_point : ∀ D : D7, t0Ex D := by
  intro D cc δ hc
  refine ⟨exists_lamOf hc, ?_⟩
  intro M ρ h2 h3
  obtain ⟨M', ρ', halg, hext⟩ := exists_extension M ρ
  have hl : lamConj M ρ (lamOf D cc δ) = lamConj M' ρ' (lamOf D cc δ) := by
    unfold lamConj
    rw [(hext _ h2).2, (hext _ h3).2]
  rw [hl]
  have hD : DataIn D (tor0 D cc δ) M' := by
    refine ⟨fun τ x => halg _ ?_, (hext _ h2).1, (hext _ h3).1⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom (embT D τ).toRatAlgHom
  obtain ⟨hfix, hbar, -⟩ := GlobalTheory.T.cmTheta_complexConjugation_compatible D cc δ hc M' ρ' hD
  rcases hfix with hfix | hfix
  · obtain ⟨cc', δ', hc', -, e⟩ := GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc M' ρ' hfix hD.2.1 hD.2.2 1 one_pos
    rw [e]
    exact exists_lamOf hc'
  · obtain ⟨cc', δ', hc', -, e⟩ :=
      GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice D cc δ hc M' (rhoBar M' ρ') hfix hD.2.1 hD.2.2 1 one_pos
    refine exists_bar hc' _ ?_
    rw [← e]
    exact (congrArg Tor.abelian₂ hbar).symm

end GlobalTheory.TwoTorsionPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergRelativeIndexTranslateCompletedLattice
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil.MovedIdx

theorem common_denom {A ι : Type} [CommRing A] [Fintype ι] (S : Subring A) (f : ι → A) (P : ℕ → Prop) (h1 : P 1)
    (hm : ∀ a b, P a → P b → P (a * b)) (h : ∀ i, ∃ n : ℕ, P n ∧ (n : A) * f i ∈ S) :
    ∃ n : ℕ, P n ∧ ∀ i, (n : A) * f i ∈ S := by
  choose n hn hf using h
  refine ⟨∏ i, n i, Finset.prod_induction _ P hm h1 fun i _ => hn i, fun i => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem n (Finset.mem_univ i)
  rw [hc, mul_comm (n i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem S c) (hf i)

theorem dvd_of_dvd_idx {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (A B : Submodule R X) (n q : ℕ)
    (hq : q.Prime) (h0 : idx A B ≠ 0) (hn : ∀ x ∈ B, n • x ∈ A) (hd : q ∣ idx A B) : q ∣ n := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Finite (B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) := Nat.finite_of_card_ne_zero h0
  obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' (G := B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) q hd
  rw [← hx, addOrderOf_dvd_iff_nsmul_eq_zero]
  induction x using QuotientAddGroup.induction_on with
  | H y =>
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact hn y.1 y.2

theorem denom_mul (D : D7) {q : ℕ} (hq : q.Prime) {x : AE D} (hx : ZeroAt D q x) (y : AE D) :
    ∃ n : ℕ, n.Coprime q ∧ (n : AE D) * (y * x) ∈ OhE D := by
  obtain ⟨n, hn, hy⟩ := GlobalTheory.HeckeVal.exists_denom D y
  obtain ⟨a, n', hn', rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' q hq.ne_one
  obtain ⟨m, -, hmq, s, hs, h⟩ := hx a
  refine ⟨m * n', Nat.Coprime.mul_left hmq ((Nat.Prime.coprime_iff_not_dvd hq).2 hn').symm, ?_⟩
  convert mul_mem hs hy using 1
  push_cast
  linear_combination (n' : AE D) * y * h

theorem one_entry_mem (D : D7) {N : ℕ} (i j : Fin N) : (1 : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  rw [Matrix.one_apply]; split_ifs
  · exact one_mem _
  · exact zero_mem _

theorem denom_triv (D : D7) {q N : ℕ} {g : GL (Fin N) (AE D)} (hg : TrivAt D q g) :
    ∃ n : ℕ, n.Coprime q ∧ ∀ i j, (n : AE D) * (g : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N => (g : Matrix (Fin N) (Fin N) (AE D)) p.1 p.2)
    (fun n => n.Coprime q) (by simp) (fun a b => Nat.Coprime.mul_left) (by
      rintro ⟨i, j⟩
      obtain ⟨m, -, hm, s, hs, e⟩ := hg i j 0
      refine ⟨m, hm, ?_⟩
      convert add_mem hs (mul_mem (natCast_mem _ m) (one_entry_mem D i j)) using 1
      linear_combination e)
  exact ⟨n, hn, fun i j => h (i, j)⟩

theorem denom_triv_inv (D : D7) {q N : ℕ} (hq : q.Prime) {g : GL (Fin N) (AE D)} (hg : TrivAt D q g) :
    ∃ n : ℕ, n.Coprime q ∧ ∀ i j, (n : AE D) * ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N × Fin N =>
      ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) p.1 p.2.1 *
      ((g : Matrix (Fin N) (Fin N) (AE D)) p.2.1 p.2.2 - (1 : Matrix (Fin N) (Fin N) (AE D)) p.2.1 p.2.2))
    (fun n => n.Coprime q) (by simp) (fun a b => Nat.Coprime.mul_left) (fun p => denom_mul D hq (hg _ _) _)
  refine ⟨n, hn, fun i j => ?_⟩
  have e : ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) =
      1 - ((g⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) * ((g : Matrix (Fin N) (Fin N) (AE D)) - 1) := by
    rw [Matrix.mul_sub, Units.inv_mul, Matrix.mul_one, sub_sub_cancel]
  rw [e, Matrix.sub_apply, Matrix.mul_apply, mul_sub, Finset.mul_sum]
  exact sub_mem (mul_mem (natCast_mem _ n) (one_entry_mem D i j)) (sum_mem fun l _ => h (i, l, j))

theorem denom_mat (D : D7) {N : ℕ} (M : Matrix (Fin N) (Fin N) (AE D)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i j, (n : AE D) * M i j ∈ OhE D := by
  obtain ⟨n, hn, h⟩ := common_denom (OhE D) (fun p : Fin N × Fin N => M p.1 p.2)
    (fun n => 0 < n) one_pos (fun a b => Nat.mul_pos) (fun p => GlobalTheory.HeckeVal.exists_denom D _)
  exact ⟨n, hn, fun i j => h (i, j)⟩

theorem nsmul_mem_latA (D : D7) (cc : Ideal (𝓞 D.host.K)) {N N' : ℕ} (g : GA D N) (g' : GA D N') {n n' : ℕ}
    (h : ∀ i j, (n : AE D) * (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D)) i j ∈ OhE D)
    (h' : ∀ i j, (n' : AE D) * ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D)) i j ∈ OhE D) :
    ∀ ζ ∈ (latA D cc N N').map (actA D N N' (g, g')), (n * n') • ζ ∈ latA D cc N N' := by
  rintro _ ⟨ζ, hζ, rfl⟩ i j
  rw [actA_apply, Matrix.smul_apply, Matrix.mul_apply, Finset.smul_sum]
  refine sum_mem fun l _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul, Finset.smul_sum]
  refine sum_mem fun k _ => ?_
  convert ihE_mul D cc (mul_mem (h l j) (h' i k)) (hζ k l) using 1
  rw [nsmul_eq_mul]
  push_cast
  ring

end GlobalTheory.FinWeil.MovedIdx

open GlobalTheory.FinWeil.MovedIdx in

theorem GlobalTheory.FinWeil.idx_map_actA : ∀ (D : D7), admG1 D → ∀ (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → ∀ (N N' : ℕ) (g : GA D N) (g' : GA D N'), idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 ∧ (∀ q : ℕ, q.Prime → TrivAt D q (g : GL (Fin N) (AE D)) → TrivAt D q (g' : GL (Fin N') (AE D)) → ¬ q ∣ idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g')))) ∧ (IntG D (g : GL (Fin N) (AE D)) → IntG D (g' : GL (Fin N') (AE D)) → (latA D cc N N').map (actA D N N' (g, g')) ≤ latA D cc N N') := by
  intro D hD cc δ hC N N' g g'
  have h0 : idx (latA D cc N N') ((latA D cc N N').map (actA D N N' (g, g'))) ≠ 0 := by
    obtain ⟨n, hn, h⟩ := denom_mat D (((g : GL (Fin N) (AE D))⁻¹ : GL (Fin N) (AE D)) : Matrix (Fin N) (Fin N) (AE D))
    obtain ⟨n', hn', h'⟩ := denom_mat D ((g' : GL (Fin N') (AE D)) : Matrix (Fin N') (Fin N') (AE D))
    exact GlobalTheory.T.heisenbergRelativeIndex_completedStandard_ne_zero D hD cc δ hC N N' _ (Nat.mul_pos hn hn') _ (nsmul_mem_latA D cc g g' h h')
  refine ⟨h0, fun q hq hg hg' hd => ?_, fun hg hg' ζ hζ => ?_⟩
  · obtain ⟨n, hn, h⟩ := denom_triv_inv D hq hg
    obtain ⟨n', hn', h'⟩ := denom_triv D hg'
    exact (Nat.Prime.coprime_iff_not_dvd hq).1 (Nat.Coprime.mul_left hn hn').symm
      (dvd_of_dvd_idx _ _ _ q hq h0 (nsmul_mem_latA D cc g g' h h') hd)
  · have := nsmul_mem_latA D cc g g' (n := 1) (n' := 1) (fun i j => by simpa using (hg i j).2)
      (fun i j => by simpa using (hg' i j).1) ζ hζ
    simpa using this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralKerSumGraphEq
section
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical

namespace GlobalTheory.UnitaryTheta.Graph

theorem integral_kerSum_graph_eq : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (H : Sesq V), IsPosHerm H → ∀ a : V ≃ₗ[ℂ] V, (∀ z w, H (a z) (a w) = H z w) → LinearMap.det (1 - (a : V →ₗ[ℂ] V)) ≠ 0 → ∀ (B : V →ₗ[ℂ] V), (∀ x, B x - a (B x) = x) → ∀ (Λ Λ' : AddSubgroup V) [DiscreteTopology Λ], Λ' ≤ Λ → (∀ y ∈ Λ', a y ∈ Λ) → ∀ α : V → ℂ, IsSemichar H Λ α → (∀ y ∈ Λ', α (a y) = α y) → ∀ Fd : Set V, IsAddFundamentalDomain Λ' Fd μ → ∀ (M : Type) [Fintype M] (s : M → V), (∀ m, s m ∈ Λ) → (∀ x ∈ Λ, ∃! p : M × Λ', x = s p.1 - ((p.2 : V) - a p.2)) → ∃ κ : ℝ, 0 < κ ∧ ∫ z in Fd, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) * ∑ m, α (s m) * cexp (-((π : ℂ) * I) * ((H (B (s m)) (s m)).im : ℂ)) := by
  intro V _ _ _ _ _ μ _ H hH a ha hdet B hB1 Λ Λ' _ hle haΛ α hα hαa Fd hFd M _ s hs huniq
  haveI : ProperSpace V := FiniteDimensional.proper ℂ V
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  haveI : Countable Λ' := (AddSubgroup.inclusion_injective hle).countable
  obtain ⟨κ, hκ, hg⟩ := integral_gaussian_unitary_pos V μ H hH a ha hdet
  refine ⟨κ, hκ, ?_⟩
  have hint : ∀ x, Integrable (term H a α x) μ := fun x => by
    have : term H a α x = _ := funext fun z => term_eq H a ha α x (B x) z (hB1 x)
    rw [this]
    exact (hg (B x) _).1.const_mul _
  have hval : ∀ x, ∫ z, term H a α x z ∂μ = κ / LinearMap.det (1 - (a : V →ₗ[ℂ] V)) *
      (α x * cexp (-((π : ℂ) * I) * ((H (B x) x).im : ℂ))) := fun x => by
    simp only [fun z => term_eq H a ha α x (B x) z (hB1 x)]
    rw [integral_const_mul, (hg (B x) _).2, ← value_eq H hH a ha x (B x) (hB1 x)]
    ring
  let f : M × Λ' → Λ := fun p => ⟨s p.1 - ((p.2 : V) - a p.2),
    Λ.sub_mem (hs _) (Λ.sub_mem (hle p.2.2) (haΛ _ p.2.2))⟩
  have hf : Function.Bijective f := by
    constructor
    · intro p q hpq
      exact (huniq _ (f p).2).unique rfl (congrArg Subtype.val hpq)
    · intro x
      obtain ⟨p, hp, -⟩ := huniq x x.2
      exact ⟨p, Subtype.ext hp.symm⟩
  have hsum : ∀ z, kerSum H Λ α z (a z) * cexp (-(π : ℂ) * H z z) =
      ∑ m, ∑' y : Λ', term H a α (s m) (z + y) := fun z => by
    have h1 : Summable (fun x : Λ => term H a α x z) :=
      ((GlobalTheory.UnitaryTheta.KerSum.kerSum_spec V H hH Λ α hα).1 (a z) z).mul_right _
    have h2 := (Equiv.ofBijective f hf).summable_iff.2 h1
    rw [kerSum, ← tsum_mul_right]
    change ∑' x : Λ, term H a α x z = _
    rw [← (Equiv.ofBijective f hf).tsum_eq]
    refine (h2.tsum_prod).trans ?_
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun m _ => tsum_congr fun y => ?_
    exact term_shift H hH a ha Λ α hα (s m) y z (hs m) (hle y.2) (haΛ _ y.2) (hαa _ y.2)
  have hu := fun m => GlobalTheory.integral_unfold_fundamentalDomain V μ Λ' Fd hFd _ (hint (s m))
  simp only [hsum]
  rw [integral_finset_sum _ (fun m _ => (hu m).1)]
  simp only [fun m => (hu m).2, hval]
  rw [← Finset.mul_sum]

end GlobalTheory.UnitaryTheta.Graph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InvariantMeasureLowerBoundOfChart
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory

namespace GlobalTheory.CartanInt

theorem invariant_measure_lower_bound_of_chart :
    ∀ (G ι : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Fintype ι] (mK : Measure G) [IsProbabilityMeasure mK] (K U : Set G) (θ : (ι → ℝ) → G) (T δ : ℝ), Continuous θ → IsClosed U → mK Kᶜ = 0 → (∀ R, Measure.map (fun x => θ R * x) mK = mK) → 0 < δ → 0 ≤ T → (∀ x ∈ K, ∃ R₀ : ι → ℝ, (∀ i, |R₀ i| ≤ T) ∧ ∀ R : ι → ℝ, (∀ i, |R i - R₀ i| ≤ δ) → (θ R)⁻¹ * x ∈ U) → ENNReal.ofReal ((δ / (T + δ)) ^ Fintype.card ι) ≤ mK U := by
  intro G ι _ _ _ _ _ _ _ mK _ K U θ T δ hθ hU hK hinv hδ hT hch
  have hTδ : 0 < T + δ := by linarith
  set Q : Set (ι → ℝ) := Metric.closedBall 0 (T + δ) with hQ
  set S : Set ((ι → ℝ) × G) := {p | (θ p.1)⁻¹ * p.2 ∈ U} with hS
  have hSc : IsClosed S := hU.preimage (by fun_prop : Continuous fun p : (ι → ℝ) × G => (θ p.1)⁻¹ * p.2)
  have hSm : MeasurableSet S := hSc.measurableSet
  have hQv : volume Q = ENNReal.ofReal ((2 * (T + δ)) ^ Fintype.card ι) :=
    Real.volume_pi_closedBall _ hTδ.le
  have hsec : ∀ R, mK (Prod.mk R ⁻¹' S) = mK U := by
    intro R
    have hm : MeasurableSet (Prod.mk R ⁻¹' S) := measurable_prodMk_left hSm
    conv_lhs => rw [← hinv R]
    rw [Measure.map_apply (by fun_prop) hm]
    congr 1
    ext x
    simp [hS]
  have h1 : ((volume.restrict Q).prod mK) S = mK U * volume Q := by
    rw [Measure.prod_apply hSm]
    simp [hsec]
  have h2 : ENNReal.ofReal ((2 * δ) ^ Fintype.card ι) ≤ ((volume.restrict Q).prod mK) S := by
    rw [Measure.prod_apply_symm hSm]
    have hae : ∀ᵐ x ∂mK, x ∈ K := hK
    calc ENNReal.ofReal ((2 * δ) ^ Fintype.card ι)
        = ∫⁻ _x, ENNReal.ofReal ((2 * δ) ^ Fintype.card ι) ∂mK := by simp
      _ ≤ _ := by
        refine lintegral_mono_ae (hae.mono fun x hx => ?_)
        obtain ⟨R₀, hR₀, hR⟩ := hch x hx
        have hm : MeasurableSet ((fun R => (R, x)) ⁻¹' S) := measurable_prodMk_right hSm
        rw [Measure.restrict_apply hm, ← Real.volume_pi_closedBall R₀ hδ.le]
        refine measure_mono fun R hRm => ?_
        have hd : ∀ i, |R i - R₀ i| ≤ δ := fun i => by
          have := (dist_pi_le_iff hδ.le).1 (Metric.mem_closedBall.1 hRm) i
          rwa [Real.dist_eq] at this
        refine ⟨hR R hd, ?_⟩
        rw [hQ, Metric.mem_closedBall, dist_pi_le_iff hTδ.le]
        intro i
        have h3 := abs_le.1 (hd i)
        have h4 := abs_le.1 (hR₀ i)
        rw [Real.dist_eq, Pi.zero_apply, sub_zero, abs_le]
        constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]
  rw [h1, hQv] at h2
  have hpos : 0 < (2 * (T + δ)) ^ Fintype.card ι := by positivity
  have he : (δ / (T + δ)) ^ Fintype.card ι
      = (2 * δ) ^ Fintype.card ι / (2 * (T + δ)) ^ Fintype.card ι := by
    rw [← div_pow, mul_div_mul_left _ _ (two_ne_zero)]
  rw [he, ENNReal.ofReal_div_of_pos hpos]
  exact ENNReal.div_le_of_le_mul h2

end GlobalTheory.CartanInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IrreducibleCompletionOfGradedIrreducibleGK
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

namespace GlobalTheory

theorem irrU_of_dense_graded_irrGK :
    ∀ (p q : ℕ) (T : GrpData p q) (σ : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] σ.H), Function.Injective j → Dense (Set.range j) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => σ.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) → IrrGK M → ∀ (N : ℕ → Submodule ℂ M.V) (k : T.G) (lam : ℕ → ℂ), (∀ m, FiniteDimensional ℂ (N m)) → (⨆ m, N m) = ⊤ → k ∈ T.Kset → Function.Injective lam → (∀ m, ∀ x ∈ N m, σ.π k (j x) = lam m • j x) → IrrU σ := by
  intro p q T σ M j hinj hd hder hirr N k lam hfin hN _ hlam heig
  haveI := hirr.1
  refine ⟨hinj.nontrivial, fun S hS hinv => ?_⟩
  haveI : CompleteSpace S := hS.completeSpace_coe
  have hreal : ∀ Y ∈ upq p q, ∀ y, j y ∈ S → j (M.act Y y) ∈ S := by
    intro Y hY y hy
    rw [← S.orthogonal_orthogonal, Submodule.mem_orthogonal]
    intro w hw
    have h1 := ((innerSL ℂ w).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hder Y hY y)
    have h2 : HasDerivAt (fun _ : ℝ => (0 : ℂ)) (inner ℂ w (j (M.act Y y))) 0 := by
      refine HasDerivAt.congr_of_eventuallyEq h1 (Filter.Eventually.of_forall fun t => ?_)
      exact (Submodule.inner_left_of_mem_orthogonal (hinv _ _ hy) hw).symm
    exact h2.unique (hasDerivAt_const _ _)
  have hstab : ∀ Z, ∀ y ∈ S.comap j, M.act Z y ∈ S.comap j := by
    intro Z y hy
    obtain ⟨X, hX, Y, hY, rfl⟩ := GlobalTheory.FockTensor.exists_upq_add Z
    rw [Submodule.mem_comap] at hy ⊢
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply]
    exact S.add_mem (hreal X hX y hy) (S.smul_mem _ (hreal Y hY y hy))
  rcases hirr.2 _ hstab with h | h
  · left
    have hperp : ∀ b ∈ Sᗮ, σ.π k b ∈ Sᗮ := by
      intro b hb
      rw [Submodule.mem_orthogonal']
      intro u hu
      rw [GlobalTheory.FockTensor.inner_pi_left]
      exact Submodule.inner_left_of_mem_orthogonal (hinv _ _ hu) hb
    have hdense : Dense ((⨆ m, (N m).map j : Submodule ℂ σ.H) : Set σ.H) := by
      rw [← Submodule.map_iSup, hN, Submodule.map_top]
      exact hd
    have hle : (⨆ m, (N m).map j : Submodule ℂ σ.H) ≤ Sᗮ := by
      refine iSup_le fun m => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, b, hb, hab⟩ := S.exists_add_mem_mem_orthogonal (j x)
      have he := heig m x hx
      rw [hab, map_add, smul_add] at he
      have hdiff : σ.π k a - lam m • a = lam m • b - σ.π k b := by
        rw [sub_eq_sub_iff_add_eq_add, he, add_comm]
      have h1 : σ.π k a - lam m • a ∈ S := S.sub_mem (hinv _ _ ha) (S.smul_mem _ ha)
      have h2 : σ.π k a - lam m • a ∈ Sᗮ := by
        rw [hdiff]
        exact Sᗮ.sub_mem (Sᗮ.smul_mem _ hb) (hperp b hb)
      have h3 : σ.π k a = lam m • a :=
        sub_eq_zero.1 (inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal h1 h2))
      have h4 := GlobalTheory.mem_of_isometry_eigen_of_dense_iSup σ.H (σ.π k) (σ.isom k)
        (fun m => (N m).map j) lam hlam (fun m => by haveI := hfin m; infer_instance)
        (by rintro m _ ⟨x, hx, rfl⟩; exact heig m x hx) hdense m a h3
      obtain ⟨x', -, hx'⟩ := h4
      have h5 : x' ∈ S.comap j := by rw [Submodule.mem_comap, hx']; exact ha
      rw [h, Submodule.mem_bot] at h5
      rw [h5, map_zero] at hx'
      rw [hab, ← hx', zero_add]
      exact hb
    rw [← Submodule.orthogonal_eq_top_iff, eq_top_iff]
    intro v _
    exact closure_minimal hle S.isClosed_orthogonal (hdense v)
  · right
    rw [eq_top_iff]
    intro v _
    refine closure_minimal ?_ hS (hd v)
    rintro _ ⟨x, rfl⟩
    have : x ∈ S.comap j := by rw [h]; trivial
    exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreservedStatement
section
open NumberField IsDedekindDomain MvPolynomial Formalism.BasicNotions Formalism.L2.DIV Formalism.DivisionValues GlobalTheory.TestLat Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open scoped Matrix ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nablaDeltaOperator_lattice_preserved : NabDelLattice := by
  first | exact @GlobalTheory.TransLattice.nabDelLattice | exact GlobalTheory.TransLattice.nabDelLattice | (intros; apply GlobalTheory.TransLattice.nabDelLattice <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinaryEisensteinEigenfunctionalExistsStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ordinaryEisensteinEigenfunctional_exists : GlobalTheory.EisM.CuspidalUnitaryTwistsClaim := by
  first | exact @GlobalTheory.EisM.chapterM_holds | exact GlobalTheory.EisM.chapterM_holds | (intros; apply GlobalTheory.EisM.chapterM_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SigmaStarSquareQuotientInModelParameterStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigmaStarSquareQuotient_in_model_parameter : ∀ (p : ℕ) [Fact p.Prime] (g : GL3Theta.G1 p), IsWq g.W g.wq → IsLat g.abelian₂ → g2 g.abelian₂ ∈ Qbar → g3 g.abelian₂ ∈ Qbar → AlgEnt (sgStar g.abelian₂) → ∀ v, v ∉ g.abelian₂ → wpF g.abelian₂ v ∈ Qbar → AlgEnt (sqTh g.abelian₂ v) ∧ g.atU (sqTh g.abelian₂ v) = ePhi1 g.lam g.abelian₂ g.C g.wq ^ 2 * lineSer g.wq⁻¹ (xAt g v) := by
  first | exact @GlobalTheory.EvenTheta.Param.sqTh_atU | exact GlobalTheory.EvenTheta.Param.sqTh_atU | (intros; apply GlobalTheory.EvenTheta.Param.sqTh_atU <;> assumption)
end

