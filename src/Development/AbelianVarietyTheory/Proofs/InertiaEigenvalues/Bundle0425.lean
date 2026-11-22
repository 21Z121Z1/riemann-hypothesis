import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResEqIff
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0014
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0399
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0395
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0015
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DeltaStructureOfWittLengthTwoSection
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRingCornerIdealModuleIff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0396
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBound
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLt
section
noncomputable section
namespace GlobalTheory.WildMove
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc GlobalTheory.MemLoc.FrobLaws
open scoped Formalism.Per

private theorem charP_closedBallSubring_quotient_openBallIdeal {l : ℕ} [hl : Fact l.Prime] :
    CharP (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸ GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) l := by
  have hM := GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal (PadicAlgCl l)
  have : (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)).IsPrime := hM.isPrime
  refine (CharP.charP_iff_prime_eq_zero hl.out).2 ?_
  rw [← map_natCast (Ideal.Quotient.mk _), Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
  have e : ((l : PadicAlgCl l)) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := (map_natCast _ l).symm
  push_cast
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_p_lt_one

private theorem exists_norm_pow_prime_pow_sub_lt_one {l : ℕ} [hl : Fact l.Prime] (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) :
    ∃ f : ℕ, 0 < f ∧ ‖a ^ (l ^ f) - a‖ < 1 := by
  classical
  have : NeZero l := ⟨hl.out.ne_zero⟩
  set O := GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) with hO
  set M := GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l) with hM
  have : M.IsMaximal := GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal _
  let : Field (O ⧸ M) := Ideal.Quotient.field M
  have : CharP (O ⧸ M) l := charP_closedBallSubring_quotient_openBallIdeal
  let : Algebra (ZMod l) (O ⧸ M) := ZMod.algebra _ l

  have hcoef : ∀ c : ℚ_[l], ‖c‖ ≤ 1 → ∀ h : algebraMap ℚ_[l] (PadicAlgCl l) c ∈ O,
      Ideal.Quotient.mk M ⟨_, h⟩ ∈ Set.range (algebraMap (ZMod l) (O ⧸ M)) := by
    intro c hc h
    have key : ∀ x : ℤ_[l], ∃ n : ℕ, ‖(x : ℚ_[l]) - n‖ < 1 := by
      intro x
      obtain ⟨n, -, hn⟩ := PadicInt.exists_mem_range (x := x)
      rw [IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def, PadicInt.coe_sub,
        PadicInt.coe_natCast] at hn
      exact ⟨n, hn⟩
    obtain ⟨n, hn'⟩ := key ⟨c, hc⟩
    refine ⟨(n : ZMod l), ?_⟩
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk M), Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
    have e : ((n : PadicAlgCl l)) = algebraMap ℚ_[l] (PadicAlgCl l) (n : ℚ_[l]) := (map_natCast _ n).symm
    push_cast
    rw [e, ← map_sub, PadicAlgCl.norm_extends, norm_sub_rev]
    exact hn'

  have hint : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  set P := minpoly ℚ_[l] a with hP
  have hPm : P.Monic := minpoly.monic hint
  have hPc : ∀ n, ‖P.coeff n‖ ≤ 1 := by
    have h1 : spectralValue P ≤ 1 := by
      rw [← PadicAlgCl.spectralNorm_eq] at ha
      exact ha
    exact (spectralValue_le_one_iff hPm).1 h1
  set Pm := P.map (algebraMap ℚ_[l] (PadicAlgCl l)) with hPm'
  have hPmO : ∀ n, Pm.coeff n ∈ O := by
    intro n
    rw [Polynomial.coeff_map, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring, PadicAlgCl.norm_extends]
    exact hPc n
  have hsub : (↑Pm.coeffs : Set (PadicAlgCl l)) ⊆ O := by
    intro x hx
    obtain ⟨n, -, hn⟩ := Polynomial.mem_coeffs_iff.1 hx
    rw [hn]
    exact hPmO n
  set Q := Pm.toSubring O hsub with hQ
  set Qb := Q.map (Ideal.Quotient.mk M) with hQb
  have hQm : Qb.Monic := ((Polynomial.monic_toSubring _ _ _).2 (hPm.map _)).map _
  have hlift : Qb ∈ Polynomial.lifts (algebraMap (ZMod l) (O ⧸ M)) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [hQb, Polynomial.coeff_map]
    have e : Q.coeff n = ⟨algebraMap ℚ_[l] (PadicAlgCl l) (P.coeff n), by
        rw [← Polynomial.coeff_map]; exact hPmO n⟩ := by
      apply Subtype.ext
      rw [hQ, Polynomial.coeff_toSubring]
      exact Polynomial.coeff_map _ _
    rw [e]
    exact hcoef _ (hPc n) _
  set a' : O := ⟨a, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring.2 ha⟩ with ha'
  have hQa : Q.eval a' = 0 := by
    apply Subtype.ext
    show O.subtype (Q.eval a') = 0
    rw [← Polynomial.eval₂_at_apply, ← Polynomial.eval_map, hQ, Polynomial.map_toSubring]
    show Pm.eval a = 0
    rw [hPm', Polynomial.eval_map, ← Polynomial.aeval_def, hP, minpoly.aeval]
  have hroot : Qb.eval (Ideal.Quotient.mk M a') = 0 := by
    rw [hQb, Polynomial.eval_map, Polynomial.eval₂_at_apply, hQa, map_zero]
  obtain ⟨R, hRmap, -, hRmon⟩ := Polynomial.lifts_and_degree_eq_and_monic hlift hQm
  have hab : IsIntegral (ZMod l) (Ideal.Quotient.mk M a') :=
    ⟨R, hRmon, by rw [← Polynomial.eval_map, hRmap]; exact hroot⟩

  have := IntermediateField.adjoin.finiteDimensional hab
  have : Finite (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) :=
    Module.finite_of_finite (ZMod l)
  let : Fintype (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) := Fintype.ofFinite _
  have hcard : Fintype.card (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) =
      l ^ Module.finrank (ZMod l) (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}) := by
    rw [Module.card_eq_pow_finrank (K := ZMod l), ZMod.card]
  have hx := FiniteField.pow_card (⟨Ideal.Quotient.mk M a', IntermediateField.mem_adjoin_simple_self _ _⟩ :
    IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})
  rw [hcard] at hx
  have hx' := congrArg Subtype.val hx
  simp only [SubmonoidClass.coe_pow] at hx'
  refine ⟨Module.finrank (ZMod l) (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'}), ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos (Module.finrank (ZMod l)
        (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})) with h0 | h0
    · have h1 := Fintype.one_lt_card (α := IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})
      rw [hcard, h0, pow_zero] at h1
      exact absurd h1 (lt_irrefl 1)
    · exact h0
  · have h2 : Ideal.Quotient.mk M (a' ^ (l ^ Module.finrank (ZMod l)
        (IntermediateField.adjoin (ZMod l) {Ideal.Quotient.mk M a'})) - a') = 0 := by
      rw [map_sub, map_pow, hx', sub_self]
    rw [Ideal.Quotient.eq_zero_iff_mem, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal] at h2
    simpa [ha'] using h2

private theorem exists_teichmuller_root_norm_sub_lt_one {l : ℕ} [hl : Fact l.Prime] (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) :
    ∃ ζ : PadicAlgCl l, (ζ = 0 ∨ ∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) ∧ ‖a - ζ‖ < 1 := by
  classical
  obtain ⟨f, hf, hlt⟩ := exists_norm_pow_prime_pow_sub_lt_one a ha
  have hl1 : 1 < l := hl.out.one_lt
  have hq1 : 1 < l ^ f := Nat.one_lt_pow hf.ne' hl1
  set q := l ^ f with hq
  set P : Polynomial (PadicAlgCl l) := Polynomial.X ^ q - Polynomial.X with hP
  have hPm : P.Monic := Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; exact_mod_cast hq1)
  have hprod := Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hPm
    IsAlgClosed.card_roots_eq_natDegree
  have heval : a ^ q - a = (P.roots.map fun r => a - r).prod := by
    have h := congrArg (Polynomial.eval a) hprod
    rw [Polynomial.eval_multiset_prod, Multiset.map_map] at h
    simpa [hP, Function.comp_def] using h.symm
  by_contra hcon
  push_neg at hcon
  have hge : ∀ r ∈ P.roots, 1 ≤ ‖a - r‖ := by
    intro r hr
    have hr' : r ^ q = r := by
      have h := Polynomial.isRoot_of_mem_roots hr
      simp only [Polynomial.IsRoot, hP, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X] at h
      exact sub_eq_zero.1 h
    by_cases h0 : r = 0
    · exact hcon r (Or.inl h0)
    · refine hcon r (Or.inr ⟨q - 1, by omega, ?_, ?_⟩)
      · intro hd
        have h2 : l ∣ q - 1 + 1 := by rw [Nat.sub_add_cancel hq1.le, hq]; exact dvd_pow_self l hf.ne'
        have h3 : l ∣ 1 := (Nat.dvd_add_right hd).1 h2
        exact hl1.ne' (Nat.dvd_one.1 h3)
      · have h4 : r ^ (q - 1) * r = 1 * r := by
          rw [← pow_succ, Nat.sub_add_cancel hq1.le, one_mul, hr']
        exact mul_right_cancel₀ h0 h4
  have key : ∀ s : Multiset (PadicAlgCl l), (∀ r ∈ s, 1 ≤ ‖a - r‖) →
      1 ≤ ‖(s.map fun r => a - r).prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | cons r s ih =>
      intro h
      rw [Multiset.map_cons, Multiset.prod_cons, norm_mul]
      exact one_le_mul_of_one_le_of_one_le (h r (Multiset.mem_cons.2 (Or.inl rfl)))
        (ih fun x hx => h x (Multiset.mem_cons.2 (Or.inr hx)))
  have h5 := key _ hge
  rw [← heval] at h5
  exact absurd hlt (not_lt.2 h5)

private theorem norm_apply_sub_lt_one_of_fixes_prime_to_l_roots {l : ℕ} [hl : Fact l.Prime] (γ : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)
    (hγ : ∀ ζ : PadicAlgCl l, (∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) → γ ζ = ζ)
    (a : PadicAlgCl l) (ha : ‖a‖ ≤ 1) : ‖γ a - a‖ < 1 := by
  obtain ⟨ζ, hζ, hlt⟩ := exists_teichmuller_root_norm_sub_lt_one a ha
  have hfix : γ ζ = ζ := by
    rcases hζ with h0 | h1
    · rw [h0, map_zero]
    · exact hγ ζ h1
  have e : γ a - a = γ (a - ζ) + -(a - ζ) := by rw [map_sub, hfix]; ring
  have hn : ‖γ (a - ζ)‖ = ‖a - ζ‖ := (spectralNorm_eq_of_equiv γ (a - ζ)).symm
  rw [e]
  refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt ?_
  rw [hn, norm_neg, max_self]
  exact hlt

private theorem apply_root_eq_of_mem_fixingSubgroup_Kur {l : ℕ} [hl : Fact l.Prime] (γ : GQ l) (hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup) :
    ∀ ζ : PadicAlgCl l, (∃ m, 0 < m ∧ ¬ l ∣ m ∧ ζ ^ m = 1) → γ ζ = ζ := by
  intro ζ hζ
  have hmem : ζ ∈ MaximalUnramifiedExtension l := by
    unfold MaximalUnramifiedExtension
    exact IntermediateField.subset_adjoin _ _ hζ
  exact hγ ⟨ζ, hmem⟩

theorem norm_sub_lt (l : ℕ) [hl : Fact l.Prime] (γ : GQ l) (hγ : γ ∈ (MaximalUnramifiedExtension l).fixingSubgroup)
    (n : ℕ) (x : Om l) (hx : x ≠ 0) (h : (γ ^ l ^ n) x = x) : ‖γ x - x‖ < ‖x‖ := by
  have hn : ∀ (g : PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l) (y : PadicAlgCl l), ‖g y‖ = ‖y‖ :=
    fun g y => (spectralNorm_eq_of_equiv g y).symm
  have hfix := apply_root_eq_of_mem_fixingSubgroup_Kur γ hγ
  have hx0 : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  have hγx : γ x ≠ 0 := by
    intro h0
    apply hx
    rw [← norm_eq_zero, ← hn γ x, h0, norm_zero]
  set u : Om l := γ x / x with hu'
  have hu : ‖u‖ = 1 := by rw [hu', norm_div, hn, div_self hx0]
  have hind : ∀ k : ℕ, ‖(γ ^ k) x / x - u ^ k‖ < 1 := by
    intro k
    induction k with
    | zero => simp [div_self hx]
    | succ k ih =>
      have hvk : ‖(γ ^ k) x / x‖ = 1 := by rw [norm_div, hn, div_self hx0]
      have e : (γ ^ (k + 1)) x / x - u ^ (k + 1) =
          ((γ ((γ ^ k) x / x) - (γ ^ k) x / x) + ((γ ^ k) x / x - u ^ k)) * u := by
        rw [show γ ^ (k + 1) = γ * γ ^ k from pow_succ' γ k, AlgEquiv.mul_apply, pow_succ u k, map_div₀, hu']
        field_simp
        ring
      rw [e, norm_mul, hu, mul_one]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (norm_apply_sub_lt_one_of_fixes_prime_to_l_roots γ hfix _ hvk.le) ih)
  have hq : ‖u ^ (l ^ n) - 1‖ < 1 := by
    have h1 := hind (l ^ n)
    rw [h, div_self hx, norm_sub_rev] at h1
    exact h1
  have hM : (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)).IsMaximal :=
    GlobalTheory.ClosedBallValuationSubring.openBallIdeal_isMaximal _
  let : Field (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸ GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) :=
    Ideal.Quotient.field _
  have : CharP (GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) ⧸
    GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) l := charP_closedBallSubring_quotient_openBallIdeal
  set u' : GlobalTheory.ClosedBallValuationSubring.closedBallSubring (PadicAlgCl l) :=
    ⟨u, GlobalTheory.ClosedBallValuationSubring.mem_closedBallSubring.2 hu.le⟩ with hu''
  have h1 : (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) u') ^ (l ^ n) = 1 := by
    rw [← map_pow, ← map_one (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l))),
      Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal]
    simpa [hu''] using hq
  have h2 : (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l)) u' - 1) ^ (l ^ n) = 0 := by
    rw [sub_pow_char_pow, h1, one_pow, sub_self]
  have h3 := pow_eq_zero_iff (pow_ne_zero n hl.out.ne_zero) |>.1 h2
  rw [sub_eq_zero, ← map_one (Ideal.Quotient.mk (GlobalTheory.ClosedBallValuationSubring.openBallIdeal (PadicAlgCl l))),
    Ideal.Quotient.eq, GlobalTheory.ClosedBallValuationSubring.mem_openBallIdeal] at h3
  have h4 : ‖u - 1‖ < 1 := by simpa [hu''] using h3
  have e : γ x - x = x * (u - 1) := by
    rw [mul_sub, mul_one, hu', mul_div_assoc', mul_comm x (γ x), mul_div_assoc, div_self hx, mul_one]
  rw [e, norm_mul]
  exact mul_lt_of_lt_one_right (norm_pos_iff.2 hx) h4

end GlobalTheory.WildMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PointGaloisRepsConjugateOverFractionField
section
noncomputable section

namespace GlobalTheory.PointRepConj

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices

theorem exists_gl_of_equiv {K Γ : Type} [Field K] {n : ℕ} (A B : Γ → Matrix (Fin n) (Fin n) K)
    (e : (Fin n → K) ≃ₗ[K] (Fin n → K))
    (he : ∀ g u, e (Matrix.toLin' (A g) u) = Matrix.toLin' (B g) (e u)) :
    ∃ P : GL (Fin n) K, ∀ g, (P : Matrix (Fin n) (Fin n) K) * A g = B g * (P : Matrix (Fin n) (Fin n) K) := by
  refine ⟨⟨LinearMap.toMatrix' (e : (Fin n → K) →ₗ[K] (Fin n → K)),
      LinearMap.toMatrix' (e.symm : (Fin n → K) →ₗ[K] (Fin n → K)), ?_, ?_⟩, ?_⟩
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · rw [← LinearMap.toMatrix'_comp]
    simp
  · intro g
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun u => ?_
    simpa [Matrix.toLin'_mul] using he g u

theorem main : GlobalTheory.TwSys.Cheb → ∀ {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (i : N.Loc) (r r' : (N.X i → (GE N →* GL (Fin R.nV) (N.O i)))), GoodR N i r → GoodR N i r' → ∀ x, (∃ Pm : GL (Fin R.nV) (KK N i), ∀ g, (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i)) * (rO N i r x g).map (toK N i) = (rO N i r' x g).map (toK N i) * (Pm : Matrix (Fin R.nV) (Fin R.nV) (KK N i))) := by
  intro hC R H what₂ N i r r' hr hr' x
  have h₁ := (GlobalTheory.ComplementCompare.isHeckeGalois_iff N i x (r x)).1 (hr x)
  have h₂ := (GlobalTheory.ComplementCompare.isHeckeGalois_iff N i x (r' x)).1 (hr' x)
  obtain ⟨e, he⟩ := GlobalTheory.ComplementCompare.isRx_unique N hC i x _ _ h₁ h₂
  exact exists_gl_of_equiv _ _ e he

end GlobalTheory.PointRepConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowDvdTiltUniformizerPowAcrisEventuallyStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primePow_dvd_tiltUniformizer_pow_acris_eventually : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (c M : ℕ), ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → (l : Per.Acris l) ^ (c * n + M) ∣ ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) X ^ (l ^ n - 1) := by
  first | exact @GlobalTheory.AcrisPow.main | exact GlobalTheory.AcrisPow.main | (intros; apply GlobalTheory.AcrisPow.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismLocalizationSpanNonZeroDivisorBoundedTorsioStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prismLocalization_span_nonZeroDivisor_bounded_torsion : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (B : Obj l R) (f d : B.A), GenAway B f d → ∀ M : Submonoid B.A, f ∈ M → B.I.map (algebraMap B.A (Localization M)) = Ideal.span {algebraMap B.A (Localization M) d} ∧ algebraMap B.A (Localization M) d ∈ nonZeroDivisors (Localization M) ∧ ∃ N : ℕ, ∀ (x : Localization M) (m : ℕ), (l : Localization M) ^ m * x ∈ Ideal.span {algebraMap B.A (Localization M) d} → (l : Localization M) ^ N * x ∈ Ideal.span {algebraMap B.A (Localization M) d} := by
  first | exact @GlobalTheory.BSP.locAway_span_nzd_bdd | exact GlobalTheory.BSP.locAway_span_nzd_bdd | (intros; apply GlobalTheory.BSP.locAway_span_nzd_bdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProdOtherRootFactorsActionFirstCoordinate
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory.RootFactorProduct

private lemma map_sub_smul_E_mulVec_eq {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c))
    (a : ℕ) (v : Fin n → FractionRing O) :
    e (((X₀ - ρ a • E).map (toFr O)).mulVec v) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1) - ρ a) * (e v).2 c) := by
  have hm : (X₀ - ρ a • E).map (toFr O) = X₀.map (toFr O) - toFr O (ρ a) • E.map (toFr O) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub, map_mul]
  have hs : ((toFr O (ρ a)) • E.map (toFr O)).mulVec v = toFr O (ρ a) • (E.map (toFr O)).mulVec v := by
    ext i
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum,
      mul_assoc]
  rw [hm, Matrix.sub_mulVec, hs, map_sub, map_smul, hX, hE]
  refine Prod.ext (by simp) ?_
  funext c
  simp only [Prod.snd_sub, Prod.smul_snd, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, map_sub]
  ring

theorem prod_cons_action {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c))
    (s : List ℕ) : ∀ (a : ℕ) (u : Fin n → FractionRing O),
      e (((((a :: s).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) =
        (0, fun c : Fin t =>
          toFr O (((a :: s).map fun c' => ρ ((c : ℕ) + 1) - ρ c').prod) * (e u).2 c) := by
  induction s with
  | nil =>
    intro a u
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    exact map_sub_smul_E_mulVec_eq e E X₀ ρ hE hX a u
  | cons b s ih =>
    intro a u
    rw [List.map_cons, List.prod_cons, Matrix.map_mul, ← Matrix.mulVec_mulVec,
      map_sub_smul_E_mulVec_eq e E X₀ ρ hE hX a, ih b u]
    refine Prod.ext rfl ?_
    funext c
    simp only [List.map_cons, List.prod_cons, map_mul, mul_assoc]

private lemma list_prod_range'_eq_prod_Ico {M : Type} [CommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∀ m : ℕ, ((List.range' m n).map g).prod = ∏ k ∈ Finset.Ico m (m + n), g k := by
  induction n with
  | zero => intro m; simp
  | succ n ih =>
    intro m
    rw [List.range'_succ, List.map_cons, List.prod_cons, ih, show m + (n + 1) = m + 1 + n by omega,
      Finset.prod_eq_prod_Ico_succ_bot (show m < m + 1 + n by omega)]

theorem prod_other_factors_action {O : Type} [CommRing O] [IsDomain O] {n r t : ℕ}
    (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O]
      ((Fin r → FractionRing O) × (Fin t → FractionRing O)))
    (E X₀ : Matrix (Fin n) (Fin n) O) (ρ : ℕ → O) (ht : 2 ≤ t)
    (hE : ∀ u, e ((E.map (toFr O)).mulVec u) = (0, (e u).2))
    (hX : ∀ u, e ((X₀.map (toFr O)).mulVec u) =
      (0, fun c : Fin t => toFr O (ρ ((c : ℕ) + 1)) * (e u).2 c)) (u : Fin n → FractionRing O) :
    e (((((List.range' 2 (t - 1)).map fun c => X₀ - ρ c • E).prod).map (toFr O)).mulVec u) =
      (0, fun c : Fin t => if (c : ℕ) = 0 then
        toFr O (∏ c' ∈ Finset.Ioc 1 t, (ρ 1 - ρ c')) * (e u).2 c else 0) := by
  have hl : List.range' 2 (t - 1) = 2 :: List.range' 3 (t - 2) := by
    rw [show t - 1 = (t - 2) + 1 by omega, List.range'_succ]
  rw [hl, prod_cons_action e E X₀ ρ hE hX, ← hl]
  refine Prod.ext rfl ?_
  funext c
  dsimp only
  split_ifs with h0
  · simp only [h0, zero_add]
    congr 2
    all_goals
      rw [list_prod_range'_eq_prod_Ico]
      apply Finset.prod_congr _ (fun _ _ => rfl)
      ext x
      simp only [Finset.mem_Ico, Finset.mem_Ioc]
      omega
  · have hc := c.isLt
    rw [List.prod_eq_zero, map_zero, zero_mul]
    exact List.mem_map.2 ⟨(c : ℕ) + 1, List.mem_range'_1.2 ⟨by omega, by omega⟩, sub_self _⟩

end GlobalTheory.RootFactorProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PureOfAttachedStatement
section
open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_of_attached : ∀ (D : D7) (bkP : BlochKatoReduction.BK D) (i : D.ntw.Tw) (s : D.ntw.Sig i), TripleAtt D.naut bkP i s → ∃ ι, Pure i s ι := by
  first | exact @GlobalTheory.TripleGal.pure_of_tripleAtt | exact GlobalTheory.TripleGal.pure_of_tripleAtt | (intros; apply GlobalTheory.TripleGal.pure_of_tripleAtt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationTwoAndConjugationAtQAndDStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aux_statement : ∀ D : D7, EmbeddingTypeJumps.Conclusion1 D := by
  first | exact @GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d | exact GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d | (intros; apply GlobalTheory.PrimesQD.ramification_two_and_conjugation_at_q_and_d <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankEqOfActsThroughFirstBlock
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.SpanRing

namespace GlobalTheory

theorem _root_.GlobalTheory.rank_eq_of_acts_through_first_block {K : Type} [Field K] {n r t : ℕ}
    (e : (Fin n → K) ≃ₗ[K] ((Fin r → K) × (Fin t → K))) (F : Matrix (Fin n) (Fin n) K)
    (ε : Matrix (Fin r) (Fin r) K) (h : ∀ u, e (F.mulVec u) = (ε.mulVec (e u).1, 0)) :
    F.rank = ε.rank := by
  have key : (LinearMap.range F.mulVecLin).map (e : (Fin n → K) →ₗ[K] _) =
      (LinearMap.range ε.mulVecLin).map (LinearMap.inl K (Fin r → K) (Fin t → K)) := by
    ext ⟨a, b⟩
    simp only [Submodule.mem_map, LinearMap.mem_range, Matrix.mulVecLin_apply]
    constructor
    · rintro ⟨_, ⟨u, rfl⟩, hx⟩
      rw [LinearEquiv.coe_coe, h] at hx
      exact ⟨_, ⟨(e u).1, rfl⟩, by simpa using hx⟩
    · rintro ⟨_, ⟨v, rfl⟩, hx⟩
      refine ⟨_, ⟨e.symm (v, 0), rfl⟩, ?_⟩
      rw [LinearEquiv.coe_coe, h]
      simpa using hx
  unfold Matrix.rank
  rw [← LinearEquiv.finrank_map_eq e, key]
  exact (Submodule.equivMapOfInjective _ LinearMap.inl_injective _).finrank_eq.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RatioInvariantInK0Statement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratio_invariant_in_K0 : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (a b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, P.actQ g a * b = a * P.actQ g b) → ∃ c : ↥(K0 K), a = algebraMap ↥(K0 K) P.R.B c * b := by
  first | exact @GlobalTheory.Per.FracInv.tied_frac_invariant | exact GlobalTheory.Per.FracInv.tied_frac_invariant | (intros; apply GlobalTheory.Per.FracInv.tied_frac_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RegularAndBoundedTorsionOfAdicTopologicalBasisStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_and_bounded_torsion_of_adicTopologicalBasis : ∀ (l : ℕ) [Fact l.Prime] (A : Type) [CommRing A] (Q : Type) [CommRing Q] (i : A →+* Q) (d : A) (N : ℕ) (ι : Type), d ∈ nonZeroDivisors A → (∀ (x : A) (m : ℕ), (l : A) ^ m * x ∈ Ideal.span {d} → (l : A) ^ N * x ∈ Ideal.span {d}) → TopBasis i (Ideal.span {(l : A)} ⊔ Ideal.span {d}) ι → i d ∈ nonZeroDivisors Q ∧ ∀ (x : Q) (m : ℕ), (l : Q) ^ m * x ∈ Ideal.span {i d} → (l : Q) ^ N * x ∈ Ideal.span {i d} := by
  first | exact @GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded | exact GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded | (intros; apply GlobalTheory.BSP.TopBasis.regular_and_torsion_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerDeterminantOrderBoundStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residual_selmer_determinant_order_bound : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), GalHyp bkP i s → FirstHalf i s → Recip bkP i s → EqDim bkP i s → ResBound bkP i s := by
  first | exact @GlobalTheory.ResOrder.resBound | exact GlobalTheory.ResOrder.resBound | (intros; apply GlobalTheory.ResOrder.resBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomEqOfIsAdicCompletionMapStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_eq_of_isAdicCompletionMap : ∀ (L : Type) [CommRing L] (Q : Type) [CommRing Q] (C : Type) [CommRing C] (i : L →+* Q) (J : Ideal L) (JC : Ideal C), IsCompl i J → IsHausdorff JC C → ∀ (h h' : Q →+* C), J.map (h.comp i) ≤ JC → h.comp i = h'.comp i → h = h' := by
  first | exact @GlobalTheory.BSP.ringHom_eq_of_isCompl | exact GlobalTheory.BSP.ringHom_eq_of_isCompl | (intros; apply GlobalTheory.BSP.ringHom_eq_of_isCompl <;> assumption)
end

