import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyUnramifiedLift
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0409
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0398
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0389
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0390
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0403
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0397
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0408
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0410
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0381
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0391
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedH1CardInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0275
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesEqOfCongruentValuesAtPrimitiveRoots

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CohomologyUnramifiedLiftStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomology_unramified_lift : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (y z : G ℚ Ω → Fin 2 → Qbar l) (u : G ℚ Ω → Qbar l) (S' : Finset Pl) (n : ℕ), 1 ≤ n → (∀ s i j, mat W s i j ∈ c.O) → y ∈ Z1 (Loc.colRep W) → z ∈ Z1 (Loc.colRep (dual1 W)) → (∀ s i, y s i ∈ c.O) → (∀ s i, z s i ∈ c.O) → Unr W y → (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Ine (F := ℚ) B, z s = mat (dual1 W) s *ᵥ x - x) → (∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c.O) ∧ ∀ s ∈ Dec (F := ℚ) A, z s = mat (dual1 W) s *ᵥ x - x) → (∀ w : Pl, w ∉ S' → l ^ n ∣ normV w - 1 → ∀ ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n)), KillsMu (normV w) ψ → Function.Surjective ψ → Tame c W y n w ψ) → Continuous u → (∀ s, u s ∈ c.O) → (∀ s, ∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cg n (u (s * a)) (u s)) → (∀ s t, Cg n (cup W y z s t) (eps l s * u t - u (s * t) + u s)) → ∀ σ ∈ ⁅H0g W, H0g W⁆, Cg n ((mat W σ - 1).det * ht W y z u σ) 0 := by
  first | exact @GlobalTheory.Ord2.ht_vanish_commutator | exact GlobalTheory.Ord2.ht_vanish_commutator | (intros; apply GlobalTheory.Ord2.ht_vanish_commutator <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalModPrimePowCommutesHeckeDiamondStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFunctionalModPrimePow_commutes_hecke_diamond : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w d : ℕ), Odd w → d.Coprime N → ∀ b : X.Fn l, b ∈ X.B N l w →
  (∀ q : ℕ, q.Prime → ¬ q ∣ N * l → ∀ r, CgA A l n ((thN X A N l n d (X.heckeT N l q b)).coeff r)
      ((hq ε q (thN X A N l n d b) + ((q : Ω) ^ (w + 1)) • vq q (thN X A N l n (d * q) b)).coeff r)) ∧
  (∀ r, CgA A l n ((thN X A N l n d (X.heckeU l b)).coeff r) ((uq l (thN X A N l (n + 1) d b)).coeff r)) ∧
  (∀ a : ℕ, a.Coprime N → ∀ r, CgA A l n ((thN X A N l n d (X.diam N l a b)).coeff r) ((thN X A N l n (d * a) b).coeff r)) := by
  first | exact @GlobalTheory.CyclotomicQExpansion.thN_hecke | exact GlobalTheory.CyclotomicQExpansion.thN_hecke | (intros; apply GlobalTheory.CyclotomicQExpansion.thN_hecke <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerUnboundedOrderNonzeroOrdinaryClass
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem gw_limit : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ¬ GrZero (dual1 W) A := by
  intro hL l _ Ω _ _ _ e S A W hW c hc H hGr
  have h1 := GlobalTheory.T.continuous_galoisRepRankTwoTateDual_of_ordinaryNormalForm l Ω e S A W hW
  have h2 := GlobalTheory.T.galoisRepRankTwoTateDual_matrix_mem_coefRing_of_normalForm_alt l Ω e S A W hW c hc
  have h3 := GlobalTheory.T.galoisRepRankTwoTateDual_exists_no_eigenvalue_one l Ω e S A W hW
  have h4 := GlobalTheory.T.galoisRepRankTwoTateDual_eq_one_of_mem_ker_unramifiedQuotient l Ω e S A W hW
  have h5 := GlobalTheory.T.galoisRepRankTwoTateDual_upperTriangular_decompositionGroup l Ω e S A W hW
  have hunb := GlobalTheory.T.exists_cocycle_local_conditions l Ω S A (dual1 W) c h2 h3 H
  have hfin := GlobalTheory.T.finite_lTorsion_selmer_rank_two_adjoint hL l Ω S A (dual1 W) c hW.above h1 h2 h4
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.T.exists_divisible_chain_primary_torsion_group l (DivSel c (dual1 W) S A) (divSel_torsion c (dual1 W) S A) hfin hunb
  obtain ⟨a, N, p1, p2, p3, p4, p5, p6, p7, p8⟩ := GlobalTheory.T.divisibleOrdinarySelmerChain_exists_integral_representatives l Ω S A (dual1 W) c h1 h2 h4 h5 x hx0 hx
  exact GlobalTheory.T.nonzero_ordinary_class_of_compatible_cocycles_mod_pow l Ω S A (dual1 W) c h1 h2 h3 a N p1 p2 p3 p4 p5 p6 p7 p8 hGr

end GlobalTheory.Ord2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInPrimitiveRootOfInertiaFixedStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ n) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ Q : Polynomial Ω, (∀ d, Q.coeff d ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s (Q.coeff d) = Q.coeff d) ∧ Q.eval ζ = u := by
  first | exact @GlobalTheory.ZetaPoly.exists_poly | exact GlobalTheory.ZetaPoly.exists_poly | (intros; apply GlobalTheory.ZetaPoly.exists_poly; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialPrimitiveRootOfCyclotomicInertia
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.CycIne

theorem exists_poly_of_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ P.eval ζ = u := by
  intro l _ Ω _ _ _ A hA m ζ hζ u hu hfix
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · refine ⟨Polynomial.C u, ?_, by simp⟩
    intro x hx
    have hxu : x = u := by
      obtain ⟨n, hn, rfl⟩ := Polynomial.mem_coeffs_iff.1 hx
      rw [Polynomial.mem_support_iff, Polynomial.coeff_C] at hn
      rw [Polynomial.coeff_C]
      split_ifs at hn ⊢ with h
      · rfl
      · exact absurd rfl hn
    subst hxu
    haveI : Subsingleton (ZMod (l ^ 0)) := by rw [pow_zero]; infer_instance
    exact ⟨hu, fun s hs => hfix s hs (Units.ext (Subsingleton.elim _ _))⟩
  · obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_poly_in_root_of_inertia_cyclotomic_fixed l Ω A m ζ hζ u hfix
    have hl : A.valuation (l : Ω) < 1 := by
      obtain ⟨v, hv, hlv⟩ := hA
      have := (hv (l : 𝓞 ℚ)).2 hlv
      simpa using this
    let K : Subfield Ω := (IntermediateField.fixedField (Ine (F := ℚ) A)).toSubfield
    have hK : ∀ x, x ∈ K ↔ ∀ s ∈ Ine (F := ℚ) A, s x = x := fun x =>
      IntermediateField.mem_fixedField_iff _ x
    obtain ⟨P, hP, hPe⟩ := GlobalTheory.T.exists_integral_poly_eval_zeta_of_totally_ramified l Ω A hl K
      (fun x hx hx0 => GlobalTheory.T.inertia_fixed_valuation_eq_zpow_prime_valuation l Ω A hA x hx0 ((hK x).1 hx)) m hm ζ hζ
      (GlobalTheory.T.valuationSubring_primitiveRoot_sub_one_pow_totient_charZero l Ω A m hm ζ hζ) u hu ⟨Q, fun x hx => (hK x).2 (hQ x hx), hQe⟩
    exact ⟨P, fun x hx => ⟨(hP x hx).1, (hK x).1 (hP x hx).2⟩, hPe⟩

end GlobalTheory.CycIne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveCharacterTwist
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp

namespace GlobalTheory.KZ.Cmp.PrimChar

variable {l : ℕ} [Fact l.Prime]

theorem norm_sub_lt_one_trans {x y z : Qbar l} (h1 : ‖x - y‖ < 1) (h2 : ‖y - z‖ < 1) : ‖x - z‖ < 1 := by
  have : x - z = (x - y) + (y - z) := by ring
  rw [this]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h2)

theorem norm_eq_one_of_pow {x : Qbar l} {n : ℕ} (hn : n ≠ 0) (h : x ^ n = 1) : ‖x‖ = 1 := by
  have : ‖x‖ ^ n = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn).1 this

theorem norm_pow_sub_pow_lt_one {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (h : ‖x - y‖ < 1) (n : ℕ) :
    ‖x ^ n - y ^ n‖ < 1 :=
  _root_.GlobalTheory.PowerDifferenceNorm.norm_pow_sub_pow_lt_one hx hy h n

theorem norm_natCast_sub_lt_one {a b : ℕ} (h : (a : ZMod l) = (b : ZMod l)) : ‖(a : Qbar l) - b‖ < 1 := by
  obtain ⟨m, hm⟩ := ((ZMod.natCast_eq_natCast_iff a b l).1 h).symm.dvd
  have h2 : (a : Qbar l) - b = (l : Qbar l) * (m : Qbar l) := by
    have := congrArg (Int.cast : ℤ → Qbar l) hm
    push_cast at this
    exact this
  rw [h2, norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one _ m)).trans_lt
    (GlobalTheory.KZ.norm_prime_lt_one_qbar l)

theorem exists_root_close {x : Qbar l} {n : ℕ} (hn : n ≠ 0) (h : ‖x ^ n - 1‖ < 1) :
    ∃ w : Qbar l, w ^ n = 1 ∧ ‖w - x‖ < 1 := by
  haveI : NeZero n := ⟨hn⟩
  haveI : NeZero (n : Qbar l) := ⟨Nat.cast_ne_zero.2 hn⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (Qbar l) n
  have h1 := congrArg (Polynomial.eval x) (Polynomial.X_pow_sub_one_eq_prod (Nat.pos_of_ne_zero hn) hμ)
  simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_prod, Polynomial.eval_C] at h1
  rw [h1, norm_prod] at h
  by_contra hc
  push Not at hc
  refine absurd h (not_lt.2 (Finset.one_le_prod fun w hw => ?_))
  rw [norm_sub_rev]
  exact hc w ((Polynomial.mem_nthRootsFinset (Nat.pos_of_ne_zero hn) 1).1 hw)

theorem exists_teichmuller : ∃ ω : (ZMod l)ˣ →* (Qbar l)ˣ,
    ∀ x : (ZMod l)ˣ, ‖(ω x : Qbar l) - ((x : ZMod l).val : Qbar l)‖ < 1 := by
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  have hord : orderOf g = l - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units]
  have h0 : ‖(((g : ZMod l).val : ℕ) : Qbar l) ^ (l - 1) - 1‖ < 1 := by
    have := norm_natCast_sub_lt_one (l := l) (a := (g : ZMod l).val ^ (l - 1)) (b := 1) (by
      push_cast
      rw [ZMod.natCast_zmod_val, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one])
    exact_mod_cast this
  obtain ⟨w, hw, hwg⟩ := exists_root_close hl1 h0
  let w' : (Qbar l)ˣ := Units.ofPowEqOne w (l - 1) hw hl1
  have hw' : (w' : Qbar l) = w := rfl
  have hdvd : orderOf w' ∣ orderOf g := by
    rw [hord]
    apply orderOf_dvd_of_pow_eq_one
    ext
    rw [Units.val_pow_eq_pow_val, hw', hw, Units.val_one]
  refine ⟨monoidHomOfForallMemZpowers hg hdvd, fun x => ?_⟩
  obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hg x))
  rw [map_pow, monoidHomOfForallMemZpowers_apply_gen, Units.val_pow_eq_pow_val, hw']
  refine norm_sub_lt_one_trans (norm_pow_sub_pow_lt_one (norm_eq_one_of_pow hl1 hw).le
    (IsUltrametricDist.norm_natCast_le_one _ _) hwg j) ?_
  have := norm_natCast_sub_lt_one (l := l) (a := (g : ZMod l).val ^ j) (b := ((g ^ j : (ZMod l)ˣ) : ZMod l).val) (by
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val])
  exact_mod_cast this

theorem exists_wild (k : ℕ) (ζ : Qbar l) (h2 : l ≠ 2) (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (l ^ k))
    (u : (ZMod (l ^ (k + 1)))ˣ) (hu : (u : ZMod (l ^ (k + 1))) = 1 + l) :
    ∃ χ : (ZMod (l ^ (k + 1)))ˣ →* (Qbar l)ˣ, (χ u : Qbar l) = ζ ∧ ∀ b, b ^ (l - 1) = 1 → χ b = 1 := by
  have hl : l.Prime := Fact.out
  have hl2 := hl.two_le
  have hlk : l ^ k ≠ 0 := pow_ne_zero _ hl.ne_zero
  haveI : NeZero (l ^ k) := ⟨hlk⟩
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨g, hg⟩ := (ZMod.isCyclic_units_of_prime_pow l hl h2 (k + 1)).exists_generator
  have hord : orderOf g = l ^ k * (l - 1) := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow_succ hl]
  have hou : orderOf u = l ^ k := by
    rw [← orderOf_units, hu, ZMod.orderOf_one_add_prime hl h2]
  obtain ⟨a, ha⟩ := (mem_powers_iff_mem_zpowers.2 (hg u))
  simp only at ha
  have hcop : Nat.Coprime l (l - 1) := by
    rw [Nat.Prime.coprime_iff_not_dvd hl]
    intro h
    have := Nat.le_of_dvd (by omega) h
    omega
  have hla : Nat.Coprime a (l ^ k) := by
    apply Nat.Coprime.pow_right
    rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd hl]
    rintro ⟨c, rfl⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have h1 : u ^ (l ^ j * (l - 1)) = 1 := by
      rw [← ha, ← pow_mul, show l * c * (l ^ j * (l - 1)) = (l ^ (j + 1) * (l - 1)) * c by ring, ← hord, pow_mul,
        pow_orderOf_eq_one, one_pow]
    have h3 := orderOf_dvd_of_pow_eq_one h1
    rw [hou, pow_succ] at h3
    exact (Nat.Prime.coprime_iff_not_dvd hl).1 hcop (Nat.dvd_of_mul_dvd_mul_left (pow_pos hl.pos j) h3)
  obtain ⟨i, -, hi⟩ := (hζ.pow_of_coprime a hla).eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hc : (ζ ^ i) ^ (l ^ k) = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  let c : (Qbar l)ˣ := Units.ofPowEqOne (ζ ^ i) (l ^ k) hc hlk
  have hc' : (c : Qbar l) = ζ ^ i := rfl
  have hc1 : c ^ (l ^ k) = 1 := by
    ext
    rw [Units.val_pow_eq_pow_val, hc', hc, Units.val_one]
  have hdvd : orderOf c ∣ orderOf g := by
    rw [hord]
    exact (orderOf_dvd_of_pow_eq_one hc1).mul_right _
  refine ⟨monoidHomOfForallMemZpowers hg hdvd, ?_, fun b hb => ?_⟩
  · rw [← ha, map_pow, monoidHomOfForallMemZpowers_apply_gen, Units.val_pow_eq_pow_val, hc', ← pow_mul, mul_comm,
      pow_mul, hi]
  · have e1 : (monoidHomOfForallMemZpowers hg hdvd b) ^ (l - 1) = 1 := by rw [← map_pow, hb, map_one]
    have e2 : (monoidHomOfForallMemZpowers hg hdvd b) ^ (l ^ k) = 1 := by
      obtain ⟨j, rfl⟩ := (mem_powers_iff_mem_zpowers.2 (hg b))
      simp only
      rw [map_pow, monoidHomOfForallMemZpowers_apply_gen, ← pow_mul, mul_comm, pow_mul, hc1, one_pow]
    rw [← orderOf_eq_one_iff]
    exact Nat.eq_one_of_dvd_coprimes (hcop.pow_left k) (orderOf_dvd_of_pow_eq_one e2) (orderOf_dvd_of_pow_eq_one e1)

theorem isPrimitive_of_value (k : ℕ) (ζ : Qbar l) (h2 : l ≠ 2) (hk : 1 ≤ k) (hζ : IsPrimitiveRoot ζ (l ^ k))
    (χ : DirichletCharacter (Qbar l) (l ^ (k + 1))) (hχ : χ (1 + (l : ZMod (l ^ (k + 1)))) = ζ)
    (u : (ZMod (l ^ (k + 1)))ˣ) (hu : (u : ZMod (l ^ (k + 1))) = 1 + l) : χ.IsPrimitive := by
  have hl : l.Prime := Fact.out
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [DirichletCharacter.isPrimitive_def]
  by_contra hne
  have hd := χ.conductor_dvd_level
  obtain ⟨i, hi, hc⟩ := (Nat.dvd_prime_pow hl).1 hd
  have hi' : i ≤ j + 1 := by
    rcases Nat.lt_or_eq_of_le hi with h | h
    · omega
    · exact absurd (by rw [hc, h]) hne
  have hd2 : χ.conductor ∣ l ^ (j + 1) := by rw [hc]; exact pow_dvd_pow _ hi'
  have hker := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).1 χ.factorsThrough_conductor
  have h1 : (1 + (l : ZMod (l ^ (j + 1)))) ^ (l ^ j) = 1 := by
    rw [← ZMod.orderOf_one_add_prime hl h2 j]; exact pow_orderOf_eq_one _
  have hmem : u ^ (l ^ j) ∈ (ZMod.unitsMap hd).ker := by
    rw [MonoidHom.mem_ker]
    ext
    have := congrArg (ZMod.castHom hd2 (ZMod χ.conductor)) h1
    rw [map_pow, map_add, map_one, map_natCast] at this
    rw [ZMod.unitsMap_def, Units.coe_map, Units.val_pow_eq_pow_val, hu, Units.val_one]
    show ZMod.castHom hd (ZMod χ.conductor) _ = 1
    rw [map_pow, map_add, map_one, map_natCast]
    exact this
  have h3 := hker hmem
  rw [MonoidHom.mem_ker] at h3
  have h4 := congrArg Units.val h3
  rw [MulChar.coe_toUnitHom, Units.val_pow_eq_pow_val, hu, map_pow, hχ, Units.val_one] at h4
  exact hζ.pow_ne_one_of_pos_of_lt (pow_ne_zero _ hl.ne_zero)
    (Nat.pow_lt_pow_right hl.one_lt (Nat.lt_succ_self j)) h4

theorem exists_primitive_inComp : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e k : ℕ) (ζ : Qbar l),
    l ≠ 2 → 1 ≤ k → IsPrimitiveRoot ζ (l ^ k) → ∃ ψ : DirichletCharacter (Qbar l) (l ^ (k + 1)),
      ψ.IsPrimitive ∧ InComp φ e ψ ∧ ψ⁻¹ (1 + (l : ZMod (l ^ (k + 1)))) = ζ := by
  intro l _ φ e k ζ h2 hk hζ
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by have := hl.two_le; omega
  haveI : NeZero (l ^ (k + 1)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hcop : Nat.Coprime (1 + l) (l ^ (k + 1)) := Nat.Coprime.pow_right _ (by simp)
  let u : (ZMod (l ^ (k + 1)))ˣ := ZMod.unitOfCoprime (1 + l) hcop
  have hu : (u : ZMod (l ^ (k + 1))) = 1 + l := by
    rw [ZMod.coe_unitOfCoprime]; push_cast; rfl
  obtain ⟨ω, hω⟩ := exists_teichmuller (l := l)
  obtain ⟨χ₂, hχu, hχT⟩ := exists_wild k ζ h2 hk hζ u hu
  have hd : l ∣ l ^ (k + 1) := dvd_pow_self l (Nat.succ_ne_zero k)
  have hred : ∀ b : (ZMod (l ^ (k + 1)))ˣ, ((ZMod.unitsMap hd b : (ZMod l)ˣ) : ZMod l) =
      ZMod.castHom hd (ZMod l) (b : ZMod (l ^ (k + 1))) := fun b => rfl
  have hu1 : ZMod.unitsMap hd u = 1 := by
    ext
    rw [hred, hu, map_add, map_one, map_natCast, ZMod.natCast_self, add_zero, Units.val_one]
  let f : (ZMod (l ^ (k + 1)))ˣ →* (Qbar l)ˣ := ((ω ^ e * MulChar.toUnitHom φ).comp (ZMod.unitsMap hd)) * χ₂
  have hf : ∀ b, (f b : Qbar l) = (ω (ZMod.unitsMap hd b) : Qbar l) ^ e *
      φ ((ZMod.unitsMap hd b : (ZMod l)ˣ) : ZMod l) * χ₂ b := fun b => by
    simp only [f, MonoidHom.mul_apply, MonoidHom.comp_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom]
  let χ : DirichletCharacter (Qbar l) (l ^ (k + 1)) := MulChar.ofUnitHom f
  have hχ : ∀ b : (ZMod (l ^ (k + 1)))ˣ, χ b = f b := fun b => MulChar.ofUnitHom_coe f b
  have hval : χ (1 + (l : ZMod (l ^ (k + 1)))) = ζ := by
    rw [← hu, hχ, hf, hu1, hχu]; simp
  refine ⟨χ⁻¹, ?_, ?_, ?_⟩
  · have := isPrimitive_of_value k ζ h2 hk hζ χ hval u hu
    rw [DirichletCharacter.isPrimitive_def] at this ⊢
    rw [DirichletCharacter.conductor_inv, this]
  · intro b hb
    have hb' : (((b : ZMod (l ^ (k + 1))).val : ℕ) : ZMod l) = ((ZMod.unitsMap hd b : (ZMod l)ˣ) : ZMod l) := by
      rw [hred, ZMod.castHom_apply, ZMod.natCast_val]
    rw [inv_inv, hχ, hf, hχT b hb, Units.val_one, mul_one, hb', ← sub_mul, norm_mul]
    set x := ZMod.unitsMap hd b with hx
    have hx1 : x ^ (l - 1) = 1 := ZMod.units_pow_card_sub_one_eq_one l x
    have n1 : ‖φ (x : ZMod l)‖ = 1 := norm_eq_one_of_pow hl1 (by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, hx1, Units.val_one, map_one])
    have n2 : ‖(ω x : Qbar l)‖ = 1 := norm_eq_one_of_pow hl1 (by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hx1, map_one, Units.val_one])
    rw [n1, mul_one]
    refine norm_pow_sub_pow_lt_one n2.le (IsUltrametricDist.norm_natCast_le_one _ _) ?_ e
    refine norm_sub_lt_one_trans (hω x) (norm_natCast_sub_lt_one ?_)
    rw [hb', ZMod.natCast_zmod_val]
  · rw [inv_inv, hval]

end GlobalTheory.KZ.Cmp.PrimChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GlobOfShapiroSystem
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix

namespace GlobalTheory.KZGlobAsm

theorem norm_le_one_of_mem {l : ℕ} [Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  _root_.UpperTheory.Reformulated.B.Rc8.norm_le_one_of_mem c hx

theorem inv_pow_val_mem (l : ℕ) [Fact l.Prime] (c : Coef l) (e r : ℕ) (x : (ZMod (l ^ r))ˣ) :
    ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ ∈ c.O :=
  _root_.GlobalTheory.PadicInversePower.inv_pow_mem l c e r x

theorem eta_compat (l : ℕ) [Fact l.Prime] (c : Coef l) (e : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l)
    (hχ : ∀ r x, χ r x ∈ c.O)
    (hχc : ∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖)
    (r : ℕ) (x : (ZMod (l ^ (r + 1)))ˣ) :
    ‖(fun x : (ZMod (l ^ (r + 1)))ˣ => ((((x : ZMod (l ^ (r + 1))).val : ℕ) : Qbar l) ^ e)⁻¹ * χ (r + 1) x) x -
      (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x)
        ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ :=
  _root_.GlobalTheory.PadicNormCastBounds.twist_compat l c e χ hχ hχc r x

end GlobalTheory.KZGlobAsm

namespace GlobalTheory.KZ

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergWilesDualSelmerLowerBoundModPrimePow
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwIneq

theorem exists_cc (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] :
    ∃ cc : InfinitePlace ℚ → G ℚ Ω, ∀ w, w.IsReal → IsCCAt w (cc w) := by
  have h : ∀ w : InfinitePlace ℚ, ∃ c : G ℚ Ω, w.IsReal → IsCCAt w c := fun w => by
    by_cases hw : w.IsReal
    · haveI : Module.IsTorsionFree ℚ Ω := DivisionSemiring.to_moduleIsTorsionFree
      haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
      haveI : IsGalois ℚ Ω := {}
      letI : Algebra ℚ ℂ := w.embedding.toAlgebra
      let j : Ω →ₐ[ℚ] ℂ := IsAlgClosed.lift
      have hr : ComplexEmbedding.IsReal w.embedding := InfinitePlace.isReal_iff.1 hw
      let cj : ℂ →ₐ[ℚ] ℂ := { starRingEnd ℂ with commutes' := fun x => RingHom.congr_fun hr x }
      letI : Algebra Ω ℂ := j.toRingHom.toAlgebra
      haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq fun x => (j.commutes x).symm
      refine ⟨(cj.comp j).restrictNormal' Ω, fun _ => ⟨j.toRingHom, fun x => ?_, ?_⟩⟩
      · exact AlgHom.restrictNormal_commutes (cj.comp j) Ω x
      · rw [show j.toRingHom.comp (algebraMap ℚ Ω) = w.embedding from RingHom.ext fun x => j.commutes x]
        exact w.mk_embedding
    · exact ⟨1, fun h => absurd h hw⟩
  choose cc hcc using h
  exact ⟨cc, hcc⟩

theorem gw_ineq : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (y : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A W (y i)) → (∀ i j, i ≠ j → ¬ Cob1 c n W ⊤ (y i - y j)) → ∃ (N' : ℕ) (z : Fin N' → G ℚ Ω → Fin 2 → Qbar l), N ≤ C * N' ∧ (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) ∧ ∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j) := by
  classical
  intro hL l _ Ω _ _ _ e S A W hW c hint
  have hN := kills_NS hW
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.card_galoisInvariants_ordinaryRankTwo_mod_pow_bounded l Ω e S A W hW c hint hN
  obtain ⟨CA, hCA⟩ := GlobalTheory.T.card_ordinaryLocalConditionModPrimePow_le_const_mul hL l Ω e S A W hW c hint hN
  refine ⟨C0 * CA, fun n hn N y hy hyd => ?_⟩
  have hn0 : 0 < n := hn
  have hS := hW.above
  obtain ⟨μ, hμ⟩ := GlobalTheory.Published.PoitouTate.exists_lift_cycMod (F := ℚ) (Ω := Ω) (l := l) (r := n) (S := S) hS
  obtain ⟨cc, hcc⟩ := exists_cc Ω
  have hρ : ReciprocityTheory.Gal.ContAction (rhoS c n W hint S hN) := contAction_rhoS c n W hint S hN hW.cont
  have hgw := hL.gw ℚ Ω l n (Mn c n) S (rhoS c n W hint S hN) hn0 hW.l_odd hS hρ μ hμ (Av A S)
    (isPlaceOver_Av A S) cc hcc (Lc c n W hint S hN A)
  have hρd : ReciprocityTheory.Gal.ContAction (twDual μ (rhoS c n W hint S hN)) :=
    GlobalTheory.DualSide.contAction_twDual (GlobalTheory.Published.PoitouTate.contAction_charRep hμ) hρ
  haveI : Finite (TDual (ZMod (l ^ n)) (Mn c n)) := GlobalTheory.DualSide.finite_TDual
  haveI : Finite (H1 (rhoS c n W hint S hN)) := (hL.gf ℚ Ω l n (Mn c n) S _ hn0 hS hρ).2.1
  haveI : Finite (H1 (twDual μ (rhoS c n W hint S hN))) :=
    (hL.gf ℚ Ω l n (TDual (ZMod (l ^ n)) (Mn c n)) S _ hn0 hS hρd).2.1

  obtain ⟨v0, hA0, hl0⟩ := hW.atL
  let vA : S := ⟨v0, hS v0 hl0⟩
  have huniq : ∀ v w : Pl, IsPlaceOver A v → IsPlaceOver A w → v = w := fun v w hv hw =>
    HeightOneSpectrum.ext (Ideal.ext fun x => (hv x).symm.trans (hw x))
  have hLv : ∀ v : S, v ≠ vA → Nat.card (Lc c n W hint S hN A v) =
      Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) := by
    intro v hv
    have hnp : ¬ IsPlaceOver A v.1 := fun h => hv (Subtype.ext (huniq _ _ h hA0))
    have e1 : Lc c n W hint S hN A v = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))
        ((Ine (F := ℚ) (Av A S v)).subgroupOf (Dec (F := ℚ) (Av A S v))) := if_neg hnp
    rw [e1]
    exact GlobalTheory.Ord2.UrCard.card_unramified_h1_eq_card_h0 ℚ Ω l n (Mn c n) (Av A S v) v.1 _
      (hρ.comp' (continuous_locFam S (Av A S) v)) (isPlaceOver_Av A S v)
  have harch := GlobalTheory.T.archimedean_invariants_card l Ω e S A W hW c hint hN n hn cc hcc
  rw [harch, ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ vA),
    Finset.prod_congr rfl fun v hv => hLv v (Finset.ne_of_mem_erase hv)] at hgw
  have hLA := hCA n hn vA hA0
  have hH0 := hC0 n hn
  have hP : 0 < ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))) :=
    Finset.prod_pos fun v _ => Nat.card_pos
  have hq : 0 < Nat.card (Qn c n) := Nat.card_pos
  have h1d : 1 ≤ Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) := Nat.card_pos
  have h1A : 1 ≤ Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) := Nat.card_pos
  set P := ∏ v ∈ Finset.univ.erase vA, Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) v)))
  have hsel : Nat.card (SelG c n W hint S hN A) ≤ C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ) := by
    have key : Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P) ≤
        (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by
      calc Nat.card (SelG c n W hint S hN A) * (Nat.card (Qn c n) * P)
          = Nat.card (SelG c n W hint S hN A) * 1 * (1 * P) * Nat.card (Qn c n) := by ring
        _ ≤ Nat.card (SelG c n W hint S hN A) * Nat.card (H0 (twDual μ (rhoS c n W hint S hN))) *
            (Nat.card (H0 ((rhoS c n W hint S hN).comp (locFam S (Av A S) vA))) * P) * Nat.card (Qn c n) := by
          gcongr
        _ = Nat.card (SelD c n W hint S hN A hW.cont μ) * Nat.card (H0 (rhoS c n W hint S hN)) *
            (Nat.card (Lc c n W hint S hN A vA) * P) := hgw
        _ ≤ Nat.card (SelD c n W hint S hN A hW.cont μ) * C0 * (CA * Nat.card (Qn c n) * P) := by
          gcongr
        _ = (C0 * CA * Nat.card (SelD c n W hint S hN A hW.cont μ)) * (Nat.card (Qn c n) * P) := by ring
    exact Nat.le_of_mul_le_mul_right key (Nat.mul_pos hq hP)

  obtain ⟨cls, hcls, hinj⟩ := GlobalTheory.T.ordinarySelmerModPrimePow_injects_residualSelmer l Ω e S A W hW c hint hN n hn
  have hN1 : N ≤ Nat.card (SelG c n W hint S hN A) := by
    let f : Fin N → SelG c n W hint S hN A := fun i => ⟨cls (y i), hcls _ (hy i)⟩
    have hf : Function.Injective f := by
      intro i j hij
      by_contra hne
      exact hyd i j hne (hinj _ _ (hy i) (hy j) (congrArg Subtype.val hij))
    simpa using Nat.card_le_card_of_injective f hf

  obtain ⟨z, hz, hzd⟩ := GlobalTheory.T.dualSelmer_classes_give_noncohomologous_cochains hL l Ω e S A W hW c hint hN n hn μ hμ
  let eqv := Finite.equivFin (SelD c n W hint S hN A hW.cont μ)
  refine ⟨Nat.card (SelD c n W hint S hN A hW.cont μ), fun i => z (eqv.symm i), ?_, fun i => hz _, ?_⟩
  · exact hN1.trans hsel
  · intro i j hij
    exact hzd _ _ (fun h => hij (eqv.symm.injective h))

end GlobalTheory.Ord2.GwIneq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.PowerSeriesEqOfCongruentValuesAtPrimitiveRootsStatement
section
open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.powerSeries_eq_of_congruent_values_at_primitiveRoots : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (A B : PowerSeries (Qbar l)) (u : Qbar l) (w : ℕ → Qbar l) (c₀ m₀ : ℕ), (∀ n, A.coeff n ∈ c.O) → (∀ n, B.coeff n ∈ c.O) → B ≠ 0 → ‖u‖ = 1 → (∀ m, ‖w m‖ = 1 ∧ Cg m (w (m + 1)) (w m)) → (∀ m, m₀ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg (m / 2 - c₀) (tval A (l ^ (3 * m)) z) (w m * u ^ m * tval B (l ^ (3 * m)) z)) → u = 1 ∧ ∀ k : ℕ, ∃ m₁ : ℕ, ∀ m, m₁ ≤ m → ∀ n, Cg k (A.coeff n) (w m * B.coeff n) := by
  first | exact @GlobalTheory.KZ.autoPin_congr | exact GlobalTheory.KZ.autoPin_congr | (intros; apply GlobalTheory.KZ.autoPin_congr <;> assumption)
end

