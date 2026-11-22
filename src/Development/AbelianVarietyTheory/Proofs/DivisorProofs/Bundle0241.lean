import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0147
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0190
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0021

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarePresentationOfCounitalComul
section
open scoped TensorProduct

namespace GlobalTheory

theorem square_presentation_counital_comul_of_finrank (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (n : ℕ) :
    ∀ (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A] (ε : A →ₐ[k] k)
      (Δ : A →ₐ[k] A ⊗[k] A), Module.finrank k A = n →
      ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧
        (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) →
      IsNilpotent (RingHom.ker ε) →
      (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k),
        Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro A _ _ _ ε Δ hn hΔ hε
  obtain ⟨d, x, l, hl, hlx, hadj⟩ := GlobalTheory.T.exists_generators_dual_point_derivations_augmented k A ε hε
  choose D hD using fun i => GlobalTheory.T.exists_invariant_derivation_of_counital_comul k A ε Δ hΔ (l i) (hl i)
  obtain ⟨E, hE⟩ := GlobalTheory.T.exists_derivations_dual_to_family_of_nilpotent_aug k A ε hε d x D (fun i j => by rw [hD, hlx])
  have hnt : Nontrivial A := ε.toRingHom.domain_nontrivial
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    refine ⟨0, MvPolynomial.aeval x, fun _ => 0, ?_, ?_⟩
    · rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, hadj]
    · rw [Set.range_eq_empty, Ideal.span_empty, ← RingHom.injective_iff_ker_eq_bot]
      intro f g h
      rw [MvPolynomial.eq_C_of_isEmpty f, MvPolynomial.eq_C_of_isEmpty g] at h ⊢
      simp only [MvPolynomial.aeval_C] at h
      rw [(algebraMap k A).injective h]
  · obtain ⟨B, hB, Δ', hΔ'⟩ := GlobalTheory.T.frobeniusSubalgebra_counital_comul p k A ε Δ hΔ
    have hp : (p : A) = 0 := by
      rw [← map_natCast (algebraMap k A), CharP.cast_eq_zero, map_zero]
    have hEB : ∀ i, ∀ b ∈ B, E i b = 0 := by
      intro i b hb
      obtain ⟨c, rfl⟩ := (hB b).1 hb
      rw [Derivation.leibniz_pow, nsmul_eq_mul, hp, zero_mul]
    have hBtop : B ≠ ⊤ := by
      intro h
      have h1 := hE ⟨0, hd⟩ ⟨0, hd⟩
      rw [hEB _ _ (h ▸ Algebra.mem_top), if_pos rfl] at h1
      exact zero_ne_one h1
    have hlt : Module.finrank k B < n := by
      rw [← hn]
      have : (Subalgebra.toSubmodule B) ≠ ⊤ := by
        intro h
        apply hBtop
        rw [← Algebra.toSubmodule_eq_top]
        exact h
      exact Submodule.finrank_lt this
    have hfin : Module.Finite k B :=
      Module.Finite.of_injective B.val.toLinearMap Subtype.val_injective
    have hε' : IsNilpotent (RingHom.ker (ε.comp B.val)) := by
      obtain ⟨m, hm⟩ := hε
      refine ⟨m, ?_⟩
      have h1 : (RingHom.ker (ε.comp B.val)) = Ideal.comap B.val (RingHom.ker ε) := by
        ext b; simp [RingHom.mem_ker, Ideal.mem_comap]
      rw [h1, Ideal.zero_eq_bot, eq_bot_iff]
      refine (Ideal.le_comap_pow _ m).trans ?_
      rw [hm, Ideal.zero_eq_bot]
      intro b hb
      rw [Ideal.mem_comap, Ideal.mem_bot] at hb
      rw [Ideal.mem_bot]
      exact Subtype.ext hb
    refine GlobalTheory.T.exists_square_presentation_of_tower k B A (ih _ hlt B (ε.comp B.val) Δ' rfl hΔ' hε') ?_
    refine ⟨d, MvPolynomial.aeval x, _, ?_,
      GlobalTheory.T.ker_aeval_truncatedPolynomial_presentation p (Fact.out : p.Prime).pos B A d x
        (fun i => ⟨x i ^ p, (hB _).2 ⟨x i, rfl⟩⟩) (fun i => rfl)
        (GlobalTheory.T.truncatedMonomials_linearIndependent_over_constants p k A d x E hE B hEB)⟩
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval, eq_top_iff]
    intro a _
    have ha : a ∈ Algebra.adjoin k (Set.range x) := hadj ▸ Algebra.mem_top
    have hle : Algebra.adjoin k (Set.range x) ≤
        (Algebra.adjoin B (Set.range x)).restrictScalars k :=
      Algebra.adjoin_le Algebra.subset_adjoin
    exact hle ha

theorem square_presentation_of_counital_comul : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CommRing A] [Algebra k A] [CharP k p] [PerfectRing k p] [Module.Finite k A] (ε : A →ₐ[k] k) (Δ : A →ₐ[k] A ⊗[k] A), ((∀ a : A, TensorProduct.lid k A (LinearMap.rTensor A ε.toLinearMap (Δ a)) = a) ∧ (∀ a : A, TensorProduct.rid k A (LinearMap.lTensor A ε.toLinearMap (Δ a)) = a)) → IsNilpotent (RingHom.ker ε) → (∃ (s : ℕ) (φ : MvPolynomial (Fin s) k →ₐ[k] A) (g : Fin s → MvPolynomial (Fin s) k), Function.Surjective φ ∧ RingHom.ker φ = Ideal.span (Set.range g)) := by
  intro p _ k A _ _ _ _ _ _ ε Δ h hε
  exact square_presentation_counital_comul_of_finrank p k _ A ε Δ rfl h hε

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableExpNegTraceTotallyPositiveFractionalIdeaStatement
section
open NumberField Complex
open scoped nonZeroDivisors
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_exp_neg_trace_totallyPositive_fractionalIdeal : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (L : FractionalIdeal (𝓞 F)⁰ F) (δ : ℝ), 0 < δ → Summable (fun x : {x : F // x ∈ L ∧ ∀ τ : Emb F, 0 < τ x} => Real.exp (-δ * ∑ τ : Emb F, τ x.1)) := by
  first | exact @GlobalTheory.LatExpSum.summable_exp_neg_trace | exact GlobalTheory.LatExpSum.summable_exp_neg_trace | (intros; apply GlobalTheory.LatExpSum.summable_exp_neg_trace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummableHeckeBalancedLatticeDoubleSum
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo.LatSum

variable {F : Type} [Field F] [NumberField F]

def absSum (x : F) : ℝ := ∑ τ : Emb F, |τ x|

theorem absSum_nonneg (x : F) : 0 ≤ absSum x := Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem abs_le_absSum (x : F) (τ : Emb F) : |τ x| ≤ absSum x :=
  Finset.single_le_sum (f := fun τ : Emb F => |τ x|) (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)

theorem one_add_sum_le_prod {ι : Type} (s : Finset ι) (a : ι → ℝ) (h : ∀ i, 0 ≤ a i) :
    1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg fun j _ => h j
    nlinarith [mul_le_mul_of_nonneg_left ih (by linarith [h i] : (0:ℝ) ≤ 1 + a i), mul_nonneg (h i) h1]

theorem bound_eq (K₁ s x q : ℝ) (a b : ℕ) (hs : s ≠ 0) (hx : x ≠ 0) (hq : q ≠ 0) :
    (K₁ * s) ^ a / (x * (s / q)) ^ (a + b) = K₁ ^ a * q ^ (a + b) * ((s ^ b)⁻¹ * (x ^ (a + b))⁻¹) := by
  rw [mul_pow, mul_pow, div_pow, pow_add s]
  field_simp

variable [IsTotallyReal F]

open scoped Classical in

theorem norm_mixedEmbedding_le (x : F) : ‖mixedEmbedding F x‖ ≤ absSum x := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace]
  refine Finset.sup'_le _ _ fun w _ => ?_
  rw [mixedEmbedding.normAtPlace_apply, ← InfinitePlace.norm_embedding_of_isReal (IsTotallyReal.isReal w) x,
    Real.norm_eq_abs]
  exact abs_le_absSum x _

open scoped Classical in
theorem absSum_pos {x : F} (hx : x ≠ 0) : 0 < absSum x := by
  have h : 0 < ‖mixedEmbedding F x‖ := norm_pos_iff.2 fun h =>
    hx ((mixedEmbedding F).injective (h.trans (map_zero _).symm))
  exact h.trans_le (norm_mixedEmbedding_le x)

open scoped Classical in

theorem summable_absSum_inv_pow (I : Frac F) {k : ℕ} (hk : Module.finrank ℚ F < k) :
    Summable (fun x : NZ (I : FractionalIdeal (𝓞 F)⁰ F) => ((absSum x.1) ^ k)⁻¹) := by
  let L := mixedEmbedding.idealLattice F I
  have hL := ZLattice.summable_norm_rpow L (-(k : ℝ)) (by
    rw [ZLattice.rank ℝ L, mixedEmbedding.finrank F]
    have : (Module.finrank ℚ F : ℝ) < k := by exact_mod_cast hk
    linarith)
  let j : NZ (I : FractionalIdeal (𝓞 F)⁰ F) → L := fun x =>
    ⟨mixedEmbedding F x.1, (mixedEmbedding.mem_idealLattice F I).2 ⟨x.1, x.2.1, rfl⟩⟩
  have hj : Function.Injective j := fun x y h =>
    Subtype.ext ((mixedEmbedding F).injective (congrArg Subtype.val h))
  refine (hL.comp_injective hj).of_nonneg_of_le (fun x => inv_nonneg.2 (pow_nonneg (absSum_nonneg _) _))
    (fun x => ?_)
  have hpos : 0 < ‖mixedEmbedding F x.1‖ := norm_pos_iff.2 fun h =>
    x.2.2 ((mixedEmbedding F).injective (h.trans (map_zero _).symm))
  show ((absSum x.1) ^ k)⁻¹ ≤ ‖mixedEmbedding F x.1‖ ^ (-(k : ℝ))
  rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
  exact inv_anti₀ (pow_pos hpos k) (pow_le_pow_left₀ hpos.le (norm_mixedEmbedding_le x.1) k)

theorem prod_abs_emb (x : F) : ∏ τ : Emb F, |τ x| = |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
  have h := congrArg (fun z : ℂ => ‖z‖) (prod_emb x)
  simp only [norm_prod, Complex.norm_real, Real.norm_eq_abs] at h
  rw [h, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]

theorem exists_absSum_lower (I : FractionalIdeal (𝓞 F)⁰ F) :
    ∃ β : ℝ, 0 < β ∧ ∀ x ∈ I, x ≠ 0 → β ≤ absSum x := by
  obtain ⟨d, hd, h⟩ := I.isFractional
  have hd0 : ((d : 𝓞 F) : F) ≠ 0 := by exact_mod_cast nonZeroDivisors.ne_zero hd
  set D := |((Algebra.norm ℚ ((d : 𝓞 F) : F) : ℚ) : ℝ)| with hD
  have hDpos : 0 < D := by simp [hD, Algebra.norm_eq_zero_iff, hd0]
  have hn : 1 ≤ Fintype.card (Emb F) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact Fintype.card_pos_iff.2 ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩
  refine ⟨min 1 D⁻¹, lt_min one_pos (inv_pos.2 hDpos), fun x hx hx0 => ?_⟩
  obtain ⟨g, hg⟩ := h x hx
  have hg' : ((g : 𝓞 F) : F) = ((d : 𝓞 F) : F) * x := by
    rw [← Algebra.smul_def] at *; simpa using hg
  have hg0 : g ≠ 0 := by
    intro h0; rw [h0] at hg'; simp at hg'
    exact hg'.elim (fun h => hd0 (by exact_mod_cast h)) hx0
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℤ g : ℤ) : ℝ)| := by
    have : Algebra.norm ℤ g ≠ 0 := Algebra.norm_ne_zero_iff.2 hg0
    exact_mod_cast Int.one_le_abs this
  have e1 : ((Algebra.norm ℤ g : ℤ) : ℚ) = Algebra.norm ℚ ((d : 𝓞 F) : F) * Algebra.norm ℚ x := by
    rw [Algebra.coe_norm_int, hg', map_mul]
  have e2 : ((Algebra.norm ℤ g : ℤ) : ℝ) =
      ((Algebra.norm ℚ ((d : 𝓞 F) : F) : ℚ) : ℝ) * ((Algebra.norm ℚ x : ℚ) : ℝ) := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) e1
  rw [e2, abs_mul, ← hD, ← prod_abs_emb] at h1
  have hle : ∏ τ : Emb F, |τ x| ≤ absSum x ^ Fintype.card (Emb F) := by
    calc ∏ τ : Emb F, |τ x| ≤ ∏ _τ : Emb F, absSum x :=
          Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun τ _ => abs_le_absSum x τ)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ]
  have hS0 := absSum_nonneg x
  rcases le_or_gt 1 (absSum x) with hS | hS
  · exact (min_le_left _ _).trans hS
  · have hpow : absSum x ^ Fintype.card (Emb F) ≤ absSum x := pow_le_of_le_one hS0 hS.le (by omega)
    refine (min_le_right _ _).trans ?_
    have : 1 ≤ D * absSum x := h1.trans (mul_le_mul_of_nonneg_left (hle.trans hpow) hDpos.le)
    rw [inv_le_iff_one_le_mul₀ hDpos]
    linarith

end GlobalTheory.HeckeTwo.LatSum

open GlobalTheory.HeckeTwo.LatSum in

theorem GlobalTheory.HeckeTwo.summable_balanced_latSum :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔞 𝔟 : Frac F) (C₀ : ℝ) (m : ℕ), ∃ N : ℕ,
    ∀ ε : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → (𝓞 F)ˣ,
      (∀ c (τ τ' : Emb F), |τ (((ε c : 𝓞 F) : F) * c.out.1)| ≤ C₀ * |τ' (((ε c : 𝓞 F) : F) * c.out.1)|) →
      Summable (fun p : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) =>
        ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N) := by
  intro F _ _ _ 𝔞 𝔟 C₀ m
  set n := Fintype.card (Emb F) with hn_def
  set f := Module.finrank ℚ F with hf_def
  refine ⟨m * n + (f + 1), fun ε hbal => ?_⟩
  set N := m * n + (f + 1) with hN
  rcases isEmpty_or_nonempty (Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) with hE | ⟨⟨c₀⟩⟩
  · exact summable_empty
  have hn : 1 ≤ n := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    exact Fintype.card_pos_iff.2 ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩
  obtain ⟨τ₀⟩ : Nonempty (Emb F) := Fintype.card_pos_iff.1 hn
  obtain ⟨β, hβ, hβS⟩ := exists_absSum_lower (𝔟 : FractionalIdeal (𝓞 F)⁰ F)

  let bp : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → F := fun c => ((ε c : 𝓞 F) : F) * c.out.1
  have hunit0 : ∀ u : (𝓞 F)ˣ, ((u : 𝓞 F) : F) ≠ 0 := fun u h =>
    u.ne_zero (by exact_mod_cast h)
  have hbp_mem : ∀ c, bp c ∈ (𝔟 : FractionalIdeal (𝓞 F)⁰ F) := fun c => by
    have := Submodule.smul_mem (𝔟 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule (ε c : 𝓞 F) c.out.2.1
    rwa [Algebra.smul_def] at this
  have hbp0 : ∀ c, bp c ≠ 0 := fun c => mul_ne_zero (hunit0 _) c.out.2.2
  have hC₀ : 1 ≤ C₀ := by
    have h := hbal c₀ τ₀ τ₀
    have hpos : 0 < |τ₀ (bp c₀)| := abs_pos.2 ((map_ne_zero τ₀).2 (hbp0 c₀))
    exact le_of_mul_le_mul_right (by rw [one_mul]; exact h) hpos
  have hq : 0 < (n : ℝ) * C₀ := mul_pos (by exact_mod_cast hn) (by linarith)
  have hlow : ∀ c (τ : Emb F), absSum (bp c) / (n * C₀) ≤ |τ (bp c)| := by
    intro c τ
    rw [div_le_iff₀ hq]
    calc absSum (bp c) = ∑ τ' : Emb F, |τ' (bp c)| := rfl
      _ ≤ ∑ _τ' : Emb F, C₀ * |τ (bp c)| := Finset.sum_le_sum fun τ' _ => hbal c τ' τ
      _ = |τ (bp c)| * (n * C₀) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

  let g : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) → ℝ := fun c => ((absSum (bp c)) ^ (f + 1))⁻¹
  let h : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ := fun y => ((absSum y.1) ^ N)⁻¹
  have hg : Summable g := by
    refine (summable_absSum_inv_pow 𝔟 (k := f + 1) (by omega)).comp_injective
      (i := fun c => (⟨bp c, hbp_mem c, hbp0 c⟩ : NZ (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) ?_
    intro c c' hcc
    have e : bp c = bp c' := congrArg Subtype.val hcc
    refine Quotient.out_equiv_out.1 ⟨(ε c')⁻¹ * ε c, ?_⟩
    have h1 : (((ε c')⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε c' : 𝓞 F) : F) = 1 := unit_inv_mul (ε c')
    simp only [bp] at e
    push_cast
    linear_combination (-(c'.out.1) * h1) - ((((ε c')⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * e
  have hh : Summable h := summable_absSum_inv_pow 𝔞 (k := N) (by omega)
  let e : (Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → (Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F))) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) := fun p =>
    (p.1, ⟨((((ε p.1)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * p.2.1, by
      have := Submodule.smul_mem (𝔞 : FractionalIdeal (𝓞 F)⁰ F).coeToSubmodule
        (((ε p.1)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) p.2.2.1
      rwa [Algebra.smul_def] at this, mul_ne_zero (hunit0 _) p.2.2.2⟩)
  have he : Function.Injective e := by
    rintro ⟨c, ν⟩ ⟨c', ν'⟩ hcc
    have h1 : c = c' := congrArg Prod.fst hcc
    subst h1
    have h2 := congrArg (fun p => (p.2 : NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F)).1) hcc
    simp only [e] at h2
    exact Prod.ext rfl (Subtype.ext (mul_left_cancel₀ (hunit0 _) h2))
  have hV := (hg.mul_of_nonneg hh (fun c => inv_nonneg.2 (pow_nonneg (absSum_nonneg _) _))
    (fun y => inv_nonneg.2 (pow_nonneg (absSum_nonneg _) _))).comp_injective he
  set K₁ : ℝ := 1 + n * C₀ / β ^ 2 with hK₁
  refine (hV.mul_left (K₁ ^ (m * n) * (n * C₀) ^ N)).of_nonneg_of_le
    (fun p => Finset.prod_nonneg fun τ _ => div_nonneg (pow_nonneg (by positivity) _) (pow_nonneg (by positivity) _))
    (fun p => ?_)

  obtain ⟨c, ν⟩ := p
  set b' := bp c with hb'
  set ν' := ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1 with hν'
  set s := absSum b' with hs
  set x := absSum ν' with hx
  have hsβ : β ≤ s := hβS _ (hbp_mem c) (hbp0 c)
  have hs0 : 0 < s := hβ.trans_le hsβ
  have hx0 : 0 < x := absSum_pos (mul_ne_zero (hunit0 _) ν.2.2)
  have hid : ∀ τ : Emb F, |τ ν.1 * τ c.out.1| = |τ ν'| * |τ b'| := by
    intro τ
    have h1 : (((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε c : 𝓞 F) : F) = 1 := unit_inv_mul (ε c)
    rw [← abs_mul, ← map_mul, ← map_mul]
    congr 2
    simp only [hν', hb', bp]
    linear_combination (-(ν.1 * c.out.1)) * h1
  have hA : ∀ τ : Emb F, |τ b'| + |τ b'|⁻¹ ≤ K₁ * s := by
    intro τ
    have hlo := hlow c τ
    have hpos : 0 < s / (n * C₀) := div_pos hs0 hq
    have h1 : |τ b'|⁻¹ ≤ n * C₀ / s := by
      calc |τ b'|⁻¹ ≤ (s / (n * C₀))⁻¹ := inv_anti₀ hpos hlo
        _ = n * C₀ / s := inv_div _ _
    have h2 : n * C₀ / s ≤ n * C₀ / β ^ 2 * s := by
      rw [div_le_iff₀ hs0]
      have hβ2 : β ^ 2 ≤ s * s := by nlinarith
      calc (n : ℝ) * C₀ = n * C₀ / β ^ 2 * β ^ 2 := by field_simp
        _ ≤ n * C₀ / β ^ 2 * (s * s) := mul_le_mul_of_nonneg_left hβ2 (by positivity)
        _ = _ := by ring
    have h3 : |τ b'| ≤ s := abs_le_absSum _ τ
    rw [hK₁]; nlinarith
  have hnum : ∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m ≤ (K₁ * s) ^ (m * n) := by
    calc ∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m ≤ ∏ _τ : Emb F, (K₁ * s) ^ m :=
          Finset.prod_le_prod (fun _ _ => pow_nonneg (by positivity) _) (fun τ _ => pow_le_pow_left₀ (by positivity) (hA τ) m)
      _ = (K₁ * s) ^ (m * n) := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  have hden : (x * (s / (n * C₀))) ^ N ≤ ∏ τ : Emb F, (1 + |τ ν.1 * τ c.out.1|) ^ N := by
    rw [Finset.prod_pow]
    refine pow_le_pow_left₀ (mul_nonneg hx0.le (div_pos hs0 hq).le) ?_ N
    calc x * (s / (n * C₀)) = ∑ τ : Emb F, |τ ν'| * (s / (n * C₀)) := by rw [hx, absSum, Finset.sum_mul]
      _ ≤ ∑ τ : Emb F, |τ ν.1 * τ c.out.1| := Finset.sum_le_sum fun τ _ => by
          rw [hid]; exact mul_le_mul_of_nonneg_left (hlow c τ) (abs_nonneg _)
      _ ≤ 1 + ∑ τ : Emb F, |τ ν.1 * τ c.out.1| := by linarith
      _ ≤ _ := one_add_sum_le_prod _ _ fun τ => abs_nonneg _
  have hdpos : 0 < (x * (s / (n * C₀))) ^ N := pow_pos (mul_pos hx0 (div_pos hs0 hq)) N
  show ∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m / (1 + |τ ν.1 * τ c.out.1|) ^ N ≤
    K₁ ^ (m * n) * (n * C₀) ^ N * (((s) ^ (f + 1))⁻¹ * ((x) ^ N)⁻¹)
  rw [Finset.prod_div_distrib]
  calc (∏ τ : Emb F, (|τ b'| + |τ b'|⁻¹) ^ m) / ∏ τ : Emb F, (1 + |τ ν.1 * τ c.out.1|) ^ N
      ≤ (K₁ * s) ^ (m * n) / (x * (s / (n * C₀))) ^ N :=
        div_le_div₀ (by positivity) hnum hdpos hden
    _ = K₁ ^ (m * n) * (n * C₀) ^ N * ((s ^ (f + 1))⁻¹ * (x ^ N)⁻¹) := by
        rw [hN]
        exact bound_eq _ _ _ _ _ _ hs0.ne' hx0.ne' hq.ne'
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
section
noncomputable section

namespace GlobalTheory.SwapSlice

open GlobalTheory.WeilM

variable {k κ Y : Type}

def barL (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ) where
  toFun Φ := fun y => starRingEnd ℂ (ι (fun x => starRingEnd ℂ (Φ x)) y)
  map_add' Φ Ψ := by
    funext y
    have e : (fun x => starRingEnd ℂ ((Φ + Ψ) x)) = (fun x => starRingEnd ℂ (Φ x)) + fun x => starRingEnd ℂ (Ψ x) := by
      funext x; simp
    show starRingEnd ℂ (ι (fun x => starRingEnd ℂ ((Φ + Ψ) x)) y) = _
    rw [e, map_add, Pi.add_apply, map_add]
    rfl
  map_smul' c Φ := by
    funext y
    have e : (fun x => starRingEnd ℂ ((c • Φ) x)) = starRingEnd ℂ c • fun x => starRingEnd ℂ (Φ x) := by
      funext x; simp
    show starRingEnd ℂ (ι (fun x => starRingEnd ℂ ((c • Φ) x)) y) = _
    rw [e, map_smul, Pi.smul_apply, smul_eq_mul, map_mul, Complex.conj_conj]
    rfl

theorem barL_apply (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (Φ : (κ → k) → ℂ) (y : Y) :
    barL ι Φ y = starRingEnd ℂ (ι (fun x => starRingEnd ℂ (Φ x)) y) := rfl

def sliceT (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) : ((κ ⊕ κ → k) → ℂ) →ₗ[ℂ] (Y × Y → ℂ) where
  toFun Φ := fun Z => barL ι (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) Z.2
  map_add' Φ Ψ := by
    funext Z
    have e : (fun x₂ => ι (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) Z.1) =
        (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) + fun x₂ => ι (fun x₁ => Ψ (Sum.elim x₁ x₂)) Z.1 := by
      funext x₂
      have e' : (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) = (fun x₁ => Φ (Sum.elim x₁ x₂)) + fun x₁ => Ψ (Sum.elim x₁ x₂) := rfl
      rw [e', map_add]
      rfl
    show barL ι (fun x₂ => ι (fun x₁ => (Φ + Ψ) (Sum.elim x₁ x₂)) Z.1) Z.2 = _
    rw [e, map_add]
    rfl
  map_smul' c Φ := by
    funext Z
    have e : (fun x₂ => ι (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) Z.1) =
        c • fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1 := by
      funext x₂
      have e' : (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) = c • fun x₁ => Φ (Sum.elim x₁ x₂) := rfl
      rw [e', map_smul]
      rfl
    show barL ι (fun x₂ => ι (fun x₁ => (c • Φ) (Sum.elim x₁ x₂)) Z.1) Z.2 = _
    rw [e, map_smul]
    rfl

theorem sliceT_apply (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (Φ : (κ ⊕ κ → k) → ℂ) (Z : Y × Y) :
    sliceT ι Φ Z = barL ι (fun x₂ => ι (fun x₁ => Φ (Sum.elim x₁ x₂)) Z.1) Z.2 := rfl

def swapNeg [Neg Y] (Z : Y × Y) : Y × Y := (-Z.2, -Z.1)

theorem swapNeg_apply [Neg Y] (Z : Y × Y) : swapNeg Z = (-Z.2, -Z.1) := rfl

theorem sliceT_boxFun [CommRing k] (ι : ((κ → k) → ℂ) →ₗ[ℂ] (Y → ℂ)) (φ₁ φ₂ : (κ → k) → ℂ) (Z : Y × Y) :
    sliceT ι (boxFun φ₁ φ₂) Z = ι φ₁ Z.1 * barL ι φ₂ Z.2 := by
  have e : (fun x₂ => ι (fun x₁ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) Z.1) = ι φ₁ Z.1 • φ₂ := by
    funext x₂
    have e' : (fun x₁ => boxFun φ₁ φ₂ (Sum.elim x₁ x₂)) = φ₂ x₂ • φ₁ := by
      funext x₁; simp [boxFun, Function.comp_def, mul_comm]
    rw [e', map_smul]
    simp [mul_comm]
  rw [sliceT_apply, e, map_smul]
  simp

end GlobalTheory.SwapSlice
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticZmodLift
section
namespace GlobalTheory

theorem symplectic_zmod_lift : ∀ (h k : ℕ) (M : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) (ZMod k)),
    M ∈ Matrix.symplecticGroup (Fin h) (ZMod k) → ∃ N : Matrix (Fin h ⊕ Fin h) (Fin h ⊕ Fin h) ℤ,
      N ∈ Matrix.symplecticGroup (Fin h) ℤ ∧ N.map (Int.cast : ℤ → ZMod k) = M := by
  intro h k M hM
  obtain ⟨N, hN⟩ := symplecticGroupMap_zmod_surjective (Fin h) k ⟨M, hM⟩
  refine ⟨N.1, N.2, ?_⟩
  have := congrArg Subtype.val hN
  rw [coe_symplecticGroupMap] at this
  simpa using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetFgOverFirstStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_fg_over_first : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ) (F : Finset A), ∃ F' : Finset (firstAndFinite R A k F), Algebra.adjoin R (Set.range (firstIncl R A k F) ∪ (F' : Set (firstAndFinite R A k F))) = ⊤ := by
  first | (exact @GlobalTheory.EtC.firstAndFinite_fg_over_first) | (exact GlobalTheory.EtC.firstAndFinite_fg_over_first) | (intros; apply GlobalTheory.EtC.firstAndFinite_fg_over_first  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPowerFirstFactorAdjoinFinsetIsIntegralStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorPowerFirstFactorAdjoinFinset_isIntegral : ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] (k : ℕ) (F : Finset A), Algebra.IsIntegral R (firstAndFinite R A k F) := by
  first | (exact @GlobalTheory.EtC.firstAndFinite_isIntegral) | (exact GlobalTheory.EtC.firstAndFinite_isIntegral) | (intros; apply GlobalTheory.EtC.firstAndFinite_isIntegral  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivialIff
section
open IsLocalRing

noncomputable section

namespace GlobalTheory.LocAcyc

def IsZModTorsor (B D : Type) [CommRing B] [CommRing D] [Algebra B D] (q : ℕ)
    (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)) : Prop :=
  Module.Finite B D ∧ Module.Projective B D ∧ Module.FaithfullyFlat B D ∧
    Function.Bijective (Algebra.TensorProduct.productMap
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
      (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)))

theorem torsorsTrivial_iff (B : Type) [CommRing B] (q : ℕ) :
    TorsorsTrivial B q ↔ ∀ (D : Type) [CommRing D] [Algebra B D]
      (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)), IsZModTorsor B D q act →
        Nonempty (D →ₐ[B] B) := by
  constructor
  · intro h D _ _ act hD
    exact h D hD.1 hD.2.1 hD.2.2.1 act hD.2.2.2
  · intro h D _ _ h1 h2 h3 act h4
    exact h D act ⟨h1, h2, h3, h4⟩

def LocPiecesEtale (R S : Type) [CommRing R] [CommRing S] [Algebra R S] : Prop :=
  ∃ (ι : Type) (_ : Preorder ι) (_ : IsDirected ι (· ≤ ·)) (_ : Nonempty ι)
    (Si : ι → Subalgebra R S), Monotone Si ∧ (∀ s : S, ∃ i, s ∈ Si i) ∧
    ∀ i, ∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A)
      (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Si i)

end GlobalTheory.LocAcyc
end
end

