import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0114
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGaloisInvariantsOrdinaryRankTwoModPowBounded
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0396
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0394
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupProductFixedSubmoduleRestrictDual

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyProdInv
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KumUnit

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def ValPres (A : ValuationSubring Ω) (m r : ℕ) (ζ : Ω) (z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (o : ι → Qbar l) (u : ι → Ω) (n : ι → ℤ) (k : ι → G ℚ Ω → ZMod (l ^ m)),
    (∀ i, ‖o i‖ ≤ 1) ∧ (∀ i, u i ≠ 0 ∧ A.valuation (u i) ^ (l ^ r).totient = A.valuation (l : Ω) ^ n i) ∧
    (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l r s = 1 →
      (∀ i, GlobalTheory.Col.KumVal (l := l) m ζ (u i) s (k i s)) ∧ Cg m (z s 1) (∑ i, o i * ((k i s).val : Qbar l))) ∧
    Cg m (∑ i, o i * (((n i : ZMod (l ^ m))).val : Qbar l)) 0

theorem cg_trans {m : ℕ} {x y z : Qbar l} (h : Cg m x y) (h' : Cg m y z) : Cg m x z := by
  unfold Cg at *
  have hm := IsUltrametricDist.norm_add_le_max (x - y) (y - z)
  rw [sub_add_sub_cancel] at hm
  exact hm.trans (max_le h h')

theorem cg_symm {m : ℕ} {x y : Qbar l} (h : Cg m x y) : Cg m y x := by
  unfold Cg at *
  rwa [norm_sub_rev]

theorem cg_sum {m : ℕ} {ι : Type} (S : Finset ι) {x y : ι → Qbar l} (h : ∀ i ∈ S, Cg m (x i) (y i)) :
    Cg m (∑ i ∈ S, x i) (∑ i ∈ S, y i) := by
  unfold Cg
  rw [← Finset.sum_sub_distrib]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) h

theorem cg_mul_left {m : ℕ} {o x y : Qbar l} (ho : ‖o‖ ≤ 1) (h : Cg m x y) : Cg m (o * x) (o * y) := by
  unfold Cg at *
  rw [← mul_sub, norm_mul]
  calc ‖o‖ * ‖x - y‖ ≤ 1 * ‖x - y‖ := mul_le_mul_of_nonneg_right ho (norm_nonneg _)
    _ = ‖x - y‖ := one_mul _
    _ ≤ _ := h

end GlobalTheory.KumUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ArchimedeanInvariantsCardStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_invariants_card : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∀ cc : InfinitePlace ℚ → G ℚ Ω, (∀ w, w.IsReal → IsCCAt w (cc w)) → archH0Card S (rhoS c n W hint S hN) cc = Nat.card (Qn c n) := by
  first | exact @GlobalTheory.Ord2.GwIneq.Arch.archimedean_h0_card_eq | exact GlobalTheory.Ord2.GwIneq.Arch.archimedean_h0_card_eq | (intros; apply GlobalTheory.Ord2.GwIneq.Arch.archimedean_h0_card_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardGaloisInvariantsOrdinaryRankTwoModPowBoundedStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_galoisInvariants_ordinaryRankTwo_mod_pow_bounded : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1), ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → Nat.card (H0 (rhoS c n W hint S hN)) ≤ C := by
  first | exact @GlobalTheory.Ord2.GwCard.exists_card_H0_rhoS_le | exact GlobalTheory.Ord2.GwCard.exists_card_H0_rhoS_le | (intros; apply GlobalTheory.Ord2.GwCard.exists_card_H0_rhoS_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardOrdinaryLocalConditionModPrimePowLeConstMulStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_ordinaryLocalConditionModPrimePow_le_const_mul : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1), ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ v : S, IsPlaceOver A v.1 → Nat.card (Lc c n W hint S hN A v) ≤ C * Nat.card (Qn c n) := by
  first | exact @GlobalTheory.Ord2.GwIneq.CardOrd.card_ord | exact GlobalTheory.Ord2.GwIneq.CardOrd.card_ord | (intros; apply GlobalTheory.Ord2.GwIneq.CardOrd.card_ord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ChSumSubCMul
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries

namespace GlobalTheory.KZ.Cmp

variable {l : ℕ} [Fact l.Prime]

def chSum (F : PowerSeries (Qbar l)) (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Qbar l :=
  ∑ b : (ZMod (l ^ m))ˣ, ψ b * tval F (l ^ (3 * m)) (z ^ (b : ZMod (l ^ m)).val)

def gSum (m : ℕ) (z : Qbar l) (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Qbar l :=
  ∑ b : (ZMod (l ^ m))ˣ, ψ b * z ^ (b : ZMod (l ^ m)).val

def rSum (φ : DirichletCharacter (Qbar l) l) (e : ℕ) (F : PowerSeries (Qbar l)) (r : ℕ) (ξ : Qbar l) : Qbar l :=
  ∑ x ∈ (Finset.range (l ^ r)).filter (fun x => ¬ l ∣ x), φ (x : ZMod l) * ((x : Qbar l) ^ e) * mass F r ξ x

def InComp (φ : DirichletCharacter (Qbar l) l) (e : ℕ) {m : ℕ} (ψ : DirichletCharacter (Qbar l) (l ^ m)) : Prop :=
  ∀ b : (ZMod (l ^ m))ˣ, b ^ (l - 1) = 1 →
    ‖ψ⁻¹ (b : ZMod (l ^ m)) - (((b : ZMod (l ^ m)).val : Qbar l) ^ e) * φ (((b : ZMod (l ^ m)).val : ℕ) : ZMod l)‖ < 1

theorem tval_sub_C_mul (F G : PowerSeries (Qbar l)) (a : Qbar l) (N : ℕ) (z : Qbar l) :
    tval (F - PowerSeries.C a * G) N z = tval F N z - a * tval G N z := by
  unfold tval
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_sub, PowerSeries.coeff_C_mul]; ring

theorem tval_C_mul (G : PowerSeries (Qbar l)) (a : Qbar l) (N : ℕ) (z : Qbar l) :
    tval (PowerSeries.C a * G) N z = a * tval G N z := by
  unfold tval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [PowerSeries.coeff_C_mul]; ring

end GlobalTheory.KZ.Cmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoefficientCongruenceOfTwistedValues
section
noncomputable section

open GlobalTheory.KZ GlobalTheory.Ord2 UpperTheory.V.HV Formalism.ConjugateSelfDual PowerSeries

namespace GlobalTheory.KZ.CoefVal

variable {l : ℕ} [Fact l.Prime]

private theorem norm_le_one_of_int' (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormAlgebraMap.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem (c : Coef l) {x : PadicAlgCl l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 := by
  haveI := c.fin
  exact norm_le_one_of_int' x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

theorem norm_unit (c : Coef l) (u : c.Oˣ) : ‖((u : c.O) : PadicAlgCl l)‖ = 1 := by
  have h1 : ‖((u : c.O) : PadicAlgCl l)‖ * ‖(((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)‖ = 1 := by
    rw [← norm_mul, ← Subalgebra.coe_mul, Units.mul_inv]; simp
  have h2 := norm_le_one_of_mem c (u : c.O).2
  have h3 := norm_le_one_of_mem c ((u⁻¹ : c.Oˣ) : c.O).2
  have h4 := norm_nonneg ((u : c.O) : PadicAlgCl l)
  have h5 := norm_nonneg (((u⁻¹ : c.Oˣ) : c.O) : PadicAlgCl l)
  refine le_antisymm h2 ?_
  nlinarith

theorem norm_l : ‖((l : ℕ) : PadicAlgCl l)‖ = (l : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap', Padic.norm_p]

theorem exists_unif (c : Coef l) : ∃ ϖ : PadicAlgCl l, ∃ s : ℕ, 0 < s ∧ ‖((l : ℕ) : PadicAlgCl l)‖ = ‖ϖ‖ ^ s ∧
    ∀ x ∈ c.O, x = 0 ∨ ∃ j : ℕ, ‖x‖ = ‖ϖ‖ ^ j := by
  haveI := c.dvr
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have key : ∀ y : c.O, y ≠ 0 → ∃ j : ℕ, ‖(y : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ j := by
    intro y hy
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    refine ⟨n, ?_⟩
    rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow, norm_mul, norm_pow, norm_unit, one_mul]
  have hlp : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : l.Prime).one_lt)
  have hl0 : ((l : ℕ) : c.O) ≠ 0 := by
    intro h
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = 0 := by rw [h]; rfl
    have : ((l : ℕ) : PadicAlgCl l) = 0 := by simpa using h'
    exact (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) this
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hl0 hϖ
  have hnorm : ‖((l : ℕ) : PadicAlgCl l)‖ = ‖(ϖ : PadicAlgCl l)‖ ^ n := by
    have h' : (((l : ℕ) : c.O) : PadicAlgCl l) = ((u : c.O) : PadicAlgCl l) * (ϖ : PadicAlgCl l) ^ n := by
      rw [hu, Subalgebra.coe_mul, Subalgebra.coe_pow]
    have h'' : (((l : ℕ) : c.O) : PadicAlgCl l) = ((l : ℕ) : PadicAlgCl l) := by simp
    rw [← h'', h', norm_mul, norm_pow, norm_unit, one_mul]
  refine ⟨ϖ, n, ?_, hnorm, ?_⟩
  · rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h, pow_zero, norm_l] at hnorm
      linarith
    · exact h
  · intro x hx
    by_cases h : x = 0
    · exact Or.inl h
    · right
      exact key ⟨x, hx⟩ (fun h' => h (congrArg Subtype.val h'))

theorem norm_eq_one_of_pow {z : PadicAlgCl l} {N : ℕ} (hN : 0 < N) (hz : z ^ N = 1) : ‖z‖ = 1 := by
  have : ‖z‖ ^ N = 1 := by rw [← norm_pow, hz, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hN.ne').1 this

theorem norm_one_sub_pow_le {z : PadicAlgCl l} (hz : ‖z‖ = 1) (b : ℕ) : ‖1 - z ^ b‖ ≤ ‖1 - z‖ := by
  have : 1 - z ^ b = (1 - z) * ∑ i ∈ Finset.range b, z ^ i := by
    rw [mul_comm, geom_sum_mul_neg]
  rw [this, norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    (fun i _ => by rw [norm_pow, hz, one_pow])

theorem norm_one_sub_prim {z : PadicAlgCl l} {m : ℕ} (hz : IsPrimitiveRoot z (l ^ (m + 1))) :
    ‖1 - z‖ ^ Nat.totient (l ^ (m + 1)) = ‖((l : ℕ) : PadicAlgCl l)‖ := by
  have hpos : 0 < l ^ (m + 1) := pow_pos (Fact.out : l.Prime).pos _
  have hcyc := Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz
  have h1 : Polynomial.eval 1 (Polynomial.cyclotomic (l ^ (m + 1)) (PadicAlgCl l)) = l :=
    Polynomial.eval_one_cyclotomic_prime_pow m
  rw [hcyc, Polynomial.eval_prod] at h1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  have hz1 : ‖z‖ = 1 := norm_eq_one_of_pow hpos hz.pow_eq_one
  have h2 : ∀ μ ∈ primitiveRoots (l ^ (m + 1)) (PadicAlgCl l), ‖1 - μ‖ = ‖1 - z‖ := by
    intro μ hμ
    have hμ' := (mem_primitiveRoots hpos).1 hμ
    have hμ1 : ‖μ‖ = 1 := norm_eq_one_of_pow hpos hμ'.pow_eq_one
    obtain ⟨i, -, hi⟩ := hz.eq_pow_of_pow_eq_one hμ'.pow_eq_one
    obtain ⟨j, -, hj⟩ := hμ'.eq_pow_of_pow_eq_one hz.pow_eq_one
    apply le_antisymm
    · rw [← hi]; exact norm_one_sub_pow_le hz1 i
    · calc ‖1 - z‖ = ‖1 - μ ^ j‖ := by rw [hj]
        _ ≤ ‖1 - μ‖ := norm_one_sub_pow_le hμ1 j
  rw [← h1, norm_prod, Finset.prod_congr rfl h2, Finset.prod_const, hz.card_primitiveRoots]

theorem coeff_cg_of_values : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (F : PowerSeries (Qbar l)) (k m₁ : ℕ),
    (∀ n, F.coeff n ∈ c.O) → (∀ m, m₁ ≤ m → ∀ z : Qbar l, IsPrimitiveRoot z (l ^ m) → Cg k (tval F (l ^ (3 * m)) z) 0) →
    ∀ n, Cg k (F.coeff n) 0 := by
  intro l _ c F k m₁ hF hval n₀
  have hlP : l.Prime := Fact.out
  unfold Cg
  rw [sub_zero]
  by_contra hlt
  push_neg at hlt
  obtain ⟨ϖ, s, hs, hls, hdisc⟩ := exists_unif c
  set q := ‖ϖ‖ with hq
  have hlpos : (0 : ℝ) < (l : ℝ)⁻¹ := by have := hlP.pos; positivity
  have hlone : (l : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hlP.one_lt)
  have hl0 : 0 < q ^ s := by rw [← hls, norm_l]; exact hlpos
  have hl1 : q ^ s < 1 := by rw [← hls, norm_l]; exact hlone
  have hq0 : 0 < q := by
    by_contra hc
    push_neg at hc
    have h0 : q = 0 := le_antisymm hc (norm_nonneg _)
    rw [h0, zero_pow hs.ne'] at hl0
    exact lt_irrefl _ hl0
  have hq1 : q < 1 := (pow_lt_one_iff_of_nonneg hq0.le hs.ne').1 hl1
  have hlk : ‖((l : ℕ) : Qbar l) ^ k‖ = q ^ (s * k) := by
    rw [norm_pow, pow_mul]; congr 1
  have hex : ∃ J, ∃ n, ‖F.coeff n‖ = q ^ J := by
    rcases hdisc _ (hF n₀) with h | ⟨j, hj⟩
    · exfalso; rw [h, norm_zero] at hlt; exact absurd hlt (not_lt.2 (norm_nonneg _))
    · exact ⟨j, n₀, hj⟩
  classical
  have hJ := Nat.find_spec hex
  set J := Nat.find hex with hJdef
  have hle : ∀ n, ‖F.coeff n‖ ≤ q ^ J := by
    intro n
    rcases hdisc _ (hF n) with h | ⟨j, hj⟩
    · rw [h, norm_zero]; positivity
    · rw [hj]; exact pow_le_pow_of_le_one hq0.le hq1.le (Nat.find_min' hex ⟨n, hj⟩)
  have hd := Nat.find_spec hJ
  set d := Nat.find hJ with hddef
  have hbefore : ∀ n < d, ‖F.coeff n‖ ≤ q ^ (J + 1) := by
    intro n hn
    rcases hdisc _ (hF n) with h | ⟨j, hj⟩
    · rw [h, norm_zero]; positivity
    · rw [hj]
      apply pow_le_pow_of_le_one hq0.le hq1.le
      have h1 : J ≤ j := Nat.find_min' hex ⟨n, hj⟩
      have h2 : j ≠ J := fun h => Nat.find_min hJ hn (by rw [hj, h])
      omega
  have hJk : J + 1 ≤ s * k := by
    have h1 : q ^ (s * k) < q ^ J := by
      rw [← hlk]; exact lt_of_lt_of_le hlt (hle n₀)
    have := (pow_lt_pow_iff_right_of_lt_one₀ hq0 hq1).1 h1
    omega

  set M := m₁ + d * s + 1 with hM
  haveI : NeZero (l ^ (M + 1)) := ⟨pow_ne_zero _ hlP.ne_zero⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) (l ^ (M + 1))
  have h := hval (M + 1) (by omega) z hz
  unfold Cg at h
  rw [sub_zero, hlk] at h
  set a := ‖z - 1‖ with ha
  have hphi := norm_one_sub_prim hz
  rw [norm_sub_rev, ← ha, hls] at hphi
  have htot : d * s < Nat.totient (l ^ (M + 1)) := by
    rw [Nat.totient_prime_pow_succ hlP]
    have h1 : M < l ^ M := Nat.lt_pow_self hlP.one_lt
    have h2 : 1 ≤ l - 1 := by have := hlP.two_le; omega
    calc d * s < M := by omega
      _ < l ^ M := h1
      _ ≤ l ^ M * (l - 1) := Nat.le_mul_of_pos_right _ h2
  have htpos : 0 < Nat.totient (l ^ (M + 1)) := by omega
  have ha0 : 0 < a := by
    by_contra hc
    push_neg at hc
    have h0 : a = 0 := le_antisymm hc (norm_nonneg _)
    rw [h0, zero_pow htpos.ne'] at hphi
    rw [← hphi] at hl0
    exact lt_irrefl _ hl0
  have ha1 : a < 1 := by
    have : a ^ Nat.totient (l ^ (M + 1)) < 1 := by rw [hphi]; exact hl1
    exact (pow_lt_one_iff_of_nonneg ha0.le htpos.ne').1 this
  have hqa : q < a ^ d := by
    by_contra hc
    push_neg at hc
    have h1 : a ^ (d * s) ≤ a ^ Nat.totient (l ^ (M + 1)) := by
      rw [hphi, pow_mul]; exact pow_le_pow_left₀ (by positivity) hc s
    have := (pow_le_pow_iff_right_of_lt_one₀ ha0 ha1).1 h1
    omega

  set N := l ^ (3 * (M + 1)) with hN
  have hdN : d < N := by
    have : 3 * (M + 1) < l ^ (3 * (M + 1)) := Nat.lt_pow_self hlP.one_lt
    have : d ≤ d * s := Nat.le_mul_of_pos_right d hs
    omega
  have hdmem : d ∈ Finset.range N := Finset.mem_range.2 hdN
  have hsplit : tval F N z = F.coeff d * (z - 1) ^ d +
      ∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n := by
    unfold tval
    exact (Finset.add_sum_erase _ _ hdmem).symm
  have hmain : ‖F.coeff d * (z - 1) ^ d‖ = q ^ J * a ^ d := by
    rw [norm_mul, norm_pow, hd]
  have hB : max (q ^ (J + 1)) (q ^ J * a ^ (d + 1)) < q ^ J * a ^ d := by
    have hqJ : 0 < q ^ J := pow_pos hq0 J
    apply max_lt
    · rw [pow_succ]; exact mul_lt_mul_of_pos_left hqa hqJ
    · rw [pow_succ, ← mul_assoc]
      exact mul_lt_of_lt_one_right (mul_pos hqJ (pow_pos ha0 d)) ha1
  have hrest : ‖∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n‖ ≤
      max (q ^ (J + 1)) (q ^ J * a ^ (d + 1)) := by
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) fun n hn => ?_
    have hnd : n ≠ d := (Finset.mem_erase.1 hn).1
    rw [norm_mul, norm_pow, ← ha]
    rcases lt_or_gt_of_ne hnd with h' | h'
    · refine le_max_of_le_left ?_
      calc ‖F.coeff n‖ * a ^ n ≤ q ^ (J + 1) * 1 :=
            mul_le_mul (hbefore n h') (pow_le_one₀ ha0.le ha1.le) (by positivity) (by positivity)
        _ = q ^ (J + 1) := mul_one _
    · refine le_max_of_le_right ?_
      exact mul_le_mul (hle n) (pow_le_pow_of_le_one ha0.le ha1.le h') (by positivity) (by positivity)
  have hval' : ‖tval F N z‖ = q ^ J * a ^ d := by
    rw [hsplit, ← hmain]
    have hne : ‖F.coeff d * (z - 1) ^ d‖ ≠ ‖∑ n ∈ (Finset.range N).erase d, F.coeff n * (z - 1) ^ n‖ := by
      rw [hmain]; exact (lt_of_le_of_lt hrest hB).ne'
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, max_eq_left]
    rw [hmain]; exact hrest.trans hB.le
  rw [hval'] at h
  have h1 : q ^ (s * k) ≤ q ^ (J + 1) := pow_le_pow_of_le_one hq0.le hq1.le hJk
  have h2 : q ^ (J + 1) < q ^ J * a ^ d := by
    rw [pow_succ]; exact mul_lt_mul_of_pos_left hqa (pow_pos hq0 J)
  linarith

end GlobalTheory.KZ.CoefVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousResiduePlaneGaloisRepUnramifiedOutsideStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_residuePlaneGaloisRep_unramifiedOutside : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (hO : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ (toGS Ω (S : Set Pl)).ker, W a = 1), Continuous W → ContAction (resRep c W hO S hN) := by
  first | exact @GlobalTheory.Ord2.resRep_contAction | exact GlobalTheory.Ord2.resRep_contAction | (intros; apply GlobalTheory.Ord2.resRep_contAction <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CyclotomicDvdOfAevalPrimitiveRootInertiaFixed
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne.CycDvd

theorem apply_eq_pow (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (s : G ℚ Ω)
    {t : Ω} (ht : t ^ (l ^ n) = 1) : s t = t ^ ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)).val := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  haveI : NeZero (l : Ω) := ⟨by exact_mod_cast (Fact.out : l.Prime).ne_zero⟩
  have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) t ht
  have h2 : (cyclotomicCharacter Ω l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s)).val.toZModPow n =
      ((cycMod ℚ Ω l n s : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) := by
    simp [cycMod, cycZ]
  rw [h2] at h1
  exact h1

theorem exists_Ine_apply_eq (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : A.valuation (l : Ω) < 1) (n : ℕ) {z μ : Ω} (hz : IsPrimitiveRoot z (l ^ n))
    (hμ : IsPrimitiveRoot μ (l ^ n)) : ∃ s ∈ Ine (F := ℚ) A, s z = μ := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  obtain ⟨i, hi, hcop, rfl⟩ := (hz.isPrimitiveRoot_iff).1 hμ
  obtain ⟨⟨s, hs⟩, hsu⟩ := GlobalTheory.InertiaPowers.cycMod_Ine_surjective l Ω A hA n (ZMod.unitOfCoprime i hcop)
  refine ⟨s, hs, ?_⟩
  have hsu' : cycMod ℚ Ω l n s = ZMod.unitOfCoprime i hcop := hsu
  rw [apply_eq_pow l Ω n s hz.pow_eq_one, hsu', ZMod.coe_unitOfCoprime, ZMod.val_natCast, Nat.mod_eq_of_lt hi]

theorem cyclotomic_dvd : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (n : ℕ) (z : A), IsPrimitiveRoot (z : Ω) (l ^ n) → ∀ R : Polynomial (fixA A), Polynomial.aeval z R = 0 → Polynomial.cyclotomic (l ^ n) (fixA A) ∣ R := by
  intro l _ Ω _ _ _ A hO n z hz R hR
  classical
  have hA : A.valuation (l : Ω) < 1 := by
    obtain ⟨v, hv, hl⟩ := hO
    have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
    simpa using h1
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  let f : fixA A →+* Ω := A.subtype.comp (fixA A).subtype
  have hf : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  have h0 : Polynomial.eval₂ f (z : Ω) R = 0 := by
    have := Polynomial.hom_eval₂ R (algebraMap (fixA A) A) A.subtype z
    rw [← Polynomial.aeval_def, hR, map_zero] at this
    exact this.symm
  have hroot : ∀ μ ∈ primitiveRoots (l ^ n) Ω, (R.map f).eval μ = 0 := by
    intro μ hμ
    obtain ⟨s, hs, rfl⟩ := exists_Ine_apply_eq l Ω A hA n hz ((mem_primitiveRoots hpos).1 hμ)
    have e := Polynomial.hom_eval₂ R f (s : Ω →+* Ω) (z : Ω)
    have e2 : (s : Ω →+* Ω).comp f = f := RingHom.ext fun a => a.2 s hs
    rw [h0, map_zero, e2] at e
    rw [Polynomial.eval_map]
    exact e.symm
  rw [← Polynomial.map_dvd_map f hf (Polynomial.cyclotomic.monic _ _), Polynomial.map_cyclotomic,
    Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hz]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro a _ b _ hab
    exact Polynomial.isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit
  · intro μ hμ
    exact Polynomial.dvd_iff_isRoot.2 (hroot μ hμ)

end GlobalTheory.RecOne.CycDvd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondCommutesHeckeUStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diamond_commutes_hecke_U : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (w d : ℕ), d.Coprime N → ¬ l ∣ N → ∀ b : X.Fn l, b ∈ X.B N l w →
  X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) (X.heckeU l b) = X.heckeU l (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  first | exact @GlobalTheory.KZ.DiamU.act_sgD_heckeU | exact GlobalTheory.KZ.DiamU.act_sgD_heckeU | (intros; apply GlobalTheory.KZ.DiamU.act_sgD_heckeU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualCocycleCoboundaryOnInertiaOfOrthogonal
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

namespace GlobalTheory.Ord2.GwIneq

theorem cob_of_perp_transport {R : Type} [CommRing R] [TopologicalSpace R] [DiscreteTopology R]
    {Γ D : Type} [Group Γ] [Group D] [TopologicalSpace D]
    {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (μ : Γ →* Rˣ) (rho : Representation R Γ M) (φ : D →* Γ) (J : Subgroup D)
    (h : ContAction (rho.comp φ)) (h' : ContAction ((rho.comp φ).comp (MonoidHom.id D)))
    (key : ∀ y : H1 (twDual (μ.comp φ) (rho.comp φ)),
      (∀ x ∈ H1ur (rho.comp φ) J, cupH1H1TwistedDual (μ.comp φ) (rho.comp φ) (MonoidHom.id D) h' y x = 0) →
        y ∈ H1ur (twDual (μ.comp φ) (rho.comp φ)) J)
    (f : Z1 ((twDual μ rho).comp φ))
    (hf : ∀ a ∈ H1ur (rho.comp φ) J, cupH1H1TwistedDual μ rho φ h (Submodule.mkQ _ f) a = 0) :
    ∃ m : TDual R M, ∀ s ∈ J, f.1 s = twDual μ rho (φ s) m - m := by
  have heq : twDual (μ.comp φ) (rho.comp φ) = (twDual μ rho).comp φ := by
    refine MonoidHom.ext fun s => LinearMap.ext fun ψ => TDual.ext fun x => ?_
    simp only [MonoidHom.comp_apply, twDual_apply, map_inv φ]
  have hf' : f.1 ∈ Z1 (twDual (μ.comp φ) (rho.comp φ)) := by rw [heq]; exact f.2
  have hy := key (Submodule.Quotient.mk ⟨f.1, hf'⟩) (by
    intro x hx
    induction x using Submodule.Quotient.induction_on with | H a =>
    have e := hf _ hx
    have e' := (Submodule.Quotient.mk_eq_zero _).1 e
    exact (Submodule.Quotient.mk_eq_zero _).2 e')
  rw [H1ur, LinearMap.mem_ker] at hy
  change Submodule.Quotient.mk (restrictCocycles1 _ J.subtype continuous_subtype_val ⟨f.1, hf'⟩) = 0 at hy
  rw [Submodule.Quotient.mk_eq_zero] at hy
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hy
  refine ⟨m, fun s hs => ?_⟩
  have e := hm ⟨s, hs⟩
  change f.1 s = twDual (μ.comp φ) (rho.comp φ) s m - m at e
  rw [e, heq]
  rfl

theorem dual_cocycle_cob_on_inertia : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ), 1 ≤ n → ∀ (S : Finset Pl) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ n)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (rho : Representation (ZMod (l ^ n)) (GS Ω (S : Set Pl)) M) (hrho : ContAction rho) (μ : GS Ω (S : Set Pl) →* (ZMod (l ^ n))ˣ), μ.comp (toGS Ω (S : Set Pl)) = cycMod ℚ Ω l n → ∀ (B : ValuationSubring Ω) (q : Pl), IsPlaceOver B q → ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ f : Z1 ((twDual μ rho).comp (locHom (S : Set Pl) B)), (∀ a ∈ H1ur (rho.comp (locHom (S : Set Pl) B)) ((Ine (F := ℚ) B).subgroupOf (Dec (F := ℚ) B)), cupH1H1TwistedDual μ rho (locHom (S : Set Pl) B) (hrho.comp' (continuous_locHom _ B)) (Submodule.mkQ _ f) a = 0) → ∃ m : TDual (ZMod (l ^ n)) M, ∀ s : Dec (F := ℚ) B, (s : G ℚ Ω) ∈ Ine (F := ℚ) B → f.1 s = twDual μ rho (locHom (S : Set Pl) B s) m - m := by
  intro hL l _ Ω _ _ _ n hn S M _ _ _ _ _ rho hrho μ hμ B q hq hl f hf
  have hχ : (cycMod ℚ Ω l n).comp (Dec (F := ℚ) B).subtype = μ.comp (locHom (S : Set Pl) B) := by
    rw [← hμ]; rfl
  have hc := hrho.comp' (continuous_locHom (S : Set Pl) B)
  have key := GlobalTheory.Ord2.unramified_h1_dual_iff_perp hL ℚ Ω l n M B q (rho.comp (locHom (S : Set Pl) B)) hc
    hq hn hl
  rw [hχ] at key
  obtain ⟨m, hm⟩ := cob_of_perp_transport μ rho (locHom (S : Set Pl) B) _ hc _
    (fun y hy => (key y).2 hy) f hf
  exact ⟨m, fun s hs => hm s (Subgroup.mem_subgroupOf.2 hs)⟩

end GlobalTheory.Ord2.GwIneq
end

