import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnramifiedSplitting.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0002

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.SumRangeRatAdeleCharIotaMulOneSubEqIte
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private theorem psi_add (x y : A ℚ) : ψ (x + y) = ψ x * ψ y := by
  simp only [ψ, AddChar.map_add_eq_mul, Circle.coe_mul]

private theorem psi_eq_one_iff (x : A ℚ) : ψ x = 1 ↔ adelicChar ℚ x = 1 := Circle.coe_eq_one

private theorem psi_neg_of_one {x : A ℚ} (h : ψ x = 1) : ψ (-x) = 1 := by
  rw [psi_eq_one_iff] at *
  rw [AddChar.map_neg_eq_inv, h, inv_one]

private theorem psi_zsmul (m : ℤ) {x : A ℚ} (h : ψ x = 1) : ψ (m • x) = 1 := by
  rw [psi_eq_one_iff] at *
  rw [AddChar.map_zsmul_eq_zpow, h, _root_.one_zpow]

private theorem psi_nsmul (a : ℕ) (x : A ℚ) : ψ (a • x) = ψ x ^ a := by
  simp only [ψ, AddChar.map_nsmul_eq_pow, Circle.coe_pow]

private theorem psi_Oh {c : A ℚ} (hc : c ∈ Oh ℚ) : ψ c = 1 := by
  have h : c ∈ invDifferentAdeles ℚ :=
    mem_invDifferentAdeles.2 (mem_finiteInvDifferent.2 fun v =>
      mem_localInvDifferent_of_mem (hc.2 v))
  rw [psi_eq_one_iff, adelicChar_of_mem_invDifferentAdeles h, hc.1]
  simp

private theorem different_rat : differentIdeal ℤ (𝓞 ℚ) = ⊤ := by
  rw [← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal (K := ℚ), NumberField.discr_rat]
  rfl

private theorem mem_inv_iff (v : H.P ℚ) (x : H.Kv v) : x ∈ localInvDifferent v ↔ Valued.v x ≤ 1 := by
  rw [mem_localInvDifferent_iff_valued, different_rat]
  simp [FractionalIdeal.count_one]

private theorem psi_sg_eq (v : H.P ℚ) (x : H.Kv v) : ψ (H.sg v x) = (localAdelicChar ℚ v x : ℂ) := rfl

private noncomputable def eA : A ℚ := (0, 1)

private theorem fin_alg_val {K : Type} [Field K] [NumberField K] (v : H.P K) (a : K) :
    Valued.v ((algebraMap K (FiniteAdeleRing (𝓞 K) K) a) v) = v.valuation K a :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v a

private theorem nat_val (v : H.P ℚ) (n : ℕ) : Valued.v ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) v) ≤ 1 := by
  have e : (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v = (n : H.Kv v) := map_natCast (pLoc ℚ v) n
  rw [e]
  exact natCast_mem (v.adicCompletionIntegers ℚ) n

private theorem decomp (n : ℕ) (hn : 0 < n) {c : A ℚ} (hc : c ∈ Oh ℚ) :
    ∃ (m : ℤ) (c' : A ℚ), c' ∈ Oh ℚ ∧ c = m • eA + (n : A ℚ) * c' := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨k, hk⟩ := exists_sub_mem_finiteInvDifferent (K := ℚ)
    (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ * c.2)
  obtain ⟨f, hf⟩ : ∃ f, f = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ * c.2 -
      algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) k := ⟨_, rfl⟩
  rw [← hf] at hk
  have hfv : ∀ v : H.P ℚ, Valued.v (f v) ≤ 1 := fun v =>
    (mem_inv_iff v _).1 (mem_finiteInvDifferent.1 hk v)
  have hnn : (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (n : ℚ)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) n, ← map_mul, mul_inv_cancel₀ hn0, map_one]
  have key : c.2 = (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * f + algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k) := by
    rw [hf, map_mul, map_natCast, mul_sub, ← mul_assoc, hnn, one_mul, sub_add_cancel]
  have hint : ∀ v : H.P ℚ, v.valuation ℚ ((n : ℚ) * k) ≤ 1 := by
    intro v
    have e : (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k)) v = c.2 v - (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * f v := by
      have h2 : c.2 v = (n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * f v + (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) ((n : ℚ) * k)) v :=
        congrArg (fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => x v) key
      rw [h2]
      ring
    rw [← fin_alg_val, e]
    refine (Valuation.map_sub _ _ _).trans (max_le (hc.2 v) ?_)
    rw [map_mul]
    exact mul_le_one' (nat_val v n) (hfv v)
  obtain ⟨r, hr⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one ℚ _ hint
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.1 (r.2 : IsIntegral ℤ (r : ℚ))
  have hmk : (n : ℚ) * k = (m : ℚ) := by
    exact hr.symm.trans (hm.symm.trans (eq_intCast (algebraMap ℤ ℚ) m))
  refine ⟨m, ((0, f) : InfiniteAdeleRing ℚ × FiniteAdeleRing (𝓞 ℚ) ℚ), ⟨rfl, hfv⟩, ?_⟩
  refine Prod.ext ?_ ?_
  · change c.1 = m • (0 : InfiniteAdeleRing ℚ) + (n : A ℚ).1 * 0
    rw [hc.1]
    simp
  · change c.2 = m • (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) + (n : FiniteAdeleRing (𝓞 ℚ) ℚ) * f
    rw [key, hmk, map_intCast, zsmul_one, add_comm]

private theorem local_good (v : H.P ℚ) (x : H.Kv v)
    (h : ∀ c : H.Kv v, Valued.v c ≤ 1 → ψ (H.sg v (c * x)) = 1) : Valued.v x ≤ 1 := by
  refine (mem_inv_iff v x).1 ((forall_localAdelicChar_mul_eq_one_iff v x).1 fun a ha => ?_)
  have := h a ha
  rw [psi_sg_eq] at this
  exact Circle.coe_eq_one.1 this

private theorem sg_oh (v : H.P ℚ) (c : H.Kv v) (hc : Valued.v c ≤ 1) : H.sg v c ∈ Oh ℚ := by
  obtain ⟨-, -, hcp, -, -, -, -, hs, -, -⟩ := H.sgLaws ℚ v
  refine ⟨(hs c).1, fun w => ?_⟩
  by_cases h : w = v
  · subst h
    have : (H.sg w c).2 w = c := hcp c
    rw [this]
    exact hc
  · rw [(hs c).2 w h, map_zero]
    exact zero_le'

private theorem oh_nat_mul (n : ℕ) {c : A ℚ} (hc : c ∈ Oh ℚ) : (n : A ℚ) * c ∈ Oh ℚ := by
  refine ⟨?_, fun v => ?_⟩
  · change (n : A ℚ).1 * c.1 = 0
    rw [hc.1, mul_zero]
  · change Valued.v ((n : FiniteAdeleRing (𝓞 ℚ) ℚ) v * c.2 v) ≤ 1
    rw [map_mul]
    exact mul_le_one' (nat_val v n) (hc.2 v)

private theorem eA_mem : eA ∈ Oh ℚ := by
  refine ⟨rfl, fun v => ?_⟩
  change Valued.v (1 : H.Kv v) ≤ 1
  rw [map_one]

private theorem eA_mul {c : A ℚ} (hc : c.1 = 0) : eA * c = c := by
  refine Prod.ext ?_ ?_
  · change 0 * c.1 = c.1
    rw [hc, mul_zero]
  · change 1 * c.2 = c.2
    rw [one_mul]

private theorem L_iota (L : ℕ) (hL : 0 < L) : (L : A ℚ) * iota L = eA := by
  have hL0 : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  refine Prod.ext ?_ ?_
  · change (L : A ℚ).1 * 0 = 0
    rw [mul_zero]
  · change (L : FiniteAdeleRing (𝓞 ℚ) ℚ) * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ)⁻¹ = 1
    rw [← map_natCast (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)) L, ← map_mul, mul_inv_cancel₀ hL0, map_one]

private theorem psi_mul_of_one (L M : ℕ) (hL : 0 < L) (hM : 0 < M) (y : A ℚ)
    (hy : ∀ c ∈ Oh ℚ, ψ (y * ((M : A ℚ) * c)) = 1) (hz : ψ (iota L * (1 - y)) = 1)
    {c : A ℚ} (hc : c ∈ Oh ℚ) : ψ (c * (iota L * (1 - y))) = 1 := by
  obtain ⟨m, c', hc', e⟩ := decomp (L * M) (Nat.mul_pos hL hM) hc
  have hw : (iota L * (1 - y)).1 = 0 := by
    change (0 : InfiniteAdeleRing ℚ) * (1 - y).1 = 0
    rw [zero_mul]
  have e2 : c * (iota L * (1 - y)) =
      m • (iota L * (1 - y)) + ((M : A ℚ) * c' + -(y * ((M : A ℚ) * c'))) := by
    have h1 : ((L * M : ℕ) : A ℚ) * c' * (iota L * (1 - y)) = (M : A ℚ) * c' - y * ((M : A ℚ) * c') := by
      have h2 : ((L * M : ℕ) : A ℚ) * c' * (iota L * (1 - y)) = (M : A ℚ) * (eA * c') * (1 - y) := by
        rw [← L_iota L hL]
        push_cast
        ring
      rw [h2, eA_mul hc'.1]
      ring
    rw [e, add_mul, h1, zsmul_eq_mul, mul_assoc, ← zsmul_eq_mul, eA_mul hw, sub_eq_add_neg ((M : A ℚ) * c')]
  rw [e2, psi_add, psi_add, psi_zsmul m hz, psi_Oh (oh_nat_mul M hc'), psi_neg_of_one (hy c' hc')]
  simp

private theorem val_iff (L : ℕ) (hL : 0 < L) (y : A ℚ) (v : H.P ℚ) :
    Dv L v (y - 1) ↔ Valued.v (H.cp v (iota L * (1 - y))) ≤ 1 := by
  have hab : Valued.v (L : H.Kv v) * Valued.v (H.cp v (iota L)) = 1 := by
    have e : (L : H.Kv v) * H.cp v (iota L) = 1 := by
      have h1 : H.cp v ((L : A ℚ) * iota L) = 1 := by
        rw [L_iota L hL]
        rfl
      rwa [map_mul, map_natCast] at h1
    rw [← map_mul, e, map_one]
  have hx : Valued.v (H.cp v (iota L * (1 - y))) =
      Valued.v (H.cp v (iota L)) * Valued.v (H.cp v (y - 1)) := by
    rw [map_mul, map_mul, ← neg_sub y 1, map_neg, Valuation.map_neg]
  rw [hx]
  unfold Dv
  constructor
  · intro h
    calc _ ≤ Valued.v (H.cp v (iota L)) * Valued.v (L : H.Kv v) := mul_le_mul' le_rfl h
      _ = 1 := by rw [mul_comm, hab]
  · intro h
    calc Valued.v (H.cp v (y - 1)) =
        Valued.v (L : H.Kv v) * (Valued.v (H.cp v (iota L)) * Valued.v (H.cp v (y - 1))) := by
          rw [← mul_assoc, hab, one_mul]
      _ ≤ Valued.v (L : H.Kv v) * 1 := mul_le_mul' le_rfl h
      _ = _ := mul_one _

theorem UpperTheory.sum_range_ratAdeleChar_iota_mul_one_sub_eq_ite :
    ∀ (L M : ℕ), 0 < L → 0 < M → ∀ y : A ℚ, (∀ c ∈ Oh ℚ, ψ (y * ((M : A ℚ) * c)) = 1) → ∑ a ∈ Finset.range (L * M), ψ ((a : A ℚ) * iota L * (1 - y)) = if ∀ v : H.P ℚ, Dv L v (y - 1) then ((L * M : ℕ) : ℂ) else 0 := by
  intro L M hL hM y hy
  have hsum : ∀ a : ℕ, ψ ((a : A ℚ) * iota L * (1 - y)) = ψ (iota L * (1 - y)) ^ a := by
    intro a
    rw [mul_assoc, ← nsmul_eq_mul, psi_nsmul]
  simp only [hsum]
  have hzn : ψ (iota L * (1 - y)) ^ (L * M) = 1 := by
    rw [← psi_nsmul, nsmul_eq_mul]
    have e : ((L * M : ℕ) : A ℚ) * (iota L * (1 - y)) =
        (M : A ℚ) * eA + -(y * ((M : A ℚ) * eA)) := by
      have h1 : ((L * M : ℕ) : A ℚ) * (iota L * (1 - y)) =
          (M : A ℚ) * ((L : A ℚ) * iota L) * (1 - y) := by
        push_cast
        ring
      rw [h1, L_iota L hL]
      ring
    rw [e, psi_add, psi_Oh (oh_nat_mul M eA_mem), psi_neg_of_one (hy eA eA_mem), one_mul]
  have hw1 : (iota L * (1 - y)).1 = 0 := by
    change (0 : InfiniteAdeleRing ℚ) * (1 - y).1 = 0
    rw [zero_mul]
  split_ifs with h
  · have hz : ψ (iota L * (1 - y)) = 1 :=
      psi_Oh ⟨hw1, fun v => (val_iff L hL y v).1 (h v)⟩
    simp [hz]
  · have hz : ψ (iota L * (1 - y)) ≠ 1 := by
      intro hz
      refine h fun v => (val_iff L hL y v).2 (local_good v _ fun c hc => ?_)
      obtain ⟨-, hm, -⟩ := H.sgLaws ℚ v
      rw [mul_comm c, ← hm, mul_comm]
      exact psi_mul_of_one L M hL hM y hy hz (sg_oh v c hc)
    rw [geom_sum_eq hz, hzn]
    simp
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.UnipotentConjCongruenceOfPowFive
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

namespace UpperTheory.OrderAdditiveConjugation

variable {E : Type} [Field E] [NumberField E]

private theorem oh_zero : (0 : A E) ∈ Oh E := by
  refine ⟨rfl, fun v => ?_⟩
  have h : ((0 : A E).2 v) = 0 := rfl
  rw [h, map_zero]
  exact zero_le_one

private theorem oh_add {c d : A E} (hc : c ∈ Oh E) (hd : d ∈ Oh E) : c + d ∈ Oh E := by
  refine ⟨by show c.1 + d.1 = 0; rw [hc.1, hd.1, add_zero], fun v => ?_⟩
  have h : ((c + d).2 v) = c.2 v + d.2 v := rfl
  rw [h]
  exact (Valuation.map_add_le _ (hc.2 v) (hd.2 v))

private theorem oh_neg {c : A E} (hc : c ∈ Oh E) : -c ∈ Oh E := by
  refine ⟨by show -c.1 = 0; rw [hc.1, neg_zero], fun v => ?_⟩
  have h : ((-c).2 v) = -(c.2 v) := rfl
  rw [h, Valuation.map_neg]
  exact hc.2 v

private theorem oh_nat (n : ℕ) {c : A E} (hc : c ∈ Oh E) : (n : A E) * c ∈ Oh E := by
  induction n with
  | zero => simpa using oh_zero
  | succ n ih =>
    have : ((n + 1 : ℕ) : A E) * c = (n : A E) * c + c := by push_cast; ring
    rw [this]
    exact oh_add ih hc

private theorem oh_mul_of {T c : A E} (hT : ∀ w : H.P E, Valued.v (H.cp w T) ≤ 1) (hc : c ∈ Oh E) :
    T * c ∈ Oh E := by
  refine ⟨by show T.1 * c.1 = 0; rw [hc.1, mul_zero], fun v => ?_⟩
  have h : ((T * c).2 v) = H.cp v T * c.2 v := rfl
  rw [h, map_mul]
  exact mul_le_one' (hT v) (hc.2 v)

private theorem rt_mul_nat (L : ℕ) (θ : E) :
    (UpperTheory.ConvolutionTheory.R2.rt ((L : E) * θ) : A E) = (L : A E) * UpperTheory.ConvolutionTheory.R2.rt θ := by
  have : (UpperTheory.ConvolutionTheory.R2.rt ((L : E) * θ) : A E) = algebraMap E (A E) ((L : E) * θ) := rfl
  rw [this, map_mul, map_natCast]

private theorem nat_mul_iota (L : ℕ) (hL : 0 < L) : (L : A ℚ) * iota L = (0, 1) := by
  have hq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  refine Prod.ext ?_ ?_
  · show (L : A ℚ).1 * 0 = 0
    exact mul_zero _
  · show (L : A ℚ).2 * algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ)⁻¹ = 1
    have : (L : A ℚ).2 = algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ) (L : ℚ) := by
      rw [map_natCast]; rfl
    rw [this, ← map_mul, mul_inv_cancel₀ hq, map_one]

private theorem unit_mul (L : ℕ) (hL : 0 < L) {r : A E} (hr : r ∈ Oh E) :
    ((L : A E) * am E (iota L)) * r = r := by
  have h1 : (L : A E) * am E (iota L) = am E ((L : A ℚ) * iota L) := by
    rw [map_mul, map_natCast]
  rw [h1, nat_mul_iota L hL]
  refine Prod.ext ?_ ?_
  · show (am E ((0, 1) : A ℚ)).1 * r.1 = r.1
    rw [hr.1, mul_zero]
  · show (am E ((0, 1) : A ℚ)).2 * r.2 = r.2
    have : (am E ((0, 1) : A ℚ)).2 = 1 := map_one (AdeleBaseChange.finiteAdeleMap ℚ E)
    rw [this, one_mul]

private theorem conj_entry {R : Type} [CommRing R] (O : Set R) (l t : R)
    (hadd : ∀ {c d : R}, c ∈ O → d ∈ O → c + d ∈ O) (hneg : ∀ {c : R}, c ∈ O → -c ∈ O)
    (P Q W : R → R) (hP : ∀ r ∈ O, P r ∈ O) (hQ : ∀ r ∈ O, Q r ∈ O) (hW : ∀ r ∈ O, W r ∈ O)
    (eP : ∀ r ∈ O, l ^ 5 * r = l * P r) (eQ : ∀ r ∈ O, t * (l ^ 5 * r) = l * Q r)
    (eW : ∀ r ∈ O, t * (t * (l ^ 5 * r)) = l * W r)
    (K : Matrix (Fin 2) (Fin 2) R)
    (hK : ∀ i j, ∃ c ∈ O, K i j - (1 : Matrix (Fin 2) (Fin 2) R) i j = l ^ 5 * c) :
    ∀ i j, ∃ c ∈ O, (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) i j - (1 : Matrix (Fin 2) (Fin 2) R) i j = l * c := by
  obtain ⟨c00, m00, h00⟩ := hK 0 0
  obtain ⟨c01, m01, h01⟩ := hK 0 1
  obtain ⟨c10, m10, h10⟩ := hK 1 0
  obtain ⟨c11, m11, h11⟩ := hK 1 1
  simp only [Matrix.one_apply_eq, ne_eq, zero_ne_one, one_ne_zero, not_false_eq_true, Matrix.one_apply_ne, sub_zero] at h00 h01 h10 h11
  have q00 := eQ c00 m00
  have q10 := eQ c10 m10
  have q11 := eQ c11 m11
  have p00 := eP c00 m00
  have p01 := eP c01 m01
  have p10 := eP c10 m10
  have p11 := eP c11 m11
  have w10 := eW c10 m10
  have a00 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 0 = K 0 0 - t * K 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]; ring
  have a01 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 1 = (K 0 0 - t * K 1 0) * t + (K 0 1 - t * K 1 1) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]; ring
  have a10 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 0 = K 1 0 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  have a11 : (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 1 = K 1 0 * t + K 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
  intro i j
  fin_cases i <;> fin_cases j
  · refine ⟨P c00 + -Q c10, hadd (hP _ m00) (hneg (hQ _ m10)), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 0 - (1 : Matrix (Fin 2) (Fin 2) R) 0 0 = _
    rw [a00, Matrix.one_apply_eq]
    linear_combination h00 - t * h10 + p00 - q10
  · refine ⟨Q c00 + P c01 + -W c10 + -Q c11, hadd (hadd (hadd (hQ _ m00) (hP _ m01)) (hneg (hW _ m10))) (hneg (hQ _ m11)), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 0 1 - (1 : Matrix (Fin 2) (Fin 2) R) 0 1 = _
    rw [a01, Matrix.one_apply_ne (by simp)]
    linear_combination t * h00 + h01 - t * t * h10 - t * h11 + q00 + p01 - w10 - q11
  · refine ⟨P c10, hP _ m10, ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 0 - (1 : Matrix (Fin 2) (Fin 2) R) 1 0 = _
    rw [a10, Matrix.one_apply_ne (by simp)]
    linear_combination h10 + p10
  · refine ⟨Q c10 + P c11, hadd (hQ _ m10) (hP _ m11), ?_⟩
    show (!![1, -t; 0, 1] * K * !![1, t; 0, 1]) 1 1 - (1 : Matrix (Fin 2) (Fin 2) R) 1 1 = _
    rw [a11, Matrix.one_apply_eq]
    linear_combination t * h10 + h11 + q10 + p11

end UpperTheory.OrderAdditiveConjugation

open UpperTheory.OrderAdditiveConjugation in
theorem UpperTheory.unipotent_conj_congruence_of_pow_five :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (L a : ℕ), 0 < L → (∀ w : H.P E, Valued.v (H.cp w (rt ((L : E) * D.θ))) ≤ 1) → ∀ κ : GL (Fin 2) (A E), CongE (L ^ 5) κ → CongE L ((nu D ((a : A ℚ) * iota L))⁻¹ * κ * nu D ((a : A ℚ) * iota L)) := by
  intro E _ _ D L a hL hT κ hκ
  obtain ⟨t, htd⟩ : ∃ t, t = D.mkE 0 ((a : A ℚ) * iota L) := ⟨_, rfl⟩
  obtain ⟨ν, hνd⟩ : ∃ ν, ν = nu D ((a : A ℚ) * iota L) := ⟨_, rfl⟩
  rw [← hνd]
  have hν : (ν : Matrix (Fin 2) (Fin 2) (A E)) = !![1, t; 0, 1] := by rw [hνd, htd]; rfl
  have hνi : ((ν⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) = !![1, -t; 0, 1] := by
    rw [Matrix.coe_units_inv, hν]
    apply Matrix.inv_eq_right_inv
    simp [Matrix.one_fin_two]
  have ht : t = (a : A E) * am E (iota L) * UpperTheory.ConvolutionTheory.R2.rt D.θ := by
    rw [htd, Dat.mkE_def, map_zero, map_mul, map_natCast, zero_add]
  obtain ⟨T, hTd⟩ : ∃ T : A E, T = UpperTheory.ConvolutionTheory.R2.rt ((L : E) * D.θ) := ⟨_, rfl⟩
  have hT' : ∀ w : H.P E, Valued.v (H.cp w T) ≤ 1 := by rw [hTd]; exact hT
  have hTe : T = (L : A E) * UpperTheory.ConvolutionTheory.R2.rt D.θ := by rw [hTd, rt_mul_nat]
  have key : ∀ r ∈ Oh E, (L : A E) ^ 2 * t * r = (a : A E) * (T * r) := by
    intro r hr
    have hu := unit_mul L hL hr
    rw [ht, hTe]
    linear_combination ((a : A E) * ((L : A E) * UpperTheory.ConvolutionTheory.R2.rt D.θ)) * hu
  have main := conj_entry (Oh E) (L : A E) t oh_add oh_neg
    (fun r => ((L ^ 4 : ℕ) : A E) * r)
    (fun r => ((L ^ 2 * a : ℕ) : A E) * (T * r))
    (fun r => ((a ^ 2 : ℕ) : A E) * (T * (T * r)))
    (fun r hr => oh_nat _ hr)
    (fun r hr => oh_nat _ (oh_mul_of hT' hr))
    (fun r hr => oh_nat _ (oh_mul_of hT' (oh_mul_of hT' hr)))
    (fun r _ => by push_cast; ring)
    (fun r hr => by
      have := key r hr
      push_cast
      linear_combination (L : A E) ^ 3 * this)
    (fun r hr => by
      have h1 := key r hr
      have h2 := key (T * r) (oh_mul_of hT' hr)
      push_cast
      linear_combination ((L : A E) ^ 3 * t) * h1 + ((L : A E) * (a : A E)) * h2)
  have cast5 : ∀ {x : A E} {c : A E}, x = ((L ^ 5 : ℕ) : A E) * c → x = (L : A E) ^ 5 * c := by
    intro x c h; rw [h, Nat.cast_pow]
  have hinv : (ν⁻¹ * κ * ν)⁻¹ = ν⁻¹ * κ⁻¹ * ν := by group
  intro i j
  constructor
  · obtain ⟨c, hc, e⟩ := main (κ : Matrix (Fin 2) (Fin 2) (A E))
      (fun i j => by
        obtain ⟨c, hc, e⟩ := (hκ i j).1
        exact ⟨c, hc, cast5 e⟩) i j
    refine ⟨c, hc, ?_⟩
    rw [← e, Units.val_mul, Units.val_mul, hν, hνi]
  · obtain ⟨c, hc, e⟩ := main ((κ⁻¹ : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E))
      (fun i j => by
        obtain ⟨c, hc, e⟩ := (hκ i j).2
        exact ⟨c, hc, cast5 e⟩) i j
    refine ⟨c, hc, ?_⟩
    rw [← e, hinv, Units.val_mul, Units.val_mul, hν, hνi]
end

-- bundled from Development.AutomorphicArithmetic.WhittakerHecke.UnipotentNatDivMemMaximalCompactOfNotBadPrime
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

private lemma nL_memK {K : Type} [Field K] [NumberField K] {v : H.P K} {c : H.Kv v} (hc : Valued.v c ≤ 1) :
    H.nL c ∈ GlobalTheory.LFun.KGL v 2 := by
  have hc' : c ∈ v.adicCompletionIntegers K := hc
  have hn : -c ∈ v.adicCompletionIntegers K := neg_mem hc'
  rw [GlobalTheory.LFun.KGL, GlobalTheory.AdelicU.mem_GLint_iff]
  have h1 : (1 : H.Kv v) ∈ Formalism.UG.Ov K v := one_mem _
  have h0 : (0 : H.Kv v) ∈ Formalism.UG.Ov K v := zero_mem _
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hc'
    · exact h0
    · exact h1
  · fin_cases i <;> fin_cases j
    · exact h1
    · exact hn
    · exact h0
    · exact h1

private lemma map_gl_nU {K : Type} [Field K] [NumberField K] (v : H.P K) (z : A K) :
    Matrix.GeneralLinearGroup.map (H.cp v) (gl (nU z)) = H.nL (H.cp v z) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j
  · exact map_one (H.cp v)
  · rfl
  · exact map_zero (H.cp v)
  · exact map_one (H.cp v)

private lemma val_nat_one {E : Type} [Field E] [NumberField E] (w : H.P E) (L : ℕ)
    (hL : (L : 𝓞 E) ∉ w.asIdeal) : Valued.v (L : H.Kv w) = 1 := by
  have h1 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := E) w (L : 𝓞 E)
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hL] at h1
  simpa using h1

private lemma val_nat_le {E : Type} [Field E] [NumberField E] (w : H.P E) (a : ℕ) :
    Valued.v (a : H.Kv w) ≤ 1 :=
  show (a : H.Kv w) ∈ w.adicCompletionIntegers E from natCast_mem _ a

private lemma not_mem_of_bad {E : Type} [Field E] [NumberField E] (w : H.P E) (L : ℕ)
    (h : ¬ Bad L (w.under (𝓞 ℚ))) : (L : 𝓞 E) ∉ w.asIdeal := by
  intro hm
  apply h
  show (L : 𝓞 ℚ) ∈ (w.under (𝓞 ℚ)).asIdeal
  change (L : 𝓞 ℚ) ∈ w.asIdeal.comap (algebraMap (𝓞 ℚ) (𝓞 E))
  rw [Ideal.mem_comap, map_natCast]
  exact hm

private lemma cp_iota (v : H.P ℚ) (L : ℕ) : H.cp v (iota L) = (L : H.Kv v)⁻¹ := by
  have h := eq_ratCast ((pLoc ℚ v).comp (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))) (L : ℚ)⁻¹
  have e : H.cp v (iota L) = ((pLoc ℚ v).comp (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ))) (L : ℚ)⁻¹ := rfl
  rw [e, h]
  push_cast
  rfl

private lemma completion_adele_natural {E : Type} [Field E] [NumberField E] (w : H.P E) (L a : ℕ) :
    H.cp w (AdeleBaseChange.adeleMap ℚ E ((a : A ℚ) * iota L)) = (a : H.Kv w) * (L : H.Kv w)⁻¹ := by
  have h : ((a : A ℚ) * iota L).2 (AdeleBaseChange.below ℚ w) =
      (a : H.Kv (AdeleBaseChange.below ℚ w)) * (L : H.Kv (AdeleBaseChange.below ℚ w))⁻¹ := by
    have := map_mul (H.cp (AdeleBaseChange.below ℚ w)) (a : A ℚ) (iota L)
    rw [cp_iota, map_natCast] at this
    exact this
  show SemiLocal.completionMap (AdeleBaseChange.below ℚ w) w (((a : A ℚ) * iota L).2 (AdeleBaseChange.below ℚ w)) = _
  rw [h, map_mul, map_inv₀, map_natCast, map_natCast]

theorem UpperTheory.unipotent_natDiv_mem_maximalCompact_of_not_badPrime :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (L a : ℕ) (w : H.P E), ¬ Bad L (w.under (𝓞 ℚ)) → Valued.v (H.cp w (rt D.θ)) ≤ 1 → H.KAt w (nu D ((a : A ℚ) * iota L)) := by
  intro E _ _ D L a w hL hθ
  have hL1 := val_nat_one w L (not_mem_of_bad w L hL)
  have hz : Valued.v (H.cp w (D.mkE 0 ((a : A ℚ) * iota L))) ≤ 1 := by
    rw [Dat.mkE, map_zero, zero_add, map_mul, map_mul, completion_adele_natural, map_mul, map_inv₀, hL1, inv_one, mul_one]
    calc _ ≤ (1 : _) * 1 := mul_le_mul' (val_nat_le w a) hθ
      _ = 1 := mul_one 1
  show Matrix.GeneralLinearGroup.map (H.cp w) (gl (nU (D.mkE 0 ((a : A ℚ) * iota L)))) ∈ GlobalTheory.LFun.KGL w 2
  rw [map_gl_nU]
  exact nL_memK hz
end

