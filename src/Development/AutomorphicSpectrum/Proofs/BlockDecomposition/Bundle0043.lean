import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0024
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.WedgeSub
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0020

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MonomialCoefficientComparison
section
open Finset GlobalTheory.CompanionTheory.CoefId

namespace GlobalTheory.CompanionTheory.CoefId

theorem unitCircle_infinite : {z : ℂ | ‖z‖ = 1}.Infinite := by
  have hinj : Function.Injective (fun k : ℕ => ((1 + (k : ℂ) * Complex.I) / (1 - (k : ℂ) * Complex.I))) := by
    intro s t hst
    have h1 : ∀ k : ℕ, (1 - (k : ℂ) * Complex.I) ≠ 0 := by
      intro k h0
      have := congrArg Complex.re h0
      simp at this
    have h2 := (div_eq_div_iff (h1 s) (h1 t)).mp hst
    have h3 := congrArg Complex.im h2
    simp at h3
    have h4 : (s : ℝ) = t := by linarith
    exact_mod_cast h4
  refine Set.infinite_of_injective_forall_mem hinj fun k => ?_
  have h5 : ‖(1 + (k : ℂ) * Complex.I)‖ = ‖(1 - (k : ℂ) * Complex.I)‖ := by
    rw [← Complex.norm_conj (1 + (k : ℂ) * Complex.I)]
    simp [sub_eq_add_neg]
  have h6 : ‖(1 - (k : ℂ) * Complex.I)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    intro h0
    have := congrArg Complex.re h0
    simp at this
  simp only [Set.mem_ofPred_eq, norm_div, h5]
  exact div_self h6

theorem poly_zero_of_torus {n : ℕ} (p : MvPolynomial (Fin n) ℂ)
    (h : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      MvPolynomial.eval z p = 0) : p = 0 := by
  classical
  set D : MvPolynomial (Fin n) ℂ :=
    ∏ q ∈ prs n, (MvPolynomial.X q.1 ^ 2 - MvPolynomial.X q.2 ^ 2) with hD
  have hD0 : D ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun q hq => ?_
    have hlt : q.1 < q.2 := (mem_filter.mp hq).2
    intro h0
    have h1 : (MvPolynomial.X q.1 ^ 2 : MvPolynomial (Fin n) ℂ) = MvPolynomial.X q.2 ^ 2 :=
      sub_eq_zero.mp h0
    have := congrArg (MvPolynomial.eval (fun a => if a = q.1 then (1 : ℂ) else 0)) h1
    simp [hlt.ne'] at this
  have hz : p * D = 0 := by
    apply MvPolynomial.funext_set (fun _ => {z : ℂ | ‖z‖ = 1}) (fun _ => unitCircle_infinite)
    intro x hx
    have hx' : ∀ a, ‖x a‖ = 1 := fun a => hx a (Set.mem_univ a)
    rw [map_mul, map_zero]
    by_cases hi : Function.Injective (fun a => x a ^ 2)
    · rw [h x hx' hi, zero_mul]
    · obtain ⟨a, b, hab, hne⟩ : ∃ a b, x a ^ 2 = x b ^ 2 ∧ a ≠ b := by
        simpa [Function.Injective] using hi
      have : MvPolynomial.eval x D = 0 := by
        rw [hD, map_prod]
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · exact Finset.prod_eq_zero (i := (a, b)) (by simp [prs, hlt]) (by simp [hab])
        · exact Finset.prod_eq_zero (i := (b, a)) (by simp [prs, hlt]) (by simp [hab])
      rw [this, mul_zero]
  exact (mul_eq_zero.mp hz).resolve_right hD0

theorem coeff_zero_of_torus {n : ℕ} (S : Finset (Fin n → ℤ)) (h : (Fin n → ℤ) → ℂ)
    (H : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ m ∈ S, h m * mon m z = 0) : ∀ m ∈ S, h m = 0 := by
  classical
  set N : ℕ := ∑ m ∈ S, ∑ a, (m a).natAbs with hNdef
  have hN : ∀ m ∈ S, ∀ a, 0 ≤ m a + (N : ℤ) := by
    intro m hm a
    have h1 : (m a).natAbs ≤ ∑ a, (m a).natAbs :=
      Finset.single_le_sum (f := fun a => (m a).natAbs) (fun _ _ => Nat.zero_le _) (mem_univ a)
    have h2 : ∑ a, (m a).natAbs ≤ N :=
      Finset.single_le_sum (f := fun m : Fin n → ℤ => ∑ a, (m a).natAbs)
        (fun _ _ => Nat.zero_le _) hm
    have h3 : ((m a).natAbs : ℤ) ≤ N := by exact_mod_cast h1.trans h2
    have h4 : -((m a).natAbs : ℤ) ≤ m a := by
      have := abs_nonneg (m a)
      rw [Int.natCast_natAbs]
      exact neg_abs_le (m a)
    linarith
  let s : (Fin n → ℤ) → (Fin n →₀ ℕ) := fun m =>
    Finsupp.equivFunOnFinite.symm (fun a => (m a + (N : ℤ)).toNat)
  have hs : ∀ m ∈ S, ∀ a, ((s m a : ℕ) : ℤ) = m a + N := by
    intro m hm a
    simp only [s, Finsupp.equivFunOnFinite_symm_apply_apply]
    exact Int.toNat_of_nonneg (hN m hm a)
  have hinj : ∀ m ∈ S, ∀ m' ∈ S, s m = s m' → m = m' := by
    intro m hm m' hm' hss
    funext a
    have h1 := hs m hm a
    have h2 := hs m' hm' a
    rw [hss] at h1
    linarith
  have hp : (∑ m ∈ S, MvPolynomial.monomial (s m) (h m) : MvPolynomial (Fin n) ℂ) = 0 := by
    refine poly_zero_of_torus _ fun z hz hi => ?_
    have hz0 : ∀ a, z a ≠ 0 := by
      intro a h0
      have := hz a
      simp [h0] at this
    have hterm : ∀ m ∈ S, MvPolynomial.eval z (MvPolynomial.monomial (s m) (h m)) =
        (∏ a, z a ^ N) * (h m * mon m z) := by
      intro m hm
      rw [MvPolynomial.eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mon]
      have : ∀ a, z a ^ (s m a) = z a ^ N * z a ^ (m a) := by
        intro a
        rw [← zpow_natCast, hs m hm a, ← zpow_natCast, ← zpow_add₀ (hz0 a), add_comm]
      simp only [this, Finset.prod_mul_distrib]
      ring
    rw [map_sum, Finset.sum_congr rfl hterm, ← Finset.mul_sum, H z hz hi, mul_zero]
  intro m hm
  have h1 := congrArg (MvPolynomial.coeff (s m)) hp
  rw [MvPolynomial.coeff_sum, Finset.sum_eq_single m] at h1
  · simpa [MvPolynomial.coeff_monomial] using h1
  · intro b hb hne
    rw [MvPolynomial.coeff_monomial, if_neg fun e => hne (hinj b hb m hm e)]
  · exact fun h' => absurd hm h'

theorem laurent_indep_torus {n : ℕ} {ι κ : Type} (I : Finset ι) (J : Finset κ) (f : ι → ℂ)
    (g : κ → ℂ) (e : ι → Fin n → ℤ) (e' : κ → Fin n → ℤ)
    (H : ∀ z : Fin n → ℂ, (∀ a, ‖z a‖ = 1) → Function.Injective (fun a => z a ^ 2) →
      ∑ i ∈ I, f i * mon (e i) z = ∑ j ∈ J, g j * mon (e' j) z) (m : Fin n → ℤ) :
    ∑ i ∈ I.filter (fun i => e i = m), f i = ∑ j ∈ J.filter (fun j => e' j = m), g j := by
  classical
  set S : Finset (Fin n → ℤ) := insert m (I.image e ∪ J.image e') with hS
  set h : (Fin n → ℤ) → ℂ := fun m => ∑ i ∈ I.filter (fun i => e i = m), f i -
    ∑ j ∈ J.filter (fun j => e' j = m), g j with hh
  have hI : ∀ i ∈ I, e i ∈ S := fun i hi =>
    mem_insert_of_mem (mem_union_left _ (mem_image_of_mem e hi))
  have hJ : ∀ j ∈ J, e' j ∈ S := fun j hj =>
    mem_insert_of_mem (mem_union_right _ (mem_image_of_mem e' hj))
  have key := coeff_zero_of_torus S h (fun z hz hi => by
    have h1 : ∑ i ∈ I, f i * mon (e i) z =
        ∑ m ∈ S, (∑ i ∈ I.filter (fun i => e i = m), f i) * mon m z := by
      rw [← Finset.sum_fiberwise_of_maps_to hI]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [(mem_filter.mp hi).2]
    have h2 : ∑ j ∈ J, g j * mon (e' j) z =
        ∑ m ∈ S, (∑ j ∈ J.filter (fun j => e' j = m), g j) * mon m z := by
      rw [← Finset.sum_fiberwise_of_maps_to hJ]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(mem_filter.mp hj).2]
    simp only [hh, sub_mul, Finset.sum_sub_distrib]
    rw [← h1, ← h2, H z hz hi, sub_self]) m (mem_insert_self _ _)
  exact sub_eq_zero.mp key

end GlobalTheory.CompanionTheory.CoefId
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MulProdCongr
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.RootNear

theorem mul_prod_congr {B ι : Type} [CommRing B] (u : B) (x y : ι → B) (S : Finset ι)
    (h : ∀ j ∈ S, u * x j = u * y j) : u * ∏ j ∈ S, x j = u * ∏ j ∈ S, y j := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 : u * x a = u * y a := h a (Finset.mem_insert_self a s)
    have h2 : u * ∏ j ∈ s, x j = u * ∏ j ∈ s, y j :=
      ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    calc u * (x a * ∏ j ∈ s, x j) = (u * x a) * ∏ j ∈ s, x j := by ring
      _ = (u * y a) * ∏ j ∈ s, x j := by rw [h1]
      _ = y a * (u * ∏ j ∈ s, x j) := by ring
      _ = y a * (u * ∏ j ∈ s, y j) := by rw [h2]
      _ = u * (y a * ∏ j ∈ s, y j) := by ring

theorem exists_shift {B ι : Type} [CommRing B] (I : Ideal B) (c f : ι → B) (S : Finset ι)
    (hf : ∀ j ∈ S, IsIdempotentElem (f j)) (hc : ∀ j ∈ S, f j * c j ∈ I) :
    ∃ s ∈ I, (∏ j ∈ S, (1 - f j)) ∣ ∏ j ∈ S, (c j - s) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨0, I.zero_mem, by simp⟩
  | insert a s ha ih =>
    obtain ⟨t, htI, hdvd⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      (fun j hj => hc j (Finset.mem_insert_of_mem hj))
    have hfa : f a * f a = f a := hf a (Finset.mem_insert_self a s)
    have hca : f a * c a ∈ I := hc a (Finset.mem_insert_self a s)
    refine ⟨(1 - f a) * t + f a * c a, I.add_mem (I.mul_mem_left _ htI) hca, ?_⟩
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hcong : (1 - f a) * ∏ j ∈ s, (c j - ((1 - f a) * t + f a * c a)) =
        (1 - f a) * ∏ j ∈ s, (c j - t) :=
      mul_prod_congr (1 - f a) _ _ s (fun j _ => by linear_combination (c a - t) * hfa)
    have hfirst : c a - ((1 - f a) * t + f a * c a) = (1 - f a) * (c a - t) := by ring
    rw [hfirst, mul_comm (1 - f a) (c a - t), mul_assoc, hcong]
    exact Dvd.dvd.mul_left (mul_dvd_mul_left (1 - f a) hdvd) _

theorem root_near (B : Type) [CommRing B] (π : B) (hπ : π ∈ nonZeroDivisors B) (hV : VAL π)
    (d M : ℕ) (b : Fin d → B) (a : B) (hd : 0 < d)
    (hprod : ∏ j, (a - b j) ∈ Ideal.span {π ^ (d * M)}) :
    ∃ a₁ : B, a₁ - a ∈ Ideal.span {π ^ M} ∧ ∏ j, (a₁ - b j) = 0 := by
  classical
  have key : ∀ j : Fin d, ∃ e : B, IsIdempotentElem e ∧ e * (a - b j) ∈ Ideal.span {π ^ M} ∧
      (1 - e) * π ^ M ∈ Ideal.span {a - b j} := fun j =>
    hV (a - b j) (π ^ M) ⟨M, Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩
  choose e he1 he2 he3 using key
  have hee : ∀ j, e j * e j = e j := fun j => he1 j
  have hr : ∀ j, ∃ r : B, (1 - e j) * π ^ M = (a - b j) * r := fun j =>
    Ideal.mem_span_singleton.mp (he3 j)
  choose r hr using hr
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp hprod
  obtain ⟨j0, -⟩ : ∃ j : Fin d, True := ⟨⟨0, hd⟩, trivial⟩
  obtain ⟨E, hEdef⟩ : ∃ E : B, E = ∏ j, (1 - e j) := ⟨_, rfl⟩
  have hEE : E * E = E := by
    rw [hEdef, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun j _ => by linear_combination hee j)
  have hEj : ∀ j, E * (1 - e j) = E := by
    intro j
    have hsplit : (1 - e j) * ∏ i ∈ Finset.univ.erase j, (1 - e i) = E := by
      rw [hEdef]; exact Finset.mul_prod_erase _ (fun i => 1 - e i) (Finset.mem_univ j)
    rw [← hsplit]
    linear_combination (∏ i ∈ Finset.univ.erase j, (1 - e i)) * hee j
  have hT : ∀ j, (a - b j) * (E * r j) = E * π ^ M := by
    intro j
    calc (a - b j) * (E * r j) = E * ((a - b j) * r j) := by ring
      _ = E * ((1 - e j) * π ^ M) := by rw [← hr j]
      _ = (E * (1 - e j)) * π ^ M := by ring
      _ = E * π ^ M := by rw [hEj j]
  have hEpow : ∀ n : ℕ, E ^ (n + 1) = E := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, ih, hEE]
  have hEd : E ^ d = E := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', hEpow]
  have hmain : π ^ (d * M) * (q * ∏ j, (E * r j)) = π ^ (d * M) * E := by
    calc π ^ (d * M) * (q * ∏ j, (E * r j)) = (∏ j, (a - b j)) * ∏ j, (E * r j) := by
          rw [hq]; ring
      _ = ∏ j, ((a - b j) * (E * r j)) := Finset.prod_mul_distrib.symm
      _ = ∏ _j : Fin d, (E * π ^ M) := Finset.prod_congr rfl (fun j _ => hT j)
      _ = π ^ (d * M) * E := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow, hEd, ← pow_mul,
            mul_comm M d]
          ring
  have hpow : π ^ (d * M) ∈ nonZeroDivisors B := pow_mem hπ _
  have hET : E = q * ∏ j, (E * r j) := by
    have h0 : (q * ∏ j, (E * r j) - E) * π ^ (d * M) = 0 := by linear_combination hmain
    exact (sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hpow).2 _ h0)).symm
  have hEa : E * (a - b j0) ∈ Ideal.span {π ^ M} := by
    rw [Ideal.mem_span_singleton]
    have hsplit : (E * r j0) * ∏ i ∈ Finset.univ.erase j0, (E * r i) = ∏ i, (E * r i) :=
      Finset.mul_prod_erase _ (fun i => E * r i) (Finset.mem_univ j0)
    refine ⟨q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * E, ?_⟩
    calc E * (a - b j0) = q * (∏ i, (E * r i)) * (a - b j0) := by rw [← hET]
      _ = q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * ((a - b j0) * (E * r j0)) := by
          rw [← hsplit]; ring
      _ = π ^ M * (q * (∏ i ∈ Finset.univ.erase j0, (E * r i)) * E) := by rw [hT j0]; ring
  obtain ⟨s, hs, w, hw⟩ := exists_shift (Ideal.span {π ^ M}) (fun j => a - b j) e Finset.univ
    (fun j _ => he1 j) (fun j _ => he2 j)
  have hw' : ∏ j, (a - b j - s) = E * w := by rw [hEdef]; exact hw
  obtain ⟨a₁, ha₁⟩ : ∃ x : B, x = (1 - E) * (a - s) + E * b j0 := ⟨_, rfl⟩
  refine ⟨a₁, ?_, ?_⟩
  · have h1 : a₁ - a = (E - 1) * s - E * (a - b j0) := by rw [ha₁]; ring
    rw [h1]
    exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ hs) hEa
  · have hsplit2 : (a₁ - b j0) * ∏ i ∈ Finset.univ.erase j0, (a₁ - b i) = ∏ i, (a₁ - b i) :=
      Finset.mul_prod_erase _ (fun i => a₁ - b i) (Finset.mem_univ j0)
    have hE0 : E * ∏ i, (a₁ - b i) = 0 := by
      rw [← hsplit2]
      linear_combination E * (∏ i ∈ Finset.univ.erase j0, (a₁ - b i)) * ha₁ +
        (∏ i ∈ Finset.univ.erase j0, (a₁ - b i)) * (b j0 - (a - s)) * hEE
    have hcong : (1 - E) * ∏ i, (a₁ - b i) = (1 - E) * ∏ i, (a - b i - s) :=
      mul_prod_congr (1 - E) _ _ Finset.univ
        (fun j _ => by linear_combination (1 - E) * ha₁ + (a - s - b j0) * hEE)
    calc ∏ i, (a₁ - b i) = E * ∏ i, (a₁ - b i) + (1 - E) * ∏ i, (a₁ - b i) := by ring
      _ = 0 + (1 - E) * ∏ i, (a - b i - s) := by rw [hE0, hcong]
      _ = 0 := by rw [hw']; linear_combination (-w) * hEE

end GlobalTheory.CompanionTheory.RootNear
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicativityInfinitePlaces
section
noncomputable section

open Matrix PositivityTheory.Rg.BcB.D1
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.GramWedge

theorem star_dotProduct_self {α : Type} [Fintype α] (w : α → ℂ) :
    star w ⬝ᵥ w = ((∑ i, ‖w i‖ ^ 2 : ℝ) : ℂ) := by
  simp only [dotProduct, Pi.star_apply]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using Complex.conj_mul' (w i)

theorem norm_entry_le_sz {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : Matrix ι' ι ℂ) (a : ι') (b : ι) :
    ‖g a b‖ ≤ sz g :=
  le_ciSup (f := fun p : ι' × ι => ‖g p.1 p.2‖) (Set.finite_range _).bddAbove (a, b)

theorem sum_norm_mulVec_sq_le {ι ι' : Type} [Fintype ι] [Fintype ι'] (g : Matrix ι' ι ℂ) (v : ι → ℂ) :
    ∑ a, ‖(g *ᵥ v) a‖ ^ 2 ≤
      (Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := by
  have row : ∀ a, ‖(g *ᵥ v) a‖ ^ 2 ≤ (Fintype.card ι : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := by
    intro a
    have h1 : ‖(g *ᵥ v) a‖ ≤ sz g * ∑ b, ‖v b‖ := by
      rw [Finset.mul_sum]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_entry_le_sz g a b) (norm_nonneg _)
    have h2 : (∑ b, ‖v b‖) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ b, ‖v b‖ ^ 2 := by
      simpa using sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun b => ‖v b‖)
    calc ‖(g *ᵥ v) a‖ ^ 2 ≤ (sz g * ∑ b, ‖v b‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = sz g ^ 2 * (∑ b, ‖v b‖) ^ 2 := mul_pow _ _ _
      _ ≤ sz g ^ 2 * ((Fintype.card ι : ℝ) * ∑ b, ‖v b‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      _ = _ := by ring
  calc ∑ a, ‖(g *ᵥ v) a‖ ^ 2
      ≤ ∑ _a : ι', (Fintype.card ι : ℝ) * sz g ^ 2 * ∑ b, ‖v b‖ ^ 2 := Finset.sum_le_sum fun a _ => row a
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem posSemidef_smul_gram_sub {ι ι' κ : Type} [Fintype ι] [Fintype ι'] [Fintype κ] [DecidableEq κ]
    (g : Matrix ι' ι ℂ) (A : Matrix ι κ ℂ) :
    (((((Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 : ℝ) : ℂ) • (Aᴴ * A)) -
      (g * A)ᴴ * (g * A)).PosSemidef := by
  set c : ℝ := (Fintype.card ι * Fintype.card ι' : ℝ) * sz g ^ 2 with hc
  have hG : (Aᴴ * A).IsHermitian := isHermitian_conjTranspose_mul_self A
  have hH : ((g * A)ᴴ * (g * A)).IsHermitian := isHermitian_conjTranspose_mul_self _
  refine PosSemidef.of_dotProduct_mulVec_nonneg
    ((hG.smul (show star (c : ℂ) = c from Complex.conj_ofReal c)).sub hH) fun x => ?_
  have e : ∀ {α : Type} [Fintype α] (B : Matrix α κ ℂ),
      star x ⬝ᵥ ((Bᴴ * B) *ᵥ x) = star (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
    intro α _ B
    rw [← mulVec_mulVec, star_mulVec, dotProduct_mulVec]
  have e1 := e A
  have e2 : star x ⬝ᵥ (((g * A)ᴴ * (g * A)) *ᵥ x) = star (g *ᵥ (A *ᵥ x)) ⬝ᵥ (g *ᵥ (A *ᵥ x)) := by
    rw [e (g * A), mulVec_mulVec]
  rw [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul, e1, e2, star_dotProduct_self,
    star_dotProduct_self, smul_eq_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub]
  exact Complex.zero_le_real.2 (sub_nonneg.2 (sum_norm_mulVec_sq_le g (A *ᵥ x)))

theorem gram_mul_det {ι κ : Type} [Fintype ι] [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (s : Matrix κ κ ℂ) :
    ((A * s)ᴴ * (A * s)).det = ((‖s.det‖ ^ 2 : ℝ) : ℂ) * (Aᴴ * A).det := by
  have h : star s.det * s.det = ((‖s.det‖ ^ 2 : ℝ) : ℂ) := by
    simpa using Complex.conj_mul' s.det
  rw [conjTranspose_mul, show sᴴ * Aᴴ * (A * s) = sᴴ * (Aᴴ * A) * s by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc],
    det_mul, det_mul, det_conjTranspose, ← h]
  ring

theorem mulI_of_detMono : DetMono → MulI := by
  intro hm ι ι' κ _ _ _ _ A
  refine ⟨fun g => ?_, fun s => ?_, fun s => ?_⟩
  · have h := hm κ _ _ (posSemidef_conjTranspose_mul_self (g * A)) (posSemidef_smul_gram_sub g A)
    rw [det_smul, ← Complex.ofReal_pow, Complex.re_ofReal_mul] at h
    exact h
  · simp only [nI]
    rw [gram_mul_det, Complex.re_ofReal_mul, mul_comm]
  · have h := gram_mul_det (1 : Matrix κ κ ℂ) s
    simp only [Matrix.one_mul, conjTranspose_one, Matrix.mul_one, det_one, mul_one] at h
    simp only [nI]
    rw [h, Complex.ofReal_re]

end GlobalTheory.CompanionTheory.GramWedge

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NewtonPolygonSlopeExistence
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R

namespace GlobalTheory.CompanionTheory.NewtonSlope

theorem exists_dvd_all {S ι : Type} [CommRing S] (T : Finset ι) (hT : T.Nonempty) (r : ι → S)
    (hc : ∀ i ∈ T, ∀ j ∈ T, r i ∣ r j ∨ r j ∣ r i) :
    ∃ i₀ ∈ T, ∀ j ∈ T, r j ∣ r i₀ := by
  classical
  revert hT hc
  refine Finset.induction_on T ?_ ?_
  · intro hT
    exact absurd hT Finset.not_nonempty_empty
  · intro a s ha ih hT hc
    rcases s.eq_empty_or_nonempty with hs | hs
    · subst hs
      refine ⟨a, Finset.mem_insert_self a ∅, ?_⟩
      intro j hj
      rw [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · exact dvd_refl _
      · exact absurd hj (Finset.notMem_empty j)
    · obtain ⟨i₀, hi₀, hmax⟩ := ih hs (fun i hi j hj =>
        hc i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      rcases hc a (Finset.mem_insert_self a s) i₀ (Finset.mem_insert_of_mem hi₀) with h | h
      · refine ⟨i₀, Finset.mem_insert_of_mem hi₀, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact h
        · exact hmax j hj
      · refine ⟨a, Finset.mem_insert_self a s, ?_⟩
        intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact dvd_refl _
        · exact (hmax j hj).trans h

theorem dich_of_dvd {S : Type} [CommRing S] {ϖ : S} (hD : Dich ϖ) {a b : S} {M : ℕ}
    (h : a ∣ ϖ ^ M) : b ∣ a ∨ a ∣ b := by
  obtain ⟨k, hk⟩ := h
  refine hD a b ⟨M, ?_⟩
  rw [hk]
  exact Ideal.mul_mem_right k _ (Ideal.subset_span (by simp))

theorem first_slope : ∀ {S : Type} [CommRing S] (ϖ : S), Dich ϖ → Roots ϖ → ∀ (q : ℕ → S) (d M : ℕ),
    0 < d → q d = 1 → q 0 ∣ ϖ ^ M → ∃ c : S, (∀ i, 1 ≤ i → i ≤ d → q 0 ∣ q i * c ^ i) ∧
      ∃ i, 1 ≤ i ∧ i ≤ d ∧ q i * c ^ i ∣ q 0 := by
  intro S _ ϖ hD hR q d M hd hqd h0
  classical
  have hex : ∀ j : ℕ, ∃ s : S, (1 ≤ j → q j ∣ q 0 → ∃ u : Sˣ, q 0 = q j * (↑u * s ^ j)) := by
    intro j
    by_cases hj : 1 ≤ j ∧ q j ∣ q 0
    · obtain ⟨t, ht⟩ := hj.2
      have htd : t ∣ ϖ ^ M := (Dvd.intro_left (q j) ht.symm).trans h0
      obtain ⟨r, u, hru⟩ := hR t M j htd (by omega)
      exact ⟨r, fun _ _ => ⟨u, by rw [ht, hru]⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hj⟩
  choose s hs using hex
  set T := (Finset.Icc 1 d).filter (fun j => q j ∣ q 0) with hTdef
  have hmemT : ∀ j, j ∈ T ↔ (1 ≤ j ∧ j ≤ d) ∧ q j ∣ q 0 := by
    intro j
    rw [hTdef, Finset.mem_filter, Finset.mem_Icc]
  have hdT : d ∈ T := (hmemT d).mpr ⟨⟨hd, le_refl d⟩, by rw [hqd]; exact one_dvd _⟩
  have hsdvd : ∀ j ∈ T, s j ∣ ϖ ^ M := by
    intro j hj
    obtain ⟨⟨hj1, _⟩, hjq⟩ := (hmemT j).mp hj
    obtain ⟨u, hu⟩ := hs j hj1 hjq
    have h1 : s j ^ j ∣ q 0 := ⟨q j * ↑u, by rw [hu]; ring⟩
    exact ((dvd_pow_self (s j) (by omega)).trans h1).trans h0
  have hcomp : ∀ i ∈ T, ∀ j ∈ T, s i ∣ s j ∨ s j ∣ s i := by
    intro i hi j _
    exact (dich_of_dvd hD (b := s j) (hsdvd i hi)).symm
  obtain ⟨i₀, hi₀T, hmax⟩ := exists_dvd_all T ⟨d, hdT⟩ s hcomp
  obtain ⟨⟨hi₀1, hi₀d⟩, hi₀q⟩ := (hmemT i₀).mp hi₀T
  refine ⟨s i₀, ?_, i₀, hi₀1, hi₀d, ?_⟩
  · intro i hi1 hid
    rcases dich_of_dvd hD (b := q i) h0 with h | h
    · have hiT : i ∈ T := (hmemT i).mpr ⟨⟨hi1, hid⟩, h⟩
      obtain ⟨u, hu⟩ := hs i hi1 h
      have h2 : q 0 ∣ q i * s i ^ i := by
        rw [hu, mul_left_comm, Units.mul_left_dvd]
      obtain ⟨k, hk⟩ := hmax i hiT
      exact h2.trans ⟨k ^ i, by rw [hk, mul_pow]; ring⟩
    · exact dvd_mul_of_dvd_left h _
  · obtain ⟨u, hu⟩ := hs i₀ hi₀1 hi₀q
    exact ⟨↑u, by rw [hu]; ring⟩

end GlobalTheory.CompanionTheory.NewtonSlope
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneTmulMemRangeIff
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.CovCmp

theorem one_tmul_mem_range_iff {A : Type} [CommRing A] (B' : Type) [CommRing B'] [Algebra A B']
    {K₁ K₀ : Type} [AddCommGroup K₁] [Module A K₁] [AddCommGroup K₀] [Module A K₀]
    (d : K₁ →ₗ[A] K₀) (z : K₀) :
    ((1 : B') ⊗ₜ[A] z) ∈ LinearMap.range (d.lTensor B') ↔
      (1 : B') ⊗ₜ[A] ((LinearMap.range d).mkQ z) = 0 := by
  have hex := lTensor_exact B' (LinearMap.exact_map_mkQ_range d)
    (Submodule.mkQ_surjective (LinearMap.range d))
  have := hex ((1 : B') ⊗ₜ[A] z)
  rw [LinearMap.lTensor_tmul] at this
  exact this.symm

theorem cov_of_solv : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (r : ℕ → A), (∀ (m n : ℕ) (a : Fin m → Fin n → A) (c : Fin m → A), Solv B a c → ∃ (B₁ : Type) (_ : CommRing B₁) (_ : Algebra A B₁), Cov p r B₁ ∧ Solv B₁ a c) → Cov p r B := by
  intro p _ A _ B _ _ r h K₁ K₀ _ _ _ _ h₁ h₀ d hd z hz k
  have hB := (one_tmul_mem_range_iff B d z).mp hz
  obtain ⟨m, n, a, c, hs, hall⟩ := GlobalTheory.CompanionTheory.EqCrit.exists_system B ((LinearMap.range d).mkQ z) hB
  obtain ⟨B₁, i₁, i₂, hc, hs₁⟩ := h m n a c hs
  have h0 := hall B₁ hs₁
  exact hc K₁ K₀ h₁ h₀ d hd z ((one_tmul_mem_range_iff B₁ d z).mpr h0) k

end GlobalTheory.CompanionTheory.CovCmp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolynomialTimesGaussianBoundedStatement
section
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polynomial_times_gaussian_bounded : ∀ (ι : Type) [Fintype ι] (c : ℝ), 0 < c → ∀ N : ℕ, ∃ M : ℝ, ∀ y : ι → ℝ,
    (1 + ‖y‖) ^ N * Real.exp (-(c * ∑ i, y i ^ 2)) ≤ M := by
  first | exact @GlobalTheory.CompanionTheory.EisTube.polyGaussBdd | exact GlobalTheory.CompanionTheory.EisTube.polyGaussBdd | (intros; apply GlobalTheory.CompanionTheory.EisTube.polyGaussBdd <;> assumption)
end

