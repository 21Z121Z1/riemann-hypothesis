import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0383
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0388
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0384
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0386
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0381
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0389
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScaling
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0385
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ResPlaneSmulEqZero
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsRootOfIsAlgClosed
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0382

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFixedCongrAxLemmaOddPrime
section
open Polynomial

namespace GlobalTheory.AxSen

section Step

variable {K : Type} [Field K] {A : ValuationSubring K} {ϖ : K}

theorem ge_coeff_prod (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) {q : ℚ} (s : Multiset K) (hs : ∀ d ∈ s, Ge A ϖ d q) (k : ℕ) :
    Ge A ϖ ((s.map fun d => X + C d).prod.coeff k) (((s.card : ℚ) - k) * q) := by
  induction s using Multiset.induction_on generalizing k with
  | empty =>
    rcases k with _ | k
    · have := (ge_natCast_iff (A := A) h0 h1 (w := 1) (m := 0)).mpr ⟨1, A.one_mem, by simp⟩
      simpa using this
    · simpa [coeff_one] using ge_zero _
  | cons d s ih =>
    have hd := hs d (Multiset.mem_cons_self _ _)
    have ih' := ih fun x hx => hs x (Multiset.mem_cons_of_mem hx)
    rw [Multiset.map_cons, Multiset.prod_cons, add_mul, coeff_add, coeff_C_mul, Multiset.card_cons]
    refine Ge.add ?_ ((hd.mul h0 h1 (ih' k)).mono (le_of_eq (by push_cast; ring)))
    rcases k with _ | k
    · rw [coeff_X_mul_zero]; exact ge_zero _
    · rw [coeff_X_mul]; exact (ih' k).mono (le_of_eq (by push_cast; ring))

theorem exists_ge_of_prod (s : Multiset K) (hs : s ≠ 0) {q : ℚ} (h : Ge A ϖ s.prod (q * s.card)) :
    ∃ d ∈ s, Ge A ϖ d q := by
  classical
  obtain ⟨d, hd, hmin⟩ := Finset.exists_min_image s.toFinset A.valuation (Multiset.toFinset_nonempty.mpr hs)
  refine ⟨d, Multiset.mem_toFinset.mp hd, Ge.root (Multiset.card_pos.mpr hs) (h.of_le ?_)⟩
  rw [map_pow, map_multiset_prod, ← Multiset.card_map A.valuation s]
  refine Multiset.pow_card_le_prod fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
  exact hmin y (Multiset.mem_toFinset.mpr hy)

theorem exists_root_hasseDeriv [IsAlgClosed K] [CharZero K] (h0 : ϖ ≠ 0) (h1 : A.valuation ϖ ≤ 1) (T : Finset K) (α : K) {a : ℚ}
    (hT : ∀ t ∈ T, Ge A ϖ (α - t) a) {j e : ℕ} (hj : j < T.card)
    (hc : A.valuation ϖ ^ e ≤ A.valuation ((T.card.choose j : ℕ) : K)) :
    ∃ β ∈ (hasseDeriv j (∏ t ∈ T, (X - C t))).roots, Ge A ϖ (α - β) (a - e / ((T.card - j : ℕ) : ℚ)) := by
  set P : K[X] := ∏ t ∈ T, (X - C t) with hP
  have hPm : P.Monic := monic_prod_of_monic _ _ fun t _ => monic_X_sub_C t
  have hPd : P.natDegree = T.card := by simp [hP]
  set Q := hasseDeriv j P with hQ
  have hQd : Q.natDegree = T.card - j := by rw [hQ, natDegree_hasseDeriv, hPd]
  have hlc : Q.leadingCoeff = ((T.card.choose j : ℕ) : K) := by
    rw [leadingCoeff, hQd, hQ, hasseDeriv_coeff, Nat.sub_add_cancel hj.le, ← hPd, hPm.coeff_natDegree, mul_one]
  have hcard : Q.roots.card = Q.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hfac := C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hev : Q.eval α = ((T.val.map fun t => α - t).map fun d => X + C d).prod.coeff j := by
    rw [hQ, ← taylor_coeff, taylor_apply, hP, prod_comp, Multiset.map_map]
    congr 1
    refine Finset.prod_congr rfl fun t _ => ?_
    simp [add_sub_assoc]
  have hge := ge_coeff_prod h0 h1 (T.val.map fun t => α - t) (q := a) (by
    intro d hd
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.mp hd
    exact hT t ht) j
  rw [← hev, ← hfac, eval_mul, eval_C, hlc, eval_multiset_prod, Multiset.map_map] at hge
  have hdiv := hge.div h0 h1 hc
  have hpos : 0 < T.card - j := Nat.sub_pos_of_lt hj
  obtain ⟨d, hd, hd'⟩ := exists_ge_of_prod (A := A) (ϖ := ϖ) (q := a - e / ((T.card - j : ℕ) : ℚ))
    (Q.roots.map ((fun p => eval α p) ∘ fun a => X - C a)) (by
      rw [← Multiset.card_pos, Multiset.card_map, hcard, hQd]; exact hpos)
    (hdiv.mono (le_of_eq (by
      rw [Multiset.card_map, Multiset.card_map, hcard, hQd, Finset.card_val]
      have : ((T.card - j : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [← Nat.cast_sub hj.le]
      field_simp)))
  obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hd
  exact ⟨β, hβ, by simpa using hd'⟩

end Step

section Orbit

variable {K : Type} [Field K] [Algebra ℚ K] {A : ValuationSubring K}

def loss (p n : ℕ) : ℚ := (p : ℚ) / ((p : ℚ) - 1) ^ 2 * (1 - 1 / (p : ℚ) ^ Nat.log p n)

theorem loss_mono {p n n' : ℕ} (hp : p.Prime) (h : n ≤ n') : loss p n ≤ loss p n' := by
  have h1 : (1 : ℚ) ≤ p := by exact_mod_cast hp.one_le
  unfold loss
  gcongr

theorem loss_nonneg {p : ℕ} (hp : p.Prime) (n : ℕ) : 0 ≤ loss p n := by
  have := loss_mono hp (Nat.zero_le n)
  simpa [loss] using this

theorem loss_le_one {p : ℕ} (hp : 3 ≤ p) (n : ℕ) : loss p n ≤ 1 := by
  have h1 : (3 : ℚ) ≤ p := by exact_mod_cast hp
  have h2 : (p : ℚ) / ((p : ℚ) - 1) ^ 2 ≤ 1 := by
    rw [div_le_one (by nlinarith)]; nlinarith
  have h3 : (0 : ℚ) ≤ 1 / (p : ℚ) ^ Nat.log p n := by positivity
  have h4 : (0 : ℚ) ≤ (p : ℚ) / ((p : ℚ) - 1) ^ 2 := by positivity
  unfold loss
  nlinarith [mul_nonneg h3 h4]

theorem valuation_natCast_ge {p : ℕ} (hp : p.Prime) (h1 : A.valuation (p : K) < 1) {c e : ℕ} (hc : ¬ p ^ (e + 1) ∣ c) :
    A.valuation (p : K) ^ e ≤ A.valuation (c : K) := by
  have hc0 : c ≠ 0 := by rintro rfl; exact hc (dvd_zero _)
  obtain ⟨k, u, hu, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hc0 p hp.one_lt.ne'
  have hk : k ≤ e := by
    by_contra hk
    exact hc ((pow_dvd_pow p (by omega)).mul_right u)
  have hint : ∀ z : ℤ, A.valuation (z : K) ≤ 1 := fun z => (A.valuation_le_one_iff _).mpr (intCast_mem A z)
  have hu1 : 1 ≤ A.valuation (u : K) := by
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨s, t, hst⟩ : IsCoprime (p : ℤ) (u : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr hu)
    have e1 : (s : K) * p + t * u = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → K) hst
    have : A.valuation ((s : K) * p + t * u) < 1 := by
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint s)) h1
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint t)) hlt
    rw [e1, map_one] at this
    exact lt_irrefl _ this
  rw [Nat.cast_mul, Nat.cast_pow, map_mul, map_pow]
  exact (pow_le_pow_right_of_le_one' h1.le hk).trans (le_mul_of_one_le_right' hu1)

theorem exists_fixed [IsAlgClosed K] {p : ℕ} (hp : p.Prime) (h1 : A.valuation (p : K) < 1) (H : Subgroup (K ≃ₐ[ℚ] K))
    (hH : ∀ h ∈ H, ∀ x ∈ A, h x ∈ A) (n : ℕ) :
    ∀ (α : K) (a : ℚ) (S : Finset K), S.card ≤ n → (∀ h ∈ H, h α ∈ S) → (∀ h ∈ H, Ge A (p : K) (h α - α) a) →
      ∃ y, (∀ h ∈ H, h y = y) ∧ Ge A (p : K) (α - y) (a - loss p n) := by
  classical
  haveI : CharZero K := algebraRat.charZero K
  have h0 : (p : K) ≠ 0 := by exact_mod_cast hp.ne_zero
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro α a S hS hαS hα
  set T := S.filter fun t => ∃ h ∈ H, h α = t with hT
  have hmem : ∀ t, t ∈ T ↔ ∃ h ∈ H, h α = t := fun t => by
    rw [hT, Finset.mem_filter]
    exact ⟨fun h => h.2, fun ⟨h, hh, e⟩ => ⟨e ▸ hαS h hh, h, hh, e⟩⟩
  have hTn : T.card ≤ n := (Finset.card_filter_le _ _).trans hS
  by_cases h2 : 2 ≤ T.card
  swap
  · refine ⟨α, fun h hh => ?_, by simpa using ge_zero _⟩
    exact Finset.card_le_one.mp (by omega : T.card ≤ 1) _ ((hmem _).mpr ⟨h, hh, rfl⟩) _ ((hmem _).mpr ⟨1, H.one_mem, rfl⟩)
  obtain ⟨j, e, hj0, hj, hdvd, hloss⟩ := GlobalTheory.T.exists_choose_small_padicVal_ax_induction p hp T.card h2
  change _ + loss p _ ≤ loss p _ at hloss
  obtain ⟨β, hβ, hαβ⟩ := exists_root_hasseDeriv h0 h1.le T α (a := a) (fun t ht => by
    obtain ⟨h, hh, rfl⟩ := (hmem t).mp ht
    exact (hα h hh).symm) hj (valuation_natCast_ge hp h1 hdvd)
  set P : K[X] := ∏ t ∈ T, (X - C t) with hP
  have hPd : P.natDegree = T.card := by simp [hP]
  have hQd : (hasseDeriv j P).natDegree = T.card - j := by rw [natDegree_hasseDeriv, hPd]
  have hPmap : ∀ h ∈ H, P.map (h : K →+* K) = P := by
    intro h hh
    rw [hP, Polynomial.map_prod]
    refine Finset.prod_bij (fun t _ => h t) (fun t ht => ?_) (fun t _ t' _ e => h.injective e) (fun t ht => ?_) (fun t _ => by simp)
    · obtain ⟨g, hg, rfl⟩ := (hmem t).mp ht
      exact (hmem _).mpr ⟨h * g, H.mul_mem hh hg, rfl⟩
    · obtain ⟨g, hg, rfl⟩ := (hmem t).mp ht
      exact ⟨(h⁻¹ * g) α, (hmem _).mpr ⟨_, H.mul_mem (H.inv_mem hh) hg, rfl⟩, by
        rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]⟩
  have hQmap : ∀ h ∈ H, (hasseDeriv j P).map (h : K →+* K) = hasseDeriv j P := by
    intro h hh
    ext k
    rw [coeff_map, hasseDeriv_coeff, map_mul, map_natCast, ← coeff_map, hPmap h hh]
  have he : (0 : ℚ) ≤ e / ((T.card - j : ℕ) : ℚ) := by positivity
  obtain ⟨y, hy, hβy⟩ := ih (T.card - j) (by omega) β (a - e / ((T.card - j : ℕ) : ℚ)) (hasseDeriv j P).roots.toFinset
    ((Multiset.toFinset_card_le _).trans ((card_roots' _).trans hQd.le)) (fun h hh => by
      rw [Multiset.mem_toFinset, mem_roots'] at *
      refine ⟨hβ.1, ?_⟩
      rw [← hQmap h hh]
      exact hβ.2.map) (fun h hh => by
      have k1 := hαβ.symm.map h0 (h : K →+* K) (hH h hh) (map_natCast _ p)
      rw [map_sub] at k1
      exact Ge.trans k1 (((hα h hh).mono (by linarith)).trans hαβ))
  have hm := loss_mono hp hTn
  have hnn := loss_nonneg hp (T.card - j)
  exact ⟨y, hy, (hαβ.mono (by linarith)).trans (hβy.mono (by linarith))⟩

end Orbit

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Ord2 in

theorem exists_fixed_congr (l : ℕ) [Fact l.Prime] (hl : l ≠ 2) (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω]
    (A : ValuationSubring Ω) (hA : OverL l A) (H : Subgroup (G ℚ Ω)) (hH : H ≤ Dec (F := ℚ) A) (m : ℕ) (x : Ω) (hx : x ∈ A)
    (hcg : ∀ h ∈ H, GlobalTheory.Glue.CgA A l (m + 1) (h x) x) :
    ∃ y ∈ A, (∀ h ∈ H, h y = y) ∧ GlobalTheory.Glue.CgA A l m x y := by
  classical
  have hp : l.Prime := Fact.out
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have h0 : (l : Ω) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨v, hv, hlv⟩ := hA
  have h1 : A.valuation (l : Ω) < 1 := by simpa using (hv _).mpr hlv
  have hint : IsIntegral ℚ x := (IsAlgClosure.isAlgebraic.isAlgebraic x).isIntegral
  have h3 : 3 ≤ l := by have := hp.two_le; omega
  obtain ⟨y, hy, hxy⟩ := exists_fixed hp h1 H (fun h hh z hz => (apply_mem_iff_of_mem_Dec (hH hh) z).mpr hz) _ x ((m + 1 : ℕ) : ℚ)
    ((minpoly ℚ x).aroots Ω).toFinset le_rfl (fun h _ => by
      rw [Multiset.mem_toFinset, mem_aroots]
      refine ⟨minpoly.ne_zero hint, ?_⟩
      rw [aeval_algHom_apply, minpoly.aeval, map_zero])
    (fun h hh => (ge_natCast_iff h0 h1.le).mpr (hcg h hh))
  have hm : Ge A (l : Ω) (x - y) (m : ℚ) := hxy.mono (by
    have := loss_le_one h3 ((minpoly ℚ x).aroots Ω).toFinset.card
    push_cast; linarith)
  obtain ⟨z, hz, e⟩ := (ge_natCast_iff h0 h1.le).mp hm
  refine ⟨y, ?_, hy, z, hz, e⟩
  have : y = x - (l : Ω) ^ m * z := by rw [← e]; ring
  rw [this]
  exact A.sub_mem hx (A.mul_mem _ _ (A.pow_mem (natCast_mem A l) m) hz)

end GlobalTheory.AxSen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNf
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.NfEx

theorem up2 {k : Type} [Field k] (X Y Z : Matrix (Fin 2) (Fin 2) k) (hX : X 1 0 = 0) (hY : Y 1 0 = 0) (hZ : Z 1 0 = 0) :
    (X * Y * Z) 1 0 = 0 ∧ (X * Y * Z) 0 0 = X 0 0 * Y 0 0 * Z 0 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_two, hX, hY, hZ]

theorem inv_up {k : Type} [Field k] (B : GL (Fin 2) k) (hB : (B : Matrix (Fin 2) (Fin 2) k) 1 0 = 0) :
    ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 ∧
    (B : Matrix (Fin 2) (Fin 2) k) 0 0 * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 0 0 = 1 := by
  have key : ∀ i j, ∑ x, (B : Matrix (Fin 2) (Fin 2) k) i x * ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) x j =
      (1 : Matrix (Fin 2) (Fin 2) k) i j := fun i j => by
    rw [← Matrix.mul_apply, B.mul_inv]
  have e10 := key 1 0
  have e11 := key 1 1
  have e00 := key 0 0
  rw [Fin.sum_univ_two, hB, zero_mul, zero_add] at e10 e11
  rw [Fin.sum_univ_two] at e00
  rw [Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at e10
  rw [Matrix.one_apply_eq] at e11 e00
  have hN : ((B⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) 1 0 = 0 := by
    rcases mul_eq_zero.1 e10 with h | h
    · rw [h, zero_mul] at e11
      exact absurd e11 zero_ne_one
    · exact h
  refine ⟨hN, ?_⟩
  rw [hN, mul_zero, add_zero] at e00
  exact e00

theorem exists_nf : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (W : R2 Ω l), l ≠ 2 → 1 ≤ e → admitted ι e W → (∀ (A : ValuationSubring Ω) (κ : Fin 2 → ↥(Dec (F := ℚ) A) →* (Qbar l)ˣ), OverL l A → IsFlagOn W (Dec (F := ℚ) A) κ → ∃ s : ↥(Dec (F := ℚ) A), κ 0 s ≠ cycBar ℚ Ω l s) → ∃ (S : Finset Pl) (A : ValuationSubring Ω) (W' : R2 Ω l), RepIso W W' ∧ Nf e S A W' := by
  intro l _ Ω _ _ _ ι e W hl he hW hne
  obtain ⟨A, χ, κ, hA, hχ, hfl, -, hIne⟩ := hW.flag
  obtain ⟨g, hg⟩ := hfl
  obtain ⟨M, hM, hMa⟩ := hW.away
  obtain ⟨S, hSa, hSu⟩ := GlobalTheory.T.unramified_of_levelAway_inertia_characters l Ω W M hM hMa
  let r : G ℚ Ω →* GL (Fin 2) (Qbar l) := (MulAut.conj g).toMonoidHom.comp W
  have hrc : Continuous r := by
    show Continuous fun s => g * W s * g⁻¹
    exact (continuous_const.mul hW.cont).mul continuous_const
  obtain ⟨E, hE, hEm⟩ := GlobalTheory.CompactRepField.exists_finiteDimensional_entries_mem l (G ℚ Ω) 2 r
    (fun i j => ((Units.continuous_val.comp hrc).matrix_elem i j))
  obtain ⟨B, hB10, hBint⟩ := GlobalTheory.T.exists_upperTriangular_conj_integral_compact l (G ℚ Ω) E r hE hrc hEm
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_coefficientRing_finiteExtension_padic l E hE
  let h : GL (Fin 2) (Qbar l) := B * g
  let W' : R2 Ω l := (MulAut.conj h).toMonoidHom.comp W
  have hW' : ∀ s, W' s = B * r s * B⁻¹ := fun s => by
    show h * W s * h⁻¹ = B * (g * W s * g⁻¹) * B⁻¹
    simp only [h, mul_inv_rev]; group
  have hiso : RepIso W W' := ⟨h, fun s => rfl⟩
  have hdt : dt W' = dt W := by
    ext s
    rw [GlobalTheory.Ord2.TwDet.dt_coe, GlobalTheory.Ord2.TwDet.dt_conj W h s]
    rfl
  have hker : ∀ s, W' s = 1 ↔ W s = 1 := fun s => by
    show h * W s * h⁻¹ = 1 ↔ W s = 1
    constructor
    · intro hh; rw [mul_inv_eq_one, mul_eq_left] at hh; exact hh
    · intro hh; rw [hh]; simp
  have hinv := inv_up B hB10
  have hup : ∀ (s : G ℚ Ω) (hs : s ∈ Dec (F := ℚ) A), mat W' s 1 0 = 0 ∧ mat W' s 0 0 = (κ 0 ⟨s, hs⟩ : Qbar l) := by
    intro s hs
    have h1 := (hg ⟨s, hs⟩).1 1 0 (by decide)
    have h2 := (hg ⟨s, hs⟩).2 0
    have := up2 (B : Matrix (Fin 2) (Fin 2) (Qbar l)) ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l))
      ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) hB10 h1 hinv.1
    have e1 : mat W' s = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) := by
      simp only [mat, hW', Units.val_mul]
    refine ⟨by rw [e1]; exact this.1, ?_⟩
    rw [e1, this.2, ← h2]
    change _ = ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0
    calc _ = (B : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((B⁻¹ : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 * ((r s : GL (Fin 2) (Qbar l)) : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 := by ring
      _ = _ := by rw [hinv.2, one_mul]
  refine ⟨S, A, W', hiso, ?_⟩
  refine
    { l_odd := hl
      e_pos := he
      cont := ?_
      int := ⟨c, fun s i j => (hc _).2 ⟨?_, ?_⟩⟩
      above := hSa
      unr := ?_
      det2 := by rw [hdt]; exact hW.det2
      odd := by rw [hdt]; exact hW.odd
      irr := GlobalTheory.T.irreducible_restriction_of_iso Ω l W W' hiso hW.irr
      atL := hA
      upper := fun s hs => (hup s hs).1
      wt := ?_
      ne := ?_ }
  · show Continuous fun s => h * W s * h⁻¹
    exact (continuous_const.mul hW.cont).mul continuous_const
  · have := (hBint s i j).1; simpa only [mat, hW'] using this
  · have := (hBint s i j).2; simpa only [mat, hW'] using this
  · intro w hw B' hB' s hs
    exact (hker s).2 (hSu w hw B' hB' hs)
  · refine ⟨l - 1, ?_, fun s hs => ?_⟩
    · have := (Fact.out : l.Prime).two_le; omega
    · have hd : s ∈ Dec (F := ℚ) A := Ine_le_Dec A hs
      rw [(hup s hd).2, (hIne ⟨s, hd⟩ hs).1]
      have hχ1 := GlobalTheory.T.character_pow_pred_eq_one_of_killsPrimeRoots Ω l _ χ s hχ
      simp only [Units.val_mul, Units.val_zpow_eq_zpow_val, zpow_natCast, mul_pow, eps]
      rw [← Units.val_pow_eq_pow_val (χ s), hχ1, Units.val_one, mul_one, Units.val_pow_eq_pow_val, ← pow_mul]
  · obtain ⟨s, hs⟩ := hne A κ hA ⟨g, hg⟩
    refine ⟨s, s.2, ?_⟩
    rw [(hup s s.2).2]
    intro hh
    exact hs (Units.ext hh)

end GlobalTheory.NfEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBActDiagNatOneCommStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galB_act_diagNatOne_comm : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → ∀ (l : ℕ) [Fact l.Prime] (q : ℕ), 0 < q → ∀ (s : Ω ≃ₐ[ℚ] Ω) (b : X.Fn l), X.galB l s (X.act l !![(q : ℤ), 0; 0, 1] b) = X.act l !![(q : ℤ), 0; 0, 1] (X.galB l s b) := by
  first | exact @GlobalTheory.KZ.Tower.galB_act_diag | exact GlobalTheory.KZ.Tower.galB_act_diag | (intros; apply GlobalTheory.KZ.Tower.galB_act_diag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisActionUpperTriangularHeckeReindexOnBStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisAction_upperTriangular_hecke_reindex_on_B : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω) (q : ℕ) (e : ℤ), 0 < q → (∀ ζ : Ω, IsPrimitiveRoot ζ q → s ζ = ζ ^ e) → ∀ (j : ℤ), ∀ b ∈ X.B N l w, X.galB l s (X.act l !![1, j; 0, (q : ℤ)] b) = X.act l !![1, j * e; 0, (q : ℤ)] (X.galB l s b) := by
  first | exact @GlobalTheory.KZ.GalUpper.galB_act_upper | exact GlobalTheory.KZ.GalUpper.galB_act_upper | (intros; apply GlobalTheory.KZ.GalUpper.galB_act_upper <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCocycleIntegralAfterScalingStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_cocycle_integral_after_scaling : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (S : Finset Pl) (W : R2 Ω l) (c : Coef l) (z : G ℚ Ω → Fin 2 → Qbar l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → (∀ w, w ∉ S → ∀ B : ValuationSubring Ω, IsPlaceOver B w → Ine (F := ℚ) B ≤ W.ker) → z ∈ Z1 (Loc.colRep W) → Unr W z → ∀ A : ValuationSubring Ω, ∃ (c' : Coef l) (k : ℕ), c.O ≤ c'.O ∧ (∀ s i, ((l : ℕ) : Qbar l) ^ k * z s i ∈ c'.O) ∧ (∀ q : Pl, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∀ B : ValuationSubring Ω, IsPlaceOver B q → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c'.O) ∧ ∀ s ∈ Ine (F := ℚ) B, ((l : ℕ) : Qbar l) ^ k • z s = mat W s *ᵥ x - x) ∧ (Triv W A z → ∃ x : Fin 2 → Qbar l, (∀ i, x i ∈ c'.O) ∧ ∀ s ∈ Dec (F := ℚ) A, ((l : ℕ) : Qbar l) ^ k • z s = mat W s *ᵥ x - x) ∧ (Gr W A z → ∃ x ∈ c'.O, ∀ s ∈ Dec (F := ℚ) A, ((l : ℕ) : Qbar l) ^ k * z s 1 = mat W s 1 1 * x - x) := by
  first | exact @GlobalTheory.CocInt.integral_after_scaling | exact GlobalTheory.CocInt.integral_after_scaling | (intros; apply GlobalTheory.CocInt.integral_after_scaling <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisCommutesHeckeActionStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galois_commutes_hecke_action : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (N l w : ℕ) [Fact l.Prime], 1 ≤ N → ∀ b ∈ X.BSet N l w, ∀ δ ∈ CongruenceSubgroup.Gamma0 N ⊓ CongruenceSubgroup.Gamma0 l, ∀ s : Ω ≃ₐ[ℚ] Ω, X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) (X.galB l s b) = X.galB l s (X.act l (δ : Matrix (Fin 2) (Fin 2) ℤ) b) := by
  first | exact @GlobalTheory.KZ.GamComm.act_galB_comm | exact GlobalTheory.KZ.GamComm.act_galB_comm | (intros; apply GlobalTheory.KZ.GamComm.act_galB_comm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisHomZlLipschitzOfKerLeLinearGroupStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisHom_zl_lipschitz_of_ker_le_linearGroup : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] (r : Γ →* GL (Fin 2) (Qbar l)) (lam : Γ →* Multiplicative ℤ_[l]), Continuous r → (∀ g i j, (r g : Matrix (Fin 2) (Fin 2) (Qbar l)) i j ∈ c.O) → Continuous lam → r.ker ≤ lam.ker → ∃ C : ℝ, ∀ (m : ℕ) (g : Γ), (∀ i j, ‖((r g : Matrix (Fin 2) (Fin 2) (Qbar l)) - 1) i j‖ ≤ ‖((l : ℕ) : Qbar l) ^ m‖) → ‖(lam g).toAdd‖ ≤ C * ‖((l : ℕ) : Qbar l) ^ m‖ := by
  first | exact @GlobalTheory.Ord2.hom_lipschitz_of_ker_le | exact GlobalTheory.Ord2.hom_lipschitz_of_ker_le | (intros; apply GlobalTheory.Ord2.hom_lipschitz_of_ker_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisRepRankTwoTateDualExistsNoEigenvalueOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.Ord2

theorem galoisRepRankTwoTateDual_exists_no_eigenvalue_one_alt : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∃ g, (mat (dual1 W) g - 1).det ≠ 0 := by
  intro l _ Ω _ _ _ e S A W h
  obtain ⟨φ, hφ, hd⟩ := GlobalTheory.T.exists_commutator_det_nonzero l Ω e S A W h
  have hφ' : φ ∈ H0g W := (Subgroup.commutator_le.2 (fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))) hφ
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hφ'
  rw [MonoidHom.mem_ker] at h1 h2
  have hχ : (cycBar ℚ Ω l * (dt W)⁻¹) φ = 1 := by
    simp [h1, h2]
  refine ⟨φ, ?_⟩
  have : mat (dual1 W) φ = mat W φ := by
    unfold dual1
    generalize (cycBar ℚ Ω l * (dt W)⁻¹) = χ at hχ
    simp [mat, tw, hχ]
  rw [this]; exact hd

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaCocycleEqZeroOfVanishWildTameGeneratorStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA GlobalTheory.InertCoh
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaCocycle_eq_zero_of_vanish_wild_tameGenerator : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (B : ValuationSubring Ω) (γ : G ℚ Ω), Formalism.BasicNotions.TameGenAt B γ → ∀ z : G ℚ Ω → Fin 2 → Qbar l, (∀ i, Continuous fun s => z s i) → (∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, z (s * t) = z s + mat W s *ᵥ z t) → (∀ σ : G ℚ Ω, (∀ y : Ω, y ≠ 0 → B.valuation (σ y / y - 1) < 1) → z σ = 0) → z γ = 0 → ∀ s ∈ Ine (F := ℚ) B, z s = 0 := by
  first | exact @GlobalTheory.CocWildTame.eq_zero_on_Ine | exact GlobalTheory.CocWildTame.eq_zero_on_Ine | (intros; apply GlobalTheory.CocWildTame.eq_zero_on_Ine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralGaloisRepLocallyConstantModPrimePowStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGaloisRep_locallyConstant_modPrimePow : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (W : R2 Ω l), Continuous W → (∀ s i j, mat W s i j ∈ c.O) → ∀ (n : ℕ) (s : G ℚ Ω), ∀ᶠ t in nhds s, ∀ i j, ∃ o ∈ c.O, mat W t i j - mat W s i j = (l : Qbar l) ^ n * o := by
  first | exact @GlobalTheory.Ord2.locConst_mod_pow | exact GlobalTheory.Ord2.locConst_mod_pow | (intros; apply GlobalTheory.Ord2.locConst_mod_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspFunctionalValueModPrimePowDiamondIndependeStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCuspFunctionalValueModPrimePow_diamond_independent : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime] (n w d : ℕ) (b : X.Fn l), b ∈ X.B N l w → ∀ s : SL(2, ℤ), IsDiam N l d s → ∀ φ : HahnSeries ℚ Ω,
  IsThB X A N l n (X.act l (s : Matrix (Fin 2) (Fin 2) ℤ) b) φ ↔ IsThB X A N l n (X.act l (sgD N l d : Matrix (Fin 2) (Fin 2) ℤ) b) φ := by
  first | exact @GlobalTheory.KZ.isThB_act_isDiam_iff | exact GlobalTheory.KZ.isThB_act_isDiam_iff | (intros; apply GlobalTheory.KZ.isThB_act_isDiam_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LimitOfApproximateCocyclesStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_of_approximate_cocycles : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l), (∀ s i j, mat W s i j ∈ c.O) → ∀ (a : ℕ → G ℚ Ω → Fin 2 → Qbar l) (z : G ℚ Ω → Fin 2 → Qbar l), (∀ n s t, Cv n (a n (s * t)) (a n s + mat W s *ᵥ a n t)) → (∀ n s, ∀ᶠ t in nhds s, Cv n (a n t) (a n s)) → (∀ n s, Cv n (z s) (a n s)) → z ∈ Z1 (Loc.colRep W) := by
  first | exact @GlobalTheory.Ord2.limit_cocycle_mem_cocycles | exact GlobalTheory.Ord2.limit_cocycle_mem_cocycles | (intros; apply GlobalTheory.Ord2.limit_cocycle_mem_cocycles <;> assumption)
end

