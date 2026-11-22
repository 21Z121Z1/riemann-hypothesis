import Formalism.GradedWeylDivisibility.Bundle0001
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0006
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCassemLemmas

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem lclosedeq_rowGen_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (f : MvPolynomial (Fin r × Fin n) R) :
    rowGen S a b (map φ f) = Polynomial.map (map φ) (rowGen R a b f) := by
  induction f using MvPolynomial.induction_on with
  | C c =>
    simp only [map_C, rowGen, aeval_C, Polynomial.algebraMap_apply, algebraMap_eq, Polynomial.map_C]
  | add p q hp hq => simp only [map_add, hp, hq, Polynomial.map_add]
  | mul_X p v hp =>
    simp only [map_mul, map_X, hp, Polynomial.map_mul]
    congr 1
    simp only [rowGen, aeval_X]
    split_ifs <;> simp [Polynomial.map_add, Polynomial.map_mul, map_X]

theorem lclosedeq_rowDiv_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin n) R) :
    rowDiv S a b k (map φ f) = map φ (rowDiv R a b k f) := by
  simp only [rowDiv, lclosedeq_rowGen_map, Polynomial.coeff_map]

theorem lclosedeq_applyWord_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (w : List (Fin r × Fin r × ℕ)) (f : MvPolynomial (Fin r × Fin n) R) :
    applyWord S w (map φ f) = map φ (applyWord R w f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons] at ih ⊢
    rw [ih, lclosedeq_rowDiv_map]

theorem lclosedeq_lpMinor_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (s : ℕ) (hr : s ≤ r) (hn : s ≤ n) :
    map φ (lpMinor R (r := r) (n := n) s hr hn) = lpMinor S s hr hn := by
  unfold lpMinor
  rw [RingHom.map_det]
  congr 1
  ext p q
  simp [RingHom.mapMatrix_apply, map_X]

theorem lclosedeq_hw_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) {r n : ℕ}
    (hn : n ≤ r) (ν : Fin n → ℕ) :
    map φ (hw R hn ν) = hw S hn ν := by
  simp only [hw, map_prod, map_pow, lclosedeq_lpMinor_map]

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaTallZero
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

private lemma isWH_coeff_one_polynomial {r n : ℕ} (δ : ℕ) :
    ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ))
      ((1 : Polynomial (MvPolynomial (Fin r × Fin n) ℚ)).coeff k) (0 + k * δ) := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs with hk
  · subst hk
    simpa using isWeightedHomogeneous_one (R := ℚ) (w := (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)))
  · exact fun d hd => (hd (coeff_zero d)).elim

private lemma isWH_coeff_mul_of_isWH_coeff {r n : ℕ} (δ : ℕ) (p q : Polynomial (MvPolynomial (Fin r × Fin n) ℚ)) (d e : ℕ)
    (hp : ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) (p.coeff k) (d + k * δ))
    (hq : ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) (q.coeff k) (e + k * δ)) :
    ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) ((p * q).coeff k) (d + e + k * δ) := by
  intro k
  rw [Polynomial.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
  have h := (hp x.1).mul (hq x.2)
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
  rw [← hx]
  convert h using 1
  ring

private lemma isWH_coeff_prod_of_isWH_coeff {r n : ℕ} (δ : ℕ) {ι : Type} (s : Finset ι)
    (p : ι → Polynomial (MvPolynomial (Fin r × Fin n) ℚ)) (d : ι → ℕ)
    (h : ∀ i ∈ s, ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) ((p i).coeff k) (d i + k * δ)) :
    ∀ k, IsWeightedHomogeneous (fun v : Fin r × Fin n => r - 1 - (v.1 : ℕ)) ((∏ i ∈ s, p i).coeff k) (∑ i ∈ s, d i + k * δ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isWH_coeff_one_polynomial (r := r) (n := n) δ
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact isWH_coeff_mul_of_isWH_coeff δ _ _ _ _ (h i (Finset.mem_insert_self i s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end Formalism.GradedWeylDivisibility
end
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.SMSAssembly
section
open MvPolynomial

namespace Formalism.GradedWeylDivisibility

open scoped MonomialOrder

theorem semistandard_module_assembly : SMSAssembly := by
  intro hCL hCS hSS hLI B _ _ r n ν
  apply le_antisymm
  · have key : ∀ d : (colLex r n).syn, ∀ f ∈ dualWeyl B r n ν,
        (colLex r n).toSyn ((colLex r n).degree f) = d →
        f ∈ Submodule.span B {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n)
          (I : ∀ k, Fin (sz k) → Fin r), shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} := by
      intro d
      induction d using WellFoundedLT.induction with
      | _ d ih =>
        intro f hf hd
        by_cases hf0 : f = 0
        · rw [hf0]; exact Submodule.zero_mem _
        have hm := (colLex r n).degree_mem_support hf0
        obtain ⟨K, sz, hsz, I, hsh, hmono, hexp⟩ :=
          hSS r n ν _ (hCS B r n ν f hf _ hm) (hLI B r n ν f hf hf0)
        obtain ⟨hdeg, hlc⟩ := hCL B r n K sz hsz I hmono
        have hg : bideterminant B sz hsz I ∈ dualWeyl B r n ν := by
          rw [← hsh]; exact bidetMem B r n K sz hsz I
        have hgS : bideterminant B sz hsz I ∈ Submodule.span B {f | ∃ (K : ℕ) (sz : Fin K → ℕ)
            (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
            shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} :=
          Submodule.subset_span ⟨K, sz, hsz, I, hsh, rfl⟩
        have hf' : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I ∈ dualWeyl B r n ν :=
          Submodule.sub_mem _ hf (Submodule.smul_mem _ _ hg)
        have h1 : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I ∈ Submodule.span B
            {f | ∃ (K : ℕ) (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ n) (I : ∀ k, Fin (sz k) → Fin r),
              shapeDeg sz = ν ∧ f = bideterminant B sz hsz I} := by
          by_cases hne : f - (colLex r n).leadingCoeff f • bideterminant B sz hsz I = 0
          · rw [hne]; exact Submodule.zero_mem _
          have hlt := lcassem_sub_lt (colLex r n) (hdeg.trans hexp) hlc hne
          exact ih _ (by rw [← hd]; exact hlt) _ hf' rfl
        have h2 := Submodule.add_mem _ h1 (Submodule.smul_mem _ ((colLex r n).leadingCoeff f) hgS)
        rwa [sub_add_cancel] at h2
    exact fun f hf => key _ f hf rfl
  · rw [Submodule.span_le]
    rintro _ ⟨K, sz, hsz, I, hsh, rfl⟩
    rw [← hsh]
    exact bidetMem B r n K sz hsz I

end Formalism.GradedWeylDivisibility
end

-- bundled from Formalism.GradedWeylDivisibility.FockSpaceTableaux.WeylEqNablaQ
section
open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

theorem weylEqNablaQ_of (h : ClosedEqNabla) : WeylEqNablaQ := by
  intro r n hn ν hν
  refine h r n hn ν hν (weyl ℚ r n hn ν) (weylLeDual ℚ r n hn ν hν)
    (fun a b k f hf => weylRowDivStable ℚ r n hn ν a b k f hf) ?_

  exact Submodule.subset_span ⟨[], rfl⟩

end Formalism.GradedWeylDivisibility
end
end

