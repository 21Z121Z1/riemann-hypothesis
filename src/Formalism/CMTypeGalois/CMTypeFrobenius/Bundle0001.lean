import Mathlib
import Formalism.CMTypeGalois.StatementGroup

-- bundled from Formalism.CMTypeGalois.CMTypeFrobenius.KroneckerMeaning
section
namespace Formalism.Q3

open ZMod

lemma kron_odd (q p : ℕ) (hq4 : q % 4 = 3) (hp : p.Prime) (hp2 : p ≠ 2) :
    jacobiSym (p : ℤ) q = jacobiSym (-(q : ℤ)) p := by
  have hpo : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hqo : q % 2 = 1 := by omega
  rw [jacobiSym.neg _ (Nat.odd_iff.mpr hpo)]
  have h := jacobiSym.quadratic_reciprocity_if hpo hqo
  rcases Nat.odd_mod_four_iff.mp hpo with h1 | h3
  · rw [χ₄_nat_one_mod_four h1, one_mul, ← h]
    simp [h1]
  · rw [χ₄_nat_three_mod_four h3, ← h]
    simp [h3, hq4]

theorem kroneckerMeaning : KroneckerMeaning := by
  intro q hq hq4
  have hqo : Odd q := Nat.odd_iff.mpr (by omega)
  refine ⟨fun p hp hp2 _ => kron_odd q p hq4 hp hp2, ?_, ?_⟩
  · unfold chiQ
    rw [jacobiSym.at_two hqo, χ₈_nat_eq_if_mod_eight]
    rw [if_neg (by omega)]
    by_cases h8 : q % 8 = 7
    · rw [if_pos (Or.inr h8)]; simp [h8]
    · rw [if_neg (by omega)]; simp [h8]
  · unfold chiQ
    rw [jacobiSym.at_neg_one hqo, χ₄_nat_three_mod_four hq4]

lemma sgn_one : sgn 1 = 1 := by
  unfold sgn; rw [if_pos rfl]

lemma cc_not_mem (a b : Gal3) (j : Fin 3) (ha : a j = 1) (hb : b j = 1) :
    cc ∉ Subgroup.closure ({a, b} : Set Gal3) := by
  intro h
  have hle : Subgroup.closure ({a, b} : Set Gal3) ≤ (Pi.evalMonoidHom (fun _ : Fin 3 => ℤˣ) j).ker := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]; exact ha
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, Pi.evalMonoidHom_apply]; exact hb
  have := hle h
  rw [MonoidHom.mem_ker, Pi.evalMonoidHom_apply] at this
  have h' : (-1 : ℤˣ) = 1 := this
  exact absurd h' (by decide)

end Formalism.Q3
end

-- bundled from Formalism.CMTypeGalois.CMTypeFrobenius.TypesA
section
open Finset

namespace Formalism.Q3

section general

variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}

lemma cc_mul (hc : c * c = 1) (g : G) : c * (c * g) = g := by
  rw [← mul_assoc, hc, one_mul]

lemma mem_dualTypeG (hc : c * c = 1) (Φ : Finset G) (g : G) :
    g ∈ dualTypeG c Φ ↔ g = 1 ∨ (c * g ∈ Φ ∧ c * g ≠ 1) := by
  unfold dualTypeG
  rw [Finset.mem_insert, Finset.mem_image]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · rw [Finset.mem_erase] at ha
      rw [cc_mul hc]
      exact Or.inr ⟨ha.2, ha.1⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨c * g, Finset.mem_erase.2 ⟨h2, h1⟩, cc_mul hc g⟩

lemma mul_ne_one_iff' (hc : c * c = 1) (g : G) : c * g ≠ 1 ↔ g ≠ c := by
  constructor
  · rintro h rfl
    exact h hc
  · intro h h'
    apply h
    have := cc_mul hc g
    rw [h', mul_one] at this
    exact this.symm

lemma key_dual (hc : c * c = 1) {Φ : Finset G} (hΦ : IsCMTypeG c Φ) (σ : G) (h1 : σ ≠ 1)
    (h2 : σ ≠ c) : σ ∈ dualTypeG c Φ ↔ σ ∉ Φ := by
  rw [mem_dualTypeG hc, hΦ σ, not_not]
  have := (mul_ne_one_iff' hc σ).2 h2
  tauto

end general

end Formalism.Q3
end

-- bundled from Formalism.CMTypeGalois.CMTypeFrobenius.TypesB
section
open Finset

namespace Formalism.Q3

namespace TypesB

variable {G : Type*} [CommGroup G] [DecidableEq G] {c : G}

lemma cc_mul' (hc : c * c = 1) (g : G) : c * (c * g) = g := by
  rw [← mul_assoc, hc, one_mul]

lemma mem_image_cmul (hc : c * c = 1) (X : Finset G) (g : G) :
    g ∈ X.image (fun x => c * x) ↔ c * g ∈ X := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 h
    rwa [cc_mul' hc]
  · intro h
    exact Finset.mem_image.2 ⟨c * g, h, cc_mul' hc g⟩

lemma exists_cmType [Fintype G] (hc1 : c ≠ 1) (hc : c * c = 1) :
    ∃ H : Finset G, IsCMTypeG c H ∧ 1 ∈ H := by
  let e := Fintype.equivFin G
  refine ⟨univ.filter (fun g => g = 1 ∨ (g ≠ c ∧ e g < e (c * g))), ?_, by simp⟩
  intro g
  simp only [mem_filter, mem_univ, true_and, cc_mul' hc]
  by_cases h1 : g = 1
  · subst h1
    simp [hc1]
  by_cases h2 : g = c
  · subst h2
    simp [hc, hc1]
  have h3 : c * g ≠ 1 := by
    intro h
    apply h2
    have := congrArg (fun x => c * x) h
    simp only [cc_mul' hc, mul_one] at this
    exact this
  have h4 : c * g ≠ c := by
    intro h
    apply h1
    exact mul_left_cancel (h.trans (mul_one c).symm)
  have h5 : e g ≠ e (c * g) := by
    intro h
    have h' : g = c * g := e.injective h
    apply hc1
    have : 1 * g = c * g := by rw [one_mul]; exact h'
    exact (mul_right_cancel this).symm
  simp only [h1, h2, h3, h4, false_or, ne_eq, not_false_eq_true, true_and, not_lt]
  exact ⟨le_of_lt, fun h => lt_of_le_of_ne h h5⟩

def ext (c : G) (H S : Finset G) : Finset G := S ∪ (H \ S).image (fun x => c * x)

lemma mem_ext (hc : c * c = 1) (H S : Finset G) (x : G) :
    x ∈ ext c H S ↔ x ∈ S ∨ (c * x ∈ H ∧ c * x ∉ S) := by
  unfold ext
  rw [mem_union, mem_image_cmul hc, mem_sdiff]

end TypesB

end Formalism.Q3
end

