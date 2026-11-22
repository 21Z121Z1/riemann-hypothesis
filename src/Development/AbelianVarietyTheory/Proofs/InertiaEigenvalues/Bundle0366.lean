import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0260
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComparisonIsFiltered
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0344
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionLeftExactFunctorKernelSquareMatrix
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0013
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLatInOfIndexLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.StepJumpDirect
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.StrictIndepPowOfRegularPair
section
namespace GlobalTheory.BSP.StrictIndep

variable {S A : Type} [CommRing S] [CommRing A]

theorem span_sup_span_eq_pair (x y : S) :
    Ideal.span {x} ⊔ Ideal.span {y} = Ideal.span ({x, y} : Set S) := by
  rw [← Ideal.span_union, Set.singleton_union]

theorem map_span_pair (s : S →+* A) (x y : S) :
    (Ideal.span {x} ⊔ Ideal.span {y}).map s = Ideal.span ({s x, s y} : Set A) := by
  rw [Ideal.map_sup, Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton,
    span_sup_span_eq_pair]

theorem sum_decomp (s : S →+* A) {ι : Type} (b : ι → A) (T : Finset ι) (u v : ι → S) (P Q : S) :
    ∑ i ∈ T, s (u i * P + v i * Q) * b i
      = s P * ∑ i ∈ T, s (u i) * b i + s Q * ∑ i ∈ T, s (v i) * b i := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_add, map_mul]
  ring

theorem indep_finset (s : S →+* A) (p q : S) {ι : Type} (b : ι → A)
    (h3 : ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q})
    (T : Finset ι) (c : ι → S) (h : ∑ i ∈ T, s (c i) * b i ∈ Ideal.span ({s p, s q} : Set A)) :
    ∀ i ∈ T, c i ∈ Ideal.span ({p, q} : Set S) := by
  classical
  intro i hi
  have key := h3 (Finsupp.onFinset T (fun j => if j ∈ T then c j else 0)
    (by intro j hj; by_contra hn; simp [hn] at hj)) (by
      rw [map_span_pair, Finsupp.onFinset_sum _ (by intro j; simp)]
      convert h using 1
      exact Finset.sum_congr rfl (fun j hj => by simp [hj])) i
  rw [span_sup_span_eq_pair] at key
  simpa [hi] using key

theorem dvd_of_dvd_pow_mul (s : S →+* A) (p q : S)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x) :
    ∀ (n : ℕ) (x : A), s p ∣ s q ^ n * x → s p ∣ x := by
  intro n
  induction n with
  | zero => intro x h; simpa using h
  | succ n ih =>
    intro x h
    apply h2
    apply ih
    rw [pow_succ, mul_assoc] at h
    exact h

theorem pow_dvd_of_dvd_pow_mul (s : S →+* A) (p q : S)
    (h1 : ∀ x : A, s p * x = 0 → x = 0)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x) (n : ℕ) :
    ∀ (m : ℕ) (x : A), s q ^ n ∣ s p ^ m * x → s q ^ n ∣ x := by
  have base : ∀ x : A, s q ^ n ∣ s p * x → s q ^ n ∣ x := by
    rintro x ⟨y, hy⟩
    obtain ⟨t, ht⟩ := dvd_of_dvd_pow_mul s p q h2 n y ⟨x, by rw [← hy]⟩
    refine ⟨t, ?_⟩
    have h0 : s p * (x - s q ^ n * t) = 0 := by
      rw [mul_sub, hy, ht]; ring
    exact sub_eq_zero.1 (h1 _ h0)
  intro m
  induction m with
  | zero => intro x h; simpa using h
  | succ m ih =>
    intro x h
    apply base
    apply ih
    rw [pow_succ, mul_assoc] at h
    exact h

theorem step_one (s : S →+* A) (p q : S) {ι : Type} (b : ι → A)
    (h1 : ∀ x : A, s p * x = 0 → x = 0)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x)
    (h3 : ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q}) :
    ∀ (n : ℕ) (T : Finset ι) (c : ι → S),
      ∑ i ∈ T, s (c i) * b i ∈ Ideal.span ({s p, s q ^ n} : Set A) →
      ∀ i ∈ T, c i ∈ Ideal.span ({p, q ^ n} : Set S) := by
  intro n
  induction n with
  | zero =>
    intro T c _ i _
    exact Ideal.mem_span_pair.2 ⟨0, c i, by simp⟩
  | succ n ih =>
    intro T c h
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 h
    have hT : ∀ i ∈ T, c i ∈ Ideal.span ({p, q ^ n} : Set S) :=
      ih T c (Ideal.mem_span_pair.2 ⟨x, y * s q, by rw [← hxy]; ring⟩)
    have hex : ∀ i, ∃ u v : S, i ∈ T → u * p + v * q ^ n = c i := by
      intro i
      by_cases hi : i ∈ T
      · obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hT i hi)
        exact ⟨u, v, fun _ => huv⟩
      · exact ⟨0, 0, fun h => absurd h hi⟩
    choose u v huv using hex
    have hsum : ∑ i ∈ T, s (c i) * b i
        = s p * ∑ i ∈ T, s (u i) * b i + s q ^ n * ∑ i ∈ T, s (v i) * b i := by
      rw [← map_pow, ← sum_decomp]
      exact Finset.sum_congr rfl fun i hi => by rw [huv i hi]
    set U := ∑ i ∈ T, s (u i) * b i
    set V := ∑ i ∈ T, s (v i) * b i
    have hd : s p ∣ s q ^ n * (V - y * s q) :=
      ⟨x - U, by linear_combination -hxy - hsum⟩
    obtain ⟨t, ht⟩ := dvd_of_dvd_pow_mul s p q h2 n _ hd
    have hV : V ∈ Ideal.span ({s p, s q} : Set A) :=
      Ideal.mem_span_pair.2 ⟨t, y, by linear_combination -ht⟩
    intro i hi
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 (indep_finset s p q b h3 T v hV i hi)
    refine Ideal.mem_span_pair.2 ⟨u i + α * q ^ n, β, ?_⟩
    rw [← huv i hi, ← hαβ]
    ring

theorem step_three (s : S →+* A) (p q : S) {ι : Type} (b : ι → A)
    (h1 : ∀ x : A, s p * x = 0 → x = 0)
    (h2 : ∀ x : A, s p ∣ s q * x → s p ∣ x)
    (h3 : ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q}) (n : ℕ) :
    ∀ (m : ℕ) (T : Finset ι) (c : ι → S),
      ∑ i ∈ T, s (c i) * b i ∈ Ideal.span ({s p ^ m, s q ^ n} : Set A) →
      ∀ i ∈ T, c i ∈ Ideal.span ({p ^ m, q ^ n} : Set S) := by
  intro m
  induction m with
  | zero =>
    intro T c _ i _
    exact Ideal.mem_span_pair.2 ⟨c i, 0, by simp⟩
  | succ m ih =>
    intro T c h
    obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 h
    have hT : ∀ i ∈ T, c i ∈ Ideal.span ({p ^ m, q ^ n} : Set S) :=
      ih T c (Ideal.mem_span_pair.2 ⟨x * s p, y, by rw [← hxy]; ring⟩)
    have hex : ∀ i, ∃ u v : S, i ∈ T → u * p ^ m + v * q ^ n = c i := by
      intro i
      by_cases hi : i ∈ T
      · obtain ⟨u, v, huv⟩ := Ideal.mem_span_pair.1 (hT i hi)
        exact ⟨u, v, fun _ => huv⟩
      · exact ⟨0, 0, fun h => absurd h hi⟩
    choose u v huv using hex
    have hsum : ∑ i ∈ T, s (c i) * b i
        = s p ^ m * ∑ i ∈ T, s (u i) * b i + s q ^ n * ∑ i ∈ T, s (v i) * b i := by
      rw [← map_pow, ← map_pow, ← sum_decomp]
      exact Finset.sum_congr rfl fun i hi => by rw [huv i hi]
    set U := ∑ i ∈ T, s (u i) * b i
    set V := ∑ i ∈ T, s (v i) * b i
    have hd : s q ^ n ∣ s p ^ m * (U - x * s p) :=
      ⟨y - V, by linear_combination -hxy - hsum⟩
    obtain ⟨w, hw⟩ := pow_dvd_of_dvd_pow_mul s p q h1 h2 n m _ hd
    have hU : U ∈ Ideal.span ({s p, s q ^ n} : Set A) :=
      Ideal.mem_span_pair.2 ⟨x, w, by linear_combination -hw⟩
    intro i hi
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.1 (step_one s p q b h1 h2 h3 n T u hU i hi)
    refine Ideal.mem_span_pair.2 ⟨α, β * p ^ m + v i, ?_⟩
    rw [← huv i hi, ← hαβ]
    ring

end GlobalTheory.BSP.StrictIndep

namespace GlobalTheory.BSP

open GlobalTheory.BSP.StrictIndep in

theorem strict_indep_pow : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (p q : S)
    (ι : Type) (b : ι → A), (∀ x : A, s p * x = 0 → x = 0) →
    (∀ x : A, s p ∣ s q * x → s p ∣ x) →
    (∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈ (Ideal.span {p} ⊔ Ideal.span {q}).map s →
      ∀ i, a i ∈ Ideal.span {p} ⊔ Ideal.span {q}) →
    ∀ n : ℕ, ∃ m : ℕ, ∀ a : ι →₀ S, a.sum (fun i y => s y * b i) ∈
      ((Ideal.span {p} ⊔ Ideal.span {q}) ^ m).map s →
      ∀ i, a i ∈ (Ideal.span {p} ⊔ Ideal.span {q}) ^ n := by
  intro S A _ _ s p q ι b h1 h2 h3 n
  refine ⟨n + n, fun a ha i => ?_⟩
  have hle : (Ideal.span {p} ⊔ Ideal.span {q}) ^ (n + n) ≤ Ideal.span {p ^ n} ⊔ Ideal.span {q ^ n} := by
    refine Ideal.sup_pow_add_le_pow_sup_pow.trans ?_
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow]
  have ha' : a.sum (fun i y => s y * b i) ∈ Ideal.span ({s p ^ n, s q ^ n} : Set A) := by
    have := Ideal.map_mono (f := s) hle ha
    rwa [map_span_pair, map_pow, map_pow] at this
  by_cases hi : i ∈ a.support
  · have hc := step_three s p q b h1 h2 h3 n n a.support (fun j => a j) ha' i hi
    rw [← span_sup_span_eq_pair, ← Ideal.span_singleton_pow, ← Ideal.span_singleton_pow] at hc
    have hle2 : Ideal.span {p} ^ n ⊔ Ideal.span {q} ^ n ≤ (Ideal.span {p} ⊔ Ideal.span {q}) ^ n :=
      sup_le (Ideal.pow_right_mono le_sup_left n) (Ideal.pow_right_mono le_sup_right n)
    exact hle2 hc
  · rw [Finsupp.notMem_support_iff.1 hi]
    exact Ideal.zero_mem _

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDeRhamFiltrationQuotientInvariants
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.TateFilQuot

open GlobalTheory.DRFil

section Abstract

variable {G B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
  (σ : G → B →+* B) (ρ : G → M →+ M) (F : ℤ → AddSubgroup B) (FM : ℤ → AddSubgroup M)

theorem step_invariant
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    {ι : Type} [DecidableEq ι] (k : ι → ℤ) (d : ι → M) (hd : ∀ i g, ρ g (d i) = d i)
    (hdk : ∀ i, d i ∈ FM (k i)) (c : ℤ) (n : ℕ) :
    ∀ (s : Finset ι), s.card = n → ∀ b : ι → B, (∀ i ∈ s, b i ∈ F (c - k i)) →
      (∀ g, ρ g (∑ i ∈ s, b i • d i) - ∑ i ∈ s, b i • d i ∈ FM (c + 1)) →
      ∃ w ∈ FM c, (∀ g, ρ g w = w) ∧ ∑ i ∈ s, b i • d i - w ∈ FM (c + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn b hb hsum
  by_cases hs : ∃ i ∈ s, ∃ κ : ι → B, (∀ j, κ j ∈ F 0 ∧ (∀ g, σ g (κ j) = κ j) ∧ (k i ≠ k j → κ j = 0)) ∧
      d i + ∑ j ∈ s.erase i, κ j • d j ∈ FM (k i + 1)
  · obtain ⟨i, hi, κ, hκ, hmem⟩ := hs
    have heq : ∑ j ∈ s, b j • d j = b i • (d i + ∑ j ∈ s.erase i, κ j • d j) +
        ∑ j ∈ s.erase i, (b j - b i * κ j) • d j := by
      rw [← Finset.add_sum_erase s _ hi]
      simp only [smul_add, Finset.smul_sum, mul_smul, sub_smul, Finset.sum_sub_distrib]
      abel
    have h1 := hsmul _ _ _ _ (hb i hi) hmem
    rw [show c - k i + (k i + 1) = c + 1 by ring] at h1
    rw [heq] at hsum ⊢
    obtain ⟨w, hw, hwg, hw'⟩ := ih _ (hn ▸ Finset.card_erase_lt_of_mem hi) (s.erase i) rfl
      (fun j => b j - b i * κ j) (fun j hj => by
        refine (F _).sub_mem (hb j (Finset.mem_of_mem_erase hj)) ?_
        by_cases hk : k i = k j
        · have := hmul _ _ _ _ (hb i hi) (hκ j).1
          rwa [add_zero, hk] at this
        · rw [(hκ j).2.2 hk, mul_zero]
          exact (F _).zero_mem) (fun g => by
        have h2 := (FM _).sub_mem (hsum g) ((FM _).sub_mem (hMG g _ _ h1) h1)
        convert h2 using 1
        rw [map_add (ρ g) (b i • _)]
        abel)
    refine ⟨w, hw, hwg, ?_⟩
    rw [add_sub_assoc]
    exact (FM _).add_mem h1 hw'
  · have hg : ∀ g, ∀ i ∈ s, σ g (b i) - b i ∈ F (c - k i + 1) := fun g =>
      graded_indep σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k d hd hdk s hs c
        (fun i => σ g (b i) - b i) (fun i hi => (F _).sub_mem (hFG _ _ _ (hb i hi)) (hb i hi)) (by
          convert hsum g using 1
          simp only [map_sum, hρ, hd, sub_smul, Finset.sum_sub_distrib])
    have hκ : ∀ i, ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (c - k i ≠ 0 → κ = 0) ∧
        (i ∈ s → b i - κ ∈ F (c - k i + 1)) := fun i => by
      by_cases hi : i ∈ s
      · obtain ⟨κ, h1, h2, h3, h4⟩ := hT _ _ (hb i hi) (fun g => hg g i hi)
        exact ⟨κ, h1, h2, h3, fun _ => h4⟩
      · exact ⟨0, (F 0).zero_mem, fun g => map_zero _, fun _ => rfl, fun h => (hi h).elim⟩
    choose κ h1 h2 h3 h4 using hκ
    refine ⟨∑ i ∈ s, κ i • d i, (FM _).sum_mem fun i _ => ?_, fun g => ?_, ?_⟩
    · by_cases hk : c - k i = 0
      · have := hsmul _ _ _ _ (h1 i) (hdk i)
        rwa [show 0 + k i = c by omega] at this
      · rw [h3 i hk, zero_smul]
        exact (FM _).zero_mem
    · simp only [map_sum, hρ, hd, h2]
    · rw [← Finset.sum_sub_distrib]
      refine (FM _).sum_mem fun i hi => ?_
      have := hsmul _ _ _ _ (h4 i hi) (hdk i)
      rwa [show c - k i + 1 + k i = c + 1 by ring, sub_smul] at this

theorem invariant_mod
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    (hFa : Antitone F) (hMa : Antitone FM) (hFe : ∀ x, ∃ a, x ∈ F a) (hMe : ∀ x, ∃ a, x ∈ FM a)
    (hspan : ∀ y : M, ∃ (m : ℕ) (b : Fin m → B) (d : Fin m → M),
      (∀ i g, ρ g (d i) = d i) ∧ y = ∑ i, b i • d i)
    (a b : ℤ) (z : M) (hz : z ∈ FM a) (hg : ∀ g, ρ g z - z ∈ FM b) :
    ∃ w ∈ FM a, (∀ g, ρ g w = w) ∧ z - w ∈ FM b := by
  have key : ∀ c, a ≤ c → c ≤ max a b → ∃ w ∈ FM a, (∀ g, ρ g w = w) ∧ z - w ∈ FM c := by
    intro c hc
    induction c, hc using Int.le_induction with
    | base => exact fun _ => ⟨0, (FM _).zero_mem, fun g => map_zero _, by rwa [sub_zero]⟩
    | succ c hc ih =>
      intro hcb
      have hcb' : c + 1 ≤ b := by omega
      obtain ⟨w, hw, hwg, hzw⟩ := ih (by omega)
      obtain ⟨m, b₀, d₀, hd₀, e₀⟩ := hspan (z - w)
      obtain ⟨m', k', b', d', h, e⟩ := filtered σ ρ F FM hρ hmul hsmul hFG hMG hinv hT hFa hMa hFe hMe
        c (z - w) hzw m b₀ d₀ hd₀ e₀
      obtain ⟨w', hw', hwg', hzw'⟩ := step_invariant σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k' d'
        (fun i => (h i).1) (fun i => (h i).2.1) c _ Finset.univ rfl b' (fun i _ => (h i).2.2)
        (fun g => by
          rw [← e, map_sub, hwg, sub_sub_sub_cancel_right]
          exact hMa hcb' (hg g))
      refine ⟨w + w', (FM _).add_mem hw (hMa hc hw'), fun g => by rw [map_add, hwg, hwg'], ?_⟩
      rwa [← e, sub_sub] at hzw'
  obtain ⟨w, hw, hwg, hzw⟩ := key (max a b) (le_max_left _ _) le_rfl
  exact ⟨w, hw, hwg, hMa (le_max_right _ _) hzw⟩

end Abstract

theorem tied_invariant_mod (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (TT : LocTied l P AI) (K : FinExt l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
    [FiniteDimensional ℚ_[l] LL] (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    (hdR : IsDR (P.PD K) ρ) (a b : ℤ) (z : V ⊗[ℚ_[l]] P.R.BdR)
    (hz : z ∈ FilV (P.PD K) (LL := LL) (V := V) a)
    (hg : ∀ g, actVdR (P.PD K) ρ g z - z ∈ FilV (P.PD K) (LL := LL) (V := V) b) :
    ∃ w ∈ DdR (P.PD K) ρ ⊓ FilV (P.PD K) (LL := LL) (V := V) a,
      z - w ∈ FilV (P.PD K) (LL := LL) (V := V) b := by
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT
  have hspan := GlobalTheory.Per.DeRhamSpan.span_of_isField (P.PD K) ρ
    (GlobalTheory.Per.TiedField.tied_field l P AI TT).1 hdR
  let φ : P.R.BdR →+* Module.End LL (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := fun b => AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] b)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul, tmul_add] }
  letI : Module P.R.BdR (V ⊗[ℚ_[l]] P.R.BdR) := Module.compHom _ φ
  have hsm : ∀ (b : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR), b • x =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (LinearMap.mulLeft ℚ_[l] b) x := fun _ _ => rfl
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ ↔ ∀ g, actVdR (P.PD K) ρ g x = x := fun x => by
    simp [DdR, Submodule.mem_iInf, sub_eq_zero]
  have htm : ∀ (a : ℤ) (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a →
      v ⊗ₜ[ℚ_[l]] x ∈ FilV (P.PD K) (LL := LL) (V := V) a := fun a v x hx =>
    ⟨v ⊗ₜ ⟨x, hx⟩, rfl⟩
  have hind : ∀ (a : ℤ) (S : AddSubgroup (V ⊗[ℚ_[l]] P.R.BdR)),
      (∀ (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a → v ⊗ₜ[ℚ_[l]] x ∈ S) →
      ∀ z ∈ FilV (P.PD K) (LL := LL) (V := V) a, z ∈ S := by
    rintro a S hS _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | tmul v x => exact hS v x x.2
    | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
  have hFa : Antitone fun a => ((P.PD K).Fil a).toAddSubgroup :=
    antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a
  have hMa : Antitone fun a => (FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup :=
    fun a a' h z hz => hind a' _ (fun v x hx => htm a v x (hFa h hx)) z hz
  obtain ⟨w, hw, hwg, hzw⟩ := invariant_mod (G := ↥(GK K))
    (fun g => ((P.PD K).actdR g : P.R.BdR →+* P.R.BdR))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom)
    (fun a => ((P.PD K).Fil a).toAddSubgroup)
    (fun a => (FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup)
    (fun g b x => by
      rw [hsm, hsm]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v x => simp [actVdR]
      | add x y hx hy => simp only [map_add, hx, hy])
    (P.PD K).Fil_mul
    (fun a c x z hx hz => hind c
      ((FilV (P.PD K) (LL := LL) (V := V) (a + c)).toAddSubgroup.comap (φ x).toAddMonoidHom)
      (fun v w hw => htm _ v (x * w) ((P.PD K).Fil_mul _ _ _ _ hx hw)) z hz)
    (P.PD K).Fil_G
    (fun g a z hz => hind a
      ((FilV (P.PD K) (LL := LL) (V := V) a).toAddSubgroup.comap (actVdR (P.PD K) ρ g).toAddMonoidHom)
      (fun v w hw => htm _ (ρ g v) ((P.PD K).actdR g w) ((P.PD K).Fil_G _ _ _ hw)) z hz)
    (graded_inv Θ K) (graded_invariants TT Θ K) hFa hMa (P.PD K).Fil_exh
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, AddSubgroup.zero_mem _⟩
      | tmul v x =>
        obtain ⟨c, hc⟩ := (P.PD K).Fil_exh x
        exact ⟨c, htm c v x hc⟩
      | add x y hx hy =>
        obtain ⟨c, hc⟩ := hx
        obtain ⟨c', hc'⟩ := hy
        exact ⟨min c c', AddSubgroup.add_mem _ (hMa (min_le_left _ _) hc) (hMa (min_le_right _ _) hc')⟩)
    (fun y => by
      obtain ⟨m, b, d, hd, e⟩ := hspan y
      exact ⟨m, b, d, fun i g => (hD _).1 (hd i) g, e⟩)
    a b z hz hg
  exact ⟨w, ⟨(hD _).2 hwg, hw⟩, hzw⟩

theorem tate_fil_quot : ∀ D : D7, Formalism.MainNotions.LocalSituation.adm5 D := by
  intro D l _ K LL _ _ _ O _ _ hO A hA a b z hz hg
  haveI := hO.2.1
  exact tied_invariant_mod l (D.loc l) (D.locA l) (D.locT l) K LL A.V A.ρ hA a b z hz hg

end GlobalTheory.TateFilQuot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ToricLam0UnitaryTrivOnMaxRealSubfieldStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lam0_isUnitary_and_trivOnF : ∀ (D : D7) (Z : LamDat D), Z.Ok → ∀ (l : ℕ) (j a : Fin D.R.m), (Z.lam0 l j a).IsUnitary ∧ TrivOnF (Z.lam0 l j a) := by
  first | exact @GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | exact GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield | (intros; apply GlobalTheory.LamTie.toricLam0_unitary_trivOnMaxRealSubfield <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TorsionLeftExactFunctorKernelSquareMatrixStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_left_exact_functor_kernel_square_matrix : KernelRep := by
  first | exact @GlobalTheory.KRep.kernelRep | exact GlobalTheory.KRep.kernelRep | (intros; apply GlobalTheory.KRep.kernelRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistModuleAllCharacterPowersOfAdmissible
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction.Gen Formalism.MainNotions.IntegralHeckeForms
open scoped TensorProduct

namespace GlobalTheory.ExportFromInputs

variable {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂}
  {X : NTw D.R D.host D.what₂ D.LL0 N} (Y : NExp D.R D.host D.what₂ D.LL0 N X)

open GlobalTheory.TwistInputsTest GlobalTheory.TwAll

theorem twistModule_all_character_powers_of_admissible (bkP : BKPh X) (E : ExpDat Y) (N0 : X.Tw → ℕ) (h2 : TwAll.admissibleIndexBoundAllPowers Y bkP N0) (h3 : IsotypicPartsInternalDirectSum Y E)
    (h5 : GroupAlgebraIntegrality Y) (h7 : admT4 Y E) (h10 : TwistedSeriesSpecialisation Y) (h11 : GoodLatticePoints Y) (i : X.Tw) (hi : X.NonzeroIndexPlace i) :
    TwAll.goodTwistExistsAllCoprimePowers Y bkP E N0 i := by
  classical
  intro hs eps' he hF S hS A
  choose z hz using fun b => (h5 i hi b).1
  have hAB := fun j hj b => abHyp_fam Y E i hi j hj b z (hz b) S h3 h5 h11 (hF j hj b) (hS j hj b)
  obtain ⟨Q, k, ψ₀, hall⟩ := h2 i hi hs eps' he (fam Y i z S) hAB (levs Y i S ∪ A)
  refine ⟨Q, k, ψ₀, fun n hn => ?_⟩
  have hn' := hall n hn
  generalize ψ₀ ^ n = ψ' at hn' ⊢
  obtain ⟨hok, ha, hc, hd, M, χ, hχ, epsB, h0, hsum, H⟩ := hn'
  have key : ∀ j ∈ Finset.Icc 1 D.R.m, ∀ b : Bool, _ := fun j hj b => by
    obtain ⟨htw, hu, hdis⟩ := twOK_of_psiOk i _ Q k ψ' hok b
    refine export_at Y E i hi j hj b (S j b) h3 h7 (hF j hj b) (hS j hj b) k Q _ htw hu (epsB j b) ?_
    intro T hT hle
    obtain ⟨-, hfg, hsp, -⟩ := h3 i hi j hj b
    have hA : (fam Y i z S).A j b = AO Y i j b := zO_eq Y i j b _ (hz b)
    have hTh : (fam Y i z S).Th j b = (Th Y i j b (SgJ Y E i j b)).map (AO Y i j b) := by
      rw [← (hS j hj b).2.2, RFam.Th, hA]; rfl
    rw [← hTh]
    refine H j hj b T ?_ fun a ha => ?_
    · have : Submodule.span (FractionRing (X.O i)) ((fam Y i z S).B j b : Set (Y.Fm i j b)) = V0 Y i j b :=
        span_of_isLatIn (isLatIn_B Y i j b hfg hsp)
      rw [this]; exact hT
    · have ha' : a ∈ S j b := ha
      rw [hχ, psiAt_comp] at htw hle
      have hlev : Disjoint Q (Y.lev i j b a) := by
        refine hdis.mono_right (le_trans ?_ Finset.subset_union_left)
        intro v hv
        simp only [levs, Finset.mem_biUnion]
        exact ⟨j, hj, b, Finset.mem_univ _, a, ha', hv⟩
      rw [hA]
      refine hle ⟨_, ?_, rfl⟩
      refine Submodule.span_mono ?_ (h10 i hi j hj b k Q M _ htw a hlev)
      exact Set.biUnion_subset_biUnion_left (Set.singleton_subset_iff.2 ((hS j hj b).1 ha'))
  exact ⟨hok, ⟨epsB, h0, hsum, fun j hj b => (key j hj b).1⟩, fun j hj b => (key j hj b).2, ha, hc, hd⟩

end GlobalTheory.ExportFromInputs

open GlobalTheory.TwAll in

theorem GlobalTheory.exportAll_of_inputs :
    ∀ (D : Formalism.BasicNotions.D7) (bkP : Formalism.MainNotions.BlochKatoReduction.BK D) (E : Formalism.MainNotions.IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ),
      Formalism.MainNotions.IntegralHeckeForms.admitted D bkP E N0 → admissibleIndexBoundAllPowers D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) N0 →
      ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (Formalism.MainNotions.BlochKatoReduction.pin bkP) E N0 i := by
  rintro D bkP E N0 ⟨-, -, h3, -, h5, h7, -, -, h10, h11⟩ h2 i hi
  exact GlobalTheory.ExportFromInputs.twistModule_all_character_powers_of_admissible D.nexp _ E N0 h2 h3 h5 h7 h10 h11 i hi

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedGaloisRepCharacterBlocksStatement
section
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_galois_rep_character_blocks : StepSub := by
  first | exact @GlobalTheory.Pass.stepSub_holds | exact GlobalTheory.Pass.stepSub_holds | (intros; apply GlobalTheory.Pass.stepSub_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UntiltFrobeniusDoubleSeriesHasSumAndNormBoundsStatement
section
open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.untiltFrobeniusDoubleSeries_hasSum_and_norm_bounds : ∀ (l : ℕ) [Fact l.Prime] (h j : ℕ) (r : ℝ) (y : ℕ → Fl l), 1 ≤ h → r < 1 → (∀ k, ‖sh (y k)‖ ≤ r) → HasSum (fun k : ℕ => (l : ℂ_[l]) ^ k * lam h j (y k)) (abelian₂ h j y) ∧ ‖abelian₂ h j y - lam h j (y 0)‖ ≤ ‖(l : ℂ_[l])‖ * gam l h j r ∧ ‖abelian₂ h j y‖ ≤ gam l h j r ∧ ∀ N : ℕ, abelian₂ h j (fun k => y k ^ l ^ (h * N)) = (l : ℂ_[l]) ^ N * abelian₂ h j y := by
  first | exact @GlobalTheory.PSer.Lam_main | exact GlobalTheory.PSer.Lam_main | (intros; apply GlobalTheory.PSer.Lam_main <;> assumption)
end

