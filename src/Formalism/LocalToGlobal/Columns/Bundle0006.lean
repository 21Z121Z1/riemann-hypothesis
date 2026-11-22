import Mathlib
import Formalism.LocalToGlobal.Columns.Bundle0005
import Formalism.LocalToGlobal.Columns.BaseInst
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Formalism.LocalToGlobal.Columns.RowForms
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Formalism.LocalToGlobal.Columns.Bundle0002
import Formalism.LocalToGlobal.Columns.LevGCount
import Formalism.LocalToGlobal.Columns.BaseLemmas
import Formalism.LocalToGlobal.Divisibility.DivisibilityProofs.TuplesP

-- bundled from Formalism.LocalToGlobal.Columns.ColFormsInst
section
open NumberField IsDedekindDomain IntermediateField Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.L2.Host Formalism.L2.DIV

section Gauss

variable (ι : Qb →+* ℂ) (LL : Fld) [FiniteDimensional ℚ LL] [Normal ℚ LL] (hE : KQ 1 ≤ LL)

def gaussianPrimesSmall : Primes (gaussFields ι LL hE) where
  cond := 4
  g := ![29, 5]
  piG := ![gz ι LL hE 5 2, gz ι LL hE 2 1]
  Word := Unit
  T := fun _ => 14145788201
  piT := fun _ => gz ι LL hE 84101 84100

set_option maxRecDepth 1000000 in
theorem prime_fourteen_billion_example : Nat.Prime 14145788201 := by norm_num

theorem gaussianPrimesSmall_ok : (gaussianPrimesSmall ι LL hE).Ok := by
  have n0 := gz_norm ι LL hE 5 2 29 (by norm_num)
  have n1 := gz_norm ι LL hE 2 1 5 (by norm_num)
  have nT := gz_norm ι LL hE 84101 84100 14145788201 (by norm_num)
  have p0 : Nat.Prime 29 := by norm_num
  have p1 : Nat.Prime 5 := by norm_num
  have hr := gauss_rank ι LL hE
  have hf := gauss_f ι LL hE
  exact
    { g_prime := Fin.forall_fin_two.2 ⟨p0, p1⟩
      piG_Kq := fun _ => gauss_Kq ι LL hE _
      piG_norm := Fin.forall_fin_two.2 ⟨n0, n1⟩
      piG_cop := Fin.forall_fin_two.2 ⟨gz_cop ι LL hE 5 2 3 (-1) (by norm_num), gz_cop ι LL hE 2 1 (-1) 1 (by norm_num)⟩
      vG_card := Fin.forall_fin_two.2
        ⟨(card_divs_of_norm _ hr p0 (conj_norm _ n0)).trans hf.symm, (card_divs_of_norm _ hr p1 (conj_norm _ n1)).trans hf.symm⟩
      vG_norm := Fin.forall_fin_two.2
        ⟨norm_divs_of_norm _ hr p0 (conj_norm _ n0), norm_divs_of_norm _ hr p1 (conj_norm _ n1)⟩
      g_cong := Fin.forall_fin_two.2 ⟨(by decide : 29 ≡ 1 [MOD 4]), (by decide : 5 ≡ 1 [MOD 4])⟩
      g_ne := (by decide : (29 : ℕ) ≠ 5)
      T_prime := fun _ => prime_fourteen_billion_example
      piT_Kq := fun _ => gauss_Kq ι LL hE _
      piT_norm := fun _ => nT
      piT_cop := fun _ => gz_cop ι LL hE 84101 84100 (-84100) 1 (by norm_num)
      vT_card := fun _ => (card_divs_of_norm _ hr prime_fourteen_billion_example nT).trans hf.symm
      vT_norm := fun _ => norm_divs_of_norm _ hr prime_fourteen_billion_example nT
      piT_cong := fun _ => by
        have e : (gaussianPrimesSmall ι LL hE).cond * ((gaussianPrimesSmall ι LL hE).g 0 * (gaussianPrimesSmall ι LL hE).g 1) ^ 2 = 84100 := by
          show 4 * (29 * 5) ^ 2 = 84100
          norm_num
        rw [e]
        refine ⟨gz ι LL hE 1 1, ?_⟩
        show gz ι LL hE 84101 84100 - 1 = _
        unfold gz
        push_cast
        ring
      T_ne_g := fun _ => Fin.forall_fin_two.2 ⟨(by norm_num : (14145788201 : ℕ) ≠ 29), (by norm_num : (14145788201 : ℕ) ≠ 5)⟩ }

theorem gaussianSmallPrime_gt_twice_rank : 2 * (gaussFields ι LL hE).f * Examples₂.R0.k < (gaussianPrimesSmall ι LL hE).g 0 - 1 := by
  rw [gauss_f]
  show 2 * 1 * 8 < 29 - 1
  norm_num

end Gauss

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.GoodXg
section
open NumberField IsDedekindDomain Polynomial

noncomputable section

namespace Formalism.L2.Col

open Formalism.L2.DIV

section Good

variable {X : Fields} (Pr : Primes X)

theorem gxMemGs (i : Fin 2) {w : HeightOneSpectrum (𝓞 X.E)} (h : w ∈ Pr.vG i) : w ∈ Pr.vGs := by
  classical
  unfold Primes.vGs
  rw [Finset.mem_union]
  match i, h with
  | 0, h => exact Or.inl h
  | 1, h => exact Or.inr h

variable {m : ℕ} (Ch : Chars X Pr m) (r : ℕ) [∀ i, Fact (Pr.g i).Prime]
  (σ : X.K →+* ℂ) (teich : ∀ i : Fin 2, Formalism.CyclotomicNorms.Fbar (Pr.g i) →* ℂ) (ζ : ∀ i : Fin 2, ℕ → Formalism.CyclotomicNorms.Fbar (Pr.g i))

def gxLoc (i : Fin 2) (w : HeightOneSpectrum (𝓞 X.E)) (χw : GL (Fin r) (𝓞 X.E ⧸ w.asIdeal) → ℂ)
    (f : (ZMod (Pr.g i))[X]) : Prop :=
  ∃ e : (𝓞 X.E ⧸ w.asIdeal) ≃+* ZMod (Pr.g i),
    Formalism.L2.NT.IsIrrChar (fun x : GL (Fin r) (ZMod (Pr.g i)) => χw (Matrix.GeneralLinearGroup.map e.symm.toRingHom x)) ∧
      Formalism.L2.NT.InSeries (teich i) (ζ i)
        (fun x : GL (Fin r) (ZMod (Pr.g i)) => χw (Matrix.GeneralLinearGroup.map e.symm.toRingHom x)) f

def gxChiLab (i : Fin 2) (w : {w // w ∈ Pr.vGs}) (j : Fin m) (a : (ZMod (Pr.g i))ˣ) : Prop :=
  ∃ (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* ZMod (Pr.g i)) (k : ℕ),
    (∀ x : (ZMod (Pr.g i))ˣ, σ ((Ch.chi j w (Units.map e.symm.toRingHom.toMonoidHom x) : X.Kˣ) : X.K) =
      teich i (algebraMap (ZMod (Pr.g i)) (Formalism.CyclotomicNorms.Fbar (Pr.g i)) (x : ZMod (Pr.g i))) ^ k) ∧
    algebraMap (ZMod (Pr.g i)) (Formalism.CyclotomicNorms.Fbar (Pr.g i)) (a : ZMod (Pr.g i)) = ζ i 1 ^ k

def gxGoodLab (i : Fin 2) (f : {w // w ∈ Pr.vG i} → (ZMod (Pr.g i))[X]) : Prop :=
  ∃ a : {w // w ∈ Pr.vG i} → Fin m → (ZMod (Pr.g i))ˣ,
    (∀ w j, gxChiLab Pr Ch σ teich ζ i ⟨w.1, gxMemGs Pr i w.2⟩ j (a w j)) ∧
      Formalism.CyclotomicNorms.IsGood r (Pr.g i) f a ∧ Formalism.CyclotomicNorms.IsGood r (Pr.g i) f (fun w j => (a w j)⁻¹)

def gxGood (χc : G0 X.E Pr.vGs r → ℂ) : Prop :=
  ∃ (χw : ∀ w : {w // w ∈ Pr.vGs}, GL (Fin r) (𝓞 X.E ⧸ w.1.asIdeal) → ℂ)
    (f : ∀ i : Fin 2, {w // w ∈ Pr.vG i} → (ZMod (Pr.g i))[X]),
    (∀ x : G0 X.E Pr.vGs r, χc x = ∏ w, χw w (x w)) ∧
      (∀ (i : Fin 2) (w : {w // w ∈ Pr.vG i}),
        gxLoc Pr r teich ζ i w.1 (χw ⟨w.1, gxMemGs Pr i w.2⟩) (f i w)) ∧
      ∀ i : Fin 2, gxGoodLab Pr Ch r σ teich ζ i (f i)

def XgSet : Set (G0 X.E Pr.vGs r → X.K) :=
  {χ | IsAbsIrrChar χ ∧ gxGood Pr Ch r σ teich ζ (fun x => σ (χ x))}

theorem XgSet_finite : (XgSet Pr Ch r σ teich ζ).Finite :=
  (absIrrChar_finite (G := G0 X.E Pr.vGs r) (K := X.K)).subset fun _ h => h.1

def XgC : Finset (G0 X.E Pr.vGs r → X.K) := (XgSet_finite Pr Ch r σ teich ζ).toFinset

end Good

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RowFormsSel
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.EigenvalueLevelCeiling

section Sel

theorem exists_sel (X : Fields) : ∃ sel, IsSel X sel := by
  classical
  have h : ∀ v : HeightOneSpectrum (𝓞 X.F), ∃ P : HeightOneSpectrum (𝓞 X.E),
      P.asIdeal.under (𝓞 X.F) = v.asIdeal := by
    intro v
    obtain ⟨Q, hQm, hQ⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 X.E) v.asIdeal
    have hQ0 : Q ≠ ⊥ := by
      intro h0
      apply v.ne_bot
      rw [hQ.over, h0, Ideal.under_bot]
    exact ⟨⟨Q, hQm.isPrime, hQ0⟩, hQ.over.symm⟩
  choose sel hsel using h
  exact ⟨sel, hsel⟩

variable {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

theorem rf_tup_fin : (Qprime (mu : Chr X.F X.E X.K)).Finite :=
  auxiliary_primes_finite X.F X.E X.K _ ((mem_tupGrp (mu : Chr X.F X.E X.K)).mp mu.2).1.2.1

theorem mem_QE (P : HeightOneSpectrum (𝓞 X.E)) :
    P ∈ QE sel (mu : Chr X.F X.E X.K) ↔ ∃ v ∈ Qprime (mu : Chr X.F X.E X.K), sel v = P := by
  unfold QE
  rw [dif_pos (rf_tup_fin mu)]
  simp only [Finset.mem_image, Set.Finite.mem_toFinset]

variable {sel}

theorem resChar_QE_ne (hX : X.Ok) (hsel : IsSel X sel) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    resChar (mu : Chr X.F X.E X.K) P ≠ 1 := by
  obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu P).mp hP
  obtain ⟨⟨P1, P2, hne, hsp⟩, -, -⟩ := mu.good hv
  have hm := (mem_tupGrp (mu : Chr X.F X.E X.K)).mp mu.2
  have hR := residue_character_ramified X.F X.E X.K hX.rankE (mu : Chr X.F X.E X.K) hm.2.2.1 hm.2.1
  by_cases h1 : sel v = P1
  · rw [h1]; exact (hR v P1 P2 hne hsp).mp hv
  · by_cases h2 : sel v = P2
    · rw [h2]; exact (hR v P2 P1 hne.symm (by rw [hsp, mul_comm])).mp hv
    · exact absurd (hsel v) (d_other hsp h1 h2)

theorem rowTyQ_ne (R : Ranks) (hX : X.Ok) (hsel : IsSel X sel) (P : QE sel (mu : Chr X.F X.E X.K)) :
    (rowTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)) P).lam ≠ 1 ∧
    (mtTyQ R (mu : Chr X.F X.E X.K) (QE sel (mu : Chr X.F X.E X.K)) P).lam ≠ 1 := by
  have ht : 0 < R.t := by have := R.rank_add_five_le; omega
  have hm : 0 < R.m := by have := R.two_le_m; omega
  constructor
  · intro h
    exact lamQ_ne_one (Nat.mul_pos hm ht) (le_of_eq (rank_X'_eq R).symm) (resChar_QE_ne mu hX hsel P.1 P.2) (inv_eq_one.mp h)
  · exact lamQ_ne_one ht le_rfl (resChar_QE_ne mu hX hsel P.1 P.2)

theorem qdat_tied (hsel : IsSel X sel) :
    QDat.TiedTo (⟨QE sel (mu : Chr X.F X.E X.K), fun P => resChar (mu : Chr X.F X.E X.K) P.1⟩ : QDat X) (mu : Chr X.F X.E X.K) where
  places := by
    intro v
    constructor
    · intro hv
      exact ⟨sel v, (mem_QE sel mu _).mpr ⟨v, hv, rfl⟩, hsel v⟩
    · rintro ⟨P, hP, e⟩
      obtain ⟨v', hv', rfl⟩ := (mem_QE sel mu P).mp hP
      have : v' = v := HeightOneSpectrum.ext ((hsel v').symm.trans e)
      exact this ▸ hv'
  res := fun _ => rfl

end Sel

section Disj

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  (mu : Tup X.F X.E X.K S)

open Classical in

theorem QE_disj (hP : Pr.Ok) (hsel : IsSel X sel) (hS : ∀ i, Pr.g i ∈ S) (w : HeightOneSpectrum (𝓞 X.E))
    (hw : w ∈ Pr.vGs) : w ∉ QE sel (mu : Chr X.F X.E X.K) := by
  intro hQ
  obtain ⟨v, hv, rfl⟩ := (mem_QE sel mu w).mp hQ
  have hg : ∃ i, ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
    have key : ∀ i, sel v ∈ Pr.vG i → ((Pr.g i : ℕ) : 𝓞 X.E) ∈ (sel v).asIdeal := by
      intro i hi
      have h0 : X.conjO (Pr.piG i) ≠ 0 := by
        intro h0
        have := hP.piG_norm i
        rw [h0, mul_zero] at this
        exact (Nat.cast_ne_zero.mpr (hP.g_prime i).ne_zero) this.symm
      rw [← hP.piG_norm i]
      exact Ideal.mul_mem_left _ _ ((mem_divs h0 _).mp hi)
    rcases Finset.mem_union.mp hw with h | h
    · exact ⟨0, key 0 h⟩
    · exact ⟨1, key 1 h⟩
  obtain ⟨i, hi⟩ := hg
  have h1 : ((Pr.g i : ℕ) : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v]
    show algebraMap (𝓞 X.F) (𝓞 X.E) ((Pr.g i : ℕ) : 𝓞 X.F) ∈ (sel v).asIdeal
    rw [map_natCast]
    exact hi
  have h2 : plc v ∣ Pr.g i := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast] at h1
    exact (ringChar.spec _ _).mp h1
  have hpp : (plc v).Prime := by
    have : Finite (𝓞 X.F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
    have : v.asIdeal.IsPrime := v.isPrime
    exact CharP.char_is_prime (𝓞 X.F ⧸ v.asIdeal) (ringChar (𝓞 X.F ⧸ v.asIdeal))
  have h3 : plc v = Pr.g i := (Nat.prime_dvd_prime_iff_eq hpp (hP.g_prime i)).mp h2
  exact (mu.good hv).2.2 (h3 ▸ hS i)

end Disj

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.RowFormsSym
section
noncomputable section

open NumberField IsDedekindDomain

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section RBlockSym

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)

def rPsymF : LevFam X.E X.K R.r Pr.vGs := fun w =>
  ⟨HPsymF (𝓞 X.E ⧸ w.1.asIdeal) R.r R.k R.rS, chiSymF (Ch.psi0 w) R.r R.k R.rS⟩

theorem rowTyG_PsymF_H (w : {w // w ∈ Pr.vGs}) :
    (rowTyG Ch (rPsymF Ch) w).H = HJsym (𝓞 X.E ⧸ w.1.asIdeal) (R.N R.m - 1) R.k R.r R.t R.m R.rS (r_le_X' R) := rfl

end RBlockSym

end Formalism.L2.Col
end
end

