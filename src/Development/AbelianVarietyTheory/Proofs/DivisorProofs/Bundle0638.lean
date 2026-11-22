import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0614
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0619
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0620
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridInvarianceOfRankOneTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankCharacterEigenspaceInfKerLeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ArithmeticCylinders GlobalTheory.BadCount Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_characterEigenspace_inf_ker_le : ∀ (Γ V : Type) [Group Γ] [Fintype Γ] [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V) (Hb : Subgroup Γ) (lam : Hb →* ℂˣ) (H : Fin 2 → Subgroup Γ) (n : Fin 2 → ℕ) (e : MonoidAlgebra ℂ Γ) (b : Fin 2 → MonoidAlgebra ℂ Γ) (s : Fin 2 → ℝ) (c : ℝ), (∀ k, EmbReg ρ (H k) (n k)) → (∀ k, (n k : ℝ) * Nat.card (H k) ≤ c * Nat.card Hb * finrank ℂ (eig ρ Hb lam)) → (∀ k, b k * b k = b k) → (∀ k, b k * Formalism.L2.DIV.lvlIdem Hb lam = Formalism.L2.DIV.lvlIdem Hb lam * b k) → 1 - e = b 0 + b 1 - b 0 * b 1 → (∀ k g, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff g ≠ 0 → g ∈ H k) → (∀ k, (b k * Formalism.L2.DIV.lvlIdem Hb lam).coeff 1 = (s k : ℂ) / (Nat.card Hb : ℂ)) → (finrank ℂ (eig ρ Hb lam ⊓ LinearMap.ker (ρ.asAlgebraHom e) : Submodule ℂ V) : ℝ) ≤ c * (s 0 + s 1) * finrank ℂ (eig ρ Hb lam) := by
  first | exact @GlobalTheory.BadCount.finrank_eig_inf_ker_le | exact GlobalTheory.BadCount.finrank_eig_inf_ker_le | (intros; apply GlobalTheory.BadCount.finrank_eig_inf_ker_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatHensStatement
section
open IsLocalRing GlobalTheory.Henselisation
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_hens' : ∀ (R : Type) [CommRing R] [IsLocalRing R], Module.Flat R (Hens R) := by
  first | exact @GlobalTheory.Henselisation.flat_hens | exact GlobalTheory.Henselisation.flat_hens | (intros; apply GlobalTheory.Henselisation.flat_hens <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDetCharInvariantsLeSpanProdMaximalMinorsStatement
section
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockDetCharInvariants_le_span_prodMaximalMinors : ∀ {ι : Type} [Fintype ι] (a d : ℕ) (n : ι → ℕ), GlobalTheory.MinorFrame.inv a d n ≤ Submodule.span ℂ (Set.range (GlobalTheory.MinorFrame.prodMinors (ι := ι) (a := a) (d := d) (n := n))) := by
  first | exact @GlobalTheory.MinorFrame.inv_le_span_prodMinors | exact GlobalTheory.MinorFrame.inv_le_span_prodMinors | (intros; apply GlobalTheory.MinorFrame.inv_le_span_prodMinors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStable
section
noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MvPolynomial

namespace GlobalTheory.FockAlg.HarmStable

section General

variable {σ : Type}

def DegZero (K : Module.End ℂ (MvPolynomial σ ℂ)) : Prop :=
  ∀ (d : ℕ) (P : MvPolynomial σ ℂ), P ∈ homog σ d → K P ∈ homog σ d

theorem hc_hc (d e : ℕ) (P : MvPolynomial σ ℂ) :
    homogeneousComponent d (homogeneousComponent e P) =
      if d = e then homogeneousComponent e P else 0 :=
  homogeneousComponent_of_mem (homogeneousComponent_mem e P)

theorem DegZero.comm {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K) (d : ℕ)
    (P : MvPolynomial σ ℂ) : homogeneousComponent d (K P) = K (homogeneousComponent d P) := by
  rw [← sum_homogeneousComponent P]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [homogeneousComponent_of_mem (hK e _ (homogeneousComponent_mem e P)), hc_hc]
  split_ifs <;> simp

theorem minusPart_eq_zero_iff (A : Module.End ℂ (MvPolynomial σ ℂ)) (P : MvPolynomial σ ℂ) :
    minusPart A P = 0 ↔
      ∀ d, homogeneousComponent d (A (homogeneousComponent (d + 2) P)) = 0 := by
  constructor
  · intro h d
    have hfin : (Function.support fun e : ℕ =>
        homogeneousComponent e (A (homogeneousComponent (e + 2) P))) ⊆
        ((Finset.range (P.totalDegree + 1) ∪ {d} : Finset ℕ) : Set ℕ) := by
      intro e he
      by_contra hne
      apply he
      have : P.totalDegree < e + 2 := by
        simp only [Finset.coe_union, Finset.coe_range, Set.mem_union, Set.mem_Iio, not_or] at hne
        omega
      simp [homogeneousComponent_eq_zero _ _ this]
    rw [minusPart, finsum_eq_sum_of_support_subset _ hfin] at h
    have h2 := congrArg (homogeneousComponent d) h
    rw [map_sum, map_zero] at h2
    simp only [hc_hc] at h2
    rw [Finset.sum_ite_eq] at h2
    simpa using h2
  · intro h
    rw [minusPart]
    simp [h]

def lowKer {ι : Type} (A : ι → Module.End ℂ (MvPolynomial σ ℂ)) (c : ι → Prop) :
    Submodule ℂ (MvPolynomial σ ℂ) :=
  ⨅ Z, ⨅ (_ : c Z), ⨅ d : ℕ,
    LinearMap.ker (homogeneousComponent d ∘ₗ A Z ∘ₗ homogeneousComponent (d + 2))

theorem mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {P : MvPolynomial σ ℂ} : P ∈ lowKer A c ↔
      ∀ Z, c Z → ∀ d, homogeneousComponent d (A Z (homogeneousComponent (d + 2) P)) = 0 := by
  simp [lowKer, Submodule.mem_iInf]

theorem coe_lowKer {ι : Type} (A : ι → Module.End ℂ (MvPolynomial σ ℂ)) (c : ι → Prop) :
    (lowKer A c : Set (MvPolynomial σ ℂ)) = {P | ∀ Z, c Z → minusPart (A Z) P = 0} := by
  ext P
  simp only [SetLike.mem_coe, mem_lowKer, Set.mem_setOf_eq, minusPart_eq_zero_iff]

theorem hc_mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowKer A c) (e : ℕ) :
    homogeneousComponent e P ∈ lowKer A c := by
  rw [mem_lowKer] at hP ⊢
  intro Z hZ d
  rw [hc_hc]
  split_ifs with h
  · rw [← h]; exact hP Z hZ d
  · simp

theorem map_mem_lowKer {ι : Type} {A : ι → Module.End ℂ (MvPolynomial σ ℂ)} {c : ι → Prop}
    {K : Module.End ℂ (MvPolynomial σ ℂ)} (hK : DegZero K)
    (hc : ∀ Z, c Z → A Z * K = K * A Z ∨ ∃ Z', c Z' ∧ A Z' = A Z * K - K * A Z)
    {P : MvPolynomial σ ℂ} (hP : P ∈ lowKer A c) : K P ∈ lowKer A c := by
  rw [mem_lowKer] at hP ⊢
  intro Z hZ d
  rw [hK.comm, ← Module.End.mul_apply (A Z) K]
  rcases hc Z hZ with h | ⟨Z', hZ', h⟩
  · rw [h, Module.End.mul_apply, hK.comm, hP Z hZ d, map_zero]
  · rw [← sub_add_cancel (A Z * K) (K * A Z), ← h, LinearMap.add_apply, map_add, hP Z' hZ' d,
      Module.End.mul_apply, hK.comm, hP Z hZ d, map_zero, add_zero]

theorem X_mul_pderiv_mem (u v : σ) {d : ℕ} {P : MvPolynomial σ ℂ} (hP : P ∈ homog σ d) :
    X u * pderiv v P ∈ homog σ d := by
  rcases d with _ | d
  · rw [totalDegree_eq_zero_iff_eq_C.1 ((totalDegree_zero_iff_isHomogeneous _).2 hP), pderiv_C,
      mul_zero]
    exact Submodule.zero_mem _
  · have := (isHomogeneous_X ℂ u).mul (IsHomogeneous.pderiv (i := v) hP)
    rwa [Nat.add_sub_cancel, add_comm] at this

theorem pderiv_X_mul_mem (u v : σ) {d : ℕ} {P : MvPolynomial σ ℂ} (hP : P ∈ homog σ d) :
    pderiv v (X u * P) ∈ homog σ d := by
  have := IsHomogeneous.pderiv (i := v) ((isHomogeneous_X ℂ u).mul hP)
  rwa [Nat.add_sub_cancel_left] at this

end General

variable {p q r s : ℕ}

theorem degZero_omE {l l' : Ln p q r s} (h : linePos l = linePos l') : DegZero (omE l l') := by
  intro d P hP
  rw [omE, LinearMap.add_apply]
  refine Submodule.add_mem _ ?_ ?_
  · rw [raiB, lowB, ← h]
    split_ifs
    · exact X_mul_pderiv_mem l l' hP
    · exact Submodule.neg_mem _ (pderiv_X_mul_mem l' l hP)
  · split_ifs
    · exact Submodule.smul_mem _ _ hP
    · exact Submodule.zero_mem _

theorem degZero_omAct {M : Matrix (Ln p q r s) (Ln p q r s) ℂ}
    (h : ∀ l l', linePos l ≠ linePos l' → M l l' = 0) : DegZero (omAct p q r s M) := by
  intro d P hP
  rw [omAct_apply, LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [LinearMap.sum_apply]
  refine Submodule.sum_mem _ fun l' _ => ?_
  by_cases hl : linePos l = linePos l'
  · exact Submodule.smul_mem _ _ (degZero_omE hl d P hP)
  · rw [h l l' hl, zero_smul]; exact Submodule.zero_mem _

theorem degZero_fockAct1 {Y : Mat p q} (hY : IsKC Y) : DegZero (fockAct1 p q r s Y) := by
  refine degZero_omAct ?_
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  show Y a b * (1 : Mat r s) c e = 0
  by_cases hce : c = e
  · subst hce
    rw [hY a b, zero_mul]
    revert h
    rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;>
      simp [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hce, mul_zero]

theorem degZero_fockAct2 {Y : Mat r s} (hY : IsKC Y) : DegZero (fockAct2 p q r s Y) := by
  refine degZero_omAct ?_
  rintro ⟨a, c⟩ ⟨b, e⟩ h
  show (1 : Mat p q) a b * Y c e = 0
  by_cases hab : a = b
  · subst hab
    rw [hY c e, mul_zero]
    revert h
    rcases a with a | a <;> rcases e with e | e <;> rcases c with c | c <;>
      simp [linePos, sameBlock]
  · rw [Matrix.one_apply_ne hab, zero_mul]

theorem isPC_bracket {Y Z : Mat p q} (hY : IsKC Y) (hZ : IsPC Z) : IsPC (Z * Y - Y * Z) := by
  intro a b hab
  have h1 : (Z * Y) a b = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : sameBlock a c
    · rw [hZ a c hc, zero_mul]
    · rw [hY c b, mul_zero]
      revert hab hc
      rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp [sameBlock]
  have h2 : (Y * Z) a b = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hc : sameBlock a c
    · rw [hZ c b, mul_zero]
      revert hab hc
      rcases a with a | a <;> rcases b with b | b <;> rcases c with c | c <;> simp [sameBlock]
    · rw [hY a c hc, zero_mul]
  rw [Matrix.sub_apply, h1, h2, sub_zero]

def sub1 (p q r s : ℕ) : Submodule ℂ (Pol p q r s) :=
  lowKer (fun Z : Mat r s => fockAct2 p q r s Z) IsPC

def sub2 (p q r s : ℕ) : Submodule ℂ (Pol p q r s) :=
  lowKer (fun Z : Mat p q => fockAct1 p q r s Z) IsPC

theorem coe_fockHarmonicsFirstMemberSubspace : (sub1 p q r s : Set (Pol p q r s)) = harm1 p q r s := coe_lowKer _ _

theorem coe_fockHarmonicsSecondMemberSubmodule : (sub2 p q r s : Set (Pol p q r s)) = harm2 p q r s := coe_lowKer _ _

theorem fockHarmonicsFirstMember_kStable : KStable (fockAct1 p q r s) (sub1 p q r s) ∧
    KStable (fockAct2 p q r s) (sub1 p q r s) := by
  obtain ⟨-, -, h2, h3⟩ := GlobalTheory.T.fockOperators_lie_representation_commute p q r s
  exact ⟨fun Y hY _ hw => map_mem_lowKer (degZero_fockAct1 hY)
      (fun Z _ => Or.inl (h3 Y Z).symm) hw,
    fun Y hY _ hw => map_mem_lowKer (degZero_fockAct2 hY)
      (fun Z hZ => Or.inr ⟨_, isPC_bracket hY hZ, h2 Z Y⟩) hw⟩

theorem fockHarmonicsSecondMember_kStable : KStable (fockAct1 p q r s) (sub2 p q r s) ∧
    KStable (fockAct2 p q r s) (sub2 p q r s) := by
  obtain ⟨-, h1, -, h3⟩ := GlobalTheory.T.fockOperators_lie_representation_commute p q r s
  exact ⟨fun Y hY _ hw => map_mem_lowKer (degZero_fockAct1 hY)
      (fun Z hZ => Or.inr ⟨_, isPC_bracket hY hZ, h1 Z Y⟩) hw,
    fun Y hY _ hw => map_mem_lowKer (degZero_fockAct2 hY)
      (fun Z _ => Or.inl (h3 Z Y)) hw⟩

end GlobalTheory.FockAlg.HarmStable

namespace GlobalTheory.FockAlg

open HarmStable

theorem harm_graded_stable : ∀ (p q r s : ℕ) (S : Set (Pol p q r s)),
    (S = harm1 p q r s ∨ S = harm2 p q r s ∨ S = jointHarm p q r s) →
    (Submodule.span ℂ S : Set (Pol p q r s)) = S ∧
      KStable (fockAct1 p q r s) (Submodule.span ℂ S) ∧
      KStable (fockAct2 p q r s) (Submodule.span ℂ S) ∧
      ∀ P ∈ S, ∀ d : ℕ, homogeneousComponent d P ∈ S := by
  intro p q r s S hS
  rcases hS with rfl | rfl | rfl
  · rw [← coe_fockHarmonicsFirstMemberSubspace, Submodule.span_eq]
    exact ⟨rfl, fockHarmonicsFirstMember_kStable.1, fockHarmonicsFirstMember_kStable.2, fun P hP d => hc_mem_lowKer hP d⟩
  · rw [← coe_fockHarmonicsSecondMemberSubmodule, Submodule.span_eq]
    exact ⟨rfl, fockHarmonicsSecondMember_kStable.1, fockHarmonicsSecondMember_kStable.2, fun P hP d => hc_mem_lowKer hP d⟩
  · rw [jointHarm, ← coe_fockHarmonicsFirstMemberSubspace, ← coe_fockHarmonicsSecondMemberSubmodule, ← Submodule.coe_inf, Submodule.span_eq]
    exact ⟨rfl,
      fun Y hY w hw => ⟨fockHarmonicsSecondMember_kStable.1 Y hY w hw.1, fockHarmonicsFirstMember_kStable.1 Y hY w hw.2⟩,
      fun Y hY w hw => ⟨fockHarmonicsSecondMember_kStable.2 Y hY w hw.1, fockHarmonicsFirstMember_kStable.2 Y hY w hw.2⟩,
      fun P hP d => ⟨hc_mem_lowKer hP.1 d, hc_mem_lowKer hP.2 d⟩⟩

end GlobalTheory.FockAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawLinearCoeffAdditive
section
set_option autoImplicit false

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory.Katz.LowLaw

theorem eq_single_of_degree_eq_one {σ : Type} {e : σ →₀ ℕ} (h : e.degree = 1) :
    ∃ j, e = Finsupp.single j 1 := by
  classical
  have hne : e ≠ 0 := by rintro rfl; simp at h
  obtain ⟨j, hj⟩ := Finsupp.support_nonempty_iff.mpr hne
  have hle : Finsupp.single j 1 ≤ e := by
    rw [Finsupp.single_le_iff]; exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hj)
  refine ⟨j, ?_⟩
  have hsum : e = (e - Finsupp.single j 1) + Finsupp.single j 1 := (tsub_add_cancel_of_le hle).symm
  have hd : (e - Finsupp.single j 1).degree = 0 := by
    have h2 := congrArg Finsupp.degree hsum
    rw [map_add, Finsupp.degree_single, h] at h2
    omega
  rw [Finsupp.degree_eq_zero_iff] at hd
  rw [hsum, hd, zero_add]

theorem coeff_addLaw (R : Type) [CommRing R] (d : ℕ) (i : Fin d) (α : Fin d ⊕ Fin d →₀ ℕ) :
    coeff α (addLaw R d i) =
      if α = Finsupp.single (Sum.inl i) 1 ∨ α = Finsupp.single (Sum.inr i) 1 then 1 else 0 := by
  classical
  simp only [addLaw, map_add, coeff_X]
  by_cases h1 : α = Finsupp.single (Sum.inl i) 1
  · have h2 : α ≠ Finsupp.single (Sum.inr i) 1 := by
      rw [h1]; intro h
      exact Sum.inl_ne_inr ((Finsupp.single_left_inj one_ne_zero).1 h)
    rw [if_pos h1, if_neg h2, if_pos (Or.inl h1), add_zero]
  · rw [if_neg h1, zero_add]
    by_cases h2 : α = Finsupp.single (Sum.inr i) 1
    · rw [if_pos h2, if_pos (Or.inr h2)]
    · rw [if_neg h2, if_neg (by tauto)]

variable {k : Type} [CommRing k] {d : ℕ}

theorem coeff_inl {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inl j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have hu := congrArg (coeff (Finsupp.single j 1)) (congrFun h.unit i)
  simp only [op, at2] at hu
  rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hu
  simpa [coeff_X, Finsupp.single_left_inj] using hu

theorem coeff_inr {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k} (h : IsLaw μ) (i j : Fin d) :
    coeff (Finsupp.single (Sum.inr j) 1) (μ i) = if j = i then 1 else 0 := by
  classical
  have hc := congrArg (coeff (Finsupp.single (Sum.inr j) 1)) (h.comm i)
  simp only [swap, at2] at hc
  rw [GlobalTheory.FormalCalc.coeff_single_subst (fun s => by cases s <;> simp), Fintype.sum_sum_type] at hc
  rw [← hc, ← coeff_inl h i j]
  simp [coeff_X, Finsupp.single_left_inj]

end GlobalTheory.Katz.LowLaw

namespace GlobalTheory.Katz

open LowLaw in

theorem coeff_law_of_degree_le_one (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p]
    [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) (h : IsLaw μ)
    (i : Fin d) (α : Fin d ⊕ Fin d →₀ ℕ) (hα : α.degree ≤ 1) :
    coeff α (μ i) = coeff α (addLaw k d i) ∧
      coeff α (Katz.lift p (μ i)) = coeff α (addLaw (Fr p k) d i) := by
  classical
  have h1 : coeff α (μ i) = coeff α (addLaw k d i) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hα with h0 | h1
    · rw [(Finsupp.degree_eq_zero_iff α).1 h0, coeff_zero_eq_constantCoeff_apply, h.const,
        coeff_addLaw, if_neg]
      rintro (h | h) <;> exact Finsupp.single_ne_zero.2 one_ne_zero h.symm
    · obtain ⟨s, rfl⟩ := eq_single_of_degree_eq_one h1
      rcases s with j | j
      · rw [coeff_inl h, coeff_addLaw]; simp [Finsupp.single_left_inj]
      · rw [coeff_inr h, coeff_addLaw]; simp [Finsupp.single_left_inj]
  refine ⟨h1, ?_⟩
  rw [coeff_lift, h1, coeff_addLaw, coeff_addLaw]
  split_ifs <;> simp

end GlobalTheory.Katz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedAdjointRingActionSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyUnramified_adjointRingAction_scheme : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left) (O : Type) [Ring O] (bar : O → O) (R : ActRep A Q bar), IsAbelianScheme A → FormallyUnramified R.π := by
  first | exact @GlobalTheory.EndLoc.formallyUnramified_actRep | exact GlobalTheory.EndLoc.formallyUnramified_actRep | (intros; apply GlobalTheory.EndLoc.formallyUnramified_actRep; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedHomWithFixedPullbackSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyUnramified_homWithFixedPullback_scheme : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B → FormallyUnramified R.π := by
  first | exact @GlobalTheory.EndLoc.formallyUnramified_homFixRep | exact GlobalTheory.EndLoc.formallyUnramified_homFixRep | (intros; apply GlobalTheory.EndLoc.formallyUnramified_homFixRep; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionRingAwayEtaleDedekindArtinianReducedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fractionRing_away_etale_dedekind_artinian_reduced : ∀ (B : Type) [CommRing B] [IsDedekindDomain B] (f : B) (A' : Type) [CommRing A'] [Algebra B A'] [Algebra.Etale B A'], IsArtinianRing (FractionRing (Localization.Away (algebraMap B A' f))) ∧ IsReduced (FractionRing (Localization.Away (algebraMap B A' f))) := by
  first | (exact @GlobalTheory.fractionRing_away_etale_isArtinian_isReduced) | (exact GlobalTheory.fractionRing_away_etale_isArtinian_isReduced) | (intros; apply GlobalTheory.fractionRing_away_etale_isArtinian_isReduced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFibreMulKTorsorHarrisTaylor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.Hecke.FibreMulK

private theorem ev_nsmul' {p : ℕ} [Fact p.Prime] {D : Datum p} {k : Type} [Field k] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : TateIsoO D k Q act e) (n j : ℕ) (y : D.La) :
    I.ev n (j • y) = I.ev n y ^ j := by
  induction j with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    rw [zero_smul, _root_.pow_zero]
    exact mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)
  | succ j ih => rw [succ_nsmul, I.add, ih, _root_.pow_succ]

private theorem nsmul_cancel {M : Type} [AddCommGroup M] [Module.Free ℤ M] {k : ℕ} (hk : 0 < k) {x y : M}
    (h : k • x = k • y) : x = y := by
  have hk' : (k : ℤ) ≠ 0 := by exact_mod_cast hk.ne'
  apply smul_right_injective M hk'
  simpa only [natCast_zsmul] using h

theorem fibre_mulK : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (k N : ℕ), 0 < k → 0 < N → k.Coprime p → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k * k) s) (K : Type) [Field K] [IsAlgClosed K] (y y' : Sp K ⟶ o.A.left), y ≫ ((𝟙 o.A) ^ k).left = y' ≫ ((𝟙 o.A) ^ k).left → ∃! a : GlobalTheory.UPel.HT.Hecke.heckeSub o LinearMap.id (N * k), y ≫ (GlobalTheory.UPel.HT.Hecke.transl a.1).left = y' := by
  intro p _ D R _ b k N hk hN hkp hNp S s o K _ _ y y' hyy
  set x : Sp K ⟶ S := y ≫ o.A.hom with hx
  have hx' : y' ≫ o.A.hom = x := by
    have e := congrArg (· ≫ o.A.hom) hyy
    simp only [Category.assoc, Over.w] at e
    exact e.symm
  let T : Over S := Over.mk x
  let yt : T ⟶ o.A := Over.homMk y rfl
  let yt' : T ⟶ o.A := Over.homMk y' hx'
  have hpow : yt ^ k = yt' ^ k := by
    have e : yt ≫ (𝟙 o.A) ^ k = yt' ≫ (𝟙 o.A) ^ k := Over.OverMorphism.ext hyy
    rwa [comp_pow, comp_pow, Category.comp_id, Category.comp_id] at e
  set d : T ⟶ o.A := yt⁻¹ * yt' with hd
  have hdk : d ^ k = 1 := by rw [hd, mul_pow, inv_pow, hpow, inv_mul_cancel]
  have hβ : x ≫ s = spMap (Spec.preimage (x ≫ s)).hom := (Spec.map_preimage _).symm
  obtain ⟨I, hI⟩ := o.geom K x _ hβ
  have hcop : (N * k * k).Coprime p := Nat.Coprime.mul (Nat.Coprime.mul hNp hkp) hkp
  have hpos : 0 < N * k * k := Nat.mul_pos (Nat.mul_pos hN hk) hk
  obtain ⟨z, hz⟩ := (I.onto (N * k * k) hpos hcop d).1 (by
    rw [pow_mul, pow_right_comm, hdk, one_pow])
  have hkz : I.ev (N * k * k) (k • z) = 1 := by rw [ev_nsmul', hz, hdk]
  obtain ⟨w, hw⟩ := (I.ker (N * k * k) hpos hcop _).1 hkz
  haveI := D.freeLa
  have hzw : z = (N * k) • w := by
    apply nsmul_cancel hk
    rw [hw, smul_smul, show k * (N * k) = N * k * k by ring]
  have key : ∀ a : heckeSub o LinearMap.id (N * k), y ≫ (transl a.1).left = y' ↔ toUnit T ≫ a.1 = d := by
    intro a
    have e1 : yt ≫ transl a.1 = yt * (toUnit T ≫ a.1) := by
      rw [transl, comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (yt ≫ toUnit o.A) (toUnit T)]
    constructor
    · intro h
      have e2 : yt ≫ transl a.1 = yt' := Over.OverMorphism.ext h
      rw [e1] at e2
      rw [hd, ← e2, inv_mul_cancel_left]
    · intro h
      have e2 : yt ≫ transl a.1 = yt' := by rw [e1, h, hd, mul_inv_cancel_left]
      exact congrArg CommaMorphism.left e2
  have hmem : o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) ∈ heckeSub o LinearMap.id (N * k) :=
    mem_heckeSub o _ _ w
  refine ⟨⟨_, hmem⟩, (key _).2 ?_, ?_⟩
  · show toUnit T ≫ o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) = d
    rw [LinearMap.id_apply, hI, ← hzw, hz]
  · intro a ha
    have h1 : toUnit T ≫ a.1 = d := (key a).1 ha
    have h2 : toUnit T ≫ o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w) = d := by
      rw [LinearMap.id_apply, hI, ← hzw, hz]
    have hm : a.1 * (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹ ∈ heckeSub o LinearMap.id (N * k) :=
      Subgroup.mul_mem _ a.2 (Subgroup.inv_mem _ hmem)
    have h3 : toUnit T ≫ (a.1 * (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹) = 1 := by
      have hi : toUnit T ≫ (o.eta ((N * k) • (LinearMap.id : D.La →ₗ[D.O] D.La) w))⁻¹ = d⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← h2, ← comp_mul, inv_mul_cancel, comp_one]
      rw [comp_mul, h1, hi, mul_inv_cancel]
    have h4 := (heckeSub_finite_free p D R b LinearMap.id k (N * k) hk (Nat.mul_pos hN hk) hkp
      (Nat.Coprime.mul hNp hkp) S s o).2 K x _ hm h3
    exact Subtype.ext (mul_inv_eq_one.mp h4)

end GlobalTheory.UPel.HT.Hecke.FibreMulK
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalFunctionsConstantAfterBaseChangeOfAbelianSStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalFunctionsConstantAfterBaseChange_of_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → UConst A.hom := by
  first | exact @GlobalTheory.AbCoh.uConst_of_isAbelianScheme | exact GlobalTheory.AbCoh.uConst_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.uConst_of_isAbelianScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalOneFormFrameCoordinatesConstantStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.globalOneFormFrame_coordinates_constant : ∀ (R : Type) [CommRing R] (C : Type) [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R), CohomZeroIsConstants F → ∀ (n : ℕ) (Φ : Frame F n), ∃ l : Fin n → (Glob1 F →ₗ[R] R), (∀ i (w : Glob1 F) T, Φ.δ i T (w.1 T) = algebraMap R (F.obj T) (l i w)) ∧ ∀ w, w = ∑ i, l i w • Φ.w i := by
  first | exact @GlobalTheory.AbCoh.frame_coord | exact GlobalTheory.AbCoh.frame_coord | (intros; apply GlobalTheory.AbCoh.frame_coord <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GridInvarianceOfRankOneTwoStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grid_invariance_of_rank_one_two : GlobalTheory.LeviCut.RankOne → GlobalTheory.LeviCut.RankTwo → GlobalTheory.LeviCut.GridInv := by
  first | exact @GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo | exact GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo | (intros; apply GlobalTheory.LeviCut.gridInv_of_rankOne_rankTwo <;> assumption)
end

