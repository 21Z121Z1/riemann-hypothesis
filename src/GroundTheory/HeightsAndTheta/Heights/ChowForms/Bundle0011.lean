import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.StatementsChartMax
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LowerBoundConditional
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PComponentOfIncIdeal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace ComponentOfIncIdeal

theorem ringKrullDim_quot_add_one_le {A : Type} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (hPQ : P ≤ Q) (hne : P ≠ Q) : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ P) := by
  obtain ⟨x, hxQ, hxP⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hPQ hne)
  have hne' : Q.map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro h0
    have hx : Ideal.Quotient.mk P x ∈ Q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hxQ
    rw [h0, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hx
    exact hxP hx
  have h := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le _ hne'
  rwa [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ)] at h

theorem one_le_ringKrullDim_quot {F : Type} [Field F] {n : ℕ} {W : Ideal (MvPolynomial (Fin n) F)}
    (hW : IsProjPrime W) : (1 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ W) := by
  have hWp := hW.isPrime
  set m : Ideal (MvPolynomial (Fin n) F) := RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F)
  have hmp : m.IsPrime := RingHom.ker_isPrime _
  have hle : W ≤ m := by
    intro f hf
    rw [RingHom.mem_ker]
    by_contra h
    have h0 := hW.isHomog f hf 0
    rw [homogeneousComponent_zero] at h0
    have hc : coeff 0 f ≠ 0 := by rwa [← constantCoeff_eq]
    exact hWp.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit hc).map C))
  have hne : W ≠ m := by
    obtain ⟨j, hj⟩ := hW.isRelevant
    intro h
    exact hj (h ▸ (by simp [m] : (X j : MvPolynomial (Fin n) F) ∈ m))
  have h := ringKrullDim_quot_add_one_le hle hne
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin n) F ⧸ m) :=
    ringKrullDim_nonneg_of_nontrivial
  exact (le_add_of_nonneg_left h0).trans h

theorem exists_nat_of_bounds {x : WithBot ℕ∞} {e : ℕ} (h1 : 1 ≤ x) (h2 : x + 1 ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ k : ℕ, x = (k : WithBot ℕ∞) ∧ 1 ≤ k ∧ k ≤ e := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h1 (by simp)
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      have h3 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
        le_trans (le_add_of_nonneg_right zero_le_one) h2
      have h4 : (⊤ : ℕ∞) ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast h3
      exact absurd h4 (by simp)
    | coe k =>
      refine ⟨k, rfl, ?_, ?_⟩
      · exact_mod_cast h1
      · have : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h2
        have : k + 1 ≤ e + 1 := by exact_mod_cast this
        omega

end ComponentOfIncIdeal

open ComponentOfIncIdeal in

theorem ComponentOfIncIdeal.proof (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement)
    (h₃ : ConeDimComponent.Statement) : ComponentOfIncIdeal.Statement := by
  intro F _ n e I W u q hI hdim hu hW hle hq hinc
  have hWp := hW.isPrime
  have := hI.isPrime

  have hIW : I ≤ W := le_sup_left.trans hle
  have huW : linForm u ∈ W := hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  have hIneW : I ≠ W := fun h => hu (h ▸ huW)
  have hup := ringKrullDim_quot_add_one_le hIW hIneW
  rw [hdim] at hup
  obtain ⟨k, hk, hk1, hke⟩ := exists_nat_of_bounds (one_le_ringKrullDim_quot hW) hup

  have hdimInc := h₁ F n e (k - 1) W hW (by rw [hk]; congr 2; omega)
  have hincp : (incIdeal W e).IsPrime := h₂ F n e W hWp hW.isRelevant
  have hS : ringKrullDim (MvPolynomial (Fin e × Fin n) F) = ((e * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_isField (Field.toIsField F)]
    simp [Nat.card_eq_fintype_card]
  have hsum := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F (incIdeal W e)
  rw [hdimInc, hS] at hsum
  have hqle : (Ideal.span {q}).height ≤ 1 := Ideal.height_span_singleton_le_one hq.not_isUnit
  have hht : (incIdeal W e).height ≤ 1 := (Ideal.height_mono hinc).trans hqle
  obtain ⟨h, hh⟩ : ∃ h : ℕ, (incIdeal W e).height = h :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (by simp) hht) |>.imp fun _ h => h.symm
  rw [hh] at hsum hht
  have hh1 : h ≤ 1 := by exact_mod_cast hht
  have hnat : h + (e * n - e + min e (k - 1)) = e * n := by
    have h5 : (((h + (e * n - e + min e (k - 1)) : ℕ) : ℕ∞) : WithBot ℕ∞) = (((e * n : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      rw [Nat.cast_add, WithBot.coe_add]
      exact hsum
    exact_mod_cast WithBot.coe_inj.mp h5
  have hn : 1 ≤ n := by
    obtain ⟨j, _⟩ := hW.isRelevant
    exact Nat.one_le_iff_ne_zero.mpr fun h0 => (h0 ▸ j).elim0
  have hen : e ≤ e * n := Nat.le_mul_of_pos_right e hn
  have hmin : min e (k - 1) = k - 1 := min_eq_right (by omega)
  rw [hmin] at hnat
  generalize e * n = N at hnat hen
  have hke' : k = e := by omega
  have hh' : h = 1 := by omega
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨W'', hmin'', hW''⟩ := Ideal.exists_minimalPrimes_le hle
    have hrel : IsRelevant W'' := by
      obtain ⟨j, hj⟩ := hW.isRelevant
      exact ⟨j, fun hj'' => hj (hW'' hj'')⟩
    have hdim'' := (h₃ F n e I W'' u hI hdim hu ⟨hmin'', hrel⟩).2
    by_cases heq : W'' = W
    · exact heq ▸ ⟨hmin'', hrel⟩
    · have := hmin''.1.1
      have hlt := ringKrullDim_quot_add_one_le hW'' heq
      rw [hdim'', hk, hke'] at hlt
      have : e + 1 ≤ e := by exact_mod_cast hlt
      omega
  ·
    by_contra hne
    have : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    have : (Ideal.span {q}).FiniteHeight :=
      (Ideal.span {q}).finiteHeight_iff.mpr (Or.inr (ne_top_of_le_ne_top (by simp) hqle))
    have hlt := Ideal.height_strict_mono_of_isPrime_of_isPrime (lt_of_le_of_ne hinc hne)
    rw [hh, hh'] at hlt
    exact absurd (hlt.trans_le hqle) (lt_irrefl _)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

theorem ConeDimComponent.proof_closed : ConeDimComponent.Statement := by
  intro F _ n e I W u hI hdim hu hW
  obtain ⟨hmin, hrel⟩ := hW
  have hWprime : W.IsPrime := hmin.1.1

  have hJ : IsHomogIdeal (I ⊔ Ideal.span {linForm u}) := isHomogIdeal_sup_span_linForm hI.isHomog u
  have hproj : IsProjPrime W := by
    classical
    have hJh := (isHomogIdeal_iff _).mp hJ
    refine ⟨hWprime, (isHomogIdeal_iff W).mpr ?_, hrel⟩
    set core := (W.homogeneousCore (homogeneousSubmodule (Fin n) F)).toIdeal
    have hcore_prime : core.IsPrime := hWprime.homogeneousCore
    have hJcore : I ⊔ Ideal.span {linForm u} ≤ core := by
      rw [← hJh.toIdeal_homogeneousCore_eq_self]
      exact Ideal.homogeneousCore_mono _ hmin.1.2
    have hle : core ≤ W := Ideal.toIdeal_homogeneousCore_le _ _
    have heq : core = W := le_antisymm hle (hmin.2 ⟨hcore_prime, hJcore⟩ hle)
    rw [Ideal.IsHomogeneous.iff_eq]
    exact heq
  refine ⟨hproj, ?_⟩

  have hIprime : I.IsPrime := hI.isPrime
  have hIW : I ≤ W := le_sup_left.trans hmin.1.2
  have huW : linForm u ∈ W := (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
  set B := MvPolynomial (Fin n) F ⧸ I
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F I)
      (Ideal.Quotient.mkₐ_surjective F I)
  set W' : Ideal B := W.map (Ideal.Quotient.mk I)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hu
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk I (linForm u) ∈ W' := Ideal.mem_map_of_mem _ huW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MvPolynomial (Fin n) F ⧸ W) = y := by
    cases h : ringKrullDim (MvPolynomial (Fin n) F ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) F ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ e := by
    have : y + 1 ≤ (e : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, (m : ℕ∞) = y := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top
    (ENat.natCast_ne_top e) hyle)
  have h3 : ((e + 1 : ℕ) : ℕ∞) ≤ 1 + m := by rw [← h2]; gcongr
  have h4 : e + 1 ≤ 1 + m := by exact_mod_cast h3
  have h5 : m ≤ e := by exact_mod_cast hyle
  have : m = e := by omega
  subst this
  rfl

theorem ConeDimComponent.proof (_h₁ : MinimalPrimeHomog.Statement) : ConeDimComponent.Statement :=
  ConeDimComponent.proof_closed

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimOfChowForm
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IsChowForm.incIdeal_eq_span {F : Type*} [Field F] {n k : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} {f : MvPolynomial (Fin k × Fin n) F}
    (hf : IsChowForm P k f) : incIdeal P k = Ideal.span {f} := by
  ext g
  rw [Ideal.mem_span_singleton, ← hf.2 g]
  simp only [incIdeal, Ideal.mem_iInf, RingHom.mem_ker]

theorem constantCoeff_eq_zero_of_isHomogIdeal {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsHomogIdeal P) (htop : P ≠ ⊤)
    {g : MvPolynomial (Fin n) F} (hg : g ∈ P) : constantCoeff g = 0 := by
  by_contra h
  have h0 := hP g hg 0
  rw [homogeneousComponent_zero, ← constantCoeff_eq] at h0
  exact htop (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))

theorem IsProjPrime.not_isField_quotient {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) :
    ¬ IsField (MvPolynomial (Fin n) F ⧸ P) := by
  intro hfield
  obtain ⟨j, hj⟩ := hP.isRelevant
  have hx : Ideal.Quotient.mk P (X j) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨y, hy⟩ := hfield.mul_inv_cancel hx
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, ← map_one (Ideal.Quotient.mk P), Ideal.Quotient.eq] at hy
  have := constantCoeff_eq_zero_of_isHomogIdeal hP.isHomog hP.isPrime.ne_top hy
  simp at this

theorem ConeDimOfChowForm.proof (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement) :
    ConeDimOfChowForm.Statement := by
  intro F _ n k P f hP hf
  have hspan := hf.incIdeal_eq_span
  have hprime : (Ideal.span {f}).IsPrime := hspan ▸ h₂ F n k P hP.isPrime hP.isRelevant
  have hnu : ¬ IsUnit f := fun hu => hprime.ne_top (Ideal.span_singleton_eq_top.mpr hu)
  have hht : (Ideal.span {f}).height = 1 :=
    Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hf.1) hnu
  have hdimS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field, zero_add,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F (Ideal.span {f})
  rw [hht, hdimS] at hform
  have := hP.isPrime
  obtain ⟨m, hm, -⟩ :=
    GroundTheory.Arith.Abelian.Jacobian.exists_ringKrullDim_eq_trdeg (k := F) (A := MvPolynomial (Fin n) F ⧸ P)
  cases m with
  | zero =>
    exfalso
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) F ⧸ P) := Ring.krullDimLE_iff.mpr (by rw [hm])
    exact hP.not_isField_quotient Ring.KrullDimLE.isField_of_isDomain
  | succ d =>
    have h := h₁ F n k d P hP hm
    rw [hspan] at h
    rw [h] at hform
    have h3 : ((1 + (k * n - k + min k d) : ℕ) : WithBot ℕ∞) = ((k * n : ℕ) : WithBot ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_one]
      convert hform using 2
      exact WithBot.coe_one.symm
    replace h3 := Nat.cast_injective h3
    rw [hm]
    congr 1
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      omega
    · have hkn := Nat.le_mul_of_pos_right k hn
      generalize k * n = N at h3 hkn
      omega

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PIncIdealDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem IncIdealDim.proof (h₁ : IncidenceGeneric.Statement) (h₂ : GenericLinearTrdeg.Statement)
    (h₃ : AffineChartTrdeg.Statement) : IncIdealDim.Statement := by
  intro F _ n k d P hP hdim
  have := hP.isPrime
  obtain ⟨j, hj⟩ := hP.isRelevant
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := j.pos; omega⟩
  set K := FractionRing (MvPolynomial (Fin (n' + 1)) F ⧸ P)
  set ξ := genPt P
  have hξj : ξ j ≠ 0 := by
    simp only [ξ, genPt]
    rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
    exact hj
  set c : Fin (n' + 1) → K := fun m => if m = j then (ξ j)⁻¹ else 0 with hc_def
  have hc : ∑ m, c m * ξ m = 1 := by
    simp [c, inv_mul_cancel₀ hξj]

  let τ : Fin k × Fin n' → Fin k × Fin (n' + 1) := fun im => (im.1, j.succAbove im.2)
  have hτ : Function.Injective τ := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ h
    simp only [τ, Prod.mk.injEq] at h
    exact Prod.ext h.1 (j.succAbove_right_injective h.2)
  let ψ : MvPolynomial (Fin k × Fin n') K →ₐ[F] MvPolynomial (Fin k × Fin (n' + 1)) K :=
    (rename τ).restrictScalars F
  have hψ : Function.Injective ψ := rename_injective τ hτ
  let η : Fin n' → K := fun m => -(ξ (j.succAbove m) * (ξ j)⁻¹)
  let G : Set (MvPolynomial (Fin k × Fin n') K) :=
    Set.range (fun ij => X ij) ∪ Set.range (fun i : Fin k => ∑ m, X (i, m) * C (η m))

  have hA : ∀ i m, genSubst ξ c (i, j.succAbove m) = ψ (X (i, m)) := by
    intro i m
    simp [ψ, τ, genSubst, c, Fin.succAbove_ne]
  have hB : ∀ i, genSubst ξ c (i, j) = ψ (∑ m, X (i, m) * C (η m)) := by
    intro i
    have h1 : (C (ξ j) * C (ξ j)⁻¹ : MvPolynomial (Fin k × Fin (n' + 1)) K) = 1 := by
      rw [← map_mul, mul_inv_cancel₀ hξj, map_one]
    have h2 : ψ (∑ m, X (i, m) * C (η m)) =
        -((∑ m, X (i, j.succAbove m) * C (ξ (j.succAbove m))) * C (ξ j)⁻¹) := by
      simp only [ψ, AlgHom.restrictScalars_apply, map_sum, map_mul, rename_X, rename_C, τ]
      rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [C_neg, C_mul]
      ring
    rw [h2]
    simp only [genSubst, c, if_pos rfl]
    rw [Fin.sum_univ_succAbove _ j]
    linear_combination (-(X (i, j) : MvPolynomial (Fin k × Fin (n' + 1)) K)) * h1
  have hrange : Set.range (genSubst ξ c) = ψ '' G := by
    ext p
    constructor
    · rintro ⟨⟨i, m⟩, rfl⟩
      by_cases hm : m = j
      · rw [hm]
        exact ⟨_, Or.inr ⟨i, rfl⟩, (hB i).symm⟩
      · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hm
        exact ⟨_, Or.inl ⟨(i, m'), rfl⟩, (hA i m').symm⟩
    · rintro ⟨q, (⟨⟨i, m⟩, rfl⟩ | ⟨i, rfl⟩), rfl⟩
      · exact ⟨(i, j.succAbove m), hA i m⟩
      · exact ⟨(i, j), hB i⟩

  have hη : Algebra.trdeg F (Algebra.adjoin F (Set.range η)) = ((d : ℕ) : Cardinal) := by
    have heq : Algebra.adjoin F (Set.range η) =
        Algebra.adjoin F (Set.range fun m => ξ m * (ξ j)⁻¹) := by
      apply le_antisymm
      · rw [Algebra.adjoin_le_iff]
        rintro _ ⟨m, rfl⟩
        exact neg_mem (Algebra.subset_adjoin ⟨j.succAbove m, rfl⟩)
      · rw [Algebra.adjoin_le_iff]
        rintro _ ⟨m, rfl⟩
        by_cases hm : m = j
        · beta_reduce
          rw [hm, mul_inv_cancel₀ hξj]
          exact one_mem _
        · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hm
          have : ξ (j.succAbove m') * (ξ j)⁻¹ = -η m' := (neg_neg _).symm
          beta_reduce
          rw [this]
          exact neg_mem (Algebra.subset_adjoin ⟨m', rfl⟩)
    rw [heq]
    exact h₃ F (n' + 1) d P j hP hdim hj

  let φ : MvPolynomial (Fin k × Fin (n' + 1)) F →ₐ[F] MvPolynomial (Fin k × Fin (n' + 1)) K :=
    aeval (genSubst ξ c)
  have hker : incIdeal P k = RingHom.ker φ := by
    ext g
    rw [h₁ F (n' + 1) k P c hc g, RingHom.mem_ker]
  have hφrange : φ.range = (Algebra.adjoin F G).map ψ := by
    show (aeval (genSubst ξ c)).range = _
    rw [aeval_range, hrange, Algebra.adjoin_image]
  haveI : Algebra.FiniteType F φ.range :=
    Algebra.FiniteType.of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  have htr : Algebra.trdeg F φ.range = ((k * n' + min k d : ℕ) : Cardinal) := by
    rw [hφrange, ← AlgEquiv.trdeg_eq (A := ↥(Algebra.adjoin F G))
      (Subalgebra.equivMapOfInjective (Algebra.adjoin F G) ψ hψ)]
    exact h₂ F K n' k d η hη
  rw [hker, ringKrullDim_eq_of_ringEquiv (AlgEquiv.toRingEquiv (Ideal.quotientKerEquivRange φ)),
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F (A := ↥φ.range), htr]
  have hnum : k * (n' + 1) - k + min k d = k * n' + min k d := by
    rw [Nat.mul_succ, Nat.add_sub_cancel]
  rw [hnum]
  simp

end GroundTheory.Heights₂.Heights
end

