import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsFieldSubalgebraSelf
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PHilbertPrime
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0013
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMixedNumberPolynomial
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PMultigradedFiltration
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PFiltrationHilbSum
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0044
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.NefFibresSegreSt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial

def NefFibresSegre.Statement : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K]
    [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (NumbersDVR.MRing ι O)) (d : ℕ)
    (β : K → ℤ), NumbersDVR.IsModelOver P d →
    ∃ (Ω : Type) (_ : Field Ω) (_ : Algebra O Ω) (_ : Algebra (FractionRing O) Ω)
      (_ : IsScalarTower O (FractionRing O) Ω) (N : ℕ) (x : Fin (N + 1) → Ω) (M : Kleiman.LineBundle O x),
      (Kleiman.NefAbove M.toSubSystem ((IsLocalRing.maximalIdeal O).map (C : O →+* Kleiman.Poly O N)) ↔
        IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (IsLocalRing.ResidueField O) (NumbersDVR.specialIdeal P) β) ∧
      (Kleiman.Nef (M.toSubSystem.extend (FractionRing O)) ↔
        IndefiniteRowSideFullHecke.Kleiman2.IsNefIdeal (FractionRing O) (NumbersDVR.genFib P) β)

theorem NefFibresSegre.hyps :
    NumbersDVR.IsModelOver (⊥ : Ideal (NumbersDVR.MRing (fun _ : Unit => Fin 2) exO)) 1 :=
  NumbersDVR.isModelOver_projectiveSpace 1

example (h : NefFibresSegre.Statement) :=
  h exO Unit (fun _ => Fin 2) ⊥ 1 (fun _ => 1) NefFibresSegre.hyps

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.OfParts
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)
open IndefiniteRowSideFullHecke.Kleiman2 (locIn modelPts SameModel modVec resImage residue ResField)

def RestrictionPoints.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime],
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
      modelPts S (modVec S y c p) =
        {z' | ∃ z ∈ modelPts S y, z ≤ locIn (chartRingOver S y c) p ∧
          z' = Subring.closure (resImage S y c p z)}

def RestrictionSections.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) (Ω : Type) [Field Ω] [Algebra S Ω]
    (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime],
    (∀ k, y ⟨k, c k⟩ ≠ 0) →
      ∀ β : K → ℤ, ∀ s ∈ secOver S y β,
        residue S y c p (s * ∏ k, y ⟨k, c k⟩ ^ (-β k)) ∈ secOver S (modVec S y c p) β

def RestrictionSame.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] (ι : K → Type) (K' : Type) (ι' : K' → Type)
    (Ω : Type) [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (y' : (Σ k, ι' k) → Ω),
    SameModel S y y' →
    ∀ (c : ∀ k, ι k) (p : Ideal (chartRingOver S y c)) [p.IsPrime], (∀ k, y ⟨k, c k⟩ ≠ 0) →
      ∀ (c' : ∀ k, ι' k) (p' : Ideal (chartRingOver S y' c')) [p'.IsPrime],
        (∀ k, y' ⟨k, c' k⟩ ≠ 0) →
        locIn (chartRingOver S y' c') p' = locIn (chartRingOver S y c) p →
        ∃ φ : ResField S y c p ≃ₐ[S] ResField S y' c' p',
          (∀ z ∈ modelPts S y, z ≤ locIn (chartRingOver S y c) p →
            φ '' resImage S y c p z = resImage S y' c' p' z) ∧
          SameModel S (fun q => φ (modVec S y c p q)) (modVec S y' c' p')

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace HilbertPositive

theorem hilbertPrime : HilbertSamuel.HilbertPrime.Statement.{u} :=
  HilbertSamuel.HilbertPrime.proof HilbertSamuel.HilbertDimZero.proof
    (HilbertSamuel.HilbertIncrement.proof HilbertSamuel.IntersectionRecursion.proof)
    (HilbertSamuel.MixedNumberPolynomial.proof
      (HilbertSamuel.MultigradedHilbertPolynomial.proof HilbertSamuel.EventualPolynomial.proof))
    (HilbertSamuel.ModulesFromPrimes.proof HilbertSamuel.MultigradedFiltration.proof
      HilbertSamuel.FiltrationHilbSum.proof HilbertSamuel.DegLTGrowth.proof)

theorem mixedNumber : HilbertSamuel.MixedNumberPolynomial.Statement.{u} :=
  HilbertSamuel.MixedNumberPolynomial.proof
    (HilbertSamuel.MultigradedHilbertPolynomial.proof HilbertSamuel.EventualPolynomial.proof)

def blockEquiv (N : ℕ) : (Σ _ : Unit, Fin (N + 1)) ≃ Fin (N + 1) where
  toFun v := v.2
  invFun i := ⟨(), i⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

theorem weight_blockWeight_one (d : (Σ _ : Unit, Fin (N + 1)) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) d = fun _ => d.degree := by
  funext u
  rw [Finsupp.weight_apply, Finsupp.degree, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp [NumbersDVR.blockWeight]

theorem isWeightedHomogeneous_iff (p : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k) (n : ℕ) :
    IsWeightedHomogeneous (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1))) p (fun _ => n) ↔
      p.IsHomogeneous n := by
  constructor
  · intro h d hd
    have h1 : d.degree = n := congrFun ((weight_blockWeight_one d).symm.trans (h hd)) ()
    rw [← h1, Finsupp.degree_eq_weight_one]
    rfl
  · intro h d hd
    rw [weight_blockWeight_one]
    funext _
    rw [Finsupp.degree_eq_weight_one]
    exact h hd

theorem ringKrullDim_primeOfOne (y : Fin (N + 1) → Ω) :
    ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ringKrullDim (Poly k N ⧸ primeOf (S := k) y) := by
  let f : NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ≃+* Poly k N :=
    (renameEquiv k (blockEquiv N)).toRingEquiv
  have hc : primeOfOne (S := k) y = (primeOf (S := k) y).comap f.toRingHom :=
    Ideal.ext fun _ => Iff.rfl
  have h : primeOf (S := k) y = (primeOfOne (S := k) y).map f.toRingHom := by
    rw [hc, Ideal.map_comap_of_surjective f.toRingHom f.surjective]
  exact ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv _ _ f h)

theorem ne_zero_of_isSubvar {y : Fin (N + 1) → Ω} {e : ℕ} (h : IsSubvar y (primeOf (S := k) y) e) :
    y ≠ 0 := by
  obtain ⟨i, hi⟩ := h.relevant
  intro hy
  apply hi
  rw [mem_primeOf_of_isHomogeneous y (isHomogeneous_X k i), aeval_X, hy, Pi.zero_apply]

theorem finrank_piece_eq_hilbFn (y : Fin (N + 1) → Ω) (n : ℕ) :
    (Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℤ) =
      NumbersDVR.hilbFn (primeOfOne (S := k) y) (fun _ => (n : ℤ)) := by
  classical
  rw [NumbersDVR.hilbFn, if_pos (fun _ => Int.natCast_nonneg n)]
  simp only [Int.toNat_natCast]
  congr 1
  set V := weightedHomogeneousSubmodule k (NumbersDVR.blockWeight (fun _ : Unit => Fin (N + 1)))
    (fun _ : Unit => n) with hV
  let f₁ : V →ₗ[k] NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y :=
    (Ideal.Quotient.mkₐ k (primeOfOne (S := k) y)).toLinearMap ∘ₗ V.subtype
  let f₂ : V →ₗ[k] Ω :=
    (aeval (fun v : Σ _ : Unit, Fin (N + 1) => y v.2)).toLinearMap ∘ₗ V.subtype
  have hhom : ∀ v ∈ V, (oneBlock (S := k) (N := N) v).IsHomogeneous n := fun v hv =>
    ((isWeightedHomogeneous_iff v n).mp ((mem_weightedHomogeneousSubmodule _ _ _ _).mp hv)).rename_isHomogeneous
  have heval : ∀ v, aeval y (oneBlock (S := k) (N := N) v) = aeval (fun w : Σ _ : Unit, Fin (N + 1) => y w.2) v :=
    fun v => by rw [oneBlock, aeval_rename]; rfl
  have hr₁ : LinearMap.range f₁ = NumbersDVR.gradedPiece (primeOfOne (S := k) y) (fun _ => n) := by
    rw [NumbersDVR.gradedPiece, LinearMap.range_comp, Submodule.range_subtype]
  have hr₂ : LinearMap.range f₂ = (coordGraded k y).piece (n : ℤ) := by
    apply le_antisymm
    · rintro _ ⟨⟨v, hv⟩, rfl⟩
      refine Submodule.subset_span ⟨oneBlock (S := k) (N := N) v, n, hhom v hv, rfl, ?_⟩
      exact (heval v).symm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, e, hg, he, rfl⟩
      have he' : e = n := by exact_mod_cast he
      subst he'
      refine ⟨⟨rename (blockEquiv N).symm g, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
        ((isWeightedHomogeneous_iff _ e).mpr (hg.rename_isHomogeneous))⟩, ?_⟩
      change aeval (fun v : Σ _ : Unit, Fin (N + 1) => y v.2) (rename (blockEquiv N).symm g) = aeval y g
      rw [aeval_rename]
      rfl
  have hker : LinearMap.ker f₁ = LinearMap.ker f₂ := by
    ext ⟨v, hv⟩
    simp only [LinearMap.mem_ker, f₁, f₂, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype,
      AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    change oneBlock (S := k) (N := N) v ∈ primeOf (S := k) y ↔ _
    rw [mem_primeOf_of_isHomogeneous y (hhom v hv), heval]
  have e₁ := ((f₁.quotKerEquivRange.symm.trans (Submodule.quotEquivOfEq _ _ hker)).trans
    f₂.quotKerEquivRange).finrank_eq
  rw [hr₁, hr₂] at e₁
  exact e₁.symm

end HilbertPositive

open HilbertPositive in

theorem HilbertPositive.proof (hPos : ProjDegreePositive.Statement.{u})
    (hSec : TwistSections.Statement.{u, w}) : HilbertPositive.Statement.{u, w} := by
  intro k _ Ω _ _ N y e he hW
  have hy : y ≠ 0 := ne_zero_of_isSubvar hW
  have hq : NumbersDVR.IsMultiProjPrime (primeOfOne (S := k) y) := isMultiProjPrime_primeOfOne y hy
  have hdim : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ((e + 1 : ℕ) : WithBot ℕ∞) := by
    rw [ringKrullDim_primeOfOne]
    exact hW.dim
  refine ⟨?_, hPos k (Fin (N + 1)) _ e hq hdim, hSec k Ω N y hy⟩
  have hdim' : ringKrullDim (NumbersDVR.MRing (fun _ : Unit => Fin (N + 1)) k ⧸ primeOfOne (S := k) y) =
      ((e + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
    simpa using hdim
  obtain ⟨a₀, C, hC⟩ := hilbertPrime e k Unit (fun _ => Fin (N + 1)) _ hq hdim'
  have hadd := (mixedNumber k Unit (fun _ => Fin (N + 1)) _ e hq hdim').2
  have hhom : ∀ n : ℕ, NumbersDVR.intNum k (primeOfOne (S := k) y)
      (fun _ : Fin e => fun _ : Unit => (n : ℤ)) = (n : ℤ) ^ e *
        NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) := by
    intro n
    have := HilbertSamuel.RankOfSections.const_nsmul
      (fun bs => NumbersDVR.intNum k (primeOfOne (S := k) y) bs) hadd n (fun _ : Unit => (1 : ℤ))
    have e' : (n • fun _ : Unit => (1 : ℤ)) = fun _ : Unit => (n : ℤ) := by
      funext u
      simp
    rw [e'] at this
    exact this
  refine ⟨|C| * 2 ^ (e - 1), ?_⟩
  filter_upwards [eventually_ge_atTop (max a₀ 1)] with n hn
  have h := hC (fun _ => n) (fun _ => le_of_max_le_left hn)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  rw [hhom n, ← finrank_piece_eq_hilbFn] at h
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have hpow : ((n : ℝ) + 1) ^ ((e : ℝ) - 1) ≤ 2 ^ (e - 1) * (n : ℝ) ^ (e - 1) := by
    rw [show (e : ℝ) - 1 = ((e - 1 : ℕ) : ℝ) by rw [Nat.cast_sub he]; simp, Real.rpow_natCast,
      ← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  calc |(Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℝ) -
        (NumbersDVR.intNum k (primeOfOne (S := k) y) (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℝ) *
          (n : ℝ) ^ e / (e.factorial : ℝ)|
      = |(((Module.finrank k ((coordGraded k y).piece (n : ℤ)) : ℤ)) : ℝ) -
          (((n : ℤ) ^ e * NumbersDVR.intNum k (primeOfOne (S := k) y)
            (fun _ : Fin e => fun _ : Unit => (1 : ℤ)) : ℤ) : ℝ) / (e.factorial : ℝ)| := by
        push_cast
        ring_nf
    _ ≤ C * ((n : ℝ) + 1) ^ ((e : ℝ) - 1) := h
    _ ≤ |C| * ((n : ℝ) + 1) ^ ((e : ℝ) - 1) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ ≤ |C| * (2 ^ (e - 1) * (n : ℝ) ^ (e - 1)) := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)
    _ = |C| * 2 ^ (e - 1) * (n : ℝ) ^ (e - 1) := by ring

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PProjDegreePositive
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.HilbertSamuel

noncomputable section

universe u

namespace ProjDegreePositive

variable {F : Type u} [Field F] {ι₀ : Type} [Fintype ι₀]

theorem ringKrullDim_of_mem_minimalPrimes (q W : Ideal (MRing (fun _ : Unit => ι₀) F)) [q.IsPrime]
    (x : MRing (fun _ : Unit => ι₀) F) (hx : x ∉ q) (e : ℕ)
    (hdim : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((e + 1 : ℕ) : WithBot ℕ∞))
    (hmin : W ∈ (q ⊔ Ideal.span {x}).minimalPrimes) :
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e : ℕ) : WithBot ℕ∞) := by
  have hWprime : W.IsPrime := hmin.1.1
  have hIW : q ≤ W := le_sup_left.trans hmin.1.2
  have hxW : x ∈ W := (le_sup_right.trans hmin.1.2) (Ideal.mem_span_singleton_self _)
  set B := MRing (fun _ : Unit => ι₀) F ⧸ q
  have _ : Algebra.FiniteType F B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F q) (Ideal.Quotient.mkₐ_surjective F q)
  set W' : Ideal B := W.map (Ideal.Quotient.mk q)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk q x ∈ W' := Ideal.mem_map_of_mem _ hxW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hmin
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = y := by
    cases h : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MRing (fun _ : Unit => ι₀) F ⧸ W)
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

omit [Fintype ι₀] in

theorem isRelevant_of_ringKrullDim (W : Ideal (MRing (fun _ : Unit => ι₀) F)) [W.IsPrime] (e : ℕ)
    (hW : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ W) = ((e + 1 : ℕ) : WithBot ℕ∞)) :
    IsRelevant W := by
  intro k
  by_contra h
  simp only [not_exists, not_not] at h
  have hX : ∀ v : (Σ _ : Unit, ι₀), (X v : MRing (fun _ : Unit => ι₀) F) ∈ W := by
    rintro ⟨⟨⟩, i⟩
    cases k
    exact h i
  have hsurj : Function.Surjective (algebraMap F (MRing (fun _ : Unit => ι₀) F ⧸ W)) := by
    intro z
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction p using MvPolynomial.induction_on with
    | C a =>
      exact ⟨a, by rw [← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]⟩
    | add p r hp hr =>
      obtain ⟨a, ha⟩ := hp
      obtain ⟨b, hb⟩ := hr
      exact ⟨a + b, by rw [map_add, ha, hb, map_add]⟩
    | mul_X p v _ =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hX v), mul_zero]
  have hle := ringKrullDim_le_of_surjective _ hsurj
  rw [hW, ringKrullDim_eq_zero_of_field] at hle
  have : e + 1 ≤ 0 := by exact_mod_cast hle
  omega

set_option synthInstance.maxHeartbeats 400000 in

theorem hilbFn_pos (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) (n : ℕ) :
    0 < hilbFn q (fun _ => (n : ℤ)) := by
  obtain ⟨i, hi⟩ := hq.relevant ()
  have hqp := hq.isPrime
  obtain ⟨hfin, heq⟩ :=
    GroundTheory.Heights₂.Heights.FieldNumbers.GradedFinite.full F Unit (fun _ => ι₀) q (fun _ => n)
  have heq' : hilbFn q (fun _ => (n : ℤ)) =
      (Module.finrank F (gradedPiece q (fun _ : Unit => n)) : ℤ) := heq
  rw [heq']
  have hmem : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ∈
      gradedPiece q (fun _ : Unit => n) := by
    refine ⟨(X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n, ?_, rfl⟩
    change _ ∈ weightedHomogeneousSubmodule F (blockWeight (fun _ : Unit => ι₀)) (fun _ : Unit => n)
    rw [mem_weightedHomogeneousSubmodule]
    have hp := (isWeightedHomogeneous_X F (blockWeight (fun _ : Unit => ι₀)) ⟨(), i⟩).pow n
    convert hp using 1
    funext k
    cases k
    simp [blockWeight]
  have hne : Ideal.Quotient.mk q ((X ⟨(), i⟩ : MRing (fun _ : Unit => ι₀) F) ^ n) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => hi (hqp.mem_of_pow_mem n h)
  have := hfin
  have : Nontrivial (gradedPiece q (fun _ : Unit => n)) :=
    ⟨⟨⟨_, hmem⟩, 0, fun h => hne (congrArg Subtype.val h)⟩⟩
  have hpos : 0 < Module.finrank F (gradedPiece q (fun _ : Unit => n)) := Module.finrank_pos
  exact_mod_cast hpos

omit [Fintype ι₀] in

theorem le_ker_constantCoeff (q : Ideal (MRing (fun _ : Unit => ι₀) F)) (hq : IsMultiProjPrime q) :
    q ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by
  intro p hp
  rw [RingHom.mem_ker]
  by_contra h
  have h0 := hq.multiHomog p hp 0
  rw [weightedHomogeneousComponent_zero p (fun v => by
    obtain ⟨⟨⟩, _⟩ := v
    intro h'
    have := congrFun h' ()
    simp [blockWeight] at this)] at h0
  have hu : IsUnit (C (coeff 0 p) : MRing (fun _ : Unit => ι₀) F) :=
    (isUnit_iff_ne_zero.mpr (by rwa [← constantCoeff_eq])).map C
  exact hq.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 hu)

theorem pos (D : ℕ) : ∀ q : Ideal (MRing (fun _ : Unit => ι₀) F), IsMultiProjPrime q →
    ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) = ((D + 1 : ℕ) : WithBot ℕ∞) →
    0 < intNum F q (fun _ : Fin D => fun _ => (1 : ℤ)) := by
  induction D with
  | zero =>
    intro q hq hd
    obtain ⟨a₀, ha⟩ := HilbertSamuel.HilbertDimZero.proof F Unit (fun _ => ι₀) q hq
      (by rw [Fintype.card_unit]; exact hd)
    have h := ha (fun _ => a₀) (fun _ => le_rfl)
    have e : (fun _ : Fin 0 => fun _ : Unit => (1 : ℤ)) = (![] : Fin 0 → Unit → ℤ) :=
      funext fun j => j.elim0
    rw [e, ← h]
    exact hilbFn_pos q hq a₀
  | succ D ih =>
    intro q hq hd
    have hqp : q.IsPrime := hq.isPrime
    obtain ⟨i, hX⟩ := hq.relevant ()
    set x : MRing (fun _ : Unit => ι₀) F := X ⟨(), i⟩ with hxdef
    have hx : IsMultiHomog x (blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩) :=
      isWeightedHomogeneous_X F _ _
    have hlt : ringKrullDim (MRing (fun _ : Unit => ι₀) F ⧸ q) <
        ((D + 2 + Fintype.card Unit : ℕ) : WithBot ℕ∞) := by
      rw [hd, Fintype.card_unit]
      exact_mod_cast (by omega : D + 1 + 1 < D + 2 + 1)
    have hcut := CutByForm.full F Unit (fun _ => ι₀) D q hqp hq.multiHomog hlt x _ hx hX
      (fun _ : Fin D => fun _ : Unit => (1 : ℤ))
    have e1 : Matrix.vecCons (fun k => ((blockWeight (fun _ : Unit => ι₀) ⟨(), i⟩ k : ℕ) : ℤ))
        (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) = fun _ : Fin (D + 1) => fun _ : Unit => (1 : ℤ) := by
      funext j k
      cases k
      refine Fin.cases ?_ (fun j => ?_) j <;> simp [blockWeight]
    rw [e1] at hcut
    rw [hcut, cycEval]
    set J := q ⊔ Ideal.span {x} with hJdef
    have hJh : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hq.multiHomog hx

    have hterm : ∀ W, divCycle q x W ≠ 0 →
        0 < divCycle q x W ∧ 0 < intNum F W (fun _ : Fin D => fun _ : Unit => (1 : ℤ)) := by
      intro W hW
      unfold divCycle at hW ⊢
      by_cases hc : W ∈ J.minimalPrimes ∧ IsRelevant W
      · rw [dif_pos hc] at hW ⊢
        have hWp : W.IsPrime := hc.1.1.1
        have hWd := ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hc.1
        have hWq : IsMultiProjPrime W :=
          ⟨hWp, MinimalPrimeMultiHomog.full F Unit (fun _ => ι₀) J W hJh hc.1, hc.2⟩
        exact ⟨lt_of_le_of_ne (by positivity) (Ne.symm hW), ih W hWq hWd⟩
      · rw [dif_neg hc] at hW
        exact absurd rfl hW
    have hfin := DivCycleFiniteSupport.full F Unit (fun _ => ι₀) q x
    rw [finsum_eq_sum_of_support_subset _
      ((Function.support_mul_subset_left _ _).trans hfin.coe_toFinset.symm.subset)]
    refine Finset.sum_pos' (fun W _ => ?_) ?_
    · by_cases hW : divCycle q x W = 0
      · rw [hW, zero_mul]
      · exact (mul_pos (hterm W hW).1 (hterm W hW).2).le

    have hJm : J ≤ RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F) := by
      refine sup_le (le_ker_constantCoeff q hq) ?_
      rw [Ideal.span_le, Set.singleton_subset_iff]
      change constantCoeff x = 0
      rw [hxdef, constantCoeff_X]
    have hmax : (RingHom.ker (constantCoeff : MRing (fun _ : Unit => ι₀) F →+* F)).IsPrime :=
      (RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩).isPrime
    obtain ⟨W, hmin, -⟩ := Ideal.exists_minimalPrimes_le hJm
    have hWp : W.IsPrime := hmin.1.1
    have hWd := ringKrullDim_of_mem_minimalPrimes q W x hX (D + 1) hd hmin
    have hrel := isRelevant_of_ringKrullDim W D hWd
    have hne : divCycle q x W ≠ 0 := by
      unfold divCycle
      rw [dif_pos ⟨hmin, hrel⟩]
      have htop := length_localizedQuot_ne_top J W hmin
      have hzero : multAt J W ≠ 0 := by
        unfold multAt
        rw [Ne, Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
        intro hs
        obtain ⟨r, hr, hr1⟩ := hs (1 : MRing (fun _ : Unit => ι₀) F ⧸ J)
        rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem] at hr1
        exact hr (hmin.1.2 hr1)
      have : (multAt J W).toNat ≠ 0 := by
        rw [Ne, ENat.toNat_eq_zero]
        exact not_or.mpr ⟨hzero, htop⟩
      exact_mod_cast this
    refine ⟨W, hfin.mem_toFinset.mpr hne, mul_pos (hterm W hne).1 (hterm W hne).2⟩

end ProjDegreePositive

theorem ProjDegreePositive.proof : ProjDegreePositive.Statement.{u} := by
  intro F _ ι₀ _ q D hq hd
  exact ProjDegreePositive.pos D q hq hd

end

end GroundTheory.Heights₂.Heights.Kleiman
end

