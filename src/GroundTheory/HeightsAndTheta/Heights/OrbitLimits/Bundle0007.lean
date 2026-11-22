import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MixedFieldContraction.ContractMixedFieldStatement
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0015

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageCoord
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem ImageCoord.mConeMap_rename {K : Type} {ι : K → Type} {K' : Type} {ι' : K' → Type}
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (hv : ∀ p, (v p).1 = κ p.1)
    {Ω : Type} [Field Ω] (y : (Σ k', ι' k') → Ω) (f : MRing ι) :
    mConeMap y (rename v f) = rename κ (mConeMap (y ∘ v) f) := by
  have h : ((mConeMap y).comp (rename v : MRing ι →ₐ[ℤ] MRing ι')) =
      ((rename κ : MvPolynomial K Ω →ₐ[Ω] MvPolynomial K' Ω).restrictScalars ℤ).comp
        (mConeMap (y ∘ v)) := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap, hv p]
  exact congrArg (fun φ => φ f) h

theorem ImageCoord.proof : ImageCoordStatement := by
  intro K _ ι _ K' _ ι' _ κ v Ω _ y hB
  obtain ⟨hκ, -, hv, -⟩ := hB
  ext f
  simp only [imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, ImageCoord.mConeMap_rename κ v hv y f]
  constructor
  · intro h
    exact rename_injective κ hκ (by rw [h, map_zero])
  · intro h
    rw [h, map_zero]

end GroundTheory.Heights₂.Heights.Targets
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PBlockTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 Algebra Cardinal

namespace BlockTrdeg

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open scoped Classical

section Denominators

variable {σ : Type} {L : Type} [Field L] [Algebra ℚ L]

theorem exists_nat_mul_mem_range (ψ : MvPolynomial σ ℤ →+* L) {y : L}
    (hy : y ∈ adjoin ℚ (Set.range fun p ↦ ψ (X p))) :
    ∃ n : ℕ, n ≠ 0 ∧ (n : L) * y ∈ ψ.range := by
  induction hy using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨p, rfl⟩ := hx
    exact ⟨1, one_ne_zero, ⟨X p, by rw [Nat.cast_one, one_mul]⟩⟩
  | algebraMap q =>
    refine ⟨q.den, q.den_nz, ⟨(q.num : MvPolynomial σ ℤ), ?_⟩⟩
    rw [map_intCast, ← map_natCast (algebraMap ℚ L), ← map_mul, Rat.den_mul_eq_num, map_intCast]
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : L) * (x + y) = m * (n * x) + n * (m * y) := by push_cast; ring
    rw [e]
    exact add_mem (mul_mem (natCast_mem _ _) hnx) (mul_mem (natCast_mem _ _) hmy)
  | mul x y _ _ hx hy =>
    obtain ⟨n, hn, hnx⟩ := hx
    obtain ⟨m, hm, hmy⟩ := hy
    refine ⟨n * m, mul_ne_zero hn hm, ?_⟩
    have e : ((n * m : ℕ) : L) * (x * y) = (n * x) * (m * y) := by push_cast; ring
    rw [e]
    exact mul_mem hnx hmy

theorem exists_nat_mul_mem_range_finset (ψ : MvPolynomial σ ℤ →+* L) (s : Finset L)
    (hs : ∀ y ∈ s, y ∈ adjoin ℚ (Set.range fun p ↦ ψ (X p))) :
    ∃ n : ℕ, n ≠ 0 ∧ ∀ y ∈ s, (n : L) * y ∈ ψ.range := by
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨n, hn, hns⟩ := ih fun y hy ↦ hs y (Finset.mem_insert_of_mem hy)
    obtain ⟨m, hm, hma⟩ := exists_nat_mul_mem_range ψ (hs a (Finset.mem_insert_self a s))
    refine ⟨n * m, mul_ne_zero hn hm, fun y hy ↦ ?_⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · rw [Nat.cast_mul, mul_assoc]
      exact mul_mem (natCast_mem _ _) hma
    · rw [Nat.cast_mul, mul_comm (n : L), mul_assoc]
      exact mul_mem (natCast_mem _ _) (hns y hy)

end Denominators

section Grading

variable {K : Type} {K' : Type} [Fintype K'] {ι : K → Type} {ι' : K' → Type} [∀ k, Fintype (ι' k)]

abbrev Forgotten (κ : K → K') : Type := {k' : K' // k' ∉ Set.range κ}

def forgetWeight (κ : K → K') : (Σ k', ι' k') → (Forgotten κ → ℕ) :=
  fun q k ↦ if q.1 = k.1 then 1 else 0

theorem weight_forgetWeight (κ : K → K') (m : (Σ k', ι' k') →₀ ℕ) (k : Forgotten κ) :
    Finsupp.weight (forgetWeight (ι' := ι') κ) m k = ∑ i, m ⟨k.1, i⟩ := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intro; simp), Finset.sum_apply,
    Fintype.sum_sigma, Finset.sum_eq_single k.1]
  · simp [forgetWeight]
  · intro b _ hb
    simp [forgetWeight, hb]
  · simp

theorem isHomogeneous_forgetWeight (κ : K → K') {P : Ideal (MRing ι')} (h : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (forgetWeight (ι' := ι') κ)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx ↦ ?_
  obtain ⟨a, ha⟩ := hS x hx
  refine ⟨fun k ↦ a k.1, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ?_⟩
  intro d hd
  funext k
  rw [weight_forgetWeight]
  exact ha d (mem_support_iff.mpr hd) k.1

omit [Fintype K'] [∀ k, Fintype (ι' k)] in

theorem isWeightedHomogeneous_rename (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')}
    (hv : ∀ p, (v p).1 ∈ Set.range κ) (g : MvPolynomial (Σ k, ι k) ℤ) :
    IsWeightedHomogeneous (forgetWeight κ) (rename v g) 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => rw [rename_C]; exact isWeightedHomogeneous_C _ _
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p q hp =>
    rw [map_mul, rename_X]
    have h0 : forgetWeight κ (v q) = 0 := by
      funext k
      simp only [forgetWeight, Pi.zero_apply]
      rw [if_neg]
      intro h
      exact k.2 (h ▸ hv q)
    have := hp.mul (isWeightedHomogeneous_X ℤ (forgetWeight κ) (v q))
    rwa [h0, add_zero] at this

def forgetMonomial (κ : K → K') (i : ∀ k : Forgotten κ, ι' k.1) (a : Forgotten κ →₀ ℕ) : MRing ι' :=
  ∏ k, X ⟨k.1, i k⟩ ^ a k

omit [∀ k, Fintype (ι' k)] in

theorem isWeightedHomogeneous_forgetMonomial (κ : K → K') (i : ∀ k : Forgotten κ, ι' k.1)
    (a : Forgotten κ →₀ ℕ) :
    IsWeightedHomogeneous (forgetWeight κ) (forgetMonomial κ i a) ⇑a := by
  have := IsWeightedHomogeneous.prod Finset.univ (fun k ↦ (X ⟨k.1, i k⟩ : MRing ι') ^ a k)
    (fun k ↦ a k • forgetWeight κ ⟨k.1, i k⟩)
    fun k _ ↦ (isWeightedHomogeneous_X ℤ (forgetWeight κ) _).pow (a k)
  unfold forgetMonomial
  convert this using 1
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp [forgetWeight]
  · intro b _ hb
    rw [Pi.smul_apply, forgetWeight, if_neg (fun h ↦ hb (Subtype.ext h)), smul_zero]
  · simp

end Grading

section Independence

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')}
  {L : Type} [Field L] [Algebra ℚ L] {φ : MRing ι' →+* L}

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem algebraicIndependent_forgotten (hv : ∀ p, (v p).1 = κ p.1) (hP : IsMultiHomogIdeal P')
    (hprime : P'.IsPrime) (hker : RingHom.ker φ = P') (i : ∀ k : Forgotten κ, ι' k.1)
    (hi : ∀ k, (X ⟨k.1, i k⟩ : MRing ι') ∉ P') (S : Subalgebra ℚ L)
    (hS : S ≤ adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p)))) :
    AlgebraicIndependent S (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) := by
  rw [algebraicIndependent_iff]
  intro p hp
  set ψ : MvPolynomial (Σ k, ι k) ℤ →+* L := φ.comp (rename v).toRingHom with hψ
  have hA : adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p))) = adjoin ℚ (Set.range fun p ↦ ψ (X p)) := by
    simp [ψ]
  obtain ⟨N, hN, hNs⟩ := exists_nat_mul_mem_range_finset ψ (p.support.image fun a ↦ ((coeff a p : S) : L)) (by
    intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
    rw [← hA]
    exact hS (coeff a p).2)
  choose g hg using fun a : p.support ↦ RingHom.mem_range.mp (hNs _ (Finset.mem_image_of_mem _ a.2))
  set H : MRing ι' := ∑ a : p.support, rename v (g a) * forgetMonomial κ i a.1 with hHdef
  have hH : H ∈ P' := by
    rw [← hker, RingHom.mem_ker]
    have e1 : φ H = (N : L) * aeval (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) p := by
      rw [hHdef, map_sum, aeval_def, eval₂_eq', Finset.mul_sum, ← Finset.sum_coe_sort p.support]
      refine Finset.sum_congr rfl fun a _ ↦ ?_
      rw [map_mul, show φ (rename v (g a)) = ψ (g a) from rfl, hg a, forgetMonomial, map_prod]
      simp only [map_pow, mul_assoc]
      rfl
    rw [e1, hp, mul_zero]
  refine MvPolynomial.ext _ _ fun a ↦ ?_
  rw [coeff_zero]
  by_cases ha : a ∈ p.support
  swap
  · exact notMem_support_iff.mp ha
  have hhom : ∀ b : p.support, IsWeightedHomogeneous (forgetWeight κ)
      (rename v (g b) * forgetMonomial κ i b.1) ⇑b.1 := by
    intro b
    have := (isWeightedHomogeneous_rename κ (fun p ↦ ⟨p.1, (hv p).symm⟩) (g b)).mul
      (isWeightedHomogeneous_forgetMonomial κ i b.1)
    rwa [zero_add] at this
  have hcomp := weightedHomogeneousComponent_mem_of_mem ℤ (forgetWeight κ)
    (isHomogeneous_forgetWeight κ hP) hH (⇑a)
  have e2 : weightedHomogeneousComponent (forgetWeight κ) (⇑a) H =
      rename v (g ⟨a, ha⟩) * forgetMonomial κ i a := by
    rw [hHdef, map_sum, Finset.sum_eq_single ⟨a, ha⟩]
    · exact (hhom ⟨a, ha⟩).weightedHomogeneousComponent_same
    · intro b _ hb
      exact (hhom b).weightedHomogeneousComponent_ne _
        (fun h ↦ hb (Subtype.ext (DFunLike.coe_injective h).symm))
    · simp
  rw [e2] at hcomp
  rcases hprime.mem_or_mem hcomp with h1 | h1
  · rw [← hker, RingHom.mem_ker] at h1
    have h2 : (N : L) * ((coeff a p : S) : L) = 0 := by
      rw [← hg ⟨a, ha⟩]
      exact h1
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
    have h3 := (mul_eq_zero.mp h2).resolve_left (Nat.cast_ne_zero.mpr hN)
    exact_mod_cast h3
  · exfalso
    have := hprime
    rw [forgetMonomial] at h1
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
    exact hi k (hprime.mem_of_pow_mem _ hk)

end Independence

theorem proof : Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' L _ _ φ hκv hP hker
  obtain ⟨hκ, -, hv, -⟩ := hκv
  choose i hi using fun k : Forgotten κ ↦ hP.2.2 k.1
  set A := adjoin ℚ (Set.range fun p : Σ k, ι k ↦ φ (X (v p))) with hAdef
  set B := adjoin ℚ (Set.range fun q : Σ k', ι' k' ↦ φ (X q)) with hBdef
  have : FaithfulSMul ℚ A :=
    (faithfulSMul_iff_algebraMap_injective ℚ A).mpr (algebraMap ℚ A).injective
  obtain ⟨τ, x, hx⟩ := exists_isTranscendenceBasis' ℚ A
  set b₀ : τ → L := A.val ∘ x with hb₀def
  have hb₀ : AlgebraicIndependent ℚ b₀ := hx.1.map' Subtype.val_injective
  have hSA : adjoin ℚ (Set.range b₀) ≤ A := adjoin_le (Set.range_subset_iff.mpr fun j ↦ (x j).2)
  have he := algebraicIndependent_forgotten hv hP.2.1 hP.1 hker i hi _ hSA
  have hind : AlgebraicIndependent ℚ (Sum.elim (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) b₀) :=
    hb₀.sumElim he
  have hAB : A ≤ B := adjoin_mono (Set.range_subset_iff.mpr fun p ↦ ⟨v p, rfl⟩)
  have hmem : ∀ j, Sum.elim (fun k : Forgotten κ ↦ φ (X ⟨k.1, i k⟩)) b₀ j ∈ B := by
    rintro (k | j)
    · exact subset_adjoin ⟨_, rfl⟩
    · exact hAB (x j).2
  have hy : AlgebraicIndependent ℚ (fun j ↦ (⟨_, hmem j⟩ : B)) := AlgebraicIndependent.of_comp B.val hind
  have hle := hy.cardinalMk_le_trdeg
  have hcard : ((Fintype.card K' - Fintype.card K : ℕ) : Cardinal) = #(Forgotten κ) := by
    rw [Cardinal.mk_fintype, Fintype.card_subtype_compl, Set.card_range_of_injective hκ]
  rw [← hx.cardinalMk_eq_trdeg, hcard, add_comm, ← lift_id #(Forgotten κ), ← lift_id #τ, ← mk_sum]
  exact hle

end BlockTrdeg

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PFnDegRelDeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GroundTheory.Heights₂.Heights.FieldNumbers

noncomputable section

universe u

namespace FnDegRelDeg

theorem exists_div_of_mem_adjoin {F R L : Type*} [Field F] [CommRing R] [Field L] [Algebra F L]
    (τ : R →+* L) (hF : ∀ c : F, ∃ x, τ x = algebraMap F L c) {z : L}
    (hz : z ∈ IntermediateField.adjoin F (Set.range τ)) : ∃ x y, z = τ x / τ y := by
  obtain ⟨r, hr, s, hs, rfl⟩ := IntermediateField.mem_adjoin_iff_div.1 hz
  let S : Subalgebra F L := { τ.rangeS with algebraMap_mem' := fun c => RingHom.mem_rangeS.2 (hF c) }
  have hle : Algebra.adjoin F (Set.range τ) ≤ S :=
    Algebra.adjoin_le (by rintro _ ⟨x, rfl⟩; exact RingHom.mem_rangeS.2 ⟨x, rfl⟩)
  obtain ⟨x, rfl⟩ := RingHom.mem_rangeS.1 (hle hr)
  obtain ⟨y, rfl⟩ := RingHom.mem_rangeS.1 (hle hs)
  exact ⟨x, y, rfl⟩

theorem isFractionRing_codRestrict {R L F' : Type*} [CommRing R] [Field L] [Field F'] [Algebra F' L]
    (E : IntermediateField F' L) (τ : R →+* L) (hτ : Function.Injective τ) (hmem : ∀ x, τ x ∈ E)
    (hq : ∀ z ∈ E, ∃ x y, z = τ x / τ y) :
    letI := (τ.codRestrict E hmem).toAlgebra
    IsFractionRing R E := by
  let _ := (τ.codRestrict E hmem).toAlgebra
  have hinj : Function.Injective (algebraMap R E) := fun a b h => hτ (congrArg Subtype.val h)
  have : FaithfulSMul R E := (faithfulSMul_iff_algebraMap_injective R E).2 hinj
  refine IsFractionRing.of_field R E fun z => ?_
  obtain ⟨x, y, hxy⟩ := hq z z.2
  refine ⟨x, y, Subtype.ext ?_⟩
  rw [IntermediateField.coe_div]
  exact hxy

theorem finrank_eq_relfinrank {F R₁ R₂ L : Type*} [Field F] [CommRing R₁] [CommRing R₂] [Field L]
    [Algebra F L] [Algebra R₁ R₂] (ρ : R₂ →+* L) (hρ : Function.Injective ρ)
    (E H : IntermediateField F L) (hEH : E ≤ H)
    (hτ : Function.Injective (ρ.comp (algebraMap R₁ R₂)))
    (hτE : ∀ x, ρ (algebraMap R₁ R₂ x) ∈ E) (hρH : ∀ x, ρ x ∈ H)
    (hEq : ∀ z ∈ E, ∃ x y, z = ρ (algebraMap R₁ R₂ x) / ρ (algebraMap R₁ R₂ y))
    (hHq : ∀ z ∈ H, ∃ x y, z = ρ x / ρ y) :
    Module.finrank R₁ R₂ = IntermediateField.relfinrank E H := by
  rw [IntermediateField.relfinrank_eq_finrank_of_le hEH]
  set H' := IntermediateField.extendScalars hEH
  have hρH' : ∀ x, ρ x ∈ H' := fun x => (IntermediateField.mem_extendScalars hEH).2 (hρH x)
  let _ : Algebra R₁ E := ((ρ.comp (algebraMap R₁ R₂)).codRestrict E hτE).toAlgebra
  let _ : Algebra R₂ H' := (ρ.codRestrict H' hρH').toAlgebra
  let _ : Algebra R₁ H' := ((algebraMap R₂ H').comp (algebraMap R₁ R₂)).toAlgebra
  have : IsScalarTower R₁ R₂ H' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower R₁ E H' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsFractionRing R₁ E := isFractionRing_codRestrict E _ hτ hτE hEq
  have : IsFractionRing R₂ H' := isFractionRing_codRestrict H' ρ hρ hρH' fun z hz =>
    hHq z ((IntermediateField.mem_extendScalars hEH).1 hz)
  exact (IsFractionRing.finrank_eq R₁ E R₂ H').symm

section Dehom

variable {F : Type u} [Field F] {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
  [∀ k, Fintype (ι k)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem dehom_mem_homFracDegZero (V : Ideal (MRing ι F)) [V.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) (f : MRing ι F) :
    IntNumPoint.dehom V i f ∈ homFracDegZero V := by
  have : (IntNumPoint.dehom V i).range ≤ (homFracDegZero V).toSubalgebra := by
    rw [IntNumPoint.dehom, aeval_range]
    refine Algebra.adjoin_le ?_
    rintro _ ⟨p, rfl⟩
    exact IntermediateField.subset_adjoin F _
      ⟨blockWeight ι p, X p, X ⟨p.1, i p.1⟩, isWeightedHomogeneous_X (R := F) _ _,
        isWeightedHomogeneous_X (R := F) _ _, hi p.1, rfl⟩
  exact this ⟨f, rfl⟩

theorem div_eq_dehom_div (V : Ideal (MRing ι F)) [V.IsPrime] (i : ∀ k, ι k)
    (hi : ∀ k, (X ⟨k, i k⟩ : MRing ι F) ∉ V) {b : K → ℕ} {f g : MRing ι F}
    (hf : IsMultiHomog f b) (hg : IsMultiHomog g b) :
    algebraMap (MRing ι F ⧸ V) (FractionRing (MRing ι F ⧸ V)) (Ideal.Quotient.mk V f) /
        algebraMap (MRing ι F ⧸ V) (FractionRing (MRing ι F ⧸ V)) (Ideal.Quotient.mk V g) =
      IntNumPoint.dehom V i f / IntNumPoint.dehom V i g := by
  rw [← IntNumPoint.cls_apply, ← IntNumPoint.cls_apply,
    ← IntNumPoint.dehom_mul_of_isMultiHomog i hi hf, ← IntNumPoint.dehom_mul_of_isMultiHomog i hi hg,
    mul_div_mul_right _ _ (IntNumPoint.chartProd_ne_zero i hi b)]

end Dehom

section Contract

variable {F : Type u} [Field F] {K K' : Type} {ι' : K' → Type} (j : K ↪ K') (P' : Ideal (MRing ι' F))
  [P'.IsPrime] (i' : ∀ k', ι' k')

theorem contractFracMap_algebraMap (f : MRing (fun k => ι' (j k)) F) :
    contractFracMap j P' (algebraMap _ _ (Ideal.Quotient.mk (contractPrime j P') f)) =
      algebraMap (MRing ι' F ⧸ P') (FractionRing (MRing ι' F ⧸ P'))
        (Ideal.Quotient.mk P' (rename (blockIncl j ι') f)) := by
  simp [contractFracMap, contractQuot]
  rfl

theorem contractFracMap_comp_dehom :
    (contractFracMap j P').comp (IntNumPoint.dehom (contractPrime j P') (fun k => i' (j k))) =
      (IntNumPoint.dehom P' i').comp (rename (blockIncl j ι')) := by
  refine MvPolynomial.algHom_ext fun r => ?_
  simp only [AlgHom.comp_apply, IntNumPoint.dehom, aeval_X, rename_X, map_div₀, IntNumPoint.xc,
    contractFracMap_algebraMap]
  rfl

end Contract

theorem proof : FnDegRelDeg.Statement.{u} := by
  intro F _ K K' _ _ _ _ ι _ ι' _ κ v hκv P' hP' i' hi
  have := hP'.isPrime
  set j : K ↪ K' := ⟨κ, hκv.1⟩

  have hu : ∀ q : Σ k, ι k, ∃ r : ι' (j q.1), blockIncl j ι' ⟨q.1, r⟩ = v q := by
    intro q
    have h := hκv.2.2.1 q
    revert h
    generalize v q = q'
    obtain ⟨k', r⟩ := q'
    rintro (h : k' = κ q.1)
    subst h
    exact ⟨r, rfl⟩
  let ucoord : (Σ k, ι k) → (Σ k, ι' (j k)) := fun q => ⟨q.1, (hu q).choose⟩
  have hucoord : blockIncl j ι' ∘ ucoord = v := funext fun q => (hu q).choose_spec
  have hw : ∀ r : Σ k, ι' (j k), ∃ q, v q = blockIncl j ι' r := fun r => hκv.2.2.2 _ ⟨r.1, rfl⟩
  let wcoord : (Σ k, ι' (j k)) → (Σ k, ι k) := fun r => (hw r).choose
  have hwcoord : v ∘ wcoord = blockIncl j ι' := funext fun r => (hw r).choose_spec
  have hi0 : ∀ k, (X ⟨k, i' (j k)⟩ : MRing (fun k => ι' (j k)) F) ∉ contractPrime j P' := by
    intro k h
    have h' := Ideal.mem_comap.1 h
    rw [rename_X] at h'
    exact hi (j k) h'

  let ρ := Ideal.Quotient.liftₐ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartIdeal P' i') (IntNumPoint.dehom P' i')
    (fun a ha => IntNumPoint.dehom_eq_zero_of_mem_chartIdeal i' hi hP'.multiHomog ha)
  have hρ : ∀ f, ρ (Ideal.Quotient.mk _ f) = IntNumPoint.dehom P' i' f := fun f => rfl
  have hρinj : Function.Injective ρ := by
    refine (injective_iff_map_eq_zero ρ).2 fun a ha => ?_
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [hρ] at ha
    exact Ideal.Quotient.eq_zero_iff_mem.2 (IntNumPoint.mem_chartIdeal_of_dehom_eq_zero i' hi ha)
  let _ := (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i').toAlgebra
  have hτ : ∀ p : MRing ι F, ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ p)) =
      IntNumPoint.dehom P' i' (rename v p) := fun p => rfl
  have key : ∀ p : MRing ι F, IntNumPoint.dehom P' i' (rename v p) =
      contractFracMap j P' (IntNumPoint.dehom (contractPrime j P') (fun k => i' (j k))
        (rename ucoord p)) := by
    intro p
    have e : rename v p = rename (blockIncl j ι') (rename ucoord p) := by
      rw [rename_rename, hucoord]
    rw [e]
    exact (AlgHom.congr_fun (contractFracMap_comp_dehom j P' i') _).symm
  have key2 : ∀ f, contractFracMap j P' (IntNumPoint.dehom (contractPrime j P')
      (fun k => i' (j k)) f) =
      ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ (rename wcoord f))) := by
    intro f
    rw [hτ, rename_rename, hwcoord]
    exact AlgHom.congr_fun (contractFracMap_comp_dehom j P' i') f
  have hρH : ∀ x, ρ x ∈ homFracDegZero P' := by
    intro x
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact dehom_mem_homFracDegZero P' i' hi f
  have hτE : ∀ x, ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' x) ∈
      (homFracDegZero (contractPrime j P')).map (contractFracMap j P') := by
    intro x
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hτ, key]
    exact (IntermediateField.mem_map _).2 ⟨_, dehom_mem_homFracDegZero _ _ hi0 _, rfl⟩
  have hHq : ∀ z ∈ homFracDegZero P', ∃ x y, z = ρ x / ρ y := by
    intro z hz
    refine exists_div_of_mem_adjoin ρ.toRingHom (fun c => ⟨algebraMap F _ c, ρ.commutes c⟩) ?_
    revert z
    show homFracDegZero P' ≤ _
    unfold homFracDegZero
    refine IntermediateField.adjoin_le_iff.2 ?_
    rintro _ ⟨b, f, g, hf, hg, hgP, rfl⟩
    rw [div_eq_dehom_div P' i' hi hf hg]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ f, rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ g, rfl⟩)
  have hEq : ∀ z ∈ (homFracDegZero (contractPrime j P')).map (contractFracMap j P'),
      ∃ x y, z = ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' x) /
        ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' y) := by
    intro z hz
    refine exists_div_of_mem_adjoin (ρ.toRingHom.comp (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i'))
      (fun c => ⟨Ideal.Quotient.mk _ (C c), ?_⟩) ?_
    · show ρ (ReciprocityTheory.ChartRestriction.G.AI.I1.chartMap v P' i' (Ideal.Quotient.mk _ (C c))) = _
      rw [hτ, rename_C]
      exact (IntNumPoint.dehom P' i').commutes c
    revert z
    show (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤ _
    unfold homFracDegZero
    rw [IntermediateField.adjoin_map, IntermediateField.adjoin_le_iff]
    rintro _ ⟨_, ⟨d, f, g, hf, hg, hgP, rfl⟩, rfl⟩
    rw [div_eq_dehom_div _ _ hi0 hf hg, map_div₀, key2, key2]
    exact div_mem (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ (rename wcoord f), rfl⟩)
      (IntermediateField.subset_adjoin _ _ ⟨Ideal.Quotient.mk _ (rename wcoord g), rfl⟩)
  have hEH : (homFracDegZero (contractPrime j P')).map (contractFracMap j P') ≤
      homFracDegZero P' := by
    intro z hz
    obtain ⟨x, y, rfl⟩ := hEq z hz
    exact div_mem (hρH _) (hρH _)
  unfold ReciprocityTheory.ChartRestriction.G.AI.I1.fnDeg relDeg
  exact finrank_eq_relfinrank ρ.toRingHom hρinj _ _ hEH
    (fun a b h => Ideal.quotientMap_injective (hρinj h)) hτE hρH hEq hHq

end FnDegRelDeg

end

end GroundTheory.Heights₂.Heights.Targets
end

