import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.ExistsPrimeFiltrationOfIsMultiHomogIdeal
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable abbrev lexDecEq (n : ℕ) : DecidableEq (Lex (Fin n → ℕ)) := LinearOrder.toDecidableEq

attribute [local instance 2000] lexDecEq

section Lex

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}

def lexW (e : K ≃ Fin n) : (Σ k, ι k) → Lex (Fin n → ℕ) :=
  fun p => toLex (Pi.single (e p.1) 1)

theorem weight_lexW (e : K ≃ Fin n) (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (lexW (ι := ι) e) m = toLex (fun j => ∑ i, m ⟨e.symm j, i⟩) := by
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype m (fun i c => c • lexW (ι := ι) e i) (fun i => zero_nsmul _)]
  show (∑ p, m p • (Pi.single (e p.1) 1 : Fin n → ℕ)) = fun j => ∑ i, m ⟨e.symm j, i⟩
  funext j
  rw [Finset.sum_apply, Fintype.sum_sigma, Finset.sum_eq_single (e.symm j)]
  · simp [Pi.single_apply]
  · intro k _ hk
    refine Finset.sum_eq_zero fun i _ => ?_
    have hjk : j ≠ e k := fun h => hk (by rw [h, Equiv.symm_apply_apply])
    simp [Pi.single_apply, hjk]
  · simp

theorem isMultiHomog_iff_lex (e : K ≃ Fin n) (f : MRing ι) (a : K → ℕ) :
    IsMultiHomog f a ↔ IsWeightedHomogeneous (lexW e) f (toLex (a ∘ e.symm)) := by
  constructor
  · intro h d hd
    rw [weight_lexW]
    congr 1
    funext j
    exact h d (MvPolynomial.mem_support_iff.mpr hd) (e.symm j)
  · intro h d hd k
    have h1 := h (MvPolynomial.mem_support_iff.mp hd)
    rw [weight_lexW] at h1
    obtain ⟨j, rfl⟩ := e.symm.surjective k
    exact congrFun (toLex.injective h1) j

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomog_of_mem_lex (e : K ≃ Fin n) {f : MRing ι} {m : Lex (Fin n → ℕ)}
    (h : f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) m) :
    IsMultiHomog f (fun k => ofLex m (e k)) := by
  rw [mem_weightedHomogeneousSubmodule] at h
  rw [isMultiHomog_iff_lex e]
  have hm : (fun k => ofLex m (e k)) ∘ e.symm = ofLex m := by
    funext j
    simp
  rw [hm, toLex_ofLex]
  exact h

theorem mem_lex_of_isMultiHomog (e : K ≃ Fin n) {f : MRing ι} {a : K → ℕ} (h : IsMultiHomog f a) :
    f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) (toLex (a ∘ e.symm)) := by
  rw [mem_weightedHomogeneousSubmodule]
  exact (isMultiHomog_iff_lex e f a).1 h

theorem isHomogeneous_lex_iff (e : K ≃ Fin n) (J : Ideal (MRing ι)) :
    J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) ↔ IsMultiHomogIdeal J := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := (Ideal.IsHomogeneous.iff_exists _ J).1 h
    refine ⟨Subtype.val '' S, ?_, hS⟩
    rintro _ ⟨x, -, rfl⟩
    obtain ⟨i, hi⟩ := x.2
    exact ⟨_, isMultiHomog_of_mem_lex e hi⟩
  · rintro ⟨S, hS, rfl⟩
    apply Ideal.homogeneous_span
    intro x hx
    obtain ⟨a, ha⟩ := hS x hx
    exact ⟨_, mem_lex_of_isMultiHomog e ha⟩

end Lex

section Filtration

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_one : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
    by_contra h
    exact hm (if_neg (Ne.symm h))
  simp [hm0]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem exists_colon_prime (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) (hJt : J ≠ ⊤) :
    ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∉ J ∧
      (J.colon {f}).IsPrime ∧ IsMultiHomogIdeal (J.colon {f}) := by
  let e := Fintype.equivFin K
  have hJh : J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) :=
    (isHomogeneous_lex_iff e J).2 hJ

  have hcolh : ∀ (f : MRing ι) (d : Lex (Fin (Fintype.card K) → ℕ)),
      f ∈ weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e) d →
      (J.colon {f}).IsHomogeneous (weightedHomogeneousSubmodule ℤ (lexW (ι := ι) e)) := by
    intro f d hf i g hg
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
    rw [← DirectSum.coe_decompose_mul_add_of_right_mem _ hf]
    exact hJh (i + d) hg

  let S : Set (Ideal (MRing ι)) := {P | ∃ (f : MRing ι) (c : K → ℕ), IsMultiHomog f c ∧ f ∉ J ∧ P = J.colon {f}}
  have hne : S.Nonempty := by
    refine ⟨J.colon {1}, ?_⟩
    simp only [S, Set.mem_setOf_eq]
    exact ⟨1, 0, isMultiHomog_one, fun h => hJt ((Ideal.eq_top_iff_one J).2 h), rfl⟩
  obtain ⟨P, hP, hmax⟩ :=
    set_has_maximal_iff_noetherian.2 (inferInstance : IsNoetherian (MRing ι) (MRing ι)) S hne
  obtain ⟨f, c, hf, hfJ, rfl⟩ := hP
  have hfm := mem_lex_of_isMultiHomog e hf
  have hPh := hcolh f _ hfm
  refine ⟨f, c, hf, hfJ, ?_, (isHomogeneous_lex_iff e _).1 hPh⟩
  apply Ideal.IsHomogeneous.isPrime_of_homogeneous_mem_or_mem hPh
  · intro h
    apply hfJ
    have h1 : (1 : MRing ι) ∈ J.colon {f} := by rw [h]; exact Submodule.mem_top
    rwa [Submodule.mem_colon_singleton, one_smul] at h1
  · rintro x y ⟨i, hx⟩ ⟨j, hy⟩ hxy
    by_cases hxP : x ∈ J.colon {f}
    · exact Or.inl hxP
    right
    have hxf := SetLike.GradedMul.mul_mem hx hfm
    have hxfJ : x * f ∉ J := by rwa [Submodule.mem_colon_singleton, smul_eq_mul] at hxP
    have hmem : J.colon {x * f} ∈ S := by
      simp only [S, Set.mem_setOf_eq]
      exact ⟨x * f, _, isMultiHomog_of_mem_lex e hxf, hxfJ, rfl⟩
    have hle : J.colon {f} ≤ J.colon {x * f} := by
      intro g hg
      rw [Submodule.mem_colon_singleton, smul_eq_mul] at hg ⊢
      rw [← mul_assoc, mul_comm g x, mul_assoc]
      exact J.mul_mem_left x hg
    have heq : J.colon {f} = J.colon {x * f} := by
      by_contra hne'
      exact hmax _ hmem (lt_of_le_of_ne hle hne')
    rw [heq, Submodule.mem_colon_singleton, smul_eq_mul]
    rw [Submodule.mem_colon_singleton, smul_eq_mul] at hxy
    rw [← mul_assoc, mul_comm y x]
    exact hxy

theorem isMultiHomogIdeal_sup_span {J : Ideal (MRing ι)} (hJ : IsMultiHomogIdeal J) {f : MRing ι}
    {c : K → ℕ} (hf : IsMultiHomog f c) : IsMultiHomogIdeal (J ⊔ Ideal.span {f}) := by
  obtain ⟨S, hS, rfl⟩ := hJ
  refine ⟨S ∪ {f}, ?_, (Ideal.span_union _ _).symm⟩
  rintro g (hg | hg)
  · exact hS g hg
  · rw [Set.mem_singleton_iff.mp hg]
    exact ⟨c, hf⟩

theorem exists_primeFiltration_of_isMultiHomogIdeal (J : Ideal (MRing ι)) (hJ : IsMultiHomogIdeal J) :
    ∃ (N : ℕ) (F : Fin (N + 1) → Ideal (MRing ι)) (f : Fin N → MRing ι) (c : Fin N → K → ℕ)
      (q : Fin N → Ideal (MRing ι)),
      F 0 = J ∧ F (Fin.last N) = ⊤ ∧ ∀ j : Fin N,
        IsMultiHomog (f j) (c j) ∧ F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧
        (q j).IsPrime ∧ IsMultiHomogIdeal (q j) ∧
        ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc := by
  induction J using WellFoundedGT.induction
  rename_i J ih
  by_cases hJt : J = ⊤
  · exact ⟨0, fun _ => J, Fin.elim0, Fin.elim0, Fin.elim0, rfl, hJt, fun j => Fin.elim0 j⟩
  obtain ⟨f, c, hf, hfJ, hprime, hqh⟩ := exists_colon_prime J hJ hJt
  have hlt : J < J ⊔ Ideal.span {f} := lt_of_le_of_ne le_sup_left fun h =>
    hfJ (h ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
  obtain ⟨N, F, g, cc, q, hF0, hFl, hstep⟩ := ih _ hlt (isMultiHomogIdeal_sup_span hJ hf)
  refine ⟨N + 1, Fin.cons J F, Fin.cons f g, Fin.cons c cc, Fin.cons (J.colon {f}) q, rfl, ?_, ?_⟩
  · rw [← Fin.succ_last, Fin.cons_succ]
    exact hFl
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · refine ⟨by simpa using hf, ?_, by simpa using hprime, by simpa using hqh, fun g' => ?_⟩
      · simp [hF0]
      · simp [Submodule.mem_colon_singleton, smul_eq_mul]
    · simp only [← Fin.succ_castSucc, Fin.cons_succ]
      exact hstep j

end Filtration

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.StepTStB
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

theorem ringKrullDim_le_of_isIntegral' {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] : ringKrullDim S ≤ ringKrullDim R := by
  unfold ringKrullDim
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  intro P Q hPQ
  exact Ideal.IsIntegral.comap_lt_comap (I := P.asIdeal) (J := Q.asIdeal) hPQ

section Arith

variable {Ω : Type*} [Field Ω] [CharZero Ω]

theorem X_mem_coordIdeal_iff {J : Type} (v : J → Ω) (i : J) :
    (X i : MvPolynomial J ℤ) ∈ coordIdeal ℤ v ↔ v i = 0 := by
  rw [coordIdeal, RingHom.mem_ker, coneMap, aeval_X, mul_eq_zero, Polynomial.C_eq_zero]
  simp [Polynomial.X_ne_zero]

theorem isHorizontal_coordIdeal {κ : Type} (v : Ix κ → Ω) :
    IsHorizontal (ι := GlobalTheory κ) (coordIdeal ℤ v) := by
  rw [IsHorizontal, eq_bot_iff]
  intro n hn
  rw [Ideal.mem_comap, coordIdeal, RingHom.mem_ker, coneMap, aeval_C] at hn
  rw [Submodule.mem_bot]
  simpa using hn

theorem isMultiHomogIdeal_coordIdeal {κ : Type} [Fintype κ] (v : Ix κ → Ω) :
    IsMultiHomogIdeal (ι := GlobalTheory κ) (coordIdeal ℤ v) := by
  refine ⟨{f | f ∈ coordIdeal ℤ v ∧ ∃ n, f.IsHomogeneous n}, ?_, ?_⟩
  · rintro f ⟨_, n, hn⟩
    refine ⟨fun _ => n, fun m hm k => ?_⟩
    have h1 : Finsupp.degree m = n := by
      rw [Finsupp.degree_eq_weight_one]
      exact hn (mem_support_iff.mp hm)
    rw [Finsupp.degree_eq_sum, Fintype.sum_sigma] at h1
    cases k
    simpa using h1
  · apply le_antisymm
    · intro f hf
      rw [← sum_homogeneousComponent f]
      exact Ideal.sum_mem _ fun d _ => Ideal.subset_span
        ⟨coordIdeal_isHomogIdeal ℤ v f hf d, d, homogeneousComponent_isHomogeneous d f⟩
    · exact Ideal.span_le.mpr fun f hf => hf.1

theorem coneMap_rename {J J' : Type} (v : J → Ω) (e : J' → J) (p : MvPolynomial J' ℤ) :
    coneMap ℤ v (rename e p) = coneMap ℤ (v ∘ e) p := by
  rw [coneMap, coneMap, aeval_rename]
  rfl

end Arith

section Dim

variable {Ω : Type*} [Field Ω] [CharZero Ω] {J : Type} [Fintype J] {D : ℕ}

theorem isIntegralElem_of_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (val : S →+* T) (hval : Function.Injective val) {s : S}
    (h : (val.comp f).IsIntegralElem (val s)) : f.IsIntegralElem s := by
  obtain ⟨p, hp, he⟩ := h
  refine ⟨p, hp, hval ?_⟩
  rw [map_zero, ← he, Polynomial.hom_eval₂]

theorem isIntegralElem_coneMap (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e)
    (q : MvPolynomial J ℤ) :
    (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).IsIntegralElem
      (coneMap ℤ v q) := by
  have hinj : Function.Injective (coneMap ℤ (v ∘ e)) := by
    rw [injective_iff_map_eq_zero]
    intro p hp
    have : p ∈ coordIdeal ℤ (v ∘ e) := by simpa [coordIdeal, RingHom.mem_ker] using hp
    rw [hf.free] at this
    exact (Ideal.mem_bot).mp this
  set φ := AlgEquiv.ofInjective (coneMap ℤ (v ∘ e)) hinj
  have hgen : ∀ i, (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).IsIntegralElem
      (Polynomial.C (v i) * Polynomial.X) := by
    intro i
    have hi : IsIntegral (coneMap ℤ (v ∘ e)).range (Polynomial.C (v i) * Polynomial.X : Polynomial Ω) :=
      hf.integral i
    obtain ⟨p, hp, hps⟩ := hi
    refine ⟨p.map φ.symm.toRingEquiv.toRingHom,
      hp.map _, ?_⟩
    have hcomp : ((coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω).comp
        φ.symm.toRingEquiv.toRingHom) = algebraMap (coneMap ℤ (v ∘ e)).range (Polynomial Ω) := by
      refine RingHom.ext fun r => ?_
      have h1 : ((φ (φ.symm r) : (coneMap ℤ (v ∘ e)).range) : Polynomial Ω) =
          coneMap ℤ (v ∘ e) (φ.symm r) := rfl
      rw [AlgEquiv.apply_symm_apply] at h1
      exact h1.symm
    rw [Polynomial.eval₂_map, hcomp]
    exact hps
  induction q using MvPolynomial.induction_on with
  | C a =>
    have : coneMap ℤ v (C a) = coneMap ℤ (v ∘ e) (C a) := by simp
    rw [this]
    exact RingHom.isIntegralElem_map _
  | add p q hp hq =>
    rw [map_add]
    exact RingHom.IsIntegralElem.add _ hp hq
  | mul_X p i hp =>
    rw [map_mul]
    refine RingHom.IsIntegralElem.mul _ hp ?_
    simpa [coneMap] using hgen i

theorem coneMap_injective_of_frame (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e) :
    Function.Injective (coneMap ℤ (v ∘ e)) := by
  exact (injective_iff_map_eq_zero _).2 fun p hp => by
    have h : p ∈ coordIdeal ℤ (v ∘ e) := (RingHom.mem_ker).2 hp
    rwa [hf.free, Ideal.mem_bot] at h

theorem ringKrullDim_mvPoly_fin_int :
    ringKrullDim (MvPolynomial (Fin (D + 1)) ℤ) = ((D + 2 : ℕ) : WithBot ℕ∞) := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField,
    Nat.card_eq_fintype_card, Fintype.card_fin]
  rw [show ((D + 2 : ℕ) : WithBot ℕ∞) = 1 + ((D + 1 : ℕ) : WithBot ℕ∞) by norm_cast; omega]

theorem ringKrullDim_quot_of_frame (v : J → Ω) (e : Fin (D + 1) → J) (hf : IsProjFrame v e) :
    ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ v) = ((D + 2 : ℕ) : WithBot ℕ∞) := by
  have hq : ringKrullDim (MvPolynomial J ℤ ⧸ coordIdeal ℤ v) =
      ringKrullDim (coneMap ℤ v).range :=
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (coneMap ℤ v)).toRingEquiv
  let f : MvPolynomial (Fin (D + 1)) ℤ →+* (coneMap ℤ v).range :=
    ((coneMap ℤ v).rangeRestrict.comp (rename e)).toRingHom
  have hvalf : ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω).comp f =
      (coneMap ℤ (v ∘ e) : MvPolynomial (Fin (D + 1)) ℤ →+* Polynomial Ω) := by
    refine RingHom.ext fun p => ?_
    simp [f, coneMap_rename]
  have hinj : Function.Injective f := by
    intro a b hab
    apply coneMap_injective_of_frame v e hf
    have := congrArg ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω) hab
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, hvalf] at this
    exact this
  have hint : f.IsIntegral := fun s => by
    obtain ⟨q, hq⟩ := s.2
    apply isIntegralElem_of_comp f ((coneMap ℤ v).range.val : (coneMap ℤ v).range →+* Polynomial Ω)
      Subtype.val_injective
    rw [hvalf]
    change RingHom.IsIntegralElem _ (s : Polynomial Ω)
    rw [← hq]
    exact isIntegralElem_coneMap v e hf q
  rw [hq]
  apply le_antisymm
  · let _ := f.toAlgebra
    have : Algebra.IsIntegral (MvPolynomial (Fin (D + 1)) ℤ) (coneMap ℤ v).range := ⟨hint⟩
    rw [← ringKrullDim_mvPoly_fin_int]
    exact ringKrullDim_le_of_isIntegral'
  · exact le_ringKrullDim_of_isIntegral f hint hinj _ ringKrullDim_mvPoly_fin_int.ge

end Dim

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
end
end

