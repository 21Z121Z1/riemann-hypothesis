import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0012
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubringNoMonicFactorisationSpecialisation
section
open Polynomial

namespace GlobalTheory.FactorCertificate

noncomputable def monicOf {R : Type} [CommRing R] {d m : ℕ} (v : Fin d × Fin (m + 1) → R) :
    R[X][X] :=
  X ^ d + ∑ i : Fin d, C (∑ j : Fin (m + 1), C (v (i, j)) * X ^ (j : ℕ)) * X ^ (i : ℕ)

theorem map_monicOf {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {d m : ℕ}
    (v : Fin d × Fin (m + 1) → R) :
    (monicOf v).map (mapRingHom f) = monicOf (fun x => f (v x)) := by
  simp [monicOf, Polynomial.map_sum]

theorem coeff_monicOf {R : Type} [CommRing R] {d m : ℕ} (v : Fin d × Fin (m + 1) → R) :
    (monicOf v).coeff d = 1 := by
  rw [monicOf, coeff_add, coeff_X_pow_self, finsetSum_coeff, Finset.sum_eq_zero, add_zero]
  intro i _
  rw [coeff_C_mul_X_pow, if_neg i.2.ne']

theorem monicOf_coeff {R : Type} [CommRing R] (A : R[X][X]) (hA : A.Monic) {d m : ℕ}
    (hd : A.natDegree = d) (hm : ∀ i, (A.coeff i).natDegree ≤ m) :
    monicOf (fun x : Fin d × Fin (m + 1) => (A.coeff x.1).coeff x.2) = A := by
  subst hd
  conv_rhs => rw [hA.as_sum]
  rw [monicOf, ← Fin.sum_univ_eq_sum_range (fun i => C (A.coeff i) * X ^ i)]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  rw [Fin.sum_univ_eq_sum_range (fun j => C ((A.coeff i).coeff j) * X ^ j)]
  exact ((A.coeff i).as_sum_range_C_mul_X_pow' (Nat.lt_succ_of_le (hm i))).symm

abbrev Unk (a b m : ℕ) : Type := (Fin a × Fin (m + 1)) ⊕ (Fin b × Fin (m + 1))

noncomputable def eqn {R : Type} [CommRing R] (Ψ : R[X][X]) (a b m : ℕ) (p : ℕ × ℕ) :
    MvPolynomial (Unk a b m) R :=
  ((monicOf (fun x => (MvPolynomial.X (Sum.inl x) : MvPolynomial (Unk a b m) R)) *
    monicOf (fun x => (MvPolynomial.X (Sum.inr x) : MvPolynomial (Unk a b m) R)) -
    Ψ.map (mapRingHom MvPolynomial.C)).coeff p.1).coeff p.2

theorem ringHom_eqn {R S : Type} [CommRing R] [CommRing S] (Ψ : R[X][X]) (a b m : ℕ)
    (g : MvPolynomial (Unk a b m) R →+* S) (p : ℕ × ℕ) :
    g (eqn Ψ a b m p) =
      ((monicOf (fun x => g (MvPolynomial.X (Sum.inl x))) *
        monicOf (fun x => g (MvPolynomial.X (Sum.inr x))) -
        Ψ.map (mapRingHom (g.comp MvPolynomial.C))).coeff p.1).coeff p.2 := by
  rw [eqn, ← coeff_map g, ← coe_mapRingHom, ← coeff_map (mapRingHom g), Polynomial.map_sub,
    Polynomial.map_mul, map_monicOf, map_monicOf, Polynomial.map_map, mapRingHom_comp]

theorem map_eqn {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (Ψ : R[X][X]) (a b m : ℕ)
    (p : ℕ × ℕ) :
    MvPolynomial.map f (eqn Ψ a b m p) = eqn (Ψ.map (mapRingHom f)) a b m p := by
  rw [ringHom_eqn, eqn, Polynomial.map_map, mapRingHom_comp]
  have : (MvPolynomial.map f : MvPolynomial (Unk a b m) R →+* _).comp MvPolynomial.C =
      MvPolynomial.C.comp f := by
    ext; simp
  simp only [MvPolynomial.map_X, this]

theorem one_mem_span {F : Type} [Field F] [IsAlgClosed F] (Φ : F[X][X]) (hΦ : Irreducible Φ)
    (a b m : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    (1 : MvPolynomial (Unk a b m) F) ∈ Ideal.span (Set.range (eqn Φ a b m)) := by
  by_contra h
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ ((Ideal.ne_top_iff_one _).2 h)
  obtain ⟨x, rfl⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton).1 hM
  have h0 : ∀ p, MvPolynomial.eval x (eqn Φ a b m p) = 0 := fun p => by
    have := (MvPolynomial.mem_vanishingIdeal_singleton_iff x _).1
      (hle (Ideal.subset_span ⟨p, rfl⟩))
    simpa [MvPolynomial.aeval_eq_eval] using this
  have hc : (MvPolynomial.eval x).comp MvPolynomial.C = RingHom.id F := by
    ext; simp
  have hAB : Φ = monicOf (fun y => x (Sum.inl y)) * monicOf (fun y => x (Sum.inr y)) := by
    symm
    rw [← sub_eq_zero]
    ext i j
    have := h0 (i, j)
    rw [ringHom_eqn, hc] at this
    simpa using this
  have key : ∀ {d : ℕ} (v : Fin d × Fin (m + 1) → F), d ≠ 0 → ¬ IsUnit (monicOf v) := by
    intro d v hd hu
    have h1 := natDegree_eq_zero_of_isUnit hu
    have h2 : d ≤ (monicOf v).natDegree :=
      le_natDegree_of_ne_zero (by rw [coeff_monicOf]; exact one_ne_zero)
    omega
  rcases hΦ.isUnit_or_isUnit hAB with hu | hu
  · exact key _ ha hu
  · exact key _ hb hu

theorem descend {F : Type} [CommRing F] (Φ : F[X][X]) (a b m : ℕ)
    (h : (1 : MvPolynomial (Unk a b m) F) ∈ Ideal.span (Set.range (eqn Φ a b m))) :
    ∃ s : Finset F, ∀ R : Subring F, (s : Set F) ⊆ R → ∀ Ψ : R[X][X],
      Ψ.map (mapRingHom R.subtype) = Φ →
      (1 : MvPolynomial (Unk a b m) R) ∈ Ideal.span (Set.range (eqn Ψ a b m)) := by
  classical
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 h
  refine ⟨c.support.biUnion fun e => (c e).coeffs, fun R hR Ψ hΨ => ?_⟩
  have hl : ∀ e, ∃ q : MvPolynomial (Unk a b m) R,
      e ∈ c.support → MvPolynomial.map R.subtype q = c e := by
    intro e
    by_cases he : e ∈ c.support
    · have : c e ∈ Set.range (MvPolynomial.map (σ := Unk a b m) R.subtype) := by
        rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
        intro y hy
        exact ⟨⟨y, hR (by
          simp only [Finset.coe_biUnion, Set.mem_iUnion]
          exact ⟨e, he, hy⟩)⟩, rfl⟩
      obtain ⟨q, hq⟩ := this
      exact ⟨q, fun _ => hq⟩
    · exact ⟨0, fun h => absurd h he⟩
  choose q hq using hl
  have h1 : ∑ e ∈ c.support, q e * eqn Ψ a b m e = 1 := by
    apply MvPolynomial.map_injective R.subtype Subtype.val_injective
    rw [map_sum, map_one, ← hc, Finsupp.sum]
    refine Finset.sum_congr rfl fun e he => ?_
    rw [map_mul, hq e he, map_eqn, hΨ, smul_eq_mul]
  rw [← h1]
  exact Ideal.sum_mem _ fun e _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨e, rfl⟩)

theorem false_of_one_mem {R k : Type} [CommRing R] [CommRing k] [Nontrivial k] (Ψ : R[X][X])
    (a b m : ℕ)
    (h : (1 : MvPolynomial (Unk a b m) R) ∈ Ideal.span (Set.range (eqn Ψ a b m)))
    (φ : R →+* k) (A B : k[X][X]) (hA : A.Monic) (hB : B.Monic) (ha : A.natDegree = a)
    (hb : B.natDegree = b) (hAm : ∀ i, (A.coeff i).natDegree ≤ m)
    (hBm : ∀ i, (B.coeff i).natDegree ≤ m) (hAB : A * B = Ψ.map (mapRingHom φ)) : False := by
  let x : Unk a b m → k :=
    Sum.elim (fun y => (A.coeff y.1).coeff y.2) (fun y => (B.coeff y.1).coeff y.2)
  let g : MvPolynomial (Unk a b m) R →+* k := MvPolynomial.eval₂Hom φ x
  have hc : g.comp MvPolynomial.C = φ := by
    ext; simp [g]
  have hle : Ideal.span (Set.range (eqn Ψ a b m)) ≤ RingHom.ker g := by
    rw [Ideal.span_le]
    rintro _ ⟨p, rfl⟩
    have e1 : (fun y => g (MvPolynomial.X (Sum.inl y))) =
        fun y : Fin a × Fin (m + 1) => (A.coeff y.1).coeff y.2 := by
      funext y; simp [g, x]
    have e2 : (fun y => g (MvPolynomial.X (Sum.inr y))) =
        fun y : Fin b × Fin (m + 1) => (B.coeff y.1).coeff y.2 := by
      funext y; simp [g, x]
    change g _ = 0
    rw [ringHom_eqn, hc, e1, e2, monicOf_coeff A hA ha hAm, monicOf_coeff B hB hb hBm, hAB,
      sub_self, coeff_zero, coeff_zero]
  have := hle h
  rw [RingHom.mem_ker, map_one] at this
  exact one_ne_zero this

theorem exists_subring_no_monic_factorisation {F : Type} [Field F] [IsAlgClosed F]
    (Φ : Polynomial (Polynomial F)) (hm : Φ.Monic) (hΦ : Irreducible Φ) :
    ∃ s : Finset F, ∃ Ψ : Polynomial (Polynomial (Subring.closure (s : Set F))),
      Ψ.map (Polynomial.mapRingHom (Subring.closure (s : Set F)).subtype) = Φ ∧
      ∀ (k : Type) [Field k] (φ : Subring.closure (s : Set F) →+* k)
        (A B : Polynomial (Polynomial k)), A.Monic → B.Monic →
        A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
  classical
  set d := Φ.natDegree with hd
  set D := Φ.support.sup fun i => (Φ.coeff i).natDegree with hD
  have hDle : ∀ i, (Φ.coeff i).natDegree ≤ D := fun i => by
    by_cases hi : i ∈ Φ.support
    · exact Finset.le_sup (f := fun i => (Φ.coeff i).natDegree) hi
    · rw [notMem_support_iff.1 hi]; simp
  have hex : ∀ p : ℕ × ℕ, ∃ s : Finset F, p.1 ≠ 0 → p.2 ≠ 0 → ∀ R : Subring F, (s : Set F) ⊆ R →
      ∀ Ψ : R[X][X], Ψ.map (mapRingHom R.subtype) = Φ →
      (1 : MvPolynomial (Unk p.1 p.2 (d * D)) R) ∈
        Ideal.span (Set.range (eqn Ψ p.1 p.2 (d * D))) := by
    intro p
    by_cases h : p.1 ≠ 0 ∧ p.2 ≠ 0
    · obtain ⟨s, hs⟩ := descend Φ _ _ _ (one_mem_span Φ hΦ p.1 p.2 (d * D) h.1 h.2)
      exact ⟨s, fun _ _ => hs⟩
    · exact ⟨∅, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose s₀ hs₀ using hex
  let s : Finset F := (Φ.support.biUnion fun i => (Φ.coeff i).coeffs) ∪
    (Finset.range (d + 1) ×ˢ Finset.range (d + 1)).biUnion s₀
  set R := Subring.closure (s : Set F) with hR
  have hinj : Function.Injective (mapRingHom R.subtype) :=
    Polynomial.map_injective _ Subtype.val_injective
  have hlift : Φ ∈ lifts (mapRingHom R.subtype) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    have : Φ.coeff i ∈ lifts R.subtype := by
      rw [lifts_iff_coeff_lifts]
      intro j
      by_cases h0 : (Φ.coeff i).coeff j = 0
      · exact ⟨0, by simp [h0]⟩
      · refine ⟨⟨_, Subring.subset_closure ?_⟩, rfl⟩
        have hi : i ∈ Φ.support := mem_support_iff.2 fun h => h0 (by rw [h, coeff_zero])
        exact Finset.mem_coe.2 (Finset.mem_union_left _
          (Finset.mem_biUnion.2 ⟨i, hi, coeff_mem_coeffs h0⟩))
    exact this
  obtain ⟨Ψ, hΨ⟩ := hlift
  replace hΨ : Ψ.map (mapRingHom R.subtype) = Φ := hΨ
  refine ⟨s, Ψ, hΨ, fun k _ φ A B hA hB hAB => ?_⟩
  by_contra hcon
  rw [not_or] at hcon
  have hΨm : Ψ.Monic := monic_of_injective hinj (hΨ ▸ hm)
  have hΨd : Ψ.natDegree = d := by
    rw [hd, ← hΨ, natDegree_map_eq_of_injective hinj]
  have hφd : (Ψ.map (mapRingHom φ)).natDegree = d := by
    rw [hΨm.natDegree_map, hΨd]
  have hφD : ∀ i, ((Ψ.map (mapRingHom φ)).coeff i).natDegree ≤ D := fun i => by
    rw [coeff_map, coe_mapRingHom]
    refine natDegree_map_le.trans (le_trans (le_of_eq ?_) (hDle i))
    rw [← hΨ, coeff_map, coe_mapRingHom, natDegree_map_eq_of_injective Subtype.val_injective]
  have hsum : A.natDegree + B.natDegree = d := by
    rw [← hA.natDegree_mul hB, hAB, hφd]
  have hsub : (s₀ (A.natDegree, B.natDegree) : Set F) ⊆ R := fun y hy =>
    Subring.subset_closure (Finset.mem_coe.2 (Finset.mem_union_right _
      (Finset.mem_biUnion.2 ⟨_, Finset.mem_product.2
        ⟨Finset.mem_range.2 (by simp only; omega), Finset.mem_range.2 (by simp only; omega)⟩, hy⟩)))
  refine false_of_one_mem Ψ _ _ _ (hs₀ (A.natDegree, B.natDegree) hcon.1 hcon.2 R hsub Ψ hΨ)
    φ A B hA hB rfl rfl ?_ ?_ hAB
  · rw [← hφd]
    exact GlobalTheory.MonicFactorDegree.monic_factor_coeff_natDegree_le _ A B D (hΨm.map _) hA hB
      hAB.symm hφD
  · rw [← hφd]
    exact GlobalTheory.MonicFactorDegree.monic_factor_coeff_natDegree_le _ B A D (hΨm.map _) hB hA
      (by rw [mul_comm, hAB]) hφD

end GlobalTheory.FactorCertificate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteGaloisApproximation
section
open GlobalTheory.K5

namespace GlobalTheory.K5

theorem gal_finite_subcover : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ S : Gal p Ω → Finset Ω, ∃ F : Finset (Gal p Ω), ∀ h : Gal p Ω, ∃ g ∈ F, ∀ x ∈ S g, h x = g x := by
  intro p _ Ω _ _ hΩ S
  classical
  letI : TopologicalSpace Ω := ⊥
  haveI : DiscreteTopology Ω := ⟨rfl⟩
  haveI : IsDomain (O0 p) := hΩ.inj.isDomain (algebraMap (O0 p) Ω)
  haveI : Module.IsTorsionFree (O0 p) Ω := Module.isTorsionFree_iff_algebraMap_injective.mpr hΩ.inj
  haveI := hΩ.alg
  choose P hP0 hP using fun x : Ω => (Algebra.IsAlgebraic.isAlgebraic (R := O0 p) x)
  have hmap : ∀ x, (P x).map (algebraMap (O0 p) Ω) ≠ 0 := fun x =>
    (Polynomial.map_ne_zero_iff hΩ.inj).mpr (hP0 x)
  let R : Ω → Set Ω := fun x => (((P x).map (algebraMap (O0 p) Ω)).roots.toFinset : Set Ω)
  have hR : ∀ (φ : Ω →ₐ[O0 p] Ω) x, φ x ∈ R x := by
    intro φ x
    simp only [R, Finset.mem_coe, Multiset.mem_toFinset]
    rw [Polynomial.mem_roots (hmap x), Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def,
      Polynomial.aeval_algHom_apply, hP x, map_zero]
  let K : Set (Ω → Ω) := Set.pi Set.univ R
  have hK : IsCompact K := isCompact_univ_pi (fun x => (Finset.finite_toSet _).isCompact)
  let C : Set (Ω → Ω) := (⋂ a, ⋂ b, {f | f (a + b) = f a + f b}) ∩ (⋂ a, ⋂ b, {f | f (a * b) = f a * f b})
      ∩ {f | f 1 = 1} ∩ ⋂ r : O0 p, {f | f (algebraMap (O0 p) Ω r) = algebraMap (O0 p) Ω r}
  have hC : IsClosed C := by
    have key : ∀ (u : (Ω → Ω) → Ω × Ω × Ω), Continuous u → ∀ T : Set (Ω × Ω × Ω),
        IsClosed (u ⁻¹' T) := fun u hu T => (isClosed_discrete T).preimage hu
    refine IsClosed.inter (IsClosed.inter (IsClosed.inter ?_ ?_) ?_) ?_
    · refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
      exact key (fun f => (f (a + b), f a, f b)) (by fun_prop) {t | t.1 = t.2.1 + t.2.2}
    · refine isClosed_iInter fun a => isClosed_iInter fun b => ?_
      exact key (fun f => (f (a * b), f a, f b)) (by fun_prop) {t | t.1 = t.2.1 * t.2.2}
    · exact key (fun f => (f 1, f 1, f 1)) (by fun_prop) {t | t.1 = 1}
    · refine isClosed_iInter fun r => ?_
      exact key (fun f => (f (algebraMap (O0 p) Ω r), f 1, f 1)) (by fun_prop)
        {t | t.1 = algebraMap (O0 p) Ω r}
  let U : Gal p Ω → Set (Ω → Ω) := fun g => ⋂ x ∈ S g, (fun f => f x) ⁻¹' {g x}
  have hU : ∀ g, IsOpen (U g) := fun g =>
    isOpen_biInter_finset (fun x _ => (isOpen_discrete {g x}).preimage (continuous_apply x))
  have hcov : K ∩ C ⊆ ⋃ g, U g := by
    rintro f ⟨-, ⟨⟨hadd, hmul⟩, h1⟩, halg⟩
    simp only [Set.mem_iInter, Set.mem_setOf_eq] at hadd hmul h1 halg
    have h0 : f 0 = 0 := by
      have := hadd 0 0
      simp only [add_zero] at this
      exact left_eq_add.mp this
    let φ : Ω →ₐ[O0 p] Ω :=
      { toFun := f, map_one' := h1, map_mul' := hmul, map_zero' := h0, map_add' := hadd,
        commutes' := halg }
    let e : Gal p Ω := AlgEquiv.ofBijective φ (Algebra.IsAlgebraic.algHom_bijective φ)
    refine Set.mem_iUnion.mpr ⟨e, ?_⟩
    simp only [U, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    intro x _
    rfl
  have hmem : ∀ h : Gal p Ω, (⇑h : Ω → Ω) ∈ K ∩ C := by
    intro h
    refine ⟨fun x _ => hR (h : Ω →ₐ[O0 p] Ω) x, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro a b; exact map_add h a b
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro a b; exact map_mul h a b
    · exact map_one h
    · simp only [Set.mem_iInter, Set.mem_setOf_eq]; intro r; exact h.commutes r
  obtain ⟨F, hF⟩ := (hK.inter_right hC).elim_finite_subcover U hU hcov
  refine ⟨F, fun h => ?_⟩
  obtain ⟨g, hg, hgh⟩ := Set.mem_iUnion₂.mp (hF (hmem h))
  refine ⟨g, hg, fun x hx => ?_⟩
  have := Set.mem_iInter₂.mp hgh x hx
  simpa using this

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankEichlerShimuraCoboundariesOfGammaLe
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices.CobDim

lemma eval_polySlash (w : ℕ) (g : Matrix (Fin 2) (Fin 2) ℤ) (p : ℂ[X]) (x : ℂ) :
    (slP w g p).eval x = ∑ i ∈ Finset.range (w + 1), p.coeff i *
      (((g 0 0 : ℤ) : ℂ) * x + ((g 0 1 : ℤ) : ℂ)) ^ i * (((g 1 0 : ℤ) : ℂ) * x + ((g 1 1 : ℤ) : ℂ)) ^ (w - i) := by
  simp [slP, LinearMap.sum_apply, eval_finset_sum, mul_assoc]

lemma natDeg_lt {w : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1)) : p.natDegree < w + 1 := by
  by_cases h : p = 0
  · simp [h]
  · exact (natDegree_lt_iff_degree_lt h).2 (mem_degreeLT.1 hp)

def upU (M : ℕ) : SL(2, ℤ) := ⟨!![1, (M : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩

lemma upU_mem (M : ℕ) : upU M ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [upU]

def loU (M : ℕ) : SL(2, ℤ) := ⟨!![1, 0; (M : ℤ), 1], by simp [Matrix.det_fin_two]⟩

lemma loU_mem (M : ℕ) : loU M ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp [loU]

lemma eval_shift {w M : ℕ} {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (h : slP w (mat (upU M)) p = p) (x : ℂ) : p.eval (x + M) = p.eval x := by
  have h1 := eval_polySlash w (mat (upU M)) p x
  rw [h] at h1
  rw [h1, eval_eq_sum_range' (natDeg_lt hp)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [upU, mat, add_comm]

lemma eq_const_of_shift {w M : ℕ} (hM : 0 < M) {p : ℂ[X]} (hp : p ∈ degreeLT ℂ (w + 1))
    (h : slP w (mat (upU M)) p = p) : p = C (p.eval 0) := by
  have hroot : ∀ n : ℕ, (p - C (p.eval 0)).IsRoot ((n : ℂ) * M) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := eval_shift hp h ((n : ℂ) * M)
      simp only [IsRoot, eval_sub, eval_C] at ih ⊢
      push_cast
      rw [add_mul, one_mul, this, ih]
  have hinf : {x | (p - C (p.eval 0)).IsRoot x}.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => (n : ℂ) * M) ?_ hroot
    intro a b hab
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    exact_mod_cast mul_right_cancel₀ hM' hab
  exact sub_eq_zero.1 (eq_zero_of_infinite_isRoot _ hinf)

lemma const_eq_zero {w M : ℕ} (hM : 0 < M) (hw : 1 ≤ w) (c : ℂ) (h : slP w (mat (loU M)) (C c) = C c) : c = 0 := by
  have h1 := eval_polySlash w (mat (loU M)) (C c) 1
  rw [h, eval_C, Finset.sum_eq_single 0] at h1
  · simp [loU, mat] at h1
    have hne : ((M : ℂ) + 1) ^ w ≠ 1 := by
      have : (M + 1) ^ w ≠ 1 := by
        have : 1 < (M + 1) ^ w := Nat.one_lt_pow (by omega) (by omega)
        omega
      exact_mod_cast this
    by_contra hc
    exact hne (by
      have := h1.symm
      field_simp at this
      linear_combination this)
  · intro i _ hi
    simp [coeff_C, hi]
  · simp

end GlobalTheory.HeckeFamilyMatrices.CobDim

open GlobalTheory.HeckeFamilyMatrices.CobDim in
theorem GlobalTheory.HeckeFamilyMatrices.finrank_eichlerShimuraCoboundaries_of_Gamma_le : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (w : ℕ), 0 < M → 1 ≤ w →
    CongruenceSubgroup.Gamma M ≤ Γ → Module.finrank ℂ (B1 Γ w) = w + 1 := by
  intro M Γ w hM hw hΓ
  unfold B1
  rw [LinearMap.finrank_range_of_inj, (degreeLTEquiv ℂ (w + 1)).finrank_eq, Module.finrank_fin_fun]
  intro p q hpq
  rw [← sub_eq_zero, ← map_sub] at hpq
  rw [← sub_eq_zero]
  set r := p - q with hr
  have hfix : ∀ γ : Γ, slP w (mat γ) (r : ℂ[X]) = r := by
    intro γ
    have := congrFun hpq γ
    simpa [sub_eq_zero] using this
  have hc := eq_const_of_shift hM r.2 (hfix ⟨upU M, hΓ (upU_mem M)⟩)
  have h0 : (r : ℂ[X]).eval 0 = 0 := by
    apply const_eq_zero hM hw
    rw [← hc]
    exact hfix ⟨loU M, hΓ (loU_mem M)⟩
  ext1
  rw [hc, h0]
  simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FrobeniusPowerBasisIndependent
section
open GlobalTheory.K5 Polynomial
open scoped NNReal

namespace GlobalTheory

theorem laurent_terms_eq_zero_of_order_injOn {K ι : Type*} [Field K] (s : Finset ι)
    (f : ι → LaurentSeries K)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 → (f i).order = (f j).order → i = j)
    (hsum : ∑ i ∈ s, f i = 0) : ∀ i ∈ s, f i = 0 := by
  classical
  by_contra hne
  push Not at hne
  have hnon : (s.filter fun i => f i ≠ 0).Nonempty := by
    obtain ⟨i, hi, hfi⟩ := hne
    exact ⟨i, Finset.mem_filter.2 ⟨hi, hfi⟩⟩
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image _ (fun i => (f i).order) hnon
  obtain ⟨his, hfi⟩ := Finset.mem_filter.1 hi
  have h1 : (∑ j ∈ s, f j).coeff (f i).order = (f i).coeff (f i).order := by
    rw [HahnSeries.coeff_sum]
    refine Finset.sum_eq_single_of_mem i his ?_
    intro j hj hji
    by_cases hfj : f j = 0
    · simp [hfj]
    · apply HahnSeries.coeff_eq_zero_of_lt_order
      exact lt_of_le_of_ne (hmin j (Finset.mem_filter.2 ⟨hj, hfj⟩))
        (fun h => hji (hinj i his j hj hfi hfj h).symm)
  rw [hsum] at h1
  exact hfi (HahnSeries.coeff_order_eq_zero.1 (by simpa using h1.symm))

theorem laurent_pow_indep_over_prime_pow_powers :
    ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (c : ℕ → LaurentSeries (ZMod p)), ∑ i ∈ Finset.range (p ^ n), c i ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ i = 0 → ∀ i < p ^ n, c i = 0 := by
  intro p _ n c hsum i hi
  have hX : ∀ j : ℕ, (HahnSeries.single (1 : ℤ) (1 : ZMod p) : LaurentSeries (ZMod p)) ^ j ≠ 0 :=
    fun j => pow_ne_zero _ (HahnSeries.single_ne_zero one_ne_zero)
  have hord : ∀ j : ℕ, c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j ≠ 0 →
      (c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j).order
        = ((p ^ n : ℕ) : ℤ) * (c j).order + j := by
    intro j hj
    rw [HahnSeries.order_mul (left_ne_zero_of_mul hj) (hX j), HahnSeries.order_pow,
      HahnSeries.order_pow, HahnSeries.order_single one_ne_zero]
    simp
  have key := laurent_terms_eq_zero_of_order_injOn (Finset.range (p ^ n))
    (fun j => c j ^ (p ^ n) * (HahnSeries.single (1 : ℤ) (1 : ZMod p)) ^ j) ?_ hsum i
    (Finset.mem_range.2 hi)
  · exact pow_eq_zero_iff (by omega) |>.1 ((mul_eq_zero.1 key).resolve_right (hX i))
  · intro a ha b hb hfa hfb h
    have h' := (hord a hfa).symm.trans (h.trans (hord b hfb))
    have ha' := Finset.mem_range.1 ha
    have hb' := Finset.mem_range.1 hb
    have hm := congrArg (fun z : ℤ => z % ((p ^ n : ℕ) : ℤ)) h'
    simp only [Int.mul_add_emod_self_left] at hm
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast ha'),
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hb')] at hm
    exact_mod_cast hm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Gamma1InterGamma0ModularFormHasSumQExpansion
section
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem one_mem_strictPeriods_lev (N l : ℕ) :
    (1 : ℝ) ∈ ((lev N l : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.strictPeriods_eq_zmultiples_one_of_T_mem]
  · exact AddSubgroup.mem_zmultiples 1
  · refine ⟨?_, ?_⟩
    · show ModularGroup.T ∈ Gamma1 N
      rw [CongruenceSubgroup.Gamma1_mem]
      simp [ModularGroup.T]
    · show ModularGroup.T ∈ Gamma0 l
      rw [CongruenceSubgroup.Gamma0_mem]
      simp [ModularGroup.T]

theorem lev_hasSum_coef : ∀ (N l : ℕ) (k : ℤ), 0 < N → ∀ (f : ModularForm (lev N l) k) (τ : ℍ),
    HasSum (fun m => coef ⇑f m • Function.Periodic.qParam 1 τ ^ m) (f τ) := by
  intro N l k _ f τ
  have h1 := one_mem_strictPeriods_lev N l
  haveI : Fact (IsCusp OnePoint.infty ((lev N l : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos h1⟩
  exact ModularForm.hasSum_qExpansion f one_pos h1 τ

end GlobalTheory.Hk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnVerticalRayNormIntegralLeStatement
section
open MeasureTheory Filter Topology Set
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrableOn_vertical_ray_norm_integral_le : ∀ (g : ℂ → ℂ) (K c : ℝ) (m : ℕ) (τ : ℂ), ContinuousOn g {z : ℂ | 0 < z.im} → 0 < c →
    (∀ z : ℂ, 1 ≤ z.im → ‖g z‖ ≤ K * Real.exp (-c * z.im) * (1 + ‖z‖) ^ m) → 1 ≤ τ.im →
    IntegrableOn (fun s : ℝ => g (τ + s * Complex.I)) (Ioi 0) ∧
      ‖∫ s in Ioi (0:ℝ), g (τ + s * Complex.I)‖ ≤
        K * Real.exp (-c * τ.im) * (1 + ‖τ‖) ^ m * ∫ s in Ioi (0:ℝ), Real.exp (-c * s) * (1 + s) ^ m := by
  first | exact @GlobalTheory.vertRay_integral_expPow_bound | exact GlobalTheory.vertRay_integral_expPow_bound | (intros; apply GlobalTheory.vertRay_integral_expPow_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsFieldAndPthRootsOfLocalAlgFrobeniusFixedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_and_pthRoots_of_localAlg_frobenius_fixed : ∀ (p : ℕ) [Fact p.Prime] (k A : Type) [Field k] [CharP k p] [CommRing A] [Algebra k A] [IsLocalRing A]
  (T : Finset A) (f : ℕ), 0 < f → Algebra.adjoin k (T : Set A) = ⊤ → (∀ t ∈ T, t ^ p ^ f = t) →
  IsField A ∧ ∀ (y : A) (a : k), y ^ p = algebraMap k A a → ∃ b : k, y = algebraMap k A b := by
  first | exact @GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots | exact GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots | (intros; apply GlobalTheory.localAlg_frob_fixed_isField_and_pth_roots <;> assumption)
end

