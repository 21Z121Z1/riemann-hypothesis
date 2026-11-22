import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAllOnesSumAlgEquivMkDerivation
section
open MvPolynomial

namespace GlobalTheory

theorem sumAlgEquiv_rename_inr_eq_C {σ : Type} {L : ℕ} (q : MvPolynomial σ ℂ) :
    MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.rename Sum.inr q) = MvPolynomial.C q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [sumAlgEquiv_C_inl]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp => simp only [map_mul, hp, rename_X, sumAlgEquiv_X_inr]

theorem coeff_sumAlgEquiv_mkDerivation_gen {σ : Type} {L : ℕ}
    (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ))
    (b : MvPolynomial (Fin L ⊕ σ) ℂ) (m : Fin L →₀ ℕ) :
    MvPolynomial.coeff m (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ
      (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ))
        (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) =
      D (MvPolynomial.coeff m (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ b)) := by
  induction b using MvPolynomial.induction_on generalizing m with
  | C a =>
    have h1 : (MvPolynomial.C a : MvPolynomial (Fin L ⊕ σ) ℂ) = algebraMap ℂ _ a := rfl
    rw [h1, Derivation.map_algebraMap, map_zero, coeff_zero, AlgEquiv.commutes]
    rw [MvPolynomial.algebraMap_apply, MvPolynomial.coeff_C]
    split_ifs
    · exact (D.map_algebraMap a).symm
    · simp
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | mul_X p i hp =>
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_add, map_mul, map_mul, map_mul, coeff_add]
    rcases i with j | v
    · simp only [mkDerivation_X, Sum.elim_inl, map_zero, mul_zero, coeff_zero, zero_add,
        sumAlgEquiv_X_inl]
      rw [mul_comm (X j), coeff_mul_X', coeff_mul_X']
      split_ifs
      · exact hp _
      · exact (D.map_zero).symm
    · simp only [mkDerivation_X, Sum.elim_inr, sumAlgEquiv_X_inr, sumAlgEquiv_rename_inr_eq_C,
        coeff_C_mul, hp]
      rw [mul_comm ((sumAlgEquiv ℂ (Fin L) σ) p) (C (D (X v))),
        mul_comm ((sumAlgEquiv ℂ (Fin L) σ) p) (C (X v)), coeff_C_mul, coeff_C_mul,
        Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      ring

theorem coeff_allOnes_sumAlgEquiv_mkDerivation :
    ∀ {σ : Type} {L : ℕ} (D : Derivation ℂ (MvPolynomial σ ℂ) (MvPolynomial σ ℂ)) (b : MvPolynomial (Fin L ⊕ σ) ℂ), MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (MvPolynomial.mkDerivation ℂ (Sum.elim (fun _ : Fin L => (0 : MvPolynomial (Fin L ⊕ σ) ℂ)) (fun v : σ => MvPolynomial.rename Sum.inr (D (MvPolynomial.X v)))) b)) = D (MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm fun _ : Fin L => (1 : ℕ)) (MvPolynomial.sumAlgEquiv ℂ (Fin L) σ (b))) :=
  fun D b => coeff_sumAlgEquiv_mkDerivation_gen D b _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffAnnihilatedOfAevalMemKerPow
section
open scoped TensorProduct

namespace GlobalTheory.TriangularityLowCoeff

open MvPolynomial

noncomputable def iterDer {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}
    (D : Fin d → Derivation R A A) : List (Fin d) → A →ₗ[R] A
  | [] => LinearMap.id
  | i :: L => (iterDer D L) ∘ₗ (D i).toLinearMap

noncomputable def expOf {d : ℕ} (L : List (Fin d)) : Fin d →₀ ℕ :=
  Multiset.toFinsupp (L : Multiset (Fin d))

noncomputable def fac {d : ℕ} : List (Fin d) → (Fin d →₀ ℕ) → ℕ
  | [], _ => 1
  | i :: L, m => ((m + expOf L) i + 1) * fac L m

theorem expOf_cons {d : ℕ} (i : Fin d) (L : List (Fin d)) :
    expOf (i :: L) = Finsupp.single i 1 + expOf L := by
  rw [expOf, ← Multiset.cons_coe, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_singleton, expOf]

theorem degree_expOf {d : ℕ} (L : List (Fin d)) : (expOf L).degree = L.length := by
  induction L with
  | nil => simp [expOf]
  | cons i L ih => rw [expOf_cons, map_add, ih, Finsupp.degree_single]; simp; omega

theorem expOf_apply_le {d : ℕ} (L : List (Fin d)) (i : Fin d) : expOf L i ≤ L.length := by
  rw [expOf, Multiset.toFinsupp_apply, Multiset.coe_count]
  exact List.count_le_length

theorem expOf_toList {d : ℕ} (α : Fin d →₀ ℕ) : expOf (Finsupp.toMultiset α).toList = α := by
  rw [expOf, Multiset.coe_toList, Finsupp.toMultiset_toFinsupp]

theorem fac_dvd {d : ℕ} (L : List (Fin d)) : fac L 0 ∣ (L.length).factorial ^ L.length := by
  induction L with
  | nil => simp [fac]
  | cons i L ih =>
    simp only [fac, zero_add, List.length_cons]
    rw [pow_succ']
    refine mul_dvd_mul (Nat.dvd_factorial (by omega) (by have := expOf_apply_le L i; omega)) ?_
    exact ih.trans (pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial (by omega)) _)

theorem der_mem_pow {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
    (D : Derivation R A A) (J : Ideal A) : ∀ (k : ℕ) (x : A), x ∈ J ^ (k + 1) → D x ∈ J ^ k
  | 0, x, _ => by simp
  | k + 1, x, hx => by
    rw [pow_succ'] at hx
    refine Submodule.mul_induction_on (C := fun x => D x ∈ J ^ (k + 1)) hx ?_ ?_
    · intro a ha b hb
      rw [D.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ ?_ (Ideal.mul_mem_right _ _ hb)
      rw [pow_succ']
      exact Ideal.mul_mem_mul ha (der_mem_pow D J k b hb)
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy

theorem iterDer_mem {R A : Type} [CommRing R] [CommRing A] [Algebra R A] {d : ℕ}
    (D : Fin d → Derivation R A A) (J : Ideal A) :
    ∀ (L : List (Fin d)) (m : ℕ) (x : A), x ∈ J ^ (L.length + m) → iterDer D L x ∈ J ^ m
  | [], m, x, hx => by simpa [iterDer] using hx
  | i :: L, m, x, hx => by
    show iterDer D L (D i x) ∈ J ^ m
    apply iterDer_mem D J L m
    apply der_mem_pow (D i) J
    have e : L.length + m + 1 = (i :: L).length + m := by simp; omega
    rw [e]; exact hx

theorem der_aeval {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (D : Derivation R B B) (y : Fin d → B) (Q : MvPolynomial (Fin d) R) :
    D (aeval y Q) = ∑ j, aeval y (pderiv j Q) * D (y j) := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p i hp =>
    rw [map_mul, aeval_X, D.leibniz, hp, smul_eq_mul, smul_eq_mul]
    simp only [pderiv_mul, pderiv_X, map_add, map_mul, aeval_X, add_mul, Finset.sum_add_distrib,
      Finset.mul_sum]
    rw [add_comm]
    congr 1
    · exact Finset.sum_congr rfl fun j _ => by ring
    · rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj; simp [Pi.single_apply, hj]
      · simp

theorem coeff_iterPD {R : Type} [CommRing R] {d : ℕ} :
    ∀ (L : List (Fin d)) (m : Fin d →₀ ℕ) (Q : MvPolynomial (Fin d) R),
      coeff m (iterDer (fun i => pderiv i) L Q) = coeff (m + expOf L) Q * (fac L m : R)
  | [], m, Q => by simp [iterDer, expOf, fac]
  | i :: L, m, Q => by
    show coeff m (iterDer (fun i => pderiv i) L (pderiv i Q)) = _
    rw [coeff_iterPD L m, coeff_pderiv, fac, expOf_cons]
    have e : m + expOf L + Finsupp.single i 1 = m + (Finsupp.single i 1 + expOf L) := by abel
    rw [e]; push_cast; ring

theorem aeval_mem_pow {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (hy : ∀ i, ε (y i) = 0) (n : ℕ) (Q : MvPolynomial (Fin d) R)
    (hQ : Q ∈ idealOfVars (Fin d) R ^ n) : aeval y Q ∈ RingHom.ker ε ^ n := by
  have h1 : Ideal.map (aeval y) (idealOfVars (Fin d) R) ≤ RingHom.ker ε := by
    rw [idealOfVars, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    simp [RingHom.mem_ker, hy]
  have h2 := Ideal.mem_map_of_mem (aeval y) hQ
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2

theorem eval_aeval {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (hy : ∀ i, ε (y i) = 0) (Q : MvPolynomial (Fin d) R) :
    ε (aeval y Q) = coeff 0 Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hy, coeff_mul_X']

theorem eval_iterDer_aeval {R B : Type} [CommRing R] [CommRing B] [Algebra R B] {d : ℕ}
    (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B)
    (hy : ∀ i, ε (y i) = 0) (hD : ∀ i j, ε (D i (y j)) = if i = j then 1 else 0) :
    ∀ (L : List (Fin d)) (Q : MvPolynomial (Fin d) R), Q ∈ idealOfVars (Fin d) R ^ L.length →
      ε (iterDer D L (aeval y Q)) = coeff 0 (iterDer (fun i => pderiv i) L Q)
  | [], Q, _ => by simpa [iterDer] using eval_aeval ε y hy Q
  | i :: L, Q, hQ => by
    show ε (iterDer D L (D i (aeval y Q))) = coeff 0 (iterDer (fun i => pderiv i) L (pderiv i Q))
    have hP : ∀ j, pderiv j Q ∈ idealOfVars (Fin d) R ^ L.length := fun j =>
      der_mem_pow (pderiv j) _ L.length Q (by simpa using hQ)
    have key : ∀ j, ε (iterDer D L (aeval y (pderiv j Q) * D i (y j))) =
        ε (D i (y j)) * coeff 0 (iterDer (fun i => pderiv i) L (pderiv j Q)) := by
      intro j
      set x := aeval y (pderiv j Q)
      set u := D i (y j)
      have split : x * u = ε u • x + x * (u - algebraMap R B (ε u)) := by
        rw [Algebra.smul_def]; ring
      have hmem : x * (u - algebraMap R B (ε u)) ∈ RingHom.ker ε ^ (L.length + 1) := by
        rw [pow_succ]
        refine Ideal.mul_mem_mul (aeval_mem_pow ε y hy _ _ (hP j)) ?_
        simp [RingHom.mem_ker]
      have h0 : ε (iterDer D L (x * (u - algebraMap R B (ε u)))) = 0 := by
        have := iterDer_mem D (RingHom.ker ε) L 1 _ hmem
        rw [pow_one, RingHom.mem_ker] at this
        exact this
      rw [split, map_add, map_add, h0, add_zero, map_smul, map_smul, smul_eq_mul,
        eval_iterDer_aeval ε y D hy hD L (pderiv j Q) (hP j)]
    rw [der_aeval, map_sum, map_sum]
    simp only [key, hD, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem exists_mul_coeff_eq_zero (d N : ℕ) : ∃ K : ℕ, 0 < K ∧ ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (y : Fin d → B) (D : Fin d → Derivation R B B), (∀ i, ε (y i) = 0) →
    (∀ i j, ε (D i (y j)) = if i = j then 1 else 0) → ∀ P : MvPolynomial (Fin d) R,
    (∀ α : Fin d →₀ ℕ, N ≤ α.degree → MvPolynomial.coeff α P = 0) →
    MvPolynomial.aeval y P ∈ RingHom.ker ε ^ N → ∀ α, (K : R) * MvPolynomial.coeff α P = 0 := by
  refine ⟨(N.factorial ^ N) ^ N, by positivity, ?_⟩
  intro R B _ _ _ ε y D hy hD P hhi hP
  set c : ℕ := N.factorial ^ N with hc
  have claim : ∀ k, k ≤ N → ∀ α : Fin d →₀ ℕ, α.degree < k → ((c ^ k : ℕ) : R) * coeff α P = 0 := by
    intro k
    induction k with
    | zero => intro _ α h; omega
    | succ k ih =>
      intro hk α hα
      rcases Nat.lt_or_ge α.degree k with h | h
      · rw [pow_succ, Nat.cast_mul, mul_comm ((c ^ k : ℕ) : R), mul_assoc, ih (by omega) α h, mul_zero]
      · have hdeg : α.degree = k := by omega
        set L := (Finsupp.toMultiset α).toList
        have hL : expOf L = α := expOf_toList α
        have hlen : L.length = k := by rw [← degree_expOf, hL, hdeg]
        set P' := C ((c ^ k : ℕ) : R) * P
        have hP'1 : P' ∈ idealOfVars (Fin d) R ^ L.length := by
          rw [mem_pow_idealOfVars_iff', hlen]
          intro β hβ
          rw [coeff_C_mul, ih (by omega) β hβ]
        have hP'2 : aeval y P' ∈ RingHom.ker ε ^ (L.length + 1) := by
          rw [map_mul]
          refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right (by omega) hP)
        have e1 := eval_iterDer_aeval ε y D hy hD L P' hP'1
        have e2 := iterDer_mem D (RingHom.ker ε) L 1 _ hP'2
        rw [pow_one, RingHom.mem_ker, e1, coeff_iterPD, zero_add, hL, coeff_C_mul] at e2
        obtain ⟨g, hg⟩ : fac L 0 ∣ c := by
          refine (fac_dvd L).trans ?_
          rw [hc, hlen]
          exact (pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial (by omega)) k).trans
            (pow_dvd_pow _ (by omega))
        have hg' : (c : R) = (fac L 0 : R) * (g : R) := by rw [hg, Nat.cast_mul]
        push_cast at e2
        calc ((c ^ (k + 1) : ℕ) : R) * coeff α P = (c : R) ^ k * (c : R) * coeff α P := by
              push_cast; ring
          _ = (c : R) ^ k * ((fac L 0 : R) * (g : R)) * coeff α P := by rw [← hg']
          _ = ((c : R) ^ k * coeff α P * (fac L 0 : R)) * g := by ring
          _ = 0 := by rw [e2, zero_mul]
  intro α
  rcases Nat.lt_or_ge α.degree N with h | h
  · exact claim N le_rfl α h
  · rw [hhi α h, mul_zero]

end GlobalTheory.TriangularityLowCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMinpolyMemAdicCompletionIntegers
section
open scoped TensorProduct Classical
open Polynomial

namespace GlobalTheory.DescCoeff

theorem natDegree_minpoly_le_one_tmul {F A : Type} [Field F] [Ring A] [Algebra F A] (K : Type)
    [Field K] [Algebra F K] (g : A) (hK : IsIntegral K ((1 : K) ⊗ₜ[F] g)) :
    (minpoly F g).natDegree ≤ (minpoly K ((1 : K) ⊗ₜ[F] g)).natDegree := by
  set x : K ⊗[F] A := (1 : K) ⊗ₜ[F] g with hx
  have hli : LinearIndependent K (fun j : Fin (minpoly F g).natDegree => x ^ (j : ℕ)) := by
    have h := Module.Flat.linearIndependent_one_tmul (S := K) (linearIndependent_pow (K := F) g)
    convert h using 1
    funext j
    simp [hx, Algebra.TensorProduct.tmul_pow]
  by_contra hlt
  push_neg at hlt
  have hsum := aeval_eq_sum_range' hlt x
  rw [minpoly.aeval, ← Fin.sum_univ_eq_sum_range (fun i => (minpoly K x).coeff i • x ^ i)] at hsum
  have hc := Fintype.linearIndependent_iff.mp hli (fun i => (minpoly K x).coeff i) hsum.symm
  apply minpoly.ne_zero hK
  ext i
  rw [coeff_zero]
  by_cases hi : i < (minpoly F g).natDegree
  · exact hc ⟨i, hi⟩
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem minpoly_one_tmul_eq {F B : Type} [Field F] [Ring B] [Algebra F B] [FiniteDimensional F B]
    (K : Type) [Field K] [Algebra F K] (y : B) :
    minpoly K ((1 : K) ⊗ₜ[F] y) = (minpoly F y).map (algebraMap F K) := by
  set z : K ⊗[F] B := (1 : K) ⊗ₜ[F] y with hz
  have hzi : IsIntegral K z := IsIntegral.of_finite K z
  have hyi : IsIntegral F y := IsIntegral.of_finite F y
  have hzr : z = Algebra.TensorProduct.includeRight y := rfl
  have hdvd : minpoly K z ∣ (minpoly F y).map (algebraMap F K) := by
    apply minpoly.dvd
    rw [aeval_map_algebraMap, hzr, aeval_algHom_apply, minpoly.aeval, map_zero]
  have hge := natDegree_minpoly_le_one_tmul K y hzi
  have := eq_leadingCoeff_mul_of_monic_of_dvd_of_natDegree_le (minpoly.monic hzi) hdvd
    (by rw [natDegree_map]; exact hge)
  rw [this, ((minpoly.monic hyi).map _).leadingCoeff, C_1, one_mul]

end GlobalTheory.DescCoeff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.HilbAff

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

abbrev str : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

def Good (r : ℕ) {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A))
    (I : (pullback (str A B) g).IdealSheafData) : Prop :=
  IsFinite (I.subschemeι ≫ pullback.snd _ g) ∧ Flat (I.subschemeι ≫ pullback.snd _ g) ∧
    ∀ y, (I.subschemeι ≫ pullback.snd _ g).finrank y = r

abbrev bc {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) :
    pullback (str A B) (a ≫ g) ⟶ pullback (str A B) g :=
  pullback.map _ _ _ _ (𝟙 _) a (𝟙 _) (by simp) (by simp)

theorem isPullback_bc {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T) :
    IsPullback (bc A B g a) (pullback.snd _ (a ≫ g)) (pullback.snd _ g) a :=
  by
    have h : bc A B g a ≫ pullback.fst (str A B) g = pullback.fst _ _ :=
      (pullback.lift_fst _ _ _).trans (Category.comp_id _)
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
    rw [h]
    exact IsPullback.of_hasPullback (str A B) (a ≫ g)

theorem good_comap (r : ℕ) {T T' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T)
    (I : (pullback (str A B) g).IdealSheafData) (hI : Good A B r g I) :
    Good A B r (a ≫ g) (I.comap (bc A B g a)) := by
  obtain ⟨h1, h2, h3⟩ := hI
  have H : IsPullback (pullback.snd (bc A B g a) I.subschemeι)
      (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g))
      (I.subschemeι ≫ pullback.snd _ g) a :=
    (IsPullback.of_hasPullback (bc A B g a) I.subschemeι).flip.paste_vert (isPullback_bc A B g a)
  have e : (I.comap (bc A B g a)).subschemeι ≫ pullback.snd _ (a ≫ g) =
      (I.comapIso (bc A B g a)).hom ≫ (pullback.fst (bc A B g a) I.subschemeι ≫
        pullback.snd _ (a ≫ g)) := by
    rw [← Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst]
  have f1 : IsFinite (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) H h1
  have f2 : Flat (pullback.fst (bc A B g a) I.subschemeι ≫ pullback.snd _ (a ≫ g)) :=
    MorphismProperty.of_isPullback (P := @Flat) H h2
  refine ⟨?_, ?_, fun y => ?_⟩
  · rw [e]; infer_instance
  · rw [e]; infer_instance
  · rw [e, Scheme.Hom.finrank_comp_left_of_isIso, Scheme.Hom.finrank_of_isPullback _ _ _ _ H y, h3]

theorem sigma_eq (r : ℕ) {T : Scheme.{0}} {g₀ g : T ⟶ Spec (CommRingCat.of A)} (h : g₀ = g)
    {I₀ : (pullback (str A B) g₀).IdealSheafData} {I : (pullback (str A B) g).IdealSheafData}
    (hI : I₀ = I.comap (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp [h])))
    (h₀ : Good A B r g₀ I₀) (h₁ : Good A B r g I) :
    (⟨g₀, ⟨I₀, h₀⟩⟩ : Σ g : T ⟶ Spec (CommRingCat.of A),
      {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}) = ⟨g, ⟨I, h₁⟩⟩ := by
  subst h
  have : pullback.map (str A B) g₀ (str A B) g₀ (𝟙 _) (𝟙 _) (𝟙 _) (by simp) (by simp) = 𝟙 _ := by
    ext <;> simp
  rw [this, Scheme.IdealSheafData.comap_id] at hI
  subst hI
  rfl

theorem comap_bc_comp {T T' T'' : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of A)) (a : T' ⟶ T)
    (b : T'' ⟶ T') (I : (pullback (str A B) g).IdealSheafData) :
    I.comap (bc A B g (b ≫ a)) = ((I.comap (bc A B g a)).comap (bc A B (a ≫ g) b)).comap
      (pullback.map (str A B) ((b ≫ a) ≫ g) (str A B) (b ≫ a ≫ g) (𝟙 _) (𝟙 _) (𝟙 _)
        (by simp) (by simp)) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
  congr 1
  apply pullback.hom_ext <;>
    simp only [bc, pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]

def functor (r : ℕ) : Scheme.{0}ᵒᵖ ⥤ Type where
  obj T := Σ g : T.unop ⟶ Spec (CommRingCat.of A),
    {I : (pullback (str A B) g).IdealSheafData // Good A B r g I}
  map {_ _} a := TypeCat.ofHom fun x => ⟨a.unop ≫ x.1, ⟨x.2.1.comap (bc A B x.1 a.unop),
    good_comap A B r x.1 a.unop x.2.1 x.2.2⟩⟩
  map_id T := by
    ext x : 3
    exact sigma_eq A B r (Category.id_comp _) rfl _ _
  map_comp {T T' T''} a b := by
    ext x : 3
    exact sigma_eq A B r (Category.assoc _ _ _) (comap_bc_comp A B x.1 a.unop b.unop x.2.1) _ _

theorem functor_map (r : ℕ) {T T' : Scheme.{0}} (a : T' ⟶ T) (y : (functor A B r).obj (op T)) :
    (functor A B r).map a.op y =
      ⟨a ≫ y.1, ⟨y.2.1.comap (bc A B y.1 a), good_comap A B r y.1 a y.2.1 y.2.2⟩⟩ := rfl

def Basic {r N : ℕ} (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : Prop :=
  ∀ U : T.affineOpens, Function.Bijective fun c : Fin r → Γ(T, U) =>
    ∑ k, ((y.2.1.subschemeι ≫ pullback.snd _ y.1).app U).hom (c k) *
      ((y.2.1.subschemeι ≫ pullback.fst _ y.1).appLE ⊤
        ((y.2.1.subschemeι ≫ pullback.snd _ y.1) ⁻¹ᵁ U) (by simp)).hom
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (e (σ k)))

end GlobalTheory.HilbAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommensurableMapConjProdPi
section
open Matrix

namespace GlobalTheory

theorem relIndex_iInf_fin_ne_zero {G : Type} [Group G] {m : ℕ} (K : Fin m → Subgroup G)
    (L : Subgroup G) (h : ∀ i, (K i).relIndex L ≠ 0) : (⨅ i, K i).relIndex L ≠ 0 := by
  have key : ∀ s : Finset (Fin m), (⨅ i ∈ s, K i).relIndex L ≠ 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.iInf_insert]
      exact Subgroup.relIndex_inf_ne_zero (h a) ih
  simpa using key Finset.univ

theorem prod_pi_eq_inf_iInf {A : Type} [Group A] {m : ℕ} {B : Fin m → Type} [∀ i, Group (B i)]
    (H : Subgroup A) (K : ∀ i, Subgroup (B i)) :
    H.prod (Subgroup.pi Set.univ K) =
      H.comap (MonoidHom.fst A ((i : Fin m) → B i)) ⊓
        ⨅ i, (K i).comap ((Pi.evalMonoidHom B i).comp (MonoidHom.snd A ((i : Fin m) → B i))) := by
  ext x
  simp [Subgroup.mem_prod, Subgroup.mem_pi, Subgroup.mem_iInf]

theorem relIndex_prod_pi_ne_zero {A : Type} [Group A] {m : ℕ} {B : Fin m → Type}
    [∀ i, Group (B i)] (H H' : Subgroup A) (K K' : ∀ i, Subgroup (B i))
    (hH : H.relIndex H' ≠ 0) (hK : ∀ i, (K i).relIndex (K' i) ≠ 0) :
    (H.prod (Subgroup.pi Set.univ K)).relIndex (H'.prod (Subgroup.pi Set.univ K')) ≠ 0 := by
  rw [prod_pi_eq_inf_iInf H K]
  apply Subgroup.relIndex_inf_ne_zero
  · rw [Subgroup.relIndex_comap]
    refine mt (Subgroup.relIndex_eq_zero_of_le_right ?_) hH
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_prod.mp hx).1
  · apply relIndex_iInf_fin_ne_zero
    intro i
    rw [Subgroup.relIndex_comap]
    refine mt (Subgroup.relIndex_eq_zero_of_le_right ?_) (hK i)
    rintro _ ⟨x, hx, rfl⟩
    exact ((Subgroup.mem_pi Set.univ).mp (Subgroup.mem_prod.mp hx).2) i (Set.mem_univ i)

theorem map_conj_prod_pi {A : Type} [Group A] {m : ℕ} {B : Fin m → Type} [∀ i, Group (B i)]
    (H : Subgroup A) (K : ∀ i, Subgroup (B i)) (g : A × ((i : Fin m) → B i)) :
    (H.prod (Subgroup.pi Set.univ K)).map (MulAut.conj g).toMonoidHom =
      (H.map (MulAut.conj g.1).toMonoidHom).prod
        (Subgroup.pi Set.univ fun i => (K i).map (MulAut.conj (g.2 i)).toMonoidHom) := by
  ext x
  simp only [Subgroup.mem_map_equiv, Subgroup.mem_prod, Subgroup.mem_pi, Set.mem_univ,
    true_implies, MulAut.conj_symm_apply, Prod.fst_mul, Prod.snd_mul, Prod.fst_inv,
    Prod.snd_inv, Pi.mul_apply, Pi.inv_apply]

theorem commensurable_map_conj_prod_pi : ∀ {A : Type} [Group A] {m : ℕ} {B : Fin m → Type} [∀ i, Group (B i)] (H : Subgroup A) (K : ∀ i, Subgroup (B i)) (g : A × ((i : Fin m) → B i)), Subgroup.Commensurable (H.map (MulAut.conj g.1).toMonoidHom) H → (∀ i, Subgroup.Commensurable ((K i).map (MulAut.conj (g.2 i)).toMonoidHom) (K i)) → Subgroup.Commensurable ((H.prod (Subgroup.pi Set.univ K)).map (MulAut.conj g).toMonoidHom) (H.prod (Subgroup.pi Set.univ K)) := by
  intro A _ m B _ H K g hH hK
  rw [map_conj_prod_pi]
  exact ⟨relIndex_prod_pi_ne_zero _ _ _ _ hH.1 fun i => (hK i).1,
    relIndex_prod_pi_ne_zero _ _ _ _ hH.2 fun i => (hK i).2⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutingMapEqSmulMultiplier
section
namespace GlobalTheory

theorem commuting_map_eq_smul_multiplier :
  ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra ℂ B] (W W' : Submodule ℂ B) [FiniteDimensional ℂ W] (h h' : B), h * h' = 1 → (∀ w ∈ W', h' * w ∈ W) → ∀ T : W →ₗ[ℂ] W', T ≠ 0 → (∀ f g : W, (T f : B) * (g : B) = (f : B) * (T g : B)) → ∃ a : ℂ, a ≠ 0 ∧ ∀ f : W, (T f : B) = a • (h * (f : B)) := by
  intro B _ _ _ W W' _ h h' hhh hW T hT hcomm
  let S : W →ₗ[ℂ] W :=
    { toFun := fun f => ⟨h' * (T f : B), hW _ (T f).2⟩
      map_add' := fun f g => by ext; simp [mul_add]
      map_smul' := fun c f => by ext; simp [mul_smul_comm] }
  haveI : Nontrivial W := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hT
    ext f
    rw [Subsingleton.elim f 0]
    simp
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue S
  obtain ⟨f₀, hf₀⟩ := ha.exists_hasEigenvector
  have hS : S f₀ = a • f₀ := hf₀.apply_eq_smul
  have h0 : (T f₀ : B) = a • (h * (f₀ : B)) := by
    have hc : h' * (T f₀ : B) = a • (f₀ : B) := by
      have := congrArg (fun x : W => (x : B)) hS
      simpa [S] using this
    calc (T f₀ : B) = h * (h' * T f₀) := by rw [← mul_assoc, hhh, one_mul]
    _ = h * (a • (f₀ : B)) := by rw [hc]
    _ = a • (h * (f₀ : B)) := mul_smul_comm _ _ _
  have hf0ne : (f₀ : B) ≠ 0 := by
    intro hz
    exact hf₀.2 (Subtype.ext hz)
  have key : ∀ f : W, (T f : B) = a • (h * (f : B)) := by
    intro f
    have hx := hcomm f f₀
    rw [h0] at hx
    apply mul_right_cancel₀ hf0ne
    rw [hx]
    simp only [Algebra.smul_def]
    ring
  refine ⟨a, ?_, key⟩
  rintro rfl
  apply hT
  ext f
  simp [key f]

end GlobalTheory
end

