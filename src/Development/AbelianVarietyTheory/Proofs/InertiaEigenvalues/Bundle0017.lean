import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMonomialsSpan
section
open scoped BigOperators
open Polynomial

namespace GlobalTheory.SplittingAlgebra

theorem exists_monomials_span (t : ℕ) : ∃ e : Fin t.factorial → Fin t → ℕ,
    ∀ (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (y : Fin t → A),
      (∏ c, (X - C (y c))) ∈ Polynomial.lifts (algebraMap R A) →
      ∀ a ∈ Algebra.adjoin R (Set.range y),
        ∃ cf : Fin t.factorial → R, a = ∑ k, cf k • ∏ c, y c ^ e k c := by
  induction t with
  | zero =>
    refine ⟨fun _ _ => 0, fun R A _ _ _ y _ a ha => ?_⟩
    rw [Set.range_eq_empty, Algebra.adjoin_empty, Algebra.mem_bot] at ha
    obtain ⟨r, rfl⟩ := ha
    refine ⟨fun _ => r, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp [Algebra.algebraMap_eq_smul_one]
  | succ t ih =>
    obtain ⟨e, he⟩ := ih
    let E : Fin (t + 1).factorial ≃ Fin (t + 1) × Fin t.factorial :=
      (finCongr (Nat.factorial_succ t)).trans finProdFinEquiv.symm
    refine ⟨fun k => Fin.cons ((E k).1 : ℕ) (e (E k).2), fun R A _ _ _ y hP a ha => ?_⟩
    have hPm : (∏ c, (X - C (y c))).Monic := monic_prod_of_monic _ _ fun c _ => monic_X_sub_C _
    obtain ⟨q, hq, hqd, hqm⟩ := lifts_and_natDegree_eq_and_monic hP hPm
    have hdeg : q.natDegree ≤ t + 1 := by
      rw [hqd]
      refine (natDegree_prod_le _ _).trans ?_
      refine (Finset.sum_le_sum (g := fun _ => 1) fun c _ => natDegree_X_sub_C_le _).trans ?_
      simp
    have hq0 : aeval (y 0) q = 0 := by
      rw [← eval_map_algebraMap, hq, Fin.prod_univ_succ]
      simp
    set R1 := Algebra.adjoin R {y 0} with hR1
    have hR1s : ∀ s ∈ R1, ∃ d : Fin (t + 1) → R, s = ∑ i, d i • y 0 ^ (i : ℕ) := by
      intro s hs
      classical
      have h1 : s ∈ Subalgebra.toSubmodule R1 := hs
      rw [hR1, ← Submodule.span_range_natDegree_eq_adjoin hqm hq0] at h1
      have h2 : s ∈ Submodule.span R (Set.range fun i : Fin (t + 1) => y 0 ^ (i : ℕ)) := by
        refine Submodule.span_mono ?_ h1
        intro z hz
        simp only [Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at hz
        obtain ⟨i, hi, rfl⟩ := hz
        exact ⟨⟨i, by omega⟩, rfl⟩
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 h2
      exact ⟨d, hd.symm⟩
    have hQ : (∏ c : Fin t, (X - C (y c.succ))) ∈ Polynomial.lifts (algebraMap R1 A) := by
      let y0 : R1 := ⟨y 0, Algebra.self_mem_adjoin_singleton R _⟩
      refine ⟨(q.map (algebraMap R R1)) /ₘ (X - C y0), ?_⟩
      rw [coe_mapRingHom, map_divByMonic _ (monic_X_sub_C _), Polynomial.map_map,
        ← IsScalarTower.algebraMap_eq, hq, Fin.prod_univ_succ]
      have : Polynomial.map (algebraMap R1 A) (X - C y0) = X - C (y 0) := by
        simp [y0]
      rw [this, mul_divByMonic_cancel_left _ (monic_X_sub_C _)]
    have ha' : a ∈ Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ) := by
      have : Algebra.adjoin R (Set.range y) ≤
          (Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ)).restrictScalars R := by
        refine Algebra.adjoin_le ?_
        rintro _ ⟨c, rfl⟩
        refine Fin.cases ?_ (fun c => ?_) c
        · exact Subalgebra.algebraMap_mem (Algebra.adjoin R1 (Set.range fun c : Fin t => y c.succ))
            (⟨y 0, Algebra.self_mem_adjoin_singleton R _⟩ : R1)
        · exact Algebra.subset_adjoin (R := R1) (s := Set.range fun c : Fin t => y c.succ) ⟨c, rfl⟩
      exact this ha
    obtain ⟨cf, hcf⟩ := he R1 A (fun c => y c.succ) hQ a ha'
    choose d hd using fun k => hR1s (cf k) (cf k).2
    refine ⟨fun k => d (E k).2 (E k).1, ?_⟩
    rw [hcf, ← E.symm.sum_comp, Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Subalgebra.smul_def, smul_eq_mul, hd k, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Fin.prod_univ_succ]

theorem adjoin_perm_eq_top {K : Type} [Field K] {t : ℕ} (α : Fin t → K)
    (hα : Function.Injective α) (f : Equiv.Perm (Fin t) → K) :
    f ∈ Algebra.adjoin K (Set.range fun (c : Fin t) (σ : Equiv.Perm (Fin t)) => α (σ c)) := by
  classical
  set S := Algebra.adjoin K (Set.range fun (c : Fin t) (σ : Equiv.Perm (Fin t)) => α (σ c))
  have h1 : ∀ σ : Equiv.Perm (Fin t), (Pi.single σ (1 : K) : Equiv.Perm (Fin t) → K) ∈ S := by
    intro σ
    have : (Pi.single σ (1 : K) : Equiv.Perm (Fin t) → K) =
        ∏ c, aeval (fun τ : Equiv.Perm (Fin t) => α (τ c)) (Lagrange.basis Finset.univ α (σ c)) := by
      funext τ
      rw [Finset.prod_apply]
      simp only [aeval_pi_apply₂, coe_aeval_eq_eval]
      by_cases h : τ = σ
      · subst h
        rw [Pi.single_eq_same]
        exact (Finset.prod_eq_one fun c _ =>
          Lagrange.eval_basis_self hα.injOn (Finset.mem_univ _)).symm
      · rw [Pi.single_eq_of_ne h]
        obtain ⟨c, hc⟩ : ∃ c, σ c ≠ τ c := by
          by_contra hh
          push_neg at hh
          exact h (Equiv.ext fun c => (hh c).symm)
        exact (Finset.prod_eq_zero (Finset.mem_univ c)
          (Lagrange.eval_basis_of_ne hc (Finset.mem_univ _))).symm
    rw [this]
    refine Subalgebra.prod_mem _ fun c _ => ?_
    refine Algebra.adjoin_mono ?_ (aeval_mem_adjoin_singleton K _)
    rintro _ rfl
    exact ⟨c, rfl⟩
  rw [pi_eq_sum_univ' f]
  exact Subalgebra.sum_mem _ fun σ _ => Subalgebra.smul_mem _ (h1 σ) _

theorem coeff_prod_apply {O I : Type} [CommRing O] {t : ℕ} (y : Fin t → I → O) (i : I) (j : ℕ) :
    (∏ c, (X - C (y c))).coeff j i = (∏ c, (X - C (y c i))).coeff j := by
  have := coeff_map (p := ∏ c, (X - C (y c))) (Pi.evalRingHom (fun _ : I => O) i) j
  rw [Polynomial.map_prod] at this
  simpa using this.symm

theorem main : ∀ {O X : Type} [CommRing O] [IsDomain O] [Finite X] (T : Subalgebra O (X → O)) (t : ℕ) (α : X → Fin t → O), (∀ x, Function.Injective (α x)) → (∀ x y, x ≠ y → ∃ f ∈ T, f x ≠ f y) → (∀ j, (fun x => (∏ c, (Polynomial.X - Polynomial.C (α x c))).coeff j) ∈ T) → let T' : Subalgebra O (X × Equiv.Perm (Fin t) → O) := Algebra.adjoin O ((fun f : X → O => fun x' => f x'.1) '' (T : Set (X → O)) ∪ Set.range fun c : Fin t => fun x' => α x'.1 (x'.2 c)); ∃ b : Fin t.factorial → X × Equiv.Perm (Fin t) → O, (∀ k, b k ∈ T') ∧ ∀ f ∈ T', ∃! cf : Fin t.factorial → T, f = ∑ k, (fun x' => (cf k : X → O) x'.1) * b k := by
  intro O Y _ _ _ T t α hα _ hT T'
  obtain ⟨e, he⟩ := exists_monomials_span t
  let y : Fin t → Y × Equiv.Perm (Fin t) → O := fun c x' => α x'.1 (x'.2 c)
  refine ⟨fun k => ∏ c, y c ^ e k c, fun k => ?_, fun f hf => ?_⟩
  · have hy : ∀ c, y c ∈ T' := fun c =>
      Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_range_self c))
    exact Subalgebra.prod_mem _ fun c _ => Subalgebra.pow_mem _ (hy c) _
  have hind : ∀ (x : Y) (d : Fin t.factorial → O),
      (∀ σ : Equiv.Perm (Fin t), ∑ k, d k * ∏ c, α x (σ c) ^ e k c = 0) → ∀ k, d k = 0 := by
    intro x d hd k
    let K := FractionRing O
    have hi : Function.Injective (algebraMap O K) := IsFractionRing.injective O K
    let β : Fin t → K := fun c => algebraMap O K (α x c)
    let z : Fin t → Equiv.Perm (Fin t) → K := fun c σ => β (σ c)
    have hl : (∏ c, (X - C (z c))) ∈ Polynomial.lifts (algebraMap K (Equiv.Perm (Fin t) → K)) := by
      rw [lifts_iff_coeff_lifts]
      intro j
      refine ⟨(∏ c, (X - C (β c))).coeff j, funext fun σ => ?_⟩
      rw [coeff_prod_apply, Equiv.prod_comp σ (fun c => X - C (β c))]
      rfl
    have hli : LinearIndependent K (fun k => ∏ c, z c ^ e k c) := by
      refine linearIndependent_of_top_le_span_of_card_eq_finrank (fun g _ => ?_) ?_
      · obtain ⟨cf, hcf⟩ := he K _ z hl g (adjoin_perm_eq_top β (hi.comp (hα x)) g)
        exact (Submodule.mem_span_range_iff_exists_fun K).2 ⟨cf, hcf.symm⟩
      · simp [Fintype.card_perm]
    have := Fintype.linearIndependent_iff.1 hli (fun k => algebraMap O K (d k)) (by
      funext σ
      have := congrArg (algebraMap O K) (hd σ)
      simpa [z, β, Finset.sum_apply, Finset.prod_apply, Algebra.smul_def] using this) k
    exact hi (by simpa using this)
  let φ : T →+* (Y × Equiv.Perm (Fin t) → O) :=
    Pi.ringHom fun x' => (Pi.evalRingHom (fun _ : Y => O) x'.1).comp T.val.toRingHom
  letI : Algebra T (Y × Equiv.Perm (Fin t) → O) := φ.toAlgebra
  have hl : (∏ c, (X - C (y c))) ∈
      Polynomial.lifts (algebraMap T (Y × Equiv.Perm (Fin t) → O)) := by
    rw [lifts_iff_coeff_lifts]
    intro j
    refine ⟨⟨_, hT j⟩, funext fun x' => ?_⟩
    rw [coeff_prod_apply, Equiv.prod_comp x'.2 (fun c => X - C (α x'.1 c))]
    rfl
  have hf' : f ∈ Algebra.adjoin T (Set.range y) := by
    induction hf using Algebra.adjoin_induction with
    | mem g hg =>
      rcases hg with ⟨g, hg, rfl⟩ | hg
      · exact Subalgebra.algebraMap_mem _ (⟨g, hg⟩ : T)
      · exact Algebra.subset_adjoin hg
    | algebraMap r => exact Subalgebra.algebraMap_mem _ (algebraMap O T r)
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  obtain ⟨cf, hcf⟩ := he T _ y hl f hf'
  refine ⟨cf, hcf, fun cg hcg => ?_⟩
  funext k
  ext x
  refine sub_eq_zero.1 (hind x (fun k => (cg k : Y → O) x - (cf k : Y → O) x) (fun σ => ?_) k)
  have h1 : f = ∑ k, (fun x' => (cf k : Y → O) x'.1) * ∏ c, y c ^ e k c := hcf
  have h2 := congrFun (hcg.symm.trans h1) (x, σ)
  simp only [Finset.sum_apply, Pi.mul_apply, Finset.prod_apply, Pi.pow_apply, y] at h2
  simp only [sub_mul, Finset.sum_sub_distrib, h2, sub_self]

end GlobalTheory.SplittingAlgebra
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNotXPowDvdAdjugateOfFirstOrderKernel
section
open Polynomial Matrix

namespace GlobalTheory
namespace CofactorOrder

variable {K : Type} [Field K] {n : Type} [Fintype n] [DecidableEq n]

theorem exists_diag (M : Matrix n n K) :
    ∃ (P Q : Matrix n n K) (D : n → K), P.det = 1 ∧ Q.det = 1 ∧ P * M * Q = diagonal D := by
  obtain ⟨L, L', D, hL⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal M
  have hdet : ∀ T : List (TransvectionStruct n K),
      (T.map TransvectionStruct.toMatrix).prod.det = 1 := by
    intro T
    induction T with
    | nil => simp
    | cons t T ih => rw [List.map_cons, List.prod_cons, det_mul, ih, TransvectionStruct.det, one_mul]
  exact ⟨_, _, D, hdet L, hdet L', hL⟩

theorem mulVec_eq_zero_of_det {P : Matrix n n K} (hP : P.det = 1) {v : n → K}
    (h : P *ᵥ v = 0) : v = 0 := by
  have hu : IsUnit P := (isUnit_iff_isUnit_det P).mpr (by rw [hP]; exact isUnit_one)
  exact (mulVec_injective_iff_isUnit.mpr hu) (by rw [h, mulVec_zero])

theorem ker_eq_bot_of_det {P : Matrix n n K} (hP : P.det = 1) :
    LinearMap.ker P.mulVecLin = ⊥ := by
  refine LinearMap.ker_eq_bot'.mpr fun v hv => ?_
  rw [mulVecLin_apply] at hv
  exact mulVec_eq_zero_of_det hP hv

theorem card_le_finrank {M P Q : Matrix n n K} {D : n → K} [DecidablePred fun i => D i = 0]
    (hP : P.det = 1) (hQ : Q.det = 1) (h : P * M * Q = diagonal D) :
    Fintype.card {i // D i = 0} ≤ Module.finrank K (LinearMap.ker M.mulVecLin) := by
  set V := LinearMap.ker M.mulVecLin
  have hmem : ∀ i : {i // D i = 0}, Q *ᵥ Pi.single i.1 (1 : K) ∈ V := by
    intro i
    rw [LinearMap.mem_ker, mulVecLin_apply]
    apply mulVec_eq_zero_of_det hP
    simp only [mulVec_mulVec, ← Matrix.mul_assoc, h]
    funext k
    rw [mulVec_diagonal]
    by_cases hk : k = i.1
    · subst hk; simp [i.2]
    · simp [hk]
  have hsingle : LinearIndependent K (fun i : {i // D i = 0} => (Pi.single i.1 (1 : K) : n → K)) := by
    have := (Pi.basisFun K n).linearIndependent.comp Subtype.val
      (Subtype.val_injective (p := fun i => D i = 0))
    convert this using 1
    funext i
    simp
  have hli : LinearIndependent K (fun i : {i // D i = 0} => (⟨_, hmem i⟩ : V)) := by
    apply LinearIndependent.of_comp V.subtype
    have hmapped := hsingle.map' Q.mulVecLin (ker_eq_bot_of_det hQ)
    have e : (⇑V.subtype ∘ fun i : {i // D i = 0} => (⟨_, hmem i⟩ : V)) =
        ⇑Q.mulVecLin ∘ fun i => (Pi.single i.1 (1 : K) : n → K) := by
      funext i
      simp
    rw [e]
    exact hmapped
  exact hli.fintype_card_le_finrank

theorem adjugate_ne_zero [Nonempty n] (M : Matrix n n K)
    (h : Module.finrank K (LinearMap.ker M.mulVecLin) ≤ 1) : M.adjugate ≠ 0 := by
  classical
  obtain ⟨P, Q, D, hP, hQ, hPQ⟩ := exists_diag M
  have hone := Fintype.card_le_one_iff.mp ((card_le_finrank hP hQ hPQ).trans h)
  obtain ⟨i, hi⟩ : ∃ i, ∀ j, j ≠ i → D j ≠ 0 := by
    by_cases hex : ∃ i, D i = 0
    · obtain ⟨i, hi0⟩ := hex
      exact ⟨i, fun j hj hj0 => hj (congrArg Subtype.val (hone ⟨j, hj0⟩ ⟨i, hi0⟩))⟩
    · push Not at hex
      exact ⟨Classical.arbitrary n, fun j _ => hex j⟩
  intro hM
  have hdiag : (diagonal D).adjugate = 0 := by
    rw [← hPQ, adjugate_mul_distrib, adjugate_mul_distrib, hM, Matrix.zero_mul, Matrix.mul_zero]
  have hii := congrFun (congrFun hdiag i) i
  rw [adjugate_diagonal, diagonal_apply_eq, Matrix.zero_apply] at hii
  exact Finset.prod_ne_zero_iff.mpr (fun j hj => hi j (Finset.ne_of_mem_erase hj)) hii

theorem exists_coeff_adjugate_ne_zero [Nonempty n] (Ψ : Matrix n n K[X])
    (h : Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ 1) :
    ∃ b c, ¬ (X : K[X]) ∣ Ψ.adjugate b c := by
  have hmap : (Ψ.map fun p => p.coeff 0) = constantCoeff.mapMatrix Ψ := by
    ext i j
    simp [constantCoeff_apply]
  have hne := adjugate_ne_zero _ h
  rw [hmap, ← RingHom.map_adjugate] at hne
  by_contra hall
  push Not at hall
  apply hne
  ext b c
  rw [RingHom.mapMatrix_apply, map_apply, Matrix.zero_apply, constantCoeff_apply]
  exact X_dvd_iff.mp (hall b c)

theorem map_coeff_mul (P Q : Matrix n n K) (Ψ : Matrix n n K[X]) (k : ℕ) :
    ((P.map C * Ψ * Q.map C).map fun p => p.coeff k) = P * (Ψ.map fun p => p.coeff k) * Q := by
  ext i j
  simp only [map_apply, Matrix.mul_apply, Polynomial.finsetSum_coeff, Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul, Finset.sum_mul]

theorem diag_case [Nonempty n] (Θ : Matrix n n K[X]) (D : n → K)
    [DecidablePred fun i => D i = 0] (hD : (Θ.map fun p => p.coeff 0) = diagonal D)
    (H : ∀ x0 x1 : Fin (1 + 1) → n → K, (∀ j, (Θ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
      (Θ.map fun p => p.coeff 1).mulVec (x0 j) + (Θ.map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0) :
    ∃ b c, ¬ (X : K[X]) ^ (Fintype.card {i // D i = 0} + 1) ∣ Θ.adjugate b c := by
  obtain ⟨s, hs⟩ : ∃ s : n → K[X], s = fun i => if D i = 0 then X else 1 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : Matrix n n K[X],
      T = Matrix.of fun i j => if D i = 0 then divX (Θ i j) else Θ i j := ⟨_, rfl⟩
  have h0 : ∀ i j, (Θ i j).coeff 0 = diagonal D i j := fun i j => by
    simpa using congrFun (congrFun hD i) j
  have hfac : Θ = diagonal s * T := by
    refine Matrix.ext fun i j => ?_
    rw [diagonal_mul, hs, hT, of_apply]
    by_cases hi : D i = 0
    · have hc : (Θ i j).coeff 0 = 0 := by
        rw [h0]
        by_cases hij : i = j
        · subst hij; simp [hi]
        · simp [diagonal_apply_ne _ hij]
      have hX := X_mul_divX_add (Θ i j)
      rw [hc, C_0, add_zero] at hX
      simp only [hi, if_true]
      exact hX.symm
    · simp [hi]
  have hadj : ∀ b c, Θ.adjugate b c = T.adjugate b c * ∏ j ∈ Finset.univ.erase c, s j := by
    intro b c
    rw [hfac, adjugate_mul_distrib, adjugate_diagonal, mul_diagonal]
  have hprod : ∀ c, (∏ j ∈ Finset.univ.erase c, s j) ∣ X ^ Fintype.card {i // D i = 0} := by
    intro c
    have hall : ∏ j, s j = X ^ Fintype.card {i // D i = 0} := by
      simp [hs, Finset.prod_ite, Fintype.card_subtype]
    rw [← hall]
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.erase_subset _ _)
  have hrow : ∀ (v : n → K) (i : n), ((T.map fun p => p.coeff 0) *ᵥ v) i =
      if D i = 0 then ((Θ.map fun p => p.coeff 1) *ᵥ v) i else D i * v i := by
    intro v i
    by_cases hi : D i = 0
    · simp [Matrix.mulVec, dotProduct, hT, hi, coeff_divX]
    · simp [Matrix.mulVec, dotProduct, hT, hi, h0, diagonal_apply]
  have hker : Module.finrank K (LinearMap.ker (T.map fun p => p.coeff 0).mulVecLin) ≤ 1 := by
    by_contra hlt
    push Not at hlt
    set V := LinearMap.ker (T.map fun p => p.coeff 0).mulVecLin
    have h2 : 1 + 1 ≤ Module.finrank K V := hlt
    have hinj : Function.Injective (Fin.castLE h2) := fun a b hab =>
      Fin.ext (by simpa using congrArg Fin.val hab)
    have hf := (Module.finBasis K V).linearIndependent.comp _ hinj
    have hli := hf.map' V.subtype (Submodule.ker_subtype V)
    refine H (fun j => (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j)
      (fun j i => if D i = 0 then 0 else
        -((Θ.map fun p => p.coeff 1) *ᵥ (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j) i / D i)
      ?_ hli
    intro j
    set v := (V.subtype ∘ (Module.finBasis K V ∘ Fin.castLE h2)) j with hv
    have hvk : (T.map fun p => p.coeff 0) *ᵥ v = 0 := by
      have := (Module.finBasis K V (Fin.castLE h2 j)).2
      rw [LinearMap.mem_ker, mulVecLin_apply] at this
      exact this
    have hvi : ∀ i, (if D i = 0 then ((Θ.map fun p => p.coeff 1) *ᵥ v) i else D i * v i) = 0 := by
      intro i
      rw [← hrow, hvk]
      rfl
    constructor
    · rw [hD]
      funext i
      rw [mulVec_diagonal]
      by_cases hi : D i = 0
      · simp [hi]
      · have := hvi i
        simp only [hi, if_false] at this
        simpa using this
    · rw [hD]
      funext i
      rw [Pi.add_apply, mulVec_diagonal]
      by_cases hi : D i = 0
      · have := hvi i
        simp only [hi, if_true] at this
        simp [hi, this]
      · simp only [hi, if_false]
        rw [Pi.zero_apply, ← mul_div_assoc, mul_div_cancel_left₀ _ hi, add_neg_cancel]
  obtain ⟨b, c, hbc⟩ := exists_coeff_adjugate_ne_zero T hker
  refine ⟨b, c, fun hdvd => hbc ?_⟩
  rw [hadj] at hdvd
  obtain ⟨r, hr⟩ := hprod c
  have h3 := Dvd.dvd.mul_right hdvd r
  rw [mul_assoc, ← hr, pow_succ, mul_comm (X ^ _) X] at h3
  exact (mul_dvd_mul_iff_right (pow_ne_zero _ X_ne_zero)).mp h3

end CofactorOrder

open CofactorOrder in

theorem exists_not_X_pow_dvd_adjugate_of_firstOrderKernel (K : Type) [Field K] (a m : ℕ)
    (Ψ : Matrix (Fin a) (Fin a) (Polynomial K))
    (H : ∀ x0 x1 : Fin (1 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
      (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0)
    (hν : Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m + 1)
    (ha : a ≠ 0) :
    ∃ b c, ¬ (Polynomial.X : Polynomial K) ^ (2 * m + 1) ∣ Ψ.adjugate b c := by
  classical
  have : Nonempty (Fin a) := ⟨⟨0, Nat.pos_of_ne_zero ha⟩⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨b, c, hbc⟩ := exists_coeff_adjugate_ne_zero Ψ (by simpa using hν)
    exact ⟨b, c, by simpa using hbc⟩
  obtain ⟨P, Q, D, hP, hQ, hPQ⟩ := exists_diag (Ψ.map fun p => p.coeff 0)
  have hΘ0 : ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0) = diagonal D := by
    rw [map_coeff_mul]; exact hPQ
  have hz := card_le_finrank hP hQ hPQ
  have HΘ : ∀ x0 x1 : Fin (1 + 1) → Fin a → K,
      (∀ j, ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧
        ((P.map C * Ψ * Q.map C).map fun p => p.coeff 1).mulVec (x0 j) +
          ((P.map C * Ψ * Q.map C).map fun p => p.coeff 0).mulVec (x1 j) = 0) →
      ¬ LinearIndependent K x0 := by
    intro x0 x1 hx hli
    refine H (fun j => Q *ᵥ x0 j) (fun j => Q *ᵥ x1 j) (fun j => ?_)
      (hli.map' Q.mulVecLin (ker_eq_bot_of_det hQ))
    obtain ⟨h0, h1⟩ := hx j
    rw [map_coeff_mul] at h0 h1
    rw [map_coeff_mul] at h1
    constructor
    · apply mulVec_eq_zero_of_det hP
      simpa only [mulVec_mulVec, ← Matrix.mul_assoc] using h0
    · apply mulVec_eq_zero_of_det hP
      simpa only [mulVec_add, mulVec_mulVec, ← Matrix.mul_assoc] using h1
  obtain ⟨b, c, hbc⟩ := diag_case _ D hΘ0 HΘ
  by_contra hcon
  push Not at hcon
  apply hbc
  have hle : Fintype.card {i // D i = 0} + 1 ≤ 2 * m + 1 := by omega
  refine (pow_dvd_pow X hle).trans ?_
  rw [adjugate_mul_distrib, adjugate_mul_distrib, ← Matrix.mul_assoc]
  simp only [Matrix.mul_apply]
  exact Finset.dvd_sum fun l _ => Dvd.dvd.mul_right
    (Finset.dvd_sum fun k _ => Dvd.dvd.mul_left (hcon k l) _) _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPartitionOneIntegralAtPlaces
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_partition_one_integral_at_places (L : Type) [Field L] [NumberField L]
    (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : S.Nonempty) (Y : S → Finset L)
    (hY : ∀ la, ∀ y ∈ Y la, la.1.valuation L y ≤ 1) :
    ∃ e : S → L, ∑ la, e la = 1 ∧
      ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, la'.valuation L (e la * y) ≤ 1 := by
  classical
  have hb : ∀ (_la : S) (y : L) (la' : HeightOneSpectrum (𝓞 L)),
      ∃ n : ℕ, WithZero.exp (-(n : ℤ)) * la'.valuation L y ≤ 1 := by
    intro _ y la'
    by_cases hy : la'.valuation L y = 0
    · exact ⟨0, by simp [hy]⟩
    · obtain ⟨m, hm⟩ : ∃ m : ℤ, WithZero.exp m = la'.valuation L y := ⟨_, WithZero.exp_log hy⟩
      refine ⟨m.toNat, ?_⟩
      rw [← hm, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
      omega
  choose n hn using hb
  let N : ℕ := ∑ la : S, ∑ y ∈ Y la, ∑ la' ∈ S, n la y la'
  have hN : ∀ la, ∀ y ∈ Y la, ∀ la' ∈ S, n la y la' ≤ N := by
    intro la y hy la' hla'
    calc n la y la' ≤ ∑ la'' ∈ S, n la y la'' :=
          Finset.single_le_sum (f := fun la'' => n la y la'') (fun _ _ => Nat.zero_le _) hla'
      _ ≤ ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'' :=
          Finset.single_le_sum (f := fun y' => ∑ la'' ∈ S, n la y' la'') (fun _ _ => Nat.zero_le _) hy
      _ ≤ N := Finset.single_le_sum (f := fun la => ∑ y' ∈ Y la, ∑ la'' ∈ S, n la y' la'')
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ la)
  let J : S → Ideal (𝓞 L) := fun la => ∏ la' ∈ S.erase la.1, la'.asIdeal ^ N
  have htop : ⨆ la ∈ (Finset.univ : Finset S), J la = ⊤ := by
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    have hJM : ∀ la : S, J la ≤ M := fun la =>
      le_trans (le_iSup₂_of_le (f := fun la (_ : la ∈ (Finset.univ : Finset S)) => J la)
        la (Finset.mem_univ _) le_rfl) hle
    obtain ⟨la0, hla0⟩ := hS
    obtain ⟨la1, hla1, h1⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la0, hla0⟩)
    have hle1 : la1.asIdeal ≤ M := hM.isPrime.le_of_pow_le h1
    have heq : la1.asIdeal = M := la1.isMaximal.eq_of_le hM.ne_top hle1
    have hla1S : la1 ∈ S := Finset.mem_of_mem_erase hla1
    obtain ⟨la2, hla2, h2⟩ := (Ideal.IsPrime.prod_le hM.isPrime).1 (hJM ⟨la1, hla1S⟩)
    have hle2 : la2.asIdeal ≤ la1.asIdeal := heq ▸ hM.isPrime.le_of_pow_le h2
    have h22 : la2.asIdeal = la1.asIdeal := la2.isMaximal.eq_of_le la1.isPrime.ne_top hle2
    exact (Finset.ne_of_mem_erase hla2) (HeightOneSpectrum.ext h22)
  have h1 : (1 : 𝓞 L) ∈ ⨆ la ∈ (Finset.univ : Finset S), J la := htop ▸ Submodule.mem_top
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ _).1 h1
  refine ⟨fun la => ((μ la : 𝓞 L) : L), ?_, ?_⟩
  · have := congrArg (fun x : 𝓞 L => (x : L)) hμ
    simpa using this
  · intro la y hy la' hla'
    rw [map_mul]
    by_cases h : la' = la.1
    · subst h
      calc la.1.valuation L ((μ la : 𝓞 L) : L) * la.1.valuation L y ≤ 1 * 1 :=
            mul_le_mul' (HeightOneSpectrum.valuation_le_one _ _) (hY la y hy)
        _ = 1 := one_mul 1
    · have hmem : (μ la : 𝓞 L) ∈ la'.asIdeal ^ N := by
        have hm : (μ la : 𝓞 L) ∈ J la := (μ la).2
        have hs : la' ∈ S.erase la.1 := Finset.mem_erase.2 ⟨h, hla'⟩
        have : J la ≤ la'.asIdeal ^ N := by
          show ∏ la'' ∈ S.erase la.1, la''.asIdeal ^ N ≤ _
          rw [← Finset.mul_prod_erase _ _ hs]
          exact le_trans Ideal.mul_le_inf inf_le_left
        exact this hm
      have hv : la'.valuation L ((μ la : 𝓞 L) : L) ≤ WithZero.exp (-(N : ℤ)) := by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_dvd,
          Ideal.dvd_span_singleton]
        exact hmem
      calc la'.valuation L ((μ la : 𝓞 L) : L) * la'.valuation L y
          ≤ WithZero.exp (-(N : ℤ)) * la'.valuation L y := mul_le_mul' hv le_rfl
        _ ≤ WithZero.exp (-(n la y la' : ℤ)) * la'.valuation L y := by
            refine mul_le_mul' ?_ le_rfl
            rw [WithZero.exp_le_exp]
            have := hN la y hy la' hla'
            omega
        _ ≤ 1 := hn la y la'

end GlobalTheory
end

