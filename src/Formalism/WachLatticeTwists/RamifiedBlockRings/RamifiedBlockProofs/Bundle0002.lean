import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.Bundle0001
import Formalism.WachLatticeTwists.RamifiedBlockRings.ChainFromPrimitiveData
import Formalism.CharacterColumnKernels.IdempotentNormalForms.SpacedProductLowerBound
import Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.LengthBoundViaSplitting
import Formalism.WachLatticeTwists.CoprimeLiftBounds.CoprimeLiftProofs.TheoremNFiveTopHolds

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.CharpolyRevMap
section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.TruncatedSeriesCounting.TruncatedSeriesCountingIdentities

theorem cornerIdem : CornerIdempotentInSubalgebra := by
  unfold CornerIdempotentInSubalgebra
  intro k _ n ι _ _ B hn hsurj A
  classical
  obtain ⟨p, q, hpq⟩ : ∃ p q : n, p ≠ q := Fintype.exists_pair_of_one_lt_card hn
  have hc : ((Matrix.single p p (1 : k) - Matrix.single q q 1 : Matrix n n k), (0 : ι → k)) ∈ B := by
    obtain ⟨z1, hz1B, hz1⟩ := hsurj (Matrix.single p q 1)
    obtain ⟨z2, hz2B, hz2⟩ := hsurj (Matrix.single q p 1)
    have := B.sub_mem (B.mul_mem hz1B hz2B) (B.mul_mem hz2B hz1B)
    convert this using 1
    refine Prod.ext ?_ ?_
    · simp [hz1, hz2, Matrix.single_mul_single_same]
    · simp [mul_comm]
  have hij : ∀ i j, ((Matrix.single i j (1 : k) : Matrix n n k), (0 : ι → k)) ∈ B := by
    intro i j
    obtain ⟨w1, hw1B, hw1⟩ := hsurj (Matrix.single i p 1)
    obtain ⟨w2, hw2B, hw2⟩ := hsurj (Matrix.single p j 1)
    have := B.mul_mem (B.mul_mem hw1B hc) hw2B
    convert this using 1
    refine Prod.ext ?_ ?_
    · simp [hw1, hw2, Matrix.mul_sub, Matrix.sub_mul, Matrix.single_mul_single_same,
        Matrix.single_mul_single_of_ne, hpq]
    · simp
  have hA : (A, (0 : ι → k)) = ∑ i, ∑ j, A i j • ((Matrix.single i j (1 : k) : Matrix n n k), (0 : ι → k)) := by
    refine Prod.ext ?_ ?_
    · simp only [Prod.fst_sum, Prod.smul_fst, Matrix.smul_single, smul_eq_mul, mul_one]
      exact Matrix.matrix_eq_sum_single A
    · simp [Prod.snd_sum]
  rw [hA]
  exact B.sum_mem fun i _ => B.sum_mem fun j _ => B.smul_mem (hij i j) _

theorem charpolyRev_map {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) {d : Type*} [Fintype d]
    [DecidableEq d] (M : Matrix d d A) :
    (Matrix.charpolyRev M).map f = Matrix.charpolyRev (M.map f) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h, Matrix.one_apply]

theorem nilConst : StatNilConst := by
  intro O _ _ X T d _ _ hT a ha y hy x
  have hrev : Matrix.charpolyRev ((a x).map (IsLocalRing.residue O)) = 1 := by
    have h1 : Matrix.charpolyRev ((a x).map (IsLocalRing.residue O)) =
        Matrix.charpolyRev ((a y).map (IsLocalRing.residue O)) := by
      rw [← charpolyRev_map, ← charpolyRev_map]
      ext k
      rw [Polynomial.coeff_map, Polynomial.coeff_map]
      exact resConst O X T hT _ (ha k) x y
    rw [h1, hy]
    simp [Matrix.charpolyRev]
  set M := (a x).map (IsLocalRing.residue O) with hM
  have hcp : M.charpoly = Polynomial.X ^ Fintype.card d := by
    have hdeg : M.charpoly.natDegree = Fintype.card d := Matrix.charpoly_natDegree_eq_dim M
    ext k
    rw [Polynomial.coeff_X_pow]
    by_cases hk : k ≤ Fintype.card d
    · have h2 : M.charpoly.reverse.coeff (Fintype.card d - k) = M.charpoly.coeff k := by
        rw [Polynomial.coeff_reverse, hdeg, Polynomial.revAt_le (Nat.sub_le _ _)]
        congr 1; omega
      rw [← h2, Matrix.reverse_charpoly, hrev, Polynomial.coeff_one]
      by_cases hk2 : k = Fintype.card d
      · simp [hk2]
      · rw [if_neg (by omega), if_neg hk2]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), if_neg (by omega)]
  have hch := Matrix.aeval_self_charpoly M
  rw [hcp] at hch
  have h5 : ((a x) ^ Fintype.card d).map (IsLocalRing.residue O) = M ^ Fintype.card d := by
    rw [hM, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, map_pow]
  rw [h5]
  simpa using hch

theorem tailProd {M : Type*} [CommMonoid M] (f : ℕ → M) (t : ℕ) :
    ((List.range t).tail.map f).prod = ∏ i ∈ Finset.Ioo 0 t, f i := by
  cases t with
  | zero => simp
  | succ n =>
    rw [List.range_succ_eq_map, List.tail_cons, List.map_map, ← List.prod_toFinset _ List.nodup_range,
      List.toFinset_range]
    have hI : Finset.Ioo 0 (n + 1) = (Finset.range n).map ⟨Nat.succ, Nat.succ_injective⟩ := by
      ext i
      simp only [Finset.mem_Ioo, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨i - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩
        omega
    (rw [hI, Finset.prod_map]) <;> rfl

theorem listDiag {A : Type*} [CommRing A] {d : Type*} [Fintype d] [DecidableEq d] (f : ℕ → d → A)
    (l : List ℕ) :
    (l.map fun i => (Matrix.diagonal (f i) : Matrix d d A)).prod =
      Matrix.diagonal fun a => (l.map fun i => f i a).prod := by
  induction l with
  | nil => simp
  | cons i l ih => simp [ih, Matrix.diagonal_mul_diagonal]

theorem eDiag : StatEDiag := by
  unfold StatEDiag
  intro A _ d _ _ S β t α
  dsimp only
  have hfac : ∀ i, (Matrix.diagonal (fun a => if S a then β a else 0) -
      α i • Matrix.diagonal (fun a => if S a then (1 : A) else 0)) =
      Matrix.diagonal (fun a => if S a then β a - α i else 0) := by
    intro i
    ext a b
    by_cases hab : a = b
    · subst hab
      by_cases hS : S a <;> simp [hS]
    · simp [Matrix.diagonal_apply_ne _ hab]
  simp_rw [hfac]
  rw [listDiag, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  by_cases hS : S a
  · simp only [hS, ↓reduceIte, one_mul]
    exact tailProd _ t
  · simp [hS]

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.SplitExt
section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG

theorem local_of_complete (O A : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CommRing A] [IsDomain A] [Algebra O A]
    [Module.Finite O A] : IsLocalRing A := by
  by_contra hnl
  obtain ⟨M₁, M₂, hM₁, hM₂, hne⟩ := (IsLocalRing.not_isLocalRing_tfae.out 0 2).mp hnl
  let m := IsLocalRing.maximalIdeal O
  let I : Ideal A := m.map (algebraMap O A)
  have hIM : ∀ M : Ideal A, M.IsMaximal → I ≤ M := by
    intro M hM
    have h1 : (M.comap (algebraMap O A)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal M
    exact Ideal.map_le_iff_le_comap.mpr (le_of_eq (IsLocalRing.eq_maximalIdeal h1).symm)
  have hart : IsArtinianRing (A ⧸ I) := by
    let : Field (O ⧸ m) := Ideal.Quotient.field m
    let : Algebra (O ⧸ m) (A ⧸ I) := Ideal.Quotient.algebraQuotientOfLEComap Ideal.le_comap_map
    have : IsScalarTower O (O ⧸ m) (A ⧸ I) := IsScalarTower.of_algebraMap_eq fun x => rfl
    have : Module.Finite (O ⧸ m) (A ⧸ I) := Module.Finite.of_restrictScalars_finite O _ _
    exact IsArtinianRing.of_finite (O ⧸ m) (A ⧸ I)
  let q : A →+* A ⧸ I := Ideal.Quotient.mk I
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hmax : ∀ M : Ideal A, M.IsMaximal → (M.map q).IsMaximal ∧ (M.map q).comap q = M := by
    intro M hM
    have h1 : (M.map q).comap q = M := by
      rw [Ideal.comap_map_of_surjective q hq, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
      exact sup_eq_left.mpr (hIM M hM)
    refine ⟨(Ideal.map_eq_top_or_isMaximal_of_surjective q hq hM).resolve_left fun h => ?_, h1⟩
    rw [h, Ideal.comap_top] at h1
    exact hM.ne_top h1.symm
  let J₁ : MaximalSpectrum (A ⧸ I) := ⟨M₁.map q, (hmax M₁ hM₁).1⟩
  let J₂ : MaximalSpectrum (A ⧸ I) := ⟨M₂.map q, (hmax M₂ hM₂).1⟩
  have hJ : J₁ ≠ J₂ := by
    intro h
    have h1 : M₁.map q = M₂.map q := congrArg MaximalSpectrum.asIdeal h
    exact hne (by rw [← (hmax M₁ hM₁).2, h1, (hmax M₂ hM₂).2])
  let φ := IsArtinianRing.quotNilradicalEquivPi (A ⧸ I)
  let f : A →+* (A ⧸ I) ⧸ nilradical (A ⧸ I) := (Ideal.Quotient.mk _).comp q
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hq
  have hker : ∀ x : A, f x = 0 → ∃ n : ℕ, x ^ n ∈ m • (⊤ : Submodule O A) := by
    intro x hx
    have h1 : q x ∈ nilradical (A ⧸ I) := Ideal.Quotient.eq_zero_iff_mem.mp hx
    obtain ⟨n, hn⟩ := mem_nilradical.mp h1
    refine ⟨n, ?_⟩
    rw [Ideal.smul_top_eq_map]
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by rw [map_pow]; exact hn)
  let u : ∀ J : MaximalSpectrum (A ⧸ I), (A ⧸ I) ⧸ J.asIdeal := Pi.single J₁ 1
  have hu : u * u = u := by
    funext J
    by_cases h : J = J₁
    · subst h; simp [u]
    · simp [u, Pi.single_eq_of_ne h]
  obtain ⟨E, -, hE, -, -, -, hfE, -⟩ := idemLift O A _ f hf hker (φ.symm u) 0
    (by show φ.symm u * φ.symm u = φ.symm u; rw [← map_mul, hu]) (IsIdempotentElem.zero)
    (mul_zero _) (zero_mul _)
  have hφ : φ (f E) = u := by rw [hfE]; exact φ.apply_symm_apply u
  rcases (IsIdempotentElem.iff_eq_zero_or_one.mp hE) with h0 | h1
  · rw [h0, map_zero, map_zero] at hφ
    have h2 := congrFun hφ J₁
    have : Nontrivial ((A ⧸ I) ⧸ J₁.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr J₁.isMaximal.ne_top
    simp [u] at h2
  · rw [h1, map_one, map_one] at hφ
    have h2 := congrFun hφ J₂
    have : Nontrivial ((A ⧸ I) ⧸ J₂.asIdeal) := Ideal.Quotient.nontrivial_iff.mpr J₂.isMaximal.ne_top
    simp [u, Pi.single_eq_of_ne (Ne.symm hJ)] at h2

theorem exists_ramification (O O' : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O']
    (hinj : Function.Injective (algebraMap O O')) [IsLocalHom (algebraMap O O')] :
    ∃ e : ℕ, ∀ y : O, IsDiscreteValuationRing.addVal O' (algebraMap O O' y) =
      e * IsDiscreteValuationRing.addVal O y := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨ϖ', hϖ'⟩ := IsDiscreteValuationRing.exists_irreducible O'
  have hφϖ0 : algebraMap O O' ϖ ≠ 0 := fun h => hϖ.ne_zero (hinj (by rw [h, map_zero]))
  have hφϖnu : ¬ IsUnit (algebraMap O O' ϖ) := fun h => hϖ.not_isUnit (isUnit_of_map_unit _ _ h)
  obtain ⟨e, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hφϖ0 hϖ'
  have he0 : e ≠ 0 := by
    rintro rfl
    apply hφϖnu
    rw [hv, pow_zero, mul_one]
    exact v.isUnit
  refine ⟨e, fun y => ?_⟩
  by_cases hy : y = 0
  · subst hy
    simp [he0, ENat.mul_top]
  · obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy hϖ
    have hu : IsDiscreteValuationRing.addVal O' (algebraMap O O' (u : O)) = 0 :=
      IsDiscreteValuationRing.addVal_eq_zero_iff.2 (u.isUnit.map _)
    simp only [map_mul, map_pow, hv, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hu,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, IsDiscreteValuationRing.addVal_uniformizer hϖ,
      IsDiscreteValuationRing.addVal_uniformizer hϖ']
    simp only [zero_add, nsmul_eq_mul, mul_one]
    ring

open Polynomial in

theorem sep_splitting {K : Type} [Field K] {X : Type} [Fintype X] (F : X → K[X])
    (hF : ∀ x, (F x).Separable) (L : Type) [Field L] [Algebra K L] [IsSplittingField K L (∏ x, F x)] :
    Algebra.IsSeparable K L := by
  classical
  rw [← separableClosure.eq_top_iff, eq_top_iff]
  intro z _
  have hz : z ∈ Algebra.adjoin K ((∏ x, F x).rootSet L) := by
    rw [Polynomial.IsSplittingField.adjoin_rootSet]
    exact Algebra.mem_top
  refine Algebra.adjoin_le (S := (separableClosure K L).toSubalgebra) ?_ hz
  intro α hα
  rw [Polynomial.mem_rootSet] at hα
  obtain ⟨-, hα0⟩ := hα
  rw [map_prod, Finset.prod_eq_zero_iff] at hα0
  obtain ⟨x, -, hx⟩ := hα0
  exact mem_separableClosure_iff.2 ((hF x).of_dvd (minpoly.dvd K α hx))

set_option maxHeartbeats 1000000 in
theorem splitExt : StatSplitExt := by
  intro O _ _ _ _ X _ P hmon hsep
  let K := FractionRing O
  let Q : Polynomial K := ∏ x, (P x).map (algebraMap O K)
  let L := Q.SplittingField
  have hsepL : Algebra.IsSeparable K L := sep_splitting (fun x => (P x).map (algebraMap O K)) hsep L
  let O' := integralClosure O L
  have hfin : Module.Finite O O' := IsIntegralClosure.finite O K L O'
  have htf : Module.IsTorsionFree O L := Module.IsTorsionFree.trans_faithfulSMul O K L
  have hfree : Module.Free O O' := IsIntegralClosure.module_free O K L O'
  have hded : IsDedekindDomain O' := inferInstance
  have hloc : IsLocalRing O' := local_of_complete O O'
  have hinj : Function.Injective (algebraMap O O') := FaithfulSMul.algebraMap_injective O O'
  have hnf : ¬ IsField O' := fun h =>
    IsDiscreteValuationRing.not_isField O (isField_of_isIntegral_of_isField hinj h)
  have hdvr : IsDiscreteValuationRing O' := ((IsDiscreteValuationRing.TFAE O' hnf).out 0 2).mpr hded
  obtain ⟨e, he⟩ := exists_ramification O O' hinj
  refine ⟨O', inferInstance, inferInstance, hdvr, inferInstance, hfree, hfin, e, he, fun x => ?_⟩
  have hfr : IsFractionRing O' L := integralClosure.isFractionRing_of_finite_extension K L
  let σ : L →+* FractionRing O' := (FractionRing.algEquiv O' L).symm.toRingEquiv.toRingHom
  have hσ : (algebraMap O' (FractionRing O')).comp (algebraMap O O') =
      σ.comp ((algebraMap K L).comp (algebraMap O K)) := by
    refine RingHom.ext fun y => ?_
    have h1 : algebraMap K L (algebraMap O K y) = algebraMap O' L (algebraMap O O' y) := by
      rw [← IsScalarTower.algebraMap_apply O K L, ← IsScalarTower.algebraMap_apply O O' L]
    show _ = (FractionRing.algEquiv O' L).symm (algebraMap K L (algebraMap O K y))
    rw [h1, AlgEquiv.commutes]
    rfl
  rw [hσ, ← Polynomial.map_map, ← Polynomial.map_map]
  refine Polynomial.Splits.map ?_ σ
  have hQ : (Q.map (algebraMap K L)).Splits := Polynomial.SplittingField.splits Q
  have hQ0 : Q.map (algebraMap K L) ≠ 0 :=
    Polynomial.map_ne_zero (Finset.prod_ne_zero_iff.mpr fun x _ => ((hmon x).map _).ne_zero)
  exact hQ.of_dvd hQ0 (Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ x)))

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

-- bundled from Formalism.WachLatticeTwists.RamifiedBlockRings.RamifiedBlockProofs.TopLengthBoundViaSplitting
section
open Finset Classical

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.ringDataObjects

open Formalism.NG Formalism.RepresentationBoundsCohomology.BR

set_option maxHeartbeats 4000000 in
theorem top_length_bound_via_splitting :
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (X X' : Type)
    (T : Subalgebra O (X → O)) (T' : Subalgebra O (X' → O)) (Z : Set X) (p : X' → X) (q : ℕ)
    (b : Fin q → (X' → O)),
    (∀ f' ∈ T', ∃ a : Fin q → (X → O), (∀ k, a k ∈ T) ∧ f' = ∑ k, (a k ∘ p) * b k) →
    (∀ x ∉ Z, ∀ a : Fin q → O, (∀ x', p x' = x → ∑ k, a k * b k x' = 0) → a = 0) →
    ∀ (d : Type) [Fintype d] [DecidableEq d] (R' : Subalgebra O (X' → Matrix d d (FractionRing O)))
      [IsNoetherian R' R'],
    (∀ (g : Type) [Fintype g] [DecidableEq g] (Θ : Matrix g g R'), ∃ f ∈ T', ∀ x',
      algebraMap O (FractionRing O) (f x') =
        (bigMat (fun r : R' => (r : X' → Matrix d d (FractionRing O)) x') Θ).det) →
    ∀ (Tc : Type) [CommRing Tc] [Algebra Tc R'] [∀ x', Module Tc (EvalSp O d R' x')]
      [∀ x', IsScalarTower Tc R' (EvalSp O d R' x')]
      (G : Type) [Group G] (r : G →* R') (χ : G →* Tcˣ) (E e₁ : R') (δ : Tc)
      (ι : Type) [Fintype ι] [DecidableEq ι] (colIdx : ι → ℕ), Function.Injective colIdx →
    ∀ (D : ℕ → Subgroup G) (j e' : ℕ → ℕ) (Kc : ∀ l, Fin (j (colIdx l)) → G → R')
      (k0 : ι → G → R'),
      E * E = algebraMap Tc R' δ * E → e₁ * e₁ = e₁ →
    (∀ x', p x' ∉ Z →
      ∃ δx : FractionRing O, δx ≠ 0 ∧ (∀ v : EvalSp O d R' x', δ • v = δx • v) ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E)) = 1 ∧
      Module.finrank (FractionRing O)
        (LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁)) = 1 ∧
      (∀ η ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E), η ≠ 0 →
        ∃ g : G, ((((χ g)⁻¹ : Tcˣ) : Tc) • r g) • η ≠ η) ∧
      (∀ l, ∃ L : Submodule (FractionRing O) (D (colIdx l) → EvalSp O d R' x'),
        LinearMap.range (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l))) ≤ L ∧
        (∀ a, ∀ s ∈ LinearMap.range
            (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') e₁),
          (fun g : D (colIdx l) => Kc l a g • s) ∈ L) ∧
        (∀ s ∈ LinearMap.range (DistribSMul.toLinearMap (FractionRing O) (EvalSp O d R' x') E),
          (fun g : D (colIdx l) => k0 l g • s) ∈ L) ∧
        Module.rank (FractionRing O)
            (L ⧸ (LinearMap.range
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))).comap
              L.subtype) ≤
          (j (colIdx l) + Module.finrank (FractionRing O)
            (LinearMap.ker
              (colD (K := FractionRing O) (V := EvalSp O d R' x') r χ (D (colIdx l)))) : ℕ))) →
    ∀ (π' : X') (ρπ : R' →ₐ[O] Matrix d d O),
      (∀ r : R', (ρπ r).map (algebraMap O (FractionRing O)) = (r : X' → Matrix d d (FractionRing O)) π') →
    ∀ (t : ℕ) (ht : 1 ≤ t) (bl : d → Fin (t + 1)), (∀ r, (ρπ r).BlockTriangular bl) →
    ∀ (ρk : ∀ k : Fin (t + 1), R' →ₐ[O] Matrix {a // bl a = k} {a // bl a = k} O),
      (∀ k, Function.Surjective (ρk k)) → (∀ r k, (ρπ r).toSquareBlock bl k = ρk k r) →
      [∀ k, SMulCommClass R' O (blockRestrictedRepresentationType bl ρk k)] → [∀ k, Module Tc (blockRestrictedRepresentationType bl ρk k)] →
      [∀ k, IsScalarTower Tc R' (blockRestrictedRepresentationType bl ρk k)] → [∀ k, IsScalarTower O R' (blockRestrictedRepresentationType bl ρk k)] →
      vcc T Z (p π') ≤ ∑ k : Fin (t + 1), Module.length O
        (ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0 →ₗ[R'] blockRestrictedRepresentationType bl ρk k) →
      (∀ c : Fin (t + 1), c ≠ 0 → Fintype.card {a // bl a = c} = 1) →
    ∀ (sE : Finset G) (tE : G → Tc) (δO : O) (ℓ cB : ℕ) (what₂ qs : Finset ℕ)
      (deg : ℕ → ℕ) (s vhE H0 : ℕ∞) (Sha : ℕ → ℕ∞),
      E = ∑ g ∈ sE, tE g • r g → (∀ l g, ∃ a : R', k0 l g = a * E) →
    let NNc := ColNNJ r χ E e₁ δ (fun l => D (colIdx l)) (fun l => j (colIdx l)) Kc k0
    let cols : Finset ℕ := univ.image colIdx
    let eO : ℕ∞ := Module.length O (O ⧸ Ideal.span {(ℓ : O)})
    let vδ : ℕ∞ := IsDiscreteValuationRing.addVal O δO
    let N : ℕ∞ := Fintype.card {a // bl a = 0}
    let h0 : ℕ → ℕ∞ := fun w =>
      Module.length O (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk 0) r χ (D w)))

    ∀ (L : Type) [AddCommGroup L] [Module R' L] [Module O L]
      (tens : L →ₗ[O] KO O →ₗ[O] blockRestrictedRepresentationType bl ρk 0) (v₁ : L) (κ : ∀ l, Fin (j (colIdx l)) → G → L)
      (HcG : ∀ c, Submodule O (H1z (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ)))
      (Hc F : ∀ c w, Submodule O (H1z (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c) r χ) (D w))))
      (Vo VS : Type) (Io : Vo → Subgroup G) (IS : VS → Subgroup G) (ε : G →* Oˣ)
      (T₁ T₂ : Type) [AddCommGroup T₁] [Module O T₁] [AddCommGroup T₂] [Module O T₂]
      (ρ₁ : Representation O G T₁) (ρ₂ : Representation O G T₂) (inc : T₁ →ₗ[O] R')
      (π : T₁ →ₗ[O] T₂) (γ : T₂ →ₗ[O] blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O) (lam : blockRestrictedRepresentationType bl ρk 0 →ₗ[O] KO O)
      (Cs : ℕ → Type) [∀ w, AddCommGroup (Cs w)] [∀ w, Module O (Cs w)]
      (cls : ∀ w, (D w → T₂) → Cs w) (pr : ∀ w, Hc 0 w →ₗ[O] Cs w →ₗ[O] KO O)
      (Fs Im : ∀ w, Submodule O (Cs w))
      (cT : Fin (t + 1) → ℕ → ℕ) (I : ∀ w, Subgroup (D w)) (γQ : ∀ w, D w) (ζ : ℕ → Tc)
      (ζO : ℕ → O) (nQ : ∀ w, D w → ℕ) (u : ι → G → O),

    (∀ m : blockRestrictedRepresentationType bl ρk 0, E • m = 0) → (∀ m : blockRestrictedRepresentationType bl ρk 0, δ • m = δO • m) →
    (∀ m : blockRestrictedRepresentationType bl ρk 0, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) →
    Nonempty (↥(LinearMap.range (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk 0) e₁)) ≃ₗ[O] KO O) →
    InRho (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ colIdx D j e' Kc k0 ℓ what₂ s tens v₁ κ (HcG 0) (Hc 0) (F 0)
      Io ε ρ₁ ρ₂ inc π γ lam cls pr Fs Im →

    (∀ c : Fin (t + 1), 2 ≤ (c : ℕ) →
      (∀ m : blockRestrictedRepresentationType bl ρk c, e₁ • m = 0) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c, E • m = 0) ∧
      (∀ m : blockRestrictedRepresentationType bl ρk c, δ • m = δO • m) ∧
      (∀ m : blockRestrictedRepresentationType bl ρk c, (∑ g ∈ sE, tE g * ((χ g : Tcˣ) : Tc)) • m = δO • m) ∧
      (∀ w ∈ cols, Module.length O
        (LinearMap.ker (colDO (O := O) (M := blockRestrictedRepresentationType bl ρk c) r χ (D w))) ≤ H0) ∧
      InChi (blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ colIdx D j Kc k0 ℓ cB what₂ qs deg (cT c)
        (Sha ((c : ℕ) - 1)) (HcG c) (Hc c) (F c) Io IS I γQ ζ ζO nQ) →

    (let c1 : Fin (t + 1) := ⟨1, by omega⟩
     (∀ g (m : blockRestrictedRepresentationType bl ρk c1), uElt r χ g • m = m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, e₁ • m = 0) ∧
     (∀ m : blockRestrictedRepresentationType bl ρk c1, E • m = δO • m) ∧ (∀ m : blockRestrictedRepresentationType bl ρk c1, δ • m = δO • m) ∧
     (∀ l, ∀ g ∈ D (colIdx l), ∀ m : blockRestrictedRepresentationType bl ρk c1,
       k0 l g • m = ((ℓ : O) ^ e' (colIdx l) * δO * u l g) • m) ∧
     (∀ l, ∀ g ∈ I (colIdx l), u l (g : G) = 0) ∧ (∀ l, ∃ g ∈ D (colIdx l), u l g = 1) ∧
     (∀ l, unrH1 (resRep (uRep O (M := blockRestrictedRepresentationType bl ρk c1) r χ) (D (colIdx l))) (I (colIdx l)) ≤
       F c1 (colIdx l)) ∧
     InChi (blockRestrictedRepresentationType bl ρk c1) r χ E e₁ δ colIdx D j Kc k0 ℓ cB what₂ qs deg (cT c1) vhE
       (HcG c1) (Hc c1) (F c1) Io IS I γQ ζ ζO nQ) →
    vcc T Z (p π') ≤
      ∑ w ∈ what₂, Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype) +
        ∑ w ∈ cols, (eO * (e' w : ℕ∞) + (j w : ℕ∞) * (eO * (e' w : ℕ∞) + vδ) + 2 * vδ + h0 w) + s +
        ∑ e ∈ Finset.Ioo 0 t, Sha e + vhE +
        (t : ℕ∞) * eO * (cB : ℕ∞) * ∑ w ∈ what₂, ((deg w : ℕ∞) + 2) +
        4 * (N + t) * ((cols.card : ℕ∞) + 1) * vδ +
        (t : ℕ∞) * (cols.card : ℕ∞) * H0 + (t : ℕ∞) * ∑ w ∈ qs, IsDiscreteValuationRing.addVal O (ζO w - 1) := by
  intro O _ _ _ X X' T T' Z p q b ha hb d _ _ R' _ hc Tc _ _ _ _ G _ r χ E e₁ δ ι _ _ colIdx hinj
    D j e' Kc k0 hEE hee hpts π' ρπ hρπ t ht bl hbl ρk hsurj hblk _ _ _ _ hG hcard1
    sE tE δO ℓ cB what₂ qs deg s vhE H0 Sha hEsum hk0 NNc cols eO vδ N h0
    L _ _ _ tens v₁ κ HcG Hc F Vo VS Io IS ε T₁ T₂ _ _ _ _ ρ₁ ρ₂ inc π γ lam Cs _ _ cls pr Fs Im
    cT I γQ ζ ζO nQ u hE0 hδ0 hτ0 hne hIn0 hC hOne
  have hlen : ∀ c : Fin (t + 1), c ≠ 0 →
      (fun w => Module.length O (LinearMap.ker
        (DistribSMul.toLinearMap O (blockRestrictedRepresentationType bl ρk c) (ζO w - 1)))) =
      fun w => IsDiscreteValuationRing.addVal O (ζO w - 1) := by
    intro c hc0
    funext w
    have h := KernelLengthBounds.length_ker_smul_pi (O := O) {a // bl a = c} (ζO w - 1)
    rw [hcard1 c hc0, Nat.cast_one, one_mul] at h
    exact h
  have h0b := bridgeRho O R' Tc G (blockRestrictedRepresentationType bl ρk 0) r χ E e₁ δ δO ι colIdx D j e' Kc k0 ℓ what₂ s
    L tens v₁ κ (HcG 0) (Hc 0) (F 0) Vo Io ε T₁ T₂ ρ₁ ρ₂ inc π γ lam Cs cls pr Fs Im hee hE0 hk0
    (fun m => by rw [algebraMap_smul]; exact hδ0 m) hIn0
  refine length_bound_via_splitting O X X' T T' Z p q b ha hb d R' hc Tc G r χ E e₁ δ ι colIdx hinj D j e' Kc k0 hEE hee
    hpts π' ρπ hρπ t ht bl hbl ρk hsurj hblk hG hcard1 sE tE δO ℓ cB what₂ qs
    (fun w => Module.length O (Fs w ⧸ (Im w).comap (Fs w).subtype)) deg
    (fun w => IsDiscreteValuationRing.addVal O (ζO w - 1)) s vhE H0 Sha hEsum hk0
    hE0 hδ0 hτ0 hne h0b.1 ?_ ?_ ?_
  · have h02 := h0b.2
    unfold OutRho at h02
    obtain ⟨F', Q', x1, x2, x3, x4⟩ := h02
    refine ⟨F', Q', ?_, ?_, ?_, ?_⟩
    · exact x1
    · exact x2
    · exact x3
    · exact x4
  · intro c hc2
    obtain ⟨a1, a2, a3, a4, a5, hIn⟩ := hC c hc2
    have hc0 : c ≠ 0 := by
      intro h
      rw [h] at hc2
      simp at hc2
    have hout := bridgeChiC O R' Tc G (blockRestrictedRepresentationType bl ρk c) r χ E e₁ δ ι colIdx D j Kc k0 ℓ cB what₂ qs
      deg (cT c) (Sha ((c : ℕ) - 1)) (HcG c) (Hc c) (F c) Vo VS Io IS I γQ ζ ζO nQ a1 a2 hk0 hIn
    rw [hlen c hc0] at hout
    unfold OutChi at hout
    exact ⟨a1, a2, a3, a4, a5, hout⟩
  · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, hIn⟩ := hOne
    have hc0 : (⟨1, by omega⟩ : Fin (t + 1)) ≠ 0 := by
      intro h
      have := congrArg Fin.val h
      simp at this
    have hout := bridgeChiOne O R' Tc G (blockRestrictedRepresentationType bl ρk ⟨1, by omega⟩) r χ E e₁ δ δO ι colIdx D j e'
      Kc k0 ℓ cB what₂ qs deg (cT _) vhE (HcG _) (Hc _)
      (F _) Vo VS Io IS I γQ ζ ζO nQ u a1 a2 a3
      (fun m => by rw [algebraMap_smul]; exact a4 m) a5 a6 a7 a8 hIn
    rw [hlen _ hc0] at hout
    unfold OutChi at hout
    exact ⟨a1, a2, a3, a4, hout.1, hout.2⟩

end Formalism.RepresentationBoundsCohomology.ringDataObjects
end
end

