import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PMobiusAlgIndep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

theorem MobiusAlgIndep.proof : MobiusAlgIndep.Statement := by
  intro Ω _ Φ _ _ n a p q p' q' ha hdet
  have hden : ∀ j, algebraMap Ω Φ p' + a j * algebraMap Ω Φ q' ≠ 0 := by
    intro j h
    by_cases hq' : q' = 0
    · subst hq'
      have hp' : p' = 0 := by simpa using h
      exact hdet (by simp [hp'])
    · apply ha.transcendental j
      have hq : algebraMap Ω Φ q' ≠ 0 := by simpa using hq'
      have : a j = algebraMap Ω Φ (-p' / q') := by
        rw [map_div₀, map_neg]
        field_simp
        linear_combination h
      rw [this]
      exact isAlgebraic_algebraMap _
  refine ⟨hden, ?_⟩
  set b : Fin n → Φ := fun j => (algebraMap Ω Φ p + a j * algebraMap Ω Φ q) /
    (algebraMap Ω Φ p' + a j * algebraMap Ω Φ q') with hb

  have hrel : ∀ j, (algebraMap Ω Φ q' * b j - algebraMap Ω Φ q) * a j =
      algebraMap Ω Φ p - algebraMap Ω Φ p' * b j := by
    intro j
    have hbD : b j * (algebraMap Ω Φ p' + a j * algebraMap Ω Φ q') =
        algebraMap Ω Φ p + a j * algebraMap Ω Φ q := div_mul_cancel₀ _ (hden j)
    linear_combination hbD
  have hc : ∀ j, algebraMap Ω Φ q' * b j - algebraMap Ω Φ q ≠ 0 := by
    intro j h
    have h2 := hrel j
    rw [h, zero_mul] at h2
    apply hdet
    apply (algebraMap Ω Φ).injective
    simp only [map_sub, map_mul, map_zero]
    linear_combination algebraMap Ω Φ p' * h - algebraMap Ω Φ q' * h2

  let S : Set Φ := Set.range a ∪ Set.range b
  let A := Algebra.adjoin Ω S
  let a' : Fin n → A := fun j => ⟨a j, Algebra.subset_adjoin (Or.inl ⟨j, rfl⟩)⟩
  let b' : Fin n → A := fun j => ⟨b j, Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)⟩
  have ha' : AlgebraicIndependent Ω a' := AlgebraicIndependent.of_comp A.val ha
  have halg : Algebra.IsAlgebraic (Algebra.adjoin Ω (Set.range b')) A := by
    refine ⟨fun z => ?_⟩
    have hz : z ∈ Algebra.adjoin Ω (((↑) : A → Φ) ⁻¹' S) := by
      rw [Algebra.adjoin_adjoin_coe_preimage]; trivial
    refine IsAlgebraic.adjoin_of_forall_isAlgebraic (R := Ω) (s := ((↑) : A → Φ) ⁻¹' S)
      (t := Set.range b') ?_ (isAlgebraic_algebraMap (⟨z, hz⟩ : Algebra.adjoin Ω (((↑) : A → Φ) ⁻¹' S)))
    rintro x ⟨hxS, hxb⟩
    rcases hxS with ⟨j, hj⟩ | ⟨j, hj⟩
    · have hx : x = a' j := Subtype.ext hj.symm
      subst hx
      let bj : Algebra.adjoin Ω (Set.range b') := ⟨b' j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
      let c : Algebra.adjoin Ω (Set.range b') :=
        algebraMap Ω _ q' * bj - algebraMap Ω _ q
      let d : Algebra.adjoin Ω (Set.range b') :=
        algebraMap Ω _ p - algebraMap Ω _ p' * bj
      refine IsAlgebraic.of_mul (y := algebraMap _ A c) ?_ (isAlgebraic_algebraMap c) ?_
      · apply mem_nonZeroDivisors_of_ne_zero
        intro h0
        apply hc j
        have h1 := congrArg (fun w : A => (w : Φ)) h0
        exact h1
      · have h3 : algebraMap _ A c * a' j = algebraMap _ A d := by
          apply Subtype.ext
          exact hrel j
        rw [h3]
        exact isAlgebraic_algebraMap d
    · exact absurd ⟨j, Subtype.ext hj⟩ hxb
  have hn : Cardinal.mk (Fin n) ≤ Algebra.trdeg Ω A := ha'.cardinalMk_le_trdeg
  have hT := Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω b' hn
  exact hT.1.map' (f := A.val) Subtype.val_injective

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PThmIUnique
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

namespace ThmIUnique

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem recR_congr {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (P : Ideal (MRing ι))
    {n : ℕ} (L : Fin n → HermLine ι) (A : HermLine ι) (s : MRing ι)
    (h : ∀ W ∈ divSupp P s, IsHorizontal W → I W n L = J W n L) :
    recR I P L A s = recR J P L A s := by
  classical
  unfold recR
  congr 1
  refine finsum_mem_congr rfl fun W hW => ?_
  by_cases hh : IsHorizontal W
  · rw [if_pos hh, if_pos hh, h W hW hh]
  · rw [if_neg hh, if_neg hh]

theorem isMultiHomog_one' : IsMultiHomog (1 : MRing ι) 0 := by
  classical
  intro m hm k
  rw [MvPolynomial.support_one, Finset.mem_singleton] at hm
  subst hm
  simp

theorem isMultiHomog_mul' {f g : MRing ι} {a b : K → ℕ} (hf : IsMultiHomog f a)
    (hg : IsMultiHomog g b) : IsMultiHomog (f * g) (a + b) := by
  classical
  intro m hm k
  obtain ⟨m1, hm1, m2, hm2, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul f g hm)
  simp only [Finsupp.add_apply, Finset.sum_add_distrib, Pi.add_apply, hf m1 hm1 k, hg m2 hm2 k]

open Classical in

theorem isMultiHomog_X' (k : K) (i : ι k) :
    IsMultiHomog (X ⟨k, i⟩ : MRing ι) (Pi.single k 1) := by
  classical
  intro m hm k'
  rw [MvPolynomial.support_X, Finset.mem_singleton] at hm
  subst hm
  by_cases h : k' = k
  · subst h
    simp [Finsupp.single_apply]
  · have : ∀ j : ι k', (⟨k, i⟩ : Σ k, ι k) ≠ ⟨k', j⟩ := fun j e => h (congrArg Sigma.fst e).symm
    simp [Finsupp.single_apply, this, h, Pi.single_apply]

theorem isMultiHomog_pow' {f : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (n : ℕ) :
    IsMultiHomog (f ^ n) (n • a) := by
  induction n with
  | zero => simpa using (isMultiHomog_one' (ι := ι))
  | succ n ih =>
    rw [pow_succ, succ_nsmul]
    exact isMultiHomog_mul' ih hf

theorem isMultiHomog_coordMonomial (c : ∀ k, ι k) (d : K → ℕ) :
    IsMultiHomog (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) d := by
  classical
  have key : ∀ s : Finset K, IsMultiHomog (∏ k ∈ s, (X ⟨k, c k⟩ : MRing ι) ^ d k)
      (∑ k ∈ s, d k • Pi.single k 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (isMultiHomog_one' (ι := ι))
    | insert k s hk ih =>
      rw [Finset.prod_insert hk, Finset.sum_insert hk]
      exact isMultiHomog_mul' (isMultiHomog_pow' (isMultiHomog_X' k (c k)) _) ih
  have e : (∑ k, d k • (Pi.single k 1 : K → ℕ)) = d := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have := key Finset.univ
  rwa [e] at this

theorem coordMonomial_not_mem {P : Ideal (MRing ι)} (hP : P.IsPrime) (c : ∀ k, ι k)
    (hc : ∀ k, (X ⟨k, c k⟩ : MRing ι) ∉ P) (d : K → ℕ) :
    (∏ k, (X ⟨k, c k⟩ : MRing ι) ^ d k) ∉ P := by
  intro h
  obtain ⟨k, -, hk⟩ := (hP.prod_mem_iff).mp h
  exact hc k (hP.mem_of_pow_mem _ hk)

theorem eq_of_lower {I J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsRFamily I) (hJ : IsRFamily J) {P : Ideal (MRing ι)} {m : ℕ}
    (L : Fin m → HermLine ι) (A : HermLine ι) (hP : IsArithVar P (m + 1))
    (hL : ∀ j, IsSmoothHerm (L j)) (hA : IsSmoothHerm A)
    (hlow : ∀ W, IsArithVar W m → I W m L = J W m L) :
    I P (m + 1) (Fin.snoc L A) = J P (m + 1) (Fin.snoc L A) := by
  classical
  have hPp : P.IsPrime := hP.2.1.1
  choose c hc using hP.2.1.2.2

  let b : K → ℕ := fun k => (-A.a k).toNat
  let e : K → ℕ := fun k => (A.a k + (b k : ℤ)).toNat
  let B : HermLine ι := HermLine.sqMetric b
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric b
  have hC : IsSmoothHerm (A.tensor B) := isSmoothHerm_tensor hA hB
  have hBa : ∀ k, B.a k = (b k : ℤ) := fun k => rfl
  have hCa : ∀ k, (A.tensor B).a k = (e k : ℤ) := by
    intro k
    have h0 : (0 : ℤ) ≤ A.a k + ((-A.a k).toNat : ℤ) := by
      rw [Int.toNat_eq_max]
      omega
    exact (Int.toNat_of_nonneg h0).symm
  let sB : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ b k
  let sC : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ e k
  have hsB : IsMultiHomog sB b := isMultiHomog_coordMonomial c b
  have hsC : IsMultiHomog sC e := isMultiHomog_coordMonomial c e
  have hsBP : sB ∉ P := coordMonomial_not_mem hPp c hc b
  have hsCP : sC ∉ P := coordMonomial_not_mem hPp c hc e

  have diff : ∀ F : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ, IsRFamily F →
      F P (m + 1) (Fin.snoc L A) = recR F P L (A.tensor B) sC - recR F P L B sB := by
    intro F hF
    have h1 := hF.1 P m L A B hP hL hA hB
    rw [hF.2 P m L (A.tensor B) sC e hP hL hC hCa hsC hsCP,
      hF.2 P m L B sB b hP hL hB hBa hsB hsBP] at h1
    linarith
  have hor : ∀ (X' : HermLine ι) (s : MRing ι), IsSectionOn P X' s →
      ∀ W ∈ divSupp P s, IsHorizontal W → I W m L = J W m L := fun X' s hs W hW hh =>
    hlow W ((divSuppArith K ι P m X' s W hP hs hW).1 hh)
  rw [diff I hI, diff J hJ,
    recR_congr P L (A.tensor B) sC (hor _ sC ⟨e, hCa, hsC, hsCP⟩),
    recR_congr P L B sB (hor _ sB ⟨b, hBa, hsB, hsBP⟩)]

end ThmIUnique

theorem ThmIUnique.proof (h₀ : ArithVarZeroStatement) : ThmIUnique.Statement := by
  unfold ThmIUnique.Statement UniqueStatement
  intro K _ ι _ I J hI hJ
  have key : ∀ (m : ℕ) (P : Ideal (MRing ι)) (L : Fin (m + 1) → HermLine ι), IsArithVar P (m + 1) →
      (∀ j, IsSmoothHerm (L j)) → I P (m + 1) L = J P (m + 1) L := by
    intro m
    induction m with
    | zero =>
      intro P L hP hL
      rw [← Fin.snoc_init_self L]
      exact ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _)
        fun W hW => absurd hW (h₀ K ι W)
    | succ m ih =>
      intro P L hP hL
      rw [← Fin.snoc_init_self L]
      exact ThmIUnique.eq_of_lower hI hJ _ _ hP (fun j => hL j.castSucc) (hL _)
        fun W hW => ih W _ hW fun j => hL j.castSucc
  intro P n L hn hP hL
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact key m P L hP hL

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PYYRatioBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.T

noncomputable section

theorem isAlgebraic_map_of_map_le {Ω Φ : Type*} [Field Ω] [Field Φ] [Algebra ℚ Ω] [Algebra ℚ Φ]
    (f : Ω →ₐ[ℚ] Φ) {L : IntermediateField ℚ Ω} {M : IntermediateField ℚ Φ} (hLM : L.map f ≤ M) {y : Ω}
    (hy : IsAlgebraic L y) : IsAlgebraic M (f y) := by
  obtain ⟨p, hp, hpy⟩ := hy
  let ψ : L →+* M := ((f : Ω →+* Φ).comp (algebraMap L Ω)).codRestrict M (fun z => hLM ⟨z, z.2, rfl⟩)
  have hψ : (algebraMap M Φ).comp ψ = (f : Ω →+* Φ).comp (algebraMap L Ω) := by
    ext z; rfl
  refine ⟨p.map ψ, (Polynomial.map_ne_zero_iff ψ.injective).mpr hp, ?_⟩
  have h := congrArg f hpy
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hψ]
  rw [Polynomial.aeval_def, map_zero] at h
  rw [← h]
  exact (Polynomial.hom_eval₂ p (algebraMap L Ω) (f : Ω →+* Φ) y).symm

theorem YYRatioBasis.proof (hM : MobiusAlgIndep.Statement) : YYRatioBasis.Statement := by
  intro Ω _ _ ι ν κ _ _ _ E _ _ Φ _ _ _ x e b φ δ g i₀ l₀ k₀ k₁ d t a hx ht htF htalg hδ hδF hφb hgF hD ha
  let f : Ω →ₐ[ℚ] Φ := IsScalarTower.toAlgHom ℚ Ω Φ
  have hf : ∀ z, f z = algebraMap Ω Φ z := fun _ => rfl
  have hφe : ∀ k p, φ k (e p) = x i₀ * (b.repr (e p) 0 * g k 0 + b.repr (e p) 1 * g k 1) := by
    intro k p
    conv_lhs => rw [← b.sum_repr (e p)]
    simp only [map_add, map_smul, Fin.sum_univ_two, hφb, smul_eq_mul]; ring
  have hB : b.repr (e 0) 0 * b.repr (e 1) 1 - b.repr (e 1) 0 * b.repr (e 0) 1 ≠ 0 := by
    intro h0
    have h := congrArg Matrix.det (b.toMatrix_mul_toMatrix_flip e)
    rw [Matrix.det_mul, Matrix.det_one, Matrix.det_fin_two] at h
    simp only [Module.Basis.toMatrix_apply, h0, zero_mul] at h
    exact zero_ne_one h
  have hdet : φ k₁ (e 0) * φ k₀ (e 1) - φ k₁ (e 1) * φ k₀ (e 0) ≠ 0 := by
    have : φ k₁ (e 0) * φ k₀ (e 1) - φ k₁ (e 1) * φ k₀ (e 0) = -(x i₀ ^ 2 *
        (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0) * (b.repr (e 0) 0 * b.repr (e 1) 1 - b.repr (e 1) 0 * b.repr (e 0) 1)) := by
      rw [hφe, hφe, hφe, hφe]; ring
    rw [this]; exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hx) hD) hB)
  obtain ⟨hden, hmob⟩ := hM Ω Φ 1 (fun _ => a) (φ k₁ (e 0)) (φ k₁ (e 1)) (φ k₀ (e 0)) (φ k₀ (e 1))
    (algebraicIndependent_unique_type_iff.mpr ha) hdet
  have hu : lineVal e (φ k₀) a ≠ 0 := hden 0
  set r := lineVal e (φ k₁) a / lineVal e (φ k₀) a with hr
  have hy : AlgebraicIndependent Ω (fun _ : Fin 1 => r) := hmob
  let σ : Fin (d + 1) ≃ Fin 1 ⊕ Fin d := finSumFinEquiv.symm.trans (Equiv.sumComm _ _)
  let t' : Fin (d + 1) → Φ := Sum.elim (fun _ : Fin 1 => r) (algebraMap Ω Φ ∘ t) ∘ σ
  have ht' : ∀ n, t' n = r ∨ ∃ m, t' n = f (t m) := by
    intro n; rcases h : σ n with j | m
    · exact Or.inl (by simp [t', h])
    · exact Or.inr ⟨m, by simp [t', h, hf]⟩
  have hr_mem : r ∈ Set.range t' := ⟨σ.symm (Sum.inl 0), by simp [t']⟩
  have ht_mem : ∀ m, f (t m) ∈ Set.range t' := fun m => ⟨σ.symm (Sum.inr m), by simp [t', hf]⟩
  let c : ∀ k, T.yyIdx ι ν κ k := fun | .base => i₀ | .det => l₀ | .line => k₀
  set S := coneRatios (T.yyCoord x δ e φ a) c
  set F := IntermediateField.adjoin ℚ (Set.range fun j => x j / x i₀)
  have hF : ∀ z ∈ F, f z ∈ F.map f := fun z hz => ⟨z, hz, rfl⟩
  refine ⟨c, t', ?_, (AlgebraicIndependent.sumElim_comp ht hy).comp σ σ.injective, ?_, ?_⟩
  · rintro (_ | _ | _)
    · exact (map_ne_zero _).mpr hx
    · exact (map_ne_zero _).mpr hδ
    · exact hu
  · have hFS : F.map f ≤ IntermediateField.adjoin ℚ S := by
      rw [IntermediateField.adjoin_map]
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      refine IntermediateField.subset_adjoin _ _ ⟨⟨.base, j⟩, ?_⟩
      show algebraMap Ω Φ (x j) / algebraMap Ω Φ (x i₀) = f (x j / x i₀)
      rw [hf, map_div₀]
    intro n
    rcases ht' n with h | ⟨m, h⟩ <;> rw [h]
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨.line, k₁⟩, rfl⟩
    · exact hFS (hF _ (htF m))
  · set M := IntermediateField.adjoin ℚ (Set.range t')
    let A := (algebraicClosure M Φ).restrictScalars ℚ
    have hMA : ∀ z ∈ M, z ∈ A := fun z hz =>
      mem_algebraicClosure_iff.mpr (isAlgebraic_algebraMap (⟨z, hz⟩ : M))
    have hLM : (IntermediateField.adjoin ℚ (Set.range t)).map f ≤ M := by
      rw [IntermediateField.adjoin_map]
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨_, ⟨m, rfl⟩, rfl⟩
      exact IntermediateField.subset_adjoin _ _ (ht_mem m)
    have hFA : F.map f ≤ A := by
      rw [IntermediateField.adjoin_map]
      refine IntermediateField.adjoin_le_iff.mpr ?_
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      exact mem_algebraicClosure_iff.mpr (isAlgebraic_map_of_map_le f hLM (htalg j))
    have hFA' : ∀ z ∈ F, f z ∈ A := fun z hz => hFA (hF z hz)
    have hrA : r ∈ A := hMA r (IntermediateField.subset_adjoin _ _ hr_mem)
    have key : ∀ k, lineVal e (φ k) a = f (x i₀) * (f (g k 0) * (f (b.repr (e 0) 0) + a * f (b.repr (e 1) 0)) +
        f (g k 1) * (f (b.repr (e 0) 1) + a * f (b.repr (e 1) 1))) := by
      intro k; simp only [lineVal, hφe, map_add, map_mul, hf]; ring
    have hD' : f (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0) ≠ 0 := (map_ne_zero f).mpr hD
    have hline : ∀ k, lineVal e (φ k) a / lineVal e (φ k₀) a = (f (g k 0) * (f (g k₁ 1) - f (g k₀ 1) * r) +
        f (g k 1) * (f (g k₀ 0) * r - f (g k₁ 0))) / f (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0) := by
      intro k
      have hkey : f (g k₀ 0 * g k₁ 1 - g k₀ 1 * g k₁ 0) * lineVal e (φ k) a =
          f (g k 0) * (f (g k₁ 1) * lineVal e (φ k₀) a - f (g k₀ 1) * lineVal e (φ k₁) a) +
          f (g k 1) * (f (g k₀ 0) * lineVal e (φ k₁) a - f (g k₁ 0) * lineVal e (φ k₀) a) := by
        rw [key k, key k₀, key k₁, map_sub, map_mul, map_mul]; ring
      rw [hr, eq_div_iff hD']
      field_simp
      linear_combination hkey
    intro s hs
    suffices s ∈ A from mem_algebraicClosure_iff.mp this
    obtain ⟨⟨k, i⟩, rfl⟩ := hs
    cases k
    · show algebraMap Ω Φ (x i) / algebraMap Ω Φ (x i₀) ∈ A
      rw [← map_div₀]
      exact hFA' _ (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · show algebraMap Ω Φ (δ i) / algebraMap Ω Φ (δ l₀) ∈ A
      rw [← map_div₀]
      exact hFA' _ (hδF i)
    · show lineVal e (φ i) a / lineVal e (φ k₀) a ∈ A
      rw [hline i]
      have hg : ∀ k q, f (g k q) ∈ A := fun k q => hFA' _ (hgF k q)
      refine div_mem (add_mem (mul_mem (hg _ _) (sub_mem (hg _ _) (mul_mem (hg _ _) hrA)))
        (mul_mem (hg _ _) (sub_mem (mul_mem (hg _ _) hrA) (hg _ _)))) ?_
      exact hFA' _ (sub_mem (mul_mem (hgF _ _) (hgF _ _)) (mul_mem (hgF _ _) (hgF _ _)))

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.RegLine
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

set_option linter.unusedSectionVars false

section Objects

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]

def secNorm (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ‖eval z (map (Int.castRingHom ℂ) t)‖ / E.h z

theorem logNorm_eq_log_secNorm (E : HermLine ι) (t : MRing ι) (z : (Σ k, ι k) → ℂ) :
    logNorm E t z = Real.log (secNorm E t z) := rfl

theorem secNorm_nonneg (E : HermLine ι) (t : MRing ι) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    0 ≤ secNorm E t z :=
  div_nonneg (norm_nonneg _) (E.pos z hz).le

theorem secNorm_smul {E : HermLine ι} {t : MRing ι} {a : K → ℕ} (hE : ∀ k, E.a k = a k)
    (ht : IsMultiHomog t a) {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (z : (Σ k, ι k) → ℂ) :
    secNorm E t (fun p => c p.1 * z p) = secNorm E t z := by
  have he := eval_bsmul_of_isMultiHomog ht c z
  have hh : E.h (bsmul c z) = (∏ k, ‖c k‖ ^ E.a k) * E.h z := E.smul c z hc
  have hpos : 0 < ∏ k, ‖c k‖ ^ E.a k :=
    Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
  have hn : ‖∏ k, c k ^ a k‖ = ∏ k, ‖c k‖ ^ E.a k := by
    rw [norm_prod]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_pow, hE k, zpow_natCast]
  change ‖eval (bsmul c z) (map (Int.castRingHom ℂ) t)‖ / E.h (bsmul c z) = _
  rw [he, hh, norm_mul, hn, mul_div_mul_left _ _ hpos.ne']
  rfl

def regLine (E : HermLine ι) (t : MRing ι) (ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a)
    (ε : ℝ) : HermLine ι :=
  HermLine.ofWeight (fun z => -(Real.log (secNorm E t z ^ 2 + ε) / 2)) (by
    intro c z hc
    obtain ⟨a, hE, hta⟩ := ht
    simp only [secNorm_smul hE hta hc z])

variable {E : HermLine ι} {t : MRing ι} {ht : ∃ a : K → ℕ, (∀ k, E.a k = a k) ∧ IsMultiHomog t a}
  {ε : ℝ}

theorem regLine_a : (regLine E t ht ε).a = 0 := rfl

theorem regLine_h (z : (Σ k, ι k) → ℂ) :
    (regLine E t ht ε).h z = Real.exp (Real.log (secNorm E t z ^ 2 + ε) / 2) := by
  simp [regLine, HermLine.ofWeight]

theorem log_regLine_h (z : (Σ k, ι k) → ℂ) :
    Real.log ((regLine E t ht ε).h z) = Real.log (secNorm E t z ^ 2 + ε) / 2 := by
  rw [regLine_h, Real.log_exp]

theorem contDiff_eval_map (t : MRing ι) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : (Σ k, ι k) → ℂ => eval z (map (Int.castRingHom ℂ) t)) := by
  induction t using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p v hp => simpa using hp.mul (contDiff_apply ℝ ℂ v)

theorem isSmoothHerm_regLine (hE : IsSmoothHerm E) (hε : 0 < ε) : IsSmoothHerm (regLine E t ht ε) := by
  unfold IsSmoothHerm
  have hn : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : (Σ k, ι k) → ℂ => ‖eval z (map (Int.castRingHom ℂ) t)‖ ^ 2) :=
    (contDiff_norm_sq ℝ).comp (contDiff_eval_map t)
  have hq : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z => ‖eval z (map (Int.castRingHom ℂ) t)‖ ^ 2 / E.h z ^ 2 + ε)
      {z : (Σ k, ι k) → ℂ | ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0} :=
    (hn.contDiffOn.div (hE.pow 2) fun z hz => pow_ne_zero _ (E.pos z hz).ne').add contDiffOn_const
  have hl := (hq.log fun z hz => (add_pos_of_nonneg_of_pos
    (div_nonneg (sq_nonneg _) (sq_nonneg _)) hε).ne').div_const 2
  refine (Real.contDiff_exp.comp_contDiffOn hl).congr fun z _ => ?_
  rw [regLine_h, secNorm, div_pow]
  rfl

theorem logNorm_le_log_regLine_h (hε : 0 ≤ ε) {z : (Σ k, ι k) → ℂ} (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0)
    (ht0 : eval z (map (Int.castRingHom ℂ) t) ≠ 0) :
    logNorm E t z ≤ Real.log ((regLine E t ht ε).h z) := by
  rw [log_regLine_h, logNorm_eq_log_secNorm]
  have hpos : 0 < secNorm E t z := div_pos (norm_pos_iff.mpr ht0) (E.pos z hz)
  have h2 : Real.log (secNorm E t z) = Real.log (secNorm E t z ^ 2) / 2 := by
    rw [Real.log_pow]
    push_cast
    ring
  rw [h2]
  exact div_le_div_of_nonneg_right (Real.log_le_log (by positivity) (by linarith)) (by norm_num)

end Objects

theorem isMultiHomog_planeCoordinate (i : Fin 3) : ∃ a : Unit → ℕ, (∀ k, (fsLine 3).a k = a k) ∧ IsMultiHomog (Xc 3 i) a := by
  obtain ⟨a, ha, hm, -⟩ := isSectionOn_coordinate_plane i
  exact ⟨a, ha, hm⟩

theorem regLine.inhabited :
    IsSmoothHerm (regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1) ∧
      (regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1).a = 0 ∧
      ∀ z ∈ mcPts (⊥ : Ideal (MRing (PBlk 3))), eval z (map (Int.castRingHom ℂ) (Xc 3 0)) ≠ 0 →
        logNorm (fsLine 3) (Xc 3 0) z ≤
          Real.log ((regLine (fsLine 3) (Xc 3 0) (isMultiHomog_planeCoordinate 0) 1).h z) :=
  ⟨isSmoothHerm_regLine (isSmoothHerm_fsLine 3) one_pos, rfl,
    fun _ hz h0 => logNorm_le_log_regLine_h zero_le_one hz.1 h0⟩

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StLocRingFrac
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def LocRingFrac.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    P.IsPrime → W.IsPrime → P ≤ W →
    ∀ y ∈ locRing P W, ∃ (u v : MRing ι) (a : K → ℕ),
      IsMultiHomog u a ∧ IsMultiHomog v a ∧ v ∉ W ∧ y * algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P v) = algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u)

end

end GroundTheory.Heights₂.Heights.Inter
end

