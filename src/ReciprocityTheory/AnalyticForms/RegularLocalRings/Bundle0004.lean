import ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCA
import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.HeightAddRingKrullDimQuotientMvPolynomialField
import Mathlib
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartB

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.BaseChangeCB
section
namespace ReciprocityTheory.AnForm.R.BaseChangeC

open MvPolynomial TensorProduct

variable {σ : Type} [Fintype σ]

noncomputable def quotExtEquiv (𝔭 : Ideal (MvPolynomial σ ℚ)) :
    (ℂ ⊗[ℚ] (MvPolynomial σ ℚ ⧸ 𝔭)) ≃+* (MvPolynomial σ ℂ ⧸ Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭) :=
  (Algebra.TensorProduct.tensorQuotientEquiv (R := ℚ) ℂ (MvPolynomial σ ℚ) ℂ 𝔭).toRingEquiv.trans
    (Ideal.quotientEquiv _ _ (algebraTensorAlgEquiv ℚ ℂ).toRingEquiv (by
      have h : (algebraTensorAlgEquiv (σ := σ) ℚ ℂ).toRingEquiv.toRingHom.comp
          (Algebra.TensorProduct.includeRight : MvPolynomial σ ℚ →ₐ[ℚ] ℂ ⊗[ℚ] MvPolynomial σ ℚ).toRingHom
          = MvPolynomial.map (algebraMap ℚ ℂ) := by
        apply RingHom.ext
        intro p
        simp [Algebra.TensorProduct.includeRight_apply, algebraTensorAlgEquiv_tmul]
      rw [← h, ← Ideal.map_map]
      rfl))

section Rad

theorem isRadical_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime] : (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).IsRadical := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  set A := MvPolynomial σ ℚ ⧸ 𝔭
  set K := FractionRing A
  have : Algebra.EssFiniteType ℚ K := inferInstanceAs (Algebra.EssFiniteType ℚ (Localization _))
  have h1 : IsReduced (K ⊗[ℚ] ℂ) := isReduced_tensor_of_essFiniteType K ℂ
  have h2 : IsReduced (ℂ ⊗[ℚ] K) :=
    isReduced_of_injective (Algebra.TensorProduct.comm ℚ ℂ K).toRingEquiv.toRingHom
      (Algebra.TensorProduct.comm ℚ ℂ K).injective
  have hinj : Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ A K)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ (IsFractionRing.injective _ _)
  have h3 : IsReduced (ℂ ⊗[ℚ] A) := isReduced_of_injective (Algebra.TensorProduct.map (AlgHom.id ℚ ℂ)
      (IsScalarTower.toAlgHom ℚ A K)).toRingHom hinj
  exact isReduced_of_injective (quotExtEquiv 𝔭).symm.toRingHom (quotExtEquiv 𝔭).symm.injective

end Rad

section GD

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem flat_mvPolynomial_rat_complex :
    Module.Flat (MvPolynomial σ ℚ) (MvPolynomial σ ℂ) :=
  Module.Flat.isBaseChange ℚ (MvPolynomial σ ℚ) ℂ (MvPolynomial σ ℂ)
    (Algebra.IsPushout.out (R := ℚ) (S := MvPolynomial σ ℚ) (R' := ℂ) (S' := MvPolynomial σ ℂ))

theorem comap_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).minimalPrimes) :
    Q.comap (MvPolynomial.map (algebraMap ℚ ℂ)) = 𝔭 := by
  have := flat_mvPolynomial_rat_complex (σ := σ)
  have hQp : Q.IsPrime := hQ.1.1
  have hle : Ideal.map (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ)) 𝔭 ≤ Q := hQ.1.2
  set q := Q.comap (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ)) with hq
  have : q.IsPrime := Ideal.comap_isPrime _ _
  have : Q.LiesOver q := ⟨rfl⟩
  have hpq : 𝔭 ≤ q := Ideal.map_le_iff_le_comap.mp hle
  obtain ⟨P, hPQ, hP, hPl⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) Q hpq
  have hPext : Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭 ≤ P := by
    rw [Ideal.map_le_iff_le_comap]
    exact hPl.over.le
  have hQP : Q ≤ P := hQ.2 ⟨hP, hPext⟩ hPQ
  have hPQe : P = Q := le_antisymm hPQ hQP
  subst hPQe
  exact hPl.over.symm

theorem height_eq_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).minimalPrimes) :
    Q.height = 𝔭.height := by
  have := flat_mvPolynomial_rat_complex (σ := σ)
  have : Q.IsPrime := hQ.1.1
  have hc := comap_of_mem_minimalPrimes_map 𝔭 Q hQ
  have : Q.LiesOver 𝔭 := ⟨hc.symm⟩
  rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔭 Q]
  have h0 : (Q.map (Ideal.Quotient.mk (𝔭.map (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ))))).height = 0 := by
    have hQ' : Q ∈ (𝔭.map (algebraMap (MvPolynomial σ ℚ) (MvPolynomial σ ℂ))).minimalPrimes := hQ
    rw [Ideal.minimalPrimes_eq_comap] at hQ'
    obtain ⟨Q', hQ'm, hQ'e⟩ := hQ'
    have : Q'.IsPrime := hQ'm.1.1
    rw [← hQ'e, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
    exact Ideal.height_eq_zero_iff.mpr hQ'm
  rw [h0, add_zero]

end GD

theorem height_add_ringKrullDim_quotient_fintype (k : Type) [Field k]
    (P : Ideal (MvPolynomial σ k)) [P.IsPrime] :
    (P.height : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ k ⧸ P) = Fintype.card σ := by
  let e : MvPolynomial σ k ≃+* MvPolynomial (Fin (Fintype.card σ)) k :=
    (MvPolynomial.renameEquiv k (Fintype.equivFin σ)).toRingEquiv
  have : (P.map e).IsPrime := Ideal.map_isPrime_of_equiv e
  have h := ReciprocityTheory.CA.height_add_ringKrullDim_quotient_mvPolynomial_field k _ (P.map e)
  rw [RingEquiv.height_map,
    ← ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv P (P.map e) e rfl)] at h
  exact h

theorem withBot_enat_cancel {h : ℕ∞} {a b : WithBot ℕ∞} {N : ℕ}
    (ha : (h : WithBot ℕ∞) + a = N) (hb : (h : WithBot ℕ∞) + b = N) : a = b := by
  induction a using WithBot.recBotCoe with
  | bot => simp at ha
  | coe a =>
    induction b using WithBot.recBotCoe with
    | bot => simp at hb
    | coe b =>
      have ha' : h + a = N := by exact_mod_cast ha
      have hb' : h + b = N := by exact_mod_cast hb
      congr 1
      induction h using ENat.recTopCoe with
      | top => simp at ha'
      | coe h => exact WithTop.add_left_cancel (ENat.coe_ne_top h) (ha'.trans hb'.symm)

theorem ringKrullDim_of_mem_minimalPrimes_map (𝔭 : Ideal (MvPolynomial σ ℚ)) [𝔭.IsPrime]
    (Q : Ideal (MvPolynomial σ ℂ))
    (hQ : Q ∈ (Ideal.map (MvPolynomial.map (algebraMap ℚ ℂ)) 𝔭).minimalPrimes) :
    ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = ringKrullDim (MvPolynomial σ ℚ ⧸ 𝔭) := by
  have : Q.IsPrime := hQ.1.1
  have h1 := height_add_ringKrullDim_quotient_fintype ℂ Q
  have h2 := height_add_ringKrullDim_quotient_fintype ℚ 𝔭
  rw [height_eq_of_mem_minimalPrimes_map 𝔭 Q hQ] at h1
  exact withBot_enat_cancel h1 h2

end ReciprocityTheory.AnForm.R.BaseChangeC
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.IntToRatA
section
namespace ReciprocityTheory.AnForm.R.IntegerToRational

open MvPolynomial

variable {σ : Type} [Fintype σ]

noncomputable def ChZero (q : Ideal (MvPolynomial σ ℤ)) : Prop := ∀ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ q → m = 0

noncomputable abbrev intS (σ : Type) : Submonoid (MvPolynomial σ ℤ) := (nonZeroDivisors ℤ).map (C (σ := σ))

attribute [local instance] MvPolynomial.algebraMvPolynomial

lemma disj_intS (P : Ideal (MvPolynomial σ ℤ)) (hP : ChZero P) :
    Disjoint ((intS σ : Submonoid _) : Set (MvPolynomial σ ℤ)) (P : Set _) := by
  rw [Set.disjoint_left]
  rintro _ ⟨m, hm, rfl⟩ hmP
  exact nonZeroDivisors.ne_zero hm (hP m hmP)

lemma map_isPrime (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] (hP : ChZero P) :
    (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) P).IsPrime := by
  have hA : algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  rw [← hA]
  exact IsLocalization.isPrime_of_isPrime_disjoint (intS σ) (MvPolynomial σ ℚ) P ‹_› (disj_intS P hP)

lemma comap_map_eq (P : Ideal (MvPolynomial σ ℤ)) [P.IsPrime] (hP : ChZero P) :
    (Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) P).comap
      (MvPolynomial.map (Int.castRingHom ℚ)) = P := by
  have hA : algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  rw [← hA]
  exact IsLocalization.under_map_of_isPrime_disjoint (intS σ) (MvPolynomial σ ℚ) ‹_› (disj_intS P hP)

lemma chZero_comap (Q : Ideal (MvPolynomial σ ℚ)) [Q.IsPrime] :
    ChZero (Q.comap (MvPolynomial.map (Int.castRingHom ℚ))) := by
  intro m hm
  rw [Ideal.mem_comap, MvPolynomial.map_C] at hm
  by_contra h
  have hu : IsUnit (C (Int.castRingHom ℚ m) : MvPolynomial σ ℚ) :=
    (isUnit_iff_ne_zero.mpr (by simpa using h)).map C
  exact (‹Q.IsPrime›).ne_top (Ideal.eq_top_of_isUnit_mem Q hm hu)

lemma comap_strictMono :
    StrictMono (fun Q : Ideal (MvPolynomial σ ℚ) => Q.comap (MvPolynomial.map (Int.castRingHom ℚ))) := by
  have hA : algebraMap (MvPolynomial σ ℤ) (MvPolynomial σ ℚ) = MvPolynomial.map (Int.castRingHom ℚ) := by
    rw [MvPolynomial.algebraMap_def, algebraMap_int_eq]
  rw [← hA]
  exact (IsLocalization.orderEmbedding (intS σ) (MvPolynomial σ ℚ)).strictMono

theorem isJacobsonRing_int : IsJacobsonRing ℤ := by
  rw [isJacobsonRing_iff_prime_eq]
  intro P hP
  by_cases h : P = ⊥
  · subst h
    refine le_antisymm (fun x hx => ?_) Ideal.le_jacobson
    rw [Ideal.mem_jacobson_bot] at hx
    rw [Ideal.mem_bot]
    rcases Int.isUnit_iff.mp (hx x) with hu | hu
    · exact mul_self_eq_zero.mp (by linarith)
    · nlinarith [mul_self_nonneg x]
  · have := hP
    have : P.IsMaximal := IsPrime.to_maximal_ideal h
    exact Ideal.jacobson_eq_self_of_isMaximal

lemma ringKrullDim_quotient_eq_coheight {A : Type*} [CommRing A] (I : Ideal A) [hI : I.IsPrime] :
    ringKrullDim (A ⧸ I) = (Order.coheight (⟨I, hI⟩ : PrimeSpectrum A) : WithBot ℕ∞) := by
  rw [Order.coheight_eq_krullDim_Ici]
  unfold ringKrullDim
  rw [Order.krullDim_eq_of_orderIso (Ideal.primeSpectrumQuotientOrderIsoZeroLocus I)]
  exact Order.krullDim_eq_of_orderIso (OrderIso.setCongr _ _ (Set.ext fun p => Iff.rfl))

lemma eq_zero_of_aeval_mem {ι : Type*} (q : Ideal (MvPolynomial σ ℤ)) [q.IsPrime] (hq : ChZero q)
    (p : ℕ) (hp : 1 < p) (x : ι → MvPolynomial σ ℤ)
    (hred : ∀ G : MvPolynomial ι ℤ, aeval x G ∈ q → map (Int.castRingHom (ZMod p)) G = 0)
    (G : MvPolynomial ι ℤ) (hG : aeval x G ∈ q) : G = 0 := by
  have : NeZero p := ⟨by omega⟩
  have hp0 : (C (p : ℤ) : MvPolynomial σ ℤ) ∉ q := fun h => by
    have := hq _ h
    omega
  have key : ∀ k : ℕ, ∀ G : MvPolynomial ι ℤ, aeval x G ∈ q → ∀ s, ((p : ℤ) ^ k) ∣ G.coeff s := by
    intro k
    induction k with
    | zero => intros; simp
    | succ k ih =>
      intro G hG s
      have hdiv : C (p : ℤ) ∣ G := by
        rw [MvPolynomial.C_dvd_iff_dvd_coeff]
        intro i
        have h0 := congrArg (MvPolynomial.coeff i) (hred G hG)
        rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, eq_intCast,
          ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
        exact h0
      obtain ⟨H, rfl⟩ := hdiv
      have hH : aeval x H ∈ q := by
        rw [map_mul, MvPolynomial.aeval_C] at hG
        exact (‹q.IsPrime›.mem_or_mem hG).resolve_left (by simpa using hp0)
      rw [MvPolynomial.coeff_C_mul, pow_succ']
      exact mul_dvd_mul_left _ (ih H hH s)
  ext s
  rw [MvPolynomial.coeff_zero]
  by_contra hne
  have hd := key (G.coeff s).natAbs G hG s
  have h1 := Int.natAbs_dvd_natAbs.mpr hd
  rw [Int.natAbs_pow, Int.natAbs_natCast] at h1
  have h2 := Nat.le_of_dvd (Int.natAbs_pos.mpr hne) h1
  have h3 : (G.coeff s).natAbs < p ^ (G.coeff s).natAbs := Nat.lt_pow_self hp
  omega

lemma dim_le_of_charP (q q' : Ideal (MvPolynomial σ ℤ)) [q.IsPrime] [q'.IsPrime] (hle : q ≤ q')
    (hq : ChZero q) (hq' : ¬ ChZero q') :
    ringKrullDim (MvPolynomial σ ℤ ⧸ q') ≤
      ringKrullDim (MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q) := by
  classical
  obtain ⟨m, hmq', hm0⟩ : ∃ m : ℤ, (C m : MvPolynomial σ ℤ) ∈ q' ∧ m ≠ 0 := by
    by_contra h
    exact hq' fun m hm => by_contra fun hne => h ⟨m, hm, hne⟩

  have hgen := Ideal.span_singleton_generator (q'.comap (C : ℤ →+* MvPolynomial σ ℤ))
  obtain ⟨g, hg⟩ : ∃ g : ℤ, Ideal.span {g} = q'.comap (C : ℤ →+* MvPolynomial σ ℤ) := ⟨_, hgen⟩
  have hspan : Ideal.span {((g.natAbs : ℕ) : ℤ)} = q'.comap (C : ℤ →+* MvPolynomial σ ℤ) := by
    rw [Int.span_natAbs, hg]
  have hmemC : ∀ n : ℤ, (C n : MvPolynomial σ ℤ) ∈ q' ↔ ((g.natAbs : ℕ) : ℤ) ∣ n := by
    intro n
    rw [← Ideal.mem_span_singleton, hspan]
    rfl
  have hp0 : ((g.natAbs : ℕ) : ℤ) ≠ 0 := by
    intro h
    have := (hmemC m).mp hmq'
    rw [h, zero_dvd_iff] at this
    exact hm0 this
  have hpP : Nat.Prime g.natAbs := by
    have hpr : (Ideal.span {((g.natAbs : ℕ) : ℤ)}).IsPrime := by
      rw [hspan]
      infer_instance
    have := (Ideal.span_singleton_prime hp0).mp hpr
    rw [Int.prime_iff_natAbs_prime, Int.natAbs_natCast] at this
    exact this
  set p := g.natAbs with hpdef
  have : Fact p.Prime := ⟨hpP⟩

  have : CharP (MvPolynomial σ ℤ ⧸ q') p := ⟨fun n => by
    rw [← map_natCast (Ideal.Quotient.mk q'), Ideal.Quotient.eq_zero_iff_mem,
      ← map_natCast (C : ℤ →+* MvPolynomial σ ℤ), hmemC, Int.natCast_dvd_natCast]⟩
  let : Algebra (ZMod p) (MvPolynomial σ ℤ ⧸ q') := ZMod.algebra _ p
  have : Algebra.FiniteType ℤ (MvPolynomial σ ℤ ⧸ q') :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ q') (Ideal.Quotient.mkₐ_surjective ℤ q')
  have : Algebra.FiniteType (ZMod p) (MvPolynomial σ ℤ ⧸ q') :=
    Algebra.FiniteType.of_restrictScalars_finiteType ℤ (ZMod p) _
  obtain ⟨d, hdB, htrB⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ZMod p) (A := MvPolynomial σ ℤ ⧸ q')
  have : FaithfulSMul (ZMod p) (MvPolynomial σ ℤ ⧸ q') :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (RingHom.injective _)
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis (ZMod p) (MvPolynomial σ ℤ ⧸ q')

  let x : s → MvPolynomial σ ℤ := fun i => (Ideal.Quotient.mk_surjective (i : MvPolynomial σ ℤ ⧸ q')).choose
  have hx : ∀ i, Ideal.Quotient.mk q' (x i) = i := fun i =>
    (Ideal.Quotient.mk_surjective (i : MvPolynomial σ ℤ ⧸ q')).choose_spec
  have hred : ∀ G : MvPolynomial s ℤ, aeval x G ∈ q → map (Int.castRingHom (ZMod p)) G = 0 := by
    intro G hG
    apply hs.1.eq_zero_of_aeval_eq_zero
    rw [← algebraMap_int_eq, MvPolynomial.aeval_map_algebraMap,
      show ((↑) : s → MvPolynomial σ ℤ ⧸ q') = fun i => Ideal.Quotient.mkₐ ℤ q' (x i) from
        funext fun i => (hx i).symm,
      ← MvPolynomial.comp_aeval_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact hle hG
  have hinj := eq_zero_of_aeval_mem q hq p hpP.one_lt x hred

  have := map_isPrime q hq
  have : Algebra.FiniteType ℚ (MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℚ _) (Ideal.Quotient.mkₐ_surjective ℚ _)
  obtain ⟨e, hdC, htrC⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := ℚ)
    (A := MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q)
  let φ : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q :=
    ((Ideal.Quotient.mk _).comp (MvPolynomial.map (Int.castRingHom ℚ))).toIntAlgHom
  let y : s → MvPolynomial σ ℚ ⧸ Ideal.map (MvPolynomial.map (Int.castRingHom ℚ)) q := fun i => φ (x i)
  have hy : AlgebraicIndependent ℚ y := by
    rw [algebraicIndependent_iff]
    intro H hH
    obtain ⟨⟨G, c⟩, hGH⟩ := IsLocalization.surj ((nonZeroDivisors ℤ).map (C (σ := s))) H
    obtain ⟨n, hn, hnc⟩ := Submonoid.mem_map.mp c.2
    have hG0 : G = 0 := by
      apply hinj G
      have h1 := congrArg (MvPolynomial.aeval y) hGH
      rw [map_mul, hH, zero_mul, MvPolynomial.algebraMap_def, MvPolynomial.aeval_map_algebraMap,
        ← MvPolynomial.comp_aeval_apply] at h1
      have h2 : Ideal.Quotient.mk _ (MvPolynomial.map (Int.castRingHom ℚ) (aeval x G)) = 0 := h1.symm
      rw [Ideal.Quotient.eq_zero_iff_mem] at h2
      rw [← comap_map_eq q hq]
      exact h2
    rw [hG0, map_zero] at hGH
    have hc0 : algebraMap (MvPolynomial s ℤ) (MvPolynomial s ℚ) (c : MvPolynomial s ℤ) ≠ 0 := by
      rw [← hnc, MvPolynomial.algebraMap_def, MvPolynomial.map_C, Ne, MvPolynomial.C_eq_zero]
      simpa using nonZeroDivisors.ne_zero hn
    exact (mul_eq_zero.mp hGH).resolve_right hc0
  have hle' := hy.cardinalMk_le_trdeg
  rw [hs.cardinalMk_eq_trdeg, htrB, htrC] at hle'
  have hde : d ≤ e := by exact_mod_cast hle'
  rw [hdB, hdC]
  exact_mod_cast hde

end ReciprocityTheory.AnForm.R.IntegerToRational
end

-- bundled from ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartC
section
namespace ReciprocityTheory.AnForm.R.JacobianCriterionAlt

open MvPolynomial IsLocalRing

noncomputable section

variable {n : ℕ}

theorem isRegularLocalRing_of_jacobian' (K : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin n → ℂ)
    (hp : ∀ h ∈ K, eval p h = 0) {c : ℕ} (F : Fin c → MvPolynomial (Fin n) ℂ) (hF : ∀ i, F i ∈ K)
    (hlin : LinearIndependent ℂ (fun i => gradP p (F i)))
    (hq : ∃ 𝔮 ∈ K.minimalPrimes, 𝔮 ≤ ptI p ∧ 𝔮.height ≤ c) :
    IsRegularLocalRing (locR K p) ∧ ringKrullDim (locR K p) = ((n - c : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hloc, hnoeth⟩ := locRing_isLocalRing_isNoetherian' K p hp
  have hcot := finrank_cot_eq p K
  have hrank : c ≤ Module.finrank ℂ (jacS K p) := by
    let v : Fin c → jacS K p := fun i => ⟨gradP p (F i), Submodule.subset_span ⟨F i, hF i, rfl⟩⟩
    have hv : LinearIndependent ℂ v := LinearIndependent.of_comp (jacS K p).subtype hlin
    simpa using hv.fintype_card_le_finrank
  have hcotle : Module.finrank (ResidueField (locR K p)) (CotangentSpace (locR K p)) ≤ n - c := by
    omega
  have hdimle : ringKrullDim (locR K p) ≤ ((n - c : ℕ) : WithBot ℕ∞) := by
    refine (ringKrullDim_le_spanFinrank_maximalIdeal _).trans ?_
    rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
    exact_mod_cast hcotle
  obtain ⟨𝔮, h𝔮min, h𝔮P, h𝔮c⟩ := hq
  have h𝔮prime : 𝔮.IsPrime := h𝔮min.1.1
  have hK𝔮 : K ≤ 𝔮 := h𝔮min.1.2
  set Pb : Ideal (MvPolynomial (Fin n) ℂ ⧸ 𝔮) := (ptI p).map (Ideal.Quotient.mk 𝔮) with hPb
  have hker : RingHom.ker (Ideal.Quotient.mk 𝔮) ≤ ptI p := by rw [Ideal.mk_ker]; exact h𝔮P
  have hPbprime : Pb.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hPmax : (ptI p).IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C _⟩)
  have hPbmax : Pb.IsMaximal :=
    (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective hPmax).resolve_left
      hPbprime.ne_top
  have hheight := ReciprocityTheory.CA.height_add_height_maximal_quotient_field ℂ n 𝔮 Pb
  have hmemPb : ∀ s, Ideal.Quotient.mk 𝔮 s ∈ Pb ↔ s ∈ ptI p := by
    intro s; rw [hPb, Ideal.mem_quotient_iff_mem_sup, sup_eq_left.mpr h𝔮P]
  let gq : MvPolynomial (Fin n) ℂ →+* Localization.AtPrime Pb :=
    (algebraMap _ (Localization.AtPrime Pb)).comp (Ideal.Quotient.mk 𝔮)
  have hunits : ∀ y : (ptI p).primeCompl, IsUnit (gq y) := fun y =>
    IsLocalization.map_units (Localization.AtPrime Pb)
      (⟨Ideal.Quotient.mk 𝔮 y, fun h => y.2 ((hmemPb y).mp h)⟩ : Pb.primeCompl)
  let φ : localization₂ p →+* Localization.AtPrime Pb :=
    IsLocalization.lift (M := (ptI p).primeCompl) hunits
  have hφ : Function.Surjective φ := by
    intro t
    obtain ⟨⟨x, y⟩, rfl⟩ := IsLocalization.mk'_surjective Pb.primeCompl t
    obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y', hy'⟩ := Ideal.Quotient.mk_surjective (y : MvPolynomial (Fin n) ℂ ⧸ 𝔮)
    have hy'P : y' ∉ ptI p := fun h => y.2 (hy' ▸ (hmemPb y').mpr h)
    refine ⟨IsLocalization.mk' (localization₂ p) x' (⟨y', hy'P⟩ : (ptI p).primeCompl), ?_⟩
    rw [IsLocalization.lift_mk'_spec]
    simp only [gq, RingHom.coe_comp, Function.comp_apply, hy']
    rw [IsLocalization.mk'_spec']
  have hφK : ∀ a ∈ Ideal.map (algebraMap _ (localization₂ p)) K, φ a = 0 := by
    intro a ha
    have : Ideal.map (algebraMap _ (localization₂ p)) K ≤ RingHom.ker φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, RingHom.mem_ker]
      simp only [φ, IsLocalization.lift_eq, gq, RingHom.coe_comp, Function.comp_apply,
        Ideal.Quotient.eq_zero_iff_mem.mpr (hK𝔮 hk), map_zero]
    exact this ha
  have hφB : Function.Surjective (Ideal.Quotient.lift _ φ hφK) :=
    Ideal.Quotient.lift_surjective_of_surjective _ _ hφ
  have hle := ringKrullDim_le_of_surjective _ hφB
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height Pb (Localization.AtPrime Pb)] at hle
  have hqfin : 𝔮.height ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top c) h𝔮c
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hqfin
  have hPbfin : Pb.height ≠ ⊤ := by
    intro h; rw [h, add_top] at hheight; exact ENat.top_ne_natCast n hheight
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hPbfin
  have hkm : k + m = n := by rw [← hk, ← hm] at hheight; exact_mod_cast hheight
  have hkc : k ≤ c := by rw [← hk] at h𝔮c; exact_mod_cast h𝔮c
  rw [← hm] at hle
  have hdimge : ((n - c : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (locR K p) := by
    refine le_trans ?_ hle
    show (((n - c : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ((m : ℕ∞) : WithBot ℕ∞)
    exact WithBot.coe_le_coe.mpr (Nat.cast_le.mpr (by omega))
  have hdim := le_antisymm hdimle hdimge
  refine ⟨?_, hdim⟩
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace, hdim]
  exact_mod_cast hcotle

end

end ReciprocityTheory.AnForm.R.JacobianCriterionAlt
end

