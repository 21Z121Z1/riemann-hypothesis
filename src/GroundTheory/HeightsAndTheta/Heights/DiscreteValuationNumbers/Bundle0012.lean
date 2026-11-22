import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PEffectiveShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem EffectiveShift.proof : EffectiveShift.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P e hP b f g hD
  classical
  have hPr : P.IsPrime := hP.multiProj.isPrime
  have hCP : (C ϖ : MRing ι O) ∉ P := by
    intro h
    have h' : ϖ ∈ P.comap (C : O →+* MRing ι O) := h
    rw [hP.noTorsion, Ideal.mem_bot] at h'
    exact hϖ.ne_zero h'

  let J : Ideal (MRing ι O) :=
    { carrier := {u | ∃ v, u * f - v * g ∈ P}
      add_mem' := by
        rintro a c ⟨v, hv⟩ ⟨w, hw⟩
        exact ⟨v + w, by convert P.add_mem hv hw using 1; ring⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨v, hv⟩
        exact ⟨c * v, by convert P.mul_mem_left c hv using 1; simp only [smul_eq_mul]; ring⟩ }
  have hJ : ∀ u, u ∈ J ↔ ∃ v, u * f - v * g ∈ P := fun u => Iff.rfl
  have hPJ : P ≤ J := fun p hp => (hJ p).2 ⟨0, by simpa using P.mul_mem_right f hp⟩

  let 𝔞 : Ideal (MRing ι O) :=
    ∏ k : K, Ideal.span (Set.range fun i : ι k => (X ⟨k, i⟩ : MRing ι O))
  let I : Ideal (MRing ι O) := Ideal.span {(C ϖ : MRing ι O)} * 𝔞
  have hIJ : I ≤ J.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun W hW => ?_
    obtain ⟨hJW, hWp⟩ := hW
    by_cases hϖW : (C ϖ : MRing ι O) ∈ W
    · exact Ideal.mul_le_left.trans ((Ideal.span_singleton_le_iff_mem W).2 hϖW)
    · have hrel : ¬ IsRelevant W := by
        intro hrel
        obtain ⟨u, v, hu, -, huv⟩ := hD.unit_off_special W hWp (hPJ.trans hJW) hrel hϖW
        exact hu (hJW ((hJ u).2 ⟨v, huv⟩))
      simp only [IsRelevant, not_forall, not_exists, not_not] at hrel
      obtain ⟨k, hk⟩ := hrel
      refine Ideal.mul_le_right.trans
        (Ideal.prod_le_inf.trans ((Finset.inf_le (Finset.mem_univ k)).trans ?_))
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      exact hk i
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hIJ (IsNoetherian.noetherian I)
  have hCN : (C ϖ : MRing ι O) ^ N ∉ P := fun h => hCP (hPr.mem_of_pow_mem N h)
  refine ⟨N, ?_, ?_⟩
  · obtain ⟨bf, bg, hf, hg, hb⟩ := hD.degrees
    refine IsVerticalDivisor.of_unit_off_special ⟨bf, bg, ?_, hg, hb⟩ ?_ hD.den_not_mem ?_
    · have h := (isWeightedHomogeneous_C (blockWeight ι) (ϖ ^ N)).mul hf
      rw [zero_add, map_pow] at h
      exact h
    · exact fun h => (hPr.mem_or_mem h).elim hCN hD.num_not_mem
    · intro W hW hPW hrel hϖW
      obtain ⟨u, v, hu, hv, huv⟩ := hD.unit_off_special W hW hPW hrel hϖW
      refine ⟨u, C ϖ ^ N * v, hu, ?_, ?_⟩
      · exact fun h => (hW.mem_or_mem h).elim (fun h' => hϖW (hW.mem_of_pow_mem N h')) hv
      · convert P.mul_mem_left (C ϖ ^ N) huv using 1; ring
  · intro W hW hPW hrel
    choose i hi using hrel
    have hz : (∏ k, (X ⟨k, i k⟩ : MRing ι O)) ∉ W := by
      rw [hW.prod_mem_iff]
      rintro ⟨k, -, hk⟩
      exact hi k hk
    have hz𝔞 : (∏ k, (X ⟨k, i k⟩ : MRing ι O)) ∈ 𝔞 :=
      Ideal.prod_mem_prod fun k _ => Ideal.subset_span ⟨i k, rfl⟩
    have hmem : (C ϖ * ∏ k, (X ⟨k, i k⟩ : MRing ι O)) ^ N ∈ J :=
      hN (Ideal.pow_mem_pow (Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hz𝔞) N)
    obtain ⟨v, hv⟩ := (hJ _).1 hmem
    refine ⟨(∏ k, (X ⟨k, i k⟩ : MRing ι O)) ^ N, v, fun h => hz (hW.mem_of_pow_mem N h), ?_⟩
    convert hv using 1
    ring

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PFibreVarieties
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

private theorem withBot_eq_of_add_one_eq (a : WithBot ℕ∞) (m : ℕ)
    (h : a + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) : a = (m : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot =>
    exfalso
    have e : ((m : WithBot ℕ∞) + 1) = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by push_cast; rfl
    rw [Nat.cast_add, Nat.cast_one, e] at h
    exact WithBot.bot_ne_coe h
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      simp at h
      have e : ((m : ℕ∞) : WithBot ℕ∞) = (m : WithBot ℕ∞) := rfl
      rw [← e] at h
      exact ENat.top_ne_natCast m (WithBot.coe_injective h)
    | coe a =>
      have h' : ((a + 1 : ℕ) : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← h]; push_cast; rfl
      have : a + 1 = m + 1 := by exact_mod_cast h'
      have ham : a = m := by omega
      subst ham
      rfl

theorem FibreVarieties.proof
    (hGen : GenericFibProps.Statement.{u}) (hBound : GenericDimBound.Statement.{u})
    (hGe : GenericDimGe.Statement.{u}) (hCorr : SpecialIdealCorresp.Statement.{u})
    (hSpecHomog : SpecialIdealMultiHomog.Statement.{u}) (hSup : SupSpanMultiHomog.Statement.{u})
    (hMin : MinimalPrimeMultiHomog.Statement.{u}) (hQuot : SpecialQuotDim.Statement.{u})
    (hComp : ComponentDim.Statement.{u}) : FibreVarieties.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP
  obtain ⟨hprime, hhomog, hforms⟩ := hGen O K ι P hP.multiProj hP.noTorsion
  have hcast : ((d + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) =
      ((d + Fintype.card K + 1 : ℕ) : WithBot ℕ∞) := by
    congr 1; omega
  refine ⟨⟨⟨hprime, hhomog, ?_⟩, ?_⟩, ?_⟩
  ·
    intro k
    obtain ⟨i, hi⟩ := hP.multiProj.relevant k
    obtain ⟨-, h⟩ := hforms _ _ (isWeightedHomogeneous_X O (blockWeight ι) ⟨k, i⟩) hi
    exact ⟨i, by simpa [MvPolynomial.map_X] using h⟩
  ·
    have h1 := hBound O K ι P hP.multiProj hP.noTorsion
    have h2 := hGe O K ι P hP.multiProj.isPrime hP.noTorsion
    rw [hP.dim, hcast] at h1 h2
    exact withBot_eq_of_add_one_eq _ _ (le_antisymm h1 h2)
  ·
    intro W hW
    have hW0 := hW
    unfold divCycle at hW
    split_ifs at hW with h
    · obtain ⟨hWmin, hWrel⟩ := h
      have hWp : W.IsPrime := hWmin.1.1
      have hϖW : (C ϖ : MRing ι O) ∈ W := hWmin.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))
      obtain ⟨hsp, -, hrel, -⟩ := hCorr O ϖ hϖ K ι P W hWp hϖW
      have hJ : IsMultiHomogIdeal (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
        hSup O K ι P (C ϖ) 0 hP.multiProj.multiHomog (isWeightedHomogeneous_C _ _)
      have hWh : IsMultiHomogIdeal W := hMin O K ι _ W hJ hWmin
      have hϖP : (C ϖ : MRing ι O) ∉ P := by
        intro hmem
        have : ϖ ∈ P.comap (C : O →+* MRing ι O) := hmem
        rw [hP.noTorsion, Ideal.mem_bot] at this
        exact hϖ.ne_zero this
      refine ⟨⟨hsp, hSpecHomog O K ι W hWh, hrel.mp hWrel⟩, ?_⟩
      rw [hQuot O ϖ hϖ K ι W hϖW]
      exact hComp O ϖ hϖ K ι P d hP 0 (C ϖ) (isWeightedHomogeneous_C _ _) hϖP W hW0 hϖW
    · exact absurd rfl hW

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericDimBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GenericDimBound.proof (hmax : MaximalIdealHeightFG.Statement.{u}) :
    GenericDimBound.Statement.{u} := by
  intro O _ _ _ K _ _ ι _ P hP hT
  classical
  let KO := FractionRing O
  let S := MRing ι O
  let MainNotions := MRing ι KO
  let φ : S →+* MainNotions := algebraMap S MainNotions
  let M : Submonoid S := (nonZeroDivisors O).map (C : O →+* S)
  have : IsLocalization M MainNotions := MvPolynomial.isLocalization (nonZeroDivisors O) KO

  have hPker : ∀ f ∈ P, constantCoeff f = 0 := by
    intro f hf
    have h0 := hP.multiHomog f hf 0
    rw [weightedHomogeneousComponent_zero] at h0
    · have : coeff 0 f ∈ P.comap (C : O →+* S) := h0
      rw [hT, Ideal.mem_bot] at this
      rw [constantCoeff_eq]
      exact this
    · intro v h
      have := congrFun h v.1
      simp [blockWeight] at this

  have hdisj : Disjoint (M : Set S) (P : Set S) := by
    rw [Set.disjoint_left]
    rintro _ ⟨a, ha, rfl⟩ hmem
    have : a ∈ P.comap (C : O →+* S) := hmem
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero ha this
  have hPK : (genFib P).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint M MainNotions P hP.isPrime hdisj

  let N : Ideal MainNotions := RingHom.ker (constantCoeff : MainNotions →+* KO)
  have hNmax : N.IsMaximal :=
    RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, constantCoeff_C _ _⟩
  have hPN : genFib P ≤ N := by
    rw [genFib, Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, RingHom.mem_ker, constantCoeff_map, hPker f hf, map_zero]
  let A := MainNotions ⧸ genFib P
  let mk : MainNotions →+* A := Ideal.Quotient.mk (genFib P)
  have hmk : Function.Surjective mk := Ideal.Quotient.mk_surjective
  have hcomapN : (N.map mk).comap mk = N := by
    rw [Ideal.comap_map_of_surjective' _ hmk, Ideal.mk_ker, sup_eq_left.mpr hPN]
  let m : Ideal A := N.map mk
  have hm : m.IsMaximal := by
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective mk hmk hNmax with h | h
    · exfalso
      have : N = ⊤ := by rw [← hcomapN, h, Ideal.comap_top]
      exact hNmax.ne_top this
    · exact h
  have : Algebra.FiniteType KO A :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ KO (genFib P))
      (Ideal.Quotient.mkₐ_surjective KO _)
  have hht : (m.height : WithBot ℕ∞) = ringKrullDim A := hmax KO A m hm

  let g : PrimeSpectrum A → PrimeSpectrum.zeroLocus (R := S) (P : Set S) := fun x =>
    ⟨⟨(x.asIdeal.comap mk).comap φ, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show mk (φ f) ∈ x.asIdeal
      have h0 : mk (φ f) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem φ hf : φ f ∈ genFib P)
      rw [h0]
      exact x.asIdeal.zero_mem⟩
  have hg : StrictMono g := by
    intro x y hxy
    have h1 : x.asIdeal.comap mk < y.asIdeal.comap mk :=
      lt_of_le_of_ne (Ideal.comap_mono hxy.le) fun h =>
        hxy.ne (PrimeSpectrum.ext (Ideal.comap_injective_of_surjective mk hmk h))
    exact (IsLocalization.orderEmbedding M MainNotions).strictMono h1

  have hlastN : ∀ f : S, f ∈ (m.comap mk).comap φ ↔ constantCoeff f = 0 := by
    intro f
    rw [hcomapN, Ideal.mem_comap, RingHom.mem_ker]
    show constantCoeff (MvPolynomial.map (algebraMap O KO) f) = 0 ↔ _
    rw [constantCoeff_map]
    exact ⟨fun h => IsFractionRing.injective O KO (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩

  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  let M1 : Ideal S := (IsLocalRing.maximalIdeal O).comap (constantCoeff : S →+* O)
  let top : PrimeSpectrum.zeroLocus (R := S) (P : Set S) :=
    ⟨⟨M1, inferInstance⟩, by
      rw [PrimeSpectrum.mem_zeroLocus]
      intro f hf
      show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [hPker f hf]
      exact Ideal.zero_mem _⟩
  have htop : g ⟨m, hm.isPrime⟩ < top := by
    show (m.comap mk).comap φ < M1
    refine lt_of_le_of_ne (fun f hf => ?_) fun h => ?_
    · show constantCoeff f ∈ IsLocalRing.maximalIdeal O
      rw [(hlastN f).mp hf]
      exact Ideal.zero_mem _
    · have hC : (C ϖ : S) ∈ M1 := by
        show constantCoeff (C ϖ : S) ∈ IsLocalRing.maximalIdeal O
        rw [constantCoeff_C]
        exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
      rw [← h, hlastN, constantCoeff_C] at hC
      exact hϖ.ne_zero hC

  have key : ∀ n : ℕ, (n : ℕ∞) ≤ m.height →
      ((n + 1 : ℕ) : WithBot ℕ∞) ≤ Order.krullDim (PrimeSpectrum.zeroLocus (R := S) (P : Set S)) := by
    intro n hn
    rw [show m.height = Order.height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) from
      PrimeSpectrum.height_eq_orderHeight ⟨m, hm.isPrime⟩] at hn
    obtain ⟨p, hplast, hplen⟩ :=
      Order.exists_series_of_le_height (⟨m, hm.isPrime⟩ : PrimeSpectrum A) hn
    have hlt : (p.map g hg).last < top := by
      rw [LTSeries.last_map, hplast]
      exact htop
    have := Order.LTSeries.length_le_krullDim ((p.map g hg).snoc top hlt)
    simpa [hplen] using this

  rw [← hht, ringKrullDim_quotient P]
  have h1 := key 0 (by simp)
  have hne : Order.krullDim (PrimeSpectrum.zeroLocus (R := S) (P : Set S)) ≠ ⊥ := fun h => by
    rw [h] at h1; simp at h1
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp hne
  rw [← hd] at key ⊢
  rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
  refine ENat.forall_natCast_le_iff_le.mp fun a ha => ?_
  rcases a with _ | k
  · simp
  · have hk : (k : ℕ∞) ≤ m.height := by
      have : (k : ℕ∞) + 1 ≤ m.height + 1 := by exact_mod_cast ha
      exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
    have := key k hk
    exact_mod_cast this

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PGenericFibProps
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem weightedHomogeneousComponent_map {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (φ : R →+* S) (w : σ → M) (n : M) (p : MvPolynomial σ R) :
    weightedHomogeneousComponent w n (MvPolynomial.map φ p) =
      MvPolynomial.map φ (weightedHomogeneousComponent w n p) := by
  classical
  ext d
  rw [coeff_weightedHomogeneousComponent, coeff_map, coeff_map,
    coeff_weightedHomogeneousComponent]
  split_ifs <;> simp

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem GenericFibProps.proof : GenericFibProps.Statement := by
  intro O _ _ _ K _ _ ι _ P hP hT
  set φ := algebraMap O (FractionRing O) with hφ
  let M : Submonoid (MRing ι O) := (nonZeroDivisors O).map (C (σ := Σ k, ι k))
  have : IsLocalization M (MRing ι (FractionRing O)) :=
    MvPolynomial.isLocalization (nonZeroDivisors O) (FractionRing O)
  have hmap : algebraMap (MRing ι O) (MRing ι (FractionRing O)) = MvPolynomial.map φ := rfl
  have hdisj : Disjoint (M : Set (MRing ι O)) P := by
    rw [Set.disjoint_left]
    rintro _ ⟨m, hm, rfl⟩ hmP
    have : m ∈ P.comap (C : O →+* MRing ι O) := hmP
    rw [hT, Ideal.mem_bot] at this
    exact nonZeroDivisors.ne_zero hm this
  have hgen : genFib P = Ideal.map (algebraMap (MRing ι O) (MRing ι (FractionRing O))) P := rfl
  have hprime : (genFib P).IsPrime :=
    hgen ▸ IsLocalization.isPrime_of_isPrime_disjoint M _ P hP.isPrime hdisj
  have hunder : (genFib P).comap (MvPolynomial.map φ) = P :=
    IsLocalization.under_map_of_isPrime_disjoint M (MRing ι (FractionRing O)) hP.isPrime hdisj
  refine ⟨hprime, ?_, ?_⟩
  · intro x hx b
    rw [hgen, IsLocalization.mem_map_algebraMap_iff M] at hx
    obtain ⟨⟨⟨p, hp⟩, ⟨_, ⟨m, hm, rfl⟩⟩⟩, h⟩ := hx
    simp only [hmap, map_C] at h
    have hm0 : φ m ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hm
    have hx' : x = C (φ m)⁻¹ * MvPolynomial.map φ p := by
      rw [← h, mul_comm x, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hm0, C_1, one_mul]
    rw [hx', weightedHomogeneousComponent_C_mul, weightedHomogeneousComponent_map]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ (hP.multiHomog p hp b))
  · intro s c hs hsP
    refine ⟨?_, ?_⟩
    · intro d hd
      apply hs
      intro h0
      rw [coeff_map, h0, map_zero] at hd
      exact hd rfl
    · intro h
      apply hsP
      rw [← hunder]
      exact h

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PIntNumAddFirstField
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial GroundTheory.Heights₂.Heights.FieldNumbers

universe u

private lemma mixedDiff_eventually_zero {K : Type*} (h : (K → ℤ) → ℤ)
    (hh : ∀ᶠ m in Filter.atTop, h m = 0) {n : ℕ} (bs : Fin n → K → ℤ) :
    ∀ᶠ m in Filter.atTop, mixedDiff bs h m = 0 := by
  unfold mixedDiff
  induction (List.ofFn bs) with
  | nil => simpa using hh
  | cons b l ih =>
    have hs : Filter.Tendsto (fun m : K → ℤ => m - b) Filter.atTop Filter.atTop := by
      simpa [sub_eq_add_neg] using
        Filter.tendsto_atTop_add_const_right Filter.atTop (-b) Filter.tendsto_id
    filter_upwards [ih, hs.eventually ih] with m h1 h2
    simp [List.foldr, diffStep, h1, h2]

private lemma eventualValue_of_eventually_zero {K : Type*} (f : (K → ℤ) → ℤ)
    (hf : ∀ᶠ m in Filter.atTop, f m = 0) : eventualValue f = 0 := by
  classical
  have hex : ∃ c, ∀ᶠ m in Filter.atTop, f m = c := ⟨0, hf⟩
  rw [eventualValue, dif_pos hex]
  obtain ⟨m, h1, h2⟩ := (hex.choose_spec.and hf).exists
  rw [← h1, h2]

theorem IntNumAddFirst.proof (h1 : FieldNumbers.IntNumAdd.Statement.{u})
    (h2 : FieldNumbers.IntNumZeroSlot.Statement.{u})
    (h3 : FieldNumbers.HilbDegreeBound.Statement.{u}) : IntNumAddFirst.Statement.{u} := by
  intro F _ K _ _ ι _ n G hG hGh hdim b₁ b₂ L
  have hupd : ∀ b : K → ℤ,
      Matrix.vecCons b L = Function.update (Matrix.vecCons (0 : K → ℤ) L) 0 b := fun b => by
    simp [Matrix.vecCons, Fin.update_cons_zero]
  by_cases hrel : IsRelevant G
  ·
    have hle : relDim G = ((n + 1 : ℕ) : WithBot (WithTop ℤ)) ∨
        relDim G < ((n + 1 : ℕ) : WithBot (WithTop ℤ)) := by
      have hc : ((n + 1 : ℕ) : WithBot (WithTop ℤ)) = (((n + 1 : ℕ) : ℤ) : WithTop ℤ) := by
        rfl
      unfold relDim
      generalize ringKrullDim (MRing ι F ⧸ G) = x at hdim ⊢
      induction x using WithBot.recBotCoe with
      | bot => exact Or.inr (WithBot.bot_lt_coe _)
      | coe d =>
        induction d using ENat.recTopCoe with
        | top => exfalso; exact absurd hdim (by simp)
        | coe e =>
          have he : e < n + 2 + Fintype.card K := by
            rw [← WithBot.coe_natCast] at hdim
            exact_mod_cast WithBot.coe_lt_coe.1 hdim
          simp only [WithBot.map_coe]
          rw [hc]
          show ((((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) = _ ∨
            ((((e : ℤ) - Fintype.card K : ℤ) : WithTop ℤ) : WithBot (WithTop ℤ)) < _
          rcases (show (e : ℤ) - Fintype.card K ≤ ((n + 1 : ℕ) : ℤ) by omega).lt_or_eq with h | h
          · exact Or.inr (WithBot.coe_lt_coe.2 (WithTop.coe_lt_coe.2 h))
          · exact Or.inl (by rw [h])
    rcases hle with heq | hlt
    · rw [hupd (b₁ + b₂), hupd b₁, hupd b₂]
      exact h1 F K ι G hGh hrel (n + 1) heq (Matrix.vecCons 0 L) 0 b₁ b₂
    · simp only [(h2 F K ι G).2 hGh (n + 1) _ hlt, add_zero]
  · have hz := (h3 F K ι G hGh).2 hrel
    simp only [intNum, eventualValue_of_eventually_zero _ (mixedDiff_eventually_zero _ hz _),
      add_zero]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialQuotDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

theorem SpecialQuotDim.proof : SpecialQuotDim.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ W hW
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hsurj : Function.Surjective π :=
    MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π ≤ W := by
    change RingHom.ker (MvPolynomial.map (IsLocalRing.residue O)) ≤ W
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.map_span,
      Set.image_singleton, Ideal.span_le, Set.singleton_subset_iff]
    exact hW
  have hcomap : (specialIdeal W).comap π = W := by
    change (W.map π).comap π = W
    rw [Ideal.comap_map_of_surjective' _ hsurj, sup_eq_left.2 hker]
  let f := (Ideal.Quotient.mk (specialIdeal W)).comp π
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hsurj
  have hkf : RingHom.ker f = W := by
    ext x
    change Ideal.Quotient.mk _ (π x) = 0 ↔ x ∈ W
    rw [Ideal.Quotient.eq_zero_iff_mem, ← Ideal.mem_comap, hcomap]
  exact (ringKrullDim_eq_of_ringEquiv
    ((Ideal.quotEquivOfEq hkf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))).symm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

