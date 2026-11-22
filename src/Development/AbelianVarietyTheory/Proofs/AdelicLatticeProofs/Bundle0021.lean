import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0015
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCommonDenominatorNilpotentCoboundary
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory

theorem exists_denominator_of_isField_localization (B A : Type) [CommRing B] [CommRing A]
    [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] (M : Submonoid B)
    (hF : IsField (Localization M)) (f : A)
    (hf : IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) :
    ∃ m ∈ M, ∃ b' : B, algebraMap B A m * f = algebraMap B A b' := by
  letI : Field (Localization M) := hF.toField
  haveI : CharZero (Localization M) := algebraRat.charZero _
  let K := Localization M
  let A' := Localization (Algebra.algebraMapSubmonoid A M)
  haveI : IsReduced A' := inferInstance
  haveI : Algebra.FiniteType K A' := by
    haveI : IsLocalization (Submonoid.map (algebraMap B A) M) A' :=
      inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid A M) A')
    have h := RingHom.finiteType_localizationPreserves (algebraMap B A) M K A'
      (RingHom.finiteType_algebraMap.mpr inferInstance)
    exact h
  let g : A →ₐ[B] A' := IsScalarTower.toAlgHom B A A'
  let φ : A ⊗[B] A →ₐ[B] A' ⊗[K] A' :=
    Algebra.TensorProduct.lift
      (((Algebra.TensorProduct.includeLeft : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g)
      (((Algebra.TensorProduct.includeRight : A' →ₐ[K] A' ⊗[K] A').restrictScalars B).comp g)
      (fun _ _ => Commute.all _ _)
  have hn : IsNilpotent (g f ⊗ₜ[K] (1 : A') - (1 : A') ⊗ₜ[K] g f) := by
    have := hf.map φ
    simpa [φ] using this
  obtain ⟨k, hk⟩ := GlobalTheory.ClassFin.mem_range_algebraMap_of_isNilpotent_tmul_sub K A' (g f) hn
  obtain ⟨⟨β, t⟩, ht⟩ := IsLocalization.surj M k
  have h1 : algebraMap A A' (algebraMap B A t * f) = algebraMap A A' (algebraMap B A β) := by
    have := congrArg (algebraMap K A') ht
    rw [map_mul, hk, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← this,
      mul_comm]
    rfl
  obtain ⟨⟨_, u, hu, rfl⟩, hc⟩ :=
    (IsLocalization.eq_iff_exists (Algebra.algebraMapSubmonoid A M) A').1 h1
  refine ⟨u * t, M.mul_mem hu t.2, u * β, ?_⟩
  simpa [map_mul, mul_assoc] using hc

theorem exists_common_denominator_of_isNilpotent :
    ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℚ B] [Algebra B A] [Algebra.FiniteType B A] [IsReduced A] [Nontrivial B], Function.Injective (algebraMap B A) → ∀ s : Finset A, (∀ f ∈ s, IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f)) → ∃ b : B, b ≠ 0 ∧ ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
  intro B A _ _ _ _ _ _ _ hinj s hs
  classical
  haveI : IsReduced B := isReduced_of_injective (algebraMap B A) hinj
  obtain ⟨m, hm⟩ := Ideal.exists_maximal B
  obtain ⟨p, hp, -⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := m) bot_le
  haveI : p.IsPrime := hp.1.1
  haveI : Ring.KrullDimLE 0 (Localization.AtPrime p) :=
    Ring.KrullDimLE.of_isLocalization p hp _
  have hF : IsField (Localization.AtPrime p) := Ring.KrullDimLE.isField_of_isReduced
  have key : ∃ b ∈ p.primeCompl, ∀ f ∈ s, ∃ b' : B, algebraMap B A b * f = algebraMap B A b' := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, by simp⟩
    | insert a s _ ih =>
      obtain ⟨b, hb, h⟩ := ih (fun f hf => hs f (Finset.mem_insert_of_mem hf))
      obtain ⟨c, hc, c', hc'⟩ := exists_denominator_of_isField_localization B A p.primeCompl hF a
        (hs a (Finset.mem_insert_self _ _))
      refine ⟨b * c, mul_mem hb hc, fun f hf => ?_⟩
      rcases Finset.mem_insert.1 hf with rfl | hf
      · exact ⟨b * c', by rw [map_mul, map_mul, mul_assoc, hc']⟩
      · obtain ⟨b', hb'⟩ := h f hf
        exact ⟨c * b', by rw [map_mul, map_mul, ← hb']; ring⟩
  obtain ⟨b, hb, h⟩ := key
  exact ⟨b, fun h0 => hb (h0 ▸ p.zero_mem), h⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDenominatorPrimesPrescribed
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_pow_eq_span_singleton (E : Type) [Field E] [NumberField E] (a : Ideal (𝓞 E))
    (ha : a ≠ ⊥) : ∃ (h : ℕ) (s : 𝓞 E), h ≠ 0 ∧ a ^ h = Ideal.span {s} := by
  have ha0 : a ∈ nonZeroDivisors (Ideal (𝓞 E)) := mem_nonZeroDivisors_of_ne_zero ha
  have hone : ClassGroup.mk0 ⟨a, ha0⟩ ^ Fintype.card (ClassGroup (𝓞 E)) = 1 := pow_card_eq_one
  rw [← map_pow, SubmonoidClass.mk_pow] at hone
  have hprin : (a ^ Fintype.card (ClassGroup (𝓞 E))).IsPrincipal :=
    (ClassGroup.mk0_eq_one_iff _).mp hone
  exact ⟨Fintype.card (ClassGroup (𝓞 E)), Submodule.IsPrincipal.generator _, Fintype.card_ne_zero,
    (Ideal.span_singleton_generator _).symm⟩

theorem exists_denominator_primes_prescribed :
    ∀ (E : Type) [Field E] [NumberField E] (Q : Ideal (𝓞 E) → Prop) (ι : Type) [Finite ι]
      (x : ι → E),
      (∀ i, ∀ P : HeightOneSpectrum (𝓞 E), ¬ Q P.asIdeal → P.valuation E (x i) ≤ 1) →
      ∃ s : 𝓞 E, s ≠ 0 ∧ (∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → Q P) ∧
        ∀ i, ∃ b : 𝓞 E, (s : E) * x i = (b : E) := by
  intro E _ _ Q ι _ x hx
  classical
  have : Fintype ι := Fintype.ofFinite ι

  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (y : E), v.valuation E y ≤ 1 →
      ∃ u : 𝓞 E, u ∉ v.asIdeal ∧ ∃ b : 𝓞 E, (u : E) * y = (b : E) := by
    intro v y hy
    obtain ⟨n, d, hnd | hnd⟩ := v.exists_primeCompl_mul_eq_or_mul_eq (K := E) y
    · exact ⟨d, d.2, n, by rw [mul_comm]; exact hnd⟩
    · have hd : v.valuation E (algebraMap (𝓞 E) E d) = 1 := by
        rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff]
        exact d.2
      have hprod : v.valuation E y * v.valuation E (algebraMap (𝓞 E) E n) = 1 := by
        rw [← map_mul, hnd, hd]
      have hn1 : 1 ≤ v.valuation E (algebraMap (𝓞 E) E n) := by
        calc (1 : _) = v.valuation E y * v.valuation E (algebraMap (𝓞 E) E n) := hprod.symm
          _ ≤ v.valuation E (algebraMap (𝓞 E) E n) := mul_le_of_le_one_left' hy
      have hn : n ∉ v.asIdeal := by
        rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := E)]
        exact le_antisymm (HeightOneSpectrum.valuation_le_one _ _) hn1
      exact ⟨n, hn, d, by rw [mul_comm]; exact hnd⟩

  let A : ι → Ideal (𝓞 E) := fun i =>
    { carrier := {r | ∃ b : 𝓞 E, (r : E) * x i = (b : E)}
      add_mem' := by
        rintro r₁ r₂ ⟨b₁, h₁⟩ ⟨b₂, h₂⟩
        exact ⟨b₁ + b₂, by push_cast; rw [add_mul, h₁, h₂]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c r ⟨b, h⟩
        exact ⟨c * b, by simp only [smul_eq_mul]; push_cast; rw [mul_assoc, h]⟩ }
  have memA : ∀ i r, r ∈ A i ↔ ∃ b : 𝓞 E, (r : E) * x i = (b : E) := fun _ _ => Iff.rfl
  let A0 : Ideal (𝓞 E) := ⨅ i, A i
  have hA0 : A0 ≠ ⊥ := by
    obtain ⟨c, hc⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) x
    have hc0 : (c : 𝓞 E) ≠ 0 := nonZeroDivisors.coe_ne_zero c
    intro hbot
    apply hc0
    have hcmem : (c : 𝓞 E) ∈ A0 := by
      refine (Submodule.mem_iInf _).mpr fun i => (memA i _).mpr ?_
      obtain ⟨b, hb⟩ := hc i
      exact ⟨b, by rw [Algebra.smul_def] at hb; exact hb.symm⟩
    rw [hbot] at hcmem
    exact (Submodule.mem_bot _).mp hcmem
  obtain ⟨h, s, hh, hs⟩ := exists_pow_eq_span_singleton E A0 hA0
  have hsA : s ∈ A0 := Ideal.pow_le_self hh (hs ▸ Ideal.mem_span_singleton_self s)
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [Ideal.span_singleton_eq_bot.mpr rfl] at hs
    exact hA0 (pow_eq_zero_iff hh |>.mp hs)
  refine ⟨s, hs0, ?_, fun i => (memA i s).mp ((Submodule.mem_iInf _).mp hsA i)⟩
  intro P hP hsP
  by_contra hQ
  have hPne : P ≠ ⊥ := fun hb => hs0 ((Submodule.mem_bot _).mp (hb ▸ hsP))
  let v : HeightOneSpectrum (𝓞 E) := ⟨P, hP, hPne⟩
  have hle : A0 ≤ P := by
    refine hP.le_of_pow_le (n := h) ?_
    rw [hs, Ideal.span_le, Set.singleton_subset_iff]
    exact hsP
  choose u hu b hb using fun i => key v (x i) (hx i v hQ)
  have hU : (∏ i, u i) ∉ P := by
    intro hmem
    obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hu i hi
  apply hU
  refine hle ((Submodule.mem_iInf _).mpr fun i => ?_)
  exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem u (Finset.mem_univ i)) ((memA i _).mpr ⟨b i, hb i⟩)

end GlobalTheory.UnRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGlobalUniformizerResidueRepresentatives
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero

namespace GlobalTheory.QNorm

theorem exists_uniformizer_and_residue_representatives :
    ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)), (∃ π : F, v.valuation F π = WithZero.exp (-1) ∧ Valued.v (algebraMap F (v.adicCompletion F) π) = WithZero.exp (-1)) ∧ (∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x) ∧ (∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1) ∧ ∃ R : Finset (v.adicCompletion F), R.card ≤ Ideal.absNorm v.asIdeal ∧ (∀ r ∈ R, Valued.v r ≤ 1) ∧ ∀ x : v.adicCompletion F, Valued.v x ≤ 1 → ∃ r ∈ R, Valued.v (x - r) < 1 := by
  intro F _ _ v
  classical
  have h2 : ∀ x : F, Valued.v (algebraMap F (v.adicCompletion F) x) = v.valuation F x :=
    fun x => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x
  have h3 : ∀ x : v.adicCompletion F, Valued.v x ≤ 1 →
      ∃ a : 𝓞 F, Valued.v (x - algebraMap F (v.adicCompletion F) (a : F)) < 1 := by
    intro x hx
    obtain ⟨a, ha⟩ := GlobalTheory.Idele.exists_valued_sub_le v hx 1
    refine ⟨a, lt_of_le_of_lt ha ?_⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  refine ⟨?_, h2, h3, ?_⟩
  · obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer F
    exact ⟨π, hπ, (h2 π).trans hπ⟩
  · haveI : Finite (𝓞 F ⧸ v.asIdeal) := v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    choose s hs using Ideal.Quotient.mk_surjective (I := v.asIdeal)
    refine ⟨Finset.univ.image fun q : 𝓞 F ⧸ v.asIdeal =>
      algebraMap F (v.adicCompletion F) ((s q : 𝓞 F) : F), ?_, ?_, ?_⟩
    · refine Finset.card_image_le.trans (le_of_eq ?_)
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Finset.card_univ, Nat.card_eq_fintype_card]
    · intro r hr
      obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 hr
      rw [h2]
      exact v.valuation_le_one (s q)
    · intro x hx
      obtain ⟨a, ha⟩ := h3 x hx
      refine ⟨_, Finset.mem_image.2 ⟨Ideal.Quotient.mk _ a, Finset.mem_univ _, rfl⟩, ?_⟩
      have hm : a - s (Ideal.Quotient.mk _ a) ∈ v.asIdeal := Ideal.Quotient.eq.1 (hs _).symm
      have hl : v.valuation F (algebraMap (𝓞 F) F (a - s (Ideal.Quotient.mk _ a))) < 1 :=
        (v.valuation_lt_one_iff_mem _).2 hm
      rw [← h2, map_sub, map_sub] at hl
      rw [← sub_add_sub_cancel x (algebraMap F (v.adicCompletion F) (a : F))]
      exact lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ha hl)

end GlobalTheory.QNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsGroupHomRangeEqOfAutStableStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_group_hom_range_eq_of_isPre : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), IsPre Γ → ∃ (G : Type) (_ : Group G) (ρ : G →* Matrix ι ι ℂ), Set.range ρ = Γ := by
  first | exact @GlobalTheory.ClassFin.IsPre.exists_group_range | exact GlobalTheory.ClassFin.IsPre.exists_group_range | (intros; apply GlobalTheory.ClassFin.IsPre.exists_group_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIndependentPrimeRelIndexSubgroups
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem relIndex_eq_prime_of_generated {G : Type} [CommGroup G] {p : ℕ} (hp : p.Prime)
    (E K : Subgroup G) (x : G) (hxE : x ∈ E) (hxK : x ∉ K) (hxp : x ^ p ∈ K)
    (hgen : ∀ y ∈ E, ∃ k : ℕ, y / x ^ k ∈ K) : K.relIndex E = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  set c : E ⧸ K.subgroupOf E := QuotientGroup.mk (⟨x, hxE⟩ : E) with hc
  have ho : orderOf c = p := by
    apply orderOf_eq_prime
    · rw [hc, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hxp
    · rw [hc, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hxK
  have hall : ∀ y : E ⧸ K.subgroupOf E, y ∈ Submonoid.powers c := by
    intro y
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hgen y y.2
    refine ⟨k, ?_⟩
    simp only [hc]
    rw [← QuotientGroup.mk_pow, eq_comm, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa using hk
  rw [Subgroup.relIndex, Subgroup.index, ← ho]
  exact (orderOf_eq_card_of_forall_mem_powers hall).symm

theorem exists_independent_prime_relIndex_subgroups (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι]
    (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ) (hp : p.Prime)
    (hH : H.relIndex U = p ^ m) (h1 : ∀ i, good i → U ⊓ H ≤ K i)
    (h2 : ∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i)
    (h2' : ∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i)
    (h3 : ∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) (k : ℕ) (hk : k ≤ m) :
    ∃ T : Finset ι, T.card = k ∧ (∀ i ∈ T, good i) ∧
      (∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j) ∧
      ∃ D : Subgroup G, (∀ x, x ∈ D ↔ ∀ i ∈ T, x ∈ K i) ∧ D.relIndex U = p ^ k := by
  induction k with
  | zero =>
    refine ⟨∅, rfl, by simp, by simp, ⊤, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨T, hT, hg, hA, D, hD, hDi⟩ := ih (by omega)
    have hx : ∃ x ∈ U, x ∈ D ∧ x ∉ H := by
      by_contra hcon
      push Not at hcon
      have heq : D ⊓ U = H ⊓ U := by
        ext x
        simp only [Subgroup.mem_inf]
        constructor
        · rintro ⟨a, b⟩
          exact ⟨hcon x b a, b⟩
        · rintro ⟨a, b⟩
          exact ⟨(hD x).2 fun i hi => h1 i (hg i hi) ⟨b, a⟩, b⟩
      have h4 : D.relIndex U = H.relIndex U := by
        rw [← Subgroup.inf_relIndex_right D U, heq, Subgroup.inf_relIndex_right]
      rw [hDi, hH] at h4
      have := Nat.pow_right_injective hp.two_le h4
      omega
    obtain ⟨x, hxU, hxD, hxH⟩ := hx
    obtain ⟨j, hj, hxj⟩ := h3 x hxU hxH
    have hjT : j ∉ T := fun h => hxj ((hD x).1 hxD j h)
    refine ⟨insert j T, by rw [Finset.card_insert_of_notMem hjT, hT], ?_, ?_, K j ⊓ D, ?_, ?_⟩
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hj
      · exact hg i hi
    · intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · refine ⟨x, hxU, hxj, fun l hl hli => ?_⟩
        rcases Finset.mem_insert.1 hl with rfl | hl
        · exact absurd rfl hli
        · exact (hD x).1 hxD l hl
      · obtain ⟨u, huU, hui, hu⟩ := hA i hi
        obtain ⟨n, hn⟩ := h2' j hj x hxU hxj u huU
        refine ⟨u / x ^ n, U.div_mem huU (U.pow_mem hxU n), ?_, fun l hl hli => ?_⟩
        · intro h
          apply hui
          have := (K i).mul_mem h ((K i).pow_mem ((hD x).1 hxD i hi) n)
          simpa using this
        · rcases Finset.mem_insert.1 hl with rfl | hl
          · exact hn
          · exact (K l).div_mem (hu l hl hli) ((K l).pow_mem ((hD x).1 hxD l hl) n)
    · intro y
      simp only [Subgroup.mem_inf, hD, Finset.forall_mem_insert]
    · have h5 : (K j).relIndex (D ⊓ U) = p :=
        relIndex_eq_prime_of_generated hp (D ⊓ U) (K j) x ⟨hxD, hxU⟩ hxj (h2 j hj x hxU)
          (fun y hy => h2' j hj x hxU hxj y hy.2)
      rw [← Subgroup.relIndex_inf_mul_relIndex, h5, hDi, pow_succ, mul_comm]

theorem exists_indep_prime_index : ∀ (p : ℕ) (G ι : Type) [CommGroup G] [DecidableEq ι] (U H : Subgroup G) (K : ι → Subgroup G) (good : ι → Prop) (m : ℕ), p.Prime → H.relIndex U = p ^ m → (∀ i, good i → U ⊓ H ≤ K i) → (∀ i, good i → ∀ x ∈ U, x ^ p ∈ K i) → (∀ i, good i → ∀ x ∈ U, x ∉ K i → ∀ y ∈ U, ∃ k : ℕ, y / x ^ k ∈ K i) → (∀ x ∈ U, x ∉ H → ∃ i, good i ∧ x ∉ K i) → ∃ T : Finset ι, T.card = m ∧ (∀ i ∈ T, good i) ∧ ∀ i ∈ T, ∃ u ∈ U, u ∉ K i ∧ ∀ j ∈ T, j ≠ i → u ∈ K j := by
  intro p G ι _ _ U H K good m hp hH h1 h2 h2' h3
  obtain ⟨T, a, b, c, -⟩ :=
    exists_independent_prime_relIndex_subgroups p G ι U H K good m hp hH h1 h2 h2' h3 m le_rfl
  exact ⟨T, a, b, c⟩

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsInfiniteAdeleTensorEquivMixedSpace
section
noncomputable section

open NumberField IsDedekindDomain NumberField.mixedEmbedding Complex Classical
open scoped TensorProduct ContDiff nonZeroDivisors

namespace GlobalTheory.InfAdeleMixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def toMixed [IsTotallyComplex E] {R : Type} [CommRing R]
    (θ : {w : InfinitePlace E // w.IsComplex} → (R →+* ℂ)) : R →+* mixedSpace E :=
  RingHom.prod
    (Pi.ringHom fun w : {w : InfinitePlace E // w.IsReal} =>
      (False.elim (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2) : R →+* ℝ))
    (Pi.ringHom θ)

theorem mixed_ext [IsTotallyComplex E] {x y : mixedSpace E} (h : ∀ w, x.2 w = y.2 w) : x = y :=
  Prod.ext (funext fun w =>
    (InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex w.1) w.2).elim) (funext h)

theorem exists_place_over [IsTotallyComplex E] [IsTotallyReal F] (v : InfinitePlace F) :
    ∃ w : {w : InfinitePlace E // w.IsComplex}, InfinitePlace.mk (w.1.embedding.comp (algebraMap F E)) = v := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  refine ⟨⟨w, IsTotallyComplex.isComplex w⟩, ?_⟩
  rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
  exact hw

theorem exists_equiv_mixedSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsTotallyReal F → IsTotallyComplex E → Module.finrank F E = 2 → (∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) → letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) := moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E); ∃ θ : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E, (∀ x : E, θ (1 ⊗ₜ[F] x) = mixedEmbedding E x) ∧ Continuous θ.symm ∧ ∀ u : (mixedSpace E)ˣ, (∀ w, ((u : mixedSpace E).2 w).im = 0) → ∃ a : (InfiniteAdeleRing F)ˣ, θ ((a : InfiniteAdeleRing F) ⊗ₜ[F] 1) = u := by
  intro F E _ _ _ _ _ σ hF hE h2 hσ
  letI : TopologicalSpace (InfiniteAdeleRing F ⊗[F] E) :=
    moduleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E)
  haveI : IsModuleTopology (InfiniteAdeleRing F) (InfiniteAdeleRing F ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (InfiniteAdeleRing F ⊗[F] E) := IsModuleTopology.toContinuousAdd (InfiniteAdeleRing F) _
  haveI : FiniteDimensional F E := Module.finite_of_finrank_pos (by omega)
  let c : E ≃ₐ[F] E := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hc' : ∀ (τ : E →+* ℂ) x, τ (c x) = starRingEnd ℂ (τ x) := hσ
  have hnr : ∀ φ : E →+* ℂ, ComplexEmbedding.conjugate φ ≠ φ := fun φ hφ =>
    IsTotallyComplex.complexEmbedding_not_isReal φ (ComplexEmbedding.isReal_iff.2 hφ)
  have hc : c ≠ 1 := by
    intro h1
    obtain ⟨φ⟩ : Nonempty (E →+* ℂ) := inferInstance
    refine hnr φ (RingHom.ext fun x => ?_)
    rw [ComplexEmbedding.conjugate_coe_eq, ← hc', h1]
    rfl
  choose θ0 h0 h0' using fun φ : E →+* ℂ => GlobalTheory.InfAdeleCM.exists_hom (F := F) φ
  have hθ := fun φ => GlobalTheory.InfAdeleCM.hom_tmul φ (θ0 φ) (h0 φ) (h0' φ)
  obtain ⟨δ, hδ0, hcδ, hs⟩ := GlobalTheory.InfAdeleCM.exists_delta c h2 hc hc'
  have hre : ∀ τ : E →+* ℂ, (τ δ).re = 0 := by
    intro τ
    have := congrArg Complex.re (hc' τ δ)
    rw [hcδ, map_neg, Complex.neg_re, Complex.conj_re] at this
    linarith
  have him : ∀ τ : E →+* ℂ, (τ δ).im ≠ 0 := by
    intro τ h
    exact hδ0 (τ.injective (by rw [map_zero]; exact Complex.ext (hre τ) h))
  let r : ∀ v : InfinitePlace F, v.Completion ≃ᵢ ℝ := fun v =>
    InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal v)
  have hr : ∀ v x, r v x = InfinitePlace.Completion.extensionEmbeddingOfIsReal (IsTotallyReal.isReal v) x :=
    fun _ _ => rfl
  let p : {w : InfinitePlace E // w.IsComplex} → InfinitePlace F := fun w =>
    InfinitePlace.mk (w.1.embedding.comp (algebraMap F E))
  let Θ : InfiniteAdeleRing F ⊗[F] E →+* mixedSpace E := toMixed fun w => θ0 w.1.embedding
  have hΘ : ∀ z w, (Θ z).2 w = θ0 w.1.embedding z := fun _ _ => rfl
  have hval : ∀ (w) (a b : InfiniteAdeleRing F), (Θ (a ⊗ₜ 1 + b ⊗ₜ δ)).2 w =
      ⟨r _ (a (p w)), r _ (b (p w)) * (w.1.embedding δ).im⟩ := by
    intro w a b
    rw [hΘ, map_add, hθ, hθ, GlobalTheory.InfAdeleCM.ext_eq_ofReal, GlobalTheory.InfAdeleCM.ext_eq_ofReal, map_one, mul_one]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, hre, mul_zero, add_zero, hr, p]
    · simp only [Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, zero_add, hr, p]
  choose t ht using exists_place_over (F := F) (E := E)
  have ht' : ∀ v, p (t v) = v := ht
  have htp : ∀ w, t (p w) = w := by
    intro w
    apply Subtype.ext
    rw [← InfinitePlace.mk_embedding (t (p w)).1, ← InfinitePlace.mk_embedding w.1]
    rcases GlobalTheory.InfAdeleCM.eq_or_conj c hc' hδ0 hcδ hs _ _ (GlobalTheory.InfAdeleCM.mk_eq_iff (ht (p w))) with e | e
    · rw [e]
    · rw [e, InfinitePlace.mk_conjugate_eq]
  let A : (({w : InfinitePlace E // w.IsComplex}) → ℝ) → InfiniteAdeleRing F := fun y v => (r v).symm (y (t v))
  have hA : Continuous A := continuous_pi fun v => (r v).symm.continuous.comp (continuous_apply (t v))
  have hA' : ∀ y w, r _ (A y (p w)) = y w := by
    intro y w
    simp only [A, IsometryEquiv.apply_symm_apply, htp]
  let G : mixedSpace E → InfiniteAdeleRing F ⊗[F] E := fun z =>
    A (fun w => (z.2 w).re) ⊗ₜ[F] (1 : E) + A (fun w => (z.2 w).im / (w.1.embedding δ).im) ⊗ₜ[F] δ
  have hG : ∀ z, Θ (G z) = z := by
    intro z
    refine mixed_ext fun w => ?_
    rw [hval]
    refine Complex.ext (hA' (fun w => (z.2 w).re) w) ?_
    have h := hA' (fun w => (z.2 w).im / (w.1.embedding δ).im) w
    exact (congrArg (· * (w.1.embedding δ).im) h).trans (div_mul_cancel₀ _ (him _))
  have hinj : Function.Injective Θ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨a, b, rfl⟩ := GlobalTheory.InfAdeleCM.exists_decomp hs z
    have key : ∀ v, a v = 0 ∧ b v = 0 := by
      intro v
      have h := hval (t v) a b
      rw [hz, ht' v] at h
      have h1 := congrArg Complex.re h
      have h3 := congrArg Complex.im h
      simp only [Prod.snd_zero, Pi.zero_apply, Complex.zero_re, Complex.zero_im] at h1 h3
      have z0 : r v 0 = 0 := by rw [hr, map_zero]
      exact ⟨(r v).injective (by rw [z0, ← h1]),
        (r v).injective (by rw [z0]; exact (mul_eq_zero.1 h3.symm).resolve_right (him _))⟩
    have ha : a = 0 := funext fun v => (key v).1
    have hb : b = 0 := funext fun v => (key v).2
    rw [ha, hb, TensorProduct.zero_tmul, TensorProduct.zero_tmul, add_zero]
  let e : InfiniteAdeleRing F ⊗[F] E ≃+* mixedSpace E := RingEquiv.ofBijective Θ ⟨hinj, fun z => ⟨G z, hG z⟩⟩
  have he : ∀ z, e z = Θ z := fun _ => rfl
  have htm : ∀ x : E, Continuous fun a : InfiniteAdeleRing F => a ⊗ₜ[F] x := by
    intro x
    have : (fun a : InfiniteAdeleRing F => a ⊗ₜ[F] x) = fun a => a • ((1 : InfiniteAdeleRing F) ⊗ₜ[F] x) := by
      funext a
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Continuous.fun_smul continuous_id' continuous_const
  refine ⟨e, fun x => mixed_ext fun w => ?_, ?_, fun u hu => ?_⟩
  · rw [he, hΘ, h0, mixedEmbedding_apply_isComplex]
  · have : (e.symm : mixedSpace E → _) = G := by
      funext z
      rw [RingEquiv.symm_apply_eq, he, hG]
    rw [this]
    have c1 : Continuous fun z : mixedSpace E => (fun w => (z.2 w).re) := by fun_prop
    have c2 : Continuous fun z : mixedSpace E => (fun w => (z.2 w).im / (w.1.embedding δ).im) := by fun_prop
    exact Continuous.fun_add ((htm 1).comp' (hA.comp' c1)) ((htm δ).comp' (hA.comp' c2))
  · have hne : ∀ w, ((u : mixedSpace E).2 w).re ≠ 0 := by
      intro w h
      have h1 : (u : mixedSpace E).2 w = 0 := Complex.ext h (hu w)
      have h3 := congrArg (fun z : mixedSpace E => z.2 w) u.mul_inv
      simp only [Prod.snd_mul, Pi.mul_apply, h1, zero_mul, Prod.snd_one, Pi.one_apply] at h3
      exact zero_ne_one h3
    have hunit : IsUnit (A fun w => ((u : mixedSpace E).2 w).re) := by
      refine Pi.isUnit_iff.2 fun v => IsUnit.mk0 _ fun h => hne (t v) ?_
      have h1 : (r v).symm ((u : mixedSpace E).2 (t v)).re = 0 := h
      have h3 := congrArg (r v) h1
      rwa [IsometryEquiv.apply_symm_apply, hr, map_zero] at h3
    refine ⟨hunit.unit, mixed_ext fun w => ?_⟩
    have h := hval w (A fun w => ((u : mixedSpace E).2 w).re) 0
    rw [TensorProduct.zero_tmul, add_zero] at h
    rw [IsUnit.unit_spec, he, h]
    refine Complex.ext (hA' (fun w => ((u : mixedSpace E).2 w).re) w) ?_
    have z0 : r (p w) ((0 : InfiniteAdeleRing F) (p w)) = 0 := by
      rw [hr]
      exact map_zero _
    rw [hu w]
    simp only [z0, zero_mul]

end GlobalTheory.InfAdeleMixed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsHermitianLogOfPosDefGramStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHermitianLogOfPosDef_gram : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (x : Matrix ι ι ℂ), IsUnit x.det → ∃ H : Matrix ι ι ℂ, IsLog H (xᴴ * x) := by
  first | exact @GlobalTheory.ClassFin.exists_isLog_gram | exact GlobalTheory.ClassFin.exists_isLog_gram | (intros; apply GlobalTheory.ClassFin.exists_isLog_gram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsQuadraticSqrtExtensionOfNotSquareStatement
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isQuadraticSqrtExtension_of_not_square : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : Algebra F E) (θ : E) (σ : E ≃ₐ[F] E), IsQuad δ θ σ := by
  first | exact @GlobalTheory.QNorm.exists_isQuad | exact GlobalTheory.QNorm.exists_isQuad | (intros; apply GlobalTheory.QNorm.exists_isQuad <;> assumption)
end

