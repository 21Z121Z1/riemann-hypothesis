import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0062
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFineSubgroupMovesAtLattice
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Formalism.LocalRingCardinality.DataSpaces
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0023
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0064
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0063
import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0028
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthonormalBasisAndOneOrbit
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivOfRetractions
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BasisOfIsCompl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FramesCommonStabiliserEqPairingMatrixStabiliser
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeUnipotentTranslateStandard
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermInvariantsIndependentOfWitnesses
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTerms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0058
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TermExponentsNonnegAndDefectGroupBound
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsGluingHomomorphismDefectGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitEntries
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralOfMulVec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0039
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0042
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0066
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0065

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.EncardSublatticesOfIndexLeStatement
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.encard_sublattices_of_index_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ i : ℕ, 1 ≤ i → (({N : Submodule (𝓞 K) V | N ≤ M ∧ idxN M N = i}.encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal ((i : ℝ) ^ ((Module.finrank K V : ℝ) + Real.logb 2 (Module.finrank ℚ K))) := by
  first | exact @GlobalTheory.Mass.sublattice_count | exact GlobalTheory.Mass.sublattice_count | (intros; apply GlobalTheory.Mass.sublattice_count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFineSubgroupMovesAtLatticeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fineSubgroup_moves_at_lattice : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∃ B : AddSubgroup S.MW, Fine (S.refA (j + 1) Λ) (ind (S.Mv (j + 1) d Λ)) B ∧ ∀ w, S.Mv (j + 1) d Λ w → ∀ b ∈ B, S.moved Λ (w + b).1.1 (w + b).2.1 (S.sOf (w + b)) = S.moved Λ w.1.1 w.2.1 (S.sOf w) ∧ S.chiM j d Λ (w + b).1 (w + b).2.1 = S.chiM j d Λ w.1 w.2.1 ∧ (S.NoLeak Λ (w + b).2.1 ↔ S.NoLeak Λ w.2.1) := by
  first | exact @GlobalTheory.MoveFine.main | exact GlobalTheory.MoveFine.main | (intros; apply GlobalTheory.MoveFine.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIdealCoprimeConjMulEqSpanSingleton
section
open NumberField IsDedekindDomain

namespace GlobalTheory

theorem exists_ideal_coprime_conj_mul_eq_spanSingleton :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E],
      Formalism.BasicNotions.CMData F E → ∀ (c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), c ≠ 0 →
      ∀ N : 𝓞 E, N ≠ 0 → ∃ P : Ideal (𝓞 E), P ≠ ⊥ ∧
        P ⊔ P.comap (RingOfIntegers.mapRingHom (starRingEnd E)) = ⊤ ∧
        (∃ t : 𝓞 E, ∃ p ∈ P, t * N + p = 1) ∧
        ∃ α : E, (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c =
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) α := by
  intro F E _ _ _ _ _ _ hcm c hc N hN
  obtain ⟨a, hac, hQ, hp⟩ := GlobalTheory.T.exists_mem_fractionalIdeal_primitive_local_generator' F E hcm.deg2 c hc N hN

  have ha : a ≠ 0 := by
    rintro rfl
    obtain ⟨p, hpm⟩ := Ideal.exists_maximal (𝓞 F)
    exact hp p hpm (Submodule.zero_mem _)

  have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a * c⁻¹ ≤ 1 := by
    rw [← mul_inv_cancel₀ hc]
    exact mul_le_mul' (FractionalIdeal.spanSingleton_le_iff_mem.mpr hac) le_rfl
  obtain ⟨P, hP⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hPc : (P : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 E)) a := by
    rw [hP, mul_assoc, inv_mul_cancel₀ hc, mul_one]

  have key : ∀ Q : Ideal (𝓞 E), P ≤ Q → a ∈ (Q : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) * c := by
    intro Q hPQ
    rw [← FractionalIdeal.spanSingleton_le_iff_mem, ← hPc]
    exact mul_le_mul' ((FractionalIdeal.coeIdeal_le_coeIdeal E).mpr hPQ) le_rfl
  have hσσ : ∀ x : 𝓞 E, RingOfIntegers.mapRingHom (starRingEnd E)
      (RingOfIntegers.mapRingHom (starRingEnd E) x) = x := by
    intro x
    ext
    simp
  refine ⟨P, ?_, ?_, ?_, a, hPc⟩
  · rintro rfl
    apply ha
    rw [FractionalIdeal.coeIdeal_bot, zero_mul, eq_comm,
      FractionalIdeal.spanSingleton_eq_zero_iff] at hPc
    exact hPc
  · by_contra htop
    obtain ⟨Q, hQm, hPQ⟩ := Ideal.exists_le_maximal _ htop
    have h1 : P ≤ Q := le_sup_left.trans hPQ
    have h2 : P ≤ Q.comap (RingOfIntegers.mapRingHom (starRingEnd E)) := by
      intro x hx
      apply hPQ (Ideal.mem_sup_right _)
      show RingOfIntegers.mapRingHom (starRingEnd E) (RingOfIntegers.mapRingHom (starRingEnd E) x) ∈ P
      rw [hσσ]
      exact hx
    have h3 := GlobalTheory.T.le_map_comap_of_le_conj_maximal_cmData F E hcm P Q hQm h1 h2
    have hpm : (Q.comap (algebraMap (𝓞 F) (𝓞 E))).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
    exact hp _ hpm (key _ h3)
  · have htop : P ⊔ Ideal.span {N} = ⊤ := by
      by_contra htop
      obtain ⟨Q, hQm, hPQ⟩ := Ideal.exists_le_maximal _ htop
      exact hQ Q hQm (hPQ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self N)))
        (key Q (le_sup_left.trans hPQ))
    have h1 : (1 : 𝓞 E) ∈ P ⊔ Ideal.span {N} := htop ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp h1
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact ⟨t, y, hy, by rw [add_comm]; exact hyz⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsOrthonormalSameIntegralSpanUnimodularStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.HL.StdPlace NumberField IsDedekindDomain
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormal_same_integralSpan_unimodular : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (Hm : Matrix (Fin n) (Fin n) E), IsHermND L Hm → ∀ b : Fin m → Fin n → E, (∀ i j, hf L Hm (b i) (b j) ∈ L.O) → (∃ P : Matrix (Fin m) (Fin m) E, IsIntM L P ∧ (Matrix.of fun i j => hf L Hm (b i) (b j)) * P = 1) → ∃ b' : Fin m → Fin n → E, (∀ i j, hf L Hm (b' i) (b' j) = if i = j then 1 else 0) ∧ Submodule.span L.O (Set.range b') = Submodule.span L.O (Set.range b) := by
  first | exact @GlobalTheory.HL.SelfDual.exists_orthonormal_same_span | exact GlobalTheory.HL.SelfDual.exists_orthonormal_same_span | (intros; apply GlobalTheory.HL.SelfDual.exists_orthonormal_same_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProdLeOfIsRadical
section
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical

namespace GlobalTheory.RowLev.SqfCrt

theorem mem_mul_smul_of_coprime {S M : Type*} [CommRing S] [AddCommGroup M] [Module S M] (N : Submodule S M)
    {A B : Ideal S} (h : IsCoprime A B) {y : M} (hA : y ∈ A • N) (hB : y ∈ B • N) : y ∈ (A * B) • N := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  have hsplit : y = a • y + b • y := by rw [← add_smul, hab, one_smul]
  rw [hsplit]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul ha hB
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hb hA

theorem mem_prod_smul_of_coprime {S M ι : Type*} [CommRing S] [AddCommGroup M] [Module S M] (N : Submodule S M)
    (J : ι → Ideal S) (hJ : ∀ i j, i ≠ j → IsCoprime (J i) (J j)) {y : M} (hy : y ∈ N) (T : Finset ι)
    (h : ∀ i ∈ T, y ∈ J i • N) : y ∈ (∏ i ∈ T, J i) • N := by
  induction T using Finset.induction_on with
  | empty => simpa [Ideal.one_eq_top, Submodule.top_smul] using hy
  | @insert a T haT ih =>
    rw [Finset.prod_insert haT]
    refine mem_mul_smul_of_coprime N ?_ (h a (Finset.mem_insert_self a T))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    exact IsCoprime.prod_right fun i hi => hJ a i fun hai => haT (hai ▸ hi)

theorem exists_prod_le_of_isRadical {R : Type*} [CommRing R] [IsDedekindDomain R] {𝔞 : Ideal R} (h0 : 𝔞 ≠ ⊥)
    (hr : 𝔞.IsRadical) : ∃ T : Finset (HeightOneSpectrum R), (∀ u ∈ T, 𝔞 ≤ u.asIdeal) ∧
      ∏ u ∈ T, u.asIdeal ≤ 𝔞 := by
  have hfin := Ideal.finite_factors h0
  refine ⟨hfin.toFinset, fun u hu => Ideal.le_of_dvd ((Set.Finite.mem_toFinset hfin).1 hu), ?_⟩
  intro x hx
  apply hr
  rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
  rintro P ⟨hle, hP⟩
  have hP0 : P ≠ ⊥ := fun hb => h0 (le_bot_iff.1 (hb ▸ hle))
  let v : HeightOneSpectrum R := ⟨P, hP, hP0⟩
  have hv : v ∈ hfin.toFinset := (Set.Finite.mem_toFinset hfin).2 (Ideal.dvd_iff_le.2 hle)
  exact (Ideal.prod_le_inf.trans (Finset.inf_le hv)) hx

theorem extId_eq_image (I : AutInst) (𝔞 : Ideal (𝓞 I.E)) : extId I 𝔞 = 𝔞.map (Inhab.psi I.F I.E) := by
  unfold extId
  rw [Ideal.map]
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, hz⟩
    exact ⟨a, ha, Subtype.ext hz.symm⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨a, ha, rfl⟩

private theorem isCoprime_map_of_ne {R S : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    (f : R →+* S) {u v : HeightOneSpectrum R} (huv : u ≠ v) :
    IsCoprime (u.asIdeal.map f) (v.asIdeal.map f) := by
  have hmax : u.asIdeal ⊔ v.asIdeal = ⊤ :=
    u.isMaximal.coprime_of_ne v.isMaximal fun e => huv (HeightOneSpectrum.ext e)
  rw [Ideal.isCoprime_iff_sup_eq, ← Ideal.map_sup, hmax, Ideal.map_top]

private theorem prod_map_le_map_of_prod_le {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (T : Finset (HeightOneSpectrum R)) {𝔞 : Ideal R} (hle : ∏ u ∈ T, u.asIdeal ≤ 𝔞) :
    ∏ u ∈ T, u.asIdeal.map f ≤ 𝔞.map f := by
  have hprod : ∀ T' : Finset (HeightOneSpectrum R),
      ∏ u ∈ T', u.asIdeal.map f = (∏ u ∈ T', u.asIdeal).map f := by
    intro T'
    induction T' using Finset.induction_on with
    | empty => rw [Finset.prod_empty, Finset.prod_empty, Ideal.one_eq_top, Ideal.one_eq_top, Ideal.map_top]
    | @insert a T' haT ih => rw [Finset.prod_insert haT, Finset.prod_insert haT, Ideal.map_mul, ih]
  rw [hprod]
  exact Ideal.map_mono hle

private theorem mem_map_smul_of_forall_mem_map_smul {R S M : Type*} [CommRing R] [IsDedekindDomain R] [CommRing S]
    [AddCommGroup M] [Module S M] (f : R →+* S) (N : Submodule S M) {𝔞 : Ideal R} (h0 : 𝔞 ≠ ⊥)
    (hr : 𝔞.IsRadical) {y : M} (hy : y ∈ N)
    (h : ∀ u : HeightOneSpectrum R, 𝔞 ≤ u.asIdeal → y ∈ u.asIdeal.map f • N) : y ∈ 𝔞.map f • N := by
  obtain ⟨T, hT, hle⟩ := exists_prod_le_of_isRadical h0 hr
  have hmem : y ∈ (∏ u ∈ T, u.asIdeal.map f) • N :=
    mem_prod_smul_of_coprime (ι := HeightOneSpectrum R) N (fun u => u.asIdeal.map f)
      (fun _ _ huv => isCoprime_map_of_ne f huv) hy T fun u hu => h u (hT u hu)
  exact Submodule.smul_mono_left (prod_map_le_map_of_prod_le f T hle) hmem

theorem mem_extId_smul_forall_iff : ∀ (I : AutInst) (m : ℕ), 1 ≤ m → (Ideal.span {(m : 𝓞 I.E)}).IsRadical →
    ∀ y ∈ I.Lf, (∀ u : HeightOneSpectrum (𝓞 I.E), (m : 𝓞 I.E) ∈ u.asIdeal → y ∈ extId I u.asIdeal • I.Lf) ↔
      ∃ z ∈ I.Lf, y = (m : (I.E ⊗[I.F] Af I.F)) • z := by
  intro I m hm hrad y hy
  constructor
  · intro h
    have h0 : Ideal.span {(m : 𝓞 I.E)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact Nat.cast_ne_zero.2 (by omega)
    have key : y ∈ (Ideal.span {(m : 𝓞 I.E)}).map (Inhab.psi I.F I.E) • I.Lf :=
      mem_map_smul_of_forall_mem_map_smul (Inhab.psi I.F I.E) I.Lf h0 hrad hy fun u hu => by
        rw [← extId_eq_image I]
        exact h u (hu (Ideal.mem_span_singleton_self _))
    rw [Ideal.map_span, Set.image_singleton, map_natCast, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at key
    obtain ⟨z, hz, hzy⟩ := key
    refine ⟨z, hz, ?_⟩
    rw [← hzy, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul]
  · rintro ⟨z, hz, rfl⟩ u hu
    have hm' : (m : IntAf I.F I.E) ∈ extId I u.asIdeal := by
      rw [extId_eq_image, ← map_natCast (Inhab.psi I.F I.E)]
      exact Ideal.mem_map_of_mem _ hu
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul (IntAf I.F I.E)]
    exact Submodule.smul_mem_smul hm' hz

end GlobalTheory.RowLev.SqfCrt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnimodularOverlatticeCyclicSplitDiscrimina
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.SplitOver

theorem cyc_iff {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] (A B : Submodule R W) (I : Ideal R) :
    Nonempty ((↥A ⧸ B.comap A.subtype) ≃ₗ[R] (R ⧸ I)) ↔
      ∃ x ∈ A, (∀ y ∈ A, ∃ r : R, y - r • x ∈ B) ∧ ∀ r : R, r • x ∈ B ↔ r ∈ I := by
  constructor
  · rintro ⟨e⟩
    obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (e.symm (Submodule.Quotient.mk 1))
    have key : ∀ r : R, e (Submodule.Quotient.mk (r • x)) = Submodule.Quotient.mk r := by
      intro r
      rw [Submodule.Quotient.mk_smul, map_smul, hx, e.apply_symm_apply, ← Submodule.Quotient.mk_smul,
        smul_eq_mul, mul_one]
    refine ⟨x, x.2, fun y hy => ?_, fun r => ?_⟩
    · obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective I (e (Submodule.Quotient.mk ⟨y, hy⟩))
      rw [← key, e.injective.eq_iff, eq_comm, Submodule.Quotient.eq] at hr
      exact ⟨r, hr⟩
    · rw [← Submodule.Quotient.mk_eq_zero I, ← key, EmbeddingLike.map_eq_zero_iff,
        Submodule.Quotient.mk_eq_zero]
      rfl
  · rintro ⟨x, hx, h1, h2⟩
    let f : R →ₗ[R] (↥A ⧸ B.comap A.subtype) :=
      (B.comap A.subtype).mkQ ∘ₗ LinearMap.toSpanSingleton R A ⟨x, hx⟩
    have hk : I = LinearMap.ker f := by
      ext r
      rw [← h2, LinearMap.mem_ker]
      exact (Submodule.Quotient.mk_eq_zero (B.comap A.subtype) (x := r • (⟨x, hx⟩ : A))).symm
    have hsurj : Function.Surjective f := by
      intro z
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
      obtain ⟨r, hr⟩ := h1 y y.2
      refine ⟨r, Eq.symm ?_⟩
      exact (Submodule.Quotient.eq (B.comap A.subtype) (x := y) (y := r • (⟨x, hx⟩ : A))).2 hr
    exact ⟨((Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hsurj)).symm⟩

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

noncomputable abbrev cj : 𝓞 K →+* 𝓞 K := locBasic_sigma (genusCovol_hinj (K := K)) star_algebraMap_ringOfIntegers_mem_range

theorem cj_cj (r : 𝓞 K) : cj (cj r) = r := genusCovol_hinj (by
  rw [locBasic_sigma_spec, locBasic_sigma_spec, star_star])

theorem mem_conj (P : Ideal (𝓞 K)) (r : 𝓞 K) : r ∈ conjIdeal (K := K) P ↔ cj r ∈ P := by
  rw [locBasic_conj_eq genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, Ideal.mem_comap]

omit [FiniteDimensional K V] in
theorem adj (h : V →ₗ⋆[K] V →ₗ[K] K) (r : 𝓞 K) (v w : V) : h v (r • w) = h (cj r • v) w := by
  rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range, genusBasic_hsmul_right]
  exact congrArg (fun t => algebraMap (𝓞 K) K t * h v w) (cj_cj r).symm

theorem smul_mem_of_gen {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W] {A B : Submodule R W}
    {I : Ideal R} {x : W} (h1 : ∀ y ∈ A, ∃ r : R, y - r • x ∈ B) (h2 : ∀ r : R, r • x ∈ B ↔ r ∈ I)
    {s : R} (hs : s ∈ I) {y : W} (hy : y ∈ A) : s • y ∈ B := by
  obtain ⟨r, hr⟩ := h1 y hy
  have : s • y = s • (y - r • x) + (s * r) • x := by rw [smul_sub, mul_smul, sub_add_cancel]
  rw [this]
  exact B.add_mem (B.smul_mem s hr) ((h2 _).2 (I.mul_mem_right r hs))

variable (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm) (hn : h.Nondegenerate)
include hs hn

theorem exists_unique_over (P : Ideal (𝓞 K)) (hc : IsCoprime P (conjIdeal (K := K) P))
    (L : Submodule (𝓞 K) V) (hL : IsIntLat h L)
    (e : Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P * conjIdeal (K := K) P))) :
    ∃! M : Submodule (𝓞 K) V, Submodule.IsLattice K M ∧ IsUnimodular h M ∧ L ≤ M ∧
      Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P)) := by
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨an, -, -, hint, huni⟩ := dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨x, hx, g1, g2⟩ := (cyc_iff _ _ _).1 e
  have hLD := (hint L).1 hL.2
  have hDD := (dl L hL.1).2.1
  have split : ∀ y : V, p • y + q • y = y := fun y => by rw [← add_smul, hpq, one_smul]
  have kill : ∀ a ∈ P, ∀ b ∈ conjIdeal (K := K) P, ∀ y ∈ dual h L, a • b • y ∈ L := fun a ha b hb y hy => by
    rw [← mul_smul]
    exact smul_mem_of_gen g1 g2 (Ideal.mul_mem_mul ha hb) hy
  let M : Submodule (𝓞 K) V := dual h L ⊓ L.comap (LinearMap.lsmul (𝓞 K) V p)
  have mem : ∀ y, y ∈ M ↔ y ∈ dual h L ∧ p • y ∈ L := fun y => Iff.rfl
  have hLM : L ≤ M := fun y hy => (mem y).2 ⟨hLD hy, L.smul_mem p hy⟩
  have hMD : M ≤ dual h L := inf_le_left
  have hQ : ∀ b ∈ conjIdeal (K := K) P, ∀ y ∈ dual h L, b • y ∈ M := fun b hb y hy =>
    (mem _).2 ⟨Submodule.smul_mem _ b hy, kill p hp b hb y hy⟩
  have hP : ∀ a ∈ P, ∀ y ∈ M, a • y ∈ L := fun a ha y hy => by
    rw [← split y, smul_add]
    exact L.add_mem (L.smul_mem a ((mem y).1 hy).2) (kill a ha q hq y (hMD hy))
  have hMu : IsUnimodular h M := by
    refine (huni M).2 ⟨fun y hy y' hy' => ?_, fun y hy => (mem y).2 ⟨an _ _ hLM hy, ?_⟩⟩
    · rw [← split y', map_add]
      refine Submodule.add_mem _ ?_ ?_
      · have := ((mem y').1 hy').2
        rw [← hDD, dualBasic_mem_dual] at this
        exact this y (hMD hy)
      · rw [adj]
        exact (dualBasic_mem_dual h L y').1 (hMD hy') _ (hP _ ((mem_conj P q).1 hq) y hy)
    · rw [← hDD, dualBasic_mem_dual]
      intro d hd
      rw [adj]
      exact (dualBasic_mem_dual h M y).1 hy _ (hQ _ ((mem_conj P _).2 (by rwa [cj_cj])) d hd)
  refine ⟨M, ⟨DiscOrder.lattice_between hL.1 (dl L hL.1).1 hLM hMD, hMu, hLM,
    (cyc_iff _ _ _).2 ⟨q • x, hQ q hq x hx, fun y hy => ?_, fun r => ⟨fun hr => ?_, fun hr => kill r hr q hq x hx⟩⟩⟩, ?_⟩
  · obtain ⟨r, hr⟩ := g1 y (hMD hy)
    refine ⟨r, ?_⟩
    have : y - r • q • x = p • y + q • (y - r • x) := by
      rw [smul_sub, smul_comm q r x, ← add_sub_assoc, split]
    rw [this]
    exact L.add_mem ((mem y).1 hy).2 (L.smul_mem q hr)
  · rw [← mul_smul, g2] at hr
    have : r = r * p + r * q := by rw [← mul_add, hpq, mul_one]
    rw [this]
    exact P.add_mem (P.mul_mem_left r hp) (Ideal.mul_le_left hr)
  · rintro N ⟨-, hNu, hLN, eN⟩
    obtain ⟨m, -, k1, k2⟩ := (cyc_iff _ _ _).1 eN
    have hNu' : dual h N = N := hNu
    have hMu' : dual h M = M := hMu
    have hNM : N ≤ M := fun y hy =>
      (mem y).2 ⟨an _ _ hLN (hNu'.symm ▸ hy), smul_mem_of_gen k1 k2 hp hy⟩
    refine le_antisymm hNM ?_
    rw [← hNu', ← hMu']
    exact an _ _ hNM

theorem disc_of_over (P : Ideal (𝓞 K)) (hP0 : P ≠ ⊥) (hc : IsCoprime P (conjIdeal (K := K) P))
    (M L : Submodule (𝓞 K) V) (hM : Submodule.IsLattice K M) (hMu : IsUnimodular h M) (hLM : L ≤ M)
    (e : Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P))) :
    IsIntLat h L ∧
      Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ P * conjIdeal (K := K) P)) := by
  have dl := dualLattice (𝓞 K) K V h hs hn star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨an, -, -, hint, huni⟩ := dualBasic (𝓞 K) K V h hs star_algebraMap_ringOfIntegers_mem_range
  obtain ⟨p, hp, q, hq, hpq⟩ := Ideal.isCoprime_iff_exists.1 hc
  obtain ⟨m, hm, k1, k2⟩ := (cyc_iff _ _ _).1 e
  obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hMu' : dual h M = M := hMu
  have hP : ∀ a ∈ P, ∀ y ∈ M, a • y ∈ L := fun a ha y hy => smul_mem_of_gen k1 k2 ha hy
  have hL : Submodule.IsLattice K L := by
    refine ⟨hM.fg.of_le hLM, ?_⟩
    rw [eq_top_iff, ← hM.span_eq_top, Submodule.span_le]
    intro y hy
    have hne : algebraMap (𝓞 K) K t ≠ 0 := (map_ne_zero_iff _ genusCovol_hinj).2 ht0
    have : y = (algebraMap (𝓞 K) K t)⁻¹ • (t • y) := by
      rw [← algebraMap_smul K t y, smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hP t ht y hy))
  have hMD : M ≤ dual h L := hMu' ▸ an _ _ hLM
  have hDD := (dl L hL).2.1
  refine ⟨⟨hL, (hint L).2 (hLM.trans hMD)⟩, ?_⟩
  have test : ∀ d ∈ dual h L, h m d ∈ (1 : Submodule (𝓞 K) K) → d ∈ M := by
    intro d hd hmd
    rw [← hMu', dualBasic_mem_dual]
    intro y hy
    obtain ⟨r, hr⟩ := k1 y hy
    have : h y d = h (y - r • m) d + h (r • m) d := by simp
    rw [this]
    refine Submodule.add_mem _ ((dualBasic_mem_dual h L d).1 hd _ hr) ?_
    rw [genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range]
    exact genusBasic_mem_one_mul _ hmd _
  have hQ : ∀ b ∈ conjIdeal (K := K) P, ∀ d ∈ dual h L, b • d ∈ M := by
    intro b hb d hd
    refine test _ (Submodule.smul_mem _ b hd) ?_
    rw [adj]
    exact (dualBasic_mem_dual h L d).1 hd _ ((k2 _).2 ((mem_conj P b).1 hb))
  have hQ' : ∀ b, (∀ d ∈ dual h L, b • d ∈ M) → b ∈ conjIdeal (K := K) P := by
    intro b hb
    rw [mem_conj, ← k2, ← hDD, dualBasic_mem_dual]
    intro d hd
    rw [adj, cj_cj]
    exact (dualBasic_mem_dual h M m).1 (hMu'.symm ▸ hm) _ (hb d hd)

  obtain ⟨d₀, hd₀, gen⟩ : ∃ d₀ ∈ dual h L, ∀ d ∈ dual h L, ∃ v : 𝓞 K, d - v • d₀ ∈ M := by
    have hs0 : cj t ≠ 0 := fun e => ht0 (by rw [← cj_cj t, e, map_zero])
    have hne : algebraMap (𝓞 K) K (cj t) ≠ 0 := (map_ne_zero_iff _ genusCovol_hinj).2 hs0
    let φ : V →ₗ[𝓞 K] K := (h (t • m)).restrictScalars (𝓞 K)
    have hφ : ∀ d, φ d = algebraMap (𝓞 K) K (cj t) * h m d := fun d =>
      genusBasic_hsmul_left genusCovol_hinj star_algebraMap_ringOfIntegers_mem_range h t m d
    let J : Ideal (𝓞 K) := ((dual h L).map φ).comap (Algebra.linearMap (𝓞 K) K)
    obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {cj t})
      (J := Ideal.span {cj t} ⊔ J) le_sup_left (by simpa using hs0)
    have ha1 : a ∈ Ideal.span {cj t} ⊔ J := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
    obtain ⟨b, hb, c₀, hc₀, rfl⟩ := Submodule.mem_sup.1 ha1
    obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨d₀, hd₀, e₀⟩ := Submodule.mem_map.1 (Submodule.mem_comap.1 hc₀)
    refine ⟨d₀, hd₀, fun d hd => ?_⟩
    obtain ⟨c, hc⟩ := Submodule.mem_one.1 ((dualBasic_mem_dual h L d).1 hd _ (hP t ht m hm))
    have hcJ : c ∈ Ideal.span {cj t} ⊔ J :=
      Ideal.mem_sup_right (Submodule.mem_comap.2 (Submodule.mem_map.2 ⟨d, hd, hc.symm⟩))
    rw [← ha] at hcJ
    obtain ⟨b, hb, b', hb', e1⟩ := Submodule.mem_sup.1 hcJ
    obtain ⟨x, rfl⟩ := Ideal.mem_span_singleton'.1 hb
    obtain ⟨v, rfl⟩ := Ideal.mem_span_singleton'.1 hb'
    refine ⟨v, test _ (Submodule.sub_mem _ hd (Submodule.smul_mem _ v hd₀))
      (Submodule.mem_one.2 ⟨x + v * u, mul_left_cancel₀ hne ?_⟩)⟩
    have e2 : φ d = algebraMap (𝓞 K) K c := hc.symm
    have e3 : φ d₀ = algebraMap (𝓞 K) K c₀ := e₀
    rw [← hφ, map_sub, map_smul, e2, e3, ← e1, Algebra.smul_def]
    simp only [map_add, map_mul]
    ring
  have gen' : ∀ r, r • d₀ ∈ M ↔ r ∈ conjIdeal (K := K) P := by
    refine fun r => ⟨fun hr => hQ' r fun d hd => ?_, fun hr => hQ r hr d₀ hd₀⟩
    obtain ⟨v, hv⟩ := gen d hd
    have : r • d = r • (d - v • d₀) + v • r • d₀ := by rw [smul_sub, smul_comm r v, sub_add_cancel]
    rw [this]
    exact M.add_mem (M.smul_mem r hv) (M.smul_mem v hr)
  have hq' : q = 1 - p := by rw [← hpq]; ring
  refine (cyc_iff _ _ _).2 ⟨q • m + p • d₀,
    Submodule.add_mem _ (Submodule.smul_mem _ _ (hMD hm)) (Submodule.smul_mem _ _ hd₀), fun d hd => ?_,
    fun r => ⟨fun hr => ?_, fun hr => ?_⟩⟩
  · obtain ⟨v, hv⟩ := gen d hd
    obtain ⟨u, hu⟩ := k1 _ (M.add_mem hv (M.smul_mem v (hQ q hq d₀ hd₀)))
    refine ⟨v * p + u * q, ?_⟩
    have : d - (v * p + u * q) • (q • m + p • d₀) = (d - v • d₀ + v • q • d₀ - u • m)
        + p • ((u * (2 - p) - v * q) • m) + p • ((v - u) • q • d₀) := by
      rw [hq']; module
    rw [this]
    exact L.add_mem (L.add_mem hu (hP p hp _ (M.smul_mem _ hm)))
      (hP p hp _ (M.smul_mem _ (hQ q hq d₀ hd₀)))
  · have e1 : r = r * p + r * q := by rw [← mul_add, hpq, mul_one]
    have h1 : r ∈ conjIdeal (K := K) P := by
      have : (r * p) • d₀ = r • (q • m + p • d₀) - (r * q) • m := by module
      have h2 : (r * p) • d₀ ∈ M := this ▸ M.sub_mem (hLM hr) (M.smul_mem _ hm)
      rw [e1]
      exact Ideal.add_mem _ ((gen' _).1 h2) (Ideal.mul_mem_left _ r hq)
    have h2 : r ∈ P := by
      have : (r * q) • m = r • (q • m + p • d₀) - p • r • d₀ := by module
      have h3 : (r * q) • m ∈ L := this ▸ L.sub_mem hr (hP p hp _ (hQ r h1 d₀ hd₀))
      rw [e1]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ r hp) ((k2 _).1 h3)
    rw [e1]
    exact Ideal.add_mem _ (mul_comm r p ▸ Ideal.mul_mem_mul hp h1) (Ideal.mul_mem_mul h2 hq)
  · have : r • (q • m + p • d₀) = r • q • m + p • r • d₀ := by module
    rw [this]
    exact L.add_mem (hP r (Ideal.mul_le_left hr) _ (M.smul_mem q hm))
      (hP p hp _ (hQ r (Ideal.mul_le_right hr) d₀ hd₀))

end GlobalTheory.Mass.SplitOver

namespace GlobalTheory.Mass.SplitOver

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (𝔓 : Ideal (𝓞 K)), 𝔓 ≠ ⊥ → IsCoprime 𝔓 (conjIdeal (K := K) 𝔓) → (∀ L : Submodule (𝓞 K) V, IsIntLat h L → Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓 * conjIdeal (K := K) 𝔓)) → ∃! M : Submodule (𝓞 K) V, Submodule.IsLattice K M ∧ IsUnimodular h M ∧ L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓))) ∧ ∀ M L : Submodule (𝓞 K) V, Submodule.IsLattice K M → IsUnimodular h M → L ≤ M → Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓)) → IsIntLat h L ∧ Nonempty ((↥(dual h L) ⧸ L.comap (dual h L).subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ 𝔓 * conjIdeal (K := K) 𝔓)) := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hn P hP0 hc
  exact ⟨exists_unique_over h hs hn P hc, disc_of_over h hs hn P hP0 hc⟩

end GlobalTheory.Mass.SplitOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesDatumMovePropertiesStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCosetFrames_datum_move_properties : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → ∀ x x' u s, S.IsMove (j + 1) d Λ x x' u s → s • x ∈ Λ ∧ L.cj s • x ∈ Λ ∧ s • x' ∈ Λ ∧ L.cj s • x' ∈ Λ ∧ (∃ c ∈ L.O, S.h x' x = algebraMap F E S.th * c) ∧ S.h x x = 0 ∧ S.h x' x' = 0 ∧ S.h u x = 0 ∧ S.h u x' = 0 ∧ x ∈ S.X ∧ x' ∈ S.X' := by
  first | exact @GlobalTheory.HL.MoveFacts.move_facts | exact GlobalTheory.HL.MoveFacts.move_facts | (intros; apply GlobalTheory.HL.MoveFacts.move_facts <;> assumption)
end

