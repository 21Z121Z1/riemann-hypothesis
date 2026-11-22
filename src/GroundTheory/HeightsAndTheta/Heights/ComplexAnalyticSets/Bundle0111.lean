import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0095
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0106
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0105
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0088

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMLengthParameters
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

theorem mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq (hCM : CMRegularElement.Statement.{u})
    {B : Type u} [CommRing B] [IsCohenMacaulayLocalRing B] {P : Ideal B} (hmin : minimalPrimes B = {P})
    {s : B} (hs : s ∉ P) : s ∈ nonZeroDivisors B := by
  by_cases hsm : s ∈ maximalIdeal B
  · refine (hCM B s hsm fun p hp => ?_).1
    rw [hmin, Set.mem_singleton_iff] at hp
    rwa [hp]
  · exact ((IsLocalRing.notMem_maximalIdeal.1 hsm)).mem_nonZeroDivisors

theorem length_localization_maximalIdeal (B : Type u) [CommRing B] [IsLocalRing B] :
    Module.length (Localization.AtPrime (maximalIdeal B)) (Localization.AtPrime (maximalIdeal B)) =
      Module.length B B := by
  have hU : (maximalIdeal B).primeCompl ≤ IsUnit.submonoid B := fun s hs =>
    IsLocalRing.notMem_maximalIdeal.1 hs
  let e := IsLocalization.atUnits B (maximalIdeal B).primeCompl
    (S := Localization.AtPrime (maximalIdeal B)) hU
  have hsurj : Function.Surjective (algebraMap B (Localization.AtPrime (maximalIdeal B))) :=
    e.surjective
  rw [← Module.length_eq_of_surjective (S := B) hsurj]
  exact e.toLinearEquiv.length_eq.symm

theorem withBot_natCast_le_of_add_one_le {k : ℕ} {D : WithBot ℕ∞}
    (h : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ D + 1) : ((k : ℕ) : WithBot ℕ∞) ≤ D := by
  induction D using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exact WithBot.coe_le_coe.2 le_top
    | coe n =>
      have h' : k + 1 ≤ n + 1 := by exact_mod_cast h
      exact_mod_cast (by omega : k ≤ n)

theorem spanFinrank_span_range_le {R : Type*} [CommRing R] {k : ℕ} (z : Fin k → R) :
    (Ideal.span (Set.range z)).spanFinrank ≤ k := by
  classical
  refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.finite_range z)).trans ?_
  have hz : Set.range z = ((Finset.univ.image z : Finset R) : Set R) := by simp
  rw [hz, Set.ncard_coe_finset]
  exact Finset.card_image_le.trans (by simp)

theorem span_range_eq_span_range_succ {R : Type*} [CommRing R] {k : ℕ} (z : Fin (k + 1) → R) (h0 : z 0 = 0) :
    Ideal.span (Set.range z) = Ideal.span (Set.range fun j : Fin k => z j.succ) := by
  refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono ?_)
  · rintro _ ⟨i, rfl⟩
    cases i using Fin.cases with
    | zero => rw [h0]; exact Ideal.zero_mem _
    | succ j => exact Ideal.subset_span ⟨j, rfl⟩
  · rintro _ ⟨j, rfl⟩
    exact ⟨j.succ, rfl⟩

theorem maximalIdeal_quotient_eq_span {B : Type u} [CommRing B] [IsLocalRing B] {I : Ideal B} {k : ℕ}
    (x : Fin k → B) (hI : Ideal.span (Set.range x) ⊔ I = maximalIdeal B) [IsLocalRing (B ⧸ I)] :
    maximalIdeal (B ⧸ I) = Ideal.span (Set.range fun i => Ideal.Quotient.mk I (x i)) := by
  rw [← map_maximalIdeal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective, ← hI, Ideal.map_sup,
    Ideal.map_span, ← Set.range_comp, Ideal.map_quotient_self, sup_bot_eq]
  rfl

theorem notMem_and_isPrime_sup_span {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {P : Ideal B} [hP : P.IsPrime] {k : ℕ} (x : Fin (k + 1) → B)
    (hdim : ringKrullDim (B ⧸ P) = ((k + 1 : ℕ) : WithBot ℕ∞))
    (hmax : Ideal.span (Set.range x) ⊔ P = maximalIdeal B) :
    x 0 ∉ P ∧ (P ⊔ Ideal.span {x 0}).IsPrime ∧
      ringKrullDim (B ⧸ (P ⊔ Ideal.span {x 0})) = ((k : ℕ) : WithBot ℕ∞) := by
  have hPm : P ≤ maximalIdeal B := hmax ▸ le_sup_right
  have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => hmax ▸ Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
  have : Nontrivial (B ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  have : IsLocalRing (B ⧸ P) := IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have hA := maximalIdeal_quotient_eq_span x hmax
  have hy : x 0 ∉ P := by
    intro hyP
    have h0 : Ideal.Quotient.mk P (x 0) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hyP
    have hle := ringKrullDim_le_spanFinrank_maximalIdeal (B ⧸ P)
    rw [hA, span_range_eq_span_range_succ (fun i => Ideal.Quotient.mk P (x i)) h0, hdim] at hle
    have hk := spanFinrank_span_range_le (fun j : Fin k => Ideal.Quotient.mk P (x j.succ))
    have h2 : ((k + 1 : ℕ) : WithBot ℕ∞) ≤ ((k : ℕ) : WithBot ℕ∞) := hle.trans (by exact_mod_cast hk)
    have h3 : k + 1 ≤ k := by exact_mod_cast h2
    omega
  set Q₀ := P ⊔ Ideal.span {x 0} with hQ₀
  have hQ₀m : Q₀ ≤ maximalIdeal B := sup_le hPm ((Ideal.span_singleton_le_iff_mem _).2 (hxm 0))
  have hmaxQ : Ideal.span (Set.range x) ⊔ Q₀ = maximalIdeal B :=
    le_antisymm (sup_le (hmax ▸ le_sup_left) hQ₀m) (hmax ▸ sup_le_sup_left le_sup_left _)
  have : Nontrivial (B ⧸ Q₀) := Ideal.Quotient.nontrivial_iff.2 fun h =>
    (IsLocalRing.maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ hQ₀m))
  have : IsLocalRing (B ⧸ Q₀) := IsLocalRing.of_surjective' (Ideal.Quotient.mk Q₀) Ideal.Quotient.mk_surjective
  have hA' := maximalIdeal_quotient_eq_span x hmaxQ
  have h0' : Ideal.Quotient.mk Q₀ (x 0) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [span_range_eq_span_range_succ (fun i => Ideal.Quotient.mk Q₀ (x i)) h0'] at hA'
  have hfin : (maximalIdeal (B ⧸ Q₀)).spanFinrank ≤ k := hA' ▸ spanFinrank_span_range_le _
  have hge : ((k : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ Q₀) := by
    have e : (B ⧸ P) ⧸ Ideal.span {Ideal.Quotient.mk P (x 0)} ≃+* B ⧸ Q₀ :=
      (Ideal.quotEquivOfEq (by rw [Ideal.map_span, Set.image_singleton])).trans
        (DoubleQuot.quotQuotEquivQuotSup P (Ideal.span {x 0}))
    have hj : ({Ideal.Quotient.mk P (x 0)} : Set (B ⧸ P)) ⊆ Ring.jacobson (B ⧸ P) := by
      rw [Set.singleton_subset_iff, IsLocalRing.ringJacobson_eq_maximalIdeal, hA]
      exact Ideal.subset_span ⟨0, rfl⟩
    have h := ringKrullDim_le_ringKrullDim_quotient_add_encard _ hj
    rw [hdim, Set.encard_singleton, ringKrullDim_eq_of_ringEquiv e] at h
    exact withBot_natCast_le_of_add_one_le (by exact_mod_cast h)
  have hle : ringKrullDim (B ⧸ Q₀) ≤ ((k : ℕ) : WithBot ℕ∞) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans (by exact_mod_cast hfin)
  have : IsRegularLocalRing (B ⧸ Q₀) :=
    IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ((by exact_mod_cast hfin :
      ((maximalIdeal (B ⧸ Q₀)).spanFinrank : WithBot ℕ∞) ≤ ((k : ℕ) : WithBot ℕ∞)).trans hge)
  have := GroundTheory.Arith.SchemeCoh.IsRegularLocalRing.isDomain (R := B ⧸ Q₀)
  exact ⟨hy, (Ideal.Quotient.isDomain_iff_prime Q₀).1 inferInstance, le_antisymm hle hge⟩

theorem CMLengthParameters.proof (hCM : CMRegularElement.Statement.{u})
    (hLen : LengthLocalizedQuotient.Statement.{u}) : CMLengthParameters.Statement.{u} := by
  suffices h : ∀ d : ℕ, ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (P : Ideal B) [P.IsPrime]
      (x : Fin d → B), minimalPrimes B = {P} → ringKrullDim (B ⧸ P) = (d : ℕ) →
      Ideal.span (Set.range x) ⊔ P = maximalIdeal B →
        Module.length B (B ⧸ Ideal.span (Set.range x)) =
          Module.length (Localization.AtPrime P) (Localization.AtPrime P) from
    fun B _ _ P _ d x => h d B P x
  intro d
  induction d with
  | zero =>
    intro B _ _ P _ x _ _ hmax
    have hx : Ideal.span (Set.range x) = ⊥ := by rw [Set.range_eq_empty, Ideal.span_empty]
    rw [hx, bot_sup_eq] at hmax
    subst hmax
    rw [hx, length_localization_maximalIdeal]
    exact (Submodule.quotEquivOfEqBot ⊥ rfl).length_eq
  | succ k ih =>
    intro B _ _ P _ x hmin hdim hmax
    obtain ⟨hyP, hQ₀, hdimQ⟩ := notMem_and_isPrime_sup_span x hdim hmax
    set y := x 0 with hy
    set Q₀ := P ⊔ Ideal.span {y} with hQ₀def
    have hxm : ∀ i, x i ∈ maximalIdeal B := fun i => hmax ▸ Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
    have hnzd : ∀ s ∉ P, s ∈ nonZeroDivisors B := fun s hs =>
      mem_nonZeroDivisors_of_notMem_of_minimalPrimes_eq hCM hmin hs
    have hyQ : Ideal.span {y} ≤ Q₀ := le_sup_right

    have hB'CM : IsCohenMacaulayLocalRing (B ⧸ Ideal.span {y}) := (hCM B y (hxm 0) fun p hp => by
      rw [hmin, Set.mem_singleton_iff] at hp
      rwa [hp]).2
    set f := Ideal.Quotient.mk (Ideal.span {y}) with hf
    have hfs : Function.Surjective f := Ideal.Quotient.mk_surjective
    have hker : RingHom.ker f ≤ Q₀ := by rw [hf, Ideal.mk_ker]; exact hyQ
    set P' := Q₀.map f with hP'def
    have hP' : P'.IsPrime := Ideal.map_isPrime_of_surjective hfs hker
    have hcomap : P'.comap f = Q₀ := by
      rw [hP'def, Ideal.comap_map_of_surjective' f hfs, sup_eq_left.2 hker]

    have hall : ∀ q : Ideal (B ⧸ Ideal.span {y}), q.IsPrime → P' ≤ q := by
      intro q hq
      have hqc : (q.comap f).IsPrime := Ideal.comap_isPrime f q
      obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (bot_le : ⊥ ≤ q.comap f)
      have hpP : p = P := by
        have : p ∈ minimalPrimes B := hp
        rw [hmin, Set.mem_singleton_iff] at this
        exact this
      subst hpP
      have hyq : Ideal.span {y} ≤ q.comap f := fun z hz => by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hz]
        exact q.zero_mem
      rw [hP'def, Ideal.map_le_iff_le_comap]
      exact sup_le hpq hyq
    have hmin' : minimalPrimes (B ⧸ Ideal.span {y}) = {P'} := by
      ext q
      rw [Set.mem_singleton_iff]
      constructor
      · intro hq
        exact le_antisymm (hq.2 ⟨hP', bot_le⟩ (hall q hq.1.1)) (hall q hq.1.1)
      · rintro rfl
        exact ⟨⟨hP', bot_le⟩, fun q hq _ => hall q hq.1⟩
    have hdim' : ringKrullDim ((B ⧸ Ideal.span {y}) ⧸ P') = (k : ℕ) := by
      rw [ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hyQ)]
      exact hdimQ

    set x' : Fin k → B ⧸ Ideal.span {y} := fun j => f (x j.succ) with hx'
    have hmB' : (maximalIdeal B).map f = maximalIdeal (B ⧸ Ideal.span {y}) :=
      map_maximalIdeal_of_surjective f hfs
    have hmax' : Ideal.span (Set.range x') ⊔ P' = maximalIdeal (B ⧸ Ideal.span {y}) := by
      apply le_antisymm
      · refine sup_le (Ideal.span_le.2 ?_) (IsLocalRing.le_maximalIdeal hP'.ne_top)
        rintro _ ⟨j, rfl⟩
        rw [← hmB']
        exact Ideal.mem_map_of_mem f (hxm _)
      · rw [← hmB', Ideal.map_le_iff_le_comap, ← hmax]
        refine sup_le (Ideal.span_le.2 ?_) fun p hp => ?_
        · rintro _ ⟨i, rfl⟩
          cases i using Fin.cases with
          | zero =>
            exact Ideal.mem_sup_right (Ideal.mem_map_of_mem f (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
          | succ j => exact Ideal.mem_sup_left (Ideal.subset_span ⟨j, rfl⟩)
        · exact Ideal.mem_sup_right (Ideal.mem_map_of_mem f (Ideal.mem_sup_left hp))
    have key := ih (B ⧸ Ideal.span {y}) P' x' hmin' hdim' hmax'
    rw [hLen B P y hmin hnzd hyP P' hcomap] at key
    rw [← key]

    have hyx : Ideal.span {y} ≤ Ideal.span (Set.range x) :=
      (Ideal.span_singleton_le_iff_mem _).2 (Ideal.subset_span ⟨0, rfl⟩)
    have hJ : (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y})) = Ideal.span (Set.range x') := by
      rw [Ideal.map_span, ← Set.range_comp]
      refine span_range_eq_span_range_succ _ ?_
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    calc Module.length B (B ⧸ Ideal.span (Set.range x))
        = Module.length B ((B ⧸ Ideal.span {y}) ⧸
            (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y}))) :=
          (DoubleQuot.quotQuotEquivQuotOfLEₐ B hyx).toLinearEquiv.length_eq.symm
      _ = Module.length (B ⧸ Ideal.span {y}) ((B ⧸ Ideal.span {y}) ⧸
            (Ideal.span (Set.range x)).map (Ideal.Quotient.mkₐ B (Ideal.span {y}))) :=
          Module.length_eq_of_surjective Ideal.Quotient.mk_surjective
      _ = Module.length (B ⧸ Ideal.span {y}) ((B ⧸ Ideal.span {y}) ⧸ Ideal.span (Set.range x')) := by
          rw [hJ]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMParameterQuotient
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

theorem IsCohenMacaulayLocalRing.of_ringEquiv {A C : Type*} [CommRing A] [CommRing C]
    [IsCohenMacaulayLocalRing A] (e : A ≃+* C) : IsCohenMacaulayLocalRing C := by
  have : Nontrivial C := e.injective.nontrivial
  have : IsLocalRing C := IsLocalRing.of_surjective' e.toRingHom e.surjective
  have : IsNoetherianRing C := isNoetherianRing_of_ringEquiv A e
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := A)
  refine { exists_isWeaklyRegular := ⟨rs.map e, ?_, ?_, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hr
    have hs' := hm s hs
    rw [mem_maximalIdeal, mem_nonunits_iff] at hs' ⊢
    exact fun h => hs' (by simpa using h.map e.symm)
  · have := RingHomInvPair.of_ringEquiv e
    have := RingHomInvPair.symm (↑e : A →+* C) (e.symm : C →+* A)
    exact (e.toSemilinearEquiv.isWeaklyRegular_congr' rs).1 hreg
  · rw [← ringKrullDim_eq_of_ringEquiv e, hdim, List.length_map]

theorem exists_nat_of_add_natCast_eq {a : WithBot ℕ∞} {m n : ℕ}
    (h : a + (m : WithBot ℕ∞) = (n : WithBot ℕ∞)) : ∃ k : ℕ, a = k ∧ k + m = n := by
  induction a using WithBot.recBotCoe with
  | bot => simp at h
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_inj, top_add] at h
      exact absurd h (ENat.top_ne_natCast n)
    | coe k =>
      refine ⟨k, rfl, ?_⟩
      exact_mod_cast h

theorem CMParameterQuotient.proof (hreg : CMRegularElement.Statement.{0}) :
    CMParameterQuotient.Statement := by
  intro B _ _ d
  induction d generalizing B with
  | zero =>
    intro x _ _
    have h0 : Ideal.span (Set.range x) = ⊥ := by
      rw [Set.range_eq_empty, Ideal.span_empty]
    exact IsCohenMacaulayLocalRing.of_ringEquiv
      ((RingEquiv.quotientBot B).symm.trans (Ideal.quotEquivOfEq h0.symm))
  | succ d ih =>
    classical
    intro x hx hdim
    let x' : Fin d → B ⧸ Ideal.span {x 0} := fun i => Ideal.Quotient.mk _ (x i.succ)
    have hIJ : Ideal.span (Set.range x) =
        Ideal.span {x 0} ⊔ Ideal.span (Set.range (Fin.tail x)) := by
      rw [Fin.range_fin_succ, Ideal.span_insert]
    have hmap : (Ideal.span (Set.range (Fin.tail x))).map (Ideal.Quotient.mk (Ideal.span {x 0})) =
        Ideal.span (Set.range x') := by
      rw [Ideal.map_span, ← Set.range_comp]
      rfl
    let e : (B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x') ≃+* B ⧸ Ideal.span (Set.range x) :=
      (Ideal.quotEquivOfEq hmap.symm).trans
        ((DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq hIJ.symm))
    have hIne : Ideal.span {x 0} ≠ ⊤ := fun h =>
      (maximalIdeal.isMaximal B).ne_top (top_le_iff.1 (h ▸ (Ideal.span_singleton_le_iff_mem _).2 (hx 0)))
    have : Nontrivial (B ⧸ Ideal.span {x 0}) := Ideal.Quotient.nontrivial_iff.2 hIne
    have : IsLocalRing (B ⧸ Ideal.span {x 0}) :=
      IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
    have : IsLocalHom (Ideal.Quotient.mk (Ideal.span {x 0})) :=
      IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
    have hx' : ∀ i, x' i ∈ maximalIdeal (B ⧸ Ideal.span {x 0}) := fun i =>
      (mem_maximalIdeal _).2 fun hu =>
        (mem_maximalIdeal _).1 (hx i.succ) (isUnit_of_map_unit (Ideal.Quotient.mk _) _ hu)
    obtain ⟨rs, -, -, hD⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
    have he := ringKrullDim_eq_of_ringEquiv e
    obtain ⟨k, hk, hkn⟩ := exists_nat_of_add_natCast_eq (hdim.trans hD)

    have hKrull : ringKrullDim (B ⧸ Ideal.span {x 0}) ≤ (k : WithBot ℕ∞) + (d : WithBot ℕ∞) := by
      have hs : ((Finset.univ.image x' : Finset _) : Set _) ⊆ SetLike.coe (Ring.jacobson (B ⧸ Ideal.span {x 0})) := by
        rw [IsLocalRing.ringJacobson_eq_maximalIdeal]
        intro z hz
        rw [Finset.coe_image, Finset.coe_univ, Set.image_univ] at hz
        obtain ⟨i, rfl⟩ := hz
        exact hx' i
      have h1 := ringKrullDim_le_ringKrullDim_quotient_add_card _ hs
      rw [Finset.coe_image, Finset.coe_univ, Set.image_univ, he, hk] at h1
      refine h1.trans ?_
      gcongr
      exact_mod_cast Finset.card_image_le.trans (Finset.card_univ.trans (Fintype.card_fin d)).le
    have hmin : ∀ p ∈ minimalPrimes B, x 0 ∉ p := by
      intro p hp hyp
      have hle : Ideal.span {x 0} ≤ p := (Ideal.span_singleton_le_iff_mem _).2 hyp
      have h1 := ringKrullDim_quotient_eq_of_mem_minimalPrimes hp
      have h2 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ Ideal.span {x 0}) :=
        ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle) (Ideal.Quotient.factor_surjective hle)
      have h3 := (h1.symm.trans_le h2).trans hKrull
      rw [hD] at h3
      have h4 : rs.length ≤ k + d := by exact_mod_cast h3
      omega
    obtain ⟨hnzd, hCM⟩ := hreg B (x 0) (hx 0) hmin
    have hdimI : ringKrullDim (B ⧸ Ideal.span {x 0}) + ((1 : ℕ) : WithBot ℕ∞) = (rs.length : WithBot ℕ∞) := by
      rw [Nat.cast_one, ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd (hx 0),
        hD]
    obtain ⟨k', hk', hk'n⟩ := exists_nat_of_add_natCast_eq hdimI
    have hdim' : ringKrullDim ((B ⧸ Ideal.span {x 0}) ⧸ Ideal.span (Set.range x')) + (d : WithBot ℕ∞) =
        ringKrullDim (B ⧸ Ideal.span {x 0}) := by
      rw [he, hk, hk']
      exact_mod_cast (by omega : k + d = k')
    have : IsCohenMacaulayLocalRing (B ⧸ Ideal.span {x 0}) := hCM
    have := ih (B ⧸ Ideal.span {x 0}) x' hx' hdim'
    exact IsCohenMacaulayLocalRing.of_ringEquiv e

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCMRegularElement
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing RingTheory.Sequence CategoryTheory Abelian Limits Pointwise

universe u

theorem mem_minimalPrimes_of_mem_associatedPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B]
    {p : Ideal B} (hp : p ∈ associatedPrimes B B) : p ∈ minimalPrimes B := by
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  obtain ⟨hprime, m, hpm⟩ := isAssociatedPrime_iff.mp hp
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hprime.ne_top
    rw [hpm, eq_top_iff]
    intro r _
    rw [Submodule.mem_colon_singleton, smul_zero]
    exact Submodule.zero_mem _
  have hD := length_le_ringKrullDim_quotient_colon rs m hm0 hm hreg
  rw [← hpm] at hD
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal B)) (J := p) bot_le
  by_cases hqp' : q = p
  · exact hqp' ▸ hq
  exfalso
  obtain ⟨a, hap, haq⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hqp hqp')
  have : q.IsPrime := hq.1.1
  have hnzd : Ideal.Quotient.mk q a ∈ nonZeroDivisors (B ⧸ q) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have hd2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnzd
  have heq : (B ⧸ q) ⧸ Ideal.span {Ideal.Quotient.mk q a} ≃+* B ⧸ (q ⊔ Ideal.span {a}) := by
    have : Ideal.span {Ideal.Quotient.mk q a} = (Ideal.span {a}).map (Ideal.Quotient.mk q) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [this]
    exact DoubleQuot.quotQuotEquivQuotSup q (Ideal.span {a})
  rw [ringKrullDim_eq_of_ringEquiv heq] at hd2
  have hle : q ⊔ Ideal.span {a} ≤ p := sup_le hqp ((Ideal.span_singleton_le_iff_mem p).mpr hap)
  have h1 : ringKrullDim (B ⧸ p) ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a})) :=
    ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective hle)
  have h2 : ringKrullDim (B ⧸ q) ≤ ringKrullDim B := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  have h3 : ringKrullDim (B ⧸ p) ≤ ringKrullDim B := ringKrullDim_le_of_surjective _ Ideal.Quotient.mk_surjective
  rw [hdim] at h2 h3
  have h4 : ringKrullDim (B ⧸ p) = (rs.length : WithBot ℕ∞) := le_antisymm h3 hD
  have h5 : ringKrullDim (B ⧸ p) + 1 ≤ (rs.length : WithBot ℕ∞) :=
    ((by gcongr : ringKrullDim (B ⧸ p) + 1 ≤ ringKrullDim (B ⧸ (q ⊔ Ideal.span {a})) + 1).trans hd2).trans h2
  rw [h4] at h5
  norm_cast at h5
  omega

theorem mem_nonZeroDivisors_of_not_mem_minimalPrimes {B : Type*} [CommRing B] [IsCohenMacaulayLocalRing B] {y : B}
    (hy : ∀ p ∈ minimalPrimes B, y ∉ p) : y ∈ nonZeroDivisors B := by
  by_contra h
  have h' : y ∈ (nonZeroDivisors B : Set B)ᶜ := h
  rw [← biUnion_associatedPrimes_eq_compl_nonZeroDivisors, Set.mem_iUnion₂] at h'
  obtain ⟨p, hp, hyp⟩ := h'
  exact hy p (mem_minimalPrimes_of_mem_associatedPrimes hp) hyp

theorem exists_isRegular_quotSMulTop {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {rs : List B} (hm : ∀ r ∈ rs, r ∈ maximalIdeal B) (hreg : IsWeaklyRegular B rs)
    {y : B} (hy : IsSMulRegular B y) (hym : y ∈ maximalIdeal B) :
    ∃ rs' : List B, rs'.length = rs.length - 1 ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧
      IsRegular (QuotSMulTop y B) rs' := by
  have key : ∀ (X : Type u) [AddCommGroup X] [Module B X] [Module.Finite B X] [Nontrivial X],
      maximalIdeal B • (⊤ : Submodule B X) < ⊤ := fun X _ _ _ _ => by
    refine (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator ?_).symm.lt_top
    have H : Module.annihilator B X ≠ ⊤ := fun h => not_subsingleton X (Module.annihilator_eq_top_iff.mp h)
    exact (jacobson_eq_maximalIdeal _ H).ge
  have hne : (y • (⊤ : Submodule B B)) ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ y • (⊤ : Submodule B B) := by rw [h]; exact Submodule.mem_top
    obtain ⟨b, -, hb⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h1
    exact (mem_maximalIdeal _).mp hym (IsUnit.of_mul_eq_one b (by simpa [smul_eq_mul] using hb))
  have : Nontrivial (QuotSMulTop y B) := Submodule.Quotient.nontrivial_iff.mpr hne
  let M : ModuleCat.{u} B := ModuleCat.of B B
  let S := ModuleCat.smulShortComplex M y
  have hS : S.ShortExact := IsSMulRegular.smulShortComplex_shortExact (M := M) hy
  let N : ModuleCat.{u} B := ModuleCat.of B (Shrink.{u} (B ⧸ maximalIdeal B))
  have hregB : IsRegular B rs := (isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hm).mpr hreg
  have hextB : ∀ i < rs.length, Subsingleton (Ext N M i) :=
    ((ModuleCat.exists_isRegular_tfae (maximalIdeal B) rs.length M (key B)).out 1 3).mpr
      (⟨rs, rfl, hm, hregB⟩ : ∃ rs' : List B, rs'.length = rs.length ∧ (∀ r ∈ rs', r ∈ maximalIdeal B) ∧ IsRegular M rs')
  have hext3 : ∀ i < rs.length - 1, Subsingleton (Ext N S.X₃ i) := by
    intro i hi
    have hex := Ext.covariant_sequence_exact₃' N hS i (i + 1) rfl
    have h1 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₂ i)) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB i (by omega))
    have h3 : IsZero (AddCommGrpCat.of (Abelian.Ext N S.X₁ (i + 1))) :=
      AddCommGrpCat.isZero_of_iff_subsingleton.mpr (hextB (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero (hex.isZero_of_both_zeros (h1.eq_of_src _ _) (h3.eq_of_tgt _ _))
  have : Module.Finite B S.X₃ := inferInstanceAs (Module.Finite B (QuotSMulTop y B))
  have : Nontrivial S.X₃ := inferInstanceAs (Nontrivial (QuotSMulTop y B))
  obtain ⟨rs', hlen, hm', hreg'⟩ :=
    ((ModuleCat.exists_isRegular_tfae (maximalIdeal B) (rs.length - 1) S.X₃ (key S.X₃)).out 1 3).mp hext3
  exact ⟨rs', hlen, hm', hreg'⟩

theorem CMRegularElement.proof : CMRegularElement.Statement.{u} := by
  intro B _ _ y hym hy
  have hnzd := mem_nonZeroDivisors_of_not_mem_minimalPrimes hy
  refine ⟨hnzd, ?_⟩
  obtain ⟨rs, hm, hreg, hdim⟩ := IsCohenMacaulayLocalRing.exists_isWeaklyRegular (B := B)
  have hyreg : IsSMulRegular B y := Module.Flat.isSMulRegular_of_nonZeroDivisors hnzd
  obtain ⟨rs', hlen, hm', hreg'⟩ := exists_isRegular_quotSMulTop hm hreg hyreg hym
  set I := Ideal.span {y} with hIdef
  have hI : I ≠ ⊤ := Ideal.span_singleton_ne_top ((mem_maximalIdeal _).mp hym)
  have : Nontrivial (B ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  have : IsLocalRing (B ⧸ I) := IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have hloc : IsLocalHom (Ideal.Quotient.mk I) := isLocalHom_of_le_jacobson_bot I (by
    rw [jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).mpr hym)
  have hsub : (y • (⊤ : Submodule B B)) = I := by
    rw [hIdef, ← Submodule.ideal_span_singleton_smul, Ideal.smul_eq_mul, Ideal.mul_top]
  let e : QuotSMulTop y B ≃ₗ[B] B ⧸ I := Submodule.quotEquivOfEq _ _ hsub
  have hw : IsWeaklyRegular (B ⧸ I) (rs'.map (algebraMap B (B ⧸ I))) :=
    (isWeaklyRegular_map_algebraMap_iff (S := B ⧸ I) (M := B ⧸ I) rs').mpr
      ((e.isWeaklyRegular_congr rs').mp hreg'.toIsWeaklyRegular)
  have hdimq := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hnzd hym
  refine { exists_isWeaklyRegular := ⟨rs'.map (algebraMap B (B ⧸ I)), ?_, hw, ?_⟩ }
  · intro r hr
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
    exact map_nonunit (Ideal.Quotient.mk I) s (hm' s hs)
  · rw [List.length_map, hlen]
    have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim (B ⧸ I) := ringKrullDim_nonneg_of_nontrivial
    rw [hdim] at hdimq
    obtain ⟨d, hd⟩ : ∃ d : ℕ∞, ringKrullDim (B ⧸ I) = d :=
      (WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.zero_ne_bot h0)).imp fun _ h => h.symm
    rw [hd] at hdimq ⊢
    have h2 : d + 1 = (rs.length : ℕ∞) := by exact_mod_cast hdimq
    induction d using ENat.recTopCoe with
    | top => simp at h2
    | coe k =>
      norm_cast at h2 ⊢
      rw [show k = rs.length - 1 by omega]

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchOffHypersurface
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial

noncomputable section

def BranchOffHypersurface.Statement : Prop :=
  ∀ (n k : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (b : MvPolynomial (Fin n) ℂ) (U : Set (Fin k → ℂ))
    (φ : (Fin k → ℂ) → Fin n → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (k : ℕ) → b ∉ J →
    IsOpen U → U.Nonempty → DifferentiableOn ℂ φ U → Set.InjOn φ U → Set.MapsTo φ U (zeroSetIn J) →
    ∃ t ∈ U, eval (φ t) b ≠ 0

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

