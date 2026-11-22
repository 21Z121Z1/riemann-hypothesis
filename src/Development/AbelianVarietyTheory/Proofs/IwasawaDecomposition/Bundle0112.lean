import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Formalism.LocalToGlobal.UnitaryNorms.CharHost
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqOfMapEq
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.GoodPlace

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem plc_eq_absNorm (v : HeightOneSpectrum (𝓞 F)) (h : (Ideal.absNorm v.asIdeal).Prime) :
    Formalism.EigenvalueLevelCeiling.plc v = Ideal.absNorm v.asIdeal := by
  have := v.isPrime
  have : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  unfold Formalism.EigenvalueLevelCeiling.plc
  apply CharP.ringChar_of_prime_eq_zero h
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.absNorm_mem _

theorem absNorm_map (h2 : Module.finrank F E = 2) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (Ideal.map (algebraMap (𝓞 F) (𝓞 E)) I) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, ← h2]
  congr 1
  exact (Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E).symm

theorem absNorm_under_dvd (P : HeightOneSpectrum (𝓞 E)) :
    Ideal.absNorm (P.under (𝓞 F)).asIdeal ∣ Ideal.absNorm P.asIdeal := by
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact AddSubgroup.card_dvd_of_injective
    (Ideal.quotientMap P.asIdeal (algebraMap (𝓞 F) (𝓞 E)) le_rfl).toAddMonoidHom Ideal.quotientMap_injective

theorem of_split (h2 : Module.finrank F E = 2) {v : HeightOneSpectrum (𝓞 F)} (hv : Formalism.L2.DIV.DegOne v)
    {Q Q' : HeightOneSpectrum (𝓞 E)} (hne : Q ≠ Q')
    (hm : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * Q'.asIdeal) (hQ : Q.under (𝓞 F) = v) :
    Ideal.absNorm Q.asIdeal = Ideal.absNorm v.asIdeal ∧ ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 := by
  have hN : Ideal.absNorm Q.asIdeal * Ideal.absNorm Q'.asIdeal = Ideal.absNorm v.asIdeal ^ 2 := by
    rw [← map_mul, ← hm, absNorm_map h2]
  have h1 : Ideal.absNorm Q.asIdeal ≠ 1 := fun h => Q.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  have h1' : Ideal.absNorm Q'.asIdeal ≠ 1 := fun h => Q'.isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
  refine ⟨((Nat.Prime.mul_eq_prime_sq_iff hv.1 h1 h1').1 hN).1, ?_⟩
  intro hmem
  have hqv : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F) ∈ v.asIdeal := Ideal.absNorm_mem _
  obtain ⟨I, hI⟩ : v.asIdeal ∣ Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)} :=
    Ideal.dvd_span_singleton.2 hqv
  have hd : Q.asIdeal ^ 2 ∣ Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (Ideal.span {((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 F)}) := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
    exact Ideal.dvd_span_singleton.2 hmem
  rw [hI, Ideal.map_mul, hm, pow_two, mul_assoc, mul_dvd_mul_iff_left Q.ne_bot] at hd
  rcases (Ideal.prime_of_isPrime Q.ne_bot Q.isPrime).dvd_or_dvd hd with h | h
  · exact hne (HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le Q.isPrime.ne_top (Ideal.le_of_dvd h)).symm)
  · have hle : I ≤ v.asIdeal := by
      rw [← hQ]
      exact Ideal.map_le_iff_le_comap.1 (Ideal.le_of_dvd h)
    apply hv.2
    rw [← Ideal.span_singleton_le_iff_mem, hI, pow_two]
    exact Ideal.mul_mono_right hle

theorem under_eq_of_map_eq {v : HeightOneSpectrum (𝓞 F)} {Q : HeightOneSpectrum (𝓞 E)} {J : Ideal (𝓞 E)}
    (hm : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = Q.asIdeal * J) : Q.under (𝓞 F) = v := by
  refine (HeightOneSpectrum.ext (v.isMaximal.eq_of_le (Q.under (𝓞 F)).isPrime.ne_top ?_)).symm
  exact Ideal.map_le_iff_le_comap.1 (hm ▸ Ideal.mul_le_left)

theorem map_eq_mul (h2 : Module.finrank F E = 2) {P P' : HeightOneSpectrum (𝓞 E)} (hne : P ≠ P')
    (hu : P'.under (𝓞 F) = P.under (𝓞 F)) :
    Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal = P.asIdeal * P'.asIdeal := by
  have hle : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal ≤ P.asIdeal * P'.asIdeal := by
    rw [Ideal.mul_eq_inf_of_isCoprime (HeightOneSpectrum.isCoprime_of_ne P P' hne)]
    refine le_inf Ideal.map_comap_le ?_
    rw [← hu]
    exact Ideal.map_comap_le
  obtain ⟨J, hJ⟩ := Ideal.dvd_iff_le.2 hle
  have hN := absNorm_map h2 (P.under (𝓞 F)).asIdeal
  obtain ⟨a, ha⟩ := absNorm_under_dvd (F := F) P
  obtain ⟨b, hb⟩ := absNorm_under_dvd (F := F) P'
  rw [hu] at hb
  have h0 : Ideal.absNorm (P.under (𝓞 F)).asIdeal ≠ 0 := fun h => (P.under (𝓞 F)).ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  rw [hJ, map_mul, map_mul, ha, hb] at hN
  have h3 : (a * b) * Ideal.absNorm J = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero 2 h0)
    rw [mul_one]
    refine Eq.trans ?_ hN
    ring
  rw [hJ, Ideal.absNorm_eq_one_iff.1 (Nat.eq_one_of_mul_eq_one_left h3), Ideal.mul_top]

theorem goodPl_iff (h2 : Module.finrank F E = 2) (S : Set ℕ) (P : HeightOneSpectrum (𝓞 E)) :
    Formalism.L2.DIV.GoodPl E S (P.under (𝓞 F)) ↔ ((∃ P', P ≠ P' ∧ P'.under (𝓞 F) = P.under (𝓞 F)) ∧
      (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2 ∧
      Ideal.absNorm P.asIdeal ∉ S) := by
  constructor
  · rintro ⟨⟨Q, Q', hne, hm⟩, hv, hS⟩
    obtain ⟨P', hne', hm'⟩ : ∃ P', P ≠ P' ∧
        Ideal.map (algebraMap (𝓞 F) (𝓞 E)) (P.under (𝓞 F)).asIdeal = P.asIdeal * P'.asIdeal := by
      have hle : Q.asIdeal * Q'.asIdeal ≤ P.asIdeal := by
        rw [← hm]
        exact Ideal.map_comap_le
      rcases P.isPrime.mul_le.1 hle with h | h
      · obtain rfl : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h)
        exact ⟨Q', hne, hm⟩
      · obtain rfl : Q' = P := HeightOneSpectrum.ext (Q'.isMaximal.eq_of_le P.isPrime.ne_top h)
        exact ⟨Q, hne.symm, by rw [hm, mul_comm]⟩
    obtain ⟨e, hn⟩ := of_split h2 hv hne' hm' rfl
    rw [plc_eq_absNorm _ hv.1] at hS
    rw [e]
    exact ⟨⟨P', hne', under_eq_of_map_eq (hm'.trans (mul_comm _ _))⟩, hv.1, hn, hS⟩
  · rintro ⟨⟨P', hne, hu⟩, hp, hn, hS⟩
    have e : Ideal.absNorm (P.under (𝓞 F)).asIdeal = Ideal.absNorm P.asIdeal :=
      ((Nat.dvd_prime hp).1 (absNorm_under_dvd P)).resolve_left fun h =>
        (P.under (𝓞 F)).isPrime.ne_top (Ideal.absNorm_eq_one_iff.1 h)
    refine ⟨⟨P, P', hne, map_eq_mul h2 hne hu⟩, ⟨e ▸ hp, fun h => hn ?_⟩, ?_⟩
    · rw [e] at h
      have h3 := Ideal.mem_map_of_mem (algebraMap (𝓞 F) (𝓞 E)) h
      rw [map_natCast, Ideal.map_pow] at h3
      exact Ideal.pow_right_mono Ideal.map_comap_le 2 h3
    · rw [plc_eq_absNorm _ (e ▸ hp), e]
      exact hS

end General

theorem isSplitPl_iff {R : Ranks} (H : Formalism.BasicNotions.Host R) (P : HeightOneSpectrum (𝓞 H.E)) :
    IsSplitPl H P ↔ ∃ P', P ≠ P' ∧ P'.under (𝓞 H.F) = P.under (𝓞 H.F) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨P', hP', -⟩ := existsUnique_conjPl c.toRingEquiv P
    refine ⟨P', ?_, (under_eq_iff_conjPl c hcm.rank hcm.ne P P').2 (Or.inr hP')⟩
    rintro rfl
    exact hy (RingOfIntegers.mapRingEquiv c.toRingEquiv x) (hc x) (((conjPl_iff_mem _ P P).1 hP' x _ rfl).1 hx)
  · rintro ⟨P', hne, hu⟩
    have hP' := ((under_eq_iff_conjPl c hcm.rank hcm.ne P P').1 hu).resolve_left hne.symm
    rw [conjPl_iff_mem] at hP'
    by_contra hn
    unfold IsSplitPl at hn
    push Not at hn
    refine hne (HeightOneSpectrum.ext (P'.isMaximal.eq_of_le P.isPrime.ne_top fun y hy => ?_).symm)
    have hxy : (y : H.E) = c.toRingEquiv ((RingOfIntegers.mapRingEquiv c.toRingEquiv).symm y : 𝓞 H.E) :=
      congrArg (fun z : 𝓞 H.E => (z : H.E)) ((RingOfIntegers.mapRingEquiv c.toRingEquiv).apply_symm_apply y).symm
    obtain ⟨z, hz, hzP⟩ := hn _ ((hP' _ y hxy).2 hy)
    have e : z = y := RingOfIntegers.ext (hz.trans ((hc _).symm.trans hxy.symm))
    exact e ▸ hzP

open Classical in

theorem goodPl_under_iff : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (S : Set ℕ) (P : HeightOneSpectrum (𝓞 H.E)), Formalism.L2.DIV.GoodPl H.E S (P.under (𝓞 H.F)) ↔ (IsSplitPl H P ∧ (Ideal.absNorm P.asIdeal).Prime ∧ ((Ideal.absNorm P.asIdeal : ℕ) : 𝓞 H.E) ∉ P.asIdeal ^ 2 ∧ Ideal.absNorm P.asIdeal ∉ S) := by
  intro R H S P
  obtain ⟨c, -, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm R H
  rw [isSplitPl_iff]
  exact goodPl_iff hcm.rank S P

end GlobalTheory.Mem.GoodPlace
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalAnticyclotomicCharacterLaws
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.FrobeniusOrbits GlobalTheory.HeckeGal

namespace GlobalTheory.GalChar

theorem isTorsionFree_field (E Ω : Type) [Field E] [Field Ω] [Algebra E Ω] : Module.IsTorsionFree E Ω := inferInstance

attribute [local instance 10000] isTorsionFree_field

section Avatar

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] {l : ℕ} [Fact l.Prime]
  {O : Type} [CommRing O] [IsDomain O]

def toQ (κ : FractionRing O →+* Qbar l) : O →+* Qbar l := κ.comp (algebraMap O (FractionRing O))

def inQ (κ : FractionRing O →+* Qbar l) (r : G E Ω →* Oˣ) : G E Ω →* (Qbar l)ˣ :=
  (Units.map (toQ κ).toMonoidHom).comp r

def IsGal [TopologicalSpace O] (art : Ideles E →* Gab E Ω) (κ : FractionRing O →+* Qbar l) (ι : Qbar l ≃+* ℂ)
    (χ : HChar E) (n : (E →+* ℂ) → ℤ) (r : G E Ω →* Oˣ) : Prop :=
  IsAlgPos χ n ∧ Continuous (fun g => ((r g : Oˣ) : O)) ∧ IsLAdicOf art ι χ n (inQ κ r)

def sideIso (ι : Qbar l ≃+* ℂ) (b : Bool) : Qbar l ≃+* ℂ :=
  if b then ι else ι.trans (starRingAut : ℂ ≃+* ℂ)

def block (μ η : HChar E) (r : ℕ) : HChar E := μ * (η⁻¹ * Model.absPow E (-(r : ℝ) / 2))

end Avatar

section Universal

variable {R : Ranks} (H : Formalism.BasicNotions.Host R) {Ω : Type} [Field Ω] [Algebra H.E Ω]

def delAt {e : Fin R.m → R.Psi → ℚ} (C : GlobalTheory.Mem.Chr.HFrame H e) (l : ℕ) : HChar H.E :=
  if l = H.pde then C.del' else C.del

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  let φ : H.E →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  have h := fun y => H.conjE_apply φ y
  exact (h _).trans ((congrArg (starRingEnd ℂ) (h x)).trans (Complex.conj_conj _))

def pair (P : PlE H) : Set (PlE H) := {v | v = P ∨ IsConjPl H P v}

variable {H}

theorem isConjPl_symm {P P' : PlE H} (h : IsConjPl H P P') : IsConjPl H P' P := fun x y e =>
  (h y x (by rw [e, conj_conj])).symm

theorem isConjPl_unique {P P' P'' : PlE H} (h : IsConjPl H P P') (h' : IsConjPl H P P'') : P' = P'' :=
  (GlobalTheory.Mem.Chr.existsUnique_conjPl H.conj.toRingEquiv P).unique
    ((GlobalTheory.Mem.Chr.conjPl_main.2.1 R H P P').1 h) ((GlobalTheory.Mem.Chr.conjPl_main.2.1 R H P P'').1 h')

theorem pair_eq {P P' : PlE H} (h : IsConjPl H P P') : pair H P' = pair H P := by
  ext v
  constructor
  · rintro (rfl | hv)
    · exact Or.inr h
    · exact Or.inl (isConjPl_unique hv (isConjPl_symm h))
  · rintro (rfl | hv)
    · exact Or.inr (isConjPl_symm h)
    · exact Or.inl (isConjPl_unique hv h)

variable (H) (cc : Ω ≃+* Ω) (l : ℕ)

def IsDel (M : ℕ) (T : Set (PlE H)) (d : G H.E Ω →* Multiplicative (ZMod (l ^ M))) : Prop :=
  IsOpen (d.ker : Set (G H.E Ω)) ∧ AntiHom cc d ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A, d σ = 1) ∧
    (∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, d σ = 1) ∧
    (∀ v, v ∈ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ c, ∃ σ ∈ Ine (F := H.E) A, d σ = c)

open Classical in

def delOf (M : ℕ) (T : Set (PlE H)) : G H.E Ω →* Multiplicative (ZMod (l ^ M)) :=
  if h : ∃ d, IsDel H cc l M T d then h.choose else 1

theorem isDel_delOf {M : ℕ} {T : Set (PlE H)} (h : ∃ d, IsDel H cc l M T d) : IsDel H cc l M T (delOf H cc l M T) := by
  rw [delOf, dif_pos h]
  exact h.choose_spec

theorem delOf_laws (M : ℕ) (T : Set (PlE H)) :
    IsOpen ((delOf H cc l M T).ker : Set (G H.E Ω)) ∧ AntiHom cc (delOf H cc l M T) ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A,
      delOf H cc l M T σ = 1) ∧
    (∀ v, v ∉ T → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, delOf H cc l M T σ = 1) := by
  by_cases h : ∃ d, IsDel H cc l M T d
  · obtain ⟨h1, h2, h3, h4, -⟩ := isDel_delOf H cc l h
    exact ⟨h1, h2, h3, h4⟩
  · rw [delOf, dif_neg h]
    refine ⟨by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

open Classical in

def delCoord (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) : G H.E Ω →* Multiplicative (ZMod (l ^ M)) :=
  if pair H P ⊆ ↑Q then delOf H cc l M (pair H P) else 1

def delU (Q : Finset (PlE H)) (M : ℕ) : G H.E Ω →* Multiplicative (DelQM H l Q M) where
  toFun σ := Multiplicative.ofAdd fun P => Multiplicative.toAdd (delCoord H cc l Q M P.1 σ)
  map_one' := by simp only [map_one, toAdd_one]; rfl
  map_mul' g h := by simp only [map_mul, toAdd_mul]; rfl

theorem delU_apply (Q : Finset (PlE H)) (M : ℕ) (σ : G H.E Ω) (P : ↥Q) :
    Multiplicative.toAdd (delU H cc l Q M σ) P = Multiplicative.toAdd (delCoord H cc l Q M P.1 σ) := rfl

theorem delU_eq_one_iff (Q : Finset (PlE H)) (M : ℕ) (σ : G H.E Ω) :
    delU H cc l Q M σ = 1 ↔ ∀ P ∈ Q, delCoord H cc l Q M P σ = 1 :=
  ⟨fun h P hP => Multiplicative.toAdd.injective (congrFun (congrArg Multiplicative.toAdd h) ⟨P, hP⟩),
    fun h => Multiplicative.toAdd.injective (funext fun P => congrArg Multiplicative.toAdd (h P.1 P.2))⟩

theorem delCoord_laws (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) :
    IsOpen ((delCoord H cc l Q M P).ker : Set (G H.E Ω)) ∧ AntiHom cc (delCoord H cc l Q M P) ∧
    (∀ v ∈ placesOver H.E l, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Dec (F := H.E) A,
      delCoord H cc l Q M P σ = 1) ∧
    (∀ v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A,
      delCoord H cc l Q M P σ = 1) := by
  unfold delCoord
  split_ifs with h
  · obtain ⟨h1, h2, h3, h4⟩ := delOf_laws H cc l M (pair H P)
    exact ⟨h1, h2, h3, fun v hv => h4 v fun hm => hv (h hm)⟩
  · refine ⟨by simp, fun _ _ _ => by simp, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ => rfl⟩

theorem delCoord_of_closed {Q : Finset (PlE H)} (hQ : ∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) (M : ℕ) {P : PlE H}
    (hP : P ∈ Q) : delCoord H cc l Q M P = delOf H cc l M (pair H P) := by
  refine if_pos ?_
  rintro v (rfl | hv)
  · exact hP
  · exact hQ P hP v hv

def UniversalAnticyclotomicCharLaws : Prop :=
  (∀ Q M v, v ∉ Q → ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ ∈ Ine (F := H.E) A, delU H cc l Q M σ = 1) ∧
  (∀ Q M v, v ∈ placesOver H.E l → ∀ A : ValuationSubring Ω, IsPlaceOver A v →
    ∀ σ ∈ Dec (F := H.E) A, delU H cc l Q M σ = 1) ∧
  (∀ Q M, AntiHom cc (delU H cc l Q M)) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ), IsOpen ((delU H cc l Q M).ker : Set (G H.E Ω))) ∧
  (∀ (M : ℕ) (Q' Q : Finset (PlE H)) (h : Q' ⊆ Q),
    (∀ P ∈ Q', ∀ P', IsConjPl H P P' → P' ∈ Q') → (∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) →
    ∀ (σ : G H.E Ω) (P : PlE H) (hP : P ∈ Q'),
      Multiplicative.toAdd (delU H cc l Q' M σ) ⟨P, hP⟩ = Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, h hP⟩) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ) (P : PlE H) (hP : P ∈ Q) (P' : PlE H) (hP' : P' ∈ Q),
    IsConjPl H P P' → ∃ s : ℤˣ, ∀ σ : G H.E Ω,
      Multiplicative.toAdd (delU H cc l Q M σ) ⟨P', hP'⟩ =
        ((s : ℤ) : ZMod (l ^ M)) * Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, hP⟩) ∧
  (∀ (Q : Finset (PlE H)) (M : ℕ), (∀ P ∈ Q, ∀ P', IsConjPl H P P' → P' ∈ Q) → ∀ (P : PlE H) (hP : P ∈ Q) (σ : G H.E Ω),
    Multiplicative.toAdd (delU H cc l Q M σ) ⟨P, hP⟩ = Multiplicative.toAdd (delOf H cc l M (pair H P) σ)) ∧
  ∀ (M : ℕ) (P : PlE H), (∃ d, IsDel H cc l M (pair H P) d) → IsDel H cc l M (pair H P) (delOf H cc l M (pair H P))

theorem universal_anticyclotomic_character_laws : UniversalAnticyclotomicCharLaws H cc l := by
  refine ⟨fun Q M v hv A hA σ hσ => ?_, fun Q M v hv A hA σ hσ => ?_, fun Q M g g' h => ?_, fun Q M => ?_,
    fun M Q' Q h h1 h2 σ P hP => ?_, fun Q M P hP P' hP' h => ⟨1, fun σ => ?_⟩, fun Q M hQ P hP σ => ?_,
    fun M P h => isDel_delOf H cc l h⟩
  · exact (delU_eq_one_iff H cc l Q M σ).2 fun P _ => (delCoord_laws H cc l Q M P).2.2.2 v hv A hA σ hσ
  · exact (delU_eq_one_iff H cc l Q M σ).2 fun P _ => (delCoord_laws H cc l Q M P).2.2.1 v hv A hA σ hσ
  · exact Multiplicative.toAdd.injective (funext fun P =>
      congrArg Multiplicative.toAdd ((delCoord_laws H cc l Q M P.1).2.1 g g' h))
  · have e : ((delU H cc l Q M).ker : Set (G H.E Ω)) = ⋂ P ∈ Q, ((delCoord H cc l Q M P).ker : Set (G H.E Ω)) := by
      ext σ
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_iInter, delU_eq_one_iff]
    rw [e]
    exact isOpen_biInter_finset fun P _ => (delCoord_laws H cc l Q M P).1
  · rw [delU_apply, delU_apply, delCoord_of_closed H cc l h1 M hP, delCoord_of_closed H cc l h2 M (h hP)]
  · rw [delU_apply, delU_apply]
    have e : delCoord H cc l Q M P' = delCoord H cc l Q M P := by
      unfold delCoord
      rw [pair_eq h]
    simp only [e, Units.val_one, Int.cast_one, one_mul]
  · rw [delU_apply, delCoord_of_closed H cc l hQ M hP]

end Universal

theorem delUTie_of_exists {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}
    (Y : NExp D.R D.host D.what₂ D.LL0 N X) (hY : ∀ i Q M, Y.delU i Q M = delU D.host X.cc (X.l i) Q M)
    (h : GlobalTheory.TwSys.K1 X) : GlobalTheory.TwSys.DelUTie Y := by
  intro i M _ hM
  obtain ⟨H', S, d, h1, h2, h3, h4⟩ := h i M hM
  refine ⟨H', S, fun P => delOf D.host X.cc (X.l i) M (pair D.host P), ⟨h1, h2, h3, fun P a b c => ?_⟩,
    fun Q hQ P hP σ => ?_⟩
  · exact isDel_delOf D.host X.cc (X.l i) ⟨d P, h4 P a b c⟩
  · rw [hY]
    exact (universal_anticyclotomic_character_laws D.host X.cc (X.l i)).2.2.2.2.2.2.1 Q M hQ P hP σ

end GlobalTheory.GalChar

end
end

