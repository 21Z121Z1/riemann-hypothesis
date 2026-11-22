import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2438
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2212
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2243
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2439
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2358

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallExtensionDualNumberFibreProductAffineMilnor
section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

open IsLocalRing in

theorem smallExt_fibre_ring : ∀ (C : Type) [CommRing C] [IsLocalRing C] (e : C), e ∈ IsLocalRing.maximalIdeal C → (∀ a ∈ IsLocalRing.maximalIdeal C, a * e = 0) → e ≠ 0 → ∃ (P : Type) (_ : CommRing P) (i : C →+* P) (p σ : P →+* C) (q : P →+* DualNumber (IsLocalRing.ResidueField C)), p.comp i = RingHom.id C ∧ σ.comp i = RingHom.id C ∧ q.comp i = (dnInl _).comp (IsLocalRing.residue C) ∧ IsClosedImmersion (spMap σ) ∧ Surjective (spMap σ) ∧ Milnor (spMap p) (spMap σ) (spMap (Ideal.Quotient.mk (Ideal.span {e}))) (spMap (Ideal.Quotient.mk (Ideal.span {e}))) ∧ Milnor (spMap p) (spMap q) (spMap (IsLocalRing.residue C)) (spMap (dnFst _)) := by
  intro C _ _ e he hm hne
  have hee : e * e = 0 := hm e he
  obtain ⟨φ, hφ⟩ : ∃ φ : ResidueField C →+ C, ∀ c, φ (residue C c) = c * e := by
    refine ⟨(Submodule.liftQ (maximalIdeal C) (LinearMap.toSpanSingleton C C e) ?_).toAddMonoidHom, fun c ↦ ?_⟩
    · intro a ha
      simpa using hm a ha
    · rfl
  have hφ0 : ∀ x, φ x = 0 → x = 0 := by
    intro x hx
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ] at hx
    rw [residue_eq_zero_iff]
    by_contra hc
    have hu : IsUnit c := by simpa using hc
    exact hne (hu.mul_right_eq_zero.mp hx)
  let P : Subring (C × DualNumber (ResidueField C)) :=
    RingHom.eqLocus ((residue C).comp (RingHom.fst _ _)) ((dnFst _).comp (RingHom.snd _ _))
  have hP : ∀ x : C × DualNumber (ResidueField C), x ∈ P ↔ residue C x.1 = x.2.fst := fun x ↦ Iff.rfl
  let p : P →+* C := (RingHom.fst _ _).comp P.subtype
  let q : P →+* DualNumber (ResidueField C) := (RingHom.snd _ _).comp P.subtype
  let i : C →+* P := RingHom.codRestrict ((RingHom.id C).prod ((dnInl _).comp (residue C))) P
    (fun c ↦ (hP _).2 rfl)
  let σ : P →+* C :=
    { toFun := fun x ↦ x.1.1 + φ x.1.2.snd
      map_one' := by simp
      map_zero' := by simp
      map_add' := by
        intro x y
        simp only [Subring.coe_add, Prod.fst_add, Prod.snd_add, TrivSqZeroExt.snd_add, map_add]
        ring
      map_mul' := by
        rintro ⟨⟨a, x⟩, hx⟩ ⟨⟨b, y⟩, hy⟩
        have hx' : residue C a = x.fst := hx
        have hy' : residue C b = y.fst := hy
        obtain ⟨c, hc⟩ := residue_surjective (R := C) x.snd
        obtain ⟨d, hd⟩ := residue_surjective (R := C) y.snd
        show a * b + φ (x * y).snd = (a + φ x.snd) * (b + φ y.snd)
        rw [DualNumber.snd_mul, ← hx', ← hy', ← hc, ← hd, ← map_mul, ← map_mul, ← map_add, hφ, hφ, hφ]
        linear_combination (-(c * d)) * hee }
  have hσ : ∀ x : P, σ x = x.1.1 + φ x.1.2.snd := fun _ ↦ rfl
  have hσi : σ.comp i = RingHom.id C := by
    ext c
    show c + φ (TrivSqZeroExt.inl (residue C c) : DualNumber _).snd = c
    simp
  have hsurj : Function.Surjective σ := fun c ↦ ⟨i c, RingHom.congr_fun hσi c⟩
  have hφmem : ∀ x, φ x ∈ Ideal.span {e} := by
    intro x
    obtain ⟨c, rfl⟩ := residue_surjective x
    rw [hφ]
    exact Ideal.mem_span_singleton'.2 ⟨c, rfl⟩
  have hker : RingHom.ker σ ≤ nilradical P := by
    rintro ⟨⟨a, x⟩, hx⟩ h
    have hx' : residue C a = x.fst := hx
    have h' : a + φ x.snd = 0 := h
    obtain ⟨c, hc⟩ := residue_surjective (R := C) x.snd
    rw [← hc, hφ] at h'
    have ha : a = -c * e := by linear_combination h'
    have h0 : x.fst = 0 := by
      rw [← hx', residue_eq_zero_iff, ha]
      exact Ideal.mul_mem_left _ _ he
    refine mem_nilradical.2 ⟨2, ?_⟩
    rw [pow_two]
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show a * a = 0
      rw [ha]
      linear_combination (c * c) * hee
    · show x * x = 0
      ext
      · simp [h0]
      · simp [DualNumber.snd_mul, h0]
  refine ⟨P, inferInstance, i, p, σ, q, rfl, hσi, rfl, ?_, ?_, ?_, ?_⟩
  · exact IsClosedImmersion.spec_of_surjective _ hsurj
  · refine ⟨fun x ↦ ?_⟩
    have := range_comap_of_surjective _ σ hsurj
    have hx : x ∈ PrimeSpectrum.zeroLocus (RingHom.ker σ : Set P) := fun a ha ↦
      @nilradical_le_prime _ _ x.asIdeal x.isPrime _ (hker ha)
    rw [← this] at hx
    exact hx
  · refine GlobalTheory.T.affineMilnorSquare_of_cartesian_ring_square _ _ _ _ _ _ _ _ ?_ ?_ ?_ Ideal.Quotient.mk_surjective
    · refine RingHom.ext fun x ↦ ?_
      refine (Ideal.Quotient.eq.2 ?_).symm
      show x.1.1 + φ x.1.2.snd - x.1.1 ∈ _
      simpa using hφmem _
    · rintro ⟨⟨a, x⟩, hx⟩ h1 h2
      have hx' : residue C a = x.fst := hx
      have h1' : a = 0 := h1
      have h2' : a + φ x.snd = 0 := h2
      subst h1'
      rw [zero_add] at h2'
      refine Subtype.ext (Prod.ext rfl ?_)
      show x = 0
      ext
      · simp [← hx']
      · simpa using hφ0 _ h2'
    · intro a b hab
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hab.symm)
      refine ⟨⟨(a, ⟨residue C a, residue C c⟩), rfl⟩, rfl, ?_⟩
      show a + φ (residue C c) = b
      rw [hφ, hc]
      ring
  · refine GlobalTheory.T.affineMilnorSquare_of_cartesian_ring_square _ _ _ _ _ _ _ _ ?_ ?_ ?_ (fun x ↦ ⟨TrivSqZeroExt.inl x, rfl⟩)
    · exact RingHom.ext fun x ↦ x.2
    · intro x h1 h2
      exact Subtype.ext (Prod.ext h1 h2)
    · intro a b hab
      exact ⟨⟨(a, b), hab⟩, rfl, rfl⟩

end GlobalTheory.DualOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftComparisonRelationsAddSmul
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm

section Ring

variable {R : Type} [CommRing R] {B : Type} [CommRing B] [Algebra R B] {J : Ideal B} {δ : DividedPowers J}

theorem divPowerCompatFunctionDifferential_smul (r : R) (b : B) : kd0 R δ (r • b) = r • kd0 R δ b := by
  rw [divPowerCompatFunctionDifferential_apply, divPowerCompatFunctionDifferential_apply, Derivation.map_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatOneFormDerivative_smul (r : R) (x : K1 R δ) : kd1 R δ (r • x) = r • kd1 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormDerivative_mk, divPowerCompatOneFormDerivative_mk, map_smul, Submodule.Quotient.mk_smul]

theorem divPowerCompatTwoFormDerivative_smul (r : R) (x : K R δ 2) : kd2 R δ (r • x) = r • kd2 R δ x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatTwoFormDerivative_mk, divPowerCompatTwoFormDerivative_mk, map_smul, Submodule.Quotient.mk_smul]

variable {R' B' : Type} [CommRing R'] [CommRing B'] [Algebra R' B'] {J' : Ideal B'} {δ' : DividedPowers J'}
  {σ : R →+* R'} {α : B →+* B'} (h : SemiHom σ α) (hd : IsDPMorphism δ δ' α)

theorem divPowerCompatOneFormMap_smul (r : R) (x : K1 R δ) : km1 h hd (r • x) = σ r • km1 h hd x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, divPowerCompatOneFormMap_mk, divPowerCompatOneFormMap_mk, map_smulₛₗ, Submodule.Quotient.mk_smul]

theorem km_smul (j : ℕ) (r : R) (x : K R δ j) : km h hd j (r • x) = σ r • km h hd j x := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Submodule.Quotient.mk_smul, km_mk, km_mk, map_smulₛₗ, Submodule.Quotient.mk_smul]

end Ring

section Site

variable {R : Type} [CommRing R] {I : Ideal R} {X : Scheme.{0}} {κ : DividedPowers I} {t : X ⟶ Sp R}

theorem crystallineCompatibleFormsComplex_functionMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M0.obj T) :
    (KK κ t).M0.map φ (r • x) = r • (KK κ t).M0.map φ x := map_smul (mp (O κ t) φ) r x

theorem crystallineCompatibleFormsComplex_oneFormMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M1.obj T) :
    (KK κ t).M1.map φ (r • x) = r • (KK κ t).M1.map φ x := divPowerCompatOneFormMap_smul (SemiHom.of_algHom φ.φ) φ.dp r x

theorem crystallineCompatibleFormsComplex_twoFormMap_smul {T T' : Thick κ t} (φ : T ⟶ T') (r : R) (x : (KK κ t).M2.obj T) :
    (KK κ t).M2.map φ (r • x) = r • (KK κ t).M2.map φ x := km_smul (SemiHom.of_algHom φ.φ) φ.dp 2 r x

theorem crystallineCompatibleFormsComplex_functionDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M0.obj T) :
    (KK κ t).d0 T (r • x) = r • (KK κ t).d0 T x := divPowerCompatFunctionDifferential_smul r x

theorem crystallineCompatibleFormsComplex_oneFormDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M1.obj T) :
    (KK κ t).d1 T (r • x) = r • (KK κ t).d1 T x := divPowerCompatOneFormDerivative_smul r x

theorem crystallineCompatibleFormsComplex_twoFormDifferential_smul (T : Thick κ t) (r : R) (x : (KK κ t).M2.obj T) :
    (KK κ t).d2 T (r • x) = r • (KK κ t).d2 T x := divPowerCompatTwoFormDerivative_smul r x

theorem crystallineCompatibleFormsComplex_totalDifferentialOne_smul (r : R) (c : (KK κ t).T1) : (KK κ t).D1 (r • c) = r • (KK κ t).D1 c := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ
    show (KK κ t).M0.map ψ (r • c.1 T T' φ) - r • c.1 T T'' (φ ≫ ψ) + r • c.1 T' T'' ψ =
      r • ((KK κ t).M0.map ψ (c.1 T T' φ) - c.1 T T'' (φ ≫ ψ) + c.1 T' T'' ψ)
    rw [crystallineCompatibleFormsComplex_functionMap_smul, smul_add, smul_sub]
  · funext T T' φ
    show r • c.2 T' - (KK κ t).M1.map φ (r • c.2 T) - (KK κ t).d0 T' (r • c.1 T T' φ) =
      r • (c.2 T' - (KK κ t).M1.map φ (c.2 T) - (KK κ t).d0 T' (c.1 T T' φ))
    rw [crystallineCompatibleFormsComplex_oneFormMap_smul, crystallineCompatibleFormsComplex_functionDifferential_smul, smul_sub, smul_sub]
  · funext T
    exact crystallineCompatibleFormsComplex_oneFormDifferential_smul T r (c.2 T)

theorem crystallineCompatibleFormsComplex_cocyclesOne_smul_mem (r : R) {c : (KK κ t).T1} (hc : c ∈ (KK κ t).Z1) : r • c ∈ (KK κ t).Z1 := by
  have h0 : (KK κ t).D1 c = 0 := hc
  show (KK κ t).D1 (r • c) = 0
  rw [crystallineCompatibleFormsComplex_totalDifferentialOne_smul, h0, smul_zero]

theorem crystallineCompatibleFormsComplex_cocyclesTwo_smul_mem (r : R) {c : (KK κ t).T2} (hc : c ∈ (KK κ t).Z2) : r • c ∈ (KK κ t).Z2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hc
  refine ⟨fun T T' T'' T''' φ ψ χ ↦ ?_, fun T T' T'' φ ψ ↦ ?_, fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · show (KK κ t).M0.map χ (r • c.1 T T' T'' φ ψ) + r • c.1 T T'' T''' (φ ≫ ψ) χ =
      r • c.1 T T' T''' φ (ψ ≫ χ) + r • c.1 T' T'' T''' ψ χ
    rw [crystallineCompatibleFormsComplex_functionMap_smul, ← smul_add, ← smul_add, h1]
  · show r • c.2.1 T T'' (φ ≫ ψ) = (KK κ t).M1.map ψ (r • c.2.1 T T' φ) + r • c.2.1 T' T'' ψ +
      (KK κ t).d0 T'' (r • c.1 T T' T'' φ ψ)
    rw [crystallineCompatibleFormsComplex_oneFormMap_smul, crystallineCompatibleFormsComplex_functionDifferential_smul, ← smul_add, ← smul_add, h2]
  · show r • c.2.2 T' = (KK κ t).M2.map φ (r • c.2.2 T) + (KK κ t).d1 T' (r • c.2.1 T T' φ)
    rw [crystallineCompatibleFormsComplex_twoFormMap_smul, crystallineCompatibleFormsComplex_oneFormDifferential_smul, ← smul_add, h3]
  · show (KK κ t).d2 T (r • c.2.2 T) = 0
    rw [crystallineCompatibleFormsComplex_twoFormDifferential_smul, h4, smul_zero]

end Site

theorem rel_add_smul : ∀ (D : Data) (Λ : Lift D),
    (∀ a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel1 (a + b) (h + h')) ∧
    (∀ (r : D.R) a h, Λ.Rel1 a h → Λ.Rel1 (r • a) (r • h)) ∧
    (∀ a b h h', Λ.Rel2 a h → Λ.Rel2 b h' → Λ.Rel2 (a + b) (h + h')) ∧
    ∀ (r : D.R) a h, Λ.Rel2 a h → Λ.Rel2 (r • a) (r • h) := by
  intro D Λ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro a b h h' ⟨k, f, w, hf, hw, hk, hr⟩ ⟨k', f', w', hf', hw', hk', hr'⟩
    refine ⟨k + k', f + f', w + w', by rw [map_add, hf, hf'], by rw [map_add, hw, hw'], ?_, ?_⟩
    · show k.1.1 + k'.1.1 = f.1 + f'.1
      rw [hk, hk']
    · refine ⟨fun U V c ↦ (congrArg₂ (· + ·) (hr.1 U V c) (hr'.1 U V c)).trans (map_add (Λ.e V) _ _).symm,
        fun U ↦ (congrArg₂ (· + ·) (hr.2 U) (hr'.2 U)).trans ?_⟩
      show _ = Submodule.Quotient.mk ((Λ.semi U).m1 (w.1.2 U + w'.1.2 U))
      rw [map_add, Submodule.Quotient.mk_add]
  · rintro r a h ⟨k, f, w, hf, hw, hk, hr⟩
    refine ⟨⟨r • k.1, crystallineCompatibleFormsComplex_cocyclesOne_smul_mem r k.2⟩, r • f, r • w, by rw [map_smul, hf], by rw [map_smul, hw], ?_, ?_⟩
    · show r • k.1.1 = r • f.1
      rw [hk]
    · refine ⟨fun U V c ↦ (congrArg (r • ·) (hr.1 U V c)).trans (map_smul (Λ.e V) r _).symm,
        fun U ↦ (congrArg (r • ·) (hr.2 U)).trans ?_⟩
      show _ = Submodule.Quotient.mk ((Λ.semi U).m1 (r • w.1.2 U))
      rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]
  · rintro a b h h' ⟨k, f, w, hf, hw, hk, hr⟩ ⟨k', f', w', hf', hw', hk', hr'⟩
    refine ⟨k + k', f + f', w + w', by rw [map_add, hf, hf'], by rw [map_add, hw, hw'], ?_, ?_⟩
    · show k.1.1 + k'.1.1 = f.1 + f'.1
      rw [hk, hk']
    · refine ⟨fun U V W c d ↦ (congrArg₂ (· + ·) (hr.1 U V W c d) (hr'.1 U V W c d)).trans (map_add (Λ.e W) _ _).symm,
        fun U V c ↦ (congrArg₂ (· + ·) (hr.2.1 U V c) (hr'.2.1 U V c)).trans ?_,
        fun U ↦ (congrArg₂ (· + ·) (hr.2.2 U) (hr'.2.2 U)).trans ?_⟩
      · show _ = Submodule.Quotient.mk ((Λ.semi V).m1 (w.1.2.1 U V c + w'.1.2.1 U V c))
        rw [map_add, Submodule.Quotient.mk_add]
      · show _ = Submodule.Quotient.mk ((Λ.semi U).mOm 2 (w.1.2.2 U + w'.1.2.2 U))
        rw [map_add, Submodule.Quotient.mk_add]
  · rintro r a h ⟨k, f, w, hf, hw, hk, hr⟩
    refine ⟨⟨r • k.1, crystallineCompatibleFormsComplex_cocyclesTwo_smul_mem r k.2⟩, r • f, r • w, by rw [map_smul, hf], by rw [map_smul, hw], ?_, ?_⟩
    · show r • k.1.1 = r • f.1
      rw [hk]
    · refine ⟨fun U V W c d ↦ (congrArg (r • ·) (hr.1 U V W c d)).trans (map_smul (Λ.e W) r _).symm,
        fun U V c ↦ (congrArg (r • ·) (hr.2.1 U V c)).trans ?_,
        fun U ↦ (congrArg (r • ·) (hr.2.2 U)).trans ?_⟩
      · show _ = Submodule.Quotient.mk ((Λ.semi V).m1 (r • w.1.2.1 U V c))
        rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]
      · show _ = Submodule.Quotient.mk ((Λ.semi U).mOm 2 (r • w.1.2.2 U))
        rw [map_smulₛₗ, RingHom.id_apply, Submodule.Quotient.mk_smul]

end GlobalTheory.PDForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfForallField
section
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)

namespace GlobalTheory.FibreDim

theorem smoothOfRelativeDimension_of_forall_field : ∀ (R : Type) [CommRing R] (X : Over (Sp R)) (g : ℕ), Smooth X.hom → (∀ (k : Type) [Field k] [Algebra R k], SmoothOfRelativeDimension g (Limits.pullback.snd X.hom (spMap (algebraMap R k)))) → SmoothOfRelativeDimension g X.hom := by
  intro R _ X g hs h
  choose n W hW hd using ReciprocityTheory.ChartRestriction.G.H1.exists_dim X.hom
  have hn : ∀ x, n x = g := fun x => by
    let p : PrimeSpectrum R := X.hom x
    have hk := h p.asIdeal.ResidueField
    let t := spMap (algebraMap R p.asIdeal.ResidueField)
    obtain ⟨y, hy⟩ : p ∈ Set.range (PrimeSpectrum.comap (algebraMap R p.asIdeal.ResidueField)) := by
      refine ⟨⟨⊥, Ideal.isPrime_bot⟩, PrimeSpectrum.ext ?_⟩
      exact Ideal.ker_algebraMap_residueField p.asIdeal
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} (n x)
    have h1 : SmoothOfRelativeDimension (n x) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) :=
      this.of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t) (hd x)
    have h2 : SmoothOfRelativeDimension (0 + (0 + g)) (Limits.pullback.snd ((W x).ι ≫ X.hom) t) := by
      rw [← Limits.pullbackRightPullbackFstIso_inv_snd_snd]
      infer_instance
    obtain ⟨z, -⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback ((W x).ι ≫ X.hom) t)
      ⟨x, hW x⟩ y hy.symm
    simpa using ReciprocityTheory.ChartRestriction.G.H1.dim_unique _ h1 h2 z
  have : IsZariskiLocalAtSource (@SmoothOfRelativeDimension g) := HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension g) W
    (top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, hW x⟩) fun x => ?_
  rw [← hn x]; exact hd x

end GlobalTheory.FibreDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothPresentationRelationsCombinationNormalStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothPresentation_relations_combination_normal : ∀ (R₀ : Type) [CommRing R₀] (n r : ℕ) (g : Fin r → MvPolynomial (Fin n) R₀) (a : Fin n → Fin r → MvPolynomial (Fin n) R₀) (b : Fin r → Fin r → Fin r → MvPolynomial (Fin n) R₀), (∀ j, MvPolynomial.aeval (fun i ↦ MvPolynomial.X i + ∑ k, a i k * g k) (g j) = ∑ k, ∑ l, b j k l * (g k * g l)) → (∀ j, g j + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * g k ∈ Ideal.span (Set.range g) ^ 2) ∧ ∀ j m, MvPolynomial.pderiv m (g j) + ∑ i, MvPolynomial.pderiv i (g j) * ∑ k, a i k * MvPolynomial.pderiv m (g k) ∈ Ideal.span (Set.range g) := by
  first | exact @GlobalTheory.SmoothRel.relations_combination | exact GlobalTheory.SmoothRel.relations_combination | (intros; apply GlobalTheory.SmoothRel.relations_combination <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSectionsMonoReductionAffineInf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.SmoothLift

theorem Data.sec_smooth (D : Data) (U : D.X.affineOpens) : Algebra.Smooth D.R (Sec D.s U.1) := by
  haveI := D.smooth
  have h := HasRingHomProperty.appLE @Smooth D.s ‹_› ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h' : RingHom.Smooth ((D.s.appLE ⊤ U.1 le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of D.R)).inv.hom) :=
    RingHom.Smooth.comp (RingHom.Smooth.of_bijective
      (Scheme.ΓSpecIso (CommRingCat.of D.R)).symm.commRingCatIsoToRingEquiv.bijective) h
  exact RingHom.smooth_algebraMap.mp h'

theorem Data.mono_i (D : Data) : Mono D.i := by
  obtain ⟨s₀, hpb, -⟩ := D.red
  haveI : IsClosedImmersion (spMap (Ideal.Quotient.mk D.I)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  haveI : IsClosedImmersion D.i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip ‹_›
  infer_instance

theorem Data.affine_inf (D : Data) {U V : D.X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) :
    IsAffineOpen (U ⊓ V) := by
  haveI := D.sep
  haveI : IsSeparated (Limits.terminal.from D.X) := by
    rw [← Limits.terminal.comp_from D.s]; infer_instance
  exact hU.inf hV

theorem Data.smooth_mono_inf : ∀ D : Data, (∀ U : D.X.affineOpens, Algebra.Smooth D.R (Sec D.s U.1)) ∧ Mono D.i ∧
    ∀ U V : D.X.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V) :=
  fun D ↦ ⟨D.sec_smooth, D.mono_i, fun _ _ hU hV ↦ D.affine_inf hU hV⟩

end GlobalTheory.SmoothLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncChartKltCriterion
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

namespace GlobalTheory.Discrepancy

theorem IsSncChart.neg_one_lt_formOrd_sub_sum : ∀ (k : Type) [Field k] [CharZero k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) [SmoothOfRelativeDimension n q] (B : Closeds Y) (y : Y) (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y) (u : Fin n → Y.functionFieldˣ), IsSncChart q n B y U hy z J w u → ∀ (E : DivOver q), E.Through y → ∀ a : Fin n → ℚ, ((∀ j ∈ J, a j < 1) → -1 < (E.formOrd (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) ∧ ((∀ j ∈ J, a j ≤ 1) → -1 ≤ (E.formOrd (formOf U (gen_mem hy) (dOn q z)) : ℚ) - ∑ j ∈ J, a j * E.ord (u j)) := by
  intro k _ _ Y _ _ q n _ B y U hy z J w u hc E hE a
  classical
  haveI := SmoothOfRelativeDimension.smooth n q
  have hn : topologicalKrullDim Y = n := by
    have hd (V : Y.Opens) (hV : IsAffineOpen V) (hne : (V : Set Y).Nonempty) :
        topologicalKrullDim (V : Set Y) = n := by
      rw [topologicalKrullDim_eq_of_isEmbedding hV.fromSpec.isOpenEmbedding.isEmbedding
        hV.range_fromSpec]
      exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := Γ(Y, V))).trans
        (SmoothDim.ringKrullDim_affineOpen k _ q _ inferInstance V hV hne)
    refine le_antisymm (topologicalKrullDim_le_of_forall_exists_isOpen fun x => ?_) ?_
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top x)
      exact ⟨V, V.isOpen, hx, (hd V hV ⟨x, hx⟩).le⟩
    · obtain ⟨V, hV, hx, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens
        (TopologicalSpace.Opens.mem_top y)
      exact (hd V hV ⟨_, hx⟩).ge.trans (topologicalKrullDim_subspace_le _ _)
  have h0 : formOf U (gen_mem hy) (dOn q z) ≠ 0 := fun h =>
    one_ne_zero ((isFreeGen_formOf (gen_mem hy) hc.frame).1 (a₁ := 1) (a₂ := 0) (by simp [h]))
  have hnn : ∀ j ∈ J, 0 ≤ E.ord (u j) := fun j hj =>
    (E.ord_nonneg_iff _).2 (by rw [hc.val j hj]; exact hE _ (regAt_fnOf hy _ (z j)))
  have hA := DivOver.sum_ord_sub_one_le_formOrd_dOn hn E hy hE z h0 (J := {j // j ∈ J})
    Subtype.val Subtype.val_injective (fun j => u j.1) fun j => hc.val j.1 j.2
  rw [Finset.sum_coe_sort J (fun j => E.ord (u j))] at hA
  have hF := DivOver.formOrd_formOf_nonneg hn hy hE (dOn q z) h0
  set F := E.formOrd (formOf U (gen_mem hy) (dOn q z))
  have hAq : ∑ j ∈ J, (E.ord (u j) : ℚ) - 1 ≤ F := by exact_mod_cast hA
  have hFq : (0 : ℚ) ≤ F := by exact_mod_cast hF
  have hnq : ∀ j ∈ J, (0 : ℚ) ≤ E.ord (u j) := fun j hj => by exact_mod_cast hnn j hj
  have hle : (∀ j ∈ J, a j ≤ 1) → ∀ j ∈ J, a j * (E.ord (u j) : ℚ) ≤ E.ord (u j) :=
    fun ha j hj => by nlinarith [ha j hj, hnq j hj]
  refine ⟨fun ha => ?_, fun ha => ?_⟩
  · by_cases hz : ∀ j ∈ J, (E.ord (u j) : ℚ) = 0
    · rw [Finset.sum_eq_zero fun j hj => by rw [hz j hj, mul_zero]]
      linarith
    · push Not at hz
      obtain ⟨j, hj, hj0⟩ := hz
      have hpos : (0 : ℚ) < E.ord (u j) := lt_of_le_of_ne (hnq j hj) hj0.symm
      have := Finset.sum_lt_sum (hle fun j hj => (ha j hj).le)
        ⟨j, hj, by nlinarith [ha j hj]⟩
      linarith
  · have := Finset.sum_le_sum (hle ha)
    linarith

end GlobalTheory.Discrepancy
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapFromSpecStalkTopLeIff
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory

theorem spMap_fromSpecStalk_le_preimage_iff (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω]
    (ψ : X.presheaf.stalk x →+* Ω) (hψ : IsLocalHom ψ) (O : X.Opens) :
    ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O := by
  constructor
  · intro h
    let p : ↥(Sp Ω) := closedPoint Ω
    have hm : (spMap ψ ≫ X.fromSpecStalk x) p ∈ O := h (x := p) trivial
    rw [Scheme.Hom.comp_apply] at hm
    have e : (spMap ψ) p = (closedPoint (X.presheaf.stalk x) : ↥(Spec (X.presheaf.stalk x))) := by
      show PrimeSpectrum.comap ψ (closedPoint Ω) = _
      exact IsLocalRing.comap_closedPoint ψ
    rw [e, Scheme.fromSpecStalk_closedPoint] at hm
    exact hm
  · intro hx w _
    have : X.fromSpecStalk x (spMap ψ w) ∈ Set.range (X.fromSpecStalk x) := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    show (spMap ψ ≫ X.fromSpecStalk x) w ∈ O
    rw [Scheme.Hom.comp_apply]
    exact Specializes.mem_open (x := X.fromSpecStalk x (spMap ψ w)) this O.isOpen hx

theorem spMap_fromSpecStalk_top_le_iff : ∀ (X : Scheme.{0}) (x : X) (Ω : Type) [CommRing Ω] [IsLocalRing Ω]
    (ψ : X.presheaf.stalk x →+* Ω), IsLocalHom ψ → ∀ O : X.Opens,
    ⊤ ≤ (spMap ψ ≫ X.fromSpecStalk x) ⁻¹ᵁ O ↔ x ∈ O :=
  fun X x Ω _ _ ψ hψ O => spMap_fromSpecStalk_le_preimage_iff X x Ω ψ hψ O

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanIInterSubmodulesOfFlatBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_iInter_submodules_of_flat_baseChange : ∀ (R R₁ K L : Type) [CommRing R] [CommRing R₁] [CommRing K] [CommRing L] [Algebra R R₁] [Algebra R K] [Module.Flat R R₁] (θ : K →+* L) (c : R₁ →+* L), (∀ a : R, θ (algebraMap R K a) = c (algebraMap R R₁ a)) → (∀ (n : ℕ) (u : Fin n → K) (r : Fin n → R₁), ∑ j, c (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0) → ∀ (J : Type) [Finite J] [Nonempty J] (N : J → Submodule R K), spanBy c (θ '' ⋂ j, (N j : Set K)) = ⋂ j, spanBy c (θ '' (N j : Set K)) := by
  first | exact @GlobalTheory.Desc.spanBy_iInter_of_flat | exact GlobalTheory.Desc.spanBy_iInter_of_flat | (intros; apply GlobalTheory.Desc.spanBy_iInter_of_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanImageInterOfFlatLinearlyDisjointStatement
section
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.span_image_inter_of_flat_linearlyDisjoint : ∀ (R R₁ F F₁ : Type) [CommRing R] [IsDomain R] [CommRing R₁] [Field F] [Field F₁] (ρ : R →+* R₁) (c₀ : R →+* F) (c₁ : R₁ →+* F₁) (θ : F →+* F₁), ρ.Flat → Function.Injective c₀ → θ.comp c₀ = c₁.comp ρ → LinDisj c₀ c₁ θ → ∀ (M N : Set F), (0 : F) ∈ M → (∀ a ∈ M, ∀ b ∈ M, a + b ∈ M) → (∀ r, ∀ a ∈ M, c₀ r * a ∈ M) → (0 : F) ∈ N → (∀ a ∈ N, ∀ b ∈ N, a + b ∈ N) → (∀ r, ∀ a ∈ N, c₀ r * a ∈ N) → spanBy c₁ (θ '' (M ∩ N)) = spanBy c₁ (θ '' M) ∩ spanBy c₁ (θ '' N) := by
  first | exact @GlobalTheory.Desc.spanBy_image_inter | exact GlobalTheory.Desc.spanBy_image_inter | (intros; apply GlobalTheory.Desc.spanBy_image_inter <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecFibreProductLocalArtinianGlueExistsUniqueStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.SmallGlue
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spec_fibreProduct_localArtinian_glue_existsUnique : ∀ (P B₁ B₂ B₀ : CommRingCat.{0}) (f₁ : P ⟶ B₁) (f₂ : P ⟶ B₂) (g₁ : B₁ ⟶ B₀) (g₂ : B₂ ⟶ B₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective f₁ → Function.Surjective f₂ → Nontrivial B₀ → ∀ (Z : Scheme.{0}) (a : Spec B₁ ⟶ Z) (b : Spec B₂ ⟶ Z), Spec.map g₁ ≫ a = Spec.map g₂ ≫ b → ∃! w : Spec P ⟶ Z, Spec.map f₁ ≫ w = a ∧ Spec.map f₂ ≫ w = b := by
  first | exact @GlobalTheory.spec_pullback_localArtinian_glue_existsUnique | exact GlobalTheory.spec_pullback_localArtinian_glue_existsUnique | (intros; apply GlobalTheory.spec_pullback_localArtinian_glue_existsUnique <;> assumption)
end

