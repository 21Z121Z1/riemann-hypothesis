import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0001
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Bundle0002
import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.InfUnram
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaInfl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ImageConj

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.Formula
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem vFormula_of_classicalTheorems (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hc : PTCase F l) (D : LData F Ω l) (e : ℤ) :
    VLen D e + KStar.TotallyRealRoots.nuGal l F e.natAbs = shaLen D e + sumLocalH0TwistLength D e := by
  have hfl := fun r (hr : 0 < r) => GlobalTheory.TateLimit.finite_level D e hP hc r hr
  have hcok := GlobalTheory.TateLimit.ptCokerAt D e hF hT (fun r hr => (hfl r hr).1)
    (fun r hr => (hfl r hr).2.1) (hfl 1 one_pos).2.2
  have hsha := GlobalTheory.TateLimit.ptShaAt D e hF hT (fun r hr => (hfl r hr).1)
    (fun r hr => (hfl r hr).2.1) (hfl 1 one_pos).2.2
  have h := vFormula F Ω l D e hc hcok hsha (GlobalTheory.TateLimit.local_tate_duality_h2_limit hF hT D e)
  rwa [length_H0_global_eq_nu] at h

theorem ptCase_of_isTotallyComplex (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (l : ℕ) : PTCase F l :=
  Or.inr (NumberField.nrRealPlaces_eq_zero_iff.2 inferInstance)

theorem VLen_le_shaLen_add (hP : GlobalTheory.Published.PoitouTateDuality) (hF : LocalFinitenessK) (hT : LocalTateDualityK)
    (hc : PTCase F l) (D : LData F Ω l) (e : ℤ) : VLen D e ≤ shaLen D e + sumLocalH0TwistLength D e := by
  rw [← vFormula_of_classicalTheorems hP hF hT hc]
  exact le_self_add

end

end UpperTheory.V.LDataCardLeFinrank

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.LengthH0GlobalEqLevelGroup
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {N : ℕ} [NeZero N] {K : Type} [Field K] [NumberField K] [IsCyclotomicExtension {N} ℚ K] (φ : F →ₐ[ℚ] K)

section

variable {l : ℕ} [Fact l.Prime] {v : HeightOneSpectrum (𝓞 F)} {A : ValuationSubring Ω}

include φ

theorem princ_le_ineImage (hv : v ∈ Above F l) (hA : IsPlaceOver A v) :
    KStar.TotallyRealRoots.princ l (N.factorization l) ≤ ineImage F l A :=
  (KStar.TotallyRealRoots.princ_le_levelGroup N _).1.trans (levelLeIne F Ω N K φ l v A hv hA)

end

include φ

end

end UpperTheory.V.LDataCardLeFinrank

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaLenEqShaInv
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem map_Sha (D : LData F Ω l) (e : ℤ) :
    (Sha D e).map (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) =
      ShaAbs ((qzTw D e).comp (toGS Ω _)) (Above F l) := by
  rw [← D.hS]
  exact shaInfl F Ω D.S D.A D.hA _ _ _ (contTw F Ω l D e).1

theorem injective_infl (D : LData F Ω l) (e : ℤ) :
    Function.Injective (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) :=
  (infUnram F Ω _ _ _ _ (contTw F Ω l D e).1).1

theorem shaLen_eq_abs (D : LData F Ω l) (e : ℤ) :
    shaLen D e = Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) := by
  rw [← qzTw_comp_toGS D e, ← map_Sha]
  exact (Submodule.equivMapOfInjective _ (injective_infl D e) _).length_eq

variable {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω']

theorem length_ShaAbs_le (f : F ≃+* F') (e : ℤ) :
    Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) ≤
      Module.length ℤ_[l] (ShaAbs (qzG F' Ω' l e) (Above F' l)) := by
  let σ : Ω ≃+* Ω' := IsAlgClosure.equivOfEquiv Ω Ω' f
  have hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f.toRingHom x) :=
    fun x => IsAlgClosure.equivOfEquiv_algebraMap Ω Ω' f x
  obtain ⟨φ, h1, h2, h3, -, h5⟩ := galTransport F Ω F' Ω' f.toRingHom σ hσ
  have e1 : (qzG F Ω l e).comp φ = qzG F' Ω' l e := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    rw [MonoidHom.comp_apply, qzG_apply, qzG_apply, h3]
  rw [← e1]
  refine (shaAbsRes F Ω F' Ω' _ _ φ h1 (fun v' A' hA' => ?_) _ _ _).2 (h5 f.surjective)
  obtain ⟨v, A, a, b, -, c, d⟩ := placeTransport F Ω F' Ω' f.toRingHom σ hσ φ h2 v' A' hA'
  exact ⟨v, A, a, b l, fun g hg => (c g).2 hg, fun g hg => (d g).2 hg⟩

theorem shaLen_congr (f : F ≃+* F') (D : LData F Ω l) (D' : LData F' Ω' l) (e : ℤ) : shaLen D e = shaLen D' e := by
  rw [shaLen_eq_abs, shaLen_eq_abs]
  exact le_antisymm (length_ShaAbs_le f e) (length_ShaAbs_le f.symm e)

theorem shaLen_eq_shaInv (D : LData F Ω l) (e : ℤ) : shaLen D e = shaInv F l e := by
  rw [shaLen_eq_abs]
  exact le_antisymm (length_ShaAbs_le (RingEquiv.refl F) e) (length_ShaAbs_le (RingEquiv.refl F) e)

theorem shaInv_congr (f : F ≃+* F') (e : ℤ) : shaInv F l e = shaInv F' l e :=
  le_antisymm (length_ShaAbs_le f e) (length_ShaAbs_le f.symm e)

end

theorem indep : Indep := fun F Ω _ _ _ _ _ l _ D D' e => by
  refine ⟨shaLen_congr (RingEquiv.refl F) D D' e, (vLenIndep F Ω l D D' e).2, ?_⟩
  have hS := (vLenIndep F Ω l D D' e).1
  rw [local_H0_length_eq_sum, local_H0_length_eq_sum]
  refine Fintype.sum_equiv (Equiv.subtypeEquivRight fun v => by rw [hS]) _ _ fun v => ?_
  rw [(imageConj F Ω l v.1 _ _ (D.hA v) (D'.hA ⟨v.1, hS ▸ v.2⟩)).1]
  rfl

theorem vvle_iff_shaInv (E : Type) [Field E] [NumberField E] (t : ℕ) (B : ℝ) :
    UpperTheory.Top.VVle E t B ↔
      (∀ (p : ℕ) [Fact p.Prime] (e : ℕ), 0 < e → e < t → shaInv E p (e : ℤ) ≠ ⊤) ∧
      ∀ S : Finset Nat.Primes, ∑ l ∈ S, Real.log (l : ℕ) *
        ∑ e ∈ Finset.Ico 1 t, ((@shaInv E _ _ l ⟨l.2⟩ (e : ℤ)).toNat : ℝ) ≤ B := by
  constructor
  · intro h
    have := h (AlgebraicClosure E) fun p _ => (ldata_nonempty p).some
    simpa only [shaLen_eq_shaInv] using this
  · intro h Ω _ _ _ ld
    simpa only [shaLen_eq_shaInv] using h

theorem vvle_congr {E E' : Type} [Field E] [NumberField E] [Field E'] [NumberField E'] (f : E ≃+* E') (t : ℕ) (B : ℝ) :
    UpperTheory.Top.VVle E t B ↔ UpperTheory.Top.VVle E' t B := by
  simp only [vvle_iff_shaInv, shaInv_congr f]

end UpperTheory.V.LDataCardLeFinrank

end
end

