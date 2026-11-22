import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1355
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1497
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0152
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0182
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Definitions.Divisors.LineOppositeParabolicUnitaryLeviSectionEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0375
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1403
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Formalism.PeriodIntegrals.CuspInfChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1503
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalTypes
section
noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut

namespace GlobalTheory.LeviGL

section Group

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {a : ℕ}

def lev (ι : GlobalTheory.CuspRep.GA E a →* GAd σ J) (U : Subgroup (GAd σ J)) (g : GAd σ J) :
    Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E)) :=
  U.comap ((MulAut.conj g⁻¹).toMonoidHom.comp (ι.comp (GlobalTheory.CuspRep.finGL E a)))

variable [IsTotallyComplex E]

def types {K : Subgroup (GAd σ J)} (W : Submodule ℂ (K → ℂ)) (ι : GlobalTheory.CuspRep.GA E a →* GAd σ J) (g : GAd σ J)
    (hK : ∀ κ : GlobalTheory.CuspRep.Kinf E a, g⁻¹ * ι (GlobalTheory.CuspRep.infGL E a (Unitary.toUnits κ)) * g ∈ K) :
    Submodule ℂ (GlobalTheory.CuspRep.Kinf E a → ℂ) :=
  W.map (LinearMap.funLeft ℂ ℂ fun κ => ⟨g⁻¹ * ι (GlobalTheory.CuspRep.infGL E a (Unitary.toUnits κ)) * g, hK κ⟩)

end Group

section Good

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def Good (L : Subgroup (GL (Fin a) (GlobalTheory.CuspRep.Af E))) (W₁ : Submodule ℂ (GlobalTheory.CuspRep.Kinf E a → ℂ))
    (ψ : GlobalTheory.CuspRep.Sm E a) : Prop :=
  GlobalTheory.CuspRep.IsAutForm ψ ∧ (∀ l ∈ L, GlobalTheory.CuspRep.finRep E a l ψ = ψ) ∧
    ∀ x, (fun κ : GlobalTheory.CuspRep.Kinf E a => (GlobalTheory.CuspRep.cptRep E a κ ψ).1 x) ∈ W₁

end Good

end GlobalTheory.LeviGL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEllipticCharpolyCompactSection
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FinChar

theorem norm_coeff_le_of_mem_ell (E : Type) [Field E] (n : ℕ) (P : E[X]) (hP : P ∈ Ell E n) (τ : E →+* ℂ) (k : ℕ) :
    ‖τ (P.coeff k)‖ ≤ (2 : ℝ) ^ n := by
  obtain ⟨hm, hd, -, hr⟩ := hP
  have h := Polynomial.coeff_le_of_roots_le (f := τ) (B := 1) k hm (IsAlgClosed.splits _) (fun z hz => (hr τ z hz).le)
  rw [Polynomial.coeff_map, one_pow, one_mul, hd] at h
  exact h.trans (by exact_mod_cast Nat.choose_le_two_pow n k)

theorem finite_ell_charpoly : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E)), IsSection S → ∀ C : ∀ w : Pl E, Set (GLw n w), (∀ w, IsCompact (C w)) → (∀ᶠ w in cofinite, C w ⊆ GlobalTheory.LFun.KGL w n) → {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P}.Finite := by
  intro E _ _ _ n S hS C hC hK
  set T := {P : E[X] | P ∈ Ell E n ∧ ∀ w ∈ S, ∃ g ∈ C w, g.val.charpoly = atPl w P} with hT
  choose σ hσ using fun w => (hS w).exists
  choose B hB using fun w => GlobalTheory.T.charpoly_coeffs_valued_bounded_on_compact_GL E n w (C w) (hC w)
  have loc : ∀ P ∈ T, ∀ u ∈ S, (∀ k, u.valuation E (P.coeff k) ≤ B u) ∧ u.valuation E (P.coeff 0)⁻¹ ≤ B u ∧
      (C u ⊆ GlobalTheory.LFun.KGL u n → (∀ k, u.valuation E (P.coeff k) ≤ 1) ∧ u.valuation E (P.coeff 0) = 1) := by
    intro P hP u hu
    obtain ⟨g, hg, hgP⟩ := hP.2 u hu
    have e : ∀ k, u.valuation E (P.coeff k) = Valued.v (g.val.charpoly.coeff k) := fun k => by
      rw [hgP, Polynomial.coeff_map]; exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).symm
    refine ⟨fun k => (e k).trans_le ((hB u g hg).1 k), ?_, fun hsub => ?_⟩
    · rw [map_inv₀, e, ← map_inv₀]; exact (hB u g hg).2
    · have := GlobalTheory.T.charpoly_integral_unit_constCoeff_of_mem_maxCompact E n u g (hsub hg)
      exact ⟨fun k => (e k).trans_le (this.1 k), (e 0).trans this.2⟩
  have glob : ∀ P ∈ T, ∀ w : Pl E, ∀ k, w.valuation E (P.coeff k) ≤ max (B (σ w)) (B (σ w) * B (σ w)) ∧
      (C (σ w) ⊆ GlobalTheory.LFun.KGL (σ w) n → w.valuation E (P.coeff k) ≤ 1) := by
    intro P hP w k
    have hu := loc P hP (σ w) (hσ w).1
    obtain ⟨h0, hc⟩ := GlobalTheory.T.elliptic_poly_conj_selfReciprocal_coeff E n P hP.1
    rcases GlobalTheory.T.valuation_eq_or_conj_of_under_maximalRealSubfield_eq E w (σ w) (hσ w).2 with h | h
    · rw [h]
      exact ⟨(hu.1 k).trans (le_max_left _ _), fun hs => (hu.2.2 hs).1 k⟩
    · rw [h]
      by_cases hk : k ≤ n
      · have e : IsCMField.complexConj E (P.coeff k) = P.coeff (n - k) * (P.coeff 0)⁻¹ := by
          rw [← hc k hk]; field_simp
        rw [e, map_mul]
        refine ⟨(mul_le_mul' (hu.1 _) hu.2.1).trans (le_max_right _ _), fun hs => ?_⟩
        rw [map_inv₀, (hu.2.2 hs).2, inv_one, mul_one]; exact (hu.2.2 hs).1 _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega), map_zero, map_zero]
        exact ⟨zero_le', fun _ => zero_le'⟩
  set A := {x : E | ∃ P ∈ T, ∃ k, P.coeff k = x} with hA
  have hAfin : A.Finite := by
    refine GlobalTheory.T.finite_of_bounded_embeddings_and_valuations E A ((2 : ℝ) ^ n) ?_ ?_ ?_
    · rintro _ ⟨P, hP, k, rfl⟩ τ; exact norm_coeff_le_of_mem_ell E n P hP.1 τ k
    · intro w; exact ⟨_, by rintro _ ⟨P, hP, k, rfl⟩; exact (glob P hP w k).1⟩
    · have hbad : {u : Pl E | ¬ C u ⊆ GlobalTheory.LFun.KGL u n}.Finite := Filter.eventually_cofinite.1 hK
      have : {w : Pl E | ¬ ∀ x ∈ A, w.valuation E x ≤ 1} ⊆ ⋃ u ∈ {u : Pl E | ¬ C u ⊆ GlobalTheory.LFun.KGL u n},
          {w : Pl E | w.under (𝓞 (maximalRealSubfield E)) = u.under (𝓞 (maximalRealSubfield E))} := by
        intro w hw
        simp only [Set.mem_setOf_eq, Set.mem_iUnion] at hw ⊢
        refine ⟨σ w, fun hs => hw ?_, (hσ w).2.symm⟩
        rintro _ ⟨P, hP, k, rfl⟩; exact (glob P hP w k).2 hs
      refine Filter.eventually_cofinite.2 (Set.Finite.subset (hbad.biUnion fun u _ => ?_) this)
      exact ((IsDedekindDomain.primesOver_finite (u.under (𝓞 (maximalRealSubfield E))).asIdeal (𝓞 E)).preimage
        (fun a _ b _ h => HeightOneSpectrum.ext h)).subset fun w hw => ⟨w.isPrime, ⟨(congrArg HeightOneSpectrum.asIdeal hw).symm⟩⟩
  refine Set.Finite.of_finite_image (f := fun P : E[X] => fun k : Fin (n + 1) => P.coeff k) ?_ ?_
  · refine (Set.Finite.pi (t := fun _ : Fin (n + 1) => A) fun _ => hAfin).subset ?_
    rintro _ ⟨P, hP, rfl⟩ k _
    exact ⟨P, hP, k, rfl⟩
  · intro P hP Q hQ h
    ext k
    by_cases hk : k ≤ n
    · exact congrFun h ⟨k, Nat.lt_succ_of_le hk⟩
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP.1.2.1]; omega),
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ.1.2.1]; omega)]

end GlobalTheory.FinChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteEtalePointOfExt
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.AlgClosedDescent

theorem finiteEtale_point_of_ext : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (X : Scheme.{0}) (p : X ⟶ Sp k₀), IsFinite p → Etale p → ∀ x : Sp K ⟶ X, x ≫ p = spMap (algebraMap k₀ K) → ∃ x₀ : Sp k₀ ⟶ X, x₀ ≫ p = 𝟙 _ ∧ spMap (algebraMap k₀ K) ≫ x₀ = x := GlobalTheory.T.exists_base_point_of_finite_etale_over_algClosed

theorem exists_spread_specialise : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B, IsMonHom f → ∃ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ ∧ IsMonHom f₀ ∧ GlobalTheory.Spread.bcMap B.hom R.val ≫ Ψ.left ≫ pullback.fst _ _ = f.left ≫ pullback.fst _ _ ∧ σ ≫ pullback.fst _ _ = 𝟙 _ ∧ σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom ∧ f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ := GlobalTheory.T.exists_abelian_endomorphism_spread_specialise

theorem torsion_section_comp_eq : ∀ (k₀ K : Type) [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K] (B : Over (Sp k₀)) [GrpObj B], IsAbelianScheme B → ∀ (R : Subalgebra k₀ K) (g : R →ₐ[k₀] k₀) (Ψ : (Over.pullback (spMap (algebraMap k₀ R))).obj B ⟶ (Over.pullback (spMap (algebraMap k₀ R))).obj B) (f₀ : B ⟶ B) (σ : B.left ⟶ pullback B.hom (spMap (algebraMap k₀ R))), IsMonHom Ψ → IsMonHom f₀ → σ ≫ pullback.fst _ _ = 𝟙 _ → σ ≫ pullback.snd _ _ = B.hom ≫ spMap g.toRingHom → f₀.left = σ ≫ Ψ.left ≫ pullback.fst _ _ → ∀ (N : ℕ), (N : k₀) ≠ 0 → ∀ y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ N = 1 → ∀ c : Sp R ⟶ pullback B.hom (spMap (algebraMap k₀ R)), c ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left → c ≫ pullback.snd _ _ = 𝟙 _ → c ≫ Ψ.left ≫ pullback.fst _ _ = spMap (algebraMap k₀ R) ≫ y₀.left ≫ f₀.left := GlobalTheory.T.spread_endomorphism_torsion_section_eq_specialisation

variable {k₀ K : Type} [Field k₀] [IsAlgClosed k₀] [Field K] [Algebra k₀ K]

theorem isUnit_natCast_gamma {k : Type} [Field k] {N : ℕ} (hN : (N : k) ≠ 0) :
    IsUnit (N : Γ(Sp k, ⊤)) := by
  have h : IsUnit (N : k) := hN.isUnit
  simpa using h.map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom

theorem torsion_descent (B : Over (Sp k₀)) [GrpObj B] (hB : IsAbelianScheme B) (N : ℕ)
    (hN : (N : k₀) ≠ 0) {t : Sp K ⟶ Sp k₀} (ht : t = spMap (algebraMap k₀ K))
    (u : Over.mk t ⟶ B) (hu : u ^ N = 1) :
    ∃ y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ N = 1 ∧ u.left = t ≫ y₀.left := by
  subst ht
  haveI : IsAbelianScheme B := hB
  obtain ⟨-, hfin, het⟩ := GrpTangent.finiteEtale_mulN_torsion B (isUnit_natCast_gamma hN)
  obtain ⟨x, hx, -⟩ := LatticeTorsion.existsUnique_torsion B N u hu
  obtain ⟨x₀, hx₀, hjx⟩ := finiteEtale_point_of_ext k₀ K _ (torsion B N).hom hfin het x.left (Over.w x)
  let y₀' : 𝟙_ (Over (Sp k₀)) ⟶ torsion B N := Over.homMk x₀ hx₀
  refine ⟨y₀' ≫ torsion.ι B N, ?_, ?_⟩
  · rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
  · rw [← hx, Over.comp_left, ← hjx, Over.comp_left, Category.assoc]
    rfl

theorem hom_eq_of_lTorsion {Ω : Type} [Field Ω] [IsAlgClosed Ω] {A : Over (Sp Ω)} [GrpObj A]
    (hA : IsAbelianScheme A) (F₁ F₂ : A ⟶ A) [IsMonHom F₁] [IsMonHom F₂] {l : ℕ} (hl : l.Prime)
    (hlk : (l : Ω) ≠ 0)
    (h : ∀ (y : 𝟙_ (Over (Sp Ω)) ⟶ A) (a : ℕ), y ^ (l ^ a) = 1 → y ≫ F₁ = y ≫ F₂) : F₁ = F₂ := by
  have := hA.comm
  have hS := isSemiAbelian_of_isAbelianScheme A hA
  have hm : IsMonHom (F₁ * F₂⁻¹) :=
    { one_hom := by
        rw [MonObj.comp_mul, GrpObj.comp_inv, IsMonHom.one_hom, IsMonHom.one_hom, mul_inv_cancel,
          one_eq_one]
      mul_hom := by
        have e (z : A ⊗ A ⟶ A) : z ≫ (F₁ * F₂⁻¹) = z ≫ F₁ * (z ≫ F₂)⁻¹ := by
          rw [MonObj.comp_mul, GrpObj.comp_inv]
        rw [mul_eq_mul, e, MonObj.mul_comp, MonObj.mul_comp, MonObj.comp_mul,
          tensorHom_fst, tensorHom_snd, e, e, mul_inv, _root_.mul_mul_mul_comm] }
  have h1 := GlobalTheory.TorsionDense.eq_one_of_torsion_comp_eq_one Ω A A hS hS l hl hlk (F₁ * F₂⁻¹) hm
    (fun _ _ y a hy ↦ by
      rw [MonObj.comp_mul, GrpObj.comp_inv]
      exact mul_inv_eq_one.mpr (h y a hy))
  exact mul_inv_eq_one.mp h1

theorem exists_prime_ne_zero (k : Type) [Field k] : ∃ l : ℕ, l.Prime ∧ (l : k) ≠ 0 := by
  obtain ⟨p, hp⟩ := CharP.exists k
  by_cases h2 : p = 2
  · subst h2
    refine ⟨3, Nat.prime_three, fun h3 ↦ ?_⟩
    have := (CharP.cast_eq_zero_iff k 2 3).mp (by exact_mod_cast h3)
    omega
  · refine ⟨2, Nat.prime_two, fun h3 ↦ ?_⟩
    have h4 := (CharP.cast_eq_zero_iff k p 2).mp (by exact_mod_cast h3)
    rcases (Nat.dvd_prime Nat.prime_two).mp h4 with h5 | h5
    · exact CharP.char_ne_one k p h5
    · exact h2 h5

theorem endo_descent (B : Over (Sp k₀)) [GrpObj B] (hB : IsAbelianScheme B)
    (f : (Over.pullback (spMap (algebraMap k₀ K))).obj B ⟶
      (Over.pullback (spMap (algebraMap k₀ K))).obj B) (hf : IsMonHom f) :
    ∃! f₀ : B ⟶ B, IsMonHom f₀ ∧ (Over.pullback (spMap (algebraMap k₀ K))).map f₀ = f := by
  obtain ⟨R, g, Ψ, f₀, σ, hΨ, hf₀, hbc, hσ₁, hσ₂, hf₀σ⟩ := exists_spread_specialise k₀ K B hB f hf
  have key : (Over.pullback (spMap (algebraMap k₀ K))).map f₀ = f := by
    let Ω := AlgebraicClosure K
    let qΩ : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
    letI : Algebra k₀ Ω := ((algebraMap K Ω).comp (algebraMap k₀ K)).toAlgebra
    have hιj : qΩ ≫ spMap (algebraMap k₀ K) = spMap (algebraMap k₀ Ω) := by
      simp only [qΩ, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      try rfl
    haveI := hf₀
    haveI := hΨ
    apply ActDescent.pullback_map_injective qΩ
    have hBK := isAbelianScheme_overPullback (spMap (algebraMap k₀ K)) B hB
    have hA := isAbelianScheme_overPullback qΩ _ hBK
    obtain ⟨l, hl, hlk⟩ := exists_prime_ne_zero k₀
    have hlΩ : (l : Ω) ≠ 0 := by
      intro h
      apply hlk
      apply (algebraMap k₀ Ω).injective
      rw [map_natCast, h, map_zero]
    refine hom_eq_of_lTorsion hA _ _ hl hlΩ fun y a hy => ?_
    have h₁ := isGrpPullback_pullback B (spMap (algebraMap k₀ K))
    have h₂ := isGrpPullback_pullback ((Over.pullback (spMap (algebraMap k₀ K))).obj B) qΩ
    have h₁₂ := h₂.comp h₁
    let u := pushHom h₁₂ (𝟙_ _) y
    have hu : u ^ (l ^ a) = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨y₀, hy₀, huy⟩ := torsion_descent (K := Ω) B hB (l ^ a)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlk)
      (t := (𝟙_ (Over (Sp Ω))).hom ≫ qΩ ≫ spMap (algebraMap k₀ K))
      (by rw [hιj]; exact Category.id_comp _) u hu
    have hu' : y.left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) =
        qΩ ≫ spMap (algebraMap k₀ K) ≫ y₀.left := by
      have e : u.left = y.left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) := rfl
      rw [← e, huy]
      simp
    have hy0 : y₀.left ≫ B.hom = 𝟙 _ := Over.w y₀
    let w : Sp K ⟶ pullback B.hom (spMap (algebraMap k₀ K)) :=
      pullback.lift (spMap (algebraMap k₀ K) ≫ y₀.left) (𝟙 _)
        (by rw [Category.assoc, hy0]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
    have e2 : y.left ≫ pullback.snd (pullback.snd B.hom (spMap (algebraMap k₀ K))) qΩ = 𝟙 _ := Over.w y
    have hv : y.left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ = qΩ ≫ w := by
      apply pullback.hom_ext
      · rw [Category.assoc, hu', Category.assoc, pullback.lift_fst]
      · rw [Category.assoc, Category.assoc, pullback.lift_snd, Category.comp_id]
        have e1 : pullback.fst (pullback.snd B.hom (spMap (algebraMap k₀ K))) qΩ ≫
            pullback.snd B.hom (spMap (algebraMap k₀ K)) =
            pullback.snd (pullback.snd B.hom (spMap (algebraMap k₀ K))) qΩ ≫ qΩ := pullback.condition
        erw [e1]
        rw [← Category.assoc, e2, Category.id_comp]
    let c : Sp R ⟶ pullback B.hom (spMap (algebraMap k₀ R)) :=
      pullback.lift (spMap (algebraMap k₀ R) ≫ y₀.left) (𝟙 _)
        (by rw [Category.assoc, hy0]; exact (Category.comp_id _).trans (Category.id_comp _).symm)
    have hwc : w ≫ Spread.bcMap B.hom R.val = spMap R.val.toRingHom ≫ c := by
      apply pullback.hom_ext
      · rw [Category.assoc, Spread.bcMap_fst, pullback.lift_fst, Category.assoc, pullback.lift_fst,
          ← Category.assoc, Spread.spMap_algHom_comp]
      · rw [Category.assoc, Spread.bcMap_snd, pullback.lift_snd_assoc, Category.assoc, pullback.lift_snd,
          Category.id_comp, Category.comp_id]
    have hC := torsion_section_comp_eq k₀ K B hB R g Ψ f₀ σ hΨ hf₀ hσ₁ hσ₂ hf₀σ (l ^ a)
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ hlk) y₀ hy₀ c (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _)
    have m1 : ((Over.pullback qΩ).map ((Over.pullback (spMap (algebraMap k₀ K))).map f₀)).left ≫
        pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ = pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ ((Over.pullback (spMap (algebraMap k₀ K))).map f₀).left :=
      ActDescent.pullback_map_left_fst _
    have m3 : ((Over.pullback (spMap (algebraMap k₀ K))).map f₀).left ≫
        pullback.fst B.hom (spMap (algebraMap k₀ K)) = pullback.fst B.hom (spMap (algebraMap k₀ K)) ≫ f₀.left :=
      ActDescent.pullback_map_left_fst _
    have m4 : ((Over.pullback qΩ).map f).left ≫ pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ = pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ f.left :=
      ActDescent.pullback_map_left_fst _
    have hL : y.left ≫ ((Over.pullback qΩ).map ((Over.pullback (spMap (algebraMap k₀ K))).map f₀)).left ≫
        pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) =
        qΩ ≫ spMap (algebraMap k₀ K) ≫ y₀.left ≫ f₀.left := by
      rw [reassoc_of% m1, m3, reassoc_of% hu']
    have hR : y.left ≫ ((Over.pullback qΩ).map f).left ≫
        pullback.fst ((Over.pullback (spMap (algebraMap k₀ K))).obj B).hom qΩ ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) =
        qΩ ≫ spMap (algebraMap k₀ K) ≫ y₀.left ≫ f₀.left := by
      rw [reassoc_of% m4, ← hbc]
      erw [reassoc_of% hv]
      rw [reassoc_of% hwc, hC, ← Spread.spMap_algHom_comp R.val]
      simp only [Category.assoc]
    apply Over.OverMorphism.ext
    apply h₁₂.1.hom_ext
    · simp only [Over.comp_left, Category.assoc]
      exact hL.trans hR.symm
    · simp only [Over.comp_left, Category.assoc, Over.w]

  exact ⟨f₀, ⟨hf₀, key⟩, fun f₁ hf₁ =>
    ActDescent.pullback_map_injective (spMap (algebraMap k₀ K)) B B (hf₁.2.trans key.symm)⟩

theorem point_descent (B : Over (Sp k₀)) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ)
    (hn : (n : k₀) ≠ 0) (y : 𝟙_ (Over (Sp K)) ⟶ (Over.pullback (spMap (algebraMap k₀ K))).obj B)
    (z₀ : 𝟙_ (Over (Sp k₀)) ⟶ B)
    (hz : (y ^ n).left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) = spMap (algebraMap k₀ K) ≫ z₀.left) :
    ∃! y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B, y₀ ^ n = z₀ ∧
      y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) = spMap (algebraMap k₀ K) ≫ y₀.left := by
  have := hB.comm
  have := hB.smooth
  have := hB.proper
  have hnu := isUnit_natCast_gamma hn
  have := GrpTangent.isFinite_mulN B hnu
  have := GrpTangent.etale_mulN B hnu
  have h₁ := isGrpPullback_pullback B (spMap (algebraMap k₀ K))
  have hw : (y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K))) ≫ (mulN B n).left =
      spMap (algebraMap k₀ K) ≫ z₀.left := by
    have e1 : (pushHom h₁ (𝟙_ _) y ≫ mulN B n) = pushHom h₁ (𝟙_ _) (y ^ n) := by
      rw [GrpTangent.comp_mulN, map_pow]
    have e2 := congrArg (fun z => z.left) e1
    simp only [Over.comp_left] at e2
    exact e2.trans hz
  let x : Sp K ⟶ pullback (mulN B n).left z₀.left :=
    pullback.lift (y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K))) (spMap (algebraMap k₀ K)) hw
  obtain ⟨x₀, hx₀, hjx⟩ := finiteEtale_point_of_ext k₀ K _ (pullback.snd (mulN B n).left z₀.left) inferInstance inferInstance x
    (pullback.lift_snd _ _ _)
  have hz0 : z₀.left ≫ B.hom = 𝟙 _ := Over.w z₀
  have hfB : pullback.fst (mulN B n).left z₀.left ≫ B.hom = pullback.snd (mulN B n).left z₀.left := by
    rw [← Over.w (mulN B n), ← Category.assoc, pullback.condition, Category.assoc, hz0, Category.comp_id]
  let y₀ : 𝟙_ (Over (Sp k₀)) ⟶ B := Over.homMk (x₀ ≫ pullback.fst _ _)
    (by rw [Category.assoc, hfB, hx₀]; rfl)
  have hepi : Epi (spMap (algebraMap k₀ K)) := Flat.epi_of_flat_of_surjective _
  have hy₀ : y.left ≫ pullback.fst B.hom (spMap (algebraMap k₀ K)) = spMap (algebraMap k₀ K) ≫ y₀.left := by
    change _ = spMap (algebraMap k₀ K) ≫ x₀ ≫ pullback.fst _ _
    rw [← Category.assoc, hjx, pullback.lift_fst]
  refine ⟨y₀, ⟨?_, hy₀⟩, fun y₁ hy₁ => ?_⟩
  · rw [← GrpTangent.comp_mulN]
    apply Over.OverMorphism.ext
    change (x₀ ≫ pullback.fst _ _) ≫ (mulN B n).left = z₀.left
    rw [Category.assoc, pullback.condition, ← Category.assoc, hx₀, Category.id_comp]
  · apply Over.OverMorphism.ext
    rw [← cancel_epi (spMap (algebraMap k₀ K)), ← hy₁.2, hy₀]

end GlobalTheory.AlgClosedDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankCoinvariantInducedIsoStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_rank_coinvariant_induced_iso : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (n d : ℕ) (ν : kˣ →* ℂˣ), n ≤ d → GlobalTheory.SmGL.IsSmoothChar ν →
    ∃ Z : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] (GL (Fin d) k → ℂ),
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ ∈ GlobalTheory.FullRankCoinv.indSp k n d ν) ∧
      (∀ f ∈ GlobalTheory.FullRankCoinv.indSp k n d ν, ∃ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = f) ∧
      (∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, Z Ψ = 0 → Ψ ∈ GlobalTheory.FullRankCoinv.augRk n d ν) ∧
      ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d, ∀ h₀ : GL (Fin d) k,
        Z (fun Y => Ψ (Y * h₀.1)) = fun h => Z Ψ (h * h₀) := by
  first | exact @GlobalTheory.FullRankCoinv.fibre_coinvariants | exact GlobalTheory.FullRankCoinv.fibre_coinvariants | (intros; apply GlobalTheory.FullRankCoinv.fibre_coinvariants <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GelfandKazhdanDualOfHyps
section
open NumberField IsDedekindDomain Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory.GelfandKazhdanTop

theorem gelfandKazhdanDual_of_rapidDecay : GlobalTheory.Published.JacquetShalika → GlobalTheory.Published.AutomorphicFormsFiniteGL →
    GlobalTheory.Published.CuspRapidDecaySiegelGL → GlobalTheory.Published.GelfandKazhdanDual := by
  intro hJS hAF hRD E _ _ _ n π
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact GlobalTheory.Published.InvTransposeModel.rank_zero π
  · obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_twist_cuspidal_trivial_on_splitCentre E n hn π
    have hp := GlobalTheory.T.cusp_rep_paired_with_itself hJS.1 (GlobalTheory.CuspBoundSiegel.cuspFormsBounded_of_rapidDecay hRD) hAF E n hn (π.twist χ) hχ
    have h := GlobalTheory.Published.InvTransposeModel.twist hp χ⁻¹
    rwa [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one] at h

end GlobalTheory.GelfandKazhdanTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Gl2LocalToAdelicEmbedding
section
noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.StdPar
open Formalism.UG (cT)
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.GLTwoHecke

section Matrices

variable {R : Type} [CommRing R]

def dg (a b : Rˣ) : GL (Fin 2) R :=
  ⟨!![(a : R), 0; 0, (b : R)], !![((a⁻¹ : Rˣ) : R), 0; 0, ((b⁻¹ : Rˣ) : R)],
    by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

def up (b : R) : GL (Fin 2) R :=
  ⟨!![1, b; 0, 1], !![1, -b; 0, 1], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

variable (R) in

def wy : GL (Fin 2) R :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

@[simp] theorem dg_val (a b : Rˣ) : (dg a b).1 = !![(a : R), 0; 0, (b : R)] := rfl
@[simp] theorem up_val (b : R) : (up b).1 = !![1, b; 0, 1] := rfl
@[simp] theorem wy_val : (wy R).1 = !![0, 1; 1, 0] := rfl

end Matrices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def twoCols {n r : ℕ} (h1 : 1 < r) (C : Matrix (Fin n) (Fin r) E) : Matrix (Fin n) (Fin 2) E :=
  C.submatrix id (Fin.castLE h1)

variable (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

def IsBlockEmb (X Y : Matrix (Fin n) (Fin r) E) (h1 : 1 < r) (j : GL (Fin 2) (AF F ⊗[F] E) →* GAd σ J) : Prop :=
  Continuous j ∧ ∀ h : GL (Fin 2) (AF F ⊗[F] E),
    (matHom _ σ J (j h)).1 * adMat F (twoCols h1 X) = adMat F (twoCols h1 X) * h.1 ∧
    (matHom _ σ J (j h)).1 * adMat F (twoCols h1 Y) = adMat F (twoCols h1 Y) * cT (sigR (AF F) σ) (h⁻¹).1 ∧
    ∀ z ∈ colPerp σ J X {i | i.val < 2} ⊓ colPerp σ J Y {i | i.val < 2}, (matHom _ σ J (j h)).1 *ᵥ z = z

def singleNU (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →ₙ+* FiniteAdeleRing (𝓞 E) E where
  toFun := singleFin w
  map_mul' := singleFin_mul w
  map_zero' := map_zero _
  map_add' := map_add _

variable (F) in

def locNU (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →ₙ+* AF F ⊗[F] E :=
  (GlobalTheory.LFun.extZero F E).comp (((GlobalTheory.LFun.finAdEquiv F E).symm : _ →+* _).toNonUnitalRingHom.comp (singleNU w))

variable (F) in

def gl2_local_to_adelic_embedding (w : HeightOneSpectrum (𝓞 E)) : GL (Fin 2) (w.adicCompletion E) →* GL (Fin 2) (AF F ⊗[F] E) :=
  PI.CuspInfChar.emb (locNU F w)

def qChr (χ : (AF F ⊗[F] E)ˣ →* Circle) (z : ℝ) (t : (AF F ⊗[F] E)ˣ) : ℂ :=
  (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ)

end GlobalTheory.GLTwoHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePolynomialsOfCarriedEigensystemStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram SphOp hyp)
open GlobalTheory.StdFrame (StdPsi)
attribute [local instance] Formalism.IndefR.principalLevelFrame.instCMHostI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePolynomials_of_carried_eigensystem : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ p c, R.Carries p c → ∀ P ∈ A3.A.ok A3.A.μ0, RealDat.polE (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (dualLab (splitLab D.R.r k))) ∧ RealDat.polW (A := A3.A) p.1.1 P = Formalism.L2.Col.heckePolyOf D.R.r (A3.A.q P) (fun k => c (R.pl P) (splitLab D.R.r k)) := by
  first | exact @GlobalTheory.CarriedHecke.hecke_polys_of_carries | exact GlobalTheory.CarriedHecke.hecke_polys_of_carries | (intros; apply GlobalTheory.CarriedHecke.hecke_polys_of_carries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianPosDefSimultaneousNormalFormStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_posDef_simultaneous_normal_form : ∀ {n : ℕ} {J P : Matrix (Fin n) (Fin n) ℂ}, J.IsHermitian → J.det ≠ 0 → P.IsHermitian →
    (∀ x : Fin n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ P *ᵥ x).re) →
    ∃ (ε : Fin n → Bool) (Q : GL (Fin n) ℂ), Q.1ᴴ * J * Q.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      ∀ g : Matrix (Fin n) (Fin n) ℂ, gᴴ * P * g = P → gᴴ * J * g = J →
        ((Q⁻¹).1 * g * Q.1)ᴴ * ((Q⁻¹).1 * g * Q.1) = 1 := by
  first | exact @GlobalTheory.SimNormal.simultaneous_normal_form | exact GlobalTheory.SimNormal.simultaneous_normal_form | (intros; apply GlobalTheory.SimNormal.simultaneous_normal_form <;> assumption)
end

