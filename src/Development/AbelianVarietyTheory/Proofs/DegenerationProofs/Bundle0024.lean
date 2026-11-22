import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLocalizationOfLeClosure
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.CycAway
open NumberField

theorem isLocalization_of_le_closure {Ω : Type} [Field Ω] {n : ℕ} (h0 : (n : Ω) ≠ 0) (A : Type) [CommRing A]
    (T : Subring Ω) [Algebra A T] (hinj : Function.Injective (algebraMap A T)) (hinv : (n : Ω)⁻¹ ∈ T)
    (hT : T ≤ Subring.closure ({x | ∃ a, x = (algebraMap A T a : Ω)} ∪ {(n : Ω)⁻¹})) :
    IsLocalization (Submonoid.powers (n : A)) T := by
  have key : ∀ z ∈ Subring.closure ({x | ∃ a, x = (algebraMap A T a : Ω)} ∪ {(n : Ω)⁻¹}),
      ∃ m : ℕ, ∃ a, z * (n : Ω) ^ m = (algebraMap A T a : Ω) := by
    intro z hz
    induction hz using Subring.closure_induction with
    | mem x hx =>
      rcases hx with ⟨a, rfl⟩ | rfl
      · exact ⟨0, a, by simp⟩
      · exact ⟨1, 1, by simp [h0]⟩
    | zero => exact ⟨0, 0, by simp⟩
    | one => exact ⟨0, 1, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨m, a, ha⟩ := hx
      obtain ⟨k, b, hb⟩ := hy
      refine ⟨m + k, a * n ^ k + b * n ^ m, ?_⟩
      simp only [map_add, map_mul, map_pow, map_natCast]
      push_cast
      rw [← ha, ← hb]; ring
    | neg x _ hx =>
      obtain ⟨m, a, ha⟩ := hx
      refine ⟨m, -a, ?_⟩
      simp only [map_neg]
      push_cast
      rw [← ha]; ring
    | mul x y _ _ hx hy =>
      obtain ⟨m, a, ha⟩ := hx
      obtain ⟨k, b, hb⟩ := hy
      refine ⟨m + k, a * b, ?_⟩
      simp only [map_mul]
      push_cast
      rw [← ha, ← hb]; ring
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, m, rfl⟩
    simp only [map_pow, map_natCast]
    refine IsUnit.pow _ (IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_))
    simp [h0]
  · intro z
    obtain ⟨m, a, ha⟩ := key z (hT z.2)
    refine ⟨(a, ⟨_, m, rfl⟩), Subtype.ext ?_⟩
    simp only [map_pow, map_natCast]
    push_cast
    exact ha
  · intro x y h
    exact ⟨1, by rw [hinj h]⟩

theorem dedekind_closure {Ω K : Type} [Field Ω] [CharZero Ω] [Field K] [CharZero K] {n a : ℕ} (hn : n.Prime)
    [IsCyclotomicExtension {n ^ a} ℚ K] (φ : K →+* Ω) {ζ : K} (hζ : IsPrimitiveRoot ζ (n ^ a)) :
    IsDedekindDomain (Subring.closure {φ ζ, (n : Ω)⁻¹}) ∧ Algebra.FiniteType ℤ (Subring.closure {φ ζ, (n : Ω)⁻¹}) := by
  haveI := Fact.mk hn
  haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  let io : 𝓞 K →+* Ω := φ.comp (algebraMap _ K)
  have hio : Function.Injective io := φ.injective.comp RingOfIntegers.coe_injective
  have hmem : ∀ x, io x ∈ T := by
    intro x
    obtain ⟨y, hy⟩ := (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton_of_prime_pow hζ).isIntegral_iff.1
      (RingOfIntegers.isIntegral_coe x)
    have h1 : (y : K) ∈ Subring.closure ({ζ} : Set K) := by
      exact Algebra.mem_adjoin_iff.1 y.2 |> fun h => (Subring.closure_le.2 (by
        rintro _ (⟨r, rfl⟩ | h)
        · exact intCast_mem (Subring.closure ({ζ} : Set K)) r
        · exact Subring.subset_closure h)) h
    have h2 : Subring.closure ({ζ} : Set K) ≤ T.comap φ := by
      rw [Subring.closure_le]
      rintro _ rfl
      exact Subring.subset_closure (Or.inl rfl)
    have h3 : io x = φ y := congrArg φ hy.symm
    rw [h3]
    exact h2 h1
  letI : Algebra (𝓞 K) T := (io.codRestrict _ hmem).toAlgebra
  have hL : IsLocalization (Submonoid.powers (n : 𝓞 K)) T := by
    refine isLocalization_of_le_closure h0 _ _ (fun x y h => hio (congrArg (fun z : T => (z : Ω)) h))
      (Subring.subset_closure (Or.inr rfl)) (Subring.closure_mono ?_)
    rintro x (rfl | h)
    · exact Or.inl ⟨hζ.toInteger, rfl⟩
    · exact Or.inr h
  have hn' : (n : 𝓞 K) ≠ 0 := by exact_mod_cast hn.ne_zero
  refine ⟨IsLocalization.isDedekindDomain _ (powers_le_nonZeroDivisors_of_noZeroDivisors hn') _, ?_⟩
  have h1 : Algebra.FiniteType ℤ (𝓞 K) := inferInstance
  have h2 : Algebra.FiniteType (𝓞 K) T :=
    have := IsLocalization.Away.finitePresentation (S := T) (n : 𝓞 K)
    inferInstance
  exact h1.trans h2

theorem exists_base : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (n a : ℕ), n.Prime → ∃ (o : Subring Ω) (ze : oˣ), IsDedekindDomain o ∧ Algebra.FiniteType ℤ o ∧ IsUnit (n : o) ∧ IsPrimitiveRoot (Units.map o.subtype.toMonoidHom ze) (n ^ a) ∧ o = Subring.closure {((ze : o) : Ω), (n : Ω)⁻¹} := by
  intro Ω _ _ _ n a hn
  haveI := Fact.mk hn
  have h0 : (n : Ω) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne_zero
  let K := CyclotomicField (n ^ a) ℚ
  haveI : IsCyclotomicExtension {n ^ a} ℚ K := CyclotomicField.isCyclotomicExtension (n ^ a) ℚ
  haveI : NumberField K := IsCyclotomicExtension.numberField {n ^ a} ℚ _
  let φ : K →+* Ω := (IsAlgClosed.lift (R := ℚ) (S := K) (M := Ω)).toRingHom
  have hζ := IsCyclotomicExtension.zeta_spec (n ^ a) ℚ K
  set ζ := IsCyclotomicExtension.zeta (n ^ a) ℚ K
  obtain ⟨hD, hF⟩ := dedekind_closure hn φ hζ
  set T : Subring Ω := Subring.closure {φ ζ, (n : Ω)⁻¹} with hTdef
  have hz : IsPrimitiveRoot (φ ζ) (n ^ a) := hζ.map_of_injective φ.injective
  let z : T := ⟨φ ζ, Subring.subset_closure (Or.inl rfl)⟩
  have hz' : IsPrimitiveRoot z (n ^ a) := IsPrimitiveRoot.of_map_of_injective (f := T.subtype) hz T.subtype_injective
  have hu : IsUnit z := hz'.isUnit (NeZero.ne _)
  refine ⟨T, hu.unit, hD, hF, ?_, ?_, ?_⟩
  · refine IsUnit.of_mul_eq_one ⟨_, Subring.subset_closure (Or.inr rfl)⟩ (Subtype.ext ?_)
    simp [h0]
  · rw [← IsPrimitiveRoot.coe_units_iff]
    exact hz
  · rfl

end GlobalTheory.CycAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsNilpotentSubOneOfConjPow
section
namespace GlobalTheory

namespace Unipotence

open Polynomial

theorem pow_card_eq_zero {K n : Type} [Field K] [IsAlgClosed K] [Fintype n] [DecidableEq n]
    (Y : Matrix n n K) (h : ∀ μ ∈ spectrum K Y, μ = 0) : IsNilpotent Y := by
  have hm := Y.charpoly_monic
  have hs : Y.charpoly.Splits := IsAlgClosed.splits _
  have hr : Y.charpoly.roots = Multiset.replicate (Multiset.card Y.charpoly.roots) 0 := by
    rw [Multiset.eq_replicate_card]
    intro μ hμ
    exact h μ (Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (isRoot_of_mem_roots hμ))
  have he := hs.eq_prod_roots_of_monic hm
  rw [hr] at he
  have hch := Matrix.aeval_self_charpoly Y
  rw [he] at hch
  refine ⟨Multiset.card Y.charpoly.roots, ?_⟩
  simpa using hch

theorem root_of_unity {K n : Type} [Field K] [Fintype n] [DecidableEq n]
    (A : Matrix n n K) (hA : IsUnit A) (P : (Matrix n n K)ˣ) (q : ℕ) (hq : 2 ≤ q)
    (h : (P : Matrix n n K) * A = A ^ q * P) (x : K) (hx : x ∈ spectrum K A) :
    ∃ m : ℕ, m ≠ 0 ∧ x ^ m = 1 := by
  have hconj : A ^ q = P * A * (P⁻¹ : (Matrix n n K)ˣ) := by
    rw [h, mul_assoc, Units.mul_inv, mul_one]
  have hstep : ∀ y ∈ spectrum K A, y ^ q ∈ spectrum K A := by
    intro y hy
    have := spectrum.pow_mem_pow A q hy
    rwa [hconj, spectrum.units_conjugate] at this
  have hall : ∀ k : ℕ, x ^ (q ^ k) ∈ spectrum K A := by
    intro k
    induction k with
    | zero => simpa using hx
    | succ k ih => rw [pow_succ, pow_mul]; exact hstep _ ih
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact (spectrum.zero_mem_iff K).mp hx hA
  obtain ⟨i, j, hij, he⟩ := (Matrix.finite_spectrum A).exists_lt_map_eq_of_forall_mem hall
  have hlt : q ^ i < q ^ j := Nat.pow_lt_pow_right (by omega) hij
  refine ⟨q ^ j - q ^ i, by omega, ?_⟩
  apply mul_left_cancel₀ (pow_ne_zero (q ^ i) hx0)
  rw [← pow_add, mul_one, Nat.add_sub_cancel' hlt.le]
  exact he.symm

theorem eq_zero_of_integral (l : ℕ) [hl : Fact l.Prime] (h3 : 3 ≤ l) {K : Type} [Field K] [CharZero K]
    [Algebra ℤ_[l] K] (μ : K) (hμ : IsIntegral ℤ_[l] μ) (m : ℕ) (hm : m ≠ 0)
    (h : (1 + l • μ) ^ m = 1) : μ = 0 := by
  let E := Algebra.adjoin ℤ_[l] ({μ} : Set K)
  haveI : Module.Finite ℤ_[l] E := Module.Finite.iff_fg.mpr hμ.fg_adjoin_singleton
  let ψ : E := ⟨μ, Algebra.self_mem_adjoin_singleton _ _⟩
  have hl0 : l ≠ 0 := by omega
  have key : (1 : E) + l • ψ = 1 := by
    refine SerreTorsion.eq_one_of_pow (E := E) (q := l) (c := l) ?_ hl.out ?_ hl0 dvd_rfl
      (fun h2 => by omega) m hm ψ ?_
    · intro n x hn hx
      have : (n : K) * (x : K) = 0 := by
        have := congrArg (Subtype.val : E → K) hx
        simpa using this
      exact Subtype.ext ((mul_eq_zero.mp this).resolve_left (Nat.cast_ne_zero.mpr hn))
    · intro x hx
      have hk := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (R := ℤ_[l]) (M := E)
        (IsLocalRing.maximalIdeal ℤ_[l]) (IsLocalRing.maximalIdeal.isMaximal _).ne_top
      rw [← Submodule.mem_bot ℤ_[l], ← hk, Submodule.mem_iInf]
      intro k
      obtain ⟨y, hy⟩ := hx k
      rw [hy, ← Nat.cast_smul_eq_nsmul ℤ_[l], Nat.cast_pow]
      refine Submodule.smul_mem_smul (Ideal.pow_mem_pow ?_ k) Submodule.mem_top
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    · apply Subtype.ext
      simpa [ψ] using h
  have := congrArg (Subtype.val : E → K) key
  simpa [ψ, hl0] using this

theorem matrix_nilpotent (l : ℕ) [hl : Fact l.Prime] (h3 : 3 ≤ l) {n : Type} [Fintype n]
    [DecidableEq n] (Y P : Matrix n n ℤ_[l]) (hA : IsUnit (1 + l • Y)) (hP : IsUnit P)
    (q : ℕ) (hq : 2 ≤ q) (h : P * (1 + l • Y) = (1 + l • Y) ^ q * P) : IsNilpotent Y := by
  let K := AlgebraicClosure ℚ_[l]
  have hinj : Function.Injective (algebraMap ℤ_[l] K) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  let f : Matrix n n ℤ_[l] →+* Matrix n n K := (algebraMap ℤ_[l] K).mapMatrix
  have hf : Function.Injective f := Matrix.map_injective hinj
  rw [← IsNilpotent.map_iff hf]
  apply pow_card_eq_zero
  intro μ hμ
  have hint : IsIntegral ℤ_[l] μ := by
    refine ⟨Y.charpoly, Y.charpoly_monic, ?_⟩
    have := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hμ
    rw [show f Y = Y.map (algebraMap ℤ_[l] K) from rfl, Matrix.charpoly_map] at this
    rw [← Polynomial.eval_map]
    exact this
  have hspec : 1 + l • μ ∈ spectrum K (f (1 + l • Y)) := by
    have := spectrum.subset_polynomial_aeval (f Y) (1 + l • (X : K[X])) ⟨μ, hμ, rfl⟩
    simpa using this
  obtain ⟨m, hm, hx⟩ := root_of_unity (f (1 + l • Y)) (hA.map f) (hP.map f).unit q hq
    (by rw [IsUnit.unit_spec, ← map_mul, h, map_mul, map_pow]) _ hspec
  exact eq_zero_of_integral l h3 μ hint m hm hx

end Unipotence

theorem isNilpotent_sub_one_of_conj_pow :
    ∀ (l : ℕ) [Fact l.Prime], 3 ≤ l → ∀ (T : Type) [AddCommGroup T] [Module ℤ_[l] T] [Module.Free ℤ_[l] T] [Module.Finite ℤ_[l] T] (S Φ : T ≃ₗ[ℤ_[l]] T) (q : ℕ), 2 ≤ q → Φ * S = S ^ q * Φ → (∀ x, ∃ y, S x - x = l • y) → IsNilpotent ((S : T →ₗ[ℤ_[l]] T) - 1) := by
  intro l _ h3 T _ _ _ _ S Φ q hq h hS
  classical
  let b := Module.Free.chooseBasis ℤ_[l] T
  choose y hy using hS
  let Y : Module.End ℤ_[l] T := b.constr ℤ_[l] (fun i => y (b i))
  have hSY : (S : T →ₗ[ℤ_[l]] T) = 1 + l • Y := by
    apply b.ext
    intro i
    simp only [Y, LinearMap.add_apply, LinearMap.smul_apply, Module.Basis.constr_basis,
      Module.End.one_apply, LinearEquiv.coe_coe, ← hy]
    abel
  let g : (T ≃ₗ[ℤ_[l]] T) →* Module.End ℤ_[l] T := LinearEquiv.automorphismGroup.toLinearMapMonoidHom
  have hgS : g S = 1 + l • Y := hSY
  let e := LinearMap.toMatrixAlgEquiv b
  have heS : e (g S) = 1 + l • e Y := by rw [hgS, map_add, map_one, map_nsmul]
  have hN : IsNilpotent (e Y) := by
    refine Unipotence.matrix_nilpotent l h3 (e Y) (e (g Φ)) ?_ (((Group.isUnit Φ).map g).map e) q hq ?_
    · rw [← heS]; exact ((Group.isUnit S).map g).map e
    · rw [← heS, ← map_mul, ← map_mul, h, map_mul, map_mul, map_pow, map_pow]
  rw [IsNilpotent.map_iff (f := e) e.injective] at hN
  rw [hSY, add_sub_cancel_left]
  exact hN.smul l

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsOpenImmersionOfSections
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.CompatCrit

theorem section_open {G X V : Scheme.{0}} [IsReduced G] (p : G ⟶ X) [IsSeparated p] (s : V ⟶ G)
    [IsDominant s] [IsOpenImmersion (s ≫ p)] :
    IsOpenImmersion s ∧ ∀ x : G, p x ∈ Set.range (s ≫ p) → x ∈ Set.range s := by
  let t : V ⟶ pullback p (s ≫ p) := pullback.lift s (𝟙 V) (by simp)
  have h1 : t ≫ pullback.fst p (s ≫ p) = s := pullback.lift_fst _ _ _
  have h2 : t ≫ pullback.snd p (s ≫ p) = 𝟙 V := pullback.lift_snd _ _ _
  have : IsClosedImmersion (t ≫ pullback.snd p (s ≫ p)) := by rw [h2]; infer_instance
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t (pullback.snd p (s ≫ p))
  have : IsDominant (t ≫ pullback.fst p (s ≫ p)) := by rw [h1]; infer_instance
  have : IsDominant t := IsDominant.of_comp_of_isOpenImmersion t (pullback.fst p (s ≫ p))
  have : Surjective t := surjective_of_isDominant_of_isClosed_range t t.isClosedEmbedding.isClosed_range
  have : IsReduced (pullback p (s ≫ p)) := isReduced_of_isOpenImmersion (pullback.fst p (s ≫ p))
  have : IsIso t := isIso_of_isClosedImmersion_of_surjective t
  refine ⟨by rw [← h1]; infer_instance, fun x hx => ?_⟩
  have hx' : x ∈ Set.range (pullback.fst p (s ≫ p)) := by
    rw [Scheme.Pullback.range_fst]; exact hx
  obtain ⟨y, rfl⟩ := hx'
  obtain ⟨v, rfl⟩ := t.surjective y
  exact ⟨v, by rw [← Scheme.Hom.comp_apply, h1]⟩

theorem isOpenImmersion_of_sections {G X : Scheme.{0}} [IsReduced G] (p : G ⟶ X) [IsSeparated p]
    (h : ∀ x : G, ∃ (V : Scheme.{0}) (s : V ⟶ G), IsDominant s ∧ IsOpenImmersion (s ≫ p) ∧ x ∈ Set.range s) :
    IsOpenImmersion p := by
  refine IsOpenImmersion.of_forall_source_exists p (fun x y hxy => ?_) (fun x => ?_)
  · obtain ⟨V, s, _, _, u, rfl⟩ := h x
    obtain ⟨v, rfl⟩ := (section_open p s).2 y ⟨u, by rw [← hxy, Scheme.Hom.comp_apply]⟩
    have : u = v := (s ≫ p).isOpenEmbedding.injective (by simpa using hxy)
    rw [this]
  · obtain ⟨V, s, _, _, hx⟩ := h x
    exact ⟨V, s, (section_open p s).1, hx, inferInstance⟩

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {A : Over (Sp K)}

theorem isPullback_j (M : Model R A) : IsPullback M.j A.hom M.Y.hom (spMap (algebraMap R K)) := by
  have : IsIso M.e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map M.e.inv))
  have h : IsPullback M.e.inv.left A.hom (pullback.snd M.Y.hom (spMap (algebraMap R K))) (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simpa using Over.w M.e.inv⟩
  simpa [Model.j] using h.paste_horiz (IsPullback.of_hasPullback M.Y.hom (spMap (algebraMap R K)))

theorem exists_model (M : Model R A) {G : Scheme.{0}} (p : G ⟶ M.Y.left) [IsOpenImmersion p]
    [QuasiCompact p] (i : A.left ⟶ G) (hi : i ≫ p = M.j) :
    ∃ e : (Over.pullback (spMap (algebraMap R K))).obj (Over.mk (p ≫ M.Y.hom)) ≅ A,
      e.inv.left ≫ pullback.fst (p ≫ M.Y.hom) (spMap (algebraMap R K)) = i := by
  have h : IsPullback i (𝟙 _) p M.j := IsPullback.of_vert_isIso_mono ⟨by simp [hi]⟩
  have h' := h.paste_vert (isPullback_j M)
  rw [Category.id_comp] at h'
  exact ⟨(Over.isoMk h'.isoPullback (by simp)).symm, by simp⟩

theorem mem_range_j [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K] (M : Model R A)
    (y : M.Y.left) (hy : y ∉ M.sp) : y ∈ Set.range M.j := by
  have h1 : (M.Y.hom y : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap R K)) := by
    rw [PrimeSpectrum.localization_comap_range K (nonZeroDivisors R)]
    have hb : (M.Y.hom y : PrimeSpectrum R).asIdeal = ⊥ := by
      by_contra hb
      exact hy (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal
        ((M.Y.hom y : PrimeSpectrum R).isPrime.isMaximal hb)))
    show Disjoint _ _
    rw [hb, Set.disjoint_left]
    intro a ha ha'
    exact nonZeroDivisors.ne_zero ha ha'
  obtain ⟨t, ht⟩ := h1
  obtain ⟨a, ha, -⟩ := Scheme.exists_preimage_of_isPullback (isPullback_j M) y t ht.symm
  exact ⟨a, ha⟩

end GlobalTheory.SS.CompatCrit

namespace GlobalTheory.SS
open CompatCrit

theorem compat_of_isoAt_closure : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [IsIntegral A.left] (M N : Model R A) (δ : A.left ⟶ (M.Y ⊗ N.Y).left), δ ≫ (fst M.Y N.Y).left = M.j → δ ≫ (snd M.Y N.Y).left = N.j → (∀ z ∈ closure (Set.range δ), IsClosed {z} → (fst M.Y N.Y).left z ∈ M.sp → IsoAt M N (𝟙 A) ((fst M.Y N.Y).left z)) → Compat M N := by
  intro R K _ _ _ _ _ ⟨hD, _, _, hF⟩ A _ M N δ h₁ h₂ H
  have := M.smooth; have := M.sep; have := M.qc; have := N.smooth; have := N.sep; have := N.qc
  have : IsOpenImmersion (spMap (algebraMap R K)) := isOpenImmersion_spMap_of_isDiscreteValuationRing R K
  have : IsSchemeTheoreticallyDominant (spMap (algebraMap R K)) :=
    (schemeDominant_specMap_iff _).2 (IsFractionRing.injective R K)
  have jM : IsOpenImmersion M.j := MorphismProperty.of_isPullback (isPullback_j M).flip ‹_›
  have jN : IsOpenImmersion N.j := MorphismProperty.of_isPullback (isPullback_j N).flip ‹_›
  have qM : QuasiCompact M.j := MorphismProperty.of_isPullback (P := @QuasiCompact) (isPullback_j M).flip inferInstance
  have dM : IsSchemeTheoreticallyDominant M.j := .of_isPullback (isPullback_j M).flip
  have s₁ : IsSeparated (fst M.Y N.Y).left := inferInstanceAs (IsSeparated (pullback.fst M.Y.hom N.Y.hom))
  have s₂ : IsSeparated (snd M.Y N.Y).left := inferInstanceAs (IsSeparated (pullback.snd M.Y.hom N.Y.hom))
  have c₁ : QuasiCompact (fst M.Y N.Y).left := inferInstanceAs (QuasiCompact (pullback.fst M.Y.hom N.Y.hom))
  have : QuasiCompact (δ ≫ (fst M.Y N.Y).left) := by rw [h₁]; infer_instance
  have qδ : QuasiCompact δ := QuasiCompact.of_comp δ (fst M.Y N.Y).left
  have : IsReduced δ.image := IsSchemeTheoreticallyDominant.isReduced δ.toImage
  let p := δ.imageι ≫ (fst M.Y N.Y).left
  let q := δ.imageι ≫ (snd M.Y N.Y).left
  have hp : δ.toImage ≫ p = M.j := (δ.toImage_imageι_assoc _).trans h₁
  have hq : δ.toImage ≫ q = N.j := (δ.toImage_imageι_assoc _).trans h₂
  have : CompactSpace M.Y.left := QuasiCompact.compactSpace_of_compactSpace M.Y.hom
  have : CompactSpace δ.image := QuasiCompact.compactSpace_of_compactSpace p
  let S : Set δ.image := {x | ∃ (V : Scheme.{0}) (s : V ⟶ δ.image), IsDominant s ∧ IsOpenImmersion (s ≫ p) ∧
    IsOpenImmersion (s ≫ q) ∧ x ∈ Set.range s}
  have hSo : IsOpen S := by
    refine isOpen_iff_forall_mem_open.2 ?_
    rintro x ⟨V, s, a, b, c, hx⟩
    have := (section_open p s).1
    exact ⟨Set.range s, fun y hy => ⟨V, s, a, b, c, hy⟩, s.isOpenEmbedding.isOpen_range, hx⟩
  have hS : ∀ x, x ∈ S := by
    by_contra hne
    obtain ⟨x, hx, hc⟩ := hSo.isClosed_compl.exists_closed_singleton (not_forall.1 hne)
    apply hx
    by_cases hsp : p x ∈ M.sp
    · have hz : δ.imageι x ∈ closure (Set.range δ) := by
        have h := image_closure_subset_closure_image δ.imageι.continuous
          ⟨x, δ.toImage.denseRange x, rfl⟩
        refine closure_mono ?_ h
        rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
        exact ⟨a, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.toImage_imageι]⟩
      have hcz : IsClosed {δ.imageι x} := by
        simpa using δ.imageι.isClosedEmbedding.isClosedMap _ hc
      obtain ⟨U, g, hU, ⟨e₁, e₂⟩, hg⟩ := H _ hz hcz hsp
      let t : U.toScheme ⟶ (M.Y ⊗ N.Y).left := pullback.lift U.ι g e₁.symm
      have t₁ : t ≫ (fst M.Y N.Y).left = U.ι := pullback.lift_fst _ _ _
      have t₂ : t ≫ (snd M.Y N.Y).left = g := pullback.lift_snd _ _ _
      have : IsSchemeTheoreticallyDominant (M.j ∣_ U) := .of_isPullback (isPullback_morphismRestrict M.j U).flip
      have hw : (M.j ∣_ U) ≫ t = (M.j ⁻¹ᵁ U).ι ≫ δ := by
        refine pullback.hom_ext ?_ ?_
        · change ((M.j ∣_ U) ≫ t) ≫ (fst M.Y N.Y).left = (_ ≫ δ) ≫ (fst M.Y N.Y).left
          rw [Category.assoc, Category.assoc, t₁, h₁, morphismRestrict_ι]
        · change ((M.j ∣_ U) ≫ t) ≫ (snd M.Y N.Y).left = (_ ≫ δ) ≫ (snd M.Y N.Y).left
          rw [Category.assoc, Category.assoc, t₂, h₂, e₂]; simp
      let s := closureLift δ t (M.j ∣_ U) _ hw
      have sp : s ≫ p = U.ι := (closureLift_imageι_assoc δ t _ _ hw _).trans t₁
      have sq : s ≫ q = g := (closureLift_imageι_assoc δ t _ _ hw _).trans t₂
      have : IsDominant (M.j ⁻¹ᵁ U).ι := ⟨by
        rw [DenseRange, Scheme.Opens.range_ι]
        refine (M.j ⁻¹ᵁ U).isOpen.dense ?_
        obtain ⟨a, ha⟩ := M.j.denseRange.exists_mem_open U.isOpen ⟨_, hU⟩
        exact ⟨a, ha⟩⟩
      have : IsDominant ((M.j ∣_ U) ≫ s) := by
        simp only [s, comp_closureLift]; infer_instance
      have ds : IsDominant s := IsDominant.of_comp (M.j ∣_ U) s
      have op : IsOpenImmersion (s ≫ p) := by rw [sp]; infer_instance
      refine ⟨_, s, ds, op, by rw [sq]; exact hg, (section_open p s).2 x ?_⟩
      rw [sp, Scheme.Opens.range_ι]
      exact hU
    · have op : IsOpenImmersion (δ.toImage ≫ p) := by rw [hp]; exact jM
      refine ⟨_, δ.toImage, inferInstance, op, by rw [hq]; exact jN, (section_open p _).2 x ?_⟩
      rw [hp]
      exact mem_range_j M _ hsp
  have op : IsOpenImmersion p := isOpenImmersion_of_sections p fun x => by
    obtain ⟨V, s, a, b, -, hx⟩ := hS x
    exact ⟨V, s, a, b, hx⟩
  have oq : IsOpenImmersion q := isOpenImmersion_of_sections q fun x => by
    obtain ⟨V, s, a, -, c, hx⟩ := hS x
    exact ⟨V, s, a, c, hx⟩
  obtain ⟨e, he⟩ := exists_model M p δ.toImage hp
  let W : Model R A := ⟨Over.mk (p ≫ M.Y.hom), e, inferInstanceAs (Smooth (p ≫ M.Y.hom)),
    inferInstanceAs (IsSeparated (p ≫ M.Y.hom)), inferInstanceAs (QuasiCompact (p ≫ M.Y.hom))⟩
  have hW : W.j = δ.toImage := he
  let i : W.Y ⟶ M.Y ⊗ N.Y := Over.homMk δ.imageι (by simp [W, p])
  refine ⟨W, i ≫ fst _ _, i ≫ snd _ _, op, oq, ?_, ?_, ?_⟩
  · rw [hW]; exact hp
  · rw [hW]; exact hq
  · rw [lift_comp_fst_snd]
    exact inferInstanceAs (IsClosedImmersion δ.imageι)

end GlobalTheory.SS
end

