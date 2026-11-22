import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HDiscAE
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsPowSmulMemBall
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsIntegralIffMemSpanOneTmulIntegralClosure
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemIntegralClosureOfMemSpan
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AlgebraicCurves.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0014
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAdmissible
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteVerticalGaussValuations

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEquivCoverPointsPlacesBaseChange
section
open ReciprocityTheory.ChartRestriction.G.T0 Formalism.MainNotions.Gaps.EtaleWeightGaps
open scoped TensorProduct

namespace GlobalTheory

namespace CoverPlaces

variable {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A]
  [Algebra O A] {ϖ : O}

theorem ord_pos_iff (h : IsUnif A ϖ) (ζ : Pts O A) [IsDVRAt ζ] (a : As O A) :
    0 < ord ϖ ζ (a : A) ↔ a ∈ ζ.asIdeal := by
  rw [ord_of_mem ζ h a.2, ← not_iff_not, ← vL_eq_zero_iff]
  change ¬ 0 < (vL ζ a).map (Nat.cast : ℕ → ℤ) ↔ _
  generalize vL ζ a = v
  cases v with
  | top => simp
  | coe j =>
    rw [ENat.map_natCast, ← WithTop.coe_zero, WithTop.coe_lt_coe]
    simp

theorem surjective_of_detect [∀ ζ : Pts O A, IsDVRAt ζ] (h : IsUnif A ϖ) {T : Type} [Finite T]
    (Z : T → Pts O A) (hZ : ∀ x, (∀ t, 0 ≤ ord ϖ (Z t) x) → x ∈ As O A) :
    Function.Surjective Z := by
  classical
  cases nonempty_fintype T
  intro ζ
  by_contra hne
  have hex : ∀ t, ∃ a ∈ (Z t).asIdeal, a ∉ ζ.asIdeal := by
    intro t
    by_contra hc
    push Not at hc
    exact hne ⟨t, MaximalSpectrum.ext ((Z t).isMaximal.eq_of_le ζ.isMaximal.ne_top hc)⟩
  choose a ha ha' using hex
  haveI := ζ.isMaximal.isPrime
  have hb : ∏ t, a t ∉ ζ.asIdeal := by
    rw [Ideal.IsPrime.prod_mem_iff]
    rintro ⟨t, -, ht⟩
    exact ha' t ht
  have hbt : ∀ t, ∏ t, a t ∈ (Z t).asIdeal := fun t =>
    Ideal.prod_mem _ (Finset.mem_univ t) (ha t)
  generalize ∏ t, a t = b at hb hbt
  obtain ⟨v, hv⟩ := h.isUnit.exists_right_inv
  set n : ℕ := ∑ t, ep ϖ (Z t) with hn
  have hx : v * (b : A) ^ n ∈ As O A := by
    apply hZ
    intro t
    have h1 : ord ϖ (Z t) (algebraMap O A ϖ * (v * (b : A) ^ n)) = n • ord ϖ (Z t) b := by
      rw [← mul_assoc, hv, one_mul, ord_pow _ h]
    rw [ord_mul _ h, ord_unif _ h] at h1
    have h2 := (ord_pos_iff h (Z t) b).2 (hbt t)
    have h3 : ep ϖ (Z t) ≤ n :=
      Finset.single_le_sum (f := fun t => ep ϖ (Z t)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    have h4 := ep_pos (Z t) h
    generalize ord ϖ (Z t) (v * (b : A) ^ n) = p at h1
    generalize ord ϖ (Z t) (b : A) = q at h1 h2
    generalize ep ϖ (Z t) = e at h1 h3 h4
    induction p using WithTop.recTopCoe with
    | top => exact le_top
    | coe p =>
      induction q using WithTop.recTopCoe with
      | top =>
        obtain ⟨m, hm⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        rw [hm, succ_nsmul, add_top, ← WithTop.coe_add] at h1
        exact absurd h1 WithTop.coe_ne_top
      | coe q =>
        rw [← WithTop.coe_add, ← WithTop.coe_nsmul, WithTop.coe_inj, nsmul_eq_mul] at h1
        have h5 : 0 < q := by exact_mod_cast h2
        have h6 : (e : ℤ) ≤ n := by exact_mod_cast h3
        have h7 : 0 ≤ p := by nlinarith
        exact_mod_cast h7
  have hp : b ^ n = algebraMap O (As O A) ϖ * ⟨_, hx⟩ := by
    apply Subtype.ext
    change (b : A) ^ n = algebraMap O A ϖ * (v * (b : A) ^ n)
    rw [← mul_assoc, hv, one_mul]
  exact hb (ζ.isMaximal.isPrime.mem_of_pow_mem n (hp ▸ Ideal.mul_mem_right _ _ (unif_mem h ζ)))

theorem isIntegral_of_forall {R A ι : Type} [CommRing R] [CommRing A] [Algebra R A] [Finite ι]
    {S : ι → Type} [∀ c, CommRing (S c)] [∀ c, Algebra R (S c)] (Ψ : ∀ c, A →ₐ[R] S c)
    (hΨ : ∀ a, (∀ c, Ψ c a = 0) → a = 0) (x : A) (hx : ∀ c, IsIntegral R (Ψ c x)) :
    IsIntegral R x := by
  classical
  cases nonempty_fintype ι
  choose p hp hp0 using hx
  refine ⟨∏ c, p c, Polynomial.monic_prod_of_monic _ _ fun c _ => hp c, hΨ _ fun c => ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_algHom_apply, map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [Polynomial.aeval_def]; exact hp0 c)

end CoverPlaces

open CoverPlaces in

theorem exists_equiv_pts_places_baseChange : ∀ (R R' F F' : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R'] [Module.Flat R R'] [IsLocalHom (algebraMap R R')] [Field F] [Algebra R F] [IsFractionRing R F] [Field F'] [Algebra R' F'] [IsFractionRing R' F'] [Algebra F F'] [Algebra R F'] [IsScalarTower R F F'] [IsScalarTower R R' F'], Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R' → Function.Surjective (IsLocalRing.ResidueField.map (algebraMap R R')) → ∀ (ι : Type) [Finite ι] (L : ι → Type) [∀ c, Field (L c)] [∀ c, Algebra F (L c)] [∀ c, FiniteDimensional F (L c)] [∀ c, Algebra.IsSeparable F (L c)] [∀ c, Algebra R (L c)] [∀ c, IsScalarTower R F (L c)] (A : Type) [CommRing A] [Algebra R' A] (ϖ : R'), IsUnif A ϖ → ∀ [∀ ζ : Pts R' A, IsDVRAt ζ] (Ψ : ∀ c, A →ₐ[R'] F' ⊗[F] L c), (∀ c, Function.Surjective (Ψ c)) → (∀ a, (∀ c, Ψ c a = 0) → a = 0) → (∀ c c', c ≠ c' → ∃ a, Ψ c a = 0 ∧ Ψ c' a = 1) → ∃ e : Pts R' A ≃ Σ c, ValPl.PlacesOver R (L c), ∀ ζ, fdeg ζ = (letI := resAlg (F := F) (e ζ).2.1; Module.finrank (IsLocalRing.ResidueField ((vRing (e ζ).2.1).comap (algebraMap F (L (e ζ).1)))) (IsLocalRing.ResidueField (vRing (e ζ).2.1))) ∧ ∃ u : AddValuation (F' ⊗[F] L (e ζ).1) (WithTop ℤ), (∀ g, u ((1 : F') ⊗ₜ[F] g) = (e ζ).2.1 g) ∧ ∀ a, ord ϖ ζ a = u (Ψ (e ζ).1 a) := by
  intro R R' F F' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hmax hres ι _ L _ _ _ _ _ _ A _ _ ϖ hϖ _ Ψ
    hsurj hinj hsep
  choose w' hw1 hw2 hw3 hw4 using fun c =>
    exists_unique_place_baseChange R R' F F' hmax hres (L c)
      (isIntegral_iff_mem_span_one_tmul_integralClosure R R' F F' hmax hres (L c))
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hex : ∀ t : Σ c, ValPl.PlacesOver R (L c), ∃ ζ : Pts R' A,
      ∀ a, ord ϖ ζ a = w' t.1 t.2 (Ψ t.1 a) := by
    rintro ⟨c, w⟩
    refine exists_pt_ord_eq_addValuation R' A ϖ hϖ ((w' c w).comap (Ψ c).toRingHom) ?_ ?_ ?_
    · intro a ha
      exact (hw2 c _).1 (IsIntegral.map (Ψ c) ha) w
    · have hm : ϖ ∈ Ideal.span {algebraMap R R' π} := by
        rw [← PlaceExt.maximalIdeal_eq_span hmax hπ]
        exact hϖ.irreducible.not_isUnit
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 hm
      change 0 < w' c w (Ψ c (algebraMap R' A ϖ))
      rw [AlgHom.commutes, ← hr, map_mul, AddValuation.map_mul, PlaceExt.algebraMap_eq_one_tmul,
        hw1]
      exact lt_of_lt_of_le ((w.2.2 π).2.2 hπ.not_isUnit)
        (le_add_of_nonneg_left ((hw2 c _).1 isIntegral_algebraMap w))
    · obtain ⟨g, hg⟩ := w.2.1.2
      obtain ⟨a, ha⟩ := hsurj c ((1 : F') ⊗ₜ[F] g)
      refine ⟨a, ?_⟩
      change w' c w (Ψ c a) = 1
      rw [ha, hw1, hg]
  choose Z hZ using hex
  have hZinj : Function.Injective Z := by
    rintro ⟨c, w⟩ ⟨c', w₂⟩ he
    have h1 : ∀ a, w' c w (Ψ c a) = w' c' w₂ (Ψ c' a) := fun a => by
      rw [← hZ ⟨c, w⟩ a, he, hZ]
    obtain rfl : c = c' := by
      by_contra hc
      obtain ⟨a, h0, h1'⟩ := hsep c c' hc
      have := h1 a
      rw [h0, h1', AddValuation.map_zero, AddValuation.map_one] at this
      exact WithTop.top_ne_zero this
    congr 1
    apply Subtype.ext
    apply AddValuation.ext
    intro g
    obtain ⟨a, ha⟩ := hsurj c ((1 : F') ⊗ₜ[F] g)
    rw [← hw1, ← hw1, ← ha, h1]
  haveI : ∀ c, Finite (ValPl.PlacesOver R (L c)) := fun c => by
    haveI := integralClosure.isDedekindDomain R F (L c)
    haveI := integralClosure.isFractionRing_of_finite_extension (A := R) F (L c)
    exact (ValPl.placesOver_finite (F := F) R (L c)).to_subtype
  have hZsurj : Function.Surjective Z := by
    refine surjective_of_detect hϖ Z fun x hx => ?_
    refine isIntegral_of_forall Ψ hinj x fun c => (hw2 c _).2 fun w => ?_
    have := hx ⟨c, w⟩
    rwa [hZ] at this
  refine ⟨(Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm, fun ζ => ?_⟩
  have hζ : Z ((Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm ζ) = ζ :=
    (Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).apply_symm_apply ζ
  generalize (Equiv.ofBijective Z ⟨hZinj, hZsurj⟩).symm ζ = t at hζ ⊢
  subst hζ
  obtain ⟨c, w⟩ := t
  refine ⟨?_, w' c w, hw1 c w, hZ ⟨c, w⟩⟩
  refine T.fdeg_eq_finrank_residueField_alt R R' F hres (L c) A ϖ hϖ _ w.1 w.2 (F' ⊗[F] L c) (w' c w) (Ψ c).toRingHom
    (Algebra.TensorProduct.includeRight : L c →ₐ[F] F' ⊗[F] L c).toRingHom (hsurj c) ?_
    (hw1 c w) (hZ ⟨c, w⟩) (hw3 c w)
  intro r
  exact ((Ψ c).commutes _).trans (PlaceExt.algebraMap_eq_one_tmul r)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsRingHomTensorOmSOfPoint
section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_ringHom_tensor_OmS_of_point :
    ∀ (K Ω K' U : Type) [Field K] [Field Ω] [Algebra K Ω] [Field K'] [Field U] (D N : ℕ) (j₀ : Fin (N + 1)) (x : Fin N → Ω) [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)] [Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K'] (κ : K' →+* U) (τ : Ω →+* U) (T : ReciprocityTheory.ChartRestriction.G.T0.TVar D N → K'), Algebra.trdeg K Ω = D → (∀ p : ReciprocityTheory.ChartRestriction.G.T0.KTp K D N, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) p) = ReciprocityTheory.ChartRestriction.G.T0.sHom j₀ x p) → (∀ p, algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K' (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (MvPolynomial.X p)) = T p) → (∀ a : K, τ (algebraMap K Ω a) = κ (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K' (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (MvPolynomial.C a)))) → (∀ i : Fin D, κ (T (i.succ, j₀)) + ∑ k, κ (T (i.succ, j₀.succAbove k)) * τ (x k) = 0) → ∃ χ : K' ⊗[ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N →+* U, (∀ a : K', χ (a ⊗ₜ 1) = κ a) ∧ ∀ ω : Ω, χ (1 ⊗ₜ algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) ω) = τ ω := by
  intro K Ω K' U _ _ _ _ _ D N j₀ x _ _ κ τ T hD hS hT hC hrel
  classical
  letI : Algebra K U := (τ.comp (algebraMap K Ω)).toAlgebra
  have hKU : ∀ a : K, algebraMap K U a = τ (algebraMap K Ω a) := fun _ => rfl
  let φ : Ω →ₐ[K] U := { τ with commutes' := fun _ => rfl }
  let g : ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →+* U :=
    κ.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K').comp
      (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)))
  have hg : Function.Injective g :=
    κ.injective.comp ((algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K').injective.comp
      (IsFractionRing.injective (ReciprocityTheory.ChartRestriction.G.T0.KTp K D N) (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N)))
  have hgC : ∀ a : K, g (MvPolynomial.C a) = τ (algebraMap K Ω a) := fun a => (hC a).symm
  have hgX : ∀ p, g (MvPolynomial.X p) = κ (T p) := fun p => congrArg κ (hT p)
  have hind : AlgebraicIndependent K (fun p => κ (T p)) := by
    rw [algebraicIndependent_iff_injective_aeval]
    have : (MvPolynomial.aeval (fun p => κ (T p)) :
        ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →ₐ[K] U).toRingHom = g := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [hgC]
        simp [hKU]
      · intro p
        rw [hgX]
        simp
    have h2 : Function.Injective (MvPolynomial.aeval (fun p => κ (T p)) :
        ReciprocityTheory.ChartRestriction.G.T0.KTp K D N →ₐ[K] U).toRingHom := this ▸ hg
    exact h2
  obtain ⟨P, ⟨hP1, hP2⟩, -⟩ :=
    GlobalTheory.existsUnique_ringHom_OmS K Ω U D N j₀ x (fun p => κ (T p)) φ hD hind hrel
  have hP1' : ∀ a : Ω, P (algebraMap Ω (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N) a) = τ a := hP1
  have key : P.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) (ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N)) =
      κ.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K') := by
    apply IsFractionRing.ringHom_ext (A := ReciprocityTheory.ChartRestriction.G.T0.KTp K D N)
    intro q
    have : P.comp (ReciprocityTheory.ChartRestriction.G.T0.sHom (K := K) (D := D) j₀ x).toRingHom = g := by
      apply MvPolynomial.ringHom_ext
      · intro a
        rw [hgC, ← hP1', ← IsScalarTower.algebraMap_apply]
        simp [ReciprocityTheory.ChartRestriction.G.T0.sHom]
      · intro p
        rw [hgX, ← hP2]
        simp [ReciprocityTheory.ChartRestriction.G.T0.sHom]
    rw [RingHom.comp_apply, hS]
    exact DFunLike.congr_fun this q
  letI : Algebra (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) U :=
    (κ.comp (algebraMap (ReciprocityTheory.ChartRestriction.G.T0.KTf K D N) K')).toAlgebra
  let κ' : K' →ₐ[ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] U := { κ with commutes' := fun _ => rfl }
  let P' : ReciprocityTheory.ChartRestriction.G.T0.OmS Ω D N →ₐ[ReciprocityTheory.ChartRestriction.G.T0.KTf K D N] U :=
    { P with commutes' := fun r => DFunLike.congr_fun key r }
  refine ⟨(Algebra.TensorProduct.productMap κ' P').toRingHom, fun a => ?_, fun ω => ?_⟩
  · change Algebra.TensorProduct.productMap κ' P' (a ⊗ₜ 1) = κ a
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, mul_one]
    rfl
  · change Algebra.TensorProduct.productMap κ' P' (1 ⊗ₜ _) = τ ω
    rw [Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]
    exact hP1' ω

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteSupportAndDensityAndAemeasurable
section
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

theorem finite_support_and_density_and_aemeasurable :
    (∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, 1 ≤ d.D → (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → (∀ G, Module.finrank (Ω c) (𝒜 c G) = 1) → (∀ j, d.w j c ∈ 𝒜 c d.wL) → d.w (d.jc c) c ≠ 0 → ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD d c → (∀ g : Ω c, g ≠ 0 → {v | d.admitted c v ∧ v g ≠ 0}.Finite) ∧ ∀ (G : WT) (e : A c) (S : Finset (Ω c)), e ∈ 𝒜 c G → e ≠ 0 → (∀ v, d.admitted c v → ∀ a : Ω c, a ≠ 0 → ((d.ord c v G (a • e) : ℤ) : WithTop ℤ) = v a + (d.ord c v G e : WithTop ℤ)) → (∀ v, d.admitted c v → (∀ s ∈ S, 0 ≤ v s) → d.ord c v G e = 0) → ∀ f ∈ 𝒜 c G, f ≠ 0 → {v | d.admitted c v ∧ d.ord c v G f ≠ 0}.Finite) ∧ (∀ (K A Ω : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.FiniteType K A] [Field Ω] [Algebra A Ω] [IsFractionRing A Ω] [Algebra K Ω] [IsScalarTower K A Ω] (sg : K →+* ℂ) (φ : A →+* ℂ), φ.comp (algebraMap K A) = sg → ∀ (S : Finset A) (ε : ℝ), 0 < ε → ∃ P ∈ PT (Ω := Ω) sg, ∀ a ∈ S, ‖P (algebraMap A Ω a) - φ a‖ < ε) ∧ (∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 → (∃ J : Fin d.D → Fin d.N, LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) → ∀ (sg : K →+* ℂ) (m : ℕ) (a : Fin m → Ω c) (Nf : (Fin m → ℂ) → ℝ) (h : (Ω c →+* ℂ) → ℝ), Measurable Nf → (∀ P ∈ PT (Ω := Ω c) sg, h P = Nf (fun i => P (a i))) → AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 => ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j), h P) d.sphMeasure) :=
  ⟨finite_support_admissible finite_vertical_gauss_valuations finite_zeros_poles_of_trdeg_one,
    generic_points_dense exists_algIndep_tuple_near,
    aemeasurable_finsum_section ae_eval₂_ne_zero_pi_toSphere
      (measurable_sum_embeddings_over_generic_point exists_measurable_roots_enumeration)
      existsUnique_ringHom_OmS⟩

end GlobalTheory
end

