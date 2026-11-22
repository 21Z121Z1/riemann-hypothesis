import Mathlib
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0003
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
import ReciprocityTheory.DualLattices.Bundle0018
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0010
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0018
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0005
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.DetUpdateRowDiagonal
section
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

namespace PositivityTheory.HtPt.Rh

theorem det_updateRow_diagonal {R : Type} [CommRing R] {m : ℕ} (c r : Fin m → R) (i : Fin m) :
    ((Matrix.diagonal c).updateRow i r).det = (∏ j ∈ Finset.univ.erase i, c j) * r i := by
  rw [← Matrix.cramer_transpose_apply, Matrix.diagonal_transpose, Matrix.cramer_eq_adjugate_mulVec,
    Matrix.adjugate_diagonal, Matrix.mulVec_diagonal]

theorem len_eq : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → ∀ (ι : Type) [Fintype ι] (L L' : Submodule R (ι → R)), L ≤ L' → ∀ x y : NNReal, x ≠ 0 → HasLen v R ((ι → R) ⧸ L) x → HasLen v R ((ι → R) ⧸ L') y → x ≤ y ∧ (x = y → L = L') := by
  intro C _ v R _ _ hv ι _ L L' hL x y hx0 hx hy
  obtain ⟨m, c, ⟨e⟩, rfl⟩ := hx
  obtain ⟨n, d, ⟨e'⟩, rfl⟩ := hy
  haveI := isLocal_of_integers hv
  let π : ((i : Fin m) → R ⧸ Ideal.span {c i}) →ₗ[R] ((i : Fin n) → R ⧸ Ideal.span {d i}) :=
    e'.toLinearMap ∘ₗ (Submodule.factor hL) ∘ₗ e.symm.toLinearMap
  have hπ : Function.Surjective π :=
    e'.surjective.comp ((Submodule.factor_surjective hL).comp e.symm.surjective)
  let s : Fin m → ((i : Fin m) → R ⧸ Ideal.span {c i}) :=
    fun i => Pi.single i (1 : R ⧸ Ideal.span {c i})
  have hsp : Submodule.span R (Set.range fun i => π (s i)) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨w, rfl⟩ := hπ z
    rw [eq_sum_single c w, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hdiag : ∀ k, ∑ i, Matrix.diagonal c k i • π (s i) = 0 := by
    intro k
    rw [Finset.sum_eq_single k]
    · rw [Matrix.diagonal_apply_eq, ← map_smul, single_smul_self c k, map_zero]
    · intro i _ hi
      rw [Matrix.diagonal_apply_ne' _ hi, zero_smul]
    · simp
  have key : ∀ T : Matrix (Fin m) (Fin m) R, (∀ k, ∑ i, T k i • π (s i) = 0) →
      v (algebraMap R C T.det) ≤ ∏ i, v (algebraMap R C (d i)) := by
    intro T hT
    have h := det_mem_span_prod n d m _ hsp T hT
    rw [Ideal.mem_span_singleton] at h
    have h2 := hv.le_of_dvd h
    rwa [map_prod, map_prod] at h2
  refine ⟨?_, fun hxy => le_antisymm hL fun l hl => ?_⟩
  · have := key _ hdiag
    rwa [Matrix.det_diagonal, map_prod, map_prod] at this
  · set w := e (Submodule.Quotient.mk l) with hw
    have hπw : π w = 0 := by
      have : (Submodule.Quotient.mk l : (ι → R) ⧸ L') = 0 := (Submodule.Quotient.mk_eq_zero _).2 hl
      simp [π, hw, this]
    have hw0 : w = 0 := by
      funext i
      have hrel : ∑ k, (Quotient.out (w k) : R) • π (s k) = 0 := by
        rw [← hπw]
        conv_rhs => rw [eq_sum_single c w, map_sum]
        simp only [map_smul, s]
      have h := key ((Matrix.diagonal c).updateRow i fun k => (Quotient.out (w k) : R)) (by
        intro k
        by_cases hk : k = i
        · subst hk
          simpa only [Matrix.updateRow_self] using hrel
        · simpa only [Matrix.updateRow_ne hk] using hdiag k)
      rw [det_updateRow_diagonal, ← hxy, map_mul, map_mul, map_prod, map_prod,
        ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)] at h
      have hne : ∏ j ∈ Finset.univ.erase i, v (algebraMap R C (c j)) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun j _ =>
          Finset.prod_ne_zero_iff.1 hx0 j (Finset.mem_univ j)
      have h2 := le_of_mul_le_mul_left h (pos_iff_ne_zero.2 hne)
      have h3 := hv.dvd_of_le h2
      rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_out] at h3
      exact h3
    have : (Submodule.Quotient.mk l : (ι → R) ⧸ L) = 0 := e.injective (by rw [← hw, hw0, map_zero])
    exact (Submodule.Quotient.mk_eq_zero _).1 this

end PositivityTheory.HtPt.Rh
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.EigFrob
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ci

theorem mem_eig {K O V : Type} [Field K] [AddCommGroup V] [Module K V] {ρ : O → V →ₗ[K] V} {χ : O → K} {x : V} :
    x ∈ eig ρ χ ↔ ∀ a, ρ a x = χ a • x := by
  simp [eig, sub_eq_zero]

theorem eig_frob : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ℕ) (O : Type) (ρ : O → Matrix (Fin d) (Fin d) K) (χ : O → K), eig (fun a => Matrix.toLin' ((ρ a).map (· ^ p))) (fun a => χ a ^ p) = frobSub p (eig (fun a => Matrix.toLin' (ρ a)) χ) := by
  intro K _ p _ _ d O ρ χ
  apply le_antisymm
  · classical
    intro y hy
    rw [mem_eig] at hy
    set K0 := (frobenius K p).fieldRange with hK0
    let β := Module.Basis.ofVectorSpace K0 K
    have hpow : ∀ c : K, c ^ p ∈ K0 := fun c => RingHom.mem_fieldRange.2 ⟨c, frobenius_def p c⟩
    have hrepr : ∀ (c u : K) ι, (β.repr (c ^ p * u) ι : K) = c ^ p * β.repr u ι := by
      intro c u ι
      have h0 : c ^ p * u = (⟨c ^ p, hpow c⟩ : K0) • u := rfl
      rw [h0, map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    have hsum : ∀ ι (f : Fin d → K), (β.repr (∑ j, f j) ι : K) = ∑ j, (β.repr (f j) ι : K) := by
      intro ι f
      simp [map_sum, Finsupp.finset_sum_apply]
    let z : _ → Fin d → K := fun ι j => (β.repr (y j) ι : K)
    have hz : ∀ ι a r, ∑ j, ρ a r j ^ p * z ι j = χ a ^ p * z ι r := by
      intro ι a r
      have h1 := congrFun (hy a) r
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.smul_apply,
        smul_eq_mul] at h1
      have h2 := congrArg (fun u => (β.repr u ι : K)) h1
      simp only [hsum, hrepr] at h2
      exact h2
    have hex : ∀ ι j, ∃ x : K, x ^ p = z ι j := by
      intro ι j
      obtain ⟨x, hx⟩ := RingHom.mem_fieldRange.1 (β.repr (y j) ι).2
      exact ⟨x, by rw [← frobenius_def]; exact hx⟩
    choose x hx using hex
    have hxE : ∀ ι, x ι ∈ eig (fun a => Matrix.toLin' (ρ a)) χ := by
      intro ι
      rw [mem_eig]
      intro a
      funext r
      simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
      apply frobenius_inj K p
      rw [frobenius_def, frobenius_def, sum_pow_char, mul_pow]
      simp only [mul_pow, hx]
      exact hz ι a r
    let T := Finset.univ.biUnion fun j => (β.repr (y j)).support
    have hT : y = ∑ ι ∈ T, β ι • frobVec p (x ι) := by
      funext j
      rw [Finset.sum_apply]
      conv_lhs => rw [← β.linearCombination_repr (y j)]
      rw [Finsupp.linearCombination_apply,
        Finsupp.sum_of_support_subset _ (Finset.subset_biUnion_of_mem
          (fun j => (β.repr (y j)).support) (Finset.mem_univ j)) (fun i (a : K0) => a • β i) (fun i _ => zero_smul _ _)]
      refine Finset.sum_congr rfl fun ι _ => ?_
      show (β.repr (y j) ι : K) * β ι = β ι * x ι j ^ p
      rw [hx ι j, mul_comm]
    rw [hT, frobSub]
    exact Submodule.sum_mem _ fun ι _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨x ι, hxE ι, rfl⟩)
  · rw [frobSub, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_eig]
    rw [SetLike.mem_coe, mem_eig] at hx
    intro a
    have hxa := hx a
    simp only [Matrix.toLin'_apply] at hxa ⊢
    funext r
    have h1 := congrFun hxa r
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, frobVec, Matrix.map_apply] at h1 ⊢
    rw [← mul_pow, ← h1, sum_pow_char]
    simp only [mul_pow]

theorem eig_dual : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (O k S : Type) [CommRing O] [Field k] [Algebra k K] [Fintype S] [DecidableEq S] (χ : S → (O →+* k)), IsSplit χ → (∀ i (c : k), C.v i (algebraMap k K c) ≤ 1) → ∀ ρ : O →+* Matrix (Fin d) (Fin d) K, IsBun C L → (∀ a, IsHom C L L (Matrix.toLin' (ρ a))) → ∀ s, subDeg C (dotDual C L) (eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a))) = - subDeg C L (eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a))) := by
  intro K _ C d L O k S _ _ _ _ _ χ hχ hv ρ hL hρ s
  let ρL : O →+* Module.End K (Fin d → K) :=
    (Matrix.toLinAlgEquiv'.toRingEquiv : Matrix (Fin d) (Fin d) K ≃+* Module.End K (Fin d → K)).toRingHom.comp ρ
  obtain ⟨e, he_hom, he_mem, he_id, -, he_comb⟩ :=
    GlobalTheory.T.eigen_projectors_split_action K C (Fin d → K) L O k S χ hχ hv ρL hL hρ
  obtain ⟨m, c, b, hc, hes⟩ := he_comb s
  set W := eig (fun a => Matrix.toLin' (ρ a)) (fun a => algebraMap k K (χ s a)) with hW
  set W' := eig (fun a => Matrix.toLin' (ρ a).transpose) (fun a => algebraMap k K (χ s a)) with hW'
  set E : Matrix (Fin d) (Fin d) K := ∑ j, algebraMap k K (c j) • ρ (b j) with hE
  have hlin : Matrix.toLin' E = ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j)) := by
    rw [hE, map_sum]
    simp only [map_smul]
  have hlinT : Matrix.toLin' E.transpose =
      ∑ j, algebraMap k K (c j) • Matrix.toLin' (ρ (b j)).transpose := by
    rw [hE, Matrix.transpose_sum, map_sum]
    simp only [Matrix.transpose_smul, map_smul]
  have heE : ∀ x, e s x = E.mulVec x := by
    intro x
    rw [← Matrix.toLin'_apply, hlin, hes]
    rfl
  have hEW : ∀ x, E.mulVec x ∈ W := fun x => heE x ▸ he_mem s x
  have hEL : ∀ i, ∀ x ∈ L i, E.mulVec x ∈ L i := fun i x hx => heE x ▸ he_hom s i x hx
  have hEid : ∀ x ∈ W, E.mulVec x = x := fun x hx => (heE x).symm.trans (he_id s x hx)
  have hETid : ∀ y ∈ W', E.transpose.mulVec y = y := by
    intro y hy
    simp only [hW', mem_eig, Matrix.toLin'_apply] at hy
    rw [← Matrix.toLin'_apply, hlinT, LinearMap.sum_apply]
    simp only [LinearMap.smul_apply, Matrix.toLin'_apply, hy, smul_smul, ← map_mul,
      ← Finset.sum_smul, ← map_sum]
    rw [hc s, if_pos rfl, map_one, one_smul]
  have hETW : ∀ z, E.transpose.mulVec z ∈ W' := by
    intro z
    rw [hW', mem_eig]
    intro a
    have hmat : ρ a * E = algebraMap k K (χ s a) • E := by
      refine Matrix.toLin'.injective (LinearMap.ext fun w => ?_)
      rw [map_smul, LinearMap.smul_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
        ← Matrix.mulVec_mulVec]
      have h1 := (mem_eig.1 (hEW w)) a
      simpa only [Matrix.toLin'_apply] using h1
    have h2 : (ρ a).transpose * E.transpose = algebraMap k K (χ s a) • E.transpose := by
      have hcm : E * ρ a = ρ a * E := by
        rw [hE, Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [smul_mul_assoc, mul_smul_comm, ← map_mul, ← map_mul, mul_comm]
      rw [← Matrix.transpose_mul, hcm, hmat, Matrix.transpose_smul]
    show Matrix.toLin' (ρ a).transpose (E.transpose.mulVec z) =
      algebraMap k K (χ s a) • E.transpose.mulVec z
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, h2, ← Matrix.toLin'_apply, map_smul,
      LinearMap.smul_apply, Matrix.toLin'_apply]
  have hadj : ∀ x y, x ⬝ᵥ E.transpose.mulVec y = E.mulVec x ⬝ᵥ y := by
    intro x y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
  let B : W →ₗ[K] W' →ₗ[K] K := (dotProductBilin K K).compl₁₂ W.subtype W'.subtype
  have hB : ∀ x y, B x y = (x : Fin d → K) ⬝ᵥ (y : Fin d → K) := fun x y => rfl
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun x hx => ?_
    have h0 : ∀ z, (x : Fin d → K) ⬝ᵥ z = 0 := by
      intro z
      have h1 : B x ⟨_, hETW z⟩ = 0 := by rw [hx]; rfl
      rw [hB] at h1
      change (x : Fin d → K) ⬝ᵥ E.transpose.mulVec z = 0 at h1
      rwa [hadj, hEid _ x.2] at h1
    apply Subtype.ext
    funext j
    simpa using h0 (Pi.single j 1)
  have hinj2 : Function.Injective B.flip := by
    refine (injective_iff_map_eq_zero B.flip).2 fun y hy => ?_
    have h0 : ∀ z, z ⬝ᵥ (y : Fin d → K) = 0 := by
      intro z
      have h1 : B.flip y ⟨_, hEW z⟩ = 0 := by rw [hy]; rfl
      rw [LinearMap.flip_apply, hB] at h1
      change E.mulVec z ⬝ᵥ (y : Fin d → K) = 0 at h1
      rwa [← hadj, hETid _ y.2] at h1
    apply Subtype.ext
    funext j
    simpa using h0 (Pi.single j 1)
  have hd1 : Module.finrank K (W' →ₗ[K] K) = Module.finrank K W' := Subspace.dual_finrank_eq
  have hd2 : Module.finrank K (W →ₗ[K] K) = Module.finrank K W := Subspace.dual_finrank_eq
  have hle1 := LinearMap.finrank_le_finrank_of_injective hinj
  have hle2 := LinearMap.finrank_le_finrank_of_injective hinj2
  have hfr : Module.finrank K W = Module.finrank K (W' →ₗ[K] K) := by omega
  have hbij : Function.Bijective B :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).1 hinj⟩
  obtain ⟨-, hdeg, -⟩ := GlobalTheory.T.dual_lattice_degree_neg K C W W' (sub C L W) B (GlobalTheory.T.sub_and_quotient_bundles K C _ L W hL).1 hbij
  have hident : dualLat C (sub C L W) B = sub C (dotDual C L) W' := by
    funext i
    ext y
    show (∀ x ∈ sub C L W i, C.v i (B x y) ≤ 1) ↔ ∀ x ∈ L i, C.v i (dotProductBilin K K x y) ≤ 1
    constructor
    · intro h x hx
      have hxy : dotProductBilin K K x y = B ⟨_, hEW x⟩ y := by
        rw [hB]
        show x ⬝ᵥ (y : Fin d → K) = E.mulVec x ⬝ᵥ (y : Fin d → K)
        rw [← hadj, hETid _ y.2]
      rw [hxy]
      exact h _ (hEL i x hx)
    · intro h x hx
      exact h x hx
  show deg C (sub C (dotDual C L) W') = -deg C (sub C L W)
  rw [← hident]
  exact hdeg

end PositivityTheory.HtPt.Ci
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.EqOfPowEqSelf
section
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num NumberField

namespace PositivityTheory.HtPt.Teich

theorem eq_of_pow_eq_self {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] (q : ℕ)
    (hq : (q : IsLocalRing.ResidueField O) = 0) {x y : O} (hx : x ^ q = x) (hy : y ^ q = y)
    (h : IsLocalRing.residue O x = IsLocalRing.residue O y) : x = y := by
  by_contra hne
  have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
  have hgeom := geom_sum₂_mul x y q
  rw [hx, hy] at hgeom
  have hS : (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) = 1 := by
    have hmul : (∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i)) * (x - y) = 1 * (x - y) := by
      rw [hgeom, one_mul]
    exact mul_right_cancel₀ hsub hmul
  have hres := congrArg (IsLocalRing.residue O) hS
  rw [map_sum, map_one] at hres
  simp only [map_mul, map_pow, ← h] at hres
  rw [geom_sum₂_self, hq, zero_mul] at hres
  exact zero_ne_one hres

theorem card_eq_zero {O : Type} [CommRing O] [IsLocalRing O] {F : Type} [Field F] [Fintype F]
    (σ : F →+* IsLocalRing.ResidueField O) :
    ((Fintype.card F : ℕ) : IsLocalRing.ResidueField O) = 0 := by
  rw [← map_natCast σ, FiniteField.cast_card_eq_zero, map_zero]

theorem exists_lift {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {F : Type} [Field F]
    [Fintype F] (ζ : O) (hζ : IsPrimitiveRoot ζ (Fintype.card F - 1))
    (σ : F →+* IsLocalRing.ResidueField O) (a : F) :
    ∃ x : O, x ^ Fintype.card F = x ∧ IsLocalRing.residue O x = σ a := by
  have hQ1 : 1 < Fintype.card F := Fintype.one_lt_card
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card F = m + 1 := ⟨Fintype.card F - 1, by omega⟩
  rw [hm, Nat.add_sub_cancel] at hζ
  haveI : NeZero m := ⟨by omega⟩
  have hQres := PositivityTheory.HtPt.Teich.card_eq_zero (O := O) σ
  have hfix : ∀ k : ℕ, (ζ ^ k) ^ Fintype.card F = ζ ^ k := by
    intro k
    rw [hm, pow_succ, ← pow_mul, mul_comm k m, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
  have hprim : IsPrimitiveRoot (IsLocalRing.residue O ζ) m := by
    refine ⟨?_, ?_⟩
    · rw [← map_pow, hζ.pow_eq_one, map_one]
    · intro l hl
      apply hζ.dvd_of_pow_eq_one
      apply PositivityTheory.HtPt.Teich.eq_of_pow_eq_self _ hQres (hfix l) (one_pow _)
      rw [map_pow, hl, map_one]
  by_cases ha : a = 0
  · refine ⟨0, zero_pow (by omega), ?_⟩
    rw [ha, map_zero, map_zero]
  · have hpow := FiniteField.pow_card_sub_one_eq_one a ha
    rw [hm, Nat.add_sub_cancel] at hpow
    have h1 : (σ a) ^ m = 1 := by rw [← map_pow, hpow, map_one]
    obtain ⟨i, -, hi⟩ := hprim.eq_pow_of_pow_eq_one h1
    exact ⟨ζ ^ i, hfix i, by rw [map_pow, hi]⟩

theorem glue_teich : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] (F : Type) [Field F] [Fintype F] (p : ℕ) [Fact p.Prime] [CharP F p] (ζ : O), IsPrimitiveRoot ζ (Fintype.card F - 1) → ∀ σ : F →+* IsLocalRing.ResidueField O, (∃! χ : F →*₀ O, ∀ a, IsLocalRing.residue O (χ a) = σ a) ∧ ∀ (σ' : F →+* IsLocalRing.ResidueField O) (χ χ' : F →*₀ O), (∀ a, σ' a = σ a ^ p) → (∀ a, IsLocalRing.residue O (χ a) = σ a) → (∀ a, IsLocalRing.residue O (χ' a) = σ' a) → ∀ a, χ' a = χ a ^ p := by
  intro O _ _ _ F _ _ p _ _ ζ hζ σ
  have hQ : ((Fintype.card F : ℕ) : IsLocalRing.ResidueField O) = 0 :=
    PositivityTheory.HtPt.Teich.card_eq_zero σ
  have huniq : ∀ {x y : O}, x ^ Fintype.card F = x → y ^ Fintype.card F = y →
      IsLocalRing.residue O x = IsLocalRing.residue O y → x = y :=
    fun hx hy h => PositivityTheory.HtPt.Teich.eq_of_pow_eq_self _ hQ hx hy h
  have hfixχ : ∀ (χ : F →*₀ O) (a : F), χ a ^ Fintype.card F = χ a := fun χ a => by
    rw [← map_pow, FiniteField.pow_card]
  refine ⟨?_, ?_⟩
  · choose L hL hLres using PositivityTheory.HtPt.Teich.exists_lift ζ hζ σ
    let χ : F →*₀ O :=
      { toFun := L
        map_zero' := huniq (hL 0) (zero_pow Fintype.card_ne_zero) (by rw [hLres, map_zero, map_zero])
        map_one' := huniq (hL 1) (one_pow _) (by rw [hLres, map_one, map_one])
        map_mul' := fun a b => huniq (hL (a * b)) (by rw [mul_pow, hL a, hL b])
          (by rw [hLres, map_mul, map_mul, hLres, hLres]) }
    refine ⟨χ, hLres, fun χ' hχ' => ?_⟩
    exact MonoidWithZeroHom.ext fun a => huniq (hfixχ χ' a) (hL a) ((hχ' a).trans (hLres a).symm)
  · intro σ' χ χ' hσ' hχ hχ' a
    refine huniq (hfixχ χ' a) (by rw [← pow_mul, mul_comm p, pow_mul, hfixχ χ a]) ?_
    rw [hχ', hσ', map_pow, hχ]

end PositivityTheory.HtPt.Teich
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.FinClosure
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb

theorem fin_closure : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.EssFiniteType ℤ A] (K : Type) [Field K] [Algebra A K] [IsFractionRing A K] (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra A L] [IsScalarTower A K L], Module.Finite A (integralClosure A L) := by
  intro A _ _ _ K _ _ _ L _ _ _ _ _
  let A₀ := Algebra.EssFiniteType.subalgebra ℤ A
  let S := Algebra.EssFiniteType.submonoid ℤ A
  have hS : ∀ a : A, ∃ u s : A₀, IsUnit (s : A) ∧ a * s = u := fun a => by
    obtain ⟨⟨u, s⟩, e⟩ := IsLocalization.surj S a
    exact ⟨u, s, IsLocalization.map_units A s, e⟩
  have : FaithfulSMul A₀ K := (faithfulSMul_iff_algebraMap_injective _ _).2
    ((IsFractionRing.injective A K).comp Subtype.val_injective)
  have : IsFractionRing A₀ K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) z
    obtain ⟨u, s, hs, e⟩ := hS a
    obtain ⟨v, t, ht, e'⟩ := hS b
    refine ⟨u * t, v * s, ?_⟩
    have h1 : algebraMap A K s ≠ 0 := (hs.map _).ne_zero
    have h2 : algebraMap A K t ≠ 0 := (ht.map _).ne_zero
    show _ = algebraMap A K (u * t) / algebraMap A K (v * s)
    rw [← e, ← e']
    simp only [map_mul]
    rw [mul_assoc, mul_assoc, mul_comm (algebraMap A K t), mul_div_mul_right _ _ (mul_ne_zero h1 h2)]
  have hfin : Module.Finite A₀ (integralClosure A₀ L) :=
    GroundTheory.Heights₂.Heights.Model.FiniteIntegralClosure.proof A₀ K L
  obtain ⟨g, hg⟩ : (Subalgebra.toSubmodule (integralClosure A₀ L)).FG := Module.Finite.iff_fg.1 hfin
  refine (Module.Finite.iff_fg (N := Subalgebra.toSubmodule (integralClosure A L))).2 ⟨g, le_antisymm ?_ ?_⟩
  · refine Submodule.span_le.2 fun y hy => ?_
    have h : y ∈ Subalgebra.toSubmodule (integralClosure A₀ L) := hg ▸ Submodule.subset_span hy
    exact IsIntegral.tower_top (R := A₀) h
  · intro y hy
    obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization S y (hy : IsIntegral A y)
    have h : m • y ∈ Submodule.span A₀ (g : Set L) := by
      rw [hg]
      exact hm
    have h' : (m.1 : A) • y ∈ Submodule.span A (g : Set L) := Submodule.span_le_restrictScalars A₀ A _ h
    obtain ⟨w, hw⟩ := (IsLocalization.map_units A m).exists_left_inv
    have := Submodule.smul_mem _ w h'
    have hw' : w * (m.1 : A) = 1 := hw
    rwa [smul_smul, hw', one_smul] at this

end PositivityTheory.HtPt.Mb
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatBuild
section
noncomputable section

namespace PositivityTheory.HtPt.Htat

open GlobalTheory.CompanionTheory.Ar.HT NumberField TensorProduct

theorem chart_build : ∀ (A K : Type) [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (p R N : ℕ) (W Ω : Type) [AddCommGroup W] [Module A W] [Module.Finite A W] [Module.Projective A W] [AddCommGroup Ω] [Module K Ω] [Module A Ω] [IsScalarTower A K Ω] (j : W →ₗ[A] Ω), IsBaseChange K j → ∀ (ρ : 𝓞 E →+* Module.End A W) (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)) (h : (Fin N → 𝓞 E) →+ W), (∀ x, e x x = 0) → (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv c a • y)) → (∀ φ : (Fin N → 𝓞 E) →+ ZMod (p ^ R), ∃ x, e x = φ) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → (∀ (a : 𝓞 E) x, ∃ y, h (a • x) = ρ a (h x) + (p ^ R) • y) → ∃ D : HTChart A K c p R N Ω, D.om = LinearMap.range j ∧ D.e = e ∧ (∀ x, D.h x = j (h x)) ∧ ∀ a w, D.ρΩ a (j w) = j (ρ a w) := by
  intro A K _ _ _ _ _ E _ _ c p R N W Ω _ _ _ _ _ _ _ _ j hj ρ e h halt hadj hsurj hinj hlin
  classical
  have hsym : ∀ w : W, hj.equiv.symm (j w) = (1 : K) ⊗ₜ[A] w := by
    intro w
    rw [LinearEquiv.symm_apply_eq, IsBaseChange.equiv_tmul, one_smul]
  let T : 𝓞 E →+* Module.End K (K ⊗[A] W) := (Module.End.baseChangeHom A K W).toRingHom.comp ρ
  have hT : ∀ a (w : W), T a ((1 : K) ⊗ₜ[A] w) = (1 : K) ⊗ₜ[A] (ρ a w) := fun a w => rfl
  let ρΩ : 𝓞 E →+* Module.End K Ω :=
    { toFun := fun a => hj.equiv.toLinearMap ∘ₗ T a ∘ₗ hj.equiv.symm.toLinearMap
      map_one' := by ext x; simp
      map_mul' := by intro a b; ext x; simp [Module.End.mul_apply]
      map_zero' := by ext x; simp
      map_add' := by intro a b; ext x; simp }
  have hρ : ∀ a w, ρΩ a (j w) = j (ρ a w) := by
    intro a w
    show hj.equiv (T a (hj.equiv.symm (j w))) = _
    rw [hsym, hT, IsBaseChange.equiv_tmul, one_smul]
  have hinjj : Function.Injective j := by
    have h1 : Function.Injective ((Algebra.linearMap A K).rTensor W) :=
      Module.Flat.rTensor_preserves_injective_linearMap _ (IsFractionRing.injective A K)
    intro x y hxy
    apply (TensorProduct.lid A W).symm.injective
    apply h1
    apply hj.equiv.injective
    simp only [TensorProduct.lid_symm_apply, LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one,
      IsBaseChange.equiv_tmul, one_smul]
    exact hxy
  have hfg : (LinearMap.range j).FG := Module.Finite.iff_fg.mp (Module.Finite.range j)
  have hspan : Submodule.span K (LinearMap.range j : Set Ω) = ⊤ := by
    rw [eq_top_iff]
    intro ω hω
    clear hω
    obtain ⟨t, rfl⟩ := hj.equiv.surjective ω
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [IsBaseChange.equiv_tmul]
      exact Submodule.smul_mem _ s (Submodule.subset_span ⟨w, rfl⟩)
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  have hproj : Module.Projective A (LinearMap.range j) :=
    Module.Projective.of_equiv (LinearEquiv.ofInjective j hinjj)
  refine ⟨{ om := LinearMap.range j
            om_lat := ⟨hfg, hspan⟩
            om_proj := hproj
            ρΩ := ρΩ
            om_stable := ?_
            e := e
            alt := halt
            adj := hadj
            e_surj := hsurj
            e_inj := hinj
            h := j.toAddMonoidHom.comp h
            h_mem := fun x => ⟨h x, rfl⟩
            h_lin := ?_ }, rfl, rfl, fun x => rfl, hρ⟩
  · rintro a x ⟨w, rfl⟩
    exact ⟨ρ a w, (hρ a w).symm⟩
  · intro a x
    obtain ⟨y, hy⟩ := hlin a x
    refine ⟨j y, ⟨y, rfl⟩, ?_⟩
    show j (h (a • x)) = ρΩ a (j (h x)) + p ^ R • j y
    rw [hy, map_add, map_nsmul, hρ]

end PositivityTheory.HtPt.Htat
end
end

