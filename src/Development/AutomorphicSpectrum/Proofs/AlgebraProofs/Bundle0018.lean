import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0013
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0015
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XHaLattice
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0012
import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0001
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeQuotientStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_base_change_quotient : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] {Z Zc : Type} [AddCommGroup Z] [Module Ω Z] [AddCommGroup Zc] [Module C Zc] [Module Ω Zc] [IsScalarTower Ω C Zc] (b : V →ₗ[Ω] Vc) (b' : Z →ₗ[Ω] Zc), IsBaseChange C b → IsBaseChange C b' → ∀ (Δ : AddSubgroup (V × Z)) (H : AddSubgroup V) (N : ℕ), (∀ a ∈ R, ∀ v ∈ Δ, a • v ∈ Δ) → LocFree R N (Δ.map (AddMonoidHom.fst V Z)) → H ≤ Δ.map (AddMonoidHom.fst V Z) → (∀ a ∈ R, ∀ v ∈ H, a • v ∈ H) → spanOver RC (Prod.map b b' '' Δ) ⊓ (spanOver RC (b '' H)).prod ⊤ = spanOver RC (Prod.map b b' '' (Δ ⊓ H.prod ⊤ : AddSubgroup (V × Z))) ∧ (spanOver RC (Prod.map b b' '' Δ)).comap (AddMonoidHom.inr Vc Zc) = spanOver RC (b' '' Δ.comap (AddMonoidHom.inr V Z)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.GraphRestrict.main | exact GlobalTheory.CompanionTheory.Ar.GraphRestrict.main | (intros; apply GlobalTheory.CompanionTheory.Ar.GraphRestrict.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeSummandStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_base_change_summand : ∀ {o Ω C : Type} [CommRing o] [Field Ω] [Field C] [Algebra o Ω] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (R : Subalgebra o Ω) (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ {V Vc : Type} [AddCommGroup V] [Module Ω V] [AddCommGroup Vc] [Module C Vc] [Module Ω Vc] [IsScalarTower Ω C Vc] (b : V →ₗ[Ω] Vc), IsBaseChange C b → ∀ (L : AddSubgroup V) (U : Submodule Ω V), (∀ a ∈ R, ∀ v ∈ L, a • v ∈ L) → Summand L U → Summand (spanOver RC (b '' L)) (Submodule.span C (b '' U)) ∧ spanOver RC (b '' L) ⊓ (Submodule.span C (b '' U)).toAddSubgroup = spanOver RC (b '' (L ⊓ U.toAddSubgroup : AddSubgroup V)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange | exact GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.summand_baseChange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfShortExactStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_of_short_exact : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E E₁ E₂ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω E₁] [AddCommGroup E₂] [Module Ω E₂] (i : E₁ →ₗ[Ω] E) (q : E →ₗ[Ω] E₂), Function.Injective i → Function.Surjective q → LinearMap.range i = LinearMap.ker q → ∀ (L : AddSubgroup E) (r₁ r₂ : ℕ), LocFree R (r₁ + r₂) L → LocFree R r₂ (L.map q.toAddMonoidHom) → LocFree R r₁ (L.comap i.toAddMonoidHom) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel.main | exact GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.LocFreeKernel.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeSummandCriterionStatement
section
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_free_summand_criterion : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {V : Type} [AddCommGroup V] [Module Ω V] (U : Submodule Ω V) (N m : ℕ) (L : AddSubgroup V), LocFree R N L → (LocFree R m (L.map U.mkQ.toAddMonoidHom) → Summand L U) ∧ (Summand L U → LocFree R (Module.finrank Ω U) (L.comap U.subtype.toAddMonoidHom) ∧ LocFree R (N - Module.finrank Ω U) (L.map U.mkQ.toAddMonoidHom)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot | exact GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.summand_of_locFree_quot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeTestPointMembership
section
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.HaLattice

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) (p : ℕ), p.Prime → (p : Ω) ≠ 0 → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ {ι : Type} [Fintype ι] (N : ℕ) (L : AddSubgroup (ι → Ω)), LocFree R N L → ∀ v : ι → Ω, (∃ m : ℕ, (p : Ω) ^ m • v ∈ L) → (∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), IsTestPt p R RC → bcMap Ω C ι v ∈ spanOver RC (bcMap Ω C ι '' L)) → v ∈ L :=
  @PositivityTheory.Xgn.t_ha_lattice

end GlobalTheory.CompanionTheory.Ar.Num.HaLattice
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyOfFinitePresentationOfCancelStatement
section
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locallyOfFinitePresentation_of_cancel : ∀ {X Y S : Scheme.{0}} (q : X ⟶ Y) (f : Y ⟶ S), IsFinite q → Flat q → LocallyOfFinitePresentation q → Surjective q → LocallyOfFinitePresentation (q ≫ f) → LocallyOfFinitePresentation f := by
  first | exact @GlobalTheory.CompanionTheory.LfpDescent.descends | exact GlobalTheory.CompanionTheory.LfpDescent.descends | (intros; apply GlobalTheory.CompanionTheory.LfpDescent.descends <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleBasisLatticeBundleFreeStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Flat.DegCurve
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_basis_lattice_bundle_free : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (O ι k : Type) [CommRing O] [Fintype ι] [Field k] [Algebra k K] (b : Module.Basis ι ℤ O) (ρ : O →+* Module.End K V) (r : ℕ) (i : C.I), IsBun C L → (∀ c : k, C.v i (algebraMap k K c) ≤ 1) → (∃ x : Fin r → V, LinearIndependent K (fun q : Fin r × ι => ρ (b q.2) (x q.1)) ∧ ∀ y, y ∈ L i ↔ ∃ c : Fin r × ι → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • ρ (b q.2) (x q.1)) → FreeAt C k (act k ρ) L r i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice | exact GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.DegCurve.freeAt_of_basis_lattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ModuleFlatOfFlatAndFibreFlatStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.module_flat_of_flat_and_fibre_flat : ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B] [IsNoetherianRing R] [IsNoetherianRing A] [IsNoetherianRing B] [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B] [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)], Module.Flat R B → (Algebra.TensorProduct.map (AlgHom.id R (IsLocalRing.ResidueField R)) (IsScalarTower.toAlgHom R A B)).toRingHom.Flat → Module.Flat A B := by
  first | exact @GlobalTheory.CompanionTheory.Relay.module_flat_of_flat_and_fibre_flat | exact GlobalTheory.CompanionTheory.Relay.module_flat_of_flat_and_fibre_flat | (intros; apply GlobalTheory.CompanionTheory.Relay.module_flat_of_flat_and_fibre_flat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.NegDefBlockOfPosDef
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.Sylvester

theorem neg_posDef_of_compl_posDef : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (C : Matrix (Fin q) (Fin p ⊕ Fin q) ℂ), A.PosDef → B.IsHermitian → (-(C * Matrix.fromBlocks A 0 0 B * Cᴴ)).PosDef → (-B).PosDef :=
  @PositivityTheory.Xgf.negDef_block_of_posDef

end GlobalTheory.CompanionTheory.Ar.Fl.Sylvester
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundlesStatement
section
open GlobalTheory.CompanionTheory.Ar.Crv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sub_and_quotient_bundles : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L : C.I → AddSubgroup V) (W : Submodule K V), IsBun C L → IsBun C (sub C L W) ∧ IsBun C (quot C L W) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot | exact GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot | (intros; apply GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TwoMulFinrank
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT

open Module NumberField

namespace PtBasic

variable {C O : Type} [Field C] [CommRing O] [Algebra O C] {E : Type} [Field E] [NumberField E]
  {c : E ≃+* E} {κ : O} {N : ℕ}
  {V Ω : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]
  [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω]
  (P : HTPoint C O c κ N V Ω)

theorem ht_surjective : Function.Surjective P.ht := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← P.om_lat.span_eq_top, Submodule.span_le]
  intro y hy
  obtain ⟨x, -, hx⟩ := P.κ_mem y hy
  show y ∈ LinearMap.range P.ht
  rw [LinearMap.mem_range]
  refine ⟨(algebraMap O C κ)⁻¹ • x, ?_⟩
  rw [map_smul, hx, ← algebraMap_smul C κ y, smul_smul, inv_mul_cancel₀ P.κ_ne, one_smul]

theorem T_lattice : P.T.IsLattice C := by
  obtain ⟨-, hsp, hT⟩ := P.free
  refine ⟨?_, hsp⟩
  rw [hT]
  exact Submodule.fg_span (Set.finite_range _)

theorem rho_t_mem (a : 𝓞 E) (i : Fin N) : P.ρ a (P.t i) ∈ P.T := by
  obtain ⟨-, -, hT⟩ := P.free
  have hmem : ∀ k, P.ρ (RingOfIntegers.basis E k) (P.t i) ∈ P.T := fun k => by
    rw [hT]
    exact Submodule.subset_span ⟨(i, k), rfl⟩
  rw [← (RingOfIntegers.basis E).sum_repr a]
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
  exact Submodule.sum_mem _ fun k _ => zsmul_mem (hmem k) _

theorem T_stable (a : 𝓞 E) : ∀ x ∈ P.T, P.ρ a x ∈ P.T := by
  obtain ⟨-, -, hT⟩ := P.free
  have hle : P.T ≤ P.T.comap ((P.ρ a).restrictScalars O) := by
    nth_rewrite 1 [hT]
    rw [Submodule.span_le]
    rintro _ ⟨q, rfl⟩
    show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) ∈ P.T
    rw [show P.ρ a (P.ρ (RingOfIntegers.basis E q.2) (P.t q.1)) =
        (P.ρ a * P.ρ (RingOfIntegers.basis E q.2)) (P.t q.1) from rfl, ← map_mul]
    exact rho_t_mem P _ _
  exact fun x hx => hle hx

theorem ht_eigProj (σ : E →+* C) (x : V) :
    P.ht (eigProj P.ρ σ x) = eigProj P.ρΩ σ (P.ht x) := by
  simp only [eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, P.ht_lin]

theorem om'_lattice : P.om'.IsLattice C := by
  have hT := T_lattice P
  refine ⟨?_, ?_⟩
  · rw [HTPoint.om']
    exact hT.fg.map _
  · rw [HTPoint.om', Submodule.map_coe, LinearMap.coe_restrictScalars, ← Submodule.map_span,
      hT.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact ht_surjective P

theorem omHT_eq (σ : E →+* C) :
    P.omHT σ = (eigQuot P.ρ σ P.T).map (P.ht.restrictScalars O) := by
  have hcomm : ((eigProj P.ρΩ σ).restrictScalars O) ∘ₗ (P.ht.restrictScalars O) =
      (P.ht.restrictScalars O) ∘ₗ ((eigProj P.ρ σ).restrictScalars O) :=
    LinearMap.ext fun x => (ht_eigProj P σ x).symm
  show (P.T.map (P.ht.restrictScalars O)).map ((eigProj P.ρΩ σ).restrictScalars O) =
    (P.T.map ((eigProj P.ρ σ).restrictScalars O)).map (P.ht.restrictScalars O)
  rw [← Submodule.map_comp, ← Submodule.map_comp, hcomm]

theorem e_skew (x y : V) : P.e x y = - P.e y x := by
  have h := P.alt (x + y)
  simp only [map_add, LinearMap.add_apply, P.alt, zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_right h

theorem dualLat_flip : dualLat P.e.flip P.T = P.T := by
  conv_rhs => rw [← P.perfect]
  ext y
  simp only [LatBasic.mem_dualLat, LinearMap.flip_apply]
  refine forall₂_congr fun x _ => ?_
  rw [e_skew P y x, neg_mem_iff]
include P in
theorem finite_V : Module.Finite C V := by
  obtain ⟨s, hs⟩ := (T_lattice P).fg
  refine ⟨⟨s, ?_⟩⟩
  rw [← Submodule.span_span_of_tower O, hs, (T_lattice P).span_eq_top]
include P in
theorem two_mul_finrank : 2 * finrank C Ω = finrank C V := by
  haveI := finite_V P
  have hrefl : LinearMap.BilinForm.IsRefl P.e := fun x y h => by rw [e_skew P y x, h, neg_zero]
  have horth : LinearMap.BilinForm.orthogonal P.e (LinearMap.ker P.ht) = LinearMap.ker P.ht := by
    ext x
    simp only [LinearMap.BilinForm.mem_orthogonal_iff, LinearMap.BilinForm.isOrtho_def,
      LinearMap.mem_ker]
    rw [P.lagr x]
    refine forall₂_congr fun y _ => ?_
    rw [e_skew P y x, neg_eq_zero]
  have htop : LinearMap.BilinForm.orthogonal P.e ⊤ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hx
    exact (Submodule.mem_bot C).mpr (P.nondeg x fun y => hx y Submodule.mem_top)
  have h1 := LinearMap.BilinForm.finrank_add_finrank_orthogonal hrefl (LinearMap.ker P.ht)
  rw [horth, htop, inf_bot_eq, finrank_bot, add_zero] at h1
  have h2 := LinearMap.finrank_range_add_finrank_ker P.ht
  rw [LinearMap.range_eq_top.mpr (ht_surjective P), finrank_top] at h2
  omega

end PtBasic

theorem htPoint_basic : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [IsAlgClosed C] [CharZero C] (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (hc : ∀ x, c (c x) = x) (κ : O) (N : ℕ) (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (Ω : Type) [AddCommGroup Ω] [Module C Ω] [Module O Ω] [IsScalarTower O C Ω] (P : HTPoint C O c κ N V Ω), Function.Surjective P.ht ∧ P.T.IsLattice C ∧ (∀ (a : 𝓞 E), ∀ x ∈ P.T, P.ρ a x ∈ P.T) ∧ (∀ (σ : E →+* C) x, P.ht (eigProj P.ρ σ x) = eigProj P.ρΩ σ (P.ht x)) ∧ P.om'.IsLattice C ∧ (∀ σ : E →+* C, P.omHT σ = (eigQuot P.ρ σ P.T).map (P.ht.restrictScalars O)) ∧ dualLat P.e.flip P.T = P.T ∧ 2 * Module.finrank C Ω = Module.finrank C V := by
  intro C _ v O _ _ _ _ _ E _ _ c _ κ N V _ _ _ _ Ω _ _ _ _ P
  exact ⟨PtBasic.ht_surjective P, PtBasic.T_lattice P, PtBasic.T_stable P, PtBasic.ht_eigProj P,
    PtBasic.om'_lattice P, PtBasic.omHT_eq P, PtBasic.dualLat_flip P, PtBasic.two_mul_finrank P⟩

end GlobalTheory.CompanionTheory.Ar.HT
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.UltrametricDetNormLeStatement
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ultrametric_det_norm_le : ∀ (A : Type) [NormedField A] [IsUltrametricDist A] (I : Type) [Fintype I] [DecidableEq I] (M : Matrix I I A) (r : ℝ), 0 ≤ r → (∀ a b, ‖M a b‖ ≤ r) → ‖M.det‖ ≤ r ^ Fintype.card I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric | exact GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.norm_det_le_pow_card_of_ultrametric <;> assumption)
end

