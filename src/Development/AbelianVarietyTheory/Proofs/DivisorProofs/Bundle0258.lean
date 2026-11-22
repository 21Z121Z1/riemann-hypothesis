import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0166
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0155
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0114
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenAffineHilbertChartBasicLocus
section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff.Locus

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B] {r N : ℕ}

theorem secs_props {T : Scheme.{0}} (y : (functor A B r).obj (op T)) (U : T.Opens)
    (hU : IsAffineOpen U) :
    letI := ((proj y).app U).hom.toAlgebra
    Module.Finite Γ(T, U) Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) ∧
      Module.Flat Γ(T, U) Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) ∧
      ∀ q : PrimeSpectrum Γ(T, U), Module.rankAtStalk Γ(y.2.1.subscheme, proj y ⁻¹ᵁ U) q = r := by
  obtain ⟨h1, h2, h3⟩ := y.2.2
  exact GlobalTheory.T.sections_finite_flat_rank_of_isFinite_flat _ _ (proj y) r h3 U hU

theorem isOpen_bad_compl (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U) :
    IsOpen (bad e σ y U)ᶜ := by
  letI := ((proj y).app U).hom.toAlgebra
  haveI := (secs_props y U hU).1
  exact (Module.isClosed_support (R := Γ(T, U))).isOpen_compl

theorem isCompact_bad_compl (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U) :
    IsCompact (bad e σ y U)ᶜ := by
  letI := ((proj y).app U).hom.toAlgebra
  obtain ⟨h1, h2, h3⟩ := secs_props y U hU
  exact GlobalTheory.T.free_module_complement_support_compact _ _ r h3 (gens e σ y U)

theorem basic_iff (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) :
    Basic A B e σ y ↔ ∀ U : T.affineOpens, bad e σ y U = ∅ := by
  refine forall_congr' fun U => ?_
  letI := ((proj y).app U).hom.toAlgebra
  obtain ⟨h1, h2, h3⟩ := secs_props y U U.2
  have hf : (fun c : Fin r → Γ(T, U) => ∑ k, ((proj y).app U).hom (c k) * gens e σ y U k) =
      Fintype.linearCombination Γ(T, U) (gens e σ y U) := by
    ext c
    simp [Fintype.linearCombination_apply, Algebra.smul_def]
    rfl
  change Function.Bijective (fun c : Fin r → Γ(T, U) =>
    ∑ k, ((proj y).app U).hom (c k) * gens e σ y U k) ↔ _
  rw [hf]
  refine ⟨fun hb => ?_, fun hb => GlobalTheory.T.linearCombination_bijective_of_rankAtStalk_eq _ _ r h3 _ hb⟩
  show Module.support _ _ = ∅
  rw [Module.support_eq_empty_iff, Submodule.Quotient.subsingleton_iff,
    ← Fintype.range_linearCombination, LinearMap.range_eq_top]
  exact hb.2

theorem appLE_congr_eq {X Y : Scheme.{0}} {f g : X ⟶ Y} (e : f = g) (U : Y.Opens) (V : X.Opens)
    (h : V ≤ f ⁻¹ᵁ U) : f.appLE U V h = g.appLE U V (e ▸ h) := by
  subst e; rfl

theorem gens_pbMap (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T T' : Scheme.{0}}
    (a : T' ⟶ T) (y : (functor A B r).obj (op T)) (U : T.Opens) (U' : T'.Opens)
    (hleG : proj ((functor A B r).map a.op y) ⁻¹ᵁ U' ≤ pbMap a y ⁻¹ᵁ (proj y ⁻¹ᵁ U)) (k : Fin r) :
    ((pbMap a y).appLE (proj y ⁻¹ᵁ U) _ hleG).hom (gens e σ y U k) =
      gens e σ ((functor A B r).map a.op y) U' k := by
  simp only [gens]
  rw [← CommRingCat.comp_apply]
  erw [Scheme.Hom.appLE_comp_appLE]
  rw [appLE_congr_eq (pbMap_fst a y)]

theorem bad_nat (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T T' : Scheme.{0}}
    (a : T' ⟶ T) (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U)
    (U' : T'.Opens) (hU' : IsAffineOpen U') (h : U' ≤ a ⁻¹ᵁ U) (x : T') (hx : x ∈ U') :
    hU'.primeIdealOf ⟨x, hx⟩ ∈ bad e σ ((functor A B r).map a.op y) U' ↔
      hU.primeIdealOf ⟨a x, h hx⟩ ∈ bad e σ y U := by
  have sq := isPullback_pbMap a y
  have hleG : proj ((functor A B r).map a.op y) ⁻¹ᵁ U' ≤ pbMap a y ⁻¹ᵁ (proj y ⁻¹ᵁ U) := by
    intro z hz
    show (pbMap a y ≫ proj y) z ∈ U
    rw [sq.w, Scheme.Hom.comp_apply]
    exact h hz
  haveI : IsFinite (proj y) := y.2.2.1
  have hP := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance hU hU' h hleG
  have fin : ((proj y).app U).hom.Finite := (secs_props y U hU).1
  have H := GlobalTheory.T.mem_support_quotient_span_iff_of_isPushout' _ _ _ _ _ _ _ _ hP fin (gens e σ y U) (hU'.primeIdealOf ⟨x, hx⟩)
  rw [IsAffineOpen.comap_primeIdealOf_appLE U hU U' hU' h hx] at H
  have hg : (fun i => ((pbMap a y).appLE (proj y ⁻¹ᵁ U) _ hleG).hom (gens e σ y U i)) =
      gens e σ ((functor A B r).map a.op y) U' := funext (gens_pbMap e σ a y U U' hleG)
  rw [hg] at H
  exact H

theorem map_id_apply' {T : Scheme.{0}} (y : (functor A B r).obj (op T)) :
    (functor A B r).map (𝟙 T).op y = y := by
  rw [op_id, FunctorToTypes.map_id_apply]

theorem bad_local (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U₁ U₂ : T.Opens) (h₁ : IsAffineOpen U₁) (h₂ : IsAffineOpen U₂)
    (x : T) (hx₁ : x ∈ U₁) (hx₂ : x ∈ U₂) :
    h₁.primeIdealOf ⟨x, hx₁⟩ ∈ bad e σ y U₁ ↔ h₂.primeIdealOf ⟨x, hx₂⟩ ∈ bad e σ y U₂ := by
  obtain ⟨U₀, hU₀, hx₀, hle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) (show x ∈ U₁ ⊓ U₂ from ⟨hx₁, hx₂⟩)
  have k₁ := bad_nat e σ (𝟙 T) y U₁ h₁ U₀ hU₀ (fun z hz => (hle hz).1) x hx₀
  have k₂ := bad_nat e σ (𝟙 T) y U₂ h₂ U₀ hU₀ (fun z hz => (hle hz).2) x hx₀
  rw [map_id_apply'] at k₁ k₂
  exact k₁.symm.trans k₂

theorem primeIdealOf_fromSpec {T : Scheme.{0}} {U : T.Opens} (hU : IsAffineOpen U)
    (q : PrimeSpectrum Γ(T, U)) (h : hU.fromSpec q ∈ U) :
    hU.primeIdealOf ⟨hU.fromSpec q, h⟩ = q :=
  hU.fromSpec.isOpenEmbedding.injective (hU.fromSpec_primeIdealOf _)

theorem mem_goodSet_iff (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) (U : T.Opens) (hU : IsAffineOpen U) (x : T) (hx : x ∈ U) :
    x ∈ goodSet e σ y ↔ hU.primeIdealOf ⟨x, hx⟩ ∉ bad e σ y U := by
  constructor
  · intro hmem
    obtain ⟨U₁, q, hq, rfl⟩ := Set.mem_iUnion.mp hmem
    have h₁ : IsAffineOpen (U₁ : T.Opens) := U₁.2
    have hx₁ : h₁.fromSpec q ∈ (U₁ : T.Opens) := by
      rw [← SetLike.mem_coe, ← h₁.range_fromSpec]; exact ⟨q, rfl⟩
    have key : h₁.primeIdealOf ⟨h₁.fromSpec q, hx₁⟩ = q := primeIdealOf_fromSpec h₁ q hx₁
    rw [← bad_local e σ y U₁ U h₁ hU _ hx₁ hx, key]
    exact hq
  · intro hq
    exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, _, hq, hU.fromSpec_primeIdealOf _⟩

theorem goodSet_map (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T T' : Scheme.{0}}
    (a : T' ⟶ T) (y : (functor A B r).obj (op T)) (x : T') :
    x ∈ goodSet e σ ((functor A B r).map a.op y) ↔ a x ∈ goodSet e σ y := by
  obtain ⟨U, hU, hxU, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) (show a x ∈ (⊤ : T.Opens) from trivial)
  obtain ⟨U', hU', hxU', hle⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T'.isBasis_affineOpens) (show x ∈ a ⁻¹ᵁ U from hxU)
  rw [mem_goodSet_iff e σ _ U' hU' x hxU', mem_goodSet_iff e σ y U hU (a x) hxU,
    bad_nat e σ a y U hU U' hU' hle x hxU']

theorem isOpenMap_fromSpec {T : Scheme.{0}} {U : T.Opens} (hU : IsAffineOpen U) :
    IsOpenMap hU.fromSpec :=
  hU.fromSpec.isOpenEmbedding.isOpenMap

theorem isOpen_goodSet (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : IsOpen (goodSet e σ y) :=
  isOpen_iUnion fun U => isOpenMap_fromSpec U.2 _ (isOpen_bad_compl e σ y U U.2)

theorem basic_iff_goodSet (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) {T : Scheme.{0}}
    (y : (functor A B r).obj (op T)) : Basic A B e σ y ↔ goodSet e σ y = Set.univ := by
  rw [basic_iff, Set.eq_univ_iff_forall]
  constructor
  · intro h x
    obtain ⟨U, hU, hxU, -⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) (show x ∈ (⊤ : T.Opens) from trivial)
    rw [mem_goodSet_iff e σ y U hU x hxU, h ⟨U, hU⟩]
    exact Set.notMem_empty _
  · intro h U
    refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => ?_
    have hU : IsAffineOpen (U : T.Opens) := U.2
    have hx : hU.fromSpec q ∈ (U : T.Opens) := by
      rw [← SetLike.mem_coe, ← hU.range_fromSpec]; exact ⟨q, rfl⟩
    have := (mem_goodSet_iff e σ y U hU _ hx).mp (h _)
    rw [primeIdealOf_fromSpec hU q hx] at this
    exact this hq

theorem exists_basic_locus : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0})
    (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)), ∃ W : Z.Opens,
      (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Z), Set.range a ⊆ (W : Set Z) ↔
        GlobalTheory.HilbAff.Basic A B e σ ((GlobalTheory.HilbAff.functor A B r).map a.op y)) ∧
      (CompactSpace Z → IsCompact (W : Set Z)) := by
  intro A B _ _ _ N r e σ Z y
  refine ⟨⟨goodSet e σ y, isOpen_goodSet e σ y⟩, fun Z' a => ?_, fun hZ => ?_⟩
  · rw [basic_iff_goodSet, Set.eq_univ_iff_forall, Set.range_subset_iff]
    exact forall_congr' fun x => (goodSet_map e σ a y x).symm
  · have hcov : Set.univ ⊆ ⋃ U : Z.affineOpens, ((U : Z.Opens) : Set Z) := by
      intro x _
      obtain ⟨U, hU, hxU, -⟩ :=
        (TopologicalSpace.Opens.isBasis_iff_nbhd.mp Z.isBasis_affineOpens) (show x ∈ (⊤ : Z.Opens) from trivial)
      exact Set.mem_iUnion.mpr ⟨⟨U, hU⟩, hxU⟩
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover _ (fun U : Z.affineOpens => U.1.isOpen) hcov
    have heq : goodSet e σ y = ⋃ U ∈ t, U.2.fromSpec '' (bad e σ y U)ᶜ := by
      apply Set.Subset.antisymm
      · intro x hx
        obtain ⟨U, hUt, hxU⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
        refine Set.mem_iUnion₂.mpr ⟨U, hUt, _, (mem_goodSet_iff e σ y U U.2 x hxU).mp hx, ?_⟩
        exact U.2.fromSpec_primeIdealOf _
      · exact Set.iUnion₂_subset fun U _ => Set.subset_iUnion
          (fun U : Z.affineOpens => U.2.fromSpec '' (bad e σ y U)ᶜ) U
    show IsCompact (goodSet e σ y)
    rw [heq]
    exact t.isCompact_biUnion fun U _ =>
      (isCompact_bad_compl e σ y U U.2).image U.2.fromSpec.continuous

end GlobalTheory.HilbAff.Locus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyVanishingOfFibre
section
open IsLocalRing

namespace GlobalTheory.DenseSec
open TensorProduct

theorem exists_poly_vanishing_of_fibre : ∀ (R : Type) [CommRing R] (A : Type) [CommRing A] [Algebra R A] (g : ℕ) (t : Fin g → A) (h : A), GlobalTheory.DenseSec.EtChart R A t h → ∀ (Ω : Type) [Field Ω] [Algebra R Ω], IrreducibleSpace (PrimeSpectrum (TensorProduct R Ω A)) → ∀ f : TensorProduct R Ω A, ¬ IsNilpotent f → ∃ Q : MvPolynomial (Fin g) Ω, Q ≠ 0 ∧ ∀ a : A →ₐ[R] Ω, a h ≠ 0 → GlobalTheory.DenseSec.pt a f = 0 → MvPolynomial.eval (fun i => a (t i)) Q = 0 := by
  intro R _ A _ _ g t h hE Ω _ _ hirr f hf
  have hN : (nilradical (TensorProduct R Ω A)).IsPrime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.1 hirr
  have kill : ∀ (a : A →ₐ[R] Ω) (x : TensorProduct R Ω A), x ∈ nilradical (TensorProduct R Ω A) → GlobalTheory.DenseSec.pt a x = 0 := by
    intro a x hx
    exact ((mem_nilradical.1 hx).map (GlobalTheory.DenseSec.pt a)).eq_zero
  have pth : ∀ (a : A →ₐ[R] Ω) (x : A), GlobalTheory.DenseSec.pt a (1 ⊗ₜ[R] x) = a x := by
    intro a x
    simp [GlobalTheory.DenseSec.pt]
  have ptw : ∀ (a : A →ₐ[R] Ω) (w : Ω), GlobalTheory.DenseSec.pt a (w ⊗ₜ[R] 1) = w := by
    intro a w
    simp [GlobalTheory.DenseSec.pt]
  by_cases h1 : (1 ⊗ₜ[R] h : TensorProduct R Ω A) ∈ nilradical (TensorProduct R Ω A)
  · refine ⟨1, one_ne_zero, fun a ha _ => ?_⟩
    exact absurd (by rw [← pth a h]; exact kill a _ h1) ha
  set N := nilradical (TensorProduct R Ω A)
  set u : TensorProduct R Ω A ⧸ N := Ideal.Quotient.mk N (1 ⊗ₜ[R] h)
  have hu : u ≠ 0 := by
    simpa [u, Ideal.Quotient.eq_zero_iff_mem] using h1
  letI : IsDomain (TensorProduct R Ω A ⧸ N) := Ideal.Quotient.isDomain N
  have hle : Submonoid.powers u ≤ nonZeroDivisors (TensorProduct R Ω A ⧸ N) := powers_le_nonZeroDivisors_of_noZeroDivisors hu
  letI : IsDomain (Localization.Away u) := IsLocalization.isDomain_localization hle
  obtain ⟨hFT, hFU⟩ := GlobalTheory.T.etaleChart_localization_finiteType_formallyUnramified R A g t h hE Ω N
  letI : Algebra (MvPolynomial (Fin g) Ω) (Localization.Away u) :=
    (MvPolynomial.aeval (fun i => algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N (1 ⊗ₜ[R] t i)))).toRingHom.toAlgebra
  have hf' : algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N f) ≠ 0 := by
    intro h0
    rw [map_eq_zero_iff _ (IsLocalization.injective (Localization.Away u) hle), Ideal.Quotient.eq_zero_iff_mem] at h0
    exact hf (mem_nilradical.1 h0)
  obtain ⟨Q, hQ, d, hd⟩ := GlobalTheory.T.exists_ne_zero_algebraMap_eq_mul_of_formallyUnramified' (MvPolynomial (Fin g) Ω) (Localization.Away u) _ hf'
  refine ⟨Q, hQ, fun a ha hfa => ?_⟩
  let φ : TensorProduct R Ω A ⧸ N →+* Ω := Ideal.Quotient.lift N (GlobalTheory.DenseSec.pt a).toRingHom (fun x hx => kill a x hx)
  have hφu : IsUnit (φ u) := by
    simp only [φ, u, Ideal.Quotient.lift_mk]
    exact isUnit_iff_ne_zero.2 (by simpa [pth] using ha)
  let χ : Localization.Away u →+* Ω := IsLocalization.Away.lift u hφu
  have hχ : ∀ x : TensorProduct R Ω A, χ (algebraMap (TensorProduct R Ω A ⧸ N) (Localization.Away u) (Ideal.Quotient.mk N x)) = GlobalTheory.DenseSec.pt a x := by
    intro x
    simp [χ, φ, IsLocalization.Away.lift]
  have hP : χ.comp (algebraMap (MvPolynomial (Fin g) Ω) (Localization.Away u)) = MvPolynomial.eval₂Hom (RingHom.id Ω) (fun i => a (t i)) := by
    apply MvPolynomial.ringHom_ext
    · intro w
      show χ (MvPolynomial.aeval _ (MvPolynomial.C w)) = _
      have e : algebraMap Ω (TensorProduct R Ω A ⧸ N) w = Ideal.Quotient.mk N (w ⊗ₜ[R] 1) := rfl
      rw [MvPolynomial.aeval_C, IsScalarTower.algebraMap_apply Ω (TensorProduct R Ω A ⧸ N) (Localization.Away u), e, hχ, ptw]
      simp
    · intro i
      show χ (MvPolynomial.aeval _ (MvPolynomial.X i)) = _
      rw [MvPolynomial.aeval_X, hχ, pth]
      simp
  have := congrArg χ hd
  rw [← RingHom.comp_apply, hP, map_mul, hχ, hfa, zero_mul] at this
  exact this

end GlobalTheory.DenseSec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularNearOfRegularQuotientPrime
section
open IsLocalRing TensorProduct

namespace GlobalTheory.RegularAscent

open IsLocalRing TensorProduct in
private lemma spanFinrank_maximalIdeal_le_add (A : Type) [CommRing A] [IsLocalRing A]
    (J : Ideal A) [IsLocalRing (A ⧸ J)] (hJ : J.FG) (hm : (maximalIdeal (A ⧸ J)).FG) :
    (maximalIdeal A).spanFinrank ≤ J.spanFinrank + (maximalIdeal (A ⧸ J)).spanFinrank := by
  classical
  obtain ⟨T, hTc, hT⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hJ
  obtain ⟨U, hUc, hU⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hm
  let L : Finset A := U.image Quotient.out
  have hJm : J ≤ maximalIdeal A := by
    refine le_maximalIdeal fun h => ?_
    have : Subsingleton (A ⧸ J) := Ideal.Quotient.subsingleton_iff.mpr h
    exact not_subsingleton (A ⧸ J) this
  have hL : ∀ l ∈ L, l ∈ maximalIdeal A := by
    intro l hl
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hl
    have hu' : u ∈ maximalIdeal (A ⧸ J) := hU ▸ Ideal.subset_span hu
    intro hunit
    apply hu'
    have := hunit.map (Ideal.Quotient.mk J)
    rwa [Ideal.Quotient.mk_out] at this
  have hspan : maximalIdeal A = Ideal.span (↑(T ∪ L) : Set A) := by
    apply le_antisymm
    · intro x hx
      have hx' : Ideal.Quotient.mk J x ∈ Ideal.span (Ideal.Quotient.mk J '' (L : Set A)) := by
        have e : Ideal.Quotient.mk J '' (L : Set A) = (U : Set (A ⧸ J)) := by
          ext u; simp [L, Ideal.Quotient.mk_out]
        rw [e]
        change _ ∈ Submodule.span (A ⧸ J) _
        rw [hU]
        intro hunit
        obtain ⟨y, hy⟩ := hunit.exists_right_inv
        obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
        have h1 : x * y' - 1 ∈ J := Ideal.Quotient.eq.mp (by simpa using hy)
        apply (maximalIdeal.isMaximal A).ne_top
        rw [Ideal.eq_top_iff_one]
        simpa using Ideal.sub_mem _ (Ideal.mul_mem_right y' _ hx) (hJm h1)
      rw [← Ideal.map_span] at hx'
      obtain ⟨y, hy, hyx⟩ := Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective |>.mp hx'
      have hxy : x - y ∈ J := by
        rw [← Ideal.Quotient.eq]; exact hyx.symm
      rw [← hT] at hxy
      rw [Finset.coe_union, Ideal.span_union]
      have := Submodule.add_mem_sup hxy hy
      simpa using this
    · rw [Ideal.span_le]
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact hJm (hT ▸ Ideal.subset_span hx)
      · exact hL x hx
  calc (maximalIdeal A).spanFinrank ≤ (T ∪ L).card := hspan ▸ _root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le _
    _ ≤ T.card + L.card := Finset.card_union_le _ _
    _ ≤ J.spanFinrank + (maximalIdeal (A ⧸ J)).spanFinrank := by
        rw [hTc, ← hUc]; gcongr; exact Finset.card_image_le

open IsLocalRing TensorProduct in
private lemma height_add_ringKrullDim_quotient_le' (A : Type) [CommRing A] (I : Ideal A)
    [I.IsPrime] : (I.height : WithBot ℕ∞) + ringKrullDim (A ⧸ I) ≤ ringKrullDim A := by
  let P : PrimeSpectrum A := ⟨I, inferInstance⟩
  have h1 : I.height = Order.height P := PrimeSpectrum.height_eq_orderHeight P
  have h2 : ringKrullDim (A ⧸ I) = (Order.coheight P : WithBot ℕ∞) := by
    rw [ringKrullDim_quotient, Order.coheight_eq_krullDim_Ici]
    rfl
  have : Nonempty (PrimeSpectrum A) := ⟨P⟩
  rw [h1, h2, ringKrullDim, Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
  norm_cast
  exact le_iSup (fun a : PrimeSpectrum A => Order.height a + Order.coheight a) P

open IsLocalRing TensorProduct in

theorem _root_.GlobalTheory.RegularAscent.exists_regular_near_of_regular_quotient (B : Type) [CommRing B]
    [IsNoetherianRing B] (p : Ideal B) [p.IsPrime]
    (hp : IsRegularLocalRing (Localization.AtPrime p)) :
    ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q →
      IsRegularLocalRing
        (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) →
      IsRegularLocalRing (Localization.AtPrime q) := by
  classical
  have hmfg : (maximalIdeal (Localization.AtPrime p)).FG := IsNoetherian.noetherian _
  obtain ⟨U, hUc, hU⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hmfg
  choose f hf using fun u : Localization.AtPrime p => IsLocalization.surj p.primeCompl u
  let T : Finset B := U.image fun u => (f u).1
  have hTp : ∀ t ∈ T, t ∈ p := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p, ← hf u]
    exact Ideal.mul_mem_right _ _ (hU ▸ Ideal.subset_span hu)
  have hTspan : p.map (algebraMap B (Localization.AtPrime p)) =
      Ideal.span (algebraMap B (Localization.AtPrime p) '' T) := by
    rw [Localization.AtPrime.map_eq_maximalIdeal]
    apply le_antisymm
    · rw [← hU]
      change Ideal.span _ ≤ _
      rw [Ideal.span_le]
      intro u hu
      have hunit := IsLocalization.map_units (Localization.AtPrime p) (f u).2
      have e : u = algebraMap B _ (f u).1 * ↑hunit.unit⁻¹ := by
        rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec]; exact hf u
      rw [e]
      exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨(f u).1, Finset.mem_image_of_mem _ hu, rfl⟩)
    · rw [Ideal.span_le]
      rintro _ ⟨t, ht, rfl⟩
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ (hTp t ht)
  obtain ⟨V, hV⟩ := (IsNoetherian.noetherian p : p.FG)
  have hc : ∀ v ∈ V, ∃ c ∈ p.primeCompl, c * v ∈ Ideal.span (T : Set B) := by
    intro v hv
    rw [← IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p),
      Ideal.map_span, ← hTspan]
    exact Ideal.mem_map_of_mem _ (hV ▸ Ideal.subset_span hv)
  choose! c hcp hcT using hc
  have hg : ∀ x ∈ p, (∏ v ∈ V, c v) * x ∈ Ideal.span (T : Set B) := by
    have : Ideal.span {∏ v ∈ V, c v} * p ≤ Ideal.span (T : Set B) := by
      rw [← hV, Ideal.span_mul_span', Ideal.span_le]
      rintro _ ⟨a, ha, v, hv, rfl⟩
      rw [Set.mem_singleton_iff.mp ha, ← Finset.prod_erase_mul V c hv]
      change (∏ x ∈ V.erase v, c x) * c v * v ∈ Ideal.span (T : Set B)
      rw [mul_assoc]
      exact Ideal.mul_mem_left _ _ (hcT v hv)
    exact Ideal.span_singleton_mul_le_iff.mp this
  refine ⟨∏ v ∈ V, c v, p.primeCompl.prod_mem fun v hv => hcp v hv, ?_⟩
  intro q _ hpq hgq hreg
  have hdisj : Disjoint (q.primeCompl : Set B) p :=
    Set.disjoint_left.mpr fun x hxq hxp => hxq (hpq hxp)
  have hI : p.map (algebraMap B (Localization.AtPrime q)) =
      Ideal.span (algebraMap B (Localization.AtPrime q) '' T) := by
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have hu : IsUnit (algebraMap B (Localization.AtPrime q) (∏ v ∈ V, c v)) :=
        IsLocalization.map_units (Localization.AtPrime q) (⟨_, hgq⟩ : q.primeCompl)
      have h2 : algebraMap B (Localization.AtPrime q) ((∏ v ∈ V, c v) * x) ∈
          Ideal.span (algebraMap B (Localization.AtPrime q) '' T) := by
        rw [← Ideal.map_span]; exact Ideal.mem_map_of_mem _ (hg x hx)
      rw [map_mul] at h2
      exact (Ideal.unit_mul_mem_iff_mem _ hu).mp h2
    · rw [← Ideal.map_span]
      exact Ideal.map_mono (Ideal.span_le.mpr fun t ht => hTp t ht)
  have hIprime : (p.map (algebraMap B (Localization.AtPrime q))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hdisj
  have hIcard : (p.map (algebraMap B (Localization.AtPrime q))).spanFinrank ≤ T.card := by
    rw [hI, ← Finset.coe_image]
    exact (_root_.ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.spanFinrank_span_finset_le _).trans Finset.card_image_le
  have hTcard : (T.card : WithBot ℕ∞) ≤ (p.map (algebraMap B (Localization.AtPrime q))).height := by
    have h1 : (p.map (algebraMap B (Localization.AtPrime q))).height = p.height := by
      rw [← IsLocalization.height_under q.primeCompl,
        IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl _ ‹_› hdisj]
    have h2 : (p.height : WithBot ℕ∞) = (maximalIdeal (Localization.AtPrime p)).spanFinrank := by
      rw [← IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p),
        hp.spanFinrank_maximalIdeal]
    rw [h1, h2]
    exact_mod_cast (Finset.card_image_le.trans hUc.le)
  have := hreg.toIsLocalRing
  have hA := spanFinrank_maximalIdeal_le_add (Localization.AtPrime q)
    (p.map (algebraMap B (Localization.AtPrime q))) (IsNoetherian.noetherian _)
    (IsNoetherian.noetherian _)
  have hd := hreg.spanFinrank_maximalIdeal
  have hdim := height_add_ringKrullDim_quotient_le' (Localization.AtPrime q)
    (p.map (algebraMap B (Localization.AtPrime q)))
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  calc ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((T.card + (maximalIdeal (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q)))).spanFinrank : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast hA.trans (by omega)
    _ = (T.card : WithBot ℕ∞) + ringKrullDim (Localization.AtPrime q ⧸
          p.map (algebraMap B (Localization.AtPrime q))) := by
        push_cast; rw [hd]
    _ ≤ (p.map (algebraMap B (Localization.AtPrime q))).height + ringKrullDim
          (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q))) := by
        gcongr
    _ ≤ ringKrullDim (Localization.AtPrime q) := hdim

end GlobalTheory.RegularAscent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewHermitianMulAddDetNeZeroOfPairStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_skewHermitian_mul_add_det_ne_zero : ∀ (k : Type) [Field k] (σ : k →+* k), (∀ x, σ (σ x) = x) → ∀ ε : k, ε ≠ 0 → σ ε = -ε →
    ∀ (n : ℕ) (C D : Matrix (Fin n) (Fin n) k), C * (D.map σ)ᵀ + D * (C.map σ)ᵀ = 0 →
    (∀ a : Fin n → k, a ᵥ* C = 0 → a ᵥ* D = 0 → a = 0) →
      ∃ V : Matrix (Fin n) (Fin n) k, (V.map σ)ᵀ = -V ∧ (C * V + D).det ≠ 0 := by
  first | exact @GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair | exact GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair | (intros; apply GlobalTheory.exists_skewHermitian_mul_add_det_ne_zero_of_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallConjFixedOfValuationStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_conjFixed_of_valuation : ∀ (K : GlobalTheory.UnitLemma.UQ) (k : ℕ), 1 ≤ k → ∃ t : K.O, K.Small t ∧ GlobalTheory.UnitLemma.val K.O (algebraMap K.O K.E t) = k := by
  first | exact @GlobalTheory.UnitLemma.exists_small_val | exact GlobalTheory.UnitLemma.exists_small_val | (intros; apply GlobalTheory.UnitLemma.exists_small_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothSectionLiftBasicOpenAffineStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_section_lift_basicOpen_affine : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)), Smooth X.hom → ∀ g₀ : Sp R₀ ⟶ X.left, g₀ ≫ X.hom = spMap π →
    ∀ p : PrimeSpectrum R, ∃ f ∉ p.asIdeal, ∃ V : X.left.Opens, IsAffineOpen V ∧ GlobalTheory.SecLift.LiftIn π X g₀ f V := by
  first | exact @GlobalTheory.SecLift.exists_liftIn | exact GlobalTheory.SecLift.exists_liftIn | (intros; apply GlobalTheory.SecLift.exists_liftIn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulDvdOfLocalizationAtPrimeTensorStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smul_dvd_of_localization_atPrime_tensor' : ∀ (R C O : Type) [CommRing R] [CommRing C] [Algebra R C] [CommRing O] [Algebra R O]
    (Q : Ideal O) [Q.IsPrime] (b : R) (m : O ⊗[R] C),
    (∃ m' : Localization.AtPrime Q ⊗[R] C,
      (IsScalarTower.toAlgHom R O (Localization.AtPrime Q)).toLinearMap.rTensor C m = algebraMap R (Localization.AtPrime Q) b • m') →
    ∃ s ∉ Q, ∃ m' : O ⊗[R] C, s • m = algebraMap R O b • m' := by
  first | (exact @GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor) | (exact GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor) | (intros; apply GlobalTheory.exists_smul_dvd_of_localization_atPrime_tensor  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningImageLatticeStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spanning_image_lattice : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (V : Type) [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V] (h : ℕ) (π : (Fin h → C) →ₗ[C] V), Function.Surjective π → ∃ g : Fin h → V, Submodule.span C (Set.range g) = ⊤ ∧ Set.range (fun t : Fin h → O => π (fun i => algebraMap O C (t i))) = (Submodule.span O (Set.range g) : Set V) := by
  first | exact @GlobalTheory.image_integral_points_eq_span_of_surjective | exact GlobalTheory.image_integral_points_eq_span_of_surjective | (intros; apply GlobalTheory.image_integral_points_eq_span_of_surjective <;> assumption)
end

