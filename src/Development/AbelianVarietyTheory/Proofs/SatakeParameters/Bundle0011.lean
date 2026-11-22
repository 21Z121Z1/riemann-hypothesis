import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0003
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0006
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.LinearIndependentWave
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ImEmbeddingNeZeroOfNotMemRangeOfTotallyRealQuadrStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.im_embedding_ne_zero_of_not_mem_range_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w : InfinitePlace E) (θ : E), θ ∉ Set.range (algebraMap F E) → (w.embedding θ).im ≠ 0 := by
  first | exact @GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic | exact GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic | (intros; apply GlobalTheory.im_embedding_ne_zero_of_not_mem_range_of_totallyReal_quadratic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.InfinitePlaceEqOfEmbeddingCompAlgebraMapEqStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitePlace_eq_of_embedding_comp_algebraMap_eq' : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [IsTotallyComplex E] [Algebra.IsQuadraticExtension F E] (w₁ w₂ : InfinitePlace E), w₁.embedding.comp (algebraMap F E) = w₂.embedding.comp (algebraMap F E) → w₁ = w₂ := by
  first | exact @GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq | exact GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq | (intros; apply GlobalTheory.infinitePlace_eq_of_embedding_comp_algebraMap_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsComplOrthogonalOfNoCommonIrreducibleTypesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompl_orthogonal_of_no_common_irreducible_types : ∀ (K V : Type) [Group K] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ K V) (σ : K →* K), Function.Surjective σ → (∀ S : Subrepresentation ρ, IsAtom S → FiniteDimensional ℂ S.toSubmodule) → (∀ X : Subrepresentation ρ, X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule) → ∀ B : V →ₗ[ℂ] V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) → (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) → (∀ k φ ψ, B (ρ k φ) (ρ (σ k) ψ) = B φ ψ) → ∀ X Y : Subrepresentation ρ, IsCompl X.toSubmodule Y.toSubmodule → (∀ S₁ S₂ : Subrepresentation ρ, IsAtom S₁ → IsAtom S₂ → S₁ ≤ Y → S₂ ≤ X → IsEmpty (S₁.toRepresentation.Equiv S₂.toRepresentation)) → IsCompl (⨅ y ∈ Y.toSubmodule, LinearMap.ker (B y)) (⨅ x ∈ X.toSubmodule, LinearMap.ker (B x)) := by
  first | exact @GlobalTheory.IsotypicOrth.orth_isCompl | exact GlobalTheory.IsotypicOrth.orth_isCompl | (intros; apply GlobalTheory.IsotypicOrth.orth_isCompl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIndEtaleTensorProductLeft
section
open CategoryTheory

namespace GlobalTheory

theorem isIndEtale_tensorProduct_left (C A M : Type) [CommRing C] [CommRing A] [CommRing M]
    [Algebra C A] [Algebra C M] (h : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap C A)) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap M (TensorProduct C M A)) := by
  haveI : (RingHom.toMorphismProperty @RingHom.Etale).IsStableUnderCobaseChange :=
    RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
      RingHom.Etale.isStableUnderBaseChange
  exact MorphismProperty.of_isPushout (P := MorphismProperty.ind.{0}
    (RingHom.toMorphismProperty @RingHom.Etale))
    (CommRingCat.isPushout_tensorProduct C M A) h

example : ∀ (C A M : Type) [CommRing C] [CommRing A] [CommRing M] [Algebra C A] [Algebra C M],
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap C A) →
      GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (algebraMap M (TensorProduct C M A)) :=
  @isIndEtale_tensorProduct_left

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsReducedQuotientOfArtinianOfMaximalLeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isReduced_quotient_of_artinian_of_maximal_le' : ∀ (A : Type) [CommRing A] (I : Ideal A), IsArtinianRing (A ⧸ I) →
    (∀ m : Ideal A, m.IsMaximal → I ≤ m → m ≤ I ⊔ m ^ 2) → IsReduced (A ⧸ I) := by
  first | (exact @GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (exact GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le) | (intros; apply GlobalTheory.isReduced_quotient_of_artinian_of_maximal_le  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSemisimpleOfLocallyFiniteCompactGroup
section
namespace GlobalTheory.LocFinSemisimple

variable {K V : Type} [Group K] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ K V}

theorem exists_isAtom_le : ∀ (n : ℕ) (Y : Subrepresentation ρ),
    FiniteDimensional ℂ Y.toSubmodule → Module.finrank ℂ Y.toSubmodule = n → Y ≠ ⊥ →
      ∃ T : Subrepresentation ρ, IsAtom T ∧ T ≤ Y := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Y hY hn hne
    by_cases hA : IsAtom Y
    · exact ⟨Y, hA, le_rfl⟩
    · have : ∃ Z, Z < Y ∧ Z ≠ ⊥ := by
        by_contra hc
        push_neg at hc
        exact hA ⟨hne, hc⟩
      obtain ⟨Z, hZY, hZ⟩ := this
      have hlt : Z.toSubmodule < Y.toSubmodule :=
        lt_of_le_of_ne hZY.le fun h => hZY.ne (Subrepresentation.toSubmodule_injective h)
      have hZf : FiniteDimensional ℂ Z.toSubmodule := Submodule.finiteDimensional_of_le hlt.le
      have hr := Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨T, hT, hTZ⟩ := ih _ (hn ▸ hr) Z hZf rfl hZ
      exact ⟨T, hT, hTZ.trans hZY.le⟩

def ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U) : Subrepresentation ρ :=
  ⟨U, fun k _ hu => hU k _ hu⟩

variable [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]

theorem isSemisimple_ofInvariant (U : Submodule ℂ V) (hU : ∀ k, ∀ u ∈ U, ρ k u ∈ U)
    (hfd : FiniteDimensional ℂ U)
    (hc : ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) :
    (ofInvariant U hU).toRepresentation.IsSemisimpleRepresentation := by
  haveI : FiniteDimensional ℂ (ofInvariant U hU).toSubmodule := hfd
  refine GlobalTheory.isSemisimpleRepresentation_of_continuous_coeff _ fun l v => ?_
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := U) l
  have h : ∀ k, l ((ofInvariant U hU).toRepresentation k v) = g (ρ k v) := fun k => by
    rw [← hg]; rfl
  simp only [h]
  exact hc g v v.2

theorem le_iSup_atoms
    (H : ∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧ (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧
      ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u))
    (X : Subrepresentation ρ) :
    X.toSubmodule ≤ ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  set N := ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule with hNdef
  have hNX : N ≤ X.toSubmodule := iSup₂_le fun S hS => hS.2
  have hNinv : ∀ k, ∀ x ∈ N, ρ k x ∈ N := by
    intro k
    have : N ≤ N.comap (ρ k) := iSup₂_le fun S hS x hx =>
      (le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) S hS)
        (S.apply_mem_toSubmodule k hx)
    exact fun x hx => this hx
  intro x hxX
  obtain ⟨U, hxU, hfd, hU, hc⟩ := H x
  let R := ofInvariant U hU
  haveI : ComplementedLattice (Subrepresentation R.toRepresentation) :=
    isSemisimple_ofInvariant U hU hfd hc
  let W : Subrepresentation R.toRepresentation :=
    ⟨N.comap U.subtype, fun k w hw => hNinv k _ hw⟩
  obtain ⟨W', hW'⟩ := exists_isCompl W
  have hdis : W.toSubmodule ⊓ W'.toSubmodule = ⊥ :=
    congrArg Subrepresentation.toSubmodule hW'.inf_eq_bot
  have hsup : W.toSubmodule ⊔ W'.toSubmodule = ⊤ :=
    congrArg Subrepresentation.toSubmodule hW'.sup_eq_top
  let Xc : Submodule ℂ U := X.toSubmodule.comap U.subtype
  let Y : Subrepresentation ρ := ⟨(W'.toSubmodule ⊓ Xc).map U.subtype, by
    rintro k _ ⟨u, ⟨hu1, hu2⟩, rfl⟩
    exact ⟨R.toRepresentation k u, ⟨W'.apply_mem_toSubmodule k hu1,
      X.apply_mem_toSubmodule k hu2⟩, rfl⟩⟩
  have hY : Y = ⊥ := by
    by_contra hne
    haveI : FiniteDimensional ℂ Y.toSubmodule := Submodule.finiteDimensional_of_le
      (S₂ := U) (fun y hy => by obtain ⟨u, _, rfl⟩ := Submodule.mem_map.1 hy; exact u.2)
    obtain ⟨T, hT, hTY⟩ := exists_isAtom_le _ Y this rfl hne
    have hTX : T ≤ X := by
      intro t ht
      obtain ⟨u, ⟨_, hu2⟩, rfl⟩ := hTY ht
      exact hu2
    have hTN : T.toSubmodule ≤ N :=
      le_iSup₂ (f := fun (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X) => S.toSubmodule) T ⟨hT, hTX⟩
    have hT0 : T.toSubmodule ≠ ⊥ := fun h => hT.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨t, ht, ht0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT0
    obtain ⟨u, ⟨hu1, _⟩, rfl⟩ := hTY ht
    have hu : u ∈ W.toSubmodule ⊓ W'.toSubmodule := ⟨hTN ht, hu1⟩
    rw [hdis] at hu
    have hu0 : ((u : R.toSubmodule) : V) = 0 :=
      congrArg Subtype.val ((Submodule.mem_bot ℂ (M := R.toSubmodule) (x := u)).1 hu)
    exact ht0 hu0
  have hx' : (⟨x, hxU⟩ : R.toSubmodule) ∈ W.toSubmodule ⊔ W'.toSubmodule := by rw [hsup]; trivial
  obtain ⟨w, hw, w', hw', hww⟩ := Submodule.mem_sup.1 hx'
  have hsum : (w : V) + (w' : V) = x := congrArg Subtype.val hww
  have hw'X : w' ∈ Xc := by
    have h1 : (w : V) ∈ X.toSubmodule := hNX hw
    have h2 : (w' : V) = x - w := by
      rw [← hsum]; abel
    show (w' : V) ∈ X.toSubmodule
    rw [h2]
    exact X.toSubmodule.sub_mem hxX h1
  have hw'0 : (w' : V) ∈ Y.toSubmodule := ⟨w', ⟨hw', hw'X⟩, rfl⟩
  rw [hY] at hw'0
  have : (w' : V) = 0 := (Submodule.mem_bot ℂ).1 hw'0
  have hxw : x = w := by
    rw [← hsum, ‹(w' : V) = 0›, add_zero]
  rw [hxw]
  exact hw

theorem semisimple_of_locallyFinite : ∀ (K V : Type) [Group K] [TopologicalSpace K]
    [IsTopologicalGroup K] [CompactSpace K] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ K V), (∀ v : V, ∃ U : Submodule ℂ V, v ∈ U ∧ FiniteDimensional ℂ U ∧
      (∀ k, ∀ u ∈ U, ρ k u ∈ U) ∧ ∀ (ℓ : Module.Dual ℂ V), ∀ u ∈ U, Continuous fun k => ℓ (ρ k u)) →
    ρ.IsSemisimpleRepresentation ∧ (∀ S : Subrepresentation ρ, IsAtom S →
      FiniteDimensional ℂ S.toSubmodule) ∧ ∀ X : Subrepresentation ρ,
        X.toSubmodule = ⨆ (S : Subrepresentation ρ) (_ : IsAtom S ∧ S ≤ X), S.toSubmodule := by
  intro K V _ _ _ _ _ _ ρ H
  have hle := le_iSup_atoms H
  refine ⟨?_, ?_, fun X => le_antisymm (hle X) (iSup₂_le fun S hS => hS.2)⟩
  · rw [Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule,
      ← sSup_simples_eq_top_iff_isSemisimpleModule]
    let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := ρ)
    set s := sSup {m : Submodule (MonoidAlgebra ℂ K) ρ.asModule |
      IsSimpleModule (MonoidAlgebra ℂ K) m} with hs
    have hZ : (e.symm s).toSubmodule = ⊤ := by
      refine eq_top_iff.2 ((hle ⊤).trans (iSup₂_le fun S hS => ?_))
      have : S ≤ e.symm s := e.le_symm_apply.2
        (le_sSup (isSimpleModule_iff_isAtom.2 ((e.isAtom_iff S).2 hS.1)))
      exact this
    have h1 : e.symm s = ⊤ := Subrepresentation.toSubmodule_injective hZ
    rw [← e.apply_symm_apply s, h1, e.map_top]
  · intro S hS
    have hS0 : S.toSubmodule ≠ ⊥ := fun h => hS.1 (Subrepresentation.toSubmodule_injective h)
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
    obtain ⟨U, hvU, hfd, hU, -⟩ := H v
    rcases hS.le_iff.1 (inf_le_left : S ⊓ ofInvariant U hU ≤ S) with h | h
    · have hm : v ∈ (S ⊓ ofInvariant U hU).toSubmodule := ⟨hv, hvU⟩
      rw [h] at hm
      exact absurd ((Submodule.mem_bot ℂ).1 hm) hv0
    · have hSU : S.toSubmodule ≤ U := by
        rw [← h]; exact fun x hx => hx.2
      exact Submodule.finiteDimensional_of_le hSU

end GlobalTheory.LocFinSemisimple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthLeOfForallFgSubmoduleLengthLeStatement
section
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_le_of_forall_fg_submodule_length_le : ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (b : ℕ∞), (∀ N : Submodule O M, N.FG → Module.length O N ≤ b) → Module.length O M ≤ b := by
  first | exact @GlobalTheory.length_le_of_forall_fg_length_le | exact GlobalTheory.length_le_of_forall_fg_length_le | (intros; apply GlobalTheory.length_le_of_forall_fg_length_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientScalarMulStatement
section
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_quotient_scalar_mul : ∀ (O M : Type) [CommRing O] [Nontrivial O] [AddCommGroup M] [Module O M] [Module.Free O M] [Module.Finite O M] (a : O), Module.length O (M ⧸ LinearMap.range (a • (LinearMap.id : M →ₗ[O] M))) = (Module.finrank O M : ℕ∞) * Module.length O (O ⧸ Ideal.span {a}) := by
  first | exact @GlobalTheory.length_quot_smul_range_finite_free | exact GlobalTheory.length_quot_smul_range_finite_free | (intros; apply GlobalTheory.length_quot_smul_range_finite_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSmulSupLeIntermediateStatement
section
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_quotient_smul_sup_le_intermediate : ∀ (O A : Type) [CommRing O] [AddCommGroup A] [Module O A] (Z B B' : Submodule O A) (a : O), B ≤ B' → Module.length O (↥Z ⧸ (Z.map (a • (LinearMap.id : A →ₗ[O] A)) ⊔ B).comap Z.subtype) ≤ Module.length O ((↥Z ⧸ B'.comap Z.subtype) ⧸ LinearMap.range (a • (LinearMap.id : (↥Z ⧸ B'.comap Z.subtype) →ₗ[O] (↥Z ⧸ B'.comap Z.subtype)))) + Module.length O (↥(Z ⊓ B') ⧸ B.comap (Z ⊓ B').subtype) := by
  first | exact @GlobalTheory.length_quotient_smul_sup_le | exact GlobalTheory.length_quotient_smul_sup_le | (intros; apply GlobalTheory.length_quotient_smul_sup_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LengthQuotientSpanPowLeMulLengthStatement
section
open Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.length_quotient_span_pow_le_mul_length : ∀ (O : Type) [CommRing O] (p : O) (n : ℕ), Module.length O (O ⧸ Ideal.span {p ^ n}) ≤ (n : ℕ∞) * Module.length O (O ⧸ Ideal.span {p}) := by
  first | exact @GlobalTheory.main | exact GlobalTheory.main | (intros; apply GlobalTheory.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemSpanTranslatesOfFixedLattice
section
noncomputable section

namespace GlobalTheory.FourierSpan

variable {G : Type} [AddCommGroup G]

def annihIn (χ : G → G → ℂ) (hχ : GlobalTheory.PlaceModel.IsBichar χ) (Yh L : AddSubgroup G) : AddSubgroup G where
  carrier := {y | y ∈ Yh ∧ ∀ x ∈ L, χ x y = 1}
  add_mem' := fun {a b} ha hb => ⟨Yh.add_mem ha.1 hb.1, fun x hx => by rw [hχ.right, ha.2 x hx, hb.2 x hx, one_mul]⟩
  zero_mem' := ⟨Yh.zero_mem, fun x _ => hχ.zero_right x⟩
  neg_mem' := fun {a} ha => ⟨Yh.neg_mem ha.1, fun x hx => by
    have e : χ x (-a) * χ x a = 1 := by rw [← hχ.right, neg_add_cancel, hχ.zero_right]
    rwa [ha.2 x hx, mul_one] at e⟩

theorem bichar_pow_left {χ : G → G → ℂ} (hχ : GlobalTheory.PlaceModel.IsBichar χ) (k : ℕ) (x y : G) :
    χ (k • x) y = χ x y ^ k := by
  induction k with
  | zero => simp [hχ.zero_left]
  | succ k ih => rw [succ_nsmul, hχ.left, ih, pow_succ]

theorem mem_span_translates_of_fixed {G V : Type} [AddCommGroup G] [AddCommGroup V] [Module ℂ V]
    (χ : G → G → ℂ) (hχ : GlobalTheory.PlaceModel.IsBichar χ) (ρ : G → V →ₗ[ℂ] V) (X Yh L L' K : AddSubgroup G)
    (hLL' : L ≤ L') (hL'X : L' ≤ X) (hKY : K ≤ Yh) (ρ0 : ∀ v, ρ 0 v = v)
    (ρX : ∀ x ∈ X, ∀ x' ∈ X, ∀ v, ρ x (ρ x' v) = ρ (x + x') v)
    (ρY : ∀ y ∈ Yh, ∀ y' ∈ Yh, ∀ v, ρ y (ρ y' v) = ρ (y + y') v)
    (ρXY : ∀ x ∈ X, ∀ y ∈ Yh, ∀ v, ρ x (ρ y v) = χ x y • ρ y (ρ x v))
    (hR : ∃ R : Finset G, ∀ t ∈ L', ∃ r ∈ R, t - r ∈ L)
    (hLK : ∀ x ∈ L', ∀ y ∈ K, χ x y = 1)
    (hsep : ∀ y ∈ Yh, (∀ x ∈ L', χ x y = 1) → y ∈ K)
    (W : Submodule ℂ V) (hWX : ∀ v ∈ W, ∀ x ∈ X, ρ x v ∈ W) (hWY : ∀ v ∈ W, ∀ y ∈ Yh, ρ y v ∈ W)
    (f : V) (hfW : f ∈ W) (hfL : ∀ x ∈ L, ρ x f = f) (hfK : ∀ y ∈ K, ρ y f = f) :
    f ∈ Submodule.span ℂ {v | ∃ r ∈ X, ∃ g ∈ W, (∀ x ∈ L, ρ x g = g) ∧
      (∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y g = g) ∧ v = ρ r g} := by
  classical
  obtain ⟨R, hR⟩ := hR
  have negR : ∀ x y, χ x (-y) * χ x y = 1 := fun x y => by rw [← hχ.right, neg_add_cancel, hχ.zero_right]
  set P := annihIn χ hχ Yh L with hPdef
  have memP : ∀ y, y ∈ P ↔ y ∈ Yh ∧ ∀ x ∈ L, χ x y = 1 := fun y => Iff.rfl
  have hPY : ∀ y ∈ P, y ∈ Yh := fun y hy => ((memP y).1 hy).1
  have hKP : K ≤ P := fun y hy => (memP y).2 ⟨hKY hy, fun x hx => hLK x (hLL' hx) y hy⟩

  have wdQ : ∀ y ∈ P, ∀ u v : L', (QuotientAddGroup.mk u : L' ⧸ L.addSubgroupOf L') = QuotientAddGroup.mk v →
      χ u y = χ v y := by
    intro y hy u v huv
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at huv
    have e : (v : G) = u + ((-u + v : L') : G) := by simp
    rw [e, hχ.left, ((memP y).1 hy).2 _ huv, mul_one]
  have wdQ' : ∀ h : V, (∀ k ∈ K, ρ k h = h) → ∀ u v : P,
      (QuotientAddGroup.mk u : P ⧸ K.addSubgroupOf P) = QuotientAddGroup.mk v → ρ u h = ρ v h := by
    intro h hh u v huv
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf] at huv
    have e : (v : G) = u + ((-u + v : P) : G) := by simp
    rw [e, ← ρY _ (hPY _ u.2) _ (hKY huv), hh _ huv]

  have finQ : Finite (L' ⧸ L.addSubgroupOf L') := by
    let φ : R → L' ⧸ L.addSubgroupOf L' := fun r =>
      if h : (r : G) ∈ L' then QuotientAddGroup.mk ⟨r, h⟩ else 0
    refine Finite.of_surjective φ ?_
    intro q
    obtain ⟨t, rfl⟩ := QuotientAddGroup.mk_surjective q
    obtain ⟨r, hr, htr⟩ := hR t t.2
    have hrL' : r ∈ L' := by
      have := L'.sub_mem t.2 (hLL' htr)
      simpa using this
    refine ⟨⟨r, hr⟩, ?_⟩
    simp only [φ, dif_pos hrL']
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg]
    convert htr using 1
    simp only
    abel
  letI : Fintype (L' ⧸ L.addSubgroupOf L') := Fintype.ofFinite _
  set n := Fintype.card (L' ⧸ L.addSubgroupOf L') with hn_def
  have hn : 0 < n := Fintype.card_pos
  have powQ : ∀ y ∈ P, ∀ u : L', χ u y ^ n = 1 := by
    intro y hy u
    have hnu : ((n • u : L') : G) ∈ L := by
      have h0 : n • (QuotientAddGroup.mk u : L' ⧸ L.addSubgroupOf L') = 0 := card_nsmul_eq_zero
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0
      exact h0
    rw [← bichar_pow_left hχ, ← AddSubgroup.coe_nsmul]
    exact ((memP y).1 hy).2 _ hnu

  have finS : ({z : ℂ | z ^ n = 1} : Set ℂ).Finite :=
    (Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.subset fun z hz => by
      simp only [Finset.mem_coe, Multiset.mem_toFinset]
      exact (Polynomial.mem_nthRoots hn).2 hz
  haveI := finS.to_subtype
  have finQ' : Finite (P ⧸ K.addSubgroupOf P) := by
    let Φ : (P ⧸ K.addSubgroupOf P) → ((L' ⧸ L.addSubgroupOf L') → ({z : ℂ | z ^ n = 1} : Set ℂ)) :=
      fun q' q => ⟨χ (q.out : L') (q'.out : P), powQ _ (q'.out).2 _⟩
    refine Finite.of_injective Φ ?_
    intro a b hab
    rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' b, QuotientAddGroup.eq,
      AddSubgroup.mem_addSubgroupOf]
    refine hsep _ (hPY _ (-a.out + b.out : P).2) fun x hx => ?_
    have e := congrArg Subtype.val (congrFun hab (QuotientAddGroup.mk ⟨x, hx⟩))
    simp only [Φ] at e
    have ea := wdQ _ (a.out).2 ((QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L').out) ⟨x, hx⟩
      (QuotientAddGroup.out_eq' _)
    have eb := wdQ _ (b.out).2 ((QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L').out) ⟨x, hx⟩
      (QuotientAddGroup.out_eq' _)
    rw [ea, eb] at e
    rw [AddSubgroup.coe_add, AddSubgroup.coe_neg, hχ.right, ← e]
    exact negR _ _
  letI : Fintype (P ⧸ K.addSubgroupOf P) := Fintype.ofFinite _

  have hKh : ∀ r ∈ L', ∀ k ∈ K, ρ k (ρ (-r) f) = ρ (-r) f := by
    intro r hr k hk
    have := ρXY (-r) (X.neg_mem (hL'X hr)) k (hKY hk) f
    rw [hfK k hk, hLK _ (L'.neg_mem hr) k hk, one_smul] at this
    exact this.symm
  let g : (L' ⧸ L.addSubgroupOf L') → V := fun q =>
    ∑ q' : P ⧸ K.addSubgroupOf P, ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)
  have gW : ∀ q, g q ∈ W := fun q => Submodule.sum_mem _ fun q' _ =>
    hWY _ (hWX f hfW _ (X.neg_mem (hL'X (q.out).2))) _ (hPY _ (q'.out).2)
  have gL : ∀ q, ∀ x ∈ L, ρ x (g q) = g q := by
    intro q x hx
    simp only [g, map_sum]
    refine Finset.sum_congr rfl fun q' _ => ?_
    have hxX : x ∈ X := hL'X (hLL' hx)
    have hrX : -((q.out : L') : G) ∈ X := X.neg_mem (hL'X (q.out).2)
    rw [ρXY x hxX _ (hPY _ (q'.out).2), ((memP _).1 (q'.out).2).2 x hx, one_smul, ρX x hxX _ hrX, add_comm,
      ← ρX _ hrX _ hxX, hfL x hx]
  have gP : ∀ q, ∀ y ∈ Yh, (∀ x ∈ L, χ x y = 1) → ρ y (g q) = g q := by
    intro q y hy hyL
    have hyP : y ∈ P := (memP y).2 ⟨hy, hyL⟩
    simp only [g, map_sum]
    refine Eq.trans ?_ (Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ⟨y, hyP⟩ : P ⧸ K.addSubgroupOf P))
      (fun q' : P ⧸ K.addSubgroupOf P => ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)))
    refine Finset.sum_congr rfl fun q' _ => ?_
    simp only [Equiv.coe_addRight]
    rw [ρY y hy _ (hPY _ (q'.out).2), ← wdQ' _ (hKh _ (q.out).2) (q'.out + ⟨y, hyP⟩) _ ?_]
    · rw [AddSubgroup.coe_add, add_comm]
    · rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
  have key : ∑ q : L' ⧸ L.addSubgroupOf L', ρ ((q.out : L') : G) (g q) = (n : ℂ) • f := by
    have step : ∀ q : L' ⧸ L.addSubgroupOf L', ∀ q' : P ⧸ K.addSubgroupOf P,
        ρ ((q.out : L') : G) (ρ ((q'.out : P) : G) (ρ (-((q.out : L') : G)) f)) =
          χ ((q.out : L') : G) ((q'.out : P) : G) • ρ ((q'.out : P) : G) f := by
      intro q q'
      have hrX := hL'X (q.out).2
      rw [ρXY _ hrX _ (hPY _ (q'.out).2), ρX _ hrX _ (X.neg_mem hrX), add_neg_cancel, ρ0]
    simp only [g, map_sum, step]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single (0 : P ⧸ K.addSubgroupOf P)]
    · have h0K : (((0 : P ⧸ K.addSubgroupOf P).out : P) : G) ∈ K := by
        have := QuotientAddGroup.out_eq' (0 : P ⧸ K.addSubgroupOf P)
        rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at this
        exact this
      have h1 : ∀ q : L' ⧸ L.addSubgroupOf L',
          χ ((q.out : L') : G) (((0 : P ⧸ K.addSubgroupOf P).out : P) : G) = 1 :=
        fun q => hLK _ (q.out).2 _ h0K
      rw [hfK _ h0K]
      simp only [h1, Finset.sum_const, Finset.card_univ, ← hn_def, nsmul_eq_mul, mul_one]
    · intro q' _ hq'
      have hnK : ((q'.out : P) : G) ∉ K := by
        intro hK
        apply hq'
        rw [← QuotientAddGroup.out_eq' q', QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
        exact hK
      obtain ⟨x, hx, hxy⟩ : ∃ x ∈ L', χ x ((q'.out : P) : G) ≠ 1 := by
        by_contra hc
        push_neg at hc
        exact hnK (hsep _ (hPY _ (q'.out).2) hc)
      have hyP := (q'.out).2
      have shift : ∀ q : L' ⧸ L.addSubgroupOf L',
          χ (((q + (QuotientAddGroup.mk (⟨x, hx⟩ : L') : L' ⧸ L.addSubgroupOf L')).out : L') : G) ((q'.out : P) : G) =
            χ ((q.out : L') : G) ((q'.out : P) : G) * χ x ((q'.out : P) : G) := by
        intro q
        rw [← wdQ _ hyP (q.out + (⟨x, hx⟩ : L')) _ ?_, AddSubgroup.coe_add, hχ.left]
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq', QuotientAddGroup.out_eq']
      have hS2 := Equiv.sum_comp (Equiv.addRight (QuotientAddGroup.mk ⟨x, hx⟩ : L' ⧸ L.addSubgroupOf L'))
        (fun q : L' ⧸ L.addSubgroupOf L' => χ ((q.out : L') : G) ((q'.out : P) : G))
      simp only [Equiv.coe_addRight, shift, ← Finset.sum_mul] at hS2
      have hsum : ∑ q : L' ⧸ L.addSubgroupOf L', χ ((q.out : L') : G) ((q'.out : P) : G) = 0 := by
        have h3 : (∑ q : L' ⧸ L.addSubgroupOf L', χ ((q.out : L') : G) ((q'.out : P) : G)) *
            (χ x ((q'.out : P) : G) - 1) = 0 := by
          rw [mul_sub, hS2, mul_one, sub_self]
        exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hxy)
      rw [hsum, zero_smul]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hf : f = (n : ℂ)⁻¹ • ∑ q : L' ⧸ L.addSubgroupOf L', ρ ((q.out : L') : G) (g q) := by
    rw [key, smul_smul, inv_mul_cancel₀ hn0, one_smul]
  rw [hf]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => Submodule.subset_span ?_)
  exact ⟨_, hL'X (q.out).2, g q, gW q, gL q, gP q, rfl⟩
end GlobalTheory.FourierSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormLeOfRecurrenceGrowthStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_le_of_recurrence_growth' : ∀ (β : Multiset ℂ) (a : ℕ → ℂ) (C B : ℝ) (m : ℕ), 0 < B → a 0 = 1 → (∀ n, 1 ≤ n → ∑ k ∈ Finset.range (n + 1), (-1 : ℂ) ^ k * β.esymm k * a (n - k) = 0) → (∀ n, ‖a n‖ ≤ C * ((n : ℝ) + 1) ^ m * B ^ n) → ∀ b ∈ β, ‖b‖ ≤ B := by
  first | exact @GlobalTheory.norm_le_of_recurrence_growth | exact GlobalTheory.norm_le_of_recurrence_growth | (intros; apply GlobalTheory.norm_le_of_recurrence_growth <;> assumption)
end

