import Formalism.LogFactorialIndices.Bundle0001
import Lemmata.GeneralBFactSecondFurther.Imports
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0006
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0020

-- bundled from Formalism.LogFactorialIndices.SignedSubspaceIndex.IdxBase
section
noncomputable section

namespace Formalism.LatticeIndexTer

open Module
open scoped Pointwise

namespace LatticeIndexLength

section SlopeTestRemainingChoices

theorem length_quot_ne_top {O M : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup M] [Module O M] [Module.Finite O M]
    (d : O) (hd : d ≠ 0) (N : Submodule O M) (hN : ∀ m : M, d • m ∈ N) :
    Module.length O (M ⧸ N) ≠ ⊤ := by
  let I : Ideal O := Ideal.span {d}
  have hle : I • (⊤ : Submodule O M) ≤ N := by
    rw [Submodule.smul_le]
    intro r hr m _
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [mul_smul]
    exact N.smul_mem _ (hN m)
  refine ne_top_of_le_ne_top ?_
    (Module.length_le_of_surjective (Submodule.factor hle) (Submodule.factor_surjective hle))
  have h1 : IsFiniteLength O (O ⧸ I) :=
    isFiniteLength_quotient_span_singleton O (mem_nonZeroDivisors_of_ne_zero hd)
  rw [isFiniteLength_iff_isNoetherian_isArtinian] at h1
  obtain ⟨_, h1a⟩ := h1
  have : IsArtinianRing (O ⧸ I) := isArtinian_of_tower O h1a
  have : Module.Finite (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M)) :=
    Module.Finite.of_restrictScalars_finite O (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M))
  have : IsArtinian (O ⧸ I) (M ⧸ I • (⊤ : Submodule O M)) := inferInstance
  have : IsArtinian O (M ⧸ I • (⊤ : Submodule O M)) :=
    isArtinian_of_surjective_algebraMap (Ideal.Quotient.mk_surjective (I := I))
  exact Module.length_ne_top

theorem length_quotient_tower_add {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
    (D E P : Submodule O X) (hDE : D ≤ E) (hEP : E ≤ P) :
    Module.length O (P ⧸ D.comap P.subtype) =
      Module.length O (E ⧸ D.comap E.subtype) + Module.length O (P ⧸ E.comap P.subtype) := by
  let f : (E ⧸ D.comap E.subtype) →ₗ[O] (P ⧸ D.comap P.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hEP) (by intro x hx; simpa using hx)
  let g : (P ⧸ D.comap P.subtype) →ₗ[O] (P ⧸ E.comap P.subtype) :=
    Submodule.factor (Submodule.comap_mono hDE)
  apply Module.length_eq_add_of_exact f g
  · rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    induction x using Submodule.Quotient.induction_on with | H e => ?_
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap,
      Submodule.subtype_apply, Submodule.coe_inclusion] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    exact hx
  · exact Submodule.factor_surjective _
  · intro y
    induction y using Submodule.Quotient.induction_on with | H p => ?_
    rw [show g (Submodule.Quotient.mk p) = Submodule.Quotient.mk p from Submodule.factor_mk _ p,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.subtype_apply]
    constructor
    · intro hp
      exact ⟨Submodule.Quotient.mk ⟨p, hp⟩, rfl⟩
    · rintro ⟨x, hx⟩
      induction x using Submodule.Quotient.induction_on with | H e => ?_
      simp only [f, Submodule.mapQ_apply] at hx
      rw [Submodule.Quotient.eq, Submodule.mem_comap] at hx
      simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion] at hx
      have : (p : X) = (e : X) - ((e : X) - p) := by abel
      rw [this]
      exact E.sub_mem e.2 (hDE hx)

end SlopeTestRemainingChoices

section Sat

variable {O K X : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] [AddCommGroup X] [Module K X] [Module O X] [IsScalarTower O K X]

theorem exists_smul_mem_of_span (B : Submodule O X) (hB : Submodule.span K (B : Set X) = ⊤)
    (x : X) : ∃ d : O, d ≠ 0 ∧ d • x ∈ B := by
  first | exact Bl.general_b_fact_second''.goal1 .. | (apply Bl.general_b_fact_second''.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_second''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_second''.goal1 <;> assumption) | (apply @Bl.general_b_fact_second''.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B hB x | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B hB | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› B | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X ‹_› | exact @Bl.general_b_fact_second''.goal1 O K X | exact @Bl.general_b_fact_second''.goal1 O K | exact @Bl.general_b_fact_second''.goal1 O

theorem exists_smul_le (A B : Submodule O X) (hA : A.FG)
    (hB : Submodule.span K (B : Set X) = ⊤) : ∃ d : O, d ≠ 0 ∧ ∀ a ∈ A, d • a ∈ B := by
  classical
  obtain ⟨s, rfl⟩ := hA
  choose f hf0 hf using fun x => exists_smul_mem_of_span (K := K) B hB x
  refine ⟨∏ x ∈ s, f x, Finset.prod_ne_zero_iff.2 (fun x _ => hf0 x), ?_⟩
  intro a ha
  have h : Submodule.span O (s : Set X) ≤ B.comap ((∏ x ∈ s, f x) • LinearMap.id) := by
    rw [Submodule.span_le]
    intro x hx
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.1 hx)
    show ((∏ x ∈ s, f x) • LinearMap.id : X →ₗ[O] X) x ∈ B
    rw [LinearMap.smul_apply, LinearMap.id_apply, hc, mul_comm, mul_smul]
    exact B.smul_mem _ (hf x)
  exact h ha

theorem exists_smul_mem_inf_three (P Q₁ Q₂ Q₃ : Submodule O X) (hP : P.FG)
    (h₁ : Submodule.span K (Q₁ : Set X) = ⊤) (h₂ : Submodule.span K (Q₂ : Set X) = ⊤)
    (h₃ : Submodule.span K (Q₃ : Set X) = ⊤) :
    ∃ d : O, d ≠ 0 ∧ ∀ p ∈ P, d • p ∈ Q₁ ⊓ Q₂ ⊓ Q₃ := by
  obtain ⟨d₁, hd₁, e₁⟩ := exists_smul_le P Q₁ hP h₁
  obtain ⟨d₂, hd₂, e₂⟩ := exists_smul_le P Q₂ hP h₂
  obtain ⟨d₃, hd₃, e₃⟩ := exists_smul_le P Q₃ hP h₃
  refine ⟨d₁ * d₂ * d₃, mul_ne_zero (mul_ne_zero hd₁ hd₂) hd₃, fun p hp => ?_⟩
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [show d₁ * d₂ * d₃ = (d₂ * d₃) * d₁ by ring, mul_smul]; exact Q₁.smul_mem _ (e₁ p hp)
  · rw [show d₁ * d₂ * d₃ = (d₁ * d₃) * d₂ by ring, mul_smul]; exact Q₂.smul_mem _ (e₂ p hp)
  · rw [mul_smul]; exact Q₃.smul_mem _ (e₃ p hp)

end Sat

section Main

theorem len_ne_top {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup X] [Module O X] (P D : Submodule O X) (hP : P.FG) (d : O) (hd : d ≠ 0)
    (h : ∀ p ∈ P, d • p ∈ D) : Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤ := by
  have : Module.Finite O P := Module.Finite.iff_fg.2 hP
  refine length_quot_ne_top d hd _ (fun m => ?_)
  rw [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_smul]
  exact h m m.2

theorem idx_eq_sub {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]
    (P Q D : Submodule O X) (hD : D ≤ P ⊓ Q)
    (hP : Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤)
    (hQ : Module.length O (Q ⧸ D.comap Q.subtype) ≠ ⊤) :
    idx O X P Q = ((Module.length O (P ⧸ D.comap P.subtype)).toNat : ℤ) -
      ((Module.length O (Q ⧸ D.comap Q.subtype)).toNat : ℤ) := by
  have eP := length_quotient_tower_add D (P ⊓ Q) P hD inf_le_left
  have eQ := length_quotient_tower_add D (P ⊓ Q) Q hD inf_le_right
  have cP : Q.comap P.subtype = (P ⊓ Q).comap P.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
  have cQ : P.comap Q.subtype = (P ⊓ Q).comap Q.subtype := by
    rw [Submodule.comap_inf, Submodule.comap_subtype_self, inf_top_eq]
  unfold idx qlen
  rw [cP, cQ]
  rw [eP] at hP ⊢
  rw [eQ] at hQ ⊢
  obtain ⟨h1, h2⟩ := WithTop.add_ne_top.1 hP
  obtain ⟨_, h3⟩ := WithTop.add_ne_top.1 hQ
  rw [ENat.toNat_add h1 h2, ENat.toNat_add h1 h3]
  push_cast
  ring

end Main

end LatticeIndexLength

open LatticeIndexLength

theorem lattice_quotient_finite : LatFinite := by
  intro O K X _ _ _ _ _ _ _ _ _ _ A B hA hB
  obtain ⟨d, hd, h⟩ := exists_smul_le (K := K) A B hA.1 hB.2
  exact len_ne_top A B hA.1 d hd h

theorem lattice_index_add : IdxAdd := by
  intro O K X _ _ _ _ _ _ _ _ _ _ A B C hA hB hC
  let D := A ⊓ B ⊓ C
  have fin : ∀ P : Submodule O X, IsLat O K X P → Module.length O (P ⧸ D.comap P.subtype) ≠ ⊤ := by
    intro P hP
    obtain ⟨d, hd, h⟩ := exists_smul_mem_inf_three (K := K) P A B C hP.1 hA.2 hB.2 hC.2
    exact len_ne_top P D hP.1 d hd h
  have hAB : D ≤ A ⊓ B := inf_le_left
  have hBC : D ≤ B ⊓ C := le_inf (inf_le_left.trans inf_le_right) inf_le_right
  have hAC : D ≤ A ⊓ C := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  rw [idx_eq_sub A C D hAC (fin A hA) (fin C hC), idx_eq_sub A B D hAB (fin A hA) (fin B hB),
    idx_eq_sub B C D hBC (fin B hB) (fin C hC)]
  ring

theorem lattice_has_basis : LatBasis := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ A hA
  have : Submodule.IsLattice K A := ⟨hA.1, hA.2⟩
  let b := Module.Free.chooseBasis O A
  let b' := b.extendOfIsLattice K
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex O A) = finrank K X :=
    (Module.finrank_eq_card_basis b').symm
  refine ⟨b'.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  rw [Module.Basis.range_reindex]
  have hr : Set.range b' = A.subtype '' Set.range b := by
    rw [← Set.range_comp]
    ext x
    simp [b']
  rw [hr, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]

end Formalism.LatticeIndexTer
end
end

-- bundled from Formalism.LogFactorialIndices.SignedSubspaceIndex.LogProductFormula
section
noncomputable section

namespace Formalism.LatticeIndexTer

open scoped ComplexConjugate
open IsDedekindDomain NumberField

theorem log_product_formula : LogProductFormula := by
  intro L _ _ x hx
  obtain ⟨I, hIdef⟩ : ∃ I : FractionalIdeal (nonZeroDivisors (𝓞 L)) L,
      I = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 L)) x := ⟨_, rfl⟩
  rw [← hIdef]
  have hI : I ≠ 0 := by
    rw [hIdef, Ne, FractionalIdeal.spanSingleton_eq_zero_iff]
    exact hx
  have hfin : (Function.support fun v : HeightOneSpectrum (𝓞 L) => FractionalIdeal.count L v I).Finite :=
    by
      have hev := FractionalIdeal.finite_factors I
      exact Filter.eventually_cofinite.mp hev
  have hR : (∑ᶠ v : HeightOneSpectrum (𝓞 L), (FractionalIdeal.count L v I : ℝ) *
        Real.log (Ideal.absNorm v.asIdeal : ℝ)) =
      ∑ v ∈ hfin.toFinset, (FractionalIdeal.count L v I : ℝ) * Real.log (Ideal.absNorm v.asIdeal : ℝ) := by
    apply finsum_eq_sum_of_support_subset
    intro v hv
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    rw [Function.mem_support] at hv
    intro h0
    exact hv (by simp [h0])
  have hsub2 : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 L) =>
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ^ FractionalIdeal.count L v I) ⊆
      (hfin.toFinset : Set _) := by
    intro v hv
    rw [Set.Finite.coe_toFinset, Function.mem_support]
    rw [Function.mem_mulSupport] at hv
    intro h0
    exact hv (by simp [h0])
  have hfac : ∏ v ∈ hfin.toFinset, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ^
      FractionalIdeal.count L v I = I := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ hsub2]
    exact FractionalIdeal.finprod_heightOneSpectrum_factorization' L hI
  have hN1 : FractionalIdeal.absNorm I =
      ∏ v ∈ hfin.toFinset, (Ideal.absNorm v.asIdeal : ℚ) ^ FractionalIdeal.count L v I := by
    conv_lhs => rw [← hfac]
    rw [map_prod]
    refine Finset.prod_congr rfl (fun v _ => ?_)
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm]
  have hN2 : FractionalIdeal.absNorm I = |Algebra.norm ℚ x| := by
    rw [hIdef]
    exact FractionalIdeal.absNorm_span_singleton (𝓞 L) x
  have hprod : ∏ σ : L →+* ℂ, σ x = algebraMap ℚ ℂ (Algebra.norm ℚ x) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ x]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _ (fun σ => rfl)
  have hne1 : ∀ σ ∈ (Finset.univ : Finset (L →+* ℂ)), ‖σ x‖ ≠ 0 := fun σ _ => by
    rw [norm_ne_zero_iff]
    exact (map_ne_zero σ).mpr hx
  have hL : ∑ σ : L →+* ℂ, Real.log ‖σ x‖ = Real.log |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    rw [← Real.log_prod hne1, ← norm_prod, hprod]
    congr 1
    rw [eq_ratCast (algebraMap ℚ ℂ)]
    simp
  have hne2 : ∀ v ∈ hfin.toFinset, ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ FractionalIdeal.count L v I ≠ 0 := by
    intro v _
    apply zpow_ne_zero
    rw [Nat.cast_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  rw [hL, hR, ← Rat.cast_abs, ← hN2, hN1]
  push_cast
  rw [Real.log_prod hne2]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  rw [Real.log_zpow]

end Formalism.LatticeIndexTer
end
end

-- bundled from Formalism.LogFactorialIndices.SignedSubspaceIndex.SubspaceLatticeIndex
section
open scoped Pointwise

noncomputable section

namespace Formalism.LatticeIndexTer.subgroupData

variable {O X : Type} [CommRing O] [AddCommGroup X] [Module O X]

theorem length_chain' {A B C : Submodule O X} (hAB : A ≤ B) (hBC : B ≤ C) :
    Module.length O (C ⧸ A.comap C.subtype) =
      Module.length O (B ⧸ A.comap B.subtype) + Module.length O (C ⧸ B.comap C.subtype) :=
  _root_.UpperTheory.Reformulated.B.JointEigenvalueBoundsFromAnyDatum.length_chain hAB hBC

theorem length_le_of_le {S T A B : Submodule O X} (hST : S ≤ T) (hBA : B ≤ A)
    (hSA : S ⊓ A ≤ B) :
    Module.length O (S ⧸ B.comap S.subtype) ≤ Module.length O (T ⧸ A.comap T.subtype) := by
  let f : (S ⧸ B.comap S.subtype) →ₗ[O] (T ⧸ A.comap T.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hST) (fun x hx => by
      simp only [Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_inclusion] at hx ⊢
      exact hBA hx)
  apply Module.length_le_of_injective f
  intro x y hxy
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  simp only [f, Submodule.mapQ_apply] at hxy
  rw [Submodule.Quotient.eq] at hxy ⊢
  simp only [Submodule.mem_comap, Submodule.coe_subtype, map_sub, Submodule.coe_inclusion]
    at hxy ⊢
  exact hSA (Submodule.mem_inf.mpr ⟨S.sub_mem x.2 y.2, hxy⟩)

theorem length_le_of_ge {S A B : Submodule O X} (hBA : B ≤ A) :
    Module.length O (S ⧸ A.comap S.subtype) ≤ Module.length O (S ⧸ B.comap S.subtype) := by
  let g : (S ⧸ B.comap S.subtype) →ₗ[O] (S ⧸ A.comap S.subtype) :=
    Submodule.mapQ _ _ LinearMap.id (fun x hx => by simpa using hBA hx)
  apply Module.length_le_of_surjective g
  intro z
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  exact ⟨Submodule.Quotient.mk z, rfl⟩

theorem qlen_eq_zero {A B : Submodule O X} (h : A ≤ B) : qlen O X A B = 0 := by
  unfold qlen
  rw [Module.length_eq_zero_iff]
  refine ⟨fun a b => ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [Submodule.Quotient.eq]
  exact h (a - b).2

theorem qlen_ne_top_of_pow {O X : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [AddCommGroup X] [Module O X] [Module.IsTorsionFree O X] (ϖ : O) (hϖ : Irreducible ϖ) (k : ℕ)
    (A B : Submodule O X) (hA : A.FG) (hk : ∀ a ∈ A, ϖ ^ k • a ∈ B) : qlen O X A B ≠ ⊤ := by
  show Module.length O (A ⧸ B.comap A.subtype) ≠ ⊤
  have : Module.Finite O A := Module.Finite.iff_fg.mpr hA
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := A)
  let ψ : (Fin n → O) →ₗ[O] A ⧸ B.comap A.subtype :=
    (B.comap A.subtype).mkQ ∘ₗ b.equivFun.symm.toLinearMap
  have hψ : Function.Surjective ψ :=
    (Submodule.mkQ_surjective _).comp b.equivFun.symm.surjective
  let P : Submodule O (Fin n → O) := Submodule.pi Set.univ (fun _ => Ideal.span {ϖ ^ k})
  have hP : P ≤ LinearMap.ker ψ := by
    intro x hx
    choose y hy using fun i =>
      Ideal.mem_span_singleton.mp (Submodule.mem_pi.mp hx i (Set.mem_univ i))
    have hxy : x = ϖ ^ k • y := funext fun i => by simp [hy i]
    rw [LinearMap.mem_ker, hxy, map_smul]
    set m : A := b.equivFun.symm y
    rw [show ψ y = Submodule.Quotient.mk m from rfl, ← Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    simp only [Submodule.coe_subtype, SetLike.val_smul]
    exact hk _ m.2
  have hsurj : Function.Surjective (P.liftQ ψ hP) := by
    intro z
    obtain ⟨w, hw⟩ := hψ z
    exact ⟨Submodule.Quotient.mk w, hw⟩
  refine ne_top_of_le_ne_top ?_ (Module.length_le_of_surjective _ hsurj)
  rw [(Submodule.quotientPi (fun _ : Fin n => Ideal.span {ϖ ^ k})).length_eq, Module.length_pi]
  have : Ideal.span {ϖ ^ k} = IsLocalRing.maximalIdeal O ^ k := by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
  simp only [ENat.card_eq_coe_fintype_card, Fintype.card_fin, ne_eq]
  rw [← Nat.cast_mul]
  exact ENat.natCast_ne_top _

end Formalism.LatticeIndexTer.subgroupData

namespace Formalism.LatticeIndexTer

open Formalism.LatticeIndexTer.subgroupData

theorem subspace_lattice_index : SubspaceIndex := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ ϖ hϖ F M Θ hM hΘ W MW ΘW
  have hΘM : Θ ≤ M := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hΘ hx)
    exact M.smul_mem _ hy
  have hMW : MW ≤ M := inf_le_left
  have h1 : Θ ≤ Θ ⊔ MW := le_sup_left
  have h2 : Θ ⊔ MW ≤ M := sup_le hΘM hMW
  rw [length_chain' h1 h2]
  have hA : Module.length O (MW ⧸ ΘW.comap MW.subtype) ≤
      Module.length O (↥(Θ ⊔ MW) ⧸ Θ.comap (Θ ⊔ MW).subtype) :=
    length_le_of_le le_sup_right inf_le_left (fun x hx =>
      Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).2,
        (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).2⟩)
  refine add_le_add hA ?_

  have : Module.IsTorsionFree O (X ⧸ W) := .trans_faithfulSMul O K (X ⧸ W)
  let q : X →ₗ[O] X ⧸ W := W.mkQ.restrictScalars O
  let N : Submodule O (X ⧸ W) := M.map q
  have : Module.Finite O N := Module.Finite.iff_fg.mpr (hM.1.map q)
  obtain ⟨n, b⟩ := Module.basisOfFiniteTypeTorsionFree' (R := O) (M := N)
  have hNle : ∀ y : N, (y : X ⧸ W) ∈ Submodule.span K (Set.range fun i => ((b i : N) : X ⧸ W)) := by
    intro y
    rw [← b.sum_repr y]
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hspan : Submodule.span K (Set.range fun i => ((b i : N) : X ⧸ W)) = ⊤ := by
    rw [eq_top_iff]
    rintro z -
    obtain ⟨x, rfl⟩ := W.mkQ_surjective z
    have hx : x ∈ Submodule.span K (M : Set X) := hM.2 ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact hNle ⟨q y, Submodule.mem_map_of_mem hy⟩
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul a y _ hy => rw [map_smul]; exact Submodule.smul_mem _ a hy
  have hd : Module.finrank K X - Module.finrank K W ≤ n := by
    have e1 := Submodule.finrank_quotient_add_finrank W
    have e2 := finrank_range_le_card (R := K) (fun i => ((b i : N) : X ⧸ W))
    rw [Set.finrank, hspan, finrank_top, Fintype.card_fin] at e2
    omega

  let I : Ideal O := Ideal.span {ϖ ^ F}
  let φ : M →ₗ[O] N := q.submoduleMap M
  let π : (Fin n → O) →ₗ[O] (Fin n → O ⧸ I) := LinearMap.pi fun i => I.mkQ ∘ₗ LinearMap.proj i
  let ψ : M →ₗ[O] (Fin n → O ⧸ I) := π ∘ₗ b.equivFun.toLinearMap ∘ₗ φ
  have hψ : Function.Surjective ψ := by
    intro y
    choose c hc using fun i => Submodule.Quotient.mk_surjective I (y i)
    obtain ⟨m, hm⟩ := LinearMap.submoduleMap_surjective q M (b.equivFun.symm c)
    refine ⟨m, ?_⟩
    have hm' : φ m = b.equivFun.symm c := hm
    funext i
    simp only [ψ, LinearMap.comp_apply, hm', LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    simp only [π, LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply, Submodule.mkQ_apply]
    exact hc i
  have hker : (Θ ⊔ MW).comap M.subtype ≤ LinearMap.ker ψ := by
    intro m hm
    rw [Submodule.mem_comap] at hm
    obtain ⟨θ, hθ, w, hw, hsum⟩ := Submodule.mem_sup.mp hm
    have hm' : m = ⟨θ, hΘM hθ⟩ + ⟨w, hMW hw⟩ := Subtype.ext (by simp [hsum])
    rw [LinearMap.mem_ker, hm', map_add]
    have hw0 : φ ⟨w, hMW hw⟩ = 0 := by
      apply Subtype.ext
      simp only [φ, ZeroMemClass.coe_zero]
      exact (Submodule.Quotient.mk_eq_zero W).mpr (Submodule.mem_inf.mp hw).2
    have hw0' : ψ ⟨w, hMW hw⟩ = 0 := by
      simp only [ψ, LinearMap.comp_apply, hw0, map_zero]
    have hθ0 : ψ ⟨θ, hΘM hθ⟩ = 0 := by
      obtain ⟨y, hy, hyθ⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp (hΘ hθ)
      have hsm : (⟨θ, hΘM hθ⟩ : M) = ϖ ^ F • ⟨y, hy⟩ := Subtype.ext hyθ.symm
      rw [hsm, map_smul]
      funext i
      simp only [Pi.smul_apply, Pi.zero_apply]
      obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective I (ψ ⟨y, hy⟩ i)
      rw [← hc, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    rw [hθ0, hw0', add_zero]
  have hsurj : Function.Surjective (((Θ ⊔ MW).comap M.subtype).liftQ ψ hker) := by
    intro z
    obtain ⟨m, hm⟩ := hψ z
    exact ⟨Submodule.Quotient.mk m, hm⟩
  have hlen : Module.length O (Fin n → O ⧸ I) = ((n * F : ℕ) : ℕ∞) := by
    rw [Module.length_pi]
    have : I = IsLocalRing.maximalIdeal O ^ F := by
      rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
    rw [this, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal]
    simp
  refine le_trans ?_ (Module.length_le_of_surjective _ hsurj)
  rw [hlen]
  exact_mod_cast (by rw [Nat.mul_comm n]; exact Nat.mul_le_mul_left F hd)

theorem goodIndex_of_latFinite (h1 : LatFinite) : GoodIndex := by
  intro O K X _ _ _ _ _ _ _ _ _ _ _ e he A Θ hA hΘ hΘA V₀
  have hfin : qlen O X A Θ ≠ ⊤ := h1 O K X A Θ hA hΘ
  have hQ'P : Θ ⊓ V₀ ≤ A ⊓ V₀ := inf_le_inf_right _ hΘA
  have hPQ' : qlen O X (A ⊓ V₀) (Θ ⊓ V₀) ≤ qlen O X A Θ :=
    length_le_of_le inf_le_left inf_le_left (fun x hx =>
      Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hx).2,
        (Submodule.mem_inf.mp (Submodule.mem_inf.mp hx).1).2⟩)
  have hfin' : qlen O X (A ⊓ V₀) (Θ ⊓ V₀) ≠ ⊤ := ne_top_of_le_ne_top hfin hPQ'
  have hidx1 : idx O X A Θ = ((qlen O X A Θ).toNat : ℤ) := by
    simp [idx, qlen_eq_zero hΘA]
  have hidx2 : idx O X (A ⊓ V₀) (Θ ⊓ V₀) = ((qlen O X (A ⊓ V₀) (Θ ⊓ V₀)).toNat : ℤ) := by
    simp [idx, qlen_eq_zero hQ'P]
  refine ⟨?_, ?_⟩
  · rw [hidx1, hidx2]
    exact_mod_cast ENat.toNat_le_toNat hPQ' hfin
  · rw [hidx2]
    have hQ'Q : Θ ⊓ V₀ ≤ Θ.map (e.restrictScalars O) := by
      intro x hx
      have hxΘ : x ∈ Θ := (Submodule.mem_inf.mp hx).1
      have hxV : x ∈ LinearMap.range e := (Submodule.mem_inf.mp hx).2
      obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hxV
      refine Submodule.mem_map.mpr ⟨e y, hxΘ, ?_⟩
      have := LinearMap.congr_fun he y
      simpa using this
    have hle : qlen O X (A ⊓ V₀) (Θ.map (e.restrictScalars O)) ≤ qlen O X (A ⊓ V₀) (Θ ⊓ V₀) :=
      length_le_of_ge hQ'Q
    have := ENat.toNat_le_toNat hle hfin'
    unfold idx
    omega

theorem goodIndex_of (h1 : LatFinite) (_h2 : IdxAdd) : GoodIndex := goodIndex_of_latFinite h1

end Formalism.LatticeIndexTer
end
end

