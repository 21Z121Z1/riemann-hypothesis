import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FirstIndexEqOfUnfolded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2117
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.GradedWeylDivisibility.FinalB
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2112
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionDegreeDvdCardInvariants
section
open Polynomial

namespace GlobalTheory.InvariantSpecialisation

theorem exists_extension {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B))
    [Field Ω] [IsAlgClosed Ω] (e : A →+* Ω) :
    ∃ φ : B →+* Ω, φ.comp (algebraMap A B) = e := by
  haveI hP : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  obtain ⟨Q, -, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B) (RingHom.ker e) ⊥
    (by
      intro a ha
      have : a = 0 := hinj (by simpa using ha)
      simp [this])
  haveI : Q.LiesOver (RingHom.ker e) := ⟨hQP.symm⟩
  letI : Algebra (A ⧸ RingHom.ker e) Ω := (RingHom.kerLift e).toAlgebra
  haveI : FaithfulSMul (A ⧸ RingHom.ker e) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective e)
  haveI : Algebra.IsIntegral (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance
  haveI : IsDomain (A ⧸ RingHom.ker e) := Ideal.Quotient.isDomain _
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain _
  haveI : FaithfulSMul (A ⧸ RingHom.ker e) (B ⧸ Q) := inferInstance
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) (B ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (FaithfulSMul.algebraMap_injective _ _)
  haveI : Module.IsTorsionFree (A ⧸ RingHom.ker e) Ω :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective e)
  haveI : Algebra.IsAlgebraic (A ⧸ RingHom.ker e) (B ⧸ Q) := Algebra.IsIntegral.isAlgebraic
  let l : (B ⧸ Q) →ₐ[A ⧸ RingHom.ker e] Ω := IsAlgClosed.lift
  refine ⟨(l : (B ⧸ Q) →+* Ω).comp (Ideal.Quotient.mk Q), ?_⟩
  ext a
  have h := l.commutes (Ideal.Quotient.mk _ a)
  exact h

theorem exists_smul_of_comp_eq {A B Ω : Type} [CommRing A] [CommRing B] [Algebra A B]
    (G : Type) [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [Field Ω] [CharZero Ω] (φ ψ : B →+* Ω)
    (h : ψ.comp (algebraMap A B) = φ.comp (algebraMap A B)) :
    ∃ g : G, ∀ b, ψ b = φ (g • b) := by
  classical
  letI := Fintype.ofFinite G
  have h1 : ∀ b, ∃ g : G, ψ b = φ (g • b) := by
    intro b
    obtain ⟨p, hp⟩ := Algebra.IsInvariant.charpoly_mem_lifts A B G b
    have hp' : p.map (algebraMap A B) = MulSemiringAction.charpoly G b := hp
    have e1 : (MulSemiringAction.charpoly G b).map ψ = (MulSemiringAction.charpoly G b).map φ := by
      rw [← hp', Polynomial.map_map, Polynomial.map_map, h]
    have e2 : ((MulSemiringAction.charpoly G b).map ψ).eval (ψ b) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_hom, MulSemiringAction.eval_charpoly, map_zero]
    rw [e1, MulSemiringAction.charpoly_eq, Polynomial.map_prod, Polynomial.eval_prod,
      Finset.prod_eq_zero_iff] at e2
    obtain ⟨g, -, hg⟩ := e2
    refine ⟨g, ?_⟩
    simpa [sub_eq_zero] using hg
  let H : G → AddSubgroup B := fun g =>
    { carrier := {b | ψ b = φ (g • b)}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, smul_add, map_add, ha, hb]
      neg_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [map_neg, smul_neg, map_neg, ha] }
  obtain ⟨g, -, hg⟩ := AddSubgroup.exists_finiteIndex_of_leftCoset_cover
    (H := H) (g := fun _ => 0) (s := Finset.univ) (by
      rw [Set.eq_univ_iff_forall]
      intro b
      obtain ⟨g, hg⟩ := h1 b
      simp only [Set.mem_iUnion]
      exact ⟨g, Finset.mem_univ _, b, hg, zero_add b⟩)
  refine ⟨g, fun b => ?_⟩
  have h2 : ψ ((H g).index • b) = φ (g • ((H g).index • b)) := (H g).nsmul_index_mem b
  rw [smul_comm g, map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul] at h2
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hg.index_ne_zero) h2

theorem exists_finite_extension_finrank_dvd :
    ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (G : Type) [Group G] [Finite G]
      [MulSemiringAction G B] [SMulCommClass G A B] [Algebra.IsInvariant A B G],
      Function.Injective (algebraMap A B) → ∀ (k : Type) [Field k] [CharZero k] (ev : A →+* k),
      ∃ (K' : Type) (_ : Field K') (_ : Algebra k K') (β : B →+* K'), FiniteDimensional k K' ∧
        Module.finrank k K' ∣ Nat.card G ∧
        β.comp (algebraMap A B) = (algebraMap k K').comp ev := by
  intro A B _ _ _ G _ _ _ _ _ hinj k _ _ ev
  haveI := Algebra.IsInvariant.isIntegral A B G
  let Ω := AlgebraicClosure k
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap k Ω).injective
  obtain ⟨φ, hφ⟩ := exists_extension hinj ((algebraMap k Ω).comp ev)
  let K : IntermediateField k Ω := IntermediateField.adjoin k (Set.range φ)
  let P : Subgroup ((Ω ≃ₐ[k] Ω) × G) :=
    { carrier := {x | ∀ b, x.1 (φ b) = φ (x.2 • b)}
      one_mem' := by intro b; simp
      mul_mem' := by
        intro x y hx hy b
        simp only [Prod.fst_mul, Prod.snd_mul, AlgEquiv.mul_apply]
        rw [hy, hx, mul_smul]
      inv_mem' := by
        intro x hx b
        apply x.1.injective
        rw [hx]
        simp }
  let p₁ : P →* (Ω ≃ₐ[k] Ω) := (MonoidHom.fst _ _).comp P.subtype
  let p₂ : P →* G := (MonoidHom.snd _ _).comp P.subtype
  have hsurj : Function.Surjective p₁ := by
    intro σ
    obtain ⟨g, hg⟩ := exists_smul_of_comp_eq (A := A) G φ ((σ : Ω →+* Ω).comp φ) (by
      rw [RingHom.comp_assoc, hφ]
      ext a
      simp)
    exact ⟨⟨(σ, g), hg⟩, rfl⟩
  have hle : p₂.ker ≤ K.fixingSubgroup.comap p₁ := by
    rintro ⟨⟨σ, g⟩, hx⟩ hg
    have hg1 : g = 1 := hg
    subst hg1
    change σ ∈ K.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hxK
    induction hxK using IntermediateField.adjoin_induction with
    | mem x hx' =>
      obtain ⟨b, rfl⟩ := hx'
      simpa using hx b
    | algebraMap c => exact σ.commutes c
    | add x y _ _ h1 h2 => rw [map_add, h1, h2]
    | inv x _ h1 => rw [map_inv₀, h1]
    | mul x y _ _ h1 h2 => rw [map_mul, h1, h2]
  have hdvd : Module.finrank k K ∣ Nat.card G := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index,
      ← Subgroup.index_comap_of_surjective _ hsurj]
    refine (Subgroup.index_dvd_of_le hle).trans ?_
    rw [Subgroup.index_ker]
    exact Subgroup.card_subgroup_dvd_card _
  refine ⟨K, inferInstance, inferInstance,
    φ.codRestrict K (fun b => IntermediateField.subset_adjoin _ _ ⟨b, rfl⟩), ?_, hdvd, ?_⟩
  · exact Module.finite_of_finrank_pos (Nat.pos_of_dvd_of_pos hdvd Nat.card_pos)
  · ext a
    exact RingHom.congr_fun hφ a

end GlobalTheory.InvariantSpecialisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagDomainDataOfFiniteIndexSubgroup
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EqCovol

theorem exists_data_of_le_relIndex_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : Data E r) (Δ : Subgroup (GL (Fin r) E)), Δ ≤ X.Γ → Δ.relIndex X.Γ ≠ 0 →
    ∃ P : Data E r, P.Ψ = X.Ψ ∧ P.Gm = X.Gm ∧ P.p0 = X.p0 ∧ P.Γ = Δ := by
  intro E _ _ _ r X Δ hle hidx
  classical
  have hT : ∃ T : Finset (GL (Fin r) E), ∀ g ∈ X.Γ, ∃ t ∈ T, t⁻¹ * g ∈ Δ := by
    letI := Subgroup.fintypeOfIndexNeZero hidx
    refine ⟨Finset.univ.image
      (fun q : X.Γ ⧸ Δ.subgroupOf X.Γ => ((Quotient.out q : X.Γ) : GL (Fin r) E)), ?_⟩
    intro g hg
    set q : X.Γ ⧸ Δ.subgroupOf X.Γ := QuotientGroup.mk (⟨g, hg⟩ : X.Γ) with hq
    refine ⟨((Quotient.out q : X.Γ) : GL (Fin r) E),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have h : ((Quotient.out q : X.Γ) : X.Γ ⧸ Δ.subgroupOf X.Γ) = QuotientGroup.mk (⟨g, hg⟩ : X.Γ) :=
      QuotientGroup.out_eq' q
    have h2 := QuotientGroup.eq.mp h
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  obtain ⟨T, hT⟩ := hT
  obtain ⟨S, hS⟩ := X.Γ_index
  refine ⟨{ X with
    Γ := Δ
    Γ_stab := fun γ hγ => X.Γ_stab γ (hle hγ)
    Γ_index := ⟨(S ×ˢ T).image (fun p => p.1 * p.2), by
      intro γ hγ
      obtain ⟨s, hs, h1⟩ := hS γ hγ
      obtain ⟨t, ht, h2⟩ := hT _ h1
      refine ⟨s * t, Finset.mem_image.mpr ⟨(s, t), Finset.mem_product.mpr ⟨hs, ht⟩, rfl⟩, ?_⟩
      rw [mul_inv_rev, mul_assoc]
      exact h2⟩
    Γ_free := fun γ hγ => X.Γ_free γ (hle hγ)
    χ_mul := fun la γ hγ γ' hγ' => X.χ_mul la γ (hle hγ) γ' (hle hγ')
    χ_add := fun la la' γ hγ => X.χ_add la la' γ (hle hγ)
    χ_fin := fun la => by
      obtain ⟨n, hn, h⟩ := X.χ_fin la
      exact ⟨n, hn, fun γ hγ => h γ (hle hγ)⟩
    m := X.m * (Δ.relIndex X.Γ).factorial
    m_pos := Nat.mul_pos X.m_pos (Nat.factorial_pos _)
    transv := by
      intro ξ hξ hiso s hs hint
      obtain ⟨γ, hγ, hmat⟩ := X.transv ξ hξ hiso s hs hint
      refine ⟨γ ^ (Δ.relIndex X.Γ).factorial,
        (Subgroup.mem_inf.mp (Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd hidx hγ
          (fun k hk hk' => Nat.dvd_factorial hk hk'))).1, ?_⟩
      rw [Units.val_pow_eq_pow_val, hmat, TransvectionPeriodicity.transvMat_pow X.Gm hiso]
      congr 1
      push_cast
      ring }, rfl, rfl, rfl, rfl⟩

end GlobalTheory.EqCovol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralWeylBasisSpanningAllRings
section
set_option autoImplicit false

open Formalism.GradedWeylDivisibility MvPolynomial

namespace GlobalTheory.WeylBasis

theorem map_mem_span {σ ι : Type} (R : Type) [CommRing R] (g : ι → MvPolynomial σ ℤ) {f : MvPolynomial σ ℤ}
    (hf : f ∈ Submodule.span ℤ (Set.range g)) :
    MvPolynomial.map (Int.castRingHom R) f ∈
      Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (g i)) := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i, rfl⟩ := hy
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy => rw [map_zsmul]; exact zsmul_mem hy a

theorem weyl_finite (n : ℕ) (ν : Fin n → ℕ) (hν : Antitone ν) : Module.Finite ℤ (weyl ℤ n n le_rfl ν) := by
  obtain ⟨c, hc, -⟩ := sSBasis ℤ n n ν
  have : Finite (ssIdx n n ν) := (sSIdxFinite n n ν).to_subtype
  have : Module.Finite ℤ (dualWeyl ℤ n n ν) := by
    rw [← hc.2.1]
    exact Module.Finite.span_of_finite ℤ (Set.finite_range c)
  exact Module.Finite.of_injective (Submodule.inclusion (weylLeDual ℤ n n le_rfl ν hν))
    (Submodule.inclusion_injective _)

theorem exists_weyl_basis : ∀ (n : ℕ) (ν : Fin n → ℕ), Antitone ν → ∃ (P : Type) (_ : Fintype P) (b : P → MvPolynomial (Fin n × Fin n) ℤ), LinearIndependent ℤ b ∧ (∀ (R : Type) [CommRing R], weyl R n n le_rfl ν = Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (b i))) ∧ ∀ (K : Type) [Field K] [CharZero K], dualWeyl K n n ν = Submodule.span K (Set.range fun i => MvPolynomial.map (Int.castRingHom K) (b i)) := by
  intro n ν hν
  have := weyl_finite n ν hν
  have : Module.Free ℤ (weyl ℤ n n le_rfl ν) := inferInstance
  let B := Module.Free.chooseBasis ℤ (weyl ℤ n n le_rfl ν)
  have hspan : Submodule.span ℤ (Set.range fun i => (B i : MvPolynomial (Fin n × Fin n) ℤ)) = weyl ℤ n n le_rfl ν := by
    have h := congrArg (Submodule.map (weyl ℤ n n le_rfl ν).subtype) B.span_eq
    rw [Submodule.map_span, ← Set.range_comp, Submodule.map_subtype_top] at h
    exact h
  have hR : ∀ (R : Type) [CommRing R], weyl R n n le_rfl ν =
      Submodule.span R (Set.range fun i => MvPolynomial.map (Int.castRingHom R) (B i : MvPolynomial (Fin n × Fin n) ℤ)) := by
    intro R _
    apply le_antisymm
    · unfold weyl
      rw [Submodule.span_le]
      rintro _ ⟨w, rfl⟩
      have hw' : applyWord ℤ w (hw ℤ le_rfl ν) ∈ weyl ℤ n n le_rfl ν := Submodule.subset_span ⟨w, rfl⟩
      rw [← hspan] at hw'
      have h := map_mem_span R _ hw'
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map] at h
      exact h
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      have h := map_mem_span R (fun w : List (Fin n × Fin n × ℕ) => applyWord ℤ w (hw ℤ le_rfl ν)) (B i).2
      simp only [← lclosedeq_applyWord_map, lclosedeq_hw_map] at h
      exact h
  refine ⟨_, inferInstance, fun i => (B i : MvPolynomial (Fin n × Fin n) ℤ), ?_, hR, ?_⟩
  · exact B.linearIndependent.map' (weyl ℤ n n le_rfl ν).subtype (Submodule.ker_subtype _)
  · intro K _ _
    apply le_antisymm
    · obtain ⟨c, hc, -⟩ := sSBasis ℤ n n ν
      rw [← span_map_weightBasis_eq_dualWeyl (K := K) hc, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      have hj : c j ∈ dualWeyl ℤ n n ν := hc.2.1 ▸ Submodule.subset_span ⟨j, rfl⟩
      obtain ⟨m, hm, hmj⟩ := weylRational n n le_rfl ν hν _ hj
      rw [← hspan] at hmj
      have h := map_mem_span K _ hmj
      rw [map_zsmul, ← Int.cast_smul_eq_zsmul K] at h
      exact (Submodule.smul_mem_iff _ (Int.cast_ne_zero.2 hm)).1 h
    · rw [← hR K]
      exact weylLeDual K n n le_rfl ν hν

end GlobalTheory.WeylBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicIndefiniteSelfDualTraceForm
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped nonZeroDivisors Matrix

noncomputable section

namespace GlobalTheory.EqCovol.IsoPlane

open GlobalTheory

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem selfD_of_isSelfDualTr {r : ℕ} (Y : Data E r) (h : IsSelfDualTr Y) : GlobalTheory.SW.SelfD Y Y.Λ := by
  refine ⟨Y.Λ_fg, fun x => (h x).trans (forall₂_congr fun y _ => ?_)⟩
  rw [GlobalTheory.ThFr.EF_def]
  rcases Y.κ0_xi with hk | hk
  · rw [hk, show (2 * Y.ξ0) / 2 = Y.ξ0 by ring]
  · have e : -(-(2 * Y.ξ0) / 2) * herm Y.Gm x y = -(-Y.ξ0 * herm Y.Gm x y) := by ring
    rw [hk, e, map_neg]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [hn, Int.cast_neg]⟩
    · rintro ⟨n, hn⟩
      exact ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩

def hypG : Matrix (Fin 2) (Fin 2) E := !![0, 1; 1, 0]

theorem hypG_herm (a b : Fin 2) : cc (hypG (E := E) a b) = hypG b a := by
  fin_cases a <;> fin_cases b <;> simp [hypG, cc]

theorem hypG_det : (hypG (E := E)).det ≠ 0 := by
  simp [hypG, Matrix.det_fin_two_of]

theorem herm_hypG (x y : Fin 2 → E) : herm hypG x y = x 0 * cc (y 1) + x 1 * cc (y 0) := by
  simp [herm, hypG, Fin.sum_univ_two]

def hypLat (J : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin 2 → E) :=
  ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E).comap (LinearMap.proj 0) ⊓
    (J : Submodule (𝓞 E) E).comap (LinearMap.proj 1)

theorem mem_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} {x : Fin 2 → E} :
    x ∈ hypLat J ↔ x 0 ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ∧ x 1 ∈ J := Iff.rfl

theorem isLattice_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} (hJ0 : J ≠ 0) :
    ReciprocityTheory.MultiplicativeHeights.IsLattice (hypLat J) := by
  classical
  constructor
  · refine Submodule.FG.of_le ((Submodule.fg_span_singleton (Pi.single 0 1 : Fin 2 → E)).sup
      ((FractionalIdeal.fg_of_isNoetherianRing le_rfl J).map
        (LinearMap.single (𝓞 E) (fun _ : Fin 2 => E) 1))) fun x hx => ?_
    obtain ⟨h0, h1⟩ := mem_hypLat.1 hx
    let z : 𝓞 E := ⟨x 0, mem_one_fractionalIdeal_iff.1 h0⟩
    refine Submodule.mem_sup.2 ⟨z • Pi.single 0 1, Submodule.smul_mem _ z (Submodule.mem_span_singleton_self _),
      Pi.single 1 (x 1), ⟨x 1, h1, rfl⟩, ?_⟩
    funext i
    fin_cases i
    · simp [Algebra.smul_def]; rfl
    · simp
  · obtain ⟨j, hj, hj0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (mt FractionalIdeal.coeToSubmodule_eq_bot.1 hJ0)
    have e0 : (Pi.single 0 1 : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) :=
      Submodule.subset_span (mem_hypLat.2 ⟨by simp, by rw [Pi.single_eq_of_ne (by decide)]; exact (J : Submodule (𝓞 E) E).zero_mem⟩)
    have e1' : (Pi.single 1 j : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) :=
      Submodule.subset_span (mem_hypLat.2 ⟨by simp, by simpa using hj⟩)
    have e1 : (Pi.single 1 1 : Fin 2 → E) ∈ Submodule.span E (hypLat J : Set (Fin 2 → E)) := by
      have := Submodule.smul_mem _ j⁻¹ e1'
      rwa [← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hj0] at this
    refine Submodule.eq_top_iff'.2 fun v => ?_
    have hv : v = v 0 • (Pi.single 0 1 : Fin 2 → E) + v 1 • Pi.single 1 1 := by
      funext i; fin_cases i <;> simp
    rw [hv]
    exact add_mem (Submodule.smul_mem _ _ e0) (Submodule.smul_mem _ _ e1)

theorem modular_hypLat {J : FractionalIdeal (𝓞 E)⁰ E} (hJ0 : J ≠ 0) (hJc : ∀ z ∈ J, cc z ∈ J)
    (x : Fin 2 → E) : x ∈ hypLat J ↔ ∀ y ∈ hypLat J, herm hypG x y ∈ J := by
  constructor
  · intro hx y hy
    obtain ⟨hx0, hx1⟩ := mem_hypLat.1 hx
    obtain ⟨hy0, hy1⟩ := mem_hypLat.1 hy
    rw [herm_hypG]
    refine (J : Submodule (𝓞 E) E).add_mem ?_ ?_
    · simpa using FractionalIdeal.mul_mem_mul hx0 (hJc _ hy1)
    · have : cc (y 0) ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) :=
        mem_one_fractionalIdeal_iff.2 (isIntegral_cc (mem_one_fractionalIdeal_iff.1 hy0))
      simpa using FractionalIdeal.mul_mem_mul hx1 this
  · intro h
    have h1 : x 1 ∈ J := by
      have := h (Pi.single 0 1) (mem_hypLat.2 ⟨by simp, by rw [Pi.single_eq_of_ne (by decide)]; exact (J : Submodule (𝓞 E) E).zero_mem⟩)
      simpa [herm_hypG, cc] using this
    have h0 : ∀ j ∈ J, x 0 * j ∈ J := fun j hj => by
      have := h (Pi.single 1 (cc j)) (mem_hypLat.2 ⟨by simp, by simpa using hJc j hj⟩)
      simpa [herm_hypG, cc] using this
    have hle : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) * J ≤ J := by
      refine FractionalIdeal.mul_le.2 fun i hi j hj => ?_
      obtain ⟨a, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
      rw [smul_mul_assoc]
      exact (J : Submodule (𝓞 E) E).smul_mem a (h0 j hj)
    have hle1 : FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) ≤ 1 := by
      calc FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0)
          = J⁻¹ * (FractionalIdeal.spanSingleton (𝓞 E)⁰ (x 0) * J) := by
            rw [mul_left_comm, inv_mul_cancel₀ hJ0, mul_one]
        _ ≤ J⁻¹ * J := mul_le_mul_right hle _
        _ = 1 := inv_mul_cancel₀ hJ0
    exact ⟨hle1 (FractionalIdeal.mem_spanSingleton_self _ _), h1⟩

theorem hypG_signature (τ : E →+* ℂ) : ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
    gram τ hypG Q = Matrix.diagonal fun a : Fin 2 => ((sgn 1 (a : ℕ) : ℝ) : ℂ) := by
  refine ⟨!![1, 1; 1 / 2, -1 / 2], by simp [Matrix.det_fin_two_of]; norm_num, ?_⟩
  ext a b
  fin_cases a <;> fin_cases b <;> simp [gram, hermC, col, hypG, sgn, Fin.sum_univ_two, map_ofNat] <;> norm_num

theorem iso_rank_two (H : Host E) (Y : Data E 2) (hp : Y.p0 = 1) (hY : IsSelfDualTr Y) :
    ∃ z : Fin 2 → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  haveI := H.unram
  obtain ⟨J, hJ0, hJc, hJ⟩ := GlobalTheory.Ker.OntoLat.exists_valueIdeal Y
  have HN := GlobalTheory.QNorm.hasseNormSt
  have hΨ : ∀ τ : E →+* ℂ, τ ∈ (Y.Ψ : Set (E →+* ℂ)) ∨ ComplexEmbedding.conjugate τ ∈ (Y.Ψ : Set (E →+* ℂ)) := by
    intro τ
    by_cases h : ComplexEmbedding.conjugate τ ∈ Y.Ψ
    · exact Or.inr h
    · exact Or.inl ((Y.cmType τ).mpr h)
  have hs : ∀ τ ∈ (Y.Ψ : Set (E →+* ℂ)), ∃ p : ℕ,
      (∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
        gram τ Y.Gm Q = Matrix.diagonal fun a : Fin 2 => ((sgn p (a : ℕ) : ℝ) : ℂ)) ∧
      ∃ Q : Matrix (Fin 2) (Fin 2) ℂ, Q.det ≠ 0 ∧
        gram τ hypG Q = Matrix.diagonal fun a : Fin 2 => ((sgn p (a : ℕ) : ℝ) : ℂ) := by
    intro τ hτ
    obtain ⟨Q, hQ, hg⟩ := Y.signature ⟨τ, hτ⟩
    rw [hp] at hg
    exact ⟨1, ⟨Q, hQ, hg⟩, hypG_signature τ⟩
  obtain ⟨P, hP, hPG⟩ := GlobalTheory.SelfDualGenus.congr_of_modular (G := Y.Gm) (G' := hypG) (L := Y.Λ)
    (L' := hypLat J) (GlobalTheory.LocalQuad.landherr_of_hasseNormSt HN) HN hJ0 hJc Y.Gm_herm hypG_herm Y.Gm_det
    hypG_det ⟨Y.Λ_fg, Y.Λ_span⟩ (isLattice_hypLat hJ0) (hJ Y.Λ (selfD_of_isSelfDualTr Y hY))
    (modular_hypLat hJ0 hJc) (GlobalTheory.Published.Landherr.congr_of_signature _ hΨ hs)
  refine ⟨P *ᵥ Pi.single 0 1, fun h => ?_, ?_⟩
  · have := congrFun (Matrix.eq_zero_of_mulVec_eq_zero hP h) 0
    simp at this
  · rw [GlobalTheory.SelfDualGenus.herm_mulVec, ← hPG, herm_hypG]
    simp

end GlobalTheory.EqCovol.IsoPlane

namespace GlobalTheory.EqCovol

theorem exists_isotropic_of_isSelfDualTr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (r : ℕ)
    (Y : Data E r), 1 ≤ Y.p0 → Y.p0 < r → GlobalTheory.EqCovol.IsSelfDualTr Y →
    ∃ z : Fin r → E, z ≠ 0 ∧ herm Y.Gm z z = 0 := by
  intro E _ _ _ H r Y h1 h2 hY
  by_cases hr : 3 ≤ r
  · obtain ⟨cu⟩ := GlobalTheory.CuspExist.nonempty_cuspFD GlobalTheory.QNorm.hasseNormSt E r 1 Y h1 (by omega) (by omega)
    exact ⟨cu.e 0, cu.ind.ne_zero 0, cu.iso 0 0⟩
  · obtain rfl : r = 2 := by omega
    exact IsoPlane.iso_rank_two H Y (by omega) hY

end GlobalTheory.EqCovol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearModelIntertwinerGoodSplitPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearModel_intertwiner_goodSplitPlace : ∀ {D : D7} {a a' : ℕ} (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig a a')
    (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (hTr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om'),
    ∃ ι : ((Fin a' × Fin (a + a') → Fv D.host.F Bs.v₁) → ℂ) →ₗ[ℂ] (Matrix (Fin a') (Fin (a + a')) (Fv D.host.F Bs.v₁) → ℂ), Γ.M'.IsLinBar Bs.ψ Bs.τ₁ 1 1 ι := by
  first | exact @GlobalTheory.LinBarExist.exists_isLinBar | exact GlobalTheory.LinBarExist.exists_isLinBar | (intros; apply GlobalTheory.LinBarExist.exists_isLinBar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitaryStatement
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_satake_sphericalVector_definiteUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w n → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w n).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ := by
  first | exact @GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec | exact GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec | (intros; apply GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec <;> assumption)
end

