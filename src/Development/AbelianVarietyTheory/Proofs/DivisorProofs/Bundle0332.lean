import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapIntegralClosureTensorEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0310
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformTwiceEqPosSmulReflect
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbhyankarResidueFieldIsSeparable
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory

theorem residueField_isSeparable_of_kummer_root (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)]
    (hinj : Function.Injective (algebraMap T V))
    (α : V) (ϖ u : T) (m k : ℕ) (hϖ : Irreducible ϖ) (hu : IsUnit u) (hk : IsUnit (k : T)) (hk0 : 0 < k) (hm0 : 0 < m)
    (hα : α ^ (m * k) = algebraMap T V (u * ϖ ^ k))
    (hgen : ∀ v : V, ∃ f g : Polynomial T, Polynomial.aeval α g ≠ 0 ∧ Polynomial.aeval α g * v = Polynomial.aeval α f) :
    Algebra.IsSeparable (IsLocalRing.ResidueField T) (IsLocalRing.ResidueField V) := by
  obtain ⟨γ, hγu, hαγ, hγk⟩ := GlobalTheory.T.dvr_exists_unit_pow_eq_mul_uniformizer T V hinj α ϖ u m k hϖ hu hk0 hα
  have hK := GlobalTheory.T.kummer_aeval_valuation_dvr T V hinj γ ϖ u k hϖ hu hk hk0 hγk
  have hres := GlobalTheory.T.kummer_residue_mem_adjoin_unit T V hinj α γ ϖ m hϖ hm0 hγu hαγ hK hgen
  set g := IsLocalRing.residue V γ
  have hsepg : IsSeparable (IsLocalRing.ResidueField T) g := by
    have hroot : Polynomial.aeval g (Polynomial.X ^ k - Polynomial.C (IsLocalRing.residue T u)) = 0 := by
      simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, g]
      rw [← map_pow, hγk]
      rw [sub_eq_zero]
      rfl
    have hsep : (Polynomial.X ^ k - Polynomial.C (IsLocalRing.residue T u)).Separable := by
      apply Polynomial.separable_X_pow_sub_C
      · have := hk.map (IsLocalRing.residue T)
        simpa using this.ne_zero
      · exact (hu.map (IsLocalRing.residue T)).ne_zero
    exact hsep.of_dvd (minpoly.dvd _ _ hroot)
  have htop : IntermediateField.adjoin (IsLocalRing.ResidueField T) {g} = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨v, rfl⟩ := IsLocalRing.residue_surjective x
    exact hres v
  have hS := (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable _ _).2 hsepg
  refine ⟨fun x => ?_⟩
  have hx : x ∈ IntermediateField.adjoin (IsLocalRing.ResidueField T) {g} := by rw [htop]; trivial
  have h := Algebra.IsSeparable.isSeparable (IsLocalRing.ResidueField T)
    (⟨x, hx⟩ : IntermediateField.adjoin (IsLocalRing.ResidueField T) {g})
  unfold IsSeparable at h ⊢
  rwa [IntermediateField.minpoly_eq] at h
end GlobalTheory

namespace GlobalTheory

theorem abhyankar_residueField_isSeparable : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → P.ramificationIdx S ∣ e) →
    (∀ P : Ideal (integralClosure S L), P.IsMaximal → ∀ [P.LiesOver (maximalIdeal S)],
      Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)) →
    ∀ [IsDomain D] [IsDiscreteValuationRing D] (Q : Ideal (integralClosure D (TensorProduct S D L))) [Q.IsMaximal],
    ∀ [Q.LiesOver (maximalIdeal D)],
    Algebra.IsSeparable (D ⧸ maximalIdeal D) (integralClosure D (TensorProduct S D L) ⧸ Q) := by
  intro S K L _ _ _ _ _ _ _ _ _ _ _ _ π e D _ _ hD hπ he hram hsep _ _ Q _ _
  obtain ⟨φ⟩ := hD
  have he0 : 0 < e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · subst h; simp at he
    · exact h
  haveI : Module.Finite S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) :=
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C π he0.ne')).finite
  haveI : Module.Finite S D := Module.Finite.equiv φ.symm.toLinearEquiv
  haveI : Algebra.IsIntegral S D := inferInstance
  haveI : Algebra.IsIntegral D (integralClosure D (TensorProduct S D L)) := inferInstance
  haveI : Algebra.IsIntegral S (integralClosure D (TensorProduct S D L)) := Algebra.IsIntegral.trans D
  haveI : Algebra.IsIntegral (integralClosure S L) (integralClosure D (TensorProduct S D L)) :=
    Algebra.IsIntegral.tower_top S
  set P : Ideal (integralClosure S L) := Q.under (integralClosure S L) with hPdef
  haveI hPmax : P.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  haveI : P.LiesOver (maximalIdeal S) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P)).symm⟩
  letI := Localization.AtPrime.algebraOfLiesOver P Q
  obtain ⟨hVd, hVdvr⟩ := GlobalTheory.T.localization_normalization_rootAdjoin_isDVR S K L π e D ⟨φ⟩ hπ he Q
  have hinj := GlobalTheory.T.integralClosure_tensor_localization_injective' S K L π e D ⟨φ⟩ hπ he Q
  have hπP : algebraMap S (integralClosure S L) π ∈ P :=
    (Ideal.mem_of_liesOver P (maximalIdeal S) π).mp ((IsLocalRing.mem_maximalIdeal π).2 hπ.not_isUnit)
  obtain ⟨ϖ, hϖ, u', hπu'⟩ := GlobalTheory.T.uniformizer_eq_pow_ramificationIdx_mul_unit_integralClosure S K L π e D P hπ hπP
  set u : Localization.AtPrime P := (u' : Localization.AtPrime P) with hu_def
  have hu : IsUnit u := u'.isUnit
  have hπu : algebraMap S (Localization.AtPrime P) π = u * ϖ ^ P.ramificationIdx S := by
    rw [hπu', mul_comm]
  have hk0 : 0 < P.ramificationIdx S := by
    rcases Nat.eq_zero_or_pos (P.ramificationIdx S) with h | h
    · exfalso
      have hmem : algebraMap S (Localization.AtPrime P) π ∈ maximalIdeal (Localization.AtPrime P) := by
        rw [IsScalarTower.algebraMap_apply S (integralClosure S L) (Localization.AtPrime P)]
        exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).2 hπP
      rw [hπu, h, pow_zero, mul_one] at hmem
      exact (IsLocalRing.mem_maximalIdeal _).1 hmem hu
    · exact h
  haveI : IsLocalHom (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) := by
    show IsLocalHom (Localization.localRingHom _ _ _ _)
    infer_instance
  have hdvd : P.ramificationIdx S ∣ e := hram P hPmax
  have hmk : e / P.ramificationIdx S * P.ramificationIdx S = e := Nat.div_mul_cancel hdvd
  have hm0 : 0 < e / P.ramificationIdx S := Nat.div_pos (Nat.le_of_dvd he0 hdvd) hk0
  have hk : IsUnit ((P.ramificationIdx S : ℕ) : Localization.AtPrime P) := by
    have h1 : IsUnit ((e : ℕ) : Localization.AtPrime P) := by
      simpa using he.map (algebraMap S (Localization.AtPrime P))
    rw [← hmk, Nat.cast_mul] at h1
    exact isUnit_of_mul_isUnit_right h1
  set t : D := φ.symm (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)) with ht_def
  have ht : t ^ e = algebraMap S D π := by
    have h0 : (AdjoinRoot.root (Polynomial.X ^ e - Polynomial.C π)) ^ e =
        algebraMap S (AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) π := by
      have h := AdjoinRoot.eval₂_root (Polynomial.X ^ e - Polynomial.C π)
      simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
      rw [sub_eq_zero] at h
      rw [h, AdjoinRoot.algebraMap_eq]
    rw [ht_def, ← map_pow, h0, AlgEquiv.commutes]
  have hα : (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
      (algebraMap D _ t)) ^ (e / P.ramificationIdx S * P.ramificationIdx S) =
      algebraMap (Localization.AtPrime P) (Localization.AtPrime Q) (u * ϖ ^ P.ramificationIdx S) := by
    rw [hmk, ← hπu, ← map_pow, ← map_pow, ht]
    rw [← IsScalarTower.algebraMap_apply S (Localization.AtPrime P) (Localization.AtPrime Q)]
    rw [← IsScalarTower.algebraMap_apply S D (integralClosure D (TensorProduct S D L))]
    rw [← IsScalarTower.algebraMap_apply S (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)]
  have hST : ∀ s : S, s ≠ 0 → algebraMap S (Localization.AtPrime P) s ≠ 0 := by
    intro s hs h
    have hSL : Function.Injective (algebraMap S L) := by
      rw [IsScalarTower.algebraMap_eq S K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
    have hSO : Function.Injective (algebraMap S (integralClosure S L)) := by
      intro a b hab
      apply hSL
      have := congrArg (fun x : integralClosure S L => (x : L)) hab
      simpa using this
    have hOT : Function.Injective (algebraMap (integralClosure S L) (Localization.AtPrime P)) :=
      IsLocalization.injective _ (P.primeCompl_le_nonZeroDivisors)
    rw [IsScalarTower.algebraMap_apply S (integralClosure S L) (Localization.AtPrime P)] at h
    exact hs (hSO (hOT (h.trans (map_zero _).symm) |>.trans (map_zero _).symm))
  have hpoly : ∀ f : Polynomial (integralClosure S L),
      Polynomial.aeval (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap D _ t)) (f.map (algebraMap (integralClosure S L) (Localization.AtPrime P))) =
      algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (Polynomial.aeval (algebraMap D _ t) f) := by
    intro f
    rw [Polynomial.aeval_map_algebraMap, Polynomial.aeval_algebraMap_apply]
  have hgen : ∀ v : Localization.AtPrime Q, ∃ f g : Polynomial (Localization.AtPrime P),
      Polynomial.aeval (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap D _ t)) g ≠ 0 ∧
      Polynomial.aeval (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap D _ t)) g * v =
      Polynomial.aeval (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap D _ t)) f := by
    intro v
    obtain ⟨⟨b, c⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl v
    obtain ⟨fb, sb, hsb, hb⟩ := GlobalTheory.T.exists_mul_eq_aeval_root_normalisation S K L π e D φ b
    obtain ⟨fc, sc, hsc, hc⟩ := GlobalTheory.T.exists_mul_eq_aeval_root_normalisation S K L π e D φ c.1
    refine ⟨Polynomial.C (algebraMap S _ sc) * fb.map (algebraMap (integralClosure S L) (Localization.AtPrime P)),
      Polynomial.C (algebraMap S _ sb) * fc.map (algebraMap (integralClosure S L) (Localization.AtPrime P)), ?_, ?_⟩
    · rw [map_mul, Polynomial.aeval_C, hpoly, ← hc]
      refine mul_ne_zero ?_ ?_
      · rw [← IsScalarTower.algebraMap_apply]
        rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime P) (Localization.AtPrime Q)]
        exact fun h => hST sb hsb (hinj (h.trans (map_zero _).symm))
      · rw [map_mul]
        refine mul_ne_zero ?_ (IsLocalization.map_units (Localization.AtPrime Q) c).ne_zero
        rw [← IsScalarTower.algebraMap_apply]
        rw [IsScalarTower.algebraMap_apply S (Localization.AtPrime P) (Localization.AtPrime Q)]
        exact fun h => hST sc hsc (hinj (h.trans (map_zero _).symm))
    · dsimp only
      rw [map_mul, map_mul, Polynomial.aeval_C, Polynomial.aeval_C, hpoly, hpoly, ← hb, ← hc, map_mul, map_mul]
      simp only [← IsScalarTower.algebraMap_apply S (Localization.AtPrime P) (Localization.AtPrime Q)]
      simp only [IsScalarTower.algebraMap_apply S (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)]
      have hm := IsLocalization.mk'_spec (Localization.AtPrime Q) b c
      linear_combination (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap S _ sb) * algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q)
        (algebraMap S _ sc)) * hm
  haveI : IsDedekindDomain (integralClosure S L) := integralClosure.isDedekindDomain S K L
  haveI : FaithfulSMul S (integralClosure S L) := by
    rw [faithfulSMul_iff_algebraMap_injective]
    have hSL : Function.Injective (algebraMap S L) := by
      rw [IsScalarTower.algebraMap_eq S K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective S K)
    intro a b hab
    apply hSL
    have := congrArg (fun x : integralClosure S L => (x : L)) hab
    simpa using this
  have hP0 : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field S) P
  haveI : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain _ hP0 _
  have hsepV := residueField_isSeparable_of_kummer_root (Localization.AtPrime P) (Localization.AtPrime Q) hinj
    (algebraMap (integralClosure D (TensorProduct S D L)) (Localization.AtPrime Q) (algebraMap D _ t))
    ϖ u (e / P.ramificationIdx S) (P.ramificationIdx S) hϖ hu hk hk0 hm0 hα hgen
  have h1 : Algebra.IsSeparable P.ResidueField Q.ResidueField := hsepV
  have h2 : Algebra.IsSeparable (integralClosure S L ⧸ P) (integralClosure D (TensorProduct S D L) ⧸ Q) :=
    Algebra.isSeparable_residueField_iff.mp h1
  have h3 : Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P) := hsep P hPmax
  letI := Ideal.Quotient.field (maximalIdeal S)
  letI := Ideal.Quotient.field (maximalIdeal D)
  letI := Ideal.Quotient.field P
  letI := Ideal.Quotient.field Q
  haveI : Q.LiesOver (maximalIdeal S) := Ideal.LiesOver.trans Q P (maximalIdeal S)
  haveI : IsScalarTower (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P)
      (integralClosure D (TensorProduct S D L) ⧸ Q) := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Ideal.Quotient.algebraMap_mk_of_liesOver]
    rw [← IsScalarTower.algebraMap_apply]
  haveI h4 : Algebra.IsSeparable (S ⧸ maximalIdeal S) (integralClosure D (TensorProduct S D L) ⧸ Q) :=
    Algebra.IsSeparable.trans (S ⧸ maximalIdeal S) (integralClosure S L ⧸ P) _
  haveI : (maximalIdeal D).LiesOver (maximalIdeal S) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (maximalIdeal D))).symm⟩
  haveI : IsScalarTower (S ⧸ maximalIdeal S) (D ⧸ maximalIdeal D)
      (integralClosure D (TensorProduct S D L) ⧸ Q) := IsScalarTower.of_algebraMap_eq fun x => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [Ideal.Quotient.algebraMap_mk_of_liesOver]
    rw [← IsScalarTower.algebraMap_apply]
  exact Algebra.isSeparable_tower_top_of_isSeparable (S ⧸ maximalIdeal S) (D ⧸ maximalIdeal D) _
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnnihilatorOfDirectedEssentiallyEtaleUnionStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_of_directed_essentiallyEtale_union : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → ∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0 := by
  first | exact @GlobalTheory.ann_of_directed_essEtale | exact GlobalTheory.ann_of_directed_essEtale | (intros; apply GlobalTheory.ann_of_directed_essEtale <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AugmentedExactIff
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.AugExact

theorem augmented_exact_iff (C : Type 2) [Category.{1} C] [Abelian C] (K : SimplicialObject C) (B : C)
    (f : K ⟶ (SimplicialObject.const C).obj B) :
    QuasiIso ((AlgebraicTopology.alternatingFaceMapComplex C).map f) ↔
      (Epi (f.app (op (SimplexCategory.mk (0)))) ∧
        (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0,
          (ShortComplex.mk _ _ w).Exact) ∧
        ∀ n : ℕ, ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1)) := by
  let e := (SimplicialObject.Augmented.ExtraDegeneracy.const B).homotopyEquiv
  let g : (AlgebraicTopology.alternatingFaceMapComplex C).obj ((SimplicialObject.const C).obj B) ⟶
      (ChainComplex.single₀ C).obj B := e.hom
  haveI : QuasiIso g := e.quasiIso_hom
  have hg : g.f 0 = 𝟙 B := AlgebraicTopology.AlternatingFaceMapComplex.ε_app_f_zero _
  rw [← quasiIso_iff_comp_right _ g, quasiIso_iff]
  set φ := (AlgebraicTopology.alternatingFaceMapComplex C).map f ≫ g with hφ
  have h0 : φ.f 0 = f.app (op (SimplexCategory.mk 0)) := by
    rw [hφ, HomologicalComplex.comp_f, hg]
    exact Category.comp_id _
  have hd : ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).d 1 0 =
      K.δ (n := 0) 0 - K.δ (n := 0) 1 := by
    change (AlgebraicTopology.AlternatingFaceMapComplex.obj K).d (0 + 1) 0 = _
    rw [AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two]
    simp [sub_eq_add_neg]
  have w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0 := by
    simp [Preadditive.sub_comp, SimplicialObject.δ_naturality, SimplicialObject.δ]
  have he : Epi (φ.f 0) ↔ Epi (f.app (op (SimplexCategory.mk (0)))) := h0 ▸ Iff.rfl
  have hz : QuasiIsoAt φ 0 ↔ (Epi (f.app (op (SimplexCategory.mk (0)))) ∧
      (∃ w : (K.δ (n := 0) 0 - K.δ (n := 0) 1) ≫ f.app (op (SimplexCategory.mk (0))) = 0,
        (ShortComplex.mk _ _ w).Exact)) := by
    rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros' _ rfl rfl rfl]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨he.1 h2, w, (ShortComplex.exact_iff_of_iso ?_).1 h1⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (hd.symm.trans (Category.comp_id _).symm))
        ((Category.id_comp _).trans (h0.symm.trans (Category.comp_id _).symm))
    · rintro ⟨h1, _, h2⟩
      refine ⟨(ShortComplex.exact_iff_of_iso ?_).1 h2, he.2 h1⟩
      exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        ((Category.id_comp _).trans (hd.trans (Category.comp_id _).symm))
        ((Category.id_comp _).trans (h0.trans (Category.comp_id _).symm))
  have hs : ∀ n : ℕ, QuasiIsoAt φ (n + 1) ↔
      ((AlgebraicTopology.alternatingFaceMapComplex C).obj K).ExactAt (n + 1) :=
    fun n => quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)
  constructor
  · intro h
    exact ⟨(hz.1 (h 0)).1, (hz.1 (h 0)).2, fun n => (hs n).1 (h (n + 1))⟩
  · rintro ⟨h1, h2, h3⟩ i
    cases i with
    | zero => exact hz.2 ⟨h1, h2⟩
    | succ n => exact (hs n).2 (h3 n)

end GlobalTheory.EtC.AugExact
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwOCommD
section
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v

noncomputable section
namespace GlobalTheory.EZ.AWChain

theorem bop_comp {n m p q r s : ℕ} (α : SimplexCategory.mk p ⟶ SimplexCategory.mk n)
    (β : SimplexCategory.mk q ⟶ SimplexCategory.mk m) (α' : SimplexCategory.mk r ⟶ SimplexCategory.mk p)
    (β' : SimplexCategory.mk s ⟶ SimplexCategory.mk q) :
    bop α β ≫ bop α' β' = bop (α' ≫ α) (β' ≫ β) := by
  have := Free.single_comp_single (R := ℤ) (C := SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ)
    (X := (op (SimplexCategory.mk n), op (SimplexCategory.mk m)))
    (Y := (op (SimplexCategory.mk p), op (SimplexCategory.mk q)))
    (Z := (op (SimplexCategory.mk r), op (SimplexCategory.mk s))) (α.op, β.op) (α'.op, β'.op) 1 1
  simp only [mul_one] at this
  exact this

theorem comp_apply' {a b c : ℕ} (f : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (g : SimplexCategory.mk b ⟶ SimplexCategory.mk c) (j : Fin (a+1)) :
    ((f ≫ g).toOrderHom j : ℕ) = (g.toOrderHom (f.toOrderHom j) : ℕ) := rfl

theorem hom_ext' {a b : ℕ} (f g : SimplexCategory.mk a ⟶ SimplexCategory.mk b)
    (h : ∀ j : Fin (a+1), (f.toOrderHom j : ℕ) = (g.toOrderHom j : ℕ)) : f = g := by
  apply SimplexCategory.Hom.ext
  ext j
  exact h j

theorem faceFun_lt {i j : ℕ} (h : j < i) : faceFun i j = j := if_pos h
theorem faceFun_ge {i j : ℕ} (h : i ≤ j) : faceFun i j = j + 1 := if_neg (by omega)

theorem backc_apply (n a b : ℕ) (j : Fin (b+1)) : ((backc n a b).toOrderHom j : ℕ) = min n (a + j) := rfl
theorem idc_apply (n m : ℕ) (j : Fin (m+1)) : ((idc n m).toOrderHom j : ℕ) = min n j := rfl
theorem fc_apply (n m i : ℕ) (j : Fin (m+1)) : ((fc n m i).toOrderHom j : ℕ) = min n (faceFun i j) := rfl

section
variable (a b : ℕ)

theorem front_face_low (i : ℕ) (hi : i ≤ a) :
    idc (a+b) a ≫ fc (a+b+1) (a+b) i = fc (a+1) a i ≫ idc (a+b+1) (a+1) := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rcases lt_or_ge (j:ℕ) i with h | h
  · rw [faceFun_lt (by omega), faceFun_lt h]; omega
  · rw [faceFun_ge (by omega), faceFun_ge h]; omega

theorem back_face_low (i : ℕ) (hi : i ≤ a) :
    backc (a+b) a b ≫ fc (a+b+1) (a+b) i = idc b b ≫ backc (a+b+1) (a+1) b := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_ge (by omega)]; omega

theorem front_face_high (i : ℕ) (hi : a < i) :
    idc (a+b) a ≫ fc (a+b+1) (a+b) i = idc a a ≫ idc (a+b+1) a := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_lt (by omega)]; omega

theorem back_face_high (j : ℕ) (hj : j ≤ b) :
    backc (a+b) a b ≫ fc (a+b+1) (a+b) (a+1+j) = fc (b+1) b (j+1) ≫ backc (a+b+1) a (b+1) := by
  apply hom_ext'; intro k; have hk := k.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rcases lt_or_ge (k:ℕ) (j+1) with h | h
  · rw [faceFun_lt (by omega), faceFun_lt h]; omega
  · rw [faceFun_ge (by omega), faceFun_ge h]; omega

theorem front_face_cancel : fc (a+1) a (a+1) ≫ idc (a+b+1) (a+1) = idc a a ≫ idc (a+b+1) a := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_lt (by omega)]; omega

theorem back_face_cancel : idc b b ≫ backc (a+b+1) (a+1) b = fc (b+1) b 0 ≫ backc (a+b+1) a (b+1) := by
  apply hom_ext'; intro j; have hj := j.isLt
  simp only [comp_apply', fc_apply, idc_apply, backc_apply]
  rw [faceFun_ge (by omega)]; omega

end

theorem dT_h (a b : ℕ) : dT (a+1) b a b = ∑ i ∈ Finset.range (a+1+1), ((-1 : ℤ) ^ i) • bop (fc (a+1) a i) (idc b b) := by
  simp [dT, dH, dV]

theorem dT_v (a b : ℕ) : dT a (b+1) a b = ((-1 : ℤ) ^ a) • ∑ j ∈ Finset.range (b+1+1), ((-1 : ℤ) ^ j) • bop (idc a a) (fc (b+1) b j) := by
  simp [dT, dH, dV]

theorem dT_zero (x y a b : ℕ) (h1 : ¬ (x = a + 1 ∧ y = b)) (h2 : ¬ (x = a ∧ y = b + 1)) : dT x y a b = 0 := by
  simp [dT, dH, dV, h1, h2]

end GlobalTheory.EZ.AWChain

namespace GlobalTheory.EZ
open GlobalTheory.EZ.AWChain

theorem awO_comm_d : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b =
    ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := by
  intro n a b hab
  subst hab
  rw [Finset.sum_eq_add (a + 1, b) (a, b + 1) (by simp)]
  rotate_left
  · rintro c hc ⟨h1, h2⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hc
    rw [dT_zero, Limits.comp_zero]
    · rintro ⟨e1, e2⟩; exact h1 (Prod.ext e1 e2)
    · rintro ⟨e1, e2⟩; exact h2 (Prod.ext e1 e2)
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  · intro h; exact absurd (by rw [Finset.HasAntidiagonal.mem_antidiagonal]; omega) h
  simp only [dT_h, dT_v]
  have e1 : awO (a + b + 1) (a + 1) b = bop (idc (a+b+1) (a+1)) (backc (a+b+1) (a+1) b) := if_pos (by omega)
  have e2 : awO (a + b + 1) a (b + 1) = bop (idc (a+b+1) a) (backc (a+b+1) a (b+1)) := if_pos (by omega)
  have e3 : awO (a + b) a b = bop (idc (a+b) a) (backc (a+b) a b) := if_pos rfl
  have e4 : dD (a + b + 1) (a + b) = ∑ i ∈ Finset.range (a+b+1+1),
      ((-1 : ℤ) ^ i) • bop (fc (a+b+1) (a+b) i) (fc (a+b+1) (a+b) i) := if_pos rfl
  rw [e1, e2, e3, e4]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, Preadditive.zsmul_comp, Preadditive.comp_zsmul,
    bop_comp]
  rw [show a + b + 1 + 1 = (a + 1) + (b + 1) by omega, Finset.sum_range_add]
  conv_rhs => rw [Finset.sum_range_succ _ (a + 1), Finset.sum_range_succ' _ (b + 1), smul_add]
  have hA : ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) •
      bop (idc (a+b) a ≫ fc (a+b+1) (a+b) i) (backc (a+b) a b ≫ fc (a+b+1) (a+b) i) =
      ∑ i ∈ Finset.range (a + 1), ((-1 : ℤ) ^ i) •
      bop (fc (a+1) a i ≫ idc (a+b+1) (a+1)) (idc b b ≫ backc (a+b+1) (a+1) b) := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [front_face_low a b i (by omega), back_face_low a b i (by omega)]
  have hB : ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ (a + 1 + j)) •
      bop (idc (a+b) a ≫ fc (a+b+1) (a+b) (a + 1 + j)) (backc (a+b) a b ≫ fc (a+b+1) (a+b) (a + 1 + j)) =
      ((-1 : ℤ) ^ a) • ∑ j ∈ Finset.range (b + 1), ((-1 : ℤ) ^ (j + 1)) •
      bop (idc a a ≫ idc (a+b+1) a) (fc (b+1) b (j + 1) ≫ backc (a+b+1) a (b+1)) := by
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [front_face_high a b (a + 1 + j) (by omega), back_face_high a b j (by omega), smul_smul, ← pow_add, show a + (j + 1) = a + 1 + j by omega]
  have hC : ((-1 : ℤ) ^ (a + 1)) • bop (fc (a+1) a (a + 1) ≫ idc (a+b+1) (a+1)) (idc b b ≫ backc (a+b+1) (a+1) b)
      + ((-1 : ℤ) ^ a) • (((-1 : ℤ) ^ 0) • bop (idc a a ≫ idc (a+b+1) a) (fc (b+1) b 0 ≫ backc (a+b+1) a (b+1))) = 0 := by
    rw [front_face_cancel, back_face_cancel, smul_smul, pow_zero, mul_one, pow_succ, mul_neg_one, neg_smul, neg_add_cancel]
  rw [hA, hB, add_add_add_comm, hC, add_zero]

end GlobalTheory.EZ

example : ∀ (n a b : ℕ), a + b = n → dD (n + 1) n ≫ awO n a b = ∑ x ∈ Finset.HasAntidiagonal.antidiagonal (n + 1), awO (n + 1) x.1 x.2 ≫ dT x.1 x.2 a b := GlobalTheory.EZ.awO_comm_d
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapCompAlgebraMap
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC

theorem chains_spMap_comp (R : Type) [CommRing R] {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (g : A →+* B)
    (h : B →+* C) : (chains R).map (spMap h) ≫ (chains R).map (spMap g) = (chains R).map (spMap (h.comp g)) := by
  rw [← Functor.map_comp]
  congr 1
  simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
  rfl

theorem awayMap_comp_algebraMap {A B : Type} [CommRing A] [CommRing B] (g : A →+* B) (f : A) :
    (Localization.awayMap g f).comp (algebraMap A (Localization.Away f)) = (algebraMap B (Localization.Away (g f))).comp g :=
  IsLocalization.map_comp _

theorem excision_square_comm (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    (chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) ≫ (chains R).map (spMap (algebraMap A A')) =
      (chains R).map (spMap (Localization.awayMap (algebraMap A A') f)) ≫
        (chains R).map (spMap (algebraMap A (Localization.Away f))) := by
  rw [chains_spMap_comp, chains_spMap_comp, awayMap_comp_algebraMap]

def excisionConeMap (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) :
    mappingCone ((chains R).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))) ⟶
      mappingCone ((chains R).map (spMap (algebraMap A (Localization.Away f)))) :=
  mappingCone.map _ _ _ _ (excision_square_comm R A A' f)

end GlobalTheory.EtC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformMemSchwartzBruhatStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bicharacterFourierTransform_mem_schwartzBruhat : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∀ φ ∈ SB X, four μ e φ ∈ SB X := by
  first | exact @GlobalTheory.KSp.FourMem.four_mem_SB | exact GlobalTheory.KSp.FourMem.four_mem_SB | (intros; apply GlobalTheory.KSp.FourMem.four_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BicharacterFourierTransformTwiceEqPosSmulReflectStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bicharacterFourierTransform_twice_eq_pos_smul_reflect : ∀ (X : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (_ : Good X) (μ : Measure X) [μ.IsAddHaarMeasure] (e : X → X → ℂ), IsPair e → ∃ C : ℝ, 0 < C ∧ ∀ φ ∈ SB X, ∀ x, four μ e (four μ e φ) x = (C : ℂ) * φ (-x) := by
  first | exact @GlobalTheory.KSp.four_four | exact GlobalTheory.KSp.four_four | (intros; apply GlobalTheory.KSp.four_four <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardResidueFieldLocalOrderUnitaryProdStatement
section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_residueField_localOrder_unitary_prod : ∀ (K : UQ) (B₁ B₂ : InvAlg K), B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → (B₁.P * B₂.P).Separable → IsIntegral K.O B₁.g → IsIntegral K.O B₂.g → ∀ hl : IsLocalRing (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)), ∃ d : ℕ, Odd d ∧ Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({(B₁.prod B₂).g} : Set (B₁.prod B₂).A)) _ hl) = K.q ^ (2 * d) := by
  first | exact @GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any | exact GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any | (intros; apply GlobalTheory.UnitLemma.ResDeg.card_residueField_prod_any <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CochainEqOfSameDegreeChartMorphismStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cochain_eq_of_same_degree_chartMorphism : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (h : C1 K.Oc) (l : Λ), (∀ (k : K.K) (T : K.Obj) (χ : K.jet k ⟶ T), χ.deg = l → h _ _ (jet0 k ≫ χ) = h _ _ (jet1 k ≫ χ)) → ∀ (k : K.K) (T : K.Obj) (f : K.triv k ⟶ T), f.deg = l → h _ _ f = h _ _ (ptHom T (Charts.Hom.le f)) := by
  first | exact @GlobalTheory.AnPer.Charts.cochain_eq_ptHom | exact GlobalTheory.AnPer.Charts.cochain_eq_ptHom | (intros; apply GlobalTheory.AnPer.Charts.cochain_eq_ptHom <;> assumption)
end

