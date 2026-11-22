import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0212
import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0213

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIotaScalarExactPair
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv.ScalarEx

theorem det_add_rows {C : Type} [Field C] {N : ℕ} (S : Fin N → Prop) [DecidablePred S]
    (W : Submodule C (Fin N → C)) (hW : Module.finrank C W = Fintype.card {i // S i})
    (r s : Fin N → Fin N → C) (hr : ∀ i, S i → r i ∈ W) (hd0 : ∀ i, S i → s i = r i)
    (hd : ∀ i, ¬ S i → s i - r i ∈ W) :
    (Matrix.of s).det = (Matrix.of r).det := by
  classical
  by_cases hli : LinearIndependent C (fun i : {i // S i} => r i)
  · have hspan : Submodule.span C (Set.range (fun i : {i // S i} => r i)) = W := by
      apply Submodule.eq_of_le_of_finrank_eq
      · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hr i i.2
      · rw [finrank_span_eq_card hli, hW]
    have hc : ∀ j, ∃ c : {i // S i} → C, (S j → c = 0) ∧ ∑ i, c i • r i = s j - r j := by
      intro j
      by_cases hj : S j
      · exact ⟨0, fun _ => rfl, by simp [hd0 j hj]⟩
      · have h1 := hd j hj
        rw [← hspan] at h1
        obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun C).1 h1
        exact ⟨c, fun h => absurd h hj, hc⟩
    choose c hc0 hc using hc
    let Q : Matrix {i // S i} (Fin N) C := Matrix.of fun i l => if i.1 = l then 1 else 0
    have hQ : ∀ {κ : Type} (M : Matrix (Fin N) κ C) (i : {i // S i}) (k : κ),
        (Q * M) i k = M i k := by
      intro κ M i k
      simp [Q, Matrix.mul_apply]
    have h1 : Matrix.of s = (1 + Matrix.of c * Q) * Matrix.of r := by
      ext j k
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, Matrix.add_apply, Matrix.mul_apply]
      have h2 := congrFun (hc j) k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at h2
      simp only [hQ, Matrix.of_apply, h2]
      ring
    have h2 : Q * Matrix.of c = 0 := by
      ext i k
      rw [hQ]
      simp [hc0 i.1 i.2]
    rw [h1, Matrix.det_mul, Matrix.det_one_add_mul_comm, h2]
    simp
  · have h1 : (Matrix.of r).det = 0 := by
      by_contra h
      exact hli ((Matrix.linearIndependent_rows_of_det_ne_zero h).comp _ Subtype.val_injective)
    have h2 : (Matrix.of s).det = 0 := by
      by_contra h
      have h3 := (Matrix.linearIndependent_rows_of_det_ne_zero h).comp _
        (Subtype.val_injective (p := S))
      apply hli
      have h4 : (fun i : {i // S i} => r i) = (fun i => Matrix.of s i) ∘ Subtype.val :=
        funext fun i => (hd0 i.1 i.2).symm
      rw [h4]
      exact h3
    rw [h1, h2]

theorem exists_ginv {C V : Type} [Field C] [AddCommGroup V] [Module C V] (f : V →ₗ[C] V) :
    ∃ g : V →ₗ[C] V, ∀ z, f (g (f z)) = f z := by
  obtain ⟨s, hs⟩ := LinearMap.exists_rightInverse_of_surjective f.rangeRestrict
    (LinearMap.range_rangeRestrict f)
  obtain ⟨t, ht⟩ := LinearMap.exists_leftInverse_of_injective (LinearMap.range f).subtype
    (Submodule.ker_subtype _)
  refine ⟨s ∘ₗ t, fun z => ?_⟩
  have h1 : t (f z) = f.rangeRestrict z := LinearMap.congr_fun ht (f.rangeRestrict z)
  have h2 := congrArg Subtype.val (LinearMap.congr_fun hs (f.rangeRestrict z))
  rw [LinearMap.comp_apply, h1]
  exact h2

theorem card_lt {N a : ℕ} (h : a ≤ N) : Fintype.card {i : Fin N // (i : ℕ) < a} = a := by
  rw [Fintype.card_subtype, Fin.card_filter_val_lt]
  exact min_eq_right h

theorem exists_iotaScalar (C : Type) [Field C] (N : ℕ) (α β : Matrix (Fin N) (Fin N) C)
    (hab : α * β = 0) (hba : β * α = 0) (hex : ∀ x, α *ᵥ x = 0 → ∃ y, x = β *ᵥ y) :
    ∃ lam : C, lam ≠ 0 ∧ IotaScalar α β β.rank lam := by
  classical
  set U : Submodule C (Fin N → C) := LinearMap.range β.mulVecLin with hUdef
  have hU : Module.finrank C U = β.rank := rfl
  have haN : β.rank ≤ N := by simpa using Matrix.rank_le_width β
  have hUker : ∀ z, z ∈ U ↔ α *ᵥ z = 0 := by
    intro z
    constructor
    · rintro ⟨y, rfl⟩
      simp [Matrix.mulVec_mulVec, hab]
    · intro h
      obtain ⟨y, rfl⟩ := hex z h
      exact ⟨y, rfl⟩
  have hker : LinearMap.ker α.mulVecLin = U := by
    ext z
    rw [hUker]; simp
  have hkerβ : LinearMap.range α.mulVecLin = LinearMap.ker β.mulVecLin := by
    apply Submodule.eq_of_le_of_finrank_eq
    · rintro _ ⟨y, rfl⟩
      simp [Matrix.mulVec_mulVec, hba]
    · have h1 := LinearMap.finrank_range_add_finrank_ker α.mulVecLin
      have h2 := LinearMap.finrank_range_add_finrank_ker β.mulVecLin
      rw [hker] at h1
      rw [← hUdef] at h2
      omega
  obtain ⟨F, hF⟩ := Submodule.exists_isCompl U
  have hFr : Module.finrank C F = Fintype.card {i : Fin N // ¬ (i : ℕ) < β.rank} := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hF
    rw [Fintype.card_subtype_compl, card_lt haN]
    simp only [Module.finrank_fintype_fun_eq_card] at h1
    omega
  obtain ⟨q, hqF, hqU⟩ : ∃ q : (Fin N → C) →ₗ[C] (Fin N → C),
      (∀ z, q z ∈ F) ∧ ∀ z, z - q z ∈ U := by
    refine ⟨F.subtype ∘ₗ F.projectionOnto U hF.symm, fun z => Subtype.prop _, fun z => ?_⟩
    refine (Submodule.ker_projectionOnto hF.symm).le ?_
    rw [LinearMap.mem_ker, map_sub, LinearMap.comp_apply, Submodule.subtype_apply,
      Submodule.projectionOnto_apply_left, sub_self]
  obtain ⟨g, hg⟩ := exists_ginv α.mulVecLin
  simp only [Matrix.mulVecLin_apply] at hg
  let Θ : (Fin N → C) →ₗ[C] (Fin N → C) := β.mulVecLin + q ∘ₗ g
  have hΘ : ∀ z, Θ z = β *ᵥ z + q (g z) := fun z => rfl
  have hq : ∀ z, α *ᵥ q z = α *ᵥ z := by
    intro z
    have h1 := (hUker _).1 (hqU z)
    rw [Matrix.mulVec_sub, sub_eq_zero] at h1
    exact h1.symm
  have hΘα : ∀ z, Θ (α *ᵥ z) = q (g (α *ᵥ z)) := by
    intro z
    rw [hΘ, Matrix.mulVec_mulVec, hba, Matrix.zero_mulVec, zero_add]
  let M := LinearMap.toMatrix' Θ
  have hM : ∀ z, M *ᵥ z = Θ z := fun z => LinearMap.toMatrix'_mulVec Θ z
  have hdet : M.det ≠ 0 := by
    intro h
    obtain ⟨z, hz, h0⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
    apply hz
    rw [hM] at h0
    have h1 : β *ᵥ z ∈ F := by
      have h2 : β *ᵥ z = - q (g z) := eq_neg_of_add_eq_zero_left (by rw [← hΘ, h0])
      rw [h2]; exact F.neg_mem (hqF _)
    have h2 : β *ᵥ z = 0 := (Submodule.disjoint_def.1 hF.disjoint) _ ⟨z, rfl⟩ h1
    have h3 : z ∈ LinearMap.range α.mulVecLin := by rw [hkerβ]; exact h2
    obtain ⟨w, rfl⟩ := h3
    simp only [Matrix.mulVecLin_apply] at h0 ⊢
    rw [← hg, ← hq, ← hΘα, h0, Matrix.mulVec_zero]
  refine ⟨M.det⁻¹, inv_ne_zero hdet, fun x y hx hy => ?_⟩
  let m : Fin N → Fin N → C := fun i => if (i : ℕ) < β.rank then x i else Θ (y i)
  have h1 : (Matrix.of x).det = (Matrix.of m).det := by
    refine det_add_rows (fun i => (i : ℕ) < β.rank) U (by rw [card_lt haN, hU]) m x ?_ ?_ ?_
    · intro i hi
      simp only [m, if_pos hi]
      exact ⟨y i, (hx i hi).symm⟩
    · intro i hi
      simp only [m, if_pos hi]
    · intro i hi
      simp only [m, if_neg hi]
      rw [hUker, hy i (not_lt.1 hi), hΘα, Matrix.mulVec_sub, hq, hg, sub_self]
  have h2 : (Matrix.of fun i => Θ (y i)).det = (Matrix.of m).det := by
    refine det_add_rows (fun i => ¬ (i : ℕ) < β.rank) F hFr m _ ?_ ?_ ?_
    · intro i hi
      simp only [m, if_neg hi]
      rw [hy i (not_lt.1 hi), hΘα]
      exact hqF _
    · intro i hi
      simp only [m, if_neg hi]
    · intro i hi
      have hi' := not_not.1 hi
      simp only [m, if_pos hi']
      rw [hΘ, hx i hi', add_sub_cancel_left]
      exact hqF _
  have h3 : (Matrix.of fun i => Θ (y i)) = Matrix.of y * Mᵀ := by
    ext i k
    rw [Matrix.of_apply, ← hM]
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
  rw [h3, Matrix.det_mul, Matrix.det_transpose, ← h1] at h2
  rw [← h2]
  field_simp

end GlobalTheory.DetInv.ScalarEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalStageTensorPolynomialOrigin
section
open IsLocalRing Polynomial

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.LocalStage

theorem mem_originIdeal_iff {T : Type} [CommRing T] [IsLocalRing T] (f : Polynomial T) :
    f ∈ GlobalTheory.KeyOriginCut.originIdeal T ↔ f.coeff 0 ∈ maximalIdeal T := by
  constructor
  · intro hf
    have hle : GlobalTheory.KeyOriginCut.originIdeal T ≤
        (maximalIdeal T).comap (Polynomial.constantCoeff : Polynomial T →+* T) := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simpa using hx
      · rw [Ideal.span_le]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst hx
        simp
    simpa using hle hf
  · intro hf
    rw [← Polynomial.X_mul_divX_add f]
    refine Ideal.add_mem _ ?_ ?_
    · exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.subset_span rfl))
    · exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hf)

theorem comap_originIdeal {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] :
    (GlobalTheory.KeyOriginCut.originIdeal S).comap (Polynomial.mapRingHom φ) =
      GlobalTheory.KeyOriginCut.originIdeal R := by
  ext f
  rw [Ideal.mem_comap, mem_originIdeal_iff, mem_originIdeal_iff]
  simp only [Polynomial.coe_mapRingHom, Polynomial.coeff_map]
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_map_iff]

theorem localStage : ∀ (T O : Type) [CommRing T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O],
    (maximalIdeal O).comap (algebraMap (Polynomial T) O) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (A : Type) [CommRing A] [IsLocalRing A] (i : A →+* T), IsLocalHom i →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (A' : Type) [CommRing A'] [IsLocalRing A'] (ι : A →+* A') (α : A' →+* T), α.comp ι = i → IsLocalHom α →
    ∃ (E' : Type) (_ : CommRing E') (_ : Algebra (Polynomial A') E') (_ : Algebra.Etale (Polynomial A') E')
      (Q' : Ideal E') (_ : Q'.IsPrime),
      Q'.comap (algebraMap (Polynomial A') E') = GlobalTheory.KeyOriginCut.originIdeal A' ∧
      ∃ (β : Localization.AtPrime QA →+* Localization.AtPrime Q') (γ : Localization.AtPrime Q' →+* O),
        ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C).comp ι =
          β.comp ((algebraMap (Polynomial A) (Localization.AtPrime QA)).comp Polynomial.C) ∧
        γ.comp β = jA ∧
        γ.comp ((algebraMap (Polynomial A') (Localization.AtPrime Q')).comp Polynomial.C) =
          (algebraMap T O).comp α := by
  intro T O _ _ _ _ _ _ _ hO A _ _ i hi EA _ _ _ QA _ hQA jA hjA A' _ _ ι α hαι hα
  letI : Algebra (Polynomial A) (Polynomial A') := (Polynomial.mapRingHom ι).toAlgebra
  letI : Algebra (Polynomial A) O := ((algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i)).toAlgebra
  haveI : Algebra.Etale (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) :=
    Algebra.Etale.baseChange (Polynomial A) EA (Polynomial A')
  let f : Polynomial A' →ₐ[Polynomial A] O :=
    { toRingHom := (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α)
      commutes' := by
        intro p
        change (algebraMap (Polynomial T) O) (Polynomial.map α (Polynomial.map ι p)) =
          (algebraMap (Polynomial T) O) (Polynomial.map i p)
        rw [Polynomial.map_map, hαι] }
  let g : EA →ₐ[Polynomial A] O :=
    { toRingHom := jA.comp (algebraMap EA (Localization.AtPrime QA))
      commutes' := by
        intro p
        change jA (algebraMap EA (Localization.AtPrime QA) (algebraMap (Polynomial A) EA p)) =
          (algebraMap (Polynomial T) O) (Polynomial.map i p)
        rw [← IsScalarTower.algebraMap_apply]
        exact congrArg (fun h => h p) hjA }
  let F : (Polynomial A' ⊗[Polynomial A] EA) →+* O :=
    (Algebra.TensorProduct.productMap f g).toRingHom
  have hF : ∀ a b, F (a ⊗ₜ b) = f a * g b := fun a b => by
    simp [F, Algebra.TensorProduct.productMap_apply_tmul]
  let Q' : Ideal (Polynomial A' ⊗[Polynomial A] EA) := (maximalIdeal O).comap F
  refine ⟨Polynomial A' ⊗[Polynomial A] EA, inferInstance, inferInstance, inferInstance, Q',
    Ideal.comap_isPrime _ _, ?_, ?_⟩
  · have hcomp : F.comp (algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom α) := by
      refine RingHom.ext fun p => ?_
      rw [RingHom.comp_apply, Algebra.TensorProduct.algebraMap_apply, hF, map_one, mul_one]
      rfl
    change ((maximalIdeal O).comap F).comap _ = _
    rw [Ideal.comap_comap, hcomp, ← Ideal.comap_comap, hO, comap_originIdeal]
  let h : EA →+* (Polynomial A' ⊗[Polynomial A] EA) :=
    (Algebra.TensorProduct.includeRight : EA →ₐ[Polynomial A] _).toRingHom
  have hh : ∀ x, F (h x) = jA (algebraMap EA (Localization.AtPrime QA) x) := fun x => by
    change F (1 ⊗ₜ x) = _
    rw [hF, map_one, one_mul]
    rfl
  have hy : QA.primeCompl ≤ Q'.primeCompl.comap h := by
    intro x hx
    have hu : IsUnit (jA (algebraMap EA (Localization.AtPrime QA) x)) :=
      (IsLocalization.map_units (Localization.AtPrime QA) (⟨x, hx⟩ : QA.primeCompl)).map jA
    change h x ∉ Q'
    intro hmem
    have hmem' : F (h x) ∈ maximalIdeal O := hmem
    rw [hh] at hmem'
    exact ((mem_maximalIdeal _).mp hmem') hu
  have hγ : ∀ y : Q'.primeCompl, IsUnit (F y) := by
    intro y
    by_contra hc
    exact y.2 ((mem_maximalIdeal _).mpr hc)
  let β : Localization.AtPrime QA →+* Localization.AtPrime Q' :=
    IsLocalization.map (M := QA.primeCompl) (S := Localization.AtPrime QA) (Localization.AtPrime Q')
      (g := h) (T := Q'.primeCompl) hy
  let γ : Localization.AtPrime Q' →+* O :=
    IsLocalization.lift (M := Q'.primeCompl) (S := Localization.AtPrime Q') (g := F) hγ
  refine ⟨β, γ, ?_, ?_, ?_⟩
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Polynomial A) EA (Localization.AtPrime QA),
      IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)
        (Localization.AtPrime Q')]
    change _ = β (algebraMap EA (Localization.AtPrime QA) _)
    rw [IsLocalization.map_eq]
    congr 1
    change algebraMap (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA) (Polynomial.C (ι a)) =
      (1 : Polynomial A') ⊗ₜ algebraMap (Polynomial A) EA (Polynomial.C a)
    rw [Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply',
      Algebra.TensorProduct.algebraMap_apply]
    congr 1
    change _ = Polynomial.map ι (Polynomial.C a)
    rw [Polynomial.map_C]
    rfl
  · refine IsLocalization.ringHom_ext QA.primeCompl (RingHom.ext fun x => ?_)
    simp only [RingHom.comp_apply]
    change γ (β (algebraMap EA (Localization.AtPrime QA) x)) = _
    rw [IsLocalization.map_eq, IsLocalization.lift_eq, hh]
  · refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply]
    rw [IsScalarTower.algebraMap_apply (Polynomial A') (Polynomial A' ⊗[Polynomial A] EA)
        (Localization.AtPrime Q'), IsLocalization.lift_eq, Algebra.TensorProduct.algebraMap_apply,
      hF, map_one, mul_one]
    change algebraMap (Polynomial T) O (Polynomial.map α (Polynomial.C a)) = _
    rw [Polynomial.map_C, IsScalarTower.algebraMap_apply T (Polynomial T) O]
    rfl

end GlobalTheory.LocalStage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormOneConstRatioOfCommonRatio
section
namespace GlobalTheory

theorem exists_norm_one_const_ratio_of_common_ratio :
    ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (I : Type) (S : Set V),
      IsOpen S → IsPreconnected S → ∀ (A B : I → V → ℂ) (t : V → ℂ), (∀ i, DifferentiableOn ℂ (A i) S) →
      (∀ i, DifferentiableOn ℂ (B i) S) → (∀ i, ∀ x ∈ S, A i x = t x * B i x) →
      (∀ i, ∀ x ∈ S, ‖A i x‖ = ‖B i x‖) → ∃ ε : ℂ, ‖ε‖ = 1 ∧ ∀ i, ∀ x ∈ S, A i x = ε * B i x := by
  intro V _ _ _ I S hS hc A B t hA hB ht hn
  by_cases h0 : ∀ i, ∀ x ∈ S, B i x = 0
  · refine ⟨1, norm_one, fun i x hx => ?_⟩
    rw [ht i x hx, h0 i x hx, mul_zero, mul_zero]
  · simp only [not_forall] at h0
    obtain ⟨i₀, x₀, hx₀, hne⟩ := h0
    obtain ⟨_, c, hcc⟩ := exists_eq_const_mul_of_forall_exists_norm_eq V Unit S hS hc ⟨x₀, hx₀⟩ (A i₀)
      (fun _ => B i₀) (hA i₀) (fun _ => hB i₀) (fun x hx => ⟨(), hn i₀ x hx⟩)
    refine ⟨c, ?_, fun i x hx => ?_⟩
    · have h1 := hn i₀ x₀ hx₀
      rw [hcc x₀ hx₀, norm_mul] at h1
      exact mul_right_cancel₀ (norm_ne_zero_iff.mpr hne) (by rw [one_mul]; exact h1)
    · have hd : DifferentiableOn ℂ (fun y => A i y - c * B i y) S := (hA i).sub ((hB i).const_mul c)
      have := ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.eq_zero_of_mul_eq_zero hS hc (hB i₀) hd (fun y hy => by
        have e1 := ht i y hy
        have e2 := ht i₀ y hy
        have e3 : A i₀ y = c * B i₀ y := hcc y hy
        show B i₀ y * (A i y - c * B i y) = 0
        rw [e1]
        linear_combination (B i y) * (e3 - e2)) hx₀ hne x hx
      exact sub_eq_zero.mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParameterFunctionOfFibreDerivZero
section
set_option autoImplicit false

open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace Filter Topology

namespace GlobalTheory.AnPer.Charts

theorem exists_glue_fn {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F)
    (hK : K.Rich) (a : ∀ k, Hol (K.W k)) (ha : ∀ k k' (e : K.le 0 k' k), sh e (a k) = a k') :
    ∃ G : Tot I g → ℂ, ∀ k, ∀ q ∈ K.W k, G q = (a k).fn q := by
  classical
  have key : ∀ k₁ k₂ q, q ∈ K.W k₁ → q ∈ K.W k₂ → (a k₁).fn q = (a k₂).fn q := by
    intro k₁ k₂ q h₁ h₂
    obtain ⟨k, hk, e₁, e₂⟩ := hK.2 0 k₁ k₂ q h₁ (by rw [F.shift_zero]; exact h₂)
    have r₁ := fn_sh e₁ (a k₁) hk
    have r₂ := fn_sh e₂ (a k₂) hk
    rw [ha, F.shift_zero] at r₁ r₂
    rw [← r₁, ← r₂]
  refine ⟨fun q ↦ if h : ∃ k, q ∈ K.W k then (a h.choose).fn q else 0, fun k q hq ↦ ?_⟩
  have h : ∃ k, q ∈ K.W k := ⟨k, hq⟩
  simp only [dif_pos h]
  exact key _ _ q h.choose_spec hq

theorem exists_cst_of_dw_eq_zero : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ}
    (K : Charts F), K.Rich → ∀ (a : ∀ k, Hol (K.W k)), (∀ k k' (e : K.le 0 k' k), sh e (a k) = a k') →
    (∀ k i, dw i (a k) = 0) → ∃ p : Hol F.V, ∀ k, a k = K.cst k p := by
  intro I _ g Λ _ F K hK a ha hd
  obtain ⟨G, hG⟩ := exists_glue_fn K hK a ha
  have ev : ∀ k, ∀ q ∈ K.W k, G =ᶠ[𝓝 q] (a k).fn := fun k q hq ↦ by
    filter_upwards [(K.W k).isOpen.mem_nhds hq] with r hr using hG k r hr
  have an : ∀ q : Tot I g, q.1 ∈ F.V → AnalyticAt ℂ G q := fun q hq ↦ by
    obtain ⟨k, hk⟩ := hK.1 q hq
    exact ((a k).analytic q hk).congr (ev k q hk).symm
  have d0 : ∀ q : Tot I g, q.1 ∈ F.V → ∀ i, fderiv ℂ G q ((0, Pi.single i 1) : Tot I g) = 0 := fun q hq i ↦ by
    obtain ⟨k, hk⟩ := hK.1 q hq
    rw [(ev k q hk).fderiv_eq, ← Hol.fn_der _ _ hk]
    change (dw i (a k)).fn q = 0
    rw [hd, ← Hol.ev_apply q hk, map_zero]
  have cs : ∀ z ∈ F.V, ∀ w, G (z, w) = G (z, 0) := fun z hz w ↦ by
    have hf : ∀ w : Fin g → ℂ, HasFDerivAt (fun w ↦ G (z, w))
        ((fderiv ℂ G (z, w)).comp (ContinuousLinearMap.inr ℂ (I → ℂ) (Fin g → ℂ))) w := fun w ↦
      (an (z, w) hz).differentiableAt.hasFDerivAt.comp w (hasFDerivAt_prodMk_right z w)
    refine is_const_of_fderiv_eq_zero (𝕜 := ℂ) (f := fun w ↦ G (z, w)) (fun w ↦ (hf w).differentiableAt)
      (fun w ↦ ?_) w 0
    rw [(hf w).fderiv]
    ext v
    have hv : ((0, v) : Tot I g) = ∑ i, v i • ((0, Pi.single i 1) : Tot I g) := by
      ext j
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
    change fderiv ℂ G (z, w) (0, v) = 0
    rw [hv, map_sum]
    exact Finset.sum_eq_zero fun i _ ↦ by rw [map_smul, d0 (z, w) hz i, smul_zero]
  refine ⟨Hol.mk (fun z ↦ G (z, 0)) fun z hz ↦
    AnalyticAt.comp (g := G) (f := fun z ↦ ((z, 0) : Tot I g)) (an (z, 0) hz)
      (analyticAt_id.prod analyticAt_const), fun k ↦ Hol.ext_fn fun q hq ↦ ?_⟩
  rw [fn_cst _ _ _ hq, ← hG k q hq]
  exact (cs q.1 (K.base k q hq) q.2).trans (Hol.fn_mk (fun z ↦ G (z, 0)) _ (K.base k q hq)).symm

end GlobalTheory.AnPer.Charts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPermOfSumMonomialEqStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perm_of_sum_monomial_eq' : ∀ (ι S : Type) [Fintype ι] [Fintype S] (x y : ι → S → ℂ), (∀ μ : S → ℕ, ∑ i, ∏ s, x i s ^ μ s = ∑ i, ∏ s, y i s ^ μ s) → ∃ ρ : Equiv.Perm ι, ∀ i, x i = y (ρ i) := by
  first | exact @GlobalTheory.QFam.exists_perm_of_sum_monomial_eq | exact GlobalTheory.QFam.exists_perm_of_sum_monomial_eq | (intros; apply GlobalTheory.QFam.exists_perm_of_sum_monomial_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolyPowMulEqOneStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_poly_pow_mul_eq_one' : ∀ (n l : ℕ) (B : Matrix (Fin n) (Fin n) ℂ), 0 < l → IsUnit B → ∃ p : ℂ[X], (aeval B p) ^ l * B = 1 := by
  first | (exact @GlobalTheory.exists_poly_pow_mul_eq_one) | (exact GlobalTheory.exists_poly_pow_mul_eq_one) | (intros; apply GlobalTheory.exists_poly_pow_mul_eq_one  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDEqZeroStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero' : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (K : Type) [Field K] [Algebra k K] (f : K), KaehlerDifferential.D k K f = 0 → ∃ h : K, h ^ p = f := by
  first | exact @GlobalTheory.exists_pow_eq_of_kaehler_D_eq_zero | exact GlobalTheory.exists_pow_eq_of_kaehler_D_eq_zero | (intros; apply GlobalTheory.exists_pow_eq_of_kaehler_D_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulMemOfForallExistsStatement
section
open IsLocalRing TensorProduct Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_mem_of_forall_exists' : ∀ (S : Type) [CommRing S] (I : Ideal S) (M : Type) [AddCommGroup M] [Module S M] [Module.Finite S M] (N : Submodule S M), (∀ y : M, ∃ k : ℕ, ∀ a ∈ I ^ k, a • y ∈ N) → ∃ k : ℕ, ∀ a ∈ I ^ k, ∀ y : M, a • y ∈ N := by
  first | exact @GlobalTheory.Submodule.exists_pow_smul_mem_of_forall_exists | exact GlobalTheory.Submodule.exists_pow_smul_mem_of_forall_exists | (intros; apply GlobalTheory.Submodule.exists_pow_smul_mem_of_forall_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingHomOfJointEigenvalueStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_hom_of_joint_eigenvalue : ∀ (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ), v.Integers O → ∀ (ρ : Λ →+* Matrix (Fin h) (Fin h) O) (χ : Λ → C), (⨅ a : Λ, Module.End.eigenspace (Matrix.toLin' ((ρ a).map (algebraMap O C))) (χ a)) ≠ ⊥ → ∃ σ : Λ →+* O, ∀ a, algebraMap O C (σ a) = χ a := by
  first | exact @GlobalTheory.jointEigen_ringHom_toIntegers | exact GlobalTheory.jointEigen_ringHom_toIntegers | (intros; apply GlobalTheory.jointEigen_ringHom_toIntegers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzCexpNegFormStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_schwartz_eq_cexp_neg_form : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (Q : V →L[ℝ] V →L[ℝ] ℂ) (c : ℝ),
    0 < c → (∀ x, c * ‖x‖ ^ 2 ≤ (Q x x).re) →
    ∃ g : SchwartzMap V ℂ, (∀ x, g x = Complex.exp (-(Q x x))) ∧ ∀ x p, fderiv ℝ (⇑g) x p = -(Q x p + Q p x) * g x := by
  first | exact @GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form | exact GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form | (intros; apply GlobalTheory.GaussComplexForm.exists_schwartz_cexp_neg_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSecondOrderNbhdCommutingDerivationsStatement
section
open TopologicalSpace CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_secondOrderNbhd_commuting_derivations : ∀ (O : Type) [CommRing O] [Algebra ℂ O] (D₁ D₂ : Derivation ℂ O O), (∀ x, D₁ (D₂ x) = D₂ (D₁ x)) → ∃ (C : Type) (_ : CommRing C) (J : Ideal C) (φ₀ φ₁ φ₂ φ₃ : O →+* C) (e₁ e₂ : C), IsNilpotent J ∧ e₁ ∈ J ∧ e₂ ∈ J ∧ e₁ * e₁ = 0 ∧ e₂ * e₂ = 0 ∧ (∀ x, φ₁ x = φ₀ x + φ₀ (D₁ x) * e₁) ∧ (∀ x, φ₂ x = φ₀ x + φ₀ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₁ x + φ₁ (D₂ x) * e₂) ∧ (∀ x, φ₃ x = φ₂ x + φ₂ (D₁ x) * e₁) ∧ ∀ x, φ₀ x * e₁ * e₂ = 0 → x = 0 := by
  first | exact @GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd | exact GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd | (intros; apply GlobalTheory.SecondOrderNbhd.exists_second_order_nbhd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparableAnnihilatingPolyStatement
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separable_annihilating_poly : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [CharZero C] (φ : ℤ_[p] →+* C) (Λ : Type) [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (a : Λ), ∃ f : Polynomial ℤ_[p], Polynomial.aeval a f = 0 ∧ (f.map φ).Separable := by
  first | exact @GlobalTheory.exists_poly_aeval_eq_zero_map_separable | exact GlobalTheory.exists_poly_aeval_eq_zero_map_separable | (intros; apply GlobalTheory.exists_poly_aeval_eq_zero_map_separable <;> assumption)
end

