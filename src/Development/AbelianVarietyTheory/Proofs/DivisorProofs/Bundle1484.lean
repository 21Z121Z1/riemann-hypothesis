import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1459
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0017
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1371
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DformRelEquivalence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1175
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RapidDecaySmallestRatioAbsorbsHeightAndCharacter
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspQuot GlobalTheory.AutGrowth MeasureTheory GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction

namespace GlobalTheory.RapidDecayReal

theorem height_le (a : ℕ) (N : ℕ) (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (K : ℝ)
    (hb : ∀ i, r i ≤ K ∧ (r i)⁻¹ ≤ K) :
    (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ (1 + 2 * a * K) ^ N := by
  have h0 : 0 ≤ 1 + ∑ i, r i + ∑ i, (r i)⁻¹ := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hr i).le)
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (inv_pos.2 (hr i)).le)
    linarith
  apply pow_le_pow_left₀ h0
  have h1 : ∑ i, r i ≤ ∑ _i : Fin a, K := Finset.sum_le_sum (fun i _ => (hb i).1)
  have h2 : ∑ i, (r i)⁻¹ ≤ ∑ _i : Fin a, K := Finset.sum_le_sum (fun i _ => (hb i).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1 h2
  linarith

theorem char_ge (a : ℕ) (lam : Fin a → ℝ) (L : ℕ) (hL : ∑ i, |lam i| ≤ L) (r : Fin a → ℝ)
    (hr : ∀ i, 0 < r i) (K : ℝ) (hK : 1 ≤ K) (hb : ∀ i, r i ≤ K ∧ (r i)⁻¹ ≤ K) :
    (K ^ L)⁻¹ ≤ ∏ i, r i ^ lam i := by
  have hK0 : 0 < K := by linarith
  have hi : ∀ i, K ^ (-|lam i|) ≤ r i ^ lam i := by
    intro i
    rcases le_or_gt 0 (lam i) with h | h
    · rw [abs_of_nonneg h, Real.rpow_neg hK0.le, ← Real.inv_rpow hK0.le]
      apply Real.rpow_le_rpow (inv_nonneg.2 hK0.le) _ h
      rw [inv_le_comm₀ hK0 (hr i)]; exact (hb i).2
    · rw [abs_of_neg h, neg_neg]
      have e1 : K ^ lam i = (K⁻¹) ^ (-lam i) := by
        rw [Real.inv_rpow hK0.le, Real.rpow_neg hK0.le, inv_inv]
      have e2 : r i ^ lam i = ((r i)⁻¹) ^ (-lam i) := by
        rw [Real.inv_rpow (hr i).le, Real.rpow_neg (hr i).le, inv_inv]
      rw [e1, e2]
      apply Real.rpow_le_rpow (inv_nonneg.2 hK0.le) _ (by linarith)
      exact inv_anti₀ (hr i) (hb i).1
  calc (K ^ L)⁻¹ = K ^ (-(L : ℝ)) := by rw [Real.rpow_neg hK0.le, Real.rpow_natCast]
    _ ≤ K ^ (∑ i, -|lam i|) := by
        apply Real.rpow_le_rpow_of_exponent_le hK
        rw [Finset.sum_neg_distrib]; linarith
    _ = ∏ i, K ^ (-|lam i|) := Real.rpow_sum_of_pos hK0 _ _
    _ ≤ ∏ i, r i ^ lam i :=
        Finset.prod_le_prod (fun i _ => Real.rpow_nonneg hK0.le _) (fun i _ => hi i)

theorem key (a : ℕ) (lam : Fin a → ℝ) (L N : ℕ) (hL : ∑ i, |lam i| ≤ L) (C0 : ℝ) (hC0 : 1 ≤ C0)
    (r : Fin a → ℝ) (hr : ∀ i, 0 < r i) (ρ : ℝ) (hρ : 1 ≤ ρ)
    (hb : ∀ i, r i ≤ C0 * ρ ^ a ∧ (r i)⁻¹ ≤ C0 * ρ ^ a) :
    (ρ ^ (a * N + a * L))⁻¹ * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤
      ((1 + 2 * a * C0) ^ N * C0 ^ L) * ∏ i, r i ^ lam i := by
  set P := ρ ^ a with hPdef
  have hP : 1 ≤ P := one_le_pow₀ hρ
  have hC00 : 0 < C0 := by linarith
  have hP0 : 0 < P := by linarith
  have hK : 1 ≤ C0 * P := by nlinarith
  have h1 := height_le a N r hr (C0 * P) hb
  have h2 := char_ge a lam L hL r hr (C0 * P) hK hb
  have h3 : (1 + 2 * (a : ℝ) * (C0 * P)) ^ N ≤ ((1 + 2 * a * C0) * P) ^ N := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith
  have hm : ρ ^ (a * N + a * L) = P ^ N * P ^ L := by
    rw [hPdef, ← pow_mul, ← pow_mul, ← pow_add]
  rw [hm]
  calc (P ^ N * P ^ L)⁻¹ * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N
      ≤ (P ^ N * P ^ L)⁻¹ * ((1 + 2 * a * C0) * P) ^ N :=
        mul_le_mul_of_nonneg_left (h1.trans h3) (by positivity)
    _ = ((1 + 2 * a * C0) ^ N * C0 ^ L) * ((C0 * P) ^ L)⁻¹ := by
        rw [mul_pow, mul_pow]
        field_simp
    _ ≤ ((1 + 2 * a * C0) ^ N * C0 ^ L) * ∏ i, r i ^ lam i :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

end GlobalTheory.RapidDecayReal

open GlobalTheory.RapidDecayReal in

theorem GlobalTheory.rapidDecay_real : ∀ (a : ℕ) (t : ℝ), 0 < t → ∀ (lam : Fin a → ℝ) (N : ℕ), ∃ (m : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) → ∏ i, r i = 1 → (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i ∨ ∃ i j : Fin a, (j : ℕ) = i + 1 ∧ (r j / r i) ^ m * (1 + ∑ i, r i + ∑ i, (r i)⁻¹) ^ N ≤ C * ∏ i, r i ^ lam i := by
  intro a t ht lam N
  obtain ⟨C0, hC0, hC⟩ := GlobalTheory.T.coneCoordinate_le_pow_of_prod_eq_one a t ht
  set L := ⌈∑ i, |lam i|⌉₊ with hLdef
  have hL : ∑ i, |lam i| ≤ L := Nat.le_ceil _
  refine ⟨a * N + a * L, (1 + 2 * a * C0) ^ N * C0 ^ L, by positivity, ?_⟩
  intro r hr hcone hprod
  by_cases hall : ∀ i j : Fin a, (j : ℕ) = i + 1 → r i ≤ r j
  · left
    have hb := hC r 1 hr hcone hprod le_rfl (fun i j hij => by rw [one_mul]; exact hall i j hij)
    have := key a lam L N hL C0 hC0 r hr 1 le_rfl hb
    simpa using this
  · right
    push_neg at hall
    obtain ⟨i, j, hij, hlt⟩ := hall
    set S := (Finset.univ : Finset (Fin a × Fin a)).filter (fun p => (p.2 : ℕ) = p.1 + 1) with hS
    have hne : S.Nonempty := ⟨(i, j), by simp [hS, hij]⟩
    obtain ⟨p, hp, hmax⟩ := Finset.exists_max_image S (fun p => r p.1 / r p.2) hne
    have hpadj : (p.2 : ℕ) = p.1 + 1 := by simpa [hS] using hp
    have hij' : r i / r j ≤ r p.1 / r p.2 := hmax (i, j) (by simp [hS, hij])
    have hρ : 1 ≤ r p.1 / r p.2 := by
      have : 1 < r i / r j := by rw [one_lt_div (hr j)]; exact hlt
      linarith
    have hadj : ∀ i' j' : Fin a, (j' : ℕ) = i' + 1 → r i' ≤ (r p.1 / r p.2) * r j' := by
      intro i' j' h'
      have := hmax (i', j') (by simp [hS, h'])
      rwa [div_le_iff₀ (hr j')] at this
    have hb := hC r _ hr hcone hprod hρ hadj
    refine ⟨p.1, p.2, hpadj, ?_⟩
    have := key a lam L N hL C0 hC0 r hr _ hρ hb
    rw [← inv_div (r p.1) (r p.2), inv_pow]
    exact this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalGLBoundedSizeCompactFinitePolynomialCoun
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

namespace GlobalTheory

theorem ratGL_bounded_count : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), ∃ m : ℕ, ∀ Kf : Set (GL (Fin a) (Af E)), IsCompact Kf → ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 1 ≤ T → {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.Finite ∧ ({γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}.ncard : ℝ) ≤ C * T ^ m := by
  intro E _ _ _ a
  obtain ⟨m, hm⟩ := GlobalTheory.T.rational_boundedInfinite_compactFinite_polyCount E
  refine ⟨m * (a * a), fun Kf hKf => ?_⟩
  let Kf' : Set (Af E) := ⋃ i : Fin a, ⋃ j : Fin a, (fun g : GL (Fin a) (Af E) => g.val i j) '' Kf
  have hc : IsCompact Kf' := by
    refine isCompact_iUnion fun i => isCompact_iUnion fun j => hKf.image ?_
    exact (Units.continuous_val (M := Matrix (Fin a) (Fin a) (Af E))).matrix_elem i j
  obtain ⟨C, hC0, hC⟩ := hm Kf' hc
  refine ⟨C ^ (a * a), pow_nonneg hC0 _, fun T hT => ?_⟩
  obtain ⟨hNf, hNc⟩ := hC T hT
  let N : Set E := {ξ : E | ‖pInf E (algebraMap E (Ad E) ξ)‖ ≤ T ∧ pFin E (algebraMap E (Ad E) ξ) ∈ Kf'}
  let S : Set (GL (Fin a) E) := {γ : GL (Fin a) E | ‖toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val‖ ≤ T ∧ Matrix.GeneralLinearGroup.map (pFin E) (ratGL E a γ) ∈ Kf}
  change S.Finite ∧ (S.ncard : ℝ) ≤ C ^ (a * a) * T ^ (m * (a * a))
  have hsub : ∀ γ ∈ S, ∀ i j, γ.val i j ∈ N := by
    intro γ hγ i j
    obtain ⟨h1, h2⟩ := hγ
    refine ⟨?_, ?_⟩
    · have he : pInf E (algebraMap E (Ad E) (γ.val i j)) = (toL (Matrix.GeneralLinearGroup.map (pInf E) (ratGL E a γ)).val) i j := rfl
      rw [he]
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i)).trans h1
    · exact Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, ⟨_, h2, rfl⟩⟩⟩
  classical
  let F : Finset E := hNf.toFinset
  let P : Finset (Fin a → Fin a → E) := Fintype.piFinset fun _ => Fintype.piFinset fun _ => F
  let f : GL (Fin a) E → (Fin a → Fin a → E) := fun γ => γ.val
  have hf : Function.Injective f := fun x y h => Units.ext h
  have himg : f '' S ⊆ (P : Set (Fin a → Fin a → E)) := by
    rintro _ ⟨γ, hγ, rfl⟩
    simp only [P, F, Finset.mem_coe, Fintype.mem_piFinset, Set.Finite.mem_toFinset]
    exact fun i j => hsub γ hγ i j
  have hSfin : S.Finite := Set.Finite.of_finite_image ((P.finite_toSet).subset himg) hf.injOn
  refine ⟨hSfin, ?_⟩
  have hcardP : P.card = (F.card ^ a) ^ a := by
    simp [P, Fintype.card_piFinset, Finset.prod_const]
  have hS : S.ncard ≤ (F.card ^ a) ^ a := by
    rw [← Set.ncard_image_of_injective S hf, ← hcardP, ← Set.ncard_coe_finset]
    exact Set.ncard_le_ncard himg P.finite_toSet
  have hF : (F.card : ℝ) ≤ C * T ^ m := by
    rw [← Set.ncard_eq_toFinset_card N hNf]; exact hNc
  calc (S.ncard : ℝ) ≤ ((F.card ^ a) ^ a : ℕ) := by exact_mod_cast hS
    _ = (F.card : ℝ) ^ (a * a) := by push_cast; rw [← pow_mul]
    _ ≤ (C * T ^ m) ^ (a * a) := pow_le_pow_left₀ (Nat.cast_nonneg _) hF _
    _ = C ^ (a * a) * T ^ (m * (a * a)) := by rw [mul_pow, ← pow_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalLagrangianSubspaceExists
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.MixedLagr

theorem rat_first_zero_dim : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W), Module.finrank F E = 2 →
    ∀ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f → (∀ x, hat (f x) = M.co.e (incM F x)) →
      ∃ K : Submodule F (Matrix (Fin n) (Fin d) E), Module.finrank F K = n * d ∧ ∀ z ∈ K, (M.co.e (incM F z)).1 = 0 := by
  intro F E _ _ _ _ _ σ n d X W M hE f hf hhat
  haveI : Module.Finite F E := Module.finite_of_finrank_pos (by omega)
  have hdom : Module.finrank F (Matrix (Fin n) (Fin d) E) = n * d * 2 := by
    rw [Module.finrank_matrix, hE]; simp
  have hcod : Module.finrank F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) = n * d * 2 := by
    rw [Module.finrank_prod, Module.finrank_fintype_fun_eq_card]; simp; ring
  have hsurj : Function.Surjective f :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (hdom.trans hcod.symm)).mp hf
  set g := (LinearMap.fst F (Fin n × Fin d → F) (Fin n × Fin d → F)).comp f with hg
  have gsurj : Function.Surjective g := by
    intro y
    obtain ⟨x, hx⟩ := hsurj (y, 0)
    exact ⟨x, by simp [hg, hx]⟩
  refine ⟨LinearMap.ker g, ?_, ?_⟩
  · have h1 := LinearMap.finrank_range_add_finrank_ker g
    rw [LinearMap.range_eq_top.mpr gsurj, finrank_top, Module.finrank_fintype_fun_eq_card, hdom] at h1
    simp at h1
    have : Fintype.card (Fin n × Fin d) = n * d := by simp
    omega
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    rw [← hhat z]
    have hz' : (f z).1 = 0 := by simpa [hg] using hz
    funext i
    simp [hat, hz']

end GlobalTheory.MixedLagr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalModelCoordinates
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.MixedLagr
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

theorem ratCoord_linear_injective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W),
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
      M.co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
    ∃ f : Matrix (Fin n) (Fin d) E →ₗ[F] (Fin n × Fin d → F) × (Fin n × Fin d → F),
      Function.Injective f ∧ ∀ x, hat (f x) = M.co.e (incM F x) := by
  intro F E _ _ _ _ _ σ n d X W M h
  choose y z hyz using h
  have hA : Function.Injective (algebraMap F (AF F)) := AdeleRing.algebraMap_injective (𝓞 F) F
  have hg : ∀ x, hat ((y x, z x) : (Fin n × Fin d → F) × (Fin n × Fin d → F)) = M.co.e (incM F x) :=
    fun x => (hyz x).symm
  have hinj : Function.Injective (hat : (Fin n × Fin d → F) × (Fin n × Fin d → F) → _) := by
    intro a b hab
    simp only [hat, Prod.mk.injEq] at hab
    exact Prod.ext (funext fun i => hA (congrFun hab.1 i)) (funext fun i => hA (congrFun hab.2 i))
  have hadd : ∀ x x' : Matrix (Fin n) (Fin d) E, incM F (x + x') = incM F x + incM F x' := by
    intro x x'
    ext i j
    simp [incM, Matrix.map_apply, map_add]
  have hsmul : ∀ (c : F) (x : Matrix (Fin n) (Fin d) E), incM F (c • x) = algebraMap F (AF F) c • incM F x := by
    intro c x
    ext i j
    simp only [incM, Matrix.map_apply, Matrix.smul_apply]
    show (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) (c • x i j) =
      algebraMap F (AF F) c • (Algebra.TensorProduct.includeRight : E →ₐ[F] AE F E) (x i j)
    rw [map_smul, algebraMap_smul]
  have hI : Function.Injective (incM F : Matrix (Fin n) (Fin d) E → Matrix (Fin n) (Fin d) (AE F E)) :=
    Matrix.map_injective (Algebra.TensorProduct.includeRight_injective hA)
  refine ⟨{ toFun := fun x => (y x, z x), map_add' := ?_, map_smul' := ?_ }, ?_, hg⟩
  · intro x x'
    apply hinj
    rw [hat_add, hg, hg, hg, hadd, map_add]
  · intro c x
    apply hinj
    rw [RingHom.id_apply, hat_smul, hg, hg, hsmul, LinearEquiv.map_smul]
  · intro x x' hx
    apply hI
    apply M.co.e.injective
    rw [← hg, ← hg]
    exact congrArg hat hx

end GlobalTheory.MixedLagr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalUnitaryIffGroupPoints
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability

namespace GlobalTheory.RatCorr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem inclR_injective : Function.Injective (inclR (F := F) (E := E) (AF F)) :=
  haveI : Nontrivial (AF F) := inferInstanceAs (Nontrivial (Ainf F × Af F))
  Algebra.TensorProduct.includeRight_injective (algebraMap F (AF F)).injective

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) : sigR (AF F) σ (inclR (AF F) x) = inclR (AF F) (σ x) := by
  simp [sigR, inclR]

theorem ratU_iff (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (d : ℕ) (J : Matrix (Fin d) (Fin d) E) (c : E) (hc : c ≠ 0)
    (g : UA σ J) : g ∈ ratU σ J ↔ toGAd hσ J hc g ∈ GlobalTheory.AdelicU.ratPts σ (c • J.map σ) := by
  have hg : (g.1 : GL (Fin d) (AE F E)) ∈ HR (AF F) σ (c • J.map σ) := (toGAd hσ J hc g).2
  change g.1 ∈ (Matrix.GeneralLinearGroup.map (n := Fin d) (inclR (F := F) (E := E) (AF F))).range ↔
    g.1 ∈ (Formalism.UG.UJ (σ : E →+* E) (c • J.map σ)).map (Formalism.UG.bc (inclR (AF F)))
  constructor
  · rintro ⟨g₀, hg₀⟩
    refine ⟨g₀, ?_, hg₀⟩
    have h1 : Formalism.UG.cT (sigR (AF F) σ) ((g.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) *
        JR (AF F) (c • J.map σ) * ((g.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) =
        JR (AF F) (c • J.map σ) := hg
    have hm : ((g.1 : GL (Fin d) (AE F E)) : Matrix (Fin d) (Fin d) (AE F E)) =
        (g₀ : Matrix (Fin d) (Fin d) E).map (inclR (AF F)) := by
      rw [← hg₀]; rfl
    rw [hm] at h1
    change Formalism.UG.cT (σ : E →+* E) (g₀ : Matrix (Fin d) (Fin d) E) * (c • J.map σ) * (g₀ : Matrix (Fin d) (Fin d) E) = c • J.map σ
    apply Matrix.map_injective (inclR_injective (F := F) (E := E))
    dsimp only
    have e1 : (Formalism.UG.cT (σ : E →+* E) (g₀ : Matrix (Fin d) (Fin d) E)).map (inclR (F := F) (AF F)) =
        Formalism.UG.cT (sigR (AF F) σ) ((g₀ : Matrix (Fin d) (Fin d) E).map (inclR (AF F))) := by
      ext i j
      simp [Formalism.UG.cT, sigR_inclR]
    have e2 : (c • J.map σ).map (inclR (F := F) (AF F)) = JR (AF F) (c • J.map σ) := rfl
    rw [Matrix.map_mul, Matrix.map_mul, e1, e2]
    exact h1
  · rintro ⟨g₀, -, hg₀⟩
    exact ⟨g₀, hg₀⟩

theorem ratU_iff_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hσ : ∀ x, σ (σ x) = x) (d : ℕ) (J : Matrix (Fin d) (Fin d) E) (c : E) (hc : c ≠ 0),
      ∀ g : UA σ J, g ∈ ratU σ J ↔ toGAd hσ J hc g ∈ GlobalTheory.AdelicU.ratPts σ (c • J.map σ) :=
  fun _ _ _ _ _ _ _ σ hσ d J c hc g => ratU_iff σ hσ d J c hc g

end GlobalTheory.RatCorr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RdIndepOfLawsM
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

set_option maxHeartbeats 1000000 in

theorem rdIndep_of_lawsM : ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ →
    RdIndep (T.Q.Xo j) T.Q.c (T.U j) σ := by
  intro D T h j hj σ hσ
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.rdIndep_laws T.Q.c GlobalTheory.abelianSchemeLaws_all.2.secBaseChangeAny GlobalTheory.abelianSchemeLaws_all.2.secTwist (T.U j) σ (h.evalWD j hj)
    (GlobalTheory.Frames.allTest_of_secBaseChange GlobalTheory.abelianSchemeLaws_all.1.secBaseChange _ _ _ _ (T.Q.Xo j) T.Q.c)
    (h.unf j hj σ hσ)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealLineContinuous
section
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

namespace GlobalTheory.RealLineCont

theorem continuous_of_isRealLine : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (γ : ℝ → GAd σ J), IsRealLine σ J γ → Continuous γ := by
  intro F E _ _ _ _ _ σ h n J γ ⟨w, τ, Z, _, hy⟩
  choose y hγ hy using hy
  have hc : Continuous y := by
    rw [(GlobalTheory.Orb.isEmbedding_archMat J h τ).continuous_iff]
    have e : (GlobalTheory.Orb.matCoord (GlobalTheory.Orb.archMat σ J τ) ∘ y) = fun t i j => NormedSpace.exp (t • Z) i j := by
      funext t i j; simp only [Function.comp_apply, GlobalTheory.Orb.matCoord, hy t]
    rw [e]
    have hexp : Continuous fun t : ℝ => NormedSpace.exp (t • Z) := by
      letI : NormedRing (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedRing
      letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) ℂ) := Matrix.linftyOpNormedAlgebra
      letI : NormedAlgebra ℚ (Matrix (Fin n) (Fin n) ℂ) := NormedAlgebra.restrictScalars ℚ ℂ _
      exact NormedSpace.exp_continuous.comp (continuous_id.smul continuous_const)
    exact continuous_pi fun i => continuous_pi fun j => (continuous_apply j).comp ((continuous_apply i).comp hexp)
  have : γ = fun t => embArch σ J w (y t) := funext hγ
  rw [this]
  exact (continuous_embArch σ J w).comp hc

end GlobalTheory.RealLineCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPlaceSplittingConstantEqDoubledSpaceStatement
section
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPlace_splittingConstant_eq_doubledSpace : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (Φd : Tens F P Q (R + S) (S + R) →ₗ[ℂ] SInf F (κ ⊕ κ))
    (om : UG (cA σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (omd : UG (cA σ) (dbl JB) →* Module.End ℂ ((κ ⊕ κ → AF F) → ℂ))
    (c cd : InfinitePlace F → ℂ),
    IsCMExt F E σ → IsStd ψ → IsFockMap ψ τ d A C Φ →
    (∀ (g : UG (cA σ) JB) (gd : UG (cA σ) (dbl JB)),
      ((gd : GL (β ⊕ β) (AE F E)) : Matrix (β ⊕ β) (β ⊕ β) (AE F E)) =
        Matrix.fromBlocks ((g : GL β (AE F E)) : Matrix β β (AE F E)) 0 0 1 →
      ∀ φ₁ ∈ (adeleClass F).sp κ, ∀ φ₂ ∈ (adeleClass F).sp κ, omd gd (boxFun φ₁ φ₂) = boxFun (om g φ₁) φ₂) →
    ActsBy τ C om Φ (fockAct2 P Q R S) c →
    ActsBy τ (fun w => dblM (C w)) omd Φd (fockAct2 P Q (R + S) (S + R)) cd →
    (∃ z : ℂ, z ≠ 0 ∧ ∀ x : κ ⊕ κ → mixedEmbedding.mixedSpace F,
      Φd (PiTensorProduct.tprod ℂ fun _ => 1) x = z * Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inl) *
        star (Φ (PiTensorProduct.tprod ℂ fun _ => 1) (x ∘ Sum.inr))) →
    0 < R + S → ∀ w, c w = cd w := by
  first | exact @GlobalTheory.RealLift.Compare.constant_eq_dbl | exact GlobalTheory.RealLift.Compare.constant_eq_dbl | (intros; apply GlobalTheory.RealLift.Compare.constant_eq_dbl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexPrincipalCongruenceNeZero
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

theorem GlobalTheory.LKDef.Regroup.regroup :
    ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (wt : Polynomial G.F → ℂ)
    (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      GlobalTheory.LKDef.dSumIrr G wt L.K.toSubgroup f 1 K' f' =
        ∑ᶠ q : GlobalTheory.LKDef.DFCls G, ∑ᶠ c : ConjClasses (GlobalTheory.LKCx.grp G (Quot.out q).β),
          if GlobalTheory.LKDef.RegIrr G (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C) then
            wt (minpoly G.F (((Quotient.out c : GlobalTheory.LKCx.grp G (Quot.out q).β).1.1 : G.Cˣ) : G.C)) *
              centSum (GlobalTheory.LKCx.toAfF G (Quot.out q).β (Quot.out q).trivAf.choose (Quot.out q).trivAf.choose_spec.choose
                  (Quot.out q).trivAf.choose_spec.choose_spec)
                (GlobalTheory.LKCx.toP1 G (Quot.out q).β) (MonoidHom.id (Gr G 1)) L.K.toSubgroup K' 1 f f' (Quotient.out c)
          else 0 :=
  GlobalTheory.LKDef.Regroup.regroup_main GlobalTheory.LKDef.DFormPos.sim_pos GlobalTheory.T.bi_invariant_conjugacy_classes_finite GlobalTheory.T.definitePair_term_eq_centraliser_orbit_sum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledCosetIndicatorSchwartz
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct Classical

namespace GlobalTheory.EvAdm

theorem isCompact_scaledInt_of_ne_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Finite κ] {a : F} (ha : a ≠ 0) :
    IsCompact (scaledInt F κ a : Set (κ → FiniteAdeleRing (𝓞 F) F)) := by
  have hO : IsCompact {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F} := by
    haveI : ∀ v : HeightOneSpectrum (𝓞 F), CompactSpace (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
      fun v => isCompact_iff_compactSpace.1 (ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isCompact_integers v)
    have h := isCompact_range (RestrictedProduct.isEmbedding_structureMap
      (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
      (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
      (𝓕 := Filter.cofinite)).continuous
    rw [RestrictedProduct.range_structureMap] at h
    exact h
  let g : (κ → FiniteAdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F) :=
    fun z i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a * z i
  have hg : Continuous g := continuous_pi fun i => continuous_const.mul (continuous_apply i)
  have hP : IsCompact (Set.pi Set.univ fun _ : κ =>
      {x : FiniteAdeleRing (𝓞 F) F | ∀ v, x v ∈ v.adicCompletionIntegers F}) := isCompact_univ_pi fun _ => hO
  refine (hP.image hg).of_isClosed_subset ((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)) ?_
  intro z hz
  refine ⟨fun i => algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i, fun i _ v => ?_, ?_⟩
  · have h : (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v =
        (algebraMap F (v.adicCompletion F) a)⁻¹ * (z i) v := by
      have h1 := map_mul (evalV F v) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹) (z i)
      rw [AlgHom.commutes, map_inv₀ (algebraMap F (v.adicCompletion F))] at h1
      exact h1
    show (algebraMap F (FiniteAdeleRing (𝓞 F) F) a⁻¹ * z i) v ∈ _
    rw [h]
    exact hz i v
  · funext i
    simp only [g]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ ha, map_one, one_mul]

theorem indicator_coset_scaledInt_mem_SB : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (a : F), a ≠ 0 →
    ∀ r : κ → FiniteAdeleRing (𝓞 F) F,
      {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a}.indicator (fun _ => (1 : ℂ)) ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  intro F _ _ κ _ a ha r
  have hf : Continuous fun y : κ → FiniteAdeleRing (𝓞 F) F => y - r := continuous_id.sub continuous_const
  have hcl : IsClopen {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    ⟨((scaledInt F κ a).isClosed_of_isOpen (isOpen_scaledInt a)).preimage hf, (isOpen_scaledInt a).preimage hf⟩
  have hco : IsCompact {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} :=
    (Homeomorph.subRight r).isCompact_preimage.2 (isCompact_scaledInt_of_ne_zero (κ := κ) ha)
  generalize {y | y - r ∈ GlobalTheory.EvAdm.scaledInt F κ a} = S at hcl hco ⊢
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · filter_upwards [hcl.isOpen.mem_nhds hx] with y hy
      rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]
    · filter_upwards [hcl.isClosed.isOpen_compl.mem_nhds hx] with y hy
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]
  · exact HasCompactSupport.intro' hco hcl.isClosed (fun y hy => Set.indicator_of_notMem hy _)

end GlobalTheory.EvAdm
end

