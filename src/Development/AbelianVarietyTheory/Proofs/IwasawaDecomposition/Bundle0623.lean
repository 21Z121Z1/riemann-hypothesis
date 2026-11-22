import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishesToPullChartIffOfFlat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsLevel
import ReciprocityTheory.Automorphisms.SplitCoeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoTame
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacterDetLevelEqLocalTameProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0605
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0563
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusPointsSubsetHolPeriodicOneParamSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0606
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SInfMulNormPlk
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.GradedNorm

open Matrix

theorem det_mem {C : Type} [Field C] (W : ValuationSubring C) {k : ℕ} (A : Matrix (Fin k) (Fin k) C)
    (h : ∀ i j, A i j ∈ W) : A.det ∈ W := by
  rw [Matrix.det_apply']
  exact W.toSubring.sum_mem fun σ _ =>
    W.toSubring.mul_mem (intCast_mem W.toSubring _) (W.toSubring.prod_mem fun i _ => h _ _)

theorem plk_eq {C : Type} [Field C] {M n : ℕ} (c : Fin n → Fin (M + 1) → C)
    (u : Matrix (Fin (M + 1)) (Fin n) C) (b : Matrix (Fin n) (Fin n) C) (hb : b.BlockTriangular id)
    (hc : (Matrix.of c)ᵀ = u * b) {k : ℕ} (hk : k ≤ n) (q : Fin (plN M k + 1)) :
    plk c (Fin.castLE hk) q =
      (u.submatrix (plE M k q) (Fin.castLE hk)).det * ∏ l : Fin k, b (Fin.castLE hk l) (Fin.castLE hk l) := by
  have h1 : (Matrix.of fun l l' => c (Fin.castLE hk l) (plE M k q l'))ᵀ =
      u.submatrix (plE M k q) (Fin.castLE hk) * b.submatrix (Fin.castLE hk) (Fin.castLE hk) := by
    ext l' l
    have h2 := congrFun (congrFun hc (plE M k q l')) (Fin.castLE hk l)
    simp only [transpose_apply, of_apply] at h2 ⊢
    rw [h2, mul_apply, mul_apply]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hk) (Fin.castLE_injective hk) _ _ ?_ (fun _ => rfl)
    intro j hj
    have : b j (Fin.castLE hk l) = 0 := by
      apply hb
      by_contra hlt
      have hle : (j : ℕ) ≤ l := Fin.le_def.mp (not_lt.mp hlt)
      exact hj ⟨⟨j, lt_of_le_of_lt hle l.2⟩, rfl⟩
    rw [this, mul_zero]
  have h3 : (b.submatrix (Fin.castLE hk) (Fin.castLE hk)).BlockTriangular id := fun i j hij => hb hij
  unfold plk
  rw [← det_transpose, h1, det_mul, Matrix.det_of_isUpperTriangular h3]
  rfl

theorem norm_plk_max {C : Type} [NontriviallyNormedField C] (W : ValuationSubring C)
    (hW : ∀ x, x ∈ W ↔ ‖x‖ ≤ 1) {M n : ℕ} (c : Fin n → Fin (M + 1) → C) (ι : Fin n → Fin (M + 1))
    (u : Matrix (Fin (M + 1)) (Fin n) C) (b : Matrix (Fin n) (Fin n) C) (huW : ∀ i j, u i j ∈ W)
    (hu0 : ∀ i j : Fin n, i < j → u (ι i) j = 0) (hu1 : ∀ i, u (ι i) i = 1) (hb : b.BlockTriangular id)
    (hc : (Matrix.of c)ᵀ = u * b) {k : ℕ} (hk : k ≤ n) (q₀ : Fin (plN M k + 1))
    (hq : ∀ q, ‖plk c (Fin.castLE hk) q‖ ≤ ‖plk c (Fin.castLE hk) q₀‖) :
    ‖plk c (Fin.castLE hk) q₀‖ = ∏ l : Fin k, ‖b (Fin.castLE hk l) (Fin.castLE hk l)‖ := by
  apply le_antisymm
  · rw [plk_eq c u b hb hc hk, norm_mul, norm_prod]
    exact mul_le_of_le_one_left (Finset.prod_nonneg fun _ _ => norm_nonneg _)
      ((hW _).1 (det_mem W _ fun _ _ => huW _ _))
  · refine le_trans (le_of_eq ?_) (hq ((plE M k).symm (ι ∘ Fin.castLE hk)))
    rw [plk_eq c u b hb hc hk, Equiv.apply_symm_apply, norm_mul, norm_prod]
    have hMt : (u.submatrix (ι ∘ Fin.castLE hk) (Fin.castLE hk)).BlockTriangular OrderDual.toDual :=
      fun i j hij => hu0 _ _ hij
    rw [Matrix.det_of_isLowerTriangular _ hMt]
    simp [hu1]

theorem mem_of_mulVec {C : Type} [Field C] (W : ValuationSubring C) {m n : ℕ} (ι : Fin n → Fin m)
    (u : Matrix (Fin m) (Fin n) C) (huW : ∀ i j, u i j ∈ W)
    (hu0 : ∀ i j : Fin n, i < j → u (ι i) j = 0) (hu1 : ∀ i, u (ι i) i = 1) (y : Fin n → C)
    (hy : ∀ s, (u *ᵥ y) s ∈ W) (i : Fin n) : y i ∈ W := by
  induction i using WellFoundedLT.induction with
  | ind i ih =>
    have h1 : y i = (u *ᵥ y) (ι i) - ∑ j ∈ Finset.univ.erase i, u (ι i) j * y j := by
      rw [mulVec, dotProduct, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hu1]
      ring
    rw [h1]
    refine W.toSubring.sub_mem (hy _) (W.toSubring.sum_mem fun j hj => ?_)
    rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase hj) with h | h
    · exact W.toSubring.mul_mem (huW _ _) (ih j h)
    · rw [hu0 _ _ h, zero_mul]
      exact W.toSubring.zero_mem

theorem sInf_mul_norm_plk : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] (M n : ℕ) (c : Fin n → Fin (M + 1) → C) (i : Fin n) (q₀ : Fin (plN M i + 1)) (q₁ : Fin (plN M (i + 1) + 1)), plk c id ≠ 0 → (∀ q, ‖plk c (Fin.castLE i.2.le) q‖ ≤ ‖plk c (Fin.castLE i.2.le) q₀‖) → (∀ q, ‖plk c (Fin.castLE (Nat.succ_le_of_lt i.2)) q‖ ≤ ‖plk c (Fin.castLE (Nat.succ_le_of_lt i.2)) q₁‖) → sInf {r : ℝ | ∃ cf : Fin n → C, cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧ (∀ s, ‖(∑ j, cf j • c j) s‖ ≤ 1) ∧ r = ‖cf i‖⁻¹} * ‖plk c (Fin.castLE i.2.le) q₀‖ = ‖plk c (Fin.castLE (Nat.succ_le_of_lt i.2)) q₁‖ := by
  intro C _ _ M n c i q₀ q₁ hne h₀ h₁
  let W : ValuationSubring C := (NormedField.valuation (K := C)).valuationSubring
  have hW : ∀ x, x ∈ W ↔ ‖x‖ ≤ 1 := fun x => by
    rw [Valuation.mem_valuationSubring_iff, NormedField.valuation_apply]
    exact Iff.rfl
  have hli : LinearIndependent C (Matrix.of c)ᵀᵀ := by
    obtain ⟨q, hq⟩ := Function.ne_iff.mp hne
    have h2 := Matrix.linearIndependent_rows_of_det_ne_zero (A := Matrix.of fun l l' => c l (plE M n q l')) hq
    exact LinearIndependent.of_comp (LinearMap.funLeft C C (plE M n q)) h2
  obtain ⟨ι, u, b, huW, hu0, hu1, hb, hbd, hc⟩ := GlobalTheory.exists_integral_pivot_decomposition C W _ _ _ hli
  have hsum : ∀ cf : Fin n → C, ∑ j, cf j • c j = u *ᵥ (b *ᵥ cf) := fun cf => by
    rw [mulVec_mulVec, ← hc]
    funext s
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hdiag : ∀ cf : Fin n → C, (∀ k, i < k → cf k = 0) → (b *ᵥ cf) i = b i i * cf i := fun cf hcf => by
    rw [mulVec, dotProduct]
    refine Finset.sum_eq_single i (fun j _ hj => ?_) (by simp)
    rcases lt_or_gt_of_ne hj with h | h
    · rw [hb h, zero_mul]
    · rw [hcf j h, mul_zero]
  have hbdet : IsUnit b.det := by
    rw [Matrix.det_of_isUpperTriangular hb]
    exact (Finset.prod_ne_zero_iff.mpr fun i _ => hbd i).isUnit
  have hleast : IsLeast {r : ℝ | ∃ cf : Fin n → C, cf i ≠ 0 ∧ (∀ k, i < k → cf k = 0) ∧
      (∀ s, ‖(∑ j, cf j • c j) s‖ ≤ 1) ∧ r = ‖cf i‖⁻¹} ‖b i i‖ := by
    constructor
    · letI := b.invertibleOfIsUnitDet hbdet
      have hinv : (b⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hb
      have hz : ∀ k, i < k → (b⁻¹ *ᵥ Pi.single i 1 : Fin n → C) k = 0 := fun k hk => by
        rw [mulVec_single_one]
        exact hinv hk
      have hbb : b *ᵥ (b⁻¹ *ᵥ Pi.single i 1) = Pi.single i 1 := by
        rw [mulVec_mulVec, mul_nonsing_inv _ hbdet, one_mulVec]
      have h1 := hdiag _ hz
      rw [hbb, Pi.single_eq_same] at h1
      refine ⟨b⁻¹ *ᵥ Pi.single i 1, right_ne_zero_of_mul (h1 ▸ one_ne_zero), hz, fun s => ?_, ?_⟩
      · rw [hsum, hbb, mulVec_single_one]
        exact (hW _).1 (huW _ _)
      · rw [eq_inv_of_mul_eq_one_left h1.symm, norm_inv]
    · rintro r ⟨cf, hcf, hz, hint, rfl⟩
      have h1 := (hW _).1 (mem_of_mulVec W ι u huW hu0 hu1 (b *ᵥ cf)
        (fun s => (hW _).2 (hsum cf ▸ hint s)) i)
      rw [hdiag cf hz, norm_mul] at h1
      rw [← one_div, le_div_iff₀ (norm_pos_iff.2 hcf)]
      exact h1
  rw [hleast.csInf_eq, norm_plk_max W hW c ι u b huW hu0 hu1 hb hc _ q₀ h₀,
    norm_plk_max W hW c ι u b huW hu0 hu1 hb hc _ q₁ h₁, Fin.prod_univ_castSucc, mul_comm]
  rfl

end GlobalTheory.FlagEmb.GradedNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkIdComapOfAffine
section
noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open ReciprocityTheory.AnForm.R (ds_stalkId_eq_map)
open ReciprocityTheory.AnForm.R.FinalTheorems (stalkId)

namespace GlobalTheory.VanStalk

theorem eq_of_forall_prime {R : Type*} [CommRing R] {A B : Ideal R} (hA : A.IsRadical) (hB : B.IsRadical)
    (h : ∀ q : PrimeSpectrum R, A ≤ q.asIdeal ↔ B ≤ q.asIdeal) : A = B := by
  rw [← hA.radical, ← hB.radical, Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
  congr 1
  ext J
  exact ⟨fun ⟨h1, h2⟩ => ⟨(h ⟨J, h2⟩).1 h1, h2⟩, fun ⟨h1, h2⟩ => ⟨(h ⟨J, h2⟩).2 h1, h2⟩⟩

variable {X X' : Scheme.{0}}

theorem van_spec (Z : Closeds X) (x : X) :
    (stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x).IsRadical ∧
    ∀ q : PrimeSpectrum (X.presheaf.stalk x),
      X.fromSpecStalk x q ∈ Z ↔ stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x ≤ q.asIdeal := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hx, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  rw [ds_stalkId_eq_map _ ⟨W, hW⟩ x hx, Scheme.IdealSheafData.vanishingIdeal_ideal]
  letI : Algebra Γ(X, W) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hW.isLocalization_stalk ⟨x, hx⟩
  have hg : (X.presheaf.germ W x hx).hom = algebraMap Γ(X, W) (X.presheaf.stalk x) := rfl
  have hcl : IsClosed (X := PrimeSpectrum Γ(X, W)) (hW.fromSpec ⁻¹' (Z : Set X)) :=
    Z.isClosed.preimage hW.fromSpec.continuous
  rw [hg]
  generalize hJ : PrimeSpectrum.vanishingIdeal (R := Γ(X, W)) (hW.fromSpec ⁻¹' (Z : Set X)) = J
  have hz : PrimeSpectrum.zeroLocus (J : Set Γ(X, W)) = hW.fromSpec ⁻¹' (Z : Set X) := by
    rw [← hJ, PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure, hcl.closure_eq]
    rfl
  have hr : J.radical = J := hJ ▸ (PrimeSpectrum.isRadical_vanishingIdeal _).radical
  refine ⟨?_, fun q => ?_⟩
  · rw [← hr, IsLocalization.map_radical (hW.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl]
    exact Ideal.radical_isRadical _
  · have e : X.fromSpecStalk x q =
        hW.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q) := by
      rw [← hW.fromSpecStalk_eq_fromSpecStalk hx]
      rfl
    rw [e, Ideal.map_le_iff_le_comap]
    change PrimeSpectrum.comap (algebraMap Γ(X, W) (X.presheaf.stalk x)) q ∈ hW.fromSpec ⁻¹' (Z : Set X) ↔ _
    rw [← hz]
    exact (PrimeSpectrum.mem_zeroLocus _ _).trans SetLike.coe_subset_coe

end GlobalTheory.VanStalk

namespace GlobalTheory.VanStalk

variable {X X' : Scheme.{0}}

theorem van_eq_top (Z : Closeds X) {x : X} (hx : x ∉ Z) :
    stalkId (Scheme.IdealSheafData.vanishingIdeal Z) x = ⊤ := by
  by_contra hne
  have h := ((van_spec Z x).2 (IsLocalRing.closedPoint _)).2 (IsLocalRing.le_maximalIdeal hne)
  rw [Scheme.fromSpecStalk_closedPoint] at h
  exact hx h

theorem fromSpecStalk_comap (π : X' ⟶ X) (x' : X') (q : PrimeSpectrum (X'.presheaf.stalk x')) :
    π (X'.fromSpecStalk x' q) = X.fromSpecStalk (π x') (PrimeSpectrum.comap (π.stalkMap x').hom q) := by
  have h := congrArg (fun g => g q) (Scheme.SpecMap_stalkMap_fromSpecStalk π (x := x'))
  simp only [Scheme.Hom.comp_apply] at h
  exact h.symm

theorem van_pre (π : X' ⟶ X) (Z : Closeds X) (x' : X') :
    stalkId (Scheme.IdealSheafData.vanishingIdeal (GlobalTheory.TorRef.pre π Z)) x' =
      ((stalkId (Scheme.IdealSheafData.vanishingIdeal Z) (π x')).map (π.stalkMap x').hom).radical := by
  refine eq_of_forall_prime (van_spec _ _).1 (Ideal.radical_isRadical _) fun q => ?_
  rw [← (van_spec _ _).2, q.isPrime.radical_le_iff, Ideal.map_le_iff_le_comap, GlobalTheory.TorRef.mem_pre,
    fromSpecStalk_comap]
  exact (van_spec Z (π x')).2 _

theorem stalkId_comap_of_affine {T : Scheme.{0}} [IsAffine T] (J : X.IdealSheafData) (χ : T ⟶ X)
    (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) (z : T) :
    stalkId (J.comap χ) z = (stalkId J (χ z)).map (χ.stalkMap z).hom := by
  have key : ∀ z : T, stalkId (Scheme.IdealSheafData.ofIdealTop ((J.ideal U).map (χ.appLE U.1 ⊤ hle).hom)) z =
      (stalkId J (χ z)).map (χ.stalkMap z).hom := by
    intro z
    have hz : χ z ∈ U.1 := hle trivial
    rw [GlobalTheory.LocM.stalkId_ofIdealTop, ds_stalkId_eq_map J U _ hz, Ideal.map_map, Ideal.map_map,
      ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE,
      Category.assoc]
    congr 3
    exact T.presheaf.germ_res (homOfLE hle) z (by trivial)
  rw [← GlobalTheory.Vanishing.eq_comap_of_stalk key, key]

theorem map_le_stalkId_comap (π : X' ⟶ X) (J : X.IdealSheafData) (x' : X') :
    (stalkId J (π x')).map (π.stalkMap x').hom ≤ stalkId (J.comap π) x' := by
  by_cases hx : x' ∈ (J.comap π).support
  · obtain ⟨z, rfl⟩ := GlobalTheory.Vanishing.exists_ι_eq hx
    have h : stalkId J (π ((J.comap π).subschemeι z)) ≤ RingHom.ker
        (((J.comap π).subschemeι.stalkMap z).hom.comp (π.stalkMap ((J.comap π).subschemeι z)).hom) := by
      have h0 := (GlobalTheory.Vanishing.le_ker_iff_stalk ((J.comap π).subschemeι ≫ π)).1
        (Scheme.IdealSheafData.le_map_comap J π) z
      rw [Scheme.Hom.stalkMap_comp] at h0
      exact h0
    rw [← RingHom.comap_ker, GlobalTheory.Vanishing.ker_stalkMap] at h
    exact Ideal.map_le_iff_le_comap.2 h
  · rw [GlobalTheory.Vanishing.stalkId_eq_top _ hx]
    exact le_top

theorem stalkId_comap (π : X' ⟶ X) (J : X.IdealSheafData) (x' : X') :
    stalkId (J.comap π) x' = (stalkId J (π x')).map (π.stalkMap x').hom := by
  refine le_antisymm ?_ (map_le_stalkId_comap π J x')
  obtain ⟨U, hU, hxU, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show π x' ∈ (⊤ : X.Opens) from trivial)
  obtain ⟨V₀, hV, hxV, hVU⟩ := Opens.isBasis_iff_nbhd.1 X'.isBasis_affineOpens
    (show x' ∈ π ⁻¹ᵁ U from hxU)
  let V : X'.Opens := V₀
  haveI : IsAffine V.toScheme := hV
  obtain ⟨z, rfl⟩ : ∃ z : V.toScheme, V.ι z = x' := ⟨⟨x', hxV⟩, rfl⟩
  have hle : ⊤ ≤ (V.ι ≫ π) ⁻¹ᵁ U := fun w _ => hVU w.2
  have h1 := stalkId_comap_of_affine J (V.ι ≫ π) ⟨U, hU⟩ hle z
  rw [Scheme.IdealSheafData.comap_comp] at h1
  have h2 : (stalkId (J.comap π) (V.ι z)).map (V.ι.stalkMap z).hom ≤
      ((stalkId J (π (V.ι z))).map (π.stalkMap (V.ι z)).hom).map (V.ι.stalkMap z).hom := by
    have h0 := map_le_stalkId_comap V.ι (J.comap π) z
    rw [h1, Scheme.Hom.stalkMap_comp] at h0
    rw [Ideal.map_map]
    exact h0
  have hb : Function.Bijective (V.ι.stalkMap z).hom := ConcreteCategory.bijective_of_isIso _
  rwa [Ideal.map_le_iff_le_comap, Ideal.comap_map_of_bijective _ hb] at h2

end GlobalTheory.VanStalk

namespace GlobalTheory.TorRef

end GlobalTheory.TorRef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameHeckeCharacterSplitPlaceLocalComponent
section
open NumberField IsDedekindDomain Formalism.L2

noncomputable section

namespace GlobalTheory.HeckeSplitComp

open ReciprocityTheory.Aut

theorem le_exp_neg_one_of_lt_one {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-(1 : ℕ) : ℤ) := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_le'
  rw [← WithZero.exp_log hx] at h ⊢
  rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
  rw [WithZero.exp_le_exp]; push_cast; omega

theorem main : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (s : ReciprocityTheory.Aut.SplitPlace L) (χ : Formalism.L2.Host.HChar L), χ.TameAt s.w → ∃ ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ, NG.IsCompAt χ s ξ ∧ ∀ (u : (s.v.adicCompletion (maximalRealSubfield L))ˣ) (a : 𝓞 L) (k : Lˣ), (k : L) = (a : L) → Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 → Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) < 1 → ξ u = χ.locK s.w k := by
  intro L _ _ _ s χ hχ
  obtain ⟨c, hc, -, hci⟩ := GlobalTheory.SplitCompl.exists_ringEquiv L s
  have hlt : ∀ y, Valued.v (c y) < 1 ↔ Valued.v y < 1 := GlobalTheory.TypeBlockFix.v_map_lt_one_iff s.v s.w c hc
  have hle : ∀ y, Valued.v (c y) ≤ 1 ↔ Valued.v y ≤ 1 := GlobalTheory.TypeBlockFix.v_map_le_one_iff s.v s.w c hc
  have heq1 : ∀ y, Valued.v y = 1 → Valued.v (c y) = 1 := by
    intro y hy
    refine le_antisymm ((hle y).2 hy.le) (not_lt.1 fun h => ?_)
    have := (hlt y).1 h
    rw [hy] at this
    exact lt_irrefl _ this
  refine ⟨(χ.loc s.w).comp (Units.map c.toRingHom.toMonoidHom), ⟨⟨1, fun u hu => ?_⟩, fun k => ?_⟩, ?_⟩
  · have hu1 : Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) < 1 :=
      lt_of_le_of_lt hu (by rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    have hv : Valued.v (u : s.v.adicCompletion (maximalRealSubfield L)) = 1 := by
      have := Valuation.map_eq_of_sub_lt Valued.v (x := 1)
        (y := (u : s.v.adicCompletion (maximalRealSubfield L))) (by rw [map_one]; exact hu1)
      rwa [map_one] at this
    show χ.loc s.w (Units.map c.toRingHom.toMonoidHom u) = 1
    refine hχ _ (heq1 _ hv) ?_
    have e : ((Units.map c.toRingHom.toMonoidHom u : (s.w.adicCompletion L)ˣ) : s.w.adicCompletion L) - 1 =
        c ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) := by
      rw [map_sub, map_one]; rfl
    rw [e]
    exact le_exp_neg_one_of_lt_one ((hlt _).2 hu1)
  · show χ.loc s.w (Units.map c.toRingHom.toMonoidHom (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k)) =
      χ.loc s.w (Formalism.L2.Host.atFin s.w k)
    congr 1
    ext
    simp [Formalism.L2.Host.atFin, hci]
  · intro u a k hka hu hua
    show χ.loc s.w (Units.map c.toRingHom.toMonoidHom u) = χ.locK s.w k
    have hia : Valued.v (s.i (a : L)) = 1 := by
      have := Valuation.map_eq_of_sub_lt Valued.v (x := (u : s.v.adicCompletion (maximalRealSubfield L)))
        (y := s.i (a : L)) (by rw [Valuation.map_sub_swap, hu]; exact hua)
      rw [this, hu]
    have hk : s.w.valuation L (k : L) = 1 := by
      have h1 := heq1 _ hia
      rw [hci, ← hka] at h1
      rwa [Formalism.UG.P.levelaf_valued_algebraMap] at h1
    refine GlobalTheory.LevMuDet.loc_eq_locK hχ hk ?_
    have e : ((Units.map c.toRingHom.toMonoidHom u : (s.w.adicCompletion L)ˣ) : s.w.adicCompletion L) -
        algebraMap L _ (k : L) = c ((u : s.v.adicCompletion (maximalRealSubfield L)) - s.i (a : L)) := by
      rw [map_sub, hci, hka]; rfl
    rw [e]
    exact (hlt _).2 hua

end GlobalTheory.HeckeSplitComp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentCombinationEigenAction
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb

noncomputable section

namespace GlobalTheory.FlagEmb

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem det_cell_eq_one {T : Type} {m : T → ℕ} {S : Type} [CommRing S] (y : CellVar m → S) (τ : T) :
    (Matrix.of fun i j => cell y τ i j).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    simp [cell]
  · intro i j hij
    have h : i < j := hij
    simp [cell, h.ne, not_lt.2 h.le]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  (t : SAB H X) {R : Type} [CommRing R] {x : Sp R ⟶ X}

theorem eig_of_comb {n : ℕ} (u : Fin n → Tn t R) (cf : Fin n → R) (w : Tn t R) (a : 𝓞 E) (r : R)
    (hu : ∀ j, IsTanAtG t x (u j) ∧ u j ≫ (t.act.act a).left = spMap (epsMul r) ≫ u j)
    (h : IsCombAtG t x u cf w) : w ≫ (t.act.act a).left = spMap (epsMul r) ≫ w := by
  have e := (isCombAtG_iff t x (fun j => ovT (hu j).1) cf w).1 h
  have := t.act.hom a
  have h2 := combT_eig x (fun j => ovT (hu j).1) (t.act.act a) r
    (fun j => Over.OverMorphism.ext (hu j).2) cf
  subst e
  exact congrArg (fun φ => φ.left) h2

theorem isCombAtG_perm {n : ℕ} {u : Fin n → Tn t R} (hu : ∀ j, IsTanAtG t x (u j)) (σ : Equiv.Perm (Fin n))
    (a : Fin n → R) (w : Tn t R) :
    IsCombAtG t x (fun i => u (σ i)) (fun i => a (σ i)) w ↔ IsCombAtG t x u a w := by
  have e : combT x (fun j => ovT (hu (σ j))) (fun i => a (σ i)) = combT x (fun j => ovT (hu j)) a :=
    Equiv.prod_comp σ (fun j => smT x (a j) (ovT (hu j)))
  refine (isCombAtG_iff t x (fun j => ovT (hu (σ j))) _ w).trans ?_
  rw [e]
  exact (isCombAtG_iff t x (fun j => ovT (hu j)) _ w).symm

theorem existsUnique_comb_change {n : ℕ} {e u : Fin n → Tn t R} (he : ∀ j, IsTanAtG t x (e j))
    (K : Matrix (Fin n) (Fin n) R) (hK : IsUnit K.det) (hu : ∀ j, IsCombAtG t x e (fun i => K i j) (u j))
    {w : Tn t R} (hw : IsTanAtG t x w) (hb : ∃! a, IsCombAtG t x e a w) : ∃! a, IsCombAtG t x u a w := by
  have hU : u = fun j => (combT x (fun i => ovT (he i)) (fun i => K i j)).left :=
    funext fun j => ((isCombAtG_iff t x (fun i => ovT (he i)) _ _).1 (hu j)).symm
  subst hU
  have h2 : ∃! a : Fin n → R, ovT hw = combT x (fun j => ovT (he j)) a := by
    obtain ⟨a, ha, hq⟩ := hb
    exact ⟨a, Over.OverMorphism.ext ((isCombAtG_iff t x (fun j => ovT (he j)) _ _).1 ha).symm,
      fun b hb => hq b ((isCombAtG_iff t x (fun j => ovT (he j)) _ _).2 (by rw [← hb]; rfl))⟩
  obtain ⟨a, ha, hq⟩ := reframe_basis x _ (fun j => smT_zero_ovT _) K hK _ h2
  exact ⟨a, (isCombAtG_iff t x _ _ _).2 (by rw [← ha]; rfl),
    fun b hb => hq b (Over.OverMorphism.ext ((isCombAtG_iff t x _ _ _).1 hb).symm)⟩

theorem isFrame_cell {Dw : Datum H} {l : Level H} {c : Coeff l} (f : c.F →+* R) (e u : Vecs Dw t R) (w : Pm Dw.mult)
    (y : CellVar Dw.mult → R) (he : GlobalTheory.LocM.IsFrame t f x e)
    (hu : ∀ τ j, IsCombAtG t x (fun i => e τ (w τ i)) (fun i => cell y τ i j) (u τ j)) :
    GlobalTheory.LocM.IsFrame t f x u := by
  refine ⟨fun τ j => ⟨comb_tan t (fun i => (he.1 τ (w τ i)).1) (hu τ j), fun a => ?_⟩, fun τ v hv hE => ?_⟩
  · exact eig_of_comb t _ _ _ a _ (fun i => ⟨(he.1 τ (w τ i)).1, (he.1 τ (w τ i)).2 a⟩) (hu τ j)
  · refine existsUnique_comb_change t (fun i => (he.1 τ (w τ i)).1) (Matrix.of fun i j => cell y τ i j)
      (by rw [det_cell_eq_one]; exact isUnit_one) (hu τ) hv ?_
    obtain ⟨a, ha, hq⟩ := he.2 τ v hv hE
    refine ⟨fun i => a (w τ i), (isCombAtG_perm t (fun i => (he.1 τ i).1) (w τ) a v).2 ha, fun b hb => ?_⟩
    have h1 := hq (fun i => b ((w τ).symm i))
      ((isCombAtG_perm t (fun i => (he.1 τ i).1) (w τ) _ v).1 (by simpa using hb))
    funext i
    rw [← h1]
    simp

theorem eig_comb_and_frame_cell : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (c : Coeff l) (X : Scheme.{0}) (t : SAB H X)
    (R : Type) [CommRing R] (x : Sp R ⟶ X),
    (∀ (n : ℕ) (u : Fin n → Tn t R) (cf : Fin n → R) (w : Tn t R) (a : 𝓞 E) (r : R),
      (∀ j, IsTanAtG t x (u j) ∧ u j ≫ (t.act.act a).left = spMap (epsMul r) ≫ u j) → IsCombAtG t x u cf w →
        w ≫ (t.act.act a).left = spMap (epsMul r) ≫ w) ∧
    ∀ (f : c.F →+* R) (e u : Vecs Dw t R) (w : Pm Dw.mult) (y : CellVar Dw.mult → R), GlobalTheory.LocM.IsFrame t f x e →
      (∀ τ j, IsCombAtG t x (fun i => e τ (w τ i)) (fun i => cell y τ i j) (u τ j)) → GlobalTheory.LocM.IsFrame t f x u :=
  fun _ _ _ _ _ _ _ _ _ t _ _ _ =>
    ⟨fun _ u cf w a r hu h => eig_of_comb t u cf w a r hu h, fun f e u w y he hu => isFrame_cell t f e u w y he hu⟩

end GlobalTheory.FlagEmb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPulledTraitPointFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricTorsionSection_eq_pulled_trait_point_field : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W]
    (t' : SAB H (Sp W)) (P' : PELUnif (maximalIdeal W) t') (k : ℕ)
    (s' : ∀ (A : Type) [CommRing A] (a : W →+* A) (τ : Multiplicative P'.D.toPre.X →* Aˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ t'.G)),
    (∀ (A A' : Type) [CommRing A] [CommRing A'] (a : W →+* A) (ha : ∀ x ∈ maximalIdeal W, a x = 0) (a' : W →+* A')
      (f : A →+* A') (t₀ : SAB H (Sp A)) (m₀ : SABMap t₀ t' (spMap a)) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp A) P'.D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s' A' a' τ h).left = (z ≫ GlobalTheory.TorusPart.PELUnif.torus P' ha m₀).left ≫ m₀.φ) →
    ∀ (R : Type) [CommRing R] (t : SAB H (Sp R)) (g : R →+* W) (m : SABMap t' t (spMap g))
      (V : Type) [CommRing V] (ψ : R →+* V) (tV : SAB H (Sp V)) (mV : SABMap tV t (spMap ψ))
      (Ω : Type) [Field Ω] (α : V →+* Ω) (β : W →+* Ω) (hβ : ∀ x ∈ maximalIdeal W, β x = 0)
      (tΩ : SAB H (Sp Ω)) (n : SABMap tΩ tV (spMap α)) (n' : SABMap tΩ t' (spMap β))
      (j : splitTorus (Sp V) P'.D.toPre.X ⟶ tV.G),
      GlobalTheory.TorusPart.pullTorus n.cart j = GlobalTheory.TorusPart.PELUnif.torus P' hβ n' →
      n.φ ≫ mV.φ = n'.φ ≫ m.φ →
    ∀ (Ω' : Type) [Field Ω'] (σ : Ω →+* Ω') (a' : W →+* Ω'), a' = σ.comp β →
    ∀ (U : Type) [CommRing U] (u : V →+* U) (w : U →+* Ω'), w.comp u = σ.comp α →
    ∀ (τU : Multiplicative P'.D.toPre.X →* Uˣ) (τ'' : Multiplicative P'.D.toPre.X →* Ω'ˣ) (h : τ'' ^ k = 1),
      (∀ χ, (τ'' χ : Ω') = w (τU χ : U)) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) P'.D.toPre.X),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τU (Multiplicative.ofAdd χ))) →
      (s' Ω' a' τ'' h).left ≫ m.φ = spMap w ≫ (z ≫ j).left ≫ mV.φ := by
  first | exact @GlobalTheory.ToricOverField.toric_section_eq_over_field | exact GlobalTheory.ToricOverField.toric_section_eq_over_field | (intros; apply GlobalTheory.ToricOverField.toric_section_eq_over_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusPointsSubsetHolPeriodicOneParamSpanStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.BdArc Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (Data Frame Bor rmul lact mat col dmin Wt)
open scoped CategoryTheory.MonObj CategoryTheory.Obj
open MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.PeriodSpan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusPoints_subset_holPeriodicOneParamSpan : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] (y : Sp ℂ ⟶ X) (E : TorusExtension ((Over.pullback y).obj G)), torusPts G y E ⊆ (perHolSub G y : Set (Over.mk y ⟶ G)) := by
  first | exact @GlobalTheory.PeriodSpan.torusPts_subset_perHolSub | exact GlobalTheory.PeriodSpan.torusPts_subset_perHolSub | (intros; apply GlobalTheory.PeriodSpan.torusPts_subset_perHolSub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TransitionUniqueAndPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transition_unique_and_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i i₂ : Idx H p) (τ τ' : (Y i₂).X ⟶ (Y i).X) (mu : SABMap (Y i₂).t (Y i).t τ) (mu' : SABMap (Y i₂).t (Y i).t τ'), i.c.F ≤ i₂.c.F → IsTrans i i₂ τ mu → IsTrans i i₂ τ' mu' → τ = τ' ∧ ∀ (k : Type) [Field k] (y : Sp k ⟶ (Xo i₂.l).XF i₂.c) (T : Scheme.{0}) (s : T ⟶ Sp k) (g : T ⟶ (Y i₂).t.G.left), g ≫ (Y i₂).t.G.hom = s ≫ y ≫ (Y i₂).j → g ≫ mu.φ = g ≫ mu'.φ := by
  first | exact @GlobalTheory.TransUniq.trans_unique | exact GlobalTheory.TransUniq.trans_unique | (intros; apply GlobalTheory.TransUniq.trans_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwoMarkingsDifferByLevelIsometryStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_markings_differ_by_level_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (a : CxFr Z σ), (∀ i j Q Q', Per Fu a i Q → Per Fu a j Q' → i = j) ∧ ∀ i Q Q', Per Fu a i Q → Per Fu a i Q' → ∃ gm : (Fu.Di i).La ≃ₗ[𝓞 E] (Fu.Di i).La, IsIsom (Fu.Di i) gm ∧ IsLev l (Fu.Di i) gm ∧ ∀ v, Q' (gm v) = Q v := by
  first | exact @GlobalTheory.ShFam.Hor.TwoMarkings.per_unique | exact GlobalTheory.ShFam.Hor.TwoMarkings.per_unique | (intros; apply GlobalTheory.ShFam.Hor.TwoMarkings.per_unique <;> assumption)
end

