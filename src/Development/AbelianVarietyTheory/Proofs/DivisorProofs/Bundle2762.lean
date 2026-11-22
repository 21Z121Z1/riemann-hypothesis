import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1481
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2057
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1527
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2666
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2554
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2464
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSiegelDomainDecay
section
noncomputable section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThKSoDecay GlobalTheory.ThKTorus

namespace GlobalTheory.ThKTorus

theorem torusDecay : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ (q : ℕ) (x y : Fin q → Fin n → E), IsFrameU σ X.J x y →
    ∀ Cc : Set (UA σ X.J), IsCompact Cc → ∀ c : ℝ, 0 < c →
    ∀ φ ∈ SB (Fin n × Fin d → Af F), (∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ M.So B.ψ B.τ₁) →
    ∀ N : ℕ, ∃ (C : ℝ) (k : ℕ), ∀ (f : SInf F (Fin n × Fin d)) (t : Fin q → ℝ) (a κ : UA σ X.J) (h : UA σ W.J),
      (∀ i, c ≤ t i) → IsTorusU x y t a → κ ∈ Cc →
      ‖theta om (pureA F f φ) (a * κ) h‖ * (1 + ∏ i, t i) ^ N ≤ C * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k := by
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hPair q x y hxy Cc hCc c hc φ hφ hφS N
  obtain ⟨M₁, blk, e, c₀, hM₁, hF, hE, hc₀, hθ⟩ := GlobalTheory.T.exists_model_blocks_unitary_frame hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy
  obtain ⟨A, hA⟩ := GlobalTheory.T.norm_weil_action_pure_tensor_le_majorant hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy M₁ blk e hM₁ hF hE Cc hCc c hc φ hφ
  obtain ⟨N₁, C₅, K, h5⟩ := GlobalTheory.T.lattice_sum_polynomial_bound F (Fin n × Fin d) q blk A N c hc
  obtain ⟨C₄, k, h4⟩ := hA N₁
  refine ⟨‖c₀⁻¹‖ * max C₄ 0 * max C₅ 0 * (max C₄ 0) ^ K, k * (K + 1), fun f t a κ h htc ha hκ => ?_⟩
  obtain ⟨m, hm1, hmC, hb⟩ := h4 f t a κ h htc ha hκ
  obtain ⟨hsum, hle⟩ := h5 m t hm1 htc
  have hΦ : pureA F f φ ∈ schA F (Fin n × Fin d) := Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  have hΨ : om (a * κ, h) (pureA F f φ) ∈ schA F (Fin n × Fin d) := hPair.weil.isUSplitting.pres _ _ hΦ
  have ht0 : ∀ i, 0 ≤ t i := fun i => hc.le.trans (htc i)
  have hsk : 0 ≤ semK (Fin n × Fin d) k f := apply_nonneg _ _
  have hhk : (0 : ℝ) ≤ (ht h : ℝ) ^ k := pow_nonneg (NNReal.coe_nonneg _) _
  have hC4 : (0 : ℝ) ≤ max C₄ 0 := le_max_right _ _
  have hB' : 0 ≤ max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k := mul_nonneg (mul_nonneg hC4 hsk) hhk
  have hpt : ∀ ξ : Fin n × Fin d → F, ‖e (om (a * κ, h) (pureA F f φ)) (fun j => algebraMap F (AF F) (ξ j))‖ ≤
      max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * latG (F := F) blk A N₁ m t ξ := by
    intro ξ
    unfold latG
    split_ifs with hnz
    · calc _ ≤ C₄ * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majI blk A N₁ m t ξ := hb ξ
        _ ≤ max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * majI blk A N₁ m t ξ := by
          apply mul_le_mul_of_nonneg_right _ (majI_nonneg _ _ _ _ _ _ ht0)
          apply mul_le_mul_of_nonneg_right _ hhk
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) hsk
    · push_neg at hnz
      rw [GlobalTheory.T.unitary_frame_model_evaluation hP F E σ B n d X W M χX χW om r s r' s' hPair q x y hxy M₁ blk e hM₁ hF hE _ (hφS f) (a * κ) h ξ hnz]
      simp
  have hs : Summable fun ξ : Fin n × Fin d → F =>
      ‖e (om (a * κ, h) (pureA F f φ)) (fun j => algebraMap F (AF F) (ξ j))‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpt (hsum.mul_left _)
  have hT : ‖thetaSum F (e (om (a * κ, h) (pureA F f φ)))‖ ≤
      max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * ∑' ξ, latG (F := F) blk A N₁ m t ξ := by
    rw [← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hs).trans (Summable.tsum_le_tsum hpt hs (hsum.mul_left _))
  have e1 : theta om (pureA F f φ) (a * κ) h = c₀⁻¹ * thetaSum F (e (om (a * κ, h) (pureA F f φ))) := by
    rw [hθ _ hΨ, ← mul_assoc, inv_mul_cancel₀ hc₀, one_mul]; rfl
  have hP0 : (0 : ℝ) ≤ (1 + ∏ i, t i) ^ N := pow_nonneg (add_nonneg zero_le_one (Finset.prod_nonneg fun i _ => ht0 i)) _
  have hmK : (m : ℝ) ^ K ≤ (max C₄ 0 * (ht h : ℝ) ^ k) ^ K :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (hmC.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hhk)) K
  have hsemi : semK (Fin n × Fin d) k f ≤ semK (Fin n × Fin d) (k * (K + 1)) f := by
    have hk : k ≤ k * (K + 1) := Nat.le_mul_of_pos_right k (Nat.succ_pos K)
    have hle' : semK (F := F) (Fin n × Fin d) k ≤ semK (F := F) (Fin n × Fin d) (k * (K + 1)) :=
      Finset.sup_mono (Finset.Iic_subset_Iic.2 (Prod.mk_le_mk.2 ⟨hk, hk⟩))
    exact hle' f
  have hS0 : 0 ≤ ∑' ξ, latG (F := F) blk A N₁ m t ξ := tsum_nonneg fun ξ => latG_nonneg _ _ _ _ _ _ ht0
  calc ‖theta om (pureA F f φ) (a * κ) h‖ * (1 + ∏ i, t i) ^ N
      ≤ ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k * ∑' ξ, latG (F := F) blk A N₁ m t ξ) *
          (1 + ∏ i, t i) ^ N := by
        rw [e1, norm_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT (norm_nonneg _)) hP0
    _ = ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k) *
          ((∑' ξ, latG (F := F) blk A N₁ m t ξ) * (1 + ∏ i, t i) ^ N) := by ring
    _ ≤ ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) k f * (ht h : ℝ) ^ k) * (max C₅ 0 * (m : ℝ) ^ K) :=
        mul_le_mul_of_nonneg_left (hle.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (Nat.cast_nonneg _) _)))
          (mul_nonneg (norm_nonneg _) hB')
    _ ≤ ‖c₀⁻¹‖ * (max C₄ 0 * semK (Fin n × Fin d) (k * (K + 1)) f * (ht h : ℝ) ^ k) *
          (max C₅ 0 * (max C₄ 0 * (ht h : ℝ) ^ k) ^ K) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsemi hC4) hhk)
          (norm_nonneg _)) (mul_le_mul_of_nonneg_left hmK (le_max_right _ _))
          (mul_nonneg (le_max_right _ _) (pow_nonneg (Nat.cast_nonneg _) _))
        exact mul_nonneg (norm_nonneg _) (mul_nonneg (mul_nonneg hC4 (apply_nonneg _ _)) hhk)
    _ = ‖c₀⁻¹‖ * max C₄ 0 * max C₅ 0 * (max C₄ 0) ^ K * semK (Fin n × Fin d) (k * (K + 1)) f *
          (ht h : ℝ) ^ (k * (K + 1)) := by
        rw [mul_pow, ← pow_mul, show k * (K + 1) = k + k * K by ring, pow_add]; ring

end GlobalTheory.ThKTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecRatioAppRestrict
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem secRatio_app_restrict {Y Z : Scheme.{0}} (h : Z ⟶ Y) {U W : Y.Opens} (hle : W ≤ U)
    (hle' : h ⁻¹ᵁ W ≤ h ⁻¹ᵁ U) (x : Γ(Y, U)) :
    (Z.presheaf.map (homOfLE hle').op).hom ((h.app U).hom x) =
      (h.app W).hom ((Y.presheaf.map (homOfLE hle).op).hom x) := by
  have := congrArg (fun φ => φ.hom x) (h.naturality (homOfLE hle).op)
  simpa using this.symm

theorem secRatioEq_comp : ∀ {X Y Z : Scheme.{0}} (L : LB X) {k k' : ℕ} (u v : Y ⟶ X) (h : Z ⟶ Y) (s₁ s₂ : H0 L k) (t₁ t₂ : H0 L k'), SecRatioEq L u v s₁ s₂ t₁ t₂ → SecRatioEq L (h ≫ u) (h ≫ v) s₁ s₂ t₁ t₂ := by
  intro X Y Z L k k' u v h s₁ s₂ t₁ t₂ hR i i'
  have e := congrArg (h.app (u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i')).hom (hR i i')
  simp only [map_mul] at e
  simp only [Scheme.Hom.comp_app, CommRingCat.hom_comp, RingHom.comp_apply]
  erw [secRatio_app_restrict h (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i),
    secRatio_app_restrict h (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i'),
    secRatio_app_restrict h (inf_le_left : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ u ⁻¹ᵁ secChart L i),
    secRatio_app_restrict h (inf_le_right : u ⁻¹ᵁ secChart L i ⊓ v ⁻¹ᵁ secChart L i' ≤ v ⁻¹ᵁ secChart L i')]
  exact e

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOfExpansionModMaximalIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.ExpandNonzero

open ReciprocityTheory.ChartRestriction.G.Semi

theorem mem_wchart {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (j : K → L.ι) (y : Y) : y ∈ LB.wchart L φ j ↔ ∀ k, (φ k).base y ∈ L.U (j k) := by
  show y ∈ ⋂ k, (φ k).base ⁻¹' (L.U (j k) : Set X) ↔ _
  exact Set.mem_iInter

theorem sec_mem_basicOpen {X : Scheme.{0}} {L : LB X} (s : LB.Sec L) (i j : L.ι) {x : X}
    (hx : x ∈ X.basicOpen (s.f j)) (hi : x ∈ L.U i) : x ∈ X.basicOpen (s.f i) := by
  have hxj : x ∈ L.U j := X.basicOpen_le _ hx
  have h := congrArg X.basicOpen (s.compat i j)
  simp only [Scheme.basicOpen_res, Scheme.basicOpen_mul,
    Scheme.basicOpen_of_isUnit _ (L.g i j).isUnit] at h
  have hm : x ∈ (L.U i ⊓ L.U j) ⊓ ((L.U i ⊓ L.U j) ⊓ X.basicOpen (s.f j)) :=
    ⟨⟨hi, hxj⟩, ⟨hi, hxj⟩, hx⟩
  rw [← h] at hm
  exact hm.2

theorem nonzero_of_expandsAt_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G]
      [IsCommMonObj G] (U : UnifPre (maximalIdeal R) D A G) (k : ℕ) (s : H0 U.LG.L k)
      (f : ∀ α : D.toPre.X, D.toPre.SecB k α), U.ExpandsAt 0 k s f →
      (∀ α, α ≠ 0 → ∀ j : Fin 4 → D.toPre.P.L.ι, ((U.gt 0).pG.left.app _).hom ((f α).f j) = 0) →
      ∀ y : (thickObj R (maximalIdeal R) 0 G).left,
      (∃ j : Fin 4 → D.toPre.P.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
          (((U.gt 0).pG.left.app _).hom ((f 0).f j))) →
      ∃ i : Fin 1 → U.LG.L.ι, y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
        (((fstG (maximalIdeal R) 0 G).left.app (secChart U.LG.L i)).hom (s.f i)) := by
  intro R _ _ _ D A G _ _ U k s f hexp hzero y hy
  classical
  obtain ⟨j, hj⟩ := hy
  obtain ⟨S, hS, hE⟩ := hexp
  have hcovM : ∀ ψ : (thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left,
      ∃ i, ψ.base y ∈ D.toPre.P.L.U i := fun ψ => by
    have : ψ.base y ∈ ⨆ i, D.toPre.P.L.U i := by rw [D.toPre.P.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  obtain ⟨iL, hiL⟩ : ∃ i, (fstG (maximalIdeal R) 0 G).left.base y ∈ U.LG.L.U i := by
    have : (fstG (maximalIdeal R) 0 G).left.base y ∈ ⨆ i, U.LG.L.U i := by
      rw [U.LG.isLB.cover]; trivial
    exact TopologicalSpace.Opens.mem_iSup.1 this
  let idx : ((thickObj R (maximalIdeal R) 0 G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι :=
    fun ψ => (hcovM ψ).choose
  have hidx : ∀ ψ, ψ.base y ∈ D.toPre.P.L.U (idx ψ) := fun ψ => (hcovM ψ).choose_spec
  refine ⟨fun _ => iL, ?_⟩
  have h0S : (0 : D.toPre.X) ∈ S := by
    by_contra h
    have h' := hS 0 h j
    rw [h', Scheme.basicOpen_zero] at hj
    exact hj
  have key := hE (fun _ => idx (U.gt 0).pG.left, fun _ => iL) (fun _ => iL)
    (fun α i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB α i))
    (fun α i => idx (D.toPre.Oφ (U.gt 0).pG α i)) rfl (by
      intro a b hab
      rcases a with _ | (a | a) <;> rcases b with _ | (b | b) <;> exact congrArg idx hab)

  have hyW : y ∈ U.expW 0 (fun _ => idx (U.gt 0).pG.left, fun _ => iL) (fun _ => iL) S
      (fun α i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB α i))
      (fun α i => idx (D.toPre.Oφ (U.gt 0).pG α i)) := by
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · exact (mem_wchart _ _ _ y).2 fun _ => hidx _
    · exact (mem_wchart _ _ _ y).2 fun _ => hiL
    · show (fstG (maximalIdeal R) 0 G).left.base y ∈ LB.wchart _ _ _
      exact (mem_wchart _ _ _ _).2 fun _ => hiL
    · refine Finset.inf_induction
        (p := fun V : (thickObj R (maximalIdeal R) 0 G).left.Opens => y ∈ V)
        (show y ∈ (⊤ : (thickObj R (maximalIdeal R) 0 G).left.Opens) from trivial)
        (fun a ha b hb => TopologicalSpace.Opens.mem_inf.2 ⟨ha, hb⟩) fun α _ =>
          TopologicalSpace.Opens.mem_inf.2 ⟨?_, ?_⟩
      · show (U.gt 0).pG.left.base y ∈ LB.wchart _ _ _
        exact (mem_wchart _ _ _ _).2 fun i => hidx ((U.gt 0).pG.left ≫ D.toPre.famφB α i)
      · exact (mem_wchart _ _ _ y).2 fun i => hidx _

  have hf0 : y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen
      (((U.gt 0).pG.left.app _).hom
        ((f 0).f (fun i => idx ((U.gt 0).pG.left ≫ D.toPre.famφB 0 i)))) := by
    rw [← Scheme.preimage_basicOpen] at hj ⊢
    exact sec_mem_basicOpen (f 0) _ j hj
      ((mem_wchart _ _ _ _).2 fun i => hidx ((U.gt 0).pG.left ≫ D.toPre.famφB 0 i))
  rw [Finset.sum_eq_single ⟨0, h0S⟩ (fun b _ hb => by
      have hb' : b.1 ≠ 0 := fun h => hb (Subtype.ext h)
      refine mul_eq_zero_of_left ?_ _
      exact (congrArg _ (hzero b.1 hb' _)).trans (map_zero _))
    (fun h => absurd (Finset.mem_attach _ _) h)] at key
  have hL := (congrArg (fun a => y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen a) key).mpr (by
    simp only [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ (Units.isUnit _),
      Scheme.basicOpen_res, TopologicalSpace.Opens.mem_inf]
    exact ⟨⟨hyW, hf0⟩, hyW⟩)
  simp only [Scheme.basicOpen_mul, Scheme.basicOpen_of_isUnit _ ((Units.isUnit _).pow k),
    Scheme.basicOpen_res, TopologicalSpace.Opens.mem_inf] at hL
  exact hL.2.2

end GlobalTheory.Mum.ExpandNonzero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionNonzeroOnEveryFibreLocalFormBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sectionNonzeroOnEveryFibre_localFormBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (δ : LB S)
    (σ : (CechPic.tens L.L (δ.pull G.hom)).Sec) (i : δ.ι) (R : Type) [CommRing R] (ξ : Sp R ⟶ S) (t : (KeyVals.bL L ξ).L.Sec),
    ⊤ ≤ ξ ⁻¹ᵁ δ.U i → KeyVals.IsLocSec σ i ξ t → NzFib σ → NzFib t := by
  first | exact @GlobalTheory.KeyVals.nzFib_of_isLocSec | exact GlobalTheory.KeyVals.nzFib_of_isLocSec | (intros; apply GlobalTheory.KeyVals.nzFib_of_isLocSec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualAndPrincipalCongruenceOrbitsOfGoodLevelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_and_principalCongruence_orbits_of_goodLevel : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → (∀ p : ℕ, p.Prime → l.GoodAt p) → 1 ≤ Dw.p → 1 ≤ Dw.q → ∀ k : U.Comp, GlobalTheory.EqCovol.IsSelfDualTr (U.X k) ∧ ∀ γ ∈ (U.X k).Γ, ∀ x ∈ (U.X k).dom, ∃ γ' : GL (Fin r) E, IsUStab (U.X k).Gm (U.X k).Λ γ' ∧ (∀ v ∈ (U.X k).Λ, ∃ w ∈ (U.X k).Λ, (γ' : Matrix (Fin r) (Fin r) E).mulVec v - v = l.M' • w) ∧ ∃ b ∈ Bor (U.X k).Ψ r, lact γ x = rmul (lact γ' x) b := by
  first | exact @GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf | exact GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf | (intros; apply GlobalTheory.EqCovol.selfDual_and_congr_of_isUnf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianEndomorphismUniqueOverDegenerationDatStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_endomorphism_unique_over_degenerationData : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X), (∀ b b', FormalEnd U.toUnifPre a h' b → FormalEnd U.toUnifPre a h' b' → b = b') ∧ ∀ b b' : G ⟶ G, (∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map b = (Over.pullback (thick R (maximalIdeal R) e)).map b') → b = b' := by
  first | exact @GlobalTheory.MumUniq.main | exact GlobalTheory.MumUniq.main | (intros; apply GlobalTheory.MumUniq.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericEndomorphismExtendsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_generic_endomorphism_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ f : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom f → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = f := by
  first | exact @GlobalTheory.Mum.genericEnd_extends | exact GlobalTheory.Mum.genericEnd_extends | (intros; apply GlobalTheory.Mum.genericEnd_extends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianGenericFibreHomExtendsNormalNoetheria
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.semiAbelian_end_generic_extends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, IsMonHom φ → ∃ g : G ⟶ G, IsMonHom g ∧ (Over.pullback (jK R)).map g = φ := by
  intro R _ _ _ _ G _ hG φ hφ
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := GlobalTheory.semiAbelianHomExtension_holds.of_isGenericPointHom
    (GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec R)
    (GlobalTheory.IsGenericPointHom.fractionField R (FractionRing R)) hG hG φ
  exact ⟨F, hF, hF'⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtendsAtStalkAgreeingOnOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelian_hom_extends_at_stalk_agreeing_on_open : ∀ {U S : Scheme.{0}} (j : U ⟶ S) [IsOpenImmersion j] (G H : Over S) [GrpObj G] [GrpObj H], IsSemiAbelian G → IsSemiAbelian H → ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f → ∀ (s : S) [IsDomain (S.presheaf.stalk s)] [IsNoetherianRing (S.presheaf.stalk s)] [IsIntegrallyClosed (S.presheaf.stalk s)] (k : Sp (FractionRing (S.presheaf.stalk s)) ⟶ U), k ≫ j = ReciprocityTheory.ChartRestriction.G.Out.jK (S.presheaf.stalk s) ≫ S.fromSpecStalk s → ∃ g : pullback G.hom (S.fromSpecStalk s) ⟶ H.left, g ≫ H.hom = pullback.fst G.hom (S.fromSpecStalk s) ≫ G.hom ∧ GlobalTheory.DedekindExt.Agree (pullback.fst G.hom j) (f.left ≫ pullback.fst H.hom j) (pullback.fst G.hom (S.fromSpecStalk s)) g := by
  first | exact @GlobalTheory.StalkExt.exists_agree_at_stalk | exact GlobalTheory.StalkExt.exists_agree_at_stalk | (intros; apply GlobalTheory.StalkExt.exists_agree_at_stalk <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermInjectiveClosedPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_germ_injective_closed_point : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, Function.Injective ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) := by
  first | exact @GlobalTheory.Mum.LocalInj.base_to_stalk_injective | exact GlobalTheory.Mum.LocalInj.base_to_stalk_injective | (intros; apply GlobalTheory.Mum.LocalInj.base_to_stalk_injective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGermPrimeIdealMapStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiabelian_germ_prime_ideal_map : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], AdmBase R' (maximalIdeal R') → ∀ (G₁ : Over (Sp R')) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ x : G₁.left, G₁.hom x = closedPoint R' → ∀ q : Ideal R', q.IsPrime → (Ideal.map ((G₁.left.presheaf.germ ⊤ x trivial).hom.comp ((G₁.hom.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R')).inv.hom)) q).IsPrime := by
  first | exact @GlobalTheory.Mum.ideal_map_stalk_isPrime_of_closedPoint | exact GlobalTheory.Mum.ideal_map_stalk_isPrime_of_closedPoint | (intros; apply GlobalTheory.Mum.ideal_map_stalk_isPrime_of_closedPoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemilinearDualBasisBaseChangeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semilinear_dual_basis_base_change : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] {M' : Type*} [AddCommGroup M'] [Module R' M']
    (f : M →ₛₗ[algebraMap R R'] M') (hf : Function.Bijective (liftSemi f)) {n : ℕ}
    (b : Module.Dual R M ≃ₗ[R] (Fin n → R)) (x : Fin n → Module.Dual R' M')
    (hx : ∀ k c, x k (f c) = algebraMap R R' (b.symm (Pi.single k 1) c)),
   LinearIndependent R' x ∧ Submodule.span R' (Set.range x) = ⊤ := by
  first | exact @GlobalTheory.dualBasis_baseChange | exact GlobalTheory.dualBasis_baseChange | (intros; apply GlobalTheory.dualBasis_baseChange <;> assumption)
end

