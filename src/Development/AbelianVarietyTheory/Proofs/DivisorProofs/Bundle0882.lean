import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0862
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HenselianLocalRingOfIsAdicComplete
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RatioTranslate
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TorsionInvariantDescendsFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0845
import Formalism.LocalToGlobal.InertKernelTheory.StatementAlg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0864
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0814
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0836
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqFieldExtensionLeComparableNorms
section
open NumberField GlobalTheory.AllWt

noncomputable section

namespace GlobalTheory.SlopeMaxExt

open Module Matrix

section One

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] {N : (K →+* ℂ) → V → ℝ} {L : Submodule (𝓞 K) V}

omit [Module K V] [IsScalarTower (𝓞 K) K V] in

theorem fg_of_le (hL : L.FG) {M : Submodule (𝓞 K) V} (hM : M ≤ L) : M.FG := by
  haveI : IsNoetherian (𝓞 K) L := isNoetherian_of_fg_of_noetherian L hL
  exact isNoetherian_submodule.1 inferInstance M hM

theorem exists_slope_eq (hN : HasGram N) (hL : L.FG) (h0 : L ≠ ⊥) :
    ∃ M : Submodule (𝓞 K) V, M ≤ L ∧ M ≠ ⊥ ∧ slope_sq N M = slopeMax_sq N L := by
  letI : StarRing K := starRingOfComm
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  obtain ⟨hLat, -, -⟩ := Formalism.HN.plLat K V _ b X (fun v => (hG v).1) L hL
  obtain ⟨-, -, ⟨M, hM, hM0, hMs⟩, -, -⟩ := Formalism.HN.muChar _ _ _ _ L hLat h0
  refine ⟨M, hM.1, hM0, ?_⟩
  rw [slope_sq_eq hG (fg_of_le hL hM.1), (slopeMax_slopeMin_eq hG hL h0).1]
  simp only [Formalism.HN.muDef, Formalism.HN.muMaxDef, hMs]

theorem slope_le_slopeMax (hN : HasGram N) (hL : L.FG) {M : Submodule (𝓞 K) V} (hM : M ≤ L) (hM0 : M ≠ ⊥) :
    slope_sq N M ≤ slopeMax_sq N L := by
  letI : StarRing K := starRingOfComm
  have h0 : L ≠ ⊥ := fun h => hM0 (eq_bot_iff.2 (h ▸ hM))
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN
  have l1 := (Formalism.HN.plLat K V _ b X (fun v => (hG v).1) M (fg_of_le hL hM)).1
  have l2 := (Formalism.HN.plLat K V _ b X (fun v => (hG v).1) L hL).1
  have m1 := Formalism.HN.muChar _ _ _ _ _ l1 hM0
  have m2 := (Formalism.HN.muChar _ _ _ _ _ l2 h0).1
  have key := (m1.1 _).2 fun P hP => (m2 _).1 le_rfl P (hP.trans hM)
  have := m1.2.2.2.2
  rw [slope_sq_eq hG (fg_of_le hL hM), (slopeMax_slopeMin_eq hG hL h0).1]
  unfold Formalism.HN.muDef Formalism.HN.muMaxDef
  linarith

end One

section Two

variable {K K' V V' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V']
  (ι : V →ₛₗ[algebraMap K K'] V')

omit [NumberField K] [NumberField K'] in

theorem map_mem_of_mem_span {s : Set V} {P : Submodule (𝓞 K') V'} (hs : ∀ x ∈ s, ι x ∈ P) {x : V}
    (hx : x ∈ Submodule.span (𝓞 K) s) : ι x ∈ P := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => rw [map_zero]; exact P.zero_mem
  | add x y _ _ hx hy => rw [map_add]; exact P.add_mem hx hy
  | smul a x _ hx =>
    have : ι (a • x) = algebraMap (𝓞 K) (𝓞 K') a • ι x := by
      rw [← algebraMap_smul K a, map_smulₛₗ, ← algebraMap_smul K' (algebraMap (𝓞 K) (𝓞 K') a)]
      rfl
    rw [this]; exact P.smul_mem _ hx

omit [NumberField K] [NumberField K'] in

theorem fg_span_image {L : Submodule (𝓞 K) V} (hL : L.FG) :
    (Submodule.span (𝓞 K') (ι '' (L : Set V))).FG := by
  obtain ⟨s, rfl⟩ := hL
  refine Submodule.fg_def.2 ⟨ι '' s, s.finite_toSet.image _, le_antisymm ?_ ?_⟩
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact map_mem_of_mem_span ι (fun y hy => Submodule.subset_span (Set.mem_image_of_mem _ hy)) hx

omit [NumberField K] [NumberField K'] [IsScalarTower (𝓞 K) K V] [IsScalarTower (𝓞 K') K' V'] in

theorem span_image_ne_bot
    (hli : ∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k)))
    {L : Submodule (𝓞 K) V} (h0 : L ≠ ⊥) : Submodule.span (𝓞 K') (ι '' (L : Set V)) ≠ ⊥ := by
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  have h1 := (hli 1 (fun _ => x) (linearIndependent_unique_iff.2 hx0)).ne_zero 0
  intro h
  exact h1 (Submodule.span_eq_bot.1 h _ ⟨x, hx, rfl⟩)

end Two

theorem exists_frame {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (X : InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) (hX : ∀ v, IsUnit (X v).det)
    (τ : K →+* ℂ) {t : ℝ} (ht : 0 < t) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y.det ∧ ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y⁻¹ *ᵥ fun i => τ (b.repr x i)) =
      t * Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x := by
  have hs : ∀ u : Fin n → ℂ, Formalism.HermitianLatticesTheory.cnorm ((t : ℂ) • u) = t * Formalism.HermitianLatticesTheory.cnorm u := fun u => by
    unfold Formalism.HermitianLatticesTheory.cnorm
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, ← Finset.mul_sum, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq ht.le]
  have key : ∀ Z : Matrix (Fin n) (Fin n) ℂ, IsUnit Z.det →
      (∀ x, Formalism.HermitianLatticesTheory.cnorm (Z *ᵥ fun i => τ (b.repr x i)) = Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x) →
      ∃ Y : Matrix (Fin n) (Fin n) ℂ, IsUnit Y.det ∧ ∀ x, Formalism.HermitianLatticesTheory.cnorm (Y⁻¹ *ᵥ fun i => τ (b.repr x i)) =
        t * Formalism.HermitianLatticesTheory.normAt b X (InfinitePlace.mk τ) x := fun Z hZ h => by
    have hu : IsUnit ((t : ℂ) • Z).det := by
      rw [det_smul]
      exact (IsUnit.pow _ (Ne.isUnit (by exact_mod_cast ht.ne'))).mul hZ
    refine ⟨((t : ℂ) • Z)⁻¹, isUnit_nonsing_inv_det _ hu, fun x => ?_⟩
    rw [nonsing_inv_nonsing_inv _ hu, smul_mulVec, hs, h]
  have hi := isUnit_nonsing_inv_det _ (hX (InfinitePlace.mk τ))
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · refine key _ hi fun x => ?_
    unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
    rw [h]
  · refine key ((starRingEnd ℂ).mapMatrix (X (InfinitePlace.mk τ))⁻¹) ?_ fun x => ?_
    · rw [← RingHom.map_det]; exact hi.map _
    · unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt Formalism.HermitianLatticesTheory.cnorm
      rw [h]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Complex.norm_conj]
      simp [Matrix.mulVec, dotProduct]

def coordExt {K V : Type} (F : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) : V →ₛₗ[algebraMap K F] (Fin n → F) where
  toFun x i := algebraMap K F (b.repr x i)
  map_add' x y := by funext i; simp
  map_smul' a x := by funext i; simp

theorem coordExt_li {K V : Type} (F : Type) [Field K] [Field F] [Algebra K F] [AddCommGroup V] [Module K V] {n : ℕ}
    (b : Basis (Fin n) K V) (m : ℕ) (e : Fin m → V) (he : LinearIndependent K e) :
    LinearIndependent F fun k => coordExt F b (e k) :=
  (linearIndependent_algebraMap_comp_iff (S := F) (v := fun k => b.equivFun (e k))).2
    (he.map' b.equivFun.toLinearMap b.equivFun.ker)

theorem slopeMax_sq_span_le : ∀ (K K' V V' : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field K'] [NumberField K'] [Algebra K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V'] (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V) (c : (K' →+* ℂ) → ℝ) (B : ℝ), HasGram N → HasGram N' → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → (∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k))) → L.FG → L ≠ ⊥ → (∀ σ', 0 < c σ' ∧ |Real.log (c σ')| ≤ B) → (∀ σ' x, N' σ' (ι x) = c σ' * N (σ'.comp (algebraMap K K')) x) → slopeMax_sq N' (Submodule.span (𝓞 K') (ι '' (L : Set V))) ≤ slopeMax_sq N L + 2 * B := by
  intro K K' V V' _ _ _ _ _ _ _ _ _ _ _ _ _ _ N N' ι L c B hN hN' hc hli hL h0 hcB hι
  haveI : IsTotallyComplex K' := isTotallyComplex_of_algebra K K'
  haveI : Module.Finite K K' := Module.Finite.of_restrictScalars_finite ℚ K K'
  haveI : IsAlgClosure K (AlgebraicClosure K') := ⟨inferInstance, Algebra.IsAlgebraic.trans K K' _⟩
  let F : Type := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  haveI : IsGalois K F := inferInstance
  haveI : NumberField F := NumberField.of_module_finite K F
  have hL' := fg_span_image ι hL
  obtain ⟨M, hM, hM0, hMs⟩ := exists_slope_eq hN' hL' (span_image_ne_bot ι hli h0)
  have hMfg := fg_of_le hL' hM
  obtain ⟨⟨n, ⟨b, X⟩, hG⟩⟩ := hN'
  letI : StarRing K' := starRingOfComm
  let N₁ : (K' →+* ℂ) → V' → ℝ := fun σ x => N' (InfinitePlace.mk σ).embedding x
  have hG₁ : IsGram b X N₁ := fun v => ⟨(hG v).1, fun x => by
    simp only [N₁, InfinitePlace.mk_embedding]; exact (hG v).2 x⟩
  have hc₁ : ∀ σ x, N₁ ((starRingEnd ℂ).comp σ) x = N₁ σ x := fun σ x => by
    have : InfinitePlace.mk ((starRingEnd ℂ).comp σ) = InfinitePlace.mk σ := InfinitePlace.mk_conjugate_eq σ
    simp only [N₁, this]
  choose Y hY hYn using fun τ : K' →+* ℂ => exists_frame b X (fun v => (hG v).1) τ
    (inv_pos.2 (hcB (InfinitePlace.mk τ).embedding).1)
  let N₂ : (F →+* ℂ) → (Fin n → F) → ℝ := fun σ y =>
    Formalism.HermitianLatticesTheory.cnorm ((Y (σ.comp (algebraMap K' F)))⁻¹ *ᵥ fun i => σ (y i))
  have hG₂ : IsGram (Pi.basisFun F (Fin n)) (fun u => Y (u.embedding.comp (algebraMap K' F))) N₂ :=
    fun u => ⟨hY _, fun y => by
      unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
      simp only [N₂, Pi.basisFun_repr]⟩
  have hN₂ : HasGram N₂ := ⟨⟨n, ⟨(_, _), hG₂⟩⟩⟩
  let φ := coordExt F b
  have hφ : ∀ (σ : F →+* ℂ) x, N₂ σ (φ x) = (c (InfinitePlace.mk (σ.comp (algebraMap K' F))).embedding)⁻¹ *
      N₁ (σ.comp (algebraMap K' F)) x := fun σ x => (hYn _ x).trans (by rw [(hG _).2])
  let ψ : V →ₛₗ[algebraMap K F] (Fin n → F) :=
    { toFun := fun x => φ (ι x)
      map_add' := fun x y => by simp
      map_smul' := fun a x => by
        rw [map_smulₛₗ, map_smulₛₗ, ← IsScalarTower.algebraMap_apply] }
  have h1 := GlobalTheory.SlopeExt.slope_sq_sub_le_slope_sq_span K' F V' (Fin n → F) N₁ N₂ φ M B ⟨⟨n, ⟨(b, X), hG₁⟩⟩⟩ hN₂ hc₁
    (coordExt_li F b) hMfg hM0 (fun σ x => by
      rw [hφ]
      refine mul_le_mul_of_nonneg_right ?_ ?_
      · obtain ⟨h1, h2⟩ := hcB (InfinitePlace.mk (σ.comp (algebraMap K' F))).embedding
        rw [← Real.exp_log h1, ← Real.exp_neg]
        exact Real.exp_le_exp.2 ((neg_le_abs _).trans h2)
      · show 0 ≤ N' _ x
        rw [← (hG _).2]; exact Real.sqrt_nonneg _)
  have h2 := GlobalTheory.T.maxSlope_extendedLattice_galois_le K F V (Fin n → F) N N₂ ψ L hN hN₂ hc
    (fun m e he => coordExt_li F b m _ (hli m e he)) hL h0 (fun σ x => by
      show N₂ σ (φ (ι x)) = _
      rw [hφ]
      show _ * N' _ (ι x) = _
      rw [hι, inv_mul_cancel_left₀ (hcB _).1.ne', IsScalarTower.algebraMap_eq K K' F, ← RingHom.comp_assoc]
      rcases InfinitePlace.embedding_mk_eq (σ.comp (algebraMap K' F)) with h | h
      · rw [h]
      · rw [h]; exact hc ((σ.comp (algebraMap K' F)).comp (algebraMap K K')) x)
  have h3 : slope_sq N₂ (Submodule.span (𝓞 F) (φ '' (M : Set V'))) ≤
      slopeMax_sq N₂ (Submodule.span (𝓞 F) (ψ '' (L : Set V))) := by
    refine slope_le_slopeMax hN₂ (fg_span_image ψ hL) (Submodule.span_le.2 ?_)
      (span_image_ne_bot φ (coordExt_li F b) hM0)
    rintro _ ⟨x, hx, rfl⟩
    refine map_mem_of_mem_span φ ?_ (hM hx)
    rintro _ ⟨y, hy, rfl⟩
    exact Submodule.subset_span ⟨y, hy, rfl⟩
  have h4 : slope_sq N₁ M = slope_sq N' M := by rw [slope_sq_eq hG₁ hMfg, slope_sq_eq hG hMfg]
  linarith

end GlobalTheory.SlopeMaxExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemKernelOfCubWeilOrthogonal
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.OrthKer

theorem fibreDescent_transport' {X : Scheme.{0}} {m m' : X ⟶ X} (e : m = m')
    (P : (X ⟶ X) → Prop)
    (H : ∀ (V : X.Opens) (a : Γ(X, m' ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m' ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m' ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m'.app V).hom a' = a) :
    ∀ (V : X.Opens) (a : Γ(X, m ⁻¹ᵁ V)),
      (∀ t, P t → ∀ h : m ⁻¹ᵁ V ≤ t ⁻¹ᵁ (m ⁻¹ᵁ V), (t.appLE _ _ h).hom a = a) →
      ∃! a' : Γ(X, V), (m.app V).hom a' = a := by
  subst e; exact H

open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Chart in

theorem descends_fibre (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsAbelianScheme G)
    (K : Type) [Field K] [IsAlgClosed K] (f : Spec (CommRingCat.of K) ⟶ S) (N : ℕ) (hN : (N : K) ≠ 0)
    (V : (G ⊗ Over.mk f).left.Opens) (a : Γ((G ⊗ Over.mk f).left, (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V))
    (ha : ∀ y : Over.mk f ⟶ G, y ^ N = 1 → ∀ h : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V ≤
      (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left ⁻¹ᵁ
        ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left ⁻¹ᵁ V),
      ((lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left.appLE _ _ h).hom a = a) :
    ∃! a' : Γ((G ⊗ Over.mk f).left, V), ((((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left.app V).hom a' = a := by
  let A : Over (Spec (CommRingCat.of K)) := (Over.pullback f).obj G
  let ρ : ∀ (T : Over (Spec (CommRingCat.of K))) (t : T.left ⟶ S) (ht : T.hom ≫ f = t),
      (T ⟶ A) ≃* (Over.mk t ⟶ G) := fun T t ht => TorsionLift.ptsEquiv f G T t ht
  have hρ : ∀ T t ht x, (ρ T t ht x).left = x.left ≫ Limits.pullback.fst G.hom f :=
    fun T t ht x => TorsionLift.ptsEquiv_left f G T t ht x
  have hA : A.hom ≫ f = (G ⊗ Over.mk f).hom := Limits.pullback.condition.symm
  have hid : ρ A _ hA (𝟙 A) = fst G (Over.mk f) := Over.OverMorphism.ext (by
    rw [hρ]; exact Category.id_comp _)
  have ext : ∀ (u : A ⟶ A) (v : G ⊗ Over.mk f ⟶ G ⊗ Over.mk f),
      v ≫ fst _ _ = ρ A _ hA u → v ≫ snd _ _ = snd _ _ → v.left = u.left := by
    intro u v h1 h2
    apply Limits.pullback.hom_ext
    · exact (congrArg (·.left) h1).trans (hρ _ _ _ _)
    · exact (congrArg (·.left) h2).trans (Over.w u).symm
  have hm : (((𝟙 G) ^ N : G ⟶ G) ▷ Over.mk f).left = ((𝟙 A) ^ N : A ⟶ A).left := by
    refine ext _ _ ?_ (whiskerRight_snd _ _)
    rw [map_pow, hid, whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have hAb : IsAbelianScheme A := TLinPf.isAb_pullback f G hG
  have hu : IsUnit (N : Γ(Spec (CommRingCat.of K), ⊤)) := by
    simpa using (Ne.isUnit hN).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, h3, h1, h2⟩ := abelianScheme_id_pow_finite_etale_surjective _ A N hAb hu
  refine fibreDescent_transport' hm (fun t => ∃ y : Over.mk f ⟶ G, y ^ N = 1 ∧
    t = (lift (fst G (Over.mk f) * (snd G (Over.mk f) ≫ y)) (snd G (Over.mk f))).left) ?_ V a ?_
  · intro V a ha
    refine existsUnique_descend_of_torsion_invariant A N V a fun y hy => ?_
    refine ha _ ⟨ρ (𝟙_ _) f (Category.id_comp _) y, by rw [← map_pow, hy, map_one], ?_⟩
    refine (ext _ _ ?_ (lift_snd _ _)).symm
    rw [lift_fst, map_mul, hid, _root_.mul_comm]
    congr 1
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hρ, hρ, Over.comp_left, Category.assoc]
    rfl
  · rintro _ ⟨y, hy, rfl⟩
    exact ha y hy

theorem mem_kernel_of_cubWeil_orthogonal : ∀ (K : Type) [Field K] [IsAlgClosed K] (S : Scheme.{0}) (p : Sp K ⟶ S) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (L : RigLB B) (c : CubicalStr B L) (N : ℕ), (N : K) ≠ 0 → ∀ x : Over.mk p ⟶ B, x ^ N = 1 → (∀ y : Over.mk p ⟶ B, y ^ N = 1 → CubWeil c N x y 1) → Triv (translDiff B L.L x) := by
  intro K _ _ S t A _ _ hA L c n hn x hx hp
  let T : Over S := Over.mk t
  let m : A ⊗ T ⟶ A ⊗ T := ((𝟙 A) ^ n : A ⟶ A) ▷ T
  have m₁ : m ≫ fst A T = fst A T ^ n := by
    rw [whiskerRight_fst, MonObj.comp_pow, Category.comp_id]
  have m₂ : m ≫ snd A T ≫ x = snd A T ≫ x := by rw [whiskerRight_snd_assoc]
  let ψ : Fin 4 → ((A ⊗ T).left ⟶ A.left) :=
    ![(fst A T * (snd A T ≫ x)).left, (fst A T).left, (snd A T ≫ x).left, (1 : A ⊗ T ⟶ A).left]
  obtain ⟨σ, hσ, hv⟩ := CubNondeg.exists_sigma c n (fst A T) (snd A T ≫ x)
    (by rw [← MonObj.comp_pow, hx, MonObj.comp_one]) (fun k => m.left ≫ ψ k) (by
      funext k
      fin_cases k
      · show (m ≫ (fst A T * (snd A T ≫ x))).left = (fst A T ^ n * (snd A T ≫ x)).left
        rw [MonObj.comp_mul, m₁, m₂]
      · exact congrArg (fun q => q.left) m₁
      · exact congrArg (fun q => q.left) m₂
      · exact congrArg (fun q : A ⊗ T ⟶ A => q.left) (MonObj.comp_one m))
  obtain ⟨u, hu⟩ := CubNondeg.descend_linComb m.left (T := {y : T ⟶ A // y ^ n = 1})
    (fun y => (lift (fst A T * (snd A T ≫ y.1)) (snd A T)).left) (fun y => by
      rw [← Over.comp_left]
      congr 1
      ext1
      · rw [Category.assoc, m₁, MonObj.comp_pow, lift_fst, mul_pow, ← MonObj.comp_pow, y.2, MonObj.comp_one,
          _root_.mul_one]
      · simp [m])
    (fun V a ha => descends_fibre S A hA K t n hn V a (fun y hy => ha ⟨y, hy⟩)) L.L L.isLB ψ _ σ hσ
    (fun y z J hJ => by
      have e₁ := hv _ (lift (fst A T * (snd A T ≫ y.1)) (snd A T)) z J hJ
      have e₂ := hv _ (𝟙 (A ⊗ T)) z J hJ
      rw [lift_fst, lift_snd_assoc] at e₁
      rw [Category.id_comp, Category.id_comp] at e₂
      have w := (hp y.1 y.2).comp (snd A T)
      have w' := w.2.2 z J hJ
      rw [map_one, map_one, _root_.one_mul] at w'
      exact e₁.trans ((CubNondeg.ratio_translate (isCub_cubV c hJ) n _ _ _ w.1 w.2.1 w').trans e₂.symm))
  obtain ⟨g, hg⟩ := DVR.exists_gen_of_local (V := K) L.L L.isLB (![x.left, (1 : T ⟶ A).left] : Fin 2 → _) ![1, -1]
  let s : T ⊗ A ⟶ A ⊗ T := lift (snd T A) (fst T A)
  have s₀ : s.left ≫ ψ 0 = (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left := by
    show (s ≫ (fst A T * (snd A T ≫ x))).left = ((fst T A ≫ x) * snd T A).left
    rw [MonObj.comp_mul, lift_fst, lift_snd_assoc, mul_comm]
  have s₁ : s.left ≫ ψ 1 = (snd T A).left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_fst _ _)
  have s₂ : s.left ≫ ψ 2 = (fst T A).left ≫ x.left := congrArg (fun q : T ⊗ A ⟶ A => q.left) (lift_snd_assoc _ _ x)
  have s₃ : s.left ≫ ψ 3 = (fst T A).left ≫ (1 : T ⟶ A).left :=
    congrArg (fun q : T ⊗ A ⟶ A => q.left) ((MonObj.comp_one s).trans (MonObj.comp_one (fst T A)).symm)
  obtain ⟨w, hw, -⟩ := exists_gen L.isLB
    (φ' := (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _)) (ε' := ![1, -1])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two]
      show h (s.left ≫ ψ 0) ^ (1 : ℤ) * h (s.left ≫ ψ 1) ^ (-1 : ℤ) * h (s.left ≫ ψ 2) ^ (-1 : ℤ) *
        h (s.left ≫ ψ 3) ^ (1 : ℤ) * (h ((fst T A).left ≫ x.left) ^ (1 : ℤ) *
        h ((fst T A).left ≫ (1 : T ⟶ A).left) ^ (-1 : ℤ)) =
        h (lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left ^ (1 : ℤ) * h (snd T A).left ^ (-1 : ℤ)
      rw [s₀, s₁, s₂, s₃]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ u s.left) (LB.pullGen L.L _ _ g (fst T A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hg _))
  exact ⟨w, hw⟩

end GlobalTheory.OrthKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalBasisBlockVacuumLatticeBasisFamilyStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.BaseVacuum
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orthonormalBasis_blockVacuumLatticeBasisFamily : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (n n' : ℕ), StandardLatticesGL3.OnB D (bas B n n') := by
  first | exact @GlobalTheory.BaseVacuum.onB_bas | exact GlobalTheory.BaseVacuum.onB_bas | (intros; apply GlobalTheory.BaseVacuum.onB_bas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceIdempotentComponentsConjValuationStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Links Formalism.L2.JoinChr Formalism.L2.Host
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placeIdempotent_components_conj_valuation : ∀ (D : D7) (ι : (Af D.host.F ⊗[D.host.F] D.host.E) ≃+* FiniteAdeleRing (𝓞 D.host.E) D.host.E), (∀ x : D.host.E, ι ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) = algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x) → (∀ y, y ∈ intAE D ↔ ∀ P : HeightOneSpectrum (𝓞 D.host.E), Valued.v (ι y P) ≤ 1) → (∀ P : HeightOneSpectrum (𝓞 D.host.E), ∃ e : AE D, IsPlIdem D e P ∧ infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) → (∀ (e : AE D) (P : HeightOneSpectrum (𝓞 D.host.E)), Formalism.L2.NTheta.IsIdemAt e P → infPart D e = 0 ∧ ι (finPart D e) P = 1 ∧ ∀ P' : HeightOneSpectrum (𝓞 D.host.E), P' ≠ P → ι (finPart D e) P' = 0) ∧ ∀ (z : AE D) (Q : HeightOneSpectrum (𝓞 D.host.E)), Valued.v (ι (finPart D (cA D z)) (GlobalTheory.IdemSupport.cP Q)) = Valued.v (ι (finPart D z) Q) := by
  first | exact @GlobalTheory.ConjVal.components_and_conj_valuation | exact GlobalTheory.ConjVal.components_and_conj_valuation | (intros; apply GlobalTheory.ConjVal.components_and_conj_valuation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresPowEightMul
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem sqProd_pow_eight_mul (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ)
    (hp : p.Prime) (h4 : p % 4 = 3) (h3 : 3 < p) (hD : Datum p F L t) :
    sqProd p L t ^ 8 * (p : ℂ) ^ 6 = (latticeCurve L).Δ ^ (p - 1) := by
  obtain ⟨hmul, -, hrep⟩ := GlobalTheory.T.sqrtNegPrime_kernel_cyclic p F L t hp h4 h3 hD
  have ht0 : t ≠ 0 := by
    rintro rfl; exact hD.notMem (zero_mem _)
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hα2 : sqrtNegNat p ^ 2 = -(p : ℂ) := by
    simp only [sqrtNegNat, mul_pow, Complex.I_sq]
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p)]
    push_cast; ring
  have hα0 : sqrtNegNat p ≠ 0 := by
    intro h; apply hp0; have := hα2; rw [h] at this; simp at this; exact_mod_cast this
  have hα12 : sqrtNegNat p ^ 12 = (p : ℂ) ^ 6 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, pow_mul, hα2]; ring
  have hinj : Set.InjOn (fun k : ℕ => (k : ℂ) * t) (Finset.Ico 1 p : Set ℕ) := by
    intro a _ b _ hab
    exact_mod_cast mul_right_cancel₀ ht0 hab
  set S := (Finset.Ico 1 p).image fun k : ℕ => (k : ℂ) * t with hS
  have hcard : S.card = p - 1 := by
    rw [hS, Finset.card_image_of_injOn hinj, Nat.card_Ico]
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have heven : Even S.card := by
    rw [hcard]; obtain ⟨m, hm⟩ := hodd; exact ⟨m, by omega⟩
  have hpf := GlobalTheory.T.prod_derivWeierstrassP_kerReps_pow_four_mul' L (sqrtNegNat p) S hα0 hD.mul hrep heven
  rw [hcard, hα12] at hpf
  rw [← hpf]
  congr 1

  have hprod : ∏ x ∈ S, L.derivWeierstrassP x
      = ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t) := by
    rw [hS, Finset.prod_image hinj]
  obtain ⟨e, he⟩ := GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four p hp h4
  have hpt : (p : ℂ) * t ∈ L.lattice := by
    have := (hmul (p : ℤ)).2 dvd_rfl
    simpa using this
  have hsplit : ∏ k ∈ Finset.Ico 1 p, L.derivWeierstrassP ((k : ℂ) * t)
      = ∏ s : Sq p ⊕ Sq p, L.derivWeierstrassP (((e s : ℕ) : ℂ) * t) := by
    rw [← Finset.prod_coe_sort]
    exact (Fintype.prod_equiv e _ _ (fun _ => rfl)).symm
  have hneg : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inr k) : ℕ) : ℂ) * t)
      = -L.derivWeierstrassP (sqPt p t k) := by
    intro k
    rw [(he k).2, Nat.cast_sub (le_of_lt k.1.2), sub_mul, sqPt]
    have := L.derivWeierstrassP_add_coe (-((k.1 : ℕ) : ℂ) * t) ⟨_, hpt⟩
    simp only at this
    rw [show (p : ℂ) * t - ((k.1 : ℕ) : ℂ) * t = -((k.1 : ℕ) : ℂ) * t + (p : ℂ) * t by ring, this,
      neg_mul, L.derivWeierstrassP_neg]
  have hpos : ∀ k : Sq p, L.derivWeierstrassP (((e (Sum.inl k) : ℕ) : ℂ) * t)
      = L.derivWeierstrassP (sqPt p t k) := by
    intro k; rw [(he k).1, sqPt]
  rw [hprod, hsplit, Fintype.prod_sum_type]
  simp only [hneg, hpos, Finset.prod_neg]
  have h1 : ((-1 : ℂ) ^ (Finset.univ : Finset (Sq p)).card) ^ 4 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  rw [sqProd, mul_pow, mul_pow, h1]
  ring

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdDerivWeierstrassPOverSquaresSqMemStable
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

theorem GlobalTheory.CMModel.sqProd_sq_mem_and_stable : ∀ (p : ℕ) (F : IntermediateField ℚ ℂ) (L : PeriodPair) (t : ℂ),
    p.Prime → p % 4 = 3 → 3 < p → Datum p F L t →
    sqProd p L t ^ 2 ∈ F ∧ (sqProd p L t ∈ F → Stable L F (sqPt p t)) := by
  intro p F L t hp h4 h3 hD
  refine ⟨?_, ?_⟩
  · apply GlobalTheory.T.mem_intermediateField_of_forall_complexAut_fixed F
    intro σ hσ
    rw [map_pow]
    rcases GlobalTheory.T.prodDerivWeierstrassPOverSquares_conj p F L t hp h4 h3 hD σ hσ with ⟨h, _⟩ | h
    · rw [h]
    · rw [h, neg_sq]
  · intro hmem σ hσ
    rcases GlobalTheory.T.prodDerivWeierstrassPOverSquares_conj p F L t hp h4 h3 hD σ hσ with ⟨_, he⟩ | h
    · exact he
    · exfalso
      have hne := (GlobalTheory.T.prodDerivWeierstrassPOverSquares_ne_zero p F L t hp h4 h3 hD).2
      have hfix : σ (sqProd p L t) = sqProd p L t := hσ _ hmem
      rw [hfix] at h
      have h2 : (2 : ℂ) * sqProd p L t = 0 := by linear_combination h
      rcases mul_eq_zero.mp h2 with h2 | h2
      · norm_num at h2
      · exact hne h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureEndomorphismHomLiftSquareZeroStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_endomorphism_hom_lift_square_zero : GlobalTheory.Published.GrothendieckMessing → ∀ p : ℕ, p.Prime → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), IsNilpotent (p : R) → Function.Surjective π → RingHom.ker π ^ 2 = ⊥ → ∀ (g g' : ℕ) (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (A₀ B₀ : Over (Sp R₀)) [GrpObj A₀] [GrpObj B₀] (i : A₀.left ⟶ A.left) (j : B₀.left ⟶ B.left), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → IsAbelianScheme B → SmoothOfRelativeDimension g' B.hom → IsGrpPullback A₀ A (spMap π) i → IsGrpPullback B₀ B (spMap π) j → ∀ (U : A ⟶ A) (V : B ⟶ B) (U₀ : A₀ ⟶ A₀) (V₀ : B₀ ⟶ B₀) [IsMonHom U] [IsMonHom V] [IsMonHom U₀] [IsMonHom V₀], i ≫ U.left = U₀.left ≫ i → j ≫ V.left = V₀.left ≫ j → ∀ r s r' s' : R, IsPure A U r s → IsPure B V r' s' → IsUnit (r - s') → ∀ (f₀ : A₀ ⟶ B₀) [IsMonHom f₀], U₀ ≫ f₀ = f₀ ≫ V₀ → ∃ f : A ⟶ B, IsMonHom f ∧ i ≫ f.left = f₀.left ≫ j ∧ U ≫ f = f ≫ V ∧ ∀ f' : A ⟶ B, IsMonHom f' → i ≫ f'.left = f₀.left ≫ j → f' = f := by
  first | exact @GlobalTheory.pureLift_step | exact GlobalTheory.pureLift_step | (intros; apply GlobalTheory.pureLift_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShintaniFormulaStatement
section
open NumberField IsDedekindDomain Formalism.UG GlobalTheory.PRep GlobalTheory.LFun
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shintani_formula_alt : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x : w.adicCompletion E, (∀ y ∈ Ov E w, ψ (x * y) = 1) ↔ x ∈ Ov E w) → ∀ (W : GL (Fin n) (w.adicCompletion E) → ℂ) (α : Fin n → ℂˣ), (∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin n), ∀ g, W (u * g) = ψ (GlobalTheory.Whittaker.superDiag u) * W g) → (∀ g, ∀ k ∈ KGL w n, W (g * k) = W g) → (∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ n, heckeVec (rightReg ℂ (GL (Fin n) (w.adicCompletion E)) ℂ) (KGL w n) (Tj ℂ n (Ov E w) ϖ j) W = satEig (qV E w) n (Finset.univ.val.map α) j • W) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ l : Fin n → ℕ, W (Units.map (Matrix.diagonalRingHom (Fin n) (w.adicCompletion E)).toMonoidHom (MulEquiv.piUnits.symm fun i => ϖ ^ l i)) = GlobalTheory.JSW.sphW (qV E w) (fun i => (α i : ℂ)) l * W 1 := by
  first | exact @GlobalTheory.JSW.shintani_formula | exact GlobalTheory.JSW.shintani_formula | (intros; apply GlobalTheory.JSW.shintani_formula <;> assumption)
end

