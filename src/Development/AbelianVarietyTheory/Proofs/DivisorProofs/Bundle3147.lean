import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3102
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinFreeAwayOfFinitePresentation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2933
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3127
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2917
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3126
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2999

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDualHeightOneAdjoinPrimitiveEqTop
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.HeightOneDual

variable {K H : Type} [Field K] [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H]

theorem cobOne_toConv_eq_zero {δ : H →ₗ[K] K} (hδ : ReciprocityTheory.PGsh.IsPtDer δ) :
    cobOne K (CartierDual K H) (WithConv.toConv δ) = 0 := by
  rw [cobOne_apply, sub_sub, sub_eq_zero, CartierDual.comul_eq_iff]
  intro a b
  rw [map_add, LinearMap.add_apply, CartierDual.pair_tmul_tmul, CartierDual.pair_tmul_tmul,
    CartierDual.one_apply, CartierDual.one_apply]
  change _ = δ (a * b)
  rw [hδ a b]
  change δ a * counit b + counit a * δ b = _
  ring

theorem apply_convD (φ : CartierDual K H) (δ : H →ₗ[K] K) (y : H) :
    φ (ReciprocityTheory.PGsh.convD δ y) = (φ * WithConv.toConv δ) y := by
  rw [CartierDual.mul_apply, CartierDual.pair_tmul]
  simp only [ReciprocityTheory.PGsh.convD, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  generalize comul (R := K) y = t
  induction t with
  | zero => simp
  | add u v hu hv => simp only [map_add, hu, hv]
  | tmul a b => simp [mul_comm]

theorem adjoin_primitive_eq_top : ∀ (p : ℕ) [Fact p.Prime] (K H : Type) [Field K] [CharP K p]
    [CommRing H] [HopfAlgebra K H] [IsCocomm K H] [Module.Finite K H],
    (∀ a ∈ augIdeal K H, a ^ p = 0) →
    Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} = ⊤ := by
  intro p hp K H _ _ _ _ _ _ hpow
  classical
  set ε := counitAlgHom K H with hεdef
  set S := Algebra.adjoin K {φ : CartierDual K H | cobOne K (CartierDual K H) φ = 0} with hSdef
  haveI : Module.Finite K (AugCot ε) := Module.Finite.of_surjective _ (AugCot.d_surjective ε)
  let b := Module.finBasis K (AugCot ε)
  choose x hx using fun i => (RingHom.ker ε).toCotangent_surjective (b i)
  let y : Fin (Module.finrank K (AugCot ε)) → H := fun i => (x i : H)
  have hy : ∀ i, y i ∈ RingHom.ker ε := fun i => (x i).2
  have hsum : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      AugCot.d ε (∑ i, l i • y i) = ∑ i, l i • b i := by
    intro l
    simp [y, map_sum, hx]
  have hmem : ∀ l : Fin (Module.finrank K (AugCot ε)) → K, (∑ i, l i • y i) ∈ RingHom.ker ε := by
    intro l
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left _ _ (hy i)
  have hspan : ∀ z ∈ RingHom.ker ε, ∃ l : Fin (Module.finrank K (AugCot ε)) → K,
      z - ∑ i, l i • y i ∈ RingHom.ker ε ^ 2 := by
    intro z hz
    refine ⟨b.repr (AugCot.d ε z), ?_⟩
    have h1 : AugCot.d ε (z - ∑ i, b.repr (AugCot.d ε z) i • y i) = 0 := by
      rw [map_sub, hsum, b.sum_repr, sub_self]
    rwa [AugCot.d_of_mem _ (sub_mem hz (hmem _)), Ideal.toCotangent_eq_zero] at h1
  have hind : ∀ l : Fin (Module.finrank K (AugCot ε)) → K,
      ∑ i, l i • y i ∈ RingHom.ker ε ^ 2 → l = 0 := by
    intro l hl
    have h1 : AugCot.d ε (∑ i, l i • y i) = 0 := by
      rw [AugCot.d_of_mem _ (hmem _), Ideal.toCotangent_eq_zero]
      exact hl
    rw [hsum] at h1
    funext i
    exact Fintype.linearIndependent_iff.1 b.linearIndependent l h1 i
  have : IsNoetherianRing H := isNoetherian_of_tower K inferInstance
  have hnil : IsNilpotent (RingHom.ker ε) := by
    rw [Ideal.FG.isNilpotent_iff_le_nilradical (IsNoetherian.noetherian _)]
    intro f hf
    exact ⟨p, hpow f hf⟩
  have hsurj := GlobalTheory.HeightOneHopf.aeval_surjective_of_span_cotangent ε hnil y hy hspan
  obtain ⟨δ, hδ, hδx⟩ := GlobalTheory.HeightOneHopf.exists_isPtDer_dual y hy hind

  let Z : Set H := {h | ∀ φ ∈ S, φ h = 0}
  have hZε : ∀ h ∈ Z, ε h = 0 := fun h hh => by
    have h1 := hh 1 S.one_mem
    rwa [CartierDual.one_apply] at h1
  have hZD : ∀ i, ∀ h ∈ Z, ReciprocityTheory.PGsh.convD (δ i) h ∈ Z := fun i h hh φ hφ => by
    rw [apply_convD]
    exact hh _ (S.mul_mem hφ (Algebra.subset_adjoin (cobOne_toConv_eq_zero (hδ i))))
  have hZ0 : ∀ h ∈ Z, h = 0 := by
    intro h hh
    obtain ⟨P, rfl⟩ := hsurj h
    have hc := ReciprocityTheory.PGsh.coeff_eq_zero_of_stable ε y hy (fun i => ReciprocityTheory.PGsh.convD (δ i))
      (fun i => ReciprocityTheory.PGsh.convD_mul _ (hδ i)) (fun i j =>
        (ReciprocityTheory.PGsh.counit_convD (δ i) (y j)).trans (hδx i j)) hsurj
      (CharP.cast_eq_zero K p) (fun n h0 hn => by
        rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff K p]
        exact Nat.not_dvd_of_pos_of_lt h0 hn) Z hZε hZD P hh
    exact ReciprocityTheory.PGsh.aeval_eq_zero_of_mem_span y (fun j => hpow _ (hy j))
      (ReciprocityTheory.PGsh.mem_span_pow_of_coeff hc)

  let W : Submodule K (Module.Dual K H) :=
    (Subalgebra.toSubmodule S).map (CartierDual.toDual K H).toLinearMap
  have hW : W.dualCoannihilator = ⊥ := by
    refine eq_bot_iff.2 fun h hh => ?_
    rw [Submodule.mem_dualCoannihilator] at hh
    rw [Submodule.mem_bot]
    exact hZ0 h fun φ hφ => hh _ ⟨φ, hφ, rfl⟩
  have hWtop : W = ⊤ := by
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := W), hW, Submodule.dualAnnihilator_bot]
  rw [← Algebra.toSubmodule_eq_top, eq_top_iff]
  intro φ _
  have h1 : CartierDual.toDual K H φ ∈ W := hWtop ▸ Submodule.mem_top
  obtain ⟨ψ, hψ, e⟩ := h1
  rwa [(CartierDual.toDual K H).injective e] at hψ

end GlobalTheory.HeightOneDual
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNonvanishingInvMixPairKunnethIsogeny
section
set_option autoImplicit false

noncomputable section

section Lemmas
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleGen

open GlobalTheory.CechPic in

theorem cls_tw_one {X : Scheme.{0}} {M H : LB X} (hM : M.IsLB) (hH : H.IsLB) :
    cls (GlobalTheory.AbLaw.tw M H 1) (GlobalTheory.AbLaw.isLB_tw hM hH 1) = cls M hM + cls H hH := by
  refine (cls_div (A := M) (B := GlobalTheory.AbLaw.pw H (-1)) hM (GlobalTheory.AbLaw.isLB_pw hH _) (GlobalTheory.AbLaw.isLB_tw hM hH 1)).trans ?_
  rw [GlobalTheory.AmpleStabFinite.cls_pw hH]
  simp

open GlobalTheory.CechPic in

theorem cls_mix_pull {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] {L : LB A.left} (hL : L.IsLB)
    {T : Over (Sp K)} (z : T ⟶ A) (a b : ℤ) :
    cls ((mix A L a b).pull z.left) (LB.isLB_pull (LB.isLB_linComb hL _ _) _) =
      a • pull z.left (cls L hL) + b • pull (z⁻¹).left (cls L hL) := by
  refine (cls_pull (L := LB.LinComb L ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![a, b])
    (LB.isLB_linComb hL _ _) _ _).trans ?_
  rw [cls_linComb hL, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, map_add, map_zsmul, pull_id, ← pull_comp,
    ← Over.comp_left, Hom.inv_def]

end GlobalTheory.AmpleGen
end Lemmas

section RowLatticeBoundForBasis
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AmpleGen
open GlobalTheory.CechPic in

theorem lbIso_pull_psiMap {K : Type} [Field K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (a₁ b₁ a₂ b₂ : ℤ) (hs : a₁ * b₁ + a₂ * b₂ = 0) {L : LB A.left} (hL : L.IsLB) (a b : ℤ) :
    LBIso ((GlobalTheory.AbLaw.tw ((mix A L a b).pull (fst A A).left) ((mix A L a b).pull (snd A A).left) 1).pull
        (psiMap A a₁ b₁ a₂ b₂).left)
      (GlobalTheory.AbLaw.tw ((mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
                   (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂)).pull (fst A A).left)
        ((mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
          (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂)).pull (snd A A).left) 1) := by
  haveI := hA.comm
  have hP' : ∀ a b : ℤ, (mix A L a b).IsLB := fun _ _ => LB.isLB_linComb hL _ _
  have h₁ := GlobalTheory.AbLaw.isLB_tw (LB.isLB_pull (hP' a b) (fst A A).left) (LB.isLB_pull (hP' a b) (snd A A).left) 1
  refine (cls_eq_iff (LB.isLB_pull h₁ _) (GlobalTheory.AbLaw.isLB_tw (LB.isLB_pull (hP' _ _) _)
    (LB.isLB_pull (hP' _ _) _) 1)).1 ?_
  rw [cls_pull h₁, cls_tw_one, cls_tw_one, cls_mix_pull A hL, cls_mix_pull A hL, cls_mix_pull A hL,
    cls_mix_pull A hL]
  simp only [map_add, map_zsmul, ← pull_comp, ← Over.comp_left, GrpObj.comp_inv, psiMap, lift_fst, lift_snd]
  set c := cls L hL
  set x := fst A A
  set y := snd A A
  have e₁ := GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split K A hA L hL _ x y a₁ b₁ a b
  have e₂ := GlobalTheory.T.cechPicardPullback_zpow_mul_mixed_split K A hA L hL _ x y a₂ b₂ a b
  have f (z : A ⊗ A ⟶ A) (n : ℤ) := GlobalTheory.T.cechPicardPullback_zpow_eq_mumford_formula K A hA L hL _ z n
  have g (z : A ⊗ A ⟶ A) (n : ℤ) : pull ((z ^ n)⁻¹).left c = tri (-n) • pull z.left c + tri n • pull (z⁻¹).left c := by
    rw [← zpow_neg, f, neg_neg]
  rw [e₁, e₂, f x a₁, g x a₁, f x a₂, g x a₂, f y b₁, g y b₁, f y b₂, g y b₂]
  have hl : ((a + b) * (a₁ * b₁)) • lam c x y + ((a + b) * (a₂ * b₂)) • lam c x y = 0 := by
    rw [← add_smul, ← mul_add, hs, mul_zero, zero_smul]
  linear_combination (norm := module) hl
  all_goals exact LB.isLB_pull (hP' _ _) _
end GlobalTheory.AmpleGen
end RowLatticeBoundForBasis

section MainAux
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen GlobalTheory.AbLaw
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.AmpleGen

theorem finrank_pos_of_not_exactAt {K : Type} [Field K] {X : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of K)}
    {M : LB X} {κ : Type} [LinearOrder κ] {D : κ → X.Opens} {n : ℕ}
    [Module.Finite K ((cechLB f M D).homology n)] (h : ¬ (cechLB f M D).ExactAt n) :
    0 < Module.finrank K ((cechLB f M D).homology n) := by
  have : Nontrivial ((cechLB f M D).homology n) := by
    by_contra hn
    rw [not_nontrivial_iff_subsingleton] at hn
    exact h ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (ModuleCat.isZero_of_subsingleton _))
  exact Module.finrank_pos

theorem exists_nonvanishing_invMix_pair_isogeny (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A] (hA : IsAbelianScheme A)
    (a₁ b₁ a₂ b₂ : ℤ) (hs : a₁ * b₁ + a₂ * b₂ = 0) (hd : ((a₁ * b₂ - b₁ * a₂ : ℤ) : K) ≠ 0)
    (L : LB A.left) (hL : L.IsLB) (a b j : ℕ) (hN : NV A (mix A L a b) j) :
    ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧
      NV A (mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
        (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂)) j₁ ∧
      NV A (mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
        (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂)) j₂ := by
  haveI := hA.comm
  haveI := hA.proper
  obtain ⟨κ, _, _, W, hW, hWc, hne⟩ := hN
  have hP' : ∀ a b : ℤ, (mix A L a b).IsLB := fun _ _ => LB.isLB_linComb hL _ _
  have hsep : IsSeparated A.hom := inferInstance
  have hproj := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K A hA
  have fin : ∀ M : LB A.left, M.IsLB → ∀ n, Module.Finite K ((cechLB A.hom M W).homology n) :=
    fun M hM => cechLB_homology_finite_of_affine_cover K _ A.hom M κ W hM hsep hproj hW hWc
  have h₀ : IsPullback (fst A A).left (snd A A).left A.hom A.hom := IsPullback.of_hasPullback A.hom A.hom
  have hAA := ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  haveI := hAA.comm
  haveI := hAA.proper
  have hsepAA : IsSeparated (A ⊗ A).hom := inferInstance
  have hprojAA := GlobalTheory.AbelianProjective.isProjBy_of_isAbelianScheme K (A ⊗ A) hAA
  haveI : CompactSpace (A ⊗ A).left := QuasiCompact.compactSpace_of_compactSpace (A ⊗ A).hom
  obtain ⟨k, E, hE, hEc⟩ := GlobalTheory.PicZeroVan.exists_fin_affine_cover (A ⊗ A).left
  obtain ⟨hfin, hflat, hlfp, r, hr, hr0⟩ := GlobalTheory.T.abelianVarietySquareLinearEndomorphism_finiteLocallyFree K A hA a₁ b₁ a₂ b₂ hd
  set ψ := psiMap A a₁ b₁ a₂ b₂ with hψ
  set P := mix A L a b with hPdef
  have hP := hP' a b
  have hf₁ : (fst A A).left ≫ A.hom = (A ⊗ A).hom := Over.w (fst A A)
  have hfψ : ψ.left ≫ (A ⊗ A).hom = (A ⊗ A).hom := Over.w ψ

  have k₀ := finrank_cechLB_homology_extProd K _ _ _ A.hom A.hom (fst A A).left (snd A A).left P P h₀ hP hP
    hsep hsep κ W κ W (Fin k) E hW hWc hW hWc hE hEc (fin P hP) (fin P hP) (2 * j)
  have hpos : 0 < Module.finrank K ((cechLB A.hom P W).homology j) := by
    haveI := fin P hP j
    exact finrank_pos_of_not_exactAt hne
  have hM : ¬ (cechLB ((fst A A).left ≫ A.hom) (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).ExactAt
      (2 * j) := by
    intro hex
    have hz : Module.finrank K ((cechLB ((fst A A).left ≫ A.hom)
        (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).homology (2 * j)) = 0 := by
      have : Subsingleton ((cechLB ((fst A A).left ≫ A.hom)
          (tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1) E).homology (2 * j)) :=
        ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 hex)
      exact Module.finrank_zero_of_subsingleton
    rw [k₀] at hz
    have := (Finset.sum_eq_zero_iff.1 hz) (j, j) (by simp [two_mul])
    exact (Nat.mul_pos hpos hpos).ne' this

  have hu : IsUnit ((r : ℕ) : Γ((A ⊗ A).left, ⊤)) := by
    have := (GlobalTheory.AbelianMulFin.isUnit_natCast_Sp (K := K) hr0).map (A ⊗ A).hom.appTop.hom
    rwa [map_natCast] at this
  rw [hf₁] at hM
  have hM' : ¬ (cechLB (ψ.left ≫ (A ⊗ A).hom)
      ((tw (P.pull (fst A A).left) (P.pull (snd A A).left) 1).pull ψ.left) (fun i => ψ.left ⁻¹ᵁ E i)).ExactAt
      (2 * j) := fun h => hM ((GlobalTheory.FinTrace.cechLB_retract_and_exactAt ψ.left (A ⊗ A).hom r hr hu _ E).2 _ h)
  rw [hfψ] at hM'
  set P₁ := mix A L (a * tri a₁ + b * tri (-a₁) + a * tri a₂ + b * tri (-a₂))
        (a * tri (-a₁) + b * tri a₁ + a * tri (-a₂) + b * tri a₂) with hP₁def
  set P₂ := mix A L (a * tri b₁ + b * tri (-b₁) + a * tri b₂ + b * tri (-b₂))
        (a * tri (-b₁) + b * tri b₁ + a * tri (-b₂) + b * tri b₂) with hP₂def
  have hP₁ : P₁.IsLB := hP' _ _
  obtain ⟨w, hw⟩ := lbIso_pull_psiMap A hA a₁ b₁ a₂ b₂ hs hL a b
  have hP₂ : P₂.IsLB := hP' _ _
  have hTw : (tw (P₁.pull (fst A A).left) (P₂.pull (snd A A).left) 1).IsLB :=
    isLB_tw (LB.isLB_pull hP₁ _) (LB.isLB_pull hP₂ _) 1
  have hN₂ : ¬ (cechLB (A ⊗ A).hom (tw (P₁.pull (fst A A).left) (P₂.pull (snd A A).left) 1)
      (fun i => ψ.left ⁻¹ᵁ E i)).ExactAt (2 * j) := fun h =>
    hM' (h.of_iso (cechLBCongr _ _ (LB.isLB_pull (isLB_tw (LB.isLB_pull hP _) (LB.isLB_pull hP _) 1) _)
      hTw w hw).symm)

  have hD : ∀ i, IsAffineOpen (ψ.left ⁻¹ᵁ E i) := fun i => (hE i).preimage ψ.left
  have hDc : ⨆ i, ψ.left ⁻¹ᵁ E i = ⊤ := by
    rw [← Scheme.Hom.preimage_iSup, hEc]; rfl
  have k₁ := finrank_cechLB_homology_extProd K _ _ _ A.hom A.hom (fst A A).left (snd A A).left P₁ P₂ h₀ hP₁ hP₂
    hsep hsep κ W κ W (Fin k) (fun i => ψ.left ⁻¹ᵁ E i) hW hWc hW hWc hD hDc (fin P₁ hP₁) (fin P₂ hP₂) (2 * j)
  rw [hf₁] at k₁
  haveI := cechLB_homology_finite_of_affine_cover K _ (A ⊗ A).hom _ (Fin k) (fun i => ψ.left ⁻¹ᵁ E i) hTw hsepAA
    hprojAA hD hDc (2 * j)
  have hpos₂ := finrank_pos_of_not_exactAt hN₂
  rw [k₁] at hpos₂
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos₂.ne'
  have hx' : x.1 + x.2 = 2 * j := by simpa using hx
  refine ⟨x.1, x.2, hx', ⟨κ, inferInstance, inferInstance, W, hW, hWc, fun h => hx0 ?_⟩,
    ⟨κ, inferInstance, inferInstance, W, hW, hWc, fun h => hx0 ?_⟩⟩
  · haveI := fin P₁ hP₁ x.1
    have : Subsingleton ((cechLB A.hom P₁ W).homology x.1) :=
      ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h)
    rw [Module.finrank_zero_of_subsingleton, zero_mul]
  · haveI := fin P₂ hP₂ x.2
    have : Subsingleton ((cechLB A.hom P₂ W).homology x.2) :=
      ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 h)
    rw [Module.finrank_zero_of_subsingleton (R := K) (M := (cechLB A.hom P₂ W).homology x.2), mul_zero]

end GlobalTheory.AmpleGen
end MainAux

section Target
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AmpleGen
open scoped CategoryTheory.Obj

theorem GlobalTheory.AmpleGen.nv_mix_pair_of_nv : ∀ (K : Type) [Field K] [IsAlgClosed K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ α β γ δ : ℤ, α * β + γ * δ = 0 → ((α * δ - β * γ : ℤ) : K) ≠ 0 → ∀ L : LB A.left, L.IsLB → ∀ a b j : ℕ, NV A (mix A L a b) j → ∃ j₁ j₂ : ℕ, j₁ + j₂ = 2 * j ∧ NV A (mix A L (a * tri α + b * tri (-α) + a * tri γ + b * tri (-γ)) (a * tri (-α) + b * tri α + a * tri (-γ) + b * tri γ)) j₁ ∧ NV A (mix A L (a * tri β + b * tri (-β) + a * tri δ + b * tri (-δ)) (a * tri (-β) + b * tri β + a * tri (-δ) + b * tri δ)) j₂ := by
  intro K _ _ A _ hA α β γ δ hs hd L hL a b j h
  exact exists_nonvanishing_invMix_pair_isogeny K A hA α β γ δ hs hd L hL a b j h

end Target
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreConstPreconnected
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.GFib

theorem latAt_const_on_fibre : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (Y : RatModel o Ω) (G : Over Y.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (Z : Scheme.{0}) (q : Y.Z ⟶ Z) (z : Z), _root_.IsPreconnected (q.base ⁻¹' {z}) → (∃ r₀ : ℕ, ∀ w, q.base w = z → RkAt G w r₀) → ∀ (I T : Type) (f : I → (G ⟶ G)), (∀ e, IsMonHom (f e)) → ∀ (gγ : T → (Over.mk Y.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → ζ ^ L = 1 → IsUnit (L : o) → (∀ t, gγ t ^ L = 1) → (∀ t w, q.base w = z → ExtNear (gγ t) w) → ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (m : I → X →+ X) (c : T → X →+ ZMod L) (w w' : Y.Z), q.base w = z → q.base w' = z → LatAt f gγ ζ L m c w → LatAt f gγ ζ L m c w' := by
  intro o Ω _ _ _ _ Y G _ _ hG Z q z hpre hrk I T f hf gγ ζ L hL hζ hu hγ hext X _ _ _ m c w w' hw hw'
  obtain ⟨r₀, hr⟩ := hrk
  haveI : IsNoetherianRing o := by
    haveI := ArithBase.ded (o := o) (Ω := Ω)
    infer_instance
  haveI := Y.lft
  haveI := Y.qc
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.Z := QuasiCompact.compactSpace_of_compactSpace Y.s
  haveI : IsNoetherian Y.Z := {}
  exact GlobalTheory.fibre_const_of_specializes_invariant Y.Z Z q.base q.continuous z hpre
    (fun v => LatAt f gγ ζ L m c v)
    (fun a b ha hb hab => latAt_iff_of_specializes hG hL hζ hu hf hγ m c hab (hr a ha) (hr b hb)
      (fun t => hext t b hb)) w w' hw hw'

end GlobalTheory.UPoinc.GFib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLatticeAtFibreUniqueUpToIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.FibLat
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.GFibUniq

theorem isPrimitiveRoot_map {o : Type} [CommRing o] [IsDomain o] {ζ : o} {L : ℕ} (hL : 0 < L)
    (hζ : IsPrimitiveRoot ζ L) (hu : IsUnit (L : o)) (κ : Type) [Field κ] (a : o →+* κ) : IsPrimitiveRoot (a ζ) L := by
  haveI : NeZero (L : κ) := ⟨by simpa using (hu.map a).ne_zero⟩
  rw [← Polynomial.isRoot_cyclotomic_iff]
  have hr := (hζ.isRoot_cyclotomic hL).map (f := a)
  simpa [Polynomial.map_cyclotomic] using hr

theorem latAt_unique : ∀ (o Ω : Type) [CommRing o] [IsDomain o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (G : Over M.Z) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (I T : Type) (f : I → (G ⟶ G)) (gγ : T → (Over.mk M.pt ⟶ G)) (ζ : oˣ) (L : ℕ), 0 < L → IsPrimitiveRoot (ζ : o) L → IsUnit (L : o) → ∀ (X X' : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [AddCommGroup X'] [Module.Free ℤ X'] [Module.Finite ℤ X'] (m : I → X →+ X) (c : T → X →+ ZMod L) (m' : I → X' →+ X') (c' : T → X' →+ ZMod L) (w : M.Z), LatAt f gγ ζ L m c w → LatAt f gγ ζ L m' c' w → ∃ e : X ≃+ X', (∀ i x, e (m i x) = m' i (e x)) ∧ ∀ t x, c' t (e x) = c t x := by
  intro o Ω _ _ _ _ M G _ _ hG I T f gγ ζ L hL hζ hu X X' _ _ _ _ _ _ m c m' c' w h h'
  haveI : IsSeparated G.hom := hG.separated
  exact LatAt.unique hL (fun κ _ a => isPrimitiveRoot_map hL hζ hu κ a) h h'

end GlobalTheory.UPoinc.GFibUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartOfHilbertBlumenthal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatJet.An

theorem jetRing_local_nil : ∀ (I : Type) [Fintype I] (n : ℕ) (J : JetRing ℂ I n),
    IsLocalRing J.B ∧ (∀ a : ℂ, J.π (algebraMap ℂ J.B a) = a) ∧ ∀ x ∈ RingHom.ker J.π, IsNilpotent x := by
  intro I _ n J
  have hπ : ∀ a : ℂ, J.π (algebraMap ℂ J.B a) = a := by
    intro a
    rw [J.π_eq, Algebra.algebraMap_eq_smul_one, ← J.one, map_smul]
    simp
  have hnil : ∀ x ∈ RingHom.ker J.π, IsNilpotent x := by
    intro x hx
    obtain ⟨N, hN⟩ := J.nil
    refine ⟨N, ?_⟩
    have := hN (List.replicate N (1, x)) (by
      intro p hp; rw [List.eq_of_mem_replicate hp]; exact hx) (by simp)
    simpa [J.κ.dpow_one hx] using this
  refine ⟨?_, hπ, hnil⟩
  haveI : Nontrivial J.B := RingHom.domain_nontrivial J.π
  have key : ∀ a : J.B, a ∈ nonunits J.B → J.π a = 0 := by
    intro a ha
    by_contra h0
    apply ha
    have hu : IsUnit (algebraMap ℂ J.B (J.π a)) := (IsUnit.mk0 _ h0).map _
    have hn : IsNilpotent (a - algebraMap ℂ J.B (J.π a)) :=
      hnil _ (by simp [RingHom.mem_ker, hπ])
    have := hn.isUnit_add_left_of_commute hu (Commute.all _ _)
    simpa using this
  refine IsLocalRing.of_nonunits_add fun a b ha hb ↦ ?_
  intro hab
  have h1 := hab.map J.π
  rw [map_add, key a ha, key b hb, add_zero] at h1
  exact not_isUnit_zero h1

theorem exists_smooth_modulus_point : GlobalTheory.Published.DelignePappasModel → ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (R : Type) [CommRing R] [Algebra ℂ R] (X' : Obj F 𝔠 (Sp R)), X'.Level 3 →
    ∃ (M : Scheme.{0}) (s : M ⟶ Sp (Localization.Away (3 : ℤ))) (U : Obj F 𝔠 M) (V : M.Opens) (b : Sp R ⟶ M)
      (φ : X'.A.left ⟶ U.A.left) (ι₀ : Localization.Away (3 : ℤ) →+* ℂ),
      X'.IsPullBy U b φ ∧ SmoothOfRelativeDimension (Module.finrank ℚ F) (V.ι ≫ s) ∧ (∀ x, b.base x ∈ V) ∧
      b ≫ s = spMap ((algebraMap ℂ R).comp ι₀) := by
  intro H F _ _ _ 𝔠 R _ _ X' β
  obtain ⟨M, s, U, α, hfine, -, -, -, -, -, ⟨V, -, hV, hdisc, -⟩, -⟩ := H F 𝔠 3 le_rfl
  have h3 : IsUnit ((Int.castRingHom ℂ) 3) := by
    rw [isUnit_iff_ne_zero]; norm_num
  let ι₀ : Localization.Away (3 : ℤ) →+* ℂ := IsLocalization.Away.lift (3 : ℤ) h3
  obtain ⟨b, ⟨hbs, φ, hφ, -⟩, -⟩ := hfine (Sp R) (spMap ((algebraMap ℂ R).comp ι₀)) X' β
  refine ⟨M, s, U, V, b, φ, ι₀, hφ, hV, ?_, hbs⟩
  intro x
  apply hdisc
  have hd : IsUnit ((NumberField.discr F : ℤ) : R) := by
    rw [← map_intCast (algebraMap ℂ R)]
    exact (IsUnit.mk0 _ (by exact_mod_cast NumberField.discr_ne_zero F)).map _
  let e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
  have hu : IsUnit ((NumberField.discr F : ℤ) : Γ(Sp R, ⊤)) := by
    have := hd.map e.symm.toRingHom
    simpa [map_intCast] using this
  have hx : x ∈ b ⁻¹ᵁ M.basicOpen ((NumberField.discr F : ℤ) : Γ(M, ⊤)) := by
    rw [Scheme.preimage_basicOpen, map_intCast]
    have hu' : IsUnit ((NumberField.discr F : ℤ) : Γ(Sp R, b ⁻¹ᵁ ⊤)) := by
      have := hu.map ((Sp R).presheaf.map (homOfLE (le_top : b ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom
      rwa [map_intCast] at this
    rw [Scheme.basicOpen_of_isUnit _ hu']
    trivial
  exact hx

theorem chart_of_hilbertBlumenthal : GlobalTheory.Published.HilbertBlumenthal → Chart := by
  intro H F _ _ _ 𝔠 I _ n J X'
  obtain ⟨hloc, hπ, hnil⟩ := jetRing_local_nil I n J
  let π : J.B →ₐ[ℂ] ℂ := { J.π with commutes' := hπ }
  obtain ⟨X₀, i₀, h₀⟩ := Obj.exists_isPullBy X' (spMap (π : J.B →+* ℂ))
  obtain ⟨α₀⟩ := GlobalTheory.T.nonempty_level_structure_complex F 𝔠 3 (by norm_num) X₀
  obtain ⟨β⟩ := GlobalTheory.T.level_structure_lift_nilpotent F 𝔠 3 (by norm_num) J.B π hnil X' X₀ i₀ h₀ α₀
  obtain ⟨M, s, U, V, b, φ, ι₀, hφ, hV, hb, hbs⟩ := exists_smooth_modulus_point H.1 F 𝔠 J.B X' β
  obtain ⟨B, _, _, _, g, j, hg⟩ := GlobalTheory.T.exists_smooth_local_factorization _ ι₀ M s V _ hV J.B b hb hbs
  obtain ⟨X₁, φ₁, h₁⟩ := Obj.exists_isPullBy U g
  rw [← hg] at hφ
  obtain ⟨ψ, hψ, -⟩ := hφ.cancel h₁
  obtain ⟨B', _, _, _, X₂, δ, k, j', q, hq, hk⟩ := GlobalTheory.T.exists_smooth_det_generated_cover F 𝔠 B J.B j X₁
  have e : spMap (j : B →+* J.B) = spMap (j' : B' →+* J.B) ≫ spMap (k : B →+* B') := by
    rw [← hk]
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp]; rfl
  rw [e] at hψ
  obtain ⟨ψ', hψ', -⟩ := hψ.cancel hq
  exact ⟨B', _, _, inferInstance, X₂, δ, j', ψ', hψ'⟩

end GlobalTheory.LatJet.An
end
end

