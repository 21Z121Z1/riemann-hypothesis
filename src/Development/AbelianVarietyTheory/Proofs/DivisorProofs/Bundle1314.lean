import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylRepInvMulDiag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1256
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionTopCoeffComplexPartitionOfUnityE
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem corrC_sum_eq_zero : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {ι : Type} [Fintype ι]
    (ρ : ι → V n → ℝ) (G₀ G₁ : V n → Matrix r r ℂ) (v : V n), (∀ i, DifferentiableAt ℝ (ρ i) v) →
    (∀ x, ∑ i, ρ i x = 1) → ∑ i, corrC (ρ i) G₀ G₁ v = 0 := by
  intro n r _ _ ι _ ρ G₀ G₁ v hd h1
  have hsum : ∀ w, ∑ i, dbar (fun x => (ρ i x : ℂ)) v w = 0 := by
    intro w
    have e : (fun x => ∑ i, (ρ i x : ℂ)) = fun _ => (1 : ℂ) := by
      funext x; rw [← Complex.ofReal_sum, h1]; simp
    have hs := dbar_sum (t := Finset.univ) (A := fun i x => (ρ i x : ℂ)) (z := v)
      (fun i _ => Complex.ofRealCLM.differentiableAt.comp v (hd i))
    rw [e, dbar_const] at hs
    rw [← ContinuousLinearMap.sum_apply, ← hs]; rfl
  have hadd : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n) (L L' : EndValuedForm11Coeffs n r),
      mixTop (intersection_update_fsHerm_neg_one K₁ (L + L') K₀ j) = mixTop (intersection_update_fsHerm_neg_one K₁ L K₀ j) + mixTop (intersection_update_fsHerm_neg_one K₁ L' K₀ j) := by
    intro K₁ K₀ j L L'; simpa using GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ L L' 1 1 j
  have hzero : ∀ (K₁ K₀ : EndValuedForm11Coeffs n r) (j : Fin n), mixTop (intersection_update_fsHerm_neg_one K₁ (0 : EndValuedForm11Coeffs n r) K₀ j) = 0 := by
    intro K₁ K₀ j; simpa using GlobalTheory.T.polarisedTopChernCoeff_position_linear K₁ K₀ 0 0 0 0 j
  have hc : ∑ i, cutForm (ρ i) G₀ G₁ v = 0 := by
    funext a b
    simp only [Finset.sum_apply, cutForm, ← Finset.sum_smul, hsum, zero_smul]
    rfl
  unfold corrC
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  let F : EndValuedForm11Coeffs n r →+ ℂ :=
    { toFun := fun L => mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) L (curvAt G₀ v) j)
      map_zero' := hzero _ _ _
      map_add' := fun L L' => hadd _ _ _ L L' }
  have hF : ∑ i, mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm (ρ i) G₀ G₁ v) (curvAt G₀ v) j) =
      F (∑ i, cutForm (ρ i) G₀ G₁ v) := by
    rw [map_sum]; rfl
  rw [hF, hc, map_zero]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapLtSwapIffOfAddTwo
section
noncomputable section

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG GlobalTheory.WeylCell.WeylUnipotentShell

namespace GlobalTheory

namespace WeylCell

namespace WeylUnipotentShell

theorem swap_lt_swap_iff_of_add_two {n : ℕ} (A A' a b : Fin n) (hA : A'.val = A.val + 2) (hab : a < b) :
    Equiv.swap A A' a < Equiv.swap A A' b ↔ (a < A ∨ A' < b) := by
  rw [Fin.lt_iff_val_lt_val] at hab
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def]
  split_ifs with h1 h2 h3 h4 h3 h4 <;>
    simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem val_rev_lo_of_last {n : ℕ} (k : Fin (n / 2)) (hk : ¬ k.val + 1 < n / 2) (hn : ¬ Even n) :
    ((lo k).rev : Fin n).val = (lo k).val + 2 := by
  have h2 := Nat.odd_iff.1 (Nat.not_even_iff_odd.1 hn)
  have := k.isLt
  simp only [Fin.val_rev, lo, Fin.coe_castLE]
  omega

theorem mem_cellU_last_iff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q →
    ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → ¬ Even n →
    ∀ y : GU σ n, y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ u : GU σ n, u ∈ cellU y ↔ IsUnipU u ∧ ∀ i j : Fin n, i < j → (i < lo k ∨ (lo k).rev < j) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = 0 := by
  intro L _ _ _ ϖ σ q _ n k hk hn y _ hy u
  have hw : simpleU k = Equiv.swap (lo k) (lo k).rev := by simp [simpleU, hk]
  have hA := val_rev_lo_of_last k hk hn
  rw [hw] at hy
  rw [cellU, Subgroup.mem_subgroupOf, GKFactor.mem_cell_iff hy, mem_unipB, Equiv.swap_inv]
  unfold IsUnipU IsBorelU
  refine and_congr_right fun _ => forall₂_congr fun a b => ?_
  constructor
  · intro h hab hor
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).2 hor)
  · intro h hab hs
    exact h hab ((swap_lt_swap_iff_of_add_two _ _ a b hA hab).1 hs)

end WeylUnipotentShell

end WeylCell

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiInjectiveCriterion
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt.CnSurj

theorem kappa_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (r : Γ(Sp O, ⊤))
    (s : Γ(GlobalTheory.Conormal.conormal (GlobalTheory.LieVB.sec (zeroSec O M)), ⊤)) :
    kappa O M (r • s) = toO O r • kappa O M s := by
  letI := (isChart O M).algebra
  letI := topModule O M
  exact map_smul ((AugCot.lift ((isChart O M).aug (GlobalTheory.LieVB.sec_hom _)) (sndFn O M)
    (sndFn_der O M)) ∘ₗ ((isChart O M).augCotEquiv (GlobalTheory.LieVB.sec_hom _)).symm.toLinearMap) r s

theorem Phi_smul {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] {A : Over (Sp O)} [GrpObj A]
    (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A) :
    Phi z h (c • w) = c • Phi z h w := by
  have e : toO O (GlobalTheory.LieVB.cst O c) = c := Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of O)) c
  have h1 := map_smul (QCoh.appLinear (GlobalTheory.LieVB.cotMap z h) ⊤) (GlobalTheory.LieVB.cst O c)
    (show Γ(GlobalTheory.LieVB.omega A, ⊤) from w)
  refine (congrArg (kappa O M) h1).trans ((kappa_smul O M _ _).trans ?_)
  rw [e]
  rfl

theorem cn_surjective (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O))
    [GrpObj A] (t : G.TorsionTower A)
    (hinj : ∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]
      (z z' : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]),
      (∀ w, Phi z h w = Phi z' h' w) → z = z')
    (hnat : ∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M]
      (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M)
      (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A),
      Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w =
        GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w))
    (n : ℕ) : Function.Surjective (cn t n) := by
  let ε := Bialgebra.counitAlgHom O (G.A n)
  let c : Wmod A →ₗ[O] AugCot ε :=
    { toFun := cn t n
      map_add' := map_add (cn t n)
      map_smul' := fun a w => Phi_smul _ _ a w }
  let N := AugCot ε ⧸ LinearMap.range c
  letI : Module Oᵐᵒᵖ N := opModule O N
  haveI : IsCentralScalar O N := opModule_central O N
  let q : AugCot ε →ₗ[O] N := (LinearMap.range c).mkQ
  let φ := (AugCot.sqZeroEquiv ε N).symm q
  let φ₀ := (AugCot.sqZeroEquiv ε N).symm 0
  have e : φ.1 = φ₀.1 := t.inj n _ _ _ <|
    hinj N _ _ (zeroSec_spOver_y t n φ.1 φ.2) (zeroSec_spOver_y t n φ₀.1 φ₀.2) fun w => by
      refine (hnat N n φ.1 φ.2 w).trans (Eq.trans ?_ (hnat N n φ₀.1 φ₀.2 w).symm)
      change AugCot.sqZeroEquiv ε N φ (c w) = AugCot.sqZeroEquiv ε N φ₀ (c w)
      rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, LinearMap.zero_apply]
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨w, rfl⟩
  have hq : q = 0 := (AugCot.sqZeroEquiv ε N).symm.injective (Subtype.ext e)
  intro x
  exact (Submodule.Quotient.mk_eq_zero (LinearMap.range c)).1 (LinearMap.congr_fun hq x)

end GlobalTheory.SqZeroPt.CnSurj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityFamily
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LieKer

theorem mem_smul_top_of_forms {O W : Type} [CommRing O] [AddCommGroup W] [Module O W]
    [Module.Finite O W] [Module.Projective O W] (I : Ideal O) (w : W)
    (hw : ∀ l : W →ₗ[O] O, l w ∈ I) : w ∈ (I • ⊤ : Submodule O W) := by
  obtain ⟨m, f, hf⟩ := Module.Finite.exists_fin' O W
  obtain ⟨s, hs⟩ := Module.projective_lifting_property f LinearMap.id hf
  have e : w = ∑ i, (s w i) • f (Pi.single i 1) := by
    conv_lhs => rw [← LinearMap.id_apply (R := O) w, ← hs]
    rw [LinearMap.comp_apply]
    conv_lhs => rw [pi_eq_sum_univ (s w)]
    simp only [map_sum, map_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext j
    simp [Pi.single_apply, eq_comm]
  rw [e]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ Submodule.mem_top
  exact hw (LinearMap.proj i ∘ₗ s)

end GlobalTheory.LieKer

namespace GlobalTheory.LieKer

open GlobalTheory.PDiv

theorem zeroSec_sqZeroMap {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N]
    [IsCentralScalar O N] (l : M →ₗ[O] N) :
    zeroSec O N ≫ GlobalTheory.GrpTangent.sqZeroMap l = zeroSec O M := by
  ext1
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
  simp

theorem ker_cn_le : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), Module.Finite O (Wmod A) → Module.Projective O (Wmod A) → (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (l : Wmod A →ₗ[O] O), ∃ (v : TM O O ⟶ A) (h : zeroSec O O ≫ v = η[A]), ∀ w, Phi v h w = l w) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ (n : ℕ) (w : Wmod A), cn t n w = 0 → w ∈ (Ideal.span {(p : O) ^ n} • ⊤ : Submodule O (Wmod A)) := by
  intro p O _ G A _ t hfin hproj hnat hsurj hcn n w hw
  refine mem_smul_top_of_forms _ w fun l => ?_
  obtain ⟨v, hv, hl⟩ := hsurj l
  let M := ModPow p O n
  let mk : O →ₗ[O] M := (Ideal.Quotient.mkₐ O (Ideal.span {(p : O) ^ n})).toLinearMap
  have h' : zeroSec O M ≫ (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) = η[A] := by
    rw [← Category.assoc, zeroSec_sqZeroMap, hv]
  have e1 := hnat O M mk v hv h' w
  have htan : IsTangent v := by
    have := congrArg Over.Hom.left hv
    simp only [Over.comp_left, zeroSec, Over.homMk_left] at this
    exact this
  have hpow : (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v : SpAlg O (TrivSqZeroExt O M) ⟶ A) ^ p ^ n = 1 := by
    have hs : GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale (((p ^ n : ℕ) : O)) =
        GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale 0 := by
      ext1
      change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp, ← Spec.map_comp]
      congr 1
      refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
      ext
      · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR]
      · simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.epsScaleR, mk]
    rw [← MonObj.comp_pow, GlobalTheory.GrpTangent.pow_eq_epsScale_comp htan, ← Category.assoc, hs,
      Category.assoc, GlobalTheory.GrpTangent.epsScale_zero_comp htan, MonObj.comp_one]
  obtain ⟨φ, hφy⟩ := t.surj n (TrivSqZeroExt O M) _ hpow
  have hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n) := by
    have H : spOver ((TrivSqZeroExt.fstHom O O M).comp φ) ≫ t.y n = 1 := by
      rw [← spOver_comp, Category.assoc, hφy]
      ext1
      simp only [Over.comp_left]
      have e : (spOver (TrivSqZeroExt.fstHom O O M)).left ≫ (GlobalTheory.GrpTangent.sqZeroMap mk).left =
          spMap (TrivSqZeroExt.fstHom O O O).toRingHom := by
        change Spec.map _ ≫ Spec.map _ = Spec.map _
        rw [← Spec.map_comp]
        congr 1
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        simp
      rw [← Category.assoc, e]
      refine (htan : _).trans ?_
      have hu : (toUnit (Over.mk (spMap (algebraMap O O)))).left = 𝟙 (Sp O) := by
        rw [Over.toUnit_left]; exact Spec.map_id _
      change η[A].left = (toUnit (Over.mk (spMap (algebraMap O O))) ≫ η[A]).left
      rw [Over.comp_left, hu]
      exact (Category.id_comp _).symm
    exact AlgHom.ext fun a => ((t.eq_one_iff n _).1 H a).trans (by simp)
  have e2 := hcn M n φ hφ w
  have e3 : Phi (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) h' w = 0 := by
    have tr : ∀ (z : TM O M ⟶ A) (hz : zeroSec O M ≫ z = η[A]), spOver φ ≫ t.y n = z →
        Phi z hz w = Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w := by
      rintro z hz rfl; rfl
    rw [tr _ h' hφy, e2, hw, map_zero]
  rw [e3, hl] at e1
  exact (Ideal.Quotient.eq_zero_iff_mem).1 e1.symm

end GlobalTheory.LieKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityModule
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

theorem Phi_congr {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    [IsCentralScalar O M] {A : Over (Sp O)} [GrpObj A] {z z' : TM O M ⟶ A} (e : z = z')
    (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O M ≫ z' = η[A]) (w : Wmod A) :
    Phi z h w = Phi z' h' w := by
  subst e; rfl

theorem eq_map_comp_univ {p : ℕ} {O : Type} [CommRing O] (G : GlobalTheory.PDivGroup p O) {M : Type}
    [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ)
    (φ : G.A n →ₐ[O] TrivSqZeroExt O M)
    (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) :
    φ = (TrivSqZeroExt.map
      (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩)).comp (univ G n) := by
  have hf : ∀ a, (φ a).fst = Bialgebra.counitAlgHom O (G.A n) a := fun a => AlgHom.congr_fun hφ a
  ext a
  · simp [univ, hf]
  · simp [univ]

theorem Phi_spOver_y : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) := by
  intro p O _ G A _ t nat M _ _ _ _ n φ hφ w
  have e : spOver φ ≫ t.y n = GlobalTheory.GrpTangent.sqZeroMap
      (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩) ≫
        spOver (univ G n) ≫ t.y n := by
    rw [← Category.assoc]
    congr 1
    have e1 : GlobalTheory.GrpTangent.sqZeroMap
        (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩) =
        spOver (TrivSqZeroExt.map
          (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩)) := rfl
    rw [e1, spOver_comp, ← eq_map_comp_univ G n φ hφ]
  have h' : zeroSec O M ≫ GlobalTheory.GrpTangent.sqZeroMap
      (GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩) ≫
        spOver (univ G n) ≫ t.y n = η[A] := e ▸ zeroSec_spOver_y t n φ hφ
  rw [Phi_congr e _ h' w]
  exact nat _ M _ (spOver (univ G n) ≫ t.y n)
    (zeroSec_spOver_y t n _ (fst_comp_univ (G := G) n)) h' w

end GlobalTheory.SqZeroPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiNaturalityPair
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

open GlobalTheory.PDiv

namespace GlobalTheory.SqZeroPt

theorem tanDer_cn : ∀ (p : ℕ) (O : Type) [CommRing O] (G : GlobalTheory.PDivGroup p O) (A : Over (Sp O)) [GrpObj A] (t : G.TorsionTower A), (∀ (M N : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] [AddCommGroup N] [Module O N] [Module Oᵐᵒᵖ N] [IsCentralScalar O N] (l : M →ₗ[O] N) (z : TM O M ⟶ A) (h : zeroSec O M ≫ z = η[A]) (h' : zeroSec O N ≫ (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) = η[A]) (w : Wmod A), Phi (GlobalTheory.GrpTangent.sqZeroMap l ≫ z) h' w = l (Phi z h w)) → (∀ (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (n : ℕ) (φ : G.A n →ₐ[O] TrivSqZeroExt O M) (hφ : (TrivSqZeroExt.fstHom O O M).comp φ = Bialgebra.counitAlgHom O (G.A n)) (w : Wmod A), Phi (spOver φ ≫ t.y n) (zeroSec_spOver_y t n φ hφ) w = GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) M ⟨φ, hφ⟩ (cn t n w)) → ∀ (v : epsR O ⟶ A) (hv : IsTangent v) (h : zeroSec O O ≫ v = η[A]) (n : ℕ) (w : Wmod A), t.tanDer hv n (cn t n w) = Ideal.Quotient.mk _ (Phi v h w) := by
  intro p O _ G A _ t hlin hpt v hv h n w
  haveI : IsCentralScalar O (ModPow p O n) := ⟨fun r m => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
    change (Submodule.Quotient.mk (MulOpposite.op r • x) : ModPow p O n) =
      Submodule.Quotient.mk (r • x)
    rw [op_smul_eq_smul]⟩
  let mk : O →ₗ[O] ModPow p O n := (Ideal.Quotient.mkₐ O _).toLinearMap
  let v' : TM O (ModPow p O n) ⟶ A := GlobalTheory.GrpTangent.sqZeroMap mk ≫ v
  have hsq : ∀ l : O →ₗ[O] ModPow p O n,
      GlobalTheory.GrpTangent.sqZeroMap l = spOver (TrivSqZeroExt.map l) := fun _ => rfl
  have hsc : ∀ c : O, GlobalTheory.GrpTangent.epsScale c =
      spOver (TrivSqZeroExt.map (c • (LinearMap.id : O →ₗ[O] O))) := fun _ => rfl
  have hpow : v' ^ p ^ n = 1 := by
    have h0 : mk ∘ₗ (((p ^ n : ℕ) : O) • (LinearMap.id : O →ₗ[O] O)) =
        mk ∘ₗ ((0 : O) • (LinearMap.id : O →ₗ[O] O)) := by
      refine LinearMap.ext fun x => ?_
      have hz : mk ((p ^ n : ℕ) : O) = 0 := by
        change Ideal.Quotient.mk (Ideal.span {(p : O) ^ n}) ((p ^ n : ℕ) : O) = 0
        rw [Ideal.Quotient.eq_zero_iff_mem, Nat.cast_pow]
        exact Ideal.mem_span_singleton_self _
      change mk (((p ^ n : ℕ) : O) • x) = mk ((0 : O) • x)
      rw [zero_smul, map_zero, smul_eq_mul, mul_comm, ← smul_eq_mul, map_smul, hz, smul_zero]
    have e1 : GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale ((p ^ n : ℕ) : O) =
        GlobalTheory.GrpTangent.sqZeroMap mk ≫ GlobalTheory.GrpTangent.epsScale 0 := by
      rw [hsq, hsc, hsc, spOver_comp, spOver_comp, ← TrivSqZeroExt.map_comp_map,
        ← TrivSqZeroExt.map_comp_map, h0]
    change (GlobalTheory.GrpTangent.sqZeroMap mk ≫ v) ^ p ^ n = 1
    rw [← MonObj.comp_pow, GlobalTheory.GrpTangent.pow_eq_epsScale_comp hv, ← Category.assoc, e1,
      Category.assoc, GlobalTheory.GrpTangent.epsScale_zero_comp hv, MonObj.comp_one]
  obtain ⟨φ, hφv⟩ := t.surj n (TrivSqZeroExt O (ModPow p O n)) v' hpow
  have hone : spOver (TrivSqZeroExt.fstHom O O O) ≫ v = 1 := by
    have h2 := congrArg Over.Hom.left h
    simp only [Over.comp_left] at h2
    ext1
    simp only [Over.comp_left]
    change (zeroSec O O).left ≫ v.left = _
    rw [h2]
    have hu : (toUnit (Over.mk (spMap (algebraMap O O)))).left = 𝟙 (Sp O) := by
      rw [Over.toUnit_left]; exact Spec.map_id _
    change _ = (toUnit (Over.mk (spMap (algebraMap O O)))).left ≫ η[A].left
    erw [hu]
    exact (Category.id_comp _).symm
  have hφ : (TrivSqZeroExt.fstHom O O (ModPow p O n)).comp φ =
      Bialgebra.counitAlgHom O (G.A n) := by
    have e : (TrivSqZeroExt.fstHom O O (ModPow p O n)).comp (TrivSqZeroExt.map mk) =
        TrivSqZeroExt.fstHom O O O := by
      ext; simp
    have h1 : spOver ((TrivSqZeroExt.fstHom O O (ModPow p O n)).comp φ) ≫ t.y n = 1 := by
      rw [← spOver_comp, Category.assoc, hφv]
      change spOver _ ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v = 1
      rw [hsq, ← Category.assoc, spOver_comp, e, hone]
    exact AlgHom.ext fun a => ((t.eq_one_iff n _).1 h1 a).trans (by simp)
  let q := Ideal.Quotient.mk (Ideal.span {(p : O) ^ n})
  let κ : TrivSqZeroExt O (ModPow p O n) →ₐ[O] DualNumber (ModPow p O n) :=
    { toFun := fun z => TrivSqZeroExt.inl (q z.fst) + TrivSqZeroExt.inr z.snd
      map_one' := by ext <;> simp
      map_mul' := fun x y => by
        ext
        · simp
        · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr]
          simp [Algebra.smul_def, q, mul_comm]
      map_zero' := by ext <;> simp
      map_add' := fun x y => by ext <;> simp [q]
      commutes' := fun r => by ext <;> simp [q, TrivSqZeroExt.algebraMap_eq_inl', Ideal.Quotient.algebraMap_eq] }
  have key : κ.comp (TrivSqZeroExt.map mk) = epsTo O (ModPow p O n) := by
    ext <;> simp [κ, q, mk]
  have htan : t.tanPt hv n = κ.comp φ := by
    refine t.inj n _ _ _ ?_
    rw [t.tanPt_y hv n, ← spOver_comp, Category.assoc, hφv]
    change _ = spOver κ ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v
    rw [hsq, ← Category.assoc, spOver_comp, key]
  have hder : t.tanDer hv n =
      GlobalTheory.AugCot.sqZeroEquiv (Bialgebra.counitAlgHom O (G.A n)) (ModPow p O n) ⟨φ, hφ⟩ :=
    GlobalTheory.AugCot.hom_ext fun a => by
      change t.tanDer hv n (dUnit O a) = _
      rw [t.tanDer_d hv n, GlobalTheory.AugCot.sqZeroEquiv_d, htan]
      simp [κ]
  have h' : zeroSec O (ModPow p O n) ≫ GlobalTheory.GrpTangent.sqZeroMap mk ≫ v = η[A] :=
    by have e := zeroSec_spOver_y t n φ hφ; rw [hφv] at e; exact e
  have hc : ∀ (z z' : TM O (ModPow p O n) ⟶ A) (e : z = z') (hz : zeroSec O (ModPow p O n) ≫ z = η[A])
      (hz' : zeroSec O (ModPow p O n) ≫ z' = η[A]), Phi z hz w = Phi z' hz' w := by
    intro z z' e hz hz'; subst e; rfl
  rw [hder, ← hpt (ModPow p O n) n φ hφ w, hc _ _ hφv _ h']
  exact hlin O (ModPow p O n) mk v h h' w

end GlobalTheory.SqZeroPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open GlobalTheory.SqZeroPt GlobalTheory.PDivGroup GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqZeroPt

open GlobalTheory.LieVB GlobalTheory.Conormal

theorem kappa_cotMap_cst_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    [Module Oᵐᵒᵖ M] [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Γ(omega A, ⊤)) :
    kappa O M ((cotMap z h).app ⊤ (cst O c • w)) = c • kappa O M ((cotMap z h).app ⊤ w) := by
  rw [show (cotMap z h).app ⊤ (cst O c • w) = cst O c • (cotMap z h).app ⊤ w from
    (QCoh.appLinear (cotMap z h) ⊤).map_smul (cst O c) w]
  obtain ⟨b, hb⟩ := (isChart O M).d_surjective (sec_hom (zeroSec O M)) ((cotMap z h).app ⊤ w)
  rw [← hb]
  have key : cst O c • d (sec_hom (zeroSec O M)) (isChart O M).le b =
      d (sec_hom (zeroSec O M)) (isChart O M).le ((TM O M).hom.appLE ⊤ ⊤ le_top (cst O c) * b) := by
    rw [d_mul]
    erw [d_base (sec_hom (zeroSec O M)) (isChart O M).le le_top (cst O c)]
    rw [smul_zero, add_zero]
    erw [appLE_base (sec_hom (zeroSec O M)) _ _ le_rfl]
    rfl
  rw [key, kappa_d, kappa_d, map_mul, toTsze_base, TrivSqZeroExt.snd_mul]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem Phi_smul (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M] [Module Oᵐᵒᵖ M]
    [IsCentralScalar O M] (A : Over (Sp O)) [GrpObj A] (z : TM O M ⟶ A)
    (h : zeroSec O M ≫ z = η[A]) (c : O) (w : Wmod A) :
    Phi z h (c • w) = c • Phi z h w :=
  kappa_cotMap_cst_smul O M A z h c w

end GlobalTheory.SqZeroPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThUContinuousInvol
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.EulerTw

theorem continuous_prjG (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (T : Finset (Pl E)) :
    Continuous (prjG E n T) := by
  have hc : Continuous (prjM E n T) := by
    show Continuous fun M : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E) =>
      idem E T • M + (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))
    exact (continuous_id.const_smul (idem E T)).add
      (continuous_const (y := (1 - idem E T) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E))))
  exact Continuous.units_map (prjM E n T) hc

theorem thU_continuous_invol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (u : Pl E),
    Continuous (GlobalTheory.EulerTw.thU E n u) ∧ ∀ g, GlobalTheory.EulerTw.thU E n u (GlobalTheory.EulerTw.thU E n u g) = g := by
  intro E _ _ _ n u
  refine ⟨?_, fun g => Subtype.ext ?_⟩
  · have hT : Continuous (thF E n) := GlobalTheory.ThetaPull.continuous_thetaGL _ (continuous_conjFin _)
    exact (((continuous_prjG E n (orb E u)).comp hT).comp continuous_subtype_val).subtype_mk _
  · rw [Comm.thU_val, Comm.thU_val, Comm.thF_thF]

end GlobalTheory.EulerTw
end
end

