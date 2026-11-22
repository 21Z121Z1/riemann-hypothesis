import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SortSign
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.OmegaPullOmegaTraceOfSecTraceOne
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0397
import Development.AutomorphicArithmetic.CommutativeAlgebra.Bundle0058
import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.Bundle0009
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3316
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0051

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.FunctionFieldOfFiniteEtaleCover
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory GlobalTheory.PD GlobalTheory.CechDR GlobalTheory.HodgeCoh ReciprocityTheory.ChartRestriction.G.Geo.Tor

private theorem mDR_alg_eq_mapDR (k K L : Type) [Field k] [Field K] [Field L] [Algebra k K] [Algebra k L]
    [Algebra K L] [IsScalarTower k K L] (w : DR k K) :
    (semiHom_algebraMap k K L).mDR w = GlobalTheory.W1.mapDR k K L w := by
  induction w using ExteriorAlgebra.induction with
  | algebraMap r =>
    rw [SemiHom.mDR_algebraMap, AlgHom.commutes]
    rfl
  | ι x =>
    have h1 := SemiHom.mDR_ι (semiHom_algebraMap k K L) x
    simp only [ι1] at h1
    rw [h1, SemiHom.oneFormMap_eq_kaehlerDifferential_map _ (fun _ => rfl)]
    simp only [GlobalTheory.W1.mapDR, ExteriorAlgebra.lift_ι_apply, GlobalTheory.W1.map1, LinearMap.coe_comp,
      LinearMap.coe_restrictScalars, Function.comp_apply, ι1]
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

private theorem mDR_square {k B B' K L : Type} [Field k] [Field K] [Field L] [CommRing B] [CommRing B']
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L] [Algebra k B] [Algebra k B']
    {α : B →+* K} {β : B →+* B'} {γ : B' →+* L} (hα : SemiHom (RingHom.id k) α)
    (hβ : SemiHom (RingHom.id k) β) (hγ : SemiHom (RingHom.id k) γ)
    (h : ∀ b, γ (β b) = algebraMap K L (α b)) {j : ℕ} (x : Om k B j) :
    hγ.mDR (hβ.mDR (x : DR k B)) = GlobalTheory.W1.mapDR k K L (hα.mDR (x : DR k B)) := by
  rw [← SemiHom.coe_mOm hβ, ← SemiHom.coe_mOm hγ, ← mDR_alg_eq_mapDR, ← SemiHom.coe_mOm hα,
    ← SemiHom.coe_mOm (semiHom_algebraMap k K L),
    SemiHom.mOm_mOm hβ hγ (hβ.comp hγ) (fun _ => rfl),
    SemiHom.mOm_mOm hα (semiHom_algebraMap k K L) (hβ.comp hγ) (fun b => (h b).symm)]

private theorem formGerm_toOm {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] (s : X ⟶ Sp k) (j : ℕ)
    {V : X.Opens} (hV : IsAffineOpen V) (hη : genericPoint X ∈ V) (x : OmU s V j) :
    letI := algΓ s; letI := ffAlg s
    formGerm s j hV hη (toOm s j V x) = (semiHom_germSec s hη).mDR (x : DR k (Sec s V)) := by
  letI := algΓ s; letI := ffAlg s
  change (semiHom_germSec s hη).mDR (((toOmEquiv s j hV).symm (toOm s j V x) : OmU s V j) : DR k (Sec s V)) = _
  rw [← toOmEquiv_apply s j hV, LinearEquiv.symm_apply_apply]

theorem UpperTheory.functionField_of_finite_etale_cover :
    ∀ (Z Y : Scheme.{0}) [IsIntegral Z] [IsIntegral Y] (p : Z ⟶ Sp ℂ) (p' : Y ⟶ Sp ℂ) (c : Y ⟶ Z) (hc : c ≫ p = p') [IsFinite c] [Etale c] [inst : Algebra ℂ Z.functionField] [inst' : Algebra ℂ Y.functionField] [Algebra Z.functionField Y.functionField] [IsScalarTower ℂ Z.functionField Y.functionField] (hinst : inst = ffAlg p) (hinst' : inst' = ffAlg p'), (∀ (V : Z.Opens) (hV : genericPoint Z ∈ V) (hV' : genericPoint Y ∈ c ⁻¹ᵁ V) (g : Γ(Z, V)), (Y.presheaf.germ (c ⁻¹ᵁ V) (genericPoint Y) hV').hom ((c.app V).hom g) = algebraMap Z.functionField Y.functionField ((Z.presheaf.germ V (genericPoint Z) hV).hom g)) → FiniteDimensional Z.functionField Y.functionField → ∀ (a : ℕ) (V : Z.Opens) (hV : IsAffineOpen V) (hη : genericPoint Z ∈ V) (hη' : genericPoint Y ∈ c ⁻¹ᵁ V) (y : Γ(Omega p' a, c ⁻¹ᵁ V)), letI := algΓ p; letI := algΓ p'; formGermI p a hV hη hinst ((omegaTrace hc a).app V y) = GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField (formGermI p' a (hV.preimage c) hη' hinst' y) := by
  intro Z Y _ _ p p' c hc _ _ inst inst' _ _ hinst hinst' hg hfd a V hV hη hη' y
  subst hinst hinst'
  letI := ffAlg p; letI := ffAlg p'
  haveI : CharZero Z.functionField := charZero_of_injective_algebraMap (algebraMap ℂ Z.functionField).injective
  haveI : Algebra.IsSeparable Z.functionField Y.functionField := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hT := UpperTheory.exists_deRhamTrace_of_separable ℂ Z.functionField Y.functionField
  have hspec : GlobalTheory.W1.IsTrDR ℂ Z.functionField Y.functionField (GlobalTheory.W1.trDR ℂ Z.functionField Y.functionField) := by
    unfold GlobalTheory.W1.trDR; rw [dif_pos hT]; exact hT.choose_spec
  obtain ⟨z, rfl⟩ := toOm_surjective (s := p') (j := a) (hV.preimage c) y
  change formGerm p a hV hη _ = GlobalTheory.W1.trDR ℂ _ _ (formGerm p' a (hV.preimage c) hη' _)
  rw [omegaTrace_app_toOm hc a hV, formGerm_toOm, formGerm_toOm]
  refine formOm_induction (P := fun z ↦ (semiHom_germSec p hη).mDR
      ((formTraceU hc hV a z : OmU p V a) : DR ℂ (Sec p V)) =
    GlobalTheory.W1.trDR ℂ _ _ ((semiHom_germSec p' hη').mDR (z : DR ℂ (Sec p' (c ⁻¹ᵁ V))))) hc hV ?_ ?_ ?_ z
  · simp only [map_zero, ZeroMemClass.coe_zero]
  · intro y z hy hz
    simp only [map_add, Submodule.coe_add, hy, hz]
  · intro b' x
    have e : ((formPull hc V a x : OmU p' (c ⁻¹ᵁ V) a) : DR ℂ (Sec p' (c ⁻¹ᵁ V))) =
        (semiHom_appSec hc V).mDR (x : DR ℂ (Sec p V)) := SemiHom.coe_mOm _ x
    rw [formTraceU_smul_formPull, Submodule.coe_smul, Submodule.coe_smul, SemiHom.mDR_smul,
      SemiHom.mDR_smul, e, mDR_square (semiHom_germSec p hη) (semiHom_appSec hc V)
        (semiHom_germSec p' hη') (fun b ↦ hg V hη hη' b), hspec]
    exact congrArg (· • _) (UpperTheory.Cb.germ_comap_eq_algebraMap_germ_of_finite_etale Z Y p p' c hc hg V hV hη hη' b')
end

-- bundled from Development.AutomorphicArithmetic.CommutativeAlgebra.QuotientModuliIso
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

theorem UpperTheory.quotient_moduli_iso : UpperTheory.Gal.Int.Geo.QIso := by
  intro q _ D R R' _ _ _ b gb N N' N₀ c c' X X₁ s s₁ o' o u f ψ hiso hmon hact hpol heta n
  obtain ⟨hP⟩ := hpol
  have hrefl : ∀ {Y : Scheme} (L : LB Y), L.IsLB → LBIso L L :=
    fun L hL => (GlobalTheory.CechPic.cls_eq_iff hL hL).mp rfl
  have h1 : (Hecke.lbPow o'.P 1).IsLB := DVR.linComb_isLB _ o'.isLB _ _
  have e1 : LBIso o'.P (Hecke.lbPow o'.P 1) :=
    (GlobalTheory.CechPic.cls_eq_iff o'.isLB h1).mp (by rw [GlobalTheory.LocTrivDescent.cls_lbPow_eq o'.isLB 1 h1, one_smul])
  have e3 : LBIso (o.P.pull (Hecke.sq2 ψ)) ((u.P.pull n.φ₂).pull (Hecke.sq2 ψ)) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullPull _ _ _ rfl) n.pol
  have e4 : LBIso ((u.P.pull n.φ₂).pull (Hecke.sq2 ψ)) (u.P.pull (Hecke.sq2 ψ ≫ n.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn u.P (fun _ => n.φ₂) (fun _ => (1 : ℤ)) (Hecke.sq2 ψ))
      (hrefl _ (pull_isLB (pull_isLB u.isLB _) _))
  have pol : LBIso o'.P (u.P.pull (Hecke.sq2 ψ ≫ n.φ₂)) :=
    LBIso.trans o'.isLB (pull_isLB o.isLB _) (pull_isLB u.isLB _)
      (LBIso.trans o'.isLB h1 (pull_isLB o.isLB _) e1 hP)
      (LBIso.trans (pull_isLB o.isLB _) (pull_isLB (pull_isLB u.isLB _) _) (pull_isLB u.isLB _) e3 e4)
  refine ⟨⟨Over.Hom.left ψ ≫ n.φ, Hecke.sq2 ψ ≫ n.φ₂, ?_, ?_, ?_, pol, ?_⟩, rfl⟩
  · have hc := (GlobalTheory.FibreAct.isGrpPullback_of_iso ψ).comp n.cart
    simpa using hc
  · constructor
    · rw [Category.assoc, n.sq.1, ← Category.assoc, ← Category.assoc, Hecke.sq2, ← Over.comp_left,
        lift_fst, Over.comp_left]
    · rw [Category.assoc, n.sq.2, ← Category.assoc, ← Category.assoc, Hecke.sq2, ← Over.comp_left,
        lift_snd, Over.comp_left]
  · intro x
    rw [← Category.assoc, ← Over.comp_left, hact x, Over.comp_left, Category.assoc, n.act x,
      Category.assoc]
  · intro y
    rw [← Category.assoc, ← Over.comp_left, heta y, n.eta y]
end
end

