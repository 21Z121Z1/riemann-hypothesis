import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0291
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsAffineOpenPreimageEqOfIsNilpotent
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.Bundle0002
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0253
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0290
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.Bundle0004
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.RedGalBase
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftDetOneAdelicApprox
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0275

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningCechCoverCompatible
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

private theorem rs_rs' {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V)
    (z : ↑(X.presheaf.obj (Opposite.op U))) : rs X h₂ (rs X h₁ z) = rs X (h₂.trans h₁) z := by
  simp only [rs]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp]
  rfl

theorem congr_secMulOn {X X' : Scheme.{0}} {π : X ⟶ X'} {N : LB X} {N' : LB X'}
    (v : LB.Iso N (N'.pull π)) (hN : N.IsLB) (hN' : N'.IsLB) (hv : v.IsGen) {a b c : ℤ}
    (h : a + b = c) {V : X.Opens} {V' : X'.Opens} (e : V ≤ π ⁻¹ᵁ V')
    (x : SecOn (pw N' a) V') (y : SecOn (pw N' b) V') (s : SecOn (pw N a) V)
    (t : SecOn (pw N b) V)
    (hs : SecOn.congr (isLB_pw hN a) (LB.isLB_pull (isLB_pw hN' a) π) (pullPow v a)
      (pullPow_isGen v a hv) V s = SecOn.pullLE (pw N' a) π V' V e x)
    (ht : SecOn.congr (isLB_pw hN b) (LB.isLB_pull (isLB_pw hN' b) π) (pullPow v b)
      (pullPow_isGen v b hv) V t = SecOn.pullLE (pw N' b) π V' V e y) :
    SecOn.congr (isLB_pw hN c) (LB.isLB_pull (isLB_pw hN' c) π) (pullPow v c)
      (pullPow_isGen v c hv) V (secMulOn h s t) =
      SecOn.pullLE (pw N' c) π V' V e (secMulOn h x y) := by
  subst h
  classical
  have hMc : ((pw N' (a + b)).pull π).IsLB := LB.isLB_pull (isLB_pw hN' (a + b)) π
  have key : ∀ (p : ((pw N' (a + b)).pull π).ι) (q : N.ι) {O : X.Opens}
      (hp : O ≤ V ⊓ ((pw N' (a + b)).pull π).U p)
      (hq : O ≤ V ⊓ (pw N (a + b)).U q) (hpq : O ≤ ((pw N' (a + b)).pull π).U p ⊓ (pw N (a + b)).U q),
      rs X hp (GlobalTheory.LB.coord (SecOn.congr (isLB_pw hN (a + b)) (LB.isLB_pull (isLB_pw hN' (a + b)) π)
        (pullPow v (a + b)) (pullPow_isGen v (a + b) hv) V (secMulOn rfl s t)) p) =
      rs X hp (GlobalTheory.LB.coord (SecOn.pullLE (pw N' (a + b)) π V' V e (secMulOn rfl x y)) p) := by
    intro p q O hp hq hpq
    have ha := SecOn.coord_congr (isLB_pw hN a) (LB.isLB_pull (isLB_pw hN' a) π) (pullPow v a)
      (pullPow_isGen v a hv) s p q hp hq hpq
    have hb := SecOn.coord_congr (isLB_pw hN b) (LB.isLB_pull (isLB_pw hN' b) π) (pullPow v b)
      (pullPow_isGen v b hv) t p q hp hq hpq
    rw [hs, SecOn.coord_pullLE π e x p] at ha
    rw [ht, SecOn.coord_pullLE π e y p] at hb
    rw [SecOn.coord_congr (isLB_pw hN (a + b)) (LB.isLB_pull (isLB_pw hN' (a + b)) π) (pullPow v (a + b))
      (pullPow_isGen v (a + b) hv) _ p q hp hq hpq, SecOn.coord_pullLE π e (secMulOn rfl x y) p,
      coord_secMulOn, coord_secMulOn rfl x y (p PUnit.unit)]
    erw [map_mul, map_mul, map_mul, ha, hb]
    dsimp only [pullPow]
    erw [zpow_add, Units.val_mul, map_mul]
    exact mul_mul_mul_comm _ _ _ _
  have hcov : V ≤ ⨆ a' : ((pw N' (a + b)).pull π).ι × N.ι, V ⊓ ((pw N' (a + b)).pull π).U a'.1 ⊓ N.U a'.2 := by
    intro z hz
    have h1 : z ∈ (⨆ i, ((pw N' (a + b)).pull π).U i) := by rw [hMc.cover]; trivial
    have h2 : z ∈ (⨆ i, N.U i) := by rw [hN.cover]; trivial
    rw [TopologicalSpace.Opens.mem_iSup] at h1 h2 ⊢
    obtain ⟨p, hp⟩ := h1
    obtain ⟨q, hq⟩ := h2
    exact ⟨(p, q), ⟨⟨hz, hp⟩, hq⟩⟩
  refine SecOn.ext_of_cover
    (fun a' : ((pw N' (a + b)).pull π).ι × N.ι => V ⊓ ((pw N' (a + b)).pull π).U a'.1 ⊓ N.U a'.2)
    (fun a' => inf_le_left.trans inf_le_left) hcov ?_
  intro a'
  apply (SecOn.chart hMc a'.1 (inf_le_left.trans inf_le_right)).injective
  rw [SecOn.chart_apply, SecOn.chart_apply, SecOn.coord_restrict, SecOn.coord_restrict, rs_rs', rs_rs']
  exact key a'.1 a'.2 _ (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right)

private theorem secOnR_linEquiv_symm_of {X : Scheme.{0}} {R : Type} [CommRing R] (f : X ⟶ Spec (CommRingCat.of R))
    {L M : LB X} {V : X.Opens} (φ : SecOn L V ≃ₗ[↑(X.presheaf.obj (Opposite.op V))] SecOn M V) (m : SecOn M V) :
    (SecOnR.linEquiv f φ).symm (SecOnR.of f M V m) = SecOnR.of f L V (φ.symm m) := by
  rw [LinearEquiv.symm_apply_eq, SecOnR.linEquiv_of, LinearEquiv.apply_symm_apply]

theorem red_secMulOn : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (hDβ : ∀ e S, D e S ≤ β e ⁻¹ᵁ D (e + 1) S) (a b c : ℤ) (h : a + b = c) (e : ℕ) (S : Finset ι) (x : SecOn (pw (N (e + 1)) a) (D (e + 1) S)) (y : SecOn (pw (N (e + 1)) b) (D (e + 1) S)), red I Y N D β hβ v hN hDβ c e S (SecOnR.of _ _ _ (secMulOn h x y)) = SecOnR.of _ _ _ (secMulOn h ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ a e S (SecOnR.of _ _ _ x))) ((SecOnR.of _ _ _).symm (red I Y N D β hβ v hN hDβ b e S (SecOnR.of _ _ _ y)))) := by
  intro R _ I Y β hβ N v hN ι D hDβ a b c h e S x y
  simp only [red, redL, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, SecOnR.pull_of,
    secOnR_linEquiv_symm_of, LinearEquiv.symm_apply_apply]
  refine congrArg (SecOnR.of _ _ _) ?_
  rw [LinearEquiv.symm_apply_eq]
  exact (congr_secMulOn (v e) (hN e).1 (hN (e + 1)).1 (hN e).2 h (hDβ e S) x y _ _
    (LinearEquiv.apply_symm_apply _ _) (LinearEquiv.apply_symm_apply _ _)).symm

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningRestrictionCompatibleOpens
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem redL_restrict : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (L : ∀ e, LB (Y e).left) (w : ∀ e, LB.Iso (L e) ((L (e + 1)).pull (β e))) (hL : ∀ e, (L e).IsLB ∧ (w e).IsGen) (e : ℕ) (V W : (Y (e + 1)).left.Opens) (V' W' : (Y e).left.Opens) (hV : V' ≤ β e ⁻¹ᵁ V) (hW : W' ≤ β e ⁻¹ᵁ W) (h : W ≤ V) (h' : W' ≤ V') (x : SecOnR (toR I Y (e + 1)) (L (e + 1)) V), redL I Y β hβ L w hL e W W' hW (SecOnR.restrict _ _ h x) = SecOnR.restrict _ _ h' (redL I Y β hβ L w hL e V V' hV x) := by
  intro R _ I Y β hβ L w hL e V W V' W' hV hW h h' x
  have key := SecOnR.pull_restrict (M := L (e + 1)) (toR_w I Y β hβ e) h h' hV hW x
  apply (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 W')).injective
  simp only [redL, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
  rw [key]
  obtain ⟨y, hy⟩ := (SecOnR.linEquiv (toR I Y e) (SecOn.congr (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e)
    (hL e).2 V')).surjective (SecOnR.pull (L (e + 1)) (toR_w I Y β hβ e) V V' hV x)
  rw [← hy, LinearEquiv.symm_apply_apply]
  exact (SecOn.congr_restrict (hL e).1 (LB.isLB_pull (hL (e + 1)).1 (β e)) (w e) (hL e).2 h' y).symm

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningSectionHomogeneousForm
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace Sp spMap)

namespace GlobalTheory.CompanionTheory.GE

theorem comp_app_eq_zero_iff {X Y Z : Scheme.{0}} (b : X ⟶ Y) [IsIso b] (g : Y ⟶ Z) (U : Z.Opens)
    (s : Γ(Z, U)) : ((b ≫ g).app U).hom s = 0 ↔ (g.app U).hom s = 0 := by
  rw [Scheme.Hom.comp_app]
  have hi : Function.Injective (b.app (g ⁻¹ᵁ U)).hom :=
    (ConcreteCategory.bijective_of_isIso (b.app (g ⁻¹ᵁ U))).1
  change (b.app (g ⁻¹ᵁ U)).hom ((g.app U).hom s) = 0 ↔ _
  exact map_eq_zero_iff _ hi

theorem mem_ker_thickι_iff {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1))
    (s : Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N k)) :
    s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal
        ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ↔
      ((GlobalTheory.ProjSpace.baseChange N (Ideal.Quotient.mk (I ^ (e + 1)))).app
        (GlobalTheory.ProjSpace.chart R N k)).hom s = 0 := by
  have h := GlobalTheory.ProjSpace.isPullback_baseChange N (Ideal.Quotient.mk (I ^ (e + 1)))
  have hb : h.isoPullback.hom ≫ thickι R I N e =
      GlobalTheory.ProjSpace.baseChange N (Ideal.Quotient.mk (I ^ (e + 1))) := h.isoPullback_hom_fst
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker, ← hb]
  exact (comp_app_eq_zero_iff h.isoPullback.hom (thickι R I N e) _ s).symm

theorem formOn_eq_zero_iff {R : Type} [CommRing R] {N : ℕ} (k : Fin (N + 1))
    {V : (PSpace R N).Opens} (hV : V = GlobalTheory.ProjSpace.chart R N k) (hle : V ≤ GlobalTheory.ProjSpace.chart R N k)
    {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) :
    GlobalTheory.ProjSpace.formOn V k hle n f hf = 0 ↔ f = 0 := by
  subst hV
  rw [← GlobalTheory.ProjSpace.formOn_zero (U := GlobalTheory.ProjSpace.chart R N k) (i := k) (hi := le_rfl) (n := n)]
  exact GlobalTheory.ProjSpace.formOn_chart_inj R N k hf _

open scoped GlobalTheory.ProjSpace in
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem exists_formOn_eq {R : Type} [CommRing R] {N : ℕ} (k : Fin (N + 1))
    (s : Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N k)) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n),
      s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf := by
  obtain ⟨p, rfl⟩ := (GlobalTheory.ProjSpace.chartAlgEquiv R N k).surjective s
  obtain ⟨n, f, hf, h⟩ := HomogeneousLocalization.Away.mk_surjective _ (GlobalTheory.ProjSpace.X_mem R N k)
    (GlobalTheory.ProjSpace.polyEquivAway R N k p)
  have hf' : f.IsHomogeneous n := by simpa using hf
  refine ⟨n, f, hf', ?_⟩
  rw [← GlobalTheory.ProjSpace.chartAlgEquiv_dehom R N k hf']
  congr 1
  have h1 := GlobalTheory.ProjSpace.awayToPoly_mk R N k n f hf
  rw [h] at h1
  exact ((GlobalTheory.ProjSpace.polyEquivAway R N k).left_inv p).symm.trans h1

theorem ker_thickι_chart : ∀ {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1)),
    (∀ s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩,
      ∃ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
        t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ∧
        s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht) ∧
    (∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) →
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩) := by
  intro R _ I N e k
  have hmem : ∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ↔
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
    intro n t ht
    rw [mem_ker_thickι_iff, GlobalTheory.ProjSpace.baseChange_app_formOn,
      formOn_eq_zero_iff k (GlobalTheory.ProjSpace.baseChange_preimage_chart N _ k), ← RingHom.mem_ker,
      MvPolynomial.ker_map, Ideal.mk_ker]
  refine ⟨fun s hs => ?_, fun n t ht h => (hmem n t ht).2 h⟩
  obtain ⟨n, t, ht, rfl⟩ := exists_formOn_eq k s
  exact ⟨n, t, ht, (hmem n t ht).1 hs, rfl⟩

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningTwistedSectionTransition
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem mul_mul_cancel_of_eq_one {A : Type*} [CommRing A] (a b c : A) (h : b * c = 1) :
    a * b * c = a := by
  rw [mul_assoc, h, mul_one]

theorem mul_mul_cancel_of_eq_one' {A : Type*} [CommRing A] (a b c : A) (h : c * b = 1) :
    a * b * c = a := by
  rw [mul_assoc, mul_comm b, h, mul_one]

theorem mulT_bijective_of_inverse :
    ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left) (hβ : ∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) (N : ∀ e, LB (Y e).left) (v : ∀ e, LB.Iso (N e) ((N (e + 1)).pull (β e))) (hN : ∀ e, (N e).IsLB ∧ (v e).IsGen) (d : ℤ) (ι : Type) (D : ∀ e, Finset ι → (Y e).left.Opens) (e : ℕ) (t : ℤ) (S : Finset ι) (σ : SecOn (pw (N e) d) (D e S)) (y : SecOn (pw (N e) (-d)) (D e S)), secMulOn rfl σ y = oneOn (N e) (add_neg_cancel d) (D e S) → Function.Bijective (mulT I Y N D d e t S σ) := by
  intro R _ I Y β hβ N v hN d ι D e t S σ y h
  have hc : ∀ i : (N e).ι, @HMul.hMul (Γ((Y e).left, D e S ⊓ (N e).U i)) (Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ (GlobalTheory.LB.coord σ i) (GlobalTheory.LB.coord y i) = 1 := by
    intro i
    have := congrArg (fun z : SecOn (pw (N e) (d + -d)) (D e S) =>
      GlobalTheory.LB.coord z (show (pw (N e) (d + -d)).ι from i)) h
    exact this
  let g : Tm I Y N D d e (t + 1) S →ₗ[R] Tm I Y N D d e t S :=
    mulRight (toR I Y e) (show d * (t + 1) + -d = d * t by ring) y
  refine Function.bijective_iff_has_inverse.2 ⟨g, ?_, ?_⟩
  · intro x
    exact GlobalTheory.LB.sec_ext fun (i : (N e).ι) =>
      mul_mul_cancel_of_eq_one (A := Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ _ (hc i)
  · intro x
    exact GlobalTheory.LB.sec_ext fun (i : (N e).ι) =>
      mul_mul_cancel_of_eq_one' (A := Γ((Y e).left, D e S ⊓ (N e).U i)) _ _ _ (hc i)

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningVeryAmpleOpensExist
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg GlobalTheory.CompanionTheory.FormalAlg.Lift

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.FormalAlg.Lift

theorem basicOpen_rs {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) :
    X.basicOpen (rs X h f) = V ⊓ X.basicOpen f :=
  Scheme.basicOpen_res X f (homOfLE h).op

theorem mem_nonzeroLocus_iff {X : Scheme.{0}} {H : LB X} (s : LB.Sec H) (x : X) :
    x ∈ nonzeroLocus s ↔ ∃ k, x ∈ X.basicOpen (s.f k) :=
  TopologicalSpace.Opens.mem_iSup

theorem basicOpen_eq_inf_nonzeroLocus {X : Scheme.{0}} {H : LB X} (a b : LB.Sec H)
    (r : Γ(X, nonzeroLocus a))
    (hr : ∀ k, rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (b.f k) =
      rs X (inf_le_left : nonzeroLocus a ⊓ H.U k ≤ nonzeroLocus a) r *
        rs X (inf_le_right : nonzeroLocus a ⊓ H.U k ≤ H.U k) (a.f k)) :
    X.basicOpen r = nonzeroLocus a ⊓ nonzeroLocus b := by
  have key : ∀ (k : H.ι) (x : X), x ∈ nonzeroLocus a → x ∈ H.U k →
      (x ∈ X.basicOpen (b.f k) ↔ x ∈ X.basicOpen r ∧ x ∈ X.basicOpen (a.f k)) := by
    intro k x hxa hxk
    have h := congrArg X.basicOpen (hr k)
    rw [Scheme.basicOpen_mul, basicOpen_rs, basicOpen_rs, basicOpen_rs] at h
    have hx : x ∈ nonzeroLocus a ⊓ H.U k := ⟨hxa, hxk⟩
    constructor
    · intro hb
      have : x ∈ (nonzeroLocus a ⊓ H.U k) ⊓ X.basicOpen (b.f k) := ⟨hx, hb⟩
      rw [h] at this
      exact ⟨this.1.2, this.2.2⟩
    · rintro ⟨h₁, h₂⟩
      have : x ∈ (nonzeroLocus a ⊓ H.U k ⊓ X.basicOpen r) ⊓
          (nonzeroLocus a ⊓ H.U k ⊓ X.basicOpen (a.f k)) := ⟨⟨hx, h₁⟩, ⟨hx, h₂⟩⟩
      rw [← h] at this
      exact this.2
  apply le_antisymm
  · intro x hx
    have hxa : x ∈ nonzeroLocus a := X.basicOpen_le r hx
    obtain ⟨k, hk⟩ := (mem_nonzeroLocus_iff a x).1 hxa
    exact ⟨hxa, (mem_nonzeroLocus_iff b x).2
      ⟨k, (key k x hxa (X.basicOpen_le _ hk)).2 ⟨hx, hk⟩⟩⟩
  · rintro x ⟨hxa, hxb⟩
    obtain ⟨k, hk⟩ := (mem_nonzeroLocus_iff b x).1 hxb
    exact ((key k x hxa (X.basicOpen_le _ hk)).1 hk).1

theorem exists_basicOpen_eq_inf_iInf {X : Scheme.{0}} {H : LB X} {m : ℕ}
    (s : Fin (m + 1) → LB.Sec H) (i : Fin (m + 1))
    (hi : ∀ j, ∃ r : Γ(X, nonzeroLocus (s i)),
      X.basicOpen r = nonzeroLocus (s i) ⊓ nonzeroLocus (s j))
    (S : Finset (Fin (m + 1))) :
    ∃ f : Γ(X, nonzeroLocus (s i)),
      X.basicOpen f = nonzeroLocus (s i) ⊓ ⨅ j ∈ S, nonzeroLocus (s j) := by
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | insert j S _ ih =>
    obtain ⟨f, hf⟩ := ih
    obtain ⟨r, hr⟩ := hi j
    refine ⟨f * r, ?_⟩
    rw [Scheme.basicOpen_mul, hf, hr, Finset.iInf_insert]
    ext x
    simp only [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe]
    tauto

theorem isAffineOpen_iInf_nonzeroLocus {X : Scheme.{0}} {R : Type} [CommRing R]
    {f : X ⟶ Spec (CommRingCat.of R)} {H : LB X} {m : ℕ} {s : Fin (m + 1) → LB.Sec H}
    (h : VeryAmpleBy f H s) {S : Finset (Fin (m + 1))} (hS : S.Nonempty) :
    IsAffineOpen (⨅ i ∈ S, nonzeroLocus (s i)) := by
  obtain ⟨i, hi⟩ := hS
  obtain ⟨hA, r, hr, -⟩ := h.2 i
  obtain ⟨g, hg⟩ := exists_basicOpen_eq_inf_iInf s i
    (fun j => ⟨r j, basicOpen_eq_inf_nonzeroLocus (s i) (s j) (r j) (hr j)⟩) S
  have e : ⨅ j ∈ S, nonzeroLocus (s j) = X.basicOpen g := by
    rw [hg]
    exact (inf_eq_right.2 (iInf₂_le i hi)).symm
  rw [e]
  exact hA.basicOpen g

theorem surjective_spec_of_nilpotent_ker {A A' : Type} [CommRing A] [CommRing A'] (g : A →+* A')
    (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g)) :
    Surjective (Spec.map (CommRingCat.ofHom g)) := by
  refine ⟨fun (x : PrimeSpectrum A) ↦ ?_⟩
  have : x ∈ Set.range (PrimeSpectrum.comap g) := by
    rw [_root_.range_comap_of_surjective _ _ hg]
    obtain ⟨n, hn⟩ := hn
    intro a ha
    apply x.isPrime.mem_of_pow_mem n
    have : a ^ n ∈ RingHom.ker g ^ n := Ideal.pow_mem_pow ha n
    rw [hn] at this
    rw [show a ^ n = 0 from this]
    exact zero_mem _
  exact this

theorem isNilpotent_ker_factor {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1)))) := by
  refine ⟨2, ?_⟩
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow, ← pow_mul]
  change _ = ⊥
  rw [eq_bot_iff, ← Ideal.map_quotient_self (I ^ (e + 1 + 1))]
  exact Ideal.map_mono (Ideal.pow_le_pow_right (by omega))

theorem exists_orderIso_opens {X X' : Scheme.{0}} (β : X ⟶ X') [IsClosedImmersion β]
    [Surjective β] : ∃ Φ : X.Opens ≃o X'.Opens, ∀ U, β ⁻¹ᵁ Φ U = U := by
  let h : X ≃ₜ X' := (β.isClosedEmbedding.isEmbedding).toHomeomorphOfSurjective β.surjective
  refine ⟨h.opensCongr, fun U => ?_⟩
  ext x
  have e : h.symm (β x) = x := h.symm_apply_apply x
  simp [h] at e ⊢
  rw [e]

theorem exists_orderIso_opens_tower (X : ℕ → Scheme.{0}) (β : ∀ e, X e ⟶ X (e + 1))
    [∀ e, IsClosedImmersion (β e)] [∀ e, Surjective (β e)] :
    ∃ G : ∀ e, (X 0).Opens ≃o (X e).Opens, (∀ U, G 0 U = U) ∧
      ∀ e U, β e ⁻¹ᵁ G (e + 1) U = G e U := by
  choose Φ hΦ using fun e => exists_orderIso_opens (β e)
  let G : ∀ e, (X 0).Opens ≃o (X e).Opens := fun e =>
    Nat.rec (OrderIso.refl _) (fun e G => G.trans (Φ e)) e
  exact ⟨G, fun _ => rfl, fun e U => hΦ e (G e U)⟩

theorem exists_basicOpens_of_tower : ∀ (R : Type) [CommRing R] (I : Ideal R) (Y : ∀ e : ℕ, Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (β : ∀ e, (Y e).left ⟶ (Y (e + 1)).left), (∀ e, IsPullback (β e) (Y e).hom (Y (e + 1)).hom (thickTrans R I e)) → ∀ (H : LB (Y 0).left) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy (Y 0).hom H s → ∃ D : ∀ e, Finset (Fin (m + 1)) → (Y e).left.Opens, (∀ S, D 0 S = ⨅ i ∈ S, nonzeroLocus (s i)) ∧ (∀ e S, β e ⁻¹ᵁ D (e + 1) S = D e S) ∧ (∀ e (S S' : Finset (Fin (m + 1))), S ⊆ S' → D e S' ≤ D e S) ∧ (∀ e S j, D e (insert j S) = D e S ⊓ D e {j}) ∧ (∀ e, ⨆ i, D e {i} = ⊤) ∧ (∀ e S, S.Nonempty → IsAffineOpen (D e S)) := by
  intro R _ I Y β hβ H m s _ hV
  have hg := fun e => Ideal.Quotient.factor_surjective
    (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)) : I ^ (e + 1 + 1) ≤ I ^ (e + 1))
  have hci : ∀ e, IsClosedImmersion (β e) := fun e =>
    have : IsClosedImmersion (thickTrans R I e) := .spec_of_surjective _ (hg e)
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) (hβ e).flip this
  have hsu : ∀ e, Surjective (β e) := fun e =>
    have : Surjective (thickTrans R I e) :=
      surjective_spec_of_nilpotent_ker _ (hg e) (isNilpotent_ker_factor I e)
    MorphismProperty.of_isPullback (P := @Surjective) (hβ e).flip this
  obtain ⟨G, hG0, hG⟩ := exists_orderIso_opens_tower (fun e => (Y e).left) β
  have hinj : ∀ e (U V : (Y (e + 1)).left.Opens), β e ⁻¹ᵁ U = β e ⁻¹ᵁ V → U = V := by
    intro e U V h
    ext x
    obtain ⟨y, rfl⟩ := (β e).surjective x
    exact Set.ext_iff.1 (congrArg (fun W : (Y e).left.Opens => (W : Set _)) h) y
  refine ⟨fun e S => G e (⨅ i ∈ S, nonzeroLocus (s i)), fun S => hG0 _, fun e S => hG e _,
    fun e S S' h => (G e).monotone (biInf_mono h), fun e S j => ?_, fun e => ?_, ?_⟩
  · beta_reduce
    rw [← map_inf, Finset.iInf_insert, Finset.iInf_singleton, inf_comm]
  · beta_reduce
    simp only [Finset.iInf_singleton]
    rw [← OrderIso.map_iSup, hV.1, OrderIso.map_top]
  · intro e S hS
    beta_reduce
    induction e with
    | zero =>
      rw [hG0]
      exact isAffineOpen_iInf_nonzeroLocus hV hS
    | succ e ih =>
      obtain ⟨D, hD, he⟩ := GlobalTheory.AffineThickening.exists_isAffineOpen_preimage_eq_of_isNilpotent
        _ _ _ (hg e) (isNilpotent_ker_factor I e) _ _ (Y (e + 1)).hom (Y e).hom (β e) (hβ e) _ ih
      rwa [hinj e _ _ (he.trans (hG e _).symm)] at hD

end GlobalTheory.CompanionTheory.FormalAlg.Lift
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedEnvelopeTorsionFreeStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_envelope_torsion_free : ∀ {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (l s : ℕ) (δ' : DividedPowers (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1))))), IsDPMorphism (eta δ) δ' (Ideal.Quotient.mk (fil (eta δ) (max s 1))) → fil δ s = ⊥ → (∀ (r : ℕ) (x : B), (l : B) * x ∈ fil δ r → x ∈ fil δ r) → fil δ' s = ⊥ ∧ (∀ (r : ℕ) (x : (pq B).P ⧸ fil (eta δ) (max s 1)), (l : (pq B).P ⧸ fil (eta δ) (max s 1)) * x ∈ fil δ' r → x ∈ fil δ' r) ∧ IsNilpotent (((pq B).ext J).map (Ideal.Quotient.mk (fil (eta δ) (max s 1)))) := by
  first | exact @GlobalTheory.CompanionTheory.SiteTr.tr_tf | exact GlobalTheory.CompanionTheory.SiteTr.tr_tf | (intros; apply GlobalTheory.CompanionTheory.SiteTr.tr_tf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherianStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.truncated_witt_isNoetherian : ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l], IsNoetherianRing (Wc.Wm l k 1) := by
  first | exact @GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one | exact GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one | (intros; apply GlobalTheory.CompanionTheory.WittLevel.isNoetherianRing_Wm_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwAcrFromBase
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.BetaGal

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dd_twAcr (k : Bool) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) :
    IsDPMorphism (DD k (tw σ A) n) (DD k A n) (twAcr σ A n) := by
  cases k
  exacts [dp_twAcr A σ n, dpP_twAcr A σ n]

theorem twAcr_fromBase (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (r : (base l).Acr n) :
    twAcr σ A n (mapAcr (tw σ A).fromBase n r) = mapAcr A.fromBase n (galBase σ n r) := by
  have e : (tw σ A).fromBase = baseTw σ ≫ twMap σ A.fromBase := (fromBase_comp _ (twMap σ A.fromBase)).symm
  rw [e, mapAcr_comp, twAcr_mapAcr]
  rfl

theorem uJ_tw (k : Bool) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (h) (x : (tw σ A).U) :
    Ideal.quotientMap (JJ k A n) (twAcr σ A n) h (uJ k (tw σ A) n x) = uJ k A n (twU σ A x) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotientMap (JJ k A n) (twAcr σ A n) h (uJ k (tw σ A) n ((tw σ A).th w)) = uJ k A n (twU σ A ((tw σ A).th w))
  rw [uJ_th, twU_th, uJ_th, Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) ((pdOk_twId σ A).acr_toAcr n w)

theorem map3 (P : CommRingCat.{0} ⥤ Type) {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (e : A →+* D) (he : ∀ x, h (g (f x)) = e x) (y : P.obj (CommRingCat.of A)) :
    P.map (CommRingCat.ofHom h) (P.map (CommRingCat.ofHom g) (P.map (CommRingCat.ofHom f) y)) = P.map (CommRingCat.ofHom e) y := by
  have e' : CommRingCat.ofHom f ≫ CommRingCat.ofHom g ≫ CommRingCat.ofHom h = CommRingCat.ofHom e :=
    CommRingCat.hom_ext (RingHom.ext he)
  rw [← e', Functor.map_comp_apply, Functor.map_comp_apply]

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (σ : Gal(PadicAlgCl l/K))
  (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n : ℕ)

def etaGal (T : El (F.pt κ)) :
    (gT F κ k n).obj ((elTw σ (ptTw F κ σ hσ)).obj T) ⟶ (SH.galM F κ σ hσ k n).obj ((gT F κ k n).obj T) :=
  crHom (twAcr σ T.1.obj n) (twAcr_fromBase σ T.1.obj n) (dd_twAcr k σ T.1.obj n) fun h =>
    map3 F.Pt (twUEquiv σ T.1.obj).symm.toRingHom (uJ k (tw σ T.1.obj) n) (Ideal.quotientMap _ (twAcr σ T.1.obj n) h)
      (uJ k T.1.obj n) (fun x => (uJ_tw k σ T.1.obj n h _).trans
        (congrArg (uJ k T.1.obj n) ((twUEquiv σ T.1.obj).apply_symm_apply x))) T.2.1

theorem β_gal : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) (x : Hc F κ k n j), β F κ k n j (galHc F κ σ hσ k n j x) = (galMor σ (ptTw F κ σ hσ) n).pull j (β F κ k n j x) := by
  intro l _ O _ F κ K σ hσ k n j x
  have h1 := pull_pull (ACris.galCris σ) (galMorC F κ σ hσ k n) (βMor F κ k n) j x
  have h2 := pull_pull (ACris.galCris σ) (βMor F κ k n) (galMor σ (ptTw F κ σ hσ) n) j x
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (cr_pull_eq ((βMor F κ k n).comp (σ'' := ACris.galCris σ) (galMor σ (ptTw F κ σ hσ) n))
    ((galMorC F κ σ hσ k n).comp (σ'' := ACris.galCris σ) (βMor F κ k n)) (etaGal F κ σ hσ k n)
    (fun f x => twAcr_mapAcr σ f.1.hom n x) (fun _ _ => rfl) j x).symm

end GlobalTheory.CompanionTheory.BetaGal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftDetOneAdelicApproxStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lift_det_one_adelic_approx : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → (∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1)) → ∀ ε : AF F, ε * P.inj 1 = P.inj 1 → ∀ a b : Fin M → E, IsoPlane K σ J (incV K a) (incV K b) → ¬ IsCompact (PlaneSupp σ J ε a b) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.NotCompact.not_isCompact_planeSupp | exact GlobalTheory.CompanionTheory.SaGen.NotCompact.not_isCompact_planeSupp | (intros; apply GlobalTheory.CompanionTheory.SaGen.NotCompact.not_isCompact_planeSupp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VeryAmpleTensorPowerSectionsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw PositivityTheory.FormalThickening
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier GlobalTheory.CompanionTheory.FormalAlg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.very_ample_tensor_power_sections : ∀ (R : Type) [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R)) (L : LB X) (d D : ℤ) (k : ℕ) (h : d * k = D) (p : ℕ) (a : Fin (p + 1) → LB.Sec (pw L d)), L.IsLB → 1 ≤ k → VeryAmpleBy f (pw L d) a → ∀ (m : ℕ) (e : Fin (m + 1) ≃ (Fin k → Fin (p + 1))), VeryAmpleBy f (pw L D) (fun j => secMono h a (e j)) := by
  first | exact @GlobalTheory.CompanionTheory.FormalAlg.veryAmpleBy_secMono | exact GlobalTheory.CompanionTheory.FormalAlg.veryAmpleBy_secMono | (intros; apply GlobalTheory.CompanionTheory.FormalAlg.veryAmpleBy_secMono <;> assumption)
end

