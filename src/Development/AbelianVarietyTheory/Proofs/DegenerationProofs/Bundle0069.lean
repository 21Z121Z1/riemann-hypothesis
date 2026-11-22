import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0055
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.GenericFiberGluing.SemistableCompleteSplit
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiEvenTauBimultDescendOfInjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section

namespace GlobalTheory.PullDescent

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'} {D : DegPre R}
  {D' : DegPre R'}

theorem corr_of_val_genMap (hφ : Function.Injective φ) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' : Type}
    [Fintype K] [Fintype K'] {ψ : K → ((TK R).left ⟶ X)} {ε : K → ℤ} {ψ' : K' → ((TK R).left ⟶ X)} {ε' : K' → ℤ}
    {t : LB.Gen (LB.LinComb L ψ ε)} {t' : LB.Gen (LB.LinComb L ψ' ε')}
    (h : ∀ (z : (TK R').left) (J : ((TK R').left ⟶ X) → L.ι), Good L z J →
      val t (genMap hφ) z J = val t' (genMap hφ) z J) : LB.Gen.Corr L ψ ε ψ' ε' t t' :=
  corr_of_val_field_extension _ _ (fracMap hφ) X L hL K K' ψ ε ψ' ε' t t' h

theorem psiEven_desc (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (h : D'.PsiEven) :
    D.PsiEven := by
  intro χ
  obtain ⟨x, rfl⟩ := hD.xe.surjective χ
  refine corr_of_val_genMap hφ D.P.isLB fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK R').left) z
  have sq := fracMap_sq hφ
  have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
  have cW : (𝟙 _ ≫ D'.xK x) ≫ proj hD = genMap hφ ≫ D.xK (hD.xe x) := by
    rw [Category.id_comp]; exact cPoint_proj hD _ hh x
  have cn : D'.xK (-x) = D'.xK x ≫ (ι[D'.P.A]).left := by
    show (toUnit _ ≫ D'.c (-x)).left = _
    rw [PsiEvenPull.c_neg, ← Category.assoc, Over.comp_left]
  have c' : 𝟙 _ ≫ D'.xK (-x) = (𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left := by rw [cn, Category.assoc]
  have e := val_corr hJ' (h x) (𝟙 (TK R').left)
  rw [val_mul hJ', val_pull hJ'] at e
  have a₁ := psi_val hD (Z := (TK R').left) _ _ sq hJ hJ' (-x)
  have a₂ := psi_val hD (Z := (TK R').left) _ _ sq hJ hJ' x
  have a₃ : val D.sym (genMap hφ ≫ D.xK (hD.xe x)) z J =
      om hD.w z J J' ((𝟙 _ ≫ D'.xK x) ≫ (ι[D'.P.A]).left) * (om hD.w z J J' (𝟙 _ ≫ D'.xK x))⁻¹ *
        val D'.sym (𝟙 _ ≫ D'.xK x) z J' :=
    (congrArg (fun q => val D.sym q z J) cW.symm).trans (PsiEvenPull.sym_pull hG hD _ z hJ hJ')
  rw [c', map_neg] at a₁
  refine (val_mul hJ _ _ _).trans (Eq.trans (congrArg₂ (· * ·) a₁ ((val_pull hJ _ _ _).trans a₃))
    (Eq.trans ?_ a₂.symm))
  rw [← e]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

set_option maxHeartbeats 1000000 in
theorem tauBimult_desc (hG : GlobalFnsSt) (hφ : Function.Injective φ) (hD : IsPullDeg φ D D') (h : D'.TauBimult) :
    D.TauBimult := by
  intro χ χ' ν
  obtain ⟨a, rfl⟩ := hD.xe.surjective χ
  obtain ⟨a', rfl⟩ := hD.xe.surjective χ'
  obtain ⟨b, rfl⟩ := hD.xe.surjective ν
  refine corr_of_val_genMap hφ D.P.isLB fun y J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK R').left) y
  have sq := fracMap_sq hφ
  have hh : (TK R').hom ≫ spMap φ = genMap hφ ≫ (TK R).hom := (Category.id_comp _).symm.trans sq
  have gp := pull_grp hD
  let T : Over (Spec (CommRingCat.of R)) := Over.mk ((TK R').hom ≫ spMap φ)
  let κ : T ⟶ TK R := Over.homMk (genMap hφ) hh.symm
  let β : (TK R' ⟶ D'.P.A) → (T ⟶ D.P.A) := fun x => pushPt gp.1.w x
  have βc : ∀ χ, β (cP D' _ χ) = cP D _ (hD.xe χ) := fun χ => Over.OverMorphism.ext (by
    show ((TK R').hom ≫ (D'.c χ).left) ≫ proj hD = ((TK R').hom ≫ spMap φ) ≫ (D.c (hD.xe χ)).left
    rw [Category.assoc, hD.c_pr, Category.assoc])
  let Ω : (TK R' ⟶ D'.P.A) → ((TK R').left.presheaf.stalk y)ˣ := fun x => om hD.w (Z := (TK R').left) y J J' x.left
  let θ : (T ⟶ D.P.A) → (T ⟶ D.P.A) → (T ⟶ D.P.A) → ((TK R').left.presheaf.stalk y)ˣ := th D (T := T) y J
  have cub : ∀ a b c : TK R' ⟶ D'.P.A, θ (β a) (β b) (β c) =
        Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ *
          th D' (T := TK R') y J' a b c := by
    intro a b c
    have e := cub_pull hG hD (T' := TK R') hJ hJ' a b c
    have q : (lift a (lift b c)).left ≫ (cubeMapOf gp).F3 = (lift (β a) (lift (β b) (β c))).left :=
      hom_ext_triple _ fun i => by
        rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
        fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b c (fun q => om hD.w (Z := (TK R').left) y J J' q)) rfl)
  let τ : D.X → D.X → ((TK R').left.presheaf.stalk y)ˣ := fun a b => val (D.tau a b) (genMap hφ) y J
  let τ' : D'.X → D'.X → ((TK R').left.presheaf.stalk y)ˣ := fun a b => val (D'.tau a b) (𝟙 (TK R').left) y J'
  have vτ : ∀ a b, τ (hD.xe a) (hD.xe b) =
      (Ω (cP D' _ a * cP D' _ b))⁻¹ * Ω (cP D' _ a) * Ω (cP D' _ b) * (Ω 1)⁻¹ * τ' a b := fun a b => by
    have e := tau_val hD (Z := (TK R').left) _ _ sq hJ hJ' a b
    simp only [Category.id_comp] at e
    rw [← cPoint_add]
    exact e
  have e : τ' (a + a') b * th D' (T := TK R') y J' (cP D' _ a) (cP D' _ a') (cP D' _ b) = τ' a b * τ' a' b := by
    refine Eq.trans (congrArg₂ (· * ·) rfl ?_)
      ((val_mul hJ' _ _ _).symm.trans ((val_corr hJ' (h a a' b) (𝟙 (TK R').left)).trans (val_mul hJ' _ _ _)))
    refine Eq.trans ?_ (val_cub D'.cub (𝟙 (TK R')) hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b)).symm
    rw [Category.id_comp, Category.id_comp, Category.id_comp]
  have key : τ (hD.xe a + hD.xe a') (hD.xe b) * θ (cP D T (hD.xe a)) (cP D T (hD.xe a')) (cP D T (hD.xe b)) =
      τ (hD.xe a) (hD.xe b) * τ (hD.xe a') (hD.xe b) := by
    rw [← βc, ← βc, ← βc, cub, ← map_add, vτ, vτ, vτ, cPoint_add]
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  refine (val_mul hJ _ _ _).trans (Eq.trans ?_ (val_mul hJ _ _ _).symm)
  refine Eq.trans (congrArg₂ (· * ·) rfl ?_) key
  refine (val_cub D.cub κ hJ (cP D _ (hD.xe a)) (cP D _ (hD.xe a')) (cP D _ (hD.xe b))).trans ?_
  rw [comp_cP, comp_cP, comp_cP]

end GlobalTheory.PullDescent

namespace GlobalTheory

theorem psiEven_tauBimult_of_isPullDeg_injective : GlobalFnsSt → ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∀ (D : DegPre R) (D' : DegPre R') (_ : IsPullDeg φ D D'), (D'.PsiEven → D.PsiEven) ∧ (D'.TauBimult → D.TauBimult) :=
  fun hG _ _ _ _ _ _ _ hφ _ _ hD => ⟨PullDescent.psiEven_desc hG hφ hD, PullDescent.tauBimult_desc hG hφ hD⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PsiRelationDescendsFieldExtension
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiRelationDescent

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull
open GlobalTheory.PsiEvenPull (proj)

def chartPullComb {X Y Y' : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y) :
    ChartPull ((LB.LinComb L φ ε).pull h) (LB.LinComb L (fun k => h ≫ φ k) ε) (𝟙 Y') :=
  have le : ∀ J : PUnit → K → L.ι, ((LB.LinComb L φ ε).pull h).U J ≤
      LB.wchart L (fun k => h ≫ φ k) (J PUnit.unit) :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 hy) k
  { idx := fun J => J PUnit.unit
    le := le
    g := fun y J J' hj hj' => by
      refine (gm_pull_g (LB.LinComb L φ ε) h (𝟙 Y') y J J' hj hj').trans
        ((gm_linComb L φ ε (𝟙 Y' ≫ h) y _ _ (mem_pull.1 hj) (mem_pull.1 hj')).trans
          (Eq.trans ?_ (gm_linComb L (fun k => h ≫ φ k) ε (𝟙 Y') y _ _ (le J hj) (le J' hj')).symm))
      simp only [Category.assoc] }

section

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]
  (oa : D.OAct O) (w : O)

abbrev mor : Fin 4 → (D.P.A.left ⟶ D.P.A.left) :=
  ![(padd D.P.A (𝟙 _) (oa.onB.act w)).left, 𝟙 D.P.A.left, (oa.onB.act w).left, (toUnit D.P.A ≫ η[D.P.A]).left]

theorem prod_mor {T : Over (Sp R)} (x : T ⟶ D.P.A) {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h (x.left ≫ mor oa w k) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) k =
      h (x * (x ≫ oa.onB.act w)).left * (h x.left ^ 2)⁻¹ * (h (x ≫ oa.onB.act w).left)⁻¹ *
        h (1 : T ⟶ D.P.A).left ^ 2 := by
  have a₀ : x ≫ padd D.P.A (𝟙 _) (oa.onB.act w) = x * (x ≫ oa.onB.act w) :=
    (MonObj.comp_mul _ _ _).trans (by rw [Category.comp_id])
  have a₁ : x ≫ toUnit D.P.A ≫ η[D.P.A] = 1 := MonObj.comp_one (M := D.P.A) x
  rw [Fin.prod_univ_four]
  show h (x ≫ padd D.P.A (𝟙 _) (oa.onB.act w)).left ^ (1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (-2 : ℤ) *
    h (x ≫ oa.onB.act w).left ^ (-1 : ℤ) * h (x ≫ toUnit D.P.A ≫ η[D.P.A]).left ^ (2 : ℤ) = _
  rw [a₀, a₁, Category.comp_id]
  simp only [zpow_neg, zpow_ofNat, pow_one]

theorem prod_mor_one {T : Over (Sp R)} {U : Type} [CommGroup U] (h : (T.left ⟶ D.P.A.left) → U) :
    ∏ k : Fin 4, h ((1 : T ⟶ D.P.A).left ≫ mor oa w k) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) k = 1 := by
  have := oa.onB.hom w
  rw [prod_mor, MonObj.one_comp, _root_.mul_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one]
  abel

theorem exists_normalised (u : LB.Gen (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2])) (hu : u.IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2]), t.IsGen ∧
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec D.P.A)) (LB.oneGen D.P.L) := by
  obtain ⟨t, ht, hv⟩ := exists_gen D.P.isLB (φ' := mor oa w) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _
        (c := ∏ i, k (mor oa w i) ^ (![1, -2, -1, 2] : Fin 4 → ℤ) i) rfl
        (prod_neg _ _ (prod_mor_one oa w (T := D.P.A) k))) ?_
      simp)
    (LB.mulGen D.P.L _ _ _ _ u (LB.invGen D.P.L _ _ (LB.pullGen D.P.L _ _ u (1 : D.P.A ⟶ D.P.A).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hu (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hu _)))
  refine ⟨t, ht, corr_of_val D.P.isLB fun y J hJ => ?_⟩
  have e : eSec D.P.A ≫ (1 : D.P.A ⟶ D.P.A).left = eSec D.P.A :=
    (congrArg (fun q => q.left) (MonObj.comp_one (M := D.P.A) η[D.P.A])).trans (Category.id_comp _)
  rw [val_pull hJ, val_one, Category.id_comp, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, e, mul_inv_cancel]

end

end GlobalTheory.PsiRelationDescent

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ArcPull GlobalTheory.PsiRelationDescent in

theorem psi_relation_descend_field : GlobalFnsSt → ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (D : DegPre K₀) (D' : DegPre K) (hD : IsPullDeg i D D') (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X] (oa : D.OAct O) (oa' : D'.OAct O), (∀ (a : O) (y : D'.X), hD.xe (a • y) = a • hD.xe y) → (∀ a, (oa'.onB.act a).left ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ (oa.onB.act a).left) → ∀ w : O, TraceFormTwistIso D' oa' w → TraceFormTwistIso D oa w := by
  intro hG K₀ K _ _ i D D' hD O _ _ _ _ oa oa' hx ho w ⟨u', hu', u₀', hy'⟩
  have gp := pull_grp hD
  have hφ : Function.Injective i := i.injective
  have i₁ : (𝟙 D'.P.A : D'.P.A ⟶ _).left ≫ PsiEvenPull.proj hD =
      PsiEvenPull.proj hD ≫ (𝟙 D.P.A : D.P.A ⟶ _).left :=
    (Category.id_comp _).trans (Category.comp_id _).symm
  have i₂ : (toUnit D'.P.A ≫ η[D'.P.A]).left ≫ PsiEvenPull.proj hD =
      PsiEvenPull.proj hD ≫ (toUnit D.P.A ≫ η[D.P.A]).left := by
    show (D'.P.A.hom ≫ eSec D'.P.A) ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ D.P.A.hom ≫ eSec D.P.A
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hD.he).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) gp.1.w.symm).trans (Category.assoc _ _ _))))
  have hψ : ∀ k, mor oa' w k ≫ PsiEvenPull.proj hD = PsiEvenPull.proj hD ≫ mor oa w k := fun k => by
    fin_cases k
    exacts [mul_push gp _ i₁ (ho w), i₁, ho w, i₂]
  obtain ⟨s, hs, -⟩ := exists_up_om ((isGen_iff _).1 hD.w_gen) D.P.isLB D'.P.isLB (mor oa' w)
    (fun k => PsiEvenPull.proj hD ≫ mor oa w k) _ hψ u' hu'
  obtain ⟨u₁, hu₁⟩ := (lb_gen_iso_descend_field K₀ K i _ _ D.P.A.hom D'.P.A.hom (PsiEvenPull.proj hD)
    D.P.isAb.smooth D.P.isAb.proper D.P.isAb.geomConnected gp.1).1 (LB.LinComb D.P.L (mor oa w) ![1, -2, -1, 2])
    (LB.isLB_linComb D.P.isLB _ _) ⟨_, GtBaseChange.genPull_isGen (chartPullComb D.P.L (mor oa w) _ _) hs⟩
  obtain ⟨u, hu, u₀⟩ := exists_normalised oa w u₁ hu₁
  obtain ⟨t, ht, vt⟩ := exists_down_om hD.w_gen D.P.isLB D'.P.isLB (φ' := mor oa' w) (PsiEvenPull.proj hD) hψ u hu
  have tu := gen_unique D'.P.isLB D'.P.A.hom (eSec D'.P.A) (Over.w η[D'.P.A]) (hG _ _ D'.P.isAb).2 ht hu'
    fun y J' hJ' => by
      obtain ⟨J, hJ⟩ := DegPull.exists_good' D.P.isLB y
      have o₁ : (1 : 𝟙_ (Over (Sp K)) ⟶ D'.P.A).left = eSec D'.P.A := Category.id_comp _
      have e := vt _ (1 : 𝟙_ (Over (Sp K)) ⟶ D'.P.A).left y J J' hJ hJ'
      rw [prod_mor_one, _root_.one_mul, o₁, hD.he] at e
      have e₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ u₀ (specOf i)).trans (val_one _))
      have e₂ := (val_pull hJ' _ _ _).symm.trans ((val_corr hJ' u₀' (𝟙 _)).trans (val_one _))
      rw [Category.id_comp] at e₂
      exact e.symm.trans (e₁.trans e₂.symm)
  refine ⟨u, hu, u₀, fun y => ?_⟩
  obtain ⟨x, rfl⟩ := hD.xe.surjective y
  refine corr_of_val_field_extension _ _ (fracMap hφ) _ _ D.P.isLB _ _ _ _ _ _ _ _ fun z J hJ => ?_
  obtain ⟨J', hJ'⟩ := DegPull.exists_good' D'.P.isLB (Z := (TK K).left) z
  have sq := fracMap_sq hφ
  have hh : (TK K).hom ≫ spMap i = genMap hφ ≫ (TK K₀).hom := (Category.id_comp _).symm.trans sq
  have e := val_corr hJ' (hy' x) (𝟙 _)
  have v := vt _ (cP D' (TK K) x).left z J J' hJ hJ'
  rw [prod_mor, cPoint_proj hD _ hh, ← TorusExt.cPoint_smul oa', ← cPoint_add, tu _ _ z J' hJ'] at v
  have c₀ : ∀ x, (cP D' (TK K) x).left = D'.xK x := fun _ => rfl
  have c₁ : ∀ x, (cP D (TK K₀) x).left = D.xK x := fun _ => rfl
  simp only [c₀, c₁] at v
  rw [val_mul hJ', val_mul hJ', val_pull hJ', Category.id_comp] at e
  show val (LB.mulGen D.P.L _ _ _ _ (D.tau (hD.xe x) (w • hD.xe x)) (LB.pullGen D.P.L _ _ u (D.xK (hD.xe x))))
    (genMap hφ) z J = val (LB.mulGen D.P.L _ _ _ _ (D.psi (hD.xe x)) D.rigK) (genMap hφ) z J
  have hJ₀ : Good (Z := (TK K).left) D.P.L z J := hJ
  rw [val_mul hJ₀, val_mul hJ₀, val_pull hJ₀, v, ← hx, tau_val hD _ _ sq hJ₀ hJ', psi_val hD _ _ sq hJ₀ hJ',
    rig_val hD _ _ sq hJ₀ hJ']
  simp only [Category.id_comp]
  have e' := congrArg Additive.ofMul e
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow] at e' ⊢
  linear_combination (norm := abel) e'

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RigidificationComparisonUniformisation
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.RigCmpPf

theorem eSec_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (h : IsGrpPullback G' G f F) :
    eSec G' ≫ F = f ≫ eSec G := (cubeMapOf h).e_comm

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def upt (G : Over (Spec (CommRingCat.of R))) [GrpObj G] {e : ℕ} {Z : Scheme.{0}}
    (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) : Z ⟶ (thickObj R I e G).left :=
  a ≫ eSec (thickObj R I e G)

omit [IsDomain R] [IsCommMonObj G] in
theorem eSec_fst (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :
    (upt G a) ≫ (fstG I e G).left = (a ≫ thick R I e) ≫ eSec G :=
  (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (UnitValue.eSec_pullback_fst (thick R I e) G)).trans
    (Category.assoc _ _ _).symm)

theorem eSec_pG {e : ℕ} (g : GtCoord I D e G) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) :
    (upt G a) ≫ g.pG.left = (a ≫ thick R I e) ≫ eSec D.P.A := by
  have := g.q_hom
  have h1 : (η[thickObj R I e G] ≫ g.q) = η[thickObj R I e D.P.A] := IsMonHom.one_hom _
  have h2 : eSec (thickObj R I e G) ≫ g.q.left = eSec (thickObj R I e D.P.A) := congrArg Over.Hom.left h1
  refine Eq.trans ?_ (eSec_fst (G := D.P.A) e a)
  unfold upt
  rw [← h2]
  exact (Category.assoc _ _ _).trans ((congrArg (a ≫ ·) (Category.assoc _ _ _).symm).trans
    (Category.assoc _ _ _).symm)

theorem rig_val (U : PreU I D A G) (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (z : Z) {JG : (Z ⟶ G.left) → U.P.L.L.ι} {J : (Z ⟶ D.P.A.left) → D.P.L.ι} (hJG : Good U.P.L.L z JG)
    (hJ : Good D.P.L z J) :
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (a ≫ thick R I e) z J =
      gw (U.w e) (upt G a) z (J ((upt G a) ≫ (U.gt e).pG.left))
          (fun _ => JG ((upt G a) ≫ (fstG I e G).left)) *
        val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (a ≫ thick R I e) z JG := by
  have h := (U.w_vals e (Over.mk a) z JG J hJG hJ _ (fun _ => rfl)).1
  rw [one_left] at h
  exact h

theorem rig_level {V : Type} [CommRing V] [IsDomain V] {I' : Ideal V} {D' : DegPre V}
    {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
    [IsCommMonObj G'] {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}
    (C : Cmp φ U U' F) (e : ℕ) {Z : Scheme.{0}} (a : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
    (a' : Z ⟶ Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))
    (ha : a ≫ thick R I e = (a' ≫ thick V I' e) ≫ spMap φ) (z : Z) {J J'} (hJ : Good D.P.L z J)
    (hJ' : Good D'.P.L z J') :
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (a ≫ thick R I e) z J =
      gw C.v (upt G' a' ≫ (U'.gt e).pG.left) z (J (upt G a ≫ (U.gt e).pG.left))
          (J' (upt G' a' ≫ (U'.gt e).pG.left)) *
        val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (a' ≫ thick V I' e) z J' := by
  have hG := eSec_comm C.pb
  obtain ⟨K, hK⟩ := exists_good_pt U.P.L.isLB z
  obtain ⟨K', hK'⟩ := exists_good_pt U'.P.L.isLB z
  have e₁ := rig_val U e a z hK hJ
  have e₂ := rig_val U' e a' z hK' hJ'
  have e₃ := (C.wL_map.vals (Over.mk (a' ≫ thick V I' e)) z K' K hK' hK _ (fun _ => rfl)).1
  rw [one_left] at e₃
  have hx : upt G a ≫ (fstG I e G).left = (upt G' a' ≫ (fstG I' e G').left) ≫ F := by
    rw [eSec_fst e a, eSec_fst e a', ha]
    exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hG.symm).trans (Category.assoc _ _ _).symm)
  have e₄ := ((C.lev e _ _ _ (hx.trans (Category.assoc _ _ _))).2 z J J' hJ hJ').2 _ _
    (hK (upt G a ≫ (fstG I e G).left)) (hK' (upt G' a' ≫ (fstG I' e G').left))
  have f₃ : val (L := U.P.L.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) U.P.L.rig (a ≫ thick R I e) z K =
      gw C.wL (upt G' a' ≫ (fstG I' e G').left) z (K (upt G a ≫ (fstG I e G).left))
        (K' (upt G' a' ≫ (fstG I' e G').left)) *
      val (L := U'.P.L.L) (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1) U'.P.L.rig
        (a' ≫ thick V I' e) z K' := by
    rw [ha, hx, eSec_fst e a']
    exact e₃
  exact e₁.trans ((congrArg _ f₃).trans ((_root_.mul_assoc _ _ _).symm.trans
    ((congrArg (· * _) e₄.symm).trans ((_root_.mul_assoc _ _ _).trans (congrArg _ e₂.symm)))))

end GlobalTheory.RigCmpPf

namespace GlobalTheory

open RigCmpPf in

theorem rigCmp_of_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I' ≠ ⊤ → I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (A' : PolAV (Sp (FractionRing V))) (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), RigCmp φ D D' C.β C.v := by
  intro R V _ _ _ _ _ _ I I' φ hI' hφ D D' A G _ _ A' G' _ _ U U' F C
  have hB := eSec_comm C.pbB
  have key := AbelianPartIso.pmaps_of_thickenings hI' D.P.isLB D'.P.isLB C.v C.v_gen (eSec D'.P.A)
    (spMap φ ≫ eSec D.P.A) hB D'.rig D'.rig_gen
    (LB.pullGen D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => 1) D.rig (spMap φ))
    (DVR.pullGen_isGen _ _ _ _ D.rig_gen _) fun e z p q hp hq => by
      have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ := by
        rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
        exact Ideal.pow_right_mono hφ _
      let a : Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))) ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) :=
        spMap (Ideal.quotientMap _ φ hle)
      have ha : a ≫ thick R I e = (𝟙 _ ≫ thick V I' e) ≫ spMap φ := by
        rw [Category.id_comp, ← Spec.map_comp, ← Spec.map_comp]
        rfl
      obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB z (fun _ : Unit => thick V I' e ≫ spMap φ ≫ eSec D.P.A)
        (fun _ => p) (fun _ _ _ => rfl) (fun _ => hp)
      obtain ⟨J', hJ', eJ'⟩ := exists_good D'.P.L D'.P.isLB z (fun _ : Unit => thick V I' e ≫ eSec D'.P.A)
        (fun _ => q) (fun _ _ _ => rfl) (fun _ => hq)
      have E := rig_level C e a (𝟙 _) ha z hJ hJ'
      have hp' : (a ≫ thick R I e) ≫ eSec D.P.A = thick V I' e ≫ spMap φ ≫ eSec D.P.A := by
        rw [ha, Category.id_comp]
        exact Category.assoc _ _ _
      rw [eSec_pG (U.gt e) a, eSec_pG (U'.gt e) (𝟙 _), hp', ha, Category.id_comp, eJ (), eJ' (),
        val_of _ _ z J (fun _ => p) (fun _ => (congrArg J (Category.assoc _ _ _)).trans (eJ ())),
        val_of _ _ z J' (fun _ => q) (fun _ => eJ' ())] at E
      refine Eq.trans ?_ E
      have m₁ : thick V I' e z ∈ LB.wchart D.P.L (fun _ : PUnit => spMap φ ≫ eSec D.P.A) (fun _ => p) :=
        Set.mem_iInter.2 fun _ => hp
      have m₂ : spMap φ (thick V I' e z) ∈ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) (fun _ => p) :=
        Set.mem_iInter.2 fun _ => hp
      exact (gm_res _ z _ m₁ _).trans (gm_pull _ (spMap φ) z _ m₂ _)
  intro Z r z p q hp hq
  have hm : (spMap φ ≫ eSec D.P.A) (r z) ∈ D.P.L.U (p PUnit.unit) :=
    (congrArg (fun g => g (r z) ∈ D.P.L.U (p PUnit.unit)) hB).mp (hp PUnit.unit)
  refine Eq.trans ?_ (key Z r z p q hp hq)
  rw [Category.comp_id]
  have m₁ : r z ∈ LB.wchart D.P.L (fun _ : PUnit => spMap φ ≫ eSec D.P.A) p := Set.mem_iInter.2 fun _ => hm
  have m₂ : spMap φ (r z) ∈ LB.wchart D.P.L (fun _ : PUnit => eSec D.P.A) p := Set.mem_iInter.2 fun _ => hm
  exact ((gm_res r z _ m₁ _).trans (gm_pull r (spMap φ) z _ m₂ _)).symm

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableOfPotentialSemiAbelianModel
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS

theorem semistable_of_potModel_semiAbelian : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] (K : Type) [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K] (A : Over (Spec (CommRingCat.of K))) [GrpObj A], IsAbelianScheme A → PotModel V K A (fun _ _ _ G _ => IsSemiAbelian G)) → SemistableReductionZero ∧ SemistableCompleteSplit := by
  intro h
  refine ⟨?_, ?_⟩
  · intro V _ _ _ _ K _ _ _ _ A _ hA
    obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, h1, h2, h3, G, i11, hG, he, hT⟩ :=
      GlobalTheory.T.exists_semiAbelian_torusExtension_of_potentialModel V K A (h V K A hA)
    exact ⟨K', i1, i2, i3, V', i4, i5, i6, i8, i9, i10, h1, h2, h3, G, i11,
      hG.comm, hG.smooth, hG.separated, hG.quasiCompact, he, GlobalTheory.SplitExtTorus.nonempty_torusExt_of_split _ _ hT⟩
  · intro V _ _ _ _ K _ _ _ _ A _ hA
    obtain ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, h1, h2, h3, G, i11, hG, he, hT⟩ :=
      GlobalTheory.T.exists_semiAbelian_torusExtension_of_potentialModel V K A (h V K A hA)
    exact ⟨K', i1, i2, i3, V', i4, i5, i6, i7, i8, i9, i10, inferInstance, h3, G, i11, hG, he, hT⟩

end GlobalTheory.SS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelTorsionRationalOverFractionField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem torsion_descends {B V K L : Scheme.{0}} {A : Over B} {G : Over V} {H : Over K} [GrpObj A] [GrpObj G] [GrpObj H]
    {f : K ⟶ B} {j : K ⟶ V} {ψ : H.left ⟶ A.left} {π : H.left ⟶ G.left}
    (hA : IsGrpPullback H A f ψ) (hG : IsGrpPullback H G j π) (i : L ⟶ K) (n : ℕ)
    (hs : ∀ z : Over.mk (i ≫ f) ⟶ A, z ^ n = 1 → ∃ s : B ⟶ A.left, s ≫ A.hom = 𝟙 B ∧ (i ≫ f) ≫ s = z.left)
    (y : Over.mk (i ≫ j) ⟶ G) (hy : y ^ n = 1) : ∃ x : K ⟶ G.left, i ≫ x = y.left := by
  let y' : Over.mk i ⟶ H := Over.homMk (hG.1.lift y.left i (Over.w y)) (hG.1.lift_snd _ _ _)
  have e₁ : y'.left ≫ π = y.left := hG.1.lift_fst _ _ _
  have e₂ : pushHom hG (Over.mk i) y' = y := Over.OverMorphism.ext e₁
  have inj : Function.Injective (pushHom hG (Over.mk i)) := fun a b h => by
    apply Over.OverMorphism.ext
    apply hG.1.hom_ext
    · exact congrArg (fun z => z.left) h
    · rw [Over.w, Over.w]
  have e₃ : y' ^ n = 1 := inj (by rw [map_pow, e₂, map_one]; exact hy)
  obtain ⟨s, hs₁, hs₂⟩ := hs (pushHom hA (Over.mk i) y') (by rw [← map_pow, e₃, map_one])
  have w : (f ≫ s) ≫ A.hom = 𝟙 K ≫ f := by rw [Category.assoc, hs₁, Category.comp_id, Category.id_comp]
  refine ⟨hA.1.lift (f ≫ s) (𝟙 K) w ≫ π, ?_⟩
  rw [← e₁, ← Category.assoc]
  congr 1
  apply hA.1.hom_ext
  · rw [Category.assoc, hA.1.lift_fst, ← Category.assoc, hs₂]
    rfl
  · rw [Category.assoc, hA.1.lift_snd, Category.comp_id]
    exact (Over.w y').symm

theorem torsion_rational : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (m : ℕ), m ∣ S.r * S.N → ∀ y : Over.mk (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V) ⟶ u.G, y ^ m = 1 → ∃ x : Sp (FractionRing u.V) ⟶ u.G.left, spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ x = y.left := by
  intro o Ω _ _ _ S ρ p _ y₀ u m hm y hy
  have := u.U.gen_hom
  have hA := ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  refine torsion_descends hA (isGrpPullback_pullback u.G (jK u.V)) _ (S.r * S.N) (fun z hz => ?_) y ?_
  · obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) _ z hz
    exact ⟨(ρ.pt a).left, Over.w (ρ.pt a), congrArg (fun t => t.left) ha⟩
  · obtain ⟨c, hc⟩ := hm
    rw [hc, pow_mul, hy, one_pow]

end GlobalTheory.UnitTheta
end

