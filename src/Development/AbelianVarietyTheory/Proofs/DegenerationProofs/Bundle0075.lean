import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAbelianSchemeThick
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionMatchedPartsDimEq
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPrincipalPolarisationAbelianFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib
open GlobalTheory.CoordToExt

theorem lbIso_of_refines {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K K' K'' : Type} [Fintype K] [Fintype K']
    [Fintype K''] {M M' : LB Y} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    (h : Refines M L φ ε) (h' : Refines M' L φ' ε') {ψ : K'' → (Y ⟶ X)} {δ : K'' → ℤ}
    (t : LB.Gen (LB.LinComb L ψ δ)) (ht : t.IsGen)
    (hF : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ X) → U),
      (∏ k, f (ψ k) ^ δ k) * ∏ k, f (φ k) ^ ε k = ∏ k, f (φ' k) ^ ε' k) : LBIso M M' := by
  refine (h'.div h).exists_gen hL (fun U _ f => ?_) t ht
  refine Eq.symm ((Fintype.prod_sum_type _).trans ?_)
  simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rw [← hF U f, mul_inv_cancel_right]

theorem refines_npw {X : Scheme.{0}} (L : LB X) (N : ℕ) :
    Refines (npw L N) L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (N : ℤ)) := by
  refine ⟨fun i _ => i, fun i y hy => Set.mem_iInter.2 fun _ => hy, fun Z r z i j _ _ => ?_⟩
  refine (map_pow _ _ _).trans (Eq.symm ((Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)))
  rw [Category.comp_id]
  rfl

theorem npw_iso {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (N : ℕ) :
    LBIso (npw L N) (LB.LinComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (N : ℤ))) :=
  lbIso_of_refines hL (refines_npw L N) (refines_self _ _) _ isGen_one fun U _ f => by
    rw [Fintype.prod_empty, _root_.one_mul]

theorem lbIso_drop {k : Type} [Field k] {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) (p : Y ⟶ Sp k) (a b : Sp k ⟶ X)
    (u v : Y ⟶ X) (φ : Fin 4 → (Y ⟶ X)) (h₀ : φ 0 = u) (h₁ : φ 1 = p ≫ a) (h₂ : φ 2 = v) (h₃ : φ 3 = p ≫ b) :
    LBIso (LB.LinComb L φ Oε) (LB.LinComb L (K := Fin 2) ![u, v] ![1, -1]) := by
  obtain ⟨e, he⟩ := DVR.exists_gen_of_local (V := k) L hL (K := Fin 2) ![a, b] ![1, -1]
  refine lbIso_of_refines hL (refines_self _ _) (refines_self _ _) _ (DVR.pullGen_isGen _ _ _ e he p) fun U _ f => ?_
  rw [Fin.prod_univ_four, Fin.prod_univ_two, Fin.prod_univ_two, h₀, h₁, h₂, h₃]
  change f (p ≫ a) ^ (1 : ℤ) * f (p ≫ b) ^ (-1 : ℤ) *
    (f u ^ (1 : ℤ) * f (p ≫ a) ^ (-1 : ℤ) * f v ^ (-1 : ℤ) * f (p ≫ b) ^ (1 : ℤ)) = f u ^ (1 : ℤ) * f v ^ (-1 : ℤ)
  simp only [zpow_neg, zpow_one]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_pol : PolBaseChangeSt → ∀ (k : Type) [Field k] (Φ : FibPre k) (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (s : Sp k ⟶ Sp R) (π : Φ.E.B.left ⟶ D.P.A.left), IsGrpPullback Φ.E.B D.P.A s π → ∀ (xe : Φ.E.X → D.X), (∀ χ, LBIso (Φ.E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) → ∀ (N : ℕ), Nonempty (ChartPull Φ.N₀ (npw D.P.L N) π) → ∃ pol : Φ.Pol N, pol.PB.g = D.P.g := by
  rintro hB k _ Φ R _ _ D s π hπ xe hO N ⟨cp⟩
  obtain ⟨P', g, hg, hdim, hm, t, ht⟩ := hB _ _ s D.P
  have gp : IsGrpPullback P'.A D.P.A s g := ⟨hg, fun T x y x₀ y₀ hx hy => by
    rw [(Over.OverMorphism.ext hx : x₀ = toBase hg.w x), (Over.OverMorphism.ext hy : y₀ = toBase hg.w y), ← hm]
    rfl⟩
  obtain ⟨β, hβ, hβπ⟩ := grpPullback_iso hπ gp
  obtain ⟨w, hw⟩ := LBIso.symm ⟨t, ht⟩
  have hL := D.P.isLB
  have hL' := P'.isLB
  have key : ∀ {K : Type} [Fintype K] (φ' : K → (Φ.E.B.left ⟶ P'.A.left)) (φ : K → (Φ.E.B.left ⟶ D.P.A.left))
      (ε : K → ℤ), (∀ a, φ a = φ' a ≫ g) → LBIso (LB.LinComb D.P.L φ ε) (LB.LinComb P'.L φ' ε) := by
    intro K _ φ' φ ε h
    obtain rfl : φ = fun a => φ' a ≫ g := funext h
    exact (iso_linComb ((isGen_iff w).1 hw) φ' ε).symm
  have hc : ∀ x : 𝟙_ (Over (Sp R)) ⟶ D.P.A, (s ≫ x.left) ≫ D.P.A.hom = 𝟙 _ ≫ s := fun x => by
    rw [Category.assoc, Over.w x, Category.id_comp]
    exact Category.comp_id _
  let c : Φ.E.X → (baseOver (Sp k) ⟶ P'.A) := fun χ =>
    Over.homMk (hg.lift (s ≫ (D.c (xe χ)).left) (𝟙 _) (hc _)) (hg.lift_snd _ _ _)
  have hcg : ∀ χ, (c χ).left ≫ g = s ≫ (D.c (xe χ)).left := fun χ => hg.lift_fst _ _ _
  have hu : ∀ x : 𝟙_ (Over (Sp R)) ⟶ D.P.A, π ≫ (toUnit D.P.A ≫ x).left = Φ.E.B.hom ≫ s ≫ x.left := fun x => by
    rw [← Category.assoc, ← hπ.1.w, Category.assoc]
    rfl
  refine ⟨⟨P', β, hβ, c, ?_, fun χ => ?_⟩, hdim⟩
  · have h₁ : LBIso Φ.N₀ (LB.LinComb D.P.L (K := PUnit) (fun _ => π) (fun _ => (N : ℤ))) :=
      LBIso.chartPull cp (chartPullSame _ _ _ _ π fun _ => (Category.comp_id _).symm) (npw_iso hL N)
    have h₂ := key (K := PUnit) (fun _ => β.hom.left) (fun _ => π) (fun _ => (N : ℤ)) fun _ => hβπ.symm
    have h₃ : LBIso (LB.LinComb P'.L (K := PUnit) (fun _ => β.hom.left) (fun _ => (N : ℤ)))
        ((lbPow P'.L N).pull β.hom.left) :=
      LBIso.chartPull (chartPullId _) (chartPullOut P'.L _ _ β.hom.left _ fun _ => (Category.comp_id _).symm)
        (exists_iso hL' rfl _)
    exact LBIso.trans Φ.isLB (DVR.linComb_isLB _ hL _ _) (pull_isLB (DVR.linComb_isLB _ hL' _ _) _) h₁
      (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _)
        (pull_isLB (DVR.linComb_isLB _ hL' _ _) _) h₂ h₃)
  · let q : Φ.E.B ⟶ baseOver (Sp k) := Over.homMk Φ.E.B.hom (Category.comp_id _)
    have e₀ : π ≫ D.Oφ (𝟙 D.P.A) (xe χ) 0 = (β.hom * (q ≫ c χ)).left ≫ g := by
      let ρ : Over.mk (Φ.E.B.hom ≫ s) ⟶ D.P.A := Over.homMk π hπ.1.w
      refine Eq.trans ?_ (gp.2 Φ.E.B β.hom (q ≫ c χ) (ρ ≫ 𝟙 _) (ρ ≫ toUnit _ ≫ D.c (xe χ))
        ((Category.comp_id _).trans hβπ.symm) ?_)
      · exact congrArg (fun f => f.left) (MonObj.comp_mul ρ (𝟙 _) (toUnit _ ≫ D.c (xe χ)))
      · refine (hu _).trans ?_
        rw [← hcg]
        exact (Category.assoc _ _ _).symm
    have h₁ := lbIso_drop hL Φ.E.B.hom (s ≫ (D.c (xe χ)).left) (s ≫ (η[D.P.A]).left) _ π
      (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) e₀ (hu _) (Category.comp_id _) (hu _)
    have h₂ := key (K := Fin 2) ![(β.hom * (q ≫ c χ)).left, β.hom.left] ![(β.hom * (q ≫ c χ)).left ≫ g, π] ![1, -1]
      (fun a => by
        fin_cases a
        · rfl
        · exact hβπ.symm)
    exact LBIso.trans (Φ.E.O χ).isLB (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) (hO χ)
      (LBIso.trans (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL _ _) (DVR.linComb_isLB _ hL' _ _) h₁ h₂)

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_cancel_of_eq {X X' X'' : Scheme.{0}} {L : LB X} {L' : LB X'} {L'' : LB X''} {F : X' ⟶ X}
    {F' : X'' ⟶ X'} {F'' : X'' ⟶ X} (e : F' ≫ F = F'') (hL : L.IsLB) (hL' : L'.IsLB) (hL'' : L''.IsLB)
    (w : LB.Iso L' (L.pull F)) (w'' : LB.Iso L'' (L.pull F'')) (hw : PGen w) (hw'' : PGen w'')
    {Y Y' Y'' : Scheme.{0}} {φ : Y ⟶ X} {φ' : Y' ⟶ X'} {φ'' : Y'' ⟶ X''}
    {t : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => φ) (fun _ => 1))}
    {t' : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => φ') (fun _ => 1))}
    {t'' : LB.Gen (LB.LinComb L'' (K := PUnit) (fun _ => φ'') (fun _ => 1))}
    {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'} {h'' : Y'' ⟶ Y} (eh : h' ≫ h = h'') (hc : φ'' ≫ F' = h' ≫ φ')
    (H : PMaps w _ _ _ t' t h) (H'' : PMaps w'' _ _ _ t'' t h'') :
    ∃ w' : LB.Iso L'' (L'.pull F'), PGen w' ∧ PMaps w' _ _ _ t'' t' h' ∧
      ∀ (Z : Scheme.{0}) (z : Z) J J' J'', Good L z J → Good L' z J' → Good L'' z J'' → ∀ x : Z ⟶ X'',
        om w'' z J J'' x = om w z J J' (x ≫ F') * om w' z J' J'' x := by
  subst e eh
  obtain ⟨w', T⟩ := exists_cancel hL w w'' hw hw'' hL' hL''
  refine ⟨w', T.pgen_cancel hL hw hw'', T.pmaps_cancel hL (fun _ => hc) H H'', fun Z z J J' J'' hJ hJ' hJ'' x => ?_⟩
  rw [om, om, om, Category.assoc]
  exact T Z x z _ _ _ (hJ (x ≫ F' ≫ F)) (hJ' (x ≫ F')) (hJ'' x)

theorem exists_isPullDeg_cancel : ∀ (K₀ K₁ K : Type) [Field K₀] [Field K₁] [Field K] (α : K₀ →+* K₁) (β : K₁ →+* K) (D₀ : DegPre K₀) (D₁ : DegPre K₁) (D : DegPre K) (h₁ : IsPullDeg α D₀ D₁) (h : IsPullDeg (β.comp α) D₀ D), ∃ hD : IsPullDeg β D₁ D, PsiEvenPull.proj hD ≫ PsiEvenPull.proj h₁ = PsiEvenPull.proj h := by
  intro K₀ K₁ K _ _ _ α β D₀ D₁ D h₁ h
  have p₁ : IsGrpPullback D₁.P.A D₀.P.A (spMap α) (proj h₁) := pull_grp h₁
  have sc : spMap β ≫ spMap α = spMap (β.comp α) := (spMap_comp α β).symm
  have p : IsGrpPullback D.P.A D₀.P.A (spMap β ≫ spMap α) (proj h) := (pull_grp h).congr sc.symm rfl
  obtain ⟨Φ, e₁, e₂⟩ : ∃ Φ : D.P.A.left ⟶ D₁.P.A.left, Φ ≫ proj h₁ = proj h ∧ Φ ≫ D₁.P.A.hom = D.P.A.hom ≫ spMap β :=
    ⟨p₁.1.lift (proj h) (D.P.A.hom ≫ spMap β) (p.1.w.trans (Category.assoc _ _ _).symm), p₁.1.lift_fst _ _ _,
      p₁.1.lift_snd _ _ _⟩
  have gp : IsGrpPullback D.P.A D₁.P.A (spMap β) Φ := IsGrpPullback.cancel p₁ (p.congr rfl e₁.symm) e₂
  obtain ⟨w, hw, hr, T⟩ := exists_cancel_of_eq e₁ D₀.P.isLB D₁.P.isLB D.P.isLB h₁.w h.w ((isGen_iff _).1 h₁.w_gen)
    ((isGen_iff _).1 h.w_gen) sc (cubeMapOf gp).e_comm (pmaps_rig h₁) (pmaps_rig h)
  let xe : D.X ≃+ D₁.X := h.xe.trans h₁.xe.symm
  have hxe : ∀ x, h₁.xe (xe x) = h.xe x := fun x => h₁.xe.apply_symm_apply _
  have hc : ∀ x, (D.c x).left ≫ Φ = spMap β ≫ (D₁.c (xe x)).left := fun x => by
    apply p₁.1.hom_ext
    · rw [Category.assoc, e₁, Category.assoc, h₁.c_pr, hxe]
      exact (h.c_pr x).trans ((congrArg (· ≫ _) sc.symm).trans (Category.assoc _ _ _))
    · rw [Category.assoc, e₂, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨hD, hΦ, -, -⟩ := exists_isPullDeg_of_val β D₁ D gp w hw hr xe hc (fun x z J₁ J hJ₁ hJ => by
    obtain ⟨J₀, hJ₀⟩ := DegPull.exists_good' D₀.P.isLB z
    have sβ : jK K ≫ spMap β = genMap β.injective ≫ jK K₁ :=
      (Category.id_comp _).symm.trans (fracMap_sq β.injective)
    have sα : jK K₁ ≫ spMap α = genMap α.injective ≫ jK K₀ :=
      (Category.id_comp _).symm.trans (fracMap_sq α.injective)
    have q₁ : genMap β.injective ≫ jK K₁ ≫ spMap α = (genMap β.injective ≫ genMap α.injective) ≫ jK K₀ :=
      (congrArg (_ ≫ ·) sα).trans (Category.assoc _ _ _).symm
    have q : 𝟙 (TK K).left ≫ jK K ≫ spMap (β.comp α) = (genMap β.injective ≫ genMap α.injective) ≫ jK K₀ :=
      (Category.id_comp _).trans ((congrArg (_ ≫ ·) sc.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) sβ).trans ((Category.assoc _ _ _).trans q₁))))
    have v := psi_val h _ _ q hJ₀ hJ x
    have v₁ := psi_val h₁ _ _ q₁ hJ₀ hJ₁ (xe x)
    have hx : D.xK x ≫ Φ = genMap β.injective ≫ D₁.xK (xe x) := by
      show (jK K ≫ (D.c x).left) ≫ Φ = genMap β.injective ≫ jK K₁ ≫ (D₁.c (xe x)).left
      rw [Category.assoc, hc, ← Category.assoc, sβ, Category.assoc]
    rw [hxe, v, Category.id_comp, T _ z J₀ J₁ J hJ₀ hJ₁ hJ, hx, mul_inv, _root_.mul_assoc] at v₁
    exact (mul_left_cancel v₁).symm)
  exact ⟨hD, hΦ ▸ e₁⟩

end GlobalTheory.FieldPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatLog
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.NormValuation

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in
private lemma exists_rat_norm_eq_rpow {p : ℕ} [Fact p.Prime] {x : PadicAlgCl p} (hx : x ≠ 0) :
    ∃ t : ℚ, ‖x‖ = (p : ℝ) ^ (t : ℝ) := by
  have hint : IsIntegral ℚ_[p] x := Algebra.IsIntegral.isIntegral x
  have hc := minpoly.coeff_zero_ne_zero hint hx
  refine ⟨(-((minpoly ℚ_[p] x).coeff 0).valuation : ℚ) / (minpoly ℚ_[p] x).natDegree, ?_⟩
  rw [← PadicAlgCl.spectralNorm_eq, spectralNorm.spectralNorm_eq_norm_coeff_zero_rpow,
    Padic.norm_eq_zpow_neg_valuation hc, ← Real.rpow_intCast,
    ← Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  ring

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing in
open scoped CategoryTheory.Obj in
open Classical in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem _root_.GlobalTheory.NormValuation.main : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra (FractionRing V) (PadicAlgCl p)], (∀ x : FractionRing V, ‖algebraMap _ (PadicAlgCl p) x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → ∀ ϖ : V, Irreducible ϖ → ∃ v : AddValuation (PadicAlgCl p) (WithTop ℚ), _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver ϖ (PadicAlgCl p) v ∧ _root_.GlobalTheory.ZH.NormVal (algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)) v ∧ ∀ x : PadicAlgCl p, (0 ≤ v x ↔ ‖x‖ ≤ 1) ∧ (v x = 0 ↔ ‖x‖ = 1) := by
  intro p _ V _ _ _ _ hV ϖ hϖ
  set π : PadicAlgCl p :=
    algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ) with hπ
  have hinjV := IsFractionRing.injective V (FractionRing V)
  have hπne : π ≠ 0 := by
    rw [hπ, map_ne_zero]
    exact fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hπle : ‖π‖ ≤ 1 := (hV _).2 ⟨ϖ, rfl⟩
  have hπlt : ‖π‖ < 1 := by
    refine lt_of_le_of_ne hπle fun h1 => hϖ.not_isUnit ?_
    have hle : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv, ← hπ, h1, inv_one]
    obtain ⟨a, ha⟩ := (hV _).1 hle
    refine isUnit_iff_exists_inv.2 ⟨a, hinjV ?_⟩
    rw [map_mul, ha, map_one]
    exact mul_inv_cancel₀ fun h => hϖ.ne_zero (hinjV (by rw [h, map_zero]))
  have hb0 : 0 < ‖π‖ := norm_pos_iff.2 hπne
  have hle : ∀ s t : ℝ, ‖π‖ ^ s ≤ ‖π‖ ^ t ↔ t ≤ s := fun s t =>
    Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hπlt
  have hinj : ∀ s t : ℝ, ‖π‖ ^ s = ‖π‖ ^ t → s = t := fun s t h =>
    le_antisymm ((hle t s).1 h.ge) ((hle s t).1 h.le)
  obtain ⟨s, hs⟩ := exists_rat_norm_eq_rpow hπne
  have hs0 : (s : ℝ) ≠ 0 := by
    intro h0
    rw [h0, Real.rpow_zero] at hs
    exact hπlt.ne hs
  obtain ⟨r, hexp⟩ : ∃ r : PadicAlgCl p → ℚ, ∀ x, x ≠ 0 → ‖x‖ = ‖π‖ ^ (r x : ℝ) := by
    refine ⟨fun x => if h : x = 0 then 0 else (exists_rat_norm_eq_rpow h).choose / s, ?_⟩
    intro x hx
    simp only [dif_neg hx]
    rw [hs, ← Real.rpow_mul (Nat.cast_nonneg _)]
    push_cast
    rw [mul_div_cancel₀ _ hs0]
    exact (exists_rat_norm_eq_rpow hx).choose_spec
  have hr_one : r 1 = 0 := by
    have h := hexp 1 one_ne_zero
    rw [norm_one, ← Real.rpow_zero ‖π‖] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_mul : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → r (x * y) = r x + r y := by
    intro x y hx hy
    have h := hexp (x * y) (mul_ne_zero hx hy)
    rw [norm_mul, hexp x hx, hexp y hy, ← Real.rpow_add hb0] at h
    exact_mod_cast (hinj _ _ h).symm
  have hr_add : ∀ x y : PadicAlgCl p, x ≠ 0 → y ≠ 0 → x + y ≠ 0 →
      min (r x) (r y) ≤ r (x + y) := by
    intro x y hx hy hxy
    have h := (PadicAlgCl.isNonarchimedean p) x y
    rw [hexp x hx, hexp y hy, hexp _ hxy] at h
    rcases le_total (r x) (r y) with hxy' | hxy'
    · rw [min_eq_left hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r x : ℝ) :=
        max_eq_left ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
    · rw [min_eq_right hxy']
      have hm : max (‖π‖ ^ (r x : ℝ)) (‖π‖ ^ (r y : ℝ)) = ‖π‖ ^ (r y : ℝ) :=
        max_eq_right ((hle _ _).2 (by exact_mod_cast hxy'))
      rw [hm, hle] at h
      exact_mod_cast h
  set w : PadicAlgCl p → WithTop ℚ := fun x => if x = 0 then ⊤ else (r x : WithTop ℚ) with hw
  have hw0 : w 0 = ⊤ := by simp [hw]
  have hw1 : w 1 = 0 := by simp [hw, hr_one]
  have hwadd : ∀ x y, min (w x) (w y) ≤ w (x + y) := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    by_cases hxy : x + y = 0
    · simp [hw, hxy]
    simp only [hw, if_neg hx, if_neg hy, if_neg hxy]
    rw [← WithTop.coe_min, WithTop.coe_le_coe]
    exact hr_add x y hx hy hxy
  have hwmul : ∀ x y, w (x * y) = w x + w y := by
    intro x y
    by_cases hx : x = 0
    · simp [hw, hx]
    by_cases hy : y = 0
    · simp [hw, hy]
    simp only [hw, if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy)]
    rw [hr_mul x y hx hy, WithTop.coe_add]
  let v : AddValuation (PadicAlgCl p) (WithTop ℚ) := AddValuation.of w hw0 hw1 hwadd hwmul
  have hv : ∀ x, v x = w x := fun x => rfl
  have hunit : ∀ u : Vˣ,
      ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ = 1 := by
    intro u
    have h1 := (hV (algebraMap V (FractionRing V) u)).2 ⟨u, rfl⟩
    have h2 := (hV (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))).2 ⟨_, rfl⟩
    have h3 : ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) u)‖ *
        ‖algebraMap (FractionRing V) (PadicAlgCl p) (algebraMap V (FractionRing V) (u⁻¹ : Vˣ))‖
          = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) u)), norm_nonneg (algebraMap (FractionRing V) (PadicAlgCl p)
      (algebraMap V (FractionRing V) (u⁻¹ : Vˣ)))]
  refine ⟨v, ?_, ?_, ?_⟩
  · unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.ValOver
    intro c n hc
    unfold _root_.ReciprocityTheory.ChartRestriction.G.DVR.HasVal at hc
    obtain ⟨u, rfl⟩ := hc
    have hne : algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u) ≠ 0 := by
      rw [map_mul, map_zpow₀]
      refine mul_ne_zero (zpow_ne_zero _ hπne) ?_
      intro h
      have := hunit u
      rw [h, norm_zero] at this
      exact zero_ne_one this
    rw [hv]
    simp only [hw, if_neg hne]
    have h2 : ‖algebraMap (FractionRing V) (PadicAlgCl p)
        ((algebraMap V (FractionRing V)) ϖ ^ n * (algebraMap V (FractionRing V)) u)‖ =
          ‖π‖ ^ (n : ℝ) := by
      rw [map_mul, map_zpow₀, norm_mul, norm_zpow, hunit u, _root_.mul_one, ← hπ,
        Real.rpow_intCast]
    have := hinj _ _ ((hexp _ hne).symm.trans h2)
    rw [WithTop.coe_eq_coe]
    exact_mod_cast this
  · unfold _root_.GlobalTheory.ZH.NormVal
    refine ⟨hb0, hπlt, fun x q => ?_⟩
    by_cases hx : x = 0
    · subst hx
      rw [hv, hw0, norm_zero]
      constructor
      · intro h; exact absurd h WithTop.top_ne_coe
      · intro h; exact absurd h.symm (Real.rpow_pos_of_pos hb0 _).ne'
    rw [hv]
    simp only [hw, if_neg hx, WithTop.coe_eq_coe]
    rw [hexp x hx]
    constructor
    · rintro rfl; rfl
    · intro h; exact_mod_cast hinj _ _ h
  · intro x
    by_cases hx : x = 0
    · subst hx
      simp [hv, hw0]
    rw [hv]
    simp only [hw, if_neg hx]
    rw [hexp x hx]
    have h1 := hle (r x : ℝ) 0
    rw [Real.rpow_zero] at h1
    refine ⟨?_, ?_⟩
    · rw [h1, WithTop.coe_nonneg]
      exact_mod_cast Iff.rfl
    · rw [WithTop.coe_eq_zero]
      constructor
      · rintro h; rw [h]; simp
      · intro h
        have := hinj (r x : ℝ) 0 (by rw [Real.rpow_zero]; exact h)
        exact_mod_cast this

end GlobalTheory.NormValuation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRatioDescendsDegenerationPsiFamily
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

noncomputable section
namespace GlobalTheory.FieldPull
open GlobalTheory.ArcPull GlobalTheory.PsiEvenPull

theorem exists_psi_ratio {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (ψ : TauTwist.PsiFam D)
    (hψ : ∀ χ, (ψ χ).IsGen) (χ : D.X) : ∃ u : (FractionRing R)ˣ, ∀ (z : (TK R).left) J, Good D.P.L z J →
      val (D.psi χ) (𝟙 _) z J = TauTwist.unitAt (A := FractionRing R) (Z := (TK R).left) (𝟙 _) z u * val (ψ χ) (𝟙 _) z J :=
  TauTwist.exists_ratio (F := FractionRing R) D.P.isLB (fun _ _ _ => rfl) (D.psi_gen χ) (hψ χ)

theorem unitAt_genMap {K₁ K : Type} [Field K₁] [Field K] (β : K₁ →+* K) (z : (TK K).left) (v : (FractionRing K₁)ˣ) :
    TauTwist.unitAt (A := FractionRing K₁) (genMap β.injective) z v =
      TauTwist.unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (Units.map (fracMap β.injective).toMonoidHom v) :=
  (congrArg (fun r => TauTwist.unitAt (A := FractionRing K₁) r z v) (Category.id_comp _).symm).trans
    (TauTwist.unitAt_spMap (𝟙 _) (fracMap β.injective) z v)

theorem exists_isPullDeg_rescale {K₁ K : Type} [Field K₁] [Field K] (β : K₁ →+* K) (D₁ : DegPre K₁) (D : DegPre K)
    (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ))
    (q : D₁.X → (FractionRing K₁)ˣ)
    (hq : ∀ χ (z : (TK K).left) J, Good D.P.L z J → val (D.psi χ) (𝟙 _) z J =
      TauTwist.unitAt (A := FractionRing K) (Z := (TK K).left) (𝟙 _) z (Units.map (fracMap β.injective).toMonoidHom (q (h.xe χ))) *
        val (ψ χ) (𝟙 _) z J) :
    ∃ hD : IsPullDeg β (TauTwist.rescale D₁ q) D, proj hD = proj h := by
  have key : ∀ (x : D.X) (z : (TK K).left) J J', Good D₁.P.L z J → Good D.P.L z J' →
      val ((TauTwist.rescale D₁ q).psi (h.xe x)) (genMap β.injective) z J =
        (om h.w z J J' (D.xK x))⁻¹ * val (D.psi x) (𝟙 _) z J' := fun x z J J' hJ hJ' => by
    have e := psi_val (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h (genMap β.injective) (𝟙 _) (fracMap_sq β.injective) hJ hJ' x
    rw [Category.id_comp] at e
    refine (TauTwist.val_psi_rescale q (h.xe x) _ hJ).trans ((congrArg₂ (· * ·) (unitAt_genMap β z _) e).trans ?_)
    exact (mul_left_comm _ _ _).trans (congrArg₂ (· * ·) rfl (hq x z J' hJ')).symm
  obtain ⟨hD, hp, -, -⟩ := exists_isPullDeg_of_val β (TauTwist.rescale D₁ q) D (Φ := proj (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h)
    (pull_grp (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h) h.w
    ((isGen_iff h.w).1 h.w_gen) (pmaps_rig (D := D₁) (D' := TauTwist.withPsi D ψ hψ) h) h.xe h.c_pr key
  exact ⟨hD, hp⟩

theorem exists_ratio_descends (K : Type) [Field K] (D : DegPre K) (ψ : TauTwist.PsiFam D) (hψ : ∀ χ, (ψ χ).IsGen) :
    ∃ a : D.X → K, ∀ (K₁ : Type) [Field K₁] (β : K₁ →+* K) (D₁ : DegPre K₁)
      (h : IsPullDeg β D₁ (TauTwist.withPsi D ψ hψ)), (∀ χ, a χ ∈ Set.range β) →
      ∃ (ψ₁ : TauTwist.PsiFam D₁) (hψ₁ : ∀ χ, (ψ₁ χ).IsGen) (hD : IsPullDeg β (TauTwist.withPsi D₁ ψ₁ hψ₁) D),
        PsiEvenPull.proj hD = PsiEvenPull.proj h := by
  choose u hu using exists_psi_ratio D ψ hψ
  refine ⟨fun χ => FractionRing.algEquiv K K (u χ).val, fun K₁ _ β D₁ h ha => ?_⟩
  choose a₁ ha₁ using ha
  have key : ∀ χ, fracMap β.injective (algebraMap K₁ (FractionRing K₁) (a₁ χ)) = (u χ).val := fun χ => by
    rw [fracMap_algebraMap, ha₁]
    exact (FractionRing.algEquiv K K).injective ((FractionRing.algEquiv K K).commutes _)
  have hne : ∀ χ, algebraMap K₁ (FractionRing K₁) (a₁ χ) ≠ 0 := fun χ e => (u χ).ne_zero (by
    rw [← key, e, map_zero])
  obtain ⟨q, hq⟩ : ∃ q : D₁.X → (FractionRing K₁)ˣ,
      ∀ χ, Units.map (fracMap β.injective).toMonoidHom (q (h.xe χ)) = u χ :=
    ⟨fun y => Units.mk0 _ (hne (h.xe.symm y)), fun χ => Units.ext (by
      show fracMap β.injective (algebraMap K₁ (FractionRing K₁) (a₁ (h.xe.symm (h.xe χ)))) = _
      rw [AddEquiv.symm_apply_apply, key])⟩
  obtain ⟨hD, hp⟩ := exists_isPullDeg_rescale β D₁ D ψ hψ h q fun χ z J hJ => by
    rw [hq]; exact hu χ z J hJ
  exact ⟨_, _, hD, hp⟩

end GlobalTheory.FieldPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionPullbackMulGenerator
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem gm_chartPull_g {Y Y' Z : Scheme.{0}} {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y} (a : ChartPull A' A h)
    (r : Z ⟶ Y') (z : Z) (i j : A'.ι) (hi : r z ∈ A'.U i) (hj : r z ∈ A'.U j) :
    gm r z (A'.U i ⊓ A'.U j) (A'.g i j) =
      gm (r ≫ h) z (A.U (a.idx i) ⊓ A.U (a.idx j)) (A.g (a.idx i) (a.idx j)) := by
  have le : A'.U i ⊓ A'.U j ≤ h ⁻¹ᵁ (A.U (a.idx i) ⊓ A.U (a.idx j)) := fun y hy => ⟨a.le i hy.1, a.le j hy.2⟩
  have e : A'.g i j = res le (pullU h _ (A.g (a.idx i) (a.idx j))) := unit_ext fun y hy =>
    (a.g y i j hy.1 hy.2).trans ((gm_res (𝟙 Y') y le hy _).trans
      ((gm_pull (𝟙 Y') h y _ (le hy) _).trans (by rw [Category.id_comp]))).symm
  have hm : r z ∈ A'.U i ⊓ A'.U j := ⟨hi, hj⟩
  rw [e]
  exact (gm_res r z le hm _).trans (gm_pull r h z _ (le hm) _)

theorem exists_red : ∀ (k : Type) [Field k] [IsAlgClosed k] (Φ : FibPre k) (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (π : Φ.E.B.left ⟶ Y) (N : ℕ) (c : ChartPull Φ.N₀ (npw L N) π) (K K' : Type) [Fintype K] [Fintype K'] (ψ : K → (Φ.E.B.left ⟶ Y)) (ε : K → ℤ) (φt : K' → (Φ.G.left ⟶ Y)) (εt : K' → ℤ) (t : LB.Gen (LB.LinComb L φt εt)), t.IsGen → FormEq (Sum.elim (fun a => Φ.D.q.left ≫ ψ a) φt) (Sum.elim ε εt) (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => (N : ℤ)) → ∀ b : LB.Sec (LB.LinComb L ψ ε), ∃ φ : (Φ.H 1).Sec, UFib.Red Φ c t b φ := by
  intro k _ _ Φ Y L hL π N c K K' _ _ ψ ε φt εt t ht hF b
  obtain ⟨s, hs⟩ := exists_sec hL hF (pullMulSec b Φ.D.q.left t ht)
  have le : ∀ l : Φ.N₀.ι, Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l ≤
      LB.wchart L (fun _ : Fin 1 => Φ.D.q.left ≫ π) (fun _ => c.idx l) :=
    fun l y hy => Set.mem_iInter.2 fun _ => c.le l hy
  refine ⟨⟨fun l => (Φ.G.left.presheaf.map (homOfLE (le l)).op).hom (s.f (fun _ => c.idx l)),
    fun l l' => fn_ext fun y hy => ?_⟩, fun Z r z J hJ l hl e => ?_⟩
  · refine ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le l) hy.1 _)).trans
      ((sec_trans s (𝟙 _) y (le l hy.1) (le l' hy.2)).trans (Eq.trans ?_ ((gs_mul (𝟙 _) y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _)
          ((gs_res (𝟙 _) y _ hy _).trans (gs_res (𝟙 _) y (le l') hy.2 _)))).symm))
    refine congrArg₂ (· * ·) (congrArg Units.val ?_) rfl
    have e₁ := gm_chartPull_g c (𝟙 _ ≫ Φ.D.q.left) y l l' hy.1 hy.2
    have e₂ := gm_pull (𝟙 _) Φ.D.q.left y (Φ.N₀.U l ⊓ Φ.N₀.U l') ⟨hy.1, hy.2⟩ (Φ.N₀.g l l')
    refine Eq.trans ?_ (((congrArg (gm (𝟙 _) y _) (pow_one _)).trans e₂).trans e₁).symm
    refine Eq.trans ?_ (map_pow _ _ _).symm
    refine (Fintype.prod_unique _).trans ((zpow_natCast _ _).trans ?_)
    rw [Category.assoc]
    rfl
  · refine (gs_res r z (le l) hl _).trans ?_
    rw [← sval_pullMulSec b Φ.D.q.left t ht r z hJ, ← hs Z r z J hJ]
    exact (sval_of s r z J (fun _ => c.idx l) (fun _ => e)).symm

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionMatchedPartsDimEqStatement
section
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaRecognition_matched_parts_dim_eq : AllMatch fun μ g g' => μ.A ∧ g = g' := by
  first | exact @GlobalTheory.MatchParts.match_parts | exact GlobalTheory.MatchParts.match_parts | (intros; apply GlobalTheory.MatchParts.match_parts <;> assumption)
end

