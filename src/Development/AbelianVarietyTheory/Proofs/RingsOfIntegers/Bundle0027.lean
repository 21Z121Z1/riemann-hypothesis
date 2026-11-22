import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0096
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0025
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecIsMulOfSval
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.LevelOneIdeal

theorem exists_psi_val {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} (D : DegPre R) (χ : D.X)
    (h : D.PsiIn χ I) :
    ∃ (e : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))), e.IsGen ∧ ∃ a ∈ I,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
        (val (D.psi χ) r z J).val = cst (r ≫ jK R) z a * (val e (r ≫ jK R) z J).val := by
  have hL := D.P.isLB
  obtain ⟨e, he⟩ := exists_gen_of_local (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  obtain ⟨j, hj⟩ := exists_chart_top (V := R) D.P.L hL (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1)
  have le : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j := hj.ge
  have hx : D.xK χ = jK R ≫ (D.c χ).left := by
    simp [DegPre.xK, ptK]
  have le' : jK R ⁻¹ᵁ ⊤ ≤ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := fun y _ =>
    Set.mem_iInter.2 fun k => by
      rw [hx]; exact Set.mem_iInter.1 (le (show (jK R) y ∈ (⊤ : (Spec (CommRingCat.of R)).Opens) from trivial)) k
  obtain ⟨r₀, hr₀, hψ⟩ := h j ⊤ (isAffineOpen_top _) (le.trans (LB.wchart_le _ _ _ PUnit.unit)) le'
  have hto : ∀ a, DegPre.toOpen (R := R) ⊤ a = (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a := fun a => by
    simp [DegPre.toOpen]
  have hs : Function.Surjective (DegPre.toOpen (R := R) ⊤) := fun x => by
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 x
    exact ⟨a, (hto a).trans ha⟩
  obtain ⟨a₀, ha₀, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hs).1 hr₀
  obtain ⟨b, hb⟩ := hs (res le (e.s j))⁻¹.val
  refine ⟨e, he, a₀ * b, I.mul_mem_right _ ha₀, fun Z r z J hJ => ?_⟩
  have m₁ : r z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j := le' trivial
  have m₂ : (r ≫ jK R) z ∈ LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j := le trivial
  have e₁ : val (D.psi χ) r z J = _ := gen_trans (D.psi_gen χ) r z (hJ.mem _ r) m₁
  have e₂ : val e (r ≫ jK R) z J = _ := gen_trans he (r ≫ jK R) z (hJ.mem _ _) m₂
  have e₃ : trF (L := D.P.L) (K := PUnit) (fun _ => D.xK χ) (fun _ => -1) r z (fun _ => J (r ≫ D.xK χ)) j =
      trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j := by
    have hq : r ≫ D.xK χ = (r ≫ jK R) ≫ (D.c χ).left :=
      (congrArg (r ≫ ·) hx).trans (Category.assoc _ _ _).symm
    simp only [trF]
    rw [hq]
  have e₄ : (gm r z (LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) j) ((D.psi χ).s j)).val = cst (r ≫ jK R) z a₀ := by
    refine (gs_unit r z _ m₁ _).symm.trans ((gs_res r z le' trivial _).symm.trans ?_)
    refine (congrArg (gs r z _) hψ.symm).trans ((gs_pull r (jK R) z ⊤ trivial _).trans ?_)
    rw [hto]; rfl
  have e₅ : cst (r ≫ jK R) z b *
      (gm (r ≫ jK R) z (LB.wchart D.P.L (K := PUnit) (fun _ => (D.c χ).left) j) (e.s j)).val = 1 := by
    rw [cst, ← hto, hb, gs_unit _ z ⊤ trivial, map_inv]
    exact (congrArg₂ (fun q c => q⁻¹.val * c) (gm_res (r ≫ jK R) z le trivial (e.s j)) rfl).trans (Units.inv_mul _)
  have e₆ : cst (r ≫ jK R) z (a₀ * b) = cst (r ≫ jK R) z a₀ * cst (r ≫ jK R) z b := by
    rw [cst, map_mul, gs_mul _ z ⊤ trivial]; rfl
  rw [e₁, e₂, e₆, Units.val_mul, Units.val_mul]
  erw [e₃, e₄]
  linear_combination (-(cst (r ≫ jK R) z a₀ * (trF (L := D.P.L) (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1) (r ≫ jK R) z
        (fun _ => J ((r ≫ jK R) ≫ (D.c χ).left)) j).val)) * e₅

theorem val_famMult_one {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {F : Type} [Field F]
    [Algebra (FractionRing R) F] {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F) {z : T.left}
    {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (χ : D.X) :
    val (DegPre.famMult D F 1 χ 0) σ.left z J =
      val (D.psi χ) (σ.left ≫ jFK (R := R) F) z J * val D.rigK (σ.left ≫ jFK (R := R) F) z J := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have t0 := tau_mul σ hJ hB 0 0 χ
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t0
  have τ0 : val (D.tau 0 χ) (σ.left ≫ jFK (R := R) F) z J = 1 := mul_eq_left.1 t0.symm
  rw [val_famMult σ hJ, UUA.val_powGen', UUA.val_powGen', tau_symm σ hJ, τ0, _root_.one_mul, pow_one, pow_one]

theorem secIsMul_of_sval {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {R : Type} [CommRing R] (p : Y ⟶ Spec (CommRingCat.of R)) {a : R}
    {s s' : LB.Sec (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (hinj : ∀ W : Y.Opens, Function.Injective (h.app W))
    (H : ∀ y J, Good L y J → sval s' h y J = cst (h ≫ p) y a * sval s h y J) : SecIsMul p a s' s := by
  intro j
  refine hinj _ (fn_ext fun y hy => ?_)
  choose J hJ using fun ψ : Y' ⟶ X => exists_chart hL (ψ y)
  have hJ' : Good L y J := hJ
  have hy' : h y ∈ LB.wchart L φ j := hy
  have m := hJ'.mem φ h
  have e₃ : gs h y (LB.wchart L φ j) (Out.resTop _ (scal p a)) = cst (h ≫ p) y a :=
    (gs_res _ y le_top hy' _).trans (gs_pull _ p y ⊤ trivial _)
  refine (gs_pull (𝟙 Y') h y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 Y') h y _ hy _).symm)
  rw [Category.id_comp]
  refine (sec_trans s' _ y hy' m).trans (Eq.trans ?_ ((gs_mul _ y _ hy' _ _).trans
    (congrArg₂ (· * ·) e₃ (sec_trans s _ y hy' m))).symm)
  exact (congrArg _ (H y J hJ')).trans (mul_left_comm _ _ _)

theorem main : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R) (D : DegData R I) (E : Fam D.toPre (FractionRing R) 1) (g : ∀ α : D.toPre.X, D.toPre.SecB 1 α), (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε 1) (E.s α) (D.toPre.famφB α) (DegPre.famε 1) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1) → ∀ χ, χ ≠ 0 → ∃ a ∈ I, ∃ g' : D.toPre.SecB 1 χ, SecIsMul D.toPre.P.A.hom a (g χ) g' := by
  intro hG R _ _ _ I D E g hg χ hχ
  have hL := D.toPre.P.isLB
  obtain ⟨e, he, a, ha, hψ⟩ := exists_psi_val D.toPre χ (D.psi_pos χ hχ)
  refine ⟨a, ha, ?_⟩
  suffices H : ∃ g' : D.toPre.SecB 1 (0 + 1 • χ), SecIsMul D.toPre.P.A.hom a (g (0 + 1 • χ)) g' by
    rwa [zero_add, one_smul] at H
  have c₁ : D.toPre.P.A.hom ≫ (D.toPre.c χ).left = (SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left := by simp [SectionScalarValuation.cQ]
  have c₂ : D.toPre.P.A.hom ≫ eSec D.toPre.P.A = (1 : D.toPre.P.A ⟶ D.toPre.P.A).left := by
    rw [Hom.one_def]; simp [eSec]
  have c₃ : SectionScalarValuation.cQ D.toPre D.toPre.P.A 0 = 1 := cPoint_zero (D := D.toPre) _
  obtain ⟨eB, heB, veB⟩ := SectionScalarValuation.exists_eB D.toPre 1 0 χ (LB.mulGen D.toPre.P.L _ _ _ _ e D.toPre.rig)
    (mulGen_isGen _ _ _ _ _ _ _ he D.toPre.rig_gen) (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.prod_unique, c₁, c₂, c₃, _root_.one_mul]
      simp)
  have hformB : FormEq (Sum.elim (fun i => (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left ≫ D.toPre.famφB 0 i)
      (Sum.elim (D.toPre.famφB (0 + 1 • χ))
        (fun i => (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left ≫ D.toPre.famφB 0 i)))
      (Sum.elim (DegPre.famε 1) (DegPre.deltaε 1)) (D.toPre.famφB (0 + 1 • χ)) (DegPre.famε 1) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  obtain ⟨g', hg'⟩ := exists_sec hL hformB
    (pullMulSec (g 0) (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left eB heB)
  refine ⟨g', secIsMul_of_sval hL _ (IntegralExpansion.prB_app_injective D.toPre) fun y J hJ => ?_⟩
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing R) hG 1 χ 0
  have vu := hv u hu hc _ (𝟙 _) y J hJ
  have hrel := (secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 (E.fe χ 0 u hu hc) _ (𝟙 _) y J hJ
  have htr : (DegPre.trF D.toPre (FractionRing R) χ).left ≫ (DegPre.prB D.toPre (FractionRing R)).left =
      (DegPre.prB D.toPre (FractionRing R)).left ≫ (𝟙 D.toPre.P.A * SectionScalarValuation.cQ D.toPre D.toPre.P.A χ).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    rw [DegPre.trF, DegPre.prB, lift_snd, MonObj.comp_mul, Category.comp_id, SectionScalarValuation.comp_cQ]
    rfl
  rw [H1.sval_scal (hg _) _ y hJ, H1.sval_scal (hg _) _ y hJ, Category.id_comp, Category.id_comp, htr] at hrel
  rw [hrel, hg' _ _ y J hJ, sval_pullMulSec _ _ _ heB _ y hJ, mul_left_comm]
  congr 1
  have w₁ : (fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R) ≫ jK R =
      (DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom :=
    (Over.w (fst (TF (R := R) (FractionRing R)) D.toPre.P.A)).trans (Over.w (DegPre.prB D.toPre (FractionRing R))).symm
  have v₁ := veB _ (DegPre.prB D.toPre (FractionRing R)) y J hJ
  have v₂ := hψ _ ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y J hJ
  have v₃ : val D.toPre.rigK ((fst (TF (R := R) (FractionRing R)) D.toPre.P.A).left ≫ jFK (R := R) (FractionRing R)) y J =
      val D.toPre.rig ((DegPre.prB D.toPre (FractionRing R)).left ≫ D.toPre.P.A.hom) y J := by
    rw [← w₁, ← Category.assoc]
    exact val_pull hJ _ _ _
  rw [Category.assoc, w₁] at v₂
  rw [Over.id_left, Category.id_comp, val_famMult_one D.tau_bimult _ hJ, v₃, uVal, Category.id_comp, Category.id_comp,
    comp_cP] at vu
  rw [val_mul hJ] at v₁
  rw [vu, v₁]
  simp only [Units.val_mul]
  rw [v₂]
  simp only [SectionScalarValuation.cQ, cP, th]
  ring

end GlobalTheory.LevelOneIdeal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValueAtUnitSectionGenericFibre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericUnitValue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem sval_of_secScal {X Y Y' Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ₁ : K → (Y' ⟶ X)} {ε₁ : K → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ₂ : K' → (Y ⟶ X)} {ε₂ : K' → ℤ}
    {s₂ : LB.Sec (LB.LinComb L φ₂ ε₂)} {h : Y' ⟶ Y} {c : Γ(Y', ⊤)} (H : GeneratorPullback.SecScal L φ₁ ε₁ s₁ φ₂ ε₂ s₂ h c)
    (r : Z ⟶ Y') (z : Z) {J} (hJ : Good L z J) :
    sval s₂ (r ≫ h) z J = gs r z ⊤ c * sval s₁ r z J := by
  have hj : ∀ q : K ⊕ K', Sum.elim (fun k => J (r ≫ φ₁ k)) (fun k => J ((r ≫ h) ≫ φ₂ k)) q =
      J (r ≫ Sum.elim φ₁ (fun k => h ≫ φ₂ k) q) := by
    intro q
    cases q with
    | inl q => rfl
    | inr q => exact congrArg J (Category.assoc _ _ _)
  have key := H (fun k => J (r ≫ φ₁ k)) (fun k => J ((r ≫ h) ≫ φ₂ k))
    (fun q₁ q₂ hq => by rw [hj, hj, hq])
  have m₂ := hJ.mem φ₂ (r ≫ h)
  have m : r z ∈ L.wchart φ₁ (fun k => J (r ≫ φ₁ k)) ⊓
      L.wchart (fun k => h ≫ φ₂ k) (fun k => J ((r ≫ h) ≫ φ₂ k)) := by
    refine ⟨hJ.mem φ₁ r, ?_⟩
    have e₃ : (fun k => J ((r ≫ h) ≫ φ₂ k)) = (fun k => J (r ≫ (fun k => h ≫ φ₂ k) k)) :=
      funext fun k => congrArg J (Category.assoc _ _ _)
    rw [e₃]
    exact hJ.mem (fun k => h ≫ φ₂ k) r
  have e := congrArg (gs r z _) key
  rw [gs_mul r z _ m] at e
  unfold resTop at e
  rw [gs_res r z _ m, gs_res r z _ m] at e
  have p := gs_pull r h z _ m₂ (s₂.f fun k => J ((r ≫ h) ≫ φ₂ k))
  exact p.symm.trans (e.trans (congrArg (gs r z ⊤ c * ·) (gs_res r z _ m _)))

theorem isUnit_cst_generic {V : Type} [CommRing V] [IsDomain V] (y : Spec (CommRingCat.of (FractionRing V)))
    {c : V} (hc : c ≠ 0) : IsUnit (cst (jK V) y c) := by
  have hK : IsUnit (algebraMap V (FractionRing V) c) :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hc)).isUnit
  obtain ⟨w, hw⟩ := hK
  rw [show cst (jK V) y c = cst (𝟙 _) y (algebraMap V (FractionRing V) c) from H1.gs_spec _ y c, ← hw]
  exact ⟨⟨cst (𝟙 _) y (w : FractionRing V), cst (𝟙 _) y (↑w⁻¹ : FractionRing V),
    by rw [← H1.cst_mul, Units.mul_inv, H1.cst_one], by rw [← H1.cst_mul, Units.inv_mul, H1.cst_one]⟩, rfl⟩

section

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]

lemma unitK_fst : (unitK (G := G)) ≫ pullback.fst G.hom (jK V) = jK V ≫ eSec G := by
  simp only [unitK, pullback.lift_fst]

lemma gs_unitK_scal (y : Spec (CommRingCat.of (FractionRing V))) (c : V) :
    gs (unitK (G := G)) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) c) = cst (jK V) y c := by
  have hsec : (unitK (G := G)) ≫ pullback.snd G.hom (jK V) = 𝟙 _ := by
    simp only [unitK, pullback.lift_snd]
  unfold scal cst
  refine (gs_pull (unitK (G := G)) (pullback.snd G.hom (jK V) ≫ jK V) y ⊤ trivial _).trans ?_
  rw [← Category.assoc, hsec, Category.id_comp]

end

theorem value_at_generic_unit : Laws → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (k : ℕ) (s : P.U.SecK k) (F : Fam P.D.toPre (FractionRing V) k) (u : P.U.SecK (k * N)) (F' : Fam P.D.toPre (FractionRing V) (k * N)), P.U.Expands k s F → P.U.Expands (k * N) u F' → PullAl P.D (FractionRing V) P.oD a k N F F' → ∀ (y : Spec (CommRingCat.of (FractionRing V))) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval u unitK y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig (jK V) y J ^ (k * (N - 1))).val * Geo.Tor.sval s unitK y J := by
  intro hL V _ _ _ E _ _ _ H t P a N hN hN0
  intro k s F u F' hs hu hpull y J hJ
  let _ := H.starRing
  obtain ⟨uΨ, huΨ, -, -⟩ := P.w0
  obtain ⟨X, hX, hXc⟩ := exists_XB P.D P.D.toPre.P.isLB P.oD H.w0 uΨ huΨ a N hN hN0 1
  obtain ⟨c, σ'', τ, hc, hsτ, huσ, hth⟩ :=
    GlobalTheory.PullExpInt.main hL.globalFns V E H t P a N hN hN0 X hX hXc k s F u F' hs hu hpull
  have hv := GlobalTheory.UnitValue.value_at_unit_section V E H t P a N hN hN0 X hX hXc k σ'' τ hth _ (jK V) y J hJ
  have e₁ := sval_of_secScal huσ unitK y hJ
  have e₂ := sval_of_secScal hsτ unitK y hJ
  rw [unitK_fst, gs_unitK_scal] at e₁ e₂
  rw [e₁, e₂] at hv
  apply (isUnit_cst_generic y hc).mul_left_cancel
  rw [hv]
  ring

end GlobalTheory.GenericUnitValue
end
end

