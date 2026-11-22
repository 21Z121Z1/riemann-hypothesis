import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ChartOfPoint
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

theorem chart_of_point {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) {n : ℕ} (b : Fin n → Γ(Y, ⊤)) (t : Fin n → LB.Sec (LB.LinComb L φ ε))
    (h : ∀ y I, Good L y I → sval s (𝟙 Y) y I = ∑ i, gs (𝟙 Y) y ⊤ (b i) * sval (t i) (𝟙 Y) y I) :
    ∀ j, s.f j = ∑ i, resTop _ (b i) * (t i).f j := by
  intro j
  refine fn_ext fun y hy0 => ?_
  have hy : y ∈ LB.wchart L φ j := hy0
  choose I hI using fun ψ : Y ⟶ X => exists_chart hL (ψ y)
  have hIy : Good L y I := hI
  have mm := hIy.mem φ (𝟙 _)
  have T0 := sec_trans s (𝟙 _) y hy mm
  set τ := (trF φ ε (𝟙 _) y j (fun k => I (𝟙 _ ≫ φ k))).val with hτ
  have RHS : gs (𝟙 _) y (LB.wchart L φ j) (∑ i, resTop (LB.wchart L φ j) (b i) *
      (show Γ(Y, LB.wchart L φ j) from (t i).f j)) =
      τ * ∑ i, gs (𝟙 _) y ⊤ (b i) * sval (t i) (𝟙 _) y I := by
    rw [gs_sum _ y _ hy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gs_mul _ y _ hy, gs_res _ y le_top hy, sec_trans (t i) (𝟙 _) y hy mm, hτ]
    exact mul_left_comm _ _ _
  exact T0.trans ((congrArg (fun x => τ * x) (h y I hIy)).trans RHS.symm)

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem hformF (k : ℕ) (ρ : D.toPre.X) :
    FormEq (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) (DegPre.famε k)
      (DegPre.famφ D.toPre F ρ) (DegPre.famε k) := by
  have e : (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) = DegPre.famφ D.toPre F ρ := by
    funext i
    fin_cases i
    · simp [DegPre.famφ, DegPre.famφB]
    · show (DegPre.prB D.toPre F).left ≫ (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ D.toPre.c ρ)).left =
        (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c ρ)).left
      rw [← Over.comp_left]
      congr 1
      simp only [padd]
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ D.toPre.c ρ).left = (toUnit _ ≫ D.toPre.c ρ).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left =
        (toUnit _ ≫ η[D.toPre.P.A]).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
  intro U _ h
  rw [e]

theorem hformF' (k : ℕ) (ρ : D.toPre.X) :
    FormEq (DegPre.famφ D.toPre F ρ) (DegPre.famε k)
      (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) (DegPre.famε k) := by
  have e : (fun i => (DegPre.prB D.toPre F).left ≫ D.toPre.famφB ρ i) = DegPre.famφ D.toPre F ρ := by
    funext i
    fin_cases i
    · simp [DegPre.famφ, DegPre.famφB]
    · show (DegPre.prB D.toPre F).left ≫ (padd D.toPre.P.A (𝟙 D.toPre.P.A) (toUnit D.toPre.P.A ≫ D.toPre.c ρ)).left =
        (padd D.toPre.P.A (DegPre.prB D.toPre F) (toUnit _ ≫ D.toPre.c ρ)).left
      rw [← Over.comp_left]
      congr 1
      simp only [padd]
      rw [← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ D.toPre.c ρ).left = (toUnit _ ≫ D.toPre.c ρ).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
    · show (DegPre.prB D.toPre F).left ≫ (toUnit D.toPre.P.A ≫ η[D.toPre.P.A]).left =
        (toUnit _ ≫ η[D.toPre.P.A]).left
      rw [← Over.comp_left, ← Category.assoc,
        CartesianMonoidalCategory.toUnit_unique (DegPre.prB D.toPre F ≫ toUnit _) (toUnit _)]
  intro U _ h
  rw [e]

theorem gF_gs (c : F) (y : (DegPre.BF D.toPre F).left) :
    gs (𝟙 _) y ⊤ (gF D.toPre F c) = gs (fst (TF (R := V) F) D.toPre.P.A).left y ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) := by
  first
  | rfl
  | exact (gs_appLE_top _ _ _ le_top _).symm
  | (unfold gF; exact (gs_appLE_top _ _ _ le_top _).symm)
  | simp [gF, gs_appLE_top]

theorem coordsF {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J) :
    (∀ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)), ∃ c : Fin m → F,
      ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        sval t (𝟙 _) y J = ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J) ∧
    (∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0) := by
  have hL := D.toPre.P.isLB
  have eT : Over.mk (Spec.map (CommRingCat.ofHom (algVF (F := F) (V := V)))) = TF (R := V) F := by
    rw [← TF_hom]; rfl
  have hbF' := hb F (algVF (F := F) (V := V))
  rw [eT] at hbF'
  let b' := fun i => pullSec D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k) (b i)
    (snd (TF (R := V) F) D.toPre.P.A).left
  have hB := hbF' b' (fun i j => rfl)
  have hb' : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (b' i) (𝟙 _) y J = sval (bF i) (𝟙 _) y J := fun i y J hJ => by
    rw [hbF i y J hJ]
    exact (sval_pullSec _ _ _ _ _ y hJ).trans (by rw [Category.id_comp])
  refine ⟨fun t => ?_, fun c hc => ?_⟩
  · obtain ⟨t', ht'⟩ := exists_sec hL (hformF' k ρ) t
    obtain ⟨r, hr, -⟩ := hB t'
    choose c hc using fun i => (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 (r i)
    refine ⟨c, fun y J hJ => ?_⟩
    rw [← ht' _ (𝟙 _) y J hJ, sval_lin (fun i => (fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom (r i)) b' hr (𝟙 _) y hJ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb' i y J hJ, gF, RingHom.comp_apply, ← hc i]
  · let z0 : LB.Sec (LB.LinComb D.toPre.P.L (fun i => (snd (TF (R := V) F) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
      (DegPre.famε k)) := SecOps.secZero
    have r1 := chart_of_point hL z0 (fun i => (fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i))) b' (fun y I hI => by
        rw [sval_zero_of (fun j => rfl) _ y I (hI.mem _ _), ← hc y I hI]
        exact Finset.sum_congr rfl fun i _ => by rw [hb' i y I hI]; rfl)
    have r0 : ∀ j, z0.f j = ∑ i, resTop _ ((fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom 0) * (b' i).f j := fun j => by
      simp only [map_zero, MulZeroClass.zero_mul, Finset.sum_const_zero]; rfl
    obtain ⟨r, -, hu⟩ := hB z0
    have e := (hu _ r1).trans (hu _ r0).symm
    funext i
    have hi : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (c i) = 0 := congrFun e i
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom hi
    simpa using this

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GsScalJFK
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

section FE

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]
  {v : AddValuation F (WithTop ℚ)}

theorem trF_fst (mu : D.toPre.X) :
    (DegPre.trF D.toPre F mu).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left := by
  rw [← Over.comp_left]
  simp [DegPre.trF]

theorem trF_prB (mu : D.toPre.X) :
    (DegPre.trF D.toPre F mu).left ≫ (DegPre.prB D.toPre F).left =
      (DegPre.prB D.toPre F).left ≫ (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  simp only [DegPre.trF, CartesianMonoidalCategory.lift_snd, padd, CategoryTheory.Hom.mul_def, cQ,
    CartesianMonoidalCategory.comp_lift_assoc, Category.comp_id, SemiCartesianMonoidalCategory.comp_toUnit_assoc]

theorem gs_gF_zF (y : (TF (R := V) F).left) (ζ : F) :
    gs (DegPre.zF D.toPre F).left y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) := by
  have h := gs_pull (DegPre.zF D.toPre F).left (fst (TF (R := V) F) D.toPre.P.A).left y ⊤ (by simp)
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ)
  have e : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left]
    simp [DegPre.zF]
  rw [e] at h
  rw [← h]
  rfl

theorem gs_scal_jFK (y : (TF (R := V) F).left) (c : FractionRing V) :
    gs (𝟙 (TF (R := V) F).left ≫ jFK (R := V) F) y ⊤ (scal (𝟙 _) c) =
      gs (𝟙 _) y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (algebraMap (FractionRing V) F c)) := by
  have key : ((jFK (R := V) F).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (algebraMap (FractionRing V) F c) := by
    have := congrArg (fun φ => φ.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing V) F)))
    exact this.symm
  have h := gs_pull (𝟙 (TF (R := V) F).left) (jFK (R := V) F) y ⊤ (by simp)
    ((Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c)
  have hs : scal (𝟙 (Spec (CommRingCat.of (FractionRing V)))) c =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom c := by
    simp [scal]
  erw [hs, ← h]
  exact congrArg (gs (𝟙 (TF (R := V) F).left) y ⊤) key

theorem fe_move (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} (hQ : IsQ D.toPre ϖ Q) (hv : ValOver ϖ F v) (k : ℕ)
    (mu α : D.toPre.X) (s : Fam D.toPre F k) {r : ℚ} (hs : VGe D F v k α (s.s α) r) :
    VGe D F v k (α + k • mu) (s.s (α + k • mu)) (r + ((k * Q mu + bOf D.toPre Q mu α : ℤ) : ℚ)) := by
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨Ix, _, φV, εV, e', he', hC, c₀, hc₀, hval⟩ := famMult_data D hϖ hQ k mu α
  obtain ⟨eB, heB, veB⟩ := exists_eB D.toPre k α mu e' he' hC
  have hc0 : c₀ ≠ 0 := ne_zero_of_hasVal hϖ hc₀
  set c : F := algebraMap (FractionRing V) F c₀ with hc
  have hcne : c ≠ 0 := (map_ne_zero _).2 hc0
  let cU : Γ((DegPre.BF D.toPre F).left, ⊤)ˣ :=
    ⟨gF D.toPre F c, gF D.toPre F c⁻¹, by rw [← map_mul, mul_inv_cancel₀ hcne, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hcne, map_one]⟩
  let g0 : LB.Gen (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim) :=
    ⟨fun _ => res le_top cU⟩
  have hg0 : g0.IsGen := fun i j => by
    have hg : (LB.LinComb D.toPre.P.L (Y := (DegPre.BF D.toPre F).left) (K := PEmpty) PEmpty.elim PEmpty.elim).g i j = 1 := by
      simp [LB.LinComb]; rfl
    calc res _ (g0.s i) = res _ (g0.s j) := (res_res' _ _ cU).trans (res_res' _ _ cU).symm
      _ = _ := by rw [hg, _root_.one_mul]
  have hformU : FormEq (Sum.elim (fun i => (DegPre.prB D.toPre F).left ≫ Sum.elim (D.toPre.famφB (α + k • mu))
        (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i) i) PEmpty.elim)
      (Sum.elim (DegPre.deltaε k) PEmpty.elim) (DegPre.deltaφ D.toPre F k α mu) (DegPre.deltaε k) := fun U _ h => by
    have e0 : ∀ f : PEmpty → U, ∏ i, f i = 1 := fun f => Fintype.prod_empty f
    rw [Fintype.prod_sum_type, e0, _root_.mul_one]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases i with i | i
    · simp only [Sum.elim_inl, DegPre.deltaφ, GC.famφ_eq]
    · simp only [Sum.elim_inr, DegPre.deltaφ, GC.famφ_eq]
      rw [← Category.assoc, trF_prB, Category.assoc]
      rfl
  obtain ⟨u, hu, vu⟩ := exists_gen hL hformU
    (LB.mulGen D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ eB (DegPre.prB D.toPre F).left) g0)
    (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ heB _) hg0)
  have hval_u : ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι),
      Good D.toPre.P.L z J →
      (val u ρ z J).val = (val eB (ρ ≫ (DegPre.prB D.toPre F).left) z J).val * gs ρ z ⊤ (gF D.toPre F c) := by
    intro Z ρ z J hJ
    rw [vu Z ρ z J hJ, val_mul hJ, val_pull hJ, Units.val_mul]
    congr 1
    have hmem : ρ z ∈ LB.wchart D.toPre.P.L (K := PEmpty) PEmpty.elim (fun k => J (ρ ≫ PEmpty.elim k)) :=
      Set.mem_iInter.2 fun k => k.elim
    exact (congrArg Units.val (gm_res ρ z le_top hmem cU)).trans (gs_unit ρ z ⊤ (by trivial) cU).symm
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have hcorr : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left)
      (DegPre.famMult D.toPre F k mu α) := corr_of_val hL fun y J hJ => Units.ext (by
    have C : IsCub (cubV D.toPre.cub (T := TF (R := V) F) y J) := isCub_cubV D.toPre.cub hJ
    have E2 : val eB ((DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left) y J =
        val e' (DegPre.jFR (R := V) F) y J := by
      have E1 := veB (TF (R := V) F) (DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F) y J hJ
      rw [z₂, C.N_one, C.face₂, inv_one, _root_.one_mul, _root_.one_mul] at E1
      have e3 : (1 : TF (R := V) F ⟶ D.toPre.P.A).left ≫ D.toPre.P.A.hom = DegPre.jFR (R := V) F := Over.w _
      rw [e3] at E1
      have e4 : (DegPre.zF D.toPre F).left ≫ (DegPre.prB D.toPre F).left = (1 : TF (R := V) F ⟶ D.toPre.P.A).left := by
        rw [← Over.comp_left, z₂]
      rw [e4]; exact E1
    rw [val_pull hJ, Category.id_comp, hval_u _ _ y J hJ, hval F (TF (R := V) F).left (𝟙 (TF (R := V) F).left) y J hJ, E2, gs_gF_zF, gs_scal_jFK,
      Category.id_comp, ← hc]
    exact mul_comm _ _)
  have hrel := s.fe mu α u hu hcorr
  have hformB : FormEq (Sum.elim (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i)
      (Sum.elim (D.toPre.famφB (α + k • mu)) (fun i => (𝟙 D.toPre.P.A * cQ D.toPre D.toPre.P.A mu).left ≫ D.toPre.famφB α i)))
      (Sum.elim (DegPre.famε k) (DegPre.deltaε k)) (D.toPre.famφB (α + k • mu)) (DegPre.famε k) := fun U _ h => by
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, DegPre.deltaε, zpow_neg, Finset.prod_inv_distrib]
    rw [mul_left_comm, mul_inv_cancel, _root_.mul_one]
  refine vge_move (trF_fst mu) (trF_prB mu) u hrel eB heB hformB c (fun y J hJ => ?_) ?_ hs
  · rw [hval_u _ _ y J hJ, Category.id_comp]; exact mul_comm _ _
  · exact le_of_eq (hv c₀ _ hc₀).symm

end FE

end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtSt
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

def NuExtSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (vK : AddValuation (FractionRing V) (WithTop ℚ)), ValOver ϖ (FractionRing V) vK →
    ∀ (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V)))
      [GrpObj G] [IsCommMonObj G] [Smooth G.hom] [IsSeparated G.hom] [QuasiCompact G.hom]
      (U : Unif (maximalIdeal V) D A G) (k : ℕ), 1 ≤ k →
      ∀ (s : U.SecK k) (E : Fam D.toPre (FractionRing V) k), U.Expands k s E →
        NuGe D Q (FractionRing V) vK k E 0 →
        ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))),
          GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK V)) (fun _ => (k : ℤ)) s
            (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (pullback.fst G.hom (jK V)) 1

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi IsLocalRing QForm

def TWStatement : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (Q : D.toPre.X → ℤ), IsQ D.toPre ϖ Q →
    ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)), ValOver ϖ F v →
    ∀ k : ℕ, 1 ≤ k → ∀ (p : QkPt D.toPre F k)
      (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
      w.IsGen → ∀ ζ : F, ζ ≠ 0 →
      ∃ c : ℚ, ∀ s t s' : Fam D.toPre F k, PhiRel D.toPre F k p w s t → Fam.IsSmul D.toPre F ζ t s' →
        ∀ r : ℚ, NuGe D Q F v k s r ↔ NuGe D Q F v k s' (r + c)

namespace PeriodicValuation

theorem all_of_periodic {P : ℚ → Prop} (hmono : ∀ r r' : ℚ, r' ≤ r → P r → P r') {d : ℚ} (hd : d ≠ 0)
    (hper : ∀ r, P r ↔ P (r + d)) (r₁ r₂ : ℚ) (h : P r₁) : P r₂ := by
  have he : ∀ r, P r → P (r + |d|) := by
    intro r hr
    rcases lt_or_gt_of_ne hd with hneg | hpos
    · rw [abs_of_neg hneg]
      have h1 : P (r - d) := (hper (r - d)).2 (by rwa [sub_add_cancel])
      simpa [sub_eq_add_neg] using h1
    · rw [abs_of_pos hpos]
      exact (hper r).1 hr
  have hn : ∀ k : ℕ, P (r₁ + k * |d|) := by
    intro k
    induction k with
    | zero => simpa using h
    | succ k ih =>
      have h2 := he _ ih
      convert h2 using 1
      push_cast
      ring
  have hpos : 0 < |d| := abs_pos.2 hd
  obtain ⟨k, hk⟩ := exists_nat_gt ((r₂ - r₁) / |d|)
  rw [div_lt_iff₀ hpos] at hk
  exact hmono _ _ (by linarith) (hn k)

end PeriodicValuation

open PeriodicValuation

theorem galois_fixed_adelic_matrices_descend (hL : Laws) (hTW : TWStatement) : FiniteOrderValuationInvariance := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv k hk p w hw ζ hζ hfin s t s' hst hts' r
  obtain ⟨c, hc⟩ := hTW V ϖ hϖ D Q hQ F v hv k hk p w hw ζ hζ
  obtain ⟨Φ, hΦ⟩ := phiFun_of_globalFns hL.globalFns V (maximalIdeal V) D F k hk p w hw
  obtain ⟨M, hM1, hM⟩ := hfin
  let step : Fam D.toPre F k → Fam D.toPre F k := fun x => ζ • Φ x
  have hsm : ∀ x : Fam D.toPre F k, Fam.IsSmul D.toPre F ζ (Φ x) (step x) := fun x α j => rfl
  have hstep : ∀ x r, NuGe D Q F v k x r ↔ NuGe D Q F v k (step x) (r + c) := fun x r =>
    hc x (Φ x) (step x) ((hΦ x (Φ x)).2 rfl) (hsm x) r
  have hsame : ∀ x y : Fam D.toPre F k, (∀ α j, (x.s α).f j = (y.s α).f j) →
      ∀ r, NuGe D Q F v k x r ↔ NuGe D Q F v k y r := by
    intro x y hxy r
    simp only [NuGe, VGe, hxy]
  have hiter : ∀ n : ℕ, ∀ r, NuGe D Q F v k s r ↔ NuGe D Q F v k (step^[n] s) (r + n * c) := by
    intro n
    induction n with
    | zero => intro r; simp
    | succ n ih =>
      intro r
      rw [ih r, Function.iterate_succ_apply', hstep (step^[n] s) (r + n * c)]
      have e : r + n * c + c = r + ((n + 1 : ℕ) : ℚ) * c := by push_cast; ring
      rw [e]
  have hret : ∀ α j, ((step^[M] s).s α).f j = (s.s α).f j := by
    refine hM (fun i => step^[i.val] s) (fun i => Φ (step^[i.val] s)) fun i => ⟨?_, ?_⟩
    · exact (hΦ _ _).2 rfl
    · intro α j
      show ((step^[i.val + 1] s).s α).f j = _
      rw [Function.iterate_succ_apply']
      exact hsm _ α j
  have hper : ∀ r, NuGe D Q F v k s r ↔ NuGe D Q F v k s (r + M * c) := fun r =>
    (hiter M r).trans (hsame _ _ hret _)
  by_cases hc0 : c = 0
  · have h := hc s t s' hst hts' r
    rwa [hc0, add_zero] at h
  · have hd : (M : ℚ) * c ≠ 0 := mul_ne_zero (by exact_mod_cast (by omega : M ≠ 0)) hc0
    have hmono : ∀ r r' : ℚ, r' ≤ r → NuGe D Q F v k s r → NuGe D Q F v k s r' :=
      fun r r' h hp => NuGe.mono (h := hp) (hr := h)
    constructor
    · intro h
      have h1 : NuGe D Q F v k s (r - c) := all_of_periodic hmono hd hper r (r - c) h
      have h2 := (hc s t s' hst hts' (r - c)).1 h1
      rwa [sub_add_cancel] at h2
    · intro h
      have h1 : NuGe D Q F v k s (r - c) :=
        (hc s t s' hst hts' (r - c)).2 (by rwa [sub_add_cancel])
      exact all_of_periodic hmono hd hper (r - c) r h1

end ReciprocityTheory.ChartRestriction.G.DVR
end
end

