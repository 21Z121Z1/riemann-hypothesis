import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0002
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0070
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0049
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorRawOfFrep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ConjugateKernelCount
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ProdPullZero
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.BoxPull

open GlobalTheory.BoxPhi

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [CommRing O] [StarRing O]

theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  by_cases h : f y ∈ U
  · rw [gs_eq f y U h, map_zero, map_zero]
  · exact dif_neg h

theorem prod_pull_zero (D : DegData V (maximalIdeal V)) [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N : ℕ)
    (hN : 1 ≤ N) (χ : D.toPre.X) {U : Type} [CommGroup U] (h : ((TF (R := V) F).left ⟶ D.toPre.P.A.left) → U) :
    ∏ i, h ((DegPre.zF D.toPre F).left ≫ pullφ D F oa a χ i) ^ pullε k N i =
      h (1 : TF (R := V) F ⟶ D.toPre.P.A).left ^ (k * (N - 1)) := by
  have := oa.onB.hom a
  have p₃ := prod_fam D.toPre F (DegPre.zF D.toPre F) (star a • χ) (k * N) h
  have p₄ := prod_fam D.toPre F (DegPre.zF D.toPre F ≫ aF D F oa a) χ k h
  have z₂ : DegPre.zF D.toPre F ≫ DegPre.prB D.toPre F = 1 := lift_snd _ _
  have z₃ : (DegPre.zF D.toPre F ≫ aF D F oa a) ≫ DegPre.prB D.toPre F = 1 := by
    rw [Category.assoc, aF, lift_snd, ← Category.assoc, z₂, MonObj.one_comp]
  rw [z₂, _root_.mul_one] at p₃
  rw [z₃, _root_.mul_one] at p₄
  simp only [Over.comp_left, Category.assoc] at p₄
  refine (prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := U) _ p₃ (prod_neg _ _ p₄)).trans ?_
  rw [← zpow_natCast, Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hN]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

theorem aF_pr {j : ℕ} {D D' : DegData V (maximalIdeal V)} (pD : IsPowDeg D'.toPre D.toPre j)
    [Module O D.toPre.X] [Module O D'.toPre.X] (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O) (a : O) (i : Fin j)
    (hact : oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) :
    (aF D' F oa' a).left ≫ prB pD F i = prB pD F i ≫ (aF D F oa a).left := by
  refine congrArg (fun q => q.left) (?_ : aF D' F oa' a ≫ (TF (R := V) F ◁ pD.pw.pr i) =
    (TF (R := V) F ◁ pD.pw.pr i) ≫ aF D F oa a)
  apply CartesianMonoidalCategory.hom_ext
  · simp [aF]
  · simp [aF, hact]

theorem pullAl_box {j : ℕ} {D D' : DegData V (maximalIdeal V)} (pD : IsPowDeg D'.toPre D.toPre j)
    [Module O D.toPre.X] [Module O D'.toPre.X]
    (hx : ∀ (a : O) (x : D'.toPre.X) (i : Fin j), pD.xe (a • x) i = a • pD.xe x i)
    (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O)
    (hact : ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) (a : O) (N k : ℕ) (hN : 1 ≤ N)
    (s : Fin j → Fam D.toPre F k) (s' : Fin j → Fam D.toPre F (k * N)) (S : Fam D'.toPre F k)
    (S' : Fam D'.toPre F (k * N)) (hs : ∀ i, PullAl D F oa a k N (s i) (s' i)) (hS : IsBoxFam pD F k S s)
    (hS' : IsBoxFam pD F (k * N) S' s') : PullAl D' F oa' a k N S S' := by
  have ht := fun i => aF_pr (F := F) pD oa oa' a i (hact a i)
  refine ⟨fun χ' => ?_, fun β' hβ' => ?_⟩
  · choose u hu hc hr using fun i => (hs i).1 (pD.xe χ' i)
    have hφ : ∀ i b, pullφ D' F oa' a χ' b ≫ (pD.pw.pr i).left =
        prB pD F i ≫ pullφ D F oa a (pD.xe χ' i) b := by
      rintro i (b | b)
      · exact ((hS' (star a • χ')).choose i b).trans (by rw [hx]; rfl)
      · show ((aF D' F oa' a).left ≫ DegPre.famφ D'.toPre F χ' b) ≫ _ =
          _ ≫ (aF D F oa a).left ≫ DegPre.famφ D.toPre F (pD.xe χ' i) b
        rw [Category.assoc, (hS χ').choose i b, ← Category.assoc, ht, Category.assoc]
    obtain ⟨v, hv, vv⟩ := exists_box_gen D.toPre.P.isLB D'.toPre.P.isLB pD.w pD.w_gen hφ u hu
    refine ⟨v, hv, corr_of_val D'.toPre.P.isLB fun y J' hJ' => ?_,
      (secRel_iff D'.toPre.P.isLB _ _ _ _ _ _ _ _ _ v).2 fun y J' hJ' => ?_⟩
    · obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
      have e₂ := vv _ (DegPre.zF D'.toPre F).left y J J' hJ hJ'
      let r : (TF (R := V) F).left ⟶ (TK V).left := 𝟙 (TF (R := V) F).left ≫ jFK (R := V) F
      have e₃ : om pD.w y J J' (1 : TF (R := V) F ⟶ D'.toPre.P.A).left * val D'.toPre.rigK r y J' =
          ∏ _i : Fin j, val D.toPre.rigK r y J := by
        have z : (1 : TF (R := V) F ⟶ D'.toPre.P.A).left = r ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A :=
          (show (1 : TF (R := V) F ⟶ D'.toPre.P.A).left =
              jFK (R := V) F ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A by
            show (toUnit _ ≫ η[D'.toPre.P.A]).left = _
            rw [Over.comp_left]
            rfl).trans (congrArg (· ≫ (toUnit (TK V)).left ≫ eSec D'.toPre.P.A)
            (Category.id_comp (jFK (R := V) F)).symm)
        rw [z]
        exact BoxFamily.rig_val pD hJ hJ' r
      have e₅ : ∀ i, val (u i) ((DegPre.zF D'.toPre F).left ≫ prB pD F i) y J =
          val D.toPre.rigK r y J ^ (k * (N - 1)) := fun i => by
        have := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (hc i) (𝟙 _)).trans
          ((val_pull hJ _ _ _).trans (BoxFamily.val_powGen _ _ _ _ _ _ _)))
        rw [Category.id_comp] at this
        rw [BoxFamily.zF_pr]
        exact this
      rw [prod_pull_zero D' oa' a k N hN χ', Finset.prod_congr rfl (fun i _ => e₅ i), Finset.prod_pow, ← e₃,
        mul_pow] at e₂
      refine (val_pull hJ' _ _ _).trans (Eq.trans ?_
        ((val_pull hJ' _ _ _).trans (BoxFamily.val_powGen _ _ _ _ _ _ _)).symm)
      rw [Category.id_comp]
      exact mul_left_cancel e₂
    · obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
      have e₁ := fam_val pD hS' (star a • χ') (𝟙 _) y hJ hJ'
      have e₂ := fam_val pD hS χ' (𝟙 _ ≫ (aF D' F oa' a).left) y hJ hJ'
      have e₃ := vv _ (𝟙 _) y J J' hJ hJ'
      have e₄ : ∀ i, sval ((s' i).s (pD.xe (star a • χ') i)) (𝟙 _ ≫ prB pD F i) y J =
          sval ((s i).s (pD.xe χ' i)) ((𝟙 _ ≫ (aF D' F oa' a).left) ≫ prB pD F i) y J *
            (val (u i) (𝟙 _ ≫ prB pD F i) y J).val := fun i => by
        rw [hx, Category.assoc, ht, ← Category.assoc]
        exact (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ (u i)).1 (hr i) _ _ y J hJ
      have e₅ : ∏ b, om pD.w y J J' (𝟙 _ ≫ pullφ D' F oa' a χ' b) ^ pullε k N b =
          (∏ b, om pD.w y J J' (𝟙 _ ≫ DegPre.famφ D'.toPre F (star a • χ') b) ^ DegPre.famε (k * N) b) *
          (∏ b, om pD.w y J J' ((𝟙 _ ≫ (aF D' F oa' a).left) ≫ DegPre.famφ D'.toPre F χ' b) ^
            DegPre.famε k b)⁻¹ := by
        simp only [Category.assoc]
        exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
      rw [Finset.prod_congr rfl (fun i _ => e₄ i), Finset.prod_mul_distrib, ← e₂, ← Units.coe_prod, ← e₃, e₅] at e₁
      exact alg_fin e₁
  · obtain ⟨i, hi⟩ : ∃ i, ∀ χ, pD.xe β' i ≠ star a • χ := by
      by_contra hne
      push Not at hne
      choose χ hχ using hne
      refine hβ' (pD.xe.symm χ) (pD.xe.injective (funext fun i => ?_))
      rw [hx, AddEquiv.apply_symm_apply, hχ]
    have hz := (hs i).2 _ hi
    intro jj
    refine fn_ext fun y hy => ?_
    obtain ⟨J', hJ', e⟩ := sval_trans D'.toPre.P.isLB (S'.s β') y jj hy
    obtain ⟨J, hJ⟩ := BoxFamily.exists_good_at D.toPre.P.isLB y
    have e₁ := fam_val pD hS' β' (𝟙 _) y hJ hJ'
    have z₀ : sval ((s' i).s (pD.xe β' i)) (𝟙 _ ≫ prB pD F i) y J = 0 := by
      exact (congrArg (gs _ y _) (hz _)).trans (gs_zero' _ y _)
    rw [Finset.prod_eq_zero (Finset.mem_univ i) z₀, Units.mul_right_eq_zero] at e₁
    rw [e₁, mul_zero] at e
    refine e.trans ?_
    exact (gs_zero' _ y _).symm

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] (j : ℕ) (D D' : DegData V (maximalIdeal V)) (pD : IsPowDeg D'.toPre D.toPre j) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X], (∀ (a : O) (x : D'.toPre.X) (i : Fin j), pD.xe (a • x) i = a • pD.xe x i) → ∀ (oa : D.toPre.OAct O) (oa' : D'.toPre.OAct O), (∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a) → ∀ (a : O) (N k : ℕ), 1 ≤ N → 1 ≤ k → a * star a = (N : O) → ∀ (s : Fin j → Fam D.toPre F k) (s' : Fin j → Fam D.toPre F (k * N)) (S : Fam D'.toPre F k) (S' : Fam D'.toPre F (k * N)), (∀ i, PullAl D F oa a k N (s i) (s' i)) → IsBoxFam pD F k S s → IsBoxFam pD F (k * N) S' s' → PullAl D' F oa' a k N S S' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ pD _ _ _ _ _ _ _ _ hx oa oa' hact a N k hN _ _ s s' S S' hs hS hS' =>
    pullAl_box pD hx oa oa' hact a N k hN s s' S S' hs hS hS'

end GlobalTheory.BoxPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselSum
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem coef_mul_split : PI.KFinSmooth → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → IsCoef R l l' F s → ∃ (Ft : κ → Mx k r → (Wq →L[ℂ] Wp)) (st : κ → ℂ), (∀ I, IsCoef (RI I) (lI I) (lI' I) (Ft I) (st I)) ∧ (∀ g ∈ GG k r, Formalism.QuantumDeterminants.herm Γ (ρ g *ᵥ om') om • F g = ∑ I, Ft I g) ∧ (∀ I, (¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) → st I = 0) ∧ ∀ I (κ₀ κ₁ : ℂ), (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) → (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) → st I = (ep I : ℂ) * κ₁ * star κ₀ * s := by
  intro hK k r ι κ _ _ _ _ ρ Γ d R RI io pr ep ε mu muI Wp _ _ _ _ Wq _ _ _ _ om om' l l' lI lI' F s
    hR hRI hF hT hC
  obtain ⟨m, x, y, X, hxy, hFg, hs⟩ := hC
  have hsm : ∀ v ∈ R.TK, v ∈ R.sm := (GlobalTheory.rep_basic_of_isDS hK k r ε mu R hR).2.2.2.2.1
  have hsmI : ∀ I, ∀ v ∈ (RI I).TK, v ∈ (RI I).sm := fun I =>
    (GlobalTheory.rep_basic_of_isDS hK k r ε (muI I) (RI I) (hRI I)).2.2.2.2.1
  have hadj := (GlobalTheory.TensAdj.tens_adj hK k r ι κ ρ Γ d R RI io pr ep ε mu muI hR hRI hF hT).2.2.2.2
  have hkf := (GlobalTheory.tensor_decomposition_kfinite hK k r ι κ ρ Γ d R RI io pr ε mu muI hR hRI hF hT.raw).2.2.2
  have hp : ∀ I (a : ι → ℂ), ∀ v ∈ R.TK, (∑ c, pr I c (tm R a v c)) ∈ (RI I).TK := fun I a v hv =>
    Submodule.sum_mem _ fun c _ => hkf I c _ (Submodule.smul_mem _ _ hv)
  refine ⟨fun I g => ∑ i, ⟪∑ c, pr I c (tm R om (x i) c), (RI I).σ g (∑ c, pr I c (tm R om' (y i) c))⟫_ℂ •
      ((ep I : ℂ) • X i),
    fun I => ∑ i, ⟪lI I (∑ c, pr I c (tm R om (x i) c)),
      ((ep I : ℂ) • X i) (lI' I (∑ c, pr I c (tm R om' (y i) c)))⟫_ℂ, ?_, ?_, ?_, ?_⟩
  · intro I
    exact ⟨m, fun i => ∑ c, pr I c (tm R om (x i) c), fun i => ∑ c, pr I c (tm R om' (y i) c),
      fun i => (ep I : ℂ) • X i, fun i => ⟨hp I om _ (hxy i).1, hp I om' _ (hxy i).2⟩, fun g _ => rfl, rfl⟩
  · intro g hg
    rw [hFg g hg, Finset.smul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hadj om om' _ (hsm _ (hxy i).1) _ (hsm _ (hxy i).2) g hg, Finset.sum_smul]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [smul_smul, mul_comm]
  · intro I h
    refine Finset.sum_eq_zero fun i _ => ?_
    rcases h with h | h
    · have : lI I (∑ c, pr I c (tm R om (x i) c)) = 0 := by
        by_contra hne
        exact h ⟨_, hsmI I _ (hp I om _ (hxy i).1), hne⟩
      rw [this, inner_zero_left]
    · have : lI' I (∑ c, pr I c (tm R om' (y i) c)) = 0 := by
        by_contra hne
        exact h ⟨_, hsmI I _ (hp I om' _ (hxy i).2), hne⟩
      rw [this, map_zero, inner_zero_right]
  · intro I κ₀ κ₁ h0 h1
    rw [hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h0 _ (hsm _ (hxy i).1), h1 _ (hsm _ (hxy i).2), map_smul, ContinuousLinearMap.smul_apply,
      inner_smul_left, inner_smul_right, inner_smul_right]
    simp only [starRingEnd_apply]
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TypingsAgree
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj IsLocalRing NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionFactsCompare

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateKernelCount

section Operators

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

def cUnit (ζ : F) (hζ : ζ ≠ 0) : Γ((TF (R := R) F).left, ⊤)ˣ :=
  ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit

end Operators

section Data

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F]

def FinOrdConcl (k : ℕ) : Prop :=
  ∀ (p : QkPt D.toPre F k)
    (w : LB.Gen (LB.LinComb D.toPre.P.L (DegPre.lineφ D.toPre F p.g.b) (DegPre.lineε k))),
    w.IsGen → ∃ ζ : F, ζ ≠ 0 ∧ FinOrd D F k p w ζ

def FrameConcl (Q : D.toPre.X → ℤ) (v : AddValuation F (WithTop ℚ)) (N : ℕ) (s₀ : Fam D.toPre F (1 * N)) : Prop :=
  ∀ r : ℚ, NuGe D Q F v (1 * N) s₀ r → ((r + (Q 0 : ℚ) / (1 : ℕ) : ℚ) : WithTop ℚ) ≤ v 1

open QForm in

theorem bOf_balance {ϖ : V} (hϖ : Irreducible ϖ) {Q : D.toPre.X → ℤ} {O : Type} [Ring O] [StarRing O]
    [Module O D.toPre.X] (ιD : D.toPre.OAct O) (hQ : IsQ D.toPre ϖ Q) (a : O) (χ χ' : D.toPre.X) :
    bOf D.toPre Q (a • χ) χ' = bOf D.toPre Q χ (star a • χ') := by
  have hL := D.toPre.P.isLB
  have := ιD.onB.hom a
  have := ιD.onB.hom (star a)
  obtain ⟨u, hu, hnorm⟩ := exists_ros GlobalTheory.globalFns_holds D.toPre.P.isAb D.toPre.P.isLB _ _ (ιD.onB.rosati a)
  have hc := ιD.tau_bal a u hu hnorm χ χ'
  obtain ⟨_, _, hsA, hA⟩ := tau_val hϖ D hQ (a • χ) χ'
  obtain ⟨_, _, hsB, hB⟩ := tau_val hϖ D hQ χ (star a • χ')
  have hu0 := genHasVal_pullGen_of (ϖ := ϖ) D.toPre.P.L _ _ u hu (lift (D.toPre.c χ) (D.toPre.c χ')).left
    (D.toPre.pt2 χ χ') (by simp [DegPre.pt2, ← CartesianMonoidalCategory.comp_lift])
  have h1 := genHasVal_mulGen hϖ D.toPre.P.L hL _ _ _ _ _ _ _ _ _ _ hA hu0
  have := genHasVal_unique hϖ D.toPre.P.L hL _ _ _ _ _
    (genHasVal_corr hϖ D.toPre.P.L hL D.toPre.P.A.hom _ _ _ _ _ _ _ _
      (sumElim_sec hsA (fun k => by
        obtain ⟨q, hq⟩ := rosatiφ_over D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k
        show (_ ≫ rosatiφ D.toPre.P.A (ιD.onB.act a) (ιD.onB.act (star a)) k) ≫ _ = _
        rw [hq]; exact over_sec _ _)) hsB _ _
      (genHasVal_isGen D.toPre.P.L _ _ _ _ _ hB) hc h1) hB
  linarith

end Data

section Unif

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
  (P : PELUnif (maximalIdeal V) t) (F : Type) [Field F] [Algebra (FractionRing V) F]

def EnumConcl (α : 𝓞 E) (N : ℕ) : Prop :=
  letI := H.starRing
  ∃ (p : Fin (N ^ P.A.g) → QkPt P.D.toPre F (1 * N)) (x : Fin (N ^ P.A.g) → (TFK (R := V) F ⟶ P.A.A)),
    (∀ b, P.ToA F (1 * N) (p b) (x b)) ∧ (∀ b, x b ≫ P.oA.act (star α) = 1) ∧ Function.Injective x ∧
    ∀ y : TFK (R := V) F ⟶ P.A.A, y ≫ P.oA.act (star α) = 1 → ∃ b, x b = y

def CanonConcl (α : 𝓞 E) (N : ℕ) (s₀ : Fam P.D.toPre F (1 * N)) : Prop :=
  letI := H.starRing
  ∀ (p : QkPt P.D.toPre F (1 * N)) (x : TFK (R := V) F ⟶ P.A.A), P.ToA F (1 * N) p x →
    x ≫ P.oA.act α = 1 →
    ∃ w : LB.Gen (LB.LinComb P.D.toPre.P.L (DegPre.lineφ P.D.toPre F p.g.b) (DegPre.lineε (1 * N))),
      w.IsGen ∧ FinOrd P.D F (1 * N) p w 1 ∧ PhiRel P.D.toPre F (1 * N) p w s₀ s₀

def PairConcl (α : 𝓞 E) (N : ℕ) : Prop :=
  letI := H.starRing
  ∀ (x x' : TFK (R := V) F ⟶ P.A.A), x ≫ P.oA.act (star α) = 1 → x' ≫ P.oA.act (star α) = 1 → x ≠ x' →
    ∃ z : TFK (R := V) F ⟶ P.A.A, z ≫ P.oA.act α = 1 ∧
      ∃ c c' : Γ((TFK (R := V) F).left, ⊤)ˣ,
        WeilIs P.A.A P.A.L N z x c ∧ WeilIs P.A.A P.A.L N z x' c' ∧ c ≠ c'

end Unif

end GlobalTheory.TorsionFactsCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilPairingPowPolAVEqProdField
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.WeilPower

open GlobalTheory.CommutatorPairing GlobalTheory.BoxPhi

variable {S : Scheme.{0}} {j : ℕ} {A A' : PolAV S} (pA : IsPowPolAV A' A j) {k : ℤ} {T : Over S}

theorem exists_box_theta (x : T ⟶ A'.A) (θ : Fin j → ThetaGrp A.A A.L k T) (hθ : ∀ i, (θ i).pt = x ≫ pA.pr i) :
    ∃ θ' : ThetaGrp A'.A A'.L k T, θ'.pt = x ∧ ∀ (Z : Over S) (t : Z ⟶ T) (a : Z ⟶ A'.A) (z : Z.left) (J J'),
      Good A.L z J → Good A'.L z J' →
      om pA.w z J J' a.left ^ k * om pA.w z J J' ((t ≫ x) * a).left ^ (-k) * thetaVal θ' t a z J' =
        ∏ i, thetaVal (θ i) t (a ≫ pA.pr i) z J := by
  have hP : ∀ i, translPt A'.A x ≫ pA.pr i = T ◁ pA.pr i ≫ translPt A.A (θ i).pt := fun i => by
    have := pA.hom i
    rw [hθ, BoxTheta.translPt_hom]
  obtain ⟨u, hu, hv⟩ := exists_box_gen (pr := fun i => (pA.pr i).left) A.isLB A'.isLB pA.w pA.w_gen (K := Fin 2)
    (φ' := ![(snd T A'.A).left, (translPt A'.A x).left])
    (φ := fun i => ![(snd T A.A).left, (translPt A.A (θ i).pt).left]) (ε := ![k, -k])
    (p := fun i => (T ◁ pA.pr i).left) (fun i a => by
      fin_cases a
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T (pA.pr i)).symm
      · exact congrArg (fun q => q.left) (hP i)) (fun i => (θ i).φ) (fun i => (θ i).isGen)
  refine ⟨⟨x, u, hu⟩, rfl, fun Z t a z J J' hJ hJ' => ?_⟩
  have e := hv _ (lift t a).left z J J' hJ hJ'
  rw [prod_theta x t a (om pA.w z J J')] at e
  refine e.trans (Finset.prod_congr rfl fun i _ => ?_)
  rw [← Over.comp_left, lift_whiskerLeft]
  rfl

theorem commVal_pow (hG : GlobalFnsSt) (θx' θy' : ThetaGrp A'.A A'.L k T) (θx θy : Fin j → ThetaGrp A.A A.L k T)
    (hx : ∀ i, (θx i).pt = θx'.pt ≫ pA.pr i) (hy : ∀ i, (θy i).pt = θy'.pt ≫ pA.pr i)
    {Z : Over S} (t : Z ⟶ T) (a : Z ⟶ A'.A) (z : Z.left) {J J'} (hJ : Good A.L z J) (hJ' : Good A'.L z J') :
    commVal θx' θy' t a z J' = ∏ i, commVal (θx i) (θy i) t (a ≫ pA.pr i) z J := by
  have := A'.isAb.comm
  obtain ⟨bx, ex, vx⟩ := exists_box_theta pA θx'.pt θx hx
  obtain ⟨by', ey, vy⟩ := exists_box_theta pA θy'.pt θy hy
  rw [commVal_indep hG A'.isAb A'.isLB θx' θy' bx by' t t (by rw [ex]) (by rw [ey]) a z J' hJ']
  have m : ∀ (x : T ⟶ A'.A) (i), ((t ≫ x) * a) ≫ pA.pr i = (t ≫ x ≫ pA.pr i) * (a ≫ pA.pr i) := fun x i => by
    have := pA.hom i
    rw [MonObj.mul_comp, Category.assoc]
  have e₁ := vx Z t a z J J' hJ hJ'
  have e₂ := vy Z t ((t ≫ θx'.pt) * a) z J J' hJ hJ'
  have e₃ := vy Z t a z J J' hJ hJ'
  have e₄ := vx Z t ((t ≫ θy'.pt) * a) z J J' hJ hJ'
  rw [mul_left_comm (t ≫ θy'.pt)] at e₂
  simp only [m, ← hx, ← hy] at e₂ e₄
  simp only [commVal, Finset.prod_mul_distrib, Finset.prod_inv_distrib, ← e₁, ← e₂, ← e₃, ← e₄, ex, ey, zpow_neg]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem weilIs_pow (hG : GlobalFnsSt) [Subsingleton T.left] (x y : T ⟶ A'.A) (c : Fin j → Γ(T.left, ⊤)ˣ)
    (h : ∀ i, WeilIs A.A A.L k (x ≫ pA.pr i) (y ≫ pA.pr i) (c i)) : WeilIs A'.A A'.L k x y (∏ i, c i) := by
  intro p
  have h' : ∀ i, (∃ θx θy : ThetaGrp A.A A.L k (overRes ⊤), θx.pt = overResι ⊤ ≫ x ≫ pA.pr i ∧
      θy.pt = overResι ⊤ ≫ y ≫ pA.pr i) ∧ ∀ θx θy : ThetaGrp A.A A.L k (overRes ⊤),
      θx.pt = overResι ⊤ ≫ x ≫ pA.pr i → θy.pt = overResι ⊤ ≫ y ≫ pA.pr i →
      CommIsOf A.A A.L k θx θy (unitRes ⊤ (c i)) := fun i => by
    obtain ⟨V, hV, H⟩ := h i p
    obtain rfl : V = ⊤ := top_le_iff.1 fun q _ => by rw [Subsingleton.elim q p]; exact hV
    exact H
  choose θx θy hx hy using fun i => (h' i).1
  obtain ⟨bx, ex, -⟩ := exists_box_theta pA (overResι ⊤ ≫ x) θx (fun i => by rw [hx, Category.assoc])
  obtain ⟨by', ey, -⟩ := exists_box_theta pA (overResι ⊤ ≫ y) θy (fun i => by rw [hy, Category.assoc])
  refine ⟨⊤, trivial, ⟨bx, by', ex, ey⟩, fun θx' θy' ex' ey' => (commIsOf_iff A'.isLB _ _ _).2 fun Z t a z J' hJ' => ?_⟩
  choose J hJ using fun χ : Z.left ⟶ A.A.left => exists_chart A.isLB (χ z)
  rw [commVal_pow pA hG θx' θy' θx θy (fun i => by rw [hx, ex', Category.assoc])
    (fun i => by rw [hy, ey', Category.assoc]) t a z hJ hJ']
  refine (Finset.prod_congr rfl fun i _ => (commIsOf_iff A.isLB _ _ _).1 ((h' i).2 _ _ (hx i) (hy i)) Z t _ z J hJ).trans ?_
  exact (map_prod _ _ _).symm.trans (congrArg _ (map_prod (Units.map (⊤ : T.left.Opens).ι.appTop.hom.toMonoidHom) c _).symm)

theorem weilIs_pow_field : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (pA : IsPowPolAV A' A j) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (x x' : TFK (R := R) F ⟶ A'.A) (c : Fin j → Fˣ), (∀ i, WeilIs A.A A.L k (x ≫ pA.pr i) (x' ≫ pA.pr i) (unitOn (c i))) → WeilIs A'.A A'.L k x x' (unitOn (∏ i, c i)) := by
  intro hL _ _ _ R _ _ j A A' pA F _ _ k _ x x' c h
  have : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (Spec (CommRingCat.of F)))
  have e : unitOn (∏ i, c i) = ∏ i, unitOn (c i) := map_prod (Units.map _) _ _
  rw [e]
  exact weilIs_pow pA hL.globalFns x x' (fun i => unitOn (c i)) h

end GlobalTheory.WeilPower
end
end

