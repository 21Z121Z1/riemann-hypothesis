import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3370
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2559
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2502
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3381
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3380

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDataSymmetricPullbackAndPsiEqTau
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensPsi

theorem tensorData_symmetric_pullback_and_psi_eq_tau : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D D' : DegData R I) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (A₀ : Matrix (Fin r) (Fin r) ℤ) (O : Type) [CommRing O] [StarRing O] [Module O D'.toPre.X] (o : D'.toPre.OAct O) (w₀ : O), o.onB.act w₀ = GlobalTheory.TensAct.matAct T A₀ → (∀ y : D'.toPre.X, w₀ • y = GlobalTheory.TensAct.latAct T A₀ y) → W = (W + W.transpose) * A₀ → TraceFormTwistIso D'.toPre o w₀ := by
  intro R _ _ I D D' r W T A₀ O _ _ _ o w₀ hact hlat hW
  have := o.onB.hom w₀
  obtain ⟨t, ht, vt⟩ := GlobalTheory.T.tensorData_mumfordSide_generator_values R I D D'.toPre W T A₀ (o.onB.act w₀) hact hW
  obtain ⟨u₀, hu₀, vu₀⟩ := GlobalTheory.T.exists_generator_transfer_through_tensorIso R D.toPre D'.toPre W T
    (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left, (o.onB.act w₀).left,
      (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → (D'.toPre.P.A.left ⟶ D'.toPre.P.A.left))
    ![1, -2, -1, 2] t ht
  obtain ⟨u, hu, hv⟩ := exists_gen D'.toPre.P.isLB
    (φ' := (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left, (o.onB.act w₀).left,
      (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → _)) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ rfl
        (DVR.prod_neg _ _ (GlobalTheory.PsiWZeroPull.prod_four (o.onB.act w₀) (1 : D'.toPre.P.A ⟶ D'.toPre.P.A) k))) ?_
      rw [MonObj.one_comp, _root_.mul_one (1 : D'.toPre.P.A ⟶ D'.toPre.P.A)]
      refine mul_eq_left.2 (inv_eq_one.2 ?_)
      group)
    (LB.mulGen D'.toPre.P.L _ _ _ _ u₀ (LB.invGen D'.toPre.P.L _ _ (LB.pullGen D'.toPre.P.L _ _ u₀ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu₀ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu₀ _)))
  refine ⟨u, hu, corr_of_val D'.toPre.P.isLB fun y J hJ => ?_, fun y => corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_⟩
  · have e : eSec D'.toPre.P.A ≫ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left = eSec D'.toPre.P.A :=
      congrArg (fun q : 𝟙_ (Over _) ⟶ D'.toPre.P.A => q.left) ((MonObj.comp_one (M := D'.toPre.P.A) η[D'.toPre.P.A]).trans (by simp [Hom.one_def]))
    rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, e, mul_inv_cancel]

  · choose J hJ using fun ψ : (TK R).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ z)
    let ω : ((TK R).left ⟶ D'.toPre.P.A.left) → ((TK R).left.presheaf.stalk z)ˣ := fun ψ =>
      gm ψ z _ (T.w.s (fun k => J (ψ ≫ tensφ T.pr k), J' ψ))
    let Tv : D'.toPre.X → ((TK R).left.presheaf.stalk z)ˣ := fun v =>
      ∏ i, ∏ j, val (D.toPre.tau (T.xe v i) (T.xe v j)) (𝟙 _) z J ^ W i j
    have hψ : ∀ v, val (D'.toPre.psi v) (𝟙 _) z J' = ω (D'.toPre.xK v) * Tv v := fun v => T.psi v z J J' hJ hJ'
    have k0 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left =
        D'.toPre.xK (x + w₀ • x) := by
      intro x
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left =
        (toUnit (TK R) ≫ D'.toPre.c (x + w₀ • x)).left
      congr 1
      rw [D'.toPre.c_add, o.c_lin]
      simp only [padd, ← Category.assoc, comp_lift, Category.comp_id]
    have k2 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (o.onB.act w₀).left = D'.toPre.xK (w₀ • x) := by
      intro x
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ o.onB.act w₀).left = (toUnit (TK R) ≫ D'.toPre.c (w₀ • x)).left
      rw [o.c_lin, Category.assoc]
    have k3 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left = D'.toPre.xK 0 := by
      intro x
      have c0 : (toUnit (TK R) ≫ D'.toPre.c 0 : TK R ⟶ D'.toPre.P.A) = 1 := cPoint_zero (D := D'.toPre) (TK R)
      show ((toUnit (TK R) ≫ D'.toPre.c x) ≫ toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left = (toUnit (TK R) ≫ D'.toPre.c 0).left
      rw [c0, ← Category.assoc, toUnit_unique ((toUnit (TK R) ≫ D'.toPre.c x) ≫ toUnit D'.toPre.P.A) (toUnit (TK R))]
      simp [Hom.one_def]
    have k1 : ∀ x : D'.toPre.X, D'.toPre.xK x ≫ (1 : D'.toPre.P.A ⟶ D'.toPre.P.A).left = D'.toPre.xK 0 := by
      intro x
      have := k3 x
      rwa [← Hom.one_def] at this
    have F : ∀ x : D'.toPre.X, val u₀ (D'.toPre.xK x) z J' = (val (D'.toPre.psi (x + w₀ • x)) (𝟙 _) z J')⁻¹ *
        val (D'.toPre.psi x) (𝟙 _) z J' ^ (2 : ℤ) * val (D'.toPre.psi (w₀ • x)) (𝟙 _) z J' *
        (val (D'.toPre.psi 0) (𝟙 _) z J') ^ (-2 : ℤ) := by
      intro x
      have e1 : ω (D'.toPre.xK (x + w₀ • x)) ^ (1 : ℤ) * ω (D'.toPre.xK x) ^ (-2 : ℤ) *
          ω (D'.toPre.xK (w₀ • x)) ^ (-1 : ℤ) * ω (D'.toPre.xK 0) ^ (2 : ℤ) * val u₀ (D'.toPre.xK x) z J' =
          val t (D'.toPre.xK x) z J := by
        have h₀ := vu₀ _ (D'.toPre.xK x) z J J' hJ hJ'
        have h₁ : (∏ a : Fin 4, ω (D'.toPre.xK x ≫ (![(padd D'.toPre.P.A (𝟙 _) (o.onB.act w₀)).left, 𝟙 D'.toPre.P.A.left,
            (o.onB.act w₀).left, (toUnit D'.toPre.P.A ≫ η[D'.toPre.P.A]).left] : Fin 4 → (D'.toPre.P.A.left ⟶ D'.toPre.P.A.left)) a) ^
            (![1, -2, -1, 2] : Fin 4 → ℤ) a) * val u₀ (D'.toPre.xK x) z J' = val t (D'.toPre.xK x) z J := h₀
        rw [Fin.prod_univ_four] at h₁
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, neg_neg, Category.comp_id] at h₁
        rw [k0, k2, k3] at h₁
        exact h₁
      have e2 : val t (D'.toPre.xK x) z J = Tv (x + w₀ • x) ^ (-1 : ℤ) * Tv x ^ (2 : ℤ) * Tv (w₀ • x) ^ (1 : ℤ) *
          Tv 0 ^ (-2 : ℤ) := by
        have h₀ := vt x z J hJ
        rw [Fin.prod_univ_four] at h₀
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val, neg_neg] at h₀
        simp only [Tv, hlat]
        exact h₀
      rw [hψ, hψ, hψ, hψ]
      rw [e2] at e1
      apply Additive.ofMul.injective
      have e' := congrArg Additive.ofMul e1
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at e' ⊢
      linear_combination (norm := abel) e'
    have hu_y : ∀ x, val u (D'.toPre.xK x) z J' = val u₀ (D'.toPre.xK x) z J' * (val u₀ (D'.toPre.xK 0) z J')⁻¹ := by
      intro x
      rw [hv _ _ z J' hJ', val_mul hJ', val_inv, val_pull hJ', k1]
    have tau_e : ∀ a b : D'.toPre.X, val (D'.toPre.tau a b) (𝟙 _) z J' = val (D'.toPre.psi (a + b)) (𝟙 _) z J' *
        (val (D'.toPre.psi a) (𝟙 _) z J')⁻¹ * (val (D'.toPre.psi b) (𝟙 _) z J')⁻¹ * (val D'.toPre.rigK (𝟙 _) z J')⁻¹ :=
      fun a b => (val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·)
        ((val_mul hJ' _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
    have p0 := GlobalTheory.PsiInPow.val_psi_zero D'.toPre D'.tau_bimult hJ'
    have f0 := F 0
    rw [smul_zero, add_zero] at f0
    rw [val_mul hJ', val_mul hJ', val_pull hJ', Category.id_comp, hu_y, F y, f0, tau_e, p0]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel

end GlobalTheory.TensPsi
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelLocalLatticeFourierPartsOrders
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem local_lattice_orders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∀ (_ : NeZero S.N) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, ∃ (r : ℕ) (b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : (Fin 8 → Fin r → ZMod S.N) → (Fin 8 → Fin r → ℤ)) (e : (Fin 8 → Fin r → ZMod S.N) → Ω), r ≤ g ∧ (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧ (∀ c u i, ((μ c u i : ℤ) : ZMod S.N) = c u i) ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) ∧ (∀ c, e c ≠ 0 ∧ ∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e c = S.FF T₀ c' κ / S.th x₀) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : (Fin r → ℤ) →+ T.D.toPre.X, Function.Surjective π ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) α) ∧ ∀ c, 0 ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ∧ OrdEq M T ξ (e c ^ S.N) (qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c)).toNat := by
  intro g n hg hn hodd F W hW o' Ω _ _ _ _ S ρ u hS hsh hgen hN M U₀ EE FinalForm hadm hEE x
  have hc : CompactSpace M.Z := by
    have := M.qc
    exact QuasiCompact.compactSpace_of_compactSpace M.s
  obtain ⟨y, hy, hyc⟩ := (isClosed_closure (s := ({x} : Set M.Z))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  have hxy : x ⤳ y := specializes_iff_mem_closure.2 hy
  obtain ⟨r, b₀, μ, e, h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.T.exists_rank_form_minimalTuples_at_closedPoint g n hg hn hodd F W hW o' Ω S ρ u hS hsh hgen hN M U₀ EE FinalForm hadm hEE y hyc
  exact ⟨r, b₀, μ, e, h1, h2, h3, h4, h5, h6, fun T ξ hT hξ => h7 T ξ hT (hξ.trans hxy)⟩

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupDividingLabelPersistsDeeperLevelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_dividingLabel_persists_deeperLevel : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁), ∀ (z₁ : X₁.M.Z) (x₀ : X₁.S.Gam), x₀ ∈ X₁.S.supI X₁.M z₁ → ∀ (z' : D.X.M.Z), D.q z' = z₁ → D.X.M.Div D.X.S.th (D.lab x₀) z' := by
  first | exact @GlobalTheory.Poinc.DivDeep.main | exact GlobalTheory.Poinc.DivDeep.main | (intros; apply GlobalTheory.Poinc.DivDeep.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupLabellingTransportGaloisConjugateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_labelling_transport_galoisConjugate : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X₁.M.s → ∀ (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), IsDiagEnd F W X₁.ρ.P X₁.u ε₁ → ∀ (D : Deep X₁ ε₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁), ∀ (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (c : CTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = c.y) (h' : (y ≫ s) ≫ D.q = c.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) (Fin 8 → c.T.D.toPre.X)), IsLab D.X D.ε (D.lift c y h) yy → IsLab D.X D.ε (D.lift c (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  first | exact @GlobalTheory.Poinc.GalTrans.isLab_conj | exact GlobalTheory.Poinc.GalTrans.isLab_conj | (intros; apply GlobalTheory.Poinc.GalTrans.isLab_conj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaShiftFunctionalEqSubConstFnSmul
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.HeatMod

section Values

variable {R : Type} [CommRing R] {X Y Z : Scheme.{0}}

def germConstHom (q : Z ⟶ Sp R) (z : Z) : R →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ ⊤ z trivial).hom.comp (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

theorem gs_id_scal_eq_germConstHom (q : Z ⟶ Sp R) (z : Z) (a : R) :
    gs (𝟙 Z) z ⊤ (scal q a) = germConstHom q z a := by
  rw [gs_eq (𝟙 Z) z ⊤ trivial]; rfl

theorem gs_constFn_eq_germConstHom (p : Y ⟶ Sp R) (r : Z ⟶ Y) (z : Z) (a : R) :
    gs r z ⊤ (constFn p ⊤ a) = germConstHom (r ≫ p) z a := by
  have : constFn p ⊤ a = (p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) := by
    unfold constFn
    rw [← Scheme.Hom.appLE_eq_app]; rfl
  exact (congrArg (gs r z ⊤) this).trans ((gs_eq r z ⊤ trivial _).trans rfl)

theorem sval_sub_constFn_smul {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (p : Y ⟶ Sp R)
    (s s' : LB.Sec (LB.LinComb L φ ε)) (a : R) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval (s' - constFn p ⊤ a • s) r z J = sval s' r z J - germConstHom (r ≫ p) z a * sval s r z J := by
  have hm := hJ.mem φ r
  have h₁ : sval (s' - constFn p ⊤ a • s) r z J + sval (constFn p ⊤ a • s) r z J = sval s' r z J :=
    (gs_add r z _ hm _ _).symm.trans (congrArg (gs r z _) (sub_add_cancel _ _))
  have h₂ : sval (constFn p ⊤ a • s) r z J = germConstHom (r ≫ p) z a * sval s r z J :=
    (gs_mul r z _ hm _ _).trans (congrArg₂ (· * ·)
      ((gs_res r z le_top hm _).trans (gs_constFn_eq_germConstHom p r z a)) rfl)
  rw [← h₁, h₂, add_sub_cancel_right]

end Values

theorem shiftEq_of_sub_constFn_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (k : ℕ) (mu α : Q.X) (σ σ' : Q.SecB k α) (σ₁ σ₁' : Q.SecB k (α + k • mu)) (c e e₁ : R), ShiftEq Q k mu α σ σ₁ 0 σ₁ → ShiftEq Q k mu α (σ' - constFn Q.P.A.hom ⊤ e • σ) (σ₁' - constFn Q.P.A.hom ⊤ e₁ • σ₁) c σ₁ → ShiftEq Q k mu α σ' σ₁' (c + e₁ - e) σ₁ := by
  intro R _ _ Q k mu α σ σ' σ₁ σ₁' c e e₁ h₀ h₁ u hu hc z J hJ
  have a₀ := h₀ u hu hc z J hJ
  have a₁ := h₁ u hu hc z J hJ
  rw [sval_sub_constFn_smul _ _ _ _ _ _ hJ, sval_sub_constFn_smul _ _ _ _ _ _ hJ, Over.w, Over.w,
    gs_id_scal_eq_germConstHom] at a₁
  rw [gs_id_scal_eq_germConstHom, map_zero, zero_mul, add_zero] at a₀
  rw [gs_id_scal_eq_germConstHom, map_sub, map_add]
  linear_combination a₁ + germConstHom (DegPre.BF Q (FractionRing R)).hom z e * a₀

end GlobalTheory.HeatMod
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageNonemptyOpenOfPointValueInjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.GenPtOpen

theorem top_le_preimage_of_valR_injective : ∀ (K : Type) [Field K] (P₀ : Out.PolAV (Sp K)), ∀ (F : Type) [Field F] (ψ : K →+* F) (ξ : Sp F ⟶ P₀.A.left), ξ ≫ P₀.A.hom = spMap ψ → (∀ O (f : Γ(P₀.A.left, O)), ⊤ ≤ ξ ⁻¹ᵁ O → valR ξ O f = 0 → f = 0) → ∀ O : P₀.A.left.Opens, (O : Set P₀.A.left).Nonempty → ⊤ ≤ ξ ⁻¹ᵁ O := by
  intro K _ P₀ F _ ψ ξ _ H O hO
  haveI : IsIntegral P₀.A.left := GlobalTheory.isIntegral_left_of_isAbelianScheme_field P₀.A P₀.isAb
  by_contra hno
  haveI : Subsingleton (Sp F) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨p⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have key : ∀ V : P₀.A.left.Opens, ξ p ∈ V → ⊤ ≤ ξ ⁻¹ᵁ V := fun V hV y _ => by
    rw [Subsingleton.elim y p]; exact hV
  obtain ⟨U, hU, hxU, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    P₀.A.left.isBasis_affineOpens) (show ξ p ∈ (⊤ : P₀.A.left.Opens) from trivial)
  obtain ⟨y, hyU, hyO⟩ := nonempty_preirreducible_inter U.isOpen O.isOpen ⟨_, hxU⟩ hO
  obtain ⟨f, hfO, hyf⟩ := (show IsAffineOpen U from hU).exists_basicOpen_le (V := O) ⟨y, hyO⟩ hyU
  have hUt : ⊤ ≤ ξ ⁻¹ᵁ U := key U hxU
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at hyf
    exact hyf
  refine hf0 (H U f hUt ?_)
  by_contra hv
  have hu : IsUnit (valR ξ U f) := isUnit_iff_ne_zero.mpr hv
  have hb := (GlobalTheory.ZH.CrdCalc.isUnit_valR_iff ξ U hUt f).mp hu
  exact hno (hb.trans (ξ.preimage_mono hfO))

end GlobalTheory.GenPtOpen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartCompGenericFibreInclusionEqSpecChartMa
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LocReg

theorem comp_genι_eq_spMap_chartHom (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) :
    ξ ≫ genι Y = spMap (GlobalTheory.LocReg.chartHom Y U ξ hx) ≫ chart U := by
  have hx' : (ξ ≫ genι Y) (closedPoint (ChartRing k m d)) ∈ U.1 := hx
  have e1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (ξ ≫ genι Y)
  have e2 : Y.X.fromSpecStalk ((ξ ≫ genι Y) (closedPoint (ChartRing k m d))) =
      Spec.map (Y.X.presheaf.germ U.1 _ hx') ≫ U.2.fromSpec :=
    (U.2.fromSpecStalk_eq_fromSpecStalk hx').symm
  rw [e2, ← Spec.map_comp_assoc, Scheme.stalkClosedPointTo_comp] at e1
  rw [← e1, chart]
  congr 2
  exact (Scheme.Hom.germ_stalkMap_assoc (genι Y) U.1 (ξ (closedPoint _)) hx (Scheme.stalkClosedPointTo ξ)).trans rfl

end GlobalTheory.LocReg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartDerivationBoundaryParamMemSpanStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.toricChart_derivation_boundaryParam_mem_span : ∀ (A : Type) [CommRing A] (k : Type) [Field k] (m d : ℕ) (ψ : A →+* ChartRing k m d) (δ : Derivation ℤ A A) (D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (I : Ideal A), (∀ a ∈ I, δ a ∈ I) → (∀ a, D' (ψ a) = ψ (δ a)) → I.map ψ = Ideal.span {∏ i, bdParam k m d i} → ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  first | exact @GlobalTheory.ChartDerBd.deriv_bdParam_mem_span | exact GlobalTheory.ChartDerBd.deriv_bdParam_mem_span | (intros; apply GlobalTheory.ChartDerBd.deriv_bdParam_mem_span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricChartRingMapFlatAndComapMaximalIdeal
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.LocRegFlat

theorem germ_flat {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    (X.presheaf.germ U x hx).hom.Flat := by
  let _ := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)

theorem chartHom_flat_comap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (U : Y.X.affineOpens) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → ∀ mm : Ideal Γ(Y.X, U.1), mm.IsMaximal → (∀ f ∈ mm, genι Y (ξ (closedPoint _)) ∉ Y.X.basicOpen f) → (GlobalTheory.LocReg.chartHom Y U ξ hx).Flat ∧ (maximalIdeal (ChartRing k m d)).comap (GlobalTheory.LocReg.chartHom Y U ξ hx) = mm := by
  intro E _ _ _ H Dw l Xo c Y U k _ m d ξ hx he mm hmm hmem
  have key : GlobalTheory.LocReg.chartHom Y U ξ hx = ((Y.X.presheaf.germ U.1 (genι Y (ξ (closedPoint _))) hx ≫
      (genι Y).stalkMap (ξ (closedPoint _))) ≫ Scheme.stalkClosedPointTo ξ).hom := by
    have h := (genι Y).germ_stalkMap U.1 (ξ (closedPoint _)) hx
    unfold GlobalTheory.LocReg.chartHom
    rw [h]; rfl
  rw [key]
  simp only [CommRingCat.hom_comp]
  have hg := germ_flat U.2 _ hx
  have hs : ((genι Y).stalkMap (ξ (closedPoint _))).hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  refine ⟨(hg.comp hs).comp he.1, ?_⟩
  symm
  refine hmm.eq_of_le (Ideal.comap_ne_top _ (maximalIdeal.isMaximal _).ne_top) ?_
  intro f hf
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hu
  apply hmem f hf
  rw [Scheme.mem_basicOpen]
  simp only [RingHom.comp_apply] at hu
  exact isUnit_of_map_unit ((genι Y).stalkMap _).hom _ (isUnit_of_map_unit (Scheme.stalkClosedPointTo ξ).hom _ hu)
  exact hx
end GlobalTheory.LocRegFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusInvariantHeatOperatorPreservesWeightStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusInvariant_heatOperator_preserves_weight : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R) (h : Heat Y.H Y.q.left Q.P.L dd D), (∀ a (α : Q.X) (V : Y.H.left.Opens) f, IsWt Y α V f → IsWt Y α V (dd a V f)) → IsBasic Y h → ∀ (i : h.J) (k : ℕ) (α : Q.X) (f : Γ(Y.H.left, h.W i)), IsWt Y α (h.W i) f → IsWt Y α (h.W i) (op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) := by
  first | exact @GlobalTheory.Heat.WtAlg.op_isWt | exact GlobalTheory.Heat.WtAlg.op_isWt | (intros; apply GlobalTheory.Heat.WtAlg.op_isWt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusWeightScalarZeroCharacterEqOneStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torusWeightScalar_zeroCharacter_eq_one : ∀ {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X] {oa : Q.OAct O} (Y : Ray oa) (S : Type) [CommRing S] (φ : R →+* S) (x x' : Over.mk (spMap φ) ⟶ Y.H) (c : Q.X → Sˣ), x' ≫ Y.q = x ≫ Y.q → (∀ χ y J, Good Q.P.L y J → val ((Y.Φ _ x').s χ) (𝟙 _) y J = gm (𝟙 (Over.mk (spMap φ)).left) y ⊤ (unitOn (c χ)) * val ((Y.Φ _ x).s χ) (𝟙 _) y J) → c 0 = 1 := by
  first | exact @GlobalTheory.Heat.weight_scalar_zero_eq_one | exact GlobalTheory.Heat.weight_scalar_zero_eq_one | (intros; apply GlobalTheory.Heat.weight_scalar_zero_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransitionUnitPointValueCocycle
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CocVal

theorem valR_pos {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f : Γ(X, U)) : valR x U f = (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((x.appLE U ⊤ h).hom f) := dif_pos h

theorem valR_map_le {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) :
    valR x V ((X.presheaf.map (homOfLE hVU).op).hom f) = valR x U f := by
  have hU : ⊤ ≤ x ⁻¹ᵁ U := h.trans (x.preimage_mono hVU)
  rw [valR_pos x V h, valR_pos x U hU]
  congr 1
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

theorem valR_mul_pos {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (f g : Γ(X, U)) : valR x U (f * g) = valR x U f * valR x U g := by
  simp only [valR_pos x U h, map_mul]

theorem top_le_inf {A : Type} [CommRing A] {X : Scheme.{0}} (x : Sp A ⟶ X) {U V : X.Opens}
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hV : ⊤ ≤ x ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ (U ⊓ V) :=
  fun p _ => ⟨hU trivial, hV trivial⟩

theorem valR_cocycle : ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (F : Type) [Field F] (ξ : Sp F ⟶ X)
    (j j' j'' : L.ι), ⊤ ≤ ξ ⁻¹ᵁ L.U j → ⊤ ≤ ξ ⁻¹ᵁ L.U j' → ⊤ ≤ ξ ⁻¹ᵁ L.U j'' →
    valR ξ (L.U j ⊓ L.U j') (L.g j j').val * valR ξ (L.U j' ⊓ L.U j'') (L.g j' j'').val =
      valR ξ (L.U j ⊓ L.U j'') (L.g j j'').val := by
  intro X L hL F _ ξ j j' j'' h1 h2 h3
  have h123 : ⊤ ≤ ξ ⁻¹ᵁ (L.U j ⊓ L.U j' ⊓ L.U j'') := top_le_inf ξ (top_le_inf ξ h1 h2) h3
  have e := congrArg (fun u : Γ(X, L.U j ⊓ L.U j' ⊓ L.U j'')ˣ => valR ξ _ u.val) (hL.cocycle j j' j'')
  simp only [Units.val_mul] at e
  rw [valR_mul_pos ξ _ h123] at e
  simp only [res, Units.coe_map, MonoidHom.coe_coe] at e
  rw [valR_map_le ξ _ h123, valR_map_le ξ _ h123, valR_map_le ξ _ h123] at e
  exact e

end GlobalTheory.CocVal
end
end

