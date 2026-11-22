import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0742
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullDegEquivApply
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.Transport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriesAtRev
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0743
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0704
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0641
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0637

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperGeometricallyConnectedSmoothNilpotentLifStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isProper_geometricallyConnected_smooth_nilpotent_lift : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    IsProper X₀.hom → GeometricallyConnected X₀.hom → IsProper X.hom ∧ GeometricallyConnected X.hom := by
  first | exact @GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift | exact GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift | (intros; apply GlobalTheory.NilLift.isProper_and_geometricallyConnected_of_smooth_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullDegIdentitySymm
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification (CarriesAt PullIdent)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.PullDegSymm

namespace GlobalTheory.PullDegSymm

theorem carriesAt_gm {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)}
    {p' : Y ⟶ X'} {p : Y ⟶ X} {hp : p' ≫ F = p} {n : ℤ}
    {a : LB.Gen (LB.LinComb L' (K := PUnit) (fun _ => p') (fun _ => n))}
    {b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))}
    (H : CarriesAt L L' F w p' p hp n a b) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (j : L.ι) (j' : L'.ι)
    (h₁ : F (p' (r z)) ∈ L.U j) (h₂ : p' (r z) ∈ L'.U j') :
    gm r z (LB.wchart L (fun _ : PUnit => p) (fun _ => j)) (b.s (fun _ => j)) =
      gw w (r ≫ p') z j j' ^ n * gm r z (LB.wchart L' (fun _ : PUnit => p') (fun _ => j')) (a.s (fun _ => j')) := by
  have hm : r z ∈ p' ⁻¹ᵁ (LB.div (L.pull F) L').U (fun _ => j, j') := ⟨mem_pull.2 h₁, h₂⟩
  have e := congrArg (gm r z _) (H j j')
  refine (gm_res _ z _ hm _).symm.trans (e.trans ?_)
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans (congrArg (· ^ n)
    (gm_pull _ _ z _ hm _))) (gm_res _ z _ hm _))

theorem exists_psiOn_rev : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (p : PullIdent (RingHom.id R) D D')
    (W : (Spec (CommRingCat.of R)).Opens) (ψW : PsiOn D W) (g : (TK R).left ⟶ (TW W).left)
    (hg : g ≫ W.ι = jK R ≫ GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)),
    (∀ χ : D'.X, CarriesAt D.P.L D'.P.L p.F p.w (D'.xK χ) (g ≫ (toUnit (TW W) ≫ D.c (p.xe χ)).left)
      (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.ptK_comp (RingHom.id R) p.F (D.c (p.xe χ)) (D'.c χ) (p.c_eq χ) W g hg) (-1) (D'.psi χ)
      (LB.pullGen D.P.L _ _ (ψW.psi (p.xe χ)) g)) →
    ∃ ψW' : PsiOn D' W, ∀ χ : D'.X, PMaps p.w (K := PUnit) (fun _ => (toUnit (TW W) ≫ D'.c χ).left)
      (fun _ => (toUnit (TW W) ≫ D.c (p.xe χ)).left) (fun _ => -1) (ψW'.psi χ) (ψW.psi (p.xe χ)) (𝟙 _) := by
  intro R _ _ D D' p W ψW g hg H
  have hgj : g ≫ W.ι = jK R := by rw [hg, specOf_id', Category.comp_id]
  have hc : ∀ χ : D'.X, ∀ _ : PUnit, (toUnit (TW W) ≫ D'.c χ).left ≫ p.F =
      𝟙 _ ≫ (toUnit (TW W) ≫ D.c (p.xe χ)).left := by
    intro χ _
    show (W.ι ≫ (D'.c χ).left) ≫ p.F = 𝟙 _ ≫ W.ι ≫ (D.c (p.xe χ)).left
    rw [Category.assoc, p.c_eq, specOf_id', Category.id_comp, Category.id_comp]
  choose ψ hψg hψm using fun χ : D'.X => GlobalTheory.DegPull.exists_pmaps ((isGen_iff _).1 p.w_gen) D.P.isLB
    D'.P.isLB (𝟙 _) (hc χ) (ψW.psi (p.xe χ)) (ψW.psi_gen _)
  refine ⟨⟨ψ, hψg, fun χ => ?_⟩, hψm⟩
  apply corr_of_val D'.P.isLB
  intro y J hJ
  rw [val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp]
  have hr : (jK R ∣_ W) ≫ W.ι = (jK R ⁻¹ᵁ W).ι ≫ jK R := morphismRestrict_ι _ _
  have hιg : (jK R ⁻¹ᵁ W).ι ≫ g = jK R ∣_ W := by
    rw [← cancel_mono W.ι, Category.assoc, hgj, hr]
  have hpt : (jK R ∣_ W) ≫ (toUnit (TW W) ≫ D'.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ D'.xK χ := by
    show (jK R ∣_ W) ≫ W.ι ≫ (D'.c χ).left = (jK R ⁻¹ᵁ W).ι ≫ jK R ≫ (D'.c χ).left
    rw [← Category.assoc, hr, Category.assoc]
  obtain ⟨jD, hjD⟩ := exists_chart D.P.isLB (p.F (((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ) y))
  have mq : ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ) y ∈ D'.P.L.U (J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) := hJ _
  have k1 := hψm χ _ (jK R ∣_ W) y (fun _ => jD) (fun _ => J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ))
    (fun _ => (congrArg (fun f => p.F (f y) ∈ D.P.L.U jD) hpt).mpr hjD)
    (fun _ => (congrArg (fun f => f y ∈ D'.P.L.U (J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ))) hpt).mpr mq)
  rw [Category.comp_id, Fintype.prod_unique, hpt] at k1
  have k2 := carriesAt_gm (H χ) (jK R ⁻¹ᵁ W).ι y jD (J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) hjD mq
  have hq : (jK R ⁻¹ᵁ W).ι ≫ g ≫ (toUnit (TW W) ≫ D.c (p.xe χ)).left =
      ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ) ≫ p.F := by
    rw [← Category.assoc, hιg, ← hpt, Category.assoc, hc χ PUnit.unit, Category.id_comp]
  have a := gm_pullGen D.P.L _ _ (ψW.psi (p.xe χ)) g (jK R ⁻¹ᵁ W).ι y (fun _ => jD)
    (Set.mem_iInter.2 fun _ => (congrArg (fun f => f y ∈ D.P.L.U jD) hq).mpr hjD)
  rw [hιg] at a
  rw [val_of (ψ χ) (jK R ∣_ W) y J (fun _ => J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) (fun _ => by rw [hpt]),
      val_of (D'.psi χ) (jK R ⁻¹ᵁ W).ι y J (fun _ => J ((jK R ⁻¹ᵁ W).ι ≫ D'.xK χ)) (fun _ => rfl)]
  exact mul_left_cancel (k1.symm.trans (a.symm.trans k2))

theorem psiOn_carries_pullbackIdent_reverse_of_pmaps {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} (p : PullIdent (RingHom.id R) D D')
    {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) {g : (TK R).left ⟶ (TW W).left}
    (hg : g ≫ W.ι = jK R ≫ GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (ψW' : PsiOn D' W)
    (hψ : ∀ χ : D'.X, PMaps p.w (K := PUnit) (fun _ => (toUnit (TW W) ≫ D'.c χ).left)
      (fun _ => (toUnit (TW W) ≫ D.c (p.xe χ)).left) (fun _ => -1) (ψW'.psi χ) (ψW.psi (p.xe χ)) (𝟙 _))
    (χ : D.X) (χ' : D'.X) (hχ : p.xe χ' = χ) (hx : D.xK χ ≫ Finv p = g ≫ (toUnit (TW W) ≫ D'.c χ').left) :
    CarriesAt D'.P.L D.P.L (Finv p) (wInv p) (D.xK χ) (g ≫ (toUnit (TW W) ≫ D'.c χ').left) hx (-1) (D.psi χ)
      (LB.pullGen D'.P.L _ _ (ψW'.psi χ') g) := by
  subst hχ
  rw [carriesAt_iff]
  intro y j jD h₁ h₂
  have hgj : g ≫ W.ι = jK R := by rw [hg, specOf_id', Category.comp_id]
  have hP : g ≫ (toUnit (TW W) ≫ D.c (p.xe χ')).left = D.xK (p.xe χ') := by
    show g ≫ W.ι ≫ (D.c (p.xe χ')).left = jK R ≫ (D.c (p.xe χ')).left
    rw [← Category.assoc, hgj]
  have m₁ : (toUnit (TW W) ≫ D'.c χ').left (g y) ∈ D'.P.L.U j :=
    (congrArg (fun f => f y ∈ D'.P.L.U j) hx).mp h₁
  have m₂ : p.F ((toUnit (TW W) ≫ D'.c χ').left (g y)) ∈ D.P.L.U jD := by
    have : p.F ((toUnit (TW W) ≫ D'.c χ').left (g y)) = D.xK (p.xe χ') y := by
      have e := congrArg (fun f => f y) hx
      exact (congrArg p.F e.symm).trans (base_cancel (Finv_F p) _)
    rw [this]; exact h₂
  have k := hψ χ' (TK R).left g y (fun _ => jD) (fun _ => j) (fun _ => m₂) (fun _ => m₁)
  rw [Category.comp_id, Fintype.prod_unique] at k
  obtain ⟨J, hJ, eJ⟩ := exists_good D.P.L D.P.isLB y (fun _ : PUnit => D.xK (p.xe χ')) (fun _ => jD)
    (fun _ _ _ => rfl) (fun _ => h₂)
  have v := GlobalTheory.ArcSpecialise.psiOn_generic ψW (p.xe χ') g (𝟙 _) (by rw [hgj, Category.id_comp]) hJ
  rw [val_of _ g y J (fun _ => jD) (fun _ => by rw [hP]; exact eJ PUnit.unit),
    val_of _ (𝟙 _) y J (fun _ => jD) (fun _ => by rw [Category.id_comp]; exact eJ PUnit.unit)] at v
  have a₁ := gm_pullGen D'.P.L _ _ (ψW'.psi χ') g (𝟙 _) y (fun _ => j) (Set.mem_iInter.2 fun _ => m₁)
  rw [Category.id_comp] at a₁
  have key : ∀ {G : Type} [CommGroup G] (A B C E : G), C = A ^ (-1 : ℤ) * B → C = E → B = A⁻¹ ^ (-1 : ℤ) * E := by
    intro G _ A B C E h₁ h₂
    rw [← h₂, h₁]; group
  refine a₁.trans ?_
  rw [show gw (wInv p) (D.xK (p.xe χ')) y j jD = _ from gw_revIso p.w (Finv_F p) _ y j jD h₁ h₂, hx]
  exact key _ _ _ _ k v

theorem psi_carries_rev : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R) (p : PullIdent (RingHom.id R) D D')
    (W : (Spec (CommRingCat.of R)).Opens) (ψW : PsiOn D W) (g : (TK R).left ⟶ (TW W).left)
    (hg : g ≫ W.ι = jK R ≫ GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.specOf (RingHom.id R)) (ψW' : PsiOn D' W),
    (∀ χ : D'.X, PMaps p.w (K := PUnit) (fun _ => (toUnit (TW W) ≫ D'.c χ).left)
      (fun _ => (toUnit (TW W) ≫ D.c (p.xe χ)).left) (fun _ => -1) (ψW'.psi χ) (ψW.psi (p.xe χ)) (𝟙 _)) →
    ∀ χ : D.X, CarriesAt D'.P.L D.P.L (GlobalTheory.PullDegSymm.Finv p) (GlobalTheory.PullDegSymm.wInv p) (D.xK χ)
      (g ≫ (toUnit (TW W) ≫ D'.c (p.xe.symm χ)).left)
      (GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification.ptK_comp (RingHom.id R) (GlobalTheory.PullDegSymm.Finv p) (D'.c (p.xe.symm χ)) (D.c χ)
        (GlobalTheory.PullDegSymm.c_eq' p χ) W g hg) (-1) (D.psi χ) (LB.pullGen D'.P.L _ _ (ψW'.psi (p.xe.symm χ)) g) := fun R _ _ D D' p W ψW g hg ψW' hψ χ =>
  psiOn_carries_pullbackIdent_reverse_of_pmaps p ψW hg ψW' hψ χ (p.xe.symm χ) (p.xe.apply_symm_apply χ) _

theorem isPullDeg_symm : ∀ (R : Type) [CommRing R] [IsDomain R] (D D' : DegPre R),
    IsPullDeg (RingHom.id R) D D' → Nonempty (IsPullDeg (RingHom.id R) D' D) := by
  intro R _ _ D D' hD
  obtain ⟨p⟩ := GlobalTheory.PullDegCompare.nonempty_iff.1 ⟨hD⟩
  obtain ⟨W, ψW, g, hg, H⟩ := p.w_psi
  obtain ⟨ψW', hψ⟩ := exists_psiOn_rev R D D' p W ψW g hg H
  exact GlobalTheory.PullDegCompare.nonempty_iff.2 ⟨⟨Finv p, cart' p, F_one' p, F_mul' p, wInv p, wInv_isGen p, w_rig' p,
    p.xe.symm, c_eq' p, ⟨W, ψW', g, hg, psi_carries_rev R D D' p W ψW g hg ψW' hψ⟩⟩⟩

end GlobalTheory.PullDegSymm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTestPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isTest_comp_isPullD_of_isTest : ∀ (Rg : Type) [CommRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (T T' : Scheme.{0}) (t : T ⟶ Sp Rg) (h : T' ⟶ T) (A₁ B₁ : Over T) [GrpObj A₁] [GrpObj B₁] (φA₁ : A₁.left ⟶ A.left) (φB₁ : B₁.left ⟶ B.left) (Φ₁ : A₁ ⟶ B₁), IsTest A B L M t A₁ B₁ φA₁ φB₁ Φ₁ → ∃ (A₂ : Over T') (_ : GrpObj A₂) (B₂ : Over T') (_ : GrpObj B₂) (φA₂ : A₂.left ⟶ A.left) (φB₂ : B₂.left ⟶ B.left) (Φ₂ : A₂ ⟶ B₂), IsTest A B L M (h ≫ t) A₂ B₂ φA₂ φB₂ Φ₂ ∧ IsPullD φA₁ φB₁ Φ₁ φA₂ φB₂ Φ₂ h := by
  first | (exact @GlobalTheory.HomFixMat.isTest_pullback) | (exact GlobalTheory.HomFixMat.isTest_pullback) | (intros; apply GlobalTheory.HomFixMat.isTest_pullback  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFormulaWeierstrassPIntegral
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.IsogFormula

theorem main : ∀ (L : PeriodPair) (α β Ω P : ℂ) (M n : ℕ), MulStable L β → β.im ≠ 0 → Ω ^ 12 = latDisc L → MulStable L α → Complex.normSq α = n → 0 < n → 0 < M → P ∉ L.lattice → (M : ℂ) * P ∈ L.lattice → IsIntegral ℤ (((M * n : ℕ) : ℂ) ^ 2 * ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2) - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2))) := by
  intro L α β Ω P M n hβ hβim hΩ hα hnorm hn hM hP hMP
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [map_zero] at hnorm
    have h0 : n = 0 := by exact_mod_cast hnorm.symm
    omega
  obtain ⟨S, hS⟩ := kernel_reps_exist L α hα0 hα
  have hcard := kernel_reps_card L α S hα0 hα hS
  have hs2 := quasiPeriodConstIsogeny_thm L α S hα0 hα hS
  obtain ⟨t, m, ht, hm, -⟩ := mul_stable_integral L α hα
  have hcardn : S.card + 1 = n := by
    rw [hnorm] at hcard
    exact_mod_cast hcard
  have hVL := (GlobalTheory.T.isIntegral_weierstrassP_torsion_nonreal_multiplier L β Ω (M * n) hβ hβim hΩ (Nat.mul_pos hM hn)).2
  have hnat : ∀ (k : ℕ) (x : ℂ), x ∈ L.lattice → (k : ℂ) * x ∈ L.lattice := by
    intro k x hx
    have := L.lattice.nsmul_mem hx k
    simpa [nsmul_eq_mul] using this
  have hconj : ∀ ω ∈ L.lattice, conj α * ω ∈ L.lattice := by
    intro ω hω
    have hc : conj α = (t : ℂ) - α := by rw [← ht]; ring
    rw [hc, sub_mul]
    refine L.lattice.sub_mem ?_ (hα ω hω)
    have := L.lattice.smul_mem t hω
    simpa [zsmul_eq_mul] using this
  have hnT : ∀ T ∈ S, (n : ℂ) * T ∈ L.lattice := by
    intro T hT
    have h1 := hconj _ (hS.1 T hT).1
    have hn' : (n : ℂ) = conj α * α := by
      rw [mul_comm, Complex.mul_conj, hnorm]
      simp
    rw [hn', mul_assoc]
    exact h1
  have hs2' : (α ^ 2 - (n : ℂ)) * s2 L = ∑ T ∈ S, L.weierstrassP T := by
    rw [← hs2, hnorm]
    simp
  have hnc : (n : ℂ) = (S.card : ℂ) + 1 := by exact_mod_cast hcardn.symm
  have key : ((M * n : ℕ) : ℂ) ^ 2 * ((α ^ 2 - n) * ((s2 L + L.weierstrassP P) / Ω ^ 2)
      - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2))
      = ∑ T ∈ S, ((M * n : ℕ) : ℂ) ^ 2 * (L.weierstrassP T - L.weierstrassP P) / Ω ^ 2 := by
    have e1 : ∑ T ∈ S, ((M * n : ℕ) : ℂ) ^ 2 * (L.weierstrassP T - L.weierstrassP P) / Ω ^ 2
        = ((M * n : ℕ) : ℂ) ^ 2 * (∑ T ∈ S, L.weierstrassP T - (S.card : ℂ) * L.weierstrassP P) / Ω ^ 2 := by
      rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [e1, ← hs2']
    rw [show (α ^ 2 - (n : ℂ)) * ((s2 L + L.weierstrassP P) / Ω ^ 2) - (α ^ 2 - 1) * (L.weierstrassP P / Ω ^ 2)
        = ((α ^ 2 - (n : ℂ)) * s2 L + (1 - (n : ℂ)) * L.weierstrassP P) / Ω ^ 2 by ring]
    rw [hnc]
    ring
  rw [key]
  refine IsIntegral.sum _ (fun T hT => ?_)
  refine hVL T P (hS.1 T hT).2 hP ?_ ?_
  · have h := hnat M _ (hnT T hT)
    rw [show ((M * n : ℕ) : ℂ) * T = (M : ℂ) * ((n : ℂ) * T) by push_cast; ring]
    exact h
  · have h := hnat n _ hMP
    rw [show ((M * n : ℕ) : ℂ) * P = (n : ℂ) * ((M : ℂ) * P) by push_cast; ring]
    exact h

end GlobalTheory.IsogFormula
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IterateLinearPart
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace GlobalTheory.LinearPartIteration

variable {R : Type} [CommRing R] {d : ℕ}

def part (F : MvPowerSeries (Fin d) R) (j : Fin d) : MvPowerSeries (Fin d) R :=
  fun α => if ∀ k < j, α k = 0 then coeff (α + Finsupp.single j 1) F else 0

theorem coeff_part (F : MvPowerSeries (Fin d) R) (j : Fin d) (α : Fin d →₀ ℕ) :
    coeff α (part F j) = if ∀ k < j, α k = 0 then coeff (α + Finsupp.single j 1) F else 0 := rfl

theorem constantCoeff_part (F : MvPowerSeries (Fin d) R) (j : Fin d) :
    constantCoeff (part F j) = coeff (Finsupp.single j 1) F := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_part]
  simp

theorem coeff_X_mul_part (F : MvPowerSeries (Fin d) R) (j : Fin d) (β : Fin d →₀ ℕ) :
    coeff β (X j * part F j) = if β j ≠ 0 ∧ ∀ k < j, β k = 0 then coeff β F else 0 := by
  classical
  rw [X_def, coeff_monomial_mul, one_mul, coeff_part]
  by_cases h : β j = 0
  · rw [if_neg, if_neg]
    · simp [h]
    · rw [Finsupp.single_le_iff]; omega
  · have hle : Finsupp.single j 1 ≤ β := by rw [Finsupp.single_le_iff]; omega
    rw [if_pos hle, tsub_add_cancel_of_le hle]
    have : (∀ k < j, (β - Finsupp.single j 1 : Fin d →₀ ℕ) k = 0) ↔ (β j ≠ 0 ∧ ∀ k < j, β k = 0) := by
      constructor
      · intro H
        refine ⟨h, fun k hk => ?_⟩
        have := H k hk
        rwa [Finsupp.tsub_apply, Finsupp.single_eq_of_ne hk.ne, Nat.sub_zero] at this
      · intro H k hk
        rw [Finsupp.tsub_apply, H.2 k hk, Nat.zero_sub]
    simp only [this]

theorem eq_const_add_sum (F : MvPowerSeries (Fin d) R) :
    F = C (constantCoeff F) + ∑ j, X j * part F j := by
  classical
  ext β
  rw [map_add, map_sum, coeff_C]
  simp only [coeff_X_mul_part]
  by_cases hβ : β = 0
  · subst hβ
    simp
  · rw [if_neg hβ, zero_add]
    have hne : β.support.Nonempty := Finsupp.support_nonempty_iff.2 hβ
    have h0 : β (β.support.min' hne) ≠ 0 := Finsupp.mem_support_iff.1 (β.support.min'_mem hne)
    have h1 : ∀ k < β.support.min' hne, β k = 0 := fun k hk => by
      by_contra hk0
      exact absurd (β.support.min'_le k (Finsupp.mem_support_iff.2 hk0)) (not_le.2 hk)
    rw [Finset.sum_eq_single (β.support.min' hne), if_pos ⟨h0, h1⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨h2, h3⟩
      rcases lt_or_gt_of_ne hj with h | h
      · exact h2 (h1 j h)
      · exact h0 (h3 _ h)
    · simp

theorem iterate_linear_part : ∀ (p : ℕ) [Fact (Nat.Prime p)] (R : Type) [inst : CommRing R] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R), (∀ (i : Fin d), (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d ⊕ Fin d) R → R) (μ i) = (0 : R)) → ((GlobalTheory.Katz.op μ (fun (i : Fin d) ↦ MvPowerSeries.X i) fun (x : Fin d) ↦ (0 : MvPowerSeries (Fin d) R)) = fun (i : Fin d) ↦ MvPowerSeries.X i) → (∀ (i : Fin d), GlobalTheory.Katz.swap (μ i) = μ i) → ∀ (u : Fin d → R) (F : MvPowerSeries (Fin d) R), ∃ (r : R), (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) R → R) ((GlobalTheory.LawDer.invDer μ u)^[p] F) - ∑ j : Fin d, (MvPowerSeries.constantCoeff : MvPowerSeries (Fin d) R → R) ((GlobalTheory.LawDer.invDer μ u)^[p] (MvPowerSeries.X j)) * (MvPowerSeries.coeff fun₀ | j => (1 : ℕ) : MvPowerSeries (Fin d) R → R) F = (↑p : R) * r := by
  intro p hp R _ d μ h0 h1 _ u F
  obtain ⟨hadd, hsmul, hC⟩ := GlobalTheory.T.invariantDerivationFormalGroupLaw_isLinear R d μ h0 u
  let D : MvPowerSeries (Fin d) R →ₗ[R] MvPowerSeries (Fin d) R :=
    { toFun := GlobalTheory.LawDer.invDer μ u, map_add' := hadd, map_smul' := hsmul }
  have hD : ∀ G, (GlobalTheory.LawDer.invDer μ u)^[p] G = (D ^ p) G := fun G => by
    rw [Module.End.pow_apply]; rfl
  have hDC : ∀ a : R, (D ^ p) (C a) = 0 := fun a => by
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hp.out.ne_zero
    rw [hn, pow_succ, Module.End.mul_apply, show D (C a) = 0 from hC a, map_zero]
  have key : ∀ j : Fin d, ∃ r : R, constantCoeff ((D ^ p)
      (X j * (part F j - C (coeff (Finsupp.single j 1) F)))) = p * r := fun j => by
    rw [← hD]
    exact GlobalTheory.T.constantCoeff_iterate_p_invariantDerivation_mul p R d μ h0 h1 u _ _ (by simp) (by simp [constantCoeff_part])
  choose r hr using key
  refine ⟨∑ j, r j, ?_⟩
  have hF : constantCoeff ((D ^ p) F) = ∑ j, constantCoeff ((D ^ p) (X j * part F j)) := by
    conv_lhs => rw [eq_const_add_sum F]
    rw [map_add, hDC, zero_add, map_sum, map_sum]
  simp only [hD]
  rw [hF, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hr j, mul_sub, map_sub, map_sub, mul_comm (X j) (C _), ← smul_eq_C_mul, map_smul,
    ← coeff_zero_eq_constantCoeff_apply ((_ : R) • _), map_smul, coeff_zero_eq_constantCoeff_apply,
    smul_eq_mul, mul_comm (constantCoeff _)]

end GlobalTheory.LinearPartIteration
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeISupOfUniformisationParametersCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.le_iSup_of_uniformisationParameters_cover : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (U : A.left.Opens) (K : Type) (W : K → A.left.Opens), (∀ z ∈ pre u.ex U, ∃ i, z ∈ pre u.ex (W i)) → U ≤ ⨆ i, W i := by
  first | exact @GlobalTheory.CechPer.le_iSup_of_pre_cover | exact GlobalTheory.CechPer.le_iSup_of_pre_cover | (intros; apply GlobalTheory.CechPer.le_iSup_of_pre_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralWeightedAtlasFrameEtaleTransfer
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.lintegral_frame_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → ∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A E U z β hE hβ a w ha hw hw0
  classical
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hc := api_nsq_contOn A hE.isOpen hβ.1
  have hm := ContinuousOn.measurable_piecewise hc
    (continuousOn_const (c := (0 : ℝ)) (s := Uᶜ)) hUm
  set N : Y → ℝ := U.piecewise (A.nsq (A.kap + E) β) (fun _ => 0) with hN
  have hNU : ∀ y ∈ U, N y = A.nsq (A.kap + E) β y := fun y hy => by simp [hN, hy]
  have hΦ : Measurable fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y) :=
    ENNReal.measurable_ofReal.comp ((hm.mul (ha.norm.pow_const 2)).mul hw)
  rw [setLIntegral_congr_fun hUm
    (g := fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y)) (fun y hy => by simp only [hNU y hy]),
    GlobalTheory.T.lintegral_atlasMeasure_etale_pullback_lebesgue n Y ι La A U z hE _ hΦ]
  refine lintegral_congr fun x => ?_
  have hJ : 0 < A.nsq A.kap (jdet A z) x := by
    have := hE.det_ne (A.pick (x : Y)) x x.2 (A.mem_pick _)
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hB : 0 < A.nsq (A.kap + E) β x := by
    have : β (A.pick (x : Y)) x ≠ 0 := by
      exact hβ.2 _ x.2
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hwx := hw0 x x.2
  rw [hNU x x.2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold GlobalTheory.OTY.TwEst.wt
  rw [neg_add, neg_neg, Real.exp_add, Real.exp_neg, Real.exp_log hB, Real.exp_log hJ]
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCocycleCohomologousStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_cocycle_cohomologous_alt : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg) := by
  first | exact @GlobalTheory.AnPer.log_cocycle_cohomologous | exact GlobalTheory.AnPer.log_cocycle_cohomologous | (intros; apply GlobalTheory.AnPer.log_cocycle_cohomologous <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneWhittakerVectorDimHolds
section
namespace GlobalTheory.GenericProduct

theorem oneGenericVector : OneGenericVector := GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one

theorem genericMultOne_holds : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne := genericMultOne oneGenericVector

theorem oneWhittakerVector_holds : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector :=
  GlobalTheory.CuspidalIdempotentCharacters.genericMultOne_iff.1 genericMultOne_holds

end GlobalTheory.GenericProduct
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupChartIntegralAdditiveSeriesEqZeroStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroupChart_integral_additive_series_eq_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ s : MvPowerSeries (Fin d) O, cob1 (up E c.μ) (map (algebraMap O E) s) = 0 → s = 0 := by
  first | exact @GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero | exact GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero | (intros; apply GlobalTheory.QLog.IntAdd.eq_zero_of_cob1_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIdempotentSplitField
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

set_option autoImplicit false

noncomputable section

namespace GlobalTheory

namespace PDivGroup

theorem idempotent_split (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k)
    (u v : G ⟶ G) (huv : u + v = 𝟙 G) (h1 : u ≫ v = 0) (h2 : v ≫ u = 0) :
    ∃ (K : PDivGroup p k) (i : K ⟶ G) (q : G ⟶ K), i ≫ q = 𝟙 K ∧ q ≫ i = v ∧
      ∀ n : ℕ, Function.Surjective (i.app n) ∧ RingHom.ker (i.app n) = kerIdeal (u.app n) := by
  obtain ⟨h₀, hrank⟩ := @kerIdeal_finrank_eq_pow_of_idempotent p _ k _ G u v huv h1 h2
  obtain ⟨K, i, hi⟩ := @KerGrp.exists_kernel p _ k _ G u h₀ hrank
  obtain ⟨hfac, hcan⟩ := factor_closedImmersion p k K G i (fun n => (hi n).1)
  have hvu : v + u = 𝟙 G := by rw [add_comm]; exact huv
  have hker : ∀ n, RingHom.ker (i.app n) = RingHom.ker (v.app n) := fun n => by
    rw [(hi n).2, ker_app_eq_kerIdeal_of_idempotents p k G v u hvu h2 h1 n]
  obtain ⟨q, hq⟩ := hfac G v (fun n => (hker n).le)
  have hiu : i ≫ u = 0 := by
    refine hom_ext fun n => BialgHom.ext fun b => ?_
    have h := (kerIdeal_le_ker_iff (u.app n) (i.app n : G.A n →ₐ[k] K.A n)).1 (hi n).2.ge b
    change i.app n (u.app n b) = (1 : WithConv (G.A n →ₐc[k] K.A n)).ofConv b
    refine Eq.trans h ?_
    simp
  have hiv : i ≫ v = i := by
    have e := Preadditive.comp_add _ _ _ i u v
    rw [huv, hiu, zero_add, Category.comp_id] at e
    exact e.symm
  refine ⟨K, i, q, ?_, hq, hi⟩
  apply hcan K
  rw [Category.assoc, hq, hiv, Category.id_comp]

end PDivGroup

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakSectionSmallFirstJetNormalFrameStatement
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.peak_section_small_first_jet_normal_frame : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H G : La) (i : ι) (p : V n) (r0 c Cq K : ℝ) (q : V n → ℂ), 0 < r0 → 0 < c → closedBall p r0 ⊆ (A.chart i).target → Differentiable ℂ q → (∀ v ∈ closedBall p r0, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ Cq * ‖v - p‖ ^ 2) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ D : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) D → DifferentiableOn ℂ (D i ∘ (A.chart i).symm) (ball p r0) → n0 A (G + k • H) D ≤ ENNReal.ofReal (K * Real.exp (-c * k)) → ‖D i ((A.chart i).symm p) * Complex.exp (-(k * q p))‖ ≤ ε ∧ ‖fderiv ℂ (fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v))) p‖ ≤ ε := by
  first | exact @GlobalTheory.JetSmall.main | exact GlobalTheory.JetSmall.main | (intros; apply GlobalTheory.JetSmall.main <;> assumption)
end

