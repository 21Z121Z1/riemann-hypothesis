import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0618
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3468
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3482
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3477
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3486
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorsionNe
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Definitions.Divisors.TorusMemOfSepAtBTate
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3363
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3475
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3348
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3463
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3483
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSymplecticLevelLocus
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.SympLevLocus

theorem range_sub_iff {X : Scheme.{0}} {k : Type} [Field k] (x : Sp k ⟶ X) (W : Set X) (p₀ : Sp k) :
    Set.range x.base ⊆ W ↔ x.base p₀ ∈ W := by
  refine ⟨fun H => H ⟨p₀, rfl⟩, ?_⟩
  rintro H _ ⟨p, rfl⟩
  rwa [Subsingleton.elim p p₀]

open GlobalTheory.SiegelPull in

theorem exists_open_sympLev : ∀ (h M : ℕ) (S' : Scheme.{0}) [IsLocallyNoetherian S'] (t : S' ⟶ Sp (cycAway M)) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (lev : (Fin h ⊕ Fin h → ℤ) → (𝟙_ (Over S') ⟶ G)), IsAbelianScheme G → P.IsLB → (∃ s : (P.pull (lift (1 : G ⟶ G) (𝟙 G)).left).Gen, s.IsGen) → (∃ s : (P.pull (lift (𝟙 G) (1 : G ⟶ G)).left).Gen, s.IsGen) → LBIso P (P.pull (lift (snd G G) (fst G G)).left) → 3 ≤ M → Odd M → (∀ a b, lev (a + b) = lev a * lev b) → (∀ a, lev a ^ M = 1) → ∃ U : S'.Opens, (∀ V : S'.Opens, V ≤ U → IsSympLev (P.pull (Pdiv.PullbackComparison.pφ₂ V.ι G)) h M (zetaAway M) (V.ι ≫ t) (fun a => GlobalTheory.SiegelPull.secPull (Pdiv.PullbackComparison.isGrpPullback V.ι G) (lev a))) ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S') (c' : SiegPre h M (zetaAway M) (g ≫ t)) (φ : c'.A.left ⟶ G.left) (φ₂ : (G2 c'.A).left ⟶ (G2 G).left), IsGrpPullback c'.A G g φ → IsSquare φ φ₂ → LBIso c'.P (P.pull φ₂) → (∀ a, (c'.lev a).left ≫ φ = g ≫ (lev a).left) → Set.range g.base ⊆ (U : Set S') := by
  intro h M S' _ t G _ _ P lev hab hP hr₁ hr₂ hsy hM hodd hadd htor
  let Good : S'.Opens → Prop := fun W => ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S')
    (β : cycAway M →+* k) (z : kˣ), Set.range x.base ⊆ W → x ≫ t = spMap β → (z : k) = β (zetaAway M) →
      SympAt P h M lev k x z
  have hsup : ∀ (k : Type) [Field k] (x : Sp k ⟶ S'), Set.range x.base ⊆ (sSup {W | Good W} : S'.Opens) →
      ∃ W, Good W ∧ Set.range x.base ⊆ W := by
    intro k _ x hx
    let p₀ : Sp k := (⊥ : PrimeSpectrum k)
    rw [range_sub_iff x _ p₀] at hx
    obtain ⟨W, hW, hpW⟩ := TopologicalSpace.Opens.mem_sSup.1 hx
    exact ⟨W, hW, (range_sub_iff x _ p₀).2 hpW⟩
  refine ⟨sSup {W | Good W}, fun V hV => ?_, ?_⟩
  · have pb := Pdiv.PullbackComparison.isGrpPullback V.ι G
    refine (isSympLev_iff _ _ _ _ _ _).2 ⟨fun a b => push_injective pb _ ?_, fun a => push_injective pb _ ?_,
      fun k _ _ x β z hx hz => ?_⟩
    · rw [map_mul, push_secPull', push_secPull', push_secPull', hadd, MonObj.comp_mul]
    · rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, htor, MonObj.comp_one]
    · rw [sympAt_pullback_iff V.ι hP (pull_isLB hP _) pb (Pdiv.PullbackComparison.isSquare V.ι G)
        (Pdiv.PullbackComparison.gen_refl _ (pull_isLB hP _)) (fun a => secPull_left pb _)]
      obtain ⟨W, hW, hxW⟩ := hsup k (x ≫ V.ι) (by
        rintro _ ⟨p, rfl⟩
        exact hV (by first | exact (x.base p).2 | simp | (rw [← Scheme.Opens.range_ι V]; exact ⟨_, rfl⟩)))
      exact hW k (x ≫ V.ι) β z hxW (by rw [Category.assoc]; exact hx) hz
  · intro T g c' φ φ₂ pb sq iso hl
    rintro _ ⟨τ, rfl⟩
    obtain ⟨K, _, _, x₀, ⟨q, hq⟩⟩ := GlobalTheory.SiegelTypings.exists_geomPt τ
    obtain ⟨β, hβ⟩ := (⟨(Spec.preimage (x₀ ≫ g ≫ t)).hom, by simp [spMap]⟩ : ∃ β : cycAway M →+* K, spMap β = x₀ ≫ g ≫ t)
    let z : Kˣ := ((GlobalTheory.LowChart.isUnit_zetaAway M hM).map β).unit
    have hc : SympAt c'.P h M c'.lev K x₀ z := c'.geom K x₀ β z hβ.symm rfl
    obtain ⟨hS₁, hS₂, hS₃⟩ := (sympAt_pullback_iff g hP c'.isLB pb sq iso hl K x₀ z).1 hc
    have e₁ := GlobalTheory.T.level_sections_exact_kernel_locus_open S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₂ := GlobalTheory.T.exists_open_locus_torsion_points_are_level_sections S' M t G h lev hab hM hadd htor K (x₀ ≫ g)
    have e₃ := GlobalTheory.T.symmetric_bundle_level_odd S' M t G P h lev hab hP hr₁ hr₂ hsy hM hodd hadd htor K (x₀ ≫ g) β z (by rw [Category.assoc, hβ]) rfl
    obtain ⟨W₁, hW₁, H₁⟩ := e₁ hS₁
    obtain ⟨W₂, hW₂, H₂⟩ := e₂ hS₂
    obtain ⟨W₃, hW₃, H₃⟩ := e₃ hS₃
    have hgood : Good (W₁ ⊓ W₂ ⊓ W₃) := fun k _ _ x β' z' hx hxt hz' =>
      ⟨H₁ k x (hx.trans (le_trans inf_le_left inf_le_left)), H₂ k x (hx.trans (le_trans inf_le_left inf_le_right)),
        H₃ k x β' z' (hx.trans inf_le_right) hxt hz'⟩
    have hmem : g.base τ ∈ (W₁ ⊓ W₂ ⊓ W₃ : S'.Opens) := by
      have e : (x₀ ≫ g).base q = g.base τ := by first | simp [← hq] | (rw [Scheme.Hom.comp_apply, hq]) | (rw [Scheme.comp_base_apply, hq])
      rw [← e]
      exact ⟨⟨hW₁ ⟨q, rfl⟩, hW₂ ⟨q, rfl⟩⟩, hW₃ ⟨q, rfl⟩⟩
    exact (le_sSup (show W₁ ⊓ W₂ ⊓ W₃ ∈ {W | Good W} from hgood)) hmem

end GlobalTheory.SympLevLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFrameSqOfTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
noncomputable section

namespace GlobalTheory.USep

open GlobalTheory.TorsFrame

theorem isTorsFrame_sq : ∀ (S : Scheme.{0}) (P : PolAV S) (rig : LB.Gen (P.L.pull (eSec P.A))) (n : ℕ) (T : Over S)
    (x : T ⟶ P.A) (τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => x.left) (fun _ => 1))),
    IsTorsFrame P rig n x τ → IsTorsFrame P rig (n ^ 2) x τ := by
  intro S P rig n T x τ ⟨hx, hτ, α, hα, hN, hC⟩
  have hL := P.isLB
  have eN : (mulA P.A n).left ≫ (mulA P.A n).left = (mulA P.A (n ^ 2)).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, ← pow_mul, ← sq]
  have ex : x.left ≫ (mulA P.A n).left = T.hom ≫ eSec P.A := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx, one_left]
  obtain ⟨α', hα', vα'⟩ := exists_gen hL (φ' := ![𝟙 P.A.left, (mulA P.A (n ^ 2)).left])
    (ε' := ![((n ^ 2 : ℕ) : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Category.comp_id, eN]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module)
    (LB.mulGen P.L _ _ _ _ (LB.pullGen P.L _ _ α (mulA P.A n).left) (GeneratorPullback.powGen P.L _ _ α (n ^ 2)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (DVR.powGen_isGen _ _ _ _ hα _))
  have vα₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (J), Good P.L z J →
      val α' r z J = val α (r ≫ (mulA P.A n).left) z J * val α r z J ^ (n ^ 2) := fun Z r z J hJ => by
    rw [vα' _ _ z J hJ, val_mul hJ, val_pull hJ, val_powGen]
  refine ⟨by rw [sq, pow_mul, hx, one_pow], hτ, α', hα', corr_of_val hL fun z J hJ => ?_,
    corr_of_val hL fun z J hJ => ?_⟩
  · have h0 := val_corr hJ hN (𝟙 (𝟙_ (Over S)).left)
    rw [val_pull hJ, val_mul hJ, val_inv] at h0 ⊢
    rw [vα₂ _ _ z J hJ, Category.assoc, eSec_mulA, h0]
    have hp : ∀ k : ℤ, val (rigPow P.A P.L rig k) (𝟙 (𝟙_ (Over S)).left) z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig (𝟙 (𝟙_ (Over S)).left) z J ^ k := fun k => map_zpow _ _ _
    rw [hp, hp]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    push_cast
    module
  · have h1 := val_corr hJ hC (𝟙 T.left)
    have h2 := val_corr hJ hN T.hom
    have hp : ∀ k : ℤ, val (rigPow P.A P.L rig k) T.hom z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig T.hom z J ^ k := fun k => map_zpow _ _ _
    have hf : ∀ k : ℤ, val (powFrame P.A P.L x τ k) (𝟙 T.left) z J = val τ (𝟙 T.left) z J ^ k :=
      fun k => map_zpow _ _ _
    rw [val_pull hJ, val_mul hJ, val_inv, hp] at h2
    rw [hf, val_mul hJ, val_pull hJ, val_rigT rig _ z hJ] at h1
    simp only [Category.id_comp] at h1
    rw [hf, val_mul hJ, val_pull hJ, val_rigT rig _ z hJ]
    simp only [Category.id_comp]
    rw [vα₂ _ _ z J hJ, ex, h2]
    have ha : val α x.left z J = val τ (𝟙 T.left) z J ^ ((n : ℤ) ^ 2) *
        (val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) rig T.hom z J)⁻¹ := by
      rw [h1, mul_inv_cancel_right]
    rw [ha]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
    push_cast
    module

end GlobalTheory.USep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitCoefficientOfThetaSquareIntegralTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

set_option maxHeartbeats 400000 in

theorem GlobalTheory.Poinc.Sep.CoefInt.isUnit_of_theta_sq : ∀ (N₁ : ℕ), 2 ≤ N₁ → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ →
    (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) → ∀ (D : DegPre V₁)
    (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))),
    (∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ') →
    ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V₁)) ⟶ D.P.A)),
    (∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Sp V₁) (p : Over.mk x ⟶ D.P.A), p ^ N₁ = 1 →
      ∃ c, p = toUnit _ ≫ b c) →
    ∃ c₁ : C, ∀ (G : V₁) (U : ∀ (Z : Scheme.{0}) (_ : Z ⟶ Sp V₁) (z : Z) (_ : (Z ⟶ D.P.A.left) → D.P.L.ι),
        (Z.presheaf.stalk z)ˣ),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V₁) (z : Z) J, Good D.P.L z J →
        gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) =
          sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ (b c₁).left) z J ^ 2 *
            (U Z r z J).val) → IsUnit G := by
  intro N₁ hN V₁ _ _ _ hV hunit D θ hθ C b hcov
  let K := AlgebraicClosure (ResidueField V₁)
  let ev : V₁ →+* K := (algebraMap (ResidueField V₁) K).comp (residue V₁)
  have hθ' : ∃ j, (ThetaOne.pullTo D ev θ).f j ≠ 0 :=
    ThetaOne.exists_ne_zero D ev _ (hθ K ev _ (ThetaOne.isPullSecLC_pullTo D ev θ))
  have hNK : (N₁ : K) ≠ 0 := by
    have := (hunit N₁ (by omega)).map ev
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨p, hp, hne⟩ := GlobalTheory.Poinc.Sep.Coef.exists_torsion_ne D ev θ hθ' N₁ hN hNK
  obtain ⟨c₁, hc⟩ := hcov K (spMap ev) p hp
  refine ⟨c₁, fun G U hG => ?_⟩
  by_contra hGu
  have hG0 : ev G = 0 := by
    show algebraMap (ResidueField V₁) K (residue V₁ G) = 0
    rw [(residue_eq_zero_iff G).2 ((mem_maximalIdeal G).2 hGu), map_zero]
  let z : Sp K := IsLocalRing.closedPoint K
  have hch : ∀ ψ : Sp K ⟶ D.P.A.left, ∃ i, ψ z ∈ D.P.L.U i := fun ψ =>
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart D.P.isLB (ψ z)
  choose J hJ using hch
  have hgood : Good D.P.L z J := hJ
  have e := hG (Sp K) (spMap ev) z J hgood
  have e2 : gs (spMap ev) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) = toStk z (ev G) := by
    have := GlobalTheory.Poinc.Sep.Coef.gs_ev ev ((Scheme.ΓSpecIso (CommRingCat.of V₁)).inv.hom G) z
    simpa using this
  have hpl : p.left = spMap ev ≫ (b c₁).left := by rw [hc]; rfl
  have h1 := hne z J hgood
  rw [hpl] at h1
  obtain ⟨y, hy⟩ := GlobalTheory.Poinc.Sep.Coef.toStk_surj z (sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (spMap ev ≫ (b c₁).left) z J)
  rw [e2, hG0, map_zero, ← hy, ← map_pow] at e
  have h3 : toStk z (y ^ 2) = 0 := (Units.mul_left_eq_zero _).1 e.symm
  have h4 : y ^ 2 = 0 := (toStk z).injective (h3.trans (map_zero _).symm)
  exact h1 (by rw [← hy, pow_eq_zero_iff two_ne_zero |>.1 h4, map_zero])
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitTauScaledGeneratorTorusMonomial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.ScaleTorus

theorem unitOn_mul' {R : Type} [CommRing R] (x y : Rˣ) : unitOn (x * y) = unitOn x * unitOn y := by
  apply Units.ext
  exact map_mul (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (x : R) (y : R)

theorem isUnitTau_scaleGen : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
    (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R]
    (C : MonoFam Xo c φ R) (N : ℕ) (s : Fin C.m ⊕ Fin N → R)
    (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre),
    (∀ i, s (.inl i) = C.s i) → (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) →
    TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
      (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) →
    ∀ (u : Fin N → Rˣ), (∀ k, (u k : R) = s (.inr k)) → ∀ a b,
      GlobalTheory.RigChart.IsUnitTau C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) a b
        (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen
          (unitOn (∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b))) (τ₀ a b)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ C N s ε τ₀ hs hε hτ u hu a b
  obtain ⟨hgen, k, hk, hval⟩ := hτ a b
  set w : Rˣ := ∏ k, u k ^ ((l.M' : ℤ) * (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X) a b) with hw
  let w' : (FractionRing R)ˣ := Units.map (algebraMap R (FractionRing R)).toMonoidHom w
  have hw' : (w' : FractionRing R) = ∏ k, algebraMap R (FractionRing R) (s (.inr k)) ^
      ((l.M' : ℤ) • (ε (.inr k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b := by
    simp only [w', hw, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.coe_map,
      LinearMap.smul_apply, smul_eq_mul, ← hu]
    rfl
  refine ⟨ReciprocityTheory.ChartRestriction.G.DVR.scaleGen_isGen _ _ hgen, k * w'⁻¹, ?_, fun zz J hJ => ?_⟩
  · rw [Units.val_mul, Units.val_inv_eq_inv_val, mul_inv_eq_iff_eq_mul₀ w'.ne_zero, hk, hw']
    refine (finSumFinEquiv.symm.prod_comp fun k => algebraMap R (FractionRing R) (s k) ^
      ((l.M' : ℤ) • (ε k : LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b).trans ?_
    rw [Fintype.prod_sum_type]
    simp only [hs, hε]
  · have e₁ : val (ReciprocityTheory.ChartRestriction.G.DVR.scaleGen (unitOn w) (τ₀ a b)) (toUnit (TK R)).left zz J =
        gm (toUnit (TK R)).left zz ⊤ (unitOn w) * val (τ₀ a b) (toUnit (TK R)).left zz J :=
      (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ zz le_top (hJ.mem _ _) _) rfl)
    have e₂ : gm (toUnit (TK R)).left zz ⊤ (unitOn w) = gm (𝟙 (TK R).left) zz ⊤ (unitOn w') := by
      have e : (toUnit (TK R)).left = spMap (algebraMap R (FractionRing R)) := by simp
      rw [e]
      exact SepBModel.gm_spMap _ zz w
    have e₃ : gm (𝟙 (TK R).left) zz ⊤ (unitOn k) =
        gm (𝟙 (TK R).left) zz ⊤ (unitOn (k * w'⁻¹)) * gm (𝟙 (TK R).left) zz ⊤ (unitOn w') := by
      refine Eq.trans ?_ (map_mul _ _ _)
      refine congrArg _ (Eq.trans ?_ (unitOn_mul' _ _))
      rw [inv_mul_cancel_right]
    refine (hval zz J hJ).trans (Eq.trans ?_ (congrArg _ e₁.symm))
    rw [e₂, ← _root_.mul_assoc, ← e₃]

end GlobalTheory.UCanon.ScaleTorus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricShiftOfIsometric
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CovTest.GeoSwap

open HermLB

section Shift

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k}

theorem isometric_pull_shift (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ)
    (π : Y ⟶ X) (hπ : π ≫ p = q) : ((L.shift t ht).pull π hπ).Isometric ((L.pull π hπ).shift t ht) :=
  isometric_of_eqOn fun σ a y _ => by
    exact (congrArg (· + 2 * t σ) (Weight.pull_φ (L.φ σ) π hπ a y)).trans
      (Weight.pull_φ ((L.φ σ).addFn fun _ => 2 * t σ) π hπ a y).symm

theorem isometric_shift_of_isometric {L M : HermLB p} (h : L.Isometric M) (t : (k →+* ℂ) → ℝ)
    (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) : (L.shift t ht).Isometric (M.shift t ht) := by
  obtain ⟨w, hw, h⟩ := h
  refine ⟨w, hw, fun σ a b y ha hb => ?_⟩
  have e := h σ a b y ha hb
  exact (congrArg (· + 2 * t σ) e).trans (add_right_comm _ _ _)

theorem isometric_tens_shift_left (L M : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) :
    ((L.shift t ht).tens M).Isometric ((L.tens M).shift t ht) :=
  isometric_of_eqOn fun σ a y _ => by
    show ((L.φ σ).φ a.1 y + (M.φ σ).φ a.2 y) + 2 * t σ = ((L.φ σ).φ a.1 y + 2 * t σ) + (M.φ σ).φ a.2 y
    ring

variable (p) in

def constB (t : ℝ) : HermLB p := (triv p).shift (fun _ => t) fun _ => rfl

theorem icls_shift_const (L : HermLB p) (t : ℝ) :
    (L.shift (fun _ => t) fun _ => rfl).icls = L.icls + (constB p t).icls := by
  rw [add_comm, constB, ← icls_tens, icls_eq_iff]
  exact (isometric_shift_of_isometric (isometric_triv_tens L).symm _ _).trans
    (isometric_tens_shift_left _ _ _ _).symm

theorem icls_constB_add (s t : ℝ) : (constB p (s + t)).icls = (constB p s).icls + (constB p t).icls := by
  rw [← icls_shift_const, icls_eq_iff]
  exact isometric_of_eqOn fun σ a y _ => by
    show ((0 : ℝ) + 2 * s) + 2 * t = (0 : ℝ) + 2 * (s + t)
    ring

variable (p) in

def constHom : ℝ →+ IsomClass p := AddMonoidHom.mk' (fun t => (constB p t).icls) icls_constB_add

theorem gdeg_shift_const (L : HermLB p) (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) (D : ℕ) :
    gdeg (L.shift t ht) D = gdeg L D := by
  simp only [gdeg, chInt, HermLB.shift, Weight.chernInt, Weight.chernPart_addFn_const]

theorem isometric_comb_three_shift (S Q A A' : HermLB p)
    (hA : A'.Isometric (A.shift (fun _ => 1) fun _ => rfl)) (m : Fin 3 → ℤ) (c : ℝ) (hc : ((m 2 : ℤ) : ℝ) = c) :
    (comb ![S, Q, A'] m).Isometric ((comb ![S, Q, A] m).shift (fun _ => c) fun _ => rfl) := by
  subst hc
  refine icls_eq_iff.1 ?_
  rw [icls_shift_const, icls_comb, icls_comb, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
  rw [icls_eq_iff.2 hA, icls_shift_const]
  have e : (constB p ((m 2 : ℤ) : ℝ)).icls = m 2 • (constB p 1).icls := by
    have := map_zsmul (constHom p) (m 2) 1
    simpa [constHom] using this
  rw [e, smul_add]
  abel

end Shift

theorem rename_lin_swap {κ : Type} [Fintype κ] [DecidableEq κ] (x y : κ) (c : κ → ℝ) :
    rename (Equiv.swap x y) (lin c) = lin fun z => c (Equiv.swap x y z) := by
  simp only [lin, map_sum, map_mul, rename_C, rename_X]
  exact Fintype.sum_equiv (Equiv.swap x y) _ _ fun z => by simp [Equiv.swap_apply_self]

theorem cast_triple (u v : ℤ) : (fun j => (((![u, v, 1] : Fin 3 → ℤ) j : ℤ) : ℝ)) = ![(u : ℝ), v, 1] := by
  funext j
  fin_cases j <;> simp

theorem geo_swap : ArCalc → RegularAlteration → ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d D : ℕ), IsArithVar q d → IsArithVar p D → ∀ (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (h : ∀ a, VMetric q (E a) (r a)) (H : ∀ a, (h a).IsCInf) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), IsFlagBundle π E r fl → ∀ Ψ : MvPolynomial (Σ a, Fin (r a)) ℝ →ₗ[ℝ] ℝ, IsGeoFun (fun z : Σ a, Fin (r a) => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w)) D Ψ → ∀ (a : ι) (i i' : Fin (r a)), (i' : ℕ) = i + 1 → ∀ P : MvPolynomial (Σ a, Fin (r a)) ℝ, Ψ (rename (Equiv.swap (⟨a, i⟩ : Σ a, Fin (r a)) ⟨a, i'⟩) P) = -Ψ P := by
  intro hC hR k _ B Y _ _ q p d D hq hp π w ι _ E r h H fl hfl Ψ hΨ a i i' hi
  obtain ⟨G, -, hS⟩ := GlobalTheory.CovTest.homog_swap_exists_of_ar_calc hC hR
  obtain ⟨Y₁, q₁, d₁, ρ, wρ, E₁, h₁, H₁, fl₁, M, rfl, hY₁, hfl₁, hS0, hS1, hM⟩ :=
    GlobalTheory.SwapBundle.swapFl_bundle k B Y q p d D hq hp π w ι E r h H fl hfl a i i' hi
  haveI := hY₁.isIntegral
  set x : Σ a, Fin (r a) := ⟨a, i⟩ with hx
  set y : Σ a, Fin (r a) := ⟨a, i'⟩ with hy
  have hxy : x ≠ y := by
    intro e
    rw [hx, hy, Sigma.mk.inj_iff] at e
    have := congrArg Fin.val (eq_of_heq e.2)
    omega
  set L : (Σ a, Fin (r a)) → HermLB p := fun z => VMetric.grLB (fl z.1) z.2 ((H z.1).pull π w) with hL
  have key : ∀ n : (Σ a, Fin (r a)) → ℤ,
      Ψ (lin (fun z => (n z : ℝ)) ^ (d₁ + 1)) + Ψ (lin (fun z => (n (Equiv.swap x y z) : ℝ)) ^ (d₁ + 1)) = 0 := by
    intro n
    set n' : (Σ a, Fin (r a)) → ℤ := fun z => if z = x ∨ z = y then 0 else n z with hn'
    set A₀ : HermLB q₁ := comb M n' with hA₀
    set A₁ : HermLB q₁ := A₀.shift (fun _ => 1) fun _ => rfl with hA₁
    set S := VMetric.grLB fl₁ 0 (H₁.pull ρ wρ) with hSd
    set Q := VMetric.grLB fl₁ 1 (H₁.pull ρ wρ) with hQd
    set Mf : Fin 3 → HermLB p := ![S, Q, A₀.pull ρ wρ] with hMf
    set Mf' : Fin 3 → HermLB p := ![S, Q, A₁.pull ρ wρ] with hMf'
    set Am : Fin 3 → (Σ a, Fin (r a)) → ℤ := ![Pi.single x 1, Pi.single y 1, n'] with hAm
    have hiso : ∀ j, (comb L (Am j)).Isometric (Mf j) := by
      intro j
      fin_cases j
      · exact (isometric_comb_single L x).trans hS0.symm
      · exact (isometric_comb_single L y).trans hS1.symm
      · exact SwapFlProof.comb_isometric_pullback L M ρ wρ n' (fun z => z = x ∨ z = y) (fun z hz => if_pos hz)
          (fun z hz => hM z (fun e => hz (Or.inl e)) (fun e => hz (Or.inr e)))
    set f : Fin 3 → MvPolynomial (Σ a, Fin (r a)) ℝ := fun j => lin fun z => (Am j z : ℝ) with hf
    set Ψ₃ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ := Ψ ∘ₗ (aeval f : MvPolynomial (Fin 3) ℝ →ₐ[ℝ] _).toLinearMap with hΨ₃
    have hΨ' : IsGeoFun Mf (d₁ + 1) Ψ₃ := by
      refine ⟨fun m => ?_, fun P e he hP => ?_⟩
      · rw [hΨ₃, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, hf, aeval_lin]
        have h2 := hΨ.1 (fun z => ∑ j, m j * Am j z)
        simp only [Int.cast_sum, Int.cast_mul] at h2
        rw [h2]
        exact ((isometric_comb_comb L Am m).trans (isometric_comb_congr hiso m)).gdeg_eq _
      · rw [hΨ₃, LinearMap.comp_apply, AlgHom.toLinearMap_apply]
        exact hΨ.2 _ e he (by simpa using hP.aeval _ fun j => isHomogeneous_lin _)
    have hA' : (A₁.pull ρ wρ).Isometric ((A₀.pull ρ wρ).shift (fun _ => 1) fun _ => rfl) :=
      isometric_pull_shift A₀ _ _ ρ wρ
    have hcomb : ∀ (m : Fin 3 → ℤ) (c : ℝ), ((m 2 : ℤ) : ℝ) = c →
        (comb Mf' m).Isometric ((comb Mf m).shift (fun _ => c) fun _ => rfl) :=
      fun m c hc => isometric_comb_three_shift S Q _ _ hA' m c hc
    have hΨ'' : IsGeoFun Mf' (d₁ + 1) Ψ₃ :=
      ⟨fun m => (hΨ'.1 m).trans (((hcomb m _ rfl).gdeg_eq _).trans (gdeg_shift_const _ _ _ _)).symm, hΨ'.2⟩
    obtain ⟨Φ, hΦ⟩ := ((hC.arExists k Y p (d₁ + 1) hp).2 (Fin 3) Mf).1
    obtain ⟨Φ', hΦ'⟩ := ((hC.arExists k Y p (d₁ + 1) hp).2 (Fin 3) Mf').1
    have e1 := hS k Y₁ Y q₁ p d₁ hY₁ hp ρ wρ E₁ h₁ H₁ fl₁ hfl₁ A₀ Φ Ψ₃ hΦ hΨ' (n x) (n y)
    have e2 := hS k Y₁ Y q₁ p d₁ hY₁ hp ρ wρ E₁ h₁ H₁ fl₁ hfl₁ A₁ Φ' Ψ₃ hΦ' hΨ'' (n x) (n y)
    have hsh : ∀ u v : ℤ, Φ' (lin ![(u : ℝ), v, 1] ^ (d₁ + 2)) =
        Φ (lin ![(u : ℝ), v, 1] ^ (d₁ + 2)) + (((d₁ + 1 : ℕ) : ℝ) + 1) * 1 * Ψ₃ (lin ![(u : ℝ), v, 1] ^ (d₁ + 1)) := by
      intro u v
      have h1 := hΦ.1 ![u, v, 1]
      have h2 := hΦ'.1 ![u, v, 1]
      rw [cast_triple] at h1 h2
      have h3 := hC.arShift k Y p (d₁ + 1) hp (comb Mf ![u, v, 1]) _ 1 h1
      have h4 := (hcomb ![u, v, 1] 1 (by simp)).symm.isSelfInter hp h3
      rw [h2.unique hp h4, ← cast_triple u v, hΨ'.1 ![u, v, 1]]
    rw [hsh, hsh] at e2
    have e3 : (((d₁ + 1 : ℕ) : ℝ) + 1) * (Ψ₃ (lin ![(n x : ℝ), n y, 1] ^ (d₁ + 1)) +
        Ψ₃ (lin ![(n y : ℝ), n x, 1] ^ (d₁ + 1))) = 0 := by linarith
    have hpos : (((d₁ + 1 : ℕ) : ℝ) + 1) ≠ 0 := by positivity
    have e4 := (mul_eq_zero.1 e3).resolve_left hpos
    have hx0 : n' x = 0 := if_pos (Or.inl rfl)
    have hy0 : n' y = 0 := if_pos (Or.inr rfl)
    have hne : ∀ z, z ≠ x → z ≠ y → n' z = n z := fun z h1 h2 => if_neg (by tauto)
    simp only [hΨ₃, LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, hf, aeval_lin] at e4
    rw [hAm, SwapFlProof.lin_update_two_coords x y hxy n n' hx0 hy0 hne (n x) (n y),
      SwapFlProof.lin_update_two_coords x y hxy n n' hx0 hy0 hne (n y) (n x)] at e4
    convert e4 using 4
    · congr 1
      funext z
      rw [Function.update_eq_self, Function.update_eq_self]
    · congr 1
      funext z
      by_cases h1 : z = x
      · subst h1; simp [Function.update_apply, hxy, Equiv.swap_apply_left]
      · by_cases h2 : z = y
        · subst h2; simp [Function.update_apply, Equiv.swap_apply_right]
        · simp [Function.update_apply, h1, h2, Equiv.swap_apply_of_ne_of_ne h1 h2]
  have hz := GlobalTheory.ArInt.Model.eq_zero_of_pow (d₁ + 1)
    (Ψ + Ψ ∘ₗ (rename (Equiv.swap x y) : MvPolynomial (Σ a, Fin (r a)) ℝ →ₐ[ℝ] _).toLinearMap)
    (fun n => by
      rw [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
        map_pow (rename (Equiv.swap x y)), rename_lin_swap]
      exact key n)
    (fun P e he hP => by
      rw [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, hΨ.2 P e he hP,
        hΨ.2 _ e he (hP.rename_isHomogeneous), add_zero])
  intro P
  have := LinearMap.congr_fun hz P
  rw [LinearMap.add_apply, LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.zero_apply] at this
  linarith

end GlobalTheory.CovTest.GeoSwap

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelKilledOverOpenOfLocalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelKilledOverOpen_of_local : ∀ (d : ℕ) (S' : Scheme.{0}) (G : Over S') [GrpObj G] [IsCommMonObj G] (P : LB (G2 G).left) (W : S'.Opens), (∀ p ∈ W, ∃ V : S'.Opens, p ∈ V ∧ GlobalTheory.KerKilledLocus.KerKilledOn d G P V) → GlobalTheory.KerKilledLocus.KerKilledOn d G P W := by
  first | (exact @GlobalTheory.KerKilledLocal.kerKilledOn_of_local) | (exact GlobalTheory.KerKilledLocal.kerKilledOn_of_local) | (intros; apply GlobalTheory.KerKilledLocal.kerKilledOn_of_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightRecursiveValueWellDefinedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedHeightRecursiveValue_well_defined : ArchInteg → ArchRecip → ∀ m : ℕ, (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∃ T, IsMix q m T) → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k), IsAmb p → ∀ T, IsMix p m T → ∀ (x : X), HasDim x (m + 1) → ∀ (M : HermLB p) (L : Fin m → HermLB p), ∃ v : ℝ, ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q), i (genericPoint Y) = x → ∀ (M' : HermLB q) (L' : Fin m → HermLB q), (M.pull i hi).Isometric M' → (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ (r : M'.B.ι → Y.functionFieldˣ) (hr : IsRatSec M'.B r), v = recVal (fun z => T m L (i z)) L' M' hr := by
  first | exact @GlobalTheory.MixHt.StepVal.step_val | exact GlobalTheory.MixHt.StepVal.step_val | (intros; apply GlobalTheory.MixHt.StepVal.step_val <;> assumption)
end

