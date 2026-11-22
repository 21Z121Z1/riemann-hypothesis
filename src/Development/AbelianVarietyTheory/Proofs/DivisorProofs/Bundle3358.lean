import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2651
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1545
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2817
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2665
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3352
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEffCartierCompl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosed
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3349
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0034

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapIdentityFromRegularBase
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

namespace GlobalTheory.CovTest.Reduce
open Limits

variable {k : Type} [CommRing k]

theorem isIsometry_pullbackCongr {X Y : Scheme.{0}} {q : Y ⟶ Sp k} {t : X ⟶ Sp k} {E : Y.Modules} {r : ℕ}
    (h : VMetric q E r) {f f' : X ⟶ Y} (e : f = f') (hf : f ≫ q = t) (hf' : f' ≫ q = t) :
    (h.pull f hf).IsIsometry (h.pull f' hf') ((Scheme.Modules.pullbackCongr e).app E) := by
  subst e
  intro σ V s s' y hy
  rfl

theorem isIsometry_bcIso {B Y B' : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
    (g : B' ⟶ B) {E : B.Modules} {r : ℕ} (h : VMetric q E r)
    (w' : pullback.snd π g ≫ g ≫ q = pullback.fst π g ≫ p) :
    ((h.pull π w).pull (pullback.fst π g) rfl).IsIsometry ((h.pull g rfl).pull (pullback.snd π g) w')
      (bcIso π g E) := by
  obtain ⟨-, hc⟩ := VMetric.isIsometry_pull_id_comp k B q E r h
  have e₁ : (pullback.fst π g ≫ π) ≫ q = pullback.fst π g ≫ p := by rw [Category.assoc, w]
  have e₂ : (pullback.snd π g ≫ g) ≫ q = pullback.fst π g ≫ p := by rw [Category.assoc, w']
  exact IsometryPullback.isIsometry_trans (hc Y _ p _ π (pullback.fst π g) w rfl e₁)
    (IsometryPullback.isIsometry_trans (isIsometry_pullbackCongr h pullback.condition e₁ e₂)
      (IsometryPullback.isIsometry_symm (hc B' _ (g ≫ q) _ g (pullback.snd π g) rfl w' e₂)))

theorem isometric_grLB_bcFlag {B Y B' : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
    (g : B' ⟶ B) {E : B.Modules} {r : ℕ} {h : VMetric q E r} (H : h.IsCInf)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) r)
    (w' : pullback.snd π g ≫ g ≫ q = pullback.fst π g ≫ p) (i : Fin r) :
    (VMetric.grLB (bcFlag π g fl) i ((H.pull g rfl).pull (pullback.snd π g) w')).Isometric
      ((VMetric.grLB fl i (H.pull π w)).pull (pullback.fst π g) rfl) := by
  rw [bcFlag, VMetric.grLB_ofIso (isIsometry_bcIso π w g h w') ((H.pull π w).pull _ rfl)]
  exact VMetric.isometric_grLB_pull k Y _ p _ _ r (h.pull π w) (H.pull π w) fl (pullback.fst π g) rfl i

end GlobalTheory.CovTest.Reduce

namespace GlobalTheory.CovTest.Reduce
open Limits

theorem swap_of_section (hA : ArCalc) (hG : GdegPull) {G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ} (hS : SwapReg G)
    (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hp : IsArithVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2)
    (hfl : IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl))
    (A : HermLB q) (Φ Ψ : MvPolynomial (Fin 3) ℝ →ₗ[ℝ] ℝ)
    (hΦ : IsArFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Φ)
    (hΨ : IsGeoFun ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] (d + 1) Ψ)
    (a b : ℤ) (B' : Scheme.{0}) [IsIntegral B'] (g : B' ⟶ B) (s : B' ⟶ Y) (hs : s ≫ π = g)
    (hgq : IsArithVar (g ≫ q) d) (hreg : ∀ b : B', IsRegularLocalRing (B'.presheaf.stalk b))
    [IsIntegral (pullback π g : Scheme.{0})] (hY' : IsArithVar (pullback.fst π g ≫ p) (d + 1))
    (hfg : pullback.fst π g (genericPoint (pullback π g : Scheme.{0})) = genericPoint Y)
    (hfd : (pullback.fst π g).residueDegree (genericPoint (pullback π g : Scheme.{0})) ≠ 0) :
    Φ (lin ![(a : ℝ), b, 1] ^ (d + 2)) + Φ (lin ![(b : ℝ), a, 1] ^ (d + 2)) = Ψ (G (d + 1) a b) := by
  set ρ := pullback.fst π g
  set π' := pullback.snd π g
  set δ := ρ.residueDegree (genericPoint (pullback π g : Scheme.{0}))
  have w' : π' ≫ g ≫ q = ρ ≫ p := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, w]
  set L : Fin 3 → HermLB p := ![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w]
  set L' : Fin 3 → HermLB (ρ ≫ p) := ![VMetric.grLB (bcFlag π g fl) 0 ((H.pull g rfl).pull π' w'),
    VMetric.grLB (bcFlag π g fl) 1 ((H.pull g rfl).pull π' w'), (A.pull g rfl).pull π' w']
  have iso : ∀ j, ((L j).pull ρ rfl).Isometric (L' j) := by
    intro j
    fin_cases j
    · exact (isometric_grLB_bcFlag π w g H fl w' 0).symm
    · exact (isometric_grLB_bcFlag π w g H fl w' 1).symm
    · have e₁ : (ρ ≫ π) ≫ q = ρ ≫ p := by rw [Category.assoc, w]
      have e₂ : (π' ≫ g) ≫ q = ρ ≫ p := by rw [Category.assoc, w']
      exact (HermLB.isometric_of_refines (HermLB.refines_pull_pull A π w ρ rfl e₁)).trans
        ((HermLB.isometric_pull_of_eq A pullback.condition e₁ e₂).trans
          (HermLB.isometric_of_refines (HermLB.refines_pull_comp A g rfl π' w' e₂)))
  have hΦ' : IsArFun L' (d + 1) ((δ : ℝ) • Φ) :=
    (((hA.arIso) k _ (ρ ≫ p) (d + 1) hY').2 (Fin 3) _ _
      (((hA.arProj) k Y _ p (ρ ≫ p) (d + 1) hp hY' ρ rfl hfg hfd).2 (Fin 3) L Φ hΦ)).2.1 L' iso
  have hΨ' : IsGeoFun L' (d + 1) ((δ : ℝ) • Ψ) := by
    refine ⟨fun n => ?_, fun P e he hP => ?_⟩
    · rw [LinearMap.smul_apply, hΨ.1 n, smul_eq_mul,
        ← hG k Y _ p (ρ ≫ p) (d + 1) hp hY' ρ rfl hfg hfd (comb L n)]
      exact ((isometric_comb_pull L n ρ rfl).symm.trans (isometric_comb_congr iso n)).gdeg_eq _
    · rw [LinearMap.smul_apply, hΨ.2 P e he hP, smul_zero]
  have hflat : Nonempty (Vert.Flag ((Scheme.Modules.pullback g).obj E) 2) :=
    ⟨(fl.pull s).ofIso ((Scheme.Modules.pullbackComp s π).app E ≪≫ (Scheme.Modules.pullbackCongr hs).app E)⟩
  have key := hS k B' _ (g ≫ q) (ρ ≫ p) d hgq hY' hreg π' w' _ (h.pull g rfl) (H.pull g rfl) hflat
    (bcFlag π g fl) (GlobalTheory.T.flag_bundle_pullback_base_change B Y B' π g Unit (fun _ => E) (fun _ => 2) (fun _ => fl) hfl)
    (A.pull g rfl) ((δ : ℝ) • Φ) ((δ : ℝ) • Ψ) hΦ' hΨ' a b
  simp only [LinearMap.smul_apply, smul_eq_mul, ← mul_add] at key
  exact mul_left_cancel₀ (Nat.cast_ne_zero.2 hfd) key

end GlobalTheory.CovTest.Reduce

namespace GlobalTheory.CovTest

open Limits in

theorem swap2_of_swapRegular : ArCalc → RegularAlteration → GdegPull →
    ∀ G : ℕ → ℤ → ℤ → MvPolynomial (Fin 3) ℝ, SwapReg G → Swap2 G := by
  intro hA hR hG G hS k _ B Y _ _ q p d hq hp π w E h H fl hfl A Φ Ψ hΦ hΨ a b
  obtain ⟨Z, _, i, hZ, hZg, hZd⟩ := GlobalTheory.T.rank_two_flag_bundle_section k B Y q p d hq hp π w E h.isVB fl hfl
  obtain ⟨B', _, ρ₀, hB', hreg, hρg, hρd⟩ := GlobalTheory.T.exists_regular_integral_cover_same_dimension hR k Z (i ≫ p) d hZ
  have hgq : IsArithVar ((ρ₀ ≫ i ≫ π) ≫ q) d := by
    rwa [Category.assoc, Category.assoc, w]
  have hgg : (ρ₀ ≫ i ≫ π) (genericPoint B') = genericPoint B := by
    rw [Scheme.Hom.comp_apply, hρg, hZg]
  have hgd : (ρ₀ ≫ i ≫ π).residueDegree (genericPoint B') ≠ 0 := by
    rw [CurveDegreesCompare.residueDegree_comp, hρg]
    exact mul_ne_zero hZd hρd
  obtain ⟨_, hY', hfg, hfd⟩ := GlobalTheory.T.flag_bundle_base_change_arith_variety k B Y B' q p d hq hp π w E h.isVB fl hfl _ hgq hgg hgd
  exact Reduce.swap_of_section hA hG hS k B Y q p d hp π w E h H fl hfl A Φ Ψ hΦ hΨ a b B' _ (ρ₀ ≫ i)
    (Category.assoc _ _ _) hgq hreg hY' hfg hfd

end GlobalTheory.CovTest

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningEqOfGenericSectionRatios
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem fstG_comm_thick (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) (g : G ⟶ G) :
    ((Over.pullback (thick R I e)).map g).left ≫ (fstG I e G).left = (fstG I e G).left ≫ g.left := by
  first
    | (have := congrArg CommaMorphism.left ((Over.mapPullbackAdj (thick R I e)).counit.naturality g)
       simpa [fstG] using this)
    | (simp [fstG]; exact pullback.lift_fst _ _ _)

theorem thick_eq_of_ratios : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ b, FormalEnd U.toUnifPre a h' b → ∀ (N : ℕ) (S : ∀ k : ℕ, H0 U.LG.L k → H0 U.LG.L (N * k)), (∀ (k e : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L ((b e).left ≫ (fstG (maximalIdeal R) e G).left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)) → (∀ k : ℕ, 3 ≤ k → ∃ s₀ : H0 U.LG.L k, SecCoNonzero U.LG.L ((b 0).left ≫ (fstG (maximalIdeal R) 0 G).left) (fstG (maximalIdeal R) 0 G).left s₀ (S k s₀)) → ∀ φ : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G, (∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k), SecRatioEq U.LG.L (φ.left ≫ pullback.fst G.hom (jK R)) (pullback.fst G.hom (jK R)) s₁ s₂ (S k s₁) (S k s₂)) → ∀ g : G ⟶ G, IsMonHom g → (Over.pullback (jK R)).map g = φ → ∀ e, (Over.pullback (thick R (maximalIdeal R) e)).map g = b e := by
  intro R _ _ _ hB D A G _ _ hG U a a' h h' hE b hb N S hS hC φ hφ g hg hgφ e
  have hcomm : φ.left ≫ pullback.fst G.hom (jK R) = pullback.fst G.hom (jK R) ≫ g.left := by
    subst hgφ
    first
      | (simp; done)
      | (simp; exact pullback.lift_fst _ _ _)
      | exact pullback.lift_fst _ _ _
  have hGI : GeometricallyIntegral G.hom := GlobalTheory.geometricallyIntegral_of_isSemiAbelian G (h := hG)
  have hfin : Finite (irreducibleComponents (Sp R)) := by
    rw [irreducibleComponents_eq_singleton]
    infer_instance
  have hfl : Flat G.hom := by
    obtain ⟨_, hsm, -, -, -, -⟩ := hG
    infer_instance
  have hred : IsReduced G.left :=
    GeometricallyReduced.isReduced_of_flat_of_finite_irreducibleComponents G.hom
  have hdom : IsDominant (pullback.fst G.hom (jK R)) :=
    isDominant_genericFibre_of_flat R (FractionRing R) G.hom

  have hGrat : ∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k),
      SecRatioEq U.LG.L g.left (𝟙 G.left) s₁ s₂ (S k s₁) (S k s₂) := by
    intro k s₁ s₂
    apply SecRatioEq.of_isDominant (pullback.fst G.hom (jK R))
    rw [← hcomm, Category.comp_id]
    exact hφ k s₁ s₂

  have hxc : ((Over.pullback (thick R (maximalIdeal R) e)).map g).left ≫ (fstG (maximalIdeal R) e G).left =
      (fstG (maximalIdeal R) e G).left ≫ g.left := fstG_comm_thick R (maximalIdeal R) e G g
  have hxrat : ∀ (k : ℕ) (s₁ s₂ : H0 U.LG.L k),
      SecRatioEq U.LG.L (((Over.pullback (thick R (maximalIdeal R) e)).map g).left ≫ (fstG (maximalIdeal R) e G).left)
        (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂) := by
    intro k s₁ s₂
    have := secRatioEq_comp U.LG.L g.left (𝟙 G.left) (fstG (maximalIdeal R) e G).left s₁ s₂ (S k s₁) (S k s₂)
      (hGrat k s₁ s₂)
    rwa [Category.comp_id, ← hxc] at this
  have hxmon : IsMonHom ((Over.pullback (thick R (maximalIdeal R) e)).map g) := inferInstance
  obtain ⟨k₀, hk₀, hnear⟩ := GlobalTheory.T.uniformisedGroup_morphisms_agree_of_sectionRatios R hB D A G hG U
  obtain ⟨s₀, hs₀⟩ := hC k₀ hk₀

  obtain ⟨y, i'', i', hy1, hy2⟩ :=
    formalEnd_secCoNonzero_lift R hB D A G hG U a h' b hb k₀ (N * k₀) s₀ (S k₀ s₀) hs₀ e
  obtain ⟨i, hy0⟩ := GlobalTheory.T.mem_basicOpen_of_sectionRatioEq_basePoint R hB D A G hG U e k₀ (N * k₀) hk₀
    ((Over.pullback (thick R (maximalIdeal R) e)).map g) (S k₀) (hxrat k₀) y s₀ i' hy2
  obtain ⟨W, hyW, hW⟩ := hnear e k₀ (N * k₀) le_rfl ((Over.pullback (thick R (maximalIdeal R) e)).map g) (b e)
    (S k₀) (hxrat k₀) (fun s₁ s₂ => hS k₀ e s₁ s₂) y s₀ i i' i'' hy0 hy2 hy1
  exact GlobalTheory.T.semiAbelian_thickening_hom_eq_of_eq_on_open R hB D A G hG U e _ (b e) hxmon (hb.1 e) W y hyW hW

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalBoundaryLocalEquation
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BdEquation
open GlobalTheory.Cartier GlobalTheory.ZH GlobalTheory.FlagBundle

theorem dvd_pow_of_vanishing {Y : Scheme.{0}} (O V : Y.Opens) (t : Γ(Y, V))
    (ht : ∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ O) (W : Y.Opens) (hW : W ≤ V) (f : Γ(Y, W))
    (hf : ∀ z (hz : z ∈ W), z ∉ O → ger z hz f ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk z))
    (z : Y) (hz : z ∈ W) : ∃ n : ℕ, ger z (hW hz) t ∣ ger z hz f ^ n := by
  obtain ⟨A, hA, hzA, e⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hz
  have hA' : IsAffineOpen A := hA
  let f' : Γ(Y, A) := Y.presheaf.map (homOfLE e).op f
  let t' : Γ(Y, A) := Y.presheaf.map (homOfLE (e.trans hW)).op t
  have hle : Y.basicOpen f' ≤ Y.basicOpen t' := by
    intro x hx
    have hxA : x ∈ A := Y.basicOpen_le _ hx
    rw [Y.mem_basicOpen _ x hxA] at hx ⊢
    rw [Y.presheaf.germ_res_apply] at hx ⊢
    refine (ht x _).2 ?_
    by_contra hO
    exact hf x (e hxA) hO hx
  have h2 : PrimeSpectrum.basicOpen f' ≤ PrimeSpectrum.basicOpen t' := by
    rw [← hA'.fromSpec_preimage_basicOpen, ← hA'.fromSpec_preimage_basicOpen]
    exact fun x hx => hle hx
  obtain ⟨n, hn⟩ := (PrimeSpectrum.basicOpen_le_basicOpen_iff _ _).1 h2
  have h3 := map_dvd (Y.presheaf.germ A z hzA).hom (Ideal.mem_span_singleton.1 hn)
  rw [map_pow] at h3
  refine ⟨n, ?_⟩
  rw [← Y.presheaf.germ_res_apply (homOfLE (e.trans hW)) z hzA t, ← Y.presheaf.germ_res_apply (homOfLE e) z hzA f]
  exact h3

theorem exists_section {X : Scheme.{0}} [IsIntegral X] (D : CartierDiv X) (hD : D.Eff)
    (hr : ∀ (y : X) (g : X.functionFieldˣ), D.IsEqn y g → ∀ (f : X.functionField) (n : ℕ), RegAt y f →
      RegAt y (f ^ n / g) → RegAt y (f / g)) (y : X) :
    ∃ (V : X.Opens) (_ : y ∈ V) (t : Γ(X, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∉ D.supp) ∧
      ∀ z (hz : z ∈ V) (b : X.presheaf.stalk z) (n : ℕ), ger z hz t ∣ b ^ n → ger z hz t ∣ b := by
  obtain ⟨U, hyU, g, hg⟩ := D.exists_isEqn_nhds y
  obtain ⟨a, ha⟩ := (hg y hyU).regularAt_iff.1 (hD y)
  rw [one_mul] at ha
  obtain ⟨W, hyW, s, rfl⟩ := X.presheaf.germ_exist a
  have inj := fun z : X => IsFractionRing.injective (X.presheaf.stalk z) X.functionField
  have key : ∀ z (hz : z ∈ W ⊓ U), algebraMap _ X.functionField
      (ger z hz (X.presheaf.map (homOfLE inf_le_left).op s)) = g := fun z hz => by
    refine Eq.trans ?_ ((algebraMap_germ hz.1 s).trans ((algebraMap_germ hyW s).symm.trans ha))
    exact congrArg _ (X.presheaf.germ_res_apply (homOfLE inf_le_left) z hz s)
  refine ⟨W ⊓ U, ⟨hyW, hyU⟩, X.presheaf.map (homOfLE inf_le_left).op s, fun z hz => ?_, fun z hz b n hb => ?_⟩
  · rw [(hg z hz.2).mem_supp_iff, not_not]
    refine ⟨fun h => ⟨_, h, key z hz⟩, fun ⟨u, hu, e⟩ => ?_⟩
    rwa [inj z (e.trans (key z hz).symm)] at hu
  · obtain ⟨c, hc⟩ := hb
    obtain ⟨d, hd⟩ := hr z g (hg z hz.2) (algebraMap _ X.functionField b) n ⟨b, rfl⟩ ⟨c, by
      rw [eq_div_iff g.ne_zero, ← map_pow, hc, map_mul, key z hz, mul_comm]⟩
    refine ⟨d, inj z ?_⟩
    rw [map_mul, key z hz, hd, mul_div_cancel₀ _ g.ne_zero]

theorem exists_reduced_equation : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → IsVariety₀ TF.X Z → ∀ y : Y₀ TF.X Z, y ∉ U₀ TF.X Z → ∃ (V : (Y₀ TF.X Z).Opens) (_ : y ∈ V) (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) ∧ (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) := by
  intro _ E _ _ _ H Dw l Xo c T Z hF _ y _
  have hsm := GlobalTheory.VarFlag.smooth_gen T.smooth
  obtain ⟨B, j, hB, hcov⟩ := GlobalTheory.T.exists_varieties_components_smooth_genericFibre E H Dw l Xo c c.F (RingHom.id c.F) T.Y c.F (RingEquiv.refl _) hF hsm
  have := (hB Z).1
  obtain ⟨C, f, hπ, -, hl⟩ :=
    GlobalTheory.FlagBundle.exists_flagCpt T.Y (RingEquiv.refl _) (GlobalTheory.T.snc_toroidalGenericBoundary_of_snc_boundary T.snc) (B Z) (j Z) (hB Z).2.2.1
  obtain ⟨h, hiso, hh, -, -⟩ := GlobalTheory.CompProport.exists_iso T Z B j hB hcov C f hπ hl
  have hmem : ∀ z : Y₀ T.X Z, h z ∉ CartierDiv.supp C.bd ↔ z ∈ U₀ T.X Z := fun z => by
    have e : GlobalTheory.Toroidal.genι T.Y (C.π (h z)) = T.X.π (inc₀ T.X Z z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← hh]
    refine (not_congr (C.bd_supp (h z))).trans (not_not.trans ?_)
    change C.π (h z) ∈ Set.range T.Y.jQ ↔ T.X.π (inc₀ T.X Z z) ∈ Set.range T.Y.j
    refine exists_congr fun x => ?_
    rw [← e, Model.j, Scheme.Hom.comp_apply]
    exact (GlobalTheory.Toroidal.genι T.Y).isOpenEmbedding.injective.eq_iff.symm
  obtain ⟨V, hyV, t, ht, hrad⟩ := exists_section C.bd C.bd_eff C.bd_red (h y)
  have hg : ∀ z (hz : z ∈ h ⁻¹ᵁ V), ger z hz (h.app V t) = (h.stalkMap z).hom (ger (h z) hz t) :=
    fun z hz => (Scheme.Hom.germ_stalkMap_apply h V z hz t).symm
  have hu : ∀ z (hz : z ∈ h ⁻¹ᵁ V), IsUnit (ger z hz (h.app V t)) ↔ z ∈ U₀ T.X Z := fun z hz => by
    rw [hg, isUnit_map_iff]
    exact (ht (h z) hz).trans (hmem z)
  refine ⟨h ⁻¹ᵁ V, hyV, h.app V t, hu, fun W hW s hs z hz => ?_⟩
  obtain ⟨n, c', hc⟩ := dvd_pow_of_vanishing _ _ _ hu W hW s hs z hz
  have hb := GlobalTheory.BoundaryDivisor.stalkMap_bijective h z
  obtain ⟨b, hb'⟩ := hb.2 (ger z hz s)
  obtain ⟨c'', rfl⟩ := hb.2 c'
  rw [hg, ← hb', ← map_pow, ← map_mul] at hc
  rw [hg, ← hb']
  exact map_dvd _ (hrad _ _ b n ⟨c'', hb.1 hc⟩)

end GlobalTheory.BdEquation
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ZConn

theorem preconnectedSpace_of_isLocalRing (Z : Scheme.{0}) [IsLocalRing Γ(Z, ⊤)] : PreconnectedSpace Z := by
  rw [preconnectedSpace_iff_clopen]
  intro s hs
  obtain ⟨e, he, hes⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen Z s hs
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with hu | hu
  · right
    rw [← hes, Z.basicOpen_of_isUnit hu]
    simp
  · left
    have h0 : e = 0 := by
      have : e * (1 - e) = 0 := by rw [mul_sub, _root_.mul_one, he, sub_self]
      exact hu.mul_left_eq_zero.1 this
    rw [← hes, h0, Z.basicOpen_zero]
    simp

theorem exists_complete_flat (R : Type) [CommRing R] [IsNoetherianRing R] (P : PrimeSpectrum R) :
    ∃ (A : Type) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsLocalRing A) (φ : R →+* A),
      IsAdicComplete (maximalIdeal A) A ∧ φ.Flat ∧ (maximalIdeal A).comap φ = P.asIdeal := by
  let L := Localization.AtPrime P.asIdeal
  have fg : (maximalIdeal L).FG := IsNoetherian.noetherian _
  haveI hloc : IsLocalRing (AdicCompletion (maximalIdeal L) L) := AdicCompletion.isLocalRing_of_fg fg
  haveI : IsNoetherianRing (AdicCompletion (maximalIdeal L) L) := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ _
  have hm := AdicCompletion.maximalIdeal_eq_map_of_fg fg
  let ψ := algebraMap L (AdicCompletion (maximalIdeal L) L)
  haveI : IsLocalHom ψ := ((IsLocalRing.local_hom_TFAE ψ).out 0 2).mpr hm.symm.le
  refine ⟨AdicCompletion (maximalIdeal L) L, inferInstance, inferInstance, hloc, ψ.comp (algebraMap R L), ?_, ?_, ?_⟩
  · rw [hm]; exact AdicCompletion.isAdicComplete_self _ fg
  · exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance)
      (RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _))
  · rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap ψ]
    exact Localization.AtPrime.comap_maximalIdeal

theorem isPreconnected_fibre : ∀ (X Y : Scheme.{0}) (a : X ⟶ Y), IsLocallyNoetherian Y → IsProper a →
    (∀ V : Y.Opens, Function.Bijective (a.app V).hom) → ∀ y : Y, _root_.IsPreconnected {x : X | a x = y} := by
  intro X Y a hY ha hbij y
  obtain ⟨_, ⟨U, hU, rfl⟩, hyU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  haveI : IsNoetherianRing Γ(Y, U) := hY.component_noetherian ⟨U, hU⟩
  let e := hU.isoSpec
  let P : PrimeSpectrum Γ(Y, U) := e.hom ⟨y, hyU⟩
  obtain ⟨A, _, _, _, φ, hAc, hφ, hφP⟩ := exists_complete_flat Γ(Y, U) P
  let π : (a ⁻¹ᵁ U).toScheme ⟶ Sp Γ(Y, U) := (a ∣_ U) ≫ e.hom
  let g : Sp A ⟶ Sp Γ(Y, U) := Spec.map (CommRingCat.ofHom φ)
  haveI : Flat g := HasRingHomProperty.Spec_iff.2 hφ
  haveI : IsProper π := inferInstance
  have hres : Function.Bijective ((a ∣_ U).app ⊤).hom := by
    rw [morphismRestrict_app]
    have h1 := hbij ((Scheme.Opens.ι U) ''ᵁ ⊤)
    have h2 := ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom (image_morphismRestrict_preimage a U ⊤)).op)
    exact h2.comp h1
  have hπ : Function.Bijective π.appTop.hom := by
    change Function.Bijective ((a ∣_ U) ≫ e.hom).appTop.hom
    rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp]
    haveI : IsIso e.hom.appTop := inferInstanceAs (IsIso (e.hom.app ⊤))
    exact hres.comp (ConcreteCategory.bijective_of_isIso _)
  have hp := GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions Γ(Y, U) _ _ _ π g (pullback.snd π g) (pullback.fst π g) inferInstance inferInstance hπ
    inferInstance (IsPullback.of_hasPullback π g).flip
  let Z : Scheme.{0} := pullback π g
  let ψ : A →+* Γ(Z, ⊤) :=
    ((pullback.snd π g).app ⊤).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hψ : Function.Bijective ψ := (hp ⊤).comp (ConcreteCategory.bijective_of_isIso _)
  haveI : Nontrivial Γ(Z, ⊤) := hψ.1.nontrivial
  haveI : IsLocalHom ψ := IsLocalHom.of_surjective ψ hψ.2
  haveI : IsLocalRing Γ(Z, ⊤) := IsLocalRing.of_surjective ψ hψ.2
  haveI : PreconnectedSpace Z := preconnectedSpace_of_isLocalRing Z
  have hfib := GlobalTheory.T.isPreconnected_closedFibre_proper_completeLocalNoetherian A hAc Z (pullback.snd π g) inferInstance inferInstance
  have hg : g (closedPoint A) = P := PrimeSpectrum.ext hφP
  have einj : Function.Injective e.hom := e.hom.isOpenEmbedding.injective
  have key : {x : X | a x = y} = (pullback.fst π g ≫ (a ⁻¹ᵁ U).ι) '' {z | pullback.snd π g z = closedPoint A} := by
    ext x
    constructor
    · intro hx
      have hxU : x ∈ a ⁻¹ᵁ U := by
        show a x ∈ U
        rw [hx]; exact hyU
      let x' : (a ⁻¹ᵁ U).toScheme := ⟨x, hxU⟩
      have h1 : (a ∣_ U) x' = ⟨y, hyU⟩ := Subtype.ext ((morphismRestrict_base_coe a U x').trans hx)
      have h2 : π x' = g (closedPoint A) := by
        rw [hg]
        change ((a ∣_ U) ≫ e.hom) x' = P
        rw [Scheme.Hom.comp_apply, h1]
      obtain ⟨z, hz1, hz2⟩ := Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback π g) x' (closedPoint A) h2
      refine ⟨z, hz2, ?_⟩
      rw [Scheme.Hom.comp_apply, hz1]
      rfl
    · rintro ⟨z, hz, rfl⟩
      have h3 : π (pullback.fst π g z) = g (pullback.snd π g z) := by
        rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
      rw [hz, hg] at h3
      have h4 : (a ∣_ U) (pullback.fst π g z) = ⟨y, hyU⟩ := einj (by
        rw [← Scheme.Hom.comp_apply]; exact h3)
      show a ((pullback.fst π g ≫ (a ⁻¹ᵁ U).ι) z) = y
      rw [Scheme.Hom.comp_apply]
      change a (pullback.fst π g z).1 = y
      rw [← morphismRestrict_base_coe a U, h4]
  rw [key]
  exact hfib.image _ (pullback.fst π g ≫ (a ⁻¹ᵁ U).ι).continuous.continuousOn

end GlobalTheory.ZConn
end

