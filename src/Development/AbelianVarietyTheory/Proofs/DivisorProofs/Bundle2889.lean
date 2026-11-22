import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2790
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticMapTangentDifferential
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

open Filter Topology Polynomial

namespace GlobalTheory.CMTorsion.HolPt

theorem isHolTo_congr {B : Set ℂ} {Y : Scheme.{0}} {a a' : ℂ → (Sp ℂ ⟶ Y)} (h : IsHolTo B a)
    (he : ∀ b ∈ B, a' b = a b) : IsHolTo B a' := by
  intro U f
  have hs : {b ∈ B | ⊤ ≤ a' b ⁻¹ᵁ U} = {b ∈ B | ⊤ ≤ a b ⁻¹ᵁ U} := by
    ext b
    exact and_congr_right fun hb => by rw [he b hb]
  rw [hs]
  exact ⟨(h U f).1, (h U f).2.congr fun b hb => by rw [he b hb.1]⟩

theorem valAt'_spMap {A : Type} [CommRing A] (ψ : A →+* ℂ) (a : A) :
    valAt' (spMap ψ) ⊤ ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) = ψ a := by
  have := ReciprocityTheory.ChartRestriction.G.PullbackSections.valAt'_specMap (CommRingCat.ofHom ψ) (𝟙 _) a
  rw [Category.id_comp] at this
  refine this.trans ((ReciprocityTheory.ChartRestriction.G.TB.ValAt.valAt'_of _ _ le_top _).trans ?_)
  simp [valAt, Scheme.Hom.appLE]

theorem isHolTo_spMap {R : Type} [CommRing R] {B : Set ℂ} (hB : IsOpen B) {Ψ : ℂ → (R →+* ℂ)}
    (h : ∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B) : IsHolTo B fun b => spMap (Ψ b) :=
  ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_of_affine hB fun r => by
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 r
    exact (h a).congr fun b _ => valAt'_spMap (Ψ b) a

theorem differentiableOn_eval₂ {B : Set ℂ} {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a B)
    (hb : DifferentiableOn ℂ b B) (p : ℂ[X][X]) :
    DifferentiableOn ℂ (fun t => p.eval₂ (eval₂RingHom (RingHom.id ℂ) (a t)) (b t)) B := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval₂_add]
    exact hp.add hq
  | monomial n c =>
    simp only [eval₂_monomial, coe_eval₂RingHom]
    exact (c.differentiable.comp_differentiableOn ha).mul (hb.pow n)

theorem differentiableOn_adjoinRoot {q : ℂ[X][X]} {B : Set ℂ} {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a B)
    (hb : DifferentiableOn ℂ b B) (Ψ : ℂ → (AdjoinRoot q →+* ℂ))
    (hΨ : ∀ t ∈ B, ∀ p, Ψ t (AdjoinRoot.mk q p) = p.eval₂ (eval₂RingHom (RingHom.id ℂ) (a t)) (b t))
    (r : AdjoinRoot q) : DifferentiableOn ℂ (fun t => Ψ t r) B := by
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective r
  exact (differentiableOn_eval₂ ha hb p).congr fun t ht => hΨ t ht p

theorem affine_equation (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) (t : ℂ) (ht : t ∉ Λ.lattice) :
    ((curve Λ Ω).map (RingHom.id ℂ)).toAffine.Equation (Λ.weierstrassP t / Ω ^ 2)
      (Λ.derivWeierstrassP t / (2 * Ω ^ 3)) := by
  rw [WeierstrassCurve.map_id, WeierstrassCurve.Affine.equation_iff]
  have h := Λ.derivWeierstrassP_sq t ht
  simp only [curve]
  field_simp
  linear_combination 4 * h

end GlobalTheory.CMTorsion.HolPt

namespace GlobalTheory.CMTorsion.HolPt

open GlobalTheory.WeierstrassCurve in

theorem pt_eq_chartZ (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) (t : ℂ) (ht : t ∉ Λ.lattice) :
    pt Λ Ω t = spMap (affineEval (curve Λ Ω) (RingHom.id ℂ) (Λ.weierstrassP t / Ω ^ 2)
      (Λ.derivWeierstrassP t / (2 * Ω ^ 3)) (affine_equation Λ Ω hΩ t ht)) ≫ chartZ (curve Λ Ω) := by
  rw [SpecMap_affineEval_chartZ]
  exact ptHom_congr _ _ _ _ rfl (by simp [coords, ht]) _

open GlobalTheory.WeierstrassCurve in

theorem isHolTo_off (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) :
    IsHolTo ((Λ.lattice : Set ℂ)ᶜ) (pt Λ Ω) := by
  classical
  have hB : IsOpen ((Λ.lattice : Set ℂ)ᶜ) := Λ.isClosed_lattice.isOpen_compl
  have h2 : Λ.ω₁ / 2 ∉ Λ.lattice := Λ.ω₁_div_two_notMem_lattice
  let Ψ : ℂ → ((curve Λ Ω).toAffine.CoordinateRing →+* ℂ) := fun t =>
    if h : t ∉ Λ.lattice then affineEval (curve Λ Ω) (RingHom.id ℂ) (Λ.weierstrassP t / Ω ^ 2)
      (Λ.derivWeierstrassP t / (2 * Ω ^ 3)) (affine_equation Λ Ω hΩ t h)
    else affineEval (curve Λ Ω) (RingHom.id ℂ) (Λ.weierstrassP (Λ.ω₁ / 2) / Ω ^ 2)
      (Λ.derivWeierstrassP (Λ.ω₁ / 2) / (2 * Ω ^ 3)) (affine_equation Λ Ω hΩ _ h2)
  have hP : DifferentiableOn ℂ (fun t => Λ.weierstrassP t / Ω ^ 2) ((Λ.lattice : Set ℂ)ᶜ) :=
    fun t ht => ((Λ.analyticOnNhd_weierstrassP t ht).differentiableAt.div_const _).differentiableWithinAt
  have hP' : DifferentiableOn ℂ (fun t => Λ.derivWeierstrassP t / (2 * Ω ^ 3)) ((Λ.lattice : Set ℂ)ᶜ) :=
    fun t ht => ((Λ.analyticOnNhd_derivWeierstrassP t ht).differentiableAt.div_const _).differentiableWithinAt
  have hΨ : ∀ r, DifferentiableOn ℂ (fun t => Ψ t r) ((Λ.lattice : Set ℂ)ᶜ) :=
    differentiableOn_adjoinRoot hP hP' Ψ fun t ht p => by
      simp only [Ψ, dif_pos (show t ∉ Λ.lattice from ht), affineEval, AdjoinRoot.lift_mk]
  refine isHolTo_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp (isHolTo_spMap hB hΨ) (chartZ (curve Λ Ω)))
    fun t ht => ?_
  simp only [Ψ, dif_pos (show t ∉ Λ.lattice from ht)]
  exact pt_eq_chartZ Λ Ω hΩ t ht

end GlobalTheory.CMTorsion.HolPt

namespace GlobalTheory.CMTorsion.HolPt

open GlobalTheory.WeierstrassCurve in

theorem exists_isHolTo_near (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) (l : ℂ) (hl : l ∈ Λ.lattice) :
    ∃ N : Set ℂ, IsOpen N ∧ l ∈ N ∧ IsHolTo N (pt Λ Ω) := by
  classical
  set A : ℂ → ℂ := fun t => Λ.weierstrassPExcept l t - 1 / l ^ 2 with hA
  set B : ℂ → ℂ := Λ.derivWeierstrassPExcept l with hB
  have hAa : AnalyticAt ℂ A l := (Λ.analyticAt_weierstrassPExcept l).sub analyticAt_const
  have hBa : AnalyticAt ℂ B l := Λ.analyticAt_derivWeierstrassPExcept l
  set D : ℂ → ℂ := fun t => -2 + B t * (t - l) ^ 3 with hD
  have hDc : ContinuousAt D l :=
    continuousAt_const.add (hBa.continuousAt.mul ((continuousAt_id.sub continuousAt_const).pow 3))
  have hD0 : D l ≠ 0 := by simp [hD]
  have hev : ∀ᶠ t in 𝓝 l, t ∉ (Λ.lattice : Set ℂ) \ {l} ∧ AnalyticAt ℂ A t ∧ AnalyticAt ℂ B t ∧ D t ≠ 0 :=
    Filter.Eventually.and (p := fun t => t ∉ (Λ.lattice : Set ℂ) \ {l}) (Λ.compl_lattice_sdiff_singleton_mem_nhds l)
      (hAa.eventually_analyticAt.and (hBa.eventually_analyticAt.and (hDc.eventually_ne hD0)))
  obtain ⟨N, hN, hNo, hlN⟩ := eventually_nhds_iff.1 hev
  have hAd : DifferentiableOn ℂ A N := fun t ht => (hN t ht).2.1.differentiableAt.differentiableWithinAt
  have hBd : DifferentiableOn ℂ B N := fun t ht => (hN t ht).2.2.1.differentiableAt.differentiableWithinAt
  have hDne : ∀ t ∈ N, D t ≠ 0 := fun t ht => (hN t ht).2.2.2
  set Z : ℂ → ℂ := fun t => -2 * Ω * ((t - l) + A t * (t - l) ^ 3) / D t with hZ
  set V : ℂ → ℂ := fun t => -2 * Ω ^ 3 * (t - l) ^ 3 / D t with hV
  have hDd : DifferentiableOn ℂ D N := (differentiableOn_const _).add (hBd.mul ((differentiableOn_id.sub
    (differentiableOn_const _)).pow 3))
  have hZd : DifferentiableOn ℂ Z N := (((differentiableOn_const _).mul ((differentiableOn_id.sub
    (differentiableOn_const _)).add (hAd.mul ((differentiableOn_id.sub (differentiableOn_const _)).pow 3))))).div
    hDd hDne
  have hVd : DifferentiableOn ℂ V N :=
    ((differentiableOn_const _).mul ((differentiableOn_id.sub (differentiableOn_const _)).pow 3)).div hDd hDne
  have key : ∀ t ∈ N, ∃ c : ℂ, c ≠ 0 ∧ coords Λ Ω t = c • ![Z t, -1, V t] := by
    intro t ht
    by_cases htl : t = l
    · subst htl
      refine ⟨-1, by norm_num, ?_⟩
      ext i
      fin_cases i <;> simp [coords, hl, hZ, hV]
    · have ht' : t ∉ Λ.lattice := fun h => (hN t ht).1 ⟨h, htl⟩
      have hs : t - l ≠ 0 := sub_ne_zero.2 htl
      have e1 := Λ.weierstrassPExcept_def ⟨l, hl⟩ t
      have e2 := Λ.derivWeierstrassPExcept_def ⟨l, hl⟩ t
      simp only at e1 e2
      have hAt : A t = Λ.weierstrassP t - 1 / (t - l) ^ 2 := by simp only [hA, e1]; ring
      have hBt : B t = Λ.derivWeierstrassP t + 2 / (t - l) ^ 3 := by simp only [hB, e2]
      have hDt : D t = Λ.derivWeierstrassP t * (t - l) ^ 3 := by
        simp only [hD, hBt]
        field_simp
        ring
      have hQ : Λ.derivWeierstrassP t ≠ 0 := by
        intro h0
        exact hDne t ht (by rw [hDt, h0, zero_mul])
      refine ⟨-(Λ.derivWeierstrassP t / (2 * Ω ^ 3)), by
        exact neg_ne_zero.2 (div_ne_zero hQ (by simp [hΩ])), ?_⟩
      ext i
      fin_cases i
      · simp only [coords, if_neg ht', hZ, hDt, hAt]
        simp
        field_simp
        ring
      · simp only [coords, if_neg ht']
        simp
      · simp only [coords, if_neg ht', hV, hDt]
        simp
        field_simp
  have heq : ∀ t ∈ N, ((curve Λ Ω).map (RingHom.id ℂ)).toProjective.Equation ![Z t, -1, V t] := by
    intro t ht
    obtain ⟨c, hc, h⟩ := key t ht
    have := (isUnimodularSol_coords Λ Ω t).equation
    rwa [h, WeierstrassCurve.Projective.equation_smul _ (IsUnit.mk0 c hc)] at this
  let Ψ : ℂ → (OriginRing (curve Λ Ω) →+* ℂ) := fun t =>
    if h : t ∈ N then originEval (curve Λ Ω) (RingHom.id ℂ) (Z t) (V t) (heq t h)
    else originEval (curve Λ Ω) (RingHom.id ℂ) (Z l) (V l) (heq l hlN)
  have hΨ : ∀ r, DifferentiableOn ℂ (fun t => Ψ t r) N :=
    differentiableOn_adjoinRoot hVd hZd Ψ fun t ht p => by
      simp only [Ψ, dif_pos ht, originEval, AdjoinRoot.lift_mk]
  refine ⟨N, hNo, hlN, isHolTo_congr (ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp (isHolTo_spMap hNo hΨ) (chartY (curve Λ Ω)))
    fun t ht => ?_⟩
  simp only [Ψ, dif_pos ht]
  rw [SpecMap_originEval_chartY]
  obtain ⟨c, hc, h⟩ := key t ht
  exact (ptHom_congr _ _ _ _ rfl h _).trans (ptHom_smul _ _ _ _ (IsUnit.mk0 c hc))

end GlobalTheory.CMTorsion.HolPt

namespace GlobalTheory.CMTorsion.HolPt

theorem isHolTo_pt (Λ : PeriodPair) (Ω : ℂ) (hΩ : Ω ≠ 0) : IsHolTo (Set.univ : Set ℂ) (pt Λ Ω) := by
  refine GlobalTheory.HolHom.isHolTo_of_holAt isOpen_univ fun z _ => ?_
  by_cases hz : z ∈ Λ.lattice
  · obtain ⟨N, -, hzN, hN⟩ := exists_isHolTo_near Λ Ω hΩ z hz
    exact GlobalTheory.HolHom.holAt_of_isHolTo hN hzN
  · exact GlobalTheory.HolHom.holAt_of_isHolTo (isHolTo_off Λ Ω hΩ) hz

end GlobalTheory.CMTorsion.HolPt

namespace GlobalTheory.CMTorsion

theorem exists_vector_of_additive_curve_hom : ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt) (n : ℕ) (u : HolUnif X.A (X.diag c) n) (Λ : PeriodPair) (Ω : ℂ), Ω ≠ 0 → ∀ f : scheme (curve Λ Ω) ⟶ X.A.left, f ≫ X.A.hom = toSpec (curve Λ Ω) → ∀ e : ℂ → (𝟙_ (Over (Sp ℂ)) ⟶ X.A), (∀ z w, e (z + w) = e z * e w) → (∀ z, (e z).left = pt Λ Ω z ≫ f) → ∃ β₁ : Fin n → ℂ, ∀ z, pt Λ Ω z ≫ f = (u.ex (z • β₁)).left := by
  intro F _ _ 𝔠 X c n u Λ Ω hΩ f _ e he hef
  have hg := GlobalTheory.RealMult.Obj.holUnif_dim_eq X u
  subst hg
  obtain ⟨h₁, h₂⟩ := GlobalTheory.TorusTransfer.tangent_bijective u X.dim
  have hpt := HolPt.isHolTo_pt Λ Ω hΩ
  have hol : IsHolTo (Set.univ : Set (Fin 1 → ℂ)) (fun z => (e (z 0)).left) := by
    refine GlobalTheory.HolHom.isHolTo_of_holAt isOpen_univ fun z _ => ?_
    have h1 := ((GlobalTheory.HolHom.holAt_of_isHolTo hpt (Set.mem_univ (z 0))).comp f).precomp
      (k := fun z : Fin 1 → ℂ => z 0) (z := z) (by fun_prop)
    simpa only [hef] using h1
  obtain ⟨L, hL, -⟩ := GlobalTheory.existsUnique_linear_lift_of_isHolTo X.A X.ab (X.diag c) _ 1 u h₁ h₂
    (fun z => e (z 0)) (fun z w => he _ _) hol
  refine ⟨L (fun _ => 1), fun z => ?_⟩
  have hz : z • L (fun _ => 1) = L (fun _ => z) := by
    rw [← map_smul]
    congr 1
    funext
    simp
  rw [hz, hL, hef]

end GlobalTheory.CMTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

section Two

variable {B : Scheme.{0}} (H : Over B) [GrpObj H]
  {V₁ : Type} [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] {D₁ : DegData V₁ (maximalIdeal V₁)}
  {A₁ : PolAV (Sp (FractionRing V₁))} {G₁ : Over (Sp V₁)} [GrpObj G₁] [IsCommMonObj G₁]
  {V₂ : Type} [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] {D₂ : DegData V₂ (maximalIdeal V₂)}
  {A₂ : PolAV (Sp (FractionRing V₂))} {G₂ : Over (Sp V₂)} [GrpObj G₂] [IsCommMonObj G₂]

def Spread₂ (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left)
    (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left)
    (ρ : D₂.toPre.X →+ D₁.toPre.X) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (ψ : Sp W ⟶ B)
    (GW : Over (Sp W)) (_ : GrpObj GW) (_ : IsCommMonObj GW) (φW : GW.left ⟶ H.left)
    (j : splitTorus (Sp W) D₁.toPre.X ⟶ GW)
    (Ω : Type) (_ : Field Ω) (α : W →+* Ω) (b₁ : V₁ →+* Ω) (hb₁ : ∀ x ∈ maximalIdeal V₁ ^ (0 + 1), b₁ x = 0)
    (GΩ : Over (Sp Ω)) (_ : GrpObj GΩ) (n : GΩ.left ⟶ GW.left) (hn : IsGrpPullback GΩ GW (spMap α) n)
    (n₁ : GΩ.left ⟶ G₁.left) (hn₁ : IsGrpPullback GΩ G₁ (spMap b₁) n₁)
    (κ : Type) (_ : Field κ) (c : W →+* κ) (b₂ : V₂ →+* κ) (hb₂ : ∀ x ∈ maximalIdeal V₂ ^ (0 + 1), b₂ x = 0)
    (Gκ : Over (Sp κ)) (_ : GrpObj Gκ) (m : Gκ.left ⟶ GW.left) (hm : IsGrpPullback Gκ GW (spMap c) m)
    (m₂ : Gκ.left ⟶ G₂.left) (hm₂ : IsGrpPullback Gκ G₂ (spMap b₂) m₂),
    IsGrpPullback GW H ψ φW ∧ IsMonHom j ∧ Function.Injective α ∧ IsLocalHom c ∧
      spMap α ≫ ψ = spMap b₁ ≫ ξ₁ ∧ spMap c ≫ ψ = spMap b₂ ≫ ξ₂ ∧ n ≫ φW = n₁ ≫ β₁ ∧ m ≫ φW = m₂ ≫ β₂ ∧
      GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb₁ hn₁ ∧
      GlobalTheory.TorusPart.pullTorus hm j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U₂.gt 0) hb₂ hm₂

def TorAt (U : Unif (maximalIdeal V₁) D₁ A₁ G₁) (F : Type) [Field F] [Algebra (FractionRing V₁) F] (k : ℕ) (z : F)
    (c : D₁.toPre.X →+ ℤ) (x : TFK (R := V₁) F ⟶ A₁.A) : Prop :=
  ∃ (τ : Multiplicative D₁.toPre.X →* Fˣ) (q : QkPt D₁.toPre F k),
    (∀ χ, (τ (Multiplicative.ofAdd χ) : F) = z ^ c χ) ∧ q.y = 0 ∧ IsTor τ q.g ∧ QkToAkU U.toUnifPre F k q x

end Two

section Model
open Classical

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE)

def EndOn (f : ρ.P.A ⟶ ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G) : Prop :=
  ((Over.pullback FinalForm.u₀).map f).left ≫ FinalForm.φ = FinalForm.φ ≫ Fm.left

def SecOn (a : S.Gam) (Wo : M.Z.Opens) (h : Wo.toScheme ⟶ FinalForm.G.left) : Prop :=
  h ≫ FinalForm.G.hom = Wo.ι ∧
    ∀ (x : Sp Ω ⟶ Wo.toScheme) (x' : Sp Ω ⟶ pullback ρ.P.A.hom FinalForm.u₀), x ≫ Wo.ι = M.pt → x' ≫ FinalForm.φ ≫ FinalForm.G.hom = M.pt →
      x' ≫ pullback.fst _ _ = spMap S.R.val.toRingHom ≫ (ρ.pt a).left → x ≫ h = x' ≫ FinalForm.φ

def Link {T : Scheme.{0}} (x : T ⟶ M.Z) (u : T ⟶ Sp S.R) (A : Over T) [GrpObj A] (φ : A.left ⟶ ρ.P.A.left)
    (gm : A.left ⟶ FinalForm.G.left) : Prop :=
  IsGrpPullback A FinalForm.G x gm ∧
    (∀ (f : ρ.P.A ⟶ ρ.P.A) (Fm : FinalForm.G ⟶ FinalForm.G), EndOn FinalForm f Fm → ∀ (T' : Scheme.{0}) (p p' : T' ⟶ A.left),
      p' ≫ A.hom = p ≫ A.hom → p' ≫ φ = p ≫ φ ≫ f.left → p' ≫ gm = p ≫ gm ≫ Fm.left) ∧
    ∀ (a : S.Gam) (Wo : M.Z.Opens) (h : Wo.toScheme ⟶ FinalForm.G.left), SecOn FinalForm a Wo h →
      ∀ (T' : Scheme.{0}) (p : T' ⟶ A.left) (x' : T' ⟶ Wo.toScheme), x' ≫ Wo.ι = p ≫ A.hom ≫ x →
        p ≫ φ = p ≫ A.hom ≫ u ≫ (ρ.pt a).left → p ≫ gm = x' ≫ h

theorem Link.pull {T T₁ : Scheme.{0}} {x : T ⟶ M.Z} {u : T ⟶ Sp S.R} {A : Over T} [GrpObj A] {φ : A.left ⟶ ρ.P.A.left}
    {gm : A.left ⟶ FinalForm.G.left} (h : Link FinalForm x u A φ gm) {v : T₁ ⟶ T} {A' : Over T₁} [GrpObj A'] {w : A'.left ⟶ A.left}
    (hw : IsGrpPullback A' A v w) : Link FinalForm (v ≫ x) (v ≫ u) A' (w ≫ φ) (w ≫ gm) := by
  have e : w ≫ A.hom = A'.hom ≫ v := hw.1.w
  refine ⟨hw.comp h.1, fun f Fm hf T' p p' h₁ h₂ => ?_, fun a Wo s hs T' p x' h₁ h₂ => ?_⟩
  · have := h.2.1 f Fm hf T' (p ≫ w) (p' ≫ w) (by rw [Category.assoc, Category.assoc, e, reassoc_of% h₁])
      (by simpa only [Category.assoc] using h₂)
    simpa only [Category.assoc] using this
  · have := h.2.2 a Wo s hs T' (p ≫ w) x' (by rw [h₁, Category.assoc, reassoc_of% e])
      (by rw [Category.assoc, Category.assoc, reassoc_of% e]; simpa only [Category.assoc] using h₂)
    simpa only [Category.assoc] using this

end Model

end GlobalTheory.Poinc.Sep.Spz
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfProdZpowSymmetricFormBasisEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.SymMono

def elem {r : ℕ} (a b : Fin r) : LinearMap.BilinForm ℤ (Fin r → ℤ) :=
  (LinearMap.mul ℤ ℤ).compl₁₂ (LinearMap.proj a) (LinearMap.proj b)

@[simp] theorem elem_apply {r : ℕ} (a b : Fin r) (u v : Fin r → ℤ) : elem a b u v = u a * v b := rfl

def symElem {r : ℕ} (a b : Fin r) : LinearMap.BilinForm ℤ (Fin r → ℤ) :=
  (if a ≤ b then elem a b else 0) + (if a < b then elem b a else 0)

theorem symElem_symm {r : ℕ} (a b : Fin r) (u v : Fin r → ℤ) : symElem a b u v = symElem a b v u := by
  unfold symElem
  rcases lt_trichotomy a b with h | rfl | h
  · simp [h, h.le]; ring
  · simp; ring
  · simp [not_le.2 h, not_lt.2 h.le]

theorem ite_bil_apply {r : ℕ} (p : Prop) [Decidable p] (f : LinearMap.BilinForm ℤ (Fin r → ℤ)) (u v : Fin r → ℤ) :
    (if p then f else 0) u v = if p then f u v else 0 := by
  split_ifs <;> rfl

theorem sum_symElem {r : ℕ} (β : LinearMap.BilinForm ℤ (Fin r → ℤ)) (hβ : ∀ u v, β u v = β v u) :
    β = ∑ a, ∑ b, β (Pi.single a 1) (Pi.single b 1) • symElem a b := by
  refine LinearMap.BilinForm.ext_basis (Pi.basisFun ℤ (Fin r)) fun i j => ?_
  simp only [Pi.basisFun_apply, LinearMap.sum_apply, LinearMap.smul_apply, symElem,
    LinearMap.add_apply, smul_eq_mul]
  simp only [ite_bil_apply, elem_apply, Pi.single_apply, mul_add, Finset.sum_add_distrib, mul_ite, ite_mul, mul_one, mul_zero, zero_mul, one_mul]
  simp only [← ite_and]
  rw [Fintype.sum_eq_single i (fun x hx => Fintype.sum_eq_zero _ (fun y => if_neg (by tauto))),
    Fintype.sum_eq_single j (fun x hx => Fintype.sum_eq_zero _ (fun y => if_neg (by tauto))),
    Fintype.sum_eq_single j (fun y hy => if_neg (by tauto)),
    Fintype.sum_eq_single i (fun y hy => if_neg (by tauto))]
  rcases le_or_gt i j with h | h
  · simp [h, not_lt.2 h]
  · simp [h, not_le.2 h, hβ (Pi.single i 1)]

end GlobalTheory.SymMono

namespace GlobalTheory.SymMono

theorem zpow_finsum {G J : Type} [CommGroup G] (g : G) (s : Finset J) (f : J → ℤ) :
    g ^ (∑ i ∈ s, f i) = ∏ i ∈ s, g ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

theorem symElem_mem {r : ℕ} (a b : Fin r) : symElem a b ∈ balForms (id : ℤ → ℤ) (Fin r → ℤ) :=
  mem_balForms_int.2 (symElem_symm a b)

theorem repr_self_eq_sum {r : ℕ} {I : Type} (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (i k : I) :
    ε.repr (ε i) k = ∑ a, ∑ b, (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1) (Pi.single b 1) *
      ε.repr ⟨symElem a b, symElem_mem a b⟩ k := by
  have he : ε i = ∑ a, ∑ b, (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1) (Pi.single b 1) •
      (⟨symElem a b, symElem_mem a b⟩ : balForms (id : ℤ → ℤ) (Fin r → ℤ)) := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact sum_symElem _ (mem_balForms_int.1 (ε i).2)
  conv_lhs => rw [he]
  simp only [map_sum, LinearEquiv.map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem eq_of_prod_zpow_eq (F : Type) [Field F] (r : ℕ) (I : Type) [Fintype I]
    (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (x y : I → F) (hx : ∀ i, x i ≠ 0) (hy : ∀ i, y i ≠ 0)
    (h : ∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b =
      ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) : x = y := by
  classical
  set X : I → Fˣ := fun i => Units.mk0 (x i) (hx i) with hXd
  set Y : I → Fˣ := fun i => Units.mk0 (y i) (hy i) with hYd
  have hXY : ∀ a b, ∏ i, (X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) = 1 := by
    intro a b
    rw [Finset.prod_congr rfl (fun i _ => div_zpow _ _ _), Finset.prod_div_distrib, div_eq_one]
    apply Units.ext
    simpa [X, Y, Units.coe_prod] using h a b
  funext k
  have hk : X k / Y k = 1 := by
    calc X k / Y k = ∏ i, (X i / Y i) ^ (ε.repr (ε i) k) := by
          simp [Finsupp.single_apply]
      _ = ∏ i, ∏ a, ∏ b, ((X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1)
            (Pi.single b 1))) ^ (ε.repr ⟨symElem a b, symElem_mem a b⟩ k) := by
          refine Finset.prod_congr rfl fun i _ => ?_
          rw [repr_self_eq_sum, zpow_finsum]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [zpow_finsum]
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [zpow_mul]
      _ = ∏ a, ∏ b, (∏ i, (X i / Y i) ^ ((ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) (Pi.single a 1)
            (Pi.single b 1))) ^ (ε.repr ⟨symElem a b, symElem_mem a b⟩ k) := by
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun a _ => ?_
          rw [Finset.prod_comm]
          refine Finset.prod_congr rfl fun b _ => ?_
          rw [Finset.prod_zpow]
      _ = 1 := by simp [hXY]
  simpa [X, Y] using congrArg Units.val (div_eq_one.1 hk)

end GlobalTheory.SymMono

example : ∀ (F : Type) [Field F] (r : ℕ) (I : Type) [Fintype I] (ε : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin r → ℤ))) (x y : I → F), (∀ i, x i ≠ 0) → (∀ i, y i ≠ 0) → (∀ a b, ∏ i, x i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b = ∏ i, y i ^ (ε i : LinearMap.BilinForm ℤ (Fin r → ℤ)) a b) → x = y := GlobalTheory.SymMono.eq_of_prod_zpow_eq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivMapOfTorMatch
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8

theorem equivMap_of_torMatch : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), Function.Injective g → ∀ ρ, TorMatch U U' g β ρ → EquivMap U U' β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hg ρ h
  intro f f' hf hf' hc m m' hm hm' y
  have hkV : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : V) := fun k hk => by
    simpa using hk.map g
  have hkR : ∀ k : ℕ, IsUnit (k : R) → IsUnit (k : R) := fun _ hk => hk
  have t := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar R hR G hG D A U f hf m hm
  have t' := GlobalTheory.Poinc.TorEnd.torMatch_of_endChar V hV G' hG' D' A' U' f' hf' m' hm'
  have c₁ := torMatch_comp R hR G hG D A U R hR G hG D A U (RingHom.id R) f.left V hV G' hG' D' A' U' g β hg hkR m ρ t h
  have c₂ := torMatch_comp R hR G hG D A U V hV G' hG' D' A' U' g β V hV G' hG' D' A' U' (RingHom.id V) f'.left
    Function.injective_id hkV ρ m' h t'
  rw [RingHom.comp_id] at c₁
  rw [RingHom.id_comp, hc] at c₂
  have e := torMatch_unique R hR G hG D A U V hV G' hG' D' A' U' g (β ≫ f.left) hg _ _ c₁ c₂
  exact DFunLike.congr_fun e y

end GlobalTheory.Poinc.Eq8
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveActionThickeningEndosCompletePointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additive_action_thickeningEndos_completePoints : ∀ (R : Type) [CommRing R] (I : Ideal R) (G : Over (Sp R)) [GrpObj G] (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G), (∀ e, IsMonHom (b e)) → (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) → ∀ (B : Type) [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B] (s : Sp B ⟶ Sp R), s (closedPoint B) ∈ Set.range (thick R I 0) → ∃ Φ : (Over.mk s ⟶ G) → (Over.mk s ⟶ G), (∀ x y, Φ (x * y) = Φ x * Φ y) ∧ ∀ (x : Over.mk s ⟶ G) (e : ℕ), ∃ r : Sp (B ⧸ maximalIdeal B ^ (e + 1)) ⟶ (thickObj R I e G).left, r ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ x.left ∧ r ≫ (b e).left ≫ pullback.fst G.hom (thick R I e) = thick B (maximalIdeal B) e ≫ (Φ x).left := by
  first | exact @GlobalTheory.exists_mul_map_points_of_thickEndo | exact GlobalTheory.exists_mul_map_points_of_thickEndo | (intros; apply GlobalTheory.exists_mul_map_points_of_thickEndo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineChartThetaSystemUnitaryModelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_chart_thetaSystem_unitary_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf) (X : USetup C) (wi : UWit X) (w : X.M.Z), X.π w ∈ Set.range C.i → ∃ (U : X.M.Z.Opens) (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (fg : (X.M.ringOn U).FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ X.M.ringOn U, ∃ b ∈ X.M.ringOn U, x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ X.M.ringOn U) (hev : ∀ x k, c₀ * X.S.ev x k ∈ X.M.ringOn U) (ρ' : (X.S.rechart c₀ hc (X.M.ringOn U) fg frac hth hev).Real) (u' : Sp (ratHull (X.M.ringOn U)) ⟶ Xo.XF cf), IsAffineOpen U ∧ w ∈ U ∧ USame X.ρ ρ' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ (∃ (G : Over (Sp (ratHull (X.M.ringOn U)))) (_ : GrpObj G) (α : G.left ⟶ ρ'.P.A.left) (β : G.left ⟶ Xo.univ.t.G.left), IsGrpPullback G ρ'.P.A (spMap (toRat (X.M.ringOn U))) α ∧ IsGrpPullback G Xo.univ.t.G (u' ≫ pullback.fst _ _) β ∧ LBIso (ρ'.P.L.pull α) (Xo.univ.t.PP.L.pull β) ∧ (∃ m : wi.G.left ⟶ G.left, IsGrpPullback wi.G G (spMap (ratHull (X.M.ringOn U)).val.toRingHom) m ∧ m ≫ β = wi.β ∧ ∀ x, ∃ w : Sp X.Ω₁ ⟶ wi.G.left, w ≫ wi.α = spMap X.S.R.val.toRingHom ≫ (X.ρ.pt x).left ∧ w ≫ m ≫ α = spMap (Subalgebra.val (X.M.ringOn U)).toRingHom ≫ (ρ'.pt x).left)) ∧ spMap (ratHull (X.M.ringOn U)).val.toRingHom ≫ u' = X.uΩ := by
  first | exact @GlobalTheory.UPoinc.exists_urechart_affine | exact GlobalTheory.UPoinc.exists_urechart_affine | (intros; apply GlobalTheory.UPoinc.exists_urechart_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspFormParallelWeightEachComponentStatement
section
open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_cuspForm_parallelWeight_each_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n ∧ (∀ τ i, i < Dw.mult τ → 2 ≤ a (τ, i)) ∧ 4 * (finrank ℚ E * r) + 4 ≤ n ∧ ∃ f ∈ cuspOn U Z (wtZ a n), f ≠ 0 := by
  first | exact @GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero | exact GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero | (intros; apply GlobalTheory.FlatCore.NonzeroCusp.exists_cuspOn_ne_zero <;> assumption)
end

