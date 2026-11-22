import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0164
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReduction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0123
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0098
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionsPowVeryAmpleAreFormsOfClosedFibre

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSectionLiftClosedBaseChangeOfH1VanishesStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_lift_closed_baseChange_of_h1Vanishes : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → IsProjBy f → ∀ M : LB X, M.IsLB → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (M₀ : LB X₀) (w₀ : LB.Iso M₀ (M.pull π)), M₀.IsLB → w₀.IsGen → FirstCohomologyVanishes M₀ → ∀ (A' : Type) [CommRing A'] (g : A →+* A'), Function.Surjective g → ∀ (X' : Scheme.{0}) (β : X' ⟶ X) (f' : X' ⟶ Spec (CommRingCat.of A')), IsPullback β f' f (Spec.map (CommRingCat.ofHom g)) → ∀ (M' : LB X') (w : LB.Iso M' (M.pull β)), M'.IsLB → w.IsGen → ∀ s' : LB.Sec M', ∃ s : LB.Sec M, (∀ z (k : (M).ι) (k' : (M').ι), (β) z ∈ (M).U k → z ∈ (M').U k' → gs (β) z _ ((s).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s').f k')) := by
  first | exact @GlobalTheory.SecLiftClosed.exists_lift | exact GlobalTheory.SecLiftClosed.exists_lift | (intros; apply GlobalTheory.SecLiftClosed.exists_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTwistSections
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ThetaData

theorem valR_eq_gs {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (x : Sp R ⟶ X) (U : X.Opens)
    (h : x (IsLocalRing.closedPoint R) ∈ U) (f : Γ(X, U)) :
    valR x U f = (stalkClosedPointIso (CommRingCat.of R)).hom.hom (gs x (IsLocalRing.closedPoint R) U f) := by
  have h' := (CrdCalc.top_le_iff x U).2 h
  rw [CrdCalc.valR_eq x U h', gs_eq x _ U h]
  have e := germ_stalkClosedPointIso_hom (CommRingCat.of R)
  change (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
    (((Sp R).presheaf.map (homOfLE h').op).hom ((x.app U).hom f)) = _
  rw [← e]
  exact congrArg (stalkClosedPointIso (CommRingCat.of R)).hom.hom
    (TopCat.Presheaf.germ_res_apply (Sp R).presheaf (homOfLE h') _ trivial _)

theorem crd_of_chartSec {R : Type} [CommRing R] [IsLocalRing R] {Y Y' : Scheme.{0}} {A' : LB Y'} {A : LB Y}
    {h : Y' ⟶ Y} (a : ChartPull A' A h) {J : Type} (s : J → A.Sec) (x : Sp R ⟶ Y') (v : J → R)
    (H : Crd A' (fun j => chartSec a (s j)) x v) : Crd A s (x ≫ h) v := by
  obtain ⟨l, c, hl, hv⟩ := H
  have m := (CrdCalc.top_le_iff x _).1 hl
  have m' : (x ≫ h) (IsLocalRing.closedPoint R) ∈ A.U (a.idx l) := a.le l m
  refine ⟨a.idx l, c, (CrdCalc.top_le_iff _ _).2 m', fun j => ?_⟩
  rw [hv, valR_eq_gs x _ m, valR_eq_gs _ _ m', gs_chartSec a (s j) x _ l m]

theorem crd_secPull {R : Type} [CommRing R] [IsLocalRing R] {Y Y' : Scheme.{0}} {A : LB Y}
    (h : Y' ⟶ Y) {J : Type} (s : J → A.Sec) (x : Sp R ⟶ Y') (v : J → R)
    (H : Crd A s (x ≫ h) v) : Crd (A.pull h) (fun j => secPull (s j) h) x v := by
  obtain ⟨l, c, hl, hv⟩ := H
  have m' := (CrdCalc.top_le_iff _ _).1 hl
  have m : x (IsLocalRing.closedPoint R) ∈ (A.pull h).U (fun _ => l) := mem_pull.2 m'
  refine ⟨fun _ => l, c, (CrdCalc.top_le_iff _ _).2 m, fun j => ?_⟩
  rw [hv, valR_eq_gs x _ m, valR_eq_gs _ _ m']
  exact congrArg (fun q => (c : R) * (stalkClosedPointIso (CommRingCat.of R)).hom.hom q)
    (gs_chartSec (GlobalTheory.chartPullPull A h) (s j) x _ (fun _ => l) m).symm

theorem exists_twist_sections {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) {T : Over S}
    {ψ : T ⊗ A ⟶ T ⊗ A} {m : T ⊗ A ⟶ A} {hm : ψ ≫ snd T A = m} {a : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, m.left] ![a, -1])} (hα : α.IsGen) {J : Type}
    (s : J → LB.Sec (LPow A L a T)) (th : LB.Sec (LPow A L 1 T)) (i₀ : J)
    (H : IsTwistPull A L ψ m hm a 1 α th (s i₀)) {Y : Scheme.{0}} (κ : Y ⟶ (T ⊗ A).left) (F : Y ⟶ A.left)
    (hF : κ ≫ (snd T A).left = F) (n : Y ⟶ Y) (hn : n ≫ κ = κ ≫ ψ.left) :
    ∃ (θ : (L.pull F).Sec) (t : J → ((L.pull F).pull n).Sec),
      (∀ (K : Type) [Field K] (x : Sp K ⟶ Y) (v : J → K), Crd _ t x v → Crd (LPow A L a T) s (x ≫ κ) v) ∧
      ∀ (y : Y) (j : (L.pull F).ι), n y ∈ (L.pull F).U j →
        gs (𝟙 Y) y _ ((t i₀).f (fun _ => j)) = gs n y _ (θ.f j) := by
  have e : κ ≫ m.left = n ≫ F := by
    rw [← hm, Over.comp_left, ← Category.assoc, ← hn, Category.assoc, hF]
  obtain ⟨θ, hθ⟩ := exists_sec hL (φ := fun _ : Fin 1 => F) (ε := fun _ => 1) (φ' := fun _ : PUnit => F)
    (ε' := fun _ => 1) (fun U _ h => by simp)
    (VVRank.pullTo (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => 1) th κ (fun _ => hF))
  have hu := LB.isGen_invGen L _ _ _ (LB.isGen_pullGen L _ _ α hα κ)
  have hσ : ∀ j, ∃ σ : (L.pull (n ≫ F)).Sec, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I), Good L z I →
      sval (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) σ r z I =
        VVRank.sv A (s j) (r ≫ κ) z I * ((val α (r ≫ κ) z I)⁻¹).val := by
    intro j
    obtain ⟨σ, hσ⟩ := exists_sec hL (φ' := fun _ : PUnit => n ≫ F) (ε' := fun _ => 1)
      (fun U _ h => by simp [Fintype.prod_sum_type, e])
      (pullMulSec (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => a) (s j) κ _ hu)
    refine ⟨σ, fun Z r z I hI => (hσ Z r z I hI).trans ((sval_pullMulSec _ κ _ hu r z hI).trans ?_)⟩
    rw [val_inv, val_pull hI]
  choose σ hσ using hσ
  let c := chartPullLinComb L F (fun _ : PUnit => n) (fun _ : PUnit => n ≫ F) (fun _ => 1) (𝟙 Y)
    (fun _ => (Category.id_comp _).symm)
  refine ⟨θ, fun j => chartSec c (σ j), fun K _ x v hv => ?_, fun y j hj => ?_⟩
  · obtain ⟨l, u, hl, hv⟩ := crd_of_chartSec c σ x v hv
    rw [Category.comp_id] at hl hv
    have m₁ := (CrdCalc.top_le_iff _ _).1 hl
    obtain ⟨I, hI, eI⟩ := exists_good L hL (IsLocalRing.closedPoint K : Sp K) (fun _ : PUnit => x ≫ n ≫ F) l
      (fun _ _ _ => rfl) (fun k => Set.mem_iInter.1 m₁ k)
    have m₂ := hI.mem (fun _ : Fin 1 => (snd T A).left) (x ≫ κ)
    refine ⟨fun _ => I ((x ≫ κ) ≫ (snd T A).left), u * Units.map (stalkClosedPointIso (CommRingCat.of K)).hom.hom.toMonoidHom
      (val α (x ≫ κ) _ I)⁻¹, (CrdCalc.top_le_iff _ _).2 m₂, fun j => ?_⟩
    have e₁ := (sval_of (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) (σ j) x _ I l eI).symm.trans (hσ j _ x _ I hI)
    refine (hv j).trans ?_
    refine (congrArg (_ * ·) ((valR_eq_gs x _ m₁ _).trans ((congrArg _ e₁).trans (map_mul _ _ _)))).trans ?_
    rw [Units.val_mul, _root_.mul_assoc, _root_.mul_comm (Units.val (Units.map _ _))]
    exact congrArg (fun q => (u : K) * (q * _)) (valR_eq_gs (x ≫ κ) _ m₂ _).symm
  · have m₁ : (n ≫ F) y ∈ L.U (j PUnit.unit) := mem_pull (F := F).1 hj
    obtain ⟨I, hI, eI⟩ := exists_good L hL y (fun _ : PUnit => n ≫ F) j (fun _ _ _ => rfl) (fun k => m₁)
    refine (gs_chartSec c (σ i₀) (𝟙 Y) y (fun _ => j) (mem_pull (F := n).2 hj)).trans ?_
    have e₁ := (sval_of (φ := fun _ : PUnit => n ≫ F) (ε := fun _ => 1) (σ i₀) (𝟙 Y ≫ 𝟙 Y) y I j
      (fun k => by simpa using eI k)).symm.trans (hσ i₀ _ _ _ I hI)
    have e₂ := (sval_of (φ := fun _ : PUnit => F) (ε := fun _ => 1) θ n y I j eI).symm.trans
      ((hθ _ n y I hI).trans (VVRank.sval_pullTo _ _ _ _ _ hI))
    refine e₁.trans (Eq.trans ?_ e₂.symm)
    rw [VVRank.sv_of_isTwistPull A H _ y hI, mul_right_comm, Units.mul_inv, _root_.one_mul, hn]
    simp only [Category.id_comp]

theorem mulN_eq_id_pow {S : Scheme.{0}} (G : Over S) [GrpObj G] (n : ℕ) : mulN G n = (𝟙 G) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem mulN_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G]
    [GrpObj G'] [IsCommMonObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (n : ℕ) :
    (mulN G' n).left ≫ φ = φ ≫ (𝟙 G ^ n : G ⟶ G).left := by
  have e := congrArg (fun q => q.left) (map_pow (pushHom h G') (𝟙 G') n)
  have e₂ : pushHom h G' (𝟙 G') ≫ 𝟙 G ^ n = pushHom h G' (𝟙 G') ^ n := by
    rw [MonObj.comp_pow, Category.comp_id]
  rw [← e₂, ← mulN_eq_id_pow] at e
  refine Eq.trans e ?_
  change (𝟙 _ ≫ φ) ≫ _ = _
  rw [Category.id_comp]

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem exists_iso [ArithBase o Ω] (hLL : GlobalTheory.UT.LL) {S : ThetaSys o Ω} (ρ : S.Real) {B : Scheme.{0}} (A' : Over B)
    [GrpObj A'] [IsCommMonObj A'] [IsIntegral A'.left] {f : B ⟶ Sp S.R} {F : A'.left ⟶ ρ.P.A.left}
    (h : IsGrpPullback A' ρ.P.A f F) {Y : Scheme.{0}} (a : A'.left ⟶ Y) {O : LB Y} (hO : O.IsLB) (st : S.J → O.Sec)
    (hc : ∀ (K : Type) [Field K] (x : Sp K ⟶ A'.left) (v : S.J → K), ρ.Crd (x ≫ F) v → Crd O st (x ≫ a) v) :
    ∃ (θ : (ρ.P.L.pull F).Sec) (w : LB.Iso ((ρ.P.L.pull F).pull (mulN A' (ρ.n ^ ρ.k)).left) (O.pull a)), w.IsGen ∧
      ∀ (x : A'.left) (i : O.ι) (j : (ρ.P.L.pull F).ι), a x ∈ O.U i →
        (mulN A' (ρ.n ^ ρ.k)).left x ∈ (ρ.P.L.pull F).U j →
        gs a x _ ((st ρ.i₀).f i) = gs (𝟙 _) x _ (w.s (fun _ => i, fun _ => j)).val *
          gs (mulN A' (ρ.n ^ ρ.k)).left x _ (θ.f j) := by
  have : IsIso (snd (baseOver (Sp S.R)) ρ.P.A).left :=
    inferInstanceAs (IsIso (pullback.snd (𝟙 (Sp S.R)) ρ.P.A.hom))
  let κ := F ≫ inv (snd (baseOver (Sp S.R)) ρ.P.A).left
  have hκ : κ ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = F := by simp [κ]
  have hn : (mulN A' (ρ.n ^ ρ.k)).left ≫ κ = κ ≫ (mulT ρ.P.A (baseOver (Sp S.R)) (ρ.n ^ ρ.k)).left := by
    rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, Category.assoc, hκ, mulN_comp h, Category.assoc,
      ← Over.comp_left, mulT, lift_snd, ← hκ, Category.assoc, ← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨θ, t, ht, hθ⟩ := exists_twist_sections ρ.P.A ρ.P.isLB ρ.α_gen ρ.s ρ.th₁ ρ.i₀ ρ.s_zero κ F hκ _ hn
  have hH := LB.isLB_pull (LB.isLB_pull ρ.P.isLB F) (mulN A' (ρ.n ^ ρ.k)).left
  have hcov : ⨆ j, nonzeroLocus (t j) = ⊤ := by
    refine top_le_iff.1 fun y _ => ?_
    obtain ⟨K, _, p, hp⟩ := CrdIso.exists_pt y
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists hH t p
    have h₀ := (ThetaSys.Real.immBy_basis hLL o Ω S ρ).1
    have h₁ : (p ≫ κ) (IsLocalRing.closedPoint K) ∈ ⨆ i ∈ (Set.univ : Set S.J), nonzeroLocus (ρ.s i) := by
      rw [h₀]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 h₁
    obtain ⟨-, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
    have h₂ := (CrdCalc.crd_isUnit_iff i (ht K p v hv)).2 ((CrdCalc.top_le_iff _ _).2 hi)
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (hp _).1 ((CrdCalc.crd_isUnit_iff i hv).1 h₂)⟩
  obtain ⟨w, hw, hs⟩ := CrdIso.exists_iso_of_crd _ _ (O.pull a) _ t (fun j => secPull (st j) a) hH
    (LB.isLB_pull hO a) hcov (fun K _ x v hv => crd_secPull a st x v
      (hc K x v ⟨x ≫ κ, by rw [Category.assoc, hκ], ht K x v hv⟩))
  refine ⟨θ, w, hw, fun x i j hi hj => ?_⟩
  have e := hs ρ.i₀ x (fun _ => j) (fun _ => i) (mem_pull.2 hj) (mem_pull.2 hi)
  rw [hθ x j hj] at e
  refine Eq.trans ?_ e
  have e' := gs_chartSec (GlobalTheory.chartPullPull O a) (st ρ.i₀) (𝟙 _) x (fun _ => i) (mem_pull.2 hi)
  rw [Category.id_comp] at e'
  exact e'.symm

theorem exists_theta : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ∃ T : ex.core.Theta, LBIso T.L.L (ρ.P.L.pull (pullback.fst ρ.P.A.hom Q.u₀)) := by
  intro hLL o Ω _ _ _ _ S ρ M U₀ EE hB Q ex hS hG
  have := ArithBase.ded (o := o) (Ω := Ω)
  have : Algebra.FiniteType o S.R := (Subalgebra.fg_iff_finiteType _).1 S.fg
  have : IsNoetherianRing S.R := Algebra.FiniteType.isNoetherianRing o S.R
  have : IsLocallyNoetherian (Sp S.R) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of S.R)))
  have := ex.ab.comm
  have hI : IsIntegral ex.core.A.left := by
    have := ex.core.isIntegral_G
    have := ex.core.isOpenImmersion_a
    have := ex.core.nonempty_A
    exact isIntegral_of_isOpenImmersion ex.core.a
  have : IsIntegral ((Over.pullback Q.u₀).obj ρ.P.A).left := hI
  have h := isGrpPullback_pullback ρ.P.A Q.u₀
  obtain ⟨c⟩ := (hLL.1.cube _ ρ.P ⟨ρ.P.L, ρ.rig, ρ.P.isLB, ρ.rig_gen⟩ rfl).1
  obtain ⟨hL, hr, ⟨c', -⟩, -⟩ := hLL.2.2.1.cubePull _ _ _ _ (cubeMapOf h) _ c
  obtain ⟨θ, w, hw, hs⟩ := exists_iso hLL ρ _ h ex.a (LB.isLB_pull Q.isLB Q.G.ι) (fun j => secPull (Q.st j) Q.G.ι)
    (fun K _ x v hv => crd_secPull _ _ _ _ (by
      have e := Q.crd K x v hv
      rw [← ex.a_eq] at e
      rw [Category.assoc]
      exact e))
  have hm : IsUnit ((ρ.n ^ ρ.k : ℕ) : Γ(M.Z, ⊤)) := by
    have h₁ : IsUnit ((ρ.n ^ ρ.k : ℕ) : o) :=
      isUnit_of_dvd_unit (Nat.cast_dvd_cast (ρ.N_eq ▸ Dvd.dvd.mul_left (dvd_pow_self _ two_ne_zero) S.r)) S.unit
    have h₂ := h₁.map (M.s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
    rwa [map_natCast] at h₂
  refine ⟨⟨_, c', θ, ρ.n ^ ρ.k, hm, _, LB.isLB_pull Q.isLB Q.G.ι, secPull (Q.st ρ.i₀) Q.G.ι, w, hw, hs,
    fun z hz => ?_⟩, lbIso_refl hL⟩
  obtain ⟨x, hx, hG', e⟩ := GlobalTheory.T.exists_theta_pullback_nonzero_on_closed_fibre hLL o Ω S ρ M U₀ EE hB Q hS hG z hz
  refine ⟨⟨x, hG'⟩, ?_, e⟩
  erw [nonzeroLocus_secPull]
  exact hx

end GlobalTheory.ZH.ThetaData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnramifiedExtTorsionPointsGoodReductionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unramified_ext_torsion_points_good_reduction : Laws → Laws2 → ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → abLocus G = Set.univ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T F], Function.Injective (algebraMap T F) → ∀ k : ℕ, IsUnit (k : T) → ∃ (T' : Subalgebra T F) (_ : IsDiscreteValuationRing T'), (∀ π : T, Irreducible π → Irreducible (algebraMap T T' π)) ∧ ∀ x : Over.mk (spMap (algebraMap T F)) ⟶ G, x ^ k = 1 → ∃ x' : Sp T' ⟶ G.left, spMap (T'.val.toRingHom) ≫ x' = x.left := by
  first | exact @GlobalTheory.exists_unramified_torsion_points | exact GlobalTheory.exists_unramified_torsion_points | (intros; apply GlobalTheory.exists_unramified_torsion_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasGradedChartsNearGenericPointClosureStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGradedCharts_near_generic_point_closure : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (ex : Q.Ext), S.Big → ρ.HasGeo → ex.core.Fib → ex.core.HasCharts := by
  first | exact @GlobalTheory.ZH.GradedCharts.hasCharts | exact GlobalTheory.ZH.GradedCharts.hasCharts | (intros; apply GlobalTheory.ZH.GradedCharts.hasCharts <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfClosedFibreLocalRing
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KTrivLocal

open GlobalTheory.AbLaw GlobalTheory.UU

theorem ring_retraction {A C : Type} [CommRing A] [IsLocalRing A] [CommRing C] (φ : A →+* C) (hφ : φ.Finite)
    (ε : C →+* A) (he : ∀ a, ε (φ a) = a)
    (h : ∀ c, c - φ (ε c) ∈ (IsLocalRing.maximalIdeal A).map φ) (c : C) : φ (ε c) = c := by
  algebraize [φ]
  have hle : (⊤ : Submodule A C) ≤ LinearMap.range (Algebra.linearMap A C) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
      (IsLocalRing.maximalIdeal_le_jacobson _) fun x _ => ?_
    refine Submodule.mem_sup.2 ⟨φ (ε x), ⟨ε x, rfl⟩, x - φ (ε x), ?_, by ring⟩
    rw [Ideal.smul_top_eq_map]
    exact h x
  obtain ⟨a, rfl⟩ := hle (Submodule.mem_top (x := c))
  exact congrArg φ (he a)

theorem comp_section_eq_id_spec {A : Type} [CommRing A] [IsLocalRing A] {C : CommRingCat.{0}}
    (f : Spec C ⟶ Spec (CommRingCat.of A)) [hf : IsFinite f] (e : Spec (CommRingCat.of A) ⟶ Spec C)
    (he : e ≫ f = 𝟙 _)
    (h : ∀ (T : Scheme.{0}) (t : T ⟶ Sp (IsLocalRing.ResidueField A)) (y : T ⟶ Spec C),
      y ≫ f = t ≫ spMap (IsLocalRing.residue A) → y ≫ f ≫ e = y) : f ≫ e = 𝟙 _ := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  obtain ⟨ε, rfl⟩ := Spec.map_surjective e
  have hφ : φ.hom.Finite := (IsFinite.SpecMap_iff φ).1 hf
  have he' : φ ≫ ε = 𝟙 _ := Spec.map_injective (by rw [Spec.map_comp, he, Spec.map_id])
  let I : Ideal C := (IsLocalRing.maximalIdeal A).map φ.hom
  let τ : IsLocalRing.ResidueField A →+* C ⧸ I :=
    Ideal.Quotient.lift _ ((Ideal.Quotient.mk I).comp φ.hom) fun a ha =>
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ ha)
  have k := h _ (spMap τ) (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) (by
    rw [← Spec.map_comp, ← Spec.map_comp]
    rfl)
  rw [← Spec.map_comp, ← Spec.map_comp] at k
  have k' := Spec.map_injective k
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  ext c
  refine ring_retraction φ.hom hφ ε.hom (fun a => congrArg (fun q => q.hom a) he') (fun x => ?_) c
  exact Ideal.Quotient.eq.1 (congrArg (fun q => q.hom x) k').symm

theorem comp_section_eq_id {A : Type} [CommRing A] [IsLocalRing A] {H : Scheme.{0}}
    (f : H ⟶ Spec (CommRingCat.of A)) [IsFinite f] (e : Spec (CommRingCat.of A) ⟶ H) (he : e ≫ f = 𝟙 _)
    (h : ∀ (T : Scheme.{0}) (t : T ⟶ Sp (IsLocalRing.ResidueField A)) (y : T ⟶ H),
      y ≫ f = t ≫ spMap (IsLocalRing.residue A) → y ≫ f ≫ e = y) : f ≫ e = 𝟙 _ := by
  have : IsAffine H := isAffine_of_isAffineHom f
  have k := comp_section_eq_id_spec (H.isoSpec.inv ≫ f) (e ≫ H.isoSpec.hom) (by simpa using he)
    fun T t y hy => by
      have := h T t (y ≫ H.isoSpec.inv) (by simpa using hy)
      simp only [Category.assoc] at this ⊢
      rw [reassoc_of% this]
      simp
  rw [← cancel_epi H.isoSpec.inv, ← cancel_mono H.isoSpec.hom]
  simpa using k

theorem kTriv_of_closed_fibre : Laws → Laws2 → ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (B : Over (Spec (CommRingCat.of A))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ N : LB B.left, N.IsLB → RelAmple B N → KTriv ((Over.pullback (spMap (IsLocalRing.residue A))).obj B) (N.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))) → KTriv B N := by
  intro hLaws _ A _ _ _ B _ _ hB L hLB hL hk
  have hG := hLaws.globalFns
  obtain ⟨d, -, n, s, hs⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy A B L hLB).1 hL
  have hP : IsProjBy B.hom := ⟨_, isLB_pw hLB _, n, s, hs⟩
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hLB
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.UU.TwistKer.exists_closed_twist_kernel hG A B hB hP L (pw L 0) hLB hO
  have hfin : IsFinite H.hom :=
    GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG A B hB L (pw L 0) hLB hO hL H j hj hH
  have hrep : ∀ (T : Over (Spec (CommRingCat.of A))) (x : T ⟶ B), InK B L x ↔ ∃ y : T ⟶ H, y ≫ j = x :=
    fun T x => (hK _ rfl T x).trans (hH T x)
  have hm : Mono j := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono j.left))
  obtain ⟨e, he⟩ := (hrep _ _).1 (inK_one hLB (𝟙_ _))
  have h := isGrpPullback_pullback B (spMap (IsLocalRing.residue A))
  have hL' : (L.pull (pullback.fst B.hom (spMap (IsLocalRing.residue A)))).IsLB := DVR.linComb_isLB _ hLB _ _
  have key : H.hom ≫ e.left = 𝟙 _ := by
    refine comp_section_eq_id H.hom e.left (Over.w e) fun T t y hy => ?_
    have hdi : (y ≫ j.left) ≫ B.hom = t ≫ spMap (IsLocalRing.residue A) := by
      rw [Category.assoc, Over.w j, hy]
    let x : Over.mk t ⟶ (Over.pullback (spMap (IsLocalRing.residue A))).obj B :=
      Over.homMk (h.1.lift _ _ hdi) (h.1.lift_snd _ _ _)
    let z : Over.mk (t ≫ spMap (IsLocalRing.residue A)) ⟶ H := Over.homMk y hy
    have hz : z ≫ j = pushPt h.1.w x := Over.OverMorphism.ext (h.1.lift_fst _ _ hdi).symm
    have hx : x = 1 := InK.eq_one hk (inK_of_push h hLB hL' (lbIso_self hL') x ((hrep _ _).2 ⟨z, hz⟩))
    have hx' : pushPt h.1.w x = 1 := (congrArg (pushHom h (Over.mk t)) hx).trans (map_one _)
    have h1 : z ≫ toUnit H ≫ e = z := by
      rw [← cancel_mono j, hz, hx', Category.assoc, Category.assoc, he, MonObj.comp_one, MonObj.comp_one]
    have h2 : (toUnit H).left = H.hom := (Category.comp_id _).symm.trans (Over.w (toUnit H))
    exact (congrArg (fun q => y ≫ q ≫ e.left) h2).symm.trans (congrArg (fun q => q.left) h1)
  have hj1 : j = 1 := by
    have h2 : (toUnit H).left = H.hom := (Category.comp_id _).symm.trans (Over.w (toUnit H))
    have h1 : toUnit H ≫ e = 𝟙 H :=
      Over.OverMorphism.ext ((congrArg (fun q => q ≫ e.left) h2).trans key)
    rw [← Category.id_comp j, ← h1, Category.assoc, he, MonObj.comp_one]
  refine kTriv_iff_forall.2 fun T x hxK => ?_
  obtain ⟨y, rfl⟩ := (hrep T x).1 hxK
  rw [hj1, MonObj.comp_one]

end GlobalTheory.KTrivLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyAlgebraisationFormalTowerAmpleStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_algebraisation_formal_tower_ample : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G) (X : Type) [AddCommGroup X] (T : TowerR I P X), RelAmple (T.l 0).Q.B (T.l 0).D.M.L.L → Nonempty T.Alg := by
  first | exact @GlobalTheory.TowerAlg.nonempty_alg | exact GlobalTheory.TowerAlg.nonempty_alg | (intros; apply GlobalTheory.TowerAlg.nonempty_alg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleLocalBase

theorem relAmple_baseChange {S S' : Scheme.{0}} [IsAffine S] {f : S' ⟶ S} {A : Over S} {A' : Over S'}
    {φ : A'.left ⟶ A.left} {L : LB A.left} {L' : LB A'.left} (h : IsPullback φ A'.hom A.hom f)
    (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hA : RelAmple A L) : RelAmple A' L' := by
  obtain ⟨w, hw⟩ := hw
  exact relAmple_pull h hL hL' ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S) (fun _ => trivial) hA

theorem relAmple_of_closed : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (B : Over (Spec (CommRingCat.of R))) (M : LB B.left), Flat B.hom → IsProjBy B.hom → M.IsLB → ∀ (R₀ : Type) [CommRing R₀] [Nontrivial R₀] (g : R →+* R₀), Function.Surjective g → ∀ (Y₀ : Over (Spec (CommRingCat.of R₀))) (b : Y₀.left ⟶ B.left), IsPullback b Y₀.hom B.hom (Spec.map (CommRingCat.ofHom g)) → ∀ N₀ : LB Y₀.left, N₀.IsLB → LBIso N₀ (M.pull b) → RelAmple Y₀ N₀ → RelAmple B M := by
  intro R _ _ _ B M hF hP hM R₀ _ _ g hg Y₀ b hb N₀ hN₀ hiso hA
  have hker : RingHom.ker g ≤ RingHom.ker (IsLocalRing.residue R) := by
    rw [IsLocalRing.ker_residue]
    exact IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top g)
  let g' : R₀ →+* IsLocalRing.ResidueField R :=
    RingHom.liftOfSurjective g hg ⟨IsLocalRing.residue R, hker⟩
  have hg' : g'.comp g = IsLocalRing.residue R := RingHom.liftOfSurjective_comp g hg _
  let k := Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
  have hk : Spec.map (CommRingCat.ofHom g') ≫ Spec.map (CommRingCat.ofHom g) = k := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hg']
  let ψ : pullback B.hom k ⟶ Y₀.left := hb.lift (pullback.fst B.hom k)
    (pullback.snd B.hom k ≫ Spec.map (CommRingCat.ofHom g'))
    (by rw [Category.assoc, hk, pullback.condition])
  have hψ : ψ ≫ b = pullback.fst B.hom k := hb.lift_fst _ _ _
  have hψ' : IsPullback ψ (pullback.snd B.hom k) Y₀.hom (Spec.map (CommRingCat.ofHom g')) := by
    refine IsPullback.of_right ?_ (hb.lift_snd _ _ _) hb
    rw [hψ, hk]
    exact IsPullback.of_hasPullback _ _
  have h₁ : RelAmple ((Over.pullback k).obj B) (M.pull (pullback.fst B.hom k)) :=
    relAmple_baseChange (A' := (Over.pullback k).obj B) hψ' hN₀ (pull_isLB hM _)
      (LBIso.chartPull (Geo.Tor.chartPullPull N₀ ψ ψ rfl)
        (chartPullSame M (fun _ : PUnit => pullback.fst B.hom k) (fun _ => b) (fun _ => 1) ψ
          fun _ => hψ.symm) hiso).symm hA
  obtain ⟨r, hr, h₂⟩ := GlobalTheory.AmpleNear.relAmple_near_fibre R B M hF hP hM _ (IsLocalRing.residue R) (fun y => by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨a, 1, by simp, by simp⟩) h₁
  have hu : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).1 hr
  have htop : PrimeSpectrum.basicOpen r = ⊤ := by
    exact top_le_iff.1 fun p _ => fun hp => p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp hu)
  generalize (PrimeSpectrum.basicOpen r : (Spec (CommRingCat.of R)).Opens) = U at htop h₂
  subst htop
  let j := Scheme.Opens.ι (X := Spec (CommRingCat.of R)) ⊤
  have : IsIso j := inferInstanceAs (IsIso (Spec (CommRingCat.of R)).topIso.hom)
  have : IsAffine (⊤ : (Spec (CommRingCat.of R)).Opens).toScheme := isAffineOpen_top _
  have h₃ : IsPullback (inv (pullback.fst B.hom j)) B.hom (pullback.snd B.hom j) (inv j) :=
    IsPullback.of_horiz_isIso ⟨by
      rw [IsIso.inv_comp_eq, ← Category.assoc, pullback.condition, Category.assoc, IsIso.hom_inv_id,
        Category.comp_id]⟩
  refine relAmple_baseChange (A := (Over.pullback j).obj B) h₃ (pull_isLB hM _) hM ?_ h₂
  exact (LBIso.chartPull (Geo.Tor.chartPullPull _ _ _ rfl) (chartPullSec M _ _ (IsIso.inv_hom_id (pullback.fst B.hom j)))
    ⟨_, idIso_isGen (pull_isLB hM _)⟩).symm

end GlobalTheory.AmpleLocalBase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SectionsPowVeryAmpleAreFormsOfClosedFibreStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sections_pow_veryAmple_are_forms_of_closedFibre : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)), Flat f → ∀ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (K : Type) [Field K] (g₀ : A →+* K), Function.Surjective g₀ → ∀ (X₀ : Scheme.{0}) (π : X₀ ⟶ X) (f₀ : X₀ ⟶ Spec (CommRingCat.of K)), IsPullback π f₀ f (Spec.map (CommRingCat.ofHom g₀)) → ∀ (H₀ : LB X₀) (w₀ : LB.Iso H₀ (H.pull π)) (s₀ : Fin (n + 1) → LB.Sec H₀), H₀.IsLB → w₀.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H₀).ι), (π) z ∈ (H).U k → z ∈ (H₀).U k' → gs (π) z _ ((s j).f k) = (Geo.Tor.gw (w₀) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s₀ j).f k'))) → ∀ t : ℕ, FirstCohomologyVanishes (pw H₀ t) → (∀ σ : LB.Sec (pw H₀ t), ∃ P : MvPolynomial (Fin (n + 1)) K, P.IsHomogeneous t ∧ ∀ k : H₀.ι, σ.f k = MvPolynomial.eval₂Hom (cst (f₀) ((H₀).U k)) (fun j => (s₀ j).f k) (P)) → ∀ σ : LB.Sec (pw H t), ∃ P : MvPolynomial (Fin (n + 1)) A, P.IsHomogeneous t ∧ ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (P) := by
  first | exact @GlobalTheory.Degen.sections_pw_are_forms_of_closed_fibre | exact GlobalTheory.Degen.sections_pw_are_forms_of_closed_fibre | (intros; apply GlobalTheory.Degen.sections_pw_are_forms_of_closed_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianHomExtensionOfLawsStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiAbelianHomExtension_of_laws : Laws → Laws2 → HomExtSt := by
  first | exact @GlobalTheory.LN.homExt_of_laws | exact GlobalTheory.LN.homExt_of_laws | (intros; apply GlobalTheory.LN.homExt_of_laws <;> assumption)
end

