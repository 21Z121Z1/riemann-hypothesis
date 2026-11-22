import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullInvClsOfFibres
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0120
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0121
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModelBirationalGroupLaw
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRigidificationPullbackCompatibleIso
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

noncomputable section
namespace GlobalTheory.Ex.OneGen

section Defs
variable {S : Scheme.{0}} (G : Over S) [GrpObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G)))

def ThG (m : ℕ) {T : Over S} (th : LB.Sec (LPow G L ((1 : ℕ) : ℤ) T)) (x : T ⟶ G) (c : Γ(T.left, ⊤)) : Prop :=
  x ^ (m ^ 2) = 1 ∧ ∃ (t : LB.Sec (LPow G L ((m ^ 2 : ℕ) : ℤ) T))
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T G).left, (snd T G ^ m).left] ![((m ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]))
    (s₁ : LB.Sec (LPow G L ((m ^ 2 : ℕ) : ℤ) T)) (θ : ThetaGrp G L ((m ^ 2 : ℕ) : ℤ) T),
    α.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ α (ptSecT G 1).left) (rigT G L ρ T (((m ^ 2 : ℕ) : ℤ) - 1)) ∧
    IsTwistPull G L (mulT G _ m) (snd _ G ^ m) (lift_snd _ _) ((m ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α th s₁ ∧
    SymLift G L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ ∧ IsActOf G L ((m ^ 2 : ℕ) : ℤ) θ s₁ t ∧
    ∀ z J, Good L z J → VVRank.sv G t (ptSecT G 1).left z J =
      gs (𝟙 _) z ⊤ c * (val (rigT G L ρ T ((m ^ 2 : ℕ) : ℤ)) (𝟙 _) z J).val

def NZ {V : Type} [CommRing V] [IsLocalRing V] (χ : Sp V ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))) : Prop :=
  ∃ g : (Over.mk χ ⊗ G).left, (fst (Over.mk χ) G).left g = closedPoint V ∧ g ∈ nonzeroLocus σ

def UnivBasis {K : Type} [CommRing K] (x : Sp K ⟶ S) (e : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk x))) : Prop :=
  ∀ (K' : Type) [CommRing K'] (i : K →+* K') (x' : Sp K' ⟶ S) (h : spMap i ≫ x = x') (s : SecM G L ((1 : ℕ) : ℤ) (Over.mk x')),
    ∃! c : Γ((Over.mk x').left, ⊤),
      s = c • SecM.ofSec G (VVRank.pullS G _ (Over.homMk (spMap i) h : Over.mk x' ⟶ Over.mk x) e)

variable {G L} in

def IsRigidificationPullbackCompatibleIso {S' : Scheme.{0}} {A : Over S'} [GrpObj A] {φ : A.left ⟶ G.left} {L' : LB A.left} (w : LB.Iso L' (L.pull φ))
    (f : S' ⟶ S) (ρ' : LB.Gen (L'.pull (eSec A))) (ρ : LB.Gen (L.pull (eSec G))) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ S') (z : Z) (J) (J'), Good L z J → Good L' z J' →
    val (L := L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ (r ≫ f) z J =
      wVal w z J J' (r ≫ eSec A) * val (L := L') (φ := fun _ : PUnit => eSec A) (ε := fun _ => 1) ρ' r z J'
end Defs

theorem thG_iff {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) {F : Type} [Field F]
    [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))) (m : ℕ) (th : GlobalTheory.UT.SecA A F 1)
    (x : TFK (R := R) F ⟶ A.A) (c : F) :
    ThG A.A A.L ρ m th x (fnOf c) ↔ x ^ (m ^ 2) = 1 ∧ ∃ t, GlobalTheory.UT.ThC A ρ m th x t c := Iff.rfl

section Move
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)}
  {ρ₀ : LB.Gen (L₀.pull (eSec G))} {ρ₁ : LB.Gen (L₁.pull (eSec A))}

theorem val_rigT (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T₀.left) (z : Z) {J} (hJ : Good L₀ z J) :
    val (rigT G L₀ ρ₀ T₀ k) r z J =
      val (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ T₀.hom) z J ^ k := by
  have hz := hJ.mem (fun _ : Fin 1 => T₀.hom ≫ eSec G) r
  rw [val_of (L := L₀) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) ρ₀ (r ≫ T₀.hom) z J
    (fun _ => J (r ≫ T₀.hom ≫ eSec G)) (fun _ => by rw [Category.assoc])]
  refine (map_zpow _ _ _).trans (congrArg (· ^ k) ?_)
  exact (gm_res r z _ hz _).trans (gm_pull r T₀.hom z _ (rigT_le G L₀ _ hz) _)

include hτ in

theorem IsRigidificationPullbackCompatibleIso.rigT (h : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) (k : ℤ) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'}
    (hJ : Good L₀ z J) (hJ' : Good L₁ z J') : val (rigT G L₀ ρ₀ T₀ k) (r ≫ τ) z J =
      wVal w z J J' (r ≫ T.hom ≫ eSec A) ^ k * val (rigT A L₁ ρ₁ T k) r z J' := by
  rw [val_rigT k _ z hJ, val_rigT k _ z hJ', Category.assoc, hτ, ← Category.assoc, h _ _ z J J' hJ hJ', mul_zpow,
    Category.assoc]

theorem norm_iff (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ} {a : ℤ}
    {α₀ : LB.Gen (LB.LinComb L₀ (K := Fin 2) ![(snd T₀ G).left, (snd T₀ G ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    {α : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![(snd T A).left, (snd T A ^ m).left] ![a, -((1 : ℕ) : ℤ)])}
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
      val α₀ (r ≫ psi hp τ hτ) z J = (wVal w z J J' (r ≫ (snd T A).left) ^ a *
        wVal w z J J' (r ≫ (snd T A ^ m).left) ^ (-((1 : ℕ) : ℤ))) * val α r z J')
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'} (hJ : Good L₀ z J) (hJ' : Good L₁ z J') :
    val α₀ ((r ≫ τ) ≫ (ptSecT G 1).left) z J = val (Out.rigT G L₀ ρ₀ T₀ (a - 1)) (r ≫ τ) z J ↔
      val α (r ≫ (ptSecT A 1).left) z J' = val (Out.rigT A L₁ ρ₁ T (a - 1)) r z J' := by
  rw [hr.rigT τ hτ _ r z hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc,
    H _ _ _ _ _ hJ hJ', Category.assoc, Category.assoc, NormTheta.ptSec_snd, NormTheta.ptSec_snd_pow, ← zpow_add,
    show a + -((1 : ℕ) : ℤ) = a - 1 from rfl, mul_right_inj]

theorem value_iff (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {a : ℤ} {t₀ : LB.Sec (LPow G L₀ a T₀)} {t : LB.Sec (LPow A L₁ a T)}
    (ht : SecRel hp τ hτ w t t₀) {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J J'} (hJ : Good L₀ z J) (hJ' : Good L₁ z J')
    (c : Z.presheaf.stalk z) :
    VVRank.sv G t₀ ((r ≫ τ) ≫ (ptSecT G 1).left) z J = c * (val (Out.rigT G L₀ ρ₀ T₀ a) (r ≫ τ) z J).val ↔
      VVRank.sv A t (r ≫ (ptSecT A 1).left) z J' = c * (val (Out.rigT A L₁ ρ₁ T a) r z J').val := by
  rw [hr.rigT τ hτ _ r z hJ hJ', Category.assoc, ← psi_ptSec hp τ hτ (over_one hp τ hτ), ← Category.assoc,
    ht _ _ _ _ _ hJ hJ', Category.assoc, NormTheta.ptSec_snd, Units.val_mul, mul_left_comm, Units.mul_right_inj]

theorem value_at {a : ℤ} {t : LB.Sec (LPow A L₁ a T)} {c : Γ(T.left, ⊤)} (hL₁ : L₁.IsLB)
    (h : ∀ z J, Good L₁ z J → VVRank.sv A t (ptSecT A 1).left z J =
      gs (𝟙 _) z ⊤ c * (val (Out.rigT A L₁ ρ₁ T a) (𝟙 _) z J).val)
    {Z : Scheme.{0}} (r : Z ⟶ T.left) (z : Z) {J} (hJ : Good L₁ z J) :
    VVRank.sv A t (r ≫ (ptSecT A 1).left) z J = gs r z ⊤ c * (val (Out.rigT A L₁ ρ₁ T a) r z J).val :=
  sv_of_isValueAt (x := (1 : T ⟶ A)) (ρ := Out.rigT A L₁ ρ₁ T a) (isValueAt_of_sv hL₁ fun y J hJ => by
    rw [Category.id_comp]; exact h y J hJ) r z hJ

theorem ThG.move [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {th₀ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) T₀)} (hth : SecRel hp τ hτ w th th₀)
    {c : Γ(T₀.left, ⊤)} (H : ThG G L₀ ρ₀ m th₀ x₀ c) : ThG A L₁ ρ₁ m th x (τ.appTop.hom c) := by
  obtain ⟨-, t₀, α₀, s₀, θ₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ s₀
  obtain ⟨t, ht⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ t₀
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ m) α₀ h₁
  obtain ⟨θ, hθ, hθ'⟩ := symLift_move hp τ hτ hw hL₀ hL₁ hx hn h₄
  refine ⟨hn, t, α, s, θ, hα, corr_of_val hL₁ fun y J' hJ' => ?_,
    isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ m) hα vα hth hs h₃, hθ, hθ' _ _ _ _ hs ht h₅, fun y J' hJ' => ?_⟩
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    rw [val_pull hJ']
    exact (norm_iff hp τ hτ hr vα _ y hJ hJ').1 ((val_pull hJ _ _ _).symm.trans (val_corr hJ h₂ _))
  · obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    have q := (value_iff hp τ hτ hr ht (𝟙 _) y hJ hJ' _).1 (value_at hL₀ h₆ (𝟙 _ ≫ τ) y hJ)
    rw [Category.id_comp (ptSecT A 1).left] at q
    exact q.trans (congrArg (· * _) (gs_pull (𝟙 _) τ y ⊤ trivial c).symm)

theorem ThG.up [IsIso τ] [IsCommMonObj A] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hr : IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀) {m : ℕ}
    {x : T ⟶ A} {x₀ : T₀ ⟶ G} (hx : τ ≫ x₀.left = x.left ≫ φ) (hn : x₀ ^ (m ^ 2) = 1)
    {th : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {th₀ : LB.Sec (LPow G L₀ ((1 : ℕ) : ℤ) T₀)} (hth : SecRel hp τ hτ w th th₀)
    {c : Γ(T.left, ⊤)} (H : ThG A L₁ ρ₁ m th x c) : ThG G L₀ ρ₀ m th₀ x₀ ((inv τ).appTop.hom c) := by
  obtain ⟨h₀, t, α, s, θ, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ s
  obtain ⟨t₀, ht⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ t
  obtain ⟨α₀, hα, vα⟩ := ThetaPtUp.exists_genThrough_up hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ m) α h₁
  obtain ⟨θ₀, hθ, hθ'⟩ := ThetaPtUp.symLift_up hp τ hτ hw hL₀ hL₁ hx h₀ h₄
  refine ⟨hn, t₀, α₀, s₀, θ₀, hα, corr_of_val hL₀ fun y J hJ => ?_,
    ThetaPtUp.isTwistPull_up hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ m) hα vα hth hs h₃, hθ, hθ' _ _ _ _ hs ht h₅,
    fun y J hJ => ?_⟩
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    rw [val_pull hJ, ← IsIso.inv_hom_id τ]
    exact (norm_iff hp τ hτ hr vα _ y hJ hJ').2 ((val_pull hJ' _ _ _).symm.trans (val_corr hJ' h₂ _))
  · obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    have q := (value_iff hp τ hτ hr ht (inv τ) y hJ hJ' _).2 (value_at hL₁ h₆ (inv τ) y hJ')
    rw [IsIso.inv_hom_id, Category.id_comp] at q
    exact q.trans (congrArg (· * _) ((gs_pull (𝟙 _) (inv τ) y ⊤ trivial c).trans (by rw [Category.id_comp])).symm)

theorem ThG.smul (hL₁ : L₁.IsLB) {m : ℕ} {x : T ⟶ A} {th th' : LB.Sec (LPow A L₁ ((1 : ℕ) : ℤ) T)} {a c : Γ(T.left, ⊤)}
    (h : SecM.ofSec A th' = a • SecM.ofSec A th) (H : ThG A L₁ ρ₁ m th x c) : ThG A L₁ ρ₁ m th' x (a * c) := by
  obtain ⟨h₀, t, α, s, θ, h₁, h₂, h₃, h₄, h₅, h₆⟩ := H
  have tw : ∀ {p q : ℤ} {κ : T ⊗ A ⟶ A} {β} (_ : β.IsGen) {u u' : LB.Sec (LPow A L₁ q T)} {v : LB.Sec (LPow A L₁ p T)},
      SecM.ofSec A u' = a • SecM.ofSec A u → IsTwistPull A L₁ (lift (fst T A) κ) κ (lift_snd _ _) p q β u v →
      IsTwistPull A L₁ (lift (fst T A) κ) κ (lift_snd _ _) p q β u' (SecM.toSec A (a • SecM.ofSec A v)) := by
    intro p q κ β hβ u u' v hu hv
    refine VVRank.isTwistPull_of_sv A hL₁ hβ fun y J hJ => ?_
    have e₁ := sv_of_eq_mul (s := u') (t := u) (c := a) (fun j => congrArg (fun q => q.1 j) hu)
      (𝟙 _ ≫ (lift (fst T A) κ).left) y hJ
    have e₂ := sv_of_eq_mul (s := SecM.toSec A (a • SecM.ofSec A v)) (t := v) (c := a) (fun j => rfl) (𝟙 _) y hJ
    rw [e₁, e₂, VVRank.sv_of_isTwistPull A hv (𝟙 _) y hJ, Category.assoc, ← Over.comp_left, lift_fst, mul_left_comm]
  refine ⟨h₀, SecM.toSec A (a • SecM.ofSec A t), α, SecM.toSec A (a • SecM.ofSec A s), θ, h₁, h₂, tw h₁ h h₃, h₄,
    tw θ.isGen rfl h₅, fun y J hJ => ?_⟩
  rw [sv_of_eq_mul (s := SecM.toSec A (a • SecM.ofSec A t)) (t := t) (c := a) (fun j => rfl) _ y hJ, h₆ y J hJ,
    ptSecT_fst, ← _root_.mul_assoc, gs_mul _ y ⊤ trivial]

include hp in

theorem exists_rigidificationPullbackCompatibleIso (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (hρ : ρ₀.IsGen) :
    ∃ ρ₁ : LB.Gen (L₁.pull (eSec A)), ρ₁.IsGen ∧ IsRigidificationPullbackCompatibleIso w f ρ₁ ρ₀ := by
  have e : eSec A ≫ φ = f ≫ eSec G := by
    have := over_one hp (T := baseOver S') (T₀ := baseOver S) f ((Category.comp_id _).trans (Category.id_comp _).symm)
    exact ((Category.id_comp _).symm.trans (Category.assoc _ _ _).symm).trans
      (this.symm.trans (congrArg (f ≫ ·) (Category.id_comp _)))
  obtain ⟨ρ₁, h₁, h₂⟩ := exists_gen_through (φ' := fun _ : PUnit => eSec A) (φ := fun _ : PUnit => eSec G)
    (ε := fun _ => 1) (h := f) hw hL₀ hL₁ (fun _ => e) ρ₀ hρ
  exact ⟨ρ₁, h₁, fun Z r z J J' hJ hJ' => (h₂ Z r z J J' hJ hJ').trans (by rw [Fintype.prod_unique, zpow_one])⟩

end Move

theorem ThG.unique (hLaw : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {ρ : LB.Gen (P.L.pull (eSec P.A))} {m : ℕ} (hm : Odd m) (hu : IsUnit ((m ^ 2 : ℕ) : Γ(S, ⊤))) {T : Over S}
    {th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T)} {x : T ⟶ P.A} {c c' : Γ(T.left, ⊤)} (H : ThG P.A P.L ρ m th x c)
    (H' : ThG P.A P.L ρ m th x c') : c = c' := by
  obtain ⟨hx, t, α, s₁, θ, hα, hn, hs₁, hθ, ht, hc⟩ := H
  obtain ⟨-, t', α', s₁', θ', hα', hn', hs₁', hθ', ht', hc'⟩ := H'
  have hL := P.isLB
  obtain ⟨-, huniq⟩ := hLaw.symLift _ P (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T P.A).left (ptSecT P.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns P.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  obtain rfl : s₁ = s₁' := NormTheta.sec_ext (sec_ext_val hL fun y J hJ =>
    (ThetaLin.sval_of_isTwistPull P.A hs₁ _ y hJ).trans
      (Eq.trans (by rw [ea _ _ y J hJ]) (ThetaLin.sval_of_isTwistPull P.A hs₁' _ y hJ).symm))
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  obtain rfl : t = t' := NormTheta.sec_ext (sec_ext_val hL fun y J hJ =>
    (ThetaLin.sval_of_isTwistPull P.A ht _ y hJ).trans
      (Eq.trans (by rw [val_corr hJ eθ, ept]) (ThetaLin.sval_of_isTwistPull P.A ht' _ y hJ).symm))
  refine fn_ext (V := ⊤) fun y _ => ?_
  obtain ⟨J, hJ⟩ := exists_good' hL y
  exact (Units.mul_left_inj _).1 ((hc y J hJ).symm.trans (hc' y J hJ))

end GlobalTheory.Ex.OneGen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsRingHomComplexOfCountableOfRelations
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

namespace GlobalTheory

theorem isAlgebraic_int_eval₂Hom_of_isAlgebraic {σ : Type} (y : σ → ℂ)
    (hy : ∀ i, IsAlgebraic ℚ (y i)) (c : MvPolynomial σ ℤ) :
    IsAlgebraic ℤ (MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c) := by
  rw [IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ]
  induction c using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.eval₂Hom_C]
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (a : ℚ)
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | mul_X p i hp => rw [map_mul, MvPolynomial.eval₂Hom_X']; exact hp.mul (hy i)

theorem exists_ringHom_complex_of_countable_of_relations :
    ∀ (F : Type) [Field F] [CharZero F] [Countable F] (x : Fin 2 → F) (y : Fin 2 → ℂ), (∀ i, IsAlgebraic ℚ (y i)) → (∀ c : MvPolynomial (Fin 2) ℤ, MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y c = 0 → MvPolynomial.eval₂Hom (Int.castRingHom F) x c = 0) → ∃ f : F →+* ℂ, ∀ i, f (x i) = y i := by
  intro F _ _ _ x y hy hrel
  set ey := MvPolynomial.eval₂Hom (Int.castRingHom ℂ) y with hey
  set ex := MvPolynomial.eval₂Hom (Int.castRingHom F) x with hex
  let R := MvPolynomial (Fin 2) ℤ ⧸ RingHom.ker ey
  have hprime : (RingHom.ker ey).IsPrime := RingHom.ker_isPrime ey
  have : IsDomain R := Ideal.Quotient.isDomain _
  let em : R →+* ℂ := RingHom.kerLift ey
  have hem : Function.Injective em := RingHom.kerLift_injective ey
  let β : R →+* F := Ideal.Quotient.lift _ ex fun c hc => hrel c hc
  have halg : ∀ r : R, IsAlgebraic ℤ r := by
    intro r
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective r
    refine (isAlgebraic_algHom_iff em.toIntAlgHom hem).1 ?_
    exact isAlgebraic_int_eval₂Hom_of_isAlgebraic y hy c
  have hβ : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    refine Ideal.comap_ne_bot_of_algebraic_mem (R := ℤ) (I := RingHom.ker β) h0 hr (halg r) ?_
    rw [eq_bot_iff]
    intro n hn
    rw [Ideal.mem_comap, RingHom.mem_ker] at hn
    simpa using hn
  have hc : Countable R := hβ.countable
  let : Algebra R F := β.toAlgebra
  let : Algebra R ℂ := em.toAlgebra
  have : FaithfulSMul R F := (faithfulSMul_iff_algebraMap_injective R F).2 hβ
  have : FaithfulSMul R ℂ := (faithfulSMul_iff_algebraMap_injective R ℂ).2 hem
  obtain ⟨j⟩ := nonempty_algHom_complex_of_countable R F
  refine ⟨j.toRingHom, fun i => ?_⟩
  have h := j.commutes (Ideal.Quotient.mk _ (MvPolynomial.X i))
  have h1 : algebraMap R F (Ideal.Quotient.mk _ (MvPolynomial.X i)) = x i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom F) x i
  have h2 : algebraMap R ℂ (Ideal.Quotient.mk _ (MvPolynomial.X i)) = y i :=
    MvPolynomial.eval₂Hom_X' (Int.castRingHom ℂ) y i
  rw [h1, h2] at h
  exact h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetricSpreadOutLineBundleAbelianScheme
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenSpread

theorem pull_inv_cls_iff {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB)
    (hL' : L'.IsLB) (e : LBIso L' (L.pull φ)) :
    CechPic.pull (GrpObj.inv : G' ⟶ G').left (CechPic.cls L' hL') = CechPic.cls L' hL' ↔
      LBIso ((L.pull (GrpObj.inv : G ⟶ G).left).pull φ) (L.pull φ) := by
  rw [← CechPic.cls_eq_iff (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _),
    (CechPic.cls_eq_iff hL' (pull_isLB hL _)).2 e, CechPic.cls_pull hL, CechPic.cls_pull (pull_isLB hL _),
    CechPic.cls_pull hL, ← CechPic.pull_comp, ← CechPic.pull_comp, OddDescent.inv_left_comp h]

theorem exists_sym : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → Out.Sym A L₀ → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → Out.Sym G' L' := by
  intro R K _ _ _ _ _ _ G _ _ A _ _ φ L L₀ hG h hL hL₀ e hs
  have := hG.proper
  obtain ⟨a, ha, H⟩ := exists_lbIso G.hom h.1 (pull_isLB hL _) hL
    ((pull_inv_cls_iff h hL hL₀ e).1 (OddDescent.pull_inv_cls_of_sym A hL₀ hs))
  exact ⟨a, ha, fun R' _ g hg G' _ _ π L' h' hL' e' => OddDescent.sym_of_pull_inv_cls G' hL'
    ((pull_inv_cls_iff h' hL hL' e').2 (H R' g hg _ π G'.hom h'.1.w))⟩

end GlobalTheory.GenSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSymmetryHypothesisSpreadFromGenericFibreStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetryHypothesis_spread_from_genericFibre : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ G.left) (L : LB G.left) (L₀ : LB A.left), IsAbelianScheme G → IsGrpPullback A G (spMap (algebraMap R K)) φ → L.IsLB → L₀.IsLB → LBIso L₀ (L.pull φ) → ∀ (w wd : G ⟶ G) (w₀ wd₀ : A ⟶ A), φ ≫ w.left = w₀.left ≫ φ → φ ≫ wd.left = wd₀.left ≫ φ → IsMonHom w₀ → IsMonHom wd₀ → w₀ * wd₀ = 𝟙 A → LBIso L₀ (cubeLB A ![𝟙 A, w₀] L₀) → LBIso (cubeLB A ![fst A A ≫ w₀, snd A A] L₀) (cubeLB A ![fst A A, snd A A ≫ wd₀] L₀) → ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) → ∀ (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'] (π : G'.left ⟶ G.left) (L' : LB G'.left), IsGrpPullback G' G (spMap g) π → L'.IsLB → LBIso L' (L.pull π) → HypS G' L' := by
  first | exact @GlobalTheory.SymSpread.exists_forall_hypS | exact GlobalTheory.SymSpread.exists_forall_hypS | (intros; apply GlobalTheory.SymSpread.exists_forall_hypS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionPairDescentAlgClosedSubfield
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

namespace GlobalTheory.QkDescent

theorem exists_qkExt_of_isAlgClosed : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), D.TauBimult → ∀ (F F' : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F] [Algebra (FractionRing R) F'] (f : F →+* F'), f.comp (algebraMap (FractionRing R) F) = algebraMap (FractionRing R) F' → ∀ k : ℕ, 1 ≤ k → ∀ p' : QkPt D F' k, ∃ p : QkPt D F k, QkExt f p p' := by
  intro hL R _ _ _ D hB F F' _ _ _ _ _ _ _ f hf k hk p'
  have hk' : (k : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  obtain ⟨p, hp⟩ := GlobalTheory.ArcExt.exists_qkExt f hf hB hL hk' p'
  exact ⟨p, (GlobalTheory.TorusExt.qkExt_iff hB f hf p p').2 hp.symm⟩

end GlobalTheory.QkDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorusAbelianQuotientPDivisibleSmoothGroup
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SS.DivSemi

theorem smooth_proj {S : Scheme.{0}} {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G B : Over S} [GrpObj G] [GrpObj B] {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsQuot i q) : Smooth q.left := by
  obtain ⟨hi, hq, hf, hs, ha, hk, -⟩ := h
  have := (H1.torus_dim S X).smooth
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    ((H1.torsor_pullback i q hk).map (Over.forget _)).flip
    ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
  exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this

theorem dim_eq_add {S : Scheme.{0}} (y : S) {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
    {G B : Over S} [GrpObj G] [GrpObj B] {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsQuot i q) {g g' : ℕ}
    (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' B.hom) :
    g = g' + Module.finrank ℤ X := by
  have := smooth_proj h
  obtain ⟨hi, hq, hf, hs, ha, hk, -⟩ := h
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (hk.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

theorem exists_lift_point {k : Type} [Field k] [IsAlgClosed k] {G B : Over (Sp k)} (q : G ⟶ B)
    [LocallyOfFiniteType q.left] [QuasiCompact q.left] [Surjective q.left] (y : 𝟙_ (Over (Sp k)) ⟶ B) :
    ∃ x : 𝟙_ (Over (Sp k)) ⟶ G, x ≫ q = y := by
  let x : Sp k ⟶ B.left := y.left
  have : CompactSpace ↥(pullback q.left x) := QuasiCompact.compactSpace_of_compactSpace (pullback.snd q.left x)
  obtain ⟨p, -⟩ := (pullback.snd q.left x).surjective (default : PrimeSpectrum k)
  obtain ⟨z, -, hz⟩ := isClosed_univ.exists_closed_singleton (X := ↥(pullback q.left x)) ⟨p, trivial⟩
  have e : (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x) ≫ q.left = x := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd q.left x) z hz ≫ pullback.fst q.left x) ?_, ?_⟩
  · rw [← Over.w q, ← Category.assoc]
    exact (congrArg (· ≫ B.hom) e).trans (Over.w y)
  · exact Over.OverMorphism.ext e

theorem isMonHom_id_pow {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (n : ℕ) :
    IsMonHom ((𝟙 B) ^ n : B ⟶ B) := by
  induction n with
  | zero => rw [pow_zero, Hom.one_def]; infer_instance
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 B) ^ n) (𝟙 B) ≫ μ[B]))

theorem exists_torus_abelian_quotient :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) [Fact p.Prime] [CharP k p] (G : Over (Sp k)) [GrpObj G], SmConn G → (∀ y : (𝟙_ (Over (Sp k)) ⟶ G), ∃ x : (𝟙_ (Over (Sp k)) ⟶ G), x ^ p = y) → ∃ (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (B : Over (Sp k)) (_ : GrpObj B) (i : splitTorus (Sp k) X ⟶ G) (q : G ⟶ B), IsQuot i q ∧ IsAbelianScheme B ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ a, SmoothOfRelativeDimension a B.hom ∧ g = a + Module.finrank ℤ X := by
  intro k _ _ p _ _ G _ hG hp
  obtain ⟨X, _, _, _, B, _, i, q, hQ, hmax⟩ := GlobalTheory.T.exists_torusQuotient_no_cocharacter k G hG
  have hsm := smooth_proj hQ
  have hQ' := hQ
  obtain ⟨hi, hq, hf, hs, ha, hk, hB⟩ := hQ'
  have hB' := hB
  obtain ⟨hc, h₁, h₂, h₃, h₄⟩ := hB'
  have hgi := GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom h₁ h₄
  have hint : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hfin : Finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ p = 1} := by
    have e : ∀ x : (𝟙_ (Over (Sp k)) ⟶ B), x ≫ ((𝟙 B) ^ p : B ⟶ B) = x ^ p := fun x => by
      rw [MonObj.comp_pow, Category.comp_id]
    have := GlobalTheory.SS.finite_ker_of_surjective_points k B hB ((𝟙 B) ^ p) (isMonHom_id_pow B p) fun y => by
      obtain ⟨y', rfl⟩ := exists_lift_point q y
      obtain ⟨x, rfl⟩ := hp y'
      exact ⟨x ≫ q, by rw [e, MonObj.pow_comp]⟩
    simpa only [e] using this
  have hpr : IsProper B.hom := by
    refine GlobalTheory.T.isProper_of_powerSeries_arcs_over_algClosed k B h₂ inferInstance h₃ fun a ha => ?_
    by_contra hn
    rcases GlobalTheory.T.infinite_torsion_or_cocharacter_of_arc_at_infinity k p B hB a ha hn with h | ⟨f, hf, hf'⟩
    · exact not_finite {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ p = 1}
    · exact hf' (hmax f hf)
  refine ⟨X, _, ‹_›, ‹_›, B, _, i, q, hQ, ⟨hc, h₁, hpr, h₄⟩, fun g hg => ?_⟩
  obtain ⟨x⟩ : Nonempty B.left := inferInstance
  obtain ⟨a, ha⟩ := exists_dim_of_preconnected B.hom x
  exact ⟨a, ha, dim_eq_add (default : PrimeSpectrum k) hQ hg ha⟩

end GlobalTheory.SS.DivSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeakNeronModelBirationalGroupLawStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_weakNeronModel_birational_groupLaw : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [Algebra R K], SH R K → ∀ (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) → WeakNeron M → ∃ N : Model R A, BirLaw N ∧ ∃ c : ℕ, 1 ≤ c ∧ ∀ a : (𝟙_ (Over (Sp K)) ⟶ A), GenIso N N (transl (a ^ c)).hom := by
  first | exact @GlobalTheory.SS.NeutralModel.exists_birLaw | exact GlobalTheory.SS.NeutralModel.exists_birLaw | (intros; apply GlobalTheory.SS.NeutralModel.exists_birLaw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FullTorsionObjectExistsUniqueModuliPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

theorem GlobalTheory.FullPoint.fullAt_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)
    {K : Type} [Field K] (y : Sp K ⟶ Xo.XF c) (o : Full D K) :
    FullAt Y y o ↔ FullPoint.IsFibre Y.oF y o ∧ ∀ f : KA l →+* K, y ≫ pullback.fst _ _ ≫ Xo.s = spMap f →
      o.ρ = f (baseKA l).ρ ∧ (o.I.ζ l.A : K) = f (baseKA l).ζ :=
  ⟨fun ⟨φ, a, b, c, d, e, f⟩ => ⟨⟨φ, a, b, c, d, e⟩, f⟩, fun ⟨⟨φ, a, b, c, d, e⟩, f⟩ => ⟨φ, a, b, c, d, e, f⟩⟩

theorem GlobalTheory.FullPoint.fullAt_existsUnique_exists_ext : HV → Laws6 → GlobalTheory.LN.UDvrSt → GlobalTheory.LN.HomExtSt → ThetaPtDeterminesSt → EndDeterminedOnTorsionSt → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (W₀ : ValuationSubring ℂ) (Y : Model Xo c (c.V W₀).subtype), ∀ (K : Type) [Field K] [IsAlgClosed K] (bF : c.F →+* K), (∀ o : Full D K, (∀ r : c.F, (r : ℂ) = H.rt0 → o.ρ = bF r) → (∀ z : c.F, (z : ℂ) = zeta l.A → (o.I.ζ l.A : K) = bF z) → ∃! y : Sp K ⟶ Xo.XF c, y ≫ pullback.snd _ _ = spMap bF ∧ FullAt Y y o) ∧ (∀ y : Sp K ⟶ Xo.XF c, ∃ o, FullAt Y y o) ∧ ∀ (K' : Type) [Field K'] (f : K →+* K') y o o', FullAt Y y o → FullExt f o o' → FullAt Y (spMap f ≫ y) o' := by
  intro hv _ _ _ _ _ _ E _ _ _ H D l Xo c W₀ Y K _ _ bF
  refine ⟨fun o hρ hζ => ?_, fun y => ?_, fun K' _ f y o o' h h' => ?_⟩
  · obtain ⟨y, ⟨h₁, h₂⟩, hu⟩ := FullPoint.existsUnique_point hv.1.1 Y bF o hρ hζ
    refine ⟨y, ⟨h₁, (FullPoint.fullAt_iff Y y o).2 ⟨h₂, fun f hf => ?_⟩⟩,
      fun y' h => hu y' ⟨h.1, ((FullPoint.fullAt_iff Y y' o).1 h.2).1⟩⟩
    rw [pullback.condition, ← Category.assoc, h₁, ← spMap_comp] at hf
    obtain rfl := FullPoint.spMap_inj hf
    exact ⟨hρ _ rfl, hζ _ rfl⟩
  · obtain ⟨o, h⟩ := FullPoint.exists_isFibre Y.oF y
    exact ⟨o, (FullPoint.fullAt_iff Y y o).2 h⟩
  · obtain ⟨hρ, hζ, ψ, g₁, g₂, g₃, g₄⟩ := h'
    obtain ⟨h₁, h₂⟩ := (FullPoint.fullAt_iff Y y o).1 h
    refine (FullPoint.fullAt_iff Y _ o').2 ⟨FullPoint.IsFibre.ext f h₁ ψ g₁ g₂ g₃ g₄, fun g hg => ?_⟩
    obtain ⟨j, hj⟩ : ∃ j : KA l →+* K, y ≫ pullback.fst _ _ ≫ Xo.s = spMap j :=
      ⟨(Spec.preimage (y ≫ pullback.fst _ _ ≫ Xo.s)).hom, (Spec.map_preimage _).symm⟩
    rw [Category.assoc, hj, ← spMap_comp] at hg
    obtain rfl := FullPoint.spMap_inj hg
    rw [hρ, hζ _ l.A_pos, (h₂ j hj).1, (h₂ j hj).2]
    exact ⟨rfl, rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralGaugeValuesAreValuationUnitsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralGauge_values_are_valuationUnits : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∀ (N : NumD F) (ν : NumOf D F N), ν.Integral S → (∀ x y u, S.valuation (N.θ x y u : F) = 1) ∧ (∀ x, S.valuation (N.σ x : F) = 1) ∧ (∀ x, N.th x ∈ S) ∧ ((∀ y, PsiUnitOn D y Set.univ) → ∀ χ, S.valuation (N.ψ χ : F) = 1) := by
  first | exact @GlobalTheory.Ex.UnitVal.integral_values | exact GlobalTheory.Ex.UnitVal.integral_values | (intros; apply GlobalTheory.Ex.UnitVal.integral_values <;> assumption)
end

