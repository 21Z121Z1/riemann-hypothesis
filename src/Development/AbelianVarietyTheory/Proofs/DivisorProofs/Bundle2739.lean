import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2635
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapGermFromSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2649
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2676
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2629
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0063
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2637
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetDeterminantOfDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSumPolAV
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MumProd

def tensLB {X : Scheme.{0}} (L M : LB X) : LB X :=
  LB.mk (L.ι × M.ι) (fun p => L.U p.1 ⊓ M.U p.2) fun p q =>
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ L.U p.1 ⊓ L.U q.1) (L.g p.1 q.1) *
    res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
      L.U p.1 ⊓ M.U p.2 ⊓ (L.U q.1 ⊓ M.U q.2) ≤ M.U p.2 ⊓ M.U q.2) (M.g p.2 q.2)

abbrev extLB {X X₁ X₂ : Scheme.{0}} (L₁ : LB X₁) (L₂ : LB X₂) (f₁ : X ⟶ X₁) (f₂ : X ⟶ X₂) : LB X :=
  tensLB (L₁.pull f₁) (L₂.pull f₂)

section MapsAt

variable {Y X X₁ X₂ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}

def extIdx (j₁ : L₁.ι) (j₂ : L₂.ι) : (extLB L₁ L₂ f₁ f₂).ι :=
  ((fun _ => j₁, fun _ => j₂) : (PUnit → L₁.ι) × (PUnit → L₂.ι))

lemma mapsAt₂_le_a (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L (fun _ : PUnit => p) (fun _ => jL) :=
  fun _ hy => Set.mem_iInter.2 fun _ => hy.2

lemma mapsAt₂_le_1 (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L₁ (fun _ : PUnit => p ≫ f₁) (fun _ => j₁) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 := Set.mem_iInter.1 hy.1.1 PUnit.unit
  exact h1

lemma mapsAt₂_le_2 (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι) :
    p ⁻¹ᵁ (LB.div (extLB L₁ L₂ f₁ f₂) L).U (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL) ≤
      LB.wchart L₂ (fun _ : PUnit => p ≫ f₂) (fun _ => j₂) := by
  intro y hy
  refine Set.mem_iInter.2 fun _ => ?_
  have h1 := Set.mem_iInter.1 hy.1.2 PUnit.unit
  exact h1

def MapsAt₂ (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (p : Y ⟶ X) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n)))
    (b₁ : LB.Gen (LB.LinComb L₁ (K := PUnit) (fun _ => p ≫ f₁) (fun _ => n)))
    (b₂ : LB.Gen (LB.LinComb L₂ (K := PUnit) (fun _ => p ≫ f₂) (fun _ => n))) : Prop :=
  ∀ (j₁ : L₁.ι) (j₂ : L₂.ι) (jL : L.ι),
    res (mapsAt₂_le_1 w p j₁ j₂ jL) (b₁.s fun _ => j₁) * res (mapsAt₂_le_2 w p j₁ j₂ jL) (b₂.s fun _ => j₂) =
      (pullU p _ (w.s (extIdx (f₁ := f₁) (f₂ := f₂) j₁ j₂, jL))) ^ n * res (mapsAt₂_le_a w p j₁ j₂ jL) (a.s fun _ => jL)

end MapsAt

structure IsSumPolAV {S : Scheme.{0}} (P P₁ P₂ : PolAV S) (a₁ : P.A ⟶ P₁.A) (a₂ : P.A ⟶ P₂.A) : Prop where
  hom₁ : IsMonHom a₁
  hom₂ : IsMonHom a₂
  lim : IsIso (lift a₁ a₂)
  w : ∃ w : LB.Iso P.L (extLB P₁.L P₂.L a₁.left a₂.left), w.IsGen

variable {R : Type} [CommRing R] [IsDomain R]

structure IsSumDeg (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X)
    (q₂ : D.X →+ D₂.X) : Prop where
  hom₁ : IsMonHom p₁
  hom₂ : IsMonHom p₂
  lim : IsIso (lift p₁ p₂)
  xsum : Function.Bijective (q₁.prod q₂)
  c_pr₁ : ∀ x, D.c x ≫ p₁ = D₁.c (q₁ x)
  c_pr₂ : ∀ x, D.c x ≫ p₂ = D₂.c (q₂ x)
  w : ∃ w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left), w.IsGen ∧
    (∃ b₁ b₂, MapsAt₂ w (eSec D.P.A) 1 D.rig b₁ b₂ ∧ LB.Gen.Corr D₁.P.L _ _ _ _ b₁ D₁.rig ∧
      LB.Gen.Corr D₂.P.L _ _ _ _ b₂ D₂.rig) ∧
    ∀ x, ∃ b₁ b₂, MapsAt₂ w (D.xK x) (-1) (D.psi x) b₁ b₂ ∧ LB.Gen.Corr D₁.P.L _ _ _ _ b₁ (D₁.psi (q₁ x)) ∧
      LB.Gen.Corr D₂.P.L _ _ _ _ b₂ (D₂.psi (q₂ x))

end GlobalTheory.MumProd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricRigidifiedBundleBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSymmetric_rigidifiedBundleBaseChange : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (R : Type) [CommRing R] (ξ : Sp R ⟶ S),
    L.IsSymmetric → (KeyVals.bL L ξ).IsSymmetric := by
  first | exact @GlobalTheory.KeyVals.isSymmetric_bL | exact GlobalTheory.KeyVals.isSymmetric_bL | (intros; apply GlobalTheory.KeyVals.isSymmetric_bL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricTwoCocycleOfAdditiveStructureTorsor
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt

theorem isSymCoc_of_isAdd : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A →
    ∀ (f : Fn1 A) (g : Fn2 A), IsAdd f g → IsSymCoc g := by
  intro R _ A _ hA f g hfg
  have hc : IsCommMonObj A := hA.comm
  intro D _ _
  constructor
  · let k : Fn0 (A ⊗ A) := fun E _ _ w ↦
      g E (w ≫ fst A A) (w ≫ snd A A) - g E (w ≫ snd A A) (w ≫ fst A A)
    have hk : IsCob (whole (A ⊗ A)) (Fn1.zero (A ⊗ A)) k := by
      intro E _ _ E' _ _ φ w _
      have h1 := hfg E E' φ (w ≫ fst A A) (w ≫ snd A A)
      have h2 := hfg E E' φ (w ≫ snd A A) (w ≫ fst A A)
      rw [mul_comm (w ≫ snd A A) (w ≫ fst A A)] at h2
      simp only [k, Fn1.zero, Category.assoc, map_sub]
      linear_combination h2 - h1
    obtain ⟨r, hr⟩ := GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base R (A ⊗ A) Unit (whole (A ⊗ A)) (by simp [whole])
      (GlobalTheory.globalFns_holds (Sp R) (A ⊗ A)
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA)).2 k hk
    intro x y
    have e1 := hr D (lift x y) (sm_whole _)
    have e0 := hr D (lift 1 1) (sm_whole _)
    simp only [k, lift_fst, lift_snd, sub_self] at e0 e1
    exact sub_eq_zero.mp (e1.trans e0.symm)
  · let k : Fn0 (A ⊗ (A ⊗ A)) := fun E _ _ w ↦
      g E (w ≫ snd _ _ ≫ fst A A) (w ≫ snd _ _ ≫ snd A A)
        - g E ((w ≫ fst _ _) * (w ≫ snd _ _ ≫ fst A A)) (w ≫ snd _ _ ≫ snd A A)
        + g E (w ≫ fst _ _) ((w ≫ snd _ _ ≫ fst A A) * (w ≫ snd _ _ ≫ snd A A))
        - g E (w ≫ fst _ _) (w ≫ snd _ _ ≫ fst A A)
    have hk : IsCob (whole (A ⊗ (A ⊗ A))) (Fn1.zero _) k := by
      intro E _ _ E' _ _ φ w _
      have h1 := hfg E E' φ (w ≫ snd _ _ ≫ fst A A) (w ≫ snd _ _ ≫ snd A A)
      have h2 := hfg E E' φ ((w ≫ fst _ _) * (w ≫ snd _ _ ≫ fst A A)) (w ≫ snd _ _ ≫ snd A A)
      have h3 := hfg E E' φ (w ≫ fst _ _) ((w ≫ snd _ _ ≫ fst A A) * (w ≫ snd _ _ ≫ snd A A))
      have h4 := hfg E E' φ (w ≫ fst _ _) (w ≫ snd _ _ ≫ fst A A)
      rw [_root_.mul_assoc] at h2
      simp only [MonObj.comp_mul] at h2 h3
      simp only [k, Fn1.zero, Category.assoc, map_sub, map_add, MonObj.comp_mul]
      linear_combination h2 - h1 - h3 + h4
    obtain ⟨r, hr⟩ := GlobalTheory.T.natural_pointwiseCochain_const_of_globalSections_base R (A ⊗ (A ⊗ A)) Unit (whole _) (by simp [whole])
      (GlobalTheory.globalFns_holds (Sp R) (A ⊗ (A ⊗ A))
        (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A (A ⊗ A) hA
          (ReciprocityTheory.ChartRestriction.G.Geo.Tor.AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA))).2 k hk
    intro x y z
    have e1 := hr D (lift x (lift y z)) (sm_whole _)
    have e0 := hr D (lift 1 (lift 1 1)) (sm_whole _)
    simp only [k, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, _root_.mul_one, sub_self, add_sub_cancel_right,
      sub_add_cancel] at e0 e1
    rw [← e0] at e1
    exact e1

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentOfFibrePullbackTangentAtChartStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTangent_of_fibre_pullback_tangent_at_chart : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) (U : X.affineOpens) {n : ℕ} (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (hv : ∀ a, IsTanAtG t (LogKS.chart U) (v a)) {K : Type} [Field K] (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (u : Fin n → (epsR K ⟶ A)) (hm : IsGrpPullback A t.G x0 m) (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (ev x0 U.1 hU)) ≫ v a) (a : Fin n), IsTangent (u a) := by
  first | exact @GlobalTheory.CechKS.isTangent_of_fibre | exact GlobalTheory.CechKS.isTangent_of_fibre | (intros; apply GlobalTheory.CechKS.isTangent_of_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtFibreSpreadModelAtFieldPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaPt_fibre_spread_model_at_fieldPoint : ∀ (F Ω T : Type) [Field F] [IsAlgClosed F] [CharZero F] [Field Ω] [IsAlgClosed Ω] [CommRing T] [IsDomain T] [Algebra F T] (em : F →+* Ω) (jT : T →+* Ω) (t : T →ₐ[F] F), Algebra.FiniteType F T → Function.Injective jT → jT.comp (algebraMap F T) = em → ∀ (A : PolAV (Sp Ω)) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap jT) φ → LBIso A.L (P.L.pull φ) → ∀ (m : ℕ) (I : Type) (x : I → (baseOver (Sp Ω) ⟶ A.A)) (y : I → (baseOver (Sp T) ⟶ P.A)) (v : I → F), Odd m → 3 ≤ m → (∀ i, (x i).left ≫ φ = spMap jT ≫ (y i).left) → (∀ i, y i ^ (m ^ 2) = 1) → (∀ z : Over.mk (spMap t.toRingHom) ⟶ P.A, z ^ m = 1 → ∃ i, ((Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) ^ m = z) → IsThetaPt A m x (fun i => (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom (em (v i))) → IsThetaPt P m (fun i => (Over.homMk (spMap t.toRingHom) : Over.mk (spMap t.toRingHom) ⟶ baseOver (Sp T)) ≫ y i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (v i)) := by
  first | exact @GlobalTheory.Mum.isThetaPt_fibre | exact GlobalTheory.Mum.isThetaPt_fibre | (intros; apply GlobalTheory.Mum.isThetaPt_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaPtOfMap
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.ThetaDown

theorem isThetaPt_of_map : ∀ (B : Scheme.{0}) [IsLocallyNoetherian B] (P : PolAV B) (K C : Type) [Field K] [Field C] (j : K →+* C) (s : Sp K ⟶ B) (x : Sp C ⟶ B) (hx : spMap j ≫ s = x) (k : ℕ) (J : Type) (p : J → (Over.mk s ⟶ P.A)) (w : J → K), (∀ i, p i ^ k ^ 2 = 1) → IsThetaPt P k (fun i => (Over.homMk (spMap j) hx : Over.mk x ⟶ Over.mk s) ≫ p i) (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (j (w i))) → IsThetaPt P k p (fun i => (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (w i)) := by
  intro B _ P K C _ _ j s x hx k J p w hp H
  have h₁ : Laws := GlobalTheory.firstFiveLaws.1
  have h₂ : Laws2 := GlobalTheory.firstFiveLaws.2.1
  have hk : Odd k := H.1
  let eC : Γ(Sp C, ⊤) ≃+* C := (Scheme.ΓSpecIso (CommRingCat.of C)).commRingCatIsoToRingEquiv
  have hkC : (k : C) ≠ 0 := by
    have := H.2.1.map eC.toRingHom
    rw [map_natCast] at this
    exact this.ne_zero
  have hkK : IsUnit (k : K) := IsUnit.mk0 _ fun h0 => hkC (by rw [← map_natCast j, h0, map_zero])
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.Ex.Specialise.exists_isThetaPt_local h₁ h₂ P s hk hkK p hp
  have hC := GlobalTheory.Ex.Specialise.isThetaPt_map h₂ P j hx hw₀
  haveI : IsLocalRing Γ((Over.mk x).left, ⊤) := eC.symm.isLocalRing
  obtain ⟨u, hu⟩ := GlobalTheory.ThetaUniq.exists_unit_over h₁.globalFns P hk
    (GlobalTheory.ThetaUniq.isThetaPtOver_of_local _ x hC) (GlobalTheory.ThetaUniq.isThetaPtOver_of_local _ x H)
  set c : C := eC (u : Γ((Over.mk x).left, ⊤)) with hcdef
  have hc : ∀ i, j (w i) = c * j (w₀ i) := fun i => by
    have q := (congrArg eC (hu i)).trans (map_mul eC _ _)
    exact (eC.apply_symm_apply (j (w i))).symm.trans (q.trans (congrArg (_ * ·) (eC.apply_symm_apply (j (w₀ i)))))
  have hu0 : c ≠ 0 := fun h0 => (u.isUnit.map eC.toRingHom).ne_zero h0
  by_cases hz : ∀ i, w₀ i = 0
  · have e : w = w₀ := funext fun i => j.injective (by rw [hc, hz, map_zero, MulZeroClass.mul_zero])
    subst e
    exact hw₀
  · push_neg at hz
    obtain ⟨i₀, hi₀⟩ := hz
    have hd : j (w i₀ / w₀ i₀) = c := by
      rw [map_div₀, hc, mul_div_assoc, div_self ((map_ne_zero j).2 hi₀), _root_.mul_one]
    have hd0 : w i₀ / w₀ i₀ ≠ 0 := fun h0 => hu0 (by rw [← hd, h0, map_zero])
    have e : ∀ i, w i = (w i₀ / w₀ i₀) * w₀ i := fun i => j.injective (by rw [map_mul, hd, hc])
    have := GlobalTheory.Ex.Specialise.isThetaPt_mul P hw₀ hd0
    convert this using 2 with i
    rw [e i]

end GlobalTheory.Mum.ThetaDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsThetaTermsOfMulIndexZeroTermEqOneStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isThetaTerms_of_mul_index_zero_term_eq_one : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] (D : DegPre V₁) (N₁ : ℕ) (X C : Type) [AddCommGroup X] (e : X ≃+ D.X) (T : X → C → V₁) (v : V₁) (c₀ : C), IsThetaTerms₀ D N₁ e T → T 0 c₀ * v = 1 → IsThetaTerms D N₁ e (fun mu c => T mu c * v) := by
  first | exact @GlobalTheory.Poinc.Sep.isThetaTerms_of_mul_eq_one | exact GlobalTheory.Poinc.Sep.isThetaTerms_of_mul_eq_one | (intros; apply GlobalTheory.Poinc.Sep.isThetaTerms_of_mul_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranscendenceBasisResidueFieldUniformiserConsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTranscendenceBasis_residueField_uniformiser_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K) (S : Place cL) (ψ : S.ring →+* K),
  Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) →
  ∀ (F : Place cK) (m : ℕ) (π : K) (y : Fin m → K), (∃ x : Fin (m + 2) → L, TrBasis cL x) →
  F.ord π = 1 → (∀ i, y i ∈ F.ring) →
  (∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 → MvPolynomial.eval₂ cK y P ≠ 0 ∧ (MvPolynomial.eval₂ cK y P)⁻¹ ∈ F.ring) →
  TrBasis cK (Fin.cons π y : Fin (m + 1) → K) := by
  first | exact @GlobalTheory.FieldPair.ResidueTrBasis.trBasis_cons | exact GlobalTheory.FieldPair.ResidueTrBasis.trBasis_cons | (intros; apply GlobalTheory.FieldPair.ResidueTrBasis.trBasis_cons <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslateOfTangentVectorFibreToGroupScheme
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
open GlobalTheory.CechKS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS

section

open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_mul_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {m : G'.left ⟶ G.left} (hm : IsGrpPullback G' G f m) (T : Over S') (x y : T ⟶ G')
    (s : T.left ⟶ S) (hs : s = T.hom ≫ f) :
    ∃ x₀ y₀ : Over.mk s ⟶ G, x₀.left = x.left ≫ m ∧ y₀.left = y.left ≫ m ∧ (x₀ * y₀).left = (x * y).left ≫ m := by
  subst hs
  have e : ∀ z : T ⟶ G', (z.left ≫ m) ≫ G.hom = T.hom ≫ f := fun z ↦ by
    rw [Category.assoc, hm.1.w, ← Category.assoc, Over.w z]
  exact ⟨Over.homMk (x.left ≫ m) (e x), Over.homMk (y.left ≫ m) (e y), rfl, rfl, hm.2 T x y _ _ rfl rfl⟩

end

theorem IsTransl.isTranslate_comp : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} (t : SAB H X) {K : Type} [Field K] (x0 : Sp K ⟶ X) (A : Over (Sp K)) [GrpObj A] (m : A.left ⟶ t.G.left) (hm : IsGrpPullback A t.G x0 m) {R : Type} [CommRing R] (ψ : R →+* K) (v : Sp (DualNumber R) ⟶ t.G.left) (u : epsR K ⟶ A) (hu : u.left ≫ m = spMap (dualMap ψ) ≫ v) {B : Type} [CommRing B] (φ : K →+* B) (x : Sp B ⟶ A.left) (hx : x ≫ A.hom = spMap φ) (w : Sp (DualNumber B) ⟶ A.left) (hw : IsTransl φ x u w), LogKS.IsTranslate t (φ.comp ψ) (x ≫ m) v (w ≫ m) := by
  intro E _ _ _ H X t K _ x0 A _ m hm R _ ψ v u hu B _ φ x hx w hw
  obtain ⟨x₁, v₁, a, b, rfl⟩ := hw
  have sc : ∀ {P Q T : Type} [CommRing P] [CommRing Q] [CommRing T] (f : P →+* Q) (g : Q →+* T),
      spMap g ≫ spMap f = spMap (g.comp f) := fun f g ↦ by
    unfold spMap
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have dc : (dualMap φ).comp (dualMap ψ) = dualMap (φ.comp ψ) :=
    RingHom.ext fun c ↦ by ext <;> simp [dualMap]
  obtain ⟨x₀, y₀, h₁, h₂, h₃⟩ := exists_mul_of_isGrpPullback hm _ x₁ v₁
    (spMap (algebraMap B (DualNumber B)) ≫ (x ≫ m) ≫ t.G.hom) (by
      change _ = spMap ((algebraMap B (DualNumber B)).comp φ) ≫ x0
      rw [Category.assoc, hm.1.w, ← Category.assoc x, hx, ← Category.assoc, sc])
  refine ⟨x₀, y₀, ?_, ?_, h₃⟩
  · rw [h₁, a]; exact Category.assoc _ _ _
  · rw [h₂, b, ← dc, ← sc (dualMap ψ) (dualMap φ)]
    refine (Category.assoc _ _ _).trans ?_
    rw [hu]; exact (Category.assoc (spMap (dualMap φ)) (spMap (dualMap ψ)) v).symm

end GlobalTheory.CechKS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitOfBasicOpenTop
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.RescaleLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_of_basicOpen_top {Y : Scheme.{0}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) : IsUnit s :=
  Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Y.mem_basicOpen _ x hx).1 (h.ge hx)

abbrev fnSp (A : Type) [CommRing A] : A →+* Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem appTop_comp_spMap {R₀ A : Type} [CommRing R₀] [CommRing A] (α : R₀ →+* A) {Z : Scheme.{0}}
    (s : Z ⟶ Sp A) (r : R₀) : (s ≫ spMap α).appTop.hom (fnSp R₀ r) = s.appTop.hom (fnSp A (α r)) := by
  have nat := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom α))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg s.appTop.hom nat.symm

def fnOn {R₀ : Type} [CommRing R₀] (W : (Sp R₀).Opens) : R₀ →+* Γ(W.toScheme, ⊤) :=
  W.ι.appTop.hom.comp (fnSp R₀)

theorem appTop_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) :
    t.appTop.hom (fnOn W r) = s.appTop.hom (fnSp A (α r)) := by
  have e : t.appTop.hom (fnOn W r) = (t ≫ W.ι).appTop.hom (fnSp R₀ r) := by
    rw [Scheme.Hom.comp_appTop]; rfl
  rw [e, h, appTop_comp_spMap]

theorem gm_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) (u : Γ(W.toScheme, ⊤)ˣ) (v : Aˣ)
    (hu : (u : Γ(W.toScheme, ⊤)) = fnOn W r) (hv : (v : A) = α r) (z : Z) :
    gm t z ⊤ u = gm s z ⊤ (unitOn v) := by
  rw [GlobalTheory.UU.gm_top t, GlobalTheory.UU.gm_top s]
  congr 1
  apply Units.ext
  show t.appTop.hom (u : Γ(W.toScheme, ⊤)) = s.appTop.hom (fnSp A (v : A))
  rw [hu, hv, appTop_fnOn W α t s h r]

theorem isUnit_fnOn {R₀ : Type} [CommRing R₀] (f r : R₀) (N : ℕ) (hr : r ∣ f ^ N) :
    IsUnit (fnOn ((Sp R₀).basicOpen (fnSp R₀ f)) r) := by
  set W := (Sp R₀).basicOpen (fnSp R₀ f)
  have hf : IsUnit (fnOn W f) := isUnit_of_basicOpen_top _ (by
    have e := Scheme.preimage_basicOpen W.ι (fnSp R₀ f)
    rw [Scheme.Opens.ι_preimage_self] at e
    exact e.symm)
  exact isUnit_of_dvd_unit (map_dvd (fnOn W) hr |>.trans (by rw [map_pow])) (hf.pow N)

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

theorem exists_psiOn_rescale {R₀ : Type} [CommRing R₀] [IsDomain R₀] (D₁ : DegPre R₀) (κ₀ : D₁.X → (FractionRing R₀)ˣ)
    {W W' : (Sp R₀).Opens} (ψ : PsiOn D₁ W) (hle : W' ≤ W) (u : D₁.X → Γ(W'.toScheme, ⊤)ˣ) (r : D₁.X → R₀)
    (hu : ∀ y, (u y : Γ(W'.toScheme, ⊤)) = fnOn W' (r y)) (hr : ∀ y, algebraMap R₀ (FractionRing R₀) (r y) = κ₀ y) :
    ∃ ψW : PsiOn (GlobalTheory.PolDeg.rescale D₁ κ₀) W', ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J,
      Good D₁.P.L z J → val (ψW.psi y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ (Sp R₀).homOfLE hle) z J := by
  let m : W'.toScheme ⟶ W.toScheme := (Sp R₀).homOfLE hle
  have hm : m ≫ W.ι = W'.ι := Scheme.homOfLE_ι _ _
  have hφ : ∀ y : D₁.X, m ≫ (toUnit (TW W) ≫ D₁.c y).left = (toUnit (TW W') ≫ D₁.c y).left := fun y => by
    show m ≫ W.ι ≫ (D₁.c y).left = W'.ι ≫ (D₁.c y).left
    rw [← Category.assoc, hm]
  choose b hb vb using fun y : D₁.X => exists_gen D₁.P.isLB (K' := PUnit)
    (φ' := fun _ => (toUnit (TW W') ≫ D₁.c y).left) (ε' := fun _ => -1)
    (fun U _ k => Finset.prod_congr rfl fun _ _ => congrArg (fun q => k q ^ (-1 : ℤ)) (hφ y))
    (GlobalTheory.UU.scaleGen (u y) (LB.pullGen D₁.P.L _ _ (ψ.psi y) m))
    (GlobalTheory.UU.scaleGen_isGen _ (DVR.pullGen_isGen _ _ _ _ (ψ.psi_gen y) m))
  have ev : ∀ (y : D₁.X) {Z : Scheme.{0}} (t : Z ⟶ W'.toScheme) (z : Z) J, Good D₁.P.L z J →
      val (b y) t z J = gm t z ⊤ (u y) * val (ψ.psi y) (t ≫ m) z J := fun y Z t z J hJ =>
    (vb y Z t z J hJ).trans ((GlobalTheory.UU.val_scaleGen _ _ _ hJ).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _)))
  refine ⟨{ psi := b, psi_gen := hb, psi_eq := fun y => corr_of_val D₁.P.isLB fun z J hJ => ?_ }, ev⟩
  refine (val_pull hJ _ _ _).trans ((ev y _ z J hJ).trans (Eq.trans ?_ (val_pull hJ _ _ _).symm))
  refine (congrArg₂ (· * ·) ?_ ?_).trans (GlobalTheory.UU.val_scaleGen (unitOn (κ₀ y)) (D₁.psi y) _ hJ).symm
  · refine gm_fnOn W' (algebraMap R₀ (FractionRing R₀)) _ _ ?_ (r y) _ _ (hu y) (hr y).symm z
    rw [Category.id_comp, Category.id_comp, morphismRestrict_ι]
  · refine GlobalTheory.ArcSpecialise.psiOn_generic ψ y _ _ ?_ hJ
    rw [Category.assoc, hm, Category.id_comp, Category.id_comp, morphismRestrict_ι]

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

end GlobalTheory.RescaleLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacquetFiniteLengthStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_lift_de_rham_unique : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (κ : DividedPowers I), IsNilDP κ →
    ∀ (π : R →+* R₀), Function.Surjective π → RingHom.ker π = I →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A : Over (Sp R)) [GrpObj A] (i : A₀.left ⟶ A.left),
      IsGrpPullback A₀ A (spMap π) i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (l : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left), IsSquare i l →
    ∀ (L : LB A.left), L.IsLB → Out.RelAmple A L →
    ∀ (P₀ Q₀ S₀ : LB (A₀ ⊗ A₀).left), P₀.IsLB → Q₀.IsLB → S₀.IsLB → LBIso Q₀ (LB.div S₀ P₀) →
    ∀ (P Q S : LB (A ⊗ A).left), P.IsLB → Q.IsLB → S.IsLB →
      HasGen (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      HasGen (S.pull (lift (1 : A ⟶ A) (𝟙 A)).left) → HasGen (S.pull (lift (𝟙 A) (1 : A ⟶ A)).left) →
      LBIso (P.pull l) P₀ → LBIso (Q.pull l) Q₀ → LBIso (S.pull l) S₀ → LBIso Q (LB.div S P) := by
  first | exact @GlobalTheory.BirigidLift.lift_div | exact GlobalTheory.BirigidLift.lift_div | (intros; apply GlobalTheory.BirigidLift.lift_div <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetDeterminantOfDeRhamStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jet_determinant_of_de_rham : GlobalTheory.Published.AbelianDeRham → JetCalc → JetDet := by
  first | exact @GlobalTheory.LatJet.An.Det.jetDet | exact GlobalTheory.LatJet.An.Det.jetDet | (intros; apply GlobalTheory.LatJet.An.Det.jetDet <;> assumption)
end

