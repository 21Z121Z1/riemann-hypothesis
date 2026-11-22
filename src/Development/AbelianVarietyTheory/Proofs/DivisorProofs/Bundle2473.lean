import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0055
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2387
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2418

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCrystallineFormLiftDifferenceEqSum
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechKS.FormLocal

open KaehlerDifferential
attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

section Alg

variable {R B C : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  {J : Ideal C}

theorem mul_eq_zero_of_sq (hJ : J ^ 2 = 0) {a b : C} (ha : a ∈ J) (hb : b ∈ J) : a * b = 0 := by
  have := Ideal.mul_mem_mul ha hb
  rwa [← pow_two, hJ, Ideal.zero_eq_bot, Ideal.mem_bot] at this

def diffDer (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J) :
    letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
    Derivation R B C :=
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  { toFun := fun b ↦ ρ₁ b - ρ₂ b
    map_add' := fun a b ↦ by simp only [map_add]; ring
    map_smul' := fun r b ↦ by
      simp only [map_smul, RingHom.id_apply, smul_sub]
    map_one_eq_zero' := by simp
    leibniz' := fun a b ↦ by
      change ρ₁ (a * b) - ρ₂ (a * b) = ρ₂ a * (ρ₁ b - ρ₂ b) + ρ₂ b * (ρ₁ a - ρ₂ a)
      have h0 := mul_eq_zero_of_sq hJ (hd a) (hd b)
      simp only [map_mul]
      linear_combination h0 }

def diffLam (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J) : Ω[B⁄R] →+ C :=
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  ((diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential).toAddMonoidHom

variable (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J)

theorem diffLam_smul (b : B) (m : Ω[B⁄R]) :
    diffLam hJ ρ₁ ρ₂ hd (b • m) = ρ₂ b * diffLam hJ ρ₁ ρ₂ hd m := by
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  exact ((diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential).map_smul b m

theorem diffLam_D (t : B) : diffLam hJ ρ₁ ρ₂ hd (D R B t) = ρ₁ t - ρ₂ t := by
  letI : Algebra B C := (ρ₂ : B →+* C).toAlgebra
  haveI : IsScalarTower R B C := IsScalarTower.of_algebraMap_eq fun r ↦ (ρ₂.commutes r).symm
  exact (diffDer hJ ρ₁ ρ₂ hd).liftKaehlerDifferential_comp_D t

theorem diffLam_mem (m : Ω[B⁄R]) : diffLam hJ ρ₁ ρ₂ hd m ∈ J := by
  induction m using GlobalTheory.CechDR.ind1 with
  | h b c => rw [diffLam_smul, diffLam_D]; exact J.mul_mem_left _ (hd c)
  | h0 => rw [map_zero]; exact J.zero_mem
  | ha x y hx hy => rw [map_add]; exact J.add_mem hx hy

end Alg

section Alg2

variable {R B C : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing C] [Algebra R C]
  {J : Ideal C} (hJ : J ^ 2 = 0) (ρ₁ ρ₂ : B →ₐ[R] C) (hd : ∀ b, ρ₁ b - ρ₂ b ∈ J)

def diagLift : TrivSqZeroExt B Ω[B⁄R] →ₐ[R] C where
  toFun c := ρ₂ c.fst + diffLam hJ ρ₁ ρ₂ hd c.snd
  map_one' := by simp
  map_zero' := by simp
  map_add' a b := by simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add, map_add]; ring
  map_mul' a b := by
    have h0 := mul_eq_zero_of_sq hJ (diffLam_mem hJ ρ₁ ρ₂ hd a.snd) (diffLam_mem hJ ρ₁ ρ₂ hd b.snd)
    have e : (MulOpposite.op b.fst • a.snd : Ω[B⁄R]) = b.fst • a.snd := rfl
    simp only [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, map_mul, map_add, e, diffLam_smul]
    linear_combination -h0
  commutes' r := by
    simp [TrivSqZeroExt.algebraMap_eq_inl']

theorem diagLift_apply (c : TrivSqZeroExt B Ω[B⁄R]) :
    diagLift hJ ρ₁ ρ₂ hd c = ρ₂ c.fst + diffLam hJ ρ₁ ρ₂ hd c.snd := rfl

theorem diagLift_inl (b : B) : diagLift hJ ρ₁ ρ₂ hd (TrivSqZeroExt.inl b) = ρ₂ b := by
  simp [diagLift_apply]

theorem diagLift_diagSec (b : B) : diagLift hJ ρ₁ ρ₂ hd (diagSec R B b) = ρ₁ b := by
  rw [diagLift_apply, fst_derSec, snd_derSec, diffLam_D]; ring

theorem diagLift_sub_mem (c : TrivSqZeroExt B Ω[B⁄R]) : diagLift hJ ρ₁ ρ₂ hd c - ρ₂ c.fst ∈ J := by
  rw [diagLift_apply, add_sub_cancel_left]; exact diffLam_mem hJ ρ₁ ρ₂ hd _

end Alg2

section Repr

variable {R B : Type} [CommRing R] [CommRing B] [Algebra R B]

theorem exists_sum_smul_D (m : Ω[B⁄R]) : ∃ (n : ℕ) (r t : Fin n → B), m = ∑ k, r k • D R B (t k) := by
  induction m using GlobalTheory.CechDR.ind1 with
  | h b c => exact ⟨1, fun _ ↦ b, fun _ ↦ c, by simp⟩
  | h0 => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | ha x y hx hy =>
    obtain ⟨n, r, t, rfl⟩ := hx
    obtain ⟨n', r', t', rfl⟩ := hy
    refine ⟨n + n', Fin.append r r', Fin.append t t', ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

end Repr

section Geo

variable {R : Type} [CommRing R] {X : Scheme.{0}} {s : X ⟶ Sp R} {U : X.Opens}

def valHom {C : Type} [CommRing C] [Algebra R C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U)
    (hs : y ≫ s = spMap (algebraMap R C)) : CechDR.Sec s U →ₐ[R] C :=
  { (GlobalTheory.Points.valMap y U hy).hom with
    commutes' := fun r ↦ by
      have e1 := GlobalTheory.Points.valR_appLE y s (U := ⊤) (V := U) le_top hy
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
      rw [hs, GlobalTheory.Points.valR_specMap, GlobalTheory.Points.valR_eq y U hy] at e1
      exact e1 }

theorem valR_eq_valHom {C : Type} [CommRing C] [Algebra R C] (y : Sp C ⟶ X) (hy : ⊤ ≤ y ⁻¹ᵁ U)
    (hs : y ≫ s = spMap (algebraMap R C)) (f : Γ(X, U)) : valR y U f = valHom y hy hs f :=
  GlobalTheory.Points.valR_eq y U hy f

theorem valHom_pt {C : Type} [CommRing C] [Algebra R C] (hU : IsAffineOpen U) (y : Sp C ⟶ X)
    (hy : ⊤ ≤ y ⁻¹ᵁ U) (hs : y ≫ s = spMap (algebraMap R C)) :
    spMap (valHom y hy hs : CechDR.Sec s U →+* C) ≫ CechDR.affPt s ⟨U, hU⟩ = y :=
  GlobalTheory.Points.specMap_valMap_fromSpec hU y hy

theorem ringHom_ext_affPt {C : Type} [CommRing C] (hU : IsAffineOpen U) {a b : CechDR.Sec s U →+* C}
    (h : spMap a ≫ CechDR.affPt s ⟨U, hU⟩ = spMap b ≫ CechDR.affPt s ⟨U, hU⟩) : a = b := by
  have h1 : spMap a = spMap b := (cancel_mono hU.fromSpec).1 h
  have h2 := Spec.map_injective h1
  exact congrArg CommRingCat.Hom.hom h2

def diagPr (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X) (hx : x ≫ s = spMap (algebraMap R B)) :
    (diagExt R B).thick x hx ⟶ Thick.triv B x hx where
  φ := (diagExt R B).π
  φ₀ := RingHom.id B
  comm _ := rfl
  dp := (DividedPowers.isDPMorphism_iff _ _ _).2 ⟨Ideal.map_le_iff_le_comap.2 fun a ha ↦ ha,
    fun n hn a ha ↦ by
      have ha' : ((diagExt R B).π : TrivSqZeroExt B Ω[B⁄R] →+* B) a = 0 := ha
      have hm := (divided₂ (diagExt R B).sq).dpow_mem hn ha
      have hm' : ((diagExt R B).π : TrivSqZeroExt B Ω[B⁄R] →+* B) ((divided₂ (diagExt R B).sq).dpow n a) = 0 := hm
      rw [hm', ha', DividedPowers.dpow_eval_zero _ hn]⟩
  pt := by rw [spMap_id, Category.id_comp]

theorem fst_ev_secHom (ω : Form s) (B : Type) [CommRing B] [Algebra R B] (x : Sp B ⟶ X)
    (hx : x ≫ s = spMap (algebraMap R B)) (j : B →ₐ[R] TrivSqZeroExt B Ω[B⁄R])
    (hj : ∀ b, (j b).fst = b) :
    (ev ω.1 ((diagExt R B).secHom hx j hj)).fst = - ev ω.1 (diagPr B x hx) := by
  have h0 : ev ω.1 ((diagExt R B).secHom hx j hj ≫ diagPr B x hx) = 0 := ω.2 _ rfl rfl
  rw [ev_comp] at h0
  exact eq_neg_of_add_eq_zero_left h0

end Geo

theorem ev_idLift_sub_eq_sum : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (ω : Form s) (U : X.Opens), IsAffineOpen U → ∃ (n : ℕ) (r t : Fin n → Γ(X, U)), ∀ (T : Thick (dp0 R) s) (hJ : T.J ^ 2 = 0), T.δ = divided₂ hJ → ∀ (y₁ y₂ : Sp T.B ⟶ X) (h₁ : y₁ ≫ s = spMap (algebraMap R T.B)) (h₂ : y₂ ≫ s = spMap (algebraMap R T.B)) (e₁ : spMap T.π ≫ y₁ = T.x) (e₂ : spMap T.π ≫ y₂ = T.x), ⊤ ≤ y₁ ⁻¹ᵁ U → ⊤ ≤ y₂ ⁻¹ᵁ U → ev ω.1 (idLift T y₂ h₂ e₂) - ev ω.1 (idLift T y₁ h₁ e₁) = ∑ k, valR y₂ U (r k) * (valR y₁ U (t k) - valR y₂ U (t k)) := by
  intro R _ X s ω U hU
  have hx := CechDR.affPt_w s ⟨U, hU⟩
  obtain ⟨n, r, t, hΩ⟩ := exists_sum_smul_D (connForm ω.1 (CechDR.affPt s ⟨U, hU⟩) hx)
  refine ⟨n, r, t, ?_⟩
  intro T hJ hδ y₁ y₂ h₁ h₂ e₁ e₂ hy₁ hy₂
  have p₁ := valHom_pt hU y₁ hy₁ h₁
  have p₂ := valHom_pt hU y₂ hy₂ h₂
  have hπ : T.π.comp (valHom y₁ hy₁ h₁ : CechDR.Sec s U →+* T.B) = T.π.comp (valHom y₂ hy₂ h₂ : CechDR.Sec s U →+* T.B) :=
    ringHom_ext_affPt hU (by rw [Cris.spMap_comp, Cris.spMap_comp, Category.assoc, Category.assoc, p₁, p₂, e₁, e₂])
  have hd : ∀ b, valHom y₁ hy₁ h₁ b - valHom y₂ hy₂ h₂ b ∈ T.J := fun b ↦
    (T.ker _).1 (by rw [map_sub, sub_eq_zero]; exact RingHom.congr_fun hπ b)
  let Φ : (diagExt R (CechDR.Sec s U)).thick (CechDR.affPt s ⟨U, hU⟩) hx ⟶ T :=
    { φ := diagLift hJ _ _ hd
      φ₀ := T.π.comp (valHom y₂ hy₂ h₂ : CechDR.Sec s U →+* T.B)
      comm := fun c ↦ by
        have h0 := (T.ker _).2 (diagLift_sub_mem hJ _ _ hd c)
        rw [map_sub, sub_eq_zero] at h0
        exact h0.symm
      dp := by
        have key : DividedPowers.IsDPMorphism (divided₂ (diagExt R (CechDR.Sec s U)).sq) (divided₂ hJ)
            (diagLift hJ _ _ hd : TrivSqZeroExt (CechDR.Sec s U) Ω[(CechDR.Sec s U)⁄R] →+* T.B) :=
          isDPMorphism_sqDP _ hJ _ fun (a : TrivSqZeroExt (CechDR.Sec s U) Ω[(CechDR.Sec s U)⁄R]) ha ↦ by
            have ha' : a.fst = 0 := ha
            have h0 := diagLift_sub_mem hJ _ _ hd a
            rwa [ha', map_zero, sub_zero] at h0
        rw [hδ]
        exact key
      pt := by rw [Cris.spMap_comp, Category.assoc, p₂, e₂] }
  let a₁ : Thick.triv (CechDR.Sec s U) (CechDR.affPt s ⟨U, hU⟩) hx ⟶ Thick.triv T.B y₁ h₁ :=
    Thick.trivHom (valHom y₁ hy₁ h₁) p₁
  let a₂ : Thick.triv (CechDR.Sec s U) (CechDR.affPt s ⟨U, hU⟩) hx ⟶ Thick.triv T.B y₂ h₂ :=
    Thick.trivHom (valHom y₂ hy₂ h₂) p₂
  have k₂ := Form.ev_sq ω a₂ (idLift T y₂ h₂ e₂)
    ((diagExt R (CechDR.Sec s U)).secHom hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl) Φ rfl rfl
    fun c ↦ (diagLift_inl hJ _ _ hd c).symm
  have k₁ := Form.ev_sq ω a₁ (idLift T y₁ h₁ e₁)
    ((diagExt R (CechDR.Sec s U)).secHom hx (diagSec R (CechDR.Sec s U)) (fst_derSec _)) Φ rfl rfl
    fun c ↦ (diagLift_diagSec hJ _ _ hd c).symm
  have f₁ := fst_ev_secHom ω (CechDR.Sec s U) _ hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl
  have f₂ := fst_ev_secHom ω (CechDR.Sec s U) _ hx (diagSec R (CechDR.Sec s U)) (fst_derSec _)
  rw [k₁, k₂, add_sub_add_right_eq_sub, ← map_sub]
  change diagLift hJ _ _ hd _ = _
  rw [diagLift_apply, TrivSqZeroExt.fst_sub, f₁, f₂, sub_self, map_zero, zero_add]
  have hc : (ev ω.1 ((diagExt R (CechDR.Sec s U)).secHom hx (diagExt R (CechDR.Sec s U)).i fun _ ↦ rfl) -
      ev ω.1 ((diagExt R (CechDR.Sec s U)).secHom hx (diagSec R (CechDR.Sec s U)) (fst_derSec _))).snd =
      connForm ω.1 (CechDR.affPt s ⟨U, hU⟩) hx := rfl
  rw [hc, hΩ, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [diffLam_smul, diffLam_D]
  exact (congrArg₂ (fun a b ↦ a * b) (valR_eq_valHom y₂ hy₂ h₂ (r k))
    (congrArg₂ (fun a b ↦ a - b) (valR_eq_valHom y₁ hy₁ h₁ (t k)) (valR_eq_valHom y₂ hy₂ h₂ (t k)))).symm

end GlobalTheory.CechKS.FormLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureMapOfLineBundleIsoRescaled
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.PkgBaseChange
open GlobalTheory.UU

theorem surjective_of_cube {S' : Scheme.{0}} (G' : Over S') [GrpObj G']
    (h3 : Function.Surjective (G3 G').hom.appTop.hom) : Function.Surjective G'.hom.appTop.hom := by
  let s : G' ⟶ G3 G' := lift (𝟙 G') (lift 1 1)
  have hs : s.left ≫ (fst G' (G' ⊗ G')).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_fst]; rfl
  have hw : s.left ≫ (G3 G').hom = G'.hom := Over.w s
  intro g
  obtain ⟨c, hc⟩ := h3 ((fst G' (G' ⊗ G')).left.appTop.hom g)
  refine ⟨c, ?_⟩
  have e1 : G'.hom.appTop.hom c = s.left.appTop.hom ((G3 G').hom.appTop.hom c) := by
    rw [← hw, Scheme.Hom.comp_appTop]; rfl
  have e2 : s.left.appTop.hom ((fst G' (G' ⊗ G')).left.appTop.hom g) = g := by
    rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, hs]; rfl
  rw [e1, hc, e2]

theorem exists_isCPMap_of_lbIso : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G]
    (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (F : G'.left ⟶ G.left) (hw : F ≫ G.hom = G'.hom ≫ f),
    (∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) →
    Function.Surjective (G3 G').hom.appTop.hom → ∀ (P : GlobalTheory.UU.CP G) (P' : GlobalTheory.UU.CP G'),
    LBIso P'.L.L (P.L.L.pull F) → ∃ w, GlobalTheory.UU.IsCPMap P' P f F hw w := by
  intro S S' f G _ _ G' _ _ F hw mul h3 M M' ⟨w, hg⟩
  have h1 := surjective_of_cube G' h3
  obtain ⟨rig, hr, c, s, hs, h₂, h₃, H⟩ := exists_isCPMap M mul M'.L.L M'.L.isLB w hg
  let N : CP G' := ⟨⟨M'.L.L, rig, M'.L.isLB, hr⟩, c, s, hs, h₂, h₃⟩
  obtain ⟨a, ha⟩ := GlobalTheory.AbPackage.exists_unit_ratio M'.L.isLB (φ := fun _ : PUnit => eSec G') (ε := fun _ => 1)
    hr M'.L.rigGen
  let b : Γ(G'.left, ⊤)ˣ := pullU G'.hom ⊤ a
  have es : ∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (J), Good M'.L.L z J → val s r z J = val M'.sym r z J :=
    gen_unique M'.L.isLB G'.hom (1 : 𝟙_ (Over S') ⟶ G').left (Over.w _) h1 hs M'.sym_gen
      fun y J hJ => (N.val_sym_one hJ).trans (M'.val_sym_one hJ).symm
  have ec : ∀ (T : Over S') (z : T.left) (J), Good M'.L.L z J → ∀ x y u : T ⟶ G',
      cubV c z J x y u = cubV M'.c z J x y u := fun T z J hJ x y u =>
    gen_unique M'.L.isLB (φ := thφ G' (x3 G')) (ε := thε) (G3 G').hom
      (lift (1 : 𝟙_ (Over S') ⟶ G') (lift 1 1)).left (Over.w _) h3 c.isGen M'.c.isGen
      (fun y J hJ => ((isCub_cubV c hJ).face 1 1).trans ((isCub_cubV M'.c hJ).face 1 1).symm) _ _ z J hJ
  refine ⟨scaleGen b w, mul, scaleGen_isGen b hg, fun T z J' J hJ' hJ W hW => ?_⟩
  obtain ⟨W₀, hW₀⟩ : ∃ W₀ : (T ⟶ G') → (T.left.presheaf.stalk z)ˣ,
    ∀ x, W₀ x = gw w x.left z (J (x.left ≫ F)) (J' x.left) := ⟨_, fun _ => rfl⟩
  obtain ⟨α, hα⟩ : ∃ α : (T.left.presheaf.stalk z)ˣ, α = gm (Y := T.left) T.hom z ⊤ a := ⟨_, rfl⟩
  have e : ∀ x, W x = α * W₀ x := fun x => by
    have hm : x.left z ∈ (M.L.L.pull F).U (fun _ => J (x.left ≫ F)) ⊓ M'.L.L.U (J' x.left) :=
      ⟨mem_pull.2 (hJ (x.left ≫ F)), hJ' x.left⟩
    rw [hW, hW₀, hα, ← Over.w x]
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_res x.left z le_top hm b).trans
      (gm_pull x.left G'.hom z ⊤ trivial a)) rfl)
  obtain ⟨a₁, a₂, a₃⟩ := H.vals T z J' J hJ' hJ W₀ hW₀
  refine ⟨?_, fun x => ?_, fun x y u => ?_⟩
  · refine a₁.trans ((congrArg (W₀ 1 * ·) (ha _ T.hom z J' hJ')).trans ?_)
    rw [e, hα, mul_comm _ (W₀ 1), _root_.mul_assoc]
  · have q : val M.sym (x.left ≫ F) z J * W₀ x = W₀ x⁻¹ * val M'.sym x.left z J' :=
      (a₂ x).trans (congrArg (W₀ x⁻¹ * ·) (es _ x.left z J' hJ'))
    rw [e, e, mul_left_comm, q, _root_.mul_assoc]
  · have q := (a₃ x y u).trans (congrArg (W₀ (x * y * u) * W₀ x * W₀ y * W₀ u * ·) (ec T z J' hJ' x y u))
    simp only [e]
    apply Additive.ofMul.injective
    have q' := congrArg Additive.ofMul q
    simp only [ofMul_mul] at q' ⊢
    linear_combination (norm := abel) q'

end GlobalTheory.PkgBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCyclotomicAwayFiniteEtaleCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.HTSympCover

noncomputable section

namespace GlobalTheory.CycAwayCover

theorem isUnit_natCast_cycAway {M : ℕ} (hM : M ≠ 0) : IsUnit (M : cycAway M) := by
  refine isUnit_iff_exists_inv.2 ⟨⟨(M : ℂ)⁻¹, Subring.subset_closure (Or.inr rfl)⟩, ?_⟩
  exact Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hM : (M : ℂ) ≠ 0))

def awayToCyc (M : ℕ) (hM : M ≠ 0) : Localization.Away (M : ℤ) →+* cycAway M :=
  IsLocalization.Away.lift (S := Localization.Away (M : ℤ)) (M : ℤ) (g := Int.castRingHom (cycAway M))
    (by simpa using isUnit_natCast_cycAway hM)

theorem awayToCyc_injective {M : ℕ} (hM : M ≠ 0) : Function.Injective (awayToCyc M hM) := by
  have hle : Submonoid.powers (M : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hM)
  rw [awayToCyc, IsLocalization.Away.lift, IsLocalization.lift_injective_iff]
  intro x y
  rw [(IsLocalization.injective (Localization.Away (M : ℤ)) hle).eq_iff,
    (Int.castRingHom (cycAway M)).injective_int.eq_iff]

theorem finite_awayToCyc {M : ℕ} (hM : M ≠ 0) : (awayToCyc M hM).Finite := by
  letI := (awayToCyc M hM).toAlgebra
  have hv : ∀ hx, (⟨(M : ℂ)⁻¹, hx⟩ : cycAway M) =
      algebraMap (Localization.Away (M : ℤ)) (cycAway M) (IsLocalization.Away.invSelf (M : ℤ)) := by
    intro hx
    have h1 : (M : cycAway M) * ⟨(M : ℂ)⁻¹, hx⟩ = 1 :=
      Subtype.ext (by simpa using mul_inv_cancel₀ (Nat.cast_ne_zero.2 hM : (M : ℂ) ≠ 0))
    have h2 : (M : cycAway M) * algebraMap (Localization.Away (M : ℤ)) (cycAway M)
        (IsLocalization.Away.invSelf (M : ℤ)) = 1 := by
      have := congrArg (algebraMap (Localization.Away (M : ℤ)) (cycAway M))
        (IsLocalization.Away.mul_invSelf (S := Localization.Away (M : ℤ)) (M : ℤ))
      simpa using this
    exact (isUnit_natCast_cycAway hM).mul_left_cancel (h1.trans h2.symm)
  have hint : Algebra.IsIntegral (Localization.Away (M : ℤ)) (cycAway M) := by
    constructor
    rintro ⟨x, hx⟩
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ⟨Polynomial.X ^ M - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hM, by
          simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, map_one, Polynomial.eval₂_one]
          exact sub_eq_zero.2 (GlobalTheory.SiegelTor.zetaAway_pow_self hM)⟩
      · convert (isIntegral_algebraMap (R := Localization.Away (M : ℤ)) (x := IsLocalization.Away.invSelf (M : ℤ)) : IsIntegral _ (algebraMap (Localization.Away (M : ℤ)) (cycAway M) _)) using 1
        exact hv _
    | zero => exact isIntegral_zero
    | one => exact isIntegral_one
    | add x y _ _ hx hy => exact hx.add hy
    | neg x _ hx => exact hx.neg
    | mul x y _ _ hx hy => exact hx.mul hy
  haveI : Algebra.FiniteType (Localization.Away (M : ℤ)) (cycAway M) := by
    refine ⟨⟨{zetaAway M}, eq_top_iff.2 ?_⟩⟩
    rintro ⟨x, hx⟩ -
    induction hx using Subring.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_singleton_self _))
      · convert Subalgebra.algebraMap_mem (Algebra.adjoin (Localization.Away (M : ℤ)) ((({zetaAway M} : Finset (cycAway M)) : Set (cycAway M)))) (IsLocalization.Away.invSelf (M : ℤ)) using 1
        exact hv _
    | zero => exact Subalgebra.zero_mem _
    | one => exact Subalgebra.one_mem _
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | neg x _ hx => exact Subalgebra.neg_mem _ hx
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  exact (Algebra.IsIntegral.finite : Module.Finite (Localization.Away (M : ℤ)) (cycAway M))

theorem etale_awayToCyc {M : ℕ} (hM : M ≠ 0) : (awayToCyc M hM).Etale := by
  letI := (awayToCyc M hM).toAlgebra
  have hle : Submonoid.powers (M : ℤ) ≤ nonZeroDivisors ℤ :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (by exact_mod_cast hM)
  haveI : IsDomain (Localization.Away (M : ℤ)) := IsLocalization.isDomain_localization hle
  haveI : IsDedekindDomain (Localization.Away (M : ℤ)) :=
    IsLocalization.isDedekindDomain ℤ hle (Localization.Away (M : ℤ))
  haveI : Module.Finite (Localization.Away (M : ℤ)) (cycAway M) := finite_awayToCyc hM
  haveI : FaithfulSMul (Localization.Away (M : ℤ)) (cycAway M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (awayToCyc_injective hM)
  haveI : Module.Flat (Localization.Away (M : ℤ)) (cycAway M) := inferInstance
  haveI : Algebra.FinitePresentation (Localization.Away (M : ℤ)) (cycAway M) :=
    Algebra.FinitePresentation.of_finiteType.1 inferInstance
  haveI := formallyUnramified_cycAway hM (Localization.Away (M : ℤ))
  exact (Algebra.Etale.of_formallyUnramified_of_flat : Algebra.Etale (Localization.Away (M : ℤ)) (cycAway M))

theorem exists_cycAway_cover : ∀ (M : ℕ) (S : Scheme.{0}), 0 < M → IsUnit (M : Γ(S, ⊤)) → ∃ (S' : Over S) (t₀ : S'.left ⟶ Sp (cycAway M)), IsFinite S'.hom ∧ Etale S'.hom ∧ ∀ (T : Scheme.{0}) (f : T ⟶ S) (t₁ : T ⟶ Sp (cycAway M)), ∃! g : T ⟶ S'.left, g ≫ S'.hom = f ∧ g ≫ t₀ = t₁ := by
  intro M S hM hS
  have hM0 : M ≠ 0 := hM.ne'
  have hSu : IsUnit ((Int.castRingHom Γ(S, ⊤)) (M : ℤ)) := by simpa using hS
  let φ : S ⟶ Sp (Localization.Away (M : ℤ)) :=
    S.toSpecΓ ≫ spMap (IsLocalization.Away.lift (S := Localization.Away (M : ℤ)) (M : ℤ) hSu)
  let S' : Over S := Over.mk (pullback.fst φ (spMap (awayToCyc M hM0)))
  haveI : IsFinite (spMap (awayToCyc M hM0)) := (IsFinite.SpecMap_iff _).2 (finite_awayToCyc hM0)
  haveI : Etale (spMap (awayToCyc M hM0)) := HasRingHomProperty.Spec_iff.2 (etale_awayToCyc hM0)
  refine ⟨S', pullback.snd φ (spMap (awayToCyc M hM0)), ?_, ?_, ?_⟩
  · exact (inferInstance : IsFinite (pullback.fst φ (spMap (awayToCyc M hM0))))
  · exact (inferInstance : Etale (pullback.fst φ (spMap (awayToCyc M hM0))))
  · intro T f t₁
    haveI : IsOpenImmersion (spMap (algebraMap ℤ (Localization.Away (M : ℤ)))) :=
      inferInstanceAs (IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap ℤ (Localization.Away (M : ℤ))))))
    have e : f ≫ φ = t₁ ≫ spMap (awayToCyc M hM0) :=
      (cancel_mono (spMap (algebraMap ℤ (Localization.Away (M : ℤ))))).1 (specZIsTerminal.hom_ext _ _)
    refine ⟨pullback.lift f t₁ e, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩, ?_⟩
    rintro g ⟨h1, h2⟩
    exact pullback.hom_ext (h1.trans (pullback.lift_fst _ _ e).symm) (h2.trans (pullback.lift_snd _ _ e).symm)

end GlobalTheory.CycAwayCover
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataPullbackInjectiveLocalHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.MumPull

theorem specOf_genericPoint {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (ρ : R →+* R')
    (hρ : Function.Injective ρ) :
    (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) = genericPoint (Spec (CommRingCat.of R)) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  show Ideal.comap ρ ⊥ = ⊥
  exact Ideal.comap_bot_of_injective ρ hρ

theorem exists_pull : ∀ (R R' : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), Function.Injective ρ → IsLocalHom ρ → ∀ D : DegData R (maximalIdeal R), ∃ D' : DegData R' (maximalIdeal R'), Nonempty (IsPullDeg ρ D.toPre D'.toPre) := by
  intro R R' _ _ _ _ _ _ ρ hρ hloc D
  obtain ⟨L, -⟩ := GlobalTheory.T.all_six_abelian_scheme_laws_hold
  obtain ⟨W, hW, hψ⟩ := GlobalTheory.PsiSpread.exists_psiOn D.toPre D.tau_bimult
  have hη : (specOf ρ).base (genericPoint (Spec (CommRingCat.of R'))) ∈ W := by
    rw [specOf_genericPoint ρ hρ]; exact hW
  have hI : (maximalIdeal R).map ρ ≤ maximalIdeal R' :=
    ((IsLocalRing.local_hom_TFAE ρ).out 0 2).1 hloc
  obtain ⟨D', hD, -, -⟩ := GlobalTheory.exists_degData_isPullDeg L.polBaseChange L.globalFns R R' (maximalIdeal R)
    (maximalIdeal R') ρ hI D W hψ hη
  exact ⟨D', ⟨hD⟩⟩

end GlobalTheory.MumPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegenerationDataValuesUltrametric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section
namespace GlobalTheory.IntGauge

theorem exists_ball (C : Type) [NormedField C] [IsUltrametricDist C] :
    ∃ S : ValuationSubring C, ∀ x, x ∈ S ↔ ‖x‖ ≤ 1 := by
  refine ⟨{ carrier := {x | ‖x‖ ≤ 1}
            mul_mem' := fun {a b} ha hb => by
              simp only [Set.mem_setOf_eq, norm_mul] at *
              exact mul_le_one₀ ha (norm_nonneg _) hb
            one_mem' := by simp
            add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
            zero_mem' := by simp
            neg_mem' := fun {a} ha => by simpa using ha
            mem_or_inv_mem' := fun x => by
              by_cases h : ‖x‖ ≤ 1
              · exact Or.inl h
              · right
                show ‖x⁻¹‖ ≤ 1
                rw [norm_inv]
                exact inv_le_one_of_one_le₀ (le_of_lt (not_le.1 h)) }, fun x => Iff.rfl⟩

theorem exists_intN : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (D : DegData V (IsLocalRing.maximalIdeal V)), ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] [CharZero C] [Algebra (FractionRing V) C], CExt V (IsLocalRing.maximalIdeal V) C → ∃ (N : NumD C) (ν : NumOf D.toPre C N), ν.IntN := by
  intro V _ _ _ _ _ D C _ _ _ _ _ _ hC
  obtain ⟨S, hS⟩ := exists_ball C
  obtain ⟨N, ν, hν⟩ := GlobalTheory.ValuesExist.exists_integral_values GlobalTheory.firstFiveLaws.1 V D.toPre D.psi_even D.tau_bimult
    C S (fun r => (hS _).2 (hC.1 r))
  exact ⟨N, ν, S, hS, hν⟩

end GlobalTheory.IntGauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegularLocalRingQuotientOfDetDerivationUnitStatement
section
open IsLocalRing TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isRegularLocalRing_quotient_of_det_derivation_unit : ∀ (T : Type) [CommRing T] [IsRegularRing T] (h : ℕ) (f : Fin h → T) (D : Fin h → Derivation ℤ T T) (n : Ideal T) [n.IsPrime], (∀ j, f j ∈ n) → (Matrix.of fun i j => D i (f j)).det ∉ n → IsRegularLocalRing (Localization.AtPrime n ⧸ (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime n))) := by
  first | exact @GlobalTheory.JacobianDerivation.isRegularLocalRing_quotient | exact GlobalTheory.JacobianDerivation.isRegularLocalRing_quotient | (intros; apply GlobalTheory.JacobianDerivation.isRegularLocalRing_quotient <;> assumption)
end

