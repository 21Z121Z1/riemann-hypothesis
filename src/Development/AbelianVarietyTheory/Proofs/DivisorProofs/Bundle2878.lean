import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0045
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2578
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2570
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEndomorphismPlaceIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyPeriodNormalization
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.BirigidLift

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMModel

theorem cls_eq_of_pull {S S' : Scheme.{0}} {b : S' ⟶ S} [Flat b] [Surjective b] {A B D : Over S} [GrpObj A] [GrpObj D]
    {A' B' D' : Over S'} [GrpObj A'] [GrpObj D'] {f : A'.left ⟶ A.left} {g : B'.left ⟶ B.left} {d : D'.left ⟶ D.left}
    {l : (A' ⊗ B').left ⟶ (A ⊗ B).left} {m : (A' ⊗ D').left ⟶ (A ⊗ D).left}
    (hg : IsPullback g B'.hom B.hom b) (hd : IsGrpPullback D' D b d)
    (l₁ : l ≫ (fst A B).left = (fst A' B').left ≫ f) (l₂ : l ≫ (snd A B).left = (snd A' B').left ≫ g)
    (m₁ : m ≫ (fst A D).left = (fst A' D').left ≫ f) (m₂ : m ≫ (snd A D).left = (snd A' D').left ≫ d)
    {Q : LB (A ⊗ D).left} (q : IsDual A D Q) (q' : IsDual A' D' (Q.pull m))
    {P P' : LB (A ⊗ B).left} (hP : P.IsLB) (hP' : P'.IsLB) (a : IsAdditive P) (a' : IsAdditive P')
    (e : CechPic.pull l (cls P hP) = CechPic.pull l (cls P' hP')) : cls P hP = cls P' hP' := by
  obtain ⟨x, hx, -⟩ := q.univ B P hP a
  obtain ⟨x', hx', -⟩ := q.univ B P' hP' a'
  have ex : cls P hP = evc q.isLB (fst A B) (snd A B ≫ x) := (cls_eq_iff hP (pull_isLB q.isLB _)).2 hx
  have ex' : cls P' hP' = evc q.isLB (fst A B) (snd A B ≫ x') := (cls_eq_iff hP' (pull_isLB q.isLB _)).2 hx'
  have ly : ∀ y : B ⟶ D, ∃ y' : B' ⟶ D', g ≫ y.left = y'.left ≫ d := fun y ↦
    ⟨_, (liftPt_left hd B'.hom (g ≫ y.left) (by rw [Category.assoc, Over.w y, hg.w])).symm⟩
  obtain ⟨y, ey⟩ := ly x
  obtain ⟨y', ey'⟩ := ly x'
  obtain rfl : y = y' := dual_ext q' <| by
    rw [← pull_evc_eq l₁ l₂ m₁ m₂ q.isLB q'.isLB ey, ← pull_evc_eq l₁ l₂ m₁ m₂ q.isLB q'.isLB ey', ← ex, ← ex', e]
  obtain rfl : x = x' := ActDescent.over_hom_ext hg (ey.trans ey'.symm)
  exact ex.trans ex'.symm

theorem exists_obj_of_isGrpPullback (HD : GlobalTheory.Published.DualAbelianScheme) {F : Type} [Field F] [NumberField F]
    {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (c₀ : 𝔠.elt) (hc₀ : IsTotPos (c₀ : F)) (A₀ : Over (Sp Qb)) [GrpObj A₀]
    (p : X.A.left ⟶ A₀.left) (hA₀ : IsAbelianScheme A₀) (gA₀ : SmoothOfRelativeDimension (Module.finrank ℚ F) A₀.hom)
    (hp : IsGrpPullback X.A A₀ (spMap (algebraMap Qb ℂ)) p) :
    ∃ (X₀ : Obj F 𝔠 (Sp Qb)) (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p := by
  haveI : Flat (spMap (algebraMap Qb ℂ)) := Flat.SpecMap_iff.2 (by
    letI := (algebraMap Qb ℂ).toAlgebra
    exact (inferInstance : Module.Flat Qb ℂ))
  haveI : Surjective (spMap (algebraMap Qb ℂ)) := ⟨fun x ↦ ⟨(inferInstance : Nonempty (PrimeSpectrum ℂ)).some,
    Subsingleton.elim (α := PrimeSpectrum Qb) _ _⟩⟩
  haveI := hA₀.comm
  obtain ⟨rm, hrm⟩ := ActDescent.exists_oAct hp X.rm fun a ↦ by
    obtain ⟨f, -, hf⟩ := GlobalTheory.T.homomorphism_descends_to_algebraic A₀ A₀ X.A X.A p p _ _ hA₀ gA₀ hA₀ gA₀ hp hp (X.rm.act a) (X.rm.hom a)
    exact ⟨f, hf⟩
  obtain ⟨D₀, _, Q, D, _, d, m, hD₀, gD₀, q₀, q₀', hd, m₁, m₂, q, q'⟩ := exists_dual_pair HD hA₀ gA₀ hp
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback hp hp
  obtain ⟨H, hH, aH⟩ := exists_relAmple_prod X.ab X.ab (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
    (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
  have hx : ∀ c : 𝔠.elt, ∃ P₀ : LB (A₀ ⊗ A₀).left, ∃ h : P₀.IsLB, IsAdditive P₀ ∧ IsAdditive (swap P₀) ∧
      CechPic.pull l (cls P₀ h) = cls (X.P c) (X.isLB c) := fun c ↦ by
    obtain ⟨a₁, a₂⟩ := additive_of_triv X.ab X.ab hH aH (X.isLB c) (X.rig₁ c) (X.rig₂ c)
    obtain ⟨x, hx, ex⟩ := exists_hom q q' (X.isLB c) a₁ a₂
    obtain ⟨x₀, hx₀, e₀⟩ := GlobalTheory.T.homomorphism_descends_to_algebraic A₀ D₀ X.A D p d _ _ hA₀ gA₀ hD₀ gD₀ hp hd x hx
    obtain ⟨b₁, b₂⟩ := additive_ev q₀.isLB q₀.additive q₀'.additive x₀
    refine ⟨_, pull_isLB q₀.isLB _, b₁, b₂, ?_⟩
    rw [cls_ev q₀.isLB, ex]
    exact pull_evc_eq l₁ l₂ m₁ m₂ q₀.isLB q.isLB e₀.symm
  choose P₀ hP₀ a₁ a₂ eP using hx
  have inj : ∀ {P P' : LB (A₀ ⊗ A₀).left} (hP : P.IsLB) (hP' : P'.IsLB), IsAdditive P → IsAdditive P' →
      CechPic.pull l (cls P hP) = CechPic.pull l (cls P' hP') → LBIso P P' := fun hP hP' a a' e ↦
    (cls_eq_iff hP hP').1 (cls_eq_of_pull hp.1 hd l₁ l₂ m₁ m₂ q₀ q hP hP' a a' e)
  have iso : ∀ c, LBIso ((P₀ c).pull l) (X.P c) := fun c ↦
    (cls_eq_iff (pull_isLB (hP₀ c) _) (X.isLB c)).1 (by rw [cls_pull (hP₀ c)]; exact eP c)

  have val : ∀ (c : 𝔠.elt) {Y₀ : Over (Sp Qb)} {Y : Over (Sp ℂ)} (r : Y.left ⟶ Y₀.left) (a₀ t₀ : Y₀ ⟶ A₀)
      (a t : Y ⟶ X.A), a.left ≫ p = r ≫ a₀.left → t.left ≫ p = r ≫ t₀.left →
      CechPic.pull r (evc (hP₀ c) a₀ t₀) = evc (X.isLB c) a t := fun c Y₀ Y r a₀ t₀ a t ha ht ↦ by
    rw [evc, evc, ← eP, ← pull_comp, ← pull_comp]
    congr 2
    apply left_ext
    · rw [Category.assoc, Category.assoc, lift_left_fst, l₁, lift_left_fst_assoc, ha]
    · rw [Category.assoc, Category.assoc, lift_left_snd, l₂, lift_left_snd_assoc, ht]
  refine ⟨{ A := A₀
            ab := hA₀
            dim := gA₀
            rm := rm
            P := P₀
            isLB := hP₀
            rig₁ := fun c ↦ triv_left (hP₀ c) (a₁ c)
            rig₂ := fun c ↦ triv_right (hP₀ c) (a₂ c)
            symm := fun c ↦ ?_
            add := fun c c' ↦ ?_
            smul := fun a c ↦ ?_
            pos := fun c hc ↦ ?_
            ker := fun c T₀ x hx a ha ↦ ?_ }, p, hp, hrm, l, ⟨l₁, l₂⟩, fun c ↦ ?_⟩
  · refine inj (hP₀ c) (pull_isLB (hP₀ c) _) (a₁ c) (a₂ c) ?_
    rw [eP, cls_ev (hP₀ c), val c l _ _ _ _ l₂.symm l₁.symm]
    exact (cls_eq_iff _ (pull_isLB (X.isLB c) _)).2 (X.symm c)
  · have hq := LB.isLB_div (hP₀ (c + c')) (hP₀ c)
    have ev' : ∀ (Y : Over (Sp Qb)) (a t : Y ⟶ A₀), evc hq a t = evc (hP₀ (c + c')) a t - evc (hP₀ c) a t :=
      fun Y a t ↦ by rw [evc, cls_div (hP₀ (c + c')) (hP₀ c), map_sub]; rfl
    refine inj (hP₀ c') hq (a₁ c') ((isAdditive_iff hq).2 fun Y a a' t ↦ ?_) ?_
    · rw [ev', ev', ev', (isAdditive_iff (hP₀ _)).1 (a₁ _), (isAdditive_iff (hP₀ _)).1 (a₁ _)]
      abel
    · rw [cls_div (hP₀ (c + c')) (hP₀ c), map_sub, eP, eP, eP, ← cls_div (X.isLB (c + c')) (X.isLB c)
        (LB.isLB_div (X.isLB (c + c')) (X.isLB c))]
      exact (cls_eq_iff _ _).2 (X.add c c')
  · have hq : (ev (P₀ c) (fst A₀ A₀) (snd A₀ A₀ ≫ rm.act a)).IsLB := pull_isLB (hP₀ c) _
    refine inj (hP₀ _) hq (a₁ _) ((isAdditive_iff hq).2 fun Y u u' t ↦ ?_) ?_
    · simp only [evc_ev (hP₀ c), lift_fst, lift_snd_assoc]
      exact (isAdditive_iff (hP₀ c)).1 (a₁ c) _ _ _ _
    · rw [eP, cls_ev (hP₀ c), val c l _ _ (fst X.A X.A) (snd X.A X.A ≫ X.rm.act a) l₁.symm (by
        rw [Over.comp_left, Over.comp_left, Category.assoc, hrm, ← Category.assoc, ← Category.assoc, l₂])]
      exact (cls_eq_iff _ (pull_isLB (X.isLB c) _)).2 (X.smul a c)
  · refine AmpleDescent.relAmple_of_fieldExtension Qb ℂ _ A₀ X.A p _ _ hA₀ hp (pull_isLB (hP₀ c) _)
      (pull_isLB (X.isLB c) _) ((cls_eq_iff (pull_isLB (X.isLB c) _) (pull_isLB (pull_isLB (hP₀ c) _) _)).1 ?_)
      (X.pos c hc)
    rw [cls_pull (pull_isLB (hP₀ c) _), cls_ev (hP₀ c), cls_ev (X.isLB c)]
    exact (val c p _ _ _ _ (by simp) (by simp)).symm
  · let T : Over (Sp ℂ) := (Over.pullback (spMap (algebraMap Qb ℂ))).obj T₀
    let r : T.left ⟶ T₀.left := Limits.pullback.fst _ _
    have hr : IsPullback r T.hom T₀.hom (spMap (algebraMap Qb ℂ)) := IsPullback.of_hasPullback _ _
    have w : (r ≫ x.left) ≫ A₀.hom = T.hom ≫ spMap (algebraMap Qb ℂ) := by rw [Category.assoc, Over.w x, hr.w]
    let x' : T ⟶ X.A := liftPt hp T.hom _ w
    have ex : x'.left ≫ p = r ≫ x.left := liftPt_left hp _ _ w
    let u : Over.mk ((X.A ⊗ T).hom ≫ spMap (algebraMap Qb ℂ)) ⟶ T₀ := Over.homMk ((snd X.A T).left ≫ r) (by
      change ((snd X.A T).left ≫ r) ≫ T₀.hom = _
      rw [Category.assoc, hr.w, ← Category.assoc, Over.w]
      rfl)
    let s : (X.A ⊗ T).left ⟶ (A₀ ⊗ T₀).left := (lift (pushP hp (s := (X.A ⊗ T).hom) rfl (fst X.A T)) u).left
    have s₁ : s ≫ (fst A₀ T₀).left = (fst X.A T).left ≫ p := lift_left_fst _ _
    have s₂ : s ≫ (snd A₀ T₀).left = (snd X.A T).left ≫ r := lift_left_snd _ _
    have z : evc (X.isLB c) (fst X.A T) (snd X.A T ≫ x') = 0 := by
      rw [← val c s (fst A₀ T₀) (snd A₀ T₀ ≫ x) _ _ s₁.symm (by
        rw [Over.comp_left, Over.comp_left, Category.assoc, ex, ← Category.assoc, ← Category.assoc, s₂]),
        (triv_ev_iff (hP₀ c) _ _).1 hx, map_zero]
    have k := X.ker c T x' ((triv_ev_iff (X.isLB c) _ _).2 z) a ha
    refine ActDescent.over_hom_ext hr ?_
    rw [Over.comp_left, ← Category.assoc, ← ex, Category.assoc, ← hrm, ← Category.assoc, ← Over.comp_left, k]
    refine (one_left_comp hp (s := T.hom) rfl).trans ?_
    let r' : Over.mk (T.hom ≫ spMap (algebraMap Qb ℂ)) ⟶ T₀ := Over.homMk r hr.w
    exact congrArg (fun y ↦ y.left) (MonObj.comp_one (M := A₀) r').symm
  · exact (cls_eq_iff (X.isLB c) (pull_isLB (hP₀ c) _)).1 (by rw [cls_pull (hP₀ c)]; exact (eP c).symm)

theorem exists_model : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
      ∃ (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p := by
  intro _ _ HD K _ _ d δ io h2 hd hδ E _ _ _ _ I _ φ hφ hio c y hc 𝔠 X U
  obtain ⟨C₀, _, C, _, p, L, u, s, hC₀, gC₀, hp, hL, hs, hu⟩ := GlobalTheory.T.elliptic_curve_lattice_period_form d (io δ) hd (by
    rw [← map_pow, hδ, map_neg, map_natCast])
  obtain ⟨B₀, _, B, _, q, M, v, hB₀, gB₀, hB, gB, hq, hv⟩ :=
    GlobalTheory.T.abelian_scheme_descent_with_uniformization Qb _ C₀ C p L u hC₀ gC₀ hp hL (Module.finrank ℚ (FR E))
  obtain ⟨T, hT, hTΛ⟩ := GlobalTheory.T.cm_period_matrix_exists K d δ io h2 hd hδ E I φ hφ hio c y hc U.e
  obtain ⟨ψ, hψ, eψ⟩ := GlobalTheory.T.lattice_map_gives_homomorphism B X.A _ hB X.ab gB X.dim M _ v U.u (s⁻¹ • T) fun z hz ↦ by
    obtain ⟨x, hx, ex⟩ := hTΛ (s⁻¹ • z) fun j ↦ by
      obtain ⟨a, b, e⟩ := hu _ (hv z hz j)
      exact ⟨a, b, by rw [Pi.smul_apply, e, smul_eq_mul, inv_mul_cancel_left₀ hs]⟩
    refine (U.lat _).2 ⟨x, hx, ?_⟩
    rw [LinearMap.smul_apply, ← map_smul, ex]
    funext j
    simp [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord]
  obtain ⟨A₀, _, r, hA₀, gA₀, hr⟩ := GlobalTheory.T.quotient_abelian_scheme_descends B₀ B X.A q _ hB₀ gB₀ hq X.ab X.dim ψ hψ fun w ↦ by
    obtain ⟨z, rfl⟩ := U.u.ex_onto w
    obtain ⟨z', rfl⟩ := hT z
    refine ⟨v.ex (s • z'), ?_⟩
    rw [← eψ, LinearMap.smul_apply, map_smul, inv_smul_smul₀ hs]
  exact exists_obj_of_isGrpPullback HD.1 X U.c U.pos A₀ r hA₀ gA₀ hr

end GlobalTheory.CMModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetGaloisDescentStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_auxiliary_set_galois_descent : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)) (σ : E →+* FractionRing R),
      Module.finrank (FractionRing R) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) σ) = 1 := by
  first | exact @GlobalTheory.DRLine.eigK_finrank_eq_one | exact GlobalTheory.DRLine.eigK_finrank_eq_one | (intros; apply GlobalTheory.DRLine.eigK_finrank_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetLevelStructureStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_auxiliary_set_level_structure : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (c₀ : 𝔠.elt) (ψ₀ : LinearMap.BilinForm R (HdR X₀.A)), (c₀ : FR E) ≠ 0 →
      IsPolForm (dp0 R) (𝟙 _) X₀.A (X₀.diag c₀) ((2 : R) • ψ₀) →
      ∀ a b : orderC (condQ 𝔣 Q), (b : E) = IsCMField.complexConj E a → ∀ h h' : HdR X₀.A,
        ψ₀ (act (dp0 R) (𝟙 _) cm a h) h' = ψ₀ h (act (dp0 R) (𝟙 _) cm b h') := by
  first | exact @GlobalTheory.CMAdjoint.half_form_adjoint | exact GlobalTheory.CMAdjoint.half_form_adjoint | (intros; apply GlobalTheory.CMAdjoint.half_form_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmEndomorphismPlaceIntegralStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_endomorphism_place_integral : GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.Published.AbelianDeRham →
  ∀ (F : Type) [Field F] [NumberField F] (𝔠 : FracId F) (O : Type) [CommRing O] (ofO : 𝓞 F → O) (l : ℕ) [Fact l.Prime]
    (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (k₀ : IntermediateField ℚ ℂ) (R₀ : Subring ℂ), Module.Finite ℤ O →
    FiniteDimensional ℚ k₀ → IsPlaceOver l lam k₀ R₀ → (∀ x ∈ R₀, x ∈ k₀) →
    ∀ (σ : R₀ →+* Qb), (∀ x, ((σ x : Qb) : ℂ) = x) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (P₀ : Out.PolAV (Sp R₀)) (Ψ₀ : P₀.A ⟶ G₀),
      IsAbelianScheme G₀ → IsMonHom Ψ₀ → IsFinite Ψ₀.left → Flat Ψ₀.left → Surjective Ψ₀.left →
    ∀ (XQ : Obj F 𝔠 (Sp Qb)) (gQ : XQ.A.left ⟶ G₀.left) (cmQ : OAct O XQ.A), IsGrpPullback XQ.A G₀ (spMap σ) gQ →
      (∀ a, cmQ.act (ofO a) = XQ.rm.act a) →
      Eventually l lam fun R ↦ ∀ (ic : R₀ →+* R) (j : R →+* Qb), (∀ x, ((ic x : R) : ℂ) = x) → (∀ x, ((j x : Qb) : ℂ) = x) →
        ∃ (X₀ : Obj F 𝔠 (Sp R)) (pj : XQ.A.left ⟶ X₀.A.left) (g : X₀.A.left ⟶ G₀.left) (cm : OAct O X₀.A),
          XQ.IsPullBy X₀ (spMap j) pj ∧ IsGrpPullback X₀.A G₀ (spMap ic) g ∧ pj ≫ g = gQ ∧
          (∀ a, cm.act (ofO a) = X₀.rm.act a) ∧ ∀ a, (cmQ.act a).left ≫ pj = pj ≫ (cm.act a).left := by
  first | exact @GlobalTheory.PlaceModel.exists_obj_eventually | exact GlobalTheory.PlaceModel.exists_obj_eventually | (intros; apply GlobalTheory.PlaceModel.exists_obj_eventually <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeSpansRealSpace
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HermDiagCM

open ComplexConjugate

theorem matrix_eq_zero_of_im_form {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
    (Λ : Submodule ℤ (Fin n → ℂ)) (hs : Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤)
    (h0 : ∀ v ∈ Λ, ∀ v' ∈ Λ, (v ⬝ᵥ M.mulVec (star v')).im = 0) : M = 0 := by
  let B : (Fin n → ℂ) →ₗ[ℝ] (Fin n → ℂ) →ₗ[ℝ] ℝ :=
    LinearMap.mk₂ ℝ (fun v v' => (v ⬝ᵥ M.mulVec (star v')).im)
      (fun a b c => by simp [add_dotProduct])
      (fun r a b => by simp [smul_dotProduct])
      (fun a b c => by simp [star_add, Matrix.mulVec_add, dotProduct_add])
      (fun r a b => by simp [star_smul, Matrix.mulVec_smul, dotProduct_smul])
  have h1 : ∀ v ∈ Λ, B v = 0 := fun v hv =>
    LinearMap.ext_on hs (fun v' hv' => by simpa [B] using h0 v hv v' hv')
  have hB : B = 0 := LinearMap.ext_on hs (fun v hv => by simpa using h1 v hv)
  have him : ∀ z w : Fin n → ℂ, (z ⬝ᵥ M.mulVec (star w)).im = 0 := fun z w => by
    have := congrArg (fun f => f z w) hB
    simpa [B] using this
  have hall : ∀ z w : Fin n → ℂ, z ⬝ᵥ M.mulVec (star w) = 0 := fun z w => by
    apply Complex.ext
    · have := him (Complex.I • z) w
      simpa [smul_dotProduct] using this
    · simpa using him z w
  ext i j
  have := hall (Pi.single i 1) (Pi.single j 1)
  simpa [Matrix.mulVec_single, single_dotProduct] using this

section CM

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem sum_embeddings_eq {I : Type} [Fintype I] (φ : I → E →+* ℂ) (hφ : GlobalTheory.CMVal.IsCMType φ)
    (w : E) : ∑ σ : E →+* ℂ, σ w = ∑ i, (φ i w + conj (φ i w)) := by
  let f : I × Bool → (E →+* ℂ) := fun p => cond p.2 (ComplexEmbedding.conjugate (φ p.1)) (φ p.1)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨i, a⟩ ⟨j, b⟩ hij
      have uniq : ∀ k l, φ k = φ l ∨ φ k = ComplexEmbedding.conjugate (φ l) → k = l := by
        intro k l hkl
        obtain ⟨m, -, hm⟩ := hφ (φ k)
        exact (hm k (Or.inl rfl)).trans (hm l hkl).symm
      cases a <;> cases b <;> simp only [f, cond_true, cond_false] at hij
      · simp [uniq i j (Or.inl hij)]
      · have hij' := uniq i j (Or.inr hij)
        subst hij'
        exact absurd (ComplexEmbedding.isReal_iff.mpr hij.symm)
          (IsTotallyComplex.complexEmbedding_not_isReal (φ i))
      · have hij' := uniq j i (Or.inr hij.symm)
        subst hij'
        exact absurd (ComplexEmbedding.isReal_iff.mpr hij)
          (IsTotallyComplex.complexEmbedding_not_isReal (φ j))
      · have : φ i = φ j := by
          have := congrArg ComplexEmbedding.conjugate hij
          simpa using this
        simp [uniq i j (Or.inl this)]
    · intro σ
      obtain ⟨i, hi, -⟩ := hφ σ
      rcases hi with h | h
      · exact ⟨(i, false), h.symm⟩
      · exact ⟨(i, true), h.symm⟩
  rw [← Fintype.sum_bijective f hf (fun p => f p w) (fun σ => σ w) (fun _ => rfl),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Fintype.sum_bool]
  simp [f, ComplexEmbedding.conjugate_coe_eq, add_comm]

theorem sum_embeddings_map (g : ℂ ≃+* ℂ) (w : E) :
    ∑ σ : E →+* ℂ, g (σ w) = ∑ σ : E →+* ℂ, σ w := by
  let eq : (E →+* ℂ) ≃ (E →+* ℂ) :=
    { toFun := fun σ => (g : ℂ →+* ℂ).comp σ
      invFun := fun σ => (g.symm : ℂ →+* ℂ).comp σ
      left_inv := fun σ => by ext x; simp
      right_inv := fun σ => by ext x; simp }
  exact Fintype.sum_equiv eq _ _ (fun σ => by simp [eq])

theorem term_eq (σ : E →+* ℂ) (β x x' : E) (hβ : conj (σ β) = -σ β) :
    (2 * Complex.I * σ β) * (((σ x * conj (σ x')).im : ℝ) : ℂ) =
      σ (β * x * IsCMField.complexConj E x') + conj (σ (β * x * IsCMField.complexConj E x')) := by
  have e1 : σ (β * x * IsCMField.complexConj E x') = σ β * (σ x * conj (σ x')) := by
    rw [map_mul, map_mul, IsCMField.complexEmbedding_complexConj]; ring
  rw [e1, map_mul, hβ]
  have hs := Complex.sub_conj (σ x * conj (σ x'))
  push_cast at hs
  linear_combination (-σ β) * hs

end CM

end GlobalTheory.HermDiagCM

open ComplexConjugate in

theorem GlobalTheory.HermDiagCM.diagonal_of_conj_form : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) →
      ∀ (n : ℕ) (e : Fin n ≃ I) (Λ : Submodule ℤ (Fin n → ℂ)) (L : Set E),
        Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ g (φ (e j) x)) →
      ∀ (h : I → ℝ) (β : E), (∀ i, (h i : ℂ) = 2 * Complex.I * φ i β) → ∀ N : ℝ, 0 < N →
      ∀ Hm : Matrix (Fin n) (Fin n) ℂ, Hm.IsHermitian →
        (∀ x ∈ L, ∀ x' ∈ L, ((fun j ↦ g (φ (e j) x)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) x'))).im =
          N⁻¹ * ∑ i, h i * (φ i x * starRingEnd ℂ (φ i x')).im) →
        ∃ h' : I → ℝ, Hm = Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) ∧
          ∀ i, g ((h i : ℂ) * (Real.sqrt d : ℝ)) = (N : ℂ) * ((h' i : ℂ) * (Real.sqrt d : ℝ)) := by
  intro K _ _ d δ io hd hδ g hg E _ _ _ _ I _ φ hφ hio n e Λ L hs hΛ h β hh N hN Hm hHm hform
  have hconj : ∀ (σ : E →+* ℂ) (y : E), conj (σ y) = σ (IsCMField.complexConj E y) :=
    fun σ y => (IsCMField.complexEmbedding_complexConj E σ y).symm
  have hgcomp : ∀ i y, ((g : ℂ →+* ℂ).comp (φ i)) y = g (φ i y) := fun i y => rfl
  have hβi : ∀ i, conj (φ i β) = -(φ i β) := by
    intro i
    have h2 : conj ((h i : ℂ)) = (h i : ℂ) := Complex.conj_ofReal _
    rw [hh i, map_mul, map_mul, Complex.conj_I, map_ofNat] at h2
    have h3 : (2 * Complex.I : ℂ) ≠ 0 := by simp
    have h4 : (2 * Complex.I) * conj (φ i β) = (2 * Complex.I) * (-(φ i β)) := by
      linear_combination -h2
    exact mul_left_cancel₀ h3 h4
  have hcβ : ∀ i, IsCMField.complexConj E β = -β := fun i =>
    (φ i).injective (by rw [← hconj, hβi, map_neg])
  have hgc : ∀ i y, conj (g (φ i y)) = g (conj (φ i y)) := by
    intro i y
    rw [← hgcomp, hconj, hconj, hgcomp]
  have hgβ : ∀ i, conj (g (φ i β)) = -(g (φ i β)) := by
    intro i
    rw [hgc, hβi, map_neg]
  set h' : I → ℝ := fun i => ((2 * Complex.I * g (φ i β)) / N).re with hh'def
  have hh' : ∀ i, (h' i : ℂ) = 2 * Complex.I * g (φ i β) / N := by
    intro i
    exact Complex.conj_eq_iff_re.mp (by
      rw [map_div₀, map_mul, map_mul, Complex.conj_I, hgβ i, map_ofNat, Complex.conj_ofReal]; ring)
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  refine ⟨h', ?_, ?_⟩
  · set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) with hD
    suffices Hm - D = 0 from sub_eq_zero.mp this
    apply matrix_eq_zero_of_im_form (Hm - D) Λ hs
    intro v hv v' hv'
    obtain ⟨x, hx, rfl⟩ := (hΛ v).mp hv
    obtain ⟨x', hx', rfl⟩ := (hΛ v').mp hv'
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_im, hform x hx x' hx', sub_eq_zero]
    have hDv : ((fun j ↦ g (φ (e j) x)) ⬝ᵥ D.mulVec (star fun j ↦ g (φ (e j) x'))).im =
        ∑ i, h' i * (g (φ i x) * conj (g (φ i x'))).im := by
      rw [dotProduct, Complex.im_sum]
      rw [← Equiv.sum_comp e (fun i => h' i * (g (φ i x) * conj (g (φ i x'))).im)]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp only [hD, Matrix.mulVec_diagonal, Pi.star_apply, Complex.star_def]
      rw [mul_left_comm, Complex.im_ofReal_mul]
    rw [hDv]
    apply Complex.ofReal_injective
    push_cast
    simp only [hh, hh']
    set w := β * x * IsCMField.complexConj E x' with hw
    have A : ∀ i, 2 * Complex.I * g (φ i β) / N * (((g (φ i x) * conj (g (φ i x'))).im : ℝ) : ℂ) =
        (N : ℂ)⁻¹ * (g (φ i w) + conj (g (φ i w))) := by
      intro i
      have := term_eq ((g : ℂ →+* ℂ).comp (φ i)) β x x' (by rw [hgcomp]; exact hgβ i)
      simp only [hgcomp] at this
      rw [div_eq_mul_inv, mul_comm _ (N : ℂ)⁻¹, _root_.mul_assoc, this]
    have B : ∀ i, 2 * Complex.I * φ i β * (((φ i x * conj (φ i x')).im : ℝ) : ℂ) =
        φ i w + conj (φ i w) := fun i => term_eq (φ i) β x x' (hβi i)
    rw [Finset.sum_congr rfl (fun i _ => A i), Finset.sum_congr rfl (fun i _ => B i),
      ← Finset.mul_sum]
    congr 1
    rw [← sum_embeddings_eq φ hφ w, ← sum_embeddings_map g w, ← map_sum, sum_embeddings_eq φ hφ w,
      map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_add, hgc]
  · intro i
    have key : g (Complex.I * (Real.sqrt d : ℂ)) = Complex.I * (Real.sqrt d : ℂ) := by
      have hsq : (Complex.I * (Real.sqrt d : ℂ)) ^ 2 = -(d : ℂ) := by
        rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        push_cast; ring
      have hio2 : (io δ) ^ 2 = -(d : ℂ) := by rw [← map_pow, hδ, map_neg, map_natCast]
      have hprod : (io δ - Complex.I * (Real.sqrt d : ℂ)) * (io δ + Complex.I * (Real.sqrt d : ℂ)) = 0 := by
        linear_combination hio2 - hsq
      rcases mul_eq_zero.mp hprod with h1 | h1
      · have h5 : Complex.I * (Real.sqrt d : ℂ) = io δ := by linear_combination -h1
        rw [h5, hg]
      · have h5 : Complex.I * (Real.sqrt d : ℂ) = -io δ := by linear_combination h1
        rw [h5, map_neg, hg]
    rw [hh i, hh' i]
    have e2 : 2 * Complex.I * φ i β * (Real.sqrt d : ℂ) = 2 * φ i β * (Complex.I * (Real.sqrt d : ℂ)) := by
      ring
    rw [e2, map_mul, map_mul, key, map_ofNat]
    field_simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectednessStatementHoldsStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedness_statement_holds : GlobalTheory.CovTop.Hypotheses2 → ConnSt := by
  first | exact @GlobalTheory.FlatModel.connected_of_hypotheses | exact GlobalTheory.FlatModel.connected_of_hypotheses | (intros; apply GlobalTheory.FlatModel.connected_of_hypotheses <;> assumption)
end

