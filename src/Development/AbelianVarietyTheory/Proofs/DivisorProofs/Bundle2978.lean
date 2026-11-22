import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2844
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2686
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2879
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2416
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomLieEquivScalarTmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2667
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2881
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2882

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeDifferentialsAlgebraic
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CMEigen

theorem polForm_bc {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R] [CommRing R']
    (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')} {p : X'.A.left ⟶ X.A.left}
    (hX : X'.IsPullBy X (spMap σ) p) (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) p) (c : 𝔠.elt)
    {ψ : LinearMap.BilinForm R (HdR X.A)} (hψ : IsPolForm (dp0 R) (𝟙 _) X.A (X.diag c) ψ) :
    ∃ ψ' : LinearMap.BilinForm R' (HdR X'.A), IsPolForm (dp0 R') (𝟙 _) X'.A (X'.diag c) ψ' ∧
      ∀ x x' y y', m.Corr x x' → m.Corr y y' → ψ' x' y' = σ (ψ x y) := by
  obtain ⟨ψ', ⟨n, a, b, hch, he⟩, h'⟩ :=
    IsPolForm.pull_comp m (X.isLB c) (π := (lift (𝟙 X.A) (𝟙 X.A)).left) (L := X.P c) hψ
  obtain ⟨φ₂, hsq, hiso⟩ := hX.pol
  have e : (lift (𝟙 X'.A) (𝟙 X'.A)).left ≫ φ₂ = p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left := by
    apply Limits.pullback.hom_ext
    · change _ ≫ (fst X.A X.A).left = _ ≫ (fst X.A X.A).left
      rw [Category.assoc, hsq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Category.assoc, ← Over.comp_left,
        lift_fst]
      simp
    · change _ ≫ (snd X.A X.A).left = _ ≫ (snd X.A X.A).left
      rw [Category.assoc, hsq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Category.assoc, ← Over.comp_left,
        lift_snd]
      simp
  have hI : LBIso (X'.diag c) ((X.P c).pull (p ≫ (lift (𝟙 X.A) (𝟙 X.A)).left)) :=
    GlobalTheory.GenSpread.lbIso_pull_of_lbIso (hiso c) _ e.symm
  exact ⟨ψ', ⟨n, a, b, (isChern_existsUnique_and_iso _ _ _ _ _).2 _ _ (pull_isLB (X.isLB c) _)
    (pull_isLB (X'.isLB c) _) hI.symm _ hch, he⟩, h'⟩

theorem corr_inj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} (hσ : Function.Injective σ)
    {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {b : Sp R' ⟶ Sp R} {q : A'.left ⟶ A.left}
    {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b q} {x y : HdR A} {x' : HdR A'}
    (hx : m.Corr x x') (hy : m.Corr y x') : x = y :=
  LinearMap.ext fun c ↦ hσ ((hx c).symm.trans (hy c))

theorem corr_smul {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    {A : Over (Sp R)} [GrpObj A] {A' : Over (Sp R')} [GrpObj A'] {b : Sp R' ⟶ Sp R} {q : A'.left ⟶ A.left}
    {m : GrpMor (dp0 R) (𝟙 _) A (dp0 R') (𝟙 _) A' σ b q} {x : HdR A} {x' : HdR A'}
    (hx : m.Corr x x') (r : R) : m.Corr (r • x) (σ r • x') := fun c ↦ by
  simp only [LinearMap.smul_apply, smul_eq_mul, hx c, map_mul]

theorem isAlg_emb {E : Type} [Field E] [NumberField E] (τ : E →+* ℂ) (x : E) : τ x ∈ algebraicClosure ℚ ℂ := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic x).algHom τ.toRatAlgHom

set_option maxHeartbeats 1000000 in

theorem eigen_ops : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (L : Set E)
    (𝔠 : FracId (FR E)) (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (p : X.A.left ⟶ X₀.A.left)
    (U : Unif φ L 0 X) (v₀ : I → X₀.Lie) (v : I → X.Lie) (a : I → ℂ), IsCMType φ →
    X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p →
    (∀ i, Obj.LieCorr (algebraMap Qb ℂ) p (v₀ i) (v i) ∧ U.u.IsDiff (Pi.single (U.e.symm i) (a i)) (v i).hom ∧ a i ≠ 0) →
    (∀ b : E, (∀ x ∈ L, b * x ∈ L) → ∃ α : X.A ⟶ X.A, IsMonHom α ∧
      ∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
    (∀ (b : E) (α : X.A ⟶ X.A) [IsMonHom α], (∀ w', U.u.ex (fun j ↦ φ (U.e j) b * w' j) = U.u.ex w' ≫ α) →
      ∃ α₀ : X₀.A ⟶ X₀.A, IsMonHom α₀ ∧ α.left ≫ p = p ≫ α₀.left) →
    ∃ (N : I → Module.End Qb (HdR X₀.A))
      (m : GrpMor (dp0 Qb) (𝟙 _) X₀.A (dp0 ℂ) (𝟙 _) X.A (algebraMap Qb ℂ) (spMap (algebraMap Qb ℂ)) p)
      (ψ : LinearMap.BilinForm ℂ (HdR X.A)) (yv : I → HdR X.A) (w : I → ℂ),
      IsPolForm (dp0 ℂ) (𝟙 _) X.A (X.diag U.c) ψ ∧ admitted X₀ N ∧
      ∀ i, U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧ IsAlgebraic ℚ (w i / a i) ∧
        ∀ x₀ x, m.Corr x₀ x → m.Corr (N i x₀) ((ψ.flip (yv i)).smulRight (yv i) x) := by
  intro hPC hDR hDC E _ _ _ I _ φ L 𝔠 X₀ X p U v₀ v a hφ hp hv hex hdesc
  obtain ⟨y₀, yv, w, hy⟩ := GlobalTheory.T.cm_period_transcendence_relation hPC hDR hDC E I φ L 𝔠 X₀ X p U v₀ v a hp hφ hv hex hdesc
  have m := GlobalTheory.Published.AbelianDeRham.bcMor hp.grp
  have hne : ∀ i, y₀ i ≠ 0 := fun i ↦ (hy i).1
  replace hy : ∀ i, m.Corr (y₀ i) (yv i) ∧ U.IsCMVec i (yv i) (w i) ∧ w i ≠ 0 ∧ IsAlgebraic ℚ (w i / a i) :=
    fun i ↦ (hy i).2
  have hσ : Function.Injective (algebraMap Qb ℂ) := Subtype.val_injective
  obtain ⟨ψ₀, hψ₀⟩ := GlobalTheory.T.polarization_form_exists_free_de_rham hDR.1 X₀ U.c
  obtain ⟨ψ, hψ, hψc⟩ := polForm_bc (algebraMap Qb ℂ) hp m U.c hψ₀

  have eig : ∀ i (b : 𝓞 (FR E)) (β : Qb), algebraMap Qb ℂ β = φ i ((b : FR E) : E) →
      act (dp0 Qb) (𝟙 _) X₀.rm b (y₀ i) = β • y₀ i := by
    intro i b β hβ
    haveI := X₀.rm.hom b
    haveI := X.rm.hom b
    have h1 : m.Corr (act (dp0 Qb) (𝟙 _) X₀.rm b (y₀ i)) (push (dp0 ℂ) (𝟙 _) (X.rm.act b) (yv i)) := by
      rw [act_apply]
      exact GrpMor.Corr.push (m := m) m (X₀.rm.act b) (X.rm.act b) (hp.act b).symm (hy i).1
    have h2 : push (dp0 ℂ) (𝟙 _) (X.rm.act b) (yv i) = algebraMap Qb ℂ β • yv i := by
      rw [hβ]
      exact (hy i).2.1.1 _ (X.rm.act b) fun w' ↦ U.act b w'
    rw [h2] at h1
    exact corr_inj hσ h1 (corr_smul (hy i).1 β)
  have eigβ : ∀ i (b : 𝓞 (FR E)), ∃ β : Qb, algebraMap Qb ℂ β = φ i ((b : FR E) : E) := fun i b ↦
    ⟨⟨_, isAlg_emb (φ i) _⟩, rfl⟩

  have orth : ∀ (c : 𝔠.elt) (ψ' : LinearMap.BilinForm Qb (HdR X₀.A)),
      IsPolForm (dp0 Qb) (𝟙 _) X₀.A (X₀.diag c) ψ' → ∀ i j, ψ' (y₀ i) (y₀ j) = 0 := by
    intro c ψ' hψ' i j
    by_cases hij : i = j
    · subst hij; exact hψ'.isAlt _
    obtain ⟨b, hb⟩ := GlobalTheory.T.exists_ne_of_isCMType_of_ne φ hφ i j hij
    obtain ⟨βi, hβi⟩ := eigβ i b
    obtain ⟨βj, hβj⟩ := eigβ j b
    have := GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ c ψ' hψ' b (y₀ i) (y₀ j)
    rw [eig i b βi hβi, eig j b βj hβj, LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul] at this
    have hne' : βi ≠ βj := fun e ↦ hb (by rw [← hβi, ← hβj, e])
    have : (βi - βj) * ψ' (y₀ i) (y₀ j) = 0 := by rw [sub_mul, this, sub_self]
    exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')
  let N : I → Module.End Qb (HdR X₀.A) := fun i ↦ (ψ₀.flip (y₀ i)).smulRight (y₀ i)
  have hN : ∀ i x, N i x = ψ₀ x (y₀ i) • y₀ i := fun _ _ ↦ rfl
  refine ⟨N, m, ψ, yv, w, hψ, ⟨?_, ?_, ?_⟩, fun i ↦ ⟨(hy i).2.1, (hy i).2.2.1, (hy i).2.2.2, ?_⟩⟩
  · intro i b
    obtain ⟨β, hβ⟩ := eigβ i b
    refine LinearMap.ext fun x ↦ ?_
    change N i (act (dp0 Qb) (𝟙 _) X₀.rm b x) = act (dp0 Qb) (𝟙 _) X₀.rm b (N i x)
    rw [hN, hN, GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ U.c ψ₀ hψ₀, eig i b β hβ, LinearMap.map_smul, map_smul, eig i b β hβ, smul_smul,
      smul_eq_mul, mul_comm]
  · intro i j
    refine LinearMap.ext fun x ↦ ?_
    change N i (N j x) = 0
    rw [hN, hN, LinearMap.map_smul₂, orth U.c ψ₀ hψ₀ j i, smul_zero, zero_smul]
  · intro c ψ' hψ'
    refine ⟨fun i x y ↦ ?_, fun i j x y ↦ ?_⟩
    · rw [hN, hN, LinearMap.map_smul₂, LinearMap.map_smul, smul_eq_mul, smul_eq_mul]
      have h0 : (ψ₀ (y₀ i)) (y₀ i) = 0 := hψ₀.isAlt (y₀ i)
      have h0' : (ψ' (y₀ i)) (y₀ i) = 0 := hψ'.isAlt (y₀ i)
      have hr := GlobalTheory.T.cm_periods_algebraic_nonzero hPC hDR E I φ L 𝔠 X₀ X p U hφ hp i (y₀ i) (hne i) (eig i) (ψ₀ (y₀ i)) (ψ' (y₀ i))
        h0 h0' (fun b β hβ z ↦ ⟨by
          rw [← GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ U.c ψ₀ hψ₀, eig i b β hβ, LinearMap.map_smul₂, smul_eq_mul], by
          rw [← GlobalTheory.T.polarization_form_ring_action_symmetric hDR hDC X₀ c ψ' hψ', eig i b β hβ, LinearMap.map_smul₂, smul_eq_mul]⟩) x y
      have a1 : ψ₀ x (y₀ i) = - ψ₀ (y₀ i) x := (LinearMap.IsAlt.neg hψ₀.isAlt (y₀ i) x).symm
      have a2 : ψ₀ y (y₀ i) = - ψ₀ (y₀ i) y := (LinearMap.IsAlt.neg hψ₀.isAlt (y₀ i) y).symm
      have a3 : ψ' x (y₀ i) = - ψ' (y₀ i) x := (LinearMap.IsAlt.neg hψ'.isAlt (y₀ i) x).symm
      rw [a1, a2, a3]
      linear_combination -hr
    · rw [hN, hN, LinearMap.map_smul₂, LinearMap.map_smul, orth c ψ' hψ' i j]
      simp
  · intro x₀ x hx
    have h1 := corr_smul (m := m) (hy i).1 (ψ₀ x₀ (y₀ i))
    rw [← hψc x₀ x (y₀ i) (yv i) hx (hy i).1] at h1
    exact h1

end GlobalTheory.CMEigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmUniformizationAlgebraicModel
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

section ModelOver

open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.BirigidLift

namespace GlobalTheory.CMModel

theorem exists_obj_of_isGrpPullback_over (HD : GlobalTheory.Published.DualAbelianScheme) {F : Type} [Field F] [NumberField F]
    {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (c₀ : 𝔠.elt) (hc₀ : IsTotPos (c₀ : F)) (A₀ : Over (Sp Qb)) [GrpObj A₀]
    (p : X.A.left ⟶ A₀.left) (hA₀ : IsAbelianScheme A₀) (gA₀ : SmoothOfRelativeDimension (Module.finrank ℚ F) A₀.hom)
    (hp : IsGrpPullback X.A A₀ (spMap (algebraMap Qb ℂ)) p) {S₀ : Scheme.{0}} (G₀ : Over S₀) [GrpObj G₀]
    (b : Sp Qb ⟶ S₀) (g : A₀.left ⟶ G₀.left) (hg : IsGrpPullback A₀ G₀ b g) :
    ∃ (X₀ : Obj F 𝔠 (Sp Qb)) (p' : X.A.left ⟶ X₀.A.left) (g' : X₀.A.left ⟶ G₀.left),
      X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p' ∧ IsGrpPullback X₀.A G₀ b g' ∧ p' ≫ g' = p ≫ g := by
  haveI : Flat (spMap (algebraMap Qb ℂ)) := Flat.SpecMap_iff.2 (by
    letI := (algebraMap Qb ℂ).toAlgebra
    exact (inferInstance : Module.Flat Qb ℂ))
  haveI : Surjective (spMap (algebraMap Qb ℂ)) := ⟨fun x ↦ ⟨(inferInstance : Nonempty (PrimeSpectrum ℂ)).some,
    Subsingleton.elim (α := PrimeSpectrum Qb) _ _⟩⟩
  haveI := hA₀.comm
  obtain ⟨rm, hrm⟩ := ActDescent.exists_oAct hp X.rm fun a ↦ by
    obtain ⟨f, -, hf⟩ := GlobalTheory.HomDescentQb.hom_descends A₀ A₀ X.A X.A p p _ _ hA₀ gA₀ hA₀ gA₀ hp hp (X.rm.act a) (X.rm.hom a)
    exact ⟨f, hf⟩
  obtain ⟨D₀, _, Q, D, _, d, m, hD₀, gD₀, q₀, q₀', hd, m₁, m₂, q, q'⟩ := exists_dual_pair HD hA₀ gA₀ hp
  obtain ⟨l, l₁, l₂⟩ := exists_prod_pullback hp hp
  obtain ⟨H, hH, aH⟩ := exists_relAmple_prod X.ab X.ab (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
    (pull_isLB (X.isLB c₀) _) (X.pos c₀ hc₀)
  have hx : ∀ c : 𝔠.elt, ∃ P₀ : LB (A₀ ⊗ A₀).left, ∃ h : P₀.IsLB, IsAdditive P₀ ∧ IsAdditive (swap P₀) ∧
      CechPic.pull l (cls P₀ h) = cls (X.P c) (X.isLB c) := fun c ↦ by
    obtain ⟨a₁, a₂⟩ := additive_of_triv X.ab X.ab hH aH (X.isLB c) (X.rig₁ c) (X.rig₂ c)
    obtain ⟨x, hx, ex⟩ := exists_hom q q' (X.isLB c) a₁ a₂
    obtain ⟨x₀, hx₀, e₀⟩ := GlobalTheory.HomDescentQb.hom_descends A₀ D₀ X.A D p d _ _ hA₀ gA₀ hD₀ gD₀ hp hd x hx
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
            ker := fun c T₀ x hx a ha ↦ ?_ }, p, g, ⟨hp, hrm, l, ⟨l₁, l₂⟩, fun c ↦ ?_⟩, hg, rfl⟩
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

end GlobalTheory.CMModel

end ModelOver

namespace GlobalTheory.CMModel

open GlobalTheory.ComplexPoints
open scoped CategoryTheory.Obj

theorem exists_qbModel_of_subring : GlobalTheory.Published.AbelianDualCrystal →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (c : Ideal (OF E))
    (L : Set E) (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X),
    (∀ a : orderC c, ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (R₀ : Subring ℂ) (σ : R₀ →+* Qb), (∀ x, ((σ x : Qb) : ℂ) = x) →
    ∀ (G₀ : Over (Sp R₀)) [GrpObj G₀] (p₀ : X.A.left ⟶ G₀.left), IsAbelianScheme G₀ →
      IsGrpPullback X.A G₀ (spMap R₀.subtype) p₀ →
    ∃ (XQ : Obj (FR E) 𝔠 (Sp Qb)) (pQ : X.A.left ⟶ XQ.A.left) (gQ : XQ.A.left ⟶ G₀.left) (cmQ : OAct (orderC c) XQ.A),
      X.IsPullBy XQ (spMap (algebraMap Qb ℂ)) pQ ∧ IsGrpPullback XQ.A G₀ (spMap σ) gQ ∧ pQ ≫ gQ = p₀ ∧
      (∀ a : OF E, cmQ.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF c a) = XQ.rm.act a) ∧
      ∀ (a : orderC c) (α : X.A ⟶ X.A), IsMonHom α →
        (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α.left ≫ pQ = pQ ≫ (cmQ.act a).left := by
  intro HD E _ _ _ I _ φ c L 𝔠 X U hα R₀ σ hσ G₀ _ p₀ _ hpb

  haveI : Flat (spMap (algebraMap Qb ℂ)) := Flat.SpecMap_iff.2 (by
    letI := (algebraMap Qb ℂ).toAlgebra
    exact (inferInstance : Module.Flat Qb ℂ))
  haveI : Surjective (spMap (algebraMap Qb ℂ)) := ⟨fun x ↦ ⟨(inferInstance : Nonempty (PrimeSpectrum ℂ)).some,
    Subsingleton.elim (α := PrimeSpectrum Qb) _ _⟩⟩
  have hring : R₀.subtype = (algebraMap Qb ℂ).comp σ := RingHom.ext fun x ↦ (hσ x).symm
  have hcomp : spMap R₀.subtype = spMap (algebraMap Qb ℂ) ≫ spMap σ := by
    rw [hring]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  let A₀ : Over (Sp Qb) := (Over.pullback (spMap σ)).obj G₀
  letI : GrpObj A₀ := inferInstanceAs (GrpObj ((Over.pullback (spMap σ)).obj G₀))
  have hA₀G : IsGrpPullback A₀ G₀ (spMap σ) (pullback.fst G₀.hom (spMap σ)) := isGrpPullback_pullback G₀ (spMap σ)
  let p : X.A.left ⟶ A₀.left := pullback.lift p₀ (X.A.hom ≫ spMap (algebraMap Qb ℂ)) (by
    rw [Category.assoc, ← hcomp]; exact hpb.1.w)
  have hp₁ : p ≫ pullback.fst G₀.hom (spMap σ) = p₀ := pullback.lift_fst _ _ _
  have hp₂ : p ≫ A₀.hom = X.A.hom ≫ spMap (algebraMap Qb ℂ) := pullback.lift_snd _ _ _
  have hp : IsGrpPullback X.A A₀ (spMap (algebraMap Qb ℂ)) p :=
    IsGrpPullback.cancel hA₀G (by rw [hp₁, ← hcomp]; exact hpb) hp₂
  obtain ⟨hA₀, hdim⟩ := GlobalTheory.FieldDescentAb.isAbelianScheme_and_relDim_descend Qb ℂ (algebraMap Qb ℂ) A₀ X.A p hp X.ab

  obtain ⟨XQ, pQ, gQ, hXQ, hgQ, hpg⟩ := exists_obj_of_isGrpPullback_over HD.1 X U.c U.pos A₀ p hA₀ (hdim _ X.dim) hp
    G₀ (spMap σ) _ hA₀G

  let ρ : orderC c →+* Module.End ℂ (Fin (Module.finrank ℚ (FR E)) → ℂ) :=
    (Algebra.lmul ℂ (Fin (Module.finrank ℚ (FR E)) → ℂ)).toRingHom.comp
      ((Pi.ringHom fun j ↦ φ (U.e j)).comp (orderC c).subtype)
  have hρ : ∀ a w, ρ a w = fun j ↦ φ (U.e j) (a : E) * w j := fun a w ↦ rfl
  have hlat : ∀ a, ∀ z ∈ U.u.Λ, ρ a z ∈ U.u.Λ := fun a z hz ↦ by
    obtain ⟨α, hαm, hαe⟩ := hα a
    haveI := hαm
    rw [← U.u.ker] at hz ⊢
    rw [hρ, hαe, hz, MonObj.one_comp]
  obtain ⟨act, hact⟩ := GlobalTheory.TorusAction.exists_oAct_of_map_lattice _ X.A X.ab _ U.u (orderC c) ρ hlat
  haveI := X.ab.smooth
  haveI := X.ab.proper
  haveI : IsReduced X.A.left := isReduced_of_smooth_complex _ X.A.hom X.ab.smooth
  have hext : ∀ f f' : X.A ⟶ X.A, (∀ z, U.u.ex z ≫ f = U.u.ex z ≫ f') → f = f' := fun f f' h ↦
    over_hom_ext_of_complexPoints fun x ↦ by
      obtain ⟨z, rfl⟩ := U.u.ex_onto x
      exact h z
  have huniq : ∀ (a : orderC c) (α : X.A ⟶ X.A),
      (∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) → α = act.act a := fun a α h ↦
    hext _ _ fun z ↦ by rw [← h, ← hact, hρ]

  obtain ⟨cmQ, hcm⟩ := GlobalTheory.ActDescent.exists_oAct hXQ.grp act fun a ↦ by
    haveI := act.hom a
    obtain ⟨β, -, hβ⟩ := GlobalTheory.RealMult.Obj.exists_end_descend_algebraic _ _ XQ X pQ hXQ (act.act a)
    exact ⟨β, hβ⟩
  refine ⟨XQ, pQ, gQ, cmQ, hXQ, hgQ, by rw [hpg, hp₁], fun a ↦ ?_, fun a α _ h ↦ ?_⟩
  · refine GlobalTheory.ActDescent.over_hom_ext hXQ.grp.1 ?_
    rw [← hcm, ← hXQ.act a]
    congr 2
    exact (huniq _ _ (U.act a)).symm
  · rw [huniq a α h]
    exact hcm a

end GlobalTheory.CMModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientGermsZeroFiniteFreeBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_germs_zero_finiteFree_baseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ₁ : R →+* R₁) (d : ℕ) (b : Fin d → R₁), (∀ r : R₁, ∃! c : Fin d → R, r = ∑ l, ρ₁ (c l) * b l) → ∀ (X : Scheme.{0}) (f : X ⟶ Sp R) (U : X.Opens) (a : Fin d → Γ(X, U)) (x : X), x ∈ U → (∀ z : (pullback f (spMap ρ₁) : Scheme.{0}), (pullback.fst f (spMap ρ₁)) z = x → ∑ l, gs (pullback.snd f (spMap ρ₁)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (b l)) * gs (pullback.fst f (spMap ρ₁)) z U (a l) = 0) → ∀ l, gs (𝟙 X) x U (a l) = 0 := by
  first | exact @GlobalTheory.Mum.FreeCoord.germ_eq_zero | exact GlobalTheory.Mum.FreeCoord.germ_eq_zero | (intros; apply GlobalTheory.Mum.FreeCoord.germ_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientSpecRestrictionCompatibleStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_spec_restriction_compatible : ∀ (M : Scheme.{0}) (W W' : M.Opens) (hW : IsAffineOpen W) (hW' : IsAffineOpen W') (hle : W' ≤ W)
    (R₀ : Type) [CommRing R₀],
    spMap (Algebra.TensorProduct.map (AlgHom.id R₀ R₀) (M.presheaf.map (homOfLE hle).op).hom.toIntAlgHom :
      R₀ ⊗[ℤ] Γ(M, W) →ₐ[R₀] R₀ ⊗[ℤ] Γ(M, W')).toRingHom ≫ coefSpecMap hW R₀ = coefSpecMap hW' R₀ := by
  first | exact @GlobalTheory.RealMult.spMap_restrict_comp_coefSpecMap | exact GlobalTheory.RealMult.spMap_restrict_comp_coefSpecMap | (intros; apply GlobalTheory.RealMult.spMap_restrict_comp_coefSpecMap <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfPullbackInjectiveDomainsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comesFromBase_of_pullback_injective_domains : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (J : Ideal R) (D₀ : DegData R J) (ω : W →+* R) (s : I → R) (e : D₀.toPre.X ≃+ (Fin T.r → ℤ)) (β : D₀.toPre.P.A.left ⟶ T.B.left) (ββ : (G2 D₀.toPre.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D₀.toPre.P.A D₀.toPre.P.L) ((abelian₂ T.B T.M.L).pull ββ)) (f : R →+* V) (D : DegPre V) (hD : IsPullDeg f D₀.toPre D), Function.Injective f → From T ω s ε n D₀.toPre e β ββ w → ∃ ββ' w', From T (f.comp ω) (fun i => f (s i)) ε n D (hD.xe.trans e) ((hD.e.hom.left ≫ pullback.fst D₀.toPre.P.A.hom (specOf f)) ≫ β) ββ' w' := by
  first | exact @GlobalTheory.TInj.from_pull | exact GlobalTheory.TInj.from_pull | (intros; apply GlobalTheory.TInj.from_pull <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComesFromBaseOfRefinesPolarisedDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comesFromBase_of_refines_polarisedData : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (R : Type) [CommRing R] [IsDomain R] (V : Type) [CommRing V] [IsDomain V] (ρ : R →+* V) (ω : W →+* R) (s : I → R) (Q : Data R) (e : Q.X ≃+ (Fin T.r → ℤ)) (D : DegPre V) (e' : D.X ≃+ Q.X), Function.Injective ρ → DataFrom T ω s ε n Q e → Refines Q ρ D e' → ∃ β ββ w, From T (ρ.comp ω) (fun i => ρ (s i)) ε n D (e'.trans e) β ββ w := by
  first | exact @GlobalTheory.TInj.FromRefine.from_of_refines | exact GlobalTheory.TInj.FromRefine.from_of_refines | (intros; apply GlobalTheory.TInj.FromRefine.from_of_refines <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommonRefinementCoversStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.common_refinement_covers : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V₁ V₂ : Cover Y), ∃ (V : Cover Y) (π₁ : V.X ⟶ V₁.X) (π₂ : V.X ⟶ V₂.X), π₁ ≫ V₁.p = V.p ∧ π₂ ≫ V₂.p = V.p ∧ Lies V V₁ π₁ ∧ Lies V V₂ π₂ := by
  first | exact @GlobalTheory.CoverCommon.exists_cover_dominating_two | exact GlobalTheory.CoverCommon.exists_cover_dominating_two | (intros; apply GlobalTheory.CoverCommon.exists_cover_dominating_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompleteSymmetricMulDifferenceStatement
section
open MvPolynomial GlobalTheory.LineForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complete_symmetric_mul_difference : ∀ k : ℕ, aeval ![X 0 + X 1, X 0 * X 1] (hs k) * (X 0 - X 1) = (X 0 ^ (k + 1) - X 1 ^ (k + 1) : MvPolynomial (Fin 2) ℝ) := by
  first | exact @GlobalTheory.LineForm.aeval_hs_mul_sub | exact GlobalTheory.LineForm.aeval_hs_mul_sub | (intros; apply GlobalTheory.LineForm.aeval_hs_mul_sub <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompletionGaloisInvariantsAgreeModMaxIdealPowStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completion_galoisInvariants_agree_mod_maxIdeal_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → IsGal (algebraMap R R') → ∀ (C' : Type) [CommRing C'] [Algebra R C'] [Algebra R' C'] [IsScalarTower R R' C'] [Algebra.FiniteType R' C'] (act : Gal (algebraMap R R') →* (C' ≃ₐ[R] C')), (∀ σ r, act σ (algebraMap R' C' r) = algebraMap R' C' (σ.1 r)) → ∀ (O : Type) [CommRing O] [Algebra R O] [Module.Flat R O] [Algebra.FiniteType R O] (i : ∀ e : ℕ, O →ₐ[R] C' ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C')), (∀ e x y, Ideal.Quotient.mk _ y = i (e + 1) x → Ideal.Quotient.mk _ y = i e x) → (∀ e σ x y, Ideal.Quotient.mk _ y = i e x → Ideal.Quotient.mk _ (act σ y) = i e x) → (∀ e, Function.Surjective (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) ∧ RingHom.ker (Algebra.TensorProduct.lift (i e) ((Ideal.Quotient.mkₐ R _).comp (IsScalarTower.toAlgHom R R' C')) fun _ _ => Commute.all _ _) = (maximalIdeal R ^ (e + 1)).map (algebraMap R (TensorProduct R O R'))) → ∀ C : Subalgebra R C', (∀ x, x ∈ C ↔ ∀ σ, act σ x = x) → Algebra.FiniteType R C → Module.Finite C C' → ∀ e : ℕ, ∃ gm : (O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)), ∀ (x : O) (c : C), gm (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ c → Ideal.Quotient.mk ((maximalIdeal R ^ (e + 1)).map (algebraMap R C')) (c : C') = i e x := by
  first | exact @GlobalTheory.InvAlg.completion_invariants_agree | exact GlobalTheory.InvAlg.completion_invariants_agree | (intros; apply GlobalTheory.InvAlg.completion_invariants_agree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexSymmetricAmpleSquareDecompositionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_symmetricAmple_square_decomposition : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → ∀ (L M : LB A.left), L.IsLB → M.IsLB → RelAmple A L → RelAmple A M → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso (M.pull (GrpObj.inv : A ⟶ A).left) M → SqDec A L M := by
  first | exact @GlobalTheory.SqDecC.sqDec_complex | exact GlobalTheory.SqDecC.sqDec_complex | (intros; apply GlobalTheory.SqDecC.sqDec_complex <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsDelOperatorDbarOperatorStatement
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffOn_coefficients_delOperator_dbarOperator : ∀ (n : ℕ) (s : Set (V n)) (F : V n → Alt n), IsOpen s →
    (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
    ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (delAt F v) S) s ∧ ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt F v) S) s := by
  first | exact @GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef | exact GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef | (intros; apply GlobalTheory.CxForm.SmoothCoef.contDiffOn_coef <;> assumption)
end

