import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0592
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LatticeDeterminedByInvariants
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.WeierstrassCurvePointOfLatticeAddOfGeneric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqZeroOfFderivEqZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0562
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2792
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistFunctionDecomposition
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
open GlobalTheory.CMTorsion
open GlobalTheory.WeierstrassCurve (scheme toSpec mapHom)

namespace GlobalTheory.CMTorsion.Conj

open PeriodPair

theorem ptHom_eq_iff_of_eq {W : WeierstrassCurve ℂ} {ρ ρ' : ℂ →+* ℂ} (e : ρ = ρ') {P Q : Fin 3 → ℂ}
    (hP : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ) P)
    (hQ : GlobalTheory.WeierstrassCurve.IsUnimodularSol (W.map ρ') Q) :
    GlobalTheory.WeierstrassCurve.ptHom W ρ P hP = GlobalTheory.WeierstrassCurve.ptHom W ρ' Q hQ ↔
      ∃ v : ℂˣ, Q = (v : ℂ) • P := by
  subst e
  exact GlobalTheory.WeierstrassCurve.ptHom_eq_ptHom_iff W hP hQ

theorem rel_iff (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (g : ℂ ≃+* ℂ) (hΩ₀ : Ω₀ ≠ 0) (hΩ₁ : Ω₁ ≠ 0)
    (h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁) (z z' : ℂ) :
    (pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z) ↔
      GlobalTheory.ConjPoint.IsConj (GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀) (GlobalTheory.scalePeriods Λ₁ Ω₁ hΩ₁) g
        (Ω₀ * z) (Ω₁ * z') := by
  have H₀ := GlobalTheory.isHomothetic_scalePeriods Λ₀ Ω₀ hΩ₀
  have H₁ := GlobalTheory.isHomothetic_scalePeriods Λ₁ Ω₁ hΩ₁
  unfold pt
  rw [GlobalTheory.WeierstrassCurve.ptHom_mapHom, spMap, GlobalTheory.WeierstrassCurve.SpecMap_ptHom,
    ptHom_eq_iff_of_eq ((RingHom.id_comp _).trans (RingHom.comp_id _).symm)]
  unfold GlobalTheory.ConjPoint.IsConj
  rw [H₀ z, H₁ z', H₀.weierstrassP_mul, H₁.weierstrassP_mul, H₀.derivWeierstrassP_mul,
    H₁.derivWeierstrassP_mul]
  by_cases hz : z ∈ Λ₀.lattice <;> by_cases hz' : z' ∈ Λ₁.lattice
  · simp only [coords, hz, hz', if_true]
    refine iff_of_true ⟨1, ?_⟩ (Or.inl ⟨trivial, trivial⟩)
    ext i; fin_cases i <;> simp
  · simp only [coords, hz, hz', if_true, if_false]
    refine iff_of_false ?_ (by tauto)
    rintro ⟨v, hv⟩
    have := congrFun hv 2
    simp at this
    exact v.ne_zero this.symm
  · simp only [coords, hz, hz', if_true, if_false]
    refine iff_of_false ?_ (by tauto)
    rintro ⟨v, hv⟩
    have := congrFun hv 2
    simp at this
  · simp only [coords, hz, hz', if_false, not_false_iff, true_and, false_and, false_or]
    constructor
    · rintro ⟨v, hv⟩
      have h2 := congrFun hv 2
      have h0 := congrFun hv 0
      have h1 := congrFun hv 1
      have g2 : g 2 = 2 := map_ofNat g 2
      simp [g2] at h0 h1 h2
      rw [← h2] at h0 h1
      simp only [map_mul, map_inv₀, map_pow]
      constructor
      · linear_combination -h0
      · linear_combination -2 * h1
    · rintro ⟨e1, e2⟩
      simp only [map_mul, map_inv₀, map_pow] at e1 e2
      refine ⟨1, ?_⟩
      funext i
      have g2 : g 2 = 2 := map_ofNat g 2
      fin_cases i <;> simp [g2] <;> first | linear_combination -e1 | linear_combination (-1/2 : ℂ) * e2

theorem pt_conj_onto_add : ∀ (Λ₀ Λ₁ : PeriodPair) (Ω₀ Ω₁ : ℂ) (g : ℂ ≃+* ℂ), Ω₀ ≠ 0 → Ω₁ ≠ 0 → ∀ h : (curve Λ₀ Ω₀).map (g : ℂ →+* ℂ) = curve Λ₁ Ω₁, (∀ z', ∃ z, pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z) ∧ ∀ z w z' w', pt Λ₁ Ω₁ z' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ z → pt Λ₁ Ω₁ w' ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ w → pt Λ₁ Ω₁ (z' + w') ≫ mapHom (curve Λ₀ Ω₀) (g : ℂ →+* ℂ) h = spMap (g : ℂ →+* ℂ) ≫ pt Λ₀ Ω₀ (z + w) := by
  intro Λ₀ Λ₁ Ω₀ Ω₁ g hΩ₀ hΩ₁ h
  have H₀ := GlobalTheory.isHomothetic_scalePeriods Λ₀ Ω₀ hΩ₀
  have H₁ := GlobalTheory.isHomothetic_scalePeriods Λ₁ Ω₁ hΩ₁
  have g4 : g 4 = 4 := map_ofNat g 4
  have e₄ := congrArg WeierstrassCurve.a₄ h
  have e₆ := congrArg WeierstrassCurve.a₆ h
  simp [curve, g4] at e₄ e₆
  have h₂ : (GlobalTheory.scalePeriods Λ₁ Ω₁ hΩ₁).g₂ = g (GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀).g₂ := by
    rw [H₁.g₂_eq, H₀.g₂_eq, map_mul, map_inv₀, map_pow]
    linear_combination -e₄
  have h₃ : (GlobalTheory.scalePeriods Λ₁ Ω₁ hΩ₁).g₃ = g (GlobalTheory.scalePeriods Λ₀ Ω₀ hΩ₀).g₃ := by
    rw [H₁.g₃_eq, H₀.g₃_eq, map_mul, map_inv₀, map_pow]
    linear_combination -e₆
  obtain ⟨s, -, hs⟩ := GlobalTheory.ConjPoint.exists_conjEquiv h₂ h₃
  have R := rel_iff Λ₀ Λ₁ Ω₀ Ω₁ g hΩ₀ hΩ₁ h
  refine ⟨fun z' => ?_, fun z w z' w' hz hw => ?_⟩
  · obtain ⟨t, ht⟩ := GlobalTheory.latticePoint_surjective _ (s.symm (GlobalTheory.latticePoint _ (Ω₁ * z')))
    refine ⟨Ω₀⁻¹ * t, (R _ _).2 ((hs _ _).2 ?_)⟩
    rw [← _root_.mul_assoc, mul_inv_cancel₀ hΩ₀, _root_.one_mul, ht, AddEquiv.apply_symm_apply]
  · rw [R, hs] at hz hw ⊢
    rw [_root_.mul_add, _root_.mul_add, GlobalTheory.latticePoint_add, GlobalTheory.latticePoint_add, map_add, hz, hw]

end GlobalTheory.CMTorsion.Conj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateUniformizationSemilinearMap
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.ConjTangentSemilin

open GlobalTheory.ArchMetricCompare

variable {A A' : Over (Sp ℂ)} [GrpObj A] [GrpObj A'] {p : A'.left ⟶ A.left} {g : ℂ ≃+* ℂ}

theorem isIso_spMap (g : ℂ ≃+* ℂ) : IsIso (spMap (g : ℂ →+* ℂ)) := by
  have : IsIso (CommRingCat.ofHom (g : ℂ →+* ℂ)) :=
    ⟨⟨CommRingCat.ofHom (g.symm : ℂ →+* ℂ), by ext; simp, by ext; simp⟩⟩
  unfold spMap
  infer_instance

theorem snd_pull [IsIso p] {L : LB A.left} {N : ℕ} (u : HolUnif A L N) {v : epsR ℂ ⟶ A} {v' : epsR ℂ ⟶ A'}
    (e : v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) {w : Fin N → ℂ} (hd : u.IsDiff w v)
    (U : A'.left.Opens) (hU : ⊤ ≤ v'.left ⁻¹ᵁ U) (f : Γ(A'.left, U)) :
    (TangentOrigin.evalPt (R := DualNumber ℂ) v'.left U hU f).snd =
      g (fderiv ℂ (fun z => valAt' (u.ex z).left (inv p ⁻¹ᵁ U) (((inv p).app U).hom f)) 0 w) := by
  have e2 : v'.left = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫
      (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p := by
    rw [← Category.assoc]
    exact (IsIso.eq_comp_inv p).2 e
  have h2 : ⊤ ≤ v.left ⁻¹ᵁ (inv p ⁻¹ᵁ U) := fun q _ => by
    have := subsingleton_dual ℂ
    have hq := hU (show q ∈ (⊤ : (Sp (DualNumber ℂ)).Opens) from trivial)
    rw [e2] at hq
    rw [Subsingleton.elim (α := PrimeSpectrum (DualNumber ℂ)) q
      (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) q)]
    exact hq
  have k : ∀ (y : Sp (DualNumber ℂ) ⟶ A'.left) (hy : ⊤ ≤ y ⁻¹ᵁ U),
      y = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ (show Sp (DualNumber ℂ) ⟶ _ from v.left) ≫ inv p →
      TangentOrigin.evalPt y U hy f = Chart.dualMapR (g : ℂ →+* ℂ)
        (TangentOrigin.evalPt (R := DualNumber ℂ) v.left _ h2 (((inv p).app U).hom f)) := by
    rintro _ hy rfl
    rw [TangentOrigin.evalPt_spMap_comp _ _ U h2]
    congr 1
  rw [k _ hU e2]
  have e3 := hd _ h2 (((inv p).app U).hom f)
  simp only [Chart.dualMapR, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, TrivSqZeroExt.snd_add,
    TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact congrArg g e3

def Rel {L : LB A.left} {L' : LB A'.left} {N : ℕ} (p : A'.left ⟶ A.left) [IsIso p] (g : ℂ ≃+* ℂ)
    (u : HolUnif A L N) (u' : HolUnif A' L' N) (w' w : Fin N → ℂ) : Prop :=
  ∀ (U : A'.left.Opens), ⊤ ≤ (u'.ex 0).left ⁻¹ᵁ U → ∀ f : Γ(A'.left, U),
    fderiv ℂ (fun z => valAt' (u'.ex z).left U f) 0 w' =
      g (fderiv ℂ (fun z => valAt' (u.ex z).left (inv p ⁻¹ᵁ U) (((inv p).app U).hom f)) 0 w)

theorem isDiff_iff_rel [IsIso p] (h : IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p) {L : LB A.left} {L' : LB A'.left}
    {N : ℕ} (u : HolUnif A L N) (u' : HolUnif A' L' N) {v : epsR ℂ ⟶ A} {v' : epsR ℂ ⟶ A'} (hv : IsTangent v)
    (e : v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) {w : Fin N → ℂ} (hd : u.IsDiff w v)
    (w' : Fin N → ℂ) : u'.IsDiff w' v' ↔ Rel p g u u' w' w := by
  have hv' : IsTangent v' := isTangent_of_pull (σ := (g : ℂ →+* ℂ)) h hv e
  constructor
  · intro hd' U hU f
    have hU' := (TangentOrigin.tangent_mem_iff (u := u') hv' U).2 hU
    exact (hd' U hU' f).symm.trans (snd_pull u e hd U hU' f)
  · intro hr U hU f
    exact (snd_pull u e hd U hU f).trans
      (hr U ((TangentOrigin.tangent_mem_iff (u := u') hv' U).1 hU) f).symm

theorem rel_add [IsIso p] {L : LB A.left} {L' : LB A'.left} {N : ℕ} (u : HolUnif A L N) (u' : HolUnif A' L' N)
    {w₁' w₁ w₂' w₂ : Fin N → ℂ} (h₁ : Rel p g u u' w₁' w₁) (h₂ : Rel p g u u' w₂' w₂) :
    Rel p g u u' (w₁' + w₂') (w₁ + w₂) := fun U hU f => by
  rw [map_add, map_add, map_add, h₁ U hU f, h₂ U hU f]

theorem rel_smul [IsIso p] {L : LB A.left} {L' : LB A'.left} {N : ℕ} (u : HolUnif A L N) (u' : HolUnif A' L' N)
    {w' w : Fin N → ℂ} (c : ℂ) (h₁ : Rel p g u u' w' w) : Rel p g u u' (g c • w') (c • w) := fun U hU f => by
  rw [map_smul, map_smul, h₁ U hU f, smul_eq_mul, smul_eq_mul, map_mul]

theorem pull_sq (g : ℂ ≃+* ℂ) (v : epsR ℂ ⟶ A) :
    (spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left) ≫ A.hom = (epsR ℂ).hom ≫ spMap (g : ℂ →+* ℂ) := by
  rw [Category.assoc, Over.w]
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

def liftT (h : IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p) (v : epsR ℂ ⟶ A) : epsR ℂ ⟶ A' :=
  Over.homMk (h.1.lift _ _ (pull_sq g v)) (h.1.lift_snd _ _ _)

theorem liftT_left (h : IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p) (v : epsR ℂ ⟶ A) :
    (liftT h v).left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left :=
  h.1.lift_fst _ _ _

theorem exists_semilinear_transport : ∀ (A A' : Over (Sp ℂ)) [GrpObj A] [GrpObj A'] (p : A'.left ⟶ A.left) (g : ℂ ≃+* ℂ),
    IsGrpPullback A' A (spMap (g : ℂ →+* ℂ)) p → ∀ (L : LB A.left) (L' : LB A'.left) (N : ℕ) (u : HolUnif A L N)
    (u' : HolUnif A' L' N), (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → (∀ v, IsTangent v → ∃! w, u'.IsDiff w v) →
    ∃ T : (Fin N → ℂ) →ₛₗ[(g : ℂ →+* ℂ)] (Fin N → ℂ), Function.Injective T ∧
      ∀ (w : Fin N → ℂ) (v : epsR ℂ ⟶ A) (v' : epsR ℂ ⟶ A'), IsTangent v →
        v'.left ≫ p = spMap (Chart.dualMapR (g : ℂ →+* ℂ)) ≫ v.left → u.IsDiff w v → u'.IsDiff (T w) v' := by
  intro A A' _ _ p g h L L' N u u' hex huniq
  haveI := isIso_spMap g
  haveI : IsIso p := h.1.isIso_fst_of_isIso
  choose vv hvv using fun w => (hex w).exists
  have ht : ∀ w, IsTangent (liftT h (vv w)) := fun w =>
    isTangent_of_pull (σ := (g : ℂ →+* ℂ)) h (hvv w).1 (liftT_left h _)
  choose T hT using fun w => (huniq _ (ht w)).exists
  have hR : ∀ w, Rel p g u u' (T w) w := fun w =>
    (isDiff_iff_rel h u u' (hvv w).1 (liftT_left h _) (hvv w).2 _).1 (hT w)
  have hU : ∀ w w', Rel p g u u' w' w → T w = w' := fun w w' hr =>
    (huniq _ (ht w)).unique (hT w) ((isDiff_iff_rel h u u' (hvv w).1 (liftT_left h _) (hvv w).2 _).2 hr)
  let Tl : (Fin N → ℂ) →ₛₗ[(g : ℂ →+* ℂ)] (Fin N → ℂ) :=
    { toFun := T
      map_add' := fun a b => hU _ _ (rel_add u u' (hR a) (hR b))
      map_smul' := fun c a => hU _ _ (rel_smul u u' c (hR a)) }
  refine ⟨Tl, ?_, ?_⟩
  · refine (injective_iff_map_eq_zero Tl).2 fun w hw => ?_
    have hw' : T w = 0 := hw
    have h0 : u'.IsDiff 0 (liftT h (vv w)) := by rw [← hw']; exact hT w
    have e1 := eq_of_isDiff u' (ht w) (isTangent_zero A') h0 (isDiff_zero u')
    have e2 := (zero_pull_iff (σ := (g : ℂ →+* ℂ)) h (liftT_left h (vv w))).1 e1
    have hd := (hvv w).2
    rw [e2] at hd
    exact eq_zero_of_isDiff u hd
  · intro w v v' hv e hd
    exact (isDiff_iff_rel h u u' hv e hd _).2 (hR w)

end GlobalTheory.ConjTangentSemilin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsDelOperatorDbarOperator
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.SmoothCoef

theorem contDiffOn_del_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => del f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [del_apply]
  exact ((h.clm_apply contDiffOn_const).sub ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_dbar_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => dbar f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [dbar_apply]
  exact ((h.clm_apply contDiffOn_const).add ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_coef : ∀ (n : ℕ) (s : Set (V n)) (F : V n → Alt n), IsOpen s →
    (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
    ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (delAt F v) S) s ∧
      ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt F v) S) s := by
  intro n s F hs hF U
  constructor
  · simp only [delAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_del_dir hs (hF S) _).mul contDiffOn_const
  · simp only [dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum,
      Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
    exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_dbar_dir hs (hF S) _).mul contDiffOn_const

end GlobalTheory.CxForm.SmoothCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderiv
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

namespace GlobalTheory.PullSmooth

theorem repr_mul {m : ℕ} (a b : Alt m) (S : Finset (Fin (m + m))) :
    (bas m).repr (a * b) S = ∑ S₁, ∑ S₂, (bas m).repr a S₁ * (bas m).repr b S₂ *
      (bas m).repr (bas m S₁ * bas m S₂) S := by
  conv_lhs => rw [← (bas m).sum_repr a, ← (bas m).sum_repr b]
  simp only [Finset.sum_mul, Finset.mul_sum, smul_mul_smul_comm, map_sum, map_smul, Finsupp.coe_finset_sum,
    Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]

theorem entries_smooth {m n : ℕ} {τ : V m → V n} {U : Set (V m)} (hU : IsOpen U) (hτ : DifferentiableOn ℂ τ U)
    (v : V m) (a : Fin n) :
    ContDiffOn ℝ ∞ (fun x => fderiv ℂ τ x v a) U ∧ ContDiffOn ℝ ∞ (fun x => conj (fderiv ℂ τ x v a)) U := by
  have h₁ : ContDiffOn ℂ ∞ (fun x => fderiv ℂ τ x) U :=
    ContDiffOn.fderiv_of_isOpen (n := ω) (m := ∞)
      (((GlobalTheory.SCV.analyticOnNhd_iff_differentiableOn hU).2 hτ).contDiffOn hU.uniqueDiffOn) hU le_top
  have h₂ : ContDiffOn ℂ ∞ (fun x => fderiv ℂ τ x v a) U :=
    (EuclideanSpace.proj a : V n →L[ℂ] ℂ).contDiff.comp_contDiffOn (h₁.clm_apply contDiffOn_const)
  have h₃ : ContDiffOn ℝ ∞ (fun x => fderiv ℂ τ x v a) U := h₂.restrict_scalars ℝ
  exact ⟨h₃, Complex.conjCLE.contDiff.comp_contDiffOn h₃⟩

theorem contDiffOn_repr_pull_fderiv : ∀ (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (γ : Alt n), IsOpen U →
    DifferentiableOn ℂ τ U → ∀ S, ContDiffOn ℝ ∞ (fun x => (bas m).repr (pull (fderiv ℂ τ x) γ) S) U := by
  intro m n τ U γ hU hτ
  induction γ using ExteriorAlgebra.induction with
  | algebraMap r =>
    intro S
    simp only [AlgHom.commutes]
    exact contDiffOn_const
  | ι u =>
    intro S
    have hcoef : ∀ x, (bas m).repr (pull (fderiv ℂ τ x) (ExteriorAlgebra.ι ℂ u)) S =
        ((bas m).coord S ∘ₗ ExteriorAlgebra.ι ℂ)
          (Matrix.toLin' (Matrix.fromBlocks (Matrix.of fun b a => fderiv ℂ τ x (coordVec b) a) 0 0
            (Matrix.of fun b a => conj (fderiv ℂ τ x (coordVec b) a))) u) := by
      intro x
      simp [pull, ExteriorAlgebra.map_apply_ι]
    simp_rw [hcoef]
    refine (LinearMap.toContinuousLinearMap ((bas m).coord S ∘ₗ ExteriorAlgebra.ι ℂ)).contDiff.restrict_scalars ℝ
      |>.comp_contDiffOn ?_
    refine contDiffOn_pi.2 fun i => ?_
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct]
    refine ContDiffOn.sum fun j _ => ContDiffOn.mul ?_ contDiffOn_const
    rcases i with i | i <;> rcases j with j | j
    · simp only [Matrix.fromBlocks_apply₁₁, Matrix.of_apply]; exact (entries_smooth hU hτ _ _).1
    · simp only [Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]; exact contDiffOn_const
    · simp only [Matrix.fromBlocks_apply₂₂, Matrix.of_apply]; exact (entries_smooth hU hτ _ _).2
  | mul a b ha hb =>
    intro S
    have e : (fun x => (bas m).repr (pull (fderiv ℂ τ x) (a * b)) S) = fun x => ∑ S₁, ∑ S₂,
        (bas m).repr (pull (fderiv ℂ τ x) a) S₁ * (bas m).repr (pull (fderiv ℂ τ x) b) S₂ *
          (bas m).repr (bas m S₁ * bas m S₂) S := funext fun x => by rw [map_mul, repr_mul]
    rw [e]
    exact ContDiffOn.sum fun S₁ _ => ContDiffOn.sum fun S₂ _ =>
      ((ha S₁).mul (hb S₂)).mul contDiffOn_const
  | add a b ha hb =>
    intro S
    simp only [map_add, Finsupp.add_apply]
    exact (ha S).add (hb S)

end GlobalTheory.PullSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMapOfIsPullDeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.PullUnif

theorem coordMap_of_isPullDeg {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [CommRing V] [IsDomain V]
    [IsLocalRing V] {g : R →+* V} {D : DegPre R} {D' : DegPre V} (hD : IsPullDeg g D D') :
    CoordMap D D' g hD.xe.symm.toAddMonoidHom := by
  intro y r r' hr hr'
  have hr2 : PsiCoord D (hD.xe (hD.xe.symm y)) r := by rwa [AddEquiv.apply_symm_apply]
  obtain ⟨u, hu⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD (hD.xe.symm y) r hr2
  have h1 : Associated (u * g r) r' := GlobalTheory.TorRef.psiCoord_associated hu hr'
  exact Associated.trans ⟨u, mul_comm _ _⟩ h1

set_option maxHeartbeats 1600000 in

theorem gtTorus_pull {R V : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
    {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    [CommRing V] [IsDomain V] [IsLocalRing V] {D' : DegData V (maximalIdeal V)}
    {A' : PolAV (Sp (FractionRing V))} {G' : Over (Sp V)} [GrpObj G'] [IsCommMonObj G']
    {U : Unif (maximalIdeal R) D A G} {U' : Unif (maximalIdeal V) D' A' G'} {g : R →+* V}
    {bc : G' ≅ (Over.pullback (specOf g)).obj G} {hD : IsPullDeg g D.toPre D'.toPre}
    (H : IsPullUnif g hD bc U U')
    {κ : Type} [Field κ] {b : V →+* κ} (hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), b x = 0)
    (hb' : ∀ x ∈ maximalIdeal R ^ (0 + 1), (b.comp g) x = 0)
    {G₀ : Over (Sp κ)} [GrpObj G₀] {φ' : G₀.left ⟶ G'.left}
    (hp' : IsGrpPullback G₀ G' (spMap b) φ')
    (hp : IsGrpPullback G₀ G (spMap (b.comp g)) (φ' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g))) :
    GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hp' =
      GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) hb' hp := by
  obtain ⟨wL, -, he, -, Hs⟩ := (isPullUnif_iff_stalks R V _ _ g D D' hD A A' G G' bc U U').1 H
  obtain ⟨h, hf, ⟨hpG, hψ⟩, -⟩ := Hs 0
  obtain ⟨s, τ, hτ⟩ := GlobalTheory.PullLinear.exists_point (U.gt 0) (U'.gt 0) hpG (hψ 0).1 (𝟙 _)
  have : IsClosedImmersion (thick R (maximalIdeal R) 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have C1 : GlobalTheory.TorusPart.thickLift hb' hp = GlobalTheory.TorusPart.thickLift hb hp' ≫ h := by
    rw [← cancel_mono (pullback.fst G.hom (thick R (maximalIdeal R) 0)), GlobalTheory.TorusPart.thickLift_fst,
      Category.assoc]
    erw [hf]
    erw [← Category.assoc (GlobalTheory.TorusPart.thickLift hb hp'), GlobalTheory.TorusPart.thickLift_fst hb hp']
  have hτ' : (U'.gt 0).i.left ≫ h = τ.left ≫ (U.gt 0).i.left := by
    rw [← Over.comp_left, hτ, Category.id_comp]
  have key : GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb) D'.toPre.X ≫ τ.left =
      (GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom).left ≫
        GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb') D.toPre.X := by
    have wA : (GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb) D'.toPre.X ≫ τ.left) ≫
        (splitTorus (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) D.toPre.X).hom =
        (splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb' := by
      rw [Category.assoc, ← Over.w (U.gt 0).i, ← Category.assoc τ.left, ← hτ', Category.assoc,
        ← Category.assoc _ (U'.gt 0).i.left]
      erw [← GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb hp') (U'.gt 0).i]
      rw [Category.assoc, ← Category.assoc _ h, ← C1, (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp).1.w,
        ← Category.assoc, Over.w]
    have wB : ((GlobalTheory.SplitTorus.torusMap (Sp κ) hD.xe.symm.toAddMonoidHom).left ≫
        GlobalTheory.SplitTorus.bcMap (GlobalTheory.TorusPart.thickPt 0 hb') D.toPre.X) ≫
        (splitTorus (Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (0 + 1)))) D.toPre.X).hom =
        (splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb' := by
      rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w]
    have hchar : ∀ x' : D'.toPre.X, τ.left.appTop.hom (Rosenlicht.chi D.toPre.X (hD.xe x')) =
        Rosenlicht.chi D'.toPre.X x' := by
      intro x'
      apply TopCat.Presheaf.section_ext (splitTorus _ D'.toPre.X).left.sheaf ⊤
      intro z hz
      have e := congrArg Units.val
        (GlobalTheory.PullLinear.char_eq (U.gt 0) (U'.gt 0) hD.w (hψ x').1 (hψ x').2 (𝟙 _) τ hτ z)
      rw [gm_val τ.left z ⊤ trivial, gm_val (Over.Hom.left (𝟙 (WeightPf.Te D'.toPre (maximalIdeal V) 0))) z ⊤ trivial, GlobalTheory.SplitTorus.charUnit_val,
        GlobalTheory.SplitTorus.charUnit_val] at e
      exact e
    have e := GlobalTheory.SplitTorus.hom_ext (T := Over.mk ((splitTorus (Sp κ) D'.toPre.X).hom ≫ GlobalTheory.TorusPart.thickPt 0 hb'))
      (g := Over.homMk _ wA) (g' := Over.homMk _ wB) (fun a => by
        rw [GlobalTheory.SplitTorus.val_eq, GlobalTheory.SplitTorus.val_eq]
        simp only [Over.homMk_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
        rw [GlobalTheory.SplitTorus.bcMap_appTop_chi, GlobalTheory.SplitTorus.torusMap_appTop_chi,
          ← AddEquiv.apply_symm_apply hD.xe a, hchar, GlobalTheory.SplitTorus.bcMap_appTop_chi,
          AddEquiv.apply_symm_apply]
        rfl)
    exact congrArg (·.left) e
  apply GlobalTheory.TorusPart.hom_ext_of_pullback (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp)
  rw [Over.comp_left, Category.assoc]
  erw [GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb' hp) (U.gt 0).i]
  rw [C1, ← Category.assoc]
  erw [GlobalTheory.TorusPart.pullTorus_left (GlobalTheory.TorusPart.isGrpPullback_thickLift hb hp') (U'.gt 0).i]
  rw [Category.assoc, hτ', ← Category.assoc, key, Category.assoc]

set_option maxHeartbeats 800000 in

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsLocalHom g → ∀ (bc : G' ≅ (Over.pullback (specOf g)).obj G), IsMonHom bc.hom → β = bc.hom.left ≫ pullback.fst G.hom (specOf g) → ∀ hD : IsPullDeg g D.toPre D'.toPre, IsPullUnif g hD bc U U' → LBIso U'.LG.L (U.LG.L.pull β) ∧ CoordMap D.toPre D'.toPre g hD.xe.symm.toAddMonoidHom ∧ EquivMap U U' β hD.xe.symm.toAddMonoidHom := by
  intro R _ _ _ _ G _ _ _ D A U V _ _ _ _ G' _ _ _ D' A' U' g β hloc bc hbc hβ hD H
  subst hβ
  refine ⟨?_, coordMap_of_isPullDeg hD, ?_⟩
  · obtain ⟨wL, hwL, -⟩ := H.lg
    exact ⟨wL, hwL⟩
  intro f f' _ _ hcomm m m' hm hm' y
  have hb : ∀ x ∈ maximalIdeal V ^ (0 + 1), residue V x = 0 := fun x hx =>
    (residue_eq_zero_iff x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx)
  have hb' : ∀ x ∈ maximalIdeal R ^ (0 + 1), ((residue V).comp g) x = 0 := fun x hx =>
    (residue_eq_zero_iff _).2 ((map_mem_nonunits_iff g x).2 (Ideal.pow_le_self (Nat.succ_ne_zero 0) hx))
  have hp' := isGrpPullback_pullback G' (spMap (residue V))
  have hβ : IsGrpPullback G' G (spMap g) (bc.hom.left ≫ pullback.fst G.hom (specOf g)) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G (specOf g))).congr (Category.id_comp _) rfl
  have hp : IsGrpPullback ((Over.pullback (spMap (residue V))).obj G') G (spMap ((residue V).comp g))
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) :=
    (hp'.comp hβ).congr (Spec.map_comp (CommRingCat.ofHom g) (CommRingCat.ofHom (residue V))).symm rfl
  have e' : ((Over.pullback (spMap (residue V))).map f').left ≫ pullback.fst G'.hom (spMap (residue V)) =
      pullback.fst G'.hom (spMap (residue V)) ≫ f'.left := pullback.lift_fst _ _ _
  have e : ((Over.pullback (spMap (residue V))).map f').left ≫
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) =
      (pullback.fst G'.hom (spMap (residue V)) ≫ bc.hom.left ≫ pullback.fst G.hom (specOf g)) ≫ f.left := by
    rw [← Category.assoc, e', Category.assoc, hcomm]
    simp only [Category.assoc]
  have k' := hm' _ _ hb _ _ hp' _ e'
  have k := hm _ _ hb' _ _ hp _ e
  have K := gtTorus_pull H hb hb' hp' hp
  have hmono := (GlobalTheory.TorusPart.mono_gtTorus_and_factor (U.gt 0) hb' hp).1
  have k2 := (Category.assoc _ _ _).trans ((congrArg (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V))
    hD.xe.symm.toAddMonoidHom ≫ ·) k.symm).trans ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (Over.pullback (spMap (residue V))).map f') K.symm).trans (k'.trans
    ((congrArg (GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V)) m' ≫ ·) K).trans (Category.assoc _ _ _).symm)))))
  have k3 := (cancel_mono _).1 k2
  rw [← GlobalTheory.SplitTorus.torusMap_comp, ← GlobalTheory.SplitTorus.torusMap_comp] at k3
  exact congrArg (fun φ : D.toPre.X →+ D'.toPre.X => φ y) (GlobalTheory.SplitTorus.torusMap_injective k3)

end GlobalTheory.Poinc.Eq8.PullUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAwaySpreadPointLocalizationAtPrimeStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_away_spread_point_localization_atPrime : ∀ (B : Type) [CommRing B] (X : Scheme.{0}) (q : X ⟶ Sp B) [LocallyOfFinitePresentation q] (R : Type) [CommRing R] (β : B →+* R) (𝔭 : Ideal R) [𝔭.IsPrime] (f₀ : Sp (Localization.AtPrime 𝔭) ⟶ X), f₀ ≫ q = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) → ∃ r ∉ 𝔭, ∃ (j : Localization.Away r →+* Localization.AtPrime 𝔭) (f : Sp (Localization.Away r) ⟶ X), j.comp (algebraMap R (Localization.Away r)) = algebraMap R (Localization.AtPrime 𝔭) ∧ f ≫ q = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ spMap j ≫ f = f₀ := by
  first | exact @GlobalTheory.SpreadPoint.exists_away | exact GlobalTheory.SpreadPoint.exists_away | (intros; apply GlobalTheory.SpreadPoint.exists_away <;> assumption)
end

