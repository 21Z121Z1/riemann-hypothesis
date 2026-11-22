import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0029
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0018
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0139
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Counterexamples.UniformisationSurvey.BoxCubicalUnconditional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2351
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0880
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2370
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0059

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieCotValEqTanVal
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def sqToEps {M S : Type} [AddCommGroup M] [Module R M] [Module Rᵐᵒᵖ M] [IsCentralScalar R M]
    [CommRing S] [Algebra R S] (k : M →ₗ[R] S) : TrivSqZeroExt R M →ₐ[R] DualNumber S where
  toFun z := (algebraMap R S z.fst, k z.snd)
  map_one' := TrivSqZeroExt.ext (map_one (algebraMap R S)) (map_zero k)
  map_mul' a b := TrivSqZeroExt.ext (map_mul (algebraMap R S) _ _) (by
    change k (a.fst • b.snd + MulOpposite.op b.fst • a.snd) =
      algebraMap R S a.fst * k b.snd + k a.snd * algebraMap R S b.fst
    rw [op_smul_eq_smul, map_add, map_smul, map_smul, Algebra.smul_def, Algebra.smul_def,
      mul_comm (k a.snd)])
  map_zero' := TrivSqZeroExt.ext (map_zero (algebraMap R S)) (map_zero k)
  map_add' a b := TrivSqZeroExt.ext (map_add (algebraMap R S) _ _) (map_add k _ _)
  commutes' _ := TrivSqZeroExt.ext rfl (map_zero k)

attribute [local instance] cotOp cotCentral cotTower

theorem tanDer_cotVal {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R} (t : G.TorsionTower A)
    (β : Form (A.hom ≫ 𝟙 _)) {v : epsR R ⟶ A} (hv : IsTangent v) (n : ℕ) :
    t.tanDer hv n (cotVal β.1 (t.y n)) = algebraMap R (ModPow p R n) (tanVal v β) := by
  let S := ModPow p R n
  let E : SqExt R := SqExt.ofModule R S S
  let ρ : (cotExt R (G.A n)).C →ₐ[R] DualNumber S := sqToEps (t.tanDer hv n)
  let y' : Pt A (cotExt R (G.A n)).C := spOver (cotPt R (G.A n)) ≫ t.y n
  have hρ : ρ.comp (cotPt R (G.A n)) = t.tanPt hv n := AlgHom.ext fun a ↦ by
    refine TrivSqZeroExt.ext ?_ ?_
    · rw [t.fst_tanPt]
      exact congrArg (algebraMap R S) (add_zero _)
    · rw [← t.tanDer_d]
      exact congrArg (t.tanDer hv n) (zero_add _)
  have e : spOver ρ ≫ y' = epsRedPow p n v := by
    rw [← Category.assoc, spOver_comp, hρ, t.tanPt_y]
  have k1 := (cotExt R (G.A n)).val_map E ρ (Algebra.ofId R S) (fun _ ↦ rfl)
    (fun _ ↦ TrivSqZeroExt.ext rfl (map_zero (t.tanDer hv n))) y'.left y'.w _
    (Pt.w (epsRedPow p n v)) (congrArg Over.Hom.left e) β
  have k2 := (SqExt.dual R).val_map E (epsTo R S) (Algebra.ofId R S) (fun c ↦ (fst_epsTo S c).symm)
    (fun c ↦ TrivSqZeroExt.ext (fst_epsTo S _) ((snd_epsTo S _).trans (map_zero _))) v.left (pt_w v) _
    (Pt.w (epsRedPow p n v)) rfl β
  have h0 : fv β.1 (G.A n) (cotExt R (G.A n)).C (cotPt R (G.A n)) (t.y n) = 0 := β.2 _ rfl rfl
  have k3 := congrArg TrivSqZeroExt.snd (k1.symm.trans k2)
  rw [snd_epsTo] at k3
  refine Eq.trans ?_ k3
  change t.tanDer hv n (cotSnd R _ (_ - fv β.1 (G.A n) (cotExt R (G.A n)).C (cotPt R (G.A n)) (t.y n))) = _
  rw [h0, sub_zero]
  rfl

theorem lie_cotVal_eq_tanVal : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R) (t : G.TorsionTower A), IsNilpotent (p : R) → ∀ (β : Form (A.hom ≫ 𝟙 _)) (w : G.omega), (∀ n, w.1 n = cotVal β.1 (t.y n)) → ∀ (x : G.Lie) (v : epsR R ⟶ A), t.LieCorr x v → x w = tanVal v β := by
  intro R _ A _ p G t ⟨n, hn⟩ β w hw x v h
  have h1 := (t.lieCorr_iff h.1 x).1 h n w
  rw [hw, tanDer_cotVal] at h1
  have h2 := Ideal.Quotient.eq.1 h1
  rw [hn, Ideal.mem_span_singleton, zero_dvd_iff] at h2
  exact sub_eq_zero.1 h2

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieFiltrationSpannedCorrespondence
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult DividedPowers GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DeRham

theorem exists_finite_dualBasis {R : Type} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [Module.Projective R M] :
    ∃ (n : ℕ) (e : Fin n → M) (f : Fin n → Module.Dual R M), ∀ c, ∑ i, f i c • e i = c := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property π LinearMap.id hπ
  refine ⟨n, fun i ↦ π (Pi.single i 1), fun i ↦ LinearMap.proj i ∘ₗ s, fun c ↦ ?_⟩
  calc ∑ i, (LinearMap.proj i ∘ₗ s) c • π (Pi.single i 1)
      = π (∑ i, s c i • Pi.single i (1 : R)) := by simp [map_sum, map_smul]
    _ = π (s c) := by
        congr 1; ext j; simp [Finset.sum_apply, Pi.single_apply]
    _ = c := LinearMap.congr_fun hs c

theorem span_corr_baseChange : GlobalTheory.Published.AbelianDeRham → ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}
    {R R' : Type} [CommRing R] [CommRing R'] (σ : R →+* R') {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap σ) φ →
    ∀ (m : GrpMor (dp0 R) (𝟙 _) X.A (dp0 R') (𝟙 _) X'.A σ (spMap σ) φ),
    Submodule.span R' {x' | ∃ x, m.Corr x x'} = ⊤ ∧
      Fil X'.A ≤ Submodule.span R' {x' | ∃ x ∈ Fil X.A, m.Corr x x'} ∧
      ∀ x x', x ∈ Fil X.A → m.Corr x x' → x' ∈ Fil X'.A := by
  intro H F _ _ 𝔠 R R' _ _ σ X X' φ hP m
  letI := σ.toAlgebra
  obtain ⟨H1, H2, H3, -, -⟩ := H
  obtain ⟨hbc, hF⟩ := H3 R X.A _ X.ab X.dim R' X'.A φ hP.grp
  have hm : m.IsBC := hbc
  have hF' : PrimitiveSubmodule X'.A = Submodule.span R' (m.pull '' PrimitiveSubmodule X.A) := hF
  have ext' : ∀ y z : HdR X'.A, (∀ c, y (m.pull c) = z (m.pull c)) → y = z := by
    intro y z h
    refine LinearMap.ext fun c' ↦ ?_
    obtain ⟨w, rfl⟩ := hm.2 c'
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul r c => rw [liftSemi_tmul, map_smul, map_smul, h c]
    | add a b ha hb => rw [map_add, map_add, map_add, ha, hb]
  obtain ⟨hfin, hproj, -⟩ := H1.prim X.ab X.dim
  obtain ⟨n, e, f, hef⟩ := exists_finite_dualBasis (R := R) (M := primDR X.A)
  have key : ∀ (q : primDR X.A →ₗ[R] primDR X.A) (y' : HdR X'.A),
      (∀ c, y' (m.pull (q c)) = y' (m.pull c)) →
      y' ∈ Submodule.span R' {x' | ∃ x, (∃ d : HdR X.A, x = d ∘ₗ q) ∧ m.Corr x x'} := by
    intro q y' hy
    choose g hg using fun i ↦ hm.exists ((f i) ∘ₗ q)
    have hy' : y' = ∑ i, y' (m.pull (e i)) • g i := by
      refine ext' _ _ fun c ↦ ?_
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      have hgc : ∀ i, g i (m.pull c) = σ ((f i ∘ₗ q) c) := fun i ↦ hg i c
      simp only [hgc]
      rw [← hy c]
      conv_lhs => rw [← hef (q c)]
      rw [map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, mul_comm]
      rfl
    rw [hy']
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, ⟨f i, rfl⟩, hg i⟩)
  refine ⟨?_, ?_, ?_⟩
  · refine eq_top_iff.2 fun y' _ ↦ ?_
    refine Submodule.span_mono ?_ (key LinearMap.id y' fun c ↦ rfl)
    rintro x' ⟨x, -, hx⟩
    exact ⟨x, hx⟩
  · intro y' hy'
    obtain ⟨-, ⟨N, hN⟩, -⟩ := H2 R X.A _ X.ab X.dim
    let P : primDR X.A →ₗ[R] primDR X.A := N.projection (PrimitiveSubmodule X.A) hN.symm
    have hP0 : ∀ c ∈ PrimitiveSubmodule X.A, P c = 0 := fun c hc ↦
      Submodule.projection_apply_of_mem_right hN.symm hc
    have hP1 : ∀ c, c - P c ∈ PrimitiveSubmodule X.A := fun c ↦ by
      obtain ⟨u, v, huv, -⟩ := Submodule.existsUnique_add_of_isCompl hN c
      have hv : P v = v := Submodule.projection_apply_of_mem_left hN.symm v.2
      rw [← huv, map_add, hP0 _ u.2, hv, zero_add, add_sub_cancel_right]
      exact u.2
    have hy0 := (Submodule.mem_dualAnnihilator _).1 hy'
    refine Submodule.span_mono ?_ (key P y' fun c ↦ ?_)
    · rintro x' ⟨x, ⟨d, rfl⟩, hx⟩
      refine ⟨_, (Submodule.mem_dualAnnihilator _).2 fun c hc ↦ ?_, hx⟩
      rw [LinearMap.comp_apply, hP0 c hc, map_zero]
    · have h0 : y' (m.pull (c - P c)) = 0 :=
        hy0 _ (hF' ▸ Submodule.subset_span ⟨_, hP1 c, rfl⟩)
      rw [map_sub, map_sub, sub_eq_zero] at h0
      exact h0.symm
  · intro x x' hx hxx'
    refine (Submodule.mem_dualAnnihilator _).2 fun w hw ↦ ?_
    rw [hF'] at hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨c, hc, rfl⟩ := hw
      rw [hxx' c, (Submodule.mem_dualAnnihilator _).1 hx c hc, map_zero]
    | zero => exact map_zero _
    | add a b _ _ ha hb => rw [map_add, ha, hb, add_zero]
    | smul r a _ ha => rw [map_smul, ha, smul_zero]

end GlobalTheory.DeRham
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftCompSquare
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.SharpIdent

theorem lift_comp_square {S S' : Scheme.{0}} {G : Over S} {G₁ G₂ T : Over S'} {φ : G₁.left ⟶ G.left}
    {ψ : G₂.left ⟶ G.left} {φ₂ : (G₁ ⊗ G₁).left ⟶ (G ⊗ G).left} {ψ₂ : (G₂ ⊗ G₂).left ⟶ (G ⊗ G).left}
    (hφ : IsSquare φ φ₂) (hψ : IsSquare ψ ψ₂) (x x' : T ⟶ G₁) (y y' : T ⟶ G₂) (h : x.left ≫ φ = y.left ≫ ψ)
    (h' : x'.left ≫ φ = y'.left ≫ ψ) : (lift x x').left ≫ φ₂ = (lift y y').left ≫ ψ₂ := by
  have e₁ : ((lift x x').left ≫ φ₂) ≫ (fst G G).left = ((lift y y').left ≫ ψ₂) ≫ (fst G G).left := by
    rw [Category.assoc, Category.assoc, hφ.1, hψ.1, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, lift_fst, lift_fst, h]
  have e₂ : ((lift x x').left ≫ φ₂) ≫ (snd G G).left = ((lift y y').left ≫ ψ₂) ≫ (snd G G).left := by
    rw [Category.assoc, Category.assoc, hφ.2, hψ.2, ← Category.assoc, ← Category.assoc, ← Over.comp_left,
      ← Over.comp_left, lift_snd, lift_snd, h']
  exact pullback.hom_ext e₁ e₂

theorem exists_iso_pow : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ) (T : Trait F)
    (P : PolAV (Sp (FractionRing T.V))), SharpOver F W P T.y → ∀ (A8 : PolAV (Sp (FractionRing T.V)))
    (pA : IsPowPolAV A8 T.A 8), ∃ φ : P.A ≅ A8.A, IsMonHom φ.hom ∧
      LBIso P.L (LB.LinComb (abelian₂ T.A.A T.A.L) (K := Fin 8 × Fin 8)
        (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)) := by
  intro g n o _ ζ F W T P hP A8 pA
  obtain ⟨c, ⟨φc, φ₂, hc, hsq, ⟨w, hw⟩, -⟩, pr, hpr, huniv, hL⟩ := hP
  obtain ⟨e, he, hee⟩ := grpPullback_iso hc T.cart
  let p : IsPowGrp P.A T.A.A 8 :=
    { pr := fun a => pr a ≫ e.hom
      hom := fun a => by have := hpr a; infer_instance
      lim := Fan.IsLimit.mk _ (fun s => (huniv s.pt fun a => s.proj a ≫ e.inv).choose)
        (fun s a => by
          have h := (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.1 a
          change _ ≫ pr a ≫ e.hom = _
          rw [← Category.assoc, h, Category.assoc, e.inv_hom_id, Category.comp_id])
        (fun s m hm => (huniv s.pt fun a => s.proj a ≫ e.inv).choose_spec.2 m fun a => by
          have h : m ≫ pr a ≫ e.hom = s.proj a := hm a
          rw [← h, Category.assoc, Category.assoc, e.hom_inv_id, Category.comp_id]) }
  obtain ⟨φ, hφ, hφp⟩ := GlobalTheory.PowerExamples.pow_unique p pA.toIsPowGrp
  refine ⟨φ, hφ, ?_⟩
  have hpt : ∀ a, (pr a).left ≫ φc = (φ.hom ≫ pA.pr a).left ≫ T.α := fun a => by
    have h : φ.hom ≫ pA.pr a = pr a ≫ e.hom := hφp a
    rw [h, Over.comp_left, Category.assoc, hee]
  have hΛ : (abelian₂ T.A.A T.A.L).IsLB := LB.isLB_linComb T.A.isLB _ _
  obtain ⟨w', hw'⟩ := T.lb
  have i₁ := iso_linComb ((isGen_iff w).1 hw) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have i₂ := iso_linComb ((isGen_iff w').1 hw') (K := Fin 8 × Fin 8)
    (fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left) (fun ab => W ab.1 ab.2)
  have hm : (fun ab : Fin 8 × Fin 8 => (lift (pr ab.1) (pr ab.2)).left ≫ φ₂) =
      fun ab => (lift (φ.hom ≫ pA.pr ab.1) (φ.hom ≫ pA.pr ab.2)).left ≫ T.α₂ :=
    funext fun ab => lift_comp_square hsq T.sq _ _ _ _ (hpt ab.1) (hpt ab.2)
  rw [hm] at i₁
  exact LBIso.trans P.isLB (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb hΛ _ _) hL
    (LBIso.trans (LB.isLB_linComb c.isLB _ _) (LB.isLB_linComb F.univ.isLB _ _) (LB.isLB_linComb hΛ _ _) i₁ i₂.symm)

end GlobalTheory.Poinc.SharpIdent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftLineBundleSectionOfClosedImmersionAffineOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_lineBundle_section_of_closedImmersion_affineOpen : ∀ (X' Z' : Scheme.{0}) (i' : Z' ⟶ X') [IsClosedImmersion i'] (L' : LB X'), L'.IsLB →
    ∀ (Y' : X'.Opens), IsAffineOpen Y' → ∀ (τ : ∀ k, Γ(Z', i' ⁻¹ᵁ (L'.U k ⊓ Y'))),
    (∀ (k l : L'.ι) (z : Z') (hk : z ∈ i' ⁻¹ᵁ (L'.U k ⊓ Y')) (hl : z ∈ i' ⁻¹ᵁ (L'.U l ⊓ Y')),
      Z'.presheaf.germ _ z hk (τ k) =
        Z'.presheaf.germ (i' ⁻¹ᵁ (L'.U k ⊓ L'.U l)) z ⟨hk.1, hl.1⟩ ((i'.app _).hom (L'.g k l).val) *
          Z'.presheaf.germ _ z hl (τ l)) →
    ∃ θ : ∀ k, Γ(X', L'.U k ⊓ Y'),
      (∀ (k l : L'.ι) (x : X') (hk : x ∈ L'.U k ⊓ Y') (hl : x ∈ L'.U l ⊓ Y'),
        X'.presheaf.germ _ x hk (θ k) =
          X'.presheaf.germ (L'.U k ⊓ L'.U l) x ⟨hk.1, hl.1⟩ (L'.g k l).val * X'.presheaf.germ _ x hl (θ l)) ∧
      ∀ k, (i'.app (L'.U k ⊓ Y')).hom (θ k) = τ k := by
  first | exact @GlobalTheory.PinchLift.lift_section_of_closedImm | exact GlobalTheory.PinchLift.lift_section_of_closedImm | (intros; apply GlobalTheory.PinchLift.lift_section_of_closedImm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongPrincipalSmallExtensionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftsAlong_principal_small_extension : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (U : Over (Sp R)) (M : LB (A ⊗ U).left), Fam A M → SmallLift A M → ∀ (B : Type) [CommRing B] [IsLocalRing B] (t : B), t ∈ IsLocalRing.maximalIdeal B → IsLocalRing.maximalIdeal B * Ideal.span {t} = ⊥ → LiftsAlong A M B (Ideal.span {t}) := by
  first | exact @GlobalTheory.DualOpen.liftsAlong_span_singleton | exact GlobalTheory.DualOpen.liftsAlong_span_singleton | (intros; apply GlobalTheory.DualOpen.liftsAlong_span_singleton <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinFormSymmBilinEqSumLiftsOdd
section
open GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc

theorem symm_bilin_pow_dvd_of_lifts {Y : Type} [AddCommGroup Y] (n N : ℕ) (hodd : Odd N)
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y)
    (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (B : LinearMap.BilinForm ℤ Y) (hB : ∀ x y, B x y = B y x) (h0 : ∀ cl, B (μ cl) (μ cl) = 0) :
    ∀ k : ℕ, ∀ x y, (N : ℤ) ^ k ∣ B x y := by
  have hdec : ∀ x : Y, ∃ y : Y, x = μ (fun i => (eb x i : ZMod N)) + (N : ℤ) • y := by
    intro x
    have hd : ∀ i, (N : ℤ) ∣ eb x i - eb (μ (fun i => (eb x i : ZMod N))) i := by
      intro i
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      rw [hμ _ i, sub_self]
    choose z hz using hd
    refine ⟨eb.symm z, ?_⟩
    apply eb.injective
    funext i
    rw [map_add, map_smul, LinearEquiv.apply_symm_apply]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hz i]
  have hdiag : ∀ k, (∀ x y, (N : ℤ) ^ k ∣ B x y) → ∀ x, (N : ℤ) ^ (k + 1) ∣ B x x := by
    intro k hk x
    obtain ⟨y, hy⟩ := hdec x
    have hm := h0 (fun i => (eb x i : ZMod N))
    generalize μ (fun i => (eb x i : ZMod N)) = m at hy hm
    subst hy
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hm]
    rw [hB y m]
    obtain ⟨a, ha⟩ := hk m y
    obtain ⟨b, hb⟩ := hk y y
    rw [ha, hb]
    exact ⟨2 * a + N * b, by ring⟩
  have hcop : IsCoprime (N : ℤ) 2 := by
    have := Nat.isCoprime_iff_coprime.mpr (Nat.coprime_two_right.mpr hodd)
    exact_mod_cast this
  intro k
  induction k with
  | zero => intro x y; simp
  | succ k ih =>
    intro x y
    have h2 : (N : ℤ) ^ (k + 1) ∣ 2 * B x y := by
      have hxy := hdiag k ih (x + y)
      have hx := hdiag k ih x
      have hy := hdiag k ih y
      have e : 2 * B x y = B (x + y) (x + y) - B x x - B y y := by
        simp only [map_add, LinearMap.add_apply]
        rw [hB y x]
        ring
      rw [e]
      exact dvd_sub (dvd_sub hxy hx) hy
    exact (hcop.pow_left).dvd_of_dvd_mul_left h2

theorem symm_bilin_eq_zero_of_lifts {Y : Type} [AddCommGroup Y] (n N : ℕ) (hN : 3 ≤ N) (hodd : Odd N)
    (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y)
    (hμ : ∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i)
    (B : LinearMap.BilinForm ℤ Y) (hB : ∀ x y, B x y = B y x) (h0 : ∀ cl, B (μ cl) (μ cl) = 0) :
    B = 0 := by
  ext x y
  have h := symm_bilin_pow_dvd_of_lifts n N hodd eb μ hμ B hB h0 (B x y).natAbs x y
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs h ?_
  rw [Int.natAbs_pow, Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

theorem linForm_eq_sum_lifts : ∀ (Y : Type) [AddCommGroup Y] (n N : ℕ) [NeZero N], 3 ≤ N → Odd N →
    ∀ (eb : Y ≃ₗ[ℤ] (Fin n → ℤ)) (μ : (Fin n → ZMod N) → Y), (∀ cl i, ((eb (μ cl) i : ℤ) : ZMod N) = cl i) →
    ∀ ℓ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ℤ, ∃ (D : ℕ) (ν : (Fin n → ZMod N) → ℤ), 0 < D ∧
      ∀ b : LinearMap.BilinForm ℤ Y, (∀ x y, b x y = b y x) → (D : ℤ) * ℓ b = ∑ cl, ν cl * b (μ cl) (μ cl) := by
  intro Y _ n N _ hN hodd eb μ hμ ℓ
  classical
  haveI : Module.Free ℤ Y := Module.Free.of_equiv eb.symm
  haveI : Module.Finite ℤ Y := Module.Finite.equiv eb.symm
  let S : Submodule ℤ (LinearMap.BilinForm ℤ Y) :=
    { carrier := {b | ∀ x y, b x y = b y x}
      add_mem' := by intro a b ha hb x y; simp [ha x y, hb x y]
      zero_mem' := by intro x y; simp
      smul_mem' := by intro c b hb x y; simp [hb x y] }
  let Φ : LinearMap.BilinForm ℤ Y →ₗ[ℤ] ((Fin n → ZMod N) → ℤ) :=
    { toFun := fun b c => b (μ c) (μ c)
      map_add' := by intro a b; funext c; simp
      map_smul' := by intro k b; funext c; simp }
  have hinj : Function.Injective (Φ ∘ₗ S.subtype) := by
    intro x y hxy
    apply Subtype.ext
    apply sub_eq_zero.mp
    refine symm_bilin_eq_zero_of_lifts n N hN hodd eb μ hμ _ ?_ ?_
    · intro u v
      simp [x.2 u v, y.2 u v]
    · intro c
      have := congrFun hxy c
      simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.coe_mk, AddHom.coe_mk, Φ] at this
      simp [this]
  obtain ⟨D, hD, ν, hν⟩ := exists_nat_mul_eq_sum_of_injective (Φ ∘ₗ S.subtype) hinj (ℓ ∘ₗ S.subtype)
  exact ⟨D, ν, hD, fun b hb => hν ⟨b, hb⟩⟩

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyAtPointLambdaTrivial
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwistFlat

variable {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T : Over (Sp R)} {V : Type} [CommRing V]
  (φ : Sp V ⟶ T.left)

theorem upa_mul {Y : Over (Sp V)} (x y : Y ⟶ bc A φ) : upa φ (x * y) = upa φ x * upa φ y := by
  have h := (isGrpPullback_pullback A (φ ≫ T.hom)).2 Y x y (upa φ x) (upa φ y) rfl rfl
  exact Over.OverMorphism.ext h.symm

theorem upa_one {Y : Over (Sp V)} : upa φ (1 : Y ⟶ bc A φ) = 1 := by
  have e := upa_mul φ (1 : Y ⟶ bc A φ) 1
  rw [_root_.mul_one] at e
  exact left_eq_mul.1 e

theorem pull_cls_twist {N : LB (A ⊗ T).left} (hN : N.IsLB) (h : (twist A φ N).IsLB) {Y : Over (Sp V)}
    (x : Y ⟶ bc A φ) : CechPic.pull x.left (cls _ h) = evc hN (upa φ x) (upt φ Y) := by
  let u : up φ Y ⟶ bcR A φ := Over.homMk x.left (by
    show x.left ≫ (bc A φ).hom ≫ φ ≫ T.hom = Y.hom ≫ φ ≫ T.hom
    rw [← Category.assoc, Over.w x])
  have ha : u ≫ pa A φ = upa φ x := Over.OverMorphism.ext rfl
  have ht : u ≫ pt A φ = upt φ Y := Over.OverMorphism.ext (by
    show x.left ≫ (bc A φ).hom ≫ φ = Y.hom ≫ φ
    rw [← Category.assoc, Over.w x])
  have e := pull_evc hN u (pa A φ) (pt A φ)
  rw [ha, ht] at e
  exact e

variable (A) in

theorem triv_lam_twist (N : LB (A ⊗ T).left) (hF : Fam A N) : Triv (abelian₂ (bc A φ) (twist A φ N)) := by
  have hO : (twist A φ N).IsLB := pull_isLB hF.isLB _
  have hP : (abelian₂ (bc A φ) (twist A φ N)).IsLB := LB.isLB_linComb hO _ _
  refine (cls_eq_zero_iff hP).1 ?_
  have e : cls _ hP = lam (G := bc A φ) (cls (X := (bc A φ).left) _ hO) (fst (bc A φ) (bc A φ)) (snd (bc A φ) (bc A φ)) := cls_cube_two (G := bc A φ) (L := twist A φ N) hO _ _ hP
  rw [e, lam, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO, pull_cls_twist φ hF.isLB hO,
    pull_cls_twist φ hF.isLB hO, upa_mul, upa_one, (isAdditive_iff hF.isLB).1 hF.add, hF.add.evc_one hF.isLB]
  simp only [add_sub_cancel_left, sub_self, add_zero]

end GlobalTheory.TwistFlat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyChartOfAffineParametersStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleFamilyChart_of_affine_parameters : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : Over S) (M : LB (A ⊗ U).left), Fam A M → Inj A M → (∀ (T : Over S) [IsAffine T.left] (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N) → ∀ (T : Over S) (N : LB (A ⊗ T).left), Fam A N → ChartAt A M N := by
  first | exact @GlobalTheory.DualCon.chartAt_of_affine | exact GlobalTheory.DualCon.chartAt_of_affine | (intros; apply GlobalTheory.DualCon.chartAt_of_affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoPullbackOfLocalUnitGeneratorsStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_iso_pullback_of_local_unit_generators : ∀ (X Y : Scheme.{0}) (f : Y ⟶ X) (L : LB Y) (J : Type) (W : J → X.Opens) (g : ∀ x y, Γ(X, W x ⊓ W y)ˣ) (s : ∀ x k, Γ(Y, L.U k ⊓ f ⁻¹ᵁ W x)ˣ), (∀ x, GlobalTheory.PinchLift.GenOn L (f ⁻¹ᵁ W x) (s x)) → (∀ x y (t : Y) (k : L.ι), f t ∈ W x → f t ∈ W y → t ∈ L.U k → gm f t (W x ⊓ W y) (g x y) = gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W y) (s y k) * (gm (𝟙 Y) t (L.U k ⊓ f ⁻¹ᵁ W x) (s x k))⁻¹) → LBIso L ((⟨J, W, g⟩ : LB X).pull f) := by
  first | exact @GlobalTheory.PinchLift.lbIso_pull_of_genOn | exact GlobalTheory.PinchLift.lbIso_pull_of_genOn | (intros; apply GlobalTheory.PinchLift.lbIso_pull_of_genOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSymmetryHypothesisOfPolAVPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc

theorem hypS_polAV_pullback : ∀ {S S' : Scheme.{0}} (P : PolAV S) (P' : PolAV S') (f : S' ⟶ S) (ψ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f ψ → LBIso P'.L (P.L.pull ψ) → HypS P.A P.L → HypS P'.A P'.L :=
  fun {S S'} P P' f ψ h hb hS =>
    GlobalTheory.SymBaseChange.hypS_baseChange S S' P.A P'.A f ψ P.L P'.L P.isLB P'.isLB h hb hS

end GlobalTheory.Poinc
end

