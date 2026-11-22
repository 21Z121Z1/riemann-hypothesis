import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2996
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0619
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0077
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GradedLineBundleExists
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudProjectionSectionValuesIdentity
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FourierDescent

theorem cst_eq_gs_scal {R : Type} [CommRing R] {Z : Scheme.{0}} (p : Z ⟶ Sp R) (z : Z) (C : R) :
    cst p z C = gs (𝟙 _) z ⊤ (scal p C) := by
  have h := gs_pull (𝟙 Z) p z ⊤ trivial ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom C)
  rw [Category.id_comp] at h
  exact h.symm

theorem values_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (k : ℕ) (α : Q.X) (σ σ' σ'' : Q.SecB k α) (C : R), (∀ (y : Y.H.left) J, Good Q.P.L y J → sval σ' Y.q.left y J = sval σ'' Y.q.left y J + gs (𝟙 _) y ⊤ (scal Y.H.hom C) * sval σ Y.q.left y J) → ∀ (T : Over (Sp R)) (x : T ⟶ Q.P.A) z J, Good Q.P.L z J → sval σ' x.left z J = sval σ'' x.left z J + gs (𝟙 _) z ⊤ (scal T.hom C) * sval σ x.left z J := by
  intro R _ _ Q O _ _ _ oa Y k α σ σ' σ'' C hyp T x z J hJ
  classical
  have hL := Q.P.isLB
  have : Smooth Y.q.left := GlobalTheory.RayEv.Ray.smooth_q Y
  have : Surjective Y.q.left := (GlobalTheory.RayEv.Ray.surjective_quasiCompact_q Y).1
  have key : ∀ j : Fin 4 → Q.P.L.ι, σ'.f j =
      σ''.f j + constFn Q.P.A.hom ((LB.LinComb Q.P.L (DegPre.famφB Q α) (DegPre.famε k)).U j) C * σ.f j := by
    intro j
    apply GlobalTheory.EigenDescent.app_injective_of_flat_surjective Y.q.left
    apply fn_ext
    intro y hy
    rw [gs_pull (𝟙 _) Y.q.left y _ hy, gs_pull (𝟙 _) Y.q.left y _ hy, Category.id_comp]
    obtain ⟨J', hJ'⟩ : ∃ J', Good Q.P.L y J' :=
      ⟨fun ψ => (exists_chart hL (ψ y)).choose, fun ψ => (exists_chart hL (ψ y)).choose_spec⟩
    have h := hyp y J' hJ'
    have hm := hJ'.mem (DegPre.famφB Q α) Y.q.left
    rw [gs_add _ _ _ hy, gs_mul _ _ _ hy, gs_constFn _ _ _ _ hy]
    erw [sec_trans σ' _ y hy hm, sec_trans σ'' _ y hy hm, sec_trans σ _ y hy hm]
    rw [Over.w Y.q, cst_eq_gs_scal]
    change _ * sval σ' Y.q.left y J' = _ * sval σ'' Y.q.left y J' + _ * (_ * sval σ Y.q.left y J')
    rw [h]
    ring
  have hm := hJ.mem (DegPre.famφB Q α) x.left
  change gs x.left z _ (σ'.f _) = gs x.left z _ (σ''.f _) + _ * gs x.left z _ (σ.f _)
  rw [key]
  erw [gs_add _ _ _ hm, gs_mul _ _ _ hm, gs_constFn _ _ _ _ hm]
  rw [Over.w x, cst_eq_gs_scal]
  rfl

end GlobalTheory.FourierDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudShiftUnitIdentityFractionField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.DVR

set_option autoImplicit false

namespace GlobalTheory.ShiftUnit

theorem cv_nsmul {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T : Over (Spec (CommRingCat.of R))}
    (g : GtPt D T) {y : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L y J) (a mu : D.X) (k : ℕ) :
    GlobalTheory.TorusModel.cv g (a + k • mu) y J * cubN (th D y J) k (cP D T a) (cP D T mu) g.b =
      GlobalTheory.TorusModel.cv g a y J * GlobalTheory.TorusModel.cv g mu y J ^ k := by
  induction k with
  | zero => rw [zero_nsmul, add_zero, pow_zero]; rfl
  | succ k ih =>
    have e := GlobalTheory.TorusModel.cv_add g hJ (a + k • mu) mu
    rw [cPoint_add, cPoint_nsmul] at e
    rw [succ_nsmul, ← add_assoc, cubN, Finset.prod_range_succ, mul_comm (∏ _ ∈ _, _), ← _root_.mul_assoc, e, pow_succ,
      ← _root_.mul_assoc, ← ih, cubN, mul_right_comm]

theorem cst_mul {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (a b : V) :
    cst q z (a * b) = cst q z a * cst q z b := by
  unfold cst; rw [map_mul]; exact gs_mul q z ⊤ trivial _ _

theorem cst_pow {V : Type} [CommRing V] {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of V)) (z : Z) (a : V) (n : ℕ) :
    cst q z (a ^ n) = cst q z a ^ n := by
  induction n with
  | zero => unfold cst; rw [pow_zero, pow_zero, map_one, gs_eq q z ⊤ trivial, map_one, map_one]
  | succ n ih => rw [pow_succ, cst_mul, ih, pow_succ]

end GlobalTheory.ShiftUnit

open GlobalTheory.ShiftUnit in

theorem GlobalTheory.ShiftUnit.shift_unit_identity : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa), Q.TauBimult → ∀ (k : ℕ) (mu α : Q.X) (xp : 𝟙_ (Over (Sp R)) ⟶ Y.H) (A₀ B₀ P₀ : R) (ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1)) (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ xp⁻¹)).left ≫ Y.q.left] ![1, -1])), xp ≫ Y.q = Q.c mu → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z A₀ * (val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 Z) z J).val = cst (g ≫ jK R) z B₀ * (val (Q.tau mu α) g z J).val) → (∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → (val (Q.psi mu) g z J).val = cst (g ≫ jK R) z P₀ * (val ψ₀ (g ≫ jK R) z J).val) → (∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ xp⁻¹))).s mu) (𝟙 _) z J = 1) → ∀ (u : LB.Gen (LB.LinComb Q.P.L (DegPre.deltaφ Q (FractionRing R) k α mu) (DegPre.deltaε k))), u.IsGen → LB.Gen.Corr Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ u (DegPre.zF Q (FractionRing R)).left) (DegPre.famMult Q (FractionRing R) k mu α) → ∀ (Z : Scheme.{0}) (g : Z ⟶ (TK R).left) (pp : Over.mk (g ≫ jK R) ⟶ DegPre.BF Q (FractionRing R)) (yp : Over.mk (g ≫ jK R) ⟶ Y.H), (pp ≫ fst _ _).left ≫ jFK (R := R) (FractionRing R) = g → pp ≫ DegPre.prB Q (FractionRing R) = yp ≫ Y.q → ∀ (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → cst (g ≫ jK R) z B₀ * (val u (show Z ⟶ _ from pp.left) z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 Z) z J).val * ((val e (show Z ⟶ Y.H.left from (yp * (toUnit _ ≫ xp)).left) z J) ^ k).val = cst (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 Z) z J).val := by
  intro R _ _ Q O _ _ _ oa Y hB k mu α xp A₀ B₀ P₀ ψ₀ e hxp hA hP he u hu hcorr Z g pp yp hg hpp z J hJ
  have e1 := (gen_fe (D := Q) (F := FractionRing R) GlobalTheory.SemiRigid.globalFns k mu α).2 u hu hcorr _ pp z J hJ
  rw [uVal, val_famMult _ hJ, hg, TWM.val_powGen, TWM.val_powGen] at e1
  have c1 : pp ≫ fst (TF (FractionRing R)) Q.P.A ≫ cP Q (TF (FractionRing R)) mu = cP Q (Over.mk (g ≫ jK R)) mu := by
    rw [← Category.assoc, comp_cP]
  have jr : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
  have hr : val (Z := (Over.mk (g ≫ jK R)).left) Q.rigK g z J = val (Z := (Over.mk (g ≫ jK R)).left) Q.rig (g ≫ jK R) z J := by
    rw [DegPre.rigK, val_pull hJ, jr]
  rw [c1, hpp, hr] at e1
  have b1 : (Y.Φ (Over.mk (g ≫ jK R)) yp).b = yp ≫ Y.q := Ray.Φ_b Y yp
  have b2 : (Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).b = cP Q (Over.mk (g ≫ jK R)) mu := by
    rw [Ray.Φ_b, Category.assoc, hxp]; rfl
  have e2 : val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J *
      cubN (th Q z J) k (cP Q (Over.mk (g ≫ jK R)) α) (cP Q (Over.mk (g ≫ jK R)) mu) (yp ≫ Y.q) =
      val ((Y.Φ _ yp).s α) (𝟙 _) z J * val ((Y.Φ _ yp).s mu) (𝟙 _) z J ^ k := by
    have := cv_nsmul (Y.Φ _ yp) hJ α mu k
    rw [b1] at this
    exact this
  have e3 : val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J *
      th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu) =
      val ((Y.Φ _ yp).s α) (𝟙 _) z J * val ((Y.Φ (Over.mk (g ≫ jK R)) (toUnit _ ≫ xp)).s α) (𝟙 _) z J := by
    have := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ yp (toUnit _ ≫ xp))).2 α z J hJ
    rw [b1, b2] at this
    exact this
  have m1 : (yp * (toUnit (Over.mk (g ≫ jK R)) ≫ xp)) * (toUnit (Over.mk (g ≫ jK R)) ≫ xp⁻¹) = yp := by
    rw [GrpObj.comp_inv, mul_inv_cancel_right]
  have e4 : val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J * val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J * val (Z := (Over.mk (g ≫ jK R)).left) Q.rig (g ≫ jK R) z J *
      val ((Y.Φ _ yp).s mu) (𝟙 _) z J = 1 := by
    have := he (Over.mk (g ≫ jK R)) (yp * (toUnit _ ≫ xp)) z J hJ
    rw [m1] at this
    exact this
  have e5 : (val (Z := (Over.mk (g ≫ jK R)).left) (Q.psi mu) g z J).val = cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val :=
    hP Z g z J hJ
  have e6 : cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (val ((Y.Φ _ (toUnit _ ≫ xp)).s α) (𝟙 _) z J).val =
      cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * (val (Z := (Over.mk (g ≫ jK R)).left) (Q.tau mu α) g z J).val :=
    hA Z g z J hJ
  have V : val (Z := (Over.mk (g ≫ jK R)).left) u pp.left z J * val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J * val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J ^ k *
      val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J ^ k =
      (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹ *
        val (Z := (Over.mk (g ≫ jK R)).left) (Q.tau mu α) g z J * val (Z := (Over.mk (g ≫ jK R)).left) (Q.psi mu) g z J ^ k * val ((Y.Φ _ yp).s α) (𝟙 _) z J := by
    apply Additive.ofMul.injective
    have a1 := congrArg Additive.ofMul e1
    have a2 := congrArg Additive.ofMul e2
    have a4 := congrArg Additive.ofMul e4
    simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at a1 a2 a4 ⊢
    have a4k := congrArg (k • ·) a4
    simp only [smul_add, smul_zero] at a4k
    linear_combination (norm := abel) a1 + a2 + a4k
  have Vv := congrArg Units.val V
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at Vv
  rw [e5, mul_pow] at Vv
  have e3v := congrArg Units.val e3
  simp only [Units.val_mul] at e3v
  have hθ : Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu)) * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) = 1 := Units.mul_inv _
  suffices FINAL : cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * (val (Z := (Over.mk (g ≫ jK R)).left) u pp.left z J).val * (val ((Y.Φ _ yp).s (α + k • mu)) (𝟙 _) z J).val *
      ((val (Z := (Over.mk (g ≫ jK R)).left) e (yp * (toUnit _ ≫ xp)).left z J) ^ k).val =
    cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z (P₀ ^ k * A₀) * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J).val by exact FINAL
  rw [cst_mul, cst_pow, Units.val_pow_eq_pow_val]
  have hu0 : IsUnit ((val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k) := (Units.isUnit _).pow k
  apply hu0.mul_right_cancel
  linear_combination cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z B₀ * Vv + cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (val ((Y.Φ _ (yp * (toUnit _ ≫ xp))).s α) (𝟙 _) z J).val * hθ - cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z A₀ * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) * e3v - cst (Z := (Over.mk (g ≫ jK R)).left) (g ≫ jK R) z P₀ ^ k * (val (Z := (Over.mk (g ≫ jK R)).left) ψ₀ (g ≫ jK R) z J).val ^ k * (val ((Y.Φ _ yp).s α) (𝟙 _) z J).val * (Units.val (th Q z J (cP Q (Over.mk (g ≫ jK R)) α) (yp ≫ Y.q) (cP Q (Over.mk (g ≫ jK R)) mu))⁻¹) * e6
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResV
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HeatV

abbrev bo (R : Type) [CommRing R] (f : R) : (Sp R).affineOpens :=
  (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f)

abbrev resV (R : Type) [CommRing R] (f : R) : R →+* Γ(Sp R, (bo R f).1) :=
  ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom f))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

abbrev cst {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {O : Y.Opens} (h : O ≤ π ⁻¹ᵁ V) : Γ(X, V) →+* Γ(Y, O) :=
  (π.appLE V O h).hom

def opV {Y X : Scheme.{0}} (π : Y ⟶ X) (V : X.Opens) {n : ℕ} (dd : Fin n → Fld Y) (Θ : Matrix (Fin n) (Fin n) Γ(X, V))
    (u : Fin n → Γ(X, V)) (d : Fld Y) {W : Y.Opens} (p p' : Γ(Y, W)) (k : ℕ) (O : Y.Opens) (h : O ≤ π ⁻¹ᵁ V)
    (f : Γ(Y, O)) : Γ(Y, O) :=
  2 * (k : Γ(Y, O)) * d O f - ∑ a, ∑ b, cst π V h (Θ a b) * dd a O (dd b O f) +
    2 * ∑ a, cst π V h (u a) * dd a O f + (2 * (k : Γ(Y, O)) ^ 2 * rsT p O + 2 * (k : Γ(Y, O)) * rsT p' O) * f

end GlobalTheory.HeatV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidChartDualNumberDeformation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSUniq

variable {K : Type} [Field K]

theorem theta_eq_fibre (P₀ : Out.PolAV (Sp K)) {n : ℕ} (u : Fin n → (epsR K ⟶ P₀.A)) (hu : IsLieBasis u)
    (dd : Fin n → ∀ O : P₀.A.left.Opens, Γ(P₀.A.left, O) → Γ(P₀.A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    {X Z : Scheme.{0}} (π : Z ⟶ X) (x0 : Sp K ⟶ X) (m : P₀.A.left ⟶ Z) (hm : IsPullback m P₀.A.hom π x0)
    {U : X.Opens} (hU : IsAffineOpen U) (L : LB Z) (hL : L.IsLB) (hiso : LBIso P₀.L (L.pull m))
    (D : Γ(X, U) → Γ(X, U)) (θ θ' : Matrix (Fin n) (Fin n) K)
    {J J' : Type} (W : J → Z.Opens) (W' : J' → Z.Opens) (j : J → L.ι) (j' : J' → L.ι)
    (d : J → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (d' : J' → ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O))
    (hWU : ∀ i, W i ≤ π ⁻¹ᵁ U) (hWU' : ∀ k, W' k ≤ π ⁻¹ᵁ U)
    (hWj : ∀ i, W i ≤ L.U (j i)) (hWj' : ∀ k, W' k ≤ L.U (j' k))
    (hcov : ∀ z : P₀.A.left, ∃ i, m z ∈ W i) (hcov' : ∀ z : P₀.A.left, ∃ k, m z ∈ W' k)
    (hf : ∀ i, GlobalTheory.LogKS.IsField (W i) (d i)) (hf' : ∀ k, GlobalTheory.LogKS.IsField (W' k) (d' k))
    (hl : ∀ i (h : W i ≤ π ⁻¹ᵁ U) (r : Γ(X, U)),
      d i (W i) ((π.appLE U (W i) h).hom r) = (π.appLE U (W i) h).hom (D r))
    (hl' : ∀ k (h : W' k ≤ π ⁻¹ᵁ U) (r : Γ(X, U)),
      d' k (W' k) ((π.appLE U (W' k) h).hom r) = (π.appLE U (W' k) h).hom (D r))
    (φ : Fin n → C1 (fun i => m ⁻¹ᵁ L.U i)) (hφ : IsDlog m L dd φ)
    (hP : ∀ i i' (O : Z.Opens), O ≤ W i ⊓ W i' → ∀ f, (m.app O).hom (d i O f - d i' O f) =
      ∑ a, (∑ b, constFn P₀.A.hom _ (θ a b) * rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) * dd a _ ((m.app O).hom f))
    (hP' : ∀ k k' (O : Z.Opens), O ≤ W' k ⊓ W' k' → ∀ f, (m.app O).hom (d' k O f - d' k' O f) =
      ∑ a, (∑ b, constFn P₀.A.hom _ (θ' a b) * rsT (φ b (j' k) (j' k')) (m ⁻¹ᵁ O)) * dd a _ ((m.app O).hom f)) :
    θ = θ' := by
  have hs : Smooth P₀.A.hom := P₀.isAb.smooth
  obtain ⟨-, hind⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hdd Z m L hL hiso
  obtain ⟨hcoc, hcob⟩ := hind φ hφ
  let Wp : J × J' → Z.Opens := fun p => W p.1 ⊓ W' p.2
  have hWpU : ∀ p, Wp p ≤ π ⁻¹ᵁ U := fun p => inf_le_left.trans (hWU p.1)
  have bse := fun i => field_base π (W i) (hWU i) (d i) (hf i) D (hl i)
  have bse' := fun k => field_base π (W' k) (hWU' k) (d' k) (hf' k) D (hl' k)
  have ex : ∀ p : J × J', ∃ h : Fin n → Γ(P₀.A.left, m ⁻¹ᵁ Wp p), ∀ W₁, W₁ ≤ Wp p → ∀ f,
      (m.app W₁).hom (d p.1 W₁ f - d' p.2 W₁ f) = ∑ a, rsT (h a) _ * dd a (m ⁻¹ᵁ W₁) ((m.app W₁).hom f) := by
    intro p
    refine (coeff_id hs hu hdd x0 π m hm hU (Wp p) (hWpU p)
      (fun W₁ f => (m.app W₁).hom (d p.1 W₁ f - d' p.2 W₁ f))
      (fun W₁ h f f' => ?_) (fun W₁ h f f' => ?_) (fun W₁ W₂ h h₀ f => ?_) (fun W₁ h r => ?_)).exists
    · rw [(hf p.1).1 W₁ (h.trans inf_le_left), (hf' p.2).1 W₁ (h.trans inf_le_right)]
      simp only [map_sub, map_add]; ring
    · rw [(hf p.1).2.1 W₁ (h.trans inf_le_left), (hf' p.2).2.1 W₁ (h.trans inf_le_right)]
      simp only [map_sub, map_add, map_mul]; ring
    · rw [(hf p.1).2.2 W₁ W₂ h (h₀.trans inf_le_left), (hf' p.2).2.2 W₁ W₂ h (h₀.trans inf_le_right), ← map_sub,
        app_resG]
    · rw [bse p.1 W₁ (h.trans inf_le_left), bse' p.2 W₁ (h.trans inf_le_right), sub_self, map_zero]
  choose h hh using ex
  have cmp : ∀ (p p' : J × J') (a : Fin n),
      rsT (h p a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') - rsT (h p' a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') =
      ∑ b, (constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ a b) *
          rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') -
        constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b) *
          rsT (φ b (j' p.2) (j' p'.2)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) := by
    intro p p'
    let W₁ := Wp p ⊓ Wp p'
    have l1 : W₁ ≤ Wp p := inf_le_left
    have l2 : W₁ ≤ Wp p' := inf_le_right
    have k2 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ Wp p := m.preimage_mono l1
    have k3 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ Wp p' := m.preimage_mono l2
    have k4 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨hWj p.1 (hz.1.1), hWj p'.1 (hz.2.1)⟩
    have k5 : m ⁻¹ᵁ W₁ ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) :=
      fun z hz => ⟨hWj' p.2 (hz.1.2), hWj' p'.2 (hz.2.2)⟩
    let y₁ : Fin n → Γ(P₀.A.left, m ⁻¹ᵁ W₁) := fun a =>
      rsT (h p a) _ - rsT (h p' a) _ - ∑ b, (constFn P₀.A.hom _ (θ a b) * rsT (φ b (j p.1) (j p'.1)) _ -
        constFn P₀.A.hom _ (θ' a b) * rsT (φ b (j' p.2) (j' p'.2)) _)
    have z := (coeff_id hs hu hdd x0 π m hm hU W₁ (l1.trans (hWpU p)) (fun _ _ => 0) (fun _ _ _ _ => by simp)
      (fun _ _ _ _ => by simp) (fun _ _ _ _ _ => by simp [rsT_zero]) (fun _ _ _ => rfl)).unique
      (y₁ := y₁) (y₂ := fun _ => 0) (fun W₂ hW₂ f => ?_) (fun W₂ hW₂ f => by simp [rsT_zero])
    · intro a
      have := congrFun z a
      simp only [y₁] at this
      rw [sub_eq_zero] at this
      exact this
    · have k1 : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ W₁ := m.preimage_mono hW₂
      have E1 := hh p W₂ (hW₂.trans l1) f
      have E2 := hh p' W₂ (hW₂.trans l2) f
      have E3 := hP p.1 p'.1 W₂ (fun z hz => ⟨(l1 (hW₂ hz)).1, (l2 (hW₂ hz)).1⟩) f
      have E4 := hP' p.2 p'.2 W₂ (fun z hz => ⟨(l1 (hW₂ hz)).2, (l2 (hW₂ hz)).2⟩) f
      have k1' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ Wp p := k1.trans k2
      have k1'' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ Wp p' := k1.trans k3
      have k4' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) := k1.trans k4
      have k5' : m ⁻¹ᵁ W₂ ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) := k1.trans k5
      simp (disch := assumption) only [y₁, rsT_sub, rsT_sum, rsT_mul, rsT_rsT, rsT_constFn, sub_mul,
        Finset.sum_sub_distrib, Finset.sum_mul] at E1 E2 E3 E4 ⊢
      simp only [map_sub] at E1 E2 E3 E4
      linear_combination E1 - E2 - E3 + E4
  funext a
  refine sub_eq_zero.1 (hcob (θ a - θ' a) ?_)
  refine GlobalTheory.T.isCechOneCoboundary_of_refinement (fun i => m ⁻¹ᵁ L.U i) (lc P₀.A.hom (θ a - θ' a) φ) (isCoc_lc _ _ _ hcoc)
    (fun p => m ⁻¹ᵁ Wp p) (fun p => j p.1) (fun p => m.preimage_mono (inf_le_left.trans (hWj p.1))) ?_
    (fun p => -(h p a) - ∑ b, constFn P₀.A.hom _ (θ' a b) * rsT (φ b (j' p.2) (j p.1)) (m ⁻¹ᵁ Wp p)) ?_
  · refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨i, hi⟩ := hcov z
    obtain ⟨k, hk⟩ := hcov' z
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, k), hi, hk⟩
  · intro p p'
    have k2 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ Wp p := inf_le_left
    have k3 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ Wp p' := inf_le_right
    have k4 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨hWj p.1 hz.1.1, hWj p'.1 hz.2.1⟩
    have k6 : m ⁻¹ᵁ Wp p ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) :=
      fun z hz => ⟨hWj' p.2 hz.2, hWj p.1 hz.1⟩
    have k7 : m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨hWj' p'.2 hz.2, hWj p'.1 hz.1⟩
    have T1 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤
        m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨⟨hWj' p.2 hz.1.2, hWj' p'.2 hz.2.2⟩, hWj p'.1 hz.2.1⟩
    have T2 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤
        m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) :=
      fun z hz => ⟨⟨hWj' p.2 hz.1.2, hWj p.1 hz.1.1⟩, hWj p'.1 hz.2.1⟩
    have C1 : ∀ b, rsT (φ b (j' p.2) (j' p'.2)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') +
        rsT (φ b (j' p'.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') =
        rsT (φ b (j' p.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') := fun b => by
      have := congrArg (fun s => rsT s (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) (hcoc b (j' p.2) (j' p'.2) (j p'.1))
      have a1 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) := inf_le_left
      have a2 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.2, h.2⟩
      have a3 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.1, h.2⟩
      simpa (disch := assumption) only [rsT_add, rsT_rsT] using this
    have C2 : ∀ b, rsT (φ b (j' p.2) (j p.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') +
        rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') =
        rsT (φ b (j' p.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') := fun b => by
      have := congrArg (fun s => rsT s (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) (hcoc b (j' p.2) (j p.1) (j p'.1))
      have a1 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) := inf_le_left
      have a2 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.2, h.2⟩
      have a3 : m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) ≤
          m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := fun _ h => ⟨h.1.1, h.2⟩
      simpa (disch := assumption) only [rsT_add, rsT_rsT] using this
    have E := cmp p p' a
    have k8 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j' p.2) ⊓ m ⁻¹ᵁ L.U (j p.1) := k2.trans k6
    have k9 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j' p'.2) ⊓ m ⁻¹ᵁ L.U (j p'.1) := k3.trans k7
    have k10 : m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p' ≤ m ⁻¹ᵁ L.U (j p.1) ⊓ m ⁻¹ᵁ L.U (j p'.1) := k4
    simp (disch := assumption) only [lc, rsT_sub, rsT_neg, rsT_sum, rsT_mul, rsT_rsT, rsT_constFn, constFn_sub,
      sub_mul, Finset.sum_sub_distrib]
    have E' : ∑ b, (constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ a b) *
          rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') -
        constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b) *
          rsT (φ b (j p.1) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) =
        rsT (h p a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') - rsT (h p' a) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') +
        ∑ b, constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b) *
          (rsT (φ b (j' p.2) (j p.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') -
            rsT (φ b (j' p'.2) (j p'.1)) (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p')) := by
      rw [E, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      linear_combination (constFn P₀.A.hom (m ⁻¹ᵁ Wp p ⊓ m ⁻¹ᵁ Wp p') (θ' a b)) * (C1 b - C2 b)
    simp only [Pi.sub_apply, constFn_sub, sub_mul, mul_sub, Finset.sum_sub_distrib] at E' ⊢
    linear_combination E'

theorem eq_of_resG_eq_of_dense {Y : Scheme.{0}} [IsReduced Y] {U V : Y.Opens} (hV : Dense (V : Set Y))
    (f g : Γ(Y, U)) (h : resG Y (inf_le_left : U ⊓ V ≤ U) f = resG Y inf_le_left g) : f = g := by
  rw [← sub_eq_zero, ← AlgebraicGeometry.basicOpen_eq_bot_iff]
  have h0 : Y.basicOpen (resG Y (inf_le_left : U ⊓ V ≤ U) (f - g)) = ⊥ := by
    rw [map_sub, h, sub_self, Scheme.basicOpen_zero]
  rw [resG, Scheme.basicOpen_res] at h0
  refine eq_bot_iff.2 fun x hx => ?_
  obtain ⟨y, hy1, hy2⟩ := hV.inter_open_nonempty _ (Y.basicOpen (f - g)).isOpen ⟨x, hx⟩
  have : y ∈ (U ⊓ V) ⊓ Y.basicOpen (f - g) := ⟨⟨Y.basicOpen_le _ hy1, hy2⟩, hy1⟩
  rw [h0] at this
  exact this.elim

theorem isKS_unique_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), 1 ≤ Dw.p + Dw.q → SmoothOfRelativeDimension Dw.dim (genStr Y) → ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Y) → (∀ x ∈ genBd Y, IsClosed ({x} : Set (gen Y)) → HasRigidChart Y x) → ∀ (U : Y.X.affineOpens) (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Y.X, U.1)) ⟶ Y.t.G.left)) (A : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), (∀ i, IsTanAtG Y.t (chart U) (v i)) → (∀ w, IsTanAtG Y.t (chart U) w → ∃! cf : Fin n → Γ(Y.X, U.1), IsCombAtG Y.t (chart U) v cf w) → (∀ a i, IsCombAtG Y.t (chart U) v (A a i) (v i ≫ (Y.t.act.act a).left)) → ∀ (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (Θ Θ' : Matrix (Fin n) (Fin n) Γ(Y.X, U.1)), IsKS Y.t (interior Y) U v D.1 Θ → IsKS Y.t (interior Y) U v D.1 Θ' → Θ = Θ' := by
  intro E _ _ _ H Dw l Xo c Y _ _ _ _ U n v A hv hb hA D Θ Θ' hK hK'
  haveI : IsReduced Y.X := GlobalTheory.Coisotropic.isReduced_of_isNormalScheme Y.normal
  have key : ∀ {K : Type} [Field K] (x0 : Sp K ⟶ Y.X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1), ⊤ ≤ x0 ⁻¹ᵁ interior Y →
      ∀ a b, GlobalTheory.FlagMod.ev x0 U.1 hU (Θ a b) = GlobalTheory.FlagMod.ev x0 U.1 hU (Θ' a b) := by
    intro K _ x0 hU hV a b
    obtain ⟨P₀, θm, hpb, hiso⟩ := exists_polAV_interior Y x0 hV
    haveI : IsCommMonObj P₀.A := P₀.isAb.comm
    have hx : spMap (GlobalTheory.FlagMod.ev x0 U.1 hU) ≫ chart U = x0 := GlobalTheory.FlagMod.spMap_ev x0 U.2 hU
    have hv' := fun i => GlobalTheory.LieMet.isTan_map (GlobalTheory.FlagMod.ev x0 U.1 hU) hx (hv i)
    have hb' := GlobalTheory.GradedPieces.basis_map (GlobalTheory.FlagMod.ev x0 U.1 hU) hx hv hb
    obtain ⟨u, hu, hu'⟩ := GlobalTheory.LiePull.lieBasis_of_tanBasis Y.t x0 P₀.A θm hpb _ hv' hb'
    choose dd hdd using fun a => (GlobalTheory.KS.InvField.main K P₀.A (u a) (hu.1 a)).1
    obtain ⟨⟨φ, hφ⟩, -⟩ := GlobalTheory.KS.DlogPol.dlog_independent K P₀ n u dd hu hdd _ θm Y.t.PP.L Y.t.PP.isLB hiso
    obtain ⟨J, W, j, d, hcov, hWj, hf, hl, hdiff⟩ := hK
    obtain ⟨J', W', j', d', hcov', hWj', hf', hl', hdiff'⟩ := hK'
    have hP := pull_diff Y.t (interior Y) U v hv Θ W j d hWj hdiff x0 hU P₀.A θm hpb u hu' dd hdd φ hφ
    have hP' := pull_diff Y.t (interior Y) U v hv Θ' W' j' d' hWj' hdiff' x0 hU P₀.A θm hpb u hu' dd hdd φ hφ
    have hWU : ∀ i, W i ≤ Y.t.G.hom ⁻¹ᵁ U.1 := fun i p hp => by
      have : p ∈ Y.t.G.hom ⁻¹ᵁ (U.1 ⊓ interior Y) := hcov ▸ (le_iSup W i) hp
      exact this.1
    have hWU' : ∀ i, W' i ≤ Y.t.G.hom ⁻¹ᵁ U.1 := fun i p hp => by
      have : p ∈ Y.t.G.hom ⁻¹ᵁ (U.1 ⊓ interior Y) := hcov' ▸ (le_iSup W' i) hp
      exact this.1
    have hfib : ∀ z, Y.t.G.hom (θm z) ∈ U.1 ⊓ interior Y := fun z => by
      rw [← Scheme.Hom.comp_apply, hpb.1.w, Scheme.Hom.comp_apply]
      exact ⟨hU (Set.mem_univ _), hV (Set.mem_univ _)⟩
    have hcv : ∀ z, ∃ i, θm z ∈ W i := fun z => by
      have h2 : θm z ∈ ⨆ i, W i := by rw [hcov]; exact hfib z
      exact TopologicalSpace.Opens.mem_iSup.1 h2
    have hcv' : ∀ z, ∃ i, θm z ∈ W' i := fun z => by
      have h2 : θm z ∈ ⨆ i, W' i := by rw [hcov']; exact hfib z
      exact TopologicalSpace.Opens.mem_iSup.1 h2
    have := theta_eq_fibre P₀ u hu dd hdd Y.t.G.hom x0 θm hpb.1 U.2 Y.t.PP.L Y.t.PP.isLB hiso _
      (Matrix.of fun a b => GlobalTheory.FlagMod.ev x0 U.1 hU (Θ a b)) (Matrix.of fun a b => GlobalTheory.FlagMod.ev x0 U.1 hU (Θ' a b))
      W W' j j' d d' hWU hWU' hWj hWj' hcv hcv' hf hf' hl hl' φ hφ hP hP'
    exact congrFun (congrFun this a) b
  refine Matrix.ext fun a b => eq_of_resG_eq_of_dense (V := interior Y) (dense_interior Y) _ _ ?_
  refine GlobalTheory.GenericExtend.eq_of_valR_eq fun x hx => ⟨Y.X.residueField x, inferInstance,
    Y.X.fromSpecResidueField x, fun o => Scheme.fromSpecResidueField_apply x o, ?_⟩
  have ho : ∀ o, (Y.X.fromSpecResidueField x : Sp (Y.X.residueField x) ⟶ Y.X) o = x :=
    fun o => Scheme.fromSpecResidueField_apply x o
  generalize (Y.X.fromSpecResidueField x : Sp (Y.X.residueField x) ⟶ Y.X) = h at ho
  have hU : ⊤ ≤ h ⁻¹ᵁ U.1 := fun o _ => show h o ∈ U.1 by rw [ho]; exact hx.1
  have hV : ⊤ ≤ h ⁻¹ᵁ interior Y := fun o _ => show h o ∈ interior Y by rw [ho]; exact hx.2
  have hUV : ⊤ ≤ h ⁻¹ᵁ (U.1 ⊓ interior Y) := fun o _ => show h o ∈ U.1 ⊓ interior Y by rw [ho]; exact hx
  exact (GlobalTheory.CechKS.valR_resG h _ hUV _).trans ((GlobalTheory.CechKS.valR_eq_ev _ _ hU _).trans ((key h hU hV a b).trans
    ((GlobalTheory.CechKS.valR_eq_ev _ _ hU _).symm.trans (GlobalTheory.CechKS.valR_resG h _ hUV _).symm)))

end GlobalTheory.KSUniq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopLePreimageOfClosedPoint
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
open GlobalTheory.LocM GlobalTheory.PolFan ReciprocityTheory.AnForm.R
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChartDer

def resEps {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ R] (δ : Derivation ℤ R R) : R →+* DualNumber (ResidueField R) where
  toFun r := TrivSqZeroExt.inl (residue R r) + TrivSqZeroExt.inr (residue R (δ r))
  map_one' := by ext <;> simp
  map_zero' := by ext <;> simp
  map_add' a b := by ext <;> simp
  map_mul' a b := by ext <;> simp [Derivation.leibniz, mul_comm, add_comm]

@[simp] theorem resEps_fst {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ R] (δ : Derivation ℤ R R) (r : R) :
    (resEps δ r).fst = residue R r := by simp [resEps]

@[simp] theorem resEps_snd {R : Type} [CommRing R] [IsLocalRing R] [Algebra ℤ R] (δ : Derivation ℤ R R) (r : R) :
    (resEps δ r).snd = residue R (δ r) := by simp [resEps]

theorem top_le_preimage_of_closedPoint {R : Type} [CommRing R] [IsLocalRing R] {X : Scheme.{0}} (f : Sp R ⟶ X)
    (V : X.Opens) (h : f (closedPoint R) ∈ V) : ⊤ ≤ f ⁻¹ᵁ V := by
  intro p _
  have hp : p ⤳ closedPoint R := (PrimeSpectrum.le_iff_specializes p (closedPoint R)).1 (le_maximalIdeal p.2.ne_top)
  exact hp.mem_open (f ⁻¹ᵁ V).2 h

end GlobalTheory.ChartDer
end
end

