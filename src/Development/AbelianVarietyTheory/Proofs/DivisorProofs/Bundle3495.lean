import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0160
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePoints
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTorusInvariantHeatOperatorOfSymmetricRelat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3384
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3373
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2409
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3480
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2911
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsComplexArcDatumCmFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsPosHermOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3474
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2889
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.IntPointFn

theorem comp_padd_c_zero (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ D.c 0)).left = b.left := by
  rw [← Over.comp_left, GlobalTheory.Poinc.ThetaOne.c_zero]
  simp only [padd, comp_one]
  show (b ≫ (𝟙 D.P.A * 1)).left = b.left
  rw [_root_.mul_one, Category.comp_id]

theorem comp_toUnit_c_zero (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (toUnit D.P.A ≫ D.c 0).left = (η[D.P.A]).left := by
  rw [← Over.comp_left, GlobalTheory.Poinc.ThetaOne.c_zero, ← SymFrame.eta_eq, ← Category.assoc,
    toUnit_unique (b ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

theorem comp_toUnit_eta (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) :
    b.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (η[D.P.A]).left := by
  rw [← Over.comp_left, ← Category.assoc, toUnit_unique (b ≫ toUnit D.P.A) (𝟙 _), Category.id_comp]

end GlobalTheory.IntPointFn

namespace GlobalTheory.IntPointFn

theorem fn_of_theta : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (θ : SecOver D.P.A.hom (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A) (t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1))), t.IsGen → ∀ (ρ₀ : LB.Gen (D.P.L.pull (eSec D.P.A))), ρ₀.IsGen → ∃ f : V, ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp V) (z : Z) J, Good D.P.L z J → sval (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) (r ≫ b.left) z J * (val t r z J).val = gs r z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom f) * (val ρ₀ r z J).val := by
  intro V _ _ D θ b t ht ρ₀ hρ
  have hL := D.P.isLB
  have hu := mulGen_isGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ ρ₀) ht (invGen_isGen _ _ _ _ hρ)
  have hF : FormEq (Sum.elim (fun k => b.left ≫ D.famφB 0 k)
      (Sum.elim ![(η[D.P.A]).left, b.left] (fun _ : PUnit => eSec D.P.A)))
      (Sum.elim (DegPre.famε 1) (Sum.elim (DegPre.lineε 1) (fun _ : PUnit => -(1 : ℤ))))
      (PEmpty.elim : PEmpty → (Sp V ⟶ D.P.A.left)) (PEmpty.elim : PEmpty → ℤ) := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_four, Fin.prod_univ_two,
      Fintype.prod_empty, Fintype.prod_unique, DegPre.famφB, DegPre.famε, DegPre.lineε, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, Category.comp_id, Nat.cast_one, sub_self,
      comp_padd_c_zero, comp_toUnit_c_zero, comp_toUnit_eta, eSec]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
    abel
  obtain ⟨s', hs'⟩ := exists_sec hL hF (pullMulSec (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))) b.left
    (LB.mulGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ ρ₀)) hu)
  have hle : (⊤ : (Sp V).Opens) ≤ LB.wchart D.P.L (PEmpty.elim : PEmpty → (Sp V ⟶ D.P.A.left)) (PEmpty.elim : PEmpty → D.P.L.ι) :=
    fun _ _ => Set.mem_iInter.2 fun k => k.elim
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
    (((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι))), fun Z r z J hJ => ?_⟩
  have e1 := (hs' Z r z J hJ).trans (sval_pullMulSec _ _ _ hu r z hJ)
  rw [val_mul hJ, val_inv,
    sval_of s' r z J (PEmpty.elim : PEmpty → D.P.L.ι) (fun k => k.elim)] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom
      (((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι)))) =
      ((Sp V).presheaf.map (homOfLE hle).op).hom (s'.f (PEmpty.elim : PEmpty → D.P.L.ι)) := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  have e3 := gs_res r z hle (by trivial) (s'.f (PEmpty.elim : PEmpty → D.P.L.ι))
  rw [e2]
  erw [e3, e1]
  rw [Units.val_mul, _root_.mul_assoc, _root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel,
    Units.val_one, _root_.mul_one]

end GlobalTheory.IntPointFn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaugedTorusInvariantHeatOperator
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
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Heat.Gauge

open GlobalTheory.KS

theorem gauge_op {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hdd : ∀ a, IsField ⊤ (dd a)) (c : R) (hc : 2 * c = 1)
    (p : h₁.J × (Fin 2 → L.ι)) (k : ℕ) (O : G.left.Opens) (hO : O ≤ W m h₁ p) (f : Γ(G.left, O)) :
    op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k O (rsT (gU m h₁ e p).val O ^ k * f) =
      rsT (gU m h₁ e p).val O ^ k * op G dd h₁.Θ h₁.u (h₁.d p.1) (h₁.p p.1) (h₁.p' p.1) k O f :=
  GlobalTheory.T.gauged_local_heat_operator_power_mul _ G n X m m₁ L dd D h₁ e hdd c hc p k O hO f

theorem gauge_cocycle {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (p p' : h₁.J × (Fin 2 → L.ι))
    (O : G.left.Opens) (hO : O ≤ W m h₁ p ⊓ W m h₁ p') :
    pbT m (L.g (p.2 0) (p'.2 0)).val O * rsT (gU m h₁ e p').val O =
      rsT (gU m h₁ e p).val O * pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O :=
  GlobalTheory.T.gauge_units_transition_relation_on_overlaps _ G n X m m₁ L dd D h₁ e hL he p p' O hO

theorem gauge_chart {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (k : ℕ) (σ : SecM m₁ L k)
    (ρ : SecM m L k)
    (hρ : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val)
    (p : h₁.J × (Fin 2 → L.ι)) :
    rsT (ρ.f fun _ => p.2 0) (W m h₁ p) = (gU m h₁ e p).val ^ k * rsT (σ.f fun _ => h₁.j p.1) (W m h₁ p) :=
  GlobalTheory.T.gauged_chart_function_eq_gauge_power_mul _ G n X m m₁ L dd D h₁ e hL he k σ ρ hρ p

theorem gauge_wt {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) {n : ℕ} (dd : Fin n → Fld Y.H.left) (D : R → R)
    (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D)
    (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X)
    (hwe : ∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens),
      Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j →
        IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))
    (p : h₁.J × (Fin 2 → Q.P.L.ι)) (V : Q.P.A.left.Opens) (hV : Y.q.left ⁻¹ᵁ V ≤ W Y.q.left h₁ p) :
    IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (gU Y.q.left h₁ e p).val (Y.q.left ⁻¹ᵁ V)) :=
  GlobalTheory.T.gauge_unit_has_generator_weight_on_preimages _ Q O oa Y n dd D x h₁ e β hwe p V hV

section General

variable {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
  (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
  (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1]))

theorem gauge_cover (hL : L.IsLB) : ⨆ p, W m h₁ p = ⊤ := by
  refine eq_top_iff.2 fun y _ => ?_
  have hy : y ∈ ⨆ i, h₁.W i := by rw [h₁.cover]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨a, ha⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (m y)
  obtain ⟨b, hb⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_chart hL (m₁ y)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨(i, ![a, b]), hi, Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨ha, hb⟩)⟩

theorem gauge_lift (hF : ∀ a, IsField ⊤ (dd a)) (h0 : ∀ a O r, dd a O (constFn G.hom O r) = 0)
    (p : h₁.J × (Fin 2 → L.ι)) : IsLift G D (W m h₁ p) (gD m h₁ e p) := by
  have hd₁ := h₁.lift p.1
  refine ⟨GlobalTheory.Heat.Adjust.isField_add_comb (h₁.d p.1) dd (fun a => gY m h₁ e a p)
    (isField_mono hd₁.1 (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) hF, fun O' hO r => ?_⟩
  show h₁.d p.1 O' (constFn G.hom O' r) + ∑ a, rsT (gY m h₁ e a p) O' * dd a O' (constFn G.hom O' r) = _
  rw [hd₁.2 O' (hO.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) r]
  simp [h0]

theorem gauge_glue (hL : L.IsLB) (he : e.IsGen) (hF : ∀ a, IsField ⊤ (dd a)) (c : R) (hc : 2 * c = 1) (k : ℕ)
    (p p' : h₁.J × (Fin 2 → L.ι)) (O' : G.left.Opens) (hO : O' ≤ W m h₁ p ⊓ W m h₁ p') (f : Γ(G.left, O')) :
    op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k O' (pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f) =
      pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k *
        op G dd h₁.Θ h₁.u (gD m h₁ e p') (gP m h₁ e c p') (gP' m h₁ e c p') k O' f := by
  have hOp : O' ≤ W m h₁ p := hO.trans inf_le_left
  have hOp' : O' ≤ W m h₁ p' := hO.trans inf_le_right
  have hco := gauge_cocycle G m m₁ L dd D h₁ e hL he p p' O' hO
  have hA' : rsT (gU m h₁ e p').val O' * rsT (gU m h₁ e p')⁻¹.val O' = 1 := by
    rw [← GlobalTheory.KS.rsT_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, GlobalTheory.KS.rsT_one hOp']
  have hk := congrArg (· ^ k) hco
  have hk' := congrArg (· ^ k) hA'
  simp only [one_pow, mul_pow] at hk hk'
  have e1 : pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f =
      rsT (gU m h₁ e p).val O' ^ k *
        (pbT m₁ (L.g (h₁.j p.1) (h₁.j p'.1)).val O' ^ k * (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f)) := by
    linear_combination (-(pbT m (L.g (p.2 0) (p'.2 0)).val O' ^ k * f)) * hk' +
      (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f) * hk
  have ef : f = rsT (gU m h₁ e p').val O' ^ k * (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f) := by
    linear_combination (-f) * hk'
  rw [e1, gauge_op G m m₁ L dd D h₁ e hF c hc p k O' hOp,
    h₁.glue k p.1 p'.1 O' (le_inf (hOp.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)) (hOp'.trans (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p')))]
  conv_rhs => rw [ef, gauge_op G m m₁ L dd D h₁ e hF c hc p' k O' hOp']
  linear_combination (-(op G dd h₁.Θ h₁.u (h₁.d p'.1) (h₁.p p'.1) (h₁.p' p'.1) k O'
    (rsT (gU m h₁ e p')⁻¹.val O' ^ k * f))) * hk

end General

theorem gauge_acts {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m m₁ : G.left ⟶ X) (L : LB X) (dd : Fin n → Fld G.left) (D : R → R) (h₁ : Heat G m₁ L dd D)
    (e : LB.Gen (LB.LinComb L ![m, m₁] ![1, -1])) (hL : L.IsLB) (he : e.IsGen) (hF : ∀ a, IsField ⊤ (dd a))
    (c : R) (hc : 2 * c = 1) (k : ℕ) (σ σ' : SecM m₁ L k) (ρ ρ' : SecM m L k)
    (hρ : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val)
    (hρ' : ∀ (Z : Scheme.{0}) (r : Z ⟶ G.left) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval ρ' r z J = sval σ' r z J * ((val e r z J) ^ k).val)
    (hA : h₁.Acts k σ σ') (p : h₁.J × (Fin 2 → L.ι)) :
    rsT (ρ'.f fun _ => p.2 0) (W m h₁ p) = op G dd h₁.Θ h₁.u (gD m h₁ e p) (gP m h₁ e c p) (gP' m h₁ e c p) k
      (W m h₁ p) (rsT (ρ.f fun _ => p.2 0) (W m h₁ p)) := by
  have c1 := gauge_chart G m m₁ L dd D h₁ e hL he k σ ρ hρ p
  have c2 := gauge_chart G m m₁ L dd D h₁ e hL he k σ' ρ' hρ' p
  have hU : rsT (gU m h₁ e p).val (W m h₁ p) = (gU m h₁ e p).val := GlobalTheory.KS.rsT_self _
  rw [c1, c2, ← hU, gauge_op G m m₁ L dd D h₁ e hF c hc p k _ le_rfl, hU]
  congr 1
  have hWc : h₁.W p.1 ≤ (LB.LinComb L (K := Fin 1) (fun _ => m₁) fun _ => (k : ℤ)).U (fun _ => h₁.j p.1) :=
    GlobalTheory.Heat.Glue.le_wchart _ (h₁.le p.1)
  rw [← GlobalTheory.KS.rsT_rsT hWc (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p) (σ'.f fun _ => h₁.j p.1), hA p.1,
    op_rsT G dd hF _ _ _ _ _ k (h₁.lift p.1).1 le_rfl (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p),
    GlobalTheory.KS.rsT_rsT hWc (heatGaugeCoverOpen_le_heatOperatorOpen m h₁ p)]

theorem gauge_basic {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {O : Type} [CommRing O] [StarRing O]
    [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) {n : ℕ} (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left)
    (hinv : ∀ a, IsInv Y.H (v a) (dd a)) (D : R → R)
    (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd D)
    (hB₁ : ∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧
      ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
        IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f))
    (e : LB.Gen (LB.LinComb Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X)
    (hwe : ∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens),
      Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j →
        IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))
    (c : R) (p : h₁.J × (Fin 2 → Q.P.L.ι)) :
    (∃ V : Q.P.A.left.Opens, W Y.q.left h₁ p = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (gP Y.q.left h₁ e c p) ∧
      IsWt Y 0 _ (gP' Y.q.left h₁ e c p) ∧
      ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ W Y.q.left h₁ p → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f →
        IsWt Y α (Y.q.left ⁻¹ᵁ V) (gD Y.q.left h₁ e p _ f) := by
  obtain ⟨τ, hτ⟩ := trans_factor Q oa Y x
  obtain ⟨⟨V₁, hV₁⟩, hp₁, hp₁', hd₁⟩ := hB₁ p.1
  let Vp : Q.P.A.left.Opens := V₁ ⊓ (Q.P.L.U (p.2 0) ⊓ τ ⁻¹ᵁ Q.P.L.U (p.2 1))
  have hm₁ : ∀ y, ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) y = τ (Y.q.left y) := fun y => by
    rw [hτ, Scheme.Hom.comp_apply]
  have hWp : W Y.q.left h₁ p = Y.q.left ⁻¹ᵁ Vp := by
    refine TopologicalSpace.Opens.ext (Set.ext fun y => ⟨fun hy => ?_, fun hy => ?_⟩)
    · have h1 : y ∈ Y.q.left ⁻¹ᵁ V₁ := hV₁ ▸ hy.1
      have h2 := Set.mem_iInter.1 hy.2
      refine ⟨h1, h2 0, ?_⟩
      show τ (Y.q.left y) ∈ Q.P.L.U (p.2 1)
      rw [← hm₁]; exact h2 1
    · have h1 : y ∈ h₁.W p.1 := hV₁ ▸ hy.1
      refine ⟨h1, Set.mem_iInter.2 (Fin.forall_fin_two.2 ⟨hy.2.1, ?_⟩)⟩
      show ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) y ∈ Q.P.L.U (p.2 1)
      rw [hm₁]; exact hy.2.2
  have tr : ∀ (α : Q.X) (W₀ : Y.H.left.Opens), W₀ = Y.q.left ⁻¹ᵁ Vp → ∀ f : Γ(Y.H.left, W₀),
      IsWt Y α (Y.q.left ⁻¹ᵁ Vp) (rsT f (Y.q.left ⁻¹ᵁ Vp)) → IsWt Y α W₀ f := by
    rintro α W₀ rfl f h
    rwa [GlobalTheory.KS.rsT_self] at h
  have hU : IsWt Y β (W Y.q.left h₁ p) (gU Y.q.left h₁ e p).val :=
    tr β _ hWp _ (gauge_wt Q oa Y dd D x h₁ e β hwe p Vp hWp.ge)
  have hdW : ∀ α f, IsWt Y α (W Y.q.left h₁ p) f → IsWt Y α (W Y.q.left h₁ p) (h₁.d p.1 (W Y.q.left h₁ p) f) := by
    have hle : Y.q.left ⁻¹ᵁ Vp ≤ h₁.W p.1 := hWp ▸ heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p
    rw [hWp]
    exact fun α => hd₁ α Vp hle
  have hinvU : (gU Y.q.left h₁ e p).val * (gU Y.q.left h₁ e p)⁻¹.val = 1 := Units.mul_inv _
  have hL0 : ∀ a, IsWt Y 0 (W Y.q.left h₁ p) (gL Y.q.left h₁ e a p) := fun a =>
    GlobalTheory.Heat.WtPres.isWt_div (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) β _ _ hU) hU hinvU
  have hE0 : IsWt Y 0 (W Y.q.left h₁ p) (gE Y.q.left h₁ e p) :=
    GlobalTheory.Heat.WtPres.isWt_div (hdW β _ hU) hU hinvU
  have hY0 : ∀ a, IsWt Y 0 (W Y.q.left h₁ p) (gY Y.q.left h₁ e a p) := fun a =>
    GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ => GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 b)
  refine ⟨⟨Vp, hWp⟩, ?_, ?_, fun α V hV f hf => ?_⟩
  · refine GlobalTheory.Heat.WtAlg.isWt_sub (GlobalTheory.Heat.WtAlg.isWt_sub
      (GlobalTheory.Heat.Adjust.isWt_rsT Y (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p) hp₁) hE0) ?_
    refine GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) ?_
    exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ =>
      GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 a)) (hL0 b)
  · refine GlobalTheory.Heat.WtAlg.isWt_sub (GlobalTheory.Heat.WtAlg.isWt_add
      (GlobalTheory.Heat.Adjust.isWt_rsT Y (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p) hp₁') ?_) ?_
    · refine GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) ?_
      exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun b _ =>
        GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _)
          (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) 0 _ _ (hL0 b))
    · exact GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ =>
        GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul (GlobalTheory.Heat.WtAlg.isWt_constFn _ _) (hL0 a)
  · show IsWt Y α _ (h₁.d p.1 _ f + ∑ a, rsT (gY Y.q.left h₁ e a p) _ * dd a _ f)
    exact GlobalTheory.Heat.WtAlg.isWt_add (hd₁ α V (hV.trans (heatGaugeCoverOpen_le_heatOperatorOpen Y.q.left h₁ p)) f hf)
      (GlobalTheory.Heat.WtAlg.isWt_sum _ _ fun a _ => GlobalTheory.Heat.WtAlg.isRaynaudTorusWeightFunction_weightZero_mul
        (GlobalTheory.Heat.Adjust.isWt_rsT Y hV (hY0 a)) (GlobalTheory.Heat.IsInv.isWt Y (v a) (dd a) (hinv a) α _ _ hf))

theorem exists_gauge_heat : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (n : ℕ) (v : Fin n → TanM (𝟙 (Sp R)) Y.H) (dd : Fin n → Fld Y.H.left), (∀ a, IsInv Y.H (v a) (dd a)) → ∀ (D : Derivation ℤ R R) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H) (h₁ : Heat Y.H ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L dd ⇑D), (∀ i, (∃ V : Q.P.A.left.Opens, h₁.W i = Y.q.left ⁻¹ᵁ V) ∧ IsWt Y 0 _ (h₁.p i) ∧ IsWt Y 0 _ (h₁.p' i) ∧ ∀ (α : Q.X) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ h₁.W i → ∀ f, IsWt Y α (Y.q.left ⁻¹ᵁ V) f → IsWt Y α (Y.q.left ⁻¹ᵁ V) (h₁.d i _ f)) → ∀ (e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1])) (β : Q.X), e.IsGen → (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y β (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) → ∃ h' : Heat Y.H Y.q.left Q.P.L dd ⇑D, IsBasic Y h' ∧ h'.Θ = h₁.Θ ∧ h'.u = h₁.u ∧ ∀ (k : ℕ) (σ σ' : SecM ((𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left) Q.P.L k) (ρ ρ' : SecM Y.q.left Q.P.L k), (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ r z J = sval σ r z J * ((val e r z J) ^ k).val) → (∀ (Z : Scheme.{0}) (r : Z ⟶ Y.H.left) (z : Z) (J : (Z ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → sval ρ' r z J = sval σ' r z J * ((val e r z J) ^ k).val) → h₁.Acts k σ σ' → h'.Acts k ρ ρ' := by
  intro R _ _ _ Q O _ _ _ oa Y n v dd hinv D x h₁ hB₁ e β he hwe
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hF : ∀ a, IsField ⊤ (dd a) := fun a => (hinv a).1
  have hc : 2 * algebraMap ℚ R (1 / 2) = 1 := by
    rw [← map_ofNat (algebraMap ℚ R) 2, ← map_mul]
    norm_num
  refine ⟨⟨h₁.Θ, h₁.symm, h₁.u, h₁.J × (Fin 2 → Q.P.L.ι), W Y.q.left h₁, fun p => p.2 0,
    gD Y.q.left h₁ e, gP Y.q.left h₁ e (algebraMap ℚ R (1 / 2)), gP' Y.q.left h₁ e (algebraMap ℚ R (1 / 2)),
    gauge_cover Y.H _ _ Q.P.L dd _ h₁ hL, fun p => W_le_m Y.q.left h₁ p,
    gauge_lift Y.H _ _ Q.P.L dd _ h₁ e hF (fun a O' r => GlobalTheory.Heat.Adjust.inv_constFn Y.H (v a) (dd a) (hinv a) O' r),
    fun k p p' O' hO f => gauge_glue Y.H _ _ Q.P.L dd _ h₁ e hL he hF _ hc k p p' O' hO f⟩,
    gauge_basic Q oa Y v dd hinv _ x h₁ hB₁ e β hwe _, rfl, rfl, ?_⟩
  intro k σ σ' ρ ρ' hρ hρ' hA p
  exact gauge_acts Y.H _ _ Q.P.L dd _ h₁ e hL he hF _ hc k σ σ' ρ ρ' hρ hρ' hA p

end GlobalTheory.Heat.Gauge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratingDegenerationDataPrincipalTriple
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UBaseData

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (t : SAB H (Sp W)), IsProper t.G.hom → Out.RelAmple t.G t.PP.L → Out.KTriv t.G t.PP.L → (∃ g, SmoothOfRelativeDimension g t.G.hom) → ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (x₀ : X → (𝟙_ (Over (Sp W)) ⟶ t.G)), (∀ y z, x₀ (y + z) = x₀ y * x₀ z) → (∀ (a : 𝓞 E) y, x₀ (a • y) = x₀ y ≫ t.act.act a) → ∃ (D : DegPre W) (_ : Module (𝓞 E) D.X) (oa : letI := H.starRing; D.OAct (𝓞 E)) (φB : t.G.left ⟶ D.P.A.left) (e : X ≃ₗ[𝓞 E] D.X), D.PsiEven ∧ D.TauBimult ∧ (∀ y, PsiUnitOn D y Set.univ) ∧ (letI := H.starRing; TraceFormTwistIso D oa H.w0) ∧ IsAbPart t D oa φB ∧ ∀ y, (x₀ y).left ≫ φB = (D.c (e y)).left := by
  intro E _ _ _ H W _ _ _ t hp hA hK ⟨g, hg⟩ X _ _ _ _ x₀ hadd hlin
  letI := H.starRing
  let P := GlobalTheory.GenericPol.toPolAV t g hg hp hA hK
  obtain ⟨sym, hsym, hsym'⟩ := (GlobalTheory.isSymmetric_iff_exists_gen _ _ t.PP).1 t.sym
  have hψ0 : ∀ y : X, ∃ ψ : LB.Gen (LB.LinComb P.L (K := PUnit) (fun _ => ptK (x₀ y)) (fun _ => -1)), ψ.IsGen :=
    fun y => ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_local (V := FractionRing W) P.L P.isLB _ _
  choose ψ hψ using hψ0
  let D₀ : DegPre W :=
    { P := P, rig := t.PP.rig, rig_gen := t.PP.rigGen, cub := t.cub, sym := sym, sym_gen := hsym, sym_rig := hsym',
      X := X, c := x₀, c_add := hadd, psi := ψ, psi_gen := hψ }
  letI : Module (𝓞 E) D₀.X := ‹Module (𝓞 E) X›
  haveI : Module.Projective (𝓞 E) D₀.X := GlobalTheory.PointStepCompare.projective_of_free E (X := X)
  haveI : Module.Finite (𝓞 E) D₀.X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  have := t.act.hom H.w0
  let onB : D₀.P.OAct (𝓞 E) := ⟨t.act.toRingAct, GlobalTheory.GenericPol.rosatiAdj t⟩
  obtain ⟨u, hu, hu0⟩ := GlobalTheory.ArcCM.CxFibre.exists_primGen t.PP (t.act.act H.w0) t.prim
  obtain ⟨ψ', hψ', oa, hoa, he, hb, hw, hU⟩ := GlobalTheory.UTau0.exists_symmetric_balanced_generator_psi_zero_localRing W D₀ (𝓞 E) onB hlin H.w0
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one H) ⟨u, hu, hu0⟩
  refine ⟨{ D₀ with psi := ψ', psi_gen := hψ' }, ‹Module (𝓞 E) X›, oa, 𝟙 _, LinearEquiv.refl _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact he
  · exact hb
  · exact hU
  · exact hw
  · refine ⟨GlobalTheory.PolDeg.Wit.grpPullback_id t.G, fun a => ?_, GlobalTheory.PolDeg.Wit.idPull _, GlobalTheory.PolDeg.Wit.idPull_isGen t.PP.isLB⟩
    rw [hoa]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · intro y
    exact Category.comp_id _

end GlobalTheory.UBaseData
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTranslatedBundleIntegralPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.FieldBaseChange GlobalTheory.UT
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic

namespace GlobalTheory.GenLocal

theorem exists_gen_unit_point : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (D : DegPre V) (b : 𝟙_ (Over (Sp V)) ⟶ D.P.A), ∃ t : LB.Gen (LB.LinComb D.P.L ![(η[D.P.A]).left, b.left] (DegPre.lineε 1)), t.IsGen := by
  intro V _ _ _ D b
  choose i hi using fun k : Fin 2 =>
    exists_chart D.P.isLB ((![(η[D.P.A]).left, b.left] k) (closedPoint V))
  exact AbSquare.exists_gen_of_mem_chart D.P.isLB _ _ i fun k y => by
    have : (![(η[D.P.A]).left, b.left] k) ⁻¹ᵁ D.P.L.U (i k) = ⊤ :=
      (IsLocalRing.closedPoint_mem_iff _).1 (hi k)
    exact (this.ge trivial : y ∈ (![(η[D.P.A]).left, b.left] k) ⁻¹ᵁ D.P.L.U (i k))

end GlobalTheory.GenLocal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackCompleteDVROfGenericCompat
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

theorem GlobalTheory.UPoinc.exists_grpPullback_of_generic_compat : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (ξ : Sp V ⟶ S) (GK : Over (Sp (FractionRing V))) [GrpObj GK] (φ : GK.left ⟶ G₁.left) (γ : GK.left ⟶ G.left), IsGrpPullback GK G₁ (jK V) φ → IsGrpPullback GK G (jK V ≫ ξ) γ → ∃ β : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ β ∧ φ ≫ β = γ ∧ ∀ (f₁ : G₁ ⟶ G₁) (f : G ⟶ G) (fK : GK ⟶ GK), fK.left ≫ φ = φ ≫ f₁.left → fK.left ≫ γ = γ ≫ f.left → f₁.left ≫ β = β ≫ f.left := by
  intro V _ _ _ hV G₁ _ _ hG₁ S G _ _ hG ξ GK _ φ γ hφ hγ
  haveI : IsDiscreteValuationRing V := hV.1
  haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  have hid : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := isGrpPullback_of_iso (Iso.refl G)
  obtain ⟨β, hβ, e⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map V (𝟙 S) G G (𝟙 G.left) hG hid G₁ hG₁ ξ
    (jK V ≫ ξ) (Category.comp_id _) GK φ γ hφ hγ
  rw [Category.comp_id] at e
  refine ⟨β, hβ, e, fun f₁ f fK h₁ h₂ => ?_⟩
  have hj : GlobalTheory.IsGenericPointHom (S := Sp V) (ReciprocityTheory.ChartRestriction.G.Out.jK V) := .fractionField V (FractionRing V)
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G₁ hG₁
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback hφ.1.flip
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ φ ?_
  · rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, hβ.1.w]
  · rw [← Category.assoc, ← h₁, Category.assoc, e, h₂, ← Category.assoc, e]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackMapSemiAbelianNormalDomainStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_grpPullback_map_semiAbelian_normalDomain : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] {X S : Scheme.{0}} (j : X ⟶ S) (A : Over X) [GrpObj A] (G : Over S) [GrpObj G] (e : A.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback A G j e → ∀ (G₁ : Over (Sp R)) [GrpObj G₁], IsSemiAbelian G₁ → ∀ (ξ : Sp R ⟶ S) (y : Sp (FractionRing R) ⟶ X), y ≫ j = jK R ≫ ξ → ∀ (B : Over (Sp (FractionRing R))) [GrpObj B] (a : B.left ⟶ G₁.left) (b : B.left ⟶ A.left), IsGrpPullback B G₁ (jK R) a → IsGrpPullback B A y b → ∃ πC : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ πC ∧ a ≫ πC = b ≫ e := by
  first | exact @GlobalTheory.SemiAbDesc.exists_grpPullback_map | exact GlobalTheory.SemiAbDesc.exists_grpPullback_map | (intros; apply GlobalTheory.SemiAbDesc.exists_grpPullback_map <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackUniformisingGroupSameGenericFib
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.Poinc.Sep.Spz

theorem endU_genMap {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {D : DegData V (maximalIdeal V)}
    {A : PolAV (Sp (FractionRing V))} {G : Over (Sp V)} [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G)
    (E : EndU U.toUnifPre) : E.aA.left ≫ genMap U = genMap U ≫ E.aG.left := by
  have h1 : E.aA ≫ U.gen.inv = U.gen.inv ≫ (Over.pullback (jK V)).map E.aG := by
    rw [Iso.comp_inv_eq, Category.assoc, E.ext, Iso.inv_hom_id_assoc]
  have h1' : E.aA.left ≫ U.gen.inv.left = U.gen.inv.left ≫ ((Over.pullback (jK V)).map E.aG).left := by
    have := congrArg CommaMorphism.left h1
    simpa only [Over.comp_left] using this
  have h2 : ((Over.pullback (jK V)).map E.aG).left ≫ pullback.fst G.hom (jK V) = pullback.fst G.hom (jK V) ≫ E.aG.left :=
    pullback.lift_fst _ _ _
  unfold genMap
  rw [← Category.assoc, h1', Category.assoc, h2, Category.assoc]

theorem exists_ext : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (U : Unif (maximalIdeal V) D A G) (ξ : Sp V ⟶ B) (gm : A.A.left ⟶ H.left), IsGrpPullback A.A H (jK V ≫ ξ) gm → ∃ β : G.left ⟶ H.left, IsGrpPullback G H ξ β ∧ genMap U ≫ β = gm ∧ ∀ (E : EndU U.toUnifPre) (Fm : H ⟶ H), E.aA.left ≫ gm = gm ≫ Fm.left → E.aG.left ≫ β = β ≫ Fm.left := by
  intro B H _ _ hH V _ _ _ hV G _ _ hG D A U ξ gm hgm
  obtain ⟨⟨hN, -, hIC, -⟩, -⟩ := hV
  haveI := hN
  haveI := hIC
  have gpA : IsGrpPullback A.A G (jK V) (genMap U) := by
    have := U.gen_hom
    have : IsMonHom U.gen.symm.hom := by show IsMonHom U.gen.inv; infer_instance
    exact ((isGrpPullback_of_iso U.gen.symm).comp (isGrpPullback_pullback G (jK V))).congr
      (Category.id_comp _) rfl
  have : IsMonHom (Iso.refl H).hom := by show IsMonHom (𝟙 H); infer_instance
  have hHH : IsGrpPullback H H (𝟙 B) (𝟙 H.left) := isGrpPullback_of_iso (Iso.refl H)
  obtain ⟨β, hβ, hβg⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map V (𝟙 B) H H (𝟙 _) hH hHH G hG ξ (jK V ≫ ξ)
    (Category.comp_id _) A.A (genMap U) gm gpA hgm
  have hβg' : genMap U ≫ β = gm := by simpa using hβg
  refine ⟨β, hβ, hβg', ?_⟩
  intro E Fm hE
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian H hH
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.spec_fractionRing V (FractionRing V)
  haveI : IsSchemeTheoreticallyDominant (genMap U) := .of_isPullback gpA.1.flip
  have key := endU_genMap U E
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant H.hom ?_ (genMap U) ?_
  · rw [Category.assoc, Category.assoc, Over.w Fm, hβ.1.w, ← Category.assoc, Over.w E.aG]
  · rw [← Category.assoc, ← key, Category.assoc, hβg', hE, ← Category.assoc, hβg']

end GlobalTheory.Poinc.Sep.Spz
end
end

