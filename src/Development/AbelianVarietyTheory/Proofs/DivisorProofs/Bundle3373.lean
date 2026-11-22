import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CohomologyLogDerivativeAdjointEndomorphisms
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalPolChartsKS
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsScalarFormTraceForm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0504

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
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

namespace GlobalTheory.Heat.Glue

open GlobalTheory.KS

variable {X Y : Scheme.{0}}

theorem map_eq_rsT {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) :
    (Y.presheaf.map (homOfLE h).op).hom s = rsT s O := (rsT_of_le h s).symm

theorem rsT_pow' {O₀ O : Y.Opens} (h : O ≤ O₀) (s : Γ(Y, O₀)) (k : ℕ) : rsT (s ^ k) O = rsT s O ^ k := by
  rw [rsT_of_le h, rsT_of_le h, map_pow]

theorem le_wchart {m : Y ⟶ X} {L : LB X} (c : Fin 1 → L.ι) {O : Y.Opens} (h : O ≤ m ⁻¹ᵁ L.U (c 0)) :
    O ≤ LB.wchart L (fun _ : Fin 1 => m) c := fun y hy =>
  Set.mem_iInter.2 fun x => by rw [Subsingleton.elim x 0]; exact h hy

theorem pullbackBundleChart_le_preimage {m : Y ⟶ X} {L : LB X} (c : Fin 1 → L.ι) :
    LB.wchart L (fun _ : Fin 1 => m) c ≤ m ⁻¹ᵁ L.U (c 0) := LB.wchart_le L _ c 0

theorem pbT_cocycle {L : LB X} (hL : L.IsLB) (m : Y ⟶ X) (a b c : L.ι) {O : Y.Opens}
    (h : O ≤ m ⁻¹ᵁ (L.U a ⊓ L.U b ⊓ L.U c)) :
    pbT m (L.g a b).val O * pbT m (L.g b c).val O = pbT m (L.g a c).val O := by
  have e := congrArg (fun u => pbT m u.val O) (hL.cocycle a b c)
  simp only [Units.val_mul, GlobalTheory.KS.AdjDlog.val_res, pbT_mul] at e
  rwa [pbT_rsT m inf_le_left h, pbT_rsT m (le_inf (inf_le_left.trans inf_le_right) inf_le_right) h,
    pbT_rsT m (le_inf (inf_le_left.trans inf_le_left) inf_le_right) h] at e

theorem linComb_g {L : LB X} (m : Y ⟶ X) (k : ℕ) (c c' : Fin 1 → L.ι) {O : Y.Opens}
    (h : O ≤ LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c') :
    rsT ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).g c c').val O =
      pbT m (L.g (c 0) (c' 0)).val O ^ k := by
  have hle : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (c' 0)) :=
    fun y hy => ⟨pullbackBundleChart_le_preimage c hy.1, pullbackBundleChart_le_preimage c' hy.2⟩
  simp only [LB.LinComb, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]
  rw [rsT_pow' h]
  exact congrArg (· ^ k) ((congrArg (fun s => rsT s O) (GlobalTheory.KS.AdjDlog.val_res_pullU m hle (L.g (c 0) (c' 0)))).trans
    (rsT_pbT m hle h _))

theorem sec_rel {L : LB X} (m : Y ⟶ X) (k : ℕ) (τ : SecM m L k) (c c' : Fin 1 → L.ι) {O : Y.Opens}
    (h : O ≤ LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c') :
    rsT (τ.f c) O = pbT m (L.g (c 0) (c' 0)).val O ^ k * rsT (τ.f c') O := by
  have e := congrArg (fun s => rsT s O) (τ.compat c c')
  simp only [map_eq_rsT] at e
  have h' : O ≤ (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
      (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' := h
  rwa [rsT_rsT inf_le_left h', rsT_mul, linComb_g m k c c' h, rsT_rsT inf_le_right h'] at e

theorem exists_acts : ∀ {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] {n : ℕ} {X : Scheme.{0}}
    (m : G.left ⟶ X) (L : LB X), L.IsLB → ∀ (dd : Fin n → Fld G.left), (∀ a, IsField ⊤ (dd a)) →
    ∀ (D : R → R) (h : Heat G m L dd D) (k : ℕ) (τ : SecM m L k), ∃ τ' : SecM m L k, h.Acts k τ τ' := by
  intro R _ G _ _ n X m L hL dd hdd D h k τ

  have loc : ∀ i O (hO : O ≤ h.W i) (f : Γ(G.left, h.W i)),
      rsT (op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) O =
        op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O (rsT f O) := by
    intro i O hO f
    have hd : ∀ g, resG G.left hO (h.d i (h.W i) g) = h.d i O (resG G.left hO g) :=
      fun g => ((h.lift i).1.2.2 (h.W i) O hO le_rfl g).symm
    have hdd' : ∀ a g, resG G.left hO (dd a (h.W i) g) = dd a O (resG G.left hO g) :=
      fun a g => ((hdd a).2.2 (h.W i) O hO le_top g).symm
    have hc : ∀ r, resG G.left hO (constFn G.hom (h.W i) r) = constFn G.hom O r :=
      fun r => (rsT_of_le hO _).symm.trans (rsT_constFn G.hom hO r)
    have hp : ∀ q : Γ(G.left, h.W i), resG G.left hO (rsT q (h.W i)) = rsT q O := fun q => by
      rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
    rw [rsT_of_le hO, rsT_of_le hO]
    simp only [op, map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]
  obtain ⟨F, hF⟩ : ∃ F : ∀ i, Γ(G.left, h.W i), ∀ i,
      F i = op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) (rsT (τ.f fun _ => h.j i) (h.W i)) :=
    ⟨_, fun _ => rfl⟩
  have hWc : ∀ i, h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) := fun i => le_wchart _ (h.le i)

  have Fc : ∀ i i', rsT (F i) (h.W i ⊓ h.W i') =
      pbT m (L.g (h.j i) (h.j i')).val (h.W i ⊓ h.W i') ^ k * rsT (F i') (h.W i ⊓ h.W i') := by
    intro i i'
    have hWc' : ∀ i, h.W i ≤ (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U (fun _ => h.j i) := hWc
    rw [hF, hF, loc i _ inf_le_left, loc i' _ inf_le_right, rsT_rsT (hWc' i) inf_le_left,
      rsT_rsT (hWc' i') inf_le_right,
      sec_rel m k τ (fun _ => h.j i) (fun _ => h.j i') (inf_le_inf (hWc i) (hWc i'))]
    exact h.glue k i i' _ le_rfl _
  have cov : ∀ V : G.left.Opens, V ≤ ⨆ i, V ⊓ h.W i := by
    intro V y hy
    have : y ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hi⟩

  have glue : ∀ c : Fin 1 → L.ι, ∃ t : Γ(G.left, LB.wchart L (fun _ : Fin 1 => m) c), ∀ i,
      rsT t (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) =
        pbT m (L.g (c 0) (h.j i)).val (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ^ k *
          rsT (F i) (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) := by
    intro c
    refine exists_rsT_eq (fun i => LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) (fun i => inf_le_left) (cov _) _
      fun i i' => ?_
    have hN1 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i := inf_le_left
    have hN2 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i' := inf_le_right
    have hNW : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        h.W i ⊓ h.W i' := fun y hy => ⟨hy.1.2, hy.2.2⟩
    have hV : ∀ i, LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i)) :=
      fun i y hy => ⟨pullbackBundleChart_le_preimage c hy.1, h.le i hy.2⟩
    have h3 : (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i) ⊓ (LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i') ≤
        m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i) ⊓ L.U (h.j i')) :=
      fun y hy => ⟨⟨pullbackBundleChart_le_preimage c hy.1.1, h.le i hy.1.2⟩, h.le i' hy.2.2⟩
    rw [rsT_mul, rsT_mul, rsT_pow' hN1, rsT_pow' hN2, rsT_pbT m (hV i) hN1, rsT_pbT m (hV i') hN2,
      rsT_rsT inf_le_right hN1, rsT_rsT inf_le_right hN2, ← rsT_rsT inf_le_left hNW (F i), Fc, rsT_mul,
      rsT_pow' hNW, rsT_pbT m (show h.W i ⊓ h.W i' ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i')) from fun y hy => ⟨h.le i hy.1, h.le i' hy.2⟩) hNW, rsT_rsT inf_le_right hNW,
      ← _root_.mul_assoc, ← _root_.mul_pow, pbT_cocycle hL m _ _ _ h3]
  choose t ht using glue

  refine ⟨⟨t, fun c c' => ?_⟩, fun i => ?_⟩
  · have goal : rsT (t c) ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c') =
        ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).g c c').val *
          rsT (t c') ((LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
            (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c') := ?_
    · exact (rsT_of_le inf_le_left (t c)).symm.trans (goal.trans (congrArg _ (rsT_of_le inf_le_right (t c'))))
    refine eq_of_rsT_eq (fun i => LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i)
      (fun i => inf_le_left) (cov _) _ _ fun i => ?_
    have a1 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i := fun y hy => ⟨hy.1.1, hy.2⟩
    have a2 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i := fun y hy => ⟨hy.1.2, hy.2⟩
    have hV : ∀ c : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => m) c ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (h.j i)) :=
      fun c y hy => ⟨pullbackBundleChart_le_preimage c hy.1, h.le i hy.2⟩
    have h3 : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        m ⁻¹ᵁ (L.U (c 0) ⊓ L.U (c' 0) ⊓ L.U (h.j i)) :=
      fun y hy => ⟨⟨pullbackBundleChart_le_preimage c hy.1.1, pullbackBundleChart_le_preimage c' hy.1.2⟩, h.le i hy.2⟩
    have e' : LB.wchart L (fun _ : Fin 1 => m) c ⊓ LB.wchart L (fun _ : Fin 1 => m) c' ⊓ h.W i ≤
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
          (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' := inf_le_left
    have eL : (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' ≤ LB.wchart L (fun _ : Fin 1 => m) c := inf_le_left
    have eR : (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c ⊓
        (LB.LinComb L (K := Fin 1) (fun _ => m) fun _ => (k : ℤ)).U c' ≤ LB.wchart L (fun _ : Fin 1 => m) c' := inf_le_right
    erw [rsT_rsT eL e', rsT_mul, rsT_rsT eR e', linComb_g m k c c' e',
      ← rsT_rsT inf_le_left a1 (t c), ← rsT_rsT inf_le_left a2 (t c'), ht, ht, rsT_mul, rsT_mul,
      rsT_pow' a1, rsT_pow' a2, rsT_pbT m (hV c) a1, rsT_pbT m (hV c') a2, rsT_rsT inf_le_right a1,
      rsT_rsT inf_le_right a2, ← _root_.mul_assoc, ← _root_.mul_pow, pbT_cocycle hL m _ _ _ h3]
  ·
    change rsT (t fun _ => h.j i) (h.W i) = _
    have a : h.W i ≤ LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) ⊓ h.W i := le_inf (hWc i) le_rfl
    rw [← rsT_rsT inf_le_left a, ht, rsT_mul, rsT_pow' a,
      rsT_pbT m (show LB.wchart L (fun _ : Fin 1 => m) (fun _ => h.j i) ⊓ h.W i ≤ m ⁻¹ᵁ (L.U (h.j i) ⊓ L.U (h.j i))
        from fun y hy => ⟨pullbackBundleChart_le_preimage _ hy.1, h.le i hy.2⟩) a, rsT_rsT inf_le_right a, rsT_self,
      GlobalTheory.KS.AdjDlog.pbT_g_self hL m (h.j i) (h.le i), one_pow, _root_.one_mul, hF]

end GlobalTheory.Heat.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRaynaudGaugeGeneratorWeightNeg
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

namespace GlobalTheory.Heat.ShiftGauge

theorem toUnit_left {R : Type} [CommRing R] (T : Over (Sp R)) : (toUnit T).left = T.hom := by
  simpa using Over.w (toUnit T)

theorem exists_gauge : ∀ (R : Type) [CommRing R] [IsDomain R] (Q : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O Q.X] (oa : Q.OAct O) (Y : Ray oa) (mu : Q.X) (x : 𝟙_ (Over (Sp R)) ⟶ Y.H), (x ≫ Y.q) * Q.c mu = 1 → ∀ ψ₀ : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c mu).left) fun _ => -1), ψ₀.IsGen → ∃ e : LB.Gen (LB.LinComb Q.P.L (K := Fin 2) ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] ![1, -1]), e.IsGen ∧ (∀ (j : Fin 2 → Q.P.L.ι) (V : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ V ≤ LB.wchart Q.P.L ![Y.q.left, (𝟙 Y.H * (toUnit Y.H ≫ x)).left ≫ Y.q.left] j → IsWt Y (-mu) (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V))) ∧ ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J → val e y.left z J * val ψ₀ T.hom z J * val Q.rig T.hom z J * val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J = 1 := by
  intro R _ _ Q O _ _ _ oa Y mu x hx ψ₀ hψ₀
  have hL : Q.P.L.IsLB := Q.P.isLB
  have hq : IsMonHom Y.q := Y.q_linear.isMonHom
  set Tx : Y.H ⟶ Y.H := 𝟙 Y.H * (toUnit Y.H ≫ x) with hTx

  have hTq : Tx ≫ Y.q = Y.q * (toUnit Y.H ≫ x ≫ Y.q) := by
    rw [hTx, MonObj.mul_comp, Category.id_comp, Category.assoc]
  have hcq : cP Q Y.H mu * (Tx ≫ Y.q) = Y.q := by
    rw [hTq, cP, _root_.mul_comm, _root_.mul_assoc, ← MonObj.comp_mul (toUnit Y.H) (x ≫ Y.q) (Q.c mu), hx,
      MonObj.comp_one, _root_.mul_one]
  have e₁ : (cP Q Y.H mu).left = Y.H.hom ≫ (Q.c mu).left := by rw [cP, Over.comp_left, toUnit_left]
  have e₂ : (1 : Y.H ⟶ Q.P.A).left = Y.H.hom ≫ eSec Q.P.A := by rw [Hom.one_def, Over.comp_left, toUnit_left]; rfl
  let s := (Y.Φ Y.H Tx).s mu
  let w := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.pullGen Q.P.L _ _ ψ₀ Y.H.hom)
    (LB.pullGen Q.P.L _ _ Q.rig Y.H.hom)) s
  have hw : w.IsGen := mulGen_isGen _ _ _ _ _ _ _ (mulGen_isGen _ _ _ _ _ _ _ (pullGen_isGen _ _ _ _ hψ₀ _)
    (pullGen_isGen _ _ _ _ Q.rig_gen _)) ((Y.Φ Y.H Tx).isGen mu)
  have hF : FormEq (Sum.elim (Sum.elim (fun _ : PUnit => Y.H.hom ≫ (Q.c mu).left)
      (fun _ : PUnit => Y.H.hom ≫ eSec Q.P.A)) (DegPre.gtφT Q Y.H (Y.Φ Y.H Tx).b mu))
      (fun k => - Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (fun _ : PUnit => (1 : ℤ))) DegPre.gtε k)
      (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] := by
    intro U _ h
    simp only [zpow_neg, Finset.prod_inv_distrib, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
      Fintype.prod_unique, Fin.prod_univ_two]
    rw [GlobalTheory.TorusModel.prod_pt, Ray.Φ_b, hcq, e₁, e₂]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Over.comp_left]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    abel
  obtain ⟨e, he, hve⟩ := exists_gen hL hF (LB.invGen Q.P.L _ _ w) (invGen_isGen _ _ _ _ hw)
  have hval : ∀ (T : Over (Sp R)) (y : T ⟶ Y.H) (z : T.left) (J : (T.left ⟶ Q.P.A.left) → Q.P.L.ι), Good Q.P.L z J →
      val e y.left z J = (val ψ₀ T.hom z J * val Q.rig T.hom z J *
        val ((Y.Φ T (y * (toUnit T ≫ x))).s mu) (𝟙 _) z J)⁻¹ := by
    intro T y z J hJ
    have hy : y ≫ Tx = y * (toUnit T ≫ x) := by
      rw [hTx, MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (y ≫ toUnit Y.H) (toUnit T)]
    have hp := ((GlobalTheory.TorusModel.isPull_iff y (Y.Φ Y.H Tx) (Y.Φ T (y ≫ Tx))).1 (Y.rep.1 T Y.H y Tx)).2 mu z J hJ
    rw [hve _ _ z J hJ, val_inv, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, Over.w y, ← hy]
    rw [show val ((Y.Φ T (y ≫ Tx)).s mu) (𝟙 _) z J = _ from hp]
  refine ⟨e, he, ?_, fun T y z J hJ => ?_⟩
  · intro j V hV S _ φ x₁ x₁' c a a' ha ha' hV₁ hV₂ hqq hc
    subst ha ha'
    have hV' : Y.q.left ⁻¹ᵁ V ≤
        (LB.LinComb Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1]).U j := hV
    have germ : ∀ (b : Sp S ⟶ Y.H.left), ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V) → ∀ z,
        gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom
          (valR b (Y.q.left ⁻¹ᵁ V) (rsT (e.s j).val (Y.q.left ⁻¹ᵁ V)))) =
          gs b z (LB.wchart Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) j)
            (e.s j).val := by
      intro b hb z
      rw [valR, dif_pos hb, Iso.hom_inv_id_apply, rsT, dif_pos hV']
      refine (gs_res (𝟙 _) z hb trivial _).trans ((gs_pull (𝟙 _) b z _ (hb trivial) _).trans ?_)
      rw [Category.id_comp]
      exact gs_res b z hV (hb trivial) _
    have hq' : x₁'.left ≫ Y.q.left = x₁.left ≫ Y.q.left := congrArg CommaMorphism.left hqq
    have hu : ∀ u : Over.mk (spMap φ) ⟶ Y.H, u ≫ Tx ≫ Y.q = (u ≫ Y.q) * (toUnit _ ≫ x ≫ Y.q) := fun u => by
      rw [hTq, MonObj.comp_mul, ← Category.assoc u (toUnit Y.H), toUnit_unique (u ≫ toUnit Y.H) (toUnit _)]
    have hT₀ : x₁' ≫ Tx ≫ Y.q = x₁ ≫ Tx ≫ Y.q := by rw [hu, hu, hqq]
    have hT : x₁'.left ≫ Tx.left ≫ Y.q.left = x₁.left ≫ Tx.left ≫ Y.q.left := congrArg CommaMorphism.left hT₀
    have hk : ∀ k, x₁'.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k =
        x₁.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k :=
      Fin.forall_fin_two.2 ⟨hq', hT⟩
    apply (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv.symm.injective
    refine fn_ext fun z _ => ?_
    choose I hI using fun χ : (Over.mk (spMap φ)).left ⟶ Q.P.A.left => exists_chart hL (χ z)
    have hJ : Good Q.P.L z I := hI
    have hgv : ∀ (b : Sp S ⟶ Y.H.left) (hb : ⊤ ≤ b ⁻¹ᵁ (Y.q.left ⁻¹ᵁ V)),
        gs b z (LB.wchart Q.P.L (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) j)
          (e.s j).val = (trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] b z j
            (fun k => I (b ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) *
            val e b z I).val := fun b hb =>
      (gs_unit b z _ (hV (hb trivial)) _).trans (congrArg Units.val (gen_trans he b z (hV (hb trivial)) (hJ.mem _ b)))
    have htr : trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] x₁'.left z j
          (fun k => I (x₁'.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) =
        trF (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) ![1, -1] x₁.left z j
          (fun k => I (x₁.left ≫ (![Y.q.left, Tx.left ≫ Y.q.left] : Fin 2 → (Y.H.left ⟶ Q.P.A.left)) k)) := by
      unfold trF
      exact Finset.prod_congr rfl fun k _ => congrArg (fun ψ => gm ψ z (Q.P.L.U (j k) ⊓ Q.P.L.U (I ψ)) (Q.P.L.g (j k) (I ψ)) ^ (![1, -1] : Fin 2 → ℤ) k) (hk k)
    have ve : val e x₁'.left z I = gm (𝟙 (Over.mk (spMap φ)).left) z ⊤ (unitOn (c (-mu))) * val e x₁.left z I := by
      have hb : (Y.Φ _ x₁').b = (Y.Φ _ x₁).b := by rw [Ray.Φ_b, Ray.Φ_b, hqq]
      have h1 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁ (toUnit _ ≫ x))).2 mu z I hJ
      have h2 := ((GlobalTheory.TorusModel.isAdd_iff _ _ _).1 (Y.rep.2 _ x₁' (toUnit _ ≫ x))).2 mu z I hJ
      rw [hb] at h2
      have h3 := hc mu z I hJ
      have h4 := GlobalTheory.TorusModel.cv_add (Y.Φ _ x₁) hJ mu (-mu)
      have h5 := GlobalTheory.TorusModel.cv_add (Y.Φ _ x₁') hJ mu (-mu)
      rw [add_neg_cancel, GlobalTheory.TorusModel.cv_zero _ hJ] at h4 h5
      rw [hb] at h5
      have h6 := hc (-mu) z I hJ
      rw [hval _ x₁ z I hJ, hval _ x₁' z I hJ]
      apply Additive.ofMul.injective
      have g1 := congrArg Additive.ofMul h1
      have g2 := congrArg Additive.ofMul h2
      have g3 := congrArg Additive.ofMul h3
      have g4 := congrArg Additive.ofMul h4
      have g5 := congrArg Additive.ofMul h5
      have g6 := congrArg Additive.ofMul h6
      simp only [ofMul_mul, ofMul_inv, ofMul_one] at g1 g2 g3 g4 g5 g6 ⊢
      linear_combination (norm := abel) g1 - g2 - g4 + g5 + g6
    show gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _) =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom _)
    rw [germ _ hV₂ z, map_mul, gs_mul (𝟙 _) z ⊤ trivial, germ _ hV₁ z, hgv _ hV₂, hgv _ hV₁, htr, ve,
      show (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (c (-mu) : S) = (unitOn (c (-mu))).val from rfl,
      gs_unit (𝟙 _) z ⊤ trivial, ← Units.val_mul]
    exact congrArg Units.val (_root_.mul_left_comm _ _ _)
  · rw [hval T y z J hJ]
    simp only [_root_.mul_assoc, inv_mul_cancel]

end GlobalTheory.Heat.ShiftGauge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRescalePsiW0
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiRescale

open GlobalTheory.PsiWZeroPull (prod_four)

section Geometry

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

abbrev FourGen (L : LB A.left) (f : A ⟶ A) : Type :=
  LB.Gen (LB.LinComb L (K := Fin 4) ![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2])

theorem exists_normalised {L : LB A.left} (hL : L.IsLB) (f : A ⟶ A) [IsMonHom f] (u : FourGen L f) (hu : u.IsGen) :
    ∃ u' : FourGen L f, u'.IsGen ∧ LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ u' (eSec A)) (LB.oneGen L) := by
  obtain ⟨t, ht, hv⟩ := exists_gen hL
    (φ' := (![(padd A (𝟙 _) f).left, 𝟙 A.left, f.left, (toUnit A ≫ η[A]).left] : Fin 4 → _)) (ε' := ![1, -2, -1, 2])
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ rfl
        (DVR.prod_neg _ _ (prod_four f (1 : A ⟶ A) k))) ?_
      rw [MonObj.one_comp, _root_.mul_one (1 : A ⟶ A)]
      refine mul_eq_left.2 (inv_eq_one.2 ?_)
      group)
    (LB.mulGen L _ _ _ _ u (LB.invGen L _ _ (LB.pullGen L _ _ u (1 : A ⟶ A).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hu (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _)))
  refine ⟨t, ht, corr_of_val hL fun y J hJ => ?_⟩
  have e : eSec A ≫ (1 : A ⟶ A).left = eSec A :=
    congrArg (fun q : 𝟙_ (Over S) ⟶ A => q.left) ((MonObj.comp_one (M := A) η[A]).trans (by simp [Hom.one_def]))
  rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.assoc, e, mul_inv_cancel]

end Geometry

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O D.X]

open DVR (cP cPoint_add)

theorem cPoint_smul (oa : D.OAct O) (w : O) (a : D.X) : cP D (TK R) (w • a) = cP D (TK R) a ≫ oa.onB.act w := by
  rw [cP, cP, oa.c_lin, Category.assoc]

end GlobalTheory.PsiRescale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSubfamilyUniqueReprOfSpanningLocalRing
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

namespace GlobalTheory

theorem exists_subfamily_unique_repr_of_spanning_localRing
    (R : Type) [CommRing R] [IsLocalRing R] (M : Type) [AddCommGroup M] [Module R M] (d g : ℕ) :
    Nonempty (Module.Basis (Fin d) R M) → ∀ w : Fin g → M,
      (∀ u : M, ∃ cf : Fin g → R, u = ∑ a, cf a • w a) →
      ∃ e : Fin d → Fin g, ∀ u : M, ∃! cf : Fin d → R, u = ∑ a, cf a • w (e a) := by
  rintro ⟨b⟩ w hw
  haveI : Module.Finite R M := Module.Finite.of_basis b
  let V := IsLocalRing.ResidueField R ⊗[R] M
  let v : Fin g → V := fun a => (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] w a
  have hsp : Submodule.span (IsLocalRing.ResidueField R) (Set.range v) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c m =>
      obtain ⟨cf, rfl⟩ := hw m
      have : c ⊗ₜ[R] (∑ a, cf a • w a) = c • ∑ a, cf a • v a := by
        simp only [v, TensorProduct.tmul_sum, Finset.smul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
          TensorProduct.smul_tmul', smul_comm c (cf a) (1 : IsLocalRing.ResidueField R),
          smul_eq_mul, _root_.mul_one]
      rw [this]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a _ => ?_)
      exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ hx hy
  obtain ⟨κ, a, ha, hspa, hli⟩ := exists_linearIndependent' (IsLocalRing.ResidueField R) v
  let bk : Module.Basis κ (IsLocalRing.ResidueField R) V :=
    Module.Basis.mk hli (by rw [hspa, hsp])
  let bV : Module.Basis (Fin d) (IsLocalRing.ResidueField R) V :=
    Algebra.TensorProduct.basis (IsLocalRing.ResidueField R) b
  let eq : Fin d ≃ κ := bV.indexEquiv bk
  refine ⟨a ∘ eq, ?_⟩
  have hspR : Submodule.span R (Set.range (w ∘ a ∘ eq)) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (w ∘ a ∘ eq) (bk.reindex eq.symm) (fun i => by
      simp [bk, v])
  let f : (Fin d → R) →ₗ[R] M := Fintype.linearCombination R (w ∘ a ∘ eq)
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspR
  have hfi : Function.Injective f :=
    OrzechProperty.injective_of_surjective_of_injective b.equivFun.symm.toLinearMap f
      b.equivFun.symm.injective hf
  intro u
  obtain ⟨cf, hcf⟩ := hf u
  refine ⟨cf, ?_, ?_⟩
  · rw [← hcf]; simp [f, Fintype.linearCombination_apply]
  · intro cf' hcf'
    apply hfi
    rw [hcf]; simp [f, Fintype.linearCombination_apply, hcf']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueDualNumberThickeningOpenDecomp
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

noncomputable section

namespace GlobalTheory.SpThickening

open GlobalTheory.RelConstThickening

theorem existsUnique_affine {R : Type} [CommRing R] {Z P : Scheme.{0}} (h : Z ⟶ Sp R) (p₁ : P ⟶ Sp (DualNumber R))
    (p₂ : P ⟶ Z) (H : IsPullback p₂ p₁ h (spMap (algebraMap R (DualNumber R))))
    {V : Z.Opens} (hV : IsAffineOpen V) (F : Γ(P, p₂ ⁻¹ᵁ V)) : ∃! ab : Γ(Z, V) × Γ(Z, V),
      F = (p₂.app V).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app V).hom ab.2 := by
  refine existsUnique_of_isPushout (K := R) (constHom h V) (p₂.app V) (constHom p₁ (p₂ ⁻¹ᵁ V)) ?_ F
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := V) (UY := p₂ ⁻¹ᵁ V) le_top le_top
    (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hV)
  refine po.of_iso (Scheme.ΓSpecIso (.of R)) (Iso.refl _) (Scheme.ΓSpecIso (.of (DualNumber R))) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · ext x; simp [RelConstThickening.constHom, RingHom.comp_apply]
  · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    simp
  · simp [Scheme.Hom.app_eq_appLE]
  · ext x; simp [RelConstThickening.constHom, RingHom.comp_apply]

theorem existsUnique_decomp : ∀ (R : Type) [CommRing R] {Z P : Scheme.{0}} (h : Z ⟶ Sp R) (p₁ : P ⟶ Sp (DualNumber R)) (p₂ : P ⟶ Z), IsPullback p₂ p₁ h (spMap (algebraMap R (DualNumber R))) → ∀ (O : Z.Opens) (F : Γ(P, p₂ ⁻¹ᵁ O)), ∃! ab : Γ(Z, O) × Γ(Z, O), F = (p₂.app O).hom ab.1 + constFn p₁ _ DualNumber.eps * (p₂.app O).hom ab.2 :=
  fun _ _ _ _ h p₁ p₂ H O F =>
    existsUnique_comb (W := ⊤) (fun _ hV _ F => existsUnique_affine h p₁ p₂ H hV F) O le_top F

end GlobalTheory.SpThickening

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsTailMore
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

noncomputable section
namespace GlobalTheory.LocReg

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

def chartHom (Y : Model Xo c β) (U : Y.X.affineOpens) {k : Type} [Field k] {m d : ℕ} (ξ : Sp (ChartRing k m d) ⟶ gen Y)
    (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1) : Γ(Y.X, U.1) →+* ChartRing k m d :=
  (Scheme.stalkClosedPointTo ξ).hom.comp
    (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)

end GlobalTheory.LocReg
end
end

