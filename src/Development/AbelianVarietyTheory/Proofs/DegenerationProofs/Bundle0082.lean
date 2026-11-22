import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsLevelPoint
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationEqPolarFormOfWeightZeroMax
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH.ValLat

theorem norm_le_of_hasSum {I C : Type} [NormedAddCommGroup C] [IsUltrametricDist C] {f : I → C} {a : C}
    (h : HasSum f a) {r : ℝ} (hr : 0 ≤ r) (hf : ∀ x, ‖f x‖ ≤ r) : ‖a‖ ≤ r := by
  rw [← h.tsum_eq]
  exact IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg hr hf

theorem le_norm_of_hasSum {I C : Type} [NormedAddCommGroup C] [IsUltrametricDist C] {f : I → C} {a : C}
    (h : HasSum f a) {b : I} (hf : ∀ x, x ≠ b → ‖f x‖ < ‖f b‖) : ‖f b‖ ≤ ‖a‖ := by
  rcases (norm_nonneg (f b)).eq_or_lt with h0 | h0
  · rw [← h0]; exact norm_nonneg _
  obtain ⟨r, hr0, hrb, hr⟩ : ∃ r, 0 ≤ r ∧ r < ‖f b‖ ∧ ∀ x, x ≠ b → ‖f x‖ ≤ r := by
    have ht := (tendsto_zero_iff_norm_tendsto_zero.1 h.summable.tendsto_cofinite_zero).eventually
      (gt_mem_nhds (half_pos h0))
    have hfin : {x | x ≠ b ∧ ‖f b‖ / 2 ≤ ‖f x‖}.Finite :=
      (Filter.eventually_cofinite.1 ht).subset fun x hx => not_lt.2 hx.2
    rcases Set.eq_empty_or_nonempty {x | x ≠ b ∧ ‖f b‖ / 2 ≤ ‖f x‖} with he | he
    · refine ⟨‖f b‖ / 2, by positivity, half_lt_self h0, fun x hx => ?_⟩
      by_contra hc
      exact (Set.eq_empty_iff_forall_notMem.1 he x) ⟨hx, (not_le.1 hc).le⟩
    · obtain ⟨y, hy, hm⟩ := Set.exists_max_image _ (fun x => ‖f x‖) hfin he
      refine ⟨‖f y‖, norm_nonneg _, hf y hy.1, fun x hx => ?_⟩
      by_cases hc : ‖f b‖ / 2 ≤ ‖f x‖
      · exact hm x ⟨hx, hc⟩
      · exact (not_le.1 hc).le.trans hy.2
  have h1 := norm_le_of_hasSum (h.update b 0) hr0 fun x => by
    rcases eq_or_ne x b with rfl | hx
    · simpa using hr0
    · rw [Function.update_of_ne hx]; exact hr x hx
  by_contra hc
  have h2 := IsUltrametricDist.norm_add_le_max a (-(0 - f b + a))
  rw [norm_neg, show a + -(0 - f b + a) = f b by abel] at h2
  exact h2.not_gt (max_lt (not_le.1 hc) (h1.trans_lt hrb))

theorem main : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : QuadraticMap ℤ X ℝ) (g N : ℕ) (J : Type) (cls : J → X) (p : ℕ) [Fact p.Prime] (w : J → PadicAlgCl p) (ν : X →+ ℝ), Filter.Tendsto q Filter.cofinite Filter.atTop → Module.finrank ℤ X ≤ g → 1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2) < N → (∀ i, Short q N (cls i)) → Ser q N cls w ν → (∃ i₀, cls i₀ = 0 ∧ ∀ i, ‖w i‖ ≤ ‖w i₀‖) → ∃ m, ∀ α, ν α = QuadraticMap.polar q m α := by
  intro X _ _ _ q g N J cls p _ w ν hq hg hN _ ⟨t, κ, hκ, hsum, hcls, hsz⟩ ⟨i₀, hi₀, hmax⟩
  have hQ := GlobalTheory.posDef_realExt_of_tendsto q hq
  have hN0 : (0 : ℝ) < N := lt_trans (by positivity) hN
  obtain ⟨m, hm⟩ := ClassMin.exists_global_min (ClassMin.realExtension_eq_realExt q ▸ hQ) ν one_pos
  simp only [div_one] at hm
  let ν' : X →+ ℝ := ν + (QuadraticMap.polarBilin q m).toAddMonoidHom
  have hν' : ∀ x, ν' x = ν x + QuadraticMap.polar q m x := fun x => rfl
  by_cases h0 : ν' = 0
  · refine ⟨-m, fun α => ?_⟩
    have := hν' α
    rw [h0] at this
    rw [QuadraticMap.polar_neg_left]
    simp only [AddMonoidHom.zero_apply] at this
    linarith
  exfalso
  obtain ⟨α, -, h1, h2⟩ := ClassMin.exists_shifted_lt_of_le (N := (N : ℤ)) hg hQ (by exact_mod_cast hN) h0
    fun y => by
      have := hm (m + y)
      rw [map_add ν] at this
      rw [hν', QuadraticMap.polar]
      linarith
  simp only [natCast_zsmul, Int.cast_natCast] at h1 h2
  have hshift : ∀ x, q (x + N • m) / N + ν (x + N • m) = q x / N + ν' x + N * (q m + ν m) := fun x => by
    have e := ClassMin.map_add_zsmul q x m (N : ℤ)
    rw [natCast_zsmul] at e
    rw [e, hν', map_add, map_nsmul, nsmul_eq_mul, QuadraticMap.polar_comm q m x]
    push_cast
    field_simp
    ring
  obtain ⟨i, hi⟩ := (hsz (α + N • m)).2
  obtain ⟨u, hu⟩ := hcls (α + N • m) i (by
    rw [← norm_pos_iff, hi]; positivity)
  have hA : ‖t (α + N • m) i‖ ≤ ‖w i‖ := le_norm_of_hasSum (f := fun x => t x i) (hsum i) fun x hx => by
    by_cases hz : t x i = 0
    · rw [hz, norm_zero, hi]; positivity
    obtain ⟨v, hv⟩ := hcls x i hz
    have e : x = α + N • (v - u) + N • m := by
      rw [hv, add_right_comm, hu, smul_sub]; abel
    have h3 := h1 (v - u) fun h => hx (by rw [e, h, smul_zero, add_zero])
    refine ((hsz x).1 i).trans_lt ?_
    rw [hi]
    refine mul_lt_mul_of_pos_left (Real.exp_lt_exp.2 ?_) hκ
    have e1 := hshift (α + N • (v - u))
    rw [← e] at e1
    have e2 := hshift α
    rw [sub_div, sub_div]
    linarith
  have hB : ‖w i₀‖ ≤ κ * Real.exp (-(N * (q m + ν m))) := norm_le_of_hasSum (hsum i₀) (by positivity) fun x => by
    by_cases hz : t x i₀ = 0
    · rw [hz, norm_zero]; positivity
    obtain ⟨v, hv⟩ := hcls x i₀ hz
    refine ((hsz x).1 i₀).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hκ.le)
    have e := ClassMin.shifted_zsmul (Q := q) (N := (N : ℤ)) (by exact_mod_cast hN0.ne') ν v
    simp only [natCast_zsmul, Int.cast_natCast] at e
    rw [hv, hi₀, zero_add, map_zero, sub_zero, e]
    exact neg_le_neg (mul_le_mul_of_nonneg_left (hm v) hN0.le)
  have hC := (hA.trans (hmax i)).trans hB
  rw [hi] at hC
  have hD := Real.exp_le_exp.1 (le_of_mul_le_mul_left hC hκ)
  have h3 := h2 (m - u)
  have e : α + N • (m - u) = cls i := by
    rw [smul_sub, ← add_sub_assoc, hu]; abel
  rw [e] at h3
  have e2 := hshift α
  rw [sub_div] at hD
  linarith

end GlobalTheory.ZH.ValLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValuationsTorusExtensionPoints
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TorusVal
open GlobalTheory.ZH.GeoModel ReciprocityTheory.ChartRestriction.G.DVR

variable {p : ℕ} [Fact p.Prime]

def NormIs (z : Sp (PadicAlgCl p)) (a : ((Sp (PadicAlgCl p)).presheaf.stalk z)ˣ) (r : ℝ) : Prop :=
  ∃ x, toStk z x = a.val ∧ ‖x‖ = r

variable {z : Sp (PadicAlgCl p)}

theorem NormIs.mul {a b} {r s : ℝ} (h : NormIs z a r) (h' : NormIs z b s) : NormIs z (a * b) (r * s) := by
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨y, hy, rfl⟩ := h'
  exact ⟨x * y, by rw [map_mul, hx, hy, Units.val_mul], norm_mul _ _⟩

theorem toStk_inj : Function.Injective (toStk z) := by
  obtain rfl : z = cpt (PadicAlgCl p) := Subsingleton.elim (α := PrimeSpectrum (PadicAlgCl p)) _ _
  exact toStkA_injective

theorem NormIs.unique {a} {r s : ℝ} (h : NormIs z a r) (h' : NormIs z a s) : r = s := by
  obtain ⟨x, hx, rfl⟩ := h
  obtain ⟨y, hy, rfl⟩ := h'
  rw [toStk_inj (hx.trans hy.symm)]

theorem NormIs.inv {a} {r : ℝ} (h : NormIs z a r) : NormIs z a⁻¹ r⁻¹ := by
  obtain ⟨x, hx, rfl⟩ := h
  have h0 : x ≠ 0 := fun h0 => by
    have : toStk z 1 = toStk z 0 := by
      rw [map_one, ← a.mul_inv, ← hx, h0, map_zero, zero_mul]
    exact one_ne_zero (toStk_inj this)
  refine ⟨x⁻¹, ?_, norm_inv _⟩
  refine (Units.inv_eq_of_mul_eq_one_right ?_).symm
  rw [← hx, ← map_mul, mul_inv_cancel₀ h0, map_one]

theorem normIs_val {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp (PadicAlgCl p) ⟶ Y) (J) (j : K → L.ι) (hj : ∀ k, J (r ≫ φ k) = j k)
    (h : r z ∈ LB.wchart L φ j) : NormIs z (val t r z J) ‖valF r (LB.wchart L φ j) (t.s j).val‖ := by
  rw [val_of t r z J j hj]
  exact ⟨_, toStk_valF r _ z h _, rfl⟩

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω}
  {ρ : S.Real} {y₀ : S.R →+* PadicAlgCl p} {u : ρ.UTest p y₀}

theorem normIs_int {Y : Scheme.{0}} {K : Type} [Fintype K] {φ : K → (Y ⟶ u.D.toPre.P.A.left)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb u.D.toPre.P.L φ ε)) (r₀ : Sp (OO p) ⟶ Y)
    (h₀ : ∀ k, r₀ ≫ φ k ≫ u.D.toPre.P.A.hom = spMap u.j) {r : Sp (PadicAlgCl p) ⟶ Y} (hr : gPt p ≫ r₀ = r)
    {J} (hJ : u.IntGood J) : NormIs z (val t r z J) 1 := by
  subst hr
  have h : ⊤ ≤ r₀ ⁻¹ᵁ LB.wchart u.D.toPre.P.L φ (fun k => J (gPt p ≫ r₀ ≫ φ k)) := fun w _ =>
    Set.mem_iInter.2 fun k => hJ (r₀ ≫ φ k) (by rw [Category.assoc, h₀]) (x := w) trivial
  have e := normIs_val (z := z) t (gPt p ≫ r₀) J (fun k => J (gPt p ≫ r₀ ≫ φ k)) (fun k => rfl)
    (h (x := gPt p z) trivial)
  exact (norm_unit r₀ _ h _) ▸ e

theorem tf_hom : (TF (R := u.V) (PadicAlgCl p)).hom = gPt p ≫ spMap u.j := by
  show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  rfl

theorem normIs_th (x x' y : TF (R := u.V) (PadicAlgCl p) ⟶ u.D.toPre.P.A) {J} (hJ : u.IntGood J) :
    NormIs z (th u.D.toPre (T := TF (R := u.V) (PadicAlgCl p)) z J x x' y) 1 := by
  let T : Over (Sp u.V) := Over.mk (spMap u.j)
  let i₀ : TF (R := u.V) (PadicAlgCl p) ⟶ T := Over.homMk (gPt p) tf_hom.symm
  have ex : ∀ b : TF (R := u.V) (PadicAlgCl p) ⟶ u.D.toPre.P.A, ∃ m : T ⟶ u.D.toPre.P.A, i₀ ≫ m = b := fun b => by
    obtain ⟨ψ, h1, h2⟩ := exists_ext u b
    exact ⟨Over.homMk ψ h1, Over.OverMorphism.ext h2⟩
  obtain ⟨m, hm⟩ := ex x
  obtain ⟨m', hm'⟩ := ex x'
  obtain ⟨n, hn⟩ := ex y
  refine normIs_int (φ := thφ u.D.toPre.P.A (x3 u.D.toPre.P.A)) (ε := thε) u.D.toPre.cub.t
    (lift m (lift m' n)).left (fun k => ?_) ?_ hJ
  · exact (congrArg _ (Over.w (psum _ _ _))).trans (Over.w _)
  · show i₀.left ≫ _ = _
    rw [← Over.comp_left, comp_lift, comp_lift, hm, hm', hn]

theorem normIs_gt {g : GtPtF u.D.toPre (PadicAlgCl p)} {J} (hG : Good u.D.toPre.P.L z J) (χ : u.D.toPre.X) :
    NormIs z (val (g.s χ) (𝟙 _) z J) ‖valF (𝟙 (Sp (PadicAlgCl p))) _
      ((g.s χ).s (fun k => J (DegPre.gtφ u.D.toPre (PadicAlgCl p) g.b χ k))).val‖ :=
  normIs_val (g.s χ) (𝟙 _) J _ (fun k => by rw [Category.id_comp]) (Set.mem_iInter.2 fun k => hG _)

theorem gtN_iff {g : GtPtF u.D.toPre (PadicAlgCl p)} {J} (hJ : u.IntGood J) (hG : Good u.D.toPre.P.L z J)
    {ν : u.D.toPre.X → ℝ} : u.GtN g ν ↔ ∀ χ, NormIs z (val (g.s χ) (𝟙 _) z J) (Real.exp (-ν χ)) := by
  refine ⟨fun h χ => h J hJ χ ▸ normIs_gt hG χ, fun h => ?_⟩
  obtain ⟨ν', h'⟩ := exists_gtN u g
  obtain rfl : ν' = ν := funext fun χ => by
    have := (h χ).unique (h' J hJ χ ▸ normIs_gt hG χ)
    simpa using this.symm
  exact h'

theorem top_le_of_j (U : (Sp u.V).Opens) (h : ⊤ ≤ spMap u.j ⁻¹ᵁ U) : ⊤ ≤ U := by
  have : IsLocalHom u.j := ((IsLocalRing.local_hom_TFAE u.j).out 0 3).2 (fun x hx => j_mem_max u x hx)
  refine (top_le_iff_cpt (𝟙 (Sp u.V)) U).2 ?_
  have e : spMap u.j (cpt (OO p)) = cpt u.V := IsLocalRing.comap_closedPoint u.j
  have := h (x := cpt (OO p)) trivial
  rw [← e]; exact this

theorem normIs_psi (l : u.Lab) {J} (hJ : u.IntGood J) (χ : u.D.toPre.X) :
    NormIs z (val (u.D.toPre.psi χ) (jFK (R := u.V) (PadicAlgCl p)) z J) (Real.exp (-l.q χ)) := by
  let j : PUnit → u.D.toPre.P.L.ι := fun _ => J (gPt p ≫ spMap u.j ≫ (u.D.toPre.c χ).left)
  have h1 : ⊤ ≤ (u.D.toPre.c χ).left ⁻¹ᵁ u.D.toPre.P.L.U (j PUnit.unit) :=
    top_le_of_j _ (hJ (spMap u.j ≫ (u.D.toPre.c χ).left) (by
      rw [Category.assoc, Over.w]; exact Category.comp_id _))
  have h2 : ⊤ ≤ (𝟙 (Sp (FractionRing u.V))) ⁻¹ᵁ LB.wchart u.D.toPre.P.L (fun _ : PUnit => ptK (u.D.toPre.c χ)) j :=
    fun w _ => Set.mem_iInter.2 fun k => by
      rw [QForm.ptK_eq]; exact h1 (x := jK u.V w) trivial
  have e := normIs_val (z := z) (u.D.toPre.psi χ) (jFK (R := u.V) (PadicAlgCl p)) J j (fun _ => by
    refine congrArg J ?_
    rw [← Category.assoc (gPt p), ← tf_hom]
    exact (congrArg _ (QForm.ptK_eq _ χ)).trans (Category.assoc _ _ _).symm) (h2 (x := jFK (R := u.V) (PadicAlgCl p) z) trivial)
  rw [← l.q_eq χ j h1]
  have e2 := GlobalTheory.Points.valR_spMap_comp (algebraMap (FractionRing u.V) (PadicAlgCl p)) (𝟙 (Sp (FractionRing u.V))) _ h2
    ((u.D.toPre.psi χ).s j).val
  rw [Category.comp_id] at e2
  exact (congrArg norm e2) ▸ e

theorem normIs_tau (l : u.Lab) {J} (hJ : u.IntGood J) (hG : Good u.D.toPre.P.L z J) (y χ : u.D.toPre.X) :
    NormIs z (val (u.D.toPre.tau y χ) (jFK (R := u.V) (PadicAlgCl p)) z J)
      (Real.exp (-QuadraticMap.polar l.q y χ)) := by
  have hr : NormIs z (val u.D.toPre.rigK (jFK (R := u.V) (PadicAlgCl p)) z J) 1 := by
    rw [DegPre.rigK, val_pull hG]
    refine normIs_int u.D.toPre.rig (spMap u.j) (fun k => ?_) tf_hom.symm hJ
    simp [eSec]
  have e := (((normIs_psi (z := z) l hJ (y + χ)).mul (normIs_psi l hJ y).inv).mul (normIs_psi l hJ χ).inv).mul hr.inv
  rw [DegPre.tau, val_mul hG, val_mul hG, val_mul hG, val_inv, val_inv, val_inv]
  convert e using 1
  rw [inv_one, _root_.mul_one, ← Real.exp_neg, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add, QuadraticMap.polar]
  congr 1; ring

theorem main : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∃ J, u.IntGood J ∧ ∀ z, Good u.D.toPre.P.L z J) ∧ (∀ g : GtPtF u.D.toPre (PadicAlgCl p), ∃ ν : u.D.toPre.X →+ ℝ, u.GtN g ν) ∧ (∀ (g : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', u.GtN g ν → u.GtN g ν' → ν = ν') ∧ (∀ (g g' g'' : GtPtF u.D.toPre (PadicAlgCl p)) ν ν', GtPtF.IsAdd g g' g'' → u.GtN g ν → u.GtN g' ν' → u.GtN g'' (ν + ν')) ∧ ∀ (y : u.D.toPre.X) (g : GtPtF u.D.toPre (PadicAlgCl p)), GtPtF.IsIota y g → u.GtN g (QuadraticMap.polar l.q y) := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u l
  obtain ⟨J, hJ, hG'⟩ := exists_intGood u
  let z : Sp (PadicAlgCl p) := cpt _
  have hG := hG' z
  refine ⟨⟨J, hJ, hG'⟩, fun g => ?_, gtN_unique u, fun g g' g'' ν ν' h a a' => ?_, fun y g h => ?_⟩
  · obtain ⟨ν, hν⟩ := exists_gtN u g
    refine ⟨AddMonoidHom.mk' ν fun χ χ' => ?_, hν⟩
    have a := (gtN_iff hJ hG).1 hν
    have e := gt_mul (𝟙 (TF (R := u.V) (PadicAlgCl p))) hG g χ χ'
    rw [Category.id_comp, Over.id_left] at e
    have b := (a (χ + χ')).mul (normIs_th (cP _ _ χ) (cP _ _ χ') g.b hJ)
    have c := (e ▸ b).unique ((a χ).mul (a χ'))
    rw [_root_.mul_one, ← Real.exp_add, Real.exp_eq_exp] at c
    linarith
  · obtain ⟨-, hs⟩ := (isAdd_iff _ _ _).1 h
    obtain ⟨ν'', hν⟩ := exists_gtN u g''
    obtain rfl : ν'' = ν + ν' := funext fun χ => by
      have b := ((gtN_iff hJ hG).1 hν χ).mul (normIs_th (cP _ _ χ) g.b g'.b hJ)
      have c := (hs χ z J hG ▸ b).unique (((gtN_iff hJ hG).1 a χ).mul ((gtN_iff hJ hG).1 a' χ))
      rw [_root_.mul_one, ← Real.exp_add, Real.exp_eq_exp] at c
      show ν'' χ = ν χ + ν' χ
      linarith
    exact hν
  · obtain ⟨-, hs⟩ := (isIota_iff _ _).1 h
    refine (gtN_iff hJ hG).2 fun χ => ?_
    have e := hs χ z J hG
    rw [Category.id_comp] at e
    exact e ▸ normIs_tau l hJ hG y χ

end GlobalTheory.ZH.TorusVal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeilPairingLabelledTorsionUniformTest
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.UT
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ZH

theorem weilIs_uTest : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), (∀ a, (x a).left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left) → ∀ a b (c : (PadicAlgCl p)ˣ), (c : PadicAlgCl p) = y₀ (algebraMap o S.R (S.ζ ^ (S.r * S.N * (eStd S.g _ a b).val))) → WeilIs u.A.A u.A.L (S.r * S.N : ℕ) (x a) (x b) (unitOn c) := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u x hx a b c hc
  have hpos : (S.r * S.N) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Nat.mul_ne_zero (by have := S.r_pos; omega) (by have := S.N_ge; omega))
  have hζ : IsUnit S.ζ := S.prim.isUnit hpos
  obtain ⟨c₀, hc₀⟩ := (hζ.pow (S.r * S.N * (eStd S.g _ a b).val)).map (algebraMap o S.R)
  have H := ρ.weil a b c₀ hc₀
  have hf : (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK = spMap y₀ := by
    refine Eq.trans ?_ (congrArg spMap u.fac)
    exact (Spec.map_comp (CommRingCat.ofHom u.yK)
      (CommRingCat.ofHom (algebraMap (FractionRing u.V) (PadicAlgCl p)))).symm
  let h : Over.mk ((TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK) ⟶ baseOver (Sp S.R) :=
    Over.homMk (spMap y₀) ((Category.comp_id _).trans hf.symm)
  have H' := CommPairing.weilIs_pull hL.globalFns ρ.P.isAb ρ.P.isLB h H
  have e : Units.map h.left.appTop.hom.toMonoidHom (unitOn c₀) = unitOn c := by
    refine Units.ext ?_
    refine (congrArg (fun q => q.hom c₀.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom y₀))).symm.trans ?_
    show (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom (y₀ c₀.val) =
      (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).inv.hom c.val
    rw [hc, hc₀]
  rw [e] at H'
  exact (weilIs_grpPullback_of_comm' _ _ ρ.P.A u.A.A (spMap u.yK) u.φ ρ.P.L u.A.L ρ.P.isLB u.A.isLB u.cart u.lb
    (TFK (R := u.V) (PadicAlgCl p)) _ (x a) (x b) (h ≫ ρ.pt a) (h ≫ ρ.pt b) (unitOn c) (hx a).symm (hx b).symm).2 H'

end GlobalTheory.ZH
end
end

