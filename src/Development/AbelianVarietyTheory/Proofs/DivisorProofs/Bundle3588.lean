import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0210
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2391
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3432
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3576
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2727
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyUWit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3383
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2557
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2987
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryClassicalTraitPeriodsBoundedBelow
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc.ShortBound

theorem exists_not_dvd_le {X : Type} [AddCommGroup X] (β : LinearMap.BilinForm ℤ X)
    (hβ : ∀ y, y ≠ 0 → 0 < β y y) (m : ℕ) (hm : 2 ≤ m) :
    ∀ (k : ℕ) (x : X), (β x x).toNat = k → x ≠ 0 →
      ∃ x', x' ≠ 0 ∧ (¬ ∃ v, x' = m • v) ∧ β x' x' ≤ β x x := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro x hk hx
    by_cases hd : ∃ v, x = m • v
    · obtain ⟨v, rfl⟩ := hd
      have hv : v ≠ 0 := by rintro rfl; simp at hx
      have hvv := hβ v hv
      have e : β (m • v) (m • v) = (m : ℤ) * ((m : ℤ) * β v v) := by
        simp [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      have hm' : (2 : ℤ) ≤ m := by exact_mod_cast hm
      have h2 : 2 * β v v ≤ (m : ℤ) * β v v := mul_le_mul_of_nonneg_right hm' hvv.le
      have h3 : 2 * ((m : ℤ) * β v v) ≤ (m : ℤ) * ((m : ℤ) * β v v) :=
        mul_le_mul_of_nonneg_right hm' (by linarith)
      have hlt : β v v < β (m • v) (m • v) := by rw [e]; linarith
      obtain ⟨x', h1, h2, h3⟩ := ih (β v v).toNat (by omega) v rfl hv
      exact ⟨x', h1, h2, h3.trans hlt.le⟩
    · exact ⟨x, hx, hd, le_rfl⟩

theorem exists_shortest {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (N : ℕ) (a : X) :
    ∃ v : X, ∀ v0, q (a + N • v) ≤ q (a + N • v + N • v0) := by
  have hfin : {x | ¬ q a < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop (q a))
  obtain ⟨b, ⟨hb, v, rfl⟩, hmin⟩ := Set.exists_min_image ({x | ¬ q a < q x} ∩ Set.range fun v => a + N • v) q
    (hfin.inter_of_left _) ⟨a, lt_irrefl _, 0, by simp⟩
  refine ⟨v, fun v0 => ?_⟩
  by_cases h : q a < q (a + N • v + N • v0)
  · exact (not_lt.1 hb).trans h.le
  · exact hmin _ ⟨h, v + v0, by simp [add_assoc]⟩

theorem pos_of_tendsto {X : Type} [AddCommGroup X] [Module.Free ℤ X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) (ha : a ≠ 0) : 0 < q a := by
  by_contra h
  have h : q a ≤ 0 := not_lt.1 h
  have hfin : {x | ¬ (0 : ℝ) < q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_gt_atTop 0)
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℤ => n • a) (smul_left_injective ℤ ha) (fun n => ?_) hfin
  simp only [Set.mem_setOf_eq, not_lt, QuadraticMap.map_smul, zsmul_eq_mul]
  push_cast
  exact mul_nonpos_of_nonneg_of_nonpos (mul_self_nonneg _) h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem be_pos (T : UTrait Xo c) (x : T.P.D.toPre.X) (hx : x ≠ 0) : 0 < T.be x x := by
  obtain ⟨j, hj⟩ := IsMonomial.exists_pos (IsLocalRing.maximalIdeal.isMaximal T.V).ne_top T.mono hx
  fin_cases j
  simpa using hj

theorem sc_pos {C : UCompact Xo c} {X₁ : USetup C} {p : ℕ} [Fact p.Prime] {z₁ : X₁.M.Z} (t : UCTrait X₁ p z₁) :
    0 < t.sc := by
  have hϖ0 : algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2 t.T.irr.ne_zero
  have h0 : t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ) ≠ 0 := (map_ne_zero _).2 hϖ0
  have hlt : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)‖ < 1 := by
    by_contra hge
    have hinv : ‖t.ι (algebraMap t.T.V (FractionRing t.T.V) t.T.ϖ)⁻¹‖ ≤ 1 := by
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (not_lt.1 hge)
    obtain ⟨w, hw⟩ := (t.int _).1 hinv
    apply t.T.irr.not_isUnit
    refine isUnit_iff_exists_inv.2 ⟨w, IsFractionRing.injective t.T.V (FractionRing t.T.V) ?_⟩
    rw [map_mul, hw, map_one, mul_inv_cancel₀ hϖ0]
  unfold UCTrait.sc
  have := Real.log_neg (norm_pos_iff.2 h0) hlt
  linarith

theorem one_le_of_ne_zero (T : UTrait Xo c) {x : T.P.D.toPre.X} (hx : x ≠ 0) : 1 ≤ Dw.p + Dw.q := by
  haveI : Module.Projective (𝓞 E) T.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) _
  haveI : Module.Finite (𝓞 E) T.P.D.toPre.X := Module.Finite.of_restrictScalars_finite ℤ _ _
  haveI : Nontrivial T.P.D.toPre.X := ⟨x, 0, hx⟩
  have h1 : 0 < Module.finrank (𝓞 E) T.P.D.toPre.X := Module.finrank_pos
  have h2 := UTrait.finrank_le_min E H Dw l Xo c T
  omega

theorem exists_mem_maximalIdeal {C : UCompact Xo c} (X₁ : USetup C) (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z)
    (hz : IsClosed ({z₁} : Set X₁.M.Z)) (t : UCTrait X₁ p z₁) (x : t.T.P.D.toPre.X) (hx : x ≠ 0) :
    ∃ h ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁),
      Real.exp (-(1 / (2 * X₁.S.N) * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  obtain ⟨x', hx', hnd, hle⟩ :=
    exists_not_dvd_le t.T.be (be_pos t.T) X₁.S.N X₁.S.N_ge _ x rfl hx
  obtain ⟨wi⟩ := nonempty_uWit X₁
  obtain ⟨yy, hyy⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw (one_le_of_ne_zero t.T hx) l Xo c C X₁ wi p z₁ t
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', -, -, -, hR, G, _, α, β, -, -, -, y₀, hat, u, lb, j, hq, -⟩ :=
    hyy.uIsLab
  let S' := X₁.S.rechart c₀ hc R' fg frac hth hev
  have hdiv' : X₁.M.HasDiv S'.th := fun z => (X₁.hasDiv z).imp fun k hk => (RatModel.div_mul_iff hc).2 hk
  have htests : S'.HasTests :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hU hL hL2 hUT X₁.o₁ X₁.Ω₁ S' ρ').1
  have hy : ∀ a : X₁.o₁, ‖y₀ (algebraMap X₁.o₁ S'.R a)‖ ≤ 1 := fun a => by
    rw [hat]
    exact RatModel.norm_val_le_one t.cen ((X₁.M.O z₁).algebraMap_mem a)
  obtain ⟨τ, e, hτ, -⟩ := exists_test_match X₁.o₁ X₁.Ω₁ S' ρ' p y₀ u lb
    (GlobalTheory.T.thetaConstant_bounded_by_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u lb hy) (GlobalTheory.T.unitThetaConstants_generate_integralTorsion hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
    (GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hUT _ _ S' ρ' p y₀ u lb hy) (GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
    (GlobalTheory.T.exists_weightZeroSection_unit_integralTorsionPoint hL hL2 hUT _ _ S' ρ' p y₀ u lb hy)
  let α₀ : τ.X := e.symm (j.symm x')
  obtain ⟨v, hv⟩ := exists_shortest τ.q τ.pos X₁.S.N α₀
  have hne : α₀ + X₁.S.N • v ≠ 0 := fun h0 => hnd ⟨-(j (e v)), by
    have h1 := congrArg (fun s => j (e s)) h0
    simp only [α₀, map_add, map_nsmul, AddEquiv.apply_symm_apply, map_zero] at h1
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left h1⟩
  have hqle : τ.q (α₀ + X₁.S.N • v) ≤ t.sc * t.T.be x' x' / 2 := by
    have h1 := hv (-v)
    rw [smul_neg, add_neg_cancel_right] at h1
    refine h1.trans_eq ?_
    rw [hτ, hq]
    simp only [α₀, AddEquiv.apply_symm_apply]
  obtain ⟨h, hm, hh⟩ := GlobalTheory.exists_mem_maximalIdeal_exp_le_norm_val X₁.o₁ X₁.Ω₁ S' X₁.M X₁.normal hdiv' htests z₁ hz p
    t.y y₀ t.cen (fun a ha => hR ha) hat τ _ hv (pos_of_tendsto τ.q τ.pos _ hne)
  refine ⟨h, hm, le_trans (Real.exp_le_exp.2 ?_) hh⟩
  have hsc := sc_pos t
  have hNpos : (0 : ℝ) < X₁.S.N := by
    have := X₁.S.N_ge
    exact_mod_cast (by omega : 0 < X₁.S.N)
  have hb : (t.T.be x' x' : ℝ) ≤ t.T.be x x := by exact_mod_cast hle
  have h1 : τ.q (α₀ + X₁.S.N • v) ≤ t.sc * t.T.be x x / 2 :=
    hqle.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb hsc.le) zero_le_two)
  rw [neg_le_neg_iff]
  refine (div_le_div_of_nonneg_right h1 hNpos.le).trans_eq ?_
  field_simp

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X' : USetup C) (p : ℕ) [Fact p.Prime], ∃ K : ℝ, ∀ (z' : X'.M.Z), IsClosed ({z'} : Set X'.M.Z) → ∀ t : UCTrait X' p z', X'.S.R ≤ X'.M.O ((gPt p ≫ t.y) (IsLocalRing.closedPoint (PadicAlgCl p))) → ∀ x : t.T.P.D.toPre.X, x ≠ 0 → ∃ h ∈ maximalIdeal (X'.M.Z.presheaf.stalk z'), Real.exp (-(K * (t.sc * t.T.be x x))) ≤ ‖t.val h‖ := by
  intro E _ _ _ H Dw l Xo c C X' p _
  exact ⟨1 / (2 * X'.S.N), fun z' hz t _ x hx => exists_mem_maximalIdeal X' p z' hz t x hx⟩

end GlobalTheory.UPoinc.ShortBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLabellingTransportGaloisConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UPoinc.UGalTrans

theorem exists_lift_rat {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [CharZero Ω] {R : Subalgebra o Ω}
    {P : PolAV (Sp R)} {G : Over (Sp (ratHull R))} [GrpObj G] {α : G.left ⟶ P.A.left}
    (hα : IsGrpPullback G P.A (spMap (toRat R)) α) {K : Type} [Field K] [CharZero K] (q : Sp K ⟶ P.A.left) :
    ∃ g : Sp K ⟶ G.left, g ≫ α = q := by
  obtain ⟨x', hx', -⟩ := existsUnique_ratPoint R (q ≫ P.A.hom)
  exact ⟨hα.1.lift q x' hx'.symm, hα.1.lift_fst _ _ _⟩

set_option maxHeartbeats 1600000 in
theorem isLab_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (cf : Coeff l) (C : UCompact Xo cf), ∀ (X₁ : USetup C) (D : UDeep X₁) (σ : D.X.Ω₁ ≃ₐ[X₁.Ω₁] D.X.Ω₁) (s : D.X.M.Z ⟶ D.X.M.Z), D.X.M.pt ≫ s = spMap (σ : D.X.Ω₁ →+* D.X.Ω₁) ≫ D.X.M.pt → ∀ a : D.X.S.Gam ≃+ D.X.S.Gam, D.GalLab σ a → (∀ x, a (D.lab x) = D.lab x) → ∀ (p : ℕ) [Fact p.Prime] (z₁ : X₁.M.Z) (ct : UCTrait X₁ p z₁) (y : Sp (OO p) ⟶ D.X.M.Z) (h : y ≫ D.q = ct.y) (h' : (y ≫ s) ≫ D.q = ct.y) (yy : D.X.S.Gam →+ ModN (D.X.S.r * D.X.S.N) ct.T.P.D.toPre.X), UIsLab D.X (D.lift ct y h) yy → UIsLab D.X (D.lift ct (y ≫ s) h') (yy.comp a.toAddMonoidHom) := by
  intro E _ _ _ H Dw hpq l Xo cf C X₁ D σ s hs a hG _ p _ z₁ ct y h h' yy hy
  haveI : CharZero D.X.Ω₁ := D.X.ar.char
  obtain ⟨c₀, hc, R', fg, frac, hth, hev, ρ', u', hS, -, hu', hR, G, _, α, β, hα, hβ, hL, y₀, hy₀, u, lb, j, hq, hyy,
    hall⟩ := hy
  obtain ⟨wi, W₀, _, e, k₀, he, hk₀, heβ, htw⟩ :=
    GlobalTheory.T.exists_conj_universalTriple_identification E H Dw l Xo cf C X₁ D σ a hG c₀ hc R' fg frac hth hev ρ' u' hS hu' G _ α β hα hβ hL
  obtain ⟨yy₁, hW⟩ := GlobalTheory.T.exists_labels_unitaryClassicalTrait E H Dw hpq l Xo cf C D.X wi p _ (D.lift ct (y ≫ s) h')
  obtain ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', u'', hS₁, hi₁, hu₁, hR₁, G'', _, α'', β'', hα'', hβ'', hL'',
    ⟨m'', hm'', hmβ, hmt⟩, y₁, hy₁, u₁, lb₁, j₁, -, -, -⟩ := hW
  have hk'' : IsGrpPullback W₀ G'' (spMap ((σ : D.X.Ω₁ →+* D.X.Ω₁).comp (ratHull R'').val.toRingHom)) (e ≫ m'') :=
    (he.comp hm'').congr (GalTrans.sp_comp rfl) rfl
  have hββ : k₀ ≫ β = (e ≫ m'') ≫ β'' := by rw [Category.assoc, hmβ, heβ]
  obtain ⟨P₀, ka, ka', hka, hka', lka, lka', htor, hβeq⟩ := GlobalTheory.T.unitaryRechartings_common_geometricFibre E H Dw l Xo cf C D.X (σ : D.X.Ω₁ →+* D.X.Ω₁) s hs p
    (gPt p ≫ y) _ _ ρ' ρ'' hR (by rw [Category.assoc]; exact hR₁) y₀ y₁ hy₀ (by rw [Category.assoc]; exact hy₁) u u₁ u'
    u'' G _ α β G'' _ α'' β'' hα hβ hL hα'' hβ'' hL'' W₀ _ k₀ (e ≫ m'') hk₀ hk'' hββ
  obtain ⟨ee, hqe, hlab, hback⟩ := GalTrans.compare u u₁ lb lb₁ P₀ ka ka' hka hka' lka lka'
  have hrN : 1 ≤ D.X.S.r * D.X.S.N := Nat.mul_pos D.X.S.r_pos (by have := D.X.S.N_ge; omega)
  refine ⟨c₁, hc₁, R'', fg₁, frac₁, hth₁, hev₁, ρ'', u'', hS₁, hi₁, hu₁, hR₁, G'', _, α'', β'', hα'', hβ'', hL'', y₁, hy₁,
    u₁, lb₁, ee.symm.trans j, fun χ => ?_, fun x χ hχ => ?_, fun m A pk' pk₂' x' x₂' w w₂ hm hQ' hQ₂' hw hw₂ hA => ?_⟩
  · rw [← ee.apply_symm_apply χ, hqe, ee.apply_symm_apply]
    exact hq (ee.symm χ)
  · obtain ⟨w, hw1, hw2⟩ := hmt x
    obtain ⟨w₀, hw₀, hw₀e, hw₀k⟩ := htw x w hw1
    have c'' : w₀ ≫ (e ≫ m'') ≫ α'' =
        spMap ((σ : D.X.Ω₁ →+* D.X.Ω₁).comp R''.val.toRingHom) ≫ (ρ''.pt x).left := by
      rw [Category.assoc, reassoc_of% hw₀e, hw2, ← Category.assoc, GalTrans.sp_comp rfl]
    obtain ⟨v, xo, xo', hv, hva, hva', hx, hx'⟩ := htor (a x) x w₀ hw₀ hw₀k c''
    obtain ⟨pk, pk', hQ, hQ', hcm⟩ := hlab _ xo xo' v hrN
      (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ' p y₀ u _ xo hx)
      (GlobalTheory.LabelTorsion.pow_eq_one_of_over_label _ ρ'' p y₁ u₁ _ xo' hx') hv hva hva'
    refine (hyy (a x) pk.y (lb.yy_eq _ pk xo hQ hx)).trans (GalTrans.cm_mk ?_)
    have c2 : CongMod (D.X.S.r * D.X.S.N) χ pk'.y := GalTrans.cm_of_mk (hχ.symm.trans (lb₁.yy_eq x pk' xo' hQ' hx'))
    simpa using GalTrans.cm_symm (GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom (GalTrans.cm_trans c2 hcm))
  · obtain ⟨pk, xo, vo, hQ, -, hvo, hvoa, hvoa', c1⟩ := hback m pk' x' hm hQ'
    obtain ⟨pk₂, xo₂, vo₂, hQ₂, -, hvo₂, hvo₂a, hvo₂a', c2⟩ := hback m pk₂' x₂' hm hQ₂'
    obtain ⟨g, hg⟩ := exists_lift_rat hα (xo.left ≫ u.φ)
    obtain ⟨g₂, hg₂⟩ := exists_lift_rat hα (xo₂.left ≫ u.φ)
    have e1 : g ≫ β = w ≫ β'' := hβeq vo g w hvo (by rw [hg, ← hvoa, Category.assoc])
      (by rw [hw, ← hvoa', Category.assoc])
    have e2 : g₂ ≫ β = w₂ ≫ β'' := hβeq vo₂ g₂ w₂ hvo₂ (by rw [hg₂, ← hvo₂a, Category.assoc])
      (by rw [hw₂, ← hvo₂a', Category.assoc])
    have hA' : g₂ ≫ β = g ≫ β ≫ (Xo.univ.t.act.act A).left := by
      rw [e2, hA, ← Category.assoc, ← e1, Category.assoc]
    have c3 := hall m A pk pk₂ xo xo₂ g g₂ hm hQ hQ₂ hg hg₂ hA'
    have c4 : CongMod m ((ee.symm.trans j) pk₂'.y) (j pk₂.y) := by
      have := GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom c2
      rwa [show (ee.symm.trans j).toAddMonoidHom (ee pk₂.y) = j pk₂.y from
        congrArg j (ee.symm_apply_apply pk₂.y)] at this
    have c5 : CongMod m ((ee.symm.trans j) pk'.y) (j pk.y) := by
      have := GalTrans.cm_map (ee.symm.trans j).toAddMonoidHom c1
      rwa [show (ee.symm.trans j).toAddMonoidHom (ee pk.y) = j pk.y from
        congrArg j (ee.symm_apply_apply pk.y)] at this
    have c6 : CongMod m (A • j pk.y) (A • (ee.symm.trans j) pk'.y) :=
      GalTrans.cm_symm (GalTrans.cm_map (DistribMulAction.toAddMonoidHom _ A) c5)
    exact GalTrans.cm_trans c4 (GalTrans.cm_trans c3 c6)

end GlobalTheory.UPoinc.UGalTrans
end
end

