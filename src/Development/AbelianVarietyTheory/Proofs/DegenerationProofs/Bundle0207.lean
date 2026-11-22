import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0133
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0136
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0146
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0204
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0050
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0138
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0200
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0206
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0197
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0129
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFullTorsionIsometryOfTateIsoQ
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.Relabel

namespace GlobalTheory.Relabel

theorem weilIs_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] [IsCommMonObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left} (hL : L.IsLB) (hL' : L'.IsLB)
    (hp : IsGrpPullback G' G f φ) (hw : LBIso L' (L.pull φ)) (T : Over S') (g : T.left ⟶ S) (hg : g = T.hom ≫ f)
    (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk g ⟶ G) (c : Γ(T.left, ⊤)ˣ) (ex : x₀.left = x.left ≫ φ)
    (ey : y₀.left = y.left ≫ φ) (h : WeilIs G L k x₀ y₀ c) : WeilIs G' L' k x y c := by
  subst hg
  exact (GlobalTheory.weilIs_grpPullback_of_comm' S S' G G' f φ L L' hL hL' hp hw T k x y x₀ y₀ c ex ey).2 h

theorem exists_fullI_of_tateIsoQ : GlobalTheory.UT.LL → AllD fun {E} _ _ _ {H} D => ∀ (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (I' : TateIsoQ D M.P.D.toPre M.P.oD C), ∃ I : FullI o, I.ζ = I'.ζ ∧ ∀ j, 0 < j → ∀ x, ∃ z : TFK (R := M.W) C ⟶ M.P.A.A, z.left = (I.ev j x).left ≫ M.φ ∧ M.P.ToA C j (I'.ev j x) z := by
  intro hLL E _ _ _ H D C _ o M I'
  let := H.starRing
  have : IsAlgClosed C := o.closed
  obtain ⟨hadm, hcz⟩ := M.admissible_base_of_complete_dvr
  have : CharZero M.W := hcz
  have hall := GlobalTheory.TestFibre.laws_all hLL.1 hLL.2.1
  have hT : M.P.TorsionIso := GlobalTheory.T.torsionIso_of_linear_uniformisation_triple hLL hall.2.1 hall.2.2.1 hall.2.2.2.1 hall.2.2.2.2 E H M.W
    (IsLocalRing.maximalIdeal M.W) hadm M.t M.P
  have hTw := GlobalTheory.T.uniformisation_torsion_maps_compatible_in_level hLL M.W (IsLocalRing.maximalIdeal M.W) hadm M.P.D M.P.A M.t.G M.t.semi M.P.U C
  have hT' := fun (k : ℕ) (hk : 1 ≤ k) => hT C k hk
  choose f hfA hfB hfC hfD hfE hfF using hT'
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv M.cart (baseOver (Sp C)) (jFK (R := M.W) C)
    (by simp)

  have gA : ∀ (n : ℕ) (hn : 0 < n) a, M.P.ToA C n (I'.ev n a) (f n hn (I'.ev n a)) := fun n hn a => (hfA n hn _ _).2 rfl
  have gAdd : ∀ (n : ℕ) (hn : 0 < n) a b, f n hn (I'.ev n (a + b)) = f n hn (I'.ev n a) * f n hn (I'.ev n b) :=
    fun n hn a b => hfD n hn _ _ _ (I'.add n hn a b)
  have gLin : ∀ (n : ℕ) (hn : 0 < n) (c : 𝓞 E) a, f n hn (I'.ev n (c • a)) = f n hn (I'.ev n a) ≫ M.P.oA.act c :=
    fun n hn c a => hfE n hn c _ _ (I'.lin n hn c a)
  have gEq : ∀ (n : ℕ) (hn : 0 < n) a b, f n hn (I'.ev n a) = f n hn (I'.ev n b) ↔ ∃ e, a = b + n • e :=
    fun n hn a b => (hfC n hn _ _).trans (I'.ker n hn a b)
  have gZero : ∀ (n : ℕ) (hn : 0 < n), f n hn (I'.ev n 0) = 1 := by
    intro n hn
    have h0 := gAdd n hn 0 0
    rw [add_zero] at h0
    exact mul_left_cancel (h0.symm.trans (_root_.mul_one _).symm)
  have gNsmul : ∀ (n : ℕ) (hn : 0 < n) a (m : ℕ), f n hn (I'.ev n (m • a)) = f n hn (I'.ev n a) ^ m := by
    intro n hn a m
    induction m with
    | zero => rw [zero_smul, gZero, pow_zero]
    | succ m ih => rw [succ_nsmul, gAdd, ih, pow_succ]
  have gPow : ∀ (n : ℕ) (hn : 0 < n) a, f n hn (I'.ev n a) ^ n = 1 := by
    intro n hn a
    rw [← gNsmul, ← gZero n hn]
    exact (gEq n hn _ _).2 ⟨a, by rw [zero_add]⟩
  have gOnto : ∀ (n : ℕ) (hn : 0 < n) x, x ^ n = 1 → ∃ a, f n hn (I'.ev n a) = x := by
    intro n hn x hx
    obtain ⟨p, rfl⟩ := hfB n hn x hx
    obtain ⟨a, ha⟩ := I'.onto n hn p
    exact ⟨a, (hfC n hn _ _).2 ha⟩
  have gTower : ∀ (n m : ℕ) (hn : 0 < n) (hm : 0 < m) a,
      f (n * m) (Nat.mul_pos hn hm) (I'.ev (n * m) a) ^ m = f n hn (I'.ev n a) := by
    intro n m hn hm a
    obtain ⟨q, hqy, hqg, hqe⟩ := I'.tower n m hn hm a
    have h1 := (hTw n m (n * m) hn hm rfl q (I'.ev (n * m) a) (f (n * m) (Nat.mul_pos hn hm) (I'.ev (n * m) a))).2
      hqy hqg (gA (n * m) (Nat.mul_pos hn hm) a)
    rw [(hfA n hn q _).1 h1]
    exact (hfC n hn _ _).2 hqe
  have gWeil : ∀ (n : ℕ) (hn : 0 < n) a b, WeilIs M.P.A.A M.P.A.L n (f n hn (I'.ev n a)) (f n hn (I'.ev n b))
      (unitOn (I'.ζ n ^ D.EF a b)) := fun n hn a b => (hfF n hn _ _ _).1 (I'.isom n hn a b)

  have hL : ∀ y, (e.symm y).left ≫ M.φ = y.left := fun y => by rw [← he, e.apply_symm_apply]
  have hComm : ∀ y (c : 𝓞 E), e.symm (y ≫ M.P.oA.act c) = e.symm y ≫ o.oa.act c := by
    intro y c
    apply e.injective
    rw [e.apply_symm_apply]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, M.act c, ← Category.assoc, hL]
  obtain ⟨ev, hev⟩ : ∃ ev : ℕ → D.La → (baseOver (Sp C) ⟶ o.P.A),
      ∀ n a, ev n a = if hn : 0 < n then e.symm (f n hn (I'.ev n a)) else o.I.ev n a := ⟨_, fun _ _ => rfl⟩
  refine ⟨{ ζ := I'.ζ, ζ_prim := I'.ζ_prim, ζ_pow := I'.ζ_pow, ev := ev, add := ?_, lin := ?_, ker := ?_, onto := ?_, tower := ?_, isom := ?_ }, rfl, ?_⟩
  · intro n a b
    by_cases hn : 0 < n
    · rw [hev, hev, hev, dif_pos hn, dif_pos hn, dif_pos hn, gAdd, map_mul]
    · rw [hev, hev, hev, dif_neg hn, dif_neg hn, dif_neg hn]
      exact o.I.add n a b
  · intro n c a
    by_cases hn : 0 < n
    · rw [hev, hev, dif_pos hn, dif_pos hn, gLin, hComm]
    · rw [hev, hev, dif_neg hn, dif_neg hn]
      exact o.I.lin n c a
  · intro n hn a
    rw [hev, dif_pos hn, map_eq_one_iff _ e.symm.injective, ← gZero n hn, gEq]
    simp only [zero_add]
  · intro n hn x
    constructor
    · intro hx
      obtain ⟨a, ha⟩ := gOnto n hn (e x) (by rw [← map_pow, hx, map_one])
      exact ⟨a, by rw [hev, dif_pos hn, ha, e.symm_apply_apply]⟩
    · rintro ⟨a, rfl⟩
      rw [hev, dif_pos hn, ← map_pow, gPow, map_one]
  · intro n m hn hm a
    rw [hev, hev, dif_pos (Nat.mul_pos hn hm), dif_pos hn, ← map_pow, gTower n m hn hm]
  · intro n hn a b
    rw [hev, hev, dif_pos hn, dif_pos hn]
    exact weilIs_push M.P.A.isLB o.P.isLB M.cart M.lb (baseOver (Sp C)) (jFK (R := M.W) C)
      (by simp) n _ _ _ _ _ (hL _).symm (hL _).symm (gWeil n hn a b)
  · intro j hj x
    refine ⟨f j hj (I'.ev j x), ?_, gA j hj x⟩
    change _ = (ev j x).left ≫ M.φ
    rw [hev, dif_pos hj, hL]

end GlobalTheory.Relabel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormTorsionSumShortestVectorEq
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TestFibre

theorem val_lt_of_shortest {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {n r : ℕ}
    (hn : 1 ≤ n) (hr : 2 ≤ r) (z : D.toPre.X) (hz : ∀ m, Q z ≤ Q (z + n • m)) (m : D.toPre.X)
    (hm : (n * r) • m ≠ 0) : Q z < Q (z + (n * r) • m) := by
  let B : D.toPre.X →+ D.toPre.X →+ ℤ := AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => QForm.bOf D.toPre Q a b)
    (fun b b' => by
      rw [QForm.bOf_comm D (Q := Q) a, QForm.bOf_add_left hϖ D hQ, QForm.bOf_comm D (Q := Q) b,
        QForm.bOf_comm D (Q := Q) b']))
    (fun a a' => AddMonoidHom.ext fun b => QForm.bOf_add_left hϖ D hQ a a' b)
  refine shortest_vector_strict_of_mul _ Q B (fun a b => ?_) (fun a => ?_) (fun a ha => QForm.Q_pos hϖ D hQ ha)
    n r hn hr z hz m hm
  · show _ = Q a + Q b + QForm.bOf D.toPre Q a b
    rw [QForm.bOf]; ring
  · show _ = QForm.bOf D.toPre Q a a
    have h := QForm.bOf_add_left hϖ D hQ a (-a) a
    simp only [QForm.bOf, add_neg_cancel, neg_add_cancel, zero_add, QForm.Q_neg hϖ D hQ, QForm.Q_zero hϖ D hQ] at h ⊢
    linarith

theorem exists_origin (hLL : LL) (hT : TwistBCSpanStatement) (hVR : TWM.VRatioGtStatement) (hTW : TWStatement)
    (hUU : UUStatement) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (hadm : AdmBase V (IsLocalRing.maximalIdeal V))
    {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) (k : ℕ) : ∃ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b), g.IsZero ∧ FrmOne w ∧
      GtV hϖ hv g (fun _ => 0) ∧ GenV hϖ hv w 0 := by
  obtain ⟨-, -, h₁, -, h₂⟩ := gt_onto_divisible_kernel hLL V _ hadm D F
  obtain ⟨g, hg, -⟩ := h₁ 1
  obtain ⟨w, hw⟩ := (CoefBasic.coef_basic V D.toPre F k g).2.1 hg.1
  obtain ⟨⟨l, hl, hu⟩, -, h₃, h₄, -⟩ := CoefVal.main hLL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv g
  have hadd : g.IsAdd g g := (h₂ 1 1 g g g hg hg).2 (by rwa [_root_.mul_one])
  have e : l + l = l := hu (l + l) (h₄ g g l l hadd hl hl)
  have e₀ : l = 0 := by simpa using e
  refine ⟨g, w, (isZero_iff g).2 ⟨hg.1, fun χ y J hJ => Units.ext ?_⟩, hw, ?_, h₃ k w hw hg.1⟩
  · refine (hg.2 χ y J hJ).trans ?_
    rw [CoefBasic.cst_eq]
    exact map_one _
  · rw [e₀] at hl
    exact hl

set_option maxHeartbeats 1000000 in

theorem exists_norm_FF_eq : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∃ (k : _) (hk : S.FF _ (l.wt α) k ∈ S.R), ‖y₀ ⟨S.FF _ (l.wt α) k, hk⟩‖ = S.delta y₀ * Real.exp (-(l.q α / S.N))) := by
  intro hL hL2 hU o Ω _ _ _ _ S ρ p _ y₀ u l hint α hα
  obtain ⟨hLL, hT, hVR, hTW, hUU⟩ := laws_all hL hL2
  obtain ⟨hch, -, hadm, hN', hζ, ϖ, Q, v, lam, hϖ, hv, hnorm⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hint
  obtain ⟨⟨x, hx⟩, -⟩ := GlobalTheory.T.uniformisedModel_torsionPoints_group_pairing hL o Ω S ρ p y₀ u
  obtain ⟨rig, e, th, s, hs⟩ := GlobalTheory.T.exists_thetaSystem_test_sections_on_geometric_fibre hL o Ω S ρ p y₀ u x hx
  have hle : S.perp l.yy.ker ≤ l.yy.ker :=
    l.isoFree.1.trans ((thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1 _).le
  refine GlobalTheory.T.thetaSystem_exists_rootOfUnity_sum_norm_attained o Ω S p y₀ hint _ (l.wt α) _
    (fun t i => GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hU o Ω S ρ p y₀ u l hint α hα t (hle t.2) i) ?_
  obtain ⟨w₀, hw₀⟩ := (EvalZero.value_at_origin hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p)).2.1 rig hs.1
  obtain ⟨th', ϑ, hϑ, hprim, hgen⟩ := exists_prim_generator hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hnorm.2.1
    (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ hw₀.1
  obtain ⟨c₀, hc₀⟩ := hgen th
  obtain ⟨c, rfl⟩ : ∃ c : PadicAlgCl p, cF u.V c = c₀ :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).hom.hom c₀,
      (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).hom_inv_id_apply c₀⟩
  have hδ : S.delta y₀ ≤ ‖c‖ := ciSup_le
    (GlobalTheory.T.norm_thetaConstant_le_primitiveGenerator_scale hL hL2 hU o Ω S ρ p y₀ u l hint x rig e th s hx hs ϖ Q v lam hϖ hv hnorm w₀ th' ϑ c hw₀ hϑ hprim hc₀)
  by_cases hc : c = 0
  · rw [hc, norm_zero] at hδ
    exact ⟨0, ρ.i₀, (mul_nonpos_of_nonpos_of_nonneg hδ (Real.exp_pos _).le).trans (norm_nonneg _)⟩
  obtain ⟨hlam, hQ, hq, hge, heq⟩ := id hnorm
  have hN0 : 1 ≤ S.N := le_trans (by norm_num) S.N_ge
  have hrN : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos hN0
  have hN4 : 4 ≤ S.N := by
    have : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]; nlinarith
  have hr2 : 2 ≤ S.r := by
    obtain ⟨j, hj, hr⟩ := ρ.r_eq
    rw [hr]
    exact ρ.n_prime.two_le.trans (Nat.le_self_pow (by omega) _)
  haveI : NeZero (S.r * S.N) := ⟨by omega⟩
  haveI : Fintype (S.perp l.yy.ker) := Fintype.ofFinite _
  obtain ⟨g, w₁, hg, hw₁, hgv, hwv⟩ := exists_origin hLL hT hVR hTW hUU u.complete hadm hϖ u.D hQ hv S.N
  obtain ⟨Φ, hΦ, hsupp, hval⟩ := CoefUnit.exists_fam_coef_val hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv S.N hN4 g w₁ _ 0 hw₁.1 hgv hwv α
  obtain ⟨b, σ, hb, hσ, hσΦ⟩ := GlobalTheory.T.exists_integral_basis_combination_of_integral_family hL hL2 hU o Ω S ρ p y₀ u l hint x rig e th s hx hs ϖ Q v lam hϖ hv hnorm
    w₀ th' ϑ c hw₀ hϑ hprim hc₀ hc Φ hΦ
  choose τ q hqy hτ hqx hτv using GlobalTheory.T.thetaSystem_orthogonal_labels_are_torus_points hL hL2 hU o Ω S ρ p y₀ u l hint x hx
  have key : ∀ t : S.perp l.yy.ker, ∃ ζ : PadicAlgCl p, v ζ = 0 ∧
      SumV v (fun β => (τ t (Multiplicative.ofAdd β)).val * coef Φ g w₁ β)
        (ζ * ∑ j, b j * y₀ ⟨S.ev t j, S.ev_mem t j⟩) := fun t => by
    obtain ⟨ζ, hζ, H⟩ := WeightValue.value_at_formal_torsion hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
      (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ rig hw₀ (S.r * S.N) S.N hrN hN0 (q t) (x t) (hqy t) (hqx t) (e t)
      (hs.2.1 t)
    exact ⟨ζ, hζ, (H σ Φ _ hσΦ ((GlobalTheory.T.isFibreSectionValueInFrame_linear_unique_exists hL u.V u.A (PadicAlgCl p) S.N (x t) (e t)).1 S.J s b _ σ hσ
      fun i => hs.2.2.2.1 i t)).2 _ (hτ t) g w₁ hg hw₁⟩
  choose ζ hζv hsum using key
  have v1 : ∀ z : PadicAlgCl p, ‖z‖ = 1 → v z = 0 := fun z hz => (heq z 0).2 (by simpa using hz)
  have hζ1 : ‖y₀ (algebraMap o S.R S.ζ)‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero 2 (NeZero.ne (S.r * S.N)))).1
      (by rw [← norm_pow, hζ.pow_eq_one, norm_one])
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_val_le_of_valuedSum_against_characters (PadicAlgCl p) v u.D.toPre.X (S.perp l.yy.ker)
    (fun t β => (τ t (Multiplicative.ofAdd β)).val) (coef Φ g w₁) ζ _ α ((Q α : ℚ) / S.N) hsum hζv
    (fun t β => by
      obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk β)
      exact v1 _ (by rw [hτv t a β ha, norm_pow, hζ1, one_pow]))
    (by
      obtain ⟨d, ⟨E⟩⟩ := l.isoFree.2
      refine v1 _ ?_
      rw [Fintype.card_congr E.toEquiv, Fintype.card_fun, ZMod.card, Nat.cast_pow, norm_pow, hN', one_pow])
    (by simpa using hval)
    (fun β hβ => by
      obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (β - α))
      by_cases hk : a ∈ l.yy.ker
      · right
        rw [AddMonoidHom.mem_ker, ha, QuotientAddGroup.eq_zero_iff] at hk
        obtain ⟨m, hm⟩ := hk
        have hm' : (S.N * S.r) • m = β - α := by rw [Nat.mul_comm]; exact hm
        have hlt := val_lt_of_shortest hϖ u.D hQ hN0 hr2 α (fun m => by
          have := hα m
          rw [hq, hq] at this
          exact_mod_cast le_of_mul_le_mul_left this hlam) m (by rw [hm']; exact sub_ne_zero.2 hβ)
        rw [hm', add_sub_cancel] at hlt
        refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_)
          ((((CoefVal.main hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv g).2.2.2.2.2.2
            S.N hN0 w₁ Φ hw₁.1).2 _ 0 0 hgv hwv hΦ β))
        have : (0 : ℚ) < S.N := by exact_mod_cast hN0
        simp only [zero_add, add_zero]
        exact div_lt_div_of_pos_right (by exact_mod_cast hlt) this
      · left
        refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_) (GlobalTheory.T.thetaSystem_sum_character_orthogonal_eq_zero o Ω S _ _ hζ l.yy.ker a hk)
        rw [← hτv t a _ ha, ofAdd_sub, map_div, Units.val_div_eq_div_val, div_eq_inv_mul])
  rw [← GlobalTheory.T.thetaSystem_weightProjector_fixes_eigenvector o Ω S (PadicAlgCl p) (y₀.comp (algebraMap o S.R)) _ (l.wt α) l.isoFree b _
    (fun t' => GlobalTheory.T.torusOperator_eigen_of_expansion_single_class hL hL2 hU o Ω S ρ p y₀ u l hint x rig e th s hx hs w₀ hw₀.1 α b σ Φ hσ hσΦ hsupp t' t)] at ht
  have hE : Real.exp (-(l.q α / S.N)) = Real.exp (-(lam * (((Q α : ℚ) / S.N : ℚ) : ℝ))) := by
    rw [hq]; push_cast; ring_nf
  obtain ⟨i, -, hi⟩ := IsUltrametricDist.exists_norm_finset_sum_le_of_nonempty Finset.univ_nonempty
    (fun i => b i * ∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt α) j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩)
  refine ⟨t, i, ?_⟩
  have hw : Real.exp (-(l.q α / S.N)) ≤
      ‖∑ i, b i * ∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt α) j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ := by
    rw [hE]
    by_contra hlt
    have hlt := not_le.1 hlt
    exact hlt.ne ((heq _ _).1 (le_antisymm ht ((hge _ _).2 hlt.le)))
  have hbi := hb i
  rw [norm_mul] at hi hbi
  calc _ ≤ ‖c‖ * (‖b i‖ * _) := mul_le_mul hδ (hw.trans hi) (Real.exp_pos _).le (norm_nonneg _)
    _ = (‖c‖ * ‖b i‖) * _ := (_root_.mul_assoc _ _ _).symm
    _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hbi (norm_nonneg _)
    _ = _ := _root_.one_mul _

end GlobalTheory.TestFibre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsTorsionIsometryUniformisedModelStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex
open GlobalTheory.ModelData
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_torsion_isometry_uniformised_model : GlobalTheory.UT.LL → BrGtSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (C : Type) [NormedField C] (o : Full D C) (M : Mdl o) (N' : NumD C) (_ : NumOf M.P.D.toPre C N'), ∃ I : TateIsoQ D M.P.D.toPre M.P.oD C, I.ζ = o.I.ζ ∧ ∀ k, 0 < k → ∀ x p' (z : TFK (R := M.W) C ⟶ M.P.A.A), QkPt.Equiv _ C (I.ev k x) p' → z.left = (o.I.ev k x).left ≫ M.φ → M.P.ToA C k p' z := by
  first | exact @GlobalTheory.ModelData.ModelTate.exists_tateIsoQ_of_model | exact GlobalTheory.ModelData.ModelTate.exists_tateIsoQ_of_model | (intros; apply GlobalTheory.ModelData.ModelTate.exists_tateIsoQ_of_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PrincipallyPolarizedAbelianVarietyPotentialSemiA
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.SemiPol

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

theorem exists_prime_unit (V : Type) [CommRing V] [IsLocalRing V] :
    ∃ l : ℕ, l.Prime ∧ 3 ≤ l ∧ IsUnit (l : V) := by
  have h : IsUnit ((2 : V) * ((3 : ℕ) : V) + -((5 : ℕ) : V)) := by
    have : (2 : V) * ((3 : ℕ) : V) + -((5 : ℕ) : V) = 1 := by push_cast; ring
    rw [this]; exact isUnit_one
  rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add h with h | h
  · exact ⟨3, Nat.prime_three, le_rfl, isUnit_of_mul_isUnit_right h⟩
  · exact ⟨5, Nat.prime_five, by norm_num, by simpa using h⟩

theorem exists_pullback {S S' : Scheme.{0}} (f : S' ⟶ S) (P : Out.PolAV S) :
    ∃ (P' : Out.PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ := by
  obtain ⟨P', φ, hφ, -, mul, -⟩ :=
    polBaseChange_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S S' f P
  refine ⟨P', φ, hφ, fun T x y x₀ y₀ hx hy => ?_⟩
  have e₁ : x₀ = Out.toBase hφ.w x := Over.OverMorphism.ext hx
  have e₂ : y₀ = Out.toBase hφ.w y := Over.OverMorphism.ext hy
  rw [e₁, e₂, ← mul]
  rfl

theorem fixed_of_rational {K K₁ Ω Ω₁ : Type} [Field K] [Field K₁] [Field Ω] [Field Ω₁] [Algebra K K₁] [Algebra K Ω]
    [Algebra K₁ Ω] [IsScalarTower K K₁ Ω] [Algebra K₁ Ω₁] (j : Ω ≃ₐ[K₁] Ω₁)
    {A : Over (Sp K)} [GrpObj A] {A₁ : Over (Sp K₁)} [GrpObj A₁] {φ : A₁.left ⟶ A.left}
    (h : IsGrpPullback A₁ A (spMap (algebraMap K K₁)) φ) (l : ℕ)
    (hr : ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ A, x ^ l = 1 →
      ∃ y : Sp K₁ ⟶ A.left, spMap (algebraMap K₁ Ω) ≫ y = x.left)
    (τ : Ω₁ ≃ₐ[K₁] Ω₁) (x : Over.mk (spMap (algebraMap K₁ Ω₁)) ⟶ A₁) (hx : x ^ l = 1) :
    spMap τ.toRingEquiv.toRingHom ≫ x.left = x.left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback h (spMap (algebraMap K₁ Ω₁))
    (spMap (algebraMap K₁ Ω₁) ≫ spMap (algebraMap K K₁)) rfl
  let u : Over.mk (spMap (algebraMap K Ω)) ⟶ Over.mk (spMap (algebraMap K₁ Ω₁) ≫ spMap (algebraMap K K₁)) :=
    Over.homMk (spMap j.symm.toRingEquiv.toRingHom) (by
      show spMap _ ≫ spMap _ ≫ spMap _ = spMap _
      rw [sp_comp, sp_comp]
      congr 1
      ext c
      simp [← IsScalarTower.algebraMap_apply])
  obtain ⟨y, hy⟩ := hr (u ≫ e x) (by rw [← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one])
  have hy' : spMap (algebraMap K₁ Ω) ≫ y = spMap j.symm.toRingEquiv.toRingHom ≫ x.left ≫ φ := by
    rw [hy, ← he]; rfl
  have h₁ : spMap (algebraMap K₁ Ω₁) ≫ y = x.left ≫ φ := by
    have e₁ : spMap j.toRingEquiv.toRingHom ≫ spMap (algebraMap K₁ Ω) = spMap (algebraMap K₁ Ω₁) := by
      rw [sp_comp]; congr 1; ext c; simp
    have e₂ : spMap j.toRingEquiv.toRingHom ≫ spMap j.symm.toRingEquiv.toRingHom = 𝟙 _ := by
      rw [sp_comp, ← Spec.map_id]; congr 1; ext c; simp
    refine (congrArg (· ≫ y) e₁.symm).trans ((Category.assoc _ _ _).trans ?_)
    rw [hy', ← Category.assoc, e₂]
    exact Category.id_comp _
  have hτ : spMap τ.toRingEquiv.toRingHom ≫ spMap (algebraMap K₁ Ω₁) = spMap (algebraMap K₁ Ω₁) := by
    rw [sp_comp]; congr 1; ext c; simp
  refine h.1.hom_ext ?_ ?_
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) h₁.symm).trans ?_
    rw [← Category.assoc, hτ, h₁]
  · refine (Category.assoc _ _ _).trans ?_
    refine (congrArg (_ ≫ ·) (Over.w x)).trans ?_
    exact hτ.trans (Over.w x).symm

theorem exists_finset (K : Type) [Field K] [CharZero K] (P : Out.PolAV (Sp K)) (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (l : ℕ) (hl : l.Prime) :
    ∃ s : Finset Ω, ∀ (K₁ : Type) [Field K₁] [Algebra K K₁] [Algebra K₁ Ω] [IsScalarTower K K₁ Ω],
      (∀ c ∈ s, c ∈ (algebraMap K₁ Ω).fieldRange) →
      ∀ x : Over.mk (spMap (algebraMap K Ω)) ⟶ P.A, x ^ l = 1 →
        ∃ y : Sp K₁ ⟶ P.A.left, spMap (algebraMap K₁ Ω) ≫ y = x.left := by
  classical
  have hc := (GlobalTheory.T.torsion_points_polarised_abelianVariety_galois K P Ω l hl).1 1
  rw [pow_one] at hc
  have hfin : Finite {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1} :=
    Nat.finite_of_card_ne_zero (by rw [hc]; exact pow_ne_zero _ hl.ne_zero)
  have hsm := P.smoothDim
  have hsm' : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  have hft : LocallyOfFiniteType P.A.hom := inferInstance
  have key : ∀ x : {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1}, ∃ s : Finset Ω,
      ∀ (K₁ : Type) [Field K₁] [Algebra K K₁] [Algebra K₁ Ω] [IsScalarTower K K₁ Ω],
      (∀ c ∈ s, c ∈ (algebraMap K₁ Ω).fieldRange) →
        ∃ y : Sp K₁ ⟶ P.A.left, spMap (algebraMap K₁ Ω) ≫ y = x.1.left := by
    intro x
    obtain ⟨E, -, h₂, h₃⟩ := GlobalTheory.SS.exists_fieldOfValues P.A.left Ω x.1.left
    obtain ⟨L, hL, rfl⟩ := h₃ K P.A.hom hft (Over.w x.1) inferInstance
    obtain ⟨s, hs⟩ : (Subalgebra.toSubmodule L.toSubalgebra).FG :=
      (Submodule.fg_iff_finiteDimensional _).2 hL
    refine ⟨s, fun K₁ _ _ _ _ hK => (h₂ K₁ _).1 fun c hc => ?_⟩
    have : Subalgebra.toSubmodule L.toSubalgebra ≤
        Subalgebra.toSubmodule (IsScalarTower.toAlgHom K K₁ Ω).range := by
      rw [← hs, Submodule.span_le]
      exact fun d hd => hK d hd
    exact this hc
  choose s hs using key
  have := Fintype.ofFinite {x : (Over.mk (spMap (algebraMap K Ω)) ⟶ P.A) // x ^ l = 1}
  exact ⟨Finset.univ.biUnion s, fun K₁ _ _ _ _ hK x hx => hs ⟨x, hx⟩ K₁ fun c hc =>
    hK c (Finset.mem_biUnion.2 ⟨_, Finset.mem_univ _, hc⟩)⟩

theorem potModel_semiAbelian : ∀ (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (IsLocalRing.maximalIdeal V) V] [Field K] [CharZero K] [Algebra V K] [IsFractionRing V K], Finite (IsLocalRing.ResidueField V) → ∀ P : Out.PolAV (Sp K), PotModel V K P.A (fun _ _ _ G _ => IsSemiAbelian G) := by
  intro V K _ _ _ _ _ _ _ _ hres P
  obtain ⟨l, hl, h3, hu⟩ := exists_prime_unit V
  let Ω := AlgebraicClosure K
  obtain ⟨s, hs⟩ := exists_finset K P Ω l hl
  have hV : CharZero V := (algebraMap V K).charZero
  have hinj : Function.Injective (algebraMap V Ω) := by
    rw [IsScalarTower.algebraMap_eq V K Ω]
    exact (algebraMap K Ω).injective.comp (IsFractionRing.injective V K)
  have hf : FaithfulSMul V Ω := (faithfulSMul_iff_algebraMap_injective V Ω).2 hinj
  have ha : Algebra.IsAlgebraic V Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := K) (C := Ω)).2 inferInstance
  obtain ⟨W, hW, hWc, -, hWf, -, hWl, hWs, -⟩ := exists_complete_dvr_finite_subalgebra V Ω s
  let K₁ := FractionRing W
  have hinj₁ : Function.Injective ((algebraMap W K₁).comp (algebraMap V W)) :=
    (IsFractionRing.injective W K₁).comp fun a b h => hinj (congrArg Subtype.val h)
  let _ : Algebra K K₁ := (IsFractionRing.lift hinj₁ : K →+* K₁).toAlgebra
  let _ : Algebra K₁ Ω := (IsFractionRing.lift (g := algebraMap W Ω) Subtype.val_injective : K₁ →+* Ω).toAlgebra
  have c₁ : ∀ a, algebraMap K K₁ (algebraMap V K a) = algebraMap W K₁ (algebraMap V W a) := fun a =>
    IsFractionRing.lift_algebraMap hinj₁ a
  have c₂ : ∀ a : W, algebraMap K₁ Ω (algebraMap W K₁ a) = a := fun a =>
    IsFractionRing.lift_algebraMap (g := algebraMap W Ω) Subtype.val_injective a
  have hT : IsScalarTower K K₁ Ω := IsScalarTower.of_algebraMap_eq' (by
    refine IsLocalization.ringHom_ext (nonZeroDivisors V) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply]
    rw [c₁, c₂, ← IsScalarTower.algebraMap_apply]
    rfl)
  have hK₁ : CharZero K₁ := charZero_of_injective_algebraMap (algebraMap K K₁).injective
  have hal : Algebra.IsAlgebraic K₁ Ω := Algebra.IsAlgebraic.tower_top (K := K) K₁
  have hac : IsAlgClosure K₁ Ω := ⟨inferInstance, hal⟩
  have hres₁ : Finite (IsLocalRing.ResidueField W) :=
    Module.finite_of_finite (IsLocalRing.ResidueField V)
  obtain ⟨P₁, φ, hφ⟩ := exists_pullback (spMap (algebraMap K K₁)) P
  refine GlobalTheory.SS.potModel_trans V K W K₁ (RingHom.ext fun a => (c₁ a).symm) hWf hWl P.A P₁.A φ hφ _ ?_
  refine GlobalTheory.T.potentialSemistable_of_rational_lTorsion W K₁ hres₁ l hl h3 (by simpa using hu.map (algebraMap V W)) P₁ ?_
  refine fixed_of_rational (IsAlgClosure.equiv K₁ Ω (AlgebraicClosure K₁)) hφ l (hs K₁ fun c hc => ?_)
  obtain ⟨a, ha, b, hb, hb0, h⟩ := hWs c hc
  refine ⟨algebraMap W K₁ ⟨a, ha⟩ / algebraMap W K₁ ⟨b, hb⟩, ?_⟩
  rw [map_div₀, c₂, c₂]
  exact (div_eq_iff hb0).2 h.symm

end GlobalTheory.SemiPol
end

