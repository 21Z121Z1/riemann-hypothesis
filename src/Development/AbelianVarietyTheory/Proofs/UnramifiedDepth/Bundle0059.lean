import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.Bundle0026
import ReciprocityTheory.DualLattices.Bundle0015
import ReciprocityTheory.DualLattices.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.Bundle0021
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0049
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0058
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCharacterPairSer
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CoeffActAdd
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0043
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlace
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0050
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueExtensionOfForallNormLeOne
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GoodCurvesPairingMemMaxIdeal
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlace
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartCokernelLengthLe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem place_mul_bar {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] [StarRing OE] (w : Place p OE)
    (hinv : ∀ x, sig p OE (sig p OE x) = x) : w.e * w.bar = 0 := by
  have hb : w.bar * w.bar = w.bar := by
    unfold Place.bar
    rw [← map_mul, w.idem]
  rcases w.prim (w.e * w.bar) (by rw [_root_.mul_mul_mul_comm, w.idem, hb])
    (by rw [mul_right_comm, w.idem]) with h | h
  · exact h
  · exfalso
    apply w.split
    have h2 := congrArg (sig p OE) h
    unfold Place.bar at h h2
    rw [map_mul, hinv, mul_comm, h] at h2
    exact h2.symm

theorem abelian_coker_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp), H.P = 0 → H.PL = 0 → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (rm : ℕ), (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ cw : NNReal, HasLen v O (htCoker H w.e w.bar) cw ∧ (v (algebraMap O C (p : O)) : ℝ) ^ (((w.n : ℝ) * rm) / ((p : ℝ) - 1)) ≤ cw := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H hP hPL w t rm hrm
  obtain ⟨-, -, hstar⟩ := GlobalTheory.ChF.embeddings_idempotents_conjugation p C v O hv OE
  have hsig : ∀ x, sig p OE x = sigE p OE x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => rw [map_add, map_add, ha, hb]
  have hinv : ∀ x, sig p OE (sig p OE x) = x := fun x => by rw [hsig, hsig, hS.invol]
  have h0 : w.e * w.bar = 0 := place_mul_bar w hinv
  have he := w.idem
  have hbar : sigE p OE w.e = w.bar := (hsig _).symm
  have hbar' : sigE p OE w.bar = w.e := by rw [← hbar, hS.invol]
  have hb : w.bar * w.bar = w.bar := by rw [← hbar, ← map_mul, w.idem]
  let c : OE →+* OE := ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom
  have hcc : ∀ τ : OE →+* O, (τ.comp c).comp c = τ := fun τ => by
    ext a
    simp [c]
  let s : Emb (O := O) w.e ≃ Emb (O := O) w.bar :=
    { toFun := fun τ => ⟨τ.1.comp c, by
        have := τ.2
        simp only [Emb, Set.mem_setOf_eq] at this ⊢
        rw [(hstar τ.1 w.bar).1, hbar', this]⟩
      invFun := fun τ => ⟨τ.1.comp c, by
        have := τ.2
        simp only [Emb, Set.mem_setOf_eq] at this ⊢
        rw [(hstar τ.1 w.e).1, hbar, this]⟩
      left_inv := fun τ => Subtype.ext (hcc τ.1)
      right_inv := fun τ => Subtype.ext (hcc τ.1) }
  have hd := GlobalTheory.T.range_idempotent_rank_sum_eigenspaceDim p C v O hv OE g H.ρL w.bar hb w.n (t.trans s)
  obtain ⟨cw, hcw⟩ : ∃ x, HasLen v O (htCoker H w.e w.bar) x :=
    lenEx C v O hv g H.Ht (H.ρL w.e) ((H.ρ w.bar).map (algebraMap ℤ_[p] O))
  refine ⟨cw, hcw, ?_⟩
  have hav := lengthDegree_abelianVariety p g C v O _ _ cp hS H 3 ![w.e, w.bar, 1 - w.e - w.bar] (Equiv.swap 0 1)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp <;>
        first
        | exact he
        | exact hb
        | linear_combination h0
        | linear_combination -he - h0
        | linear_combination -hb - h0
        | linear_combination he + hb + 2 * h0)
    (by
      intro i
      fin_cases i
      · simpa using hbar
      · simpa using hbar'
      · have : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
        simp only [Fin.reduceFinMk, this, Matrix.cons_val, map_sub, map_one, hbar, hbar']
        ring)
    (by simp [Fin.sum_univ_three, hP]) (by simp [hP])
    (by simp [Fin.sum_univ_three, hPL]) (by simp [hPL])
    0 (by decide) _ hd cw hcw
  refine le_trans ?_ hav
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine Real.rpow_le_rpow_of_exponent_ge ?_ ?_ ?_
  · exact_mod_cast pos_iff_ne_zero.2 hS.p_ne
  · exact_mod_cast hS.p_lt.le
  · refine div_le_div_of_nonneg_right ?_ (by linarith)
    have := Finset.sum_le_card_nsmul Finset.univ _ rm (fun j _ => hrm _ ((t.trans s) j).2)
    simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact_mod_cast this

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CharacterOnTorsionPointsEqSeriesStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_series_eq_character_on_torsion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (k : ℕ) (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Killed F.F (p ^ k) φ → Killed F.F (p ^ k) φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, ∀ φ, Killed F.F (p ^ k) φ → algebraMap O C (φ u) = κ φ := by
  first | exact @GlobalTheory.character_on_torsion_points_eq_series | exact GlobalTheory.character_on_torsion_points_eq_series | (intros; apply GlobalTheory.character_on_torsion_points_eq_series <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCharacterPairSerStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_pairSer_alt : ∀ (R₀ : Type) [CommRing R₀] (B : BX R₀) (O : LAlg R₀) (g : ℕ) (F : FGLaw (O : Type) g) (Y : ∀ R : LAlg R₀, LHom O R → (Fin g → (R : Type)) → B.G R), BXChart B O F.F Y → ∀ (p : ℕ), ¬ IsUnit (p : (O : Type)) → IsAdicComplete (Ideal.span {(p : (O : Type))}) (O : Type) → ∀ τ : ℕ → B.G O, (∀ n, (p ^ (n + 1)) • τ n = 0) → (∀ n, τ n = p • τ (n + 1)) → ∃ u : PS (O : Type) 1 g, IsCh F.F u ∧ PairSer B O Y p τ u := by
  first | exact @GlobalTheory.ChF.exists_character_pairSer | exact GlobalTheory.ChF.exists_character_pairSer | (intros; apply GlobalTheory.ChF.exists_character_pairSer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEndomorphismPairW0
section
noncomputable section

open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw GlobalTheory.RowVal ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.GermDerivativeLinearMaps GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.ActionLimit GlobalTheory.ActionEnd

namespace GlobalTheory.ActionEndSelf

section Chart

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)
variable {d : ℕ} {I : Fin 2 → Type} (X : RawChart C d I (Fin dd))
  (hlg : X.lg = fun i => un1 (Y.lg i)) (hex : X.ex = fun i => un1 (Y.ex i)) (hh : X.h = Y.h)

include hlg hex hh in

theorem isEnd_act_raw (a : O) : IsEnd X V (dLin (Y.B.A.act a)) (dLin (Y.B.A.act (star a))) := by
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  refine isEnd_of_hom_raw Y X hlg hex hh _ _ (g _) (g _) (Y.B.A.hom _) (Y.B.A.hom _) (Y.intAct _) (Y.intAct _) ?_
  have h := Y.gauge.ad a
  rw [actK_self, actK_self] at h
  rw [← h]
  have e : FB.toK C (Y.B.ad a) = Y.B.ad a := by
    show MvPowerSeries.map (RingHom.id C) _ = _
    rw [MvPowerSeries.map_id]; rfl
  rw [e]
  exact Y.intAd a

include hlg hex hh in

theorem gauge_at_linearPart_action_eq_hermitianLift (a : O) : un1 (Y.B.hL C Y.h a) =
    hAt X (endP X 1 (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C))
      (endP X (dLin (Y.B.A.act a)) (MvPowerSeries.X : Fin dd → MvPowerSeries (Fin dd) C)) := by
  have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
    fun i => by simp
  have g : ∀ b, GP (Y.B.A.act b) := fun b i => Y.B.A.const b i
  have p0 : GP (pt C (n := 2) dd 0) := gp_pt 0
  have p1 : GP (pt C (n := 2) dd 1) := gp_pt 1
  have q0 : GP (pt C (n := 1) dd 0) := gp_pt 0
  have hs : MvPowerSeries.HasSubst
      (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hX q.2
  have e1 := matrixEnd_eq_subst' Y X hlg hex (pt C dd 0) q0 (by
    rw [germ_comp1_zero_point_left _ (gp_addOf _ Y.B.G.const _ _ p0 p1), germ_comp1_zero_point_left _ p0, germ_comp1_zero_point_left _ p1]) _ hX
  rw [germLinearPart_coordinatePoint_zero] at e1
  have e2 := matrixEnd_eq_subst' Y X hlg hex _ (g a) (Y.B.A.hom a) _ hX
  have e3 : comp1 (Y.B.A.act a) (pt C dd (0 : Fin 1)) = Y.B.A.act a := by
    funext i
    rw [germComp1_eq_subst]
    have : (fun q : Fin 1 × Fin dd => pt C dd (0 : Fin 1) q.2) = MvPowerSeries.X := by
      funext ⟨s, x⟩
      obtain rfl : s = 0 := Subsingleton.elim _ _
      rfl
    rw [this, MvPowerSeries.subst_self]; rfl
  have e4 : un1 (Y.B.hL C Y.h a) = MvPowerSeries.subst
      (fun q : Fin 1 × Fin dd => (MvPowerSeries.X q.2 : MvPowerSeries (Fin dd) C)) (Y.B.hL C Y.h a) := by
    rw [← subst_singlePointUncurry _ hX, MvPowerSeries.subst_self]; rfl
  rw [e4, FB.hL, actK_self, e3, ev, MvPowerSeries.subst_comp_subst_apply
    (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 2 × Fin dd => pair_points_zero_constant q0 (g a) q.1 q.2) hs,
    hAt, hh]
  show MvPowerSeries.subst _ Y.h = MvPowerSeries.subst _ Y.h
  congr 1
  funext ⟨s, x⟩
  fin_cases s
  · exact (e1 x).symm
  · exact (e2 x).symm

theorem linear_parts_w0_sum_one : dLin (Y.B.A.act Y.w0) + dLin (Y.B.A.act (star Y.w0)) = 1 := by
  rw [← germLinearPart_coordinatePoint_zero, ← Y.B.A.one_act, ← Y.halfIntegralGenerator_add_conj_eq_one]
  ext i j
  exact (Nab.coeff_act_add Y.B _ _ i j).symm

end Chart

theorem exists_endomorphism_w0 : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), ∃ W W' : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C, IsEnd (Y.rawSelf p) V W W' ∧ W + W' = 1 ∧ (∀ (v : Fin 2 × Fin dd → C) (x : Fin 2 × Fin dd), W.mulVec v x = linAct (Y.B.A.act Y.w0) (fun i => v (x.1, i)) x.2) ∧ ∑ col : Fin 2, inCol col (un1 (Y.B.hL C Y.h Y.w0)) = hEnd (Y.rawSelf p) 1 W := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p
  let X : RawChart C d (fun _ => I0) (Fin dd) :=
    { lg := fun i => un1 (Y.lg i), ex := fun i => un1 (Y.ex i), h := Y.h, k := 0, u := fun _ => p.e,
      ty := fun _ => p.ty0, n := 0, j := 0, j' := 0, big := fun _ _ => True }
  have hlg : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (un1 (Y.lg i)) = 0
    rw [constantCoeff_uncurry, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, Y.lg_lin i 0 (by simp)]
    simp
  have hex : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0 := by
    intro i
    show MvPowerSeries.constantCoeff (un1 (Y.ex i)) = 0
    rw [constantCoeff_uncurry]
    exact Y.ex_const i
  have hh : MvPowerSeries.constantCoeff X.h = 0 := by
    have := coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl (by
      intro g' hg'
      rw [fin_two_eq_one_sub_of_ne' _ _ hg']
      rfl) Y.gauge.ax0 0 (by simp)
    simpa using this
  have blk : ∀ M M' : Matrix (Fin dd) (Fin dd) C, M + M' = 1 →
      (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = y.1 then M x.2 y.2 else 0) +
        (Matrix.of fun x y : Fin 2 × Fin dd => if x.1 = y.1 then M' x.2 y.2 else 0) = 1 := by
    intro M M' h
    ext ⟨a, i⟩ ⟨b, j⟩
    have := congrFun (congrFun h i) j
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.of_apply, Prod.mk.injEq] at this ⊢
    by_cases hab : a = b
    · simp [hab, this]
    · simp [hab]
  have hone : (1 : Matrix (Fin 2 × Fin dd) (Fin 2 × Fin dd) C) =
      fun x y => if x.1 = y.1 then (1 : Matrix (Fin dd) (Fin dd) C) x.2 y.2 else 0 := by
    rw [← blk 1 0 (add_zero _)]
    ext x y
    simp
  refine ⟨_, _, teichSelf_double C V dd d d _ _ X (Y.rawSelf p) hlg hex hh rfl rfl rfl _ _
    (isEnd_act_raw Y X rfl rfl rfl Y.w0), blk _ _ (linear_parts_w0_sum_one Y), fun v x => ?_, ?_⟩
  · show _ = (dLin (Y.B.A.act Y.w0)).mulVec (fun i => v (x.1, i)) x.2
    simp only [Matrix.mulVec, dotProduct]
    rw [Fintype.sum_prod_type, Finset.sum_eq_single x.1]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · have hX : ∀ i : Fin dd, MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) = 0 :=
      fun i => by simp
    have hX' : ∀ i : Fin 2 × Fin dd,
        MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2 × Fin dd) C) = 0 := fun i => by simp
    have hlg' : ∀ i, MvPowerSeries.constantCoeff ((Y.rawSelf p).lg i) = 0 := fun i =>
      constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hlg _)
    have hex' : ∀ i, MvPowerSeries.constantCoeff ((Y.rawSelf p).ex i) = 0 := fun i =>
      constantCoeff_subst_zero (fun _ => MvPowerSeries.constantCoeff_X _) (hex _)
    unfold hEnd
    rw [hone]
    refine Eq.trans ?_ (teichSelf_hAt_col X (Y.rawSelf p) rfl _ _ (teichSelf_cc_endP _ hlg' hex' _ _ hX')
      (teichSelf_cc_endP _ hlg' hex' _ _ hX')).symm
    refine Finset.sum_congr rfl fun col _ => ?_
    have c : ∀ y : Fin dd, MvPowerSeries.constantCoeff
        (MvPowerSeries.X (col, y) : MvPowerSeries (Fin 2 × Fin dd) C) = 0 := fun _ => hX' _
    rw [gauge_at_linearPart_action_eq_hermitianLift Y X rfl rfl rfl, inCol, teichSelf_subst_hAt X _ _ (teichSelf_cc_endP X hlg hex _ _ hX)
      (teichSelf_cc_endP X hlg hex _ _ hX) _ c]
    simp only [teichSelf_subst_endP X hlg _ _ hX _ c,
      MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero c)]
    congr 1 <;> funext y <;> exact (teichSelf_endP_col X (Y.rawSelf p) hlg rfl rfl _ _ hX' (col, y)).symm

end GlobalTheory.ActionEndSelf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFreeGeneratorsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearIndependent_spanning_range_mulVec : ∀ (p : ℕ) [Fact p.Prime] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] (w : PlaceU p OE) (b : Module.Basis (Fin w.n) ℤ_[p] (LinearMap.range (LinearMap.mulLeft ℤ_[p] w.e))) (κ : Type) [Fintype κ] [DecidableEq κ] (ρ : (ℤ_[p] ⊗[ℤ] OE) →ₐ[ℤ_[p]] Matrix κ κ ℤ_[p]), ∃ (h : ℕ) (y : Fin h → κ → ℤ_[p]), LinearIndependent ℤ_[p] (fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) ∧ Submodule.span ℤ_[p] (Set.range fun q : Fin w.n × Fin h => ρ (b q.1 : ℤ_[p] ⊗[ℤ] OE) *ᵥ y q.2) = LinearMap.range (Matrix.mulVecLin (ρ w.e)) := by
  first | exact @GlobalTheory.LocalFactorFree.exists_free_generators | exact GlobalTheory.LocalFactorFree.exists_free_generators | (intros; apply GlobalTheory.LocalFactorFree.exists_free_generators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsSectionOfPow
section
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.CubeFib
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechRoot

theorem gen_res {X : Scheme.{0}} [IsIntegral X] {V W : X.Opens} [Nonempty V] [Nonempty W]
    (h : W ≤ V) (s : Γ(X, V)) :
    (X.germToFunctionField W).hom ((X.presheaf.map (homOfLE h).op).hom s) = (X.germToFunctionField V).hom s :=
  X.presheaf.germ_res_apply (homOfLE h) _ _ s

theorem nonempty_inf {X : Scheme.{0}} [IsIntegral X] (V W : X.Opens) [hV : Nonempty V] [hW : Nonempty W] :
    Nonempty (V ⊓ W : X.Opens) := by
  obtain ⟨⟨v, hv⟩⟩ := hV
  obtain ⟨⟨w, hw⟩⟩ := hW
  obtain ⟨z, hz⟩ := nonempty_preirreducible_inter V.isOpen W.isOpen ⟨v, hv⟩ ⟨w, hw⟩
  exact ⟨⟨z, hz⟩⟩

theorem exists_section_of_pow {X : Scheme.{0}} [IsIntegral X] (hN : ∀ b : X, IsIntegrallyClosed (X.presheaf.stalk b))
    {l : ℕ} (hl : 0 < l) (V : X.Opens) [Nonempty V] (f : Γ(X, V)) (t : X.functionField)
    (ht : t ^ l = (X.germToFunctionField V).hom f) : ∃ s : Γ(X, V), (X.germToFunctionField V).hom s = t := by
  refine IsNormalScheme.exists_germToFunctionField_eq_of_locally V t fun x hx => ?_
  refine exists_germToFunctionField_eq_of_mem_range_stalk ?_ hx
  haveI := hN x
  refine IsIntegrallyClosed.algebraMap_eq_of_integral (IsIntegral.of_pow hl ?_)
  rw [ht, ← Scheme.algebraMap_germ_eq_germToFunctionField X hx f]
  exact isIntegral_algebraMap

theorem charP_functionField {X : Scheme.{0}} [IsIntegral X] (l : ℕ) [Fact l.Prime] (h : (l : Γ(X, ⊤)) = 0) :
    CharP X.functionField l := by
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  refine (CharP.charP_iff_prime_eq_zero Fact.out).2 ?_
  rw [← map_natCast (X.germToFunctionField ⊤).hom, h, map_zero]

theorem exists_root : ∀ (X : Scheme.{0}) [IsIntegral X], (∀ b : X, IsIntegrallyClosed (X.presheaf.stalk b)) → ∀ (l : ℕ) [Fact l.Prime], (l : Γ(X, ⊤)) = 0 → ∀ (J : Type) (U : J → X.Opens) (f : ∀ j, Γ(X, U j)) (n : ∀ j j', Γ(X, U j ⊓ U j')), (∀ j j', (X.presheaf.map (homOfLE (inf_le_left : U j ⊓ U j' ≤ U j)).op).hom (f j) - (X.presheaf.map (homOfLE (inf_le_right : U j ⊓ U j' ≤ U j')).op).hom (f j') = n j j' ^ l) → ∀ (i : J) (b : X) (hb : b ∈ U i) (h : FractionRing (X.presheaf.stalk b)), h ^ l = algebraMap (X.presheaf.stalk b) _ ((X.presheaf.germ (U i) b hb).hom (f i)) → ∃ H : ∀ j, Γ(X, U j), ∀ j j', (X.presheaf.map (homOfLE (inf_le_left : U j ⊓ U j' ≤ U j)).op).hom (H j) - (X.presheaf.map (homOfLE (inf_le_right : U j ⊓ U j' ≤ U j')).op).hom (H j') = n j j' := by
  intro X _ hN l _ hl J U f n hf i b hb h hh
  haveI := charP_functionField l hl
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  haveI : Nonempty (U i) := ⟨⟨b, hb⟩⟩
  let e := FractionRing.algEquiv (X.presheaf.stalk b) X.functionField
  have he : e h ^ l = (X.germToFunctionField (U i)).hom (f i) := by
    rw [← map_pow, hh, AlgEquiv.commutes]
    exact Scheme.algebraMap_germ_eq_germToFunctionField X hb (f i)
  have hg : ∀ j j' [Nonempty (U j)] [Nonempty (U j')] [Nonempty (U j ⊓ U j' : X.Opens)],
      (X.germToFunctionField (U j)).hom (f j) - (X.germToFunctionField (U j')).hom (f j') =
        (X.germToFunctionField (U j ⊓ U j')).hom (n j j') ^ l := by
    intro j j' _ _ _
    rw [← map_pow, ← hf, map_sub, gen_res, gen_res]
  have ex : ∀ j, ∃ H : Γ(X, U j), ∀ [Nonempty (U j)],
      (X.germToFunctionField (U j)).hom H ^ l = (X.germToFunctionField (U j)).hom (f j) := by
    intro j
    by_cases hj : Nonempty (U j)
    · haveI := nonempty_inf (U j) (U i)
      have ht : (e h + (X.germToFunctionField (U j ⊓ U i)).hom (n j i)) ^ l =
          (X.germToFunctionField (U j)).hom (f j) := by
        rw [add_pow_char, he, ← hg, add_sub_cancel]
      obtain ⟨s, hs⟩ := exists_section_of_pow hN hl0 (U j) (f j) _ ht
      exact ⟨s, by intro _; rw [hs, ht]⟩
    · exact ⟨0, by intro h; exact absurd h hj⟩
  choose H hH using ex
  refine ⟨H, fun j j' => ?_⟩
  by_cases hj : Nonempty (U j ⊓ U j' : X.Opens)
  · obtain ⟨⟨z, hz⟩⟩ := id hj
    haveI : Nonempty (U j) := ⟨⟨z, hz.1⟩⟩
    haveI : Nonempty (U j') := ⟨⟨z, hz.2⟩⟩
    apply X.germToFunctionField_injective (U j ⊓ U j')
    apply frobenius_inj X.functionField l
    change (X.germToFunctionField (U j ⊓ U j')).hom _ ^ l = (X.germToFunctionField (U j ⊓ U j')).hom _ ^ l
    rw [map_sub, gen_res, gen_res, sub_pow_char, hH, hH, hg]
  · exact fn_ext (V := U j ⊓ U j') fun x hx => absurd ⟨⟨x, hx⟩⟩ hj

end GlobalTheory.CechRoot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalGroupSeriesSeparatedByTorsionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalGroup_series_separated_by_torsion : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → (∀ (k : ℕ) (f : PS O 1 d), (∀ φ, Killed F.F (p ^ k) φ → φ f = 0) → f ∈ Ideal.span (Set.range (mulF F.F (p ^ k)))) ∧ ∀ f : PS O 1 d, (∀ φ, Tors p F.F φ → φ f = 0) → f = 0 := by
  first | exact @GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors | exact GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors | (intros; apply GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GoodCurvesPairingMemMaxIdealStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodCurves_pairing_mem_maxIdeal : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → ∀ (H : ∀ g, X.CartHyp V g) (g : Fin 2) (a a' : ZMod d) (w : I g → C) (x : ℕ → I g ⊕ JJ I g → C) (w' : I (1 - g) → C) (x' : ℕ → I (1 - g) ⊕ JJ I (1 - g) → C), (RawChart.cart (H g)).Good a w x → (RawChart.cart (H (1 - g))).Good a' w' x' → (∀ c, V.MM ((RawChart.cart (H g)).V2 x c)) → V.MM (∑ q : I (1 - g), (RawChart.cart (H g)).c0' x q * w' q) := by
  first | exact @GlobalTheory.RowLaw.good_pairing_mem_max | exact GlobalTheory.RowLaw.good_pairing_mem_max | (intros; apply GlobalTheory.RowLaw.good_pairing_mem_max <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointLieProjectorsSelfConjugatePlaceStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaugeAdjointLieProjectors_selfConjugatePlace : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), HasProj (Y.rawSelf p) V := by
  first | exact @GlobalTheory.ProjSelf.hasProj_self | exact GlobalTheory.ProjSelf.hasProj_self | (intros; apply GlobalTheory.ProjSelf.hasProj_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasGaugeAdjointTeichmullerEndSelfConjugatePlaceStatement
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_selfConjugatePlace : ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] [StarRing O] (dd : ℕ) (Y : FBChart C V O dd) (d : ℕ) [NeZero d] (I0 : Type) [Fintype I0] (p : SelfData Y d I0), ∀ g, HasTeich (Y.rawSelf p) V g := by
  first | exact @GlobalTheory.hasTeich_selfData | exact GlobalTheory.hasTeich_selfData | (intros; apply GlobalTheory.hasTeich_selfData <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.InvariantValueCopiesEqZeroOfLowCoeffStatement
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantValueCopies_eq_zero_of_low_coeff : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (f : PS K n d) (P : MvPolynomial ι K), (∀ μ : Fin n × Fin d →₀ ℕ, μ.degree ≤ P.totalDegree → MvPowerSeries.coeff μ f = 0) → nabValN B K h w0 m f cp u P = 0 := by
  first | exact @GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero | exact GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero | (intros; apply GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero <;> assumption)
end

