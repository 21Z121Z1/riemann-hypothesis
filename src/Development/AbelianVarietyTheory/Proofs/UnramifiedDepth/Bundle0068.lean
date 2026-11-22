import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0067
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
import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffSubstSame
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.BlockOfNormalForm
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SumEqOfIsHomogeneous
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.RowTieSelf
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import Formalism.LocalToGlobal.CharacterGerms.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0059
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0063

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsCompleteIsAlgClosedAddValuation
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory.DvrClosedEmbedding

theorem exists_addValuation_log_norm {C : Type} [NormedField C] [IsUltrametricDist C] {r : ℝ}
    (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ v : AddValuation C (WithTop ℝ),
      (∀ x, x ≠ 0 → v x = ((Real.log ‖x‖ / Real.log r : ℝ) : WithTop ℝ)) ∧
      ∀ (x : C) (n : ℕ), (((n : ℕ) : ℝ) : WithTop ℝ) ≤ v x ↔ ‖x‖ ≤ r ^ n := by
  classical
  have hl : Real.log r < 0 := Real.log_neg hr0 hr1
  let f : C → WithTop ℝ := fun x =>
    if x = 0 then ⊤ else ((Real.log ‖x‖ / Real.log r : ℝ) : WithTop ℝ)
  have hf0 : f 0 = ⊤ := by simp [f]
  have hf : ∀ x, x ≠ 0 → f x = ((Real.log ‖x‖ / Real.log r : ℝ) : WithTop ℝ) := fun x hx => by
    simp [f, hx]
  have hmono : ∀ x y : C, ‖x‖ ≤ ‖y‖ → f y ≤ f x := by
    intro x y h
    by_cases hx : x = 0
    · rw [hx, hf0]; exact le_top
    have hx' : 0 < ‖x‖ := norm_pos_iff.2 hx
    have hy : y ≠ 0 := norm_pos_iff.1 (hx'.trans_le h)
    rw [hf x hx, hf y hy, WithTop.coe_le_coe]
    exact div_le_div_of_nonpos_of_le hl.le (Real.log_le_log hx' h)
  refine ⟨AddValuation.of f hf0 ?_ ?_ ?_, hf, ?_⟩
  · rw [hf 1 one_ne_zero]; simp
  · intro x y
    rcases le_max_iff.1 (IsUltrametricDist.norm_add_le_max x y) with h | h
    · exact min_le_of_left_le (hmono _ _ h)
    · exact min_le_of_right_le (hmono _ _ h)
  · intro x y
    by_cases hx : x = 0
    · rw [hx, zero_mul, hf0, WithTop.top_add]
    by_cases hy : y = 0
    · rw [hy, mul_zero, hf0, WithTop.add_top]
    rw [hf x hx, hf y hy, hf _ (mul_ne_zero hx hy), norm_mul,
      Real.log_mul (norm_ne_zero_iff.2 hx) (norm_ne_zero_iff.2 hy), add_div, WithTop.coe_add]
  · intro x n
    change _ ≤ f x ↔ _
    by_cases hx : x = 0
    · rw [hx, hf0, norm_zero]
      exact ⟨fun _ => by positivity, fun _ => le_top⟩
    rw [hf x hx, WithTop.coe_le_coe, le_div_iff_of_neg hl, ← Real.log_pow,
      Real.log_le_log_iff (norm_pos_iff.2 hx) (pow_pos hr0 n)]

theorem exists_limit_of_norm_sub_le_pow {C : Type} [NormedField C] [IsUltrametricDist C]
    [CompleteSpace C] {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (s : ℕ → C)
    (hs : ∀ n, ‖s (n + 1) - s n‖ ≤ r ^ n) : ∃ x, ∀ n, ‖x - s n‖ ≤ r ^ n := by
  have hc : CauchySeq s := by
    refine cauchySeq_of_le_geometric r 1 hr1 fun n => ?_
    rw [dist_comm, dist_eq_norm, one_mul]
    exact hs n
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨L, fun n => ?_⟩
  refine le_of_tendsto ((hL.sub tendsto_const_nhds).norm) ?_
  filter_upwards [Filter.eventually_ge_atTop n] with m hm
  induction m, hm using Nat.le_induction with
  | base => simp; positivity
  | succ m hm ih =>
    have h := IsUltrametricDist.norm_add_le_max (s (m + 1) - s m) (s m - s n)
    rw [sub_add_sub_cancel] at h
    exact h.trans (max_le ((hs m).trans (pow_le_pow_of_le_one hr0.le hr1.le hm)) ih)

theorem exists_complete_isAlgClosed_addValuation :
    ∀ (T : CDVR) (p : ℕ), p.Prime → ¬ IsUnit (p : T.V) → ∃ (C : Type) (_ : Field C) (_ : CharZero C) (v : AddValuation C (WithTop ℝ)) (ι : T.Fr →+* C), v (p : C) = 1 ∧ (∀ x : T.Fr, x ≠ 0 → v (ι x) = (((vV T.V x : ℝ) / (vV T.V ((p : ℕ) : T.Fr) : ℝ) : ℝ) : WithTop ℝ)) ∧ IsAlgClosed C ∧ ∀ s : ℕ → C, (∀ n : ℕ, (((n : ℕ) : ℝ) : WithTop ℝ) ≤ v (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, (((n : ℕ) : ℝ) : WithTop ℝ) ≤ v (x - s n) := by
  intro T p hp hu
  have hp0 : (p : T.V) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hr0 : (0 : ℝ) < 1 / 2 := by norm_num
  have hr1 : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨C, _, _, _, _, _, hC, hCp⟩ :=
    exists_complete_isAlgClosed_of_isDiscreteValuationRing T.V T.Fr hp0
      ((IsLocalRing.mem_maximalIdeal _).2 hu) hr0 hr1
  rw [map_natCast] at hCp
  have : CharZero T.Fr := charZero_of_injective_ringHom (IsFractionRing.injective T.V T.Fr)
  have : CharZero C := charZero_of_injective_ringHom (algebraMap T.Fr C).injective
  obtain ⟨v, hv, hvn⟩ := exists_addValuation_log_norm (C := C) hr0 hr1
  have hl : Real.log (1 / 2) ≠ 0 := (Real.log_neg hr0 hr1).ne
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  have hz : ∀ x : T.Fr, x ≠ 0 → Real.log ‖algebraMap T.Fr C x‖ =
      (vV T.V x : ℝ) * Real.log ‖algebraMap T.Fr C (algebraMap T.V T.Fr π)‖ := fun x hx => by
    rw [ArcQ.norm_map_eq_zpow_vV (algebraMap T.Fr C) (fun a => (hC _).2 ⟨a, rfl⟩) hπ hx,
      Real.log_zpow]
  have hpF : (p : T.Fr) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hzp := hz p hpF
  rw [hCp] at hzp
  refine ⟨C, inferInstance, inferInstance, v, algebraMap T.Fr C, ?_, fun x hx => ?_,
    inferInstance, fun s hs => ?_⟩
  · rw [map_natCast] at hCp
    rw [hv _ (Nat.cast_ne_zero.2 hp.ne_zero), hCp, div_self hl, WithTop.coe_one]
  · rw [hv _ ((map_ne_zero _).2 hx), hz x hx, hzp,
      mul_div_mul_right _ _ (right_ne_zero_of_mul (hzp ▸ hl))]
  · obtain ⟨x, hx⟩ := exists_limit_of_norm_sub_le_pow hr0 hr1 s fun n => (hvn _ n).1 (hs n)
    exact ⟨x, fun n => (hvn _ n).2 (hx n)⟩

end GlobalTheory.DvrClosedEmbedding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLinearDataOfSplitFormalGroupExtensionStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearData_of_split_formalGroup_extension : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (d g r : ℕ) (F : FGLaw O d) (FB : FGLaw O g) (J : Fin d → PS O 1 r) (Q : Fin g → PS O 1 d), ExtSer F.F FB.F J Q → FH p F.F → ∀ (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (αB : OE → Fin g → PS O 1 g), (∀ a, lin Q * ρG a = lin (αB a) * lin Q) → (∀ a, ρG a * lin J = lin J * (N a).map (Int.castRingHom O)) → (∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (αB a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ ∀ i, ∃ u : PS O 1 g, IsCh FB.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (B : Matrix (Fin g) (Fin d) O) (m : ℕ) (u : Fin m → PS O 1 d), (∀ k, IsCh F.F (u k)) ∧ LinDat H (lin J) B ρG N (fun k => dl (u k)) := by
  first | exact @GlobalTheory.ChF.exists_linDat_of_extSer | exact GlobalTheory.ChF.exists_linDat_of_extSer | (intros; apply GlobalTheory.ChF.exists_linDat_of_extSer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OddLevelBlockBoundAttained
section
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.MinorShiftJet

variable {K : Type} [Field K] {V : VF K} {d : ℕ} [NeZero d] {I J : Fin 2 → Type}
  [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem big_shift (X : RowData K V d I J) (h : X.Alt) {g : Fin 2} {a : ZMod d} (ha : X.big g a) {i : ℕ}
    (hi : Odd i) : X.big (1 - g) (a + (i : ZMod d)) := by
  have hpar : Even (a + (i : ZMod d)).val ↔ ¬ Even a.val := by
    rw [ZMod.val_add, ZMod.val_natCast]
    obtain ⟨r, hr⟩ := h.1
    have h2 : 2 ∣ d := ⟨r, by omega⟩
    rw [Nat.even_iff, Nat.even_iff, Nat.mod_mod_of_dvd _ h2, Nat.add_mod, Nat.mod_mod_of_dvd _ h2,
      Nat.odd_iff.1 hi]
    omega
  rw [X.big_compl]
  have h1 : ∀ b, X.big 1 b ↔ ¬ X.big 0 b := fun b => by simpa using X.big_compl 0 b
  fin_cases g
  · simp only [Fin.zero_eta] at ha ⊢
    rw [h.2] at ha ⊢
    rw [hpar]; exact fun h' => h' ha
  · simp only [Fin.mk_one] at ha ⊢
    rw [h1, h.2] at ha ⊢
    rw [hpar]; exact fun h' => h' ha

omit [∀ g, Fintype (I g)] in
theorem rename_minor {n N : ℕ} (hN : n ≤ N) (g : Fin 2) (en : Fin N → I g) :
    MvPolynomial.rename (fun x : Fin n × Fin N => (x.1, (⟨g, en x.2⟩ : WV I))) (minorK K n N n) =
      letterDet K g fun c => en (Fin.castLE hN c) := by
  rw [minorK, dif_pos ⟨le_rfl, hN⟩, AlgHom.map_det, letterDet]
  congr 1
  refine Matrix.ext fun b c => ?_
  simp

theorem satIn_single (X : RowData K V d I J) (g : Fin 2) (a : ZMod d) {N : ℕ} (p : Fin N → I g)
    (hp : Function.Injective p) (hty : ∀ c, (X.G g).ty (Sum.inl (p c)) = a) :
    X.SatIn g a fun b x => if x = p b then 1 else 0 := by
  have h01 : ∀ (P : Prop) [Decidable P], V.Ge 0 (if P then (1 : K) else 0) := by
    intro P _; split_ifs
    exacts [VF.Ge.one, VF.Ge.zero _]
  refine ⟨⟨fun c x => h01 _, fun x c => if x = p c then 1 else 0, fun x c => h01 _, fun c c' => ?_⟩,
    fun c x hx => if_neg fun h => hx (by rw [h, hty])⟩
  simp [hp.eq_iff, eq_comm]

theorem cc_mvExp' {σ : Type} (x : MvPowerSeries σ K) : constantCoeff (mvExp x) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply]
  change ∑ j ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), coeff 0 (x ^ j) / (j.factorial : K) = 1
  simp

theorem jetAt0_one' {σ : Type} (G : MvPowerSeries σ K) : jetAt0 1 G = constantCoeff G := by
  rw [← MvPolynomial.C_1, ← MvPolynomial.monomial_zero', jetAt0_monomial]
  simp [mfact]

theorem mono_resι_var {l i n0 n : ℕ} (hl : 5 ≤ l) (hn : n0 ≤ n) : S0 l i n0 ≤ S0 l i n := by
  unfold S0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have h0 : 0 ≤ Real.logb l ((n0 : ℝ) + 1) := Real.logb_nonneg hl1 (by linarith [Nat.cast_nonneg (α := ℝ) n0])
  have h1 : Real.logb l ((n0 : ℝ) + 1) ≤ Real.logb l ((n : ℝ) + 1) :=
    Real.logb_le_logb_of_le hl1 (by positivity) (by linarith)
  refine Nat.ceil_mono ?_
  gcongr

theorem sum_positive_of_five_le {l i n : ℕ} (hl : 5 ≤ l) (hn : 1 ≤ n) : 0 < S0 l i n := by
  unfold S0
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : 0 ≤ Real.logb l ((n : ℝ) + 1) := Real.logb_nonneg hl1 (by linarith)
  refine Nat.ceil_pos.2 ?_
  positivity

theorem window_letterDet (X : RowData K V d I J) (hA : X.Alt) (hl : 5 ≤ V.l) (hn1 : 1 ≤ X.n)
    (g : Fin 2) (a : ZMod d) (ha : X.big g a) (i : ℕ) (hi : Odd i) (hid : i < d)
    (p : Fin X.n → I g) (p' : Fin X.n → I (1 - g)) (hp : Function.Injective p) (hp' : Function.Injective p')
    (hty : ∀ c, (X.G g).ty (Sum.inl (p c)) = a)
    (hty' : ∀ c, (X.G (1 - g)).ty (Sum.inl (p' c)) = a + (i : ZMod d)) :
    Windows (S0 V.l i X.n) {y | ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) K),
      (∀ g, (S g).IsT (t g)) ∧ ∃ gr : Fin X.n → MvPowerSeries (WV I) K, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (letterDet K g p ^ (V.l ^ i * y) * letterDet K (1 - g) p' ^ y)
          (fun _ => some (g, a, a + (i : ZMod d))) gr) ≤ ((blockBd V.l X.n X.m i y : ℝ) : WithTop ℝ)} := by
  have := X.charZero
  obtain ⟨n0, e, v', Φ, hM, -⟩ := (GlobalTheory.T.rowData_mainTerm_normalForm_and_levelOne K V d I J X).1 hA hl g a ha i hi hid _ _
    (satIn_single X g a p hp hty) (satIn_single X (1 - g) _ p' hp' hty')
  have hn : n0 ≤ X.n := hM.1.2
  obtain ⟨hR, hH1, hH2, -⟩ := GlobalTheory.T.mainTerm_implies_rowHypothesis K V d I J X g a i _ _ n0 e v' Φ hM hn
  obtain ⟨S, t, hSt, hr, tt, tt', hB, hy⟩ :=
    block_of_normal_form X g a i p p' hp hp' n0 e v' Φ hM hn _ hR
  have hrank : X.n - n0 ≤ (i + 1) * X.m := by
    have h1 := hM.1.1
    have h2 : (i + 1) * X.m = (i + 1) * X.j' + X.j + i * X.j := by unfold RowData.m; ring
    omega
  have hgood : ∀ y : ℕ, V.v (jetAt0 (detL K X.n ^ (V.l ^ i * y) * detR K X.n ^ y)
      (BiF V.l i n0 X.n y hr tt tt')) ≤ (((bdP V.l i X.n X.n y + ((i : ℝ) + 1) * X.m * ((V.l : ℝ) ^ i + 1) * y /
        ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ) ∨ y = 0 →
      ∃ gr : Fin X.n → MvPowerSeries (WV I) K, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (letterDet K g p ^ (V.l ^ i * y) * letterDet K (1 - g) p' ^ y)
          (fun _ => some (g, a, a + (i : ZMod d))) gr) ≤ ((blockBd V.l X.n X.m i y : ℝ) : WithTop ℝ) := by
    intro y h
    obtain ⟨gr, hgr, hv⟩ := hy y
    refine ⟨gr, hgr, hv.trans ?_⟩
    by_cases h0 : y = 0
    · subst h0
      simp only [blockBd, if_true, mul_zero, pow_zero, mul_one, jetAt0_one', BiF, ite_self, one_mul, map_prod,
        cc_mvExp', Finset.prod_const_one, V.v.map_one]
      rfl
    · rw [blockBd, if_neg h0]
      exact h.resolve_right h0
  refine ⟨⟨S, t, hSt, hgood 0 (Or.inr rfl)⟩, fun Y0 => ?_⟩
  rcases Nat.eq_zero_or_pos n0 with h0 | h0
  · subst h0
    refine ⟨Y0, ⟨S, t, hSt, hgood Y0 (Or.inl ?_)⟩, le_rfl, Nat.lt_add_of_pos_right (sum_positive_of_five_le hl hn1)⟩
    have hl1 : (1 : ℝ) < V.l := by exact_mod_cast (by omega : 1 < V.l)
    rw [GlobalTheory.T.blockValue_on_rows_eq K V.l i 0 X.n hn hr tt tt' _ hB Y0]
    refine (GlobalTheory.OddBlock.content_and_window.1 K V.v V.l V.l_prime hl V.v_l i X.n 0 Y0 hi hn1 hn _ ?_).trans ?_
    · have : LamP K V.l i 0 (X.restrictedCurveSystemSeries g a i hn e v') Y0 = 1 := by
        simp [LamP, detL, detR, jetAt0_one', cc_mvExp']
      rw [this, V.v.map_one]
      have hn' : (1 : ℝ) ≤ X.n := by exact_mod_cast hn1
      have h0 : 0 ≤ Real.logb V.l (X.n : ℝ) := Real.logb_nonneg hl1 hn'
      have : 0 ≤ bdP V.l i 0 X.n Y0 := by
        simp only [bdP, Nat.cast_zero, zero_mul, zero_add]; positivity
      exact_mod_cast this
    · rw [WithTop.coe_le_coe]
      have h3 : ((X.n : ℝ) - ((0 : ℕ) : ℝ)) ≤ ((i : ℝ) + 1) * X.m := by
        rw [Nat.cast_zero, sub_zero]; exact_mod_cast hrank
      have : (0 : ℝ) < (V.l : ℝ) - 1 := by linarith
      gcongr
  · obtain ⟨y, h1, h2, h3⟩ := GlobalTheory.OddBlock.content_and_window.2 K V.v V.l V.l_prime hl V.v_l i hi n0 X.n X.m hn h0 hrank hr tt tt' _
      hB hH1 hH2 Y0
    exact ⟨y, ⟨S, t, hSt, hgood y (Or.inl h3)⟩, h1, h2.trans_le (Nat.add_le_add_left (mono_resι_var hl hn) _)⟩

end GlobalTheory.MinorShiftJet

namespace GlobalTheory

open MinorShiftJet

theorem oddBlock_supply : BiSupply ∧ RF.BiSupply := by
  constructor
  · intro K _ V d _ I J _ _ X F hA hl hn g a ha i hi hid
    have h1 : X.n ≤ X.rk g a := (Nat.le_add_right _ _).trans (X.rk_big g a ha).ge
    have h2 : X.n ≤ X.rk (1 - g) (a + (i : ZMod d)) :=
      (Nat.le_add_right _ _).trans (X.rk_big _ _ (big_shift X hA ha hi)).ge
    have key := window_letterDet X hA hl hn g a ha i hi hid (fun c => F.en g a (Fin.castLE h1 c))
      (fun c => F.en (1 - g) (a + (i : ZMod d)) (Fin.castLE h2 c))
      ((F.en_inj _ _).comp (Fin.castLE_injective h1)) ((F.en_inj _ _).comp (Fin.castLE_injective h2))
      (fun c => F.en_ty _ _ _) (fun c => F.en_ty _ _ _)
    rw [← rename_minor h1 g (F.en g a), ← rename_minor h2 (1 - g) (F.en (1 - g) (a + (i : ZMod d)))] at key
    exact key
  · intro K _ V d _ I J _ _ X F hA hl hn g a ha i hi hid
    have h1 : X.n ≤ X.rkF g a := (Nat.le_add_right _ _).trans (X.rk_big g a ha).ge
    have h2 : X.n ≤ X.rkF (1 - g) (a + (i : ZMod d)) :=
      (Nat.le_add_right _ _).trans (X.rk_big _ _ (big_shift X hA ha hi)).ge
    have key := window_letterDet X hA hl hn g a ha i hi hid (fun c => F.en g a (Fin.castLE h1 c))
      (fun c => F.en (1 - g) (a + (i : ZMod d)) (Fin.castLE h2 c))
      ((F.en_inj _ _).comp (Fin.castLE_injective h1)) ((F.en_inj _ _).comp (Fin.castLE_injective h2))
      (fun c => F.en_ty _ _ _) (fun c => F.en_ty _ _ _)
    rw [← rename_minor h1 g (F.en g a), ← rename_minor h2 (1 - g) (F.en (1 - g) (a + (i : ZMod d)))] at key
    exact key

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.RowLawFormalStatementsSelfConjugate
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem formal_statements_selfConj :
    CartSelfSt ∧ AxesSelfSt ∧ GermZeroSelfConjugate ∧ CEqSelfSt ∧ IndependenceBoundSelfConjugate := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact GlobalTheory.T.cartHyp_of_integralGaugedFormalGroupLaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p) (GlobalTheory.T.hasGaugeAdjointLieProjectors_selfConjugatePlace C V O dd Y d I0 p)
      (GlobalTheory.T.hasGaugeAdjointTeichmullerEnd_selfConjugatePlace C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    have h := GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p
    exact RawChart.axes_of _ h.exc h.axes
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact intGerm_indep_of_rlaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p _
    exact GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)
  · intro C _ _ V O _ _ dd Y d _ I0 _ p
    exact GlobalTheory.T.gaugedFormalGroup_kernel_small_of_second C V d _ _ _ (GlobalTheory.T.isIntegralGaugedFormalGroupLaw_selfConjugateSquare C V O dd Y d I0 p)

end GlobalTheory.RowLaw
end

