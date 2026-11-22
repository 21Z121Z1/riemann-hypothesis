import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2526
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2843
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2627
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3239
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2788
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3101
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3313
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3517
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngehrnSiuNotKltAtSeveralPoints
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3519
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3523
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3268
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3031
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GensOfPsiUnitOn
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2181
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3334
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2678
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2842
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3413
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3377

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicNormNefIndicators
section
set_option autoImplicit false

noncomputable section

section Moduli

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open scoped NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.FlatModel

namespace GlobalTheory.DetHT

theorem detConst_of (hT : TestPtSt) (hX : ExFrameSt) (hP : PointSt) {E : Type} [Field E] [NumberField E] [IsCMField E]
    [IsGalois ℚ E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
    (hpq : 1 ≤ Dw.p + Dw.q) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (Zc : Formalism.L2.Pj.Comp Xo c)
    (τ : Psi H) {f : Rul Xo c} (hf : f ∈ secZ Xo c (exOf Dw (flatWt Dw τ) 0))
    (h : ∀ la : HeightOneSpectrum (𝓞 c.F), ∃ ρ : ℝ, ∀ w ∈ htValOn Zc la, w f = (ρ : EReal)) : DetConst Z Zc τ.1 f := by
  intro la p _
  obtain ⟨ρ, hρ⟩ := h la
  obtain ⟨K, hK⟩ := hP E H Dw τ p
  refine ⟨ρ * Real.log ((Valued.v : Valuation ℂ_[p] ℝ≥0) (p : ℂ_[p])) / (vLa la (p : c.F) : ℝ) + K, fun hla P hA hZ => ?_⟩
  obtain ⟨yb, hyb⟩ := hT E H Dw l Xo c Z p P hA
  obtain ⟨y, hy, hyP, Q, π, ψ, z, hQ, hz⟩ := hX E H Dw l Xo c hpq Z Zc la p hla P yb hyb hZ
  have h1 : val_vw la p (Valued.v : Valuation ℂ_[p] ℝ≥0) (evR Xo c f y) = (ρ : EReal) := hρ _ hy
  have h0 : evR Xo c f y ≠ 0 := fun e => by
    rw [e, val_vw_zero] at h1
    exact EReal.coe_ne_top ρ h1.symm
  obtain ⟨h2, h3⟩ := hK l Xo c Z f hf P y z yb hyP Q π ψ hQ hz h0
  refine ⟨h2, h3.trans (congrArg (· + K) ?_)⟩
  rw [val_vw_of_ne la p _ h0, EReal.coe_eq_coe_iff, coe_valued, coe_valued] at h1
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [← coe_valued]
    exact_mod_cast lt_one_of_not_isUnit (PadicComplexInt.integers p) (PadicComplexHost.not_isUnit_p p)
  have hl : Real.log ‖(p : ℂ_[p])‖ ≠ 0 := (Real.log_neg (norm_pos_iff.2 hp0) hp1).ne
  have hv : (vLa la (p : c.F) : ℝ) ≠ 0 := by
    have hc : (p : c.F) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
    have hne : la.valuation c.F (p : c.F) ≠ 1 := fun e => by
      have := (hla (p : c.F)⁻¹).2 (by rw [map_inv₀, e, inv_one])
      rw [map_inv₀, map_natCast, norm_inv] at this
      exact absurd (one_lt_inv₀ (norm_pos_iff.2 hp0) |>.2 hp1) this.not_gt
    have h0' : la.valuation c.F (p : c.F) ≠ 0 := (Valuation.ne_zero_iff _).2 hc
    rw [Int.cast_ne_zero, vLa, neg_ne_zero]
    intro e
    exact hne (by rw [← WithZero.exp_log h0', e, WithZero.exp_zero])
  rw [coe_valued, ← h1]
  field_simp

end GlobalTheory.DetHT

end Moduli

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

namespace GlobalTheory.DetHT

theorem valAt_stalk {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : GlobalTheory.Cartier.RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [GlobalTheory.TrueGeo.valAt, dif_pos h, IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec]

theorem valAt_inv_of_unit {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) {g : Z.functionField}
    (h : GlobalTheory.Cartier.UnitAt (below y) g) : valAt y g⁻¹ = (valAt y g)⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := h
  obtain ⟨u, rfl⟩ := ha
  rw [← map_units_inv, valAt_stalk, valAt_stalk, map_units_inv]

theorem log_w_valAt_inv {F : Type} [Field F] [NumberField F] {Y : Var F} {v : HeightOneSpectrum (𝓞 F)} (e : Ext v)
    (y : AlgPt Y) {g : Y.Fn} (h : GlobalTheory.Cartier.UnitAt (below y.1) g) :
    Real.log (e.w (valAt y.1 g⁻¹)) = -Real.log (e.w (valAt y.1 g)) := by
  rw [valAt_inv_of_unit y.1 h, map_inv₀, Real.log_inv]

theorem nefOver_det_of (hG : GeoSt) (hA : AnyLevSt) (hT : TestPtSt) (hX : ExFrameSt) (hP : PointSt) (hF : FlagSt) :
    OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∀ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ τ : D.what₂.Tau, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l := by
  intro D O _ _ _ _ _ _ c Q l hlQ hl V M hM τ
  haveI : IsGalois ℚ D.host.E := D.host.hostE_isGalois
  have hpq : 1 ≤ O.S.Dw.p + O.S.Dw.q := (one_le_two.trans O.S.two_le).trans O.S.rank_eq.ge
  obtain ⟨q, hq⟩ := GlobalTheory.T.flag_components_biject_moduli_components D O.A O.N O.j O.S O.κ O.s O.Φ
  let τ' : Psi O.A.H := ⟨DV.tauEmb D τ, O.A.cm τ⟩
  obtain ⟨f, hf, hc⟩ := hA _ O.A.H O.S.Dw O.κ.l O.s.Xo O.κ.c hpq O.κ.good
    (GlobalTheory.RankOneDatum.exists_datum_of_rt D O.A.H O.A.rt_eq O.A.cmHost_rootComplex_eq_pm_sqrt) O.κ.curve (q c) τ'
  have hD := detConst_of hT hX hP hpq O.s.T.Z (q c) τ' hf hc
  have key := hF _ O.A.H O.S.Dw O.κ.l O.s.Xo O.κ.c O.s.T.Z _ O.κ.e (O.Φ.C c) (q c) τ' f hf (hq c) hD O.N O.S.rank_eq
    (GlobalTheory.ShFam.Pad.ArIn.ind Q) none
  let W : (O.var c).X.Opens := (O.Φ.C c).π ⁻¹ᵁ (GlobalTheory.Toroidal.genBd O.s.T.Z).compl
  have hW : (W : Set (O.var c).X).Nonempty := by
    letI := (GlobalTheory.ShFam.constF O.κ.e (O.Φ.C c).Y).toAlgebra
    refine ⟨genericPoint _, fun h => h ⟨GlobalTheory.AllWt.ptF (O.Φ.C c).y0 (IsLocalRing.closedPoint _), ?_⟩⟩
    have := congrArg (fun g : Sp (O.var c).Fn ⟶ _ => g (IsLocalRing.closedPoint (O.var c).Fn)) (O.Φ.C c).y0_x
    simp only [Scheme.Hom.comp_apply] at this
    refine this.trans (congrArg (O.Φ.C c).π ?_)
    exact Scheme.fromSpecStalk_closedPoint
  have hv : ∀ v : HeightOneSpectrum (𝓞 D.what₂.LL), (l : 𝓞 D.what₂.LL) ∈ v.asIdeal →
      GlobalTheory.ShFam.Pad.ArIn.ind Q (resP v) = true := fun v hv => by
    simp [GlobalTheory.ShFam.Pad.ArIn.ind, (GlobalTheory.PlaceSum.residueCharacteristic_eq_iff v hl).2 hv, hlQ]
  have e₁ (n : ℤ) (z : (O.var c).X) : ∏ x : DV.Rt D.what₂.Tau O.N, genAt (O.root0 c Q x).D z ^ (if x.1 = τ then n else 0) =
      (∏ i : Fin O.N, genAt (divOf (O.Φ.C c) (expo O.S.Dw (rootSym O.S.Dw (GlobalTheory.ShFam.Pad.ArIn.ind Q) none τ'.1 i))) z) ^ n := by
    rw [Fintype.prod_prod_type, Finset.prod_eq_single τ (fun σ _ hσ => by simp [hσ]) (by simp), ← Finset.prod_zpow]
    simp only [if_true]
    rfl
  have e₂ (n : ℤ) (v e y) : ∑ x : DV.Rt D.what₂.Tau O.N, ((if x.1 = τ then n else 0 : ℤ) : ℝ) * (O.root0 c Q x).lg v e y =
      n * ∑ i : Fin O.N, lgOf (O.Φ.C c) (rootSym O.S.Dw (GlobalTheory.ShFam.Pad.ArIn.ind Q) none τ'.1 i) v e y := by
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun σ _ hσ => by simp [hσ]) (by simp), Finset.mul_sum]
    simp only [if_true]
    rfl
  constructor
  · refine hG _ _ V _ _ _ _ (norms_comb hM _) ((O.Φ.C c).val f) W hW l hl fun v h => ?_
    obtain ⟨ρ, hρ⟩ := key v (hv v h)
    refine ⟨ρ, fun e y hy => ?_⟩
    rw [e₁, e₂, zpow_one, Int.cast_one, one_mul]
    exact hρ e y hy
  · refine hG _ _ V _ _ _ _ (norms_comb hM _) ((O.Φ.C c).val f)⁻¹ W hW l hl fun v h => ?_
    obtain ⟨ρ, hρ⟩ := key v (hv v h)
    refine ⟨-ρ, fun e y hy => ?_⟩
    obtain ⟨h₁, h₂⟩ := hρ e y hy
    rw [e₁, e₂, zpow_neg_one, inv_div_inv, ← inv_div, Int.cast_neg, Int.cast_one, neg_one_mul]
    refine ⟨h₁.inv, ?_⟩
    rw [log_w_valAt_inv e y h₁]
    linarith

theorem nefOver_det :
    Hypotheses2 → HypothesesH → OnObj fun D O _ _ _ _ => ∀ (c : O.s.Comp) (Q : Finset ℕ) (l : ℕ), l ∈ Q → l.Prime → ∀ (V : Cover (O.var c)) (M : DV.Rt D.what₂.Tau O.N → HermLB V.p), (∀ x, Norms V (M x) (fun z => genAt (O.root0 c Q x).D z) (fun σ y => lnAdl (O.root0 c Q x) σ y) (fun v e y => (O.root0 c Q x).lg v e y)) → ∀ τ : D.what₂.Tau, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l :=
  fun hP _ => nefOver_det_of (GlobalTheory.T.regular_local_implies_geometric GlobalTheory.T.RegularLocalStatement) (GlobalTheory.T.anyLevSt_of_covering hP) GlobalTheory.T.TestPointStatement GlobalTheory.T.ExistsFrameStatement
    (GlobalTheory.T.point_count_of_eigen_covolume_hypotheses GlobalTheory.T.ConnectingStatement GlobalTheory.T.EigenvalueStatement GlobalTheory.T.CovolumeStatement) GlobalTheory.T.flag_statement_holds

end GlobalTheory.DetHT

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointActionsOrderFiniteUnramifiedSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjointActions_order_finite_unramified_scheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (Q : LB (A ⊗ A).left), IsAbelianScheme A → Q.IsLB → (∃ t : (Q.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (Q.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso Q (Q.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (Q.pull (lift (𝟙 A) (𝟙 A)).left) → ∀ (O : Type) [Ring O] (bar : O → O) (r : ℕ) (e : Fin r → O) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), (∀ a b, bar (a + b) = bar a + bar b) → Submodule.span ℤ (Set.range e) = ⊤ → ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → 0 < d → ∑ i, ∑ j, W i j • (e j * bar (e i)) = (d : O) → ∃ R : ActRep A Q bar, IsFinite R.π ∧ FormallyUnramified R.π := by
  first | (exact @GlobalTheory.EndLoc.actRep_finite_unramified) | (exact GlobalTheory.EndLoc.actRep_finite_unramified) | (intros; apply GlobalTheory.EndLoc.actRep_finite_unramified  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AngehrnSiuNotKltAtSeveralPointsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.angehrnSiu_not_klt_at_several_points : GlobalTheory.Published.Principalisation →
  ∀ {K κ : Type} [Field K] [Field κ] [Algebra ℂ K] [Algebra ℂ κ] (n k c l M : ℕ) (R : Fin c → Subring K)
    (π : ∀ i, R i →+* κ) (w : ∀ i, Fin l → R i) (lam : Fin c → κ) (wb : Fin l → κ),
  (∃ x : Fin n → K, TrBasis (algebraMap ℂ K) x) → (∃ z : Fin k → κ, TrBasis (algebraMap ℂ κ) z) → 1 ≤ k →
  (∀ i, IsLocModel (algebraMap ℂ K) (R i) ∧ IsIntegrallyClosed (R i) ∧ RatRes (algebraMap ℂ K) (R i)) →
  (∀ i a (h : algebraMap ℂ K a ∈ R i), π i ⟨algebraMap ℂ K a, h⟩ = algebraMap ℂ κ a) →
  (∀ i (f : κ), ∃ a b : R i, π i b ≠ 0 ∧ f * π i b = π i a) →
  (∀ i, IsLocModel (algebraMap ℂ κ) (π i).range ∧ RatRes (algebraMap ℂ κ) (π i).range) →
  (∀ i, lam i ≠ 0 ∧ ∀ j, π i (w i j) = lam i * wb j) →
  c * (M + k - 1).choose k < l → 1 ≤ M →
  ∃ a : Fin l → ℂ, a ≠ 0 ∧ ∀ (i : Fin c) (xi : Fin n → R i) (φ : R i →₀ ℚ) (u s : R i) (t : ℚ),
    TrBasis (algebraMap ℂ K) (fun j => (xi j : K)) → (∀ g ∈ φ.support, g ≠ 0) →
    EffAt (algebraMap ℂ K) n (R i) (dForm (algebraMap ℂ K) (fun j => (xi j : K)))
      (Finsupp.mapDomain (fun g : R i => (g : K)) φ) →
    π i u = 0 → 0 ≤ t → (s : K) = ∑ j, algebraMap ℂ K (a j) * (w i j : K) + u → (s : K) ≠ 0 →
    ((Function.Injective (π i) ∧ (k : ℚ) ≤ t * M) ∨
      ∃ E : Place (algebraMap ℂ K), E.Contains (R i) ∧ (∀ r : R i, (r : K) ≠ 0 → (π i r = 0 ↔ 0 < E.ord r)) ∧
        (k : ℚ) + M * (E.disc (dForm (algebraMap ℂ K) (fun j => (xi j : K)))
          (Finsupp.mapDomain (fun g : R i => (g : K)) φ) + 1) ≤ t * M) →
    ¬ Klt (algebraMap ℂ K) n (R i) (dForm (algebraMap ℂ K) (fun j => (xi j : K)))
      (Finsupp.mapDomain (fun g : R i => (g : K)) φ + Finsupp.single (s : K) t) := by
  first | exact @GlobalTheory.LocalHeart.not_klt_at_points | exact GlobalTheory.LocalHeart.not_klt_at_points | (intros; apply GlobalTheory.LocalHeart.not_klt_at_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyLatticeIdentificationEqId
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.LatId

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem second_diff_bal {X Y K I : Type} [AddCommGroup X] [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] [Field K]
    [Fintype I] (e : X ≃ₗ[𝓞 E] Y) (s : I → K) (hs : ∀ k, s k ≠ 0) (ε : I → LinearMap.BilinForm ℤ Y)
    (hε : ∀ k, ε k ∈ balForms H.bar Y) (n : ℤ) (g : X → Kˣ)
    (hg : ∀ y, (((g y)⁻¹ : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e y) (H.w0 • e y))) (a a' : X) :
    (((g (a + a'))⁻¹ * g a * g a' : Kˣ) : K) = ∏ k, s k ^ (n * ε k (e a) (e a')) := by
  have hw : H.w0 + H.bar H.w0 = 1 := GlobalTheory.PelPrim.cmHostUnit_add_conj_eq_one H
  have hg' : ∀ y, (g y : K) = (∏ k, s k ^ (n * ε k (e y) (H.w0 • e y)))⁻¹ := fun y => by
    rw [← hg, Units.val_inv_eq_inv_val, inv_inv]
  rw [Units.val_mul, Units.val_mul, hg, hg', hg', ← Finset.prod_inv_distrib, ← Finset.prod_inv_distrib,
    ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_neg, ← zpow_neg, ← zpow_add₀ (hs k), ← zpow_add₀ (hs k)]
  congr 1
  have h1 : ε k (e a') (H.w0 • e a) = ε k (e a) (H.bar H.w0 • e a') := by rw [(hε k).1, (hε k).2]
  have h2 : ε k (e a) (H.w0 • e a') + ε k (e a) (H.bar H.w0 • e a') = ε k (e a) (e a') := by
    rw [← map_add, ← add_smul, hw, one_smul]
  simp only [map_add, smul_add, LinearMap.add_apply, h1]
  rw [← h2]
  ring

set_option maxHeartbeats 1000000 in

theorem lattice_eq_id : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (∀ (x : 𝓞 E) (y : C.P.D.toPre.X), hD₂.xe (φ' (hD₁.xe.symm (x • y))) = x • hD₂.xe (φ' (hD₁.xe.symm y))) → (∀ p₀ : QkPt C.P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M') (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → ∀ y : C.P.D.toPre.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y := by
  intro E _ _ _ H Dw l Xo c φ hpq hφ hns R _ _ _ hR C Cn V _ _ _ _ hVc f₁ f₂ hf₁ hf₂ lf₁ lf₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b ph hE₁ hE₂
    hM hlin hpairs
  letI := H.starRing
  have hn : 3 ≤ l.M' := l.three_le.trans (Nat.le_of_dvd (Nat.lcm_pos (by have := l.three_le; omega) l.A_pos)
    (Nat.dvd_lcm_left _ _))
  have hn1 : 1 ≤ l.M' := by omega
  set iw := Cn.ψ.comp MvPolynomial.C with hiwd
  have hiw : Function.Injective iw := by
    have hfl : iw.Flat := RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 inferInstance) Cn.compl.2.2.1
    letI := iw.toAlgebra
    have : Module.Flat Cn.L.W R := hfl
    have : IsLocalHom (algebraMap Cn.L.W R) := Cn.ψ_loc
    have : Module.FaithfullyFlat Cn.L.W R := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact FaithfulSMul.algebraMap_injective Cn.L.W R
  let s : Fin C.m ⊕ Fin Cn.N → R := fun k => Cn.ψ (MvPolynomial.X k)
  have hs0 : ∀ k, s k ≠ 0 := by
    rintro (k | k)
    · exact (Cn.bd k).trans_ne (C.s_ne_zero k)
    · exact (Cn.tor k).ne_zero
  obtain ⟨hev, hbi, hgen, -⟩ := GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws Cn.L.W Cn.L.D (𝓞 E) Cn.L.oa H.w0 l.M' Cn.L.even Cn.L.bimult Cn.L.w0 Cn.L.gen
  obtain ⟨T, ib, β₀, ββ₀, w₀, hF₀⟩ := GlobalTheory.T.exists_tautologicalBase_nsmul_degenerationData Cn.L.b Cn.L.D Cn.L.bimult Cn.L.gen l.M'
  obtain ⟨g, hD, hg, hxe, -⟩ := Cn.data
  let ε : Fin C.m ⊕ Fin Cn.N → LinearMap.BilinForm ℤ (Fin T.r → ℤ) := fun k =>
    (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X).compl₁₂ ib.symm.toIntLinearEquiv.toLinearMap ib.symm.toIntLinearEquiv.toLinearMap
  have hε : ∀ k a b, ε k (ib a) (ib b) = (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) a b := fun k a b =>
    congrArg₂ (fun x y => (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) x y) (ib.symm_apply_apply a) (ib.symm_apply_apply b)
  let e : C.P.D.toPre.X ≃+ (Fin T.r → ℤ) := Cn.e.toAddEquiv.trans ib
  have he : ∀ y, e y = ib (Cn.e y) := fun _ => rfl
  obtain ⟨β, ββ, w, hF⟩ := GlobalTheory.T.comesFromTautBase_of_rescaled_pullback_monomial T l.M' (mulDeg Cn.L.D l.M') hev hbi hgen ib β₀ ββ₀ w₀ hF₀ R iw hiw C.P.D.toPre g hD
    s ε e (fun y => congrArg ib (hxe y).symm) (fun a a' => by
      simp only [he, hε]
      exact second_diff_bal Cn.e _ (fun k => (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 (hs0 k)) _
        (fun k => (Cn.ε k).2) _ g hg a a')
  obtain ⟨ββ₁, w₁, hF₁⟩ := GlobalTheory.TInj.from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₁ D₁.toPre hD₁ hf₁ hF
  obtain ⟨ββ₂, w₂, hF₂⟩ := GlobalTheory.TInj.from_pull T ε l.M' R V _ C.P.D iw s e β ββ w f₂ D₂.toPre hD₂ hf₂ hF

  let ga : C.P.D.toPre.X ≃ₗ[𝓞 E] C.P.D.toPre.X :=
    { (hD₁.xe.symm.trans ph).trans hD₂.xe with map_smul' := hlin }
  have hga : ∀ y, ga y = hD₂.xe (ph (hD₁.xe.symm y)) := fun _ => rfl

  have hcong : ∀ y, ∃ z, ga y = y + l.M' • z := by
    intro y
    obtain ⟨p₀, hp₀y, -⟩ := GlobalTheory.TInj.exists_qkPt_tautPt T ε l.M' R C.P.D.toPre iw s e β ββ w C.P.D.tau_bimult hF hs0
      (AlgebraicClosure (FractionRing R)) (e y)
    obtain ⟨p₁, p₂, hy₁, -, hy₂, -, p', hp', -, z, hz, -⟩ := hpairs p₀
    rw [hp₀y, AddEquiv.symm_apply_apply] at hy₁ hy₂
    have h : hD₂.xe p₂.y = hD₂.xe (ph p₁.y) + l.M' • hD₂.xe z := by rw [hz, map_add, hp', map_nsmul]
    rw [hy₂, hy₁, AddEquiv.apply_symm_apply] at h
    refine ⟨-(hD₂.xe z), ?_⟩
    rw [smul_neg, hga, ← sub_eq_add_neg, eq_sub_iff_add_eq]
    exact h.symm

  have hbd : ∀ f : R →+* V, Function.Injective f → IsLocalHom f → ∀ k, f (s (.inl k)) ∈ maximalIdeal V ∧ f (s (.inl k)) ≠ 0 :=
    fun f hf hl k => ⟨map_nonunit f _ (show Cn.ψ _ ∈ maximalIdeal R from (Cn.bd k).symm ▸ C.s_mem k),
      (map_ne_zero_iff f hf).2 (hs0 _)⟩
  have hpu := GlobalTheory.T.tautologicalBase_matching_monomials_ratio_unit T ε l.M' V D₁.toPre D₂.toPre _ _ _ _ ββ₁ w₁ _ _ _ _ ββ₂ w₂ b ph _ D₁.tau_bimult D₂.tau_bimult
    hF₁ hF₂ hM
  let gz : (Fin T.r → ℤ) ≃ₗ[ℤ] (Fin T.r → ℤ) := ((e.symm.trans ga.toAddEquiv).trans e).toIntLinearEquiv
  have hgz : ∀ y, gz (e y) = e (ga y) := fun y => by
    show e (ga (e.symm (e y))) = e (ga y)
    rw [AddEquiv.symm_apply_apply]
  obtain ⟨d₁, d₂, hd₁, hd₂, hsum⟩ := GlobalTheory.T.monomials_differ_by_units_positive_boundaryCombination V T.r C.m Cn.N l.M' hn1 ε (fun k => f₁ (s k)) (fun k => f₂ (s k))
    gz (hbd f₁ hf₁ lf₁) (fun k => (Cn.tor k).map f₁) (hbd f₂ hf₂ lf₂)
    (fun k => (Cn.tor k).map f₂) (fun a a' => by
      obtain ⟨u, hu⟩ := hpu (hD₁.xe.symm (e.symm a)) (hD₁.xe.symm (e.symm a'))
      simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply] at hu
      exact ⟨u, hu⟩)
  have hδ : ∀ k a a', C.δ k a a' = ε (.inl k) (e a) (e a') := fun k a a' => by rw [he, he, hε, Cn.cone]; rfl
  have hform : ∀ y z, ∑ i, (d₂ i : ℤ) * C.δ i (ga y) (ga z) = ∑ i, (d₁ i : ℤ) * C.δ i y z := by
    intro y z
    have h := LinearMap.congr_fun₂ hsum (e y) (e z)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, pull_apply, LinearEquiv.coe_coe, hgz, nsmul_eq_mul] at h
    simp only [hδ]
    exact h.symm
  have hpos : ∀ y, y ≠ 0 → 0 < ∑ i, C.δ i y y := by
    intro y hy
    obtain ⟨i, hi⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hy
    have hi' : 0 < C.δ i y y :=
      (mul_pos_iff_of_pos_left (show (0 : ℤ) < l.M' by exact_mod_cast (by omega : 0 < l.M'))).1 hi
    exact Finset.sum_pos' (fun j _ => C.cone.nonneg j y) ⟨i, Finset.mem_univ _, hi'⟩
  have hid := GlobalTheory.UCanon.eq_self_of_cone_congMod H φ (min Dw.p Dw.q) hφ hns C.P.D.toPre.X C.rank C.m C.δ C.cone hpos ga
    d₂ d₁ hd₂ hd₁ hform l.M' hn hcong
  intro y
  exact hid y

end GlobalTheory.UCanon.LatId
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyPeriodsInCoordinates
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.PerCoord

theorem comp_C_injective {W R σ : Type} [CommRing W] [IsLocalRing W] [CommRing R] [IsLocalRing R]
    (ψ : MvPolynomial σ W →+* R) (hf : ψ.Flat) (hl : IsLocalHom (ψ.comp MvPolynomial.C)) :
    Function.Injective (ψ.comp MvPolynomial.C) := by
  have hC : (MvPolynomial.C : W →+* MvPolynomial σ W).Flat := by
    show (algebraMap W (MvPolynomial σ W)).Flat
    rw [RingHom.flat_algebraMap_iff]
    infer_instance
  have h := RingHom.Flat.comp hC hf
  letI := (ψ.comp MvPolynomial.C).toAlgebra
  haveI : Module.Flat W R := h
  haveI : IsLocalHom (algebraMap W R) := hl
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := W) (B := R)
  exact FaithfulSMul.algebraMap_injective W R

theorem prod_zpow_add {K Ix : Type} [Field K] [Fintype Ix] (c : Ix → K) (hc : ∀ k, c k ≠ 0) (A B C D : Ix → ℤ)
    (h : ∀ k, A k = D k + B k + C k) :
    ∏ k, c k ^ A k = (∏ k, c k ^ D k) * (∏ k, c k ^ B k) * ∏ k, c k ^ C k := by
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [h k, zpow_add₀ (hc k), zpow_add₀ (hc k)]

end GlobalTheory.UCanon.PerCoord

namespace GlobalTheory.UCanon.PerCoord

theorem second_diff {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) {X Y : Type} [AddCommGroup X]
    [Module (𝓞 E) X] [AddCommGroup Y] [Module (𝓞 E) Y] (e : X ≃ₗ[𝓞 E] Y) {β : LinearMap.BilinForm ℤ Y}
    (hβ : β ∈ balForms H.bar Y) (a b : X) :
    β (e (a + b)) (H.w0 • e (a + b)) = β (e a) (e b) + β (e a) (H.w0 • e a) + β (e b) (H.w0 • e b) := by
  have h1 : β (e b) (H.w0 • e a) = β (e a) (H.bar H.w0 • e b) := (hβ.1 _ _).trans (hβ.2 _ _ _)
  have h2 : β (e a) (H.w0 • e b) + β (e a) (H.bar H.w0 • e b) = β (e a) (e b) := by
    rw [← map_add, ← add_smul, ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.cmHostUnit_add_conj_eq_one, one_smul]
  simp only [map_add, smul_add, LinearMap.add_apply]
  rw [h1]
  linarith

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C), ∃ (ε' : Module.Basis (Fin C.m ⊕ Fin Cn.N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre), (∀ k, (ε' k : LinearMap.BilinForm ℤ C.P.D.toPre.X) = pull Cn.e.toLinearMap (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X)) ∧ FromBase C.P.D.toPre τ₀ (Cn.ψ.comp MvPolynomial.C) ∧ TauIn C.P.D.toPre τ₀ (fun k => Cn.ψ (MvPolynomial.X (finSumFinEquiv.symm k))) (fun k => (l.M' : ℤ) • (ε' (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X)) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C Cn
  classical
  obtain ⟨g, hD, hg, -, -⟩ := Cn.data
  have hinj := comp_C_injective Cn.ψ Cn.compl.2.2.1 Cn.ψ_loc
  obtain ⟨-, hb, hU, -⟩ := letI := H.starRing
    GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws Cn.L.W Cn.L.D (𝓞 E) Cn.L.oa H.w0 l.M' Cn.L.even Cn.L.bimult Cn.L.w0 Cn.L.gen
  obtain ⟨τ₁, hτ, hF⟩ := GlobalTheory.UTautData.gens_fromBase _ hinj _ _ hD hb hU
  refine ⟨Cn.ε.map (pullBalEquiv H.bar Cn.e), τ₁, fun k => rfl, hF, fun a b => ?_⟩
  have hs : ∀ k, algebraMap R (FractionRing R) (Cn.ψ (MvPolynomial.X k)) ≠ 0 := by
    intro k
    refine (map_ne_zero_iff _ (IsFractionRing.injective R _)).2 ?_
    rcases k with i | k
    · rw [Cn.bd i]; exact C.s_ne_zero i
    · exact (Cn.tor k).ne_zero
  refine ⟨(hτ a b).1, g a * g b * (g (a + b))⁻¹, ?_, fun z J hJ => ?_⟩
  · have hsplit := prod_zpow_add _ hs
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e (a + b)) (H.w0 • Cn.e (a + b)))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e a) (H.w0 • Cn.e a))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e b) (H.w0 • Cn.e b))
      (fun k => (l.M' : ℤ) * (Cn.ε k : LinearMap.BilinForm ℤ Cn.L.D.X) (Cn.e a) (Cn.e b))
      (fun k => by simp only [second_diff H Cn.e (Cn.ε k).2 a b]; ring)
    have hne : ∀ y, (((g y)⁻¹ : (FractionRing R)ˣ) : FractionRing R) ≠ 0 := fun y => Units.ne_zero _
    have e1 : (((g a * g b * (g (a + b))⁻¹ : (FractionRing R)ˣ)) : FractionRing R) =
        (((g (a + b))⁻¹ : (FractionRing R)ˣ) : FractionRing R) * ((((g a)⁻¹ : (FractionRing R)ˣ) : FractionRing R))⁻¹ *
          ((((g b)⁻¹ : (FractionRing R)ˣ) : FractionRing R))⁻¹ := by
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, inv_inv]; ring
    have hA := hne a
    have hB := hne b
    rw [hg a] at hA
    rw [hg b] at hB
    rw [e1, hg (a + b), hsplit, hg a, hg b]
    beta_reduce at hA hB ⊢
    have canc : ∀ T x y : FractionRing R, x ≠ 0 → y ≠ 0 → T * x * y * x⁻¹ * y⁻¹ = T := fun T x y hx hy => by
      field_simp
    rw [canc _ _ _ hA hB]
    refine Eq.trans ?_ (Equiv.prod_comp finSumFinEquiv.symm (fun k => algebraMap R (FractionRing R)
      (Cn.ψ (MvPolynomial.X k)) ^ (((l.M' : ℤ) • ((Cn.ε.map (pullBalEquiv H.bar Cn.e)) k :
        LinearMap.BilinForm ℤ C.P.D.toPre.X)) a b))).symm
    exact Finset.prod_congr rfl fun k _ => rfl
  · have h1 := GlobalTheory.TauTwist.val_tau_rescale (D := C.P.D.toPre) g (a := a) (b := b)
      (x := (g a * g b)⁻¹ * g (a + b)) (by group) (𝟙 _) hJ
    have h2 := (hτ a b).2 z J hJ
    have hx : g a * g b * (g (a + b))⁻¹ = ((g a * g b)⁻¹ * g (a + b))⁻¹ := by
      rw [mul_inv_rev, inv_inv, mul_comm]
    rw [hx]
    show _ = GlobalTheory.TauTwist.unitAt (𝟙 _) z _ * _
    rw [map_inv]
    exact eq_inv_mul_of_mul_eq (h1.symm.trans h2)

end GlobalTheory.UCanon.PerCoord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalModificationWeightBoundStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.Vanishing.H0
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonical_modification_weight_bound : GlobalTheory.CovTop.Hypotheses₂ → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed Xo c → ∀ (M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw)) (ω : CanId M) (b s : AllWt.Weight Dw), FlagTan.kap Dw + b = s → vanBd TF.X Z s ≤ space TF.X Z U s → ∃ F : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤ → Cusp Z U s, ∀ (z : M.X) (hz : z ∈ M.off) (j : (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).ι) (hj : z ∈ (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)).U j) (i : (L₀ TF.X Z s).ι) (hi : M.σ z ∈ (L₀ TF.X Z s).U i), ∃ u : (M.X.presheaf.stalk z)ˣ, ∀ g : H0 M.str (tens M.K.bundle ((L₀ TF.X Z b).pull M.σ)) ⊤, germ j z (memTop z) hj g = u.val * (M.σ.stalkMap z).hom (germ i (M.σ z) (M.off_eq.le hz) hi (cuspSec TF.X Z U s (F g))) := by
  first | exact @GlobalTheory.CuspTransfer.exists_cusp_germ | exact GlobalTheory.CuspTransfer.exists_cusp_germ | (intros; apply GlobalTheory.CuspTransfer.exists_cusp_germ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsClassifyMarkedPeriodsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPoints_classify_markedPeriods : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (M : Model b N) h hL, 0 < N → N.Coprime p → b.IsType σ ρ → FineAt (M.univ.fam h hL) σ ρ N (D.Cls N) := by
  first | (exact @GlobalTheory.UPel.HT.Model.fineAt_univ) | (exact GlobalTheory.UPel.HT.Model.fineAt_univ) | (intros; apply GlobalTheory.UPel.HT.Model.fineAt_univ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectionClosedFibreEqDerivationIdentificationStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connection_closedFibre_eq_derivation_identification : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (ed : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj ed pb → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) ∧ ∃ κ : (DualNumber k)ˣ, ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val * (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)) := by
  first | exact @GlobalTheory.HeatConn.connK_eq_ident | exact GlobalTheory.HeatConn.connK_eq_ident | (intros; apply GlobalTheory.HeatConn.connK_eq_ident <;> assumption)
end

