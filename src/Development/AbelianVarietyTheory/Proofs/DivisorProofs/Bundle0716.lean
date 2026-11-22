import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLoc
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0692
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0679
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0686
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0693
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0696
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0709
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0708
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0694
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0695
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLeviNonnegOfChartPlurisubharmonic
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem etale_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i φ x ξ) → LeviNonneg n (fun y : U => z y) (fun y : U => φ y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE φ hφ
  unfold LeviNonneg
  intro x ξ
  have hloc := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  obtain ⟨e, he, hx⟩ := exists_chart n (fun y : U => z y) hloc x
  obtain ⟨i, hxi, hsm, hpos⟩ := hφ x.1 x.2
  have hzx : z x = e x := he hx
  have hv : e x ∈ e.target := e.map_source hx
  have hsx : e.symm (e x) = x := e.left_inv hx
  obtain ⟨hG, hev, -⟩ := GlobalTheory.T.contDiffAt_chart_inverse_of_etale n Y ι La A U z hE e he (e x) hv i (by rw [hsx]; exact hxi)
  rw [levi_eq_leviV n _ e he _ x hx ξ]
  show 0 ≤ (leviV n (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) (z x) ξ).re
  rw [hzx]

  have heq : (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) =ᶠ[𝓝 (e x)]
      (fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ)) ∘ (fun v' => A.chart i (e.symm v' : Y)) := by
    filter_upwards [hev] with v' hv'
    simp only [Function.comp_apply, (A.chart i).left_inv hv']
  have hcongr : leviV n (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) (e x) ξ =
      leviV n ((fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ)) ∘
        (fun v' => A.chart i (e.symm v' : Y))) (e x) ξ := by
    unfold leviV
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    congr 2
    apply wd_congr
    filter_upwards [heq.eventuallyEq_nhds] with y hy
    exact ReciprocityTheory.L2DbarEstimates.wdb_congr hy
  have hU : ContDiffAt ℝ 2 (fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ))
      ((fun v' => A.chart i (e.symm v' : Y)) (e x)) := by
    simp only [hsx]
    exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ hsm).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [hcongr, flA_leviV_comp hU (hG.of_le (WithTop.coe_le_coe.mpr le_top)) ξ]
  simp only [hsx]
  exact hpos _

end GlobalTheory.OTY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtFnEqValAt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AnPer

theorem evalAt_fn_eq_valAt' {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) {X : Scheme.{0}}
    (x : Sp (Hol W) ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) (p : E) (hp : p ∈ W) :
    ⊤ ≤ (spMap (Hol.ev p hp).toRingHom ≫ x) ⁻¹ᵁ U ∧
      (evalAt x U h f).fn p = valAt' (spMap (Hol.ev p hp).toRingHom ≫ x) U f := by
  set φ : Hol W →+* ℂ := (Hol.ev p hp).toRingHom
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun q _ ↦ h (Set.mem_univ ((spMap φ) q))
  refine ⟨h', ?_⟩
  have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom =
      x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of (Hol W))).hom ≫ CommRingCat.ofHom φ := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
      ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
    congr 2
  have e2 := congrArg (fun t ↦ t.hom f) e
  rw [valAt', dif_pos h', valAt, ← Hol.ev_apply p hp]
  exact e2.symm

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalAtNatural
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EvalNat

theorem evalAt_natural : ∀ {X : Scheme.{0}} {C C' : Type} [CommRing C] [CommRing C'] (φ : C →+* C') (x : Sp C ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U), ∃ h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U, (∀ f : Γ(X, U), evalAt (spMap φ ≫ x) U h' f = φ (evalAt x U h f)) ∧ ∀ (U' : X.Opens) (i : U ≤ U') (h'' : ⊤ ≤ x ⁻¹ᵁ U') (f : Γ(X, U')), evalAt x U' h'' f = evalAt x U h ((X.presheaf.map (homOfLE i).op).hom f) := by
  intro X C C' _ _ φ x U h
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ ↦ h (Set.mem_univ ((spMap φ) p))
  refine ⟨h', fun f ↦ ?_, fun U' i h'' f ↦ ?_⟩
  · have e : (spMap φ ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C')).hom =
        x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom ≫ CommRingCat.ofHom φ := by
      rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc,
        ← Scheme.Hom.appLE_comp_appLE (spMap φ) x U ⊤ ⊤ h le_rfl]
      congr 2
    exact congrArg (fun t ↦ t.hom f) e
  · have e : x.appLE U' ⊤ h'' = X.presheaf.map (homOfLE i).op ≫ x.appLE U ⊤ h := by
      rw [Scheme.Hom.map_appLE]
    unfold evalAt
    rw [e]
    rfl

end GlobalTheory.EvalNat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalSwapEq
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.CommSwap

theorem eval_swap_eq : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] [Coalgebra.IsCocomm O A] [IsAdicComplete (Ideal.span {(p : A ⊗[O] A)}) (A ⊗[O] A)] {d : ℕ} (x : Fin d → A) (E₂ : MvPowerSeries (Fin d ⊕ Fin d) O →ₐ[O] A ⊗[O] A) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), (∀ i, ∃ N : ℕ, (p : A) ∣ x i ^ N) → IsEval p (Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i) E₂ → (∀ i, E₂ (μ i) = Coalgebra.comul (R := O) (x i)) → ∀ i, E₂ (swap (μ i)) = E₂ (μ i) := by
  intro p O A _ _ _ _ _ d x E₂ μ hnil hE hμ i
  set y : Fin d ⊕ Fin d → A ⊗[O] A := Sum.elim (fun i => x i ⊗ₜ[O] (1 : A)) fun i => (1 : A) ⊗ₜ[O] x i with hy
  have hny : ∀ j, ∃ N : ℕ, (p : A ⊗[O] A) ∣ y j ^ N := by
    intro j
    rcases j with j | j
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, a ⊗ₜ[O] 1, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeLeftRingHom (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeLeftRingHom_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inl, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
    · obtain ⟨N, a, ha⟩ := hnil j
      refine ⟨N, 1 ⊗ₜ[O] a, ?_⟩
      have h1 := map_mul (Algebra.TensorProduct.includeRight (R := O) (A := A) (B := A)) (p : A) a
      simp only [Algebra.TensorProduct.includeRight_apply, map_natCast] at h1
      simp only [hy, Sum.elim_inr, Algebra.TensorProduct.tmul_pow, one_pow, ha, h1]
  set T := (Algebra.TensorProduct.comm O A A).toAlgHom
  set E' := T.comp E₂
  set u : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) O :=
    Sum.elim (fun i => X (Sum.inr i)) (fun i => X (Sum.inl i)) with hu
  have hu0 : ∀ j, constantCoeff (u j) = 0 := by
    intro j; rcases j with j | j <;> simp [hu]
  have hE' : IsEval p (fun j => E₂ (u j)) E' := by
    refine ⟨?_, ?_⟩
    · intro j
      rcases j with j | j
      · simp [E', T, hu, hE.1, hy]
      · simp [E', T, hu, hE.1, hy]
    · intro m
      obtain ⟨N, hN⟩ := hE.2 m
      refine ⟨N, fun f hf => ?_⟩
      obtain ⟨c, hc⟩ := hN f hf
      refine ⟨T c, ?_⟩
      simp [E', hc, map_mul, map_pow, map_natCast]
  have key := ((GlobalTheory.CEval.continuous_eval p O (A ⊗[O] A) (Fin d ⊕ Fin d) y hny).2 E₂ hE).1 (Fin d ⊕ Fin d) u E' hu0 hE' (μ i)
  have hs : swap (μ i) = subst u (μ i) := rfl
  rw [hs, key, hμ i]
  simp only [E', T, AlgHom.comp_apply, hμ i]
  exact Coalgebra.comm_comul (R := O) (x i)

end GlobalTheory.CommSwap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAinfSolutionOfApproxModPhiXiMu
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.WTop

theorem mulVec_add_mul {R ι : Type} [CommRing R] [Fintype ι] (N : Matrix ι ι R) (a b : ι → R) (s : R) (i : ι) :
    N.mulVec (fun j => a j + s * b j) i = N.mulVec a i + s * N.mulVec b i := by
  simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 1000000 in

theorem main : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (ι : Type) [Fintype ι] (N : Matrix ι ι (Ainf p O)) (v0 : ι → Ainf p O), IsNil (WittVector.fontaineTheta O p) WittVector.frobenius N → (∀ i, WittVector.frobenius (xi ε) * Sandwich.mu ε ∣ N.mulVec (fun j => WittVector.frobenius (v0 j)) i - WittVector.frobenius (xi ε) * v0 i) → ∃ w : ι → Ainf p O, (∀ i, Sandwich.mu ε ∣ w i - v0 i) ∧ ∀ i, WittVector.frobenius (xi ε) * w i = N.mulVec (fun j => WittVector.frobenius (w j)) i := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε ι _ N v0 hN h
  choose c hc using h
  obtain ⟨z, hz⟩ := (GlobalTheory.T.ainf_frobenius_semilinear_equation_existsUnique p C v O hv ε hε ι N hN).1 c
  refine ⟨fun i => v0 i + Sandwich.mu ε * z i, fun i => ⟨z i, by ring⟩, fun i => ?_⟩
  have hw : (fun j => WittVector.frobenius (v0 j + Sandwich.mu ε * z j)) =
      fun j => WittVector.frobenius (v0 j) +
        (WittVector.frobenius (xi ε) * Sandwich.mu ε) * WittVector.frobenius (z j) := by
    funext j
    rw [map_add, map_mul, GlobalTheory.WinLift.frob_mu]
  rw [hw, mulVec_add_mul]
  linear_combination (-1 : Ainf p O) * hc i + WittVector.frobenius (xi ε) * Sandwich.mu ε * hz i

end GlobalTheory.WTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCharSeries
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.FormalCalc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLog.Chart

variable {p : ℕ} {O : Type} [CommRing O] [IsHausdorff (Ideal.span {(p : O)}) O]
  {G : PDivGroup p O} {d : ℕ}

theorem res_ev (c : Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    G.res n (c.ev (n + 1) f) = c.ev n f := by
  haveI : IsHausdorff (Ideal.span {(p : G.A n)}) (G.A n) :=
    GlobalTheory.CEval.isHausdorff_of_projective (O := O) p
  have h := GlobalTheory.CEval.isEval_comp p (c.isEval (n + 1)) (G.res n : G.A (n + 1) →ₐ[O] G.A n)
  have h' : IsEval p (c.x n) ((G.res n : G.A (n + 1) →ₐ[O] G.A n).comp (c.ev (n + 1))) := by
    convert h using 2 with i
    exact (c.res n i).symm
  exact congrArg (fun E : MvPowerSeries (Fin d) O →ₐ[O] G.A n => E f)
    (GlobalTheory.CEval.eval_unique p (c.x n) _ _ h' (c.isEval n))

theorem counit_ev (c : Chart G d) (n : ℕ) (f : MvPowerSeries (Fin d) O) :
    Coalgebra.counit (R := O) (c.ev n f) = constantCoeff f := by
  let E₂ : MvPowerSeries (Fin d) O →ₐ[O] O :=
    { (constantCoeff : MvPowerSeries (Fin d) O →+* O) with
      commutes' := fun r => by
        show constantCoeff (algebraMap O (MvPowerSeries (Fin d) O) r) = r
        rw [← c_eq_algebraMap]; simp }
  have h := GlobalTheory.CEval.isEval_comp p (c.isEval n) (Bialgebra.counitAlgHom O (G.A n))
  have h₁ : IsEval p (fun _ : Fin d => (0 : O))
      ((Bialgebra.counitAlgHom O (G.A n)).comp (c.ev n)) := by
    convert h using 2 with i
    exact (c.aug n i).symm
  have h₂ : IsEval p (fun _ : Fin d => (0 : O)) E₂ := by
    refine ⟨fun i => by simp [E₂], fun m => ⟨1, fun g hg => ?_⟩⟩
    have : constantCoeff g = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply]
      exact hg 0 (by simp)
    show (p : O) ^ m ∣ constantCoeff g
    rw [this]
    exact dvd_zero _
  exact congrArg (fun E : MvPowerSeries (Fin d) O →ₐ[O] O => E f)
    (GlobalTheory.CEval.eval_unique p (fun _ => (0 : O)) _ _ h₁ h₂)

end GlobalTheory.QLog.Chart

namespace GlobalTheory.QLog

theorem exists_charSeries : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (χ : G.dual.Tate), ∃ u : MvPowerSeries (Fin d) O, constantCoeff u = 1 ∧ ∀ n, c.ev n u = charElem χ n := by
  intro p _ O _ _ _ G d c χ
  haveI : ∀ n, IsHausdorff (Ideal.span {(p : G.A n)}) (G.A n) := fun n =>
    GlobalTheory.CEval.isHausdorff_of_projective (O := O) p
  obtain ⟨u, hu⟩ := (GlobalTheory.Limits.exists_unique_of_compatible p O (Fin d) G.A
    (fun n => (G.res n : G.A (n + 1) →ₐ[O] G.A n)) c.x c.ev c.isEval
    (fun n f => c.res_ev n f) c.ker).2 c.surj (charElem χ) (fun n => res_charElem χ n)
  refine ⟨u, ?_, hu⟩
  rw [← c.counit_ev 0 u, hu 0]
  exact (isGroupLikeElem_charElem χ 0).counit_eq_one

end GlobalTheory.QLog
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesOfIsConnected
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open scoped TensorProduct

theorem GlobalTheory.PDivGroup.exists_coords_of_isConn : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ G : PDivGroup p O, IsConn G → ∃ (d : ℕ) (x : ∀ n, Fin d → G.A n) (ev : ∀ n, MvPowerSeries (Fin d) O →ₐ[O] G.A n), (∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N) ∧ (∀ n, IsEval p (x n) (ev n)) ∧ (∀ n i, G.res n (x (n + 1) i) = x n i) ∧ (∀ n i, Coalgebra.counit (R := O) (x n i) = 0) ∧ (∀ n, Function.Surjective (ev n)) ∧ ∀ m N : ℕ, ∃ n, ∀ f, ev n f = 0 → ∀ α : Fin d →₀ ℕ, α.degree < N → (p : O) ^ m ∣ coeff α f := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G hG
  obtain ⟨d, x, hcou, hres, hspan, hl⟩ := GlobalTheory.T.exists_compatible_pDivGroup_level_coordinates p C v O hv G
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  have hpm : (p : O) ∈ IsLocalRing.maximalIdeal O :=
    (IsLocalRing.mem_maximalIdeal _).2 (Fact.out : ¬IsUnit (p : O))
  have hmem : ∀ n i, ¬IsUnit (x n i) := by
    intro n i hu
    have h1 := hu.map (Bialgebra.counitAlgHom O (G.A n))
    rw [Bialgebra.counitAlgHom_apply, hcou n i] at h1
    exact not_isUnit_zero h1
  have hnil : ∀ n i, ∃ N : ℕ, (p : G.A n) ∣ x n i ^ N := fun n i => by
    haveI := hG n
    exact GlobalTheory.T.maximalIdeal_pow_natCast_dvd_finite_integers_algebra p hp0 C v O hv (G.A n) (x n i) ((IsLocalRing.mem_maximalIdeal _).2 (hmem n i))
  have hex : ∀ n, ∃ E : MvPowerSeries (Fin d) O →ₐ[O] G.A n, IsEval p (x n) E := fun n => by
    haveI := GlobalTheory.T.isAdicComplete_span_natCast_finite_projective_algebra p O (G.A n)
    exact ((GlobalTheory.T.padicContinuousEvaluation_existsUnique_subst_natural p O (G.A n) (Fin d) (x n) (hnil n)).1).exists
  choose ev hev using hex
  have hpoly : ∀ n (P : MvPolynomial (Fin d) O),
      ev n (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval (x n) P := by
    intro n P
    have h : (ev n).comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval (x n) :=
      MvPolynomial.algHom_ext fun i => by
        simp [MvPolynomial.coeToMvPowerSeries.algHom_apply, (hev n).1 i]
    exact DFunLike.congr_fun h P
  refine ⟨d, x, ev, hnil, hev, hres, hcou, fun n => ?_, fun m N => ?_⟩
  · haveI := hG n
    intro a
    obtain ⟨P, hP⟩ := GlobalTheory.T.aeval_surjective_of_cotangent_span_top O (G.A n) (p : O) hpm (Bialgebra.counitAlgHom O (G.A n)) d (x n)
      (fun i => by rw [Bialgebra.counitAlgHom_apply]; exact hcou n i)
      (fun i => by simpa [map_natCast] using hnil n i) (hspan n) a
    exact ⟨P, (hpoly n P).trans hP⟩
  · obtain ⟨K, hK0, hK⟩ := GlobalTheory.T.coeff_annihilated_of_aeval_mem_ker_pow d N
    obtain ⟨e, u, hu, hKu⟩ := Nat.exists_eq_pow_mul_and_not_dvd hK0.ne' p (Fact.out : p.Prime).ne_one
    refine ⟨m + e, fun f hf α hα => ?_⟩
    obtain ⟨P, hPdeg, hPco, hPmem⟩ := GlobalTheory.T.exists_truncation_congr_of_padicContinuousEval_eq_zero p O (G.A (m + e)) d (x (m + e)) (ev (m + e)) (hev _) (m + e) N f hf
    obtain ⟨l, hlx⟩ := hl (m + e)
    let I : Ideal O := Ideal.span {(p : O) ^ (m + e)}
    let l' : Fin d → (G.A (m + e) →ₗ[O] O ⧸ I) :=
      fun i => l i ∘ₗ AugCot.d (Bialgebra.counitAlgHom O (G.A (m + e)))
    obtain ⟨D, hD⟩ := GlobalTheory.T.exists_invariant_derivations_quotient_bialgebra O (G.A (m + e)) I d l' (fun i a b => by
      simp only [l', LinearMap.comp_apply, AugCot.d_mul, map_add, map_smul, Bialgebra.counitAlgHom_apply])
    let φ : G.A (m + e) →ₐ[O] (O ⧸ I) ⊗[O] G.A (m + e) := Algebra.TensorProduct.includeRight
    have hy0 : ∀ j, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) (φ (x (m + e) j)) = 0 := by
      intro j
      simp [φ, Algebra.TensorProduct.includeRight_apply, TensorProduct.counit_tmul, hcou]
    have hDy : ∀ i j, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) (D i (φ (x (m + e) j))) =
        if i = j then 1 else 0 := fun i j => (hD i _).trans (hlx i j)
    have hdeg : ∀ β : Fin d →₀ ℕ, N ≤ β.degree →
        MvPolynomial.coeff β (MvPolynomial.map (algebraMap O (O ⧸ I)) P) = 0 := fun β hβ => by
      rw [MvPolynomial.coeff_map, hPdeg β hβ, map_zero]
    have hmemB : MvPolynomial.aeval (fun j => φ (x (m + e) j)) (MvPolynomial.map (algebraMap O (O ⧸ I)) P) ∈
        RingHom.ker (Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e))) ^ N := by
      rw [MvPolynomial.aeval_map_algebraMap, ← MvPolynomial.comp_aeval, AlgHom.comp_apply]
      refine (Ideal.map_le_iff_le_comap.1 ?_) hPmem
      rw [Ideal.map_sup, Ideal.map_pow, Ideal.map_span, Ideal.map_span]
      refine sup_le (Ideal.pow_right_mono ?_ N) ?_
      · rw [Ideal.span_le]
        rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
        exact hy0 j
      · rw [Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
        have h0 : φ ((p : G.A (m + e)) ^ (m + e)) = 0 := by
          rw [map_pow, map_natCast]
          have h1 : ((p : (O ⧸ I) ⊗[O] G.A (m + e))) ^ (m + e) =
              algebraMap (O ⧸ I) _ (Ideal.Quotient.mk I ((p : O) ^ (m + e))) := by
            rw [map_pow, map_pow, map_natCast, map_natCast]
          rw [h1, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _), map_zero]
        rw [SetLike.mem_coe, h0]
        exact zero_mem _
    have key := hK (O ⧸ I) ((O ⧸ I) ⊗[O] G.A (m + e)) _ _ D hy0 hDy _ hdeg hmemB α
    rw [MvPolynomial.coeff_map, ← map_natCast (algebraMap O (O ⧸ I)), ← map_mul,
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at key
    rw [← hPco α hα]
    have hpO : (p : O) ≠ 0 := by
      intro h
      have h2 := congrArg (algebraMap O C) h
      rw [map_natCast, map_zero] at h2
      exact hp0 (by exact_mod_cast h2)
    have hunit : IsUnit (u : O) := by
      by_contra hnu
      have hcop : IsCoprime (u : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.2
        ((Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (Fact.out : p.Prime)).2 hu)))
      obtain ⟨a, b, hab⟩ := hcop.map (Int.castRingHom O)
      have h3 : a * Int.castRingHom O u + b * Int.castRingHom O p ∈ IsLocalRing.maximalIdeal O := by
        refine add_mem (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
        · simpa using (IsLocalRing.mem_maximalIdeal _).2 hnu
        · simpa using hpm
      rw [hab] at h3
      exact (IsLocalRing.maximalIdeal.isMaximal O).ne_top ((Ideal.eq_top_iff_one _).2 h3)
    rw [hKu, Nat.cast_mul, Nat.cast_pow, pow_add, mul_assoc, mul_comm ((p : O) ^ m)] at key
    have key2 := (mul_dvd_mul_iff_left (pow_ne_zero e hpO)).1 key
    exact (hunit.dvd_mul_left).1 key2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePrimesOverPrimeCoprimalityEquiv
section
open NumberField Module Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.IndefiniteRowSideFullHecke.ZetaValueIdeals GlobalTheory.ZetaDenom
open scoped nonZeroDivisors

namespace GlobalTheory.PrimesOverL

theorem primes_over_l : ∀ {F : Type} [Field F] [NumberField F] (l : ℕ), l.Prime →
    ∃ P : Finset (Ideal (𝓞 F)), (∀ 𝔭 ∈ P, 𝔭.IsMaximal ∧ 𝔭 ≠ ⊥ ∧ l ∣ Ideal.absNorm 𝔭) ∧
      ∀ I : Ideal (𝓞 F), CoprimeTo F (∏ 𝔭 ∈ P, 𝔭) I ↔ CoprimeTo F (Ideal.span {(l : 𝓞 F)}) I := by
  first
  | exact @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above
  | exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above
  | (apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimesAboveExistence.exists_primes_above <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimesAboveExistence.exists_primes_above ..)

end GlobalTheory.PrimesOverL
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFirstOrderJetAlgHom
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnPer.Hol

def jet {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {p : E} (hp : p ∈ W) (v : E) :
    Hol W →ₐ[ℂ] DualNumber ℂ where
  toFun h := TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h))
  map_one' := by
    ext <;> simp
  map_mul' f g := by
    ext
    · simp
    · simp [Derivation.leibniz]; ring
  map_zero' := by
    ext <;> simp
  map_add' f g := by
    ext <;> simp <;> ring
  commutes' c := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem jet_spec {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {W : Opens E} {p : E} (hp : p ∈ W)
    (v : E) (h : Hol W) : (jet hp v h).fst = h.fn p ∧ (jet hp v h).snd = fderiv ℂ h.fn p v := by
  constructor
  · change (TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h)) : DualNumber ℂ).fst = _
    simp [ev_apply]
  · change (TrivSqZeroExt.inl (ev p hp h) + TrivSqZeroExt.inr (ev p hp (der v h)) : DualNumber ℂ).snd = _
    simp [ev_apply, fn_der v h hp]

end GlobalTheory.AnPer.Hol

theorem GlobalTheory.AnPer.Hol.exists_jet_algHom : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (W : Opens E) (p : E), p ∈ W → ∀ v : E, ∃ ρ : Hol W →ₐ[ℂ] DualNumber ℂ, ∀ h, (ρ h).fst = h.fn p ∧ (ρ h).snd = fderiv ℂ h.fn p v := by
  intro E _ _ W p hp v
  exact ⟨GlobalTheory.AnPer.Hol.jet hp v, GlobalTheory.AnPer.Hol.jet_spec hp v⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLiftOfSurjectiveStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalGroupLawLift_of_surjective : ∀ (B O : Type) [CommRing B] [CommRing O] (θ : B →+* O), Function.Surjective θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∃ μ' : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B, IsLift θ μ' ∧ ∀ i, map θ (μ' i) = μ i := by
  first | exact @GlobalTheory.LiftLaw.exists_isLift | exact GlobalTheory.LiftLaw.exists_isLift | (intros; apply GlobalTheory.LiftLaw.exists_isLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralCoboundaryOneCongrFrobeniusStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_coboundaryOne_congr_frobenius : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ (c : MvPowerSeries (Fin d ⊕ Fin d) O) (t : MvPowerSeries (Fin d) O), (∀ α : Fin d →₀ ℕ, (∃ i, ¬ p ∣ α i) → ¬IsUnit (coeff α t)) → (∀ β : Fin d ⊕ Fin d →₀ ℕ, ¬IsUnit (coeff (p • β) (cob1 μ t) - coeff β c ^ p)) → ∃ u : MvPowerSeries (Fin d) O, ∀ α, ¬IsUnit (coeff α c - coeff α (cob1 μ u)) := by
  first | exact @GlobalTheory.SmallSecondRoot.exists_integral_cob1_congr_of_frobenius_congr | exact GlobalTheory.SmallSecondRoot.exists_integral_cob1_congr_of_frobenius_congr | (intros; apply GlobalTheory.SmallSecondRoot.exists_integral_cob1_congr_of_frobenius_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPerfectPartAlgHomFiniteAlgebraStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_perfectPart_algHom_finiteAlgebra : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (A : Type) [CommRing A] [Algebra k A] [Module.Finite k A], ∃ π : A →ₐ[k] A, ((∀ a : A, IsNilpotent (a - π a)) ∧ ∀ a : A, ∃ b : A, π a = π b ^ p) := by
  first | exact @GlobalTheory.exists_perfectPart_algHom | exact GlobalTheory.exists_perfectPart_algHom | (intros; apply GlobalTheory.exists_perfectPart_algHom <;> assumption)
end

