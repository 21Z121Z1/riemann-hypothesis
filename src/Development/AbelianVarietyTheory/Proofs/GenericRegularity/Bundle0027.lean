import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.MatrixTwoByTwoCongr
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0026
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0023
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0017
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0015
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0002
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.RigFrame
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0009
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFiniteIntegralChartCoverFlagSpace
section
noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem MChart.Lift.exists_coordinates (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (M : MChart Y) (L : Type) [Field L] [Algebra c.F L] (f : Γ(Y.X, M.U) →+* L) (y : FrPt Xo c L)
    (Λ : M.Lift f y.x) :
    ∃ g : ∀ τ : E →+* ℂ, Matrix (Fin M.n) (Fin (Dw.mult τ)) L,
      Λ.LieTie g y.u ∧ ∀ τ, LinearIndependent L (g τ).transpose := by
  classical
  have hb := vec_bijective E H Dw l Xo c O β Y M L f y.x Λ
  have hc := GlobalTheory.T.isCombAt_iff_coordinate_combination E H Dw l Xo c O β Y M L f y.x Λ
  choose cv hcv using fun τ i => (hb.2.2 (y.u τ i) (y.4 τ i)).exists
  refine ⟨fun τ j i => cv τ i j, fun τ i => hcv τ i, fun τ => ?_⟩
  refine Fintype.linearIndependent_iff.2 fun a ha k => ?_
  have ha' : ∑ i, a i • cv τ i = 0 := ha
  have s1 : ∑ i, ((Pi.single k (1 : L) : Fin (Dw.mult τ) → L) + a) i • cv τ i = cv τ k := by
    simp [Pi.single_apply, add_smul, Finset.sum_add_distrib, ha']
  have s2 : ∑ i, (Pi.single k (1 : L) : Fin (Dw.mult τ) → L) i • cv τ i = cv τ k := by
    simp [Pi.single_apply]
  have e1 : IsCombAt y.x (y.u τ) (Pi.single k 1 + a) (y.u τ k) :=
    (hc _ (cv τ) (y.u τ) _ (y.u τ k) (hcv τ)).2 (by rw [s1]; exact hcv τ k)
  have e2 : IsCombAt y.x (y.u τ) (Pi.single k 1) (y.u τ k) :=
    (hc _ (cv τ) (y.u τ) _ (y.u τ k) (hcv τ)).2 (by rw [s2]; exact hcv τ k)
  have h := (y.6 τ (y.u τ k) (y.4 τ k) (y.5 τ k)).unique e1 e2
  simpa using congrFun h k

private theorem spMap_comp_moduli_spaces {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem exists_integral_lift (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    {J : Type} (M : J → MChart Y) (hM : ∀ x : Y.X, ∃ j, x ∈ (M j).U) (L : Type) [Field L] [Algebra c.F L]
    (W : ValuationSubring L) (hW : ∀ a : O, algebraMap c.F L (β a) ∈ W) (y : FrPt Xo c L) :
    ∃ (j : J) (f : Γ(Y.X, (M j).U) →+* L), (∀ a, f a ∈ W) ∧ Nonempty ((M j).Lift f y.x) := by
  classical
  have hx : y.x ≫ Xo.s = spMap (algebraMap c.F L) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y.2]
    unfold sOf
    exact spMap_comp_moduli_spaces _ _
  obtain ⟨yt, ⟨-, hyt⟩, -⟩ := (GlobalTheory.ModelPoints.model_points_charts E H Dw l Xo c O β Y).1 W L
    (((algebraMap c.F L).comp β).codRestrict W hW) (algebraMap c.F L)
    (pullback.lift y.x (spMap (algebraMap c.F L)) hx) (RingHom.ext fun _ => rfl) (pullback.lift_snd _ _ _)
  obtain ⟨j, hj⟩ := hM (yt (IsLocalRing.closedPoint W))
  obtain ⟨ψ, hψ, -⟩ := GlobalTheory.ModelPoints.existsUnique_chartHom (M j).hU W yt hj
  refine ⟨j, (algebraMap W L).comp ψ, fun a => (ψ a).2, ?_⟩
  have key : pullback.lift y.x (spMap (algebraMap c.F L)) hx ≫ Y.j =
      spMap ((algebraMap W L).comp ψ) ≫ (M j).hU.fromSpec := by
    rw [spMap_comp_moduli_spaces, Category.assoc, hψ, hyt]
  have hn := MChart.nonempty_lift E H Dw l Xo c O β Y (M j) L ((algebraMap W L).comp ψ)
    (pullback.lift y.x (spMap (algebraMap c.F L)) hx) (pullback.lift_snd _ _ _) key
  rwa [pullback.lift_fst] at hn

theorem exists_finite_pchart_cover : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra O c.F] [IsFractionRing O c.F] (Y : Model Xo c (algebraMap O c.F)), PushInvertible Y.t.G Y.t.PP.L → ∃ (J : Type) (_ : Finite J) (P : J → PChart Xo c (algebraMap O c.F)), Covers P := by
  intro hS E _ _ _ H Dw l Xo c hBC O _ _ _ _ _ Y hP
  classical
  obtain ⟨J₀, hJ₀, M, hM⟩ := exists_finite_mchart_cover E H Dw l Xo c O (algebraMap O c.F) Y hP
  have hT := fun (j : J₀) (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin (M j).n) =>
    GlobalTheory.T.exists_flagCellChart_over_modelChart hS E H Dw l Xo c hBC O Y hP (M j) ix
  choose K hK P hPc using hT
  refine ⟨(j : J₀) × (ix : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) ↪ Fin (M j).n) × K j ix, ?_,
    fun q => P q.1 q.2.1 q.2.2, ?_⟩
  · infer_instance
  · intro L _ _ W hW y
    obtain ⟨j, f, hf, ⟨Λ⟩⟩ := exists_integral_lift E H Dw l Xo c O (algebraMap O c.F) Y M hM L W hW y
    obtain ⟨g, hg, hind⟩ := MChart.Lift.exists_coordinates E H Dw l Xo c O (algebraMap O c.F) Y (M j) L f y Λ
    choose ixs u b hu hlow hone hbt hdiag hgu using
      fun τ => GlobalTheory.exists_integral_pivot_decomposition L W (M j).n (Dw.mult τ) (g τ) (hind τ)
    obtain ⟨k, hk⟩ := hPc j ixs L W f y Λ u b hf hu (fun τ => ⟨hlow τ, hone τ⟩) (fun τ => ⟨hbt τ, hdiag τ⟩)
      (by rw [← funext hgu]; exact hg)
    exact ⟨⟨j, ixs, k⟩, hk⟩

end GlobalTheory.Reg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsHolomorphicPeriodsAdaptedStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif GlobalTheory.FrameNorm
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_holomorphic_periods_adapted : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (A : Type) [CommRing A] [Algebra c.F A] (yA : FrPt Xo c A) (m : ℕ) (B : Set (Fin m → ℂ)) (φ : (Fin m → ℂ) → (A →ₐ[c.F] CAt σ)) (y : (Fin m → ℂ) → FrPt Xo c (CAt σ)), IsOpen B → (∀ a, DifferentiableOn ℂ (fun b => toC (φ b a)) B) → (∀ b ∈ B, FrMap (φ b) yA (y b)) → ∀ b₀ ∈ B, ∃ (B' : Set (Fin m → ℂ)) (k : Fin F.n) (P : (Fin m → ℂ) → ((F.Di k).La →+ (Fin g → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ IsHolPeriods (F.Di k) (fun j => relab c σ (e j).1) B' P ∧ ∀ b ∈ B', (y b).x = F.u k (P b) ∧ ∀ τ (i : Fin (Dw.mult τ)), IsDerivAt0 (fun z => (F.ex k (P b) z).left) (Pi.single (e.symm ⟨τ, i⟩) 1) ((y b).u τ i) := by
  first | exact @GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted | exact GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted | (intros; apply GlobalTheory.AdaptedPeriods.exists_holPeriods_adapted <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIdempotentWeightZeroSectionOfComponent
section
namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.Reg.exists_idem_section : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l)
    (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.GlobalTheory.Reg.EvLaws Xo c → ∀ h : _root_.Formalism.L2.Pj.GenFrEx Xo c,
      _root_.GlobalTheory.Reg.Atlas h → ∀ Z : _root_.Formalism.L2.Pj.Comp Xo c, ∃ χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0,
        χ * χ = χ ∧ _root_.Formalism.L2.Pj.evC h Z χ = 1 ∧ ∀ Z', Z' ≠ Z → _root_.Formalism.L2.Pj.evC h Z' χ = 0 := by
  intro E _ _ _ H Dw l Xo c hev h hcov Z
  classical
  have hexp : _root_.Formalism.L2.Pj.ex Dw 0 0 = 0 := by
    unfold _root_.Formalism.L2.Pj.ex
    funext x
    cases x <;> rfl
  have hreg : ∀ C : _root_.GlobalTheory.Reg.FChart h,
      _root_.Formalism.L2.Pj.wchar (_root_.Formalism.L2.Pj.ex Dw 0 0) C.t *
        (fun Z' => if Z' = Z then (1 : _root_.Formalism.L2.Pj.Om Z') else 0) C.Z ∈ C.R := by
    intro C
    rw [hexp]
    unfold _root_.Formalism.L2.Pj.wchar
    simp only [Pi.zero_apply, pow_zero, Finset.prod_const_one, _root_.one_mul]
    split_ifs
    · exact C.R.one_mem
    · exact C.R.zero_mem
  obtain ⟨χ, hχ, hval⟩ := _root_.GlobalTheory.Reg.SecGlue.exists_sec_of_regular E H Dw l Xo c hev h
    hcov 0 0 (fun Z' => if Z' = Z then (1 : _root_.Formalism.L2.Pj.Om Z') else 0) hreg
  refine ⟨χ, hχ, ?_, by simp [hval], fun Z' hZ' => by simp [hval, hZ']⟩
  have hsq : χ * χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0 := by simpa using _root_.Formalism.L2.Pj.sec_mul Xo c 0 0 0 0 hχ hχ
  have hmem : χ * χ - χ ∈ _root_.Formalism.L2.Pj.sec Xo c 0 0 := Submodule.sub_mem _ hsq hχ
  refine sub_eq_zero.mp (_root_.GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hev h hcov
    0 0 _ hmem fun Z' => ?_)
  have hmul : _root_.Formalism.L2.Pj.evC h Z' (χ * χ) = _root_.Formalism.L2.Pj.evC h Z' χ * _root_.Formalism.L2.Pj.evC h Z' χ := by
    unfold _root_.Formalism.L2.Pj.evC _root_.Formalism.L2.Pj.evR
    exact _root_.Formalism.L2.Pj.evalAt_mul _ _ _ _ _
  have hadd : _root_.Formalism.L2.Pj.evC h Z' (χ * χ - χ + χ) =
      _root_.Formalism.L2.Pj.evC h Z' (χ * χ - χ) + _root_.Formalism.L2.Pj.evC h Z' χ := by
    unfold _root_.Formalism.L2.Pj.evC _root_.Formalism.L2.Pj.evR
    exact _root_.Formalism.L2.Pj.evalAt_add _ _ _ _ _
  have hidem : _root_.Formalism.L2.Pj.evC h Z' χ * _root_.Formalism.L2.Pj.evC h Z' χ = _root_.Formalism.L2.Pj.evC h Z' χ := by
    rw [hval]
    split_ifs <;> simp
  rw [sub_add_cancel, hmul, hidem] at hadd
  exact add_eq_right.mp hadd.symm

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsModularSectionOfIntegralGenericValue
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

namespace GlobalTheory.Reg.IntSec

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem wchar_ex_smul {S : Type} [CommRing S] (a : (E →+* ℂ) × ℕ → ℕ) (n d : ℕ) (t : Ix Dw → Sˣ) :
    wchar (ex Dw (d • a) (d * n)) t = wchar (ex Dw a n) t ^ d := by
  unfold wchar
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_mul]
  cases i <;> simp [ex, mul_comm]

theorem one_mem (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : (1 : Rul Xo c) ∈ sec Xo c (0 • a) (0 * n) := by
  refine ⟨fun p q φ y z _ => by simp, fun p t y y' _ => ?_⟩
  rw [wchar_ex_smul]; simp

theorem mul_mem {a : (E →+* ℂ) × ℕ → ℕ} {n d e : ℕ} {f g : Rul Xo c} (hf : f ∈ sec Xo c (d • a) (d * n))
    (hg : g ∈ sec Xo c (e • a) (e * n)) : f * g ∈ sec Xo c ((d + e) • a) ((d + e) * n) := by
  rw [add_smul, add_mul]; exact sec_mul Xo c _ _ _ _ hf hg

theorem pow_mem {a : (E →+* ℂ) × ℕ → ℕ} {n d : ℕ} {f : Rul Xo c} (hf : f ∈ sec Xo c (d • a) (d * n)) (j : ℕ) :
    f ^ j ∈ sec Xo c ((j * d) • a) ((j * d) * n) := by
  induction j with
  | zero => rw [pow_zero, zero_mul]; exact one_mem a n
  | succ j ih => rw [pow_succ, Nat.succ_mul]; exact mul_mem ih hf

theorem prod_mem {a : (E →+* ℂ) × ℕ → ℕ} {n N : ℕ} {w : Fin N → Rul Xo c} (hw : ∀ i, w i ∈ sec Xo c a n)
    (e : Fin N → ℕ) (s : Finset (Fin N)) :
    ∏ i ∈ s, w i ^ e i ∈ sec Xo c ((∑ i ∈ s, e i) • a) ((∑ i ∈ s, e i) * n) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty]; exact one_mem a n
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    refine mul_mem ?_ ih
    have := pow_mem (d := 1) (a := a) (n := n) (f := w i) (by simpa using hw i) (e i)
    rwa [Nat.mul_one] at this

theorem aeval_mem {a : (E →+* ℂ) × ℕ → ℕ} {n N d : ℕ} {w : Fin N → Rul Xo c} (hw : ∀ i, w i ∈ sec Xo c a n)
    {P : MvPolynomial (Fin N) c.F} (hP : P.IsHomogeneous d) :
    MvPolynomial.aeval w P ∈ sec Xo c (d • a) (d * n) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq']
  refine Submodule.sum_mem _ fun s hs => ?_
  rw [← Algebra.smul_def]
  refine Submodule.smul_mem _ _ ?_
  have h1 : ∑ i, s i = d := by
    have := hP (MvPolynomial.mem_support_iff.1 hs)
    rw [← this, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  rw [← h1]
  exact prod_mem hw s Finset.univ

def evA (hL : EvLaws Xo c) {S : Type} [CommRing S] [IsReduced S] [Algebra c.F S] (y : FrPt Xo c S) :
    Rul Xo c →ₐ[c.F] S where
  toFun f := evR Xo c f y
  map_one' := evalAt_one _ _ y (hL.test S y)
  map_mul' f g := evalAt_mul _ _ f g y
  map_zero' := evalAt_zero _ _ y
  map_add' f g := evalAt_add _ _ f g y
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one]
    have h1 := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) r 1 y
    rw [evalAt_one _ _ y (hL.test S y), _root_.mul_one] at h1
    exact h1

theorem evC_aeval (hL : EvLaws Xo c) (h : GenFrEx Xo c) (Z : Comp Xo c) {N : ℕ} (w : Fin N → Rul Xo c)
    (P : MvPolynomial (Fin N) c.F) :
    evC h Z (MvPolynomial.aeval w P) = MvPolynomial.aeval (fun s => evC h Z (w s)) P := by
  have := MvPolynomial.comp_aeval_apply (evA hL (genFr h Z)) P (f := w)
  exact this

theorem chart_mem (hL : EvLaws Xo c) {h : GenFrEx Xo c} (C : FChart h) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul Xo c} (hf : f ∈ sec Xo c a n) : wchar (ex Dw a n) C.t * evC h C.Z f ∈ C.R := by
  have h1 := hL.wt a n f hf (Om C.Z) C.t (genFr h C.Z) C.yg (hL.test _ _) (hL.test _ _) C.bor
  have h2 := GlobalTheory.T.naturalRule_value_baseChange_of_isReduced E H Dw l Xo c hL a n f hf C.R (Om C.Z) C.R.val C.y C.yg C.gen
  unfold evC
  rw [← h1, h2]
  exact (evR Xo c f C.y).2

theorem mem_of_integral {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (R : Subalgebra K Ω)
    (sm : Algebra.Smooth K R) (frac : ∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, b ≠ 0 ∧ x * b = a) (m : ℕ) (r : ℕ → Ω)
    (hr : ∀ i < m, r i ∈ R) (x : Ω) (hx : x ^ m + ∑ i ∈ Finset.range m, r i * x ^ i = 0) : x ∈ R := by
  classical
  have hq : IsIntegrallyClosed (R ⧸ (⊥ : Ideal R)) :=
    GlobalTheory.isIntegrallyClosed_quotient_minimalPrime_of_smooth K R ⊥ (by simp [IsDomain.minimalPrimes_eq_singleton_bot])
  have hR : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot R)
  have hF : IsFractionRing R Ω := by
    refine IsFractionRing.of_field R Ω fun z => ?_
    obtain ⟨a, ha, b, hb, hb0, e⟩ := frac z
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by rw [eq_div_iff]; exacts [e, hb0]⟩
  let r' : Fin m → R := fun i => ⟨r i, hr i i.2⟩
  have hi : IsIntegral R x := by
    refine ⟨Polynomial.X ^ m + ∑ i : Fin m, Polynomial.C (r' i) * Polynomial.X ^ (i : ℕ),
      Polynomial.monic_X_pow_add (Polynomial.degree_sum_fin_lt r'), ?_⟩
    rw [← hx, Finset.sum_range (fun i => r i * x ^ i)]
    simp [Polynomial.eval₂_finset_sum, r']
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hi
  exact y.2

end GlobalTheory.Reg.IntSec

open GlobalTheory.Reg.IntSec in

theorem GlobalTheory.Reg.exists_sec_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → ∀ h : GenFrEx Xo c, Atlas h → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n N : ℕ) (w : Fin N → Rul Xo c), (∀ i, w i ∈ sec Xo c a n) → ∀ (Z : Comp Xo c) (k m : ℕ) (cf : ℕ → MvPolynomial (Fin N) c.F) (b : Om Z), (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → b ^ m + ∑ i ∈ Finset.range m, MvPolynomial.aeval (fun s => evC h Z (w s)) (cf i) * b ^ i = 0 → ∃ g ∈ sec Xo c (k • a) (k * n), evC h Z g = b ∧ (∀ Z', Z' ≠ Z → evC h Z' g = 0) ∧ g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i = 0 := by
  intro E _ _ _ H Dw l Xo c hL h hA a n N w hw Z k m cf b hcf hb
  classical
  obtain ⟨g, hg, hgv⟩ := GlobalTheory.T.exists_section_of_generic_values_regular_on_charts E H Dw l Xo c hL h hA (k • a) (k * n)
    (Function.update (fun Z' => (0 : Om Z')) Z b) (by
      intro C
      by_cases hZ : C.Z = Z
      · subst hZ
        rw [Function.update_self, wchar_ex_smul]
        refine mem_of_integral C.R C.sm C.frac m
          (fun i => wchar (ex Dw a n) C.t ^ ((m - i) * k) * evC h C.Z (MvPolynomial.aeval w (cf i))) ?_ _ ?_
        · intro i hi
          rw [← wchar_ex_smul]
          exact chart_mem hL C (aeval_mem hw (hcf i hi))
        · have h0 := congrArg (fun x => wchar (ex Dw a n) C.t ^ (k * m) * x) hb
          simp only [mul_zero, mul_add, Finset.mul_sum] at h0
          rw [← h0, mul_pow, ← pow_mul]
          congr 1
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : k * m = (m - i) * k + k * i := by
            rw [mul_comm (m - i), ← mul_add, Nat.sub_add_cancel (Finset.mem_range.1 hi).le]
          rw [evC_aeval hL, hi', pow_add, mul_pow, ← pow_mul]
          ring
      · rw [Function.update_of_ne hZ, mul_zero]
        exact C.R.zero_mem)
  have hZ : evC h Z g = b := by rw [hgv, Function.update_self]
  have hZ' : ∀ Z', Z' ≠ Z → evC h Z' g = 0 := fun Z' hne => by rw [hgv, Function.update_of_ne hne]
  refine ⟨g, hg, hZ, hZ', ?_⟩
  refine GlobalTheory.T.section_eq_zero_of_genericFramedPoint_values E H Dw l Xo c hL h hA ((k + m * k) • a) ((k + m * k) * n) _ ?_ ?_
  · refine Submodule.add_mem _ (IntSec.mul_mem hg (IntSec.pow_mem hg m)) (Submodule.sum_mem _ fun i hi => ?_)
    have hi' := Finset.mem_range.1 hi
    have e : k + m * k = k + (m - i) * k + i * k := by
      rw [add_assoc, ← add_mul, Nat.sub_add_cancel hi'.le]
    rw [e]
    exact IntSec.mul_mem (IntSec.mul_mem hg (aeval_mem hw (hcf i hi'))) (IntSec.pow_mem hg i)
  · intro Z'
    have e : g * g ^ m + ∑ i ∈ Finset.range m, (g * MvPolynomial.aeval w (cf i)) * g ^ i =
        g * (g ^ m + ∑ i ∈ Finset.range m, MvPolynomial.aeval w (cf i) * g ^ i) := by
      simp only [mul_add, Finset.mul_sum, _root_.mul_assoc]
    have ev : ∀ f, evC h Z' f = evA hL (genFr h Z') f := fun f => rfl
    rw [e, ev, map_mul]
    by_cases hne : Z' = Z
    · subst hne
      refine mul_eq_zero_of_right _ ?_
      rw [← hb, map_add, map_pow, map_sum, ← ev, hZ]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, map_pow, ← ev, ← ev, hZ, evC_aeval hL]
    · rw [← ev, hZ' Z' hne, zero_mul]
end
end

