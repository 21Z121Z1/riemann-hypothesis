import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0064
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0085
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0007
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0036
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0072
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0080
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0041
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0028
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0051
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0049
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0081
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThetaSeriesTestFunctionHolomorphicWeight
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelTestFunctionFiniteSumEquivariant
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0034
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0045
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0008
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0043
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0029
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HalvesFreeAndAdjoint

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsNetMaxAtGoodEmb
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem exists_net_max_at_goodEmb : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ NN : Finset (FPt (T.U j σ).X), NN.Nonempty ∧ (∀ P ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n), ∃ p ∈ NN, supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) P ≤ 4 * ((T.U j σ).X p.1).pnorm (laU (T.U j σ) (wtA w) w.n p.1) (P p.1) p.2) ∧ Real.log (16 * NN.card) ≤ 1041 * Zb D large₂ ^ 3 := by
  intro D T h hG large₂ j hj w hw hL hrn hf σ hσ

  have hne0 : Nonempty (T.U j σ).Comp := ⟨(T.dict j σ 1).1⟩
  obtain ⟨-, hlrd, hd, hcc, hlf, -, -, -, hn⟩ := id hw
  obtain ⟨-, -, -, -, -, hfdeg, hdE, -, hfr, hf1, -, -, -⟩ := GlobalTheory.T.exists_clearing_integers_principalDatum_host D large₂.sc.L hL hlrd hd hcc
  obtain ⟨e, M, wg, hM1, hMl, hwg, hwgl, -, hk⟩ := GlobalTheory.T.exists_rankOne_cuspData_log_bounds D T h hG large₂ j hj w hw hL hrn σ hσ
  have hcard := GlobalTheory.T.log_card_components_le_at_good_embedding D T h large₂ j hj w hw hL hrn hf σ hσ
  have hL1 : (1 : ℝ) ≤ large₂.sc.L := by linarith
  have hr1 : 1 ≤ D.R.r := le_trans hf1 hfr
  have hF1 : (1 : ℝ) ≤ (fdeg D.host.E : ℝ) := by rw [hfdeg]; exact_mod_cast hf1
  have hZ : Zb D large₂ = (fdeg D.host.E : ℝ) * D.R.r * large₂.sc.L := by rw [hfdeg]; rfl

  have hlogr : Real.log (D.R.r : ℝ) ≤ large₂.sc.L := by
    refine le_trans (Real.log_le_log (by exact_mod_cast hr1) (by exact_mod_cast hrn)) hn
  have hlogf : Real.log (fdeg D.host.E : ℝ) ≤ 2 * large₂.sc.L := by rw [hfdeg]; exact hlf
  obtain ⟨NN, hne, hP, hlog⟩ :=
    GlobalTheory.NetMax.exists_net_all_components_max D.host.E D.R.r (T.U j σ).Comp (fun k => (e k).toX)
      (laU (T.U j σ) (wtA w) w.n) M wg large₂.sc.L hr1 hL1 hM1 hwg (fun k => (hk k).1) (fun k => (hk k).2.1)
      hlogf hlogr hMl hwgl hdE
      (fun k => ⟨(hk k).2.2.1, le_trans (hk k).2.2.2.1 (by nlinarith),
        le_trans (hk k).2.2.2.2.1 (by nlinarith), le_trans (hk k).2.2.2.2.2.1 (by nlinarith)⟩)
      (by rw [← hZ]; exact hcard)
  refine ⟨NN, hne, hP, ?_⟩
  rw [hZ]
  exact hlog

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGeneratorReadingNeZeroAtFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.ThetaNoZero

theorem mem_mul_smul_top {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] {I J : Ideal R}
    (h : I ⊔ J = ⊤) {x : M} (hI : x ∈ I • (⊤ : Submodule R M)) (hJ : x ∈ J • (⊤ : Submodule R M)) :
    x ∈ (I * J) • (⊤ : Submodule R M) := by
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.1 (h ▸ Submodule.mem_top : (1 : R) ∈ I ⊔ J)
  have e : x = i • x + j • x := by rw [← add_smul, hij, one_smul]
  rw [e]
  refine Submodule.add_mem _ ?_ ?_
  · rw [Submodule.mul_smul]
    exact Submodule.smul_mem_smul hi hJ
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hj hI

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem dmin_of_isOrtho {X : Data E r} {x : Frame X.Ψ r} (ho : X.IsOrtho x) (τ : X.Ψ) (i : Fin (r + 1)) :
    dmin X.Gm x τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
  unfold dmin lminor psgn
  rw [ho τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, Complex.ofReal_prod,
    ← Fin.prod_univ_eq_prod_range fun a => ((FD.sgn X.p0 a : ℝ) : ℂ)]
  rfl

theorem psgn_mul_self (p i : ℕ) : psgn p i * psgn p i = 1 := by
  unfold psgn
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold FD.sgn
  split_ifs <;> simp

theorem isUnitFr_of_isOrtho {X : Data E r} {x : Frame X.Ψ r} (ho : X.IsOrtho x) : IsUnitFr X x := by
  intro τ i
  rw [dmin_of_isOrtho ho, Complex.norm_real, Real.norm_eq_abs]
  have h := psgn_mul_self X.p0 i
  rcases mul_self_eq_one_iff.1 h with h | h <;> simp [h]

theorem rmul_mem_dom_of_isOrtho {X : Data E r} {x b : Frame X.Ψ r} (hx : x ∈ X.dom) (hb : b ∈ Bor X.Ψ r)
    (ho : X.IsOrtho (rmul x b)) : rmul x b ∈ X.dom := by
  refine fun τ => ⟨?_, fun i => ?_⟩
  · change (mat x τ * mat b τ).det ≠ 0
    rw [Matrix.det_mul]
    exact mul_ne_zero (hx τ).1 (hb τ).1
  · rw [dmin_of_isOrtho ho, Complex.ofReal_re, psgn_mul_self]
    exact one_pos

theorem mark_sub_mem {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} {L : Lt E r}
    {mk : Dw.La →ₗ[𝓞 E] (Fin r → E)} (hm : IsMark l L mk) {a a' : Dw.La}
    (ha : a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La)) (ha' : a' ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La))
    (h : a' - a ∈ l.Mb • (⊤ : Submodule (𝓞 E) Dw.La)) :
    ((l.M : E)⁻¹) • mk a' - ((l.M : E)⁻¹) • mk a ∈ L := by
  have h1 := mem_mul_smul_top l.coprime h (Submodule.sub_mem _ ha' ha)
  rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨z, -, hz⟩ := h1
  have hM : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 (by have := l.three_le; omega)
  rw [← smul_sub, ← map_sub, ← hz, map_smul, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, smul_smul,
    inv_mul_cancel₀ hM, one_smul]
  exact hm.mem z

theorem exists_thGen_rdU_ne_zero : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → 3 * Formalism.L2.Pj.DF Dw a + 2 ≤ l.M → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ k, ∀ x ∈ (U.X k).dom, ∃ f ∈ thGen Xo c nab a n, Formalism.L2.PjFree.rdU U f k x ≠ 0 := by
  intro hCI E _ _ _ H Dw l Xo c σ r U hσ hU hr t ht hc a n hdom hrn hM _ nab hnab k x hx
  have hrpq : r = Dw.p + Dw.q := hU.1
  obtain ⟨x₀, b, hb, ho, rfl⟩ := (GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal E r (U.X k).p0 (U.X k).Ψ
    (U.X k).Gm (U.X k).Gm_herm).1 x hx
  have ho : (U.X k).IsOrtho (rmul x b) := ho
  have hx₀ := rmul_mem_dom_of_isOrtho hx hb ho
  obtain ⟨⟨P, hP, hP0⟩, hhom⟩ : (∃ P ∈ harmA (Dw := Dw) c a n, P ≠ 0) ∧ _ :=
    ⟨(GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).1 hdom (hrpq ▸ hrn),
      (GlobalTheory.exists_harmA_ne_zero_and_isHomogeneous E H Dw l c a n).2⟩
  have hdeg : P.totalDegree ≤ Formalism.L2.Pj.DF Dw a := (hhom P hP.1).totalDegree_le
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨W, Dc, A, θ, v, κ, he, -, hw, hsd, hmk, hmarked, hreads, hth, hmean, hvac, hprod⟩ :=
    GlobalTheory.T.exists_analyticData_unitFrame_framedPoint E H Dw l Xo c σ r U hσ hU hr a n hdom k ⟨rmul x b, hx₀⟩ (isUnitFr_of_isOrtho ho)
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  have hME : (l.M : E) ≠ 0 := Nat.cast_ne_zero.2 hM0
  obtain ⟨-, -, hconj, hmul, hroots⟩ := GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw l r (U.X k) (U.X k).Λ (W.mark k) _ hsd hmk
    (Complex.isPrimitiveRoot_exp l.M hM0)
  obtain ⟨Y, hY⟩ := hroots n l.M (Nat.pos_of_ne_zero hM0)
  have hQ0 : MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P) ≠ 0 := by
    intro h0
    refine hP0 (MvPolynomial.map_injective (algebraMap c.F ℂ) (algebraMap c.F ℂ).injective
      (MvPolynomial.rename_injective _ Dc.eL.injective ?_))
    rw [h0, map_zero, map_zero]
  have hQd : (MvPolynomial.rename Dc.eL (MvPolynomial.map (algebraMap c.F ℂ) P)).totalDegree ≤
      Formalism.L2.Pj.DF Dw a :=
    (((hhom P hP.1).map (algebraMap c.F ℂ)).rename_isHomogeneous (f := Dc.eL)).totalDegree_le
  obtain ⟨y, hy, hne⟩ := GlobalTheory.T.exists_level_translate_jet_ne_zero_alt E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hdom.2 H.w0 hw
    (U.X k).Λ hsd (rmul x b) hx₀ ho t ht (hc k) (Mfr l) l.M l.odd (by rw [hconj, hmul]) v hvac θ κ hth hmean hprod
    _ hQ0 (by omega)
  choose xs hxs u hu hyx using fun j => hmk.surj _ (hy j)
  obtain ⟨⟨f, hf, hfs⟩, hev⟩ := GlobalTheory.thetaRule_exists_and_eval hCI E H Dw l Xo c nab hnab a n xs P hP
  have hval := GlobalTheory.T.thetaValue_standardLattice_eq_classicalTheta hCI E H Dw l Xo c r W.g (U.X k) Dc.bas Dc.idx W.e (rmul x b) (U.X k).Λ
    (unC U k ⟨rmul x b, hx₀⟩) A Dc.sympl hx₀ hsd Dw.p n Dc.hr Dc.eL hrpq hdom.2 (he ▸ Dc.dir_eq) nab hnab θ v κ
    hreads hvac hprod (W.mark k) hmk hmarked xs (Y fun j => Submodule.Quotient.mk (xs j))
    (fun j => by
      obtain ⟨⟨a', ha', hq, hYa⟩, hj⟩ := hY (fun j => Submodule.Quotient.mk (xs j)) j
      exact ⟨⟨a', ha', (Submodule.Quotient.eq _).1 hq, hYa⟩, hj⟩)
    a P hP _ (hev f hf ℂ (unC U k ⟨rmul x b, hx₀⟩))
  have hne' := hne (Y fun j => Submodule.Quotient.mk (xs j)) fun j => by
    obtain ⟨⟨a', ha', hq, hYa⟩, -⟩ := hY (fun j => Submodule.Quotient.mk (xs j)) j
    have h1 := mark_sub_mem hmk (hxs j) ha' ((Submodule.Quotient.eq _).1 hq)
    have h2 : y j = ((l.M : E)⁻¹) • W.mark k (xs j) + u j := by
      have := congrArg (fun z => ((l.M : E)⁻¹) • z) (hyx j)
      simp only [smul_add, smul_smul, inv_mul_cancel₀ hME, one_smul, ← Nat.cast_smul_eq_nsmul E l.M (u j)] at this
      exact this
    have h3 := Submodule.sub_mem _ (Submodule.add_mem _ hYa h1) (hu j)
    convert h3 using 1
    rw [h2]
    abel
  rw [← hval] at hne'
  refine ⟨f, ⟨xs, P, hP, hf⟩, fun h0 => hne' ?_⟩
  have hB := (hU.2.2.2.2.1 a n hdom f hfs k).2.1 x hx b hb
  rw [h0, mul_zero] at hB
  have e : Formalism.L2.PjFree.rdU U f k (rmul x b) = Formalism.L2.PjFree.toC (evR Xo c f (U.un k ⟨rmul x b, hx₀⟩)) := dif_pos hx₀
  exact e.symm.trans hB

end GlobalTheory.ThetaNoZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsThClsDDdBCIff
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FieldBC

namespace GlobalTheory.ClassSumFieldChange

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c c' : Coeff l} (hle : c.F ≤ c'.F) {n : ℕ} (d : DeltaDat Xo c n)

theorem eF_incF (a : c.F) :
    ((ddBC hle d).eF (incF c c' hle a) : (covCoeff hle d).F) =
      incF d.c₂ (covCoeff hle d) (le_covCoeff hle d) (d.eF a) := Subtype.ext rfl

theorem exists_algOver (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] :
    ∃ _ : Algebra c'.F k, AlgOver c c' hle k := by
  letI alg : Algebra c.F c'.F := (incF c c' hle).toAlgebra
  haveI : IsScalarTower ℚ c.F c'.F := IsScalarTower.of_algebraMap_eq fun q => by
    rw [eq_ratCast (algebraMap ℚ c'.F), eq_ratCast (algebraMap ℚ c.F), map_ratCast]
  haveI := c'.fin
  haveI : FiniteDimensional c.F c'.F := Module.Finite.of_restrictScalars_finite ℚ c.F c'.F
  let φ : c'.F →ₐ[c.F] k := IsAlgClosed.lift
  exact ⟨φ.toRingHom.toAlgebra, fun a => φ.commutes a⟩

theorem thLa_iff (w : (Fin n → LevQ Dw d.l₂) → c.F) (La : GenLat E n) (N : ℕ) (P : MvPolynomial (LtN Dw n) c.F)
    (k : Type) [CommRing k] [Algebra d.c₂.F k] [A₂ : Algebra (covCoeff hle d).F k]
    (h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k) (y₂ : FrPt d.Xo₂ (covCoeff hle d) k) (v : k) :
    thLaValAt d.Xo₂ (covCoeff hle d) (nabBC (le_covCoeff hle d) d.nab₂)
        (fun q => (ddBC hle d).eF (incF c c' hle (w q))) La N
        (MvPolynomial.map ((ddBC hle d).eF : c'.F →+* (ddBC hle d).c₂.F) (MvPolynomial.map (incF c c' hle) P)) y₂ v ↔
      thLaValAt d.Xo₂ d.c₂ d.nab₂ (fun q => d.eF (w q)) La N
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) (y₂.res (le_covCoeff hle d) h₂) v := by
  have h := GlobalTheory.FieldBC.shortValAt_bc E H Dw d.l₂ d.Xo₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d) d.nab₂ n
    (fun q => d.eF (w q)) La 1 N (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) k h₂ y₂ v
  have e : (MvPolynomial.map ((ddBC hle d).eF : c'.F →+* (ddBC hle d).c₂.F) (MvPolynomial.map (incF c c' hle) P) :
      MvPolynomial (LtN Dw n) (covCoeff hle d).F) =
      MvPolynomial.map (incF d.c₂ (covCoeff hle d) (le_covCoeff hle d))
        (MvPolynomial.map (d.eF : c.F →+* d.c₂.F) P) := by
    rw [MvPolynomial.map_map, MvPolynomial.map_map]
    exact congrArg (fun g => MvPolynomial.map g P) (RingHom.ext fun a => eF_incF hle d a)
  rw [map_one] at h
  unfold thLaValAt
  rw [e]
  exact h

theorem isThClsD_ddBC_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c c' : Coeff l) (hle : c.F ≤ c'.F) (n : ℕ) (d : DeltaDat Xo c n) (Cl : Type) [Fintype Cl] (w : Cl → (Fin n → LevQ Dw d.l₂) → c.F) (La : Cl → GenLat E n) (Nc gam : Cl → ℕ) (vol : c.F) (ep : Cl → c.F) (Vs : Type) [AddCommGroup Vs] [Module c.F Vs] (io : Vs →ₗ[c.F] MvPolynomial (LtN Dw n) c.F) (Vs' : Type) [AddCommGroup Vs'] [Module c'.F Vs'] (io' : Vs' →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F) (x : Cl → Vs) (x' : Cl → Vs'), (∀ k, io' (x' k) = MvPolynomial.map (incF c c' hle) (io (x k))) → d.cδ ∈ sec d.Xo₂ d.c₂ 0 0 → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (m : ℕ), ∀ f ∈ sec Xo c a m, (IsThClsD Xo c' (ddBC hle d) (fun k q => incF c c' hle (w k q)) La Nc gam (incF c c' hle vol) (fun k => incF c c' hle (ep k)) io' x' (rulBC hle f) ↔ IsThClsD Xo c d w La Nc gam vol ep io x f) := by
  intro E _ _ _ H Dw l Xo c c' hle n d Cl _ w La Nc gam vol ep Vs _ _ io Vs' _ _ io' x x' hio hδ a m f hf
  have hcoef : ∀ (k : Type) [Field k] [Algebra c.F k] [Algebra c'.F k], AlgOver c c' hle k → ∀ cl,
      algebraMap c'.F k (incF c c' hle vol * ((gam cl : c'.F))⁻¹ * incF c c' hle (ep cl)) =
        algebraMap c.F k (vol * ((gam cl : c.F))⁻¹ * ep cl) := by
    intro k _ _ _ h cl
    rw [← h, map_mul (incF c c' hle), map_mul (incF c c' hle), map_inv₀, map_natCast]
  have hf' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw l Xo c c' hle).1 a m f hf).2
  have hδ' := ((GlobalTheory.FieldBC.rulBC_sec_val_linear E H Dw d.l₂ d.Xo₂ d.c₂ (covCoeff hle d) (le_covCoeff hle d)).1 0 0 d.cδ hδ).2
  have hov := (GlobalTheory.T.levelCover_larger_coeffField_lying_over E H Dw l Xo c c' hle n d).1
  constructor
  · intro H' k _ _ _ _ hk y y₂ hy
    obtain ⟨A, h⟩ := exists_algOver hle k
    letI A₂ : Algebra (covCoeff hle d).F k := A
    have h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k := fun b => by
      obtain ⟨b, rfl⟩ := d.eF.surjective b
      rw [hk, ← h b]
      rfl
    obtain ⟨vc, hv, he⟩ := @H' k _ _ A A₂ (fun _ => rfl) (y.ext hle h) (y₂.ext (le_covCoeff hle d) h₂)
      ((hov k h h₂ _ _).2 hy)
    refine ⟨vc, fun cl => ?_, ?_⟩
    · have := hv cl
      rw [hio] at this
      exact (thLa_iff hle d (w cl) (La cl) (Nc cl) (io (x cl)) k h₂ _ _).1 this
    · have e1 := hf' k h (y.ext hle h)
      have e2 := hδ' k h₂ (y₂.ext (le_covCoeff hle d) h₂)
      simp only [hcoef k h] at he
      rw [e1] at he
      exact he.trans (congrArg (· * _) e2)
  · intro H' k _ _ A A₂ hk y y₂ hy
    letI A₂' : Algebra (covCoeff hle d).F k := A₂
    letI := resAlg hle k
    letI := resAlg (le_covCoeff hle d) k
    have h : AlgOver c c' hle k := fun _ => rfl
    have h₂ : AlgOver d.c₂ (covCoeff hle d) (le_covCoeff hle d) k := fun _ => rfl
    obtain ⟨vc, hv, he⟩ := H' k (fun b => hk (incF c c' hle b)) (y.res hle h)
      (FrPt.res (c' := covCoeff hle d) (le_covCoeff hle d) h₂ y₂) ((hov k h h₂ y₂ y).1 hy)
    refine ⟨vc, fun cl => ?_, ?_⟩
    · rw [hio]
      exact (thLa_iff hle d (w cl) (La cl) (Nc cl) (io (x cl)) k h₂ y₂ _).2 (hv cl)
    · have e1 := hf' k h y
      have e2 := hδ' k h₂ y₂
      simp only [hcoef k h]
      rw [e1]
      exact he.trans (congrArg (· * _) e2.symm)

end GlobalTheory.ClassSumFieldChange
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormShortGeneratorEvalLeOrthonormalFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ShortPoint

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g q0 n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem isSB_smul (c : ℂ) {φ : TF n g} (h : IsSB φ) : IsSB (c • φ) :=
  (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ _ _ φ φ h h).2.1 c

theorem thA_sum (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (f : T → TF n g) (hf : ∀ i, IsSB (f i)) :
    thA X bas idx (∑ i ∈ s, f i) x = ∑ i ∈ s, thA X bas idx (f i) x := by
  induction s using Finset.induction_on with
  | empty => simpa using UnAct.thA_smul (X := X) (bas := bas) idx x 0 (0 : TF n g)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    exact UnAct.thA_add idx hs hx (hf a) (RecSum.isSB_sum s f hf)

theorem theta_sum₂ (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (s : Finset T) (W : T → ℂ) (f : T → TF n g) (hf : ∀ i, IsSB (f i))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) :
    thP X hr bas idx (∑ i ∈ s, W i • f i) P x = ∑ i ∈ s, W i * thP X hr bas idx (f i) P x := by
  unfold thP
  rw [← Jet.polyDeriv_sum_fun P _ s W _ fun i _ => ThetaHol.differentiable_thA idx hs (hf i) hx,
    thA_sum idx hs hx s _ fun i => isSB_smul _ (hf i)]
  congr 1
  funext z
  simp only [Finset.sum_apply, UnAct.thA_smul, Pi.smul_apply, smul_eq_mul]

theorem norm_mean_le (hr : X.p0 + q0 = r) (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) {T : Type} (W : T → ℂ) (f : T → TF n g) (hf : ∀ i, IsSB (f i))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (κ : ℂ) {C B : ℝ} (hC : 0 ≤ C) (hB : 0 ≤ B) (hW : ∀ i, ‖W i‖ ≤ C)
    (hb : ∀ i, ‖κ * thP X hr bas idx (f i) P x‖ ≤ B) :
    ‖((Nat.card T : ℂ))⁻¹ * (κ * thP X hr bas idx (∑ᶠ i, W i • f i) P x)‖ ≤ C * B := by
  by_cases h0 : Nat.card T = 0
  · rw [h0]
    simpa using mul_nonneg hC hB
  haveI : Finite T := Nat.finite_of_card_ne_zero h0
  haveI := Fintype.ofFinite T
  have hpos : (0 : ℝ) < Nat.card T := by exact_mod_cast Nat.pos_of_ne_zero h0
  rw [finsum_eq_sum_of_fintype, theta_sum₂ hr idx hs hx _ W f hf, Finset.mul_sum, norm_mul, norm_inv,
    Complex.norm_natCast, inv_mul_le_iff₀ hpos]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_card_nsmul _ _ (C * B) fun i _ => ?_).trans ?_)
  · rw [mul_left_comm, norm_mul]
    exact mul_le_mul (hW i) (hb i) (norm_nonneg _) hC
  · rw [Finset.card_univ, ← Nat.card_eq_fintype_card, nsmul_eq_mul]

omit [IsCMField E] in

theorem index_Ln (Λ : GenLat E n) (h : stdLat E n = stdL E n) :
    (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index =
      (stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup := by
  rw [← h, ← AddSubgroup.inf_relIndex_left]
  rfl

omit [IsCMField E] in

theorem zCard_eq (Λ : GenLat E n) (h : stdLat E n = stdL E n) {N M : ℕ} (hN : Λ.LevOK N M) (r : ℕ) :
    Λ.zCard N r = Λ.mIdx N r * ((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) ^ r := by
  rw [← index_Ln Λ h, GenLat.zCard, GenLat.mIdx, ← mul_pow]
  congr 1
  exact (AddSubgroup.relIndex_mul_relIndex _ _ _ (Submodule.toAddSubgroup_mono hN.2.2)
    (Submodule.toAddSubgroup_mono (inf_le_left : Λ.Ln ≤ Λ.La))).symm

end Classical

theorem map_mem_HHa {T : Type} (m : T → ℕ) (n : ℕ) {F F' : IntermediateField ℚ ℂ} (h : F = F') (cc : T → T)
    (isX : T → Prop) (a : T → ℕ → ℕ) {P : MvPolynomial (Letter T m n) F} (hP : P ∈ HHa m n F cc isX a) :
    MvPolynomial.map (IntermediateField.equivOfEq h : F →+* F') P ∈ HHa m n F' cc isX a := by
  subst h
  have : (IntermediateField.equivOfEq (rfl : F = F) : F →+* F) = RingHom.id F := RingHom.ext fun _ => rfl
  rw [this, MvPolynomial.map_id]
  exact hP

theorem sum_coeff_rename {F S S' : Type} [Field F] (σ : F →+* ℂ) (e : S ≃ S') (P : MvPolynomial S F) :
    ∑ m ∈ (MvPolynomial.rename e (MvPolynomial.map σ P)).support,
      ‖(MvPolynomial.rename e (MvPolynomial.map σ P)).coeff m‖ = ∑ m ∈ P.support, ‖σ (P.coeff m)‖ := by
  rw [MvPolynomial.support_rename_of_injective e.injective, Finset.sum_image
    fun a _ b _ h => Finsupp.mapDomain_injective e.injective h,
    MvPolynomial.support_map_of_injective _ σ.injective]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain _ e.injective, MvPolynomial.coeff_map]

theorem norm_index_cancellation_le_bound {b κ t : ℂ} {m z Q : ℕ} {J C B : ℝ} {j : ℕ} (hJ : J = j) (hj : 0 < j) (hz : z = m * j)
    (hb : ‖b‖ ^ 2 = J) (hC : 0 ≤ C * (B / Real.sqrt J))
    (h : ‖((Q : ℂ))⁻¹ * (κ * t)‖ ≤ C * (B / Real.sqrt J)) :
    ‖b⁻¹ * (m : ℂ)⁻¹ * (Q : ℂ)⁻¹ * (z : ℂ) * κ * t‖ ≤ C * B := by
  have hJ0 : 0 < J := by rw [hJ]; exact_mod_cast hj
  have hs : 0 < Real.sqrt J := Real.sqrt_pos.2 hJ0
  have hbn : ‖b‖ = Real.sqrt J := by rw [← hb, Real.sqrt_sq (norm_nonneg _)]
  have hm : ‖(m : ℂ)⁻¹ * (z : ℂ)‖ ≤ J := by
    rw [hz, hJ, Nat.cast_mul, ← _root_.mul_assoc, norm_mul, Complex.norm_natCast]
    refine mul_le_of_le_one_left (Nat.cast_nonneg _) ?_
    by_cases h0 : (m : ℂ) = 0
    · simp [h0]
    · rw [inv_mul_cancel₀ h0, norm_one]
  calc ‖b⁻¹ * (m : ℂ)⁻¹ * (Q : ℂ)⁻¹ * (z : ℂ) * κ * t‖
      = (Real.sqrt J)⁻¹ * (‖(m : ℂ)⁻¹ * (z : ℂ)‖ * ‖((Q : ℂ))⁻¹ * (κ * t)‖) := by
        rw [← hbn, ← norm_inv, ← norm_mul, ← norm_mul]
        congr 1
        ring
    _ ≤ (Real.sqrt J)⁻¹ * (J * (C * (B / Real.sqrt J))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hm h (norm_nonneg _) hJ0.le) (inv_nonneg.2 hs.le)
    _ = C * B := by
        have := Real.mul_self_sqrt hJ0.le
        set s := Real.sqrt J
        rw [← this]
        field_simp

theorem norm_evR_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → ∀ d : DeltaDat Xo c n, d.IsLev → 0 < d.pd → l.A = 1 → d.l₂.A = 1 → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∃ ph ψ x₀, d.PhiPin ph ψ x₀) → UnitC d → ∀ (Λ : GenLat E n) (N : ℕ) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → (∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) → P ∈ harmL c Λ a → IsShortRule Xo c d Λ N x0 P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (d.pd : ℝ) ^ (fdeg E * r * n) * ((∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n)) := by
  intro hci E _ _ _ H Dw l Xo c σ r U hσ hU hr1 t ht hct a n hDom hrn d hlev hpd _ _ hnab hpin hunit Λ N x0 P f
    hΛu hΛt hΛl hβ hP hrule k x hxo lam hlam hlam2
  obtain ⟨sr, hnab⟩ := hnab
  obtain ⟨ph, ψ, x₀, hpin⟩ := hpin
  have hr : r = Dw.p + Dw.q := hU.1
  have hn : Even n := hDom.2
  letI A₁ : Algebra c.F ℂ := σ.toAlgebra
  let σ₂ : d.c₂.F →+* ℂ := σ.comp (d.eF.symm : d.c₂.F →+* c.F)
  letI A₂ : Algebra d.c₂.F ℂ := σ₂.toAlgebra
  have hσ₂ : ∀ s : c.F, σ₂ (d.eF s) = σ s := fun s => congrArg σ (d.eF.symm_apply_apply s)
  have hcomp : ∀ s : c.F, algebraMap d.c₂.F ℂ (d.eF s) = algebraMap c.F ℂ s := hσ₂
  have huf : IsUnitFr (U.X k) x.1 := fun τ i => by
    unfold dmin lminor
    rw [hxo τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal, norm_prod]
    refine Finset.prod_eq_one fun a _ => ?_
    simp only [Function.comp, FD.sgn]
    split_ifs <;> simp
  obtain ⟨W, Dc, A, θ, v, κ, he, hg, hw, hL, hmk, hA, hrd, hth, hmean, hvac, hprod⟩ :=
    GlobalTheory.T.exists_analyticData_unitFrame_framedPoint E H Dw l Xo c σ r U hσ hU hr1 a n hDom k x huf
  obtain ⟨-, -, hlen, -, -⟩ := hx_ortho E r (U.X k) W.g Dc.bas Dc.idx Dc.sympl x.1 x.2 hxo
  obtain ⟨y₂, hy₂⟩ := hlev.2.2.2.2.2.2.1 ℂ hcomp (unC U k x)
  obtain ⟨B, hB, mk₂, hmk₂, hB₂, -⟩ := GlobalTheory.T.anFib_lift_alt E H Dw l Xo c n d hcomp hlev r W.g (U.X k) Dc.bas Dc.idx W.e x.1
    (U.X k).Λ (unC U k x) A Dc.sympl x.2 hL y₂ hy₂ (W.mark k) hA
  obtain ⟨v0, hv0, hev⟩ := hrule ℂ hcomp (unC U k x) y₂ hy₂
  have hM : 0 < d.l₂.M := by have := d.l₂.three_le; omega
  obtain ⟨-, hV, hVd, hstd⟩ := GenLatCmp.genLat_vset E n Λ.La
  have hΛ : Λ.La ∈ Vset E n d.l₂.M := hV _ N hM hΛu hΛt hΛl
  have hΛ1 : Λ.La ∈ Vset E n 1 := hVd 1 _ (one_dvd _) hΛ
  obtain ⟨Y, hY⟩ := (GlobalTheory.T.dual_half_level_marking_exists_and_match E H Dw d.l₂ r (U.X k) (U.X k).Λ mk₂ _ hL hmk₂
    (Complex.isPrimitiveRoot_exp _ hM.ne')).2.2.2.2 n N hΛl.1.pos
  have hval := GlobalTheory.T.shortThetaValue_complexPoint_eq_classicalTheta hci E H Dw d.l₂ d.Xo₂ d.c₂ r W.g (U.X k) Dc.bas Dc.idx W.e x.1 (U.X k).Λ y₂ B
    Dc.sympl x.2 hL Dw.p n Dc.hr Dc.eL hr hn (he ▸ Dc.dir_eq) d.nab₂ hnab θ v κ (hB θ hrd) hvac hprod mk₂ hmk₂ hB₂
    Λ.La hΛ N hΛl Y hY a _ (map_mem_HHa _ n d.hF.symm _ _ _ hP.1) (d.w x0) _ v0 hv0
  have hmap : MvPolynomial.map (algebraMap d.c₂.F ℂ)
      (MvPolynomial.map (IntermediateField.equivOfEq d.hF.symm : c.F →+* d.c₂.F) P) = MvPolynomial.map σ P := by
    rw [MvPolynomial.map_map]
    exact congrArg (fun s => MvPolynomial.map s P) (RingHom.ext hσ₂)
  have hhom : (MvPolynomial.rename Dc.eL (MvPolynomial.map σ P)).IsHomogeneous (Formalism.L2.Pj.DF Dw a) :=
    (((GlobalTheory.T.exists_integralHarmonic_ne_zero_and_isHomogeneous E H Dw l c a n).2 P hP.1).map σ).rename_isHomogeneous
  have hcore := fun y => GlobalTheory.T.jet_translate_projected_vacuum_le E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn H.w0 hw _ hL Λ.La hΛ1
    v hvac x.1 x.2 hxo t ht (hct k) θ κ hth hmean hprod lam hlam (fun u hu hu0 => hlam2.trans (hlen u hu hu0)) y _ _
    hhom
  obtain ⟨R, -, -, hR, hR0, -⟩ := VacMean.vac_proj_mean E r (U.X k) W.g Dw.p Dc.hr Dc.bas Dc.idx n Dc.sympl hn
    H.w0 hw _ hL Λ.La hΛ1 v hvac
  rw [hR] at hR0
  have hJ : (0 : ℝ) < Real.sqrt ((((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) : ℝ) ^ r) :=
    Real.sqrt_pos.2 (by exact_mod_cast hR0)
  have hsb : IsSB (projA (U.X k) Dc.bas (H.w0 : E) (tens Λ.La (U.X k).Λ) v) := by
    obtain ⟨⟨v', hv'⟩, -, h, -⟩ := TensVac.vacua E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn _
      H.w0.isIntegral_coe hw _ hL 1 Λ.La hΛ1
    rw [h v hvac.1 v' hv']
    exact isSB_smul _ hv'.1
  have hβa : ‖σ (betaH (Dw := Dw) c Λ)‖ ^ 2 =
      (((stdL E n).toAddSubgroup.relIndex Λ.La.toAddSubgroup) : ℝ) ^ r := by
    rw [← index_Ln Λ hstd, hr, betaH, dif_pos hβ]
    exact hβ.choose_spec.2.2 σ
  rw [sum_coeff_rename] at hcore
  have hc2 := fun y => (le_div_iff₀ hJ).2 (hcore y)
  have hB0 := (norm_nonneg _).trans (hc2 0)
  have hC0 : (0 : ℝ) ≤ (d.pd : ℝ) ^ (W.g * n) := by positivity
  have hmeanle := norm_mean_le Dc.hr Dc.idx Dc.sympl x.2 (fun q => algebraMap d.c₂.F ℂ (d.w x0 q))
    (fun q => heisG (U.X k) Dc.bas (Y q) (projA (U.X k) Dc.bas (H.w0 : E) (tens Λ.La (U.X k).Λ) v))
    (fun q => ((heisG_laws E r (U.X k) W.g Dc.bas Dc.idx n Dc.sympl hn).2.2.2 (Y q) _ hsb).1) _ κ hC0 hB0
    (fun q => by
      rw [hg, hr]
      exact ShortVal.Coeff.norm_coeff_le E H Dw l Xo c n d hlev hpd ph ψ x₀ hpin (hr ▸ hrn) x0 q σ₂)
    (fun q => hc2 (Y q))
  have hfin := norm_index_cancellation_le_bound (Nat.cast_pow _ r).symm hR0 (zCard_eq Λ hstd hΛl r) hβa (mul_nonneg hC0 hB0) hmeanle
  have hev' : Formalism.L2.PjFree.toC (evR Xo c f (U.un k x)) = evR d.Xo₂ d.c₂ d.cδ y₂ * v0 := hev
  rw [hev', norm_mul, hunit A₂ y₂, _root_.one_mul, hval, hmap, ← hg]
  simp only [map_mul, map_inv₀, map_natCast, hcomp]
  exact hfin

end GlobalTheory.Dict.ShortPoint
end

