import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0051
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsGenericComponentPointsOffMeagre
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0048
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0038
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0040
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0046
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.GrowthConstantBoundGcR
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0046
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0049
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0045
import Formalism.LocalToGlobal.ProjectiveLattices.TieInst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsBijectiveKappa
section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CompBij

section Free

open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ}

theorem frames_nonempty (X : Data E r) : X.dom.Nonempty := by
  classical
  choose P hP hG using X.signature
  refine ⟨fun τ => P τ, fun τ => ⟨hP τ, fun i => ?_⟩⟩
  have h : dmin X.Gm (fun τ => P τ) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    have hm : mat (Ψ := X.Ψ) (fun τ => P τ) τ = P τ := rfl
    unfold dmin lminor
    rw [hm, hG τ, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
    unfold psgn
    rw [Complex.ofReal_prod, ← Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ))]
    rfl
  rw [h, Complex.ofReal_re]
  refine mul_self_pos.2 ?_
  unfold psgn
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  unfold sgn
  split_ifs <;> norm_num

theorem rdU_eq_of_reads (U : Unf Xo c σ r) (h : GenFrEx Xo c) (k : U.Comp)
    (Z : Comp Xo c) (x : (U.X k).dom) (φ : Om Z →ₐ[c.F] CAt σ) (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ)
    (hm : FrMap φ (genFr h Z) y') (hb : FrBor t (U.un k x) y') (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    ∃ w : ℂ, w ≠ 0 ∧ ∀ f ∈ sec Xo c u n, w * rdU U f k x = toC (φ (evC h Z f)) := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨hL, -, -, -⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  have h3 : wchar (ex Dw u n) t ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (t i).ne_zero
  refine ⟨toC (wchar (ex Dw u n) t), h3, fun f hf => ?_⟩
  have h1 : evR Xo c f y' = φ (evC h Z f) := by
    obtain ⟨q, χ, y₀, hy₀⟩ := hL.test (Om Z) (genFr h Z)
    unfold evC
    rw [GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q χ y₀ _ hy₀,
      GlobalTheory.Reg.evR_eq_map_of_test_point hL hf q (φ.comp χ) y₀ y' (ReciprocityTheory.ChartRestriction.G.PullbackSections.frMap_trans χ φ hy₀ hm)]
    rfl
  have h2 : evR Xo c f y' = wchar (ex Dw u n) t * evR Xo c f (U.un k x) :=
    hL.wt u n f hf (CAt σ) t _ _ (hL.test _ _) (hL.test _ _) hb
  have h4 : rdU U f k x = toC (evR Xo c f (U.un k x)) := by
    simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk]
    rw [dif_pos x.2]
  rw [h4, ← h1, h2]
  rfl

theorem exists_bijection (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (hF : FnAlgClosed Xo c)
    (h : GenFrEx Xo c) :
    ∃ κ : Comp Xo c → U.Comp, Function.Bijective κ ∧
      (∀ Z (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom u n → ∀ f ∈ sec Xo c u n,
        evC h Z f = 0 ↔ ∀ x ∈ (U.X (κ Z)).dom, rdU U f (κ Z) x = 0) ∧
      ∀ Z (φ : Om Z →ₐ[c.F] CAt σ), ∃ x ∈ (U.X (κ Z)).dom, ∀ (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
        ∃ w : ℂ, w ≠ 0 ∧ ∀ f ∈ sec Xo c u n, w * rdU U f (κ Z) x = toC (φ (evC h Z f)) := by
  have hread := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h
  have hconn := GlobalTheory.GeomConn.comp_eq_of_fnAlgClosed E H Dw l Xo c σ r U hσ hU hF h
  have hex : ∀ Z : Comp Xo c, ∃ (k : U.Comp) (x : (U.X k).dom), ∃ (φ : Om Z →ₐ[c.F] CAt σ)
      (y' : FrPt Xo c (CAt σ)) (t : Ix Dw → (CAt σ)ˣ), FrMap φ (genFr h Z) y' ∧ FrBor t (U.un k x) y' := by
    intro Z
    obtain ⟨⟨φ⟩, hφ⟩ := hread Z
    obtain ⟨k, x, y', t, hh⟩ := hφ φ
    exact ⟨k, x, φ, y', t, hh⟩
  choose κ x₀ hκ using hex
  have htie := fun Z => GlobalTheory.evC_eq_zero_iff_rdU_eq_zero E H Dw l Xo c σ r U hσ hU h (κ Z) Z (x₀ Z) (hκ Z)
  refine ⟨κ, ⟨fun Z Z' e => ?_, fun k => ?_⟩, htie, fun Z φ => ?_⟩
  · refine GlobalTheory.Reg.comp_unique_of_reading E H Dw l Xo c σ r U hσ hU h (κ Z) Z Z' (frames_nonempty _) (htie Z) ?_
    rw [e]
    exact htie Z'
  · obtain ⟨Z, S, hS, hg⟩ := GlobalTheory.GenericFrames.exists_comp_generic_off_meagre E H Dw l Xo c σ r U hσ hU h k
    have hd : Dense (⋂ n, (S n)ᶜ) :=
      dense_iInter_of_isOpen (fun n => (hS n).1.isOpen_compl) fun n => interior_eq_empty_iff_dense_compl.1 (hS n).2
    obtain ⟨y, hy, hy'⟩ := hd.inter_open_nonempty _ (FourierCoefficientDomain.isOpen_dom (U.X k)) (frames_nonempty _)
    exact ⟨Z, hconn Z _ _ (x₀ Z) ⟨y, hy⟩ (hκ Z) (hg ⟨y, hy⟩ (Set.mem_iInter.1 hy'))⟩
  · obtain ⟨k, x, y', t, hm, hb⟩ := (hread Z).2 φ
    obtain rfl : k = κ Z := hconn Z _ _ x (x₀ Z) ⟨φ, y', t, hm, hb⟩ (hκ Z)
    exact ⟨x.1, x.2, fun u n => rdU_eq_of_reads U h _ Z x φ y' t hm hb u n⟩

end Free

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

end GlobalTheory.CompBij
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.PageHypothesesAtCuspStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.RunJoin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.page_hypotheses_at_cusp : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CT : ℝ) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (S : Scal (recB h.toLawsCore)) (nus : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ) (hG : GenFrEx (T.Q.Xo j) T.Q.c), PageOK large₂ (recPJ h j hj) H C2 A2 CT ka wL wF Tn nP nW h0 → HypC large₂ (recPJ h j hj) H C2 A2 7 0 CT S ka wL wF Tn nP nW h0 nus → ∀ G : GlobalFamilyData (recPJ h j hj) ka wL wF, GenOK h j hj large₂ G S (cc D large₂ C2 A2 7 wL) → (j < D.R.m → EtaOK h j hj large₂ wL G.iet G.et) → ∃ g0 : (recB h.toLawsCore).Cusp j wF, CurveHyp h j hj hG ka wL wF (gd2Xplus G (extAll h j hj) (intAtExt_extAll h j hj)) S g0 := by
  first | exact @GlobalTheory.RunJoin.curveHyp_of_run | exact GlobalTheory.RunJoin.curveHyp_of_run | (intros; apply GlobalTheory.RunJoin.curveHyp_of_run <;> assumption)
end

