import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0044
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0029
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0037
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0027
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Formalism.LocalToGlobal.ProjectiveLattices.GenFrPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0019
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Formalism.LocalToGlobal.ProjectiveLattices.FrameEx
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0047
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0028

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitAndGenValInj
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem compSplit_and_genValInj : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j), ∀ hG : GenFrEx (T.Q.Xo j) T.Q.c, CompSplitSt h j hG ∧ GenValInjSt h j hG := by
  intro D T h j hj hG
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  refine ⟨fun Z w g => ?_, fun w g h0 => ?_⟩
  · have hg := cutR_le T.C j w g.2
    obtain ⟨g', hg', h1, h2⟩ := exists_cusp_restrict_comp _ _ _ _ (T.Q.Xo j) T.Q.c hL hG (hA hG) D.R.r
      (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (fun σ hσ => h.unf j hj σ hσ) Z (wtA w) w.n _ hg
    have hm : g' ∈ cutR T.C j w := by
      rw [cutR_eq T.C hj]; exact hg'
    exact ⟨⟨g', hm⟩, h1, h2⟩
  · exact Subtype.ext (sec_eq_zero_of_generic_values _ _ _ _ (T.Q.Xo j) T.Q.c hL hG (hA hG) (wtA w) w.n _
      (cusp_le_sec _ _ _ _ _ (cutR_le T.C j w g.2)) h0)

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompSplitRecord
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem compSplit_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j)
    (hG : GenFrEx (T.Q.Xo j) T.Q.c), CompSplitSt h j hG := by
  intro D T h j hj hG Z w g
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  have hg : (g : T.R j) ∈ T.C j w := cutR_le T.C j w g.2
  obtain ⟨g', hg', h1, h0⟩ := exists_cusp_restrict_comp _ _ _ _ (T.Q.Xo j) T.Q.c hL hG (hA hG) _
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (fun σ hσ => h.unf j hj σ hσ) Z (wtA w) w.n (g : T.R j) hg
  have hm : g' ∈ cutR T.C j w := by
    rw [cutR_eq T.C hj]; exact hg'
  exact ⟨⟨g', hm⟩, h1, h0⟩

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CompUniqueOfReading
section
open NumberField Topology ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem comp_unique_of_reading : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), GoodEmb c σ → IsUnf U → ∀ (h : GenFrEx Xo c) (k : U.Comp) (Z Z' : Comp Xo c), ((U.X k).dom).Nonempty → (∀ (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom u n → ∀ f ∈ sec Xo c u n, evC h Z f = 0 ↔ ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → (∀ (u : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom u n → ∀ f ∈ sec Xo c u n, evC h Z' f = 0 ↔ ∀ x ∈ (U.X k).dom, rdU U f k x = 0) → Z = Z' := by
  intro E _ _ _ H Dw l Xo c σ r U _ _ h k Z Z' _ hZ hZ'
  by_contra hne
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨χ, hχ, -, h1, h0⟩ := GlobalTheory.Reg.exists_idem_section E H Dw l Xo c hL h (hA h) Z
  have hd : Dom (0 : (E →+* ℂ) × ℕ → ℕ) 0 := ⟨fun _ _ _ _ => le_rfl, Even.zero⟩
  have h2 := (hZ 0 0 hd χ hχ).2 ((hZ' 0 0 hd χ hχ).1 (h0 Z' (Ne.symm hne)))
  rw [h1] at h2
  exact one_ne_zero h2

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.CuspEqZeroOfGenericValues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.Reg

theorem cusp_eq_zero_of_generic_values {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
    {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hG : GenFrEx Xo c) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (g : Rul Xo c) (hg : g ∈ cusp Xo c U a n) (h0 : ∀ Z, evC hG Z g = 0) : g = 0 := by
  obtain ⟨hL, -, -, hA⟩ := evLaws_genFr_atlas E H Dw l Xo c
  exact sec_eq_zero_of_generic_values E H Dw l Xo c hL hG (hA hG) a n g (cusp_le_sec Xo c U a n hg) h0

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem genValInj_record : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c), GenValInjSt h j hG := by
  intro D T h j _ hG w g h0
  have hg : (g : T.R j) ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := cutR_le T.C j w g.2
  exact Subtype.ext (cusp_eq_zero_of_generic_values (T.Q.Xo j) T.Q.c (T.U j) hG (wtA w) w.n _ hg h0)

end GlobalTheory.Reg
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHoldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c ∧ IntDiagUnit Xo c ∧ GenFrEx Xo c ∧ ∀ h : GenFrEx Xo c, Atlas h := by
  first | exact @GlobalTheory.Reg.evLaws_genFr_atlas | exact GlobalTheory.Reg.evLaws_genFr_atlas | (intros; apply GlobalTheory.Reg.evLaws_genFr_atlas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFrameShiftOfValuedPointsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frame_shift_of_valued_points : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), EvLaws Xo c → IntDiagUnit Xo c → (∀ la, ModelAt Xo c la) → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (h : GenFrEx Xo c), ∃ δ : ∀ Z : Comp Xo c, AddValuation (Om Z) (WithTop ℤ) → Ix Dw → ℤ, (∀ (Z : Comp Xo c) (v : AddValuation (Om Z) (WithTop ℤ)), ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v → ((∃ la, ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := c.F) v la) ∨ ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn c.F v) → ∃ (T : CDVR) (ψ : Om Z →+* T.Fr) (y : IntFr Xo c T (ψ.comp (algebraMap c.F (Om Z)))), (∀ a : Om Z, a ≠ 0 → ((vV T.V (ψ a) : ℤ) : WithTop ℤ) = v a) ∧ ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c), f ∈ sec Xo c a n → (evI y f = 0 ↔ evC h Z f = 0) ∧ (evC h Z f ≠ 0 → ordC (δ Z v) v (wtZ a n) (valC h a n f Z) = vV T.V (evI y f))) ∧ ∀ Z : Comp Xo c, ∃ S : Finset (Om Z), (∀ s ∈ S, s ≠ 0) ∧ ∀ v : AddValuation (Om Z) (WithTop ℤ), ReciprocityTheory.ChartRestriction.G.T0.IsNormDiscrete v → ((∃ la, ReciprocityTheory.ChartRestriction.G.T0.IsOver (K := c.F) v la) ∨ ReciprocityTheory.ChartRestriction.G.T0.IsTrivOn c.F v) → (∀ s ∈ S, v s = 0) → δ Z v = 0 := by
  first | exact @GlobalTheory.Reg.exists_frameShift_of_valued_points | exact GlobalTheory.Reg.exists_frameShift_of_valued_points | (intros; apply GlobalTheory.Reg.exists_frameShift_of_valued_points <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FrameNormConjugatePointsEqPointwise
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

namespace GlobalTheory.FrameNorm

theorem fnConj_valAtCx_nrmC_eq_ptNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → FnConj Xo c fn yP ∧ ValAtCx h yP ∧ ∀ (Z : Comp Xo c) (P : Om Z →+* ℂ) a n, ∀ f ∈ sec Xo c a n, nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P = ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (sgOf P) (fn (sgOf P)) (ex Dw a n) f (yP Z P) := by
  intro E _ _ _ H Dw l Xo c r U _ xR fn _ hpin h yP hcb
  have hWD := GlobalTheory.TransferCompare.evalWD_framed Xo c
  have hgt : GenFromTest Xo c h := (GlobalTheory.Reg.genFrEx_and_genFromTest E H Dw l Xo c).2 h
  have hcx : ValAtCx h yP := by
    intro Z P a n f hf
    have hT1 := hgt Z
    have hm := hcb Z P
    have hT2 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (yP Z P) := by
      obtain ⟨p, ψ, y', hy'⟩ := hT1
      exact ⟨p, (PAlg P).comp ψ, y', frMap_trans (Xo := Xo) (c := c) _ _ _ ψ (PAlg P) y' _ _ hy' hm⟩
    have key : evR Xo c f (yP Z P) = PAlg P (evR Xo c f (genFr h Z)) := by
      unfold evR evalAt
      rw [dif_pos hT2, dif_pos hT1]
      exact hWD f hf.1 _ _ _ _ _ _ _ (yP Z P) hT2.choose_spec.choose_spec.choose_spec
        (frMap_trans (Xo := Xo) (c := c) _ _ _ _ (PAlg P) _ _ _ hT1.choose_spec.choose_spec.choose_spec hm)
    rw [key]
    rfl
  refine ⟨?_, hcx, ?_⟩
  · intro Z G x P
    have hm : FrMap (conjAlg (sgOf P)) (yP Z P) (yP Z ((starRingEnd ℂ).comp P)) :=
      frMap_cancel (Xo := Xo) (c := c) _ _ _ (PAlg P) (conjAlg (sgOf P)) (genFr h Z) _ _ (hcb Z P)
        (hcb Z ((starRingEnd ℂ).comp P))
    unfold nrmC
    congr 1
    · exact Complex.norm_conj _
    · refine Finset.prod_congr rfl fun i _ => ?_
      exact congrArg (fun t : ℝ => t ^ (-exZ Dw G i)) (hpin.2 (sgOf P) (yP Z P) _ hm i)
  · intro Z P a n f hf
    show nrmC fn (yP Z) (wtZ a n) (AddMonoidAlgebra.single (wtZ a n) (evC h Z f)) P = _
    rw [nrmC_single, hcx Z P a n f hf]
    unfold ptNorm
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have e : exZ Dw (wtZ a n) i = (ex Dw a n i : ℤ) := by cases i <;> rfl
    rw [e, zpow_neg, zpow_natCast, inv_pow]

end GlobalTheory.FrameNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ProdSplitConjugateEmbeddings
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj

noncomputable section

namespace GlobalTheory.BorelChar

theorem prod_shift_eq_prod_ite (m p0 r : ℕ) (hm : p0 + m = r) (f : ℕ → ℂ) :
    ∏ i : Fin m, f (p0 + i) = ∏ j : Fin r, (if p0 ≤ (j : ℕ) then f j else 1) := by
  have h1 : ∏ j : Fin r, (if p0 ≤ (j : ℕ) then f j else 1) =
      ∏ j ∈ Finset.range r, (if p0 ≤ j then f j else 1) :=
    Fin.prod_univ_eq_prod_range (fun j => if p0 ≤ j then f j else 1) r
  have h2 : ∏ i : Fin m, f (p0 + i) = ∏ i ∈ Finset.range m, f (p0 + i) :=
    Fin.prod_univ_eq_prod_range (fun i => f (p0 + i)) m
  rw [h1, h2, ← hm, Finset.prod_range_add, Finset.prod_eq_one (s := Finset.range p0), one_mul]
  · exact Finset.prod_congr rfl (fun i _ => by simp)
  · intro j hj
    simp only [Finset.mem_range] at hj
    exact if_neg (by omega)

theorem prod_reflect_eq_prod_ite (m p0 r : ℕ) (hm : m = p0) (hp : p0 ≤ r) (f : ℕ → ℂ) :
    ∏ i : Fin m, f (p0 - 1 - i) = ∏ j : Fin r, (if (j : ℕ) < p0 then f j else 1) := by
  subst hm
  have h1 : ∏ j : Fin r, (if (j : ℕ) < m then f j else 1) =
      ∏ j ∈ Finset.range r, (if j < m then f j else 1) :=
    Fin.prod_univ_eq_prod_range (fun j => if j < m then f j else 1) r
  have h2 : ∏ i : Fin m, f (m - 1 - i) = ∏ i ∈ Finset.range m, f (m - 1 - i) :=
    Fin.prod_univ_eq_prod_range (fun i => f (m - 1 - i)) m
  have h3 : r = m + (r - m) := by omega
  rw [h1, h2, Finset.prod_range_reflect f m, h3, Finset.prod_range_add]
  have h4 : ∏ x ∈ Finset.range (r - m), (if m + x < m then f (m + x) else 1) = 1 :=
    Finset.prod_eq_one (fun j _ => if_neg (by omega))
  rw [h4, mul_one]
  exact Finset.prod_congr rfl (fun j hj => (if_pos (Finset.mem_range.1 hj)).symm)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {l : Level H} {r : ℕ}

theorem conjEmb_conjEmb_generic_regularity (τ : E →+* ℂ) : conjEmb (conjEmb τ) = τ := by
  ext x
  simp [conjEmb]

theorem relabel_injective (c : Coeff l) (σ : c.F →+* ℂ) : Function.Injective (relab (E := E) c σ) := by
  intro τ₁ τ₂ h
  ext a
  have := congrArg (fun f : E →+* ℂ => f a) h
  exact congrArg Subtype.val (σ.injective this)

theorem prod_split_conjugate_embeddings {R : (E →+* ℂ) → (E →+* ℂ)} (hR : Function.Bijective R) (X : Data E r)
    (G : (E →+* ℂ) → ℂ) :
    ∏ τ, G τ = ∏ τ' : X.Ψ, (G (Function.invFun R τ'.1) * G (Function.invFun R (conjEmb τ'.1))) := by
  classical
  have h1 : ∏ τ, G τ = ∏ τ'', G (Function.invFun R τ'') :=
    Fintype.prod_bijective R hR _ _ (fun τ => by rw [Function.leftInverse_invFun hR.1 τ])
  rw [h1, ← Finset.prod_mul_prod_compl X.Ψ, Finset.prod_mul_distrib]
  congr 1
  · exact (Finset.prod_coe_sort X.Ψ (fun τ'' => G (Function.invFun R τ''))).symm
  · rw [Finset.prod_coe_sort X.Ψ (fun τ' => G (Function.invFun R (conjEmb τ')))]
    refine Finset.prod_nbij' conjEmb conjEmb (fun τ h => ?_) (fun τ h => ?_) (fun τ _ => conjEmb_conjEmb_generic_regularity τ)
      (fun τ _ => conjEmb_conjEmb_generic_regularity τ) (fun τ _ => by rw [conjEmb_conjEmb_generic_regularity])
    · have h' : τ ∉ X.Ψ := by simpa using h
      have := (not_congr (X.cmType τ)).1 h'
      rw [conjEmb_eq']
      simpa using this
    · have := (X.cmType τ).1 h
      rw [conjEmb_eq']
      simpa using this

theorem borel_diagonal_positive (X : Data E r) (b : Frame X.Ψ r) (τ' : E →+* ℂ) (h : τ' ∈ X.Ψ) (i : ℕ)
    (hi : X.p0 + i < r) : bdiag X b τ' i = b ⟨τ', h⟩ ⟨X.p0 + i, hi⟩ ⟨X.p0 + i, hi⟩ := by
  unfold bdiag
  rw [dif_pos h, dif_pos hi]

theorem borel_diagonal_negative (X : Data E r) (b : Frame X.Ψ r) (τ' : E →+* ℂ) (h : τ' ∈ X.Ψ) (i : ℕ)
    (hi : X.p0 - 1 - i < r) :
    bdiag X b (conjEmb τ') i = (b ⟨τ', h⟩ ⟨X.p0 - 1 - i, hi⟩ ⟨X.p0 - 1 - i, hi⟩)⁻¹ := by
  have hn : conjEmb τ' ∉ X.Ψ := by
    rw [conjEmb_eq']
    exact (X.cmType τ').1 h
  have hc : conjEmb (conjEmb τ') ∈ X.Ψ := by
    rw [conjEmb_conjEmb_generic_regularity]
    exact h
  unfold bdiag
  rw [dif_neg hn, dif_pos hc, dif_pos hi]
  have : (⟨conjEmb (conjEmb τ'), hc⟩ : X.Ψ) = ⟨τ', h⟩ := Subtype.ext (conjEmb_conjEmb_generic_regularity τ')
  rw [this]

variable {Dw : Datum H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ}

theorem bchar_laU_eq (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U) (k : U.Comp)
    (b : Frame (U.X k).Ψ r) (hb : b ∈ Bor (U.X k).Ψ r) (a : (E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (hm : n = m + m) :
    bchar (laU U a n k) b = bdet (U.X k) b ^ m *
      ∏ τ : E →+* ℂ, ∏ i : Fin (Dw.mult τ), bdiag (U.X k) b (relab c σ τ) i ^ a (τ, i) := by
  classical
  have hn2 : n / 2 = m := by omega
  have hinj := relabel_injective (E := E) c σ
  have hbij : Function.Bijective (relab (E := E) c σ) := ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩
  have hRinv : ∀ τ', relab c σ (Function.invFun (relab c σ) τ') = τ' := Function.rightInverse_invFun hbij.2
  have hp0r : (U.X k).p0 ≤ r := (U.X k).p0_le
  have hpos : ∀ τ, relab c σ τ ∈ (U.X k).Ψ → (U.X k).p0 + Dw.mult τ = r := by
    intro τ h
    have h1 : τ (H.rt : E) = H.rt0 := (relab_rt_iff c σ hσ τ).1 (((hU.2.1 k).2 _).1 h)
    have hm : Dw.mult τ = Dw.p := by unfold Datum.mult; rw [if_pos h1]
    have h2 := hU.1
    rw [(hU.2.1 k).1, hm]
    omega
  have hneg : ∀ τ, relab c σ τ ∉ (U.X k).Ψ → Dw.mult τ = (U.X k).p0 := by
    intro τ h
    have h1 : ¬ τ (H.rt : E) = H.rt0 := fun h1 => h (((hU.2.1 k).2 _).2 ((relab_rt_iff c σ hσ τ).2 h1))
    have hm : Dw.mult τ = Dw.q := by unfold Datum.mult; rw [if_neg h1]
    rw [(hU.2.1 k).1, hm]
  rw [prod_split_conjugate_embeddings hbij (U.X k)]
  have hfac : ∀ τ' : (U.X k).Ψ, ∏ j : Fin r, b τ' j j ^ laU U a n k τ' j =
      (∏ j : Fin r, b τ' j j ^ (if (U.X k).p0 ≤ (j : ℕ) then (1 : ℤ) else -1)) ^ m *
      ((∏ i : Fin (Dw.mult (Function.invFun (relab c σ) τ'.1)),
          bdiag (U.X k) b (relab c σ (Function.invFun (relab c σ) τ'.1)) i ^
            a (Function.invFun (relab c σ) τ'.1, i)) *
        ∏ i : Fin (Dw.mult (Function.invFun (relab c σ) (conjEmb τ'.1))),
          bdiag (U.X k) b (relab c σ (Function.invFun (relab c σ) (conjEmb τ'.1))) i ^
            a (Function.invFun (relab c σ) (conjEmb τ'.1), i)) := by
    intro τ'
    have hτ1 := hRinv τ'.1
    have hτ2 := hRinv (conjEmb τ'.1)
    have hm1 : (U.X k).p0 + Dw.mult (Function.invFun (relab c σ) τ'.1) = r :=
      hpos _ (by rw [hτ1]; exact τ'.2)
    have hm2 : Dw.mult (Function.invFun (relab c σ) (conjEmb τ'.1)) = (U.X k).p0 :=
      hneg _ (by rw [hτ2, conjEmb_eq']; exact ((U.X k).cmType τ'.1).1 τ'.2)
    have hsplit : ∀ j : Fin r, b τ' j j ^ laU U a n k τ' j =
        (b τ' j j ^ (if (U.X k).p0 ≤ (j : ℕ) then (1 : ℤ) else -1)) ^ m *
        ((if (U.X k).p0 ≤ (j : ℕ) then
            b τ' j j ^ a (Function.invFun (relab c σ) τ'.1, (j : ℕ) - (U.X k).p0) else 1) *
          (if (j : ℕ) < (U.X k).p0 then
            (b τ' j j)⁻¹ ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - (j : ℕ)) else 1)) := by
      intro j
      have hb0 := bor_diag_ne (U.X k) hb τ' j
      have hlaU : laU U a n k τ' j = if (U.X k).p0 ≤ (j : ℕ) then
          (a (Function.invFun (relab c σ) τ'.1, (j : ℕ) - (U.X k).p0) : ℤ) + ((n / 2 : ℕ) : ℤ)
          else -(a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - (j : ℕ)) : ℤ) - ((n / 2 : ℕ) : ℤ) :=
        rfl
      rw [hlaU]
      by_cases hj : (U.X k).p0 ≤ (j : ℕ)
      · rw [if_pos hj, if_pos hj, if_pos hj, if_neg (by omega)]
        simp only [hn2, zpow_add₀ hb0, zpow_natCast, zpow_one, mul_one]
        ring
      · rw [if_neg hj, if_neg hj, if_neg hj, if_pos (by omega)]
        simp only [hn2, sub_eq_add_neg, zpow_add₀ hb0, zpow_neg, zpow_natCast, zpow_one, inv_pow, one_mul]
        ring
    rw [Finset.prod_congr rfl (fun j _ => hsplit j), Finset.prod_mul_distrib, Finset.prod_pow,
      Finset.prod_mul_distrib]
    congr 2
    · rw [hτ1]
      calc ∏ j : Fin r, (if (U.X k).p0 ≤ (j : ℕ) then
              b τ' j j ^ a (Function.invFun (relab c σ) τ'.1, (j : ℕ) - (U.X k).p0) else 1)
          = ∏ j : Fin r, (if (U.X k).p0 ≤ (j : ℕ) then
              (fun j' : ℕ => if h : j' < r then
                b τ' ⟨j', h⟩ ⟨j', h⟩ ^ a (Function.invFun (relab c σ) τ'.1, j' - (U.X k).p0) else 1) j
              else 1) := by
            refine Finset.prod_congr rfl (fun j _ => ?_)
            simp [j.isLt]
        _ = ∏ i : Fin (Dw.mult (Function.invFun (relab c σ) τ'.1)),
              (fun j' : ℕ => if h : j' < r then
                b τ' ⟨j', h⟩ ⟨j', h⟩ ^ a (Function.invFun (relab c σ) τ'.1, j' - (U.X k).p0) else 1)
                ((U.X k).p0 + i) := (prod_shift_eq_prod_ite _ _ _ hm1 (fun j' : ℕ => if h : j' < r then
                b τ' ⟨j', h⟩ ⟨j', h⟩ ^ a (Function.invFun (relab c σ) τ'.1, j' - (U.X k).p0) else 1)).symm
        _ = ∏ i : Fin (Dw.mult (Function.invFun (relab c σ) τ'.1)),
              bdiag (U.X k) b τ'.1 i ^ a (Function.invFun (relab c σ) τ'.1, i) := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            have hi : (U.X k).p0 + (i : ℕ) < r := by have := i.isLt; omega
            rw [borel_diagonal_positive _ _ _ τ'.2 _ hi]
            simp [hi]
    · rw [hτ2]
      calc ∏ j : Fin r, (if (j : ℕ) < (U.X k).p0 then
              (b τ' j j)⁻¹ ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - (j : ℕ)) else 1)
          = ∏ j : Fin r, (if (j : ℕ) < (U.X k).p0 then
              (fun j' : ℕ => if h : j' < r then
                (b τ' ⟨j', h⟩ ⟨j', h⟩)⁻¹ ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - j')
                else 1) j
              else 1) := by
            refine Finset.prod_congr rfl (fun j _ => ?_)
            simp [j.isLt]
        _ = ∏ i : Fin (Dw.mult (Function.invFun (relab c σ) (conjEmb τ'.1))),
              (fun j' : ℕ => if h : j' < r then
                (b τ' ⟨j', h⟩ ⟨j', h⟩)⁻¹ ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - j')
                else 1) ((U.X k).p0 - 1 - i) := (prod_reflect_eq_prod_ite _ _ _ hm2 hp0r (fun j' : ℕ => if h : j' < r then
                (b τ' ⟨j', h⟩ ⟨j', h⟩)⁻¹ ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), (U.X k).p0 - 1 - j')
                else 1)).symm
        _ = ∏ i : Fin (Dw.mult (Function.invFun (relab c σ) (conjEmb τ'.1))),
              bdiag (U.X k) b (conjEmb τ'.1) i ^ a (Function.invFun (relab c σ) (conjEmb τ'.1), i) := by
            refine Finset.prod_congr rfl (fun i _ => ?_)
            have hi0 := i.isLt
            have hi : (U.X k).p0 - 1 - (i : ℕ) < r := by omega
            have hii : (U.X k).p0 - 1 - ((U.X k).p0 - 1 - (i : ℕ)) = i := by omega
            rw [borel_diagonal_negative _ _ _ τ'.2 _ hi]
            simp [hi, hii]
  rw [show bchar (laU U a n k) b =
      ∏ τ' : (U.X k).Ψ, ∏ j : Fin r, b τ' j j ^ laU U a n k τ' j from rfl]
  rw [Finset.prod_congr rfl (fun τ' _ => hfac τ')]
  conv_lhs => rw [Finset.prod_mul_distrib, Finset.prod_pow]
  rfl

end GlobalTheory.BorelChar
end
end

