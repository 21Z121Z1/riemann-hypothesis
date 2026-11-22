import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2221
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.MemRangeOfIsAlgebraicRatFun
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2245
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0363
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2220
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1951
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0065
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0241
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SlopeSqSubLeSlopeSqSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2234
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2219
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0122
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2222
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentSurjectsOfOpenClosedStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.component_surjects_of_open_closed : (∀ {A B : Type} [TopologicalSpace A] [TopologicalSpace B] (f : A → B), Continuous f → IsOpenMap f → IsClosedMap f →
    (∀ C ∈ irreducibleComponents A, IsOpen C) → ∀ S : Set B, IsClopen S → IsPreconnected S → ∀ a : A, f a ∈ S →
    ∃ C ∈ irreducibleComponents A, a ∈ C ∧ f '' C = S) → (∀ {X Y : AlgebraicGeometry.Scheme.{0}} (f : X ⟶ Y) [AlgebraicGeometry.LocallyOfFiniteType f] (k : Type) [Field k] [IsAlgClosed k]
    (y : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ Y), Set.range y ⊆ Set.range f →
    ∃ x : AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ X, x ≫ f = y) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H)
    (l l' : Level H) (Xo : Moduli Dw l) (Xo' : Moduli Dw l') (c : Coeff l) (c' : Coeff l') (hle : c.F ≤ c'.F),
    (∀ Z : Comp Xo c, ∃ U : (Xo.XF c).Opens, (U : Set (Xo.XF c)) = Z ∧ ∀ (k : Type) [Field k] (f : c.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (spMap f))) →
    (∀ Z : Comp Xo' c', ∃ U : (Xo'.XF c').Opens, (U : Set (Xo'.XF c')) = Z ∧ ∀ (k : Type) [Field k] (f : c'.F →+* k),
      IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) →
    ∀ (r : Xo'.XF c' ⟶ Xo.XF c)
      (h : r ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom) =
        pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom) ≫ spMap (IntermediateField.inclusion hle).toRingHom),
      IsFinite (pullback.lift r _ h) → Etale (pullback.lift r _ h) → Surjective (pullback.lift r _ h) →
    ∀ Z : Comp Xo c, ∃ U : (Xo'.XF c').Opens, (∀ z ∈ U, r z ∈ (Z : Set (Xo.XF c))) ∧
      (∀ (k : Type) [Field k] (f : c'.F →+* k),
        IrreducibleSpace ↑(pullback (U.ι ≫ pullback.snd Xo'.s (spMap (IntermediateField.inclusion c'.le).toRingHom)) (spMap f))) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (fK : c'.F →+* k) (x : Sp k ⟶ Xo.XF c),
        x ≫ pullback.snd _ _ = spMap (fK.comp (IntermediateField.inclusion hle).toRingHom) →
        Set.range x ⊆ (Z : Set (Xo.XF c)) →
        ∃ yy : Sp k ⟶ Xo'.XF c', yy ≫ pullback.snd _ _ = spMap fK ∧ yy ≫ r = x ∧ Set.range yy ⊆ (U : Set (Xo'.XF c')) := by
  first | exact @GlobalTheory.FlatModel.exists_comp_cover_lift | exact GlobalTheory.FlatModel.exists_comp_cover_lift | (intros; apply GlobalTheory.FlatModel.exists_comp_cover_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentsPeterssonOrthogonalAndMasses
section
open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.CompPetOrth

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {r : ℕ}

section One

variable {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (V : HSp D) (dict : GA D V → Σ k, Frame (U.X k).Ψ r)

theorem framesOn_disjoint {Z Z' : Comp Xo c} (h : Z ≠ Z') : Disjoint (framesOn U Z) (framesOn U Z') := by
  rw [Set.disjoint_left]
  rintro z ⟨_, hz⟩ ⟨_, hz'⟩
  have s₀ : Sp (CAt σ) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
  exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj Xo c Z Z' h) (hz s₀) (hz' s₀)

def sqN (la : ∀ k, Wt (U.X k).Ψ r) (f : Rul Xo c) : AutQ V → ENNReal :=
  fun q => ‖ptN la (rdU U f) (dict q.out)‖ₑ ^ (2 : ℝ)

theorem ptN_rdU_of_not_dom (la : ∀ k, Wt (U.X k).Ψ r) (f : Rul Xo c) {z : Σ k, Frame (U.X k).Ψ r}
    (hz : z.2 ∉ (U.X z.1).dom) : ptN la (rdU U f) z = 0 := by
  have h0 : rdU U f z.1 z.2 = 0 := by simp [rdU, hz]
  simp only [ptN, Data.pnorm, h0, norm_zero, zero_mul]

theorem sqN_support (la : ∀ k, Wt (U.X k).Ψ r) {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    Function.support (sqN U V dict la f) ⊆ classesOver V dict (framesOn U Z) := by
  intro q hq
  by_contra hn
  apply hq
  have h0 : ptN la (rdU U f) (dict q.out) = 0 := by
    simp only [ptN, Data.pnorm, rdU_eq_zero U hf hn, norm_zero, zero_mul]
  simp [sqN, h0]

theorem petAt_sq (x : ℝ) (μ : Measure (AutQ V)) (G : WTZ D.host.E) (f : Rul Xo c) :
    petAt U x V dict μ G f ^ 2 = lieFacZ Dw x G ^ 2 * (∫⁻ q, sqN U V dict (modelWt U G) f q ∂μ).toReal := by
  unfold petAt petE
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num), ENNReal.toReal_ofNat,
    ← ENNReal.toReal_rpow, mul_pow]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num [sqN]

theorem petE_rdU_ne_top (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (la : ∀ k, Wt (U.X k).Ψ r)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X la) : petE V dict μ la (rdU U f) ≠ ⊤ := by
  have h : ∀ q : AutQ V, ‖ptN la (rdU U f) (dict q.out)‖ₑ ≤ supE U.X la (rdU U f) := fun q => by
    rw [Real.enorm_eq_ofReal (ptN_nonneg _ _ _)]
    by_cases hd : (dict q.out).2 ∈ (U.X (dict q.out).1).dom
    · exact le_iSup (fun p : FPt U.X => ENNReal.ofReal ((U.X p.1).pnorm (la p.1) (rdU U f p.1) p.2))
        ⟨(dict q.out).1, ⟨(dict q.out).2, hd⟩⟩
    · rw [ptN_rdU_of_not_dom U la f hd, ENNReal.ofReal_zero]
      exact bot_le
  refine ne_top_of_le_ne_top ?_ (eLpNorm_le_of_ae_enorm_bound (Filter.Eventually.of_forall h))
  rw [measure_univ, ENNReal.one_rpow, smul_eq_mul, mul_one]
  exact supE_ne_top U.X la hP

theorem lint_sqN_ne_top (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (la : ∀ k, Wt (U.X k).Ψ r)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X la) : ∫⁻ q, sqN U V dict la f q ∂μ ≠ ⊤ := by
  have h := petE_rdU_ne_top U V dict μ la hP
  rw [petE, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at h
  intro ht
  apply h
  simp only [sqN] at ht
  norm_num at ht ⊢
  rw [ht]

theorem lint_sqN_sum [Fintype (Comp Xo c)] (μ : Measure (AutQ V))
    (hm : ∀ Z : Comp Xo c, NullMeasurableSet (classesOver V dict (framesOn U Z)) μ) (la : ∀ k, Wt (U.X k).Ψ r)
    (f : Comp Xo c → Rul Xo c) (hf : ∀ Z, f Z ∈ suppOn Z) :
    ∫⁻ q, sqN U V dict la (∑ Z, f Z) q ∂μ = ∑ Z, ∫⁻ q, sqN U V dict la (f Z) q ∂μ := by
  have hdisj : Pairwise (Function.onFun Disjoint fun Z => classesOver V dict (framesOn U Z)) :=
    fun Z Z' h => Set.disjoint_left.2 fun q h1 h2 => Set.disjoint_left.1 (framesOn_disjoint U h) h1 h2
  have hpt : ∀ Z, ∀ q ∈ classesOver V dict (framesOn U Z),
      sqN U V dict la (∑ Z, f Z) q = sqN U V dict la (f Z) q := by
    intro Z q hq
    have e : rdU U (∑ Z', f Z') (dict q.out).1 (dict q.out).2 = rdU U (f Z) (dict q.out).1 (dict q.out).2 := by
      rw [map_sum, Finset.sum_apply, Finset.sum_apply, Finset.sum_eq_single Z]
      · intro Z' _ hZ'
        exact rdU_eq_zero U (hf Z') fun h => Set.disjoint_left.1 (framesOn_disjoint U hZ') h hq
      · intro h; exact absurd (Finset.mem_univ Z) h
    simp only [sqN, ptN, Data.pnorm, e]
  have hsupp : Function.support (sqN U V dict la (∑ Z, f Z)) ⊆ ⋃ Z, classesOver V dict (framesOn U Z) := by
    intro q hq
    by_contra hn
    simp only [Set.mem_iUnion, not_exists] at hn
    apply hq
    have e : rdU U (∑ Z', f Z') (dict q.out).1 (dict q.out).2 = 0 := by
      rw [map_sum, Finset.sum_apply, Finset.sum_apply]
      exact Finset.sum_eq_zero fun Z _ => rdU_eq_zero U (hf Z) (hn Z)
    have h0 : ptN la (rdU U (∑ Z', f Z')) (dict q.out) = 0 := by
      simp only [ptN, Data.pnorm, e, norm_zero, zero_mul]
    simp only [sqN, h0]
    simp
  rw [← setLIntegral_eq_of_support_subset hsupp, lintegral_iUnion₀ hm (fun Z Z' h => (hdisj h).aedisjoint),
    tsum_fintype]
  refine Finset.sum_congr rfl fun Z _ => ?_
  rw [← setLIntegral_eq_of_support_subset (sqN_support U V dict la (hf Z))]
  exact lintegral_congr_ae ((ae_restrict_mem₀ (hm Z)).mono fun q hq => hpt Z q hq)

theorem petAt_muOn_sq (x : ℝ) (G : WTZ D.host.E) {Z : Comp Xo c} {f : Rul Xo c} (hf : f ∈ suppOn Z) :
    (muQ1 V (classesOver V dict (framesOn U Z))).toReal * petAt U x V dict (muOn U V dict Z) G f ^ 2 =
      petAt U x V dict (muQ1 V) G f ^ 2 := by
  rw [petAt_sq, petAt_sq]
  unfold muOn muPart ProbabilityTheory.cond
  have key := setLIntegral_eq_of_support_subset (μ := muQ1 V) (sqN_support U V dict (modelWt U G) hf)
  rw [lintegral_smul_measure, key]
  by_cases h0 : muQ1 V (classesOver V dict (framesOn U Z)) = 0
  · have hI : ∫⁻ q, sqN U V dict (modelWt U G) f q ∂muQ1 V = 0 := by
      rw [← key, Measure.restrict_eq_zero.2 h0, lintegral_zero_measure]
    simp [h0, hI]
  · have ha : (muQ1 V (classesOver V dict (framesOn U Z))).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.2 ⟨h0, measure_ne_top _ _⟩
    rw [smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_inv]
    field_simp

theorem petAt_idem_le (x : ℝ) (μ : Measure (AutQ V)) [IsProbabilityMeasure μ] (G : WTZ D.host.E) (Z : Comp Xo c)
    {f : Rul Xo c} (hP : rdU U f ∈ holSub U.X (modelWt U G)) :
    petAt U x V dict μ G (GlobalTheory.FlatLine.idem Z * f) ≤ petAt U x V dict μ G f := by
  unfold petAt
  refine mul_le_mul_of_nonneg_left ?_ (lieFacZ_pos _ _).le
  refine ENNReal.toReal_mono (petE_rdU_ne_top U V dict μ _ hP) ?_
  unfold petE
  refine eLpNorm_mono fun q => ?_
  rw [Real.norm_of_nonneg (ptN_nonneg _ _ _), Real.norm_of_nonneg (ptN_nonneg _ _ _)]
  simp only [ptN, Data.pnorm]
  refine mul_le_mul_of_nonneg_right ?_ (pnorm_fac_nonneg _ _ _)
  rw [GlobalTheory.AllWt.rdU_mul, Pi.mul_apply, Pi.mul_apply, norm_mul]
  refine mul_le_of_le_one_left (norm_nonneg _) ?_
  have he : IsIdempotentElem (rdU U (GlobalTheory.FlatLine.idem Z) (dict q.out).1 (dict q.out).2) := by
    have := congrFun (congrFun (GlobalTheory.AllWt.rdU_mul U (GlobalTheory.FlatLine.idem Z) (GlobalTheory.FlatLine.idem Z)) (dict q.out).1)
      (dict q.out).2
    rw [GlobalTheory.FlatLine.idem_mul_idem] at this
    exact this.symm
  rcases IsIdempotentElem.iff_eq_zero_or_one.1 he with h | h <;> rw [h] <;> simp

end One

theorem orthogonal_mass_idem : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → ∀ G : WTZ D.host.E, Orthogonal U V dict G ∧ (∀ Z σ, 0 ≤ mass U V dict Z σ ∧ mass U V dict Z σ ≤ 1) ∧ ∀ (Z : Comp Xo c) (σ : c.F →+* ℂ) (f : cuspW Xo c U G), petW U (xiR D) V dict G σ (idem Z * (f : Rul Xo c)) ≤ petW U (xiR D) V dict G σ (f : Rul Xo c) := by
  intro D H Dw l Xo c r U V dict hc G
  haveI := CompFin.finite_comp Xo c
  letI : Fintype (Comp Xo c) := Fintype.ofFinite _
  have hm : ∀ (σ : c.F →+* ℂ) (Z : Comp Xo c), NullMeasurableSet
      (classesOver (V (goodOf c σ)) (dict (goodOf c σ)) (framesOn (U (goodOf c σ)) Z)) (muQ1 (V (goodOf c σ))) :=
    fun σ Z => GlobalTheory.ClassesMeas.nullMeasurableSet_classesOver_framesOn D H Dw l Xo c r U V dict hc _
      (goodEmb_goodOf c σ) Z
  refine ⟨fun σ => ⟨fun f => ?_, fun Z f => ?_⟩, fun Z σ => ⟨ENNReal.toReal_nonneg, ?_⟩, fun Z σ f => ?_⟩
  · rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    simp only [normRes, petW]
    rw [petAt_sq, lint_sqN_sum _ _ _ _ (hm σ) _ _ fun Z => (Submodule.mem_inf.1 (f Z).2).2,
      ENNReal.toReal_sum fun Z _ => lint_sqN_ne_top _ _ _ _ _
        ((mem_cuspW.1 (Submodule.mem_inf.1 (f Z).2).1).2 _ (goodEmb_goodOf c σ)), Finset.mul_sum]
    exact Finset.sum_congr rfl fun Z _ => (petAt_sq _ _ _ _ _ _ _).symm
  · simp only [normRes, normOn, petW, petOn, mass]
    exact (petAt_muOn_sq _ _ _ _ _ (Submodule.mem_inf.1 f.2).2).symm
  · simp only [mass]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  · simp only [petW]
    exact petAt_idem_le _ _ _ _ _ _ _ ((mem_cuspW.1 f.2).2 _ (goodEmb_goodOf c σ))

end GlobalTheory.CompPetOrth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantNormFlatSectionEqNormDivNormDetStatement
section
open CategoryTheory GlobalTheory.Frames NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.DefPt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantNorm_flatSection_eq_norm_div_norm_det : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ), DefCase U ξ → ∀ (Z : Comp Xo c) (P : PtData Z) (τ : Psi H) (s : FlatSec U ξ Z τ) (b : c.F), b ≠ 0 → (∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (u : S), (∀ τ', IsUnit (Y τ').det) → IsUnit u → FrMap (Algebra.ofId c.F S) P.y₀ z → FrChg (fun τ' => (Y τ')ᵀ) u z y → evR Xo c s.sig y * (Y τ.1).det = algebraMap c.F S b) → ∀ σ, s.cInf σ = ‖σ b‖ / ‖(P.X σ τ.1).det‖ := by
  first | exact @GlobalTheory.DefPt.ArchVal.cInf_eq_norm_div_norm_det | exact GlobalTheory.DefPt.ArchVal.cInf_eq_norm_div_norm_det | (intros; apply GlobalTheory.DefPt.ArchVal.cInf_eq_norm_div_norm_det <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMatrixCoeffInfinitePlacesWeightRepStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct Topology
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_matrixCoeff_infinitePlacesWeightRep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (lam : InfinitePlace E → DomWeight n) (u : Wsp lam) (ℓ : Module.Dual ℂ (Wsp lam)), Continuous fun g : UA E n => ℓ (wInf lam g u) := by
  first | exact @GlobalTheory.BCT.TrKer.continuous_coef_wInf | exact GlobalTheory.BCT.TrKer.continuous_coef_wInf | (intros; apply GlobalTheory.BCT.TrKer.continuous_coef_wInf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinatesIntegralOfLinearlyIndependentReductioStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinates_integral_of_linearly_independent_reduction : ∀ (W : Type) [CommRing W] [IsDomain W] (K₀ K₁ : Type) [Field K₀] [Field K₁] (i₀ : W →+* K₀) (i₁ : W →+* K₁), Function.Injective i₀ → (∀ a, i₁ a ≠ 0 → IsUnit a) → ∀ (I Λ : Type) [Fintype Λ] (u : I → Λ → W), (∀ c : Λ → K₁, (∀ i, ∑ l, c l * i₁ (u i l) = 0) → c = 0) → ∀ (w : I → W) (z : Λ → K₀), (∀ i, i₀ (w i) = ∑ l, z l * i₀ (u i l)) → ∃ z₀ : Λ → W, (∀ l, i₀ (z₀ l) = z l) ∧ ∀ i, w i = ∑ l, z₀ l * u i l := by
  first | exact @GlobalTheory.MBLow.coords_integral_of_closed_indep | exact GlobalTheory.MBLow.coords_integral_of_closed_indep | (intros; apply GlobalTheory.MBLow.coords_integral_of_closed_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableRationalSubgroupInRealSpecialUnitary
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem countable_inReal_of_numberField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)), Countable (inReal Ψ G Γ) := by
  intro E _ _ _ r Ψ G Γ
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Units.val_injective.countable
  have h : ((Γ.map (embGL Ψ r) : Subgroup (Ψ → GL (Fin r) ℂ)) : Set (Ψ → GL (Fin r) ℂ)).Countable := by
    rw [Subgroup.coe_map]
    exact (Set.to_countable _).image _
  haveI : Countable (Γ.map (embGL Ψ r)) := h.to_subtype
  refine Function.Injective.countable
    (f := fun x : inReal Ψ G Γ => (⟨x.1.1, x.2⟩ : Γ.map (embGL Ψ r))) ?_
  intro x y hxy
  have h2 : x.1.1 = y.1.1 := Subtype.mk.inj hxy
  exact Subtype.ext (Subtype.ext h2)

end GlobalTheory.CovTop.VolUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovarianceAtConstantXiStatement
section
open NumberField Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj GlobalTheory.OneMapTuples
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLift_eq_factor_mul_geometricClassSum : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → R.tup_mu_off → R.tup_mu_used → Nonempty (FWTie T R κ v₀) → T.pb = R.C.P.pb → IoExt R → ∀ (i : Fin D.R.m) (lev : G → (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (T.Q.Dw ((i : ℕ) + 1)).La) (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E) (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W) (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).coef.W), Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L → ∃ (lam : AutQ (Wc D i) → ℂ) (z : G), (∀ q, lam q ≠ 0) ∧ ∀ (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O.c'.F → O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → O.lev = lev → CoefficientBaseChange R i O.jL (inC O.c') (c0L i) O.c0' → ∀ c0 : ℂ, XiConst O (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) c0 → PtIdent O (κ i) lam z c0 := by
  first | exact @GlobalTheory.PtIdCore.point_identity_core | exact GlobalTheory.PtIdCore.point_identity_core | (intros; apply GlobalTheory.PtIdCore.point_identity_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringLeFromMeasure
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop

namespace GlobalTheory.CoreSlope

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

set_option maxHeartbeats 1000000 in

theorem coreAt_of (C : ℝ) (hg : GramAt p i) (hm : MeasAt p i C) (hr : RatAt p i) : CoreAt p i (2 * C) := by
  obtain ⟨ι, hι, hli, himg⟩ := GlobalTheory.T.exists_semilinear_emb_supLattice_onto_realisation _ _ _ _ _ p.T p.R.toRealDat p.κ p.v₀ p.fw i
  have hTC : IsTotallyComplex p.T.Q.c.F := ⟨fun v => by
    rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_iff, ComplexEmbedding.isReal_iff]
    exact fun e => GlobalTheory.CompHt.conj_comp_ne (c := p.T.Q.c) v.embedding (RingHom.ext fun a => RingHom.congr_fun e a)⟩
  have hc : ∀ σ x, nrmK p.fw i ((starRingEnd ℂ).comp σ) x = nrmK p.fw i σ x := fun σ x => by
    simp only [nrmK]
    rw [normW, normW, petW, petW, GlobalTheory.CompHt.goodOf_conj σ]
  have hfg : (latTypeK p.fw p.F.lv2 i).FG := by
    haveI := isNoetherian_of_fg_of_noetherian _ hg.2.2.2.2.1
    exact Submodule.FG.of_le_of_isNoetherian (T := latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n)) inf_le_left
  have hN : ∀ σ' x, nrmR p.R.toRealDat i σ' (ι x) ≤ Real.exp (C * unitE p) * nrmK p.fw i (σ'.comp (algebraMap p.T.Q.c.F D.what₂.LL)) x := by
    intro σ' x
    obtain ⟨c, hc0, hcl, hcf⟩ := hm σ'
    obtain ⟨h, hx⟩ := hι x
    rw [hx, hcf ⟨x, h⟩]
    have hce : c ≤ Real.exp (C * unitE p) := by
      calc c = Real.exp (Real.log c) := (Real.exp_log hc0).symm
        _ ≤ Real.exp (C * unitE p) := Real.exp_le_exp.2 ((le_abs_self _).trans hcl)
    exact mul_le_mul_of_nonneg_right hce (petAt_nonneg _ _ _ _ _ _ _)
  have hS : latType p.R.toRealDat p.F.lv2 i =
      Submodule.span (𝓞 D.what₂.LL) (ι '' (latTypeK p.fw p.F.lv2 i : Set (VK p.fw i))) := by
    rw [hr]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hy1, hy2⟩
      have hy1' : y ∈ (ι '' (latW (p.T.U ((i : ℕ) + 1)) (wtZ (wtA (p.κ i)) (p.κ i).n) : Set (VK p.fw i))) := by
        rw [himg]; exact hy1
      obtain ⟨x, hx, rfl⟩ := hy1'
      refine ⟨x, ⟨hx, ?_⟩, rfl⟩
      show (x : p.T.R _) ∈ Submodule.span _ (typeK p.fw p.F.lv2 i)
      obtain ⟨h, hx'⟩ := hι x
      exact Submodule.subset_span ⟨h, hx' ▸ hy2⟩
    · rintro ⟨x, ⟨hx1, hx2⟩, rfl⟩
      refine ⟨(show ι x ∈ ((p.R.FW i).MK : Set (Fin (p.R.nW i) → D.what₂.LL)) by rw [← himg]; exact ⟨x, hx1, rfl⟩), ?_⟩
      have hsp : Submodule.span p.T.Q.c.F (typeK p.fw p.F.lv2 i) ≤
          ((spType p.R.toRealDat p.F.lv2 i).comap ι).map (VK p.fw i).subtype := by
        rw [Submodule.span_le]
        rintro f ⟨h, hf⟩
        have hfV : f ∈ VK p.fw i := by rw [VK, cuspW_wtZ]; exact h
        refine ⟨⟨f, hfV⟩, ?_, rfl⟩
        obtain ⟨h', e⟩ := hι ⟨f, hfV⟩
        show ι ⟨f, hfV⟩ ∈ spType p.R.toRealDat p.F.lv2 i
        rw [e]
        exact hf
      obtain ⟨z, hz, hzx⟩ := hsp hx2
      have : z = x := Subtype.ext hzx
      subst this
      exact hz
  have h0 : latTypeK p.fw p.F.lv2 i ≠ ⊥ := by
    intro h0
    apply hg.2.2.1
    rw [eq_bot_iff]
    refine (latGood_le _ _ _).trans ?_
    rw [hS, h0]
    simp
  have key := GlobalTheory.SlopeExt.slope_sq_sub_le_slope_sq_span p.T.Q.c.F D.what₂.LL (VK p.fw i) (Fin (p.R.toRealDat.nW i) → D.what₂.LL)
    (nrmK p.fw i) (nrmR p.R.toRealDat i) ι (latTypeK p.fw p.F.lv2 i) (C * unitE p) hg.2.2.2.1 hg.1 hc hli hfg h0 hN
  unfold CoreAt muCore
  rw [hS]
  linarith

theorem coreLe_of_gram_meas_rat : Gram → Meas → GlobalTheory.CovTop.Rat → CoreLe := by
  intro hg hm hr
  unfold Gram Meas GlobalTheory.CovTop.Rat CoreLe Lifts at *
  refine Closed.imp (Closed.and (Closed.and hg hm) hr) ?_
  rintro eps Fm CH - ⟨⟨⟨C1, -, hg'⟩, ⟨C, hC, hm'⟩⟩, ⟨C3, -, hr'⟩⟩
  refine ⟨2 * C, by linarith, ?_⟩
  obtain ⟨x0, h⟩ := (hg'.and hm').and hr'
  exact ⟨x0, fun x hx hle ι p hp i =>
    coreAt_of p i C ((h x hx hle ι p hp).1.1 i) ((h x hx hle ι p hp).1.2 i) ((h x hx hle ι p hp).2 i)⟩

example : Gram → Meas → GlobalTheory.CovTop.Rat → CoreLe := coreLe_of_gram_meas_rat

end GlobalTheory.CoreSlope
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrysActApply
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTCount

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {R : Type} [CommRing R] {b : GlobalTheory.UPel.HT.Base D R}
  {N : ℕ} {k : Type} [Field k] {t : Sp k ⟶ Sp R}

def crysAct (o₀ : GlobalTheory.UPel.HT.Obj b N t) : D.O →+* Module.End k (HdR o₀.A) :=
  RingHom.mk'
    { toFun x := haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)
      map_one' := by
        haveI := o₀.act.hom 1
        exact (push_congr (dp0 k) (𝟙 _) o₀.act.one).trans (push_id (dp0 k) (𝟙 _))
      map_mul' x y := by
        haveI := o₀.act.hom
        exact (push_congr (dp0 k) (𝟙 _) (o₀.act.mul x y)).trans (push_comp (dp0 k) (𝟙 _) _ _) }
    fun x y ↦ by
      haveI := o₀.act.hom
      haveI : IsMonHom (o₀.act.act x * o₀.act.act y) := o₀.act.add x y ▸ o₀.act.hom _
      exact (push_congr (dp0 k) (𝟙 _) (o₀.act.add x y)).trans (push_mul (dp0 k) (𝟙 _) _ _)

theorem crysAct_apply (o₀ : GlobalTheory.UPel.HT.Obj b N t) (x : D.O) :
    crysAct o₀ x = (haveI := o₀.act.hom x; push (dp0 k) (𝟙 _) (o₀.act.act x)) := rfl

def rhoPart (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  LinearMap.range (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1)

def lieZ (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k) : Submodule k (HdR o₀.A) :=
  Submodule.span k {z | ∃ (r : ℕ) (lam : Fin r → k) (c : Fin r → 𝓞 D.F) (y : HdR o₀.A), y ∈ rhoPart o₀ β ∧
    (∀ i, ∑ l, lam l * β (b.t i (c l)) = 0) ∧ z = ∑ l, lam l • crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y}

end GlobalTheory.HTCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeLocalUnitValueHolomorphicThird
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.MBLow.Cl GlobalTheory.MBLow.Cl.CubHol
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow.Cl.CubHol

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}

def phiXY (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y : Fin g → ℂ) : (DegPre.BF D ℂ).left ⟶ (G3 D.P.A).left :=
  (lift (fst _ _ ≫ ν.eA (d.ex x)) (lift (fst _ _ ≫ ν.eA (d.ex y)) (snd _ _))).left

theorem ptB_phiXY (ν : NumOf D ℂ N) (d : AB N.toNumB g) (x y z : Fin g → ℂ) :
    ptB ν d z ≫ phiXY ν d x y = pt3 ν d x y z := by
  rw [ptB, phiXY, pt3, ← Over.comp_left, comp_lift, lift_fst_assoc, comp_lift, lift_fst_assoc, lift_snd,
    Category.id_comp, Category.id_comp]

theorem isOpen_and_differentiableOn_valF_pt3_cubW : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ} (ν : NumOf D ℂ N) (d : AB N.toNumB g), Geo ν d → ∀ (x y : Fin g → ℂ) (j : thK → D.P.L.ι), IsOpen {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} ∧ DifferentiableOn ℂ (fun z => valF (pt3 ν d x y z) (cubW D j) (D.cub.t.s j).val) {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} := by
  intro R _ _ D _ N g ν d G x y j
  have hs : {z | ⊤ ≤ pt3 ν d x y z ⁻¹ᵁ cubW D j} = {z | ⊤ ≤ ptB ν d z ⁻¹ᵁ (phiXY ν d x y ⁻¹ᵁ cubW D j)} := by
    ext z
    simp only [Set.mem_setOf_eq, ← ptB_phiXY ν d x y z, Scheme.Hom.comp_preimage]
  obtain ⟨ho, hd⟩ := G.hol (phiXY ν d x y ⁻¹ᵁ cubW D j)
    (((phiXY ν d x y).appLE (cubW D j) (phiXY ν d x y ⁻¹ᵁ cubW D j) le_rfl).hom (D.cub.t.s j).val)
  rw [hs]
  refine ⟨ho, hd.congr fun z hz => ?_⟩
  have e := UnitVal.valF_appLE' (x := ptB ν d z) (phiXY ν d x y) (cubW D j) le_rfl hz (D.cub.t.s j).val
  rw [ptB_phiXY] at e
  exact e.symm

end GlobalTheory.MBLow.Cl.CubHol

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormClearDenominatorsAwayFromPlaceStatement
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_clear_denominators_away_from_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (G : WTZ E) (f : cuspW Xo c U G) (m : HeightOneSpectrum (𝓞 c.F) → ℝ), (Function.support m).Finite → (∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, ((m w : ℝ) : EReal) ≤ v f) → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (k : ℤ), (∀ v ∈ valSet Xo c (algCls Xo c) la, ((k : ℝ) : EReal) ≤ v f) → ∃ s : c.F, s ≠ 0 ∧ vLa la s = -k ∧ ∃ g ∈ latW U G, (g : Rul Xo c) = s • (f : Rul Xo c) := by
  first | exact @GlobalTheory.RefSum.Clear.clear | exact GlobalTheory.RefSum.Clear.clear | (intros; apply GlobalTheory.RefSum.Clear.clear <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsRatioOnComponentOfBirationalStatement
section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormsRatioOnComponent_of_birational : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), ∀ (Z : Comp Xo c) (G : WTZ E), BirOn U Z G → RatioOn U Z G := by
  first | exact @GlobalTheory.DegVal.ratioOn_of_birOn | exact GlobalTheory.DegVal.ratioOn_of_birOn | (intros; apply GlobalTheory.DegVal.ratioOn_of_birOn <;> assumption)
end

