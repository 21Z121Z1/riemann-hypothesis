import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3209
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2876
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3203
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3205
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3206
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearIndependentComplexSectionValuesOfInt
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HSAmp.IndepCx

theorem finiteType_int {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) {U : X.Opens} (hU : IsAffineOpen U) : Algebra.FiniteType ℤ Γ(X, U) := by
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have h1 : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).FiniteType :=
    (p.finiteType_appLE (isAffineOpen_top _) hU _).comp
      (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).2)
  have := hX.finite
  have h0 : (algebraMap ℤ k).FiniteType := RingHom.finiteType_algebraMap.2 inferInstance
  have h2 := h1.comp h0
  rw [RingHom.ext_int ((ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).comp (algebraMap ℤ k)) (algebraMap ℤ Γ(X, U))] at h2
  exact RingHom.finiteType_algebraMap.1 h2

end GlobalTheory.HSAmp.IndepCx

namespace GlobalTheory.HSAmp

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX) in

theorem linearIndependent_vals : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ) (ι : Type) [Fintype ι] (f : ι → X.functionField),
    (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → ∀ c : ι → ℂ,
    (∀ (σ : k →+* ℂ) (y : CxPts p σ), ∑ i, c i * val P a b σ y (f i) = 0) → c = 0 := by
  intro k _ X _ p D hX P a b ι _ f hf hli c hc
  classical
  obtain ⟨i, hi⟩ := exists_chart P.L.isLB (genericPoint X)
  obtain ⟨j, hj⟩ := exists_chart P.A.isLB (genericPoint X)
  obtain ⟨U, hU, hgU, hle⟩ := exists_isAffineOpen_mem_and_subset (x := genericPoint X)
    (U := P.L.B.U i ⊓ P.A.B.U j) ⟨hi, hj⟩
  have hl : U ≤ P.L.B.U i := fun x hx => (hle hx).1
  have hr : U ≤ P.A.B.U j := fun x hx => (hle hx).2
  have : Nonempty U := ⟨⟨_, hgU⟩⟩
  have : CharZero Γ(X, U) :=
    ((resG X (le_top : U ≤ ⊤)).charZero_iff (map_injective_of_isIntegral X _)).1 hX.charZero
  have := IndepCx.finiteType_int hX hU
  choose g hg using fun l => exists_fnOf_eq hgU fun x hx => hf l x i j (hl hx) (hr hx)
  have hu0 : (P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b ≠ 0 :=
    mul_ne_zero (zpow_ne_zero _ (P.r i).ne_zero) (zpow_ne_zero _ (P.r' j).ne_zero)
  have hloc : ∀ l, P.loc a b (f l) i j = f l * ((P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b) :=
    fun l => by simp only [Pair.loc]; ring
  have hgli : LinearIndependent ℤ g := by
    rw [Fintype.linearIndependent_iff] at hli ⊢
    intro n hn
    apply hli n
    have h1 := congrArg (fnOf U hgU) hn
    rw [map_sum, map_zero] at h1
    simp only [map_zsmul, hg, hloc] at h1
    have h2 : (∑ l, n l • f l) * ((P.r i : X.functionField) ^ a * (P.r' j : X.functionField) ^ b) = 0 := by
      rw [Finset.sum_mul]; simpa only [smul_mul_assoc] using h1
    exact (mul_eq_zero.1 h2).resolve_right hu0
  set e := Fintype.equivFin ι
  obtain ⟨x, hx⟩ := GlobalTheory.CxPointsSep.exists_det_ne_zero Γ(X, U) (Fintype.card ι) (g ∘ e.symm)
    (hgli.comp _ e.symm.injective)
  have key : ∀ s, ∑ l, c l * x s (g l) = 0 := by
    intro s
    have hy : ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl) ∈ ptsIn p ((x s).comp (algX p U)) U :=
      ofHom_mem hU _ _
    obtain ⟨θ, hθ, hval⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b _ _ i j (ptsIn_mono hl hy) (ptsIn_mono hr hy)
    have h0 := hc _ (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl))
    have hθ0 : θ ≠ 0 := by
      intro h; rw [h, norm_zero] at hθ; exact zero_ne_one hθ
    set E : ℂ := ((Real.exp (-(a * (P.L.φ ((x s).comp (algX p U))).φ i
      (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl)) +
      b * (P.A.φ ((x s).comp (algX p U))).φ j (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl))) / 2) : ℝ) : ℂ)
      with hEdef
    have hE : E ≠ 0 := Complex.ofReal_ne_zero.2 (Real.exp_pos _).ne'
    have hv : ∀ l, val P a b _ (ofHom (σ := (x s).comp (algX p U)) hU (x s) (fun _ => rfl)) (f l) =
        θ * E * x s (g l) := by
      intro l
      rw [hval (f l) (hf l), ← hg l, ratVal_fnOf hy hgU, ev_ofHom]
      ring
    simp only [hv] at h0
    have h3 : θ * E * ∑ l, c l * x s (g l) = 0 := by
      rw [Finset.mul_sum, ← h0]
      exact Finset.sum_congr rfl fun l _ => by ring
    exact (mul_eq_zero.1 h3).resolve_left (mul_ne_zero hθ0 hE)
  have hM : Matrix.mulVec (Matrix.of fun s t => x s ((g ∘ e.symm) t)) (c ∘ e.symm) = 0 := by
    funext s
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Function.comp_apply, Pi.zero_apply]
    rw [← key s, ← e.symm.sum_comp (fun l => c l * x s (g l))]
    exact Finset.sum_congr rfl fun t _ => mul_comm _ _
  have hz := Matrix.eq_zero_of_mulVec_eq_zero hx hM
  funext l
  simpa using congrFun hz (e l)

end GlobalTheory.HSAmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalUnitAbsoluteValueCriterion
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Pad

theorem w_mul_exp_cmp_iff : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) [Fact (resP v).Prime] (k : ℕ) (gn : Fin k → ℝ), (∀ l, 0 < gn l) → ∀ b : AlgebraicClosure F, (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) ≤ 1 ↔ ‖ioOf (resP v) ε b‖ ≤ ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) = 1 ↔ ‖ioOf (resP v) ε b‖ = ∏ l, gn l) ∧ (ε.w b * Real.exp (-∑ l, (-Real.log (ε.w (resP v)) / Real.log (resP v)) * Real.log (gn l)) < 1 ↔ ‖ioOf (resP v) ε b‖ < ∏ l, gn l) := by
  intro F _ _ v ε _ k gn hgn b
  have hpr : (resP v).Prime := Fact.out
  have hio := ioOf_le_one_iff (resP v) (residueCharacteristic_mem v) ε
  have hlog := log_w_eq (resP v) ε (ioOf (resP v) ε) hio
  have hwp : ε.w ((resP v : ℕ) : AlgebraicClosure F) < 1 := by
    have h1 : ((resP v : ℕ) : AlgebraicClosure F) =
        algebraMap F _ (algebraMap (𝓞 F) F ((resP v : ℕ) : 𝓞 F)) := by simp
    rw [h1, ε.w_alg]
    exact (v.adicAbv_coe_lt_one_iff (K := F) (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).2 (residueCharacteristic_mem v)
  have hwp0 : 0 < ε.w ((resP v : ℕ) : AlgebraicClosure F) :=
    ε.w.pos (Nat.cast_ne_zero.2 hpr.ne_zero)
  have hlp : 0 < Real.log ((resP v : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hpr.one_lt)
  set c := -Real.log (ε.w ((resP v : ℕ) : AlgebraicClosure F)) / Real.log ((resP v : ℕ) : ℝ) with hc
  have hc0 : 0 < c := div_pos (neg_pos.2 (Real.log_neg hwp0 hwp)) hlp
  have hwb : ε.w b = ‖ioOf (resP v) ε b‖ ^ c := by
    rcases eq_or_ne b 0 with rfl | hb
    · simp [Real.zero_rpow hc0.ne']
    · have hb' : 0 < ‖ioOf (resP v) ε b‖ := norm_pos_iff.2 ((map_ne_zero _).2 hb)
      rw [← Real.exp_log (ε.w.pos hb), hlog b, Real.rpow_def_of_pos hb', mul_comm]
  have hν : 0 < ∏ l, gn l := Finset.prod_pos fun l _ => hgn l
  have hexp : Real.exp (-∑ l, c * Real.log (gn l)) = (∏ l, gn l) ^ (-c) := by
    rw [Real.rpow_def_of_pos hν, ← Finset.mul_sum, Real.log_prod (fun l _ => (hgn l).ne')]
    ring_nf
  have hkey : ε.w b * Real.exp (-∑ l, c * Real.log (gn l)) = (‖ioOf (resP v) ε b‖ / ∏ l, gn l) ^ c := by
    rw [hexp, hwb, Real.div_rpow (norm_nonneg _) hν.le, Real.rpow_neg hν.le, div_eq_mul_inv]
  rw [hkey]
  have hx : 0 ≤ ‖ioOf (resP v) ε b‖ / ∏ l, gn l := div_nonneg (norm_nonneg _) hν.le
  have hle : (‖ioOf (resP v) ε b‖ / ∏ l, gn l) ^ c ≤ 1 ↔ ‖ioOf (resP v) ε b‖ ≤ ∏ l, gn l := by
    rw [← Real.one_rpow c, Real.rpow_le_rpow_iff hx zero_le_one hc0, div_le_one hν]
  have hge : 1 ≤ (‖ioOf (resP v) ε b‖ / ∏ l, gn l) ^ c ↔ ∏ l, gn l ≤ ‖ioOf (resP v) ε b‖ := by
    rw [← Real.one_rpow c, Real.rpow_le_rpow_iff zero_le_one hx hc0, one_le_div hν]
  refine ⟨hle, ?_, ?_⟩
  · rw [le_antisymm_iff, hle, hge, ← le_antisymm_iff]
  · rw [← Real.one_rpow c, Real.rpow_lt_rpow_iff hx zero_le_one hc0, div_lt_one hν]

end GlobalTheory.ShFam.Pad
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocallyIntegralOfRegularAtAllTraits
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem locInt_of_traitReg : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [CharZero R] (M : Modif R) (G : Over M.S), Smooth G.hom → QuasiCompact G.hom → GeometricallyIrreducible G.hom → ∀ (L : LB G.left), L.IsLB → ∀ (Y : Scheme.{0}) (α : Y ⟶ G.left) (t : Y ⟶ Sp (FractionRing R)) (hpb : IsPullback α t G.hom M.gp) (k : ℕ) (s : SecK L α k), TraitReg M G L s → LocInt M G L α t hpb.w s := by
  intro R _ _ _ _ _ M G hsm hqc hgi L hL Y α t hpb k s hs
  have h4 := GlobalTheory.T.integral_at_closedFibre_of_regular_at_all_traits R M G hsm hqc hgi L hL Y α t hpb k s hs
  have h5 := GlobalTheory.T.isIntegralSection_everywhere_of_closedFibre R M G hsm hqc hgi L hL Y α t hpb k s h4
  intro j W U hW hWU hWa hUa
  exact GlobalTheory.T.integral_element_affine_section_generated R M G hsm Y α t hpb W U hWU hWa hUa _
    (GlobalTheory.T.chartValue_isIntegral_of_integral_at_points L α k s j W hW hWa (GlobalTheory.T.isAffineOpen_preimage_genericBaseChange_modification R M G Y α t hpb W hWa) (fun x _ => h5 x))

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernIntegralPointClosureClosedSubschemeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_chern_integral_point_closure_closed_subscheme : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ), IsProjOver p → ∀ [IsIntegral Y] (π : Y ⟶ X) [IsClosedImmersion π] (hπ : π ≫ p = q) (D : ℕ) (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), (CycIntg L f (π (genericPoint Y)) ↔ Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y))) ∧ cycInt L f (π (genericPoint Y)) = Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) := by
  first | exact @GlobalTheory.Mix.cycInt_of_closedImmersion | exact GlobalTheory.Mix.cycInt_of_closedImmersion | (intros; apply GlobalTheory.Mix.cycInt_of_closedImmersion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightInductiveRhsSymmIsometryInvariant
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

namespace GlobalTheory.MixHt

theorem recVal_iso_symm : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y]
    (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → ∀ T, IsMix q e T →
    ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r),
    (∀ L L' : Fin e → HermLB q, (∀ a, (L a).Isometric (L' a)) → recVal (T e L) L M hr = recVal (T e L') L' M hr) ∧
    (∀ (L : Fin e → HermLB q) (τ : Equiv.Perm (Fin e)),
      recVal (T e fun a => L (τ a)) (fun a => L (τ a)) M hr = recVal (T e L) L M hr) ∧
    (∀ (L : Fin e → HermLB q) (M' : HermLB q), M.Isometric M' → ∃ (r' : M'.B.ι → Y.functionFieldˣ)
      (hr' : IsRatSec M'.B r'), recVal (T e L) L M' hr' = recVal (T e L) L M hr) := by
  intro _ k _ Y _ _ q hq e hY T hT M r hr
  have hd : ∀ z : Y, ((M.div hr).mult z : ℝ) ≠ 0 → HasDim z e := fun z hz =>
    ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k Y q hq e hY).1 z).1
      (CartierDiv.coheight_eq_one_of_mult_ne_zero fun h => hz (by rw [h]; simp))
  refine ⟨fun L L' h => ?_, fun L τ => ?_, fun L M' h => ?_⟩
  · unfold recVal
    rw [(GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr k Y q e L M r hr).1 L' h]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((M.div hr).mult z : ℝ) = 0
    · simp [hz]
    · rw [hT.iso e L L' z le_rfl (hd z hz) h]
  · unfold recVal
    rw [(GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr k Y q e L M r hr).2.1 τ]
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((M.div hr).mult z : ℝ) = 0
    · simp [hz]
    · rw [hT.symm e L τ z le_rfl (hd z hz)]
  · obtain ⟨r', hr', hdiv, hlog⟩ := h.exists_isRatSec hr
    refine ⟨r', hr', ?_⟩
    unfold recVal
    rw [(GlobalTheory.T.mixedArchLogNormIntegral_isometry_symm_congr k Y q e L M r hr).2.2 M' r' hr' hdiv hlog, hdiv]

end GlobalTheory.MixHt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedHeightUniqueRestrictClosedSubscheme
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt

set_option autoImplicit false

namespace GlobalTheory.MixHt.Uniq

variable {k : Type} [CommRing k]

theorem isometric_of_refines {X : Scheme.{0}} {p : X ⟶ Sp k} {N L : HermLB p} {π : N.B.ι → L.B.ι}
    (h : TwistTop.Refines N L π 0) : N.Isometric L :=
  HermLB.isometric_of_chart π h.le (fun x j j' hj hj' => h.g X (𝟙 X) x j j' hj hj')
    fun σ j y hy => ((h.φ σ j y hy).trans (add_zero _)).symm

theorem card_residueField {X Z : Scheme.{0}} (i : Z ⟶ X) [IsClosedImmersion i] (z : Z) :
    Nat.card (X.residueField (i z)) = Nat.card (Z.residueField z) := by
  refine Nat.card_eq_of_bijective (i.residueFieldMap z) ⟨(i.residueFieldMap z).hom.injective, fun a => ?_⟩
  obtain ⟨b, rfl⟩ := Z.residue_surjective z a
  obtain ⟨c, rfl⟩ := i.stalkMap_surjective z b
  exact ⟨X.residue _ c, (ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i z) c :)⟩

end GlobalTheory.MixHt.Uniq

open GlobalTheory.MixHt.Uniq in

theorem GlobalTheory.MixHt.eq_of_isMix : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k), IsAmb p →
    ∀ (i : Y ⟶ X) [IsClosedImmersion i] (hi : i ≫ p = q) (m m' : ℕ) T T', IsMix p m T → IsMix q m' T' →
    ∀ d : ℕ, d ≤ m → d ≤ m' → ∀ (L : Fin d → HermLB p) (L' : Fin d → HermLB q),
    (∀ a, ((L a).pull i hi).Isometric (L' a)) → ∀ y : Y, HasDim y d → T d L (i y) = T' d L' y := by
  intro k _ X Y p q hp i _ hi m m' T T' hT hT' d
  have hq : IsAmb q := hi ▸ hp.sub i
  have DX := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k X p hp
  have DY := GlobalTheory.T.hasPointClosureDim_basic_projArithAmbient k Y q hq
  haveI : IsNoetherian Y := hq.isNoetherian
  induction d with
  | zero =>
    intro _ _ L L' _ y hy
    have hy' : HasDim (i y) 0 := (DX.2.2.2.2.1 Y i y 0).2 hy
    rw [hT.zero L (i y) hy', hT'.zero L' y hy, card_residueField i y]
  | succ e ih =>
    intro hm hm' L L' hL y hy
    have hW : IsAmb (cloι y ≫ q) := hq.sub (cloι y)
    have hgen : HasDim (genericPoint (clo y)) (e + 1) :=
      (DY.2.2.2.2.1 (clo y) (cloι y) (genericPoint (clo y)) (e + 1)).1 (by rw [cloι_genericPoint]; exact hy)
    have hdim : topologicalKrullDim (clo y) = ((e + 1 : ℕ) : WithBot ℕ∞) :=
      (DY.2.2.2.2.2 (clo y) (e + 1)).1 hgen
    obtain ⟨r, hr⟩ := exists_isRatSec ((L' 0).pull (cloι y) rfl).isLB
    have hij : (cloι y ≫ i) ≫ p = cloι y ≫ q := by rw [Category.assoc, hi]
    have hiso : ∀ (A : HermLB p) (A' : HermLB q), (A.pull i hi).Isometric A' →
        (A.pull (cloι y ≫ i) hij).Isometric (A'.pull (cloι y) rfl) := fun A A' h =>
      (isometric_of_refines (HermLB.refines_pull_pull A i hi (cloι y) rfl hij)).symm.trans (h.pull (cloι y) rfl)
    have h1 := hT'.recur (clo y) (cloι y ≫ q) (cloι y) rfl e hm' hdim (L' 0) (Fin.tail L')
      ((L' 0).pull (cloι y) rfl) (fun a => (L' a.succ).pull (cloι y) rfl) (HermLB.Isometric.refl _)
      (fun a => HermLB.Isometric.refl _) r hr
    have h2 := hT.recur (clo y) (cloι y ≫ q) (cloι y ≫ i) hij e hm hdim (L 0) (Fin.tail L)
      ((L' 0).pull (cloι y) rfl) (fun a => (L' a.succ).pull (cloι y) rfl) (hiso _ _ (hL 0))
      (fun a => hiso _ _ (hL a.succ)) r hr
    rw [Fin.cons_self_tail, cloι_genericPoint] at h1
    rw [Fin.cons_self_tail, Scheme.Hom.comp_apply, cloι_genericPoint] at h2
    rw [h1, h2]
    unfold recVal
    congr 1
    refine finsum_congr fun z => ?_
    by_cases hz : ((((L' 0).pull (cloι y) rfl)).div hr).mult z = 0
    · simp [hz]
    · have hz1 := CartierDiv.coheight_eq_one_of_mult_ne_zero hz
      have hzd : HasDim z e := ((GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith k (clo y) (cloι y ≫ q) hW e hdim).1 z).1 hz1
      have hjz : HasDim (cloι y z) e := (DY.2.2.2.2.1 (clo y) (cloι y) z e).2 hzd
      dsimp only
      rw [Scheme.Hom.comp_apply, ih (by omega) (by omega) (Fin.tail L) (Fin.tail L') (fun a => hL a.succ) _ hjz]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralPullbackGenericallyFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.PushInt

theorem mixInt_pull : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : Fin D → MLine p σ) (f : CxPts p σ → ℝ), Measurable f → (Intg (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) ↔ Intg L f) ∧ Mix.int (fun i => (L i).pull π hπ) (fun y => f (ptMap π hπ σ y)) = π.residueDegree (genericPoint Y) * Mix.int L f := by
  intro F _ X Y _ _ p q σ D h1 h2 h3 π hπ hg hk L f hf
  have hm : Measurable (ptMap π hπ σ) := (PtsOver.continuous_map π hπ (spMap σ)).measurable
  have key := fun ε => GlobalTheory.T.mixedChernMeasure_map_pullback_genericallyFinite F X Y p q σ D h1 h2 h3 π hπ hg hk L ε
  have hc0 : ((π.residueDegree (genericPoint Y) : ENNReal)) ≠ 0 := by exact_mod_cast hk
  have hcT : ((π.residueDegree (genericPoint Y) : ENNReal)) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hI : ∀ ε, Integrable (fun y => f (ptMap π hπ σ y)) (part (fun i => (L i).pull π hπ) ε) ↔
      Integrable f (part L ε) := by
    intro ε
    have e := integrable_map_measure (μ := part (fun i => (L i).pull π hπ) ε) hf.aestronglyMeasurable hm.aemeasurable
    rw [key ε, integrable_smul_measure hc0 hcT] at e
    exact e.symm
  have hJ : ∀ ε, ∫ y, f (ptMap π hπ σ y) ∂(part (fun i => (L i).pull π hπ) ε) =
      (π.residueDegree (genericPoint Y) : ℝ) * ∫ y, f y ∂(part L ε) := by
    intro ε
    rw [← integral_map hm.aemeasurable hf.aestronglyMeasurable, key ε, integral_smul_measure]
    simp
  refine ⟨?_, ?_⟩
  · simp only [Intg, hI]
  · simp only [Mix.int, hJ]
    ring

end GlobalTheory.PushInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAlongHomsDescendsAbelianPartStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mumfordBundle_iso_along_homs_descends_abelianPart : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], AdmBase R (maximalIdeal R) → ∀ (D₁ D₂ : DegData R (maximalIdeal R)) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (f g : G₁ ⟶ G₂) (fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A), IsMonHom f → IsMonHom g → IsMonHom fB → IsMonHom gB → Over₀ U₁.toUnifPre U₂.toUnifPre f fB → Over₀ U₁.toUnifPre U₂.toUnifPre g gB → LBIso (abelian₂ G₁ U₁.LG.L) ((abelian₂ G₂ U₂.LG.L).pull (lift (fst G₁ G₁ ≫ f) (snd G₁ G₁ ≫ g) : G2 G₁ ⟶ G2 G₂).left) → LBIso (abelian₂ D₁.toPre.P.A D₁.toPre.P.L) ((abelian₂ D₂.toPre.P.A D₂.toPre.P.L).pull (lift (fst D₁.toPre.P.A D₁.toPre.P.A ≫ fB) (snd D₁.toPre.P.A D₁.toPre.P.A ≫ gB) : G2 D₁.toPre.P.A ⟶ G2 D₂.toPre.P.A).left) := by
  first | exact @GlobalTheory.HomMum.lbIso_descends | exact GlobalTheory.HomMum.lbIso_descends | (intros; apply GlobalTheory.HomMum.lbIso_descends <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatDegreeMinpolyEqDegCentralSimpleCommCentraliseStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natDegree_minpoly_eq_deg_centralSimple_commCentraliser : ∀ (F C : Type) [Field F] [Ring C] [Algebra F C] [Algebra.IsCentral F C] [IsSimpleRing C] [FiniteDimensional F C] (n : ℕ), Module.finrank F C = n ^ 2 → ∀ c : C, (minpoly F c).Separable → (∀ a b : C, Commute a c → Commute b c → Commute a b) → (minpoly F c).natDegree = n := by
  first | (exact @GlobalTheory.RegDeg.natDegree_minpoly_eq) | (exact GlobalTheory.RegDeg.natDegree_minpoly_eq) | (intros; apply GlobalTheory.RegDeg.natDegree_minpoly_eq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEvalCommutesSubstAndAlgebraMap
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem evA_subst_and_map : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A], (∀ (τ : Type) [Finite τ] (φ : MvPowerSeries τ k →ₐ[k] A), (∀ t, IsNilpotent (φ (X t))) → ∀ a : σ → MvPowerSeries τ k, (∀ i, constantCoeff (a i) = 0) → ∀ (y : σ → A) (hy : ∀ i, IsNilpotent (y i)), (∀ i, φ (a i) = y i) → ∀ f : MvPowerSeries σ k, φ (subst a f) = evA k y hy f) ∧ ∀ (B : Type) [CommRing B] [Algebra k B] (g : A →ₐ[k] B) (x : σ → A) (hx : ∀ i, IsNilpotent (x i)) (y : σ → B) (hy : ∀ i, IsNilpotent (y i)), (∀ i, g (x i) = y i) → ∀ f : MvPowerSeries σ k, g (evA k x hx f) = evA k y hy f := by
  intro k _ σ _ A _ _
  refine ⟨?_, ?_⟩
  · intro τ _ φ _ a ha y hy hφa f
    have hs : HasSubst a := hasSubst_of_constantCoeff_zero ha
    have key : evA k y hy = φ.comp (substAlgHom hs) := by
      refine GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k σ A _ _ (fun i => ?_) (fun i => ?_)
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A y hy i]; exact hy i
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A y hy i, AlgHom.comp_apply, coe_substAlgHom, subst_X hs, hφa]
    rw [key, AlgHom.comp_apply, coe_substAlgHom]
  · intro B _ _ g x hx y hy hg f
    have key : evA k y hy = g.comp (evA k x hx) := by
      refine GlobalTheory.T.mvPowerSeries_algHom_ext_of_isNilpotent_X k σ B _ _ (fun i => ?_) (fun i => ?_)
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ B y hy i]; exact hy i
      · rw [GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ B y hy i, AlgHom.comp_apply, GlobalTheory.T.powerSeriesEvalAtNilpotent_X_eq_coordinate k σ A x hx i, hg]
    rw [key, AlgHom.comp_apply]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyModuliMapOfMarkedPeriodIsometryStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_moduliMap_of_marked_period_isometry : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (o o' : Obj b N (spMap σ)) h hL h' hL' (D' D'' : PLat D.O D.inv) t t' Q Q' e e' (w : D'.La ≃ₗ[D.O] D''.La) (u : (Fin D.g → ℂ) ≃ₗ[ℂ] (Fin D.g → ℂ)), 0 < N → UnifAt (o.fam h hL) σ ρ N D' t Q (𝟙 _) e → UnifAt (o'.fam h' hL') σ ρ N D'' t' Q' (𝟙 _) e' → IsMarkedIsom N D' D'' t t' w → (∀ x, Q' (w x) = u (Q x)) → Nonempty (ObjMap o o' (𝟙 _)) := by
  first | exact @GlobalTheory.HTIso.nonempty_objMap_of_markedIsom | exact GlobalTheory.HTIso.nonempty_objMap_of_markedIsom | (intros; apply GlobalTheory.HTIso.nonempty_objMap_of_markedIsom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyTwistedSectionComponentStatement
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_twisted_section_component : Hypotheses2 → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ c₁ : ℝ, GlobalTheory.FlatLine.FlatExistsAt Y.U (xiR D) c₁ → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, Nonempty (GlobalTheory.FlatTw.TwSec Y.U (xiR D) Z (wtOf (T.Q.Dw j) 0 1)) := by
  first | exact @GlobalTheory.KeyTwDeep.exists_twSec_keyRoot_deep | exact GlobalTheory.KeyTwDeep.exists_twSec_keyRoot_deep | (intros; apply GlobalTheory.KeyTwDeep.exists_twSec_keyRoot_deep <;> assumption)
end

