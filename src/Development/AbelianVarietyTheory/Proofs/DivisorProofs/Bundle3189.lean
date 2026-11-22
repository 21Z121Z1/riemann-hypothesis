import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3148
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3149
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2517
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3071
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0804
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsMulVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobTwistBaseChangeHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3172
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3175
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3171
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3165
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2874
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2564
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3154
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3150
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2982
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3105
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3123
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightOneIffPointClosureDimProjArithStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coheight_one_iff_pointClosure_dim_projArith : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 : ℕ) → (∀ z : Y, Order.coheight z = 1 ↔ HasDim z e) ∧ ∀ (z : Y) (w : clo z), Order.coheight z = 1 → (topologicalKrullDim (clo z) = e ∧ (Order.coheight w = 1 ↔ Order.coheight (cloι z w) = 2)) := by
  first | exact @GlobalTheory.MixHt.dimOne | exact GlobalTheory.MixHt.dimOne | (intros; apply GlobalTheory.MixHt.dimOne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokLen
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField Matrix IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.DiscreteGroups.LocalClassField
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKGeo
open scoped TensorProduct
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.Frame

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {k : Type} [Field k] [CharP k p]
  [PerfectRing k p] {T : Theory p} {red : (Obar p).toSubring →+* k} {r : ℕ} {H : PDivGroup p k}
  {act : D.O → (H ⟶ H)} {rat : ℤ → (H ⟶ H) → Prop} {d : (w : Fin G.m) → GL (Fin G.n) (KQ p (G.Fw w) r)}

def part (fr : Frame L T red r H act rat d) (w : Fin G.m) : Submodule (WittVector p k) (T.M H) :=
  Submodule.span (WittVector p k) (Set.range (fr.B w))

def partF (fr : Frame L T red r H act rat d) (w : Fin G.m) : Submodule (WittVector p k) (T.M H) :=
  Submodule.span (WittVector p k) ((fun x => T.F H x) '' (fr.part w : Set (T.M H)))

def cokLen (fr : Frame L T red r H act rat d) (w : Fin G.m) : ℕ∞ :=
  Module.length (WittVector p k) (fr.part w ⧸ (fr.partF w).comap (fr.part w).subtype)

end GlobalTheory.LKGeo.Frame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleFormsCocyclesDegreeTwoDifferCoboundaryStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compatibleFormsCocycles_degreeTwo_differ_coboundary : ∀ (R R' : Type) [CommRing R] [CommRing R'] (I : Ideal R) (I' : Ideal R') (κ : DividedPowers I) (κ' : DividedPowers I') (X X' : Scheme.{0}) (t : X ⟶ Sp R) (t' : X' ⟶ Sp R') (σ : R →+* R') (φ₀ : X' ⟶ X) (m : IsMor κ t κ' t' σ φ₀) (k : (KK κ t).Z2) (k' : (KK κ' t').Z2) (f : Z2 (O κ t)) (f' : Z2 (O κ' t')), k.1.1 = f.1 → k'.1.1 = f'.1 → H2.mk _ f' = m.pull2 (H2.mk _ f) → ∃ g, (KK κ' t').D1 g = (morMap m).p2 k.1 - k'.1 := by
  first | exact @GlobalTheory.PDForm.ClsTwo.cob_of_class_eq | exact GlobalTheory.PDForm.ClsTwo.cob_of_class_eq | (intros; apply GlobalTheory.PDForm.ClsTwo.cob_of_class_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsSmoothAtLogUnitAddGradedLength
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem cInfAt_ratVal_on {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {κ : Type} [Fintype κ] {f : κ → X.Fn}
    {y : CxPts X.str σ} (hf : ∀ a, RegAt (under y) (f a)) {G : (κ → ℂ) → ℝ} {O : Set (κ → ℂ)} (hO : IsOpen O)
    (hG : ContDiffOn ℝ ∞ G O) (hy : (fun a => ratVal (f a) y) ∈ O) :
    CInfAt (fun z => G fun a => ratVal (f a) z) y := by
  choose U hyU g e using fun a => (hf a).exists_fnOf
  let W : X.X.Opens := ⟨⋂ a, U a, isOpen_iInter_of_finite fun a => (U a).isOpen⟩
  have hW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 (Set.mem_iInter.2 hyU)
  have hle (a) : W ≤ U a := Set.iInter_subset (fun a => (U a : Set X.X)) a
  have hev (z : CxPts X.str σ) (hz : z ∈ ptsIn X.str σ W) :
      (fun a => ev X.str σ W (resG X.X (hle a) (g a)) z) = fun a => ratVal (f a) z := by
    funext a
    rw [ev_res (hle a) hz, ← e a, ratVal_fnOf (ptsIn_mono (hle a) hz)]
  refine ⟨W, κ, inferInstance, fun a => resG X.X (hle a) (g a), G, O, hW, hO, ?_, hG, ?_⟩
  · rw [hev y hW]; exact hy
  · filter_upwards [(isOpen_ptsIn W).mem_nhds hW] with z hz
    rw [hev z hz]

theorem cInfAt_neg_log_normSq_ratVal {F : Type} [Field F] {X : Var F} {σ : F →+* ℂ} {y : CxPts X.str σ} {u : X.Fn}
    (hu : UnitAt (under y) u) : CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2)) y := by
  have hO : IsOpen {w : Unit → ℂ | w () ≠ 0} := isOpen_ne_fun (continuous_apply ()) continuous_const
  have hG : ContDiffOn ℝ ∞ (fun w : Unit → ℂ => -Real.log (‖w ()‖ ^ 2)) {w | w () ≠ 0} := by
    intro w hw
    have h1 : ContDiffAt ℝ ∞ (fun w : Unit → ℂ => ‖w ()‖ ^ 2) w :=
      ((contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ ())).contDiffAt
    have h2 : ‖w ()‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hw)
    exact (h1.log h2).neg.contDiffWithinAt
  exact cInfAt_ratVal_on (κ := Unit) (f := fun _ => u) (fun _ => hu.regAt) hO hG (ratVal_ne_zero hu)

end GlobalTheory.ChernCalc

set_option maxHeartbeats 1000000 in
theorem GlobalTheory.ChernCalc.cInfAt_logUnit_grD : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m k : ι → ℕ) (E : Fr (ratOf X) m k)
    (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricFr E H → ∀ (y : CxPts X.str σ), ∀ A ∈ E.S (under y),
    ∀ u : X.Fn, UnitAt (under y) u → ∀ (τ : ι) (i : Fin (m τ)),
      CInfAt (fun z => -Real.log (‖ratVal u z‖ ^ 2) - Real.log (grD (H A z τ) i)) y := by
  intro F _ σ X ι _ m k E H hH y A hA u hu τ i
  refine (GlobalTheory.ChernCalc.cInfAt_neg_log_normSq_ratVal hu).add ?_ |>.congr (Eventually.of_forall fun z => sub_eq_add_neg _ _)
  have := X.smooth_str
  obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
  have hev := ((GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m k E H hH y A hA τ).2 c hc)
  obtain ⟨O, hOP, hOo, hyO⟩ := eventually_nhds_iff.1 hev
  have hS : IsOpen (c.e.source ∩ c.e ⁻¹' O) := c.e.isOpen_inter_preimage hOo
  refine cInfAt_of_chart hS c ?_ hc ⟨hc, hyO⟩
  intro v hv
  have hvO : v ∈ O := by
    have := hv.2.2
    rwa [Set.mem_preimage, c.e.right_inv hv.1] at this
  obtain ⟨hsm, hpd⟩ := hOP v hvO
  have hd := (ldPart_grD_smooth _ _ _ v hsm hpd).2 i
  have hpos := ((GlobalTheory.T.gramLowerTriangularFactor_posDef_properties _ _ hpd).2.1 i).1
  exact (hd.log hpos.ne').neg.contDiffWithinAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationExpUniqueFullLevelMarkingStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexUniformisation_exp_unique_full_level_marking : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (R : Type) [CommRing R] (σ : R →+* ℂ) (Λ : Type) (F : Fam R O Λ g) (N : ℕ) (D' : PLat O bar) (t : Λ → D'.La) P (y : Sp ℂ ⟶ F.X) e e', 3 ≤ N → FullMark N D' t → UnifAt F σ ρ N D' t P y e → UnifAt F σ ρ N D' t P y e' → e = e' := by
  first | exact @GlobalTheory.PELU.unifAt_exp_unique | exact GlobalTheory.PELU.unifAt_exp_unique | (intros; apply GlobalTheory.PELU.unifAt_exp_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegree
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem isTopForm_mul_topDens : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {ρ : CxPts X.str σ → ℝ}, Continuous ρ → IsTopForm (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H c y) (ptsIn X.str σ O) := by
  intro F _ σ X m E O H hM ρ hρ
  refine ⟨?_, ?_⟩
  · intro c c' y hy hc hc'
    have hA := (E.nonempty (under y)).choose_spec
    simp only [topDens]
    rw [chernTop_frame_chart_trans E O H hM _ hy c c' hc hc' hA hA]
    ring
  · intro c
    refine GlobalTheory.T.aemeasurable_chart_of_locally_continuous_density c.e (d := fun z => ρ z * topDens E H c z) (isOpen_ptsIn O) ?_
    intro y hy hc
    have hA := (E.nonempty (under y)).choose_spec
    refine ⟨fun v => ρ (c.e.symm v) * chernTop (MvPolynomial.X ((), X.dim))
      (fun w => H (E.nonempty (under y)).choose (c.e.symm w)) v, ?_, ?_⟩
    · have h1 : ContinuousAt (fun v => ρ (c.e.symm v)) (c.e y) :=
        hρ.continuousAt.comp (c.e.continuousAt_symm (c.e.map_source hc))
      have hsm := hM.mContDiffAt_chart hy c hc hA ()
      have hu := hM.isUnit_det_chart hy c hc hA ()
      have h2 : ContinuousAt (fun v => chernTop (MvPolynomial.X ((), X.dim))
          (fun w => H (E.nonempty (under y)).choose (c.e.symm w)) v) (c.e y) := by
        simp only [GlobalTheory.T.chernTopDensity_eq_polarisedTopChern]
        refine continuousAt_const.mul (Complex.continuous_re.continuousAt.comp ?_)
        refine GlobalTheory.T.continuousAt_polarisedTopChernCoeff (fun i a b p q => ?_)
        exact ((MContDiffAt.curv (j := 0) hsm hu (by norm_num) (coordVec a) (coordVec b)) p q).continuousAt
      exact h1.mul h2
    · filter_upwards [(isOpen_ptsIn O).mem_nhds hy, c.e.open_source.mem_nhds hc,
        GlobalTheory.FrameLift.eventually_mem hA] with z hz hzc hzA
      simp only [topDens, c.e.left_inv hzc]
      rw [hM.chernTop_frame _ hz c hzc (E.nonempty (under z)).choose_spec hzA]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimsLeHeight
section
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat GlobalTheory.GroupBplus GlobalTheory.GroupBplus.Aff
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PDivGroup.CotDim

theorem quot_finrank_le {k A : Type} [Field k] [CommRing A] [Algebra k A] [Module.Finite k A]
    {I J : Ideal A} (hIJ : I ≤ J) : Module.finrank k (A ⧸ J) ≤ Module.finrank k (A ⧸ I) := by
  let f : (A ⧸ I) →ₗ[k] (A ⧸ J) := (Ideal.Quotient.factorₐ k hIJ).toLinearMap
  have hf : Function.Surjective f := Ideal.Quotient.factor_surjective hIJ
  have := LinearMap.finrank_range_le f
  rwa [LinearMap.range_eq_top.2 hf, finrank_top] at this

theorem finrank_level_one {p : ℕ} {k : Type} [Field k] (G : PDivGroup p k) :
    Module.finrank k (G.A 1) = p ^ G.height := by
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum k) := inferInstance
  have h := G.rank_eq 1 q
  rw [Module.rankAtStalk_eq_finrank_of_free] at h
  simpa using h

end GlobalTheory.PDivGroup.CotDim

open GlobalTheory.PDivGroup.CotDim in

theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le (p : ℕ) [Fact p.Prime] (k : Type) [Field k]
    [IsAlgClosed k] [CharP k p] (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  have hp : (p : k) = 0 := CharP.cast_eq_zero k p
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((relFrob hp Γ.dual).app 1)
  have haD : p ^ Module.finrank k (Cot k (Γ.dual.A 1)) ≤
      Module.finrank k (Γ.dual.A 1 ⧸ kerIdeal ((relFrob hp Γ.dual).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.dual.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ.dual 1))

  have hker : LinearMap.ker ((verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k := fun a ha => by
    have h1 := GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha
    rw [kerIdeal_comp] at h1
    rw [Submodule.restrictScalars_mem,
      ← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP (kerIdeal ((relFrob hp Γ).app 1))]
    exact h1
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p k hp Γ
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have haA : p ^ Module.finrank k (Cot k (Γ.A 1)) ≤
      Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) :=
    (GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient p k (Γ.A 1)).trans (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp Γ 1))
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((relFrob hp Γ.dual).app 1 :
        (frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  have key : p ^ (Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1))) ≤
      p ^ Γ.height := by
    rw [pow_add, mul_comm, ← hdimD, hord]
    exact Nat.mul_le_mul haD (haA.trans hrD)
  exact (Nat.pow_le_pow_iff_right hp2).1 key
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrossRelationHomGivesExpansionTermConvolutionRel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange

noncomputable section
namespace GlobalTheory.Mum.MixTwo

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))}
  {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]

abbrev homF (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    (UnifPre.GF (G := G₁) F).left ⟶ (UnifPre.GF (G := G₂) F).left :=
  (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left

theorem homF_str (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    homF a F ≫ MixedConv.strF G₂ F = MixedConv.strF G₁ F :=
  congrArg (fun q => q.left) (whiskerLeft_fst (TFK (R := R) F) ((Over.pullback (jK R)).map a))

theorem homF_gFK (a : G₁ ⟶ G₂) (F : Type) [Field F] [Algebra (FractionRing R) F] :
    homF a F ≫ UnifPre.gFK (G := G₂) F = UnifPre.gFK (G := G₁) F ≫ a.left := by
  have h₁ := congrArg (fun q => q.left) (whiskerLeft_snd (TFK (R := R) F) ((Over.pullback (jK R)).map a))
  have h₂ : ((Over.pullback (jK R)).map a).left ≫ pullback.fst _ _ = pullback.fst _ _ ≫ a.left :=
    pullback.lift_fst _ _ _
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G₂.hom (jK R)) h₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

theorem val_secLin' {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {U : UnifPre I D A G} {F : Type} [Field F] [Algebra (FractionRing R) F] {k n : ℕ} {σ₀ : U.SecGF F k}
    {σ : Fin n → H0 U.LG.L k} {c : Fin n → F}
    (h : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) σ₀
      (fun _ : Fin 1 => 𝟙 G.left) (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i)))
    {Y : Scheme.{0}} (q : Y ⟶ Spec (CommRingCat.of F)) (r : Y ⟶ (UnifPre.GF (G := G) F).left)
    (hr : r ≫ MixedConv.strF G F = q) (y : Y) {J} (hJ : Good U.LG.L y J) :
    sval σ₀ r y J = ∑ i, GlobalTheory.BoxExpansion.constHomVal q y (c i) *
      sval (σ i) (r ≫ UnifPre.gFK (G := G) F) y J :=
  (GlobalTheory.BoxExpansion.secLin_val h r y hJ).trans (Finset.sum_congr rfl fun i _ => congrArg (· * _)
    ((gs_scal (MixedConv.strF G F) r y _).trans ((congrArg (fun q => constVal q y (c i)) hr).trans
      (GlobalTheory.BoxExpansion.constVal_eq _ _ _))))

theorem coreF₂ [CharZero R] (hL : LL) (hR : AdmBase R I) {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂}
    {a : G₁ ⟶ G₂} {b : D₁.toPre.P.A ⟶ D₂.toPre.P.A} {h : D₂.toPre.X →+ D₁.toPre.X} (hLin : Lin U₁ U₂ a b h)
    (hCo : Coord U₁ U₂ a b h) {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (j j' : ℕ)
    {N : Type} [Fintype N] (c : N → F) (σ : N → H0 U₂.LG.L j) (σ' : N → H0 U₁.LG.L j')
    (f : N → ∀ α : D₂.toPre.X, D₂.toPre.SecB j α) (f' : N → ∀ α : D₁.toPre.X, D₁.toPre.SecB j' α)
    (hE : ∀ ν e, U₂.ExpandsAt e j (σ ν) (f ν)) (hE' : ∀ ν e, U₁.ExpandsAt e j' (σ' ν) (f' ν))
    (hrel : ∀ (y : (UnifPre.GF (G := G₁) F).left) (J₁ J₂), Good U₁.LG.L y J₁ → Good U₂.LG.L y J₂ →
      ∑ ν, GlobalTheory.BoxExpansion.constHomVal (MixedConv.strF G₁ F) y (c ν) *
        (sval (σ ν) (UnifPre.gFK (G := G₁) F ≫ a.left) y J₂ * sval (σ' ν) (UnifPre.gFK (G := G₁) F) y J₁) = 0)
    (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F) (hg : Act D₁.toPre D₂.toPre b h g g')
    (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b) (hw : w.IsGen) (hw' : w'.IsGen)
    (x : N → D₂.toPre.X → F) (x' : N → D₁.toPre.X → F)
    (hx : ∀ ν χ, MixedConv.IsCoefB j g' w χ (f ν χ) (x ν χ)) (hx' : ∀ ν χ, MixedConv.IsCoefB j' g w' χ (f' ν χ) (x' ν χ))
    (α : D₁.toPre.X) :
    SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} =>
      ∑ ν, c ν * (x ν p.1.1 * x' ν p.1.2)) 0 := by
  obtain ⟨n, β, ρ, hβ, hc⟩ := MixedConv.exists_indep (R := R) c
  haveI : Nonempty G₁.left := ⟨eSec G₁ (⊥ : PrimeSpectrum R)⟩
  haveI : Nonempty G₂.left := ⟨eSec G₂ (⊥ : PrimeSpectrum R)⟩
  have P₁ := isPart_inl U₁.LG.L U₂.LG.L
  have P₂ := isPart_inr U₁.LG.L U₂.LG.L
  let d : Fin n → SecOver G₁.hom (LB.LinComb (join U₁.LG.L U₂.LG.L)
      (Sum.elim (fun _ : Fin 1 => (a.left ≫ 𝟙 G₂.left) ≫ coprod.inr) (fun _ : Fin 1 => 𝟙 G₁.left ≫ coprod.inl))
      (Sum.elim (fun _ => (j : ℤ)) (fun _ => (j' : ℤ)))) := fun m =>
    ∑ ν, ρ m ν • (show SecOver G₁.hom _ from
      H1.SectionArithmetic.mulSec (P₂.sec (H1.SectionArithmetic.pullSec (σ ν) a.left)) (P₁.sec (σ' ν)))
  have hd : ∀ m (Z : Scheme.{0}) (r : Z ⟶ G₁.left) (z : Z) (J), Good (join U₁.LG.L U₂.LG.L) z J →
      sval (d m) r z J = ∑ ν, constVal (r ≫ G₁.hom) z (ρ m ν) *
        (sval (σ ν) (r ≫ a.left) z (rr J) * sval (σ' ν) r z (rl J)) :=
    fun m Z r z J hJ => (sval_sum' (π := G₁.hom) hJ _ _ _).trans (Finset.sum_congr rfl fun ν _ =>
      (sval_smul' (π := G₁.hom) hJ _ _ _).trans (congrArg _ ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans
        (congrArg₂ (· * ·) ((P₂.sval_sec _ r z hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ z (P₂.good hJ)))
          (P₁.sval_sec _ r z hJ)))))
  have := U₁.smooth
  have h₀ := GlobalTheory.T.sval_eq_zero_of_linearIndependent_comb R F _ _ _ _ G₁.hom (MixedConv.strF G₁ F) _ MixedConv.isPullback_GF
    (join U₁.LG.L U₂.LG.L) (join_isLB U₁.LG.isLB U₂.LG.isLB) _ _ _ _ β hβ d
    (fun y J hJ => by
      refine Eq.trans ?_ (hrel y (rl J) (rr J) (P₁.good hJ) (P₂.good hJ))
      simp only [hd _ _ _ y J hJ, hc, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun m _ => ?_
      rw [(MixedConv.isPullback_GF (G := G₁) (F := F)).w, constVal_specMap, GlobalTheory.BoxExpansion.constVal_eq,
        GlobalTheory.BoxExpansion.constVal_eq, _root_.mul_assoc]
      rfl)
  have h₁ := MixedConv.sumF_comb hR Finset.univ β _ fun m => GlobalTheory.T.integralRelation_uniformisedHom_convolution_expansionTerms hL R I hR D₁ D₂ A₁ A₂ G₁ G₂ U₁ U₂ a b h hLin hCo F
    j j' N (ρ m) σ σ' f f' hE hE' (fun Z r z J₁ J₂ hJ₁ hJ₂ => by
      obtain ⟨J, hJ, rfl, rfl⟩ := exists_good_join U₁.LG.isLB U₂.LG.isLB hJ₁ hJ₂
      exact (hd m Z r z J hJ).symm.trans (h₀ m Z r z J hJ)) g g' hg w w' hw hw' x x' hx hx' α
  refine (congrArg (fun q => SumF I F q 0) (funext fun p => ?_)).mp h₁
  simp only [hc, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun ν _ => Finset.sum_congr rfl fun m _ => (_root_.mul_assoc _ _ _).symm

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R), AdmBase R I → ∀ (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂], IsSemiAbelian G₁ → IsSemiAbelian G₂ → ∀ (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (h : D₂.toPre.X →+ D₁.toPre.X), IsMonHom c → Gen₀ U₁.toUnifPre U₂.toUnifPre a c → Lin U₁.toUnifPre U₂.toUnifPre a b h → Coord U₁.toUnifPre U₂.toUnifPre a b h → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (w₁ : W0 U₁.toUnifPre) (w₂ : W0 U₂.toUnifPre), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ), 1 ≤ j → 1 ≤ j' → ∀ (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') s₁ s₂ s₁' s₂', U₂.ExpandsF F j w₂ t₁ s₁ → U₂.ExpandsF F j w₂ t₂ s₂ → U₁.ExpandsF F j' w₁ t₁' s₁' → U₁.ExpandsF F j' w₁ t₂' s₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (g : GtPtF D₁.toPre F) (g' : GtPtF D₂.toPre F), Act D₁.toPre D₂.toPre b h g g' → ∀ (w : Frm D₂.toPre F j g'.b) (w' : Frm D₁.toPre F j' g.b), w.IsGen → w'.IsGen → ∀ α, SumF I F (fun p : {p : D₂.toPre.X × D₁.toPre.X // h p.1 + p.2 = α} => coef s₁ g' w p.1.1 * coef s₂' g w' p.1.2 - coef s₂ g' w p.1.1 * coef s₁' g w' p.1.2) 0 := by
  intro R _ _ _ I hR D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ _ _ U₁ U₂ a c b h _ hG hLin hCo F _ _ _ w₁ w₂ hw₁ hw₂ j j' _ _
    t₁ t₂ t₁' t₂' s₁ s₂ s₁' s₂' H₁ H₂ H₁' H₂' hC g g' hg w w' hw hw' α
  obtain ⟨τ₁, r₁, n₁, c₁, σ₁, f₁, e₁, l₁, b₁⟩ := H₁
  obtain ⟨τ₂, r₂, n₂, c₂, σ₂, f₂, e₂, l₂, b₂⟩ := H₂
  obtain ⟨τ₁', r₁', n₁', c₁', σ₁', f₁', e₁', l₁', b₁'⟩ := H₁'
  obtain ⟨τ₂', r₂', n₂', c₂', σ₂', f₂', e₂', l₂', b₂'⟩ := H₂'
  choose x₁ hx₁ using fun i χ => MixedConv.exists_isCoefB g' hw χ (f₁ i χ)
  choose x₂ hx₂ using fun i χ => MixedConv.exists_isCoefB g' hw χ (f₂ i χ)
  choose x₁' hx₁' using fun i χ => MixedConv.exists_isCoefB g hw' χ (f₁' i χ)
  choose x₂' hx₂' using fun i χ => MixedConv.exists_isCoefB g hw' χ (f₂' i χ)
  have key := coreF₂ GlobalTheory.firstFiveLaws hR hLin hCo j j' (N := (Fin n₁ × Fin n₂') ⊕ (Fin n₂ × Fin n₁'))
    (Sum.elim (fun p => c₁ p.1 * c₂' p.2) (fun p => -(c₂ p.1 * c₁' p.2)))
    (Sum.elim (fun p => σ₁ p.1) (fun p => σ₂ p.1)) (Sum.elim (fun p => σ₂' p.2) (fun p => σ₁' p.2))
    (Sum.elim (fun p => f₁ p.1) (fun p => f₂ p.1)) (Sum.elim (fun p => f₂' p.2) (fun p => f₁' p.2))
    (by rintro (p | p); exacts [e₁ p.1, e₂ p.1]) (by rintro (p | p); exacts [e₂' p.2, e₁' p.2])
    (fun y J₁ J₂ hJ₁ hJ₂ => by
      have hh := GlobalTheory.T.carriedSections_crossRelation_of_hom R I D₁ D₂ A₁ A₂ G₁ G₂ U₁.toUnifPre U₂.toUnifPre a c hG F w₁ w₂ hw₁ hw₂ j j'
        t₁ t₂ t₁' t₂' τ₁ τ₂ τ₁' τ₂' r₁ r₂ r₁' r₂' hC y J₁ J₂ hJ₁ hJ₂
      rw [val_secLin' l₁ _ _ (homF_str a F) y hJ₂, val_secLin' l₂ _ _ (homF_str a F) y hJ₂,
        val_secLin' l₁' _ _ (Category.id_comp _) y hJ₁, val_secLin' l₂' _ _ (Category.id_comp _) y hJ₁, homF_gFK,
        Category.id_comp, Finset.sum_mul_sum, Finset.sum_mul_sum, ← sub_eq_zero] at hh
      refine Eq.trans ?_ hh
      simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr, map_neg, map_mul,
        neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
      exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)
        (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _))
    g g' hg w w' hw hw' (Sum.elim (fun p => x₁ p.1) (fun p => x₂ p.1))
    (Sum.elim (fun p => x₂' p.2) (fun p => x₁' p.2))
    (by rintro (p | p); exacts [hx₁ p.1, hx₂ p.1]) (by rintro (p | p); exacts [hx₂' p.2, hx₁' p.2]) α
  refine (congrArg (fun q => SumF I F q 0) (funext fun p => ?_)).mp key
  rw [MixedConv.coef_of_secLin (b₁ _) (fun i => hx₁ i _), MixedConv.coef_of_secLin (b₂ _) (fun i => hx₂ i _),
    MixedConv.coef_of_secLin (b₁' _) (fun i => hx₁' i _), MixedConv.coef_of_secLin (b₂' _) (fun i => hx₂' i _),
    Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Fintype.sum_sum_type, Fintype.sum_prod_type, Sum.elim_inl, Sum.elim_inr,
    neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg]
  exact congrArg₂ (· - ·) (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)
    (Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => _root_.mul_mul_mul_comm _ _ _ _)

end GlobalTheory.Mum.MixTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalBundleModificationDescendsToGroup
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.CubeDesc

theorem app_bijective (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : AdmBase R (maximalIdeal R))
    (M : Modif R) (G' : Over M.S) (G : Over (Sp R)) (β : G'.left ⟶ G.left) (hf : Flat G.hom)
    (hp : IsPullback β G'.hom G.hom M.π) : ∀ V : G.left.Opens, Function.Bijective (β.app V).hom := by
  obtain ⟨hN, -, hI, -⟩ := hR
  haveI := M.proper
  exact GlobalTheory.T.app_bijective_of_flat_baseChange_globalFunctions R M.S G.left G'.left M.π G.hom β G'.hom inferInstance inferInstance
    (GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M).1 hf hp

theorem exists_closed_spec (R : Type) [CommRing R] [IsLocalRing R] (G : Over (Sp R)) (hG : QuasiCompact G.hom)
    (y : G.left) (hy : G.hom y = closedPoint R) :
    ∃ z : G.left, IsClosed ({z} : Set G.left) ∧ y ⤳ z ∧ G.hom z = closedPoint R := by
  haveI : CompactSpace G.left := by
    haveI := hG
    exact QuasiCompact.compactSpace_of_compactSpace G.hom
  obtain ⟨z, hz, hzc⟩ := (isClosed_closure (s := ({y} : Set G.left))).exists_closed_singleton ⟨y, subset_closure rfl⟩
  have hyz : y ⤳ z := specializes_iff_mem_closure.2 hz
  refine ⟨z, hzc, hyz, ?_⟩
  have h := hyz.map G.hom.base.hom.continuous
  rw [hy] at h
  have hc : IsClosed ({closedPoint R} : Set (PrimeSpectrum R)) := isClosed_singleton_closedPoint R
  have h' := specializes_iff_mem_closure.1 h
  exact hc.closure_subset h'

theorem cubicalBundle_descends : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (P' : GlobalTheory.UU.CP G') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G M.π β → ∀ (θ : P'.L.L.Sec) (O : G.left.Opens), (∃ g ∈ O, G.hom g = closedPoint R) → (∀ g : G'.left, β g ∈ O → G.hom (β g) = closedPoint R → ∃ i, g ∈ G'.left.basicOpen (θ.f i)) → ∃ L : LB G.left, L.IsLB ∧ LBIso P'.L.L (L.pull β) := by
  intro R _ _ _ hR M G' _ _ hG' P' G _ _ β hG hpb θ O hO hθ
  have hflat : Flat G.hom := by haveI := hG.smooth; infer_instance
  have hbij := app_bijective R hR M G' G β hflat hpb.1
  have hloc : ∀ y : G.left, ∃ V : G.left.Opens, y ∈ V ∧ ∃ t : LB.Gen (P'.L.L.pull (β ⁻¹ᵁ V).ι), t.IsGen := by
    intro y
    by_cases hy : G.hom y = closedPoint R
    · obtain ⟨z, hzc, hyz, hz⟩ := exists_closed_spec R G hG.quasiCompact y hy
      obtain ⟨V, hzV, t⟩ := GlobalTheory.T.exists_generator_descendedBundle_near_closedPoint R hR M G' hG' P' G β hG hpb θ O hO hθ z hzc hz
      exact ⟨V, hyz.mem_open V.isOpen hzV, t⟩
    · exact GlobalTheory.T.exists_generator_off_closedFibre_descended R hR M G' hG' P' G β hG hpb θ O hO hθ y hy
  exact GlobalTheory.T.exists_lineBundle_descent_bijective_app _ _ β hbij P'.L.L P'.L.isLB hloc

end GlobalTheory.Mum.CubeDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelDbarCommPullbackOfSmoothDelDbarStatement
section
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.del_dbar_comm_pullback_of_smooth_del_dbar : ∀ (M M' : Type) [TopologicalSpace M] [TopologicalSpace M'] (n n' : ℕ) (A : HolAtlas M n) (A' : HolAtlas M' n')
    (f : M' → M) (α : A.Fld), A.IsHolo A' f → A.IsForm α → A.IsForm (A.del α) → A.IsForm (A.dbar α) →
    A'.del (A.pullback A' f α) = A.pullback A' f (A.del α) ∧ A'.dbar (A.pullback A' f α) = A.pullback A' f (A.dbar α) := by
  first | exact @GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback | exact GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback | (intros; apply GlobalTheory.CxForm.HolAtlas.del_dbar_comm_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalAppellHumbertRealMultStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (defCoord polydisc)
open scoped nonZeroDivisors
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_appell_humbert_real_mult : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (𝔠 : FracId F)
    (X : Obj F 𝔠 (Sp ℂ)) (c : 𝔠.elt), IsTotPos (c : F) →
    ∀ (u : HolUnif X.A (X.diag c) (Module.finrank ℚ F)) (e : Fin (Module.finrank ℚ F) ≃ (F →+* ℝ)),
    (∀ (a : 𝓞 F) w, u.ex (fun j ↦ (e j (a : F) : ℂ) * w j) = u.ex w ≫ X.rm.act a) →
    ∀ (h : Fin (Module.finrank ℚ F) → ℝ) (χ : u.Λ → ℂ), u.IsAH (Matrix.diagonal fun j ↦ (h j : ℂ)) χ →
    ∃ P : u.Λ → u.Λ → F, (∀ l l' : u.Λ, P l l' = -P l' l) ∧ (∀ l₁ l₂ l' : u.Λ, P (l₁ + l₂) l' = P l₁ l' + P l₂ l') ∧
      (∀ (a : 𝓞 F) (l l' al : u.Λ), (al : Fin (Module.finrank ℚ F) → ℂ) = (fun j ↦ (e j (a : F) : ℂ) * (l : Fin (Module.finrank ℚ F) → ℂ) j) →
        P al l' = (a : F) * P l l') ∧
      (∀ l l' : u.Λ, (∑ j, (h j : ℂ) * ((l : Fin (Module.finrank ℚ F) → ℂ) j * starRingEnd ℂ ((l' : Fin (Module.finrank ℚ F) → ℂ) j))).im =
        2 * ((Algebra.trace ℚ F ((c : F) * P l l') : ℚ) : ℝ)) ∧
      (∀ l l' : u.Λ, P l l' ∈ dualLat 𝔠) ∧
      (∀ t ∈ dualLat 𝔠, t ∈ Submodule.span (𝓞 F) {t | ∃ l l' : u.Λ, t = P l l'}) := by
  first | exact @GlobalTheory.TorusRiem.riemannForm_eq_two_trace | exact GlobalTheory.TorusRiem.riemannForm_eq_two_trace | (intros; apply GlobalTheory.TorusRiem.riemannForm_eq_two_trace <;> assumption)
end

