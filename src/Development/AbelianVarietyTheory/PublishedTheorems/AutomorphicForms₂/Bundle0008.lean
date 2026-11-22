import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.MemSmallSecTrivShift
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnderEqGenericPoint
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsCuspFunIffConstTerm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0045
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open scoped Matrix ComplexOrder

namespace GlobalTheory.GoodMetric

theorem topCoeff_pow {n : ℕ} (K : Matrix (Fin n) (Fin n) ℂ) :
    topCoeff ((∑ a, ∑ b, C (K a b) * X (a, b)) ^ n) = n.factorial * K.det := by
  classical
  rw [← Matrix.det_transpose, Matrix.det_apply', Finset.mul_sum, topCoeff]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hv (x : Fin n × Fin n) : (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) x = if w x.1 = x.2 then 1 else 0 := by
    obtain ⟨a, b⟩ := x
    rw [Finsupp.finsetSum_apply, Finset.sum_eq_single a (fun c _ hc => by simp [Finsupp.single_apply, hc]) (by simp)]
    simp [Finsupp.single_apply]
  have hs : ∑ x, (∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) x = n := by
    simp only [hv, Fintype.sum_prod_type, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp
  rw [← Fintype.sum_prod_type' (f := fun a b => C (K a b) * X (a, b))]
  simp only [C_mul']
  rw [coeff_linearCombination_X_pow_of_fintype, Finsupp.sum_fintype _ _ (fun _ => rfl), if_pos hs,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _), Nat.multinomial, hs]
  have h1 : ∏ x, ((∑ a, Finsupp.single (a, w a) 1 : Fin n × Fin n →₀ ℕ) x).factorial = 1 :=
    Finset.prod_eq_one fun x _ => by rw [hv]; split_ifs <;> rfl
  rw [h1, Nat.div_one]
  simp only [hv, Fintype.prod_prod_type, pow_ite, pow_one, pow_zero, Finset.prod_ite_eq, Finset.mem_univ, if_true,
    Matrix.transpose_apply]
  ring

theorem chernTop_line {n : ℕ} (G : V n → Mat (fun _ : Unit => 1) ℂ) (v : V n) :
    chernTop (X ((), 1) ^ n) G v = n.factorial / Real.pi ^ n *
      (Matrix.of fun a b => curv (fun u => G u ()) v (coordVec a) (coordVec b) 0 0).det.re := by
  have e : chernPoly (fun u => G u ()) v 1 = curvPoly (fun u => G u ()) v 0 0 := by
    rw [chernPoly, Matrix.coeff_charpolyRev_eq_neg_trace]
    simp [Matrix.trace]
  rw [chernTop, map_pow, aeval_X, e]
  erw [topCoeff_pow (Matrix.of fun a b => curv (fun u => G u ()) v (coordVec a) (coordVec b) 0 0)]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm]

def logGram (v : V 1) : Matrix (Fin 1) (Fin 1) ℂ := Matrix.of fun _ _ => ((-Real.log (‖v‖ ^ 2) : ℝ) : ℂ)

variable {F : Type} [Field F] {ι : Type} {m : ι → ℕ} {X : Var F} {σ : F →+* ℂ}

theorem exists_ratVal_hom (y : CxPts X.str σ) :
    ∃ ψ : ((ratOf X).O (under y)).toSubring →+* ℂ, ∀ x : ((ratOf X).O (under y)).toSubring, ratVal (x : X.Fn) y = ψ x := by
  have h (x : ((ratOf X).O (under y)).toSubring) : ratVal (x : X.Fn) y = (ratOf X).val y.1 x := by
    obtain ⟨U, hy, a, e⟩ := (mem_O_ratOf.1 x.2).exists_fnOf
    rw [← e, ratVal_fnOf (mem_ptsIn.2 hy), ← valF_fromSpecStalk]
    refine (GlobalTheory.ZH.RatModel.val_valF (M := ratOf X) ?_ a).symm
    rintro _ ⟨w, rfl⟩
    rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) w (IsLocalRing.closedPoint ℂ)]
  exact ⟨GlobalTheory.ZH.RatModel.valHom (M := ratOf X) y.1 _
    (GlobalTheory.ZH.RatModel.range_eq_singleton (M := ratOf X) y.1 (IsLocalRing.closedPoint ℂ)), fun x => (h x).trans rfl⟩

theorem cInfAt_ratVal {κ : Type} [Fintype κ] {f : κ → X.Fn} {y : CxPts X.str σ} (hf : ∀ a, RegAt (under y) (f a))
    {G : (κ → ℂ) → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) : CInfAt (fun z => G fun a => ratVal (f a) z) y := by
  choose U hy g e using fun a => (hf a).exists_fnOf
  let W : X.X.Opens := ⟨⋂ a, U a, isOpen_iInter_of_finite fun a => (U a).isOpen⟩
  have hW : y ∈ ptsIn X.str σ W := mem_ptsIn.2 (Set.mem_iInter.2 hy)
  have hle (a) : W ≤ U a := Set.iInter_subset (fun a => (U a : Set X.X)) a
  refine ⟨W, κ, inferInstance, fun a => resG X.X (hle a) (g a), G, Set.univ, hW, isOpen_univ, trivial, hG.contDiffOn, ?_⟩
  filter_upwards [(isOpen_ptsIn W).mem_nhds hW] with z hz
  congr 1
  funext a
  rw [ev_res (hle a) hz, ← e a, ratVal_fnOf (ptsIn_mono (hle a) hz)]

def scaledGram (u : CxPts X.str σ → ℝ) (A : Mat m X.Fn) (y : CxPts X.str σ) : Mat m ℂ :=
  fun τ => (u y : ℂ) • (A.map (ratVal · y) τ * (A.map (ratVal · y) τ)ᴴ)

def lineFlag (E : Fr (ratOf X) (fun _ : ι => 1) 0) : Fr (ratOf X) (fun _ : ι => 1) fun _ => 1 where
  S := E.S
  loc z := by
    obtain ⟨U, A, hz, hA, h⟩ := E.loc z
    refine ⟨U, A, hz, hA, fun z' hz' A' => (h z' hz' A').trans ⟨fun H τ => ?_, fun H => H.mono bot_le le_rfl⟩⟩
    exact ⟨(H τ).1, (H τ).2.1, (H τ).2.2.1, fun i j _ hij => absurd hij (by simp [Subsingleton.elim i j])⟩

theorem refines_lineFlag (E : Fr (ratOf X) (fun _ : ι => 1) 0) : Refines E (lineFlag E) (AlgHom.id F X.Fn) (𝟙 X.X) where
  le := bot_le
  hom := (ratOf X).isHom_id
  sub _ _ hA' _ hA := (Fr.mem_iff hA).1 hA'
  rad _ _ h := h
  lifts K _ x A hA h hh := by
    refine ⟨x, ⟨Category.comp_id _, A, hA, ?_⟩, fun p hp => (Category.comp_id _).symm.trans hp.1⟩
    have e : (A * (A.map (AlgHom.id F X.Fn))⁻¹).map ((ratOf X).val x) = 1 := by
      rw [show A.map (AlgHom.id F X.Fn) = A from rfl, Mat.mul_inv (Fr.det_ne hA)]
      exact funext fun _ => Matrix.map_one _ (GlobalTheory.ZH.RatModel.val_zero x) (GlobalTheory.ZH.RatModel.val_one x)
    rw [e, inv_one, mul_one]
    exact fun τ => ⟨(hh τ).1, (hh τ).2.1, (hh τ).2.2.1, fun i j _ hij => absurd hij (by simp [Subsingleton.elim i j])⟩

def ofDivisor (Δ : X.Dv) : Fr (ratOf X) (fun _ : Unit => 1) 0 where
  S z := {A | Δ.GeneratesAt z (A () 0 0)}
  loc z := by
    obtain ⟨U, hz, g, hg⟩ := Δ.exists_isEqn_nhds z
    refine ⟨U, fun _ => Matrix.diagonal fun _ => (g : X.Fn)⁻¹, hz, fun _ => by simp, fun z' hz' A => ?_⟩
    have e (i j) : (A * (fun _ => Matrix.diagonal fun _ => (g : X.Fn)⁻¹ : Mat (fun _ : Unit => 1) X.Fn)⁻¹) () i j =
        A () 0 0 * g := by
      rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
      simp [Matrix.mul_apply, Matrix.inv_def]
    refine (hg z' hz').generatesAt_iff.trans ⟨fun h _ => ⟨fun i j => ?_, ?_, ?_, fun i j hi => absurd hi (by simp)⟩,
      fun h => ?_⟩
    · rw [e]; exact mem_O_ratOf.2 h.regAt
    · rw [Matrix.det_unique, e]; exact h.ne_zero
    · rw [Matrix.det_unique, e]; exact mem_O_ratOf.2 h.inv.regAt
    · obtain ⟨h1, h2, h3, -⟩ := h ()
      rw [Matrix.det_unique, e] at h2 h3
      exact (unitAt_iff h2).2 ⟨mem_O_ratOf.1 (e 0 0 ▸ h1 0 0), mem_O_ratOf.1 h3⟩

theorem isGraded_ofDivisor (Δ : X.Dv) : IsGraded (lineFlag (ofDivisor Δ)) fun _ => Δ := by
  refine ⟨1, ⟨1, Δ.isEqn_genericPoint 1, by simpa using unitAt_one _⟩, fun y x => ?_⟩
  obtain ⟨g, hg⟩ := Δ.exists_isEqn y
  refine ⟨fun _ => Matrix.diagonal fun _ => (g : X.Fn)⁻¹, CartierDiv.isEqn_iff_generatesAt_inv.1 hg, g, ?_, hg⟩
  obtain ⟨⟨⟩, i⟩ := x
  rw [Subsingleton.elim i 0]
  simp [Matrix.inv_def]

end GlobalTheory.GoodMetric
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernDegreePoint
section
noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts

namespace GlobalTheory.Published.ArDegreeModel

theorem birational_int (t : ℝ) : IsArithVar (𝟙 (Sp ℤ)) 0 ∧ ((⊤ : (Sp ℤ).Opens) : Set (Sp ℤ)).Nonempty ∧
    IsIso (𝟙 (Sp ℤ) ∣_ ⊤) ∧ (ArithBase.trivShift t).IsSelfInter t ∧
    ((ArithBase.trivShift t).pull (𝟙 _) (Category.id_comp _)).IsSelfInter t :=
  ⟨ArithBase.isArithVar_int, ⟨genericPoint _, trivial⟩, inferInstance, ArithBase.isSelfInter_trivShift t,
    ArInt.Model.IsConst.isSelfInter fun i => ⟨fun _ => Set.mem_iInter.2 fun _ => trivial, fun σ y =>
      (((ArithBase.trivShift t).φ σ).pull_φ _ _ i y).trans (zero_add _)⟩⟩

variable {F : Type} [Field F] (Y : Var F) (σ : F →+* ℂ)

theorem chernDegree_triv (h : 1 ≤ Y.dim) (c : ℝ) :
    Presents (0 : Y.Dv) (LB.triv Y.X) (fun _ => 1) ∧ (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c).IsCInf ∧
      (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c).ChernIntegrableOn Y.dim Set.univ (fun _ => 1) ∧
      (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c).chernInt Y.dim Set.univ (fun _ => 1) =
        (Y.inter (fun _ => (0 : Y.Dv)) : ℝ) := by
  have hd (ch : AlgChart Y.str σ Y.dim) (y) :
      ch.chernDens (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c) y = 0 := by
    have : Nonempty (Fin Y.dim) := ⟨⟨0, h⟩⟩
    have e : ch.hess (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c) PUnit.unit y = 0 := by
      ext a b
      have e₀ : ReciprocityTheory.L2DbarEstimates.wdb Y.dim b (fun _ => (c : ℂ)) = fun _ => 0 := by
        funext v; simp [ReciprocityTheory.L2DbarEstimates.wdb]
      simp [AlgChart.hess, Weight.ofFun, ReciprocityTheory.L2DbarEstimates.cHess, ReciprocityTheory.L2DbarEstimates.wd, e₀]
    rw [AlgChart.chernDens]
    erw [e]
    simp
  have hz (ε : ℤˣ) : (Weight.ofFun (p := Y.str) (σ := σ) fun _ => c).chernPart Y.dim ε = 0 := by
    refine le_antisymm (iSup_le fun ch => le_of_eq ?_) bot_le
    simp only [hd, mul_zero, ENNReal.ofReal_zero, ChartGlue.chartMeas]
    rw [show ((fun _ => (0 : ENNReal)) ∘ ch.e.symm) = 0 from rfl]
    simp
  refine ⟨presents_zero, Weight.isCInf_ofFun (cInfAt_const c), ⟨by rw [hz]; simp [MeasureTheory.IntegrableOn],
    by rw [hz]; simp [MeasureTheory.IntegrableOn]⟩, ?_⟩
  rw [Y.inter_eq_zero_of_principal _ ⟨0, h⟩ 1 rfl, Weight.chernInt, hz, hz]
  simp

def fs : Weight Y.str σ Y.O1 :=
  Weight.fsBasis Y.str σ Y.isLineBundle_twistingSheafOne Y.coordSec Y.basePointFree_coordSys 1 (by simp)

theorem isCInf_fs : (fs Y σ).IsCInf := Weight.isCInf_fsBasis _ _ _ _ _

theorem mass_proj (H : ChernDegree) (n : ℕ) :
    (fs (proj F n) σ).chernInt n Set.univ (fun _ => 1) = 1 := by
  have := (H F (proj F n) σ _ _ _ ((proj F n).presents_hyp (proj_gen_mem F n 0)) _ (isCInf_fs _ σ)).2
  exact this.trans (by exact_mod_cast inter_projHyp F n)

theorem unique_pt (h : Y.dim = 0) : Nonempty (CxPts Y.str σ) ∧ Subsingleton (CxPts Y.str σ) := by
  have : Etale Y.str := (Etale.iff_smoothOfRelativeDimension_zero _).2 (h ▸ Y.smooth_str)
  let q := Limits.pullback.snd Y.str (spMap σ)
  have : IsIntegral (Limits.pullback Y.str (spMap σ)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := Y.str) _ _ _ (IsPullback.of_hasPullback _ _)
  have hs (s : Sp ℂ ⟶ Limits.pullback Y.str (spMap σ)) (hs : s ≫ q = 𝟙 _) : IsIso q := by
    have : IsClosedImmersion (s ≫ q) := by rw [hs]; infer_instance
    have : IsClosedImmersion s := IsClosedImmersion.of_comp s q
    have : Etale (s ≫ q) := by rw [hs]; infer_instance
    have : Etale s := Etale.of_comp s q
    have : Mono s := (SplitMono.mk q hs).mono
    have : IsOpenImmersion s := IsOpenImmersion.of_flat_of_mono s
    have : IsIso s := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (Opens.ext
      (IsClopen.eq_univ ⟨s.isClosedEmbedding.isClosed_range, s.isOpenEmbedding.isOpen_range⟩ (Set.range_nonempty _)))
    have : IsIso (s ≫ q) := by rw [hs]; infer_instance
    exact IsIso.of_isIso_comp_left s _
  have : JacobsonSpace (Limits.pullback Y.str (spMap σ) :) := LocallyOfFiniteType.jacobsonSpace q
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints (X := (Limits.pullback Y.str (spMap σ) :)) Set.univ_nonempty
    isOpen_univ.isLocallyClosed
  have := hs _ (pointOfClosedPoint_comp q c hc)
  refine ⟨⟨⟨inv q ≫ Limits.pullback.fst _ _, by rw [Category.assoc, Limits.pullback.condition]; simp [q]⟩⟩,
    ⟨fun a b => Subtype.ext ?_⟩⟩
  have e : Limits.pullback.lift a.1 (𝟙 _) (by simpa using a.2) = Limits.pullback.lift b.1 (𝟙 _) (by simpa using b.2) :=
    (cancel_mono q).1 ((Limits.pullback.lift_snd _ _ _).trans (Limits.pullback.lift_snd _ _ _).symm)
  exact (Limits.pullback.lift_fst _ _ _).symm.trans
    ((congrArg (· ≫ Limits.pullback.fst _ _) e).trans (Limits.pullback.lift_fst _ _ _))

theorem chernDegree_point (Δ : (proj F 0).Dv) (L : LB (proj F 0).X) (φ : Weight (proj F 0).str σ L) (h : φ.IsCInf) :
    φ.ChernIntegrableOn 0 Set.univ (fun _ => 1) ∧
      φ.chernInt 0 Set.univ (fun _ => 1) = ((proj F 0).inter (fun _ => Δ) : ℝ) := by
  obtain ⟨⟨y⟩, _⟩ := unique_pt (proj F 0) σ rfl
  have : SmoothOfRelativeDimension 0 (proj F 0).str := (proj F 0).smooth_str
  have := CxPts.secondCountableTopology_of_isProjOver σ (proj F 0).isProjOver
  obtain ⟨R⟩ := genSmooth_of_smooth (proj F 0).str 0 σ
  obtain ⟨a, ha⟩ := R.cover y
  have hm (ε : ℤˣ) : φ.chernPart 0 ε Set.univ = ENNReal.ofReal (ε : ℤ) := by
    rw [Weight.chernPart_apply h ε (R.chart a) MeasurableSet.univ fun z _ => Subsingleton.elim y z ▸ ha]
    simp only [AlgChart.chernDens_zero, mul_one]
    rw [show (R.chart a).e '' Set.univ = Set.univ from
      Set.eq_univ_of_forall fun v => ⟨y, trivial, Subsingleton.elim _ _⟩]
    have hv : (MeasureTheory.volume : MeasureTheory.Measure (ReciprocityTheory.L2DbarEstimates.V 0)) Set.univ = 1 := by
      have := (stdOrthonormalBasis ℝ (ReciprocityTheory.L2DbarEstimates.V 0)).volume_parallelepiped
      rwa [Set.eq_univ_of_forall (s := parallelepiped _) fun v =>
        (mem_parallelepiped_iff _ _).2 ⟨0, ⟨le_rfl, zero_le_one⟩, Subsingleton.elim _ _⟩] at this
    simp [hv]
  have hf (ε : ℤˣ) : MeasureTheory.IsFiniteMeasure (φ.chernPart 0 ε) := ⟨by rw [hm]; exact ENNReal.ofReal_lt_top⟩
  have hi : (proj F 0).inter (fun _ => Δ) = 1 :=
    (congrArg _ (funext fun i : Fin 0 => i.elim0)).trans (inter_projHyp F 0)
  refine ⟨⟨MeasureTheory.integrableOn_univ.2 (MeasureTheory.integrable_const _),
    MeasureTheory.integrableOn_univ.2 (MeasureTheory.integrable_const _)⟩, ?_⟩
  rw [hi, Weight.chernInt]
  simp [MeasureTheory.Measure.real, hm, ENNReal.toReal_ofReal']

theorem hyp_proj (N : ℕ) : GenSmooth (𝟙 (Sp ℤ)) 0 ∧ IsArithVar (PSpace.str ℤ N) N ∧ GenSmooth (PSpace.str ℤ N) N ∧
    IsIso (𝟙 (PSpace ℤ N) ∣_ ⊤) :=
  ⟨genSmooth_of_smooth _ _, ProjSpace.isArithVar_int N, genSmooth_of_smooth _ _, inferInstance⟩

theorem birational_id {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}
    (hX : IsArithVar p D) (L : HermLB p) (a : ℝ) (h : L.IsSelfInter a) :
    (L.pull (𝟙 X) (Category.id_comp p)).IsSelfInter a := by
  obtain ⟨f, hf, e⟩ := h
  have hr : TwistTop.Refines L (L.pull (𝟙 X) (Category.id_comp p)) (fun c _ => c) 0 := by
    refine ⟨fun c y hy => Set.mem_iInter.2 fun _ => hy, fun Z r z c c' hc hc' => ?_, fun σ c y _ => ?_⟩
    · refine Eq.trans ?_ (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gm_pull_g L.B (𝟙 X) r z (fun _ => c) (fun _ => c')
        (Set.mem_iInter.2 fun _ => hc) (Set.mem_iInter.2 fun _ => hc')).symm
      rw [Category.comp_id]
    · refine Eq.trans ?_ (((L.φ σ).pull_φ (𝟙 X) (Category.id_comp p) (fun _ => c) y).symm.trans (add_zero _).symm)
      exact congrArg _ (Subtype.ext (Category.comp_id _).symm)
  exact ⟨f, hr.isArithHeight hX hf, e⟩

end GlobalTheory.Published.ArDegreeModel
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsCuspFunOnePlane
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies MeasureTheory Matrix
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CuspDecay.Model

variable {D : D7}

theorem exists_theta_exp (V : HSp D) : ∃ θ, IsInfFam (D := D) θ ∧ ∃ e, IsExpFam θ V e := by
  have h := (GlobalTheory.AutFunCompare.isInfFam_iff (D := D) _).2 rfl
  exact ⟨_, h, _, GlobalTheory.SmoothForms.isExpFam_expInf ((GlobalTheory.SmoothForms.RealPts.realPoints D).2 _ h V)⟩

theorem const_hyps (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (e : LieInf V → GA D V) (c : ℂ) :
    IsAutFun V (fun _ => c) ∧ IsSmoothInf V e (fun _ => c) ∧ IsUnifModerate θ V e (fun _ => c) := by
  refine ⟨⟨fun _ _ _ => rfl, ⟨⊤, isOpen_univ, fun _ _ _ _ => rfl⟩, continuous_const⟩, isSmoothInf_const V e c, 0,
    fun l => ?_⟩
  obtain ⟨c', hc⟩ := wordDer_const V e l c
  exact ⟨‖c'‖, fun g => by rw [hc]; simp⟩

theorem isCuspFun_zero (V : HSp D) : IsCuspFun V fun _ => 0 := fun _ _ _ _ _ _ _ _ => by simp

def line (D : D7) : HSp D := Examples₂.posSpace Examples₂.star_isIntegral 1

def plane (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 2 ![false, true] 1 1

theorem isCuspFun_line (φ : GA D (line D) → ℂ) : IsCuspFun (line D) φ := by
  intro r C hC
  exfalso
  obtain ⟨hr, hli, h0⟩ := hC
  have h1 := congrFun (congrFun h0 ⟨0, hr⟩) ⟨0, hr⟩
  have hg : (line D).gram = 1 := by
    funext i j
    refine (Examples₂.stdSpace_gram_apply (E := D.host.E) Examples₂.star_isIntegral 1 (fun _ => false) 1 0 i j).trans ?_
    change (if i = j then (Examples₂.sgn false : D.host.E) else 0) = if i = j then 1 else 0
    by_cases h : i = j <;> simp [h, Examples₂.sgn]
  rw [hg, Matrix.mul_one] at h1
  let C' : Matrix (Fin 1) (Fin r) D.host.E := C
  have h2 : ∑ i : Fin 1, D.sp.cm.sig (C' i ⟨0, hr⟩) * C' i ⟨0, hr⟩ = 0 := h1
  rw [Fin.sum_univ_one] at h2
  have h3 : C' 0 ⟨0, hr⟩ = 0 := by
    rcases mul_eq_zero.1 h2 with h | h
    · exact (map_eq_zero_iff _ (D.sp.cm.sig : D.host.E →+* D.host.E).injective).1 h
    · exact h
  refine hli.ne_zero ⟨0, hr⟩ (funext fun i => ?_)
  have hi : ∀ i : Fin 1, C' i ⟨0, hr⟩ = 0 := fun i => by rw [Subsingleton.elim i 0]; exact h3
  exact hi i

theorem hyps_line (D : D7) : ∃ θ, IsInfFam (D := D) θ ∧ ∃ e, IsExpFam θ (line D) e ∧ IsAutFun (line D) (fun _ => 1) ∧
    IsSmoothInf (line D) e (fun _ => 1) ∧ IsUnifModerate θ (line D) e (fun _ => 1) ∧ IsCuspFun (line D) fun _ => 1 := by
  obtain ⟨θ, hθ, e, he⟩ := exists_theta_exp (line D)
  obtain ⟨h1, h2, h3⟩ := const_hyps θ (line D) e 1
  exact ⟨θ, hθ, e, he, h1, h2, h3, isCuspFun_line _⟩

theorem isIsoFrame_plane (D : D7) : IsIsoFrame (plane D) (r := 1) (Matrix.of fun _ _ => 1) := by
  refine ⟨one_pos, ?_, ?_⟩
  · refine linearIndependent_unique_iff.2 fun h => ?_
    have := congrFun h (0 : Fin 2)
    exact one_ne_zero this
  · have hg : ∀ i j : Fin 2, (plane D).gram i j = if i = j then (Examples₂.sgn (![false, true] i) : D.host.E) else 0 :=
      Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral 2 ![false, true] 1 1
    funext a b
    change ∑ j : Fin 2, (∑ i : Fin 2, D.sp.cm.sig 1 * (plane D).gram i j) * 1 = 0
    simp [Fin.sum_univ_two, hg, Examples₂.sgn]

theorem isClosed_NI (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C) :
    IsClosed (NI V C : Set (GA D V)) := by
  obtain ⟨L, hL, -⟩ := GlobalTheory.AutFunCompare.exists_dual D.sp.cm V C hC.2.1 hC.2.2
  have : IsModuleTopology (AF D.host.F) (AF D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  have : IsTopologicalRing (AF D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (AF D.host.F) _
  have : T2Space (AF D.host.F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField _
  have : T2Space (AF D.host.F ⊗[D.host.F] D.host.E) :=
    .of_injective_continuous (f := (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun)
      (LinearEquiv.injective _) (IsModuleTopology.continuous_of_linearMap
        (Algebra.TensorProduct.basis (AF D.host.F) (Module.finBasis D.host.F D.host.E)).equivFun.toLinearMap)
  have hm : Continuous fun g : GA D V => (HA.mat _ D.sp.cm.sig V.gram g).1 :=
    Units.continuous_val.comp continuous_subtype_val
  rw [GlobalTheory.AutFunCompare.NI_eq]
  have hcl : IsClosed {g : GA D V |
      ((HA.mat _ D.sp.cm.sig V.gram g).1 - 1) * (C * L).map (inclR (F := D.host.F) (AF D.host.F)) = 0 ∧
      (1 - (C * L).map (inclR (F := D.host.F) (AF D.host.F))) * ((HA.mat _ D.sp.cm.sig V.gram g).1 - 1) *
        (1 - GlobalTheory.AutFunCompare.adj D.sp.cm V ((C * L).map (inclR (F := D.host.F) (AF D.host.F)))) = 0} :=
    (isClosed_eq ((hm.sub continuous_const).matrix_mul continuous_const) continuous_const).inter
    (isClosed_eq ((continuous_const.matrix_mul (hm.sub continuous_const)).matrix_mul continuous_const) continuous_const)
  convert hcl using 1
  exact Set.ext fun g => GlobalTheory.AutFunCompare.mem_unipRad_idem D.sp.cm V C L hL g

theorem not_isCuspFun_const (V : HSp D) {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E} (hC : IsIsoFrame V C)
    {c : ℂ} (hc : c ≠ 0) : ¬ IsCuspFun V fun _ => c := by
  intro h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have : LocallyCompactSpace (NI V C) := (isClosed_NI V hC).locallyCompactSpace
  let i : NIQ V C → GQ V := fun x => ⟨x.1.1, x.2⟩
  have hi : Function.Injective i := fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z : GQ V => z.1) h))
  have : DiscreteTopology (NIQ V C) := DiscreteTopology.of_continuous_injective (f := i)
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _) hi
  have : Countable (NIQ V C) := hi.countable
  have : SecondCountableTopology (NI V C) := TopologicalSpace.Subtype.secondCountableTopology _
  let μ : Measure (NI V C) := Measure.haar
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (NIQ V C) μ
  have h0 := h r C hC μ 𝓕 inferInstance h𝓕 1
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have hint : IntegrableOn (fun _ : NI V C => c) 𝓕 μ := by
    have key : ∀ N : Subgroup (GA D V), N = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.unipRad D.sp.cm V (AF D.host.F) (GlobalTheory.AutFunCompare.colSpan V C) →
        ∀ Q : Subgroup (GA D V), Q = GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.ratPts D.sp.cm V →
        ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Q.subgroupOf N) 𝓕 μ →
          IntegrableOn (fun _ : N => c) 𝓕 μ := by
      rintro N rfl Q rfl μ 𝓕 hμ h𝓕
      exact GlobalTheory.AutFunCompare.integrableOn_constTerm D.sp.cm V _ ((GlobalTheory.AutFunCompare.isIsoFrame_iff V C).1 hC).2
        (fun _ => c) continuous_const (fun _ _ _ => rfl) μ hμ 𝓕 h𝓕 1
    exact key _ (GlobalTheory.AutFunCompare.NI_eq V C) _ (GlobalTheory.AutFunCompare.GQ_eq V) μ 𝓕 inferInstance h𝓕
  have hlt : μ 𝓕 ≠ ⊤ := by
    rcases (integrableOn_const_iff (C := c)).1 hint with h | h
    · exact absurd (by simpa using h) hc
    · exact h.ne
  rw [setIntegral_const, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact ENNReal.toReal_ne_zero.2 ⟨hne, hlt⟩ h0
  · exact hc h0

theorem not_isCuspFun_one_plane (D : D7) : ¬ IsCuspFun (plane D) fun _ => 1 :=
  not_isCuspFun_const _ (isIsoFrame_plane D) one_ne_zero

theorem isRapidDecay_rank_zero (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (hV : V.rank = 0) (φ : GA D V → ℂ) : IsRapidDecay θ V φ := by
  have : IsEmpty (Fin V.rank) := by rw [hV]; infer_instance
  have hs : ∀ g : GA D V, g = 1 := fun g => Subtype.ext (Units.ext (Matrix.ext fun i _ => isEmptyElim i))
  exact fun N => ⟨‖φ 1‖ * (quotHeight θ V 1 : ℝ) ^ N, fun g => by rw [hs g]⟩

theorem quotHeight_rat_mul (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    {γ : GA D V} (hγ : γ ∈ GQ V) (g : GA D V) : quotHeight θ V (γ * g) = quotHeight θ V g := by
  have key : ∀ {γ : GA D V}, γ ∈ GQ V → ∀ g, quotHeight θ V g ≤ quotHeight θ V (γ * g) := fun {γ} hγ g =>
    le_ciInf fun δ => by
      rw [← mul_assoc]
      exact quotHeight_le g (mul_mem δ.2 hγ)
  refine le_antisymm ?_ (key hγ g)
  simpa using key (inv_mem hγ) (γ * g)

end GlobalTheory.CuspDecay.Model

end
end

