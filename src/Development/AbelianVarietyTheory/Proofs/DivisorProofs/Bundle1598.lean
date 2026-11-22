import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1574
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaussianVacuumFramesPlaceSignaturesStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gaussianVacuum_frames_placeSignatures : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : InfinitePlace F → ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ) (D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ)),
    IsCMExt F E σ → FramedD τ JA JB a b A C →
    (∀ u, At (evI F) u → ∀ (f : SInf F κ) x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x) →
    ∃ f₀ : SInf F κ, f₀ ≠ 0 ∧ ∀ (w : InfinitePlace F) (a : Ix (P w) (Q w)) (b : Ix (R w) (S w)) (u u' : Matrix α β (AE F E)),
      At (evI F) u → At (evI F) u' →
      (∀ w', u.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b 1) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      (∀ w', u'.map (piInf (τ w')) = A w' * (Pi.single w (Matrix.single a b Complex.I) : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) w' * (C w')ᵀ) →
      D u f₀ + (lineSign a b * Complex.I) • D u' f₀ = 0 := by
  first | exact @GlobalTheory.HoweD.exists_vacuumD | exact GlobalTheory.HoweD.exists_vacuumD | (intros; apply GlobalTheory.HoweD.exists_vacuumD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarAdelicVectorsBoundsPureTensorsSlices
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix ENNReal Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.WeilAdm.HaarSplit

variable (F : Type) [Field F] [NumberField F] (κ : Type)

def splitE : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃+ (κ → AdeleRing (𝓞 F) F) where
  toFun p := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i)
  invFun x := (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2)
  left_inv p := Prod.ext (funext fun i => RingEquiv.apply_symm_apply _ _) (funext fun i => rfl)
  right_inv x := funext fun i => Prod.ext (RingEquiv.symm_apply_apply _ _) rfl
  map_add' p q := funext fun i => Prod.ext (map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i) (q.1 i)) rfl

theorem splitE_apply (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    splitE F κ p = fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) := rfl

theorem continuous_splitE : Continuous (splitE F κ) := by
  rw [show ⇑(splitE F κ) = fun p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F) =>
    fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (p.1 i), p.2 i) from rfl]
  exact continuous_pi fun i => ((GlobalTheory.Core.Rk.RapidInt.continuous_ofMixed F).comp
    ((continuous_apply i).comp continuous_fst)).prodMk ((continuous_apply i).comp continuous_snd)

theorem continuous_splitE_symm : Continuous (splitE F κ).symm := by
  rw [show ⇑(splitE F κ).symm = fun x : κ → AdeleRing (𝓞 F) F =>
    ((fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1, fun i => (x i).2) :
      (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) from rfl]
  exact (continuous_pi fun i => (GlobalTheory.Core.Rk.RapidInt.continuous_toMixed F).comp
    (continuous_fst.comp (continuous_apply i))).prodMk (continuous_pi fun i => continuous_snd.comp (continuous_apply i))

theorem pureA_splitE (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ)
    (p : (κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) :
    GlobalTheory.WeilM.pureA F f g (splitE F κ p) = f p.1 * g p.2 := by
  simp only [GlobalTheory.WeilM.pureA, splitE_apply, RingEquiv.apply_symm_apply]

theorem continuous_comp_splitE [Fintype κ] (Φ : (κ → AdeleRing (𝓞 F) F) → ℂ) (hΦ : Φ ∈ GlobalTheory.WeilM.schA F κ) :
    Continuous fun p => Φ (splitE F κ p) := by
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    simp only [pureA_splitE]
    exact (f.continuous.comp continuous_fst).mul (hg.1.continuous.comp continuous_snd)
  | zero => exact continuous_const
  | add x x' _ _ hx hx' => exact hx.add hx'
  | smul a x _ hx => exact hx.const_smul a

theorem splitE_add_finE (z : κ → mixedEmbedding.mixedSpace F) (y u : κ → FiniteAdeleRing (𝓞 F) F) :
    splitE F κ (z, y + u) = splitE F κ (z, y) + GlobalTheory.WeilAdm.finE F u :=
  funext fun i => Prod.ext (add_zero _).symm rfl

theorem volume_isAddHaar [Fintype κ] : (volume : Measure (κ → mixedEmbedding.mixedSpace F)).IsAddHaarMeasure := by
  haveI : MeasurableAdd (mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  exact Measure.pi.isAddHaarMeasure _

end GlobalTheory.WeilAdm.HaarSplit

namespace GlobalTheory.WeilAdm.HaarSplit

open GlobalTheory.WeilAdm.HaarSplit

theorem haar_pure_slice_bounds : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
    g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) → ∀ U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      ∃ μ : @Measure (κ → AdeleRing (𝓞 F) F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ ∧
        ∃ C c : ℝ≥0∞, C ≠ ⊤ ∧ c ≠ 0 ∧ c ≠ ⊤ ∧
          (∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, ∫⁻ x, ‖GlobalTheory.WeilM.pureA F f g x‖ₑ ^ 2 ∂μ ≤ C * ∫⁻ z, ‖f z‖ₑ ^ 2) ∧
          ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ x, ∀ u ∈ U, Φ (x + GlobalTheory.WeilAdm.finE F u) = Φ x) →
            ∀ y, c * ∫⁻ z, ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2 ≤ ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ := by
  intro F _ _ κ _ g hg U hU
  haveI := volume_isAddHaar F κ
  haveI : OpensMeasurableSpace (κ → mixedEmbedding.mixedSpace F) := inferInstance
  haveI : LocallyCompactSpace (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F
  haveI : SecondCountableTopology (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F
  haveI : T2Space (FiniteAdeleRing (𝓞 F) F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  letI mY : MeasurableSpace (κ → FiniteAdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → FiniteAdeleRing (𝓞 F) F) := ⟨rfl⟩
  letI mA : MeasurableSpace (κ → AdeleRing (𝓞 F) F) := borel _
  haveI : BorelSpace (κ → AdeleRing (𝓞 F) F) := ⟨rfl⟩
  haveI : SigmaCompactSpace (κ → FiniteAdeleRing (𝓞 F) F) := sigmaCompactSpace_of_locallyCompact_secondCountable
  set ν : Measure (κ → FiniteAdeleRing (𝓞 F) F) := Measure.addHaar with hν
  haveI : SFinite ν := inferInstance
  haveI : MeasurableAdd (κ → mixedEmbedding.mixedSpace F) := ContinuousAdd.measurableAdd
  haveI : MeasurableAdd (κ → FiniteAdeleRing (𝓞 F) F) := ContinuousAdd.measurableAdd
  haveI : ν.IsAddHaarMeasure := by rw [hν]; infer_instance
  haveI : ((volume : Measure (κ → mixedEmbedding.mixedSpace F)).prod ν).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure (κ → mixedEmbedding.mixedSpace F)) ν
  have hμH : Measure.IsAddHaarMeasure ((volume.prod ν).map (splitE F κ)) :=
    (splitE F κ).isAddHaarMeasure_map _ (continuous_splitE F κ) (continuous_splitE_symm F κ)
  let em : ((κ → mixedEmbedding.mixedSpace F) × (κ → FiniteAdeleRing (𝓞 F) F)) ≃ᵐ (κ → AdeleRing (𝓞 F) F) :=
    (Homeomorph.mk (splitE F κ).toEquiv (continuous_splitE F κ) (continuous_splitE_symm F κ)).toMeasurableEquiv
  have hint : ∀ h : (κ → AdeleRing (𝓞 F) F) → ℝ≥0∞,
      ∫⁻ x, h x ∂((volume.prod ν).map (splitE F κ)) = ∫⁻ p, h (splitE F κ p) ∂(volume.prod ν) :=
    fun h => lintegral_map_equiv h em

  have hgc : Continuous g := hg.1.continuous
  have hC : ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν ≠ ⊤ := by
    have h1 : ∫⁻ y, ‖g y * g y‖ₑ ∂ν < ⊤ :=
      ((hgc.mul hgc).integrable_of_hasCompactSupport (hg.2.mul_left (f := g))).2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq (lintegral_congr fun y => ?_)) h1)
    rw [enorm_mul, sq]

  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : κ → FiniteAdeleRing (𝓞 F) F)
  set S : Set (κ → FiniteAdeleRing (𝓞 F) F) := (U : Set _) ∩ K with hS
  have hSm : MeasurableSet S := hU.measurableSet.inter hKc.isClosed.measurableSet
  have hc0 : ν S ≠ 0 := by
    refine ne_of_gt (lt_of_lt_of_le ?_ (measure_mono (Set.inter_subset_inter_right _ interior_subset)))
    exact (hU.inter isOpen_interior).measure_pos ν ⟨0, U.zero_mem, mem_interior_iff_mem_nhds.2 hK0⟩
  have hcT : ν S ≠ ⊤ := ne_top_of_le_ne_top hKc.measure_lt_top.ne (measure_mono Set.inter_subset_right)
  refine ⟨(volume.prod ν).map (splitE F κ), hμH, ∫⁻ y, ‖g y‖ₑ ^ 2 ∂ν, ν S, hC, hc0, hcT, ?_, ?_⟩
  · intro f
    rw [hint]
    have e1 : ∀ p, ‖GlobalTheory.WeilM.pureA F f g (splitE F κ p)‖ₑ ^ 2 = ‖f p.1‖ₑ ^ 2 * ‖g p.2‖ₑ ^ 2 := by
      intro p
      rw [pureA_splitE, enorm_mul, mul_pow]
    simp_rw [e1]
    rw [lintegral_prod_mul (f.continuous.measurable.enorm.pow_const 2).aemeasurable
      (hgc.measurable.enorm.pow_const 2).aemeasurable, mul_comm]
  · intro Φ hΦ hinv y
    rw [hint]
    have hHm : Measurable fun p => ‖Φ (splitE F κ p)‖ₑ ^ 2 :=
      (continuous_comp_splitE F κ Φ hΦ).measurable.enorm.pow_const 2
    rw [lintegral_prod _ hHm.aemeasurable, ← lintegral_const_mul' _ _ hcT]
    refine lintegral_mono fun z => ?_
    set T : Set (κ → FiniteAdeleRing (𝓞 F) F) := (fun y' => y' + -y) ⁻¹' S with hT
    have hTm : MeasurableSet T := hSm.preimage (continuous_add_right (-y)).measurable
    have hνT : ν T = ν S := measure_preimage_add_right ν (-y) S
    calc ν S * ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2
        = ∫⁻ y', T.indicator (fun _ => ‖GlobalTheory.WeilAdm.slice F Φ y z‖ₑ ^ 2) y' ∂ν := by
          rw [lintegral_indicator_const hTm, hνT, mul_comm]
      _ ≤ ∫⁻ y', ‖Φ (splitE F κ (z, y'))‖ₑ ^ 2 ∂ν := by
          refine lintegral_mono fun y' => (Set.indicator_le (g := fun y' => ‖Φ (splitE F κ (z, y'))‖ₑ ^ 2) (fun a ha => le_of_eq ?_)) y'
          have hu : a + -y ∈ U := ha.1
          have ha' : a = y + (a + -y) := by abel
          show ‖Φ (splitE F κ (z, y))‖ₑ ^ 2 = ‖Φ (splitE F κ (z, a))‖ₑ ^ 2
          rw [ha', splitE_add_finE, hinv _ _ hu]

end GlobalTheory.WeilAdm.HaarSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackAlong
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.UPel.HT.Pull

theorem tanScal_iff {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] (A : Over S) [GrpObj A] (A' : Over S')
    [GrpObj A'] (φ : A'.left ⟶ A.left) (act : GlobalTheory.UPel.HT.OActN O A) (act' : GlobalTheory.UPel.HT.OActN O A')
    (h : IsGrpPullback A' A f φ) (hact : ∀ c, (act'.act c).left ≫ φ = φ ≫ (act.act c).left) (R' : Type) [CommRing R']
    (x : Sp R' ⟶ S') (b : O) (c : R') (v : GlobalTheory.UPel.HT.epsPtR x ⟶ A') (v₀ : GlobalTheory.UPel.HT.epsPtR (x ≫ f) ⟶ A)
    (hv : v₀.left = v.left ≫ φ) :
    GlobalTheory.UPel.HT.IsTanScal act' x b c v ↔ GlobalTheory.UPel.HT.IsTanScal act (x ≫ f) b c v₀ := by
  have one : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ A').left ≫ φ :=
    (congrArg (fun z => z.left) (map_one (pushHom h (Over.mk x)))).symm
  have sc : spMap (epsScaleR c) ≫ spMap (algebraMap R' (DualNumber R')) =
      spMap (algebraMap R' (DualNumber R')) := by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have fs : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
    ext a
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  have E : (v₀ ≫ act.act b).left = (v ≫ act'.act b).left ≫ φ := by
    rw [Over.comp_left, Over.comp_left, hv, Category.assoc, Category.assoc, hact]
  refine and_congr ?_ ?_
  · rw [one, hv]
    refine ⟨fun E => by rw [← E]; exact (Category.assoc _ _ _).symm,
      fun E => h.1.hom_ext ((Category.assoc _ _ _).trans E) ?_⟩
    refine ((Category.assoc _ _ _).trans ?_).trans (Over.w (1 : Over.mk x ⟶ A')).symm
    refine (congrArg (spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ x) fs).trans (Category.id_comp _))
  · rw [E, hv]
    refine ⟨fun E' => by rw [E']; exact Category.assoc _ _ _,
      fun E' => h.1.hom_ext (E'.trans (Category.assoc _ _ _).symm) ?_⟩
    refine (Over.w (v ≫ act'.act b)).trans (Eq.symm ((Category.assoc _ _ _).trans ?_))
    refine (congrArg (spMap (epsScaleR c) ≫ ·) (Over.w v)).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ x) sc)

theorem kerGen {S S' : Scheme.{0}} {f : S' ⟶ S} (A : Over S) [GrpObj A] (A' : Over S') [GrpObj A']
    (φ : A'.left ⟶ A.left) (h : IsGrpPullback A' A f φ) (P : LB (G2 A).left) (T : Over S') (x : T ⟶ A')
    (ht : ∃ t : ((P.pull (sqMap h.1.w)).pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    ∃ t : (P.pull (lift (snd A (Over.mk (T.hom ≫ f)) ≫ pushPt h.1.w x) (fst A (Over.mk (T.hom ≫ f)))).left).Gen,
      t.IsGen := by
  obtain ⟨t, ht⟩ := ht
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  let Z' : Over S' := Over.mk ((snd A T₀).left ≫ T.hom)
  have eq : (fst A T₀).left ≫ A.hom = Z'.hom ≫ f :=
    (Over.w (fst A T₀)).trans ((Over.w (snd A T₀)).symm.trans (Category.assoc _ _ _).symm)
  let a' : Z' ⟶ A' := Over.homMk (h.1.lift (fst A T₀).left Z'.hom eq) (h.1.lift_snd _ _ _)
  let t' : Z' ⟶ T := Over.homMk (snd A T₀).left rfl
  let u : Over.mk (Z'.hom ≫ f) ⟶ A ⊗ T₀ := Over.homMk (𝟙 _) (by
    show 𝟙 _ ≫ (A ⊗ T₀).hom = ((snd A T₀).left ≫ T.hom) ≫ f
    rw [Category.id_comp, Category.assoc]
    exact (Over.w (snd A T₀)).symm)
  have hc : (lift (t' ≫ x) a').left ≫ sqMap h.1.w = u.left ≫ (lift (snd A T₀ ≫ pushPt h.1.w x) (fst A T₀)).left :=
    sqMap_of h.1.w u _ _ _ _ (Over.OverMorphism.ext (by
      show ((snd A T₀).left ≫ x.left) ≫ φ = 𝟙 _ ≫ (snd A T₀).left ≫ x.left ≫ φ
      rw [Category.id_comp, Category.assoc]))
      (Over.OverMorphism.ext (by
        show h.1.lift (fst A T₀).left Z'.hom eq ≫ φ = 𝟙 _ ≫ (fst A T₀).left
        rw [Category.id_comp, h.1.lift_fst]))
  have hψ : (lift a' t').left ≫ (lift (snd A' T ≫ x) (fst A' T)).left = (lift (t' ≫ x) a').left := by
    rw [← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst]
  obtain ⟨t₁, ht₁⟩ := gen_chartPull (chartPullIn P (fun _ : PUnit => sqMap h.1.w) (fun _ => 1)
    (lift (snd A' T ≫ x) (fst A' T)).left) t ht
  refine gen_chartPull (chartPullSame P (fun _ : PUnit => (lift (snd A T₀ ≫ pushPt h.1.w x) (fst A T₀)).left)
    (fun _ => (lift (snd A' T ≫ x) (fst A' T)).left ≫ sqMap h.1.w) (fun _ => 1) (lift a' t').left fun _ => ?_) t₁ ht₁
  rw [← Category.assoc, hψ, hc]
  exact (Category.id_comp _).symm

end GlobalTheory.UPel.HT.Pull

namespace GlobalTheory.UPel.HT.Pull

open GlobalTheory.UPel.HT

theorem exists_objMap : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (S S' : Scheme.{0}) (s : S ⟶ Sp R) (f : S' ⟶ S) (o : GlobalTheory.UPel.HT.Obj b N s), ∃ o' : GlobalTheory.UPel.HT.Obj b N (f ≫ s), Nonempty (GlobalTheory.UPel.HT.ObjMap o' o f) := by
  intro p _ D R _ b N S S' s f o
  have h := isGrpPullback_pullback o.A f
  have hact := OActN.pullback_left f o.A o.act
  have w := h.1.w
  let A' := (Over.pullback f).obj o.A
  let φ := pullback.fst o.A.hom f
  let act' := OActN.pullback f o.A o.act
  let φ₂ := sqMap w
  let P' := o.P.pull φ₂
  let u : Over.mk (A'.hom ≫ f) ⟶ o.A := Over.homMk φ w
  let U : Over.mk ((G2 A').hom ≫ f) ⟶ G2 o.A := lift (pushPt w (fst A' A')) (pushPt w (snd A' A'))
  have pa : ∀ {T : Over S'} (x : T ⟶ A') c, pushPt w (x ≫ act'.act c) = pushPt w x ≫ o.act.act c := fun x c =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  have p1 : ∀ (T : Over S'), pushPt w (1 : T ⟶ A') = 1 := fun T => map_one (pushHom h T)
  have hP' : P'.IsLB := pull_isLB o.isLB φ₂

  have hΔ : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left :=
    sqMap_of w u _ _ _ _ (Over.OverMorphism.ext (by simp [u, φ, pushPt_left])) (Over.OverMorphism.ext (by simp [u, φ, pushPt_left]))
  have hL : LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).pull φ) :=
    LBIso.chartPull (chartPullOut o.P (fun _ => φ₂) (fun _ => 1) _ (fun _ => _ ≫ φ₂) fun _ => rfl)
      (chartPullOut o.P (fun _ => _) (fun _ => 1) φ (fun _ => _ ≫ φ₂) fun _ => hΔ)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB o.isLB _))
  obtain ⟨hab, hamp, -⟩ := GlobalTheory.PolPull.pol_pull_of_relAmple_local GlobalTheory.AmpleLocal.relAmple_of_locally S S' o.A A' f φ
    _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) o.ab h hL

  have r₁ : (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left :=
    sqMap_of w u _ _ _ _ ((p1 A').trans (MonObj.comp_one u).symm) (Over.OverMorphism.ext (by simp [u, φ, pushPt_left]))
  have r₂ : (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 o.A) (1 : o.A ⟶ o.A)).left :=
    sqMap_of w u _ _ _ _ (Over.OverMorphism.ext (by simp [u, φ, pushPt_left])) ((p1 A').trans (MonObj.comp_one u).symm)
  have sw : (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd o.A o.A) (fst o.A o.A)).left :=
    sqMap_of w U _ _ _ _ (lift_snd _ _).symm (lift_fst _ _).symm
  have ro : ∀ c : D.O, (lift (fst A' A' ≫ act'.act c) (snd A' A')).left ≫ φ₂ =
      φ₂ ≫ (lift (fst o.A o.A ≫ o.act.act c) (snd o.A o.A)).left := fun c =>
    sqMap_of w U _ _ _ _ (by rw [pa, ← Category.assoc, lift_fst]) (lift_snd _ _).symm
  have ro' : ∀ c : D.O, (lift (fst A' A') (snd A' A' ≫ act'.act c)).left ≫ φ₂ =
      φ₂ ≫ (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act c)).left := fun c =>
    sqMap_of w U _ _ _ _ (lift_fst _ _).symm (by rw [pa, ← Category.assoc, lift_snd])
  have pul : ∀ {Y : Scheme.{0}} (g' : Y ⟶ (G2 A').left) {Y₀ : Scheme.{0}} (k : Y ⟶ Y₀) (g₀ : Y₀ ⟶ (G2 o.A).left), g' ≫ φ₂ = k ≫ g₀ → ChartPull (P'.pull g') (o.P.pull g₀) k :=
    fun g' _ k g₀ e => chartPullLinComb o.P φ₂ (fun _ => g') (fun _ => g₀) (fun _ => 1) k fun _ => e
  refine ⟨{ A := A'
            ab := hab
            act := act'
            P := P'
            isLB := hP'
            rig₁ := ?_
            rig₂ := ?_
            symm := ?_
            ample := hamp o.ample
            kerP := ?_
            rosati := ?_
            lie := ?_
            lieRank := ?_
            eta := fun y => GlobalTheory.ObjPull.secPull h (o.eta y)
            eta_add := fun x y => by rw [o.eta_add, map_mul]
            eta_lin := ?_
            eta_ker := fun x => by rw [o.eta_ker, map_one]
            geom := ?_ },
    ⟨{ φ := φ
       φ₂ := φ₂
       cart := h
       sq := isSquare_sqMap w
       act := hact
       pol := GlobalTheory.PolBaseChange.lbIso_refl hP'
       eta := fun y => GlobalTheory.ObjPull.secPull_left h _ }⟩⟩
  · obtain ⟨t, ht⟩ := o.rig₁
    exact gen_chartPull (pul _ φ _ r₁) t ht
  · obtain ⟨t, ht⟩ := o.rig₂
    exact gen_chartPull (pul _ φ _ r₂) t ht
  · exact LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o.P φ₂ φ₂ rfl) (pul _ φ₂ _ sw) o.symm
  · obtain ⟨e, he, hk⟩ := o.kerP
    refine ⟨e, he, fun T x hx => ?_⟩
    have h0 := hk _ (pushPt w x) (kerGen o.A A' φ h o.P T x hx)
    apply (GlobalTheory.ObjPull.pushEquiv h T).injective
    rw [map_pow, map_one]
    exact h0
  · intro c
    exact LBIso.chartPull (pul _ φ₂ _ (ro c)) (pul _ φ₂ _ (ro' _)) (o.rosati c)
  · intro R' _ β x hx v hv
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv h (epsPtR x) (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f)
      (Category.assoc _ _ _).symm
    have key := fun (c : D.O) (r : R') (v : epsPtR x ⟶ A') =>
      tanScal_iff f o.A A' φ o.act act' h hact R' x c r v (e v) (he v)
    obtain ⟨w₀, hw₀, hv₀⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc]; exact hx) (e v) ((key _ _ v).1 hv)
    refine ⟨fun i => e.symm (w₀ i), fun i c => (key _ _ _).2 (by rw [MulEquiv.apply_symm_apply]; exact hw₀ i c), ?_⟩
    apply e.injective
    rw [hv₀, map_list_prod, List.map_ofFn]
    simp [Function.comp_def]
  · intro k _ _ x β hx i
    exact (GlobalTheory.LiePull.lieMult_pull _ S S' o.A A' f φ (o.act.toF D) (act'.toF D) h (fun c => hact _) k x _ _).2
      (o.lieRank k (x ≫ f) β (by rw [Category.assoc]; exact hx) i)
  · intro c y
    rw [o.eta_lin]
    apply (GlobalTheory.ObjPull.pushEquiv h _).injective
    apply Over.OverMorphism.ext
    show (GlobalTheory.ObjPull.secPull h (o.eta y ≫ o.act.act c)).left ≫ φ =
      (GlobalTheory.ObjPull.secPull h (o.eta y) ≫ act'.act c).left ≫ φ
    rw [GlobalTheory.ObjPull.secPull_left, Over.comp_left, Over.comp_left, Category.assoc, hact,
      reassoc_of% (GlobalTheory.ObjPull.secPull_left h (o.eta y))]
  · intro k _ _ x β hx
    obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc]; exact hx)
    refine ⟨tateMoveO (GlobalTheory.ObjPull.pushEquiv h (Over.mk x)) (fun c g => ?_) (fun n g g' z hz => ?_) I, fun y => ?_⟩
    · apply Over.OverMorphism.ext
      show (g.left ≫ _) ≫ φ = (g.left ≫ φ) ≫ _
      rw [Category.assoc, hact, Category.assoc]
    · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A A' f φ _ _ (pull_isLB o.isLB _) (pull_isLB hP' _) h hL
        (Over.mk x) n g g' _ _ _ rfl rfl).2 hz
    · rw [tateMoveO_ev]
      exact (MulEquiv.eq_symm_apply _).2 ((GlobalTheory.ObjPull.pushEquiv_secPull h _ _).trans (hI y))

end GlobalTheory.UPel.HT.Pull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdealSectionsEq
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace GlobalTheory.IdealSectionsFactorization

theorem comp_eq_iff_factors {S X B W : Scheme.{0}} (p : X ⟶ B) (x y : S ⟶ X)
    (h : x ≫ p = y ≫ p) (g : W ⟶ S) :
    g ≫ x = g ≫ y ↔
      ∃ l : W ⟶ pullback (pullback.lift x y h) (pullback.diagonal p),
        l ≫ pullback.fst _ _ = g := by
  constructor
  · intro hg
    refine ⟨pullback.lift g (g ≫ x) ?_, pullback.lift_fst _ _ _⟩
    apply pullback.hom_ext
    · simp [pullback.diagonal_fst, pullback.lift_fst]
    · simp [pullback.diagonal_snd, pullback.lift_snd, hg]
  · rintro ⟨l, rfl⟩
    have hc := pullback.condition (f := pullback.lift x y h) (g := pullback.diagonal p)
    have h1 := congrArg (· ≫ pullback.fst p p) hc
    have h2 := congrArg (· ≫ pullback.snd p p) hc
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.diagonal_fst,
      pullback.diagonal_snd, Category.comp_id] at h1 h2
    rw [Category.assoc, Category.assoc, h1, h2]

theorem factors_iff_kills {R T : Type} [CommRing R] [CommRing T] (I : Ideal R) (ψ : R →+* T) :
    (∃ l : Spec (CommRingCat.of T) ⟶ Spec (CommRingCat.of (R ⧸ I)),
      l ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = Spec.map (CommRingCat.ofHom ψ)) ↔
      ∀ r ∈ I, ψ r = 0 := by
  constructor
  · rintro ⟨l, hl⟩ r hr
    obtain ⟨φ, rfl⟩ := Spec.map_surjective l
    rw [← Spec.map_comp] at hl
    have h := Spec.map_injective hl
    have h' : φ.hom (Ideal.Quotient.mk I r) = ψ r :=
      congrArg (fun k : CommRingCat.of R ⟶ CommRingCat.of T => k.hom r) h
    rw [← h', Ideal.Quotient.eq_zero_iff_mem.mpr hr, map_zero]
  · intro h
    refine ⟨Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I ψ h)), ?_⟩
    rw [← Spec.map_comp]
    congr 1

theorem exists_ideal_sections_eq (R : Type) [CommRing R]
    (X : Over (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) (hX : IsSeparated X.hom)
    (x y : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ X.left)
    (hx : x ≫ X.hom = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R))
    (hy : y ≫ X.hom = 𝟙 (ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R)) :
    ∃ I : Ideal R, ∀ (T : Type) [CommRing T] (ψ : R →+* T),
      ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ x = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ ≫ y ↔
        ∀ r ∈ I, ψ r = 0 := by
  have h : x ≫ X.hom = y ≫ X.hom := hx.trans hy.symm
  have hc : IsClosedImmersion
      (pullback.fst (pullback.lift x y h) (pullback.diagonal X.hom)) :=
    IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback _ _).flip hX.isClosedImmersion_diagonal
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp hc
  refine ⟨I, fun T _ ψ => ?_⟩
  rw [comp_eq_iff_factors X.hom x y h, ← factors_iff_kills I ψ, he]
  constructor
  · rintro ⟨l, hl⟩
    exact ⟨l ≫ e.hom, by rw [Category.assoc]; exact hl⟩
  · rintro ⟨l, hl⟩
    exact ⟨l ≫ e.inv, by rw [Category.assoc, e.inv_hom_id_assoc]; exact hl⟩

end GlobalTheory.IdealSectionsFactorization
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectivePointsLargerFieldGalois
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Published.AbVarRed

def ptOverMap {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') :
    ptOver K Ω' ⟶ ptOver K Ω :=
  Over.homMk (spMap (j : Ω →+* Ω')) (by
    change spMap _ ≫ spMap _ = spMap _
    rw [← Spec.map_comp]
    congr 1
    ext x
    simp)

theorem epi_ptOverMap {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') :
    Epi (ptOverMap j).left := by
  change Epi (spMap (j : Ω →+* Ω'))
  letI := (j : Ω →+* Ω').toAlgebra
  haveI : Flat (spMap (j : Ω →+* Ω')) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat Ω Ω')
  haveI : Surjective (spMap (j : Ω →+* Ω')) :=
    ⟨fun p => ⟨(⊥ : PrimeSpectrum Ω'), Subsingleton.elim (α := PrimeSpectrum Ω) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem ptOverMap_comp_specAut {K Ω Ω' : Type} [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω']
    (j : Ω →ₐ[K] Ω') (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω') (h : ∀ x, σ' (j x) = j (σ x)) :
    ptOverMap j ≫ specAut σ = specAut σ' ≫ ptOverMap j :=
  Over.OverMorphism.ext (by
    change spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (h x).symm)

theorem exists_injective_ptOver_galois : ∀ (K Ω Ω' : Type) [Field K] [Field Ω] [Field Ω'] [Algebra K Ω] [Algebra K Ω'] (j : Ω →ₐ[K] Ω') (A : Over (Sp K)) [GrpObj A], ∃ f : (ptOver K Ω ⟶ A) →* (ptOver K Ω' ⟶ A), Function.Injective f ∧ ∀ (σ : Ω ≃ₐ[K] Ω) (σ' : Ω' ≃ₐ[K] Ω'), (∀ x, σ' (j x) = j (σ x)) → ∀ x, f (specAut σ ≫ x) = specAut σ' ≫ f x := by
  intro K Ω Ω' _ _ _ _ _ j A _
  refine ⟨MonoidHom.mk' (fun x => ptOverMap j ≫ x) fun x y => MonObj.comp_mul _ x y, ?_, ?_⟩
  · intro x y e
    have := epi_ptOverMap j
    exact Over.OverMorphism.ext ((cancel_epi (ptOverMap j).left).1
      (by simpa using congrArg (fun q => q.left) (show ptOverMap j ≫ x = ptOverMap j ≫ y from e)))
  · intro σ σ' h x
    change ptOverMap j ≫ specAut σ ≫ x = specAut σ' ≫ ptOverMap j ≫ x
    rw [← Category.assoc, ptOverMap_comp_specAut j σ σ' h, Category.assoc]

end GlobalTheory.Published.AbVarRed

end
end

