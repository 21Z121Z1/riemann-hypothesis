import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.GlobalDifferentialForms.PullHEq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SerreClassOfCechSpectralSequence
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0033
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0622
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0644
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0614
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Birational
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0633
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermConvolutionHecke
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0616
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0607

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDoubleComplexMap
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Om CrystallineSemistableComparison.Om.Glob GlobalTheory.CompanionTheory.CechSerre
universe w

noncomputable section

namespace GlobalTheory.CompanionTheory.CechSerre

section MorDbl

variable {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ ModuleCat.{0} R} {F' : C' ⥤ ModuleCat.{0} R} {ι ι' : Type}
  {U : ι → ObjectProperty C} {U' : ι' → ObjectProperty C'} {hU : ∀ α, Cosieve (U α)}
  {hU' : ∀ α, Cosieve (U' α)}

def nerveG (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (p : ℕ) :
    (CH.cech (idxπ U' hU') p).Elements ⥤ (CH.cech (idxπ U hU) p).Elements where
  obj x := ⟨m.G.obj x.1, ⟨fun k => ⟨τ (x.2.1 k).1, hτ _ _ (x.2.1 k).2⟩, fun _ _ => rfl⟩⟩
  map {x y} f := ⟨m.G.map f.1, Subtype.ext (funext fun k => Subtype.ext
    (congrArg (fun z : (CH.cech (idxπ U' hU') p).obj y.1 => τ (z.1 k).1) f.2))⟩
  map_id x := Subtype.ext (m.G.map_id _)
  map_comp f g := Subtype.ext (m.G.map_comp _ _)

def nerveM (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) (p : ℕ) :
    CH.Mor (CH.elF (CH.cech (idxπ U hU) p) F) (CH.elF (CH.cech (idxπ U' hU') p) F') (RingHom.id R) where
  G := nerveG m τ hτ p
  τ T := m.τ T.1
  nat φ x := m.nat φ.1 x

theorem nerveM_face (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T))
    (p q : ℕ) (k : Fin (p + 2)) (x : CH.Cn (CH.elF (CH.cech (idxπ U hU) p) F) q) :
    (CH.elMor (CH.cechMap (idxπ U' hU') k.succAbove) F').pullC q ((nerveM (hU := hU) (hU' := hU') m τ hτ p).pullC q x) =
      (nerveM (hU := hU) (hU' := hU') m τ hτ (p + 1)).pullC q ((CH.elMor (CH.cechMap (idxπ U hU) k.succAbove) F).pullC q x) :=
  rfl

def dblHom (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)) :
    DCx.Hom (dbl U hU F) (dbl U' hU' F') (RingHom.id R) where
  f p q := (nerveM m τ hτ p).pullC q
  ch p q x := by
    refine (Cos.d_apply ((CH.cechCos (idxπ U' hU') F').cos q) p _).trans ?_
    refine Eq.trans ?_ (congrArg _ (Cos.d_apply ((CH.cechCos (idxπ U hU) F).cos q) p x).symm)
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_zsmul]
    exact congrArg _ (nerveM_face m τ hτ p q k x)
  cv p q x := (nerveM m τ hτ p).d_pullC q x

theorem cls_eq_of_eq {K : Cx.{1} R} {n : ℕ} {a b : K.X n} (h : a = b) (ha : K.d n a = 0) (hb : K.d n b = 0) :
    K.cls a ha = K.cls b hb := by
  subst h; rfl

theorem dblHom_sgl {K L : DCx.{1} R} (φ : DCx.Hom K L (RingHom.id R)) (a b : ℕ) (y : K.X a b) (p q : ℕ) :
    φ.f p q (K.sgl a b y p q) = L.sgl a b (φ.f a b y) p q := by
  by_cases h : p = a ∧ q = b
  · obtain ⟨rfl, rfl⟩ := h
    rw [K.sgl_self, L.sgl_self]
  · rw [K.sgl_ne _ (by omega), L.sgl_ne _ (by omega), map_zero]

end MorDbl

theorem dbl_mor : ∀ {R : Type} [CommRing R] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] (F : C ⥤ ModuleCat.{0} R)
    (F' : C' ⥤ ModuleCat.{0} R) {ι ι' : Type} (U : ι → ObjectProperty C) (U' : ι' → ObjectProperty C') (hU : ∀ α, Cosieve (U α))
    (hU' : ∀ α, Cosieve (U' α)) (m : CH.Mor F F' (RingHom.id R)) (τ : ι' → ι) (hτ : ∀ α T, U' α T → U (τ α) (m.G.obj T)),
    ∃ φ : DCx.Hom (dbl U hU F) (dbl U' hU' F') (RingHom.id R),
      (∀ n (x : CH.H F n), φ.tot.mapH n ((CH.cechAugRow (idxπ U hU) F).edge.mapH n
          ((CH.Mor.restrict F (CategoryOfElements.π ((Functor.const C).obj PUnit.{1}))).hom.mapH n x)) =
        (CH.cechAugRow (idxπ U' hU') F').edge.mapH n
          ((CH.Mor.restrict F' (CategoryOfElements.π ((Functor.const C').obj PUnit.{1}))).hom.mapH n (m.pull n x))) ∧
      ∀ p q (x : ((dbl U hU F).col p).H q) (i : Fin (p + 1) → ι'),
        (tupM U' hU' F' i).pull q ((φ.col p).mapH q x) =
          (morU m (U := capT U (τ ∘ i)) (U' := capT U' i) fun T hT k => hτ (i k) T (hT k)).pull q ((tupM U hU F (τ ∘ i)).pull q x) := by
  intro R _ C C' _ _ F F' ι ι' U U' hU hU' m τ hτ
  refine ⟨dblHom m τ hτ, fun n x => ?_, fun p q x i => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := (P.cls_surj (CH.cx F) n).1 x
    refine cls_eq_of_eq (Subtype.ext (funext fun p => funext fun q => ?_)) _ _
    exact dblHom_sgl (dblHom m τ hτ) 0 n _ p q
  · obtain ⟨a, ha, rfl⟩ := (P.cls_surj ((dbl U hU F).col p) q).1 x
    exact cls_eq_of_eq rfl _ _

end GlobalTheory.CompanionTheory.CechSerre
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartGramFirstEntryStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_gram_first_entry : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] (n : ℕ) (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) → gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 0 = hR R σ (hypOne J) (x 0) (x 0) ∧ (∀ j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) 0 j.succ = s 0 j) ∧ ∀ i j : Fin n, gramR R σ (hypOne J) (chartS R σ J x a s Y) i.succ j.succ = gramR R σ J Y i j + (sigR R σ (a 0 i) * s 0 j + sigR R σ (s 0 i) * a 0 j - hR R σ (hypOne J) (x 0) (x 0) * (sigR R σ (a 0 i) * a 0 j)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.ChartGram.gramR_chartS | exact GlobalTheory.CompanionTheory.WeilSiegel.ChartGram.gramR_chartS | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.ChartGram.gramR_chartS <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIntegralFormulaHyperbolic
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStage

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem lintegral_tuple_vH {T : Type} [MeasurableSpace T] (m : Measure T) [SigmaFinite m] (n M : ℕ)
    (ψ : (Fin n → Fin (M + 2) → T) → ℝ≥0∞) (hψ : Measurable ψ) :
    ∫⁻ Y, ψ Y ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin (M + 2) => m) =
      ∫⁻ a : Fin 1 → Fin n → T, ∫⁻ s : Fin 1 → Fin n → T, ∫⁻ Y : Fin n → Fin M → T,
        ψ (fun j => vH (a 0 j) (s 0 j) (Y j))
        ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m)
        ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m) := by
  have hu : ∀ f : (Fin n → T) → ℝ≥0∞,
      ∫⁻ a : Fin 1 → Fin n → T, f (a 0) ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m) =
        ∫⁻ c, f c ∂(Measure.pi fun _ : Fin n => m) := fun f =>
    (measurePreserving_funUnique (Measure.pi fun _ : Fin n => m) (Fin 1)).lintegral_comp_emb
      (MeasurableEquiv.measurableEmbedding _) f
  have hc : ∀ c : Fin n → T, Measurable fun X : Fin n → Fin (M + 1) → T =>
      ψ (fun a => Fin.cons (c a) (X a)) := by
    intro c
    refine hψ.comp (measurable_pi_iff.2 fun a => ?_)
    exact (TupFubini.measurable_cons_tail (c a)).comp (measurable_pi_apply a)
  rw [TupFubini.lintegral_tuple_first_coord m n (M + 1) ψ hψ]
  refine Eq.trans ?_ (hu fun c => ∫⁻ s : Fin 1 → Fin n → T, ∫⁻ Y : Fin n → Fin M → T,
    ψ (fun j => vH (c j) (s 0 j) (Y j)) ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)
    ∂(Measure.pi fun _ : Fin 1 => Measure.pi fun _ : Fin n => m)).symm
  refine lintegral_congr fun c => ?_
  rw [TupFubini.lintegral_tuple_first_coord m n M _ (hc c)]
  exact (hu fun c' => ∫⁻ Y : Fin n → Fin M → T, ψ (fun j => vH (c j) (c' j) (Y j))
    ∂(Measure.pi fun _ : Fin n => Measure.pi fun _ : Fin M => m)).symm

theorem lintegral_chartS_of_unitary (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J)
    (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R)
    (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞) (hg : Measurable g)
    (hg0 : ∀ X, ¬ IsUnit (X 0 0) → g X = 0)
    (hc : ∀ x : Fin (M + 2) → R ⊗[F] E, IsUnit (x 0) → ∃ c : HA R σ (hypOne J), ∀ v,
      ((HA.mat R σ (hypOne J) c : GL (Fin (M + 2)) (R ⊗[F] E)) :
        Matrix (Fin (M + 2)) (Fin (M + 2)) (R ⊗[F] E)).mulVec v = cvec R σ J x v) :
    ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) =
      ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (chartS R σ J x a s Y) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n)
        ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 (M + 2)) := by
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨hK, hW, -⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hJ' := (GlobalTheory.T.hyperbolic_sum_nondegenerate_frame F E σ hCM M J hJ).1
  have : SigmaFinite (coordK R b lam) := inferInstance
  have hBK : BorelSpace (R ⊗[F] E) := ⟨rfl⟩
  have hBt := hBorel 1 n
  have hHaar := hW 1 n
  have step : ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) =
      ∫⁻ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, ∫⁻ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y)
        ∂(coordW R b lam n (M + 2)) ∂(coordW R b lam 1 (M + 2)) :=
    TupFubini.lintegral_tuple_succ (coordK R b lam) n (M + 2) g hg
  rw [step]
  refine lintegral_congr fun x => ?_
  by_cases hu : IsUnit (x 0 0)
  · obtain ⟨c, hcv⟩ := hc (x 0) hu
    have hact : Measurable (actW R σ (hypOne J) c :
        (Fin n → Fin (M + 2) → R ⊗[F] E) → Fin n → Fin (M + 2) → R ⊗[F] E) := by
      have := hBorel n (M + 2)
      have hcont := ((GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 2) (hypOne J) hJ' R).2.2.2.2.2 n).1
      exact (hcont.comp (Continuous.prodMk_right c)).measurable
    have hinv := GlobalTheory.T.unitary_action_preserves_haar_local F E σ hCM (M + 2) (hypOne J) hJ' R hR n (coordW R b lam n (M + 2)) (hW n (M + 2)) c
    have hf : Measurable fun Y : Fin n → Fin (M + 2) → R ⊗[F] E => g (Fin.cons (x 0) Y) :=
      hg.comp (TupFubini.measurable_cons_tail (x 0))
    have hψ := hf.comp hact
    calc ∫⁻ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y) ∂(coordW R b lam n (M + 2))
        = ∫⁻ Y, g (Fin.cons (x 0) Y) ∂((coordW R b lam n (M + 2)).map (actW R σ (hypOne J) c)) := by
          rw [hinv]
      _ = ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c Y)) ∂(coordW R b lam n (M + 2)) :=
          lintegral_map hf hact
      _ = ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c
            (fun j => vH (a 0 j) (s 0 j) (Y j)))) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n)
            ∂(coordW R b lam 1 n) :=
          lintegral_tuple_vH (coordK R b lam) n M _ hψ
      _ = _ := by
          refine lintegral_congr fun a => ?_
          have ht := lintegral_add_right_eq_self (μ := coordW R b lam 1 n)
            (fun s : Fin 1 → Fin n → R ⊗[F] E => ∫⁻ Y, g (Fin.cons (x 0) (actW R σ (hypOne J) c
              (fun j => vH (a 0 j) (s 0 j) (Y j)))) ∂(coordW R b lam n M))
            (fun _ j => - (tHalf R σ J (x 0) * a 0 j))
          rw [← ht]
          refine lintegral_congr fun s => lintegral_congr fun Y => ?_
          congr 1
          unfold chartS
          congr 1
          funext j
          simp only [actW, actTup, hcv, Pi.add_apply, sub_eq_add_neg]
  · have h0 : ∀ Y : Fin n → Fin (M + 2) → R ⊗[F] E, g (Fin.cons (x 0) Y) = 0 := fun Y => hg0 _ (by simpa using hu)
    have h1 : ∀ a s Y, g (chartS R σ J x a s Y) = 0 := fun a s Y => hg0 _ (by simpa [chartS] using hu)
    simp [h0, h1]

theorem chartS_lintegral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable g → (∀ X, ¬ IsUnit (X 0 0) → g X = 0) → ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) = ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (chartS R σ J x a s Y) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 (M + 2)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ R _ _ _ _ _ hR n d b lam hlam g hg hg0
  exact lintegral_chartS_of_unitary F E σ hCM M J hJ R hR n d b lam hlam g hg hg0
    fun x hx => GlobalTheory.CompanionTheory.WeilSiegel.HypUnit.cvec_unitary F E σ hCM M J hJ R x hx

end GlobalTheory.CompanionTheory.WeilSiegel.HypStage
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosureDimIffArithmeticVariety
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict
open GlobalTheory

namespace GlobalTheory.CompanionTheory.MPDict.DimClosure

private theorem exists_ringKrullDim_le_add_of_finiteType {R A : Type*} [CommRing R] [CommRing A]
    [IsNoetherianRing R] (f : R →+* A) (hf : f.FiniteType) :
    ∃ N : ℕ, ringKrullDim A ≤ ringKrullDim R + N := by
  letI := f.toAlgebra
  obtain ⟨k, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hf
  refine ⟨k, ?_⟩
  calc ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin k) R) :=
        ringKrullDim_le_of_surjective g.toRingHom hg
    _ = ringKrullDim R + k := by
        rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem exists_open_nhd_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} (y : MP ℤ m n) :
    ∃ U : (MP ℤ m n).Opens, y ∈ U ∧ ∃ N : ℕ, topologicalKrullDim (U : Set (MP ℤ m n)) ≤ N := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  obtain ⟨U, hU, hyU, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := (⊤ : (MP ℤ m n).Opens)) (x := y) (by simp)
  refine ⟨U, hyU, ?_⟩
  have hZ := AlgebraicGeometry.isAffineOpen_top (Spec (CommRingCat.of ℤ))
  have hft := AlgebraicGeometry.LocallyOfFiniteType.finiteType_of_affine_subset (mpStr ℤ m n) hZ hU
    (by simp)
  haveI : IsNoetherianRing ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) :=
    isNoetherianRing_of_ringEquiv ℤ (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm.commRingCatIsoToRingEquiv
  obtain ⟨N, hN⟩ := exists_ringKrullDim_le_add_of_finiteType _ hft
  have hZdim : ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of ℤ)).commRingCatIsoToRingEquiv]
    have h1 := Ring.krullDimLE_iff.mp (IsPrincipalIdealRing.krullDimLE_one ℤ)
    exact_mod_cast h1
  haveI := hU.isOpenImmersion_fromSpec
  have htop : topologicalKrullDim (U : Set (MP ℤ m n)) =
      ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U)) := by
    rw [GlobalTheory.topologicalKrullDim_eq_of_isEmbedding hU.fromSpec.isOpenEmbedding.isEmbedding hU.range_fromSpec]
    exact PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
  refine ⟨N + 1, ?_⟩
  rw [htop]
  calc ringKrullDim ((MP ℤ m n).presheaf.obj (Opposite.op U))
        ≤ ringKrullDim ((Spec (CommRingCat.of ℤ)).presheaf.obj (Opposite.op ⊤)) + N := hN
    _ ≤ 1 + N := by gcongr
    _ = ((N + 1 : ℕ) : WithBot ℕ∞) := by push_cast; exact add_comm _ _

private theorem exists_topologicalKrullDim_MP_le {m : ℕ} {n : Fin (m + 1) → ℕ} :
    ∃ d : ℕ, topologicalKrullDim (MP ℤ m n) ≤ d := by
  haveI : AlgebraicGeometry.IsProper (mpStr ℤ m n) := isProper_mpStr ℤ m n
  haveI : CompactSpace (MP ℤ m n) :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace (mpStr ℤ m n)
  choose U hyU N hN using fun y : MP ℤ m n => exists_open_nhd_topologicalKrullDim_MP_le y
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (U y : Set (MP ℤ m n)))
    (fun y => (U y).isOpen) (fun y _ => Set.mem_iUnion.mpr ⟨y, hyU y⟩)
  refine ⟨t.sup N, GlobalTheory.topologicalKrullDim_le_of_forall_exists_isOpen fun z => ?_⟩
  obtain ⟨y, hy, hzy⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ z))
  refine ⟨U y, (U y).isOpen, hzy, (hN y).trans ?_⟩
  exact_mod_cast Finset.le_sup (f := N) hy

theorem exists_dim_closure_eq {m : ℕ} {n : Fin (m + 1) → ℕ} (x : MP ℤ m n) :
    ∃ e : ℕ, topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (e : ℕ) := by
  obtain ⟨d, hd⟩ := exists_topologicalKrullDim_MP_le (m := m) (n := n)
  have hle : topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) ≤ d :=
    (topologicalKrullDim_subspace_le _ _).trans hd
  have hnn : 0 ≤ topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) := by
    haveI : Nonempty (IrreducibleCloseds (closure ({x} : Set (MP ℤ m n)))) :=
      ⟨⟨closure {(⟨x, subset_closure (Set.mem_singleton x)⟩ : closure ({x} : Set (MP ℤ m n)))},
        isIrreducible_singleton.closure, isClosed_closure⟩⟩
    unfold topologicalKrullDim
    exact Order.krullDim_nonneg
  generalize topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = D at hle hnn ⊢
  induction D using WithBot.recBotCoe with
  | bot => exact absurd hnn (not_le.mpr (WithBot.bot_lt_coe _))
  | coe a =>
    induction a using ENat.recTopCoe with
    | top =>
      exfalso
      have h5 : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((d : ℕ∞) : WithBot ℕ∞) := hle
      exact ENat.natCast_ne_top d (top_le_iff.mp (WithBot.coe_le_coe.mp h5))
    | coe e => exact ⟨e, rfl⟩

theorem dim_closure_iff_isArithVar : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) (d : ℕ),
    CharZero ((MP ℤ m n).residueField x) →
      (topologicalKrullDim (closure ({x} : Set (MP ℤ m n))) = (d : ℕ) ↔ Geo.IsArithVar (ptIdeal x) d) := by
  intro m n x d hc
  refine ⟨GlobalTheory.T.arithmetic_variety_point_dimension m n x d hc, fun h => ?_⟩
  obtain ⟨e, he⟩ := exists_dim_closure_eq x
  have h' := GlobalTheory.T.arithmetic_variety_point_dimension m n x e hc he
  have h1 := h.2.2.2
  have h2 := h'.2.2.2
  have hde : d = e := by
    have h3 := h1.symm.trans h2
    have h4 : d + Fintype.card (Fin (m + 1)) = e + Fintype.card (Fin (m + 1)) := by exact_mod_cast h3
    omega
  rw [he, hde]

end GlobalTheory.CompanionTheory.MPDict.DimClosure
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoeAbsNormUnitsPrimeIdealUnit
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 vecAt awayIntegral awayBox)
open GroundTheory.Automorphic.GJMatrix (cosetInd localTensor localFourierPi localMeasurePi)
open Ad3 Ad3.R
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap nonZeroDivisors Classical

namespace GlobalTheory.CompanionTheory.RSFT

def absNormUnits : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ →* ℝˣ :=
  Units.map (((Rat.castHom ℝ : ℚ →+* ℝ) : ℚ →* ℝ).comp
    (FractionalIdeal.absNorm : FractionalIdeal (𝓞 ℚ)⁰ ℚ →*₀ ℚ).toMonoidHom)

theorem coe_absNormUnits (I : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) :
    ((absNormUnits I : ℝˣ) : ℝ) =
      ((FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 ℚ)⁰ ℚ) : ℚ) : ℝ) := rfl

theorem coe_absNormUnits_primeIdealUnit (w : Pl) :
    ((absNormUnits (primeIdealUnit w) : ℝˣ) : ℝ) = (pOf w : ℝ) := by
  rw [coe_absNormUnits, coe_primeIdealUnit, FractionalIdeal.coeIdeal_absNorm]
  simp [pOf]

theorem idl_eq_prod (S : Finset Pl) (N : S → ℤ) :
    idl S N = ∏ v : S, primeIdealUnit v.1 ^ N v := by
  have hsub : Function.mulSupport (fun w : Pl =>
      primeIdealUnit w ^ (if h : w ∈ S then N ⟨w, h⟩ else 0)) ⊆ (S : Set Pl) := by
    intro w hw
    by_contra h
    apply hw
    have h' : w ∉ S := h
    simp [h']
  rw [idl, finprod_eq_prod_of_mulSupport_subset _ hsub, ← Finset.prod_coe_sort S]
  refine Finset.prod_congr rfl fun v _ => ?_
  simp

theorem absNorm_idl (S : Finset Pl) (N : S → ℤ) :
    ((FractionalIdeal.absNorm ((idl S N : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) :
      FractionalIdeal (𝓞 ℚ)⁰ ℚ) : ℚ) : ℝ) = ∏ v : S, (pOf v.1 : ℝ) ^ N v := by
  rw [← coe_absNormUnits, idl_eq_prod, map_prod, Units.coe_prod]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [map_zpow, Units.val_zpow_eq_zpow_val, coe_absNormUnits_primeIdealUnit]

theorem finiteAdeleMeasure_idl_toReal (S : Finset Pl) (N : S → ℤ) :
    (finiteAdeleMeasure ℚ (idealFiniteAdeles (idl S N))).toReal =
      ∏ v : S, (pOf v.1 : ℝ) ^ (-N v) := by
  rw [finiteAdeleMeasure_idealFiniteAdeles_toReal, Rat.numberField_discr]
  have hd : (NNReal.sqrt ‖(1 : ℤ)‖₊ : ℝ) = 1 := by simp
  rw [hd, inv_one, mul_one]
  have hn := absNorm_idl S N
  rw [show ((FractionalIdeal.absNorm ((idl S N : (FractionalIdeal (𝓞 ℚ)⁰ ℚ)ˣ) :
      FractionalIdeal (𝓞 ℚ)⁰ ℚ) : ℝ)) = _ from hn, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun v _ => (_root_.zpow_neg _ _).symm

end GlobalTheory.CompanionTheory.RSFT

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConcatenatedJacquetMultiplicityFactorizationStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.concatenated_jacquet_multiplicity_factorization : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {s N : ℕ} (c : Fin s → ℕ) (x : ∀ a, Fin (c a) → IrrGL k) (hpos : ∀ a, 0 < ∑ i, (x a i).1) (hcat : ∑ i, (concat c x i).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hfl : HasFiniteLength π), 1 ≤ jm (concat c x) hcat π → ∃ (σ : Fin s → IrrGL k) (hσ : ∑ a, (σ a).1 = N), (∀ a, (σ a).1 = ∑ i, (x a i).1) ∧ 1 ≤ jm σ hσ π := by
  first | exact @GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse | exact GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse | (intros; apply GlobalTheory.CompanionTheory.CoarseOcc.exists_one_le_jm_coarse <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CongruenceSubgroupCosetDecompositionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.congruence_subgroup_coset_decomposition : Ad3.R.C1 := by
  first | exact @GlobalTheory.CompanionTheory.RankinStepC.c1 | exact GlobalTheory.CompanionTheory.RankinStepC.c1 | (intros; apply GlobalTheory.CompanionTheory.RankinStepC.c1 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermConvolutionHeckeStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT PositivityTheory.Rg.BcN.F2
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_convolution_hecke : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (K' : Subgroup (GLw n w)), IsOpen (K' : Set (GLw n w)) → K' ≤ GlobalTheory.LFun.KGL w n → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∀ k' ∈ K', k * k' * k⁻¹ ∈ K') → ∀ X : Finset (GLw n w), (∀ x ∈ X, x ∈ GlobalTheory.LFun.KGL w n) → (∀ k ∈ GlobalTheory.LFun.KGL w n, ∃! x ∈ X, x⁻¹ * k ∈ K') → ∀ f₁ f₂ : GLw n w → ℂ, IsHk K' f₁ → IsHk K' f₂ → ∀ x ∈ X, ∀ z ∈ X, ∀ m, phi3 h w (gconv f₁ f₂) x z m = ((X.card : ℂ))⁻¹ * ∑ y ∈ X, mconv (phi3 h w f₁ x y) (phi3 h w f₂ y z) m := by
  first | exact @GlobalTheory.CompanionTheory.ConvMat.constant_term_convolution | exact GlobalTheory.CompanionTheory.ConvMat.constant_term_convolution | (intros; apply GlobalTheory.CompanionTheory.ConvMat.constant_term_convolution <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousThetaKernelComponentsStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_theta_kernel_components : ∀ {D : D7} {t ρ : ℕ} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) (b₀ : HermE D ρ) (b : hermA D t), Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (ip V z.2 z.2)) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => yv V b₀ z) ∧ Continuous (fun q : Mx D ρ t × (Mx D V.rank ρ × Mx D V.rank t) => ψ (trA (Matrix.trace (pr b₀ q.1 (yv V b₀ q.2))))) ∧ Continuous (fun z : Mx D V.rank ρ × Mx D V.rank t => pch ψ b.1 (qv V b₀ z)) ∧ (∀ T, ‖pch ψ b.1 T‖ = 1) ∧ ∀ u, ‖ψ u‖ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection | exact GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection | (intros; apply GlobalTheory.CompanionTheory.RCellCont.continuity_characters_projection <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceCompositionStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_composition : GlobalTheory.CompanionTheory.EGlue.ConvComp := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.convComp_proved | exact GlobalTheory.CompanionTheory.EGlue.convComp_proved | (intros; apply GlobalTheory.CompanionTheory.EGlue.convComp_proved <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceInfimumStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_infimum : GlobalTheory.CompanionTheory.EGlue.DiscInf → GlobalTheory.CompanionTheory.EGlue.TopInf → GlobalTheory.CompanionTheory.EGlue.ConvInf := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf | exact GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf | (intros; apply GlobalTheory.CompanionTheory.EGlue.ConvInfProof.convInf_of_discInf_topInf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConvergenceShiftStatement
section
open GlobalTheory.CompanionTheory.EGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convergence_shift : GlobalTheory.CompanionTheory.EGlue.ConvShift := by
  first | exact @GlobalTheory.CompanionTheory.EGlue.convShift_holds | exact GlobalTheory.CompanionTheory.EGlue.convShift_holds | (intros; apply GlobalTheory.CompanionTheory.EGlue.convShift_holds <;> assumption)
end

