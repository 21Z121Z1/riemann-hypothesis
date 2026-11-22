import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0516
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0501
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0517
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.StrictDominance.UnitaryExtremality.SatPowNonvan
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0485
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0503
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0513
import GroundTheory.GlobalFields.Adele.Compact

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFrameLevelTriangularStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_frame_level_triangular : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y → ∀ (s : Fin r) (m : GAd σ J), m ∈ unipRad σ J (pre X s) → ∀ (w : InfinitePlace F) (τ : EmbOver E w) (α β : FrameIx r), frameLev s α ≤ frameLev s β → (frameIdem (σ : E →+* E) J X Y α).map τ.1 * (archMat σ J τ (projArch σ J w m) - 1) * (frameIdem (σ : E →+* E) J X Y β).map τ.1 = 0 := by
  first | exact @GlobalTheory.CompanionTheory.RapidDecay.frameIdem_mul_unipRad_mul_frameIdem | exact GlobalTheory.CompanionTheory.RapidDecay.frameIdem_mul_unipRad_mul_frameIdem | (intros; apply GlobalTheory.CompanionTheory.RapidDecay.frameIdem_mul_unipRad_mul_frameIdem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentRadicalCompactFundamentalDomainStatement
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.RapidDecay
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal Topology

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_radical_compact_fundamental_domain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (k : ℕ) (Cc : Matrix (Fin n) (Fin k) E), GlobalTheory.UAut.IsIsoCols σ J Cc → ∀ W ∈ 𝓝 (1 : GFin σ J), ∃ Q : Set (GAd σ J), IsCompact Q ∧ ∀ m ∈ unipRad σ J Cc, ∃ γ ∈ ratPts σ J, ∃ q ∈ Q, q ∈ unipRad σ J Cc ∧ projFin σ J q ∈ W ∧ m = γ * q := by
  first | exact @GlobalTheory.CompanionTheory.StrongUnip.strong_approx_unipRad | exact GlobalTheory.CompanionTheory.StrongUnip.strong_approx_unipRad | (intros; apply GlobalTheory.CompanionTheory.StrongUnip.strong_approx_unipRad <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryFrobeniusReciprocityStatement
section
open GlobalTheory.PRep Formalism.UG GlobalTheory.LFun PositivityTheory.SphericalProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_frobenius_reciprocity : PositivityTheory.SphericalProduct.FrobU := by
  first | exact @GlobalTheory.CompanionTheory.FrobRec.frobU | exact GlobalTheory.CompanionTheory.FrobRec.frobU | (intros; apply GlobalTheory.CompanionTheory.FrobRec.frobU <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerCoefficientCongruencePullback
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

theorem measurePreserving_of_covol {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G)
    (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1) (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm)
    (hT : ∀ γ ∈ Γ, T γ ∈ Γ) (hT' : ∀ γ ∈ Γ, T.symm γ ∈ Γ) : MeasurePreserving T μ μ := by
  let e : G ≃ᵐ G := (Homeomorph.mk T.toEquiv hc hc').toMeasurableEquiv
  have he : ∀ x, e x = T x := fun _ => rfl
  haveI hH : (μ.map e).IsAddHaarMeasure := T.isAddHaarMeasure_map μ hc hc'
  have hs : μ.map e = Measure.addHaarScalarFactor (μ.map e) μ • μ := Measure.isAddLeftInvariant_eq_smul _ _
  have hpos := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) μ
  set c := Measure.addHaarScalarFactor (μ.map e) μ with hcdef
  have hq : Measure.QuasiMeasurePreserving e μ μ := by
    refine ⟨e.measurable, ?_⟩
    rw [hs]
    exact Measure.smul_absolutelyContinuous
  let σ : Γ → Γ := fun g => ⟨T.symm g, hT' g g.2⟩
  have hσ : Function.Bijective σ := by
    refine ⟨fun g g' h => ?_, fun g => ⟨⟨T g, hT g g.2⟩, ?_⟩⟩
    · apply Subtype.ext
      exact T.symm.injective (congrArg Subtype.val h)
    · apply Subtype.ext
      simp [σ]
  have hpre : IsAddFundamentalDomain Γ (e ⁻¹' 𝓕) μ := by
    refine hF.preimage_of_equiv hq hσ ?_
    intro g x
    show T (T.symm g + x) = g + T x
    simp
  have heq : μ (e ⁻¹' 𝓕) = μ 𝓕 := hpre.measure_eq hF
  have hmap : (μ.map e) 𝓕 = 1 := by rw [e.map_apply, heq, h1]
  have hc1 : c = 1 := by
    rw [hs] at hmap
    simp only [Measure.smul_apply, h1] at hmap
    have : ((c : ENNReal)) = 1 := by simpa [ENNReal.smul_def] using hmap
    exact_mod_cast this
  have : μ.map e = μ := by rw [hs, hc1, one_smul]
  exact ⟨e.measurable, this⟩

theorem integral_comp_of_covol {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (Γ : AddSubgroup G) [Countable Γ] (μ : Measure G) [μ.IsAddHaarMeasure] (𝓕 : Set G)
    (hF : IsAddFundamentalDomain Γ 𝓕 μ) (h1 : μ 𝓕 = 1) (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm)
    (hT : ∀ γ ∈ Γ, T γ ∈ Γ) (hT' : ∀ γ ∈ Γ, T.symm γ ∈ Γ) (g : G → ℂ) :
    ∫ x, g (T x) ∂μ = ∫ x, g x ∂μ :=
  (measurePreserving_of_covol Γ μ 𝓕 hF h1 T hc hc' hT hT').integral_comp
    (Homeomorph.mk T.toEquiv hc hc').toMeasurableEquiv.measurableEmbedding g

variable {D : D7}

def mulRightE {m r : ℕ} (A B : Mx D r r) (h1 : A * B = 1) (h2 : B * A = 1) : Mx D m r ≃+ Mx D m r where
  toFun y := y ⬝ A
  invFun y := y ⬝ B
  left_inv y := by
    show y ⬝ A ⬝ B = y
    rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  right_inv y := by
    show y ⬝ B ⬝ A = y
    rw [Matrix.mul_assoc, h2, Matrix.mul_one]
  map_add' x y := Matrix.add_mul x y A

theorem adj_cong_mem {r : ℕ} (A : Mx D r r) (b : hermA D r) : A ⬝ b.1 ⬝ adj A ∈ hermA D r := by
  have hb : adj b.1 = b.1 := b.2
  show adj (A ⬝ b.1 ⬝ adj A) = A ⬝ b.1 ⬝ adj A
  rw [adj_mul, adj_mul, adj_adj, hb, Matrix.mul_assoc]

theorem cong_cancel {r : ℕ} (A B : Mx D r r) (h2 : B * A = 1) (b : Mx D r r) :
    B ⬝ (A ⬝ b ⬝ adj A) ⬝ adj B = b := by
  have h3 : adj A ⬝ adj B = 1 := by rw [← adj_mul, h2, adj_one]
  calc B ⬝ (A ⬝ b ⬝ adj A) ⬝ adj B = (B * A) * b * (adj A * adj B) := by
        simp only [Matrix.mul_assoc]
    _ = b := by
        rw [h2]
        erw [h3]
        simp

def congA {r : ℕ} (A B : Mx D r r) (h1 : A * B = 1) (h2 : B * A = 1) : hermA D r ≃+ hermA D r where
  toFun b := ⟨A ⬝ b.1 ⬝ adj A, adj_cong_mem A b⟩
  invFun b := ⟨B ⬝ b.1 ⬝ adj B, adj_cong_mem B b⟩
  left_inv b := Subtype.ext (cong_cancel A B h2 b.1)
  right_inv b := Subtype.ext (cong_cancel B A h1 b.1)
  map_add' x y := Subtype.ext (by
    show A ⬝ (x.1 + y.1) ⬝ adj A = A ⬝ x.1 ⬝ adj A + A ⬝ y.1 ⬝ adj A
    rw [Matrix.mul_add, Matrix.add_mul])

theorem rat_mul_inv {r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    rat a * rat a⁻¹ = (1 : Mx D r r) := by
  rw [← rat_mul, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 ha), rat_one]

theorem rat_inv_mul {r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    rat a⁻¹ * rat a = (1 : Mx D r r) := by
  rw [← rat_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 ha), rat_one]

theorem integral_mulRight {m r : ℕ} {μ : Measure (Mx D m r)} {𝓕 : Set (Mx D m r)}
    (hμ : IsCovolOne (ratMx D m r) μ 𝓕) (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0)
    (g : Mx D m r → ℂ) : ∫ y, g (y ⬝ rat a) ∂μ = ∫ y, g y ∂μ := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D m r
  haveI : BorelSpace (Mx D m r) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI i6 : DiscreteTopology (ratMx D m r) := i5
  haveI i7 : SecondCountableTopology (ratMx D m r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D m r) := TopologicalSpace.separableSpace_iff_countable.1
    (TopologicalSpace.SecondCountableTopology.to_separableSpace)
  obtain ⟨hH, hF, h1⟩ := hμ
  exact integral_comp_of_covol (ratMx D m r) μ 𝓕 hF h1
    (mulRightE (rat a) (rat a⁻¹) (rat_mul_inv a ha) (rat_inv_mul a ha))
    (continuous_id.matrix_mul continuous_const) (continuous_id.matrix_mul continuous_const)
    (by rintro _ ⟨γ, rfl⟩; exact ⟨γ * a, rat_mul γ a⟩)
    (by rintro _ ⟨γ, rfl⟩; exact ⟨γ * a⁻¹, rat_mul γ a⁻¹⟩) g

theorem integral_congA {r : ℕ} {lam : Measure (hermA D r)} {𝓖 : Set (hermA D r)}
    (hl : IsCovolOneH lam 𝓖) (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0)
    (g : hermA D r → ℂ) :
    ∫ b, g (congA (rat a) (rat a⁻¹) (rat_mul_inv a ha) (rat_inv_mul a ha) b) ∂lam = ∫ b, g b ∂lam := by
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := GlobalTheory.TowerRestrict.lattice_Mx D r r
  haveI : BorelSpace (Mx D r r) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE D) := (Formalism.IndefR.Eqv.ae_facts D).1
  haveI i6 : DiscreteTopology (ratMx D r r) := i5
  haveI i7 : SecondCountableTopology (ratMx D r r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : Countable (ratMx D r r) := TopologicalSpace.separableSpace_iff_countable.1
    (TopologicalSpace.SecondCountableTopology.to_separableSpace)
  haveI i8 : SecondCountableTopology (hermA D r) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI i9 : BorelSpace (hermA D r) := Subtype.borelSpace _
  have hcl : IsClosed ((hermA D r : AddSubgroup (Mx D r r)) : Set (Mx D r r)) :=
    isClosed_eq continuous_adj continuous_id
  haveI : LocallyCompactSpace (hermA D r) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : Countable (ratHerm D r) := by
    let f : ratHerm D r → ratMx D r r := fun x => ⟨x.1.1, x.2⟩
    have hf : Function.Injective f := fun x y h =>
      Subtype.ext (Subtype.ext (congrArg (fun z : ratMx D r r => z.1) h))
    exact hf.countable
  obtain ⟨hH, hF, h1⟩ := hl
  have hcont : ∀ A : Mx D r r, Continuous (fun b : hermA D r => A ⬝ b.1 ⬝ adj A) := fun A =>
    (continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const
  have hrat : ∀ (c : Matrix (Fin r) (Fin r) D.host.E) (γ : hermA D r), γ ∈ ratHerm D r →
      rat c ⬝ γ.1 ⬝ adj (rat c) ∈ ratMx D r r := by
    rintro c ⟨_, _⟩ ⟨γ, rfl⟩
    refine ⟨c * γ * cᴴ, ?_⟩
    show rat (c * γ * cᴴ) = _
    rw [rat_mul, rat_mul, rat_conjTranspose]
    rfl
  exact integral_comp_of_covol (ratHerm D r) lam 𝓖 hF h1
    (congA (rat a) (rat a⁻¹) (rat_mul_inv a ha) (rat_inv_mul a ha))
    ((hcont _).subtype_mk _) ((hcont _).subtype_mk _)
    (fun γ hγ => hrat a γ hγ) (fun γ hγ => hrat a⁻¹ γ hγ) g

theorem inner_mul_right (V : HSp D) {r : ℕ} (y : Mx D V.rank r) (A : Mx D r r) :
    GlobalTheory.StdUnn.inner V (y ⬝ A) (y ⬝ A) = adj A ⬝ GlobalTheory.StdUnn.inner V y y ⬝ A := by
  simp only [GlobalTheory.StdUnn.inner, adj_mul, Matrix.mul_assoc]

theorem trace_cong_left {r : ℕ} (P A b Q : Mx D r r) :
    Matrix.trace (P ⬝ (A ⬝ b ⬝ Q)) = Matrix.trace (Q ⬝ P ⬝ A ⬝ b) := by
  calc Matrix.trace (P ⬝ (A ⬝ b ⬝ Q)) = Matrix.trace ((P ⬝ A ⬝ b) ⬝ Q) := by
        simp only [Matrix.mul_assoc]
    _ = Matrix.trace (Q ⬝ (P ⬝ A ⬝ b)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (Q ⬝ P ⬝ A ⬝ b) := by simp only [Matrix.mul_assoc]

theorem trace_cong_inner {r : ℕ} (A B b I : Mx D r r) (h1 : A * B = 1) (h2 : B * A = 1) :
    Matrix.trace ((B ⬝ b ⬝ adj B) ⬝ (adj A ⬝ I ⬝ A)) = Matrix.trace (b ⬝ I) := by
  have h3 : adj B ⬝ adj A = 1 := by rw [← adj_mul, h1, adj_one]
  calc Matrix.trace ((B ⬝ b ⬝ adj B) ⬝ (adj A ⬝ I ⬝ A))
      = Matrix.trace (B ⬝ (b ⬝ ((adj B ⬝ adj A) ⬝ (I ⬝ A)))) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (B ⬝ (b ⬝ (I ⬝ A))) := by
        rw [h3]
        simp
    _ = Matrix.trace ((b ⬝ (I ⬝ A)) ⬝ B) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (b ⬝ I ⬝ (A ⬝ B)) := by simp only [Matrix.mul_assoc]
    _ = Matrix.trace (b ⬝ I) := by
        rw [h1]
        simp

theorem rat_congrH {r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (β : HermE D r) :
    (congrH a β).1.map (incA D) = adj (rat a) ⬝ β.1.map (incA D) ⬝ rat a := by
  have h : (congrH a β).1 = aᴴ * β.1 * a := rfl
  rw [h]
  show rat (aᴴ * β.1 * a) = _
  rw [rat_mul, rat_mul, rat_conjTranspose]
  rfl

theorem W_congr : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (φ : Mx D V.rank r → ℂ) (β : HermE D r) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 → (∃ 𝓕, IsCovolOne (ratMx D V.rank r) μ 𝓕) → (∃ 𝓖, IsCovolOneH lam 𝓖) → W ψ V μ lam (pull a φ) β = W ψ V μ lam φ (GlobalTheory.CompanionTheory.WeilSiegel.Deg.congrH a β) := by
  intro D r V ψ μ lam φ β a ha ⟨𝓕, hμ⟩ ⟨𝓖, hl⟩
  set S := congA (rat a) (rat a⁻¹) (rat_mul_inv a ha) (rat_inv_mul a ha) with hS
  have hJ : ∀ b, Jt ψ V μ (pull a φ) b = Jt ψ V μ φ (S.symm b) := by
    intro b
    unfold Jt
    refine Eq.trans ?_ (integral_mulRight hμ a ha _)
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show φ (y ⬝ rat a) * _ = φ (y ⬝ rat a) * _
    congr 3
    have : (S.symm b).1 = rat a⁻¹ ⬝ b.1 ⬝ adj (rat a⁻¹) := rfl
    rw [this, inner_mul_right, trace_cong_inner _ _ _ _ (rat_mul_inv a ha) (rat_inv_mul a ha)]
  unfold W
  simp only [hJ]
  refine (integral_congA hl a ha _).symm.trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
  simp only [← hS, AddEquiv.symm_apply_apply]
  congr 4
  have : (S b).1 = rat a ⬝ b.1 ⬝ adj (rat a) := rfl
  rw [this, trace_cong_left, rat_congrH]

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSubquotientEquivStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CompanionTheory.BZNuPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_subquotient_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (d : Fin 2 → ℕ) (Y : Type) [AddCommGroup Y] [Module ℂ Y]
    (J : Representation ℂ (Levi k fun a => Fin (d a)) Y) (T T' : Subrepresentation J) (X : Fin 2 → Type)
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (Fin (d a)) k) (X a)),
    T' ≤ T → (subQuot T T').Equiv (piTensor ρ) →
    ⨆ f : (ρ 0).IntertwiningMap (subQuot (whitImg ψ d J T) (whitImg ψ d J T')), LinearMap.range f.toLinearMap = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main | exact GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main | (intros; apply GlobalTheory.CompanionTheory.BZNuPair.WhitCover.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZeroMemBoxF
section
noncomputable section

open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.RedCov.Simple

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def boxF (ρ : ℝ) : Set (AF F) :=
  {a | (∀ w : InfinitePlace F, ‖a.1 w‖ ≤ ρ) ∧ a.2 ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 F) F}

def boxE (ρ : ℝ) : Set (AF F ⊗[F] E) :=
  {x | ∀ k, (Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).repr x k ∈ boxF F ρ}

theorem zero_mem_boxF {ρ : ℝ} (hρ : 0 ≤ ρ) : (0 : AF F) ∈ boxF F ρ :=
  ⟨fun w => by rw [show (0 : AF F).1 w = 0 from rfl, norm_zero]; exact hρ, zero_mem _⟩

theorem zero_mem_boxE {ρ : ℝ} (hρ : 0 ≤ ρ) : (0 : AF F ⊗[F] E) ∈ boxE F E ρ := fun k => by
  simpa using zero_mem_boxF F hρ

end GlobalTheory.CompanionTheory.RedCov.Simple

end
end

