import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0011
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0200
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFinEmb
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0199
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolEqOfAedisjoint
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0013
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Formalism.RealPlaceAnalysis.FinalF
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0020
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0202
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LiftedFlagLatticeChainSpans
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LoopC.LatChain

section
variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

theorem mem_orth {U : Submodule E S.V} {v : S.V} : v ∈ orth S U ↔ ∀ x ∈ U, S.hT x v = 0 := by
  simp [orth, Submodule.mem_iInf]

theorem exists_mul_mem {Λ : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsLattice E Λ) (v : S.V) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ d • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set S.V) := by rw [hΛ.span_eq_top]; trivial
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors (𝓞 E)) E _ v hv
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.ne_zero t.2, ht⟩

theorem le_spanE {Λ M : Submodule (𝓞 E) S.V} (hΛ : Submodule.IsLattice E Λ) {U : Submodule E S.V}
    (h : Λ ⊓ toO S U ≤ M) : U ≤ spanE S M := by
  intro v hv
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem hΛ v
  have h0 : d • v ∈ toO S U := (toO S U).smul_mem d hv
  have h1 : d • v ∈ M := h ⟨hd, h0⟩
  have h2 := Submodule.smul_mem _ (algebraMap (𝓞 E) E d)⁻¹ (Submodule.subset_span (R := E) h1)
  rwa [← algebraMap_smul E d v, inv_smul_smul₀
    ((map_ne_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).mpr hd0)] at h2

theorem spanE_le {M : Submodule (𝓞 E) S.V} {U : Submodule E S.V} (h : M ≤ toO S U) : spanE S M ≤ U :=
  Submodule.span_le.2 h

variable {r : ℕ} {T T' : E} {Λ : Submodule (𝓞 E) S.V}

theorem mem_L0sub {F : LFlag S r T} {x : S.V} (hx : x ∈ Lrep Λ F) (hz : S.hT F.fl.z x = 0) :
    x ∈ L0sub Λ F :=
  ⟨⟨Submodule.mem_sup_left hx, hx.2⟩, hz⟩

theorem thp_le_la (g : ℕ) {F : LFlag S r T} {F' : LFlag S r T'} (hΛ : Submodule.IsLattice E Λ)
    (hF : IsLift Λ F) (hF' : IsLift Λ F') : Thp Λ F F' ≤ La Λ g F F' := by
  intro x hx
  have hperp : ∀ y ∈ UUE Λ F F', S.hT y x = 0 := mem_orth.1 hx.2
  have hX : Xsp F ≤ UUE Λ F F' :=
    le_spanE hΛ (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have hX' : Xsp F' ≤ UUE Λ F F' := le_spanE hΛ (le_sup_of_le_left le_sup_right)
  have hz : F.fl.z ∈ UUE Λ F F' := by
    rw [← hF.2]
    exact Submodule.subset_span (Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))))
  have hz' : F'.fl.z ∈ UUE Λ F F' := by
    rw [← hF'.2]
    exact Submodule.subset_span (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  have h1 : x ∈ Lrep Λ F := ⟨hx.1, mem_orth.2 fun y hy => hperp y (hX hy)⟩
  have h2 : x ∈ Lrep Λ F' := ⟨hx.1, mem_orth.2 fun y hy => hperp y (hX' hy)⟩
  refine Submodule.subset_span ⟨hx.2, mem_L0sub h1 (hperp _ hz), mem_L0sub h2 (hperp _ hz'),
    x, h1, ?_, x, h2, ?_, ?_⟩ <;> rw [sub_self] <;> exact Submodule.zero_mem _

end

theorem lattice_chain_spans : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E) (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'), Submodule.IsLattice E Λ → IsLift Λ F → IsLift Λ F' → Thp Λ F F' ≤ La Λ g F F' ∧ La Λ g F F' ≤ L0sub Λ F ⊓ toO S (Hp Λ F F') ∧ spanE S (Thp Λ F F') = Hp Λ F F' ∧ ∀ (F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V), spanE S (Mlat Λ F F' F'' β g) = Th Λ F F' F'' β := by
  intro E _ _ _ S r T T' Λ g F F' hΛ hF hF'
  have h1 := thp_le_la g hΛ hF hF'
  refine ⟨h1, Submodule.span_le.2 fun x hx => ⟨hx.2.1, hx.1⟩,
    le_antisymm (spanE_le inf_le_right) (le_spanE hΛ le_rfl), fun F'' β =>
    le_antisymm (spanE_le inf_le_right) (le_spanE hΛ fun x hx => ⟨h1 ⟨hx.1, ?_⟩, hx.2⟩)⟩
  obtain ⟨p, hp, e⟩ := hx.2
  have : p.1 = x := e
  rw [← this]
  exact hp.1.1.1

end GlobalTheory.LoopC.LatChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralTsumCosetsFundamentalDomainEqCovolStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean GlobalTheory.StabUnfold
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_tsum_cosets_fundamentalDomain_eq_covol : ∀ (G : Type) [Group G] [MeasurableSpace G] [MeasurableMul G] (Γ S : Subgroup G) (μ : Measure G) (fund : Set G) (Φ : G → ENNReal) (ι : Type) [Countable ι] (r : ι → G), (Γ : Set G).Countable → S ≤ Γ → (∀ γ ∈ Γ, μ.map (fun y => γ * y) = μ) → MeasurableSet fund → (∀ y, ∃ γ ∈ Γ, γ * y ∈ fund) → (∀ γ ∈ Γ, γ ≠ 1 → μ ((fun y => γ * y) '' fund ∩ fund) = 0) → Measurable Φ → (∀ γ ∈ S, ∀ g, Φ (γ * g) = Φ g) → (∀ i, r i ∈ Γ) → (∀ γ ∈ Γ, ∃! i, γ * (r i)⁻¹ ∈ S) → ∫⁻ g in fund, ∑' i, Φ (r i * g) ∂μ = covol (S : Set G) (μ.withDensity Φ) Set.univ := by
  first | exact @GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol | exact GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol | (intros; apply GlobalTheory.StabUnfold.lintegral_tsum_cosets_eq_covol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapInfiniteGLHaarMeasureMulLeftStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_infiniteGLHaarMeasure_mul_left : ∀ (E : Type) [Field E] [NumberField E] (j : ℕ) (γ : MatInf E j), 0 < detNorm E j γ → (haarGL E j).map (fun g => γ * g) = haarGL E j := by
  first | exact @GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq | exact GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq | (intros; apply GlobalTheory.OrbitTerm.map_haarGL_mul_left_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixConclIffOfIsDS
section
open MeasureTheory Formalism.MainNotions.S Formalism.MainNotions.PlaceDegreeData GlobalTheory.IndefiniteRowSideFullHecke.UnitarySchurOrthogonality
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.SchurProjCompare

section Abstract

variable {G : Type} [Group G]
variable {Hs : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs]
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsCyclic (σ : G → (Hs →L[ℂ] Hs)) (w : Hs) : Prop :=
  Dense (Submodule.span ℂ (Set.range fun g => σ g w) : Set Hs)

omit [Group G] in

theorem IsCyclic.ext {σ : G → (Hs →L[ℂ] Hs)} {w : Hs} (h : IsCyclic σ w) {E : Type}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {A B : Hs →L[ℂ] E}
    (hAB : ∀ g, A (σ g w) = B (σ g w)) : A = B :=
  ContinuousLinearMap.ext_on h (by rintro _ ⟨g, rfl⟩; exact hAB g)

def IsometricProps [CompleteSpace H] (σ : G → (Hs →L[ℂ] Hs)) (w : Hs) (π : G → (H →L[ℂ] H))
    (P : H →L[ℂ] H) : Prop :=
  IsStarProjection P ∧
    (∀ x : G, P ∘L π x ∘L P = ⟪w, σ x w⟫_ℂ • P) ∧
    (∀ v ∈ LinearMap.range (P : H →ₗ[ℂ] H), ‖v‖ = 1 →
      (∀ g : G, ⟪v, π g v⟫_ℂ = ⟪w, σ g w⟫_ℂ) ∧
      ∃ io : Hs →ₗᵢ[ℂ] H, io w = v ∧ ∀ (g : G) (u : Hs), io (σ g u) = π g (io u)) ∧
    ((LinearMap.range (P : H →ₗ[ℂ] H) : Submodule ℂ H) : Set H) =
      {v | ∃ io : Hs →L[ℂ] H, (∀ g : G, io ∘L σ g = π g ∘L io) ∧ v = io w}

def IsometricConcl [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) (σ : G → (Hs →L[ℂ] Hs))
    (d : ℝ) (w : Hs) : Prop :=
  (∀ g : G, star (testFn σ d w g⁻¹) = testFn σ d w g) ∧
    (∀ x y : G, ∫ g, testFn σ d w g * testFn σ d w (x⁻¹ * g⁻¹ * y) ∂μ = ⟪w, σ x w⟫_ℂ * testFn σ d w y) ∧
    ∀ (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]
      (π : G → (Hp →L[ℂ] Hp)), IsUnitaryRep π →
      (∃ P, IsIntegratedOp μ π (testFn σ d w) P) ∧
        ∀ P, IsIntegratedOp μ π (testFn σ d w) P → IsometricProps σ w π P

def homOfRep [TopologicalSpace G] (π : G → (H →L[ℂ] H)) (hπ : IsUnitaryRep π) : G →* (H →L[ℂ] H) where
  toFun := π
  map_one' := hπ.1
  map_mul' := hπ.2.1

def NormHyp [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) (σ : G →* (Hs →L[ℂ] Hs)) (d : ℝ)
    (w : Hs) : Prop :=
  (∀ g x, ‖σ g x‖ = ‖x‖) ∧ (∀ x, Continuous fun g => σ g x) ∧ 0 < d ∧
    (∀ x y : Hs, Integrable (fun g => ‖⟪y, σ g x⟫_ℂ‖ ^ 2) μ ∧
      ∫ g, ‖⟪y, σ g x⟫_ℂ‖ ^ 2 ∂μ = ‖x‖ ^ 2 * ‖y‖ ^ 2 / d) ∧
    ‖w‖ = 1 ∧ Integrable (fun g => ⟪w, σ g w⟫_ℂ) μ

def HomConcl [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) (σ : G →* (Hs →L[ℂ] Hs)) (d : ℝ)
    (w : Hs) : Prop :=
  (∀ g : G, star (phA d σ w g⁻¹) = phA d σ w g) ∧
    (∀ x y : G, ∫ g, phA d σ w g * phA d σ w (x⁻¹ * g⁻¹ * y) ∂μ = ⟪w, σ x w⟫_ℂ * phA d σ w y) ∧
    ∀ (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]
      (π : G →* (Hp →L[ℂ] Hp)), (∀ g x, ‖π g x‖ = ‖x‖) → (∀ x, Continuous fun g => π g x) →
      (∃ P : Hp →L[ℂ] Hp, IsOpIntA μ π (phA d σ w) P) ∧
      ∀ P : Hp →L[ℂ] Hp, IsOpIntA μ π (phA d σ w) P → IsometricProps σ w π P

def FirstAt [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) : Prop :=
  ∀ (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : G →* (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs), NormHyp μ σ d w → HomConcl μ σ d w

def SecondAt [TopologicalSpace G] [MeasurableSpace G] (μ : Measure G) : Prop :=
  ∀ (Hs : Type) [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [CompleteSpace Hs]
    (σ : G → (Hs →L[ℂ] Hs)) (d : ℝ) (w : Hs),
    IsUnitaryRep σ → IsTopIrred σ → SchurOrthogonality μ σ d → ‖w‖ = 1 →
    Integrable (testFn σ d w) μ → SchurRelations μ σ d w ∧ ProjectorStatement μ σ d w

end Abstract

section Unitary

open Matrix Formalism.REAL

variable {n : ℕ} {ε : Fin n → Bool}
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def toGroup (M : UJset ε) : UJ ε :=
  have h : Jm ε * M.1ᴴ * Jm ε * M.1 = 1 := by
    have h0 : M.1ᴴ * Jm ε * M.1 = Jm ε := M.2
    rw [Matrix.mul_assoc (Jm ε), Matrix.mul_assoc (Jm ε), h0, Jm_mul_self]
  ⟨⟨M.1, Jm ε * M.1ᴴ * Jm ε, mul_eq_one_comm.1 h, h⟩, M.2⟩

theorem continuous_toGroup : Continuous (toGroup (ε := ε)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩) _
  exact (continuous_const.matrix_mul continuous_subtype_val.matrix_conjTranspose).matrix_mul
    continuous_const

theorem toGroup_umat (g : UJ ε) : toGroup ⟨umat g, g.2⟩ = g := Subtype.ext (Units.ext rfl)

open Classical in

def onMatrices (π : UJ ε → (H →L[ℂ] H)) (M : Matrix (Fin n) (Fin n) ℂ) : H →L[ℂ] H :=
  if h : M ∈ UJset ε then π (toGroup ⟨M, h⟩) else 0

theorem onMatrices_umat (π : UJ ε → (H →L[ℂ] H)) (g : UJ ε) : onMatrices π (umat g) = π g := by
  have h : umat g ∈ UJset ε := g.2
  rw [onMatrices, dif_pos h, toGroup_umat]

theorem isURepOn_iff (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) :
    IsURepOn (UJset ε) π ↔ IsUnitaryRep fun g : UJ ε => π (umat g) := by
  constructor
  · intro h
    have hc : Continuous fun g : UJ ε => umat g := Units.continuous_val.comp continuous_subtype_val
    exact ⟨h.1.1, fun a b => h.1.2 (umat a) a.2 (umat b) b.2, fun g => h.2.1 (umat g) g.2,
      fun v => (h.2.2 v).comp_continuous hc fun g => g.2⟩
  · intro h
    refine ⟨⟨h.1, fun a ha b hb => h.2.1 (toGroup ⟨a, ha⟩) (toGroup ⟨b, hb⟩)⟩,
      fun g hg => h.2.2.1 (toGroup ⟨g, hg⟩), fun v => ?_⟩
    rw [continuousOn_iff_continuous_domRestrict]
    exact (h.2.2.2 v).comp continuous_toGroup

def MatrixConcl (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  Integrable (phLoc ε σ w) (muG ε) ∧
    (∀ g : UJ ε, star (phLoc ε σ w g⁻¹) = phLoc ε σ w g) ∧
    (∀ x y : UJ ε, ∫ g, phLoc ε σ w g * phLoc ε σ w (x⁻¹ * g⁻¹ * y) ∂(muG ε) =
      coefOn σ w w x * phLoc ε σ w y) ∧
    ∀ (Hp : Type) [NormedAddCommGroup Hp] [InnerProductSpace ℂ Hp] [CompleteSpace Hp]
      (π : Matrix (Fin n) (Fin n) ℂ → (Hp →L[ℂ] Hp)), IsURepOn (UJset ε) π →
      (∃ P : Hp →L[ℂ] Hp, IsOpInt ε π (phLoc ε σ w) P) ∧
      ∀ P : Hp →L[ℂ] Hp, IsOpInt ε π (phLoc ε σ w) P →
        IsometricProps (fun g : UJ ε => σ (umat g)) w (fun g : UJ ε => π (umat g)) P

end Unitary

def FirstLocallyCompact : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant], FirstAt μ

def SecondAllGroups : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant],
    SecondAt μ

end GlobalTheory.SchurProjCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeanLEqOfRealMeanCRe
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem meanL_eq_ofReal_meanC_re (G : Type) [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G)
    (ι : Type) [Countable ι] (f : ι → G → ℝ) (hm : ∀ i, Measurable (f i))
    (h0 : ∀ i h, 0 ≤ f i h) (hF : μ 𝓕 < ⊤)
    (hI : ∫⁻ h in 𝓕, ∑' i, ‖((f i h : ℝ) : ℂ)‖ₑ ∂μ < ⊤) :
    meanL μ 𝓕 (fun h => ∑' i, ENNReal.ofReal (f i h)) =
      ENNReal.ofReal (meanC μ 𝓕 (fun h => ∑' i, ((f i h : ℝ) : ℂ))).re := by
  set S : G → ℝ≥0∞ := fun h => ∑' i, ENNReal.ofReal (f i h) with hSdef
  have hnorm : ∀ i h, ‖((f i h : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (f i h) := by
    intro i h
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (h0 i h)]
  have hS : ∫⁻ h in 𝓕, S h ∂μ < ⊤ := by
    simpa only [hnorm] using hI
  have hSm : Measurable S := Measurable.ennreal_tsum (fun i => (hm i).ennreal_ofReal)
  have hae : ∀ᵐ h ∂(μ.restrict 𝓕), S h < ⊤ := ae_lt_top hSm hS.ne
  have hint : ∫ h in 𝓕, (∑' i, ((f i h : ℝ) : ℂ)) ∂μ = (((∫⁻ h in 𝓕, S h ∂μ).toReal : ℝ) : ℂ) := by
    have hcongr : (fun h => ∑' i, ((f i h : ℝ) : ℂ)) =ᵐ[μ.restrict 𝓕]
        fun h => (((S h).toReal : ℝ) : ℂ) := by
      filter_upwards [hae] with h hh
      have hsum : Summable (fun i => f i h) := by
        convert ENNReal.summable_toReal hh.ne using 1
        funext i
        exact (ENNReal.toReal_ofReal (h0 i h)).symm
      show _ = (((∑' i, ENNReal.ofReal (f i h)).toReal : ℝ) : ℂ)
      rw [← Complex.ofReal_tsum, ← ENNReal.ofReal_tsum_of_nonneg (fun i => h0 i h) hsum,
        ENNReal.toReal_ofReal (tsum_nonneg (fun i => h0 i h))]
    rw [integral_congr_ae hcongr, integral_complex_ofReal, integral_toReal hSm.aemeasurable hae]
  unfold meanL meanC
  rw [hint, Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
  by_cases hz : μ 𝓕 = 0
  · have hr : μ.restrict 𝓕 = 0 := Measure.restrict_eq_zero.mpr hz
    simp [hr, hz]
  · rw [ENNReal.ofReal_mul (inv_nonneg.2 ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hS.ne,
      ← ENNReal.toReal_inv, ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hz)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureCommonStabilizerCoordsBoxImageStatement
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_commonStabilizerCoords_box_image : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ), Monotone β → (∀ a b : Fin r, j ≤ b.val → (β a = β b ↔ j ≤ a.val)) → MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) → ∀ (F₁ : UTin β → Set (ι → ℂ)) (F₂ : {a : Fin r // j ≤ a.val} → Set (ι → Fin (k + 1) → ℂ)) (F₃ : {p : UT r // j ≤ p.1.1.val} → Set (ι → ℂ)) (F₄ : {a : Fin r // j ≤ a.val} → Set (ι → ℝ)), (∀ i, MeasurableSet (F₁ i)) → (∀ i, MeasurableSet (F₂ i)) → (∀ i, MeasurableSet (F₃ i)) → (∀ i, MeasurableSet (F₄ i)) → ∀ Ω : Set (ι → Mt k r), Ω = (fun (p : Crd ι k r j β) (v : ι) => (Matrix.of.symm (CC p v) : Mt k r)) '' (Set.pi Set.univ F₁ ×ˢ Set.pi Set.univ F₂ ×ˢ (Set.pi Set.univ F₃ ×ˢ Set.pi Set.univ F₄)) → MeasurableSet Ω ∧ Measure.pi (fun _ : ι => lebR0 k r j β) Ω = (∏ i, volume (F₁ i)) * ((∏ i, volume (F₂ i)) * ((∏ i, volume (F₃ i)) * ∏ i, volume (F₄ i))) := by
  first | exact @GlobalTheory.DegVol.RefMeas.box_meas | exact GlobalTheory.DegVol.RefMeas.box_meas | (intros; apply GlobalTheory.DegVol.RefMeas.box_meas <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasureInterTranslateEqZeroOfCovolumeStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measure_inter_translate_eq_zero_of_covolume : ∀ (X : Type) [Mul X] [MeasurableSpace X] [MeasurableSpace.CountablySeparated X] (S : Set X) (μ : Measure X) [SigmaFinite μ] (U D : Set X), S.Countable → (∀ γ ∈ S, Measurable fun x => γ * x) → (∀ γ ∈ S, μ.map (fun x => γ * x) = μ) → (∀ γ ∈ S, ∀ δ ∈ S, ∃ ε ∈ S, ∀ x, ε * x = γ * (δ * x)) → (∀ γ ∈ S, ∃ δ ∈ S, (∀ x, δ * (γ * x) = x) ∧ ∀ x, γ * (δ * x) = x) → MeasurableSet U → (∀ γ ∈ S, ∀ x ∈ U, γ * x ∈ U) → MeasurableSet D → D ⊆ U → (∀ A, MeasurableSet A → A ⊆ U → (∀ γ ∈ S, ∀ x ∈ A, γ * x ∈ A) → covol S μ A = μ (A ∩ D)) → ∀ γ ∈ S, (∀ x ∈ U, γ * x ≠ x) → μ {x | x ∈ D ∧ γ * x ∈ D} = 0 := by
  first | exact @GlobalTheory.StrictDomain.measure_inter_translate_eq_zero | exact GlobalTheory.StrictDomain.measure_inter_translate_eq_zero | (intros; apply GlobalTheory.StrictDomain.measure_inter_translate_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingCommonStabilizerCoordinatesAtPlStatement
section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_commonStabilizerCoordinatesAtPlace : ∀ (ι : Type) [Fintype ι] (k r j : ℕ) (β : Fin r → ℕ), MeasurePreserving (atP : Crd ι k r j β → ι → (UTin β → ℂ) × PTop k r j) volume (Measure.pi fun _ : ι => (volume : Measure ((UTin β → ℂ) × PTop k r j))) := by
  first | exact @GlobalTheory.DegVol.RefCov.atP_measurePreserving | exact GlobalTheory.DegVol.RefCov.atP_measurePreserving | (intros; apply GlobalTheory.DegVol.RefCov.atP_measurePreserving <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingRearrangePiProdMeasuresStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurePreserving_rearrange_pi_prod_measures : ∀ (V V' V'' : Type) [Fintype V] [Fintype V'] [Fintype V''] (β : V ≃ V') (σ : V ≃ V'') (a : ℕ) (X : Fin a → Type) [∀ i, MeasurableSpace (X i)] (Y : V'' → Type) [∀ w, MeasurableSpace (Y w)] (m : ∀ i, Measure (X i)) [∀ i, SigmaFinite (m i)] (ν : ∀ w, Measure (Y w)) [∀ w, SigmaFinite (ν w)] (b : Fin a → ℝ) (c : V'' → ℝ), (∀ i, 0 ≤ b i) → (∀ w, 0 ≤ c w) → MeasurePreserving (fun (z : (∀ i, V' → X i) × (∀ w, Y w)) (v : V) => ((fun i => z.1 i (β v)), z.2 (σ v))) (((∏ i, ENNReal.ofReal (b i ^ Fintype.card V)) * ENNReal.ofReal (∏ w, c w)) • (Measure.pi fun i => Measure.pi fun _ : V' => m i).prod (Measure.pi ν)) (Measure.pi fun v : V => (Measure.pi fun i => ENNReal.ofReal (b i) • m i).prod (ENNReal.ofReal (c (σ v)) • ν (σ v))) := by
  first | exact @GlobalTheory.LeviIso.measurePreserving_rearrange | exact GlobalTheory.LeviIso.measurePreserving_rearrange | (intros; apply GlobalTheory.LeviIso.measurePreserving_rearrange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemIsotropicFlagSelfAdjointLeviIffBlockStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_isotropicFlagSelfAdjointLevi_iff_block : ∀ (n n₀ a : ℕ) (j : Fin a → ℕ) (ε : Fin n → Bool) (ε₀ : Fin n₀ → Bool) (B : ∀ i, Matrix (Fin n) (Fin (j i)) ℂ) (B₀ : Matrix (Fin n) (Fin n₀) ℂ), IsFrame ε ε₀ B B₀ → ∀ W : Fin (a + 1) → Submodule ℂ (Fin n → ℂ), SpansFlag B W → ∀ m : Formalism.REAL.UJ ε, m ∈ flagM ε W ↔ ∃ (x : ∀ i, Matrix (Fin (j i)) (Fin (j i)) ℂ) (g : Formalism.REAL.UJ ε₀), (∀ i, (x i).det ≠ 0) ∧ uMat m = lev ε B B₀ x (uMat g) := by
  first | exact @GlobalTheory.LeviIso.Range.mem_flagM_iff | exact GlobalTheory.LeviIso.Range.mem_flagM_iff | (intros; apply GlobalTheory.LeviIso.Range.mem_flagM_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemLatticeAutSplitIffFirstColSingleStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.OrbitTerm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_latticeAut_split_iff_firstCol_single : ∀ (E : Type) [Field E] [NumberField E] (k : ℕ) (Λ : Submodule (𝓞 E) (Fin (k + 1) → E)) (Λ₀ : Submodule (𝓞 E) (Fin 1 → E)) (Λ' : Submodule (𝓞 E) (Fin k → E)), (∀ y, y ∈ Λ ↔ (fun _ => y 0) ∈ Λ₀ ∧ Fin.tail y ∈ Λ') → ∀ x : MatInf E (k + 1), (∀ w a, x w a 0 = if a = 0 then 1 else 0) → (x ∈ autGL E (k + 1) Λ ↔ (fun w a b => x w a.succ b.succ) ∈ autGL E k Λ' ∧ ∃ τ : Fin k → E, (∀ y ∈ Λ', (fun _ => τ ⬝ᵥ y) ∈ Λ₀) ∧ ∀ w b, x w 0 b.succ = w.embedding (τ b)) := by
  first | exact @GlobalTheory.OrbitTerm.mem_autGL_split_iff | exact GlobalTheory.OrbitTerm.mem_autGL_split_iff | (intros; apply GlobalTheory.OrbitTerm.mem_autGL_split_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MirabolicConjInvariantEqSumInducedDerivativesStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolicConjInvariant_eq_sum_induced_derivatives : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) , ψ ≠ 1 → ∀ (n : ℕ) (F : Gn g n → ℂ), 1 ≤ n → IsMirClass F → ∀ p : Gn g n, InMir (p : Mt g n) → F p = ∑ i ∈ Finset.range n, indR ψ i n (der ψ i F) p := by
  first | exact @GlobalTheory.GLm.MirSum.eq_sum_indR_der | exact GlobalTheory.GLm.MirSum.eq_sum_indR_der | (intros; apply GlobalTheory.GLm.MirSum.eq_sum_indR_der <;> assumption)
end

