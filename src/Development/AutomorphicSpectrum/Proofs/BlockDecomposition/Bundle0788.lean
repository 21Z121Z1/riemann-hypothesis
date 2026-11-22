import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0005
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0024
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0071
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0614
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0080
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ThetaFixedGlobalOfTraceInputs
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.ConeWeightsNotSecondType
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.FiniteTypes.FintypeHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0399
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.ExtraTop
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1312
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanVolumeRankOneIsotropic
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.Inf0 GlobalTheory.CompanionTheory.SW.BB

namespace GlobalTheory.CompanionTheory.WeilSiegel.Inf0

theorem fibre_rapid_zero_eq_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (μ : Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ 1)) (m : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin M → Ainf F ⊗[F] E)), μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFibFree (Ainf F) σ J 1 μ ν m → ∀ φ : (Fin 1 → Fin M → Ainf F ⊗[F] E) → ℝ, Continuous φ → (∀ X, 0 ≤ φ X) → RapidDecay b (fun X => (φ X : ℂ)) → ∀ D : HermR (Ainf F) σ 1 → ℝ, Continuous D → (∀ U : Set (HermR (Ainf F) σ 1), MeasurableSet U → ∫⁻ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' U), ENNReal.ofReal (φ X) ∂μ = ∫⁻ S in U, ENNReal.ofReal (D S) ∂ν) → ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) = ENNReal.ofReal (D (hermOf (Ainf F) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀)) := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM h₀ d b μ ν m hμ hν hm φ hφc hφ0 hφr D hDc hD
  obtain ⟨ρ, e, hρ, he, heρ, hen, -⟩ := GlobalTheory.T.infinite_adele_haar_map_eq_scaled_volume F hCM.1
  have hd : d = 2 := by
    have h := Module.finrank_eq_card_basis b
    simpa [hCM.2.2.1] using h.symm
  have hLoc : IsLocR (Ainf F) := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hCM.1
  obtain ⟨hTR, hLC, hSC, hT2, -, -, -, -⟩ := id hLoc
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  obtain ⟨hKr, hKl, hKs, hK2, -, -, -, hVb, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM (Ainf F)
  haveI := hKr
  haveI := hKl
  haveI := hKs
  haveI := hK2
  haveI := hVb 1 M
  obtain ⟨hXl, hXs, hX2, hXb, hlift⟩ := GlobalTheory.CompanionTheory.SW.HermTop.herm_top F E σ hCM (Ainf F) 1
  haveI := hXl
  haveI := hXs
  haveI := hX2
  haveI := hXb
  obtain ⟨g, hgc, hgf⟩ := hlift M J hJ
  have hreal : ∀ (A Pm : InfinitePlace F → Matrix (Fin M × Fin d) (Fin M × Fin d) ℝ) (Di : (InfinitePlace F → ℝ) → ℝ), Continuous Di → (∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U, ENNReal.ofReal (gaussR Pm x) = ∫⁻ y in U, ENNReal.ofReal (Di y)) → ∀ f : (InfinitePlace F → Fin M × Fin d → ℝ) → ℝ, Measurable f → (∀ x, 0 ≤ f x) → (∀ N : ℕ, ∃ C' : ℝ, ∀ x, f x * (1 + ∑ w, ‖x w‖) ^ N ≤ C') → ∀ ε : ℝ, 0 < ε → ∃ δ R : ℝ, 0 < δ ∧ 0 < R ∧ ∀ U : Set (InfinitePlace F → ℝ), MeasurableSet U → ∫⁻ x in qR0 A ⁻¹' U ∩ (coreR δ R)ᶜ, ENNReal.ofReal (f x) ≤ ENNReal.ofReal ε * volume U := by
    intro A Pm Di hDi hdens f hf hf0 hfr ε hε
    have hcard : Fintype.card (Fin M × Fin d) = M * 2 := by simp [hd]
    obtain ⟨C, hC⟩ := GlobalTheory.T.quadratic_box_volume_bound (InfinitePlace F) (Fin M × Fin d) A Pm Di (by omega) hDi hdens
    have hQ : Measurable (qR0 A : (InfinitePlace F → Fin M × Fin d → ℝ) → _) := by
      refine Continuous.measurable (continuous_pi fun w => continuous_const.mul ?_)
      exact (continuous_apply w).dotProduct (continuous_const.matrix_mulVec (continuous_apply w))
    exact GlobalTheory.T.quadratic_box_integral_small_ball (InfinitePlace F) (Fin M × Fin d) _ (by omega) (qR0 A) hQ C hC f hf hf0 hfr ε hε
  refine GlobalTheory.T.disintegration_injective_open_map _ _ _ μ ν (gramR (Ainf F) σ J) g Subtype.val Subtype.val_injective hgc hgf _ m (GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free F E σ hCM (Ainf F) hLoc 1 M) hm φ hφc hφ0 D hDc hD ?_ _
  intro ε hε
  obtain ⟨δ, R, hδ, hR, hK, hb⟩ := GlobalTheory.T.archimedean_rank_one_volume_bound F E σ hCM M J hJ hM d b ρ e hρ he heρ hen hreal μ ν hμ hν φ hφc hφ0 hφr ε hε
  refine ⟨_, hK, ?_, hb⟩
  intro X hX
  refine GlobalTheory.T.archimedean_rank_one_free_of_places F E σ hCM M d b ρ e hρ he heρ X fun w h => ?_
  have h1 := (hX w).1
  have h2 : ‖(fun w => xw e b X w) w‖ = 0 := by
    show ‖xw e b X w‖ = 0
    rw [h, norm_zero]
  linarith

end GlobalTheory.CompanionTheory.WeilSiegel.Inf0
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjugatePlacesFactsStatement
section
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_places_facts : ConjPlaces := by
  first | exact @GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces | exact GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces | (intros; apply GlobalTheory.CompanionTheory.ConjAtPlaces.conjPlaces <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EopWMemStabAlg
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.Desc

namespace GlobalTheory.CompanionTheory.TwY

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev UU (n : ℕ) : Type := Matrix.unitaryGroup (Fin n) ℂ

open Classical in

def singleN (w : InfinitePlace E) : ℂ →ₙ+* Cinf E where
  toFun x := fun v => if v = w then x else 0
  map_mul' x y := by
    funext v
    by_cases hv : v = w <;> simp [hv]
  map_zero' := by
    funext v
    simp
  map_add' x y := by
    funext v
    by_cases hv : v = w <;> simp [hv]

def locInf (w : InfinitePlace E) : PositivityTheory.RgTw.G n →* GL (Fin n) (Cinf E) := cornerGL n (singleN w)

def gAt (w : InfinitePlace E) : PositivityTheory.RgTw.G n →* GA E n := (infGL E n).comp (locInf w)

def kAt (w : InfinitePlace E) : UU n →* GA E n := (gAt w).comp Unitary.toUnits

omit [NumberField E] [IsCMField E] in
theorem one_apply_pi (i j : Fin n) (v : InfinitePlace E) :
    (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j v = (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  by_cases hij : i = j
  · subst hij; simp
  · simp [Matrix.one_apply_ne hij]

omit [NumberField E] [IsCMField E] in
open Classical in
theorem locInf_apply (w : InfinitePlace E) (g : PositivityTheory.RgTw.G n) (i j : Fin n) (v : InfinitePlace E) :
    ((locInf w g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j v =
      if v = w then (g : Matrix (Fin n) (Fin n) ℂ) i j else (1 : Matrix (Fin n) (Fin n) ℂ) i j := by
  have e : ((locInf w g : GL (Fin n) (Cinf E)) : Matrix (Fin n) (Fin n) (Cinf E)) i j v =
      (1 : Matrix (Fin n) (Fin n) (Cinf E)) i j v - singleN w ((1 : Matrix (Fin n) (Fin n) ℂ) i j) v +
        singleN w ((g : Matrix (Fin n) (Fin n) ℂ) i j) v := rfl
  rw [e, one_apply_pi]
  change _ - (if v = w then _ else 0) + (if v = w then _ else 0) = _
  by_cases hv : v = w <;> simp [hv]

def kInfAt (w : InfinitePlace E) (c : UU n) : Kinf E n :=
  ⟨(locInf w (Unitary.toUnits c) : GL (Fin n) (Cinf E)).val, by
    classical
    refine Matrix.mem_unitaryGroup_iff'.2 ?_
    ext i j v
    have hc : star c.1 * c.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 c.2
    rw [Matrix.mul_apply, Finset.sum_apply, one_apply_pi]
    simp only [Matrix.star_apply, Pi.mul_apply, Pi.star_apply, locInf_apply]
    by_cases hv : v = w
    · simp only [hv, if_true]
      have := congrFun (congrFun hc i) j
      rw [Matrix.mul_apply] at this
      simp only [Matrix.star_apply] at this
      rw [← this]
      rfl
    · simp only [hv, if_false]
      simp [Matrix.one_apply, eq_comm]⟩

theorem infGL_kInfAt (w : InfinitePlace E) (c : UU n) :
    infGL E n (Unitary.toUnits (kInfAt w c)) = kAt w c := by
  unfold kAt gAt
  simp only [MonoidHom.comp_apply]
  congr 1
  exact Units.ext rfl

def sV (π : CuspSub E n) (w : InfinitePlace E) : UU n →* Module.End ℂ π.V where
  toFun c := (rt E n (kAt w c)).restrict fun ψ hψ => by
    have h := π.stable (.cpt (kInfAt w c)) ψ hψ
    have e : rt E n (kAt w c) ψ = cptRep E n (kInfAt w c) ψ := by
      rw [← infGL_kInfAt]; rfl
    rw [e]; exact h
  map_one' := by
    ext ψ; simp
  map_mul' a b := by
    ext ψ; simp

def stabAlg (π : CuspSub E n) : Subalgebra ℂ (Module.End ℂ (Sm E n)) where
  carrier := {T | ∀ ψ ∈ π.V, T ψ ∈ π.V}
  mul_mem' ha hb ψ hψ := ha _ (hb ψ hψ)
  add_mem' ha hb ψ hψ := π.V.add_mem (ha ψ hψ) (hb ψ hψ)
  algebraMap_mem' c ψ hψ := π.V.smul_mem c hψ

theorem Eop_mem_stabAlg (π : CuspSub E n) (τ : E →+* ℂ) (i j : Fin n) : Eop (a := n) τ i j ∈ stabAlg π := by
  have hL : ∀ X, lie E n X ∈ stabAlg π := fun X ψ hψ => π.stable (.lie X) ψ hψ
  exact (stabAlg π).smul_mem ((stabAlg π).sub_mem (hL _) ((stabAlg π).smul_mem (hL _) _)) _

theorem eopW_mem_stabAlg (π : CuspSub E n) (w : InfinitePlace E) (s : Bool) (i j : Fin n) :
    PositivityTheory.RgBcC.Bridge.eopW w s i j ∈ stabAlg π := by
  cases s
  · exact Eop_mem_stabAlg π _ i j
  · exact Eop_mem_stabAlg π _ i j

theorem kG_mem_stabAlg (π : CuspSub E n) (w : InfinitePlace E) (a b : Fin n) : kG w a b ∈ stabAlg π :=
  (stabAlg π).add_mem (eopW_mem_stabAlg π w true a b)
    ((stabAlg π).neg_mem (eopW_mem_stabAlg π w false b a))

def kV (π : CuspSub E n) (w : InfinitePlace E) (a b : Fin n) : Module.End ℂ π.V :=
  (kG w a b).restrict (kG_mem_stabAlg π w a b)

def fV (π : CuspSub E n) (k : GL (Fin n) (Af E)) : Module.End ℂ π.V :=
  (finRep E n k).restrict fun ψ hψ => π.stable (.fin k) ψ hψ

section Avg

variable [MeasurableSpace (UU n)] (κ : Measure (UU n)) (Em : PositivityTheory.RgBcC.KMod n) (T : Em.V →L[ℂ] Em.V)

def qFun (w : InfinitePlace E) (φ : GA E n → ℂ) : GA E n → ℂ :=
  fun x => ∫ c, GlobalTheory.CompanionTheory.TrPassage.chiT Em T c * φ (x * kAt w c) ∂κ

def IsQ (w : InfinitePlace E) (π : CuspSub E n) (Q : Module.End ℂ π.V) : Prop :=
  ∀ (ψ : π.V) (x : GA E n), ((Q ψ : π.V) : Sm E n).1 x = qFun κ Em T w (ψ : Sm E n).1 x

end Avg

def coefW (Em : PositivityTheory.RgBcC.KMod n) : Submodule ℂ (UU n → ℂ) :=
  Submodule.span ℂ (Set.range fun p : (Em.V →L[ℂ] ℂ) × Em.V => fun c : UU n => p.1 (Em.ρ c⁻¹ p.2))

def tlS (Em : PositivityTheory.RgBcC.KMod n) (w : InfinitePlace E) : Submodule ℂ (Sm E n) where
  carrier := {φ | ∀ x, (fun c : UU n => φ.1 (x * kAt w c)) ∈ coefW Em}
  add_mem' {a b} ha hb x := (coefW Em).add_mem (ha x) (hb x)
  zero_mem' x := (coefW Em).zero_mem
  smul_mem' r a ha x := (coefW Em).smul_mem r (ha x)

abbrev tl (lam : InfinitePlace E → Fin n → ℤ) (w : InfinitePlace E) : Submodule ℂ (Sm E n) :=
  tlS (PositivityTheory.RgBcC.lefE n (lam w)) w

def vMod (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (lam : InfinitePlace E → Fin n → ℤ)
    (μ : InfinitePlace E → Fin n → ℝ) (S : Finset (InfinitePlace E)) (w : InfinitePlace E) : Submodule ℂ (Sm E n) :=
  fixK π K ⊓ (⨅ v ∈ S, hwG v (μ v)) ⊓ ⨅ (v : InfinitePlace E) (_ : v ∉ S) (_ : v ≠ w), tl lam v

def wMod (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (lam : InfinitePlace E → Fin n → ℤ)
    (μ : InfinitePlace E → Fin n → ℝ) (S : Finset (InfinitePlace E)) : Submodule ℂ (Sm E n) :=
  fixK π K ⊓ (⨅ v ∈ S, hwG v (μ v)) ⊓ ⨅ (v : InfinitePlace E) (_ : v ∉ S), tl lam v

abbrev wV (π : CuspSub E n) (K : Subgroup (GL (Fin n) (Af E))) (lam : InfinitePlace E → Fin n → ℤ)
    (μ : InfinitePlace E → Fin n → ℝ) (S : Finset (InfinitePlace E)) : Submodule ℂ π.V :=
  (wMod π K lam μ S).comap π.V.subtype

def itF [MeasurableSpace (PositivityTheory.RgTw.G n)] (μC : Measure (PositivityTheory.RgTw.G n))
    (f : InfinitePlace E → PositivityTheory.RgTw.G n → ℂ) (l : List (InfinitePlace E)) (Φ : GA E n → ℂ) : GA E n → ℂ :=
  l.foldr (fun w Ψ x => ∫ y, f w y * Ψ (x * gAt w y) ∂μC) Φ

end GlobalTheory.CompanionTheory.TwY
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsFiniteDimCompactStable
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscKfin

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {M : ℕ}

theorem fin_cpt_apply (u : GL (Fin M) (Af E)) (k : Kinf E M) (a : Sm E M) :
    finRep E M u (cptRep E M k a) = cptRep E M k (finRep E M u a) := by
  have h : finRep E M u * cptRep E M k = cptRep E M k * finRep E M u := by
    change rt E M (finGL E M u) * rt E M (infGL E M (Unitary.toUnits k)) =
      rt E M (infGL E M (Unitary.toUnits k)) * rt E M (finGL E M u)
    rw [← map_mul, ← map_mul, infGL_comm]
  exact LinearMap.congr_fun h a

theorem continuous_coeff (A : Submodule ℂ (Sm E M)) [FiniteDimensional ℂ A]
    (hA : ∀ k, ∀ a ∈ A, cptRep E M k a ∈ A) (ℓ : Sm E M →ₗ[ℂ] ℂ) (a : Sm E M) (ha : a ∈ A) :
    Continuous fun k => ℓ (cptRep E M k a) := by
  let ev : GA E M → Module.Dual ℂ A := fun g =>
    (LinearMap.proj g).comp ((Sm E M).subtype.comp A.subtype)
  have hspan : Submodule.span ℂ (Set.range ev) = ⊤ := by
    have h0 : (Submodule.span ℂ (Set.range ev)).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro v hv
      rw [Submodule.mem_dualCoannihilator] at hv
      have h2 : ∀ g, v.1.1 g = 0 := fun g => hv _ (Submodule.subset_span ⟨g, rfl⟩)
      rw [Submodule.mem_bot]
      exact Subtype.ext (Subtype.ext (funext h2))
    rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span ℂ (Set.range ev)), h0,
      Submodule.dualAnnihilator_bot]
  have key : ∀ ξ ∈ Submodule.span ℂ (Set.range ev),
      Continuous fun k => ξ ⟨cptRep E M k a, hA k a ha⟩ := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact GlobalTheory.CompanionTheory.AdmDiscFin.continuous_slice a g
    | zero => exact continuous_const
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.const_smul r
  exact key (ℓ.comp A.subtype) (hspan ▸ Submodule.mem_top)

end GlobalTheory.CompanionTheory.FinDiscKfin

theorem GlobalTheory.CompanionTheory.FinDiscKfin.exists_kfin_subspace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (V : Submodule ℂ (Sm E N)), IsDiscrete V →
      ∀ L : Subgroup (GL (Fin N) (Af E)), ∀ x ∈ V, (∀ u ∈ L, finRep E N u x = x) →
      ∃ A : Submodule ℂ (Sm E N), FiniteDimensional ℂ A ∧ x ∈ A ∧
        (∀ a ∈ A, a ∈ V ∧ ∀ u ∈ L, finRep E N u a = a) ∧ (∀ k, ∀ a ∈ A, cptRep E N k a ∈ A) ∧
        ∀ ℓ : Sm E N →ₗ[ℂ] ℂ, ∀ a ∈ A, Continuous fun k => ℓ (cptRep E N k a) := by
  intro E _ _ _ N V hV L x hx hL
  haveI hfin : FiniteDimensional ℂ (GlobalTheory.AutGrowth.spanK E N x) := (hV.aut x hx).kfin
  refine ⟨GlobalTheory.AutGrowth.spanK E N x, hfin, GlobalTheory.AutGrowth.self_mem_spanK x, ?_,
    GlobalTheory.AutGrowth.spanK_stable x, fun ℓ a ha =>
      GlobalTheory.CompanionTheory.FinDiscKfin.continuous_coeff _ (GlobalTheory.AutGrowth.spanK_stable x) ℓ a ha⟩
  intro a ha
  refine ⟨?_, fun u hu => ?_⟩
  · induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      exact hV.stable (.cpt k) x hx
    | zero => exact V.zero_mem
    | add y z _ _ hy hz => exact V.add_mem hy hz
    | smul c y _ hy => exact V.smul_mem c hy
  · induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨k, rfl⟩ := hy
      change finRep E N u (cptRep E N k x) = cptRep E N k x
      rw [GlobalTheory.CompanionTheory.FinDiscKfin.fin_cpt_apply, hL u hu]
    | zero => exact map_zero _
    | add y z _ _ hy hz => rw [map_add, hy, hz]
    | smul c y _ hy => rw [map_smul, hy]

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantProjection
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDiscAvg

theorem exists_sum_fixed {G W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [AddCommGroup W] [Module ℂ W] (ρ : G →* Module.End ℂ W) (x : W) (ho : IsOpen {k | ρ k x = x}) :
    ∃ R : Finset G, R.Nonempty ∧ ∀ u, ρ u (∑ r ∈ R, ρ r x) = ∑ r ∈ R, ρ r x := by
  let K : Subgroup G :=
    { carrier := {k | ρ k x = x}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_mul, Module.End.mul_apply, hb, ha]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h : ρ a⁻¹ (ρ a x) = x := by
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
        rwa [ha] at h }
  have hK : ∀ k, k ∈ K ↔ ρ k x = x := fun _ => Iff.rfl
  obtain ⟨R, hR, hc⟩ := GlobalTheory.compact_finite_leftCoset_reps G K ho Set.univ isCompact_univ
  have hc' : ∀ g : G, ∃ r ∈ R, r⁻¹ * g ∈ K := fun g => hc g (Set.mem_univ g)
  have hne : R.Nonempty := by
    obtain ⟨r, hr, -⟩ := hc' 1
    exact ⟨r, hr⟩
  refine ⟨R, hne, fun u => ?_⟩
  choose! σ hσR hσ using fun r : G => hc' (u * r)
  have hval : ∀ r, ρ (u * r) x = ρ (σ r) x := by
    intro r
    have h := (hK _).1 (hσ r)
    have e : u * r = σ r * ((σ r)⁻¹ * (u * r)) := by group
    rw [e, map_mul, Module.End.mul_apply, h]
  have hinj : Set.InjOn σ R := by
    intro r hr r' hr' e
    refine hR r hr r' hr' ?_
    have h1 := hσ r
    have h2 := hσ r'
    rw [show σ r = σ r' from e] at h1
    have := K.mul_mem (K.inv_mem h1) h2
    have e2 : ((σ r')⁻¹ * (u * r))⁻¹ * ((σ r')⁻¹ * (u * r')) = r⁻¹ * r' := by group
    rwa [e2] at this
  have himg : R.image σ = R := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro s hs
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.1 hs
      exact hσR r
    · rw [Finset.card_image_of_injOn hinj]
  calc ρ u (∑ r ∈ R, ρ r x) = ∑ r ∈ R, ρ (σ r) x := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [← hval, map_mul, Module.End.mul_apply]
    _ = ∑ s ∈ R.image σ, ρ s x := (Finset.sum_image (f := fun s => ρ s x) hinj).symm
    _ = ∑ r ∈ R, ρ r x := by rw [himg]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant]

theorem l2Map_right_translate (k : GL (Fin N) (Af E)) {a : Sm E N} (ha : a ∈ squareIntegrableSmoothSubmoduleGL μ) (hb : finRep E N k a ∈ squareIntegrableSmoothSubmoduleGL μ) :
    l2Map μ (finRep E N k a) = R (latticeGL E N) μ (finGL E N k) (l2Map μ a) := by
  rw [l2Map_apply μ ha, l2Map_apply μ hb, right_translate_toL2]
  rfl

theorem inner_R (g : GA E N) (u v : L2 (latticeGL E N) μ) :
    ⟪R (latticeGL E N) μ g u, R (latticeGL E N) μ g v⟫_ℂ = ⟪u, v⟫_ℂ := by
  let T : L2 (latticeGL E N) μ →ₗᵢ[ℂ] L2 (latticeGL E N) μ :=
    ⟨(R (latticeGL E N) μ g : L2 (latticeGL E N) μ →L[ℂ] L2 (latticeGL E N) μ).toLinearMap, norm_R g⟩
  exact T.inner_map_map u v

theorem exists_avg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (V : Submodule ℂ (Sm E N)), IsDiscrete V → ∀ L : Subgroup (GL (Fin N) (Af E)), IsCompact (L : Set (GL (Fin N) (Af E))) → ∀ x ∈ V, ∃ x' ∈ V, (∀ u ∈ L, finRep E N u x' = x') ∧ ∀ y : Sm E N, y ∈ squareIntegrableSmoothSubmoduleGL μ → (∀ u ∈ L, finRep E N u y = y) → ⟪l2Map μ x, l2Map μ y⟫_ℂ = ⟪l2Map μ x', l2Map μ y⟫_ℂ := by
  intro E _ _ _ N μ _ _ V hV L hL x hx
  haveI : CompactSpace L := isCompact_iff_compactSpace.1 hL
  let ρ : L →* Module.End ℂ (Sm E N) := (finRep E N).comp L.subtype
  have hρ : ∀ l : L, ρ l = finRep E N (l : GL (Fin N) (Af E)) := fun _ => rfl
  have ho : IsOpen {k : L | ρ k x = x} :=
    (hV.aut x hx).level.preimage continuous_subtype_val
  obtain ⟨S, hS, hfix⟩ := exists_sum_fixed ρ x ho
  have hn : ((S.card : ℂ)) ≠ 0 := Nat.cast_ne_zero.2 hS.card_pos.ne'
  have hmem : ∀ l : L, ρ l x ∈ V := fun l => hV.stable (.fin _) x hx
  refine ⟨(S.card : ℂ)⁻¹ • ∑ r ∈ S, ρ r x, V.smul_mem _ (V.sum_mem fun r _ => hmem r), ?_, ?_⟩
  · intro u hu
    rw [map_smul, ← hρ ⟨u, hu⟩ , hfix]
  · intro y hy hyL
    have hl2 : ∀ z ∈ V, z ∈ squareIntegrableSmoothSubmoduleGL μ := fun z hz => mem_l2Sub_of_isAutForm μ (hV.aut z hz) (hV.sqInt z hz)
    have hxl := hl2 x hx
    have key : ∀ r : L, ⟪l2Map μ (ρ r x), l2Map μ y⟫_ℂ = ⟪l2Map μ x, l2Map μ y⟫_ℂ := by
      intro r
      have e1 := l2Map_right_translate μ (r : GL (Fin N) (Af E)) hxl (hl2 _ (hmem r))
      have e2 := l2Map_right_translate μ (r : GL (Fin N) (Af E)) hy (by rw [hyL _ r.2]; exact hy)
      rw [hyL _ r.2] at e2
      rw [hρ, e1]
      conv_lhs => rw [e2]
      exact inner_R μ _ _ _
    rw [map_smul, map_sum, inner_smul_left, sum_inner, Finset.sum_congr rfl fun r _ => key r,
      Finset.sum_const, nsmul_eq_mul, map_inv₀, Complex.conj_natCast, inv_mul_cancel_left₀ hn]

end GlobalTheory.CompanionTheory.FinDiscAvg

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsOpenCompactSubgroupLe
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem exists_compact_open_level_le (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (S : Subgroup (GL (Fin N) (Af E))) (hS : IsOpen (S : Set (GL (Fin N) (Af E)))) :
    ∃ L : Subgroup (GL (Fin N) (Af E)), L ≤ S ∧ IsOpen (L : Set (GL (Fin N) (Af E))) ∧
      IsCompact (L : Set (GL (Fin N) (Af E))) := by
  let K : Subgroup (GL (Fin N) (Af E)) := GroundTheory.Automorphic.AdelicGLn.integralFiniteGL E N
  have hKo : IsOpen (K : Set (GL (Fin N) (Af E))) :=
    GroundTheory.Automorphic.AdelicGLn.isOpen_integralFiniteGL E N
  have hKc : IsCompact (K : Set (GL (Fin N) (Af E))) :=
    GroundTheory.Automorphic.AdelicGLn.isCompact_integralFiniteGL E N
  have hSc : IsClosed (S : Set (GL (Fin N) (Af E))) := Subgroup.isClosed_of_isOpen S hS
  refine ⟨S ⊓ K, inf_le_left, ?_, ?_⟩
  · simpa using hS.inter hKo
  · have : ((S ⊓ K : Subgroup _) : Set (GL (Fin N) (Af E))) =
        (K : Set (GL (Fin N) (Af E))) ∩ (S : Set (GL (Fin N) (Af E))) := by
      ext x; simp [and_comm]
    rw [this]
    exact hKc.inter_right hSc

end GlobalTheory.CompanionTheory.FinDiscOrth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqL2Inner
section
open scoped Classical InnerProductSpace ComplexConjugate
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.AutomorphicL2Unitary GlobalTheory.SqIntGL
open scoped GlobalTheory.CuspRep.CuspidalL2GL

namespace GlobalTheory.CompanionTheory.FinDiscOrth

theorem setIntegral_mul_conj_eq_inner : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) (μ : Measure (GA E N)) [μ.IsHaarMeasure] (F : Set (GA E N)), IsFundamentalDomain (latticeGL E N) F μ → ∀ x y : Sm E N, x ∈ squareIntegrableSmoothSubmoduleGL μ → y ∈ squareIntegrableSmoothSubmoduleGL μ → ∫ g in F, x.1 g * (starRingEnd ℂ) (y.1 g) ∂μ = ⟪l2Map μ y, l2Map μ x⟫_ℂ := by
  intro E _ _ _ N μ _ F hF x y hx hy
  rw [l2Map_apply μ hx, l2Map_apply μ hy, MemL2Quotient.inner_toL2_eq_theta_pairing, pet_eq hF ((mem_l2Sub μ).1 hx).1 ((mem_l2Sub μ).1 hy).1]

end GlobalTheory.CompanionTheory.FinDiscOrth
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearlyIndependentFramesOpenStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearly_independent_frames_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n M : ℕ), IsOpen {X : Fin n → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free | exact GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.FreeOpen.isOpen_free <;> assumption)
end

