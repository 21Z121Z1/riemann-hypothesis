import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.CuspLinesIrr
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.TwistedKernels.ExPhiPlusOnto
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0464
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0434
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitriangularMapInduction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0032
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0423
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0452
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenFixedOfSubgroup
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsHeight
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.DecayUniform
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0375
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0442

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearGL
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology

namespace GlobalTheory.CompanionTheory.MirPair

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def uM (n : ℕ) (x : Fin n → k) : Mir k n := unipIn k n (Multiplicative.ofAdd x)

def shearGL (n : ℕ) (b : Fin (n + 1) → k) : GL (Fin (n + 1)) k :=
  open Classical in if h : IsUnit (1 + vecMulVec (eLast k n) b) then h.unit else 1

def piHaar [MeasurableSpace k] (ν : Measure k) (m : ℕ) : Measure (Fin m → k) := Measure.pi fun _ => ν

def wt (ψ : AddChar k Circle) (n : ℕ) (x : Fin (n + 1) → k) : ℂ := ((ψ (-x (Fin.last n)) : Circle) : ℂ)

section Rep

variable {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

def coef (T : Representation ℂ (Mir k n) V) (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v' : V') (x : Fin n → k) : ℂ :=
  B (T (uM n x) v) v'

def TwInv (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V')
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ) : Prop :=
  ∀ (p : Mir k (n + 1)) v v', B (T p v) (T' p v') =
    ((detChar (Fin (n + 1 + 1)) (absPow k (s : ℂ)) (p : GL (Fin (n + 1 + 1)) k) : ℂˣ) : ℂ) * B v v'

def JJ [MeasurableSpace k] (ν : Measure k) (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (M : Set (Fin (n + 1) → k)) (v : V) (v' : V') : ℂ :=
  ∫ x in M, wt ψ n x * coef T B v v' x ∂(piHaar ν (n + 1))

def EvVal [MeasurableSpace k] (ν : Measure k) (ψ : AddChar k Circle) (T : Representation ℂ (Mir k (n + 1)) V)
    (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (v : V) (v' : V') (A : ℂ) : Prop :=
  ∃ t₀ : kˣ, ∀ t : kˣ, valuation k (t₀ : k) ≤ valuation k (t : k) →
    JJ ν ψ T B (box (n + 1) t : Set (Fin (n + 1) → k)) v v' = A

end Rep

end GlobalTheory.CompanionTheory.MirPair

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShiftedEmbeddingMemCongruenceIffStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shifted_embedding_mem_congruence_iff : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (s : kˣ) (hs : ValuativeRel.valuation k (s : k) ≤ 1) (x : Mir k n),
  sEmb k n x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs (n + 1) ↔ x ∈ GlobalTheory.CompanionTheory.BZPhiPG.Onto.congM k s hs n := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.sEmb_mem_congM_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmMemArchSmooth
section
set_option maxSynthPendingDepth 1

open NumberField GlobalTheory.CuspRep GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Reduction
open IsDedekindDomain
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.ArchSmooth

open AutomorphicForm

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

def cMap : mixedEmbedding.mixedSpace E →ₗ[ℝ] Cinf E where
  toFun z := fun w => z.2 ⟨w, IsTotallyComplex.isComplex w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem cMap_ringEquiv (x : InfiniteAdeleRing E) :
    cMap E (InfiniteAdeleRing.ringEquiv_mixedSpace E x) = (infEq E).symm x := by
  funext w
  change (InfiniteAdeleRing.ringEquiv_mixedSpace E x).2 ⟨w, IsTotallyComplex.isComplex w⟩ = _
  rw [InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  rfl

def mMap : ArchMatrix E a →ₗ[ℝ] Lie E a where
  toFun x := fun i j => cMap E ((x : Matrix (Fin a) (Fin a) (mixedEmbedding.mixedSpace E)) i j)
  map_add' x y := by
    funext i j
    exact map_add (cMap E) _ _
  map_smul' c x := by
    funext i j
    exact map_smul (cMap E) c _

def toGL (u : archGroup E a) : GL (Fin a) (Cinf E) :=
  Matrix.GeneralLinearGroup.map (infEq E).symm.toRingHom ((archEquiv E a).symm u)

theorem toL_toGL (u : archGroup E a) :
    toL (toGL E a u).val = mMap E a ((u : (ArchMatrix E a)ˣ) : ArchMatrix E a) := by
  obtain ⟨b, rfl⟩ := (archEquiv E a).surjective u
  funext i j
  simp only [toGL, ContinuousMulEquiv.symm_apply_apply]
  exact (cMap_ringEquiv E (b i j)).symm

theorem infEmb_eq (u : archGroup E a) : infEmb E a u = infGL E a (toGL E a u) := by
  apply ga_ext
  · rw [pInf_infGL]
    ext i j : 2
    have h := congrArg (fun p => (p.1 : Matrix (Fin a) (Fin a) (InfiniteAdeleRing E)) i j) (prodEquiv_infEmb u)
    exact congrArg (infEq E).symm h
  · rw [pFin_infGL]
    ext i j : 2
    exact congrArg (fun p => (p.2 : Matrix (Fin a) (Fin a) (FiniteAdeleRing (𝓞 E) E)) i j) (prodEquiv_infEmb u)

theorem archSlice_eq (φ : GA E a → ℂ) (g : GA E a) (u : archGroup E a) :
    archSlice φ g u = chart φ g (mMap E a ((u : (ArchMatrix E a)ˣ) : ArchMatrix E a)) := by
  rw [← toL_toGL, chart_val, archSlice_apply, infEmb_eq]

theorem sm_mem_archSmooth (φ : Sm E a) : φ.1 ∈ AutomorphicForm.archSmooth E a := by
  intro g
  rw [IsExpLieAlgebra.isSmoothFun_iff]
  intro g'
  let L : ArchMatrix E a →L[ℝ] Lie E a := LinearMap.toContinuousLinearMap (mMap E a)
  let c : ArchMatrix E a := ((g' : (ArchMatrix E a)ˣ) : ArchMatrix E a)
  let F : archLie E a → ArchMatrix E a := fun Y => c * NormedSpace.exp (Y : ArchMatrix E a)
  have hF : ContDiff ℝ ∞ F :=
    contDiff_const.mul ((contDiff_exp ℝ (ArchMatrix E a)).comp (archLie E a).subtypeL.contDiff)
  have hs : ContDiff ℝ ∞ fun Y => L (F Y) := L.contDiff.comp hF
  have hmem : ∀ Y, L (F Y) ∈ invSet E a := fun Y => by
    have : L (F Y) = toL (toGL E a (g' * (isExpLieAlgebra E a).expG Y)).val := (toL_toGL E a (g' * (isExpLieAlgebra E a).expG Y)).symm
    rw [this]
    exact val_mem_invSet _
  have hc := (φ.2 g).comp_contDiff hs hmem
  have e : (fun Y : archLie E a => archSlice φ.1 g (g' * (isExpLieAlgebra E a).expG Y)) =
      chart φ.1 g ∘ fun Y => L (F Y) :=
    funext fun Y => archSlice_eq E a φ.1 g _
  change ContDiff ℝ ∞ (fun Y : archLie E a => archSlice φ.1 g (g' * (isExpLieAlgebra E a).expG Y))
  rw [e]
  exact hc

end GlobalTheory.CompanionTheory.ArchSmooth
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedNearIdentityStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_near_identity : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (w : τ.V ⊗[ℂ] σ.V),
  ∃ O ∈ nhds (1 : Mir k ((i + 1) + t + 1)), ∀ h : HPG k (i + 1) (t + 1), ((h : Mir k ((i + 1) + (t + 1))) ∈ O) → sigX τ σ h w = w := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix | exact GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedParabolicNearOne
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem sigX_fix_nhds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (v : τ.V ⊗[ℂ] σ.V), ∃ O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ a : HPG k (i + 1) (t + 1),
      (a : Mir k ((i + 1) + (t + 1))) ∈ O → sigX τ σ a v = v :=
  GlobalTheory.CompanionTheory.BZPhiPG.Onto.sigX_fix

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieAction
section
noncomputable section

open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspFinDeriv

variable (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)

def cExp (t : ℝ) : GL (Fin a) (Cinf E) :=
  Units.map (Matrix.scalar (Fin a)).toMonoidHom (expU fun _ : InfinitePlace E => (t : ℂ))

theorem splitCentre_eq_infGL (t : ℝ) : GlobalTheory.UnitaryBC.splitCentre E a t = infGL E a (cExp E a t) := rfl

theorem cExp_zero : cExp E a 0 = 1 := by
  have h1 : (GlobalTheory.CuspRep.expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    apply Units.ext
    funext v
    simp [GlobalTheory.CuspRep.expU]
  unfold cExp
  rw [h1, map_one]

theorem hasDerivAt_cExp : HasDerivAt (fun t => toL (cExp E a t).val) (oneL E a) 0 := by
  unfold cExp GlobalTheory.CuspRep.toL GlobalTheory.CuspRep.oneL
  rw [hasDerivAt_pi]
  intro i
  rw [hasDerivAt_pi]
  intro j
  rw [hasDerivAt_pi]
  intro v
  simp [GlobalTheory.CuspRep.expU, Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    have h := (Complex.hasDerivAt_exp ((0 : ℝ) : ℂ)).comp_ofReal
    simp only [Complex.ofReal_zero, Complex.exp_zero] at h
    simpa using h
  · simpa [hij] using hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem hasDerivAt_splitCentre : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (s : ℝ),
    HasDerivAt (fun s : ℝ => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      ((lie E a (oneL E a) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) s := by
  intro E _ _ _ a φ g s
  have hφ := φ.2
  unfold GlobalTheory.CuspRep.Sm at hφ
  have hc := hφ (g * GlobalTheory.UnitaryBC.splitCentre E a s)
  have hopen : IsOpen (GlobalTheory.CuspRep.invSet E a) := by
    unfold GlobalTheory.CuspRep.invSet
    have hdet : Continuous fun x : GlobalTheory.CuspRep.Lie E a => (Matrix.of x).det :=
      (continuous_id.comp continuous_id).matrix_det
    have h3 := Units.isOpen.preimage hdet
    simpa [Matrix.isUnit_iff_isUnit_det] using h3
  have hmem : GlobalTheory.CuspRep.oneL E a ∈ GlobalTheory.CuspRep.invSet E a := by
    unfold GlobalTheory.CuspRep.invSet GlobalTheory.CuspRep.oneL GlobalTheory.CuspRep.toL
    simp
  have hdiff : DifferentiableAt ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      (GlobalTheory.CuspRep.oneL E a) :=
    (hc.differentiableOn (by simp)).differentiableAt (hopen.mem_nhds hmem)
  have hγ0 : GlobalTheory.CuspRep.toL (cExp E a 0).val = GlobalTheory.CuspRep.oneL E a := by
    rw [cExp_zero]
    rfl
  have hl : HasFDerivAt (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s))
      (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a))
      (GlobalTheory.CuspRep.toL (cExp E a 0).val) := by
    rw [hγ0]
    exact hdiff.hasFDerivAt
  have hcomp := hl.comp_hasDerivAt (0 : ℝ) (hasDerivAt_cExp E a)
  have hadd : ∀ s t : ℝ, GlobalTheory.UnitaryBC.splitCentre E a (s + t) =
      GlobalTheory.UnitaryBC.splitCentre E a s * GlobalTheory.UnitaryBC.splitCentre E a t := by
    intro s t
    rw [splitCentre_eq_infGL, splitCentre_eq_infGL, splitCentre_eq_infGL, ← map_mul]
    congr 1
    unfold cExp
    rw [← map_mul]
    congr 1
    apply Units.ext
    funext v
    simp [GlobalTheory.CuspRep.expU, Complex.exp_add]
  have hval : ∀ t : ℝ, GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)
      (GlobalTheory.CuspRep.toL (cExp E a t).val) = (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)) := by
    intro t
    unfold GlobalTheory.CuspRep.chart GlobalTheory.CuspRep.toL
    have hu : IsUnit (Matrix.of (Matrix.of.symm (cExp E a t).val)) := by simp
    rw [dif_pos hu]
    have hunit : hu.unit = cExp E a t := Units.ext (by simp)
    rw [hunit, ← splitCentre_eq_infGL, hadd, mul_assoc]
  have hF : HasDerivAt (fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)))
      (fderiv ℝ (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s)) (GlobalTheory.CuspRep.oneL E a)
        (GlobalTheory.CuspRep.oneL E a)) (s - s) := by
    rw [sub_self]
    have h5 : (GlobalTheory.CuspRep.chart (↑φ) (g * GlobalTheory.UnitaryBC.splitCentre E a s) ∘ fun t => GlobalTheory.CuspRep.toL (cExp E a t).val) =
        fun t : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + t)) := funext hval
    rw [← h5]
    exact hcomp
  have hF2 := HasDerivAt.comp_sub_const s s hF
  have h6 : (fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a (s + (x - s)))) =
      fun x : ℝ => (φ : GlobalTheory.CuspRep.GA E a → ℂ) (g * GlobalTheory.UnitaryBC.splitCentre E a x) := by
    funext x
    rw [show s + (x - s) = x by ring]
  rw [h6] at hF2
  exact hF2

end GlobalTheory.CompanionTheory.CuspFinDeriv

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpace
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.CuspFinGL.Transl

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem rt_comm_of_central {h : GA E a} (hc : ∀ g : GA E a, h * g = g * h) (x : GA E a) (φ : Sm E a) :
    rt E a x (rt E a h φ) = rt E a h (rt E a x φ) := by
  refine Subtype.ext (funext fun g => ?_)
  change φ.1 (g * x * h) = φ.1 (g * h * x)
  rw [mul_assoc g x h, mul_assoc g h x, hc x]

theorem rt_injective (h : GA E a) : Function.Injective (rt E a h) := fun φ ψ e => by
  refine Subtype.ext (funext fun g => ?_)
  have := congrArg (fun f : Sm E a => f.1 (g * h⁻¹)) e
  simpa using this

theorem isAutForm_rt_of_central {h : GA E a} (hc : ∀ g : GA E a, h * g = g * h) {φ : Sm E a}
    (hφ : IsAutForm φ) : IsAutForm (rt E a h φ) where
  left γ g := by
    change φ.1 (ratGL E a γ * g * h) = φ.1 (g * h)
    rw [mul_assoc, hφ.left]
  level := by
    have e : {k | finRep E a k (rt E a h φ) = rt E a h φ} = {k | finRep E a k φ = φ} := by
      ext k
      change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ ↔ rt E a (finGL E a k) φ = φ
      rw [rt_comm_of_central hc]
      exact (rt_injective h).eq_iff
    rw [e]
    exact hφ.level
  kfin := by
    have := hφ.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k => cptRep E a k φ)).map (rt E a h))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact ⟨cptRep E a k φ, Submodule.subset_span ⟨k, rfl⟩, (rt_comm_of_central hc _ φ).symm⟩
  zfin := by
    have := hφ.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a)).map (rt E a h))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z φ, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩
    exact (LinearMap.congr_fun (GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg hz h).eq φ).symm
  growth g := by
    obtain ⟨C, N, hb⟩ := hφ.growth (g * h)
    refine ⟨C, N, fun y => ?_⟩
    have e : (rt E a h φ).1 (g * infGL E a y) = φ.1 (g * h * infGL E a y) := by
      change φ.1 (g * infGL E a y * h) = _
      rw [mul_assoc g _ h, mul_assoc g h, hc]
    rw [e]
    exact hb y

theorem rt_splitCentre_mem : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ)
    (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), J ⊆ Zalg E a →
    ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → ∀ t : ℝ,
      rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ ∈ genSpace L ρ J ∧
        IsCuspidal (rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ).1 := by
  intro E _ _ _ a L W _ _ ρ J hJ φ hφ hcusp t
  set h := GlobalTheory.UnitaryBC.splitCentre E a t with hh
  have hc : ∀ g : GA E a, h * g = g * h := GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_comm t
  obtain ⟨hA, hL, hK, hZ⟩ := hφ
  refine ⟨⟨isAutForm_rt_of_central hc hA, fun k hk => ?_, fun g => ?_, fun z hz => ?_⟩, ?_⟩
  · change rt E a (finGL E a k) (rt E a h φ) = rt E a h φ
    rw [rt_comm_of_central hc]
    exact congrArg (rt E a h) (hL k hk)
  · have e : (fun k : Kinf E a => (cptRep E a k (rt E a h φ)).1 g) =
        fun k : Kinf E a => (cptRep E a k φ).1 (g * h) := by
      funext k
      exact congrArg (fun f : Sm E a => f.1 g) (rt_comm_of_central hc _ φ)
    rw [e]
    exact hK (g * h)
  · have e := LinearMap.congr_fun (GlobalTheory.CompanionTheory.CTFin.Slice1.commute_rt_of_mem_Zalg (hJ hz) h).eq φ
    rw [Module.End.mul_apply, Module.End.mul_apply] at e
    rw [e, hZ z hz, map_zero]
  · intro r hr hr' inst1 inst2 μ 𝓕 hμ hF g
    have e : ∀ x : BlockIx a r → Ad E, (rt E a h φ).1 (unip x * g) = φ.1 (unip x * (g * h)) :=
      fun x => congrArg φ.1 (mul_assoc _ _ _)
    simp only [e]
    exact hcusp r hr hr' μ 𝓕 hμ hF (g * h)

end GlobalTheory.CompanionTheory.CuspFinGL.Transl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitLocalTensorProductSwapStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_local_tensor_product_swap : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), ¬ IsField (Fv F v ⊗[F] E) → ∃ φ : (Fv F v ⊗[F] E) ≃+* Fv F v × Fv F v, (∀ r, φ (sigR (Fv F v) σ r) = (φ r).swap) ∧ ∀ r, r ∈ intLoc F E v ↔ (φ r).1 ∈ v.adicCompletionIntegers F ∧ (φ r).2 ∈ v.adicCompletionIntegers F := by
  first | exact @GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv | exact GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv | (intros; apply GlobalTheory.CompanionTheory.KFin.SplitBase.exists_split_ringEquiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitOrderFgIdealProductStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_order_fg_ideal_product : ∀ {k R : Type} [Field k] [CommRing R] (O : ValuationSubring k) (φ : R ≃+* k × k) (𝔬 : Subring R), (∀ r, r ∈ 𝔬 ↔ (φ r).1 ∈ O ∧ (φ r).2 ∈ O) → ∀ I : Submodule 𝔬 R, I.FG → ∃ α β : k, ∀ r, r ∈ I ↔ (∃ x ∈ O, (φ r).1 = α * x) ∧ (∃ y ∈ O, (φ r).2 = β * y) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal | exact GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal | (intros; apply GlobalTheory.CompanionTheory.KFin.fg_eq_prod_principal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactEntriesIntegral
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section

namespace GlobalTheory.CompanionTheory.GodementH.StdInt

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem compFin_finOne_smul' (v : HeightOneSpectrum (𝓞 F)) (z : AE F E) :
    compFin F E v (finOne F • z) = compFin F E v z := by
  have h1 : GlobalTheory.AdelicU.evFin F v (GlobalTheory.ThK.Dbl.finOne F) = 1 := by
    simp only [GlobalTheory.AdelicU.evFin, GlobalTheory.ThK.Dbl.finOne, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA, LinearMap.inr_apply]
    change (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) = 1
    exact map_one _
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x e =>
    rw [TensorProduct.smul_tmul']
    simp [GlobalTheory.AdelicU.compFin, h1]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy]

theorem absFin_compFin_le_one {z : AE F E} (hz : z ∈ intHat F E) (v : HeightOneSpectrum (𝓞 F)) :
    absFin F v (compFin F E v z) ≤ 1 := by
  let S : AddSubgroup (AE F E) :=
    { carrier := {z | GlobalTheory.AdelicU.absFin F v (GlobalTheory.AdelicU.compFin F E v z) ≤ 1}
      add_mem' := fun {x y} hx hy => by
        simp only [Set.mem_ofPred_eq] at hx hy ⊢
        rw [show GlobalTheory.AdelicU.compFin F E v (x + y) = GlobalTheory.AdelicU.compFin F E v x + GlobalTheory.AdelicU.compFin F E v y from map_add _ _ _]
        exact (GlobalTheory.AdelicU.absFin_add_le F v _ _).trans (max_le hx hy)
      zero_mem' := by
        simp only [Set.mem_ofPred_eq]
        rw [show GlobalTheory.AdelicU.compFin F E v 0 = 0 from map_zero _, GlobalTheory.AdelicU.absFin_zero]
        exact zero_le_one
      neg_mem' := fun {x} hx => by
        simp only [Set.mem_ofPred_eq] at hx ⊢
        rw [show GlobalTheory.AdelicU.compFin F E v (-x) = -GlobalTheory.AdelicU.compFin F E v x from map_neg _ _, GlobalTheory.AdelicU.absFin_neg]
        exact hx }
  have hle : intHat F E ≤ S := by
    rw [GlobalTheory.ThK.Dbl.intHat, AddSubgroup.closure_le]
    rintro z ⟨a, -, ha, o, rfl⟩
    show GlobalTheory.AdelicU.absFin F v (GlobalTheory.AdelicU.compFin F E v _) ≤ 1
    have h2 : GlobalTheory.AdelicU.compFin F E v (a • (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) (o : E)) =
        (GlobalTheory.AdelicU.evFin F v a) ⊗ₜ[F] (o : E) := by
      simp [Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR, GlobalTheory.AdelicU.compFin, TensorProduct.smul_tmul']
    rw [h2]
    refine (GlobalTheory.AdelicU.absFin_tmul_le F v _ o).trans ?_
    exact nnnorm_le_one_iff_mem.mpr (ha v)
  exact hle hz

theorem absFin_inFrame_le_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)),
    IsStdK (σ := σ) (Y := Y) B b K → ∀ k ∈ K, ∀ (v : Pl F) (i j : Fin n ⊕ Fin n), absFin F v (compFin F E v (inFrame b k i j)) ≤ 1 := by
  intro F E _ _ _ _ _ σ n Y B b K hK k hk v i j
  have h : GlobalTheory.ThK.Dbl.finOne F • GlobalTheory.ThK.Dbl.inFrame b k i j ∈ GlobalTheory.ThK.Dbl.intHat F E :=
    ((hK k).1 hk).2 k (by simp) i j
  have h' := absFin_compFin_le_one h v
  rwa [compFin_finOne_smul'] at h'

end GlobalTheory.CompanionTheory.GodementH.StdInt

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SumDiagPairsToNatEqWeightedSumStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL Matrix ValuativeRel GlobalTheory.CompanionTheory.IwJac
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_diag_pairs_toNat_eq_weighted_sum : ∀ (n : ℕ) (x : Fin n → ℤ), StrictAnti x → ((∑ d ∈ Finset.range n, ∑ p ∈ diagPairs n d, (x p.1 - x p.2).toNat : ℕ) : ℤ) = ∑ i : Fin n, ((n : ℤ) - 1 - 2 * (i : ℕ)) * x i := by
  first | exact @GlobalTheory.CompanionTheory.IwJac.sum_diagPairs_toNat | exact GlobalTheory.CompanionTheory.IwJac.sum_diagPairs_toNat | (intros; apply GlobalTheory.CompanionTheory.IwJac.sum_diagPairs_toNat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorFixedByInvolutionIsBaseStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_fixed_by_involution_is_base : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (a : K ⊗[F] E), sigR K σ a = a → ∃ x : K, algebraMap K (K ⊗[F] E) x = a := by
  first | exact @GlobalTheory.CompanionTheory.KFin.sigR_fixed_eq_algebraMap | exact GlobalTheory.CompanionTheory.KFin.sigR_fixed_eq_algebraMap | (intros; apply GlobalTheory.CompanionTheory.KFin.sigR_fixed_eq_algebraMap <;> assumption)
end

