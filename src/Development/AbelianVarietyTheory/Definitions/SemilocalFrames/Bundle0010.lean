import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0056
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AmpKFIff
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.NoPr

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.CellAmp

def Gp (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) : Prop :=
  ∃ h : ℝ, Formalism.QuantumDeterminants.GapAtLeast ε mu h ∧ Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h

def AmpKF0 : Prop :=
  ∀ (k r : ℕ) (L : LocBessel k r) (h : ℝ) (μG : Measure (Mt k r)) (w0 : L.Hs) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq),
    OnePlaceKF L h μG w0 l l' →
    ∀ (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (μR νR : Measure (Mt k r))
      (ν : Measure (PairSp k r)), CellData L μG γ μR νR ν →
    ∀ b : ℝ, 0 ≤ b → Formalism.FourierDecayAlt.ThreeDimData.AG k r + 1 < Formalism.FourierDecayAlt.ThreeDimData.aOf r h - 1 - b → Integrable (pairMaj γ b) ν →
    ∀ v v' : L.Hs, PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v → PI.UpqRep.IsKFinHpk (k := k) (r := r) L.σ v' →
    ∀ (ξ : L.Wp) (ξ' : L.Wq),
      (⟪l v, ξ⟫_ℂ * ⟪ξ', l' v'⟫_ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ =
        ((PI.BesselPeriodGGP.fdegH μG L.σ w0 : ℂ)⁻¹) • OrbInt L (coefF L v v' ξ ξ') γ ν

end GlobalTheory.NoPr

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.CellDataExists
section
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellAmp.Model

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

theorem amp_dirac {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] (R : BranchingSupport.Rep k r) (l : R.H → Wp) (l' : R.H → Wq) (w : R.H)
    (x : Mt k r) (γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (η : Wq) :
    amp R l l' w (Measure.dirac x) γ η =
      ⟪l' (R.σ (Matrix.of x) w), η⟫_ℂ • l (R.σ (γ * Matrix.of x) w) := by
  unfold amp ampJ
  rw [integral_dirac]
  simp

theorem coefF_apply {k r : ℕ} (L : LocBessel k r) (v v' : L.Hs) (ξ : L.Wp) (ξ' η : L.Wq)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    coefF L v v' ξ ξ' g η = (⟪ξ', η⟫_ℂ * ⟪v, L.σ g v'⟫_ℂ) • ξ := by
  simp [coefF, smul_smul]

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
private theorem inv_mul_conj_mul_cancel {n : Type*} [Fintype n] [DecidableEq n] (A B C D γ a : Matrix n n ℂ)
    (hγ : IsUnit γ.det) (ha : IsUnit a.det) :
    A⁻¹ * (a * B)⁻¹ * γ * (γ⁻¹ * a * γ * C) * D = A⁻¹ * B⁻¹ * γ * C * D := by
  rw [Matrix.mul_inv_rev]
  have h1 : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hγ
  have h2 : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha
  calc A⁻¹ * (B⁻¹ * a⁻¹) * γ * (γ⁻¹ * a * γ * C) * D
      = A⁻¹ * B⁻¹ * (a⁻¹ * ((γ * γ⁻¹) * a)) * γ * C * D := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.one_mul, h2, Matrix.mul_one]

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.CellAmp.Model.pairMaj_stabAct {k r : ℕ} (γ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hγ : IsUnit γ.det)
    (ha : IsUnit a.det) (b : ℝ) (p : _root_.Formalism.MainNotions.S.PairSp k r) : _root_.GlobalTheory.CellAmp.pairMaj γ b (_root_.Formalism.MainNotions.S.stabAct γ a p) = _root_.GlobalTheory.CellAmp.pairMaj γ b p :=
  congrArg (fun M => _root_.Formalism.FourierDecayAlt.B.gN M ^ (-b))
    (inv_mul_conj_mul_cancel (of p.1.1) (of p.1.2) (of p.2.2) (of p.2.1) γ a hγ ha)

theorem gap_exists (k r : ℕ) (hk : 1 ≤ k) : ∃ h : ℝ, Formalism.FourierDecayAlt.ThreeDimData.GapOK k r h ∧ GapCell k r h := by
  have hs : 0 < 8 * Real.sqrt (2 * ((r : ℝ) + 1)) := by positivity
  have ht : Filter.Tendsto (fun h : ℝ => Formalism.FourierDecayAlt.ThreeDimData.aOf r h) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.atTop_div_const hs
  obtain ⟨h, h1, h2, h3, h4⟩ := ((Filter.eventually_ge_atTop (120 * ((2 * r + k + 1 : ℕ) : ℝ) ^ 3)).and
    ((ht.eventually_ge_atTop _).and ((ht.eventually_ge_atTop _).and (ht.eventually_ge_atTop _)))).exists
  exact ⟨h, ⟨hk, h1, h2, h3⟩, h4⟩

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.CellAmp.Model.ell_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) : _root_.Formalism.QuantumDeterminants.ell k r z 1 = 0 := by
  unfold _root_.Formalism.QuantumDeterminants.ell
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro he
    have := congrArg Fin.val he
    simp [_root_.Formalism.QuantumDeterminants.eI] at this
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl (by simp [_root_.Formalism.QuantumDeterminants.eI]))

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.CellAmp.Model.cellData_open {k r : ℕ} (L : _root_.Formalism.MainNotions.S.LocBessel k r) (μG : Measure (_root_.Formalism.QuantumDeterminants.Mt k r))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) (hinv : g⁻¹ * g = 1)
    (hG : 0 < _root_.Formalism.QuantumDeterminants.Gf k r L.z L.z' g) (hm : _root_.Formalism.FourierDecayAlt.C2.IsMonomial (_root_.Formalism.QuantumDeterminants.Zhat k r L.z L.z' g))
    (hR : _root_.Formalism.MainNotions.S.RStab k r g = {1}) :
    _root_.GlobalTheory.CellAmp.CellData L μG g (Measure.dirac (fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j)) μG (_root_.Formalism.MainNotions.S.pairMeas L) := by
  have hone : (of fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j) = 1 := rfl
  refine ⟨hg, hG, hm, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hR, Set.mem_singleton_iff] at ha
    subst ha
    rw [Matrix.mul_one, hinv]
    unfold _root_.Formalism.QuantumDeterminants.psi
    rw [_root_.GlobalTheory.CellAmp.Model.ell_one _ _ _ L.hz.1, _root_.GlobalTheory.CellAmp.Model.ell_one _ _ _ L.hz'.1]
  · refine ⟨inferInstance, Measure.dirac_ne_zero, ?_, ?_⟩
    · rw [hR, Measure.dirac_apply]
      simp only [Set.mem_singleton_iff, Set.indicator_apply, Set.mem_setOf_eq]
      rw [hone]
      simp
    · intro s hs
      rw [hR, Set.mem_singleton_iff] at hs
      subst hs
      have hid : _root_.Formalism.QuantumDeterminants.lmulM (k := k) (r := r) 1 = id := funext fun x => by
        unfold _root_.Formalism.QuantumDeterminants.lmulM
        rw [Matrix.one_mul]
        rfl
      rw [hid, Measure.map_id]
  · intro f hf
    have hstab : ∀ x, _root_.Formalism.MainNotions.S.stabAct g (of fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j) x = x := by
      intro x
      unfold _root_.Formalism.MainNotions.S.stabAct
      rw [hone, Matrix.one_mul, Matrix.mul_one, hinv, Matrix.one_mul]
      rfl
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, hstab]
  · intro f hf
    rw [Measure.map_congr (ae_eq_dirac _)]
    erw [Measure.map_const]
    rw [measure_univ, one_smul]
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, hone, Matrix.mul_one, hinv, hone, Matrix.one_mul]
    rfl

theorem nset_zero (k : ℕ) : Nset k 0 = {1} := Formalism.FourierDecayAlt.P.unipotent_haar_base_case k

theorem cellData_exists {k : ℕ} (hk : 1 ≤ k) (L : LocBessel k 0) (μG : Measure (Mt k 0)) :
    ∃ g μR νR ν, CellData L μG g μR νR ν := by
  obtain ⟨μs, -, hμ⟩ := Formalism.FourierDecayAlt.P.SettingConstruction.sectionExists k 0 L.z L.z' hk L.hz.1 L.hz'.1 L.hz.2 L.hz'.2
  set τ := Tz k 0 L.z * Tz k 0 L.z' with hτ
  have hτ0 : 0 < τ := mul_pos L.hz.2 L.hz'.2
  set ζ : ℂ := ((τ + 1 : ℝ) : ℂ) with hζ
  have hn : τ < Complex.normSq ζ := by
    rw [hζ, Complex.normSq_ofReal]; nlinarith
  obtain ⟨hU, hz⟩ := hμ ζ hn
  let c : Fin 0 → ℂ := fun a => a.elim0
  have hmem := bigCellMem k 0 c (μs ζ) (fun a => a.elim0) hU
  have hZ := bigCellZhat k 0 L.z L.z' c (μs ζ) L.hz.1 L.hz'.1
  rw [Formalism.FourierDecayAlt.P.BigCellHermitian.herm_bigCell _ _ L.hz.1 L.hz'.1, hz] at hZ
  have hinv : (bigCell k 0 c (μs ζ))⁻¹ * bigCell k 0 c (μs ζ) = 1 := by
    apply Matrix.nonsing_inv_mul
    have h := congrArg Matrix.det (show (bigCell k 0 c (μs ζ))ᴴ * Hpk k 0 * bigCell k 0 c (μs ζ) = Hpk k 0 from hmem)
    have hH : (Hpk k 0).det ≠ 0 := by
      have h2 := congrArg Matrix.det (hpkFacts k 0).2.1
      rw [Matrix.det_mul, Matrix.det_one] at h2
      intro h0; rw [h0] at h2; simp at h2
    rw [Matrix.det_mul, Matrix.det_mul] at h
    refine isUnit_iff_ne_zero.2 fun h0 => hH ?_
    rw [← h, h0, mul_zero]
  refine ⟨_, _, _, _, cellData_open L μG _ hmem hinv ?_ ?_ ?_⟩
  · unfold Gf Dmin
    rw [hZ]
    have e1 : ((Matrix.diagonal fun a : Fin (0 + 1) => if h : a.val < 0 then c ⟨a.val, h⟩ else ζ).submatrix
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last (0 + 1)).isLt))
        (Fin.castLE (Nat.le_of_lt_succ (Fin.last (0 + 1)).isLt))).det = ζ := by
      have : Unique (Fin (Fin.last (0 + 1)).val) := inferInstanceAs (Unique (Fin 1))
      rw [Matrix.det_unique]; simp
    rw [e1]
    have : IsEmpty (Fin (⟨0, by omega⟩ : Fin (0 + 2)).val) := inferInstanceAs (IsEmpty (Fin 0))
    rw [Matrix.det_isEmpty]
    simp only [map_one, mul_one]
    linarith
  · refine ⟨1, fun _ => ζ, fun _ h0 => ?_, ?_⟩
    · have h0' : ζ = 0 := h0
      rw [h0'] at hn; simp at hn; linarith
    · rw [hZ]; ext i j
      have : i = j := Subsingleton.elim (α := Fin 1) i j
      subst this
      simp [Formalism.FourierDecayAlt.C2.monoP]
  · ext a
    simp only [RStab, nset_zero, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, by rw [mul_one, hinv]⟩

end GlobalTheory.CellAmp.Model

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.GaussMean

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

def qEps {n : ℕ} (ε : Fin n → Bool) (y : Fin n → ℂ) : ℝ := ∑ i, (if ε i then 1 else -1) * ‖y i‖ ^ 2

def gauss {n : ℕ} (y : Fin n → ℂ) : ℝ := Real.exp (-∑ i, ‖y i‖ ^ 2)

def gaussDens {n : ℕ} (ε : Fin n → Bool) (β : ℝ) : ℝ :=
  deriv (fun t : ℝ => ∫ y in {y : Fin n → ℂ | qEps ε y ≤ t}, gauss y) β

def sgn (R : Type) [Ring R] (s : Bool) : R := if s then 1 else -1

def gaussSum (I : AutInst) (β : I.E) (x : I.GA) : ENNReal :=
  ∑' y : {y : Fin I.n → I.E // y ∈ lamX I x ∧ star y ⬝ᵥ (I.J *ᵥ y) = β},
    ENNReal.ofReal (∏ v, gauss (((uMat (x.1 v))⁻¹ * (I.P v)⁻¹) *ᵥ fun i => I.φ v (y.1 i)))

def meanConst (E : Type) [Field E] [NumberField E] [StarRing E] (M : ℕ) : ℝ :=
  (2 * Formalism.HermitianLatticesTheory.vInv E) ^ ((Formalism.HermitianLatticesTheory.fDeg E : ℝ) / 2) * (Formalism.HermitianLatticesTheory.vInv E ^ (M * Formalism.HermitianLatticesTheory.fDeg E))⁻¹ /
    Formalism.HermitianLatticesTheory.lValEta E M

def SiegelMean : Prop :=
  ∀ (I : AutInst), 3 ≤ I.n → ∀ (s : Bool) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
    (fund : Set I.GA), I.IsFundDom (I.muA μf) fund →
    I.muA μf fund < ⊤ ∧
    ∫⁻ x in fund, gaussSum I (sgn I.E s) x ∂(I.muA μf) =
      I.muA μf fund * ENNReal.ofReal (meanConst I.E I.n * ∏ v, gaussDens (I.ε v) (sgn ℝ s))

def IsPerpInst (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E)
    (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf) : Prop :=
  (∀ y, e (star y) = star (e y)) ∧ I'.n + 1 = I.n ∧ star x ⬝ᵥ (I.J *ᵥ x) = sgn I.E s ∧
    star x ᵥ* (I.J * A) = 0 ∧ Aᴴ * I.J * A = I'.J.map e ∧ x ∈ lamX I (1, xf) ∧
    ∀ y : Fin I'.n → I'.E, y ∈ I'.L ↔ A *ᵥ (fun i => e (y i)) ∈ lamX I (1, xf)

def GaugeUnfold : Prop :=
  ∀ (I I' : AutInst) (e : I'.E ≃+* I.E) (s : Bool) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E)
    (xf : I.Gf), 3 ≤ I.n → IsPerpInst I I' e s x A xf →
    ∀ (c : InfinitePlace I.F → ℝ) (μf : Measure I.Gf) [SigmaFinite μf] [μf.IsHaarMeasure]
      (c' : InfinitePlace I'.F → ℝ) (μf' : Measure I'.Gf) [SigmaFinite μf'] [μf'.IsHaarMeasure]
      (fund : Set I.GA), IsGaugeAll I c → IsGaugeAll I' c' → I.IsFundDom (I.muA μf) fund →
      ENNReal.ofReal (∏ v, c v) * (∫⁻ g in fund, gaussSum I (sgn I.E s) g ∂(I.muA μf)) / μf I.Kset =
        gaugeVol I' c' μf' * ENNReal.ofReal (2 ^ (I.n * I.f) * ∏ v, gaussDens (I.ε v) (sgn ℝ s))

theorem gauss_pos {n : ℕ} (y : Fin n → ℂ) : 0 < gauss y := Real.exp_pos _

example : qEps (fun _ : Fin 1 => true) (fun _ => 1) = 1 := by simp [qEps]

end GlobalTheory.GaussMean
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsFundOne
section
noncomputable section
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped Pointwise ENNReal Classical
namespace GlobalTheory.DegVol
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def IsReal (H : HermSpace K V) (k r : ℕ) (σ : K →+* ℂ) (Φ : V → Fin (2 * r + k + 1) → ℂ) : Prop :=
  (∀ x y, Φ (x + y) = Φ x + Φ y) ∧ (∀ (c : K) x, Φ (c • x) = σ c • Φ x) ∧
    (∀ x y, herm (Hpk k r) (Φ x) (Φ y) = σ (H.B x y)) ∧ Submodule.span ℂ (Set.range Φ) = ⊤

def IsFrameOf {H : HermSpace K V} {r : ℕ} (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ)
    (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r) : Prop :=
  IsReal H k r σ Φ ∧ inWb k r z ∧ inWb k r z' ∧ 0 < Tz k r z ∧ (∃ c : ℂ, IsNormal0 k r N.j_le β c z z' g) ∧
    (∀ a : Fin r, Φ (N.F.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a) ∧
      g *ᵥ Φ (N.F'.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • bvec (eI k r a)) ∧
    (∀ b : Fin r, N.j ≤ b.val → Φ (N.ist b) = (((ρ ^ (r - b.val))⁻¹ : ℝ) : ℂ) • bvec (esI k r b)) ∧
    Φ N.F.z = z' ∧ g *ᵥ Φ N.F'.z = z

def IsPlaces {ι : Type} (σ : ι → (K →+* ℂ)) : Prop :=
  (∀ v a, σ v (star a) = starRingEnd ℂ (σ v a)) ∧ ∀ w : InfinitePlace K, ∃! v, InfinitePlace.mk (σ v) = w

def realPts {ι : Type} {k r : ℕ} (Φ : ι → V → Fin (2 * r + k + 1) → ℂ) (Γ : Set (V ≃ₗ[K] V)) : Set (ι → Mt k r) :=
  {m | ∃ s ∈ Γ, ∀ v x, Matrix.of (m v) *ᵥ Φ v x = Φ v (s x)}

def mulP {ι : Type} {k r : ℕ} (m x : ι → Mt k r) : ι → Mt k r := fun v => lmulM (Matrix.of (m v)) (x v)

def IsFund {ι : Type} {k r : ℕ} (Γ R Ω : Set (ι → Mt k r)) : Prop :=
  MeasurableSet Ω ∧ ∀ x ∈ R, ∃! m, m ∈ Γ ∧ mulP m x ∈ Ω

def RP {ι : Type} (k r : ℕ) (g : ι → Mat k r) : Set (ι → Mt k r) := {x | ∀ v, Matrix.of (x v) ∈ Rset k r (g v)}

end GlobalTheory.DegVol
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
section
open MeasureTheory NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.FlagBase

open Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

def IsAdapted (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (xf : I.Gf) {a : ℕ} (j : Fin a → ℕ)
    (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (Λ : ∀ i, Submodule (𝓞 I.E) (Fin (j i) → I.E))
    (x₀ : I₀.Gf) (T T' : ∀ i, Matrix (Fin I.n) (Fin (j i)) I.E) (T₀ : Matrix (Fin I.n) (Fin I₀.n) I.E) : Prop :=
  (∀ y, e (star y) = star (e y)) ∧ I.n = I₀.n + 2 * ∑ i, j i ∧ (∀ i, Submodule.IsLattice I.E (Λ i)) ∧
    (∀ i k, (T i)ᴴ * I.J * T k = 0 ∧ (T' i)ᴴ * I.J * T' k = 0 ∧ (i ≠ k → (T i)ᴴ * I.J * T' k = 0)) ∧
    (∀ i, (T i)ᴴ * I.J * T' i = 1 ∧ (T i)ᴴ * I.J * T₀ = 0 ∧ (T' i)ᴴ * I.J * T₀ = 0) ∧
    T₀ᴴ * I.J * T₀ = I₀.J.map e ∧
    (∀ z, z ∈ lamX I (1, xf) ↔ ∃ (u u' : ∀ i, Fin (j i) → I.E) (y : Fin I₀.n → I₀.E), (∀ i, u i ∈ Λ i) ∧
      (∀ i, ∀ t ∈ Λ i, star t ⬝ᵥ u' i ∈ (algebraMap (𝓞 I.E) I.E).range) ∧ y ∈ lamX I₀ (1, x₀) ∧
      z = ∑ i, T i *ᵥ u i + ∑ i, T' i *ᵥ u' i + T₀ *ᵥ fun l => e (y l)) ∧
    ∀ k z, z ∈ S k ↔ ∃ u : ∀ i, Fin (j i) → I.E, (∀ i, u i ∈ Λ i) ∧ (∀ i : Fin a, ¬ i.castSucc < k → u i = 0) ∧
      z = ∑ i, T i *ᵥ u i

def latGroup (I : AutInst) (xf : I.Gf) : Set I.Ginf :=
  {g | ∃ γ ∈ I.GFset, γ.1 = g ∧ xf⁻¹ * γ.2 * xf ∈ I.Kset}

def flagGroup (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set I.Ginf :=
  {g | g ∈ latGroup I xf ∧ ∀ v k, ∀ y ∈ flagAt I S v k, uMat (g v) *ᵥ y ∈ flagAt I S v k}

def leviGroup (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) :
    Set I.Ginf :=
  {m | (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) ∧
    ∃ g ∈ flagGroup I xf S, ∃ u : I.Ginf, (∀ v, u v ∈ flagN (I.ε v) (flagAt I S v)) ∧ g = u * m}

def sizesAt (I : AutInst) (xf : I.Gf) {a : ℕ} (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E))
    (g : I.Ginf) : Fin a → ℝ :=
  fun i => Formalism.HN.sizeQ (bas I) (frm I (g, xf)) (S i.succ) (S i.castSucc)

def slabVol (E : Type) [Field E] [NumberField E] (j : ℕ) (Λ : Submodule (𝓞 E) (Fin j → E)) : ENNReal :=
  covol (autGL E j Λ) (haarGL E j) {x | 1 ≤ detNorm E j x ∧ detNorm E j x < Real.exp 1}

section Mean

variable (E : Type) [Field E] [NumberField E] (j : ℕ)

abbrev VecInf : Type := InfinitePlace E → Fin j → ℂ

def latAt (Λ : Submodule (𝓞 E) (Fin j → E)) (g : MatInf E j) : Submodule ℤ (VecInf E j) :=
  Submodule.span ℤ ((fun (y : Fin j → E) (w : InfinitePlace E) =>
    (Matrix.of (g w))⁻¹ *ᵥ fun a => w.embedding (y a)) '' (Λ : Set (Fin j → E)))

def dualAt (L : Submodule ℤ (VecInf E j)) : Submodule ℤ (VecInf E j) :=
  Submodule.span ℤ {y | ∀ x ∈ L, ∃ z : ℤ, ∑ w, (x w ⬝ᵥ y w).re = z}

def latMean (F : Submodule ℤ (VecInf E j) → ENNReal) : ENNReal :=
  ∑' c : Quot (fun Λ Λ' : {Λ : Submodule (𝓞 E) (Fin j → E) // Submodule.IsLattice E Λ} =>
      ∃ γ : GL (Fin j) E, ∀ y, (γ : Matrix (Fin j) (Fin j) E) *ᵥ y ∈ Λ'.1 ↔ y ∈ Λ.1),
    covol (autGL E j (Quot.out c).1) ((haarGL E j).withDensity fun g => F (latAt E j (Quot.out c).1 g))
      {g | 0 < detNorm E j g}

def IsLatMeasurable (F : Submodule ℤ (VecInf E j) → ENNReal) : Prop :=
  ∀ Λ : Submodule (𝓞 E) (Fin j → E), Submodule.IsLattice E Λ → Measurable fun g : MatInf E j => F (latAt E j Λ g)

def covAt (L : Submodule ℤ (VecInf E j)) : ℝ := ZLattice.covolume L volume

def gaussV (x : VecInf E j) : ℝ := Real.exp (-Real.pi * ∑ w, ∑ a, ‖x w a‖ ^ 2)

end Mean

end GlobalTheory.FlagBase
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocDecOfDecGap
section
open MeasureTheory NumberField Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace

namespace GlobalTheory.Dec

theorem locDec_of_decOp (hD : DecOp) (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ) (hB : IsDSData B d)
    (hg : GapGe B h) (hh : ∀ v, 8 * (B.I.n : ℝ) * rkR (B.I.ε v) < h) : LocDec B h := by
  intro v g
  obtain ⟨h1, h2, h3, -⟩ := hB v
  simpa [h3.1] using hD _ _ _ _ _ h1 h2 h (hg v) (hh v) (uMat g) g.2 _ h3.2 _ h3.2

theorem locDec_of_decGap (hD : GlobalTheory.DSId.DecGap) (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : ℝ)
    (hB : IsDSData B d) (hg : GapGe B h)
    (hh : ∀ v, 120 * (B.I.n : ℝ) * ((rkR (B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h) : LocDec B h := by
  intro v g
  obtain ⟨h1, h2, h3, -⟩ := hB v
  simpa [h3.1] using (hD _ _ _ _ _ h1 h2 h (hg v) (hh v) (uMat g) g.2 _ h3.2 _ h3.2).2

end GlobalTheory.Dec
end

