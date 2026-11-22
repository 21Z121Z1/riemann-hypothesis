import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0446
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0234
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0008
import Development.WeilBound.ThetaLifts.LatticeBasics.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0462

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RtMulApply
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter BoundedContinuousFunction
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.LFun Formalism.UG Formalism.L2.Host
open PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.SmoReg

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

theorem Rt_mul_apply (g h : GA E a) (φ : XB E a) : Rt E a (g * h) φ = Rt E a g (Rt E a h φ) := by
  rw [map_mul]; rfl

theorem polyBd_repI [IsTotallyComplex E] : PolyBd (repI E a) :=
  ⟨1, 0, zero_le_one, fun g x => by
    have : ‖repI E a g x‖ = ‖x‖ := norm_Rt _ _
    simp [this]⟩

theorem conj_stab {G H X : Type} [Group G] [Group H] [TopologicalSpace H] [ContinuousMul H]
    (f : H →* G) (c : G →* H) (R : G → X → X) (hR : ∀ g h x, R (g * h) x = R g (R h x))
    (hf : ∀ u, c (f u) = u) (hcomm : ∀ g, c g = 1 → ∀ u, g * f u = f u * g)
    (g : G) (x : X) (hx : {u : H | R (f u) x = x} ∈ 𝓝 (1 : H)) :
    {u : H | R (f u) (R g x) = R g x} ∈ 𝓝 (1 : H) := by
  obtain ⟨k, hk⟩ : ∃ k, k = c g := ⟨_, rfl⟩
  have hg1 : c ((f k)⁻¹ * g) = 1 := by rw [map_mul, map_inv, hf, ← hk, inv_mul_cancel]
  have hcont : Continuous fun u : H => k⁻¹ * u * k :=
    (continuous_const.mul continuous_id).mul continuous_const
  have hat : Tendsto (fun u : H => k⁻¹ * u * k) (𝓝 1) (𝓝 1) := by
    have := hcont.tendsto 1
    simpa using this
  filter_upwards [hat hx] with u hu
  have key : f u * g = g * f (k⁻¹ * u * k) := by
    have h := hcomm _ hg1 (k⁻¹ * u * k)
    have e : f (k⁻¹ * u * k) = (f k)⁻¹ * f u * f k := by simp only [map_mul, map_inv]
    rw [e] at h ⊢
    have h2 := congrArg (f k * ·) h
    simpa only [mul_assoc, mul_inv_cancel_left] using h2.symm
  have hu' : R (f (k⁻¹ * u * k)) x = x := hu
  change R (f u) (R g x) = R g x
  rw [← hR, key, hR, hu']

theorem lev_Rt [IsTotallyComplex E] (hfl : ∀ (w : Pl E) (u : GL (Fin a) (w.adicCompletion E)),
      cLoc w (fl a w u : GA E a) = u)
    (hcomm : ∀ (w : Pl E) (g : GA E a), cLoc w g = 1 → ∀ u, g * fl a w u = fl a w u * g)
    (S : Finset (Pl E)) (g : GA E a) (φ : XB E a) (hφ : Lev S φ) : Lev S (Rt E a g φ) := by
  intro w hw
  have hx := hφ w hw
  simp only [repW_apply] at hx ⊢
  exact conj_stab (fl a w) (cLoc w) (fun g x => Rt E a g x) Rt_mul_apply (hfl w) (hcomm w) g φ hx

theorem g5b : S2 → G0 → G5b := by
  intro hS2 hG0 E _ _ _ a S
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hG0 E a
  obtain ⟨-, -, -, hgrp, hT, -⟩ := hS2 _ a (XB E a) (repI E a) polyBd_repI
  refine ⟨?_, fun g φ hφ => lev_Rt h4 h8 S g φ hφ, ?_, ?_, ?_⟩
  · intro g φ hφ
    set y := cInf g with hy
    set gf : GA E a := (infGL E a y)⁻¹ * g with hgf
    have hgf1 : cInf gf = 1 := by
      rw [hgf, map_mul, map_inv, h1, ← hy, inv_mul_cancel]
    have hg : g = infGL E a y * gf := by rw [hgf, mul_inv_cancel_left]
    have hc : ∀ (z : GL (Fin a) (Cinf E)) (x : XB E a),
        Rt E a gf (repI E a z x) = repI E a z (Rt E a gf x) := by
      intro z x
      change Rt E a gf (Rt E a (infGL E a z) x) = Rt E a (infGL E a z) (Rt E a gf x)
      rw [← Rt_mul_apply, ← Rt_mul_apply, h7 gf hgf1 z]
    have := hgrp y _ (hT (Rt E a gf) hc φ hφ)
    have e : Rt E a g φ = repI E a y (Rt E a gf φ) := by
      change Rt E a g φ = Rt E a (infGL E a y) (Rt E a gf φ)
      rw [← Rt_mul_apply, ← hg]
    rw [e]
    exact this
  · intro c φ hφ w hw
    filter_upwards [hφ w hw] with u hu
    have hu' : repW a w u φ = φ := hu
    change repW a w u (c • φ) = c • φ
    rw [map_smul, hu']
  · intro φ φ' hφ hφ' w hw
    filter_upwards [hφ w hw, hφ' w hw] with u hu hu'
    have e : repW a w u φ = φ := hu
    have e' : repW a w u φ' = φ' := hu'
    change repW a w u (φ + φ') = φ + φ'
    rw [map_add, e, e']
  · intro w hw
    filter_upwards with u
    change repW a w u 0 = 0
    rw [map_zero]

end GlobalTheory.CompanionTheory.SmoReg

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SetIntegralInvMulVec
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair

theorem setIntegral_inv_mulVec {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k)
    [ν.IsAddHaarMeasure] (m : ℕ) (g : GL (Fin m) k) (M : Set (Fin m → k))
    (F : (Fin m → k) → ℂ) :
    ∫ x in M, F (((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ x) ∂(piHaar ν m) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) *
        ∫ y in {y | (g : Matrix (Fin m) (Fin m) k) *ᵥ y ∈ M}, F y ∂(piHaar ν m) := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  have hinv : ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) * (g : Matrix (Fin m) (Fin m) k) = 1 :=
    Units.inv_mul g
  have hinv' : (g : Matrix (Fin m) (Fin m) k) * ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = 1 :=
    Units.mul_inv g
  let e : (Fin m → k) ≃ᵐ (Fin m → k) :=
    { toFun := fun x => (g : Matrix (Fin m) (Fin m) k) *ᵥ x
      invFun := fun x => ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) *ᵥ x
      left_inv := fun x => by simp only [mulVec_mulVec, hinv, one_mulVec]
      right_inv := fun x => by simp only [mulVec_mulVec, hinv', one_mulVec]
      measurable_toFun := (continuous_const.matrix_mulVec continuous_id).measurable
      measurable_invFun := (continuous_const.matrix_mulVec continuous_id).measurable }
  have he : MeasurableEmbedding (Matrix.mulVec (g : Matrix (Fin m) (Fin m) k)) :=
    e.measurableEmbedding
  have hμ := GlobalTheory.UnipChange.smul_map_mulVec_pi ν (g : Matrix (Fin m) (Fin m) k)
    (Matrix.GeneralLinearGroup.det g) (Matrix.GeneralLinearGroup.val_det_apply g)
  unfold GlobalTheory.CompanionTheory.MirPair.piHaar GlobalTheory.SplitWeil.nabs
  conv_lhs => rw [← hμ]
  rw [Measure.restrict_smul, integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul,
    he.restrict_map, he.integral_map]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [mulVec_mulVec, hinv, one_mulVec]

end GlobalTheory.CompanionTheory.MirPair
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearOrbitFinite
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.ShearOrbit

variable {k : Type} [Field k]

theorem shear_mul_inv (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    (1 + vecMulVec (eLast k n) b) * (1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (eLast k n) b) = 1 := by
  have hd : b ⬝ᵥ GlobalTheory.BZMir.eLast k n = b (Fin.last n) := by
    simp [GlobalTheory.BZMir.eLast, dotProduct_single]
  have hM : vecMulVec (GlobalTheory.BZMir.eLast k n) b * vecMulVec (GlobalTheory.BZMir.eLast k n) b =
      b (Fin.last n) • vecMulVec (GlobalTheory.BZMir.eLast k n) b := by
    rw [vecMulVec_mul_vecMulVec, hd]
    ext i j
    simp only [vecMulVec_apply, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  have hc : (1 + b (Fin.last n))⁻¹ + (1 + b (Fin.last n))⁻¹ * b (Fin.last n) = 1 := by
    rw [← mul_one_add]
    exact inv_mul_cancel₀ hb
  rw [mul_sub, mul_one, mul_smul_comm, add_mul, one_mul, hM, smul_add, smul_smul, ← add_smul, hc,
    one_smul, add_sub_cancel_right]

theorem shearGL_val (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (eLast k n) b := by
  have h := GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shear_mul_inv n b hb
  have hu : IsUnit (1 + vecMulVec (GlobalTheory.BZMir.eLast k n) b) :=
    ⟨⟨_, _, h, mul_eq_one_comm.mp h⟩, rfl⟩
  rw [GlobalTheory.CompanionTheory.MirPair.shearGL, dif_pos hu]
  exact hu.unit_spec

theorem shearGL_inv_val (n : ℕ) (b : Fin (n + 1) → k) (hb : 1 + b (Fin.last n) ≠ 0) :
    (((shearGL n b)⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 - (1 + b (Fin.last n))⁻¹ • vecMulVec (eLast k n) b :=
  Units.inv_eq_of_mul_eq_one_right (by rw [shearGL_val n b hb]; exact shear_mul_inv n b hb)

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem one_add_ne_zero_of_mem_box (n : ℕ) {r : kˣ} (hr : valuation k (r : k) < 1) {b : Fin (n + 1) → k}
    (hb : b ∈ box (n + 1) r) : 1 + b (Fin.last n) ≠ 0 := by
  intro h
  have h1 : valuation k (b (Fin.last n)) ≤ valuation k (r : k) := hb (Fin.last n)
  have h2 : b (Fin.last n) = -1 := by linear_combination h
  rw [h2, Valuation.map_neg, map_one] at h1
  exact absurd hr (not_lt.mpr h1)

theorem continuous_shearGL (n : ℕ) {r : kˣ} (hr : valuation k (r : k) < 1) :
    Continuous fun b : (box (n + 1) r : Set (Fin (n + 1) → k)) => shearGL n b.1 := by
  have hne : ∀ b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)), 1 + b.1 (Fin.last n) ≠ 0 :=
    fun b => GlobalTheory.CompanionTheory.MirPair.ShearOrbit.one_add_ne_zero_of_mem_box n hr b.2
  have hv : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      vecMulVec (GlobalTheory.BZMir.eLast k n) b.1 :=
    continuous_matrix fun i j => by
      simp only [vecMulVec_apply]
      exact continuous_const.mul ((continuous_apply j).comp continuous_subtype_val)
  rw [Units.continuous_iff]
  constructor
  · exact (continuous_const.add hv).congr fun b => (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shearGL_val n b.1 (hne b)).symm
  · have hinv : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
        (1 + b.1 (Fin.last n))⁻¹ :=
      (continuous_const.add ((continuous_apply _).comp continuous_subtype_val)).inv₀ hne
    exact (continuous_const.sub (hinv.smul hv)).congr fun b => (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.shearGL_inv_val n b.1 (hne b)).symm

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in

theorem continuous_levi (m : ℕ) : Continuous (levi k m) := by
  have hmat : Continuous (GlobalTheory.BZMir.glEmbHom k m) := by
    apply continuous_matrix
    intro i j
    induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
      simp [GlobalTheory.BZMir.glEmbHom, GlobalTheory.BZMir.glEmbMat] <;>
      first
        | exact continuous_const
        | exact continuous_id.matrix_elem _ _
        | fun_prop
  have hGL : Continuous (GlobalTheory.BZMir.glEmb k m) := Continuous.units_map _ hmat
  exact continuous_induced_rng.2 hGL

theorem isOpen_orbit_fiber {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v w : V) :
    IsOpen {p : Mir k (n + 1) | T p v = w} := by
  rw [isOpen_iff_mem_nhds]
  intro p hp
  have hS : IsOpen {g : GlobalTheory.BZMir.Mir k (n + 1) | T g v = v} := hT v
  have hcont : Continuous fun g : GlobalTheory.BZMir.Mir k (n + 1) => p⁻¹ * g := continuous_const.mul continuous_id
  have hmem : (fun g : GlobalTheory.BZMir.Mir k (n + 1) => p⁻¹ * g) ⁻¹' {g | T g v = v} ∈ 𝓝 p := by
    apply hcont.continuousAt.preimage_mem_nhds
    apply hS.mem_nhds
    simp
  filter_upwards [hmem] with g hg
  have hg' : T (p⁻¹ * g) v = v := hg
  have hsplit : T g = T p * T (p⁻¹ * g) := by
    rw [← map_mul, mul_inv_cancel_left]
  show T g v = w
  rw [hsplit, Module.End.mul_apply, hg']
  exact hp

theorem shear_orbit_finite {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : Representation ℂ (Mir k (n + 1)) V) (hT : IsSmooth T) (v : V) (r : kˣ)
    (hr : valuation k (r : k) < 1) :
    ((fun b => T (levi k (n + 1) (shearGL n b)) v) '' (box (n + 1) r : Set (Fin (n + 1) → k))).Finite := by
  haveI : CompactSpace (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) :=
    isCompact_iff_compactSpace.mp (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.isCompact_box (n + 1) r)
  have hc : Continuous fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b.1) :=
    (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.continuous_levi (n + 1)).comp (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.continuous_shearGL n hr)
  have hlc : IsLocallyConstant fun b : (GlobalTheory.CompanionTheory.BZOnto.PerpSmall.box (n + 1) r : Set (Fin (n + 1) → k)) =>
      T (GlobalTheory.BZMir.levi k (n + 1) (GlobalTheory.CompanionTheory.MirPair.shearGL n b.1)) v := by
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro w
    exact (GlobalTheory.CompanionTheory.MirPair.ShearOrbit.isOpen_orbit_fiber T hT v w).preimage hc
  rw [Set.image_eq_range]
  exact hlc.range_finite

end GlobalTheory.CompanionTheory.MirPair.ShearOrbit

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShearPreservesBoxMembership
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

namespace GlobalTheory.CompanionTheory.MirPair.ShearLat

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dotProduct_eLast {n : ℕ} (b : Fin (n + 1) → k) : b ⬝ᵥ eLast k n = b (Fin.last n) := by
  simp [eLast, dotProduct_single]

theorem isUnit_one_add {n : ℕ} (b : Fin (n + 1) → k) (h : 1 + b (Fin.last n) ≠ 0) :
    IsUnit (1 + vecMulVec (eLast k n) b) := by
  rw [Matrix.isUnit_iff_isUnit_det, vecMulVec_eq (ι := Unit),
    det_one_add_replicateCol_mul_replicateRow, dotProduct_eLast]
  exact h.isUnit

theorem shearGL_mulVec {n : ℕ} (b : Fin (n + 1) → k) (h : 1 + b (Fin.last n) ≠ 0)
    (x : Fin (n + 1) → k) :
    ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x =
      x + (b ⬝ᵥ x) • eLast k n := by
  have e : ((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) =
      1 + vecMulVec (eLast k n) b := by
    unfold shearGL
    rw [dif_pos (isUnit_one_add b h)]
    rfl
  rw [e, add_mulVec, one_mulVec, vecMulVec_mulVec, op_smul_eq_smul]

theorem dotProduct_shear {n : ℕ} (b x : Fin (n + 1) → k) :
    b ⬝ᵥ (x + (b ⬝ᵥ x) • eLast k n) = (1 + b (Fin.last n)) * (b ⬝ᵥ x) := by
  rw [dotProduct_add, dotProduct_smul, dotProduct_eLast, smul_eq_mul]
  ring

theorem exists_bound {n : ℕ} (g : GL (Fin (n + 1)) k) :
    ∃ C : kˣ, 1 ≤ valuation k (C : k) ∧
      (∀ i, valuation k (((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i) ≤ valuation k (C : k)) ∧
      ∀ i j, valuation k (((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j) ≤
        valuation k (C : k) := by
  let f : Option (Fin (n + 1) ⊕ Fin (n + 1) × Fin (n + 1)) → k := fun o =>
    match o with
    | none => 1
    | some (.inl i) => ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i
    | some (.inr p) => ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) p.1 p.2
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max fun o => valuation k (f o)
  have h1 : 1 ≤ valuation k (f i₀) := by simpa [f] using hi₀ none
  have hne : f i₀ ≠ 0 := by
    intro h
    rw [h, map_zero] at h1
    exact absurd h1 (by simp)
  exact ⟨Units.mk0 _ hne, h1, fun i => hi₀ (some (.inl i)), fun i j => hi₀ (some (.inr (i, j)))⟩

theorem mul_mem_cball {a u : k} {p C t : kˣ} (hp : valuation k (p : k) ≤ 1)
    (ha : a ∈ cball (p * C⁻¹ * t)) (hu : valuation k u ≤ valuation k (C : k)) : a * u ∈ cball t := by
  have ha' : valuation k a ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) := ha
  show valuation k (a * u) ≤ valuation k (t : k)
  calc valuation k (a * u) = valuation k a * valuation k u := map_mul _ _ _
    _ ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) * valuation k (C : k) := mul_le_mul' ha' hu
    _ = valuation k (p : k) * valuation k (t : k) := by
        rw [← map_mul, ← map_mul]
        congr 1
        simp only [Units.val_mul, Units.val_inv_eq_inv_val]
        field_simp
    _ ≤ valuation k (t : k) := mul_le_of_le_one_left' hp

theorem main : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ} (g : GL (Fin (n + 1)) k), ∃ r : kˣ, valuation k (r : k) < 1 ∧ ∀ b ∈ box (n + 1) r, ∀ (t : kˣ) (x : Fin (n + 1) → k), ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (((shearGL n b : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) ∈ box (n + 1) t ↔ (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x ∈ box (n + 1) t) := by
  intro k _ _ _ _ n g
  obtain ⟨C, hC1, hu, hH⟩ := exists_bound g
  obtain ⟨p₀, hp0, hp1⟩ : ∃ p : k, p ≠ 0 ∧ valuation k p < 1 := Valuation.IsNontrivial.exists_lt_one
  obtain ⟨p, rfl⟩ : ∃ p : kˣ, (p : k) = p₀ := ⟨Units.mk0 _ hp0, rfl⟩
  have hCi : valuation k ((C⁻¹ : kˣ) : k) ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_le_one_of_one_le₀ hC1
  have hr1 : valuation k ((p * C⁻¹ * C⁻¹ : kˣ) : k) < 1 := by
    simp only [Units.val_mul, map_mul]
    exact lt_of_le_of_lt ((mul_le_of_le_one_right' hCi).trans (mul_le_of_le_one_right' hCi)) hp1
  refine ⟨p * C⁻¹ * C⁻¹, hr1, fun b hb t x => ?_⟩
  have hlast : valuation k (b (Fin.last n)) < 1 := lt_of_le_of_lt (hb (Fin.last n)) hr1
  have hone : valuation k (1 + b (Fin.last n)) = 1 := Valuation.map_one_add_of_lt _ hlast
  have hne : 1 + b (Fin.last n) ≠ 0 := by
    intro h
    rw [h, map_zero] at hone
    exact zero_ne_one hone
  rw [shearGL_mulVec b hne x]
  have hGS : (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ (x + (b ⬝ᵥ x) • eLast k n) =
      (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x +
        (b ⬝ᵥ x) • ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) := by
    rw [mulVec_add, mulVec_smul]
  have hd : ∀ z : Fin (n + 1) → k, b ⬝ᵥ z =
      (b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ⬝ᵥ
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z) := by
    intro z
    rw [dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one]
  have hw : b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) ∈
      box (n + 1) (p * C⁻¹) := by
    intro j
    change ∑ i, b i * ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i j ∈ cball (p * C⁻¹)
    refine Finset.sum_induction _ (· ∈ cball (p * C⁻¹)) (fun _ _ => add_mem_cball) (by simp [cball]) fun i _ => ?_
    have h1 : valuation k (b i) ≤ valuation k ((p * C⁻¹ * C⁻¹ : kˣ) : k) := hb i
    show valuation k (b i * _) ≤ valuation k ((p * C⁻¹ : kˣ) : k)
    rw [map_mul]
    refine (mul_le_mul' h1 (hH i j)).trans (le_of_eq ?_)
    rw [← map_mul]
    congr 1
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp
  have hdot : ∀ y ∈ box (n + 1) t,
      (b ᵥ* ((g⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) ⬝ᵥ y ∈
        cball (p * C⁻¹ * t) := by
    intro y hy
    refine dotProduct_mem_cball (s := t) ?_ hy
    rwa [mul_inv_cancel_right]
  have hp : valuation k (p : k) ≤ 1 := hp1.le
  constructor
  · intro h i
    have h2 : (1 + b (Fin.last n)) * (b ⬝ᵥ x) ∈ cball (p * C⁻¹ * t) := by
      rw [← dotProduct_shear, hd (x + (b ⬝ᵥ x) • eLast k n)]
      exact hdot _ h
    have h3 : b ⬝ᵥ x ∈ cball (p * C⁻¹ * t) := by
      have h2' : valuation k ((1 + b (Fin.last n)) * (b ⬝ᵥ x)) ≤ valuation k ((p * C⁻¹ * t : kˣ) : k) := h2
      rw [map_mul, hone, one_mul] at h2'
      exact h2'
    rw [hGS] at h
    have e : ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x) i =
        ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ x +
          (b ⬝ᵥ x) • ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n)) i +
        -((b ⬝ᵥ x) * ((g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ eLast k n) i) := by
      simp
    rw [e]
    exact add_mem_cball (h i) (neg_mem_cball (mul_mem_cball hp h3 (hu i)))
  · intro h i
    have h3 : b ⬝ᵥ x ∈ cball (p * C⁻¹ * t) := by
      rw [hd x]
      exact hdot _ h
    rw [hGS]
    exact add_mem_cball (h i) (mul_mem_cball hp h3 (hu i))

end GlobalTheory.CompanionTheory.MirPair.ShearLat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothVectorFixedParabolicNearOneStatement
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_vector_fixed_parabolic_near_one : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ)
    (v : τ.V ⊗[ℂ] σ.V), ∃ O ∈ 𝓝 (1 : Mir k ((i + 1) + t + 1)), ∀ a : HPG k (i + 1) (t + 1),
      (a : Mir k ((i + 1) + (t + 1))) ∈ O → sigX τ σ a v = v := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sigX_fix_nhds <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SphericalAlmostEverywhereOfBounded
section
noncomputable section

open NumberField IsDedekindDomain Filter GlobalTheory.CuspRep GlobalTheory.LFun Formalism.L2.Host PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.StrongMultOne

theorem spherical_almost_everywhere_of_bounded : G1 → AlmostEverywhereSpherical := by
  intro g1 E _ _ _ a π hN φ hφ x hx
  have hex : ∀ v : π.V, ∃ y : XB E a, (y : GA E a → ℂ) = v.1.1 := fun v =>
    (g1 E a π hN v.1 v.2).imp fun _ h => h.1
  choose f hf using hex
  let ι : π.V →ₗ[ℂ] XB E a :=
    { toFun := f
      map_add' := fun u v => by
        refine DFunLike.coe_injective ?_
        rw [BoundedContinuousFunction.coe_add, hf, hf, hf]
        rfl
      map_smul' := fun c v => by
        refine DFunLike.coe_injective ?_
        funext g
        rw [hf]
        change _ = c • f v g
        rw [congrFun (hf v) g]
        rfl }
  have hι : ∀ v, (ι v : GA E a → ℂ) = v.1.1 := hf
  filter_upwards [AeFix.eventually_mem_fixed E a π ⟨φ, hφ⟩] with w hw B hB
  by_cases h0 : x = 0
  · exact Or.inl h0
  refine Or.inr ?_
  have hxι : ι ⟨φ, hφ⟩ = x := DFunLike.coe_injective ((hι _).trans hx.symm)
  have hne : (⟨φ, hφ⟩ : π.V) ≠ 0 := fun e => h0 (by rw [← hxι, e, map_zero])
  have hsat : IsSatVecGL w (π.locRep w) ⟨φ, hφ⟩ B := hB.2 _ hw hne
  have hint : ∀ g y, ι (π.locRep w g y) = repW a w g (ι y) := fun g y => by
    refine DFunLike.coe_injective ?_
    funext h
    rw [hι]
    change _ = (ι y) (h * fl a w g)
    have := congrFun (hι y) (h * fl a w g)
    rw [this]
    rfl
  have := hsat.map ι hint (by rw [hxι]; exact h0)
  rwa [hxι] at this

end GlobalTheory.CompanionTheory.StrongMultOne

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreDerivativeLieActionStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_centre_derivative_lie_action : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (φ : Sm E a) (g : GA E a) (s : ℝ), HasDerivAt (fun s : ℝ => φ.1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) ((lie E a (oneL E a) φ).1 (g * GlobalTheory.UnitaryBC.splitCentre E a s)) s := by
  first | exact @GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre | exact GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre | (intros; apply GlobalTheory.CompanionTheory.CuspFinDeriv.hasDerivAt_splitCentre <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitCentreTranslatePreservesCuspSpaceStatement
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_centre_translate_preserves_cusp_space : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (Kinf E a) W) (J : Set (Module.End ℂ (Sm E a))), J ⊆ Zalg E a → ∀ φ : Sm E a, φ ∈ genSpace L ρ J → IsCuspidal φ.1 → ∀ t : ℝ, rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ ∈ genSpace L ρ J ∧ IsCuspidal (rt E a (GlobalTheory.UnitaryBC.splitCentre E a t) φ).1 := by
  first | exact @GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem | exact GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem | (intros; apply GlobalTheory.CompanionTheory.CuspFinGL.Transl.rt_splitCentre_mem <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactEntriesIntegralStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_compact_entries_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (Y : Spc F E n) (B : Base F E) (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)),
    IsStdK (σ := σ) (Y := Y) B b K → ∀ k ∈ K, ∀ (v : Pl F) (i j : Fin n ⊕ Fin n), absFin F v (compFin F E v (inFrame b k i j)) ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one | exact GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one | (intros; apply GlobalTheory.CompanionTheory.GodementH.StdInt.absFin_inFrame_le_one <;> assumption)
end

