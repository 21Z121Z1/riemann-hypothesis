import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0435
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0411
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0382
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0398
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.LocalBaseChange.ElementaryCosets.JPred
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqOneOfLowerParab
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0426
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0437
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0438
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RealFirstNilpotent
section
noncomputable section

open Finset
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD

namespace GlobalTheory.CompanionTheory.HarmCone

variable {n : ℕ}

def sg (lev : Fin n → ℕ) (a b : Fin n) : ℝ :=
  (if lev a < lev b then 1 else 0) - (if lev b < lev a then 1 else 0)

theorem two_rhoU (lev : Fin n → ℕ) (a : Fin n) : 2 * rhoU lev a = ∑ b, sg lev a b := by
  simp only [rhoU, sg, Finset.sum_sub_distrib, Finset.sum_boole]
  ring

theorem sg_anti (lev : Fin n → ℕ) (a b : Fin n) : sg lev a b = - sg lev b a := by
  unfold sg
  ring

theorem sg_cases (lev : Fin n → ℕ) (a b : Fin n) :
    sg lev a b = 1 ∨ sg lev a b = 0 ∨ sg lev a b = -1 := by
  unfold sg
  split_ifs <;> norm_num

theorem mul_sg_self (lev : Fin n → ℕ) (a b : Fin n) :
    ((lev a : ℝ) - lev b) * sg lev a b = -|(lev a : ℝ) - lev b| := by
  rcases lt_trichotomy (lev a) (lev b) with h | h | h
  · have h' : (lev a : ℝ) < lev b := by exact_mod_cast h
    have hs : sg lev a b = 1 := by
      unfold sg
      rw [if_pos h, if_neg (by omega)]
      norm_num
    rw [hs, abs_of_neg (by linarith)]
    ring
  · have hs : sg lev a b = 0 := by
      unfold sg
      rw [if_neg (by omega), if_neg (by omega)]
      norm_num
    rw [hs, h]
    simp
  · have h' : (lev b : ℝ) < lev a := by exact_mod_cast h
    have hs : sg lev a b = -1 := by
      unfold sg
      rw [if_neg (by omega), if_pos h]
      norm_num
    rw [hs, abs_of_pos (by linarith)]
    ring

theorem neg_abs_le_mul_sg (lev : Fin n → ℕ) (x : ℝ) (a b : Fin n) : -|x| ≤ x * sg lev a b := by
  have h1 := neg_abs_le x
  have h2 := le_abs_self x
  have h3 := abs_nonneg x
  rcases sg_cases lev a b with h | h | h <;> rw [h] <;> linarith

theorem pair_root (f : Fin n → ℝ) (a b : Fin n) :
    ∑ x, f x * ((if x = a then 1 else 0) - (if x = b then 1 else 0)) = f a - f b := by
  simp [mul_sub, Finset.sum_sub_distrib]

def dsg (lev lev' : Fin n → ℕ) (x b : Fin n) : ℝ := sg lev' x b - sg lev x b

theorem dsg_anti (lev lev' : Fin n → ℕ) (x b : Fin n) : dsg lev lev' x b = - dsg lev lev' b x := by
  unfold dsg
  rw [sg_anti lev' x b, sg_anti lev x b]
  ring

theorem dsg_nonneg (lev lev' : Fin n → ℕ) (x b : Fin n) :
    0 ≤ ((lev x : ℝ) - lev b) * dsg lev lev' x b := by
  unfold dsg
  rw [mul_sub, mul_sg_self]
  have := neg_abs_le_mul_sg lev' ((lev x : ℝ) - lev b) x b
  linarith

theorem pairing_nonneg (lev lev' : Fin n → ℕ) :
    0 ≤ ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
  have e1 : ∑ x, ∑ b, (lev x : ℝ) * dsg lev lev' x b = ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    simp only [Finset.mul_sum]
  have e2 : ∑ x, ∑ b, (lev b : ℝ) * dsg lev lev' x b = -∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    rw [Finset.sum_comm, ← e1, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [dsg_anti lev lev' b x]
    ring
  have e3 : ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b
      = 2 * ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b := by
    simp only [sub_mul, Finset.sum_sub_distrib]
    rw [e1, e2]
    ring
  have e4 : 0 ≤ ∑ x, ∑ b, ((lev x : ℝ) - lev b) * dsg lev lev' x b :=
    Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun b _ => dsg_nonneg lev lev' x b
  linarith

theorem harm_cone : N1 := by
  intro n lam _ lev lev' _ _ hc
  obtain ⟨c, hc0, hQ⟩ := hc
  have hQx : ∀ x, (muQ lam lev' - muQ lam lev) x = ∑ b, dsg lev lev' x b := by
    intro x
    simp only [Pi.sub_apply, muQ, dsg, Finset.sum_sub_distrib, ← two_rhoU]
    ring
  have hD : ∑ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b
      = ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b) := by
    have e : ∀ x, (lev x : ℝ) * ∑ b, dsg lev lev' x b = ∑ a, ∑ b, (c a b : ℝ) *
        ((lev x : ℝ) * ((if x = a then 1 else 0) - (if x = b then 1 else 0))) := by
      intro x
      rw [← hQx, hQ x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      ring
    simp only [e]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, pair_root (fun x => (lev x : ℝ)) a b]
  have hterm : ∀ a b, (c a b : ℝ) * ((lev a : ℝ) - lev b) ≤ 0 := by
    intro a b
    by_cases h0 : c a b = 0
    · simp [h0]
    · have h1 : (lev a : ℝ) < lev b := by exact_mod_cast hc0 a b h0
      have h2 : (0 : ℝ) ≤ c a b := Nat.cast_nonneg _
      nlinarith
  have hsum : ∑ a, ∑ b, (c a b : ℝ) * ((lev a : ℝ) - lev b) = 0 :=
    le_antisymm (Finset.sum_nonpos fun a _ => Finset.sum_nonpos fun b _ => hterm a b)
      (hD ▸ pairing_nonneg lev lev')
  have h1 := (Finset.sum_eq_zero_iff_of_nonpos
    (fun a _ => Finset.sum_nonpos fun b _ => hterm a b)).1 hsum
  have hz : ∀ a b, c a b = 0 := by
    intro a b
    by_contra h0
    have h2 := (Finset.sum_eq_zero_iff_of_nonpos (fun b _ => hterm a b)).1
      (h1 a (Finset.mem_univ _)) b (Finset.mem_univ _)
    have h3 : (lev a : ℝ) < lev b := by exact_mod_cast hc0 a b h0
    have h4 : (c a b : ℝ) ≠ 0 := by exact_mod_cast h0
    rcases mul_eq_zero.1 h2 with h | h
    · exact h4 h
    · linarith
  funext x
  have h5 := hQ x
  simp only [hz, Nat.cast_zero, zero_mul, Finset.sum_const_zero] at h5
  exact sub_eq_zero.1 h5

end GlobalTheory.CompanionTheory.HarmCone
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RestrictionBallIndicatorSpan
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.MirLevi
open MeasureTheory GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.Rodier.SmIntEl
open scoped Topology

namespace GlobalTheory.CompanionTheory.ThetaInt

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isOpen_ball (n : ℕ) (s : kˣ) :
    IsOpen {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} :=
  (isOpen_polyBall n s).preimage continuous_ofAdd

theorem isCompact_ball (n : ℕ) (s : kˣ) :
    IsCompact {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} := by
  have e : {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} =
      Multiplicative.toAdd '' (polyBall (k := k) n s : Set (Multiplicative (Fin n → k))) := by
    ext a
    constructor
    · intro h
      exact ⟨Multiplicative.ofAdd a, h, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact hx
  rw [e]
  exact (isCompact_polyBall n s).image continuous_toAdd

theorem isLocallyConstant_of_periodic {n : ℕ} {Y : Type} (g : (Fin n → k) → Y) (s : kˣ)
    (h : ∀ v a : Fin n → k, Multiplicative.ofAdd a ∈ polyBall (k := k) n s → g (v + a) = g v) :
    IsLocallyConstant g := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun x => ?_
  have h0 : (fun z : Fin n → k => -x + z) ⁻¹'
      {a : Fin n → k | Multiplicative.ofAdd a ∈ polyBall (k := k) n s} ∈ 𝓝 x :=
    ((isOpen_ball n s).preimage (by fun_prop)).mem_nhds (by
      show Multiplicative.ofAdd (-x + x) ∈ polyBall (k := k) n s
      rw [neg_add_cancel]
      exact one_mem _)
  filter_upwards [h0] with z hz
  have e : z = x + (-x + z) := by abel
  rw [e]
  exact h x _ hz

theorem hasCompactSupport_of_ball {n : ℕ} {E : Type} [AddCommGroup E] (g : (Fin n → k) → E) (S : kˣ)
    (h : ∀ v, g v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) n S) : HasCompactSupport g := by
  haveI := GlobalTheory.SplitWeil.t2Space k
  refine HasCompactSupport.intro (isCompact_ball n S) fun x hx => ?_
  by_contra h1
  exact hx (h x h1)

def tw (ψ : AddChar k Circle) {N : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]
    (g : (Fin (N + 1) → k) → E) : (Fin (N + 1) → k) → E :=
  fun v => ((ψ (-(v (Fin.last N))) : Circle) : ℂ) • g v

variable {N : ℕ} {E : Type} [AddCommGroup E] [Module ℂ E]

theorem isLocallyConstant_tw (ψ : AddChar k Circle) (hψ : Continuous ψ)
    {g : (Fin (N + 1) → k) → E} (hg : IsLocallyConstant g) : IsLocallyConstant (tw ψ g) := by
  obtain ⟨s, hs⟩ := exists_cball_addChar_eq_one ψ hψ
  have h1 : IsLocallyConstant fun v : Fin (N + 1) → k => ((ψ (-(v (Fin.last N))) : Circle) : ℂ) := by
    refine isLocallyConstant_of_periodic _ s fun v a ha => ?_
    have h2 : ψ (a (Fin.last N)) = 1 := hs _ (ha (Fin.last N))
    rw [Pi.add_apply, neg_add, AddChar.map_add_eq_mul, AddChar.map_neg_eq_inv (a := a (Fin.last N)), h2,
      inv_one, mul_one]
  exact h1.comp₂ hg fun c x => c • x

theorem hasCompactSupport_tw (ψ : AddChar k Circle) {g : (Fin (N + 1) → k) → E} (S : kˣ)
    (h : ∀ v, g v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) :
    HasCompactSupport (tw ψ g) := by
  refine hasCompactSupport_of_ball _ S fun v hv => h v fun h0 => hv ?_
  simp [tw, h0]

section Int

variable [MeasurableSpace k] [BorelSpace k] [SecondCountableTopology k] (ν : Measure k)
  [ν.IsAddHaarMeasure]

theorem smInt_comp_inv_mulVec (g : GL (Fin (N + 1)) k) {φ : (Fin (N + 1) → k) → E}
    (l : IsLocallyConstant φ) :
    smInt (Measure.pi fun _ : Fin (N + 1) => ν) (φ ∘ ((g⁻¹ : GL (Fin (N + 1)) k) :
        Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec) =
      ((nabs k (Matrix.GeneralLinearGroup.det g) : ℝ) : ℂ) •
        smInt (Measure.pi fun _ : Fin (N + 1) => ν) φ := by
  have hm : ∀ B : Matrix (Fin (N + 1)) (Fin (N + 1)) k, Measurable B.mulVec := fun B =>
    (continuous_const.matrix_mulVec continuous_id).measurable
  have key : ∀ B : Set (Fin (N + 1) → k), MeasurableSet B →
      (Measure.pi fun _ : Fin (N + 1) => ν)
          (((g⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec ⁻¹' B) =
        (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ENNReal) *
          (Measure.pi fun _ : Fin (N + 1) => ν) B := by
    intro B hB
    have h1 := GlobalTheory.WeilM.smul_map_mulVec_pi ν g.val (Matrix.GeneralLinearGroup.det g) rfl
    conv_lhs => rw [← h1]
    rw [Measure.smul_apply, Measure.map_apply (hm _) ((hm _) hB), smul_eq_mul]
    congr 2
    ext x
    simp only [Set.mem_preimage, mulVec_mulVec]
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  unfold smInt
  rw [smul_finsum]
  refine finsum_congr fun v => ?_
  rw [Set.preimage_comp, key (φ ⁻¹' {v}) (l.isOpen_fiber v).measurableSet, ENNReal.toReal_mul, smul_smul]
  congr 1
  simp [nabs]

end Int

theorem exists_twisted_integral : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) (X E : Type) [AddCommGroup X] [Module ℂ X] [AddCommGroup E] [Module ℂ E] (r : X →ₗ[ℂ] (Fin (N + 1) → k) → E), (∀ f, ∃ s : kˣ, ∀ (v a : Fin (N + 1) → k), Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → r f (v + a) = r f v) → (∀ f, ∃ S : kˣ, ∀ v : Fin (N + 1) → k, r f v ≠ 0 → Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) S) → ∀ (tr : (Fin (N + 1) → k) → X → X), (∀ a f v, r (tr a f) v = r f (v + a)) → ∀ (lev : GL (Fin (N + 1)) k → X → X) (A : GL (Fin (N + 1)) k → E →ₗ[ℂ] E), (∀ m f v, r (lev m f) v = A m (r f (((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec v))) → ∃ T : X →ₗ[ℂ] E, (∀ a f, T (tr a f) = ((ψ (a (Fin.last N)) : Circle) : ℂ) • T f) ∧ (∀ m : GL (Fin (N + 1)) k, m ∈ Mir k N → ∀ f, T (lev m f) = ((nabs k (Matrix.GeneralLinearGroup.det m) : ℝ) : ℂ) • A m (T f)) ∧ (∀ s : kˣ, (∀ a : Fin (N + 1) → k, Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s → ψ (a (Fin.last N)) = 1) → ∃ c : ℂ, c ≠ 0 ∧ ∀ (b : X) (e : E), (∀ v, r b v = @ite _ (Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s) (Classical.propDecidable _) e 0) → T b = c • e) := by
  intro k _ _ _ _ ψ hψ N X E _ _ _ _ r hper hsup tr htr lev A hlev
  borelize k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  obtain ⟨ν, hν⟩ : ∃ ν : Measure k, ν.IsAddHaarMeasure := ⟨Measure.addHaar, inferInstance⟩
  let μ : Measure (Fin (N + 1) → k) := Measure.pi fun _ => ν
  haveI hμ : μ.IsAddHaarMeasure := Measure.pi.isAddHaarMeasure _
  have hl : ∀ f, IsLocallyConstant (tw ψ (r f)) := fun f => by
    obtain ⟨s, hs⟩ := hper f
    exact isLocallyConstant_tw ψ hψ (isLocallyConstant_of_periodic _ s fun v a ha => hs v a ha)
  have hc : ∀ f, HasCompactSupport (tw ψ (r f)) := fun f => by
    obtain ⟨S, hS⟩ := hsup f
    exact hasCompactSupport_tw ψ S hS
  let T : X →ₗ[ℂ] E :=
    { toFun := fun f => smInt μ (tw ψ (r f))
      map_add' := fun f g => by
        have e : tw ψ (r (f + g)) = tw ψ (r f) + tw ψ (r g) := by
          funext v
          simp [tw, map_add, smul_add]
        show smInt μ (tw ψ (r (f + g))) = smInt μ (tw ψ (r f)) + smInt μ (tw ψ (r g))
        rw [e, smInt_add μ (hl f) (hc f) (hl g) (hc g)]
      map_smul' := fun c f => by
        have e : tw ψ (r (c • f)) = (c • LinearMap.id : E →ₗ[ℂ] E) ∘ tw ψ (r f) := by
          funext v
          simp only [tw, Function.comp, map_smul, Pi.smul_apply, LinearMap.smul_apply, LinearMap.id_apply]
        show smInt μ (tw ψ (r (c • f))) = c • smInt μ (tw ψ (r f))
        rw [e, smInt_linear μ _ (hl f) (hc f)]
        rfl }
  have hT : ∀ f, T f = smInt μ (tw ψ (r f)) := fun _ => rfl
  refine ⟨T, ?_, ?_, ?_⟩
  · intro a f
    let L : E →ₗ[ℂ] E := ((ψ (a (Fin.last N)) : Circle) : ℂ) • LinearMap.id
    have e : tw ψ (r (tr a f)) = (L ∘ tw ψ (r f)) ∘ fun v => v + a := by
      funext v
      simp only [tw, Function.comp, htr, L, LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
      congr 1
      rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 2
      simp only [Pi.add_apply]
      abel
    rw [hT, hT, e, smInt_comp_measurePreserving μ (measurePreserving_add_right μ a) ((hl f).comp _),
      smInt_linear μ L (hl f) (hc f)]
    rfl
  · intro m hm f
    have e : tw ψ (r (lev m f)) = (A m ∘ tw ψ (r f)) ∘
        ((m⁻¹ : GL (Fin (N + 1)) k) : Matrix (Fin (N + 1)) (Fin (N + 1)) k).mulVec := by
      funext v
      simp only [tw, Function.comp, hlev, map_smul]
      rw [mulVec_last_of_mem k _ (inv_mem hm) v]
    rw [hT, hT, e]
    refine (smInt_comp_inv_mulVec ν m ((hl f).comp _)).trans ?_
    congr 1
    exact smInt_linear μ (A m) (hl f) (hc f)
  · intro s hs
    have hLo := isOpen_ball (k := k) (N + 1) s
    have hLc := isCompact_ball (k := k) (N + 1) s
    refine ⟨(((μ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s}).toReal : ℝ) : ℂ), ?_, fun b e hb => ?_⟩
    · have h0 := (hLo.measure_pos μ ⟨0, one_mem (polyBall (k := k) (N + 1) s)⟩).ne'
      exact Complex.ofReal_ne_zero.2 (ENNReal.toReal_ne_zero.2 ⟨h0, hLc.measure_lt_top.ne⟩)
    · have e' : tw ψ (r b) = Set.indicator {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} fun _ => e := by
        funext v
        by_cases hv : Multiplicative.ofAdd v ∈ polyBall (k := k) (N + 1) s
        · have h1 : ψ (v (Fin.last N)) = 1 := hs v hv
          simp only [tw]
          rw [hb v, if_pos hv, Set.indicator_of_mem (show v ∈ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} from hv),
            AddChar.map_neg_eq_inv, h1]
          simp
        · simp only [tw]
          rw [hb v, if_neg hv, Set.indicator_of_notMem (show v ∉ {a | Multiplicative.ofAdd a ∈ polyBall (k := k) (N + 1) s} from hv),
            smul_zero]
      rw [hT, e', smInt_indicator]

end GlobalTheory.CompanionTheory.ThetaInt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentDualPrecedesIff
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

namespace GlobalTheory.CompanionTheory.SegDualPrec

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section

variable (hc : ∀ x : IrrGL k, x.IsCusp → (dualCl x).IsCusp)

include hc

theorem segDual_eq (Δ : Segment k) : segDual Δ =
    Segment.ofFirst ((dualCl Δ.first).nu (1 - (Δ.len : ℂ))) ((hc _ Δ.isCusp_first).nu _) Δ.len Δ.len_pos :=
  dif_pos (hc _ Δ.isCusp_first)

theorem first_segDual (Δ : Segment k) : (segDual Δ).first = (dualCl Δ.first).nu (1 - (Δ.len : ℂ)) := by
  rw [segDual_eq hc]; rfl

theorem len_segDual (Δ : Segment k) : (segDual Δ).len = Δ.len := by
  rw [segDual_eq hc]; rfl

variable (hn : ∀ (x : IrrGL k) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s))

include hn

theorem carrier_segDual (Δ : Segment k) : (segDual Δ).carrier = dualCl '' Δ.carrier := by
  ext x
  simp only [Set.mem_image, Segment.mem_carrier, first_segDual hc, len_segDual hc, IrrGL.nu_nu]
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨_, ⟨Δ.len - 1 - a, by omega, rfl⟩, ?_⟩
    rw [hn]
    congr 1
    have h1 : a + 1 ≤ Δ.len := ha
    have h2 : ((Δ.len - 1 - a : ℕ) : ℂ) = (Δ.len : ℂ) - 1 - a := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [h2]
    ring
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    refine ⟨Δ.len - 1 - b, by omega, ?_⟩
    rw [hn]
    congr 1
    have h1 : b + 1 ≤ Δ.len := hb
    have h2 : ((Δ.len - 1 - b : ℕ) : ℂ) = (Δ.len : ℂ) - 1 - b := by
      rw [Nat.sub_sub, Nat.cast_sub (by omega)]
      push_cast
      ring
    rw [h2]
    ring

variable (hd : ∀ x : IrrGL k, dualCl (dualCl x) = x)

include hd

theorem dualCl_injective : Function.Injective (dualCl : IrrGL k → IrrGL k) :=
  Function.LeftInverse.injective hd

theorem segDual_segDual (Δ : Segment k) : segDual (segDual Δ) = Δ := by
  refine Segment.ext_first ?_ (by rw [len_segDual hc, len_segDual hc])
  rw [first_segDual hc, first_segDual hc, len_segDual hc, hn, hd, IrrGL.nu_nu]
  simp

theorem linked_segDual {Δ Δ' : Segment k} (h : Δ.Linked Δ') : (segDual Δ).Linked (segDual Δ') := by
  obtain ⟨⟨Γ, hΓ⟩, h1, h2⟩ := h
  have hi := dualCl_injective hc hn hd
  refine ⟨⟨segDual Γ, ?_⟩, ?_, ?_⟩
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, carrier_segDual hc hn, hΓ, Set.image_union]
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, Set.image_subset_image_iff hi]
    exact h1
  · rw [carrier_segDual hc hn, carrier_segDual hc hn, Set.image_subset_image_iff hi]
    exact h2

theorem precedes_segDual {Δ Δ' : Segment k} (h : Δ'.Precedes Δ) : (segDual Δ).Precedes (segDual Δ') := by
  obtain ⟨hl, j, hj, hf⟩ := h
  refine ⟨linked_segDual hc hn hd hl.symm, ?_⟩
  have hlen : Δ'.len < j + Δ.len := by
    by_contra hle
    refine hl.2.2 fun x hx => ?_
    obtain ⟨a, ha, rfl⟩ := Segment.mem_carrier.1 hx
    refine Segment.mem_carrier.2 ⟨j + a, by omega, ?_⟩
    rw [hf, IrrGL.nu_nu]
    push_cast
    rfl
  refine ⟨j + Δ.len - Δ'.len, by omega, ?_⟩
  rw [first_segDual hc, first_segDual hc, hf, hn, IrrGL.nu_nu, IrrGL.nu_nu]
  congr 1
  rw [Nat.cast_sub hlen.le]
  push_cast
  ring

theorem segDual_precedes_iff (Δ Δ' : Segment k) : (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := by
  refine ⟨fun h => ?_, precedes_segDual hc hn hd⟩
  have := precedes_segDual hc hn hd h
  rwa [segDual_segDual hc hn hd, segDual_segDual hc hn hd] at this

end

theorem segDual_precedes : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (Δ Δ' : Segment k),
    (segDual Δ).Precedes (segDual Δ') ↔ Δ'.Precedes Δ := fun hA Δ Δ' =>
  segDual_precedes_iff (fun x hx => (GlobalTheory.T.dual_class_cuspidal hA x hx).1) (GlobalTheory.T.dual_class_twist_neg hA) (GlobalTheory.T.dual_class_involutive hA) Δ Δ'

end GlobalTheory.CompanionTheory.SegDualPrec
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriFirstIdentity
section
open GlobalTheory.PRep GlobalTheory.SmGL ValuativeRel PositivityTheory.Lbc

namespace GlobalTheory.CompanionTheory.Lbc.Contraction

theorem e1 : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], PositivityTheory.Lbc.E1 k := by
  intro k _ _ _ _ N J θ l t hA hT g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := hg
  have hθJ : J.map θ.toMonoidHom = J := hA.2.2.2.2.2.2.1
  have hθa : θ a ∈ J := by
    rw [← hθJ]
    exact Subgroup.mem_map_of_mem _ ha
  obtain ⟨j₁, hj₁, n, hn, τ, hτ, h₁⟩ :=
    GlobalTheory.CompanionTheory.LbcKillN.killN N J θ l t hA hT (b * θ a) (J.mul_mem hb hθa)
  obtain ⟨j₂, hj₂, κ, hκ, h₂⟩ := GlobalTheory.CompanionTheory.Lbc.KillNlo.killNlo N J θ l t hA hT n hn τ hτ
  refine ⟨(a * j₁ * j₂)⁻¹, J.inv_mem (J.mul_mem (J.mul_mem ha hj₁) hj₂), κ, hκ, ?_⟩
  rw [← h₂, ← h₁]
  simp only [inv_inv, map_inv, map_mul]
  group

end GlobalTheory.CompanionTheory.Lbc.Contraction
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedJacquetIteratedPhiEquivStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_jacquet_iterated_phi_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle) (n j : ℕ) (τ : MRep k (n + j)), Nonempty (TwJacquet (iterPhi k ψ j τ).ρ (MirUin k n) 1 ≃ₗ[ℂ] TwJacquet τ.ρ (derUnipM k (n + j) n) (derCharM k ψ (n + j) n)) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv | exact GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv | (intros; apply GlobalTheory.CompanionTheory.BZMir.iterPhi_twJacquet_equiv <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedTraceWeylCharacterStatement
section
open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_trace_weyl_character : ∀ {n : ℕ} (lam : Fin n → ℤ) (E : KMod n) (T : E.V →L[ℂ] E.V), IsLefK lam E T → ∀ (k : Matrix.unitaryGroup (Fin n) ℂ) (z : Fin n → ℂ), k.1 = diagonal z → Function.Injective (fun a => z a ^ 2) → LinearMap.trace ℂ (E.V →L[ℂ] ℂ) (dualT E (E.ρ k⁻¹ * T) : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = (∏ a, ∏ b, (1 + z a / z b)) * weylChar lam (fun a => z a ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv | exact GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv | (intros; apply GlobalTheory.CompanionTheory.RealCountG.LefDual.trace_dualT_inv <;> assumption)
end

