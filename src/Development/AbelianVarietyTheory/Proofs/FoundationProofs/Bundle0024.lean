import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsEisensteinSlashNeOutsideGamma
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

noncomputable section

namespace GlobalTheory.EisSep

open EisensteinSeries Complex

def pt (n : ℕ) : ℍ := UpperHalfPlane.mk (((n : ℂ) + 1) * Complex.I) (by simp; positivity)

theorem coe_pt (n : ℕ) : ((pt n : ℍ) : ℂ) = ((n : ℂ) + 1) * Complex.I := rfl

def lim0 (v : Fin 2 → ℤ) : ℂ := if v 0 = 0 then (v 1 : ℂ) ^ (-3 : ℤ) else 0

theorem re_im_summand (v : Fin 2 → ℤ) (n : ℕ) :
    ((v 0 : ℂ) * (pt n : ℂ) + v 1).re = v 1 ∧ ((v 0 : ℂ) * (pt n : ℂ) + v 1).im = v 0 * ((n : ℝ) + 1) := by
  rw [coe_pt]; constructor <;> simp

theorem norm_le (v : Fin 2 → ℤ) (n : ℕ) : ‖eisSummand 3 v (pt n)‖ ≤ ‖v‖ ^ (-(3 : ℝ)) := by
  obtain ⟨hre, him⟩ := re_im_summand v n
  set w : ℂ := (v 0 : ℂ) * (pt n : ℂ) + v 1 with hw
  have hvw : ‖v‖ ≤ ‖w‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
    fin_cases i
    · have h1 := Complex.abs_im_le_norm w
      rw [him, abs_mul] at h1
      have h2 : |(v 0 : ℝ)| ≤ |(v 0 : ℝ)| * |(n : ℝ) + 1| := by
        have : (1 : ℝ) ≤ |(n : ℝ) + 1| := by rw [abs_of_pos (by positivity)]; simp
        nlinarith [abs_nonneg (v 0 : ℝ)]
      simp only [Int.norm_eq_abs]
      simpa using h2.trans h1
    · have h1 := Complex.abs_re_le_norm w
      rw [hre] at h1
      simpa [Int.norm_eq_abs] using h1
  have he : eisSummand 3 v (pt n) = w ^ (-3 : ℤ) := rfl
  rw [he, norm_zpow, Real.rpow_neg (norm_nonneg _), zpow_neg]
  rcases (norm_nonneg v).eq_or_lt with h0 | h0
  · have : v = 0 := norm_eq_zero.1 h0.symm
    have hw0 : w = 0 := by simp [hw, this]
    simp [hw0]
  · rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, zpow_ofNat]
    exact inv_anti₀ (pow_pos h0 _) (pow_le_pow_left₀ h0.le hvw _)

theorem tendsto_term (v : Fin 2 → ℤ) : Tendsto (fun n => eisSummand 3 v (pt n)) atTop (𝓝 (lim0 v)) := by
  by_cases h : v 0 = 0
  · have : ∀ n, eisSummand 3 v (pt n) = (v 1 : ℂ) ^ (-3 : ℤ) := fun n => by simp [eisSummand, h]
    simp only [this, lim0, h, if_true]
    exact tendsto_const_nhds
  · simp only [lim0, h, if_false]
    refine squeeze_zero_norm (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    obtain ⟨_, him⟩ := re_im_summand v n
    set w : ℂ := (v 0 : ℂ) * (pt n : ℂ) + v 1
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by simp
    have hw : (n : ℝ) + 1 ≤ ‖w‖ := by
      have h1 := Complex.abs_im_le_norm w
      rw [him, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 1)] at h1
      have : (1 : ℝ) ≤ |(v 0 : ℝ)| := by exact_mod_cast Int.one_le_abs h
      nlinarith
    have he : eisSummand 3 v (pt n) = w ^ (-3 : ℤ) := rfl
    rw [he, norm_zpow, zpow_neg, one_div]
    have hw1 : (1 : ℝ) ≤ ‖w‖ := hn.trans hw
    have : ‖w‖ ≤ ‖w‖ ^ (3 : ℤ) := by
      rw [zpow_ofNat]; nlinarith [mul_le_mul hw1 hw1 zero_le_one (by linarith)]
    exact inv_anti₀ (by positivity) (hw.trans this)

theorem tendsto_eis {M : ℕ} (c : Fin 2 → ZMod M) :
    Tendsto (fun n => eisensteinSeries c 3 (pt n)) atTop (𝓝 (∑' v : gammaSet M 1 c, lim0 v)) :=
  tendsto_tsum_of_dominated_convergence (bound := fun v : gammaSet M 1 c => ‖v.1‖ ^ (-(3 : ℝ)))
    ((summable_one_div_norm_rpow (by norm_num)).subtype _) (fun v => tendsto_term v.1)
    (Eventually.of_forall fun n v => norm_le v.1 n)

theorem eq_of_zero {M : ℕ} {c : Fin 2 → ZMod M} {v : Fin 2 → ℤ} (hv : v ∈ gammaSet M 1 c) (h0 : v 0 = 0) :
    v = ![0, 1] ∨ v = ![0, -1] := by
  have h := hv.2
  rw [h0, Int.gcd_zero_left, Int.natAbs_eq_iff] at h
  rcases h with h | h
  · left; ext i; fin_cases i <;> simp [h0, h]
  · right; ext i; fin_cases i <;> simp [h0, h]

theorem cast_zero_one (M : ℕ) : ((↑) : ℤ → ZMod M) ∘ (![0, 1] : Fin 2 → ℤ) = ![0, 1] := by
  ext i; fin_cases i <;> simp

theorem lim_one {M : ℕ} (hM : 3 ≤ M) : ∑' v : gammaSet M 1 (![0, 1] : Fin 2 → ZMod M), lim0 v = 1 := by
  haveI : Fact (2 < M) := ⟨by omega⟩
  have hm : (![0, 1] : Fin 2 → ℤ) ∈ gammaSet M 1 (![0, 1] : Fin 2 → ZMod M) := ⟨cast_zero_one M, by simp⟩
  rw [tsum_eq_single ⟨_, hm⟩]
  · simp [lim0]
  · intro v hv
    by_contra hne
    have h0 : v.1 0 = 0 := by by_contra h; simp [lim0, h] at hne
    rcases eq_of_zero v.2 h0 with h | h
    · exact hv (Subtype.ext h)
    · have h1 := congrFun v.2.1 1
      rw [h] at h1
      exact ZMod.neg_one_ne_one (n := M) (by simpa using h1)

theorem lim_ne {M : ℕ} {c : Fin 2 → ZMod M} (hc : c ≠ ![0, 1]) : ∑' v : gammaSet M 1 c, lim0 v ≠ 1 := by
  have key : ∀ v : gammaSet M 1 c, v.1 ≠ ![0, -1] → lim0 v = 0 := by
    intro v hv
    by_contra hne
    have h0 : v.1 0 = 0 := by by_contra h; simp [lim0, h] at hne
    rcases eq_of_zero v.2 h0 with h | h
    · exact hc (by rw [← v.2.1, h, cast_zero_one])
    · exact hv h
  by_cases hm : (![0, -1] : Fin 2 → ℤ) ∈ gammaSet M 1 c
  · rw [tsum_eq_single ⟨_, hm⟩ fun v hv => key v fun h => hv (Subtype.ext h)]
    simp only [lim0]
    norm_num
  · rw [tsum_congr fun v => key v fun h => hm (h ▸ v.2)]
    simp

theorem eq_of_eis_eq {M : ℕ} (hM : 3 ≤ M) {c : Fin 2 → ZMod M}
    (h : eisensteinSeries c 3 = eisensteinSeries (![0, 1] : Fin 2 → ZMod M) 3) : c = ![0, 1] := by
  by_contra hc
  have h1 := tendsto_eis c
  rw [h] at h1
  exact lim_ne hc ((tendsto_nhds_unique h1 (tendsto_eis _)).trans (lim_one hM))

theorem exists_isMF_slash_ne : ∀ M : ℕ, 3 ≤ M → ∀ x : SL(2, ℤ), x ∉ CongruenceSubgroup.Gamma M →
    ∃ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f ∧ f ∣[k] x ≠ f := by
  intro M hM x hx
  haveI : NeZero M := ⟨by omega⟩
  have hMF : ∀ a : Fin 2 → ZMod M, IsMF (CongruenceSubgroup.Gamma M) 3 (eisensteinSeries a 3) := fun a =>
    isMF_coe (ModularForm.eisensteinSeriesMF le_rfl a)
  rw [CongruenceSubgroup.Gamma_mem] at hx
  by_cases hrow : ((x 1 0 : ℤ) : ZMod M) = 0 ∧ ((x 1 1 : ℤ) : ZMod M) = 1
  · refine ⟨3, _, hMF ![-1, 0], fun h => ?_⟩
    have h2 := congrArg (fun f => f ∣[(3 : ℤ)] ModularGroup.S) h
    simp only [eisensteinSeries_slash_apply] at h2
    have hS0 : ((ModularGroup.S : SL(2, ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = !![0, -1; 1, 0] := by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, ModularGroup.coe_S]
      ext i j; fin_cases i <;> fin_cases j <;> simp
    have hS : Matrix.vecMul (![-1, 0] : Fin 2 → ZMod M) ((ModularGroup.S : SL(2, ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) = ![0, 1] := by
      rw [hS0]; ext i; fin_cases i <;> simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    rw [hS, hS0] at h2
    have h3 := eq_of_eis_eq hM h2
    have h30 := congrFun h3 0
    have h31 := congrFun h3 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h30 h31
    exact hx ⟨h31, h30, hrow⟩
  · refine ⟨3, _, hMF ![0, 1], fun h => ?_⟩
    rw [eisensteinSeries_slash_apply] at h
    have h3 := eq_of_eis_eq hM h
    have h30 := congrFun h3 0
    have h31 := congrFun h3 1
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two] at h30 h31
    exact hrow ⟨h30, h31⟩

end GlobalTheory.EisSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsExtensionOfDense
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem exists_extension_of_dense {X₀ X M : Type} [AddCommGroup X₀] [AddCommGroup X]
    [AddCommGroup M] [Module ℂ M] (ι : X₀ →+ X) (A : AddSubgroup X) (β : X → X → ℂ)
    (W₀ : X₀ → M →ₗ[ℂ] M)
    (hl : ∀ x y z, β (x + y) z = β x z * β y z)
    (hr : ∀ x y z, β x (y + z) = β x y * β x z)
    (hA : ∀ a ∈ A, ∀ b ∈ A, β a b = 1)
    (hβ : ∀ x, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ A, β x (m • a) = 1 ∧ β (m • a) x = 1)
    (hW : ∀ x y v, W₀ x (W₀ y v) = β (ι x) (ι y) • W₀ (x + y) v)
    (hd : ∀ (x : X) (m : ℕ), 0 < m → ∃ z, ∃ a ∈ A, ι z = x + m • a)
    (hs : ∀ v, ∃ m : ℕ, 0 < m ∧ ∀ z, (∃ a ∈ A, ι z = m • a) → W₀ z v = v) :
    ∃ W : X → M →ₗ[ℂ] M, (∀ z, W (ι z) = W₀ z) ∧
      (∀ x y v, W x (W y v) = β x y • W (x + y) v) ∧
      ∀ x v, ∃ m : ℕ, 0 < m ∧ ∀ a ∈ A, W (x + m • a) v = W x v := by
  choose b hb0 hb using hβ
  have hb' : ∀ x (n : ℕ), b x ∣ n → ∀ a ∈ A, β x (n • a) = 1 ∧ β (n • a) x = 1 := by
    rintro x n ⟨k, rfl⟩ a ha
    rw [mul_smul]
    exact hb x _ (A.nsmul_mem ha k)
  have hex : ∀ (x : X) (v : M), ∃ G : M, ∃ m : ℕ, 0 < m ∧
      ∀ n : ℕ, m ∣ n → ∀ z, ∀ a ∈ A, ι z = x + n • a → W₀ z v = G := by
    intro x v
    obtain ⟨m, hm0, hm⟩ := hs v
    obtain ⟨z₁, a₁, ha₁, hz₁⟩ := hd x (m * b x) (Nat.mul_pos hm0 (hb0 x))
    refine ⟨W₀ z₁ v, m * b x, Nat.mul_pos hm0 (hb0 x), ?_⟩
    rintro n ⟨k, rfl⟩ z a ha hz
    rw [mul_smul] at hz
    have ha' : k • a ∈ A := A.nsmul_mem ha k
    have hsub : a₁ - k • a ∈ A := A.sub_mem ha₁ ha'
    have hιd : ι (z₁ - z) = (m * b x) • (a₁ - k • a) := by
      rw [map_sub, hz₁, hz, smul_sub]; abel
    have h1 : W₀ (z₁ - z) v = v :=
      hm _ ⟨b x • (a₁ - k • a), A.nsmul_mem hsub _, by rw [hιd, mul_smul]⟩
    have h2 := hW z (z₁ - z) v
    rw [h1, hιd, hz, hl, (hb' x _ (Dvd.intro_left m rfl) _ hsub).1,
      hA _ (A.nsmul_mem ha' _) _ (A.nsmul_mem hsub _), add_sub_cancel] at h2
    simpa using h2
  choose val lev hlev0 hlev using hex
  refine ⟨fun x =>
    { toFun := val x
      map_add' := ?_
      map_smul' := ?_ }, ?_, ?_, ?_⟩
  · intro v w
    obtain ⟨z, a, ha, hz⟩ := hd x (lev x v * lev x w * lev x (v + w))
      (Nat.mul_pos (Nat.mul_pos (hlev0 _ _) (hlev0 _ _)) (hlev0 _ _))
    rw [← hlev x v _ ⟨lev x w * lev x (v + w), by ring⟩ z a ha hz,
      ← hlev x w _ ⟨lev x v * lev x (v + w), by ring⟩ z a ha hz,
      ← hlev x (v + w) _ ⟨lev x v * lev x w, by ring⟩ z a ha hz, map_add]
  · intro c v
    obtain ⟨z, a, ha, hz⟩ := hd x (lev x v * lev x (c • v))
      (Nat.mul_pos (hlev0 _ _) (hlev0 _ _))
    rw [← hlev x v _ ⟨lev x (c • v), by ring⟩ z a ha hz,
      ← hlev x (c • v) _ ⟨lev x v, by ring⟩ z a ha hz, map_smul, RingHom.id_apply]
  · intro z
    ext v
    exact (hlev (ι z) v _ dvd_rfl z 0 A.zero_mem (by simp)).symm
  · intro x y v
    change val x (val y v) = β x y • val (x + y) v
    obtain ⟨n, hn0, h1, h2, h3, h4, h5⟩ : ∃ n : ℕ, 0 < n ∧ lev x (val y v) ∣ n ∧ lev y v ∣ n ∧
        lev (x + y) v ∣ n ∧ b x ∣ n ∧ b y ∣ n :=
      ⟨lev x (val y v) * lev y v * lev (x + y) v * b x * b y,
        Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (hlev0 _ _) (hlev0 _ _)) (hlev0 _ _))
          (hb0 _)) (hb0 _),
        ⟨lev y v * lev (x + y) v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev (x + y) v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * b x * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * lev (x + y) v * b y, by ring⟩,
        ⟨lev x (val y v) * lev y v * lev (x + y) v * b x, by ring⟩⟩
    obtain ⟨z, a, ha, hz⟩ := hd x n hn0
    obtain ⟨w, c, hc, hw⟩ := hd y n hn0
    have hzw : ι (z + w) = x + y + n • (a + c) := by
      rw [map_add, hz, hw, smul_add]; abel
    have hβzw : β (ι z) (ι w) = β x y := by
      rw [hz, hw, hl, hr, hr, (hb' x n h4 c hc).1, (hb' y n h5 a ha).2,
        hA _ (A.nsmul_mem ha n) _ (A.nsmul_mem hc n)]
      ring
    rw [← hlev x (val y v) n h1 z a ha hz, ← hlev (x + y) v n h3 (z + w) _ (A.add_mem ha hc) hzw,
      ← hlev y v n h2 w c hc hw, hW, hβzw]
  · intro x v
    refine ⟨lev x v, hlev0 _ _, fun a ha => ?_⟩
    change val (x + lev x v • a) v = val x v
    obtain ⟨z, c, hc, hz⟩ := hd (x + lev x v • a) (lev x v * lev (x + lev x v • a) v)
      (Nat.mul_pos (hlev0 _ _) (hlev0 _ _))
    rw [← hlev _ v _ (Dvd.intro_left _ rfl) z c hc hz]
    refine hlev x v _ dvd_rfl z (a + lev (x + lev x v • a) v • c)
      (A.add_mem ha (A.nsmul_mem hc _)) ?_
    rw [hz, smul_add, mul_smul, add_assoc]

end GlobalTheory.FinWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePidSubalgebraDivPadicInt
section
namespace GlobalTheory

theorem exists_finite_pid_subalgebra_div_padicInt :
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ S : Finset Ω, (∀ s ∈ S, IsAlgebraic ℤ_[p] s) →
  ∃ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R ∧ IsPrincipalIdealRing R ∧ ∀ s ∈ S, ∃ a ∈ R, ∃ b ∈ R, s = a / b := by
  intro p _ Ω _ _ hinj S hS
  haveI : FaithfulSMul ℤ_[p] Ω := (faithfulSMul_iff_algebraMap_injective ℤ_[p] Ω).mpr hinj
  letI : Algebra (FractionRing ℤ_[p]) Ω := FractionRing.liftAlgebra ℤ_[p] Ω
  haveI : IsScalarTower ℤ_[p] (FractionRing ℤ_[p]) Ω := FractionRing.isScalarTower_liftAlgebra ℤ_[p] Ω
  set L := IntermediateField.adjoin (FractionRing ℤ_[p]) (S : Set Ω) with hL
  haveI : FiniteDimensional (FractionRing ℤ_[p]) L := by
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    exact ((hS x hx).extendScalars (IsFractionRing.injective ℤ_[p] (FractionRing ℤ_[p]))).isIntegral
  haveI : Algebra.IsSeparable (FractionRing ℤ_[p]) L := inferInstance
  haveI : IsDedekindDomain (integralClosure ℤ_[p] L) :=
    integralClosure.isDedekindDomain ℤ_[p] (FractionRing ℤ_[p]) L
  haveI : Module.Finite ℤ_[p] (integralClosure ℤ_[p] L) :=
    IsIntegralClosure.finite ℤ_[p] (FractionRing ℤ_[p]) L (integralClosure ℤ_[p] L)
  have hPID : IsPrincipalIdealRing (integralClosure ℤ_[p] L) := by
    apply IsPrincipalIdealRing.of_finite_primes
    haveI := GlobalTheory.finite_maximalSpectrum_of_finite_of_isLocalRing ℤ_[p] (integralClosure ℤ_[p] L)
    apply ((Set.finite_range (fun M : MaximalSpectrum (integralClosure ℤ_[p] L) => M.asIdeal)).insert ⊥).subset
    intro I hI
    by_cases h : I = ⊥
    · exact Or.inl h
    · exact Or.inr ⟨⟨I, (show I.IsPrime from hI).isMaximal h⟩, rfl⟩
  let f : L →ₐ[ℤ_[p]] Ω :=
    { algebraMap L Ω with
      commutes' := fun r => by
        change ((algebraMap ℤ_[p] L r : L) : Ω) = _
        rw [IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) L r]
        exact (IsScalarTower.algebraMap_apply ℤ_[p] (FractionRing ℤ_[p]) Ω r).symm }
  have hf : Function.Injective f := Subtype.val_injective
  let e := Subalgebra.equivMapOfInjective (integralClosure ℤ_[p] L) f hf
  refine ⟨(integralClosure ℤ_[p] L).map f, Module.Finite.equiv e.toLinearEquiv,
    IsPrincipalIdealRing.of_surjective e.toRingHom e.surjective, ?_⟩
  intro s hs
  obtain ⟨c, hc0, hci⟩ := (hS s hs).exists_integral_multiple
  have hsL : s ∈ L := IntermediateField.subset_adjoin _ _ hs
  refine ⟨c • s, ?_, algebraMap ℤ_[p] Ω c, Subalgebra.algebraMap_mem _ c, ?_⟩
  · rw [Subalgebra.mem_map]
    refine ⟨c • ⟨s, hsL⟩, ?_, rfl⟩
    show IsIntegral ℤ_[p] (c • (⟨s, hsL⟩ : L))
    rw [← isIntegral_algHom_iff f hf]
    exact hci
  · rw [Algebra.smul_def, mul_div_cancel_left₀ _ ((map_ne_zero_iff _ hinj).mpr hc0)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerHeisenbergCocycleOfFixedVector
section
noncomputable section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.FinWeil

theorem linearIndependent_of_simultaneous_eigen {ι α M : Type} [AddCommGroup M] [Module ℂ M] (f : ι → M) (χ : ι → α → ℂ)
    (op : α → M →ₗ[ℂ] M) (hχ : Function.Injective χ) (hop : ∀ a i, op a (f i) = χ i a • f i) (hf : ∀ i, f i ≠ 0) :
    LinearIndependent ℂ f := by
  first
  | exact @_root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors
  | exact _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors
  | (apply _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> assumption)
  | (intros; apply _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> assumption)
  | (intros; apply @_root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.JointEigenvectorsIndependent.linearIndependent_of_joint_eigenvectors ..)

end GlobalTheory.FinWeil
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDlog
section
open GlobalTheory.K5 Polynomial

namespace GlobalTheory.K5

def dlogSub (p : ℕ) [Fact p.Prime] (n : ℕ) : Subalgebra (O0 p) (On p n) where
  carrier := {w | KaehlerDifferential.D (O0 p) (On p n) w ∈
    Submodule.span (On p n) ({KaehlerDifferential.D (O0 p) (On p n) (xn p n),
      KaehlerDifferential.D (O0 p) (On p n) (yn p n)} : Set _)}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Derivation.leibniz] at *
    exact add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ ha)
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, map_add] at *
    exact add_mem ha hb
  algebraMap_mem' := by
    intro r
    simp only [Set.mem_setOf_eq, Derivation.map_algebraMap]
    exact zero_mem _

theorem mem_dlogSub (p : ℕ) [Fact p.Prime] (n : ℕ) (w : On p n) : w ∈ dlogSub p n := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hx : xn p n ∈ dlogSub p n :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hy : yn p n ∈ dlogSub p n :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hC : ∀ a : Polynomial (O0 p), Ideal.Quotient.mk (towerIdeal p n) (C a) ∈ dlogSub p n := by
    intro a
    induction a using Polynomial.induction_on with
    | C r =>
      have : Ideal.Quotient.mk (towerIdeal p n) (C (C r)) = algebraMap (O0 p) (On p n) r := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ r
    | add a b ha hb => rw [Polynomial.C_add, map_add]; exact add_mem ha hb
    | monomial k r _ =>
      rw [Polynomial.C_mul, Polynomial.C_pow, map_mul, map_pow]
      refine mul_mem ?_ (pow_mem hx _)
      have : Ideal.Quotient.mk (towerIdeal p n) (C (C r)) = algebraMap (O0 p) (On p n) r := rfl
      rw [this]; exact Subalgebra.algebraMap_mem _ r
  induction f using Polynomial.induction_on with
  | C a => exact hC a
  | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | monomial k a _ =>
    rw [map_mul, map_pow]
    exact mul_mem (hC a) (pow_mem hy _)

theorem exists_isDlog : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (w : (On p n)ˣ), ∃ α β : On p n, IsDlog p n (w : On p n) α β := by
  intro p _ n w
  have h : KaehlerDifferential.D (O0 p) (On p n) (w : On p n) ∈
      Submodule.span (On p n) ({KaehlerDifferential.D (O0 p) (On p n) (xn p n),
        KaehlerDifferential.D (O0 p) (On p n) (yn p n)} : Set _) := mem_dlogSub p n (w : On p n)
  obtain ⟨P, Q, hPQ⟩ := Submodule.mem_span_pair.mp h
  refine ⟨yn p n * Q * ((w⁻¹ : (On p n)ˣ) : On p n), xn p n * P * ((w⁻¹ : (On p n)ˣ) : On p n), ?_⟩
  unfold IsDlog
  rw [← hPQ, smul_add, smul_smul, smul_smul, add_comm]
  congr 1
  · congr 1
    have := w.mul_inv
    linear_combination (xn p n * yn p n * Q) * (-this)
  · congr 1
    have := w.mul_inv
    linear_combination (xn p n * yn p n * P) * (-this)

end GlobalTheory.K5
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLevelOneFormOneAddExpDecay
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory

theorem levelOne_form_one_add_expDecay :
    ∀ d : ℤ, 4 ≤ d → Even d → ∃ e : ℍ → ℂ, IsMF ⊤ d e ∧
      (fun τ : ℍ => e τ - 1) =O[atImInfty] fun τ : ℍ => Real.exp (-2 * Real.pi * τ.im) := by
  intro d hd hev
  obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ d)
  have hk : 3 ≤ k := by omega
  have hk2 : Even k := by simpa [Int.even_coe_nat] using hev
  let f : ModularForm 𝒮ℒ (k : ℤ) := ModularForm.E hk
  refine ⟨f, isMF_coe_top f, ?_⟩
  have h0 : valueAtInfty (f : ℍ → ℂ) = 1 := by
    rw [← qExpansion_coeff_zero one_pos
      (ModularFormClass.analyticAt_cuspFunction_zero f one_pos one_mem_strictPeriods_SL)
      (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)]
    exact EisensteinSeries.E_qExpansion_coeff_zero hk hk2
  have h := exp_decay_sub_atImInfty one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex f one_mem_strictPeriods_SL)
    (ModularFormClass.holo f) (ModularFormClass.bdd_at_infty f)
  rw [h0] at h
  simpa using h

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLowDegreeCoordsModMulStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lowDegree_coords_mod_mul : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k[X] A] (n : ℕ) (b : Module.Basis (Fin n) k[X] A) (g : A) (q : k[X]) (d : ℕ), g ≠ 0 → q ≠ 0 → (Algebra.norm k[X] g).natDegree + q.natDegree ≤ d + 1 →
 ∀ w : A, ∃ p : Fin n → k[X], (∀ i, (p i).natDegree ≤ d) ∧ w - ∑ i, p i • b i ∈ Ideal.span {g * algebraMap k[X] A q} := by
  first | exact @GlobalTheory.exists_lowDegree_coords_mod | exact GlobalTheory.exists_lowDegree_coords_mod | (intros; apply GlobalTheory.exists_lowDegree_coords_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNatCoeffsDetSumSmulNeZeroStatement
section
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nat_coeffs_det_sum_smul_ne_zero : ∀ {K : Type} [Field K] [CharZero K] {m n : ℕ} (T : Fin n → Matrix (Fin m) (Fin m) K) (b : Fin n → K), (∑ i, b i • T i).det ≠ 0 → ∃ a : Fin n → ℕ, (∑ i, (a i : K) • T i).det ≠ 0 := by
  first | exact @GlobalTheory.exists_nat_coeffs_det_ne_zero | exact GlobalTheory.exists_nat_coeffs_det_ne_zero | (intros; apply GlobalTheory.exists_nat_coeffs_det_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNormalFiniteIndexFixing
section
open GlobalTheory.AlmostEt
open scoped NNReal

namespace GlobalTheory.AlmostEt

theorem exists_normal_finiteIndex_fixing (L : Type) [Field L] (G : Type) [Group G]
    [MulSemiringAction G L] (S : Finset L) (hS : ∀ s ∈ S, (MulAction.orbit G s).Finite) :
    ∃ U : Subgroup G, U.Normal ∧ U.FiniteIndex ∧ (∀ s ∈ S, s ∈ Fix L U) ∧
      ∀ h : G, h ∉ U → ∃ x ∈ Fix L U, h • x ≠ x := by
  classical
  set T : Set L := ⋃ s ∈ S, MulAction.orbit G s with hT
  have hTfin : T.Finite := Set.Finite.biUnion S.finite_toSet (fun s hs => hS s hs)
  have hTstab : ∀ g : G, ∀ x ∈ T, g • x ∈ T := by
    intro g x hx
    simp only [hT, Set.mem_iUnion] at hx ⊢
    obtain ⟨s, hs, hx⟩ := hx
    exact ⟨s, hs, MulAction.mem_orbit_of_mem_orbit g hx⟩
  set F : Finset L := hTfin.toFinset
  have hF : ∀ x, x ∈ F ↔ x ∈ T := fun x => hTfin.mem_toFinset
  let U : Subgroup G := ⨅ x ∈ F, MulAction.stabilizer G x
  have hU : ∀ g : G, g ∈ U ↔ ∀ x ∈ T, g • x = x := by
    intro g
    simp only [U, Subgroup.mem_iInf, MulAction.mem_stabilizer_iff, hF]
  have hST : ∀ s ∈ S, s ∈ T := by
    intro s hs
    simp only [hT, Set.mem_iUnion]
    exact ⟨s, hs, MulAction.mem_orbit_self s⟩
  have hFix : ∀ x ∈ T, x ∈ Fix L U := by
    intro x hx
    change ∀ m : U, m • x = x
    rintro ⟨g, hg⟩
    exact (hU g).1 hg x hx
  refine ⟨U, ?_, ?_, fun s hs => hFix s (hST s hs), ?_⟩
  · refine ⟨fun n hn g => ?_⟩
    rw [hU] at hn ⊢
    intro x hx
    have := hn (g⁻¹ • x) (hTstab g⁻¹ x hx)
    rw [mul_smul, mul_smul, this, smul_inv_smul]
  · refine Subgroup.finiteIndex_iInf' _ (fun x hx => ?_)
    refine ⟨?_⟩
    rw [MulAction.index_stabilizer]
    have hx' := (hF x).1 hx
    simp only [hT, Set.mem_iUnion] at hx'
    obtain ⟨s, hs, hxs⟩ := hx'
    rw [MulAction.orbit_eq_iff.mpr hxs]
    exact (Set.ncard_pos (hS s hs)).mpr ⟨s, MulAction.mem_orbit_self s⟩ |>.ne'
  · intro h hh
    rw [hU] at hh
    push_neg at hh
    obtain ⟨x, hx, hne⟩ := hh
    exact ⟨x, hFix x hx, hne⟩

end GlobalTheory.AlmostEt
end

