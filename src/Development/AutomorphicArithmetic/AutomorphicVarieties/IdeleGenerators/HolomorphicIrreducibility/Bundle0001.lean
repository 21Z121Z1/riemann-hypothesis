import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
import Mathlib

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.CuspOf
section
open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

theorem UpperTheory.V.Sd.cuspOf :
    UpperTheory.V.Sd.CuspOf := by
  intro N k _ χ f hχ hv h0
  have hT : (1:ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    refine ⟨ModularGroup.T, ?_, ?_⟩
    · rw [SetLike.mem_coe, Gamma1_mem]
      simp [ModularGroup.T]
    · ext i j
      rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]
  have hinf : IsZeroAtImInfty f := by
    apply ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero f
    rw [← qExpansion_coeff_zero one_pos (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hT)
      (SlashInvariantFormClass.periodic_comp_ofComplex f hT)]
    exact h0
  refine ⟨⟨f.toSlashInvariantForm, f.holo', fun {c} hc => ?_⟩, rfl⟩
  have hc' : IsCusp c 𝒮ℒ := by
    rwa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc']
  intro γ _
  by_cases hd : (N:ℤ) ∣ γ 1 0
  · have hγ : γ ∈ Gamma0 N := Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hd)
    change IsZeroAtImInfty (⇑f ∣[(k:ℤ)] γ)
    rw [hχ γ hγ]
    exact hinf.smul _
  · exact hv γ hd
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DelSerre
section
open Module

section
variable {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

omit [IsAlgClosed K] in
private theorem finrank_map_lt (U : Submodule K M) (S : Module.End K M) (v : M) (hv : v ∈ U) (hv0 : v ≠ 0)
    (hS : S v = 0) : finrank K (U.map S) < finrank K U := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (S.domRestrict U)
  rw [LinearMap.range_domRestrict] at h1
  have h2 : LinearMap.ker (S.domRestrict U) ≠ ⊥ := (Submodule.ne_bot_iff _).mpr
    ⟨⟨v, hv⟩, by simpa using hS, fun h => hv0 (congrArg Subtype.val h)⟩
  have h3 : finrank K (LinearMap.ker (S.domRestrict U)) ≠ 0 := fun h => h2 (Submodule.finrank_eq_zero.mp h)
  omega

end

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem sub_le_one' {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by simpa using hy))

private theorem sub_lt_one' {x y : K} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by simpa using hy))

private def bdd {I : Type} (V : Submodule K (I → K)) : Submodule K V where
  carrier := {v | ∃ c : K, c ≠ 0 ∧ ∀ n, ‖(c • v).1 n‖ ≤ 1}
  zero_mem' := ⟨1, one_ne_zero, fun n => by simp⟩
  add_mem' := by
    have key : ∀ (c e x : K), e ≠ 0 → ‖c‖ ≤ ‖e‖ → ‖e * x‖ ≤ 1 → ‖c * x‖ ≤ 1 := by
      intro c e x _ hce hx
      rw [norm_mul] at hx ⊢
      exact (mul_le_mul_of_nonneg_right hce (norm_nonneg _)).trans hx
    rintro v w ⟨c, hc, hv⟩ ⟨e, he, hw⟩
    rcases le_total ‖c‖ ‖e‖ with h | h
    · refine ⟨c, hc, fun n => ?_⟩
      have : (c • (v + w)).1 n = c * v.1 n + c * w.1 n := by simp [mul_add]
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv n) (key c e _ he h (hw n)))
    · refine ⟨e, he, fun n => ?_⟩
      have : (e • (v + w)).1 n = e * v.1 n + e * w.1 n := by simp [mul_add]
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (key e c _ hc h (hv n)) (hw n))
  smul_mem' := by
    rintro s v ⟨c, hc, hv⟩
    by_cases hs : s = 0
    · exact ⟨1, one_ne_zero, fun n => by simp [hs]⟩
    · refine ⟨c / s, div_ne_zero hc hs, fun n => ?_⟩
      rw [smul_smul, div_mul_cancel₀ c hs]
      exact hv n

omit [IsUltrametricDist K] in
private theorem eig_le_one {I : Type} {V : Submodule K (I → K)} (T : Module.End K V)
    (hT : ∀ v : V, (∀ n, ‖v.1 n‖ ≤ 1) → ∀ n, ‖(T v).1 n‖ ≤ 1) (v : V) (hv0 : v ≠ 0) (hv : ∀ n, ‖v.1 n‖ ≤ 1)
    (c : K) (hc : T v = c • v) : ‖c‖ ≤ 1 := by
  by_contra h
  push Not at h
  have hk : ∀ k : ℕ, ∀ n, ‖(c ^ k • v).1 n‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih =>
      have := hT _ ih
      rwa [map_smul, hc, smul_smul, ← pow_succ] at this
  obtain ⟨n, hn⟩ : ∃ n, v.1 n ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hv0 (Subtype.ext (funext h'))
  have hpos : 0 < ‖v.1 n‖ := norm_pos_iff.mpr hn
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (‖v.1 n‖⁻¹) h
  have h1 := hk k n
  have h2 : (c ^ k • v).1 n = c ^ k * v.1 n := by simp
  rw [h2, norm_mul, norm_pow] at h1
  have h3 := mul_lt_mul_of_pos_right hk' hpos
  rw [inv_mul_cancel₀ hpos.ne'] at h3
  linarith

private theorem main [IsAlgClosed K] {I J : Type} (V : Submodule K (I → K)) [FiniteDimensional K V]
    (T : J → Module.End K V) (hc : ∀ i j, T i * T j = T j * T i)
    (h1 : ∀ j (v : V), (∀ n, ‖v.1 n‖ ≤ 1) → ∀ n, ‖(T j v).1 n‖ ≤ 1)
    (h2 : ∀ j (v : V), (∀ n, ‖v.1 n‖ < 1) → ∀ n, ‖(T j v).1 n‖ < 1) (a : J → K) (ha : ∀ j, ‖a j‖ ≤ 1) :
    ∀ (d : ℕ) (U : Submodule K V), finrank K U = d → U ≤ bdd V → (∀ j, ∀ x ∈ U, T j x ∈ U) →
      ∀ f ∈ U, (∀ n, ‖f.1 n‖ ≤ 1) → (∃ n, ‖f.1 n‖ = 1) → (∀ j n, ‖(T j f).1 n - a j * f.1 n‖ < 1) →
      ∃ (h : V) (b : J → K), h ≠ 0 ∧ (∀ n, ‖h.1 n‖ ≤ 1) ∧ (∀ j, T j h = b j • h) ∧ ∀ j, ‖b j - a j‖ < 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hd hb hT f hfU hf hf1 hfa
    by_cases h : ∀ j (c : K), ∀ v ∈ U, v ≠ 0 → T j v = c • v → ‖c - a j‖ < 1
    · have hU : U ≠ ⊥ := by
        refine (Submodule.ne_bot_iff U).mpr ⟨f, hfU, ?_⟩
        rintro rfl
        obtain ⟨n, hn⟩ := hf1
        simp at hn
      obtain ⟨v, hv, hv0, hve⟩ := UpperTheory.V.LinAlg.simEig T hc _ U rfl hU hT
      choose b hbv using hve
      obtain ⟨c, hc0, hcv⟩ := hb hv
      refine ⟨c • v, b, smul_ne_zero hc0 hv0, hcv, fun j => ?_, fun j => h j (b j) v hv hv0 (hbv j)⟩
      rw [map_smul, hbv j, smul_comm]
    · push Not at h
      obtain ⟨j, c, v, hv, hv0, hcv, hca⟩ := h
      have hc1 : ‖c‖ ≤ 1 := by
        obtain ⟨e, he0, hev⟩ := hb hv
        refine eig_le_one (T j) (h1 j) (e • v) (smul_ne_zero he0 hv0) hev c ?_
        rw [map_smul, hcv, smul_comm]
      have hca1 : ‖c - a j‖ = 1 := le_antisymm (sub_le_one' hc1 (ha j)) hca
      let S : Module.End K V := T j - c • 1
      have hS : ∀ x, S x = T j x - c • x := fun x => by simp [S]
      have hcomm : ∀ i x, T i (S x) = S (T i x) := by
        intro i x
        have h3 : T j (T i x) = T i (T j x) := by
          have := congrArg (fun S : Module.End K V => S x) (hc j i)
          simpa using this
        rw [hS, hS, map_sub, map_smul, h3]
      have hle : U.map S ≤ U := by
        rintro _ ⟨x, hx, rfl⟩
        rw [hS]
        exact U.sub_mem (hT j x hx) (U.smul_mem c hx)
      have hSn : ∀ (x : V) n, (S x).1 n = (T j x).1 n - c * x.1 n := fun x n => by rw [hS]; simp
      refine ih _ (hd ▸ finrank_map_lt U S v hv hv0 (by rw [hS, hcv, sub_self])) (U.map S) rfl (hle.trans hb) ?_
        (S f) ⟨f, hfU, rfl⟩ ?_ ?_ ?_
      · rintro i _ ⟨x, hx, rfl⟩
        exact ⟨T i x, hT i x hx, (hcomm i x).symm⟩
      · intro n
        rw [hSn]
        refine sub_le_one' (h1 j f hf n) ?_
        rw [norm_mul]
        exact mul_le_one₀ hc1 (norm_nonneg _) (hf n)
      · obtain ⟨n, hn⟩ := hf1
        refine ⟨n, le_antisymm ?_ ?_⟩
        · rw [hSn]
          refine sub_le_one' (h1 j f hf n) ?_
          rw [norm_mul]
          exact mul_le_one₀ hc1 (norm_nonneg _) (hf n)
        · by_contra hlt
          push Not at hlt
          have h4 := sub_lt_one' (hfa j n) hlt
          have h5 : (T j f).1 n - a j * f.1 n - (S f).1 n = (c - a j) * f.1 n := by rw [hSn]; ring
          rw [h5, norm_mul, hca1, hn] at h4
          simp at h4
      · intro i n
        have hg : ∀ n, ‖(T i f - a i • f).1 n‖ < 1 := fun n => by simpa using hfa i n
        have h6 : (T i (S f)).1 n - a i * (S f).1 n = (S (T i f - a i • f)).1 n := by
          rw [map_sub, map_smul, hcomm]; simp
        rw [h6, hSn]
        refine sub_lt_one' (h2 j _ hg n) ?_
        rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right hc1 (norm_nonneg _) (hg n)

end

theorem UpperTheory.V.Sd.delSerre :
    UpperTheory.V.Sd.DelSerre := by
  intro l _ I J V hV T hc h1 h2 f a hf hf1 ha hfa
  refine main V T hc h1 h2 a ha _ (bdd V) rfl le_rfl ?_ f ⟨1, one_ne_zero, by simpa using hf⟩ hf hf1 hfa
  rintro j x ⟨c, hc0, hx⟩
  refine ⟨c, hc0, ?_⟩
  rw [← map_smul]
  exact h1 j _ hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EPrim
section
theorem UpperTheory.V.Sd.ePrim :
    UpperTheory.V.Sd.EPrim := by
  intro l M w φ θ χ D
  have hM := D.one_lt
  have hw := D.prime
  haveI : NeZero M := ⟨by omega⟩
  haveI : NeZero w := ⟨hw.ne_zero⟩
  haveI : NeZero (M * w) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne w)⟩
  set A := DirichletCharacter.changeLevel (dvd_mul_right M w) φ with hA
  set B := DirichletCharacter.changeLevel (dvd_mul_left w M) θ with hB
  have hχ : χ = A * B := by
    ext u
    have h1 := D.mul (u : ZMod (M * w)).val
    rw [MulChar.mul_apply, hA, hB, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.natCast_val, ← ZMod.natCast_val,
      ← h1, ZMod.natCast_zmod_val]
  have hAc : A.conductor = M := by
    rw [hA, DirichletCharacter.conductor_changeLevel]
    exact D.prim
  have hBc : B.conductor = w := by
    rw [hB, DirichletCharacter.conductor_changeLevel]
    rcases (Nat.dvd_prime hw).mp θ.conductor_dvd_level with h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) D.θne
    · exact h
  have hcop : M.Coprime w := ((Nat.Prime.coprime_iff_not_dvd hw).mpr D.wM).symm
  have h1 : M ∣ χ.conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor χ B⁻¹
    rw [DirichletCharacter.conductor_inv, hBc] at h
    have e : χ * B⁻¹ = A := by rw [hχ, mul_inv_cancel_right]
    rw [e, hAc] at h
    exact hcop.dvd_of_dvd_mul_right (h.trans (Nat.lcm_dvd_mul _ _))
  have h2 : w ∣ χ.conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor A⁻¹ χ
    rw [DirichletCharacter.conductor_inv, hAc] at h
    have e : A⁻¹ * χ = B := by rw [hχ, inv_mul_cancel_left]
    rw [e, hBc] at h
    exact hcop.symm.dvd_of_dvd_mul_left (h.trans (Nat.lcm_dvd_mul _ _))
  exact Nat.dvd_antisymm χ.conductor_dvd_level (hcop.mul_dvd_of_dvd_of_dvd h1 h2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisSlash
section
noncomputable section

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

private def slashEquiv (N : ℕ) (x : ZMod N) (a b c d : ℤ) (hdet : a * d - b * c = 1) (hc : (c : ZMod N) = 0) :
    {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = x} ≃
      {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = x * (d : ZMod N)} where
  toFun v := ⟨(v.1.1 * a + v.1.2 * c, v.1.1 * b + v.1.2 * d), by
    obtain ⟨⟨m, n⟩, h1, h2⟩ := v
    simp only at h1 h2
    constructor <;> simp [h1, h2, hc]⟩
  invFun v := ⟨(v.1.1 * d - v.1.2 * c, -(v.1.1 * b) + v.1.2 * a), by
    obtain ⟨⟨m, n⟩, h1, h2⟩ := v
    simp only at h1 h2
    have h : (a : ZMod N) * d = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod N) hdet
      push_cast at this
      simpa [hc] using this
    constructor
    · simp [h1, hc]
    · push_cast
      rw [h1, h2]
      linear_combination x * h⟩
  left_inv v := by
    obtain ⟨⟨m, n⟩, h⟩ := v
    apply Subtype.ext
    apply Prod.ext
    · show (m * a + n * c) * d - (m * b + n * d) * c = m
      linear_combination m * hdet
    · show -((m * a + n * c) * b) + (m * b + n * d) * a = n
      linear_combination n * hdet
  right_inv v := by
    obtain ⟨⟨m, n⟩, h⟩ := v
    apply Subtype.ext
    apply Prod.ext
    · show (m * d - n * c) * a + (-(m * b) + n * a) * c = m
      linear_combination m * hdet
    · show (m * d - n * c) * b + (-(m * b) + n * a) * d = n
      linear_combination n * hdet

theorem eisSlash : EisSlash := by
  intro N k _ _ a γ hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hγ
  ext z
  rw [ModularForm.SL_slash_apply]
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (z : ℂ) = (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) := by
    simp [denom]
  have hsm : ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have hne : (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) ≠ 0 := by
    rw [← hden]
    exact denom_ne_zero _ z
  have key : ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) = (γ 0 0 : ℂ) * z + (γ 0 1 : ℂ) := div_mul_cancel₀ _ hne
  rw [hden]
  unfold eisFun
  rw [hsm, mul_assoc, ← tsum_mul_right]
  rw [← (slashEquiv N a (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) hdet hc).tsum_eq]
  congr 1
  congr 1
  funext v
  rw [← mul_zpow]
  congr 1
  simp only [slashEquiv, Equiv.coe_fn_mk]
  push_cast
  linear_combination ((v : ℤ × ℤ).1 : ℂ) * key

end UpperTheory.V.Sd
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisVan
section
open ModularForm UpperHalfPlane Matrix EisensteinSeries Filter Topology
open scoped MatrixGroups

namespace UpperTheory.V.Sd

private def cSet {N : ℕ} (b : Fin 2 → ZMod N) : Set (Fin 2 → ℤ) := {v | (↑) ∘ v = b}

private lemma vecMul_mem_cSet {N : ℕ} {b : Fin 2 → ZMod N} {v : Fin 2 → ℤ} (hv : v ∈ cSet b)
    (γ : SL(2, ℤ)) : v ᵥ* γ ∈ cSet (b ᵥ* γ) := by
  have := RingHom.map_vecMul (m := Fin 2) (n := Fin 2) (Int.castRingHom (ZMod N)) γ v
  simp only [eq_intCast, Int.coe_castRingHom] at this
  have hv' : (fun x : ℤ => (x : ZMod N)) ∘ v = b := hv
  change (Int.cast : ℤ → ZMod N) ∘ (v ᵥ* (γ : Matrix (Fin 2) (Fin 2) ℤ)) = b ᵥ* _
  funext i
  rw [Function.comp_apply, this i, hv']
  simp [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]

private def cEquiv {N : ℕ} (b : Fin 2 → ZMod N) (γ : SL(2, ℤ)) : cSet b ≃ cSet (b ᵥ* γ) where
  toFun v := ⟨v.1 ᵥ* γ, vecMul_mem_cSet v.2 γ⟩
  invFun v := ⟨v.1 ᵥ* ↑(γ⁻¹), by
      have := vecMul_mem_cSet v.2 γ⁻¹
      have h1 : ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) *
          (((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N)) = 1 := by
        have h0 : (γ : SL(2, ZMod N)) * ((γ⁻¹ : SL(2, ℤ)) : SL(2, ZMod N)) = 1 :=
          (map_mul (SpecialLinearGroup.map (Int.castRingHom (ZMod N))) γ γ⁻¹).symm.trans (by simp)
        exact congrArg Subtype.val h0
      rwa [vecMul_vecMul, h1, vecMul_one] at this⟩
  left_inv v := by
    have h : (γ : Matrix (Fin 2) (Fin 2) ℤ) * ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
      congrArg Subtype.val (mul_inv_cancel γ)
    refine Subtype.ext ?_
    exact (vecMul_vecMul _ _ _).trans (by rw [h, vecMul_one])
  right_inv v := by
    have h : ((γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (γ : Matrix (Fin 2) (Fin 2) ℤ) = 1 :=
      congrArg Subtype.val (inv_mul_cancel γ)
    refine Subtype.ext ?_
    exact (vecMul_vecMul _ _ _).trans (by rw [h, vecMul_one])

private noncomputable def cSer {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) (z : ℍ) : ℂ :=
  ∑' x : cSet b, eisSummand k x z

private lemma cSer_slash {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) (γ : SL(2, ℤ)) :
    cSer b k ∣[k] γ = cSer (b ᵥ* γ) k := by
  ext1 z
  simp_rw [SL_slash_apply, _root_.zpow_neg,
    mul_inv_eq_iff_eq_mul₀ (zpow_ne_zero _ <| denom_ne_zero _ z),
    cSer, eisSummand_SL2_apply, tsum_mul_left, mul_comm (_ ^ k)]
  congr 1
  exact (cEquiv b γ).tsum_eq (eisSummand k · z)

private noncomputable def cSIF {N : ℕ} (b : Fin 2 → ZMod N) (k : ℤ) :
    SlashInvariantForm (CongruenceSubgroup.Gamma N) k where
  toFun := cSer b k
  slash_action_eq' A hA := by
    obtain ⟨A, (hA : A ∈ CongruenceSubgroup.Gamma N), rfl⟩ := hA
    simp [SpecialLinearGroup.mapGL, ← SL_slash, cSer_slash, CongruenceSubgroup.Gamma_mem'.mp hA]

private lemma summand_le {k : ℕ} (v : Fin 2 → ℤ) (hv : v 0 ≠ 0) (z : ℍ) :
    ‖eisSummand k v z‖ ≤ (z.im ^ k)⁻¹ := by
  have hz := z.im_pos
  have him : z.im ≤ ‖(v 0 : ℂ) * (z : ℂ) + v 1‖ := by
    have h1 : ((v 0 : ℂ) * (z : ℂ) + v 1).im = (v 0 : ℝ) * z.im := by simp
    have h2 : (1 : ℝ) ≤ |(v 0 : ℝ)| := by exact_mod_cast Int.one_le_abs hv
    calc z.im ≤ |(v 0 : ℝ)| * z.im := by nlinarith
      _ = |((v 0 : ℂ) * (z : ℂ) + v 1).im| := by rw [h1, abs_mul, abs_of_pos hz]
      _ ≤ _ := Complex.abs_im_le_norm _
  simp only [eisSummand, norm_zpow]
  rw [_root_.zpow_neg, zpow_natCast]
  exact inv_anti₀ (pow_pos hz k) (pow_le_pow_left₀ hz.le him k)

private lemma cSer_zero {N : ℕ} [NeZero N] (b : Fin 2 → ZMod N) (hb : b 0 ≠ 0) {k : ℕ}
    (hk : 3 ≤ k) : IsZeroAtImInfty (cSer b k) := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hkr : (2 : ℝ) < k := by exact_mod_cast (show 2 < k by omega)
  have hv0 : ∀ v : cSet b, v.1 0 ≠ 0 := by
    intro v h
    apply hb
    have h2 := congrFun v.2 0
    simp only [Function.comp_apply, h, Int.cast_zero] at h2
    exact h2.symm
  have hper : ∀ (n : ℤ) (z : ℍ), cSer b k ((N : ℝ) * (n : ℝ) +ᵥ z) = cSer b k z :=
    fun n z => SlashInvariantForm.vAdd_width_periodic N k n (cSIF b k) z
  set F : Filter ℍ := atImInfty ⊓ 𝓟 (verticalStrip N 1) with hF
  set C : ℝ := r ⟨⟨N, 1⟩, one_pos⟩ with hC
  have hsum : Summable (fun v : cSet b => C ^ (-(k : ℝ)) * ‖v.1‖ ^ (-(k : ℝ))) :=
    ((summable_one_div_norm_rpow hkr).subtype (cSet b)).mul_left _
  have hT : Tendsto (fun z => cSer b k z) F (𝓝 0) := by
    have h0 : (0 : ℂ) = ∑' v : cSet b, (0 : ℂ) := by simp
    rw [h0]
    apply tendsto_tsum_of_dominated_convergence hsum
    · intro v
      have him : Tendsto (fun z : ℍ => z.im) F atTop :=
        tendsto_comap.mono_left inf_le_left
      have hdec : Tendsto (fun z : ℍ => (z.im ^ k)⁻¹) F (𝓝 0) :=
        tendsto_inv_atTop_zero.comp ((tendsto_pow_atTop (by omega)).comp him)
      exact squeeze_zero_norm' (Eventually.of_forall (fun z => summand_le v.1 (hv0 v) z)) hdec
    · rw [hF, eventually_inf_principal]
      apply Eventually.of_forall
      intro z hz v
      have h1 := summand_bound_of_mem_verticalStrip (k := (k : ℝ)) (by positivity) v.1 one_pos hz
      calc ‖eisSummand k v.1 z‖ = ‖(v.1 0 : ℂ) * z + v.1 1‖ ^ (-(k : ℝ)) := by
            rw [eisSummand, norm_zpow, ← Real.rpow_intCast]
            push_cast
            rfl
        _ ≤ _ := h1
  have hn : Tendsto (fun z => ‖cSer b k z‖) F (𝓝 0) := by simpa using hT.norm
  rw [isZeroAtImInfty_iff]
  intro ε hε
  have hev : ∀ᶠ z in F, ‖cSer b k z‖ ≤ ε := hn.eventually (Iic_mem_nhds hε)
  rw [hF, eventually_inf_principal] at hev
  obtain ⟨A, hA⟩ := (atImInfty_mem _).mp hev
  refine ⟨max A 1, fun z hz => ?_⟩
  have hfl1 := Int.floor_le (z.re / N)
  have hfl2 := Int.lt_floor_add_one (z.re / N)
  have e1 : (N : ℝ) * ⌊z.re / N⌋ ≤ z.re := by
    have := mul_le_mul_of_nonneg_left hfl1 hN.le
    rwa [mul_div_cancel₀ _ hN.ne'] at this
  have e2 : z.re < (N : ℝ) * ⌊z.re / N⌋ + N := by
    have := mul_lt_mul_of_pos_left hfl2 hN
    rwa [mul_div_cancel₀ _ hN.ne', mul_add, mul_one] at this
  have hmem : ((N : ℝ) * ((-⌊z.re / N⌋ : ℤ) : ℝ) +ᵥ z) ∈ verticalStrip N 1 := by
    rw [mem_verticalStrip_iff, vadd_re, vadd_im, abs_le]
    push_cast
    refine ⟨⟨by nlinarith, by nlinarith⟩, by linarith [le_max_right A 1]⟩
  have hz' := hA ((N : ℝ) * ((-⌊z.re / N⌋ : ℤ) : ℝ) +ᵥ z)
    (by rw [vadd_im]; linarith [le_max_left A 1]) hmem
  rwa [hper] at hz'

private lemma eisFun_eq (N k : ℕ) (a : ZMod N) :
    eisFun N k a = ((N : ℂ) ^ k / lipC k) • cSer ![0, a] k := by
  let e : {v : ℤ × ℤ // ((v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = a)} ≃ cSet (![0, a] : Fin 2 → ZMod N) :=
    { toFun := fun v => ⟨![v.1.1, v.1.2], by
        show (Int.cast : ℤ → ZMod N) ∘ ![v.1.1, v.1.2] = ![0, a]
        funext i
        fin_cases i
        · simpa using v.2.1
        · simpa using v.2.2⟩
      invFun := fun w => ⟨(w.1 0, w.1 1), by
        have h := w.2
        change (Int.cast : ℤ → ZMod N) ∘ w.1 = ![0, a] at h
        exact ⟨by simpa using congrFun h 0, by simpa using congrFun h 1⟩⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp
      right_inv := fun w => by
        apply Subtype.ext
        funext i
        fin_cases i <;> simp }
  funext z
  simp only [eisFun, cSer, Pi.smul_apply, smul_eq_mul]
  congr 1
  rw [← e.tsum_eq]
  congr 1

end UpperTheory.V.Sd

theorem UpperTheory.V.Sd.eisVan :
    UpperTheory.V.Sd.EisVan := by
  intro N k _ hk a ha hN γ hγ
  rw [UpperTheory.V.Sd.eisFun_eq, ModularForm.SL_smul_slash, UpperTheory.V.Sd.cSer_slash]
  apply Filter.ZeroAtFilter.smul
  apply UpperTheory.V.Sd.cSer_zero _ _ hk
  have hc : ((γ 1 0 : ℤ) : ZMod N) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact hγ
  have e : (![0, a] ᵥ* ((γ : SL(2, ZMod N)) : Matrix (Fin 2) (Fin 2) (ZMod N))) 0 = a * ((γ 1 0 : ℤ) : ZMod N) := by
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply]
  rw [e]
  intro h
  exact hc ((ha.mul_right_eq_zero).mp h)
end

