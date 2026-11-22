import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXEC
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSB
import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0005
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.Bundle0012
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSOmDecomp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.Bundle0007
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.Bundle0021

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXECPfA
section
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX.EC

open Formalism.QuantumDeterminants WlocSk.NB
open Formalism.MainNotions.BridgeCSB (Fil lieN adjH adjH_apply dg)

variable {k r : ℕ}

abbrev J (k r : ℕ) := (CI k r ⊕ CI k r) ⊕ Fin r

def toC (y : J k r → ℝ) : (CI k r → ℂ) × (Fin r → ℝ) :=
  (fun i => ⟨y (Sum.inl (Sum.inl i)), y (Sum.inl (Sum.inr i))⟩, fun a => y (Sum.inr a))

def Lm (t : (CI k r → ℂ) × (Fin r → ℝ)) : Mx k r :=
  mkM (cA t.1 - 1) (cB t.1) (cK t.1 t.2) (-(dD k * (cB t.1)ᴴ)) (-(cA t.1 - 1)ᴴ) - mkM 0 0 0 0 0

def ShearStep : Prop := ∀ k r : ℕ, ∃ σ : (J k r → ℝ) → (CI k r → ℂ) × (Fin r → ℝ),
  MeasurePreserving σ volume volume ∧ ∀ y, phi0 (σ y).1 (σ y).2 = NormedSpace.exp (Lm (toC y))

def ConstStep : Prop := ∀ k r : ℕ, ∃ Λ : (J k r → ℝ) → Formalism.MainNotions.S.lieE (Nset k r), Measurable Λ ∧
  (∀ y, ((Λ y : Formalism.MainNotions.S.lieE (Nset k r)) : EuclideanSpace ℝ _) = Formalism.MainNotions.BridgeCSB.RL (k := k) (r := r) (Lm (toC y))) ∧
  (volume : Measure (Formalism.MainNotions.S.lieE (Nset k r))) = ENNReal.ofReal ((2 : ℝ) ^ (r ^ 2 + r * k)) • volume.map Λ

theorem dg_eI (a : Fin r) : dg k r (eI k r a) = a.val := by
  have := a.isLt; unfold dg eI; simp only; split_ifs <;> omega
theorem dg_wI (j : Fin (k + 1)) : dg k r (wI k r j) = r := by
  have := j.isLt; unfold dg wI; simp only; split_ifs <;> omega
theorem dg_esI (a : Fin r) : dg k r (esI k r a) = 2 * r - a.val := by
  have := a.isLt; unfold dg esI; simp only; split_ifs <;> omega

theorem gtau_eI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (eI k r a) = esI k r a := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.tau eI esI; apply Fin.ext; simp only; split_ifs <;> omega
theorem gtau_esI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (esI k r a) = eI k r a := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.tau eI esI; apply Fin.ext; simp only; split_ifs <;> omega
theorem gtau_wI (j : Fin (k + 1)) : Formalism.QuantumDeterminants.WeylGroupFacts.tau k r (wI k r j) = wI k r j := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.tau wI; apply Fin.ext; simp only; split_ifs <;> omega
theorem gsgn_eI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r (eI k r a) = 1 := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.sgn eI; simp only; split_ifs <;> first | rfl | omega
theorem gsgn_esI (a : Fin r) : Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r (esI k r a) = 1 := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.sgn esI; simp only; split_ifs <;> first | rfl | omega
theorem gsgn_wI (j : Fin (k + 1)) : Formalism.QuantumDeterminants.WeylGroupFacts.sgn k r (wI k r j) = dD k j j := by
  unfold Formalism.QuantumDeterminants.WeylGroupFacts.sgn wI dD
  simp only [Matrix.diagonal_apply_eq]
  split_ifs <;> first | rfl | omega

theorem dD_star (j : Fin (k + 1)) : star (dD k j j) = dD k j j := by
  simp only [dD, Matrix.diagonal_apply_eq]; split_ifs <;> simp
theorem dD_sq' (j : Fin (k + 1)) : dD k j j * dD k j j = 1 := by
  simp only [dD, Matrix.diagonal_apply_eq]; split_ifs <;> simp

theorem chart_matrix_lower (x : CI k r → ℂ) {a b : Fin r} (h : b ≤ a) : (cA x - 1) a b = 0 := by
  rw [Matrix.sub_apply, Matrix.one_apply]; unfold cA; rw [dif_neg (not_lt.2 h)]; split_ifs <;> simp

theorem chart_matrix_upper (x : CI k r → ℂ) {a b : Fin r} (h : a < b) : (cA x - 1) a b = x (Sum.inl ⟨(a, b), h⟩) := by
  rw [Matrix.sub_apply, Matrix.one_apply, if_neg (ne_of_lt h)]; unfold cA; rw [dif_pos h, sub_zero]

theorem cK_skew (x : CI k r → ℂ) (s : Fin r → ℝ) (a b : Fin r) : cK x s a b + star (cK x s b a) = 0 := by
  unfold cK
  rcases lt_trichotomy a b with h | h | h
  · rw [dif_pos h, dif_neg (not_lt.2 h.le), dif_pos h, star_neg, star_star, add_neg_cancel]
  · subst h
    rw [dif_neg (lt_irrefl _), dif_neg (lt_irrefl _), star_mul', Complex.star_def,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  · rw [dif_neg (not_lt.2 h.le), dif_pos h, dif_pos h, neg_add_cancel]

section entries

variable (t : (CI k r → ℂ) × (Fin r → ℝ))

@[simp] theorem Lm_ee (a b : Fin r) : Lm t (eI k r a) (eI k r b) = (cA t.1 - 1) a b := by
  simp only [Lm, Matrix.sub_apply, mk_ee, Matrix.zero_apply, sub_zero]
@[simp] theorem Lm_ew (a : Fin r) (j : Fin (k + 1)) : Lm t (eI k r a) (wI k r j) = cB t.1 a j := by
  simp only [Lm, Matrix.sub_apply, mk_ew, Matrix.zero_apply, sub_zero]
@[simp] theorem Lm_es (a b : Fin r) : Lm t (eI k r a) (esI k r b) = cK t.1 t.2 a b := by
  simp only [Lm, Matrix.sub_apply, mk_es, Matrix.zero_apply, sub_zero]
@[simp] theorem Lm_we (j : Fin (k + 1)) (b : Fin r) : Lm t (wI k r j) (eI k r b) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_we, sub_zero]
@[simp] theorem Lm_ww (j c : Fin (k + 1)) : Lm t (wI k r j) (wI k r c) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_ww, sub_self]
@[simp] theorem Lm_ws (j : Fin (k + 1)) (b : Fin r) :
    Lm t (wI k r j) (esI k r b) = -(dD k j j * star (cB t.1 b j)) := by
  simp only [Lm, Matrix.sub_apply, mk_ws, Matrix.zero_apply, sub_zero, Matrix.neg_apply, dD_mul_apply,
    conjTranspose_apply]
@[simp] theorem Lm_se (a b : Fin r) : Lm t (esI k r a) (eI k r b) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_se, sub_zero]
@[simp] theorem Lm_sw (a : Fin r) (j : Fin (k + 1)) : Lm t (esI k r a) (wI k r j) = 0 := by
  simp only [Lm, Matrix.sub_apply, mk_sw, sub_zero]
@[simp] theorem Lm_ss (a b : Fin r) : Lm t (esI k r a) (esI k r b) = -star ((cA t.1 - 1) b a) := by
  simp only [Lm, Matrix.sub_apply, mk_ss, Matrix.zero_apply, sub_zero, Matrix.neg_apply, conjTranspose_apply]

end entries

theorem chart_filtration_one (t : (CI k r → ℂ) × (Fin r → ℝ)) : Fil 1 (Lm t) := by
  intro i j h
  obtain ⟨p, rfl⟩ := (posE k r).surjective i
  obtain ⟨q, rfl⟩ := (posE k r).surjective j
  rcases p with a | c | a <;> rcases q with b | c' | b <;>
    simp only [posE_apply, pos, dg_eI, dg_wI, dg_esI] at h <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss]
  all_goals first
    | rfl
    | exact chart_matrix_lower _ (Fin.le_iff_val_le_val.2 (by omega))
    | (rw [neg_eq_zero, star_eq_zero]
       exact chart_matrix_lower _ (Fin.le_iff_val_le_val.2 (by have := a.isLt; have := b.isLt; omega)))
    | (exfalso; first
        | (have := a.isLt; have := b.isLt; omega)
        | (have := a.isLt; omega)
        | (have := b.isLt; omega))

theorem Lm_adj (t : (CI k r → ℂ) × (Fin r → ℝ)) : adjH (Lm t) + Lm t = 0 := by
  ext i j
  rw [Matrix.add_apply, adjH_apply, Matrix.zero_apply]
  obtain ⟨p, rfl⟩ := (posE k r).surjective i
  obtain ⟨q, rfl⟩ := (posE k r).surjective j
  rcases p with a | c | a <;> rcases q with b | c' | b <;>
    simp only [posE_apply, pos, gtau_eI, gtau_esI, gtau_wI, gsgn_eI, gsgn_esI, gsgn_wI,
      Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss, star_zero, mul_zero, zero_mul,
      add_zero, one_mul, mul_one, star_neg, star_star, neg_add_cancel, star_mul', dD_star]
  all_goals first
    | rw [add_neg_cancel]
    | linear_combination cK_skew t.1 t.2 a b
    | linear_combination (-(cB t.1 a c')) * dD_sq' c'

theorem Lm_mem (t : (CI k r → ℂ) × (Fin r → ℝ)) : Lm t ∈ lieN k r := ⟨chart_filtration_one t, Lm_adj t⟩

def hC : CI k r → ℕ
  | Sum.inl p => p.1.2.val - p.1.1.val
  | Sum.inr (Sum.inl q) => r - q.1.val
  | Sum.inr (Sum.inr p) => 2 * r - p.1.1.val - p.1.2.val

def ht : J k r → ℕ
  | Sum.inl (Sum.inl c) => hC c
  | Sum.inl (Sum.inr c) => hC c
  | Sum.inr a => 2 * r - 2 * a.val

theorem coordinate_first_eq {y y' : J k r → ℝ} {p : ℕ} (h : ∀ j, ht j < p → y j = y' j) {c : CI k r} (hc : hC c < p) :
    (toC y).1 c = (toC y').1 c := by
  simp only [toC]; rw [h (Sum.inl (Sum.inl c)) hc, h (Sum.inl (Sum.inr c)) hc]

theorem coordinate_second_eq {y y' : J k r → ℝ} {p : ℕ} (h : ∀ j, ht j < p → y j = y' j) {a : Fin r}
    (ha : 2 * r - 2 * a.val < p) : (toC y).2 a = (toC y').2 a := by
  simp only [toC]; rw [h (Sum.inr a) ha]

theorem Lm_fil_sub {y y' : J k r → ℝ} {p : ℕ} (h : ∀ j, ht j < p → y j = y' j) :
    Fil p (Lm (toC y) - Lm (toC y')) := by
  intro i j hij
  rw [Matrix.sub_apply, sub_eq_zero]
  obtain ⟨P, rfl⟩ := (posE k r).surjective i
  obtain ⟨Q, rfl⟩ := (posE k r).surjective j
  rcases P with a | c | a <;> rcases Q with b | c' | b <;>
    simp only [posE_apply, pos, dg_eI, dg_wI, dg_esI] at hij <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss]
  · by_cases hab : a < b
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      exact coordinate_first_eq h (by simp only [hC]; omega)
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]
  · exact coordinate_first_eq h (by simp only [hC]; omega)
  · unfold cK
    split_ifs with h1 h2
    · exact coordinate_first_eq h (by simp only [hC]; have := b.isLt; omega)
    · rw [coordinate_first_eq h (by simp only [hC]; have := a.isLt; omega)]
    · have e : a = b := le_antisymm (not_lt.1 h2) (not_lt.1 h1)
      subst e
      rw [coordinate_second_eq h (by have := a.isLt; omega)]
  · simp only [cB]
    rw [coordinate_first_eq h (c := Sum.inr (Sum.inl (b, c))) (by simp only [hC]; have := b.isLt; omega)]
  · by_cases hab : b < a
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      rw [coordinate_first_eq h (by simp only [hC]; have := a.isLt; have := b.isLt; omega)]
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]

theorem Lm_add (t t' : (CI k r → ℂ) × (Fin r → ℝ)) : Lm (t + t') = Lm t + Lm t' := by
  ext i j
  rw [Matrix.add_apply]
  obtain ⟨P, rfl⟩ := (posE k r).surjective i
  obtain ⟨Q, rfl⟩ := (posE k r).surjective j
  rcases P with a | c | a <;> rcases Q with b | c' | b <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss, add_zero]
  · by_cases hab : a < b
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab, chart_matrix_upper _ hab]; rfl
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), add_zero]
  · rfl
  · unfold cK
    split_ifs
    · rfl
    · simp only [Prod.fst_add, Pi.add_apply, star_add]; ring
    · simp only [Prod.snd_add, Pi.add_apply]; push_cast; ring
  · simp only [cB, Prod.fst_add, Pi.add_apply, star_add]; ring
  · by_cases hab : b < a
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      simp only [Prod.fst_add, Pi.add_apply, star_add]; ring
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]; simp

theorem Lm_smul (c : ℝ) (t : (CI k r → ℂ) × (Fin r → ℝ)) : Lm (c • t) = c • Lm t := by
  ext i j
  rw [Matrix.smul_apply, Complex.real_smul]
  obtain ⟨P, rfl⟩ := (posE k r).surjective i
  obtain ⟨Q, rfl⟩ := (posE k r).surjective j
  rcases P with a | c | a <;> rcases Q with b | c' | b <;>
    simp only [posE_apply, pos, Lm_ee, Lm_ew, Lm_es, Lm_we, Lm_ww, Lm_ws, Lm_se, Lm_sw, Lm_ss, mul_zero]
  · by_cases hab : a < b
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]; simp [Complex.real_smul]
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab), mul_zero]
  · simp [cB, Complex.real_smul]
  · unfold cK
    split_ifs
    · simp [Complex.real_smul]
    · simp only [Prod.smul_fst, Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
        Complex.conj_ofReal]; ring
    · simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul]; push_cast; ring
  · simp only [cB, Prod.smul_fst, Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
      Complex.conj_ofReal]; ring
  · by_cases hab : b < a
    · rw [chart_matrix_upper _ hab, chart_matrix_upper _ hab]
      simp only [Prod.smul_fst, Pi.smul_apply, Complex.real_smul, star_mul', Complex.star_def,
        Complex.conj_ofReal]; ring
    · rw [chart_matrix_lower _ (not_lt.1 hab), chart_matrix_lower _ (not_lt.1 hab)]; simp

theorem toC_add (y y' : J k r → ℝ) : toC (y + y') = toC y + toC y' := by
  ext i
  · rfl
  · rfl

theorem toC_smul (c : ℝ) (y : J k r → ℝ) : toC (c • y) = c • toC y := by
  ext i
  · apply Complex.ext <;> simp [toC]
  · rfl

def LJ : (J k r → ℝ) →ₗ[ℝ] Mx k r where
  toFun y := Lm (toC y)
  map_add' y y' := by rw [toC_add, Lm_add]
  map_smul' c y := by rw [toC_smul, Lm_smul]; rfl

theorem LJ_apply (y : J k r → ℝ) : LJ y = Lm (toC y) := rfl

theorem continuous_LJ : Continuous (LJ (k := k) (r := r)) := LinearMap.continuous_of_finiteDimensional _

end Formalism.L2.SG.Pf.NcReal.JX.EC
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSKfOrb
section
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.KfOrbPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol NumberField IsDedekindDomain
  MeasureTheory Topology Filter
open Formalism.L2.SG.Pf.NcS.FinVolSk
open scoped TensorProduct

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem ev_int (x : F) : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, (algebraMap F (Fv F v) x) ∈ v.adicCompletionIntegers F :=
  (algebraMap F (Af F) x).2

theorem int_smul_mem {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (M : ℤ) (hM : M ≠ 0)
    (hMv : algebraMap F (Fv F v) ((M : F)⁻¹) ∈ v.adicCompletionIntegers F)
    (S : Submodule (v.adicCompletionIntegers F) (Fin n → Fv F v ⊗[F] E)) (y : Fin n → Fv F v ⊗[F] E)
    (hy : M • y ∈ S) : y ∈ S := by
  have h1 : algebraMap F (Fv F v) ((M : F)⁻¹) * algebraMap F (Fv F v) (M : F) = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (Int.cast_ne_zero.2 hM), map_one]
  have e : y = (⟨algebraMap F (Fv F v) ((M : F)⁻¹), hMv⟩ : v.adicCompletionIntegers F) • (M • y) := by
    show y = algebraMap F (Fv F v) ((M : F)⁻¹) • (M • y)
    rw [← Int.cast_smul_eq_zsmul (Fv F v) M y, smul_smul, ← map_intCast (algebraMap F (Fv F v)) M, h1, one_smul]
  rw [e]
  exact S.smul_mem _ hy

theorem ev_latLoc_std {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, latLoc (E := E) v (L : Set (Fin n → E)) =
      latLoc (E := E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  obtain ⟨N, hN0, hN⟩ := MassDataMassesW.KCptW.std_mult L hL.span_eq_top
  obtain ⟨N', hN'0, hN'⟩ := MassDataMassesW.KCptW.lat_mult L hL.fg
  filter_upwards [ev_int ((N : F)⁻¹), ev_int ((N' : F)⁻¹)] with v hv hv'
  apply le_antisymm
  · intro y hy
    exact int_smul_mem v N' hN'0 hv' _ y (MassDataMassesW.KCptW.zsmul_mem_latLoc_of _ _ N' hN' v hy)
  · intro y hy
    exact int_smul_mem v N hN0 hv _ y (MassDataMassesW.KCptW.zsmul_mem_latLoc_of _ _ N hN v hy)

theorem mem_oev_of_std {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (y : Fin n → Fv F v ⊗[F] E)
    (hy : y ∈ latLoc (E := E) v
      ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))) (i : Fin n) :
    y i ∈ OEv (E := E) v := by
  show y i ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨μ, hμ, rfl⟩ := hz
    obtain ⟨o, ho⟩ := LinearMap.mem_range.1 ((Submodule.mem_pi.1 hμ) i (Set.mem_univ _))
    show inclR (Fv F v) (μ i) ∈ _
    rw [← ho]
    exact Submodule.subset_span ⟨o, trivial, rfl⟩
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul c a _ ha => exact Submodule.smul_mem _ c ha

theorem entries_oev {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (g : GL (Fin n) (Fv F v ⊗[F] E))
    (hg : g ∈ Kloc (E := E) v ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)))
    (i j : Fin n) : (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) i j ∈ OEv (E := E) v := by
  classical
  have he : ratV (F := F) (Fv F v) (Pi.single j (1 : E)) ∈ latLoc (E := E) v
      ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) :=
    Submodule.subset_span ⟨_, MassDataMassesW.KCptW.single_mem_std j, rfl⟩
  have h2 := (hg _).1 he
  have e1 : ratV (F := F) (Fv F v) (Pi.single j (1 : E)) = Pi.single j 1 := by
    funext k
    by_cases h : k = j
    · subst h; simp [ratV, inclR, Algebra.TensorProduct.one_def]
    · simp [ratV, inclR, Pi.single_apply, h]
  rw [e1] at h2
  have h3 := mem_oev_of_std v _ h2 i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h3

variable [FiniteDimensional F E]

theorem ev_crd_oev {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ z ∈ OEv (E := E) v, ∀ l,
      PI.VolStabS.PositiveNearLattice.crd b (Fv F v) z l ∈ v.adicCompletionIntegers F := by
  classical
  let B := NumberField.RingOfIntegers.basis E
  filter_upwards [eventually_all.2 fun t => eventually_all.2 fun l =>
    ev_int (F := F) (b.repr ((B t : 𝓞 E) : E) l)] with v hv
  have hgen : ∀ (o : 𝓞 E) (l : Fin d),
      PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (inclR (F := F) (Fv F v) (o : E)) l ∈
        v.adicCompletionIntegers F := by
    intro o l
    have hcrd : ∀ e : E, PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (inclR (F := F) (Fv F v) e) l =
        algebraMap F (Fv F v) (b.repr e l) := by
      intro e
      simp [PI.VolStabS.PositiveNearLattice.crd, inclR, Algebra.TensorProduct.basis_repr_tmul]
    rw [hcrd]
    have ho : (o : E) = ∑ t, (B.repr o t) • ((B t : 𝓞 E) : E) := by
      have := congrArg (algebraMap (𝓞 E) E) (B.sum_repr o)
      rw [map_sum] at this
      simpa [map_zsmul] using this.symm
    rw [ho, map_sum, Finsupp.finset_sum_apply, map_sum]
    refine Subring.sum_mem _ fun t _ => ?_
    rw [map_zsmul, Finsupp.smul_apply, map_zsmul]
    exact Subring.zsmul_mem _ (hv t l) _
  intro z hz l
  change z ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hz
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨o, -, rfl⟩ := hy
    exact hgen o l
  | zero => simp [PI.VolStabS.PositiveNearLattice.crd]
  | add a c _ _ ha hc =>
    simp only [PI.VolStabS.PositiveNearLattice.crd, map_add, Finsupp.add_apply] at *
    exact Subring.add_mem _ ha hc
  | smul c a _ ha =>
    have e : PI.VolStabS.PositiveNearLattice.crd b (Fv F v) (c • a) l =
        (c : Fv F v) * PI.VolStabS.PositiveNearLattice.crd b (Fv F v) a l := by
      show (Algebra.TensorProduct.basis (Fv F v) b).repr ((c : Fv F v) • a) l = _
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
      rfl
    rw [e]
    exact Subring.mul_mem _ c.2 ha

theorem projV_eq_map (v : HeightOneSpectrum (𝓞 F)) {n : ℕ} (X : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :
    projV v X = X.map (tensMap (E := E) (evalV F v)) := rfl

end SlopeTestRemainingChoices

theorem finite_orbit_holds : KfOrb := by
  intro F E _ _ _ _ _ σ n J a X0 Λ hCM hJ hLat
  classical
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨L, hL, rfl⟩ := hLat
  let b := Module.finBasis F E
  set Y := ratTup (F := F) (Af F) X0 with hYdef
  obtain ⟨hKc, -⟩ := Formalism.L2.SG.Pf.NcS.AdTupPf.kf_compact_open σ J L hL
  have hmat : Continuous (fun g : HA (Af F) σ J =>
      ((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E))) :=
    Units.continuous_val.comp continuous_subtype_val
  have hact : Continuous (fun g : HA (Af F) σ J => g • Y) := by
    refine continuous_pi fun c => ?_
    show Continuous (fun g : HA (Af F) σ J =>
      ((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).mulVec (Y c))
    exact hmat.matrix_mulVec continuous_const

  have hcomp : ∀ (v : HeightOneSpectrum (𝓞 F)) (g : HA (Af F) σ J),
      projV v (g • Y) = (((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map
        (tensMap (E := E) (evalV F v))).mulVec ∘ (fun c => ratTup (F := F) (Fv F v) X0 c) := by
    intro v g
    funext c i
    change tensMap (E := E) (evalV F v)
        (((HA.mat (Af F) σ J g : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).mulVec (Y c) i) = _
    rw [RingHom.map_mulVec]
    congr 1
  refine ⟨?_, fun x => ⟨?_, ?_⟩⟩
  ·
    have : T2Space (Af F ⊗[F] E) := PI.VolStabS.RestrProdG.t2_tensor_product (Af F)
    have e : {x : Fin a → Fin n → Af F ⊗[F] E | ∃ k ∈ Kf σ J (L : Set (Fin n → E)), x = k • ratTup (Af F) X0} =
        (fun g : HA (Af F) σ J => g • Y) '' (Kf σ J (L : Set (Fin n → E)) : Set (HA (Af F) σ J)) := by
      ext x
      constructor
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
      · rintro ⟨k, hk, rfl⟩; exact ⟨k, hk, rfl⟩
    rw [e]
    exact (hKc.image hact).isClosed.measurableSet
  ·
    rintro ⟨k, hk, rfl⟩ v
    refine ⟨haMap σ J (evalV F v) k, ?_, ?_⟩
    · have h1 : k ∈ (Kloc (E := E) v (L : Set (Fin n → E))).comap ((compV v).comp (incAf σ J)) :=
        (Subgroup.mem_iInf.1 hk) v
      exact h1
    · rw [hcomp v k]
      rfl
  ·
    intro hx
    choose kv hkv hxv using hx
    have hgoodV : ∀ᶠ v in cofinite, ∀ g : GL (Fin n) (Fv F v ⊗[F] E),
        g ∈ Kloc (E := E) v (L : Set (Fin n → E)) →
          (g : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) ∈ latV (M := n) (n := n) b v := by
      filter_upwards [ev_latLoc_std L hL, ev_crd_oev b] with v hv hc
      intro g hg i j l
      have hg' : g ∈ Kloc (E := E) v
          ((MassDataMassesW.KCptW.stdSub : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
        intro y; rw [← hv]; exact hg y
      exact hc _ (entries_oev v g hg' i j) l
    let mat : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := fun v =>
      ((HA.mat (Fv F v) σ J (kv v) : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    let imat : ∀ v : HeightOneSpectrum (𝓞 F), Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E) := fun v =>
      (((HA.mat (Fv F v) σ J (kv v))⁻¹ : GL (Fin n) (Fv F v ⊗[F] E)) : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))
    have hK1 : ∀ v, HA.mat (Fv F v) σ J (kv v) ∈ Kloc (E := E) v (L : Set (Fin n → E)) := hkv
    have hg1 : ∀ᶠ v in cofinite, mat v ∈ latV b v :=
      hgoodV.mono fun v h => h _ (hK1 v)
    have hg2 : ∀ᶠ v in cofinite, imat v ∈ latV b v :=
      hgoodV.mono fun v h => h _ ((Kloc (E := E) v (L : Set (Fin n → E))).inv_mem (hK1 v))
    obtain ⟨Γ, -, hΓ⟩ := PI.VolStabS.rpGlue_holds F E n n _ b
    let A : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) := projFin (Γ (0, mat))
    let A' : Matrix (Fin n) (Fin n) (Af F ⊗[F] E) := projFin (Γ (0, imat))
    have hA : ∀ v, A.map (tensMap (E := E) (evalV F v)) = mat v := (hΓ (0, mat) hg1).2
    have hA' : ∀ v, A'.map (tensMap (E := E) (evalV F v)) = imat v := (hΓ (0, imat) hg2).2
    have hAA' : A * A' = 1 := by
      refine Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_
      rw [projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hA']
      exact Units.mul_inv (HA.mat (Fv F v) σ J (kv v))
    have hA'A : A' * A = 1 := by
      refine Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_
      rw [projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _), hA, hA']
      exact Units.inv_mul (HA.mat (Fv F v) σ J (kv v))
    let gGL : GL (Fin n) (Af F ⊗[F] E) := ⟨A, A', hAA', hA'A⟩
    have hcT : ∀ v (X : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)),
        (Formalism.UG.cT (sigR (Af F) σ) X).map (tensMap (E := E) (evalV F v)) =
          Formalism.UG.cT (sigR (Fv F v) σ) (X.map (tensMap (E := E) (evalV F v))) := by
      intro v X
      ext i j
      simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
      exact PI.VolStabS.RestrProdG.map_sigR (evalV F v) σ (X j i)
    have hJR : ∀ v, (JR (Af F) J).map (tensMap (E := E) (evalV F v)) = JR (Fv F v) J := by
      intro v
      ext i j
      exact PI.VolStabS.RestrProdG.map_inclR (evalV F v) (J i j)
    have hmem : gGL ∈ HR (Af F) σ J := by
      show Formalism.UG.cT (sigR (Af F) σ) A * JR (Af F) J * A = JR (Af F) J
      refine Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_
      rw [projV_eq_map, projV_eq_map, Matrix.map_mul, Matrix.map_mul, hcT, hJR, hA]
      exact (kv v).2
    let k : HA (Af F) σ J := (⟨gGL, hmem⟩ : HR (Af F) σ J)
    refine ⟨k, ?_, ?_⟩
    · refine Subgroup.mem_iInf.2 fun v => ?_
      show ∀ y, y ∈ latLoc (E := E) v (L : Set (Fin n → E)) ↔
        Matrix.mulVec (((compV v (incAf σ J k)) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) y ∈ latLoc (E := E) v (L : Set (Fin n → E))
      have e : (((compV v (incAf σ J k)) : GL (Fin n) (Fv F v ⊗[F] E)) :
          Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) = mat v := hA v
      rw [e]
      exact hK1 v
    · refine Formalism.L2.SG.Pf.NcS.OmDecompPf.projV_ext b fun v => ?_
      rw [hxv v, hcomp v k]
      have e : (((HA.mat (Af F) σ J k : GL (Fin n) (Af F ⊗[F] E)) : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)).map
          (tensMap (E := E) (evalV F v))) = mat v := hA v
      rw [e]
      rfl

end Formalism.L2.SG.Pf.NcS.KfOrbPf
end
end

