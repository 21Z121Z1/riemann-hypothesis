import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0036
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0934
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0125
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0949
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingZeroMeanNormalizedSubgroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPartMul
section
noncomputable section

namespace GlobalTheory.OrbDesc

variable {H : Type} [Group H]

theorem locPart_mul {T L : Subgroup H} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : GlobalTheory.LKLoc.locPart T L (t * x * l) = GlobalTheory.LKLoc.locPart T L x := by
  unfold GlobalTheory.LKLoc.locPart
  ext g
  simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l * k * l⁻¹, L.mul_mem (L.mul_mem hl hk) (L.inv_mem hl), ?_⟩
    calc x * (l * k * l⁻¹) * x⁻¹ = t⁻¹ * ((t * x * l * k * (t * x * l)⁻¹) * t) := by group
      _ = t⁻¹ * (t * (t * x * l * k * (t * x * l)⁻¹)) := by rw [hT _ hg t ht]
      _ = t * x * l * k * (t * x * l)⁻¹ := by group
  · rintro ⟨hg, k, hk, rfl⟩
    refine ⟨hg, l⁻¹ * k * l, L.mul_mem (L.mul_mem (L.inv_mem hl) hk) hl, ?_⟩
    have := hT _ hg t ht
    calc t * x * l * (l⁻¹ * k * l) * (t * x * l)⁻¹ = t * (x * k * x⁻¹) * t⁻¹ := by group
      _ = (x * k * x⁻¹) * t * t⁻¹ := by rw [← this]
      _ = x * k * x⁻¹ := by group

theorem wt_mul {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) {t x l : H} (ht : t ∈ T)
    (hl : l ∈ L) : wt T L U Ψ (t * x * l) = wt T L U Ψ x := by
  unfold wt
  rw [locPart_mul hT ht hl, hΨr l hl, hΨl t ht]

theorem wt_out {T L : Subgroup H} (U : Subgroup H) {Ψ : H → ℂ} (hT : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s)
    (hΨl : ∀ t ∈ T, ∀ x, Ψ (t * x) = Ψ x) (hΨr : ∀ l ∈ L, ∀ x, Ψ (x * l) = Ψ x) (x : H) :
    wt T L U Ψ (Quotient.out (DoubleCoset.mk T L x)) = wt T L U Ψ x := by
  obtain ⟨t, ht, l, hl, h⟩ := (DoubleCoset.eq T L _ _).1 (DoubleCoset.out_eq' T L (DoubleCoset.mk T L x))
  exact (wt_mul U hT hΨl hΨr ht hl).symm.trans (congrArg _ h.symm)

end GlobalTheory.OrbDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalOrderCompletionSurjectiveFromIntegralAdelesStatement
section
open IsDedekindDomain NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localOrderCompletion_surjective_from_integralAdeles : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E), a ∈ GlobalTheory.PlaceComp.ordAt E v → ∃ t ∈ GlobalTheory.PlaceComp.intA F E, GlobalTheory.PlaceComp.evF E v t = a := by
  first | exact @GlobalTheory.OrdLift.ordAt_lift | exact GlobalTheory.OrdLift.ordAt_lift | (intros; apply GlobalTheory.OrdLift.ordAt_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogIntegralUnitsSubgroupExpHomProofStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logIntegralUnitsSubgroupExpHom_proof : UnitSt := by
  first | exact @GlobalTheory.IsoTriv.unitSt | exact GlobalTheory.IsoTriv.unitSt | (intros; apply GlobalTheory.IsoTriv.unitSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmSumIntegralAdditiveStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logarithm_sum_integral_additive : AddSt := by
  first | exact @GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | exact GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality | (intros; apply GlobalTheory.IsoTriv.log_sum_additive_preserves_integrality <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogarithmicGroupLawSplitByIdempotent
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemImage

open MvPowerSeries
open ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.IndefiniteRowSideFullHecke.TypedPartSplitPrimes GlobalTheory.PrimePart

variable {C : Type} [Field C] {v : AddValuation C (WithTop ℝ)}

def lin {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) : Fin m → MvPowerSeries (Fin n) C :=
  fun a => ∑ b, N a b • X b

theorem lin_const {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) (a : Fin m) : constantCoeff (lin N a) = 0 := by
  simp [lin]

theorem lin_hs {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) : HasSubst (lin N) :=
  hasSubst_of_constantCoeff_zero (lin_const N)

theorem int_comb {σ ι : Type} [Fintype ι] {c : ι → C} (hc : ∀ i, IsIntV v (c i))
    {f : ι → MvPowerSeries σ C} (hf : ∀ i, MvIsInt v (f i)) : MvIsInt v (∑ i, c i • f i) :=
  (ptIntSer v σ).sum_mem fun i _ => ptIntSer_smul (hc i) (hf i)

theorem lin_int {m n : ℕ} {N : Matrix (Fin m) (Fin n) C} (h : ∀ a b, IsIntV v (N a b)) (a : Fin m) :
    MvIsInt v (lin N a) := int_comb (h a) fun b => ptIntSer_X b

theorem lin_coeff {m n : ℕ} (N : Matrix (Fin m) (Fin n) C) (a : Fin m) (i : Fin n) :
    coeff (Finsupp.single i 1) (lin N a) = N a i := by
  simp [lin, map_sum, pt_coeff_single_X]

theorem const_comb {σ ι : Type} [Fintype ι] (c : ι → C) {f : ι → MvPowerSeries σ C}
    (hf : ∀ i, constantCoeff (f i) = 0) : constantCoeff (∑ i, c i • f i) = 0 := by
  simp [hf]

theorem comb_comb {σ : Type} {l m n : ℕ} (A : Matrix (Fin l) (Fin m) C) (B : Matrix (Fin m) (Fin n) C)
    (f : Fin n → MvPowerSeries σ C) (b : Fin l) :
    ∑ a, A b a • ∑ e, B a e • f e = ∑ e, (A * B) b e • f e := by
  simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
  exact Finset.sum_comm

theorem comb_one {σ : Type} {n : ℕ} (f : Fin n → MvPowerSeries σ C) (b : Fin n) :
    ∑ e, (1 : Matrix (Fin n) (Fin n) C) b e • f e = f b := by
  simp [Matrix.one_apply, ite_smul]

theorem subst_lin {σ : Type} {m n : ℕ} {s : Fin n → MvPowerSeries σ C} (hs : HasSubst s)
    (N : Matrix (Fin m) (Fin n) C) (a : Fin m) : subst s (lin N a) = ∑ b, N a b • s b := by
  rw [lin, subst_sum_smul hs]
  simp only [subst_X hs]

theorem coeff_comb_lg {d m n : ℕ} (G : LogFGL v d) (N : Matrix (Fin m) (Fin d) C)
    (L : Matrix (Fin d) (Fin n) C) (a : Fin m) (i : Fin n) :
    coeff (Finsupp.single i 1) (∑ e, N a e • (subst (lin L) (G.lg e) : MvPowerSeries (Fin n) C)) = (N * L) a i := by
  simp [map_sum, pt_coeff_single_subst (lin_hs L) (lin_const L) (G.lg_const _), G.lg_lin, lin_coeff,
    Matrix.mul_apply]

theorem lg_add {σ : Type} [Finite σ] {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (a : Fin d) :
    subst (fun b => (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C)) (G.lg a) =
      subst x (G.lg a) + subst y (G.lg a) := by
  have hs : HasSubst (Sum.elim x y) := hasSubst_of_constantCoeff_zero (by rintro (b | b) <;> simp [hx, hy])
  have hl : HasSubst (fun b : Fin d => (X (Sum.inl b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  have hr : HasSubst (fun b : Fin d => (X (Sum.inr b) : MvPowerSeries (Fin d ⊕ Fin d) C)) :=
    hasSubst_of_constantCoeff_zero (fun _ => by simp)
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero G.F_const) hs, G.lg_F, subst_add hs,
    subst_comp_subst_apply hl hs, subst_comp_subst_apply hr hs]
  simp only [subst_X hs, Sum.elim_inl, Sum.elim_inr]

theorem add_const {σ : Type} {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0) (b : Fin d) :
    constantCoeff (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C) = 0 :=
  have h : ∀ s, constantCoeff (Sum.elim x y s) = 0 := by rintro (b | b) <;> simp [hx, hy]
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h) h (G.F_const b)

theorem add_int {σ : Type} {d : ℕ} (G : LogFGL v d) {x y : Fin d → MvPowerSeries σ C}
    (hx : ∀ a, constantCoeff (x a) = 0) (hy : ∀ a, constantCoeff (y a) = 0)
    (ix : ∀ a, MvIsInt v (x a)) (iy : ∀ a, MvIsInt v (y a)) (b : Fin d) :
    MvIsInt v (subst (Sum.elim x y) (G.F b) : MvPowerSeries σ C) :=
  have h : ∀ s, constantCoeff (Sum.elim x y s) = 0 := by rintro (b | b) <;> simp [hx, hy]
  ptIntSer_subst (hasSubst_of_constantCoeff_zero h) (by rintro (b | b); exacts [ix b, iy b]) (G.F_int b)

theorem lg_hom {σ : Type} {d m : ℕ} {f : MvPowerSeries (Fin d) C} {φ : Fin d → MvPowerSeries (Fin m) C}
    (h0 : ∀ a, constantCoeff (φ a) = 0) {c : Fin m → C} {g : Fin m → MvPowerSeries (Fin m) C}
    (h : subst φ f = ∑ a, c a • g a) {s : Fin m → MvPowerSeries σ C} (hs : HasSubst s) :
    subst (fun b => (subst s (φ b) : MvPowerSeries σ C)) f = ∑ a, c a • (subst s (g a) : MvPowerSeries σ C) := by
  rw [← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero h0) hs, h, subst_sum_smul hs]

theorem exists_retraction [CharZero C] {d d' : ℕ} (G : LogFGL v d) {I : Matrix (Fin d) (Fin d') C}
    {P : Matrix (Fin d') (Fin d) C} (hI : ∀ a b, IsIntV v (I a b)) (hP : ∀ a b, IsIntV v (P a b))
    (hPI : P * I = 1) {φ ψ : Fin d → MvPowerSeries (Fin d) C} (hφ : IsIntHom G G φ (I * P))
    (hψ : IsIntHom G G ψ (1 - I * P)) :
    ∃ q : Fin d' → MvPowerSeries (Fin d) C, (∀ b, constantCoeff (q b) = 0) ∧ (∀ b, MvIsInt v (q b)) ∧
      ∀ b, subst q (∑ a, P b a • (subst (lin I) (G.lg a) : MvPowerSeries (Fin d') C)) = ∑ a, P b a • G.lg a := by
  have hMi : ∀ a b, IsIntV v ((I * P) a b) := fun a b => by
    rw [Matrix.mul_apply]
    exact (ptIntSub v).sum_mem fun c _ => (ptIntSub v).mul_mem (hI a c) (hP c b)
  have hNi : ∀ a b, IsIntV v ((1 - I * P : Matrix (Fin d) (Fin d) C) a b) := fun a b => by
    rw [Matrix.sub_apply, Matrix.one_apply]
    refine (ptIntSub v).sub_mem ?_ (hMi a b)
    split_ifs
    exacts [(ptIntSub v).one_mem, (ptIntSub v).zero_mem]
  have hPM : P * (I * P) = P := by rw [← Matrix.mul_assoc, hPI, Matrix.one_mul]
  have hPN : P * (1 - I * P : Matrix (Fin d) (Fin d) C) = 0 := by rw [Matrix.mul_sub, hPM, Matrix.mul_one, sub_self]
  have hMM : I * P * (I * P) = I * P := by rw [Matrix.mul_assoc, hPM]
  have hsq : I * P * (I * P) + (1 - I * P : Matrix (Fin d) (Fin d) C) * (1 - I * P : Matrix (Fin d) (Fin d) C) = 1 := by
    rw [mul_sub, sub_mul, sub_mul, hMM]; simp
  generalize hM : I * P = M at *
  generalize (1 - M : Matrix (Fin d) (Fin d) C) = N at *
  set x : Fin d → MvPowerSeries (Fin d) C := fun a => subst (lin M) (φ a) with hx
  set y : Fin d → MvPowerSeries (Fin d) C := fun a => subst (lin N) (ψ a) with hy
  have x0 : ∀ a, constantCoeff (x a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs M) (lin_const M) (hφ.1 a)
  have y0 : ∀ a, constantCoeff (y a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs N) (lin_const N) (hψ.1 a)
  have xi : ∀ a, MvIsInt v (x a) := fun a => ptIntSer_subst (lin_hs M) (lin_int hMi) (hφ.2.1 a)
  have yi : ∀ a, MvIsInt v (y a) := fun a => ptIntSer_subst (lin_hs N) (lin_int hNi) (hψ.2.1 a)
  set Θ : Fin d → MvPowerSeries (Fin d) C := fun b => subst (Sum.elim x y) (G.F b) with hΘ
  have Θ0 : ∀ a, constantCoeff (Θ a) = 0 := add_const G x0 y0
  have Θs : HasSubst Θ := hasSubst_of_constantCoeff_zero Θ0
  have hlg : ∀ a, subst Θ (G.lg a) = ∑ e, M a e • (subst (lin M) (G.lg e) : MvPowerSeries (Fin d) C) +
      ∑ e, N a e • (subst (lin N) (G.lg e) : MvPowerSeries (Fin d) C) := fun a => by
    rw [hΘ, lg_add G x0 y0, hx, hy, lg_hom hφ.1 (hφ.2.2 a) (lin_hs M), lg_hom hψ.1 (hψ.2.2 a) (lin_hs N)]
  have Θ1 : ∀ a b, coeff (Finsupp.single b 1) (Θ a) = if a = b then 1 else 0 := fun a b => by
    have h := congrArg (coeff (Finsupp.single b 1)) (hlg a)
    rw [map_add, coeff_comb_lg, coeff_comb_lg, ← Matrix.add_apply, hsq, Matrix.one_apply,
      pt_coeff_single_subst Θs Θ0 (G.lg_const a)] at h
    simpa [G.lg_lin] using h
  obtain ⟨Ψ, Ψi, Ψ0, hΨ, -⟩ := GlobalTheory.IntInv.exists_int_inv C v d Θ (add_int G x0 y0 xi yi) Θ0 Θ1
  have Ψs : HasSubst Ψ := hasSubst_of_constantCoeff_zero Ψ0
  refine ⟨fun b => ∑ a, P b a • Ψ a, fun b => const_comb _ Ψ0, fun b => int_comb (hP b) Ψi, fun b => ?_⟩
  have key : subst (lin P) (∑ a, P b a • (subst (lin I) (G.lg a) : MvPowerSeries (Fin d') C)) =
      subst Θ (∑ a, P b a • G.lg a) := by
    have hl : (fun a => (subst (lin P) (lin I a) : MvPowerSeries (Fin d) C)) = lin M := by
      funext a
      rw [subst_lin (lin_hs P), ← hM]
      exact comb_comb I P _ a
    rw [subst_sum_smul (lin_hs P), subst_sum_smul Θs]
    simp only [hlg, smul_add, Finset.sum_add_distrib, comb_comb, hPM, hPN,
      subst_comp_subst_apply (lin_hs I) (lin_hs P), hl]
    simp
  have h := congrArg (subst Ψ) key
  rw [subst_comp_subst_apply (lin_hs P) Ψs, subst_comp_subst_apply Θs Ψs] at h
  simp only [subst_lin Ψs, hΨ] at h
  rw [h, show (fun a => (X a : MvPowerSeries (Fin d) C)) = X from rfl, subst_self]
  rfl

theorem exists_image (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d d' : ℕ) (G : LogFGL v d)
    (I : Matrix (Fin d) (Fin d') C) (P : Matrix (Fin d') (Fin d) C) (hI : ∀ a b, IsIntV v (I a b))
    (hP : ∀ a b, IsIntV v (P a b)) (hPI : P * I = 1) (hφ : ∃ φ, IsIntHom G G φ (I * P))
    (hψ : ∃ ψ, IsIntHom G G ψ (1 - I * P)) :
    ∃ G' : LogFGL v d', (∃ j, IsIntHom G' G j I) ∧ ∃ q, IsIntHom G G' q P := by
  obtain ⟨φ, hφ⟩ := hφ
  obtain ⟨ψ, hψ⟩ := hψ
  obtain ⟨q, q0, qi, hq⟩ := exists_retraction G hI hP hPI hφ hψ
  set lg' : Fin d' → MvPowerSeries (Fin d') C := fun b => ∑ a, P b a • subst (lin I) (G.lg a) with hlg'
  set j : Fin d → MvPowerSeries (Fin d') C := fun a => subst (lin I) (φ a) with hjdef
  have j0 : ∀ a, constantCoeff (j a) = 0 := fun a =>
    constantCoeff_subst_eq_zero (lin_hs I) (lin_const I) (hφ.1 a)
  have ji : ∀ a, MvIsInt v (j a) := fun a => ptIntSer_subst (lin_hs I) (lin_int hI) (hφ.2.1 a)
  have hj : ∀ a, subst j (G.lg a) = ∑ e, I a e • lg' e := fun a => by
    rw [hjdef, lg_hom hφ.1 (hφ.2.2 a) (lin_hs I), hlg']
    exact (comb_comb I P _ a).symm
  have hl0 : ∀ b : Fin d', constantCoeff (X (Sum.inl b) : MvPowerSeries (Fin d' ⊕ Fin d') C) = 0 := fun _ => by simp
  have hr0 : ∀ b : Fin d', constantCoeff (X (Sum.inr b) : MvPowerSeries (Fin d' ⊕ Fin d') C) = 0 := fun _ => by simp
  have hl := hasSubst_of_constantCoeff_zero hl0
  have hr := hasSubst_of_constantCoeff_zero hr0
  set x : Fin d → MvPowerSeries (Fin d' ⊕ Fin d') C := fun a => subst (fun b => X (Sum.inl b)) (j a) with hx
  set y : Fin d → MvPowerSeries (Fin d' ⊕ Fin d') C := fun a => subst (fun b => X (Sum.inr b)) (j a) with hy
  have x0 : ∀ a, constantCoeff (x a) = 0 := fun a => constantCoeff_subst_eq_zero hl hl0 (j0 a)
  have y0 : ∀ a, constantCoeff (y a) = 0 := fun a => constantCoeff_subst_eq_zero hr hr0 (j0 a)
  have xi : ∀ a, MvIsInt v (x a) := fun a => ptIntSer_subst hl (fun _ => ptIntSer_X _) (ji a)
  have yi : ∀ a, MvIsInt v (y a) := fun a => ptIntSer_subst hr (fun _ => ptIntSer_X _) (ji a)
  have s0 := add_const G x0 y0
  have ss := hasSubst_of_constantCoeff_zero s0
  refine ⟨{ lg := lg'
            lg_const := fun b => const_comb _ fun a =>
              constantCoeff_subst_eq_zero (lin_hs I) (lin_const I) (G.lg_const a)
            lg_lin := fun a b => by rw [hlg', coeff_comb_lg, hPI, Matrix.one_apply]
            F := fun b => subst (fun a => (subst (Sum.elim x y) (G.F a) : MvPowerSeries (Fin d' ⊕ Fin d') C)) (q b)
            F_int := fun b => ptIntSer_subst ss (add_int G x0 y0 xi yi) (qi b)
            F_const := fun b => constantCoeff_subst_eq_zero ss s0 (q0 b)
            lg_F := fun b => ?_ }, ⟨j, j0, ji, hj⟩, q, q0, qi, hq⟩
  rw [lg_hom q0 (hq b) ss]
  simp only [lg_add G x0 y0, smul_add, Finset.sum_add_distrib]
  simp only [hx, hy, lg_hom j0 (hj _) hl, lg_hom j0 (hj _) hr, comb_comb, hPI, comb_one]

end GlobalTheory.IdemImage
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapMulRightEqOfFundamentalDomain
section
open MeasureTheory
open scoped ENNReal NNReal

namespace GlobalTheory.ConjModulus

theorem map_mul_right_eq_of_fundamentalDomain {H : Type} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H]
    [MeasurableSpace H] [BorelSpace H] (Λ : Subgroup H) [Countable Λ] (ρ : Measure H)
    [ρ.IsHaarMeasure] (𝓡 : Set H) (h𝓡 : IsFundamentalDomain Λ 𝓡 ρ) (hfin : ρ 𝓡 ≠ ⊤) (x₀ : H) :
    ρ.map (· * x₀) = ρ := by
  haveI : (ρ.map (· * x₀)).IsHaarMeasure := Measure.isHaarMeasure_map_mul_right ρ x₀
  have hc := Measure.isMulLeftInvariant_eq_smul (ρ.map (· * x₀)) ρ
  set c := Measure.haarScalarFactor (ρ.map (· * x₀)) ρ
  have h' : IsFundamentalDomain Λ ((· * x₀) ⁻¹' 𝓡) ρ := by
    refine h𝓡.preimage_of_equiv (quasiMeasurePreserving_mul_right ρ x₀) (e := id)
      Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hm : ρ ((· * x₀) ⁻¹' 𝓡) = ρ 𝓡 := h'.measure_eq h𝓡
  have h0 : ρ 𝓡 ≠ 0 := h𝓡.measure_ne_zero (NeZero.ne ρ)
  have hmap : (ρ.map (· * x₀)) 𝓡 = ρ ((· * x₀) ⁻¹' 𝓡) :=
    MeasurableEquiv.map_apply (MeasurableEquiv.mulRight x₀) 𝓡
  have h1 : (c : ℝ≥0∞) * ρ 𝓡 = 1 * ρ 𝓡 := by
    calc (c : ℝ≥0∞) * ρ 𝓡 = (c • ρ) 𝓡 := by simp [Measure.smul_apply]
      _ = (ρ.map (· * x₀)) 𝓡 := by rw [hc]
      _ = 1 * ρ 𝓡 := by rw [one_mul]; exact hmap.trans hm
  have hc1 : c = 1 := by
    have := (ENNReal.mul_left_inj h0 hfin).1 h1
    exact_mod_cast this
  rw [hc, hc1, one_smul]

def conjB {H G : Type} [Group H] [Group G] (ι : H →* G) (B : Subgroup G)
    (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x : H) (b : B) : B :=
  ⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩

def conjCME {H G : Type} [Group H] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (ι : H →* G) (B : Subgroup G) (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x : H) :
    B ≃ₜ* B where
  toFun := conjB ι B hB x
  invFun := conjB ι B hB x⁻¹
  left_inv b := by apply Subtype.ext; simp [conjB, mul_assoc]
  right_inv b := by apply Subtype.ext; simp [conjB, mul_assoc]
  map_mul' a b := by apply Subtype.ext; simp [conjB, mul_assoc]
  continuous_toFun := continuous_induced_rng.2
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)
  continuous_invFun := continuous_induced_rng.2
    ((continuous_const.mul continuous_subtype_val).mul continuous_const)

theorem conjB_mul {H G : Type} [Group H] [Group G] (ι : H →* G) (B : Subgroup G)
    (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (x y : H) :
    conjB ι B hB (x * y) = conjB ι B hB x ∘ conjB ι B hB y := by
  funext b; apply Subtype.ext; simp [conjB, mul_assoc]

end GlobalTheory.ConjModulus

namespace GlobalTheory.ConjModulus

theorem map_conj_eq_self_of_lattice : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [LocallyCompactSpace H] [SecondCountableTopology H] [T2Space H] [MeasurableSpace H] [BorelSpace H] (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (ι : H →* G), Continuous ι → ∀ B : Subgroup G, IsClosed (B : Set G) →
    ∀ (hB : ∀ x : H, ∀ b ∈ B, ι x * b * (ι x)⁻¹ ∈ B) (β : Measure B), β.IsHaarMeasure →
    ∀ (Λ : Subgroup H) [Countable Λ] (ρ : Measure H) (𝓡 : Set H), ρ.IsHaarMeasure → IsFundamentalDomain Λ 𝓡 ρ → ρ 𝓡 ≠ ⊤ →
    (∀ x ∈ Λ, β.map (fun b : B => (⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩ : B)) = β) →
    ∀ x : H, β.map (fun b : B => (⟨ι x * b * (ι x)⁻¹, hB x b b.2⟩ : B)) = β := by
  intro H _ _ _ _ _ _ _ _ G _ _ _ _ _ _ _ _ ι hι B hBc hB β hβ Λ _ ρ 𝓡 hρ h𝓡 hfin hΛ
  haveI := hβ
  haveI := hρ
  haveI : LocallyCompactSpace B := hBc.locallyCompactSpace
  haveI : SecondCountableTopology B := TopologicalSpace.Subtype.secondCountableTopology (B : Set G)
  haveI : SigmaCompactSpace B := inferInstance
  haveI : SigmaFinite β := inferInstance
  have hΛ' : ∀ x ∈ Λ, β.map (conjB ι B hB x) = β := hΛ
  show ∀ x : H, β.map (conjB ι B hB x) = β
  have hφm : ∀ x, Measurable (conjB ι B hB x) := fun x => (conjCME ι B hB x).continuous.measurable
  have hHaar : ∀ x, (β.map (conjB ι B hB x)).IsHaarMeasure := fun x =>
    (conjCME ι B hB x).isHaarMeasure_map β
  obtain ⟨d, hdβ⟩ : ∃ d : H → ℝ≥0, ∀ x, β.map (conjB ι B hB x) = d x • β := ⟨fun x =>
    Measure.haarScalarFactor (β.map (conjB ι B hB x)) β, fun x => by
      haveI := hHaar x; exact Measure.isMulLeftInvariant_eq_smul _ _⟩
  obtain ⟨K, hKc, hK1⟩ := exists_compact_mem_nhds (1 : B)
  have hK0 : β K ≠ 0 := (Measure.measure_pos_of_mem_nhds β hK1).ne'
  have hKt : β K ≠ ⊤ := hKc.measure_lt_top.ne
  have hcancel : ∀ a b : ℝ≥0, a • β = b • β → a = b := by
    intro a b h
    have h2 : (a : ℝ≥0∞) * β K = (b : ℝ≥0∞) * β K := by
      have := congrArg (fun m : Measure B => m K) h
      simpa [Measure.smul_apply] using this
    exact_mod_cast (ENNReal.mul_left_inj hK0 hKt).1 h2
  have hmul : ∀ x y, d (x * y) = d x * d y := by
    intro x y
    apply hcancel
    rw [← hdβ, conjB_mul, ← Measure.map_map (hφm x) (hφm y), hdβ y, Measure.map_smul, hdβ x,
      smul_smul, mul_comm]
  have hdΛ : ∀ x ∈ Λ, d x = 1 := by
    intro x hx
    apply hcancel
    rw [← hdβ, hΛ' x hx, one_smul]
  have hpos : ∀ x, 0 < d x := by
    intro x
    rw [pos_iff_ne_zero]
    intro h0
    have h1 := congrArg (fun m : Measure B => m Set.univ) (hdβ x)
    simp only [h0, zero_smul, Measure.coe_zero, Pi.zero_apply] at h1
    rw [Measure.map_apply (hφm x) MeasurableSet.univ, Set.preimage_univ] at h1
    exact (Measure.measure_univ_pos.2 (NeZero.ne β)).ne' h1

  have hΦ : Continuous (fun p : H × B => conjB ι B hB p.1 p.2) :=
    continuous_induced_rng.2 (((hι.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd)).mul (hι.comp continuous_fst).inv)
  have hS : MeasurableSet ((fun p : H × B => conjB ι B hB p.1 p.2) ⁻¹' K) :=
    (hKc.isClosed.preimage hΦ).measurableSet
  have hDm : Measurable fun x => β (conjB ι B hB x ⁻¹' K) := measurable_measure_prodMk_left hS
  have hdK : ∀ x, (d x : ℝ≥0∞) = β (conjB ι B hB x ⁻¹' K) / β K := by
    intro x
    rw [ENNReal.eq_div_iff hK0 hKt, ← Measure.map_apply (hφm x) hKc.isClosed.measurableSet, hdβ x]
    simp [Measure.smul_apply, mul_comm]
  have hdm : Measurable d := by
    apply measurable_coe_nnreal_ennreal_iff.1
    simp_rw [hdK]
    exact hDm.div_const _

  obtain ⟨g, hgm, hgs, hg1⟩ : ∃ g : ℝ≥0 → ℝ≥0∞, Measurable g ∧
      (∀ a b : ℝ≥0, 0 < a → a < b → g a < g b) ∧ ∀ t, g t ≤ 1 := by
    refine ⟨fun t => ENNReal.ofReal ((t : ℝ) / (1 + t)), ?_, ?_, ?_⟩
    · exact (measurable_coe_nnreal_real.div (measurable_const.add measurable_coe_nnreal_real)).ennreal_ofReal
    · intro a b ha hab
      have ha' : (0 : ℝ) < a := ha
      have hab' : (a : ℝ) < b := hab
      have hb' : (0 : ℝ) < b := ha'.trans hab'
      have hpos' : (0 : ℝ) < (b : ℝ) / (1 + b) := div_pos hb' (by linarith)
      simp only
      rw [ENNReal.ofReal_lt_ofReal_iff hpos', div_lt_div_iff₀ (by linarith) (by linarith)]
      nlinarith
    · intro t
      apply ENNReal.ofReal_le_one.2
      rw [div_le_one (by positivity)]
      linarith

  have hR : ∀ x₀ : H, ρ.map (· * x₀) = ρ := map_mul_right_eq_of_fundamentalDomain Λ ρ 𝓡 h𝓡 hfin
  have hfΛ : ∀ (l : Λ) (z : H), g (d (l • z)) = g (d z) := by
    intro l z
    rw [Subgroup.smul_def, smul_eq_mul, hmul, hdΛ _ l.2, one_mul]
  have hshift : ∀ x₀ : H, ∫⁻ z in 𝓡, g (d z) ∂ρ = ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ := by
    intro x₀
    have hmp : MeasurePreserving (· * x₀) ρ ρ := ⟨measurable_mul_const x₀, hR x₀⟩
    have hemb : MeasurableEmbedding (· * x₀ : H → H) := (MeasurableEquiv.mulRight x₀).measurableEmbedding
    have h' : IsFundamentalDomain Λ ((· * x₀) '' 𝓡) ρ := by
      rw [Set.image_mul_right]
      refine h𝓡.preimage_of_equiv (quasiMeasurePreserving_mul_right ρ x₀⁻¹) (e := id)
        Function.bijective_id ?_
      intro l y
      simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
    have := (h𝓡.setLIntegral_eq h' (fun z => g (d z)) hfΛ).trans
      (hmp.setLIntegral_comp_emb hemb (fun z => g (d z)) 𝓡).symm
    simpa [hmul] using this
  have hne : ρ.restrict 𝓡 ≠ 0 := by
    rw [Ne, Measure.restrict_eq_zero]; exact h𝓡.measure_ne_zero (NeZero.ne ρ)
  have hfinI : ∀ c : ℝ≥0, ∫⁻ z in 𝓡, g (d z * c) ∂ρ ≠ ⊤ := by
    intro c
    refine ne_top_of_le_ne_top (b := ∫⁻ _ in 𝓡, 1 ∂ρ) ?_ (lintegral_mono fun z => hg1 _)
    rw [setLIntegral_const, one_mul]; exact hfin
  have hd1 : ∀ x, d x = 1 := by
    intro x₀
    by_contra hne1
    have hsh := hshift x₀
    rcases lt_or_gt_of_ne hne1 with hlt | hgt
    · have hlt' : ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ < ∫⁻ z in 𝓡, g (d z) ∂ρ := by
        refine lintegral_strict_mono hne (hgm.comp hdm).aemeasurable (hfinI _)
          (Filter.Eventually.of_forall fun z => ?_)
        exact hgs _ _ (mul_pos (hpos z) (hpos x₀)) (mul_lt_of_lt_one_right (hpos z) hlt)
      exact hlt'.ne hsh.symm
    · have hlt' : ∫⁻ z in 𝓡, g (d z) ∂ρ < ∫⁻ z in 𝓡, g (d z * d x₀) ∂ρ := by
        have h1 := hfinI 1
        simp only [mul_one] at h1
        refine lintegral_strict_mono hne ((hgm.comp (hdm.mul_const _))).aemeasurable h1
          (Filter.Eventually.of_forall fun z => ?_)
        exact hgs _ _ (hpos z) (lt_mul_of_one_lt_right (hpos z) hgt)
      exact hlt'.ne hsh
  intro x
  rw [hdβ x, hd1 x, one_smul]

end GlobalTheory.ConjModulus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixInductionTransvectionDiagonal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv

noncomputable section

namespace GlobalTheory.FormsLocus

theorem ΓSpecIso_inv_comp_specMap_appTop {W : Scheme.{0}} {A B : CommRingCat.{0}} (g : W ⟶ Spec B)
    (f : A ⟶ B) :
    (Scheme.ΓSpecIso A).inv ≫ (g ≫ Spec.map f).appTop =
      f ≫ (Scheme.ΓSpecIso B).inv ≫ g.appTop := by
  rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality]

theorem factors_quot_iff (Rg : Type) [CommRing Rg] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) Rg))
    (T : Scheme.{0}) (g : T ⟶ Sp (MvPolynomial (Fin n) Rg)) :
    (∃ w : T ⟶ Sp (MvPolynomial (Fin n) Rg ⧸ I),
      w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = g) ↔
      ∀ P ∈ I, GlobalTheory.FormsLocus.ringOf g P = 0 := by
  constructor
  · rintro ⟨w, rfl⟩ P hP
    have h := congrArg (fun k => k.hom P)
      (ΓSpecIso_inv_comp_specMap_appTop w (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h
    change ((w ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv.hom P)) = 0
    rw [h, Ideal.Quotient.eq_zero_iff_mem.2 hP, map_zero, map_zero]
  · intro h
    let φ : CommRingCat.of (MvPolynomial (Fin n) Rg) ⟶ Γ(T, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv ≫ g.appTop
    refine ⟨T.toSpecΓ ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.lift I φ.hom h)), ?_⟩
    rw [Category.assoc, ← Spec.map_comp]
    change T.toSpecΓ ≫ Spec.map φ = g
    apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin n) Rg))).inv,
      ΓSpecIso_inv_comp_specMap_appTop, Scheme.toSpecΓ_appTop, Iso.inv_hom_id, Category.comp_id]

end GlobalTheory.FormsLocus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixSpanLeRapidSpanStatement
section
open Classical MeasureTheory NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_span_le_rapid_span : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : GlobalTheory.CuspRep.CuspSub E a), GlobalTheory.JSW.mspan π ≤ GlobalTheory.JSW.rspan π := by
  first | exact @GlobalTheory.JSW.mspan_le_rspan | exact GlobalTheory.JSW.mspan_le_rspan | (intros; apply GlobalTheory.JSW.mspan_le_rspan <;> assumption)
end

