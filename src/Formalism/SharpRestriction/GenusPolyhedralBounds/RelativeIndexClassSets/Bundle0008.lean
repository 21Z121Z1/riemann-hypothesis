import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LargeConstantLeParamCube
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SubsingletonQuotientOfIdealEqTop
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0007
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.NormEuclideanEmbeddingEqNetNorm
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0007

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.DiscriminantPowEightLeSqrt
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

def q0N (T : ParamsT D L P) : ℕ := ⌈L.sc.b / (T.TO : ℝ)⌉₊

theorem f_ge (D : D7) : 8 ≤ D.R.f := by
  have he : 2 ≤ D.R.toFrame.e := D.host.two_le_e
  have hU : Nat.card (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ = 2 ^ (D.R.toFrame.e + 1) := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      show D.R.toFrame.e + 2 = (D.R.toFrame.e + 1) + 1 by ring, Nat.totient_prime_pow_succ Nat.prime_two]
    simp
  have hH : Nat.card (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one (by norm_num) (by simp)
  have hmul := Subgroup.card_mul_index (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ))
  rw [hU] at hmul
  have hidx : 2 ^ D.R.toFrame.e ≤ (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)).index := by
    have h2 : 2 ^ (D.R.toFrame.e + 1) = 2 * 2 ^ D.R.toFrame.e := by ring
    nlinarith
  have hsurj := Nat.card_le_card_of_surjective _ D.R.toFrame.projection_surjective_field
  have hcard : Nat.card (Additive (Formalism.FrobeniusOrbits.HGrp D.R.toFrame.e)) =
      (Subgroup.zpowers (-1 : (ZMod (2 ^ (D.R.toFrame.e + 2)))ˣ)).index := rfl
  have hfin : Nat.card (Formalism.HC.Idx D.R.toFrame.ord) = D.R.toFrame.ord := by
    unfold Formalism.HC.Idx
    simp
  rw [hcard, hfin] at hsurj
  have h4 : 4 ≤ 2 ^ D.R.toFrame.e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ D.R.toFrame.e := Nat.pow_le_pow_right (by norm_num) he
  unfold Ranks.f Ranks.n
  omega

theorem r_ge (D : D7) : 6 ≤ D.R.r := by
  unfold Ranks.r
  have := D.R.two_le_m
  have := D.R.m_add_three_le_k
  omega

theorem r_le_2k (D : D7) : D.R.r ≤ 2 * D.R.k := by
  unfold Ranks.r
  have := D.R.m_add_three_le_k
  omega

theorem f_le_k (D : D7) : D.R.f ≤ D.R.k := by
  unfold Ranks.f Ranks.n
  exact D.R.f_le_k

theorem one_le_L (L : SizeData₂ D) : 1 ≤ L.sc.L := by
  unfold Scale.L
  exact Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem b_pos (L : SizeData₂ D) : 0 < L.sc.b := by
  unfold Scale.b
  exact Real.exp_pos _

theorem A_le_Z (L : SizeData₂ D) : (D.R.f : ℝ) * D.R.r ≤ zBase L := by
  unfold zBase
  exact le_mul_of_one_le_right (by positivity) (one_le_L L)

theorem zBase_pow_twelve_le (T : ParamsT D L P) (hZ : 1 ≤ zBase L) : zBase L ^ 12 ≤ T.PP := by
  rw [T.PP_eq]
  have h1 : zBase L ^ (12 : ℕ) = zBase L ^ (12 : ℝ) := by
    rw [show (12 : ℝ) = ((12 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have h2 : zBase L ^ (12 : ℝ) ≤ zBase L ^ T.eP := Real.rpow_le_rpow_of_exponent_le hZ T.eP_ge
  have h3 : 0 ≤ zBase L ^ T.eP := Real.rpow_nonneg (by linarith) _
  have h4 : 1 * zBase L ^ T.eP ≤ T.CP * zBase L ^ T.eP := mul_le_mul_of_nonneg_right T.one_le_CP h3
  rw [h1]
  linarith

theorem discriminant_pow_eight_le_sqrt (P : ParameterChoice' D L) (S : SizesAt L) : D.host.rdE ^ 8 ≤ L.sc.b ^ ((1 : ℝ) / 2) := by
  obtain ⟨-, -, -, -, ⟨ht1, -⟩, -, hQD, -⟩ := S
  obtain ⟨-, -, -, -, -, -, hrd1, hrd2⟩ := hQD
  have hc := P.condE_le
  simp only [Formalism.BasicNotions.LevelStarExponents.condE] at hc
  push_cast at hc
  have hq : (1 : ℝ) ≤ D.host.q := by
    have := D.host.qd_big.1
    exact_mod_cast (by omega : 1 ≤ D.host.q)
  have hd : (1 : ℝ) ≤ D.host.d := by
    have := D.host.qd_big.2
    exact_mod_cast (by omega : 1 ≤ D.host.d)
  have hQS : (1 : ℝ) ≤ D.host.QS := by exact_mod_cast D.host.QS_pos
  have hqd : (1 : ℝ) ≤ (D.host.q : ℝ) * D.host.d := by nlinarith
  have hs0 : 0 ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) := Real.sqrt_nonneg _
  have hsq : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ (D.host.q : ℝ) * D.host.d := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hC1 : (1 : ℝ) ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by nlinarith
  have hrdC : D.host.rdE ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by
    have h1 : (D.host.QS : ℝ) / 2 * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) := by nlinarith
    have h2 : (D.host.QS : ℝ) * Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤
        (D.host.QS : ℝ) * ((D.host.q : ℝ) * D.host.d) := mul_le_mul_of_nonneg_left hsq (by linarith)
    nlinarith
  have h8 : D.host.rdE ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8 :=
    pow_le_pow_left₀ (by linarith) hrdC 8
  have h36 : ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 8 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 :=
    pow_le_pow_right₀ hC1 (by norm_num)
  have ht : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht1
  have hpos : 0 ≤ ((D.host.QS : ℝ) * D.host.q * D.host.d) ^ 36 := by positivity
  nlinarith

theorem rn_of (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) :
    Rn ((D.R.f : ℝ) * D.R.r) D.R.k L.sc.b (L.sc.b ^ ((1 : ℝ) / 2)) T.PP T.TO D.host.rdE D.R.r ((T.Dp : ℝ) + 2) T.nWn T.nP
      (q0N T) := by
  have hf8 : (8 : ℝ) ≤ D.R.f := by exact_mod_cast f_ge D
  have hr6 : (6 : ℝ) ≤ D.R.r := by exact_mod_cast r_ge D
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast f_le_k D
  have hr2k : (D.R.r : ℝ) ≤ 2 * D.R.k := by exact_mod_cast r_le_2k D
  have hz1 : (1 : ℝ) ≤ zBase L := le_trans (by norm_num) hZ
  have hz12 := zBase_pow_twelve_le T hz1
  have hAZ := A_le_Z L
  have hzz2 : zBase L ^ 2 ≤ zBase L ^ 12 := by
    first
    | exact pow_le_pow_right₀ hz1 (by norm_num)
    | exact pow_le_pow_right hz1 (by norm_num)
  have hPPA : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ T.PP := by
    have h1 : (10 : ℝ) ^ 60 * ((D.R.f : ℝ) * D.R.r) ≤ zBase L * zBase L :=
      mul_le_mul hZ hAZ (by positivity) (by linarith)
    nlinarith
  have hTO40 := T.TO_40
  have hTOpos : (0 : ℝ) < T.TO := by exact_mod_cast (by omega : 0 < T.TO)
  have hb := b_pos L
  have hrd1 : (1 : ℝ) ≤ D.host.rdE := by
    have hd : (1 : ℝ) ≤ |(NumberField.discr D.host.E : ℝ)| := by
      have h := NumberField.discr_ne_zero D.host.E
      have h' : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs h
      exact_mod_cast h'
    unfold Host.rdE
    exact Real.one_le_rpow hd (by positivity)
  have hnW : 40 ≤ T.nWn := by
    have h1 := T.nW_lo.1
    have h2 := f_ge D
    have h3 := r_ge D
    have h4 : 8 * 6 ≤ D.R.f * D.R.r := Nat.mul_le_mul h2 h3
    have h5 : D.R.f * D.R.r ≤ D.R.f * D.R.r * (D.R.r + 1) := by
      first
      | exact Nat.le_mul_of_pos_right _ (by omega)
      | exact Nat.le_mul_of_pos_right (by omega)
    generalize D.R.f * D.R.r * (D.R.r + 1) = X at *
    generalize D.R.f * D.R.r = Y at *
    omega
  have hq0lo : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℕ) := by
    unfold q0N
    have h := Nat.le_ceil (L.sc.b / T.TO)
    have e : (T.TO : ℝ) * (L.sc.b / T.TO) = L.sc.b := by
      field_simp
    calc L.sc.b = (T.TO : ℝ) * (L.sc.b / T.TO) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left h hTOpos.le
  have hq0hi : (T.TO : ℝ) * (q0N T : ℕ) ≤ L.sc.b + T.TO := by
    unfold q0N
    have h := Nat.ceil_lt_add_one (div_nonneg hb.le hTOpos.le)
    have e : (T.TO : ℝ) * (L.sc.b / T.TO + 1) = L.sc.b + T.TO := by
      field_simp
      try ring
    have := mul_le_mul_of_nonneg_left h.le hTOpos.le
    linarith
  exact
    { forty_eight_le_constant := by nlinarith
      k8 := by linarith
      Ak := by nlinarith [mul_le_mul hfk hr2k (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      sb_sq := by
        rw [← Real.sqrt_eq_rpow]
        exact Real.mul_self_sqrt hb.le
      PPA := hPPA
      h32 := T.precision_cube_order_sq_le_sqrt
      hTP := T.TO_PP'
      one_le_order_alt := by exact_mod_cast (by omega : 1 ≤ T.TO)
      rd1 := hrd1
      rd8 := discriminant_pow_eight_le_sqrt P S
      r6 := hr6
      rA := by nlinarith
      two_le_degree_alt := by have : (0 : ℝ) ≤ T.Dp := Nat.cast_nonneg _; linarith
      W := by exact_mod_cast T.TO_nW
      forty_mul_degree_le_order := by exact_mod_cast T.TO_40
      forty_le_weight_count := by exact_mod_cast hnW
      projectivePointSizes := Nat.cast_nonneg _
      nPW := by exact_mod_cast T.nW_lo.2.2
      q0lo := hq0lo
      q0hi := hq0hi }

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module ComplexConjugate

namespace Formalism.MainNotions.Gaps.NetNorms

variable {D : D7} {B : WeightFamilies.Prov D} {j : ℕ} {ka : WeightFamilies.Wt D j}

namespace NetData

variable (Nt : NetData B j ka)

theorem inner_euclideanEmbedding_eq_average (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) :
    inner ℂ (Nt.e0 σ F) (Nt.e0 σ G) =
      (((Fintype.card (Nt.NN σ) : ℝ)⁻¹ : ℝ) : ℂ) * ∑ y, conj (Nt.ev σ y F) * Nt.ev σ y G := by
  classical
  rw [PiLp.inner_apply, Fintype.sum_sigma, Finset.sum_eq_single σ]
  · have hc : (((Fintype.card (Nt.NN σ) : ℝ)⁻¹ : ℝ) : ℂ) = ((Nt.cf σ : ℝ) : ℂ) * ((Nt.cf σ : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Nt.cf_sq]
    rw [hc, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [Nt.goodRowsProjector_apply_eq_sum, if_true, RCLike.inner_apply, map_mul, Complex.conj_ofReal]
    ring
  · intro τ _ h
    simp [Nt.goodRowsProjector_apply_eq_sum, h]
  · simp

def herm : Formalism.MainNotions.Gaps.SizeBoundsAlt.Herm (fun σ => Nt.netN σ) (Fintype.card (Σ τ : B.KO →+* ℂ, Nt.NN τ)) where
  e σ := (LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (Fintype.equivFin (Σ τ : B.KO →+* ℂ, Nt.NN τ))).toLinearEquiv.toLinearMap.comp
    (Nt.e0 σ)
  norm_e σ F := by
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
      LinearIsometryEquiv.norm_map, Nt.norm_euclideanEmbedding_eq_netNorm]

theorem herm_inner (σ : B.KO →+* ℂ) (F G : B.Cusp j ka) :
    inner ℂ (Nt.herm.e σ F) (Nt.herm.e σ G) = inner ℂ (Nt.e0 σ F) (Nt.e0 σ G) := by
  simp only [herm, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv,
    LinearIsometryEquiv.inner_map_map]

theorem herm_conj : Nt.herm.Conj := by
  intro σ f g
  rw [Nt.herm_inner, Nt.herm_inner, Nt.inner_euclideanEmbedding_eq_average, Nt.inner_euclideanEmbedding_eq_average]
  rw [← Fintype.card_congr (Nt.cj σ), ← (Nt.cj σ).sum_comp]
  simp only [Nt.ev_conj, Complex.conj_conj, star_mul', Complex.star_def, Complex.conj_ofReal, map_sum, map_mul]

end NetData

theorem sup_L2_bound_of_net : SupL2BoundFromNet (D := D) (B := B) (j := j) (ka := ka) := by
  intro Nt hM hL large₂ CG AG hP F σ
  rw [Nt.Bp_L2N_run hM hL]
  change B.supN j ka σ F ^ 2 ≤ _ * Nt.netN σ F ^ 2
  obtain ⟨y, hy⟩ := hM σ F
  have hS := B.supN_nonneg j ka σ F
  have hn : (1 : ℝ) ≤ (Fintype.card (Nt.NN σ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Fintype.card_pos_iff.mpr ⟨y⟩).ne'
  have hsum0 : (0 : ℝ) ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : Nt.netN σ F ^ 2 = (Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
    Real.sq_sqrt (mul_nonneg (inv_nonneg.mpr (by linarith)) hsum0)
  have h1 : ‖Nt.ev σ y F‖ ^ 2 ≤ ∑ y, ‖Nt.ev σ y F‖ ^ 2 :=
    Finset.single_le_sum (f := fun y => ‖Nt.ev σ y F‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ y)
  have h2 : (B.supN j ka σ F / 4) ^ 2 ≤ ‖Nt.ev σ y F‖ ^ 2 := pow_le_pow_left₀ (by positivity) hy 2
  have h3 : B.supN j ka σ F ^ 2 ≤ 16 * (Fintype.card (Nt.NN σ) : ℝ) * Nt.netN σ F ^ 2 := by
    rw [hsq]
    have : 16 * (Fintype.card (Nt.NN σ) : ℝ) * ((Fintype.card (Nt.NN σ) : ℝ)⁻¹ * ∑ y, ‖Nt.ev σ y F‖ ^ 2) =
        16 * ∑ y, ‖Nt.ev σ y F‖ ^ 2 := by
      field_simp
    rw [this]
    have h4 : (B.supN j ka σ F / 4) ^ 2 = B.supN j ka σ F ^ 2 / 16 := by ring
    linarith
  have h4 : 16 * (Fintype.card (Nt.NN σ) : ℝ) ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) := by
    rw [← Real.exp_log (by positivity : (0 : ℝ) < 16 * (Fintype.card (Nt.NN σ) : ℝ))]
    exact Real.exp_le_exp.mpr (hP σ)
  calc B.supN j ka σ F ^ 2 ≤ 16 * (Fintype.card (Nt.NN σ) : ℝ) * Nt.netN σ F ^ 2 := h3
    _ ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) * Nt.netN σ F ^ 2 :=
      mul_le_mul_of_nonneg_right h4 (sq_nonneg _)

theorem deepHermNet : DeepHermNetSt (D := D) (B := B) (j := j) (ka := ka) := by
  intro P Nt hM hL X
  exact ⟨_, { e := Nt.herm.e, norm_e := fun σ F => (Nt.herm.norm_e σ F).trans (by rw [Nt.Bp_L2N_run hM hL]) },
    Nt.herm_conj⟩

theorem deepLogDNet : DeepLogDNetSt (D := D) (B := B) (j := j) (ka := ka) := by
  intro P Nt hM hL X σ Pd hI hP
  change Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd
  have hd : finrank B.KO (B.Cusp j ka) ≤ Fintype.card (Nt.NN σ) := by
    have hb := hI _ _ (Module.finBasis B.KO (B.Cusp j ka)).linearIndependent
    have := hb.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have hlog0 : 0 ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) := Real.log_natCast_nonneg _
  rcases Nat.eq_zero_or_pos (finrank B.KO (B.Cusp j ka)) with h0 | h0
  · rw [h0]
    simp only [Nat.cast_zero, Real.log_zero]
    linarith
  · calc Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Real.log (Fintype.card (Nt.NN σ) : ℝ) :=
          Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast hd)
      _ ≤ Pd := hP

end Formalism.MainNotions.Gaps.NetNorms
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IntegralFormsEqSpan
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module TensorProduct

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

theorem comap_span_of_subset {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M] [Module R M] [SMul R S]
    [IsScalarTower R S M] (p : Submodule S M) (s : Set M) (hs : s ⊆ p) :
    (Submodule.span R s).comap (p.subtype.restrictScalars R) = Submodule.span R ((↑) ⁻¹' s : Set ↥p) := by
  apply Submodule.map_injective_of_injective (f := p.subtype.restrictScalars R) Subtype.val_injective
  rw [Submodule.map_comap_eq, Submodule.map_span]
  have h : (p.subtype.restrictScalars R) '' ((↑) ⁻¹' s : Set ↥p) = s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact hy
    · intro hx; exact ⟨⟨x, hs hx⟩, hx, rfl⟩
  rw [h, inf_eq_right, Submodule.span_le]
  intro x hx
  exact ⟨⟨x, hs hx⟩, rfl⟩

theorem mem_span_subtype_iff {R S M : Type*} [CommRing R] [CommRing S] [AddCommGroup M] [Module S M] [Module R M] [SMul R S]
    [IsScalarTower R S M] (p : Submodule S M) (s : Set ↥p) (x : ↥p) :
    x ∈ Submodule.span R s ↔ (x : M) ∈ Submodule.span R ((↑) '' s : Set M) := by
  have h : Submodule.span R ((↑) '' s : Set M) = (Submodule.span R s).map (p.subtype.restrictScalars R) := by
    rw [Submodule.map_span]; rfl
  rw [h]
  constructor
  · intro hx; exact ⟨x, hx, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

theorem isBaseChange_span {K K' V : Type*} [Field K] [Field K'] [Algebra K K'] [AddCommGroup V] [Module K V]
    (W : Submodule K V) (p : Submodule K' (K' ⊗[K] V))
    (hp : p = Submodule.span K' ((fun v => (1 : K') ⊗ₜ[K] v) '' (W : Set V)))
    (f : ↥W →ₗ[K] ↥p) (hf : ∀ w, (f w : K' ⊗[K] V) = (1 : K') ⊗ₜ[K] (w : V)) : IsBaseChange K' f := by
  have hg : ∀ x : K' ⊗[K] ↥W, ((f.liftBaseChange K' x : ↥p) : K' ⊗[K] V) = W.subtype.baseChange K' x := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul s w =>
      rw [LinearMap.liftBaseChange_tmul, LinearMap.baseChange_tmul, Submodule.coe_smul, hf, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
      rfl
    | add x y hx hy => rw [map_add, map_add, Submodule.coe_add, hx, hy]
  have hbij : Function.Bijective (f.liftBaseChange K') := by
    constructor
    · intro x y hxy
      have h1 : W.subtype.baseChange K' x = W.subtype.baseChange K' y := by rw [← hg, ← hg, hxy]
      exact Module.Flat.lTensor_preserves_injective_linearMap (M := K') W.subtype Subtype.val_injective h1
    · rw [← LinearMap.range_eq_top, eq_top_iff]
      rintro ⟨y, hy⟩ -
      have hy' := hy
      rw [hp] at hy'
      induction hy' using Submodule.span_induction with
      | mem y h =>
        obtain ⟨w, hw, rfl⟩ := h
        refine ⟨(1 : K') ⊗ₜ[K] (⟨w, hw⟩ : ↥W), Subtype.ext ?_⟩
        rw [LinearMap.liftBaseChange_tmul, one_smul, hf]
      | zero => exact (LinearMap.range (f.liftBaseChange K')).zero_mem
      | add a b ha hb iha ihb =>
        exact (LinearMap.range (f.liftBaseChange K')).add_mem (iha (hp ▸ ha)) (ihb (hp ▸ hb))
      | smul r a ha ih => exact (LinearMap.range (f.liftBaseChange K')).smul_mem r (ih (hp ▸ ha))
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective (f.liftBaseChange K') hbij) (fun x => by simp)

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (ka : WeightFamilies.Wt D j)

def embV (F : B.Cusp j ka) : ↥(Vw X la N ka) := ⟨emb X la N (X.inc ka F), emb_mem_Vw X la N ka F⟩

theorem coe_embV (F : B.Cusp j ka) : (embV X la N ka F : Rp X la N) = emb X la N (X.inc ka F) := rfl

theorem jW_toW (F : B.Mlat j ka) : jW X la N ka (toW X la ka F) = embV X la N ka F := rfl

theorem inW_loc_eq_span (M : Submodule (𝓞 B.KO) X.Forms) (hM : M ≤ X.Msup ka) :
    T0.inW X ka la (X.loc la M) =
      Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F} := by
  unfold T0.inW PJ.loc
  rw [comap_span_of_subset (R := X.Ol la) (T0.WL X ka la) (X.bc la '' (M : Set X.Forms))]
  · congr 1
    ext x
    constructor
    · rintro ⟨F, hF, h⟩; exact ⟨F, hF, h.symm⟩
    · rintro ⟨F, hF, h⟩; exact ⟨F, hF, h.symm⟩
  · rintro _ ⟨F, hF, rfl⟩
    exact Submodule.subset_span ⟨F, hM hF, rfl⟩

theorem span_jW_inW (M : Submodule (𝓞 B.KO) X.Forms) (hM : M ≤ X.Msup ka) :
    Submodule.span (Op X la N) (jW X la N ka '' (T0.inW X ka la (X.loc la M) : Set ↥(T0.WL X ka la))) =
      Submodule.span (Op X la N) {f : ↥(Vw X la N ka) | ∃ F ∈ M, (f : Rp X la N) = emb X la N F} := by
  rw [inW_loc_eq_span X la ka M hM]
  have h1 : jW X la N ka '' (Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F} :
      Set ↥(T0.WL X ka la)) =
      ((Submodule.span (X.Ol la) {x : ↥(T0.WL X ka la) | ∃ F ∈ M, (x : X.Vl la) = X.bc la F}).map
        ((jW X la N ka).restrictScalars (X.Ol la)) : Set ↥(Vw X la N ka)) := rfl
  rw [h1, Submodule.map_span, Submodule.span_span_of_tower]
  congr 1
  ext f
  constructor
  · rintro ⟨x, ⟨F, hF, hx⟩, rfl⟩
    refine ⟨F, hF, ?_⟩
    show bcV X la N (x : X.Vl la) = _
    rw [hx, emb_eq_bcV]
  · rintro ⟨F, hF, hf⟩
    refine ⟨⟨X.bc la F, Submodule.subset_span ⟨F, hM hF, rfl⟩⟩, ⟨F, hF, rfl⟩, Subtype.ext ?_⟩
    rw [hf, emb_eq_bcV]
    rfl

theorem integralForms_eq_span : M1 X la N ka = Submodule.span (Op X la N) (Set.range fun F : B.Mlat j ka => embV X la N ka F) := by
  unfold M1 T0.MW
  rw [span_jW_inW X la N ka _ le_rfl]
  congr 1
  ext f
  constructor
  · rintro ⟨_, ⟨F, hF, rfl⟩, hf⟩
    exact ⟨⟨F, hF⟩, Subtype.ext hf.symm⟩
  · rintro ⟨F, rfl⟩
    exact ⟨_, ⟨F, F.2, rfl⟩, rfl⟩

theorem Th1_eq (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T : ℕ) (h : X.Theta S ka wL wF T ≤ X.Msup ka) :
    Th1 X la N ka S wL wF T = Submodule.span (Op X la N)
      {f : ↥(Vw X la N ka) | ∃ F ∈ X.Theta S ka wL wF T, (f : Rp X la N) = emb X la N F} :=
  span_jW_inW X la N ka _ h

theorem jW_isBaseChange (hM : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤) :
    IsBaseChange (Kp X la N) (jW X la N ka) := by
  have hp : Vw X la N ka = Submodule.span (Kp X la N) ((fun v => bcV X la N v) '' (T0.WL X ka la : Set (X.Vl la))) := by
    refine le_antisymm ?_ ?_
    · rw [Vw_eq_span_image X la N ka hM]
      refine Submodule.span_mono ?_
      rintro _ ⟨F, hF, rfl⟩
      exact ⟨X.bc la (X.inc ka F), Submodule.subset_span ⟨X.inc ka F, ⟨F, hF, rfl⟩, rfl⟩, rfl⟩
    · rw [Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      exact bcV_mem_Vw X la N ka hx
  exact isBaseChange_span (K := X.Kl la) (K' := Kp X la N) (V := X.Vl la) (T0.WL X ka la) (Vw X la N ka) hp
    (jW X la N ka) (fun w => rfl)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

