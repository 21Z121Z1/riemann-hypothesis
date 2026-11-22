import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.Bundle0001

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSLoc
section
noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Field

variable {K : Type} [Field K]

def Dm (Δ : K) : Subring (Matrix (Fin 2) (Fin 2) (Lsq K Δ)) where
  carrier := {m | m 1 1 = star (m 0 0) ∧ m 1 0 = - star (m 0 1)}
  mul_mem' {a b} ha hb := by
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1, h2, h3, h4] <;> ring
  one_mem' := by simp
  add_mem' {a b} ha hb := by
    obtain ⟨h1, h2⟩ := ha
    obtain ⟨h3, h4⟩ := hb
    constructor <;> simp [h1, h2, h3, h4, add_comm]
  zero_mem' := by simp
  neg_mem' {a} ha := by
    obtain ⟨h1, h2⟩ := ha
    constructor <;> simp [h1, h2]

variable {Δ : K}

theorem mem_Dm {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} : m ∈ Dm Δ ↔ m 1 1 = star (m 0 0) ∧ m 1 0 = - star (m 0 1) := Iff.rfl

theorem mem_DX {g : GL (Fin 2) (Lsq K Δ)} : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) ∈ Dm Δ := by
  have e : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map star =
      !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
    change GeneralLinearGroup.map (starRingEnd (Lsq K Δ)) g = (wJ Δ)⁻¹ * g * (wJ Δ)⁻¹⁻¹ ↔ _
    rw [inv_inv, Units.ext_iff]
    rfl
  rw [e, mem_Dm, ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.map_apply]
  simp
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact ⟨h1.symm, by rw [h2, neg_neg]⟩
  · rintro ⟨h1, h2⟩
    simp [h1, h2]

theorem mt_mem (g : DX Δ) : mt g ∈ Dm Δ := mem_DX.1 g.2

theorem det_Dm {m : Matrix (Fin 2) (Fin 2) (Lsq K Δ)} (h : m ∈ Dm Δ) :
    m.det = algebraMap K _ ((m 0 0).re ^ 2 - Δ * (m 0 0).im ^ 2 + (m 0 1).re ^ 2 - Δ * (m 0 1).im ^ 2) := by
  rw [Matrix.det_fin_two, h.1, h.2]
  ext <;> simp [sq] <;> ring

variable {O : Type} [CommRing O] [Algebra O K]

theorem mem_KD {g : DX Δ} : g ∈ KD Δ O ↔ (∀ i j, IsIntegral O (mt g i j)) ∧ ∀ i j, IsIntegral O (mt g⁻¹ i j) := by
  constructor
  · rintro ⟨u, hu⟩
    have hu' : GeneralLinearGroup.map ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ) u⁻¹ = (g⁻¹ : DX Δ) := by
      rw [map_inv, hu]; rfl
    refine ⟨fun i j => ?_, fun i j => ?_⟩
    · have : mt g i j = (u i j : Lsq K Δ) := by
        change (g : GL (Fin 2) (Lsq K Δ)) i j = _
        have hu2 : (g : GL (Fin 2) (Lsq K Δ)) = _ := hu.symm
        rw [hu2]; rfl
      rw [this]; exact (u i j).2
    · have : mt g⁻¹ i j = ((u⁻¹ : GL (Fin 2) _) i j : Lsq K Δ) := by
        change ((g⁻¹ : DX Δ) : GL (Fin 2) (Lsq K Δ)) i j = _
        rw [← hu']; rfl
      rw [this]; exact ((u⁻¹ : GL (Fin 2) _) i j).2
  · rintro ⟨h1, h2⟩
    have inj : Function.Injective (fun m : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) =>
        ((integralClosure O (Lsq K Δ)).val : integralClosure O (Lsq K Δ) →+* Lsq K Δ).mapMatrix m) :=
      Matrix.map_injective Subtype.val_injective
    let a : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := Matrix.of fun i j => ⟨_, h1 i j⟩
    let b : Matrix (Fin 2) (Fin 2) (integralClosure O (Lsq K Δ)) := Matrix.of fun i j => ⟨_, h2 i j⟩
    refine ⟨⟨a, b, inj ?_, inj ?_⟩, Units.ext rfl⟩
    · simp only [map_mul, map_one]
      exact (g : GL (Fin 2) (Lsq K Δ)).mul_inv
    · simp only [map_mul, map_one]
      exact (g : GL (Fin 2) (Lsq K Δ)).inv_mul

theorem isIntegral_star {a : Lsq K Δ} (h : IsIntegral O a) : IsIntegral O (star a) := by
  let f : Lsq K Δ →ₐ[O] Lsq K Δ := { starRingEnd (Lsq K Δ) with
    commutes' := fun r => by
      change star (algebraMap O (Lsq K Δ) r) = _
      rw [IsScalarTower.algebraMap_apply O K (Lsq K Δ)]
      ext <;> simp }
  exact h.map f

theorem isIntegral_coords {a : Lsq K Δ} (h : IsIntegral O a) {m : K} (hm : IsIntegral O m) (hmΔ : IsIntegral O (m * Δ)) :
    IsIntegral O (2 * m * Δ * a.re) ∧ IsIntegral O (2 * m * Δ * a.im) := by
  have inj : Function.Injective (algebraMap K (Lsq K Δ)) := fun x y h => by simpa using congrArg QuadraticAlgebra.re h
  have h1 : IsIntegral O (2 * a.re) := by
    rw [← isIntegral_algebraMap_iff inj]
    convert h.add (isIntegral_star h) using 1
    ext <;> simp; ring
  have h2 : IsIntegral O (Δ * (2 * a.im) ^ 2) := by
    rw [← isIntegral_algebraMap_iff inj]
    convert (h.sub (isIntegral_star h)).pow 2 using 1
    ext <;> simp [sq] <;> ring
  refine ⟨by rw [show 2 * m * Δ * a.re = m * Δ * (2 * a.re) by ring]; exact hmΔ.mul h1, ?_⟩
  refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
  rw [show (2 * m * Δ * a.im) ^ 2 = m * (m * Δ) * (Δ * (2 * a.im) ^ 2) by ring]
  exact (hm.mul hmΔ).mul h2

theorem isIntegral_of_coords {a : Lsq K Δ} {m : K} (hm : IsIntegral O m) (hmΔ : IsIntegral O (m * Δ))
    (h1 : IsIntegral O a.re) (h2 : IsIntegral O a.im) : IsIntegral O (algebraMap K (Lsq K Δ) m * a) := by
  have h3 : IsIntegral O (⟨0, m⟩ : Lsq K Δ) := by
    refine IsIntegral.of_pow (n := 2) (by norm_num) ?_
    convert (hm.mul hmΔ).algebraMap (B := Lsq K Δ) using 1
    ext <;> simp [sq]; ring
  convert ((hm.mul h1).algebraMap (B := Lsq K Δ)).add (h3.mul (h2.algebraMap (B := Lsq K Δ))) using 1
  ext <;> simp

end Field

section Global

variable {F : Type} [Field F] [NumberField F]

theorem isIntegral_Ov {v : Pl F} {t : Kv v} : IsIntegral (Ov v) t ↔ t ∈ v.adicCompletionIntegers F := by
  rw [IsIntegrallyClosed.isIntegral_iff]
  constructor
  · rintro ⟨y, rfl⟩; exact y.2
  · intro h; exact ⟨⟨t, h⟩, rfl⟩

theorem isIntegral_glob {t : F} : IsIntegral ℤ t ↔ ∀ v : Pl F, IsIntegral (Ov v) (cv v t) := by
  simp only [isIntegral_Ov]
  constructor
  · intro h v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v (⟨t, h⟩ : 𝓞 F)
  · intro h
    obtain ⟨y, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 F) F t fun v => by
      have := h v
      rw [HeightOneSpectrum.mem_adicCompletionIntegers] at this
      rw [← HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v t]
      exact this
    exact y.2

theorem exists_nat_mul (t : F) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral ℤ ((n : F) * t) := by
  obtain ⟨m, hm0, hm⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ F).2
    (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) t)).exists_integral_multiple
  refine ⟨m.natAbs, Int.natAbs_ne_zero.2 hm0, ?_⟩
  rw [zsmul_eq_mul] at hm
  rcases Int.natAbs_eq m with h | h
  · rw [h] at hm; simpa using hm
  · rw [h] at hm; simpa using hm.neg

theorem exists_nat_mul_loc (v : Pl F) (t : Kv v) : ∃ n : ℕ, n ≠ 0 ∧ IsIntegral (Ov v) ((n : Kv v) * t) := by
  obtain ⟨b, hb, h⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v t
  have hb0 : (b : F) ≠ 0 := by simpa using nonZeroDivisors.ne_zero hb
  obtain ⟨n, hn, h2⟩ := exists_nat_mul (b : F)⁻¹
  refine ⟨n, hn, ?_⟩
  have h' : IsIntegral (Ov v) (t * cv v (b : F)) := isIntegral_Ov.2 h
  have := (isIntegral_glob.1 h2 v).mul h'
  rwa [map_mul, map_natCast, mul_assoc, mul_left_comm _ t, ← map_mul, inv_mul_cancel₀ hb0, map_one, mul_one] at this

theorem exists_nat_mul_L {Δ : F} (v : Pl F) (a : Lsq (Kv v) (cv v Δ)) :
    ∃ n : ℕ, n ≠ 0 ∧ IsIntegral (Ov v) ((n : Lsq (Kv v) (cv v Δ)) * a) := by
  obtain ⟨m, hm, h⟩ := exists_nat_mul Δ
  obtain ⟨n1, hn1, h1⟩ := exists_nat_mul_loc v a.re
  obtain ⟨n2, hn2, h2⟩ := exists_nat_mul_loc v a.im
  refine ⟨m * (n1 * n2), by positivity, ?_⟩
  have := isIntegral_of_coords (O := Ov v) (a := ((n1 * n2 : ℕ) : Lsq (Kv v) (cv v Δ)) * a) (m := (m : Kv v))
    (isIntegral_natCast _) (by simpa using isIntegral_glob.1 h v)
    (by simpa [mul_assoc, mul_left_comm] using (isIntegral_natCast n2).mul h1)
    (by simpa [mul_assoc] using (isIntegral_natCast n1).mul h2)
  convert this using 1
  simp [mul_assoc]

theorem den_DA {Δ : F} (g : DA Δ) : ∃ n : ℕ, n ≠ 0 ∧ ∀ v i j, IsIntegral (Ov v) ((n : Lsq (Kv v) (cv v Δ)) * mt (g.1 v) i j) := by
  classical
  have hf : {v : Pl F | ¬ g.1 v ∈ KD (cv v Δ) (Ov v)}.Finite := g.2
  choose n hn h using fun (v : Pl F) (p : Fin 2 × Fin 2) => exists_nat_mul_L v (mt (g.1 v) p.1 p.2)
  refine ⟨∏ v ∈ hf.toFinset, ∏ p, n v p, Finset.prod_ne_zero_iff.2 fun v _ => Finset.prod_ne_zero_iff.2 fun p _ => hn v p,
    fun v i j => ?_⟩
  by_cases hv : g.1 v ∈ KD (cv v Δ) (Ov v)
  · exact (isIntegral_natCast _).mul ((mem_KD.1 hv).1 i j)
  · obtain ⟨k, hk⟩ := (Finset.dvd_prod_of_mem (n v) (Finset.mem_univ (i, j))).trans
      (Finset.dvd_prod_of_mem (fun v => ∏ p, n v p) (hf.mem_toFinset.2 hv))
    rw [hk, Nat.cast_mul, mul_comm (n v (i, j) : Lsq (Kv v) (cv v Δ)), mul_assoc]
    exact (isIntegral_natCast _).mul (h v (i, j))

end Global

end UpperTheory.V.Z.Sym.Glob
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.FinSTest
section
namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc

section Generic

variable {I G : Type} [Group G] {Gv : I → Type} [∀ v, Group (Gv v)] {K : ∀ v, Subgroup (Gv v)} (P : RPG G Gv K)

private theorem mem_box (U : ∀ v, Subgroup (Gv v)) (g : G) : g ∈ P.box U ↔ ∀ v, P.p v g ∈ U v := by
  simp [RPG.box, Subgroup.mem_iInf]

end Generic

variable {F : Type} [Field F] [NumberField F] {Δ : F}

theorem normOneLevel_le_maximalCompact (D : Dat Δ) (h : D.Ok) : D.U2 ≤ (rpg _ _).box fun v => KD (cv v Δ) (Ov v) := by
  intro g hg
  rw [Dat.U2, mem_box] at hg
  rw [mem_box]
  intro v
  have hv' := hg v
  unfold Dat.J2v at hv'
  split_ifs at hv' with hv
  · exact (h.sig v hv).levelTwoLeIntegral hv'
  · exact hv'

theorem relIndex_normOneLevel_maximalCompact_ne_zero (D : Dat Δ) (h : D.Ok) : D.U2.relIndex ((rpg _ _).box fun v => KD (cv v Δ) (Ov v)) ≠ 0 := by
  set L := (rpg (fun v => ↥(DX (cv v Δ))) fun v => KD (cv v Δ) (Ov v)).box fun v => KD (cv v Δ) (Ov v) with hL
  set M := ⨅ v : (D.Sg : Set (Pl F)), Subgroup.comap ((rpg (fun v => ↥(DX (cv v Δ))) fun v => KD (cv v Δ) (Ov v)).p v) (D.S v).J2 with hM
  have hsub : L ⊓ M ≤ D.U2 := by
    intro g hg
    rw [Subgroup.mem_inf] at hg
    obtain ⟨hgL, hgM⟩ := hg
    rw [hL, mem_box] at hgL
    rw [hM, Subgroup.mem_iInf] at hgM
    rw [Dat.U2, mem_box]
    intro v
    unfold Dat.J2v
    split_ifs with hv
    · exact hgM ⟨v, hv⟩
    · exact hgL v
  have hMne : M.relIndex L ≠ 0 := by
    rw [hM]
    haveI : Finite (D.Sg : Set (Pl F)) := D.Sg.finite_toSet.to_subtype
    apply Subgroup.relIndex_iInf_ne_zero
    rintro ⟨v, hv⟩
    rw [Subgroup.relIndex_comap]
    have hmap : Subgroup.map ((rpg (fun v => ↥(DX (cv v Δ))) fun v => KD (cv v Δ) (Ov v)).p v) L ≤ KD (cv v Δ) (Ov v) := by
      rw [Subgroup.map_le_iff_le_comap]
      intro g hg
      rw [hL, mem_box] at hg
      exact hg v
    intro h0
    exact (h.sig v hv).levelTwoFiniteIndex (Subgroup.relIndex_eq_zero_of_le_right hmap h0)
  have hinf : (L ⊓ M).relIndex L ≠ 0 :=
    Subgroup.relIndex_inf_ne_zero (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hMne
  intro h0
  exact hinf (Subgroup.relIndex_eq_zero_of_le_left hsub h0)

private theorem conj_mul {G : Type} [Group G] (x a b : G) : x⁻¹ * (a * b) * x = x⁻¹ * a * x * (x⁻¹ * b * x) := by group

private theorem fs_mul_left_right_eq_of_mem_u2 (D : Dat Δ) (h : D.Ok) (t : Dat.Par F) (ht : D.Cone t) (a b : DA Δ) (ha : a ∈ D.U2) :
    D.FS t (a * b) = D.FS t b ∧ D.FS t (b * a) = D.FS t b := by
  rw [Dat.U2, mem_box] at ha
  constructor
  all_goals
    unfold Dat.FS
    apply finprod_congr
    intro v
    have hav := ha v
    change (a : ∀ v, ↥(DX (cv v Δ))) v ∈ Dat.J2v D v at hav
    unfold Dat.J2v at hav
    unfold Dat.fSv
    simp only [Subgroup.coe_mul, Pi.mul_apply]
    split_ifs at hav ⊢ with hv
  · exact ((h.sig v hv).S_inv (t v) (ht v hv) _ hav _).1
  · rw [Subgroup.mul_mem_cancel_left _ hav]
  · exact ((h.sig v hv).S_inv (t v) (ht v hv) _ hav _).2
  · rw [Subgroup.mul_mem_cancel_right _ hav]

private theorem fSv_apply_ne_zero_of_fs_ne_zero (D : Dat Δ) (t : Dat.Par F) (g : DA Δ) (hg : D.FS t g ≠ 0) (v : Pl F) :
    D.fSv t v ((g : ∀ v, ↥(DX (cv v Δ))) v) ≠ 0 := by
  intro h0
  apply hg
  unfold Dat.FS
  apply finprod_eq_zero _ v h0
  have hfin : {w | ¬ (g : ∀ v, ↥(DX (cv v Δ))) w ∈ KD (cv w Δ) (Ov w)}.Finite := Filter.eventually_cofinite.1 g.2
  apply ((D.Sg.finite_toSet.union hfin)).subset
  intro w hw
  rw [Function.mem_mulSupport] at hw
  by_contra hc
  simp only [Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq, not_or, not_not] at hc
  apply hw
  unfold Dat.fSv
  rw [if_neg hc.1]
  simp [one, hc.2]

set_option maxHeartbeats 1000000 in
theorem finS_test : ∀ (F : Type) [Field F] [NumberField F] (Δ : F) (D : Dat Δ), D.Ok → ∀ (V : Type) [AddCommGroup V] [Module ℂ V]
    (ch : F → ℂ) (x : DA Δ) (B : Base (SU Δ) (SA Δ) V), D.IsBS ch x B → ∀ t, D.Cone t → (Base.Tw.one B).IsTest (D.FSx t x) := by
  intro F _ _ Δ D hD V _ _ ch x B hB t ht
  refine ⟨?_, ?_, ?_⟩
  · intro u y
    rw [hB.ω]
    simp only [MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
    unfold Dat.FSx
    rw [Subgroup.coe_mul, conj_mul]
    exact (fs_mul_left_right_eq_of_mem_u2 D hD t ht _ _ ((hB.U u).1 u.2)).1
  · intro u y
    rw [hB.ω]
    simp only [MonoidHom.one_apply, inv_one, Units.val_one, one_mul]
    unfold Dat.FSx
    change D.FS t (x⁻¹ * ↑(y * ↑u) * x) = D.FS t (x⁻¹ * ↑y * x)
    rw [Subgroup.coe_mul, conj_mul]
    exact (fs_mul_left_right_eq_of_mem_u2 D hD t ht _ _ ((hB.U u).1 u.2)).2
  · change {q : ↥(SA Δ) ⧸ B.U | D.FSx t x (Quotient.out q) ≠ 0}.Finite
    have hc : ∀ (y : ↥(SA Δ)) (v : Pl F), ((x⁻¹ * ↑y * x : DA Δ) : ∀ v, ↥(DX (cv v Δ))) v ∈ SU (cv v Δ) := by
      intro y v
      have hy : (y : DA Δ) ∈ SA Δ := y.2
      unfold SA at hy
      rw [Subgroup.mem_iInf] at hy
      have hyv : ((y : DA Δ) : ∀ v, ↥(DX (cv v Δ))) v ∈ SU (cv v Δ) := hy v
      haveI : (SU (cv v Δ)).Normal := by
        unfold SU
        infer_instance
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Pi.mul_apply, Pi.inv_apply]
      exact Subgroup.Normal.conj_mem' inferInstance _ hyv _
    let Φ : ↥(SA Δ) ⧸ B.U → ((v : ↥D.Sg) → ↥(SU (cv v.1 Δ)) ⧸ (D.S v.1).J2.subgroupOf (SU (cv v.1 Δ))) :=
      fun q v => QuotientGroup.mk ⟨_, hc (Quotient.out q) v.1⟩
    have hT : (Set.univ.pi fun v : ↥D.Sg => {c : ↥(SU (cv v.1 Δ)) ⧸ (D.S v.1).J2.subgroupOf (SU (cv v.1 Δ)) |
        (D.S v.1).fS (t v.1) ((Quotient.out c : ↥(SU (cv v.1 Δ))) : ↥(DX (cv v.1 Δ))) ≠ 0}).Finite :=
      Set.Finite.pi fun v => (hD.sig v.1 v.2).S_fin (t v.1) (ht v.1 v.2)
    apply Set.Finite.of_finite_image (f := Φ)
    · apply hT.subset
      rintro _ ⟨q, hq, rfl⟩ v -
      obtain ⟨j, hj⟩ := QuotientGroup.mk_out_eq_mul ((D.S v.1).J2.subgroupOf (SU (cv v.1 Δ)))
        (⟨_, hc (Quotient.out q) v.1⟩ : ↥(SU (cv v.1 Δ)))
      show (D.S v.1).fS (t v.1) ((Quotient.out (QuotientGroup.mk _ : ↥(SU (cv v.1 Δ)) ⧸ _) : ↥(SU (cv v.1 Δ))) : ↥(DX (cv v.1 Δ))) ≠ 0
      rw [hj, Subgroup.coe_mul]
      have hjm : ((j : ↥(SU (cv v.1 Δ))) : ↥(DX (cv v.1 Δ))) ∈ (D.S v.1).J2 := Subgroup.mem_subgroupOf.1 j.2
      rw [((hD.sig v.1 v.2).S_inv (t v.1) (ht v.1 v.2) _ hjm _).2]
      have hne := fSv_apply_ne_zero_of_fs_ne_zero D t _ hq v.1
      unfold Dat.fSv at hne
      rw [if_pos v.2] at hne
      exact hne
    · intro q1 hq1 q2 hq2 heq
      rw [← QuotientGroup.out_eq' q1, ← QuotientGroup.out_eq' q2, QuotientGroup.eq, hB.U]
      have hsplit : x⁻¹ * ((((Quotient.out q1)⁻¹ * Quotient.out q2 : ↥(SA Δ))) : DA Δ) * x =
          (x⁻¹ * ↑(Quotient.out q1) * x)⁻¹ * (x⁻¹ * ↑(Quotient.out q2) * x) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hsplit, Dat.U2, mem_box]
      intro v
      have hk : ∀ q : ↥(SA Δ) ⧸ B.U, D.FSx t x (Quotient.out q) ≠ 0 → v ∉ D.Sg →
          ((x⁻¹ * ↑(Quotient.out q) * x : DA Δ) : ∀ v, ↥(DX (cv v Δ))) v ∈ KD (cv v Δ) (Ov v) := by
        intro q hq hv
        have hne := fSv_apply_ne_zero_of_fs_ne_zero D t _ hq v
        unfold Dat.fSv at hne
        rw [if_neg hv] at hne
        simpa [one] using hne
      have key : (((x⁻¹ * ↑(Quotient.out q1) * x : DA Δ) : ∀ v, ↥(DX (cv v Δ))) v)⁻¹ *
          ((x⁻¹ * ↑(Quotient.out q2) * x : DA Δ) : ∀ v, ↥(DX (cv v Δ))) v ∈ D.J2v v := by
        unfold Dat.J2v
        split_ifs with hv
        · have hv' := congrFun heq ⟨v, hv⟩
          simp only [Φ] at hv'
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hv'
          exact hv'
        · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hk q1 hq1 hv)) (hk q2 hq2 hv)
      exact key

end UpperTheory.V.Z.Sym.Glob
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.IntegralStabilizers.SideGTerm
section
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Loc

theorem UpperTheory.V.Z.Sym.Glob.sideGTerm :
    ∀ (Γ G V H : Type) [Group Γ] [Group G] [AddCommGroup V] [Module ℂ V] [Group H] (B : Base Γ G V), B.Fin →
    ∀ (s : B.Tw) (f : G → ℂ), s.IsTest f → B.ω = 1 → B.Γ₀ = ⊥ → ∀ (δ n : Γ) (i : H →* Γ), n ∉ i.range →
    (∀ x, x⁻¹ * δ * s.θΓ x = δ ↔ x ∈ i.range ∨ n * x ∈ i.range) → ∀ (U : Subgroup G) (H₀ : Subgroup H), B.U = U → i.ker = H₀ →
    2 * s.term f δ = LinearMap.trace ℂ V (B.W δ ∘ₗ s.Θ) * gqOn (B.ι.comp i) H₀ U (fun y => f (y.out⁻¹ * B.ι δ * s.θ y.out)) := by
  classical
  intro Γ G V H _ _ _ _ _ B hB s f hf hω hΓ δ n i hn hc U H₀ hU hH
  subst hU hH
  set C := s.Cent δ with hC
  have memC : ∀ x, x ∈ C ↔ x⁻¹ * δ * s.θΓ x = δ := by
    intro x
    constructor
    · rintro ⟨z, hz, h⟩
      rw [hΓ, Subgroup.mem_bot] at hz
      simpa [hz] using h
    · intro h
      exact ⟨1, one_mem _, by simpa using h⟩
  have hRC : ∀ x, x ∈ C ↔ x ∈ i.range ∨ n * x ∈ i.range := fun x => (memC x).trans (hc x)
  have hiC : ∀ h, i h ∈ C := fun h => (hRC _).2 (Or.inl ⟨h, rfl⟩)
  let φ : H →* C := i.codRestrict C hiC
  have hnC : n ∈ C := by
    have : n⁻¹ ∈ C := (hRC _).2 (Or.inr (by simp [one_mem]))
    simpa using C.inv_mem this
  have hφ : ∀ c : C, c ∈ φ.range ↔ (c : Γ) ∈ i.range := by
    intro c
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h, rfl⟩
    · rintro ⟨h, e⟩
      exact ⟨h, Subtype.ext e⟩
  have hidx : (φ.range ⊔ (⊥ : Subgroup C)).index = 2 := by
    rw [sup_bot_eq, Subgroup.index_eq_two_iff']
    refine ⟨⟨n, hnC⟩, fun b => ?_⟩
    rw [hφ, hφ]
    by_cases hb : (b : Γ) ∈ i.range
    · refine Or.inr ⟨hb, fun h => hn ?_⟩
      have := i.range.mul_mem h (i.range.inv_mem hb)
      simpa using this
    · refine Or.inl ⟨?_, hb⟩
      exact ((hRC _).1 b.2).resolve_left hb
  have hfl : ∀ (u : B.U) y, f (u * y) = f y := by
    intro u y
    rw [hf.left, hω]
    simp
  have hfr : ∀ (u : B.U) y, f (y * s.θ u) = f y := by
    intro u y
    rw [hf.right, hω]
    simp
  have kmk : ∀ g : G, s.ker f δ (g : G ⧸ B.U) = f (g⁻¹ * B.ι δ * s.θ g) := by
    intro g
    obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul B.U g
    have e : (g * (u : G))⁻¹ * B.ι δ * s.θ (g * (u : G)) = ((u⁻¹ : B.U) : G) * (g⁻¹ * B.ι δ * s.θ g * s.θ u) := by
      simp [mul_assoc]
    show f (_) = _
    rw [hu, e, hfl, hfr]
  have hk : ∀ (h : C) (y : G ⧸ B.U), s.ker f δ ((B.ι.comp C.subtype) h • y) = s.ker f δ y := by
    intro h y
    induction y using QuotientGroup.induction_on with
    | H g =>
      have e : (B.ι (h : Γ) * g)⁻¹ * B.ι δ * s.θ (B.ι (h : Γ) * g) =
          g⁻¹ * B.ι ((h : Γ)⁻¹ * δ * s.θΓ (h : Γ)) * s.θ g := by
        simp [s.comm, mul_assoc]
      show s.ker f δ ((B.ι (h : Γ) * g : G) : G ⧸ B.U) = _
      rw [kmk, kmk, e, (memC _).1 h.2]
  have hS : ∃ S : Finset (G ⧸ B.U), ∀ y, s.ker f δ y ≠ 0 → ∃ h, ∃ x ∈ S, y = (B.ι.comp C.subtype) h • x := by
    obtain ⟨S, hS⟩ := Tf.centFin Γ G V B hB s f hf δ
    refine ⟨Finset.image (QuotientGroup.mk : G → G ⧸ B.U) S, fun y hy => ?_⟩
    obtain ⟨t, x, hx, u, hu, e⟩ := hS y.out hy
    refine ⟨t, (x : G ⧸ B.U), Finset.mem_image_of_mem _ hx, ?_⟩
    calc y = ((y.out : G) : G ⧸ B.U) := (QuotientGroup.out_eq' y).symm
      _ = (((B.ι.comp C.subtype) t * x : G) : G ⧸ B.U) := by
        rw [e]
        exact QuotientGroup.mk_mul_of_mem _ hu
      _ = _ := rfl
  have hw : ∀ y : G ⧸ B.U, s.ker f δ y ≠ 0 →
      (⊥ : Subgroup C).relIndex ((MulAction.stabilizer G y).comap (B.ι.comp C.subtype)) ≠ 0 := by
    intro y _
    induction y using QuotientGroup.induction_on with
    | H g =>
      have h1 := hB.stab g
      rw [hΓ, Subgroup.relIndex_bot_left] at h1
      haveI := (Nat.card_ne_zero.1 h1).2
      rw [Subgroup.relIndex_bot_left, Nat.card_ne_zero]
      refine ⟨⟨1, one_mem _⟩, ?_⟩
      let m : ((MulAction.stabilizer G (g : G ⧸ B.U)).comap (B.ι.comp C.subtype)) →
          ((B.U.map (MulAut.conj g).toMonoidHom).comap B.ι) := fun c => ⟨(c.1 : Γ), by
        have h2 : (((B.ι (c.1 : Γ) * g : G)) : G ⧸ B.U) = (g : G ⧸ B.U) := c.2
        have h3 := QuotientGroup.eq.1 h2.symm
        exact ⟨_, h3, by simp [mul_assoc]⟩⟩
      refine Finite.of_injective m fun a b e => ?_
      exact Subtype.ext (Subtype.ext (congrArg (fun c => (c.1 : Γ)) e))
  have hz : ∀ z ∈ (⊥ : Subgroup C), ∀ y : G ⧸ B.U, (B.ι.comp C.subtype) z • y = y := by
    intro z hz y
    rw [Subgroup.mem_bot.1 hz]
    simp
  have key := Tf.gqIndex H C G φ (B.ι.comp C.subtype) ⊥ B.U (s.ker f δ) inferInstance hz
    (by rw [hidx]; norm_num) hk hS hw
  have e1 : (B.ι.comp C.subtype).comp φ = B.ι.comp i := by
    ext h
    rfl
  have e2 : (⊥ : Subgroup C).comap φ = i.ker := by
    ext h
    simp [φ, MonoidHom.mem_ker, Subtype.ext_iff]
  rw [e1, e2, hidx] at key
  have e3 : gqOn (B.ι.comp i) i.ker B.U (fun y => f (y.out⁻¹ * B.ι δ * s.θ y.out)) =
      gqOn (B.ι.comp i) i.ker B.U (s.ker f δ) := rfl
  rw [e3, key, Base.Tw.term, hΓ, Subgroup.bot_subgroupOf]
  push_cast
  ring
end

