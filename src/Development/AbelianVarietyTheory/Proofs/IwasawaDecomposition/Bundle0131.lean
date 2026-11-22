import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0110
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0014
import Formalism.LocalToGlobal.HermitianForms.Bundle0003
import Formalism.LocalToGlobal.Columns.RecLevelLocT

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RelativeLatticeDeterminantClassLaws
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Chr.RelDet

open IdlFact

section General

variable {L : Type} [Field L] [NumberField L]

def ordI (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : ℤ := -WithZero.log (valAt w a)

theorem valAt_eq (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : valAt w a = WithZero.exp (-ordI w a) := by
  rw [ordI, neg_neg, WithZero.exp_log (valAt_ne_zero w a)]

theorem ordI_mul (w : HeightOneSpectrum (𝓞 L)) (a b : Ideles L) : ordI w (a * b) = ordI w a + ordI w b := by
  unfold ordI
  rw [map_mul, WithZero.log_mul (valAt_ne_zero w a) (valAt_ne_zero w b)]
  ring

theorem ordI_inv (w : HeightOneSpectrum (𝓞 L)) (a : Ideles L) : ordI w a⁻¹ = -ordI w a := by
  unfold ordI
  rw [map_inv, WithZero.log_inv]

theorem ordI_diag (w : HeightOneSpectrum (𝓞 L)) (k : Lˣ) : ordI w (diagUnits L k) = ordF w k := by
  have h : valAt w (diagUnits L k) = w.valuation L (k : L) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w (k : L)
  rw [ordI, h, ordF]

def powI (n : HeightOneSpectrum (𝓞 L) → ℕ) : Ideles L :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 L), localIdele L w (atFin w (unif w)) ^ n w

theorem ordI_powI (n : HeightOneSpectrum (𝓞 L) → ℕ) (hn : {w | n w ≠ 0}.Finite) (w : HeightOneSpectrum (𝓞 L)) :
    ordI w (powI n) = n w := by
  classical
  have e : powI n = ∏ v ∈ hn.toFinset, localIdele L v (atFin v (unif v)) ^ (n v : ℤ) := by
    unfold powI
    rw [finprod_eq_prod_of_mulSupport_subset (s := hn.toFinset)]
    · simp only [zpow_natCast]
    · intro v hv
      by_contra h
      have h0 : n v = 0 := by simpa using h
      exact hv (by simp [h0])
  have h := valAt_prod hn.toFinset (fun v => (n v : ℤ)) w
  rw [ordI, e, h, WithZero.log_exp, neg_neg]
  split_ifs with hw
  · rfl
  · have h0 : n w = 0 := by simpa using hw
    simp [h0]

end General

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem mk_mk_eq {a b : Ideles H.E}
    (h : ∀ w w', IsConjPl H w w' → ordI w a - ordI w' a = ordI w b - ordI w' b) :
    (QuotientGroup.mk (QuotientGroup.mk a) : DtT H ⧸ UOT H) = QuotientGroup.mk (QuotientGroup.mk b) := by
  have h1 : a⁻¹ * b ∈ KD H ⊔ unitIdl H.E := by
    refine (GlobalTheory.Mem.Chr.mem_KD_sup_unitIdl_iff R H _).2 fun w w' hw => ?_
    rw [← valAt_apply, ← valAt_apply, valAt_eq, valAt_eq, ordI_mul, ordI_mul, ordI_inv, ordI_inv]
    have := h w w' hw
    congr 1
    omega
  obtain ⟨k, hk, u, hu, e⟩ := Subgroup.mem_sup.1 h1
  refine QuotientGroup.eq.2 ⟨u, hu, ?_⟩
  have hk1 : (QuotientGroup.mk k : DtT H) = 1 := (QuotientGroup.eq_one_iff k).2 hk
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← e, QuotientGroup.mk_mul, hk1, one_mul]
  rfl

def repI (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) : Ideles H.E :=
  powI fun w => (ordSub w (detSub M') - ordSub w (detSub M)).toNat

theorem relDetT_eq (N : ℕ) (M M' : Submodule (𝓞 H.E) (Fin N → H.E)) :
    relDetT H N M M' = QuotientGroup.mk (QuotientGroup.mk (repI H N M M')) := rfl

theorem ordI_repI (N : ℕ) : letI := H.cmStar; ∀ (M M' : SDLat H.E N) (w w' : HeightOneSpectrum (𝓞 H.E)),
    IsConjPl H w w' → ordI w (repI H N M.1 M'.1) - ordI w' (repI H N M.1 M'.1) =
      ordSub w (detSub M'.1) - ordSub w (detSub M.1) := by
  letI := H.cmStar
  intro M M' w w' hw
  have f1 := (ordSub_detSub_lattice H.E N M.1 M.2.1 M.2.2.1).1
  have f2 := (ordSub_detSub_lattice H.E N M'.1 M'.2.1 M'.2.2.1).1
  have hf : {w | (ordSub w (detSub M'.1) - ordSub w (detSub M.1)).toNat ≠ 0}.Finite := by
    refine (f1.union f2).subset fun v hv => ?_
    by_contra hn
    simp only [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    exact hv (by simp [hn.1, hn.2])
  have h1 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N M w w' hw
  have h2 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N M' w w' hw
  unfold repI
  rw [ordI_powI _ hf, ordI_powI _ hf]
  omega

end GlobalTheory.Mem.Chr.RelDet

namespace GlobalTheory.Mem.Chr

open RelDet

open Classical in

theorem relDetT_laws : ∀ (R : Ranks) (H : Formalism.BasicNotions.Host R) (N : ℕ), letI := H.cmStar; (∀ L : SDLat H.E N, relDetT H N L.1 L.1 = 1) ∧ (∀ L L' L'' : SDLat H.E N, relDetT H N L.1 L'.1 * relDetT H N L'.1 L''.1 = relDetT H N L.1 L''.1) ∧ ∀ (L L' : SDLat H.E N) (γ : Matrix.unitaryGroup (Fin N) H.E), L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 → relDetT H N L.1 L'.1 = QuotientGroup.mk (e1T H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩) := by
  intro R H N
  letI := H.cmStar
  refine ⟨fun L => relDetT_self H N L.1, fun L L' L'' => ?_, fun L L' γ hγ => ?_⟩
  · rw [relDetT_eq, relDetT_eq, relDetT_eq, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    refine mk_mk_eq H fun w w' hw => ?_
    have h1 := ordI_repI H N L L' w w' hw
    have h2 := ordI_repI H N L' L'' w w' hw
    have h3 := ordI_repI H N L L'' w w' hw
    rw [ordI_mul, ordI_mul]
    omega
  · obtain ⟨he, hk⟩ := GlobalTheory.Mem.RatPts.rat_points R H
    obtain ⟨k, hk⟩ := hk ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩
    rw [← he k _ hk, relDetT_eq]
    refine mk_mk_eq H fun w w' hw => ?_
    have hk' : (γ : Matrix (Fin N) (Fin N) H.E).det * H.conj (k : H.E) = k := hk
    have hd : (γ : Matrix (Fin N) (Fin N) H.E).det ≠ 0 := fun h0 => k.ne_zero (by rw [← hk', h0, zero_mul])
    have hc : H.conj (k : H.E) ≠ 0 := fun h0 => k.ne_zero (by rw [← hk', h0, mul_zero])
    have e : k = Units.mk0 _ hd * Units.mk0 _ hc := Units.ext hk'.symm
    have h1 : ordF w' k = ordF w' (Units.mk0 _ hd) + ordF w' (Units.mk0 _ hc) := by
      rw [← DetOrd.ordF_mul', ← e]
    have h2 : ordF w' (Units.mk0 _ hc) = ordF w k := by
      have := (conjPl_main.2.1 R H w w').1 hw (k : H.E)
      unfold ordF
      rw [← this]
      rfl
    have h3 := (ordSub_detSub_lattice H.E N L.1 L.2.1 L.2.2.1).2.2 (γ : Matrix (Fin N) (Fin N) H.E)
      (Units.mk0 _ hd) rfl w'
    have h4 : ordSub w' (detSub L'.1) = ordF w' (Units.mk0 _ hd) + ordSub w' (detSub L.1) := by
      rw [hγ]
      exact h3
    have h5 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N L w w' hw
    have h6 := GlobalTheory.Mem.Chr.ordSub_detSub_selfDual R H N L' w w' hw
    rw [ordI_repI H N L L' w w' hw, ordI_diag, ordI_diag]
    omega

end GlobalTheory.Mem.Chr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RowHCParameterIsHCParamAndFormalDegreePos
section
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem lamS_succ_lt (R : Ranks) (P : HCParam R) (i j : Fin R.r) (hij : j.val = i.val + 1) :
    lamS R P j < lamS R P i := by
  have hk : R.m + 3 ≤ R.k := R.m_add_three_le_k
  have hm : 2 ≤ R.m := R.two_le_m
  have hjr : j.val < R.k + R.m - 1 := j.isLt
  have hu : ∀ a b : Fin R.k, a.val = b.val → P.u a = P.u b := fun a b h => by rw [Fin.ext h]
  have hb : ∀ a b : Fin R.m, a.val = b.val → P.b a = P.b b := fun a b h => by rw [Fin.ext h]
  unfold Formalism.MainNotions.S.lamS
  by_cases hj : j.val < R.k - 1
  · have hi : i.val < R.k - 1 := by omega
    rw [dif_pos hj, dif_pos hi]
    have key : P.v ⟨j.val, hj⟩ < P.v ⟨i.val, hi⟩ :=
      calc P.v ⟨j.val, hj⟩ < P.u ⟨j.val, by omega⟩ := P.u_gt_v ⟨j.val, hj⟩
        _ = P.u ⟨i.val + 1, by omega⟩ := hu _ _ (by simp [hij])
        _ < P.v ⟨i.val, hi⟩ := P.v_gt_u ⟨i.val, hi⟩
    exact_mod_cast key
  · by_cases hi : i.val < R.k - 1
    · have hj0 : j.val - (R.k - 1) < R.m := by omega
      rw [dif_neg hj, dif_pos hj0, dif_pos hi]
      have key : -P.b ⟨j.val - (R.k - 1), hj0⟩ < P.v ⟨i.val, hi⟩ :=
        calc -P.b ⟨j.val - (R.k - 1), hj0⟩ = -P.b ⟨0, by omega⟩ :=
            congrArg (fun x => -x) (hb _ _ (show j.val - (R.k - 1) = 0 by omega))
          _ < P.u ⟨R.k - 1, by omega⟩ := P.u_last_gt (by omega) (by omega)
          _ = P.u ⟨i.val + 1, by omega⟩ := hu _ _ (by simp; omega)
          _ < P.v ⟨i.val, hi⟩ := P.v_gt_u ⟨i.val, hi⟩
      have := (Rat.cast_lt (K := ℝ)).mpr key
      push_cast at this
      exact this
    · have hj0 : j.val - (R.k - 1) < R.m := by omega
      have hi0 : i.val - (R.k - 1) < R.m := by omega
      have hi1 : i.val - (R.k - 1) + 1 < R.m := by omega
      rw [dif_neg hj, dif_pos hj0, dif_neg hi, dif_pos hi0]
      have h1 := P.gap_be ⟨i.val - (R.k - 1), hi0⟩
      have h2 := P.gap_eb ⟨i.val - (R.k - 1), hi0⟩ hi1
      have h3 : P.b ⟨i.val - (R.k - 1) + 1, hi1⟩ = P.b ⟨j.val - (R.k - 1), hj0⟩ := hb _ _ (by simp; omega)
      have ht : (0 : ℚ) ≤ R.t := Nat.cast_nonneg _
      have key : P.b ⟨i.val - (R.k - 1), hi0⟩ < P.b ⟨j.val - (R.k - 1), hj0⟩ := by
        rw [← h3]; linarith
      have := (Rat.cast_lt (K := ℝ)).mpr key
      linarith

theorem lamS_int (R : Ranks) (P : HCParam R) (i : Fin R.r) : ∃ z : ℤ, lamS R P i = (z : ℝ) := by
  unfold Formalism.MainNotions.S.lamS
  split_ifs with h h'
  · obtain ⟨z, hz⟩ := P.v_int ⟨i.val, h⟩
    exact ⟨z, by rw [hz, Rat.cast_intCast]⟩
  · obtain ⟨z, hz⟩ := P.b_int ⟨i.val - (R.k - 1), h'⟩
    exact ⟨-z, by rw [hz, Rat.cast_intCast]; push_cast; ring⟩
  · exact ⟨0, by simp⟩

theorem lamSH_isHCParam (R : Ranks) (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (lamSH R P) := by
  refine ⟨?_, ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    exact lamS_succ_lt R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) (Fin.castSucc i))
      (Fin.cast (Formalism.MainNotions.S.dimS_eq R) i.succ) (by simp)
  · intro a
    obtain ⟨z, hz⟩ := lamS_int R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) a)
    obtain ⟨w, hw⟩ := R.k_even
    have hk : (R.k : ℝ) = 2 * w := by rw [hw]; push_cast; ring
    refine ⟨z - R.rS - w, ?_⟩
    show lamS R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) a) - _ = _
    rw [hz]
    push_cast
    rw [hk]
    ring

theorem fdegHC_pos_of_injective {n : ℕ} (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    0 < Formalism.QuantumDeterminants.fdegHC lam := by
  unfold Formalism.QuantumDeterminants.fdegHC
  apply div_pos
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    rw [Finset.mem_filter] at hb
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hb.2.ne (hlam h))
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    rw [Finset.mem_filter] at hb
    have h1 : (a : ℕ) < b := hb.2
    have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h1
    linarith

theorem lamSH_isHCParam_and_trueDsig_pos :
    ∀ (R : Ranks) (P : HCParam R), Formalism.QuantumDeterminants.IsHCParam (lamSH R P) ∧ 0 < trueDsig R P := by
  intro R P
  refine ⟨lamSH_isHCParam R P, ?_⟩
  exact fdegHC_pos_of_injective _ (lamSH_isHCParam R P).1.injective

end GlobalTheory.Mem.Vol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ULocDualHformOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory

theorem uLocDual_intOE_map {E : Type} [Field E] [NumberField E] (σ : E →+* E) {a : E}
    (ha : a ∈ intOE E) : σ a ∈ intOE E := by
  obtain ⟨r, rfl⟩ := ha
  exact ⟨⟨σ r, (RingOfIntegers.isIntegral_coe r).map σ.toIntAlgHom⟩, rfl⟩

theorem uLocDual_hform_one {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (x y : Fin n → E) :
    Formalism.UG.hform σ (1 : Matrix (Fin n) (Fin n) E) x y = ∑ i, σ (x i) * y i := by
  unfold Formalism.UG.hform
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [Matrix.one_apply_eq, mul_one]
  · intro j _ hj; rw [Matrix.one_apply_ne (Ne.symm hj), mul_zero, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem uLocDual_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (_ : ∀ x, σ (σ x) = x) (n : ℕ) [NeZero n] (p q : 𝓞 E) (_ : (p : E) ≠ 0) (_ : (q : E) = σ (p : E)),
    Submodule.span (𝓞 E) (dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (rll_dLat n ((p : E)⁻¹))) = rll_dLat n (q : E) := by
  intro F E _ _ _ _ _ σ _ n _ p q hp hq
  have e : dualSet (σ : E →+* E) (1 : Matrix (Fin n) (Fin n) E) (rll_dLat n ((p : E)⁻¹)) =
      (rll_dLat n (q : E) : Set (Fin n → E)) := by
    ext y
    rw [SetLike.mem_coe, rll_mem_dLat]
    show (∀ x ∈ rll_dLat n ((p : E)⁻¹), Formalism.UG.hform (σ : E →+* E) 1 x y ∈ (algebraMap (𝓞 E) E).range) ↔ _
    simp only [uLocDual_hform_one]
    constructor
    · intro hy
      refine ⟨fun i hi => ?_, ?_⟩
      · have := hy (Pi.single i 1) ⟨fun j _ => by
          by_cases hj : j = i
          · subst hj; rw [Pi.single_eq_same]; exact one_mem _
          · rw [Pi.single_eq_of_ne hj]; exact zero_mem _, by
          rw [Pi.single_eq_of_ne (Ne.symm hi), mul_zero]; exact zero_mem _⟩
        rw [Finset.sum_eq_single i] at this
        · rwa [Pi.single_eq_same, map_one, one_mul] at this
        · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
      · have := hy (Pi.single (lastIdx n) (p : E)) ⟨fun j hj => by
          rw [Pi.single_eq_of_ne hj]; exact zero_mem _, by
          rw [Pi.single_eq_same, inv_mul_cancel₀ hp]; exact one_mem _⟩
        rw [Finset.sum_eq_single (lastIdx n)] at this
        · rw [Pi.single_eq_same] at this
          show (q : E) * y (lastIdx n) ∈ intOE E
          rw [hq]; exact this
        · intro j _ hj; rw [Pi.single_eq_of_ne hj, map_zero, zero_mul]
        · intro h; exact absurd (Finset.mem_univ _) h
    · rintro ⟨h1, h2⟩ x ⟨hx1, hx2⟩
      refine sum_mem fun i _ => ?_
      by_cases hi : i = lastIdx n
      · subst hi
        have hl : x (lastIdx n) = (p : E) * ((p : E)⁻¹ * x (lastIdx n)) := by
          rw [mul_inv_cancel_left₀ hp]
        rw [hl, map_mul, mul_comm ((σ : E →+* E) (p : E)), mul_assoc]
        refine mul_mem (uLocDual_intOE_map _ hx2) ?_
        have : (σ : E →+* E) (p : E) = (q : E) := by rw [hq]; rfl
        rw [this]; exact h2
      · exact mul_mem (uLocDual_intOE_map _ (hx1 i hi)) (h1 i hi)
  rw [e, Submodule.span_eq]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UlocOfTrivDisc
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

namespace GlobalTheory

theorem uloc_of_triv_disc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (v : HeightOneSpectrum (𝓞 F)) (_ : (T : 𝓞 F) ∈ v.asIdeal)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (_ : x ∈ levelVL σ J v S.Lb)
    (_ : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb),
    x ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad S v hT x hx hy
  have hL : x ∈ stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb) := by
    unfold Formalism.UG.levelVL Formalism.UG.level at hx
    exact hx.2
  have hLi : ∀ z, z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ↔
      ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ z ∈
        latS (F := F) (v.adicCompletion F) (intV E v) S.Lb :=
    (stabGL (latS (F := F) (v.adicCompletion F) (intV E v) S.Lb)).inv_mem hL
  have hsub : latS (F := F) (v.adicCompletion F) (intV E v) S.Lb ≤
      latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    unfold Formalism.UG.latS
    apply Submodule.span_mono
    apply Set.image_mono
    intro z hz
    exact Submodule.subset_span (S.Lb_int z hz)
  have hfw : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    intro y hy'
    have h2 := Submodule.add_mem _ (hsub (hy y hy')) hy'
    rwa [sub_add_cancel] at h2
  have hbw : ∀ y, (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) →
      y ∈ latS (F := F) (v.adicCompletion F) (intV E v)
        (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)) := by
    intro y hw
    have hd := hy _ hw
    have hi := hsub ((hLi _).1 hd)
    have key : y = (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y -
        ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
          ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
            ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) -
            (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y) := by
      have hinv : ∀ u, ((x⁻¹ : GL (Fin n) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ
          ((x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ u) = u := by
        intro u
        rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
      rw [Matrix.mulVec_sub, hinv, hinv, sub_sub_cancel]
    rw [key]
    exact Submodule.sub_mem _ hw hi
  rw [S.UlocAlt v hT, Subgroup.mem_inf]
  refine ⟨hx, ⟨?_, ?_⟩⟩
  · show ∀ y, y ∈ _ ↔ _
    exact fun y => ⟨hfw y, hbw y⟩
  · intro z
    have h0 := S.fT_L v hT
      (⟨(x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (z : Fin n → E ⊗[F] v.adicCompletion F), hfw z z.2⟩ - z)
      (by
        show (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ (z : Fin n → E ⊗[F] v.adicCompletion F) -
          (z : Fin n → E ⊗[F] v.adicCompletion F) ∈ _
        exact hy z z.2)
    rw [map_sub, sub_eq_zero] at h0
    exact h0

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValNatCastLtOne
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.UG Formalism.L2.Forms Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.LevCong

variable {F : Type} [Field F] [NumberField F]

theorem val_natCast_lt_one (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hv : (p : 𝓞 F) ∈ v.asIdeal) :
    Valued.v (p : v.adicCompletion F) < 1 := by
  have : (p : v.adicCompletion F) = algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F (p : 𝓞 F)) := by simp
  rw [this]
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := F) v (algebraMap (𝓞 F) F (p : 𝓞 F))
  have h3 := (HeightOneSpectrum.valuation_lt_one_iff_mem (K := F) v _).2 hv
  exact h2 ▸ h3

theorem redM_eq_one {n : ℕ} (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (hv : (p : 𝓞 F) ∈ v.asIdeal)
    (M : Matrix (Fin n) (Fin n) (v.adicCompletion F))
    (hM : ∀ r c, ∃ t ∈ v.adicCompletionIntegers F, M r c = (1 : Matrix (Fin n) (Fin n) (v.adicCompletion F)) r c + p * t) :
    redM F v M = 1 := by
  have hp : IsLocalRing.residue (v.adicCompletionIntegers F) (p : v.adicCompletionIntegers F) = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    refine (Valuation.mem_maximalIdeal_iff _ _).2 ?_
    simpa using val_natCast_lt_one v p hv
  ext r c
  obtain ⟨t, ht, e⟩ := hM r c
  set u : v.adicCompletionIntegers F := (if r = c then 1 else 0) + p * ⟨t, ht⟩ with hu
  have e' : M r c = (u : v.adicCompletion F) := by
    rw [e, hu, Matrix.one_apply]
    split_ifs <;> simp
  have hm : M r c ∈ v.adicCompletionIntegers F := e' ▸ u.2
  unfold redM
  rw [dif_pos hm]
  have : (⟨M r c, hm⟩ : v.adicCompletionIntegers F) = u := Subtype.ext e'
  rw [this, hu, map_add, map_mul, hp, zero_mul, add_zero, Matrix.one_apply]
  split_ifs <;> simp

theorem mem_Uloc_of_cong : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {gp : Fin 2 → ℕ}
    (S : Formalism.L2.Forms.StepLevel F E σ J T f bad) (G : GLoc F E σ gp)
    {H : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin n) (kv F v))}
    {lam : ∀ a v h, H a v h →* ℂˣ} (_ : GLevH S G H lam) (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)) (_ : (gp a : 𝓞 F) ∈ v.asIdeal)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) (_ : x ∈ levelVL σ J v S.Lb)
    (_ : ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb, ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = ((gp a : ℕ) : E ⊗[F] v.adicCompletion F) • z),
    x ∈ S.Uloc v := by
  intro F E _ _ _ _ _ σ n J T f bad gp S G H lam L a v h x hx hc
  refine (L.mem a v h x hx).2 ⟨1, (H a v h).one_mem, ?_⟩
  rw [Units.val_one]
  refine (redM_eq_one v (gp a) h _ fun r c => ?_).symm
  set fr := L.fr a v h with hfr
  set φ := G.phi a v h with hφ
  have hinv : ∀ w : Fin n → v.adicCompletion F,
      ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ
        ((fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  obtain ⟨y, hy, hyw⟩ := (L.fr_lat a v h ((fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single c 1)).2 (fun b => by
    show (((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ _) b ∈ _
    rw [hinv, Pi.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _)
  obtain ⟨z, hz, e⟩ := hc y hy
  have ht := (L.fr_lat a v h (fun b => φ (z b))).1 ⟨z, hz, fun _ => rfl⟩ r
  refine ⟨_, ht, ?_⟩
  have hy' : (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ Pi.single c 1 = φ ∘ y := (funext hyw).symm
  have e2 : ((bc φ x : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ (φ ∘ y) =
      φ ∘ y + ((gp a : ℕ) : v.adicCompletion F) • fun b => φ (z b) := by
    funext b
    have e3 := congrArg φ (congrFun e b)
    rw [Pi.sub_apply, map_sub, RingHom.map_mulVec, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, sub_eq_iff_eq_add'] at e3
    exact e3
  have e4 : G.mat a v h fr x *ᵥ Pi.single c 1 = Pi.single c 1 + ((gp a : ℕ) : v.adicCompletion F) •
      (((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) *ᵥ fun b => φ (z b)) := by
    unfold GLoc.mat
    rw [Units.val_mul, Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hy', ← hφ, e2, Matrix.mulVec_add,
      Matrix.mulVec_smul, ← hy', hinv]
  have e5 := congrFun e4 r
  rw [Matrix.mulVec_single_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply] at e5
  rw [Matrix.one_apply]
  exact e5

end GlobalTheory.Mem.LevCong
end

