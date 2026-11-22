import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0003
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Bundle0009

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

namespace AffineChartTrdeg

variable {F : Type} [Field F] {n : ℕ} (P : Ideal (MvPolynomial (Fin n) F)) [P.IsPrime]

omit [P.IsPrime] in

theorem aeval_genPt (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = algebraMap (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P)) (Ideal.Quotient.mk P f) := by
  have h : aeval (genPt P) = (IsScalarTower.toAlgHom F (MvPolynomial (Fin n) F ⧸ P)
      (FractionRing (MvPolynomial (Fin n) F ⧸ P))).comp (Ideal.Quotient.mkₐ F P) :=
    MvPolynomial.algHom_ext fun i => by simp [genPt]
  rw [h]
  rfl

omit [P.IsPrime] in

theorem aeval_genPt_eq_zero_iff (f : MvPolynomial (Fin n) F) :
    aeval (genPt P) f = 0 ↔ f ∈ P := by
  rw [aeval_genPt, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]

theorem exists_isHomogeneous (j : Fin n) (hj : genPt P j ≠ 0)
    {a : FractionRing (MvPolynomial (Fin n) F ⧸ P)}
    (ha : a ∈ Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)) :
    ∃ D : ℕ, ∀ D' ≥ D, ∃ h : MvPolynomial (Fin n) F,
      h.IsHomogeneous D' ∧ aeval (genPt P) h = a * genPt P j ^ D' := by
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    refine ⟨1, fun D' hD' => ?_⟩
    obtain ⟨e, rfl⟩ : ∃ e, D' = 1 + e := ⟨D' - 1, by omega⟩
    refine ⟨X m * X j ^ e, (isHomogeneous_X F m).mul (isHomogeneous_X_pow j e), ?_⟩
    simp only [map_mul, map_pow, aeval_X]
    rw [pow_add, pow_one]
    field_simp
  | algebraMap r =>
    exact ⟨0, fun D' _ => ⟨C r * X j ^ D', isHomogeneous_C_mul_X_pow r j D', by simp⟩⟩
  | add x y _ _ hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    refine ⟨max D₁ D₂, fun D' hD' => ?_⟩
    obtain ⟨f, hf, ef⟩ := h₁ D' (le_of_max_le_left hD')
    obtain ⟨g, hg, eg⟩ := h₂ D' (le_of_max_le_right hD')
    exact ⟨f + g, hf.add hg, by rw [map_add, ef, eg, add_mul]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨D₁, h₁⟩ := hx
    obtain ⟨D₂, h₂⟩ := hy
    refine ⟨D₁ + D₂, fun D' hD' => ?_⟩
    obtain ⟨e, rfl⟩ : ∃ e, D' = D₁ + e := ⟨D' - D₁, by omega⟩
    obtain ⟨f, hf, ef⟩ := h₁ D₁ le_rfl
    obtain ⟨g, hg, eg⟩ := h₂ e (by omega)
    exact ⟨f * g, hf.mul hg, by rw [map_mul, ef, eg, pow_add]; ring⟩

theorem transcendental (hP : IsHomogIdeal P) (j : Fin n) (hj : X j ∉ P) :
    Transcendental (Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹))
      (genPt P j) := by
  classical
  set A' := Algebra.adjoin F (Set.range fun m => genPt P m * (genPt P j)⁻¹)
  set ξ := genPt P
  have hξ : ξ j ≠ 0 := fun h => hj ((aeval_genPt_eq_zero_iff P (X j)).1 (by simpa using h))
  rintro ⟨p, hp, hpe⟩
  set N := p.natDegree + 1
  choose D hD using fun e => exists_isHomogeneous P j hξ (p.coeff e).2
  set M := (Finset.range N).sup D
  have hh : ∀ e, ∃ h : MvPolynomial (Fin n) F,
      h.IsHomogeneous M ∧ aeval ξ h = (p.coeff e : _) * ξ j ^ M := by
    intro e
    by_cases he : e < N
    · exact hD e M (Finset.le_sup (Finset.mem_range.2 he))
    · refine ⟨0, isHomogeneous_zero _ _ _, ?_⟩
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
  choose h hhom heval using hh
  set G := ∑ e ∈ Finset.range N, h e * X j ^ e
  have hG : G ∈ P := by
    rw [← aeval_genPt_eq_zero_iff]
    have h0 : Polynomial.aeval (ξ j) p = ∑ e ∈ Finset.range N, (p.coeff e : _) * ξ j ^ e := by
      rw [Polynomial.aeval_eq_sum_range]
      rfl
    calc aeval ξ G = ξ j ^ M * ∑ e ∈ Finset.range N, (p.coeff e : _) * ξ j ^ e := by
          simp only [G, map_sum, map_mul, map_pow, aeval_X, heval, Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => by ring
      _ = 0 := by rw [← h0, hpe, mul_zero]
  have hcoeff : ∀ e < N, p.coeff e = 0 := by
    intro e he
    have hcomp : homogeneousComponent (M + e) G = h e * X j ^ e := by
      simp only [G, map_sum]
      rw [Finset.sum_eq_single e]
      · exact homogeneousComponent_eq_self ((hhom e).mul (isHomogeneous_X_pow j e))
      · intro b _ hb
        rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).2
          ((hhom b).mul (isHomogeneous_X_pow j b))), if_neg (by omega)]
      · intro hne
        exact absurd (Finset.mem_range.2 he) hne
    have hmem : h e * X j ^ e ∈ P := hcomp ▸ hP G hG (M + e)
    have hhe : h e ∈ P := by
      rcases Ideal.IsPrime.mem_or_mem ‹_› hmem with h1 | h1
      · exact h1
      · exact absurd (Ideal.IsPrime.mem_of_pow_mem ‹_› e h1) hj
    have h2 := heval e
    rw [(aeval_genPt_eq_zero_iff P _).2 hhe, eq_comm, mul_eq_zero] at h2
    rcases h2 with h2 | h2
    · exact Subtype.ext h2
    · exact absurd (pow_eq_zero_iff'.1 h2).1 hξ
  refine hp (Polynomial.ext fun e => ?_)
  by_cases he : e < N
  · simpa using hcoeff e he
  · simpa using Polynomial.coeff_eq_zero_of_natDegree_lt (p := p) (by omega)

theorem proof : AffineChartTrdeg.Statement := by
  intro F _ n d P _ j hP hdim hj
  set R := MvPolynomial (Fin n) F ⧸ P
  set K := FractionRing R
  set ξ := genPt P
  set A' := Algebra.adjoin F (Set.range fun m => ξ m * (ξ j)⁻¹)
  have hξ : ξ j ≠ 0 := fun h => hj ((aeval_genPt_eq_zero_iff P (X j)).1 (by simpa using h))

  have hK : Algebra.trdeg F K = ((d + 1 : ℕ) : Cardinal) := by
    have : Algebra.FiniteType F R :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ F P)
        (Ideal.Quotient.mkₐ_surjective F P)
    rw [GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_isFractionRing (k := F) (A := R) K]
    rw [GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg F] at hdim
    have h2 : (Algebra.trdeg F R).toENat = ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdim
    exact Cardinal.toENat_eq_natCast.mp h2

  set S := Algebra.adjoin A' (Set.range fun _ : Unit => ξ j)
  have hξS : ∀ m, ξ m ∈ S := by
    intro m
    have hr : ξ m * (ξ j)⁻¹ ∈ A' := Algebra.subset_adjoin ⟨m, rfl⟩
    have : ξ m = ξ m * (ξ j)⁻¹ * ξ j := by field_simp
    rw [this]
    exact S.mul_mem (S.algebraMap_mem (⟨_, hr⟩ : A')) (Algebra.subset_adjoin ⟨(), rfl⟩)
  have hRS : ∀ r : R, algebraMap R K r ∈ S := by
    intro r
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [← aeval_genPt]
    induction f using MvPolynomial.induction_on with
    | C c =>
      rw [aeval_C, IsScalarTower.algebraMap_apply F A' K]
      exact S.algebraMap_mem _
    | add f g hf hg => rw [map_add]; exact S.add_mem hf hg
    | mul_X f i hf => rw [map_mul, aeval_X]; exact S.mul_mem hf (hξS i)

  have halg : Algebra.IsAlgebraic S K := by
    refine ⟨fun x => ?_⟩
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hb0 : algebraMap R K b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨Polynomial.C ⟨_, hRS b⟩ * Polynomial.X - Polynomial.C ⟨_, hRS a⟩, fun h => hb0 ?_, ?_⟩
    · have := congrArg (Polynomial.coeff · 1) h
      simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C, ↓reduceIte,
        one_ne_zero, Polynomial.coeff_zero] at this
      have h' := congrArg Subtype.val this
      simp only [Subalgebra.coe_sub, Subalgebra.coe_zero, sub_zero] at h'
      exact h'
    · simp only [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X]
      show algebraMap R K b * (algebraMap R K a / algebraMap R K b) - algebraMap R K a = 0
      rw [mul_comm, div_mul_cancel₀ _ hb0, sub_self]

  have h1 : Algebra.trdeg A' K = 1 := by
    have hind : AlgebraicIndependent A' (fun _ : Unit => ξ j) :=
      algebraicIndependent_unique_type_iff.mpr (transcendental P hP.isHomog j hj)
    have hb : IsTranscendenceBasis A' (fun _ : Unit => ξ j) :=
      hind.isTranscendenceBasis_iff_isAlgebraic.mpr halg
    rw [← hb.cardinalMk_eq_trdeg, Cardinal.mk_fintype, Fintype.card_unit, Nat.cast_one]

  have : FaithfulSMul A' K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  have : FaithfulSMul F A' :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap F A').injective
  have hadd := trdeg_add_eq F A' (A := K)
  rw [h1, hK] at hadd
  have hfin : Algebra.trdeg F A' < Cardinal.aleph0 :=
    lt_of_le_of_lt le_self_add (by rw [hadd]; exact Cardinal.natCast_lt_aleph0)
  obtain ⟨k, hk⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hk] at hadd ⊢
  norm_cast at hadd ⊢
  omega

end AffineChartTrdeg

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChartIncOrd
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChartIncOrd

theorem isPrime_map_C {R : Type*} [CommRing R] (σ : Type*) (p : Ideal R) [p.IsPrime] :
    (p.map (C : R →+* MvPolynomial σ R)).IsPrime := by
  have h := MvPolynomial.ker_map (σ := σ) (Ideal.Quotient.mk p)
  rw [Ideal.mk_ker] at h
  rw [← h]
  exact RingHom.ker_isPrime _

variable {F : Type} [Field F] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F)) (t : Fin n → F) (e : ℕ)

abbrev ChartQ : Type := MvPolynomial (Fin n) F ⧸ (I ⊔ Ideal.span {linForm t - 1})

abbrev mkQ : MvPolynomial (Fin n) F →+* ChartQ I t := Ideal.Quotient.mk _

def mkS : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* ChartInc I t e := Ideal.Quotient.mk _

theorem mkS_surjective : Function.Surjective (mkS I t e) := Ideal.Quotient.mk_surjective

theorem mkS_eq_zero {a : MvPolynomial (Fin n ⊕ Fin e × Fin n) F} (h : a ∈ chartIncIdeal I t e) :
    mkS I t e a = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr h

theorem chartX_apply (x : MvPolynomial (Fin n) F) :
    chartX I t e x = mkS I t e (rename Sum.inl x) := rfl

def toInc : ChartQ I t →+* ChartInc I t e :=
  Ideal.Quotient.lift _ (chartX I t e) fun a ha => by
    rw [chartX_apply]
    exact mkS_eq_zero I t e (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha))

theorem toInc_mk (x : MvPolynomial (Fin n) F) :
    toInc I t e (mkQ I t x) = chartX I t e x := rfl

theorem sum_tQ : (∑ m, mkQ I t (C (t m) * X m)) = 1 := by
  rw [← map_sum, ← map_one (mkQ I t), Ideal.Quotient.eq]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

theorem sum_tS : (∑ m, chartX I t e (C (t m) * X m)) = 1 := by
  have := congrArg (toInc I t e) (sum_tQ I t)
  simpa [map_sum, toInc_mk] using this

theorem sum_uS (i : Fin e) :
    (∑ m, mkS I t e (X (Sum.inr (i, m)) * X (Sum.inl m))) = 0 := by
  rw [← map_sum]
  exact mkS_eq_zero I t e (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))

def fwd : MvPolynomial (Fin e × Fin n) (ChartQ I t) →+* MvPolynomial (Fin e) (ChartInc I t e) :=
  eval₂Hom (C.comp (toInc I t e)) fun ij =>
    C (mkS I t e (X (Sum.inr ij))) + X ij.1 * C (chartX I t e (C (t ij.2)))

theorem fwd_C (q : ChartQ I t) : fwd I t e (C q) = C (toInc I t e q) := by
  simp [fwd]

theorem fwd_X (ij : Fin e × Fin n) :
    fwd I t e (X ij) = C (mkS I t e (X (Sum.inr ij))) + X ij.1 * C (chartX I t e (C (t ij.2))) := by
  simp [fwd]

def back₀ : MvPolynomial (Fin n ⊕ Fin e × Fin n) F →+* MvPolynomial (Fin e × Fin n) (ChartQ I t) :=
  eval₂Hom (C.comp ((mkQ I t).comp C))
    (Sum.elim (fun m => C (mkQ I t (X m)))
      (fun ij => genSubst (fun m => mkQ I t (X m)) (fun m => mkQ I t (C (t m))) ij))

theorem back₀_C (r : F) : back₀ I t e (C r) = C (mkQ I t (C r)) := by
  simp [back₀]

theorem back₀_inl (m : Fin n) : back₀ I t e (X (Sum.inl m)) = C (mkQ I t (X m)) := by
  simp [back₀]

theorem back₀_inr (ij : Fin e × Fin n) :
    back₀ I t e (X (Sum.inr ij)) = genSubst (fun m => mkQ I t (X m)) (fun m => mkQ I t (C (t m))) ij := by
  simp [back₀]

theorem back₀_rename (x : MvPolynomial (Fin n) F) :
    back₀ I t e (rename Sum.inl x) = C (mkQ I t x) := by
  have : (back₀ I t e).comp (rename Sum.inl).toRingHom =
      (C : ChartQ I t →+* MvPolynomial (Fin e × Fin n) (ChartQ I t)).comp (mkQ I t) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun m => ?_)
    · simp [back₀_C]
    · simp [back₀_inl]
  exact congrArg (fun f => f x) this

theorem chartIncIdeal_le_ker : chartIncIdeal I t e ≤ RingHom.ker (back₀ I t e) := by
  refine sup_le ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker]
    rw [back₀_rename, Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker]
    have h1 := congrArg (C : ChartQ I t →+* MvPolynomial (Fin e × Fin n) (ChartQ I t)) (sum_tQ I t)
    simp only [map_sum, map_mul, map_one] at h1
    simp only [map_sum, map_mul, back₀_inl, back₀_inr, genSubst]
    set S := ∑ l, X (i, l) * C (mkQ I t (X l))
    have : ∑ m, (X (i, m) - S * C (mkQ I t (C (t m)))) * C (mkQ I t (X m)) = S - S * 1 := by
      rw [← h1, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    simpa using this

def back : ChartInc I t e →+* MvPolynomial (Fin e × Fin n) (ChartQ I t) :=
  Ideal.Quotient.lift (chartIncIdeal I t e) (back₀ I t e) fun _ ha => chartIncIdeal_le_ker I t e ha

theorem back_mk (a : MvPolynomial (Fin n ⊕ Fin e × Fin n) F) :
    back I t e (mkS I t e a) = back₀ I t e a := rfl

def bwd : MvPolynomial (Fin e) (ChartInc I t e) →+* MvPolynomial (Fin e × Fin n) (ChartQ I t) :=
  eval₂Hom (back I t e) fun i => ∑ m, X (i, m) * C (mkQ I t (X m))

theorem back_toInc (q : ChartQ I t) : back I t e (toInc I t e q) = C q := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  exact (congrArg (back I t e) (toInc_mk I t e x)).trans (back₀_rename I t e x)

theorem sum_fwd (i : Fin e) :
    (∑ l, (C (mkS I t e (X (Sum.inr (i, l)))) + X i * C (chartX I t e (C (t l)))) *
      C (chartX I t e (X l))) = (X i : MvPolynomial (Fin e) (ChartInc I t e)) := by
  have hu := congrArg (C : ChartInc I t e →+* MvPolynomial (Fin e) (ChartInc I t e)) (sum_uS I t e i)
  have ht := congrArg (C : ChartInc I t e →+* MvPolynomial (Fin e) (ChartInc I t e)) (sum_tS I t e)
  simp only [map_sum, map_mul, map_one, map_zero] at hu ht
  have hX : ∀ l, chartX I t e (X l) = mkS I t e (X (Sum.inl l)) := fun l => by
    rw [chartX_apply, rename_X]
  simp only [hX] at ht ⊢
  calc _ = (∑ l, C (mkS I t e (X (Sum.inr (i, l)))) * C (mkS I t e (X (Sum.inl l)))) +
        X i * ∑ l, C (chartX I t e (C (t l))) * C (mkS I t e (X (Sum.inl l))) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun l _ => ?_
          ring
    _ = X i := by rw [hu, ht]; ring

theorem fwd_back (s : ChartInc I t e) : fwd I t e (back I t e s) = C s := by
  have : ((fwd I t e).comp (back I t e)).comp (mkS I t e) = C.comp (mkS I t e) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun v => ?_)
    · simp only [RingHom.comp_apply, back_mk, back₀_C, fwd_C, toInc_mk, chartX_apply, rename_C]
    · rcases v with m | ⟨i, m⟩
      · simp only [RingHom.comp_apply, back_mk, back₀_inl, fwd_C, toInc_mk, chartX_apply, rename_X]
      · simp only [RingHom.comp_apply, back_mk, back₀_inr, genSubst, map_sub, map_mul, map_sum, fwd_X,
          fwd_C, toInc_mk]
        linear_combination (-(C (chartX I t e (C (t m))))) * sum_fwd I t e i
  obtain ⟨a, rfl⟩ := mkS_surjective I t e s
  exact congrArg (fun f => f a) this

theorem fwd_bwd : (fwd I t e).comp (bwd I t e) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun s => ?_) (fun i => ?_)
  · simp [bwd, fwd_back]
  · simp only [bwd, RingHom.comp_apply, eval₂Hom_X', map_sum, map_mul, fwd_X, fwd_C, toInc_mk,
      RingHom.id_apply]
    exact sum_fwd I t e i

theorem bwd_fwd : (bwd I t e).comp (fwd I t e) = RingHom.id _ := by
  refine MvPolynomial.ringHom_ext (fun q => ?_) (fun ij => ?_)
  · simp [fwd, bwd, back_toInc]
  · obtain ⟨i, m⟩ := ij
    simp only [RingHom.comp_apply, fwd_X, map_add, map_mul, bwd, eval₂Hom_C, eval₂Hom_X',
      RingHom.id_apply, chartX_apply, rename_C, back_mk, back₀_C, back₀_inr, genSubst]
    ring

theorem ord_atPrime_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (f : R ≃+* S) (P : Ideal R) [P.IsPrime]
    (P' : Ideal S) [P'.IsPrime] (h : P = P'.comap f) (x : R) :
    Ring.ord (Localization.AtPrime P') (algebraMap S _ (f x)) =
      Ring.ord (Localization.AtPrime P) (algebraMap R _ x) := by
  have := ord_ringEquiv (Localization.localRingEquiv P P' f h) (algebraMap R _ x)
  exact (congrArg (Ring.ord (Localization.AtPrime P')) (Localization.localRingHom_to_map P P' (f : R →+* S) h x)).symm.trans this

def equiv : MvPolynomial (Fin e × Fin n) (ChartQ I t) ≃+* MvPolynomial (Fin e) (ChartInc I t e) :=
  RingEquiv.ofRingHom (fwd I t e) (bwd I t e) (fwd_bwd I t e) (bwd_fwd I t e)

theorem equiv_apply (y : MvPolynomial (Fin e × Fin n) (ChartQ I t)) : equiv I t e y = fwd I t e y := rfl

theorem map_equiv (W : Ideal (MvPolynomial (Fin n) F)) :
    ((W.map (mkQ I t)).map (C : ChartQ I t →+* MvPolynomial (Fin e × Fin n) (ChartQ I t))).map
        (equiv I t e : MvPolynomial (Fin e × Fin n) (ChartQ I t) →+* MvPolynomial (Fin e) (ChartInc I t e)) =
      (W.map (chartX I t e)).map (C : ChartInc I t e →+* MvPolynomial (Fin e) (ChartInc I t e)) := by
  have h1 : (equiv I t e : MvPolynomial (Fin e × Fin n) (ChartQ I t) →+* MvPolynomial (Fin e) (ChartInc I t e)).comp
      C = C.comp (toInc I t e) := RingHom.ext fun q => fwd_C I t e q
  have h2 : (toInc I t e).comp (mkQ I t) = chartX I t e := RingHom.ext fun _ => rfl
  rw [Ideal.map_map, h1, ← Ideal.map_map, Ideal.map_map (mkQ I t), h2]

theorem proof (h₁ : OrdPolynomialLocalization.Statement) : ChartIncOrd.Statement := by
  intro F _ n e I W t _ _ x
  have := isPrime_map_C (Fin e × Fin n) (W.map (mkQ I t))
  have := isPrime_map_C (Fin e) (W.map (chartX I t e))
  have hIJ : (W.map (mkQ I t)).map (C : ChartQ I t →+* MvPolynomial (Fin e × Fin n) (ChartQ I t)) =
      ((W.map (chartX I t e)).map (C : ChartInc I t e →+* MvPolynomial (Fin e) (ChartInc I t e))).comap (equiv I t e) := by
    rw [← Ideal.comap_coe, ← map_equiv]
    exact (Ideal.comap_map_of_bijective _ (equiv I t e).bijective).symm
  have h2 := ord_atPrime_ringEquiv (equiv I t e) _ _ hIJ (C (mkQ I t x))
  rw [equiv_apply, fwd_C, toInc_mk] at h2
  exact (h₁ (ChartInc I t e) (Fin e) (W.map (chartX I t e)) (chartX I t e x)).symm.trans
    (h2.trans (h₁ (ChartQ I t) (Fin e × Fin n) (W.map (mkQ I t)) (mkQ I t x)))

end ChartIncOrd

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ChowForms.PChowFormExists
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

theorem constantCoeff_eq_zero_of_isProjPrime {F : Type*} [Field F] {n : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P) {f : MvPolynomial (Fin n) F}
    (hf : f ∈ P) : constantCoeff f = 0 := by
  by_contra h
  have h0 : homogeneousComponent 0 f ∈ P := hP.isHomog f hf 0
  rw [homogeneousComponent_zero] at h0
  apply hP.isPrime.ne_top
  refine Ideal.eq_top_of_isUnit_mem _ h0 ?_
  have hc : coeff 0 f ≠ 0 := by simpa [constantCoeff] using h
  exact hc.isUnit.map C

theorem one_le_of_isProjPrime {F : Type*} [Field F] {n k : ℕ}
    {P : Ideal (MvPolynomial (Fin n) F)} (hP : IsProjPrime P)
    (hk : ringKrullDim (MvPolynomial (Fin n) F ⧸ P) = ((k : ℕ) : WithBot ℕ∞)) : 1 ≤ k := by
  rcases Nat.eq_zero_or_pos k with rfl | h
  · exfalso
    have := hP.isPrime
    have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) F ⧸ P) := by
      rw [ringKrullDimZero_iff_ringKrullDim_eq_zero]
      simpa using hk
    have hmax : P.IsMaximal :=
      Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain
    have hle : P ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin n) F →+* F) :=
      fun f hf => constantCoeff_eq_zero_of_isProjPrime hP hf
    have heq := hmax.eq_of_le (RingHom.ker_ne_top _) hle
    obtain ⟨j, hj⟩ := hP.isRelevant
    rw [heq] at hj
    exact hj (by simp [RingHom.mem_ker])
  · exact h

theorem ChowFormExists.proof (h₁ : IncIdealDim.Statement) (h₂ : IncIdealPrime.Statement) :
    ChowFormExists.Statement := by
  intro F _ n k P hP hdim
  have hk : 1 ≤ k := one_le_of_isProjPrime hP hdim
  obtain ⟨j, -⟩ := hP.isRelevant
  have hn : 0 < n := j.pos
  have hQ : (incIdeal P k).IsPrime := h₂ F n k P hP.isPrime hP.isRelevant
  have hdimQ := h₁ F n k (k - 1) P hP (by rw [Nat.sub_add_cancel hk]; exact hdim)
  have hS : ringKrullDim (MvPolynomial (Fin k × Fin n) F) = ((k * n : ℕ) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field,
      Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, zero_add]
  have hsum := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient F (incIdeal P k)
  rw [hdimQ, hS] at hsum
  have hkn : k ≤ k * n := Nat.le_mul_of_pos_right k hn
  obtain ⟨m, hm1, hm2⟩ : ∃ m, k * n - k + min k (k - 1) = m ∧ m + 1 = k * n :=
    ⟨_, rfl, by generalize k * n = N at hkn ⊢; omega⟩
  rw [hm1, ← hm2] at hsum
  have hht : (incIdeal P k).height = 1 := by
    generalize (incIdeal P k).height = h at hsum
    have h' : (h + m : ℕ∞) = ((m + 1 : ℕ) : ℕ∞) := by
      have : ((h + m : ℕ∞) : WithBot ℕ∞) = (((m + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        push_cast at hsum ⊢
        exact hsum
      exact_mod_cast this
    induction h using ENat.recTopCoe with
    | top => exact (ENat.natCast_ne_top (m + 1) h'.symm).elim
    | coe a =>
      norm_cast at h' ⊢
      omega
  have hne : incIdeal P k ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hht
  obtain ⟨g, hgmem, hgp⟩ := Ideal.IsPrime.exists_mem_prime_of_ne_bot hQ hne
  have hspan := Ideal.eq_span_singleton_of_height_eq_one hht hgmem hgp
  refine ⟨g, hgp.ne_zero, fun f => ?_⟩
  rw [← Ideal.mem_span_singleton, ← hspan]
  simp only [incIdeal, Submodule.mem_iInf, RingHom.mem_ker]

end GroundTheory.Heights₂.Heights
end

