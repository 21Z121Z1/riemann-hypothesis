import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0010
import Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoHostA
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0011
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0018
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0044
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0017

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.KftwoHost
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

namespace Biq

variable {F : Type} [Field F] [NumberField F] {m : ℕ} (B : Biq F m)

def W : 𝓞 F := ⟨B.w, B.integral_w⟩

def J : 𝓞 F := ⟨B.i, B.integral_i⟩

def mk4 (v : ℤ × ℤ × ℤ × ℤ) : 𝓞 F := v.1 + v.2.1 * B.W + v.2.2.1 * B.J + v.2.2.2 * (B.W * B.J)

theorem coe_W : algebraMap (𝓞 F) F B.W = B.w := rfl
theorem coe_J : algebraMap (𝓞 F) F B.J = B.i := rfl

theorem W_sq : B.W * B.W = B.W - m := RingOfIntegers.ext (by
  simpa only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_natCast, coe_W] using B.w_sq)

theorem J_sq : B.J * B.J = -1 := RingOfIntegers.ext (by
  simpa only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_neg, map_one, coe_J] using B.i_sq)

theorem coe_mk_quad (v : ℤ × ℤ × ℤ × ℤ) : algebraMap (𝓞 F) F (B.mk4 v) =
    v.1 + v.2.1 * B.w + v.2.2.1 * B.i + v.2.2.2 * (B.w * B.i) := by
  simp only [mk4, map_add, map_mul, map_intCast, coe_W, coe_J]

theorem mk_quad_injective : Function.Injective B.mk4 := fun v v' h => by
  have h' := congrArg (algebraMap (𝓞 F) F) h
  rw [coe_mk_quad, coe_mk_quad] at h'
  obtain ⟨h1, h2, h3, h4⟩ := B.indep (v.1 - v'.1) (v.2.1 - v'.2.1) (v.2.2.1 - v'.2.2.1) (v.2.2.2 - v'.2.2.2) (by
    push_cast; linear_combination h')
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact_mod_cast sub_eq_zero.1 h1
  · exact_mod_cast sub_eq_zero.1 h2
  · exact_mod_cast sub_eq_zero.1 h3
  · exact_mod_cast sub_eq_zero.1 h4

theorem mk_quad_surjective {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) : Function.Surjective B.mk4 := fun x => by
  obtain ⟨a, b, c, e, h⟩ := B.coords hd hp x.isIntegral_coe
  exact ⟨(a, b, c, e), RingOfIntegers.ext (by rw [RingOfIntegers.coe_eq_algebraMap, coe_mk_quad]; exact h.symm)⟩

theorem σ_σ (x : F) : B.σ (B.σ x) = x := by
  obtain ⟨a, b, c, e, rfl⟩ := B.span x
  simp only [map_add, map_mul, map_ratCast, B.σw, B.σi, map_neg, neg_neg]

def σO : 𝓞 F ≃+* 𝓞 F :=
  RingOfIntegers.mapRingEquiv (RingEquiv.ofRingHom B.σ B.σ (RingHom.ext B.σ_σ) (RingHom.ext B.σ_σ))

theorem sigma_W : B.σO B.W = B.W := RingOfIntegers.ext B.σw

theorem σO_J : B.σO B.J = -B.J := RingOfIntegers.ext B.σi

variable [IsCMField F]

theorem complexConj_eq (hm : 0 < m) (x : F) : IsCMField.complexConj F x = B.σ (B.τ x) := by
  obtain ⟨φ⟩ : Nonempty (F →+* ℂ) := inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj, B.conj_eq hm]

include B in
theorem unramified {d : ℕ} (hd : d + 1 = 4 * m) (hp : d.Prime) :
    Algebra.Unramified (𝓞 (maximalRealSubfield F)) (𝓞 F) := by
  have hm : 0 < m := by omega
  let R := 𝓞 (maximalRealSubfield F)
  let δ := KaehlerDifferential.D R (𝓞 F)
  have h1 : (2 * B.J) • δ B.J = 0 := by
    have := congrArg δ B.J_sq
    rw [Derivation.leibniz, map_neg, Derivation.map_one_eq_zero, neg_zero] at this
    rw [two_mul, add_smul, this]
  have h2 : (2 * B.W - 1) • δ B.W = 0 := by
    have := congrArg δ B.W_sq
    rw [Derivation.leibniz, map_sub, Derivation.map_natCast, sub_zero] at this
    rw [two_mul, sub_smul, add_smul, this, one_smul, sub_self]
  have h3 : δ (B.J * (B.W + B.W - 1)) = 0 := by
    obtain ⟨r, hr⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff F (B.J * (B.W + B.W - 1))).1
      (RingOfIntegers.ext (by
        rw [IsCMField.coe_ringOfIntegersComplexConj, B.complexConj_eq hm]
        simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_sub, map_add, map_one, coe_W, coe_J, B.τi, B.τw,
          B.σi, B.σw]
        ring))
    rw [← hr, Derivation.map_algebraMap]
  rw [Derivation.leibniz, map_sub, map_add, Derivation.map_one_eq_zero, sub_zero] at h3
  have hJ : δ B.J = 0 := by
    have e : (1 : 𝓞 F) = -(2 * m * B.J) * (2 * B.J) + (2 * B.W - 1) * (B.W + B.W - 1) := by
      linear_combination (4 * m : 𝓞 F) * B.J_sq - 4 * B.W_sq
    have e2 : (2 * B.W - 1) • ((B.W + B.W - 1) • δ B.J) = 0 := by
      rw [eq_neg_of_add_eq_zero_right h3, smul_neg, smul_comm, smul_add, h2, add_zero, smul_zero, neg_zero]
    rw [← one_smul (𝓞 F) (δ B.J), e, add_smul, mul_smul, mul_smul (2 * B.W - 1), h1, e2, smul_zero, add_zero]
  have hW : δ B.W = 0 := by
    rw [hJ, smul_zero, add_zero, ← two_smul (𝓞 F), smul_smul] at h3
    have e : (1 : 𝓞 F) = -(2 * m * B.J) * (B.J * 2) + (2 * B.W - 1) * (2 * B.W - 1) := by
      linear_combination (4 * m : 𝓞 F) * B.J_sq - 4 * B.W_sq
    rw [← one_smul (𝓞 F) (δ B.W), e, add_smul, mul_smul, mul_smul (2 * B.W - 1), h3, h2, smul_zero, smul_zero, add_zero]
  have hall : ∀ x, δ x = 0 := fun x => by
    obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd hp x
    simp only [mk4, map_add, Derivation.leibniz, hW, hJ, Derivation.map_intCast, smul_zero, add_zero]
  have hs : Subsingleton (Ω[𝓞 F⁄R]) := by
    rw [← Submodule.subsingleton_iff (𝓞 F), ← subsingleton_iff_bot_eq_top, eq_comm,
      ← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨x, rfl⟩
    exact hall x
  have : Algebra.FormallyUnramified R (𝓞 F) := ⟨hs⟩
  have : Algebra.FiniteType R (𝓞 F) := Algebra.FiniteType.of_restrictScalars_finiteType ℤ R (𝓞 F)
  exact {}

end Biq

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def mat (w : 𝓞 E) (v : ℤ × ℤ × ℤ × ℤ) : Matrix (Fin 2) (Fin 2) (𝓞 E) :=
  !![v.1 + v.2.1 * w, -(v.2.2.1 + v.2.2.2 * w); v.2.2.1 + v.2.2.2 * w, v.1 + v.2.1 * w]

set_option maxHeartbeats 1600000 in

theorem exists_pairHost {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ (E' : Type) (_ : Field E') (_ : NumberField E') (_ : IsCMField E') (H' : Host E'), Nonempty (PairHost H H') := by
  obtain ⟨m, hd⟩ : ∃ m, H.d + 1 = 4 * m := ⟨(H.d + 1) / 4, by have := H.d_mod; omega⟩
  have hm : 0 < m := by omega
  obtain ⟨F, _, _, ⟨B⟩⟩ := exists_biq m (by rw [show 4 * m - 1 = H.d by omega]; exact H.d_prime)
  have := B.numberField
  have := B.isCMField hm
  have hdO : (H.d : 𝓞 F) + 1 = 4 * m := by exact_mod_cast hd
  let H' : Host F :=
    { d := H.d, d_mod := H.d_mod, d_prime := H.d_prime, rt := 2 * B.W - 1
      rt_sq := by linear_combination 4 * B.W_sq + hdO
      w0 := B.W, two_weight_eq_one_add_root := by ring
      bar := (IsCMField.ringOfIntegersComplexConj F).toRingEquiv
      bar_eq := fun _ => rfl
      unram := B.unramified hd H.d_prime
      rt0 := H.rt0, sqrt_neg_disc_sq := H.sqrt_neg_disc_sq }
  have hbW : H'.bar B.W = 1 - B.W := GlobalTheory.HostModel.cmHost_bar_halfIntegerGenerator H'
  have hbJ : H'.bar B.J = -B.J := RingOfIntegers.ext (by
    rw [H'.bar_eq, B.complexConj_eq hm]
    show B.σ (B.τ B.i) = -B.i
    rw [B.τi, B.σi])
  have hw : H.w0 * H.w0 = H.w0 - m := by
    have hdE : (H.d : 𝓞 E) + 1 = 4 * m := by exact_mod_cast hd
    have h1 := H.rt_sq
    rw [GlobalTheory.HostModel.rt_eq] at h1
    have : (4 : 𝓞 E) * (H.w0 * H.w0 - (H.w0 - m)) = 0 := by linear_combination h1 - hdE
    exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (by norm_num))
  let e := Equiv.ofBijective B.mk4 ⟨B.mk_quad_injective, B.mk_quad_surjective hd H.d_prime⟩
  have he : ∀ (x : 𝓞 F) v, x = B.mk4 v → mat H.w0 (e.symm x) = mat H.w0 v := by
    rintro _ v rfl
    rw [show e.symm (B.mk4 v) = v from e.symm_apply_apply v]
  let ψ : 𝓞 F →+* Matrix (Fin 2) (Fin 2) (𝓞 E) :=
    { toFun := fun x => mat H.w0 (e.symm x)
      map_one' := by
        rw [he 1 (1, 0, 0, 0) (by simp [Biq.mk4])]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
      map_zero' := by
        rw [he 0 (0, 0, 0, 0) (by simp [Biq.mk4])]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
      map_add' := fun x y => by
        obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
        obtain ⟨⟨a', b', c', f'⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime y
        rw [he _ _ rfl, he _ _ rfl, he _ (a + a', b + b', c + c', f + f') (by simp only [Biq.mk4]; push_cast; ring)]
        ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
      map_mul' := fun x y => by
        obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
        obtain ⟨⟨a', b', c', f'⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime y
        rw [he _ _ rfl, he _ _ rfl, he _ (a * a' - m * b * b' - c * c' + m * f * f',
          a * b' + b * a' + b * b' - c * f' - f * c' - f * f', a * c' + c * a' - m * b * f' - m * f * b',
          a * f' + b * c' + b * f' + c * b' + f * a' + f * b') (by
            simp only [Biq.mk4]; push_cast
            linear_combination ((b * b' + (b * f' + f * b') * B.J - f * f' : 𝓞 F)) * B.W_sq +
              ((c + f * B.W) * (c' + f' * B.W) : 𝓞 F) * B.J_sq)]
        ext1 i j
        fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_apply, Fin.sum_univ_two]
        · linear_combination (f * f' - b * b' : 𝓞 E) * hw
        · linear_combination (b * f' + f * b' : 𝓞 E) * hw
        · linear_combination (-(b * f' + f * b') : 𝓞 E) * hw
        · linear_combination (f * f' - b * b' : 𝓞 E) * hw }
  have hψ : ∀ (x : 𝓞 F) v, x = B.mk4 v → ψ x = mat H.w0 v := he
  clear_value ψ
  refine ⟨F, inferInstance, inferInstance, inferInstance, H', ⟨⟨ψ, B.σO, fun x i j => ?_, ?_, fun x => ?_, ?_,
    fun k _ _ τ τ' h => ?_⟩⟩⟩
  · obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
    rw [hψ _ _ rfl, hψ _ (a + b, -b, -c - f, f) (by
      simp only [Biq.mk4, map_add, map_mul, map_intCast, hbW, hbJ]; push_cast; ring)]
    fin_cases i <;> fin_cases j <;> simp [mat] <;> ring
  · rw [hψ _ (0, 1, 0, 0) (by simp [Biq.mk4, H'])]
    ext1 i j; fin_cases i <;> fin_cases j <;> simp [mat]
  · obtain ⟨⟨a, b, c, f⟩, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
    rw [hψ _ _ rfl, hψ _ (a, b, -c, -f) (by
      simp only [Biq.mk4, map_add, map_mul, map_intCast, B.sigma_W, B.σO_J]; push_cast; ring)]
    ext1 i j
    fin_cases i <;> fin_cases j <;> simp [mat, Matrix.mul_diagonal, Matrix.diagonal_mul] <;> ring
  · show B.σO (2 * B.W - 1) = 2 * B.W - 1
    rw [map_sub, map_mul, map_ofNat, map_one, B.sigma_W]
  · have hW : τ' B.W = τ B.W := by
      change τ (2 * B.W - 1) = τ' (2 * B.W - 1) at h
      simp only [map_sub, map_mul, map_ofNat, map_one] at h
      linear_combination (-1 / 2 : k) * h
    have h1 := congrArg τ B.J_sq
    have h2 := congrArg τ' B.J_sq
    simp only [map_mul, map_neg, map_one] at h1 h2
    have : (τ' B.J - τ B.J) * (τ' B.J + τ B.J) = 0 := by linear_combination h2 - h1
    rcases mul_eq_zero.1 this with h3 | h3
    · refine Or.inl (RingHom.ext fun x => ?_)
      obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
      simp only [Biq.mk4, map_add, map_mul, map_intCast, hW, sub_eq_zero.1 h3]
    · refine Or.inr (RingHom.ext fun x => ?_)
      obtain ⟨v, rfl⟩ := B.mk_quad_surjective hd H.d_prime x
      show _ = τ (B.σO _)
      simp only [Biq.mk4, map_add, map_mul, map_intCast, hW, eq_neg_of_add_eq_zero_left h3, B.sigma_W, B.σO_J, map_neg]

end PositivityTheory.HtPt.Kftwo
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinExists
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinExists

theorem join_exists : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (κ' : Type) [Finite κ'] (w : κ' → Ω'), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → (∃ l, w l ≠ 0) → Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ → ∃ (M' : PModel o (joinCo i x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f i := by
  intro o _ Ω _ _ κ _ x M Ω' _ _ i κ' _ w hi ⟨l, hl⟩ hcl
  let p : Cpt M.ξ := ⟨genPt M.ξ, specializes_rfl⟩
  obtain ⟨c, hc⟩ := M.tie.cover p
  have hic : i (x c) ≠ 0 := (map_ne_zero i).2 hc.1
  have hJ : joinCo i x w (c, l) ≠ 0 := mul_ne_zero hic hl
  have hgen : ∀ j l', joinCo i x w (j, l') / joinCo i x w (c, l) ∈ chRing o (joinCo i x w) (c, l) :=
    fun j l' => Algebra.subset_adjoin ⟨(j, l'), rfl⟩
  have hmap : ∀ a ∈ chRing o x c, i a ∈ chRing o (joinCo i x w) (c, l) := by
    intro a ha
    have ha' : a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := ha
    induction ha' using Algebra.adjoin_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      have : i (x j / x c) = joinCo i x w (j, l) / joinCo i x w (c, l) := by
        simp only [joinCo, map_div₀]
        rw [mul_div_mul_right _ _ hl]
      rw [this]
      exact hgen _ _
    | algebraMap r =>
      rw [hi]
      exact Subalgebra.algebraMap_mem _ r
    | add y z _ _ hy hz =>
      rw [map_add]
      exact add_mem (hy (by assumption)) (hz (by assumption))
    | mul y z _ _ hy hz =>
      rw [map_mul]
      exact mul_mem (hy (by assumption)) (hz (by assumption))
  have hAF : ∀ a ∈ chRing o (joinCo i x w) (c, l),
      a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') :=
    fun a ha => Subfield.subset_closure ha
  have hiF : ∀ a : Ω, i a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
    intro a
    have h2 := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hc).2
    have key : ∀ b ∈ regAt M.ξ p, i b ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
      intro b hb
      obtain ⟨s, hs, t, ht, -, rfl⟩ := (h2 b).1 hb
      rw [map_div₀]
      exact div_mem (hAF _ (hmap _ hs)) (hAF _ (hmap _ ht))
    obtain ⟨u, hu, v, hv, -, rfl⟩ := (PositivityTheory.HtPt.Ma.reg_local M.X Ω M.ξ).2.2 M.tie.gen p a
    rw [map_div₀]
    exact div_mem (key u hu) (key v hv)
  have hw : ∀ l', w l' / w l ∈ chRing o (joinCo i x w) (c, l) := by
    intro l'
    have : w l' / w l = joinCo i x w (c, l') / joinCo i x w (c, l) := by
      simp only [joinCo]
      rw [mul_div_mul_left _ _ hic]
    rw [this]
    exact hgen _ _
  have hle : Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) ≤
      Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') := by
    refine Subfield.closure_le.2 (Set.union_subset ?_ ?_)
    · rintro _ ⟨a, rfl⟩
      exact hiF a
    · rintro _ ⟨a, b, rfl⟩
      rw [← div_div_div_cancel_right₀ hl (w a) (w b)]
      exact div_mem (hAF _ (hw a)) (hAF _ (hw b))
  have hfrac : ∀ a : Ω', ∃ u ∈ chRing o (joinCo i x w) (c, l), ∃ v ∈ chRing o (joinCo i x w) (c, l),
      a = u / v := by
    intro a
    have ha : a ∈ Subfield.closure (chRing o (joinCo i x w) (c, l) : Set Ω') :=
      hle (by rw [hcl]; exact Subfield.mem_top a)
    obtain ⟨y, hy, z, hz, rfl⟩ := Subfield.mem_closure_iff.1 ha
    have hs : Subring.closure (chRing o (joinCo i x w) (c, l) : Set Ω') =
        (chRing o (joinCo i x w) (c, l)).toSubring :=
      Subring.closure_eq (chRing o (joinCo i x w) (c, l)).toSubring
    rw [hs] at hy hz
    exact ⟨y, hy, z, hz, rfl⟩
  obtain ⟨M'⟩ := GlobalTheory.T.projective_model_nonempty o Ω' (κ × κ') (joinCo i x w) ⟨(c, l), hJ, hfrac⟩
  have hctr : ∀ p', p' ∈ ctrSet o x i M'.ξ := fun p' => (PositivityTheory.HtPt.Mb.join_charts o Ω κ κ' x Ω' i w M' hi p').1
  obtain ⟨f, hf, -⟩ := PositivityTheory.HtPt.Mb.morph o Ω κ x M o Ω' (κ × κ') (joinCo i x w) M' i hctr
  exact ⟨M', f, hf⟩

end PositivityTheory.HtPt.Mb.LJoinExists

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.join_exists : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (i : Ω →+* Ω') (κ' : Type) [Finite κ'] (w : κ' → Ω'), (∀ a : o, i (algebraMap o Ω a) = algebraMap o Ω' a) → (∃ l, w l ≠ 0) → Subfield.closure (Set.range i ∪ {a | ∃ l l', a = w l / w l'}) = ⊤ → ∃ (M' : PModel o (joinCo i x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f i :=
  @PositivityTheory.HtPt.Mb.LJoinExists.join_exists
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.MbLJoinIso
section
open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField

namespace PositivityTheory.HtPt.Mb.LJoinIso.JoinIso

theorem chRing_mem {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {ι : Type} {J : ι → Ω} {d : ι}
    {S : Subring Ω} (ho : ∀ r : o, algebraMap o Ω r ∈ S) (h : ∀ q, J q / J d ∈ S) :
    ∀ a ∈ chRing o J d, a ∈ S := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨q, rfl⟩ := hy
    exact h q
  | algebraMap r => exact ho r
  | add _ _ _ _ h1 h2 => exact add_mem h1 h2
  | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

theorem eq_of_units {o : Type} [CommRing o] {Ω : Type} [Field Ω] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω}
    (M : PModel o x) {c : κ} {p q : Cpt M.ξ} (hp : InChart M.ξ x c p) (hq : InChart M.ξ x c q)
    (h : ∀ u ∈ chRing o x c, unitAt M.ξ p u ↔ unitAt M.ξ q u) : p = q := by
  have hle : ∀ {p q : Cpt M.ξ}, InChart M.ξ x c p → InChart M.ξ x c q →
      (∀ u ∈ chRing o x c, unitAt M.ξ p u → unitAt M.ξ q u) → regAt M.ξ p ≤ regAt M.ξ q := by
    intro p q hp hq h a ha
    obtain ⟨u, hu, v, hv, hvu, rfl⟩ := ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hp).2 a).1 ha
    exact ((PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c q hq).2 _).2 ⟨u, hu, v, hv, h v hv hvu, rfl⟩
  have h1 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M p q).1 (hle hp hq fun u hu => (h u hu).1)
  have h2 := (PositivityTheory.HtPt.Ma.reg_le_spec o Ω κ x M q p).1 (hle hq hp fun u hu => (h u hu).2)
  exact Subtype.ext (h2.antisymm h1).eq

theorem isoAt_of_chart : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) → ∀ p : Cpt M.ξ, (∃ l, InChart M.ξ w l p) → IsoAt M'.ξ f (RingHom.id Ω) p := by
  intro o _ Ω _ _ κ _ x M κ' _ w M' f hd p ⟨l, hl⟩
  obtain ⟨c, hc⟩ := M.tie.cover p
  have hJ0 : joinCo (RingHom.id Ω) x w (c, l) ≠ 0 := mul_ne_zero hc.1 hl.1
  have ratio : ∀ j m, joinCo (RingHom.id Ω) x w (j, m) / joinCo (RingHom.id Ω) x w (c, l) =
      (x j / x c) * (w m / w l) := fun j m => by
    simp only [joinCo, RingHom.id_apply, mul_div_mul_comm]
  have hpJ : ∀ q, joinCo (RingHom.id Ω) x w q / joinCo (RingHom.id Ω) x w (c, l) ∈ regAt M.ξ p := by
    rintro ⟨j, m⟩
    rw [ratio]
    exact mul_mem (hc.2 j) (hl.2 m)
  have hAp := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c p hc).1
  have hctr : p ∈ ctrSet o (joinCo (RingHom.id Ω) x w) (RingHom.id Ω) M.ξ :=
    ⟨(c, l), hJ0, chRing_mem (fun r => hAp _ (Subalgebra.algebraMap_mem _ r)) hpJ⟩
  obtain ⟨p', ⟨hle', hun'⟩, -, hch'⟩ :=
    PositivityTheory.HtPt.Mb.centre o Ω (κ × κ') (joinCo (RingHom.id Ω) x w) M' M.X Ω M.ξ (RingHom.id Ω) p hctr
  have hle : ∀ a ∈ regAt M'.ξ p', a ∈ regAt M.ξ p := hle'
  have hun : ∀ a ∈ regAt M'.ξ p', unitAt M.ξ p a → unitAt M'.ξ p' a := hun'
  have hp'c : InChart M'.ξ (joinCo (RingHom.id Ω) x w) (c, l) p' := hch' (c, l) hJ0 hpJ
  have dom := PositivityTheory.HtPt.Mb.dom_local M.X Ω M.ξ M'.X Ω M'.ξ (RingHom.id Ω) f hd
  obtain ⟨h, hq1', hq2'⟩ := dom p'
  have hq1 : ∀ a ∈ regAt M.ξ ⟨f p'.1, h⟩, a ∈ regAt M'.ξ p' := hq1'
  have hq2 : ∀ a ∈ regAt M.ξ ⟨f p'.1, h⟩, unitAt M'.ξ p' a → unitAt M.ξ ⟨f p'.1, h⟩ a := hq2'
  have hx : ∀ j, x j / x c ∈ regAt M'.ξ p' := fun j => by
    have e : joinCo (RingHom.id Ω) x w (j, l) / joinCo (RingHom.id Ω) x w (c, l) = x j / x c := by
      rw [ratio, div_self hl.1, mul_one]
    rw [← e]
    exact hp'c.2 (j, l)
  obtain ⟨c₁, hc₁⟩ := M.tie.cover ⟨f p'.1, h⟩
  have hu : unitAt M.ξ ⟨f p'.1, h⟩ (x c / x c₁) :=
    hq2 _ (hc₁.2 c) ⟨div_ne_zero hc.1 hc₁.1, hq1 _ (hc₁.2 c), by rw [inv_div]; exact hx c₁⟩
  have hqc : InChart M.ξ x c ⟨f p'.1, h⟩ := ⟨hc.1, fun j => by
    have e : x j / x c = (x j / x c₁) * (x c / x c₁)⁻¹ := by
      have h1 := hc.1
      have h2 := hc₁.1
      field_simp
    rw [e]
    exact mul_mem (hc₁.2 j) hu.2.2⟩
  have hqp : (⟨f p'.1, h⟩ : Cpt M.ξ) = p := by
    refine eq_of_units M hqc hc fun u hu => ?_
    have uq := (PositivityTheory.HtPt.Ma.regat_loc o Ω κ x M c _ hqc).1 u hu
    exact ⟨fun k => ⟨k.1, hAp u hu, hle _ (hq1 _ k.2.2)⟩, fun k => hq2 u uq (hun u (hq1 u uq) k)⟩
  have e' : f p'.1 = p.1 := congrArg Subtype.val hqp
  rw [hqp] at hq1
  have hreg : regAt M'.ξ p' = regAt M.ξ p := le_antisymm hle hq1
  have uniq : ∀ p'' : Cpt M'.ξ, f p''.1 = p.1 → p'' = p' := by
    intro p'' e
    obtain ⟨h2, r1', r2'⟩ := dom p''
    have e2 : (⟨f p''.1, h2⟩ : Cpt M.ξ) = p := Subtype.ext e
    rw [e2] at r1' r2'
    have r1 : ∀ a ∈ regAt M.ξ p, a ∈ regAt M'.ξ p'' := r1'
    have r2 : ∀ a ∈ regAt M.ξ p, unitAt M'.ξ p'' a → unitAt M.ξ p a := r2'
    have hch : InChart M'.ξ (joinCo (RingHom.id Ω) x w) (c, l) p'' := ⟨hJ0, fun q => r1 _ (hpJ q)⟩
    refine eq_of_units M' hch hp'c fun u hu => ?_
    have up' := (PositivityTheory.HtPt.Ma.regat_loc o Ω (κ × κ') _ M' (c, l) p' hp'c).1 u hu
    have up := hle u up'
    exact ⟨fun k => hun u up' (r2 u up k), fun k => ⟨k.1, r1 u up, r1 _ (hle _ k.2.2)⟩⟩
  refine ⟨⟨p', e', fun p'' e => uniq p'' e⟩, fun p'' e => ?_, hd⟩
  rw [uniq p'' e, hreg, Subring.map_id]

end PositivityTheory.HtPt.Mb.LJoinIso.JoinIso

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar NumberField in

theorem PositivityTheory.HtPt.Mb.join_iso : ∀ (o : Type) [CommRing o] (Ω : Type) [Field Ω] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel o x) (κ' : Type) [Finite κ'] (w : κ' → Ω) (M' : PModel o (joinCo (RingHom.id Ω) x w)) (f : M'.X ⟶ M.X), Dominates M'.ξ M.ξ f (RingHom.id Ω) → ∀ p : Cpt M.ξ, (∃ l, InChart M.ξ w l p) → IsoAt M'.ξ f (RingHom.id Ω) p :=
  @PositivityTheory.HtPt.Mb.LJoinIso.JoinIso.isoAt_of_chart
end

