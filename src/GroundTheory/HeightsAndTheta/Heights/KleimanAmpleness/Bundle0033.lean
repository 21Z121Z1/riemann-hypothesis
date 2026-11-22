import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.StepTwoFiltGraded
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0020
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0007

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapper
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem eulerCharQuot_self {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    (F : SubSystem k x E) : eulerCharQuot k F F = 0 := by
  unfold eulerCharQuot
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : ∀ I, Subsingleton (F.sub I ⧸ SubSystem.quotSub F F I) := fun I =>
    Submodule.Quotient.subsingleton_iff.mpr (eq_top_iff.mpr fun y _ => y.2)
  have h2 : Subsingleton (Cech.Cochain (fun I => F.sub I ⧸ SubSystem.quotSub F F I) i) := by
    unfold Cech.Cochain; infer_instance
  have h3 : Subsingleton (SubSystem.quotH F F i) := by
    unfold SubSystem.quotH Cech.H
    infer_instance
  simp [Module.finrank_zero_of_subsingleton]

theorem subSystem_ext {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]
    {F G : SubSystem k x E} (h : ∀ I, F.sub I = G.sub I) : F = G := by
  obtain ⟨sF, mF⟩ := F
  obtain ⟨sG, mG⟩ := G
  have : sF = sG := funext h
  subst this
  rfl

theorem twist_idealSys_of_irrelevant (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) :
    (twistSys k x a).twist (idealSys x pp) = twistSys k x a := by
  refine subSystem_ext fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  have h1 : (1 : Ω) ∈ (idealSys x pp).sub I :=
    Submodule.subset_span ⟨X i, X i, 1, hpp i, X_mem_monos hi, isHomogeneous_X _ _,
      isHomogeneous_X _ _, by rw [aeval_X, div_self hxi]⟩
  have hle : (idealSys x pp).sub I ≤ 1 := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, s, e, -, hs, hf, hse, rfl⟩
    exact Submodule.mem_one.mpr ⟨⟨_, f, s, e, hs, hf, hse, rfl⟩, rfl⟩
  rw [SubSystem.twist_sub_eq_mul_of_line]
  refine le_antisymm (Submodule.mul_le.mpr fun q hq y hy => ?_) fun y hy => by
    simpa using Submodule.mul_mem_mul h1 hy
  obtain ⟨q', rfl⟩ := Submodule.mem_one.mp (hle hq)
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ q' hy

theorem pieceChar_of_irrelevant (pp : Ideal (Poly k N)) (hpp : ∀ i, (X i : Poly k N) ∈ pp) (a : ℤ) {t : ℕ}
    (L : Fin t → LineBundle k x) (n : Fin t → ℕ) (c : ℤ) : pieceChar k pp a L n c = 0 := by
  unfold pieceChar
  rw [twist_idealSys_of_irrelevant pp hpp a]
  exact eulerCharQuot_self _

end Lemmas

section Dim

variable {R : Type*} [CommRing R]

theorem ringKrullDim_quotient_succ_le_of_lt {pp qq : Ideal R} [pp.IsPrime] (h : pp < qq) :
    ringKrullDim (R ⧸ qq) + 1 ≤ ringKrullDim (R ⧸ pp) := by
  obtain ⟨r, hrq, hrp⟩ := SetLike.exists_of_lt h
  have hr : Ideal.Quotient.mk pp r ∈ nonZeroDivisors (R ⧸ pp) :=
    mem_nonZeroDivisors_of_ne_zero (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  refine le_trans ?_ (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr)
  have hker : ∀ a ∈ Ideal.span {Ideal.Quotient.mk pp r}, Ideal.Quotient.factor h.le a = 0 := by
    intro a ha
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hrq, mul_zero]
  have := ringKrullDim_le_of_surjective _
    (Ideal.Quotient.lift_surjective_of_surjective _ hker (Ideal.Quotient.factor_surjective h.le))
  gcongr

end Dim

section Induction

variable {k : Type u} [Field k] {N : ℕ}

theorem one_le_ringKrullDim_of_relevant (pp : Ideal (Poly k N)) [pp.IsPrime]
    (hh : ∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) (hrel : ∃ i, (X i : Poly k N) ∉ pp) :
    1 ≤ ringKrullDim (Poly k N ⧸ pp) := by
  obtain ⟨i, hi⟩ := hrel
  have hle : pp ≤ RingHom.ker (constantCoeff : Poly k N →+* k) := by
    intro f hf
    rw [RingHom.mem_ker]
    by_contra h0
    have h1 := hh f hf 0
    rw [homogeneousComponent_zero] at h1
    have h0' : coeff 0 f ≠ 0 := by rwa [← constantCoeff_eq]
    have hu : IsUnit (C (coeff 0 f) : Poly k N) := (isUnit_iff_ne_zero.mpr h0').map C
    exact Ideal.IsPrime.ne_top ‹_› (Ideal.eq_top_of_isUnit_mem _ h1 hu)
  have hlt : pp < RingHom.ker (constantCoeff : Poly k N →+* k) :=
    lt_of_le_of_ne hle fun h => hi (h ▸ by simp [RingHom.mem_ker])
  have hnt : Nontrivial (Poly k N ⧸ RingHom.ker (constantCoeff : Poly k N →+* k)) :=
    Ideal.Quotient.nontrivial_iff.mpr (RingHom.ker_ne_top _)
  calc (1 : WithBot ℕ∞) = 0 + 1 := by simp
    _ ≤ ringKrullDim (Poly k N ⧸ RingHom.ker (constantCoeff : Poly k N →+* k)) + 1 :=
        by gcongr; exact ringKrullDim_nonneg_of_nontrivial
    _ ≤ ringKrullDim (Poly k N ⧸ pp) := ringKrullDim_quotient_succ_le_of_lt hlt

theorem withBot_le_of_succ_le {d : WithBot ℕ∞} {D : ℕ} (h : d + 1 ≤ ((D + 1 : ℕ) : WithBot ℕ∞)) :
    d ≤ (D : WithBot ℕ∞) := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe d =>
    have h' : d + 1 ≤ (D : ℕ∞) + 1 := by exact_mod_cast h
    exact_mod_cast (ENat.add_le_add_iff_right ENat.one_ne_top).mp h'

theorem isNumPolyLT_sum {t D r : ℕ} (g : Fin r → (Fin t → ℕ) → ℤ → ℚ) (h : ∀ m, IsNumPolyLT t D (g m)) :
    IsNumPolyLT t D (fun n c => ∑ m, g m n c) := by
  choose Q hQ hev using h
  refine ⟨∑ m, Q m, ?_, fun n c => by simp [hev, map_sum]⟩
  rcases Nat.eq_zero_or_pos D with hD | hD
  · left
    subst hD
    exact Finset.sum_eq_zero fun m _ => (hQ m).resolve_right (Nat.not_lt_zero _)
  · right
    refine lt_of_le_of_lt (totalDegree_finsetSum _ _) ?_
    rw [Finset.sup_lt_iff (by simpa using hD)]
    intro m _
    rcases hQ m with h0 | h0
    · rw [h0, totalDegree_zero]; exact hD
    · exact h0

theorem IsNumPolyLT.congr {t D : ℕ} {f g : (Fin t → ℕ) → ℤ → ℚ} (h : IsNumPolyLT t D f)
    (hfg : ∀ n c, f n c = g n c) : IsNumPolyLT t D g := by
  obtain ⟨Q, hQ, hev⟩ := h
  exact ⟨Q, hQ, fun n c => (hfg n c).symm.trans (hev n c)⟩

variable {Ω : Type w} [Field Ω] [Algebra k Ω] {x : Fin (N + 1) → Ω}

theorem pieceChar_isNumPolyLT (hH : SnapperHyperplane.Statement.{u, w}) (hS : SnapperSection.Statement.{u, w})
    (hP : SnapperDiffPoly.Statement) {t : ℕ} (L : Fin t → LineBundle k x) (D : ℕ) :
    ∀ (pp : Ideal (Poly k N)), pp.IsPrime → (∀ f ∈ pp, ∀ d : ℕ, homogeneousComponent d f ∈ pp) →
      primeOf (S := k) x ≤ pp → ringKrullDim (Poly k N ⧸ pp) ≤ (D : WithBot ℕ∞) →
      ∀ a : ℤ, IsNumPolyLT t D (fun n c => (pieceChar k pp a L n c : ℚ)) := by
  induction D with
  | zero =>
    intro pp hp hh _ hdim a
    by_cases hrel : ∃ i, (X i : Poly k N) ∉ pp
    · have := (one_le_ringKrullDim_of_relevant pp hh hrel).trans hdim
      exact absurd this (by simp)
    · push Not at hrel
      exact ⟨0, Or.inl rfl, fun n c => by simp [pieceChar_of_irrelevant pp hrel]⟩
  | succ D ih =>
    intro pp hp hh hle hdim a
    by_cases hrel : ∃ i, (X i : Poly k N) ∉ pp
    · have key : ∀ (qq : Ideal (Poly k N)) (b : ℤ), qq.IsPrime →
          (∀ f ∈ qq, ∀ d : ℕ, homogeneousComponent d f ∈ qq) → pp < qq →
          IsNumPolyLT t D (fun n c => (pieceChar k qq b L n c : ℚ)) := fun qq b hq hqh hlt =>
        ih qq hq hqh (hle.trans hlt.le)
          (withBot_le_of_succ_le ((ringKrullDim_quotient_succ_le_of_lt hlt).trans hdim)) b
      obtain ⟨i, hi⟩ := hrel
      obtain ⟨r, qq, b, hqq, heq⟩ := hH k Ω N x pp hp hh hle i hi a
      have h0 : IsNumPolyLT t D
          (fun n c => (pieceChar k pp a L n (c + 1) : ℚ) - (pieceChar k pp a L n c : ℚ)) :=
        (isNumPolyLT_sum _ fun m => key (qq m) (b m) (hqq m).1 (hqq m).2.1
          (lt_of_le_of_ne (hqq m).2.2.1 fun h => hi (h ▸ (hqq m).2.2.2))).congr
          fun n c => by exact_mod_cast (heq t L n c).symm
      choose μ r' qq' b' hqq' heq' using fun j => hS k Ω N x pp hp hh hle ⟨i, hi⟩ t L j a
      have hj : ∀ j, IsNumPolyLT t D (fun n c =>
          (pieceChar k pp a L (Function.update n j (n j + 1)) (c + μ j) : ℚ) - (pieceChar k pp a L n c : ℚ)) :=
        fun j => (isNumPolyLT_sum _ fun m => key (qq' j m) (b' j m) (hqq' j m).1 (hqq' j m).2.1
          (hqq' j m).2.2).congr fun n c => by exact_mod_cast (heq' j n c).symm
      exact hP t D (fun n c => (pieceChar k pp a L n c : ℚ)) μ h0 hj
    · push Not at hrel
      exact ⟨0, Or.inl rfl, fun n c => by simp [pieceChar_of_irrelevant pp hrel]⟩

end Induction

theorem Snapper.proof (hD : SnapperDevissage.Statement.{u, v, w}) (hH : SnapperHyperplane.Statement.{u, w})
    (hS : SnapperSection.Statement.{u, w}) (hP : SnapperDiffPoly.Statement) : Snapper.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x e hZ E _ _ _ _ F hF t L
  obtain ⟨r, pp, a, hpp, heq⟩ := hD k Ω N x E F hF
  have hdim : ∀ m, ringKrullDim (Poly k N ⧸ pp m) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := fun m =>
    (ringKrullDim_le_of_surjective _ (Ideal.Quotient.factor_surjective (hpp m).2.2)).trans hZ.dim.le
  obtain ⟨Q, hQ, hev⟩ := isNumPolyLT_sum (fun m n c => (pieceChar k (pp m) (a m) L n c : ℚ))
    fun m => pieceChar_isNumPolyLT hH hS hP L (e + 1) (pp m) (hpp m).1 (hpp m).2.1 (hpp m).2.2 (hdim m) (a m)
  refine ⟨Q, ?_, fun n c => ?_⟩
  · rcases hQ with h0 | h0
    · rw [h0, totalDegree_zero]; exact Nat.zero_le _
    · omega
  · rw [heq t L n c, ← hev n c]
    push_cast
    rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperDevissage
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w u₁ v₁ w₁

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u₁} [CommRing R]
  {G : Cell U → Type v₁} [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)]
  {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}
  {G' : Cell U → Type w₁} [∀ I, AddCommGroup (G' I)] [∀ I, Module R (G' I)]
  {ρ' : ∀ I J : Cell U, I.1 ⊆ J.1 → G' I →ₗ[R] G' J}

def mapH (φ : ∀ I, G I →ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i →ₗ[R] H G' ρ' i :=
  Submodule.mapQ _ _ ((mapC φ i).restrict (p := LinearMap.ker (d G ρ i)) (q := LinearMap.ker (d G' ρ' i))
      (fun s hs => by
        change d G' ρ' i (mapC φ i s) = 0
        rw [← mapC_d φ hφ, show d G ρ i s = 0 from hs, map_zero]))
    (by
      intro s hs
      cases i with
      | zero =>
        change (s : Cochain G 0) ∈ (⊥ : Submodule R _) at hs
        rw [Submodule.mem_bot] at hs
        change (mapC φ 0 s : Cochain G' 0) ∈ (⊥ : Submodule R _)
        rw [hs, map_zero]; exact Submodule.zero_mem _
      | succ i =>
        obtain ⟨t, hts⟩ := hs
        refine ⟨mapC φ i t, ?_⟩
        change d G' ρ' i (mapC φ i t) = mapC φ (i + 1) s
        rw [← mapC_d φ hφ, hts]
        rfl)

def hEquivOfEquiv (φ : ∀ I, G I ≃ₗ[R] G' I) (hφ : ∀ I J h m, φ J (ρ I J h m) = ρ' I J h (φ I m)) (i : ℕ) :
    H G ρ i ≃ₗ[R] H G' ρ' i :=
  have hψ : ∀ I J h m, (φ J).symm (ρ' I J h m) = ρ I J h ((φ I).symm m) := fun I J h m => by
    rw [LinearEquiv.symm_apply_eq, hφ, LinearEquiv.apply_symm_apply]
  LinearEquiv.ofLinearMap (mapH (fun I => (φ I).toLinearMap) hφ i)
    (mapH (fun I => (φ I).symm.toLinearMap) hψ i)
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).apply_symm_apply _))
    (by
      refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _
      congr 1
      exact Subtype.ext (funext fun I => (φ I.1).symm_apply_apply _))

end Cech

section Zero

variable (k : Type u) [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} (x : Fin (N + 1) → Ω)
  (E : Type v) [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]

def zeroFamily : SubFamily k x E where
  sub _ := ⊥
  mono _ _ _ _ hy := hy
  mem_iff I J h y := by
    simp only [Submodule.mem_bot]
    constructor
    · rintro rfl
      exact ⟨1, by simp, by simp⟩
    · rintro ⟨a, ha, hay⟩
      obtain ⟨b, hb⟩ := ha.exists_right_inv
      have hne : (a : Ω) ≠ 0 := by
        intro h0
        have h1 := congrArg (fun z : chartRing k x J => (z : Ω)) hb
        change (a : Ω) * _ = 1 at h1
        rw [h0, zero_mul] at h1
        exact zero_ne_one h1
      exact (smul_eq_zero.mp hay).resolve_left hne

end Zero

section Lemmas

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module k E] [IsScalarTower k Ω E]

omit [Module k E] [IsScalarTower k Ω E] in

theorem twist_sub_eq_bot {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) (Q : SubSystem k x Ω) (I : Chart x) :
    (F.twist Q).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, -, y, hy, rfl⟩
  rw [hF I, Submodule.mem_bot] at hy
  rw [hy, smul_zero]

omit [Module k E] [IsScalarTower k Ω E] in

theorem twistPows_sub_eq_bot {F : SubSystem k x E} (hF : ∀ I, F.sub I = ⊥) :
    ∀ (t : ℕ) (L : Fin t → SubSystem k x Ω) (n : Fin t → ℕ) (I : Chart x), (F.twistPows t L n).sub I = ⊥
  | 0, _, _, I => hF I
  | t + 1, _, _, I => twist_sub_eq_bot (fun I => twistPows_sub_eq_bot hF t _ _ I) _ I

omit [Module k E] [IsScalarTower k Ω E] in

theorem twist_idealSys_primeOf_sub (F : SubSystem k x E) (I : Chart x) :
    (F.twist (idealSys x (primeOf (S := k) x))).sub I = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro _ ⟨q, hq, y, -, rfl⟩
  have hq0 : q = 0 := by
    have h0 : idealMod (primeOf (S := k) x) I = ⊥ := by
      refine Submodule.span_eq_bot.mpr ?_
      rintro _ ⟨f, s, e, hf, _, hfe, _, rfl⟩
      rw [(mem_primeOf_of_isHomogeneous x hfe).mp hf, zero_div]
    have hq' : q ∈ (⊥ : Submodule (chartRing k x I) Ω) := h0 ▸ hq
    exact (Submodule.mem_bot _).mp hq'
  rw [hq0, zero_smul]

theorem eulerCharQuot_of_bot (F₁ F₂ : SubSystem k x E) (h : ∀ I, F₂.sub I = ⊥) :
    eulerCharQuot k F₁ F₂ = eulerChar k F₁ := by
  have hq : ∀ I, SubSystem.quotSub F₁ F₂ I = ⊥ := fun I => by
    refine (Submodule.eq_bot_iff _).mpr fun y hy => Subtype.ext ?_
    have hy' : (y : E) ∈ F₂.sub I := hy
    rw [h I, Submodule.mem_bot] at hy'
    exact hy'
  let φ : ∀ I, F₁.sub I ≃ₗ[k] (F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I) := fun I =>
    (Submodule.quotEquivOfEqBot _ (hq I)).symm
  have hφ : ∀ I J h m, φ J (F₁.res I J h m) = SubSystem.quotRes F₁ F₂ I J h (φ I m) := fun _ _ _ _ => rfl
  unfold eulerCharQuot eulerChar
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 2
  exact ((Cech.hEquivOfEquiv φ hφ i).finrank_eq).symm

end Lemmas

theorem SnapperDevissage.proof (hQ : SnapperQuotDevissage.Statement.{u, v, w}) :
    SnapperDevissage.Statement.{u, v, w} := by
  intro k _ Ω _ _ N x E _ _ _ _ F hF
  obtain ⟨r, pp, a, hpp, heq⟩ := hQ k Ω N x E F (zeroFamily k x E) hF (fun _ => bot_le)
    (primeOf (S := k) x) (fun f hf d => homogeneousComponent_mem_primeOf x hf d) le_rfl
    (fun I => (twist_idealSys_primeOf_sub F.toSubSystem I).le)
  refine ⟨r, pp, a, hpp, fun t L n c => ?_⟩
  rw [← heq t L n c]
  exact (eulerCharQuot_of_bot _ _ fun I =>
    twist_sub_eq_bot (twistPows_sub_eq_bot (fun _ => rfl) t _ n) _ I).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepTwoFilt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

theorem StepTwo.Filt.proof (h : PrimeFiltration.Exists.Statement.{u, v, w}) :
    StepTwo.Filt.Statement.{u, v, w} := by
  intro S _ _ Ω _ _ N x E _ _ _ _ M₁ M₂ hle J hJ
  classical
  obtain ⟨⟨F⟩, -⟩ := h S Ω N x (quotLaurent M₁ M₂) (quotLaurentGraded M₁ M₂) (quotLaurent_finite M₁ M₂)
    fun p hp y => quotLaurent_smul_eq_zero M₁ M₂ hp y
  have hrep : ∀ k, ∃ g : M₁.piece (F.deg k), quotIota M₁ M₂ (F.deg k) g = F.gen k :=
    fun k => LinearMap.mem_range.mp (F.gen_mem k)
  choose g hg using hrep
  have hstab : ∀ k : Fin (F.n + 1), IsProjStable M₁ M₂ (F.step k) := by
    intro k
    induction k using Fin.induction with
    | zero => rw [F.step_zero]; exact isProjStable_bot
    | succ k ih => rw [F.step_succ k, ← hg k]; exact isProjStable_sup ih (g k)
  have hfg : ∀ k : Fin (F.n + 1), ∃ (n : ℕ) (deg : Fin n → ℤ) (gen : Fin n → E),
      (∀ j, gen j ∈ filtPiece M₁ M₂ (F.step k) (deg j)) ∧
      ∀ c, filtPiece M₁ M₂ (F.step k) c ≤ Submodule.span S {z | ∃ (j : Fin n) (f : Poly S N) (e : ℕ),
        f.IsHomogeneous e ∧ (e : ℤ) + deg j = c ∧ z = aeval x f • gen j} := by
    intro k
    induction k using Fin.induction with
    | zero =>
      rw [F.step_zero]
      simp only [filtPiece_bot hle]
      exact M₂.fg
    | succ k ih =>
      obtain ⟨n, deg, gen, hmem, hspan⟩ := ih
      have hsup := filtPiece_sup (hstab k.castSucc) (g k)
      rw [F.step_succ k, ← hg k]
      refine ⟨n + 1, Fin.cons (F.deg k) deg, Fin.cons (g k : E) gen, fun j => ?_, fun c => ?_⟩
      · refine Fin.cases ?_ (fun j => ?_) j
        · rw [Fin.cons_zero, Fin.cons_zero, hsup]
          refine Submodule.mem_sup_right (Submodule.subset_span ⟨1, 0, isHomogeneous_one _ _, by simp, ?_⟩)
          rw [map_one, one_smul]
        · rw [Fin.cons_succ, Fin.cons_succ]
          exact filtPiece_mono le_sup_left _ (hmem j)
      · rw [hsup]
        refine sup_le ((hspan c).trans (Submodule.span_mono ?_)) (Submodule.span_mono ?_)
        · rintro _ ⟨j, f, e, hf, he, rfl⟩
          exact ⟨j.succ, f, e, hf, by rw [Fin.cons_succ]; exact he, by rw [Fin.cons_succ]⟩
        · rintro _ ⟨f, d, hf, hd, rfl⟩
          exact ⟨0, f, d, hf, by rw [Fin.cons_zero]; omega, by rw [Fin.cons_zero]⟩
  refine ⟨F.n, fun k => filtSub M₁ M₂ (F.step k) (hfg k), fun k => (g k : E), F.deg, F.prime, ?_, ?_,
    fun k => ⟨F.isPrime k, F.isHomogeneous k, ?_, ?_, ?_, ?_, ?_⟩⟩
  · refine FinGradedSub.eq_of_piece_eq (funext fun c => ?_)
    change filtPiece M₁ M₂ (F.step 0) c = _
    rw [F.step_zero, filtPiece_bot hle]
  · refine FinGradedSub.eq_of_piece_eq (funext fun c => ?_)
    change filtPiece M₁ M₂ (F.step (Fin.last F.n)) c = _
    rw [F.step_last, filtPiece_top]
  · exact fun p hp => F.ann_le k
      (Module.mem_annihilator.mpr fun y => quotLaurent_smul_eq_zero M₁ M₂ hp y)
  · exact fun f e hf he => F.ann_le k
      (Module.mem_annihilator.mpr fun y => quotLaurent_smul_eq_zero_of M₁ M₂ he (hJ f e hf he) y)
  · change ((g k : M₁.piece (F.deg k)) : E) ∈ filtPiece M₁ M₂ (F.step k.succ) (F.deg k)
    rw [coe_mem_filtPiece, hg k, F.step_succ]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · intro c
    change filtPiece M₁ M₂ (F.step k.succ) c = filtPiece M₁ M₂ (F.step k.castSucc) c ⊔ _
    rw [F.step_succ, ← hg k, filtPiece_sup (hstab k.castSucc) (g k) c]
  · intro f d hf
    rw [F.mem_prime, ← hg k, smul_quotIota M₁ M₂ hf]
    exact (coe_mem_filtPiece _).symm

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleProductPos
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u w

theorem VeryAmpleProductPos.proof (hR : GenericPointSectionInput.Statement.{u, w}) (hP : PointDegreePos.Statement.{u, w})
    (hC : CutComponent.Statement.{u, w}) (hM : CutMultPos.Statement.{u}) :
    VeryAmpleProductPos.Statement.{u, w} := by
  intro k _ Ω _ _ N x e
  induction e with
  | zero =>
    intro pp L hW _
    have h0 : (fun i => (L i).toSubSystem) = (![] : Fin 0 → SubSystem k x Ω) :=
      funext fun i => i.elim0
    rw [h0, (hR k Ω N x).2.2.2.2 pp hW]
    exact_mod_cast hP k Ω N x pp hW
  | succ n ih =>
    intro pp L hW hL
    obtain ⟨s, hs, hsI⟩ := exists_sec_not_mem (L (Fin.last n)) (hL _) hW
    have hsplit : (fun i => (L i).toSubSystem) = Fin.snoc (α := fun _ => SubSystem k x Ω)
        (fun i : Fin n => (L (Fin.castSucc i)).toSubSystem) (L (Fin.last n)).toSubSystem :=
      (Fin.snoc_init_self _).symm
    rw [hsplit, (hR k Ω N x).2.2.2.1 n pp (fun i => L (Fin.castSucc i)) (L (Fin.last n)) s hW hs hsI]
    obtain ⟨q₀, hq₀, hq₀W⟩ := hC k Ω N x n pp (L (Fin.last n)) s hW (hL _) hs hsI

    have hterm : ∀ qq (h : qq ∈ (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s).minimalPrimes),
        IsSubvar x qq n → haveI : qq.IsPrime := h.1.1
        0 < (((cutMult (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s) qq).toNat : ℤ) *
          interNum qq (fun i => (L (Fin.castSucc i)).toSubSystem)) := by
      intro qq h hqW
      have hm := hM k N _ qq h
      exact mul_pos (by exact_mod_cast ENat.toNat_pos hm.1.ne' hm.2.ne) (ih qq _ hqW fun i => hL _)
    refine lt_of_lt_of_le ?_ (single_le_finsum q₀ ?_ ?_)
    · rw [dif_pos ⟨hq₀, hq₀W⟩]
      exact hterm q₀ hq₀ hq₀W
    · refine (Ideal.finite_minimalPrimes_of_isNoetherianRing _
        (pp ⊔ zeroIdeal (L (Fin.last n)).toSubSystem s)).subset fun qq hqq => ?_
      by_contra hn
      exact hqq (dif_neg fun h => hn h.1)
    · intro qq
      split_ifs with h
      · exact (hterm qq h.1 h.2).le
      · exact le_rfl

end

end GroundTheory.Heights₂.Heights.Kleiman
end

