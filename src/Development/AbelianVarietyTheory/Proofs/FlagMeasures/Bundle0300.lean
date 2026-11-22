import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0279
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0075
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0125
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0209
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0280

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRealPointsBijectiveMultiplicative
section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf Formalism.L2.SG.PoincareInHH.PoincareSetting GlobalTheory.CovDom
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CovDom.RealPts

theorem jm_mul_self {n : ℕ} (ε : Fin n → Bool) : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  split_ifs <;> norm_num

def mkUJc {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) : Formalism.REAL.UJ ε :=
  ⟨⟨A, Formalism.REAL.Jm ε * Aᴴ * Formalism.REAL.Jm ε,
    by
      rw [mul_eq_one_comm]
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, h, jm_mul_self],
    by rw [Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Aᴴ, h, jm_mul_self]⟩, h⟩

theorem uMat_mkUJc {n : ℕ} (ε : Fin n → Bool) (A : Matrix (Fin n) (Fin n) ℂ)
    (h : Aᴴ * Formalism.REAL.Jm ε * A = Formalism.REAL.Jm ε) : Formalism.MainNotions.S.uMat (mkUJc ε A h) = A := rfl

theorem hpk_star (k r : ℕ) : (Formalism.QuantumDeterminants.Hpk k r).map star = Formalism.QuantumDeterminants.Hpk k r := by
  ext i j
  simp only [Matrix.map_apply]
  unfold Formalism.QuantumDeterminants.Hpk
  split_ifs <;> simp

theorem tauOf_spec (D : D7) (w : InfinitePlace D.host.E) : InfinitePlace.mk (embS D (tauOf D w)) = w := by
  unfold tauOf
  exact (GlobalTheory.RealPlaces.existsUnique_place D w).exists.choose_spec

theorem tauOf_mk (D : D7) (τ : D.what₂.Tau) : tauOf D (InfinitePlace.mk (embS D τ)) = τ :=
  (GlobalTheory.RealPlaces.existsUnique_place D _).unique (tauOf_spec D _) rfl

theorem cjw_cjw (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    cjw D w (cjw D w M) = M := by
  unfold cjw
  split_ifs with h
  · rfl
  · funext i j
    simp

theorem cjw_injective (D : D7) (w : InfinitePlace D.host.E) : Function.Injective (cjw D w) := by
  intro M N hMN
  rw [← cjw_cjw D w M, hMN, cjw_cjw]

theorem of_cjw_mul (D : D7) (w : InfinitePlace D.host.E) (A B : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) :
    Matrix.of (cjw D w (Matrix.of.symm (Matrix.of A * Matrix.of B))) =
      Matrix.of (cjw D w A) * Matrix.of (cjw D w B) := by
  unfold cjw
  split_ifs with h
  · simp
  · ext i j
    simp [Matrix.mul_apply, star_sum]

private theorem hpk_apply_of_outer_index (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    star (Formalism.QuantumDeterminants.Hpk k r i j) = Formalism.QuantumDeterminants.Hpk k r i j := by
  have e := congrFun (congrFun (hpk_star k r) i) j
  simpa only [Matrix.map_apply] using e

theorem cjw_mem (D : D7) (w : InfinitePlace D.host.E) (M : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)
    (hM : Matrix.of M ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS)) :
    Matrix.of (cjw D w M) ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) := by
  unfold cjw
  split_ifs with h
  · exact hM
  · simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq] at hM ⊢
    have e : (Matrix.of fun i j => star (M i j))ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Matrix.of fun i j => star (M i j))
        = ((Matrix.of M)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * Matrix.of M).map star := by
      ext i j
      simp only [Matrix.map_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply, star_sum,
        star_mul', star_star, hpk_apply_of_outer_index]
    rw [e, hM, hpk_star]

end GlobalTheory.CovDom.RealPts

namespace GlobalTheory.CovDom.RealPts

theorem trX_of {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (g : X.B.I.Ginf) (τ : D.what₂.Tau) :
    Matrix.of (trX X C g τ) = C.Qi τ * Formalism.MainNotions.S.uMat (g (vOf X τ)) * C.Q τ := rfl

private theorem of_trX_mul_eq_mul {D : D7} (X : HidaSetting D) {θ : ℝ} (C : Choice X θ) (s g : X.B.I.Ginf)
    (τ : D.what₂.Tau) :
    Matrix.of (trX X C (s * g) τ) = Matrix.of (trX X C s τ) * Matrix.of (trX X C g τ) := by
  have hQ : C.Q τ * C.Qi τ = 1 := (C.isT τ).2.1
  rw [trX_of, trX_of, trX_of]
  simp only [Pi.mul_apply, Formalism.MainNotions.S.uMat, Subgroup.coe_mul, Units.val_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), hQ, Matrix.one_mul]

private theorem eq_of_mul_mul_eq_of_det_ne_zero {n m : ℕ} (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (hQ : Q * Qi = 1) (A : Matrix (Fin n) (Fin n) ℂ) : Q * (Qi * A * Q) * Qi = A := by
  simp only [← Matrix.mul_assoc, hQ, Matrix.one_mul]
  rw [Matrix.mul_assoc, hQ, Matrix.mul_one]

private theorem hcompl_unit_property_of_isPrime {n m : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (H N : Matrix (Fin m) (Fin m) ℂ)
    (Q : Matrix (Fin n) (Fin m) ℂ) (Qi : Matrix (Fin m) (Fin n) ℂ)
    (hQ : Q * Qi = 1) (hJ : Qᴴ * J * Q = H) (hN : Nᴴ * H * N = H) :
    (Q * N * Qi)ᴴ * J * (Q * N * Qi) = J := by
  have e : (Q * N * Qi)ᴴ * J * (Q * N * Qi) = Qiᴴ * (Nᴴ * (Qᴴ * J * Q) * N) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e' : (Q * Qi)ᴴ * J * (Q * Qi) = Qiᴴ * (Qᴴ * J * Q) * Qi := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [e, hJ, hN, ← hJ, ← e', hQ]
  simp

end GlobalTheory.CovDom.RealPts

namespace GlobalTheory.CovDom

open GlobalTheory.CovDom.RealPts

theorem transport_real_points : ∀ (D : D7) (X : HidaSetting D) (θ : ℝ) (C : Choice X θ),
    (∀ x : InfinitePlace D.host.E → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS, (∀ w, Matrix.of (x w) ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS) →
      ∃ g : X.B.I.Ginf, Gm D (trX X C g) = x) ∧
    Function.Injective (fun g : X.B.I.Ginf => Gm D (trX X C g)) ∧
    ∀ (s g : X.B.I.Ginf) (w : InfinitePlace D.host.E),
      Matrix.of (Gm D (trX X C (s * g)) w) = Matrix.of (Gm D (trX X C s) w) * Matrix.of (Gm D (trX X C g) w) := by
  intro D X θ C
  refine ⟨?_, ?_, ?_⟩
  ·
    intro x hx
    have hM : ∀ τ, Matrix.of (cjw D (InfinitePlace.mk (embS D τ)) (x (InfinitePlace.mk (embS D τ)))) ∈
        Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS) :=
      fun τ => cjw_mem D _ _ (hx _).1
    have hU : ∀ v, (C.Q (X.pl v) * Matrix.of (cjw D (InfinitePlace.mk (embS D (X.pl v)))
          (x (InfinitePlace.mk (embS D (X.pl v))))) * C.Qi (X.pl v))ᴴ * Formalism.REAL.Jm (X.B.I.ε v) *
        (C.Q (X.pl v) * Matrix.of (cjw D (InfinitePlace.mk (embS D (X.pl v)))
          (x (InfinitePlace.mk (embS D (X.pl v))))) * C.Qi (X.pl v)) = Formalism.REAL.Jm (X.B.I.ε v) := by
      intro v
      have hT := C.isT (X.pl v)
      simp only [IsTranspC, vOf, Equiv.symm_apply_apply] at hT
      exact hcompl_unit_property_of_isPrime _ _ _ _ _ hT.2.1 hT.2.2.1 (hM _)
    refine ⟨fun v => mkUJc (X.B.I.ε v) _ (hU v), ?_⟩
    have key : ∀ τ, trX X C (fun v => mkUJc (X.B.I.ε v) _ (hU v)) τ =
        cjw D (InfinitePlace.mk (embS D τ)) (x (InfinitePlace.mk (embS D τ))) := by
      intro τ
      apply Matrix.of.injective
      have hQi : C.Qi τ * C.Q τ = 1 := (C.isT τ).1
      simp only [trX_of, uMat_mkUJc, vOf, Equiv.apply_symm_apply]
      exact eq_of_mul_mul_eq_of_det_ne_zero (C.Qi τ) (C.Q τ) hQi _
    funext w
    simp only [Gm, key, tauOf_spec, cjw_cjw]
  ·
    intro s g hsg
    funext v
    obtain ⟨τ, rfl⟩ : ∃ τ, vOf X τ = v := ⟨X.pl v, X.pl.symm_apply_apply v⟩
    have hw := congrFun hsg (InfinitePlace.mk (embS D τ))
    simp only [Gm, tauOf_mk] at hw
    have h2 := congrArg Matrix.of (cjw_injective D _ hw)
    rw [trX_of, trX_of] at h2
    have h3 := congrArg (fun N => C.Q τ * N * C.Qi τ) h2
    simp only [eq_of_mul_mul_eq_of_det_ne_zero (C.Q τ) (C.Qi τ) (C.isT τ).2.1] at h3
    exact Subtype.ext (Units.ext h3)
  ·
    intro s g w
    simp only [Gm]
    rw [← of_cjw_mul, ← of_trX_mul_eq_mul, Equiv.symm_apply_apply]

end GlobalTheory.CovDom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TrivialOnDualQuotientIffMemLocalUnitary
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.FunFix

section Abstract

variable {A : Type} [CommRing A] {k : ℕ} (τ : A →+* A) (J : Matrix (Fin k) (Fin k) A)

theorem hform_sub_left (x x' y : Fin k → A) : hform τ J (x - x') y = hform τ J x y - hform τ J x' y := by
  simp only [hform, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]

theorem hform_sub_right (x y y' : Fin k → A) : hform τ J x (y - y') = hform τ J x y - hform τ J x y' := by
  simp only [hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hform_smul_swap (c : A) (x y : Fin k → A) : hform τ J x (τ c • y) = hform τ J (c • x) y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_unitary {g : GL (Fin k) A} (hg : g ∈ UJ τ J) (x y : Fin k → A) :
    hform τ J (g.1 *ᵥ x) (g.1 *ᵥ y) = hform τ J x y := by
  have h : cT τ g.1 * J * g.1 = J := hg
  rw [GlobalTheory.DualFrame.hform_mulVec, mulVec_mulVec, h, GlobalTheory.DualFrame.hform_eq_dot]

theorem hform_move {g : GL (Fin k) A} (hg : g ∈ UJ τ J) (x y : Fin k → A) :
    hform τ J x (g.1 *ᵥ y) = hform τ J ((g⁻¹).1 *ᵥ x) y := by
  rw [← hform_unitary τ J hg ((g⁻¹).1 *ᵥ x) y, mulVec_mulVec, Units.mul_inv, one_mulVec]

variable {τ J} {O : Subring A} {L D : Submodule O (Fin k → A)}

theorem stab_dual (hD : ∀ y, y ∈ D ↔ ∀ x ∈ L, hform τ J x y ∈ O) {g : GL (Fin k) A}
    (hg : g ∈ level τ J L) : g ∈ stabGL D := by
  obtain ⟨hu, hs⟩ := hg
  intro y
  rw [hD, hD]
  constructor
  · intro h x hx
    rw [hform_move τ J hu]
    exact h _ (((stabGL L).inv_mem hs x).1 hx)
  · intro h x hx
    rw [← hform_unitary τ J hu]
    exact h _ ((hs x).1 hx)

theorem triv_iff_stabFun (hD : ∀ y, y ∈ D ↔ ∀ x ∈ L, hform τ J x y ∈ O)
    (hL : ∀ y, y ∈ L ↔ ∀ x ∈ D, hform τ J x y ∈ O)
    {M : Type} [AddCommGroup M] [Module O M] (f : D →ₗ[O] M) (hf0 : f ≠ 0)
    (hfL : ∀ x : D, x.1 ∈ L → f x = 0) (e : O) (hτe : τ e = 1 - e) (hact : ∀ m : M, e • m = m)
    (hfield : ∀ a : O, (∃ b : O, b * a * e = e) ∨ ∀ x ∈ D, (e * a) • x ∈ L)
    (d : Fin k → A) (hd : d ∈ D) (hgen : ∀ x ∈ D, ∃ a ∈ O, x - a • d ∈ L)
    {g : GL (Fin k) A} (hg : g ∈ level τ J L) :
    (∀ x ∈ D, (g.1 - 1) *ᵥ x ∈ L) ↔ g ∈ stabFun D f := by
  have hgD := stab_dual hD hg
  have hval : ∀ (x : D) (a : O), x.1 - a.1 • d ∈ L → f x = a • f ⟨d, hd⟩ := by
    intro x a h
    rw [← map_smul, ← sub_eq_zero, ← map_sub]
    exact hfL _ h
  have hfd : f ⟨d, hd⟩ ≠ 0 := by
    intro h
    apply hf0
    ext x
    obtain ⟨a, ha, hx⟩ := hgen x.1 x.2
    rw [hval x ⟨a, ha⟩ hx, h, smul_zero]
    rfl
  have hker : ∀ x : D, f x = 0 → e • x.1 ∈ L := by
    intro x hx0
    obtain ⟨a, ha, hx⟩ := hgen x.1 x.2
    rcases hfield ⟨a, ha⟩ with ⟨b, hb⟩ | h
    · exfalso
      apply hfd
      rw [← hact (f ⟨d, hd⟩), ← hb, mul_smul, hact, mul_smul, ← hval x ⟨a, ha⟩ hx, hx0, smul_zero]
    · have h1 := L.add_mem (L.smul_mem e hx) (h d hd)
      have h2 : e • (x.1 - a • d) + (e * ⟨a, ha⟩) • d = e • x.1 := by
        rw [smul_sub, mul_smul]
        exact sub_add_cancel _ _
      rwa [h2] at h1
  have hhalf : ∀ g' ∈ stabFun D f, ∀ x ∈ D, e • (g'.1 *ᵥ x - x) ∈ L := by
    rintro g' ⟨h1, h2⟩ x hx
    refine hker (⟨g'.1 *ᵥ x, (h1 x).1 hx⟩ - ⟨x, hx⟩) ?_
    rw [map_sub, sub_eq_zero]
    exact h2 ⟨x, hx⟩
  constructor
  · intro h
    refine ⟨hgD, fun x => ?_⟩
    rw [← sub_eq_zero, ← map_sub]
    refine hfL _ ?_
    have := h x.1 x.2
    rwa [sub_mulVec, one_mulVec] at this
  · intro h x hx
    rw [sub_mulVec, one_mulVec]
    have h1 := hhalf g h x hx
    have h2 : τ e • (g.1 *ᵥ x - x) ∈ L := by
      rw [hL]
      intro z hz
      rw [hform_smul_swap, hform_sub_right, hform_move τ J hg.1, ← hform_sub_left, mulVec_smul, ← smul_sub]
      exact (hD x).1 hx _ (hhalf g⁻¹ ((stabFun D f).inv_mem h) z hz)
    have h3 := L.add_mem h1 h2
    have h4 : e • (g.1 *ᵥ x - x) + τ e • (g.1 *ᵥ x - x) = g.1 *ᵥ x - x := by
      rw [hτe, sub_smul, one_smul]
      exact add_sub_cancel _ _
    rwa [h4] at h3

theorem idem_act {R : Type} [Ring R] {G : Type} [AddCommGroup G] [Module R G] {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p) {e : R} (he : e * e = e) : (∀ y : G, e • y = 0) ∨ (∀ y : G, e • y = y) := by
  have : Fact p.Prime := ⟨hp⟩
  have := isSimpleAddGroup_of_prime_card hG
  rcases IsSimpleAddGroup.eq_bot_or_eq_top_of_normal (DistribSMul.toAddMonoidHom G e).range inferInstance
    with h | h
  · left
    intro y
    exact AddSubgroup.mem_bot.1 (h ▸ ⟨y, rfl⟩)
  · right
    intro y
    have hy : y ∈ (DistribSMul.toAddMonoidHom G e).range := by rw [h]; exact AddSubgroup.mem_top y
    obtain ⟨z, hz⟩ := AddMonoidHom.mem_range.1 hy
    rw [← hz]
    show e • e • z = e • z
    rw [smul_smul, he]

theorem unit_or_dvd {K : Type} [Field K] (V : ValuationSubring K) (T : ℕ)
    (hmax : IsLocalRing.maximalIdeal V = Ideal.span {(T : V)}) (sp : A ≃+* K × K)
    (hint : ∀ x, x ∈ O ↔ (sp x).1 ∈ V ∧ (sp x).2 ∈ V) (e : O) (he : sp e = (1, 0)) (a : O) :
    (∃ b : O, b * a * e = e) ∨ ∃ c : O, e * a = c * T := by
  have ha := ((hint a).1 a.2).1
  have hm : ∀ c : V, sp.symm (c, 0) ∈ O := fun c => by
    rw [hint, sp.apply_symm_apply]; exact ⟨c.2, zero_mem _⟩
  by_cases hu : IsUnit (⟨_, ha⟩ : V)
  · obtain ⟨b, hb⟩ := hu.exists_left_inv
    have hb' : (b : K) * (sp a).1 = 1 := congrArg Subtype.val hb
    refine Or.inl ⟨⟨_, hm b⟩, Subtype.ext (sp.injective ?_)⟩
    change sp (sp.symm (b, 0) * a * e) = sp e
    rw [map_mul, map_mul, sp.apply_symm_apply, he]
    ext <;> simp [hb']
  · have h1 : (⟨_, ha⟩ : V) ∈ IsLocalRing.maximalIdeal V := hu
    rw [hmax, Ideal.mem_span_singleton'] at h1
    obtain ⟨c, hc⟩ := h1
    have hc' : (c : K) * T = (sp a).1 := by simpa using congrArg Subtype.val hc
    refine Or.inr ⟨⟨_, hm c⟩, Subtype.ext (sp.injective ?_)⟩
    rw [Subring.coe_mul, Subring.coe_mul, Subring.coe_natCast, map_mul, map_mul, sp.apply_symm_apply, he, map_natCast]
    ext <;> simp [hc']

end Abstract

section Local

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem sigR_mem (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) :
    ∀ a ∈ intV E v, sigR σ (v.adicCompletion F) a ∈ intV E v := by
  have : intV E v ≤ (intV E v).comap (sigR σ (v.adicCompletion F)) := by
    refine Subring.closure_le.2 ?_
    rintro _ (⟨⟨_, a, rfl⟩, rfl⟩ | ⟨a, rfl⟩)
    · exact Subring.subset_closure (Or.inl ⟨⟨_, (⟨σ a, (a.isIntegral_coe).map (σ.restrictScalars ℤ)⟩ : 𝓞 E), rfl⟩, rfl⟩)
    · show (σ 1) ⊗ₜ[F] (a : v.adicCompletion F) ∈ intV E v
      rw [map_one]
      exact Subring.subset_closure (Or.inr ⟨a, rfl⟩)
  exact this

theorem nsmul_mem_loc (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L L' : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ x ∈ L', (T : E) • x ∈ L) : ∀ x ∈ loc v L', (T : intV E v) • x ∈ loc v L := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨_, h y hy, ?_⟩
    funext i
    simp only [Nat.cast_smul_eq_nsmul, Pi.smul_apply, map_nsmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
  | smul a b _ hb => rw [smul_comm]; exact Submodule.smul_mem _ _ hb

end Local

theorem trivial_iff_mem_Uloc : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) (S : StepLevel F E cm.sig J T f bad), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → ∀ (v : HeightOneSpectrum (𝓞 F)), (T : 𝓞 F) ∈ v.asIdeal → ∀ y ∈ levelVL cm.sig J v S.Lb, (∀ x ∈ loc v (dualL cm.sig J S.Lb), (y.1 - 1) *ᵥ x ∈ loc v S.Lb) ↔ y ∈ S.Uloc v := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f bad S hT hsp hdeg v hv y hy
  obtain ⟨-, d, hd, hgen⟩ := GlobalTheory.T.hermitianLattice_level_local_dual_quotient_length_one F E cm n J hJ hdet T f S.Lb hT hsp hdeg
    (stepLevel_tLat F E n cm.sig J T f bad S) v hv
  obtain ⟨-, hmax, sp, hsig, hdiag⟩ := (GlobalTheory.T.cmField_splitCompletely_place_structure F E cm T hT hsp).2 v hv
  have hint : ∀ x, x ∈ intV E v ↔
      (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F :=
    split_integral_local F E v sp hdiag
  obtain ⟨B, C, hBC, hB, hC⟩ := GlobalTheory.DualFrame.exists_dual_frames F E cm.sig n J (isUnit_iff_ne_zero.2 hdet) S.Lb
    S.Lb_fin S.Lb_span v
  obtain ⟨hD, hL, -⟩ := GlobalTheory.DualFrames.dual_of_dual_frames _ (intV E v) (sigR cm.sig (v.adicCompletion F))
    (fun a => sp.injective (by rw [hsig, hsig]; rfl)) (sigR_mem _ v) n _
    (by ext i j; exact congrArg (inclE (F := F) (v.adicCompletion F)) (congrFun (congrFun hJ i) j))
    B C _ _ hBC hB hC
  have hTD := nsmul_mem_loc v T S.Lb (dualL cm.sig J S.Lb)
    fun x hx => S.Lb_dual x (GlobalTheory.DualFrame.mem_dualSet_of_mem_span _ _ _ hx)
  have key : ∀ (sp' : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F),
      (∀ x, x ∈ intV E v ↔
        (sp' x).1 ∈ v.adicCompletionIntegers F ∧ (sp' x).2 ∈ v.adicCompletionIntegers F) →
      ∀ e : intV E v, sp' e = (1, 0) → sigR cm.sig (v.adicCompletion F) e = 1 - e →
      (∀ m : S.fM v hv, e • m = m) →
      ((∀ x ∈ loc v (dualL cm.sig J S.Lb), (y.1 - 1) *ᵥ x ∈ loc v S.Lb) ↔ y ∈ stabFun _ (S.fT v hv)) := by
    intro sp' hint' e he hτe hact
    refine triv_iff_stabFun hD hL (S.fT v hv) (S.fT_ne v hv) (S.fT_L v hv) e hτe hact (fun a => ?_) d hd hgen hy
    refine (unit_or_dvd _ T hmax sp' hint' e he a).imp id ?_
    rintro ⟨c, hc⟩ x hx
    rw [hc, mul_smul]
    exact Submodule.smul_mem _ _ (hTD x hx)
  have he : sp.symm (1, 0) ∈ intV E v := by
    rw [hint, sp.apply_symm_apply]; exact ⟨one_mem _, zero_mem _⟩
  have hτ : sigR cm.sig (v.adicCompletion F) (sp.symm (1, 0)) = 1 - sp.symm (1, 0) := by
    apply sp.injective
    rw [hsig, map_sub, map_one, sp.apply_symm_apply]
    ext <;> simp [swapR]
  have hee : (⟨_, he⟩ : intV E v) * ⟨_, he⟩ = ⟨_, he⟩ := by
    apply Subtype.ext
    change sp.symm (1, 0) * sp.symm (1, 0) = sp.symm (1, 0)
    rw [← map_mul]
    simp
  rw [S.UlocAlt v hv, Subgroup.mem_inf, and_iff_right hy]
  rcases idem_act hT (S.fM_card v hv) hee with h0 | h1
  · refine key (sp.trans RingEquiv.prodComm) (fun x => (hint x).trans and_comm) (1 - ⟨_, he⟩) ?_ ?_ fun m => ?_
    · change RingEquiv.prodComm (sp (1 - sp.symm (1, 0))) = _
      rw [map_sub sp, map_one, sp.apply_symm_apply]
      ext <;> simp
    · change sigR cm.sig (v.adicCompletion F) (1 - sp.symm (1, 0)) = 1 - (1 - sp.symm (1, 0))
      rw [map_sub, map_one, hτ]
    · rw [sub_smul, one_smul, h0, sub_zero]
  · exact key sp hint ⟨_, he⟩ (sp.apply_symm_apply _) hτ h1

end GlobalTheory.St.G.FunFix
end

