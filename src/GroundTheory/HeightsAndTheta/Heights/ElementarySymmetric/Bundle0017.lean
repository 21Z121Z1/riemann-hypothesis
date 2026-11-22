import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.Intersections.PRFormula
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0034
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0051
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0052
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0012
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwinEqCech

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PPluckerRel
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace PluckerRelations

section Homog

variable {K : Type*} [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

theorem homog_add {f g : MRing ι} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

omit [DecidableEq K] in
theorem homog_zero (a : K → ℕ) : IsMultiHomog (0 : MRing ι) a := by
  intro m hm
  simp at hm

theorem homog_C (r : ℤ) (b : K) : IsMultiHomog (C r : MRing ι) (Pi.single b 0) := by
  classical
  intro m hm k
  have hm0 : m = 0 := by
    by_contra h
    exact (mem_support_iff.1 hm) (by rw [coeff_C, if_neg (Ne.symm h)])
  subst hm0
  simp

end Homog

variable {D : ℕ} (S : ProjectiveLineBundle D)

def wedgeVal (k m : S.κ) : S.Ω :=
  S.φ k (S.e 0) * S.φ m (S.e 1) - S.φ k (S.e 1) * S.φ m (S.e 0)

theorem apply_eq (ψ : S.E →ₗ[S.Ω] S.Ω) (u : S.E) :
    ψ u = S.e.repr u 0 * ψ (S.e 0) + S.e.repr u 1 * ψ (S.e 1) := by
  have h := congrArg ψ (S.e.sum_repr u)
  rw [Fin.sum_univ_two, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
  exact h.symm

theorem wedge_mul_detE (k m : S.κ) (u w : S.E) :
    wedgeVal S k m * T.detE S.e u w = S.φ k u * S.φ m w - S.φ k w * S.φ m u := by
  rw [apply_eq S (S.φ k) u, apply_eq S (S.φ m) w, apply_eq S (S.φ k) w, apply_eq S (S.φ m) u]
  simp only [wedgeVal, T.detE]
  ring

theorem wedge_mul_delta (i : S.ι) (hi : S.x i ≠ 0) (l : S.ν) (k m : S.κ) :
    ∃ a ∈ chartRing ℤ S.x i, wedgeVal S k m * S.δ l = S.x i ^ 3 * a := by
  suffices h : ∀ y ∈ Submodule.span (chartRing ℤ S.x i)
      {d | ∃ u ∈ S.B.lat i, ∃ w ∈ S.B.lat i, d = S.x i * T.detE S.e u w},
      ∃ a ∈ chartRing ℤ S.x i, wedgeVal S k m * y = S.x i ^ 3 * a from
    h _ ((S.detGen i hi).1 l)
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, w, hw, rfl⟩ := hy
    obtain ⟨a₁, ha₁, e₁⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi k u hu)
    obtain ⟨a₂, ha₂, e₂⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi m w hw)
    obtain ⟨a₃, ha₃, e₃⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi k w hw)
    obtain ⟨a₄, ha₄, e₄⟩ := (mem_lineLat S.x 1 i _).1 (S.dualSec i hi m u hu)
    refine ⟨a₁ * a₂ - a₃ * a₄, sub_mem (mul_mem ha₁ ha₂) (mul_mem ha₃ ha₄), ?_⟩
    have h := wedge_mul_detE S k m u w
    rw [← e₁, ← e₂, ← e₃, ← e₄] at h
    linear_combination (S.x i) * h
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hya⟩ := hy
    obtain ⟨b, hb, hzb⟩ := hz
    exact ⟨a + b, add_mem ha hb, by rw [mul_add, hya, hzb, mul_add]⟩
  | smul r y _ hy =>
    obtain ⟨a, ha, hya⟩ := hy
    refine ⟨(r : S.Ω) * a, mul_mem r.2 ha, ?_⟩
    rw [Subalgebra.smul_def, smul_eq_mul]
    linear_combination (r : S.Ω) * hya

theorem coord_base (j : S.ι) :
    T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1) ⟨T.WBlk.base, j⟩ = algebraMap S.Ω S.Φ (S.x j) :=
  rfl

theorem rename_X_base (j : S.ι) :
    (rename (T.yyEmb 0) (X ⟨T.YBlk.base, j⟩ : MRing S.YIdx) : MRing S.WIdx) = X ⟨T.WBlk.base, j⟩ :=
  rename_X _ _

theorem chart_form (i : S.ι) (hi : S.x i ≠ 0) {a : S.Ω} (ha : a ∈ chartRing ℤ S.x i) :
    ∃ (d : ℕ) (Q : MRing S.YIdx), IsMultiHomog Q (Pi.single T.YBlk.base d) ∧
      IsMultiHomog (rename (T.yyEmb 0) Q : MRing S.WIdx) (Pi.single T.WBlk.base d) ∧
      aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) Q) =
        algebraMap S.Ω S.Φ (S.x i ^ d * a) := by
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨j, rfl⟩ := hy
    refine ⟨1, X ⟨T.YBlk.base, j⟩, exHomog_X _ _, ?_, ?_⟩
    · rw [rename_X_base]
      exact exHomog_X (ι := S.WIdx) T.WBlk.base j
    · rw [rename_X_base, aeval_X, coord_base]
      congr 1
      field_simp
  | algebraMap r =>
    refine ⟨0, C r, homog_C _ _, ?_, ?_⟩
    · rw [rename_C]
      exact homog_C _ _
    · simp
  | add y z _ _ hy hz =>
    obtain ⟨d₁, Q₁, h₁, h₁', e₁⟩ := hy
    obtain ⟨d₂, Q₂, h₂, h₂', e₂⟩ := hz
    refine ⟨d₁ + d₂, Q₁ * X ⟨T.YBlk.base, i⟩ ^ d₂ + Q₂ * X ⟨T.YBlk.base, i⟩ ^ d₁, ?_, ?_, ?_⟩
    · refine homog_add ?_ ?_
      · convert exHomog_mul h₁ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) d₂) using 1
        funext b; cases b <;> simp
      · convert exHomog_mul h₂ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) d₁) using 1
        funext b; cases b <;> simp [add_comm]
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, rename_X_base]
      refine homog_add ?_ ?_
      · convert exHomog_mul h₁' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) d₂) using 1
        funext b; cases b <;> simp
      · convert exHomog_mul h₂' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) d₁) using 1
        funext b; cases b <;> simp [add_comm]
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, rename_X_base, map_add, map_mul, map_mul, map_pow, map_pow,
        aeval_X, e₁, e₂, coord_base]
      simp only [map_add, map_mul, map_pow]
      ring
  | mul y z _ _ hy hz =>
    obtain ⟨d₁, Q₁, h₁, h₁', e₁⟩ := hy
    obtain ⟨d₂, Q₂, h₂, h₂', e₂⟩ := hz
    refine ⟨d₁ + d₂, Q₁ * Q₂, ?_, ?_, ?_⟩
    · convert exHomog_mul h₁ h₂ using 1
      funext b; cases b <;> simp
    · rw [map_mul]
      convert exHomog_mul h₁' h₂' using 1
      funext b; cases b <;> simp
    · rw [map_mul, map_mul, e₁, e₂]
      simp only [map_mul, map_pow]
      ring

theorem key (i : S.ι) (l : S.ν) (k m : S.κ) :
    ∃ (d : ℕ) (Q : MRing S.YIdx), IsMultiHomog Q (Pi.single T.YBlk.base (d + 4)) ∧
      IsMultiHomog (rename (T.yyEmb 0) Q : MRing S.WIdx) (Pi.single T.WBlk.base (d + 4)) ∧
      aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) Q) =
        algebraMap S.Ω S.Φ (S.x i ^ (d + 1) * (wedgeVal S k m * S.δ l)) := by
  by_cases hi : S.x i = 0
  · refine ⟨0, 0, homog_zero _, homog_zero _, ?_⟩
    simp [hi]
  · obtain ⟨a, ha, hpa⟩ := wedge_mul_delta S i hi l k m
    obtain ⟨d, Q, hQ, hQ', hv⟩ := chart_form S i hi ha
    refine ⟨d, Q * X ⟨T.YBlk.base, i⟩ ^ 4, ?_, ?_, ?_⟩
    · convert exHomog_mul hQ (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) 4) using 1
      funext b; cases b <;> simp
    · rw [map_mul, map_pow, rename_X_base]
      convert exHomog_mul hQ' (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) 4) using 1
      funext b; cases b <;> simp
    · rw [map_mul, map_pow, rename_X_base, map_mul, map_pow, aeval_X, hv, coord_base, hpa]
      simp only [map_mul, map_pow]
      ring

end PluckerRelations

open PluckerRelations in

theorem PluckerRel.proof : PluckerRel.Statement := by
  intro D S
  classical
  choose d Q hQ hQ' hv using PluckerRelations.key S
  set N : ℕ := (Finset.univ.sup fun t : S.ι × S.ν × S.κ × S.κ => d t.1 t.2.1 t.2.2.1 t.2.2.2) + 1 with hN
  have hle : ∀ i l k m, d i l k m + 1 ≤ N := fun i l k m => by
    have := Finset.le_sup (f := fun t : S.ι × S.ν × S.κ × S.κ => d t.1 t.2.1 t.2.2.1 t.2.2.2)
      (Finset.mem_univ (i, l, k, m))
    simp only at this
    omega
  refine ⟨N, fun i l k m => Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1)), fun i l k m => ?_,
    fun i l k m => ?_⟩
  · have h := hle i l k m
    convert exHomog_mul (hQ i l k m) (exHomog_pow (exHomog_X (ι := S.YIdx) T.YBlk.base i) (N - (d i l k m + 1)))
      using 1
    funext b; cases b <;> simp; omega
  · have h := hle i l k m
    have hRF : IsMultiHomog (rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1))) :
        MRing S.WIdx) (Pi.single T.WBlk.base (N + 3)) := by
      rw [map_mul, map_pow, rename_X_base]
      convert exHomog_mul (hQ' i l k m) (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i)
        (N - (d i l k m + 1))) using 1
      funext b; cases b <;> simp; omega
    have hpl : IsMultiHomog (S.pluckerWW k m) (Pi.single T.WBlk.line0 1 + Pi.single T.WBlk.line1 1) :=
      exHomog_sub (exHomog_mul (exHomog_X (ι := S.WIdx) T.WBlk.line0 k) (exHomog_X (ι := S.WIdx) T.WBlk.line1 m))
        (exHomog_mul (exHomog_X (ι := S.WIdx) T.WBlk.line0 m) (exHomog_X (ι := S.WIdx) T.WBlk.line1 k))
    have hP : IsMultiHomog (S.g * rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1))) -
        S.h * S.pluckerWW k m * X ⟨.det, l⟩ * X ⟨.base, i⟩ ^ N)
        (T.wwDeg S.n 1 + Pi.single T.WBlk.base (N + 3)) := by
      refine exHomog_sub (exHomog_mul S.g_deg hRF) ?_
      convert exHomog_mul (exHomog_mul (exHomog_mul S.h_deg hpl) (exHomog_X (ι := S.WIdx) T.WBlk.det l))
        (exHomog_pow (exHomog_X (ι := S.WIdx) T.WBlk.base i) N) using 1
      funext b; cases b <;> simp [T.wwDeg] <;> omega
    have hF : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1)))) =
        algebraMap S.Ω S.Φ (S.x i ^ N * (wedgeVal S k m * S.δ l)) := by
      rw [map_mul, map_pow, rename_X_base, map_mul, map_pow, aeval_X, hv, coord_base, ← map_pow, ← map_mul]
      congr 1
      conv_rhs => rw [← Nat.sub_add_cancel h, pow_add]
      ring
    have hpv : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (S.pluckerWW k m) = (S.a 1 - S.a 0) * algebraMap S.Ω S.Φ (wedgeVal S k m) := by
      simp only [ProjectiveLineBundle.pluckerWW, map_sub, map_mul, aeval_X, T.wwCoord, T.lineVal, wedgeVal]
      ring
    show _ ∈ RingHom.ker (T.multiConeMap (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)))
    rw [RingHom.mem_ker, DiagRAux.multiConeMap_of_homog _ _ _ hP]
    suffices h0 : aeval (T.wwCoord S.x S.δ S.e S.φ (S.a 0) (S.a 1)) (S.g * rename (T.yyEmb 0) (Q i l k m * X ⟨T.YBlk.base, i⟩ ^ (N - (d i l k m + 1))) -
        S.h * S.pluckerWW k m * X ⟨.det, l⟩ * X ⟨.base, i⟩ ^ N) = 0 by
      rw [h0, C_0, zero_mul]
    rw [map_sub, map_mul (aeval _) S.g, hF]
    simp only [map_mul, map_pow, aeval_X, hpv, S.quot]
    simp only [T.wwCoord, T.diagSec]
    ring

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrLenEuler
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace RestrLenEuler

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}

theorem length_toNat_eq_finrank (M : Type w) [AddCommGroup M] [Module k M] :
    (Module.length k M).toNat = Module.finrank k M := by
  by_cases h : Module.Finite k M
  · rw [Module.length_eq_finrank]; rfl
  · rw [Module.finrank_of_not_finite h, Module.length_eq_rank]
    have : Cardinal.aleph0 ≤ Module.rank k M := by
      by_contra hlt
      exact h (Module.rank_lt_aleph0_iff.mp (not_le.mp hlt))
    rw [Cardinal.toENat_eq_top.mpr this]
    rfl

theorem vanish_of_fg (F : SubFamily k x Ω) (hF : ∀ I, (F.sub I).FG) :
    ∃ c₀ : ℤ, ∀ i : ℕ, 1 ≤ i → ∀ c : ℤ, c₀ ≤ c → Subsingleton ((F.toSubSystem.twist (twistSys k x c)).H i) := by
  obtain ⟨M, -, hM⟩ := Extension.full k Ω N x Ω F hF
  obtain ⟨c₀, hc₀⟩ := TildeVanish.proof SerreVanish.full k Ω N x Ω M
  have h0 : M.tildeSys 0 = F.toSubSystem := SubSystem.ext_sub fun I => hM I
  refine ⟨c₀, fun i hi c hc => ?_⟩
  rw [← h0, ← SurjectiveClosed.tildeSys_eq_twist]
  exact hc₀ i hi c hc

def incl (F₁ F₂ : SubSystem k x Ω) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (I : Chart x) :
    F₂.sub I →ₗ[k] F₁.sub I where
  toFun y := ⟨y, h21 I y.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option maxHeartbeats 1000000 in

theorem quotH_subsingleton (F₁ F₂ : SubSystem k x Ω) (h21 : ∀ I, F₂.sub I ≤ F₁.sub I) (i : ℕ)
    (h1 : Subsingleton (F₁.H i)) (h2 : Subsingleton (F₂.H (i + 1))) :
    Subsingleton (SubSystem.quotH F₁ F₂ i) := by
  have hdd := CechDSq.full (N + 1) (support x) k (fun I : Chart x => F₁.sub I) F₁.res
    (fun _ _ _ _ _ => LinearMap.ext fun _ => rfl)
  have L := Cech.longExact (R := k) (U := support x)
    (A := fun I : Chart x => F₂.sub I) (B := fun I : Chart x => F₁.sub I)
    (C := fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
    (ρA := F₂.res) (ρB := F₁.res) (ρC := SubSystem.quotRes F₁ F₂)
    (dA := fun _ => ⊤) (dB := fun _ => ⊤) (dC := fun _ => ⊤)
    (φ := incl F₁ F₂ h21) (ψ := fun I => (SubSystem.quotSub F₁ F₂ I).mkQ)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) (fun _ _ _ => Submodule.mem_top)
    (fun _ _ _ => Submodule.mem_top)
    (fun I a b hab => Subtype.ext (show (a : Ω) = b from congrArg (fun z : F₁.sub I => (z : Ω)) hab))
    (fun I y => (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mpr y.2)
    (fun I m _ hm => ⟨⟨m, (Submodule.Quotient.mk_eq_zero (SubSystem.quotSub F₁ F₂ I)).mp hm⟩, Submodule.mem_top, rfl⟩)
    (fun I z _ => (Submodule.Quotient.mk_surjective _ z).imp fun y hy => ⟨Submodule.mem_top, hy⟩)
    (fun _ _ _ _ _ => Submodule.mem_top) hdd
  obtain ⟨-, hex⟩ := L
  obtain ⟨hg, δ, hgδ, -⟩ := hex i
  have hB : Subsingleton (Cech.Hdeg (fun I : Chart x => F₁.sub I) (fun _ => (⊤ : Submodule k _)) F₁.res i) :=
    haveI : Subsingleton (Cech.H (fun I : Chart x => F₁.sub I) F₁.res i) := h1
    (SnapperQuotientAdditivity.hdegTopEquiv _ _ i).toEquiv.subsingleton
  have hA : Subsingleton (Cech.Hdeg (fun I : Chart x => F₂.sub I) (fun _ => (⊤ : Submodule k _)) F₂.res (i + 1)) :=
    haveI : Subsingleton (Cech.H (fun I : Chart x => F₂.sub I) F₂.res (i + 1)) := h2
    (SnapperQuotientAdditivity.hdegTopEquiv _ _ (i + 1)).toEquiv.subsingleton
  have hC : Subsingleton (Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
      (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₁ F₂) i) := by
    refine ⟨fun a b => ?_⟩
    have hz : ∀ y : Cech.Hdeg (fun I : Chart x => F₁.sub I ⧸ SubSystem.quotSub F₁ F₂ I)
        (fun _ => (⊤ : Submodule k _)) (SubSystem.quotRes F₁ F₂) i, y = 0 := by
      intro y
      obtain ⟨b, hb⟩ := (hgδ y).mp (Subsingleton.elim _ _)
      rw [← hb, Subsingleton.elim b 0, map_zero]
    rw [hz a, hz b]
  exact (SnapperQuotientAdditivity.hdegTopEquiv _ _ i).symm.toEquiv.subsingleton

end RestrLenEuler

open RestrLenEuler in

theorem RestrLenEuler.proof : RestrLenEuler.Statement.{u, w} := by
  intro k _ Ω _ _ N x qq hqq _ t L n
  set Ls : Fin t → SubSystem k x Ω := fun j => (L j).toSubSystem with hLs
  let Q : LineBundle k x := twistPowsBundle (twistBundle k x 0) t L n
  have hQ : Q.toSubSystem = (twistSys k x 0).twistPows t Ls n :=
    twistPowsBundle_toSubSystem (twistBundle k x 0) t L n
  obtain ⟨G, hG, hGfg⟩ := IdealTwistFamily.proof k Ω N x Q qq hqq
  obtain ⟨a₁, ha₁⟩ := vanish_of_fg Q.toSubFamily Q.fg
  obtain ⟨a₂, ha₂⟩ := vanish_of_fg G hGfg
  obtain ⟨a₃, ha₃⟩ := SurjectiveClosed.proof Extension.full IdealTwistFamily.proof
    (TildeVanish.proof SerreVanish.full) k Ω N x Q qq hqq
  refine Filter.eventually_atTop.mpr ⟨max a₁ (max a₂ a₃), fun c hc => ?_⟩
  have hc₁ : a₁ ≤ c := le_of_max_le_left hc
  have hc₂ : a₂ ≤ c := le_of_max_le_left (le_of_max_le_right hc)
  have hc₃ : a₃ ≤ c := le_of_max_le_right (le_of_max_le_right hc)
  set F₁ := ((twistSys k x 0).twistPows t Ls n).twist (twistSys k x c) with hF₁
  have hF₁Q : F₁ = Q.toSubSystem.twist (twistSys k x c) := by rw [hQ]
  have hF₂ : (((twistSys k x 0).twist (idealSys x qq)).twistPows t Ls n).twist (twistSys k x c) =
      F₁.twist (idealSys x qq) := by
    rw [twistPows_twist_comm, SurjectiveClosed.twist_twist_comm]
  have hF₂G : F₁.twist (idealSys x qq) = G.toSubSystem.twist (twistSys k x c) := by
    rw [hG, hF₁Q, SurjectiveClosed.twist_twist_comm]
  have h21 : ∀ I, (F₁.twist (idealSys x qq)).sub I ≤ F₁.sub I :=
    SurjectiveClosed.twist_idealSys_le F₁ qq
  have hvan : ∀ i, 1 ≤ i → Subsingleton (SubSystem.quotH F₁ (F₁.twist (idealSys x qq)) i) := by
    intro i hi
    refine quotH_subsingleton F₁ _ h21 i ?_ ?_
    · rw [hF₁Q]; exact ha₁ i hi c hc₁
    · rw [hF₂G]; exact ha₂ (i + 1) (by omega) c hc₂
  have hlift := ha₃ c hc₃
  rw [← hF₁Q] at hlift
  unfold pieceChar restrLen
  rw [hF₂, QuotientH0Length.length_secs_eq _ _ hlift, length_toNat_eq_finrank, eulerCharQuot,
    Finset.sum_eq_single 0]
  · simp only [pow_zero, one_mul]; rfl
  · intro i _ hi
    have := hvan i (Nat.one_le_iff_ne_zero.mpr hi)
    rw [Module.finrank_zero_of_subsingleton]
    simp
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.succ_pos N)) h

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PVanishingCechResidue
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.KeyFormula

open Complex Matrix

noncomputable section

open RigSymForm

theorem serreVanishing_graded_holds : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kleiman.SerreVanish.Statement :=
  (GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.SerreVanish.equiv
    GroundTheory.Heights₂.Heights.Kleiman.TranslateEq.GradedCech.proof).1
    GroundTheory.Heights₂.Heights.Kleiman.SerreVanish.full.{0, 0}

theorem VanishingCechResidue.proof (hM : ResidueFiniteModel.Statement)
    (hT : ResidueChartTransport.Statement) : VanishingCechResidue.Statement := by
  intro P a ha r x hx b hb
  obtain ⟨𝓜⟩ := hM P a ha r x hx b hb
  obtain ⟨c₀, hc₀⟩ := serreVanishing_graded_holds ℂ r 𝓜.M 𝓜.G 𝓜.finite
  refine ⟨c₀.toNat, fun c hc q φ hφ => hT P a b r x 𝓜 c₀ hc₀ c ?_ q φ hφ⟩
  have := Int.self_le_toNat c₀
  omega

end

end GroundTheory.Heights₂.Heights.KeyFormula
end

