import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0007

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.BoxFundX
section
noncomputable section

open MeasureTheory

namespace Formalism.L2.SG.NGCut.SplitEmbedding

theorem box_fundX {ι P : Type} [Fintype P] [DecidableEq P] (h : P → ℕ) (BX : P → (P → ℂ) → (P → ℂ) → ℂ)
    (hBd : ∀ p (x x' y y' : P → ℂ), (∀ q, h q < h p → x q = x' q ∧ y q = y' q) → BX p x y = BX p x' y')
    (τ : P → (ι → P → ℂ) → (ι → ℂ))
    (hτ : ∀ p (x x' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, x v q = x' v q) → τ p x = τ p x')
    (A : P → AddSubgroup (ι → ℂ)) (F : P → Set (ι → ℂ)) (hFd : ∀ p (v : ι → ℂ), ∃! a : A p, (a : ι → ℂ) + v ∈ F p)
    (x : ι → P → ℂ) :
    ∃! γ : ι → P → ℂ, (∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p} := by
  classical
  let w : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ => τ p γ + fun v => x v p + BX p (γ v) (x v)
  let c : P → (ι → P → ℂ) → (ι → ℂ) := fun p γ =>
    ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ
  have hloc : ∀ p (γ γ' : ι → P → ℂ), (∀ q, h q < h p → ∀ v, γ v q = γ' v q) → c p γ = c p γ' := by
    intro p γ γ' hg
    have h1 : τ p γ = τ p γ' := hτ p γ γ' hg
    have h2 : w p γ = w p γ' := by
      show (τ p γ + fun v => x v p + BX p (γ v) (x v)) = τ p γ' + fun v => x v p + BX p (γ' v) (x v)
      rw [h1]
      congr 1
      funext v
      rw [hBd p (γ v) (γ' v) (x v) (x v) (fun q hq => ⟨hg q hq v, rfl⟩)]
    have hch : ∀ u u' : ι → ℂ, u = u' →
        ((hFd p u).exists.choose : ι → ℂ) = ((hFd p u').exists.choose : ι → ℂ) := by
      rintro u _ rfl
      rfl
    show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = ((hFd p (w p γ')).exists.choose : ι → ℂ) + τ p γ'
    rw [h1, hch _ _ h2]
  have key : ∀ p (γ : ι → P → ℂ), ((fun v => γ v p) - τ p γ ∈ A p ∧ (fun v => lawX BX γ x v p) ∈ F p) ↔
      (fun v => γ v p) = c p γ := by
    intro p γ
    obtain ⟨a, ha, huniq⟩ := hFd p (w p γ)
    have hc : c p γ = (a : ι → ℂ) + τ p γ := by
      show ((hFd p (w p γ)).exists.choose : ι → ℂ) + τ p γ = (a : ι → ℂ) + τ p γ
      rw [huniq _ (hFd p (w p γ)).exists.choose_spec]
    have hlaw : (fun v => lawX BX γ x v p) = ((fun v => γ v p) - τ p γ) + w p γ := by
      funext v
      simp only [lawX, w, Pi.add_apply, Pi.sub_apply]
      ring
    rw [hc, hlaw]
    constructor
    · rintro ⟨hA, hF⟩
      have e := congrArg Subtype.val (huniq ⟨_, hA⟩ hF)
      simp only at e
      rw [← e]
      abel
    · intro hg
      rw [hg, add_sub_cancel_right]
      exact ⟨a.2, ha⟩
  let Φ : (ι → P → ℂ) → (ι → P → ℂ) := fun γ v p => c p γ v
  have hit : ∀ k (γ γ' : ι → P → ℂ), ∀ p, h p < k → ∀ v, (Φ^[k] γ) v p = (Φ^[k] γ') v p := by
    intro k
    induction k with
    | zero => intro γ γ' p hp; exact absurd hp (Nat.not_lt_zero _)
    | succ k ih =>
      intro γ γ' p hp v
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      show c p (Φ^[k] γ) v = c p (Φ^[k] γ') v
      rw [hloc p _ _ (fun q hq v => ih γ γ' q (by omega) v)]
  have hN : ∀ p, h p < Finset.univ.sup h + 1 := fun p =>
    Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ p))
  have hcond : ∀ γ : ι → P → ℂ, ((∀ p, (fun v => γ v p) - τ p γ ∈ A p) ∧
      lawX BX γ x ∈ {y : ι → P → ℂ | ∀ p, (fun v => y v p) ∈ F p}) ↔ Φ γ = γ := by
    intro γ
    rw [Set.mem_setOf_eq, ← forall_and, forall_congr' (fun p => key p γ)]
    constructor
    · intro H
      funext v p
      exact (congrFun (H p) v).symm
    · intro H p
      funext v
      exact (congrFun (congrFun H v) p).symm
  refine ⟨Φ^[Finset.univ.sup h + 1] 0, (hcond _).2 ?_, fun γ hγ => ?_⟩
  · rw [← Function.iterate_succ_apply' Φ _ 0, Function.iterate_succ_apply]
    funext v p
    exact hit _ (Φ 0) 0 p (hN p) v
  · have e1 : Φ^[Finset.univ.sup h + 1] γ = γ := Function.iterate_fixed ((hcond γ).1 hγ) _
    funext v p
    calc γ v p = (Φ^[Finset.univ.sup h + 1] γ) v p := by rw [e1]
      _ = _ := hit _ γ 0 p (hN p) v

end Formalism.L2.SG.NGCut.SplitEmbedding
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxLoc
section
noncomputable section

open IsDedekindDomain NumberField ValuativeRel

namespace Formalism.L2.SG.Pf.ProdEApprox

section Loc

open Formalism.MainNotions.S.Loc PI.StrongApproxE

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {sig : E →ₐ[F] E}
  {p : HeightOneSpectrum (𝓞 F)} (L : LocAt F E sig p)

def latS (c : L.Fp) : AddSubgroup L.Ep where
  carrier := {x | ∃ y ∈ L.O, x = algebraMap L.Fp L.Ep c * y}
  zero_mem' := ⟨0, L.O.zero_mem, by simp⟩
  add_mem' := by
    rintro x x' ⟨y, hy, rfl⟩ ⟨y', hy', rfl⟩
    exact ⟨y + y', L.O.add_mem hy hy', by ring⟩
  neg_mem' := by
    rintro x ⟨y, hy, rfl⟩
    exact ⟨-y, L.O.neg_mem hy, by ring⟩

variable {L}

theorem mem_latS {c : L.Fp} {x : L.Ep} : x ∈ latS L c ↔ ∃ y ∈ L.O, x = algebraMap L.Fp L.Ep c * y := Iff.rfl

theorem alg_mem_O {s : L.Fp} (hs : s ∈ 𝒪[L.Fp]) : algebraMap L.Fp L.Ep s ∈ L.O := by
  refine (L.O_def _).mpr ?_
  first
  | exact isIntegral_algebraMap (x := (⟨s, hs⟩ : 𝒪[L.Fp]))
  | exact (IsScalarTower.algebraMap_apply (𝒪[L.Fp]) L.Fp L.Ep ⟨s, hs⟩) ▸ isIntegral_algebraMap

theorem latS_mul {c c' : L.Fp} {x y : L.Ep} (hx : x ∈ latS L c) (hy : y ∈ latS L c') : x * y ∈ latS L (c * c') := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact ⟨a * b, L.O.mul_mem ha hb, by rw [map_mul]; ring⟩

theorem O_mul_latS {c : L.Fp} {x y : L.Ep} (hy : y ∈ L.O) (hx : x ∈ latS L c) : y * x ∈ latS L c := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨y * a, L.O.mul_mem hy ha, by ring⟩

theorem latS_mono {c c' : L.Fp} (hc' : c' ∈ 𝒪[L.Fp]) {x : L.Ep} (hx : x ∈ latS L (c * c')) : x ∈ latS L c := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨algebraMap L.Fp L.Ep c' * a, L.O.mul_mem (alg_mem_O hc') ha, by rw [map_mul]; ring⟩

theorem bounded_Fp (a : L.Fp) : ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ s * a ∈ 𝒪[L.Fp] := by
  by_cases ha : a ∈ 𝒪[L.Fp]
  · exact ⟨1, one_ne_zero, one_mem _, by rw [one_mul]; exact ha⟩
  · have h0 : a ≠ 0 := by
      rintro rfl
      exact ha (zero_mem _)
    refine ⟨a⁻¹, inv_ne_zero h0, ?_, by rw [inv_mul_cancel₀ h0]; exact one_mem _⟩
    rw [Valuation.mem_integer_iff] at ha ⊢
    rw [map_inv₀]
    exact inv_le_one_of_one_le₀ (le_of_lt (not_le.mp ha))

theorem bounded (x : L.Ep) : ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ algebraMap L.Fp L.Ep s * x ∈ L.O := by
  classical
  obtain ⟨n, b, hbint, hbspan⟩ := intSpan' F E
  obtain ⟨α, hα⟩ := local_span_holds F E sig p L n b hbspan x
  choose s hs0 hsO hsa using fun i => bounded_Fp (L := L) (α i)
  have hbO : ∀ i, L.ιE (b i) ∈ L.O := by
    intro i
    have := local_integral_of_substitution F E sig p L 1 (b i) (by simp) (hbint i)
    simpa using this
  refine ⟨∏ i, s i, Finset.prod_ne_zero_iff.2 fun i _ => hs0 i, Subring.prod_mem _ fun i _ => hsO i, ?_⟩
  rw [hα, Finset.mul_sum]
  refine L.O.sum_mem fun i _ => ?_
  have e : algebraMap L.Fp L.Ep (∏ j, s j) * (α i • L.ιE (b i)) =
      algebraMap L.Fp L.Ep ((∏ j ∈ Finset.univ.erase i, s j) * (s i * α i)) * L.ιE (b i) := by
    rw [Algebra.smul_def, ← mul_assoc, ← map_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    ring_nf
  rw [e]
  exact L.O.mul_mem (alg_mem_O (Subring.mul_mem _ (Subring.prod_mem _ fun j _ => hsO j) (hsa i))) (hbO i)

theorem bounded_mat {n : ℕ} (B : Matrix (Fin n) (Fin n) L.Ep) :
    ∃ s : L.Fp, s ≠ 0 ∧ s ∈ 𝒪[L.Fp] ∧ ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O := by
  choose s hs0 hsO hsB using fun (p : Fin n × Fin n) => bounded (B p.1 p.2)
  refine ⟨∏ p, s p, Finset.prod_ne_zero_iff.mpr fun p _ => hs0 p, prod_mem fun p _ => hsO p, ?_⟩
  intro i j
  rw [← Finset.mul_prod_erase Finset.univ s (Finset.mem_univ (i, j)), map_mul, mul_comm (algebraMap L.Fp L.Ep (s (i, j))), mul_assoc]
  exact L.O.mul_mem (alg_mem_O (prod_mem fun p _ => hsO p)) (hsB (i, j))

theorem entIn_mul_left {n : ℕ} {B : Matrix (Fin n) (Fin n) L.Ep} {s : L.Fp}
    (hs : ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O) {c : L.Fp} {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L (s * c)) X) : EntIn (latS L c) (B * X) := by
  intro i j
  rw [Matrix.mul_apply]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  obtain ⟨y, hy, hxy⟩ := hX k j
  refine ⟨algebraMap L.Fp L.Ep s * B i k * y, L.O.mul_mem (hs i k) hy, ?_⟩
  rw [hxy, map_mul]
  ring

theorem entIn_mul_right {n : ℕ} {B : Matrix (Fin n) (Fin n) L.Ep} {s : L.Fp}
    (hs : ∀ i j, algebraMap L.Fp L.Ep s * B i j ∈ L.O) {c : L.Fp} {X : Matrix (Fin n) (Fin n) L.Ep}
    (hX : EntIn (latS L (s * c)) X) : EntIn (latS L c) (X * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  obtain ⟨y, hy, hxy⟩ := hX i k
  refine ⟨algebraMap L.Fp L.Ep s * B k j * y, L.O.mul_mem (hs k j) hy, ?_⟩
  rw [hxy, map_mul]
  ring

theorem latS_mul_self {c : L.Fp} (hc : c ∈ 𝒪[L.Fp]) {x y : L.Ep} (hx : x ∈ latS L c) (hy : y ∈ latS L c) :
    x * y ∈ latS L c := latS_mono hc (latS_mul hx hy)

end Loc

end Formalism.L2.SG.Pf.ProdEApprox
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ProdEApproxMono
section
noncomputable section

namespace Formalism.L2.SG.Pf.ProdEApprox

section Mono

variable {A : Type*} [CommRing A] {n : ℕ}

def mono (σ : Fin n → Fin n) (ν : Fin n → A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun a b => if b = σ a then ν a else 0

theorem mono_mul (σ : Fin n → Fin n) (ν : Fin n → A) (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    (mono σ ν * X) i j = ν i * X (σ i) j := by
  simp [mono, Matrix.mul_apply, ite_mul]

variable {σ : Fin n → Fin n} (hσ : ∀ a, σ (σ a) = a) (ν : Fin n → A)
include hσ

theorem mul_mono (X : Matrix (Fin n) (Fin n) A) (i j : Fin n) : (X * mono σ ν) i j = X i (σ j) * ν (σ j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · simp [mono, hσ]
  · intro b _ hb
    have hj : j ≠ σ b := fun h => hb (by rw [h, hσ])
    simp [mono, hj]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem fix_entry {l c : Matrix (Fin n) (Fin n) A} (h : l * mono σ ν = mono σ ν * c) (i j : Fin n) :
    l i j * ν j = ν i * c (σ i) (σ j) := by
  have e := congrFun (congrFun h i) (σ j)
  rw [mul_mono hσ, mono_mul, hσ] at e
  exact e

theorem fix_pat (hν : ∀ a, IsUnit (ν a)) {l c : Matrix (Fin n) (Fin n) A} (hc : ∀ i j, j < i → c i j = 0)
    (h : l * mono σ ν = mono σ ν * c) (i j : Fin n) (hij : σ j < σ i) : l i j = 0 := by
  have e := fix_entry hσ ν h i j
  rw [hc _ _ hij, mul_zero] at e
  exact (hν j).mul_left_eq_zero.mp e

omit hσ in

def cOf (σ : Fin n → Fin n) (ν : Fin n → A) (l : Matrix (Fin n) (Fin n) A) : Matrix (Fin n) (Fin n) A :=
  Matrix.of fun a b => Ring.inverse (ν (σ a)) * l (σ a) (σ b) * ν (σ b)

theorem fix_cOf (hν : ∀ a, IsUnit (ν a)) (l : Matrix (Fin n) (Fin n) A) :
    l * mono σ ν = mono σ ν * cOf σ ν l := by
  ext i j
  rw [mul_mono hσ, mono_mul]
  simp only [cOf, Matrix.of_apply, hσ]
  rw [← mul_assoc, ← mul_assoc, Ring.mul_inverse_cancel _ (hν i), one_mul]

theorem cOf_up (l : Matrix (Fin n) (Fin n) A) (hl : ∀ i, l i i = 1) (hpat : ∀ i j, σ j < σ i → l i j = 0)
    (hν : ∀ a, IsUnit (ν a)) : (∀ a, cOf σ ν l a a = 1) ∧ ∀ a b, b < a → cOf σ ν l a b = 0 := by
  refine ⟨fun a => ?_, fun a b hab => ?_⟩
  · simp only [cOf, Matrix.of_apply, hl, mul_one]
    exact Ring.inverse_mul_cancel _ (hν _)
  · simp only [cOf, Matrix.of_apply]
    rw [hpat (σ a) (σ b) (by rw [hσ, hσ]; exact hab), mul_zero, zero_mul]

end Mono

end Formalism.L2.SG.Pf.ProdEApprox
end
end

