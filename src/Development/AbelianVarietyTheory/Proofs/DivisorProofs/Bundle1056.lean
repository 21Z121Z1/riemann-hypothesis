import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolySubComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToNatFloorLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct InnerProductSpace
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdelicScalar.SizeBounds

theorem one_le_rdE (D : D7) : (1 : ℝ) ≤ D.host.rdE := by
  unfold Formalism.BasicNotions.Host.rdE
  apply Real.one_le_rpow
  · have h := NumberField.discr_ne_zero D.host.E
    rw [← Int.cast_abs]
    exact_mod_cast Int.one_le_abs h
  · positivity

theorem one_le_b (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) : 1 ≤ b := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes at h
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := by
    rw [← Fintype.card_pos_iff, D.what₂.card_Tau]
    show 0 < 2 * D.R.ord
    have h1 := D.R.two_le_m
    have h2 := D.R.m_le_f
    omega
  obtain ⟨-, -, -, hb⟩ := h.1 τ
  have hq := (D.hc τ).gap_be i
  have hr : ((((D.R.t : ℚ) + 3) / 2 : ℚ) : ℝ) ≤ (((D.hc τ).e i - (D.hc τ).b i : ℚ) : ℝ) := by
    exact_mod_cast hq
  push_cast at hr
  have habs := abs_le.mp (hb i)
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  linarith [habs.1, habs.2]

theorem lam_bounds (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (τ : D.what₂.Tau) (n : ℕ) :
    -b ≤ ((Formalism.L2.NTheta.lamAt (D.hc τ) n : ℚ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ) ∧
      ((Formalism.L2.NTheta.lamAt (D.hc τ) n : ℚ) : ℝ) + (((D.hc τ).e i : ℚ) : ℝ) ≤ 3 * b := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues.Sizes at h
  obtain ⟨he0, he2, hv, hb⟩ := h.1 τ
  have hb0 : (0 : ℝ) ≤ b := by linarith
  unfold Formalism.L2.NTheta.lamAt
  split_ifs with h1 h2
  · obtain ⟨hv0, hv1⟩ := hv ⟨n, h1⟩
    constructor <;> linarith
  · have habs := abs_le.mp (hb ⟨n - (D.R.k - 1), h2⟩)
    push_cast
    constructor <;> linarith [habs.1, habs.2]
  · push_cast
    constructor <;> linarith

theorem toNat_floor_le (x : ℚ) (c : ℝ) (hc : 0 ≤ c) (hx : (x : ℝ) ≤ c) : ((⌊x⌋.toNat : ℕ) : ℝ) ≤ c := by
  rcases le_or_gt ⌊x⌋ 0 with h0 | h0
  · rw [Int.toNat_of_nonpos h0]
    simpa using hc
  · have h1 : ((⌊x⌋.toNat : ℕ) : ℤ) = ⌊x⌋ := Int.toNat_of_nonneg h0.le
    have h2 : ((⌊x⌋.toNat : ℕ) : ℝ) = ((⌊x⌋ : ℤ) : ℝ) := by exact_mod_cast h1
    rw [h2]
    have h3 : ((⌊x⌋ : ℤ) : ℝ) ≤ ((x : ℚ) : ℝ) := by exact_mod_cast Int.floor_le x
    linarith

theorem aPl_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (p : ℕ) (τ : D.what₂.Tau) (n : ℕ) :
    (aPl D i p τ n : ℝ) ≤ 3 * b := by
  have hlam := (lam_bounds D i b h τ n).2
  have hb1 := one_le_b D i b h
  unfold aPl
  split_ifs with hn
  · apply toNat_floor_le _ _ (by linarith)
    push_cast
    have hnp : (n : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  · simp only [Nat.cast_zero]
    linarith

theorem aMi_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (p q : ℕ) (τ : D.what₂.Tau) (n : ℕ) :
    (aMi D i p q τ n : ℝ) ≤ 3 * b := by
  have hlam := (lam_bounds D i b h τ (p + (q - n) - 1)).1
  have hb1 := one_le_b D i b h
  unfold aMi
  split_ifs with hn
  · apply toNat_floor_le _ _ (by linarith)
    push_cast
    have hqn : (0 : ℝ) ≤ ((q - n : ℕ) : ℝ) := Nat.cast_nonneg _
    have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
    linarith
  · simp only [Nat.cast_zero]
    linarith

theorem degAt_le (D : D7) (i : Fin D.R.m) (b : ℝ) (h : Sizes D i b) (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau) :
    (degAt D i σ ρ : ℝ) ≤ 3 * (D.R.r : ℝ) * b := by
  have hb1 := one_le_b D i b h
  have hi := i.isLt
  have hs := D.sp.W_sigval ((i : ℕ) + 1) (by omega) (by omega) (tauE D ρ)
  have hP : ∀ n, ((aPlAt D i σ ρ n : ℕ) : ℝ) ≤ 3 * b := fun n => aPl_le D i b h _ _ n
  have hM : ∀ n, ((aMiAt D i σ ρ n : ℕ) : ℝ) ≤ 3 * b := fun n => aMi_le D i b h _ _ _ n
  have h1 := Finset.sum_le_sum (s := Finset.range (pW D i ρ)) (fun n _ => hP n)
  have h2 := Finset.sum_le_sum (s := Finset.range (qW D i ρ)) (fun n _ => hM n)
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1 h2
  have hr : (pW D i ρ : ℝ) + (qW D i ρ : ℝ) = (D.R.r : ℝ) := by
    have hn : pW D i ρ + qW D i ρ = D.R.r := by
      simp only [pW, qW, Wc, hs]
      unfold Formalism.BasicNotions.Ranks.sigW Formalism.BasicNotions.Ranks.r
      dsimp only
      omega
    exact_mod_cast hn
  unfold degAt
  push_cast
  calc _ ≤ (pW D i ρ : ℝ) * (3 * b) + (qW D i ρ : ℝ) * (3 * b) := add_le_add h1 h2
    _ = 3 * (D.R.r : ℝ) * b := by rw [← hr]; ring

theorem sizes : ∀ (D : D7) (i : Fin D.R.m) (b : ℝ), Sizes D i b → (5.5 : ℝ) ≤ Lp D b ∧ Real.log (D.R.nV : ℝ) ≤ Lp D b ∧ 0 ≤ b ∧ Real.log (3 * (D.R.r : ℝ) * b + 2) ≤ 2 * Lp D b ∧ ∀ (σ : D.what₂.LL →+* ℂ) (ρ : D.what₂.Tau), (degAt D i σ ρ : ℝ) ≤ 3 * (D.R.r : ℝ) * b := by
  intro D i b h
  have hb1 := one_le_b D i b h
  have hrd := one_le_rdE D
  have hnV : (1 : ℝ) ≤ (D.R.nV : ℝ) := by
    have h1 := D.R.t_odd.pos
    have h2 : 1 ≤ D.R.nV := by
      unfold Formalism.BasicNotions.Ranks.nV
      omega
    exact_mod_cast h2
  have hk5 : 5 ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    have := D.R.two_le_m
    omega
  have hrk : D.R.r ≤ 2 * D.R.k := by
    have := D.R.m_add_three_le_k
    unfold Formalism.BasicNotions.Ranks.r
    omega
  have hk : (5 : ℝ) ≤ (D.R.k : ℝ) := by exact_mod_cast hk5
  have hr2 : (D.R.r : ℝ) ≤ 2 * (D.R.k : ℝ) := by exact_mod_cast hrk
  have hgl := h.2
  have hg0 := hgl 0
  have hg1 := hgl 1
  set y : ℝ := (D.R.k : ℝ) * b with hy
  have hy5 : 5 ≤ y := by nlinarith
  have hy8 : y ^ 3 ≤ y ^ 8 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have hyy : 25 ≤ y * y := by nlinarith
  have hy3 : 25 * y ≤ y ^ 3 := by nlinarith [mul_le_mul_of_nonneg_right hyy (by linarith : (0 : ℝ) ≤ y)]
  have hyP : (390625 : ℝ) ≤ y ^ 8 := by
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hy5 8
    norm_num at this
    linarith
  have hg1' : (1 : ℝ) ≤ (D.host.g 1 : ℝ) := by linarith
  have hg0' : (0 : ℝ) ≤ (D.host.g 0 : ℝ) := Nat.cast_nonneg _
  have hbr : (1 : ℝ) ≤ b * D.host.rdE := one_le_mul_of_one_le_of_one_le hb1 hrd
  have hG : (D.host.g 0 : ℝ) ≤ (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) := le_mul_of_one_le_right hg0' hg1'
  have hA : (D.host.g 0 : ℝ) * (D.host.g 1 : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) :=
    le_mul_of_one_le_left (by positivity) hbr
  have hB : b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) ≤
      b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) :=
    le_mul_of_one_le_right (by positivity) hnV
  have hC : (1 : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) := by linarith
  have hD : (D.R.nV : ℝ) ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) :=
    le_mul_of_one_le_left (by positivity) hC
  have hX : y ^ 8 ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by linarith
  have hL : Lp D b = Real.log (b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ)) := rfl
  have hXpos : 0 < b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by linarith
  have he6 : Real.exp (5.5 : ℝ) ≤ 729 := by
    have h1 : Real.exp (5.5 : ℝ) ≤ Real.exp 6 := Real.exp_le_exp.mpr (by norm_num)
    have h2 : Real.exp 6 = Real.exp 1 ^ 6 := by
      rw [← Real.exp_nat_mul]
      norm_num
    have h3 : Real.exp 1 ^ 6 ≤ (3 : ℝ) ^ 6 :=
      pow_le_pow_left₀ (Real.exp_pos 1).le (by linarith [Real.exp_one_lt_d9]) 6
    norm_num at h3
    linarith
  have h55 : (5.5 : ℝ) ≤ Lp D b := by
    rw [hL]
    calc (5.5 : ℝ) = Real.log (Real.exp 5.5) := (Real.log_exp _).symm
      _ ≤ _ := Real.log_le_log (Real.exp_pos _) (by linarith)
  refine ⟨h55, ?_, by linarith, ?_, fun σ ρ => degAt_le D i b h σ ρ⟩
  · rw [hL]
    exact Real.log_le_log (by linarith) hD
  · have hb0 : (0 : ℝ) ≤ b := by linarith
    have hrb : (D.R.r : ℝ) * b ≤ (2 * (D.R.k : ℝ)) * b := mul_le_mul_of_nonneg_right hr2 hb0
    have h32 : 3 * (D.R.r : ℝ) * b + 2 ≤ b * D.host.rdE * ((D.host.g 0 : ℝ) * (D.host.g 1 : ℝ)) * (D.R.nV : ℝ) := by
      nlinarith
    have hpos : 0 < 3 * (D.R.r : ℝ) * b + 2 := by positivity
    have hlog := Real.log_le_log hpos h32
    rw [← hL] at hlog
    linarith

end GlobalTheory.AdelicScalar.SizeBounds
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusOntoAdelicCentralizer
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.CentTorus
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentAway

theorem flat_centralizer (R B L : Type) [CommRing R] [Algebra ℚ R] [Ring B] [Algebra ℚ B] [Ring L] [Algebra ℚ L]
    (γ : B) (f : L →ₐ[ℚ] B) (hf : Function.Injective f)
    (hcent : ∀ x : B, x * γ = γ * x ↔ x ∈ Set.range f) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id R R) f) ∧
      ∀ y : R ⊗[ℚ] B, y * ((1 : R) ⊗ₜ[ℚ] γ) = ((1 : R) ⊗ₜ[ℚ] γ) * y ↔
        y ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id R R) f) := by
  let ad : B →ₗ[ℚ] B := LinearMap.mulRight ℚ γ - LinearMap.mulLeft ℚ γ
  have hex : Function.Exact f.toLinearMap ad := by
    intro x
    simp only [ad, LinearMap.sub_apply, LinearMap.mulRight_apply, LinearMap.mulLeft_apply, sub_eq_zero,
      AlgHom.toLinearMap_apply]
    exact hcent x
  have hmap : ∀ y, Algebra.TensorProduct.map (AlgHom.id R R) f y = LinearMap.lTensor R f.toLinearMap y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t a => simp
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have had : ∀ y : R ⊗[ℚ] B, y * ((1 : R) ⊗ₜ[ℚ] γ) - ((1 : R) ⊗ₜ[ℚ] γ) * y = LinearMap.lTensor R ad y := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t b =>
      simp [ad, Algebra.TensorProduct.tmul_mul_tmul, TensorProduct.tmul_sub]
    | add x y hx hy => rw [map_add, ← hx, ← hy]; noncomm_ring
  have hex' := Module.Flat.lTensor_exact R hex
  refine ⟨?_, fun y => ?_⟩
  · have h := Module.Flat.lTensor_preserves_injective_linearMap (M := R) f.toLinearMap hf
    intro a b hab
    rw [hmap, hmap] at hab
    exact h hab
  · rw [← sub_eq_zero, had, hex' y]
    constructor
    · rintro ⟨z, rfl⟩
      exact ⟨z, hmap z⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, (hmap z).symm⟩

variable {p : ℕ} [Fact p.Prime]

def incl (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    R ⊗[ℚ] algF P →ₐ[R] R ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id R R) ((algF P).val.restrictScalars ℚ)

theorem incl_tmul (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (a : R) (m : algF P) :
    incl R P (a ⊗ₜ m) = a ⊗ₜ (m : G.C) := rfl

theorem cent_iff {G : HTGroup p} (P : Pair G) (x : G.C) :
    x * P.γ = P.γ * x ↔ x ∈ Set.range ((algF P).val.restrictScalars ℚ) := by
  have h := GlobalTheory.CentSep.centralizer_eq_adjoin G.F G.C G.n G.rankC (P.γ : G.C) P.reg.2 P.reg.1
  constructor
  · intro hx
    have hm : x ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by
      rw [Subalgebra.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.1 hg]
      exact hx.symm
    rw [h] at hm
    exact ⟨⟨x, hm⟩, rfl⟩
  · rintro ⟨m, rfl⟩
    have hm : (m : G.C) ∈ Subalgebra.centralizer G.F {(P.γ : G.C)} := by rw [h]; exact m.2
    rw [Subalgebra.mem_centralizer_iff] at hm
    exact (hm _ (Set.mem_singleton _)).symm

theorem incl_facts (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    Function.Injective (incl R P) ∧ ∀ y : R ⊗[ℚ] G.C, y * inC G R P.γ = inC G R P.γ * y ↔ y ∈ Set.range (incl R P) :=
  flat_centralizer R G.C (algF P) (P.γ : G.C) _ Subtype.val_injective (cent_iff P)

theorem exists_retr (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    ∃ π : R ⊗[ℚ] algF P →ₗ[R] R, ∀ a, π (algebraMap R _ a) = a := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ (algF P))
    (LinearMap.ker_eq_bot.2 (algebraMap ℚ (algF P)).injective)
  have h1 : φ 1 = 1 := by
    have := LinearMap.congr_fun hφ 1
    simpa using this
  refine ⟨(TensorProduct.AlgebraTensorModule.rid ℚ R R).toLinearMap ∘ₗ
    TensorProduct.AlgebraTensorModule.lTensor R R φ, fun a => ?_⟩
  simp [Algebra.TensorProduct.algebraMap_apply, h1]

theorem alg_inj (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) :
    Function.Injective (algebraMap R (R ⊗[ℚ] algF P)) := by
  obtain ⟨π, hπ⟩ := exists_retr R P
  intro a b h
  rw [← hπ a, ← hπ b, h]

theorem incl_extC (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)
    (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (z : R ⊗[ℚ] algF P) :
    incl R P (extC R c z) =
      inC G R P.β * (starT G.star R (incl R P z)).unop * inC G R ((P.β⁻¹ : G.Cˣ) : G.C) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    rw [incl_tmul, starT_tmul]
    simp only [extC, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, incl_tmul, hc, inC, RingHom.coe_coe,
      Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, sh]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, MulOpposite.unop_add, mul_add, add_mul]

theorem incl_sim (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)
    (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (y : R ⊗[ℚ] algF P) (s : R) (hy : y * extC R c y = algebraMap R _ s) :
    incl R P y * inC G R P.β * (starT G.star R (incl R P y)).unop = algebraMap R (R ⊗[ℚ] G.C) s * inC G R P.β := by
  have h1 := congrArg (incl R P) hy
  rw [map_mul, incl_extC R P c hc, AlgHom.commutes] at h1
  have hb : inC G R ((P.β⁻¹ : G.Cˣ) : G.C) * inC G R P.β = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  calc incl R P y * inC G R P.β * (starT G.star R (incl R P y)).unop
      = incl R P y * (inC G R P.β * (starT G.star R (incl R P y)).unop * inC G R ((P.β⁻¹ : G.Cˣ) : G.C)) *
          inC G R P.β := by
        simp only [mul_assoc, hb, mul_one]
    _ = _ := by rw [h1]

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

variable {p : ℕ} [Fact p.Prime]

section Generic

variable (R : Type) [CommRing R] [Algebra ℚ R] {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)

def nu (y : simR R (extC R c)) : Rˣ := (mem_simR.1 y.2).choose

theorem nu_spec (y : simR R (extC R c)) :
    ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) =
      algebraMap R _ ((nu R P c y : Rˣ) : R) :=
  (mem_simR.1 y.2).choose_spec

theorem nu_eq (y : simR R (extC R c)) (s : Rˣ)
    (h : ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) =
      algebraMap R _ (s : R)) : nu R P c y = s :=
  Units.ext (alg_inj R P (by rw [← nu_spec, h]))

def nuHom : simR R (extC R c) →* Rˣ where
  toFun := nu R P c
  map_one' := nu_eq R P c 1 1 (by simp [Algebra.TensorProduct.one_def])
  map_mul' y z := nu_eq R P c _ _ (by
    simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
    rw [show ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * ((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) *
        (extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P)) =
        (((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((y : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P)) *
        (((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P) * extC R c ((z : (R ⊗[ℚ] algF P)ˣ) : R ⊗[ℚ] algF P)) by ring,
      nu_spec, nu_spec])

def conjHom (x : (R ⊗[ℚ] G.C)ˣ) : simR R (extC R c) →* (R ⊗[ℚ] G.C)ˣ :=
  (MulAut.conj x).toMonoidHom.comp
    ((Units.map (incl R P).toRingHom.toMonoidHom).comp (simR R (extC R c)).subtype)

def phi0 (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (x : (R ⊗[ℚ] G.C)ˣ) (t : Rˣ) (hx : Triv G R P.β x t) : simR R (extC R c) →* UPts G.star R :=
  ((conjHom R P c x).prod (nuHom R P c)).codRestrict _ fun y =>
    conj_mul_star (starT G.star R) (inC G R P.β) x
      (Units.map (incl R P).toRingHom.toMonoidHom (y : (R ⊗[ℚ] algF P)ˣ)) t ((nu R P c y : Rˣ) : R) hx
      (incl_sim R P c hc _ _ (nu_spec R P c y))

end Generic

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

open GlobalTheory.BCT

variable {p : ℕ} [Fact p.Prime]

def phi {G : HTGroup p} (P : Pair G) (c : algF P →ₐ[ℚ] algF P)
    (hc : ∀ m : algF P, ((c m : algF P) : G.C) = (P.β : G.C) * sh G (m : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C))
    (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) P.β x t) :
    simR (AfP p) (extC (AfP p) c) →* twCent (MonoidHom.id G.GAf) (P.toAf x t hx P.self) :=
  (phi0 (AfP p) P c hc x t hx).codRestrict _ fun y => by
    have hYΓ : Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) *
        Units.map (inC G (AfP p)).toMonoidHom P.γ =
        Units.map (inC G (AfP p)).toMonoidHom P.γ * Units.map (incl (AfP p) P).toRingHom.toMonoidHom y :=
      Units.ext (((incl_facts (AfP p) P).2 _).2 ⟨_, rfl⟩)
    refine Subtype.ext (Prod.ext ?_ (mul_comm _ _))
    change x * Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) * x⁻¹ *
        (x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹) =
      x * Units.map (inC G (AfP p)).toMonoidHom P.γ * x⁻¹ *
        (x * Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) * x⁻¹)
    calc _ = x * (Units.map (incl (AfP p) P).toRingHom.toMonoidHom (y : (AfP p ⊗[ℚ] algF P)ˣ) *
          Units.map (inC G (AfP p)).toMonoidHom P.γ) * x⁻¹ := by group
      _ = _ := by rw [hYΓ]; group

end GlobalTheory.CentAway

namespace GlobalTheory.CentAway

open GlobalTheory.BCT

variable {p : ℕ} [Fact p.Prime]

end GlobalTheory.CentAway
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjOfTwistedNormEqGLOneUnramified
section
open Matrix GlobalTheory.LKRes GlobalTheory.LKMid
open scoped TensorProduct

namespace GlobalTheory.LKMid

theorem twistedNormProductIterate_map_intertwining {H H' : Type} [Group H] [Group H'] (θ : H →* H) (θ' : H' →* H') (f : H →* H')
    (hf : ∀ x, f (θ x) = θ' (f x)) (r : ℕ) (x : H) : f (nrmG θ r x) = nrmG θ' r (f x) := by
  unfold nrmG
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact (Function.Semiconj.iterate_right (f := f) (ga := θ) (gb := θ') hf i) x

theorem twistedNormProductIterate_mul_commGroup {H : Type} [CommGroup H] (θ : H →* H) (r : ℕ) (a b : H) :
    nrmG θ r (a * b) = nrmG θ r a * nrmG θ r b := by
  unfold nrmG
  rw [← List.prod_map_mul]
  congr 1
  apply List.map_congr_left
  intro i hi
  clear hi
  induction i generalizing a b with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply, map_mul, ih]

end GlobalTheory.LKMid

namespace GlobalTheory.LKMid

theorem det_unramifiedExtFrobeniusGLEntrywise_GL_one (p : ℕ) [Fact p.Prime] (r : ℕ) (x : GL (Fin 1) (Qr p r)) :
    Matrix.GeneralLinearGroup.det (GlobalTheory.LKLoc.sig p (Q0 p) 1 r x) =
      Units.map (frobQ p r).toRingHom.toMonoidHom (Matrix.GeneralLinearGroup.det x) := by
  ext
  simp [GlobalTheory.LKLoc.sig, Matrix.det_unique]
  rfl

theorem generalLinearGroup_det_injective_GL_one (R : Type) [CommRing R] :
    Function.Injective (Matrix.GeneralLinearGroup.det : GL (Fin 1) R →* Rˣ) := by
  intro x y h
  ext i j
  have := congrArg Units.val h
  simp [Matrix.det_unique] at this
  fin_cases i; fin_cases j
  exact this

theorem generalLinearGroup_det_scalar_GL_one (R : Type) [CommRing R] (u : Rˣ) :
    Matrix.GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin 1) u) = u := by
  ext
  simp [Matrix.det_unique]

theorem exists_sig_twisted_conj_of_nrmG_eq : ∀ (p : ℕ) [Fact p.Prime] (r : ℕ), 0 < r → ∀ δ δ' : GL (Fin 1) (Qr p r),
    nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ = nrmG (GlobalTheory.LKLoc.sig p (Q0 p) 1 r) r δ' →
    ∃ h : GL (Fin 1) (Qr p r), δ' = h⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r h := by
  intro p _ r hr δ δ' hN
  let D : GL (Fin 1) (Qr p r) →* (Qr p r)ˣ := Matrix.GeneralLinearGroup.det
  let θ : (Qr p r)ˣ →* (Qr p r)ˣ := Units.map (frobQ p r).toRingHom.toMonoidHom
  have hD : ∀ x, D (GlobalTheory.LKLoc.sig p (Q0 p) 1 r x) = θ (D x) := det_unramifiedExtFrobeniusGLEntrywise_GL_one p r
  have hN' : nrmG θ r (D δ) = nrmG θ r (D δ') := by
    rw [← twistedNormProductIterate_map_intertwining _ _ D hD, ← twistedNormProductIterate_map_intertwining _ _ D hD, hN]
  let c : (Qr p r)ˣ := D δ' * (D δ)⁻¹
  have hc : nrmG θ r c = 1 := by
    have h1 : nrmG θ r c * nrmG θ r (D δ) = nrmG θ r (D δ) := by
      rw [← twistedNormProductIterate_mul_commGroup, inv_mul_cancel_right, hN']
    exact mul_eq_right.1 h1
  let L := Algebra.TensorProduct.lid ℚ_[p] (Qr p r)
  let Φ := Algebra.TensorProduct.map (AlgHom.id ℚ_[p] ℚ_[p]) (frobQ p r)
  have hL : ∀ x, L (Φ x) = frobQ p r (L x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
      simp only [L, Φ, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.lid_tmul, AlgHom.id_apply]
      exact ((frobQ p r).toLinearMap.map_smul b y).symm
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  have hLs : ∀ y, L.symm (frobQ p r y) = Φ (L.symm y) := by
    intro y
    apply L.injective
    rw [hL, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]
  let fS : (Qr p r)ˣ →* (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ := Units.map L.symm.toAlgHom.toRingHom.toMonoidHom
  let fL : (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ →* (Qr p r)ˣ := Units.map L.toAlgHom.toRingHom.toMonoidHom
  let ΦU : (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ →* (ℚ_[p] ⊗[ℚ_[p]] Qr p r)ˣ := Units.map Φ.toRingHom.toMonoidHom
  have hfS : ∀ x, fS (θ x) = ΦU (fS x) := fun x => Units.ext (hLs x)
  have hfL : ∀ x, fL (ΦU x) = θ (fL x) := fun x => Units.ext (hL x)
  have hLS : ∀ x, fL (fS x) = x := fun x => Units.ext (AlgEquiv.apply_symm_apply L x)
  have ha : nrmG ΦU r (fS c) = 1 := by
    rw [← twistedNormProductIterate_map_intertwining _ _ fS hfS, hc, map_one]
  obtain ⟨g, hg⟩ := hilbert90_frobenius_tensor_unramified_padic p r hr ℚ_[p] (fS c) ha
  have hc' : c = (fL g)⁻¹ * θ (fL g) := by
    rw [← hLS c, hg, map_mul, map_inv, hfL]
  refine ⟨GeneralLinearGroup.scalar (Fin 1) (fL g), generalLinearGroup_det_injective_GL_one _ ?_⟩
  have hs : D (GeneralLinearGroup.scalar (Fin 1) (fL g)) = fL g := generalLinearGroup_det_scalar_GL_one _ _
  have e : D δ' = c * D δ := by rw [inv_mul_cancel_right]
  change D δ' = D ((GeneralLinearGroup.scalar (Fin 1) (fL g))⁻¹ * δ * GlobalTheory.LKLoc.sig p (Q0 p) 1 r (GeneralLinearGroup.scalar (Fin 1) (fL g)))
  rw [map_mul, map_mul, map_inv, hD, hs, e, hc']
  exact mul_right_comm _ _ _

end GlobalTheory.LKMid
end

