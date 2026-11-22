import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallinePeriodEqCechDeRhamPeriod
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardFiniteSubgroupGLIntDvd
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
import Formalism.SharpRestriction.GlobalSchurBounds.Bundle0003
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.SixthReductionExplicit
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0074
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0733
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DUnitMemRangeOfMemKerIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeviProjectionDenominatorsOfHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuityCofilteredLimitRepresentedAffineStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuity_cofiltered_limit_represented_affine : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (D : I ⥤ PSh) (c : Cone D), IsLimit c → (∀ i, ∃ Z : Scheme.{0}, IsAffine Z ∧ Nonempty (yoneda.obj Z ≅ D.obj i)) → (∃ Z : Scheme.{0}, Nonempty (yoneda.obj Z ≅ c.pt)) → ContCone R F (disc.mapCone c) := by
  first
  | exact @GlobalTheory.contCone_of_represented
  | exact GlobalTheory.contCone_of_represented
  | (intros; apply GlobalTheory.contCone_of_represented <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvPowOfConvSubConstantCoeffInvariantDerivationStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.convPow_ofConv_sub_constantCoeff_invariantDerivation : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (n : ℕ) (m : Ideal O), (p : O) ∈ m → ∀ (u : Fin d → O) (φ : G.dual.A n), (∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m) → ∀ (k : ℕ) (F : MvPowerSeries (Fin d) O), (φ ^ k) (c.ev n F) - constantCoeff ((invDer c.μ u)^[k] F) ∈ m := by
  first | exact @GlobalTheory.LawDer.convPow_ev_sub_constantCoeff_iterate_mem | exact GlobalTheory.LawDer.convPow_ev_sub_constantCoeff_iterate_mem | (intros; apply GlobalTheory.LawDer.convPow_ev_sub_constantCoeff_iterate_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallinePeriodEqCechDeRhamPeriodStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystalline_period_eq_cechDeRham_period : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), ∀ (c : FirstDeRham (str A)) (q : u.Λ →+ ℂ) (per : u.Λ →+ Hol (fibFam u).V), (∀ l, per l = algebraMap ℂ _ (q l)) → IsPeriod (fibUnif u) c per → IsPer u.ex u.Λ (cmp1 (str A) c) q := by
  first | exact @GlobalTheory.PerLink.main | exact GlobalTheory.PerLink.main | (intros; apply GlobalTheory.PerLink.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalLeviDatumPermBlocksMatch
section
open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.Parabolic GlobalTheory.IndefiniteRowSideFullHecke.BlockProductIsomorphism

namespace GlobalTheory.FinGL.BlockMatch

variable {F : Type} [Field F] {r : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem eq_zero_of_invariant [Finite F] {b : Fin r → ℕ} {σ : Representation ℂ (blockTri (κ := F) b) V}
    (hσ : IsCuspDatum b σ) (S : Finset (Fin r)) (hS : ∃ i j, b i = b j ∧ i ∈ S ∧ j ∉ S) (T : V →ₗ[ℂ] W)
    (hT : ∀ u : blockTri (κ := F) b, (∀ i j, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠
      (1 : Matrix (Fin r) (Fin r) F) i j → b i = b j ∧ i ∈ S ∧ j ∉ S) → T ∘ₗ σ u = T) : T = 0 := by
  classical
  let c : Fin r → ℕ := fun k => if k ∈ S then 0 else 1
  let U : Subgroup (blockTri (κ := F) b) :=
    (levi F b ⊓ GlobalTheory.FiniteGL.unipRadical F c).subgroupOf (blockTri b)
  have hU : ∀ u : blockTri (κ := F) b, u ∈ U ↔ ∀ i j, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠
      (1 : Matrix (Fin r) (Fin r) F) i j → b i = b j ∧ i ∈ S ∧ j ∉ S := by
    intro u
    simp only [U, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_levi, GlobalTheory.FiniteGL.mem_unipRadical,
      Matrix.sub_apply, sub_eq_zero]
    constructor
    · rintro ⟨h1, h2⟩ i j hne
      refine ⟨?_, ?_⟩
      · by_contra h
        exact hne (by rw [h1 i j h, Matrix.one_apply_ne (fun e => h (congrArg b e))])
      · by_contra h
        refine hne (h2 i j ?_)
        by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> simp_all [c]
    · intro h
      refine ⟨fun i j hij => ?_, fun i j hij => ?_⟩
      · by_contra h0
        exact hij (h i j (by rwa [Matrix.one_apply_ne (fun e => hij (congrArg b e))])).1
      · by_contra h0
        obtain ⟨-, hi, hj⟩ := h i j h0
        simp [c, hi, hj] at hij
  letI := Fintype.ofFinite U
  have hc : (Fintype.card U : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  ext v
  have h0 : ∑ u : U, σ u v = 0 := by
    refine hσ.cusp S hS _ fun n hn => ?_
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨n, (hU n).2 hn⟩ : U)) _ _ fun u => by simp
  have h1 := congrArg T h0
  have h2 : ∀ u : U, T (σ u v) = T v := fun u => LinearMap.congr_fun (hT u ((hU u).1 u.2)) v
  rw [map_sum, map_zero, Finset.sum_congr rfl fun u _ => h2 u, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ] at h1
  exact (smul_eq_zero.1 h1).resolve_left hc

theorem mem_blockTri_of_ne {b : Fin r → ℕ} {g : GL (Fin r) F}
    (h : ∀ i j, (g : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → b i < b j) :
    g ∈ blockTri (κ := F) b := by
  refine mem_blockTri.2 fun i j hij => ?_
  by_contra h0
  have := h i j (by rwa [Matrix.one_apply_ne (fun e => by rw [e] at hij; exact lt_irrefl _ hij)])
  omega

theorem blocks_match : ∀ (F : Type) [Field F] [Finite F] (r : ℕ) (b b' : Fin r → ℕ) (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (σ : Representation ℂ (blockTri (κ := F) b) V) (σ' : Representation ℂ (blockTri (κ := F) b') V'), IsCuspDatum b σ → IsCuspDatum b' σ' → ∀ (w : Equiv.Perm (Fin r)) (T : V →ₗ[ℂ] V'), T ≠ 0 → (∀ (p : blockTri (κ := F) b) (p' : blockTri (κ := F) b'), (p' : GL (Fin r) F) * permGL F w = permGL F w * (p : GL (Fin r) F) → σ' p' ∘ₗ T = T ∘ₗ σ p) → ∀ i j : Fin r, b i = b j ↔ b' (w i) = b' (w j) := by
  intro F _ _ r b b' V V' _ _ _ _ σ σ' hσ hσ' w T hT hint
  have hone : ∀ k l : Fin r, (1 : Matrix (Fin r) (Fin r) F) (w k) (w l) = (1 : Matrix (Fin r) (Fin r) F) k l := by
    intro k l
    simp [Matrix.one_apply]
  have A : ∀ i j, b i = b j → ¬ b' (w i) < b' (w j) := by
    intro i j hij hlt
    refine hT (eq_zero_of_invariant hσ (Finset.univ.filter fun k => b' (w k) ≤ b' (w i))
      ⟨i, j, hij, by simp, by simpa using hlt⟩ T fun u hu => ?_)
    have key : ∀ k l, ((permGL F w * u * (permGL F w)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l ≠
        (1 : Matrix (Fin r) (Fin r) F) k l → b' k < b' l := by
      intro k l
      obtain ⟨k, rfl⟩ := w.surjective k
      obtain ⟨l, rfl⟩ := w.surjective l
      rw [conj_permGL_apply, hone]
      intro h
      obtain ⟨-, h1, h2⟩ := hu k l h
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      omega
    have h1 := hint u ⟨_, mem_blockTri_of_ne key⟩ (by simp)
    rw [hσ'.infl ⟨_, mem_blockTri_of_ne key⟩ fun k l hkl => by
      by_contra h0
      have := key k l h0
      omega] at h1
    exact h1.symm
  have B : ∀ i j, b' (w i) = b' (w j) → ¬ b i < b j := by
    intro i j hij hlt
    apply hT
    ext v
    refine hσ'.cusp (Finset.univ.filter fun k => b (w.symm k) ≤ b i)
      ⟨w i, w j, hij, by simp, by simpa using hlt⟩ (T v) fun u hu => ?_
    have key : ∀ k l, (((permGL F w)⁻¹ * u * permGL F w : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k l ≠
        (1 : Matrix (Fin r) (Fin r) F) k l → b k < b l := by
      intro k l
      rw [← conj_permGL_apply w, ← hone]
      intro h
      obtain ⟨-, h1, h2⟩ := hu (w k) (w l) (by simpa [mul_assoc] using h)
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] at h1 h2
      omega
    have h1 := hint ⟨_, mem_blockTri_of_ne key⟩ u (by simp [mul_assoc])
    rw [hσ.infl ⟨_, mem_blockTri_of_ne key⟩ fun k l hkl => by
      by_contra h0
      have := key k l h0
      omega] at h1
    exact LinearMap.congr_fun h1 v
  intro i j
  constructor
  · intro h
    have := A i j h
    have := A j i h.symm
    omega
  · intro h
    have := B i j h
    have := B j i h.symm
    omega

end GlobalTheory.FinGL.BlockMatch
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DGamCoprime
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.DGamCoprime

theorem two_f_N_le (R : Ranks) (h : R.f * R.m ≤ R.k) : 2 * R.f * R.N R.m ≤ 4 * R.t * R.r := by
  have h1 : R.f ≤ R.k := R.f_le_k
  have h2 := R.two_le_m
  have h3 := R.rank_add_five_le
  have h4 : R.k ≤ R.r := by unfold Ranks.r; omega
  have h5 : R.k + 1 ≤ R.t := by omega
  unfold Ranks.N
  have e : 2 * R.f * (R.k + R.m * (R.t + 1)) = 2 * (R.f * R.k) + 2 * ((R.f * R.m) * (R.t + 1)) := by ring
  have a1 : R.f * R.k ≤ R.k * R.k := Nat.mul_le_mul_right _ h1
  have a2 : (R.f * R.m) * (R.t + 1) ≤ R.k * (R.t + 1) := Nat.mul_le_mul_right _ h
  have a3 : R.k * (R.k + 1) ≤ R.k * R.t := Nat.mul_le_mul_left _ h5
  have a4 : R.t * R.k ≤ R.t * R.r := Nat.mul_le_mul_left _ h4
  rw [e]
  nlinarith

variable {D : D7} (L : SizeData₂ D)

theorem one_le_L : 1 ≤ L.sc.L := Real.one_le_rpow L.sc.one_lt_alt.le L.sc.eps_pos.le

theorem one_le_b : 1 ≤ L.sc.b := Real.one_le_exp (by linarith [one_le_L L])

theorem f_mul_m_le (h : SizeKRel L) : D.R.f * D.R.m ≤ D.R.k := by
  have h1 := h.1
  have hx := L.sc.one_lt_alt.le
  have he := L.sc.eps_pos
  have a1 : 1 ≤ L.sc.x ^ szTh L := Real.one_le_rpow hx (by unfold szTh; positivity)
  have a2 : 1 ≤ L.sc.x ^ L.sc.eps := Real.one_le_rpow hx he.le
  have a3 := one_le_L L
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (le_trans (by norm_num) D.R.two_le_m)
  have a4 : (D.R.m : ℝ) ≤ (D.R.m : ℝ) ^ 5 := le_self_pow₀ hm (by norm_num)
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have key : (1 : ℝ) * D.R.m * D.R.f * 1 * 1 ≤
      L.sc.x ^ szTh L * (D.R.m : ℝ) ^ 5 * D.R.f * L.sc.L * L.sc.x ^ L.sc.eps := by
    gcongr
  have : ((D.R.f * D.R.m : ℕ) : ℝ) ≤ D.R.k := by push_cast; linarith
  exact_mod_cast this

theorem q_le_sqrt_b (h : SizeCond L) (hd : 0 < D.host.d) (hq : 0 < D.host.q) :
    (D.host.q : ℝ) ≤ Real.sqrt L.sc.b := by
  unfold SizeCond at h
  have hd' : (1 : ℝ) ≤ D.host.d := by exact_mod_cast hd
  have hq' : (1 : ℝ) ≤ D.host.q := by exact_mod_cast hq
  have ht : (1 : ℝ) ≤ D.R.t := by
    have := D.R.three_m_lt_t
    exact_mod_cast (show 1 ≤ D.R.t by omega)
  have c1 : (D.host.q : ℝ) ≤ szCond L := by
    unfold szCond
    calc (D.host.q : ℝ) = 1 * D.host.q * 1 := by ring
      _ ≤ (D.host.QS : ℝ) * D.host.q * D.host.d := by gcongr; exact_mod_cast D.host.QS_pos
  have c2 : szCond L ≤ szCond L ^ 36 := le_self_pow₀ (hq'.trans c1) (by norm_num)
  have c3 : (1 : ℝ) ≤ (D.R.t : ℝ) ^ 150 := one_le_pow₀ ht
  have c4 : 0 ≤ szCond L ^ 36 := by linarith
  nlinarith

theorem primes_gt (hS : SizesAt L) (hT : L.TuGe) :
    (∀ u, 2 * D.R.f * D.R.N D.R.m + 1 < (D.mem u).A.T) ∧
    (∀ a, 2 * D.R.f * D.R.N D.R.m + 1 < D.host.g a) ∧
    2 * D.R.f * D.R.N D.R.m + 1 < D.host.q ∧ 2 * D.R.f * D.R.N D.R.m + 1 < D.host.d := by
  obtain ⟨-, -, -, hK, -, hC, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hG, -⟩ := hS
  have h0 := two_f_N_le D.R (f_mul_m_le L hK)
  obtain ⟨hq, hd⟩ := D.host.qd_big
  have hq' : 2 * D.R.f * D.R.N D.R.m + 1 < D.host.q := by omega
  have hd' : 2 * D.R.f * D.R.N D.R.m + 1 < D.host.d := by omega
  have hs := q_le_sqrt_b L hC (by omega) (by omega)
  have hb := one_le_b L
  have hsb : Real.sqrt L.sc.b ≤ L.sc.b := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hqb : (D.host.q : ℝ) ≤ L.sc.b := hs.trans hsb
  refine ⟨fun u => ?_, fun a => ?_, hq', hd'⟩
  · have hm : (2 : ℝ) ≤ D.R.m := by exact_mod_cast D.R.two_le_m
    have h1 : L.sc.b ^ (1 : ℝ) ≤ L.sc.b ^ ((D.R.m : ℝ) / 2) :=
      Real.rpow_le_rpow_of_exponent_le hb (by linarith)
    rw [Real.rpow_one] at h1
    have : (D.host.q : ℝ) ≤ ((D.mem u).A.T : ℝ) := hqb.trans (h1.trans (hT u))
    have : D.host.q ≤ (D.mem u).A.T := by exact_mod_cast this
    omega
  · have hk : (1 : ℝ) ≤ D.R.k := by
      have := D.R.m_add_three_le_k
      exact_mod_cast (show 1 ≤ D.R.k by omega)
    have h1 : L.sc.b ≤ (D.R.k : ℝ) * L.sc.b := by nlinarith
    have h2 : (D.R.k : ℝ) * L.sc.b ≤ ((D.R.k : ℝ) * L.sc.b) ^ 8 := le_self_pow₀ (hb.trans h1) (by norm_num)
    have : (D.host.q : ℝ) ≤ (D.host.g a : ℝ) := hqb.trans (h1.trans (h2.trans (hG a a).1))
    have : D.host.q ≤ D.host.g a := by exact_mod_cast this
    omega

end GlobalTheory.DGamCoprime
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DcOpCommOfCommute
section
noncomputable section

open Formalism.IndefR.Bridge Formalism.L2.Col

namespace GlobalTheory.HeckeParts

section Grp

variable {G : Type} [Group G] {J Q L : Subgroup G}

def Splits (Q J L : Subgroup G) : Prop :=
  ∀ κ ∈ Q, ∃ k₁ ∈ J, ∃ k₂, k₁ ∈ L ∧ κ = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l

def RInv (J : Subgroup G) (F : G → ℂ) : Prop := ∀ k ∈ J, ∀ h, F (h * k) = F h

theorem Splits.self (h : Splits Q J L) (hJ : J ≤ Q) :
    ∀ k ∈ J, ∃ k₁ ∈ J, ∃ k₂ ∈ J, k₁ ∈ L ∧ k = k₁ * k₂ ∧ ∀ l ∈ L, Commute k₂ l := by
  intro k hk
  obtain ⟨k₁, h₁, k₂, hL, e, hc⟩ := h k (hJ hk)
  refine ⟨k₁, h₁, k₂, ?_, hL, e, hc⟩
  have : k₂ = k₁⁻¹ * k := by rw [e]; group
  rw [this]
  exact J.mul_mem (J.inv_mem h₁) hk

theorem RInv.one {F : G → ℂ} (h : RInv J F) (k : J) (g : G) : F (g * k) = (((1 : J →* ℂˣ) k : ℂˣ) : ℂ) • F g := by
  simp [h k k.2 g]

theorem isDC_of_splits (hs : Splits Q J L) (hJ : J ≤ Q) {x : G} (hx : x ∈ L) {A : Finset G} (hA : ∀ a ∈ A, a ∈ L)
    {K : Set G} (hK : ∀ g, g ∈ K ↔ g ∈ J ∧ g ∈ L) (h1 : ∀ γ ∈ A, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * x * k₂)
    (h2 : ∀ y, (∃ k₁ ∈ K, ∃ k₂ ∈ K, y = k₁ * x * k₂) → ∃! γ, γ ∈ A ∧ γ⁻¹ * y ∈ K) : IsDC J x A := by
  refine ⟨fun a ha => ?_, ?_⟩
  · obtain ⟨k₁, h₁, k₂, h₂, e⟩ := h1 a ha
    exact ⟨⟨k₁, ((hK _).1 h₁).1⟩, ⟨k₂, ((hK _).1 h₂).1⟩, e⟩
  · rintro g ⟨k, k', rfl⟩
    obtain ⟨k₁, h₁, k₂, h₂, hL, e, hc⟩ := hs.self hJ k k.2
    have key : ∀ a : G, a⁻¹ * ((k : G) * x * k') = a⁻¹ * (k₁ * x * 1) * (k₂ * k') := by
      intro a
      rw [e, mul_assoc k₁ k₂ x, (hc x hx).eq]; group
    have hm : k₂ * (k' : G) ∈ J := J.mul_mem h₂ k'.2
    refine (existsUnique_congr fun a => and_congr_right fun ha => ?_).1
      (h2 _ ⟨k₁, (hK _).2 ⟨h₁, hL⟩, 1, (hK _).2 ⟨J.one_mem, L.one_mem⟩, rfl⟩)
    rw [key, J.mul_mem_cancel_right hm, hK]
    exact and_iff_left (L.mul_mem (L.inv_mem (hA a ha)) (L.mul_mem (L.mul_mem hL hx) L.one_mem))

theorem dcOp_eq_rInv {x x' : G} {A A' : Finset G} (hA : IsDC J x A) (hA' : IsDC J x' A')
    (hx : ∃ k₁ k₂ : J, x' = (k₁ : G) * x * k₂) {F : G → ℂ} (hF : RInv J F) :
    dcOp A F = dcOp A' F ∧ RInv J (dcOp A F) := by
  have := GlobalTheory.HkB.dcOp_eq_and_level J ⊤ 1 x x' A A' F
    (fun k hk => ⟨k, hk, 1, J.one_mem, trivial, (mul_one k).symm, fun l _ => Commute.one_left l⟩)
    (fun _ _ => rfl) (fun _ _ => trivial) (fun _ _ => trivial) hA hA' hx hF.one
  exact ⟨this.1, fun k hk h => by simpa using this.2 ⟨k, hk⟩ h⟩

theorem dcOp_rInv {x : G} {A : Finset G} (hA : IsDC J x A) {F : G → ℂ} (hF : RInv J F) : RInv J (dcOp A F) :=
  (dcOp_eq_rInv hA hA ⟨1, 1, by simp⟩ hF).2

theorem dcOp_translate (hs : Splits Q J L) {x : G} {A : Finset G} (hA : IsDC J x A) (hL : ∀ a ∈ A, a ∈ L)
    {F : G → ℂ} (hF : RInv J F) {κ : G} (hκ : κ ∈ Q) (h : G) :
    dcOp A F (h * κ) = dcOp A (fun g => F (g * κ)) h := by
  obtain ⟨k₁, h₁, k₂, hl, rfl, hc⟩ := hs κ hκ
  rw [← (hc k₁ hl).eq, ← mul_assoc, dcOp_rInv hA hF k₁ h₁]
  refine Finset.sum_congr rfl fun a ha => ?_
  show F (h * k₂ * a) = F (h * a * (k₂ * k₁))
  rw [← mul_assoc, hF k₁ h₁, mul_assoc, (hc a (hL a ha)).eq, mul_assoc]

theorem dcOp_comm_of_commute {A B : Finset G} (h : ∀ a ∈ A, ∀ b ∈ B, Commute a b) (F : G → ℂ) :
    dcOp A (dcOp B F) = dcOp B (dcOp A F) := by
  funext g
  simp only [dcOp]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
  rw [mul_assoc, (h a ha b hb).eq, mul_assoc]

end Grp

section Normal

variable {E I : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem exists_lift {X : Type} [AddCommGroup X] [Module ℂ X] {e : E →ₗ[ℂ] X} (he : Function.Injective e)
    (T : X →ₗ[ℂ] X) (hT : ∀ x, T (e x) ∈ LinearMap.range e) : ∃ t : Module.End ℂ E, ∀ x, e (t x) = T (e x) := by
  choose f hf using hT
  exact ⟨⟨⟨f, fun x y => he (by rw [map_add, hf, hf, hf, map_add, map_add])⟩,
    fun a x => he (by rw [RingHom.id_apply, map_smul, hf, hf, map_smul, map_smul])⟩, hf⟩

end Normal

end GlobalTheory.HeckeParts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamCrystalTwoReductionsAgreeFiltrationStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deRham_crystal_two_reductions_agree : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    ∀ (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A₁ : Over (Sp R₁)) [GrpObj A₁] (A : Over (Sp R)) [GrpObj A]
      (i₁ : A₀.left ⟶ A₁.left) (i₂ : A₁.left ⟶ A.left) (i : A₀.left ⟶ A.left)
      (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁) (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i),
      i₁ ≫ i₂ = i → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∃ N : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁,
      Function.Bijective (N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀) ∧
      ∀ d : Crys κ (spMap π) A₀, crysToDR κ h d = crysToDR (divided₂ hJ) h₂ ((N.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  first | exact @GlobalTheory.SqLift.crys_two_reductions | exact GlobalTheory.SqLift.crys_two_reductions | (intros; apply GlobalTheory.SqLift.crys_two_reductions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreePartIntegralDifferentialOfCoboundaryStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degree_part_integralDifferential_of_coboundary : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [CharP k p] [PerfectRing k p] (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k), IsLaw μ → ∀ (N : ℕ) (g h : MvPowerSeries (Fin d) (Fr p k)), 2 ≤ N → g ∈ quasiInt p k (Fin d) → (∀ α : Fin d →₀ ℕ, α.degree < N → coeff α h = 0) → (∀ γ : Fin d ⊕ Fin d →₀ ℕ, γ.degree = N → ∃ w : WittVector p k, coeff γ (cob1 (fun i => Katz.lift p (μ i)) (g + h)) = algebraMap (WittVector p k) (Fr p k) w) → ∀ (α : Fin d →₀ ℕ) (i : Fin d), α.degree = N → ∃ w : WittVector p k, (α i : Fr p k) * coeff α h = algebraMap (WittVector p k) (Fr p k) w := by
  first | exact @GlobalTheory.Katz.WDer.main | exact GlobalTheory.Katz.WDer.main | (intros; apply GlobalTheory.Katz.WDer.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDividedPowerFiltrationSuccLeStatement
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivation_dividedPowerFiltration_succ_le : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module B M] [Module R M] [IsScalarTower R B M] (J : Ideal B) (δ : DividedPowers J) (D : Derivation R B M) (N₀ : Submodule B M), (∀ n, ∀ a ∈ J, D (δ.dpow (n + 1) a) - δ.dpow n a • D a ∈ N₀) → ∀ N, ∀ x ∈ fil δ (N + 1), D x ∈ fil δ N • (⊤ : Submodule B M) ⊔ N₀ := by
  first | exact @GlobalTheory.DerFil.deriv_fil_succ_le | exact GlobalTheory.DerFil.deriv_fil_succ_le | (intros; apply GlobalTheory.DerFil.deriv_fil_succ_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltrationIdealLeMapOfIsDPMorphismStatement
section
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dividedPowerFiltrationIdeal_le_map_of_isDPMorphism : ∀ (B : Type) [CommRing B] (J : Ideal B) (δ : DividedPowers J) (C : Type) [CommRing C] (J' : Ideal C) (δ' : DividedPowers J') (f : B →+* C), IsDPMorphism δ δ' f → J' = J.map f → ∀ N, fil δ' N ≤ (fil δ N).map f := by
  first | exact @GlobalTheory.PDA.fil_le_map_fil | exact GlobalTheory.PDA.fil_le_map_fil | (intros; apply GlobalTheory.PDA.fil_le_map_fil <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLieExistsAdditiveEvalModPrimePow
section
noncomputable section

open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory

theorem PDivGroup.dual_lie_exists_eval_mod_pow : ∀ (p : ℕ) (O : Type) [CommRing O]
    (G : PDivGroup p O) (l : G.dual.Lie) (n : ℕ), ∃ (b : G.A n) (z : G.A n ⊗[O] G.A n),
    cobOne O (G.A n) b = (p : O) ^ n • z ∧ ∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)),
    dUnit O φ = w.1 n → (p : O) ^ n ∣ l w - φ b := by
  intro p O _ G l n
  let I : Ideal O := Ideal.span {(p : O) ^ n}
  let N : Submodule O G.dual.omega := Ideal.span {(p : O)} ^ n • ⊤
  let m : G.dual.omega →ₗ[O] O ⧸ I := (Ideal.Quotient.mkₐ O I).toLinearMap ∘ₗ l
  have hN : N ≤ LinearMap.ker m := by
    intro x hx
    have hx' : x ∈ (Ideal.span {(p : O)} ^ n • ⊤ : Submodule O G.dual.omega) := hx
    rw [Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul,
      Submodule.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨v, -, rfl⟩ := hx'
    rw [LinearMap.mem_ker]
    change Ideal.Quotient.mk I (l ((p : O) ^ n • v)) = 0
    rw [map_smul, smul_eq_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  let u : Cot O (CartierDual O (G.A n)) →ₗ[O] O ⧸ I :=
    N.liftQ m hN ∘ₗ (G.dual.omegaQuotEquiv n).symm.toLinearMap
  have hu : ∀ w : G.dual.omega, u (w.1 n) = Ideal.Quotient.mk I (l w) := by
    intro w
    have h := (G.dual.omegaQuotEquiv_mk n w)
    change N.liftQ m hN ((G.dual.omegaQuotEquiv n).symm (w.1 n)) = _
    rw [← h, LinearEquiv.symm_apply_apply]
    rfl
  obtain ⟨b, z, hb, hφ⟩ := GlobalTheory.T.cartierDual_tangent_mod_eq_eval_additive O (G.A n) ((p : O) ^ n) u
  refine ⟨b, z, hb, fun w φ hφw => ?_⟩
  have h1 := hφ φ
  rw [hφw, hu, Ideal.Quotient.eq] at h1
  exact Ideal.mem_span_singleton.1 h1

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLeviProjectionDenominatorsOfHypothesesStatement
section
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualWeylLeviProjectionDenominators_of_hypotheses : GlobalTheory.LeviCut.ResLat → GlobalTheory.LeviCut.ResHw → GlobalTheory.LeviCut.ResDer → GlobalTheory.LeviCut.LeviProj := by
  first | exact @GlobalTheory.LeviCut.leviProj_of | exact GlobalTheory.LeviCut.leviProj_of | (intros; apply GlobalTheory.LeviCut.leviProj_of <;> assumption)
end

