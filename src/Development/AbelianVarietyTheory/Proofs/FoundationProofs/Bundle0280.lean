import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0233
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0271
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryTransvectionMovesLatticeAtPrime

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

def sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (by intro a b c; simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum, mul_div_assoc])
    (by intro a b c; simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (starRingEnd ℂ c), ← Finset.mul_sum,
        mul_div_assoc])

theorem isHerm_sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : IsHerm (sesqOf D T N N') := by
  intro x y
  change Hf D T y x = starRingEnd ℂ (Hf D T x y)
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

theorem lam_mul_mem (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

theorem klat_gen {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    ∃ S : Set (Matrix (Fin N') (Fin N) D.host.E), Submodule.span D.host.K S = ⊤ ∧
      A = AddSubgroup.closure {z | ∃ w ∈ lamOf D cc δ, ∃ B ∈ S, z = w • embV D (tor0 D cc δ) B} := by
  rcases hA with ⟨r, b, hb, rfl⟩ | ⟨L, L', hL, hL', rfl⟩
  · refine ⟨Set.range b, hb.2, ?_⟩
    unfold LaB
    congr 1
    ext z
    simp [tor0]
  · refine ⟨YYl D L L', ?_, rfl⟩
    obtain ⟨r, y, y', hy, -, h⟩ := GlobalTheory.HomDual.exists_dual_family_hom D (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
    rw [eq_top_iff]
    intro x _
    rw [h x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hy i))

theorem klat_smul_mem {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) (a : 𝓞 D.host.K)
    {x : VC D N N'} (hx : x ∈ A) : D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ A := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, lam_mul_mem a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

theorem embV_smul (h : GL3Theta.InducedCMType D) (k : D.host.K) (B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (k • B) = D.host.φ₀ (k : D.host.E) • embV D (tor0 D cc δ) B := by
  funext τ i j
  change embT D τ ((k : D.host.E) * B i j) = D.host.φ₀ (k : D.host.E) * embT D τ (B i j)
  rw [map_mul, h τ k]

theorem embV_add (B B' : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (B + B') = embV D (tor0 D cc δ) B + embV D (tor0 D cc δ) B' := by
  funext τ i j
  exact map_add (embT D τ) _ _

theorem embV_zero : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  exact map_zero (embT D τ)

theorem klat_rat (h : GL3Theta.InducedCMType D) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A)
    {x : VC D N N'} (hx : x ∈ A) : ∃ B, x = δ • embV D (tor0 D cc δ) B := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  have hl : ∀ w ∈ lamOf D cc δ, ∃ k : D.host.K, w = δ * D.host.φ₀ (k : D.host.E) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw => obtain ⟨c, -, rfl⟩ := hw; exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨k, rfl⟩ := ha
      obtain ⟨k', rfl⟩ := hb
      exact ⟨k + k', by simp [mul_add]⟩
    | neg a _ ha =>
      obtain ⟨k, rfl⟩ := ha
      exact ⟨-k, by simp⟩
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, -, rfl⟩ := hw
    obtain ⟨k, rfl⟩ := hl w hw
    exact ⟨k • B, by rw [embV_smul h, smul_smul]⟩
  | zero => exact ⟨0, by rw [embV_zero, smul_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨B', rfl⟩ := hb
    exact ⟨B + B', by rw [embV_add, smul_add]⟩
  | neg a _ ha =>
    obtain ⟨B, rfl⟩ := ha
    exact ⟨(-1 : D.host.K) • B, by rw [embV_smul h]; simp⟩

theorem klat_mul_mem (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A : AddSubgroup (VC D N N')}
    (hA : KLat D (tor0 D cc δ) A) (B : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ m • (δ • embV D (tor0 D cc δ) B) ∈ A := by
  have hA' := hA
  obtain ⟨S, hS, hAS⟩ := klat_gen hA'
  have hB : B ∈ Submodule.span D.host.K S := hS ▸ Submodule.mem_top
  induction hB using Submodule.span_induction with
  | mem B hB =>
    refine ⟨Ideal.absNorm cc, Nat.pos_of_ne_zero (fun e => hcc (Ideal.absNorm_eq_zero_iff.1 e)), ?_⟩
    rw [hAS]
    refine AddSubgroup.subset_closure ⟨(Ideal.absNorm cc : ℂ) * δ,
      AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp [mul_comm]⟩, B, hB, ?_⟩
    rw [← smul_smul, Nat.cast_smul_eq_nsmul]
  | zero => exact ⟨1, one_pos, by simp [embV_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm, ha⟩ := ha
    obtain ⟨n, hn, hb⟩ := hb
    refine ⟨m * n, by positivity, ?_⟩
    rw [embV_add, smul_add, smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.nsmul_mem ha _
    · rw [mul_smul]; exact A.nsmul_mem hb _
  | smul k B _ hB =>
    obtain ⟨m, hm, hB⟩ := hB
    obtain ⟨n, hn, hk⟩ := exists_integral_multiples ℤ ℚ ({k} : Finset D.host.K)
    have hk' : IsIntegral ℤ (n.natAbs • k) := by
      have := hk k (Finset.mem_singleton_self k)
      rcases Int.natAbs_eq n with e | e
      · rw [e] at this; simpa using this
      · rw [e] at this; simpa using this.neg
    refine ⟨m * n.natAbs, Nat.mul_pos hm (Int.natAbs_pos.2 hn), ?_⟩
    convert klat_smul_mem hA ⟨_, hk'⟩ hB using 1
    rw [embV_smul h]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    change _ = D.host.φ₀ ((n.natAbs • k : D.host.K) : D.host.E) * _
    simp
    ring

theorem klat_finite (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A₁ A₂ : AddSubgroup (VC D N N')}
    (h₁ : KLat D (tor0 D cc δ) A₁) (h₂ : KLat D (tor0 D cc δ) A₂) (hfg : A₂.FG) :
    Finite (A₂ ⧸ A₁.addSubgroupOf A₂) :=
  finite_quot hfg fun x hx => by
    obtain ⟨B, rfl⟩ := klat_rat h h₂ hx
    exact klat_mul_mem h hcc h₁ B

theorem klat_facts (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ IsSelfDual (sesqOf D (tor0 D cc δ) N N') A ∧
      IsSemiChar (sesqOf D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) := by
  obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h3, h4, le_antisymm h2 h1, ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  refine isSemiChar_round (isHerm_sesqOf D _ N N') (Real.sqrt D.host.d) h1 (fun x hx => ?_) h5
  have := klat_smul_mem hA a hx
  rwa [ha] at this

end GlobalTheory.ThetaInter

open GlobalTheory.ThetaInter in

theorem GlobalTheory.theta_translation_intertwiner_unitary : ∀ D : D7, IntertwinerUnitary D := by
  intro D cc δ hc N N' A₁ A₂ h₁ h₂ th hth
  obtain ⟨f₁, s₁, d₁, c₁⟩ := klat_facts hc h₁
  obtain ⟨f₂, s₂, d₂, c₂⟩ := klat_facts hc h₂
  have hH := isHerm_sesqOf D (tor0 D cc δ) N N'
  have hψ := (GlobalTheory.InducedType.induced_type D).1.1
  have := klat_finite hψ hc.1.1 h₁ h₂ f₂
  have := klat_finite hψ hc.1.1 h₂ h₁ f₁
  have : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual hH d₁ f₁
  have t₂ := discrete_of_selfDual hH d₂ f₂
  have hF : th ∈ Formalism.L2.Th1.H.fixedBy (sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A₁ := hth.2
  exact ⟨fun x => mean_opU MeasureTheory.volume hH t₁ s₁ c₁ hth.1.continuous hF x,
    ⟨differentiable_inter (H := sesqOf D (tor0 D cc δ) N N') (α := al D (tor0 D cc δ)) A₁ A₂ hth.1,
      inter_mem_fixedBy hH c₁ d₂ c₂ hF⟩,
    mean_inter MeasureTheory.volume hH t₁ s₁ t₂ s₂ d₁ c₁ d₂ c₂ hth.1 hF,
    inter_inter hH d₁ d₂ c₁ hF⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTripleDataOfNeighbourTriple
section
noncomputable section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

namespace GlobalTheory.TriangleColumns

def IL (D : D7) (cc : Ideal (𝓞 D.host.K)) {n : ℕ} (L : Lat D n) : Lat D n :=
  Submodule.span (𝓞 D.host.E) {v | ∃ t ∈ Iid D cc, ∃ y ∈ L, v = t • y}

theorem smul_mem_IL {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L : Lat D n} {t : D.host.E}
    (ht : t ∈ Iid D cc) {y : Fin n → D.host.E} (hy : y ∈ L) : t • y ∈ IL D cc L :=
  Submodule.subset_span ⟨t, ht, y, hy, rfl⟩

theorem IL_mono {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L L' : Lat D n} (h : L ≤ L') :
    IL D cc L ≤ IL D cc L' :=
  Submodule.span_mono fun _ ⟨t, ht, y, hy, e⟩ => ⟨t, ht, y, h hy, e⟩

theorem hE_osmul_left (D : D7) {n : ℕ} (a : 𝓞 D.host.E) (x y : Fin n → D.host.E) :
    hE D (a • x) y = a • hE D x y := by
  rw [← algebraMap_smul D.host.E a x, hE_smul_left, Algebra.smul_def]

theorem pair_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {L : Lat D n} {v w : Fin n → D.host.E}
    (hw : ∀ y ∈ L, IntE D (hE D y w)) (hv : v ∈ IL D cc L) : hE D v w ∈ Iid D cc := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    obtain ⟨o, ho⟩ := hw y hy
    rw [hE_smul_left, ← ho, mul_comm, ← Algebra.smul_def]
    exact Submodule.smul_mem _ _ ht
  | zero => simp [hE]
  | add u v _ _ hu hv => rw [hE_add_left]; exact add_mem hu hv
  | smul a v _ hv => rw [hE_osmul_left]; exact Submodule.smul_mem _ _ hv

theorem sd_int {D : D7} {n : ℕ} {L : Lat D n} (h : SD D L) {y w : Fin n → D.host.E} (hy : y ∈ L) (hw : w ∈ L) :
    IntE D (hE D y w) := (((sd_iff D L).1 h).2.2 y).1 hy w hw

theorem smul_mem_IL_of_P {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {M : Lat D n} {P : Ideal (𝓞 D.host.E)}
    {b : Fin n → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t : D.host.E} (ht : t ∈ P • Iid D cc) :
    t • b ∈ IL D cc M := by
  refine Submodule.smul_induction_on ht (fun p hp s hs => ?_) (fun u v hu hv => ?_)
  · have : (p • s) • b = s • (p • b) := by rw [smul_assoc, smul_comm]
    rw [this]; exact smul_mem_IL hs (hb p hp)
  · rw [add_smul]; exact add_mem hu hv

theorem decomp {D : D7} {cc : Ideal (𝓞 D.host.K)} {n : ℕ} {M : Lat D n} {P : Ideal (𝓞 D.host.E)}
    {b : Fin n → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) {v : Fin n → D.host.E}
    (hv : v ∈ IL D cc (M ⊔ Submodule.span (𝓞 D.host.E) {b})) :
    ∃ a : 𝓞 D.host.E, v - (a • t₀) • b ∈ IL D cc M := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨t, ht, y, hy, rfl⟩ := hv
    obtain ⟨m, hm, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 hz
    obtain ⟨a, ha⟩ := hg (o • t) (Submodule.smul_mem _ _ ht)
    refine ⟨a, ?_⟩
    have : t • (m + o • b) - (a • t₀) • b = t • m + (o • t - a • t₀) • b := by
      rw [smul_add, sub_smul, smul_assoc o t b, smul_comm o t b]; abel
    rw [this]
    exact add_mem (smul_mem_IL ht hm) (smul_mem_IL_of_P hb ha)
  | zero => exact ⟨0, by simp⟩
  | add u v _ _ hu hv =>
    obtain ⟨a, ha⟩ := hu
    obtain ⟨a', ha'⟩ := hv
    refine ⟨a + a', ?_⟩
    have : u + v - ((a + a') • t₀) • b = (u - (a • t₀) • b) + (v - (a' • t₀) • b) := by
      rw [add_smul, add_smul]; abel
    rw [this]; exact add_mem ha ha'
  | smul c v _ hv =>
    obtain ⟨a, ha⟩ := hv
    refine ⟨c * a, ?_⟩
    have : c • v - ((c * a) • t₀) • b = c • (v - (a • t₀) • b) := by
      rw [smul_sub, mul_smul, smul_assoc c]
    rw [this]; exact Submodule.smul_mem _ _ ha

def mat (D : D7) {N N' : ℕ} (t₀ : D.host.E) (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    Matrix (Fin N') (Fin N) D.host.E := fun i j => (a j • t₀) * b i

theorem pt_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z : Matrix (Fin N') (Fin N) D.host.E)
    (τ : D.what₂.Tau) (i : Fin N') (j : Fin N) : pt D (tor0 D cc δ) δ z τ i j = δ * embT D τ (z i j) := rfl

theorem pt_sub (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z - pt D (tor0 D cc δ) δ w = pt D (tor0 D cc δ) δ (z - w) := by
  funext τ i j
  simp only [Pi.sub_apply, pt_apply, Matrix.sub_apply, map_sub, mul_sub]

theorem pt_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N N' : ℕ} (z w : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z + pt D (tor0 D cc δ) δ w = pt D (tor0 D cc δ) δ (z + w) := by
  funext τ i j
  simp only [Pi.add_apply, pt_apply, Matrix.add_apply, map_add, mul_add]

def ptH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E) (b : Fin N' → D.host.E) :
    (Fin N → 𝓞 D.host.E) →+ VC D N N' :=
  AddMonoidHom.mk' (fun a => pt D (tor0 D cc δ) δ (mat D t₀ b a)) fun a a' => by
    rw [pt_add]; congr 1; funext i j
    simp only [mat, Pi.add_apply, Matrix.add_apply, add_smul, add_mul]

theorem ptH_apply (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a = pt D (tor0 D cc δ) δ (mat D t₀ b a) := rfl

def phiH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) {N' : ℕ} (t₀ : D.host.E) (b x : Fin N' → D.host.E) :
    𝓞 D.host.E →+ ℂ :=
  AddMonoidHom.mk' (fun s => (∑ τ, ∑ i, embT D τ (s : D.host.E) *
      (δ * embT D τ (t₀ * x i) * (starRingEnd ℂ) (δ * embT D τ (t₀ * b i)))) / (area (tor0 D cc δ).abelian₂ : ℂ))
    fun s s' => by
      simp only [RingOfIntegers.coe_eq_algebraMap, map_add, add_mul, Finset.sum_add_distrib, add_div]

theorem Hf_ptH (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b x : Fin N' → D.host.E) (c c' : Fin N → 𝓞 D.host.E) :
    Hf D (tor0 D cc δ) (ptH D cc δ N t₀ x c') (ptH D cc δ N t₀ b c) =
      phiH D cc δ t₀ b x (∑ k, c' k * sgO D (c k)) := by
  have h1 : ∀ s : 𝓞 D.host.E, algebraMap (𝓞 D.host.E) D.host.E (sgO D s) =
      D.host.conj (algebraMap (𝓞 D.host.E) D.host.E s) := fun s => rfl
  rw [phiH, AddMonoidHom.mk'_apply]
  simp only [Hf, ptH_apply, pt_apply, mat, Algebra.smul_def,
    RingOfIntegers.coe_eq_algebraMap, map_sum, map_mul, h1, embT_conj, Finset.sum_mul]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

theorem pt_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} (L : Lat D N')
    (z : Matrix (Fin N') (Fin N) D.host.E) :
    pt D (tor0 D cc δ) δ z ∈ La D (tor0 D cc δ) (stdL D N) L ↔ ∀ j, (fun i => z i j) ∈ IL D cc L := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.ThetaLatImage.theta_lattice_image D cc δ hδ N N'
  rw [h2]
  constructor
  · rintro ⟨w, hw, e⟩
    rw [h1 e]; exact (h3 L w).1 hw
  · intro h
    exact ⟨z, (h3 L z).2 h, rfl⟩

theorem ptH_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} (L : Lat D N')
    (t₀ : D.host.E) (b : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a ∈ La D (tor0 D cc δ) (stdL D N) L ↔ ∀ j, (a j • t₀) • b ∈ IL D cc L :=
  pt_mem hδ L _

theorem ptH_add (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (N : ℕ) {N' : ℕ} (t₀ : D.host.E)
    (b x : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E) :
    ptH D cc δ N t₀ b a + ptH D cc δ N t₀ x a = ptH D cc δ N t₀ (b + x) a := by
  rw [ptH_apply, ptH_apply, ptH_apply, pt_add]; congr 1; funext i j
  simp only [mat, Pi.add_apply, Matrix.add_apply, mul_add]

theorem exists_sub_ptH {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (hδ : δ ≠ 0) {N N' : ℕ} {M : Lat D N'}
    {P : Ideal (𝓞 D.host.E)} {b : Fin N' → D.host.E} (hb : ∀ p ∈ P, p • b ∈ M) {t₀ : D.host.E}
    (hg : ∀ t ∈ Iid D cc, ∃ a : 𝓞 D.host.E, t - a • t₀ ∈ P • Iid D cc) {z : VC D N N'}
    (hz : z ∈ La D (tor0 D cc δ) (stdL D N) (M ⊔ Submodule.span (𝓞 D.host.E) {b})) :
    ∃ a : Fin N → 𝓞 D.host.E, ∀ L : Lat D N', M ≤ L →
      z - ptH D cc δ N t₀ b a ∈ La D (tor0 D cc δ) (stdL D N) L := by
  obtain ⟨w, -, rfl⟩ := ((GlobalTheory.ThetaLatImage.theta_lattice_image D cc δ hδ N N').2.1 _ _ z).1 hz
  choose a ha using fun j => decomp hb hg ((pt_mem hδ _ w).1 hz j)
  refine ⟨a, fun L hL => ?_⟩
  rw [ptH_apply, pt_sub, pt_mem hδ]
  exact fun j => IL_mono hL (ha j)

theorem triDat_of_tri : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), cc ≠ ⊥ → δ ≠ 0 → ∀ (N N' : ℕ) (P : Ideal (𝓞 D.host.E)), P.IsMaximal → ∀ A B C : Lat D N', Tri D P A B C → TriDat D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) A) (La D (tor0 D cc δ) (stdL D N) B) (La D (tor0 D cc δ) (stdL D N) C) P N := by
  intro D cc δ hcc hδ N N' P hP A B C ⟨hA, hB, hC, M, b, x, eA, eB, eC, hp, hbx⟩
  obtain ⟨t₀, ht₀, hg, hθ⟩ := GlobalTheory.IdealGenerator.exists_generator_Iid D cc hcc P hP
  have MA : M ≤ A := eA ▸ le_sup_left
  have MB : M ≤ B := eB ▸ le_sup_left
  have MC : M ≤ C := eC ▸ le_sup_left
  have bxA : b + x ∈ A := eA ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have bB : b ∈ B := eB ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have xC : x ∈ C := eC ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hsum : ∀ (y : Fin N' → D.host.E) (a : Fin N → 𝓞 D.host.E),
      ∑ i, ((ptH D cc δ N t₀ y).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i)) (a i) =
        ptH D cc δ N t₀ y a := by
    intro y a
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.single_apply]
    rw [← map_sum, Finset.univ_sum_single]
  have hin : ∀ (L : Lat D N') (y : Fin N' → D.host.E), y ∈ L → ∀ a : Fin N → 𝓞 D.host.E,
      ptH D cc δ N t₀ y a ∈ La D (tor0 D cc δ) (stdL D N) L := fun L y hy a =>
    (ptH_mem hδ L t₀ y a).2 fun j => smul_mem_IL (Submodule.smul_mem _ _ ht₀) hy
  have hinP : ∀ (L : Lat D N') (y : Fin N' → D.host.E), M ≤ L → (∀ p ∈ P, p • y ∈ M) → ∀ i, ∀ p ∈ P,
      ptH D cc δ N t₀ y (Pi.single i p) ∈ La D (tor0 D cc δ) (stdL D N) L := fun L y hL hy i p hp =>
    (ptH_mem hδ L t₀ y _).2 fun j => IL_mono hL <| smul_mem_IL_of_P hy <| Submodule.smul_mem_smul (by
      by_cases h : j = i
      · subst h; simpa using hp
      · simp [Pi.single_eq_of_ne h]) ht₀
  refine ⟨fun i => (ptH D cc δ N t₀ b).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i),
    fun i => (ptH D cc δ N t₀ x).comp (AddMonoidHom.single (fun _ : Fin N => 𝓞 D.host.E) i),
    fun _ => phiH D cc δ t₀ b x, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j a a'
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.single_apply]
    rw [Hf_ptH, Finset.sum_eq_single i (fun k _ hk => by rw [Pi.single_eq_of_ne hk, zero_mul]) (by simp)]
    split_ifs with h
    · subst h; simp only [Pi.single_eq_same]
    · rw [Pi.single_eq_of_ne h, map_zero, mul_zero, map_zero]
  · intro i a
    refine ⟨hin B b bB _, hin C x xC _, ?_⟩
    simp only [AddMonoidHom.comp_apply]
    rw [ptH_add]; exact hin A _ bxA _
  · intro i p hpP
    exact ⟨⟨hinP A b MA (fun p h => (hp p h).1) i p hpP, hinP C b MC (fun p h => (hp p h).1) i p hpP⟩,
      ⟨hinP A x MA (fun p h => (hp p h).2) i p hpP, hinP B x MB (fun p h => (hp p h).2) i p hpP⟩⟩
  · intro z hz
    rw [eB] at hz
    obtain ⟨a, ha⟩ := exists_sub_ptH hδ (fun p h => (hp p h).1) hg hz
    exact ⟨a, by rw [hsum]; exact ⟨ha A MA, ha C MC⟩⟩
  · intro z hz
    rw [eC] at hz
    obtain ⟨a, ha⟩ := exists_sub_ptH hδ (fun p h => (hp p h).2) hg hz
    exact ⟨a, by rw [hsum]; exact ⟨ha A MA, ha B MB⟩⟩
  · intro a ha i
    rw [hsum, ptH_mem hδ] at ha
    have h1 := pair_mem (fun y hy => sd_int hA hy bxA) (ha i)
    obtain ⟨o, ho⟩ := sd_int hB bB bB
    refine hθ (hE D b x) hbx (fun p h => ?_) (a i) ?_
    · rw [← hE_osmul_left]; exact sd_int hC (MC (hp p h).1) xC
    · have : a i • (t₀ * hE D b x) = hE D ((a i • t₀) • b) (b + x) - (a i * o) • t₀ := by
        rw [hE_smul_left, hE_add_right, ← ho]
        simp only [Algebra.smul_def, map_mul]; ring
      rw [this]; exact sub_mem h1 (Submodule.smul_mem _ _ ht₀)
  · intro a ha i
    rw [hsum, ptH_mem hδ] at ha
    have h1 := pair_mem (fun y hy => sd_int hB hy bB) (ha i)
    refine hθ (hE D x b) (fun h => hbx (conj_hE D x b ▸ h.conj)) (fun p h => ?_) (a i) ?_
    · rw [← hE_osmul_left]; exact sd_int hB (MB (hp p h).2) bB
    · rwa [hE_smul_left, smul_mul_assoc] at h1

end GlobalTheory.TriangleColumns
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TrivialAtPrimeAdelicGLSubgroupStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivialAtPrime_adelicGL_subgroup : ∀ (D : D7) (n q : ℕ), q.Prime → TrivAt D q (1 : GL (Fin n) (AE D)) ∧ (∀ g h : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q h → TrivAt D q (g * h)) ∧ ∀ g : GL (Fin n) (AE D), TrivAt D q g → TrivAt D q g⁻¹ := by
  first | exact @GlobalTheory.TrivSubgroup.trivAt_subgroup | exact GlobalTheory.TrivSubgroup.trivAt_subgroup | (intros; apply GlobalTheory.TrivSubgroup.trivAt_subgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryDoubleCosetClassesFiniteCardLeStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryDoubleCosetClasses_finite_card_le : ∀ (D : D7) (N : ℕ), Finite (Cls D N (intG D N)) ∧ (Nat.card (Cls D N (intG D N)) : ℝ) ≤ (12 * (fF D : ℝ) ^ 2 * (N : ℝ) ^ 4 * D.host.rdE ^ 2) ^ (6 * fF D * N ^ 2) ∧ ∀ J : Subgroup (GA D N), J ≤ intG D N → J.relIndex (intG D N) ≠ 0 → Finite (Cls D N J) ∧ Nat.card (Cls D N J) ≤ Nat.card (Cls D N (intG D N)) * J.relIndex (intG D N) := by
  first | exact @GlobalTheory.NormSum.cls_finite_card_le | exact GlobalTheory.NormSum.cls_finite_card_le | (intros; apply GlobalTheory.NormSum.cls_finite_card_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryRationalConjIntersectionCardDvdInvariantStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryRationalConjIntersectionCard_dvd_invariant : ∀ (D : D7) (N : ℕ) (J : Subgroup (GA D N)), J ≤ intG D N → ∀ g, gam D J g ≠ 0 ∧ gam D J g ∣ 8 ^ (2 * fF D * N) * (2 * (2 * fF D * N)).factorial ∧ ∀ γ ∈ ratG D N, ∀ j ∈ J, gam D J (γ * g * j) = gam D J g := by
  first | exact @GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant | exact GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant | (intros; apply GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitaryTransvectionMovesLatticeAtPrimeStatement
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryTransvection_moves_lattice_at_prime : ∀ (D : D7) (n q : ℕ) (P : Ideal (𝓞 D.host.E)), (∀ a ∈ P, sgO D a ∈ P) → ∀ (M : Lat D n) (b x : Fin n → D.host.E) (lam : D.host.E) (m : ℕ), (∀ p ∈ P, p • b ∈ M ∧ p • x ∈ M) → (∀ y ∈ M, IntE D (hE D y (b + x))) → IntE D (hE D (b + x) (b + x)) → lam + D.host.conj lam + lam * D.host.conj lam * hE D (b + x) (b + x) = 0 → Nat.Coprime m q → (∃ p ∈ P, (m : D.host.E) * lam = (p : D.host.E)) → (∃ p ∈ P, (m : D.host.E) * (1 + lam * hE D b (b + x)) = (p : D.host.E)) → ∃ s : Matrix (Fin n) (Fin n) D.host.E, s * cT D s = 1 ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) (M ⊔ Submodule.span (𝓞 D.host.E) {b + x}) ∧ SAt D q s (M ⊔ Submodule.span (𝓞 D.host.E) {b}) (M ⊔ Submodule.span (𝓞 D.host.E) {x}) := by
  first | exact @GlobalTheory.UnitaryTransvection.transvection | exact GlobalTheory.UnitaryTransvection.transvection | (intros; apply GlobalTheory.UnitaryTransvection.transvection <;> assumption)
end

