import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0986
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryOsc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1071

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNumberFieldInvolutionSimilitudeCentralizer
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.CentSim

variable {p : ℕ} [Fact p.Prime]

theorem commute_conj_sh_sim (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚ)
    (h : (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β) (z : G.C) (hz : Commute z (γ : G.C)) :
    Commute ((β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C)) (γ : G.C) := by
  set y : G.Cˣ := γ with hydef
  set c : G.C := algebraMap ℚ G.C c₀
  set Y := sh G (y : G.C)
  set Yi := sh G ((y⁻¹ : G.Cˣ) : G.C)
  have hYYi : Y * Yi = 1 := by
    simp only [Y, Yi, ← GlobalTheory.CentConj.sh_mul', Units.inv_mul, GlobalTheory.CentConj.sh_one']
  have hzi : Commute z ((y⁻¹ : G.Cˣ) : G.C) := hz.units_inv_right
  have hcomm : Yi * sh G z = sh G z * Yi := by
    simp only [Yi, ← GlobalTheory.CentConj.sh_mul']; rw [hzi.eq]
  have hcc : ∀ w : G.C, c * w = w * c := fun w => Algebra.commutes _ w
  have h1 : (y : G.C) * β = c * β * Yi := by
    calc (y : G.C) * β = (y : G.C) * β * (Y * Yi) := by rw [hYYi, mul_one]
      _ = c * β * Yi := by rw [← mul_assoc, h]
  have h2 : ((β⁻¹ : G.Cˣ) : G.C) * y = c * Yi * ((β⁻¹ : G.Cˣ) : G.C) := by
    calc ((β⁻¹ : G.Cˣ) : G.C) * y = ((β⁻¹ : G.Cˣ) : G.C) * ((y : G.C) * β) * ((β⁻¹ : G.Cˣ) : G.C) := by
          simp only [mul_assoc, Units.mul_inv, mul_one]
      _ = c * Yi * ((β⁻¹ : G.Cˣ) : G.C) := by
          rw [h1, ← mul_assoc, ← mul_assoc, ← hcc, mul_assoc c, Units.inv_mul, mul_one]
  change (β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C) * y = y * ((β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C))
  calc (β : G.C) * sh G z * ((β⁻¹ : G.Cˣ) : G.C) * y
        = (β : G.C) * sh G z * (((β⁻¹ : G.Cˣ) : G.C) * y) := by rw [mul_assoc]
    _ = c * (β * (sh G z * Yi)) * ((β⁻¹ : G.Cˣ) : G.C) := by
        rw [h2]; simp only [mul_assoc]
        rw [← mul_assoc (sh G z) c, ← hcc (sh G z), mul_assoc c, ← mul_assoc (β : G.C) c, ← hcc (β : G.C)]
        simp only [mul_assoc]
    _ = c * (β * (Yi * sh G z)) * ((β⁻¹ : G.Cˣ) : G.C) := by rw [hcomm]
    _ = (y : G.C) * β * sh G z * ((β⁻¹ : G.Cˣ) : G.C) := by rw [h1]; simp only [mul_assoc]
    _ = _ := by simp only [mul_assoc]

theorem centraliser_field_involution : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚˣ), sh G β = β →
    (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β → Irreducible (minpoly G.F (γ : G.C)) →
    (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
      Function.Injective ι ∧ (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) ∧
      (∀ x, ι (c x) = β * sh G (ι x) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ ∀ x, c (c x) = x := by
  intro p _ G β γ c₀ hβ hsim hirr hdeg
  obtain ⟨E, _, _, _, j, hj, hcent⟩ := GlobalTheory.CentIrr.centralizer_unit_eq_field p G γ hirr hdeg
  set w : E → G.C := fun e => (β : G.C) * sh G (j e) * ((β⁻¹ : G.Cˣ) : G.C) with hw
  have hex : ∀ e, ∃ e', j e' = w e := fun e =>
    (hcent _).1 (commute_conj_sh_sim G β γ (c₀ : ℚ) hsim (j e) ((hcent _).2 ⟨e, rfl⟩))
  choose t ht using hex
  have tt : ∀ e, t (t e) = e := by
    intro e
    apply hj
    rw [ht, hw]; dsimp only
    rw [ht, GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_mul', GlobalTheory.CentConj.sh_sh', hβ,
      GlobalTheory.CentConj.sh_inv_of_sym G β hβ]
    simp only [mul_assoc, Units.mul_inv, mul_one]
    rw [← mul_assoc, Units.mul_inv, one_mul]
  have hm : ∀ a b, t (a * b) = t a * t b := by
    intro a b
    apply hj
    rw [mul_comm a b, ht, map_mul, ht, ht, hw]; dsimp only
    rw [map_mul, GlobalTheory.CentConj.sh_mul']
    simp only [mul_assoc]
    rw [← mul_assoc ((β⁻¹ : G.Cˣ) : G.C) (β : G.C), Units.inv_mul, one_mul]
  have ha : ∀ a b, t (a + b) = t a + t b := by
    intro a b
    apply hj
    rw [ht, map_add, ht, ht, hw]; dsimp only
    rw [map_add, GlobalTheory.CentConj.sh_add']; noncomm_ring
  have h1 : t 1 = 1 := by
    apply hj
    rw [ht, hw]; dsimp only
    rw [map_one, GlobalTheory.CentConj.sh_one', mul_one, Units.mul_inv]
  have h0 : t 0 = 0 := by
    have h := ha 0 0
    rw [add_zero] at h
    exact left_eq_add.mp h
  let τ : E →+* E := { toFun := t, map_one' := h1, map_mul' := hm, map_zero' := h0, map_add' := ha }
  refine ⟨E, inferInstance, inferInstance, j.toRingHom.toRatAlgHom, τ.toRatAlgHom, hj, ?_, ?_, ?_⟩
  · intro z
    exact hcent z
  · intro x; exact ht x
  · intro x; exact tt x

end GlobalTheory.CentSim

example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (β γ : G.Cˣ) (c₀ : ℚˣ), sh G β = β →
    (γ : G.C) * β * sh G γ = algebraMap ℚ G.C c₀ * β → Irreducible (minpoly G.F (γ : G.C)) →
    (minpoly G.F (γ : G.C)).natDegree = G.n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (ι : L →ₐ[ℚ] G.C) (c : L →ₐ[ℚ] L),
      Function.Injective ι ∧ (∀ z : G.C, z * γ = γ * z ↔ ∃ w, ι w = z) ∧
      (∀ x, ι (c x) = β * sh G (ι x) * ((β⁻¹ : G.Cˣ) : G.C)) ∧ ∀ x, c (c x) = x :=
  GlobalTheory.CentSim.centraliser_field_involution
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
section
noncomputable section

namespace GlobalTheory.ThetaFacCompl

open scoped ComplexConjugate

section Abstract

variable {M : Type*} [AddCommGroup M] [Module ℂ M] (Z : Submodule ℂ M) (q : M → M → ℂ)

theorem q_zero_left (hsmul : ∀ a ∈ Z, ∀ c ∈ Z, ∀ t : ℂ, q (t • a) c = t * q a c) {c : M} (hc : c ∈ Z) :
    q 0 c = 0 := by
  have := hsmul 0 Z.zero_mem c hc 0
  simpa using this

theorem q_add_right (hadd : ∀ a ∈ Z, ∀ b ∈ Z, ∀ c ∈ Z, q (a + b) c = q a c + q b c)
    (hherm : ∀ a ∈ Z, ∀ b ∈ Z, q b a = conj (q a b)) {a b c : M} (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z) :
    q c (a + b) = q c a + q c b := by
  rw [hherm _ (Z.add_mem ha hb) _ hc, hadd a ha b hb c hc, map_add, ← hherm a ha c hc, ← hherm b hb c hc]

theorem q_smul_right (hsmul : ∀ a ∈ Z, ∀ c ∈ Z, ∀ t : ℂ, q (t • a) c = t * q a c)
    (hherm : ∀ a ∈ Z, ∀ b ∈ Z, q b a = conj (q a b)) {a c : M} (ha : a ∈ Z) (hc : c ∈ Z) (t : ℂ) :
    q c (t • a) = conj t * q c a := by
  rw [hherm _ (Z.smul_mem t ha) _ hc, hsmul a ha c hc t, map_mul, ← hherm a ha c hc]

theorem q_sub_right (hadd : ∀ a ∈ Z, ∀ b ∈ Z, ∀ c ∈ Z, q (a + b) c = q a c + q b c)
    (hsmul : ∀ a ∈ Z, ∀ c ∈ Z, ∀ t : ℂ, q (t • a) c = t * q a c)
    (hherm : ∀ a ∈ Z, ∀ b ∈ Z, q b a = conj (q a b)) {a b c : M} (ha : a ∈ Z) (hb : b ∈ Z) (hc : c ∈ Z) :
    q c (a - b) = q c a - q c b := by
  have e : a - b = a + (-1 : ℂ) • b := by simp [sub_eq_add_neg]
  rw [e, q_add_right Z q hadd hherm ha (Z.smul_mem _ hb) hc, q_smul_right Z q hsmul hherm hb hc]
  simp [sub_eq_add_neg]

theorem q_span_left (hadd : ∀ a ∈ Z, ∀ b ∈ Z, ∀ c ∈ Z, q (a + b) c = q a c + q b c)
    (hsmul : ∀ a ∈ Z, ∀ c ∈ Z, ∀ t : ℂ, q (t • a) c = t * q a c) {S : Set M} (hS : S ⊆ Z) {r : M} (hr : r ∈ Z)
    (h : ∀ u ∈ S, q u r = 0) : ∀ n ∈ Submodule.span ℂ S, q n r = 0 := by
  have hle : Submodule.span ℂ S ≤ Z := Submodule.span_le.2 hS
  intro n hn
  induction hn using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact q_zero_left Z q hsmul hr
  | add x y hx hy ihx ihy => rw [hadd x (hle hx) y (hle hy) r hr, ihx, ihy, add_zero]
  | smul t x hx ihx => rw [hsmul x (hle hx) r hr t, ihx, mul_zero]

theorem exists_orth (hadd : ∀ a ∈ Z, ∀ b ∈ Z, ∀ c ∈ Z, q (a + b) c = q a c + q b c)
    (hsmul : ∀ a ∈ Z, ∀ c ∈ Z, ∀ t : ℂ, q (t • a) c = t * q a c)
    (hherm : ∀ a ∈ Z, ∀ b ∈ Z, q b a = conj (q a b)) (hpos : ∀ a ∈ Z, q a a = 0 → a = 0) :
    ∀ S : Finset M, (↑S : Set M) ⊆ Z → ∀ x ∈ Z, ∃ n ∈ Submodule.span ℂ (S : Set M), ∀ u ∈ S, q u (x - n) = 0 := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ x _; exact ⟨0, Submodule.zero_mem _, by simp⟩
  | insert a s ha ih =>
    intro hS x hx
    have haZ : a ∈ Z := hS (by simp)
    have hsZ : (↑s : Set M) ⊆ Z := fun y hy => hS (by simp [hy])
    have hspZ : Submodule.span ℂ (↑s : Set M) ≤ Z := Submodule.span_le.2 hsZ
    obtain ⟨n1, hn1, h1⟩ := ih hsZ x hx
    obtain ⟨n2, hn2, h2⟩ := ih hsZ a haZ
    have hrZ : x - n1 ∈ Z := Z.sub_mem hx (hspZ hn1)
    have hsZ' : a - n2 ∈ Z := Z.sub_mem haZ (hspZ hn2)
    have hspan_le : Submodule.span ℂ (↑s : Set M) ≤ Submodule.span ℂ (↑(insert a s) : Set M) :=
      Submodule.span_mono (by simp [Finset.coe_insert])
    have ha_mem : a ∈ Submodule.span ℂ (↑(insert a s) : Set M) := Submodule.subset_span (by simp)
    by_cases hss : q (a - n2) (a - n2) = 0
    · have han2 : a = n2 := sub_eq_zero.1 (hpos _ hsZ' hss)
      refine ⟨n1, hspan_le hn1, fun u hu => ?_⟩
      rcases Finset.mem_insert.1 hu with rfl | hu
      · rw [han2]; exact q_span_left Z q hadd hsmul hsZ hrZ h1 n2 hn2
      · exact h1 u hu
    · set t : ℂ := conj (q (a - n2) (x - n1) / q (a - n2) (a - n2)) with ht
      have hct : conj t = q (a - n2) (x - n1) / q (a - n2) (a - n2) := by rw [ht, Complex.conj_conj]
      have hts : t • (a - n2) ∈ Z := Z.smul_mem t hsZ'
      have hx' : x - (n1 + t • (a - n2)) = (x - n1) - t • (a - n2) := by abel
      have horth : ∀ u ∈ Z, q u (x - n1) = 0 → q u (a - n2) = 0 → q u ((x - n1) - t • (a - n2)) = 0 := by
        intro u hu e1 e2
        rw [q_sub_right Z q hadd hsmul hherm hrZ hts hu, q_smul_right Z q hsmul hherm hsZ' hu, e1, e2]; simp
      have hs : ∀ u ∈ s, q u ((x - n1) - t • (a - n2)) = 0 := fun u hu => horth u (hsZ hu) (h1 u hu) (h2 u hu)
      refine ⟨n1 + t • (a - n2), add_mem (hspan_le hn1) (Submodule.smul_mem _ _ (sub_mem ha_mem (hspan_le hn2))),
        fun u hu => ?_⟩
      rw [hx']
      rcases Finset.mem_insert.1 hu with rfl | hu
      · have hself : q (u - n2) ((x - n1) - t • (u - n2)) = 0 := by
          rw [q_sub_right Z q hadd hsmul hherm hrZ hts hsZ', q_smul_right Z q hsmul hherm hsZ' hsZ', hct]
          field_simp; ring
        have hn2o : q n2 ((x - n1) - t • (u - n2)) = 0 :=
          q_span_left Z q hadd hsmul hsZ (Z.sub_mem hrZ hts) hs n2 hn2
        have e := hadd _ hsZ' _ (hspZ hn2) _ (Z.sub_mem hrZ hts)
        rw [sub_add_cancel] at e
        rw [e, hself, hn2o, add_zero]
      · exact hs u hu

theorem exists_of_mem_span_image {N : Type*} [AddCommGroup N] [Module ℂ N] (D A : Submodule ℂ M) (T : M → N)
    (hT : ∀ x ∈ D, ∀ y ∈ D, ∀ c : ℂ, T (x + c • y) = T x + c • T y) (hA : A ≤ D) {f : N}
    (hf : f ∈ Submodule.span ℂ (T '' (A : Set M))) : ∃ w ∈ A, T w = f := by
  have h0 : T 0 = 0 := by
    have := hT 0 D.zero_mem 0 D.zero_mem 1
    simpa using this
  induction hf using Submodule.span_induction with
  | mem x hx => obtain ⟨w, hw, rfl⟩ := hx; exact ⟨w, hw, rfl⟩
  | zero => exact ⟨0, A.zero_mem, h0⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨w1, hw1, rfl⟩ := ihx
    obtain ⟨w2, hw2, rfl⟩ := ihy
    exact ⟨w1 + w2, A.add_mem hw1 hw2, by simpa using hT w1 (hA hw1) w2 (hA hw2) 1⟩
  | smul c x _ ihx =>
    obtain ⟨w, hw, rfl⟩ := ihx
    exact ⟨c • w, A.smul_mem c hw, by simpa [h0] using hT 0 D.zero_mem w (hA hw) c⟩

end Abstract

end GlobalTheory.ThetaFacCompl

namespace GlobalTheory.ThetaFacCompl

open scoped ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

theorem I_transl (M : Model σ Y W) (om : Rep σ Y W) (Φ : Fn F n d) (h x : UA σ W.J) :
    M.I om (om (1, h) Φ) x = M.I om Φ (x * h) := by
  unfold Model.I theta
  congr 1
  funext g
  congr 1
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem mat_inv_mul (g : UA σ W.J) : mat g⁻¹ * mat g = 1 := by
  simp [mat]

theorem mat_mul_inv (g : UA σ W.J) : mat g * mat g⁻¹ = 1 := by
  simp [mat]

theorem inv_mem_UAt {R : Type} [Zero R] (ev : AF F → R) {h : UA σ W.J} (hh : h ∈ UAt σ W ev) :
    h⁻¹ ∈ UAt σ W ev := by
  intro u hu
  have e : mat h⁻¹ - 1 = -(mat h⁻¹ * (mat h - 1)) := by
    rw [Matrix.mul_sub, mat_inv_mul, Matrix.mul_one]; abel
  rw [e, smul_neg, ← Matrix.mul_smul, hh u hu, Matrix.mul_zero, neg_zero]

theorem inv_mem_KInf (τ : ∀ w : InfinitePlace F, EmbOver E w) {k : UA σ W.J} (hk : k ∈ KInf σ W τ) :
    k⁻¹ ∈ KInf σ W τ := by
  refine ⟨inv_mem_UAt _ hk.1, fun w => ?_⟩
  set A := (mat k).map (piInf (τ w))
  set A' := (mat k⁻¹).map (piInf (τ w))
  have h1 : A' * A = 1 := by
    simp only [A, A', ← Matrix.map_mul, mat_inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]
  have h2 : A * A' = 1 := by
    simp only [A, A', ← Matrix.map_mul, mat_mul_inv, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc : A * W.θ w = W.θ w * A := hk.2 w
  show A' * W.θ w = W.θ w * A'
  calc A' * W.θ w = A' * W.θ w * (A * A') := by rw [h2, Matrix.mul_one]
    _ = A' * (A * W.θ w) * A' := by rw [hc]; simp only [Matrix.mul_assoc]
    _ = (A' * A) * W.θ w * A' := by simp only [Matrix.mul_assoc]
    _ = W.θ w * A' := by rw [h1, Matrix.one_mul]

theorem mul_conj_polar (z w : ℂ) :
    z * conj w = ((‖z + w‖ ^ 2 : ℝ) - (‖z + (-1 : ℂ) * w‖ ^ 2 : ℝ) + Complex.I * (‖z + Complex.I * w‖ ^ 2 : ℝ)
      - Complex.I * (‖z + (-Complex.I) * w‖ ^ 2 : ℝ)) / 4 := by
  simp only [Complex.sq_norm, Complex.normSq_apply]
  apply Complex.ext <;> simp <;> ring

end GlobalTheory.ThetaFacCompl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodinger
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil Matrix

noncomputable section

namespace GlobalTheory.HoweD.Osc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ}

abbrev Lines (P Q R S : ι → ℕ) := Σ o : (Σ w : ι, Ix (P w) (Q w)), Ix (R o.1) (S o.1)

def lineSgn (n : Lines P Q R S) : Bool :=
  linePos (p := P n.1.1) (q := Q n.1.1) (r := R n.1.1) (s := S n.1.1) (n.1.2, n.2)

theorem blockDiagonal'_mulVec_apply {m : (Σ w : ι, Ix (P w) (Q w)) → Type} [∀ o, Fintype (m o)]
    [∀ o, DecidableEq (m o)] (M : ∀ o, Matrix (m o) (m o) ℂ) (v : (Σ o, m o) → ℂ) (o : Σ w : ι, Ix (P w) (Q w))
    (b : m o) : (blockDiagonal' M *ᵥ v) ⟨o, b⟩ = ∑ b', M o b b' * v ⟨o, b'⟩ := by
  simp only [mulVec, dotProduct]
  rw [Fintype.sum_sigma, Finset.sum_eq_single o]
  · simp [blockDiagonal'_apply']
  · intro o' _ h
    simp [blockDiagonal'_apply_ne M b _ (Ne.symm h)]
  · simp

theorem diagonal_lineSgn : (diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1) =
    blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => Jm (P o.1) (Q o.1) o.2 o.2 • Jm (R o.1) (S o.1) := by
  ext ⟨o, b⟩ ⟨o', b'⟩
  by_cases h : o = o'
  · subst h
    rcases o with ⟨w, a⟩
    rw [blockDiagonal'_apply']
    rcases a with a | a <;> rcases b with b | b <;> rcases b' with b' | b' <;>
      simp [diagonal_apply, Jm, Formalism.UG.Jpq, lineSgn, linePos, one_apply] <;> split_ifs <;> simp_all
  · rw [blockDiagonal'_apply_ne _ _ _ h, diagonal_apply_ne]
    intro e
    exact h (congrArg Sigma.fst e)

theorem blockDiagonal'_mem (M : ∀ w, Mat (R w) (S w)) (hM : ∀ w, (M w)ᴴ * Jm (R w) (S w) * M w = Jm (R w) (S w)) :
    (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => M o.1)ᵀ *
        (diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1) *
        (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => M o.1).map star =
      diagonal fun n : Lines P Q R S => if lineSgn n then (1 : ℂ) else -1 := by
  rw [diagonal_lineSgn, blockDiagonal'_transpose, blockDiagonal'_map _ _ (star_zero ℂ), ← blockDiagonal'_mul,
    ← blockDiagonal'_mul]
  congr 1
  funext o
  have h := congrArg transpose (hM o.1)
  rw [transpose_mul, transpose_mul, GlobalTheory.SchrodOsc.Jm_transpose] at h
  have e : (M o.1)ᴴᵀ = (M o.1).map star := by ext; simp
  rw [e] at h
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, h]

end GlobalTheory.HoweD.Osc

namespace GlobalTheory.HoweD.Osc

variable {ι : Type} [Fintype ι] [DecidableEq ι] {P Q R S : ι → ℕ} {G : Type} [Group G]

abbrev lineNum (P Q R S : ι → ℕ) := GlobalTheory.SchrodOsc.signEquiv (lineSgn (P := P) (Q := Q) (R := R) (S := S))

abbrev NumIx (P Q R S : ι → ℕ) :=
  Fin (Fintype.card {n // lineSgn (P := P) (Q := Q) (R := R) (S := S) n = true}) ⊕
    Fin (Fintype.card {n // ¬ lineSgn (P := P) (Q := Q) (R := R) (S := S) n = true})

def blockHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w))) : G →* Matrix (Lines P Q R S) (Lines P Q R S) ℂ where
  toFun g := blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1
  map_one' := by
    simp only [map_one, Pi.one_apply]
    exact blockDiagonal'_one
  map_mul' g g' := by simp [blockDiagonal'_mul]

def numHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w))) : G →* Matrix (NumIx P Q R S) (NumIx P Q R S) ℂ :=
  (reindexAlgEquiv ℂ ℂ (lineNum P Q R S)).toAlgHom.toRingHom.toMonoidHom.comp (blockHom P Q k)

theorem numHom_apply (k : G →* (∀ w, Mat (R w) (S w))) (g : G) :
    numHom P Q k g = reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1) :=
  rfl

theorem numHom_mem (k : G →* (∀ w, Mat (R w) (S w))) (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w))
    (g : G) :
    (numHom P Q k).toHomUnits g ∈ GlobalTheory.WeilM.UG (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) (fromBlocks 1 0 0 (-1)) := by
  have hc : ⇑(Complex.conjAe : ℂ →ₐ[ℝ] ℂ) = star := funext fun x => by simp
  show (numHom P Q k g)ᵀ * fromBlocks 1 0 0 (-1) * (numHom P Q k g).map (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) =
    fromBlocks 1 0 0 (-1)
  rw [hc, numHom_apply, GlobalTheory.SchrodOsc.fromBlocks_eq_reindex, transpose_reindex]
  have hm : (reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1)).map star =
      reindex (lineNum P Q R S) (lineNum P Q R S)
        ((blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1).map star) := rfl
  rw [hm, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← reindexAlgEquiv_apply ℂ ℂ, ← map_mul, ← map_mul,
    blockDiagonal'_mem _ (hk g)]

def unitHom (P Q : ι → ℕ) (k : G →* (∀ w, Mat (R w) (S w)))
    (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) :=
  (numHom P Q k).toHomUnits.codRestrict _ (numHom_mem k hk)

theorem continuous_unitHom [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w, Mat (R w) (S w)))
    (hc : Continuous k) (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) :
    Continuous (unitHom P Q k hk) := by
  have hn : Continuous (numHom P Q k) := by
    show Continuous fun g => reindex (lineNum P Q R S) (lineNum P Q R S)
      (blockDiagonal' fun o : (Σ w : ι, Ix (P w) (Q w)) => k g o.1)
    exact (Continuous.matrix_blockDiagonal'
      (continuous_pi fun (o : Σ w : ι, Ix (P w) (Q w)) => (continuous_apply o.1).comp hc)).matrix_reindex _ _
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨hn, ?_⟩)
  have : (fun g => (((Subtype.val ∘ unitHom P Q k hk) g)⁻¹ : GL _ ℂ).val) = fun g => numHom P Q k g⁻¹ := by
    funext g
    simp only [Function.comp_apply]
    rw [← Subgroup.coe_inv, ← map_inv]
    rfl
  rw [this]
  exact hn.comp continuous_inv

def coordOf (z : NumIx P Q R S → ℂ) : ∀ w, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ :=
  fun w a b => ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * z (lineNum P Q R S ⟨⟨w, a⟩, b⟩)

theorem coordOf_add (z z' : NumIx P Q R S → ℂ) : coordOf (z + z') = coordOf z + coordOf z' := by
  funext w a b
  simp [coordOf, mul_add]

theorem continuous_coordOf : Continuous (coordOf (P := P) (Q := Q) (R := R) (S := S)) :=
  continuous_pi fun _ => continuous_pi fun _ => continuous_pi fun _ => continuous_const.mul (continuous_apply _)

theorem two_mul_sum_coordOf (z z' : NumIx P Q R S → ℂ) :
    2 * ∑ w, ∑ a, ∑ b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) =
      (∑ i, z (Sum.inl i) * star (z' (Sum.inl i))) - ∑ j, z (Sum.inr j) * star (z' (Sum.inr j)) := by
  set e := lineNum P Q R S with he
  have hs : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * star (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = 2⁻¹ := by
    rw [star_inv₀, Complex.star_def, Complex.conj_ofReal, ← mul_inv, ← Complex.ofReal_mul,
      Real.mul_self_sqrt (by norm_num)]
    push_cast
    rfl
  let F : Lines P Q R S → ℂ := fun n => (if lineSgn n then 1 else -1) * z (e n) * star (z' (e n))
  have h1 : ∀ w a b, lineSign a b * coordOf z w a b * star (coordOf z' w a b) = 2⁻¹ * F ⟨⟨w, a⟩, b⟩ := by
    intro w a b
    simp only [coordOf, F, star_mul, lineSgn, GlobalTheory.SchrodOsc.lineSign_eq]
    rw [← hs, he]
    by_cases h : linePos (a, b) = true <;> simp only [h, ↓reduceIte, Bool.false_eq_true] <;> ring
  have h2 : ∑ n, F n = ∑ w, ∑ a, ∑ b, F ⟨⟨w, a⟩, b⟩ := by
    rw [Fintype.sum_sigma, Fintype.sum_sigma]
  have h3 : ∑ n, F n = ∑ i, F (e.symm i) := (e.symm.sum_comp F).symm
  simp_rw [h1, ← Finset.mul_sum, ← h2, h3, Fintype.sum_sum_type]
  simp only [F, he, GlobalTheory.SchrodOsc.pos_signEquiv_symm_inl, GlobalTheory.SchrodOsc.pos_signEquiv_symm_inr,
    Equiv.apply_symm_apply]
  simp
  ring

theorem coordOf_mulVec (k : G →* (∀ w, Mat (R w) (S w)))
    (hk : ∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) (g : G) (z : NumIx P Q R S → ℂ) :
    coordOf (((unitHom P Q k hk g).1 : Matrix _ _ ℂ) *ᵥ z) = fun w => coordOf z w * (k g w)ᵀ := by
  show coordOf (numHom P Q k g *ᵥ z) = _
  rw [numHom_apply, reindex_apply, submatrix_mulVec_equiv]
  funext w
  ext a b
  simp only [coordOf, Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply]
  rw [blockDiagonal'_mulVec_apply]
  simp only [mul_apply, transpose_apply, Finset.mul_sum, Function.comp_apply]
  exact Finset.sum_congr rfl fun _ _ => by simp only [coordOf]; ring

end GlobalTheory.HoweD.Osc

open GlobalTheory.HoweD

theorem GlobalTheory.HoweD.exists_osc : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ι → ℕ)
    (φ : (∀ w : ι, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (∀ w : ι, Mat (R w) (S w))), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm (R w) (S w) * k g w = Jm (R w) (S w)) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  intro ι l _ _ _ _ P Q R S φ hφ hcont G _ _ _ k hkc hk
  obtain ⟨ω₀, hω₀c, hω₀, -⟩ := GlobalTheory.FockRep.exists_unitary_osc _ _ (L2 l)
    (fun z => rho (φ (GlobalTheory.HoweD.Osc.coordOf z)))
    (fun v => (hcont v).comp ((LinearMap.continuous_of_finiteDimensional φ.toLinearMap).comp
      GlobalTheory.HoweD.Osc.continuous_coordOf))
    (fun z z' v => by
      rw [rho_rho, ← map_add, ← GlobalTheory.HoweD.Osc.coordOf_add, hφ, ← GlobalTheory.HoweD.Osc.two_mul_sum_coordOf]
      congr 2
      simp [Complex.mul_im]
      ring)
  refine ⟨ω₀.comp (GlobalTheory.HoweD.Osc.unitHom P Q k hk), fun v => (hω₀c v).comp (GlobalTheory.HoweD.Osc.continuous_unitHom k hkc hk),
    fun g c v => ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, GlobalTheory.HoweD.Osc.coordOf (P := P) (Q := Q) (R := R) (S := S) z = c := by
    refine ⟨fun i => ((Real.sqrt 2 : ℝ) : ℂ) * (fun n : GlobalTheory.HoweD.Osc.Lines P Q R S => c n.1.1 n.1.2 n.2)
      ((GlobalTheory.HoweD.Osc.lineNum P Q R S).symm i), ?_⟩
    funext w a b
    have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 two_pos).ne'
    simp only [GlobalTheory.HoweD.Osc.coordOf]
    rw [Equiv.symm_apply_apply, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]
  have h := hω₀ (GlobalTheory.HoweD.Osc.unitHom P Q k hk g) z v
  rw [hz, GlobalTheory.HoweD.Osc.coordOf_mulVec, hz] at h
  exact h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOscillatorActionNormalisingSchrodingerOperStatement
section
open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_oscillator_action_normalising_schrodingerOperators : ∀ (ι l : Type) [Fintype ι] [DecidableEq ι] [Fintype l] [DecidableEq l] (P Q R S : ℕ)
    (φ : (ι → Matrix (Ix P Q) (Ix R S) ℂ) ≃ₗ[ℝ] (l ⊕ l → ℝ)),
    (∀ c c', sympl (φ c) (φ c') = 2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im) →
    (∀ v : L2 l, Continuous fun w : l ⊕ l → ℝ => rho w v) →
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (k : G →* (ι → Mat R S)), Continuous k →
    (∀ g w, (k g w)ᴴ * Jm R S * k g w = Jm R S) →
    ∃ ω : G →* (L2 l ≃ₗᵢ[ℂ] L2 l), (∀ v, Continuous fun g => ω g v) ∧
      ∀ g c v, ω g (rho (φ c) v) = rho (φ fun w => c w * (k g w)ᵀ) (ω g v) := by
  first | exact @GlobalTheory.SchrodOsc.exists_osc | exact GlobalTheory.SchrodOsc.exists_osc | (intros; apply GlobalTheory.SchrodOsc.exists_osc <;> assumption)
end

