import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1412
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1306
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1315
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1305
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1204
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0130
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1420
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedOrbitalIntegralUnitGLEqHermitianLatticeCo
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.TwOrbLat

open GlobalTheory.UnitLemma

variable {K : UQ} {B : InvAlg K}

theorem mulLat_mem_iff (t : B.Aˣ) (L : Submodule K.O B.A) (y : B.A) :
    y ∈ mulLat K.O (t : B.A) L ↔ ((t⁻¹ : B.Aˣ) : B.A) * y ∈ L := by
  constructor
  · intro h
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 h
    simpa [← mul_assoc] using hx
  · intro h
    exact Submodule.mem_map.2 ⟨_, h, by simp [← mul_assoc]⟩

theorem mem_stabLat_iff (t : B.Aˣ) (L : Submodule K.O B.A) :
    t ∈ stabLat K.O L ↔ mulLat K.O (t : B.A) L = L := by
  constructor
  · intro h
    ext y
    rw [mulLat_mem_iff, h (((t⁻¹ : B.Aˣ) : B.A) * y), ← mul_assoc, Units.mul_inv, one_mul]
  · intro h y
    conv_rhs => rw [← h]
    rw [mulLat_mem_iff, ← mul_assoc, Units.inv_mul, one_mul]

theorem stabLat_mulLat (t : B.Aˣ) (L : Submodule K.O B.A) :
    stabLat K.O (mulLat K.O (t : B.A) L) = stabLat K.O L := by
  ext s
  change (∀ y, y ∈ mulLat K.O (t : B.A) L ↔ (s : B.A) * y ∈ mulLat K.O (t : B.A) L) ↔ ∀ y, y ∈ L ↔ (s : B.A) * y ∈ L
  simp only [mulLat_mem_iff]
  constructor
  · intro h y
    have := h ((t : B.A) * y)
    have e1 : ((t⁻¹ : B.Aˣ) : B.A) * ((t : B.A) * y) = y := by rw [← mul_assoc, Units.inv_mul, one_mul]
    have e2 : ((t⁻¹ : B.Aˣ) : B.A) * ((s : B.A) * ((t : B.A) * y)) = s * y := by rw [mul_left_comm, e1]
    rwa [e1, e2] at this
  · intro h y
    rw [h (((t⁻¹ : B.Aˣ) : B.A) * y), mul_left_comm]

theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hR : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [GlobalTheory.TwOrbConj.mem_rStab]
  unfold avg
  have h1 : ∀ x : H ⧸ (⊤ : Subgroup H), x = 1 := fun x =>
    QuotientGroup.induction_on x fun g => (QuotientGroup.eq_one_iff g).2 (Subgroup.mem_top g)
  rw [hR, Subgroup.index_top, finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (h1 x) hx)]
  simp

theorem cast_finsum {α : Type} (f : α → ℚ) : ((∑ᶠ i, f i : ℚ) : ℂ) = ∑ᶠ i, (f i : ℂ) := by
  by_cases h : (Function.support f).Finite
  · exact (Rat.castHom ℂ).toAddMonoidHom.map_finsum h
  · have h' : ¬ (Function.support fun i => (f i : ℂ)).Finite := by
      have : (Function.support fun i => (f i : ℂ)) = Function.support f := by ext i; simp
      rwa [this]
    rw [finsum_of_infinite_support h, finsum_of_infinite_support h', Rat.cast_zero]

end GlobalTheory.TwOrbLat

open GlobalTheory.UnitLemma GlobalTheory.TwOrbLat in
theorem GlobalTheory.TwOrbLat.twOrb_unit_eq_orbSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → ∀ (a : ℕ) (B : GlobalTheory.UnitLemma.InvAlg K), B.P.Separable → ∀ (β : B.Aˣ) (ε : B.A), (ε = 1 ∨ ε = -1) → B.σ (β : B.A) = β * (ε * B.g) → ∀ (b : Module.Basis (Fin a) K.E B.A) (δ : GLw a w), (∀ i j, ((δ.val * GlobalTheory.Tw.Phi a (w.adicCompletion E))⁻¹)ᵀ i j = e (B.herm β (b i) (b j))) → twOrb (thL a w) (GlobalTheory.LFun.KGL w a) δ ((GlobalTheory.LFun.KGL w a : Set (GLw a w)).indicator 1) = ((GlobalTheory.UnitLemma.orbSum K.O B.T {L : Submodule K.O B.A | GlobalTheory.UnitLemma.IsLat K.O K.E L ∧ ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} (fun _ => 1) : ℚ) : ℂ) := by
  intro E _ _ _ hU w hw K e he hO a B hP β ε hε hβ b δ hδ
  set θ := thL a w with hθ
  set Kg := GlobalTheory.LFun.KGL w a with hKg
  set ι := mulGL e b with hι
  set T' := twCent θ δ with hT'
  have hCent : T' = B.T.map ι := GlobalTheory.T.twistedCentralizer_eq_map_normOneTorus E w hw K e he a B hP β ε hε hβ b δ hδ
  have hinj : Function.Injective ι := mulGL_injective e b
  have hθK : ∀ k ∈ Kg, θ k ∈ Kg := GlobalTheory.BCT.ThBasic.thL_mem_KGL hU a w

  have hstab : ∀ (t : B.Aˣ) (q : GLw a w), ι t ∈ Kg.map (MulAut.conj q).toMonoidHom ↔
      t ∈ stabLat K.O (GlobalTheory.TwLat.lat e b q) := by
    intro t q
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, mem_stabLat_iff,
      ← latOf_mul e b t q, eq_comm, GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b, mul_assoc]
  have hcpt : cptPart T' = (intUnits K.O B.A ⊓ B.T).map ι := by
    rw [hCent]
    unfold cptPart
    have hS : {x | x ∈ B.T.map ι ∧ IsCompact (closure (Subgroup.zpowers x : Set (GLw a w)))} =
        ι '' ((intUnits K.O B.A ⊓ B.T : Subgroup B.Aˣ) : Set B.Aˣ) := by
      ext x
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hc⟩
        exact ⟨t, ⟨(GlobalTheory.T.isCompact_closure_zpowers_leftMulGL_iff_integral E w K e hO a B b t).1 hc, ht⟩, rfl⟩
      · rintro ⟨t, ⟨hi, ht⟩, rfl⟩
        exact ⟨⟨t, ht, rfl⟩, (GlobalTheory.T.isCompact_closure_zpowers_leftMulGL_iff_integral E w K e hO a B b t).2 hi⟩
    rw [hS, ← MonoidHom.map_closure, Subgroup.closure_eq]
  have hRel : ∀ y : GLw a w, (T' ⊓ Kg.map (MulAut.conj y).toMonoidHom).relIndex (cptPart T') =
      (stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) := by
    intro y
    have h1 : T' ⊓ Kg.map (MulAut.conj y).toMonoidHom = (stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).map ι := by
      ext x
      rw [Subgroup.mem_inf, hCent]
      constructor
      · rintro ⟨⟨t, ht, rfl⟩, hx⟩
        exact ⟨t, ⟨(hstab t y).1 hx, ht⟩, rfl⟩
      · rintro ⟨t, ⟨hs, ht⟩, rfl⟩
        exact ⟨⟨t, ht, rfl⟩, (hstab t y).2 hs⟩
    rw [h1, hcpt, Subgroup.relIndex_map_map_of_injective _ _ hinj]

  set P : GLw a w → Prop := fun y => y⁻¹ * δ * θ y ∈ Kg with hP_def
  have hPinv : ∀ (y t k : GLw a w), t ∈ T' → k ∈ Kg → (P (t * y * k) ↔ P y) := by
    intro y t k ht hk
    have hd : t⁻¹ * δ * θ t = δ := by
      rw [mul_assoc, ← (GlobalTheory.TwOrbConj.mem_twCent θ δ t).1 ht, inv_mul_cancel_left]
    have e1 : (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by
      calc (t * y * k)⁻¹ * δ * θ (t * y * k) = k⁻¹ * (y⁻¹ * (t⁻¹ * δ * θ t) * θ y) * θ k := by
            simp only [map_mul, _root_.mul_inv_rev]; group
        _ = k⁻¹ * (y⁻¹ * δ * θ y) * θ k := by rw [hd]
    simp only [hP_def]
    rw [e1]
    constructor
    · intro h
      have := Kg.mul_mem (Kg.mul_mem hk h) (Kg.inv_mem (hθK k hk))
      simpa [mul_assoc] using this
    · intro h
      exact Kg.mul_mem (Kg.mul_mem (Kg.inv_mem hk) h) (hθK k hk)

  have hsum : ∀ y : GLw a w, GlobalTheory.TwOrbConj.summand θ Kg δ ((Kg : Set (GLw a w)).indicator 1) y =
      if P y then ((((stabLat K.O (GlobalTheory.TwLat.lat e b y) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) else 0 := by
    intro y
    have hconst : (fun k : Kg => (Kg : Set (GLw a w)).indicator 1 ((y * k)⁻¹ * δ * θ (y * k))) =
        fun _ => (if P y then (1 : ℂ) else 0) := by
      funext k
      have := hPinv y 1 k (T'.one_mem) k.2
      rw [one_mul] at this
      simp only [Set.indicator_apply, SetLike.mem_coe, Pi.one_apply]
      by_cases h : P y
      · rw [if_pos h, if_pos ((this.2 h))]
      · rw [if_neg h, if_neg (fun h' => h (this.1 h'))]
    unfold GlobalTheory.TwOrbConj.summand
    rw [hconst, avg_const, hRel]
    split_ifs <;> simp

  set X : Set (Submodule K.O B.A) := {L : Submodule K.O B.A | IsLat K.O K.E L ∧
    ∀ z, z ∈ L ↔ ∀ y ∈ L, B.herm β y z ∈ (algebraMap K.O K.E).range} with hX
  have hUni : ∀ y : GLw a w, P y ↔ GlobalTheory.TwLat.lat e b y ∈ X := by
    intro y
    simp only [hP_def, hX, Set.mem_setOf_eq]
    rw [GlobalTheory.T.twistedConj_integral_iff_lattice_unimodular E w hw K e he hO a B β b δ hδ y]
    exact ⟨fun h => ⟨latOf_isLat e b y, h⟩, fun h => h.2⟩
  let r : X → X → Prop := fun L M => ∃ t ∈ B.T, (M : Submodule K.O B.A) = mulLat K.O (t : B.A) (L : Submodule K.O B.A)
  have hr : Equivalence r := by
    refine ⟨fun L => ⟨1, B.T.one_mem, ?_⟩, fun {L M} ⟨t, ht, h⟩ => ⟨t⁻¹, B.T.inv_mem ht, ?_⟩,
      fun {L M N} ⟨t, ht, h⟩ ⟨s, hs, h'⟩ => ⟨s * t, B.T.mul_mem hs ht, ?_⟩⟩
    · ext y; rw [mulLat_mem_iff]; simp
    · ext y; rw [mulLat_mem_iff, h, mulLat_mem_iff]; simp
    · ext y; rw [h', mulLat_mem_iff, h, mulLat_mem_iff, mulLat_mem_iff, ← mul_assoc]; simp [mul_comm]

  let φ : {q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) // P (Quotient.out q)} →
      Orb K.O B.T X := fun q => Quot.mk _ ⟨GlobalTheory.TwLat.lat e b (Quotient.out q.1), (hUni _).1 q.2⟩
  have hφ : Function.Bijective φ := by
    constructor
    · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
      obtain ⟨t, ht, h1⟩ := hr.eqvGen_iff.1 (Quot.eqvGen_exact h)
      simp only at h1
      rw [← latOf_mul e b t, GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b] at h1
      apply Subtype.ext
      simp only
      rw [← DoubleCoset.out_eq' T' Kg q, ← DoubleCoset.out_eq' T' Kg q', DoubleCoset.eq]
      refine ⟨ι t, by rw [hCent]; exact ⟨t, ht, rfl⟩, _, Kg.inv_mem h1, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    · intro o
      induction o using Quot.ind with
      | mk L =>
        obtain ⟨q0, hq0⟩ := GlobalTheory.T.exists_GL_latticeSpannedByGLColumns_eq_fullLattice E w K e a B b L.1 L.2.1
        obtain ⟨t', ht', k, hk, he'⟩ := (DoubleCoset.eq _ _ _ _).1
          (DoubleCoset.out_eq' T' Kg (DoubleCoset.mk T' Kg q0)).symm
        have hP0 : P q0 := (hUni q0).2 (hq0 ▸ L.2)
        refine ⟨⟨DoubleCoset.mk _ _ q0, by rw [he']; exact (hPinv q0 t' k ht' hk).2 hP0⟩, ?_⟩
        apply Quot.sound
        rw [hCent] at ht'
        obtain ⟨t, ht, rfl⟩ := ht'
        refine ⟨t⁻¹, B.T.inv_mem ht, ?_⟩
        show L.1 = _
        simp only
        rw [he', mul_assoc, latOf_mul e b t,
          ← (GlobalTheory.T.latticeSpannedByGLColumns_eq_iff E w K e hO a B b q0 (q0 * k)).2 (by simpa using hk), hq0]
        ext y; rw [mulLat_mem_iff, mulLat_mem_iff]; simp

  rw [GlobalTheory.TwOrbConj.twOrb_eq, orbSum, cast_finsum]
  simp_rw [hsum]
  rw [show (∑ᶠ q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)), if P (Quotient.out q) then
      ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) else 0) =
      ∑ᶠ q : {q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) // P (Quotient.out q)},
        ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q.1)) ⊓ B.T).relIndex (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)) by
    exact (finsum_congr fun q => finsum_eq_if.symm).trans (finsum_subtype_eq_finsum_cond
      (fun q : DoubleCoset.Quotient (T' : Set (GLw a w)) (Kg : Set (GLw a w)) => P (Quotient.out q))
      (f := fun q => ((((stabLat K.O (GlobalTheory.TwLat.lat e b (Quotient.out q)) ⊓ B.T).relIndex
        (intUnits K.O B.A ⊓ B.T) : ℕ) : ℂ)))).symm]
  refine finsum_eq_of_bijective φ hφ fun q => ?_
  obtain ⟨s, hs, hs'⟩ := hr.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq (φ q)))
  have hs2 : GlobalTheory.TwLat.lat e b (Quotient.out q.1) = mulLat K.O (s : B.A) (Quot.out (φ q)).1 := hs'
  rw [hs2, stabLat_mulLat]
  push_cast
  simp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryHeckeOperatorVectorMemLevelFunctions
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.BCT.TrKer.HopStab

theorem toSub_mul_right {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (x * k) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (y * k)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : y * (k : G) ∈ H := H.mul_mem hy k.2
    rw [dif_pos h2, dif_pos hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : y * (k : G) ∉ H := fun h => hy (by simpa using H.mul_mem h (H.inv_mem k.2))
    rw [dif_neg h2, dif_neg hy]

theorem toSub_mul_left {G : Type} [Group G] (H : Subgroup G) (K : Subgroup H) (u : H → ℂ)
    (hu : ∀ k ∈ K, ∀ x, u (k * x) = u x) (y : G) (k : H) (hk : k ∈ K) :
    u (toSub H (k * y)) = u (toSub H y) := by
  unfold toSub
  by_cases hy : y ∈ H
  · have h2 : (k : G) * y ∈ H := H.mul_mem k.2 hy
    rw [dif_pos h2, dif_pos hy]
    exact hu k hk ⟨y, hy⟩
  · have h2 : (k : G) * y ∉ H := fun h => hy (by simpa using H.mul_mem (H.inv_mem k.2) h)
    rw [dif_neg h2, dif_neg hy]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_loc {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {k : finU E n} (hk : k ∈ globLev S K')
    {w : Pl E} (hw : w ∈ S) : ∃ k' : UL n w, k' ∈ K' w ∧ (k' : GLw n w) = cLoc w k.1 := by
  unfold globLev at hk
  have := (Subgroup.mem_iInf.1 hk w)
  have := Subgroup.mem_iInf.1 this hw
  simpa using this

theorem globFn_mul_right {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU E n} (hk : k ∈ globLev S K') (x : finU E n) :
    globFn S f (x * k) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_right _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).2) _ k' hk'

theorem globFn_mul_left {S : Set (Pl E)} {K' : ∀ w : Pl E, Subgroup (UL n w)} {f : ∀ w : Pl E, UL n w → ℂ}
    (hf : ∀ w, IsHecke (K' w) (f w)) {k : finU E n} (hk : k ∈ globLev S K') (x : finU E n) :
    globFn S f (k * x) = globFn S f x := by
  unfold globFn
  refine finprod_mem_congr rfl fun w hw => ?_
  obtain ⟨k', hk', he⟩ := mem_loc hk hw
  rw [Subgroup.coe_mul, map_mul, ← he]
  exact toSub_mul_left _ (K' w) (f w) (fun k hk x => ((hf w).2 k hk x).1) _ k' hk'

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hopM_apply {S : Set (Pl E)} {lam : InfinitePlace E → DomWeight n} {K' : ∀ w : Pl E, Subgroup (UL n w)}
    (f : ∀ w : Pl E, UL n w → ℂ) (F : finU E n → Module.Dual ℂ (Wsp lam))
    (hfin : (Function.support fun q : finU E n ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite)
    (x : finU E n) :
    hopM S lam K' f F x = (((globLev S K').relIndex (globLev S (KL n)) : ℕ) : ℂ)⁻¹ •
      ∑ᶠ q : finU E n ⧸ globLev S K', globFn S f q.out • F (x * q.out) := by
  have hsub : (Function.support fun q : finU E n ⧸ globLev S K' => globFn S f q.out • F (x * q.out)) ⊆
      (hfin.toFinset : Set _) := by
    intro q hq
    simp only [Set.Finite.coe_toFinset, Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU E n → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU E n → Module.Dual ℂ (Wsp lam)) => L F x) h0
    simpa [rightReg, LinearMap.funLeft] using this
  unfold hopM levOp
  rw [finsum_eq_sum _ hfin, finsum_eq_sum_of_support_subset _ hsub]
  simp [rightReg, LinearMap.funLeft, Finset.sum_apply, LinearMap.sum_apply]

end GlobalTheory.BCT.TrKer.HopStab

namespace GlobalTheory.BCT.TrKer.HopStab

theorem hopM_mem_vecM : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (S : Set (Pl E))
    (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)),
    IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ,
    IsTest (KL n) K' f → ∀ F ∈ vecM S lam K', hopM S lam K' f F ∈ vecM S lam K' := by
  intro E _ _ _ n S lam K' _ f hf F hF
  by_cases hfin : (Function.support fun q : finU E n ⧸ globLev S K' =>
      globFn S f q.out • (rightReg ℂ (finU E n) (Module.Dual ℂ (Wsp lam)) q.out ∘ₗ LinearMap.id)).Finite
  swap
  · have h0 : hopM S lam K' f = 0 := by
      unfold hopM levOp
      rw [finsum_of_infinite_support hfin, smul_zero]
    rw [h0]
    exact (vecM S lam K').zero_mem
  have hsupp : ∀ y : finU E n, (Function.support fun q : finU E n ⧸ globLev S K' =>
      globFn S f q.out • F (y * q.out)).Finite := by
    intro y
    refine hfin.subset fun q hq => ?_
    simp only [Function.mem_support] at hq ⊢
    intro h0
    apply hq
    have := congrArg (fun L : (finU E n → Module.Dual ℂ (Wsp lam)) →ₗ[ℂ] (finU E n → Module.Dual ℂ (Wsp lam)) => L F y) h0
    simpa [rightReg, LinearMap.funLeft] using this
  refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
  · rw [hopM_apply f F hfin, hopM_apply f F hfin, map_smul, map_finsum _ (hsupp x)]
    congr 1
    refine finsum_congr fun q => ?_
    rw [mul_assoc, hF.1 γ, map_smul]
  · rw [hopM_apply f F hfin, hopM_apply f F hfin]
    congr 1
    symm
    rw [← finsum_comp_equiv (MulAction.toPerm k : Equiv.Perm (finU E n ⧸ globLev S K'))]
    refine finsum_congr fun q => ?_
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (globLev S K') (k * q.out)
    have hq : (MulAction.toPerm k : Equiv.Perm (finU E n ⧸ globLev S K')) q =
        ((k * q.out : finU E n) : finU E n ⧸ globLev S K') := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [hq, hh, globFn_mul_right hf.1 h.2, globFn_mul_left hf.1 hk, ← mul_assoc, ← mul_assoc, hF.2 h h.2]

end GlobalTheory.BCT.TrKer.HopStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalFinitenessRegularSemisimpleCentraliz
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct Pointwise

namespace GlobalTheory.LocFinU

theorem bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∃ Ω : Set (UL n w), IsCompact Ω ∧ (cptPart (twCent (MonoidHom.id (UL n w)) y) : Set (UL n w)) ⊆ Ω := by
  intro E _ _ _ hE n w y hy
  obtain ⟨Ω, hΩ, hsub⟩ := GlobalTheory.T.exists_compact_set_twisted_centralizer_elliptic E hE n w y hy
  refine ⟨Ω, hΩ, fun t ht => ?_⟩
  have hc : ∀ a ∈ twCent (MonoidHom.id (UL n w)) y, ∀ b ∈ twCent (MonoidHom.id (UL n w)) y, a * b = b * a := by
    intro a ha b hb
    have ha' : a.1.val * y.1.val =
        y.1.val * a.1.val :=
      by
        have h0 : a * y = y * a := ha
        have := congrArg (fun g : UL n w => g.1.val) h0
        simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have hb' : b.1.val * y.1.val =
        y.1.val * b.1.val :=
      by
        have h0 : b * y = y * b := hb
        have := congrArg (fun g : UL n w => g.1.val) h0
        simpa only [Subgroup.coe_mul, Units.val_mul] using this
    have := GlobalTheory.T.commute_of_commute_of_charpoly_separable' _ n _ _ _ hy ha' hb'
    exact Subtype.ext (Units.ext this)
  have := cptPart_subset_of_comm _ hc ht
  exact hsub t this.1 this.2

end GlobalTheory.LocFinU

namespace GlobalTheory.LocFinU

theorem conj_map_eq {G : Type} [Group G] (x : G) (K : Subgroup G) :
    (K.map (MulAut.conj x).toMonoidHom : Set G) = (fun k => x * k * x⁻¹) '' (K : Set G) := by
  ext g
  simp [Subgroup.coe_map, MulAut.conj_apply]

theorem locFin : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E) (y : UL n w), y.1.val.charpoly.Separable → ∀ K' : Subgroup (UL n w), IsLevel (MonoidHom.id _) (KL n w) K' → (∀ x : UL n w, twCent (MonoidHom.id _) y ⊓ (KL n w).map (MulAut.conj x).toMonoidHom ≤ cptPart (twCent (MonoidHom.id _) y) ∧ (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).relIndex (cptPart (twCent (MonoidHom.id _) y)) ≠ 0) ∧ ∀ C : Set (UL n w), IsCompact C → {q : DoubleCoset.Quotient (twCent (MonoidHom.id (UL n w)) y : Set (UL n w)) (K' : Set (UL n w)) | (Quotient.out q)⁻¹ * y * Quotient.out q ∈ C}.Finite := by
  intro E _ _ _ hE n w y hy K' hK'
  obtain ⟨hK'o, -, -⟩ := hK'
  obtain ⟨Ω, hΩ, hsub⟩ := bound E hE n w y hy
  refine ⟨fun x => ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨htT, htK⟩ := Subgroup.mem_inf.1 ht
    apply Subgroup.subset_closure
    refine ⟨htT, ?_⟩
    have hc : IsCompact ((KL n w).map (MulAut.conj x).toMonoidHom : Set (UL n w)) := by
      rw [conj_map_eq]
      exact (isCompact_KL n w).image ((continuous_const.mul continuous_id).mul continuous_const)
    refine hc.of_isClosed_subset isClosed_closure ?_
    exact closure_minimal (Subgroup.zpowers_le.2 htK) hc.isClosed
  · have hP : cptPart (twCent (MonoidHom.id _) y) ≤ twCent (MonoidHom.id _) y :=
      (Subgroup.closure_le _).2 (fun t ht => ht.1)
    have hU : IsOpen ((K'.map (MulAut.conj x).toMonoidHom : Subgroup _) : Set (UL n w)) := by
      rw [conj_map_eq]
      exact ((Homeomorph.mulLeft x).trans (Homeomorph.mulRight x⁻¹)).isOpenMap _ hK'o
    have h := relIndex_ne_zero_of_subset_cpt _ _ hU Ω hΩ hsub
    have e : (twCent (MonoidHom.id _) y ⊓ K'.map (MulAut.conj x).toMonoidHom).subgroupOf
        (cptPart (twCent (MonoidHom.id _) y)) =
        (K'.map (MulAut.conj x).toMonoidHom).subgroupOf (cptPart (twCent (MonoidHom.id _) y)) := by
      ext z
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨fun h => h.2, fun h => ⟨hP z.2, h⟩⟩
    unfold Subgroup.relIndex at h ⊢
    rwa [e]
  · intro C hC
    obtain ⟨Ω', hΩ', horb⟩ := GlobalTheory.T.regular_orbit_conj_compact_mod_centralizer_unitary E hE n w y hy C hC
    obtain ⟨s, hs⟩ := hΩ'.elim_finite_subcover (fun g : Ω' => (g : UL n w) • (K' : Set (UL n w)))
      (fun g => hK'o.smul _) (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, ⟨1, K'.one_mem, mul_one x⟩⟩)
    refine (s.finite_toSet.image
      (fun g : Ω' => DoubleCoset.mk (twCent (MonoidHom.id (UL n w)) y) K' (g : UL n w))).subset ?_
    intro q hq
    obtain ⟨t, ht, ω, hω, heq⟩ := horb _ hq
    have := hs hω
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, k, hk, hik⟩ := this
    refine ⟨i, hi, ?_⟩
    conv_rhs => rw [← Quotient.out_eq q]
    refine (DoubleCoset.eq _ _ _ _).2 ⟨t, ht, k, hk, ?_⟩
    rw [heq, ← hik]
    simp only [smul_eq_mul, mul_assoc]

end GlobalTheory.LocFinU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIntegralTupleLatticeCountBoundStatement
section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weighted_integral_tuple_lattice_count_bound : ∀ (D : D7) (κ : Type) [Fintype κ] (L : ℕ), 0 < L → ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ s : κ → ℝ, (∀ k, 0 < s k) → ∑' η : κ → D.host.E, {η : κ → D.host.E | ∀ k, IsIntegral ℤ ((L : D.host.E) * η k)}.indicator (fun η => ENNReal.ofReal (((1 + ∑ k, (∑ τ, ‖tauE D τ (η k)‖) / s k) ^ N)⁻¹)) η ≤ ENNReal.ofReal (C * ∏ k, max 1 (s k) ^ Module.finrank ℚ D.host.E) := by
  first | exact @GlobalTheory.WeightedCount.weighted_count | exact GlobalTheory.WeightedCount.weighted_count | (intros; apply GlobalTheory.WeightedCount.weighted_count <;> assumption)
end

