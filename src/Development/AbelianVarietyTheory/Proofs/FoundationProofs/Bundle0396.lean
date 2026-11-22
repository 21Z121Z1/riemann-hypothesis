import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0391
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0382
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousMatQApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0381
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0392
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0017
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0384
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0387
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCoefRingInvertPrimeInvOfMemNeZeroStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memCoefRingInvertPrime_inv_of_mem_ne_zero : ∀ (l : ℕ) [Fact l.Prime] (c : Coef l) (d : Qbar l), d ∈ c.O → d ≠ 0 → MemE c d⁻¹ := by
  first | exact @GlobalTheory.Ord2.memE_inv_of_mem | exact GlobalTheory.Ord2.memE_inv_of_mem | (intros; apply GlobalTheory.Ord2.memE_inv_of_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemCycAlgOfPow
section
noncomputable section

open ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.RecOne

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

def fixA (A : ValuationSubring Ω) : Subring A where
  carrier := {a | ∀ s ∈ Ine (F := ℚ) A, s (a : Ω) = a}
  one_mem' := fun s _ => by simp
  mul_mem' := fun {a b} ha hb s hs => by
    show s ((a : Ω) * (b : Ω)) = (a : Ω) * (b : Ω)
    rw [map_mul, ha s hs, hb s hs]
  zero_mem' := fun s _ => by simp
  add_mem' := fun {a b} ha hb s hs => by
    show s ((a : Ω) + (b : Ω)) = (a : Ω) + (b : Ω)
    rw [map_add, ha s hs, hb s hs]
  neg_mem' := fun {a} ha s hs => by
    show s (-(a : Ω)) = -(a : Ω)
    rw [map_neg, ha s hs]

theorem mem_fixA {A : ValuationSubring Ω} {a : A} : a ∈ fixA A ↔ ∀ s ∈ Ine (F := ℚ) A, s (a : Ω) = a := Iff.rfl

abbrev dA (A : ValuationSubring Ω) : Derivation (fixA A) A (KaehlerDifferential (fixA A) A) :=
  KaehlerDifferential.D (fixA A) A

def cycAlg (l : ℕ) (A : ValuationSubring Ω) : Subalgebra (fixA A) A :=
  Algebra.adjoin (fixA A) {z : A | ∃ n : ℕ, z ^ (l ^ n) = 1}

theorem mem_cycAlg_of_pow {l : ℕ} {A : ValuationSubring Ω} {z : A} {n : ℕ} (h : z ^ (l ^ n) = 1) :
    z ∈ cycAlg l A := Algebra.subset_adjoin ⟨n, h⟩

def ineCyc (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω) : Subgroup (G ℚ Ω) :=
  Ine (F := ℚ) A ⊓ (cycZ ℚ Ω l).ker

theorem mem_ineCyc {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {s : G ℚ Ω} :
    s ∈ ineCyc l A ↔ s ∈ Ine (F := ℚ) A ∧ cycZ ℚ Ω l s = 1 := Iff.rfl

abbrev FracA (A : ValuationSubring Ω) : Type := Ω ⧸ LinearMap.range (Algebra.linearMap A Ω)

omit [Algebra ℚ Ω] in

theorem mem_of_pow_mem (A : ValuationSubring Ω) {x : Ω} {n : ℕ} (hn : n ≠ 0)
    (h : x ^ n ∈ A) : x ∈ A := by
  rw [← A.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  by_contra hx
  push_neg at hx
  exact absurd h (not_le.2 (one_lt_pow' hx hn))

end GlobalTheory.RecOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OpenSubgroupCochainInvarianceStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.open_subgroup_cochain_invariance : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (n : ℕ) (H I : Subgroup (G ℚ Ω)) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), IsClosed (H : Set (G ℚ Ω)) → I ≤ H → ContinuousOn (fun p : G ℚ Ω × G ℚ Ω => ξ p.1 p.2) ((H : Set (G ℚ Ω)) ×ˢ (H : Set (G ℚ Ω))) → (∀ i ∈ I, eps l i = 1) → (∀ s ∈ H, ∀ t ∈ H, ∀ i ∈ I, Cg n (ξ (s * i) t) (ξ s t) ∧ Cg n (ξ s (t * i)) (ξ s t)) → ∃ K : Subgroup (G ℚ Ω), I ≤ K ∧ K ≤ H ∧ IsOpen ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) ∧ (∀ k ∈ K, Cg n (eps l k) 1) ∧ ∀ s ∈ H, ∀ t ∈ H, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t) := by
  first | exact @GlobalTheory.Ord2.OpenInv.open_inv | exact GlobalTheory.Ord2.OpenInv.open_inv | (intros; apply GlobalTheory.Ord2.OpenInv.open_inv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.OrdinarySelmerModPrimePowInjectsResidualSelmer
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.Ord2.GwIneq
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.SelLower

variable {l : ℕ} [Fact l.Prime]

open Classical in

def rv (c : Coef l) (n : ℕ) (v : Fin 2 → Qbar l) : Mn c n :=
  fun i => if h : v i ∈ c.O then red c n ⟨v i, h⟩ else 0

theorem rv_apply {c : Coef l} {n : ℕ} {v : Fin 2 → Qbar l} (hv : ∀ i, v i ∈ c.O) (i : Fin 2) :
    rv c n v i = red c n ⟨v i, hv i⟩ := by
  unfold rv; rw [dif_pos (hv i)]

theorem rv_eq_iff {c : Coef l} {n : ℕ} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    rv c n a = rv c n b ↔ Cv n a b := by
  rw [funext_iff]
  refine forall_congr' fun i => ?_
  rw [rv_apply ha, rv_apply hb, red_eq_iff]

theorem addV {c : Coef l} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    ∀ i, (a + b) i ∈ c.O := fun i => c.O.add_mem (ha i) (hb i)

theorem subV {c : Coef l} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    ∀ i, (a - b) i ∈ c.O := fun i => c.O.sub_mem (ha i) (hb i)

theorem zeroV (c : Coef l) : ∀ i, (0 : Fin 2 → Qbar l) i ∈ c.O := fun _ => c.O.zero_mem

theorem rv_add {c : Coef l} {n : ℕ} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    rv c n (a + b) = rv c n a + rv c n b := by
  funext i
  rw [rv_apply (addV ha hb)]
  show _ = rv c n a i + rv c n b i
  rw [rv_apply ha, rv_apply hb, ← map_add]
  rfl

theorem rv_sub {c : Coef l} {n : ℕ} {a b : Fin 2 → Qbar l} (ha : ∀ i, a i ∈ c.O) (hb : ∀ i, b i ∈ c.O) :
    rv c n (a - b) = rv c n a - rv c n b := by
  funext i
  rw [rv_apply (subV ha hb)]
  show _ = rv c n a i - rv c n b i
  rw [rv_apply ha, rv_apply hb, ← map_sub]
  rfl

theorem rv_zero (c : Coef l) (n : ℕ) : rv c n 0 = 0 := by
  funext i
  rw [rv_apply (zeroV c)]
  show _ = (0 : Qn c n)
  rw [← map_zero (red c n)]
  rfl

theorem mulVec_mem {c : Coef l} {M : Matrix (Fin 2) (Fin 2) (Qbar l)} (hM : ∀ i j, M i j ∈ c.O)
    {x : Fin 2 → Qbar l} (hx : ∀ i, x i ∈ c.O) (i : Fin 2) : (M *ᵥ x) i ∈ c.O := by
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  exact c.O.add_mem (c.O.mul_mem (hM _ _) (hx _)) (c.O.mul_mem (hM _ _) (hx _))

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem rv_mulVec (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (s : G ℚ Ω)
    {x : Fin 2 → Qbar l} (hx : ∀ i, x i ∈ c.O) :
    rv c n (mat W s *ᵥ x) = matQ c n W hint s *ᵥ rv c n x := by
  funext i
  rw [rv_apply (mulVec_mem (hint s) hx)]
  have e : (⟨(mat W s *ᵥ x) i, mulVec_mem (hint s) hx i⟩ : c.O) =
      ⟨mat W s i 0, hint s i 0⟩ * ⟨x 0, hx 0⟩ + ⟨mat W s i 1, hint s i 1⟩ * ⟨x 1, hx 1⟩ := by
    apply Subtype.ext
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [e, map_add, map_mul, map_mul]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, matQ_apply, rv_apply hx]

theorem continuous_rv (c : Coef l) (n : ℕ) {y : G ℚ Ω → Fin 2 → Qbar l} (hyc : Continuous y)
    (hO : ∀ s i, y s i ∈ c.O) : Continuous fun s => rv c n (y s) := by
  refine continuous_pi fun i => ?_
  refine continuous_discrete_rng.2 fun q => ?_
  obtain ⟨z, rfl⟩ := red_surjective c n q
  have e : (fun s => rv c n (y s) i) ⁻¹' {red c n z} =
      (fun s => y s i) ⁻¹' Metric.closedBall (z : Qbar l) ‖((l : ℕ) : Qbar l) ^ n‖ := by
    ext s
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_closedBall, dist_eq_norm, rv_apply (hO s)]
    exact red_eq_iff _ _
  rw [e]
  have hne : ‖((l : ℕ) : Qbar l) ^ n‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  exact (IsUltrametricDist.isOpen_closedBall _ hne).preimage ((continuous_apply i).comp hyc)

theorem eq_of_natCast_mem {v w : Pl} (hv : ((l : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((l : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) :
    v = w := by
  have hp : Prime ((l : ℕ) : 𝓞 ℚ) := by
    have e : ((l : ℕ) : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm ((l : ℕ) : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr
      (Nat.prime_iff_prime_int.1 (Fact.out : l.Prime))
  have hmax : (Ideal.span {((l : ℕ) : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hp.ne_zero).2 hp).isMaximal
      (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero)
  have h1 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} = v.asIdeal :=
    hmax.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hv)
  have h2 : Ideal.span {((l : ℕ) : 𝓞 ℚ)} = w.asIdeal :=
    hmax.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)
  exact HeightOneSpectrum.ext (h1.symm.trans h2)

theorem toGS_surjective (S : Finset Pl) : Function.Surjective (toGS Ω (S : Set Pl)) :=
  QuotientGroup.mk'_surjective _

def zOf (c : Coef l) (n : ℕ) (S : Finset Pl) (y : G ℚ Ω → Fin 2 → Qbar l) : GS Ω (S : Set Pl) → Mn c n :=
  fun g => rv c n (y (Function.surjInv (toGS_surjective S) g))

theorem rv_wd (c : Coef l) (n : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) {y : G ℚ Ω → Fin 2 → Qbar l} (hy : GwCount.SelN c n S A W y)
    {s t : G ℚ Ω} (h : toGS Ω (S : Set Pl) s = toGS Ω (S : Set Pl) t) : rv c n (y s) = rv c n (y t) := by
  have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
  have ha : s⁻¹ * t ∈ (toGS Ω (S : Set Pl)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have e : s * (s⁻¹ * t) = t := by group
  have h1 := hy.1.2.2 s (Subgroup.mem_top _) (s⁻¹ * t) (Subgroup.mem_top _)
  rw [e] at h1
  have h2 := hy.2.1 _ ha
  rw [(rv_eq_iff (hO t) (addV (hO s) (mulVec_mem (hint s) (hO _)))).2 h1,
    rv_add (hO s) (mulVec_mem (hint s) (hO _)), rv_mulVec c n W hint s (hO _),
    (rv_eq_iff (hO _) (zeroV c)).2 h2, rv_zero, Matrix.mulVec_zero, add_zero]

theorem zOf_toGS (c : Coef l) (n : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l)
    (hint : ∀ s i j, mat W s i j ∈ c.O) {y : G ℚ Ω → Fin 2 → Qbar l} (hy : GwCount.SelN c n S A W y)
    (s : G ℚ Ω) : zOf c n S y (toGS Ω (S : Set Pl) s) = rv c n (y s) :=
  rv_wd c n S A W hint hy (Function.surjInv_eq (toGS_surjective S) _)

theorem zOf_mem (c : Coef l) (n : ℕ) (W : R2 Ω l) (hint : ∀ s i j, mat W s i j ∈ c.O) (S : Finset Pl)
    (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (A : ValuationSubring Ω) {y : G ℚ Ω → Fin 2 → Qbar l}
    (hy : GwCount.SelN c n S A W y) : zOf c n S y ∈ Z1 (rhoS c n W hint S hN) := by
  have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
  refine ⟨?_, fun g h => ?_⟩
  · rw [(QuotientGroup.isQuotientMap_mk _).continuous_iff]
    have e : (zOf c n S y ∘ QuotientGroup.mk) = fun s => rv c n (y s) :=
      funext fun s => zOf_toGS c n S A W hint hy s
    rw [e]
    have h0 := hy.1.1
    rw [Subgroup.coe_top] at h0
    exact continuous_rv c n (continuousOn_univ.1 h0) hO
  · obtain ⟨s, rfl⟩ := toGS_surjective S g
    obtain ⟨t, rfl⟩ := toGS_surjective S h
    rw [← map_mul, zOf_toGS c n S A W hint hy, zOf_toGS c n S A W hint hy, zOf_toGS c n S A W hint hy,
      rhoS_toGS, ← rv_mulVec c n W hint s (hO t), ← rv_add (hO s) (mulVec_mem (hint s) (hO t))]
    exact (rv_eq_iff (hO _) (addV (hO s) (mulVec_mem (hint s) (hO t)))).2
      (hy.1.2.2 s (Subgroup.mem_top _) t (Subgroup.mem_top _))

end

theorem sel_lower : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ (c : Coef l) (hint : ∀ s i j, mat W s i j ∈ c.O) (hN : ∀ a ∈ NS Ω (S : Set Pl), W a = 1) (n : ℕ), 1 ≤ n → ∃ cls : (G ℚ Ω → Fin 2 → Qbar l) → H1 (rhoS c n W hint S hN), (∀ y, GwCount.SelN c n S A W y → cls y ∈ SelG c n W hint S hN A) ∧ ∀ y y', GwCount.SelN c n S A W y → GwCount.SelN c n S A W y' → cls y = cls y' → Cob1 c n W ⊤ (y - y') := by
  intro l _ Ω _ _ _ e S A W hW c hint hN n _
  classical
  refine ⟨fun y => if h : GwCount.SelN c n S A W y then
    Submodule.Quotient.mk ⟨zOf c n S y, zOf_mem c n W hint S hN A h⟩ else 0, ?_, ?_⟩
  · intro y hy
    have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
    simp only [dif_pos hy]
    rw [SelG, mem_Sel]
    intro v
    rw [resH1, Submodule.mapQ_apply]
    by_cases hv : IsPlaceOver A v.1
    · have hL : Lc c n W hint S hN A v = ordCond c n W hint S hN (Av A S v) := by
        unfold Lc; exact if_pos hv
      have hAv : Av A S v = A := by
        unfold Av; rw [if_pos hv]
      rw [hL]
      change Submodule.Quotient.mk (restrictCocycles1 (rhoS c n W hint S hN) (locHom (S : Set Pl) (Av A S v))
        (continuous_locHom _ _) ⟨zOf c n S y, zOf_mem c n W hint S hN A hy⟩) ∈ ordCond c n W hint S hN (Av A S v)
      rw [ordCond]
      have hmem : restrictCocycles1 (rhoS c n W hint S hN) (locHom (S : Set Pl) (Av A S v)) (continuous_locHom _ _)
          ⟨zOf c n S y, zOf_mem c n W hint S hN A hy⟩ ∈
          (ordZ c n W hint (Av A S v)).comap (Z1 ((rhoS c n W hint S hN).comp
            (locHom (S : Set Pl) (Av A S v)))).subtype := by
        rw [Submodule.mem_comap, mem_ordZ]
        obtain ⟨x, hx, hxs⟩ := hy.2.2.2
        refine ⟨red c n ⟨x, hx⟩, fun s => ?_⟩
        show zOf c n S y (toGS Ω (S : Set Pl) s.1) 1 = _
        have hs : (s : G ℚ Ω) ∈ Dec (F := ℚ) A := (le_of_eq (congrArg (Dec (F := ℚ)) hAv)) s.2
        rw [zOf_toGS c n S A W hint hy, rv_apply (hO s.1), matQ_apply, ← map_mul, ← map_sub, red_eq_iff]
        exact hxs s hs
      exact Submodule.mem_map_of_mem hmem
    · have hL : Lc c n W hint S hN A v = H1ur ((rhoS c n W hint S hN).comp (locFam S (Av A S) v))
          ((Ine (F := ℚ) (Av A S v)).subgroupOf (Dec (F := ℚ) (Av A S v))) := by
        unfold Lc; exact if_neg hv
      have hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.1.asIdeal := fun h => hv (by
        obtain ⟨v0, hA0, hl0⟩ := hW.atL
        rw [eq_of_natCast_mem h hl0]
        exact hA0)
      obtain ⟨B, hB, hcob⟩ := hy.2.2.1 v.1 v.2 hl
      obtain ⟨x, hxO, hx⟩ := CobConj.cob_conj l Ω W c n y v.1 B (Av A S v) hint hy.1 hB
        (isPlaceOver_Av A S v) hcob
      rw [hL, H1ur, LinearMap.mem_ker]
      refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_coboundaries1 _ _).2 ⟨rv c n x, fun g => ?_⟩)
      show zOf c n S y (toGS Ω (S : Set Pl) g.1.1) = matQ c n W hint g.1.1 *ᵥ rv c n x - rv c n x
      have hg : (g.1.1 : G ℚ Ω) ∈ Ine (F := ℚ) (Av A S v) := Subgroup.mem_subgroupOf.1 g.2
      rw [zOf_toGS c n S A W hint hy, ← rv_mulVec c n W hint _ hxO, ← rv_sub (mulVec_mem (hint _) hxO) hxO]
      exact (rv_eq_iff (hO _) (subV (mulVec_mem (hint _) hxO) hxO)).2 (hx _ hg)
  · intro y y' hy hy' heq
    have hO : ∀ s i, y s i ∈ c.O := hy.1.2.1
    have hO' : ∀ s i, y' s i ∈ c.O := hy'.1.2.1
    simp only [dif_pos hy, dif_pos hy'] at heq
    rw [Submodule.Quotient.eq, Submodule.mem_comap, mem_coboundaries1] at heq
    obtain ⟨m, hm⟩ := heq
    choose x hx using fun i => red_surjective c n (m i)
    have hxO : ∀ i, (fun i => ((x i : c.O) : Qbar l)) i ∈ c.O := fun i => (x i).2
    have hm' : rv c n (fun i => ((x i : c.O) : Qbar l)) = m := funext fun i => by
      rw [rv_apply hxO]; exact hx i
    refine ⟨fun i => ((x i : c.O) : Qbar l), hxO, fun s _ => ?_⟩
    have h := hm (toGS Ω (S : Set Pl) s)
    change zOf c n S y (toGS Ω (S : Set Pl) s) - zOf c n S y' (toGS Ω (S : Set Pl) s) =
      rhoS c n W hint S hN (toGS Ω (S : Set Pl) s) m - m at h
    rw [zOf_toGS c n S A W hint hy, zOf_toGS c n S A W hint hy', rhoS_toGS, ← hm',
      ← rv_mulVec c n W hint s hxO, ← rv_sub (hO s) (hO' s), ← rv_sub (mulVec_mem (hint s) hxO) hxO] at h
    exact (rv_eq_iff (subV (hO s) (hO' s)) (subV (mulVec_mem (hint s) hxO) hxO)).1 h

end GlobalTheory.Ord2.SelLower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperRep
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.ES

namespace GlobalTheory.KZ.ES

theorem sum_act_upper_rep : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    ∀ (N l : ℕ) [Fact l.Prime] (q M : ℕ), 0 < q → Nat.Coprime q M → ∀ b : X.Fn l,
    (∀ γ ∈ Gam N l, X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b) →
    ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] b =
      ∑ j ∈ Finset.range q, X.act l !![1, (j * M : ℤ); 0, (q : ℤ)] b := by
  intro Ω _ _ _ ε X N l _ q M hq hqM b hb
  have hT : ∀ t : ℤ, X.act l !![1, t; 0, 1] b = b := by
    intro t
    let T : SL(2, ℤ) := ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩
    have hmem : T ∈ Gam N l := by
      refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
      · rw [CongruenceSubgroup.Gamma1_mem]
        refine ⟨?_, ?_, ?_⟩ <;> simp [T]
      · rw [CongruenceSubgroup.Gamma0_mem]
        simp [T]
    exact hb T hmem
  have he : IsCoprime (M : ℤ) (q : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one]; simpa [Int.gcd_natCast_natCast] using hqM.symm
  exact (Tower.sum_act_upper_mul_unit X l b hT q (M : ℤ) hq he).symm

end GlobalTheory.KZ.ES
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumActUpperTriangularHeckeReindexCoprimeUnitStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_act_upperTriangular_hecke_reindex_coprime_unit : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (c : X.Fn l), (∀ t : ℤ, X.act l !![1, t; 0, 1] c = c) → ∀ (q : ℕ) (e : ℤ), 0 < q → IsCoprime e (q : ℤ) → ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ) * e; 0, (q : ℤ)] c = ∑ j ∈ Finset.range q, X.act l !![1, (j : ℤ); 0, (q : ℤ)] c := by
  first | exact @GlobalTheory.KZ.Tower.sum_act_upper_mul_unit | exact GlobalTheory.KZ.Tower.sum_act_upper_mul_unit | (intros; apply GlobalTheory.KZ.Tower.sum_act_upper_mul_unit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameClassLimitOfNormCompatibleShapiroSystemStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KA
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tameClass_limit_of_normCompatible_shapiroSystem : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : R2 Ω l) (c : Coef l) (e n : ℕ) (χ : ∀ r : ℕ, (ZMod (l ^ r))ˣ → Qbar l) (θ : G ℚ Ω →* (Qbar l)ˣ) (ρ : G ℚ Ω → Matrix (Fin 2) (Fin 2) (Qbar l)) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (Yw : ∀ r : ℕ, G ℚ Ω → Multiplicative (ZMod (l ^ n)) × (ZMod (l ^ r))ˣ → Fin 2 → Qbar l) (y : G ℚ Ω → Fin 2 → Qbar l) (P : Qbar l) (b : ℕ → Fin 2 → Qbar l), (∀ s i j, mat W s i j ∈ c.O) → (∀ s, mat W s = (θ s : Qbar l) • ρ s) → (∀ s i j, ρ s i j ∈ c.O) → (∀ r x, χ r x ∈ c.O) → (∀ r (x : (ZMod (l ^ (r + 1)))ˣ), ‖χ (r + 1) x - χ r ((Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom) x)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r s x, ‖(fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (x * cycMod ℚ Ω l r s) - (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) x * (θ s : Qbar l)‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → (∀ r, ShCoc ρ (ψ.prod (cycMod ℚ Ω l r)⁻¹) (Yw r)) → (∀ r x i, Continuous fun s => Yw r s x i) → (∀ r s x i, Yw r s x i ∈ c.O) → (∀ r s, Yw r s = push (Prod.map id (Units.map (ZMod.castHom (pow_dvd_pow l (Nat.le_succ r)) (ZMod (l ^ r))).toMonoidHom)) (Yw (r + 1)) s) → P ∈ c.O → (∀ r i, b r i ∈ c.O) → (∀ s i, y s i ∈ c.O) → (∀ r s i, ‖(∑ a, spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x => Yw r s (a, x)) s) i - (P • y s + (mat W s *ᵥ b r - b r)) i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖) → ∃ (Y : G ℚ Ω → Multiplicative (ZMod (l ^ n)) → Fin 2 → Qbar l) (b' : Fin 2 → Qbar l), ShCoc (mat W) ψ Y ∧ (∀ x i, Continuous fun s => Y s x i) ∧ (∀ s x i, Y s x i ∈ c.O) ∧ (∀ i, b' i ∈ c.O) ∧ (∀ s, ∑ x, Y s x = P • y s + (mat W s *ᵥ b' - b')) ∧ ∀ r s x i, ‖Y s x i - spec (fun x : (ZMod (l ^ r))ˣ => ((((x : ZMod (l ^ r)).val : ℕ) : Qbar l) ^ e)⁻¹ * χ r x) (fun s x' => Yw r s (x, x')) s i‖ ≤ ‖((l : ℕ) : Qbar l) ^ r‖ := by
  first | exact @GlobalTheory.KA.tame_limit | exact GlobalTheory.KA.tame_limit | (intros; apply GlobalTheory.KA.tame_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TameCochainCocycleExtension
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

namespace GlobalTheory.BrTame

variable {l : ℕ} [Fact l.Prime]

def ballSub (r : ℝ) (hr : 0 ≤ r) : AddSubgroup (PadicAlgCl l) where
  carrier := {x | ‖x‖ ≤ r}
  zero_mem' := by simpa using hr
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  neg_mem' := fun {a} ha => by simpa [Set.mem_setOf_eq, norm_neg] using ha

theorem mem_ballSub {r : ℝ} {hr : 0 ≤ r} {x : PadicAlgCl l} : x ∈ ballSub r hr ↔ ‖x‖ ≤ r := Iff.rfl

theorem cg_iff {n : ℕ} {a b : Qbar l} : Cg n a b ↔ a - b ∈ ballSub (l := l) ‖((l : ℕ) : Qbar l) ^ n‖ (norm_nonneg _) := Iff.rfl

theorem mul_mem_ballSub {r : ℝ} {hr : 0 ≤ r} {k x : PadicAlgCl l} (hk : ‖k‖ ≤ 1) (hx : x ∈ ballSub r hr) :
    k * x ∈ ballSub r hr := by
  rw [mem_ballSub, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hk).trans hx

theorem norm_le_one_of_int (x : PadicAlgCl l) (hx : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral
  | exact _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral
  | (apply _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralNormLeOne.norm_le_one_of_isIntegral ..)

theorem norm_le_one_of_mem (c : Coef l) {x : Qbar l} (hx : x ∈ c.O) : ‖x‖ ≤ 1 :=
  norm_le_one_of_int x ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨x, hx⟩ : c.O)).map c.O.val)

end GlobalTheory.BrTame

open GlobalTheory.BrTame in

theorem GlobalTheory.br_tame : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (c : Coef l) (n : ℕ) (w : Pl) (B : ValuationSubring Ω) (ψ : G ℚ Ω →* Multiplicative (ZMod (l ^ n))) (h : G ℚ Ω → Qbar l) (σ : G ℚ Ω), 1 ≤ n → IsPlaceOver B w → l ^ n ∣ normV w - 1 → (∃ τ ∈ Ine (F := ℚ) B, (ψ τ).toAdd = 1) → (∀ s, h s ∈ c.O) → (∀ s ∈ Dec (F := ℚ) B, ∀ t ∈ Dec (F := ℚ) B, Cg n (h (s * t)) (h s + h t)) → (∀ s ∈ Ine (F := ℚ) B, Cg n (h s) 0) → Cob2 c n (Dec (F := ℚ) B) (fun s t => (((ψ s).toAdd.val : ℕ) : Qbar l) * h t) → σ ∈ Dec (F := ℚ) B → Cg n (h σ) 0 := by
  intro l _ Ω _ _ _ c n w B ψ h σ hn hB hdiv ⟨τ, hτ, hψτ⟩ hO _ hIne ⟨u, hucont, huO, hu⟩ hσ
  set S := ballSub (l := l) ‖((l : ℕ) : Qbar l) ^ n‖ (norm_nonneg _) with hS
  have hu1 : ∀ s, ‖u s‖ ≤ 1 := fun s => norm_le_one_of_mem c (huO s)
  have heps : ∀ s ∈ Dec (F := ℚ) B, eps l s - 1 ∈ S := fun s hs => GlobalTheory.T.cyclotomicChar_congruent_one_on_decompositionGroup l Ω n w B hB hdiv hn s hs
  have hnat : ∀ k : ℕ, ‖((k : ℕ) : Qbar l)‖ ≤ 1 := fun k => IsUltrametricDist.norm_natCast_le_one _ k
  have hmul : ∀ k x : Qbar l, ‖k‖ ≤ 1 → x ∈ S → k * x ∈ S := fun k x hk hx => mul_mem_ballSub hk hx
  have hIne' : ∀ s ∈ Ine (F := ℚ) B, h s ∈ S := fun s hs => by
    have := cg_iff.1 (hIne s hs)
    rwa [sub_zero] at this
  have hIneDec : ∀ s ∈ Ine (F := ℚ) B, s ∈ Dec (F := ℚ) B := fun s hs => Ine_le_Dec B hs

  set T := ballSub (l := l) 1 zero_le_one with hT
  let M := T ⧸ S.comap T.subtype
  let f : G ℚ Ω → M := fun s => QuotientAddGroup.mk ⟨u s, hu1 s⟩
  have hf : ∀ s t, f s = f t ↔ u s - u t ∈ S := fun s t => by
    show (QuotientAddGroup.mk _ : M) = QuotientAddGroup.mk _ ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_comap]
    change -u s + u t ∈ S ↔ _
    have e : -u s + u t = -(u s - u t) := by ring
    rw [e, S.neg_mem_iff]
  have hlpos : 0 < ‖((l : ℕ) : Qbar l) ^ n‖ := norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have htors : ∀ x : M, l ^ n • x = 0 := by
    intro x
    induction x using QuotientAddGroup.induction_on with
    | H y =>
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap, AddSubgroup.coe_subtype,
        AddSubgroup.coe_nsmul, nsmul_eq_mul, mem_ballSub, norm_mul, Nat.cast_pow]
      exact mul_le_of_le_one_right (norm_nonneg _) y.2
  have hloc : IsLocallyConstant (fun s : Ine (F := ℚ) B => f s) := by
    rw [IsLocallyConstant.iff_exists_open]
    intro x
    have hc : Continuous (fun s : Ine (F := ℚ) B => u s) :=
      (hucont.mono (fun s hs => hIneDec s hs)).comp_continuous continuous_subtype_val (fun s => s.2)
    refine ⟨(fun s : Ine (F := ℚ) B => u s) ⁻¹' Metric.ball (u x) ‖((l : ℕ) : Qbar l) ^ n‖,
      Metric.isOpen_ball.preimage hc, Metric.mem_ball_self hlpos, fun y hy => ?_⟩
    rw [hf, mem_ballSub]
    have := Metric.mem_ball.1 hy
    rw [dist_eq_norm] at this
    exact this.le
  have hadd : ∀ s ∈ Ine (F := ℚ) B, ∀ t ∈ Ine (F := ℚ) B, f (s * t) = f s + f t := by
    intro s hs t ht
    have e : f s + f t = QuotientAddGroup.mk (⟨u s, hu1 s⟩ + ⟨u t, hu1 t⟩ : T) := rfl
    rw [e]
    show (QuotientAddGroup.mk _ : M) = QuotientAddGroup.mk _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_comap]
    change -u (s * t) + (u s + u t) ∈ S
    have h1 := hu s (hIneDec s hs) t (hIneDec t ht)
    have h2 := hmul _ _ (hnat ((ψ s).toAdd.val)) (hIne' t ht)
    have h3 := hmul _ _ (hu1 t) (heps s (hIneDec s hs))
    rw [cg_iff] at h1
    have e2 : -u (s * t) + (u s + u t) =
        -((((ψ s).toAdd.val : ℕ) : Qbar l) * h t - (eps l s * u t - u (s * t) + u s))
          + (((ψ s).toAdd.val : ℕ) : Qbar l) * h t - u t * (eps l s - 1) := by ring
    rw [e2]
    exact S.sub_mem (S.add_mem (S.neg_mem h1) h2) h3
  have hconj := GlobalTheory.T.inertiaTorsionQuotient_conj_invariant_decomposition l Ω n w B M f hB hdiv hn htors hloc hadd σ hσ τ hτ
  rw [hf] at hconj
  set τ' := σ * τ * σ⁻¹ with hτ'
  have hτ'I : τ' ∈ Ine (F := ℚ) B := conj_mem_Ine hσ hτ
  have hprod : τ' * σ = σ * τ := by rw [hτ']; group
  have hψ' : ((ψ τ').toAdd.val : Qbar l) = 1 := by
    have e : ψ τ' = ψ τ := by rw [hτ', map_mul, map_mul, mul_comm (ψ σ), mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    have hl1 : 1 < l ^ n := Nat.one_lt_pow (by omega) (Fact.out : l.Prime).one_lt
    rw [e, hψτ, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hl1, Nat.cast_one]
  have hA := hu τ' (hIneDec τ' hτ'I) σ hσ
  have hB' := hu σ hσ τ (hIneDec τ hτ)
  dsimp only at hA hB'
  rw [cg_iff, hprod, hψ', one_mul] at hA
  rw [cg_iff] at hB'
  have hC := hmul _ _ (hnat ((ψ σ).toAdd.val)) (hIne' τ hτ)
  have hD := hmul _ _ (hu1 σ) (heps τ' (hIneDec τ' hτ'I))
  have hF := hmul _ _ (hu1 τ) (heps σ hσ)
  rw [cg_iff, sub_zero]
  have e : h σ = (h σ - (eps l τ' * u σ - u (σ * τ) + u τ')) + u σ * (eps l τ' - 1) + (u τ' - u τ)
      - ((((ψ σ).toAdd.val : ℕ) : Qbar l) * h τ - (eps l σ * u τ - u (σ * τ) + u σ))
      + (((ψ σ).toAdd.val : ℕ) : Qbar l) * h τ - u τ * (eps l σ - 1) := by ring
  rw [e]
  exact S.sub_mem (S.add_mem (S.sub_mem (S.add_mem (S.add_mem hA hD) hconj) hB') hC) hF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoCocycleModPowCoboundaryOfFrobeniusSplitStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cob2_of_cocycle_cong_of_invariant : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (c : Coef l) (n : ℕ) (D K : Subgroup (G ℚ Ω)) (φ : ↥D) (m : ℕ) (d : ↥D →* Multiplicative (ZMod (m * l ^ n))) (ξ : G ℚ Ω → G ℚ Ω → Qbar l), 0 < m → ((φ ^ m : ↥D) : G ℚ Ω) ∈ K → IsOpen (d.ker : Set ↥D) → (∀ s : ↥D, (((φ ^ (Multiplicative.toAdd (d s)).val)⁻¹ * s : ↥D) : G ℚ Ω) ∈ K) → (∀ k ∈ K, Cg n (eps l k) 1) → (∀ s t, ξ s t ∈ c.O) → (∀ r ∈ D, ∀ s ∈ D, ∀ t ∈ D, Cg n (eps l r * ξ s t + ξ r (s * t)) (ξ (r * s) t + ξ r s)) → (∀ s ∈ D, ∀ t ∈ D, ∀ k ∈ K, Cg n (ξ (s * k) t) (ξ s t) ∧ Cg n (ξ s (t * k)) (ξ s t)) → Cob2 c n D ξ := by
  first | exact @GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split | exact GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split | (intros; apply GlobalTheory.Ord2.FrobCob.twoCocycleModPow_coboundary_of_frobenius_split <;> assumption)
end

