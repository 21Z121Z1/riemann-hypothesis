import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.GenericPointSectionHypotheses
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PClaimVanishCech
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

namespace Cech

variable {n : ℕ} {U : Finset (Fin n)} {R : Type u} [CommRing R] {G : Cell U → Type v}
  [∀ I, AddCommGroup (G I)] [∀ I, Module R (G I)] {ρ : ∀ I J : Cell U, I.1 ⊆ J.1 → G I →ₗ[R] G J}

theorem subsingleton_H_one_iff :
    Subsingleton (H G ρ 1) ↔ ∀ z : Cochain G 1, d G ρ 1 z = 0 → ∃ w : Cochain G 0, d G ρ 0 w = z := by
  unfold H
  rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
  constructor
  · intro h z hz
    exact h (LinearMap.mem_ker.mpr hz)
  · intro h z hz
    exact h z (LinearMap.mem_ker.mp hz)

theorem sgn_mul_sgn_erase {J : Finset (Fin n)} {j k : Fin n} (hj : j ∈ J) (hk : k ∈ J) (hjk : j ≠ k) :
    sgn J j * sgn (J.erase j) k = -(sgn J k * sgn (J.erase k) j) := by
  wlog h : j < k generalizing j k
  · have h' : k < j := lt_of_le_of_ne (not_lt.mp h) hjk.symm
    rw [this hk hj hjk.symm h', neg_neg]
  have hmem : j ∈ J.filter (· < k) := Finset.mem_filter.mpr ⟨hj, h⟩
  have e1 : (J.erase j).filter (· < k) = (J.filter (· < k)).erase j := by rw [Finset.filter_erase]
  have e2 : (J.erase k).filter (· < j) = J.filter (· < j) := by
    rw [Finset.filter_erase]
    apply Finset.erase_eq_of_notMem
    simp only [Finset.mem_filter, not_and, not_lt]
    intro _; exact h.le
  have hb : 1 ≤ (J.filter (· < k)).card := Finset.card_pos.mpr ⟨j, hmem⟩
  unfold sgn
  rw [e1, e2, Finset.card_erase_of_mem hmem]
  obtain ⟨b', hb'⟩ : ∃ b', (J.filter (· < k)).card = b' + 1 := ⟨_, (Nat.sub_add_cancel hb).symm⟩
  rw [hb', Nat.add_sub_cancel, pow_succ]
  ring

theorem d_one_d_zero
    (hρ : ∀ (I J K : Cell U) (h : I.1 ⊆ J.1) (h' : J.1 ⊆ K.1) (m : G I),
      ρ J K h' (ρ I J h m) = ρ I K (h.trans h') m)
    (w : Cochain G 0) : d G ρ 1 (d G ρ 0 w) = 0 := by
  funext J
  have key : ∀ (K K' : Idx U 0) (h : K.1.1 ⊆ J.1.1) (h' : K'.1.1 ⊆ J.1.1), K = K' →
      ρ K.1 J.1 h (w K) = ρ K'.1 J.1 h' (w K') := by
    rintro K _ h h' rfl; rfl
  rw [d_apply]
  simp only [d_apply, map_sum, map_zsmul, hρ, Finset.smul_sum, smul_smul]
  rw [Pi.zero_apply, Finset.sum_sigma']
  refine Finset.sum_involution
    (fun p _ => ⟨⟨p.2.1, Finset.mem_of_mem_erase p.2.2⟩,
      ⟨p.1.1, Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp p.2.2).1.symm, p.1.2⟩⟩⟩) ?_ ?_
    (fun _ _ => Finset.mem_univ _) (fun p _ => rfl)
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ -
    have hk' := Finset.mem_erase.mp hk
    have hidx : face (face J ⟨j, hj⟩) ⟨k, hk⟩ =
        face (face J ⟨k, hk'.2⟩) ⟨j, Finset.mem_erase.mpr ⟨hk'.1.symm, hj⟩⟩ :=
      Subtype.ext (Subtype.ext (Finset.erase_right_comm))
    dsimp only
    rw [key _ _ _ (((face_subset _ _).trans (face_subset _ _))) hidx, ← add_smul]
    have hs : sgn J.1.1 j * sgn (face J ⟨j, hj⟩).1.1 k =
        -(sgn J.1.1 k * sgn (face J ⟨k, hk'.2⟩).1.1 j) :=
      sgn_mul_sgn_erase hj hk'.2 hk'.1.symm
    rw [hs, neg_add_cancel, zero_smul]
  · rintro ⟨⟨j, hj⟩, ⟨k, hk⟩⟩ - - heq
    exact (Finset.mem_erase.mp hk).1 (congrArg (fun p => p.1.1) heq)

end Cech

namespace SubSystem

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}

section General

variable {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

theorem d_one_d_zero (F : SubSystem S x E) (w : Cech.Cochain (fun I => F.sub I) 0) :
    Cech.d (fun I => F.sub I) F.res 1 (Cech.d (fun I => F.sub I) F.res 0 w) = 0 :=
  Cech.d_one_d_zero (fun _ _ _ _ _ _ => rfl) w

set_option maxHeartbeats 1000000 in

theorem subsingleton_H_one_of_quot (F G : SubSystem S x E)
    (hGF : ∀ I, ∀ y ∈ G.sub I, y ∈ F.sub I) (hG : Subsingleton (G.H 1))
    (hQ : Subsingleton (quotH F G 1)) : Subsingleton (F.H 1) := by
  unfold SubSystem.H at hG ⊢
  unfold quotH at hQ
  rw [Cech.subsingleton_H_one_iff] at hG hQ ⊢
  intro z hz
  let q : ∀ I, F.sub I →ₗ[S] (F.sub I ⧸ quotSub F G I) := fun I => (quotSub F G I).mkQ
  have hq : ∀ I J h m, q J (F.res I J h m) = quotRes F G I J h (q I m) := fun _ _ _ _ => rfl
  have hqd := Cech.mapC_d (R := S) (G := fun I => ↥(F.sub I))
    (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q hq
  obtain ⟨wb, hwb⟩ := hQ (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 1 z) (by rw [← hqd, hz, map_zero])
  choose w hw using fun I : Cech.Idx (support x) 0 => Submodule.Quotient.mk_surjective _ (wb I)
  have hmw : (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 0 w) = wb := funext hw
  have hr : (Cech.mapC (R := S) (G := fun I => ↥(F.sub I)) (G' := fun I => ↥(F.sub I) ⧸ quotSub F G I) q 1 (z - Cech.d (fun I => F.sub I) F.res 0 w)) = 0 := by
    rw [map_sub, hqd 0, hmw, hwb]
    exact @sub_eq_zero_of_eq (Cech.Cochain (fun I => ↥(F.sub I) ⧸ quotSub F G I) 1) _ _ _ rfl
  have hrG : ∀ J, (((z - Cech.d (fun I => F.sub I) F.res 0 w) J : F.sub J.1) : E) ∈ G.sub J.1 :=
    fun J => (Submodule.Quotient.mk_eq_zero (quotSub F G J.1)).mp (congrFun hr J)
  let ι : ∀ I, G.sub I →ₗ[S] F.sub I := fun I =>
    { toFun := fun y => ⟨y, hGF I y y.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hι : ∀ I J h m, ι J (G.res I J h m) = F.res I J h (ι I m) := fun _ _ _ _ => rfl
  have hιd := Cech.mapC_d (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι hι
  have hιinj : ∀ i, Function.Injective (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι i) := fun i a b hab =>
    funext fun I => Subtype.ext (congrArg (fun c => ((c I : F.sub I.1) : E)) hab)
  obtain ⟨g, hg⟩ : ∃ g : Cech.Cochain (fun I => ↥(G.sub I)) 1,
      (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι 1 g) =
        z - Cech.d (fun I => F.sub I) F.res 0 w := ⟨fun J => ⟨_, hrG J⟩, rfl⟩
  have hdg : Cech.d (fun I => ↥(G.sub I)) G.res 1 g = 0 := by
    have h2 : (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι (1 + 1)
        (Cech.d (fun I => ↥(G.sub I)) G.res 1 g)) = 0 := by
      rw [hιd 1 g, hg, map_sub, hz, d_one_d_zero, sub_zero]
    exact hιinj (1 + 1) (h2.trans (LinearMap.map_zero _).symm)
  obtain ⟨v, hv⟩ := hG g hdg
  refine ⟨w + (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F.sub I)) ι 0 v), ?_⟩
  rw [map_add, ← hιd, hv, hg, add_sub_cancel]

end General

theorem subsingleton_H_one_of_smul (F' G : SubSystem S x Ω) (σ : Ω) (hσ : σ ≠ 0)
    (hG : ∀ I z, z ∈ G.sub I ↔ ∃ y ∈ F'.sub I, z = σ * y) (hF : Subsingleton (F'.H 1)) :
    Subsingleton (G.H 1) := by
  unfold SubSystem.H at hF ⊢
  rw [Cech.subsingleton_H_one_iff] at hF ⊢
  have hdiv : ∀ I (z : G.sub I), σ⁻¹ * (z : Ω) ∈ F'.sub I := fun I z => by
    obtain ⟨y, hy, hzy⟩ := (hG I z).mp z.2
    rw [hzy, ← mul_assoc, inv_mul_cancel₀ hσ, one_mul]
    exact hy
  let φ : ∀ I, G.sub I →ₗ[S] F'.sub I := fun I =>
    { toFun := fun z => ⟨σ⁻¹ * z, hdiv I z⟩
      map_add' := fun a b => Subtype.ext (mul_add _ _ _)
      map_smul' := fun s a => Subtype.ext (by
        show σ⁻¹ * (s • (a : Ω)) = s • (σ⁻¹ * (a : Ω))
        rw [Algebra.smul_def, Algebra.smul_def]; ring) }
  let ψ : ∀ I, F'.sub I →ₗ[S] G.sub I := fun I =>
    { toFun := fun y => ⟨σ * y, (hG I _).mpr ⟨y, y.2, rfl⟩⟩
      map_add' := fun a b => Subtype.ext (mul_add _ _ _)
      map_smul' := fun s a => Subtype.ext (by
        show σ * (s • (a : Ω)) = s • (σ * (a : Ω))
        rw [Algebra.smul_def, Algebra.smul_def]; ring) }
  have hφ : ∀ I J h m, φ J (G.res I J h m) = F'.res I J h (φ I m) := fun _ _ _ _ => rfl
  have hψ : ∀ I J h m, ψ J (F'.res I J h m) = G.res I J h (ψ I m) := fun _ _ _ _ => rfl
  have hφd := Cech.mapC_d (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F'.sub I)) φ hφ
  have hψd := Cech.mapC_d (R := S) (G := fun I => ↥(F'.sub I)) (G' := fun I => ↥(G.sub I)) ψ hψ
  intro z hz
  obtain ⟨w, hw⟩ := hF (Cech.mapC (R := S) (G := fun I => ↥(G.sub I)) (G' := fun I => ↥(F'.sub I)) φ 1 z) (by rw [← hφd, hz, map_zero])
  refine ⟨(Cech.mapC (R := S) (G := fun I => ↥(F'.sub I)) (G' := fun I => ↥(G.sub I)) ψ 0 w), ?_⟩
  rw [← hψd, hw]
  funext J
  apply Subtype.ext
  show σ * (σ⁻¹ * ((z J : G.sub J.1) : Ω)) = ((z J : G.sub J.1) : Ω)
  rw [← mul_assoc, mul_inv_cancel₀ hσ, one_mul]

end SubSystem

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial Filter

noncomputable section

universe u w

namespace HilbertPoint

variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}

def aff (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : Fin (N + 1) → Ω := fun l => y l / y j

theorem aff_def (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : aff y j = fun l => y l / y j := rfl

variable (k) in

def affRing (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) : Subalgebra k Ω :=
  (aeval (aff y j) : Poly k N →ₐ[k] Ω).range

variable (k) in

def affPiece (y : Fin (N + 1) → Ω) (j : Fin (N + 1)) (n : ℕ) : Submodule k Ω :=
  Submodule.span k {z | ∃ f : Poly k N, f.IsHomogeneous n ∧ z = aeval (aff y j) f}

variable {y : Fin (N + 1) → Ω} {j : Fin (N + 1)}

theorem aeval_aff_of_mem_primeOf {f : Poly k N} (hf : f ∈ primeOf (S := k) y) :
    aeval (aff y j) f = 0 := by
  rw [← sum_homogeneousComponent f, map_sum]
  refine Finset.sum_eq_zero fun d _ => ?_
  rw [aff_def, aeval_div_of_isHomogeneous (homogeneousComponent_isHomogeneous d f),
    (mem_primeOf_of_isHomogeneous y (homogeneousComponent_isHomogeneous d f)).mp
      (homogeneousComponent_mem_primeOf y hf d), zero_div]

theorem le_zero_of_add_one_le_one {d : WithBot ℕ∞} (h : d + 1 ≤ 1) : d ≤ 0 := by
  induction d using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe e =>
    have h' : e + 1 ≤ 1 := by exact_mod_cast h
    induction e using ENat.recTopCoe with
    | top => simp at h'
    | coe m =>
      have : m + 1 ≤ 1 := by exact_mod_cast h'
      have hm : m = 0 := by omega
      subst hm
      simp

theorem isField_affRing (hy : IsSubvar y (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    IsField (affRing k y j) := by
  let φ : Poly k N →ₐ[k] affRing k y j := (aeval (aff y j)).rangeRestrict
  have hφ : Function.Surjective φ := AlgHom.rangeRestrict_surjective _
  have hker : ∀ f ∈ primeOf (S := k) y, φ.toRingHom f = 0 := fun f hf =>
    Subtype.ext (aeval_aff_of_mem_primeOf hf)
  let ψ : Poly k N ⧸ primeOf (S := k) y →+* affRing k y j :=
    Ideal.Quotient.lift (primeOf (S := k) y) φ.toRingHom hker
  have hψ : Function.Surjective ψ := Ideal.Quotient.lift_surjective_of_surjective _ hker hφ
  let r : Poly k N ⧸ primeOf (S := k) y := Ideal.Quotient.mk _ (X j - 1)
  have hr : r ≠ 0 := by
    intro h
    have hmem : (X j - 1 : Poly k N) ∈ primeOf (S := k) y := Ideal.Quotient.eq_zero_iff_mem.mp h
    have h0 := homogeneousComponent_mem_primeOf y hmem 0
    rw [homogeneousComponent_zero] at h0
    have := (mem_primeOf_of_isHomogeneous y (isHomogeneous_C _ _)).mp h0
    simp at this
  have hr' : r ∈ nonZeroDivisors (Poly k N ⧸ primeOf (S := k) y) := mem_nonZeroDivisors_of_ne_zero hr
  have hψr : ψ r = 0 := by
    apply Subtype.ext
    change aeval (aff y j) (X j - 1 : Poly k N) = 0
    simp [aff, hj]
  have hrψ : ∀ a ∈ Ideal.span {r}, ψ a = 0 := by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul, hψr, mul_zero]
  have hχ : Function.Surjective (Ideal.Quotient.lift (Ideal.span {r}) ψ hrψ) :=
    Ideal.Quotient.lift_surjective_of_surjective _ hrψ hψ
  have h1 : ringKrullDim (affRing k y j) ≤
      ringKrullDim ((Poly k N ⧸ primeOf (S := k) y) ⧸ Ideal.span {r}) := by
    exact ringKrullDim_le_of_surjective _ hχ
  have h2 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr'
  rw [hy.dim] at h2
  have h3 : ringKrullDim (affRing k y j) ≤ 0 :=
    le_zero_of_add_one_le_one ((add_le_add h1 (le_refl (1 : WithBot ℕ∞))).trans (by simpa using h2))
  have : Ring.KrullDimLE 0 (affRing k y j) := Ring.krullDimLE_iff.mpr (by simpa using h3)
  exact Ring.KrullDimLE.isField_of_isDomain

theorem funField_eq (hj : y j ≠ 0) (hF : IsField (affRing k y j)) :
    funField (k := k) y = (affRing k y j).toIntermediateField' hF := by
  have haff : ∀ l, aff y j l ∈ (affRing k y j).toIntermediateField' hF := fun l =>
    show aff y j l ∈ affRing k y j from ⟨X l, by simp⟩
  apply le_antisymm
  · rw [funField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, l, hi, rfl⟩
    have : y l / y i = aff y j l * (aff y j i)⁻¹ := by
      simp only [aff]; field_simp
    rw [this]
    exact mul_mem (haff l) (inv_mem (haff i))
  · intro z hz
    change z ∈ affRing k y j at hz
    rw [affRing, ← Algebra.adjoin_range_eq_range_aeval] at hz
    refine Algebra.adjoin_le (S := (funField (k := k) y).toSubalgebra) ?_ hz
    rintro _ ⟨l, rfl⟩
    exact IntermediateField.subset_adjoin _ _ ⟨j, l, hj, rfl⟩

theorem finiteDimensional_affField (hy : IsSubvar y (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    FiniteDimensional k ((affRing k y j).toIntermediateField' (isField_affRing hy hj)) := by
  set E := (affRing k y j).toIntermediateField' (isField_affRing hy hj)
  let g : Poly k N →ₐ[k] E :=
    AlgHom.codRestrict (aeval (aff y j) : Poly k N →ₐ[k] Ω) E.toSubalgebra
      (fun f => show _ ∈ affRing k y j from ⟨f, rfl⟩)
  have hg : Function.Surjective g := by
    rintro ⟨z, f, rfl⟩
    exact ⟨f, rfl⟩
  have : Algebra.FiniteType k E := Algebra.FiniteType.of_surjective g hg
  exact finite_of_finite_type_of_isJacobsonRing k E

theorem affPiece_le (n : ℕ) : affPiece k y j n ≤ Subalgebra.toSubmodule (affRing k y j) :=
  Submodule.span_le.mpr (by rintro _ ⟨f, _, rfl⟩; exact ⟨f, rfl⟩)

theorem affPiece_mono (hj : y j ≠ 0) {m n : ℕ} (h : m ≤ n) :
    affPiece k y j m ≤ affPiece k y j n := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, hf, rfl⟩
  refine Submodule.subset_span ⟨X j ^ (n - m) * f, ?_, ?_⟩
  · have := (isHomogeneous_X_pow (R := k) j (n - m)).mul hf
    rwa [Nat.sub_add_cancel h] at this
  · simp [aff, hj]

theorem aeval_mem_affPiece (hj : y j ≠ 0) (f : Poly k N) :
    aeval (aff y j) f ∈ affPiece k y j f.totalDegree := by
  rw [show aeval (aff y j) f = ∑ d ∈ Finset.range (f.totalDegree + 1),
      aeval (aff y j) (homogeneousComponent d f) by rw [← map_sum, sum_homogeneousComponent]]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hd' : d ≤ f.totalDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hd)
  exact affPiece_mono hj hd' (Submodule.subset_span ⟨_, homogeneousComponent_isHomogeneous d f, rfl⟩)

theorem eventually_affPiece_eq (hy : IsSubvar y (primeOf (S := k) y) 0) (hj : y j ≠ 0) :
    ∀ᶠ n : ℕ in atTop, affPiece k y j n = Subalgebra.toSubmodule (affRing k y j) := by
  have := finiteDimensional_affField hy hj
  have hfin : (Subalgebra.toSubmodule (affRing k y j)).FG := by
    rw [← Module.Finite.iff_fg]
    exact inferInstanceAs (Module.Finite k ((affRing k y j).toIntermediateField' (isField_affRing hy hj)))
  obtain ⟨s, hs⟩ := hfin
  have hex : ∀ z ∈ s, ∃ n, z ∈ affPiece k y j n := fun z hz => by
    have : z ∈ affRing k y j := by
      rw [← Subalgebra.mem_toSubmodule, ← hs]; exact Submodule.subset_span hz
    obtain ⟨f, rfl⟩ := this
    exact ⟨_, aeval_mem_affPiece hj f⟩
  choose! m hm using hex
  refine eventually_atTop.mpr ⟨s.sup m, fun n hn => le_antisymm (affPiece_le n) ?_⟩
  rw [← hs, Submodule.span_le]
  intro z hz
  exact affPiece_mono hj ((Finset.le_sup hz).trans hn) (hm z hz)

theorem coordGraded_piece_eq (hj : y j ≠ 0) (n : ℕ) :
    (coordGraded k y).piece (n : ℤ) = (affPiece k y j n).map (LinearMap.mulLeft k (y j ^ n)) := by
  rw [show (coordGraded k y).piece (n : ℤ) = Submodule.span k {z | ∃ (f : Poly k N) (e : ℕ),
    f.IsHomogeneous e ∧ (e : ℤ) = n ∧ z = aeval y f} from rfl, affPiece, Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨f, e, hf, he, rfl⟩
    have hen : e = n := by exact_mod_cast he
    subst hen
    refine ⟨aeval (aff y j) f, ⟨f, hf, rfl⟩, ?_⟩
    rw [LinearMap.mulLeft_apply, aff_def, aeval_div_of_isHomogeneous hf]
    field_simp
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    refine ⟨f, n, hf, rfl, ?_⟩
    rw [LinearMap.mulLeft_apply, aff_def, aeval_div_of_isHomogeneous hf]
    field_simp

theorem coordGraded_le_secs (n : ℕ) :
    (coordGraded k y).piece (n : ℤ) ≤ (twistSys k y (n : ℤ)).secs := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, e, hf, he, rfl⟩
  refine (Submodule.mem_iInf _).mpr fun I => ?_
  exact Submodule.subset_span ⟨f, 1, 0, e, one_mem _, hf, isHomogeneous_one _ _, by simp [he],
    by simp⟩

theorem affRing_eq_ampleBase : affRing k y j = ampleBase (S := k) y j := by
  rw [affRing, ampleBase, Algebra.adjoin_range_eq_range_aeval]
  rfl

theorem div_mem_affRing_of_mem_twistMod (hj : y j ≠ 0) (n : ℕ) {z : Ω}
    (hz : z ∈ twistMod k y (n : ℤ) (singleChart hj)) : z / y j ^ n ∈ affRing k y j := by
  refine Submodule.span_induction (p := fun z _ => z / y j ^ n ∈ affRing k y j) ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨f, s, e, e', hs, hf, hse, hc, rfl⟩
    have hs' : s ∈ Submonoid.closure {(X j : Poly k N)} := by
      have : ((fun i => (X i : Poly k N)) '' ((({j} : Finset (Fin (N + 1))) : Set (Fin (N + 1))))) =
          {X j} := by simp
      rw [← this]; exact hs
    obtain ⟨m, rfl⟩ := Submonoid.mem_closure_singleton.mp hs'
    have hme : e = m := hse.inj_right (isHomogeneous_X_pow j m) (by
      rw [X_pow_eq_monomial, Ne, monomial_eq_zero]; exact one_ne_zero)
    subst hme
    have he' : e' = e + n := by omega
    subst he'
    refine ⟨f, ?_⟩
    change aeval (aff y j) f = _
    rw [aff_def, aeval_div_of_isHomogeneous hf, map_pow, aeval_X, pow_add, div_div]
  · simp
  · intro a b _ _ ha hb
    rw [add_div]; exact add_mem ha hb
  · intro c z _ hz
    rw [chartRing_smul_def, mul_div_assoc]
    refine mul_mem ?_ hz
    rw [affRing_eq_ampleBase]
    exact mem_ampleBase_of_mem_chartRing (S := k) hj c.2

theorem proof : HilbertPoint.Statement.{u, w} := by
  intro k _ Ω _ _ N y hy
  obtain ⟨j, hjX⟩ := hy.relevant
  have hj : y j ≠ 0 := fun h =>
    hjX ((mem_primeOf_of_isHomogeneous y (isHomogeneous_X k j)).mpr (by simp [h]))
  have hF := isField_affRing hy hj
  have hfun := funField_eq hj hF
  have hfd := finiteDimensional_affField hy hj
  have hev := eventually_affPiece_eq hy hj
  refine ⟨hfun ▸ hfd, hev.mono fun n hn => ?_, hev.mono fun n hn => ?_⟩
  · have hinj : Function.Injective (LinearMap.mulLeft k (y j ^ n)) :=
      mul_right_injective₀ (pow_ne_zero n hj)
    rw [coordGraded_piece_eq hj n,
      ← LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj _), hn,
      Subalgebra.finrank_toSubmodule, hfun, ← IntermediateField.finrank_eq_finrank_subalgebra]
    rfl
  · refine le_antisymm ?_ (coordGraded_le_secs n)
    intro z hz
    have hz1 : z ∈ twistMod k y (n : ℤ) (singleChart hj) :=
      (Submodule.mem_iInf _).mp hz (singleChart hj)
    have hd := div_mem_affRing_of_mem_twistMod hj n hz1
    rw [coordGraded_piece_eq hj n, hn]
    refine ⟨z / y j ^ n, hd, ?_⟩
    rw [LinearMap.mulLeft_apply]
    field_simp

end HilbertPoint

end

end GroundTheory.Heights₂.Heights.Kleiman
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeShift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open MvPolynomial

noncomputable section

universe u v w

section Tilde

variable {S : Type u} [CommRing S] {Ω : Type w} [Field Ω] [Algebra S Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
  {E : Type v} [AddCommGroup E] [Module Ω E] [Module S E] [IsScalarTower S Ω E]

omit [IsScalarTower S Ω E] in

theorem FinGradedSub.zpow_smul_mem_tilde (M : FinGradedSub (S := S) (x := x) E) {I : Chart x}
    {i : Fin (N + 1)} (hi : i ∈ I.1) (c d : ℤ) {y : E} (hy : y ∈ M.tilde d I) :
    x i ^ c • y ∈ M.tilde (d + c) I := by
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  refine Submodule.span_induction (p := fun y _ => x i ^ c • y ∈ M.tilde (d + c) I) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, s, a, e, hs, hse, hm, hae, rfl⟩
    have hs0 := eval_ne_zero_of_mem_monos I hs
    obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
    · refine Submodule.subset_span ⟨aeval x (X i ^ n : Poly S N) • m, s, a + n, e, hs, hse,
        M.smul_mem n a _ m (isHomogeneous_X_pow i n) hm, by omega, ?_⟩
      rw [smul_smul, smul_smul]
      congr 1
      simp only [map_pow, aeval_X, zpow_natCast]
      ring
    · refine Submodule.subset_span ⟨m, s * X i ^ n, a, e + n, mul_mem hs (pow_mem (X_mem_monos hi) n),
        hse.mul (isHomogeneous_X_pow i n), hm, by push_cast; omega, ?_⟩
      rw [smul_smul]
      congr 1
      simp only [map_mul, map_pow, aeval_X, zpow_neg, zpow_natCast, mul_inv]
      ring
  · rw [smul_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [smul_add]; exact Submodule.add_mem _ ha hb
  · intro a y _ hy
    have : x i ^ c • (a • y) = a • (x i ^ c • y) := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def, smul_smul, smul_smul, mul_comm]
    rw [this]
    exact Submodule.smul_mem _ a hy

theorem TildeShift.proof : TildeShift.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ M c
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  have hxi : x i ≠ 0 := (mem_support x).mp (I.2.2 hi)
  apply le_antisymm
  · intro y hy
    have h0 : x i ^ (-c) • y ∈ M.tilde 0 I := by
      simpa using M.zpow_smul_mem_tilde hi (-c) c hy
    refine Submodule.subset_span ⟨x i ^ c, ?_, x i ^ (-c) • y, h0, ?_⟩
    · change x i ^ c ∈ twistMod S x c I
      rw [twistMod_eq_span c I hi]
      exact Submodule.mem_span_singleton_self _
    · rw [smul_smul, ← zpow_add₀ hxi, add_neg_cancel, zpow_zero, one_smul]
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨q, hq, y, hy, rfl⟩
    change q ∈ twistMod S x c I at hq
    rw [twistMod_eq_span c I hi, Submodule.mem_span_singleton] at hq
    obtain ⟨a, rfl⟩ := hq
    have hy' : x i ^ c • y ∈ M.tilde c I := by
      simpa using M.zpow_smul_mem_tilde hi c 0 hy
    have : (a • x i ^ c) • y = a • (x i ^ c • y) := by
      rw [chartRing_smul_def, Subalgebra.smul_def, smul_smul]
    rw [SetLike.mem_coe, this]
    exact Submodule.smul_mem _ a hy'

end Tilde

end

end GroundTheory.Heights₂.Heights.Kleiman
end

