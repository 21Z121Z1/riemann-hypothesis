import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0052
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0050

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAlStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace' : ∀ (F : Type) [Field F] [Finite F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F) (f : F[X]) (y : AlgebraicClosure F), Irreducible f → aeval y f = 0 → Module.finrank F (LinearMap.ker (aeval (Matrix.toLin' M) f)) = f.natDegree * Module.finrank (AlgebraicClosure F) (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)))) y) := by
  first | exact @GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace | exact GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace | (intros; apply GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardMulFinrankEigenspaceLe
section
open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

theorem finrank_le_card_mul_finrank_eigenspace_le :
    ∀ (H K R : Type) [Group H] [Fintype H] [DecidableEq H] [Field K] [CommRing R] [Algebra K R]
      (st : H → R →ₐ[K] R), (∀ x, st 1 x = x) → (∀ h h' x, st (h * h') x = st h' (st h x)) →
      ∀ (χ : H →* Kˣ) (u : R),
      (Matrix.of fun h g : H => st (h * g) u).det ∈ nonZeroDivisors R →
      ∀ (Vm V Vp N : Submodule K R) [FiniteDimensional K Vm] [FiniteDimensional K V]
        [FiniteDimensional K Vp], (∀ h, ∀ x ∈ V, st h x ∈ V) →
      (∀ h, ∀ x ∈ Vm, x * st h u ∈ V) → (∀ h, ∀ x ∈ V, x * st h u ∈ Vp) →
      (∀ x, x ∈ N ↔ x ∈ V ∧ ∀ h, st h x = ((χ h : Kˣ) : K) • x) →
      Module.finrank K Vm ≤ Fintype.card H * Module.finrank K N ∧
        Fintype.card H * Module.finrank K N ≤ Module.finrank K Vp := by
  intro H K R _ _ _ _ _ _ st h1 hmul χ u hdet Vm V Vp N _ _ _ hV hm hp hN
  obtain ⟨hTr, hPhi, hPsi⟩ := GlobalTheory.twistedTrace_equivariant_and_injective_of_groupDet H K R st h1 hmul χ u hdet
  have hNV : N ≤ V := fun x hx => ((hN x).1 hx).1
  have : FiniteDimensional K N := Submodule.finiteDimensional_of_le hNV
  have hrk : Module.finrank K (H → N) = Fintype.card H * Module.finrank K N := by
    rw [Module.finrank_pi_fintype]
    simp
  rw [← hrk]
  constructor
  · have hmem : ∀ (f : Vm) (h : H),
        ∑ g, (((χ g)⁻¹ : Kˣ) : K) • st g ((f : R) * st h u) ∈ N := fun f h =>
      (hN _).2 ⟨V.sum_mem fun g _ => V.smul_mem _ (hV g _ (hm h _ f.2)), fun g => hTr _ g⟩
    let Φ : Vm →ₗ[K] (H → N) :=
      { toFun := fun f h => ⟨_, hmem f h⟩
        map_add' := fun f f' => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, map_add, smul_add, Finset.sum_add_distrib,
            Pi.add_apply]
        map_smul' := fun c f => by
          funext h
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, map_smul, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum]
          exact Finset.sum_congr rfl fun g _ => smul_comm _ _ _ }
    refine LinearMap.finrank_le_finrank_of_injective (f := Φ) ?_
    rw [injective_iff_map_eq_zero]
    intro f hf
    apply Subtype.ext
    exact hPhi f fun h => congrArg Subtype.val (congrFun hf h)
  · have hmem : ∀ F : H → N, ∑ h, (F h : R) * st h u ∈ Vp := fun F =>
      Vp.sum_mem fun h _ => hp h _ (hNV (F h).2)
    let Ψ : (H → N) →ₗ[K] Vp :=
      { toFun := fun F => ⟨_, hmem F⟩
        map_add' := fun F F' => by
          apply Subtype.ext
          simp only [Submodule.coe_add, add_mul, Finset.sum_add_distrib, Pi.add_apply]
        map_smul' := fun c F => by
          apply Subtype.ext
          simp only [Submodule.coe_smul, smul_mul_assoc, Pi.smul_apply,
            RingHom.id_apply, Finset.smul_sum] }
    refine LinearMap.finrank_le_finrank_of_injective (f := Ψ) ?_
    rw [injective_iff_map_eq_zero]
    intro F hF
    have := hPsi (fun h => (F h : R)) (fun h g => ((hN _).1 (F h).2).2 g)
      (congrArg Subtype.val hF)
    funext h
    exact Subtype.ext (congrFun this h)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankLeCardValuesStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_values_on_finrank_family : ∀ (C V Γ : Type) [Field C] [AddCommGroup V] [Module C V] [LinearOrder Γ] (ν : V → Γ), (∀ (c : C) (u : V), c ≠ 0 → ν (c • u) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u < ν v → u + v ≠ 0 ∧ ν (u + v) = ν u) → (∀ u v : V, u ≠ 0 → v ≠ 0 → ν u = ν v → ∃ c : C, u - c • v = 0 ∨ ν u < ν (u - c • v)) → ∀ (F : Submodule C V) [Module.Finite C F], ∃ f : Fin (Module.finrank C F) → V, (∀ i, f i ∈ F ∧ f i ≠ 0) ∧ Function.Injective (fun i => ν (f i)) := by
  first | exact @GlobalTheory.finrank_le_card_values | exact GlobalTheory.finrank_le_card_values | (intros; apply GlobalTheory.finrank_le_card_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankQuotOneSubIdempotentEqMulStatement
section
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_quot_one_sub_idempotent_eq_mul : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k) (e : A), IsIdempotentElem e → φ e = 1 → (∀ a, φ a = 0 → IsNilpotent (e * a)) → ∀ (H : Type u) [AddCommGroup H] [Module A H] [Module k H] [IsScalarTower k A H] [FiniteDimensional k H] [Module.Projective A H], Module.finrank k (H ⧸ (Ideal.span {1 - e} • ⊤ : Submodule A H)) = Module.finrank k (H ⧸ (RingHom.ker φ • ⊤ : Submodule A H)) * Module.finrank k (A ⧸ Ideal.span {1 - e}) := by
  first | (exact @GlobalTheory.finrank_quot_one_sub_idem_eq_mul) | (exact GlobalTheory.finrank_quot_one_sub_idem_eq_mul) | (intros; apply GlobalTheory.finrank_quot_one_sub_idem_eq_mul  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRangeMapIdempotentEqRankAtStalkStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_range_map_idempotent_eq_rankAtStalk : ∀ (A : Type) [CommRing A] (n : ℕ) (P : Matrix (Fin n) (Fin n) A), P * P = P →
    ∀ (k : Type) [Field k] (g : A →+* k),
      Module.finrank k (LinearMap.range (P.map g).mulVecLin) =
        Module.rankAtStalk (LinearMap.range P.mulVecLin) (⟨RingHom.ker g, RingHom.ker_isPrime g⟩ : PrimeSpectrum A) := by
  first | (exact @GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk) | (exact GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk) | (intros; apply GlobalTheory.IdemRankStalk.finrank_range_map_eq_rankAtStalk  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankZmodTensorHomologyZeroOfNoPTorsionStatement
section
open CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_zmod_tensor_homology_zero_of_noPTorsion : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (x : C.X 0), (p : ℤ) • x = 0 → x = 0) → Module.Finite ℤ (C.homology 0) → Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology 0)) = Module.finrank ℤ (C.homology 0) := by
  first | exact @GlobalTheory.finrank_zmod_tensor_homology_zero | exact GlobalTheory.finrank_zmod_tensor_homology_zero | (intros; apply GlobalTheory.finrank_zmod_tensor_homology_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsetMemRangeLocalizationAwayOfDvdStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finset_mem_range_localization_away_of_dvd : ∀ (R : Type) [CommRing R] (𝔭 : Ideal R) [𝔭.IsPrime] (F : Finset (Localization.AtPrime 𝔭)), ∃ s ∉ 𝔭, ∀ (c : R), s ∣ c → ∀ κ : Localization.Away c →+* Localization.AtPrime 𝔭, κ.comp (algebraMap R (Localization.Away c)) = algebraMap R (Localization.AtPrime 𝔭) → ∀ x ∈ F, x ∈ κ.range := by
  first | exact @GlobalTheory.finset_mem_range_of_away_dvd | exact GlobalTheory.finset_mem_range_of_away_dvd | (intros; apply GlobalTheory.finset_mem_range_of_away_dvd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumCompEqFinsumCardFiberMulStatement
section
open scoped Pointwise
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_comp_eq_finsum_card_fiber_mul : ∀ {X Y : Type} (π : X → Y) (h : Y → ℂ), ((∀ y, h y ≠ 0 → (π ⁻¹' {y}).Finite) ∨ (∀ y, h y ≠ 0 → Nat.card (π ⁻¹' {y}) = 0)) → ∑ᶠ x, h (π x) = ∑ᶠ y, (Nat.card (π ⁻¹' {y}) : ℂ) * h y := by
  first | exact @GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul | exact GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul | (intros; apply GlobalTheory.finsum_comp_eq_finsum_natCard_fiber_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumDoubleCosetEqFinprodLocalSumsStatement
section
open Filter
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_doubleCoset_eq_finprod_local_sums : ∀ (ι G : Type) [Group G] (H : ι → Type) [∀ i, Group (H i)] (p : ∀ i, G →* H i) (T K : Subgroup G) (TH KH : ∀ i, Subgroup (H i)) (s : G → ℂ) (s' : ∀ i, H i → ℂ), (∀ y : ∀ i, H i, (∀ᶠ i in cofinite, y i ∈ KH i) → ∃ x : G, ∀ i, p i x = y i) → (∀ x : G, ∀ᶠ i in cofinite, p i x ∈ KH i) → (∀ x : G, x ∈ K ↔ ∀ i, p i x ∈ KH i) → (∀ x, x ∈ T ↔ ∀ i, p i x ∈ TH i) → (∀ i, ∀ t ∈ TH i, ∀ k ∈ KH i, ∀ x, s' i (t * x * k) = s' i x) → (∀ i, {q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)) | s' i (Quotient.out q) ≠ 0}.Finite) → (∀ᶠ i in cofinite, ∀ x, s' i x = if ∃ t ∈ TH i, ∃ k ∈ KH i, x = t * k then 1 else 0) → (∀ g, s g = ∏ᶠ i, s' i (p i g)) → ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K : Set G), s (Quotient.out q) = ∏ᶠ i, ∑ᶠ q : DoubleCoset.Quotient (TH i : Set (H i)) (KH i : Set (H i)), s' i (Quotient.out q) := by
  first | exact @GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_eq_finprod_local | exact GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_eq_finprod_local | (intros; apply GlobalTheory.DoubleCosetEuler.finsum_doubleCoset_eq_finprod_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumFiberwiseOfFiniteSupportComplexStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finsum_fiberwise_of_finite_support_complex : ∀ {A B : Type} (ρ : A → B) (f : A → ℂ), (Function.support f).Finite → ∑ᶠ a, f a = ∑ᶠ b, ∑ᶠ a : {a // ρ a = b}, f a.1 := by
  first | exact @GlobalTheory.finsum_fiberwise_of_finite_support | exact GlobalTheory.finsum_fiberwise_of_finite_support | (intros; apply GlobalTheory.finsum_fiberwise_of_finite_support <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitRelFibredEquivariant
section
namespace GlobalTheory

open MulAction

theorem finsum_orbitRel_fibred : ∀ {H X B E : Type} [Group H] [MulAction H X] [MulAction H B] [MulAction H E] (π : X → B), (∀ (h : H) (x : X), π (h • x) = h • π x) → ∀ (S : B → Subgroup H), (∀ b : B, MulAction.stabilizer H b ≤ S b) → ∀ (j : B → E → X), (∀ b : B, Function.Injective (j b)) → (∀ (b : B) (e : E), π (j b e) = b) → (∀ (b : B) (x : X), π x = b → ∃ e : E, j b e = x) → (∀ (b : B), ∀ h ∈ S b, ∀ e : E, j b (h • e) = h • j b e) → ∀ (s : MulAction.orbitRel.Quotient H B → B), (∀ q, Quotient.mk (MulAction.orbitRel H B) (s q) = q) → ∀ (g : MulAction.orbitRel.Quotient H X → ℂ), (Function.support g).Finite → ∑ᶠ o, g o = ∑ᶠ q, ∑ᶠ o' : MulAction.orbitRel.Quotient (S (s q)) E, g (Quotient.mk (MulAction.orbitRel H X) (j (s q) (Quotient.out o'))) := by
  intro H X B E _ _ _ _ π hπ S hS j hinj hjπ hjsurj hjeq s hs g hg
  let ρ : orbitRel.Quotient H X → orbitRel.Quotient H B :=
    Quotient.map π (fun x y hxy => by
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hxy)
      exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨h, by rw [← hπ, hh]⟩))
  have hρ : ∀ x, ρ (Quotient.mk _ x) = Quotient.mk _ (π x) := fun x => rfl
  rw [GlobalTheory.finsum_fiberwise_of_finite_support ρ g hg]
  refine finsum_congr (fun q => ?_)
  set b := s q with hb

  have key : ∀ e e' : E, (orbitRel (S b) E) e e' →
      Quotient.mk (orbitRel H X) (j b e) = Quotient.mk (orbitRel H X) (j b e') := by
    intro e e' hee
    obtain ⟨k, hk⟩ := mem_orbit_iff.mp (orbitRel_apply.mp hee)
    apply Quotient.sound
    refine orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨(k : H), ?_⟩)
    rw [← hjeq b k k.2 e', ← hk]
    rfl
  let φ : orbitRel.Quotient (S b) E → {o // ρ o = q} := fun o' =>
    ⟨Quotient.mk _ (j b (Quotient.out o')), by rw [hρ, hjπ, hb, hs]⟩
  have hφ : Function.Bijective φ := by
    constructor
    · intro o₁ o₂ h12
      have h12' : Quotient.mk (orbitRel H X) (j b (Quotient.out o₁))
          = Quotient.mk (orbitRel H X) (j b (Quotient.out o₂)) := congrArg Subtype.val h12
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact h12'))
      have hbh : h • b = b := by
        have := congrArg π hh
        rwa [hπ, hjπ, hjπ] at this
      have hmem : h ∈ S b := hS b (mem_stabilizer_iff.mpr hbh)
      have he : h • Quotient.out o₂ = Quotient.out o₁ := by
        apply hinj b
        rw [hjeq b h hmem, hh]
      rw [← Quotient.out_eq o₁, ← Quotient.out_eq o₂]
      apply Quotient.sound
      exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨⟨h, hmem⟩, he⟩)
    · rintro ⟨o, ho⟩
      have hx : Quotient.mk (orbitRel H B) (π (Quotient.out o)) = Quotient.mk (orbitRel H B) b := by
        rw [← hρ, Quotient.out_eq, ho, hb, hs]
      obtain ⟨h, hh⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact hx))
      obtain ⟨e, he⟩ := hjsurj b (h⁻¹ • Quotient.out o) (by rw [hπ, ← hh, inv_smul_smul])
      refine ⟨Quotient.mk _ e, Subtype.ext ?_⟩
      show Quotient.mk (orbitRel H X) (j b (Quotient.out (Quotient.mk (orbitRel (S b) E) e))) = o
      rw [key _ e (Quotient.exact (Quotient.out_eq _)), he]
      conv_rhs => rw [← Quotient.out_eq o]
      apply Quotient.sound
      exact orbitRel_apply.mpr (mem_orbit_iff.mpr ⟨h⁻¹, rfl⟩)
  exact (finsum_comp_equiv (Equiv.ofBijective φ hφ) (f := fun o : {o // ρ o = q} => g o.1)).symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumOrbitsInvStabilizerCardMass
section
namespace GlobalTheory

open MulAction Function

theorem finsum_orbits_stabilizer_mass {K Z : Type} [Group K] [Finite K] [MulAction K Z]
    (f : Z → ℂ) (hf : ∀ (k : K) (z : Z), f (k • z) = f z) (hs : (Function.support f).Finite) :
    ∑ᶠ o : MulAction.orbitRel.Quotient K Z,
        ((Nat.card (MulAction.stabilizer K (Quotient.out o)) : ℕ) : ℂ)⁻¹ * f (Quotient.out o) =
      ((Nat.card K : ℕ) : ℂ)⁻¹ * ∑ᶠ z, f z := by
  classical
  let ρ : Z → orbitRel.Quotient K Z := fun z => Quotient.mk'' z

  have hmem : ∀ (o : orbitRel.Quotient K Z) (a : Z), ρ a = o ↔ a ∈ orbit K (Quotient.out o) := by
    intro o a
    constructor
    · intro h
      have : ρ a = ρ (Quotient.out o) := by rw [h]; exact (Quotient.out_eq' o).symm
      exact Quotient.exact this
    · intro h
      have : ρ a = ρ (Quotient.out o) := Quotient.sound h
      rw [this]; exact Quotient.out_eq' o
  have hfib : ∀ o : orbitRel.Quotient K Z,
      (∑ᶠ a : {a // ρ a = o}, f a.1) = (Nat.card (orbit K (Quotient.out o)) : ℂ) * f (Quotient.out o) := by
    intro o
    let e : {a // ρ a = o} ≃ orbit K (Quotient.out o) := Equiv.subtypeEquivRight (hmem o)
    haveI : Finite (orbit K (Quotient.out o)) := (Set.finite_range fun k : K => k • Quotient.out o).to_subtype
    haveI : Finite {a // ρ a = o} := Finite.of_equiv _ e.symm
    letI : Fintype {a // ρ a = o} := Fintype.ofFinite _
    have hc : ∀ a : {a // ρ a = o}, f a.1 = f (Quotient.out o) := by
      intro a
      obtain ⟨k, hk⟩ := (hmem o a.1).1 a.2
      rw [← hk]; exact hf _ _
    rw [finsum_eq_sum_of_fintype, Finset.sum_congr rfl (fun a _ => hc a), Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_congr e]
  have hcard : ∀ z : Z, Nat.card (orbit K z) * Nat.card (stabilizer K z) = Nat.card K := by
    intro z
    letI : Fintype K := Fintype.ofFinite K
    rw [← (stabilizer K z).index_mul_card, MulAction.index_stabilizer, Nat.card_coe_set_eq]
  rw [finsum_fiberwise_of_finite_support ρ f hs]
  simp_rw [hfib]
  rw [mul_finsum]
  apply finsum_congr
  intro o
  have h := hcard (Quotient.out o)
  haveI : Finite (orbit K (Quotient.out o)) := (Set.finite_range fun k : K => k • Quotient.out o).to_subtype
  haveI : Nonempty (orbit K (Quotient.out o)) := ⟨⟨_, mem_orbit_self _⟩⟩
  have h1 : (Nat.card (orbit K (Quotient.out o)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := orbit K (Quotient.out o))).ne'
  have h2 : (Nat.card (stabilizer K (Quotient.out o)) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := stabilizer K (Quotient.out o))).ne'
  rw [← h]; push_cast
  field_simp

end GlobalTheory
end

