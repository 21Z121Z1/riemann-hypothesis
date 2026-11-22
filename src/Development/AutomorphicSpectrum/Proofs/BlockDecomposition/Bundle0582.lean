import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0543
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0023
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.AdelicGaussians.UpperRightUnipotentInvariance
import GroundTheory.AutomorphicForms.ReductionFinite
import GroundTheory.AutomorphicForms.ReductionMahler
import GroundTheory.AutomorphicForms.ReductionSiegel
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0552
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.NotIsFinitePartOfBot
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootOfUnityCharacterPeriodic
section
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfWeight

open Finset

lemma ee_add (x y : ℂ) : ee (x + y) = ee x * ee y := by
  unfold ee
  rw [← Complex.exp_add]
  ring_nf

lemma ee_intCast (k : ℤ) : ee (k : ℂ) = 1 := by
  unfold ee
  rw [← Complex.exp_int_mul_two_pi_mul_I k]
  ring_nf

noncomputable def e1 (d : ℕ) (m : ℤ) : ℂ := ee ((m : ℂ) / d)

lemma root_of_unity_character_add (d : ℕ) (m k : ℤ) : e1 d (m + k) = e1 d m * e1 d k := by
  unfold e1
  rw [← ee_add]
  push_cast
  ring_nf

lemma root_of_unity_character_periodic (d : ℕ) (hd : 0 < d) (m k : ℤ) : e1 d (m + d * k) = e1 d m := by
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [root_of_unity_character_add]
  have : e1 d (d * k) = 1 := by
    unfold e1
    have : (((d : ℤ) * k : ℤ) : ℂ) / d = (k : ℂ) := by
      push_cast
      field_simp
    rw [this, ee_intCast]
  rw [this, mul_one]

lemma per_emod (f : ℤ → ℂ) (d : ℕ) (hf : ∀ x, f (x + d) = f x) (x : ℤ) : f (x % d) = f x := by
  have h : Function.Periodic f (d : ℤ) := hf
  have h2 := (h.int_mul (x / d)) (x % d)
  rw [← h2]
  congr 1
  rw [Int.emod_def]
  simp only [Int.cast_id]
  ring

lemma f_val (f : ℤ → ℂ) (d : ℕ) [NeZero d] (hf : ∀ x, f (x + d) = f x) (x : ℤ) :
    f (((x : ZMod d).val : ℕ) : ℤ) = f x := by
  rw [ZMod.val_intCast]
  exact per_emod f d hf x

lemma sum_range_zmod (d : ℕ) [NeZero d] (f : ℤ → ℂ) :
    ∑ x ∈ range d, f (x : ℤ) = ∑ y : ZMod d, f ((y.val : ℕ) : ℤ) := by
  symm
  refine Finset.sum_nbij' (fun y => y.val) (fun x => (x : ZMod d)) ?_ ?_ ?_ ?_ ?_
  · intro y _
    simpa using ZMod.val_lt y
  · intro x _
    simp
  · intro y _
    simp
  · intro x hx
    exact ZMod.val_cast_of_lt (by simpa using hx)
  · intro y _
    rfl

lemma sum_affine (d : ℕ) (hd : 0 < d) (f : ℤ → ℂ) (hf : ∀ x, f (x + d) = f x) (u t : ℤ)
    (hu : IsCoprime u (d : ℤ)) :
    ∑ x ∈ range d, f (u * (x : ℤ) + t) = ∑ x ∈ range d, f (x : ℤ) := by
  haveI : NeZero d := ⟨hd.ne'⟩
  have hU : IsUnit (u : ZMod d) := by
    obtain ⟨p, q, hpq⟩ := hu
    have h1 : ((p * u + q * d : ℤ) : ZMod d) = 1 := by rw [hpq]; simp
    push_cast at h1
    simp only [ZMod.natCast_self, mul_zero, add_zero] at h1
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h1)
  rw [sum_range_zmod d (fun x => f (u * x + t)), sum_range_zmod d f]
  let e : ZMod d → ZMod d := fun y => (u : ZMod d) * y + (t : ZMod d)
  have hinj : Function.Injective e := by
    intro y z hyz
    have : (u : ZMod d) * y = (u : ZMod d) * z := add_right_cancel hyz
    exact hU.mul_left_cancel this
  have he : Function.Bijective e := Finite.injective_iff_bijective.1 hinj
  rw [← he.sum_comp (fun y => f ((y.val : ℕ) : ℤ))]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h3 : e y = ((u * ((y.val : ℕ) : ℤ) + t : ℤ) : ZMod d) := by
    simp [e]
  rw [h3, f_val f d hf]

lemma sum_crt (M d : ℕ) (hM : 0 < M) (hd : 0 < d) (h : Nat.Coprime M d) (G : ℤ → ℂ)
    (hG : ∀ x, G (x + ((M * d : ℕ) : ℤ)) = G x) :
    ∑ x ∈ range (M * d), G (x : ℤ) =
      ∑ x1 ∈ range M, ∑ x2 ∈ range d, G ((d : ℤ) * x1 + M * x2) := by
  haveI : NeZero (M * d) := ⟨(Nat.mul_pos hM hd).ne'⟩
  rw [sum_range_zmod (M * d) G, ← Finset.sum_product']
  symm
  let i : ℕ × ℕ → ZMod (M * d) := fun p => ((d * p.1 + M * p.2 : ℕ) : ZMod (M * d))
  have hinj : Set.InjOn i (range M ×ˢ range d : Finset (ℕ × ℕ)) := by
    rintro ⟨x1, x2⟩ hx ⟨y1, y2⟩ hy hxy
    simp only [coe_product, Set.mem_prod, mem_coe, mem_range] at hx hy
    have hm : (d * x1 + M * x2) ≡ (d * y1 + M * y2) [MOD M * d] :=
      (ZMod.natCast_eq_natCast_iff _ _ _).1 hxy
    have h1 : (d * x1 + M * x2) ≡ (d * y1 + M * y2) [MOD M] := hm.of_mul_right d
    have h2 : (d * x1 + M * x2) ≡ (d * y1 + M * y2) [MOD d] := hm.of_mul_left M
    have h1' : d * x1 ≡ d * y1 [MOD M] := by
      simpa [Nat.ModEq] using h1
    have h2' : M * x2 ≡ M * y2 [MOD d] := by
      simpa [Nat.ModEq] using h2
    have e1' : x1 ≡ y1 [MOD M] := Nat.ModEq.cancel_left_of_coprime h h1'
    have e2' : x2 ≡ y2 [MOD d] := Nat.ModEq.cancel_left_of_coprime h.symm h2'
    have r1 := Nat.ModEq.eq_of_lt_of_lt e1' hx.1 hy.1
    have r2 := Nat.ModEq.eq_of_lt_of_lt e2' hx.2 hy.2
    simp [r1, r2]
  have hsurj : Set.SurjOn i (range M ×ˢ range d : Finset (ℕ × ℕ)) (univ : Finset (ZMod (M * d))) :=
    Finset.surjOn_of_injOn_of_card_le i (fun _ _ => mem_coe.2 (mem_univ _)) hinj
      (by simp [ZMod.card])
  refine Finset.sum_bij (fun p _ => i p) (fun _ _ => mem_univ _) (fun p hp q hq hpq => hinj hp hq hpq) ?_ ?_
  · intro y _
    obtain ⟨p, hp, hpy⟩ := hsurj (mem_coe.2 (mem_univ y))
    exact ⟨p, hp, hpy⟩
  · intro p _
    have : i p = (((d : ℤ) * p.1 + M * p.2 : ℤ) : ZMod (M * d)) := by
      simp [i]
    rw [this, f_val G (M * d) hG]

lemma inner_sum (M d : ℕ) (hd : 0 < d) (a b c' n : ℤ) (hcop : IsCoprime (M : ℤ) (d : ℤ))
    (hyp : a * d - b * (4 * (M : ℤ) ^ 2 * c') = 1) :
    ∑ x ∈ range d, e1 d (b * (M : ℤ) ^ 2 * (x : ℤ) ^ 2 + n * x) = e1 d (c' * n ^ 2) * GS b d := by
  have hper : ∀ (A B : ℤ) (x : ℤ), e1 d (A * (x + d) ^ 2 + B * (x + d)) = e1 d (A * x ^ 2 + B * x) := by
    intro A B x
    rw [← root_of_unity_character_periodic d hd (A * x ^ 2 + B * x) (A * (2 * x + d) + B)]
    congr 1
    ring
  have h1 := sum_affine d hd (fun x => e1 d (b * (M : ℤ) ^ 2 * x ^ 2 + n * x))
    (fun x => hper (b * (M : ℤ) ^ 2) n x) 1 (2 * c' * n)
    isCoprime_one_left
  have h2 := sum_affine d hd (fun x => e1 d (b * x ^ 2 + 0 * x))
    (fun x => hper b 0 x) M 0 hcop
  rw [← h1]
  have h3 : ∀ x : ℕ, e1 d (b * (M : ℤ) ^ 2 * (1 * (x : ℤ) + 2 * c' * n) ^ 2 + n * (1 * (x : ℤ) + 2 * c' * n)) =
      e1 d (c' * n ^ 2) * e1 d (b * ((M : ℤ) * x + 0) ^ 2 + 0 * ((M : ℤ) * x + 0)) := by
    intro x
    rw [← root_of_unity_character_add, ← root_of_unity_character_periodic d hd _ (-(a * (n * x + c' * n ^ 2)))]
    congr 1
    linear_combination (n * x + c' * n ^ 2) * (-hyp)
  rw [Finset.sum_congr rfl fun x _ => h3 x, ← Finset.mul_sum, h2]
  congr 1
  unfold GS e1
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  push_cast
  ring

theorem finite_sum_splitting : T2 := by
  intro M d _ ψ a b c' n hd hyp
  have hM : 0 < M := Nat.pos_of_ne_zero (NeZero.ne M)
  have hcop : IsCoprime (M : ℤ) (d : ℤ) := ⟨-(b * 4 * M * c'), a, by linear_combination hyp⟩
  have hnc : Nat.Coprime M d := Nat.isCoprime_iff_coprime.1 hcop
  let G : ℤ → ℂ := fun x => ψ (x : ZMod M) * e1 d (b * x ^ 2) * e1 (M * d) (n * x)
  have hG : ∀ x, G (x + ((M * d : ℕ) : ℤ)) = G x := by
    intro x
    have h1 : (((x + ((M * d : ℕ) : ℤ) : ℤ)) : ZMod M) = (x : ZMod M) := by
      simp
    have h2 : e1 d (b * (x + ((M * d : ℕ) : ℤ)) ^ 2) = e1 d (b * x ^ 2) := by
      rw [← root_of_unity_character_periodic d hd (b * x ^ 2) (b * (2 * x * M + (M : ℤ) ^ 2 * d))]
      congr 1
      push_cast
      ring
    have h3 : e1 (M * d) (n * (x + ((M * d : ℕ) : ℤ))) = e1 (M * d) (n * x) := by
      rw [← root_of_unity_character_periodic (M * d) (Nat.mul_pos hM hd) (n * x) n]
      congr 1
      ring
    simp only [G]
    rw [h1, h2, h3]
  have hL : ∑ x ∈ range (M * d), ψ (x : ZMod M) * ee (b * (x : ℂ) ^ 2 / d) *
      ee (n * x / ((M * d : ℕ) : ℂ)) = ∑ x ∈ range (M * d), G (x : ℤ) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    simp [G, e1]
  have hsplit : ∀ x1 x2 : ℕ, G ((d : ℤ) * x1 + M * x2) =
      ψ (d : ZMod M) * (ψ (x1 : ZMod M) * ee (n * x1 / M)) *
        e1 d (b * (M : ℤ) ^ 2 * (x2 : ℤ) ^ 2 + n * x2) := by
    intro x1 x2
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    have hM' : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
    have h1 : ((((d : ℤ) * x1 + M * x2 : ℤ)) : ZMod M) = (d : ZMod M) * (x1 : ZMod M) := by
      simp
    have h2 : e1 d (b * ((d : ℤ) * x1 + M * x2) ^ 2) = e1 d (b * (M : ℤ) ^ 2 * (x2 : ℤ) ^ 2) := by
      rw [← root_of_unity_character_periodic d hd (b * (M : ℤ) ^ 2 * (x2 : ℤ) ^ 2) (b * ((d : ℤ) * x1 ^ 2 + 2 * x1 * M * x2))]
      congr 1
      ring
    have h3 : e1 (M * d) (n * ((d : ℤ) * x1 + M * x2)) = ee (n * x1 / M) * e1 d (n * x2) := by
      unfold e1
      rw [← ee_add]
      congr 1
      push_cast
      field_simp
    simp only [G]
    rw [h1, h2, h3, root_of_unity_character_add, map_mul]
    ring
  rw [hL, sum_crt M d hM hd hnc G hG]
  simp only [hsplit]
  simp only [← Finset.mul_sum]
  rw [inner_sum M d hd a b c' n hcop hyp, ← Finset.sum_mul, ← Finset.mul_sum]
  have hc : e1 d (c' * n ^ 2) = ee (c' * (n : ℂ) ^ 2 / d) := by
    unfold e1
    push_cast
    rfl
  rw [hc]
  ring

end GlobalTheory.CompanionTheory.HalfWeight
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScaledIntegralHermitianInOpenSubgroup
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

noncomputable section
namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open Topology

theorem exists_den {F : Type} [Field F] [NumberField F] (y : F) :
    ∃ D : ℕ, 0 < D ∧ ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y := by
  have hal : IsAlgebraic ℤ y :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨z, hz, hint⟩ := hal.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.mpr hz, ?_⟩
  have hint' : IsIntegral ℤ ((z.natAbs : F) * y) := by
    rcases Int.natAbs_eq z with h | h
    · have : ((z.natAbs : F) * y) = z • y := by
        rw [zsmul_eq_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rwa [this]
    · have : ((z.natAbs : F) * y) = -(z • y) := by
        rw [zsmul_eq_mul, ← neg_mul]
        congr 1
        conv_rhs => rw [h]
        simp
      rw [this]
      exact hint.neg
  exact ⟨IsIntegralClosure.mk' (𝓞 F) _ hint', IsIntegralClosure.algebraMap_mk' _ _ _⟩

theorem exists_common_den {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (y : ι → F) :
    ∃ D : ℕ, 0 < D ∧ ∀ i, ∃ r : 𝓞 F, algebraMap (𝓞 F) F r = (D : F) * y i := by
  choose D hD r hr using fun i => exists_den (y i)
  refine ⟨∏ i, D i, Finset.prod_pos fun i _ => hD i, fun i => ?_⟩
  obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem D (Finset.mem_univ i)
  refine ⟨(m : 𝓞 F) * r i, ?_⟩
  rw [hm, map_mul, hr, map_natCast]
  push_cast
  ring

theorem coords_den {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {d : ℕ} (b : Module.Basis (Fin d) F E) :
    ∃ D : ℕ, 0 < D ∧ ∀ (o : 𝓞 E) (k : Fin d), ∃ r : 𝓞 F,
      algebraMap (𝓞 F) F r = (D : F) * b.repr (algebraMap (𝓞 E) E o) k := by
  let e := RingOfIntegers.basis E
  obtain ⟨D, hD, h⟩ := exists_common_den (F := F)
    (fun p : Module.Free.ChooseBasisIndex ℤ (𝓞 E) × Fin d => b.repr (algebraMap (𝓞 E) E (e p.1)) p.2)
  refine ⟨D, hD, fun o k => ?_⟩
  choose r hr using h
  refine ⟨∑ i, (e.repr o i) • r (i, k), ?_⟩
  have ho : algebraMap (𝓞 E) E o = ∑ i, (e.repr o i) • algebraMap (𝓞 E) E (e i) := by
    conv_lhs => rw [← e.sum_repr o]
    simp [map_sum]
  rw [ho, map_sum, map_sum, Finsupp.finset_sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, map_zsmul, Finsupp.smul_apply, hr (i, k)]
  simp only [zsmul_eq_mul]
  ring

theorem nhds_unif {ι Y : Type} [Finite ι] [TopologicalSpace Y] (y0 : Y) (W : Set (ι → Y))
    (hW : W ∈ 𝓝 (fun _ => y0)) : ∃ V ∈ 𝓝 y0, ∀ y : ι → Y, (∀ i, y i ∈ V) → y ∈ W := by
  rw [nhds_pi, Filter.mem_pi'] at hW
  obtain ⟨I, t, ht, hsub⟩ := hW
  refine ⟨⋂ i, t i, Filter.iInter_mem.mpr ht, fun y hy => hsub ?_⟩
  intro i _
  exact Set.mem_iInter.mp (hy i) i

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens

open Topology

theorem exists_smul_mem_open : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (U : AddSubgroup (HermR (Af F) σ n)), IsOpen (U : Set (HermR (Af F) σ n)) →
    ∀ t : F, t ≠ 0 → ∃ τ : ℕ, 0 < τ ∧ ∀ c ∈ hermO σ n, hermIn (Af F) σ n (((τ : F) / t) • c) ∈ U := by
  intro F E _ _ _ _ _ σ hcm n U hU t ht
  obtain ⟨-, hSC, hT2, -, -, -, hF, hN, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : SecondCountableTopology (Af F) := hSC
  haveI : T2Space (Af F) := hT2
  haveI : LocallyCompactSpace (Af F) := (GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F).1
  obtain ⟨-, -, -, -, -, -, hH, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Af F)
  let b := Module.finBasis F E
  have hh := hH _ b
  set h := hh.homeomorph with hdef
  have happ : ∀ (y : Af F ⊗[F] E) k, h y k = (Algebra.TensorProduct.basis (Af F) b).repr y k :=
    fun _ _ => rfl
  obtain ⟨U', hU'o, hU'⟩ := isOpen_induced_iff.mp hU
  let G : (Fin n × Fin n × Fin (Module.finrank F E) → Af F) →
      Matrix (Fin n) (Fin n) (Af F ⊗[F] E) :=
    fun x a c => h.symm (fun k => x (a, c, k))
  have hG : Continuous G := by
    refine continuous_matrix fun a c => ?_
    exact h.symm.continuous.comp (continuous_pi fun k => continuous_apply _)
  have hG0 : G (fun _ => 0) = 0 := by
    ext a c
    apply h.injective
    show h (h.symm _) = h 0
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    simp
  have h0 : (0 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) ∈ U' := by
    have h1 : (0 : HermR (Af F) σ n) ∈ (U : Set (HermR (Af F) σ n)) := U.zero_mem
    rw [← hU'] at h1
    exact h1
  have hW : G ⁻¹' U' ∈ 𝓝 (fun _ => (0 : Af F)) :=
    (hU'o.preimage hG).mem_nhds (by rw [Set.mem_preimage, hG0]; exact h0)
  obtain ⟨V, hV, hVW⟩ := nhds_unif _ _ hW
  obtain ⟨N, hNpos, hNV⟩ := hN V hV
  obtain ⟨D₁, hD₁, p, hp⟩ := exists_den (t⁻¹)
  obtain ⟨D₂, hD₂, hco⟩ := coords_den b
  refine ⟨D₁ * D₂ * N, by positivity, fun c hc => ?_⟩
  let y : Fin n × Fin n × Fin (Module.finrank F E) → Af F := fun q =>
    algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 q.1 q.2.1) q.2.2)
  have hy : ∀ q, y q ∈ V := by
    rintro ⟨a, a', k⟩
    obtain ⟨o, ho⟩ := hc a a'
    obtain ⟨r, hr⟩ := hco o k
    have hval : b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k
        = (N : F) * (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) := by
      have : (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a')
          = (((D₁ * D₂ * N : ℕ) : F) / t) • algebraMap (𝓞 E) E o := by
        rw [ho]; rfl
      rw [this, map_smul, Finsupp.smul_apply, hp, hr, smul_eq_mul, div_eq_mul_inv]
      push_cast
      ring
    have hmem : algebraMap F (Af F) (algebraMap (𝓞 F) F p * algebraMap (𝓞 F) F r) ∈
        GlobalTheory.CompanionTheory.SW.Core.Oh F := (hF _).mpr ⟨p * r, by simp⟩
    have := hNV _ hmem
    show algebraMap F (Af F) (b.repr (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') k) ∈ V
    rw [hval, map_mul, map_natCast]
    exact this
  have hGy : G y ∈ U' := hVW y hy
  have heq : G y = (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 := by
    ext a a'
    apply h.injective
    show h (h.symm _) = _
    rw [h.apply_symm_apply]
    funext k
    rw [happ]
    show y (a, a', k) = _
    have hentry : (hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c)).1 a a' =
        (1 : Af F) ⊗ₜ[F] (((((D₁ * D₂ * N : ℕ) : F) / t) • c).1 a a') := rfl
    rw [hentry, Algebra.TensorProduct.basis_repr_tmul]
    simp only [Finsupp.smul_apply, one_smul, Finsupp.mapRange_apply]
    rfl
  have hfin : hermIn (Af F) σ n ((((D₁ * D₂ * N : ℕ) : F) / t) • c) ∈ (U : Set (HermR (Af F) σ n)) := by
    rw [← hU']
    show _ ∈ U'
    rw [← heq]
    exact hGy
  exact hfin

end GlobalTheory.CompanionTheory.SiegelND.Integ.Hua.Commens
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothCutoffTranslateContDiff
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows PositivityTheory.AdelicQuotientData GroundTheory.Automorphic.FourierWhittaker GlobalTheory.CompanionTheory.CutOff
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.CutOff

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ}

theorem contDiff_lastEnt : ContDiff ℝ ∞ (lastEnt : (Fin k → Cinf E) → Cinf E) := by
  unfold lastEnt
  refine ContDiff.sum fun c _ => ?_
  by_cases h : (c : ℕ) + 1 = k
  · simp only [if_pos h]
    exact contDiff_apply ℝ (Cinf E) c
  · simp only [if_neg h]
    exact contDiff_const

theorem isOpen_lastEnt_unit : IsOpen {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
  (Units.isOpen (R := Cinf E)).preimage (contDiff_lastEnt (E := E)).continuous

theorem contDiffOn_inverse_lastEnt :
    ContDiffOn ℝ ∞ (fun x : Fin k → Cinf E => Ring.inverse (lastEnt x))
      {x | IsUnit (lastEnt x)} := by
  intro x hx
  obtain ⟨u, hu⟩ := hx
  have h1 : ContDiffAt ℝ ∞ (Ring.inverse : Cinf E → Cinf E) (lastEnt x) := by
    rw [← hu]; exact contDiffAt_ringInverse ℝ u
  exact (h1.comp x (contDiff_lastEnt (E := E)).contDiffAt).contDiffWithinAt

def tauM (x : Fin k → Cinf E) : LieI (InfinitePlace E) k := Matrix.of.symm (rowM (rowI x))

theorem contDiffOn_tauM :
    ContDiffOn ℝ ∞ (tauM : (Fin k → Cinf E) → LieI (InfinitePlace E) k)
      {x | IsUnit (lastEnt x)} := by
  refine contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun c => ?_
  have hinv := contDiffOn_inverse_lastEnt (E := E) (k := k)
  by_cases hi : (i : ℕ) + 1 = k
  · have e : ∀ x : Fin k → Cinf E, tauM x i c = rowI x c := fun x => rowM_apply_last _ i c hi
    simp only [e]
    by_cases hc : (c : ℕ) + 1 = k
    · simp only [rowI, if_pos hc]
      exact hinv
    · simp only [rowI, if_neg hc]
      exact ((contDiff_apply ℝ (Cinf E) c).contDiffOn.mul hinv).neg
  · have e : ∀ x : Fin k → Cinf E, tauM x i c = (1 : Matrix (Fin k) (Fin k) (Cinf E)) i c :=
      fun x => rowM_apply_ne _ i c hi
    simp only [e]
    exact contDiffOn_const

theorem tauM_isUnit {x : Fin k → Cinf E} (h : IsUnit (lastEnt x)) :
    IsUnit (Matrix.of (tauM x)) := by
  have e : Matrix.of (tauM x) = (((rowGL x)⁻¹ : GL (Fin k) (Cinf E)) : Matrix (Fin k) (Fin k) (Cinf E)) :=
    (rowGL_inv_val h).symm
  rw [e]
  exact Units.isUnit _

theorem rt_inv_eq_orb (φ : XB E k) {x : Fin k → Cinf E} (h : IsUnit (lastEnt x)) :
    Rt E k (infGL E k (rowGL x))⁻¹ φ = orb (repI E k) φ (tauM x) := by
  have hu := tauM_isUnit h
  have e : hu.unit = (rowGL x)⁻¹ := Units.ext (by
    rw [IsUnit.unit_spec]; exact (rowGL_inv_val h).symm)
  rw [orb, dif_pos hu, e]
  change _ = Rt E k (infGL E k (rowGL x)⁻¹) φ
  rw [map_inv (infGL E k)]

theorem contDiff_cut_orbit {φ : XB E k} (hφ : SmV (repI E k) φ) {b : (Fin k → Cinf E) → ℝ}
    (hb : ContDiff ℝ ∞ b) (hs : ∀ x ∈ tsupport b, IsUnit (lastEnt x)) :
    ContDiff ℝ ∞ fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ := by
  have hO := isOpen_lastEnt_unit (E := E) (k := k)
  have hbc : ContDiff ℝ ∞ fun x => (b x : ℂ) := Complex.ofRealCLM.contDiff.comp hb
  have horb : ContDiffOn ℝ ∞ (fun x => orb (repI E k) φ (tauM x)) {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
    ContDiffOn.comp hφ contDiffOn_tauM fun x hx => tauM_isUnit hx
  have hF : ContDiffOn ℝ ∞ (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ)
      {x : Fin k → Cinf E | IsUnit (lastEnt x)} :=
    (hbc.contDiffOn.smul horb).congr fun x hx => by
      rw [rt_inv_eq_orb φ hx]
      rfl
  refine contDiff_iff_contDiffAt.2 fun x => ?_
  by_cases hx : x ∈ tsupport b
  · exact hF.contDiffAt (hO.mem_nhds (hs x hx))
  · have e : (fun x => (b x : ℂ) • Rt E k (infGL E k (rowGL x))⁻¹ φ) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hx] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq e

end GlobalTheory.CompanionTheory.CutOff

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableLatticeWeightThreeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.GA
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.summable_lattice_weight_three : ∀ M : ℕ, 0 < M → Summable (fun p : ℚ × ℚ × ℚ => if ((M : ℚ) * p.1).den = 1 ∧ ((M : ℚ) * p.2.1).den = 1 ∧ ((M : ℚ) * p.2.2).den = 1 then ((1 + |(p.1 : ℝ)| + |(p.2.1 : ℝ)|) ^ 3 * (1 + |(p.2.2 : ℝ)|) ^ 2)⁻¹ else (0 : ℝ)) := by
  first | exact @GlobalTheory.CompanionTheory.MajSum.summable_lattice_majorant | exact GlobalTheory.CompanionTheory.MajSum.summable_lattice_majorant | (intros; apply GlobalTheory.CompanionTheory.MajSum.summable_lattice_majorant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TestFunctionDerivativeIsTestStatement
section
open NumberField MeasureTheory Topology Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.DiscreteSum GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.DiscSpec GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CompanionTheory.SmoothRep
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.test_function_derivative_is_test : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (β : Lie E a → ℂ), IsTest β → ∀ X : Lie E a, IsTest (dTest X β) := by
  first | exact @GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest | exact GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest | (intros; apply GlobalTheory.CompanionTheory.SmoothRep.isTest_dTest <;> assumption)
end

