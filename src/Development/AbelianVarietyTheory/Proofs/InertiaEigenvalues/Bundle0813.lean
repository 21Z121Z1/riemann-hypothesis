import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0696
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0141
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterGoodIdempotentCuspidalProduc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelSurjective.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0381
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAuxiliaryPlaceFamilyAtLevelMono
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0008
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0809
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNsmulMemOfSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.LatSandwich

variable {E : Type} [Field E] [NumberField E]

theorem exists_nsmul_le {W : Type} [AddCommGroup W] [Module (𝓞 E) W] (s : Finset W) (M : Submodule (𝓞 E) W)
    (h : ∀ x ∈ s, ∃ k : ℕ, 0 < k ∧ k • x ∈ M) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ Submodule.span (𝓞 E) (s : Set W), k • x ∈ M := by
  classical
  choose! n hn hn' using h
  refine ⟨∏ t ∈ s, n t, Finset.prod_pos fun t ht => hn t ht, fun m hm => ?_⟩
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem n (Finset.mem_coe.1 hx)
    rw [hk, mul_comm, mul_smul]
    exact M.nsmul_mem (hn' x (Finset.mem_coe.1 hx)) k
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact M.smul_mem a hx

theorem exists_nat_mul_isIntegral (z : E) : ∃ k : ℕ, 0 < k ∧ IsIntegral ℤ ((k : E) * z) := by
  have hal : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic z)
  obtain ⟨y, hy, hi⟩ := hal.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rw [zsmul_eq_mul] at hi
  rcases Int.natAbs_eq y with e | e
  · rw [hc, ← e]; exact hi
  · rw [hc, show ((y.natAbs : ℤ)) = -y by omega, Int.cast_neg, neg_mul]; exact hi.neg

theorem mem_stdLat_iff {n : ℕ} (x : Fin n → E) : x ∈ Formalism.L2.Pj.stdLat E n ↔ ∀ i, IsIntegral ℤ (x i) := by
  simp only [Formalism.L2.Pj.stdLat, Submodule.mem_pi, Set.mem_univ, true_implies, Submodule.mem_one]
  refine forall_congr' fun i => ⟨?_, fun h => ⟨⟨x i, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]
  exact RingOfIntegers.isIntegral_coe y

theorem exists_nsmul_mem_stdLat {n : ℕ} (v : Fin n → E) : ∃ k : ℕ, 0 < k ∧ k • v ∈ Formalism.L2.Pj.stdLat E n := by
  classical
  obtain ⟨k, hk, h⟩ := exists_nsmul_le (Finset.univ.image fun i => Pi.single i (v i)) (Formalism.L2.Pj.stdLat E n) (by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]
    intro i
    obtain ⟨k, hk, hi⟩ := exists_nat_mul_isIntegral (v i)
    refine ⟨k, hk, (mem_stdLat_iff _).2 fun j => ?_⟩
    by_cases e : j = i
    · subst e
      simpa [nsmul_eq_mul] using hi
    · simp [Pi.single_eq_of_ne e, isIntegral_zero])
  refine ⟨k, hk, h v ?_⟩
  have hs : ∑ i, Pi.single i (v i) ∈ Submodule.span (𝓞 E) ((Finset.univ.image fun i => Pi.single i (v i) : Finset (Fin n → E)) : Set (Fin n → E)) :=
    Submodule.sum_mem _ fun i _ => Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun i => Pi.single i (v i)) (Finset.mem_univ i)))
  rwa [Finset.univ_sum_single v] at hs

theorem exists_nsmul_mem_of_span {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E))
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) (v : Fin n → E) : ∃ k : ℕ, 0 < k ∧ k • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (Λ : Set (Fin n → E)) := by rw [hsp]; exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, ha, hy⟩ := hy
    obtain ⟨b, hb, hz⟩ := hz
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [smul_add]
    refine add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Λ.nsmul_mem hy _
    · rw [mul_smul]; exact Λ.nsmul_mem hz _
  | smul a y _ hy =>
    obtain ⟨m, hm, hy⟩ := hy
    obtain ⟨c, hc, hi⟩ := exists_nat_mul_isIntegral a
    refine ⟨c * m, Nat.mul_pos hc hm, ?_⟩
    have h := Λ.smul_mem (⟨(c : E) * a, hi⟩ : 𝓞 E) hy
    convert h using 1
    funext j
    change (c * m) • (a * y j) = ((c : E) * a) * (m • y j)
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring

end GlobalTheory.LatSandwich

namespace GlobalTheory.LatSandwich

variable {E : Type} [Field E] [NumberField E]

theorem sandwich_of_fg {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (hfg : Λ.FG)
    (hsp : Submodule.span E (Λ : Set (Fin n → E)) = ⊤) :
    ∃ a : ℕ, 0 < a ∧ (∀ x ∈ Formalism.L2.Pj.stdLat E n, (a : 𝓞 E) • x ∈ Λ) ∧
      ∀ x ∈ Λ, (a : 𝓞 E) • x ∈ Formalism.L2.Pj.stdLat E n := by
  classical
  obtain ⟨T, hT⟩ := hfg
  obtain ⟨d, hd, hup⟩ := exists_nsmul_le T (Formalism.L2.Pj.stdLat E n) fun x _ => exists_nsmul_mem_stdLat x
  obtain ⟨d', hd', hlo⟩ := exists_nsmul_le (Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → E)) Λ
    fun x _ => exists_nsmul_mem_of_span Λ hsp x
  refine ⟨d * d', Nat.mul_pos hd hd', fun x hx => ?_, fun x hx => ?_⟩
  · rw [Nat.cast_smul_eq_nsmul, mul_smul]
    refine Λ.nsmul_mem (hlo x ?_) d
    have hint := (mem_stdLat_iff x).1 hx
    have hs : ∑ i, (⟨x i, hint i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) ∈ Submodule.span (𝓞 E)
        ((Finset.univ.image fun i : Fin n => (Pi.single i 1 : Fin n → E) : Finset (Fin n → E)) : Set (Fin n → E)) :=
      Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span (Finset.mem_coe.2 (Finset.mem_image_of_mem (fun i : Fin n => (Pi.single i 1 : Fin n → E)) (Finset.mem_univ i))))
    have e : ∑ i, (⟨x i, hint i⟩ : 𝓞 E) • (Pi.single i 1 : Fin n → E) = x := by
      conv_rhs => rw [← Finset.univ_sum_single x]
      refine Finset.sum_congr rfl fun i _ => ?_
      funext j
      by_cases h : j = i
      · subst h
        change x j * (Pi.single j 1 : Fin n → E) j = _
        simp
      · change x i * (Pi.single i 1 : Fin n → E) j = _
        simp [Pi.single_eq_of_ne h]
    rwa [e] at hs
  · rw [Nat.cast_smul_eq_nsmul, mul_comm, mul_smul]
    exact nsmul_mem (hup x (hT ▸ hx)) d'

end GlobalTheory.LatSandwich

namespace GlobalTheory.LatSandwich

theorem sandwich : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), (∀ x, x ∈ Λ ↔ x ∈ L0c D V) →
    ∃ a : ℕ, 0 < a ∧ (∀ x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank, (a : 𝓞 D.host.E) • x ∈ Λ) ∧
      ∀ x ∈ Λ, (a : 𝓞 D.host.E) • x ∈ Formalism.L2.Pj.stdLat D.host.E V.rank := by
  intro D V Λ hΛ
  have e : Λ = V.L0.map (V.frame.equivFun.restrictScalars (𝓞 D.host.E)).toLinearMap := by
    ext x
    rw [hΛ, Submodule.mem_map]
    constructor
    · intro hx
      refine ⟨V.frame.equivFun.symm x, ?_, V.frame.equivFun.apply_symm_apply x⟩
      rw [V.frame.equivFun_symm_apply]
      exact hx
    · rintro ⟨y, hy, rfl⟩
      change ∑ i, V.frame.equivFun y i • V.frame i ∈ V.L0
      rw [V.frame.sum_equivFun]
      exact hy
  refine sandwich_of_fg Λ (e ▸ V.standardTuple_isLattice.fg.map _) ?_
  have hs : (Λ : Set (Fin V.rank → D.host.E)) = V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) := by
    rw [e]; rfl
  rw [hs, ← Submodule.map_span, V.standardTuple_isLattice.span_eq_top, Submodule.map_top, LinearEquiv.range]

end GlobalTheory.LatSandwich
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRightInverseCentralProjectorUnitElement
section
open GlobalTheory.MeetsGen CategoryTheory

noncomputable section

namespace GlobalTheory.MeetsUnit

variable {G : Type} [Group G] [Fintype G]

theorem single_mul_cU (U : Subgroup G) [Fintype U] (f : U → ℂ) (h : G) :
    MonoidAlgebra.single h (1 : ℂ) * cU U f = cU U f * MonoidAlgebra.single h 1 := by
  unfold cU
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Fintype.sum_equiv (Equiv.mulLeft h) _ _ (fun g => ?_)
  have e1 : MonoidAlgebra.single (h * g) (1 : ℂ) = MonoidAlgebra.single h 1 * MonoidAlgebra.single g 1 := by
    rw [MonoidAlgebra.single_mul_single, one_mul]
  have e2 : MonoidAlgebra.single (h * g)⁻¹ (1 : ℂ) * MonoidAlgebra.single h 1 = MonoidAlgebra.single g⁻¹ 1 := by
    rw [MonoidAlgebra.single_mul_single, one_mul, mul_inv_rev, inv_mul_cancel_right]
  simp only [Equiv.coe_mulLeft]
  rw [mul_assoc _ (MonoidAlgebra.single (h * g)⁻¹ (1 : ℂ)), e2, e1]
  simp only [mul_assoc]

theorem single_mul_uElt (U : Subgroup G) [Fintype U] (f : U → ℂ) (e : MonoidAlgebra ℂ G)
    (hC : ∀ a, e * a = a * e) (h : G) :
    MonoidAlgebra.single h (1 : ℂ) * uElt U f e = uElt U f e * MonoidAlgebra.single h 1 := by
  have hc := single_mul_cU U f h
  have he := hC (MonoidAlgebra.single h 1)
  simp only [uElt, mul_add, add_mul, mul_sub, sub_mul, mul_one, one_mul]
  rw [he, mul_assoc (cU U f) e, he, ← mul_assoc, ← mul_assoc, hc]

theorem trace_cU (V : FDRep ℂ G) (U : Subgroup G) [Fintype U] (f : U → ℂ) :
    LinearMap.trace ℂ V (Representation.asAlgebraHom V.ρ (cU U f)) =
      (Fintype.card G : ℂ) * ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) * V.character u := by
  have hp : Representation.asAlgebraHom V.ρ (pU U f) = ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) • V.ρ u := by
    simp only [pU, map_sum, Representation.asAlgebraHom_single]
  unfold cU
  rw [map_sum, map_sum]
  rw [Finset.sum_congr rfl (fun g _ => by
    rw [map_mul (Representation.asAlgebraHom V.ρ), map_mul (Representation.asAlgebraHom V.ρ), Representation.asAlgebraHom_single, Representation.asAlgebraHom_single, one_smul,
      one_smul, LinearMap.trace_mul_comm ℂ, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul])]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hp, map_sum]
  simp only [map_smul, smul_eq_mul, FDRep.character]

def lreg : Representation ℂ G (MonoidAlgebra ℂ G) :=
  (Algebra.lmul ℂ (MonoidAlgebra ℂ G)).toRingHom.toMonoidHom.comp (MonoidAlgebra.of ℂ G)

theorem lreg_apply (g : G) (x : MonoidAlgebra ℂ G) : lreg g x = MonoidAlgebra.single g 1 * x := rfl

theorem exists_rightInv_uElt : ∀ {G : Type} [Group G] [Fintype G] (U : Subgroup G) [Fintype U] (ψ : U →* ℂˣ)
    (e : MonoidAlgebra ℂ G), e * e = e → (∀ a, e * a = a * e) →
    (∀ χ : G → ℂ, Formalism.L2.NT.IsIrrChar χ → ∑ g, e.coeff g * χ g = χ 1 →
      ∑ u : U, χ u * (((ψ u)⁻¹ : ℂˣ) : ℂ) ≠ 0) →
    ∃ v : MonoidAlgebra ℂ G, uElt U (fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ)) e * v = 1 := by
  intro G _ _ U _ ψ e hI hC hχ
  classical
  set f : U → ℂ := fun u => (((ψ u)⁻¹ : ℂˣ) : ℂ) with hf
  set w := uElt U f e with hw
  have hinj : Function.Injective (LinearMap.mulLeft ℂ w) := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro y hy
    by_contra hy0
    let K : Submodule ℂ (MonoidAlgebra ℂ G) := LinearMap.ker (LinearMap.mulLeft ℂ w)
    have hK : ∀ x, x ∈ K ↔ w * x = 0 := fun x => LinearMap.mem_ker
    let A : Subrepresentation (lreg (G := G)) := ⟨K, fun g x hx => by
      rw [hK] at hx ⊢
      rw [lreg_apply, ← mul_assoc, ← single_mul_uElt U f e hC g, mul_assoc, hx, mul_zero]⟩
    haveI : Nontrivial A.toSubmodule :=
      Submodule.nontrivial_iff_ne_bot.2 (fun hb => hy0 ((Submodule.eq_bot_iff _).1 hb y hy))
    obtain ⟨τ, hτs, φ, hφ, hφ0⟩ := PI.GreenLabelSurjWork.exists_simple_constituent A.toRepresentation
    haveI := hτs
    haveI := PI.CharIdemW.nontrivial_of_simple τ
    have hcomm : ∀ a : MonoidAlgebra ℂ G, (∀ k : G, MonoidAlgebra.single k (1 : ℂ) * a = a * MonoidAlgebra.single k 1) →
        ∀ k : G, τ.ρ k * Representation.asAlgebraHom τ.ρ a = Representation.asAlgebraHom τ.ρ a * τ.ρ k := by
      intro a ha k
      rw [← Representation.asAlgebraHom_single_one, ← map_mul, ← map_mul, ha k]
    obtain ⟨μ, hμ⟩ := PI.CharIdemW.schur_scalar τ _ (hcomm w (single_mul_uElt U f e hC))
    obtain ⟨ν, hν⟩ := PI.CharIdemW.schur_scalar τ _ (hcomm e (fun k => hC _ |>.symm))
    have hφw : ∀ x, φ (Representation.asAlgebraHom τ.ρ w x) = 0 := by
      intro x
      rw [GlobalTheory.GoodFactor.asAlg_eq τ.ρ w, LinearMap.sum_apply, map_sum]
      simp only [LinearMap.smul_apply, map_smul]
      have h1 : ∀ g, φ (τ.ρ g x) = A.toRepresentation g (φ x) := fun g => LinearMap.congr_fun (hφ g) x
      simp only [h1]
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      show ∑ g, w.coeff g • (MonoidAlgebra.single g (1 : ℂ) * (φ x : MonoidAlgebra ℂ G)) = 0
      have h2 : ∀ g, w.coeff g • (MonoidAlgebra.single g (1 : ℂ) * (φ x : MonoidAlgebra ℂ G)) =
          MonoidAlgebra.single g (w.coeff g) * (φ x : MonoidAlgebra ℂ G) := fun g => by
        rw [← smul_mul_assoc, MonoidAlgebra.smul_single', mul_one]
      simp only [h2]
      rw [← Finset.sum_mul, GlobalTheory.GoodFactor.sum_single]
      exact (hK _).1 (φ x).2
    have hμ0 : μ = 0 := by
      by_contra h
      apply hφ0
      refine LinearMap.ext fun x => ?_
      have h3 : x = μ⁻¹ • Representation.asAlgebraHom τ.ρ w x := by
        rw [hμ, LinearMap.smul_apply, Module.End.one_apply, smul_smul, inv_mul_cancel₀ h, one_smul]
      rw [h3, map_smul, hφw, smul_zero, LinearMap.zero_apply]
    have h10 : (1 : Module.End ℂ τ) ≠ 0 := one_ne_zero
    have hνν : ν * ν = ν := by
      have h4 : Representation.asAlgebraHom τ.ρ (e * e) = Representation.asAlgebraHom τ.ρ e := by rw [hI]
      rw [map_mul, hν, smul_mul_smul_comm, one_mul] at h4
      exact smul_left_injective ℂ h10 h4
    have hTw : Representation.asAlgebraHom τ.ρ w =
        Representation.asAlgebraHom τ.ρ (cU U f) * Representation.asAlgebraHom τ.ρ e + 1 -
          Representation.asAlgebraHom τ.ρ e := by
      rw [hw, uElt, map_add, map_mul, map_sub, map_one, add_sub_assoc]
    rw [hμ, hμ0, zero_smul, hν] at hTw
    have hν01 : ν * (ν - 1) = 0 := by linear_combination hνν
    rcases mul_eq_zero.mp hν01 with h0 | h0
    · rw [h0, zero_smul, mul_zero, zero_add, sub_zero] at hTw
      exact h10 hTw.symm
    · have hν1 : ν = 1 := sub_eq_zero.mp h0
      rw [hν1, one_smul, mul_one, add_sub_cancel_right] at hTw
      have htr := trace_cU τ U f
      rw [← hTw, map_zero] at htr
      have hirr := GlobalTheory.GoodFactor.isIrrChar_character τ hτs
      have hfix : ∑ g, e.coeff g * τ.character g = τ.character 1 := by
        have h5 : LinearMap.trace ℂ τ (Representation.asAlgebraHom τ.ρ e) = ∑ g, e.coeff g * τ.character g := by
          rw [GlobalTheory.GoodFactor.asAlg_eq τ.ρ e, map_sum]
          simp only [map_smul, smul_eq_mul, FDRep.character]
        rw [← h5, hν, hν1, one_smul, FDRep.character, map_one τ.ρ]
      have hne := hχ _ hirr hfix
      have h6 : ∑ u : U, ((Fintype.card U : ℂ)⁻¹ * f u) * τ.character u =
          (Fintype.card U : ℂ)⁻¹ * ∑ u : U, τ.character u * f u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by ring
      rw [h6] at htr
      have hG : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
      have hU : (Fintype.card U : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
      exact mul_ne_zero hG (mul_ne_zero hU hne) htr.symm
  obtain ⟨v, hv⟩ := LinearMap.injective_iff_surjective.1 hinj 1
  exact ⟨v, hv⟩

end GlobalTheory.MeetsUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmallRingElemOfFractionMapIntegral
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem exists_small_ring_elem_of_fraction_map_integral {D : D7} (X : NTw D.R D.host D.what₂ D.LL0 D.nd) (i : X.Tw) (z : FractionRing (X.O0 i))
    (y : X.O i) (h : fracMap X i z = algebraMap (X.O i) (FractionRing (X.O i)) y) :
    ∃ a : X.O0 i, algebraMap (X.O0 i) (FractionRing (X.O0 i)) a = z := by
  haveI := GlobalTheory.TwistChoice.isLocalHom_O (X := X) i
  rcases eq_or_ne z 0 with rfl | hz
  · exact ⟨0, map_zero _⟩
  rcases ValuationRing.isInteger_or_isInteger (X.O0 i) z with ⟨a, e⟩ | ⟨c, e⟩
  · exact ⟨a, e⟩
  · by_cases hc : IsUnit c
    · obtain ⟨u, rfl⟩ := hc
      refine ⟨↑u⁻¹, ?_⟩
      have h1 : algebraMap (X.O0 i) (FractionRing (X.O0 i)) (u : X.O0 i) *
          algebraMap (X.O0 i) (FractionRing (X.O0 i)) ((u⁻¹ : (X.O0 i)ˣ) : X.O0 i) = 1 := by
        rw [← map_mul, Units.mul_inv, map_one]
      rw [e] at h1
      rw [← inv_inv z]
      exact (eq_inv_of_mul_eq_one_right h1)
    · exfalso
      have e2 : algebraMap (X.O i) (FractionRing (X.O i)) (y * algebraMap (X.O0 i) (X.O i) c) = 1 := by
        rw [map_mul, ← h, ← fracMap_algebraMap, ← map_mul, e, mul_inv_cancel₀ hz, map_one]
      have e3 : y * algebraMap (X.O0 i) (X.O i) c = 1 :=
        IsFractionRing.injective (X.O i) (FractionRing (X.O i)) (by rw [e2, map_one])
      exact hc (isUnit_of_map_unit (algebraMap (X.O0 i) (X.O i)) c (isUnit_iff_exists_inv.2 ⟨y, by rw [mul_comm]; exact e3⟩))

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem delAt_unr {D : D7} (cf : CharFrame D) (i : D.ntw.Tw) {P : PlE D.host} (hS : P ∉ D.ntw.S0 i) :
    (cf.delAt (D.ntw.l i)).UnrAt P := by
  have hD : P ∉ placesOver D.host.E (if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde) := fun h =>
    hS (D.ntw.primes_subset_exceptional i (by rw [← Finset.mem_coe, D.ntw.pD_eq i]; exact h))
  unfold CharFrame.delAt
  split_ifs with h
  · rw [if_pos h] at hD
    exact cf.isDel'.unr P hD
  · rw [if_neg h] at hD
    exact cf.isDel.unr P hD

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem toC_delta {D : D7} (cf : CharFrame D) (i : D.ntw.Tw) {b : Bool} (ρ : GlobalTheory.Triple.Reading D.ntw i b)
    {P : PlE D.host} (σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om) (xd : D.LL0)
    (hxd : D.what₂.embLL (xd : D.what₂.LL) = (((cf.delAt (D.ntw.l i)).val P)⁻¹ : ℂˣ).1)
    (hdel : algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) =
      D.ntw.emb0 i xd) :
    ρ.toC (((if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ : (D.ntw.O0 i)ˣ)) : D.ntw.O0 i) =
      (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)⁻¹ := by
  set δ : ℂ := (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ) with hδ
  have hδ0 : δ ≠ 0 := Units.ne_zero _
  have hz : ‖δ‖ = 1 := cf.delAt_unitary _ _
  rw [Units.val_inv_eq_inv_val] at hxd
  have hread : ρ.toC ((D.ntw.delta i σ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = ρ.ι (ρ.κ (D.ntw.emb0 i xd)) := by
    rw [Reading.toC_apply, ← hdel]; rfl
  cases b
  ·
    have hx0 : (xd : D.what₂.LL) ≠ 0 := by
      intro h0; rw [h0, map_zero] at hxd; exact inv_ne_zero hδ0 hxd.symm
    have hstar : ((xd⁻¹ : D.LL0) : D.what₂.LL) = star (xd : D.what₂.LL) := by
      apply D.what₂.embLL.injective
      rw [D.starLL_cx, hxd, ← Complex.inv_eq_conj (by rw [norm_inv, hz, inv_one]), inv_inv]
      rw [IntermediateField.coe_inv, map_inv₀, hxd, inv_inv]
    have e : D.ntw.emb0 i xd = D.ntw.emb0b i xd⁻¹ := (D.ntw.restX_coefficientEmbedding_conj i xd⁻¹ xd ?_).symm
    · have h1 := ρ.read xd⁻¹
      simp only [embSide, Bool.false_eq_true, if_false] at h1
      simp only [Bool.false_eq_true, if_false]
      rw [map_units_inv, hread, e, h1]
      show (D.what₂.embLL ((xd⁻¹ : D.LL0) : D.what₂.LL))⁻¹ = δ⁻¹
      rw [IntermediateField.coe_inv, map_inv₀, hxd, inv_inv]
    · rw [hstar, star_star]
  · have h1 := ρ.read xd
    simp only [embSide, if_true] at h1
    simp only [if_true, hread, h1]
    exact hxd

end GlobalTheory.TwInputs.HEig

namespace GlobalTheory.TwInputs.HEig

open GlobalTheory.Triple GlobalTheory.EigTie

theorem hEig_eq_heckeVal : ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ∀ Sb : Finset (PlE D.host), (∀ i, Sb ⊆ D.ntw.S0 i) → EigTrue D cf Rw Sb eig → ∀ i (s : D.ntw.Sig i) (ρ : GlobalTheory.Triple.Reading D.ntw i (D.ntw.side i s)) (π : D.naut.CG D.R.r), GlobalTheory.EigTie.IsRowPar Rw (Bs.rowS i s) π → ∀ k P, k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i → ∃ x : D.ntw.O0 i, algebraMap (D.ntw.O0 i) (D.ntw.O i) x = D.ntw.hEig i s k P ∧ ρ.toC x = GlobalTheory.Triple.heckeVal (GlobalTheory.Triple.muBase cf (D.ntw.l i) (GlobalTheory.Triple.jIdx s)) π k P := by
  intro D cf Rw low Pq S hL eig θ Bs Sb hSb hET i s ρ π hπ k P hk hP hS
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · exact ⟨1, by rw [map_one, Bs.hEig_zero], by rw [map_one, heckeVal_zero]⟩
  obtain ⟨σ, -, hσ⟩ := GlobalTheory.TripleGal.exists_mem_Dec_isFrob D P (D.nd.plOm.1 P) (D.nd.plOm.2 P)
  have hl : P ∉ placesOver D.host.E (D.ntw.l i) := fun h => hS (D.ntw.twistExcludedPlaces_contains_residueChar i h)
  obtain ⟨xd, hxd, hdel⟩ := Bs.deltaRead i P hl (delAt_unr cf i hS) _ σ (D.nd.plOm.2 P) hσ
  set u : (D.ntw.O0 i)ˣ := if D.ntw.side i s then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ with hu
  have hc : Bs.cHk i (D.ntw.side i s) P = Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom u :=
    Bs.cHk_del i (D.ntw.side i s) P hS σ hσ
  set e : ↥D.LL0 := eig (D.ntw.jS i s) (Bs.rowS i s) k P with he
  set z : FractionRing (D.ntw.O0 i) := embSide D.ntw i (D.ntw.side i s) e with hz
  have hrow := Bs.rowS_eig i s k P hk1 hk hP hS
  have hread : (show FractionRing (D.ntw.O i) from readLL0 S i (D.ntw.side i s) e) = fracMap D.ntw i z := rfl
  rw [hread, hc] at hrow
  set A : D.ntw.O0 i →+* FractionRing (D.ntw.O i) :=
    (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))).comp (algebraMap (D.ntw.O0 i) (D.ntw.O i)) with hA
  have hcu : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
      ((Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom u : (D.ntw.O i)ˣ) : D.ntw.O i) = A u := rfl
  rw [hcu] at hrow
  have hAu : A (u : D.ntw.O0 i) * A ((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]

  have hzO : fracMap D.ntw i z = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))
      (D.ntw.hEig i s k P * algebraMap (D.ntw.O0 i) (D.ntw.O i) (((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ k)) := by
    rw [map_mul, hrow, map_pow, map_pow]
    change _ = A (u : D.ntw.O0 i) ^ k * fracMap D.ntw i z * A ((u⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i) ^ k
    rw [mul_comm _ (fracMap D.ntw i z), mul_assoc, ← mul_pow, hAu, one_pow, mul_one]
  obtain ⟨a, ha⟩ := exists_small_ring_elem_of_fraction_map_integral D.ntw i z _ hzO
  refine ⟨(u : D.ntw.O0 i) ^ k * a, ?_, ?_⟩
  · apply IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
    rw [hrow, ← fracMap_algebraMap, map_mul, map_mul, ha, map_pow, map_pow, fracMap_algebraMap]
    rfl
  · have hloc : D.naut.locG π P = Rw.locR (Bs.rowS i s) P := hπ.2 P hP
    obtain ⟨hocc, hgood, -⟩ := Bs.rhoS i s
    have hocc' : D.what₂.isot ((jIdx s).1 + 1) (Bs.rowS i s) ≠ ⊥ := by rwa [jIdx_add_one]
    have hET' := (hET (jIdx s) (Bs.rowS i s) hocc' hgood P hP (fun h => hS (hSb i h))).2 k hk1 hk
    rw [jIdx_add_one] at hET'
    have hδ : ρ.toC (u : D.ntw.O0 i) = _ := toC_delta cf i ρ σ xd hxd hdel
    have hae : ρ.toC a = D.what₂.embLL (e : D.what₂.LL) := by
      rw [Reading.toC_apply]
      change ρ.ι (ρ.κ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) a)) = _
      rw [ha, hz, ρ.read]
      rfl
    rw [map_mul, map_pow, hδ, hae, he, hET', heckeVal, satake, hloc, muBase, HChar.val_mul, Units.val_mul]
    set q : ℂ := ((normV P : ℕ) : ℂ)
    set c : ℂ := (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ)⁻¹
    have hmap : (D.naut.frobEig (Rw.locR (Bs.rowS i s) P)).map (fun a =>
        a⁻¹ * ((((cf.mu0 (jIdx s)).val P : ℂˣ) : ℂ) * (((cf.delAt (D.ntw.l i)).val P : ℂˣ) : ℂ))⁻¹ * (q ^ (D.R.nV / 2))⁻¹) =
        ((D.naut.frobEig (Rw.locR (Bs.rowS i s) P)).map (fun a =>
          a⁻¹ * (((cf.mu0 (jIdx s)).val P : ℂˣ) : ℂ)⁻¹ * (q ^ (D.R.nV / 2))⁻¹)).map (fun y => c • y) := by
      rw [Multiset.map_map]
      refine Multiset.map_congr rfl fun a _ => ?_
      simp only [Function.comp_apply, smul_eq_mul, c, mul_inv]
      ring
    rw [hmap, ← Multiset.pow_smul_esymm, smul_eq_mul]
    ring

end GlobalTheory.TwInputs.HEig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FullDegreeLabelForcesTrivialWildInertia
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WildFull

open Polynomial

theorem main : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.HeightCounting.LabTrue D T → GlobalTheory.TypeLeaf.WildOne D := by
  intro D T hL k v L hdeg s hsI hsW
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have h1 := hL k v L
  rw [h1, ← T.dim] at hdeg
  rw [T.inePol _ L s hsI, ← T.dim]
  exact GlobalTheory.WeilDeligne.WD.inePol_wild_of_natDegree_lab hdeg hsW

end GlobalTheory.WildFull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsTransportStatement
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_langlands_transport : GlobalArtinReciprocity → ChevalleyUnits → BrauerDegreeZero → LocalLanglandsExists → LocalConverseGL → LanglandsExhaustionGL → BernsteinZelevinskyFiniteness → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (E' Ω' : Type) [Field E'] [NumberField E'] [Field Ω'] [Algebra E' Ω'] [IsAlgClosure E' Ω'] (A' : ValuationSubring Ω') (w' : HeightOneSpectrum (𝓞 E')) (h' : IsPlaceOver A' w') (rc : IrrGL (w.adicCompletion E) → WD h) (rc' : IrrGL (w'.adicCompletion E') → WD h'), IsRecLit h rc → IsRecLit h' rc' → FieldCompatible rc rc' := by
  first | exact @GlobalTheory.LocLanglands.FieldCompat.fieldCompatible | exact GlobalTheory.LocLanglands.FieldCompat.fieldCompatible | (intros; apply GlobalTheory.LocLanglands.FieldCompat.fieldCompatible <;> assumption)
end

