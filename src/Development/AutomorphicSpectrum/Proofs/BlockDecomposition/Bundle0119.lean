import Mathlib
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0114
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.TwistedRepresentations.Tens
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0101
import ReciprocityTheory.GroupCohomology.FinGen
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExchange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0115
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0116
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0100
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishesOfRadicalSums

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MaschkeProperties
section
open CategoryTheory
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.Maschke

section Avg

variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

def avg (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (f : V →ₗ[ℂ] W) : V →ₗ[ℂ] W :=
  (Fintype.card Γ : ℂ)⁻¹ • ∑ g : Γ, σ g ∘ₗ f ∘ₗ ρ g⁻¹

theorem avg_apply (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (f : V →ₗ[ℂ] W) (v : V) :
    avg ρ σ f v = (Fintype.card Γ : ℂ)⁻¹ • ∑ g : Γ, σ g (f (ρ g⁻¹ v)) := by
  simp [avg, LinearMap.sum_apply]

theorem mem_intw_apply {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (h : φ ∈ Intw ρ σ) (g : Γ) (v : V) : φ (ρ g v) = σ g (φ v) :=
  LinearMap.congr_fun (h g) v

theorem rep_inv_apply (ρ : Representation ℂ Γ V) (g : Γ) (v : V) : ρ g (ρ g⁻¹ v) = v := by
  have h : ρ (g * g⁻¹) v = v := by simp
  rwa [map_mul] at h

theorem avg_mem (ρ : Representation ℂ Γ V) (σ : Representation ℂ Γ W) (f : V →ₗ[ℂ] W) :
    avg ρ σ f ∈ Intw ρ σ := by
  intro h
  ext v
  simp only [LinearMap.comp_apply, avg_apply, map_smul, map_sum]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulLeft h⁻¹) _ _ fun g => ?_
  have e1 : ρ (h⁻¹ * g)⁻¹ v = ρ g⁻¹ (ρ h v) := by
    rw [mul_inv_rev, inv_inv, map_mul]; rfl
  have e2 : ∀ w, σ h (σ (h⁻¹ * g) w) = σ g w := fun w => by
    have h2 : σ (h * (h⁻¹ * g)) w = σ g w := by simp
    rw [map_mul σ h (h⁻¹ * g)] at h2
    exact h2
  simp only [Equiv.coe_mulLeft]
  rw [e1, e2]

theorem avg_of_mem {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {f : V →ₗ[ℂ] W}
    (hf : f ∈ Intw ρ σ) : avg ρ σ f = f := by
  ext v
  have hc : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have h : ∀ g : Γ, σ g (f (ρ g⁻¹ v)) = f v := fun g => by
    rw [← mem_intw_apply hf, rep_inv_apply]
  simp only [avg_apply, h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem id_mem (ρ : Representation ℂ Γ V) : (LinearMap.id : V →ₗ[ℂ] V) ∈ Intw ρ ρ := by
  intro g
  simp

theorem comp_mem {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {τ : Representation ℂ Γ U}
    {φ : V →ₗ[ℂ] W} {ψ : W →ₗ[ℂ] U} (hφ : φ ∈ Intw ρ σ) (hψ : ψ ∈ Intw σ τ) :
    ψ ∘ₗ φ ∈ Intw ρ τ := by
  intro g
  ext v
  simp only [LinearMap.comp_apply]
  rw [mem_intw_apply hφ, mem_intw_apply hψ]

theorem avg_comp {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (τ : Representation ℂ Γ U)
    {φ : V →ₗ[ℂ] W} (hφ : φ ∈ Intw ρ σ) (f : W →ₗ[ℂ] U) :
    avg σ τ f ∘ₗ φ = avg ρ τ (f ∘ₗ φ) := by
  ext v
  simp only [LinearMap.comp_apply, avg_apply]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mem_intw_apply hφ]

theorem comp_avg {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} (τ : Representation ℂ Γ U)
    {φ : V →ₗ[ℂ] W} (hφ : φ ∈ Intw ρ σ) (f : U →ₗ[ℂ] V) :
    φ ∘ₗ avg τ ρ f = avg τ σ (φ ∘ₗ f) := by
  ext v
  simp only [LinearMap.comp_apply, avg_apply, map_smul, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mem_intw_apply hφ]

theorem exists_left_inverse {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hφ : φ ∈ Intw ρ σ) (hinj : Function.Injective φ) :
    ∃ ψ ∈ Intw σ ρ, ψ ∘ₗ φ = LinearMap.id := by
  obtain ⟨q, hq⟩ := φ.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨avg σ ρ q, avg_mem σ ρ q, ?_⟩
  rw [avg_comp ρ hφ, hq, avg_of_mem (id_mem ρ)]

theorem exists_right_inverse {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hφ : φ ∈ Intw ρ σ) (hsurj : Function.Surjective φ) :
    ∃ ψ ∈ Intw σ ρ, φ ∘ₗ ψ = LinearMap.id := by
  obtain ⟨q, hq⟩ := φ.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hsurj)
  refine ⟨avg σ ρ q, avg_mem σ ρ q, ?_⟩
  rw [comp_avg σ hφ, hq, avg_of_mem (id_mem σ)]

end Avg

section Schur

variable {Γ : Type} [Group Γ]
variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem injective_of_irr {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hρ : IsIrr ρ) (hφ : φ ∈ Intw ρ σ) (h0 : φ ≠ 0) : Function.Injective φ := by
  have hinv : ∀ g, ∀ v ∈ LinearMap.ker φ, ρ g v ∈ LinearMap.ker φ := fun g v hv => by
    have h1 : φ (ρ g v) = σ g (φ v) := LinearMap.congr_fun (hφ g) v
    rw [LinearMap.mem_ker] at hv ⊢
    rw [h1, hv, map_zero]
  rcases hρ.2 _ hinv with h | h
  · exact LinearMap.ker_eq_bot.mp h
  · exact absurd (LinearMap.ker_eq_top.mp h) h0

theorem surjective_of_irr {ρ : Representation ℂ Γ V} {σ : Representation ℂ Γ W} {φ : V →ₗ[ℂ] W}
    (hσ : IsIrr σ) (hφ : φ ∈ Intw ρ σ) (h0 : φ ≠ 0) : Function.Surjective φ := by
  have hinv : ∀ g, ∀ w ∈ LinearMap.range φ, σ g w ∈ LinearMap.range φ := fun g w hw => by
    obtain ⟨v, rfl⟩ := hw
    exact ⟨ρ g v, LinearMap.congr_fun (hφ g) v⟩
  rcases hσ.2 _ hinv with h | h
  · exact absurd (LinearMap.range_eq_bot.mp h) h0
  · exact LinearMap.range_eq_top.mp h

end Schur

section Main

variable {Γ : Type} [Group Γ] [Fintype Γ]
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem irr_of_finrank_one [FiniteDimensional ℂ V] (ρ : Representation ℂ Γ V)
    (h : Module.finrank ℂ (Intw ρ ρ) = 1) : IsIrr ρ := by
  have hV : Nontrivial V := by
    by_contra hn
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hn
    have : Subsingleton (Intw ρ ρ) := inferInstance
    rw [Module.finrank_zero_of_subsingleton] at h
    exact zero_ne_one h
  refine ⟨hV, fun S hS => ?_⟩
  obtain ⟨q, hq⟩ := S.subtype.exists_leftInverse_of_injective S.ker_subtype
  set p := avg ρ ρ (S.subtype ∘ₗ q) with hp
  have hpS : ∀ v, p v ∈ S := fun v => by
    rw [hp, avg_apply]
    refine S.smul_mem _ (S.sum_mem fun g _ => hS g _ ?_)
    exact (q (ρ g⁻¹ v)).2
  have hq' : ∀ w (hw : w ∈ S), ((q w : S) : V) = w := fun w hw => by
    have := LinearMap.congr_fun hq ⟨w, hw⟩
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.id_apply] at this
    rw [this]
  have hc : (Fintype.card Γ : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hfix : ∀ w ∈ S, p w = w := fun w hw => by
    have h1 : ∀ g : Γ, ρ g ((S.subtype ∘ₗ q) (ρ g⁻¹ w)) = w := fun g => by
      simp only [LinearMap.comp_apply, Submodule.subtype_apply]
      rw [hq' _ (hS _ _ hw), rep_inv_apply]
    rw [hp, avg_apply]
    simp only [h1, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hne : (⟨LinearMap.id, id_mem ρ⟩ : Intw ρ ρ) ≠ 0 := fun h0 => by
    have h1 : (LinearMap.id : V →ₗ[ℂ] V) = 0 := congrArg Subtype.val h0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact hx (LinearMap.congr_fun h1 x)
  obtain ⟨c, hcp⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp h ⟨p, avg_mem ρ ρ _⟩
  have hpc : ∀ v, p v = c • v := fun v => by
    have h1 : c • (LinearMap.id : V →ₗ[ℂ] V) = p := congrArg Subtype.val hcp
    rw [← h1]; rfl
  by_cases hc0 : c = 0
  · left
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot, ← hfix w hw, hpc, hc0, zero_smul]
  · right
    rw [eq_top_iff]
    intro v _
    have h1 : v = c⁻¹ • p v := by rw [hpc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
    rw [h1]
    exact S.smul_mem _ (hpS v)

theorem maschkeFacts_of_simpleIffIrr (hs : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr) :
    ReciprocityTheory.Ty.Fin.St.MaschkeFacts := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro Γ _ _ τ V _ _ _ ρ hτ
    have hirr : IsIrr τ.ρ := (hs.1 Γ τ).1 hτ
    constructor
    · rintro ⟨φ, hφ, h0⟩
      obtain ⟨ψ, hψ, hl⟩ := exists_left_inverse hφ (injective_of_irr hirr hφ h0)
      refine ⟨ψ, hψ, fun hz => ?_⟩
      have := hirr.1
      obtain ⟨x, hx⟩ := exists_ne (0 : τ)
      have h1 := LinearMap.congr_fun hl x
      simp [hz] at h1
      exact hx h1.symm
    · rintro ⟨ψ, hψ, h0⟩
      obtain ⟨φ, hφ, hr⟩ := exists_right_inverse hψ (surjective_of_irr hirr hψ h0)
      refine ⟨φ, hφ, fun hz => ?_⟩
      have := hirr.1
      obtain ⟨x, hx⟩ := exists_ne (0 : τ)
      have h1 := LinearMap.congr_fun hr x
      simp [hz] at h1
      exact hx h1.symm
  · rintro Γ _ _ τ V _ _ _ W _ _ _ ρ σ hτ ⟨φ, hφ, h0⟩ ⟨φ', hφ', h0'⟩ hfin
    have hirr : IsIrr τ.ρ := (hs.1 Γ τ).1 hτ
    obtain ⟨ψ, hψ, hl⟩ := exists_left_inverse hφ (injective_of_irr hirr hφ h0)
    rw [Submodule.finrank_eq_zero] at hfin
    have hmem : φ' ∘ₗ ψ ∈ Intw ρ σ := comp_mem hψ hφ'
    rw [hfin, Submodule.mem_bot] at hmem
    apply h0'
    have h1 : (φ' ∘ₗ ψ) ∘ₗ φ = φ' := by rw [LinearMap.comp_assoc, hl, LinearMap.comp_id]
    rw [← h1, hmem, LinearMap.zero_comp]
  · intro Γ _ _ V _ _ _ ρ h
    exact irr_of_finrank_one ρ h
  · intro Γ _ _ V _ _ _ W _ _ _ ρ σ hρ hσ hfin
    have hne : Intw ρ σ ≠ ⊥ := fun hb => hfin (by rw [hb]; exact finrank_bot ℂ _)
    obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).mp hne
    exact ⟨LinearEquiv.ofBijective φ
        ⟨injective_of_irr hρ hφ h0, surjective_of_irr hσ hφ h0⟩,
      fun γ v => LinearMap.congr_fun (hφ γ) v⟩

theorem maschkeFacts : ReciprocityTheory.Ty.Fin.St.MaschkeFacts :=
  maschkeFacts_of_simpleIffIrr GlobalTheory.T.simple_iff_irreducible

end Main

end GlobalTheory.CompanionTheory.TyFin.Maschke
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModuleFiniteLimitOfLseq
section
open TensorProduct CrystallineSemistableComparison CrystallineSemistableComparison.Tw

namespace GlobalTheory.CompanionTheory.TowerLim

theorem module_finite_lim : ∀ (W : Type) [CommRing W] (l : ℕ) [IsAdicComplete (Ideal.span {(l : W)}) W]
    (S S' : Sys.{1} W) (_ : LSeq l S S'), IsFiniteLength W (S.M 1) → Module.Finite W S.lim := by
  intro W _ l _ S S' L h1
  have hfl := GlobalTheory.T.finite_length_of_lseq_first W l S S' L h1
  have hart : ∀ n, IsArtinian W (S.M n) := fun n =>
    (isFiniteLength_iff_isNoetherian_isArtinian.1 (hfl n)).2
  have hinj := GlobalTheory.T.limit_divisible_of_vanishing_level W l S S' L hart

  have hvan : ∀ n, (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) ≤ LinearMap.ker (pr S n) := by
    intro n
    refine Submodule.smul_le.2 fun r hr m _ => ?_
    rw [Ideal.span_singleton_pow] at hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [LinearMap.mem_ker, map_smul, mul_smul]
    rw [L.kill n, smul_zero]
  have hH : IsHausdorff (Ideal.span {(l : W)}) S.lim := by
    refine ⟨fun x hx => Subtype.ext (funext fun n => ?_)⟩
    have hm : x ∈ (Ideal.span {(l : W)} ^ n • (⊤ : Submodule W S.lim)) := by
      simpa [SModEq.zero] using hx n
    exact hvan n hm
  have hmem1 : ∀ x : S.lim, pr S 1 x = 0 → x ∈ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) := by
    intro x hx
    obtain ⟨y, hy⟩ := hinj 1 x hx
    rw [hy, pow_one]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  have hle : Ideal.span {(l : W)} • (⊤ : Submodule W S.lim) ≤ LinearMap.ker (pr S 1) := by
    simpa using hvan 1
  let q := (Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).liftQ (pr S 1) hle
  have hq : Function.Injective q := by
    refine (injective_iff_map_eq_zero _).2 fun z hz => ?_
    induction z using Submodule.Quotient.induction_on with
    | H x =>
      rw [Submodule.Quotient.mk_eq_zero]
      exact hmem1 x hz
  have : IsNoetherian W (S.M 1) := (isFiniteLength_iff_isNoetherian_isArtinian.1 h1).1
  have : Module.Finite W (S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)) :=
    Module.Finite.of_injective q hq
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := W)
    (M := S.lim ⧸ Ideal.span {(l : W)} • (⊤ : Submodule W S.lim))
  choose s' hs' using fun i => Submodule.Quotient.mk_surjective _ (s i)
  have : IsPrecomplete (Ideal.span {(l : W)}) (Fin r → W) := ReciprocityTheory.Coh.isPrecomplete_pi _
  have hsurj : Function.Surjective ((Ideal.span {(l : W)} • (⊤ : Submodule W S.lim)).mkQ ∘ₗ
      Fintype.linearCombination W s') := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, by simp [hs']⟩
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)

end GlobalTheory.CompanionTheory.TowerLim
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductHuaDeterminantIntegrableStatement
section
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.product_hua_determinant_integrable : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
  ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetAdjointForm
section
open Formalism.REAL

namespace GlobalTheory.CompanionTheory.CapelliAdj

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def HasAdj (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (T S : Module.End ℂ V) : Prop :=
  ∀ φ ψ : V, B (T φ) ψ = B φ (S ψ)

theorem HasAdj.mul {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {T T' S S' : Module.End ℂ V}
    (h : HasAdj B T S) (h' : HasAdj B T' S') : HasAdj B (T * T') (S' * S) := by
  intro φ ψ
  show B (T (T' φ)) ψ = B φ (S' (S ψ))
  rw [h (T' φ) ψ, h' φ (S ψ)]

theorem HasAdj.one (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : HasAdj B 1 1 := by
  intro φ ψ
  rfl

theorem HasAdj.add {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {T T' S S' : Module.End ℂ V}
    (h : HasAdj B T S) (h' : HasAdj B T' S') : HasAdj B (T + T') (S + S') := by
  intro φ ψ
  simp only [LinearMap.add_apply, map_add, h φ ψ, h' φ ψ]

theorem HasAdj.zero (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) : HasAdj B 0 0 := by
  intro φ ψ
  simp

theorem HasAdj.ofFn {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} :
    ∀ (t : ℕ) (f : Fin t → Module.End ℂ V) (g : Fin t → (Module.End ℂ V)ᵐᵒᵖ),
      (∀ k, HasAdj B (f k) (MulOpposite.unop (g k))) →
      HasAdj B (List.ofFn f).prod (MulOpposite.unop (List.ofFn g).prod) := by
  intro t
  induction t with
  | zero =>
    intro f g _
    simpa using HasAdj.one B
  | succ t ih =>
    intro f g hk
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, MulOpposite.unop_mul]
    exact (hk 0).mul (ih _ _ fun k => hk k.succ)

private theorem hasAdj_algebraMap_lemma (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (u : ℂ) :
    HasAdj B (algebraMap ℂ (Module.End ℂ V) u) (algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u)) := by
  intro φ ψ
  simp [Module.algebraMap_end_apply]

theorem HasAdj.tm {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {n : ℕ} {X Y : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (u : ℂ) (i j : Fin n) :
    HasAdj B (Tm X u i j)
      (MulOpposite.unop (Tm (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) u) i j)) := by
  have h1 : HasAdj B (if i = j then algebraMap ℂ (Module.End ℂ V) u else 0)
      (if i = j then algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u) else 0) := by
    split_ifs
    · exact hasAdj_algebraMap_lemma B u
    · exact HasAdj.zero B
  have h2 : HasAdj B (X i j) (-Y i j) := by
    intro φ ψ
    rw [h i j φ ψ, LinearMap.neg_apply, map_neg]
  have e1 : Tm X u i j = (if i = j then algebraMap ℂ (Module.End ℂ V) u else 0) + X i j := rfl
  have e2 : MulOpposite.unop (Tm (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) u) i j)
      = (if i = j then algebraMap ℂ (Module.End ℂ V) ((starRingEnd ℂ) u) else 0) + -Y i j := by
    unfold Tm
    split_ifs <;> simp [MulOpposite.algebraMap_apply]
  rw [e1, e2]
  exact h1.add h2

theorem HasAdj.intCast (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (z : ℤ) :
    HasAdj B (z : Module.End ℂ V) (z : Module.End ℂ V) := by
  intro φ ψ
  simp [Module.End.intCast_apply]

theorem HasAdj.sum {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {ι : Type*} (s : Finset ι)
    (f g : ι → Module.End ℂ V) (h : ∀ i ∈ s, HasAdj B (f i) (g i)) :
    HasAdj B (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasAdj.zero B
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem hasAdj_qdet {B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ} {n : ℕ} {X Y : Fin n → Fin n → Module.End ℂ V}
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (v : ℂ) :
    HasAdj B (qdet X v)
      (MulOpposite.unop (qdet (fun a b => MulOpposite.op (-Y a b)) ((starRingEnd ℂ) v))) := by
  unfold qdet qminor
  have e : ∀ (F : Equiv.Perm (Fin n) → (Module.End ℂ V)ᵐᵒᵖ),
      MulOpposite.unop (∑ σ, F σ) = ∑ σ, MulOpposite.unop (F σ) := fun F =>
    map_sum (MulOpposite.opAddEquiv.symm : (Module.End ℂ V)ᵐᵒᵖ ≃+ Module.End ℂ V) F Finset.univ
  rw [e]
  refine HasAdj.sum _ _ _ fun σ _ => ?_
  rw [MulOpposite.unop_mul, MulOpposite.unop_intCast]
  refine (HasAdj.intCast B _).mul ?_
  apply HasAdj.ofFn
  intro k
  have hk := HasAdj.tm h (v - ((k : ℕ) : ℂ)) (σ k) k
  simpa [map_sub, map_natCast] using hk

theorem adj_qdet (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ)
    (X Y : Fin n → Fin n → Module.End ℂ V) (hY : GlRel Y)
    (h : ∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) (v : ℂ) (φ ψ : V) :
    B (qdet X v φ) ψ =
      B φ ((((-1 : ℂ) ^ n) • qdet Y ((n : ℂ) - 1 - (starRingEnd ℂ) v)) ψ) := by
  rw [hasAdj_qdet h v φ ψ, GlobalTheory.T.quantum_det_opposite_neg (Module.End ℂ V) n Y hY ((starRingEnd ℂ) v)]

end GlobalTheory.CompanionTheory.CapelliAdj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexLatticeEqHaarDetStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_lattice_eq_haar_det : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : GL (Fin n) k) (A₀ A : AddSubgroup (Fin n → k)), IsCompact (A : Set (Fin n → k)) → IsOpen (A₀ : Set (Fin n → k)) → A₀ ≤ A → A₀ ≤ A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom → ((A₀.relIndex A : ℕ) : ℝ) = (MeasureTheory.distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ) * ((A₀.relIndex (A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) : ℕ) : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul | exact GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul | (intros; apply GlobalTheory.CompanionTheory.IndexDet.relIndex_eq_distribHaarChar_det_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RootExchangeStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_exchange' : ReciprocityTheory.Ty.Fin.St.RootExchange := by
  first | exact @GlobalTheory.CompanionTheory.RootExch.rootExchange | exact GlobalTheory.CompanionTheory.RootExch.rootExchange | (intros; apply GlobalTheory.CompanionTheory.RootExch.rootExchange <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TotalComplexFlipIsomorphismStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH
universe w w' w'' t t' v u v' u' v'' u''
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.total_complex_flip_isomorphism : ∀ {R : Type} [CommRing R] (K : DCx.{w} R), ∃ φ : Cx.Hom K.tot K.flip.tot (RingHom.id R), (∀ n, Function.Bijective (φ.f n)) ∧ ∀ n (x : K.tot.X n) p q, (φ.f n x).1 q p = (-1 : ℤ) ^ (p * q) • x.1 p q := by
  first | exact @GlobalTheory.CompanionTheory.DCFlip.flip_tot | exact GlobalTheory.CompanionTheory.DCFlip.flip_tot | (intros; apply GlobalTheory.CompanionTheory.DCFlip.flip_tot <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TubeTransformIndependentOfBaseStatement
section
open MeasureTheory Filter Topology PositivityTheory.RgEis GlobalTheory.CompanionTheory.TubeFourier
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tube_transform_independent_of_base : ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X] (Ω : Set (ℝ × ℝ)) (G : ℂ × ℂ → X), IsOpen Ω → Convex ℝ Ω → GaussTube G Ω → ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ t : ℝ × ℝ, phi G x t = phi G x' t := by
  first | exact @GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex | exact GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex | (intros; apply GlobalTheory.CompanionTheory.TubeFourier.phi_eq_of_convex <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerBlockEmbeddingConjStatement
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_block_embedding_conj : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) (g : GL (Fin j) K) (h : GL (Fin d) K) (r : Fin j → K),
    j < d → (∀ x y, χ (x * y * x⁻¹) = χ y) →
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) →
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) →
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeR K d j (Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K))) ψ₀ χ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Conj.wh_colGeR_conj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerColumnRecursionStatement
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_column_recursion : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ), j < d →
    (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard →
    (∀ x : Fin j → K, (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) = if x = 0 then (Fintype.card K : ℂ) ^ j else 0) →
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ χ = ∑ r : Fin j → K, wh (colGe d j) (colGeR K d j r) ψ₀ χ := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier.wh_colGe_succ_eq_sum <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerVanishesOfRadicalSumsStatement
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_vanishes_of_radical_sums : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ),
    (∀ u : GL (Fin d) K, (open Classical in ∑ v : GL (Fin d) K,
      if v ∈ Formalism.IrreducibleCountingLemmas.TYPES.unip K (Formalism.IrreducibleCountingLemmas.TYPES.twoBlock d j) then χ (u * v) else 0) = 0) →
    wh (colGe d j) (colGeR K d j 0) ψ₀ χ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' | exact GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' | (intros; apply GlobalTheory.CompanionTheory.TyFin.ColStep.Avg.wh_zero_row' <;> assumption)
end

