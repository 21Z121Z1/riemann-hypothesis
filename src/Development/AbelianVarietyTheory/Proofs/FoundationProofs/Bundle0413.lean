import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CayleyHamiltonHeckeEigenvectorEveryGaloisElement
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0411
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaTW
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0023
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFR2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ApplyPolyOfStable
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0190
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0224
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0401
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0399
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0400
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0397
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0020
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0404
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0373
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0396
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDualCocycleCoboundaryOfVanishOnFixing

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CayleyHamiltonHeckeEigenvectorEveryGaloisElementStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cayleyHamilton_heckeEigenvector_every_galois_element : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [NormedField E] [IsAlgClosed E] [Algebra ℤ_[l] E], (∀ z : ℤ_[l], ‖algebraMap ℤ_[l] E z‖ = ‖z‖) → ∀ (lam : Letter → E) (t d : (Ω ≃ₐ[ℚ] Ω) → E) (S0 : Finset ℕ), (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖t (s * s') - t (s)‖ < δ) → (∀ δ : ℝ, 0 < δ → ∃ E0 : Finset Ω, ∀ s s' : Ω ≃ₐ[ℚ] Ω, (∀ x ∈ E0, s' x = x) → ‖d (s * s') - d (s)‖ < δ) → (∀ q : ℕ, q.Prime → q ∉ S0 → ∀ s, FrobAt q s → t s = lam (Letter.T q) ∧ d s = (q : E) ^ (w + 1) * lam (Letter.D q)) → ∀ x ∈ X.VB N l w E, (∀ T : Letter, admitted N l T → X.opV N l E T x = lam T • x) → ∀ s : Ω ≃ₐ[ℚ] Ω, X.galV l E s (X.galV l E s x) - t s • X.galV l E s x + d s • x = 0 := by
  first | exact @GlobalTheory.cayleyHamilton_galV | exact GlobalTheory.cayleyHamilton_galV | (intros; apply GlobalTheory.cayleyHamilton_galV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualSelmerUnboundedOrderNonzeroOrdinaryClassStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualSelmer_unbounded_order_nonzero_ordinaryClass : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → (∀ m : ℕ, ∃ (n : ℕ) (z : G ℚ Ω → Fin 2 → Qbar l), Coc1 c n (dual1 W) ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧ (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧ Cob1 c n (dual1 W) (Ine (F := ℚ) B) z) ∧ (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat (dual1 W) s 1 1 * x - x)) ∧ ¬ Cob1 c n (dual1 W) ⊤ (fun s => ((l : ℕ) : Qbar l) ^ m • z s)) → ¬ GrZero (dual1 W) A := by
  first | exact @GlobalTheory.Ord2.gw_limit | exact GlobalTheory.Ord2.gw_limit | (intros; apply GlobalTheory.Ord2.gw_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAdmissibleHeckeProjectionNonvanishing
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4
open scoped TensorProduct MatrixGroups Matrix
open GlobalTheory.LambdaValuationPowers

noncomputable section

namespace GlobalTheory.AdmProj

theorem tmul_mem_VB {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l w : ℕ) [Fact l.Prime]
    {b : X.Fn l} (hb : b ∈ X.B N l w) : (1 : Qbar l) ⊗ₜ[ℤ_[l]] b ∈ X.VB N l w (Qbar l) :=
  LinearMap.mem_range.2 ⟨(1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : X.B N l w), by simp⟩

theorem fixIc_mono {l : ℕ} [Fact l.Prime] {c c' : Coef l} (h : c.O ≤ c'.O) {x : Qbar l} (hx : FixIc c x) : FixIc c' x :=
  fun σ h1 h2 => hx σ (fun y hy => h1 y (h hy)) h2

theorem fixIc_l_pow_mul {l : ℕ} [Fact l.Prime] {c : Coef l} (a : ℕ) {x : Qbar l} (hx : FixIc c x) :
    FixIc c (((l : ℕ) : Qbar l) ^ a * x) := fun σ h1 h2 => by
  rw [map_mul, map_pow, map_natCast, hx σ h1 h2]

theorem exists_admissible_hecke_projection_nonvanishing_alt : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ)
  [Fact l.Prime] (e : ℕ) (S : Finset Pl) (W : R2 Ω l) (ψ : ZMod l → Qbar l) (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1))
  (j : Ω →+* Qbar l),
  Nf e S A W → 1 ≤ e →
  (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → (l : Ω) ∈ A.nonunits → l ≠ 2 → ¬ l ∣ N → 5 ≤ N →
  (∀ x ∈ A, ‖j x‖ ≤ 1) →
  ∀ (ev : Letter → Qbar l) (ρ : (Ω ≃ₐ[ℚ] Ω) →* GL (Fin 2) (Qbar l)) (F : Finset Ω),
  (∀ s, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) = rhoK W e ψ s) →
  (∀ s ∈ Dec (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 0 = 0) →
  (∀ s ∈ Ine (F := ℚ) A, (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 1 1 = 1) →
  (∀ s ∈ Ine (F := ℚ) A, (∀ y ∈ F, s y = y) →
    (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) 0 0 = ((cycZ ℚ Ω l s : ℤ_[l]) : Qbar l) ^ (2 * e - 1 + 1)) →
  (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ev (Letter.T q) = ι.symm (gN.a q)) →
  ∀ (χ : ℕ → ℤ_[l]), (∀ d : ℕ, Nat.Coprime d N → ev (Letter.D d) = ((χ d : ℤ_[l]) : Qbar l)) →
  ∀ (m : ℕ) (π : Fin m → (Qbar l ⊗[ℤ_[l]] X.Fn l) →ₗ[Qbar l] (Fin 2 → Qbar l))
    (σ : Fin m → (Fin 2 → Qbar l) →ₗ[Qbar l] (Qbar l ⊗[ℤ_[l]] X.Fn l)) (P : FreeAlgebra (Qbar l) Letter),
  P ∈ admissibleLettersSubalgebra (Qbar l) N l → FreeAlgebra.lift (Qbar l) ev P = 1 → (∀ i v, σ i v ∈ X.VB N l (2 * e - 1) (Qbar l)) →
  (∀ i s, ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.galV l (Qbar l) s x) = (ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ π i x) →
  (∀ i s v, X.galV l (Qbar l) s (σ i v) = σ i ((ρ s : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ v)) →
  (∀ i (T : Letter) v, GlobalTheory.KZ.admitted N l T → X.opV N l (Qbar l) T (σ i v) = ev T • σ i v) →
  (∀ i (T : Letter), GlobalTheory.KZ.admitted N l T → ∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), π i (X.opV N l (Qbar l) T x) = ev T • π i x) →
  (∀ i i' v, π i (σ i' v) = if i = i' then v else 0) →
  (∀ x ∈ X.VB N l (2 * e - 1) (Qbar l), FreeAlgebra.lift (Qbar l) (X.opV N l (Qbar l)) P x = ∑ i, σ i (π i x)) →
  ∀ (c : Coef l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), FinSupp lam → (∀ i : ℕ, FixIc c (lam (Pi.single i 1))) →
  (∃ c₂ : ℕ, ∀ (n : ℕ), c₂ ≤ n → ∀ (T : Letter) (b : X.Fn l), GlobalTheory.KZ.admitted N l T → InChi X N (2 * e - 1) χ b →
    Cg (n - c₂) (lam (seqN 1 j (thN X A N l n 1 (X.op N l T b)))) (ev T * lam (seqN 1 j (thN X A N l n 1 b)))) →
  ∃ (pr : X.Fn l → Fin 2 → Qbar l) (a : ℕ) (cf : Coef l),
    c.O ≤ cf.O ∧ (∀ s i k, mat W s i k ∈ cf.O) ∧
    (∀ b b', pr (b + b') = pr b + pr b') ∧
    (∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O) ∧
    (∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b) ∧
    (∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b) ∧
    (∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) → pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b) ∧
    (∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b) ∧
    IsLamFR2 X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam) := by
  intro Ω _ _ _ ε X A N l _ e S W ψ ι gN j hNf he hφ hlA hl2 hlN hN5 hj ev ρ F hρ hDec hIne hIne0 hev χ hχ m π σ P hPadm hPev
    hσV hπgal hσgal hσT heig hπσ hPx c lam hlamF hlamI hlamE
  classical
  have hodd : Odd (2 * e - 1) := ⟨e - 1, by omega⟩
  have hinj : Function.Injective ε := ε.injective
  have hφ' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := hφ; exact ⟨φ, h2, h1⟩
  have hcop : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd (Fact.out : l.Prime)).2 hlN).symm
  obtain ⟨pr0, ⟨κ, hκ⟩, hLam⟩ := GlobalTheory.LamChi.exists_pr_isLamFR ε X A N l (2 * e - 1) j hφ hlA hl2 hlN hN5 hodd hj ev ρ F hDec hIne hIne0
    m π σ P hPadm hPev hσV hπgal hσgal hσT hπσ hPx χ c lam hlamF hlamI hlamE

  have hadd0 : ∀ b b', pr0 (b + b') = pr0 b + pr0 b' := by
    intro b b'
    simp only [hκ, TensorProduct.tmul_add, map_add, smul_add, Finset.sum_add_distrib]
  have hsmul0 : ∀ (z : ℤ_[l]) b, pr0 (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr0 b := by
    intro z b
    rw [hκ, hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (Qbar l) z, map_smul, smul_comm]
    rfl
  have hgal0 : ∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr0 (X.galB l s b) = rhoK W e ψ s *ᵥ pr0 b := by
    intro s b hb
    rw [hκ, hκ, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (1 : Qbar l) ⊗ₜ[ℤ_[l]] X.galB l s b = X.galV l (Qbar l) s ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) := by
      simp [Tower.galV]
    rw [e1, hπgal i s _ (tmul_mem_VB X N l (2 * e - 1) hb), hρ s, Matrix.mulVec_smul]
  have hop0 : ∀ T : Letter, GlobalTheory.KZ.admitted N l T → ∀ b, b ∈ X.B N l (2 * e - 1) → pr0 (X.op N l T b) = ev T • pr0 b := by
    intro T hT b hb
    rw [hκ, hκ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have e1 : (1 : Qbar l) ⊗ₜ[ℤ_[l]] X.op N l T b = X.opV N l (Qbar l) T ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) := by
      simp [Tower.opV]
    rw [e1, heig i T hT _ (tmul_mem_VB X N l (2 * e - 1) hb), smul_comm]

  obtain ⟨c1, hc1⟩ := hNf.int
  obtain ⟨c0, hcc0, hc10⟩ := (UpperTheory.V.HV.coefSup l).1 c c1
  have hfree := GlobalTheory.KZ.B_free_finite ε X hinj hφ' N l (2 * e - 1) hl2 hN5 hcop hodd
  haveI := hfree.1
  haveI := hfree.2
  let bs := Module.Free.chooseBasis ℤ_[l] (X.B N l (2 * e - 1))
  obtain ⟨a, ha⟩ := exists_le_l_pow l
    (∑ p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2, ‖pr0 (bs p.1) p.2‖)
  have hsmall : ∀ p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2,
      ‖((l : ℕ) : Qbar l) ^ a * pr0 (bs p.1) p.2‖ ≤ 1 := by
    intro p
    have h1 : ‖pr0 (bs p.1) p.2‖ ≤ (l : ℝ) ^ a :=
      le_trans (Finset.single_le_sum
        (f := fun p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2 => ‖pr0 (bs p.1) p.2‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ p)) ha
    have hl0 : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
    rw [norm_mul, norm_l_pow]
    calc ((l : ℝ)⁻¹) ^ a * ‖pr0 (bs p.1) p.2‖ ≤ ((l : ℝ)⁻¹) ^ a * (l : ℝ) ^ a :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl0.ne', one_pow]
  obtain ⟨cf, hcf, hs⟩ := GlobalTheory.PowerSeriesEvalAlgCl.exists_coef_ge_finset c0
    (Finset.univ.image fun p : Module.Free.ChooseBasisIndex ℤ_[l] (X.B N l (2 * e - 1)) × Fin 2 =>
      ((l : ℕ) : Qbar l) ^ a * pr0 (bs p.1) p.2)
    (fun y hy => by
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.1 hy
      exact (GlobalTheory.PowerSeriesEvalAlgCl.isIntegral_iff_norm_le_one _).2 (hsmall p))

  obtain ⟨pr, hpr⟩ : ∃ pr : X.Fn l → Fin 2 → Qbar l, ∀ b, pr b = ((l : ℕ) : Qbar l) ^ a • pr0 b := ⟨_, fun _ => rfl⟩
  have hadd : ∀ b b', pr (b + b') = pr b + pr b' := by
    intro b b'; rw [hpr, hpr, hpr, hadd0, smul_add]
  have hsmul : ∀ (z : ℤ_[l]) b, pr (z • b) = algebraMap ℚ_[l] (Qbar l) (z : ℚ_[l]) • pr b := by
    intro z b; rw [hpr, hpr, hsmul0, smul_comm]
  have hint : ∀ b ∈ X.B N l (2 * e - 1), ∀ i, pr b i ∈ cf.O := by
    intro b hb i
    let g : X.B N l (2 * e - 1) →ₗ[ℤ_[l]] Qbar l :=
      { toFun := fun y => pr y.1 i
        map_add' := fun y y' => by
          simp only [Submodule.coe_add, hadd, Pi.add_apply]
        map_smul' := fun z y => by
          simp only [SetLike.val_smul, hsmul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Algebra.smul_def]
          rfl }
    have hle : Submodule.span ℤ_[l] (Set.range bs) ≤ (Subalgebra.toSubmodule cf.O).comap g := by
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      have := hs _ (Finset.mem_image.2 ⟨(k, i), Finset.mem_univ _, rfl⟩)
      simpa [g, hpr] using this
    rw [bs.span_eq] at hle
    exact hle (Submodule.mem_top (x := (⟨b, hb⟩ : X.B N l (2 * e - 1))))
  have hgal : ∀ (s : Ω ≃ₐ[ℚ] Ω) b, b ∈ X.B N l (2 * e - 1) → pr (X.galB l s b) = rhoK W e ψ s *ᵥ pr b := by
    intro s b hb; rw [hpr, hpr, hgal0 s b hb, Matrix.mulVec_smul]
  have hhecke : ∀ q : ℕ, q.Prime → ¬ q ∣ l * N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.heckeT N l q b) = ι.symm (gN.a q) • pr b := by
    intro q hq hqd b hb
    have hT : GlobalTheory.KZ.admitted N l (Letter.T q) := ⟨hq, fun h => hqd (by rwa [mul_comm] at h)⟩
    have := hop0 _ hT b hb
    rw [hpr, hpr, show X.heckeT N l q b = X.op N l (Letter.T q) b from rfl, this, hev q hq hqd, smul_comm]
  have hdiam : ∀ d : ℕ, Nat.Coprime d N → ∀ b, b ∈ X.B N l (2 * e - 1) →
      pr (X.diam N l d b) = ((χ d : ℤ_[l]) : Qbar l) • pr b := by
    intro d hd b hb
    have := hop0 (Letter.D d) hd b hb
    rw [hpr, hpr, show X.diam N l d b = X.op N l (Letter.D d) b from rfl, this, hχ d hd, smul_comm]
  have hU : ∀ b ∈ X.B N l (2 * e - 1), pr (X.heckeU l b) = ev Letter.U • pr b := by
    intro b hb
    have := hop0 Letter.U trivial b hb
    rw [hpr, hpr, show X.heckeU l b = X.op N l Letter.U b from rfl, this, smul_comm]
  have hnorm : ‖((l : ℕ) : Qbar l) ^ a‖ ≤ 1 := by
    rw [norm_l_pow]
    have h1 : (1 : ℝ) ≤ l := by exact_mod_cast (Fact.out : l.Prime).one_le
    exact pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ h1)
  have hccf : c.O ≤ cf.O := hcc0.trans hcf
  have hlam : IsLamFR X A N (2 * e - 1) χ j pr cf ((((l : ℕ) : Qbar l) ^ a) • lam) := by
    obtain ⟨hf, hw, cL, per, hper, hc⟩ := hLam
    refine ⟨hf.smul _, fun i => fixIc_l_pow_mul a (fixIc_mono hccf (hw i)), cL, per,
      fun n => ⟨(hper n).1, (hper n).2.1, fixIc_mono hccf (hper n).2.2⟩, fun n hn b hb φ hφ => ?_⟩
    have h := hc n hn b hb φ hφ
    unfold GlobalTheory.Ord2.Cg at h ⊢
    rw [hpr, LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    calc ‖((l : ℕ) : Qbar l) ^ a * lam (seqN 1 j φ) - per n * (((l : ℕ) : Qbar l) ^ a * pr0 b 1)‖
        = ‖((l : ℕ) : Qbar l) ^ a‖ * ‖lam (seqN 1 j φ) - per n * pr0 b 1‖ := by
          rw [← norm_mul]; congr 1; ring
      _ ≤ 1 * ‖((l : ℕ) : Qbar l) ^ (n - cL)‖ := mul_le_mul hnorm h (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  exact ⟨pr, a, cf, hccf, fun s i k => hcf (hc10 (hc1 s i k)), hadd, hsmul, hint, hgal, hhecke, hdiam, hU, hdiam, hlam⟩

end GlobalTheory.AdmProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsHtPresNu7
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ
open scoped Matrix

namespace GlobalTheory.KZ.UnitPres

open GlobalTheory.KumUnit

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem kumVal_int {n : ℕ} {ζ u v : Ω} {s : G ℚ Ω} {j : ℤ} (hζ : ζ ^ (l ^ n) = 1) (hv : v ^ (l ^ n) = u)
    (hs : s v = ζ ^ j * v) : GlobalTheory.Col.KumVal (l := l) n ζ u s (j : ZMod (l ^ n)) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have h0 : ζ ≠ 0 := by rintro rfl; rw [zero_pow hpos.ne'] at hζ; exact zero_ne_one hζ
  refine ⟨v, hv, ?_⟩
  rw [hs, ← zpow_natCast, ZMod.val_intCast]
  congr 1
  conv_lhs => rw [← Int.emod_add_mul_ediv j ((l ^ n : ℕ) : ℤ)]
  rw [zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

theorem cg_intCast (n : ℕ) (j : ℤ) : Cg (l := l) n (((j : ZMod (l ^ n)).val : ℕ) : Qbar l) (j : Qbar l) := by
  have hpos : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  haveI : NeZero (l ^ n) := ⟨hpos.ne'⟩
  have h1 : (((j : ZMod (l ^ n)).val : ℕ) : ℤ) - j = ((l ^ n : ℕ) : ℤ) * (-(j / ((l ^ n : ℕ) : ℤ))) := by
    rw [ZMod.val_intCast, Int.emod_def]; ring
  have e : (((j : ZMod (l ^ n)).val : ℕ) : Qbar l) - (j : Qbar l) =
      (l : Qbar l) ^ n * ((-(j / ((l ^ n : ℕ) : ℤ)) : ℤ) : Qbar l) := by
    have := congrArg (Int.cast : ℤ → Qbar l) h1
    rw [Int.cast_sub, Int.cast_mul, Int.cast_natCast, Int.cast_natCast, Nat.cast_pow] at this
    exact this
  rw [Cg, e, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (IsUltrametricDist.norm_intCast_le_one (Qbar l) _)

theorem exists_open [IsAlgClosure ℚ Ω] (h : G ℚ Ω → Qbar l) (hc : Continuous h) (h1 : h 1 = 0) (m : ℕ) :
    ∃ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) ∧ ∀ s ∈ U, Cg m (h s) 0 := by
  have hl : (0 : ℝ) < ‖((l : ℕ) : Qbar l) ^ m‖ :=
    norm_pos_iff.2 (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero))
  have hn : {s | ‖h s‖ < ‖((l : ℕ) : Qbar l) ^ m‖} ∈ nhds (1 : G ℚ Ω) :=
    (isOpen_lt hc.norm continuous_const).mem_nhds (by simpa [h1] using hl)
  obtain ⟨E, hE, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ Ω _).1 hn
  refine ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen, fun s hs => ?_⟩
  rw [Cg, sub_zero]
  exact le_of_lt (hsub hs)

theorem layer_one {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {r : ℕ}
    {z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hz : Layer2 c A ν r z) : z 1 1 = 0 := by
  have h := hz.2 1 (one_mem _) 1 (one_mem _) 1
  rw [mul_one, map_one, inv_one, mul_one] at h
  have h' : (ν 1 : Qbar l) * z 1 1 = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h').resolve_left (ν 1).ne_zero

theorem layer_add {c : Coef l} {A : ValuationSubring Ω} {ν : G ℚ Ω → (Qbar l)ˣ} {r : ℕ}
    {z : G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l} (hz : Layer2 c A ν r z) {s t : G ℚ Ω} (hs : s ∈ Dec (F := ℚ) A)
    (ht : t ∈ Dec (F := ℚ) A) (hc : cycMod ℚ Ω l r s = 1) : z (s * t) 1 = z s 1 + (ν s : Qbar l) * z t 1 := by
  have h := hz.2 s hs t ht 1
  rwa [hc, inv_one, mul_one] at h

end GlobalTheory.KZ.UnitPres
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialPrimitiveRootOfCyclotomicInertiaStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_primitiveRoot_of_cyclotomic_inertia_fixed : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ (m : ℕ) (ζ : Ω), IsPrimitiveRoot ζ (l ^ m) → ∀ u ∈ A, (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l m s = 1 → s u = u) → ∃ P : Polynomial Ω, (∀ x ∈ P.coeffs, x ∈ A ∧ ∀ s ∈ Ine (F := ℚ) A, s x = x) ∧ P.eval ζ = u := by
  first | exact @GlobalTheory.CycIne.exists_poly_of_fixed | exact GlobalTheory.CycIne.exists_poly_of_fixed | (intros; apply GlobalTheory.CycIne.exists_poly_of_fixed; all_goals assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveCharacterTwistStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries GlobalTheory.KZ.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_primitive_character_twist : ∀ (l : ℕ) [Fact l.Prime] (φ : DirichletCharacter (Qbar l) l) (e k : ℕ) (ζ : Qbar l), l ≠ 2 → 1 ≤ k → IsPrimitiveRoot ζ (l ^ k) → ∃ ψ : DirichletCharacter (Qbar l) (l ^ (k + 1)), ψ.IsPrimitive ∧ InComp φ e ψ ∧ ψ⁻¹ (1 + (l : ZMod (l ^ (k + 1)))) = ζ := by
  first | (exact @GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp) | (exact GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp) | (intros; apply GlobalTheory.KZ.Cmp.PrimChar.exists_primitive_inComp  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GreenbergWilesDualSelmerLowerBoundModPrimePowStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
theorem _root_.GlobalTheory.T.greenbergWiles_dualSelmer_lower_bound_mod_prime_pow : GlobalTheory.Mem.LiteralAutomorphy.LitCoh → ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ c : Coef l, (∀ s i j, mat W s i j ∈ c.O) → ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → ∀ (N : ℕ) (y : Fin N → G ℚ Ω → Fin 2 → Qbar l), (∀ i, GwCount.SelN c n S A W (y i)) → (∀ i j, i ≠ j → ¬ Cob1 c n W ⊤ (y i - y j)) → ∃ (N' : ℕ) (z : Fin N' → G ℚ Ω → Fin 2 → Qbar l), N ≤ C * N' ∧ (∀ i, GwCount.SelN c n S A (dual1 W) (z i)) ∧ ∀ i j, i ≠ j → ¬ Cob1 c n (dual1 W) ⊤ (z i - z j) := by
  first | exact @GlobalTheory.Ord2.GwIneq.gw_ineq | exact GlobalTheory.Ord2.GwIneq.gw_ineq | (intros; apply GlobalTheory.Ord2.GwIneq.gw_ineq <;> assumption) | exact @GlobalTheory.Ord2.GwIneq.exists_cc | exact GlobalTheory.Ord2.GwIneq.exists_cc | (intros; apply GlobalTheory.Ord2.GwIneq.exists_cc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemInertiaInvariantsCyclotomicAlgebraIff
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.RecOne GlobalTheory.AlmostEt
open scoped Matrix NNReal

namespace GlobalTheory.RecOne

theorem mem_cycAlg_iff : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : A, x ∈ cycAlg l A ↔ ∀ s ∈ ineCyc l A, s (x : Ω) = x := by
  intro l _ Ω _ _ _ A hA x
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  haveI : CharZero Ω := algebraRat.charZero Ω
  have hl : l.Prime := Fact.out
  haveI : NeZero l := ⟨hl.ne_zero⟩
  haveI hE : ∀ i, HasEnoughRootsOfUnity Ω (l ^ i) := fun i => inferInstance
  constructor
  · intro hx s hs
    obtain ⟨hsI, hsZ⟩ := mem_ineCyc.1 hs
    induction hx using Algebra.adjoin_induction with
    | mem z hz =>
      obtain ⟨n, hn⟩ := hz
      refine GlobalTheory.Col.fix_of_cycMod (l := l) (le_refl n) ?_ ?_
      · simp [cycMod, hsZ]
      · exact_mod_cast congrArg (fun a : A => (a : Ω)) hn
    | algebraMap r => exact r.2 s hsI
    | add a b _ _ ha hb =>
      show s ((a : Ω) + (b : Ω)) = (a : Ω) + (b : Ω)
      rw [map_add, ha, hb]
    | mul a b _ _ ha hb =>
      show s ((a : Ω) * (b : Ω)) = (a : Ω) * (b : Ω)
      rw [map_mul, ha, hb]
  · intro hx
    have hv : A.valuation (l : Ω) < 1 := by
      obtain ⟨v, hv, hl⟩ := hA
      have h1 := (hv ((l : ℕ) : 𝓞 ℚ)).2 hl
      simpa using h1
    obtain ⟨m, hm⟩ := GlobalTheory.fixed_cycMod_of_fixed_cycZ l Ω A hv ∅ (x : Ω)
      (fun s hs _ hz => hx s (mem_ineCyc.2 ⟨hs, hz⟩))
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (l ^ m)
    have hpos : 0 < l ^ m := pow_pos hl.pos m
    haveI : NeZero (l ^ m) := ⟨hpos.ne'⟩
    have hfix : ∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s (x : Ω) = x := by
      intro s hs hsζ
      refine hm s ⟨hs, by simp, ?_⟩
      have h1 := cyclotomicCharacter.spec (L := Ω) l (MulSemiringAction.toRingAut (G ℚ Ω) Ω s) ζ hζ.pow_eq_one
      have h2 : ζ ^ (PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val = ζ ^ 1 := by
        rw [pow_one]
        exact h1.symm.trans hsζ
      have h3 := (pow_eq_pow_iff_modEq (G := Ωˣ) (x := (hζ.isUnit hpos.ne').unit)
        (n := (PadicInt.toZModPow m ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])).val) (m := 1)).1 (by
          apply Units.ext
          simpa using h2)
      have h4 : orderOf (hζ.isUnit hpos.ne').unit = l ^ m := by
        rw [← orderOf_units, IsUnit.unit_spec]
        exact hζ.eq_orderOf.symm
      rw [h4, ← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, Nat.cast_one] at h3
      exact Units.ext h3
    obtain ⟨Q, hQ, hQe⟩ := GlobalTheory.T.exists_polynomial_in_primitiveRoot_of_inertia_fixed l Ω A hA m ζ hζ (x : Ω) x.2 hfix
    have hζA : ζ ∈ A := mem_of_pow_mem A hpos.ne' (by rw [hζ.pow_eq_one]; exact A.one_mem)
    have hζc : (⟨ζ, hζA⟩ : A) ∈ cycAlg l A :=
      mem_cycAlg_of_pow (n := m) (Subtype.ext (by simpa using hζ.pow_eq_one))
    have e : x = ∑ d ∈ Finset.range (Q.natDegree + 1), (⟨Q.coeff d, (hQ d).1⟩ : A) * (⟨ζ, hζA⟩ : A) ^ d := by
      apply Subtype.ext
      rw [← hQe, Polynomial.eval_eq_sum_range]
      refine Eq.trans ?_ (map_sum A.subtype _ _).symm
      refine Finset.sum_congr rfl fun d _ => ?_
      simp
    rw [e]
    refine Subalgebra.sum_mem _ fun d _ => Subalgebra.mul_mem _ ?_ (Subalgebra.pow_mem _ hζc d)
    exact (cycAlg l A).algebraMap_mem (⟨⟨Q.coeff d, (hQ d).1⟩, (hQ d).2⟩ : fixA A)

end GlobalTheory.RecOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TateDualCocycleCoboundaryOfVanishOnFixingStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateDual_cocycle_coboundary_of_vanish_on_fixing : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ z ∈ Z1 (Loc.colRep (dual1 W)), (∀ g ∈ N0g W, z g = 0) → z ∈ ReciprocityTheory.Gal.B1 (Loc.colRep (dual1 W)) := by
  first | exact @GlobalTheory.Ord2.h1dual_of_vanish_fix | exact GlobalTheory.Ord2.h1dual_of_vanish_fix | (intros; apply GlobalTheory.Ord2.h1dual_of_vanish_fix <;> assumption)
end

