import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0203
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0202
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0109
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0273

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.ChiStab
section
open UpperTheory.V.Z.Kato.Joint

theorem UpperTheory.V.Z.Kato.Joint.chiStab :
    UpperTheory.V.Z.Kato.Joint.ChiStab := by
  intro l hp Ω _ _ _ ε X N w χ hl hlN hN hw T b hT hb
  have hNl : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hlN).symm
  obtain ⟨φ, h1, h2⟩ := X.j_hol
  refine ⟨GlobalTheory.T.hecke_letter_preserves_basis_set ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T hT b hb.1, fun d hd => ?_⟩
  have h := GlobalTheory.T.modularTowerB_admissibleHecke_commute ε X ε.injective ⟨φ, h2, h1⟩ N l w hl hN hNl hw T (GlobalTheory.KZ.Letter.D d) hT hd b hb.1
  change X.op N l T (X.diam N l d b) = X.diam N l d (X.op N l T b) at h
  rw [← h, hb.2 d hd, map_smul]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FinSuppCompLift
section
open UpperTheory.V.Z.Kato.Joint

section

open Formalism.ConjugateSelfDual GlobalTheory.KZ GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers UpperTheory.V.HV

variable {l : ℕ} [Fact l.Prime]

private theorem finSupp_comp_fop (k : ℕ) (χ : ℕ → Qbar l) (T : Letter)
    (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (h : FinSupp lam) : FinSupp (lam ∘ₗ fop k l χ T) := by
  obtain ⟨S, hS⟩ := h
  cases T with
  | T q =>
    refine ⟨S.image (q * ·) ∪ S.image (· / q), fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show GlobalTheory.EisM.To k (χ q) q f n = 0
    have h1 : f (q * n) = 0 := hf _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
    have h2 : f (n / q) = 0 := hf _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩))
    simp [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, h1, h2]
  | U =>
    refine ⟨S.image (l * ·), fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show GlobalTheory.EisM.Uo l f n = 0
    exact hf _ (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  | D d =>
    refine ⟨S, fun f hf => ?_⟩
    rw [LinearMap.comp_apply]
    apply hS
    intro n hn
    show (χ d • f) n = 0
    simp [hf n hn]

private theorem finSupp_comp_lift (k : ℕ) (χ : ℕ → Qbar l) (P : FreeAlgebra (Qbar l) Letter) :
    ∀ lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l, FinSupp lam →
      FinSupp (lam ∘ₗ FreeAlgebra.lift (Qbar l) (fop k l χ) P) := by
  induction P using FreeAlgebra.induction with
  | grade0 r =>
    intro lam h
    rw [AlgHom.commutes]
    have hr : lam ∘ₗ algebraMap (Qbar l) (Module.End (Qbar l) (ℕ → Qbar l)) r = r • lam := by
      ext f
      simp [Module.algebraMap_end_apply]
    rw [hr]
    exact FinSupp.smul h r
  | grade1 x =>
    intro lam h
    rw [FreeAlgebra.lift_ι_apply]
    exact finSupp_comp_fop k χ x lam h
  | mul a b ha hb =>
    intro lam h
    rw [map_mul, Module.End.mul_eq_comp, ← LinearMap.comp_assoc]
    exact hb _ (ha lam h)
  | add a b ha hb =>
    intro lam h
    rw [map_add, LinearMap.comp_add]
    exact FinSupp.add (ha lam h) (hb lam h)

private theorem exists_pow_mul_le (x : Qbar l) : ∃ k : ℕ, ‖((l : ℕ) : Qbar l) ^ k * x‖ ≤ 1 := by
  obtain ⟨k, hk⟩ := exists_le_l_pow l ‖x‖
  refine ⟨k, ?_⟩
  rw [norm_mul, norm_l_pow]
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  calc ((l : ℝ))⁻¹ ^ k * ‖x‖ ≤ ((l : ℝ))⁻¹ ^ k * (l : ℝ) ^ k := by gcongr
    _ = 1 := by rw [← mul_pow, inv_mul_cancel₀ hl.ne', one_pow]

end

open Formalism.ConjugateSelfDual GlobalTheory.KZ GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers UpperTheory.V.HV in
theorem UpperTheory.V.Z.Kato.Joint.finP :
    UpperTheory.V.Z.Kato.Joint.FinP := by
  classical
  intro hub l _ ι k N B cc χE c₀ P _
  let lam₀ : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l :=
    ∑ n ∈ Finset.range B, ι.symm (cc n) • LinearMap.proj n
  have hlam₀ : ∀ a : ℕ → Qbar l, lam₀ a = ι.symm (GlobalTheory.EisM.lam B cc fun i => ι (a i)) := by
    intro a
    simp [lam₀, GlobalTheory.EisM.lam, map_sum, map_mul, LinearMap.sum_apply]
  have hfs₀ : FinSupp lam₀ := by
    refine ⟨Finset.range B, fun f hf => ?_⟩
    rw [hlam₀, GlobalTheory.EisM.lam, Finset.sum_eq_zero, map_zero]
    intro n hn
    simp [hf n hn]
  let lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l := lam₀ ∘ₗ FreeAlgebra.lift (Qbar l) (fop k l χE) P
  have hfs : FinSupp lam := finSupp_comp_lift k χE P lam₀ hfs₀
  obtain ⟨S, hS⟩ := hfs
  choose e he using exists_pow_mul_le (l := l)
  let g : ℕ → Qbar l := fun i => ((l : ℕ) : Qbar l) ^ e (lam (Pi.single i 1)) * lam (Pi.single i 1)
  obtain ⟨c, hc₀, -, hcF⟩ := hub l c₀ c₀ (S.image g) (by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact he _)
  have hl : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  refine ⟨lam₀, lam, c, hc₀, hfs₀, ⟨S, hS⟩, ?_, hlam₀, fun a => rfl⟩
  intro i σ hσ _
  by_cases hi : i ∈ S
  · have hy := hσ _ (hcF _ (Finset.mem_image_of_mem g hi))
    have hne : ((l : ℕ) : Qbar l) ^ e (lam (Pi.single i 1)) ≠ 0 := by
      intro h0
      have h1 := congrArg norm h0
      rw [norm_l_pow, norm_zero] at h1
      exact pow_ne_zero _ (inv_ne_zero hl.ne') h1
    simp only [g, map_mul, map_pow, map_natCast] at hy
    exact mul_left_cancel₀ hne hy
  · have h0 : lam (Pi.single i 1) = 0 :=
      hS _ (fun s hs => Pi.single_eq_of_ne (by rintro rfl; exact hi hs) 1)
    rw [h0, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.FormPLamSmul
section
open UpperTheory.V.Z.Kato.Joint

private theorem formP_lam_add (B : ℕ) (cc a b : ℕ → ℂ) :
    GlobalTheory.EisM.lam B cc (a + b) = GlobalTheory.EisM.lam B cc a + GlobalTheory.EisM.lam B cc b := by
  unfold GlobalTheory.EisM.lam
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem formP_lam_smul (B : ℕ) (cc a : ℕ → ℂ) (r : ℂ) :
    GlobalTheory.EisM.lam B cc (r • a) = r * GlobalTheory.EisM.lam B cc a := by
  unfold GlobalTheory.EisM.lam
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem UpperTheory.V.Z.Kato.Joint.LocFacts₂ :
    UpperTheory.V.Z.Kato.Joint.FormP := by
  unfold UpperTheory.V.Z.Kato.Joint.FormP
  intro l _ ι k N χ t α B cc χE ev hk hE hχE hT hU hD P hP
  have hℓ : Nat.Prime l := Fact.out
  suffices key : ∀ a : ℕ → Formalism.ConjugateSelfDual.Qbar l,
      GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ) (fun i => ι (a i)) →
      GlobalTheory.EisM.MF k (N * l) (GlobalTheory.EisM.ch χ)
                   (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) P a i)) ∧
        (GlobalTheory.EisM.lam B cc fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) P a i)) =
          ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) ev) P) * GlobalTheory.EisM.lam B cc fun i => ι (a i) from
    fun a ha => (key a ha).2
  unfold GlobalTheory.KZ.admissibleLettersSubalgebra at hP
  induction hP using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨x, hx, rfl⟩ := hx
    intro a ha
    simp only [FreeAlgebra.lift_ι_apply]
    cases x with
    | T q =>
      obtain ⟨hq, hqn⟩ : Nat.Prime q ∧ ¬q ∣ N * l := hx
      have hcop : q.Coprime N :=
        Nat.Coprime.coprime_dvd_right (dvd_mul_right N l) ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqn)
      have hχq : ι (χE q) = GlobalTheory.EisM.ch χ (q : ℤ) := by
        rw [hχE q hcop]
        simp [GlobalTheory.EisM.ch]
      have hf : (fop k l χE (GlobalTheory.KZ.Letter.T q)) a = GlobalTheory.EisM.To k (χE q) q a := rfl
      have hcomm : (fun i => ι (GlobalTheory.EisM.To k (χE q) q a i)) =
          GlobalTheory.EisM.To k (GlobalTheory.EisM.ch χ (q : ℤ)) q (fun i => ι (a i)) := by
        funext m
        simp only [GlobalTheory.EisM.To, GlobalTheory.EisM.Vo, map_add, map_mul, map_pow, map_natCast, hχq]
        split_ifs <;> simp
      rw [hf, hcomm]
      refine ⟨GlobalTheory.T.isModularFormCoeffSeq_heckeT_of_prime_not_dvd k (N * l) N q χ _ hk (dvd_mul_right N l) hq hqn ha, ?_⟩
      rw [hE.T _ ha q hq hqn, hT q hq hqn]
    | U =>
      have hf : (fop k l χE GlobalTheory.KZ.Letter.U) a = GlobalTheory.EisM.Uo l a := rfl
      have hcomm : (fun i => ι (GlobalTheory.EisM.Uo l a i)) = GlobalTheory.EisM.Uo l (fun i => ι (a i)) := rfl
      rw [hf, hcomm]
      refine ⟨(GlobalTheory.T.isModularFormCoeffSeq_heckeU_and_depletion k (N * l) l _ (fun i => ι (a i)) hk hℓ (dvd_mul_left l N) ?_ ha).1, ?_⟩
      · intro d
        simp [GlobalTheory.EisM.ch]
      · rw [hE.U _ ha, hU]
    | D d =>
      have hd : d.Coprime N := hx
      have hf : (fop k l χE (GlobalTheory.KZ.Letter.D d)) a = χE d • a := rfl
      have hcomm : (fun i => ι ((χE d • a) i)) = ι (χE d) • fun i => ι (a i) := by
        funext i
        simp
      rw [hf, hcomm, formP_lam_smul, hD d hd]
      exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.2.1 _ _ ha).1, rfl⟩
  | algebraMap r =>
    intro a ha
    have hf : (FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) (algebraMap (Formalism.ConjugateSelfDual.Qbar l) _ r) a = r • a := by
      simp [Algebra.algebraMap_eq_smul_one]
    have hcomm : (fun i => ι ((r • a) i)) = ι r • fun i => ι (a i) := by
      funext i
      simp
    rw [hf, hcomm, formP_lam_smul, AlgHom.commutes]
    exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.2.1 _ _ ha).1, rfl⟩
  | add x y _ _ hx hy =>
    intro a ha
    obtain ⟨h1, h2⟩ := hx a ha
    obtain ⟨h3, h4⟩ := hy a ha
    have hcomm : (fun i => ι ((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE) (x + y)) a i)) =
        (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) x) a i)) +
          (fun i => ι (((FreeAlgebra.lift (Formalism.ConjugateSelfDual.Qbar l) (fop k l χE)) y) a i)) := by
      funext i
      simp
    rw [hcomm, formP_lam_add, h2, h4, map_add, map_add, add_mul]
    exact ⟨((GlobalTheory.T.modularFormCoeffSeq_linear_structure k (N * l) _).2.1 _ _ h1 h3).1, rfl⟩
  | mul x y _ _ hx hy =>
    intro a ha
    obtain ⟨h3, h4⟩ := hy a ha
    obtain ⟨h1, h2⟩ := hx _ h3
    simp only [map_mul, Module.End.mul_apply]
    refine ⟨h1, ?_⟩
    rw [h2, h4, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.FrobeniusHodgeTateLaws.SgDOneMem
section
open UpperTheory.V.Z.Kato.Joint
open Formalism.ConjugateSelfDual GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.CyclotomicQExpansion GlobalTheory.KummerEisensteinGalois GlobalTheory.K4 GlobalTheory.LambdaValuationPowers
open scoped Matrix MatrixGroups TensorProduct

namespace UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt

variable {l : ℕ} [Fact l.Prime]

private theorem norm_zl (c : ℤ_[l]) : ‖algebraMap ℤ_[l] (Qbar l) c‖ = ‖c‖ := by
  rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Qbar l), norm_algebraMap']
  rfl

private theorem nadd {r : ℝ} {x y : Qbar l} (hx : ‖x‖ ≤ r) (hy : ‖y‖ ≤ r) : ‖x + y‖ ≤ r :=
  (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

private theorem nmul {r : ℝ} {x y : Qbar l} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ r) : ‖x * y‖ ≤ r := by
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hx).trans hy

private theorem nappr (n : ℕ) (c : ℤ_[l]) :
    ‖((c.appr n : ℕ) : Qbar l) - algebraMap ℤ_[l] (Qbar l) c‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := by
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n c)
  have h := congrArg (algebraMap ℤ_[l] (Qbar l)) hz
  simp only [map_mul, map_pow, map_natCast, map_sub] at h
  rw [norm_sub_rev, ← h]
  exact nmul (by rw [norm_zl]; exact z.norm_le_one) le_rfl

private theorem extend {M : Type} [AddCommGroup M] [Module ℤ_[l] M] (B : Submodule ℤ_[l] M) [Module.Free ℤ_[l] B]
    (r : ℝ) (f : M → ℕ → Qbar l)
    (hf : ∀ b ∈ B, ∀ b' ∈ B, ∀ c c' : ℤ_[l], ∀ i,
      ‖f (c • b + c' • b') i - (algebraMap ℤ_[l] (Qbar l) c * f b i + algebraMap ℤ_[l] (Qbar l) c' * f b' i)‖ ≤ r) :
    ∃ Θ : (Qbar l ⊗[ℤ_[l]] M) →ₗ[Qbar l] (ℕ → Qbar l), ∀ b ∈ B, ∀ i, ‖Θ ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) i - f b i‖ ≤ r := by
  classical
  let e := Module.Free.chooseBasis ℤ_[l] B
  let g : B →ₗ[ℤ_[l]] (ℕ → Qbar l) := e.constr ℤ_[l] (fun k => f (e k))
  have h0 : ∀ i, ‖f 0 i‖ ≤ r := fun i => by simpa using hf 0 B.zero_mem 0 B.zero_mem 0 0 i
  have hr : 0 ≤ r := (norm_nonneg _).trans (h0 0)
  have hg : ∀ b : B, ∀ i, ‖g b i - f b i‖ ≤ r := by
    intro b i
    have hb : b ∈ Submodule.span ℤ_[l] (Set.range e) := by rw [e.span_eq]; trivial
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      simpa [g] using hr
    | zero => simpa using h0 i
    | add x y _ _ hx hy =>
      have h := hf x x.2 y y.2 1 1 i
      simp only [one_smul, map_one, one_mul] at h
      rw [← norm_neg] at h
      have := nadd (nadd hx hy) h
      convert this using 2
      simp only [map_add, Pi.add_apply, Submodule.coe_add]
      ring
    | smul c x _ hx =>
      have h := hf x x.2 0 B.zero_mem c 0 i
      simp only [zero_smul, add_zero, map_zero, zero_mul] at h
      rw [← norm_neg] at h
      have := nadd (nmul (x := algebraMap ℤ_[l] (Qbar l) c) (by rw [norm_zl]; exact c.norm_le_one) hx) h
      convert this using 2
      simp only [map_smul, Pi.smul_apply, Submodule.coe_smul, Algebra.smul_def]
      ring
  haveI : Module.IsTorsionFree ℤ_[l] (Qbar l) := by
    refine (Module.isTorsionFree_iff_algebraMap_injective).2 ?_
    rw [injective_iff_map_eq_zero]
    intro a ha
    have := norm_zl a
    rw [ha, norm_zero] at this
    exact norm_eq_zero.1 this.symm
  haveI : Module.Flat ℤ_[l] (Qbar l) := inferInstance
  have hinj : Function.Injective (B.subtype.baseChange (Qbar l)) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := Qbar l) B.subtype B.injective_subtype
  obtain ⟨s, hs⟩ := LinearMap.exists_leftInverse_of_injective (B.subtype.baseChange (Qbar l))
    (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨(g.liftBaseChange (Qbar l)) ∘ₗ s, fun b hb i => ?_⟩
  have h1 : s ((1 : Qbar l) ⊗ₜ[ℤ_[l]] b) = (1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : B) :=
    LinearMap.congr_fun hs ((1 : Qbar l) ⊗ₜ[ℤ_[l]] (⟨b, hb⟩ : B))
  simpa [h1] using hg ⟨b, hb⟩ i

private theorem sgD_one_mem {N : ℕ} (hN : N ≠ 0) : sgD N l 1 ∈ Gam N l := by
  obtain ⟨⟨h0, h1⟩, h2⟩ := Betti.isDiam_sgD (l := l) (d := 1) hN (Fact.out : l.Prime).ne_zero (Nat.coprime_one_left N)
  refine ⟨?_, h1⟩
  have h3 : (⟨sgD N l 1, h0⟩ : CongruenceSubgroup.Gamma0 N) ∈ CongruenceSubgroup.Gamma1' N := by
    rw [CongruenceSubgroup.Gamma1_mem']
    simpa [en, CongruenceSubgroup.Gamma0Map] using h2
  exact (CongruenceSubgroup.Gamma1_mem N _).2 ((CongruenceSubgroup.Gamma1_to_Gamma0_mem _).1 h3)

private theorem act_fix {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) {N w : ℕ} {γ : SL(2, ℤ)}
    (hγ : γ ∈ Gam N l) {b : X.Fn l} (hb : b ∈ X.B N l w) : X.act l (γ : Matrix (Fin 2) (Fin 2) ℤ) b = b := by
  induction hb using Submodule.span_induction with
  | mem x hx => exact hx.2 γ hγ
  | zero => exact map_zero _
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

end UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt

open UpperTheory.V.Z.Kato.Joint.ThetaLinearAlt in
theorem UpperTheory.V.Z.Kato.Joint.thLin :
    UpperTheory.V.Z.Kato.Joint.ThLin := by
  intro l _ Ω _ _ _ ε X A N w j hS n
  obtain ⟨hA, h2, hlN, h5, hw, hj⟩ := hS
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hcop : Nat.Coprime N l := ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hlN).symm
  have hhol : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero) := by
    obtain ⟨φ, h1, h2⟩ := X.j_hol; exact ⟨φ, h2, h1⟩
  haveI := (GlobalTheory.T.kummerBettiModule_free_finite ε X ε.injective hhol N l w h2 h5 hcop hw).1
  have hth : ∀ b ∈ X.B N l w, IsThB X A N l n b (thN X A N l n 1 b) := by
    intro b hb
    have h := (GlobalTheory.T.theta_lattice_diamond_action Ω ε X A N l X.j_hol h2 hlN h5 hA n w 1 hw (Nat.coprime_one_left N) b hb).1
    rwa [act_fix X (sgD_one_mem (by omega)) hb] at h
  have hint : ∀ b ∈ X.B N l w, ∀ i, ‖th X A N j n b i‖ ≤ 1 := by
    intro b hb i
    obtain ⟨f, -, -, -, h, -⟩ := hth b hb
    exact hj _ (h _)
  refine extend (X.B N l w) ‖((l : ℕ) : Qbar l) ^ n‖ (th X A N j n) ?_
  intro b hb b' hb' c c' i
  have hm : c • b + c' • b' ∈ X.B N l w := add_mem (Submodule.smul_mem _ _ hb) (Submodule.smul_mem _ _ hb')
  obtain ⟨z, hz, h⟩ := GlobalTheory.T.cuspFunctionalValueModPrimePow_unique_oddWeight Ω ε X A N l X.j_hol h2 hlN h5 hA n w hw _ hm _ _ (hth _ hm)
    (GlobalTheory.T.theta_basis_linear_combination Ω ε X A N l n w b b' hb hb' c c' _ _ (hth b hb) (hth b' hb')) ((i : ℚ) / ((1 : ℕ) : ℚ))
  have h1 := congrArg j h
  simp only [HahnSeries.coeff_add, HahnSeries.coeff_smul, smul_eq_mul, map_sub, map_add, map_mul, map_pow,
    map_natCast] at h1
  have h3 : ‖j z * ((l : ℕ) : Qbar l) ^ n‖ ≤ ‖((l : ℕ) : Qbar l) ^ n‖ := nmul (hj z hz) le_rfl
  have := nadd (nadd h3 (nmul (hint b hb i) (nappr n c))) (nmul (hint b' hb' i) (nappr n c'))
  convert this using 2
  simp only [th, seqN]
  linear_combination h1
end

