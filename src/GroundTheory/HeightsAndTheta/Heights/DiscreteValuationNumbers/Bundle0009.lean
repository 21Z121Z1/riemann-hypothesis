import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PRelevantDimGe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem RelevantDimGe.proof (h1 : BlockAdjoinPrime.Statement.{u}) : RelevantDimGe.Statement.{u} := by
  intro R _ K _ _ ι Q hQ
  classical
  let e : K ≃ Fin (Fintype.card K) := Fintype.equivFin K
  let B : ℕ → Set K := fun j => {k | (e k : ℕ) < j}
  let J : ℕ → Ideal (MRing ι R) := fun j =>
    Q ⊔ Ideal.span {p | ∃ v : Σ k, ι k, v.1 ∈ B j ∧ p = X v}
  have hJ : ∀ j, (J j).IsPrime ∧ ∀ v : Σ k, ι k, v.1 ∉ B j → (X v ∈ J j ↔ X v ∈ Q) :=
    fun j => h1 R K ι Q (B j) hQ.isPrime hQ.multiHomog
  have hle : ∀ j, Q ≤ J j := fun j => le_sup_left
  have hmono : ∀ j, J j ≤ J (j + 1) := fun j =>
    sup_le_sup_left (Ideal.span_mono (by
      rintro p ⟨v, hv, rfl⟩
      exact ⟨v, lt_trans hv (Nat.lt_succ_self _), rfl⟩)) _
  have hstrict : ∀ j (hj : j < Fintype.card K), J j < J (j + 1) := by
    intro j hj
    refine lt_of_le_of_ne (hmono j) ?_
    obtain ⟨i, hi⟩ := hQ.relevant (e.symm ⟨j, hj⟩)
    intro heq
    have hmem : (X ⟨e.symm ⟨j, hj⟩, i⟩ : MRing ι R) ∈ J (j + 1) :=
      Ideal.mem_sup_right (Ideal.subset_span ⟨⟨e.symm ⟨j, hj⟩, i⟩, by simp [B], rfl⟩)
    rw [← heq] at hmem
    exact hi (((hJ j).2 ⟨e.symm ⟨j, hj⟩, i⟩ (by simp [B])).1 hmem)
  let f : Fin (Fintype.card K + 1) → PrimeSpectrum.zeroLocus (R := MRing ι R) (Q : Set (MRing ι R)) :=
    fun j => ⟨⟨J j, (hJ j).1⟩, hle j⟩
  have hf : StrictMono f := by
    refine Fin.strictMono_iff_lt_succ.2 fun j => ?_
    show J j < J (j + 1)
    exact hstrict j j.isLt
  rw [ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim (LTSeries.mk (Fintype.card K) f hf)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialCycleEval
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem SpecialCycleEval.proof (h1 : SpecialIdealCorresp.Statement.{u})
    (h2 : SpecialIdealSurj.Statement.{u}) (h3 : SpecialMultAt.Statement.{u}) :
    SpecialCycleEval.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P n
  classical
  let s : Set (Ideal (MRing ι O)) :=
    {W | W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W}
  let t : Set (Ideal (MRing ι (IsLocalRing.ResidueField O))) :=
    {V | V ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant V}
  have hsupp1 : Function.support (fun W => divCycle P (C ϖ) W * n (specialIdeal W)) ⊆ s := by
    intro W hW
    by_contra h
    apply hW
    show divCycle P (C ϖ) W * n (specialIdeal W) = 0
    have h' : ¬ (W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W) := h
    unfold divCycle
    rw [dif_neg h', zero_mul]
  have hsupp2 : Function.support (fun V => idealCycle (specialIdeal P) V * n V) ⊆ t := by
    intro V hV
    by_contra h
    apply hV
    show idealCycle (specialIdeal P) V * n V = 0
    have h' : ¬ (V ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant V) := h
    unfold idealCycle
    rw [dif_neg h', zero_mul]
  have hmem : ∀ W ∈ s, W.IsPrime ∧ (C ϖ : MRing ι O) ∈ W := fun W hW =>
    ⟨hW.1.1.1, hW.1.1.2 (Ideal.mem_sup_right (Ideal.subset_span rfl))⟩
  have hmaps : ∀ W ∈ s, specialIdeal W ∈ t := by
    intro W hW
    obtain ⟨hp, hc⟩ := hmem W hW
    obtain ⟨-, hmin, hrel, -⟩ := h1 O ϖ hϖ K ι P W hp hc
    exact ⟨hmin.mp hW.1, hrel.mp hW.2⟩
  have e1 : (∑ᶠ W, divCycle P (C ϖ) W * n (specialIdeal W)) =
      ∑ᶠ W ∈ s, divCycle P (C ϖ) W * n (specialIdeal W) := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp1]
  have e2 : (∑ᶠ V, idealCycle (specialIdeal P) V * n V) =
      ∑ᶠ V ∈ t, idealCycle (specialIdeal P) V * n V := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsupp2]
  show (∑ᶠ W, divCycle P (C ϖ) W * n (specialIdeal W)) =
    ∑ᶠ V, idealCycle (specialIdeal P) V * n V
  rw [e1, e2]
  refine finsum_mem_eq_of_bijOn specialIdeal ⟨hmaps, ?_, ?_⟩ ?_
  · intro W hW W' hW' heq
    obtain ⟨hp, hc⟩ := hmem W hW
    obtain ⟨hp', hc'⟩ := hmem W' hW'
    exact ((h1 O ϖ hϖ K ι P W hp hc).2.2.2 W' hp' hc' heq.symm).symm
  · intro V hV
    have hVp : V.IsPrime := hV.1.1.1
    obtain ⟨W, hWp, hc, rfl⟩ := h2 O ϖ hϖ K ι V hVp
    obtain ⟨-, hmin, hrel, -⟩ := h1 O ϖ hϖ K ι P W hWp hc
    exact ⟨W, ⟨hmin.mpr hV.1, hrel.mpr hV.2⟩, rfl⟩
  · intro W hW
    obtain ⟨hp, hc⟩ := hmem W hW
    have := hp
    have := (h1 O ϖ hϖ K ι P W hp hc).1
    have hm := h3 O ϖ hϖ K ι P W hc
    congr 1
    unfold divCycle idealCycle
    have hW' : W ∈ (P ⊔ Ideal.span {C ϖ}).minimalPrimes ∧ IsRelevant W := hW
    have hV' : specialIdeal W ∈ (specialIdeal P).minimalPrimes ∧ IsRelevant (specialIdeal W) :=
      hmaps W hW
    rw [dif_pos hW', dif_pos hV']
    exact congrArg (fun x : ℕ∞ => ((x.toNat : ℕ) : ℤ)) hm

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialDimBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem withBotENat_lt_of_add_one_le {a : WithBot ℕ∞} {n : ℕ} (h : a + 1 ≤ (n : WithBot ℕ∞)) :
    a < (n : WithBot ℕ∞) := by
  induction a using WithBot.recBotCoe with
  | bot => exact WithBot.bot_lt_coe _
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      exfalso
      have h' : ((⊤ : ℕ∞) + 1 : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      simp at h'
    | coe m =>
      have h' : ((m + 1 : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by exact_mod_cast h
      have h'' : m + 1 ≤ n := by exact_mod_cast h'
      exact_mod_cast (show m < n by omega)

theorem SpecialDimBound.proof : SpecialDimBound.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P d hP
  have := hP.multiProj.isPrime
  set φ : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O) with hφdef
  have hφ : Function.Surjective φ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker φ = Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hφdef, MvPolynomial.ker_map, IsLocalRing.ker_residue, hϖ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]

  set g : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk (specialIdeal P)).comp φ with hgdef
  have hg : Function.Surjective g := Ideal.Quotient.mk_surjective.comp hφ
  have hkg : RingHom.ker g = P ⊔ Ideal.span {(C ϖ : MRing ι O)} := by
    rw [hgdef, ← RingHom.comap_ker, Ideal.mk_ker, specialIdeal, ← hφdef,
      Ideal.comap_map_of_surjective _ hφ, ← RingHom.ker_eq_comap_bot, hker]
  have e1 : MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) ≃+*
      MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.quotEquivOfEq hkg.symm).trans (RingHom.quotientKerEquivOfSurjective hg)

  set r : MRing ι O ⧸ P := Ideal.Quotient.mk P (C ϖ) with hrdef
  have hspan : (Ideal.span {(C ϖ : MRing ι O)}).map (Ideal.Quotient.mk P) = Ideal.span {r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have e2 : (MRing ι O ⧸ P) ⧸ Ideal.span {r} ≃+* MRing ι O ⧸ (P ⊔ Ideal.span {(C ϖ : MRing ι O)}) :=
    (Ideal.quotEquivOfEq hspan.symm).trans (DoubleQuot.quotQuotEquivQuotSup P _)

  have hr0 : r ≠ 0 := by
    intro h0
    rw [hrdef, Ideal.Quotient.eq_zero_iff_mem] at h0
    have hmem : ϖ ∈ P.comap (C : O →+* MRing ι O) := h0
    rw [hP.noTorsion, Ideal.mem_bot] at hmem
    exact hϖ.ne_zero hmem
  have hr : r ∈ nonZeroDivisors (MRing ι O ⧸ P) := mem_nonZeroDivisors_of_ne_zero hr0
  have hle := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr
  rw [hP.dim, ringKrullDim_eq_of_ringEquiv e2, ringKrullDim_eq_of_ringEquiv e1] at hle
  exact withBotENat_lt_of_add_one_le hle

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealCorresp
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

universe u

theorem ker_map_residue_eq_span {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {ϖ : O} (hϖ : Irreducible ϖ) {σ : Type*} :
    RingHom.ker (MvPolynomial.map (IsLocalRing.residue O) : MvPolynomial σ O →+* _) =
      Ideal.span {C ϖ} := by
  rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
    Set.image_singleton]

theorem SpecialIdealCorresp.proof : SpecialIdealCorresp.Statement := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P W hW hϖW
  obtain ⟨π, hπ⟩ : ∃ π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O),
      π = MvPolynomial.map (IsLocalRing.residue O) := ⟨_, rfl⟩
  have hsp : ∀ V : Ideal (MRing ι O), specialIdeal V = V.map π := fun V => by rw [hπ]; rfl
  have hsurj : Function.Surjective π := hπ ▸ MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := hπ ▸ ker_map_residue_eq_span hϖ
  have hle : ∀ {V : Ideal (MRing ι O)}, (C ϖ : MRing ι O) ∈ V → RingHom.ker π ≤ V := fun h => by
    rw [hker, Ideal.span_le, Set.singleton_subset_iff]; exact h
  have hcm : ∀ {V : Ideal (MRing ι O)}, (C ϖ : MRing ι O) ∈ V → (V.map π).comap π = V := fun h => by
    rw [Ideal.comap_map_of_surjective' π hsurj, sup_eq_left.mpr (hle h)]
  simp only [hsp]
  refine ⟨Ideal.map_isPrime_of_surjective hsurj (hle hϖW), ?_, ?_, ?_⟩
  · have hJ : P ⊔ Ideal.span {C ϖ} = (P.map π).comap π := by
      rw [Ideal.comap_map_of_surjective' π hsurj, hker]
    rw [hJ, Ideal.comap_minimalPrimes_eq_of_surjective hsurj]
    constructor
    · rintro ⟨Q, hQ, rfl⟩
      rwa [Ideal.map_comap_of_surjective π hsurj]
    · intro h
      exact ⟨_, h, hcm hϖW⟩
  · have hX : ∀ v, (X v : MRing ι O) ∈ W ↔ (X v : MRing ι (IsLocalRing.ResidueField O)) ∈ W.map π :=
      fun v => by
        conv_lhs => rw [← hcm hϖW]
        rw [Ideal.mem_comap, hπ, MvPolynomial.map_X]
    simp only [IsRelevant, hX]
  · intro W' _ hϖW' h
    rw [← hcm hϖW', ← hcm hϖW, h]

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialIdealMultiHomog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

attribute [local instance] MvPolynomial.weightedGradedAlgebra

universe u

theorem isWeightedHomogeneous_map_of {σ M R S : Type*} [AddCommMonoid M] [CommRing R]
    [CommRing S] (f : R →+* S) (w : σ → M) {p : MvPolynomial σ R} {b : M}
    (hp : IsWeightedHomogeneous w p b) : IsWeightedHomogeneous w (MvPolynomial.map f p) b := by
  intro d hd
  rw [coeff_map] at hd
  apply hp
  intro h0
  exact hd (by rw [h0, map_zero])

theorem span_forms_of_isMultiHomogIdeal {K : Type} [DecidableEq K] {ι : K → Type}
    {R : Type*} [CommRing R] {P : Ideal (MRing ι R)} (hP : IsMultiHomogIdeal P) :
    Ideal.span {f | f ∈ P ∧ ∃ b, IsWeightedHomogeneous (blockWeight ι) f b} = P := by
  apply le_antisymm
  · rw [Ideal.span_le]
    exact fun f hf => hf.1
  · intro p hp
    rw [← sum_weightedHomogeneousComponent (w := blockWeight ι) p,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp p)]
    refine Ideal.sum_mem _ fun m _ => Ideal.subset_span ⟨hP p hp m, m, ?_⟩
    exact weightedHomogeneousComponent_isWeightedHomogeneous m p

theorem SpecialIdealMultiHomog.proof : SpecialIdealMultiHomog.Statement := by
  classical
  intro O _ _ _ K _ ι P hP
  have hspan : specialIdeal P = Ideal.span
      (MvPolynomial.map (IsLocalRing.residue O) ''
        {f | f ∈ P ∧ ∃ b, IsWeightedHomogeneous (blockWeight ι) f b}) := by
    rw [specialIdeal, ← Ideal.map_span, span_forms_of_isMultiHomogIdeal hP]
  have hhom : (specialIdeal P).IsHomogeneous
      (weightedHomogeneousSubmodule (IsLocalRing.ResidueField O) (blockWeight ι)) := by
    rw [hspan]
    apply Ideal.homogeneous_span
    rintro _ ⟨f, ⟨_, b, hb⟩, rfl⟩
    exact ⟨b, (mem_weightedHomogeneousSubmodule _ _ _ _).2
      (isWeightedHomogeneous_map_of _ _ hb)⟩
  intro f hf b
  exact weightedHomogeneousComponent_mem_of_mem _ _ hhom hf b

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PSpecialMultAt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem length_localizedModule_eq_of_surjective {S T : Type*} [CommRing S] [CommRing T]
    (π : S →+* T) (hπ : Function.Surjective π) (Q : Ideal T) [Q.IsPrime] (W : Ideal S) [W.IsPrime]
    (hW : W = Q.comap π) (M N : Type*) [AddCommGroup M] [Module S M] [AddCommGroup N] [Module T N]
    (e : M ≃+ N) (he : ∀ (s : S) (x : M), e (s • x) = π s • e x) :
    Module.length (Localization.AtPrime W) (LocalizedModule W.primeCompl M) =
      Module.length (Localization.AtPrime Q) (LocalizedModule Q.primeCompl N) := by
  let φ : Localization.AtPrime W →+* Localization.AtPrime Q := Localization.localRingHom W Q π hW
  have hmem : ∀ s : S, s ∈ W.primeCompl ↔ π s ∈ Q.primeCompl := fun s => by
    subst hW; rfl
  have hφ : ∀ s : S, φ (algebraMap S _ s) = algebraMap T _ (π s) :=
    Localization.localRingHom_to_map W Q π hW
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨⟨t, u⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl b
    obtain ⟨s, rfl⟩ := hπ t
    obtain ⟨v, hv⟩ := hπ u
    refine ⟨IsLocalization.mk' _ s (⟨v, (hmem v).2 (hv ▸ u.2)⟩ : W.primeCompl), ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hv
  let _ : Algebra (Localization.AtPrime W) (Localization.AtPrime Q) := φ.toAlgebra
  let _ : Module (Localization.AtPrime W) (LocalizedModule Q.primeCompl N) := Module.compHom _ φ
  have _ : IsScalarTower (Localization.AtPrime W) (Localization.AtPrime Q)
      (LocalizedModule Q.primeCompl N) :=
    ⟨fun a b n => mul_smul (φ a) b n⟩
  let _ : Module S (LocalizedModule Q.primeCompl N) := Module.compHom _ (φ.comp (algebraMap S _))
  have _ : IsScalarTower S (Localization.AtPrime W) (LocalizedModule Q.primeCompl N) :=
    ⟨fun s a n => by
      show φ (s • a) • n = φ (algebraMap S _ s) • (φ a • n)
      rw [Algebra.smul_def, map_mul, mul_smul]⟩
  have hsmul : ∀ (s : S) (y : LocalizedModule Q.primeCompl N), s • y = π s • y := fun s y => by
    show φ (algebraMap S _ s) • y = _
    rw [hφ, algebraMap_smul]
  let g : M →ₗ[S] LocalizedModule Q.primeCompl N :=
    { toFun := fun x => LocalizedModule.mkLinearMap Q.primeCompl N (e x)
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun s x => by
        rw [RingHom.id_apply, hsmul, he, LinearMap.map_smul] }
  have hg : IsLocalizedModule W.primeCompl g := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ?_⟩
    · have hu : IsUnit (φ (algebraMap S _ (s : S))) :=
        (IsLocalization.map_units (Localization.AtPrime W) s).map φ
      rw [Module.End.isUnit_iff]
      refine ⟨fun y z h => ?_, fun y => ⟨((hu.unit⁻¹ : (Localization.AtPrime Q)ˣ) :
        Localization.AtPrime Q) • y, ?_⟩⟩
      · rw [Module.algebraMap_end_apply, Module.algebraMap_end_apply] at h
        exact hu.smul_left_cancel.mp h
      · rw [Module.algebraMap_end_apply]
        show φ (algebraMap S _ (s : S)) • _ = y
        rw [← mul_smul, hu.mul_val_inv, one_smul]
    · induction y using LocalizedModule.induction_on with
      | h n t =>
      obtain ⟨s, hs⟩ := hπ t
      refine ⟨(e.symm n, ⟨s, (hmem s).2 (hs ▸ t.2)⟩), ?_⟩
      show s • LocalizedModule.mk n t = LocalizedModule.mk (e (e.symm n)) 1
      rw [hsmul, hs, AddEquiv.apply_symm_apply, LocalizedModule.smul'_mk]
      exact LocalizedModule.mk_cancel t n
    · have h' : LocalizedModule.mk (e x₁) (1 : Q.primeCompl) = LocalizedModule.mk (e x₂) 1 := h
      obtain ⟨c, hc⟩ := LocalizedModule.mk_eq.mp h'
      obtain ⟨s, hs⟩ := hπ c
      refine ⟨⟨s, (hmem s).2 (hs ▸ c.2)⟩, e.injective ?_⟩
      show e (s • x₁) = e (s • x₂)
      rw [he, he, hs]
      simpa [Submonoid.smul_def] using hc
  let eA := (IsLocalizedModule.iso W.primeCompl g).extendScalarsOfIsLocalization W.primeCompl
    (Localization.AtPrime W)
  rw [eA.length_eq]
  exact Module.length_eq_of_surjective hsurj

theorem SpecialMultAt.proof : SpecialMultAt.Statement.{u} := by
  intro O _ _ _ ϖ hϖ K _ _ ι _ P W _ hW _
  let π : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) :=
    MvPolynomial.map (IsLocalRing.residue O)
  have hspec : ∀ I : Ideal (MRing ι O), specialIdeal I = I.map π := fun _ => rfl
  have hπ : Function.Surjective π := MvPolynomial.map_surjective _ IsLocalRing.residue_surjective
  have hker : RingHom.ker π = Ideal.span {C ϖ} := by
    rw [MvPolynomial.ker_map, IsLocalRing.ker_residue,
      (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ, Ideal.map_span,
      Set.image_singleton]
  have hcm : ∀ I : Ideal (MRing ι O), (specialIdeal I).comap π = I ⊔ Ideal.span {C ϖ} := by
    intro I
    rw [hspec, Ideal.comap_map_of_surjective π hπ, ← RingHom.ker_eq_comap_bot, hker]
  have hWc : W = (specialIdeal W).comap π := by
    rw [hcm]
    exact (sup_eq_left.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hW))).symm
  let f : MRing ι O →+* MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal P :=
    (Ideal.Quotient.mk _).comp π
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective.comp hπ
  have hkerf : RingHom.ker f = P ⊔ Ideal.span {C ϖ} := by
    rw [← hcm]
    ext x
    simp [f, RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]
  let e := ((Ideal.quotEquivOfEq hkerf.symm).trans (RingHom.quotientKerEquivOfSurjective hf))
  have hemk : ∀ z, e (Ideal.Quotient.mk _ z) = f z := fun z => rfl
  have he : ∀ (s : MRing ι O) (x : MRing ι O ⧸ (P ⊔ Ideal.span {C ϖ})),
      e.toAddEquiv (s • x) = π s • e.toAddEquiv x := by
    intro s x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp only [RingEquiv.toAddEquiv_eq_coe, RingEquiv.coe_toAddEquiv, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, hemk]
    simp [f]
    rw [← map_mul]
    rfl
  exact length_localizedModule_eq_of_surjective π hπ (specialIdeal W) W hWc _ _ e.toAddEquiv he

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTopDimMinimal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u

theorem TopDimMinimal.proof (h1 : DimStrictDrop.Statement.{u}) : TopDimMinimal.Statement.{u} := by
  intro A _ J Q _ N hJQ hJ hQ
  by_contra hmin
  obtain ⟨W, hW, hWQ⟩ := Ideal.exists_minimalPrimes_le hJQ
  have hWne : W ≠ Q := fun h => hmin (h ▸ hW)
  have hWlt : W < Q := lt_of_le_of_ne hWQ hWne
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := hW.1.2
  have h2 : ringKrullDim (A ⧸ Q) + 1 ≤ ringKrullDim (A ⧸ W) := h1 A W Q hWlt
  have h3 : ringKrullDim (A ⧸ W) ≤ ringKrullDim (A ⧸ J) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hJW) (Ideal.Quotient.factor_surjective hJW)
  have h4 : ((N : ℕ) : WithBot ℕ∞) + 1 ≤ ringKrullDim (A ⧸ Q) + 1 :=
    add_le_add (not_lt.mp hQ) le_rfl
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) = ((N : ℕ) : WithBot ℕ∞) + 1 := Nat.cast_succ N
  exact lt_irrefl _ (lt_of_le_of_lt (h5 ▸ h4.trans (h2.trans h3)) hJ)

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsComponentDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def ComponentDim.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      ∀ (a : K → ℕ) (f : MRing ι O), IsMultiHomog f a → f ∉ P →
      ∀ W : Ideal (MRing ι O), divCycle P f W ≠ 0 → (C ϖ : MRing ι O) ∈ W →
        ringKrullDim (MRing ι O ⧸ W) = ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFibreVar
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

def FibreVarieties.Statement : Prop :=
  ∀ (O : Type u) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ →
    ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d →
      (IsMultiProjPrime (genFib P) ∧
        ringKrullDim (MRing ι (FractionRing O) ⧸ genFib P) =
          ((d + Fintype.card K : ℕ) : WithBot ℕ∞)) ∧
      ∀ W : Ideal (MRing ι O), divCycle P (C ϖ) W ≠ 0 →
        IsMultiProjPrime (specialIdeal W) ∧
          ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
            ((d + Fintype.card K : ℕ) : WithBot ℕ∞)

end

end GroundTheory.Heights₂.Heights.NumbersDVR
end

