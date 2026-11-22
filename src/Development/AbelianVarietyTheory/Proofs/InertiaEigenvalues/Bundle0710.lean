import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemOfLpCharLpSpEqSumList
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0023
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0450
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0435
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0691
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteRationalConjMemBoundedCompact
import Formalism.LocalToGlobal.IndefiniteReal.Bridge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerImagesOrthogonalDisjointSplitSupport
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0699
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDeltaPsi
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleEmptyOfGood
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CardInversePrimeRepsIntegralRightMulHecke
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FockVectorsKilledHeisenbergAverageIsotropic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentMulNatPowOfMul
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0486
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0689

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PermOfWeilDeligneSpecialDecompositionEq
section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Published
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.WeilDeligne.SpUnique

open SpSummand

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

section Rep

variable {V U U' : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
  [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U] [AddCommGroup U'] [Module ℂ U']
  [FiniteDimensional ℂ U'] {ρ : Representation ℂ (Weil h) V} {k : ℕ} {c : Weil h → ℂ}

theorem hasCopy_sum_left {b : WDRep h U} (b' : WDRep h U') (H : HasCopy ρ k c b) :
    HasCopy ρ k c (b.sum b') := by
  obtain ⟨f, g, hf, hc, rfl⟩ := H
  refine ⟨LinearMap.inl ℂ U U' ∘ₗ ((b.N ^ k) ∘ₗ g), LinearMap.inl ℂ U U' ∘ₗ g, ?_, fun σ v => ?_, ?_⟩
  · intro h0
    apply hf
    refine LinearMap.ext fun v => ?_
    have := congrArg Prod.fst (LinearMap.congr_fun h0 v)
    simpa using this
  · have := hc σ v
    refine Prod.ext ?_ ?_
    · simpa using this
    · simp
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, sum_N_pow]
    refine Prod.ext ?_ ?_ <;> simp

theorem hasCopy_sum_right (b : WDRep h U) {b' : WDRep h U'} (H : HasCopy ρ k c b') :
    HasCopy ρ k c (b.sum b') := by
  obtain ⟨f, g, hf, hc, rfl⟩ := H
  refine ⟨LinearMap.inr ℂ U U' ∘ₗ ((b'.N ^ k) ∘ₗ g), LinearMap.inr ℂ U U' ∘ₗ g, ?_, fun σ v => ?_, ?_⟩
  · intro h0
    apply hf
    refine LinearMap.ext fun v => ?_
    have := congrArg Prod.snd (LinearMap.congr_fun h0 v)
    simpa using this
  · have := hc σ v
    refine Prod.ext ?_ ?_
    · simp
    · simpa using this
  · refine LinearMap.ext fun v => ?_
    rw [LinearMap.comp_apply, sum_N_pow]
    refine Prod.ext ?_ ?_ <;> simp

theorem powZero_sum {b : WDRep h U} {b' : WDRep h U'} (H : PowZero k b) (H' : PowZero k b') :
    PowZero k (b.sum b') := by
  unfold PowZero at *
  rw [sum_N_pow, H, H', LinearMap.prodMap_zero]

theorem powZero_of_le (a : WDRep h U) (ha : a.ρ.IsIrreducible) {m : ℕ} (hmk : m ≤ k) :
    PowZero k (a.tensor (WDRep.sp h (m + 1))) := by
  unfold PowZero
  rw [tensor_sp_N_pow a (N_eq_zero_of_irr a ha), shiftEnd_pow_eq_zero (by omega),
    LinearMap.lTensor_zero]

theorem hasCopyW_lpSum_left (x y : WD h) (H : HasCopyW ρ k c x) : HasCopyW ρ k c (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, hasCopyW_mk]
      rw [hasCopyW_mk] at H
      exact hasCopy_sum_left b H

theorem hasCopyW_lpSum_right (x y : WD h) (H : HasCopyW ρ k c y) : HasCopyW ρ k c (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, hasCopyW_mk]
      rw [hasCopyW_mk] at H
      exact hasCopy_sum_right a H

theorem powZeroW_lpSum_of (x y : WD h) (H : PowZeroW k x) (H' : PowZeroW k y) :
    PowZeroW k (x.lpSum y) := by
  induction x using WD.ind with
  | hP n a =>
    induction y using WD.ind with
    | hP n' b =>
      rw [WD.lpSum_mk, powZeroW_mk]
      rw [powZeroW_mk] at H H'
      exact powZero_sum H H'

theorem powZeroW_lpZero : PowZeroW k (WD.lpZero h) := by
  rw [WD.lpZero, powZeroW_mk]
  show (WDRep.diag h _).N ^ (k + 1) = 0
  rw [WDRep.diag_N, zero_pow (Nat.succ_ne_zero k)]

theorem hasCopyW_sumList {α : Type} (F : α → WD h) (l : List α) (p : α) (hp : p ∈ l)
    (H : HasCopyW ρ k c (F p)) : HasCopyW ρ k c (sumList (l.map F)) := by
  induction l with
  | nil => cases hp
  | cons q l ih =>
    change HasCopyW ρ k c ((F q).lpSum (sumList (l.map F)))
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hasCopyW_lpSum_left _ _ H
    · exact hasCopyW_lpSum_right _ _ (ih hp)

theorem powZeroW_sumList {α : Type} (F : α → WD h) (l : List α) (H : ∀ p ∈ l, PowZeroW k (F p)) :
    PowZeroW k (sumList (l.map F)) := by
  induction l with
  | nil => exact powZeroW_lpZero
  | cons q l ih =>
    change PowZeroW k ((F q).lpSum (sumList (l.map F)))
    exact powZeroW_lpSum_of _ _ (H q List.mem_cons_self) (ih fun p hp => H p (List.mem_cons_of_mem _ hp))

end Rep

theorem sumList_perm {l l' : List (WD h)} (hp : l.Perm l') : sumList l = sumList l' := by
  induction hp with
  | nil => rfl
  | cons x _ ih =>
    show WD.lpSum x (sumList _) = WD.lpSum x (sumList _)
    rw [ih]
  | swap x y l =>
    show WD.lpSum y (WD.lpSum x (sumList l)) = WD.lpSum x (WD.lpSum y (sumList l))
    rw [← WD.lpSum_assoc, ← WD.lpSum_assoc, WD.lpSum_comm x y]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem lpDim_pos (p : WD h × ℕ) (hp : IsIrrWD p.1) :
    0 < WD.lpDim (p.1.lpChar (WD.lpSp h (p.2 + 1))) := by
  obtain ⟨n, a, ha, hirr⟩ := hp
  rw [WD.lpDim_tensor, WD.lpDim_lpSp, ← ha, WD.lpDim_mk, Module.finrank_fin_fun]
  obtain ⟨v, hv⟩ := exists_ne_zero hirr
  have hn : n ≠ 0 := by
    rintro rfl
    exact hv (Subsingleton.elim _ _)
  exact Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.succ_pos _)

theorem perm_of_sumList_lpChar_lpSp_eq : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (l l' : List (WD h × ℕ)), (∀ p ∈ l, IsIrrWD p.1) → (∀ p ∈ l', IsIrrWD p.1) → sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) = sumList (l'.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) → l.Perm l' := by
  intro E Ω _ _ _ _ _ A w h l l'
  classical
  suffices H : ∀ n (l l' : List (WD h × ℕ)), l.length = n → (∀ p ∈ l, IsIrrWD p.1) →
      (∀ p ∈ l', IsIrrWD p.1) →
      sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) =
        sumList (l'.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1)))) → l.Perm l' from
    H _ l l' rfl
  intro n
  induction n with
  | zero =>
    intro l l' hn hl hl' heq
    obtain rfl := List.length_eq_zero_iff.1 hn
    cases l' with
    | nil => exact List.Perm.nil
    | cons q l'' =>
      exfalso
      have hd := congrArg WD.lpDim heq
      change WD.lpDim (WD.lpZero h) = WD.lpDim (WD.lpSum _ (sumList _)) at hd
      rw [WD.lpDim_zero, WD.lpDim_sum] at hd
      have := lpDim_pos q (hl' q List.mem_cons_self)
      beta_reduce at hd
      omega
  | succ n ih =>
    intro l l' hn hl hl' heq
    have hne : l ≠ [] := by
      rintro rfl
      simp at hn
    obtain ⟨⟨y, k⟩, hp, hmax⟩ : ∃ p ∈ l, ∀ q ∈ l, q.2 ≤ p.2 := by
      obtain ⟨p, hp, hmax⟩ := l.toFinset.exists_max_image Prod.snd
        (by obtain ⟨x, hx⟩ := List.exists_mem_of_ne_nil l hne; exact ⟨x, List.mem_toFinset.2 hx⟩)
      exact ⟨p, List.mem_toFinset.1 hp, fun q hq => hmax q (List.mem_toFinset.2 hq)⟩
    obtain ⟨m, a, rfl, ha⟩ := hl _ hp

    have hQ : HasCopyW a.ρ k (lastEig h k)
        (sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1))))) := by
      refine hasCopyW_sumList _ l _ hp ?_
      show HasCopyW a.ρ k (lastEig h k) ((WD.mk a).lpChar (WD.lpSp h (k + 1)))
      rw [WD.lpSp, WD.lpChar_mk, hasCopyW_mk]
      exact hasCopy_self a ha k
    have hZ : PowZeroW k
        (sumList (l.map (fun p : WD h × ℕ => p.1.lpChar (WD.lpSp h (p.2 + 1))))) := by
      refine powZeroW_sumList _ l fun q hq => ?_
      rcases q with ⟨y', k'⟩
      obtain ⟨m', a', rfl, ha'⟩ := hl _ hq
      show PowZeroW k ((WD.mk a').lpChar (WD.lpSp h (k' + 1)))
      rw [WD.lpSp, WD.lpChar_mk, powZeroW_mk]
      exact powZero_of_le a' ha' (hmax _ hq)
    rw [heq] at hQ hZ
    obtain ⟨⟨y', k'⟩, hq', hqQ, hqZ⟩ := exists_mem_of_sumList _ l' hQ hZ
    obtain ⟨n', a', rfl, ha'⟩ := hl' _ hq'
    dsimp only at hqQ hqZ
    rw [WD.lpSp, WD.lpChar_mk, hasCopyW_mk] at hqQ
    rw [WD.lpSp, WD.lpChar_mk, powZeroW_mk] at hqZ
    obtain ⟨hm, hiso⟩ := eq_of_hasCopy a ha a' ha' k' k hqQ hqZ
    have hp' : (WD.mk a, k) ∈ l' := by
      have : ((WD.mk a', k') : WD h × ℕ) = (WD.mk a, k) := Prod.ext (WD.sound hiso).symm hm
      rw [← this]
      exact hq'

    set p : WD h × ℕ := (WD.mk a, k) with hpdef
    set F : WD h × ℕ → WD h := fun p => p.1.lpChar (WD.lpSp h (p.2 + 1)) with hF
    have e1 : sumList (l.map F) = (F p).lpSum (sumList ((l.erase p).map F)) :=
      sumList_perm ((List.perm_cons_erase hp).map F)
    have e2 : sumList (l'.map F) = (F p).lpSum (sumList ((l'.erase p).map F)) :=
      sumList_perm ((List.perm_cons_erase hp').map F)
    have hc : sumList ((l.erase p).map F) = sumList ((l'.erase p).map F) := by
      refine WD.lpSum_cancel_right E Ω A w h _ _ (F p) ?_
      rw [WD.lpSum_comm, ← e1, WD.lpSum_comm, ← e2]
      exact heq
    have hlen : (l.erase p).length = n := by
      rw [List.length_erase_of_mem hp, hn]
      rfl
    have := ih (l.erase p) (l'.erase p) hlen (fun q hq => hl q (List.mem_of_mem_erase hq))
      (fun q hq => hl' q (List.mem_of_mem_erase hq)) hc
    exact ((List.perm_cons_erase hp).trans (this.cons p)).trans (List.perm_cons_erase hp').symm

end GlobalTheory.WeilDeligne.SpUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RelIndexNeZeroOfReps
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain GlobalTheory.CoefDuty GlobalTheory.ClassPet

noncomputable section

namespace GlobalTheory.FormInner

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem exists_reps (J : Subgroup (GAf L n)) (S : Finset (GAf L n))
    (hS : ∀ g : GAf L n, ∃ s ∈ S, ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ g = (γ : GAf L n) * s * κ) :
    ∃ T, IsClassReps J T := by
  classical
  let q : GAf L n → DoubleCoset.Quotient (GQ L n : Set (GAf L n)) (J : Set (GAf L n)) := DoubleCoset.mk (GQ L n) J
  have hq : ∀ a b, q a = q b ↔ ∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J ∧ b = (γ : GAf L n) * a * κ := fun a b => by
    rw [DoubleCoset.eq]
    exact ⟨fun ⟨h, hh, k, hk, e⟩ => ⟨⟨h, hh⟩, k, hk, e⟩, fun ⟨h, k, hk, e⟩ => ⟨h, h.2, k, hk, e⟩⟩
  refine ⟨S.image fun s => (q s).out, fun g => ?_⟩
  obtain ⟨s, hs, e⟩ := hS g
  have e1 : q s = q g := (hq _ _).2 e
  have ho : ∀ c : DoubleCoset.Quotient (GQ L n : Set (GAf L n)) (J : Set (GAf L n)), q c.out = c := fun c => Quotient.out_eq c
  refine ⟨(q s).out, ⟨Finset.mem_image_of_mem _ hs, (hq _ _).1 ((ho _).trans e1)⟩, ?_⟩
  rintro t ⟨ht, h⟩
  obtain ⟨s', -, rfl⟩ := Finset.mem_image.1 ht
  have := (hq _ _).2 h
  rw [ho] at this
  rw [this, e1]

theorem relIndex_ne_zero_of_reps {J K : Subgroup (GAf L n)} (hJ : IsBounded J) (hle : K ≤ J) {T : Finset (GAf L n)}
    (hT : IsClassReps K T) : K.relIndex J ≠ 0 := by
  classical
  have hfin : ∀ t : GAf L n, {γ : GQ L n | (γ : GAf L n) * t ∈ J}.Finite := by
    intro t
    rcases Set.eq_empty_or_nonempty {γ : GQ L n | (γ : GAf L n) * t ∈ J} with h | ⟨γ₀, h₀⟩
    · rw [h]; exact Set.finite_empty
    · haveI := GlobalTheory.StabFin.finite_conj_mem L n J hJ 1
      refine Set.Finite.subset (Set.finite_range fun δ : {γ : GQ L n // (1 : GAf L n)⁻¹ * (γ : GAf L n) * 1 ∈ J} => δ.1 * γ₀) ?_
      intro γ hγ
      refine ⟨⟨γ * γ₀⁻¹, ?_⟩, by simp⟩
      have := J.mul_mem hγ (J.inv_mem h₀)
      simpa [mul_assoc] using this
  refine relIndex_ne_zero_of_cover (T.biUnion fun t => (hfin t).toFinset.image fun γ : GQ L n => (γ : GAf L n) * t) (fun κ hκ => ?_) hle
  obtain ⟨t, ⟨ht, γ, k, hk, e⟩, -⟩ := hT κ
  refine ⟨γ * t, Finset.mem_biUnion.2 ⟨t, ht, Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).2 ?_)⟩, by rw [e, inv_mul_cancel_left]; exact hk⟩
  have := J.mul_mem hκ (J.inv_mem (hle hk))
  rw [e] at this
  simpa using this

theorem form_inv {a : NG.AlgWt L n} (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) {J : Subgroup (GAf L n)} (hJ : IsBounded J) {χ : J →* ℂˣ}
    {f f' : GAf L n → a.W} (hf : f ∈ NG.TypeSp a.ρ J χ) (hf' : f' ∈ NG.TypeSp a.ρ J χ) :
    ∀ κ ∈ J, ∀ g, β (f (g * κ)) (f' (g * κ)) = β (f g) (f' g) := by
  intro κ hκ g
  have e : ∀ k : J, f (g * k) = ((χ k : ℂˣ) : ℂ) • f g := fun k => congrFun (hf.2 k) g
  have e' : f' (g * κ) = ((χ ⟨κ, hκ⟩ : ℂˣ) : ℂ) • f' g := congrFun (hf'.2 ⟨κ, hκ⟩) g
  rw [e ⟨κ, hκ⟩, e']
  by_cases h0 : f g = 0
  · simp [h0]
  obtain ⟨N, hN, hinv⟩ := hf.1.2
  obtain ⟨F, hF⟩ := (GlobalTheory.CongIndex.finite_index_conj L n J hJ 1 N hN).2.1
  have hle : J ⊓ congSub L n N ≤ J := inf_le_left
  have hne : (J ⊓ congSub L n N).relIndex J ≠ 0 := by
    classical
    have : ∀ f₀ ∈ F, ∃ u, (∃ κ ∈ J, f₀⁻¹ * κ ∈ congSub L n N) → u ∈ J ∧ f₀⁻¹ * u ∈ congSub L n N := fun f₀ _ => by
      by_cases h : ∃ κ ∈ J, f₀⁻¹ * κ ∈ congSub L n N
      · obtain ⟨u, hu⟩ := h
        exact ⟨u, fun _ => hu⟩
      · exact ⟨1, fun h' => absurd h' h⟩
    choose! u hu using this
    refine relIndex_ne_zero_of_cover (F.image u) (fun κ hκ => ?_) hle
    obtain ⟨f₀, h₀, h₁⟩ := hF κ hκ
    obtain ⟨h2, h3⟩ := hu f₀ h₀ ⟨κ, hκ, h₁⟩
    refine ⟨u f₀, Finset.mem_image_of_mem _ h₀, J.mul_mem (J.inv_mem h2) hκ, ?_⟩
    have := (congSub L n N).mul_mem ((congSub L n N).inv_mem h3) h₁
    simpa [mul_assoc] using this
  have hn := norm_eq_one_of_relIndex hle hne χ (fun k hk => by
    have h1 := e ⟨k, hle hk⟩
    rw [hinv k hk.2 g] at h1
    have h2 : (((χ ⟨k, hle hk⟩ : ℂˣ) : ℂ) - 1) • f g = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact Units.ext (sub_eq_zero.1 ((smul_eq_zero.1 h2).resolve_right h0))) ⟨κ, hκ⟩
  rw [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, Complex.conj_mul', hn]
  simp

theorem classSum_index {a : NG.AlgWt L n} {β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ} (hβ : IsInvForm a β) {J K : Subgroup (GAf L n)}
    {T T' : Finset (GAf L n)} (hJ : IsBounded J) (hle : K ≤ J) (hne : K.relIndex J ≠ 0) (hT : IsClassReps J T)
    (hT' : IsClassReps K T') {χ : J →* ℂˣ} {f f' : GAf L n → a.W} (hf : f ∈ NG.TypeSp a.ρ J χ) (hf' : f' ∈ NG.TypeSp a.ρ J χ) :
    classSum a β K T' f f' = (K.relIndex J : ℂ) * classSum a β J T f f' := by
  obtain ⟨F, h1, h2, h3⟩ := exists_cosetReps hle hne
  have hi := form_inv β hJ hf hf'
  rw [GlobalTheory.ClassRefine.classSum_smaller_level L n a β hβ J K T T' hJ hle hne hT hT' f hf.1 f' hf'.1
    (fun κ hκ => hi κ (hle hκ)) F h1 h2, classSum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_congr rfl fun u hu => hi u (h1 u hu) t, Finset.sum_const, h3, nsmul_eq_mul]
  ring

theorem classSum_compare {a : NG.AlgWt L n} {β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ} (hβ : IsInvForm a β) {J J' : Subgroup (GAf L n)}
    (hJ : IsBounded J) {N : ℕ} (hN : 0 < N) (hNJ : ∀ κ, NG.Cong L n N κ → κ ∈ J) (hJ' : IsBounded J') {T' : Finset (GAf L n)}
    (hT' : IsClassReps J' T') : ∃ (T : Finset (GAf L n)) (c : ℝ), IsClassReps J T ∧ 0 < c ∧
      ∀ (χ : J →* ℂˣ) (χ' : J' →* ℂˣ) (f f' : GAf L n → a.W), f ∈ NG.TypeSp a.ρ J χ → f' ∈ NG.TypeSp a.ρ J χ →
        f ∈ NG.TypeSp a.ρ J' χ' → f' ∈ NG.TypeSp a.ρ J' χ' → classSum a β J' T' f f' = (c : ℂ) * classSum a β J T f f' := by
  classical
  obtain ⟨F, hF⟩ := (GlobalTheory.CongIndex.finite_index_conj L n J' hJ' 1 N hN).2.1
  have hne' : (J ⊓ J').relIndex J' ≠ 0 := by
    have : ∀ f₀ ∈ F, ∃ u, (∃ κ ∈ J', f₀⁻¹ * κ ∈ J) → u ∈ J' ∧ f₀⁻¹ * u ∈ J := fun f₀ _ => by
      by_cases h : ∃ κ ∈ J', f₀⁻¹ * κ ∈ J
      · obtain ⟨u, hu⟩ := h
        exact ⟨u, fun _ => hu⟩
      · exact ⟨1, fun h' => absurd h' h⟩
    choose! u hu using this
    refine relIndex_ne_zero_of_cover (F.image u) (fun κ hκ => ?_) inf_le_right
    obtain ⟨f₀, h₀, h₁⟩ := hF κ hκ
    obtain ⟨h2, h3⟩ := hu f₀ h₀ ⟨κ, hκ, hNJ _ h₁⟩
    refine ⟨u f₀, Finset.mem_image_of_mem _ h₀, ?_, J'.mul_mem (J'.inv_mem h2) hκ⟩
    have := J.mul_mem (J.inv_mem h3) (hNJ _ h₁)
    simpa [mul_assoc] using this
  obtain ⟨U, hU1, hU2, -⟩ := exists_cosetReps (inf_le_right : J ⊓ J' ≤ J') hne'
  obtain ⟨T₀, hT₀⟩ := exists_reps (J ⊓ J') ((T' ×ˢ U).image fun p => p.1 * p.2) fun g => by
    obtain ⟨t, ⟨ht, γ, κ, hκ, e⟩, -⟩ := hT' g
    obtain ⟨u, ⟨hu, hu'⟩, -⟩ := hU2 κ hκ
    exact ⟨t * u, Finset.mem_image.2 ⟨(t, u), Finset.mem_product.2 ⟨ht, hu⟩, rfl⟩, γ, u⁻¹ * κ, hu', by rw [e]; group⟩
  have hne : (J ⊓ J').relIndex J ≠ 0 := relIndex_ne_zero_of_reps hJ inf_le_left hT₀
  obtain ⟨T, hT⟩ := exists_reps J T₀ fun g => by
    obtain ⟨t, ⟨ht, γ, κ, hκ, e⟩, -⟩ := hT₀ g
    exact ⟨t, ht, γ, κ, hκ.1, e⟩
  refine ⟨T, ((J ⊓ J').relIndex J : ℝ) / ((J ⊓ J').relIndex J' : ℝ), hT,
    div_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hne)) (Nat.cast_pos.2 (Nat.pos_of_ne_zero hne')), ?_⟩
  intro χ χ' f f' h1 h2 h3 h4
  have e1 := classSum_index hβ hJ inf_le_left hne hT hT₀ h1 h2
  have e2 := classSum_index hβ hJ' inf_le_right hne' hT' hT₀ h3 h4
  have hc : (((J ⊓ J').relIndex J' : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne'
  push_cast
  rw [div_mul_eq_mul_div, ← e1, e2, mul_div_cancel_left₀ _ hc]

theorem classSum_transport {G Γ W I : Type} [Group G] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [Fintype I]
    (ι : Γ →* G) (hι : Function.Injective ι) (φ : GAf L n ≃* G) (hrat : ∀ h, h ∈ GQ L n ↔ ∃ γ, ι γ = φ h)
    (J : Subgroup G) (y : I → G) (hy : Formalism.IndefR.Bridge.IsReps ι J y) :
    ∃ T, IsClassReps (J.comap φ.toMonoidHom) T ∧ ∀ (a : NG.AlgWt L n) (β : a.W →ₗ⋆[ℂ] a.W →ₗ[ℂ] ℂ) (f f' : GAf L n → a.W)
      (F F' : G → W), (∀ g, β (f g) (f' g) = inner ℂ (F (φ g)) (F' (φ g))) →
      classSum a β (J.comap φ.toMonoidHom) T f f' = Formalism.IndefR.Bridge.adInner ι J y F F' := by
  classical
  have hinj : Function.Injective fun i => φ.symm (y i) := fun i j e => by
    have e' : y i = y j := φ.symm.injective e
    exact (hy (y i)).unique ⟨1, 1, by simp⟩ ⟨1, 1, by simp [e']⟩
  have key : ∀ g i, (∃ (γ : GQ L n) (κ : GAf L n), κ ∈ J.comap φ.toMonoidHom ∧ g = (γ : GAf L n) * φ.symm (y i) * κ) ↔
      ∃ (γ : Γ) (k : J), φ g = ι γ * y i * k := fun g i => by
    constructor
    · rintro ⟨γ, κ, hκ, rfl⟩
      obtain ⟨δ, hδ⟩ := (hrat _).1 γ.2
      exact ⟨δ, ⟨φ κ, hκ⟩, by simp [hδ]⟩
    · rintro ⟨γ, k, e⟩
      refine ⟨⟨φ.symm (ι γ), (hrat _).2 ⟨γ, by simp⟩⟩, φ.symm k, by simp, φ.injective (by simp [e])⟩
  refine ⟨Finset.univ.image fun i => φ.symm (y i), fun g => ?_, fun a β f f' F F' h => ?_⟩
  · obtain ⟨i, hi, hu⟩ := hy (φ g)
    refine ⟨φ.symm (y i), ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), (key g i).2 hi⟩, ?_⟩
    rintro t ⟨ht, h⟩
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 ht
    rw [hu j ((key g j).1 h)]
  · rw [classSum, Finset.sum_image fun i _ j _ e => hinj e, Formalism.IndefR.Bridge.adInner]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h, MulEquiv.apply_symm_apply]
    congr 3
    symm
    refine Nat.card_congr (Equiv.ofBijective (fun δ : Formalism.IndefR.Bridge.stab ι J (y i) =>
      (⟨⟨φ.symm (ι δ), (hrat _).2 ⟨δ, by simp⟩⟩, by simpa using (Formalism.IndefR.Bridge.mem_stab ι).1 δ.2⟩ :
        {γ : GQ L n // (φ.symm (y i))⁻¹ * (γ : GAf L n) * φ.symm (y i) ∈ J.comap φ.toMonoidHom})) ⟨fun δ δ' e => ?_, fun γ => ?_⟩)
    · exact Subtype.ext (hι (φ.symm.injective (congrArg (fun z => (z.1 : GAf L n)) e)))
    · obtain ⟨δ, hδ⟩ := (hrat _).1 γ.1.2
      refine ⟨⟨δ, (Formalism.IndefR.Bridge.mem_stab ι).2 ?_⟩, Subtype.ext (Subtype.ext (by simp [hδ]))⟩
      simpa [hδ] using γ.2

end GlobalTheory.FormInner

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchrodingerImagesOrthogonalDisjointSplitSupportStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schrodingerImages_orthogonal_disjoint_splitSupport : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (Pf : Finset (Pl D.host.E)) (ea e : AE D) (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → IsIdemSum ea Pf → IsSplitIdem D e → e * ea = e → IsThetaFunO ψ S T f₀ → IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Tm → IsCovolOne (ratL T S) μ 𝓕 → ∀ Φ₁ Φ₂ : WO S T → ℂ, IsSBHalf (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ₁ → IsSBHalf (cA D ea) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ₂ → (∀ x x' : WO S T, (∀ a b, (e + cA D e) * x a b = (e + cA D e) * x' a b) → Φ₁ x ≠ 0 → Φ₂ x' ≠ 0 → False) → ∀ Ω : Module.End ℂ (WO S T → ℂ), (∀ g, IsThetaFunO ψ S T g → IsThetaFunO ψ S T (Ω g)) → (∀ y : WO S T, IsHalf e y → ∀ g, IsThetaFunO ψ S T g → Ω (heisO ψ S T y g) = heisO ψ S T y (Ω g)) → thetaIP μ 𝓕 (Tm Φ₁) (Ω (Tm Φ₂)) = 0 := by
  first | exact @GlobalTheory.BadOrth.orth_of_disjoint | exact GlobalTheory.BadOrth.orth_of_disjoint | (intros; apply GlobalTheory.BadOrth.orth_of_disjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelfDualLatticeIndexEqLocalUnitaryIndexAtInertStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLatticeIndex_eq_localUnitaryIndex_at_inert : ∀ (D : D7) (W : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (ε : AF D.host.F), IsPlaceIdem D v ε → ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (σ : GlobalTheory.InertLoc.LP D P →+* GlobalTheory.InertLoc.LP D P) (π : AE D →+* GlobalTheory.InertLoc.LP D P) (β : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) (ι : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) →* GA D W), GlobalTheory.InertLoc.Chart (algebraMap (AF D.host.F) (AE D) ε) σ π → GlobalTheory.InertLoc.Frame W (algebraMap (AF D.host.F) (AE D) ε) σ π β → GlobalTheory.InertLoc.GrpChart W (algebraMap (AF D.host.F) (AE D) ε) σ π β ι → ∀ (g : Formalism.UG.UJ σ (1 : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P))), latIndex W (ι g) = ((Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).map (((g : GL (Fin W.rank) (GlobalTheory.InertLoc.LP D P)) : Matrix (Fin W.rank) (Fin W.rank) (GlobalTheory.InertLoc.LP D P)).mulVecLin.restrictScalars (P.adicCompletionIntegers D.host.E))).toAddSubgroup.relIndex (Submodule.span (P.adicCompletionIntegers D.host.E) (Set.range (Pi.basisFun (GlobalTheory.InertLoc.LP D P) (Fin W.rank)))).toAddSubgroup := by
  first | exact @GlobalTheory.InertLatIndex.latIndex_chart_eq | exact GlobalTheory.InertLatIndex.latIndex_chart_eq | (intros; apply GlobalTheory.InertLatIndex.latIndex_chart_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SiegelWeilTsumEnormRationalInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelWeil_tsum_enorm_rational_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (νV : Measure (GA D V)) (𝓗 : Set (GA D V)) (νW : Measure (GA D W)) (𝓖 : Set (GA D W)) (μ : Measure (WO V W)) (𝓕 : Set (WO V W)) (fr : Lag W → Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E), SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 fr → ∀ (F₁ F₂ : WO V W → ℂ), IsThetaFunO ψ V W F₁ → IsThetaFunO ψ V W F₂ → ∀ γ₁ ∈ GQ W, ∀ γ₂ ∈ GQ W, ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) (om (1, γ₁) F₁) (om (1, γ₂) F₂)‖ₑ = ∑' Y : Lag W, ‖lagTerm μ 𝓕 (fr Y) F₁ F₂‖ₑ := by
  first | exact @GlobalTheory.SWAbsInv.tsum_enorm_lagTerm_rat | exact GlobalTheory.SWAbsInv.tsum_enorm_lagTerm_rat | (intros; apply GlobalTheory.SWAbsInv.tsum_enorm_lagTerm_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceChartFiniteAdeleTensorLevelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries
open Formalism.L2.NTheta (IsIdemAt IsHeckeElt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlaceChart_finiteAdeleTensor_levels : ∀ (D : D7) (e : AE D) (P : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), IsIdemAt e P → GlobalTheory.SplitHecke.Chart e v π → ∃ φ : Datum.EAf D →+* Fv D.host.F v, (∀ a, φ (toEAf D a) = π a) ∧ (∀ N : Datum.EAf D, toEAf D e * N ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ GlobalTheory.SplitHecke.IsInt (GlobalTheory.SplitHecke.Ov D v) (φ N)) ∧ (∀ (m n : ℕ) (N : Matrix (Fin m) (Fin n) (Datum.EAf D)), IsIntM N → ∀ z : Matrix (Fin m) (Fin n) (GlobalTheory.SplitHecke.Ov D v), z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) = N.map φ → prim (redM P N) = prim (z.map (IsLocalRing.residue (GlobalTheory.SplitHecke.Ov D v)))) ∧ ∀ (V : HSp D) (β : GL (Fin V.rank) (Datum.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Lev.IsBaseFrame V β Λ 1 → GlobalTheory.SplitHecke.Frame V e π (Matrix.GeneralLinearGroup.map φ β) := by
  first | exact @GlobalTheory.ChartLevels.chart_levels | exact GlobalTheory.ChartLevels.chart_levels | (intros; apply GlobalTheory.ChartLevels.chart_levels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
section
open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.LamTie

namespace GlobalTheory.LamTie

theorem sum_th_empty_ne_zero : ∀ (D : D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (Z : LamDat D), Z.Ok → IsLamTie0 X Z → ∀ i, X.NonzeroIndexPlace i → ∀ lam : X.abelian₂ i, (∑ δ, X.th i ∅ lam δ) ≠ 0 ∧ ∃ s : ℤ, BlochKatoReduction.Gen.SOk X i lam s := by
  intro D N X Z hZ hT i hi lam
  obtain ⟨ι, j, a, s, hs, u, T, hu, hTs, hEq⟩ := hT i hi lam
  refine ⟨?_, s, hs⟩
  have h1 : 1 ≤ s := by
    have := hs.2.1
    exact_mod_cast this
  have h2 : (s : ℤ) ≤ (BlochKatoReduction.Gen.NFun D.R : ℤ) + 1 := hs.2.2
  obtain ⟨Λ, -, hne, hiff⟩ := GlobalTheory.T.exists_heckeL_eq_toricSum_ne_zero D.R D.host _ (phi D.host) s (Z.kap j a s) (cond0 D.host Z.w0)
    (Z.lam0 (X.l i) j a) (GlobalTheory.T.isHostDatum_kap_lam0_of_ok D Z hZ (X.l i) j a s h1 h2)
  have hT0 : T ≠ 0 := by rw [(hiff T).1 hTs]; exact hne
  intro h0
  rw [h0, map_zero] at hEq
  exact mul_ne_zero hu ((map_ne_zero ι).2 hT0) hEq.symm

end GlobalTheory.LamTie
end

