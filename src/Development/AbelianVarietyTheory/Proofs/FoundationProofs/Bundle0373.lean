import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import CompanionTheory.EightfoldTheory.VariationTheory.PublishedTheorems.ImportsAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0189
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.NormNatCastLtOne
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0027
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0019
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FontaineFormalismOfRegular

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CocyclePairAlternatingNeOnCycloKernel
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.PairSpan

section Abstract

variable {Γ k : Type} [Group Γ] [Field k]

theorem alt_left_nondeg {v : Fin 2 → k} (hv : v ≠ 0) : ∃ a : Fin 2 → k, v 0 * a 1 - v 1 * a 0 ≠ 0 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := by
      intro h1; apply hv; funext i; fin_cases i <;> simp [h0, h1]
    exact ⟨![1, 0], by simp [h1]⟩
  · exact ⟨![0, 1], by simp [h0]⟩

theorem stable_cases {W : Γ →* GL (Fin 2) k} {H : Subgroup Γ} (hirr : UpperTheory.V.Af.IsIrr (W.comp H.subtype))
    (U : Submodule k (Fin 2 → k)) (hU : ∀ s ∈ H, ∀ v ∈ U, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ v ∈ U) :
    U = ⊥ ∨ U = ⊤ :=
  hirr.2.2 U le_top (by intro g v hv; exact hU g g.2 v hv)

theorem coc_conj {n : ℕ} (ρ : Γ →* GL (Fin n) k) (y : Γ → Fin n → k)
    (hy : ∀ g h, y (g * h) = y g + (ρ g : Matrix (Fin n) (Fin n) k) *ᵥ y h) (s g : Γ) (hg : ρ g = 1) :
    y (s * g * s⁻¹) = (ρ s : Matrix (Fin n) (Fin n) k) *ᵥ y g := by
  have h1 : y 1 = 0 := by simpa using hy 1 1
  have h2 : y s + (ρ s : Matrix (Fin n) (Fin n) k) *ᵥ y s⁻¹ = 0 := by rw [← hy, mul_inv_cancel, h1]
  rw [hy, hy, map_mul, hg, mul_one, add_right_comm, h2, zero_add]

end Abstract
end GlobalTheory.Ord2.PairSpan

namespace GlobalTheory.Ord2.PairSpan

variable {Γ k : Type} [Group Γ] [Field k]

theorem exists_pair_ne [IsAlgClosed k] [CharZero k] {W : Γ →* GL (Fin 2) k} {H : Subgroup Γ}
    (hirr : UpperTheory.V.Af.IsIrr (W.comp H.subtype)) {N : Set Γ}
    (hN : ∀ s ∈ H, ∀ g ∈ N, s * g * s⁻¹ ∈ N) {y z : Γ → Fin 2 → k}
    (hy : ∀ s ∈ H, ∀ g ∈ N, y (s * g * s⁻¹) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ y g)
    (hz : ∀ s ∈ H, ∀ g ∈ N, z (s * g * s⁻¹) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ z g)
    (hy0 : ∃ g ∈ N, y g ≠ 0) (hz0 : ∃ g ∈ N, z g ≠ 0) :
    ∃ g ∈ N, ∃ h ∈ N, y h 0 * z g 1 - y h 1 * z g 0 ≠ y g 0 * z h 1 - y g 1 * z h 0 := by
  by_contra hcon
  push_neg at hcon
  let Sig : Submodule k ((Fin 2 → k) × (Fin 2 → k)) := Submodule.span k ((fun g => (y g, z g)) '' N)
  have hgen : ∀ g ∈ N, (y g, z g) ∈ Sig := fun g hg => Submodule.subset_span ⟨g, hg, rfl⟩
  have hinv : ∀ s ∈ H, ∀ σ ∈ Sig,
      ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.1, (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ σ.2) ∈ Sig := by
    intro s hs σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      rw [← hy s hs g hg, ← hz s hs g hg]
      exact hgen _ (hN s hs g hg)
    | zero =>
      simp only [Prod.fst_zero, Prod.snd_zero, Matrix.mulVec_zero, Prod.mk_zero_zero]
      exact Sig.zero_mem
    | add x x' _ _ ihx ihx' => simpa [Matrix.mulVec_add] using Sig.add_mem ihx ihx'
    | smul a x _ ihx => simpa [Matrix.mulVec_smul] using Sig.smul_mem a ihx
  have hB : ∀ g ∈ N, ∀ σ ∈ Sig, y g 0 * σ.2 1 - y g 1 * σ.2 0 = σ.1 0 * z g 1 - σ.1 1 * z g 0 := by
    intro g hg σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact (hcon g hg h hh).symm
    | zero => simp
    | add x x' _ _ ihx ihx' =>
      simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
      linear_combination ihx + ihx'
    | smul a x _ ihx =>
      simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul]
      linear_combination a * ihx
  let K' : Submodule k (Fin 2 → k) := Sig.comap (LinearMap.inr k (Fin 2 → k) (Fin 2 → k))
  have hK' : K' = ⊥ := by
    rcases stable_cases hirr K' (by
      intro s hs v hv
      have := hinv s hs _ hv
      simpa [K', Matrix.mulVec_zero] using this) with h | h
    · exact h
    · exfalso
      obtain ⟨g, hg, hyg⟩ := hy0
      obtain ⟨a, ha⟩ := alt_left_nondeg hyg
      have hmem : ((0 : Fin 2 → k), a) ∈ Sig := by
        have : a ∈ K' := h ▸ Submodule.mem_top
        simpa [K'] using this
      exact ha ((hB g hg _ hmem).trans (by simp))
  let P : Submodule k (Fin 2 → k) := Sig.map (LinearMap.fst k (Fin 2 → k) (Fin 2 → k))
  have hP : P = ⊤ := by
    rcases stable_cases hirr P (by
      rintro s hs v ⟨σ, hσ, rfl⟩
      exact ⟨_, hinv s hs σ hσ, rfl⟩) with h | h
    · exfalso
      obtain ⟨g, hg, hyg⟩ := hy0
      have : y g ∈ P := ⟨_, hgen g hg, rfl⟩
      rw [h, Submodule.mem_bot] at this
      exact hyg this
    · exact h
  let f : Sig →ₗ[k] (Fin 2 → k) := (LinearMap.fst k (Fin 2 → k) (Fin 2 → k)).comp Sig.subtype
  have hfi : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun σ hσ => ?_
    have h1 : (σ : (Fin 2 → k) × (Fin 2 → k)).1 = 0 := hσ
    have h2 : (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ K' := by
      show LinearMap.inr k _ _ (σ : (Fin 2 → k) × (Fin 2 → k)).2 ∈ Sig
      have : LinearMap.inr k (Fin 2 → k) (Fin 2 → k) (σ : (Fin 2 → k) × (Fin 2 → k)).2 = σ := by
        ext1 <;> simp [h1]
      rw [this]; exact σ.2
    rw [hK', Submodule.mem_bot] at h2
    exact Subtype.ext (Prod.ext h1 h2)
  have hfs : Function.Surjective f := by
    intro a
    have : a ∈ P := hP ▸ Submodule.mem_top
    obtain ⟨σ, hσ, rfl⟩ := this
    exact ⟨⟨σ, hσ⟩, rfl⟩
  let e := LinearEquiv.ofBijective f ⟨hfi, hfs⟩
  let φ : Module.End k (Fin 2 → k) :=
    (LinearMap.snd k (Fin 2 → k) (Fin 2 → k)).comp (Sig.subtype.comp e.symm.toLinearMap)
  have hφmem : ∀ a, (a, φ a) ∈ Sig := by
    intro a
    have h1 : ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k)).1 = a := e.apply_symm_apply a
    have : (a, φ a) = ((e.symm a : Sig) : (Fin 2 → k) × (Fin 2 → k)) := Prod.ext h1.symm rfl
    rw [this]; exact (e.symm a).2
  have hφ : ∀ σ ∈ Sig, φ σ.1 = σ.2 := by
    intro σ hσ
    have : e.symm σ.1 = ⟨σ, hσ⟩ := e.symm_apply_eq.2 rfl
    show ((e.symm σ.1 : Sig) : (Fin 2 → k) × (Fin 2 → k)).2 = σ.2
    rw [this]
  have hφW : ∀ s ∈ H, ∀ a, φ ((W s : Matrix (Fin 2) (Fin 2) k) *ᵥ a) = (W s : Matrix (Fin 2) (Fin 2) k) *ᵥ φ a :=
    fun s hs a => hφ _ (hinv s hs _ (hφmem a))
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue φ
  have hE : Module.End.eigenspace φ c = ⊤ := by
    rcases stable_cases hirr (Module.End.eigenspace φ c) (by
      intro s hs v hv
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      rw [hφW s hs, hv, Matrix.mulVec_smul]) with h | h
    · exact absurd h (Module.End.hasEigenvalue_iff.1 hc)
    · exact h
  have hφc : ∀ a, φ a = c • a := fun a => Module.End.mem_eigenspace_iff.1 (hE ▸ Submodule.mem_top)
  have hzy : ∀ g ∈ N, z g = c • y g := fun g hg => by rw [← hφc]; exact (hφ _ (hgen g hg)).symm
  obtain ⟨g1, hg1, hzg1⟩ := hz0
  have hc0 : c ≠ 0 := by rintro rfl; apply hzg1; rw [hzy g1 hg1, zero_smul]
  obtain ⟨g0, hg0, hyg0⟩ := hy0
  have horth : ∀ h ∈ N, y g0 0 * y h 1 - y g0 1 * y h 0 = 0 := by
    intro h hh
    have := hcon h hh g0 hg0
    rw [hzy h hh, hzy g0 hg0] at this
    simp only [Pi.smul_apply, smul_eq_mul] at this
    have h2 : (2 * c) * (y g0 0 * y h 1 - y g0 1 * y h 0) = 0 := by linear_combination this
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exfalso; exact hc0 (by simpa using h3)
    · exact h3
  have hall : ∀ σ ∈ Sig, y g0 0 * σ.1 1 - y g0 1 * σ.1 0 = 0 := by
    intro σ hσ
    induction hσ using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, hh, rfl⟩ := hx
      exact horth h hh
    | zero => simp
    | add x x' _ _ ihx ihx' =>
      simp only [Prod.fst_add, Pi.add_apply]
      linear_combination ihx + ihx'
    | smul a x _ ihx =>
      simp only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul]
      linear_combination a * ihx
  obtain ⟨a, ha⟩ := alt_left_nondeg hyg0
  exact ha (hall _ (hφmem a))

end GlobalTheory.Ord2.PairSpan

namespace GlobalTheory.Ord2

open PairSpan in

theorem exists_om_ne_swap_on_N0g : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (e : ℕ)
    (S : Finset Pl) (A : ValuationSubring Ω) (W : R2 Ω l), Nf e S A W → ∀ y ∈ Z1 (Loc.colRep W),
    ∀ z ∈ Z1 (Loc.colRep (dual1 W)), (∃ g ∈ N0g W, y g ≠ 0) → (∃ g ∈ N0g W, z g ≠ 0) →
    ∃ g ∈ N0g W, ∃ h ∈ N0g W, om (y h) (z g) ≠ om (y g) (z h) := by
  intro l _ Ω _ _ _ e S A W hW y hyZ z hzZ hy0 hz0
  have hy' : ∀ g h, y (g * h) = y g + (W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ y h := fun g h => by
    rw [hyZ.2 g h]; rfl
  have hz' : ∀ g h, z (g * h) = z g + (dual1 W g : Matrix (Fin 2) (Fin 2) (Qbar l)) *ᵥ z h := fun g h => by
    rw [hzZ.2 g h]; rfl
  have hnorm : (N0g W).Normal := by unfold N0g; infer_instance
  have hdual : ∀ s, cycBar ℚ Ω l s = 1 → dt W s = 1 → dual1 W s = W s := by
    intro s h1 h2
    apply Units.ext
    rw [dual1, tw_val]
    simp [h1, h2]
  have hN1 : ∀ g ∈ N0g W, W g = 1 := fun g hg => (Subgroup.mem_inf.1 hg).2
  have hNd : ∀ g ∈ N0g W, dual1 W g = 1 := by
    intro g hg
    have h1 : cycBar ℚ Ω l g = 1 := (Subgroup.mem_inf.1 hg).1
    have h2 : dt W g = 1 := by
      show Matrix.GeneralLinearGroup.det (W g) = 1
      rw [hN1 g hg, map_one]
    rw [hdual g h1 h2, hN1 g hg]
  have hH : ∀ s ∈ H0g W, dual1 W s = W s := fun s hs =>
    hdual s (Subgroup.mem_inf.1 hs).1 (Subgroup.mem_inf.1 hs).2
  obtain ⟨g, hg, h, hh, hne⟩ := exists_pair_ne (k := Qbar l) (W := W) (H := H0g W) (N := (N0g W : Set (G ℚ Ω)))
    hW.irr (fun s _ g hg => hnorm.conj_mem g hg s)
    (y := y) (z := z)
    (fun s _ g hg => coc_conj W y hy' s g (hN1 g hg))
    (fun s hs g hg => by rw [coc_conj (dual1 W) z hz' s g (hNd g hg), hH s hs])
    hy0 hz0
  exact ⟨g, hg, h, hh, hne⟩

end GlobalTheory.Ord2

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousOfIsOpenStab
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V
open scoped Matrix TensorProduct

namespace GlobalTheory.SlTwoCusp

open Topology

theorem continuous_pInf' (F : Type) [Field F] [NumberField F] [IsTotallyReal F] : Continuous (TR.pInf F) := by
  have hc : Continuous (TR.infEq F).symm :=
    continuous_pi fun w =>
      (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp (continuous_apply w)
  exact hc.comp continuous_fst

theorem continuous_of_isOpen_stab : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) (φ : TR.Sm F a),
    IsOpen {k | TR.finRep F a k φ = φ} → Continuous φ.1 := by
  intro F _ _ _ a φ hφ
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hm : Continuous fun x : GA F a => g⁻¹ * x := continuous_const.mul continuous_id
  have hI : Continuous (Matrix.GeneralLinearGroup.map (TR.pInf F) : GA F a → GL (Fin a) (TR.Rinf F)) :=
    Continuous.units_map _ (continuous_id.matrix_map (continuous_pInf' F))
  have hFn : Continuous (Matrix.GeneralLinearGroup.map (pFin F) : GA F a → GL (Fin a) (Af F)) :=
    Continuous.units_map _ (continuous_id.matrix_map continuous_snd)
  have h1 : Continuous fun x : GA F a => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val :=
    (Units.continuous_val (M := Matrix (Fin a) (Fin a) (TR.Rinf F))).comp (hI.comp hm)
  have h2 : ContinuousAt (fun x : GA F a => TR.chart φ.1 g (TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)) g :=
    ContinuousAt.comp (f := fun x : GA F a => TR.toL (Matrix.GeneralLinearGroup.map (TR.pInf F) (g⁻¹ * x)).val)
      (TR.contDiffAt_chart φ.2 g (TR.val_mem_invSet _)).continuousAt h1.continuousAt
  refine h2.congr ?_
  have h3 : {x : GA F a | TR.finRep F a (Matrix.GeneralLinearGroup.map (pFin F) (g⁻¹ * x)) φ = φ} ∈ 𝓝 g :=
    (hφ.preimage (hFn.comp hm)).mem_nhds (by simp)
  filter_upwards [h3] with x hx
  rw [TR.chart_val]
  conv_lhs => rw [← hx]
  change φ.1 (g * TR.infGL F a _ * finGL F a _) = _
  rw [mul_assoc, TR.infGL_mul_finGL, mul_inv_cancel_left]

open MeasureTheory Topology

end GlobalTheory.SlTwoCusp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineClassRestrictDecompositionGroup
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

namespace GlobalTheory.Ord2

private theorem locEmb_conj {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    {A B : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 k)} (hA : IsPlaceOver A v) (hB : IsPlaceOver B v) :
    ∃ g : G k Ω, (∀ τ ∈ Ine (F := k) B, g⁻¹ * τ * g ∈ Ine (F := k) A) ∧
      (∀ τ ∈ Dec (F := k) B, g⁻¹ * τ * g ∈ Dec (F := k) A) ∧
      ∀ τ ∈ Dec (F := k) A, g * τ * g⁻¹ ∈ Dec (F := k) B := by
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (F := k) hA hB
  have h : IsLift (RingEquiv.refl k) g.toRingEquiv := fun x => g.commutes x
  have hm : ∀ x, g.toRingEquiv x ∈ B ↔ x ∈ A := fun x => by
    show g • x ∈ B ↔ _
    rw [← hg]
    exact ValuationSubring.smul_mem_pointwise_smul_iff
  have hm' : ∀ x, g.toRingEquiv.symm x ∈ A ↔ x ∈ B := fun x => by
    rw [← hm, RingEquiv.apply_symm_apply]
  exact ⟨g, fun τ hτ => conjGal_mem_Ine h hm hτ, fun τ hτ => conjGal_mem_Dec h hm hτ,
    fun τ hτ => conjGal_mem_Dec h.symm hm' hτ⟩

theorem bk_locEmb : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (W : R2 Ω l) (A : ValuationSubring Ω), OverL l A → ∀ z ∈ Z1 (Loc.colRep W), IsBK l (Loc.colRep W) z → ∃ ι : GQ l →* G ℚ Ω, Continuous ι ∧ (∀ σ, ι σ ∈ Dec (F := ℚ) A) ∧ (∀ s ∈ Dec (F := ℚ) A, ∃ σ, ι σ = s) ∧ (∀ σ ∈ Loc.Iq l, ι σ ∈ Ine (F := ℚ) A) ∧ (∀ σ, cycZ ℚ Ω l (ι σ) = Loc.cyc l l σ) ∧ (fun σ => z (ι σ)) ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
  intro l _ Ω _ iA _ W A hA z hz hb
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  obtain rfl : iA = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  obtain ⟨v, hAv, hv⟩ := hA
  obtain ⟨j, -, -, x, hx⟩ := hb.above (algebraMap ℚ (Om l))
  obtain ⟨i1, i2, -, i4, i5, i6, -⟩ := Loc.iotaFacts j
  have h0 : (fun σ => z (Loc.iota j σ)) ∈
      Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp (Loc.iota j)) :=
    ⟨⟨hz.1.comp i1.continuous, fun g h => (congrArg z (map_mul _ g h)).trans (hz.2 _ _)⟩, x,
      fun σ => hx ⟨(Loc.iota j σ, σ), fun y => (Loc.iota_spec j σ y).symm⟩⟩
  obtain ⟨g, g1, g2, g3⟩ := locEmb_conj hAv ((i6 v).2 hv)
  let ι : GQ l →* G ℚ Ω := (MulAut.conj g⁻¹).toMonoidHom.comp (Loc.iota j)
  have hι : ∀ σ, ι σ = g⁻¹ * Loc.iota j σ * g := fun σ => by simp [ι]
  have hc : Continuous ι := by
    have : (ι : GQ l → G ℚ Ω) = fun σ => g⁻¹ * Loc.iota j σ * g := funext hι
    rw [this]
    exact (continuous_const.mul i1.continuous).mul continuous_const
  refine ⟨ι, hc, fun σ => ?_, fun s hs => ?_, fun σ hσ => ?_, fun σ => ?_, ?_⟩
  · rw [hι]
    exact g2 _ (by rw [← i2]; exact ⟨σ, rfl⟩)
  · have h1 : g * s * g⁻¹ ∈ Dec (F := ℚ) (Loc.placeJ j) := g3 s hs
    rw [← i2] at h1
    obtain ⟨σ, hσ⟩ := h1
    exact ⟨σ, by rw [hι, hσ]; group⟩
  · rw [hι]
    exact g1 _ (by rw [← i4]; exact ⟨σ, hσ, rfl⟩)
  · rw [hι, map_mul, map_mul, map_inv, mul_comm _ (cycZ ℚ Ω l (Loc.iota j σ)), inv_mul_cancel_right]
    exact DFunLike.congr_fun (i5 l) σ
  · have h1 := Loc.z1fCoef (MonoidHom.id (GQ l)) ((Loc.colRep W).comp (Loc.iota j)) ((Loc.colRep W).comp ι)
      ((Loc.colRep W g⁻¹).restrictScalars ℚ_[l]) (LinearMap.continuous_on_pi (Loc.colRep W g⁻¹))
      (fun σ y => by
        show Loc.colRep W g⁻¹ (Loc.colRep W (Loc.iota j σ) y) = Loc.colRep W (ι σ) (Loc.colRep W g⁻¹ y)
        rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hι, mul_inv_cancel_right]) _ h0
    have hcob : ∀ σ, Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹ = z (ι σ * g⁻¹) - z (ι σ) - z g⁻¹ := fun σ => by
      rw [hz.2]; abel
    have h2 : (fun σ => Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹) ∈
        Loc.finiteCocycles (MonoidHom.id (GQ l)) ((Loc.colRep W).comp ι) := by
      refine ⟨⟨?_, fun a b => ?_⟩, z g⁻¹ ⊗ₜ 1, fun σ => ?_⟩
      · rw [funext hcob]
        exact ((hz.1.comp (hc.mul continuous_const)).sub (hz.1.comp hc)).sub continuous_const
      · show Loc.colRep W (ι (a * b)) (z g⁻¹) - z g⁻¹ = Loc.colRep W (ι a) (z g⁻¹) - z g⁻¹ +
          Loc.colRep W (ι a) (Loc.colRep W (ι b) (z g⁻¹) - z g⁻¹)
        rw [map_mul, map_mul, Module.End.mul_apply, map_sub]; abel
      · simp [Loc.actC, TensorProduct.sub_tmul]
    have h3 := Submodule.sub_mem _ h1 h2
    convert h3 using 1
    funext σ
    show z (ι σ) = Loc.colRep W g⁻¹ (z (Loc.iota j σ)) - (Loc.colRep W (ι σ) (z g⁻¹) - z g⁻¹)
    have e1 := hz.2 g⁻¹ (Loc.iota j σ)
    rw [hcob, hι, mul_inv_cancel_right, e1]
    abel

end GlobalTheory.Ord2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CrystallineCocycleCoboundaryOfNegativeWeight
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped Matrix

noncomputable section

namespace GlobalTheory.NegVan

private theorem fd_adjoin_range (l : ℕ) [Fact l.Prime] {ι : Type} [Finite ι] (f : ι → PadicAlgCl l) :
    FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] (Set.range f)) := by
  haveI : Finite (Set.range f) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun z _ =>
      (Algebra.IsAlgebraic.isAlgebraic z).isIntegral

open TensorProduct in

private theorem desc {l : ℕ} [Fact l.Prime] {H : Type} [Group H] [TopologicalSpace H] (φ : H →* GQ l)
    (κ : H →* (PadicAlgCl l)ˣ) (E₀ : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] E₀]
    (hκ : ∀ g, (κ g : PadicAlgCl l) ∈ E₀) (c : H → PadicAlgCl l) (hc : c ∈ Loc.finiteCocycles φ (Loc.chRep κ)) :
    ∃ (E : IntermediateField ℚ_[l] (PadicAlgCl l)) (_ : FiniteDimensional ℚ_[l] E) (κ' : H →* Eˣ) (c' : H → E),
      (∀ g, ((κ' g : E) : PadicAlgCl l) = κ g) ∧ (∀ g, (c' g : PadicAlgCl l) = c g) ∧ c' ∈ Loc.finiteCocycles φ (Loc.chRep κ') := by
  obtain ⟨⟨hcc, hcoc⟩, x, hx⟩ := hc
  obtain ⟨S, rfl⟩ := TensorProduct.exists_finset x
  obtain ⟨T⟩ := Loc.tiedP l
  haveI : IsDomain (Loc.Bcr l) := GlobalTheory.RegularRing.isDomain_of_tied T (Loc.botExt l)
  haveI := fd_adjoin_range l (fun p : S => p.1.1)
  let E : IntermediateField ℚ_[l] (PadicAlgCl l) := E₀ ⊔ IntermediateField.adjoin ℚ_[l] (Set.range fun p : S => p.1.1)
  have hκE : ∀ g, (κ g : PadicAlgCl l) ∈ E := fun g => (le_sup_left : E₀ ≤ E) (hκ g)
  have hS : ∀ p ∈ S, p.1 ∈ E := fun p hp =>
    (le_sup_right : _ ≤ E) (IntermediateField.subset_adjoin _ _ ⟨⟨p, hp⟩, rfl⟩)
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap E (PadicAlgCl l))
    (LinearMap.ker_eq_bot.2 (algebraMap E (PadicAlgCl l)).injective)
  have hπ1 : ∀ y : E, π (y : PadicAlgCl l) = y := fun y => LinearMap.congr_fun hπ y
  let κ' : H →* Eˣ := MonoidHom.toHomUnits
    { toFun := fun g => ⟨κ g, hκE g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h => Subtype.ext (by simp) }
  have hκ' : ∀ g, ((κ' g : E) : PadicAlgCl l) = κ g := fun g => rfl
  have hπ2 : ∀ g y, π (κ g * y) = κ' g * π y := fun g y => map_smul π (κ' g : E) y
  let f : PadicAlgCl l →ₗ[ℚ_[l]] E := π.restrictScalars ℚ_[l]
  let i : E →ₗ[ℚ_[l]] PadicAlgCl l := E.val.toLinearMap
  have key : ∀ g (y : PadicAlgCl l ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) f (Loc.actC φ (Loc.chRep κ) g y) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, f, hπ2]
    | add a b ha hb => simp only [map_add, ha, hb]
  have key' : ∀ g (y : E ⊗[ℚ_[l]] Loc.Bcr l), LinearMap.rTensor (Loc.Bcr l) i (Loc.actC φ (Loc.chRep κ') g y) =
      Loc.actC φ (Loc.chRep κ) g (LinearMap.rTensor (Loc.Bcr l) i y) := by
    intro g y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [Loc.actC, Loc.chRep, i, hκ']
    | add a b ha hb => simp only [map_add, ha, hb]
  set x := ∑ p ∈ S, p.1 ⊗ₜ[ℚ_[l]] p.2 with hxd
  have hix : LinearMap.rTensor (Loc.Bcr l) i (LinearMap.rTensor (Loc.Bcr l) f x) = x := by
    rw [hxd, map_sum, map_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul]
    congr 1
    exact congrArg Subtype.val (hπ1 ⟨p.1, hS p hp⟩)
  have hx' : ∀ g, f (c g) ⊗ₜ[ℚ_[l]] (1 : Loc.Bcr l) =
      Loc.actC φ (Loc.chRep κ') g (LinearMap.rTensor (Loc.Bcr l) f x) - LinearMap.rTensor (Loc.Bcr l) f x := fun g => by
    rw [← key, ← map_sub, ← hx g, LinearMap.rTensor_tmul]
  have hcE : ∀ g, ((f (c g) : E) : PadicAlgCl l) = c g := fun g => by
    have h1 := congrArg (LinearMap.rTensor (Loc.Bcr l) i) (hx' g)
    rw [map_sub, key', hix, ← hx g, LinearMap.rTensor_tmul] at h1
    exact Algebra.TensorProduct.includeLeft_injective (R := ℚ_[l]) (S := ℚ_[l]) (B := Loc.Bcr l)
      (algebraMap ℚ_[l] (Loc.Bcr l)).injective h1
  refine ⟨E, inferInstance, κ', fun g => f (c g), hκ', hcE, ⟨?_, fun g h => ?_⟩, _, hx'⟩
  · exact continuous_induced_rng.2 (hcc.congr fun g => (hcE g).symm)
  · have := hcoc g h
    simp only [Loc.chRep] at this ⊢
    simp [this, f, hπ2]

private theorem coef_finext {l : ℕ} [Fact l.Prime] (c : Coef l) :
    ∃ K : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] K ∧ ∀ x ∈ c.O, x ∈ K := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top (R := ℤ_[l]) (M := c.O))
  refine ⟨_, fd_adjoin_range l (fun q : s => ((q : c.O) : PadicAlgCl l)), fun x hx => ?_⟩
  let K := IntermediateField.adjoin ℚ_[l] (Set.range fun q : s => ((q : c.O) : PadicAlgCl l))
  let M : Submodule ℤ_[l] (PadicAlgCl l) := (K.toSubalgebra.restrictScalars ℤ_[l]).toSubmodule
  have hmem : (⟨x, hx⟩ : c.O) ∈ Submodule.span ℤ_[l] (s : Set c.O) := hs ▸ Submodule.mem_top
  have hle : Submodule.span ℤ_[l] (s : Set c.O) ≤ M.comap c.O.val.toLinearMap := by
    rw [Submodule.span_le]
    intro q hq
    exact IntermediateField.subset_adjoin _ _ ⟨⟨q, hq⟩, rfl⟩
  exact hle hmem

end GlobalTheory.NegVan

open GlobalTheory.NegVan in

theorem GlobalTheory.NegVan.crys_cocycle_coboundary_of_neg_weight :
    Loc.LocalPublishedTheorems → ∀ (l : ℕ) [Fact l.Prime] (κ : GQ l →* (Qbar l)ˣ), Continuous (fun σ => (κ σ : Qbar l)) →
      ∀ c : Coef l, (∀ σ, (κ σ : Qbar l) ∈ c.O) → ∀ w : ℤ, w < 0 → Loc.HasWeight (MonoidHom.id (GQ l)) κ w →
      ∀ f ∈ Loc.finiteCocycles (MonoidHom.id (GQ l)) (Loc.chRep κ), ∃ x, ∀ σ, f σ = (κ σ : Qbar l) * x - x := by
  intro hP l _ κ hκc c hκO w hw hwt f hf
  obtain ⟨K₀, hK₀, hK⟩ := coef_finext c
  obtain ⟨E, _, κ', c', hκ, hc', hf'⟩ := desc (MonoidHom.id (GQ l)) κ K₀ (fun g => hK _ (hκO g)) f hf
  haveI : IsModuleTopology ℚ_[l] E := isModuleTopologyOfFiniteDimensional
  have hw' : Loc.HasWeight (MonoidHom.id (GQ l)) κ' w := by
    obtain ⟨U, hU, hUw⟩ := hwt
    refine ⟨U, hU, fun g hg hI => ?_⟩
    have h := hUw g hg hI
    have hcy : Units.map ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l)
        (Loc.cycA l l E g) = Loc.cycA l l (PadicAlgCl l) g := by
      refine Units.ext ?_
      simp only [Units.coe_map, MonoidHom.coe_coe, Loc.cycA, MonoidHom.comp_apply]
      rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] E, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (PadicAlgCl l)]
      rfl
    apply Units.map_injective (f := ((algebraMap E (PadicAlgCl l) : E →+* PadicAlgCl l) : E →* PadicAlgCl l))
      (algebraMap E (PadicAlgCl l)).injective
    rw [map_zpow, MonoidHom.id_apply, hcy, ← MonoidHom.id_apply (GQ l) g, ← h]
    exact Units.ext (hκ g)
  have hz := (Loc.z1fChar hP (MonoidHom.id (GQ l)) Topology.IsOpenEmbedding.id κ'
    (continuous_induced_rng.2 (hκc.congr fun g => (hκ g).symm)) w hw').1 hw
  rw [hz.1, mem_coboundaries1] at hf'
  obtain ⟨m, hm⟩ := hf'
  refine ⟨(m : PadicAlgCl l), fun σ => ?_⟩
  have h4 : c' σ = κ' σ * m - m := hm σ
  rw [← hc' σ, h4, AddSubgroupClass.coe_sub, MulMemClass.coe_mul, hκ]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SelNZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2
open scoped Matrix

noncomputable section

namespace GlobalTheory.Ord2.GwCount

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

def SelN (c : Coef l) (n : ℕ) (S : Finset Pl) (A : ValuationSubring Ω) (V : R2 Ω l)
    (z : G ℚ Ω → Fin 2 → Qbar l) : Prop :=
  Coc1 c n V ⊤ z ∧ (∀ a ∈ (toGS Ω (S : Set Pl)).ker, Cv n (z a) 0) ∧
    (∀ q ∈ S, ((l : ℕ) : 𝓞 ℚ) ∉ q.asIdeal → ∃ B : ValuationSubring Ω, IsPlaceOver B q ∧
      Cob1 c n V (Ine (F := ℚ) B) z) ∧
    (∃ x ∈ c.O, ∀ s ∈ Dec (F := ℚ) A, Cg n (z s 1) (mat V s 1 1 * x - x))

end GlobalTheory.Ord2.GwCount
end
end

