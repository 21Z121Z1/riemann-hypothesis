import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NontrivialTwJacquetOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactLatticeGL
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0102
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasExponentZeroIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def CuspidalMultiplicityOne : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π π' : CuspSub E a),
    CG.mk π = CG.mk π' → π.V = π'.V

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CuspidalMultiplicityOneUnitary
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def CuspidalMultiplicityOneUnitary : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π π' : CuspSub E a,
    π.IsUnitary → π'.IsUnitary → CG.mk π = CG.mk π' → π.V = π'.V

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def DiscreteSpectrumResidual : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N →
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d) ∧
    (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → IsNormalised π →
      ∃! V : Submodule ℂ (Sm E N), IsDiscrete V ∧ IsSpehOf V π d) ∧
    (∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d a' d' : ℕ) (π : CuspSub E a) (π' : CuspSub E a'),
      IsNormalised π → IsNormalised π' → IsSpehOf V π d → IsSpehOf V π' d' →
        d = d' ∧ (⟨a, CG.mk π⟩ : Σ b, CG E b) = ⟨a', CG.mk π'⟩) ∧
    (∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → IsIsoGL V V' → V = V') ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → ∀ w, (∃ σ σ', π.IsLocComp w σ ∧ IsLocCompGL V w σ') ∧
        ∀ σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
          GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

def IsUnitaryLSeg (δ : IrrGL k) : Prop := (∃ Δ : Segment k, IsLSeg Δ δ.rep) ∧ IsUnitarisable δ.rep

def factors (δ : List (IrrGL k)) (τ : List (IrrGL k × ℝ)) : List (IrrGL k) :=
  δ ++ τ.flatMap fun p => [p.1.nu (p.2 : ℝ), p.1.nu ((-p.2 : ℝ) : ℂ)]

def IsComplementaryProduct (π : Representation ℂ (GL (Fin N) k) V) : Prop :=
  ∃ (δ : List (IrrGL k)) (τ : List (IrrGL k × ℝ)), (∀ x ∈ δ, IsUnitaryLSeg x) ∧
    (∀ p ∈ τ, IsUnitaryLSeg p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) ∧
    ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = N), List.ofFn x = factors δ τ ∧
      Nonempty (π.Equiv (prodIrr x hd))

end GlobalTheory.GenericUnitary

namespace GlobalTheory.Published

def GenericUnitaryDualGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V),
    IsSmooth π → π.IsIrreducible → IsUnitarisable π → IsGeneric π → GenericUnitary.IsComplementaryProduct π

end GlobalTheory.Published

namespace GlobalTheory.GenericUnitary

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {N : ℕ}

theorem exists_of_mem_factors {δ : List (IrrGL k)} {τ : List (IrrGL k × ℝ)} (hδ : ∀ x ∈ δ, IsUnitaryLSeg x)
    (hτ : ∀ p ∈ τ, IsUnitaryLSeg p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) {y : IrrGL k} (hy : y ∈ factors δ τ) :
    ∃ (x : IrrGL k) (s : ℝ), IsUnitaryLSeg x ∧ |s| < 1 / 2 ∧ y = x.nu s := by
  rcases List.mem_append.1 hy with hy | hy
  · exact ⟨y, 0, hδ y hy, by norm_num, by simp⟩
  · obtain ⟨p, hp, hy⟩ := List.mem_flatMap.1 hy
    obtain ⟨h1, h2, h3⟩ := hτ p hp
    rcases List.mem_pair.1 hy with rfl | rfl
    · exact ⟨p.1, p.2, h1, by rwa [abs_of_pos h2], rfl⟩
    · exact ⟨p.1, -p.2, h1, by rwa [abs_neg, abs_of_pos h2], rfl⟩

theorem IsComplementaryProduct.exists_prod {π : Representation ℂ (GL (Fin N) k) V} (H : IsComplementaryProduct π) :
    ∃ (h : ℕ) (δ : Fin h → IrrGL k) (Δ : Fin h → Segment k) (s : Fin h → ℝ),
      (∀ j, IsLSeg (Δ j) (δ j).rep) ∧ (∀ j, IsUnitarisable (δ j).rep) ∧ (∀ j, |s j| < 1 / 2) ∧
      ∃ hd : ∑ j, ((δ j).nu (s j)).1 = N, Nonempty (π.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) := by
  obtain ⟨δ, τ, hδ, hτ, h, x, hd, hx, φ⟩ := H
  choose y s hy hs e using fun j => exists_of_mem_factors hδ hτ (y := x j) (hx ▸ List.mem_ofFn.2 ⟨j, rfl⟩)
  choose Δ hΔ using fun j => (hy j).1
  obtain rfl : x = fun j => (y j).nu (s j) := funext e
  exact ⟨h, y, Δ, s, hΔ, fun j => (hy j).2, hs, hd, φ⟩

theorem isUnitarisable_of_equiv {G : Type} [Group G] {π : Representation ℂ G V} {σ : Representation ℂ G W}
    (φ : π.Equiv σ) (h : IsUnitarisable π) : IsUnitarisable σ := by
  obtain ⟨B, h1, h2, h3⟩ := h
  refine ⟨(B ∘ₗ φ.symm.toLinearEquiv.toLinearMap).compl₂ φ.symm.toLinearEquiv.toLinearMap, fun v w => h1 _ _,
    fun v hv => h2 _ (φ.symm.toLinearEquiv.map_ne_zero_iff.2 hv), fun g v w => ?_⟩
  have e : ∀ v, φ.symm.toLinearEquiv (σ g v) = π g (φ.symm.toLinearEquiv v) := fun v =>
    φ.symm.toIntertwiningMap.isIntertwining _ _ g v
  show B (φ.symm.toLinearEquiv (σ g v)) (φ.symm.toLinearEquiv (σ g w)) = _
  rw [e, e, h3]
  rfl

theorem isUnitaryLSeg_of_isCusp {ρ : IrrGL k} (hρ : ρ.IsCusp) (hu : IsUnitarisable ρ.rep) : IsUnitaryLSeg ρ :=
  ⟨⟨_, (single_spec hρ).2.1⟩, hu⟩

theorem IsUnitaryLSeg.isComplementaryProduct {δ : IrrGL k} (h : IsUnitaryLSeg δ) : IsComplementaryProduct δ.rep :=
  ⟨[δ], [], by simpa using h, by simp, 1, fun _ => δ, by simp, rfl, nonempty_equiv_prodIrr_one δ _⟩

theorem IsComplementaryProduct.of_equiv {π : Representation ℂ (GL (Fin N) k) V} {σ : Representation ℂ (GL (Fin N) k) W}
    (H : IsComplementaryProduct π) (φ : π.Equiv σ) : IsComplementaryProduct σ := by
  obtain ⟨δ, τ, hδ, hτ, h, x, hd, hx, ⟨ψ⟩⟩ := H
  exact ⟨δ, τ, hδ, hτ, h, x, hd, hx, ⟨φ.symm.trans ψ⟩⟩

theorem isComplementaryProduct_of_isCuspidal {π : Representation ℂ (GL (Fin N) k) V} (hN : 0 < N)
    (hi : π.IsIrreducible) (hc : IsCuspidal π) (hu : IsUnitarisable π) : IsComplementaryProduct π :=
  (isUnitaryLSeg_of_isCusp (IrrGL.isCusp_of.2 ⟨hN, hc⟩)
    (isUnitarisable_of_equiv (IrrGL.equivOf π hc.1 hi) hu)).isComplementaryProduct.of_equiv
    (IrrGL.equivOf π hc.1 hi).symm

theorem unitaryChar_spec {χ : kˣ →* ℂˣ} (hs : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    IsSmooth (detRep (Fin 1) χ) ∧ (detRep (Fin 1) χ).IsIrreducible ∧ IsUnitarisable (detRep (Fin 1) χ) ∧
      IsGeneric (detRep (Fin 1) χ) ∧ IsComplementaryProduct (detRep (Fin 1) χ) :=
  have h : IsUnitarisable (detRep (Fin 1) χ) := (isUnitarisable_ofChar_iff _).2 fun _ => hu _
  ⟨(isCuspidal_detRep_one hs).1, isIrreducible_ofChar _, h, isGeneric_detRep_one χ,
    isComplementaryProduct_of_isCuspidal one_pos (isIrreducible_ofChar _) (isCuspidal_detRep_one hs) h⟩

end GlobalTheory.GenericUnitary

namespace GlobalTheory.Published

theorem GenericUnitaryDualGL.exists_prod (H : GenericUnitaryDualGL) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin N) k) V} (hs : IsSmooth π) (hi : π.IsIrreducible) (hu : IsUnitarisable π)
    (hg : IsGeneric π) :
    ∃ (h : ℕ) (δ : Fin h → IrrGL k) (Δ : Fin h → Segment k) (s : Fin h → ℝ),
      (∀ j, IsLSeg (Δ j) (δ j).rep) ∧ (∀ j, IsUnitarisable (δ j).rep) ∧ (∀ j, |s j| < 1 / 2) ∧
      ∃ hd : ∑ j, ((δ j).nu (s j)).1 = N, Nonempty (π.Equiv (prodIrr (fun j => (δ j).nu (s j)) hd)) :=
  (H k N V π hs hi hu hg).exists_prod

end GlobalTheory.Published
end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.IdeleCovolume

namespace GlobalTheory.DiscSpec.Model

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

omit [IsTotallyComplex E] in

theorem eq_one_of_isAbsPow {ν : HChar E} (h : ν.IsAbsPow 0) : ν = 1 :=
  GlobalTheory.HeckeUnrTrivial.eq_one_of_inf_of_val E ν (fun k => Units.ext (by simpa using h.2.2 k)) fun v _ => Units.ext (by simpa using h.2.1 v)

theorem eq_of_iso {π π' : CuspSub E 1} (h : π.Iso π') : π = π' := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  obtain ⟨χ', rfl⟩ := RankOne.exists_eq_twist π'
  rw [CG.ofChar_injective (Quotient.sound h)]

theorem iso_of_isQuotOf {a : ℕ} {π π' : CuspSub E a} (h : IsQuotOf π'.V π.V) : π.Iso π' := by
  obtain ⟨f, hf, hc⟩ := h
  have hm : ∀ φ ∈ π.V, f φ ∈ π'.V := fun φ hφ => hf ▸ Submodule.mem_map_of_mem hφ
  have hk : π.V ⊓ LinearMap.ker f = ⊥ := by
    refine (π.irred _ inf_le_left fun o φ hφ => ⟨π.stable o φ hφ.1, ?_⟩).resolve_right fun e => π'.ne_bot ?_
    · have h0 : f φ = 0 := hφ.2
      change f _ = 0
      rw [hc o φ hφ.1, h0, map_zero]
    · rw [← hf, eq_bot_iff]
      rintro _ ⟨φ, hφ, rfl⟩
      exact (e.ge hφ).2
  refine ⟨LinearEquiv.ofBijective (f.restrict hm) ⟨?_, ?_⟩, fun o φ => Subtype.ext (hc o φ.1 φ.2)⟩
  · refine (injective_iff_map_eq_zero _).2 fun φ h0 => Subtype.ext ?_
    have : φ.1 ∈ π.V ⊓ LinearMap.ker f := ⟨φ.2, congrArg Subtype.val h0⟩
    rwa [hk] at this
  · rintro ⟨ψ, hψ⟩
    obtain ⟨φ, hφ, rfl⟩ := hf.ge hψ
    exact ⟨⟨φ, hφ⟩, rfl⟩

def toCusp {V : Submodule ℂ (Sm E 1)} (h : IsDiscrete V) : CuspSub E 1 :=
  ⟨V, fun φ hφ => ⟨h.aut φ hφ, fun r h0 h1 => by omega⟩, h.stable, h.ne_bot, h.irred⟩

theorem iso_of_isSpehOf_one {a : ℕ} {π π' : CuspSub E a} (h : IsSpehOf π'.V π 1) : π.Iso π' := by
  obtain ⟨h, ν, hν, hq⟩ := h
  obtain rfl : ν = fun _ => 1 := funext fun i => eq_one_of_isAbsPow (by simpa [spehExp] using hν i)
  simp only [CuspSub.twist_one] at hq
  rw [indForms_one h π] at hq
  exact iso_of_isQuotOf hq

theorem left_lattice {a : ℕ} {π : CuspSub E a} (h : IsNormalised π) {φ : Sm E a} (hφ : φ ∈ π.V) :
    ∀ γ ∈ latticeGL E a, ∀ g, φ.1 (γ * g) = φ.1 g := by
  let S : Subgroup (GA E a) :=
    { carrier := {γ | ∀ g, φ.1 (γ * g) = φ.1 g}
      one_mem' := fun g => by rw [one_mul]
      mul_mem' := fun {x y} hx hy g => by rw [mul_assoc, hx, hy]
      inv_mem' := fun {x} hx g => by rw [← hx, mul_inv_cancel_left] }
  have : latticeGL E a ≤ S := sup_le (by rintro _ ⟨γ, rfl⟩; exact (π.cusp φ hφ).1.left γ)
    (Subgroup.zpowers_le.2 (h φ hφ 1))
  exact this

theorem continuous_form (π : CuspSub E 1) {φ : Sm E 1} (hφ : φ ∈ π.V) : Continuous φ.1 := by
  obtain ⟨ω, h⟩ := RankOne.exists_char π
  have e : φ.1 = fun g => ((ω g : ℂˣ) : ℂ) * φ.1 1 := funext fun g => by
    have h1 : φ.1 (1 * g) = ((ω g : ℂˣ) : ℂ) * φ.1 1 := congrFun (congrArg Subtype.val (h g φ hφ)) 1
    rwa [one_mul] at h1
  rw [e]
  exact (Units.continuous_val.comp (RankOne.continuous_char π ω h)).mul continuous_const

theorem isDiscrete_of_isNormalised {π : CuspSub E 1} (h : IsNormalised π) : IsDiscrete π.V := by
  refine ⟨fun φ hφ => (π.cusp φ hφ).1, fun φ hφ => ⟨h φ hφ, ?_⟩, π.stable, π.ne_bot, π.irred⟩
  obtain ⟨-, μ, 𝓕, hμ, hF, -⟩ := isSqInt_const E 1
  refine ⟨μ, 𝓕, hμ, hF, ?_⟩
  letI : MeasurableSpace (GA E 1) := borel _
  haveI : BorelSpace (GA E 1) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele E
  haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ad E)) :=
    inferInstanceAs (SecondCountableTopology (Fin 1 → Fin 1 → Ad E))
  haveI : SecondCountableTopology (Matrix (Fin 1) (Fin 1) (Ad E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (GA E 1) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI := discrete_latticeGL E
  haveI : Countable (latticeGL E 1) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨K, hK, hcov⟩ := exists_compact_latticeGL E
  have h2 := GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (latticeGL E 1) K hK hcov μ hμ 𝓕 hF
    (fun g => φ.1 g ^ 2) ((continuous_form π hφ).pow 2) fun γ hγ g => by rw [left_lattice h hφ γ hγ]
  simpa only [HasFiniteIntegral, enorm_pow] using h2.2

theorem isUnitary_of_isNormalised {π : CuspSub E 1} (h : IsNormalised π) : π.IsUnitary := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  refine (CG.isUnitary_mk _).1 ((CG.isUnitary_ofChar_iff χ).2 ?_)
  have hφ : mulChi 1 χ (oneFn E 1) ∈ ((CuspSub.triv E le_rfl).twist χ).V :=
    ⟨_, Submodule.mem_span_singleton_self _, rfl⟩
  obtain ⟨K, hK, hcov⟩ := exists_compact_latticeGL E
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (continuous_form _ hφ).continuousOn
  have hb : ∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov (CG.oneByOne x)
    have h1 := hC _ hk
    rw [left_lattice h hφ γ hγ, mulChi_apply] at h1
    change ‖1 * ((χ.1 (GeneralLinearGroup.det (CG.oneByOne x)) : ℂˣ) : ℂ)‖ ≤ C at h1
    rwa [CG.det_oneByOne, one_mul] at h1
  have hle : ∀ x, ‖((χ.1 x : ℂˣ) : ℂ)‖ ≤ 1 := fun x => by
    by_contra hc
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C (not_le.1 hc)
    have := hb (x ^ n)
    rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at this
    linarith
  intro x
  refine le_antisymm (hle x) ?_
  have := hle x⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, norm_inv] at this
  exact (inv_le_one₀ (norm_pos_iff.2 (Units.ne_zero _))).1 this

theorem isLocCompGL_iff {a : ℕ} (P : CuspSub E a) (w σ) : IsLocCompGL P.V w σ ↔ P.IsLocComp w σ := by
  constructor
  · rintro ⟨f, h0, h1, h2⟩
    exact ⟨f.codRestrict _ h1, fun e => h0 (LinearMap.ext fun v => congrArg Subtype.val (LinearMap.congr_fun e v)),
      fun g v => Subtype.ext (h2 g v)⟩
  · rintro ⟨f, h0, h1⟩
    exact ⟨P.V.subtype.comp f, fun e => h0 (LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun e v)),
      fun v => (f v).2, fun g v => congrArg Subtype.val (h1 g v)⟩

theorem hasSpehComp_rank_one (π : CuspSub E 1) : HasSpehComp π.V π 1 := by
  obtain ⟨χ, rfl⟩ := RankOne.exists_eq_twist π
  refine ⟨fun w => ⟨_, _, CG.isLoc_ofChar χ w, (isLocCompGL_iff _ _ _).2 (CG.isLoc_ofChar χ w)⟩, fun w σ σ' h h' => ?_,
    fun τ => ⟨_, CG.hasInfChar_ofChar χ τ, by rw [GlobalTheory.SphGal.spehInf_one]; exact CG.hasInfChar_ofChar χ τ⟩⟩
  let _ := GlobalTheory.LocalData.complRel w
  have := GlobalTheory.LocalData.isLocalField w
  obtain ⟨e⟩ := LocUniq.isLocComp_unique _ w σ σ' h ((isLocCompGL_iff _ w σ').1 h')
  obtain ⟨hd, hc⟩ := GlobalTheory.LocGL.isSpeh_one (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred)
  exact ⟨hd, hc.of_equiv ((GlobalTheory.LocGL.IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm.trans e) (.refl _)⟩

theorem discreteSpectrum_one :
    (∀ V : Submodule ℂ (Sm E 1), IsDiscrete V →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d) ∧
    (∀ (a d : ℕ) (π : CuspSub E a), d * a = 1 → IsNormalised π →
      ∃! V : Submodule ℂ (Sm E 1), IsDiscrete V ∧ IsSpehOf V π d) ∧
    (∀ V : Submodule ℂ (Sm E 1), IsDiscrete V → ∀ (a d a' d' : ℕ) (π : CuspSub E a) (π' : CuspSub E a'),
      IsNormalised π → IsNormalised π' → IsSpehOf V π d → IsSpehOf V π' d' →
        d = d' ∧ (⟨a, CG.mk π⟩ : Σ b, CG E b) = ⟨a', CG.mk π'⟩) ∧
    (∀ V V' : Submodule ℂ (Sm E 1), IsDiscrete V → IsDiscrete V' → IsIsoGL V V' → V = V') ∧
    ∀ V : Submodule ℂ (Sm E 1), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → HasSpehComp V π d := by
  have key : ∀ {V : Submodule ℂ (Sm E 1)} (hV : IsDiscrete V) {π : CuspSub E 1}, IsSpehOf V π 1 → π = toCusp hV :=
    fun hV π h => eq_of_iso (iso_of_isSpehOf_one (π' := toCusp hV) h)
  refine ⟨fun V hV => ?_, fun a d π h hn => ?_, fun V hV a d a' d' π π' _ _ e e' => ?_, fun V V' hV hV' h => ?_,
    fun V hV a d π _ e => ?_⟩
  · have hn : IsNormalised (toCusp hV) := isNormalised_of_isDiscrete hV
    exact ⟨1, 1, toCusp hV, isUnitary_of_isNormalised hn, hn, isSpehOf_one (toCusp hV)⟩
  · obtain ⟨rfl, rfl⟩ := mul_eq_one.1 h
    exact ⟨π.V, ⟨isDiscrete_of_isNormalised hn, isSpehOf_one π⟩, fun V hV => by rw [key hV.1 hV.2]; rfl⟩
  · obtain ⟨rfl, rfl⟩ := mul_eq_one.1 e.mul_eq
    obtain ⟨rfl, rfl⟩ := mul_eq_one.1 e'.mul_eq
    rw [key hV e, key hV e']
    exact ⟨rfl, rfl⟩
  · exact congrArg CuspSub.V (eq_of_iso ((isIsoGL_iff (toCusp hV) (toCusp hV')).1 h))
  · obtain ⟨rfl, rfl⟩ := mul_eq_one.1 e.mul_eq
    rw [key hV e]
    exact hasSpehComp_rank_one (toCusp hV)

theorem exists_discrete_speh : ∃ (V : Submodule ℂ (Sm E 1)) (π : CuspSub E 1),
    IsDiscrete V ∧ IsNormalised π ∧ IsSpehOf V π 1 :=
  ⟨_, _, isDiscrete_of_isNormalised (isNormalised_triv le_rfl), isNormalised_triv le_rfl, isSpehOf_one _⟩

theorem exists_not_isNormalised : ∃ π : CuspSub E 1, ¬ IsNormalised π := by
  obtain ⟨σ, hσ⟩ := exists_not_isUnitary (E := E)
  induction σ using Quotient.inductionOn with
  | h π => exact ⟨π, fun h => hσ ((CG.isUnitary_mk π).2 (isUnitary_of_isNormalised h))⟩

theorem exponents_two : spehExp 2 0 + (1 : ℕ) * spehExp 2 0 = 1 ∧ spehExp 2 1 + (1 : ℕ) * spehExp 2 1 = -1 := by
  norm_num [spehExp]

end GlobalTheory.DiscSpec.Model

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConverseGL
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalConverseGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (m : ℕ), 0 < m →
    ∀ π₁ π₂ : IrrRep (GL (Fin (m + 1)) k), IsCuspidal π₁.ρ → IsCuspidal π₂.ρ →
      (∀ τ : IrrRep (GL (Fin m) k), ∃ e : ℂ, HasPairEps ψ π₁.ρ τ.ρ e ∧ HasPairEps ψ π₂.ρ τ.ρ e) →
      Nonempty (π₁.ρ.Equiv π₂.ρ)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumByClass
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def ResidualSpectrumByClass : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N →
    (∃ J : (a : ℕ) → CuspSub E a → ℕ → Submodule ℂ (Sm E N),
      (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → π.IsUnitary → IsNormalised π →
        IsDiscrete (J a π d) ∧ IsSpehOf (J a π d) π d) ∧
      ∀ V : Submodule ℂ (Sm E N), IsDiscrete V →
        V ≤ ⨆ (a : ℕ) (d : ℕ) (π : CuspSub E a) (_ : d * a = N ∧ π.IsUnitary ∧ IsNormalised π), J a π d) ∧
    (∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → IsSpehOf V' π d → IsIsoGL V V') ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
        GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ResidualSpectrumHilbertSum
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CuspRep.CuspidalL2GL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

def ResidualSpectrumHilbertSum : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N →
    (∃ J : (a : ℕ) → CuspSub E a → ℕ → Submodule ℂ (Sm E N),
      (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → π.IsUnitary → IsNormalised π →
        IsDiscrete (J a π d) ∧ IsSpehOf (J a π d) π d) ∧
      ∀ (μ : Measure (GA E N)) [μ.IsHaarMeasure] (V : Submodule ℂ (Sm E N)), IsDiscrete V →
        classes V μ ≤ (classes (⨆ (a : ℕ) (d : ℕ) (π : CuspSub E a)
          (_ : d * a = N ∧ π.IsUnitary ∧ IsNormalised π), J a π d) μ).topologicalClosure) ∧
    (∀ V V' : Submodule ℂ (Sm E N), IsDiscrete V → IsDiscrete V' → ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → IsSpehOf V' π d → IsIsoGL V V') ∧
    ∀ V : Submodule ℂ (Sm E N), IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
        GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

end GlobalTheory.Published

end
end

