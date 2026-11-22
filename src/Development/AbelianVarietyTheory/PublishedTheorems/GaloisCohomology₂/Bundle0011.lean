import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeIsobaric
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0023
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteHyp
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.CuspRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCWords GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.TheRec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCWords

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n c : ℕ} {N : Fin c → ℕ}

def IsIsobaricComp (V : ∀ i, Submodule ℂ (Sm E (N i))) (w : HeightOneSpectrum (𝓞 E))
    (P : SmIrr (GL (Fin n) (w.adicCompletion E))) : Prop :=
  ∃ (A : ValuationSubring (AlgebraicClosure E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h)
    (σ : ∀ i, SmIrr (GL (Fin (N i)) (w.adicCompletion E))), IsTheRec h rc ∧ (∀ i, IsLocCompGL (V i) w (σ i)) ∧
    rc (IrrGL.of P.ρ P.smooth P.irred) = sumList (List.ofFn fun i => rc (IrrGL.of (σ i).ρ (σ i).smooth (σ i).irred))

structure IsIsobaricBaseChange (π : Submodule ℂ (UA E n → ℂ)) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i))) : Prop where

  pos : ∀ i, 0 < N i

  discrete : ∀ i, IsDiscreteU (V i)

  csd : ∀ i, PairedGL (V i) (V i) GlobalTheory.ContraPair.conjOp

  unram : ∀ (w : HeightOneSpectrum (𝓞 E)) (P : SmIrr (GL (Fin n) (w.adicCompletion E))), IsIsobaricComp V w P →
    IsUnramU π w → GlobalTheory.LGrp.IsSpherical P.ρ (GlobalTheory.LFun.KGL w n) ∧ IsUnramBC π w P

  split : ∀ (w : HeightOneSpectrum (𝓞 E)) (P : SmIrr (GL (Fin n) (w.adicCompletion E))), IsIsobaricComp V w P →
    IsSplitAt w → IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) P.ρ

  weight : ∃ W₁ W₂ : Submodule ℂ (Sm E n), IsInfSubquot h V W₁ W₂ ∧
    ∀ τ lam, HasWeightAt π τ lam → QuotHasInfChar W₁ W₂ τ (infOfWeight lam)

end GlobalTheory.BCWords

namespace GlobalTheory.Published

def BaseChangeDefiniteHyp : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E],
    (∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) →
    ∀ (p : ℕ), p.Prime → ∀ S : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E))), S.Finite →
    (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) ∈ S → IsSplitAt w) →
    (∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), (p : 𝓞 (maximalRealSubfield E)) ∈ v.asIdeal → v ∈ S) →
    ∀ n : ℕ, 1 ≤ n → ∀ π : Submodule ℂ (UA E n → ℂ), IsAutRepU π →
      ∃ (c : ℕ) (N : Fin c → ℕ) (h : ∑ i, N i = n) (V : ∀ i, Submodule ℂ (Sm E (N i))), IsIsobaricBaseChange π h V

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DeligneLocalConstants
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def DeligneLocalConstants : Prop :=
  ∀ (Ω : Type) [Field Ω] (A : ValuationSubring Ω), ∃ ε : EpsMeasFamily A, IsDeligneMeas ε

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GammaMultiplicativeGL
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def GammaMultiplicativeGL : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 →
    ∀ (n m t : ℕ) (π : IrrRep (GL (Fin n) k)) (τ : IrrRep (GL (Fin m) k)) (ρ : Fin t → IrrGL k) (z : Fin t → ℝ)
      (hd : ∑ i, ((ρ i).nu (z i)).1 = m) (e : Fin t → ℂ), 0 < m → m < n →
      IsCuspidal π.ρ → GlobalTheory.Whittaker.IsGeneric ψ π.ρ → GlobalTheory.Whittaker.IsGeneric ψ⁻¹ τ.ρ →
      (∀ i, (ρ i).IsCusp ∧ IsUnitarisable (ρ i).rep) → Antitone z →
      IsSubquotient τ.ρ (prodIrr (fun i => (ρ i).nu (z i)) hd) →
      (∀ i, HasPairGamma ψ π.ρ ((ρ i).nu (z i)).rep (e i)) → HasPairGamma ψ π.ρ τ.ρ (∏ i, e i)

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NonemptyEquivParIndZero
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.LocGL.ProjLine Matrix

namespace GlobalTheory.Published.LanglandsSumTests

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {χ : kˣ →* ℂˣ}

theorem jhMult_parInd {η : kˣ →* ℂˣ} (hη : IsSmoothChar η) :
    jhMult (detRep (Fin 2) η) (parInd pts (ofChar (detLevi pts η))) = 1 ∧
      ¬ (parInd pts (ofChar (detLevi pts η))).IsIrreducible := by
  classical
  obtain ⟨V, _, _, π, f, ⟨φ⟩, hf, h0, h, h1⟩ := exists_line hη
  have hi : (detRep (Fin 2) η).IsIrreducible := isIrreducible_ofChar _
  refine ⟨?_, fun H => ?_⟩
  · rw [← jhMult_congr_right _ φ, JHMult.jhMult_exact f (quotMk f.range) hi hf
      f.range.toSubmodule.mkQ_surjective (fun u => (Submodule.Quotient.mk_eq_zero _).2 ⟨u, rfl⟩)
      (fun v hv => (Submodule.Quotient.mk_eq_zero _).1 hv), jhMult_self hi]
    have : jhMult (detRep (Fin 2) η) (quot f.range) = 0 := by
      by_contra hne
      obtain ⟨e⟩ := (JHMult.jhMult_ne_zero_iff.1 hne).nonempty_equiv hi (isCosocle_quot h0 h).1
      exact h1.false e.toLinearEquiv
    rw [this, add_zero]
  · have H' : π.IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv φ.symm H
    rcases eq_bot_or_eq_top f.range with e | e
    · exact (isAtom_range hi f hf).1 e
    · exact h0 e

theorem nonempty_equiv_prod (hχ : IsSmoothChar χ) :
    Nonempty ((parInd pts (ofChar (detLevi pts (χ * absPow k (1 / 2))))).Equiv
      (prod₂ (detRep (Fin 1) χ) (detRep (Fin 1) (χ * absPow k 1)))) := by
  have hν := hχ.mul (isSmoothChar_absPow (k := k) 1)
  obtain ⟨a⟩ := nonempty_prod₂_equiv_prodIrr _ (IrrRep.det (Fin 1) χ hχ).smooth (IrrRep.det (Fin 1) χ hχ).irr
    _ (IrrRep.det (Fin 1) _ hν).smooth (IrrRep.det (Fin 1) _ hν).irr rfl
  obtain ⟨hd, ⟨ψ⟩⟩ := exists_equiv_prodIrr (θ := ![χ, χ * absPow k 1])
    (Fin.forall_fin_two.2 ⟨hχ, hν⟩)
    (x := ![IrrGL.of _ (IrrRep.det (Fin 1) χ hχ).smooth (IrrRep.det (Fin 1) χ hχ).irr,
      IrrGL.of _ (IrrRep.det (Fin 1) _ hν).smooth (IrrRep.det (Fin 1) _ hν).irr])
    (Fin.forall_fin_two.2 ⟨rfl, rfl⟩)
    (Θ := detLevi pts (χ * absPow k (1 / 2))) fun g => by
      rw [detLevi_pts, Fin.prod_univ_two, mul_assoc χ, mul_assoc χ, ← absPow_add, ← absPow_add]
      norm_num
  exact ⟨Representation.Equiv.trans ψ (Representation.Equiv.symm a)⟩

theorem isL_char {y : IrrGL k} (hy : y.IsCusp) (hχ : IsSmoothChar χ) (e : y = IrrGL.ofChar χ hχ) :
    IsL {Segment.single y hy} (detRep (Fin 1) χ) := by
  subst e
  exact (single_spec hy).2.2.2.of_equiv (equivRep (IrrRep.det (Fin 1) χ hχ)).symm

theorem eq_of_isLSeg_single {ρ x : IrrGL k} (hρ : ρ.IsCusp) (h : IsLSeg (.single ρ hρ) x.rep) : x = ρ := by
  obtain ⟨n, c⟩ := x
  obtain ⟨d, c'⟩ := ρ
  obtain rfl : d = n := (one_mul d).symm.trans h.deg_eq
  exact congrArg _ (irrCl_eq_iff.2 ((single_spec hρ).2.1.unique h))

theorem factors_eq (hχ : IsSmoothChar χ) {h : ℕ} {x : Fin h → IrrGL k}
    (H : LFactors ({Segment.single _ (IrrGL.isCusp_ofChar χ hχ)} +
      {Segment.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)}) x) :
    h = 2 ∧ HEq x ![(IrrGL.ofChar χ hχ).nu 1, IrrGL.ofChar χ hχ] := by
  obtain ⟨Δ, ⟨hm, ho⟩, hΔ⟩ := H
  obtain rfl : h = 2 := by simpa using congrArg Multiset.card hm
  have hm' : ({Δ 0, Δ 1} : Multiset (Segment k)) =
    {.single _ (IrrGL.isCusp_ofChar χ hχ), .single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)} := hm
  have hp := single_precedes χ hχ
  have h01 : Δ 0 = .single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1) ∧ Δ 1 = .single _ (IrrGL.isCusp_ofChar χ hχ) := by
    rcases Multiset.cons_eq_cons.1 hm' with ⟨a, b⟩ | ⟨-, s, a, b⟩
    · exact absurd hp.1 (by rw [← a, ← Multiset.singleton_inj.1 b]; exact ho 0 1 (by decide))
    · obtain rfl : s = 0 := by simpa using congrArg Multiset.card a
      exact ⟨(Multiset.singleton_inj.1 b).symm, Multiset.singleton_inj.1 a⟩
  refine ⟨rfl, heq_of_eq (funext (Fin.forall_fin_two.2 ⟨?_, ?_⟩))⟩
  · exact eq_of_isLSeg_single _ (h01.1 ▸ hΔ 0)
  · exact eq_of_isLSeg_single _ (h01.2 ▸ hΔ 1)

theorem equiv_of_isL (hχ : IsSmoothChar χ) {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin 2) k) V} (H : IsL ({Segment.single _ (IrrGL.isCusp_ofChar χ hχ)} +
      {Segment.single _ ((IrrGL.isCusp_ofChar χ hχ).nu 1)}) π) :
    Nonempty (π.Equiv (detRep (Fin 2) (χ * absPow k (1 / 2)))) := by
  obtain ⟨_, x, hd, hx, hc⟩ := H
  obtain ⟨_, y, hd', hy, hc'⟩ := isL_detRep_two hχ
  obtain ⟨rfl, h1⟩ := factors_eq hχ hx
  obtain ⟨rfl, h2⟩ := factors_eq hχ hy
  obtain rfl : x = y := eq_of_heq (h1.trans h2.symm)
  exact hc'.unique hc

theorem linked_case (hχ : IsSmoothChar χ) :
    ∃ (𝔪 𝔫 : Multiset (Segment k)) (π₁ π₂ : IrrRep (GL (Fin 1) k)),
      IsL 𝔪 π₁.ρ ∧ IsL 𝔫 π₂.ρ ∧ ¬ (prod₂ π₁.ρ π₂.ρ).IsIrreducible ∧
      (∃ π : IrrRep (GL (Fin (1 + 1)) k), IsL (𝔪 + 𝔫) π.ρ) ∧
        ∀ π : IrrRep (GL (Fin (1 + 1)) k), IsL (𝔪 + 𝔫) π.ρ → jhMult π.ρ (prod₂ π₁.ρ π₂.ρ) = 1 := by
  have hη := hχ.mul (isSmoothChar_absPow (k := k) (1 / 2))
  obtain ⟨φ⟩ := nonempty_equiv_prod hχ
  refine ⟨_, _, IrrRep.det (Fin 1) χ hχ, IrrRep.det (Fin 1) _ (hχ.mul (isSmoothChar_absPow 1)),
    isL_char (IrrGL.isCusp_ofChar χ hχ) hχ rfl,
    isL_char ((IrrGL.isCusp_ofChar χ hχ).nu 1) _ (IrrGL.tw_ofChar _ _ hχ (isSmoothChar_absPow _)),
    fun H => (jhMult_parInd hη).2 (GlobalTheory.Parabolic.isIrreducible_of_equiv φ.symm H),
    ⟨IrrRep.det (Fin 2) _ hη, isL_detRep_two hχ⟩, fun π h => ?_⟩
  obtain ⟨e⟩ := equiv_of_isL hχ h
  have h1 := jhMult_congr_right (detRep (Fin 2) (χ * absPow k (1 / 2))) φ
  rw [(jhMult_parInd hη).1] at h1
  have h2 := jhMult_congr_left e (prod₂ (detRep (Fin 1) χ) (detRep (Fin 1) (χ * absPow k 1)))
  exact h2.trans h1.symm

example : IsNonarchimedeanLocalField ℚ_[2] ∧ CharZero ℚ_[2] ∧ IsSmoothChar (1 : ℚ_[2]ˣ →* ℂˣ) :=
  ⟨inferInstance, inferInstance, isSmoothChar_one⟩

theorem nonempty_equiv_parInd_zero {α V : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [AddCommGroup V] [Module ℂ V] (e : (Σ a, m a) ≃ Fin 0)
    (ρ : Representation ℂ (Levi k m) V) (L : ℂ ≃ₗ[ℂ] V) :
    Nonempty ((detRep (Fin 0) (1 : kˣ →* ℂˣ)).Equiv (parInd e ρ)) := by
  have hg : ∀ g : GL (Fin 0) k, g = 1 := fun g => Units.ext (Subsingleton.elim _ _)
  let f : ℂ →ₗ[ℂ] IndSp e ρ :=
    { toFun := fun c => ⟨⟨fun _ => L c, fun p g => by
          obtain rfl : p = 1 := Subtype.ext (hg _)
          simp⟩, mem_smoothPart_of_nhds (Filter.Eventually.of_forall fun g => rfl)⟩
      map_add' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_add L a b))
      map_smul' := fun a b => Subtype.ext (Subtype.ext (funext fun _ => map_smul L a b)) }
  refine ⟨equivOfBijective ⟨f, fun g => by rw [hg g, map_one, map_one]; rfl⟩ ⟨fun a b h => ?_, fun φ => ?_⟩⟩
  · have h1 : L a = L b := congrArg (fun φ : IndSp e ρ => φ.1.1 1) h
    exact L.injective h1
  · refine ⟨L.symm (φ.1.1 1), Subtype.ext (Subtype.ext (funext fun g => ?_))⟩
    rw [hg g]
    exact L.apply_symm_apply _

theorem isL_rank_zero {𝔪 : Multiset (Segment k)} {V : Type} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (GL (Fin 0) k) V} (h : IsL 𝔪 π) :
    𝔪 = 0 ∧ Nonempty (π.Equiv (detRep (Fin 0) (1 : kˣ →* ℂˣ))) := by
  have h0 : 𝔪 = 0 := Multiset.eq_zero_of_forall_notMem fun Δ hΔ => by
    have := Multiset.sum_eq_zero_iff.1 (Tests.IsL_deg h) _ (Multiset.mem_map_of_mem _ hΔ)
    exact (Nat.mul_pos Δ.len_pos Δ.d_pos).ne' this
  subst h0
  obtain ⟨s, x, hd, ⟨Δ, ⟨hm, -⟩, -⟩, hc⟩ := h
  obtain rfl : s = 0 := by simpa using congrArg Multiset.card hm
  obtain ⟨φ⟩ := Tests.nonempty_equiv_prodIrr_zero x hd
  exact ⟨rfl, ((isCosocle_self (isIrreducible_ofChar _)).of_equiv (.refl _) φ).unique hc⟩

theorem rank_zero_case (𝔪 𝔫 : Multiset (Segment k)) (π₁ π₂ : IrrRep (GL (Fin 0) k)) (h₁ : IsL 𝔪 π₁.ρ)
    (h₂ : IsL 𝔫 π₂.ρ) : (∃ π : IrrRep (GL (Fin (0 + 0)) k), IsL (𝔪 + 𝔫) π.ρ) ∧
      ∀ π : IrrRep (GL (Fin (0 + 0)) k), IsL (𝔪 + 𝔫) π.ρ → jhMult π.ρ (prod₂ π₁.ρ π₂.ρ) = 1 := by
  obtain ⟨rfl, ⟨a⟩⟩ := isL_rank_zero h₁
  obtain ⟨rfl, ⟨b⟩⟩ := isL_rank_zero h₂
  refine ⟨⟨π₁, h₁⟩, fun π h => ?_⟩
  obtain ⟨-, ⟨c⟩⟩ := isL_rank_zero h
  obtain ⟨φ⟩ := nonempty_equiv_parInd_zero (two (stdSum (rfl : 0 + 0 = 0 + 0)))
    ((extTensor π₁.ρ π₂.ρ).comp (leviTwo k _ _).symm.toMonoidHom)
    ((TensorProduct.lid ℂ ℂ).symm.trans (TensorProduct.congr a.symm.toLinearEquiv b.symm.toLinearEquiv))
  have h1 := jhMult_congr_right (detRep (Fin 0) (1 : kˣ →* ℂˣ)) φ
  rw [jhMult_self (σ := detRep (Fin 0) (1 : kˣ →* ℂˣ)) (isIrreducible_ofChar _)] at h1
  exact (jhMult_congr_left c _).trans h1.symm

end GlobalTheory.Published.LanglandsSumTests

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsIrrWDLpZero
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.Whittaker GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.LocLanglands.LocalLanglandsExistence₂

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem exists_place (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) :
    ∃ A : ValuationSubring (AlgebraicClosure E), IsPlaceOver A w :=
  ⟨_, isPlaceOver_placeOf _ w⟩

theorem localLanglandsExists_of_localLanglandsGL (H : GlobalTheory.Published.LocalLanglandsGL) : GlobalTheory.Published.LocalLanglandsExists :=
  fun E Ω _ _ _ _ _ A w h => let ⟨rc, hrc, _⟩ := H.1 E Ω A w h; ⟨rc, hrc.toLit⟩

theorem eq_lpZero {x : WD h} (hx : x.lpDim = 0) : x = WD.lpZero h := by
  obtain ⟨n, a, rfl⟩ := x.exists_rep
  obtain rfl : n = 0 := by simpa using hx
  exact WD.sound ⟨.refl _ _, fun _ _ => Subsingleton.elim _ _, fun _ => Subsingleton.elim _ _⟩

theorem not_isIrrWD_lpZero : ¬ IsIrrWD (WD.lpZero h) := by
  rintro ⟨n, a, ha, hi⟩
  have h0 := congrArg WD.lpDim ha
  obtain rfl : n = 0 := by simpa [WD.lpZero] using h0
  have : Nontrivial (Subrepresentation a.ρ) := hi.toNontrivial
  obtain ⟨S, T, hST⟩ := exists_pair_ne (Subrepresentation a.ρ)
  exact hST (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem eps_tensor_zero {ε : EpsFamily A} (hε : IsDeligneEps ε) (ψ : AddChar (w.adicCompletion E) Circle)
    (hψ : Continuous ψ) (hψ' : ψ ≠ 1) (x y : WD h) (hy : y.lpDim = 0) : ε E w h ψ (x.lpChar y) = 1 := by
  have h1 : (x.lpChar y).lpDim = 0 := by
    obtain ⟨n, a, rfl⟩ := x.exists_rep
    obtain ⟨m, b, rfl⟩ := y.exists_rep
    obtain rfl : m = 0 := by simpa using hy
    simp
  have h2 : ((x.lpChar y).lpSum (x.lpChar y)).lpDim = 0 := by
    obtain ⟨n, a, ha⟩ := (x.lpChar y).exists_rep
    rw [← ha] at h1 ⊢
    obtain rfl : n = 0 := by simpa using h1
    simp
  have h3 := hε.add E w h ψ hψ hψ' (x.lpChar y) (x.lpChar y)
  rw [(eq_lpZero h2).trans (eq_lpZero h1).symm] at h3
  exact (mul_eq_left.1 h3.symm)

theorem segSum_single (rc : IrrGL (w.adicCompletion E) → WD h) (ρ : IrrGL (w.adicCompletion E)) (hρ : ρ.IsCusp) :
    segSum rc [Segment.single ρ hρ] = rc ρ := by
  obtain ⟨n, a, ha⟩ := (rc ρ).exists_rep
  show ((((rc ρ).lpTw ((((1 : ℕ) : ℝ) - 1) / 2)).lpChar (WD.lpSp h 1)).lpSum (WD.lpZero h)) = rc ρ
  rw [← ha, WD.lpTw_mk, WD.lpSp, WD.lpChar_mk, WD.lpZero, WD.lpSum_mk]
  refine WD.sound ⟨(LinearEquiv.prodUnique).trans ((TensorProduct.congr (.refl ℂ _)
    (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans (TensorProduct.rid ℂ _)), fun σ v => ?_, fun v => ?_⟩
  · obtain ⟨v, u⟩ := v
    show (TensorProduct.rid ℂ _) (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)
      (TensorProduct.map _ _ v)) = a.ρ σ ((TensorProduct.rid ℂ _)
        (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ) v))
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [WDRep.spEig, coe_qPow]
    | add x y hx hy => simp only [map_add, hx, hy]
  · obtain ⟨v, u⟩ := v
    show (TensorProduct.rid ℂ _) (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)
      (((a.tw ((((1 : ℕ) : ℝ) - 1) / 2)).tensor (WDRep.sp h 1)).N v)) = a.N ((TensorProduct.rid ℂ _)
        (TensorProduct.congr (.refl ℂ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ) v))
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [shiftEnd_apply]
    | add x y hx hy => simp only [map_add, hx, hy]

theorem frobEig_unr {rc : IrrGL (w.adicCompletion E) → WD h} (H : IsRecLit h rc) (c : ℂˣ)
    (hc : IsSmoothChar (SmGL.unrChar (w.adicCompletion E) c)) :
    (rc (.ofChar _ hc)).frobEig = {((c⁻¹ : ℂˣ) : ℂ)} := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  rw [H.one]
  have : WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp a) (ha.smooth hc) =
      WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹) := by
    simp only [WD.lpOfChar, WDRep.diag, ha.unrChar_comp]
  rw [this, WD.frobEig_diag]
  rfl

theorem not_const (y : WD h) : ¬ IsRecLit h fun _ => y := by
  rintro ⟨a, ha, ε, -, H⟩
  obtain ⟨_, h0⟩ := H.bij.2 (WD.lpSp h 0)
  obtain ⟨_, h1⟩ := H.bij.2 (WD.lpSp h 1)
  have := congrArg WD.lpDim (h0.symm.trans h1)
  simp at this

end GlobalTheory.LocLanglands.LocalLanglandsExistence₂

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PstAndWdAtOfIsRegAlg
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

def GlobalTheory.Published.LocalGlobalAboveLPst : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 2 ≤ a →
    ∀ π : CuspSub E a, π.IsCsd → GKCoh.IsCohomological π →
    ∀ (r : G E Ω →* GL (Fin a) (Qbar l)) (wt : ℤ) (HT : (E →+* Qbar l) → Multiset ℤ),
      IsGalRepOf π (quadChar E ^ a) ι r wt HT →
    ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w)
      (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
      (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw),
      IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
        wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ)

section

variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} {a : ℕ} {π : CuspSub E a}
  {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ} {HT : (E →+* Qbar l) → Multiset ℤ}
  {P : LocPrime l} {AI : LocAinf l P} {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]

theorem GlobalTheory.GalOfCusp.IsGalRepOf.isPstAt {χ : HChar (maximalRealSubfield E)} (hG : IsGalRepOf π χ ι r wt HT)
    (hB : GlobalTheory.Published.DeRhamPotSemistable) (T : LocTied l P AI) (h : IsPlaceOver A w)
    (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) :=
  hB.isPstAt T Bw _ (Units.continuous_val.comp (hG.cont.comp continuous_subtype_val))
    (hG.above P AI ⟨T⟩ w A h O Bw hj).deRham

theorem GlobalTheory.Published.LocalGlobalAboveL.pst_and_wdAt (H : GlobalTheory.Published.LocalGlobalAboveL) (hB : GlobalTheory.Published.DeRhamPotSemistable)
    (ha : 2 ≤ a) (hc : π.IsCsd) (hcoh : GKCoh.IsCohomological π) (hG : IsGalRepOf π (quadChar E ^ a) ι r wt HT)
    (T : LocTied l P AI) (h : IsPlaceOver A w) (Bw : LocBridge l E Ω (Dec (F := E) A) O) (hj : Pst.Induces Bw) :
    IsPstAt P Bw (r.comp (Dec (F := E) A).subtype) ∧ ∀ σ, π.IsLocComp w σ → ∀ rc, IsRec h rc →
      wdAt P ι Bw h hj (r.comp (Dec (F := E) A).subtype) = rc (algNorm σ) :=
  ⟨hG.isPstAt hB T h Bw hj, H E Ω l ι a ha π hc hcoh r wt HT hG P AI ⟨T⟩ w A h O Bw hj⟩

end

theorem GlobalTheory.Published.LocalGlobalAboveL.regAlg (H : GlobalTheory.Published.LocalGlobalAboveL) (hC : GlobalTheory.Published.RegularAlgebraicPurity) :
    GlobalTheory.GalOfCusp.LocalGlobalAboveL :=
  fun E Ω _ _ _ _ _ _ l _ ι a ha π hc hr r wt HT hG P AI hT w _ A h O _ _ _ Bw hj σ hσ rc hrc =>
    H E Ω l ι a ha π hc (hC E a (by omega) π hr).2 r wt HT hG P AI hT w A h O Bw hj σ hσ rc hrc

theorem GlobalTheory.Published.LocalGlobalAboveLPst.of_classicalTheorems (H : GlobalTheory.Published.LocalGlobalAboveL) (hB : GlobalTheory.Published.DeRhamPotSemistable) :
    GlobalTheory.Published.LocalGlobalAboveLPst :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ ha _ hc hcoh _ _ _ hG _ _ ⟨T⟩ _ _ h _ _ _ _ Bw hj => H.pst_and_wdAt hB ha hc hcoh hG T h Bw hj

theorem GlobalTheory.Published.LocalGlobalAboveLPst.localGlobalAboveL (H : GlobalTheory.Published.LocalGlobalAboveLPst) :
    GlobalTheory.Published.LocalGlobalAboveL :=
  fun E Ω _ _ _ _ _ _ l _ ι a ha π hc hcoh r wt HT hG P AI hT w A h O _ _ _ Bw hj =>
    (H E Ω l ι a ha π hc hcoh r wt HT hG P AI hT w A h O Bw hj).2

end
end

