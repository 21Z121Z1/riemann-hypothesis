import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0051
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroCuspidalLL
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def DepthZeroCuspidalLL : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (w.adicCompletion E) → WD h), IsRecLit h rc →
    ∀ x : IrrGL (w.adicCompletion E), x.IsCusp →
      (fixed x.rep (KOne (w.adicCompletion E) (Fin x.1)) ≠ ⊥ ↔ IsTameWD (rc x))

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsSpehOfOfIsQuotOf
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DiscSpec.ByClassModel

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ}

variable (E N) in

def Clauses : Prop :=
  (∃ J : (a : ℕ) → CuspSub E a → ℕ → Submodule ℂ (Sm E N),
      (∀ (a d : ℕ) (π : CuspSub E a), d * a = N → π.IsUnitary → IsNormalised π →
        GlobalTheory.UnitaryBC.IsDiscrete (J a π d) ∧ IsSpehOf (J a π d) π d) ∧
      ∀ V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V →
        V ≤ ⨆ (a : ℕ) (d : ℕ) (π : CuspSub E a) (_ : d * a = N ∧ π.IsUnitary ∧ IsNormalised π), J a π d) ∧
    (∀ V V' : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V → GlobalTheory.UnitaryBC.IsDiscrete V' →
      ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → IsSpehOf V' π d → IsIsoGL V V') ∧
    ∀ V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      π.IsUnitary → IsNormalised π → IsSpehOf V π d → ∀ w σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
        GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ

theorem byClass_iff : GlobalTheory.Published.ResidualSpectrumByClass ↔
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ), 1 ≤ N → Clauses E N := Iff.rfl

theorem clauses_of
    (h1 : ∀ V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V →
      ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d)
    (h2 : ∀ (a d : ℕ) (π : CuspSub E a), d * a = N → IsNormalised π →
      ∃! V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V ∧ IsSpehOf V π d)
    (h5 : ∀ V : Submodule ℂ (Sm E N), GlobalTheory.UnitaryBC.IsDiscrete V → ∀ (a d : ℕ) (π : CuspSub E a),
      IsNormalised π → IsSpehOf V π d → ∀ w, (∃ σ σ', π.IsLocComp w σ ∧ IsLocCompGL V w σ') ∧
        ∀ σ σ', π.IsLocComp w σ → IsLocCompGL V w σ' →
          GlobalTheory.LocGL.IsSpeh (GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred) d σ'.ρ) : Clauses E N := by
  classical
  refine ⟨⟨fun a π d => if h : d * a = N ∧ IsNormalised π then (h2 a d π h.1 h.2).exists.choose else ⊥,
    fun a d π h _ hn => ?_, fun V hV => ?_⟩, fun V V' hV hV' a d π _ hn e e' => ?_,
    fun V hV a d π _ hn e w => (h5 V hV a d π hn e w).2⟩
  · simp only [dif_pos (And.intro h hn)]
    exact (h2 a d π h hn).exists.choose_spec
  · obtain ⟨a, d, π, hu, hn, e⟩ := h1 V hV
    refine le_iSup_of_le a (le_iSup_of_le d (le_iSup_of_le π (le_iSup_of_le ⟨e.mul_eq, hu, hn⟩ ?_)))
    simp only [dif_pos (And.intro e.mul_eq hn)]
    exact ((h2 a d π e.mul_eq hn).unique ⟨hV, e⟩ (h2 a d π e.mul_eq hn).exists.choose_spec).le
  · obtain rfl := (h2 a d π e.mul_eq hn).unique ⟨hV, e⟩ ⟨hV', e'⟩
    exact ⟨.refl _ _, fun _ _ _ h => h⟩

theorem of_residual (H : GlobalTheory.Published.DiscreteSpectrumResidual) : GlobalTheory.Published.ResidualSpectrumByClass :=
  fun E _ _ _ N hN => let ⟨h1, h2, _, _, h5⟩ := H E N hN; clauses_of h1 h2 h5

theorem clauses_one : Clauses E 1 :=
  let ⟨h1, h2, _, _, h5⟩ := ResidualModel.residual_one E; clauses_of h1 h2 h5

section Algebra

variable {M O : Type} [AddCommGroup M] [Module ℂ M] (A : O → Module.End ℂ M)

theorem apply_mem_of_stable {V : Submodule ℂ M} (hV : ∀ o, ∀ φ ∈ V, A o φ ∈ V) {z : Module.End ℂ M}
    (hz : z ∈ Algebra.adjoin ℂ (Set.range A)) : ∀ φ ∈ V, z φ ∈ V := by
  induction hz using Algebra.adjoin_induction with
  | mem x hx => obtain ⟨o, rfl⟩ := hx; exact hV o
  | algebraMap c => exact fun φ hφ => by simpa using V.smul_mem c hφ
  | add x y _ _ hx hy => exact fun φ hφ => add_mem (hx φ hφ) (hy φ hφ)
  | mul x y _ _ hx hy => exact fun φ hφ => hx _ (hy φ hφ)

def toOp (V : Submodule ℂ M) (hV : ∀ o, ∀ φ ∈ V, A o φ ∈ V) : Submodule (Algebra.adjoin ℂ (Set.range A)) M where
  toAddSubmonoid := V.toAddSubmonoid
  smul_mem' z φ hφ := apply_mem_of_stable A hV z.2 φ hφ

def IsIrr (V : Submodule ℂ M) : Prop :=
  (∀ o, ∀ φ ∈ V, A o φ ∈ V) ∧ V ≠ ⊥ ∧ ∀ W ≤ V, (∀ o, ∀ φ ∈ W, A o φ ∈ W) → W = ⊥ ∨ W = V

theorem isSimpleModule_toOp {V : Submodule ℂ M} (hV : IsIrr A V) :
    IsSimpleModule (Algebra.adjoin ℂ (Set.range A)) (toOp A V hV.1) := by
  refine isSimpleModule_iff_isAtom.2 ⟨fun h => hV.2.1 (eq_bot_iff.2 fun φ hφ => h.le hφ), fun W hW => ?_⟩
  rcases hV.2.2 (W.restrictScalars ℂ) (fun φ hφ => hW.le hφ) (fun o φ hφ =>
    W.smul_mem (⟨A o, Algebra.subset_adjoin ⟨o, rfl⟩⟩ : Algebra.adjoin ℂ (Set.range A)) hφ) with h | h
  · exact eq_bot_iff.2 fun φ hφ => h.le hφ
  · exact absurd (fun φ hφ => h.ge hφ) hW.not_ge

theorem exists_map_eq {s : Set (Submodule ℂ M)} (hs : ∀ J ∈ s, IsIrr A J) {V : Submodule ℂ M} (hV : IsIrr A V)
    (hle : V ≤ sSup s) : ∃ J ∈ s, ∃ g : M →ₗ[ℂ] M, J.map g = V ∧ ∀ o, ∀ φ ∈ J, g (A o φ) = A o (g φ) := by
  let t : Set (Submodule (Algebra.adjoin ℂ (Set.range A)) M) := {S | ∃ (J : _) (h : J ∈ s), S = toOp A J (hs J h).1}
  haveI : ∀ m : t, IsSimpleModule (Algebra.adjoin ℂ (Set.range A)) m := by
    rintro ⟨_, J, h, rfl⟩
    exact isSimpleModule_toOp A (hs J h)
  haveI := isSimpleModule_toOp A hV
  have ht : toOp A V hV.1 ≤ sSup t := fun φ hφ => by
    have : sSup s ≤ (sSup t).restrictScalars ℂ := sSup_le fun J h ψ hψ =>
      (le_sSup (s := t) ⟨J, h, rfl⟩ : toOp A J (hs J h).1 ≤ _) hψ
    exact this (hle hφ)
  obtain ⟨_, ⟨J, hJ, rfl⟩, ⟨T⟩⟩ := (toOp A V hV.1).linearEquiv_of_le_sSup t ht
  replace T := T.symm
  let T₀ : J →ₗ[ℂ] M :=
    { toFun := fun φ => (T ⟨φ.1, φ.2⟩).1
      map_add' := fun φ ψ => congrArg Subtype.val (T.map_add ⟨φ.1, φ.2⟩ ⟨ψ.1, ψ.2⟩)
      map_smul' := fun c φ => congrArg Subtype.val ((T.toLinearMap.restrictScalars ℂ).map_smul c ⟨φ.1, φ.2⟩) }
  obtain ⟨g, hg⟩ := T₀.exists_extend
  have hg' : ∀ φ (hφ : φ ∈ J), g φ = (T ⟨φ, hφ⟩).1 := fun φ hφ => LinearMap.congr_fun hg ⟨φ, hφ⟩
  refine ⟨J, hJ, g, le_antisymm ?_ fun ψ hψ => ⟨(T.symm ⟨ψ, hψ⟩).1, (T.symm ⟨ψ, hψ⟩).2, ?_⟩, fun o φ hφ => ?_⟩
  · rintro _ ⟨φ, hφ, rfl⟩
    rw [hg' φ hφ]
    exact (T ⟨φ, hφ⟩).2
  · rw [hg' _ hφ, hg' _ ((hs J hJ).1 o φ hφ)]
    exact congrArg Subtype.val
      (T.map_smul (⟨A o, Algebra.subset_adjoin ⟨o, rfl⟩⟩ : Algebra.adjoin ℂ (Set.range A)) ⟨φ, hφ⟩)
  · rw [hg' _ (T.symm ⟨ψ, hψ⟩).2]
    exact congrArg Subtype.val (T.apply_symm_apply ⟨ψ, hψ⟩)

end Algebra

theorem isSpehOf_of_isQuotOf {V V' : Submodule ℂ (Sm E N)} (hq : IsQuotOf V' V) {a d : ℕ} {π : CuspSub E a}
    (h : IsSpehOf V π d) : IsSpehOf V' π d := by
  obtain ⟨h, ν, hν, f, hf, hc⟩ := h
  obtain ⟨g, hg, hd⟩ := hq
  refine ⟨h, ν, hν, g ∘ₗ f, by rw [Submodule.map_comp, hf, hg], fun o φ hφ => ?_⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hc o φ hφ, hd o _ (hf ▸ Submodule.mem_map_of_mem hφ)]

theorem exhaustion (H : Clauses E N) {V : Submodule ℂ (Sm E N)} (hV : GlobalTheory.UnitaryBC.IsDiscrete V) :
    ∃ (a d : ℕ) (π : CuspSub E a), π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π d := by
  obtain ⟨⟨J, hJ, hle⟩, -⟩ := H
  obtain ⟨_, ⟨a, d, π, h, hu, hn, rfl⟩, hq⟩ := exists_map_eq (act (E := E) (a := N))
    (s := {S | ∃ (a d : ℕ) (π : CuspSub E a), d * a = N ∧ π.IsUnitary ∧ IsNormalised π ∧ S = J a π d})
    (by
      rintro _ ⟨a, d, π, h, hu, hn, rfl⟩
      have := (hJ a d π h hu hn).1
      exact ⟨this.stable, this.ne_bot, this.irred⟩) ⟨hV.stable, hV.ne_bot, hV.irred⟩
    ((hle V hV).trans (iSup_le fun a => iSup_le fun d => iSup_le fun π => iSup_le fun h =>
      le_sSup ⟨a, d, π, h.1, h.2.1, h.2.2, rfl⟩))
  exact ⟨a, d, π, hu, hn, isSpehOf_of_isQuotOf hq (hJ a d π h hu hn).2⟩

theorem exists_hyp : ∃ (V : Submodule ℂ (Sm E 1)) (π : CuspSub E 1),
    GlobalTheory.UnitaryBC.IsDiscrete V ∧ π.IsUnitary ∧ IsNormalised π ∧ IsSpehOf V π 1 :=
  let ⟨V, π, h1, h2, h3⟩ := Model.exists_discrete_speh (E := E)
  ⟨V, π, h1, Model.isUnitary_of_isNormalised h2, h2, h3⟩

end GlobalTheory.DiscSpec.ByClassModel

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LanglandsSumMultiplicityOne
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

namespace GlobalTheory.Published

def LanglandsSumMultiplicityOne : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (𝔪 𝔫 : Multiset (Segment k)) (r t : ℕ) (π₁ : IrrRep (GL (Fin r) k)) (π₂ : IrrRep (GL (Fin t) k)),
    IsL 𝔪 π₁.ρ → IsL 𝔫 π₂.ρ →
      (∃ π : IrrRep (GL (Fin (r + t)) k), IsL (𝔪 + 𝔫) π.ρ) ∧
        ∀ π : IrrRep (GL (Fin (r + t)) k), IsL (𝔪 + 𝔫) π.ρ → jhMult π.ρ (prod₂ π₁.ρ π₂.ρ) = 1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
  {𝔪 𝔫 : Multiset (Segment k)} {r t : ℕ} {π₁ : IrrRep (GL (Fin r) k)} {π₂ : IrrRep (GL (Fin t) k)}

theorem LanglandsSumMultiplicityOne.isSubquotient (H : LanglandsSumMultiplicityOne) (h₁ : IsL 𝔪 π₁.ρ) (h₂ : IsL 𝔫 π₂.ρ)
    {π : IrrRep (GL (Fin (r + t)) k)} (h : IsL (𝔪 + 𝔫) π.ρ) : IsSubquotient π.ρ (prod₂ π₁.ρ π₂.ρ) :=
  JHMult.jhMult_ne_zero_iff.1 (by rw [(H k 𝔪 𝔫 r t π₁ π₂ h₁ h₂).2 π h]; exact one_ne_zero)

theorem LanglandsSumMultiplicityOne.isL_prod₂ (H : LanglandsSumMultiplicityOne) (h₁ : IsL 𝔪 π₁.ρ) (h₂ : IsL 𝔫 π₂.ρ)
    (hi : (prod₂ π₁.ρ π₂.ρ).IsIrreducible) : IsL (𝔪 + 𝔫) (prod₂ π₁.ρ π₂.ρ) := by
  obtain ⟨π, h⟩ := (H k 𝔪 𝔫 r t π₁ π₂ h₁ h₂).1
  obtain ⟨φ⟩ := (H.isSubquotient h₁ h₂ h).nonempty_equiv π.irr hi
  exact h.of_equiv φ.symm

omit [CharZero k] in

example {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) :
    ∃ (𝔪 𝔫 : Multiset (Segment k)) (π₁ π₂ : IrrRep (GL (Fin 1) k)) (π : IrrRep (GL (Fin (1 + 1)) k)),
      IsL 𝔪 π₁.ρ ∧ IsL 𝔫 π₂.ρ ∧ IsL (𝔪 + 𝔫) π.ρ ∧ π = IrrRep.det (Fin 2) _ (hχ.mul (isSmoothChar_absPow (1 / 2))) :=
  ⟨_, _, _, _, _, (single_spec (IrrGL.isCusp_ofChar χ hχ)).2.2.2,
    (single_spec ((IrrGL.isCusp_ofChar χ hχ).nu 1)).2.2.2, isL_detRep_two hχ, rfl⟩

end GlobalTheory.Published

namespace GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h}

theorem IsRec.segment (H : IsRec h rc) {Δ : Segment (w.adicCompletion E)} {x : IrrGL (w.adicCompletion E)}
    (hx : IsLSeg Δ x.rep) : rc x = ((rc Δ.first).lpTw (((Δ.len : ℝ) - 1) / 2)).lpChar (WD.lpSp h Δ.len) := by
  obtain ⟨a, ha, ε, -, H⟩ := H
  exact (H.langlands [Δ] x hx.isL).trans (WD.lpSum_zero _)

theorem IsRec.langlandsQuotient (H : IsRec h rc) {𝔪 : Multiset (Segment (w.adicCompletion E))} {s N : ℕ}
    {δ : Fin s → IrrGL (w.adicCompletion E)} (hδ : LFactors 𝔪 δ) (hd : ∑ i, (δ i).1 = N)
    {π : IrrRep (GL (Fin N) (w.adicCompletion E))} (hπ : IsCosocle π.ρ (prodIrr δ hd)) :
    rc (cls π) = sumList (List.ofFn fun i => rc (δ i)) := by
  have h1 : IsL 𝔪 (cls π).rep := IsL.of_equiv ⟨s, δ, hd, hδ, hπ⟩ (equivRep π)
  obtain ⟨Δ, ⟨hm, -⟩, hΔ⟩ := hδ
  simp only [fun i => H.segment (hΔ i)]
  obtain ⟨a, ha, ε, -, H⟩ := H
  rw [H.langlands (List.ofFn Δ) (cls π) (by rwa [← Fin.univ_val_map, hm]), List.map_ofFn]
  rfl

theorem IsRec.prod (H : IsRec h rc) {r t : ℕ} (σ : IrrRep (GL (Fin r) (w.adicCompletion E)))
    (τ : IrrRep (GL (Fin t) (w.adicCompletion E))) (π : IrrRep (GL (Fin (r + t)) (w.adicCompletion E)))
    (φ : π.ρ.Equiv (prod₂ σ.ρ τ.ρ)) : rc (cls π) = (rc (cls σ)).lpSum (rc (cls τ)) :=
  let ⟨_, _, _, _, H⟩ := H; H.prod r t σ τ π ⟨φ⟩

theorem IsRec.isSpherical_iff (H : IsRec h rc) (x : IrrGL (w.adicCompletion E)) : IsSpherical x.rep ↔ (rc x).unr :=
  let ⟨_, _, _, _, H⟩ := H; H.sph x

end GlobalTheory.LocLanglands

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalArtinExists
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalArtinExists : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalConstantsExist
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalConstantsExist : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver A w → ∃ ε : EpsFamily A, IsDeligneEps ε

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.LocalLanglandsExists
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.Published

open GlobalTheory.LocLanglands

def LocalLanglandsExists : Prop :=
  ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∃ rc : IrrGL (w.adicCompletion E) → WD h, IsRecLit h rc

end GlobalTheory.Published

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsSquareIntegrableOfTrivial
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel MeasureTheory

namespace GlobalTheory.UnitaryDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem subsingleton_quot_one : Subsingleton (GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)) := by
  rw [QuotientGroup.subsingleton_iff, eq_top_iff]
  intro g _
  rw [Subgroup.mem_center_iff]
  intro h
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [Matrix.mul_apply, mul_comm]

theorem isSquareIntegrable_one_iff (c : IrrCl (GL (Fin 1) k)) :
    IsSquareIntegrable (⟨1, c⟩ : IrrGL k) ↔ IsUnitarisable (IrrGL.rep ⟨1, c⟩) := by
  refine ⟨fun h => h.2.1, fun h => ⟨one_pos, h, ?_⟩⟩
  letI : MeasurableSpace (GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)) := borel _
  haveI : BorelSpace (GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)) := ⟨rfl⟩
  haveI := subsingleton_quot_one (k := k)
  refine ⟨Measure.haar, inferInstance, fun v ℓ _ => ?_⟩
  show ∫⁻ q : GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k), ‖ℓ (c.rep.ρ q.out v)‖ₑ ^ 2 ∂Measure.haar < ⊤
  have e : (fun q : GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k) => ‖ℓ (c.rep.ρ q.out v)‖ₑ ^ 2) =
      fun _ => ‖ℓ (c.rep.ρ (1 : GL (Fin 1) k ⧸ Subgroup.center (GL (Fin 1) k)).out v)‖ₑ ^ 2 :=
    funext fun q => by rw [Subsingleton.elim q 1]
  rw [e, lintegral_const]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top enorm_lt_top) isCompact_univ.measure_lt_top

theorem IsSquareIntegrable.isUnitarySpeh {δ : IrrGL k} (h : IsSquareIntegrable δ) : IsUnitarySpeh δ :=
  ⟨δ, 1, h, le_rfl, isSpeh_one δ⟩

theorem conclusion_one {π : Representation ℂ (GL (Fin 1) k) V} (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hu : IsUnitarisable π) :
    ∃ (u : List (IrrGL k)) (τ : List (IrrGL k × ℝ)), (∀ x ∈ u, IsUnitarySpeh x) ∧
      (∀ p ∈ τ, IsUnitarySpeh p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) ∧
      ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = 1), List.ofFn x = GenericUnitary.factors u τ ∧
        Nonempty (π.Equiv (prodIrr x hd)) := by
  have h : IsUnitarySpeh (IrrGL.of π hs hi) :=
    ((isSquareIntegrable_one_iff _).2
      (GenericUnitary.isUnitarisable_of_equiv (IrrGL.equivOf π hs hi) hu)).isUnitarySpeh
  have hd : ∑ _ : Fin 1, (IrrGL.of π hs hi).1 = (IrrGL.of π hs hi).1 := by simp
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (IrrGL.of π hs hi) hd
  exact ⟨[IrrGL.of π hs hi], [], by simpa using h, by simp, 1, fun _ => IrrGL.of π hs hi, hd, rfl,
    ⟨(IrrGL.equivOf π hs hi).trans ψ⟩⟩

theorem conclusion_zero {π : Representation ℂ (GL (Fin 0) k) V} (hi : π.IsIrreducible) :
    ∃ (u : List (IrrGL k)) (τ : List (IrrGL k × ℝ)), (∀ x ∈ u, IsUnitarySpeh x) ∧
      (∀ p ∈ τ, IsUnitarySpeh p.1 ∧ 0 < p.2 ∧ p.2 < 1 / 2) ∧
      ∃ (h : ℕ) (x : Fin h → IrrGL k) (hd : ∑ a, (x a).1 = 0), List.ofFn x = GenericUnitary.factors u τ ∧
        Nonempty (π.Equiv (prodIrr x hd)) := by
  obtain ⟨δ, τ, hδ, hτ, h, x, hd, hx, φ⟩ := GenericUnitary.isComplementaryProduct_zero hi
  obtain rfl : h = 0 := by
    by_contra h0
    let a : Fin h := ⟨0, Nat.pos_of_ne_zero h0⟩
    obtain ⟨y, s, hy, -, e⟩ := GenericUnitary.exists_of_mem_factors hδ hτ (y := x a) (hx ▸ List.mem_ofFn.2 ⟨a, rfl⟩)
    have h1 := (Finset.sum_eq_zero_iff.1 hd) a (Finset.mem_univ _)
    rw [e] at h1
    exact hy.deg_pos.ne' h1
  exact ⟨[], [], by simp, by simp, 0, x, hd, by simp [GenericUnitary.factors], φ⟩

theorem noncompactSpace_field : NoncompactSpace k := by
  let _ := IsTopologicalAddGroup.rightUniformSpace k
  have := isUniformAddGroup_of_addCommGroup (G := k)
  let _ : (Valued.v (R := k)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := k).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  exact NormedSpace.noncompactSpace k k

theorem noncompactSpace_quot_two : NoncompactSpace (GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k)) := by
  haveI := noncompactSpace_field (k := k)
  let f : GL (Fin 2) k → k := fun g => g.val 0 1 * (g⁻¹).val 1 1
  have hf : Continuous f := by
    refine Continuous.mul ?_ ?_
    · exact (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) k)).matrix_elem 0 1
    · exact (Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) k)).matrix_elem 1 1
  have hc : ∀ a b : GL (Fin 2) k, (QuotientGroup.leftRel (Subgroup.center (GL (Fin 2) k))) a b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.leftRel_apply, Matrix.GeneralLinearGroup.center_eq_range_scalar] at hab
    obtain ⟨z, hz⟩ := hab
    obtain rfl : b = a * Matrix.GeneralLinearGroup.scalar (Fin 2) z := by rw [hz]; simp
    simp only [f]
    rw [mul_inv_rev, ← map_inv, Units.val_mul, Units.val_mul]
    simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe, Matrix.scalar_apply,
      RingHom.toMonoidHom_eq_coe, Matrix.mul_diagonal, Matrix.diagonal_mul]
    rw [mul_assoc, Units.mul_inv_cancel_left]
  have hs : Function.Surjective f := fun x => by
    refine ⟨⟨!![1, x; 0, 1], !![1, -x; 0, 1], ?_, ?_⟩, ?_⟩
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    · show x * 1 = x
      exact mul_one x
  refine ⟨fun h => ?_⟩
  have := h.image (hf.quotient_lift hc)
  refine noncompact_univ k ?_
  convert this
  refine (Set.eq_univ_of_forall fun x => ?_).symm
  obtain ⟨g, rfl⟩ := hs x
  exact ⟨QuotientGroup.mk g, trivial, rfl⟩

theorem not_isSquareIntegrable_of_trivial (c : IrrCl (GL (Fin 2) k)) (L : c.rep.V ≃ₗ[ℂ] ℂ)
    (e : ∀ g w, L (c.rep.ρ g w) = L w) : ¬ IsSquareIntegrable (⟨2, c⟩ : IrrGL k) := by
  letI : MeasurableSpace (GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k)) := borel _
  haveI : BorelSpace (GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k)) := ⟨rfl⟩
  haveI := noncompactSpace_quot_two (k := k)
  have key : ∀ μ : Measure (GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k)), μ.IsHaarMeasure → μ Set.univ = ⊤ :=
    fun μ _ => measure_univ_of_isMulLeftInvariant μ
  rintro ⟨-, -, μ, hμ, H⟩
  have hs : L.toLinearMap ∈ smoothPart c.rep.ρ.dual := by
    change IsOpen {g | c.rep.ρ.dual g L.toLinearMap = L.toLinearMap}
    convert isOpen_univ
    exact Set.eq_univ_of_forall fun g => LinearMap.ext fun w => e g⁻¹ w
  have h : ∫⁻ q : GL (Fin 2) k ⧸ Subgroup.center (GL (Fin 2) k), ‖L (c.rep.ρ q.out (L.symm 1))‖ₑ ^ 2 ∂μ < ⊤ :=
    H (L.symm 1) _ hs
  simp only [e, L.apply_symm_apply, lintegral_const] at h
  rw [key μ hμ] at h
  simp at h

theorem not_isSquareIntegrable_one_two :
    ¬ IsSquareIntegrable (IrrGL.of (detRep (Fin 2) (1 : kˣ →* ℂˣ))
      ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar) (isIrreducible_ofChar _)) := by
  let φ := IrrGL.equivOf (detRep (Fin 2) (1 : kˣ →* ℂˣ))
      ((isSmooth_ofChar_iff _).2 isSmoothChar_one.detChar) (isIrreducible_ofChar _)
  refine not_isSquareIntegrable_of_trivial _ φ.symm.toLinearEquiv fun g w =>
    (φ.symm.toIntertwiningMap.isIntertwining _ _ g w).trans ?_
  exact (ofChar_apply (detChar (Fin 2) (1 : kˣ →* ℂˣ)) g _).trans (one_mul _)

theorem isUnitarySpeh_detRep_two {χ : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hu : IsUnitaryChar χ) :
    IsUnitarySpeh (IrrGL.of (detRep (Fin 2) χ) ((isSmooth_ofChar_iff _).2 hχ.detChar) (isIrreducible_ofChar _)) := by
  refine ⟨IrrGL.ofChar χ hχ, 2, (isSquareIntegrable_one_iff _).2 (GenericUnitary.isUnitarisable_of_equiv
    (equivRep (IrrRep.det (Fin 1) χ hχ)) ((isUnitarisable_ofChar_iff _).2 fun _ => hu _)), one_le_two, ?_⟩
  obtain ⟨hd, ⟨ψ⟩⟩ := ProjLine.exists_equiv_prodIrr (θ := ![χ * absPow k (1 / 2), χ * absPow k (-(1 / 2))])
    (Fin.forall_fin_two.2 ⟨hχ.mul (isSmoothChar_absPow _), hχ.mul (isSmoothChar_absPow _)⟩)
    (x := spehFactor (IrrGL.ofChar χ hχ) 2)
    (Fin.forall_fin_two.2 ⟨by
      rw [spehFactor, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]; norm_num, by
      rw [spehFactor, IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]; norm_num⟩)
    (Θ := (detLevi ProjLine.pts χ⁻¹)⁻¹) fun g => by
      rw [MonoidHom.inv_apply, detLevi_pts, Fin.prod_univ_two]
      simp [absPow_neg, mul_comm, mul_left_comm, mul_assoc]
  exact ⟨hd, (isCosocle_detRep_two hχ).of_equiv (IrrGL.equivOf _ _ _) ψ⟩

end GlobalTheory.UnitaryDual

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.SquareIntegrableSegment
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

namespace GlobalTheory.Published

def SquareIntegrableSegment : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (δ : IrrGL k), UnitaryDual.IsSquareIntegrable δ → ∃ Δ : Segment k, IsLSeg Δ δ.rep

end GlobalTheory.Published

end
end

