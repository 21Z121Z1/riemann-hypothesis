import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.NotIsTemperedGLDetRepTwo
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Formalism.SharpRestriction.LevelLetterCocycles.WildPro

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.DegOneOfChar
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem deg_one_ofChar (x : IrrGL (w.adicCompletion E)) (hx : x.1 = 1) :
    ∃ (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ), x = IrrGL.ofChar χ hχ :=
  GlobalTheory.LocGL.TemperedTests.exists_eq_ofChar x hx

end PositivityTheory.LocalParametersCuspidal.DZC

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.FixedOfCharNeBotIff
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem mem_fixed_iff' {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ u ∈ K, ρ u v = v := by
  show (∀ h : K, ρ (h : G) v = (((1 : K →* ℂˣ) h : ℂˣ) : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul, Subtype.forall]

theorem fixed_ne_bot_of_equiv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (K : Subgroup G)
    (hf : fixed ρ K ≠ ⊥) : fixed σ K ≠ ⊥ := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hf
  refine (Submodule.ne_bot_iff _).2 ⟨e v, mem_fixed_iff'.2 fun u hu => ?_, ?_⟩
  · have h1 : e (ρ u v) = σ u (e v) := LinearMap.congr_fun (e.toIntertwiningMap.isIntertwining' u) v
    rw [mem_fixed_iff'.1 hv u hu] at h1
    exact h1.symm
  · intro h0
    apply hv0
    have := congrArg e.symm h0
    rwa [Representation.Equiv.symm_apply_apply, map_zero] at this

theorem fixed_ofChar_ne_bot_iff {G : Type} [Group G] (ψ : G →* ℂˣ) (K : Subgroup G) :
    fixed (GlobalTheory.SmGL.ofChar ψ) K ≠ ⊥ ↔ ∀ u ∈ K, ψ u = 1 := by
  constructor
  · intro hf u hu
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hf
    have h1 := mem_fixed_iff'.1 hv u hu
    rw [GlobalTheory.SmGL.ofChar_apply] at h1
    have h2 : ((ψ u : ℂˣ) : ℂ) = 1 := by
      have h3 : (((ψ u : ℂˣ) : ℂ) - 1) * v = 0 := by rw [sub_mul, h1, one_mul, sub_self]
      exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hv0)
    exact Units.ext h2
  · intro H
    refine (Submodule.ne_bot_iff _).2 ⟨1, mem_fixed_iff'.2 fun u hu => ?_, one_ne_zero⟩
    rw [GlobalTheory.SmGL.ofChar_apply, H u hu]
    simp

theorem val_lt_one_iff (x : w.adicCompletion E) :
    ValuativeRel.valuation (w.adicCompletion E) x < 1 ↔ Valued.v x < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  rw [← Valuation.vlt_one_iff, ← Valuation.vlt_one_iff]

theorem ofChar_fixed_iff (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : IsSmoothChar χ) :
    fixed (IrrGL.ofChar χ hχ : IrrGL (w.adicCompletion E)).rep
        (KOne (w.adicCompletion E) (Fin (IrrGL.ofChar χ hχ : IrrGL (w.adicCompletion E)).1)) ≠ ⊥ ↔
      ∀ u : (w.adicCompletion E)ˣ, Valued.v ((u : w.adicCompletion E) - 1) < 1 → χ u = 1 := by
  let e : (IrrRep.det (Fin 1) χ hχ).ρ.Equiv (IrrRep.det (Fin 1) χ hχ).cl.rep.ρ := equivRep _
  have key : fixed (IrrGL.ofChar χ hχ : IrrGL (w.adicCompletion E)).rep
        (KOne (w.adicCompletion E) (Fin (IrrGL.ofChar χ hχ : IrrGL (w.adicCompletion E)).1)) ≠ ⊥ ↔
      fixed (GlobalTheory.SmGL.ofChar (detChar (Fin 1) χ)) (KOne (w.adicCompletion E) (Fin 1)) ≠ ⊥ :=
    ⟨fixed_ne_bot_of_equiv e.symm _, fixed_ne_bot_of_equiv e _⟩
  rw [key, fixed_ofChar_ne_bot_iff]
  constructor
  · intro H u hu
    obtain ⟨g, hg, hgv⟩ := GlobalTheory.StepData.exists_mem_KOne (k := w.adicCompletion E) (n := Fin 1)
      (M := Matrix.of fun _ _ => (u : w.adicCompletion E)) (fun i j => by
        rw [Subsingleton.elim j i, Matrix.sub_apply, Matrix.one_apply_eq, Matrix.of_apply]
        exact (val_lt_one_iff _).2 hu)
    have hd : Matrix.GeneralLinearGroup.det g = u := by
      ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, Matrix.det_unique, Matrix.of_apply]
    have := H g hg
    rwa [detChar_apply, hd] at this
  · intro H g hg
    rw [detChar_apply]
    exact GlobalTheory.StepData.tame_det_of_mem_KOne (fun x hx => H x ((val_lt_one_iff _).1 hx)) hg

end PositivityTheory.LocalParametersCuspidal.DZC

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.IsLevelOne
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Whittaker

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsLevelOne (ψ : AddChar k Circle) : Prop := ∃ c : kˣ, HasConductor ψ c ∧ ord k c = 1

def PTau {m : ℕ} (ψ' : AddChar k Circle) (τ : IrrRep (GL (Fin m) k)) : Prop :=
  (∃ ω : kˣ →* ℂˣ, HasCentralChar τ.ρ ω) ∧
    ∃ v' ∈ fixed τ.ρ (KOne k (Fin m)), ∃ l' : Module.Dual ℂ τ.V, IsFunctional ψ' τ.ρ l' ∧ l' v' ≠ 0

end Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

def unrPar (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a)
    (μ : {μ : (w.adicCompletion E)ˣ →* ℂˣ // IsUnram μ}) : WD h :=
  WD.lpOfChar h (μ.1.comp a) (ha.smooth (isSmoothChar_of_isUnram μ.2))

end PositivityTheory.LocalParametersCuspidal.DepthZeroGlueing

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.LeviInductionForms
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

theorem val_sub_one_lt_of_pow {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    {p : ℕ} (hp : p.Prime) (hpv : v (p : K) < 1) {x : K} {k : ℕ} (hx : v (x ^ p ^ k - 1) < 1) :
    v (x - 1) < 1 := by
  have hN : p ^ k ≠ 0 := pow_ne_zero _ hp.ne_zero
  have h1 : v (x ^ p ^ k) = 1 := by
    have := Valuation.map_one_add_of_lt v hx
    rwa [add_sub_cancel] at this
  have hx1 : v x ≤ 1 := by
    refine le_of_not_gt fun hc => ?_
    have : 1 < v x ^ p ^ k := one_lt_pow₀ hc hN
    rw [← map_pow, h1] at this
    exact lt_irrefl _ this
  have hy : v (x - 1) ≤ 1 :=
    (Valuation.map_sub v x 1).trans (max_le hx1 (by rw [map_one]))
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp (⟨x - 1, hy⟩ : v.integer) (1 : v.integer) k
  have hr' : x ^ p ^ k = (x - 1) ^ p ^ k + 1 + (p : K) * (x - 1) * (r : K) := by
    have := congrArg (fun z : v.integer => (z : K)) hr
    simp only [Subring.coe_add, Subring.coe_pow, Subring.coe_mul, Subring.coe_natCast, OneMemClass.coe_one,
      one_pow, mul_one, sub_add_cancel] at this
    exact this
  have hr1 : v (r : K) ≤ 1 := r.2
  have e : (x - 1) ^ p ^ k = (x ^ p ^ k - 1) + -((p : K) * (x - 1) * (r : K)) := by
    rw [hr']; ring
  have hlt : v ((x - 1) ^ p ^ k) < 1 := by
    rw [e]
    refine Valuation.map_add_lt v hx ?_
    rw [Valuation.map_neg, map_mul, map_mul]
    calc v (p : K) * v (x - 1) * v (r : K) ≤ v (p : K) * 1 * 1 := by gcongr
      _ < 1 := by rw [mul_one, mul_one]; exact hpv
  refine lt_of_not_ge fun hc => ?_
  have : 1 ≤ v (x - 1) ^ p ^ k := one_le_pow₀ hc
  rw [← map_pow] at this
  exact absurd hlt (not_lt.2 this)

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

omit [IsAlgClosure E Ω] in

theorem wildPf_of_isWild {σ : G E Ω} (hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A σ) : Formalism.MainNotions.N.KillingConditions.WildPf.IsWild A σ := by
  intro y hy
  have hv : A.valuation y ≠ 0 := by simpa using hy
  have e : σ y / y - 1 = (σ y - y) / y := by field_simp
  rw [e, map_div₀]
  exact (div_lt_one₀ (zero_lt_iff.2 hv)).2 (hσ.2 y hy)

theorem wild_to_unitsOne (a : Weil h →* (w.adicCompletion E)ˣ) (ha : IsLocalArtin h a) (σ : Weil h)
    (hσ : Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω)) : Valued.v ((a σ : w.adicCompletion E) - 1) < 1 := by
  obtain ⟨p, hp, hpw⟩ : ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : 𝓞 E) ∈ w.asIdeal :=
    ⟨_, GlobalTheory.LocalData.resChar_prime w, GlobalTheory.LocalData.resChar_mem w⟩
  have hpA : A.valuation ((p : ℕ) : Ω) < 1 := by
    have := (h ((p : ℕ) : 𝓞 E)).2 hpw
    simpa using this
  have hpv : Valued.v ((p : ℕ) : w.adicCompletion E) < 1 := by
    have h1 := (w.valuation_lt_one_iff_mem (K := E) ((p : ℕ) : 𝓞 E)).2 hpw
    have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (K := E) w ((p : ℕ) : E)
    simp only [map_natCast] at h1
    have h3 : ((p : ℕ) : w.adicCompletion E) = (((p : ℕ) : E) : w.adicCompletion E) :=
      (map_natCast (algebraMap E (w.adicCompletion E)) p).symm
    rw [h3, h2]; exact h1
  set U : Set (w.adicCompletion E)ˣ := {u | Valued.v ((u : w.adicCompletion E) - 1) < 1} with hUdef
  have hU : U ∈ nhds (1 : (w.adicCompletion E)ˣ) := by
    have h0 : {x : w.adicCompletion E | Valued.v (x - 1) < 1} ∈
        nhds ((1 : (w.adicCompletion E)ˣ) : w.adicCompletion E) := by
      rw [Valued.mem_nhds]
      exact ⟨1, fun y hy => by simpa [Valuation.restrict_lt_one_iff] using hy⟩
    exact Units.continuous_val.continuousAt.preimage_mem_nhds h0
  have hV : (fun τ : Ine (F := E) A => a (ineIncl h τ)) ⁻¹' U ∈ nhds (1 : Ine (F := E) A) := by
    refine ha.cont.continuousAt.preimage_mem_nhds ?_
    simpa using hU
  obtain ⟨O, hO, hOs⟩ := (mem_nhds_induced Subtype.val (1 : Ine (F := E) A) _).1 hV
  rw [OneMemClass.coe_one] at hO
  obtain ⟨L, hL, hLO⟩ := (krullTopology_mem_nhds_one_iff E Ω O).1 hO
  obtain ⟨k, hk⟩ := Formalism.MainNotions.N.KillingConditions.WildPf.wildProP E Ω A p hp hpA (σ : G E Ω) (wildPf_of_isWild hσ)
    L.fixingSubgroup (IntermediateField.fixingSubgroup_isOpen L)
  have hτ : (σ : G E Ω) ^ (p ^ k) ∈ Ine (F := E) A := (Ine (F := E) A).pow_mem hσ.1 _
  have hmem := hOs (show ((⟨_, hτ⟩ : Ine (F := E) A) : G E Ω) ∈ O from hLO hk)
  have e : ineIncl h (⟨_, hτ⟩ : Ine (F := E) A) = σ ^ (p ^ k) := Subtype.ext (by simp)
  simp only [Set.mem_preimage, e, map_pow, hUdef, Set.mem_ofPred_eq, Units.val_pow_eq_pow_val] at hmem
  exact val_sub_one_lt_of_pow Valued.v hp hpv hmem

end PositivityTheory.LocalParametersCuspidal.DZC

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.DepthZeroCuspidal.TameLpOfCharIff
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.LocalParametersCuspidal.DZC

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem tame_lpOfChar_iff (ξ : Weil h →* ℂˣ) (hξ : IsSmooth ξ) :
    IsTameWD (WD.lpOfChar h ξ hξ) ↔ ∀ σ : Weil h, Formalism.MainNotions.BlochKatoReduction.IsWild A (σ : G E Ω) → ξ σ = 1 := by
  constructor
  · rintro ⟨n, a, ha, H⟩ σ hσ
    unfold WD.lpOfChar at ha
    obtain ⟨e, he, -⟩ := WD.mk_eq_mk.mp ha
    have h1 : ∀ u : Fin 1 → ℂ,
        (WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) fun _ => hξ).ρ σ u = u := by
      intro u
      obtain ⟨v, rfl⟩ := e.surjective u
      rw [← he, H σ hσ]
      rfl
    have h2 := congrFun (h1 fun _ => 1) 0
    rw [WDRep.ofChars_ρ, diagEnd_apply, mul_one] at h2
    exact Units.ext h2
  · intro H
    refine ⟨1, WDRep.ofChars h (ι := Fin 1) (fun _ => ξ) (fun _ => hξ), rfl, fun σ hσ => ?_⟩
    refine LinearMap.ext fun v => funext fun i => ?_
    rw [WDRep.ofChars_ρ, diagEnd_apply, H σ hσ]
    simp

end PositivityTheory.LocalParametersCuspidal.DZC

end
end

