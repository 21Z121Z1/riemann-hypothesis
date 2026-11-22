import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Definitions.Foundations.EisValueAtIffEisPoleLE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0772
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsFactorisationCuspidal
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.AutMult
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
open Formalism.MainNotions.SchurIrreducible (Pl)
open GlobalTheory.PRep (IsAdmissible fixed)
open scoped InnerProductSpace

namespace GlobalTheory

namespace Flath

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

abbrev finFactor (R : ∀ v, IrrU (GPl σ J v)) (v : HeightOneSpectrum (𝓞 F)) :
    GLoc σ J v →* ((R (.inr v)).H →L[ℂ] (R (.inr v)).H) := (R (.inr v)).π

def IsUnramFactorisation {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (R : ∀ v, IrrU (GPl σ J v))
    (ξ : ∀ v, (R v).H) (π : GAd σ J →* (H →L[ℂ] H)) (B : (∀ v, (R v).H) → H) : Prop :=
  IsFactorisation σ J (fun v => (R v).π) ξ π B ∧
  (∀ v, (smRep (finFactor R v)).IsIrreducible ∧ IsAdmissible (smRep (finFactor R v))) ∧
  ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L →
    ∀ᶠ v in cofinite, fixed (toRep (finFactor R v)) (stabLoc σ J L v) = ℂ ∙ ξ (.inr v)

end Flath

namespace Published

def FlathFactorisation : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GAd σ J →* (H →L[ℂ] H)), IsIrrUnitary π →
        ∃ (R : ∀ v, IrrU (GPl σ J v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), Flath.IsUnramFactorisation R ξ π B

namespace FlathFactorisation

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {π : GAd σ J →* (H →L[ℂ] H)} {π' : GAd σ J →* (H' →L[ℂ] H')}

theorem isIsotypic_of_uEquiv {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    {δ : G →* (X →L[ℂ] X)} {ρ : G →* (H →L[ℂ] H)} {ρ' : G →* (H' →L[ℂ] H')} (e : UEquiv ρ ρ') (h : IsIsotypic δ ρ) :
    IsIsotypic δ ρ' := by
  obtain ⟨e, he⟩ := e
  refine eq_top_iff.2 fun y _ => ?_
  obtain ⟨x, rfl⟩ := e.surjective y
  have : isoPart δ ρ ⊤ ≤ (isoPart δ ρ' ⊤).comap (e.toLinearEquiv : H →ₗ[ℂ] H') :=
    isoPart_le ((Submodule.isClosed_topologicalClosure _).preimage e.continuous) fun T hT x =>
      apply_mem_isoPart (T := (e : H →L[ℂ] H') ∘L T)
        (mem_homIn_top.2 fun g x => (congrArg e (hT.2 g x)).trans (he g _)) x
  exact this (h.ge Submodule.mem_top)

theorem unique (hπ : IsIrrUnitary π) (e : UEquiv π' π) {R R' : ∀ v, IrrU (GPl σ J v)} {ξ : ∀ v, (R v).H}
    {ξ' : ∀ v, (R' v).H} {B : (∀ v, (R v).H) → H} {B' : (∀ v, (R' v).H) → H'}
    (h : IsFactorisation σ J (fun v => (R v).π) ξ π B) (h' : IsFactorisation σ J (fun v => (R' v).π) ξ' π' B')
    (v : Pl F) : UEquiv (R v).π (R' v).π :=
  haveI := hπ.complete
  haveI := hπ.irred.1
  IsIsotypic.uEquiv (R v).isIrr (R' v).isIrr (isUnitaryRep_comp hπ.unitary (continuous_embPl σ J v)) (h.hasCompPl v)
    (isIsotypic_of_uEquiv (e.comp _) (h'.hasCompPl v))

theorem exists_hasCompPl (h : FlathFactorisation) (hc : IsCMExt F E σ) (hJ : IsHermND σ J) (hπ : IsIrrUnitary π)
    (v : Pl F) : ∃ δ : IrrU (GPl σ J v), HasCompPl σ J v δ.π π :=
  let ⟨R, _, _, hR⟩ := h F E σ hc n J hJ H π hπ
  ⟨R v, hR.1.hasCompPl v⟩

end General

section Space

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exists_factorisation (h : FlathFactorisation) {π : GA D V →* (H →L[ℂ] H)} (hπ : IsIrrUnitary π) :
    ∃ (R : ∀ v, IrrU (GPl D.sp.cm.sig V.gram v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H),
      Flath.IsUnramFactorisation R ξ π B ∧
        ∀ᶠ v in cofinite, fixed (toRep (Flath.finFactor R v)) (Kv V v) = ℂ ∙ ξ (.inr v) :=
  let ⟨R, ξ, B, hR⟩ := h _ _ _ (isCMExt_host D) _ _ (GlobalTheory.Mem.VolExists.isHermND D.sp.cm V) H π hπ
  ⟨R, ξ, B, hR, hR.2.2 _ (SelfDual.isLattice_frameLat V)⟩

end Space

end FlathFactorisation

end Published

namespace Flath

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem smRep_charRep {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {χ : G →* Circle}
    (h : IsOpen (χ.ker : Set G)) : (smRep (charRep χ)).IsIrreducible ∧ IsAdmissible (smRep (charRep χ)) := by
  have ht : PRep.smoothPart (toRep (charRep χ)) = ⊤ := eq_top_iff.2 fun z _ => by
    refine isOpen_iff_mem_nhds.2 fun g hg => mem_of_superset
      ((h.preimage (continuous_const_mul g⁻¹)).mem_nhds (by simp)) fun x hx => ?_
    have e : χ x = χ g := by
      have : χ (g⁻¹ * x) = 1 := hx
      rw [map_mul, map_inv, inv_mul_eq_one] at this
      exact this.symm
    change (χ x : ℂ) • z = z
    rw [e]
    exact hg
  have h1 : Module.finrank ℂ (PRep.smoothPart (toRep (charRep χ))) = 1 := by rw [ht, finrank_top, Module.finrank_self]
  have := isSimpleModule_iff_finrank_eq_one.2 h1
  have hs : IsSimpleOrder (Submodule ℂ (PRep.smoothPart (toRep (charRep χ)))) := inferInstance
  have : Nontrivial (Subrepresentation (smRep (charRep χ))) :=
    ⟨⊥, ⊤, fun e => bot_ne_top (congrArg Subrepresentation.toSubmodule e :)⟩
  exact ⟨⟨fun S => (eq_bot_or_eq_top S.toSubmodule).imp (fun e => Subrepresentation.toSubmodule_injective e)
    fun e => Subrepresentation.toSubmodule_injective e⟩, isSmooth_smoothRep _, fun _ _ _ => inferInstance⟩

theorem isUnramFactorisation_charRep (χ : ∀ v, GPl σ J v →* Circle) (hχ : ∀ v, Continuous (χ v))
    (ho : ∀ v, IsOpen ((χ (.inr v)).ker : Set (GPl σ J (.inr v)))) (ψ : GAd σ J →* Circle)
    (h : ∀ g, ∀ᶠ v in cofinite, χ v (projPl σ J v g) = 1) (hψ : ∀ g, (ψ g : ℂ) = ∏ᶠ v, (χ v (projPl σ J v g) : ℂ)) :
    IsUnramFactorisation (fun v => IrrU.ofChar (χ v) (hχ v)) (fun _ => (1 : ℂ)) (charRep ψ)
      fun y : Pl F → ℂ => ∏ᶠ v, y v := by
  have hf : IsFactorisation σ J (fun v => charRep (χ v)) (fun _ => 1) (charRep ψ) fun y => ∏ᶠ v, y v :=
    isRestrTensor_charRep (projPl σ J) χ ψ h hψ
  refine ⟨hf, fun v => smRep_charRep (G := GLoc σ J v) (ho v), fun L _ => (hf.eventually_fixed L).mono fun v hv => ?_⟩
  refine le_antisymm (fun z _ => Submodule.mem_span_singleton.2 ⟨z, mul_one (z : ℂ)⟩)
    ((Submodule.span_singleton_le_iff_mem _ _).2 (LGrp.mem_fixed.2 hv))

example : IsIrrUnitary (charRep (1 : GAd σ J →* Circle)) ∧ ∃ (R : ∀ v, IrrU (GPl σ J v)) (ξ : ∀ v, (R v).H)
    (B : (∀ v, (R v).H) → ℂ), IsUnramFactorisation R ξ (charRep 1) B :=
  ⟨isIrrUnitary_charRep continuous_const, _, _, _, isUnramFactorisation_charRep (fun _ => 1) (fun _ => continuous_const)
    (fun _ => by simp) 1 (fun _ => .of_forall fun _ => rfl) fun _ => by simp⟩

end Flath

end GlobalTheory

end
end

-- bundled from Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LowerLiftsZeroOfWittIdxEqZero
section
noncomputable section

open scoped ComplexConjugate
open MeasureTheory Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory.Cusp
open GlobalTheory.Mem.Th (InfF CptF)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RallisIP

variable {D : D7} {A B : HSp D} (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)) (m : Measure (GA D A))

def thetaLift (Φ : WO A B → ℂ) (f : GA D A → ℂ) : GA D B → ℂ :=
  fun h => petersson A m (fun g => thetaKO ω g h Φ) f

def LiftConv (Φ : WO A B → ℂ) (f : GA D A → ℂ) : Prop :=
  ∀ h, Integrable (descend (GQ A) fun g => thetaKO ω g h Φ * conj (f g)) (autMeasure A m)

def LowerLiftsZero (ψ : AddChar (AF D.host.F) ℂ) (B : HSp D) (χA χB : (AE D)ˣ →* Circle)
    (π : Submodule ℂ (GA D A → ℂ)) : Prop :=
  ∀ (i : ℕ) (B' : HSp D), 1 ≤ i → IsWittLower B B' i → B'.SigOK →
    ∀ ω' : GA D A × GA D B' →* Module.End ℂ (WO A B' → ℂ), IsWeilDatumO ψ A B' χA χB ω' →
      ∀ Φ, IsThetaFunO ψ A B' Φ → ∀ f ∈ π, LiftConv ω' m Φ f → thetaLift ω' m Φ f = 0

end GlobalTheory.RallisIP

namespace GlobalTheory.Published

open GlobalTheory.RallisIP
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (delta swSec sZero IsKFinVec ThetaClause)

def RallisInnerProductConvergent : Prop :=
  ∀ (D : D7) (A B : HSp D), A.rank < B.rank → B.rank ≤ 2 * A.rank →
    (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) →
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (χA χB : (AE D)ˣ →* Circle)
    (ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ))
    (ωd : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)),
    IsWeilDatumO ψ A B χA χB ω → IsWeilDatumO ψ (dblSp A) B 1 χB ωd → ThetaClause ψ A B χB ω ωd →
  ∀ a : GL (Fin A.rank) (AE D), IsMaj A a → HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) →
  ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 →
  ∀ (θ : InfF D) (C : CptF A), IsInfFam θ → A.SigOK → IsCartanFrame A C →
  ∀ (m : Measure (GA D A)) [m.IsHaarMeasure] [m.IsMulRightInvariant] (mH : Measure (GA D B)), mH.IsHaarMeasure →
  ∀ U : Submodule ℂ (DividedPowerChartLift A m), IsIrredSubrep (RG A m) U → U ≤ L2cusp A m →
    LowerLiftsZero m ψ B χA χB (AutMult.formsIn A m (A0 θ A C) U) →
  ∀ Φ₁ Φ₂, IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → IsKFinVec ωd (Khat A a) (delta A B Φ₁ Φ₂) →
  ∀ f₁ ∈ AutMult.formsIn A m (A0 θ A C) U, ∀ f₂ ∈ AutMult.formsIn A m (A0 θ A C) U,
    (LiftConv ω m Φ₁ f₁ ∧ MemL2Quotient (GQ B) mH (thetaLift ω m Φ₁ f₁)) ∧
    (LiftConv ω m Φ₂ f₂ ∧ MemL2Quotient (GQ B) mH (thetaLift ω m Φ₂ f₂)) ∧
    ZetaValueAt A χB⁻¹ m (flat A a (swSec A B ωd ν 𝓕 (delta A B Φ₁ Φ₂)) (sZero A B)) f₁ f₂ (sZero A B)
      ((((autMeasure B mH).real Set.univ : ℝ) : ℂ)⁻¹ * petersson B mH (thetaLift ω m Φ₁ f₁) (thetaLift ω m Φ₂ f₂))

end GlobalTheory.Published

namespace GlobalTheory.RallisIP

variable {D : D7} {A B : HSp D}

theorem wittIdx_eq_wittIndex (B : HSp D) : Formalism.MainNotions.SchurIrreducible.wittIdx B = wittIndex B := by
  unfold Formalism.MainNotions.SchurIrreducible.wittIdx wittIndex
  congr 1
  ext k
  refine exists_congr fun W => and_comm.trans (and_congr_left' ⟨fun h y hy => mem_perp.2 fun x hx => ?_, fun h x hx y hy => ?_⟩)
  · exact h x hx y hy
  · exact mem_perp.1 (h hy) x hx

theorem exists_lower_iff {i : ℕ} : (∃ B' : HSp D, IsWittLower B B' i ∧ B'.SigOK) ↔ i ≤ Formalism.MainNotions.SchurIrreducible.wittIdx B := by
  rw [wittIdx_eq_wittIndex]; exact exists_isWittLower_iff

theorem lowerLiftsZero_of_wittIdx_eq_zero (h : Formalism.MainNotions.SchurIrreducible.wittIdx B = 0) (m : Measure (GA D A)) (ψ : AddChar (AF D.host.F) ℂ)
    (χA χB : (AE D)ˣ →* Circle) (π : Submodule ℂ (GA D A → ℂ)) : LowerLiftsZero m ψ B χA χB π := fun i B' hi h1 h2 => by
  have := exists_lower_iff.1 ⟨B', h1, h2⟩
  omega

variable {ω : GA D A × GA D B →* Module.End ℂ (WO A B → ℂ)} {m : Measure (GA D A)} {Φ : WO A B → ℂ} {f : GA D A → ℂ}

theorem thetaLift_smul (c : ℂ) : thetaLift ω m Φ (c • f) = conj c • thetaLift ω m Φ f := funext fun h => by
  simp only [thetaLift, Pi.smul_apply, smul_eq_mul]
  rw [← petersson_conj_symm, petersson_smul_left, map_mul, petersson_conj_symm]

example (D : D7) : ∃ A B : HSp D, A.SigOK ∧ A.rank < B.rank ∧ B.rank ≤ 2 * A.rank ∧
    A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank ∧ ∀ τ, B.SigOK ∧ B.sig τ = (8, 1) := by
  have h := Examples₂.lorentzSpace_signature_ok (E := D.host.E) Examples₂.star_isIntegral
  have h1 : Formalism.MainNotions.SchurIrreducible.wittIdx (Examples₂.lorentzSpace (E := D.host.E) Examples₂.star_isIntegral) ≤ 1 :=
    (WittSignature.wittIdx_le_signature _ _ h D.host.φ₀ (D.sp.cm.cmUnram.2.1 D.host.φ₀)).2
  exact ⟨Examples₂.posSpace Examples₂.star_isIntegral 5, Examples₂.lorentzSpace Examples₂.star_isIntegral, Examples₂.posSpace_sigOK _ 5, (by decide : 5 < 8 + 1), (by decide : 8 + 1 ≤ 2 * 5),
    (Nat.add_le_add_left h1 5).trans_lt (by decide : 5 + 1 < 8 + 1), fun _ => ⟨h, rfl⟩⟩

end GlobalTheory.RallisIP

end
end

