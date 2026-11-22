import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0040
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0041
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0014
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitary

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FRatioSelf
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjSpace

attribute [local instance] MvPolynomial.gradedAlgebra

namespace GlobalTheory.EtProj

variable {R : Type} [CommRing R] {X : Scheme.{0}} {N : ℕ} (ι : X ⟶ PSpace R N)

def fOpen (g : MvPolynomial (Fin (N + 1)) R) : X.Opens := ι ⁻¹ᵁ Proj.basicOpen (grading R N) g

def fRatio {n : ℕ} (f g : MvPolynomial (Fin (N + 1)) R) (hf : f ∈ grading R N n) (hg : g ∈ grading R N n) :
    Γ(X, fOpen ι g) :=
  (ι.app (Proj.basicOpen (grading R N) g)).hom (GlobalTheory.ProjFrac.frac (grading R N) _ f g hf hg le_rfl)

theorem fRatio_self {n : ℕ} (g : MvPolynomial (Fin (N + 1)) R) (hg : g ∈ grading R N n) :
    fRatio ι g g hg hg = 1 := by
  unfold fRatio
  rw [GlobalTheory.ProjFrac.frac_self]
  exact map_one _

theorem mem_fOpen (g : MvPolynomial (Fin (N + 1)) R) (z : X) :
    z ∈ fOpen ι g ↔ g ∉ (ι.base z).asHomogeneousIdeal := Iff.rfl

end GlobalTheory.EtProj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.H0WeightPartNoInvariantsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.H0_weight_part_no_invariants : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (i : N.Loc) (ρ : G H.E N.Om →* GL (Fin R.r) (N.O i)) (Dg : Subgroup (G H.E N.Om)), GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.NoInv Dg (GlobalTheory.IndefiniteRowSideFullHecke.NoLocalInvariantsRankParts.matW N i ρ) → H0 ((Formalism.MainNotions.N.Glob.WpK N i ρ).comp Dg.subtype) = ⊥ := by
  first | exact @GlobalTheory.Ggeo.WpKInv.H0_weight_part_eq_bot | exact GlobalTheory.Ggeo.WpKInv.H0_weight_part_eq_bot | (intros; apply GlobalTheory.Ggeo.WpKInv.H0_weight_part_eq_bot <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisLocalWeights
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.NRows

open Pointwise

theorem ine_conj_of_smul {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    {A : ValuationSubring Ω} {g σ : G F Ω} (hσ : σ ∈ Ine (F := F) (g • A)) :
    g⁻¹ * σ * g ∈ Ine (F := F) A := by
  have m : ∀ y : Ω, y ∈ g • A ↔ (g⁻¹ : G F Ω) y ∈ A := fun y => by
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def]
  have m' : ∀ y : Ω, (g • A).valuation y < 1 ↔ A.valuation ((g⁻¹ : G F Ω) y) < 1 := fun y => by
    rw [valuation_lt_one_iff', valuation_lt_one_iff', m, m, map_inv₀,
      map_eq_zero_iff _ (g⁻¹ : G F Ω).injective]
  have c : ∀ x : Ω, (g⁻¹ : G F Ω) (g x) = x := fun x => by
    show (g⁻¹ * g) x = x
    simp
  refine ⟨?_, fun x hx => ?_⟩
  · have h : σ • g • A = g • A := hσ.1
    show (g⁻¹ * σ * g) • A = A
    rw [mul_smul, mul_smul, h, inv_smul_smul]
  · have hx' : (g • A).valuation (g x) ≤ 1 := by
      rw [ValuationSubring.valuation_le_one_iff, m, c]
      exact (A.valuation_le_one_iff x).1 hx
    have h := (m' _).1 (hσ.2 _ hx')
    rw [map_sub, c] at h
    exact h

theorem crys_unram_of_lgc : ∀ D : D7, SumRepresentations.tie0 D → SumRepresentations.adm1 D → (∀ (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i) (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ → (∀ w, w ∉ placesOver D.host.E (D.nd.l i) → D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧ ∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ w ∧ D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2) ∧ ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i ρ τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) → ∀ (i : D.nd.Loc) (r : D.nd.X i → (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))), (∀ x, SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x (mapRep (iotaOQ D.nd D.naut i) (r x))) → (∀ w ∈ placesOver D.host.E (D.nd.l i),
      (D.nd.l i ≠ D.host.g 0 → D.nd.l i ≠ D.host.g 1 → ∀ x, D.naut.IsCrysW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
        ∀ τ, InducesW D.nd i τ w → D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ) ∧
      ((D.nd.l i = D.host.g 0 ∨ D.nd.l i = D.host.g 1) → ∀ x,
        (∀ P Pa, D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa → D.naut.mono0 (isoLoc D.nd D.naut Pa w)) →
        D.naut.IsPotCrysW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)) ∧
    ∀ x w, w ∉ placesOver D.host.E (D.nd.l i) → w ∉ D.nd.S i → w ∉ D.nd.Q i → UnramAt (F := D.host.E) (r x) w := by
  intro D htie hadm hLGC i r hr
  obtain ⟨-, -, hGal⟩ := htie
  have hl : (D.nd.l i).Prime := Fact.out
  have key : ∀ x, ∃ P Pa, D.naut.ptV i P = some x ∧ IsBCV D.nd D.naut i P Pa := fun x => by
    obtain ⟨P, hP⟩ := D.naut.pt_surj i x
    obtain ⟨Pa, hPa⟩ := hadm i P
    exact ⟨P, Pa, hP, hPa⟩
  have hunr : ∀ P Pa w, IsBCV D.nd D.naut i P Pa → w ∉ D.nd.Q i →
      (∀ k, w ∉ placesOver D.host.E (D.host.g k)) →
      w ∉ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde) →
      D.naut.unr (isoLoc D.nd D.naut Pa w) := by
    intro P Pa w hB hQ hg hp
    by_cases hs : IsSplitPl D.host w
    · rw [hB.2.2.2.1 w hs]
      exact D.naut.locV_unr i P w hs hQ hg hp
    · exact (hB.2.2.2.2.1 w hs).1
  refine ⟨fun w hw => ⟨fun hl0 hl1 x => ?_, fun _ x hm => ?_⟩, fun x w hwl hwS hwQ => ?_⟩
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw
    refine ⟨(hGal.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩, fun τ hτ => h.2.2 τ hτ⟩
    rw [h.2.1, D.naut.unr_tw]
    refine hunr P Pa w hB (fun hq => D.nd.SQ_l i w (Or.inr hq) hw) (fun k => ?_) ?_
    · have hk : D.nd.l i ≠ D.host.g k := by
        fin_cases k
        · exact hl0
        · exact hl1
      exact SumRepresentations.not_over_of_ne hl (D.host.g_prime k) hk hw
    · split_ifs with hpd
      · exact SumRepresentations.not_over_of_ne hl D.host.pde'_prime (hpd ▸ D.host.pde_ne) hw
      · exact SumRepresentations.not_over_of_ne hl D.host.pde_prime hpd hw
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).2 w hw
    refine (hGal.2.1 i _ _ w hw (hr x).1).2 ⟨h.1, ?_⟩
    rw [h.2.1, D.naut.monomial_twist_iff]
    exact hm P Pa hP hB
  · obtain ⟨P, Pa, hP, hB⟩ := key x
    have h := (hLGC i x P Pa hP hB _ (hr x)).1 w hwl
    have hS : ¬ ((w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
        w ∈ placesOver D.host.E (if D.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) ∧
        w ∉ placesOver D.host.E (D.nd.l i)) := fun hh => hwS ((D.nd.S_def i w).2 hh)
    have hu : D.naut.unr (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w) := by
      rw [h, D.naut.unr_tw]
      refine hunr P Pa w hB hwQ (fun k hk => hS ⟨?_, hwl⟩) (fun hk => hS ⟨Or.inr (Or.inr hk), hwl⟩)
      fin_cases k
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    have h1 := (D.naut.wdOf_unr i _ w hwl (hr x).1).1 hu
    intro A hA σ hσ
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isPlaceOver (D.nd.plOm.2 w) hA
    have hσ' : σ ∈ Ine (F := D.host.E) (g • D.nd.plOm.1 w) := by rw [hg]; exact hσ
    have h2 := h1 _ (ine_conj_of_smul hσ')
    have h3 : mapRep (iotaOQ D.nd D.naut i) (r x) σ = 1 := by
      have e : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      rw [e, map_mul, map_mul, h2, mul_one, ← map_mul, mul_inv_cancel, map_one]
    apply Units.ext
    have h4 := congrArg (fun u : GL (Fin D.R.nV) (Qbar (D.nd.l i)) => u.val) h3
    simp only [mapRep, MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe, Units.val_one] at h4
    refine Matrix.map_injective (SumRepresentations.iotaOQ_injective D.nd D.naut i) ?_
    show (r x σ).val.map (iotaOQ D.nd D.naut i) = (1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (D.nd.O i)).map (iotaOQ D.nd D.naut i)
    rw [Matrix.map_one _ (map_zero _) (map_one _)]
    exact h4

end GlobalTheory.NRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeGaloisOfUnramifiedMatch
section
noncomputable section

namespace GlobalTheory.NRows

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial

theorem isHeckeGaloisQ_of_wdOf_baseChange : ∀ (D : D7) (i : D.nd.Loc) (x : D.nd.X i) (P : D.naut.AV i)
    (Pa : List (Part D.naut.CG)), D.naut.ptV i P = some x → IsBCV D.nd D.naut i P Pa →
    ∀ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.nV) (Qbar (D.nd.l i)), SumRepresentations.At.ContQ D.nd i ρ → IsSSRep ρ →
    (∀ w, w ∉ placesOver D.host.E (D.nd.l i) →
      D.naut.wdOf i ρ w = D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) →
    SumRepresentations.At.IsHeckeGaloisQ D.nd D.naut i x ρ := by
  intro D i x P Pa hP hBC ρ hc hss hwd
  refine ⟨hc, hss, fun w hw B σ hB hσ => ?_⟩
  have hS := (D.nd.S_def i w).not.1 hw.2.2.1
  have hunr : D.naut.unr (D.naut.locV i P w) := by
    refine D.naut.locV_unr i P w hw.1 hw.2.2.2 (fun k hk => hS ⟨?_, hw.2.1⟩)
      (fun hk => hS ⟨Or.inr (Or.inr hk), hw.2.1⟩)
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hloc := hBC.2.2.2.1 w hw.1
  have hw' := hwd w hw.2.1
  have hu : D.naut.unr (D.naut.wdOf i ρ w) := by
    rw [hw', hloc]
    exact (D.naut.unr_tw _ _).2 hunr
  have e := D.naut.wdOf_frob i ρ w hw.2.1 hc hu B σ hB hσ
  rw [hw', hloc, ← D.naut.pt_loc i P x hP w hw] at e
  apply Polynomial.map_injective (D.naut.iotaQC i).toRingHom (D.naut.iotaQC i).injective
  rw [e, Polynomial.map_map]
  rfl

end GlobalTheory.NRows
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentificationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N), GlobalTheory.RowTie.WDTie N A → GlobalTheory.ThetaExh.ParamLaws N A ∧ GlobalTheory.RowTie.CharLaws N A ∧ GlobalTheory.RowTie.Cancel N A := by
  first | exact @GlobalTheory.RowLaws.main | exact GlobalTheory.RowLaws.main | (intros; apply GlobalTheory.RowLaws.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
section
open Formalism.MainNotions Formalism.MainNotions.N

namespace GlobalTheory.SplitField

def EndSpanned {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (W : Submodule L (Fin a → L)) : Prop :=
  ∀ φ : W →ₗ[L] W, ∃ X ∈ Submodule.span L (Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L)),
    ∀ w : W, X.mulVec (w : Fin a → L) = (φ w : Fin a → L)

end GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem mapRep_mapRep {Γ A B C : Type} [Group Γ] [CommRing A] [CommRing B] [CommRing C] {a : ℕ} (f : A →+* B) (g : B →+* C) (ρ : Γ →* GL (Fin a) A) : mapRep g (mapRep f ρ) = mapRep (g.comp f) ρ := by
  refine MonoidHom.ext fun x => Units.ext ?_
  ext i k
  simp [mapRep]

theorem exists_finite_field {K : Type} [Field K] (S : Set (AlgebraicClosure K)) (hS : S.Finite) : ∃ (K' : Type) (_ : Field K') (_ : Algebra K K') (_ : FiniteDimensional K K') (f : K' →+* AlgebraicClosure K), (∀ x : K, f (algebraMap K K' x) = algebraMap K (AlgebraicClosure K) x) ∧ S ⊆ Set.range f := by
  haveI := hS.to_subtype
  have hfd : FiniteDimensional K (IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => Algebra.IsIntegral.isIntegral x)
  exact ⟨IntermediateField.adjoin K S, inferInstance, inferInstance, hfd, (IntermediateField.adjoin K S).val.toRingHom,
    fun x => rfl, fun x hx => ⟨⟨x, IntermediateField.subset_adjoin K S hx⟩, rfl⟩⟩

theorem mem_span_of_map_mem_span {L E ι : Type} [Field L] [Field E] [Fintype ι] (f : L →+* E) (S : Set (ι → L)) (y : ι → L) (h : (f ∘ y) ∈ Submodule.span E ((fun v => f ∘ v) '' S)) : y ∈ Submodule.span L S := by
  classical
  by_contra hy
  have hq : (Submodule.span L S).mkQ y ≠ 0 := by
    rwa [Ne, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Module.Dual L ((ι → L) ⧸ Submodule.span L S), ψ ((Submodule.span L S).mkQ y) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hq ((Module.forall_dual_apply_eq_zero_iff L _).1 hc)
  set l : (ι → L) →ₗ[L] L := ψ ∘ₗ (Submodule.span L S).mkQ with hl
  have hlS : ∀ s ∈ S, l s = 0 := by
    intro s hs
    simp [hl, (Submodule.Quotient.mk_eq_zero _).2 (Submodule.subset_span hs)]
  let c : ι → L := fun i => l (fun j => if i = j then 1 else 0)
  have hlc : ∀ v, l v = ∑ i, v i * c i := by
    intro v
    rw [LinearMap.pi_apply_eq_sum_univ l v]
    simp [c, smul_eq_mul]
  let Λ : (ι → E) →ₗ[E] E := ∑ i, f (c i) • LinearMap.proj i
  have hΛ : ∀ v, Λ (f ∘ v) = f (l v) := by
    intro v
    simp [Λ, hlc, map_sum, mul_comm]
  have hker : Submodule.span E ((fun v => f ∘ v) '' S) ≤ LinearMap.ker Λ := by
    rw [Submodule.span_le]
    rintro _ ⟨s, hs, rfl⟩
    simp [hΛ, hlS s hs]
  have h1 := hker h
  rw [LinearMap.mem_ker, hΛ] at h1
  exact hψ ((map_eq_zero f).1 h1)

theorem mulVec_mem_of_mem_span {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (W : Submodule L (Fin a → L)) (hW : IsInv τ W) {X : Matrix (Fin a) (Fin a) L}
    (hX : X ∈ Submodule.span L (Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) :
    ∀ w ∈ W, X.mulVec w ∈ W := by
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hW g
  | zero => intro w _; simp
  | add x y _ _ hx hy => intro w hw; rw [Matrix.add_mulVec]; exact W.add_mem (hx w hw) (hy w hw)
  | smul c x _ hx => intro w hw; rw [Matrix.smul_mulVec]; exact W.smul_mem c (hx w hw)

theorem isIrrSub_of_endSpanned {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (W : Submodule L (Fin a → L)) (hne : W ≠ ⊥) (hinv : IsInv τ W) (hE : EndSpanned τ W) : IsIrrSub τ W := by
  classical
  refine ⟨hne, hinv, fun W' hle hinv' => ?_⟩
  by_cases h0 : W' = ⊥
  · exact Or.inl h0
  right
  obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff W').1 h0
  refine le_antisymm hle fun u hu => ?_
  have hx' : (⟨x, hle hx⟩ : W) ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual L W, φ ⟨x, hle hx⟩ ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hx' ((Module.forall_dual_apply_eq_zero_iff L _).1 hc)
  obtain ⟨X, hX, hXw⟩ := hE (((φ ⟨x, hle hx⟩)⁻¹ • φ).smulRight (⟨u, hu⟩ : W))
  have h1 := hXw ⟨x, hle hx⟩
  simp only [LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ, one_smul] at h1
  rw [← h1]
  exact mulVec_mem_of_mem_span τ W' hinv' hX x hx

end GlobalTheory.SplitField

namespace GlobalTheory.SplitField

theorem map_mulVec_mem_of_mem_span {Γ L E : Type} [Group Γ] [Field L] [Field E] (f : L →+* E) {a : ℕ} (τ : Γ →* GL (Fin a) L)
    (U : Submodule E (Fin a → E)) (hU : IsInv (mapRep f τ) U) {X : Matrix (Fin a) (Fin a) L}
    (hX : X ∈ Submodule.span L (Set.range fun g => ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L))) :
    ∀ u ∈ U, (X.map f).mulVec u ∈ U := by
  induction hX using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact hU g
  | zero => intro u _; rw [Matrix.map_zero _ (map_zero f), Matrix.zero_mulVec]; exact U.zero_mem
  | add x y _ _ hx hy => intro u hu; rw [Matrix.map_add _ (map_add f), Matrix.add_mulVec]; exact U.add_mem (hx u hu) (hy u hu)
  | smul c x _ hx =>
    intro u hu
    have : (c • x).map f = f c • x.map f := by ext i j; simp
    rw [this, Matrix.smul_mulVec]; exact U.smul_mem _ (hx u hu)

theorem absIrrSub_of_endSpanned {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (W : Submodule L (Fin a → L)) (hne : W ≠ ⊥) (hinv : IsInv τ W) (hE : EndSpanned τ W) : AbsIrrSub τ W := by
  unfold AbsIrrSub
  set f := algebraMap L (AlgebraicClosure L) with hf
  have hmap : ∀ (M : Matrix (Fin a) (Fin a) L) (v : Fin a → L),
      (M.map f).mulVec (f ∘ v) = f ∘ (M.mulVec v) := by
    intro M v
    funext i
    exact (RingHom.map_mulVec f M v i).symm
  have hrep : ∀ g, ((mapRep f τ g : GL (Fin a) (AlgebraicClosure L)) : Matrix (Fin a) (Fin a) (AlgebraicClosure L))
      = ((τ g : GL (Fin a) L) : Matrix (Fin a) (Fin a) L).map f := fun g => rfl
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hne
    refine (Submodule.ne_bot_iff _).2 ⟨f ∘ v, Submodule.subset_span ⟨v, hv, rfl⟩, ?_⟩
    intro h
    apply hv0
    funext i
    have := congrFun h i
    simpa using this
  · intro g u hu
    show ((mapRep f τ g : GL (Fin a) (AlgebraicClosure L)) : Matrix (Fin a) (Fin a) (AlgebraicClosure L)).mulVec u ∈ _
    rw [hrep]
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      rw [hmap]
      exact Submodule.subset_span ⟨_, hinv g v hv, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ c hx
  · intro U hU hinvU
    have key : ∀ φ : W →ₗ[L] W, ∃ M : Matrix (Fin a) (Fin a) L,
        (∀ u ∈ U, (M.map f).mulVec u ∈ U) ∧ ∀ w : W, M.mulVec w = (φ w : Fin a → L) := by
      intro φ
      obtain ⟨X, hX, hXw⟩ := hE φ
      exact ⟨X, map_mulVec_mem_of_mem_span f τ U hinvU hX, hXw⟩
    by_cases h0 : U = ⊥
    · exact Or.inl h0
    right
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff U).1 h0
    obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu0 (funext h)
    refine le_antisymm hU (Submodule.span_le.2 ?_)
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨M, h1, h2⟩ := key
      (((LinearMap.proj j : (Fin a → L) →ₗ[L] L).comp W.subtype).smulRight (⟨w, hw⟩ : W))
    have h3 : ∀ x ∈ Submodule.span (AlgebraicClosure L) ((fun v => f ∘ v) '' (W : Set (Fin a → L))),
        (M.map f).mulVec x = x j • (f ∘ w) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        rw [hmap]
        have := h2 ⟨v, hv⟩
        simp only at this
        rw [this]
        funext i
        simp
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, Pi.add_apply, add_smul]
      | smul c x _ hx => rw [Matrix.mulVec_smul, hx, Pi.smul_apply, smul_eq_mul, mul_smul]
    have h4 := h1 u hu
    rw [h3 u (hU hu)] at h4
    exact (U.smul_mem_iff hj).1 h4

theorem endSpanned_of_isoSub {Γ L : Type} [Group Γ] [Field L] {a : ℕ} (τ : Γ →* GL (Fin a) L) (W U : Submodule L (Fin a → L)) (hW : IsInv τ W) (hiso : IsoSub τ W U) (hE : EndSpanned τ U) : EndSpanned τ W := by
  obtain ⟨e, he⟩ := hiso
  intro φ
  obtain ⟨X, hX, hXw⟩ := hE ((e : W →ₗ[L] U) ∘ₗ φ ∘ₗ (e.symm : U →ₗ[L] W))
  refine ⟨X, hX, fun w => ?_⟩
  have key : ∀ v : W, ∃ h : X.mulVec (v : Fin a → L) ∈ W, ((e ⟨_, h⟩ : U) : Fin a → L) = X.mulVec (e v : Fin a → L) := by
    clear hXw
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      intro v
      exact ⟨hW g v v.2, he g v _⟩
    | zero =>
      intro v
      refine ⟨by simp, ?_⟩
      simp only [Matrix.zero_mulVec]
      have : (⟨0, W.zero_mem⟩ : W) = 0 := rfl
      rw [this, map_zero]; rfl
    | add x y hx' hy' hx hy =>
      intro v
      obtain ⟨h1, e1⟩ := hx v
      obtain ⟨h2, e2⟩ := hy v
      refine ⟨by rw [Matrix.add_mulVec]; exact W.add_mem h1 h2, ?_⟩
      have : (⟨(x + y).mulVec v, by rw [Matrix.add_mulVec]; exact W.add_mem h1 h2⟩ : W) = ⟨_, h1⟩ + ⟨_, h2⟩ := by
        ext1; simp [Matrix.add_mulVec]
      rw [this, map_add, Submodule.coe_add, e1, e2, Matrix.add_mulVec]
    | smul c x hx' hx =>
      intro v
      obtain ⟨h1, e1⟩ := hx v
      refine ⟨by rw [Matrix.smul_mulVec]; exact W.smul_mem c h1, ?_⟩
      have : (⟨(c • x).mulVec v, by rw [Matrix.smul_mulVec]; exact W.smul_mem c h1⟩ : W) = c • ⟨_, h1⟩ := by
        ext1; simp [Matrix.smul_mulVec]
      rw [this, map_smul, Submodule.coe_smul, e1, Matrix.smul_mulVec]
  obtain ⟨h, hk⟩ := key w
  have h2 := hXw (e w)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h2
  rw [h2] at hk
  have := e.injective (Subtype.ext hk)
  exact congrArg Subtype.val this
end GlobalTheory.SplitField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlaceExtendsToIso
section
namespace GlobalTheory.ThLoc

theorem place_extends_to_iso : Formalism.L2.KerInert.LamExt :=
  fun p _ lam => GlobalTheory.PadicComplexIso.exists_ringEquiv_extending p lam

end GlobalTheory.ThLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RelIndexGlMapStandardLatticeOfIntegral
section
open GlobalTheory.LatHecke GlobalTheory.SatakeInv

noncomputable section
namespace GlobalTheory.LatHecke

def coordIncl (O K : Type) [CommRing O] [Field K] [Algebra O K] (r : ℕ) :
    (Fin r → O) →ₗ[O] (Fin r → K) :=
  LinearMap.pi fun i => (Algebra.linearMap O K).comp (LinearMap.proj i)

theorem coordIncl_apply {O K : Type} [CommRing O] [Field K] [Algebra O K] {r : ℕ} (x : Fin r → O) :
    coordIncl O K r x = fun i => algebraMap O K (x i) := rfl

theorem coordIncl_injective {O K : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] {r : ℕ} : Function.Injective (coordIncl O K r) := by
  intro x y h
  funext i
  exact IsFractionRing.injective O K (congrFun h i)

theorem std_eq_map_top (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] (r : ℕ) :
    (std O K r).1 = (⊤ : Submodule O (Fin r → O)).map (coordIncl O K r) := by
  rw [← (Pi.basisFun O (Fin r)).span_eq, Submodule.map_span, ← Set.range_comp]
  show Submodule.span O (Set.range (Pi.basisFun K (Fin r))) = _
  congr 2
  funext i
  funext j
  simp [coordIncl_apply, Pi.single_apply]

theorem glMap_std_eq {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
    [Algebra O K] [IsFractionRing O K] {r : ℕ} (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K)
    (hg : (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K)) :
    glMap g (std O K r).1 = (LinearMap.range A.mulVecLin).map (coordIncl O K r) := by
  rw [glMap, std_eq_map_top, ← Submodule.map_comp, LinearMap.range_eq_map,
    ← Submodule.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearMap.restrictScalars_apply, Matrix.toLin'_apply,
      Matrix.mulVecLin_apply, coordIncl_apply, hg]
  funext i
  exact (RingHom.map_mulVec (algebraMap O K) A x i).symm

end GlobalTheory.LatHecke

open GlobalTheory.LatHecke in

theorem GlobalTheory.LatHecke.relIndex_glMap_std_of_integral : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (r : ℕ) (A : Matrix (Fin r) (Fin r) O) (g : GL (Fin r) K), (g : Matrix (Fin r) (Fin r) K) = A.map (algebraMap O K) → (glMap g (std O K r).1).toAddSubgroup.relIndex (std O K r).1.toAddSubgroup = Nat.card ((Fin r → O) ⧸ LinearMap.range A.mulVecLin) ∧ (IsLocalRing.maximalIdeal O • (std O K r).1 ≤ glMap g (std O K r).1 → IsLocalRing.maximalIdeal O • (⊤ : Submodule O (Fin r → O)) ≤ LinearMap.range A.mulVecLin) := by
  intro O K _ _ _ _ _ _ r A g hg
  rw [glMap_std_eq A g hg, std_eq_map_top]
  refine ⟨?_, ?_⟩
  · have h := AddSubgroup.relIndex_map_map_of_injective (f := (coordIncl O K r).toAddMonoidHom)
      (LinearMap.range A.mulVecLin).toAddSubgroup (⊤ : Submodule O (Fin r → O)).toAddSubgroup
      coordIncl_injective
    refine h.trans ?_
    rw [Submodule.top_toAddSubgroup, AddSubgroup.relIndex_top_right]
    rfl
  · intro h
    rw [← Submodule.map_smul''] at h
    exact (Submodule.map_le_map_iff_of_injective coordIncl_injective _ _).1 h
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitComponentsDeterminedByPointOfBaseChangeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitComponentsDeterminedByPoint_of_baseChange : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.ThetaExh.LocOfPt N A i := by
  first | exact @GlobalTheory.RowTie.locOfPt_of_splitBC | exact GlobalTheory.RowTie.locOfPt_of_splitBC | (intros; apply GlobalTheory.RowTie.locOfPt_of_splitBC <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedOfRankOneUnitaryStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_of_rank_one_unitary : ∀ (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut), GlobalTheory.RowTie.RankOneUnitary T → (∀ (a : ℕ) (π : D.naut.CG a), 2 ≤ a → D.naut.csd π → D.naut.ralg π → ∀ w, D.naut.tempered (D.naut.locG π w)) → GlobalTheory.RowCopy.TempCSD D ∧ GlobalTheory.ThetaExh.Tempered D.nd D.naut := by
  first | exact @GlobalTheory.RowTie.tempered_all_ranks | exact GlobalTheory.RowTie.tempered_all_ranks | (intros; apply GlobalTheory.RowTie.tempered_all_ranks <;> assumption)
end

