import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0354
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralMulRightOfCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0339
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0362
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsIrreducibleIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0355
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumHeisenbergLine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0894
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FixedOfForallLocalSubgroupFixedFiniteAdelicStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixed_of_forall_localSubgroup_fixed_finiteAdelic : ∀ (D : D7) (V : HSp D) (W : Type) [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (GfC V) W), GlobalTheory.PRep.IsSmooth σ → ∀ (K' : ∀ v, Subgroup (GLoc D.sp.cm.sig V.gram v)), (∀ v, K' v ≤ Kv V v) → ∀ x : W, (∀ v, ∀ k ∈ K' v, σ (locFin V v k) x = x) → ∀ g : GfC V, (∀ v, finLoc V v g ∈ K' v) → σ g x = x := by
  first | exact @GlobalTheory.TrIdem.fixed_of_forall_finLoc_mem | exact GlobalTheory.TrIdem.fixed_of_forall_finLoc_mem | (intros; apply GlobalTheory.TrIdem.fixed_of_forall_finLoc_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBesselGroupsClosedHaarProductStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_bessel_groups_closed_haar_product : ∀ (D : D7) (S S₀ A L : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) (ν : Measure (flagN d)) (𝓝 : Set (flagN d)), GlobalTheory.Per.IsUnitN S d.e ν 𝓝 → (IsClosed (jacGrp d : Set (GA D S)) ∧ ∀ μ : Measure (GA D S₀), μ.IsHaarMeasure → (semiMeas (flagN d) d.emb0 μ ν).IsHaarMeasure) ∧ IsClosed (besGrp d o : Set (GA D S)) ∧ ∀ μ : Measure (GA D A), μ.IsHaarMeasure → (semiMeas (flagN d) (embA d o) μ ν).IsHaarMeasure := by
  first | exact @GlobalTheory.MixPer.jacGrp_besGrp_haar | exact GlobalTheory.MixPer.jacGrp_besGrp_haar | (intros; apply GlobalTheory.MixPer.jacGrp_besGrp_haar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKMapExtensionLevelCharacterCovariant
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GKExtLevel

theorem sobCont_sub_smul {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {Lie : Set (Matrix (Fin n) (Fin n) ℂ)} {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {ℓ₁ ℓ₂ : H →ₗ[ℂ] ℂ}
    (c : ℂ) (h₁ : Sobolev₂ Lie σ ℓ₁) (h₂ : Sobolev₂ Lie σ ℓ₂) : Sobolev₂ Lie σ (ℓ₁ - c • ℓ₂) := by
  obtain ⟨S₁, C₁, hS₁, hC₁⟩ := h₁
  obtain ⟨S₂, C₂, hS₂, hC₂⟩ := h₂
  refine ⟨S₁ ++ S₂, |C₁| + ‖c‖ * |C₂|, fun l hl X hX => ?_, fun w hw => ?_⟩
  · rcases List.mem_append.1 hl with h | h
    exacts [hS₁ l h X hX, hS₂ l h X hX]
  · have nn : ∀ S : List (List (Matrix (Fin n) (Fin n) ℂ)), 0 ≤ (S.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      fun S => List.sum_nonneg fun x hx => by
        obtain ⟨l, -, rfl⟩ := List.mem_map.1 hx
        exact norm_nonneg _
    have n1 := nn S₁
    have n2 := nn S₂
    rw [List.map_append, List.sum_append]
    have b1 := (hC₁ w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self C₁) n1)
    have b2 := (hC₂ w hw).trans (mul_le_mul_of_nonneg_right (le_abs_self C₂) n2)
    have e : ‖(ℓ₁ - c • ℓ₂) w‖ ≤ ‖ℓ₁ w‖ + ‖c‖ * ‖ℓ₂ w‖ := by
      rw [← norm_mul]
      simpa using norm_sub_le (ℓ₁ w) (c * ℓ₂ w)
    have h3 := mul_le_mul_of_nonneg_left b2 (norm_nonneg c)
    have p1 : 0 ≤ |C₁| * (S₂.map fun l => ‖l.foldr (dRep σ) w‖).sum := mul_nonneg (abs_nonneg _) n2
    have p2 : 0 ≤ ‖c‖ * |C₂| * (S₁.map fun l => ‖l.foldr (dRep σ) w‖).sum :=
      mul_nonneg (mul_nonneg (norm_nonneg _) (abs_nonneg _)) n1
    nlinarith

theorem lev : GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D)
    (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T₀ : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap M), GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.IsGKMap θ M J χ μ 𝓕 T₀ →
    ∀ T : MMap M, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.Extends T T₀ →
    (∀ τ (v : M.Vec) (x : GA D V), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt V τ) (M.rep τ) ℓ ∧
      ∀ w : M.sm τ, ℓ w = T (Function.update v τ w) x) →
    ∀ v, ∀ k ∈ J, ∀ g, T v (g * k) = χ k * T v g := by
  intro hHC D θ _ V S M J χ μ 𝓕 T₀ hT₀ T hext hcont v k hk g
  have hsm : ∀ τ, ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, w ∈ M.sm τ := fun τ w hw => by
    haveI := (M.ds τ).1
    exact Submodule.subset_span (GlobalTheory.Published.HarishChandraModules.smoothVec hHC (M.ds τ).2.2.1 (M.ds τ).2.2.2.1 hw
      (M.fr_unit τ) (M.fr_gram τ))
  have key : ∀ s : Finset D.what₂.Tau, ∀ v : M.Vec, (∀ τ ∉ s, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ) →
      T v (g * k) = χ k * T v g := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro v hv
      rw [hext v (fun τ => ⟨v τ, hv τ (Finset.notMem_empty τ)⟩) (fun τ => rfl)]
      exact hT₀.2.2.2.2.2.1 _ k hk g
    | @insert τ s hτ ih =>
      intro v hv
      obtain ⟨ℓ₁, h₁, e₁⟩ := hcont τ v (g * k)
      obtain ⟨ℓ₂, h₂, e₂⟩ := hcont τ v g
      have h0 : ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin M τ, (ℓ₁ - χ k • ℓ₂) w = 0 := by
        intro w hw
        have hi := ih (Function.update v τ ⟨w, hsm τ w hw⟩) (fun τ' hτ' => by
          by_cases h : τ' = τ
          · subst h
            simpa using hw
          · rw [Function.update_of_ne h]
            exact hv τ' (by simp [h, hτ']))
        have a1 := e₁ ⟨w, hsm τ w hw⟩
        have a2 := e₂ ⟨w, hsm τ w hw⟩
        simp only at a1 a2
        rw [LinearMap.sub_apply, LinearMap.smul_apply, a1, a2, hi, smul_eq_mul, sub_self]
      have hz := GlobalTheory.T.sobolevForm_eq_zero_on_smooth_of_kFinite_discreteSeries hHC D V S M τ _ (sobCont_sub_smul (χ k) h₁ h₂) h0 (v τ) (v τ).2
      have a1 := e₁ (v τ)
      have a2 := e₂ (v τ)
      rw [Function.update_eq_self] at a1 a2
      rw [LinearMap.sub_apply, LinearMap.smul_apply, a1, a2, smul_eq_mul, sub_eq_zero] at hz
      exact hz
  exact key Finset.univ v fun τ h => absurd (Finset.mem_univ τ) h

end GlobalTheory.GKExtLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUnique
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section

namespace GlobalTheory.GelfandLine

variable {G : Type} [Group G]

theorem mem_fixed_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

def stabSub (K : Subgroup G) (g : G) : Subgroup G where
  carrier := {h | h ∈ K ∧ g⁻¹ * h * g ∈ K}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨K.mul_mem ha hb, ?_⟩
    convert K.mul_mem ha' hb' using 1
    group
  one_mem' := ⟨K.one_mem, by simp⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨K.inv_mem ha, ?_⟩
    convert K.inv_mem ha' using 1
    group

theorem mem_stabSub {K : Subgroup G} {g h : G} : h ∈ stabSub K g ↔ h ∈ K ∧ g⁻¹ * h * g ∈ K := Iff.rfl

def heckeOp {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (g : G)
    [Fintype (K ⧸ (stabSub K g).subgroupOf K)] : Module.End ℂ V :=
  ∑ q : K ⧸ (stabSub K g).subgroupOf K, ρ ((q.out : G) * g)

theorem heckeOp_apply {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] (v : V) :
    heckeOp ρ K g v = ∑ q : K ⧸ (stabSub K g).subgroupOf K, ρ ((q.out : G) * g) v := by
  simp [heckeOp, LinearMap.sum_apply]

def repSet (K : Subgroup G) (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] : Finset G :=
  Finset.univ.map ⟨fun q : K ⧸ (stabSub K g).subgroupOf K => (q.out : G) * g, fun q q' e => by
    have : (q.out : G) = q'.out := mul_right_cancel e
    exact Quotient.out_inj.1 (Subtype.ext this)⟩

theorem heckeOp_eq_sum {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)
    (g : G) [Fintype (K ⧸ (stabSub K g).subgroupOf K)] (v : V) :
    heckeOp ρ K g v = ∑ γ ∈ repSet K g, ρ γ v := by
  rw [heckeOp_apply, repSet, Finset.sum_map]
  rfl

theorem repSet_spec (K : Subgroup G) (a : G) [Fintype (K ⧸ (stabSub K a).subgroupOf K)] :
    (∀ γ ∈ repSet K a, GelfandTrick.InDoubleCoset K a γ) ∧
    (∀ x : G, GelfandTrick.InDoubleCoset K a x → ∃! γ, γ ∈ repSet K a ∧ γ⁻¹ * x ∈ K) := by
  constructor
  · intro γ hγ
    obtain ⟨q, -, rfl⟩ := Finset.mem_map.1 hγ
    refine ⟨q.out, q.out.2, 1, K.one_mem, ?_⟩
    show (q.out : G) * a = (q.out : G) * a * 1
    simp
  · rintro x ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((stabSub K a).subgroupOf K) (⟨k₁, hk₁⟩ : K)
    have hh' : ((h : K) : G) ∈ stabSub K a := Subgroup.mem_subgroupOf.1 h.2
    set q : K ⧸ (stabSub K a).subgroupOf K := ((⟨k₁, hk₁⟩ : K) : K ⧸ (stabSub K a).subgroupOf K)
    have hq : ((q.out : K) : G) = k₁ * ((h : K) : G) := by
      rw [hh]; rfl
    refine ⟨(q.out : G) * a, ⟨Finset.mem_map.2 ⟨q, Finset.mem_univ _, rfl⟩, ?_⟩, ?_⟩
    · rw [hq]
      have : a⁻¹ * ((h : K) : G)⁻¹ * a ∈ K := (mem_stabSub.1 (inv_mem hh')).2
      convert K.mul_mem this hk₂ using 1
      group
    · rintro y ⟨hy, hyx⟩
      obtain ⟨p, -, rfl⟩ := Finset.mem_map.1 hy
      change (p.out : G) * a = (q.out : G) * a
      congr 1
      have hx1 : ((q.out : G) * a)⁻¹ * (k₁ * a * k₂) ∈ K := by
        rw [hq]
        have : a⁻¹ * ((h : K) : G)⁻¹ * a ∈ K := (mem_stabSub.1 (inv_mem hh')).2
        convert K.mul_mem this hk₂ using 1
        group
      have hx2 : ((p.out : G) * a)⁻¹ * (k₁ * a * k₂) ∈ K := hyx
      have hu : ((p.out : K)⁻¹ * q.out : K) ∈ (stabSub K a).subgroupOf K := by
        rw [Subgroup.mem_subgroupOf]
        refine ⟨(p.out⁻¹ * q.out : K).2, ?_⟩
        convert K.mul_mem hx2 (K.inv_mem hx1) using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      have : (p.out : K ⧸ (stabSub K a).subgroupOf K) = q.out := QuotientGroup.eq.2 hu
      rw [QuotientGroup.out_eq', QuotientGroup.out_eq'] at this
      rw [this]

theorem sum_comm_anti {V : Type} [AddCommGroup V] (K : Subgroup G) (τ : G → G)
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (hK : ∀ k ∈ K, τ k ∈ K)
    (α β : G) (R S : Finset G)
    (hR : ∀ γ ∈ R, GelfandTrick.InDoubleCoset K α γ)
    (hR' : ∀ x : G, GelfandTrick.InDoubleCoset K α x → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K)
    (hS : ∀ γ ∈ S, GelfandTrick.InDoubleCoset K β γ)
    (hS' : ∀ x : G, GelfandTrick.InDoubleCoset K β x → ∃! γ, γ ∈ S ∧ γ⁻¹ * x ∈ K)
    (F : G → V) (hF : ∀ k ∈ K, ∀ g, F (g * k) = F g) :
    ∑ γ ∈ R, ∑ δ ∈ S, F (γ * δ) = ∑ δ ∈ S, ∑ γ ∈ R, F (δ * γ) := by
  classical
  let f : G ⧸ K → V := fun c => F c.out
  have hf : ∀ g : G, f (g : G ⧸ K) = F g := fun g => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [f, hk, hF k k.2]
  have key : ∀ A B : Finset G, ∑ γ ∈ A, ∑ δ ∈ B, F (γ * δ)
      = ∑ p ∈ A ×ˢ B, f ((p.1 * p.2 : G) : G ⧸ K) := fun A B => by
    rw [Finset.sum_product]
    simp only [hf]
  rw [key, key]
  let T : Finset (G ⧸ K) := (R ×ˢ S).image (fun p => ((p.1 * p.2 : G) : G ⧸ K)) ∪
    (S ×ˢ R).image (fun p => ((p.1 * p.2 : G) : G ⧸ K))
  rw [← Finset.sum_fiberwise_of_maps_to' (s := R ×ˢ S) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ K))
      (fun p hp => Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)) f,
    ← Finset.sum_fiberwise_of_maps_to' (s := S ×ˢ R) (t := T)
      (g := fun p => ((p.1 * p.2 : G) : G ⧸ K))
      (fun p hp => Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)) f]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_const, Finset.sum_const]
  congr 1
  apply le_antisymm
  · convert GelfandTrick.card_pairs_le K τ hmul hinv hdc hK α β R S hR hR' hS hS' c
  · convert GelfandTrick.card_pairs_le K τ hmul hinv hdc hK β α S R hS hS' hR hR' c

variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem heckeOp_comm (ρ : Representation ℂ G V) (K : Subgroup G) (τ : G → G)
    (hmul : ∀ a b, τ (a * b) = τ b * τ a) (hinv : ∀ a, τ (τ a) = a)
    (hdc : ∀ g : G, ∃ k₁ ∈ K, ∃ k₂ ∈ K, τ g = k₁ * g * k₂) (a b : G)
    [Fintype (K ⧸ (stabSub K a).subgroupOf K)] [Fintype (K ⧸ (stabSub K b).subgroupOf K)]
    {v : V} (hv : ∀ k ∈ K, ρ k v = v) :
    heckeOp ρ K a (heckeOp ρ K b v) = heckeOp ρ K b (heckeOp ρ K a v) := by
  have hK : ∀ k ∈ K, τ k ∈ K := fun k hk => by
    obtain ⟨k₁, h₁, k₂, h₂, e⟩ := hdc k
    rw [e]; exact K.mul_mem (K.mul_mem h₁ hk) h₂
  have := sum_comm_anti K τ hmul hinv hdc hK a b _ _ (repSet_spec K a).1 (repSet_spec K a).2
    (repSet_spec K b).1 (repSet_spec K b).2 (fun g => ρ g v)
    (fun k hk g => by simp only [map_mul, Module.End.mul_apply, hv k hk])
  rw [heckeOp_eq_sum ρ K a (heckeOp ρ K b v), heckeOp_eq_sum ρ K b v,
    heckeOp_eq_sum ρ K b (heckeOp ρ K a v), heckeOp_eq_sum ρ K a v]
  simpa only [map_sum, map_mul, Module.End.mul_apply] using this

theorem heckeTerm_eq (ρ : Representation ℂ G V) (K : Subgroup G) (a : G) {v : V}
    (hv : ∀ k ∈ K, ρ k v = v) (y : K) :
    ρ ((((y : K ⧸ (stabSub K a).subgroupOf K)).out : G) * a) v = ρ ((y : G) * a) v := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((stabSub K a).subgroupOf K) y
  have hh' : ((h : K) : G) ∈ stabSub K a := Subgroup.mem_subgroupOf.1 h.2
  rw [hh]
  have e : ((y * (h : K) : K) : G) * a = (y : G) * a * (a⁻¹ * ((h : K) : G) * a) := by
    simp only [Subgroup.coe_mul]; group
  rw [e, map_mul, Module.End.mul_apply, hv _ hh'.2]

theorem heckeOp_fixed (ρ : Representation ℂ G V) (K : Subgroup G) (a : G)
    [Fintype (K ⧸ (stabSub K a).subgroupOf K)] {v : V} (hv : ∀ k ∈ K, ρ k v = v) :
    ∀ k ∈ K, ρ k (heckeOp ρ K a v) = heckeOp ρ K a v := by
  intro k hk
  rw [heckeOp_apply, map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm (⟨k, hk⟩ : K)) _ _ fun q => ?_
  have hq : (MulAction.toPerm (⟨k, hk⟩ : K) q : K ⧸ (stabSub K a).subgroupOf K) =
      ((⟨k, hk⟩ * q.out : K) : K ⧸ (stabSub K a).subgroupOf K) := by
    show (⟨k, hk⟩ : K) • q = _
    conv_lhs => rw [← QuotientGroup.out_eq' q]
    rfl
  rw [hq, heckeTerm_eq ρ K a hv, ← Module.End.mul_apply, ← map_mul, ← mul_assoc]
  rfl

theorem finsum_quot_le {K W : Type} [Group K] [AddCommGroup W] {H H' : Subgroup K} (hle : H ≤ H')
    [H.FiniteIndex] (F : K → W) (hF : ∀ y, ∀ h ∈ H', F (y * h) = F y) :
    ∑ᶠ q : K ⧸ H, F q.out = Nat.card (H' ⧸ H.subgroupOf H') • ∑ᶠ p : K ⧸ H', F p.out := by
  classical
  haveI : H'.FiniteIndex := Subgroup.finiteIndex_of_le hle
  let e := Subgroup.quotientEquivProdOfLE hle
  haveI : Finite ((K ⧸ H') × (H' ⧸ H.subgroupOf H')) := Finite.of_equiv _ e
  haveI : Finite (H' ⧸ H.subgroupOf H') := Finite.prod_right (K ⧸ H')
  haveI := Fintype.ofFinite (K ⧸ H)
  haveI := Fintype.ofFinite (K ⧸ H')
  haveI := Fintype.ofFinite (H' ⧸ H.subgroupOf H')
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  have h1 : ∀ q : K ⧸ H, F q.out = F (e q).1.out := by
    intro q
    have : (e q).1 = ((q.out : K) : K ⧸ H') := by
      conv_lhs => rw [← QuotientGroup.out_eq' q]
      rfl
    rw [this]
    obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H' q.out
    rw [hh, hF _ _ h.2]
  rw [Finset.sum_congr rfl fun q _ => h1 q, Fintype.sum_equiv e _ (fun y => F y.1.out) (fun _ => rfl),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card]
  rw [Finset.smul_sum]

end GlobalTheory.GelfandLine

open GlobalTheory.GelfandLine in

theorem GlobalTheory.fixed_eq_span_of_gelfandPair : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G), IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ θ : G → G, (∀ x y, θ (x * y) = θ y * θ x) → (∀ x, θ (θ x) = x) → (∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), ρ.IsIrreducible → IsAdmissible ρ → ∀ x ∈ fixed ρ K, x ≠ 0 → fixed ρ K = ℂ ∙ x := by
  first
  | exact @_root_.GlobalTheory.GroupAverageProjection.main
  | exact _root_.GlobalTheory.GroupAverageProjection.main
  | (apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.GroupAverageProjection.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GroupAverageProjection.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GroupAverageProjection.main ..)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodOpStarTranslatedEvalEqGoodProjectorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodOp_star_translatedEval_eq_goodProjector : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (Gd : GoodOp X) (t : GA D (Yc D 0)) (v₀ : (MP R).Vec), RowLevelMatchAt R F X h t → ∀ S ∈ Mult R.θ (R.MY 0) (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))), ∀ φ : L2X X, φ =ᵐ[muX X] (fun x => ev (MP R) v₀ S (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) → (star (Gd.Rg (star φ)) : L2X X) =ᵐ[muX X] (fun x => ev (MP R) v₀ (postOn (MP R) R.e0 S) (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ ((iotaX X h).symm x) t)) := by
  first | exact @GlobalTheory.GoodProjEval.goodOp_star_ev | exact GlobalTheory.GoodProjEval.goodOp_star_ev | (intros; apply GlobalTheory.GoodProjEval.goodOp_star_ev <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodTypesOfTypesTrue
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.LiftRows.Inh
variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

theorem goodTypes_of_typesTrue (hL : R.toLevCh.Is A.μ0) (h : GlobalTheory.Mem.Top.TypesTrue D.ntypes R.C.P R.C.W) :
    GlobalTheory.IndefiniteRowSideFullHecke.CommutingLevelOperators.GoodTypes R := by
  intro k
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  refine ⟨_, (h.teich k).symm, h.ser k, fun v j PP hPP a u ha hu => Or.inl ?_⟩
  have hl := h.isCharLab k v j
  have hp := D.host.g_prime k
  have ha0 : (a : Formalism.CyclotomicNorms.Fbar (D.host.g k)) ≠ 0 := by
    rw [ha]; intro h0
    have := (GlobalTheory.Mem.TypePl.labDat (D.host.g k)).gen_order 1 one_pos
    rw [h0, pow_one] at this
    have h2 := hp.two_le
    have h3 : orderOf (0 : Formalism.CyclotomicNorms.Fbar (D.host.g k)) = 0 := orderOf_eq_zero_iff'.2 fun n hn => by simp [hn.ne']
    omega
  have hcop : a.Coprime (D.host.g k) := by
    rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
    intro hd
    exact ha0 ((CharP.cast_eq_zero_iff _ (D.host.g k) a).2 hd)
  have han : a ≠ 0 := by rintro rfl; exact ha0 (by simp)
  have h1 := hl.2 (ZMod.unitOfCoprime a hcop) (by rw [ZMod.coe_unitOfCoprime, map_natCast, ha])
  rw [← h1]
  have hE : (a : D.host.E) ≠ 0 := by exact_mod_cast han
  have h2 := (R.C.isMu0 j).atg k PP hPP a hcop (Units.mk0 _ hE) rfl
  have h3 := hL.chi j PP ((hL.Pg PP).2 ⟨k, hPP⟩) (a : 𝓞 D.host.E) (Units.mk0 _ hE) u (by simp) (by rw [hu, map_natCast])
  rw [h2, MonoidHom.inv_apply, _root_.inv_inj] at h3
  rw [h3, MonoidHom.pow_apply]

end GlobalTheory.LiftRows.Inh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GroupConvolutionNormalizedIndicatorSelfStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.TrIdem
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.groupConvolution_normalizedIndicator_self : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (H : Subgroup G), IsOpen (H : Set G) → IsCompact (H : Set G) → conv μ (normInd μ (H : Set G)) (normInd μ (H : Set G)) = normInd μ (H : Set G) := by
  first | exact @GlobalTheory.TrIdem.conv_normInd_self | exact GlobalTheory.TrIdem.conv_normInd_self | (intros; apply GlobalTheory.TrIdem.conv_normInd_self <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarEqRestrictedProductMeasureUnitaryFiniteAdeliStatement
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_eq_restrictedProductMeasure_unitaryFiniteAdelic : ∀ (D : D7) (V : HSp D) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF → ∀ (ν : Measure (GfC V)), IsFinMeas V μf ν → ∀ s : Set (GfC V), IsCompact (closure s) → ν s = νF ((finPtsEquiv D.sp.cm.sig V.gram) ⁻¹' s) := by
  first | exact @GlobalTheory.FinMeasEq.finMeas_eq | exact GlobalTheory.FinMeasEq.finMeas_eq | (intros; apply GlobalTheory.FinMeasEq.finMeas_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HalfPowerDetAbsRealDiagonalTorusStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped Pointwise
open Formalism.IndefR.Datum
open GlobalTheory.Grid
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.halfPowerDetAbs_realDiagonal_torus : ∀ {D : D7} (θ : InfFam D), IsInfFam θ → ∀ (r n : ℕ) (t : Fin r → ℝ), (∀ i, 0 < t i) →
    ∀ α : GL (Fin r) (Formalism.L2.Theta.AE D), α.1.map (finPart D) = 1 →
      (∀ τ, compAt θ τ α.1 = diagonal (fun i => (t i : ℂ))) →
      GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod n α = ∏ i, t i ^ (Module.finrank ℚ D.host.F * n) := by
  first | exact @GlobalTheory.HalfModTorus.halfMod_torus | exact GlobalTheory.HalfModTorus.halfMod_torus | (intros; apply GlobalTheory.HalfModTorus.halfMod_torus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumHeisenbergLineStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_thetaSum_heisenbergLine : ∀ {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F}
    {κ : Type} [Fintype κ] (d : GlobalTheory.WeilM.Darboux B κ) (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ u : W, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) u →
    ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, ∀ Φ' ∈ GlobalTheory.WeilM.schA F κ,
      (∀ x, HasDerivAt (fun t : ℝ => d.rho ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • u) Φ x) (Φ' x) 0) →
      ∀ u' : W, HasDerivAt (fun t : ℝ => GlobalTheory.WeilM.thetaSum F (d.rho ψ u' (d.rho ψ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.realAd F t • u) Φ)))
        (GlobalTheory.WeilM.thetaSum F (d.rho ψ u' Φ')) 0 := by
  first | exact @GlobalTheory.HeisLineTheta.hasDerivAt_thetaSum_line | exact GlobalTheory.HeisLineTheta.hasDerivAt_thetaSum_line | (intros; apply GlobalTheory.HeisLineTheta.hasDerivAt_thetaSum_line <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharUnramifiedAtCofinitelyManyPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeFinRam

theorem finite_ramified : ∀ (D : D7) (χ : (AE D)ˣ →* Circle), IsHeckeChar D χ →
    {w : HeightOneSpectrum (𝓞 D.host.E) | ¬ GlobalTheory.LFun.UnrAt χ w}.Finite := by
  intro D χ hχ
  obtain ⟨H, hH⟩ := GlobalTheory.HeckeTensorRead.exists_hchar_chrEq D χ hχ
  refine (GlobalTheory.Mem.UnrAe.finite_ramified H).subset fun w hw => ?_
  exact fun h => hw ((GlobalTheory.LFun.unrAt_iff_of_chrEq hH w).2 h)

end GlobalTheory.HeckeFinRam
end

