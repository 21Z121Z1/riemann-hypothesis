import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0818
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0827
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0372
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0410
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0668
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0812

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularisedComparison
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm

namespace GlobalTheory.RegCompare

variable {D : D7}

def wop {M X : HSp D} (ω : WRep M X) (z : GA D M →₀ ℂ) : Module.End ℂ (WO M X → ℂ) := z.sum fun k c => c • ω (k, 1)

section Lin

variable {M X : HSp D} (ω : WRep M X) (ν : Measure (GA D M)) (𝓕 : Set (GA D M))

theorem thetaKO_add (g : GA D M) (h : GA D X) (Φ Ψ : WO M X → ℂ) :
    thetaKO ω g h (Φ + Ψ) = thetaKO ω g h Φ + thetaKO ω g h Ψ := by
  simp [thetaKO, map_add]

theorem thetaKO_smul (g : GA D M) (h : GA D X) (c : ℂ) (Φ : WO M X → ℂ) :
    thetaKO ω g h (c • Φ) = c * thetaKO ω g h Φ := by
  simp [thetaKO, map_smul]

theorem thetaKO_sum {ι : Type} (s : Finset ι) (g : GA D M) (h : GA D X) (Φ : ι → WO M X → ℂ) :
    thetaKO ω g h (∑ i ∈ s, Φ i) = ∑ i ∈ s, thetaKO ω g h (Φ i) := by
  simp [thetaKO, map_sum, Finset.sum_apply]

theorem thetaKO_right (g k : GA D M) (h : GA D X) (Φ : WO M X → ℂ) :
    thetaKO ω g h (ω (k, 1) Φ) = thetaKO ω (g * k) h Φ := by
  unfold thetaKO
  rw [← Module.End.mul_apply, ← map_mul]
  simp

def Intg (Φ : WO M X → ℂ) : Prop := ∀ h : GA D X, IntegrableOn (fun g => thetaKO ω g h Φ) 𝓕 ν

variable {ω ν 𝓕}

theorem Intg.add {Φ Ψ : WO M X → ℂ} (hΦ : Intg ω ν 𝓕 Φ) (hΨ : Intg ω ν 𝓕 Ψ) : Intg ω ν 𝓕 (Φ + Ψ) := fun h => by
  simp only [thetaKO_add]; exact Integrable.add (hΦ h) (hΨ h)

theorem Intg.smul {Φ : WO M X → ℂ} (c : ℂ) (hΦ : Intg ω ν 𝓕 Φ) : Intg ω ν 𝓕 (c • Φ) := fun h => by
  simp only [thetaKO_smul]; exact Integrable.const_mul (hΦ h) c

theorem Intg.sub {Φ Ψ : WO M X → ℂ} (hΦ : Intg ω ν 𝓕 Φ) (hΨ : Intg ω ν 𝓕 Ψ) : Intg ω ν 𝓕 (Φ - Ψ) := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ]; exact hΦ.add (hΨ.smul _)

theorem Intg.sum {ι : Type} (s : Finset ι) {Φ : ι → WO M X → ℂ} (hΦ : ∀ i ∈ s, Intg ω ν 𝓕 (Φ i)) :
    Intg ω ν 𝓕 (∑ i ∈ s, Φ i) := fun h => by
  simp only [thetaKO_sum]
  exact integrable_finset_sum s fun i hi => hΦ i hi h

theorem intg_of_modInt {θ : InfFam D} {Φ : WO M X → ℂ} (hΦ : ModInt θ ω ν 𝓕 Φ) : Intg ω ν 𝓕 Φ := by
  obtain ⟨N, C, hC⟩ := hΦ
  exact fun h => (hC h).1

variable (ω ν 𝓕)

theorem thetaInt_smul (c : ℂ) (Φ : WO M X → ℂ) : thetaInt ω ν 𝓕 (c • Φ) = c • thetaInt ω ν 𝓕 Φ := by
  funext h
  simp only [thetaInt, thetaKO_smul, integral_const_mul, Pi.smul_apply, smul_eq_mul]

variable {ω ν 𝓕}

theorem thetaInt_add {Φ Ψ : WO M X → ℂ} (hΦ : Intg ω ν 𝓕 Φ) (hΨ : Intg ω ν 𝓕 Ψ) :
    thetaInt ω ν 𝓕 (Φ + Ψ) = thetaInt ω ν 𝓕 Φ + thetaInt ω ν 𝓕 Ψ := by
  funext h
  simp only [thetaInt, thetaKO_add, Pi.add_apply]
  exact integral_add (hΦ h) (hΨ h)

theorem thetaInt_sub {Φ Ψ : WO M X → ℂ} (hΦ : Intg ω ν 𝓕 Φ) (hΨ : Intg ω ν 𝓕 Ψ) :
    thetaInt ω ν 𝓕 (Φ - Ψ) = thetaInt ω ν 𝓕 Φ - thetaInt ω ν 𝓕 Ψ := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ Ψ, thetaInt_add hΦ (hΨ.smul _), thetaInt_smul, neg_one_smul, sub_eq_add_neg]

theorem thetaInt_sum {ι : Type} (s : Finset ι) {Φ : ι → WO M X → ℂ} (hΦ : ∀ i ∈ s, Intg ω ν 𝓕 (Φ i)) :
    thetaInt ω ν 𝓕 (∑ i ∈ s, Φ i) = ∑ i ∈ s, thetaInt ω ν 𝓕 (Φ i) := by
  funext h
  simp only [thetaInt, thetaKO_sum, Finset.sum_apply]
  exact integral_finset_sum s fun i hi => hΦ i hi h

end Lin

theorem setIntegral_mul_right' (V : HSp D) (ν : Measure (GA D V)) [hH : ν.IsHaarMeasure] (fd : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) fd ν) (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (hint : IntegrableOn F fd ν) (k : GA D V) :
    IntegrableOn (fun u => F (u * k)) fd ν ∧ ∫ u in fd, F (u * k) ∂ν = ∫ u in fd, F u ∂ν := by
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V ν hH
  have hmp : MeasurePreserving (fun x : GA D V => x * k⁻¹) ν ν := measurePreserving_mul_right ν k⁻¹
  have ht : IsFundamentalDomain (GQ V) ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν :=
    hfd.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by simp [Subgroup.smul_def, mul_assoc])
  have hinv : ∀ (g : GQ V) (x : GA D V), F (g • x) = F x := fun g x => hF g g.2 x
  have hmp2 : MeasurePreserving (fun x : GA D V => x * k) ν ν := measurePreserving_mul_right ν k
  have hpre : (fun x : GA D V => x * k) ⁻¹' ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) = fd := by
    ext x; simp
  have hemb : MeasurableEmbedding (fun x : GA D V => x * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have h1 : IntegrableOn F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν := (hfd.integrableOn_iff ht hinv).1 hint
  have e1 : ∫ u in fd, F (u * k) ∂ν = ∫ u in (fun x : GA D V => x * k⁻¹) ⁻¹' fd, F u ∂ν := by
    have := hmp2.setIntegral_preimage_emb hemb F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd)
    rw [hpre] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [← hpre]
    exact (hmp2.integrableOn_comp_preimage hemb).2 h1
  · rw [e1]; exact (hfd.setIntegral_eq ht hinv).symm

theorem modInt_right {θ : InfFam D} {M X : HSp D} {ω : WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : ModInt θ ω ν 𝓕 Φ) (k : GA D M) :
    ModInt θ ω ν 𝓕 (ω (k, 1) Φ) ∧ thetaInt ω ν 𝓕 (ω (k, 1) Φ) = thetaInt ω ν 𝓕 Φ := by
  haveI := hν.1
  obtain ⟨N, C, hC⟩ := hΦ
  have key := fun h => setIntegral_mul_right' M ν 𝓕 hν.2 (fun g => thetaKO ω g h Φ)
    (fun γ hγ u => hL γ hγ u h) (hC h).1 k
  have keyn := fun h => setIntegral_mul_right' M ν 𝓕 hν.2 (fun g => ((‖thetaKO ω g h Φ‖ : ℝ) : ℂ))
    (fun γ hγ u => by simp only [hL γ hγ u h]) (hC h).1.norm.ofReal k
  refine ⟨⟨N, C, fun h => ⟨?_, ?_⟩⟩, ?_⟩
  · simpa only [thetaKO_right] using (key h).1
  · have e : ∫ g in 𝓕, ‖thetaKO ω g h (ω (k, 1) Φ)‖ ∂ν = ∫ g in 𝓕, ‖thetaKO ω g h Φ‖ ∂ν := by
      have := (keyn h).2
      simp only [integral_complex_ofReal] at this
      simpa only [thetaKO_right] using Complex.ofReal_injective this
    rw [e]; exact (hC h).2
  · funext h
    simp only [thetaInt, thetaKO_right]
    exact (key h).2

theorem wop_apply {M X : HSp D} (ω : WRep M X) (z : GA D M →₀ ℂ) (Φ : WO M X → ℂ) :
    wop ω z Φ = ∑ k ∈ z.support, z k • ω (k, 1) Φ := by
  simp [wop, Finsupp.sum, LinearMap.sum_apply]

theorem wop_mem {M X : HSp D} {ω : WRep M X} {S : Submodule ℂ (WO M X → ℂ)} (hS : ∀ g ∈ GfC M, ∀ Φ ∈ S, ω (g, 1) Φ ∈ S)
    {z : GA D M →₀ ℂ} (hz : ∀ k ∈ z.support, k ∈ GfC M) {Φ : WO M X → ℂ} (hΦ : Φ ∈ S) : wop ω z Φ ∈ S := by
  rw [wop_apply]
  exact S.sum_mem fun k hk => S.smul_mem _ (hS k (hz k hk) Φ hΦ)

theorem thetaInt_wop {θ : InfFam D} {M X : HSp D} {ω : WRep M X} {ν : Measure (GA D M)} {𝓕 : Set (GA D M)}
    (hν : IsHaarFD M ν 𝓕) {Φ : WO M X → ℂ} (hL : ∀ γ ∈ GQ M, ∀ g h, thetaKO ω (γ * g) h Φ = thetaKO ω g h Φ)
    (hΦ : ModInt θ ω ν 𝓕 Φ) (z : GA D M →₀ ℂ) :
    Intg ω ν 𝓕 (wop ω z Φ) ∧ thetaInt ω ν 𝓕 (wop ω z Φ) = GlobalTheory.FunObj.zdeg z • thetaInt ω ν 𝓕 Φ := by
  have hk := fun k => modInt_right hν hL hΦ k
  rw [wop_apply]
  refine ⟨Intg.sum _ fun k _ => (intg_of_modInt (hk k).1).smul _, ?_⟩
  rw [thetaInt_sum _ fun k _ => (intg_of_modInt (hk k).1).smul _]
  simp only [thetaInt_smul, (hk _).2, GlobalTheory.FunObj.zdeg, Finsupp.sum, Finset.sum_smul]

theorem reg_of_const : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ ν 𝓕 ν₁ 𝓕₁, IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ c₀ : ℂ, (∀ Φ' ∈ algF ψ θ false A₁ B, ∃ Φ₀ ∈ algF ψ θ false A₁ B,
        Φ' - Φ₀ ∈ finRel ωB (algF ψ θ false A₁ B) ∧ ModInt θ ωB ν₁ 𝓕₁ Φ₀ ∧
        ∀ Φ ∈ algF ψ θ true A B, p Φ = p' Φ₀ → thetaInt ωA ν 𝓕 Φ = c₀ • thetaInt ωB ν₁ 𝓕₁ Φ₀) →
    ∀ ΦB ∈ algF ψ θ false A₁ B, ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁) ∧ GlobalTheory.FunObj.zdeg z ≠ 0 ∧
      wop ωB z ΦB ∈ algF ψ θ false A₁ B ∧ ModInt θ ωB ν₁ 𝓕₁ (wop ωB z ΦB) ∧
      ∀ Φ ∈ algF ψ θ true A B, p Φ = GlobalTheory.FunObj.zdeg z • p' ΦB →
        thetaInt ωA ν 𝓕 Φ = c₀ • thetaInt ωB ν₁ 𝓕₁ (wop ωB z ΦB) := by
  intro hP hK D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm c₀ H ΦB hΦB
  set S := algF ψ θ false A₁ B with hSdef
  have hstab : ∀ g ∈ GfC W₁, ∀ Φ ∈ S, ωB (g, 1) Φ ∈ S := hm.mapB.stabM.1
  have hL : ∀ Φ ∈ S, ∀ γ ∈ GQ W₁, ∀ g h, thetaKO ωB (γ * g) h Φ = thetaKO ωB g h Φ :=
    GlobalTheory.T.thetaKernel_leftInvariant_rational_unitary D ψ θ hθ W₁ X A₁ B α (α / β) ωB hm.weilB
  obtain ⟨Φ₀, h0S, hrel, hmod0, hI⟩ := H ΦB hΦB
  have hp : p' ΦB = p' Φ₀ := by
    have h1 : finRel ωB S ≤ LinearMap.ker p' := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, hu, Ψ, hΨ, rfl⟩
      show p' _ = 0
      rw [map_sub, hm.mapB.invf u hu Ψ hΨ, sub_self]
    have := h1 hrel
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
  rw [finRel, Submodule.mem_span_set'] at hrel
  obtain ⟨n, c, g, hsum⟩ := hrel
  choose u hu Ψ hΨ hg using fun i => (g i).2
  obtain ⟨z, hzG, hz0, hz⟩ := GlobalTheory.T.seesaw_identity_weil_triple hP hK D ψ θ hθ W W₁ X A₁ B α β hT ν₁ 𝓕₁ hν₁ ωB hm.weilB (n + 1)
    (Fin.cons ΦB Ψ) (Fin.cons 1 u) (Fin.cases hΦB hΨ) (Fin.cases (one_mem _) hu)
  have hB : ModInt θ ωB ν₁ 𝓕₁ (wop ωB z ΦB) := (hz 0).1
  have hX : ∀ i, ModInt θ ωB ν₁ 𝓕₁ (wop ωB z (Ψ i)) ∧
      ∃ u' ∈ GfC W₁, wop ωB z (ωB (u i, 1) (Ψ i)) = ωB (u', 1) (wop ωB z (Ψ i)) := fun i => hz i.succ
  choose u' hu' hcomm using fun i => (hX i).2
  have hXS : ∀ i, wop ωB z (Ψ i) ∈ S := fun i => wop_mem hstab hzG (hΨ i)
  have hXr := fun i => modInt_right hν₁ (hL _ (hXS i)) (hX i).1 (u' i)
  have h0 := thetaInt_wop hν₁ (hL _ h0S) hmod0 z

  have eB : ΦB = Φ₀ + ∑ i, c i • (ωB (u i, 1) (Ψ i) - Ψ i) := by
    have e : ∑ i, c i • (g i : WO W₁ X → ℂ) = ∑ i, c i • (ωB (u i, 1) (Ψ i) - Ψ i) := by simp only [hg]
    rw [← e, hsum]; abel
  have eW : wop ωB z ΦB = wop ωB z Φ₀ + ∑ i, c i • (ωB (u' i, 1) (wop ωB z (Ψ i)) - wop ωB z (Ψ i)) := by
    rw [eB, map_add, map_sum]
    simp only [map_smul, map_sub, hcomm]
  have hJ : thetaInt ωB ν₁ 𝓕₁ (wop ωB z ΦB) = GlobalTheory.FunObj.zdeg z • thetaInt ωB ν₁ 𝓕₁ Φ₀ := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        Intg ωB ν₁ 𝓕₁ (c i • (ωB (u' i, 1) (wop ωB z (Ψ i)) - wop ωB z (Ψ i))) := fun i _ =>
      ((intg_of_modInt (hXr i).1).sub (intg_of_modInt (hX i).1)).smul _
    rw [eW, thetaInt_add h0.1 (Intg.sum _ hi), thetaInt_sum _ hi, h0.2]
    simp only [thetaInt_smul, thetaInt_sub (intg_of_modInt (hXr _).1) (intg_of_modInt (hX _).1), (hXr _).2, sub_self,
      smul_zero, Finset.sum_const_zero, add_zero]
  refine ⟨z, hzG, hz0, wop_mem hstab hzG hΦB, hB, fun Φ hΦ hpΦ => ?_⟩
  have hΦ₁ : (GlobalTheory.FunObj.zdeg z)⁻¹ • Φ ∈ algF ψ θ true A B := Submodule.smul_mem _ _ hΦ
  have hp₁ : p ((GlobalTheory.FunObj.zdeg z)⁻¹ • Φ) = p' Φ₀ := by
    rw [map_smul, hpΦ, smul_smul, inv_mul_cancel₀ hz0, one_smul, hp]
  have e1 := hI _ hΦ₁ hp₁
  have e2 : Φ = GlobalTheory.FunObj.zdeg z • ((GlobalTheory.FunObj.zdeg z)⁻¹ • Φ) := by rw [smul_smul, mul_inv_cancel₀ hz0, one_smul]
  rw [e2, thetaInt_smul, e1, hJ, smul_comm]

theorem regularised_comparison : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.ThetaIntegralsAgree →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ ν 𝓕 ν₁ 𝓕₁, IsHaarFD W ν 𝓕 → IsHaarFD W₁ ν₁ 𝓕₁ →
    ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∃ c₀ : ℂ, c₀ ≠ 0 ∧ ∀ ΦB ∈ algF ψ θ false A₁ B, ∃ z : GA D W₁ →₀ ℂ, (∀ k ∈ z.support, k ∈ GfC W₁) ∧
      GlobalTheory.FunObj.zdeg z ≠ 0 ∧ wop ωB z ΦB ∈ algF ψ θ false A₁ B ∧ ModInt θ ωB ν₁ 𝓕₁ (wop ωB z ΦB) ∧
      ∀ Φ ∈ algF ψ θ true A B, p Φ = GlobalTheory.FunObj.zdeg z • p' ΦB →
        thetaInt ωA ν 𝓕 Φ = c₀ • thetaInt ωB ν₁ 𝓕₁ (wop ωB z ΦB) := by
  intro hP hK hS D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm
  obtain ⟨c, hc, H⟩ := hS D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm
  exact ⟨c, hc, reg_of_const hP hK D ψ θ hθ W W₁ X A A₁ B α β hT ν 𝓕 ν₁ 𝓕₁ hν hν₁ ωA ωB Pi rf rl p p' hm c H⟩

end GlobalTheory.RegCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilArchimedeanFactor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleAssembly.EqFin

theorem liftPure_pure {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ) {P : Type} [AddCommGroup P] [Module ℂ P]
    (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v) (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ) (hφ : ∀ v, φ v ∈ GlobalTheory.WeilM.SB _)
    (hφv : ∀ᶠ v in Filter.cofinite, φ v = M.vac v) :
    GlobalTheory.TripleAssembly.liftPure M pr pv s (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      pr f ⊗ₜ GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)) := by
  have H := GlobalTheory.PureLift.exists_pureLift σ Y Z M ψ hM P pr N pv s hs
  unfold GlobalTheory.TripleAssembly.liftPure
  rw [dif_pos H]
  exact H.choose_spec f φ hφ hφv

theorem darbAlg_stable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Z)
    (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver (E := E) w) (hM : M.IsGood ψ)
    {P : Type} [AddCommGroup P] [Module ℂ P] (pr : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d) →ₗ[ℂ] P)
    {N : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F → Type} [∀ v, AddCommGroup (N v)] [∀ v, Module ℂ (N v)]
    (pv : ∀ v, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] N v) (s : ∀ v, N v)
    (hs : ∀ᶠ v in Filter.cofinite, pv v (M.vac v) = s v)
    (O : Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) (T₀ : Module.End ℂ (GlobalTheory.SmallThetaModules.RTens s))
    (hgen : ∀ (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) →
      ∃ φ₁ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ,
        (∀ v, φ₁ v ∈ GlobalTheory.WeilM.SB _) ∧ (∀ᶠ v in Filter.cofinite, φ₁ v = M.vac v) ∧
        O (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ₁ ∧
        GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ₁ v)) = T₀ (GlobalTheory.SmallThetaModules.pureT s (fun v => pv v (φ v)))) :
    ∀ Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ, O Ψ ∈ GlobalTheory.TripleAssembly.darbAlg M ψ τ ∧
      GlobalTheory.TripleAssembly.liftPure M pr pv s (O Ψ) = LinearMap.lTensor P T₀ (GlobalTheory.TripleAssembly.liftPure M pr pv s Ψ) := by
  intro Ψ hΨ
  induction hΨ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, φ, hf, hφ, hφv, rfl⟩ := hx
    obtain ⟨φ₁, h1, h1v, hO, hT⟩ := hgen f φ hφ hφv
    refine ⟨?_, ?_⟩
    · rw [hO]; exact Submodule.subset_span ⟨f, φ₁, hf, h1, h1v, rfl⟩
    · rw [hO, liftPure_pure M ψ hM pr pv s hs f φ₁ h1 h1v, liftPure_pure M ψ hM pr pv s hs f φ hφ hφv,
        LinearMap.lTensor_tmul, hT]
  | zero => simp
  | add x y _ _ hx hy =>
    refine ⟨?_, ?_⟩
    · rw [map_add]; exact Submodule.add_mem _ hx.1 hy.1
    · simp only [map_add, hx.2, hy.2]
  | smul c x _ hx =>
    refine ⟨?_, ?_⟩
    · rw [map_smul]; exact Submodule.smul_mem _ c hx.1
    · simp only [map_smul, hx.2]

end GlobalTheory.TripleAssembly.EqFin

namespace GlobalTheory.TripleAssembly.EqFin

set_option maxHeartbeats 2000000 in

theorem mapA_mapB_equivariant_fin : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        (∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
          ∀ g ∈ GfC X, ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (1, g) Φ) = GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨oA, -⟩ := GlobalTheory.T.algF_map_mapA_and_mapB_eq_top hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨⟨dA, rA⟩, ⟨dB, rB⟩⟩ :=
    GlobalTheory.T.seesaw_weil_zeta_residue hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have gM : Γ.M.IsGood Bs.ψ := hM.triple.geo.hM
  have gM' : Γ.M'.IsGood Bs.ψ := hM.triple.geo.hM'
  have c1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW 1 = 1 := Subtype.ext ((congrArg _ (map_one (matHom W))).trans (map_one _))
  have c1' : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁ 1 = 1 := Subtype.ext ((congrArg _ (map_one (matHom W₁))).trans (map_one _))
  have hsA : ∀ᶠ v in Filter.cofinite, Rf.p v (Γ.M.vac v) = GlobalTheory.TripleAssembly.vacIm Γ Rf v :=
    Filter.Eventually.of_forall fun v => rfl
  have hsB : ∀ᶠ v in Filter.cofinite, Rf.p' v (Γ.M'.vac v) = GlobalTheory.TripleAssembly.vacIm Γ Rf v := by
    refine Filter.eventually_cofinite.2 ((Xc.T.finite_toSet).subset fun v hv => ?_)
    by_contra hn
    exact hv (hM.fin.sph v hn).1.symm
  have key : ∀ g ∈ GfC X, ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      (∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) ∧
      ∀ Φ ∈ algF ψ θ false A₁ B, GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (ωB (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf Φ) := by
    intro g hg
    obtain ⟨hv, hvU, fA, fB⟩ := GlobalTheory.T.matched_maps_doubling_frame hP D W W₁ X e Bs Γ Xc om om' R Rf hM h.JX g hg
    choose a ha using fun v => GlobalTheory.T.exists_localOperator_thetaQuotient_finitePlace D.sp.cm.sig W.rank W₁.rank Bs Γ Xc om om' R Rf hM v (hv v) (hvU v)
    obtain ⟨T₀, hT₀⟩ := GlobalTheory.TripleAssembly.exists_rtensOp (GlobalTheory.TripleAssembly.vacIm Γ Rf) a
    refine ⟨LinearMap.lTensor R.Pi T₀, ?_, ?_⟩
    · have st := GlobalTheory.TripleAssembly.EqFin.darbAlg_stable Γ.M Bs.ψ Bs.emb gM R.p Rf.p (GlobalTheory.TripleAssembly.vacIm Γ Rf) hsA
        (om (1, GlobalTheory.TripleRead.toUX X e h.JX g)) T₀ (fun f φ hφ hφv => by
          obtain ⟨φ₁, h1, h1v, hAct, hO⟩ := fA f φ hφ hφv
          refine ⟨φ₁, h1, h1v, hO, ?_⟩
          rw [hT₀ _ (Filter.eventually_cofinite.1 ((hφv.and hsA).mono fun v hv' => by rw [hv'.1, hv'.2]))]
          congr 1
          funext v
          exact (ha v).1 (φ v) (hφ v) (φ₁ v) (h1 v) (hAct v))
      intro Φ hΦ
      obtain ⟨Ψ, hΨ, rfl⟩ := rA Φ hΦ
      have hs := GlobalTheory.TripleAssembly.darbAlg_le_schA D.sp.cm.sig Γ.V Γ.W Γ.M Bs.ψ Bs.emb gM hΨ
      have e1 := hTA Ψ hs 1 g
      rw [c1] at e1
      have s1 := (st Ψ hΨ).1
      have s2 := (st Ψ hΨ).2
      have d1 := dA _ s1
      have d2 := dA Ψ hΨ
      have x1 := congrArg (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) e1.symm
      have x2 := congrArg (LinearMap.lTensor R.Pi T₀) d2.symm
      exact x1.trans (d1.trans (s2.trans x2))
    · have st := GlobalTheory.TripleAssembly.EqFin.darbAlg_stable Γ.M' Bs.ψ Bs.emb gM' R.p' Rf.p' (GlobalTheory.TripleAssembly.vacIm Γ Rf) hsB
        (om' (1, GlobalTheory.TripleRead.toUX X e h.JX g)) T₀ (fun f φ hφ hφv => by
          obtain ⟨φ₁, h1, h1v, hAct, hO⟩ := fB f φ hφ hφv
          refine ⟨φ₁, h1, h1v, hO, ?_⟩
          rw [hT₀ _ (Filter.eventually_cofinite.1 ((hφv.and hsB).mono fun v hv' => by rw [hv'.1, hv'.2]))]
          congr 1
          funext v
          exact (ha v).2 (φ v) (hφ v) (φ₁ v) (h1 v) (hAct v))
      intro Φ hΦ
      obtain ⟨Ψ, hΨ, rfl⟩ := rB Φ hΦ
      have hs := GlobalTheory.TripleAssembly.darbAlg_le_schA D.sp.cm.sig Γ.V' Γ.W Γ.M' Bs.ψ Bs.emb gM' hΨ
      have e1 := hTB Ψ hs 1 g
      rw [c1'] at e1
      exact (congrArg (GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf) e1.symm).trans ((dB _ (st Ψ hΨ).1).trans
        (((st Ψ hΨ).2).trans (congrArg (LinearMap.lTensor R.Pi T₀) (dB Ψ hΨ).symm)))
  have opEq : ∀ g, ∀ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf),
      (∀ Φ ∈ algF ψ θ true A B, GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) =
        T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ)) →
      GlobalTheory.TripleAssembly.opFin ωA (algF ψ θ true A B) (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) g = T := by
    intro g T hTg
    have H : ∃ T : Module.End ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf), ∀ Φ ∈ algF ψ θ true A B,
        GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf (ωA (1, g) Φ) = T (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf Φ) := ⟨T, hTg⟩
    unfold GlobalTheory.TripleAssembly.opFin
    rw [dif_pos H]
    apply LinearMap.ext
    intro y
    have hy : y ∈ (algF ψ θ true A B).map (GlobalTheory.TripleAssembly.mapA ψ e Bs Γ R Rf) := by rw [oA]; trivial
    obtain ⟨Φ, hΦ, rfl⟩ := hy
    rw [← H.choose_spec Φ hΦ, hTg Φ hΦ]
  refine ⟨fun g hg Φ hΦ => ?_, fun g hg Φ hΦ => ?_⟩
  · obtain ⟨T, h1, -⟩ := key g hg
    rw [opEq g T h1]
    exact h1 Φ hΦ
  · obtain ⟨T, h1, h2⟩ := key g hg
    rw [opEq g T h1]
    exact h2 Φ hΦ

end GlobalTheory.TripleAssembly.EqFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawWeilZetaArchimedeanStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_weil_zeta_archimedean : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
      ∀ (m : ℕ) (f : Fin m → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf D.host.F (Fin W₁.rank × Fin (W.rank + W₁.rank)))
        (φ : Fin m → ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl D.host.F, (Fin W₁.rank × Fin (W.rank + W₁.rank) → Fv D.host.F v) → ℂ),
        (∀ i, (∀ v, φ i v ∈ GlobalTheory.WeilM.SB _) ∧ ∀ᶠ v in Filter.cofinite, φ i v = Γ.M'.vac v) →
        (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i)) ∈ GlobalTheory.TripleAssembly.darbAlg Γ.M' Bs.ψ Bs.emb →
        GlobalTheory.TripleAssembly.mapB ψ e Bs Γ R Rf (GlobalTheory.TripleRead.thO Γ.M' ψ (sgn false W₁).gram e (∑ i, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f i) (φ i))) =
          ∑ i, R.p' (f i) ⊗ₜ[ℂ] GlobalTheory.SmallThetaModules.pureT (GlobalTheory.TripleAssembly.vacIm Γ Rf) (fun v => Rf.p' v (φ i v)) := by
  first | exact @GlobalTheory.TripleAssembly.mapB_thO_pure | exact GlobalTheory.TripleAssembly.mapB_thO_pure | (intros; apply GlobalTheory.TripleAssembly.mapB_thO_pure <;> assumption)
end

