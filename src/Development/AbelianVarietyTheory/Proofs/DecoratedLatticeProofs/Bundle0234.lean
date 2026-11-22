import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0213
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0211
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActOMemFinSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0198
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0207
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0185
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLine
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaIntegralConjCuspFormParameterTransfer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ChainOnto

theorem isParamVec_of_injective_equivariant {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {L : Submodule (𝓞 E) (Fin n → E)}
    {v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)} {w : IsDedekindDomain.HeightOneSpectrum (𝓞 E)}
    {h : w.under (𝓞 F) = v} {X Y : Type} [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    {ρ : Representation ℂ (GLoc σ J v) X} {ρ' : Representation ℂ (GLoc σ J v) Y} (f : X →ₗ[ℂ] Y)
    (hf : ∀ g y, f (ρ g y) = ρ' g (f y)) (hi : Function.Injective f) {x : X} {B : Multiset ℂˣ}
    (hx : GlobalTheory.LFun.IsParamVec σ J L h ρ' (f x) B) : GlobalTheory.LFun.IsParamVec σ J L h ρ x B := by
  rcases hx with ⟨hv, e, he, hx⟩ | ⟨hw, c, ϖ, e, α, hU, he, hx, hB⟩
  · exact Or.inl ⟨hv, e, he, GlobalTheory.LFun.IsSatVecGL.of_map f (fun g y => hf _ y) hi hx⟩
  · exact Or.inr ⟨hw, c, ϖ, e, α, hU, he, GlobalTheory.LFun.IsSatVecU.of_map hU f (fun g y => hf _ y) hi hx, hB⟩

theorem thetaKO_om_apply {D : D7} {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g a : GA D S)
    (x a' : GA D T) (u : WO S T → ℂ) : thetaKO om g x (om (a, a') u) = thetaKO om (g * a) (x * a') u := by
  simp only [thetaKO, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk]

theorem thetaKO_left {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om) {u : WO S T → ℂ}
    (hu : IsThetaFunO ψ S T u) (γ : GA D S) (hγ : γ ∈ GQ S) (g : GA D S) (x : GA D T) :
    thetaKO om (γ * g) x u = thetaKO om g x u := by
  have e : ((γ * g, x) : GA D S × GA D T) = (γ, 1) * (g, x) := by simp
  simp only [thetaKO, e, map_mul, Module.End.mul_apply]
  exact hW.om_aut γ hγ 1 (one_mem _) _ (hW.om_pres _ _ hu)

theorem thetaIntegral_param : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, TransferOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ t : ℕ, T.rank = S.rank + t → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → ∀ (v : HeightOneSpectrum (𝓞 D.host.F)), (∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = v → UnrAt χS w' ∧ UnrAt χT w') → ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v) (f : WO S T → ℂ), VacFin ψ S T v f → ∀ (y : GA D S → ℂ) (B : Multiset ℂˣ), IsAutFunSm θ S y → IsCuspFun S y → IsParamVec D.sp.cm.sig S.gram (frameLat S) h ((rightReg ℂ (GA D S) ℂ).comp (embV S v)) (fun g => conj (y g)) B → (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) ≠ 0 → IsParamVec D.sp.cm.sig T.gram (frameLat T) h ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) (fun x => ∫ g in 𝓕, thetaKO om g x f * conj (y g) ∂ν) (stepPar χS χT t (fun _ => B) w) := by
  intro hP D hT ψ θ S T χS χT om hθ hW t ht ν 𝓕 hν h𝓕 v hunr w h f hf y B hy hc hB hne
  let U : Submodule ℂ (WO S T → ℂ) := GlobalTheory.FinWeilO.thetaSub ψ S T
  have hU : ∀ a a', ∀ u ∈ U, om (embV S v a, embV T v a') u ∈ U := fun a a' u hu => hW.om_pres _ u hu
  let ρ0 : Representation ℂ (Gv S v) (GA D S → ℂ) := (rightReg ℂ (GA D S) ℂ).comp (embV S v)
  have hρ0 : ∀ a (z : GA D S → ℂ) g, ρ0 a z g = z (g * embV S v a) := fun _ _ _ => rfl
  let cy : GA D S → ℂ := fun g => conj (y g)
  let X : Submodule ℂ (GA D S → ℂ) := Submodule.span ℂ (Set.range fun a : Gv S v => ρ0 a cy)
  have hX : ∀ a, ∀ z ∈ X, ρ0 a z ∈ X := by
    intro a z hz
    have hle : Submodule.map (ρ0 a) X ≤ X := by
      rw [Submodule.map_span_le]
      rintro _ ⟨b, rfl⟩
      rw [← Module.End.mul_apply, ← map_mul]
      exact Submodule.subset_span ⟨a * b, rfl⟩
    exact hle ⟨z, hz, rfl⟩
  let ρ : Representation ℂ (Gv S v) X := GlobalTheory.PRep.sub ρ0 X hX
  have hcy : cy ∈ X := Submodule.subset_span ⟨1, by simp⟩
  have hXp : ∀ z ∈ X, (∀ u, IsThetaFunO ψ S T u → ∀ x, IntegrableOn (fun g => thetaKO om g x u * z g) 𝓕 ν) ∧
      (∀ γ ∈ GQ S, ∀ g, z (γ * g) = z g) := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, rfl⟩ := hz
      refine ⟨fun u hu x => GlobalTheory.T.thetaKernel_mul_conj_cuspForm_integrableOn hP D ψ S T χS χT om hW θ hθ ν 𝓕 hν h𝓕 u y hu hy hc (embV S v a) x,
        fun γ hγ g => ?_⟩
      show conj (y (γ * g * embV S v a)) = conj (y (g * embV S v a))
      rw [mul_assoc, hy.left γ hγ]
    | zero => exact ⟨fun u _ x => by simp, fun _ _ _ => rfl⟩
    | add z z' _ _ h1 h2 =>
      refine ⟨fun u hu x => ?_, fun γ hγ g => by simp [h1.2 γ hγ, h2.2 γ hγ]⟩
      rw [show (fun g => thetaKO om g x u * (z + z') g) = fun g => thetaKO om g x u * z g + thetaKO om g x u * z' g from
        funext fun g => by simp [mul_add]]
      exact (h1.1 u hu x).add (h2.1 u hu x)
    | smul c z _ h1 =>
      refine ⟨fun u hu x => ?_, fun γ hγ g => by simp [h1.2 γ hγ]⟩
      rw [show (fun g => thetaKO om g x u * (c • z) g) = fun g => c * (thetaKO om g x u * z g) from
        funext fun g => by simp [mul_left_comm]]
      exact (h1.1 u hu x).const_mul c
  let bf : U → X → GA D T → ℂ := fun u z x => ∫ g in 𝓕, thetaKO om g x (u : WO S T → ℂ) * (z : GA D S → ℂ) g ∂ν
  let b : U →ₗ[ℂ] X →ₗ[ℂ] (GA D T → ℂ) := LinearMap.mk₂ ℂ bf
    (fun u u' z => by
      funext x
      show _ = bf u z x + bf u' z x
      simp only [bf, ← integral_add ((hXp z z.2).1 u u.2 x) ((hXp z z.2).1 u' u'.2 x)]
      congr 1; funext g
      simp [thetaKO, add_mul])
    (fun c u z => by
      funext x
      show _ = c * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [thetaKO, mul_assoc])
    (fun u z z' => by
      funext x
      show _ = bf u z x + bf u z' x
      simp only [bf, ← integral_add ((hXp z z.2).1 u u.2 x) ((hXp z' z'.2).1 u u.2 x)]
      congr 1; funext g
      simp [mul_add])
    (fun c u z => by
      funext x
      show _ = c * bf u z x
      simp only [bf, ← integral_const_mul]
      congr 1; funext g
      simp [mul_left_comm])
  have hb : ∀ a a' (u : U) (z : X), b ⟨om (embV S v a, embV T v a') u, hU a a' u u.2⟩ (ρ a z) =
      (rightReg ℂ (GA D T) ℂ).comp (embV T v) a' (b u z) := by
    intro a a' u z
    funext x
    show ∫ g in 𝓕, thetaKO om g x (om (embV S v a, embV T v a') u) * (z : GA D S → ℂ) (g * embV S v a) ∂ν =
      ∫ g in 𝓕, thetaKO om g (x * embV T v a') (u : WO S T → ℂ) * (z : GA D S → ℂ) g ∂ν
    simp_rw [thetaKO_om_apply]
    exact GlobalTheory.T.setIntegral_fundamentalDomain_right_translate_invariant D S ν 𝓕 hν h𝓕 (fun g => thetaKO om g (x * embV T v a') (u : WO S T → ℂ) * (z : GA D S → ℂ) g)
      (fun γ hγ g => by simp only [thetaKO_left hW u.2 γ hγ, (hXp z z.2).2 γ hγ]) (embV S v a)
  have hx : GlobalTheory.LFun.IsParamVec D.sp.cm.sig S.gram (frameLat S) h ρ ⟨cy, hcy⟩ B :=
    isParamVec_of_injective_equivariant X.subtype (fun _ _ => rfl) Subtype.val_injective hB
  exact hT ψ S T χS χT om hW t ht v trivial hunr w h U hU ⟨f, hf.1⟩ hf X ρ ⟨cy, hcy⟩ B hx (GA D T → ℂ)
    ((rightReg ℂ (GA D T) ℂ).comp (embV T v)) b hb hne

end GlobalTheory.ChainOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelExistsForContinuous
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW

noncomputable section

namespace GlobalTheory.Core.Rk.Collect

variable {D : D7}

theorem theta_sum {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) : IsThetaFunO ψ S T (∑ i ∈ s, c i • f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ S T
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul _ (hf i)) ih

theorem lin_sum {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (Λ : (WO S T → ℂ) → ℂ) (f₀ : WO S T → ℂ)
    (h₀ : IsThetaFunO ψ S T f₀)
    (hadd : ∀ f f', IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → Λ (f + f') = Λ f + Λ f')
    (hsmul : ∀ (c : ℂ) f, IsThetaFunO ψ S T f → Λ (c • f) = c * Λ f)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (f : ι → WO S T → ℂ) (hf : ∀ i, IsThetaFunO ψ S T (f i)) :
    Λ (∑ i ∈ s, c i • f i) = ∑ i ∈ s, c i * Λ (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h := hsmul 0 f₀ h₀
    simpa using h
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi,
      hadd _ _ (GlobalTheory.LocMod.LinSpace.isThetaFunO_smul _ (hf i)) (theta_sum s c f hf), hsmul _ _ (hf i), ih]

theorem local_rep {ψ : AddChar (AF D.host.F) ℂ} {A W : HSp D} {χS χT : (AE D)ˣ →* Circle} {omh : WRep (dblSp A) W}
    (hW : IsWeilDatumO ψ (dblSp A) W χS χT omh) {φ : WO (dblSp A) W → ℂ} (hφ : IsThetaFunO ψ (dblSp A) W φ)
    {K : Set (GA D A)}
    (hfd : FiniteDimensional ℂ (Submodule.span ℂ
      {f : WO (dblSp A) W → ℂ | ∃ g₁ ∈ K, ∃ g₂ ∈ K, f = omh (io A (g₁, g₂), 1) φ})) :
    ∃ (n : ℕ) (b : Fin n → WO (dblSp A) W → ℂ) (c : Fin n → GA D A × GA D A → ℂ),
      (∀ j, IsThetaFunO ψ (dblSp A) W (b j)) ∧ (∀ j, ContinuousOn (c j) (K ×ˢ K)) ∧
      ∀ x ∈ K ×ˢ K, omh (io A x, 1) φ = ∑ j, c j x • b j := by
  classical
  set V := Submodule.span ℂ {f : WO (dblSp A) W → ℂ | ∃ g₁ ∈ K, ∃ g₂ ∈ K, f = omh (io A (g₁, g₂), 1) φ} with hV
  have hmem : ∀ x ∈ K ×ˢ K, omh (io A x, 1) φ ∈ V := fun x hx =>
    Submodule.subset_span ⟨x.1, hx.1, x.2, hx.2, rfl⟩
  have hth : ∀ f ∈ V, IsThetaFunO ψ (dblSp A) W f := by
    intro f hf
    induction hf using Submodule.span_induction with
    | mem f hf => obtain ⟨g₁, -, g₂, -, rfl⟩ := hf; exact hW.om_pres _ _ hφ
    | zero => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_zero ψ _ _
    | add f g _ _ hf hg => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_add hf hg
    | smul c f _ hf => exact GlobalTheory.LocMod.LinSpace.isThetaFunO_smul c hf
  let b := Module.finBasis ℂ V
  refine ⟨Module.finrank ℂ V, fun j => (b j : WO (dblSp A) W → ℂ),
    fun j x => if h : omh (io A x, 1) φ ∈ V then b.coord j ⟨_, h⟩ else 0, fun j => hth _ (b j).2,
    fun j => ?_, fun x hx => ?_⟩
  · rw [continuousOn_iff_continuous_restrict]
    have hQ : Continuous fun y : K ×ˢ K => (⟨omh (io A y.1, 1) φ, hmem y.1 y.2⟩ : V) := by
      refine Continuous.subtype_mk (continuous_pi fun w => ?_) _
      exact ((hW.om_cont φ hφ w).comp ((continuous_io A).prodMk continuous_const)).comp continuous_subtype_val
    have hcoord : Continuous (b.coord j) := LinearMap.continuous_of_finiteDimensional _
    refine (hcoord.comp hQ).congr fun y => ?_
    simp only [Set.restrict_apply, Function.comp_apply, dif_pos (hmem y.1 y.2)]
  · have e := congrArg Subtype.val (b.sum_repr ⟨_, hmem x hx⟩)
    simp only [Submodule.coe_sum, Submodule.coe_smul] at e
    conv_lhs => rw [← e]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [dif_pos (hmem x hx), Module.Basis.coord_apply]

theorem continuous_of_compact_sq {X Y : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [TopologicalSpace Y]
    (G : X × X → Y) (h : ∀ K : Set X, IsCompact K → ContinuousOn G (K ×ˢ K)) : Continuous G := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨N₁, hc₁, hN₁⟩ := exists_compact_mem_nhds x.1
  obtain ⟨N₂, hc₂, hN₂⟩ := exists_compact_mem_nhds x.2
  exact (h _ (hc₁.union hc₂)).continuousAt
    (prod_mem_nhds (Filter.mem_of_superset hN₁ Set.subset_union_left)
      (Filter.mem_of_superset hN₂ Set.subset_union_right))

end GlobalTheory.Core.Rk.Collect

namespace GlobalTheory.Core.Rk.Collect

theorem dblInt_collect : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A : HSp D) (cA : CptF A) (a : GL (Fin A.rank) (AE D)), Defin θ A cA a → ∀ (W : HSp D) (χ : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) W), IsWeilDatumO ψ (dblSp A) W 1 χ omh → ∀ φ, IsThetaFunO ψ (dblSp A) W φ → IsKFinVec omh (Khat A a) φ → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u : GA D A → ℂ, Continuous u → (∀ γ ∈ GQ A, ∀ g, u (γ * g) = u g) → ∃ φ', IsThetaFunO ψ (dblSp A) W φ' ∧ ∀ Λ : (WO (dblSp A) W → ℂ) → ℂ, (∀ f f', IsThetaFunO ψ (dblSp A) W f → IsThetaFunO ψ (dblSp A) W f' → Λ (f + f') = Λ f + Λ f') → (∀ (c : ℂ) f, IsThetaFunO ψ (dblSp A) W f → Λ (c • f) = c * Λ f) → (∀ γ ∈ GQ (dblSp A), ∀ g, Λ (omh (γ * g, 1) φ) = Λ (omh (g, 1) φ)) → GlobalTheory.Eis.dblInt A χ⁻¹ m (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g)) (fun g => conj (u g)) = Λ φ' := by
  intro D ψ θ A cA a hDef W χ omh hW φ hφ hK m hm u hu huinv
  haveI := hm
  obtain ⟨-, X, K, hXm, hX, hKc, hXK⟩ := GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain D A hDef.sig hDef.pos m hm
  have hloc := fun (K' : Set (GA D A)) (hK' : IsCompact K') =>
    local_rep hW hφ (GlobalTheory.T.K_finite_translates_finite_dimensional D ψ θ A cA a hDef W χ omh hW φ hK K' hK')
  obtain ⟨n, b, c, hb, hc, hrep⟩ := hloc K hKc
  have hχ : IsHeckeChar D χ⁻¹ := by
    refine ⟨?_, fun x => ?_⟩
    · have e : (χ⁻¹ : (AE D)ˣ →* Circle) = fun x => (χ x)⁻¹ := rfl
      rw [e]; exact hW.hecT.1.inv
    · rw [MonoidHom.inv_apply, hW.hecT.2 x, inv_one]
  set w : GA D A × GA D A → ℂ :=
    fun x => conj (conj (u x.1)) * conj (u x.2) * (((χ⁻¹ (detA A x.2) : Circle) : ℂ))⁻¹ with hw
  have hdet : Continuous fun g : GA D A => ((χ⁻¹ (detA A g) : Circle) : ℂ) :=
    continuous_subtype_val.comp (hχ.1.comp GlobalTheory.Eis.continuous_detA)
  have hwc : Continuous w :=
    ((Complex.continuous_conj.comp (Complex.continuous_conj.comp (hu.comp continuous_fst))).mul
      (Complex.continuous_conj.comp (hu.comp continuous_snd))).mul
      ((hdet.comp continuous_snd).inv₀ fun _ => Circle.coe_ne_zero _)
  refine ⟨∑ j, (∫ x in X ×ˢ X, c j x * w x ∂m.prod m) • b j, theta_sum _ _ _ hb, fun Λ hadd hsmul hΛ => ?_⟩
  have hG : ∀ x ∈ K ×ˢ K, Λ (omh (io A x, 1) φ) = ∑ j, c j x * Λ (b j) := fun x hx => by
    rw [hrep x hx]; exact lin_sum Λ φ hφ hadd hsmul _ _ _ hb
  have hGc : Continuous fun x : GA D A × GA D A => Λ (omh (io A x, 1) φ) := by
    refine continuous_of_compact_sq _ fun K' hK' => ?_
    obtain ⟨n', b', c', hb', hc', hrep'⟩ := hloc K' hK'
    have hs : ContinuousOn (fun x => ∑ j, c' j x * Λ (b' j)) (K' ×ˢ K') :=
      continuousOn_finset_sum _ fun j _ => (hc' j).mul continuousOn_const
    refine hs.congr fun x hx => ?_
    rw [hrep' x hx]; exact lin_sum Λ φ hφ hadd hsmul _ _ _ hb'
  have hEq : GlobalTheory.Eis.dblIntegrand A χ⁻¹ (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g)) (fun g => conj (u g)) =
      fun x => Λ (omh (io A x, 1) φ) * w x := by
    funext x; simp only [GlobalTheory.Eis.dblIntegrand, hw]; ring
  have hcont : Continuous (GlobalTheory.Eis.dblIntegrand A χ⁻¹ (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g))
      (fun g => conj (u g))) := hEq ▸ hGc.mul hwc
  have hli := GlobalTheory.Eis.leftInv_dblIntegrand (V := A) (f₁ := fun g => conj (u g)) (f₂ := fun g => conj (u g)) hχ
    (E := fun g => Λ (omh (g, 1) φ)) (fun γ hγ g => hΛ γ hγ g)
    (fun γ hγ g => congrArg (starRingEnd ℂ) (huinv γ hγ g)) (fun γ hγ g => congrArg (starRingEnd ℂ) (huinv γ hγ g))
  have hcomp : IsCompact (K ×ˢ K) := hKc.prod hKc
  have hsub : X ×ˢ X ⊆ K ×ˢ K := Set.prod_mono hXK hXK
  have hint : IntegrableOn (GlobalTheory.Eis.dblIntegrand A χ⁻¹ (fun g => Λ (omh (g, 1) φ)) (fun g => conj (u g))
      (fun g => conj (u g))) (X ×ˢ X) (m.prod m) := (hcont.continuousOn.integrableOn_compact hcomp).mono_set hsub
  have hconv := (GlobalTheory.Eis.dblConv_iff hli hcont.measurable hX).2 hint
  rw [(hconv.dblInt_eq hX).2, hEq]
  have hXXm : MeasurableSet (X ×ˢ X) := hXm.prod hXm
  rw [setIntegral_congr_fun hXXm (g := fun x => ∑ j, (c j x * w x) * Λ (b j)) fun x hx => ?_]
  · rw [integral_finset_sum _ fun j _ => ?_]
    · rw [lin_sum Λ φ hφ hadd hsmul _ _ _ hb]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_mul_const]
    · exact ((((hc j).mul hwc.continuousOn).mul continuousOn_const).integrableOn_compact hcomp).mono_set hsub
  · simp only
    rw [hG x (hsub hx), Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.Core.Rk.Collect
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainStepFockVectorsSphericalOffS
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.ChainTw

theorem fock_sph_tw : ∀ D : D7, ForStepQ D fun c _ k s s' p => (∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ) ∧ ∀ v ∉ c.S, GlobalTheory.FinZeta.VacFin c.ψ s.V s'.V v (p.pt φ)) ∧ GlobalTheory.LFun.UnrOff (c.chS (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) ∧ GlobalTheory.LFun.UnrOff (c.chT (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
  classical
  intro D _ c w hw k hk s s' hs hs' p hp
  have hc : c.Is := hw.com
  obtain ⟨hr₁, hL, hfl⟩ := hs
  obtain ⟨hr₂, -, hfl'⟩ := hs'
  obtain ⟨f₀, hvec⟩ := hp.vec
  have hψ : IsStdChar D c.ψ (-1) := hc.std
  have hθ : IsInfFam c.θ := hc.inf
  have hrk : s.V.rank ≤ s'.V.rank := by
    have e1 : s.V.rank = D.R.rankY k := hfl.rank
    have e2 : s'.V.rank = D.R.rankY (k + 1) := hfl'.rank
    rw [e1, e2]
    show D.R.r + k * D.R.t ≤ D.R.r + (k + 1) * D.R.t
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ _)) _
  have hsd : IsSelfDualC s.V s.Λ := hfl.selfDual
  have hsd' : IsSelfDualC s'.V s'.Λ := hfl'.selfDual
  obtain ⟨hfθ, -, hfv⟩ := GlobalTheory.Chain.StepVac.stepVec_vac hsd hsd' hrk hvec
  have hPS : ∀ PP ∈ s.L.Pg ∪ w.Q, PP.under (𝓞 D.host.F) ∈ c.S := by
    intro PP hPP
    rw [hL] at hPP
    have hPP' : PP ∈ c.Pg := by rw [hw.union]; exact hPP
    exact Finset.mem_image_of_mem _ hPP'
  refine ⟨fun φ => ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · exact GlobalTheory.FockSph.isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hfθ hfv φ
  · obtain ⟨hvac, e, he, hth⟩ := hvec
    exact GlobalTheory.FockSph.isLatVac_pureTensorO_off hθ (onb s.M) (onb s'.M) hvac he hth c.S hPS hp.theta φ
  · intro v hv
    obtain ⟨hf₀, e, he, hth⟩ := hvec
    obtain ⟨NS, hNS, hNSv⟩ := hfl.base
    obtain ⟨NT, hNT, hNTv⟩ := hfl'.base
    have hM : ((NS * NT : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal := by
      obtain ⟨P, hP⟩ := GlobalTheory.ChainOnto.VacOffS.exists_under (D := D) v
      have hPv : P.under (𝓞 D.host.F) ∉ c.S := by rw [hP]; exact hv
      have h1 := hNSv P hPv
      have h2 := hNTv P hPv
      intro h
      rw [← hP] at h
      change algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal at h
      rw [map_natCast, Nat.cast_mul] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact h1 h
      · exact h2 h
    have hle := GlobalTheory.ChainOnto.VacOffS.latO_at_le hNS.2.2.2.1 hNT.2.2.2.1 hM
    have hoff : ∀ PP ∈ s.L.Pg ∪ w.Q, PP.under (𝓞 D.host.F) ≠ v := by
      intro PP hPP h0
      exact hv (h0 ▸ hPS PP hPP)
    have hfix : ∀ u ∈ latO s.V s'.V (GlobalTheory.AdelicU.frameLat s.V : Set (Fin s.V.rank → D.host.E))
        (GlobalTheory.AdelicU.frameLat s'.V : Set (Fin s'.V.rank → D.host.E)) (fun u => u = v),
        heisO c.ψ s.V s'.V u f₀ = f₀ → heisO c.ψ s.V s'.V u (p.pt φ) = p.pt φ := fun u hu h0 =>
      GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite c.ψ c.θ s.V s'.V hc.inf _ _ _ _ p.f hp.theta u
        (GlobalTheory.VacGood.infPart_latO (hle hu))
        (GlobalTheory.Hk3.heisO_fix_thetaAt_off c.ψ _ _ _ _ _ _ _ _ hth u
          (fun i j => GlobalTheory.FinZeta.VacOff.idemSum_mul_off he hoff hu i j) h0) φ
    refine ⟨hp.theta φ, fun u hu => ?_, fun e' he' u hu hh => ?_⟩
    · exact hfix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hf₀.2.lat.1 u (hle hu))
    · exact hfix u hu (hf₀.2.lat.2 e' he' u (hle hu) hh)
  · intro v hv
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) v := hc.unr ⟨k, hk⟩ v hv
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ v := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 v).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) v := hμ.mul hη
    unfold Com.chS Lift.chrStep
    split_ifs <;> assumption
  · intro v hv
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) v := hc.unr ⟨k, hk⟩ v hv
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ v := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 v).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) v := hμ.mul hη
    unfold Com.chT Lift.chrStep
    split_ifs <;> assumption

end GlobalTheory.ChainTw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpImageIntegralMatrixMemCompletedHomLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.up_image_integral_matrix_mem_completed_hom_lattice : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → (ofSplit q).up FS FT x ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  first | exact @GlobalTheory.UpMem.up_mem_latO | exact GlobalTheory.UpMem.up_mem_latO | (intros; apply GlobalTheory.UpMem.up_mem_latO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepConjSourceLineEqTargetLineStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_conj_sourceLine_eq_targetLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E), L.rank = L'.rank → τᴴ ⬝ (L.gram ⬝ τ) = (((1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ (χz χ χ' : ((AE D)ˣ →* Circle)) (om : Om L S) (om' : Om S L'), IsWeilDatumO ψ L S χz χ om → IsWeilDatumO ψ S L' χ' χz om' → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L' (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) ∧ ∀ h, om' (h, 1) (fun w => star (f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)))) = fun w => star (om (1, h) f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) := by
  first | exact @GlobalTheory.ConjLine.conj_line | exact GlobalTheory.ConjLine.conj_line | (intros; apply GlobalTheory.ConjLine.conj_line <;> assumption)
end

