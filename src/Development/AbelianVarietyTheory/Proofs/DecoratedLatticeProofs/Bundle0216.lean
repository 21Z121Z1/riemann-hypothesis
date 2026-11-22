import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0133
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0134
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0187
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0164
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1055
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0193
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0149
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepAverageKillsThetaOfDenseFamily
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStepFockVectorSphericalOffS
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FockSph

variable {D : D7}

section Fock

variable {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}

variable (ψ θ sS sT) in

def Killed (n : ℕ) (g : WO S T → ℂ) : Prop :=
  ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ), l.length = n →
    l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g = 0

variable (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
include hψ hθ

theorem foldr_theta (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) :
    IsThetaFunO ψ S T (l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g) := by
  induction l with
  | nil => exact hg
  | cons p l ih => exact GlobalTheory.FockIndep.annih_theta hψ hθ _ _ _ ih

theorem foldr_add (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g g' : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) (hg' : IsThetaFunO ψ S T g') :
    l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (g + g') =
      l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g +
        l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g' := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact GlobalTheory.FockIndep.annih_add hψ hθ _ _ _ (foldr_theta hψ hθ l hg) (foldr_theta hψ hθ l hg')

theorem foldr_smul (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) (a : ℂ) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) :
    l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) (a • g) =
      a • l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact GlobalTheory.FockIndep.annih_smul hψ hθ _ _ _ _ (foldr_theta hψ hθ l hg)

theorem foldr_of_eq_zero (l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin S.rank) ℂ)) {g : WO S T → ℂ}
    (hg : IsThetaFunO ψ S T g) (h0 : g = 0) :
    l.foldr (fun p f => annih (heisO ψ S T) θ p.1 (cplxO (sS p.1) (sT p.1)) p.2 f) g = 0 := by
  have e : g = (0 : ℂ) • g := by rw [zero_smul, h0]
  rw [e, foldr_smul hψ hθ l 0 hg, zero_smul]

theorem killed_succ {n : ℕ} {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (h : Killed ψ θ sS sT n g) :
    Killed ψ θ sS sT (n + 1) g := by
  intro l hl
  obtain ⟨p, l', rfl⟩ : ∃ p l', l = p :: l' := by
    cases l with
    | nil => simp at hl
    | cons p l' => exact ⟨p, l', rfl⟩
  simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
  rw [List.foldr_cons]
  exact foldr_of_eq_zero hψ hθ [p] (foldr_theta hψ hθ l' hg) (h l' hl)

theorem killed_mono {n m : ℕ} (hnm : n ≤ m) {g : WO S T → ℂ} (hg : IsThetaFunO ψ S T g) (h : Killed ψ θ sS sT n g) :
    Killed ψ θ sS sT m g := by
  induction hnm with
  | refl => exact h
  | step _ ih => exact killed_succ hψ hθ hg ih

variable (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
include hS hT

theorem killed_aPlus (n : ℕ) : ∀ {g : WO S T → ℂ}, IsThetaFunO ψ S T g → Killed ψ θ sS sT n g →
    ∀ (τ' : D.what₂.Tau) (z' : Matrix (Fin T.rank) (Fin S.rank) ℂ),
      Killed ψ θ sS sT (n + 1) (aPlus (heisO ψ S T) θ τ' (cplxO (sS τ') (sT τ')) z' g) := by
  induction n with
  | zero =>
    intro g hg h τ' z' l _
    have hg0 : g = 0 := h [] rfl
    have ha := GlobalTheory.FockIndep.aPlus_theta hψ hθ τ' (cplxO (sS τ') (sT τ')) z' hg
    refine foldr_of_eq_zero hψ hθ l ha ?_
    have e : g = (0 : ℂ) • g := by rw [zero_smul, hg0]
    rw [e, GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ _ hg, zero_smul]
  | succ n ih =>
    intro g hg h τ' z' l hl
    rcases List.eq_nil_or_concat l with h0 | ⟨l', q, rfl⟩
    · rw [h0, List.length_nil] at hl; omega
    · replace hl : l'.length = n + 1 := by simpa using hl
      rw [List.concat_eq_append, List.foldr_append, List.foldr_cons, List.foldr_nil,
        GlobalTheory.FockIndep.annih_aPlus hψ hθ q.1 q.2 hS hT τ' z' hg]
      have hq := GlobalTheory.FockIndep.annih_theta hψ hθ q.1 (cplxO (sS q.1) (sT q.1)) q.2 hg
      have hk : Killed ψ θ sS sT n (annih (heisO ψ S T) θ q.1 (cplxO (sS q.1) (sT q.1)) q.2 g) := by
        intro l'' hl''
        have := h (l'' ++ [q]) (by simp [hl''])
        rwa [List.foldr_append, List.foldr_cons, List.foldr_nil] at this
      rw [foldr_add hψ hθ l' (GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ hq) (GlobalTheory.OrientedHeis.theta_smul _ hg),
        ih hq hk τ' z' l' hl, foldr_smul hψ hθ l' _ hg, h l' hl, smul_zero, zero_add]

theorem isFockVec_pureTensorO (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f)
    (hv : ∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec ψ θ S T sS sT (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  have key : IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ) ∧
      ∃ N, Killed ψ θ sS sT N (pureTensorO ψ θ S T sS sT BS BT f φ) := by
    refine GlobalTheory.FockIndep.pure_mem (P := fun g => IsThetaFunO ψ S T g ∧ ∃ N, Killed ψ θ sS sT N g)
      (fun g g' ⟨hg, N, hN⟩ ⟨hg', N', hN'⟩ => ⟨GlobalTheory.OrientedHeis.theta_add hg hg', max N N', fun l hl => ?_⟩)
      (fun a g ⟨hg, N, hN⟩ => ⟨GlobalTheory.OrientedHeis.theta_smul a hg, N, fun l hl => ?_⟩)
      (fun i g ⟨hg, N, hN⟩ => ⟨GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ hg, N + 1, killed_aPlus hψ hθ hS hT N hg hN _ _⟩)
      ⟨hf, 1, fun l hl => ?_⟩ φ
    · rw [foldr_add hψ hθ l hg hg', killed_mono hψ hθ (le_max_left N N') hg hN l hl,
        killed_mono hψ hθ (le_max_right N N') hg' hN' l hl, add_zero]
    · rw [foldr_smul hψ hθ l a hg, hN l hl, smul_zero]
    · obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl
      exact hv p.1 p.2
  obtain ⟨h1, N, h2⟩ := key
  exact ⟨h1, N, h2⟩

end Fock

section Sph

variable {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}

theorem placeIdem_smul_of {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {w : HeightOneSpectrum (𝓞 D.host.F)}
    {ε : AF D.host.F} (hε : IsPlaceIdem D w ε) (hw : ¬ P w) {u : WO S T} (hu : u ∈ latO S T LS LT P) :
    algebraMap (AF D.host.F) (AE D) ε • u = 0 := by
  obtain ⟨β, rfl, -, h0⟩ := hε
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, hP, a, ha, s, hs, t, ht, rfl⟩ := hx
    have hβα : β * α = 0 := by
      refine RestrictedProduct.ext _ _ fun y => ?_
      change evalV D.host.F y (β * α) = evalV D.host.F y 0
      rw [map_mul, map_zero]
      by_cases hy : y = w
      · rw [hy, hP w hw, mul_zero]
      · rw [h0 y hy, zero_mul]
    have hp : pairA D.host.F 0 β * pairA D.host.F 0 α = 0 := Prod.ext (mul_zero _) hβα
    ext i j
    change (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) * (_ ⊗ₜ _) = (0 : AE D)
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hp, TensorProduct.zero_tmul]
  | zero => rw [smul_zero]
  | add x x' _ _ h h' => rw [smul_add, h, h', add_zero]
  | neg x _ h => rw [smul_neg, h, neg_zero]

theorem idemSum_mul_of {P : HeightOneSpectrum (𝓞 D.host.F) → Prop} {e : AE D} {Pset : Finset (Pl D.host.E)}
    (he : IsIdemSum e Pset) (hv : ∀ PP ∈ Pset, ¬ P (PP.under (𝓞 D.host.F))) {u : WO S T}
    (hu : u ∈ latO S T LS LT P) (a : Fin T.rank) (b : Fin S.rank) :
    e * u a b = 0 ∧ cA D e * u a b = 0 := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have key : ∀ PP ∈ Pset, es PP * u a b = 0 ∧ cA D (es PP) * u a b = 0 := by
    intro PP hPP
    obtain ⟨⟨a1, a2, w, ε, hε, a3⟩, -⟩ := hes PP hPP
    have hw : ¬ P w := by
      rw [← GlobalTheory.IdemUnder.under_eq_of_isIdemAt D _ PP w ε (hes PP hPP) hε a3]
      exact hv PP hPP
    have h0 := congrFun (congrFun (placeIdem_smul_of hε hw hu) a) b
    rw [Matrix.smul_apply, smul_eq_mul, ← a3, Matrix.zero_apply] at h0
    have c1 : cA D (es PP) * cA D (es PP) = cA D (es PP) := by rw [← map_mul, a1]
    have c2 : cA D (es PP) * es PP = 0 := by rw [mul_comm, a2]
    refine ⟨?_, ?_⟩
    · linear_combination es PP * h0 - u a b * a1 - u a b * a2
    · linear_combination cA D (es PP) * h0 - u a b * c1 - u a b * c2
  refine ⟨?_, ?_⟩
  · rw [Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).1
  · rw [map_sum, Finset.sum_mul]; exact Finset.sum_eq_zero fun PP hPP => (key PP hPP).2

theorem isLatVac_pureTensorO_off {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    {f₀ Φ f : WO S T → ℂ} (hvac : IsVacO ψ θ S T sS sT LS LT f₀) {e : AE D} {Pset : Finset (Pl D.host.E)}
    (he : IsIdemSum e Pset) (hth : IsThetaAt ψ (symplO S T) (heisO ψ S T) e (latO S T LS LT fun _ => True) 1 f₀ Φ f)
    (Sf : Finset (HeightOneSpectrum (𝓞 D.host.F))) (hP : ∀ PP ∈ Pset, PP.under (𝓞 D.host.F) ∈ Sf)
    (hpt : ∀ φ, IsThetaFunO ψ S T (pureTensorO ψ θ S T sS sT BS BT f φ)) (φ : MvPolynomial (FVar D T.rank S.rank) ℂ) :
    IsLatVac (heisO ψ S T) (latO S T LS LT fun v => v ∉ Sf) (pureTensorO ψ θ S T sS sT BS BT f φ) := by
  have hle : latO S T LS LT (fun v => v ∉ Sf) ≤ latO S T LS LT fun _ => True :=
    GlobalTheory.PlaceTensor.latO_mono fun _ _ => trivial
  have hlat := hvac.2.lat
  have fix : ∀ u ∈ latO S T LS LT (fun v => v ∉ Sf), heisO ψ S T u f₀ = f₀ →
      heisO ψ S T u (pureTensorO ψ θ S T sS sT BS BT f φ) = pureTensorO ψ θ S T sS sT BS BT f φ := fun u hu h0 =>
    GlobalTheory.Hk3.FiniteHeis.heisO_pureTensorO_of_finite ψ θ S T hθ sS sT BS BT f hpt u
      (GlobalTheory.VacGood.infPart_latO (hle hu))
      (GlobalTheory.Hk3.heisO_fix_thetaAt_off ψ S T e _ 1 f₀ Φ f hth u
        (idemSum_mul_of he (fun PP h hn => hn (hP PP h)) hu) h0) φ
  exact ⟨fun u hu => fix (2 • u) (AddSubgroup.nsmul_mem _ hu 2) (hlat.1 u (hle hu)),
    fun e' he' u hu hh => fix u hu (hlat.2 e' he' u (hle hu) hh)⟩

end Sph

end GlobalTheory.FockSph

open GlobalTheory.FockSph in

theorem GlobalTheory.ChainOnto.fock_sph : ∀ D : D7, ForStep D fun c k s s' p => (∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsFockVec c.ψ c.θ s.V s'.V (cart s.M) (cart s'.M) (p.pt φ) ∧ GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.IsSphOff c.ψ s.V s'.V s.Λ s'.Λ c.S (p.pt φ)) ∧ GlobalTheory.LFun.UnrOff (c.chS (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) ∧ GlobalTheory.LFun.UnrOff (c.chT (k + 1)) (c.S : Set (HeightOneSpectrum (𝓞 D.host.F))) := by
  classical
  intro D _ c hc k hk s s' hs hs' p hp
  obtain ⟨ξ, f₀, hvec⟩ := hp.vec
  obtain ⟨hfθ, -, hfv, hpt⟩ := (GlobalTheory.T.thetaChainStep_vector_exists_nonzero_vacuum D c hc ⟨k, hk⟩ s s' hs hs').2 ξ f₀ p.f hvec
  obtain ⟨hvac, e, he, hth⟩ := hvec
  have hψ : IsStdChar D c.ψ (-1) := hc.std
  have hθ : IsInfFam c.θ := hc.inf
  refine ⟨fun φ => ⟨?_, ?_⟩, ?_, ?_⟩
  · exact isFockVec_pureTensorO hψ hθ (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s.M τ)
      (fun τ => GlobalTheory.AdTh.VecFock.isCartanInv_cart s'.M τ) (onb s.M) (onb s'.M) hfθ hfv φ
  · refine isLatVac_pureTensorO_off hθ (onb s.M) (onb s'.M) hvac he hth c.S (fun PP hPP => ?_) hpt φ
    obtain ⟨hr, ξ', hL⟩ := hs.lev
    rw [Finset.union_empty, hL] at hPP
    exact Finset.mem_image_of_mem _ hPP
  · intro w hw
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) w := hc.unr ⟨k, hk⟩ w hw
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ w := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) w := hμ.mul hη
    unfold Com.chS Lift.chrStep
    split_ifs <;> assumption
  · intro w hw
    have hμ : GlobalTheory.LFun.UnrAt (c.μ (k + 1)) w := hc.unr ⟨k, hk⟩ w hw
    have hη : GlobalTheory.LFun.UnrAt c.η⁻¹ w := (GlobalTheory.LFun.unrAt_of_unramEverywhere hc.chars.2.1 w).inv
    have hμη : GlobalTheory.LFun.UnrAt (c.μ (k + 1) * c.η⁻¹) w := hμ.mul hη
    unfold Com.chT Lift.chrStep
    split_ifs <;> assumption

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaContractionIsLocalModelSecondVariable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Topology

namespace GlobalTheory.ContrModR

section SlopeTestRemainingChoices
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem incA_mul_ι (b : D.host.E) (x : k) : incA D b * p.ι x = p.ι (p.pr b * x) := by
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]
  rw [hm]
  change _ = p.ι (p.π (incA D b)) * p.ι x
  rw [p.ι_π, mul_assoc, mul_left_comm, Witness.e_ι]

theorem map_rat_mul_ι {a b c : Type} [Fintype b] (N : Matrix a b D.host.E) (M : Matrix b c k) :
    N.map (incA D) * M.map p.ι = (N.map p.pr * M).map p.ι := by
  ext i j
  simp [Matrix.mul_apply, incA_mul_ι, map_sum]

theorem map_pr_eq {a b : Type} (M : Matrix a b D.host.E) : M.map p.pr = M.map (Witness.prH p) := rfl

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem core_β {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) : F₀.β * fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) = B.o.iA.map p.pr * FA.β := by
  ext r a
  rw [← h.1 r a]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]

theorem core_qA {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) :
    FA.γ * B.o.qA.map p.pr * F₀.β = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) := by
  have hA : FA.γ * B.o.qA.map p.pr * (B.o.iA.map p.pr * FA.β) = 1 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (B.o.qA.map _), ← Matrix.map_mul, B.o.qA_iA,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, FA.γβ]
  have hB : FA.γ * B.o.qA.map p.pr * B.o.iB.map p.pr = 0 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _),
      Matrix.mul_zero]
  have hc : ∀ r, F₀.β r (Sum.inr ()) = s * ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) r := by
    intro r
    rw [h.2 r, vecB, map_pr_eq]
    congr 1
    exact (RingHom.map_mulVec (Witness.prH p) B.o.iB B.ζ r)
  have hv : (FA.γ * B.o.qA.map p.pr) *ᵥ ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) = 0 := by
    rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]
  generalize (B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c)) = v at hc hv
  generalize FA.γ * B.o.qA.map p.pr = X at hA hv ⊢
  ext i (a | u)
  · have := congrFun (congrFun hA i) a
    rw [Matrix.mul_apply] at this
    rw [Matrix.mul_apply, fromCols_apply_inl, ← this]
    simp only [h.1]
  · rw [Matrix.mul_apply, fromCols_apply_inr, Matrix.zero_apply]
    simp only [hc, mul_left_comm _ s, ← Finset.mul_sum]
    have h2 := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h2
    rw [h2, mul_zero]

end SlopeTestRemainingChoices

section Up
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)
variable {n n'' : Type} [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n'']

theorem up_fromRows {σ : ℕ} (B' : BesLev D σ) {s : k} (S : HSp D) (FA' : Frame k B'.A.rank n'')
    (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B' s FA' F₀')
    (x : Matrix n'' n k) :
    p.up FS F₀' (fromRows x (0 : Matrix Unit n k)) = (B'.o.resT S).symm (p.up FS FA' x, 0) := by
  have hx : fromRows x (0 : Matrix Unit n k) = fromRows (1 : Matrix n'' n'' k) (0 : Matrix Unit n'' k) * x := by
    rw [Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul]
  rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Place.up, Place.up, OrthDec.jA, rat, map_rat_mul_ι, hx,
    ← Matrix.mul_assoc, core_β p B' FA' F₀' h]
  simp only [Matrix.mul_assoc]

theorem pA_up {σ : ℕ} (B' : BesLev D σ) {s : k} (S : HSp D) (FA' : Frame k B'.A.rank n'')
    (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B' s FA' F₀')
    (t : Matrix (n'' ⊕ Unit) n k) : B'.o.pA ⬝ p.up FS F₀' t = p.up FS FA' t.toRows₁ := by
  have hq : B'.o.qA.map p.pr * F₀'.β = fromCols FA'.β (0 : Matrix (Fin B'.A.rank) Unit k) := by
    have := congrArg (FA'.β * ·) (core_qA p B' FA' F₀' h)
    simp only [← Matrix.mul_assoc, FA'.βγ, Matrix.one_mul] at this
    rw [this, Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero]
  rw [Place.up, Place.up, OrthDec.pA, rat, map_rat_mul_ι, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hq]
  conv_lhs => rw [← fromRows_toRows t]
  rw [fromCols_mul_fromRows, Matrix.zero_mul, add_zero]

end Up

section Pass
variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ)

theorem symplOH_zero_r {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  have : hO S T x 0 = 0 := by simp [hO]
  simp [symplOH, symplO, this]

theorem heis_pass {V A L : HSp D} (o : OrthDec V A L) (S : HSp D) (f : WO S V → ℂ) (b v : WO S A) (z : WO S L) :
    heisO ψ S V ((o.resT S).symm (b, 0)) f ((o.resT S).symm (v, z)) =
      ψ (symplOH S A v b) * f ((o.resT S).symm (v + b, z)) := by
  simp only [heisO]
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_r, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

end Pass

end GlobalTheory.ContrModR

namespace GlobalTheory.ContrModR

theorem contr_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (s : k), s ≠ 0 → ∀ (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (FS : Frame k S.rank n) (FA' : Frame k B'.A.rank n'') (F₀' : Frame k B'.V₀.rank (n'' ⊕ Unit)), p.IsCoreFrame B' s FA' F₀' → ∀ (T₂ : SB (Matrix (n'' ⊕ Unit) n k) →ₗ[ℂ] (WO S B'.V₀ → ℂ)), p.IsModel ψ FS F₀' T₂ → ∀ (φ₀ : SB (n → k)) (Ξ₁ : WO B.V₀ S → ℂ), IsThetaFunO ψ B.V₀ S Ξ₁ → ∀ (u : WO B.A S) (T : SB (Matrix n'' n k) →ₗ[ℂ] (WO S B'.A → ℂ)), (∀ Ξ₂ v, T Ξ₂ v = GlobalTheory.Unf.contr l S vL Ξ₁ (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Ξ₂)) u v) → p.IsModel ψ FS FA' T := by
  intro D k _ _ _ _ p ψ hψ ρ σ B B' l S vL s hs n n'' _ _ _ _ FS FA' F₀' hcore T₂ hT₂ φ₀ Ξ₁ hΞ₁ u T hT

  have pass : ∀ (b : WO S B'.A) (Φ Φ' : SB (Matrix n'' n k)),
      T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ') =
        heisO ψ S B'.V₀ ((B'.o.resT S).symm (b, 0)) (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ)) →
      T Φ' = heisO ψ S B'.A b (T Φ) := by
    intro b Φ Φ' e
    funext v
    rw [hT Φ' v, e]
    change _ = ψ (symplOH S B'.A v b) * T Φ (v + b)
    rw [hT Φ (v + b)]
    unfold GlobalTheory.Unf.contr
    rw [← integral_const_mul]
    refine congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)
    rw [heis_pass]
    ring
  refine ⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩
  ·
    haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
    haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
      ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨C₁, hC₁⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₁ hΞ₁
    have hc : Continuous fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w)) :=
      hΞ₁.cont.comp ((OrthDec.continuous_resS_symm _ _).comp
        (Continuous.prodMk continuous_const (GlobalTheory.ContractionLocal.continuous_kappa l S)))
    have hint : Integrable (fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w))) (vL.μ.restrict vL.𝓕) :=
      (integrable_const C₁).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => hC₁ _)
    have h := GlobalTheory.SuperposT.superpos_target D ψ hψ B'.V₀ B'.A B'.L S B'.o (T₂ (GlobalTheory.ContractionLocal.rowTens φ₀ Φ))
      (hT₂.theta _) (WO S B'.L) (vL.μ.restrict vL.𝓕) id (fun w => Ξ₁ ((B.o.resS S).symm (u, l.κ S w)))
      measurable_id hint
    convert h using 1
    funext v
    rw [hT]
    unfold GlobalTheory.Unf.contr
    refine congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)
    simp only [id]
    ring
  ·
    refine pass (p.up FS FA' x) Φ Φ' ?_
    rw [← up_fromRows p B' S FA' F₀' FS hcore x]
    refine hT₂.trans _ _ _ fun t => ?_
    have h1 : (t + fromRows x (0 : Matrix Unit n k)).toRows₁ = t.toRows₁ + x := by
      ext i j; simp [Matrix.toRows₁]
    have h2 : (t + fromRows x (0 : Matrix Unit n k)) (Sum.inr ()) = t (Sum.inr ()) := by
      funext j; simp
    simp only [GlobalTheory.ContractionLocal.rowTens_apply, e, h1, h2]
  ·
    refine pass y Φ Φ' (hT₂.modul _ ?_ _ _ fun t => ?_)
    · intro i j
      rw [OrthDec.resT_symm_apply, Matrix.mul_zero, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [mul_left_comm, hy c j]
    · simp only [GlobalTheory.ContractionLocal.rowTens_apply, e]
      rw [B'.o.symplO_resT S (p.up FS F₀' t), AddEquiv.apply_symm_apply]
      rw [OrthDec.resT_apply B'.o S (p.up FS F₀' t)]
      simp only
      rw [pA_up p B' S FA' F₀' FS hcore t]
      have : symplO S B'.L (B'.o.pB ⬝ p.up FS F₀' t) 0 = 0 := by
        have h0 : hO S B'.L (B'.o.pB ⬝ p.up FS F₀' t) 0 = 0 := by simp [hO]
        simp [symplO, h0]
      simp only [this, add_zero]
      ring

end GlobalTheory.ContrModR

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedHeckeVacuumLargerEqSmallerStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unramified_hecke_vacuum_larger_eq_smaller : GlobalTheory.Hk3.HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → ∀ h' ∈ Hecke ℂ (KU σ n'), ∃ h ∈ Hecke ℂ (KU σ n), heckeVec (ω.comp (MonoidHom.inl _ _)) (KU σ n) h s = heckeVec (ω.comp (MonoidHom.inr _ _)) (KU σ n') h' s := by
  first | exact @GlobalTheory.ChainOnto.heckeVec_howe | exact GlobalTheory.ChainOnto.heckeVec_howe | (intros; apply GlobalTheory.ChainOnto.heckeVec_howe <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepAverageKillsThetaOfDenseFamilyStatement
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
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_average_kills_theta_of_dense_family : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : WRep S T), IsWeilDatumO ψ S T χS χT om → ∀ (X : Type) [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] (μ : Measure X) [IsFiniteMeasure μ] (p : X → GA D S × GA D T) (c : X → ℂ) (K : Set (GA D S × GA D T)), Continuous p → Continuous c → (∃ C : ℝ, ∀ x, ‖c x‖ ≤ C) → IsCompact K → (∀ᵐ x ∂μ, p x ∈ K) → ∀ M : Submodule ℂ (WO S T → ℂ), (∀ g ∈ M, IsThetaFunO ψ S T g) → (∀ g ∈ M, ∀ w, heisO ψ S T w g ∈ M) → (∀ g ∈ M, ∫ x, c x * om (p x) g 0 ∂μ = 0) → ∀ f, IsThetaFunO ψ S T f → GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.UnifLimit M f → ∫ x, c x * om (p x) f 0 ∂μ = 0 := by
  first | exact @GlobalTheory.AvgKill.average_kills_theta | exact GlobalTheory.AvgKill.average_kills_theta | (intros; apply GlobalTheory.AvgKill.average_kills_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittHyperbolicIsotropicColumnsAtRealPlaceStatement
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
open GlobalTheory.AdelicU Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittHyperbolic_isotropic_columns_at_real_place : ∀ {D : D7} {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) (w : InfinitePlace D.host.F), (Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion D.sp.cm.sig) (Matrix.map d.jX (compInf D.host.F D.host.E w)) * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR w.Completion T.gram : Matrix (Fin r) (Fin T.rank) (TensorProduct D.host.F w.Completion D.host.E)) * Matrix.map d.jX (compInf D.host.F D.host.E w) = 0 := by
  first | exact @GlobalTheory.IsoColReal.isotropic_at_real | exact GlobalTheory.IsoColReal.isotropic_at_real | (intros; apply GlobalTheory.IsoColReal.isotropic_at_real <;> assumption)
end

