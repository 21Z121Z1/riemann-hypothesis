import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.NotMemSpanOfCommute
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0069
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0694
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParahoricLevelLiftsExist
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0833
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0837
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ZeroDegreeOfPinFor
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatSelfDualOfUnimod
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterEmbeddingCompat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0832
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjHalfInvariantFormIdemSumVacuumNeZero
section
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.LevelSeries.IdemSumForm

open GlobalTheory.SplitScalar
open scoped ComplexOrder

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem heisL_commute_of {a : AE D} (ha : cA D a * a = 0) {x y : WO S T} (hx : IsHalf a x) (hy : IsHalf a y) :
    Commute (heisL ψ S T x) (heisL ψ S T y) := by
  have add : ∀ {x y : WO S T}, IsHalf a x → IsHalf a y → heisL ψ S T (x + y) = heisL ψ S T x * heisL ψ S T y :=
    fun hx hy => LinearMap.ext fun f => heisO_add_of_orth ψ S T (symplO_eq_zero S T ha hx hy) f
  rw [Commute, SemiconjBy, ← add hx hy, ← add hy hx, add_comm]

theorem dual_half {Λ : AddSubgroup (WO S T)} {e : AE D} (he1 : e * e = e)
    (hfin : ∀ u : WO S T, IsHalf e u → u.map (infPart D) = 0)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {y : WO S T} (hy : IsHalf e y) (hyΛ : y ∉ Λ) :
    ∃ l ∈ Λ, IsHalf (cA D e) l ∧ ψ (symplO S T l y) ≠ 1 := by
  rw [hd y (hfin y hy)] at hyΛ
  push Not at hyΛ
  obtain ⟨u, hu, h⟩ := hyΛ
  refine ⟨cA D e • u, hst u hu, isHalf_smul (by rw [← RingHom.map_mul, he1]) u, psi_skew_ne ?_⟩
  rwa [← symplO_smul, (isHalf_iff _ _).1 hy]

theorem count_form {Λ : AddSubgroup (WO S T)} {e : AE D} (he1 : e * e = e) (he2 : cA D e * e = 0)
    (hfin : ∀ u : WO S T, IsHalf e u → u.map (infPart D) = 0)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {f : WO S T → ℂ} (hf0 : f ≠ 0)
    (hfe : ∀ l ∈ Λ, IsHalf e l → heisO ψ S T l f = f) (hfc : ∀ l ∈ Λ, IsHalf (cA D e) l → heisO ψ S T l f = f) :
    ∃ κ : (WO S T → ℂ) →ₗ[ℂ] ℂ, κ f = 1 ∧ ∀ y, IsHalf e y → 0 ≤ κ (heisO ψ S T y f) := by
  have he2' : cA D (cA D e) * cA D e = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm, he2]
  have h : f ∉ Submodule.span ℂ {x | ∃ y, IsHalf e y ∧ y ∉ Λ ∧ x = heisO ψ S T y f} := by
    refine notMem_span_of_commute
      {g | ∃ l ∈ Λ, ∃ z : ℂ, IsHalf (cA D e) l ∧ z ≠ 1 ∧ g = heisL ψ S T l - z • 1} ?_ _ ?_ f ?_
    · rintro _ ⟨l, -, z, hl, -, rfl⟩ _ ⟨l', -, z', hl', -, rfl⟩
      exact ((heisL_commute_of he2' hl hl').sub_right ((Commute.one_right _).smul_right _)).sub_left
        ((Commute.one_left _).smul_left _)
    · rintro _ ⟨y, hy, hyΛ, rfl⟩
      obtain ⟨l, hl, hl', hne⟩ := dual_half he1 hfin hd hst hy hyΛ
      refine ⟨_, ⟨l, hl, _, hl', hne, rfl⟩, ?_⟩
      rw [LinearMap.sub_apply, heisL_apply, heisO_comm, hfc l hl hl']
      exact sub_self _
    · have : ∀ B ∈ Submonoid.closure
          {g | ∃ l ∈ Λ, ∃ z : ℂ, IsHalf (cA D e) l ∧ z ≠ 1 ∧ g = heisL ψ S T l - z • 1},
          ∃ c : ℂ, c ≠ 0 ∧ B f = c • f := by
        intro B hB
        induction hB using Submonoid.closure_induction with
        | mem b hb =>
          obtain ⟨l, hl, z, hl', hz, rfl⟩ := hb
          refine ⟨1 - z, sub_ne_zero.2 hz.symm, ?_⟩
          rw [LinearMap.sub_apply, heisL_apply, hfc l hl hl', sub_smul, one_smul]
          rfl
        | one => exact ⟨1, one_ne_zero, (one_smul _ _).symm⟩
        | mul x y _ _ hx hy =>
          obtain ⟨c, hc, hx⟩ := hx
          obtain ⟨d, hd, hy⟩ := hy
          exact ⟨d * c, mul_ne_zero hd hc, by rw [Module.End.mul_apply, hy, map_smul, hx, smul_smul]⟩
      intro B hB
      obtain ⟨c, hc, h⟩ := this B hB
      rw [h]
      exact smul_ne_zero hc hf0
  obtain ⟨κ, hκ, hκ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨(κ f)⁻¹ • κ, by rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hκ], fun y hy => ?_⟩
  by_cases hyΛ : y ∈ Λ
  · rw [hfe y hyΛ hy, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hκ]
    exact zero_le_one
  · have : κ (heisO ψ S T y f) = 0 := by
      rw [← Submodule.mem_bot ℂ, ← hκ']
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, hy, hyΛ, rfl⟩)
    rw [LinearMap.smul_apply, this, smul_zero]

theorem invariant_form {Λ : AddSubgroup (WO S T)} {e : AE D} (he1 : e * e = e) (he2 : cA D e * e = 0)
    (hfin : ∀ u : WO S T, IsHalf e u → u.map (infPart D) = 0)
    (hd : ∀ u : WO S T, u.map (infPart D) = 0 → (u ∈ Λ ↔ ∀ u' ∈ Λ, ψ (symplO S T u u') = 1))
    (hst : ∀ u ∈ Λ, cA D e • u ∈ Λ) {f : WO S T → ℂ} (hf0 : f ≠ 0)
    (hfe : ∀ l ∈ Λ, IsHalf e l → heisO ψ S T l f = f) (hfc : ∀ l ∈ Λ, IsHalf (cA D e) l → heisO ψ S T l f = f) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, ℓ f ≠ 0 ∧
      ∀ y, IsHalf e y → ∀ φ, IsThetaFunO ψ S T φ → ℓ (heisO ψ S T y φ) = ℓ φ := by
  obtain ⟨κ, hκ1, hκ⟩ := count_form he1 he2 hfin hd hst hf0 hfe hfc
  have h : f ∉ Submodule.span ℂ
      {x | ∃ y φ, IsHalf e y ∧ IsThetaFunO ψ S T φ ∧ x = heisO ψ S T y φ - φ} := by
    refine notMem_span_of_commute
      {g | ∃ (y : WO S T) (N : ℕ), IsHalf e y ∧ g = ∑ k ∈ Finset.range (N + 1), heisL ψ S T (k • y)} ?_ _ ?_ f ?_
    · rintro _ ⟨y, N, hy, rfl⟩ _ ⟨y', N', hy', rfl⟩
      exact Commute.sum_left _ _ _ fun k _ => Commute.sum_right _ _ _ fun k' _ =>
        heisL_commute_of he2 (isHalf_nsmul hy k) (isHalf_nsmul hy' k')
    · rintro _ ⟨y, φ, hy, hφ, rfl⟩
      obtain ⟨U, hU, hUφ⟩ := hφ.level
      obtain ⟨N, hN, hNU⟩ := exists_nsmul_mem U hU (hfin y hy)
      obtain ⟨N, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
      refine ⟨_, ⟨y, N, hy, rfl⟩, ?_⟩
      have e1 : ∀ k : ℕ, heisL ψ S T (k • y) (heisO ψ S T y φ - φ) =
          heisO ψ S T ((k + 1) • y) φ - heisO ψ S T (k • y) φ := by
        intro k
        rw [map_sub, succ_nsmul, heisO_add_of_orth ψ S T (symplO_eq_zero S T he2 (isHalf_nsmul hy k) hy)]
        rfl
      rw [LinearMap.sum_apply, Finset.sum_congr rfl fun k _ => e1 k,
        Finset.sum_range_sub (fun k => heisO ψ S T (k • y) φ), zero_smul, heisO_zero,
        hUφ _ hNU (hfin _ (isHalf_nsmul hy _)), sub_self]
    · have : ∀ B ∈ Submonoid.closure
          {g | ∃ (y : WO S T) (N : ℕ), IsHalf e y ∧ g = ∑ k ∈ Finset.range (N + 1), heisL ψ S T (k • y)},
          (∀ y, IsHalf e y → 0 ≤ κ (B (heisO ψ S T y f))) ∧ 0 < κ (B f) := by
        intro B hB
        induction hB using Submonoid.closure_induction_right with
        | one => exact ⟨hκ, by rw [Module.End.one_apply, hκ1]; exact zero_lt_one⟩
        | mul_right B _ g hg ih =>
          obtain ⟨y', N, hy', rfl⟩ := hg
          refine ⟨fun y hy => ?_, ?_⟩
          · rw [Module.End.mul_apply, LinearMap.sum_apply, map_sum, map_sum]
            refine Finset.sum_nonneg fun k _ => ?_
            rw [heisL_apply, ← heisO_add_of_orth ψ S T (symplO_eq_zero S T he2 (isHalf_nsmul hy' k) hy)]
            exact ih.1 _ (isHalf_add (isHalf_nsmul hy' k) hy)
          · rw [Module.End.mul_apply, LinearMap.sum_apply, map_sum, map_sum]
            refine Finset.sum_pos' (fun k _ => ih.1 _ (isHalf_nsmul hy' k)) ⟨0, Finset.mem_range.2 N.succ_pos, ?_⟩
            rw [heisL_apply, zero_smul, heisO_zero]
            exact ih.2
      intro B hB h0
      have := (this B hB).2
      rw [h0, map_zero] at this
      exact lt_irrefl _ this
  obtain ⟨ℓ, hℓ, hℓ'⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨ℓ, hℓ, fun y hy φ hφ => ?_⟩
  rw [← sub_eq_zero, ← map_sub, ← Submodule.mem_bot ℂ, ← hℓ']
  exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, φ, hy, hφ, rfl⟩)

theorem fix_sum_smul {Λ : AddSubgroup (WO S T)} (hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ)
    {f : WO S T → ℂ} (hf : IsLatVac (heisO ψ S T) Λ f) {ι : Type} [DecidableEq ι] (es : ι → AE D)
    {l : WO S T} (hl : l ∈ Λ) : ∀ s : Finset ι, (∀ P ∈ s, IsSplitIdem D (es P)) →
      (∀ P ∈ s, ∀ Q ∈ s, cA D (es P) * es Q = 0) → heisO ψ S T ((∑ P ∈ s, es P) • l) f = f := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ _; rw [Finset.sum_empty, zero_smul, heisO_zero]
  | insert a s ha ih =>
    intro hs ho
    have hs' : ∀ P ∈ s, IsSplitIdem D (es P) := fun P hP => hs P (Finset.mem_insert_of_mem hP)
    have ho' : ∀ P ∈ s, ∀ Q ∈ s, cA D (es P) * es Q = 0 := fun P hP Q hQ =>
      ho P (Finset.mem_insert_of_mem hP) Q (Finset.mem_insert_of_mem hQ)
    have hsa := hs a (Finset.mem_insert_self a s)
    have horth : symplO S T (es a • l) ((∑ P ∈ s, es P) • l) = 0 := by
      rw [symplO_smul, smul_smul, Finset.mul_sum,
        Finset.sum_eq_zero fun Q hQ => ho a (Finset.mem_insert_self a s) Q (Finset.mem_insert_of_mem hQ),
        zero_smul, symplO_zero_right]
    rw [Finset.sum_insert ha, add_smul, heisO_add_of_orth ψ S T horth, ih hs' ho',
      hf.2 (es a) hsa _ (hΛ _ hsa.1 l hl) (isHalf_smul hsa.1 l)]

end GlobalTheory.LevelSeries.IdemSumForm

namespace GlobalTheory.LevelSeries

open GlobalTheory.SplitScalar GlobalTheory.LevelSeries.IdemSumForm

theorem exists_invariant_form_idemSum : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)) (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (sW : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ) (f₀ : WO V W → ℂ), VacPair ψ θ V W χV χW om ΛV ΛW sW f₀ → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D), IsIdemSum eT T → ∃ ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ, ℓ f₀ ≠ 0 ∧ ∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ := by
  intro D ψ θ V W χV χW om ΛV ΛW sW f₀ hP T eT hT
  obtain ⟨-, -, -, -, hΛV, hΛW, -, -, hψ, hvac⟩ := hP
  obtain ⟨⟨es, hes, rfl⟩, hTo⟩ := hT
  obtain ⟨hd, -, -⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ V W ΛV ΛW hψ hΛV hΛW
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E))
      (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True), a • u ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E))
      (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True) := fun a ha =>
    GlobalTheory.LatticeStable.smul_mem_latO D V W _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
  have hmul : ∀ P ∈ T, (∑ Q ∈ T, es Q) * es P = es P := by
    intro P hP
    rw [Finset.sum_mul, Finset.sum_eq_single_of_mem P hP]
    · exact (hes P hP).1.1
    · intro Q hQ hne
      exact GlobalTheory.Tow.idemAt_orth (hes Q hQ) (hes P hP) hne
  have hcross : ∀ P ∈ T, ∀ Q ∈ T, cA D (es P) * es Q = 0 := by
    intro P hP Q hQ
    rw [← hmul P hP, ← hmul Q hQ, RingHom.map_mul]
    calc cA D (∑ R ∈ T, es R) * cA D (es P) * ((∑ R ∈ T, es R) * es Q)
        = ((∑ R ∈ T, es R) * cA D (∑ R ∈ T, es R)) * (cA D (es P) * es Q) := by ring
      _ = 0 := by rw [hTo, zero_mul]
  have hsum1 : (∑ Q ∈ T, es Q) * (∑ Q ∈ T, es Q) = ∑ Q ∈ T, es Q := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl hmul
  set eT := ∑ Q ∈ T, es Q with heT
  have hcsum : cA D eT = ∑ Q ∈ T, cA D (es Q) := map_sum _ _ _
  have hf0 : f₀ ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp⟩ := hvac.norm.1
    have := hvac.norm.2 p hp
    simp [nrm2] at this
  have hfe : ∀ l ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
      IsHalf eT l → heisO ψ V W l f₀ = f₀ := by
    intro l hl hlh
    rw [← (isHalf_iff _ _).1 hlh]
    exact fix_sum_smul hΛ hvac.lat es hl T (fun P hP => (hes P hP).1) hcross
  have hfc : ∀ l ∈ (latO V W (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) fun _ => True),
      IsHalf (cA D eT) l → heisO ψ V W l f₀ = f₀ := by
    intro l hl hlh
    rw [← (isHalf_iff _ _).1 hlh, hcsum]
    refine fix_sum_smul hΛ hvac.lat (fun Q => cA D (es Q)) hl T (fun P hP => isSplitIdem_conj (hes P hP).1) ?_
    intro P hP Q hQ
    rw [GlobalTheory.DualPairCheck.cA_cA, mul_comm]
    exact hcross Q hQ P hP
  have hfin : ∀ u : WO V W, IsHalf (cA D eT) u → u.map (infPart D) = 0 := by
    intro u hu
    ext i j
    show infPart D (u i j) = 0
    rw [← hu i j, RingHom.map_mul, hcsum, map_sum,
      Finset.sum_eq_zero fun Q hQ => infPart_splitIdem (isSplitIdem_conj (hes Q hQ).1), zero_mul]
  have he1 : cA D eT * cA D eT = cA D eT := by rw [← RingHom.map_mul, hsum1]
  have he2 : cA D (cA D eT) * cA D eT = 0 := by rw [GlobalTheory.DualPairCheck.cA_cA, hTo]
  exact invariant_form he1 he2 hfin hd (fun u hu => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact hΛ _ hsum1 u hu) hf0
    (fun l hl hlh => hfc l hl hlh) (fun l hl hlh => hfe l hl (by rwa [GlobalTheory.DualPairCheck.cA_cA] at hlh))

end GlobalTheory.LevelSeries

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedUnitaryAdjointAction
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

theorem smul_conj {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R) (B X Bi : Matrix n n R) :
    c • (B * X * Bi) = B * (c • X) * Bi := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem smul_one_conj {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R) (B Bi : Matrix n n R)
    (h : B * Bi = 1) : B * (c • (1 : Matrix n n R)) * Bi = c • (1 : Matrix n n R) := by
  rw [← smul_conj, Matrix.mul_one, h]

theorem suppAt_inv_of {D : D7} {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  intro i j
  have h := congrFun (congrFun (GlobalTheory.SplitScalar.off_smul_mt_inv hg) i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  rw [Matrix.sub_apply]
  linear_combination (-1 : AE D) * h

theorem chart_idem_one {D : D7} {e : AE D} {PP : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v} {ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) (hL : LevChart e PP v φ ι) : φ (toEAf D e) = 1 := by
  have h0 : φ (toEAf D e - 1) = 0 := by
    rw [hL.2.1, mul_sub, mul_one, ← map_mul, he.1.1, sub_self]
  rwa [map_sub, map_one, sub_eq_zero] at h0

set_option maxHeartbeats 1000000 in

theorem exists_supp_rdAdj_mul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ γ : GL (Fin T.rank) (Fv D.host.F v), ∃ g : GA D T, SuppAt e T g ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T 1 g x) = rdAdj S T βS βT φ x * γ.val := by
  intro D S T βS βT e PP v φ ι he hL γ
  have hfin : GlobalTheory.LevSplit.finSw D = toEAf D := rfl
  have h1 : φ (toEAf D e) = 1 := chart_idem_one he hL
  choose M hM using fun i j => hL.1 (γ.val i j)
  choose M' hM' using fun i j => hL.1 ((γ⁻¹).val i j)
  set A : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D) := Matrix.of M with hA
  set A' : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D) := Matrix.of M' with hA'
  have eA : A.map φ = γ.val := Matrix.ext hM
  have eA' : A'.map φ = (γ⁻¹).val := Matrix.ext hM'
  set c := toEAf D e with hc
  have hAA : c • (A * A') = c • (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) := by
    ext i j
    have hm : (A * A').map φ = (1 : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v)) := by
      rw [Matrix.map_mul, eA, eA', ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hz : φ ((A * A') i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) i j) = 0 := by
      rw [map_sub]
      have := congrFun (congrFun hm i) j
      rw [Matrix.map_apply] at this
      rw [this, ← Matrix.map_apply (f := φ), Matrix.map_one φ (map_zero φ) (map_one φ), sub_self]
    have := (hL.2.1 _).1 hz
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_sub, sub_eq_zero] at this
    exact this
  have hb : (βT⁻¹).val * βT.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hb' : βT.val * (βT⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmm : GlobalTheory.LevSplit.finSw D e • ((βT.val * A * (βT⁻¹).val) * (βT.val * A' * (βT⁻¹).val)) =
      GlobalTheory.LevSplit.finSw D e • (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) := by
    rw [hfin, ← hc]
    have : (βT.val * A * (βT⁻¹).val) * (βT.val * A' * (βT⁻¹).val) = βT.val * (A * A') * (βT⁻¹).val := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (βT⁻¹).val βT.val, hb, Matrix.one_mul]
    rw [this, smul_conj, hAA, smul_one_conj _ _ _ hb']
  obtain ⟨g₀, hs, hg₀⟩ := GlobalTheory.ParahoricLift.split_lift_fin T he.1 _ _ hmm
  rw [hfin, ← hc] at hg₀
  have hX : ((βT⁻¹).val * (Formalism.L2.Theta.mt T g₀).map (toEAf D) * βT.val).map φ = γ.val := by
    have hfe : (Formalism.L2.Theta.mt T g₀).map (toEAf D) = (finE T g₀).val := rfl
    have h2 : c • ((βT⁻¹).val * (finE T g₀).val * βT.val) = c • A := by
      rw [smul_conj, hg₀, ← smul_conj]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [hb, Matrix.mul_one, ← Matrix.mul_assoc, hb, Matrix.one_mul]
    rw [hfe, ← eA]
    refine Matrix.ext fun i j => ?_
    show φ _ = φ _
    have := congrArg φ (congrFun (congrFun h2 i) j)
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, h1, one_mul] using this
  refine ⟨g₀⁻¹, suppAt_inv_of hs, fun x => ?_⟩
  rw [rdAdj, rdAdj, GlobalTheory.TranslateAdj.frMapAdj_actO_inv, Matrix.map_mul, hX]

end GlobalTheory.DownLift.SplitCoef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExtOfIsKsForm
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.TwInputs.Move.Forms

set_option maxHeartbeats 4000000 in

theorem hecke_geo {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) (hsp : HEq D.sp D'.sp)
    (j : Fin D.R.m) (j' : Fin D'.R.m) (hj : (j : ℕ) = j') :
    GA D (Wc D j) = GA D' (Wc D' j') ∧ HEq (Wc D j) (Wc D' j') ∧
    ∀ (β : GL (Fin (Wc D j).rank) (Lev.EAf D)) (β' : GL (Fin (Wc D' j').rank) (Lev.EAf D')), HEq β β' →
    ∀ (Pg : Finset (Pl D.host.E)) (Pg' : Finset (Pl D'.host.E)), HEq Pg Pg' →
    ∀ (P : PlE D.host) (P' : PlE D'.host), HEq P P' → ∀ (k : ℕ) (α' : GA D' (Wc D' j')) (R' : Finset (GA D' (Wc D' j'))),
      IsHeckeAt (Wc D' j') P' k α' →
      Bridge.IsDC (Lev.levG (Wc D' j') β' (Lev.datY _ D'.R.r D'.R.t 0 (r_le_rank_Wc j') Pg' ∅ (LevelP.triv _ _ _)
        (fun _ _ => 1) (fun _ => 1) Lev.Frm.B)) α' R' →
      ∃ (α : GA D (Wc D j)) (R : Finset (GA D (Wc D j))), IsHeckeAt (Wc D j) P k α ∧
        Bridge.IsDC (Lev.levG (Wc D j) β (Lev.datY _ D.R.r D.R.t 0 (r_le_rank_Wc j) Pg ∅ (LevelP.triv _ _ _)
          (fun _ _ => 1) (fun _ => 1) Lev.Frm.B)) α R ∧
        ∀ F F', HEq F F' → HEq (Mult.heckeLin (Wc D j) R F) (Mult.heckeLin (Wc D' j') R' F') := by
  cases D; cases D'
  dsimp only at hR hH hsp
  subst hR; subst hH; subst hsp
  cases Fin.ext hj
  refine ⟨rfl, HEq.rfl, fun β β' hβ Pg Pg' hPg P P' hP k α R h1 h2 => ?_⟩
  subst hβ; subst hPg; subst hP
  exact ⟨α, R, h1, h2, fun F F' hF => by subst hF; rfl⟩

set_option maxHeartbeats 4000000 in

theorem exists_sameVec {D D' : D7} (hR : D.R = D'.R) (hH : HEq D.host D'.host) (hT : D.what₂.Tau = D'.what₂.Tau)
    (he : HEq D.eTau D'.eTau) {V : HSp D} {V' : HSp D'} (hV : HEq V V') {P : D.what₂.Tau → SPar} {P' : D'.what₂.Tau → SPar}
    {M : Mult.DSModel V P} {M' : Mult.DSModel V' P'} (hM : SameModel M M') (v' : M'.Vec) : ∃ v : M.Vec, SameVec v v' := by
  obtain ⟨h1, h2, h3, h4, -, -, h5⟩ := hM
  obtain ⟨R, H, sp, vol, vp, what₂, eT⟩ := D
  obtain ⟨R', H', sp', vol', vp', rows', eT'⟩ := D'
  dsimp only at hR hH hT he
  subst hR; subst hH
  cases what₂; cases rows'
  dsimp only at hT he
  subst hT; subst he; subst hV
  cases M; cases M'
  dsimp only at h1 h2 h3 h4 h5
  subst h1; subst h2; subst h3; subst h4; subst h5
  exact ⟨v', fun τ τ' h => by subst h; rfl⟩

set_option maxHeartbeats 4000000 in

theorem place_geo {R R' : Ranks} {H : Host R} {H' : Host R'} (hR : R = R') (hH : HEq H H') :
    PlE H = PlE H' ∧ ∀ (P : PlE H) (P' : PlE H'), HEq P P' → (IsSplitPl H P ↔ IsSplitPl H' P') ∧
      Nat.card (kP P) = Nat.card (kP P') ∧
      (∀ (χ : Formalism.L2.Host.HChar H.E) (χ' : Formalism.L2.Host.HChar H'.E), HEq χ χ' → χ.val P = χ'.val P') := by
  subst hR; subst hH
  refine ⟨rfl, fun P P' hP => ?_⟩
  subst hP
  exact ⟨Iff.rfl, rfl, fun _ _ h => by subst h; rfl⟩

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in

theorem record_heq {D D' : D7} {N : NData D.R D.host D.what₂} {N' : NData D'.R D'.host D'.what₂}
    {X : NTw D.R D.host D.what₂ D.LL0 N} {X' : NTw D'.R D'.host D'.what₂ D'.LL0 N'}
    {Y : NExp D.R D.host D.what₂ D.LL0 N X} {Y' : NExp D'.R D'.host D'.what₂ D'.LL0 N' X'}
    (h1 : GlobalTheory.TwistChoice.SameGalois N N') (h2 : GlobalTheory.TwistChoice.TwistDataAgreeAcrossCoefficients X X') (h3 : GlobalTheory.TwistChoice.SameForms Y Y')
    (hB : HEq Y.Bsup Y'.Bsup) (hd : HEq X.delta X'.delta) {i : X.Tw} {i' : X'.Tw} (hi : HEq i i') :
    (∀ j b (x : Y.Fm i j b) (x' : Y'.Fm i' j b), HEq x x' → (x ∈ Y.Bsup i j b ↔ x' ∈ Y'.Bsup i' j b) ∧
      (∀ g g', HEq g g' → HEq (Y.actG i j b g x) (Y'.actG i' j b g' x')) ∧
      ∀ k P P', HEq P P' → HEq (Y.hkF i j b k P x) (Y'.hkF i' j b k P' x')) ∧
    (∀ (ε : ∀ i, Bool → (FractionRing (X.O i) →+* ℂ)) (ε' : ∀ i, Bool → (FractionRing (X'.O i) →+* ℂ)), HEq ε ε' →
      ∀ b a a', HEq a a' → ε i b a = ε' i' b a') ∧
    ∀ (P : PlE D.host) (P' : PlE D'.host), HEq P P' → (P ∈ X.S0 i ↔ P' ∈ X'.S0 i') ∧
      ∀ σ' : Formalism.ConjugateSelfDual.G D'.host.E N'.Om, IsFrob (F := D'.host.E) (N'.plOm.1 P') (normV P') σ' →
        ∃ σ : Formalism.ConjugateSelfDual.G D.host.E N.Om, IsFrob (F := D.host.E) (N.plOm.1 P) (normV P) σ ∧ ∀ b : Bool,
          HEq (algebraMap (X.O i) (FractionRing (X.O i)) (algebraMap (X.O0 i) (X.O i)
              ((if b then X.delta i σ else (X.delta i σ)⁻¹ : (X.O0 i)ˣ) : X.O0 i)))
            (algebraMap (X'.O i') (FractionRing (X'.O i')) (algebraMap (X'.O0 i') (X'.O i')
              ((if b then X'.delta i' σ' else (X'.delta i' σ')⁻¹ : (X'.O0 i')ˣ) : X'.O0 i'))) := by
  obtain ⟨a1, a2, -, nOm, ninstOm, nalgOm, nplOm, nPlG⟩ := h1
  have xTw := h2.Tw
  have fixedFieldTransport_baseIntegerRing_heq := h2.O0
  have fixedFieldTransport_baseIntegerCommRing_heq := h2.crO0
  have xO := h2.O
  have xcrO := h2.crO
  have xalgO := h2.algO
  have fixedFieldTransport_initialPlaceSet_heq := h2.S0
  have yFm := h3.Fm
  have yacgFm := h3.acgFm
  have ymodFmK := h3.modFmK
  have ymodFmO := h3.modFmO
  have yactG := h3.actG
  have yhkF := h3.hkF
  clear h2 h3
  cases D; cases D'
  dsimp only at a1 a2
  subst a1; subst a2
  cases N; cases N'
  dsimp only at nOm ninstOm nalgOm nplOm nPlG
  subst nOm; subst ninstOm; subst nalgOm; subst nplOm; subst nPlG
  cases X; cases X'
  dsimp only at xTw fixedFieldTransport_baseIntegerRing_heq fixedFieldTransport_baseIntegerCommRing_heq xO xcrO xalgO fixedFieldTransport_initialPlaceSet_heq hd
  subst xTw; subst fixedFieldTransport_baseIntegerRing_heq; subst fixedFieldTransport_baseIntegerCommRing_heq; subst xO; subst xcrO; subst xalgO; subst fixedFieldTransport_initialPlaceSet_heq; subst hd
  cases Y; cases Y'
  dsimp only at yFm yacgFm ymodFmK ymodFmO yactG yhkF hB
  subst yFm; subst yacgFm; subst ymodFmK; subst ymodFmO; subst yactG; subst yhkF; subst hB
  subst hi
  refine ⟨fun j b x x' hx => ?_, fun ε ε' hε b a a' ha => ?_, fun P P' hP => ?_⟩
  · subst hx
    exact ⟨Iff.rfl, fun g g' h => by subst h; rfl, fun k P P' h => by subst h; rfl⟩
  · subst hε; subst ha; rfl
  · subst hP
    exact ⟨Iff.rfl, fun σ hσ => ⟨σ, hσ, fun _ => HEq.rfl⟩⟩

section Ext

variable {LL LL' Ks Ks' WL WL' G G' : Type} [Field LL] [Field LL'] [NumberField LL']
  [Field Ks] [NumberField Ks] [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL']
  [AddCommGroup WL] [Module LL WL] [Module Ks WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [IsScalarTower Ks LL WL]
  [AddCommGroup WL'] [Module LL' WL'] [Module Ks' WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
  [IsScalarTower Ks' LL' WL']
  {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
  {W' : (LL' →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)]
  [Group G] [Group G']
  {ι : LL →+* LL'} {eK : Ks ≃+* Ks'} {γ : G ≃* G'} {A : Arith.FormsL LL Ks WL W G} {A' : Arith.FormsL LL' Ks' WL' W' G'}

end Ext

end GlobalTheory.TwInputs.Move.Forms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteAdelicMemSelfDualFrameStabilizerOfSplitSupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelic_mem_selfDualFrameStabilizer_of_splitSupport : ∀ (D : D7) (W : HSp D) (β : GL (Fin W.rank) (Formalism.IndefR.Lev.EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)), IsSDFrame W β Λ 1 → ∀ (e f : AE D) (P : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e P → f = e + cA D e → GlobalTheory.IdemSupport.cP P ≠ P → ∀ k : GA D W, SuppF W f k → (∀ a b, GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D)) a b) ∈ P.adicCompletionIntegers D.host.E) → Valued.v (GlobalTheory.StdFrames.cpt P ((HMul.hMul (HMul.hMul ((β)⁻¹).val ((Formalism.L2.Theta.mt W k).map (toEAf D))) (β).val : Matrix (Fin (W).rank) (Fin (W).rank) (Formalism.IndefR.Datum.EAf D))).det) = 1 → finE W k ∈ St β := by
  first | exact @GlobalTheory.SplitStabFrame.finE_mem_St_of_split | exact GlobalTheory.SplitStabFrame.finE_mem_St_of_split | (intros; apply GlobalTheory.SplitStabFrame.finE_mem_St_of_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalConstantsFromAdmittedLocalGaloisStatementsStatement
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localConstants_from_admitted_local_Galois_statements : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), LiftingTheory.aux₃ D HW F 10 23 32 32 := by
  first | exact @GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt | exact GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt | (intros; apply GlobalTheory.localConstants_from_admitted_local_Galois_statements_alt <;> assumption)
end

