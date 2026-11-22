import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
import Formalism.LocalToGlobal.PairingIndexBounds.LatticeNormPowers.CloseUnitNorms.TestVectorMemSchwartzBruhat
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0198
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0161
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0199
import BuildAid.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0725
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EquivariantOfWave
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0082
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.RealPlaceImaginaryGeneratorReEqZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0650
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0697
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0721
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0729
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentMulOfMapsToParabolicInduction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0208
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0009
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0731
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsNotCongPow

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinearIndependentRowsMap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie

theorem linearIndependent_rows_map {K L : Type*} [Field K] [Field L] (e : K →+* L) {n m : ℕ}
    (a : Fin n → Fin m → K) (ha : LinearIndependent K a) :
    LinearIndependent L fun c k => e (a c k) := by
  classical
  obtain ⟨g, hg⟩ := (Fintype.linearCombination K a).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.2 ha.fintypeLinearCombination_injective)
  have hj : ∀ c j, g (a c) j = if c = j then 1 else 0 := fun c j => by
    have := congrFun (LinearMap.congr_fun hg (Pi.single c 1)) j
    simpa [Pi.single_apply, eq_comm] using this
  have hg' : ∀ (x : Fin m → K) j, g x j = ∑ k, x k * g (fun j' => if k = j' then 1 else 0) j := fun x j => by
    conv_lhs => rw [pi_eq_sum_univ x]
    rw [map_sum, Finset.sum_apply]
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.linearIndependent_iff]
  intro μ hμ j
  have h0 : ∀ k, ∑ c, μ c * e (a c k) = 0 := fun k => by
    have := congrFun hμ k
    simpa [Finset.sum_apply] using this
  calc μ j = ∑ c, μ c * e (g (a c) j) := by simp [hj]
    _ = ∑ c, ∑ k, μ c * e (a c k * g (fun j' => if k = j' then 1 else 0) j) :=
        Finset.sum_congr rfl fun c _ => by rw [hg' (a c) j, map_sum, Finset.mul_sum]
    _ = ∑ k, e (g (fun j' => if k = j' then 1 else 0) j) * ∑ c, μ c * e (a c k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [map_mul]
        ring
    _ = 0 := by simp [h0]

theorem realRd_faithful : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), ν ≠ 0 → Rl.toRealDat.LUnif → Rl.toRealDat.models_HW → FWT.IsChosenExtremalVector Rl.toRealDat j (sg0 D A3.A) (v₀ j _) → (S.A ((j : ℕ) + 1)).IsKsForm → Faithful (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hν hU hW hv hK
  classical
  let L : (Rl.HW j (sg0 D A3.A)).H →ₗ[ℂ] (GA D (Wc D j) → ℂ) :=
    { toFun := fun x => (Rl.HW j (sg0 D A3.A)).e x (v₀ j _)
      map_add' := fun x y => by rw [map_add]; rfl
      map_smul' := fun c x => by rw [map_smul]; rfl }
  have hL : LinearMap.ker L = ⊥ :=
    LinearMap.ker_eq_bot.2 fun x y h => GlobalTheory.LiftScalarCompare.eval_inj hW hv h
  obtain ⟨m, bb, -, hKs, hspan, hLL, -⟩ := hK
  let bK : Module.Basis (Fin m) S.Ks ↥(S.A ((j : ℕ) + 1)).WK :=
    (Module.Basis.span hKs).map (LinearEquiv.ofEq _ _ hspan)
  have hbK : ∀ k, ((bK k : ↥(S.A ((j : ℕ) + 1)).WK) : S.WL ((j : ℕ) + 1)) = bb k := fun k => by
    simp [bK, Module.Basis.span_apply]
  let φ : Fin m → (GA D (Wc D j) → ℂ) := fun k => evW YS v₀ j (bb k)
  have hφ : LinearIndependent ℂ φ := by
    have h1 : LinearIndependent D.what₂.LL fun k => (YS.fi j).e (bb k) :=
      hLL.map' (YS.fi j).e.toLinearMap (YS.fi j).e.ker
    exact ((hU j (sg0 D A3.A)).1 m _ h1).map' L hL
  let B : Module.Basis (Fin m) (NX.KB S i b) (NX.Fm S i ((j : ℕ) + 1) b) :=
    Algebra.TensorProduct.basis (NX.KB S i b) bK
  intro n v hvi
  let w : Fin n → NX.Fm S i ((j : ℕ) + 1) b := fun c => YS.eF i _ b (Nat.le_add_left _ _) j.2 (v c)
  have hw0 : LinearIndependent (FractionRing (D.ntw.O i)) w :=
    hvi.map' (YS.eF i _ b (Nat.le_add_left _ _) j.2).toLinearMap (YS.eF i _ b (Nat.le_add_left _ _) j.2).ker
  have hw1 : LinearIndependent (NX.KB S i b) w := hw0
  have hw : LinearIndependent (NX.KB S i b) fun c => B.equivFun (w c) :=
    hw1.map' B.equivFun.toLinearMap B.equivFun.ker
  have hr := linearIndependent_rows_map (ρ.e i b) (fun c => B.equivFun (w c)) hw
  let Ψ : (Fin m → ℂ) →ₗ[ℂ] (GA D (Wc D j) → ℂ) := ν⁻¹ • Fintype.linearCombination ℂ φ
  have hΨ : LinearMap.ker Ψ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun z hz => ?_
    have h0 : Fintype.linearCombination ℂ φ z = 0 := by
      have := hz
      simp only [Ψ, LinearMap.smul_apply, smul_eq_zero, inv_eq_zero, hν, false_or] at this
      exact this
    exact hφ.fintypeLinearCombination_injective (h0.trans (map_zero _).symm)
  suffices key : (fun c => realRd YS v₀ hρ i j b ν (v c)) = Ψ ∘ fun c k => ρ.e i b (B.equivFun (w c) k) by
    rw [key]; exact hr.map' Ψ hΨ
  funext c
  change ν⁻¹ • evK YS v₀ hρ i j b (w c) = ν⁻¹ • Fintype.linearCombination ℂ φ _
  congr 1
  rw [Fintype.linearCombination_apply]
  conv_lhs => rw [← B.sum_equivFun (w c)]
  refine (map_sum (evK YS v₀ hρ i j b) _ _).trans ?_
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show B k = ((1 : NX.KB S i b) ⊗ₜ[S.Ks] bK k : NX.KB S i b ⊗[S.Ks] NX.FmK S ((j : ℕ) + 1)) from
    Algebra.TensorProduct.basis_apply _ _]
  change evK YS v₀ hρ i j b ((B.equivFun (w c) k • (1 : NX.KB S i b)) ⊗ₜ[S.Ks] (bK k : NX.FmK S ((j : ℕ) + 1))) = _
  rw [smul_eq_mul, mul_one]
  refine (evK_tmul YS v₀ hρ i j b _ _).trans ?_
  exact congrArg _ (congrArg (evW YS v₀ j) (hbK k))

end GlobalTheory.SeriesTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemBlockTriangularTwoBlockSizesOfLe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.SeriesTie.ActProof
open Formalism.IndefR.Lev Formalism.L2.DIV Formalism.IndefR.Mult
open scoped TensorProduct

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem parLev_eq_of {n : ℕ} {LL : Type} [CommRing LL] (hc : CMData D.host.F D.host.E) (J : Matrix (Fin n) (Fin n) D.host.E)
    (β : GL (Fin n) (D.host.E ⊗[D.host.F] Af D.host.F)) (L L' : LevDat D.host.E LL n) (hP : L.Pg = L'.Pg) (hQ : L.Q = L'.Q)
    (hb : (blkOf L.r L.t : Fin n → ℕ) = blkOf L'.r L'.t) (hb2 : (blk2 L.r : Fin n → ℕ) = blk2 L'.r) :
    parLev hc J β L = parLev hc J β L' := by
  unfold parLev
  rw [hP, hQ, hb, hb2]

theorem blkOf_eq_zero {n r t : ℕ} (h : n ≤ r) : (blkOf r t : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blkOf]
  rw [if_pos (by omega)]

theorem twoBlockSizes_eq_zero_of_le {n r : ℕ} (h : n ≤ r) : (blk2 r : Fin n → ℕ) = fun _ => 0 := by
  funext a
  have := a.2
  simp only [blk2]
  rw [if_pos (by omega)]

theorem mem_blockTriangular_twoBlockSizes_of_le {n r : ℕ} {κ : Type} [CommRing κ] (h : n ≤ r) (g : GL (Fin n) κ) : g ∈ blockTri (blk2 r) := by
  intro i k hik
  rw [twoBlockSizes_eq_zero_of_le h] at hik
  exact absurd hik (lt_irrefl _)

variable (Rl : RealDat3 D A3 Ks) (j : Fin D.R.m)

theorem levChi_flagL (κ : GA D (Wc D j)) : levChi (Wc D j) (Rl.βW j) (flagL (Rl.datWp j Rl.triv)) κ = 1 := by
  unfold levChi levFn
  have h1 : (flagL (Rl.datWp j Rl.triv)).P.chi = 1 := rfl
  have hs : (flagL (Rl.datWp j Rl.triv)).s = 0 := rfl
  have hq : (flagL (Rl.datWp j Rl.triv)).Q = ∅ := rfl
  rw [h1, subgroupCharExtension_one_apply, hs, hq]
  simp

theorem hasType_of_mem_wall {σ : D.what₂.LL →+* ℂ} {F : MMap (Rl.MW j σ)} (hF : F ∈ Rl.toRealDat.Wall j σ)
    (v : (Rl.MW j σ).Vec) : HasType (Wc D j) (Rl.βW j) (flag1L (Rl.datWp j Rl.triv)) (F v) := by
  have key : ∀ F' ∈ Rl.toRealDat.Wall j σ, ∀ (v : (Rl.MW j σ).Vec), ∀ κ ∈ levG (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv),
      ∀ h, F' v (h * κ) = levChi (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) κ * F' v h := by
    intro F' hF'
    induction hF' using Submodule.span_induction with
    | mem x hx => exact fun v κ hκ h => hx.lev v κ hκ h
    | zero => intro v κ _ h; simp only [MultilinearMap.zero_apply, Pi.zero_apply, mul_zero]
    | add x y _ _ hx hy =>
      intro v κ hκ h
      rw [MultilinearMap.add_apply, Pi.add_apply, Pi.add_apply, hx v κ hκ h, hy v κ hκ h, mul_add]
    | smul a x _ hx =>
      intro v κ hκ h
      rw [MultilinearMap.smul_apply, Pi.smul_apply, Pi.smul_apply, hx v κ hκ h, smul_eq_mul, smul_eq_mul, mul_left_comm]
  exact fun κ hκ h => key F hF v κ hκ h

theorem isLift_transfer {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {ρ : Setup D.ntw} (hp : RealPin Rl cG ρ) (i : D.ntw.Tw) (b : Bool)
    (g : G0g D.nd) (κ : GA D (Wc D j))
    (h : IsLevelLift (Wc D j) (ρ.B i j b).F.βT (ρ.B i j b).G.levT (ρ.eG i j b g) κ) :
    IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm g) κ := by
  obtain ⟨h1, h2, h3⟩ := h
  rw [hp.frT] at h2 h3
  have hr : (Wc D j).rank ≤ D.R.r := (FWT.rank_Wc j).le
  have hpar : parLev D.sp.cm (Wc D j).gram (Rl.βW j) (ρ.B i j b).G.levT =
      parLev D.sp.cm (Wc D j).gram (Rl.βW j) (Rl.datWp j Rl.triv) := by
    apply parLev_eq_of
    · exact hp.Pg i j b
    · rfl
    · exact (blkOf_eq_zero le_rfl).trans (blkOf_eq_zero hr).symm
    · exact (twoBlockSizes_eq_zero_of_le le_rfl).trans (twoBlockSizes_eq_zero_of_le hr).symm
  refine ⟨h1, hpar ▸ h2, ?_⟩
  funext PP
  apply Units.ext
  ext a c
  have hPP : PP.1 ∈ (ρ.B i j b).G.Pg := (hp.Pg i j b).symm ▸ PP.2
  have hg := hp.grp i j b g PP.1 hPP PP.2 (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c)
  rw [← h3] at hg
  have hg2 : Units.val (cG.symm g PP) a c =
      Units.val (rTup (Rl.βW j) (ρ.B i j b).G.levT (finE (Wc D j) κ) ⟨PP.1, hPP⟩)
        (Fin.cast (FWT.rank_Wc j).symm a) (Fin.cast (FWT.rank_Wc j).symm c) := hg.symm
  rw [hg2]
  unfold rTup
  erw [upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le hr _), upper_block_val_submatrix _ (mem_blockTriangular_twoBlockSizes_of_le le_rfl _)]
  rfl

theorem sg0_eq_embLL (Rl : RealDat3 D A3 Ks) : sg0 D A3.A = D.what₂.embLL := by
  ext c
  exact congrArg (fun f : D.what₂.LL →+* ℂ => f c) (Links.sgAt_mk _ Rl.hv0)

theorem evW_rho (hU : Rl.toRealDat.LUnif) (hW : Rl.toRealDat.models_HW) {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (g' : S.G) (κ : GA D (Wc D j)) (hκ : IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (cG.symm (S.eG g')) κ)
    (z : S.WL ((j : ℕ) + 1)) (x : GA D (Wc D j)) :
    evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ g' z) x =
      D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi g' : D.what₂.LLˣ) : D.what₂.LL) * evW YS v₀ j z (x * κ) := by
  have hgeq : Rl.eG ((YS.fi j).eG g') = cG.symm (S.eG g') := by
    rw [← YS.geq j g', MulEquiv.symm_apply_apply]
  have hκ' : IsLevelLift (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) κ := hgeq ▸ hκ
  set F := (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e z)) with hFdef
  have hmem : F ∈ Rl.toRealDat.Wall j (sg0 D A3.A) := (hW j _).2.1 ▸ LinearMap.mem_range_self _ _
  have hT := hasType_of_mem_wall Rl j hmem (v₀ j _)
  have hs := level_action_spec hT ⟨κ, hκ'⟩ κ hκ' x
  rw [levChi_flagL, inv_one, one_mul] at hs
  change (Rl.HW j (sg0 D A3.A)).e ((Rl.FW j).j (sg0 D A3.A) ((YS.fi j).e ((S.A ((j : ℕ) + 1)).ρ g' z))) (v₀ j _) x = _
  rw [(YS.fi j).rho, (hU j _).2.2, (YS.fi j).chi]
  change sg0 D A3.A _ * (actG0 (Wc D j) (Rl.βW j) (Rl.datWp j Rl.triv) (Rl.eG ((YS.fi j).eG g')) (F (v₀ j _))) x = _
  rw [hs]
  exact congrArg (· * F (v₀ j _) (x * κ)) (congrArg (fun f : D.what₂.LL →+* ℂ => f _) (sg0_eq_embLL Rl))

end GlobalTheory.SeriesTie.ActProof

namespace GlobalTheory.SeriesTie
open Formalism.IndefR.Lev Formalism.L2.DIV
open scoped TensorProduct

theorem actRead_realRd : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (ρ : Setup D.ntw) (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (ν : ℂ), RealPin Rl cG ρ → Rl.toRealDat.LUnif → Rl.toRealDat.models_HW → ActRead (realRd YS v₀ hρ i j b ν) := by
  intro D Γ _ _ Pl0 I0 T A3 Ks _ _ _ Rl cG S YS v₀ ρ hρ i j b ν hp hU hW
  intro g κ hκ f x
  have hκ' := ActProof.isLift_transfer Rl j hp i b g κ hκ
  change (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 (D.nexp.actG i _ b g f))) x =
    (ν⁻¹ • evK YS v₀ hρ i j b (YS.eF i _ b (Nat.le_add_left _ _) j.2 f)) (x * κ)
  rw [YS.act, Pi.smul_apply, Pi.smul_apply]
  congr 1
  generalize YS.eF i _ b (Nat.le_add_left _ _) j.2 f = y
  induction y using TensorProduct.induction_on with
  | zero => erw [LinearEquiv.map_zero, map_zero]; rfl
  | add y z hy hz => erw [LinearEquiv.map_add, map_add, Pi.add_apply, hy, hz, map_add, Pi.add_apply]
  | tmul a f0 =>
    have hg : S.eG (S.eG.symm g) = g := S.eG.apply_symm_apply g
    have e1 : (NX.actG S i ((j : ℕ) + 1) b (YS.rho _ (Nat.le_add_left _ _) j.2) (YS.chi _ (Nat.le_add_left _ _) j.2) g)
        (a ⊗ₜ f0) = ((NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g)))⁻¹ * a) ⊗ₜ
          (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0) := by
      change (NX.readLL0 S i b (NX.chiL S _ _ (S.eG.symm g)))⁻¹ •
        (a ⊗ₜ[S.Ks] (NX.rhoKG S _ (YS.rho _ (Nat.le_add_left _ _) j.2) (S.eG.symm g) f0)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul]
    erw [e1]
    rw [evK_tmul, evK_tmul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
    have h2 := ActProof.evW_rho Rl j hU hW YS v₀ (S.eG.symm g) κ (hg.symm ▸ hκ') (Subtype.val f0) x
    have he : ρ.e i b (NX.readLL0 S i b (NX.chiL S _ (YS.chi _ (Nat.le_add_left _ _) j.2) (S.eG.symm g))) =
        D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) :=
      hρ.e_LL0 i b _
    have hne : D.what₂.embLL (((S.A ((j : ℕ) + 1)).chi (S.eG.symm g) : D.what₂.LLˣ) : D.what₂.LL) ≠ 0 :=
      (map_ne_zero _).2 (Units.ne_zero _)
    change ρ.e i b _ * evW YS v₀ j ((S.A ((j : ℕ) + 1)).ρ (S.eG.symm g) (Subtype.val f0)) x = _
    rw [h2]
    erw [map_mul, map_inv₀, he]
    field_simp

end GlobalTheory.SeriesTie
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NatCastMemUnder
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie
open Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeriesTie.PlaceChoice

variable {D : D7}

abbrev under (P : Pl D.host.E) : Ideal (𝓞 D.host.K) := P.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))

def choice (D : D7) : Set (Pl D.host.E) :=
  {P | ∃ P', IsConjPl D.host P P' ∧
    (WellOrderingRel (under P) (under P') ∨ (under P = under P' ∧ WellOrderingRel P P'))}

end GlobalTheory.SeriesTie.PlaceChoice

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProductsStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL

private theorem flat_strictMono (d h : ℕ) : StrictMono (fun p : Fin (d * h) =>
    (toLex ⟨(finProdFinEquiv.symm p).1, (finProdFinEquiv.symm p).2⟩ : Σₗ _ : Fin d, Fin h)) := by
  intro p q hpq
  obtain ⟨⟨a, b⟩, rfl⟩ := finProdFinEquiv.surjective p
  obtain ⟨⟨a', b'⟩, rfl⟩ := finProdFinEquiv.surjective q
  simp only [Equiv.symm_apply_apply]
  have h1 : (b : ℕ) + h * a < b' + h * a' := hpq
  rcases lt_trichotomy a a' with hlt | rfl | hgt
  · exact Sigma.Lex.left _ _ hlt
  · exact Sigma.Lex.right _ _ (show b < b' from by
      rw [Fin.lt_def]; omega)
  · exfalso
    have h2 : (a' : ℕ) + 1 ≤ a := hgt
    have h3 := Nat.mul_le_mul_left h h2
    have h4 := b'.2
    rw [Nat.mul_add, Nat.mul_one] at h3
    omega

theorem _root_.GlobalTheory.T.parabolicInduction_in_stages_product_of_products : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (d h : ℕ) (y : Fin d → Fin h → IrrGL k) (N : Fin d → ℕ) (M : ℕ) (hN : ∀ i, ∑ j, (y i j).1 = N i)
    (hM : ∑ i, N i = M)
    (hM' : ∑ p : Fin (d * h), (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1 = M),
    Nonempty ((multiProd (stdBlocks N hM) fun i => prodIrr (y i) (hN i)).Equiv
      (prodIrr (fun p => y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2) hM')) := by
  intro k _ _ _ _ d h y N M hN hM hM'
  have hφ := GlobalTheory.SmGL.Stages.stages_equiv (k := k) d N (fun _ => h) (fun a b => (y a b).1)
    (fun a => stdBlocks (fun b => (y a b).1) (hN a)) _ (fun a b => (y a b).rep) (Fin M) (stdBlocks N hM)
  obtain ⟨E0, ⟨φ⟩⟩ := hφ
  let F : Fin (d * h) ≃ Σₗ _ : Fin d, Fin h :=
    finProdFinEquiv.symm.trans ((Equiv.sigmaEquivProd (Fin d) (Fin h)).symm.trans toLex)
  let E : (Σ p : Fin (d * h), Fin (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1) ≃ Fin M :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ _ : Fin d, Fin h => Fin (y (ofLex c).1 (ofLex c).2).1) F).trans E0
  have hψ := GlobalTheory.SmGL.BlockRename.multiProd_rename (k := k) F (flat_strictMono d h) F.surjective E0 E
    (fun _ _ => rfl) fun c => (y (ofLex c).1 (ofLex c).2).rep
  obtain ⟨ψ⟩ := hψ
  have hχ := GlobalTheory.ProdReorder.multiProd_placing (k := k) E
    (stdBlocks (fun p => (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).1) hM')
    fun p => (y (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2).rep
  obtain ⟨χ⟩ := hχ
  exact ⟨φ.trans (ψ.trans χ)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PlaceInvariantFormKillsVanishingSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

namespace GlobalTheory.DownLift.SplitCoef

theorem form_placeModel_eq_zero_of_vanish : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D), IsStdChar D ψ (-1) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ a b : AE D, IsSplitIdem D a → b * b = b → b * cA D b = 0 → infPart D b = 0 → b * a = a → ∀ (f₀ : WO S T → ℂ) (Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ)), IsThetaFunO ψ S T f₀ → IsPlaceModel ψ (symplO S T) (heisO ψ S T) b (latH S T ΛS ΛT) 1 f₀ Tm → ∀ ℓ, InvForm ψ S T a ℓ → ∀ Ψ : WO S T → ℂ, IsSBHalf b (latH S T ΛS ΛT) Ψ → (∀ t : WO S T, a • t = 0 → Ψ t = 0) → ℓ (Tm Ψ) = 0 := by
  intro D ψ S T hψ ΛS ΛT hS hT a b ha hbb hbc hbinf hba f₀ Tm hf₀ hTm ℓ hℓ Ψ hΨ hΨ0
  have hth : ∀ Ψ', IsSBHalf b (latH S T ΛS ΛT) Ψ' → IsThetaFunO ψ S T (Tm Ψ') := by
    intro Ψ' h'
    have hspan := (GlobalTheory.Chain.StepVac.placeModel_span_ne hψ hS hT hbb hbc hbinf hTm h').1
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hspan
    · rintro _ ⟨u, rfl⟩
      exact GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf₀ u
    · exact Formalism.IndefR.Fock.CCR.theta_zero ψ S T
    · intro x y _ _ hx hy
      exact Formalism.IndefR.Fock.CCR.theta_add hx hy
    · intro c x _ hx
      exact Formalism.IndefR.Fock.CCR.theta_smul hx c
  have hca : cA D b * cA D a = cA D a := by rw [← RingHom.map_mul, hba]
  have hmod : ∀ y, IsHalf (cA D a) y → ℓ (Tm (fun t => ψ (symplO S T t y) * Ψ t)) = ℓ (Tm Ψ) := by
    intro y hy
    have hy' : IsHalf (cA D b) y := fun i j => by rw [← hy i j, ← mul_assoc, hca]
    rw [hTm.modul Ψ hΨ y hy']
    exact hℓ y hy _ (hth Ψ hΨ)
  obtain ⟨k, hk, hinv, hden⟩ := hΨ.2
  have hcomm : ∀ (c : AE D) (x : WO S T), c • (k • x) = k • (c • x) := fun c x =>
    map_nsmul (DistribMulAction.toAddMonoidHom (WO S T) c) k x
  have haa : a * a = a := ha.1
  have hainf : infPart D a = 0 := GlobalTheory.SplitScalar.infPart_splitIdem ha
  obtain ⟨Y, hYne, hY1, -, hY3⟩ := GlobalTheory.T.exists_reps_latticeQuotient_conjugateHalf_orthogonal D ψ S T hψ ΛS ΛT hS hT a haa hainf k hk
  have hzero : (fun t => ∑ y ∈ Y, ψ (symplO S T t y) * Ψ t) = 0 := by
    funext t
    simp only [Pi.zero_apply]
    by_cases ht : Ψ t = 0
    · simp [ht]
    rw [← Finset.sum_mul]
    have hsym : ∀ y ∈ Y, symplO S T t y = symplO S T (a • t) y := by
      intro y hy
      rw [GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.SplitScalar.isHalf_iff _ _).1 (hY1 y hy).1]
    have hx : IsHalf a (a • t) := (GlobalTheory.SplitScalar.isHalf_iff _ _).2 (by rw [smul_smul, haa])
    have hkx : k • (a • t) ∈ latH S T ΛS ΛT := by
      rw [← hcomm a t]
      exact GlobalTheory.SplitScalar.idem_smul_mem haa _ (hden t ht)
    obtain ⟨-, h2⟩ := hY3 (a • t) hx hkx
    by_cases hex : ∃ u ∈ latH S T ΛS ΛT, IsHalf a u ∧ a • t = k • u
    · exfalso
      obtain ⟨u, hu, hau, hxu⟩ := hex
      have hbu : IsHalf b u := fun i j => by rw [← hau i j, ← mul_assoc, hba]
      have e1 : Ψ (t - k • u + k • u) = Ψ (t - k • u) := hinv u hu hbu (t - k • u)
      rw [sub_add_cancel] at e1
      apply ht
      rw [e1]
      apply hΨ0
      rw [smul_sub, hxu, hcomm a u, (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hau, sub_self]
    · rw [Finset.sum_congr rfl fun y hy => by rw [hsym y hy], h2 hex, zero_mul]
  have hsum : ∑ y ∈ Y, ℓ (Tm (fun t => ψ (symplO S T t y) * Ψ t)) =
      ℓ (Tm (fun t => ∑ y ∈ Y, ψ (symplO S T t y) * Ψ t)) := by
    rw [← map_sum ℓ, ← map_sum Tm]
    congr 2
    funext t
    simp [Finset.sum_apply]
  rw [hzero, map_zero, map_zero, Finset.sum_congr rfl fun y hy => hmod y (hY1 y hy).1, Finset.sum_const,
    nsmul_eq_mul] at hsum
  have hc : (Y.card : ℂ) ≠ 0 := by exact_mod_cast hYne.card_pos.ne'
  exact (mul_eq_zero.1 hsum).resolve_left hc

end GlobalTheory.DownLift.SplitCoef

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RallisConvOfSteps
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift

theorem rallisConv_of_steps : ∀ D : D7, SWPair D → EisAbs D → KerAbs D → TermMove D → TermInv D → CuspKill D → RallisConv D := by
  intro D hSW hEis hKer hMove hInv hKill θ ψ V W χV χW om hθ hω hsig hpos hbig νV 𝓗 νW 𝓖 μ 𝓕 hνV h𝓗 hνW h𝓖
    hμ h𝓕 h1 f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  have hS : SWSetup ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 (lagFrame W) :=
    { weil := hω, sigOK := hsig, pos := hpos, big := hbig, haarV := hνV, fdV := h𝓗, haarW := hνW, fdW := h𝓖,
      covol := ⟨hμ, h𝓕, h1⟩, frame := lagFrame_isLagFrame W }
  obtain ⟨K1, K2, K3⟩ := GlobalTheory.T.rallis_inner_product_kernel_identity D hKer hSW ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁
    hφ₂ hc₂
  obtain ⟨-, E2, E3⟩ := GlobalTheory.T.siegelWeilSum_doubleIntegral_exchange_cuspForms D hEis ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁ hφ₂ hc₂
  obtain ⟨G1, G2⟩ := GlobalTheory.T.lagrangianGraphs_sum_eq_matrixCoeff_integral D hEis hMove ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂ hφ₁ hc₁
    hφ₂ hc₂
  have N := GlobalTheory.T.rallis_nonGraphLagrangian_sum_eq_zero_cuspidal D hEis hMove hInv hKill (GlobalTheory.RawLift.TermCont.continuous_lagTerm D) ψ V W χV χW om νV 𝓗 νW 𝓖 μ 𝓕 _ hS θ hθ f₁ f₂ φ₁ φ₂ hf₁ hf₂
    hφ₁ hc₁ hφ₂ hc₂
  refine ⟨K1, K2, G1, ?_⟩
  rw [K3, E3, ← E2.tsum_subtype_add_tsum_subtype_compl {Y : Lag W | Y.1.comap (LinearMap.inl D.host.E _ _) = ⊥}]
  erw [N, add_zero]
  rw [← G2]
  rfl

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesIdempotentMulOfMapsToParabolicInductionStatement
section
open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys GlobalTheory.TypeLeaf Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seriesIdempotent_mul_of_maps_to_parabolicInduction : ∀ (g : ℕ) [Fact g.Prime] (S : Sys g) (n a b : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) (W W' : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] (σ : Representation ℂ (GL (Fin a) ℚ_[g]) W) (ρ : Representation ℂ (GL (Fin b) ℚ_[g]) W'), IsIrrRep π → MapsToProd π σ ρ → ∀ F, Has S π F → ∃ f f', Has S σ f ∧ Has S ρ f' ∧ F = f * f' := by
  first | exact @GlobalTheory.SerSys.Prod.series_of_mapsToProd | exact GlobalTheory.SerSys.Prod.series_of_mapsToProd | (intros; apply GlobalTheory.SerSys.Prod.series_of_mapsToProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideEigenCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.CoefDuty
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.side_eigen_character : HeckeStdPlain → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : SideA D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big₀ big₁ : D.what₂.places.Pl → Finset ℂ) (L₀ L₁ : LocAll (lay0 D)), Built A M C tp.tup big₀ L₀ → Built A M C tp.tup big₁ L₁ → ∀ (i₀ : L₀.lay.fixZ.nd.Loc) (i₁ : L₁.lay.fixZ.nd.Loc), L₀.lay.fixZ.nd.w i₀ = L₁.lay.fixZ.nd.w i₁ → L₀.lay.fixZ.nd.j i₀ = L₁.lay.fixZ.nd.j i₁ → ∀ φ : L₀.lay.fixZ.nd.O i₀ →+* L₁.lay.fixZ.nd.O i₁, (∀ z, iotaO L₁.lay.fixZ.nd L₁.lay.fixZ.naut i₁ (φ z) = iotaO L₀.lay.fixZ.nd L₀.lay.fixZ.naut i₀ z) → (∀ (z : ℤ_[L₀.lay.fixZ.nd.l i₀]) (z' : ℤ_[L₁.lay.fixZ.nd.l i₁]), HEq z z' → φ (algebraMap _ _ z) = algebraMap _ _ z') → ∀ c, 1 ≤ c → c ≤ D.R.t → ∀ σ : GE L₁.lay.fixZ.nd, ((L₁.lay.fixZ.nd.chi i₁ c σ : (L₁.lay.fixZ.nd.O i₁)ˣ) : L₁.lay.fixZ.nd.O i₁) = φ ((L₀.lay.fixZ.nd.chi i₀ c σ : (L₀.lay.fixZ.nd.O i₀)ˣ) : L₀.lay.fixZ.nd.O i₀) := by
  first | exact @GlobalTheory.ChiExtend.chi_eq_of_ext | exact GlobalTheory.ChiExtend.chi_eq_of_ext | (intros; apply GlobalTheory.ChiExtend.chi_eq_of_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupAtPlaceDenseInDecompositionGroupStatement
section
open NumberField IsDedekindDomain Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.WeilDeligne
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w), ∀ d ∈ Dec (F := E) A, ∀ y : Ω, ∃ τ ∈ Weil h, τ y = d y := by
  first | exact @GlobalTheory.WeilDeligne.exists_weil_apply_eq | exact GlobalTheory.WeilDeligne.exists_weil_apply_eq | (intros; apply GlobalTheory.WeilDeligne.exists_weil_apply_eq <;> assumption)
end

