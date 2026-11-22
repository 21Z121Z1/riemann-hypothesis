import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0852
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0824
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0444
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0677
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0730
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0854
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0710
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0787
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0706
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0681
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0151
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0494
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0024
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorOInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1720
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0022
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0853
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralFlipSplitPlacesInvariantFormPhaseStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centralFlip_splitPlaces_invariantForm_phase : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (χV χW : (AE D)ˣ →* Circle) (om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χV χW om → ∀ (T : Finset (Formalism.L2.DIV.Pl D.host.E)) (eT : AE D) (m : ℕ) (z : GA D V) (x : (AE D)ˣ) (ℓ : (WO V W → ℂ) →ₗ[ℂ] ℂ), IsIdemSum eT T → m ≠ 0 → Formalism.L2.Theta.mt V z = flipElt eT m • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) → IsFlipDet V eT m x → (∀ y : WO V W, IsHalf (cA D eT) y → ∀ φ : WO V W → ℂ, IsThetaFunO ψ V W φ → ℓ (heisO ψ V W y φ) = ℓ φ) → ∃ r : ℝ, 0 < r ∧ ∀ f : WO V W → ℂ, IsThetaFunO ψ V W f → ℓ (om (z⁻¹, 1) f) = (r : ℂ) * ((χW x : Circle) : ℂ)⁻¹ * ℓ f := by
  first | exact @GlobalTheory.LevelSeries.centralFlip_phase | exact GlobalTheory.LevelSeries.centralFlip_phase | (intros; apply GlobalTheory.LevelSeries.centralFlip_phase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeffSpaceLevelFixesFockVectorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffSpaceLevel_fixes_fockVectors : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, LevFix R i t := by
  first | exact @GlobalTheory.RawLift.LevelFix.levFix | exact GlobalTheory.RawLift.LevelFix.levFix | (intros; apply GlobalTheory.RawLift.LevelFix.levFix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoefficientVanishesOffLevelGroupAtBadPrime
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.BadPlace

noncomputable section

namespace GlobalTheory.BadPlace

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem actO_one_inv_half {D : D7} {S T : HSp D} {e f : AE D} (hef : e * f = e) {γ : GA D T}
    (hγ : GlobalTheory.RawLift.TrivAt T f γ) {y : WO S T} (hy : IsHalf e y) : actO S T 1 γ⁻¹ y = y := by
  have h1 : f • Formalism.L2.Theta.mt T γ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    ext a b
    have := hγ a b
    rw [Matrix.sub_apply, mul_sub] at this
    rw [Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul]
    exact sub_eq_zero.1 this
  have h2 : Formalism.L2.Theta.mt T γ * Formalism.L2.Theta.mt T γ⁻¹ = 1 := by
    simp only [Formalism.L2.Theta.mt, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
  have h3 : f • Formalism.L2.Theta.mt T γ⁻¹ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    calc f • Formalism.L2.Theta.mt T γ⁻¹ = (f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) * Formalism.L2.Theta.mt T γ⁻¹ := by
          rw [Matrix.smul_mul, Matrix.one_mul]
      _ = (f • Formalism.L2.Theta.mt T γ) * Formalism.L2.Theta.mt T γ⁻¹ := by rw [h1]
      _ = f • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by rw [Matrix.smul_mul, h2]
  have h4 : e • Formalism.L2.Theta.mt T γ⁻¹ = e • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D)) := by
    rw [← hef, ← smul_smul, h3, smul_smul]
  have hy' : e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = y := by
    ext a b
    rw [Matrix.smul_apply, smul_eq_mul]
    exact hy a b
  have hone : Formalism.L2.Theta.mt S (1 : GA D S)⁻¹ = 1 := by
    simp only [inv_one, Formalism.L2.Theta.mt, map_one, Units.val_one]
  unfold actO
  rw [hone, Matrix.mul_one]
  calc HMul.hMul (Formalism.L2.Theta.mt T γ⁻¹) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))
      = HMul.hMul (Formalism.L2.Theta.mt T γ⁻¹) (e • (y : Matrix (Fin T.rank) (Fin S.rank) (AE D))) := by rw [hy']
    _ = HMul.hMul (e • Formalism.L2.Theta.mt T γ⁻¹) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = HMul.hMul (e • (1 : Matrix (Fin T.rank) (Fin T.rank) (AE D))) (y : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
        rw [h4]
    _ = y := by rw [Matrix.smul_mul, Matrix.one_mul, hy']

theorem pureTensorL_one {ι X : Type} (A : ι → (X → ℂ) → (X → ℂ)) (f : X → ℂ) : pureTensorL A f 1 = f := by
  have e : (1 : MvPolynomial ι ℂ) = MvPolynomial.basisMonomials ι ℂ 0 := by
    rw [MvPolynomial.coe_basisMonomials]; rfl
  rw [e]
  unfold pureTensorL
  rw [Module.Basis.constr_basis]
  simp [opPow]

set_option maxHeartbeats 2000000 in

theorem coef_bad_vanish : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ P, P ∈ R.Pg ∨ P ∈ R.Q t → ∀ e f, IsPrimeIdem P e f → ∀ γ ∈ GfC (Wc D i), TrivAt (Wc D i) f γ → ∀ k, SuppF (Wc D i) f k → k ∉ levW R i → thetaIP μ 𝓕 (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) = 0 := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hC P hP e f hPI γ _ hTr k hk hlev
  obtain ⟨ea, Tm, c, hIS, hSe, hee, hf, hψ, hSV, hSW, hv0, hvl, hTm, hSB2, hSB1, hvP, hωk⟩ :=
    GlobalTheory.T.thetaLiftVector_schroedingerImage_at_levelPrime D G Pl0 T A Ks R F hL hF i t P hP e f hPI k hk
  have hdisj := GlobalTheory.T.thetaHalfSpaceDatum_translate_disjoint_support D G Pl0 T A Ks R F hL hF i t ea hIS P hP e f hPI k hk hlev
  have hW := (hF i t).datum
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    rwa [RealDat.ptP, pureTensorO, pureTensorL_one] at this
  have hef : e * f = e := by
    rw [hf, mul_add, hSe.1, hSe.2.1, add_zero]
  have e1 := GlobalTheory.WeilPairing.thetaInner_weilRep D R.ψ _ _ _ _ (R.ωP i t) μ 𝓕 hW hC (1, γ⁻¹)
    (R.ωP i t (1, γ * k) (R.vP i t)) (R.vP i t) (hW.om_pres (1, γ * k) _ hth) hth
  rw [← e1, ← Module.End.mul_apply, ← map_mul]
  have e2 : ((1 : GA D (Vc D i)), γ⁻¹) * (1, γ * k) = (1, k) := by
    ext
    · exact mul_one 1
    · exact (inv_mul_cancel_left γ k)
  rw [e2, hωk, thetaInner_smul_left]
  have hz := GlobalTheory.T.schrodingerImages_orthogonal_disjoint_splitSupport D R.ψ (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) _ ea e (R.vacP i) Tm μ 𝓕 hψ hSV hSW hIS hSe hee hv0 hvl
    hTm hC _ _ hSB1 hSB2 (fun x x' hxx' h1 h2 => hdisj x x' (by rw [hf]; exact hxx') h1 h2) (R.ωP i t (1, γ⁻¹))
    (fun g hg => hW.om_pres _ _ hg) (fun y hy g hg => by
      rw [hW.om_heis _ _ _ _ hg, actO_one_inv_half hef hTr hy])
  rw [← hvP] at hz
  rw [hz, mul_zero]

end GlobalTheory.BadPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftAdjointEqUpwardThetaIntegral
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift
open GlobalTheory.AdjUp

namespace GlobalTheory.AdjUp

set_option maxHeartbeats 1000000 in

theorem adjFormula_holds : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, AdjFormula R i t := by
  intro hP D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t th hth v hv n b
  refine (GlobalTheory.T.petersson_integral_formula hP D G Pl0 T A Ks R F hL i v hv).elim fun P hPx => ?_
  refine (GlobalTheory.T.inner_product_integral_formula D G Pl0 T A Ks R F hL i t).elim fun c hcx => ?_
  have hval : ∀ u, val R i v (th u) = R.thF i t u (fun ρ => v ρ) := fun u => by
    show (R.HW i (sg0 D A)).e (th u) (fun ρ => v ρ) = _
    rw [hth u]
  have hK0 : ∀ k h, upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v 0) h = 0 := fun k h => by
    rw [val_zero]; exact upLift_zero _ _ _ _ h
  exact adjoint_formula_of_kernel th b ((R.νW i).restrict (R.fdW i)) ((R.νV i t).restrict (R.fdV i t)) (val R i v)
    (fun u => R.thF i t u (fun ρ => v ρ)) (R.extV i t)
    (fun k y h => upLift (R.ωP i t) (R.νW i) (R.fdW i) (jointVec R i t v (b k)) (val R i v y) h) P c hPx.1 hcx.1 hPx.2
    hval (val_zero R i v) hK0 hcx.2 (fun y u => GlobalTheory.T.adjoint_pairing_unfolding_downward_lift hP D G Pl0 T A Ks R F hL hF i t v n b y u)
    (fun y => GlobalTheory.T.upwardVectorLift_mem_range_coefficientExtension hP D G Pl0 T A Ks R F hL hF i t v n b y)

end GlobalTheory.AdjUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardLiftLevelActsByInverseCharacter
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite

noncomputable section

namespace GlobalTheory.DownLift.TypeLaw

variable {D : D7}

theorem setIntegral_mul_right_of_fd {G : Type} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ)
    (k : G) (hk : Measure.map (fun g => g * k) μ = μ) (f : G → ℂ) (hf : ∀ γ ∈ Γ, ∀ g, f (γ * g) = f g) :
    ∫ g in 𝓕, f (g * k) ∂μ = ∫ g in 𝓕, f g ∂μ := by
  have hmp : MeasurePreserving (fun g : G => g * k) μ μ := ⟨measurable_mul_const k, hk⟩
  have hemb : MeasurableEmbedding (fun g : G => g * k) := measurableEmbedding_mulRight k
  have h2 : IsFundamentalDomain Γ ((fun g : G => g * k) ⁻¹' 𝓕) μ := by
    refine h𝓕.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id ?_
    intro γ g
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ (γ : Γ) (g : G), (fun g : G => f (g * k)) (γ • g) = (fun g : G => f (g * k)) g := by
    intro γ g
    simp only [Subgroup.smul_def, smul_eq_mul, mul_assoc]
    exact hf γ γ.2 _
  rw [h𝓕.setIntegral_eq h2 hinv]
  exact hmp.setIntegral_preimage_emb hemb f 𝓕

theorem flagOneLevel_eq_self_of_trivial {n : ℕ} (L : LevDat D.host.E ℂ n) (hL : L.P = LevelP.triv L.Pg L.r ℂ) : flag1L L = L := by
  cases L
  simp only at hL
  subst hL
  rfl

theorem adForms_right {G Γ W : Type} [Group G] [Group Γ] (ι : Γ →* G) [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup G) (χ : J →* ℂˣ) (F : G → W)
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms ι ρ J χ) (x : G) (k : J) : F (x * k) = (χ k : ℂ) • F x := by
  have h1 := hF 1 x k
  rw [map_one, one_mul, map_one, Module.End.one_apply] at h1
  exact h1

theorem adForm_type (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (c : CoefA V)
    (F : Formalism.IndefR.Bridge.Gf V → c.W)
    (hF : F ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ)
    (κ : GA D V) (hκ : κ ∈ levG V β (flag1L L)) (x : Formalism.IndefR.Bridge.Gf V) :
    F (x * (finHom V).rangeRestrict κ) = levChi V β (flag1L L) κ • F x := by
  have hmem : (finHom V).rangeRestrict κ ∈ (levEnv V β L).J := by
    show finE V κ ∈ Formalism.L2.DIV.lev D.sp.cm V.gram β (flag1L L)
    exact hκ.2
  have h1 := adForms_right (W := c.W) (Formalism.IndefR.Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ F hF x ⟨_, hmem⟩
  have hχ : (((levEnv V β L).χ ⟨_, hmem⟩ : ℂˣ) : ℂ) = levChi V β (flag1L L) κ := rfl
  rw [hχ] at h1
  exact h1

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

theorem datVt_P {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t : T) :
    (R.datVt i t).P = LevelP.triv (R.datVt i t).Pg (R.datVt i t).r ℂ := by
  simp [LevCh.datVt, datY, LevelP.conj, LevelP.triv]
  rfl

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

theorem extV_type (R : RealDat D A Ks) (hM : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (κ : GA D (Vc D i))
    (hκ : κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t)) (h : GA D (Vc D i)) :
    R.extV i t y (h * κ) = levChi (Vc D i) (R.βV i) (R.datVt i t) κ • R.extV i t y h := by
  have hL : flag1L (R.datVt i t) = R.datVt i t := flagOneLevel_eq_self_of_trivial _ (datVt_P R i t)
  have hκ1 : κ ∈ levG (Vc D i) (R.βV i) (flag1L (R.datVt i t)) := by rw [hL]; exact hκ
  have hc0 : levChi (Vc D i) (R.βV i) (R.datVt i t) κ ≠ 0 := levChi_ne_zero _ κ
  have hchi : levChi (Vc D i) (R.βV i) (flag1L (R.datVt i t)) κ = levChi (Vc D i) (R.βV i) (R.datVt i t) κ := by rw [hL]
  have hyA : (R.HV i t).e y ∈ Formalism.IndefR.Bridge.AdForms (Formalism.IndefR.Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv (Vc D i) (R.βV i) (R.datVt i t)).J (levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ :=
    (hM.HV i t).2.1.le ⟨y, rfl⟩
  have hty : ∀ x, (R.HV i t).e y x = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ •
      (R.HV i t).e y (x * (finHom (Vc D i)).rangeRestrict κ) := by
    intro x
    have h1 := adForm_type (Vc D i) (R.βV i) (R.datVt i t) (R.cV i) ((R.HV i t).e y) hyA κ hκ1 x
    have h2 : (R.HV i t).e y (x * (finHom (Vc D i)).rangeRestrict κ) =
        levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.HV i t).e y x :=
      h1.trans (congrArg (· • (R.HV i t).e y x) hchi)
    exact (inv_smul_smul₀ hc0 _).symm.trans (congrArg ((levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ • ·) h2.symm)
  have e1 := GlobalTheory.ThetaProjEquiv.ext_shift (R.cV i) (hM.cV i) κ hκ.1 _ hc0 ((R.HV i t).e y) ((R.HV i t).e y) hty h
  have hx : ∀ z, R.extV i t y z = (R.cV i).ext ((R.HV i t).e y) z := fun z => rfl
  have e2 : (R.cV i).ext (levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.HV i t).e y) h =
      levChi (Vc D i) (R.βV i) (R.datVt i t) κ • (R.cV i).ext ((R.HV i t).e y) h := by
    exact congrFun (LinearMap.map_smul (R.cV i).ext _ ((R.HV i t).e y)) h
  exact (hx (h * κ)).trans (e1.symm.trans (e2.trans (congrArg (levChi (Vc D i) (R.βV i) (R.datVt i t) κ • ·) (hx h).symm)))

end GlobalTheory.DownLift.TypeLaw

namespace GlobalTheory.DownLift.TypeLaw

theorem alg_step {a b c d d' : ℂ} (hc : c ≠ 0) (hab : a = b) (hd : d' = c * d) : a * d = c⁻¹ * (b * d') := by
  rw [hab, hd, mul_left_comm b c d, inv_mul_cancel_left₀ hc]

theorem downInt_level : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (f : WO (Vc D i) (Wc D i) → ℂ), IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ κ ∈ levG (Vc D i) (R.βV i) (R.datVt i t), ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)), downInt R i t y (R.ωP i t (κ, 1) f) l g = (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * downInt R i t y f l g := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y f hf κ hκ l g
  have hM := hG.core.models
  have hc0 : levChi (Vc D i) (R.βV i) (R.datVt i t) κ ≠ 0 := levChi_ne_zero _ κ
  have hFn : ∀ h, l (R.extV i t y (h * κ)) = levChi (Vc D i) (R.βV i) (R.datVt i t) κ * l (R.extV i t y h) := by
    intro h
    exact (congrArg l (extV_type R hM i t y κ hκ h)).trans (l.map_smul _ _)

  have hth : ∀ h, thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) f) = thetaKO (R.ωP i t) (h * κ) g f := by
    intro h
    have hm : ((h, g) : GA D (Vc D i) × GA D (Wc D i)) * (κ, 1) = (h * κ, g) := by
      rw [Prod.mk_mul_mk, mul_one]
    show R.ωP i t (h, g) (R.ωP i t (κ, 1) f) 0 = R.ωP i t (h * κ, g) f 0
    rw [← hm, map_mul, Module.End.mul_apply]

  let Φ : GA D (Vc D i) → ℂ := fun h => thetaKO (R.ωP i t) h g f * l (R.extV i t y h)
  have hΦ : ∀ γ ∈ GQ (Vc D i), ∀ h, Φ (γ * h) = Φ h := by
    intro γ hγ h
    have ht : thetaKO (R.ωP i t) (γ * h) g f = thetaKO (R.ωP i t) h g f := by
      have hm : ((γ, 1) : GA D (Vc D i) × GA D (Wc D i)) * (h, g) = (γ * h, g) := by
        rw [Prod.mk_mul_mk, one_mul]
      show R.ωP i t (γ * h, g) f 0 = R.ωP i t (h, g) f 0
      rw [← hm, map_mul, Module.End.mul_apply]
      exact (hP i t).datum.om_aut γ hγ 1 (GQ (Wc D i)).one_mem _ ((hP i t).datum.om_pres _ _ hf)
    have hl : l (R.extV i t y (γ * h)) = l (R.extV i t y h) :=
      congrArg l (GlobalTheory.ThetaProjEquiv.extV_left R hM.HV i t y γ hγ h)
    exact congrArg₂ (· * ·) ht hl

  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.TwistAdelicTop.locallyCompact_secondCountable_borel_countable (Vc D i)
  have : IsTopologicalGroup (GA D (Vc D i)) :=
    inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig (Vc D i).gram))
  have hH : (R.νV i t).IsHaarMeasure := (hM.νV i t).1.1
  have hmap := GlobalTheory.haar_map_mul_right_of_mem_compact_subgroup (R.νV i t) _
    (GlobalTheory.ParahoricCompact.isCompact_levG (Vc D i) (R.βV i) (R.datVt i t)) κ hκ
  have hint := setIntegral_mul_right_of_fd (GQ (Vc D i)) (R.νV i t) (R.fdV i t) (hM.νV i t).2 κ hmap Φ hΦ
  have hfun : (fun h => thetaKO (R.ωP i t) h g (R.ωP i t (κ, 1) f) * l (R.extV i t y h)) =
      fun h => (levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * Φ (h * κ) := by
    funext h
    exact alg_step hc0 (hth h) (hFn h)
  exact (congrArg (fun φ : GA D (Vc D i) → ℂ => ∫ h in R.fdV i t, φ h ∂(R.νV i t)) hfun).trans
    ((integral_const_mul _ _).trans (congrArg ((levChi (Vc D i) (R.βV i) (R.datVt i t) κ)⁻¹ * ·) hint))

end GlobalTheory.DownLift.TypeLaw
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSectionMulAdelicFunctionLevelCoverStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix
open GlobalTheory.CompRat

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_mul_adelic_function_level_cover : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (U : Unf Xo c σ r) (dict : GA D V → Σ k, Frame (U.X k).Ψ r) (io : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)) (g : ℕ) (e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (ik : U.Comp → Fin F.n) (φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ) (th : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ), IotaOK Dw V io → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∀ k, ModelW V hr (U.X k)) → DictLat U V hr dict io e F ik φ th x₀ → (∀ h, (dict h).2 ∈ (U.X (dict h).1).dom) → IsUnf U → FnAlgClosed Xo c → ∀ w : GA D V → c.F, (∀ h h' : GA D V, finHom V h = finHom V h' → w h = w h') → (∀ γ ∈ GQ V, ∀ h, w (γ * h) = w h) → (∀ u : GA D V, gLat V u = latHat V → FinCong V l.M u → ∀ h, w (h * u) = w h) → ∀ (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ sec Xo c a n, ∃ f' ∈ sec Xo c a n, (∀ h : GA D V, rdU U f' (dict h).1 (dict h).2 = σ (w h) * rdU U f (dict h).1 (dict h).2) ∧ (∀ la : ∀ k, ReciprocityTheory.ChartRestriction.G.FD.Wt (U.X k).Ψ r, rdU U f ∈ holSub0 U.X la → rdU U f' ∈ holSub0 U.X la) ∧ ∀ lam : HeightOneSpectrum (𝓞 c.F), (∀ h, lam.valuation c.F (w h) ≤ 1) → (∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f) → ∀ v ∈ valSet Xo c (algCls Xo c) lam, 0 ≤ v f' := by
  first | exact @GlobalTheory.CompRat.exists_sec_mul_adelic_fun | exact GlobalTheory.CompRat.exists_sec_mul_adelic_fun | (intros; apply GlobalTheory.CompRat.exists_sec_mul_adelic_fun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTwistDetCharEqOneOfSupportedTypePlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodTwist_detChar_eq_one_of_supported_typePlaces : ∀ (D : D7) (S T : HSp D) (B : Base S T), B.Good → S.SigOK → ∀ (A : Type) [CommGroup A] (t : Twist D A), t.Good → B.admitted t.Q → ∀ (u : G0 B.G.Pg T.rank) (κ : GA D T), Lev.IsLevelLift T B.F.βT B.G.levT u κ → SuppAt (idem B.G.Pg) T κ → detChar T t.chi κ = 1 := by
  first | exact @GlobalTheory.TwistTypeDet.detChar_eq_one_of_suppAt | exact GlobalTheory.TwistTypeDet.detChar_eq_one_of_suppAt | (intros; apply GlobalTheory.TwistTypeDet.detChar_eq_one_of_suppAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCartanInvOneOfOnb
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RawLift

namespace GlobalTheory.RawLift.VecNonzero

theorem thetaInner_self_ne_zero {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} (hψ : IsStdChar D ψ (-1))
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (h0 : f ≠ 0) {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}
    (hμ : IsCovolOne (ratL T S) μ 𝓕) : thetaIP μ 𝓕 f f ≠ 0 := by
  obtain ⟨i1, i2, i3, i4, i5, K, hK, hKc⟩ := GlobalTheory.AdelicMatrixLattice.lattice D T S
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  obtain ⟨-, c, hc⟩ := GlobalTheory.exists_normalise_meanSquare_of_cocompact (WO S T) (ratL T S) K hK hKc f hf.cont h0
    (by
      rintro _ ⟨γ, rfl⟩ w
      exact (congrArg norm (hf.quasi γ w)).trans (by rw [norm_mul, hψ.1.2.1, one_mul]))
  have h1 := hc μ 𝓕 hμ.1 hμ.2.1 hμ.2.2
  have e1 : thetaIP μ 𝓕 f f = ((∫ w in 𝓕, ‖f w‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    unfold thetaIP
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  intro h
  rw [e1, Complex.ofReal_eq_zero] at h
  simp only [norm_mul, mul_pow] at h1
  rw [integral_const_mul, h, mul_zero] at h1
  exact zero_ne_one h1

end GlobalTheory.RawLift.VecNonzero

namespace GlobalTheory.RawLift

open GlobalTheory.RawLift.VecNonzero

open scoped ComplexOrder in

theorem isCartanInv_one_of_onb {k : ℕ} {Gm B : Matrix (Fin k) (Fin k) ℂ} (h : IsONBasis Gm 1 B k) : IsCartanInv Gm 1 := by
  obtain ⟨ε, hε, hG, -⟩ := h
  have e1 : ∀ a, (ε a : ℂ) = 1 := fun a => by
    rcases hε a with h | h
    · simp [h.1]
    · exact absurd a.2 (not_lt.2 h.2)
  have hB : Bᴴ * Gm * B = 1 := by
    rw [hG]
    simp only [e1, Matrix.diagonal_one]
  have hu : IsUnit B.det := Matrix.isUnit_det_of_left_inverse hB
  have h1 := Matrix.mul_nonsing_inv B hu
  have h2 : Gm = (B⁻¹)ᴴ * B⁻¹ := by
    have h3 : (B⁻¹)ᴴ * (Bᴴ * Gm * B) * B⁻¹ = (B⁻¹)ᴴ * B⁻¹ := by rw [hB, Matrix.mul_one]
    have h4 : (B⁻¹)ᴴ * Bᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    rw [← h3]
    simp only [Matrix.mul_assoc, h1, Matrix.mul_one]
    rw [← Matrix.mul_assoc, h4, Matrix.one_mul]
  refine ⟨Matrix.mul_one _, by simp, ?_⟩
  rw [Matrix.mul_one, h2]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (by
      rw [Matrix.det_nonsing_inv]; exact hu.ringInverse)))

theorem vecNe : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Laws R F → R.FullP → ∀ i t, VecNe R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hL hF i t μ 𝓕 hμ
  have hW := hL.thP.ωP i t
  have hth : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hL.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hv0 : R.vP i t ≠ 0 := GlobalTheory.AdTh.VecNe.thPVec_ne_zero
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βV i))
    (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.lev.βW i))
    ((D.sp.W_rank _ (Nat.le_add_left _ _) i.2).trans_le (r_le_V i)) (hL.thP.vP i t)
  refine ⟨thetaInner_self_ne_zero hW.std hth hv0 hμ, ?_⟩
  obtain ⟨-, -, v, w, hv1, -, hio⟩ := hL.thP.ioP i t
  have hvac := GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hL.thP.vP i t) hth
  have hinj := GlobalTheory.FockVecInj.pureTensorO_injective D R.ψ R.θ (Vc D i) (Wc D i) hW.std hL.models.inf (fun _ => 1) (R.BV i)
    (cart (R.MW i (sg0 D A))) (onb (R.MW i (sg0 D A))) (fun _ => (Vc D i).rank) (fun τ => ((Wc D i).sig (tauE D τ)).1)
    (fun τ => isCartanInv_one_of_onb (hL.models.BV i τ)) (GlobalTheory.AdTh.VecFock.isCartanInv_cart _) (hL.models.BV i)
    (fun τ => GlobalTheory.AdTh.VecFock.isONBasis_onb _ τ _ (hL.models.order i τ)) (D.sp.V_sig _) (D.sp.W_sig _) _ hth hvac hv0
  refine ⟨fun ρ => v ρ, w, hv1, ?_⟩
  have hj : jointVec R i t (fun ρ => v ρ) w = R.ptP i t (RealDat.Delta i) := by
    unfold jointVec
    rw [hio]
  rw [hj]
  refine thetaInner_self_ne_zero hW.std (hL.thP.pt_theta i t _) (fun h => ?_) hμ
  refine GlobalTheory.AdTh.IoExtPf.Delta_ne i (hinj ?_)
  exact h.trans (map_zero (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) (R.vP i t))).symm

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLiftingTheoremAOfBlochKatoTateDualityEulerC
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory

theorem theoremA_closing : GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ C : ℝ, 160 ≤ C → ElementDenominator.Conclusion1 D C := by
  intro hBK hTD hEC D HW F Cm C hC
  exact GlobalTheory.T.integralityFromMetric_of_160_le D HW F Cm 23 32 32 C hC (GlobalTheory.T.localLifting_theoremA_hypotheses_admitted hBK hTD hEC D HW F Cm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanTranslatesConjugateHalfTwistPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_translates_conjugateHalf_twistPlace : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)), T.rank ≤ S.rank → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), ∀ N : ℕ, IsBaseFrame S βS ΛS N → Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ (e : AE D) (PP : Pl D.host.E), Formalism.L2.NTheta.IsIdemAt e PP → ∀ ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ, ξ PP ≠ 1 → ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latH S T ΛS ΛT) Φ → (∀ κ : GA D S, SuppAt e S κ → κ ∈ GfC S → finE S κ ∈ St βS → redFn βS PP (finE S κ) ∈ blockTri (blk2 T.rank) → (∀ PP', PP' ≠ PP → ¬ Formalism.IndefR.Lev.IsConjPl PP PP' → redFn βS PP' (finE S κ) = 1) → ∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → Φ (actO S T κ 1 x) * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) x' = Φ x * adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)) (actO S T κ 1 x')) → Φ ∈ Submodule.span ℂ (translT S T (cA D e) (adjDat S T βS βT e (omegaQ {PP} T.rank ξ (-1)))) := by
  first | exact @GlobalTheory.DownLift.ConjHalfGen.mem_span_translT | exact GlobalTheory.DownLift.ConjHalfGen.mem_span_translT | (intros; apply GlobalTheory.DownLift.ConjHalfGen.mem_span_translT <;> assumption)
end

