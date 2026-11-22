import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0856
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0977
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0981
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0947
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0980
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2130
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0013
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1986
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0985
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0312
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle1004
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0193
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0019
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0776
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0884
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0788

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RationalPhaseThetaSeriesExpandsCuspFormsSmallFieStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalPhaseThetaSeries_expands_cuspForms_smallField : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), 8 * D.R.f * D.R.r + 4 ≤ D.R.nV → LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → ∀ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) Rl.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ) (fun j τ => Bridge.lamLdef (Vc D j).rank ((j : ℕ) + 1) τ) gramR c0R c0L → CoefficientBaseChange Rl.toRealDat j (O j).jL (inC (O j).c') (c0L j) (O j).c0' → ∀ (u : ∀ ρ, lowT (Rl.MW j (sg0 D A3.A)) ρ), (∀ ρ, (u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ) = v₀ j _ ρ) → ∀ (ph₀ : ℂ), GlobalTheory.SeriesTie.IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph₀ → ∀ (c : VsV D j ℂ →ₗ[ℂ] (Rl.cV j).W), ExtC Rl.toRealDat j (inC (O j).c') (O j).c0' c → ∀ (v : VsV D j D.what₂.LL), (∀ m, ∃ q : ℚ, MvPolynomial.coeff m (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) = (q : D.what₂.LL)) → ∀ (x : VsV D j ℂ), (x : Pol ℂ D.what₂.Tau (Vc D j).rank) = MvPolynomial.map D.what₂.embLL (v : Pol D.what₂.LL D.what₂.Tau (Vc D j).rank) → ∀ h ∈ GfC (Vc D j), ∃ (n : ℕ) (e : Fin n → ℂ) (f : Fin n → T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n), Expands (O j) (κ j) (fun g => ph₀ * ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (c x) g) e f ∧ ∀ k, e k ∈ (embLL0 D).fieldRange := by
  first | exact @GlobalTheory.SeriesTie.RatExpand.expands_of_isRatPhase | exact GlobalTheory.SeriesTie.RatExpand.expands_of_isRatPhase | (intros; apply GlobalTheory.SeriesTie.RatExpand.expands_of_isRatPhase <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RowLocalAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowSphSmall

theorem rowLoc_overRows : PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, OverRows fun _ _ _ _ w Z _ _ z _ Y =>
    ∀ Rw, ParIn hL (w.st Z).toD7 (TC.cf w.I w.l Z) (repOf Y) Rw → ∀ σ, RowLoc (w.st Z).toD7 Rw σ := by
  intro hP hL
  refine EvG.imp (GlobalTheory.T.spherical_away_from_types hP) fun K _ _ _ _ hK => large₂.imp hK fun B f T _ H => ?_
  intro hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA Rw hPar σ w' hsplit hoff
  have H' := H hKP w hpin Z Wt hX z p0 Y hH hEx hGeo hGrp hGA σ
  obtain ⟨s, rfl⟩ := GlobalTheory.OffBad.splitPlace_of_isSplitPl _ w' hsplit
  obtain ⟨τ, hloc, hsph⟩ := H' s hoff
  obtain ⟨Bf, k1, k2, k3, k4⟩ := exists_form_rowRepR hP.hc hP.decay _ _ _ _ _ _ _ z.R z.F z.cG p0 Y z.pins σ
  have hunit := isUnitarisable_of_isLocS (repOf Y σ) Bf k1 k2 k3 k4 s τ hloc
  have he := hPar.row.1 σ s τ hloc
  obtain ⟨hu, hb⟩ := locRec_unr_frobEig_le hL ((w.st Z).toD7.nd.plOm.2 s.w) τ hsph hunit
  rw [← he] at hu hb
  have hu' := (hPar.T.unr _ _).2 hu
  refine ⟨hu', fun α hα => ?_⟩
  rw [hPar.T.frobEig _ _ hu'] at hα
  have h1 := hb α hα
  have hq : (1 : ℝ) < ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) := by exact_mod_cast GlobalTheory.WeilDeligne.one_lt_normV s.w
  have hrt : (((w.st Z).toD7.R.r : ℝ) - 1) / 2 < (((w.st Z).toD7.R.t : ℝ) - 1) / 2 := by
    have := (w.st Z).toD7.R.rank_add_five_le
    have h2 : (w.st Z).toD7.R.r < (w.st Z).toD7.R.t := by unfold Ranks.r; omega
    have h3 : ((w.st Z).toD7.R.r : ℝ) < ((w.st Z).toD7.R.t : ℝ) := by exact_mod_cast h2
    linarith
  calc ‖α‖ ≤ ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.r : ℝ) - 1) / 2) := h1
    _ < ((Formalism.ConjugateSelfDual.normV s.w : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.t : ℝ) - 1) / 2) := Real.rpow_lt_rpow_of_exponent_lt hq hrt
    _ = ((Ideal.absNorm s.w.asIdeal : ℕ) : ℝ) ^ ((((w.st Z).toD7.R.t : ℝ) - 1) / 2) := rfl

end GlobalTheory.RowSphSmall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SymplecticPairingHalfLatticesEqProdPrimitive
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatPairing

set_option synthInstance.maxHeartbeats 400000 in

theorem trace_mul_int {D : D7} {a b : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D)) (B : Matrix (Fin b) (Fin a) (EAf D))
    (hA : IsIntM A) (hB : IsIntM B) :
    Matrix.trace (A * B) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  exact Subring.sum_mem _ fun i _ => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hB j i)

set_option synthInstance.maxHeartbeats 400000 in

theorem resS_trace_mul {D : D7} (PP : Pl D.host.E) {a b : ℕ} (A : Matrix (Fin a) (Fin b) (EAf D))
    (B : Matrix (Fin b) (Fin a) (EAf D)) (hA : IsIntM A) (hB : IsIntM B)
    (h : Matrix.trace (A * B) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    resS D.host.F PP ⟨Matrix.trace (A * B), h⟩ = Matrix.trace (redM PP A * redM PP B) := by
  have h1 : (⟨Matrix.trace (A * B), h⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ∑ i, ∑ j, (⟨A i j, hA i j⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨B j i, hB j i⟩ := by
    apply Subtype.ext
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, AddSubmonoidClass.coe_finsetSum,
      MulMemClass.coe_mul]
  rw [h1]
  simp only [map_sum, map_mul, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [redM, dif_pos (hA i j), dif_pos (hB j i)]

theorem inv_isPrimitive {R : Type} [CommRing R] (χ : AddChar R ℂ) (h : χ.IsPrimitive) : (χ⁻¹).IsPrimitive := by
  intro a ha h1
  apply h (neg_ne_zero.mpr ha)
  ext x
  have := DFunLike.congr_fun h1 x
  simpa [AddChar.mulShift_apply, AddChar.inv_apply] using this

theorem exists_primitive {E : Type} [Field E] [NumberField E] (PP : Pl E) :
    ∃ χ : AddChar (kP PP) ℂ, χ.IsPrimitive := by
  haveI : PP.asIdeal.IsMaximal := PP.isMaximal
  haveI : Finite (𝓞 E ⧸ PP.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ PP.ne_bot
  letI : Field (𝓞 E ⧸ PP.asIdeal) := Ideal.Quotient.field _
  letI : Fintype (𝓞 E ⧸ PP.asIdeal) := Fintype.ofFinite _
  exact ⟨_, AddChar.FiniteField.primitiveChar_to_Complex_isPrimitive (𝓞 E ⧸ PP.asIdeal)⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

theorem pairing_eq_prod : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)), IsStdChar D ψ (-1) → IsSelfDualC S ΛS → IsSelfDualC T ΛT → Formalism.L2.DIV.IsFrame βS ΛS → Formalism.L2.DIV.IsFrame βT ΛT → ∀ (Q : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e Q → (∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → ∀ ϖ : 𝓞 D.host.E, ϖ ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∃ ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, (∀ PP ∈ Q, (ψP PP).IsPrimitive) ∧ ∀ x : WO S T, IsHalf (cA D e) x → IsIntM (frMapAdj S T βS βT x) → ∀ u : WO S T, IsHalf e u → IsIntM (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) → ψ (symplO S T x u) = ∏ PP ∈ Q.attach, ψP PP.1 (Matrix.trace (redM PP.1 (frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) * redM PP.1 (frMapAdj S T βS βT x))) := by
  intro D ψ S T ΛS ΛT βS βT hψ hS hT hβS hβT Q e he hQ ϖ hϖ hϖQ
  by_cases h0 : S.rank = 0 ∨ T.rank = 0
  · refine ⟨fun PP => (exists_primitive PP).choose, fun PP _ => (exists_primitive PP).choose_spec, ?_⟩
    intro x _ _ u _ _
    have hz : hO S T x u = 0 := by
      unfold hO
      rcases h0 with h0 | h0
      · haveI : IsEmpty (Fin S.rank) := by rw [h0]; infer_instance
        exact Finset.sum_of_isEmpty _
      · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
        exact Finset.sum_eq_zero fun _ _ => Finset.sum_eq_zero fun _ _ => Finset.sum_of_isEmpty _
    rw [symplO, hz, mul_zero, map_zero, AddChar.map_zero_eq_one]
    symm
    refine Finset.prod_eq_one fun PP _ => ?_
    have : ∀ (A : Matrix (Fin T.rank) (Fin S.rank) (kP PP.1)) (B : Matrix (Fin S.rank) (Fin T.rank) (kP PP.1)),
        Matrix.trace (A * B) = 0 := by
      intro A B
      simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
      rcases h0 with h0 | h0
      · haveI : IsEmpty (Fin S.rank) := by rw [h0]; infer_instance
        exact Finset.sum_eq_zero fun _ _ => Finset.sum_of_isEmpty _
      · haveI : IsEmpty (Fin T.rank) := by rw [h0]; infer_instance
        exact Finset.sum_of_isEmpty _
    rw [this, AddChar.map_zero_eq_one]
  · rw [not_or] at h0
    obtain ⟨χ, hχ, hform⟩ := GlobalTheory.T.adelicCharacter_factor_primitive_on_idempotentSum D ψ Q e he ϖ hϖ hϖQ
      (GlobalTheory.T.integral_iff_selfDual_traceCharacter_splitPlaces D ψ S T ΛS ΛT βS βT hψ hS hT hβS hβT (Nat.pos_of_ne_zero h0.1) (Nat.pos_of_ne_zero h0.2) Q e he hQ)
    refine ⟨fun PP => (χ PP)⁻¹, fun PP hPP => inv_isPrimitive _ (hχ PP hPP), ?_⟩
    intro x _ hx u hu hux
    have heu : e • u = u := by
      funext i j
      exact hu i j
    have hsm : (u.map fun w => incA D (ϖ : D.host.E) * w : WO S T) = incA D (ϖ : D.host.E) • u := rfl
    have hZ : e * (-hO S T u x) = -hO S T u x := by
      rw [mul_neg, ← GlobalTheory.PlaceModel.hO_smul_left, heu]
    have htr : toEAf D (incA D (ϖ : D.host.E) * (-hO S T u x)) =
        -Matrix.trace (frMapAdj S T βS βT x * frMapO S T βS βT (u.map fun w => incA D (ϖ : D.host.E) * w)) := by
      rw [mul_neg, map_neg, ← GlobalTheory.PlaceModel.hO_smul_left, ← hsm, GlobalTheory.TraceFrames.toEAf_hO_eq_trace_frames S T βS βT]
    have hint := trace_mul_int _ _ hx hux
    have hint' : toEAf D (incA D (ϖ : D.host.E) * (-hO S T u x)) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      rw [htr]; exact Subring.neg_mem _ hint
    have hs : symplO S T x u =
        Algebra.trace (AF D.host.F) (AE D) (incA D D.host.xi0 * (-hO S T u x)) := by
      rw [GlobalTheory.PlaceModel.symplO_skew S T u x, symplO, mul_neg, map_neg]
    rw [hs, hform _ hZ hint']
    refine Finset.prod_congr rfl fun PP _ => ?_
    have h2 : (⟨_, hint'⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = -⟨_, hint⟩ := Subtype.ext htr
    rw [h2, map_neg, resS_trace_mul PP.1 _ _ hx hux, AddChar.inv_apply, Matrix.trace_mul_comm]

end GlobalTheory.FlatPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationAtRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.GenReal

theorem genInf : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ i t, GenInf R i t := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG hP i t y hy f hf l g
  obtain ⟨μ, 𝓕, hμ⟩ := GlobalTheory.Size.exists_isCovolOne (D := D) (V := Vc D i) (W := Wc D i)
  have h0 : ∀ P, downInt R i t y (R.ptP i t P) l g = 0 := fun P =>
    GlobalTheory.T.realFockThetaLift_vanishing_of_generating_vectors D G Pl0 T A Ks R F hG hP i t y (GlobalTheory.T.theta_lift_vanishes_single_coefficient_of_kernel_kills D G Pl0 T A Ks R F hG hP i t y hy) P l g
  by_contra hne
  have hpos : 0 < ‖downInt R i t y f l g‖ := norm_pos_iff.2 hne
  obtain ⟨d, δ, hδ, hc⟩ := GlobalTheory.T.downward_theta_integral_sobolev_continuous D G Pl0 T A Ks R F hG hP i t y μ 𝓕 hμ f hf.1 l g _ hpos
  obtain ⟨P, hPd⟩ := GlobalTheory.T.thetaFunction_fixedFinitePart_sobolevLimit_fockVectors D G Pl0 T A Ks R F hG hP i t μ 𝓕 hμ f hf d δ hδ
  have := hc P hPd
  rw [h0 P, sub_zero] at this
  exact lt_irrefl _ this

end GlobalTheory.GenReal
end

