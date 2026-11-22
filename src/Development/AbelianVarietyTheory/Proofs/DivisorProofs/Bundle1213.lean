import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1170
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubschemeSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ExistsFormalBiextMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTopologicalRingAE
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenMapTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1122
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0063
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0048
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1174
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.QuadraticClassFieldTheory
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0098
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1171
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsFactorialMulEulerCharTwistPowSubLeStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter Asymptotics
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abs_factorial_mul_eulerChar_twist_pow_sub_le : ∀ (k : Type) [Field k] [Infinite k] (X : Scheme.{0}) [Algebra k Γ(X, ⊤)], IsProjOver (strHom k X) → ∀ (d : ℕ) (F : X.Modules) [IsFiniteQC F], suppDim F ≤ (d : ℕ) → ∀ L : LB X, L.IsLB → ∃ C : ℕ, ∀ m : ℕ, |(d.factorial : ℤ) * chi k (twist F (lbPow L m)) - interNum k F (fun _ : Fin d => L) * (m : ℤ) ^ d| ≤ C * ((d : ℤ) * ((m : ℤ) + 1) ^ (d - 1)) := by
  first | exact @GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le | exact GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le | (intros; apply GlobalTheory.abs_factorial_mul_chi_twist_lbPow_sub_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsHalfMulAndAbsHalfNegOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.AbsHalf

theorem ordL_mul {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    ordL (x * y) = ordL x + ordL y := by
  have hx' : Valued.v x ≠ 0 := by simpa using hx
  have hy' : Valued.v y ≠ 0 := by simpa using hy
  have hxy : Valued.v (x * y) ≠ 0 := by simpa using mul_ne_zero hx hy
  unfold ordL
  rw [dif_neg hxy, dif_neg hx', dif_neg hy']
  have : WithZero.unzero hxy = WithZero.unzero hx' * WithZero.unzero hy' := by
    apply WithZero.coe_injective
    simp [map_mul]
  rw [this, toAdd_mul]
  ring

theorem ordL_neg_one {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] : ordL (-1 : L) = 0 := by
  have h1 : Valued.v (-1 : L) ≠ 0 := by simp
  unfold ordL
  rw [dif_neg h1]
  have : WithZero.unzero h1 = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero]
    simp only [Valuation.map_neg, Valuation.map_one]
    rfl
  rw [this]
  simp

end GlobalTheory.AbsHalf

namespace GlobalTheory.AbsHalf

theorem absHalf_mul_neg_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E),
    (∀ x y : w.adicCompletion E, x ≠ 0 → y ≠ 0 → absHalf w (x * y) = absHalf w x * absHalf w y) ∧
      absHalf w (-1) = 1 := by
  intro E _ _ _ w
  have hq : (0 : ℝ) < (qV E w : ℝ) := by
    have : qV E w ≠ 0 := by
      unfold qV
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    exact_mod_cast Nat.pos_of_ne_zero this
  refine ⟨fun x y hx hy => ?_, ?_⟩
  · unfold absHalf
    rw [ordL_mul x y hx hy, neg_add, zpow_add₀ hq.ne', Real.sqrt_mul (zpow_nonneg hq.le _)]
    push_cast
    ring
  · unfold absHalf
    rw [ordL_neg_one]
    simp

end GlobalTheory.AbsHalf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActionLinearLogCoordinatesIntegral
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IsoTriv

open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open GlobalTheory.LawLog ReciprocityTheory.ChartRestriction.G.TB

theorem actSt : ActSt := by
  intro C _ _ v d R _ _ O _ _ B hB σ _ a

  have hφ0 : ∀ i, constantCoeff (B.actK C a i) = 0 := by
    intro i
    show constantCoeff (MvPowerSeries.map (algebraMap R C) (B.A.act a i)) = 0
    rw [MvPowerSeries.constantCoeff_map, GlobalTheory.FBMap.nc_act B.A a i, map_zero]

  have hhom : comp1 (B.actK C a) (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G).F =
      addOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G).F (comp1 (B.actK C a) (pt C (n := 2) d 0))
        (comp1 (B.actK C a) (pt C (n := 2) d 1)) := by
    have h := (GlobalTheory.FBMap.mapAct (algebraMap R C) B.A).hom a
    rw [GlobalTheory.LawLog.add_pt] at h
    exact h

  have hcomp := GlobalTheory.FactorDepth.logOf_comp_hom _ _ (B.actK C a) hφ0 hhom
  have h0 : ∀ e, constantCoeff (subst (oneVar C d) (B.actK C a e)) = 0 := fun e =>
    constantCoeff_subst_eq_zero hs_oneVar cc_oneVar (hφ0 e)
  have hl : ∀ e, subst (fun f => subst (oneVar C d) (B.actK C a f)) ((fglOf hB).lg e) =
      ∑ f, dAct C B a e f • (fglOf hB).lg f := by
    intro e
    calc subst (fun f => subst (oneVar C d) (B.actK C a f)) ((fglOf hB).lg e)
        = subst (oneVar C d)
            (comp1 (GlobalTheory.FormalLog.logOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G)) (B.actK C a) e) :=
          GlobalTheory.LawLog.subst_oneVar (oneVar C d) cc_oneVar (B.actK C a) hφ0
            (GlobalTheory.FormalLog.logOf (GlobalTheory.FBMap.mapLaw (algebraMap R C) B.G) e)
      _ = ∑ f, dAct C B a e f • (fglOf hB).lg f := by
          rw [hcomp]
          dsimp only
          rw [← coe_substAlgHom hs_oneVar, map_sum]
          simp only [map_smul, coe_substAlgHom]
          exact Finset.sum_congr rfl fun f _ => rfl

  have hexp : ∀ w : Fin d → MvPowerSeries σ C, (∀ i, constantCoeff (w i) = 0) →
      expPt (fglOf hB) (mv (dAct C B a) w) =
        fun i => subst (fun q : Fin 1 × Fin d => expPt (fglOf hB) w q.2) (B.actK C a i) := by
    intro w hw
    have hsE : HasSubst (fun f => subst w (GlobalTheory.FGDepth.expOf (fglOf hB) f)) :=
      MvPowerSeries.hasSubst_of_constantCoeff_zero fun f => cc_expPt (fglOf hB) hw f
    funext i
    have key := GlobalTheory.FactorDepth.exp_eq_of_log_hom (fglOf hB) (fglOf hB) _ h0 (dAct C B a) hl
      (mv (dAct C B a) w) w hw (fun e => rfl) i
    show subst (mv (dAct C B a) w) (GlobalTheory.FGDepth.expOf (fglOf hB) i) = _
    rw [key, subst_comp_subst_apply hs_oneVar hsE]
    congr 1
    funext q
    exact subst_X hsE q.2
  refine ⟨hexp, fun w hw => ⟨cc_mv (dAct C B a) hw.1, fun i => ?_⟩⟩

  rw [hexp w hw.1]
  exact ReciprocityTheory.ChartRestriction.G.Sh.PTb.mvIsInt_subst v (hB.2.1 a i) (fun q => hw.2 q.2)
    (fun q => cc_expPt (fglOf hB) hw.1 q.2)

end GlobalTheory.IsoTriv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedBasesBlockTriangularOfReducedEtaleFiltratStatement
section
open NumberField GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adaptedBases_blockTriangular_of_reducedEtaleFiltration : ∀ (ι : Type) (σ : Equiv.Perm ι) (l n t : ℕ) (F : Type) [Field F] (un : PowerSeries F) (P D : ι → Matrix (Fin n) (Fin n) (PowerSeries F)) (Pψ Dψ : Fin t → ι → PowerSeries F), 0 < l → Nonempty ι → GlobalTheory.WachBlock.RedFilt σ l un P D Pψ Dψ → ∃ (g : ι → (Matrix (Fin n) (Fin n) (PowerSeries F))ˣ) (b : Fin n → ℕ) (pos : Fin t → Fin n) (w : ι → Fin t → (PowerSeries F)ˣ) (kap : ι → Fin t → ℤ), (Function.Injective pos ∧ ∀ s j, b j = b (pos s) → j = pos s) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i)).BlockTriangular b) ∧ (∀ i, (Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i)).BlockTriangular b) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.frob0 l (w (σ i) s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ ((l : ℤ) * kap (σ i) s) * ((Pψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgPhi l (g i) (g (σ i)) (P i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) ∧ (∀ i s, ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gam0 0 un (w i s : PowerSeries F) : PowerSeries F) : LaurentSeries F) * ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.gamSer 0 un : PowerSeries F) : LaurentSeries F) ^ kap i s * ((1 + PowerSeries.X * Dψ s i : PowerSeries F) : LaurentSeries F) = ((Formalism.CohomologicalDescent.FrobeniusPeriodChange.chgGam un (g i) (D i) (pos s) (pos s) : PowerSeries F) : LaurentSeries F) * ((w i s : PowerSeries F) : LaurentSeries F) * ((PowerSeries.X : PowerSeries F) : LaurentSeries F) ^ kap i s) := by
  first | exact @GlobalTheory.WachBlock.adapted_bases_of_redFilt | exact GlobalTheory.WachBlock.adapted_bases_of_redFilt | (intros; apply GlobalTheory.WachBlock.adapted_bases_of_redFilt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AddGroupFGLineBundleSectionsArithmeticVarietyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addGroupFG_lineBundleSections_arithmeticVariety : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ B : LB X, B.IsLB → AddGroup.FG B.Sec := by
  first | exact @GlobalTheory.addGroupFG_sec_of_isArithVar | exact GlobalTheory.addGroupFG_sec_of_isArithVar | (intros; apply GlobalTheory.addGroupFG_sec_of_isArithVar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHomActionRealCoordinatesEqStatement
section
open scoped TensorProduct Matrix BoundedContinuousFunction ContDiff
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.DatumF MeasureTheory Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.RealWeil GlobalTheory.RealWeilF
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicHomAction_realCoordinates_eq : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ → ∀ θ : InfinitePlace F → (Ainf F ⊗[F] E →+* ℂ),
      IsInfFamF (fun w : InfinitePlace F => (B.emb w).1) θ → ∀ ι : (InfinitePlace F → ℂ) →+ AEF F E, IsChartF θ ι →
      ∀ (g : GAF σ JS) (h : GAF σ JT) (v : IxF F nS nT → ℂ),
        actOF σ JS JT g h (iotaVF ι v) = iotaVF ι (mMF σ JS JT θ (g, h) *ᵥ v) := by
  first | exact @GlobalTheory.RealWeilF.actOF_iotaVF | exact GlobalTheory.RealWeilF.actOF_iotaVF | (intros; apply GlobalTheory.RealWeilF.actOF_iotaVF <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicVacuumReadsMultipleClassicalVacuum
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.VacLine

theorem hostHalfRoot_add_conj_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    (H.w0 : E) + cc (H.w0 : E) = 1 := by
  have := congrArg (algebraMap (𝓞 E) E) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)
  rw [map_add, map_one] at this
  exact (congrArg _ (H.bar_eq _).symm).trans this

theorem isRelTraceOneIdempotentModTwo_hostElement {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Geo.Tor.Host E) :
    GlobalTheory.Ker.IdemTwo (H.w0 : E) := by
  obtain ⟨k, hk⟩ : ∃ k, H.d = 16 * k + 7 := ⟨H.d / 16, by have := H.d_mod; omega⟩
  have h1 := hostHalfRoot_add_conj_eq_one H
  have h2 : 2 * (H.w0 : E) = 1 + (H.rt : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.two_weight_eq_one_add_root
    rwa [map_mul, map_add, map_one, map_ofNat] at this
  have h3 : (H.rt : E) ^ 2 = -(16 * k + 7) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    rw [map_pow, map_neg, map_natCast, hk] at this
    exact this.trans (by push_cast; rfl)
  refine ⟨((2 * k + 1 : ℕ) : E), isIntegral_natCast _, ?_⟩
  rw [eq_sub_of_add_eq' h1]
  push_cast
  linear_combination (-(1 / 4 : E)) * h3 - (1 / 4 : E) * (2 * (H.w0 : E) - 1 + (H.rt : E)) * h2

theorem isAA_aMul {D : D7} {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) :
    GlobalTheory.Ker.IsAA (LatOf.aMul Λ) Λ := by
  intro v
  constructor
  · intro h
    exact LatOf.aMul_induction (p := fun v => v ∈ AddSubgroup.closure
      {u | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ Λ, u = a • t})
      (fun a ha t ht => AddSubgroup.subset_closure ⟨a, ha, t, ht, rfl⟩) (zero_mem _) (fun _ _ => add_mem) h
  · intro h
    exact (AddSubgroup.closure_le (LatOf.aMul Λ).toAddSubgroup).2 Submodule.subset_span h

theorem vac_reads : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (V W : HSp D) (r g : ℕ) (hr : W.rank = r) (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsStdChar D ψ (-1) → IsInfFam θ → V.gram = 1 → Even V.rank → IsMod W hr X → IsSympl X bas → ∀ (H : Geo.Tor.Host D.host.E), (H.rt : D.host.E) = D.host.sqrtMinusD → ∀ (ΛV : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (ΛW : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E)) (Λ' : Lt D.host.E V.rank) (L : Lt D.host.E r), V.SigOK → W.SigOK → IsSelfDualC V ΛV → IsSelfDualC W ΛW → (∀ v : Fin V.rank → D.host.E, v ∈ Λ' ↔ (fun j => star (v j)) ∈ ΛV) → (∀ L₀ : Submodule (𝓞 D.host.E) (Fin W.rank → D.host.E), L₀ = Submodule.span (𝓞 D.host.E) {w | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ v ∈ ΛW, w = a • v} → L = latR hr L₀) → ∀ (x : Frame X.Ψ r) (s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ), IsONFr X x → IsInvOf W hr X x s → ∀ f, IsVacO ψ θ V W (fun _ => 1) s (ΛV : Set (Fin V.rank → D.host.E)) (ΛW : Set (Fin W.rank → D.host.E)) f → ∀ v : TF V.rank g, IsVac X bas (H.w0 : D.host.E) (tens Λ' L) v → ∃ κ : ℂ, κ ≠ 0 ∧ Reads θ V W hr X bas idx f (κ • v) x := by
  intro D ψ θ V W r g hr X bas idx hψ hθ hV he hX hs H _ ΛV ΛW Λ' L _ _ hΛV hΛW hΛ' hL x s hx hsx f hf v hv
  obtain ⟨-, hsd, hU, hfg⟩ := LatOf.isLatOf_tens D ψ θ V W r g hr X bas idx hψ hθ hV he hX hs ΛV ΛW Λ' L hΛV hΛW hΛ' hL
  subst hr
  have hL' : L = LatOf.aMul ΛW := by
    rw [hL (LatOf.aMul ΛW) rfl]
    exact Submodule.map_id _
  subst hL'
  obtain ⟨X', m, hq', hq, bas', idx', hs', -, -, hEF, hh, -, -, hfr⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hψ hθ he hV hX hs
  obtain ⟨⟨B, hB⟩, hall⟩ := hfr x hx
  obtain ⟨hIB, -, hsB, -, -, -, -, -, hrd⟩ := hall B hB
  set C : GlobalTheory.Ker.Ctx V W := ⟨ψ, hψ, θ, hθ, X', m, g, X.p0, hq', bas', idx', hs', he⟩ with hC
  obtain rfl := hsB s hsx
  have hsd' : SelfD C.X (LatOf.aMul ΛW) := by
    refine ⟨hsd.1, fun u => (hsd.2 u).trans ?_⟩
    change _ ↔ ∀ y ∈ LatOf.aMul ΛW, ∃ k : ℤ, EF X' u y = k
    simp only [hEF]
  have hv' : IsVac C.X C.bas (H.w0 : D.host.E) (tens Λ' (LatOf.aMul ΛW)) v := by
    refine ⟨hv.1, hv.2.1, fun y hy => ?_⟩
    change epsW X' _ y • heisG X' bas' y v = v
    have e : epsW X' (H.w0 : D.host.E) y = epsW X (H.w0 : D.host.E) y := by simp only [epsW, hEF]
    rw [e, hh]
    exact hv.2.2 y hy
  have hlat := hf.2.lat
  rw [GlobalTheory.Ker.LatTens.latO_eq_hatA D V W C ΛV Λ' ΛW _ hΛ' (isAA_aMul ΛW)] at hlat
  obtain ⟨t, ht⟩ := (GlobalTheory.Ker.latVac_th_line D V W C _ H.w0.isIntegral_coe (hostHalfRoot_add_conj_eq_one H) (isRelTraceOneIdempotentModTwo_hostElement H) 1 Λ'
    (VacProj.mem_vset ⟨Λ'⟩ hU hfg) _ hsd').2 B hIB v hv' f hf.2.theta hf.2.fock hlat
  refine ⟨t, ?_, ((hrd f (t • v) (TensVac.sb_smul _ hv.1)).2 ?_).2⟩
  · rintro rfl
    rw [zero_smul] at ht
    subst ht
    obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
    have := hn p hp
    simp [nrm2] at this
  · rw [(GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D V W C _ ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D V W C).2 B hIB).2.1 v hv.1).2.1]
    exact ht

end GlobalTheory.AdTh.VacLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicIndependentEtaleTowerCoordinatesStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraicIndependent_etaleTower_coordinates : ∀ {K L : Type} [Field K] [Field L] (cK : ℂ →+* K) (cL : ℂ →+* L) (n r : ℕ) (R : Subring K) (T : Subring L)
    (ι : R →+* T) (ψ : T →+* R) (τ : Fin r → T) (x : Fin n → R),
  IsEtTower cK R cL T ι ψ τ → TrBasis cK (fun i => (x i : K)) →
  Function.Injective (MvPolynomial.eval₂Hom ι τ) →
  (letI := cL.toAlgebra; AlgebraicIndependent ℂ (Fin.append (fun i => (τ i : L)) (fun i => (ι (x i) : L)))) := by
  first | exact @GlobalTheory.FieldPair.etTower_coords_algebraicIndependent | exact GlobalTheory.FieldPair.etTower_coords_algebraicIndependent | (intros; apply GlobalTheory.FieldPair.etTower_coords_algebraicIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostAllPlacesTwistedUnitIntegral
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.almost_all_places_twisted_unit_integral : ∀ (C : Type) [Ring C] [Algebra ℚ C] [FiniteDimensional ℚ C] (L : Type) [Field L] [NumberField L]
    (ι : L →ₐ[ℚ] C), Function.Injective ι → ∀ (κ : Type) (b : Module.Basis κ ℚ C) (κ' : Type)
    (bL : Module.Basis κ' ℚ L), ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S,
      ∀ (X : (v.adicCompletion ℚ ⊗[ℚ] C)ˣ) (E : v.adicCompletion ℚ ⊗[ℚ] L),
        IsIntB v b (↑X * Algebra.TensorProduct.map (AlgHom.id ℚ (v.adicCompletion ℚ)) ι E * ↑X⁻¹) →
        IsIntB v bL E := by
  first | (exact @GlobalTheory.LocIntSpan.isIntB_of_isIntB_conj) | (exact GlobalTheory.LocIntSpan.isIntB_of_isIntB_conj) | (intros; apply GlobalTheory.LocIntSpan.isIntB_of_isIntB_conj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlmostNormClassCount
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.QuadSymbol.SignCount

theorem card_prod_eq_mul_two {ι : Type} [Fintype ι] [Nonempty ι] (c : ℤˣ) :
    Nat.card {s : ι → ℤˣ // c * ∏ i, s i = 1} * 2 = 2 ^ Fintype.card ι := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  let m : ι → ℤˣ := Pi.mulSingle i₀ (-1)
  have hm : ∏ i, m i = -1 := by simp [m, Finset.prod_pi_mulSingle']
  have hmm : m * m = 1 := by
    ext i
    by_cases h : i = i₀
    · subst h; simp [m]
    · simp [m, Pi.mulSingle_eq_of_ne h]
  have key : ∀ s : ι → ℤˣ, (c * ∏ i, (s * m) i = 1) ↔ ¬ (c * ∏ i, s i = 1) := by
    intro s
    simp only [Pi.mul_apply, Finset.prod_mul_distrib, hm]
    rcases Int.units_eq_one_or (c * ∏ i, s i) with h | h
    · rw [← mul_assoc, h]; decide
    · rw [← mul_assoc, h]; decide
  let e : {s : ι → ℤˣ // c * ∏ i, s i = 1} ≃ {s : ι → ℤˣ // ¬ (c * ∏ i, s i = 1)} :=
    { toFun := fun s => ⟨s.1 * m, fun h => (key s.1).1 h s.2⟩
      invFun := fun s => ⟨s.1 * m, by
        have := (key s.1).2 s.2
        exact this⟩
      left_inv := fun s => Subtype.ext (by simp [mul_assoc, hmm])
      right_inv := fun s => Subtype.ext (by simp [mul_assoc, hmm]) }
  have htot := Fintype.card_subtype_compl (fun s : ι → ℤˣ => c * ∏ i, s i = 1)
  rw [Nat.card_eq_fintype_card, mul_two]
  nth_rewrite 2 [Fintype.card_congr e]
  have hle := Fintype.card_subtype_le (fun s : ι → ℤˣ => c * ∏ i, s i = 1)
  rw [htot, Fintype.card_pi, Finset.prod_const, Fintype.card_units_int, Finset.card_univ] at *
  omega

end GlobalTheory.QuadSymbol.SignCount

namespace GlobalTheory.QuadSymbol.SignCount

theorem neg_one_not_mem_normGroup {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [Algebra.IsQuadraticExtension K L] (hL : NumberField.IsTotallyComplex L)
    {w : InfinitePlace K} (hw : w.IsReal) : (-1 : (w.Completion)ˣ) ∉ normGroup K L w.Completion := by
  obtain ⟨δ, b, -, h0, h1⟩ := AlmostNorm.exists_basis_sq K L
  have hneg : InfinitePlace.embedding_of_isReal hw δ < 0 := by
    by_contra hc
    obtain ⟨r, hr⟩ := Real.isSquare_iff.2 (not_lt.1 hc)
    let τ : L →+* ℂ := ComplexEmbedding.lift L w.embedding
    have hτ : ∀ x : K, τ (algebraMap K L x) = InfinitePlace.embedding_of_isReal hw x := fun x => by
      rw [InfinitePlace.embedding_of_isReal_apply]
      exact ComplexEmbedding.lift_algebraMap_apply L w.embedding x
    have h2 : τ (b 1) * τ (b 1) = (r : ℂ) * r := by rw [← map_mul, h1, hτ, hr]; push_cast; rfl
    have h3 : starRingEnd ℂ (τ (b 1)) = τ (b 1) := by
      rcases mul_self_eq_mul_self_iff.1 h2 with h | h <;> rw [h] <;> simp
    refine InfinitePlace.not_isReal_iff_isComplex.2 (hL.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_)))
    change starRingEnd ℂ (τ x) = τ x
    rw [← b.sum_repr x, Fin.sum_univ_two, h0, Algebra.smul_def, Algebra.smul_def]
    simp only [map_add, map_mul, map_one, hτ, h3, Complex.conj_ofReal]
  rw [mem_normGroup_iff_form b h0 h1]
  rintro ⟨x, y, hxy⟩
  let f := InfinitePlace.Completion.ringEquivRealOfIsReal hw
  have hf : f (algebraMap K w.Completion δ) = InfinitePlace.embedding_of_isReal hw δ :=
    InfinitePlace.Completion.extensionEmbeddingOfIsReal_coe hw ((WithAbs.equiv _).symm δ)
  have := congrArg f hxy
  simp only [Units.val_neg, Units.val_one, map_neg, map_one, map_sub, map_mul, map_pow, hf] at this
  nlinarith [sq_nonneg (f x), sq_nonneg (f y)]

end GlobalTheory.QuadSymbol.SignCount

namespace GlobalTheory.QuadSymbol.SignCount

def infSigns (K L : Type) [Field K] [NumberField K] [Field L] [Algebra K L] (t : Kˣ) :
    InfinitePlace K → ℤˣ :=
  fun w => eta K L w.Completion (infDiag K t w)

theorem infSigns_eq_of_mem {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {t t' : Kˣ} (h : t⁻¹ * t' ∈ globalNorms K L) :
    infSigns K L t' = infSigns K L t := by
  funext w
  refine eta_eq_of_div_mem ?_
  have := toUnits_mem_normGroup (K := K) (L := L) w.Completion h
  rw [← div_eq_inv_mul, _root_.map_div] at this
  exact this

theorem infSigns_out {K L : Type} [Field K] [NumberField K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (t : Kˣ) :
    infSigns K L (Quotient.out (QuotientGroup.mk t : Kˣ ⧸ globalNorms K L)) = infSigns K L t :=
  infSigns_eq_of_mem (QuotientGroup.eq.1 (QuotientGroup.out_eq' _).symm)

theorem card_classes_mul_two : ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [Algebra.IsQuadraticExtension K L], NumberField.IsTotallyReal K → NumberField.IsTotallyComplex L → ∀ x : GlobalTheory.QuadSymbol.FinFam K, GlobalTheory.QuadSymbol.AlmostNorm K L x → Nat.card {q : Kˣ ⧸ GlobalTheory.QuadSymbol.globalNorms K L // ∃ t : Kˣ, q = QuotientGroup.mk t ∧ ∀ u, x u / GlobalTheory.QuadSymbol.finDiag K t u ∈ GlobalTheory.QuadSymbol.normGroup K L (u.adicCompletion K)} * 2 = 2 ^ Fintype.card (InfinitePlace K) := by
  intro K L _ _ _ _ _ _ hK hL x hx
  have hfd : FiniteDimensional K L := Module.finite_of_finrank_eq_succ (Algebra.IsQuadraticExtension.finrank_eq_two K L)
  obtain ⟨-, hnorm, hseq, -⟩ := exactSequence K L
  obtain ⟨-, hc2⟩ := localCharacters K L
  set c : ℤˣ := ∏ᶠ v : HeightOneSpectrum (𝓞 K), eta K L (v.adicCompletion K) (x v) with hc
  rw [← card_prod_eq_mul_two c]
  congr 1
  have hprod : ∀ t : Kˣ, (∀ u, x u / finDiag K t u ∈ normGroup K L (u.adicCompletion K)) →
      c * ∏ w, infSigns K L t w = 1 := by
    intro t ht
    have := (hseq x (infDiag K t) hx).1 ⟨t, fun u => ht u, fun w => by simp [one_mem]⟩
    exact this
  refine Nat.card_congr (Equiv.ofBijective (fun q => ⟨infSigns K L (Quotient.out q.1), ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨t, hq, ht⟩ := q.2
    rw [hq, infSigns_out]
    exact hprod t ht
  · rintro ⟨q₁, t₁, rfl, h₁⟩ ⟨q₂, t₂, rfl, h₂⟩ he
    have he' : infSigns K L t₁ = infSigns K L t₂ := by
      have := congrArg Subtype.val he
      simpa only [infSigns_out] using this
    refine Subtype.ext (QuotientGroup.eq.2 ((hnorm (t₁⁻¹ * t₂)).1 ⟨fun u => ?_, fun w => ?_⟩))
    · have hm := div_mem (h₁ u) (h₂ u)
      rwa [div_div_div_cancel_left, finDiag, finDiag, ← _root_.map_div, div_eq_inv_mul] at hm
    · have hm := Converse.div_mem_normGroup (hc2 w) (congrFun he' w)
      rwa [infDiag, infDiag, ← _root_.map_div, div_eq_inv_mul] at hm
  · rintro ⟨s, hs⟩
    let y : InfFam K := fun w => if s w = 1 then 1 else -1
    have hy : ∀ w, eta K L w.Completion (y w) = s w := by
      intro w
      rcases Int.units_eq_one_or (s w) with h | h
      · simp only [y, h, if_true]
        exact eta_eq_one_iff.2 (one_mem _)
      · simp only [y, h, show (-1 : ℤˣ) ≠ 1 by decide, if_false]
        exact eta_eq_neg_one_iff.2 (neg_one_not_mem_normGroup hL (hK.isReal w))
    have hy1 : etaProd K L x y = 1 := by
      unfold etaProd
      rw [Finset.prod_congr rfl fun w _ => hy w]
      exact hs
    obtain ⟨t, ht1, ht2⟩ := (hseq x y hx).2 hy1
    refine ⟨⟨QuotientGroup.mk t, t, rfl, fun u => ht1 u⟩, Subtype.ext ?_⟩
    simp only [infSigns_out]
    funext w
    rw [← hy w]
    exact (eta_eq_of_div_mem (ht2 w)).symm

end GlobalTheory.QuadSymbol.SignCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithInterProjectionFormulaOfHeightProjectionFor
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.Published

theorem arProj_of_heightProjection (H : HeightProjection) : ArProj := by
  intro k _ X Y _ _ p q D hX hY π hπ hg hm
  have key (L : HermLB p) (a : ℝ) (ha : L.IsSelfInter a) :
      (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * a) := by
    obtain ⟨h, hh, rfl⟩ := ha
    have := H k X Y p q D D hX hY π hπ (by
      rw [hg, (genericPoint_spec X).def]
      exact (IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ X).isHomeomorph).trans hX.dim_eq) hm L h hh
    exact (congrArg (fun x => (π.residueDegree (genericPoint Y) : ℝ) * h x) hg) ▸ this
  refine ⟨key, fun ι _ L Φ hΦ => ⟨fun n => ?_, fun P d hd hP => ?_⟩⟩
  · exact (ArInt.isometric_comb_pull L n π hπ).symm.isSelfInter hY (key _ _ (hΦ.1 n))
  · rw [LinearMap.smul_apply, hΦ.2 P d hd hP, smul_zero]

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgEqOfLeRightStabiliserStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT
open scoped Classical TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.avg_eq_of_le_rightStabiliser : ∀ (H : Type) [Group H] (u : H → ℂ) (S : Subgroup H), S ≤ rStab u → S.index ≠ 0 → avg u = (S.index : ℂ)⁻¹ * ∑ᶠ q : H ⧸ S, u q.out := by
  first | exact @GlobalTheory.BCT.avg_eq_of_le_rStab | exact GlobalTheory.BCT.avg_eq_of_le_rStab | (intros; apply GlobalTheory.BCT.avg_eq_of_le_rStab <;> assumption)
end

