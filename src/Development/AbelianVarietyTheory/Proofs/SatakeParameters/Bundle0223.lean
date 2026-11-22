import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0345
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0370
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0001
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0197
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0207
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0127
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0009
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0186
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0208
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0213
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0211
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0212
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0209
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0215
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0178
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHecke
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0195
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Formalism.LocalRingCardinality.Bundle0005
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0200
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0140

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PinOfNTrue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.NPin.pin_of_nTrue : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (cf : CharFrame D) (C : NChoice D) (tp : TupTied D cf C) (nt : NTrue hL D cf C tp), ValLL0 D cf → (∀ σ σ', (nt.rep σ).Iso (nt.rep σ') → σ = σ') → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → ChebSplit D.nd → ∃ P : Pin hL D, P.cf = cf ∧ P.C = C ∧ HEq P.tp tp ∧ HEq P.rep nt.rep ∧ HEq P.M (mtL nt.L nt.M) := by
  intro hL D cf C tp nt hval hinj hstar hexp hsplit hcheb
  obtain ⟨⟨D0, cf0, jE, A, cg, au, rep, row, low, Pq, S, hLm, eig, θ, Bs, M, C0, tp0, ch, mt, big, L, Sp, Au, ss, heq⟩, pack⟩ := nt
  dsimp only at pack heq hinj ⊢
  subst heq
  cases pack
  obtain ⟨Hk, hHk⟩ := GlobalTheory.FitHecke.heckeOpen_withLoc D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hstar hexp hsplit hcheb big L Sp Au
  obtain ⟨ty⟩ := GlobalTheory.HeightCounting.typesOpen_withLoc D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hstar hexp hsplit hcheb big L Sp Au ss
  obtain ⟨tw⟩ := GlobalTheory.T.side_multiplicity_character D0 cf0 jE A low Pq S hLm eig θ Bs M C0 tp0 ch mt hstar hexp hsplit hcheb big L Sp Au
  refine ⟨{ cf := cfL L cf0, C := chL L C0, tp := tpL L tp0, chr := tw.chrN, val := hval, Q_eq := ?Q, T := { A.wdT with }, lab := A.lab, cg := { cg with }, M := mtL L M, H := Hk, au := ?au, rep := rep, rep_inj := hinj, row := ?row, locW_eq := fun i i' σ w => (Au.locW i σ w).trans (Au.locW i' σ w).symm, jE := jE, ty := ty, wd := { A.wd with }, wdOf := Au.wdOf }, rfl, rfl, HEq.rfl, HEq.rfl, HEq.rfl⟩
  case Q =>
    intro i
    have hm : i ∈ L.X.nd.locs (L.X.nd.j i) (L.X.nd.w i) := (L.X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    exact (Sp.Q_eq _ _ i hm).trans (Sp.Qc_eq _ _)
  case au =>
    intro j h1 h2 π s σ h
    rw [hHk]
    exact au j h1 h2 π s σ h
  case row =>
    intro i
    refine ⟨fun σ s τ h => ?_, fun σ v w hvw Dv hα => ?_⟩
    · exact (congrArg (A.wdT.e s.w) (Au.locW i σ s.w)).trans (row.1 σ s τ h)
    · obtain ⟨α, h1, h2⟩ := row.2 σ v w hvw Dv hα
      exact ⟨α, h1, (Au.satW i σ w).trans h2⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterBlockSumEqDirectSumStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potSemistableParameter_blockSum_eq_directSum : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {L : FinExt l} {a b : ℕ} (s : ↥(Dec (F := E) A) →* GL (Fin a) ↥L.1) (s' : ↥(Dec (F := E) A) →* GL (Fin b) ↥L.1), IsPst P (Bw.repE L s) → IsPst P (Bw.repE L s') → IsPst P (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) → wdPst P ι Bw h hj (Bw.repE L (Formalism.MainNotions.SumRepresentations.At.sumRep s s')) = (wdPst P ι Bw h hj (Bw.repE L s)).lpSum (wdPst P ι Bw h hj (Bw.repE L s')) := by
  first | exact @GlobalTheory.Pst.SumOneField.wdPst_sumRep | exact GlobalTheory.Pst.SumOneField.wdPst_sumRep | (intros; apply GlobalTheory.Pst.SumOneField.wdPst_sumRep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PotSemistableParameterCoefficientFieldEnlargeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.WeilDeligne
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potSemistableParameter_coefficientField_enlarge : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ) {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces Bw) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥(Dec (F := E) A) →* GL (Fin m) ↥L₁.1), IsPst P (Bw.repE L₁ r₁) → wdPst P ι Bw h hj (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) = wdPst P ι Bw h hj (Bw.repE L₁ r₁) := by
  first | exact @GlobalTheory.Pst.EnlargeParam.wdPst_enlarge | exact GlobalTheory.Pst.EnlargeParam.wdPst_enlarge | (intros; apply GlobalTheory.Pst.EnlargeParam.wdPst_enlarge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
section
noncomputable section

namespace GlobalTheory.RankOneComp

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField
  IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil ValuativeRel

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Char

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [IsTotallyComplex E]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem locPar_ofChar_unr_iff (hL : GlobalTheory.Published.LocalLanglandsGL) (χ : HChar E) (h : IsPlaceOver A w) :
    (ParLaws.locPar hL (CG.ofChar χ) h).unr ↔ χ.UnrAt w := by
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL h
  rw [ParLaws.locPar_ofChar, H.one, Test.unr_lpOfChar_iff ha (ParLaws.isSmoothChar_loc χ w)]
  refine forall_congr' fun x => imp_congr_left ?_
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  rw [← ord_eq_zero_iff, SphCompletion.ord_completion, neg_eq_zero, IsUnitAt]
  constructor
  · intro hl
    rw [← WithZero.exp_log h0, hl, WithZero.exp_zero]
  · intro hv
    rw [hv, WithZero.log_one]

theorem locPar_ofChar_frob (hL : GlobalTheory.Published.LocalLanglandsGL) (χ : HChar E) (h : IsPlaceOver A w) (hu : χ.UnrAt w) :
    (ParLaws.locPar hL (CG.ofChar χ) h).frobEig = {(((χ.val w)⁻¹ : ℂˣ) : ℂ)} := by
  have e : χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
    refine MonoidHom.ext fun x => ?_
    have h2 := unif_spec w
    have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
    have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
      unfold IsUnitAt IsUnifAt at *
      rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
        map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
      simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
      rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
    have h3 := hu _ h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
    exact h3
  obtain ⟨a, ha, ε, -, H⟩ := ParLaws.isRec_locRec hL h
  have e2 : ParLaws.locPar hL (CG.ofChar χ) h = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
    rw [ParLaws.locPar_ofChar, H.one]
    have : ∀ (ξ : (w.adicCompletion E)ˣ →* ℂˣ) (hξ : WeilDeligne.IsSmooth (ξ.comp a)),
        ξ = SmGL.unrChar (w.adicCompletion E) (χ.val w) →
        WD.lpOfChar h (ξ.comp a) hξ = WD.mk (WDRep.diag h fun _ : Fin 1 => (χ.val w)⁻¹) := by
      rintro ξ hξ rfl
      exact Test.lpOfChar_unrChar ha _ _
    exact this _ _ e
  rw [e2, WD.frobEig_diag]
  simp

end Char

theorem locG_rankOne_eq_rcAt : GlobalTheory.Published.AutomorphicFormsFiniteGL → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D),
    ∀ (π : D.naut.CG 1) (w : PlE D.host) (ξ : (w.adicCompletion D.host.E)ˣ →* ℂˣ) (h : IsComp (P.chr.e1 π).1 w ξ),
    P.T.e w (D.naut.locG π w) = rcAt hL D w 1 (Irr.ofDet 1 ξ h.1) := by
  intro _ hL D P π w ξ h
  haveI := host_isCMField D.host
  set χ' := (CGu.equivChar D.host.E (P.cg.e 1 π)).1 with hχ'
  set χ := (P.chr.e1 π).1 with hχ
  have hloc : ∀ v, P.T.e v (D.naut.locG π v) = ParLaws.locPar hL (CG.ofChar χ') (D.nd.plOm.2 v) := fun v => by
    rw [P.cg.loc, hχ', CGu.ofChar_equivChar]; rfl
  have unr' : ∀ v, D.naut.unr (D.naut.locG π v) ↔ χ'.UnrAt v := fun v => by
    rw [P.T.unr, hloc v]; exact locPar_ofChar_unr_iff hL χ' _
  have hchar : χ' = χ := by
    rw [← mul_inv_eq_one]
    apply GlobalTheory.HeckeSplitRow.eq_one_of_split D.host
    filter_upwards [D.naut.locG_unr_ae π] with v hv _
    have u1 := (P.chr.unr_iff π v).1 hv
    have u2 := (unr' v).1 hv
    refine ⟨fun x hx => ?_, ?_⟩
    · rw [HChar.loc_mul, HChar.loc_inv, u1 x hx, u2 x hx, inv_one, mul_one]
    · have hf := P.chr.frob π v u1
      have hf' : D.naut.frobEig (D.naut.locG π v) = {(((χ'.val v)⁻¹ : ℂˣ) : ℂ)} := by
        rw [P.T.frobEig _ _ hv, hloc v]; exact locPar_ofChar_frob hL χ' _ u2
      rw [hf', Multiset.singleton_inj, Units.val_inj, inv_inj] at hf
      rw [HChar.val_mul, HChar.val_inv, hf, mul_inv_cancel]
  have hcomp : IsComp χ w (χ.loc w) := ⟨ParLaws.isSmoothChar_loc χ w, fun x => rfl⟩
  obtain ⟨ξ₀, -, huniq, -⟩ := GlobalTheory.T.heckeChar_localComponent_exists_unique_unitary D.host.E χ w
  have hξ : ξ = χ.loc w := (huniq _ h).trans (huniq _ hcomp).symm
  subst hξ
  rw [hloc, ParLaws.locPar_ofChar, rcAt]
  rw [hchar]
  rfl

end GlobalTheory.RankOneComp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuationStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_completionIso_preserves_valuation : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ x : s.v.adicCompletion (maximalRealSubfield L), Valued.v (c x) = Valued.v x := by
  first | exact @GlobalTheory.SplitConjVal.valuation_eq | exact GlobalTheory.SplitConjVal.valuation_eq | (intros; apply GlobalTheory.SplitConjVal.valuation_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceUnitsCharacterEqOfAgreeOnFieldStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_unitsCharacter_eq_of_agree_on_field : ∀ {L : Type} [Field L] [NumberField L] [IsCMField L] (s : SplitPlace L) (c : s.v.adicCompletion (maximalRealSubfield L) ≃+* s.w.adicCompletion L), Continuous c → (∀ x : L, c (s.i x) = algebraMap L (s.w.adicCompletion L) x) → ∀ (μ : (s.w.adicCompletion L)ˣ →* ℂˣ) (ξ : (s.v.adicCompletion (maximalRealSubfield L))ˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar μ → (∃ N : ℕ, ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, Valued.v ((u : s.v.adicCompletion (maximalRealSubfield L)) - 1) ≤ WithZero.exp (-(N : ℤ)) → ξ u = 1) → (∀ k : Lˣ, ξ (Units.map (s.i : L →* s.v.adicCompletion (maximalRealSubfield L)) k) = μ (Units.map (algebraMap L (s.w.adicCompletion L)).toMonoidHom k)) → ∀ u : (s.v.adicCompletion (maximalRealSubfield L))ˣ, ξ u = μ (Units.map c.toMonoidHom u) := by
  first | exact @GlobalTheory.ConjDense.eq_of_agree | exact GlobalTheory.ConjDense.eq_of_agree | (intros; apply GlobalTheory.ConjDense.eq_of_agree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.StandardBasesHyperbolicPairOrthonormal
section
noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)

open GlobalTheory.KerStd.HypCoord in

theorem GlobalTheory.KerStd.hyp_of_stdBases : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → OrbitPlaces.OrbOK D p → ((IsResidueClassZero D p ∧ hP D p ≠ 0) ∨ IsSg D p) → ∀ (om oms : Fin (nP D p / 2) → MaximalUnramifiedExtension p), OwOK (nP D p) σ om oms → TrDual (nP D p) σ om oms → ∀ (R : Finset (OrbitPlaces.Pl D)), OrbitPlaces.IsReps D p R → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ f f' : (R × Fin (nP D p / 2)) × Fin N × Fin N' → Fin r → MaximalUnramifiedExtension p, HypPair σ f f' ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (hypZ D p σ om oms R f f') (thOrth D lam c b G) := by
  intro D p _ lam σ hσ hO hcl om oms hOw hTr R hR N N' L L' P P' hA hP hP' r b hb ho
  have hcl' : IsResidueClassZero D p ∨ IsSg D p := hcl.elim (fun h => Or.inl h.1) Or.inr
  have hONB : Formalism.L2.KerInert.RepFrame.LamONB D lam b :=
    Formalism.L2.KerInert.RepFrame.lamONB_of_cols D lam b
      (Formalism.L2.KerInert.RepFrame.rank_of_locBasis L L' hA.2.2.1 hA.2.2.2 b hb)
      (Formalism.L2.KerInert.RepFrame.cols_of_trace D (Formalism.L2.KerInert.RepFrame.trace_tau_sum D) lam b ho)
  obtain ⟨hg, hh⟩ := GlobalTheory.T.frobeniusLift_moves_letter_coordinates D p lam σ hσ hcl' N N' L L' P P' hP hP' r b
  have hpair := GlobalTheory.T.orthonormalLocalBasis_coordinates_dual D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hONB
  have hiso := norm_sigma_eq p σ hσ
  have hhint := GlobalTheory.T.norm_localBasis_standardCoord_le_one_inert D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hb
  have hgint : ∀ z a b₀ i, ‖gK D lam P P' b z a b₀ i‖ ≤ 1 := fun z a b₀ i => by
    rw [← hiso, hg]; exact hhint _ _ _ _
  have hg2 : ∀ z a b₀ i, σ (σ (gK D lam P P' b z a b₀ i)) = gK D lam P P' b (posPl D p z 2) a b₀ i :=
    fun z a b₀ i => by rw [hg, hh, posPl_add]
  obtain ⟨hf1, hf2⟩ := GlobalTheory.T.hyperbolicCoordinates_integral_sigma_sq_fixed D p σ om oms R N N' r (gK D lam P P' b) hO
    (fun x hx => by rw [hiso]; exact hx) hOw hgint hg2
  obtain ⟨hi1, hi2⟩ := GlobalTheory.T.hyperbolicCoordinates_isotropic D p σ om oms R N N' r (gK D lam P P' b) (hK D lam P P' b) hO hR hg hpair
  have hd := GlobalTheory.T.hyperbolicCoordinates_dual D p σ om oms R N N' r (gK D lam P P' b) (hK D lam P P' b) hO hR hTr hg hpair
  refine ⟨fOf D p σ om R (gK D lam P P' b), fOf' D p σ oms R (gK D lam P P' b), ⟨hf1, hf2, hi1, hi2, hd⟩, ?_⟩
  have hlin := GlobalTheory.T.linearForms_hyperbolicCoordinates_eq_target D p σ om oms R N N' r _ (gK D lam P P' b) (Formalism.L2.KerInert.RepFrame.lamB D lam b)
    (fun k j => chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2))) hO hR (GlobalTheory.T.traceDual_expansion_orbitLength D p σ om oms hTr)
    (fun q z a b₀ => GlobalTheory.T.lambdaTau_orthonormalBasis_sum_coordinates D p lam σ hσ hcl' N N' L L' P P' hP hP' r b hONB q z a b₀)
  refine GlobalTheory.T.standardSeries_scaled_eq_orthonormalBasisSeries D p lam N N' r P P' b _ (fun i => ?_) hlin
  simp only [hypZ, linEv, linOd, map_sum, map_add, map_mul, MvPowerSeries.constantCoeff_C, MvPowerSeries.constantCoeff_X,
    mul_zero, apply_ite MvPowerSeries.constantCoeff, map_zero, ite_self, Finset.sum_const_zero, add_zero]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaChainLastStepIntertwinesMatchedHecke
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped ComplexOrder

namespace GlobalTheory.Hk3.StepX

variable {D : D7}

theorem gram_posDef_X (τ : D.what₂.Tau) : (gramAt D D.sp.X' τ).PosDef := by
  have := D.sp.X'_sig (tauE D τ)
  rw [D7.X'_posDef D] at this
  exact GlobalTheory.DefiniteQuotient.posDef_of_signature this

theorem lift_symm_comp {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (L : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ))
    (x : (⨂[ℂ] τ, M.sm τ) →ₗ[ℂ] (GA D V → ℂ)) :
    PiTensorProduct.lift.symm (L ∘ₗ x) = postOn M L (PiTensorProduct.lift.symm x) := by
  refine MultilinearMap.ext fun v => ?_
  rw [postOn_apply]
  simp [PiTensorProduct.lift_symm]

theorem integ_X {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D D.sp.X' →* Module.End ℂ (WO S D.sp.X' → ℂ)}
    (hW : IsWeilDatumO ψ S D.sp.X' χS χT om) {f : WO S D.sp.X' → ℂ} (hf : IsThetaFunO ψ S D.sp.X' f)
    (Φ : GA D D.sp.X' → ℂ) (hΦc : Continuous Φ) (hl : ∀ γ ∈ GQ D.sp.X', ∀ h, Φ (γ * h) = Φ h)
    (ν : Measure (GA D D.sp.X')) (hν : ν.IsHaarMeasure) (𝓕 : Set (GA D D.sp.X'))
    (h𝓕 : IsFundamentalDomain (GQ D.sp.X') 𝓕 ν) (g : GA D S) (y : GA D D.sp.X') :
    IntegrableOn (fun h => thetaKO om g h f * Φ (h * y)) 𝓕 ν := by
  have : IsTopologicalGroup (GA D D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have : BorelSpace (GA D D.sp.X') := ⟨rfl⟩
  have : Countable (GQ D.sp.X') := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig D.sp.X'.gram
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.DefiniteQuotient.exists_compact D.sp.X' gram_posDef_X
  refine GlobalTheory.integrableOn_fundamentalDomain_of_cocompact _ (GQ D.sp.X') C hC (fun h => ?_) ν hν 𝓕 h𝓕 _ ?_ ?_
  · obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    exact ⟨γ⁻¹, inv_mem hγ, by rwa [inv_mul_cancel_left]⟩
  · exact ((hW.om_cont f hf 0).comp (Continuous.prodMk_right g)).mul (hΦc.comp (continuous_mul_right y))
  · intro γ hγ h
    have h1 := (GlobalTheory.thetaKO_rat_left_and_eigen_right ψ S D.sp.X' χS χT om hW f hf).1 1 (one_mem _) γ hγ g h
    rw [one_mul] at h1
    show thetaKO om g (γ * h) f * Φ (γ * h * y) = thetaKO om g h f * Φ (h * y)
    rw [h1, mul_assoc, hl γ hγ]

theorem hyp_inv {V : HSp D} (c : CoefA V) (hc : c.Is) {β : GL (Fin V.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : IsSDFrame V β Λ 1) {L : LevDat D.host.E ℂ V.rank}
    {P : Pl D.host.E} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {f : Bridge.Gf V → c.W} (hf : f ∈ Bridge.AdForms (Bridge.ratF V) c.coef.ρ (levEnv V β L).J (levEnv V β L).χ) :
    ∀ k ∈ hyp V P, ∀ h, c.ext f (h * k) = c.ext f h := by
  obtain ⟨n, hB⟩ := hβ
  have hlev := (GlobalTheory.LevOp.level_operators V β Λ _ (flag1L L) hB P (GlobalTheory.DefLiftHecke.one_pow_notMem P n) hP).1
  exact fun k hk h => GlobalTheory.DefLiftHecke.ext_level c hc hf (hlev k hk).1 (hlev k hk).2 h

theorem mult_stable {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (hθ : IsInfFam θ) (M : DSModel V S)
    {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
    (hβ : IsSDFrame V β Λ N) {L : LevDat D.host.E ℂ V.rank} {P : Pl D.host.E} (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P) (c : List ℤ →₀ ℂ) {U : MMap M}
    (hU : U ∈ Mult θ M (levS V β L) (levChi V β L)) : postOn M (hk V P c) U ∈ Mult θ M (levS V β L) (levChi V β L) := by
  obtain ⟨n, hB⟩ := hβ
  have hN' : ((N ^ n : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := fun h' =>
    hN (P.isPrime.mem_of_pow_mem n (by rwa [Nat.cast_pow] at h'))
  exact (GlobalTheory.LevOp.level_operators V β Λ _ L hB P hN' hP).2.2.2.2 S θ M c hθ U hU

theorem toMap_hkF {V : HSp D} (c : CoefA V) (hc : c.Is) {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm]
    (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) (P : Pl D.host.E) (z : List ℤ →₀ ℂ) (f : Bridge.Gf V → c.W) (w : Dm) :
    c.toMap pr (hkF V P z f) w = hk V P z (c.toMap pr f w) := by
  funext h
  show pr (c.ext (hkF V P z f) h) w = _
  rw [GlobalTheory.DefLiftHecke.ext_hkF c hc, GlobalTheory.ThetaIntHecke.hk_apply]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  rfl

set_option maxHeartbeats 2000000 in

theorem liftInt_toMap_hk {ψ : AddChar (AF D.host.F) ℂ} {S : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D D.sp.X' →* Module.End ℂ (WO S D.sp.X' → ℂ)} {P : Pl D.host.E}
    (hW : IsWeilDatumO ψ S D.sp.X' χS χT om) {ν : Measure (GA D D.sp.X')} {𝓕 : Set (GA D D.sp.X')}
    (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ D.sp.X') 𝓕 ν) (hfix : VacFix ψ om P)
    (cS cX : List ℤ →₀ ℂ) (hM : Match ψ om P cS (dualC cX)) {f0 : WO S D.sp.X' → ℂ} (hf0 : IsVacAt ψ S D.sp.X' P f0)
    (c : CoefA D.sp.X') (hc : c.Is) {β : GL (Fin D.sp.X'.rank) (Lev.EAf D)}
    {Λ : Submodule (𝓞 D.host.E) (Fin D.sp.X'.rank → D.host.E)} (hβ : IsSDFrame D.sp.X' β Λ 1)
    {L : LevDat D.host.E ℂ D.sp.X'.rank} (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ Formalism.IndefR.Lev.IsConjPl PP P)
    {Dm : Type} [AddCommGroup Dm] [Module ℂ Dm] (pr : c.W →ₗ[ℂ] Dm →ₗ[ℂ] ℂ) {f : Bridge.Gf D.sp.X' → c.W}
    (hf : f ∈ Bridge.AdForms (Bridge.ratF D.sp.X') c.coef.ρ (levEnv _ β L).J (levEnv _ β L).χ) (w : Dm) :
    Lift.liftInt ν 𝓕 (thetaKO om) f0 (c.toMap pr (hkF D.sp.X' P cX f) w) =
      hk S P cS (Lift.liftInt ν 𝓕 (thetaKO om) f0 (c.toMap pr f w)) := by
  have he : c.toMap pr f w = (pr.flip w) ∘ c.ext f := rfl
  have hlev := hyp_inv c hc hβ hP hf
  have hcont : Continuous (c.toMap pr f w) := by
    rw [he]
    exact (LinearMap.continuous_of_finiteDimensional (pr.flip w)).comp (GlobalTheory.ThetaIntegrand.ext_continuous c hc β L hf)
  have hl : ∀ γ ∈ GQ D.sp.X', ∀ h, c.toMap pr f w (γ * h) = c.toMap pr f w h := fun γ hγ h => by
    rw [he, Function.comp_apply, Function.comp_apply, GlobalTheory.ThetaIntegrand.ext_invariant c hf γ hγ h]
  have hr : ∀ k ∈ hyp D.sp.X' P, ∀ h, c.toMap pr f w (h * k) = c.toMap pr f w h := fun k hk h => by
    rw [he, Function.comp_apply, Function.comp_apply, hlev k hk h]
  rw [toMap_hkF c hc pr]
  exact GlobalTheory.ThetaIntHecke.liftInt_hk ψ S D.sp.X' χS χT om P hW ν 𝓕 hν h𝓕 hfix cS cX hM f0 hf0 _ hl hr
    (fun g z _ => integ_X hW hf0.1 _ hcont hl ν hν 𝓕 h𝓕 g z)

theorem sub_comp_apply {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (u u' : M →ₗ[ℂ] N)
    (H : N →ₗ[ℂ] N) (x : M) (h : u' x = H (u x)) : (u' - H ∘ₗ u) x = 0 := by
  rw [LinearMap.sub_apply, LinearMap.comp_apply, h, sub_self]

theorem eq_of_sub_comp {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (u u' : M →ₗ[ℂ] N)
    (H : N →ₗ[ℂ] N) (h : u' - H ∘ₗ u = 0) (x : M) : u' x = H (u x) := by
  have := congrArg (fun L => L x) h
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, sub_eq_zero] at this
  exact this

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 2000000 in

theorem at_It (R : RealDat D A Ks) (F : Face D A) (hC : Core R F) (t : T) (P : Pl D.host.E) (hP : Good R t P)
    (hfix : VacFix R.ψ (R.ωX t) P) (cS cX : List ℤ →₀ ℂ) (hM : Match R.ψ (R.ωX t) P cS (dualC cX))
    (y y' : (R.HX t).H) (hy : (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y)) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank)
    (w : SmT R.MX) :
    (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 (R.ItX φ w) =
      hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX φ w)) := by
  have hIo := hC.chain.ioX t
  have hν := hC.models.νX t
  have hmem : (R.HX t).e y ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ (levEnv _ R.βX (R.datXt t)).J
      (levEnv _ R.βX (R.datXt t)).χ :=
    (hC.models.HX t).2.1.le (LinearMap.mem_range_self _ y)
  have k := liftInt_toMap_hk (hC.chain.ωX t) hν.1.1 hν.2 hfix cS cX hM ((GlobalTheory.T.fockVectors_chain_isVacuum_off_thetaLevels R F hC t P hP).2.1 φ)
    R.cX hC.models.cX hC.lev.βX (L := R.datXt t) hP R.prX hmem w
  have e1 : (((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y' : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
      SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w = R.cX.toMap R.prX (hkF D.sp.X' P cX ((R.HX t).e y)) w :=
    congrArg (fun f => R.cX.toMap R.prX f w) hy
  have hyY : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ) (R.cX.toMap R.prX ((R.HX t).e y) w) =
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 (R.ItX φ w) :=
    funext fun g' => hIo.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y) φ w g'
  have hyY' : Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ)
      ((((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y' : LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e)) :
        SmT R.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) w) =
      (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 (R.ItX φ w) :=
    funext fun g' => hIo.eq ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y') φ w g'
  exact hyY'.symm.trans ((congrArg (Lift.liftInt (R.νX t) (R.fdX t) (thetaKO (R.ωX t)) (R.ptX t φ)) e1).trans
    (k.trans (congrArg (hk _ P cS) hyY)))

end GlobalTheory.Hk3.StepX

set_option maxHeartbeats 2000000 in

theorem GlobalTheory.Hk3.StepX.stepX_hk : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ t P, Good R t P → VacFix R.ψ (R.ωX t) P → ∀ cS cX, Match R.ψ (R.ωX t) P cS (dualC cX) → ∀ y y' : (R.HX t).H, (R.HX t).e y' = hkF D.sp.X' P cX ((R.HX t).e y) → ∀ v, (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1 v = hk _ P cS ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1 v) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS t P hP hfix cS cX hM y y' hy
  have hm := D.R.two_le_m
  have hu : (hk (Yc D (D.R.m - 1)) P cS ∘ₗ
      ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1)) ∈ R.CC t (D.R.m - 1) := by
    rw [mem_multT, GlobalTheory.Hk3.StepX.lift_symm_comp]
    exact GlobalTheory.Hk3.StepX.mult_stable R.θ hC.models.inf (R.MY (D.R.m - 1)) (hC.lev.βY (D.R.m - 1) (by omega))
      (L := R.datYt t (D.R.m - 1) R.triv) ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hP).1 hP cS
      ((mem_multT _ _ _ _ _).1 (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).2)
  have hz := GlobalTheory.multT_eq_zero_of_apply_eq_zero R.θ (R.MY (D.R.m - 1)) _ _ (R.νY t (D.R.m - 1)) (R.fdY t (D.R.m - 1))
    hC.models.inf (hC.models.νY' t).1.1 (hC.models.νY' t).2 (hS.1 t (D.R.m - 1) (by omega))
    (((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).1) - hk (Yc D (D.R.m - 1)) P cS ∘ₗ
      ((R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y)).1))
    (sub_mem (R.ioX t ((R.cX.toMap R.prX ∘ₗ (R.HX t).e).rangeRestrict y')).2 hu)
  have hex : ∃ φ w, R.ItX φ w ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact (hC.chain.ItX t).ne (LinearMap.ext fun φ => LinearMap.ext fun w => hcon φ w)
  refine hex.elim fun φ0 hw0 => hw0.elim fun w0 hne => ?_
  have h0 := hz _ hne (GlobalTheory.Hk3.StepX.sub_comp_apply _ _ _ _ (GlobalTheory.Hk3.StepX.at_It R F hC t P hP hfix cS cX hM y y' hy φ0 w0))
  exact GlobalTheory.Hk3.StepX.eq_of_sub_comp _ _ _ h0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaIntertwinesMatchedOperators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SysW

set_option maxHeartbeats 1000000 in

theorem matched_operators_theta_intertwine : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ SF, IsSF R SF → ∀ i t P, Good R t P → ∀ cV cW, MatchW R i t P cV cW → ∀ hV, IsOpsV R i t hV → (∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y)) ∧ ∀ c, ∀ w ∈ Wcc R SF i c, hV P cV (LinearMap.adjoint (R.thG i t) w) = evC (Wc D i) P (c P) cW • LinearMap.adjoint (R.thG i t) w := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hS hX SF hSF i t P hP cV cW hM hV hhV
  have hP0 : Good R A.μ0 P := ((GlobalTheory.GoodPrimes.good_primes R F hC.lev).2.1 t P hP).2.2
  have hWinj : Function.Injective (R.HW i (sg0 D A)).e := (hC.models.HW i (sg0 D A)).1
  have key : ∀ h, IsOpsW R i h → ∀ y, R.thG i t (hV P cV y) = h P cW (R.thG i t y) := by
    intro h hh y
    have h1 := hM y (hV P cV y) (hhV P hP cV y)
    have h2 := hh P hP0 cW (R.thG i t y)
    exact hWinj (h1.trans h2.symm)
  refine ⟨key, ?_⟩
  intro c w hw
  have XW := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R F hC hS hX SF hSF i
  obtain ⟨hW, hWo, hWn, -, -, -, hWe, -⟩ := XW
  have XV := (GlobalTheory.T.realization_family_normal_operators R F hC.lev hC.fam hC.models).2 i t
  obtain ⟨hV', hV'o, hV'n⟩ := XV
  have hVinj : Function.Injective (R.HV i t).e := (hC.models.HV i t).1
  have heq : ∀ c, hV P c = hV' P c := fun c => LinearMap.ext fun x => hVinj (by rw [hhV P hP, hV'o P hP])
  have nV' : Commute (hV' P cV) (LinearMap.adjoint (hV' P cV)) :=
    Eq.mpr (congrArg (Commute (hV' P cV)) (hV'n.2 P hP cV)) (hV'n.1 P P hP hP _ _)
  have nV : Commute (hV P cV) (LinearMap.adjoint (hV P cV)) :=
    Eq.mpr (congrArg (fun L => Commute L (LinearMap.adjoint L)) (heq cV)) nV'
  have nW : Commute (hW P cW) (LinearMap.adjoint (hW P cW)) :=
    Eq.mpr (congrArg (Commute (hW P cW)) (hWn.2 P hP0 cW)) (hWn.1 P P hP0 hP0 _ _)
  exact GlobalTheory.T.eigenvector_adjoint_intertwiner_normal_operators (R.thG i t) (fun _ : Unit => hV P cV) (fun _ : Unit => hW P cW) (fun _ u => key hW hWo u)
    (fun _ => nV) (fun _ => nW) () _ w (hWe c P hP0 cW w hw)

end GlobalTheory.SysW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaLiftGoodProjectorIntertwinesMatchedHeckeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaLiftGoodProjector_intertwines_matchedHecke : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → SchurAll R → ∀ i t P, Good R t P → VacFix R.ψ (R.ωP i t) P → ∀ cV cW, Match R.ψ (R.ωP i t) P (dualC cV) cW → MatchW R i t P cV cW := by
  first | exact @GlobalTheory.DefLiftHecke.matchW_of_match | exact GlobalTheory.DefLiftHecke.matchW_of_match | (intros; apply GlobalTheory.DefLiftHecke.matchW_of_match <;> assumption)
end

