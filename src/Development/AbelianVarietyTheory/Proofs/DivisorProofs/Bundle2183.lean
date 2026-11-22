import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1880
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0155
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0184
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0014
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0015
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0016
import Development.AutomorphicArithmetic.DivisorFrames.ExistsUnitaryAutomorphicFormOfWeightVectorValued
import Development.AutomorphicArithmetic.DivisorFrames.Bundle0014
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0739
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLowestKTypeFockMapThetaVectors
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0556
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0232
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2138
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondMemberEqProdLocalGridBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2159
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2077
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0913
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2160
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1932
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0950
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2139

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallPlacePrimeLocal
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem emb_cj {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (io : PadicAlgCl l ≃+* ℂ)
    (τ : E →+* PadicAlgCl l) :
    io.toRingHom.comp (GlobalTheory.ExpFrame.cj τ) = ComplexEmbedding.conjugate (io.toRingHom.comp τ) := by
  ext x
  exact IsCMField.complexEmbedding_complexConj E (io.toRingHom.comp τ) x

private theorem places_inj {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] (io : PadicAlgCl l ≃+* ℂ)
    {ι : Type} {inc : ι → (E →+* PadicAlgCl l)} (h : IsHalf inc) :
    Function.Injective fun τ => InfinitePlace.mk (io.toRingHom.comp (inc τ)) := by
  intro τ τ' e
  have hi : ∀ a b : E →+* PadicAlgCl l, io.toRingHom.comp a = io.toRingHom.comp b → a = b := fun a b hab =>
    RingHom.ext fun x => io.injective (RingHom.congr_fun hab x)
  rcases InfinitePlace.mk_eq_iff.1 e with e | e
  · exact h.1 (hi _ _ e)
  · exact absurd (hi _ _ ((emb_cj io _).trans e)) (h.2.1 τ τ')

set_option maxHeartbeats 1600000 in
private theorem finiteRing_sq_sub_mul_sq_eq_of_card {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)
    (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} (hN : N = (Vc D j).rank)
    (F : Frame l D.what₂.Tau N) (e0 : D.what₂.LL →+* PadicAlgCl l) (ix : F.I → (blk p j t).Pl × ℕ)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)) (T : Tied p j t F e0 ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (hmu : ∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res N (mu τ))) (hθ : F.IsEig mu θ) :
    ∃ π : Submodule ℂ (UA D.host.E N → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight N, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧
        (∀ v, GlobalTheory.Hk3.Good p.R.toRealDat t v → ∀ x ∈ locU N v, cLoc v x ∈ GlobalTheory.LFun.KGL v N → RU D.host.E N x φ = φ) ∧
        ∀ Q : (blk p j t).Pl, (∀ x ∈ locU N (labOf p j t Q), cLoc (labOf p j t Q) x ∈ GlobalTheory.LFun.KGL (labOf p j t Q) N →
          RU D.host.E N x φ = φ) ∧
        ∀ i, (ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E N).comp (locU N (labOf p j t Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j t Q) N).comap ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j t Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab N (ix i).2))
              ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype x)) φ = T.io (θ i) • φ := by
  subst hN
  classical
  have hs : (Vc D j).SigOK := D.sp.V_sig _
  have hp : (Vc D j).IsPosDef := p.vpos j
  have hinf : Formalism.L2.Theta.IsInfFam p.R.θ := p.charW.base.models.inf
  obtain ⟨jj, h₀, hTr⟩ := GlobalTheory.DefTransfer.exists_isTransfer D (Vc D j) p.R.θ hinf hs hp
  obtain ⟨B, hB1, hB2⟩ := UpperTheory.exists_invariant_posDef_hermitian_form_autForm_unitary D (Vc D j) hs hp jj hTr.2.1
  obtain ⟨Fm, hF0, hFl, hFr, hFh⟩ := UpperTheory.exists_nonzero_vectorValued_eigenform_unitary p j t F e0 ix inc T mu θ hθ
  have hb : ∀ τ, T.io.toRingHom.comp (e0.comp (Links.labLL D τ)) = Formalism.BasicNotions.TH.tauE D τ := fun τ => by
    rw [← Formalism.IndefR.Conj.labE_base τ]
    exact RingHom.ext fun x => T.liftFrame_embedding_base _
  have hemb : ∀ τ, T.io.toRingHom.comp (inc τ) = Formalism.BasicNotions.TH.tauE D τ ∨
      T.io.toRingHom.comp (inc τ) = ComplexEmbedding.conjugate (Formalism.BasicNotions.TH.tauE D τ) := fun τ => by
    rcases T.lab τ with h | h
    · exact Or.inl (by rw [h, hb])
    · exact Or.inr (by rw [h, emb_cj, hb])
  have hfix : ∀ (k : Formalism.L2.Theta.GA D (Vc D j)), (∃ h : (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k ∈ levJ p j t,
      levChi p j t ⟨_, h⟩ = 1) → ∀ g, Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict k) = Fm g := by
    rintro k ⟨h, h1⟩ g
    have := hFr ⟨_, h⟩ g
    rw [h1, Units.val_one, one_smul] at this
    exact this
  have hev : ∀ᶠ κ in nhds (1 : Formalism.L2.Theta.GA D (Vc D j)), ∀ g,
      Fm (g * (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict κ) = Fm g :=
    (GlobalTheory.ThetaIntegrand.eventually_level (Vc D j) (p.R.βV j) (p.R.datVt j t)).mono fun κ h => hfix κ h
  obtain ⟨F1, h10, h1l, h1i, h1e, A, hA⟩ := UpperTheory.vectorValued_autForm_equivariant_infinite_component D (Vc D j) p.R.θ jj h₀ hinf hTr
    (fun τ => T.io.toRingHom.comp (inc τ)) hemb mu T.sh Fm hF0 hFl hev
  let lam : D.what₂.Tau → DomWeight (Vc D j).rank := fun τ =>
    ⟨fun a => (mu τ a : ℤ) + T.sh τ, fun a b hab => add_le_add_left (Int.ofNat_le.2 (hmu τ hab)) _⟩
  obtain ⟨π, hπ, hw, φ, hφ, hφ0, hsum⟩ := UpperTheory.exists_unitaryAutomorphicForm_of_weightVectorValued D.host.E (Vc D j).rank D.what₂.Tau (fun τ => T.io.toRingHom.comp (inc τ))
    (places_inj T.io T.half) mu T.sh lam (fun _ _ => rfl) B hB1 hB2 F1 h10 h1l h1i h1e
  have htr : ∀ g y, F1 (g * y) = A (Fm ((Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict (jj g * h₀) *
      (Formalism.L2.Theta.finHom (Vc D j)).rangeRestrict (GlobalTheory.DefTransfer.cj jj h₀ y))) := fun g y => by
    rw [hA, ← map_mul, GlobalTheory.DefTransfer.cj_apply, map_mul jj]
    congr 3
    group
  have hK : ∀ v v', GlobalTheory.Hk3.Good p.R.toRealDat t v' → GlobalTheory.Hk3.hyp (Vc D j) v = GlobalTheory.Hk3.hyp (Vc D j) v' →
      ∀ x ∈ GlobalTheory.DefTransfer.KP (Vc D j).rank v, RU D.host.E (Vc D j).rank x φ = φ := by
    intro v v' hg he x hx
    have h1 := (hTr.2.2.2.2.2.2.1 v x).2 hx
    rw [he] at h1
    have h2 := hfix _ (UpperTheory.levChi_eq_one_of_good_place p j t v' hg _ h1)
    have := hsum Unit Finset.univ (fun _ => x) 1 (fun _ _ => hx.1.1) fun g => by
      rw [Finset.univ_unique, Finset.sum_singleton, one_smul, htr, h2, hA]
    simpa using this
  refine ⟨π, hπ, fun τ => ⟨lam τ, fun _ => rfl, hw τ, ?_⟩, φ, hφ, hφ0, fun v hv x h1 h2 => hK v v hv rfl x ⟨h1, h2⟩, fun Q => ?_⟩
  · rw [emb_cj]
    exact GlobalTheory.DefU.AU.HasWt.conjugate (π := GlobalTheory.DefU.AU.mk ⟨π, hπ⟩) (hw τ)
  have hg : GlobalTheory.Hk3.Good p.R.toRealDat t (plOf p j t Q) :=
    ((GlobalTheory.GoodPrimes.good_primes p.R.toRealDat (p.P.face p.Dcf p.Spf p.Del p.h0 Csz).lv2
      p.charW.base.lev).2.2.2 p.charW.base.fam t Q.1 Q.2).1
  have hKQ := hK (labOf p j t Q) _ hg (GlobalTheory.SphConj.hyp_conj _ _)
  refine ⟨fun x h1 h2 => hKQ x ⟨h1, h2⟩, fun i hi => ?_⟩
  subst hi
  obtain ⟨r1, r2, -⟩ := (T.ix_range (ix i)).1 ⟨i, rfl⟩
  obtain ⟨hloc, R, hR, hRs⟩ := UpperTheory.exists_sphericalHeckeRep_splitLabel_of_offLevelPlace p j t (ix i).1 (ix i).2 r1 r2
  rw [GlobalTheory.SplitTransfer.heckeVec_divInd hTr hKQ hR]
  refine hsum _ R (fun γ => (GlobalTheory.DefTransfer.cj jj h₀).symm γ) _ (fun γ hγ => ((hTr.2.2.2.2.2.2.2 _ _ R hR).1 γ hγ).1.1) fun g => ?_
  simp only [htr, MulEquiv.apply_symm_apply]
  rw [← map_sum, hRs _ Fm hFr, hA, ← map_smul]
  exact congrArg A (hFh i hloc _)

theorem _root_.GlobalTheory.T.small_place_prime_local : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), PtAt.Rows p → More p →
    ∀ (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W → NumOk P W →
    ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → SmallAt p j P w →
    ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
      (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
      (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π : Submodule ℂ (UA D.host.E P.Nr → ℂ), IsAutRepU π ∧
      (∀ τ, ∃ lam : DomWeight P.Nr, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
        HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
      (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
      ∃ φ ∈ π, φ ≠ 0 ∧ ∀ Q : (blk p j (p.R.mu w)).Pl, ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∉ (plOf p j (p.R.mu w) Q).asIdeal →
        (∀ x ∈ locU P.Nr (labOf p j (p.R.mu w) Q), cLoc (labOf p j (p.R.mu w) Q) x ∈ GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) P.Nr →
          RU D.host.E P.Nr x φ = φ) ∧
        ∀ i, (R.ix i).1 = Q →
          GlobalTheory.LFun.heckeVec ((RU D.host.E P.Nr).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype)
            ((GlobalTheory.LFun.KGL (labOf p j (p.R.mu w) Q) P.Nr).comap ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype))
            (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov D.host.E (labOf p j (p.R.mu w) Q))
              (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab P.Nr (R.ix i).2))
              ((cLoc (labOf p j (p.R.mu w) Q)).comp (locU P.Nr (labOf p j (p.R.mu w) Q)).subtype x)) φ = T.io (θ i) • φ := by
  intro D L hT Gi Gl Kc Y cX ex Csz p _ _ j P W hD _ w hw hW _ _ F R inc T mu θ hmu hθ
  obtain ⟨π, h1, h2, φ, h3, h4, h5, h6⟩ := finiteRing_sq_sub_mul_sq_eq_of_card p j (p.R.mu w) hD.Nr F R.e0 R.ix inc T mu θ hmu hθ
  exact ⟨π, h1, h2, fun v hv => ⟨φ, h3, h4, h5 v (UpperTheory.good_place_of_twist_place_dividing p j P W hD w hw hW v hv)⟩, φ, h3, h4, fun Q _ => h6 Q⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StageTriangleKernelIntegrable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StageConv

theorem m_le_of_size {D : D7} {large₂ : SizeData₂ D} (h : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) : D.R.m ≤ D.R.r + 1 := by
  have h4 : D.R.m ^ 4 ≤ D.R.f := h.2.2.1
  have hm : 44 ≤ D.R.m := h.2.2.2.1
  have hfm : D.R.f * D.R.m ≤ (D.R.r + 1) ^ 3 := h.2.2.2.2.2.2.1
  by_contra hc
  push_neg at hc
  have h1 : (D.R.r + 1) ^ 3 < D.R.m ^ 3 := Nat.pow_lt_pow_left hc (by norm_num)
  have h2 : D.R.m ^ 3 ≤ D.R.m ^ 4 * D.R.m := by
    calc D.R.m ^ 3 ≤ D.R.m ^ 5 := Nat.pow_le_pow_right (by omega) (by norm_num)
      _ = D.R.m ^ 4 * D.R.m := by ring
  have h3 : D.R.m ^ 4 * D.R.m ≤ D.R.f * D.R.m := Nat.mul_le_mul_right _ h4
  omega

theorem rank_lt {D : D7} {i j : Fin D.R.m} {p q : ℕ} {A A' WW : HSp D} (hmr : D.R.m ≤ D.R.r + 1)
    (hp : p ≤ pp D j) (hq : q ≤ qq D j) (hA : A.rank + 2 * pp D j = rankV D (i + 1) (j + 1) + 2 * p)
    (hA' : A'.rank + 2 * qq D j = rankV D i j + 2 * q) (hd : A.rank + A'.rank = WW.rank) :
    WW.rank < 2 * (A.rank - p) := by
  have e1 : rankV D ((i : ℕ) + 1) ((j : ℕ) + 1) = rankV D i j + D.R.t + sLen D := by
    simp only [rankV]; ring
  have hpp : 2 * pp D j ≤ D.R.m - 1 := by
    simp only [pp]; have := j.2; omega
  have hs : sLen D = D.R.r + 6 := rfl
  rw [e1] at hA
  omega

theorem conv : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∀ t P h, MeasureTheory.IntegrableOn (X.ker W.ψ W.θ t P h) X.fd X.m := by
  intro hP _ _
  have hW := GlobalTheory.T.weil_convergence_of_siegel_set hP.siegelSetUnitary hP
  refine ⟨0, fun ε CF _ => ⟨0, 0, fun C _ D large₂ _ _ hRec T Lc μ₀ _ G => ?_⟩⟩
  intro W S _ _ i j p q A A' WW X hX t P h
  obtain ⟨hp, hq, hA, hA', hnA, _, _, hXi⟩ := hX
  obtain ⟨τ⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hrank : WW.rank < 2 * (A.rank - p) := rank_lt (m_le_of_size hRec.size) hp hq hA hA' hXi.rank
  have hf :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt W.ψ_std W.θ_is (hXi.fst t) (GlobalTheory.OneMapRef.isThetaFunO_of_isVacO hXi.isVac)
  have hΦ := GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := GlobalTheory.Grid.neg A) (T := WW) W.ψ_std W.θ_is (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B hf P
  obtain ⟨N, C', hint⟩ := hW D W.ψ W.θ W.θ_is true A WW _ _ (X.ω t) (hXi.weil t) p ⟨τ, hnA τ⟩ hrank X.m X.fd hXi.meas _ hΦ
  exact (hint h).1

end GlobalTheory.StageConv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMemSchwartzBruhatOfConductorExponentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPair_mem_schwartzBruhat_of_conductorExponentLE : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n c a a' : ℕ), IsUnif ϖ → CondLE ϖ n ν →
      GlobalTheory.StdPairCone.stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
        GlobalTheory.StdPairCone.stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  first | exact @GlobalTheory.StdPairSBDepth.stdPair_mem_SB | exact GlobalTheory.StdPairSBDepth.stdPair_mem_SB | (intros; apply GlobalTheory.StdPairSBDepth.stdPair_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairSecondMemberEqProdLocalGridBasesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standardPairSecondMember_eq_prod_local_gridBases : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (B : Frames G) (t : T) (i j : Fin D.R.m) (X : TriG G i j) (ε : AE D), IsIdemSum ε (locPl G t) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.alpha G t i j / GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.beta G i j) ε (X.ideal (locPl G) t)
        (spW G i j).rank (spW₁ G i j) (spX G i j) X.rA'.β X.rW.β = prodB B t i j ε (locSnd B t X) := by
  first | exact @GlobalTheory.TopFlip.StdSnd.stdSnd_eq_prodB | exact GlobalTheory.TopFlip.StdSnd.stdSnd_eq_prodB | (intros; apply GlobalTheory.TopFlip.StdSnd.stdSnd_eq_prodB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuppAtMul
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

namespace GlobalTheory.BigOn.Exp.TupLe.Swap

section Defs

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev ThAt (a : AE D) (b Φ f : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) a
    (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 b Φ f

open Classical in

def adjDat (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (a : AE D) (x : WO (Vc D i) (Wc D i)) : ℂ :=
  if IsHalf a x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
    omegaQ Q (Wc D i).rank ξR (-1) (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0

variable {R} in
open Classical in

def keepPart (t : T0) (Q' : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := (R.Q t).filter fun P => P ∈ Q'

variable {R} in
open Classical in

def flipPart (t : T0) (Q' : Finset (Pl D.host.E)) : Finset (Pl D.host.E) := (R.Q t).filter fun P => P ∉ Q'

end Defs

theorem suppAt_mul' {D : D7} {V : HSp D} {e : AE D} {a b : GA D V} (ha : SuppAt e V a) (hb : SuppAt e V b) :
    SuppAt e V (a * b) := by
  intro i j
  have hm : mt V (a * b) = mt V a * mt V b := by first | rfl | simp [Formalism.L2.Theta.mt]
  have key : mt V a * mt V b - 1 = (mt V a - 1) * mt V b + (mt V b - 1) := by noncomm_ring
  rw [hm, key, Matrix.add_apply, Matrix.mul_apply, mul_add, Finset.mul_sum, hb i j]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ha i k]

end GlobalTheory.BigOn.Exp.TupLe.Swap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectivityFromAllEstimates
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn

set_option autoImplicit false

noncomputable section

open GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

namespace GlobalTheory.BigOn.OntoPath

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem onto_path : RunsSt → RatSt → GeoSt → (AtRec fun _ _ _ _ _ _ O => GlobalTheory.TraceClassRank.RankAtPlaces O) → TwistSt →
    ShareSt → BadSt → ExpSt → PageSt → OntoX := by
  intro hRuns hRat hGeo hRank hTw hSh hBad hExp hPage
  have H := ((((((((hRuns.and hRat).and hGeo).and hRank).and hTw).and hSh).and hBad).and hExp).and hPage)
  refine Closed.imp H ?_
  intro eps Fm CH _ H _
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨xR, hR⟩, ⟨xQ, hQ⟩⟩, ⟨cG, hG⟩⟩, ⟨cK, hK⟩⟩, ⟨cT, hT⟩⟩, ⟨cS, hS⟩⟩, ⟨cB, hB⟩⟩, ⟨cE, hE⟩⟩, ⟨cP, hP⟩⟩ := H
  set c0 : ℝ := max (max (max (max cG cK) (max cT cS)) (max (max cB cE) cP)) 1 with hc0
  let c : OnConst := ⟨c0, 14, 66 * c0 + 4⟩
  have hcb : OnPage.ConstBad c := ⟨le_rfl, le_rfl⟩
  have l1 : cG ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l2 : cK ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l3 : cT ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l4 : cS ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l5 : cB ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l6 : cE ≤ c.C := le_trans (by simp) (le_max_left _ _)
  have l7 : cP ≤ c.C := le_trans (by simp) (le_max_left _ _)
  obtain ⟨x1, h1⟩ := hG c l1 hcb
  obtain ⟨x2, h2⟩ := hK c l2 hcb
  obtain ⟨x3, h3⟩ := hT c l3 hcb
  obtain ⟨x4, h4⟩ := hS c l4 hcb
  obtain ⟨x5, h5⟩ := hB c l5 hcb
  obtain ⟨x6, h6⟩ := hE c l6 hcb
  obtain ⟨x7, h7⟩ := hP c l7 hcb
  refine ⟨2 * max c.CE 0, by positivity,
    max (max (max xR xQ) (max x1 x2)) (max (max x3 x4) (max (max x5 x6) x7)), ?_⟩
  intro x hx hx0 i p hp hm C hCC
  have a0 : max xR xQ ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hx0)
  have b0 : max x1 x2 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hx0)
  have c1 : max x3 x4 ≤ x := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hx0)
  have d0 : max (max x5 x6) x7 ≤ x := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hx0)
  obtain ⟨r, hr, hown⟩ := hR x hx (le_trans (le_max_left _ _) a0) i p hp hm
  have hrat := hQ x hx (le_trans (le_max_right _ _) a0) i p hp hm
  have hct := hm.2.1
  obtain ⟨O, hO⟩ := exists_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ (Fm.parT x hx i) (Fm.ex x hx i).kap_def
    (Fm.ex x hx i).errX r c hct.canon hct.halfEX hr
  have hrec : RecAt p (Fm.parT x hx i) r O := ⟨hO, hown⟩
  obtain ⟨gSup, gSpan, gLem, gData, gIdx, gDepth⟩ := h1 x hx (le_trans (le_max_left _ _) b0) i p hp hm r O hrec
  have kRank := h2 x hx (le_trans (le_max_right _ _) b0) i p hp hm r O hrec
  have tTw := h3 x hx (le_trans (le_max_left _ _) c1) i p hp hm r O hrec
  have sSh := h4 x hx (le_trans (le_max_right _ _) c1) i p hp hm r O hrec
  have bBad := h5 x hx (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  have eExp := h6 x hx (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) d0) i p hp hm r O hrec
  obtain ⟨pPage, pSizes, pX, pBad, pLev, pY, -, pE1u, pTie⟩ :=
    h7 x hx (le_trans (le_max_right _ _) d0) i p hp hm r O hrec
  have hL : Links2 p := GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hp hm.1
  obtain ⟨hC, hOk, hU, hBL, hRR, -⟩ := hL
  have hI := GlobalTheory.ClassSumIdentity.leafIdentity_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hrat
  have hT2 := GlobalTheory.BaseTwistIncl.leafTW2_of_isRec _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1 hOk hC hU hBL hrat
  obtain ⟨dG, dR, d2, dL⟩ := gDepth c.CE CH
  obtain ⟨err, herr⟩ := GlobalTheory.T.twistedPlacesBoundChain_twoRunChain _ _ _ _ _ _ (R2 p) (F2 p) _ _ (fw2 p) _ _ _ _ _ r c O hO 1
    ((R2 p).num (F2 p) c.CE CH) c.CE hOk hC.grp.levels hC.grp.chiW hC.models hC.tup.mu_conj hC.thP.thG hU hBL hrat hRR
    pLev pY gSup gSpan gLem gIdx gData kRank hI hT2 tTw sSh bBad dG dR d2 dL pPage pSizes pX pBad (eExp c.CE CH) le_rfl
    (pTie c.CE CH)
  obtain ⟨hon, hD⟩ := GlobalTheory.T.onClauses_with_error_of_splitPart _ _ _ _ _ _ _ _ _ _ p c.CE CH err herr
  have hDpos : 0 < (p.S false).D := by rw [hD]; exact hRR.1
  have hJ : ∀ w ∈ (p.S false).Tw, ∀ j, 0 ≤ p.Z.J0 ((p.S false).μ w) w j := (eExp C CH).1
  exact on_of_onWith_canonical _ _ _ (p.S false) p.Z c.CE C CH CH err hDpos pE1u
    (le_trans (mul_le_mul_of_nonneg_left (le_max_left c.CE 0) zero_le_two) hCC) hJ (fun w j => p.err_eq w j) hon

end GlobalTheory.BigOn.OntoPath

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicProperties
section
noncomputable section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.ThKBasic

theorem thetaBasic : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.ThetaBasic := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP
  have hS := hP.weil.isUSplitting
  obtain ⟨l, hl, hlt⟩ := GlobalTheory.T.exists_admissibleForm_adelicThetaSum F (Fin n × Fin d)
  refine ⟨fun Φ hΦ => ⟨?_, ?_, GlobalTheory.T.theta_moderate_growth_height hKP F E σ B n d X W M χX χW om r s r' s' hP Φ hΦ⟩, ?_⟩
  · refine (hS.cont l hl Φ hΦ).congr fun x => ?_
    simp only [theta]
    exact hlt _ (hS.pres _ _ hΦ)
  · intro γ hγ γ' hγ' g h
    simp only [theta]
    have e : om (γ * g, γ' * h) Φ = om (γ, γ') (om (g, h) Φ) := by
      rw [← Module.End.mul_apply, ← map_mul]; rfl
    rw [e]
    exact GlobalTheory.T.thetaSum_invariant_rational_unitary hKP F E σ B n d X W M χX χW om r s r' s' hP γ hγ γ' hγ' _ (hS.pres _ _ hΦ)
  · intro φ hφ g h
    obtain ⟨T, hT⟩ := hS.adm (g, h) l hl φ hφ
    refine T.continuous.congr fun f => ?_
    simp only [theta]
    have hm : pureA F (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) φ ∈ schA F (Fin n × Fin d) :=
      Submodule.subset_span ⟨f, φ, hφ, rfl⟩
    rw [← hlt _ (hS.pres _ _ hm)]
    exact (hT f).symm

end GlobalTheory.ThKBasic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeesawTripleMovedToSelfDualIsValidStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSeesawTriple_moved_to_selfDual_isValid : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').Is ψ θ α β νH S := by
  first | exact @GlobalTheory.BotMove.moveTri_is | exact GlobalTheory.BotMove.moveTri_is | (intros; apply GlobalTheory.BotMove.moveTri_is <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransporterMovesAtOfMovesAtOpenSetStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transporter_movesAt_of_movesAt_open_set : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (γ : LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l) (k k' k'' : (uAt r v i).Comp) (a c : GL (Fin D.R.r) D.host.E) (hma : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k') a) (hmc : GlobalTheory.LevelCusp.IsMatch ((uAt r v i).X k) ((uAt r v i).X k'') c) (W : Set (Frame ((uAt r v i).X k).Ψ D.R.r)), IsOpen W → W.Nonempty → W ⊆ ((uAt r v i).X k).dom → (∀ (z : Frame ((uAt r v i).X k).Ψ D.R.r) (hz : z ∈ ((uAt r v i).X k).dom), z ∈ W → MovesAt p r i v γ k k' a hma z hz ∧ MovesAt p r i v γ k k'' c hmc z hz) → ∀ (x : Frame ((uAt r v i).X k).Ψ D.R.r) (hx : x ∈ ((uAt r v i).X k).dom), MovesAt p r i v γ k k'' c hmc x hx → MovesAt p r i v γ k k' a hma x hx := by
  first | exact @GlobalTheory.ShareOn.movesAt_of_movesAt_open | exact GlobalTheory.ShareOn.movesAt_of_movesAt_open | (intros; apply GlobalTheory.ShareOn.movesAt_of_movesAt_open <;> assumption)
end

