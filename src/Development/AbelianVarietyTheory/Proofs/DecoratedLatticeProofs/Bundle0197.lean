import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0186
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsMulRightInvariantOfLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0152
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTwAn
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsGLExistsUnique

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselGroupQuotientFundamentalDomainCocompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselGroup_quotient_fundamentalDomain_cocompact : ∀ (D : D7) (ρ : ℕ) (B : BesLev D ρ), B.μR.IsHaarMeasure ∧ IsClosed (besGrp B.d B.o : Set (GA D B.V)) ∧ (∃ Ω : Set (GA D B.V), IsCompact Ω ∧ ∀ s ∈ besGrp B.d B.o, ∃ γ ∈ GQ B.V ⊓ besGrp B.d B.o, γ * s ∈ Ω) ∧ ∃ 𝓢 : Set (besGrp B.d B.o), IsFundamentalDomain ((GQ B.V).subgroupOf (besGrp B.d B.o)) 𝓢 B.μR ∧ B.μR 𝓢 < ⊤ ∧ ∀ F : GA D B.V → ℂ, ContinuousOn F (besGrp B.d B.o : Set (GA D B.V)) → (∀ γ ∈ GQ B.V ⊓ besGrp B.d B.o, ∀ s ∈ besGrp B.d B.o, F (γ * s) = F s) → IntegrableOn (fun s : besGrp B.d B.o => F s) 𝓢 B.μR ∧ ∫ s in 𝓢, F s ∂B.μR = ∫ a in B.vA.𝓕, ∫ n in B.vN.𝓝, F (n.1 * embA B.d B.o a) ∂B.vN.ν ∂B.vA.μ := by
  first | exact @GlobalTheory.BesselQuot.besGrp_quotient | exact GlobalTheory.BesselQuot.besGrp_quotient | (intros; apply GlobalTheory.BesselQuot.besGrp_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.Core.Mi.Shift

variable {D : D7}

theorem inner_left {ρ : ℕ} (B : BesLev D ρ) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsCharAF D.host.F ψ)
    (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (hφ : ∀ γ ∈ GQ B.A, ∀ g, φ (γ * g) = φ g)
    (hf : ∀ γ ∈ GQ B.V, ∀ g, f (γ * g) = f g) {γ : GA D B.A} (hγ : γ ∈ GQ B.A) (h : GA D B.A) :
    ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f (γ * h) n ∂B.vN.ν =
      ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν := by
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag B.V (isIsoSub_e B.d)
  obtain ⟨-, -, hconj, -, hrat⟩ := GlobalTheory.Unf.besSemi D ρ B
  obtain ⟨-, hψrat, hψconj, -⟩ := GlobalTheory.MixPer.charLaws D ψ hψ B.V B.V₀ B.A B.L ρ B.d B.o B.ζ 1
  obtain ⟨u1, u2, u3⟩ := B.vN.unit
  set δ : GA D B.V := embA B.d B.o γ with hδdef
  have hδ : δ ∈ GQ B.V := by
    have := (hrat 1 (one_mem _) γ).2 ⟨one_mem _, hγ⟩
    rwa [one_mul] at this
  have hmem : ∀ n : flagN B.d, δ⁻¹ * n.1 * δ ∈ flagN B.d := fun n => by
    have := hconj n.1 n.2 γ⁻¹
    rwa [map_inv, inv_inv] at this
  have hmem' : ∀ n : flagN B.d, δ * n.1 * δ⁻¹ ∈ flagN B.d := fun n => hconj n.1 n.2 γ
  let c : flagN B.d ≃ₜ* flagN B.d :=
    { toFun := fun n => ⟨δ⁻¹ * n.1 * δ, hmem n⟩
      invFun := fun n => ⟨δ * n.1 * δ⁻¹, hmem' n⟩
      left_inv := fun n => Subtype.ext (by simp [mul_assoc])
      right_inv := fun n => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hc : ∀ n, c n ∈ NFlagQ B.V B.d.e ↔ n ∈ NFlagQ B.V B.d.e := fun n => by
    change δ⁻¹ * (n : GA D B.V) * δ ∈ GQ B.V ↔ (n : GA D B.V) ∈ GQ B.V
    rw [Subgroup.mul_mem_cancel_right _ hδ, Subgroup.mul_mem_cancel_left _ (inv_mem hδ)]
  have hK : ∀ γ' ∈ NFlagQ B.V B.d.e, ∀ n : flagN B.d,
      besFun ψ 1 B.d B.o B.ζ φ f h (γ' * n) = besFun ψ 1 B.d B.o B.ζ φ f h n := fun γ' hγ' n => by
    have hγ'Q : (γ' : GA D B.V) ∈ GQ B.V := Subgroup.mem_subgroupOf.1 hγ'
    simp only [besFun, Subgroup.coe_mul]
    rw [psiBes_mul B.d ψ 1 _ γ'.2 n.2, hψrat _ _ hγ'Q, one_mul, mul_assoc (γ' : GA D B.V), hf _ hγ'Q]
  refine Eq.trans ?_ (GlobalTheory.Mem.TrueRecord.integral_aut _ u1 u2 u3 c hc _ hK)
  congr 1
  funext n
  change _ = besFun ψ 1 B.d B.o B.ζ φ f h ⟨δ⁻¹ * n.1 * δ, hmem n⟩
  simp only [besFun]
  have e1 : psiBes ψ B.d 1 (vecB B.o B.ζ) (δ⁻¹ * n.1 * δ) = psiBes ψ B.d 1 (vecB B.o B.ζ) n.1 := by
    have := hψconj n.1 γ⁻¹
    rwa [map_inv, inv_inv] at this
  have e2 : f (δ⁻¹ * n.1 * δ * embA B.d B.o h) = f (n.1 * embA B.d B.o (γ * h)) := by
    rw [map_mul, ← hδdef, mul_assoc, mul_assoc, hf _ (inv_mem hδ)]
  rw [e1, e2, hφ γ hγ h]

theorem map_mul_right {ρ : ℕ} (B : BesLev D ρ) (a : GA D B.A) : B.vA.μ.map (· * a) = B.vA.μ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  obtain ⟨K, hK, hcov⟩ := B.cpt
  exact Formalism.L2.SG.CovariantRepresentation.haar_map_mul_right_of_lattice B.vA.μ (GQ B.A) hK hcov a

theorem setIntegral_mul_right {ρ : ℕ} (B : BesLev D ρ) (G : GA D B.A → ℂ) (hG : ∀ γ ∈ GQ B.A, ∀ h, G (γ * h) = G h)
    (a : GA D B.A) : ∫ h in B.vA.𝓕, G (h * a) ∂B.vA.μ = ∫ h in B.vA.𝓕, G h ∂B.vA.μ := by
  obtain ⟨i1, i2, i3, i4, i5, i6, i7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B.A
  haveI := B.vA.haar
  have hmp : MeasurePreserving (· * a) B.vA.μ B.vA.μ := ⟨measurable_mul_const a, map_mul_right B a⟩
  have hmp' : MeasurePreserving (· * a⁻¹) B.vA.μ B.vA.μ := ⟨measurable_mul_const a⁻¹, map_mul_right B a⁻¹⟩
  rw [← hmp.setIntegral_image_emb (measurableEmbedding_mulRight a) G B.vA.𝓕, Set.image_mul_right]
  have hF : IsFundamentalDomain (GQ B.A) ((· * a⁻¹) ⁻¹' B.vA.𝓕) B.vA.μ :=
    B.vA.fund.preimage_of_equiv hmp'.quasiMeasurePreserving (e := id) Function.bijective_id
      fun g x => by simp [Subgroup.smul_def, smul_eq_mul, mul_assoc]
  exact (B.vA.fund.setIntegral_eq hF fun γ x => hG γ γ.2 x).symm

end GlobalTheory.Core.Mi.Shift

open GlobalTheory.Core.Mi.Shift in

theorem GlobalTheory.Core.Mi.per_rTrans : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (φ : GA D B.A → ℂ)
    (f : GA D B.V → ℂ) (a : GA D B.A), IsStdChar D ψ (-1) → IsContAut B.A φ → IsContAut B.V f →
    B.per ψ (rTrans a φ) (rTrans (embA B.d B.o a) f) = B.per ψ φ f := by
  intro D ψ ρ B φ f a hψ hφ hf
  have hshift : ∀ h, ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ (rTrans a φ) (rTrans (embA B.d B.o a) f) h n ∂B.vN.ν =
      ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f (h * a) n ∂B.vN.ν := fun h => by
    simp only [besFun, rTrans, map_mul, mul_assoc]
  unfold BesLev.per besPer
  simp_rw [hshift]
  exact setIntegral_mul_right B (fun h => ∫ n in B.vN.𝓝, besFun ψ 1 B.d B.o B.ζ φ f h n ∂B.vN.ν)
    (fun γ hγ h => inner_left B ψ hψ.1 φ f hφ.1 hf.1 hγ h) a

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStageFormsTwistedLevelLeFinerLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.FlatLevel

variable {D : D7}

theorem prod_diagonal_block_dets_eq_lower_block_det {κ : Type} [CommRing κ] {r t j n : ℕ} (hn : n = r + j * t) {g : GL (Fin n) κ}
    (hg : g ∈ blockTri (blkOf r t)) :
    ∏ c ∈ Finset.range j, dBlk (blkOf r t) (c + 1) g = dBlk (blk2 r) 1 g := by
  classical
  have hg2 : g ∈ blockTri (blk2 r) := blockTri_blkOf_le r t hg
  set M : Matrix (Fin n) (Fin n) κ := (g : Matrix (Fin n) (Fin n) κ) with hM
  have sq : ∀ (b : Fin n → ℕ) (c : ℕ), g ∈ blockTri b → ((dBlk b c g : κˣ) : κ) = (M.toSquareBlock b c).det := by
    intro b c h; rw [diag_block_det_val c h]; rfl
  have emp : ∀ (b : Fin n → ℕ) (c : ℕ), c ∉ Finset.univ.image b → (M.toSquareBlock b c).det = 1 := by
    intro b c hc
    haveI : IsEmpty {a : Fin n // b a = c} := ⟨fun a => hc (Finset.mem_image.2 ⟨a.1, Finset.mem_univ _, a.2⟩)⟩
    exact Matrix.det_isEmpty
  have hdet : ∀ (b : Fin n → ℕ) (N : ℕ), (∀ a, b a < N) → M.BlockTriangular b →
      M.det = ∏ c ∈ Finset.range N, (M.toSquareBlock b c).det := by
    intro b N hb hB
    rw [hB.det]
    refine Finset.prod_subset (fun c hc => ?_) (fun c _ hc => emp b c hc)
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hc
    exact Finset.mem_range.2 (hb a)
  have h1 := hdet (blkOf r t) (j + 1) (fun a => by
      unfold blkOf
      split_ifs with h
      · omega
      · have ha : a.val - r < j * t := by have := a.2; omega
        have ht : 0 < t := by
          rcases Nat.eq_zero_or_pos t with h0 | h0
          · simp [h0] at ha
          · exact h0
        have : (a.val - r) / t < j := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact ha)
        omega) hg
  have h2 := hdet (blk2 r) 2 (fun a => by unfold blk2; split_ifs <;> omega) hg2
  rw [Finset.prod_range_succ'] at h1
  rw [Finset.prod_range_succ', Finset.prod_range_one] at h2
  have h0 : (M.toSquareBlock (blkOf r t) 0).det = (M.toSquareBlock (blk2 r) 0).det := by
    rw [← Matrix.det_submatrix_equiv_self (Equiv.subtypeEquivRight (p := fun a : Fin n => blk2 r a = 0)
      (q := fun a : Fin n => blkOf r t a = 0) (fun a => by unfold blk2 blkOf; split_ifs <;> simp_all))]
    rfl
  have hu : IsUnit (M.toSquareBlock (blk2 r) 0).det := by rw [← sq _ 0 hg2]; exact Units.isUnit _
  apply Units.ext
  rw [Units.coe_prod, sq _ 1 hg2]
  rw [Finset.prod_congr rfl (fun c _ => sq _ (c + 1) hg)]
  rw [h0] at h1
  exact hu.mul_right_cancel (h1.symm.trans h2)

end GlobalTheory.FlatLevel

namespace GlobalTheory.FlatLevel

variable {D : D7}

theorem multT_le {V : HSp D} {S : D.what₂.Tau → SPar} (θ : InfFam D) (M : DSModel V S) {J J' : Set (GA D V)}
    {χ χ' : GA D V → ℂ} (h : ∀ k ∈ J', k ∈ J ∧ χ k = χ' k) : MultT θ M J χ ≤ MultT θ M J' χ' :=
  Submodule.map_mono (Submodule.span_mono fun X hX =>
    ⟨hX.aut, hX.cusp, fun v k hk g => (h k hk).2 ▸ hX.lev v k (h k hk).1 g, hX.equiv, hX.cont⟩)

open Classical in

theorem lev_flat_le (c : Com D) (w : Twist D) (hw : w.Is c) (j : ℕ) {n : ℕ} (hn : n = D.R.r + j * D.R.t)
    (J : Matrix (Fin n) (Fin n) D.host.E) (β : GL (Fin n) (Lev.EAf D)) (hr hr' : D.R.r ≤ n)
    (x : GL (Fin n) (Lev.EAf D))
    (hx : x ∈ lev D.sp.cm J β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B)) :
    x ∈ lev D.sp.cm J β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) ∧
      levFn β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B) x =
        levFn β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) x := by
  obtain ⟨hp, hP⟩ := mem_lev.1 hx
  obtain ⟨hUA, hSt, h3, -⟩ := mem_parLev.1 hp
  have h3' : ∀ PP ∈ c.Pg, redFn β PP x ∈ blockTri (blkOf D.R.r D.R.t) := h3
  have hP' : (fun PP : c.Pg => upperLeftBlock hr (redFn β PP.1 x)) ∈ c.P.H := hP
  have hone := (hw.grp _).1 hP'
  have hPg : ∀ PP ∈ w.Pg, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_left _ h
  have hQ : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => hw.union ▸ Finset.mem_union_right _ h
  refine ⟨mem_lev.2 ⟨mem_parLev.2 ⟨hUA, hSt, fun PP h => h3' PP (hPg PP h),
    fun PP h => blockTri_blkOf_le _ _ (h3' PP (hQ PP h))⟩, ?_⟩, ?_⟩
  · show _ ∈ (⊥ : Subgroup (G0 w.Pg D.R.r))
    refine Subgroup.mem_bot.2 (funext fun PP => ?_)
    exact hone ⟨PP.1, hPg PP.1 PP.2⟩ PP.2
  · unfold levFn
    have e1 : ext1 (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B).P.H
        (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B).P.chi
        (rTup β (Lev.datY n D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B) x) = 1 := by
      show ext1 c.P.H c.P.chi _ = 1
      unfold ext1
      split_ifs
      · rw [hw.chr]; rfl
      · rfl
    have e2 : ext1 (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B).P.H
        (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B).P.chi
        (rTup β (Lev.datY n D.R.r D.R.t j hr' w.Pg w.Q (LevelP.triv _ _ _) w.chi w.ξ Lev.Frm.B) x) = 1 := by
      show ext1 (LevelP.triv w.Pg D.R.r ℂ).H (LevelP.triv w.Pg D.R.r ℂ).chi _ = 1
      unfold ext1
      split_ifs
      · rfl
      · rfl
    rw [e1, e2]
    show 1 * (∏ PP ∈ c.Pg, ∏ c' ∈ Finset.range j, c.chi (c' + 1) PP (dBlk (blkOf D.R.r D.R.t) (c' + 1) (redFn β PP x))) *
        ∏ PP ∈ (∅ : Finset (Pl D.host.E)), (w.ξ PP)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn β PP x)) =
      1 * (∏ PP ∈ w.Pg, ∏ c' ∈ Finset.range j, w.chi (c' + 1) PP (dBlk (blkOf D.R.r D.R.t) (c' + 1) (redFn β PP x))) *
        ∏ PP ∈ w.Q, (w.ξ PP)⁻¹ (dBlk (blk2 D.R.r) 1 (redFn β PP x))
    rw [Finset.prod_empty, mul_one, one_mul, one_mul, hw.union, Finset.prod_union hw.disj]
    congr 1
    · refine Finset.prod_congr rfl fun PP hP => Finset.prod_congr rfl fun c' _ => ?_
      rw [hw.chiPg (c' + 1) PP hP]
    · refine Finset.prod_congr rfl fun PP hP => ?_
      simp_rw [hw.chiQ _ PP hP]
      rw [← map_prod, prod_diagonal_block_dets_eq_lower_block_det hn (h3' PP (hQ PP hP))]

open Classical in

theorem flatLe : ∀ D : D7, FlatLe D := by
  intro D c w hw j _ s hs hr
  obtain ⟨hr', hL, hflat⟩ := hs
  have hn : s.V.rank = D.R.r + j * D.R.t := hflat.rank
  show MultT c.θ s.M (levS s.V s.β s.L) (Lev.levChi s.V s.β s.L) ≤
    MultT c.θ s.M (levS s.V s.β (Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B))
      (Lev.levChi s.V s.β (Lev.datY s.V.rank D.R.r D.R.t j hr c.Pg ∅ c.P c.chi w.ξ Lev.Frm.B))
  rw [hL]
  refine multT_le c.θ s.M fun k hk => ?_
  obtain ⟨h1, h2⟩ := lev_flat_le c w hw j hn s.V.gram s.β hr hr' _ hk.2
  exact ⟨⟨hk.1, h1⟩, (congrArg (fun u : ℂˣ => (u : ℂ)) h2).symm⟩

end GlobalTheory.FlatLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainThetaLiftUpEqAdjointValue
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw

theorem upVal_of_span_adj : ∀ D : D7, SoftQ D → UpSpanQ D → UpAdjQ D → UpVal D := by
  intro D hSoft hSpan hAdj
  intro hgap c tw htw k hk s s' hs hs' p hp ipD ip ipD' ip' hM hM' φ v hv
  have hk' : k + 1 ≤ D.R.m := hk
  haveI : FiniteDimensional ℂ (s'.CC c) := (hSoft c tw htw (k + 1) hk' s' hs').1
  have hl : ∀ (u : s.CC c) (x : s'.CC c), (∀ y, ip' y x = ip (p.io y) u) → ∀ (y : s'.CC c), ∀ w ∈ s'.KF,
      s'.pet (PiLocalization₂.val y w) (p.up φ (PiLocalization₂.val u v)) = ip' y x * ipD (p.It φ w) v := by
    intro u x hx y w hw
    rw [hx y]
    exact (hAdj hgap c tw htw k hk s s' hs hs' p hp u y φ v hv w hw).trans (hM.schur _ _ _ _)
  have key : ∀ (u : s.CC c) (x : s'.CC c), (∀ y, ip' y x = ip (p.io y) u) → p.up φ (PiLocalization₂.val u v) ≠ 0 →
      x ≠ 0 ∧ ∃ w₁, IsAdjVec p ipD ipD' φ v w₁ ∧ p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₁ := by
    intro u x hx hF
    obtain ⟨hx0, w₁, hw₁, hFx⟩ := GlobalTheory.ChainOnto.value_of_adjoint_of_mem_span (GA D s'.V) (SmT s'.M) (s'.CC c)
      (s'.CC c).subtype s'.KF ipD' ip' s'.pet hM'.hermD hM'.posD hM'.herm hM'.pos
      (fun y w n ys ws => pet_val_sum hM' y w n ys ws) x (p.up φ (PiLocalization₂.val u v)) (fun w => ipD (p.It φ w) v)
      (hSpan hgap c tw htw k hk s s' hs hs' p hp u φ v hv) (hl u x hx) hF
    have hFx' : p.up φ (PiLocalization₂.val u v) = PiLocalization₂.val x w₁ := hFx
    refine ⟨hx0, w₁, ⟨hw₁, fun w hw => ?_⟩, hFx'⟩
    have h1 := hl u x hx x w hw
    rw [hFx'] at h1
    have h2 := (hM'.schur x x w w₁).symm.trans h1
    have hxx : ip' x x ≠ 0 := fun h => by
      have := hM'.pos x hx0
      rw [h] at this
      simp at this
    exact mul_left_cancel₀ hxx h2
  refine ⟨fun ⟨u, hF⟩ => ?_, fun w₀ hw₀ u x hx => ?_⟩
  · obtain ⟨x, hx, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique (s.CC c) (s'.CC c) ip ip' hM'.herm hM'.pos p.io u
    obtain ⟨-, w₁, hw₁, hFx⟩ := key u x hx hF
    refine ⟨w₁, fun h => hF ?_, hw₁⟩
    rw [hFx, h]
    simp
  · by_cases hF : p.up φ (PiLocalization₂.val u v) = 0
    · have h1 := hl u x hx x w₀ hw₀.1
      rw [hF, ← hw₀.2 w₀ hw₀.1] at h1
      have h0 : s'.pet (PiLocalization₂.val x w₀) (0 : GA D s'.V → ℂ) = 0 := by
        simp [PiLocalization₂.pet, Lift.pet]
      rw [h0] at h1
      rw [hF]
      rcases mul_eq_zero.mp h1.symm with h | h
      · have hx0 : x = 0 := by
          by_contra hne
          have := hM'.pos x hne
          rw [h] at this
          simp at this
        subst hx0
        first | rfl | simp [PiLocalization₂.val]
      · have hw0 : w₀ = 0 := by
          by_contra hne
          have := hM'.posD w₀ hne
          rw [h] at this
          simp at this
        subst hw0
        simp
    · obtain ⟨-, w₁, hw₁, hFx⟩ := key u x hx hF
      have hd : w₁ = w₀ := by
        by_contra hne
        have hdK : w₁ - w₀ ∈ s'.KF := s'.KF.sub_mem hw₁.1 hw₀.1
        have hz : ipD' (w₁ - w₀) (w₁ - w₀) = 0 := by
          rw [map_sub, hw₁.2 _ hdK, hw₀.2 _ hdK, sub_self]
        have := hM'.posD _ (sub_ne_zero.mpr hne)
        rw [hz] at this
        simp at this
      rw [hFx, hd]

end GlobalTheory.ChainTw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletedHomLatticeStableSplitIdempotent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SplitVac

open GlobalTheory.LatVac NumberField

variable {D : D7}

def finIncl (D : D7) : (Af D.host.F ⊗[D.host.F] D.host.E) →ₗ[D.host.F] AE D :=
  (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)).rTensor D.host.E

theorem finIncl_tmul (β : Af D.host.F) (x : D.host.E) :
    finIncl D (β ⊗ₜ[D.host.F] x) = pairA D.host.F 0 β ⊗ₜ[D.host.F] x := rfl

theorem infPart_finIncl (y : Af D.host.F ⊗[D.host.F] D.host.E) : infPart D (finIncl D y) = 0 := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul β x => rw [finIncl_tmul]; exact infPart_pair β x
  | add y z hy hz => rw [LinearMap.map_add, RingHom.map_add, hy, hz, add_zero]

theorem finPart_finIncl (y : Af D.host.F ⊗[D.host.F] D.host.E) : finPart D (finIncl D y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul β x => rw [finIncl_tmul]; exact finPart_pair β x
  | add y z hy hz => rw [LinearMap.map_add, RingHom.map_add, hy, hz]

theorem eq_finIncl {z : AE D} (hz : infPart D z = 0) : z = finIncl D (finPart D z) := by
  rw [← sub_eq_zero]
  apply eq_zero_of_parts
  · rw [RingHom.map_sub, hz, infPart_finIncl, sub_zero]
  · rw [RingHom.map_sub, finPart_finIncl, sub_self]

theorem finIncl_mul_mem {S T : HSp D} (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (v : GlobalTheory.FinPl.Pl D)
    {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (hsupp : ∀ w, ¬ w = v → evalV D.host.F w α = 0)
    {a : D.host.E} (ha : a ∈ D.host.AA) {s : Fin S.rank → D.host.E} (hs : s ∈ LS)
    {t : Fin T.rank → D.host.E} (ht : t ∈ LT) {y : Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    (Matrix.of fun i j => finIncl D y *
      (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) : WO S T) ∈
      latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = v) := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨β, hβ, x, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨β * α, mul_mem_intAf hβ hα, fun w hw => ?_, a, ha, s, hs, x • t,
      LT.smul_mem x ht, ?_⟩
    · rw [map_mul, hsupp w hw, mul_zero]
    · ext i j
      simp only [Matrix.of_apply, finIncl_tmul, Algebra.TensorProduct.tmul_mul_tmul, pair_mul]
      congr 1
      change (x : D.host.E) * (a * t i * _) = a * ((x : D.host.E) * t i) * _
      ring
  | zero =>
    convert (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = v)).zero_mem using 1
    ext i j; simp
  | add y z _ _ hy hz =>
    convert add_mem hy hz using 1
    ext i j; simp only [Matrix.of_apply, Matrix.add_apply, LinearMap.map_add, add_mul]
  | neg y _ hy =>
    convert neg_mem hy using 1
    ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, LinearMap.map_neg, neg_mul]

theorem idem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (u : WO S T), u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → (Matrix.of fun i j => q.e * u i j : WO S T) ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) ∧ ∀ i j, (q.e + cA D q.e) * u i j = u i j := by
  intro D k _ _ _ _ q S T LS LT u hu
  obtain ⟨ε, ⟨α₀, rfl, h1, h0⟩, hε⟩ := q.above
  have hee : q.e * q.e = q.e := q.split.1
  have hec : q.e * cA D q.e = 0 := q.split.2.1
  have hεinf : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α₀)) = 0 := infPart_pair α₀ 1
  have hinf : infPart D q.e = 0 := by
    have : q.e = q.e * (q.e + cA D q.e) := by rw [mul_add, hee, hec, add_zero]
    rw [this, RingHom.map_mul, hε, hεinf, mul_zero]
  have hfin : finPart D q.e ∈ intAE D := by
    have h := q.sec_pr 1
    rw [map_one, mul_one] at h
    rw [← h]
    exact (q.int_iff 1).1 (one_mem _)
  have he := eq_finIncl hinf
  refine ⟨?_, ?_⟩
  · induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      have h := finIncl_mul_mem LS LT q.v hα hsupp ha hs ht hfin
      rw [← he] at h
      simpa only [Matrix.of_apply] using h
    | zero =>
      convert (latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v)).zero_mem using 1
      ext i j; simp
    | add x y _ _ hx hy =>
      convert add_mem hx hy using 1
      ext i j; simp only [Matrix.of_apply, Matrix.add_apply, mul_add]
    | neg x _ hx =>
      convert neg_mem hx using 1
      ext i j; simp only [Matrix.of_apply, Matrix.neg_apply, mul_neg]
  · induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, hα, hsupp, a, ha, s, hs, t, ht, rfl⟩ := hw
      intro i j
      have hmul : α₀ * α = α := by
        apply RestrictedProduct.ext
        intro w
        change evalV D.host.F w (α₀ * α) = evalV D.host.F w α
        rw [map_mul]
        by_cases hw : w = q.v
        · subst hw; rw [h1, one_mul]
        · rw [hsupp w hw, mul_zero]
      rw [hε, Matrix.of_apply]
      change (pairA D.host.F 0 α₀ ⊗ₜ[D.host.F] (1 : D.host.E)) * _ = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, pair_mul, hmul]
    | zero => intro i j; simp
    | add x y _ _ hx hy => intro i j; rw [Matrix.add_apply, mul_add, hx, hy]
    | neg x _ hx => intro i j; rw [Matrix.neg_apply, mul_neg, hx]

end GlobalTheory.SplitVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletionMatrixBoundedRationalAutIntegralStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completionMatrix_boundedRationalAut_integral : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (ϖ : kˣ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs →
    GlobalTheory.SymBridge.IsCompl P (qOf P) ι ϖ → ∀ (j c : ℕ) (a : AutY X R j) (g : GL (XIx (Fin R.k) (Fin R.t) j ⊕ Fin c) k),
    IsGL ι a g →
    (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, a⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ j) • a x ∈ lamYat (Pr := Pr) (R := R) j P) →
    IntM (g⁻¹ : GL _ k).val ∧ IntM ((ϖ : k) ^ j • g.val) := by
  first | exact @GlobalTheory.TwBridge.isGL_int_of_bdd | exact GlobalTheory.TwBridge.isGL_int_of_bdd | (intros; apply GlobalTheory.TwBridge.isGL_int_of_bdd <;> assumption)
end

