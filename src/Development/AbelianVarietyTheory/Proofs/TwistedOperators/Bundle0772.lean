import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0648
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0768
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1145
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0962
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0056
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0008
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0011
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SqrtDivMulEqSqrtMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0484
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0765
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0683
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseFrameOfRealizationModels
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.IsThetaFunOPull
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0767
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0478
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0749
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionFixedByKplus
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenLevelGroupSubgroupOf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.MovedVacRoot

private theorem mem_Qbar_of_pow {c : ℂ} {m : ℕ} (hm : 0 < m) (h : c ^ m = 1) : c ∈ Qbar :=
  mem_algebraicClosure_iff'.2 (IsIntegral.of_pow hm (h ▸ isIntegral_one))

private theorem norm_map_of_pow {K : Type} [NormedField K] (σ : Qbar →+* K) {c : ℂ} {m : ℕ} (hm : 0 < m) (h : c ^ m = 1)
    (hc : c ∈ Qbar) : ‖σ ⟨c, hc⟩‖ = 1 := by
  have e : (⟨c, hc⟩ : Qbar) ^ m = 1 := Subtype.ext h
  have e' : ‖σ ⟨c, hc⟩‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, e, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e'

private theorem isOpen_levelGroup_subgroupOf {D : D7} (T : HSp D) {N : ℕ} (hN : 0 < N) :
    IsOpen (((GlobalTheory.Member.PrincLevel.levelGroup T N).subgroupOf (GfC T) : Subgroup (GfC T)) : Set (GfC T)) := by
  let F : GfC T → Formalism.IndefR.Bridge.Gf T := fun x => (finHom T).rangeRestrict x.1
  have hG : Continuous fun x : GfC T => (finHom T x.1 : GL (Fin T.rank) (Formalism.L2.Herm.Af D.host.F ⊗[D.host.F] D.host.E)) := by
    refine Units.continuous_iff.2 ⟨(GlobalTheory.Member.continuous_finHom_val D T).comp continuous_subtype_val, ?_⟩
    have h := ((GlobalTheory.Member.continuous_finHom_val D T).comp continuous_inv).comp
      (continuous_subtype_val (p := fun x => x ∈ GfC T))
    refine h.congr fun x => ?_
    simp [Function.comp_def, map_inv]
  have hF : Continuous F := hG.subtype_mk _
  have e : (((GlobalTheory.Member.PrincLevel.levelGroup T N).subgroupOf (GfC T) : Subgroup (GfC T)) : Set (GfC T)) =
      F ⁻¹' (((GlobalTheory.Member.PrincLevel.levelGroup T N).map (finHom T).rangeRestrict : Subgroup (Formalism.IndefR.Bridge.Gf T)) :
        Set (Formalism.IndefR.Bridge.Gf T)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    constructor
    · intro hx
      exact Subgroup.mem_map.2 ⟨x.1, hx, rfl⟩
    · intro hx
      obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hx
      have e' : finHom T k' = finHom T x.1 := congrArg Subtype.val e
      refine ⟨x.2, ?_⟩
      have hc := hk'.2
      unfold GlobalTheory.Member.FinCong at hc ⊢
      rw [← e']
      exact hc
  rw [e]
  exact (GlobalTheory.SmoothVac.isOpen_map_levelGroup T hN).preimage hF

private theorem exists_pow_mem {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K U : Subgroup G)
    (hKH : K ≤ H) (hK : IsCompact (K : Set G)) (hU : IsOpen ((U.subgroupOf H : Subgroup H) : Set H)) {k : G} (hk : k ∈ K) :
    ∃ m : ℕ, 0 < m ∧ k ^ m ∈ U := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := by
    have hc : Continuous (Subgroup.inclusion hKH) := continuous_inclusion hKH
    exact hU.preimage hc
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  obtain ⟨m, hm, -, h⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (H := U.subgroupOf K) Subgroup.index_ne_zero_of_finite ⟨k, hk⟩
  exact ⟨m, hm, h⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

private theorem exists_pow_level {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : Submodule.IsLattice D.host.E Λ) {k : GA D V} (hk : k ∈ GfC V)
    (hfix : Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE V k) Λ = Λ) {N : ℕ} (hN : 0 < N) :
    ∃ m : ℕ, 0 < m ∧ k ^ m ∈ GlobalTheory.Member.PrincLevel.levelGroup V N := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ Λ hΛ
  have key := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds D.host.F D.host.E (Fin V.rank) Λ
    (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top (Formalism.IndefR.Lev.finE V k)
  rw [hfix] at key
  have key' : ∀ u, u ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      Matrix.mulVec ((Formalism.IndefR.Lev.finE V k)⁻¹).1 u ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := key
  have hst : Formalism.IndefR.Lev.finE V k ∈ Formalism.L2.DIV.St β := by
    refine (GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).2 ⟨fun y hy => (key' _).2 ?_, fun y hy => (key' y).1 hy⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact hy
  exact exists_pow_mem (GfC V) (Formalism.IndefR.Lev.levA V (Formalism.L2.DIV.St β)) _ inf_le_left
    (GlobalTheory.AscInh.stab_compact_open V β).1 (isOpen_levelGroup_subgroupOf V hN) ⟨hk, hst⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

private theorem exists_root {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) {k : GA D S} {k' : GA D T} (hk : k ∈ GfC S) (hk' : k' ∈ GfC T)
    (h1 : Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE S k) ΛS = ΛS)
    (h2 : Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE T k') ΛT = ΛT)
    (hf' : IsVacO ψ θ S T sS sT ΛS ΛT (om (k, k') f)) :
    ∃ (c : ℂ) (m : ℕ), 0 < m ∧ c ^ m = 1 ∧ om (k, k') f = c • f := by
  obtain ⟨c, hc⟩ := GlobalTheory.LevelVac.vac_eq_smul hS hT hΛS hΛT hf hf'
  obtain ⟨α, hα⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ ΛS hΛS.1
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ ΛT hΛT.1
  obtain ⟨N, hN, hfix⟩ := GlobalTheory.LevelVac.exists_level_fix hW hS hT hΛS hΛT hα hβ hf
  obtain ⟨a, ha, hka⟩ := exists_pow_level S ΛS hΛS.1 hk h1 hN
  obtain ⟨b, hb, hkb⟩ := exists_pow_level T ΛT hΛT.1 hk' h2 hN
  have e1 : k ^ (a * b) ∈ GlobalTheory.Member.PrincLevel.levelGroup S N := by
    rw [pow_mul]; exact pow_mem hka b
  have e2 : k' ^ (a * b) ∈ GlobalTheory.Member.PrincLevel.levelGroup T N := by
    rw [pow_mul']; exact pow_mem hkb a
  have e3 := hfix _ e1.1 _ e2.1 e1.2 e2.2
  have e4 : om (k ^ (a * b), k' ^ (a * b)) f = c ^ (a * b) • f := GlobalTheory.LevelVac.om_pow_eq om (k, k') f c hc (a * b)
  obtain ⟨w, hw⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hf
  refine ⟨c, a * b, mul_pos ha hb, ?_, hc⟩
  have e5 := congrFun (e4.symm.trans e3) w
  rw [Pi.smul_apply, smul_eq_mul] at e5
  exact mul_right_cancel₀ hw (e5.trans (one_mul _).symm)

private theorem inV_std {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E) :
    inV B (stdL D n) = (colLat B : Set (Fin n → D.host.E)) := by
  ext y
  simp only [inV, Set.mem_image, SetLike.mem_coe]
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : ∀ i, ∃ c : 𝓞 D.host.E, algebraMap _ D.host.E c = z i := fun i =>
      Submodule.mem_one.1 (hz i (Set.mem_univ i))
    choose c hc using hz'
    refine ⟨c, funext fun a => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, hc, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => algebraMap _ D.host.E (c j), fun i _ => Submodule.mem_one.2 ⟨c i, rfl⟩, funext fun a => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in

private theorem moved_root (hP : GlobalTheory.FunPr.Hypotheses₂) (hI : ∀ D, GlobalTheory.NormSum.Inp D) {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R) (hch : ch.Is) (p : Pair T) (hp : DefPair D.R.m p) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big)
    (hx : GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x = stdL D _)
    (hy : GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y = stdL D _) :
    ∃ (c : ℂ) (m : ℕ), 0 < m ∧ c ^ m = 1 ∧
      ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small))
        ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p) = c • ch.S.Z.vac p := by
  have hn := DefPair.nodes hp
  obtain ⟨h1, h2⟩ := DefPair.nodes hp
  have hom := ch.W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have negMem : ∀ (V : HSp D) {g : Formalism.L2.Theta.GA D V}, g ∈ GfC V → negGA V g ∈ GfC (negSp V) := by
    intro V g hg
    have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
    simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
    rw [e]
    exact hg
  have hvac := GlobalTheory.MovedDict.movedVac_isVacO hP hI ch hch p hp x y
  have hv := ch.S.Z.vac_is p hp
  have gx := GlobalTheory.MovedHomLat.movedLat_eq ch.S.toGridChoice _ h1 x
  have gy := GlobalTheory.MovedHomLat.movedLat_eq ch.S.toGridChoice _ h2 y
  have ix : inV (ch.S.N.fr p.small) (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) = (colLat (ch.S.N.fr p.small) : Set _) := by
    rw [hx, inV_std]
  have iy : inV (ch.S.N.fr p.big) (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) = (colLat (ch.S.N.fr p.big) : Set _) := by
    rw [hy, inV_std]
  have fx := SetLike.coe_injective (gx.symm.trans ix)
  have fy := SetLike.coe_injective (gy.symm.trans iy)
  cases p with
  | chi i j =>
    rw [show inV (frS ch.S.N (.chi i j)) (srcLat ch.S.toGridChoice (.chi i j) x y) = _ from iy,
      show inV (frT ch.S.N (.chi i j)) (tgtLat ch.S.toGridChoice (.chi i j) x y) = _ from ix] at hvac
    exact exists_root hom (fun τ => isCartanInv_neg (ch.W.cart_is _ h2.inRange τ)) (fun τ => ch.W.cart_is _ h1.inRange τ)
      (isSelfDualC_neg (ch.S.N.selfDual h2)) (ch.S.N.selfDual h1) hv (negMem _ (y * ch.S.N.u _).2) (x * ch.S.N.u _).2
      fy fx hvac
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    rw [show inV (frS ch.S.N (.top t j)) (srcLat ch.S.toGridChoice (.top t j) x y) = _ from ix,
      show inV (frT ch.S.N (.top t j)) (tgtLat ch.S.toGridChoice (.top t j) x y) = _ from iy] at hvac
    exact exists_root hom (fun τ => ch.W.cart_is _ h1.inRange τ) (fun τ => ch.W.cart_is _ h2.inRange τ)
      (ch.S.N.selfDual h1) (ch.S.N.selfDual h2) hv (x * ch.S.N.u _).2 (y * ch.S.N.u _).2
      fx fy hvac

end GlobalTheory.MovedVacRoot

end

open GlobalTheory.MovedVacRoot in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_lattice_size_sum : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x = stdL D _ → GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y = stdL D _ →
    ∃ κ : ℂ, Mod1All κ ∧ (∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.UnitAt q κ) ∧ GlobalTheory.MovedKappaEx.JetKap ch p x y κ := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y hx hy
  obtain ⟨c, m, hm, h1, hc⟩ := moved_root hP hI ch hch p hp x y hx hy
  have h2 : (opp p c) ^ m = 1 := by rw [← map_pow, h1, map_one]
  have h3 := mem_Qbar_of_pow hm h2
  refine ⟨opp p c, ⟨h3, fun σ => norm_map_of_pow σ hm h2 h3⟩, fun q _ lam => ?_, fun k => ?_⟩
  · rw [lamC, dif_pos h3]
    exact norm_map_of_pow lam hm h2 h3
  · have hs : srcLat ch.S.toGridChoice p x y = stdL D _ := by
      cases p
      exacts [hy, hx, hy, hx]
    have ht : tgtLat ch.S.toGridChoice p x y = stdL D _ := by
      cases p
      exacts [hx, hy, hx, hy]
    have hoo : opp p (opp p c) = c := by
      cases p <;> simp [opp]
    have he0 := ch.S.Z.e0_is p hp
    have hK : KLat D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) (ch.G.pS p).rank (ch.G.pT p).rank) :=
      Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D _, GlobalTheory.NormSum.VacInt.sd_std D _, rfl⟩
    obtain ⟨-, -, hself, -⟩ := GlobalTheory.ThetaTriple.klat_triples D D.host.ccK ch.S.Z.δ ch.S.Z.crv (ch.G.pS p).rank (ch.G.pT p).rank
    have hI0 : Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
        (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (srcLat ch.S.toGridChoice p x y) (tgtLat ch.S.toGridChoice p x y))
        (ch.S.Z.e0 p) = ch.S.Z.e0 p := by
      rw [hs, ht]
      exact hself _ hK _ he0.1
    have hd : Differentiable ℂ (ch.S.Z.e0 p) := he0.1.1
    have h0 := ch.S.Z.kernelNorm_constant_spec p hp k
    rw [hI0, GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd, hc]
    unfold fockIn at h0 ⊢
    rw [Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, Pi.smul_apply, h0, smul_eq_mul]
    simp only [map_mul, hoo]
    ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MapIncAMulRealPt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.L2.NTheta (IsIdemAt)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.FrameChangeRead

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.FD Formalism.IndefR.Datum

variable {D : D7}

theorem map_incA_mul_realPt (S T : HSp D) (M : Matrix (Fin T.rank) (Fin T.rank) D.host.E)
    (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    HMul.hMul (M.map (incA D)) (realPt S T X : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = realPt S T (M * X) := by
  ext a c
  simp only [realPt, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply, incA, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR,
    AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, TensorProduct.tmul_sum]

theorem exists_frAt {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (hM : R.IsModels) (ht : TieIn T R κ v₀) (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hσ : σ = T.σ₀)
    (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (h : GA D (Wc D i)) :
    ∃ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (dictW T i σ hV) γ h := by
  have e : res T (sg0 D A) = T.σ₀ := by
    rw [show sg0 D A = D.what₂.embLL from sgAt_mk _ R.hv0]
    exact res_embLL T ht.alg ht.laws.pins.2.2.1
  have hg : GoodEmb T.Q.c (res T (sg0 D A)) := e ▸ T.toCore.good_σ₀
  obtain rfl : σ = res T (sg0 D A) := hσ.trans e.symm
  obtain ⟨γ, h1, h2, -⟩ := (GlobalTheory.HolDict.BaseFrame.baseFrT_of_tieIn D G Pl0 T0 A T R κ v₀ hM ht i _ hg hV).2.2 h
  exact ⟨γ, h1, h2⟩

theorem frame_change : ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws → GlobalTheory.IndefiniteRowSideFullHecke.SplitLinearModelNorm.SplitLinearModel D → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.VacFixed D →
    ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
    ∀ (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (α : GA D (Wc D i)) (Rc : Finset (GA D (Wc D i))),
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsUnitaryHeckeOperatorSplitPrimeData T R i P p k α Rc →
    ∀ (h : GA D (Wc D i))
      (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom),
    ∀ (ph : ℂ) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E), ‖ph‖ = 1 → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b →
      (∀ (h : GA D (Wc D i)), ∀ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ h →
      ∀ (hx : (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2 ∈ ((T.U ((i : ℕ) + 1) σ).X (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1).dom)
        (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt)
        (X : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (z : Fin (Vc D i).rank → Fin Wt.g → ℂ),
        (∀ a, z a = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, X (Fin.cast (rank_Wc i).symm m) n * b n a) →
        Complex.exp (Real.pi / 2 * ∑ a, hermForm Y.Hm (z a) (z a)) *
            GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) X) =
          ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ a, Y.θ (z a)) →
    ∀ γ' ∈ GQ (Wc D i),
    ∃ γ ∈ GQ (Wc D i), FrAt (R.MW i (sg0 D A)) R.θ (rank_Wc i) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV) γ h ∧
      ∃ M : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E, Formalism.L2.Theta.mt (Wc D i) (γ * γ'⁻¹) = M.map (Formalism.L2.Theta.incA D) ∧
      ∃ (Wt : UnfAt (T.U ((i : ℕ) + 1) σ) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 ⟨(GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).2, hx⟩) (Y : UnitAt Wt),
        ∀ (Z : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E) (w : Fin (Vc D i).rank → Fin Wt.g → ℂ),
          (∀ c, w c = GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.perVec Wt fun m => ∑ n, (M * Z) (Fin.cast (rank_Wc i).symm m) n * b n c) →
          GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ' * h) (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Z) =
            ph * (T.cE ((i : ℕ) + 1) σ (GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.dictW T i σ hV h).1 * castDict hV (T.mu ((i : ℕ) + 1) σ) h) * ∏ c, (Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (w c) (w c))) * Y.θ (w c)) := by
  intro D hHk hSL hVF G _ _ Pl0 T0 A T _ R F κ v₀ hLev hGrp hFam hMod hThP hTie i σ hσ hV P p k α Rc hS h hx
    ph b hph hbON hpin γ' hγ'
  obtain ⟨γ, hγ, hfr⟩ := exists_frAt hMod hTie i σ hσ hV h
  obtain ⟨M, hM⟩ := Formalism.IndefR.Eqv.mt_GQ _ (mul_mem hγ (inv_mem hγ'))
  obtain ⟨_, Wt, ⟨Y⟩⟩ := exists_witness T i σ hV hTie.laws.toLawsM (hσ ▸ T.toCore.good_σ₀) h
  refine ⟨γ, hγ, hfr, M, hM, Wt, Y, fun Z w hw => ?_⟩
  have hω := hThP.ωP i A.μ0
  have hv : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := (hThP.vP i A.μ0).1.2.theta
  have key : thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ' * h) (realPt (Vc D i) (Wc D i) Z) =
      thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (realPt (Vc D i) (Wc D i) (M * Z)) := by
    rw [thetaAt_eq, thetaAt_eq]
    have e : ((1 : GA D (Vc D i)), γ' * h) = (1, (γ * γ'⁻¹)⁻¹) * (1, γ * h) := by
      simp [mul_assoc]
    rw [e, map_mul, Module.End.mul_apply,
      GlobalTheory.RawLift.Move.om_rat_inv_apply hω (mul_mem hγ (inv_mem hγ')) (hω.om_pres _ _ hv),
      GlobalTheory.RawLift.Move.actO_one_left, hM, map_incA_mul_realPt]
  have h1 := hpin h γ hγ hfr hx Wt Y (M * Z) w hw
  rw [key]
  have h3 : Complex.exp (Real.pi / 2 * ∑ c, hermForm Y.Hm (w c) (w c)) *
      ∏ c, Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (w c) (w c))) = 1 := by
    rw [← Complex.exp_sum, ← Complex.exp_add, Finset.sum_neg_distrib, Finset.mul_sum, add_neg_cancel, Complex.exp_zero]
  rw [Finset.prod_mul_distrib]
  linear_combination (∏ c, Complex.exp (-(Real.pi / 2 * hermForm Y.Hm (w c) (w c)))) * h1 -
    thetaAt R.ψ (R.ωP i A.μ0) (R.vacP i) (γ * h) (realPt (Vc D i) (Wc D i) (M * Z)) * h3

end GlobalTheory.FrameChangeRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSixth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspTypeApproxX

theorem norm_sub_sum_sigma_lt {E : Type*} [SeminormedAddCommGroup E] {m : ℕ} (I : E) (L : Fin m → E) (n : Fin m → ℕ)
    (J : ∀ k, Fin (n k) → E) {δ : ℝ} (hδ : 0 < δ) (h1 : ‖I - ∑ k, L k‖ < δ / 2)
    (h2 : ∀ k, ‖L k - ∑ j, J k j‖ < δ / (2 * (m + 1))) :
    ‖I - ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2‖ < δ := by
  have hs : ∑ l : Fin (∑ k, n k), J (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2 = ∑ k, ∑ j, J k j := by
    rw [Equiv.sum_comp finSigmaFinEquiv.symm (fun x => J x.1 x.2), Fintype.sum_sigma]
  have hd : I - ∑ k, ∑ j, J k j = (I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j) := by
    rw [Finset.sum_sub_distrib]; abel
  rw [hs, hd]
  have h3 : ‖∑ k, (L k - ∑ j, J k j)‖ ≤ m * (δ / (2 * (m + 1))) := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ k, ‖L k - ∑ j, J k j‖ ≤ ∑ _k : Fin m, δ / (2 * (m + 1)) := Finset.sum_le_sum fun k _ => (h2 k).le
      _ = m * (δ / (2 * (m + 1))) := by simp
  have h4 : (m : ℝ) * (δ / (2 * (m + 1))) ≤ δ / 2 := by
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  calc ‖(I - ∑ k, L k) + ∑ k, (L k - ∑ j, J k j)‖ ≤ ‖I - ∑ k, L k‖ + ‖∑ k, (L k - ∑ j, J k j)‖ := norm_add_le _ _
    _ < δ / 2 + δ / 2 := by linarith
    _ = δ := by ring

theorem lift_approx_fock : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ C : Set (GA D (G.V (i + 1) j).V), IsCompact C → ∀ δ : ℝ, 0 < δ → ∃ (n : ℕ) (f : Fin n → (WO (G.V (i + 1) j).V (G.V i j).V → ℂ)) (p : Fin n → GlobalTheory.Grid.Pol (G.V (i + 1) j) (G.V i j)) (F : Fin n → (G.V i j).Maps) (v : Fin n → SmT (G.V i j).M), (∀ l, GlobalTheory.Grid.IsFinVec R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l)) ∧ (∀ l, F l ∈ (G.V i j).Cusp R.θ) ∧ ∀ h ∈ C, ‖(∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) - ∑ l, ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f l) (p l)) * F l (v l) g ∂(G.meas t i j).ν‖ < δ := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC δ hδ
  obtain ⟨m, F, v, hF, hFi, hA⟩ := GlobalTheory.T.theta_lift_vertical_cuspidal_grid hL hP D hS G₀ Pl0 T A Ks R G hRB hG t i j hi hj Φ hΦ φ hφ hint C hC (δ / 2) (by positivity)
  have hB := fun k : Fin m => GlobalTheory.T.theta_lift_vertical_cuspidal_type hL hP D hS G₀ Pl0 T A Ks R G hRB hG t i j hi hj Φ hΦ (F k) (hF k) (v k) (hFi k) C hC
    (δ / (2 * (m + 1))) (by positivity)
  choose n f p hf hBk using hB
  refine ⟨∑ k, n k, fun l => f (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2,
    fun l => p (finSigmaFinEquiv.symm l).1 (finSigmaFinEquiv.symm l).2, fun l => F (finSigmaFinEquiv.symm l).1,
    fun l => v (finSigmaFinEquiv.symm l).1, fun l => hf _ _, fun l => hF _, fun h hh => ?_⟩
  exact norm_sub_sum_sigma_lt (J := fun k q => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g
      (GlobalTheory.Grid.fock R.ψ R.θ true (G.V (i + 1) j) (G.V i j) (f k q) (p k q)) * F k (v k) g ∂(G.meas t i j).ν) _ _ _ hδ
    (hA h hh) fun k => hBk k h hh

end GlobalTheory.CuspTypeApproxX
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PsiEAtS0ColumnPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.CharXFB

noncomputable section
namespace GlobalTheory.CharXFB.HeisenbergPairBadPlaces

theorem traceCharacter_trivial_heisenbergPair_at_badPlaces : All fun {D} _ _ {sc} {G} W _ => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (u : WO (G.V (.grid (2 * σ + 2 + 1) 0)) (G.V (.grid (2 * σ + 2) 0))), u ∈ latRow G (2 * σ + 2) → ∀ (p : Fin (σ + 1)) (v : GlobalTheory.FinPl.Pl D), v ∈ G.pl.S0 → psiE W.ψ (GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * hA _ (ratV fun k => (G.colDec (2 * σ + 2) (by omega) h').a k (Fin.castLE (by omega) p)) (u *ᵥ ratV fun k => (G.colDec (2 * (σ + 1) + 1) (by omega) (by omega)).a k (Fin.castLE (by omega) p : Fin (2 * (σ + 1) + 1 - 1)).rev))) = 1 := by
  intro D hQ T L μ0 hL sc G W M hM σ h h' u hu p v hv
  have hb := GlobalTheory.T.lattice_scaling_at_S0 D hQ T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) u hu v hv
  have hC := GlobalTheory.T.thetaGrid_pairingBound_mem_completion_of_mapBound G σ h h' u v hb p
  generalize hA _ _ _ = x at hC ⊢
  obtain ⟨-, -, h3, -, h5, -⟩ := GlobalTheory.SeeSaw.idV_props D W.ψ W.ψ_std v
  have hε : GlobalTheory.FinPlLoc.idem D (· = v) ∈ idAt D (· = v) := GlobalTheory.FinPlLoc.idem_mem_idAt _
  have hs : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) ∈ idAt D (· = v) := Ideal.mul_mem_right _ _ hε
  have hx0 : D.host.xi0 ≠ 0 := cmHost_imaginaryGenerator_ne_zero
  have hdI : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) ∈ GlobalTheory.SeeSaw.idV (GlobalTheory.SeeSaw.dI D) v := by
    have e : GlobalTheory.SeeSaw.dI D = FractionalIdeal.spanSingleton _ D.host.xi0 * (D.host.AA * D.host.AAbar) := by
      unfold GlobalTheory.SeeSaw.dI; rw [mul_assoc]
    rw [e, h3 _ _ hx0]
    refine ⟨?_, hs⟩
    have e1 : incA D D.host.xi0⁻¹ * incA D D.host.xi0 = 1 := by rw [← map_mul, inv_mul_cancel₀ hx0, map_one]
    convert hC using 1
    linear_combination (GlobalTheory.FinPlLoc.idem D (· = v) * x) * e1
  have h6 := (h5 _ hs).1 hdI _ (GlobalTheory.FinPlLoc.idem_mem_intAt _)
  have e2 : GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) * GlobalTheory.FinPlLoc.idem D (· = v) =
      GlobalTheory.FinPlLoc.idem D (· = v) * (incA D D.host.xi0 * x) := by
    rw [mul_comm, ← mul_assoc, GlobalTheory.FinPlLoc.idem_mul_self]
  rwa [e2] at h6

end GlobalTheory.CharXFB.HeisenbergPairBadPlaces
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSquareIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seesaw_unfolding_square_integral : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.KInf D.sp.cm.sig Γ.W Bs.emb, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, om (1, k) ΦD ∈ algD Γ.M Bs.ψ Bs.emb := by
  first | exact @GlobalTheory.SquareAgree.StabKW.stab_kW | exact GlobalTheory.SquareAgree.StabKW.stab_kW | (intros; apply GlobalTheory.SquareAgree.StabKW.stab_kW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingExpansionProductFunctionFixedByKplusStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingExpansion_productFunction_fixed_by_Kplus : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {t : T}, t ∈ U → ∀ {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.top 0), finG (G.V (.top 0)) k ∈ G.Kplus →
    ∀ z : ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)),
      (τ.sum fun d b => b * ∏ l, moveFirst W ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) (vecsOf S d) l (z l)) =
        τ.sum fun d b => b * ∏ l, vecsOf S d l (z l) := by
  first | exact @GlobalTheory.TopZeroFirst.product_invariant | exact GlobalTheory.TopZeroFirst.product_invariant | (intros; apply GlobalTheory.TopZeroFirst.product_invariant <;> assumption)
end

