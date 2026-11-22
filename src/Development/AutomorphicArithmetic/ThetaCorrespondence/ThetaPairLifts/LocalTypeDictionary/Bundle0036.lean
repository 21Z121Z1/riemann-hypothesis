import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0772
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0031
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0658
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0026
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0666
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0616
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2247

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumRootExistsAlgebraic
section
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
private theorem mem_algebraic_of_root_of_unity {c : ℂ} {m : ℕ} (hm : 0 < m) (h : c ^ m = 1) : c ∈ Qbar :=
  mem_algebraicClosure_iff'.2 (IsIntegral.of_pow hm (h ▸ isIntegral_one))
private theorem norm_root_of_unity_eq_one {K : Type} [NormedField K] (σ : Qbar →+* K) {c : ℂ} {m : ℕ} (hm : 0 < m) (h : c ^ m = 1)
    (hc : c ∈ Qbar) : ‖σ ⟨c, hc⟩‖ = 1 := by
  have e : (⟨c, hc⟩ : Qbar) ^ m = 1 := Subtype.ext h
  have e' : ‖σ ⟨c, hc⟩‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, e, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e'
private theorem isOpen_principal_level_subgroup {D : D7} (T : HSp D) {N : ℕ} (hN : 0 < N) :
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
private theorem exists_pow_mem_open_subgroup {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K U : Subgroup G)
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
private theorem exists_pow_mem_principal_level {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
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
  exact exists_pow_mem_open_subgroup (GfC V) (Formalism.IndefR.Lev.levA V (Formalism.L2.DIV.St β)) _ inf_le_left
    (GlobalTheory.AscInh.stab_compact_open V β).1 (isOpen_principal_level_subgroup V hN) ⟨hk, hst⟩
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
private theorem exists_root_of_unity_factor {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
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
  obtain ⟨a, ha, hka⟩ := exists_pow_mem_principal_level S ΛS hΛS.1 hk h1 hN
  obtain ⟨b, hb, hkb⟩ := exists_pow_mem_principal_level T ΛT hΛT.1 hk' h2 hN
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
private theorem inverse_image_standard_lattice {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E) :
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
theorem movedVacuum_root_exists_algebraic (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
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
  have hvac := _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral hP hI ch hch p hp x y
  have hv := ch.S.Z.vac_is p hp
  have gx := GlobalTheory.MovedHomLat.movedLat_eq ch.S.toGridChoice _ h1 x
  have gy := GlobalTheory.MovedHomLat.movedLat_eq ch.S.toGridChoice _ h2 y
  have ix : inV (ch.S.N.fr p.small) (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) = (colLat (ch.S.N.fr p.small) : Set _) := by
    rw [hx, inverse_image_standard_lattice]
  have iy : inV (ch.S.N.fr p.big) (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) = (colLat (ch.S.N.fr p.big) : Set _) := by
    rw [hy, inverse_image_standard_lattice]
  have fx := SetLike.coe_injective (gx.symm.trans ix)
  have fy := SetLike.coe_injective (gy.symm.trans iy)
  cases p with
  | chi i j =>
    rw [show inV (frS ch.S.N (.chi i j)) (srcLat ch.S.toGridChoice (.chi i j) x y) = _ from iy,
      show inV (frT ch.S.N (.chi i j)) (tgtLat ch.S.toGridChoice (.chi i j) x y) = _ from ix] at hvac
    exact exists_root_of_unity_factor hom (fun τ => isCartanInv_neg (ch.W.cart_is _ h2.inRange τ)) (fun τ => ch.W.cart_is _ h1.inRange τ)
      (isSelfDualC_neg (ch.S.N.selfDual h2)) (ch.S.N.selfDual h1) hv (negMem _ (y * ch.S.N.u _).2) (x * ch.S.N.u _).2
      fy fx hvac
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    rw [show inV (frS ch.S.N (.top t j)) (srcLat ch.S.toGridChoice (.top t j) x y) = _ from ix,
      show inV (frT ch.S.N (.top t j)) (tgtLat ch.S.toGridChoice (.top t j) x y) = _ from iy] at hvac
    exact exists_root_of_unity_factor hom (fun τ => ch.W.cart_is _ h1.inRange τ) (fun τ => ch.W.cart_is _ h2.inRange τ)
      (ch.S.N.selfDual h1) (ch.S.N.selfDual h2) hv (x * ch.S.N.u _).2 (y * ch.S.N.u _).2
      fx fy hvac
end GlobalTheory.MovedVacRoot
end
open GlobalTheory.MovedVacRoot in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moved_vacuum_has_algebraic_root : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x = stdL D _ → GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y = stdL D _ →
    ∃ κ : ℂ, Mod1All κ ∧ (∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.UnitAt q κ) ∧ GlobalTheory.MovedKappaEx.JetKap ch p x y κ := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y hx hy
  obtain ⟨c, m, hm, h1, hc⟩ := _root_.GlobalTheory.MovedVacRoot.movedVacuum_root_exists_algebraic hP hI ch hch p hp x y hx hy
  have h2 : (opp p c) ^ m = 1 := by rw [← map_pow, h1, map_one]
  have h3 := mem_algebraic_of_root_of_unity hm h2
  refine ⟨opp p c, ⟨h3, fun σ => norm_root_of_unity_eq_one σ hm h2 h3⟩, fun q _ lam => ?_, fun k => ?_⟩
  · rw [lamC, dif_pos h3]
    exact norm_root_of_unity_eq_one lam hm h2 h3
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
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.OscillatorDerivAlongLineQuadratic
section
section
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
namespace GlobalTheory.OscQuad
theorem oscillator_deriv_along_line_quadratic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (m : ℕ) (u v : Fin m → Matrix (Fin n) (Fin d) (AE F E)) (c : Fin m → ℂ) (c₀ : ℂ),
      (∀ i, At (evI F) (u i) ∧ At (evI F) (v i)) ∧
      ∀ (f : SInf F (Fin n × Fin d)) (g₁ g₂ : Fin m → SInf F (Fin n × Fin d)),
        (∀ i, ActsD (evI F) (M.heisLine ψ (v i)) f (g₁ i)) → (∀ i, ActsD (evI F) (M.heisLine ψ (u i)) (g₁ i) (g₂ i)) →
        ∀ F₁ : ℝ → SInf F (Fin n × Fin d), (∀ t, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (F₁ t)) →
        ∀ y, HasDerivAt (fun t => F₁ t y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  classical
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hCM hψ hW γ hγ
  obtain ⟨T, hT, hadd, h0⟩ := _root_.GlobalTheory.T.archimedean_theta_family_exists_smooth hP M ψ χX χW om hCM hψ hW γ hγ
  obtain ⟨A, hAc, hA⟩ := GlobalTheory.T.archimedeanLine_intertwines_realSchrodinger M ψ χX χW om hψ hW γ hγ T hT
  haveI : BorelSpace (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Pi.borelSpace
  let μ : Measure (Fin n × Fin d → mixedEmbedding.mixedSpace F) := Measure.addHaar
  have hiso : ∀ t f, ∫ x, ‖T t f x‖ ^ 2 ∂μ = ∫ x, ‖f x‖ ^ 2 ∂μ := fun t f =>
    GlobalTheory.T.weil_representation_integral_action M ψ χX χW om hW μ inferInstance (γ (Multiplicative.ofAdd t)) f (T t f) (hT t f)
  obtain ⟨hc1, hc2⟩ := GlobalTheory.T.archimedeanOneParameterFamily_continuous M ψ χX χW om hW γ hγ T hT
  obtain ⟨m, a, b, c, c₀, hR⟩ := GlobalTheory.T.realMetaplectic_family_derivative_quadratic hP.realMetaplecticRepresentation
    (Fin n × Fin d → mixedEmbedding.mixedSpace F) μ inferInstance _
    (GlobalTheory.ArchUniq.Coord.isPairing_trP (F := F) (Fin n × Fin d)) A T hAc hadd h0 hA hiso hc1 (hc2 μ inferInstance)
  choose u hu hDu using fun i => GlobalTheory.T.exists_heisenbergLine_derivative_formula M ψ hψ (a i)
  choose v hv hDv using fun i => GlobalTheory.T.exists_heisenbergLine_derivative_formula M ψ hψ (b i)
  obtain ⟨r₀, hr₀, hinj⟩ := GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz (F := F) (Fin n × Fin d)
  refine ⟨m, u, v, c, c₀, fun i => ⟨hu i, hv i⟩, ?_⟩
  intro f g₁ g₂ h1 h2 F₁ hF y
  have eF : ∀ t, F₁ t = T t f := fun t => hinj _ _ ((hF t r₀ (hr₀ f)).symm.trans (hT t f r₀ (hr₀ f)))
  simp only [eF]
  exact hR f g₁ g₂ (fun i y => hDv i f (g₁ i) (h1 i) y) (fun i y => hDu i (g₁ i) (g₂ i) (h2 i) y) y
end GlobalTheory.OscQuad
end
end

section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oscillator_lie_action_quadratic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ γ ∈ Lines σ W, ∃ (m : ℕ) (u v : Fin m → Matrix (Fin n) (Fin d) (AE F E)) (c : Fin m → ℂ) (c₀ : ℂ),
      (∀ i, At (evI F) (u i) ∧ At (evI F) (v i)) ∧
      ∀ (f : SInf F (Fin n × Fin d)) (g₁ g₂ : Fin m → SInf F (Fin n × Fin d)),
        (∀ i, ActsD (evI F) (M.heisLine ψ (v i)) f (g₁ i)) → (∀ i, ActsD (evI F) (M.heisLine ψ (u i)) (g₁ i) (g₂ i)) →
        ∀ F₁ : ℝ → SInf F (Fin n × Fin d), (∀ t, Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (F₁ t)) →
        ∀ y, HasDerivAt (fun t => F₁ t y) (∑ i, c i * g₂ i y + c₀ * f y) 0 := by
  first | exact @_root_.GlobalTheory.OscQuad.oscillator_deriv_along_line_quadratic | exact _root_.GlobalTheory.OscQuad.oscillator_deriv_along_line_quadratic | (intros; apply _root_.GlobalTheory.OscQuad.oscillator_deriv_along_line_quadratic <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PlacewiseDecompositionOfKAverage
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
noncomputable section
namespace GlobalTheory.PlaceDecomp
theorem placeDecomposition_kAverage : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), KFinFun (N.M.ε τ) e → HasCtp θ N U (TyOf θ N ρ) τ (kAvg (N.M.ε τ) (N.M.σ τ) e) := by
  intro D θ hθ hp N U W _ _ _ ρ τ e he
  haveI : CompleteSpace (N.M.H τ) := (N.M.ds τ).1
  haveI : IsTopologicalGroup (GA D N.V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hP := N.M.fr_unit τ
  have hJ := N.M.fr_gram τ
  have hσ : Std (N.M.ε τ) (N.M.σ τ) := std_of_isDS hp.harishChandraModules (N.M.ds τ)
  have hec : Continuous e := by obtain ⟨F, -, h1, h2, -⟩ := he; exact h2 _ h1
  have hU : ∀ k, (N.M.fr τ)⁻¹ * toMK k * N.M.fr τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
    fun k => GlobalTheory.Published.AutFin.conj_mem_UH hP hJ k
  have hκ := GlobalTheory.SeriesToClosure.continuous_conjK (ε := N.M.ε τ) (P := N.M.fr τ)
  have hA : ∀ f, GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f =
      GlobalTheory.AvgOtherPlace.avgF θ N.V (muK (N.M.ε τ)) τ (fun k => (N.M.fr τ)⁻¹ * toMK k * N.M.fr τ) e f := fun f => rfl
  refine ⟨GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun φ _ => GlobalTheory.SeriesToClosure.moves_avg hθ hP hJ hσ he φ⟩
  · intro f hf
    exact GlobalTheory.KFinAvgSpan.continuous_avg hθ hP hJ hec hf
  · intro f f' hf hf'
    rw [hA, hA, hA]
    exact GlobalTheory.AvgOtherPlace.avgF_add _ hθ hκ hU hec hf hf'
  · intro c f _
    rw [hA, hA]
    exact GlobalTheory.AvgOtherPlace.avgF_smul _ c f
  · intro f hf
    refine ⟨_root_.GlobalTheory.AvgCuspType.cusp_average_isCuspOfType D θ hθ hp N f hf.1 τ e he, fun k hk hkf g => ?_⟩
    simp only [GlobalTheory.SeriesToClosure.avg]
    congr 1
    funext k'
    rw [mul_assoc, ← GlobalTheory.PointAtPlaceHom.comm_of_mem N.V (GlobalTheory.PointAtPlaceHom.atTau_mem N.V τ _) hkf, ← mul_assoc,
      hf.2 k hk hkf]
  · intro τ' hne f hf hT x
    haveI := GlobalTheory.AvgCoeff.coeffSpan_finiteDimensional (ρ τ')
    have hAc : Continuous fun k' : KG (N.M.ε τ) => atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) :=
      GlobalTheory.RealAverage.continuous_atTau hθ hκ hU
    have hc : ∀ k k', GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k *
        atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) =
        atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k :=
      fun k k' => GlobalTheory.PointAtPlaceComm.atTau_comm D θ hθ N.V τ' τ hne _
        (GlobalTheory.Published.AutFin.conj_mem_UH (N.M.fr_unit τ') (N.M.fr_gram τ') k) _ (hU k')
    have hcont : ∀ k, Continuous fun k' : KG (N.M.ε τ) => e k' *
        f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k) :=
      fun k => hec.mul (hf.1.1.cont.comp ((continuous_const.mul hAc).mul continuous_const))
    have key := GlobalTheory.AvgCoeff.integral_mem (muK (N.M.ε τ)) (GlobalTheory.Published.AutFin.coeffSpan (ρ τ'))
      (fun k' k => e k' * f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) *
        GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k))
      (fun k' => Submodule.smul_mem _ (e k') (hT _)) (fun k => GlobalTheory.ExpansionAverage.integrable_K (hcont k))
    have heq : (fun k => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f
        (x * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)) =
        fun k => ∫ k', e k' * f (x * atTau θ N.V τ ((N.M.fr τ)⁻¹ * toMK k' * N.M.fr τ) *
          GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k) ∂(muK (N.M.ε τ)) := by
      funext k
      simp only [GlobalTheory.SeriesToClosure.avg]
      congr 1
      funext k'
      rw [mul_assoc, hc, ← mul_assoc]
    show (fun k => GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e f
        (x * GlobalTheory.Published.AutFin.kAt θ N.V τ' (N.M.ε τ') (N.M.fr τ') k)) ∈ _
    rw [heq]
    exact key
  · intro τ' hne g hg f _
    funext x
    simp only [GlobalTheory.SeriesToClosure.avg, rTr]
    congr 1
    funext k
    rw [mul_assoc x, mul_assoc x, GlobalTheory.AvgOtherPlace.atTau_comm hθ hne (hU k) hg]
  · intro τ' hne X hX f hf
    rw [hA, hA]
    exact (GlobalTheory.AvgOtherPlace.avgF_Rder _ hθ hne hκ hU hec hf.1.1 hX).symm
end GlobalTheory.PlaceDecomp
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.placewise_decomposition_of_K_average : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)) (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (N.M.ε τ)) (W τ)) (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), KFinFun (N.M.ε τ) e → HasCtp θ N U (TyOf θ N ρ) τ (kAvg (N.M.ε τ) (N.M.σ τ) e) := by
  exact @_root_.GlobalTheory.PlaceDecomp.placeDecomposition_kAverage
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.PureThetaIntegralContinuousOrthogonal
section
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology MeasureTheory
open GlobalTheory.WeilM
noncomputable section
namespace GlobalTheory.SoPureThetaCont
theorem continuous_pure_theta_integral : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → Decay B G om om' →
    ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∀ h, Continuous fun f : SInf F (Fin a' × Fin (a + a')) => G.M'.I om' (pure f φ) h := by
  intro hP F E _ _ _ _ _ σ B a a' G X om om' hT hD φ hSB hev hSo h
  have hPair := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).2
  have hstd : ∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 :=
    (hev.and hT.geo.hM'.std).mono fun v hv => hv.1.trans hv.2
  let A : (Fin a' × Fin (a + a') → Af F) → ℂ := fun z => ∏ᶠ v, φ v fun i => Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (z i)
  have hA : A ∈ SB (Fin a' × Fin (a + a') → Af F) := GlobalTheory.AdelicCoordSB.finprod_mem_SB F _ φ hSB hstd
  have heq : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ = pureA F u A := fun _ => rfl
  have hso : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ ∈ G.M'.So B.ψ B.τ₁ := fun u =>
    Submodule.subset_span ⟨u, φ, hSB, hev, hSo, rfl⟩
  have hsch : ∀ u : SInf F (Fin a' × Fin (a + a')), pure u φ ∈ schA F _ := fun u =>
    GlobalTheory.TensUniq.pure_mem_schA u φ hSB hstd
  have hpres : ∀ x, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), om' x Φ ∈ schA F _ := fun x Φ hΦ =>
    hPair.weil.isUSplitting.pres x Φ hΦ
  have hconv : ∀ u : SInf F (Fin a' × Fin (a + a')), IntegrableOn (fun g => theta om' (pure u φ) g h) G.M'.dom G.M'.μ :=
    fun u => (hD.2 _ (hso u)).2.1 h
  have hadd : ∀ (u u' : SInf F (Fin a' × Fin (a + a'))) g,
      theta om' (pure (u + u') φ) g h = theta om' (pure u φ) g h + theta om' (pure u' φ) g h := by
    intro u u' g
    have e : pure (u + u') φ = pure u φ + pure u' φ := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
    simp only [theta, e, map_add]
    exact thetaSum_add F (hpres _ _ (hsch u)) (hpres _ _ (hsch u'))
  have hsmul : ∀ (c : ℂ) (u : SInf F (Fin a' × Fin (a + a'))) g,
      theta om' (pure (c • u) φ) g h = c * theta om' (pure u φ) g h := by
    intro c u g
    have e : pure (c • u) φ = c • pure u φ := funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
    simp only [theta, e, map_smul]
    exact thetaSum_smul F c _
  have hcontg : ∀ g, Continuous fun u : SInf F (Fin a' × Fin (a + a')) => theta om' (pure u φ) g h := fun g =>
    (_root_.GlobalTheory.ThKBasic.theta_kernel_basic_properties hP F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hPair).2 A hA g h
  let μd := G.M'.μ.restrict G.M'.dom
  let T : SInf F (Fin a' × Fin (a + a')) → UA σ G.V'.J → ℂ := fun u g => theta om' (pure u φ) g h
  have hfin : ∀ u, (∫⁻ g, ‖T u g‖ₑ ∂μd) ≠ ⊤ := fun u => (hconv u).2.ne
  have hν : ∀ u, ∫ g, ‖T u g‖ ∂μd = (∫⁻ g, ‖T u g‖ₑ ∂μd).toReal := fun u =>
    integral_norm_eq_lintegral_enorm (hconv u).1
  let ν : Seminorm ℂ (SInf F (Fin a' × Fin (a + a'))) :=
    Seminorm.of (fun u => ∫ g, ‖T u g‖ ∂μd)
      (fun u u' => by
        calc ∫ g, ‖T (u + u') g‖ ∂μd ≤ ∫ g, (‖T u g‖ + ‖T u' g‖) ∂μd :=
              integral_mono (hconv (u + u')).norm ((hconv u).norm.add (hconv u').norm)
                fun g => by simp only [T]; rw [hadd]; exact norm_add_le _ _
          _ = _ := integral_add (hconv u).norm (hconv u').norm)
      (fun c u => by
        simp only [T, hsmul, norm_mul]
        exact integral_const_mul _ _)
  haveI : BarrelledSpace ℂ (SInf F (Fin a' × Fin (a + a'))) := by
    classical exact GlobalTheory.schwartzMap_barrelledSpace _
  have hN : LowerSemicontinuous fun u => ∫⁻ g, ‖T u g‖ₑ ∂μd := by
    rw [lowerSemicontinuous_iff_le_liminf]
    intro u
    calc ∫⁻ g, ‖T u g‖ₑ ∂μd ≤ ∫⁻ g, liminf (fun u' => ‖T u' g‖ₑ) (𝓝 u) ∂μd :=
          lintegral_mono fun g => (((hcontg g).tendsto u).enorm.liminf_eq).ge
      _ ≤ _ := lintegral_liminf_le' fun u' => (hconv u').1.enorm
  have hνc : Continuous ν := by
    refine Seminorm.continuous_of_lowerSemicontinuous ν fun u y hy => ?_
    by_cases hy0 : y < 0
    · exact Filter.Eventually.of_forall fun u' => hy0.trans_le (apply_nonneg ν u')
    · push_neg at hy0
      have hy' : y < (∫⁻ g, ‖T u g‖ₑ ∂μd).toReal := by rw [← hν]; exact hy
      have h1 : ENNReal.ofReal y < ∫⁻ g, ‖T u g‖ₑ ∂μd := (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).2 hy'
      filter_upwards [hN u _ h1] with u' hu'
      show y < ∫ g, ‖T u' g‖ ∂μd
      rw [hν]
      exact (ENNReal.ofReal_lt_iff_lt_toReal hy0 (hfin _)).1 hu'
  let L : SInf F (Fin a' × Fin (a + a')) →+ ℂ :=
    { toFun := fun u => G.M'.I om' (pure u φ) h
      map_zero' := by
        show ∫ g, T 0 g ∂μd = 0
        have : ∀ g, T 0 g = 0 := fun g => by
          simpa using hsmul 0 0 g
        simp [this]
      map_add' := fun u u' => by
        show ∫ g, T (u + u') g ∂μd = ∫ g, T u g ∂μd + ∫ g, T u' g ∂μd
        simp only [T, hadd]
        exact integral_add (hconv u) (hconv u') }
  have hLb : ∀ u, ‖L u‖ ≤ ν u := fun u => norm_integral_le_integral_norm _
  have hL : Continuous L := by
    refine continuous_of_continuousAt_zero L ?_
    rw [ContinuousAt, map_zero, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun u => norm_nonneg _) hLb ?_
    simpa using hνc.tendsto (0 : SInf F (Fin a' × Fin (a + a')))
  exact hL
end GlobalTheory.SoPureThetaCont
end
end

section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_theta_integral_continuous_orthogonal : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W),
    IsTriple B G X om om' → Decay B G om om' →
    ∀ φ : ∀ v : Pl F, (Fin a' × Fin (a + a') → Fv F v) → ℂ, (∀ v, φ v ∈ GlobalTheory.WeilM.SB _) →
      (∀ᶠ v in cofinite, φ v = G.M'.vac v) → φ B.v₁ ∈ G.M'.SoLoc B.ψ B.τ₁ →
      ∀ h, Continuous fun f : SInf F (Fin a' × Fin (a + a')) => G.M'.I om' (pure f φ) h := by
  first | exact @_root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral | exact _root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral | (intros; apply _root_.GlobalTheory.SoPureThetaCont.continuous_pure_theta_integral <;> assumption)
end
end

