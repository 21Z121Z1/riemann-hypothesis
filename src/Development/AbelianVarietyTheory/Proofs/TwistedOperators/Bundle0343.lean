import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0275
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0004
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0042
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0197
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RowDictPf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0244
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0226
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0238
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0234
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsMulCommutativeCentRealUJ
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0219
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0327
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0075
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0215

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlacePointCommuteOfNePlace
section
open Classical Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PointAtPlaceComm

open GlobalTheory.PointAtPlace GlobalTheory.PointAtPlaceHom Formalism.MainNotions.StandardLattice

theorem atTau_comm : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ τ' : D.what₂.Tau), τ ≠ τ' → ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ'), atTau θ V τ g * atTau θ V τ' g' = atTau θ V τ' g' * atTau θ V τ g := by
  intro D θ hθ V τ τ' hne g hg g' hg'
  have ha := atTau_spec hθ V τ hg
  have hb := atTau_spec hθ V τ' hg'
  set a := atTau θ V τ g
  set b := atTau θ V τ' g'
  have k : ∀ (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : GA D V),
      infMat D.sp.cm.sig V.gram φ x * infMat D.sp.cm.sig V.gram φ x⁻¹ = 1 := fun φ x => by
    rw [← infMat_mul, mul_inv_cancel, infMat_one]
  have triv : ∀ (φ : Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ) (x : GA D V),
      infMat D.sp.cm.sig V.gram φ x = 1 → infMat D.sp.cm.sig V.gram φ x⁻¹ = 1 := fun φ x h => by
    have := k φ x
    rwa [h, Matrix.one_mul] at this
  have hc : IsAtTau θ V τ 1 (a * b * a⁻¹ * b⁻¹) := by
    have all : ∀ ρ, infMat D.sp.cm.sig V.gram (θ ρ) (a * b * a⁻¹ * b⁻¹) = 1 := fun ρ => by
      simp only [infMat_mul]
      by_cases c : ρ = τ
      · subst c
        have hB : infMat D.sp.cm.sig V.gram (θ ρ) b = 1 := hb.2.2 ρ hne
        rw [hB, triv _ _ hB, Matrix.mul_one, Matrix.mul_one, k]
      · have hA : infMat D.sp.cm.sig V.gram (θ ρ) a = 1 := ha.2.2 ρ c
        rw [hA, triv _ _ hA, Matrix.one_mul, Matrix.mul_one, k]
    exact ⟨mul_mem (mul_mem (mul_mem ha.1 hb.1) (inv_mem ha.1)) (inv_mem hb.1), all τ, fun ρ _ => all ρ⟩
  have h1 : IsAtTau θ V τ 1 (1 : GA D V) := ⟨one_mem _, infMat_one V _, fun _ _ => infMat_one V _⟩
  have e : a * b * a⁻¹ * b⁻¹ = 1 :=
    (existsUnique_isAtTau V τ θ hθ 1 (one_mem_UH _)).unique hc h1
  have e2 : a * b * a⁻¹ = b := mul_inv_eq_one.1 e
  exact mul_inv_eq_iff_eq_mul.1 e2

end GlobalTheory.PointAtPlaceComm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedFnConjLocFinEqOne
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

noncomputable section

namespace GlobalTheory.PlaceAwayRed

theorem redFn_conj_locFin_eq_one : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (Formalism.IndefR.Lev.EAf D)) (a : GfC V) (v : HeightOneSpectrum (𝓞 D.host.F)) (PP : Pl D.host.E), PP.under (𝓞 D.host.F) ≠ v → ∀ k : Gv V v, finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V) ∈ St β → redFn β PP (finE V ((a * locFin V v k * a⁻¹ : GfC V) : GA D V)) = 1 := by
  intro D V β a v PP hPP k hS
  refine GlobalTheory.FinZeta.LevelOff.redFn_eq_one_of_proj β {PP.under (𝓞 D.host.F)} hS (fun u hu => ?_) (Finset.mem_singleton_self _)
  rw [Finset.mem_singleton] at hu
  subst hu
  have e : proj D.sp.cm.sig V.gram (PP.under (𝓞 D.host.F)) (embV V v k) = 1 := proj_emb_ne _ _ hPP k
  show proj D.sp.cm.sig V.gram (PP.under (𝓞 D.host.F)) ((a : GA D V) * (locFin V v k : GA D V) * ((a⁻¹ : GfC V) : GA D V)) = 1
  rw [coe_locFin, MonoidHom.map_mul, MonoidHom.map_mul, e, mul_one, ← MonoidHom.map_mul, ← Subgroup.coe_mul, mul_inv_cancel,
    Subgroup.coe_one, MonoidHom.map_one]

end GlobalTheory.PlaceAwayRed

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReductionConjugatedUnitaryElementEqOneIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KapRed

open Formalism.L2.SG.RowsJoinPinned (castGA)

variable {D : D7}

theorem iotaX_symm_eq {I : Formalism.MainNotions.S.AutInst} (h : I = Formalism.L2.SG.InstExistsPf.instOf D) (x : I.GA) :
    ((Formalism.IndefR.RationalEmbedding.iota D).trans (castGA h.symm)).symm x = (Formalism.IndefR.RationalEmbedding.iota D).symm (castGA h x) := by
  subst h
  rfl

theorem castGA_mem {I I' : Formalism.MainNotions.S.AutInst} (h : I = I') (k : I.Gf) (g : ℕ) :
    (k ∈ I.Kset ↔ (castGA h (1, k)).2 ∈ I'.Kset) ∧ (k ∈ I.Kg g ↔ (castGA h (1, k)).2 ∈ I'.Kg g) := by
  subst h
  exact ⟨Iff.rfl, Iff.rfl⟩

private theorem swapAE_map_sndA_eq_tauF (D : D7)
    (z : TensorProduct D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.host.E) :
    Formalism.IndefR.Lev.swapAE D
              (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E) z) =
      Formalism.L2.SG.AdBridge.tauF (Formalism.IndefR.RationalEmbedding.inst D) z := by
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact (map_zero _).symm
  | tmul a x =>
    exact (Formalism.L2.SG.AdBridge.tauF_tmul (Formalism.IndefR.RationalEmbedding.inst D) a x).symm
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    exact (map_add _ a b).symm

private theorem finE_Yc_zero_iota_symm (y : (Formalism.L2.SG.InstExistsPf.instOf D).GA) :
    finE (Yc D 0) ((Formalism.IndefR.RationalEmbedding.iota D).symm y) = y.2.1 := by
  have hb := (Formalism.L2.SG.AdBridge.toHA_isBridge (Formalism.IndefR.RationalEmbedding.inst D)
    (Formalism.L2.SG.Closed.adelic_isomorphism_statement (Formalism.IndefR.RationalEmbedding.inst D)).1 y).2
  apply Units.ext
  ext i j
  have hij := congrFun (congrFun hb i) j
  refine Eq.trans ?_ hij.symm
  show Formalism.IndefR.Lev.swapAE D
      (Algebra.TensorProduct.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E) _) = _
  exact swapAE_map_sndA_eq_tauF D _

abbrev kmat (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) : GL (Fin (Yc D 0).rank) (EAf D) := x.1

theorem finE_kap (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (t : GA D (Yc D 0))
    (k : X.B.I.Gf) :
    finE (Yc D 0) (kap X h t k) = (finE (Yc D 0) t)⁻¹ * kmat (castGA h (1, k)).2 * finE (Yc D 0) t := by
  have e2 : finE (Yc D 0) (id ((iotaX X h).symm (1, k)) : GA D (Yc D 0)) = kmat (castGA h (1, k)).2 :=
    (congrArg (finE (Yc D 0)) (iotaX_symm_eq h (1, k))).trans (finE_Yc_zero_iota_symm _)
  have e3 : finE (Yc D 0) (kap X h t k) =
      (finE (Yc D 0) t)⁻¹ * finE (Yc D 0) (id ((iotaX X h).symm (1, k)) : GA D (Yc D 0)) * finE (Yc D 0) t := by
    rw [← map_inv (finE (Yc D 0)) t, ← map_mul (finE (Yc D 0)), ← map_mul (finE (Yc D 0))]
    rfl
  rw [e3, e2]

section Gen

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem frGL_mul_apply (t β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (y : GL (Fin n) (Formalism.L2.Herm.intAf F E)) :
    Formalism.L2.DIV.frGL (t * β) y = t * Formalism.L2.DIV.frGL β y * t⁻¹ := by
  simp only [Formalism.L2.DIV.frGL, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, mul_inv_rev]
  group

theorem redFn_conj (β t x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (PP : Formalism.L2.DIV.Pl E) :
    Formalism.L2.DIV.redFn β PP (t⁻¹ * x * t) = Formalism.L2.DIV.redFn (t * β) PP x := by
  classical
  by_cases hx : x ∈ Formalism.L2.DIV.St (t * β)
  · obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hx
    have hy : t⁻¹ * Formalism.L2.DIV.frGL (t * β) y * t = Formalism.L2.DIV.frGL β y := by
      rw [frGL_mul_apply]
      group
    rw [hy, Formalism.L2.DIV.redFn_frGL, Formalism.L2.DIV.redFn_frGL]
  · have hx' : t⁻¹ * x * t ∉ Formalism.L2.DIV.St β := by
      intro hmem
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hmem
      apply hx
      refine MonoidHom.mem_range.2 ⟨y, ?_⟩
      rw [frGL_mul_apply, hy]
      group
    simp only [Formalism.L2.DIV.redFn, Formalism.L2.DIV.ext1, dif_neg hx, dif_neg hx']

end Gen

theorem upperLeftBlock_eq_one_iff_of_mem_blockTri {κ : Type} [CommRing κ] {n r : ℕ} (hr : r ≤ n) (hn : n ≤ r) (g : GL (Fin n) κ) :
    Formalism.L2.DIV.upperLeftBlock hr g = 1 ↔ g = 1 := by
  obtain rfl : r = n := le_antisymm hr hn
  have hmem : g ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
    rw [Formalism.L2.DIV.mem_blockTri]
    intro i j hij
    simp [Formalism.L2.DIV.blk2] at hij
  have hself : Formalism.L2.DIV.upperLeftBlock hr g = g := by
    apply Units.ext
    rw [Formalism.L2.DIV.upper_block_val_submatrix hr hmem]
    ext i j
    rfl
  rw [hself]

end GlobalTheory.KapRed

namespace GlobalTheory.KapRed

theorem core (D : D7) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (β : GL (Fin (Yc D 0).rank) (EAf D))
    (x : (Formalism.L2.SG.InstExistsPf.instOf D).Gf) (g : ℕ) (hβ : IsFrame β (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0))
    (hx : x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset) (hg : 1 ≤ g) (hrad : (Ideal.span {(g : 𝓞 D.host.E)}).IsRadical)
    (hcov : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (g : 𝓞 D.host.E) ∈ PP.asIdeal → PP ∈ Pg ∨ ∃ PP' ∈ Pg, Formalism.IndefR.Lev.IsConjPl PP' PP)
    (hin : ∀ PP ∈ Pg, (g : 𝓞 D.host.E) ∈ PP.asIdeal) :
    x ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kg g ↔ ∀ PP ∈ Pg, Formalism.L2.DIV.redFn β PP x.1 = 1 := by
  rw [GlobalTheory.KgFrame.mem_Kg_iff_redFn D β x g hβ hx hg hrad]
  constructor
  · intro H PP hP
    exact H PP (hin PP hP)
  · intro H PP hgP
    rcases hcov PP hgP with hP | ⟨PP', hP', hc⟩
    · exact H PP hP
    · exact GlobalTheory.ConjPlaceRed.redFn_conj_eq_one D β x PP PP' hβ hx hc (H PP' hP')

theorem rank_lowerChainSpace_zero_le (D : D7) : (Yc D 0).rank ≤ D.R.r := by
  have e : (Yc D 0).rank = D.R.rankY 0 := D.sp.Y_rank 0 (Nat.zero_le _)
  rw [e]
  show D.R.r + 0 * D.R.t ≤ D.R.r
  simp

theorem red_kap_eq_one_iff : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → ∀ (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (t : GA D (Yc D 0)), (∀ x : X.B.I.E, HEq (X.ιE x) x) → (∃ (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1), (∀ kv, ((plg kv : R.Pg) : Pl D.host.E) = D.naut.plGw kv.1 kv.2) ∧ (∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = D.ntypes.e0.coeff ((R.eG.trans cG) g)) ∧ (∀ kv, R.C.P.Div kv.1 (plg kv).1) ∧ ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) ((R.eG.trans cG) g kv)) → IdempotentRealFixed D → t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → IsFrame (finE (Yc D 0) t * R.βY 0) (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0) → ∀ k ∈ X.B.I.Kset, (cG (rTup (R.βY 0) (R.dat0 R.triv) (finE (Yc D 0) (kap X h t k))) = 1 ↔ k ∈ X.B.I.Kg X.B.g) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ cG t _ hplg _ _ _ hfr k hk
  obtain ⟨plg, -, hplgw, -, -, -⟩ := hplg
  have hk' := (castGA_mem h k X.B.g).1.1 hk
  have hpos : 1 ≤ D.host.g 0 * D.host.g 1 :=
    Nat.succ_le_of_lt (Nat.mul_pos (D.host.g_prime 0).pos (D.host.g_prime 1).pos)
  have hin : ∀ PP ∈ R.Pg, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hP
    have hsame := hplgw (plg.symm ⟨PP, hP⟩)
    rw [Equiv.apply_symm_apply] at hsame
    have hq : ((D.host.g (plg.symm ⟨PP, hP⟩).1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have hov := D.naut.plGw_over (plg.symm ⟨PP, hP⟩).1 (plg.symm ⟨PP, hP⟩).2
      simp only at hsame
      have hI : PP.asIdeal =
          (D.naut.plGw (plg.symm ⟨PP, hP⟩).1 (plg.symm ⟨PP, hP⟩).2).asIdeal := by
        rw [← hsame]
      rw [hI]
      exact hov
    have hdvd : ∀ q : Fin 2, D.host.g q ∣ D.host.g 0 * D.host.g 1 := by
      intro q
      fin_cases q
      · first
        | exact dvd_mul_right _ _
        | simp
      · first
        | exact dvd_mul_left _ _
        | simp
    obtain ⟨c, hc⟩ := hdvd (plg.symm ⟨PP, hP⟩).1
    rw [hc, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hq
  have hcore := core D R.Pg (finE (Yc D 0) t * R.βY 0) (castGA h (1, k)).2 (D.host.g 0 * D.host.g 1) hfr hk' hpos
    (GlobalTheory.TypePrimesRadical.isRadical_span_g_mul D) (GlobalTheory.TypeProductCover.place_cover_prod D R.Pg plg hplgw) hin
  rw [(castGA_mem h k X.B.g).2, X.g_eq, hcore]
  have hrt : ∀ y, cG y = 1 ↔ y = 1 := fun y =>
    ⟨fun hy => cG.injective (hy.trans (map_one cG).symm), fun hy => by rw [hy]; exact map_one cG⟩
  refine (hrt _).trans ?_
  rw [finE_kap X h t k]
  have key : ∀ PP : R.Pg,
      (rTup (R.βY 0) (R.dat0 R.triv) ((finE (Yc D 0) t)⁻¹ * kmat (castGA h (1, k)).2 * finE (Yc D 0) t) PP = 1 ↔
        Formalism.L2.DIV.redFn (finE (Yc D 0) t * R.βY 0) PP.1 (castGA h (1, k)).2.1 = 1) := by
    intro PP
    show Formalism.L2.DIV.upperLeftBlock (R.dat0 R.triv).hr (Formalism.L2.DIV.redFn (R.βY 0) PP.1 _) = 1 ↔ _
    rw [redFn_conj, upperLeftBlock_eq_one_iff_of_mem_blockTri (R.dat0 R.triv).hr (by exact rank_lowerChainSpace_zero_le D)]
  constructor
  · intro H PP hP
    exact (key ⟨PP, hP⟩).1 (congrFun H ⟨PP, hP⟩)
  · intro H
    funext PP
    exact (key PP).2 (H PP.1 PP.2)

end GlobalTheory.KapRed
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularCentralizerNoncompact
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.ArchVanish

open GlobalTheory.AdelicU

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

def archKerEquiv (w : InfinitePlace F) : GArch σ J w × (projArch σ J w).ker ≃ₜ* GAd σ J where
  toFun p := embArch σ J w p.1 * p.2
  invFun x := (projArch σ J w x, ⟨(embArch σ J w (projArch σ J w x))⁻¹ * x, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, projArch_embArch_self, inv_mul_cancel]⟩)
  left_inv p := by
    obtain ⟨a, z, hz⟩ := p
    have hz' : projArch σ J w z = 1 := hz
    refine Prod.ext ?_ (Subtype.ext ?_)
    · simp [hz']
    · simp [hz']
  right_inv x := by simp
  map_mul' p q := by
    obtain ⟨a, z, hz⟩ := p
    obtain ⟨a', z', hz'⟩ := q
    have hc := (commute_embArch σ J a' (g := z) hz).eq
    simp only [Prod.mk_mul_mk, Subgroup.coe_mul, map_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (embArch σ J w a'), hc, mul_assoc]
  continuous_toFun := ((continuous_embArch σ J w).comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)
  continuous_invFun := by
    refine (continuous_projArch σ J w).prodMk (Continuous.subtype_mk ?_ _)
    exact ((continuous_embArch σ J w).comp (continuous_projArch σ J w)).inv.mul continuous_id

theorem archKerEquiv_apply (w : InfinitePlace F) (p : GArch σ J w × (projArch σ J w).ker) :
    archKerEquiv σ J w p = embArch σ J w p.1 * p.2 := rfl

variable {σ J}

theorem embArch_mem_cent_iff {w : InfinitePlace F} (a : GArch σ J w) (γ : GAd σ J) :
    embArch σ J w a ∈ Orb.cent γ ↔ a ∈ Orb.cent (projArch σ J w γ) := by
  rw [Orb.mem_cent, Orb.mem_cent]
  refine ⟨fun h => by simpa using congrArg (projArch σ J w) h, fun h => GAd_ext σ J (fun u => ?_) fun v => by simp⟩
  by_cases hu : u = w
  · subst hu; simpa using h
  · simp [projArch_embArch_ne σ J hu]

theorem isMulCommutative_cent_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) :
    IsMulCommutative (Orb.cent (ratEmb σ J γ)) := by
  refine ⟨⟨fun s t => Subtype.ext (GAd_ext σ J (fun u => ?_) fun v => ?_)⟩⟩
  · have hc := Orb.isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ u)
    have hs : projArch σ J u s ∈ Orb.cent (projArch σ J u (ratEmb σ J γ)) := by
      rw [Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 s.2]
    have ht : projArch σ J u t ∈ Orb.cent (projArch σ J u (ratEmb σ J γ)) := by
      rw [Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 t.2]
    simpa using congrArg Subtype.val (hc.1.1 ⟨_, hs⟩ ⟨_, ht⟩)
  · have hc := Orb.isMulCommutative_cent_HA (isRegSS_proj_ratEmb hγ v)
    have hs : proj σ J v s ∈ Orb.cent (proj σ J v (ratEmb σ J γ)) := by
      rw [Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 s.2]
    have ht : proj σ J v t ∈ Orb.cent (proj σ J v (ratEmb σ J γ)) := by
      rw [Orb.mem_cent, ← map_mul, ← map_mul, Orb.mem_cent.1 t.2]
    simpa using congrArg Subtype.val (hc.1.1 ⟨_, hs⟩ ⟨_, ht⟩)

theorem isMulCommutative_cent_projArch_ratEmb {γ : GRat σ J} (hγ : IsRegSS γ.1.1) (w : InfinitePlace F) :
    IsMulCommutative (Orb.cent (projArch σ J w (ratEmb σ J γ))) :=
  Orb.isMulCommutative_cent_HA (isRegSS_projArch_ratEmb hγ w)

theorem archKerEquiv_mem_cent_iff (w : InfinitePlace F) (γ : GAd σ J) (a : GArch σ J w)
    (z : (projArch σ J w).ker) :
    archKerEquiv σ J w (a, z) ∈ Orb.cent γ ↔
      a ∈ Orb.cent (projArch σ J w γ) ∧ z ∈ (Orb.cent γ).comap (projArch σ J w).ker.subtype := by
  have hz : projArch σ J w z.1 = 1 := z.2
  rw [archKerEquiv_apply, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · intro h
    have ha : a ∈ Orb.cent (projArch σ J w γ) := by
      have := congrArg (projArch σ J w) (Orb.mem_cent.1 h)
      rw [Orb.mem_cent]; simpa [hz] using this
    refine ⟨ha, ?_⟩
    simpa using mul_mem (inv_mem ((embArch_mem_cent_iff a _).2 ha)) h
  · rintro ⟨ha, hz'⟩
    exact mul_mem ((embArch_mem_cent_iff a _).2 ha) hz'

theorem exists_tensor_conj_archKerEquiv (fa : ∀ w, GArch σ J w → ℂ) (ff : ∀ v, GLoc σ J v → ℂ)
    (w : InfinitePlace F) (γ : GAd σ J) (z : (projArch σ J w).ker) :
    ∃ K : ℂ, ∀ a, Orb.tensor σ J fa ff ((archKerEquiv σ J w (a, z))⁻¹ * γ * archKerEquiv σ J w (a, z)) =
      K * fa w (a⁻¹ * projArch σ J w γ * a) := by
  classical
  have hz : projArch σ J w z.1 = 1 := z.2
  refine ⟨(∏ u ∈ Finset.univ.erase w, fa u (projArch σ J u (z.1⁻¹ * γ * z))) *
    ∏ᶠ v, ff v (proj σ J v (z.1⁻¹ * γ * z)), fun a => ?_⟩
  simp only [archKerEquiv_apply, Orb.tensor]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w)]
  have h1 : projArch σ J w ((embArch σ J w a * z)⁻¹ * γ * (embArch σ J w a * z)) = a⁻¹ * projArch σ J w γ * a := by
    simp [hz]
  have h2 : ∀ u ∈ Finset.univ.erase w, fa u (projArch σ J u ((embArch σ J w a * z)⁻¹ * γ * (embArch σ J w a * z))) =
      fa u (projArch σ J u (z.1⁻¹ * γ * z)) :=
    fun u hu => by simp [projArch_embArch_ne σ J (Finset.ne_of_mem_erase hu)]
  have h3 : ∀ v, proj σ J v ((embArch σ J w a * z)⁻¹ * γ * (embArch σ J w a * z)) = proj σ J v (z.1⁻¹ * γ * z) :=
    fun v => by simp
  rw [h1, Finset.prod_congr rfl h2]
  simp only [h3]
  ring

open Orb in

theorem quotInt_cent_eq_zero_of_arch (w : InfinitePlace F) (γ : GAd σ J) (hcomm : IsMulCommutative (cent γ))
    (dh : Measure (GAd σ J)) [dh.IsHaarMeasure] (dt : Measure (cent γ)) [dt.IsHaarMeasure]
    (da : Measure (GArch σ J w)) [da.IsHaarMeasure] (ds : Measure (cent (projArch σ J w γ))) [ds.IsHaarMeasure]
    (φ : GAd σ J → ℂ) (hi : GlobalTheory.AutomorphicL2Unitary.LeftInv (cent γ) φ)
    (hint : Integrable (GlobalTheory.AutomorphicL2Unitary.descend (cent γ) φ) (quotMeas (cent γ) dt dh))
    (h0 : ∀ z : (projArch σ J w).ker, quotInt (cent (projArch σ J w γ)) ds da (fun a => φ (archKerEquiv σ J w (a, z))) = 0) :
    quotInt (cent γ) dt dh φ = 0 := by
  have hB : IsClosed ((projArch σ J w).ker : Set (GAd σ J)) := by
    rw [MonoidHom.coe_ker]; exact isClosed_singleton.preimage (continuous_projArch σ J w)
  haveI : LocallyCompactSpace (projArch σ J w).ker := hB.locallyCompactSpace
  exact GlobalTheory.T.quotient_measure_fibration (GArch σ J w) (projArch σ J w).ker (GAd σ J) (archKerEquiv σ J w) _ _ (cent γ)
    (archKerEquiv_mem_cent_iff w γ) (isClosed_cent γ) hcomm dh dt da ds φ hi hint h0

end General

end GlobalTheory.ArchVanish

end

namespace GlobalTheory.ArchVanish

set_option maxHeartbeats 400000 in

theorem hasQuotInt_weighted_eq_zero : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (fa : ∀ w, GArch D.sp.cm.sig V.gram w → ℂ) (ff : ∀ v, GLoc D.sp.cm.sig V.gram v → ℂ), (∀ w, (μa w).IsHaarMeasure) → IsTestArchG M μa fa → IsFinFamily D.sp.cm.sig V.gram (frameLat V) ff → ∀ γ : GF V, IsRegSS γ.1.1 → ∀ w, ¬ IsCompact (cent (projArch D.sp.cm.sig V.gram w (rat V γ)) : Set (GArch D.sp.cm.sig V.gram w)) → ∀ b : GA D V → ℂ, Continuous b → LeftInv (cent (rat V γ)) b → (∀ g x, b (embArch D.sp.cm.sig V.gram w g * x) = b x) → ∀ (μ : Measure (GA D V)) [μ.IsHaarMeasure] (dt : Measure (cent (rat V γ))) [dt.IsHaarMeasure], HasQuotInt (cent (rat V γ)) dt μ (fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x) 0 := by
  intro D V S M μa fa ff hμa hfa hff γ hγ w hnc b hb hbl hbw μ _ dt _
  have hcm := isCMExt_host D
  have hJ := GlobalTheory.Doubling.isHermND_gram V
  have hcomm : IsMulCommutative (cent (rat V γ)) := isMulCommutative_cent_ratEmb hγ
  haveI : dt.IsMulRightInvariant := isMulRightInvariant_cent hcomm dt
  have hT : IsClosed (cent (rat V γ) : Set (GA D V)) := isClosed_cent _
  have hten := continuous_of_mem_ccAd (tensor_mem_ccAd hfa.mem hff)
  have hφi : LeftInv (cent (rat V γ)) fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x :=
    fun t ht x => by dsimp only; rw [hbl t ht x, leftInv_conjFn le_rfl _ t ht x]
  have hint : Integrable (descend (cent (rat V γ)) fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x)
      (quotMeas (cent (rat V γ)) dt μ) := by
    obtain ⟨C, hC, h0⟩ := isProperOrbit_ratEmb hcm hJ hγ _ hten.2
    refine integrable_descend hT hφi (hb.mul (hten.1.comp (by fun_prop))) hC fun x hx => h0 x ?_
    exact subset_tsupport _ (right_ne_zero_of_mul hx)

  have horb : ∀ (ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ)))) [ds.IsHaarMeasure]
      [ds.IsMulRightInvariant], HasOrbInt (μa w) (projArch D.sp.cm.sig V.gram w (rat V γ)) ds (fa w) 0 := by
    obtain ⟨ρ, rfl⟩ := (placeOf_bijective D).2 w
    intro ds _ _
    haveI := (M.ds ρ).1
    have hs : IsRegSS (matAt V ρ (projArch D.sp.cm.sig V.gram (placeOf D ρ) (rat V γ))) :=
      (isRegSS_archMat_iff hcm (embOverOf D ρ)).2 (isRegSS_projArch_ratEmb hγ _)
    have h := (hfa ρ).orb_noncompact _ hs hnc
    exact h ds
  haveI := hμa w
  obtain ⟨ds, hds1, hds2⟩ : ∃ ds : Measure (cent (projArch D.sp.cm.sig V.gram w (rat V γ))),
      ds.IsHaarMeasure ∧ ds.IsMulRightInvariant := by
    haveI : LocallyCompactSpace (cent (projArch D.sp.cm.sig V.gram w (rat V γ))) :=
      (isClosed_cent _).locallyCompactSpace
    exact ⟨Measure.haar, inferInstance, isMulRightInvariant_cent
      (isMulCommutative_cent_projArch_ratEmb (σ := D.sp.cm.sig) (J := V.gram) hγ w) _⟩
  refine ⟨hint, quotInt_cent_eq_zero_of_arch (σ := D.sp.cm.sig) (J := V.gram) w (rat V γ) hcomm μ dt (μa w) ds _ hφi
    hint fun z => ?_⟩
  obtain ⟨K, hK⟩ := exists_tensor_conj_archKerEquiv (σ := D.sp.cm.sig) (J := V.gram) fa ff w (rat V γ) z
  have e1 : (fun a => (fun x => b x * conjFn (rat V γ) (tensor D.sp.cm.sig V.gram fa ff) x)
      (archKerEquiv D.sp.cm.sig V.gram w (a, z))) =
      fun a => (b z * K) * conjFn (projArch D.sp.cm.sig V.gram w (rat V γ)) (fa w) a := funext fun a => by
    simp only [conjFn]
    rw [hK a, archKerEquiv_apply, hbw]
    ring
  rw [e1]
  have e2 := (horb ds).2
  calc quotInt _ ds (μa w) (fun a => (b z * K) * conjFn (projArch D.sp.cm.sig V.gram w (rat V γ)) (fa w) a)
      = (b z * K) * quotInt _ ds (μa w) (conjFn (projArch D.sp.cm.sig V.gram w (rat V γ)) (fa w)) :=
        integral_const_mul _ _
    _ = 0 := by rw [show quotInt _ _ _ _ = _ from e2, mul_zero]

end GlobalTheory.ArchVanish
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SymplecticFormFockMatrixEqNegSumImRealPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symplecticForm_fockMatrix_eq_neg_sum_im_real_places : ∀ (D : D7) (S T : HSp D) (A : GlobalTheory.ChainFr.Fr S) (B : GlobalTheory.ChainFr.Fr T) (Z Y : VCx D.what₂.Tau S.rank T.rank), GlobalTheory.VacUnique.omO S T (fun τ => fockMat A B τ (Z τ) : GlobalTheory.FockCompare.RW T S) (fun τ => fockMat A B τ (Y τ) : GlobalTheory.FockCompare.RW T S) = -(2 * ∑ τ, ‖tauE D τ D.host.xi0‖ * ∑ i, ∑ j, (Z τ i j * conj (Y τ i j)).im) := by
  first | exact @GlobalTheory.FockOmega.omO_fockMat | exact GlobalTheory.FockOmega.omO_fockMat | (intros; apply GlobalTheory.FockOmega.omO_fockMat <;> assumption)
end

