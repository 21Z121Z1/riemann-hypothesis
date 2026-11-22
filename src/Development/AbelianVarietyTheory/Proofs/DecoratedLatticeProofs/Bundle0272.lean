import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0252
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.T2SpaceHalfAdelicMatrixAddSubgroup
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaFunctionZeroOfInvariantFunctionals
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0258
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0242
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0135
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1500
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0267
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRealCentreCharacterOnDefiniteVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

open scoped ComplexOrder

namespace GlobalTheory.CenterVac

variable {D : D7}

theorem lintegral_enorm_sq_eq_one {α : Type} [MeasurableSpace α] {μ : Measure α} {s : Set α} {f : α → ℂ}
    (h : ∫ w in s, ‖f w‖ ^ 2 ∂μ = 1) : ∫⁻ w in s, ‖f w‖ₑ ^ 2 ∂μ = 1 := by
  have hint : Integrable (fun w => ‖f w‖ ^ 2) (μ.restrict s) :=
    Integrable.of_integral_ne_zero (by rw [h]; exact one_ne_zero)
  have e := ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun w => by positivity)
  rw [h, ENNReal.ofReal_one] at e
  rw [e]
  refine lintegral_congr fun w => ?_
  rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem om_vac_eq_smul {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hθ : IsInfFam θ) {S T : HSp D} {x : DefSp S}
    {y : DefSp T} (hx : x.Is) (hy : y.Is) {k : KerDat S T} (hk : k.Is ψ θ x y) {z : GA D S} (hz : z ∈ GinfC S) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ k.om (z, 1) k.vac = c • k.vac := by
  obtain ⟨χS, χT, hom⟩ := hk.weil
  obtain ⟨hψ, hv⟩ := hk.vac
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have hdet : ∀ τ, (gramAt D S τ).det ≠ 0 := fun τ h0 => by
    have := (hx.cart τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  obtain ⟨r, hr, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ S hdet z hz
  have hy1 : IsDetRoot T 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  have one : ∀ τ, compAt θ τ (Formalism.L2.Theta.mt T 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one T _
  obtain ⟨a, ha⟩ : ∃ a : ℂ, k.om (z, 1) k.vac = a • k.vac :=
    ⟨_, GlobalTheory.WeilVacChar.vacuum_character D ψ hψ S T θ hθ χS χT k.om η hη hom x.s y.s hx.cart hy.cart z hz 1 (one_mem _)
      (fun τ => by rcases hx.pm τ with h | h <;> rw [h] <;> simp) (fun τ => by rw [one, one_mul, mul_one]) r 1 hr hy1
      k.vac hv.theta hv.fock⟩
  refine ⟨a, ?_, ha⟩
  obtain ⟨⟨p, hp⟩, hn⟩ := hv.norm
  have n1 : nrm2 p.1 p.2 k.vac = 1 := hn p hp
  obtain ⟨hH, hF, -⟩ := hp
  have hu := hom.om_unit p.1 p.2 hH hF (z, 1) k.vac hv.theta
  have hL := lintegral_enorm_sq_eq_one (μ := p.1) (s := p.2) (f := k.vac) n1
  rw [ha] at hu
  simp only [Pi.smul_apply, smul_eq_mul, enorm_mul, mul_pow] at hu
  rw [lintegral_const_mul' _ _ (by simp), hL, mul_one] at hu
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_eq_one] at hu
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) two_ne_zero).1 hu

theorem exists_center_char : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (S T : HSp D) (x : DefSp S) (y : DefSp T), x.Is → y.Is → ∀ k : KerDat S T, k.Is ψ θ x y → ∃ c : GA D S → ℂ, ∀ z ∈ GinfC S, z ∈ Subgroup.center (GA D S) → ‖c z‖ = 1 ∧ k.om (z, 1) k.vac = c z • k.vac := by
  intro D ψ θ hθ S T x y hx hy k hk
  have h : ∀ z : GA D S, ∃ c : ℂ, z ∈ GinfC S → ‖c‖ = 1 ∧ k.om (z, 1) k.vac = c • k.vac := fun z => by
    by_cases hz : z ∈ GinfC S
    · obtain ⟨c, hc⟩ := om_vac_eq_smul hθ hx hy hk hz
      exact ⟨c, fun _ => hc⟩
    · exact ⟨1, fun h' => absurd h' hz⟩
  choose c hc using h
  exact ⟨c, fun z hz _ => hc z hz⟩

end GlobalTheory.CenterVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSchwartzBruhatExtByZeroOfSplitPlaceHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)

namespace GlobalTheory.SBOfHalf

theorem exists_sb_ext_eq : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : GlobalTheory.LocMod.Place D k) (S T : HSp D) (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : GlobalTheory.LocMod.Frame k S.rank Y') (FT : GlobalTheory.LocMod.Frame k T.rank Y) (Λ : AddSubgroup (WO S T)), IsOpen ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → IsCompact ((Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) : AddSubgroup (Matrix Y Y' k)) : Set (Matrix Y Y' k)) → ∀ Φ : WO S T → ℂ, IsSBHalf p.e Λ Φ → ∃ Φ' : SB (Matrix Y Y' k), GlobalTheory.LocMod.Witness.ext p FS FT Φ' = Φ := by
  intro D k _ _ _ _ p S T Y Y' _ _ _ _ FS FT Λ hAo hAc Φ hΦ
  classical
  set A : AddSubgroup (Matrix Y Y' k) := Λ.comap (GlobalTheory.LocMod.Witness.upH p FS FT) with hA
  obtain ⟨hsupp, k₀, hk₀, hinv, hsup⟩ := hΦ
  have hkF : ((k₀ : D.host.F)) ≠ 0 := Nat.cast_ne_zero.2 hk₀.ne'
  have hkk : ((k₀ : k)) ≠ 0 := by
    have h := (map_ne_zero (p.π.comp (algebraMap D.host.F (AE D)))).2 hkF
    simpa using h
  have hupA : ∀ a : Matrix Y Y' k, a ∈ A ↔ p.up FS FT a ∈ Λ := fun a => Iff.rfl
  have hnsmul : ∀ (x : Matrix Y Y' k), k₀ • x = (k₀ : k) • x := fun x => by
    rw [← Nat.cast_smul_eq_nsmul k]
  have hup_nsmul : ∀ (x : Matrix Y Y' k), p.up FS FT (k₀ • x) = k₀ • p.up FS FT x := fun x =>
    map_nsmul (GlobalTheory.LocMod.Witness.upH p FS FT) k₀ x
  let f : Matrix Y Y' k → ℂ := fun x => Φ (p.up FS FT x)
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    have hV : IsOpen {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} :=
      hAo.preimage (continuous_const_smul _)
    have h0 : (x - x) ∈ {z : Matrix Y Y' k | (k₀ : k)⁻¹ • z ∈ A} := by
      simp only [sub_self, Set.mem_setOf_eq, smul_zero]; exact A.zero_mem
    have hn := (continuous_sub_right x).continuousAt.preimage_mem_nhds (hV.mem_nhds h0)
    filter_upwards [hn] with y hy
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hy
    have hy' : y = x + k₀ • ((k₀ : k)⁻¹ • (y - x)) := by
      rw [hnsmul, smul_smul, mul_inv_cancel₀ hkk, one_smul, add_sub_cancel]
    show Φ (p.up FS FT y) = Φ (p.up FS FT x)
    rw [hy', GlobalTheory.LocMod.Witness.up_add, hup_nsmul]
    exact hinv _ hy (GlobalTheory.LocMod.Witness.up_half p FS FT _) _
  have hcpt : HasCompactSupport f := by
    refine HasCompactSupport.intro (hAc.image (continuous_const_smul ((k₀ : k)⁻¹))) fun x hx => ?_
    by_contra hne
    apply hx
    refine ⟨k₀ • x, ?_, ?_⟩
    · show p.up FS FT (k₀ • x) ∈ Λ
      rw [hup_nsmul]; exact hsup _ hne
    · show (k₀ : k)⁻¹ • k₀ • x = x
      rw [hnsmul, smul_smul, inv_mul_cancel₀ hkk, one_smul]
  refine ⟨⟨f, hloc, hcpt⟩, ?_⟩
  funext t
  rw [GlobalTheory.LocMod.Witness.ext_apply]
  split_ifs with ht
  · show Φ (p.up FS FT (p.down FS FT t)) = Φ t
    rw [GlobalTheory.LocMod.Witness.up_down p FS FT ht]
  · by_contra h
    exact ht (hsupp t (Ne.symm h))

end GlobalTheory.SBOfHalf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSiegelParabolicConjDoubledCompact
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.StdUnn.ConjElt

theorem compInf_sigR_comm {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
    (w : NumberField.InfinitePlace F) (x : AF F ⊗[F] E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ x) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ (compInf F E w x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r y => simp [compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem compInf_inclR_eq {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (w : NumberField.InfinitePlace F) (y : E) :
    compInf F E w (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F) y) = Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR w.Completion y := by
  simp [compInf, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem sq_real_of_majorant {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (a b : GL (Fin n) (AF F ⊗[F] E)) (ha : IsMajorantFrame σ J a)
    (hbw : ∀ w, Formalism.UG.bc (compInf F E w) b = Formalism.UG.bc (compInf F E w) a) (w : NumberField.InfinitePlace F) :
    (((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1) *
      ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1)).map
        (compInf F E w) = 1 := by
  obtain ⟨s, hs⟩ := ha w
  rw [← hbw w] at hs
  have h1 : ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ).map (compInf F E w) =
      Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR w.Completion σ) (Formalism.UG.bc (compInf F E w) b).1 :=
    Matrix.ext fun i j => compInf_sigR_comm σ w _
  have h2 : (J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))).map (compInf F E w) =
      Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.JR (F := F) w.Completion J :=
    Matrix.ext fun i j => compInf_inclR_eq w _
  have hH : ((b.1.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ))ᵀ * J.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (AF F)) * b.1).map
      (compInf F E w) = Matrix.diagonal fun i => if s i = true then 1 else -1 := by
    rw [← hs, Matrix.map_mul, Matrix.map_mul, h1, h2]
    rfl
  rw [Matrix.map_mul, hH, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  split_ifs <;> simp

theorem gram_blk_mul {R : Type} [CommRing R] (c : R →+* R) {n : ℕ} (b J : Matrix (Fin n) (Fin n) R)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) R) :
    Formalism.UG.cT c (blkMat finSumFinEquiv b b * M) * dblGram finSumFinEquiv J * (blkMat finSumFinEquiv b b * M) =
      Formalism.UG.cT c M * dblGram finSumFinEquiv (Formalism.UG.cT c b * J * b) * M := by
  have h : Formalism.UG.cT c (blkMat finSumFinEquiv b b * M) =
      Formalism.UG.cT c M * Formalism.UG.cT c (blkMat finSumFinEquiv b b) := by
    rw [Formalism.UG.cT, Matrix.map_mul, Matrix.transpose_mul]; rfl
  have h2 : Formalism.UG.cT c (blkMat finSumFinEquiv b b) * dblGram finSumFinEquiv J * blkMat finSumFinEquiv b b =
      dblGram finSumFinEquiv (Formalism.UG.cT c b * J * b) := by
    rw [cT_blkMat, dblGram, dblGram, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul]
  rw [h, ← h2]
  simp only [Matrix.mul_assoc]

theorem diag_blk_mul {R : Type} [CommRing R] {n : ℕ} (b : Matrix (Fin n) (Fin n) R)
    (M : Matrix (Fin (n + n)) (Fin (n + n)) R) (l : Fin (n + n))
    (h : ∀ i : Fin n, M (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) l = M (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) l)
    (i : Fin n) :
    (blkMat finSumFinEquiv b b * M) (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) l =
      (blkMat finSumFinEquiv b b * M) (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) l := by
  simp only [Matrix.mul_apply, ← (finSumFinEquiv (m := n) (n := n)).sum_comp, Fintype.sum_sum_type, blkMat,
    Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, zero_mul, Finset.sum_const_zero,
    add_zero, zero_add, h]

theorem gA_dblSp {D : D7} (A : HSp D) : gA (dblSp A) = dblGram finSumFinEquiv (gA A) :=
  (congrArg (fun x => x.map (incA D)) (gram_hdbl A)).trans ((blkMat_map _ _ (map_zero _) _ _).trans
    (congrArg (blkMat finSumFinEquiv (gA A)) (Matrix.map_neg _ (map_neg _) _)))

theorem gram_frame {D : D7} (A : HSp D) (b : GL (Fin A.rank) (AE D)) (M : GL (Fin (A.rank + A.rank)) (AE D)) :
    adj (blkGL finSumFinEquiv (b, b) * M).1 * gA (dblSp A) * (blkGL finSumFinEquiv (b, b) * M).1 =
      adj M.1 * dblGram finSumFinEquiv (adj b.1 * gA A * b.1) * M.1 :=
  (congrArg (fun X : Mx D (A.rank + A.rank) (A.rank + A.rank) =>
    adj (blkGL finSumFinEquiv (b, b) * M).1 * X * (blkGL finSumFinEquiv (b, b) * M).1) (gA_dblSp A)).trans
    (gram_blk_mul (cA D) b.1 (gA A) M.1)

theorem exists_siegel_frame {D : D7} (A : HSp D) (μ : D.host.E) (hμ : IsSkew μ) (b : GL (Fin A.rank) (AE D))
    (M : GL (Fin (A.rank + A.rank)) (AE D))
    (hMg : adj M.1 * dblGram finSumFinEquiv (adj b.1 * gA A * b.1) * M.1 = incA D μ • rat (Jst D A.rank))
    (hMc : ∀ i j : Fin A.rank,
      M.1 (finSumFinEquiv (Sum.inr i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank)) =
      M.1 (finSumFinEquiv (Sum.inl i : Fin A.rank ⊕ Fin A.rank)) (finSumFinEquiv (Sum.inl j : Fin A.rank ⊕ Fin A.rank))) :
    ∃ p : siegel A, mt (dblSp A) p * (rat (Tm A μ) : Mx D (A.rank + A.rank) (A.rank + A.rank)) =
      (blkGL finSumFinEquiv (b, b) * M).1 :=
  GlobalTheory.StdUnn.exists_siegel_mul_Tm D A μ hμ (blkGL finSumFinEquiv (b, b) * M) ((gram_frame A b M).trans hMg)
    fun i j => diag_blk_mul b.1 M.1 _ (fun k => hMc k j) i

theorem adj_gram {D : D7} (A : HSp D) (b : Mx D A.rank A.rank) : adj (adj b * gA A * b) = adj b * gA A * b := by
  rw [adj_mul, adj_mul, adj_adj, adj_gA, Matrix.mul_assoc]

theorem sq_real {D : D7} (A : HSp D) (a b : GL (Fin A.rank) (AE D)) (ha : IsMaj A a)
    (hbw : ∀ w, Formalism.UG.bc (compInf D.host.F D.host.E w) b = Formalism.UG.bc (compInf D.host.F D.host.E w) a)
    (w : NumberField.InfinitePlace D.host.F) :
    ((adj b.1 * gA A * b.1) * (adj b.1 * gA A * b.1)).map (compInf D.host.F D.host.E w) = 1 :=
  sq_real_of_majorant _ _ a b ha hbw w

theorem exists_isConj : ∀ D : D7, ∃ μ : D.host.E, IsSkew μ ∧ ∀ (A : HSp D) (a : GL (Fin A.rank) (AE D)), IsMaj A a → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∃ p : siegel A, IsConj A a κ p := by
  intro D
  obtain ⟨μ, hμ, u, ε, hue⟩ := GlobalTheory.StdUnn.scalData_exists D
  obtain ⟨t, ht⟩ := GlobalTheory.StdUnn.exists_halfData D
  refine ⟨μ, hμ, fun A a ha κ hκ => ?_⟩
  obtain ⟨b, hbL, hbw⟩ := GlobalTheory.StdUnn.exists_isLatticeFrame_bc_eq D A a
  obtain ⟨Hm, hHm, hHmI⟩ := GlobalTheory.StdUnn.Unimod.gram_unimodular D A b hbL
  have hherm : adj Hm.1 = Hm.1 := by rw [hHm]; exact adj_gram A b.1
  have hsq : ∀ w, (Hm.1 * Hm.1).map (compInf D.host.F D.host.E w) = 1 := fun w => by
    rw [hHm]; exact sq_real A a b ha hbw w
  obtain ⟨M, M', hMg, hMc, hM'I, hMu, hMw⟩ := GlobalTheory.StdUnn.Frame.exists_frame D A.rank Hm hherm hHmI hsq μ u ε t hμ hue ht
  rw [hHm] at hMg
  obtain ⟨p, hp⟩ := exists_siegel_frame A μ hμ b M hMg hMc
  exact ⟨p, GlobalTheory.StdUnn.Conj.isConj_of_frame D A μ hμ κ hκ a b hbL hbw M M' u hM'I hMu hMw p hp⟩

end GlobalTheory.StdUnn.ConjElt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceInvariantFormOfWittCore
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.SplitPlaceForm

set_option maxHeartbeats 1000000 in

theorem exists_form_of_core : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ e, IsSplitIdem D e → ∀ ℓ₀ : (WO S₀ T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S₀ T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S₀ T f → ℓ₀ (heisO ψ S₀ T u f) = ℓ₀ f) → (∃ f, IsThetaFunO ψ S₀ T f ∧ ℓ₀ f ≠ 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ (∃ f, IsThetaFunO ψ S T f ∧ ℓ f ≠ 0) ∧ ∀ (h : GL (Fin T.rank) (AE D)) (a : GL (Fin ρ) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ (f f' : WO S T → ℂ) (k : ℂ), IsThetaFunO ψ S T f → IsThetaFunO ψ S T f' → (∀ x : Mx D T.rank ρ, (∀ i j, cA D e * x i j = x i j) → ℓ₀ (d.mixS T ψ μ 𝓕 (f') x) = k * ℓ₀ (d.mixS T ψ μ 𝓕 (f) (h.1 ⬝ x ⬝ a.1))) → ℓ f' = r * k * ℓ f := by
  intro D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ h0 hne
  letI : MeasurableSpace (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) := GlobalTheory.HalfAverage.measHalf _ _ _
  haveI : BorelSpace (GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ) := GlobalTheory.HalfAverage.borelHalf _ _ _
  have hH : ∀ x, x ∈ GlobalTheory.HalfAverage.halfMx (cA D e) T.rank ρ ↔ ∀ i j, cA D e * x i j = x i j := fun x => Iff.rfl
  obtain ⟨ℓ, hℓ⟩ := GlobalTheory.HalfLinForm.halfAvg_linear D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ)
  refine ⟨ℓ, fun u hu f hf => ?_, ?_, fun h a => ?_⟩
  · rw [hℓ _ (GlobalTheory.ThetaClosed.isThetaFunO_heisO_all hψ hf u), hℓ f hf]
    exact GlobalTheory.HalfInvariance.half_avg_heis_inv D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ h0 _ hH _ u hu f hf
  · obtain ⟨f, hf, hn⟩ := GlobalTheory.HalfNonvan.avg_mixS_ne_zero D ψ hψ S S₀ T ρ d μ 𝓕 hμ e he ℓ₀ hne _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ)
    exact ⟨f, hf, by rw [hℓ f hf]; exact hn⟩
  · obtain ⟨r, hr, hm⟩ := GlobalTheory.HalfTwist.integral_twist_fix_eq_smul D T.rank ρ (cA D e) _ hH (GlobalTheory.HalfAverage.haarHalf (cA D e) T.rank ρ) h a
    refine ⟨r, hr, fun f f' k hf hf' hk => ?_⟩
    have e1 := hm fun x => ℓ₀ (d.mixS T ψ μ 𝓕 f x)
    rw [hℓ f hf, hℓ f' hf', mul_comm (r : ℂ) k, mul_assoc, ← e1, ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => hk x.1 x.2)

end GlobalTheory.SplitPlaceForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUniformIsotypicAverageRealCentre
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AvgMidUnif

open GlobalTheory.AvgMid

theorem exists_isotypic_uniform : ∀ (D : D7), BiAct D → CenFock D → LiftSum D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ → ∀ (A S A' : HSp D) (x : DefSp A) (y : DefSp S) (z : DefSp A'), x.Is → y.Is → z.Is → ∀ (k₀ : KerDat A S) (k₀' : KerDat S A'), k₀.Is ψ θ x y → k₀'.Is ψ θ y z → ∀ (χ₁ : GA D A → ℂ) (χ₃ : GA D S → ℂ) (C₁ : WO A S → WO S A' → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₁ → IsBiSmooth C₁ → (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₁ u v) = χ₁ a • fun u => C₁ u v) → (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ v, k₀.om (1, b) (fun u => C₁ u v) = χ₃ b • fun u => C₁ u v) → ∃ (C₂ : WO A S → WO S A' → ℂ) (χ₂ : GA D S → ℂ), IsBiVac ψ A S A' x.L y.L z.L C₂ ∧ (∀ a ∈ GinfC A, a ∈ Subgroup.center (GA D A) → ∀ v, k₀.om (a, 1) (fun u => C₂ u v) = χ₁ a • fun u => C₂ u v) ∧ (∀ b ∈ GinfC S, b ∈ Subgroup.center (GA D S) → ∀ u, k₀'.om (b, 1) (C₂ u) = χ₂ b • C₂ u) ∧ ∀ (k : KerDat A S) (k' : KerDat S A'), k.Is ψ θ x y → k'.Is ψ θ y z → (∀ a ∈ GinfC A, ∀ b ∈ GinfC S, ∀ f, IsThetaFunO ψ A S f → k.om (a, b) f = k₀.om (a, b) f) → (∀ a ∈ GinfC S, ∀ b ∈ GinfC A', ∀ f, IsThetaFunO ψ S A' f → k'.om (a, b) f = k₀'.om (a, b) f) → ∀ φ, IsContAut A φ → biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₁) = biLift k.om k'.om x.vol y.vol φ (biComb ψ A S A' k.c k'.c C₂) := by
  intro D _ hF _ ψ θ hθ A S A' x y z hx hy hz k₀ k₀' hk₀ hk₀' χ₁ χ₃ C₁ hC₁ _ h1 h3
  obtain ⟨χA, χS, hwa⟩ := hk₀.weil
  obtain ⟨χS', χA', hwb⟩ := hk₀'.weil
  by_cases h0 : ∀ u v, C₁ u v = 0
  · refine ⟨C₁, fun _ => 1, hC₁, h1, fun b _ _ u => ?_, fun _ _ _ _ _ _ _ _ => rfl⟩
    rw [show C₁ u = 0 from funext (h0 u), map_zero, smul_zero]
  push_neg at h0
  obtain ⟨u₀, v₀, h0⟩ := h0
  have hv : ∀ b : ↥(GinfC S ⊓ Subgroup.center (GA D S)), k₀.om (1, b.1) (fun u => C₁ u v₀) u₀ = χ₃ b.1 * C₁ u₀ v₀ :=
    fun b => congrFun (h3 b.1 b.2.1 b.2.2 v₀) u₀
  have hχ : Continuous fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ₃ b.1 := by
    have : (fun b : ↥(GinfC S ⊓ Subgroup.center (GA D S)) => χ₃ b.1) =
        fun b => k₀.om (1, b.1) (fun u => C₁ u v₀) u₀ / C₁ u₀ v₀ := funext fun b => by rw [hv, mul_div_cancel_right₀ _ h0]
    rw [this]
    exact ((hwa.om_cont _ (hC₁.left v₀).1 u₀).comp (continuous_const.prodMk continuous_subtype_val)).div_const _
  have hm : ∀ b b' : ↥(GinfC S ⊓ Subgroup.center (GA D S)), χ₃ (b.1 * b'.1) = χ₃ b.1 * χ₃ b'.1 := fun b b' => by
    have e := hv (b * b')
    have e' : ((1, (b * b').1) : GA D A × GA D S) = (1, b.1) * (1, b'.1) := by simp
    rw [e', map_mul, Module.End.mul_apply, h3 b'.1 b'.2.1 b'.2.2, map_smul, Pi.smul_apply, hv, smul_eq_mul] at e
    refine mul_right_cancel₀ h0 ?_
    rw [← Subgroup.coe_mul, ← e]
    ring
  obtain ⟨hcpt, ν, hν, hν'⟩ := exists_haar hy
  obtain ⟨W, hW, hWf⟩ := hF ψ θ hθ A S x y hx hy k₀ hk₀ χ₁
  let E : Submodule ℂ (WO A S → ℂ) := Submodule.span ℂ (Set.range fun v u => C₁ u v)
  haveI : FiniteDimensional ℂ E := by
    refine Submodule.finiteDimensional_of_le (S₂ := W.map (pureTensorO ψ θ A S x.s y.s x.B y.B k₀.vac))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨v, rfl⟩
    obtain ⟨P, hP, e⟩ := hWf _ (hC₁.left v).1 (hC₁.left v).2 (fun a ha hc => h1 a ha hc v)
    exact Submodule.mem_map.2 ⟨P, hP, e.symm⟩
  have hEv : E ≤ vacSub ψ A S (latO A S x.L y.L fun _ => True) := Submodule.span_le.2 (by
    rintro _ ⟨v, rfl⟩; exact hC₁.left v)
  have hEe : ∀ (p : GA D A × GA D S) (c : ℂ), (∀ v, k₀.om p (fun u => C₁ u v) = c • fun u => C₁ u v) →
      ∀ f ∈ E, k₀.om p f = c • f := fun p c h f hf => by
    have : E ≤ LinearMap.eqLocus (k₀.om p) (c • LinearMap.id) := Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact h v)
    exact this hf
  obtain ⟨n, e, g, he, hg, hs⟩ := GlobalTheory.SeeSaw.FinRank.sum_prod_of_slices C₁ E
    (vacSub ψ S A' (latO S A' y.L z.L fun _ => True)) (fun v => Submodule.subset_span ⟨v, rfl⟩) hC₁.right
  have hg' : ∀ i, mean k₀'.om ν χ₃ (g i) ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True) := fun i =>
    vac_mean hwb hθ hχ (hg i)
  have hl : ∀ v, (fun u => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) ∈ E := fun v => by
    have : (fun u => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) = ∑ i, mean k₀'.om ν χ₃ (g i) v • e i := by
      funext u; simp [Finset.sum_apply, mul_comm]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (he i)
  have hr : ∀ u, (fun v => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v) = ∑ i, e i u • mean k₀'.om ν χ₃ (g i) := fun u => by
    funext v; simp [Finset.sum_apply]
  refine ⟨fun u v => ∑ i, e i u * mean k₀'.om ν χ₃ (g i) v, fun b => χ₃ b⁻¹, ⟨?_, fun v => hEv (hl v), fun u => ?_⟩,
    fun a ha hc v => hEe _ _ (h1 a ha hc) _ (hl v), fun b hb hc u => ?_, fun k k' hk hk' hag hag' φ hφ => ?_⟩
  · exact continuous_finset_sum _ fun i _ => ((hEv (he i)).1.cont.comp continuous_fst).mul
      ((hg' i).1.cont.comp continuous_snd)
  · rw [hr]
    exact (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hg' i) :
      _ ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True))
  · simp only []
    rw [hr, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_comm]
    exact congrArg _ (eigen_mean hwb hθ hχ hm (hg i).1 ⟨b, hb, hc⟩)
  · obtain ⟨χA₁, χS₁, hwa₁⟩ := hk.weil
    obtain ⟨χS₁', χA₁', hwb₁⟩ := hk'.weil

    have hmean : ∀ i, mean k₀'.om ν χ₃ (g i) = mean k'.om ν χ₃ (g i) := fun i => by
      funext w
      simp only [mean]
      congr 1
      funext b
      rw [hag' b.1 b.2.1 1 (GinfC A').one_mem (g i) (hg i).1]
    have hEk : ∀ b : ↥(GinfC S ⊓ Subgroup.center (GA D S)), ∀ f ∈ E, k.om (1, b.1) f = χ₃ b.1 • f :=
      fun b f hf => by
        rw [hag 1 (GinfC A).one_mem b.1 b.2.1 f (hEv hf).1]
        exact hEe _ _ (h3 b.1 b.2.1 b.2.2) f hf
    have hg'' : ∀ i, mean k'.om ν χ₃ (g i) ∈ vacSub ψ S A' (latO S A' y.L z.L fun _ => True) := fun i =>
      vac_mean hwb₁ hθ hχ (hg i)
    simp only [hmean]
    funext h₂
    have hX : ∀ i, IsThetaFunO ψ A S (comb ψ A S k.c (e i)) := fun i => theta_comb hwa₁.std hk.fin (hEv (he i)).1
    rw [show C₁ = fun u v => ∑ i, e i u * g i v from funext fun u => funext (hs u), biComb_sum, biComb_sum,
      biLift_sum hwa₁ hwb₁ hx.cpt hy.cpt _ _ hX (fun i => theta_comb hwb₁.std hk'.fin (hg i).1) hφ,
      biLift_sum hwa₁ hwb₁ hx.cpt hy.cpt _ _ hX (fun i => theta_comb hwb₁.std hk'.fin (hg'' i).1) hφ]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [comb_mean hwb₁ hχ hk'.fin (hg i).1]
    refine (lift_mean hwb₁ hθ hy.cpt y.vol hχ (theta_comb hwb₁.std hk'.fin (hg i).1)
      (contAut_lift hwa₁ hx.cpt x.vol (hX i) hφ) (fun b h => ?_) h₂).symm
    rw [← integral_const_mul]
    congr 1
    funext a
    have e' : ((a, h * b.1) : GA D A × GA D S) = (a, h) * (1, b.1) := by simp
    rw [e', map_mul, Module.End.mul_apply, GlobalTheory.FrComb.om_comb hwa₁ (GinfC A).one_mem b.2.1 hk.fin (hEv (he i)).1,
      hEk b _ (he i), comb_smul, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]

end GlobalTheory.AvgMidUnif

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.WeilDatumExistence

theorem weilDatumExists : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.WeilDatumExistenceCriterion.WeilDatumExists D := by
  intro D S T ψ χS χT hψ hS hT rS rT
  exact GlobalTheory.WeilExist.exists_isWeilDatumO D ψ hψ S T χS χT
    (GlobalTheory.WeilParts.exists_isEtaTilde_unramified D) hS hT rS rT

end GlobalTheory.WeilDatumExistence
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExtendByZeroLeftMemCoreLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Matrix
open GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ContrComb

theorem extL_mem_latO : ∀ (D : D7) (V₀ A L S : HSp D) (o : OrthDec V₀ A L) (P : Pl D → Prop) (LA : Lat A) (LS : Lat S) (M : Lat V₀), IsSelfDualC A LA → IsSelfDualC S LS → IsSelfDualC V₀ M → (∀ v, P v → ∃ LL, OrthAt o M LA LL v) → ∀ u ∈ latO A S (LA : Set _) (LS : Set _) P, (o.resS S).symm (u, 0) ∈ latO V₀ S (M : Set _) (LS : Set _) P := by
  intro D V₀ A L S o P LA LS M hA hS hM hO u hu
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D A S LA LS hA hS P u] at hu
  obtain ⟨huP, huL⟩ := hu
  rw [GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D V₀ S M LS hM hS P, OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero]
  have hloc := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2
  refine ⟨fun i j => ?_, fun y hy => ?_⟩
  · rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_right _ _ (huP i k)
  · have hy' := ((hloc V₀).2.2.2 M y hM.1).1 hy
    have hp : o.pA *ᵥ y ∈ latV A LA P := by
      refine ((hloc A).2.2.2 LA (o.pA *ᵥ y) hA.1).2 ⟨fun i => ?_, fun v hv e he => ?_⟩
      · rw [Matrix.mulVec, dotProduct]
        exact Ideal.sum_mem _ fun k _ => Ideal.mul_mem_left _ _ (hy'.1 k)
      · obtain ⟨LL, hLL⟩ := hO v hv
        have h1 := ((hLL (e • y)).1 (hy'.2 v hv e he)).1
        rwa [Matrix.mulVec_smul] at h1
    have h2 := huL _ hp
    change (u * o.pA) *ᵥ y ∈ latA S LS P
    rwa [← Matrix.mulVec_mulVec]

end GlobalTheory.ContrComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierJacobiGroupSplitRealFiniteStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiGroup_split_real_finite : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d := by
  first | exact @GlobalTheory.jacGrp_split_inf_fin | exact GlobalTheory.jacGrp_split_inf_fin | (intros; apply GlobalTheory.jacGrp_split_inf_fin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalFlatMapDualColumnMultiplicationLawsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFlatMap_dualColumn_multiplicationLaws : ∀ (D : D7), FlatLaw D → GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ν : Measure k), ν.IsAddHaarMeasure → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (st : StepBF ψ B J) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FV : Frame k B.V.rank (n' ⊕ Fin (c + 1))) (G₀ : Frame k J.W₀.rank n) (FW : Frame k J.W.rank (n ⊕ Fin c)), p.IsCoreFrame B s FA F₀ → p.IsBesFrame B s FA FV → p.IsJacFrame J s (p.hz B) G₀ FW → ∀ (Tm : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] (WO B.V J.W → ℂ)), p.IsModel ψ FV FW Tm → ∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ GlobalTheory.RootEx.Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψk (b * (t r q - GlobalTheory.RootEx.basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → flatBF st (Tm Φ') = flatBF st (Tm Φ) := by
  first | exact @GlobalTheory.FlatColLaw.law_dual_col | exact GlobalTheory.FlatColLaw.law_dual_col | (intros; apply GlobalTheory.FlatColLaw.law_dual_col <;> assumption)
end

