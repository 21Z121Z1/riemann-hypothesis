import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SizeAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0032
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0895
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0115
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1744
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianAdaptedPlaneSeesaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingMonomialProductsLinearIndependent
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0945
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Development.AbelianVarietyTheory.Definitions.Divisors.RealisedChainTorusEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2059

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicDivOfBeta
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SqTop.SqField

theorem gBig_and {Q Q' : GP} (h : GBig @Q) (h' : GBig @Q') :
    GBig fun {_ _ _ _} G μ C x b => Q G μ C x b ∧ Q' G μ C x b := by
  obtain ⟨a, ha⟩ := h
  obtain ⟨a', ha'⟩ := h'
  refine ⟨max a a', fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h1⟩ := ha ε CF (le_of_max_le_left hCF)
  obtain ⟨C1, x1, h2⟩ := ha' ε CF (le_of_max_le_right hCF)
  refine ⟨max C0 C1, max x0 x1, fun C hC D large₂ he hx hR T Lc μ hμ G => ⟨?_, ?_⟩⟩
  · exact h1 C (le_of_max_le_left hC) D large₂ he (le_of_max_le_left hx) hR T Lc μ hμ G
  · exact h2 C (le_of_max_le_right hC) D large₂ he (le_of_max_le_right hx) hR T Lc μ hμ G

theorem isAlgebraic_norm {D : D7} {δ t0 : ℂ} {Q N : ℕ} {B : ℝ} {del : ℕ → ℝ} (hC : GlobalTheory.NormSum.CoordInt D N B Q del)
    (P : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) (hP : P.Small N B) : IsAlgebraic ℚ ((P.norm : ℝ) : ℂ) := by
  have hco : ∀ h T, P.coord h T ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun h T => by
    obtain ⟨p, hp, hi⟩ := GlobalTheory.T.exists_prime_isIntegralOverStandardLatticeStabiliser D P.d h
    haveI : Fact p.Prime := ⟨hp⟩
    exact ((hC δ t0 p Q le_rfl P hP).2.2 h hi T).1
  have hsq : ∀ g, ((P.sq g : ℝ) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun g => by
    unfold GlobalTheory.NormSum.Pair.sq
    rw [Complex.ofReal_sum]
    refine sum_mem fun T _ => ?_
    have e : ((‖P.coord g T‖ ^ 2 : ℝ) : ℂ) = P.coord g T * (starRingEnd ℂ) (P.coord g T) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [e]
    exact mul_mem (hco g T)
      (mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 (hco g T)).algHom (starRingEnd ℂ).toRatAlgHom))
  have hterm : ∀ h : GlobalTheory.NormSum.Cls D P.d P.J,
      (((((GlobalTheory.NormSum.gam D P.J h.out : ℝ))⁻¹ * P.sq h.out : ℝ)) : ℂ) ∈ Formalism.MainNotions.TaylorLogMetric.Qbar := fun h => by
    rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast]
    exact mul_mem (inv_mem (natCast_mem _ _)) (hsq _)
  refine mem_algebraicClosure_iff.1 ?_
  unfold GlobalTheory.NormSum.Pair.norm
  by_cases hs : (Function.support fun h : GlobalTheory.NormSum.Cls D P.d P.J =>
      ((GlobalTheory.NormSum.gam D P.J h.out : ℝ))⁻¹ * P.sq h.out).Finite
  · rw [finsum_eq_sum _ hs, Complex.ofReal_sum]
    exact sum_mem fun h _ => hterm h
  · rw [finsum_of_infinite_support hs, Complex.ofReal_zero]
    exact zero_mem _

theorem isAlgebraic_div_of_beta {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {d s : ℕ} (hd : 0 < d)
    (hs : 1 ≤ s) (κ : I → ℕ) (Λ : PeriodPair) {x y : ℂ} (hx : x ≠ 0)
    (ha : IsAlgebraic ℚ (GlobalTheory.CMVal.beta E d s κ Λ x)) (hb : IsAlgebraic ℚ (GlobalTheory.CMVal.beta E d s κ Λ y)) :
    IsAlgebraic ℚ (y / x) := by
  have hC : (GlobalTheory.CMVal.C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (GlobalTheory.CMVal.cmValueConst_pos E hd (by omega) κ).ne'
  have hΔ : GlobalTheory.CMVal.latDisc Λ ^ Formalism.PairingDivisionLocalBalance.wtM (2 * s) κ ≠ 0 := pow_ne_zero _ (GlobalTheory.CMVal.latDisc_ne_zero Λ)
  have e : (y / x) ^ 12 = GlobalTheory.CMVal.beta E d s κ Λ y / GlobalTheory.CMVal.beta E d s κ Λ x := by
    unfold GlobalTheory.CMVal.beta
    field_simp
  refine IsAlgebraic.of_pow (n := 12) (by norm_num) ?_
  rw [e]
  exact mem_algebraicClosure_iff.1 (div_mem (mem_algebraicClosure_iff.2 hb) (mem_algebraicClosure_iff.2 ha))

theorem sqIn_of {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (μ₀ : T)
    (hI : GlobalTheory.NormSum.IntSt) (hΛ : ∃ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ)
    (hT : ∀ (i j : Fin D.R.m) (s : ℕ), 1 ≤ s → s ≤ halfRank D i j → ∀ c, ∃ x, IsTor G i j s (fam G μ₀ i j c) x ∧ x ≠ 0 ∧
      ∀ Λ, GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice D.host.d Λ →
        IsAlgebraic ℚ (GlobalTheory.CMVal.beta D.host.E D.host.d s (kap D sc.cGap i j s) Λ x))
    (hQ : GlobalTheory.NormSum.GoodLevel D (levQ G.pl))
    (hS : ∀ (δ t0 : ℂ) (Q : ℕ) (P P' : GlobalTheory.NormSum.Pair D ⊤ δ t0 Q) t (i j : Fin D.R.m) 𝔪, IsBottom G t i j 𝔪 P P' →
      P.Small (bigN D) (maxWt D sc.cGap) ∧ P'.Small (bigN D) (maxWt D sc.cGap)) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ GlobalTheory.BigTop.Fun.SqIn G μ₀ (algebraMap M ℂ) := by
  obtain ⟨C, -, hI⟩ := hI
  have hN : 1 ≤ bigN D := by have := D.R.m_add_three_le_k; unfold bigN; omega
  obtain ⟨-, del, -, hco, -⟩ := hI D (levQ G.pl) (bigN D) (maxWt D sc.cGap) (max 1 (Real.log D.host.rdE)) hQ hN
    (by exact_mod_cast le_max_left _ _) (le_max_left _ _) (le_max_right _ _)

  obtain ⟨Sn, hSn, hSa, hSb⟩ : ∃ Sn : Set ℂ, Sn.Finite ∧ (∀ z ∈ Sn, IsAlgebraic ℚ z) ∧
      (GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (fun _ => True) → GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (· ∈ Sn)) := by
    by_cases hb : GlobalTheory.BigTop.Fun.BottomsWith G μ₀ (fun _ => True)
    · obtain ⟨δ, t0, hb⟩ := hb
      choose P P' hP using hb
      refine ⟨Set.range (fun ij => ((P ij).norm : ℂ)) ∪ Set.range (fun ij => ((P' ij).norm : ℂ)),
        (Set.finite_range _).union (Set.finite_range _), ?_,
        fun _ => ⟨δ, t0, fun ij => ⟨P ij, P' ij, (hP ij).1, Or.inl ⟨ij, rfl⟩, Or.inr ⟨ij, rfl⟩⟩⟩⟩
      rintro z (⟨ij, rfl⟩ | ⟨ij, rfl⟩)
      · exact isAlgebraic_norm hco _ (hS δ t0 _ _ _ _ _ _ _ (hP ij).1).1
      · exact isAlgebraic_norm hco _ (hS δ t0 _ _ _ _ _ _ _ (hP ij).1).2
    · exact ⟨∅, Set.finite_empty, fun z hz => absurd hz (Set.notMem_empty z), fun h => absurd h hb⟩

  let St : Set ℂ := ⋃ (i : Fin D.R.m) (j : Fin D.R.m) (s ∈ Set.Icc 1 (halfRank D i j)) (c : Bool),
    {z | ∃ x y, IsTor G i j s (nuH G μ₀ i j) x ∧ IsTor G i j s (nuH G μ₀ i j * delOf Lc c) y ∧ z = y / x}
  have hSt : St.Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => (Set.finite_Icc _ _).biUnion fun s _ =>
      Set.finite_iUnion fun c => Set.Subsingleton.finite ?_
    rintro _ ⟨x, y, hx, hy, rfl⟩ _ ⟨x', y', hx', hy', rfl⟩
    rw [hx.2.unique hx'.2, hy.2.unique hy'.2]
  have hd : 0 < D.host.d := D.host.hypOdd.2.1.pos
  obtain ⟨Λ, hΛ⟩ := hΛ
  have hSta : ∀ z ∈ St, IsAlgebraic ℚ z := by
    intro z hz
    simp only [St, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨i, j, s, ⟨h1, h2⟩, c, x, y, hx, hy, rfl⟩ := hz
    obtain ⟨x0, hx0, hx00, ha⟩ := hT i j s h1 h2 none
    obtain ⟨x1, hx1, -, hb⟩ := hT i j s h1 h2 (some c)
    rw [hx.2.unique hx0.2, hy.2.unique hx1.2]
    exact isAlgebraic_div_of_beta hd h1 _ Λ hx00 (ha Λ hΛ) (hb Λ hΛ)
  let S : Set ℂ := Sn ∪ St
  haveI : Finite S := (hSn.union hSt).to_subtype
  have hmem : ∀ z ∈ S, z ∈ Set.range (algebraMap (IntermediateField.adjoin ℚ S) ℂ) := fun z hz =>
    ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin fun z hz =>
    (Or.elim hz (hSa z) (hSta z)).isIntegral, ⟨fun h => ?_, fun i j s c x y h1 h2 hx hy => ?_⟩⟩
  · obtain ⟨δ, t0, b⟩ := hSb h
    exact ⟨δ, t0, fun ij => let ⟨P, P', a, b1, b2⟩ := b ij; ⟨P, P', a, hmem _ (Or.inl b1), hmem _ (Or.inl b2)⟩⟩
  · refine hmem _ (Or.inr ?_)
    simp only [St, Set.mem_iUnion, Set.mem_setOf_eq]
    exact ⟨i, j, s, ⟨h1, h2⟩, c, x, y, hx, hy, rfl⟩

end GlobalTheory.SqTop.SqField

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSystemOf
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FrameAut

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame

section Op

variable (K : Type) [CommRing K] (n : ℕ) {ι : Type} [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ)

def wtOp (g : ι → GL (Fin n) K) : Module.End K (NablaT K n mu) :=
  ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : Kˣ) : K) • grp K n mu g

theorem wtOp_apply (g : ι → GL (Fin n) K) (u : NablaT K n mu) :
    wtOp K n mu sh g u = ((∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : Kˣ) : K) • grp K n mu g u := rfl

theorem wtOp_one : wtOp K n mu sh 1 = 1 := by
  simp [wtOp, grp]

theorem wtOp_mul (g h : ι → GL (Fin n) K) : wtOp K n mu sh (g * h) = wtOp K n mu sh g * wtOp K n mu sh h := by
  simp only [wtOp, grp, map_mul, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul, smul_mul_smul_comm]

def wtHom : (ι → GL (Fin n) K) →* Module.End K (NablaT K n mu) where
  toFun := wtOp K n mu sh
  map_one' := wtOp_one K n mu sh
  map_mul' := wtOp_mul K n mu sh

end Op

end GlobalTheory.FrameAut

open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL

namespace GlobalTheory.FrameAut

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz)

def labOf (j : Fin D.R.m) (t : p.P.T) (Q : (blk p j t).Pl) : HeightOneSpectrum (𝓞 D.host.E) := Formalism.DivisionValues.conjPl (plOf p j t Q)

def IsSystemOf (j : Fin D.R.m) (t : p.P.T) {l : ℕ} [Fact l.Prime] {N : ℕ} {F : Frame l D.what₂.Tau N} {e0 : D.what₂.LL →+* PadicAlgCl l}
    {ix : F.I → (blk p j t).Pl × ℕ} {inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl l)} (T : Tied p j t F e0 ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl l) (π : Submodule ℂ (UA D.host.E N → ℂ)) : Prop :=
  IsAutRepU π ∧
  (∀ τ, ∃ lam : DomWeight N, (∀ a, lam.w a = (mu τ a : ℤ) + T.sh τ) ∧ HasWeightAt π (T.io.toRingHom.comp (inc τ)) lam ∧
    HasWeightAt π (T.io.toRingHom.comp (GlobalTheory.ExpFrame.cj (inc τ))) lam.dual) ∧
  (∀ v : HeightOneSpectrum (𝓞 D.host.E), ((l : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → IsUnramU π v) ∧
  ∀ Q : (blk p j t).Pl, IsUnramU π (labOf p j t Q) ∧
    ∃ (σ : SmIrr (GL (Fin N) ((labOf p j t Q).adicCompletion D.host.E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU N (labOf p j t Q)) ((cLoc (labOf p j t Q)).comp (locU N (labOf p j t Q)).subtype) σ.ρ ∧
      GlobalTheory.LFun.HasSatGL (labOf p j t Q) σ.ρ S ∧
      ∀ i, (ix i).1 = Q → T.io (θ i) = GlobalTheory.LFun.satEig (Formalism.UG.qV D.host.E (labOf p j t Q)) N S (ix i).2

def PlacesOk (j : Fin D.R.m) (t : p.P.T) (l : ℕ) : Prop :=
  (∀ Q : (blk p j t).Pl, IsSplitAt (labOf p j t Q) ∧
    (labOf p j t Q).under (𝓞 (maximalRealSubfield D.host.E)) = (plOf p j t Q).under (𝓞 (maximalRealSubfield D.host.E)) ∧
    Ideal.absNorm (labOf p j t Q).asIdeal = (blk p j t).q Q ∧
    (((l : ℕ) : 𝓞 D.host.E) ∈ (labOf p j t Q).asIdeal ↔ ((l : ℕ) : 𝓞 D.host.E) ∈ (plOf p j t Q).asIdeal)) ∧
  {v : HeightOneSpectrum (𝓞 D.host.E) | (Ideal.absNorm v.asIdeal).Prime ∧
    ¬ ∃ Q : (blk p j t).Pl, ((l : ℕ) : 𝓞 D.host.E) ∉ (plOf p j t Q).asIdeal ∧ labOf p j t Q = v}.Finite ∧
  ∀ ν ∈ (blk p j t).bl, ∀ Q, ‖D.what₂.embLL (ν Q)‖ ^ 2 = ((blk p j t).q Q : ℝ) ^ ((blk p j t).n - (blk p j t).t)

open Classical in

def AutAt (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau) (w : HeightOneSpectrum (𝓞 D.what₂.LL)) : Prop :=
  PlacesOk p j (p.R.mu w) (Formalism.EigenvalueLevelCeiling.plc w) ∧
  ∀ [Fact (Formalism.EigenvalueLevelCeiling.plc w).Prime] (F : Frame (Formalism.EigenvalueLevelCeiling.plc w) D.what₂.Tau P.Nr) (R : Reads F W.lam (blk p j (p.R.mu w)) w)
    (inc : D.what₂.Tau → (D.host.E →+* PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w))) (T : Tied p j (p.R.mu w) F R.e0 R.ix inc)
    (mu : D.what₂.Tau → ℕ → ℕ) (θ : F.I → PadicAlgCl (Formalism.EigenvalueLevelCeiling.plc w)), (∀ τ, Antitone (Formalism.CohomologicalDescent.LD.res P.Nr (mu τ))) → F.IsEig mu θ →
    ∃ π, IsSystemOf p j (p.R.mu w) T mu θ π

def AutSt : Prop := InRange fun _ _ _ _ p j P W w => AutAt p j P W w

end GlobalTheory.FrameAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitAwayFromLevelProdNormalisedMatrixGaussSum
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.GaussUnit

theorem isIntegral_of_eq {x y : ℂ} (h : IsIntegral ℤ x) (e : y = x) : IsIntegral ℤ y := e ▸ h

theorem unitOff_of_two {N : ℕ} {u : ℂ} (h0 : u ≠ 0) {a b : ℕ} (ha : IsIntegral ℤ ((N : ℂ) ^ a * u))
    (hb : IsIntegral ℤ ((N : ℂ) ^ b * u⁻¹)) : UnitOff N u := by
  have hN : ∀ c : ℕ, IsIntegral ℤ ((N : ℂ) ^ c) := fun c => by
    have : IsIntegral ℤ ((N : ℕ) : ℂ) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (N : ℤ)))
    exact this.pow c
  refine ⟨h0, a + b, ?_, ?_⟩
  · have := (hN b).mul ha
    refine isIntegral_of_eq (this) ?_
    ring
  · have := (hN a).mul hb
    refine isIntegral_of_eq (this) ?_
    ring

theorem unitOff_one (N : ℕ) : UnitOff N 1 :=
  unitOff_of_two (a := 0) (b := 0) one_ne_zero (by simpa using isIntegral_one) (by simpa using isIntegral_one)

theorem unitOff_mul {N : ℕ} {u v : ℂ} (hu : UnitOff N u) (hv : UnitOff N v) : UnitOff N (u * v) := by
  obtain ⟨hu0, a, ha, ha'⟩ := hu
  obtain ⟨hv0, b, hb, hb'⟩ := hv
  refine ⟨mul_ne_zero hu0 hv0, a + b, ?_, ?_⟩
  · refine isIntegral_of_eq (ha.mul hb) ?_
    ring
  · refine isIntegral_of_eq (ha'.mul hb') ?_
    rw [mul_inv]
    ring

theorem unitOff_prod {N : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (h : ∀ i ∈ s, UnitOff N (f i)) :
    UnitOff N (∏ i ∈ s, f i) :=
  Finset.prod_induction f (UnitOff N) (fun _ _ => unitOff_mul) (unitOff_one N) h

theorem unitOff_normalised {N q n r : ℕ} (hq : q ≠ 0) {m : ℕ} (hd : q ∣ N ^ m) (hrn : r ≤ n) {S : ℂ}
    (h1 : ‖S‖ ^ 2 = (q : ℝ) ^ (r ^ 2)) (h2 : IsIntegral ℤ S) (h3 : IsIntegral ℤ ((q : ℂ) ^ (r ^ 2) * S⁻¹)) :
    UnitOff N (((q : ℂ) ^ (n * r))⁻¹ * S) := by
  have hI : ∀ c : ℕ, IsIntegral ℤ ((c : ℕ) : ℂ) := fun c => by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (c : ℤ)))
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  have hS : S ≠ 0 := by
    rintro rfl
    have : (0 : ℝ) < (q : ℝ) ^ (r ^ 2) := pow_pos (by exact_mod_cast Nat.pos_of_ne_zero hq) _
    rw [← h1] at this
    simp at this
  obtain ⟨c, hc⟩ := hd
  have hcC : (N : ℂ) ^ m = q * c := by exact_mod_cast hc
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrn
  refine unitOff_of_two (a := m * ((r + d) * r)) (b := 0) (mul_ne_zero (inv_ne_zero (pow_ne_zero _ hqC)) hS) ?_ ?_
  · refine isIntegral_of_eq (((hI c).pow ((r + d) * r)).mul h2) ?_
    rw [pow_mul, hcC, mul_pow]
    field_simp
  · refine isIntegral_of_eq (((hI q).pow (d * r)).mul h3) ?_
    rw [mul_inv, inv_inv]
    ring

theorem card_dvd_pow (k : Type) [Field k] [Fintype k] {N : ℕ} (hN : (N : k) = 0) : ∃ m, Fintype.card k ∣ N ^ m := by
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨m, -, hm⟩ := FiniteField.card k p
  exact ⟨m, hm ▸ pow_dvd_pow_of_dvd ((CharP.cast_eq_zero_iff k p N).mp hN) _⟩

theorem unitOff_prod_gaussSum : ∀ (D : D7) [∀ PP : Pl D.host.E, Fintype (kP PP)] (Q : Finset (Pl D.host.E)) (n r : ℕ), r ≤ n → ∀ (ψP : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ) (ξ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ), (∀ PP ∈ Q, (ψP PP).IsPrimitive) → (∀ PP ∈ Q, ξ PP ≠ 1) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → UnitOff N (∏ PP ∈ Q.attach, ((Nat.card (kP PP.1) : ℂ) ^ (n * r))⁻¹ * ∑ g : GL (Fin r) (kP PP.1), (((ξ PP.1 (Matrix.GeneralLinearGroup.det g))⁻¹ : ℂˣ) : ℂ) * ψP PP.1 (Matrix.trace (g : Matrix (Fin r) (Fin r) (kP PP.1)))) := by
  intro D _ Q n r hrn ψP ξ hψ hξ N _ hN
  refine unitOff_prod _ _ ?_
  rintro ⟨PP, hPP⟩ -
  haveI := PP.isMaximal
  letI : Field (kP PP) := Ideal.Quotient.field PP.asIdeal
  have h0 : (N : kP PP) = 0 := by
    have := Ideal.Quotient.eq_zero_iff_mem.mpr (hN PP hPP)
    simpa using this
  obtain ⟨m, hm⟩ := card_dvd_pow (kP PP) h0
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.T.galois_matrix_gaussSum_eq_char_pow_mul (kP PP) (ψP PP) (ξ PP) r (hψ PP hPP) (hξ PP hPP) _ rfl
  rw [Nat.card_eq_fintype_card]
  exact unitOff_normalised Fintype.card_ne_zero hm hrn h1 h2 h3

end GlobalTheory.GaussUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicIntegralInvariantHeisenbergFirstVars
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels MeasureTheory GlobalTheory.LatVac GlobalTheory.InertVacLag GlobalTheory.InertLagChar
open scoped TensorProduct Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LagIntTransl

def liftFst {R : Type} [CommRing R] {κ : Type} (a : (κ → R) × (κ → R)) : (κ ⊕ κ → R) × (κ ⊕ κ → R) :=
  (Sum.elim a.1 0, Sum.elim a.2 0)

theorem liftFst_add {R : Type} [CommRing R] {κ : Type} (a b : (κ → R) × (κ → R)) :
    liftFst (a + b) = liftFst a + liftFst b := by
  simp only [liftFst, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  refine Prod.ext ?_ ?_ <;> funext i <;> cases i <;> simp

theorem liftFst_dot {R : Type} [CommRing R] {κ : Type} [Fintype κ] (a b : (κ → R) × (κ → R)) :
    (liftFst a).1 ⬝ᵥ (liftFst b).2 = a.1 ⬝ᵥ b.2 := by
  simp [liftFst, dotProduct, Fintype.sum_sum_type]

theorem boxFun_schr {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a : (κ → R) × (κ → R)) (φ₁ φ₂ : (κ → R) → ℂ) :
    boxFun (schr ψ a φ₁) φ₂ = schr ψ (liftFst a) (boxFun φ₁ φ₂) := by
  funext z
  simp only [boxFun, schr, liftFst, dotProduct, Fintype.sum_sum_type, Function.comp_apply, Sum.elim_inl, Sum.elim_inr,
    Pi.add_apply, Pi.zero_apply, mul_zero, add_zero, mul_assoc]
  have e1 : (z + Sum.elim a.1 0) ∘ Sum.inl = z ∘ Sum.inl + a.1 := by funext i; simp
  have e2 : (z + Sum.elim a.1 0) ∘ Sum.inr = z ∘ Sum.inr := by funext i; simp
  rw [e1, e2]
  simp

theorem diagW_schr (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ)
    (μ : @Measure (κ → Fv F v) (borel _)) (a w : (κ → Fv F v) × (κ → Fv F v)) (h : w.1 ⬝ᵥ a.2 = a.1 ⬝ᵥ w.2)
    (φ₁ φ₂ : (κ → Fv F v) → ℂ) :
    diagW ψ μ (boxFun (schr ψ a φ₁) φ₂) w = diagW ψ μ (boxFun φ₁ φ₂) (w + a) := by
  unfold diagW
  rw [boxFun_schr]
  congr 1
  funext x
  have h' : (liftFst w).1 ⬝ᵥ (liftFst a).2 = (liftFst a).1 ⬝ᵥ (liftFst w).2 := by
    rw [liftFst_dot, liftFst_dot, h]
  have := GlobalTheory.MixXEvUniq.schr_add ψ (liftFst w) (liftFst a) h' (boxFun φ₁ φ₂)
  rw [← liftFst_add] at this
  rw [show ((Sum.elim (w + a).1 0, Sum.elim (w + a).2 0) : (κ ⊕ κ → Fv F v) × (κ ⊕ κ → Fv F v)) = liftFst (w + a) from rfl,
    this]
  rfl

theorem main : ∀ (F : Type) [Field F] [NumberField F] (v : Pl F) (κ : Type) [Fintype κ] (ψ : AddChar (Fv F v) ℂ) (μ : @Measure (κ → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
    ∀ (N : ℕ) (ν : @Measure (Fin N → Fv F v) (borel _)), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
    ∀ j : (Fin N → Fv F v) →ₗ[Fv F v] (κ → Fv F v) × (κ → Fv F v), (∀ y y', (j y).1 ⬝ᵥ (j y').2 = (j y').1 ⬝ᵥ (j y).2) →
    ∀ (y₀ : Fin N → Fv F v) (φ₁ φ₂ : (κ → Fv F v) → ℂ),
      lagInt ψ μ ν j (boxFun (schr ψ (j y₀) φ₁) φ₂) = lagInt ψ μ ν j (boxFun φ₁ φ₂) := by
  intro F _ _ v κ _ ψ μ _ N ν hν j hj y₀ φ₁ φ₂
  unfold lagInt
  have h1 : ∀ y, diagW ψ μ (boxFun (schr ψ (j y₀) φ₁) φ₂) (j y) = diagW ψ μ (boxFun φ₁ φ₂) (j (y + y₀)) := fun y => by
    rw [diagW_schr F v κ ψ μ _ _ (hj y y₀), map_add]
  simp only [h1]
  letI : MeasurableSpace (Fin N → Fv F v) := borel _
  haveI : BorelSpace (Fin N → Fv F v) := ⟨rfl⟩
  exact integral_add_right_eq_self (μ := ν) (fun y => diagW ψ μ (boxFun φ₁ φ₂) (j y)) y₀

end GlobalTheory.LagIntTransl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadingMonomialProductsLinearIndependentStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.leadingMonomialProducts_linearIndependent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (F : Fin Fl.δ → Frame X.Ψ r → ℂ), (∀ j, DifferentiableOn ℂ (F j) X.dom) → (∀ j j', F j (Fl.xs j') = if j' = j then 1 else 0) → ∀ (T : ℕ) (cc : (Fin (nd X) → ℕ) → Fin Fl.δ → ℂ), (∀ x ∈ X.dom, leadM X Fl.s Fl.w0 F T (T + 1) cc x = 0) → ∀ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (nd X) (T + 1), ∀ k, cc α k = 0 := by
  first | exact @GlobalTheory.JetIndepAtPts.leadM_coeff_zero | exact GlobalTheory.JetIndepAtPts.leadM_coeff_zero | (intros; apply GlobalTheory.JetIndepAtPts.leadM_coeff_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelCharacterFiniteOrderDefiniteForms
section
set_option autoImplicit false

noncomputable section

open Formalism.L2.DIV NumberField
open scoped TensorProduct

namespace GlobalTheory.BaseCmp

section
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem isOfFinOrder_hom_of_finite {G : Type} [Group G] [Finite G] (f : G →* ℂˣ) (g : G) : IsOfFinOrder (f g) :=
  f.isOfFinOrder (isOfFinOrder_of_finite g)

theorem levFn_isOfFinOrder (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (L : LevDat E ℂ n)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : IsOfFinOrder (levFn β L x) := by
  classical
  have hPP : ∀ PP : Pl E, Finite (kP PP) := fun PP =>
    Ideal.finiteQuotientOfFreeOfNeBot PP.asIdeal PP.ne_bot
  have hU : ∀ PP : Pl E, Finite (kP PP)ˣ := fun PP => Finite.of_injective _ Units.val_injective
  have hG : ∀ (PP : Pl E) (r : ℕ), Finite (GL (Fin r) (kP PP)) := fun PP r => Finite.of_injective _ Units.val_injective
  have hG0 : Finite (G0 L.Pg L.r) := Pi.finite
  rw [← CommGroup.mem_torsion]
  unfold levFn
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ ?_ ?_) ?_
  · rw [CommGroup.mem_torsion]
    unfold ext1
    split_ifs with h
    · exact isOfFinOrder_hom_of_finite L.P.chi _
    · exact IsOfFinOrder.one
  · refine Subgroup.prod_mem _ fun PP _ => Subgroup.prod_mem _ fun c _ => ?_
    rw [CommGroup.mem_torsion]
    exact isOfFinOrder_hom_of_finite _ _
  · refine Subgroup.prod_mem _ fun PP _ => ?_
    rw [CommGroup.mem_torsion]
    exact isOfFinOrder_hom_of_finite _ _
end

set_option maxHeartbeats 1600000 in
theorem levLamRoot : LevLamRoot := by
  intro D S T B t k
  have h : IsOfFinOrder (B.levLam t k) := by
    rw [GlobalTheory.MtLatConj.levelCharacter_apply_eq_levelFunction_swap]
    exact levFn_isOfFinOrder _ _ _
  obtain ⟨m, hm, hmo⟩ := (isOfFinOrder_iff_pow_eq_one).1 h
  exact ⟨m, hm.ne', by rw [← Units.val_pow_eq_pow_val, hmo, Units.val_one]⟩

end GlobalTheory.BaseCmp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftEigenvalueLowerBoundOfWeakCharacterisation
section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.AdelicScalar GlobalTheory.LiftRows GlobalTheory.LowRow
open Formalism.IndefR.Cx GlobalTheory.BigOn
namespace GlobalTheory.LowRow

theorem lamLow_of_weak : ConjRatLift5 → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat3 D A3 T.Q.c.F) (F : Face3 D A3) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.toRealDat.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R.toRealDat i Unit (fun _ => A3.A.μ0)) (s : ℕ) (b C CH : ℝ), A3.fam3.Ok3 s → A3.fam3.TypesSep3 → R.WeakCharacterisation F → R.toRealDat.ExAt → PrimRows3 R F → (∀ i, R.phs i = 1) → IsStdChar D R.ψ (-1) → ∀ fw : FWTie T R.toRealDat κ v₀, BarTie fw → IoExt R.toRealDat → (∀ i, OMPins T R.toRealDat κ v₀ O i) → (∀ i, OneMapRow0 T R.toRealDat κ v₀ O i) → (∀ i, R.toRealDat.LUnif → PhaseTie T R.toRealDat κ v₀ O (fun i => cj (twAt D.what₂.embLL A3.A.v0) (R.phs i)) i) → (∀ j, Sizes D j b) → (∀ j, (F.Zsc (R.toCx3 F).zs).l6m j ≤ lowB D j b) → (∀ j, (R.num F C CH).l6 j ≤ (F.Zsc (R.toCx3 F).zs).l6m j) → AdelC R.toRealDat F.lv2 → PrimeToHost R.toRealDat A3.A.μ0 → ((R.toCx3 F).data F.cr true).L6 (R.num F C CH) := by
  intro hCR D G _ _ Pl0 I0 T0 A3 T _ R F κ v₀ O s b C CH hOk hsep hC hEx prim hph hstd fw hbar hio hpins hrow0 htie hsz hlow hnum hAd hPH
  obtain ⟨hcore, hok, hlinks⟩ := GlobalTheory.T.splitPart_baseLinks_of_primitiveRows R F s hOk hsep hC hEx prim hph
  have hgal : ∀ i, GalOut R.toRealDat i 1 := fun i =>
    hCR D G Pl0 T0 A3.A T R.toRealDat F.lv2 κ v₀ O 1 (GlobalTheory.Core5.of_core hcore) hstd fw hbar hio prim.unif hpins i (by
      have h1 := htie i prim.unif (hrow0 i)
      simp only [hph] at h1
      simpa using h1)
  have hext : ∀ i σ, ∃ v : (R.toRealDat.MW i σ).Vec, IsExtVec (R.toRealDat.MW i σ) v := fun i σ => ⟨v₀ i σ, (fw.hv₀ i σ).1⟩
  have htop := GlobalTheory.T.liftAdjoint_eigenvalue_lower_bound_base_embedding R.toRealDat F.lv2 s b hAd hcore hok hPH hsz
  have hform := GlobalTheory.T.rationalLift_lowerBound_off_basePlace R.toRealDat F.lv2 s b hAd hgal hcore hok hext prim.unif hlinks hPH hsz
  have h0 := GlobalTheory.T.log_liftEigenvalue_lowerBound_basePlace R F b hC prim.thmA prim.posScal htop hlow
  have h1 := GlobalTheory.T.log_liftEigenvalue_lowerBound_otherPlaces R F b hC hph prim.posScal prim.scalConj hform hlow
  intro j p v
  have hn := hnum j
  by_cases hv : v = A3.A.v0
  · subst hv
    have := h0 j p
    exact le_trans hn this
  · have := h1 j p v hv
    exact le_trans hn this

end GlobalTheory.LowRow
end
end

