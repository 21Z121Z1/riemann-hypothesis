import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0008
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0006
import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.TypePrimesOfLevel
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ConjugacyRepresentativeSystems
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0069
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0063
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0107
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AlternatingWordHypothesesEveryLatticeSurjectionStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alternatingWord_hypotheses_every_lattice_surjection : ∀ {D : D7} (L : SizeData₂ D) (HW : HWOf D.loc) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (Cx : TruncatedSeriesCountingIdentities.CoefExt D i w hw) (hG : Good (D.nbr i w hw).Kw 1 Cx.LL) (Wd : NWord (RecS.nLet i w hw)) (d : ℕ), 11 ≤ D.nd.l i → RecS.WordBase L HW i r ρ π w hw Cx hG Wd → WordsAT (D.nd.l i) Wd d → RecS.AlternatingWordLatticeSurjectionHypotheses HW i r ρ π w hw Cx hG Wd d := by
  first | exact @GlobalTheory.HTW.RecS.settingC_of_wordsAT | exact GlobalTheory.HTW.RecS.settingC_of_wordsAT | (intros; apply GlobalTheory.HTW.RecS.settingC_of_wordsAT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockRowsMemIcc
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory

theorem blockRows_mem_Icc : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), ∀ r, (Fm.D x i).R.k ≤ r → r < (Fm.D x i).R.N j → 0 ≤ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ∧ DV.nuRow (Fm.D x i) u (j + 1) (tauPl (Fm.D x i) z) r ≤ (Fm.L x i).etaSz := by
  intro eps Fm
  refine ⟨0, fun x _ _ i u j hj z r hk hr => ⟨(RowWeightLemmas.nuRow_pos _ u j hj _ r hr).le, ?_⟩⟩
  obtain ⟨q, s, hq, hs, rfl⟩ := RowWeightLemmas.block_decomp _ j r hk hr
  rw [RowWeightLemmas.nuRow_block _ u j hj _ q s hq hs, (Fm.D x i).hcW_e u]
  have h1 := (Fm.L x i).be_close (tauPl (Fm.D x i) z) ⟨q, by omega⟩ ⟨j, hj⟩
  have h2 := ((Fm.D x i).hc (tauPl (Fm.D x i) z)).gap_be ⟨q, by omega⟩
  have h3 : (0 : ℚ) ≤ ((j : ℚ) - q) * (((Fm.D x i).R.t : ℚ) + 1) := by
    have : (q : ℚ) ≤ j := by exact_mod_cast hq.le
    exact mul_nonneg (by linarith) (by positivity)
  have h4 : (0 : ℚ) ≤ (((Fm.D x i).R.t : ℚ) + 3) / 2 := by positivity
  refine le_trans ?_ h1
  refine le_trans ?_ (neg_le_abs _)
  rw [← Rat.cast_neg]
  exact Rat.cast_le.2 (by linarith)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnStabilizerTrivialLocal
section
noncomputable section

namespace GlobalTheory.Proof.ColumnStabilizerTrivialLocal

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col
open GlobalTheory.IndefiniteRowSideFullHecke

section Generic

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n n' : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def castPt (h : n = n') : DecoSet E n ST SG ≃ DecoSet E n' ST SG :=
  Equiv.cast (congrArg (fun m => DecoSet E m ST SG) h)

end Generic

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem k_eq_N (D : D7) : D.R.k = D.R.N 0 := by simp [Ranks.N]

def ptEquiv (X : ErrX D) (u : D.what₂.Word) : ConjugacyRepresentativeSystems.ColPt X u ≃ UnipotentLevelStabilisers.ColPt D X.piG (X.piT u) :=
  castPt (k_eq_N D)

def repB {X : ErrX D} (rep : ConjugacyRepresentativeSystems.ColRep X) :
    ∀ u μ, (D.chTw u μ).cls 0 → UnipotentLevelStabilisers.ColPt D X.piG (X.piT u) :=
  fun u μ c => ptEquiv X u (rep u μ c)

def repA {X : ErrX D} (rep : ∀ u μ, (D.chTw u μ).cls 0 → UnipotentLevelStabilisers.ColPt D X.piG (X.piT u)) : ConjugacyRepresentativeSystems.ColRep X :=
  fun u μ c => (ptEquiv X u).symm (rep u μ c)

theorem norm_iff (π : 𝓞 D.host.E) (g : ℕ) :
    π * UnipotentLevelStabilisers.conjInt D π = (g : 𝓞 D.host.E) ↔
      (π : D.host.E) * D.host.conj (π : D.host.E) = (g : D.host.E) := by
  rw [← RingOfIntegers.coe_injective.eq_iff, map_mul, map_natCast]
  rfl

def errOf (X₀ : ErrX D) {πg : Fin 2 → 𝓞 D.host.E} {πT : D.what₂.Word → 𝓞 D.host.E}
    (hg : UnipotentLevelStabilisers.TypeGenTie D πg) (hT : UnipotentLevelStabilisers.LevelGenTie D πT) : ErrX D where
  piG := πg
  piG_K i := (hg i).1
  piG_norm i := (norm_iff _ _).mp (hg i).2.1
  piT := πT
  piT_K u := (hT u).1
  piT_norm u := (norm_iff _ _).mp (hT u).2.1
  piT_cong u := Ideal.mem_span_singleton.mpr (hT u).2.2
  vPl := X₀.vPl
  vPl_inj := X₀.vPl_inj
  norm_mem_place_ideal := X₀.norm_mem_place_ideal

theorem typePrimesLarge_iff (D : D7) :
    UnipotentLevelStabilisers.TypePrimesLarge D ↔ ∀ i, 2 * D.R.f * D.R.k < D.host.g i - 1 :=
  forall_congr' fun i => by omega

theorem gBig_of_large (h : UnipotentLevelStabilisers.TypePrimesLarge D) : Formalism.MainNotions.StandardLattice.GBig D :=
  ⟨0, (typePrimesLarge_iff D).mp h 0⟩

def ColumnStabTrivialLocal (D : D7) (πg : Fin 2 → 𝓞 D.host.E) (πT : D.what₂.Word → 𝓞 D.host.E)
    (rep : ∀ u μ, (D.chTw u μ).cls 0 → UnipotentLevelStabilisers.ColPt D πg (πT u)) : Prop :=
  UnipotentLevelStabilisers.TypePrimesLarge D → UnipotentLevelStabilisers.TypeGenTie D πg → UnipotentLevelStabilisers.LevelGenTie D πT →
    ∀ (u : D.what₂.Word) (μ : D.what₂.Tup)
      (j : ∀ c : (D.chTw u μ).cls 0, (D.chTw u μ).stab 0 c →* UnipotentLevelStabilisers.UCol D),
      UnipotentLevelStabilisers.IsReps (rep u μ) → (∀ c, UnipotentLevelStabilisers.IsStabOf (j c) (rep u μ c)) →
        (D.chTw u μ).StabZero ∧ ∀ c, (D.chTw u μ).wt 0 c = 1

variable {Dx : DivX D} {Tw : TwForms D} (E : KerEnt D Dx Tw)

end GlobalTheory.Proof.ColumnStabilizerTrivialLocal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorizationStatement
section
open NumberField IsDedekindDomain HeckeValGen GlobalTheory.HeckeSplit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_ideleChar_local_factorization : ∀ (L : Type) [Field L] [NumberField L] (χ : Ideles L →* ℂˣ), Continuous χ → (∀ᶠ v in Filter.cofinite, UnrAt χ v) ∧ (∀ v : HeightOneSpectrum (𝓞 L), ∃ n : ℕ, ∀ x : (v.adicCompletion L)ˣ, Valued.v ((x : v.adicCompletion L) - 1) ≤ WithZero.exp (-(n : ℤ)) → χ (localIdele L v x) = 1) ∧ ∀ (x : Ideles L) (S : Finset (HeightOneSpectrum (𝓞 L))), (∀ v ∉ S, χ (localIdele L v (finPart L v x)) = 1) → χ x = χ (infIdele L (infPart L x)) * ∏ v ∈ S, χ (localIdele L v (finPart L v x)) := by
  first | exact @GlobalTheory.HeckeSplit.continuous_char_factor | exact GlobalTheory.HeckeSplit.continuous_char_factor | (intros; apply GlobalTheory.HeckeSplit.continuous_char_factor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CrystallineHodgeTateMultiplicityNeZeroOfJump
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section

namespace GlobalTheory.HTW.Rec

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_succ_le (a : ℤ) : FilV PD (LL := LL) (V := V) (a + 1) ≤ FilV PD (LL := LL) (V := V) a := by
  rintro x ⟨y, rfl⟩
  have hle : (PD.Fil (a + 1)).restrictScalars Qp ≤ (PD.Fil a).restrictScalars Qp := PD.Fil_anti a
  have hc : (TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
      ((PD.Fil a).restrictScalars Qp).subtype).comp
      (TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle)) =
      TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V)
        ((PD.Fil (a + 1)).restrictScalars Qp).subtype := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro v b
    rfl
  exact ⟨TensorProduct.AlgebraTensorModule.map (LinearMap.id : V →ₗ[LL] V) (Submodule.inclusion hle) y,
    LinearMap.congr_fun hc y⟩

theorem fildR_succ_le (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ (a + 1) ≤ FildR PD ρ τ a :=
  inf_le_inf_left _ (filV_succ_le PD a)

theorem fildR_le_DdR (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (a : ℤ) :
    FildR PD ρ τ a ≤ DdR PD ρ :=
  inf_le_left.trans inf_le_left

theorem multV_ne_zero_of_jump (ρ : Representation LL G V) [Module.Finite LL ↥(DdR PD ρ)]
    (τ : K →ₐ[Qp] LL) (a : ℤ) (h : IsJumpV PD ρ τ a) : multV PD ρ τ a ≠ 0 := by
  intro h0
  apply h
  haveI : FiniteDimensional LL ↥(FildR PD ρ τ a) :=
    Submodule.finiteDimensional_of_le (fildR_le_DdR PD ρ τ a)
  refine Submodule.eq_of_le_of_finrank_eq (fildR_succ_le PD ρ τ a) ?_
  unfold multV at h0
  omega

end General

theorem jump_multV_ne_zero : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (T : Lat K LL),
    Formalism.MainNotions.LocalSituation.fontCore (P.PD K) → ∀ τ u, IsJumpV (P.PD K) T.ρ τ u → multV (P.PD K) T.ρ τ u ≠ 0 := by
  intro l _ P K LL T hF τ u hJ
  let A : GRep ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) :=
    { V := T.V, ρ := T.ρ, cont := T.cont }
  obtain ⟨-, ⟨hfin, -⟩, -⟩ := hF ↥LL.1 ↥(OL LL) (GlobalTheory.T.goodCoefficientRing_integers_padicFiniteExtension l LL) A
  haveI : Module.Finite ↥LL.1 ↥(DdR (P.PD K) T.ρ) := hfin
  exact multV_ne_zero_of_jump (P.PD K) T.ρ τ u hJ

end GlobalTheory.HTW.Rec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstRankLeDimensionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dpst_rank_le_dimension : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL], (∀ (W : Type) [AddCommGroup W] [Module LL W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] LL W] [FiniteDimensional ℚ_[l] W] (ρW : Representation LL ↥(GK K) W), Module.rank ↥(MaximalUnramifiedExtension l) (DpstUr P ρW) ≤ finrank ℚ_[l] W) → ∀ {V V' : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V] [FiniteDimensional LL V] [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] LL V'] {ρ : Representation LL ↥(GK K) V} {ρ' : Representation LL ↥(GK K) V'} {f : V →ₗ[LL] V'} (hf : ∀ g v, f (ρ g v) = ρ' g (f v)), IsPst P ρ → f ≠ 0 → ∃ x : ↥(Dpst P ρ), GlobalTheory.Pst.DpstMap.dmap P hf x ≠ 0 := by
  first | exact @GlobalTheory.Pst.DmapNonzero.exists_dmap_ne_zero | exact GlobalTheory.Pst.DmapNonzero.exists_dmap_ne_zero | (intros; apply GlobalTheory.Pst.DmapNonzero.exists_dmap_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistDualWeylStatement
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cofactorTwist_dualWeyl : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∃ g ∈ dualWeyl R (m + 1) (m + 1) (nuDual ν), CofRel R m ν f g := by
  first | exact @GlobalTheory.ValCmp.exists_cofRel_dualWeyl | exact GlobalTheory.ValCmp.exists_cofRel_dualWeyl | (intros; apply GlobalTheory.ValCmp.exists_cofRel_dualWeyl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCofactorTwistHighestWeightStatement
section
open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cofactorTwist_highestWeight : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∃ g ∈ weyl R (m + 1) (m + 1) le_rfl (nuDual ν), CofRel R m ν (hw R le_rfl ν) g := by
  first | exact @GlobalTheory.ValCmp.exists_cofRel_hw | exact GlobalTheory.ValCmp.exists_cofRel_hw | (intros; apply GlobalTheory.ValCmp.exists_cofRel_hw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsDvrFrobeniusLift
section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

namespace GlobalTheory.UnramCompletion

variable {E : Type} [Field E] [NumberField E] (Q : HeightOneSpectrum (𝓞 E))

theorem intValuation_eq_of_notMem_sq {a : 𝓞 E} (h1 : a ∈ Q.asIdeal) (h2 : a ∉ Q.asIdeal ^ 2) :
    Q.intValuation a = exp (-1 : ℤ) := by
  have ha : a ≠ 0 := by rintro rfl; exact h2 (zero_mem _)
  have e1 := (Q.intValuation_le_pow_iff_mem a 1).2 (by simpa using h1)
  have e2 := mt (Q.intValuation_le_pow_iff_mem a 2).1 h2
  have h0 : Q.intValuation a ≠ 0 := Q.intValuation_ne_zero a ha
  rw [← exp_log h0] at e1 e2 ⊢
  rw [exp_le_exp] at e1 e2
  congr 1
  push_cast at e1 e2
  omega

theorem exists_eq_pow_mul {π : Q.adicCompletionIntegers E}
    (hπ : Valued.v (π : Q.adicCompletion E) = exp (-1 : ℤ)) (k : ℕ) {x : Q.adicCompletion E}
    (hx : Valued.v x ≤ exp (-(k : ℤ))) :
    ∃ z : Q.adicCompletionIntegers E, x = (π : Q.adicCompletion E) ^ k * z := by
  have hk : Valued.v ((π : Q.adicCompletion E) ^ k) = exp (-(k : ℤ)) := by
    rw [map_pow, hπ, ← exp_nsmul]; simp
  have h0 : (π : Q.adicCompletion E) ^ k ≠ 0 := by
    intro h; rw [h, map_zero] at hk; exact exp_ne_zero hk.symm
  refine ⟨⟨x / (π : Q.adicCompletion E) ^ k, ?_⟩, (mul_div_cancel₀ _ h0).symm⟩
  rw [mem_adicCompletionIntegers, map_div₀, hk, div_le_one₀ (zero_lt_iff.2 exp_ne_zero)]
  exact hx

theorem le_exp_neg_one_of_lt_one {γ : ℤᵐ⁰} (h : γ < 1) : γ ≤ exp (-((1 : ℕ) : ℤ)) := by
  rcases eq_or_ne γ 0 with rfl | h0
  · exact zero_le'
  rw [← exp_log h0] at h ⊢
  rw [← exp_zero, exp_lt_exp] at h
  rw [exp_le_exp]
  omega

theorem maximalIdeal_eq_span {π : Q.adicCompletionIntegers E}
    (hπ : Valued.v (π : Q.adicCompletion E) = exp (-1 : ℤ)) :
    IsLocalRing.maximalIdeal (Q.adicCompletionIntegers E) = Ideal.span {π} := by
  ext x
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, adicCompletionIntegers.isUnit_iff_valued_eq_one,
    Ideal.mem_span_singleton]
  constructor
  · intro h
    obtain ⟨z, hz⟩ := exists_eq_pow_mul Q hπ 1 (le_exp_neg_one_of_lt_one (lt_of_le_of_ne x.2 h))
    exact ⟨z, Subtype.ext (by simpa using hz)⟩
  · rintro ⟨z, rfl⟩ h
    have hz : Valued.v (z : Q.adicCompletion E) ≤ 1 := z.2
    have : Valued.v ((π : Q.adicCompletion E) * z) ≤ exp (-1 : ℤ) := by
      rw [map_mul, hπ]; exact mul_le_of_le_one_right' hz
    have h' : Valued.v ((π : Q.adicCompletion E) * z) = 1 := h
    rw [h', ← exp_zero, exp_le_exp] at this
    omega

theorem exists_global_approx {π : Q.adicCompletionIntegers E}
    (hπ : Valued.v (π : Q.adicCompletion E) = exp (-1 : ℤ)) (y : Q.adicCompletionIntegers E) (k : ℕ) :
    ∃ (x : 𝓞 E) (z : Q.adicCompletionIntegers E),
      algebraMap (𝓞 E) (Q.adicCompletionIntegers E) x = y + π ^ k * z := by
  obtain ⟨s, hs⟩ := Idele.exists_valued_sub_le Q (a := (y : Q.adicCompletion E)) y.2 k
  rw [Valuation.map_sub_swap] at hs
  obtain ⟨z, hz⟩ := exists_eq_pow_mul Q hπ k hs
  refine ⟨s, z, Subtype.ext ?_⟩
  change algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) =
    (y : Q.adicCompletion E) + (π : Q.adicCompletion E) ^ k * z
  rw [← hz]; ring

theorem card_quot {π : Q.adicCompletionIntegers E}
    (hπ : Valued.v (π : Q.adicCompletion E) = exp (-1 : ℤ)) :
    Nat.card (Q.adicCompletionIntegers E ⧸ Ideal.span {π}) = Nat.card (𝓞 E ⧸ Q.asIdeal) := by
  let f : 𝓞 E →+* Q.adicCompletionIntegers E ⧸ Ideal.span {π} :=
    (Ideal.Quotient.mk _).comp (algebraMap (𝓞 E) (Q.adicCompletionIntegers E))
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨x, z, h⟩ := exists_global_approx Q hπ y 1
    refine ⟨x, ?_⟩
    change Ideal.Quotient.mk _ _ = _
    rw [h, Ideal.Quotient.eq, add_sub_cancel_left, pow_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hk : RingHom.ker f = Q.asIdeal := by
    ext x
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ _ = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, ← maximalIdeal_eq_span Q hπ, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, SelfDualGenus.isUnit_algebraMap_iff, not_not]
  rw [← hk]
  exact (Nat.card_congr (RingHom.quotientKerEquivOfSurjective hs).toEquiv).symm

theorem ringHom_ext_of_continuous {f g : Q.adicCompletion E → Q.adicCompletion E}
    (hf : Continuous f) (hg : Continuous g)
    (h : ∀ k : E, f (algebraMap E _ k) = g (algebraMap E _ k)) : f = g :=
  (denseRange_algebraMap E Q).equalizer hf hg (funext h)

theorem exists_ringEquiv (c : E ≃+* E) (hc : Mem.Chr.ConjPl c Q Q) :
    ∃ σ : Q.adicCompletion E ≃+* Q.adicCompletion E, Continuous σ ∧
      (∀ k : E, σ (algebraMap E _ k) = algebraMap E _ (c k)) ∧ ∀ x, Valued.v (σ x) = Valued.v x := by
  obtain ⟨s, s1, s2, s3⟩ := Mem.Chr.exists_finCompl_map c hc
  obtain ⟨t, t1, t2, -⟩ := Mem.Chr.exists_finCompl_map c.symm ((Mem.Chr.conjPl_symm_iff c Q Q).2 hc)
  refine ⟨RingEquiv.ofRingHom s t ?_ ?_, s1, s2, s3⟩
  · exact DFunLike.coe_injective (ringHom_ext_of_continuous Q (s1.comp t1) continuous_id fun k => by
      simp [s2, t2])
  · exact DFunLike.coe_injective (ringHom_ext_of_continuous Q (t1.comp s1) continuous_id fun k => by
      simp [s2, t2])

theorem intAt_iff (x : E) : Formalism.L2.Col.IntAt Q x ↔ Q.valuation E x ≤ 1 := by
  constructor
  · rintro ⟨r, s, hs, h⟩
    have h1 := congrArg (Q.valuation E) h
    rw [map_mul, (valuation_eq_one_iff_notMem Q).2 hs, one_mul] at h1
    rw [h1]
    exact Q.valuation_le_one r
  · intro hx
    obtain ⟨n, d, h⟩ := Q.exists_primeCompl_mul_eq_of_integer x hx
    exact ⟨n, d, d.2, by rw [mul_comm]; exact h⟩

end GlobalTheory.UnramCompletion

open Formalism.MainNotions.G Formalism.L2.Col Formalism.BasicNotions

namespace GlobalTheory.UnramCompletion

theorem exists_completion_frobenius : ∀ (E : Type) [Field E] [NumberField E] (p n : ℕ) (Q : HeightOneSpectrum (𝓞 E)) (φ : E ≃ₐ[ℚ] E), p.Prime → ((p : ℕ) : 𝓞 E) ∈ Q.asIdeal → ((p : ℕ) : 𝓞 E) ∉ Q.asIdeal ^ 2 → (∀ x : 𝓞 E, φ • x - x ^ p ∈ Q.asIdeal) → φ ^ n = 1 → ∃ (W Qq : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : Field Qq) (_ : Algebra W Qq) (i : E →+* Qq) (σ : Qq ≃+* Qq), IsFractionRing W Qq ∧ Irreducible (p : W) ∧ Nat.card (W ⧸ Ideal.span {(p : W)}) = Nat.card (𝓞 E ⧸ Q.asIdeal) ∧ IsAdicComplete (Ideal.span {(p : W)}) W ∧ (∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) ∧ σ ^ n = 1 ∧ (∀ x : E, σ (i x) = i (φ x)) ∧ (∀ x : E, Formalism.L2.Col.IntAt Q x ↔ i x ∈ Set.range (algebraMap W Qq)) ∧ ∀ (y : W) (k : ℕ), ∃ (x : 𝓞 E) (z : W), i (x : E) = algebraMap W Qq (y + (p : W) ^ k * z) := by
  intro E _ _ p n Q φ hp h1 h2 hφ hn
  have hπ : Valued.v (((p : ℕ) : Q.adicCompletionIntegers E) : Q.adicCompletion E) = exp (-1 : ℤ) := by
    rw [← map_natCast (algebraMap (𝓞 E) (Q.adicCompletionIntegers E)),
      algebraMap_adicCompletionIntegers_apply, valuedAdicCompletion_eq_valuation',
      valuation_of_algebraMap]
    exact intValuation_eq_of_notMem_sq Q h1 h2
  have hc : Mem.Chr.ConjPl φ.toRingEquiv Q Q := by
    rw [Mem.Chr.conjPl_iff_mem]
    intro x y hxy
    have e : y = φ • x := RingOfIntegers.ext hxy
    rw [e]
    constructor
    · intro hx
      simpa using Q.asIdeal.add_mem (hφ x) (Q.asIdeal.pow_mem_of_mem hx p hp.pos)
    · intro hx
      exact Q.isPrime.mem_of_pow_mem p (by simpa using Q.asIdeal.sub_mem hx (hφ x))
  obtain ⟨σ, σ1, σ2, σ3⟩ := exists_ringEquiv Q φ.toRingEquiv hc
  have hm := maximalIdeal_eq_span Q hπ
  refine ⟨Q.adicCompletionIntegers E, Q.adicCompletion E, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, algebraMap E _, σ, inferInstance, ?_, card_quot Q hπ, ?_, ?_, ?_,
    σ2, ?_, ?_⟩
  · exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hm
  · rw [← hm]; exact SelfDualGenus.isAdicComplete_adicCompletionIntegers Q
  · intro x
    obtain ⟨a, z, ha⟩ := exists_global_approx Q hπ x 1
    have hz : σ z ∈ Q.adicCompletionIntegers E := (σ3 z).trans_le z.2
    have hx : σ x ∈ Q.adicCompletionIntegers E := (σ3 x).trans_le x.2
    have e1 : algebraMap (𝓞 E) (Q.adicCompletionIntegers E) (φ • a) =
        ⟨σ x, hx⟩ + (p : Q.adicCompletionIntegers E) * ⟨σ z, hz⟩ := by
      apply Subtype.ext
      have := congrArg (fun t : Q.adicCompletionIntegers E => σ t) ha
      simp only [pow_one] at this
      push_cast at this ⊢
      rw [map_add, map_mul, map_natCast] at this
      rw [← this]
      exact (σ2 (a : E)).symm
    have e2 : algebraMap (𝓞 E) (Q.adicCompletionIntegers E) (φ • a - a ^ p) ∈
        Ideal.span {(p : Q.adicCompletionIntegers E)} := by
      rw [← hm, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, SelfDualGenus.isUnit_algebraMap_iff,
        not_not]
      exact hφ a
    have e3 : (⟨σ x, hx⟩ : Q.adicCompletionIntegers E) - x ^ p ∈
        Ideal.span {(p : Q.adicCompletionIntegers E)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem] at e2 ⊢
      have hp0 : Ideal.Quotient.mk (Ideal.span {(p : Q.adicCompletionIntegers E)})
          (p : Q.adicCompletionIntegers E) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
      rw [map_sub (algebraMap _ _), map_pow (algebraMap _ _), e1, ha, pow_one] at e2
      simp only [map_sub, map_add, map_mul, map_pow, hp0, zero_mul, add_zero] at e2 ⊢
      exact e2
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.1 e3
    refine ⟨y, ?_⟩
    rw [← hy, add_sub_cancel]
    rfl
  · have key : ∀ m : ℕ, Continuous (σ ^ m : _ ≃+* _) ∧
        ∀ k : E, (σ ^ m : _ ≃+* _) (algebraMap E _ k) = algebraMap E _ ((φ ^ m) k) := by
      intro m
      induction m with
      | zero => exact ⟨continuous_id, fun k => rfl⟩
      | succ m ih =>
        rw [pow_succ', pow_succ']
        refine ⟨σ1.comp ih.1, fun k => ?_⟩
        change σ ((σ ^ m : _ ≃+* _) _) = _
        rw [ih.2, σ2]
        rfl
    refine DFunLike.coe_injective (ringHom_ext_of_continuous Q (key n).1 continuous_id fun k => ?_)
    rw [(key n).2, hn]
    rfl
  · intro x
    rw [intAt_iff, ← valuedAdicCompletion_eq_valuation' Q]
    exact ⟨fun h => ⟨⟨_, h⟩, rfl⟩, fun ⟨y, hy⟩ => by
      have : Valued.v (algebraMap _ (Q.adicCompletion E) y) ≤ 1 := y.2
      rwa [hy] at this⟩
  · intro y k
    obtain ⟨x, z, h⟩ := exists_global_approx Q hπ y k
    exact ⟨x, z, by rw [← h]; rfl⟩

end GlobalTheory.UnramCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIdeleClassGroupHomOpenKernelStatement
section
open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ideleClassGroupHom_open_kernel : ∀ (E : Type) [Field E] [NumberField E], ∃ cl : Ideles E →* ClassGroup (𝓞 E), IsOpen (cl.ker : Set (Ideles E)) ∧ (diagUnits E).range ⊔ infConn E ≤ cl.ker ∧ (∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnitAt v x → cl (localIdele E v x) = 1) ∧ ∀ (v : HeightOneSpectrum (𝓞 E)) x, IsUnifAt v x → cl (localIdele E v x) = ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩ := by
  first | exact @GlobalTheory.exists_ideleClassHom | exact GlobalTheory.exists_ideleClassHom | (intros; apply GlobalTheory.exists_ideleClassHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlargeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst GlobalTheory.WeilDeligne TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPotentiallySemistable_coefficientField_enlarge : ∀ {l : ℕ} [Fact l.Prime] (P : LocPrime l) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {m : ℕ} {L₁ L₂ : FinExt l} (hL : L₁.1 ≤ L₂.1) (r₁ : ↥Gw →* GL (Fin m) ↥L₁.1), IsPst P (Bw.repE L₁ r₁) → IsPst P (Bw.repE L₂ (mapRep (IntermediateField.inclusion hL).toRingHom r₁)) := by
  first | exact @GlobalTheory.PstExt.isPst_enlarge | exact GlobalTheory.PstExt.isPst_enlarge | (intros; apply GlobalTheory.PstExt.isPst_enlarge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MulSmallBoundsLeRoundedSizeBound
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW

theorem mul_small_le_bHat {D : D7} (L : SizeData₂ D) (C C' : ℝ) (j : ℕ) (hR : Roomy L C') (hC : 0 ≤ C)
    (hCC : 2 * C ≤ C') (hj : 2 * j + 2 ≤ D.host.Lw) :
    C * ((j : ℝ) + 1) * (((wHat D + sHat L + etaHat L : ℕ) : ℝ) + 1) ≤ (bHat L : ℝ) := by
  have hlow := (GlobalTheory.T.roundedSizeBound_window L C' hR).1
  obtain ⟨-, hw2, hG⟩ := GlobalTheory.T.maxNonThickSizeShifted_value_and_bounds L C' hR
  obtain ⟨h100, -, -, -, -, hbig⟩ := hR
  have hw0 : (0 : ℝ) ≤ (wHat D : ℝ) := Nat.cast_nonneg _
  have heta := L.etaSz_pos
  have ht : (0 : ℝ) ≤ (D.R.t : ℝ) := Nat.cast_nonneg _
  have hhalf : ((D.R.t : ℝ) + 1) / 2 ≤ L.sc.b' := by linarith
  have hb0 : 0 ≤ L.sc.b' := by linarith
  have hjN : (j + 1) * 2 ≤ D.host.Lw := by omega
  have hjL : ((j : ℝ) + 1) * 2 ≤ (D.host.Lw : ℝ) := by exact_mod_cast hjN
  have hj0 : (0 : ℝ) ≤ (j : ℝ) + 1 := by positivity
  push_cast
  have s1 : C * ((j : ℝ) + 1) * ((wHat D : ℝ) + sHat L + etaHat L + 1)
      ≤ C * ((j : ℝ) + 1) * (2 * L.sc.b') :=
    mul_le_mul_of_nonneg_left hG (mul_nonneg hC hj0)
  have s2 : C * ((j : ℝ) + 1) * (2 * L.sc.b') ≤ C' * ((j : ℝ) + 1) * L.sc.b' := by
    have := mul_le_mul_of_nonneg_right hCC (mul_nonneg hj0 hb0)
    nlinarith
  have s3 : C' * ((j : ℝ) + 1) * L.sc.b' + L.sc.b' ≤ C' * ((D.host.Lw : ℝ) + 1) * L.sc.b' := by
    have hk : C' * ((j : ℝ) + 1) + 1 ≤ C' * ((D.host.Lw : ℝ) + 1) := by nlinarith
    nlinarith
  linarith

end GlobalTheory.HTW
end

