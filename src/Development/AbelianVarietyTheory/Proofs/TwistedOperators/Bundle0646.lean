import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0636
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0176
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumEqProdSplitPlaceFactors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0527
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0553
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0628
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRight
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFockSSelf
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
import Formalism.GradedWeylDivisibility.FinalD

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryArchimedeanLinePairOperatorsOneParameterStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryArchimedeanLine_pair_operators_oneParameter : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
      IsStd ψ → (∀ i j, σ (X.J j i) = X.J i j) → X.J.det ≠ 0 → (∀ i j, σ (W.J j i) = -W.J i j) → W.J.det ≠ 0 →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χX n →
      ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χW d → IsHecke F E χX → IsHecke F E χW →
      M.IsWeil ψ χX χW om →
      ∀ γ ∈ Lines σ W, ∀ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
        (∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) f (T t f)) →
        (∀ (s t : ℝ) (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  first | exact @GlobalTheory.LineGroupPair.archOp_oneParam_pair | exact GlobalTheory.LineGroupPair.archOp_oneParam_pair | (intros; apply GlobalTheory.LineGroupPair.archOp_oneParam_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.VacuumVectorMovedPairStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_vector_moved_pair : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y)) (inV (frT ch.S.N p) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y))
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) := by
  first | exact @GlobalTheory.MovedDict.movedVac_isVacO | exact GlobalTheory.MovedDict.movedVac_isVacO | (intros; apply GlobalTheory.MovedDict.movedVac_isVacO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompactRealPointFockVectorSubstitutionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_compactRealPoint_fockVector_substitution : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (p : Pair T), p.InRange D.R.m →
    ∀ (pS pT : D.what₂.Tau → ℕ), (∀ ρ, pS ρ ≤ (G.pS p).rank) → (∀ ρ, pT ρ ≤ (G.pT p).rank) →
    (∀ ρ, IsCartanInv (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ)) →
    (∀ ρ, IsCartanInv (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pS p) ρ) (G.cartS W.cart p ρ) (G.onS W.onb p ρ) (pS ρ)) →
    (∀ ρ, IsONBasis (gramAt D (G.pT p) ρ) (G.onT W.cart p ρ) (G.onT W.onb p ρ) (pT ρ)) →
    ∀ f : WO (G.pS p) (G.pT p) → ℂ, IsThetaFunO W.ψ _ _ f →
    (∀ ρ, IsFockVacAt (heisO W.ψ _ _) W.θ ρ (cplxO (G.cartS W.cart p ρ) (G.onT W.cart p ρ)) f) →
    ∀ (κS : D.what₂.Tau → Matrix (Fin (G.pS p).rank) (Fin (G.pS p).rank) ℂ)
      (κT : D.what₂.Tau → Matrix (Fin (G.pT p).rank) (Fin (G.pT p).rank) ℂ),
    (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pS ρ) (κS ρ)) → (∀ ρ, GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.IsKMat (pT ρ) (κT ρ)) →
    ∀ (x : GA D (G.pS p)) (y : GA D (G.pT p)), x ∈ GinfC (G.pS p) → y ∈ GinfC (G.pT p) →
    (∀ ρ, compAt W.θ ρ (mt _ x) = G.onS W.onb p ρ * κS ρ * (G.onS W.onb p ρ)⁻¹) →
    (∀ ρ, compAt W.θ ρ (mt _ y) = G.onT W.onb p ρ * κT ρ * (G.onT W.onb p ρ)⁻¹) →
    ∀ c : ℂ, W.om p (x, y) f = c • f → ∀ Q : PolF D (G.pT p).rank (G.pS p).rank,
    W.om p (x, y) (W.fock p f Q) = c • W.fock p f (GlobalTheory.RowReal.fockSubAll pS pT κS κT Q) := by
  first | exact @GlobalTheory.RowReal.om_fock_compact_all | exact GlobalTheory.RowReal.om_fock_compact_all | (intros; apply GlobalTheory.RowReal.om_fock_compact_all <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLatticeVacuumEqProdSplitPlaceFactorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.RowVertexInv GlobalTheory.SplitFlip
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.RowVacScalar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilLatticeVacuum_eq_prod_splitPlace_factors : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}, IsWeilDatumO ψ S T χS χT om →
    ∀ {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)},
    IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ (P : Finset (Pl D.host.E)), (∀ w ∈ P, Formalism.L2.NTheta.IsIdemAt (GlobalTheory.RowVacScalar.idemAt w) w) →
    Set.InjOn (fun w : Pl D.host.E => w.under (𝓞 D.host.F)) (P : Set (Pl D.host.E)) →
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), (∀ w ∈ P, w.under (𝓞 D.host.F) ≠ v) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS v ∧ GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT v) →
    ∀ g ∈ GfC S, ∀ h ∈ GfC T,
    (∀ y, y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt S g).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛS : Set (Fin S.rank → D.host.E))) →
    (∀ y, y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E)) ↔
      ((Formalism.L2.Theta.mt T h).map (finPart D)).mulVec y ∈ latHat D.host.F D.host.E (ΛT : Set (Fin T.rank → D.host.E))) →
    ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
    IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f →
    om (g, h) f = (∏ w ∈ P, ((splitFacO χS χT (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) S g)
      (GlobalTheory.RowVacScalar.detIdl (GlobalTheory.RowVacScalar.idemAt w) T h) : Circle) : ℂ)) • f := by
  first | exact @GlobalTheory.LatStabScalar.om_eq_prod_splitFac | exact GlobalTheory.LatStabScalar.om_eq_prod_splitFac | (intros; apply GlobalTheory.LatStabScalar.om_eq_prod_splitFac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineOneParameter
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open GlobalTheory.ArchUniq MeasureTheory
open scoped SchwartzMap Classical

namespace GlobalTheory.ArchFamily

theorem exists_family : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om → ∀ γ ∈ Lines σ W,
    ∃ T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d),
      (∀ t (f : SInf F (Fin n × Fin d)), Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑(T t f)) ∧
      (∀ s t (f : SInf F (Fin n × Fin d)), T (s + t) f = T s (T t f)) ∧ ∀ f : SInf F (Fin n × Fin d), T 0 f = f := by
  intro hP F E _ _ _ _ _ σ n d X W M ψ χX χW om hcm hstd hW γ hγ
  obtain ⟨r₀, hR, hinj⟩ := GlobalTheory.T.exists_admissible_finiteFactor_archimedeanSchwartz (F := F) (Fin n × Fin d)
  have hex : ∀ (t : ℝ) (f : SInf F (Fin n × Fin d)), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, γ (Multiplicative.ofAdd t))) ⇑f ⇑f₁ :=
    fun t f => GlobalTheory.T.weil_action_unitary_compact hP M ψ χX χW om hcm hstd hW _ (hγ.2 _) f
  choose S hS using hex
  have key : ∀ t (f : SInf F (Fin n × Fin d)),
      om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) ⇑f r₀) = tens (evI F) ⇑(S t f) r₀ :=
    fun t f => hS t f r₀ (hR f)
  have tadd : ∀ f g : SInf F (Fin n × Fin d),
      tens (evI F) ⇑(f + g) r₀ = tens (evI F) ⇑f r₀ + tens (evI F) ⇑g r₀ := by
    intro f g; funext x; simp [tens, add_mul]
  have tsmul : ∀ (c : ℂ) (f : SInf F (Fin n × Fin d)),
      tens (evI F) ⇑(c • f) r₀ = c • tens (evI F) ⇑f r₀ := by
    intro c f; funext x; simp [tens, mul_assoc]
  let T : ℝ → SInf F (Fin n × Fin d) →ₗ[ℂ] SInf F (Fin n × Fin d) := fun t =>
    { toFun := S t
      map_add' := fun f g => hinj _ _ (by rw [← key, tadd, map_add, key, key, tadd])
      map_smul' := fun c f => hinj _ _ (by rw [← key, tsmul, map_smul, key, RingHom.id_apply, tsmul]) }
  refine ⟨T, fun t f => hS t f, fun s t f => hinj _ _ ?_, fun f => hinj _ _ ?_⟩
  · show tens (evI F) ⇑(S (s + t) f) r₀ = tens (evI F) ⇑(S s (S t f)) r₀
    have hmul : ((1 : UA σ X.J), γ (Multiplicative.ofAdd (s + t))) =
        ((1 : UA σ X.J), γ (Multiplicative.ofAdd s)) * ((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) := by
      rw [ofAdd_add, map_mul, Prod.mk_mul_mk, one_mul]
    rw [← key, hmul, map_mul, Module.End.mul_apply, key, key]
  · show tens (evI F) ⇑(S 0 f) r₀ = tens (evI F) ⇑f r₀
    have h1 : ((1 : UA σ X.J), γ (Multiplicative.ofAdd (0 : ℝ))) = 1 := by
      rw [ofAdd_zero, map_one]; rfl
    rw [← key, h1, map_one, Module.End.one_apply]

end GlobalTheory.ArchFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeylKTypeTensorEqContragredientTranslatesSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open GlobalTheory.ChiGrid GlobalTheory.RowReal GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.DualWeylTensor

open MvPolynomial

def domOf {n : ℕ} (w : ℕ → ℤ) (h : ∀ a : ℕ, a + 1 < n → w (a + 1) ≤ w a) : Formalism.BasicNotions.DomWeight n where
  w i := w i
  anti := by
    intro i j hij
    obtain ⟨i, hi⟩ := i
    obtain ⟨j, hj⟩ := j
    simp only [Fin.mk_le_mk] at hij
    show w j ≤ w i
    have key : ∀ k, i ≤ k → k < n → w k ≤ w i := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => intro _; exact le_rfl
      | succ k hik ih => intro hk1; exact (h k hk1).trans (ih (by omega))
    exact key j hij hj

theorem rev_cast {n : ℕ} (i : Fin n) : ((Fin.rev i : ℕ) : ℝ) = (n : ℝ) - 1 - (i : ℕ) := by
  have := i.2
  rw [Fin.val_rev, Nat.cast_sub (by omega : (i : ℕ) + 1 ≤ n)]
  push_cast; ring

theorem lam_eq {n : ℕ} (lamH : Fin n → ℝ) (lam : ℕ → ℤ)
    (hl : ∀ i : Fin n, (lam i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lamH) (Fin.rev i)) (i : Fin n) :
    (lam i : ℝ) = -lamH (Fin.rev i) - ((n : ℝ) - 1) / 2 + (i : ℕ) := by
  rw [hl i, GlobalTheory.ConjTypeW.lowK_allPos, rev_cast]; ring

theorem step {n : ℕ} (lamH : Fin n → ℝ) (hH : StrictAnti lamH) (lam : ℕ → ℤ)
    (hl : ∀ i : Fin n, (lam i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lamH) (Fin.rev i))
    (a : ℕ) (ha : a + 1 < n) : lam (a + 1) ≤ lam a := by
  have h1 := lam_eq lamH lam hl ⟨a, by omega⟩
  have h2 := lam_eq lamH lam hl ⟨a + 1, ha⟩
  have h3 : lamH (Fin.rev ⟨a, by omega⟩) < lamH (Fin.rev ⟨a + 1, ha⟩) :=
    hH (by rw [Fin.rev_lt_rev]; simp [Fin.lt_def])
  simp only [Fin.val_mk] at h1 h2
  have h4 : ((lam (a + 1) : ℤ) : ℝ) < (lam a : ℝ) + 1 := by rw [h1, h2]; push_cast; linarith
  have h5 : lam (a + 1) < lam a + 1 := by exact_mod_cast h4
  omega

theorem rho_cond {n : ℕ} (lamH : Fin n → ℝ) (hH : StrictAnti lamH) (lam : ℕ → ℤ)
    (hl : ∀ i : Fin n, (lam i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) lamH) (Fin.rev i)) (i : Fin n) :
    -lamH (Fin.rev i) = ((domOf (n := n) lam (step lamH hH lam hl)).w (Fin.cast rfl i) : ℝ) +
      ((Formalism.BasicNotions.rhoVec n i : ℚ) : ℝ) := by
  show -lamH (Fin.rev i) = ((lam (Fin.cast rfl i : ℕ) : ℤ) : ℝ) + _
  rw [Fin.val_cast, lam_eq lamH lam hl i, Formalism.BasicNotions.rhoVec]
  push_cast; ring

theorem forms_ten_eq {ι : Type} [Fintype ι] {n : ℕ} (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.L2.Forms.ten f = Formalism.L2.DIV.ten f := rfl

theorem polyAction_ten' {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → Formalism.BasicNotions.DomWeight n)
    (h : ι → GL (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.L2.DIV.actP lam h (Formalism.L2.DIV.ten f) = Formalism.L2.DIV.ten fun τ => Formalism.BasicNotions.sqAct ℂ n (lam τ) (h τ) (f τ) := by
  have hb := (Formalism.GradedWeylDivisibility.blockActTensor ℂ ℂ ι n n (fun τ => ((h τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ)).1
  simp only [Formalism.L2.DIV.actP, Formalism.L2.DIV.ten, Formalism.L2.DIV.detTwK, Formalism.L2.DIV.trAct, Formalism.BasicNotions.sqAct, LinearMap.smul_apply,
    AlgHom.toLinearMap_apply, map_prod, hb, map_smul]
  rw [Finset.prod_smul]

theorem sqAct_invTr {n : ℕ} (lam : Formalism.BasicNotions.DomWeight n) (u : Matrix.unitaryGroup (Fin n) ℂ)
    (f : MvPolynomial (Fin n × Fin n) ℂ) :
    Formalism.BasicNotions.sqAct ℂ n lam (Formalism.BasicNotions.inside₂ ℂ n (GlobalTheory.Branching.unitaryIncl n u)) f =
      ((u : Matrix (Fin n) (Fin n) ℂ).det ^ (-lam.detShift)) • Formalism.GradedWeylDivisibility.rowAct ℂ (u : Matrix (Fin n) (Fin n) ℂ)ᴴ f := by
  have hm : ((Formalism.BasicNotions.inside₂ ℂ n (GlobalTheory.Branching.unitaryIncl n u) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      ((u : Matrix (Fin n) (Fin n) ℂ)ᴴ)ᵀ := by
    show (((GlobalTheory.Branching.unitaryIncl n u)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)ᵀ = _
    rw [← map_inv, GlobalTheory.Branching.unitaryIncl_coe]
    rfl
  have hu : (u : Matrix (Fin n) (Fin n) ℂ) * (u : Matrix (Fin n) (Fin n) ℂ)ᴴ = 1 := by
    have := (Matrix.mem_unitaryGroup_iff).1 u.2
    rwa [Matrix.star_eq_conjTranspose] at this
  have hd : (u : Matrix (Fin n) (Fin n) ℂ)ᴴ.det = ((u : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ := by
    have h1 : (u : Matrix (Fin n) (Fin n) ℂ).det * (u : Matrix (Fin n) (Fin n) ℂ)ᴴ.det = 1 := by
      rw [← Matrix.det_mul, hu, Matrix.det_one]
    exact (eq_inv_of_mul_eq_one_right h1)
  unfold Formalism.BasicNotions.sqAct Formalism.BasicNotions.detPow
  rw [hm, Matrix.transpose_transpose, Units.val_zpow_eq_zpow_val, Matrix.GeneralLinearGroup.val_det_apply, hm,
    Matrix.det_transpose, hd, inv_zpow', zpow_neg]

theorem main : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (H : ι → Type) [∀ τ, NormedAddCommGroup (H τ)] [∀ τ, InnerProductSpace ℂ (H τ)] [∀ τ, FiniteDimensional ℂ (H τ)] (σ : ∀ τ, Matrix (Fin n) (Fin n) ℂ → (H τ →L[ℂ] H τ)) (lamH : ι → Fin n → ℝ) (lam : ι → ℕ → ℤ), (∀ τ, StrictAnti (lamH τ)) → (∀ τ, Formalism.MainNotions.S.IsURepOn (Formalism.MainNotions.S.UJset (Formalism.MainNotions.S.allPos n)) (σ τ)) → (∀ τ, Formalism.MainNotions.S.IsKTypeOf (Formalism.MainNotions.S.allPos n) (σ τ) (Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) ⊤) → (∀ τ (i : Fin n), (lam τ i : ℝ) = -(Formalism.QuantumDeterminants.lowK (Formalism.MainNotions.S.allPos n) (lamH τ)) (Fin.rev i)) → ∃ Φ : Module.Dual ℂ (weylSub n lam) ≃ₗ[ℂ] ⨂[ℂ] τ, H τ, ∀ (u : UG ι n) (φ : Module.Dual ℂ (weylSub n lam)), Φ ((weylRep n lam).dual u φ) = PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) (Φ φ) := by
  intro ι _ _ n H _ _ _ σ lamH lam hH hU hK hl
  classical
  let lam' : ι → Formalism.BasicNotions.DomWeight n := fun τ => domOf (lam τ) (step (lamH τ) (hH τ) (lam τ) (hl τ))
  have hlw : ∀ τ (i : Fin n), (lam' τ).w i = lam τ i := fun _ _ => rfl
  haveI : FiniteDimensional ℂ (Formalism.L2.DIV.VV ℂ lam') := Module.Finite.of_basis (Formalism.L2.DIV.bVV ℂ lam')
  have hj := fun τ => GlobalTheory.DualWeylType.dual_weyl_type n n rfl (lam' τ) (H τ) (σ τ) (lamH τ) (hU τ) (hK τ)
    (rho_cond (lamH τ) (hH τ) (lam τ) (hl τ))
  choose j d b hin hon hortho heq using hj
  obtain ⟨Jt, hinj, hrange, hpure⟩ := GlobalTheory.TenInj.main ι n lam' H j d b hin hon hortho
  have hR : LinearMap.range Jt = Formalism.L2.DIV.VV ℂ lam' := hrange.trans (GlobalTheory.TrueBranch.cSpan_eq_VV lam')
  let E : (⨂[ℂ] τ, H τ) ≃ₗ[ℂ] Formalism.L2.DIV.VV ℂ lam' :=
    (LinearEquiv.ofInjective Jt hinj).trans (LinearEquiv.ofEq _ _ hR)
  have hE : ∀ x, (E x : Formalism.L2.DIV.Pol ℂ ι n) = Jt x := fun _ => rfl
  let U : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.UG ι n → (ι → GL (Fin n) ℂ) := fun u τ => GlobalTheory.Branching.unitaryIncl n (u τ)
  have hEq : ∀ (u : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.UG ι n) x,
      E (PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) x) =
        Formalism.L2.DIV.rhoK lam' (Formalism.L2.DIV.invTrK (U u)) (E x) := by
    intro u x
    apply Subtype.ext
    rw [hE]
    show Jt _ = Formalism.L2.DIV.actP lam' _ (Jt x)
    have hlin : Jt ∘ₗ PiTensorProduct.map (fun τ => ((σ τ (u τ) : H τ →L[ℂ] H τ) : H τ →ₗ[ℂ] H τ)) =
        Formalism.L2.DIV.actP lam' (Formalism.L2.DIV.invTrK (U u)) ∘ₗ Jt := by
      apply PiTensorProduct.ext
      apply MultilinearMap.ext
      intro y
      simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod, hpure]
      rw [forms_ten_eq, forms_ten_eq, polyAction_ten']
      congr 1
      funext τ
      have hs : ((u τ : Matrix (Fin n) (Fin n) ℂ)).submatrix (Fin.cast rfl) (Fin.cast rfl) =
          (u τ : Matrix (Fin n) (Fin n) ℂ) := by ext; simp
      have h1 := heq τ (u τ) (u τ).2 (y τ)
      rw [hs] at h1
      rw [ContinuousLinearMap.coe_coe, h1]
      exact (sqAct_invTr (lam' τ) (u τ) _).symm
    exact LinearMap.congr_fun hlin x
  obtain ⟨A, hA⟩ := GlobalTheory.CoefPsi.exists_equiv n lam lam' hlw
  refine ⟨(A.symm.dualMap.trans (Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).symm).trans E.symm, fun u φ => ?_⟩
  have hU' : (fun τ => GlobalTheory.Branching.unitaryIncl n ((u⁻¹ : GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries.UG ι n) τ)) = (U u)⁻¹ := by
    funext τ
    simp [U, Pi.inv_apply, map_inv]
  have key : ∀ ℓ : Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam'), weylRep n lam u⁻¹ (A.symm ℓ) =
      A.symm (ℓ ∘ₗ Formalism.L2.DIV.rhoK lam' (Formalism.L2.DIV.invTrK (U u))) := by
    intro ℓ
    apply A.injective
    rw [hA, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply, hU',
      map_inv (Formalism.L2.DIV.invTrK (K := ℂ) (ι := ι) (n := n)), inv_inv]
  obtain ⟨v, hvv⟩ : ∃ v, (Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).symm (A.symm.dualMap φ) = v := ⟨_, rfl⟩
  have hv : ∀ ℓ : Module.Dual ℂ (Formalism.L2.DIV.VV ℂ lam'), ℓ v = φ (A.symm ℓ) := by
    intro ℓ
    have h2 := congrArg (fun X => X ℓ) ((Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).apply_symm_apply (A.symm.dualMap φ))
    rw [hvv] at h2
    simpa [Module.evalEquiv_apply] using h2
  apply E.injective
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  rw [hvv, hEq, LinearEquiv.apply_symm_apply]
  apply (Module.evalEquiv ℂ (Formalism.L2.DIV.VV ℂ lam')).injective
  rw [LinearEquiv.apply_symm_apply]
  ext ℓ
  rw [Module.evalEquiv_apply, Module.Dual.eval_apply, LinearEquiv.dualMap_apply, Representation.dual_apply,
    Module.Dual.transpose_apply, LinearMap.comp_apply, key, ← hv]
  rfl

end GlobalTheory.DualWeylTensor
end
end

