import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0496
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0316
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1947
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfExt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1820
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0883
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableThetaKernelWeilRange
section
open scoped TensorProduct ENNReal Matrix Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Doubling GlobalTheory.Eis GlobalTheory GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilThetaInt

theorem integrable_thetaKO : GlobalTheory.Published.WeilThetaConvergence → ∀ (D : D7) (A B : HSp D) (m : Measure (GA D B)), m.IsHaarMeasure → 1 ≤ A.rank → (Formalism.MainNotions.SchurIrreducible.wittIdx B = 0 ∨ A.rank + Formalism.MainNotions.SchurIrreducible.wittIdx B < B.rank) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χ : (AE D)ˣ →* Circle) (ω : GA D (dblSp A) × GA D B →* Module.End ℂ (WO (dblSp A) B → ℂ)), IsWeilDatumO ψ (dblSp A) B 1 χ ω → ∀ f, IsThetaFunO ψ (dblSp A) B f → ∀ g, Integrable (descend (GQ B) fun h => thetaKO ω g h f) (autMeasure B m) := by
  intro hP D A B m hm hA hw ψ χ ω hW f hf g
  obtain ⟨θ, hθ⟩ := GlobalTheory.AdelicU.exists_isInfFam D
  obtain ⟨ν, 𝓨, hν⟩ := GlobalTheory.Size.exists_isCovolOne A B
  have hF := hW.om_pres (g, 1) f hf
  have hS : GlobalTheory.Core.Rk.SW.sch ψ A B ν 𝓨 (ω (g, 1) f) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz.schwartzA θ B.rank A.rank :=
    (GlobalTheory.SchSchwartzAll.schSchwartz D ψ hW.std θ hθ A B ν 𝓨 hν).1 _ hF
  have hfin := hP D A.rank B hA hw θ hθ m hm ⟨_, hS⟩
  have hleft := GlobalTheory.SiegelFormula.leftInv_thetaKO hW hf g
  have hcont : Continuous fun h => thetaKO ω g h f :=
    (hW.om_cont f hf 0).comp (Continuous.prodMk_right g)
  refine ⟨?_, ?_⟩
  · rw [autMeasure, aestronglyMeasurable_quotMeasure_iff_lift, hleft.lift_descend]
    exact hcont.aestronglyMeasurable
  · refine lt_of_le_of_lt (lintegral_mono fun q => ?_) hfin
    simp only [GlobalTheory.AutomorphicL2Unitary.descend, GlobalTheory.SiegelFormula.absTheta]
    rw [GlobalTheory.StdUnn.thetaKO_eq_tsum_sch D ψ A B χ ω hW ν 𝓨 hν f hf g]
    exact enorm_tsum_le_tsum_enorm

end GlobalTheory.WeilThetaInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.TopFlip

variable {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc}

variable (G) in

abbrev spX (i j : ℕ) : HSp D := GlobalTheory.Doubling.hsum (spV G i j) (spV₁ G i j)

variable (G) in

def latX (i j : ℕ) : Submodule (𝓞 D.host.E) (Fin (spX G i j).rank → D.host.E) :=
  GlobalTheory.Doubling.sumLat finSumFinEquiv (G.Λ (.grid i (j + 1))) (G.Λ (.grid (i + 1) j))

variable (G) in

def homLatA (i j : ℕ) : AddSubgroup (WO (spW G i j) (spX G i j)) :=
  latO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j) (G.Λ (.grid (i + 1) (j + 1))) (latX G i j) fun _ => True

variable (G) in

def homLatB (i j : ℕ) : AddSubgroup (WO (spW₁ G i j) (spX G i j)) :=
  latO (spW₁ G i j) (spX G i j) (G.Λ (.grid i j)) (latX G i j) fun _ => True

variable (G) in

def orderingsOnSpW (i j : ℕ) : Set (WO (spW G i j) (spX G i j)) :=
  {x | GlobalTheory.RouteSeesaw.topR (A := spV G i j) (B := spV₁ G i j) x ∈
      latO (negSp (spW G i j)) (spV G i j) (G.Λ (.grid (i + 1) (j + 1))) (G.Λ (.grid i (j + 1))) (fun _ => True) ∧
    GlobalTheory.RouteSeesaw.adjM (spW G i j) (spV₁ G i j) (GlobalTheory.RouteSeesaw.botR (A := spV G i j) (B := spV₁ G i j) x) ∈
      latO (spV₁ G i j) (spW G i j) (G.Λ (.grid (i + 1) j)) (G.Λ (.grid (i + 1) (j + 1))) fun _ => True}

variable (G) in

def orderingsOnSpWOne (i j : ℕ) : Set (WO (spW₁ G i j) (spX G i j)) :=
  {y | GlobalTheory.RouteSeesaw.topR (A := spV G i j) (B := spV₁ G i j) y ∈
      latO (spW₁ G i j) (spV G i j) (G.Λ (.grid i j)) (G.Λ (.grid i (j + 1))) (fun _ => True) ∧
    GlobalTheory.RouteSeesaw.adjM (spW₁ G i j) (negSp (spV₁ G i j)) (GlobalTheory.RouteSeesaw.botR (A := spV G i j) (B := spV₁ G i j) y) ∈
      latO (negSp (spV₁ G i j)) (spW₁ G i j) (G.Λ (.grid (i + 1) j)) (G.Λ (.grid i j)) fun _ => True}

section Vac

variable {W : G.Weil} (ρ : RealMatch W) (i j : ℕ)

def vacA : WO (spW G i j) (spX G i j) → ℂ :=
  GlobalTheory.RouteSeesaw.box2 (S := negSp (spW G i j)) (A := spV G i j) (B := spV₁ G i j) (ρ.vX i (j + 1))
    fun y => ρ.vT (i + 1) j (GlobalTheory.RouteSeesaw.adjM (spW G i j) (spV₁ G i j) y)

def vacB : WO (spW₁ G i j) (spX G i j) → ℂ :=
  GlobalTheory.RouteSeesaw.box2 (S := spW₁ G i j) (A := spV G i j) (B := spV₁ G i j) (ρ.vT i j)
    fun y => ρ.vX i j (GlobalTheory.RouteSeesaw.adjM (spW₁ G i j) (negSp (spV₁ G i j)) y)

theorem datumA_vac (t : T) : datumA W (t := t) (i := i) (j := j) (Finsupp.single (((), ρ.vX i (j + 1)), ρ.vT (i + 1) j) 1) = vacA ρ i j := by
  unfold datumA
  erw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]
  rfl

theorem datumB_vac (t : T) : datumB W (t := t) (i := i) (j := j) (Finsupp.single (((), ρ.vT i j), ρ.vX i j) 1) = vacB ρ i j := by
  unfold datumB
  erw [Finsupp.sum_single_index (by exact zero_smul ℂ _), one_smul]
  rfl

end Vac

section Coord

variable (B : Frames G) (t : T) (i j : Fin D.R.m)

def frX : GL (Fin (spX G i j).rank) (EAf D) := GlobalTheory.Doubling.blkGL finSumFinEquiv (B.β i (j + 1), -B.β (i + 1) j)

variable (G) in

def colX (w : Pl D.host.E) : Fin (spX G i j).rank ≃ (locGrid G t w).Cols i j :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr (finCongr (rank_vertex G t w (X := (i, j + 1)) ⟨i.2.le, j.2⟩).symm)
    (finCongr (rank_vertex G t w (X := (i + 1, j)) ⟨i.2, j.2.le⟩).symm))

variable (G) in

def ordX (w : Pl D.host.E) :
    (locGrid G t w).Cols i j ≃ Fin ((locGrid G t w).rank (i + 1, j + 1) + (locGrid G t w).rank (i, j)) :=
  (stdSplit ((locGrid G t w).rank_square i j)).symm.trans finSumFinEquiv

variable (G) in

abbrev MatA (w : Pl D.host.E) : Type :=
  Matrix (Fin ((locGrid G t w).rank (i + 1, j + 1))) ((locGrid G t w).Cols i j) (Kw w)

variable (G) in

abbrev MatB (w : Pl D.host.E) : Type := Matrix (Fin ((locGrid G t w).rank (i, j))) ((locGrid G t w).Cols i j) (Kw w)

def linA (w : Pl D.host.E) (x : WO (spW G i j) (spX G i j)) : MatA G t i j w :=
  reindex (finCongr (rankW G t i j w)) (colX G t i j w)
    ((frMapO (spW G i j) (spX G i j) (B.β (i + 1) (j + 1)) (frX B i j) x).map (cpt w))ᵀ

def linB (w : Pl D.host.E) (y : WO (spW₁ G i j) (spX G i j)) : MatB G t i j w :=
  reindex (finCongr (rankW₁ G t i j w)) (colX G t i j w)
    ((frMapAdj (spW₁ G i j) (spX G i j) (B.β i j) (frX B i j) y).map (cpt w))

open Classical in

def prodA (ε : AE D) (Ξ : ∀ w, MatA G t i j w → ℂ) (x : WO (spW G i j) (spX G i j)) : ℂ :=
  if IsHalf ε x then ∏ w ∈ locPl G t, Ξ w (linA B t i j w x) else 0

open Classical in

def prodB (ε : AE D) (Ψ : ∀ w, MatB G t i j w → ℂ) (y : WO (spW₁ G i j) (spX G i j)) : ℂ :=
  if IsHalf (cA D ε) y then ∏ w ∈ locPl G t, Ψ w (linB B t i j w y) else 0

variable {W : G.Weil} (ρ : RealMatch W)

def IsLinA (ε : AE D) (Ξ : ∀ w, MatA G t i j w → ℂ) (F : WO (spW G i j) (spX G i j) → ℂ) : Prop :=
  IsThetaAt W.ψ (symplO (GlobalTheory.Grid.neg (spW G i j)) (spX G i j)) (heisO W.ψ (GlobalTheory.Grid.neg (spW G i j)) (spX G i j)) ε
    (homLatA G i j) 1 (vacA ρ i j) (prodA B t i j ε Ξ) F

def IsLinB (ε : AE D) (Ψ : ∀ w, MatB G t i j w → ℂ) (F : WO (spW₁ G i j) (spX G i j) → ℂ) : Prop :=
  IsThetaAt W.ψ (symplO (spW₁ G i j) (spX G i j)) (heisO W.ψ (spW₁ G i j) (spX G i j)) (cA D ε)
    (homLatB G i j) 1 (vacB ρ i j) (prodB B t i j ε Ψ) F

end Coord

section Model

variable {i j : ℕ} (e : Num G i j)

def ptA (u : Matrix (Fin (spW G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : WO (spW G i j) (spX G i j) :=
  (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) (incM (GlobalTheory.Grid.sgn true (spW G i j)).gram) :
    Matrix (Fin (_ + _)) (Fin _) (AE D))

def ptB (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) : WO (spW₁ G i j) (spX G i j) :=
  (HMul.hMul (uᵀ.submatrix (e.symm.trans finSumFinEquiv).symm id) (incM (spW₁ G i j).gram) :
    Matrix (Fin (_ + _)) (Fin _) (AE D))

end Model

section Charts

variable (W : G.Weil) (B : Frames G) (t : T) {i j : Fin D.R.m} (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (w : Pl D.host.E)

variable (G i j) in

abbrev ToA : Type :=
  ((Fin (spW G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
    (MatA G t i j w → ℂ)

variable (G i j) in

abbrev ToB : Type :=
  ((Fin (spW₁ G i j).rank × Fin ((spW G i j).rank + (spW₁ G i j).rank) → Fv D.host.F (w.under (𝓞 D.host.F))) → ℂ) →ₗ[ℂ]
    (MatB G t i j w → ℂ)

def IsLinModelA (ι : ToA G t i j w) : Prop :=
  IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) {u | IsHalf (atPl w 1) (ptA e u)} {u | IsHalf (cA D (atPl w 1)) (ptA e u)}
    (fun u => linA B t i j w (ptA e u)) ι

def IsLinModelB (ι : ToB G t i j w) : Prop :=
  IsLagrModel Γ.M' W.ψ (w.under (𝓞 D.host.F)) {u | IsHalf (cA D (atPl w 1)) (ptB e u)} {u | IsHalf (atPl w 1) (ptB e u)}
    (fun u => linB B t i j w (ptB e u)) ι

def IsMixModelA (ι : ToA G t i j w) : Prop :=
  IsLagrModel Γ.M W.ψ (w.under (𝓞 D.host.F)) (mixHalf e (atPl w 1)) (mixHalf e (cA D (atPl w 1))) (mixCo B t e w) ι

def IsMixModelB (ι : ToB G t i j w) : Prop :=
  IsLagrModel Γ.M' W.ψ (w.under (𝓞 D.host.F)) (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w) ι

end Charts

section ZetaNonvanishing₂

variable (G) (t : T) (i j : Fin D.R.m) (w : Pl D.host.E)

def zetaA (Ξ : MatA G t i j w → ℂ) : GL ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  bigP (haarVol (KO (Kw w) _)) (unifAt w) (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j) 1 Ξ

def zetaB (Ψ : MatB G t i j w → ℂ) : GL ((locGrid G t w).Cols i j) (Kw w) → ℂ :=
  smallP (haarVol (KO (Kw w) _)) (stdSplit ((locGrid G t w).rank_square i j)) ((locGrid G t w).nu i j)
    ((locGrid G t w).nu i j * 1) Ψ

def levVol : ℝ :=
  (haarVol (KO (Kw w) (Fin ((locGrid G t w).rank (i, j))))).real ((givenLevel G t w (i, j)).map invT : Subgroup _)

end ZetaNonvanishing₂

section Std

variable (B : Frames G) (t : T) {i j : Fin D.R.m} (X : TriG G i j) (w : Pl D.host.E)

def chA : GL (Fin ((locGrid G t w).rank (i + 1, j + 1))) (Kw w) :=
  GlobalTheory.StepData.reGL (finCongr (rankW G t i j w)) (invT ((loc w X.rA.β)⁻¹ * loc w (B.β (i + 1) (j + 1))))

def chB : GL (Fin ((locGrid G t w).rank (i, j))) (Kw w) :=
  GlobalTheory.StepData.reGL (finCongr (rankW₁ G t i j w))
    (Units.map (Matrix.scalar (Fin (spW₁ G i j).rank)).toMonoidHom
        (Units.mk0 (xiAt w) ((_root_.map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero)) *
      ((loc w X.rA'.β)⁻¹ * loc w (B.β i j)))

def chX : GL ((locGrid G t w).Cols i j) (Kw w) :=
  GlobalTheory.StepData.reGL (colX G t i j w) ((loc w (frX B i j))⁻¹ * loc w X.rW.β)

def locFst (Z : MatA G t i j w) : ℂ :=
  GlobalTheory.StdPairCone.stdA ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _
    (reindex (Equiv.refl _) (ordX G t i j w) ((chA B t X w).val * Z * (invT (chX B t X w)).val))

def locSnd (Y : MatB G t i j w) : ℂ :=
  GlobalTheory.StdPairCone.stdB ((locGrid G t w).nu i j) (unifAt w) (X.c t w) _ _
    (reindex (Equiv.refl _) (ordX G t i j w) ((chB B t X w).val * Y * (chX B t X w).val))

end Std

end GlobalTheory.TopFlip

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsModelsExt
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TupExt

open Formalism.IndefR.Lev Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T N : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def ModC (R : RealDat D A Ks) : Prop :=
  R.models_HX ∧ R.models_HV ∧ R.models_jX ∧ R.models_jV ∧ R.models_νY ∧ R.models_νY' ∧ R.models_νX ∧ R.models_νV

def KerC (R : RealDat D A Ks) : Prop :=
  R.chain_ωY ∧ R.chain_ωX ∧ R.chain_vY ∧ R.chain_vX ∧ R.thP_ωP ∧ R.thP_vP

variable {R : RealDat D A Ks} {V : NewLev D N} {X : NewFam A N}

def FamC (Y : NewReal R V X) : Prop :=
  (extR R Y).grp_red_R ∧ (extR R Y).grp_red_L ∧ TieExt R Y ∧ (extR R Y).fam_roots ∧ RealDat.fam_degR (A := extA A X) ∧
    RealDat.fam_degL (A := extA A X) ∧ (extR R Y).fam_muVal

set_option maxHeartbeats 2000000 in

def updM (Y : NewReal R V X) (HX : type_of% Y.HX) (HV : type_of% Y.HV)
    (jX : ∀ n, (extA A X).fam.amb.FR (.inr n) →ₛₗ[D.what₂.embLL] (HX n).H)
    (jV : ∀ i n, (extA A X).fam.amb.FL i (.inr n) →ₛₗ[D.what₂.embLL] (HV i n).H)
    (νY : type_of% Y.νY) (fdY : type_of% Y.fdY) (νX : type_of% Y.νX) (fdX : type_of% Y.fdX) (νV : type_of% Y.νV)
    (fdV : type_of% Y.fdV) : NewReal R V X :=
  { Y with
    HX := HX, HV := HV, jX := jX, jV := jV, νY := νY, fdY := fdY, νX := νX, fdX := fdX, νV := νV, fdV := fdV,
    ioX := fun _ => 0, Th := fun _ => 0, thF := fun _ _ => 0, thG := fun _ _ => 0 }

set_option maxHeartbeats 2000000 in

def updK (Y : NewReal R V X) (ωY : type_of% Y.ωY) (ωX : type_of% Y.ωX) (ωP : type_of% Y.ωP) (vY : type_of% Y.vY)
    (vX : type_of% Y.vX) (vP : type_of% Y.vP) : NewReal R V X :=
  { Y with ωY := ωY, ωX := ωX, ωP := ωP, vY := vY, vX := vX, vP := vP }

set_option maxHeartbeats 2000000 in

def updL (Y : NewReal R V X) (ioY : type_of% (extR R Y).ioY) (ioX : type_of% (extR R Y).ioX) (Th : type_of% (extR R Y).Th)
    (thF : type_of% (extR R Y).thF) (thG : type_of% (extR R Y).thG) : NewReal R V X :=
  { Y with
    ioY := fun n => ioY (.inr n), ioX := fun n => ioX (.inr n), Th := fun n => Th (.inr n),
    thF := fun i n => thF i (.inr n), thG := fun i n => thG i (.inr n) }

set_option maxHeartbeats 2000000 in
theorem isModels_ext (hM : R.IsModels) (Y : NewReal R V X) (h : ModC (extR R Y)) : (extR R Y).IsModels := by
  refine ⟨?_, hM.vpos, ?_, ?_, ?_, h.1, h.2.1, ?_, ?_, ?_, ?_, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, ?_, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (hM.inf :))
  · exact (by with_unfolding_all exact (hM.cX :))
  · exact (by with_unfolding_all exact (hM.cV :))
  · exact (by with_unfolding_all exact (hM.prX :))
  · exact (by with_unfolding_all exact (hM.HE :))
  · exact (by with_unfolding_all exact (hM.HW :))
  · exact (by with_unfolding_all exact (hM.gE :))
  · exact (by with_unfolding_all exact (hM.gW :))
  · exact (by with_unfolding_all exact (hM.ν0 :))
  · exact (by with_unfolding_all exact (hM.νW :))
  · exact (by with_unfolding_all exact (hM.BV :))
  · exact (by with_unfolding_all exact (hM.order :))

set_option maxHeartbeats 2000000 in
theorem isFam_ext (hF : R.IsFam) (Y : NewReal R V X) (h : FamC Y) : (extR R Y).IsFam := by
  refine ⟨?_, ?_, h.2.2.2.1, ?_, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2, ?_⟩
  · obt ⟨g, c, c', ht⟩ := hF.tie
    have h1 := h.2.2.1 g c c' ht
    refine ⟨g, ?_, ?_, ?_⟩
    · exact (by with_unfolding_all exact (c :))
    · exact (by with_unfolding_all exact (c' :))
    · exact (by with_unfolding_all exact (h1 :))
  · exact (by with_unfolding_all exact (hF.Sb :))
  · exact (by with_unfolding_all exact (hF.pl_onto :))
  · exact (by with_unfolding_all exact (hF.etaVal :))

set_option maxHeartbeats 2000000 in
theorem isGrp_ext {F : Face D A} (hG : R.IsGrp F) (Y : NewReal R V X) (h : FamC Y) : (extR R Y).IsGrp (extF F X) := by
  refine ⟨h.1, h.2.1, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (hG.levels :))
  · exact (by with_unfolding_all exact (hG.record :))
  · exact (by with_unfolding_all exact (hG.chiW :))

set_option maxHeartbeats 2000000 in

theorem models_stage (hM : R.IsModels) (Y : NewReal R V X) (h : FamC Y) : ∃ Y' : NewReal R V X, FamC Y' ∧ ModC (extR R Y') := by
  choose HX jX h1 h2 using fun n => exists_modX (extR R Y) (.inr n)
  choose HV jV h3 h4 using fun i n => exists_modV (extR R Y) i (.inr n)
  choose νY fdY h5 h6 using fun n j => exists_measY (extR R Y) (.inr n) j
  choose νX fdX h7 using fun n => exists_measX (extR R Y) (.inr n)
  choose νV fdV h8 using fun i n => exists_measV (extR R Y) hM.vpos i (.inr n)
  refine ⟨updM Y HX HV jX jV νY fdY νX fdX νV fdV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kexactB h
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.HX t :))
    · exact (by with_unfolding_all exact (h1 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.HV i t :))
    · exact (by with_unfolding_all exact (h3 i n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.jX t :))
    · exact (by with_unfolding_all exact (h2 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.jV i t :))
    · exact (by with_unfolding_all exact (h4 i n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νY t :))
    · exact (by with_unfolding_all exact (h5 n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νY' t :))
    · exact (by with_unfolding_all exact (h6 n _ rfl :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hM.νX t :))
    · exact (by with_unfolding_all exact (h7 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hM.νV i t :))
    · exact (by with_unfolding_all exact (h8 i n :))

set_option maxHeartbeats 2000000 in

theorem ker_stage (hc : R.IsChain) (hp : R.IsThP) (hL : (extL R.toLevCh V).Is (.inl A.μ0)) (Y : NewReal R V X) (h : FamC Y)
    (hm : ModC (extR R Y)) : ∃ Y' : NewReal R V X, FamC Y' ∧ ModC (extR R Y') ∧ KerC (extR R Y') := by
  have hψ : IsStdChar D (extR R Y).ψ (-1) := (hc.ωX A.μ0).std
  choose ωY vY h1 using fun n k => exists_kerY (R := extR R Y) hL hψ (.inr n) k ((by with_unfolding_all exact (fun hk => (hc.vY A.μ0 k hk).1 :)))
  choose ωX vX h2 h3 using fun n => exists_kerX (R := extR R Y) hL hψ (.inr n) ((by with_unfolding_all exact ((hc.vX A.μ0).1 :)))
  choose ωP vP h4 h5 using fun i n => exists_kerP (R := extR R Y) hL hψ i (.inr n) ((by with_unfolding_all exact ((hp.vP i A.μ0).1 :)))
  refine ⟨updK Y ωY ωX ωP vY vX vP, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h :))
  · exact (by with_unfolding_all exact (hm :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ωY t :))
    · exact (by with_unfolding_all exact (fun k hk => (h1 n k hk).1 :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ωX t :))
    · exact (by with_unfolding_all exact (h2 n :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.vY t :))
    · exact (by with_unfolding_all exact (fun k hk => (h1 n k hk).2 :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.vX t :))
    · exact (by with_unfolding_all exact (h3 n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.ωP i t :))
    · exact (by with_unfolding_all exact (h4 i n :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.vP i t :))
    · exact (by with_unfolding_all exact (h5 i n :))

set_option maxHeartbeats 2000000 in
theorem isChain_updL (hc : R.IsChain) (Y : NewReal R V X) (ioY ioX Th thF thG)
    (h : ({ extR R Y with ioY := ioY, ioX := ioX, Th := Th } : RealDat D (extA A X) Ks).IsChain) :
    (extR R (updL Y ioY ioX Th thF thG)).IsChain := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kexactB h.ωY
  · exact (by with_unfolding_all exact (h.ωX :))
  · exact (by with_unfolding_all exact (h.vY :))
  · exact (by with_unfolding_all exact (h.vX :))
  · exact (by with_unfolding_all exact (h.ptY :))
  · exact (by with_unfolding_all exact (h.ptX :))
  · exact (by with_unfolding_all exact (h.ItY :))
  · exact (by with_unfolding_all exact (h.ItX :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ioY t :))
    · exact (by with_unfolding_all exact (h.ioY (.inr n) :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.ioX t :))
    · exact (by with_unfolding_all exact (h.ioX (.inr n) :))
  · rintro (t | n)
    · exact (by with_unfolding_all exact (hc.Th t :))
    · exact (by with_unfolding_all exact (h.Th (.inr n) :))

set_option maxHeartbeats 2000000 in
theorem isThP_updL (hp : R.IsThP) (Y : NewReal R V X) (ioY ioX Th thF thG)
    (h : ({ extR R Y with thF := thF, thG := thG } : RealDat D (extA A X) Ks).IsThP) :
    (extR R (updL Y ioY ioX Th thF thG)).IsThP := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (by with_unfolding_all exact (h.ωP :))
  · exact (by with_unfolding_all exact (h.vP :))
  · exact (by with_unfolding_all exact (h.pt_theta :))
  · exact (by with_unfolding_all exact (h.ioP :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thF_mem i t :))
    · exact (by with_unfolding_all exact (h.thF_mem i (.inr n) :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thF i t :))
    · exact (by with_unfolding_all exact (h.thF i (.inr n) :))
  · rintro i (t | n)
    · exact (by with_unfolding_all exact (hp.thG i t :))
    · exact (by with_unfolding_all exact (h.thG i (.inr n) :))

set_option maxHeartbeats 2000000 in

theorem core_ext (h₁ : GlobalTheory.Published.DiscreteSeriesCover) (h₂ : GlobalTheory.Published.HarishChandraModules) (h₃ : GlobalTheory.Published.CuspRapidDecay)
    (h₄ : GlobalTheory.Published.CasselmanWallach) (hP : ∀ k, GlobalTheory.Chain.ChainPar D k) {F : Face D A} (hC : GlobalTheory.Hk3.Core R F)
    (hL : (extL R.toLevCh V).Is (.inl A.μ0)) (Y : NewReal R V X) (h : FamC Y) :
    ∃ Y' : NewReal R V X, GlobalTheory.Hk3.Core (extR R Y') (extF F X) ∧ TieExt R Y' := by
  obt ⟨Y1, f1, m1⟩ := models_stage hC.models Y h
  obt ⟨Y2, f2, m2, k2⟩ := ker_stage hC.chain hC.thP hL Y1 f1 m1
  have hF := isFam_ext hC.fam Y2 f2
  have hM := isModels_ext hC.models Y2 m2
  have e1 := GlobalTheory.ConjExt.exists_chain (R := extR R Y2) h₁ h₂ h₃ h₄ hP hL (isGrp_ext hC.grp Y2 f2).record hF hM k2.1 k2.2.1 k2.2.2.1
    k2.2.2.2.1 (.inl A.μ0) ((by with_unfolding_all exact (hC.chain.ItY A.μ0 :))) ((by with_unfolding_all exact (hC.chain.ItX A.μ0 :)))
  have e2 := GlobalTheory.ConjExt.exists_thP (R := extR R Y2) h₃ hL hF hM k2.2.2.2.2.1 k2.2.2.2.2.2 (.inl A.μ0)
    ((by with_unfolding_all exact (fun i => hC.thP.ioP i A.μ0 :)))
  obt ⟨ioY, ioX, Th, c3⟩ := e1
  obt ⟨thF, thG, p3⟩ := e2
  have f3 : FamC (updL Y2 ioY ioX Th thF thG) := (by with_unfolding_all exact (f2 :))
  have m3 : ModC (extR R (updL Y2 ioY ioX Th thF thG)) := (by with_unfolding_all exact (m2 :))
  exact ⟨updL Y2 ioY ioX Th thF thG, ⟨hL, isGrp_ext hC.grp _ f3, isFam_ext hC.fam _ f3, isModels_ext hC.models _ m3,
    isChain_updL hC.chain Y2 _ _ _ _ _ c3, isThP_updL hC.thP Y2 _ _ _ _ _ p3⟩, f3.2.2.1⟩

end GlobalTheory.TupExt

end
end

