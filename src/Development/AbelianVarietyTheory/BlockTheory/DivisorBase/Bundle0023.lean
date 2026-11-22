import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.LevelCuspCharacters
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GammaMembershipConditions
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open GlobalTheory.Ker
open scoped TensorProduct ComplexConjugate ENNReal

namespace GlobalTheory.IndefiniteRowSideFullHecke.RealPointEmbeddings

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev WRe (S T : HSp D) : Type := D.what₂.Tau → Matrix (Fin T.rank) (Fin S.rank) ℂ

abbrev Sq (T : HSp D) : Type := D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ

variable {S T : HSp D}

def ptR (θ : InfFam D) (z : WRe S T) : WO S T := ∑ τ, lineAt θ τ (z τ) 1

def embQ (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : WRe S T := fun τ => γ.map (tauE D τ)

def EFr (x x' : WRe S T) : ℝ :=
  -∑ τ, 2 * (tauE D τ D.host.xi0 * ((gramAt D S τ)⁻¹ * (x' τ)ᴴ * gramAt D T τ * x τ).trace).re

def Jc (s : Sq T) (x : WRe S T) : WRe S T := fun τ => cplxO 1 (s τ) (x τ)

def Hc (s : Sq T) (u v : WRe S T) : ℂ := (EFr (Jc s u) v : ℂ) + Complex.I * (EFr u v : ℂ)

def gInf (θ : InfFam D) (g : GA D T) : Sq T := fun τ => compAt θ τ (mt T g)

def mvS (θ : InfFam D) (g : GA D T) (s : Sq T) : Sq T := fun τ => gInf θ g τ * s τ * gInf θ g⁻¹ τ

def mvO (θ : InfFam D) (g : GA D T) (B : Sq T) : Sq T := fun τ => gInf θ g τ * B τ

def lie (s B : Sq T) (ζ : FVar D T.rank S.rank → ℂ) : WRe S T := fun τ =>
  ∑ i, ∑ j, ((2 / fockScale D τ : ℝ) : ℂ) •
    (((ζ (τ, i, j)).re : ℂ) • unitMap 1 (B τ) i j + ((ζ (τ, i, j)).im : ℂ) • cplxO 1 (s τ) (unitMap 1 (B τ) i j))

def InGam (L : Lt D.host.E T.rank) (g : GA D T) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : Prop :=
  ∃ u ∈ latO S T (stdL D.host.E S.rank) L (fun _ => True),
    (ratW T S γ).map (finPart D) = (actO S T 1 g u).map (finPart D)

def IsLatOf (L : Lt D.host.E T.rank) (g : GA D T) (H : Lt D.host.E T.rank) : Prop :=
  ∀ v, v ∈ H ↔ ∃ u ∈ latHat D.host.F D.host.E {x | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ L, x = a • t},
    toAf v = fmt T g *ᵥ u

def hQ (x x' : Matrix (Fin T.rank) (Fin S.rank) D.host.E) : D.host.E :=
  (S.gram⁻¹ * x'ᴴ * T.gram * x).trace

def HasQ (x : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (m : ℤ) : Prop :=
  Algebra.trace D.host.K D.host.E (hQ x x) = (Ideal.absNorm D.host.ccK : D.host.K) * (m : D.host.K)

def wZero (D : D7) : D.host.E := (1 + D.host.sqrtMinusD) / 2

def IsCanTheta (L : Lt D.host.E T.rank) (g : GA D T) (s B : Sq T) (G : WRe S T → ℂ) : Prop :=
  Differentiable ℂ (fun ζ : FVar D T.rank S.rank → ℂ => G (lie s B ζ)) ∧
    ∀ γ, InGam L g γ → ∃ m : ℤ, HasQ γ m ∧ ∀ z : WRe S T,
      G (z + embQ γ) = (-1 : ℂ) ^ m *
        Complex.exp (Real.pi * Hc s z (embQ γ) + Real.pi * Hc s (embQ γ) (embQ γ) / 2) * G z

def latC (S : HSp D) (L : Lt D.host.E T.rank) (g : GA D T) (s B : Sq T) :
    AddSubgroup (FVar D T.rank S.rank → ℂ) :=
  AddSubgroup.closure {ζ | ∃ γ, InGam (S := S) L g γ ∧ lie s B ζ = embQ γ}

def HasMeanSq (L : Lt D.host.E T.rank) (g : GA D T) (s B : Sq T) (G : WRe S T → ℂ) (m : ℝ≥0∞) : Prop :=
  AllSome (fun 𝓕 : Set (FVar D T.rank S.rank → ℂ) => IsAddFundamentalDomain (latC S L g s B) 𝓕 volume) fun 𝓕 =>
    0 < volume 𝓕 ∧ volume 𝓕 < ⊤ ∧
      ∫⁻ ζ in 𝓕, ‖G (lie s B ζ)‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-(Real.pi * (Hc s (lie (S := S) s B ζ) (lie s B ζ)).re))) = m * volume 𝓕

def IsInertIdem (D : D7) (ε : AF D.host.F) : Prop :=
  (∃ v, IsPlaceIdem D v ε) ∧ ¬ ∃ e, IsSplitIdem D e ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε

def UnramInert (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ ε, IsInertIdem D ε → ∀ x : (AE D)ˣ,
    algebraMap (AF D.host.F) (AE D) ε * ((x : AE D) - 1) = (x : AE D) - 1 →
    finPart D (x : AE D) ∈ intAE D → finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → χ x = 1

def IsSplitDet (k : GA D T) (x : (AE D)ˣ) : Prop :=
  infPart D (x : AE D) = 1 ∧
    (∀ e, IsSplitIdem D e →
      (e * (x : AE D) = e * (mt T k).det ∧ cA D e * (x : AE D) = cA D e) ∨
      (cA D e * (x : AE D) = cA D e * (mt T k).det ∧ e * (x : AE D) = e)) ∧
    ∀ ε, IsInertIdem D ε →
      algebraMap (AF D.host.F) (AE D) ε * (x : AE D) = algebraMap (AF D.host.F) (AE D) ε

def detOn {m : ℕ} (s k : Matrix (Fin m) (Fin m) ℂ) : ℂ :=
  ((1 / 2 : ℂ) • (1 + s) * k + (1 / 2 : ℂ) • (1 - s)).det

def jChar (n : ℕ) (a : D.what₂.Tau → ℤ) (s k : Sq T) : ℂ :=
  ∏ τ, detOn (s τ) (k τ) ^ (a τ + ((n / 2 : ℕ) : ℤ)) * detOn (-s τ) (k τ) ^ (a τ - ((n / 2 : ℕ) : ℤ))

def eFr (θ : InfFam D) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (s : Sq T) (f : WO S T → ℂ)
    (g : GA D T) (z : WRe S T) : ℂ :=
  Complex.exp (Real.pi * Hc (mvS θ g s) z z / 2) * om (1, g) f (ptR θ z)

open Classical in

structure FrameLaws (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (χS : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (L : Lt D.host.E T.rank) (s B : Sq T)
    (f : WO S T → ℂ) : Prop where

  can : ∀ g, IsCanTheta L g (mvS θ g s) (mvO θ g B) (eFr θ om s f g)

  line : ∀ g (G : WRe S T → ℂ), IsCanTheta L g (mvS θ g s) (mvO θ g B) G → ∃ c : ℂ, G = c • eFr θ om s f g

  norm : ∀ g, HasMeanSq L g (mvS θ g s) (mvO θ g B) (eFr θ om s f g) 1

  jet : ∀ g (P : MvPolynomial (FVar D T.rank S.rank) ℂ),
    I2.polyDeriv P (fun k => (Pi.single k 1 : FVar D T.rank S.rank → ℂ))
        (fun ζ => eFr θ om s f g (lie (mvS θ g s) (mvO θ g B) ζ)) 0 =
      om (1, g) (pureTensorO ψ θ S T (fun _ => 1) s (fun _ => 1) B f P) 0

  rat : ∀ γ ∈ GQ T, ∀ g (z : WRe S T),
    eFr θ om s f (γ * g) (fun τ => gInf θ γ τ * z τ) = eFr θ om s f g z

  fin : UnramInert χS → ∀ k ∈ GfC T, IsMov (fmt T k) L L → AllSome (IsSplitDet k) fun x =>
    ∀ g, eFr θ om s f (g * k) = ((χS x : Circle) : ℂ) • eFr θ om s f g

  inf : ∀ a : D.what₂.Tau → ℤ, (∀ τ, HasInfExp D χS τ (a τ)) →
    ∀ k ∈ GinfC T, (∀ τ, gInf θ k τ * s τ = s τ * gInf θ k τ) →
      ∀ g, eFr θ om s f (g * k) = jChar S.rank a s (gInf θ k) • eFr θ om s f g

  classical : ∀ C : Ctx S T, C.θ = θ → C.IsB B → ∀ g, AllSome (IsLatOf L g) fun H =>
    (∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, InGam L g γ ↔ γᵀ ∈ tens (stdL D.host.E S.rank) H) ∧
    AllSome (IsVac C.X C.bas (wZero D) (tens (stdL D.host.E S.rank) H)) fun φ =>
      ∃ c : ℂ,
        (∀ z : WRe S T, eFr θ om s f g z =
          c * thA C.X C.bas C.idx φ (C.xB (C.mvB g B)) (C.zOf (C.xB (C.mvB g B)) (ptR θ z))) ∧
        (∃ m : ℝ≥0∞, HasMeanSq L g (mvS θ g s) (mvO θ g B)
          (fun z : WRe S T => thA C.X C.bas C.idx φ (C.xB (C.mvB g B)) (C.zOf (C.xB (C.mvB g B)) (ptR θ z))) m ∧
          ‖c‖ₑ ^ 2 * m = 1) ∧
        ∀ P : MvPolynomial (FVar D T.rank S.rank) ℂ,
          om (1, g) (pureTensorO ψ θ S T (fun _ => 1) s (fun _ => 1) B f P) 0 =
            c * thP C.X C.hr C.bas C.idx φ (C.toH P) (C.xB (C.mvB g B))

def VacuumFrame : Prop :=
  ∀ (D : D7) (S T : HSp D), S.gram = 1 → Even S.rank →
    ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle)
      (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ (L : Lt D.host.E T.rank), IsSelfDualC T L →
    ∀ (p : ℕ) (s B : Sq T), (∀ τ, IsCartanInv (gramAt D T τ) (s τ)) →
      (∀ τ, IsONBasis (gramAt D T τ) (s τ) (B τ) p) →
    ∀ (θ : InfFam D) (f : WO S T → ℂ),
      IsVacO ψ θ S T (fun _ => 1) s (stdL D.host.E S.rank) L f → FrameLaws ψ θ χS om L s B f

example (u v : ℂ) : detOn !![1, 0; 0, -1] !![u, 0; 0, v] = u := by
  simp [detOn, Matrix.det_fin_two, Matrix.one_fin_two]; ring

example (u v : ℂ) : detOn (-!![1, 0; 0, -1]) !![u, 0; 0, v] = v := by
  simp [detOn, Matrix.det_fin_two, Matrix.one_fin_two]; ring

end GlobalTheory.IndefiniteRowSideFullHecke.RealPointEmbeddings

end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GoodReductionModelReading
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IsOrthSum {X ι : Type} [AddCommGroup X] [Module ℂ X] (Orth : X → X → Prop) (Y : Submodule ℂ X)
    (part : ι → Submodule ℂ X) (Pi : Set ι) : Prop :=
  Pi.Finite ∧ Y = ⨆ c : Pi, part c ∧ iSupIndep (fun c : Pi => part c) ∧
    ∀ c ∈ Pi, ∀ c' ∈ Pi, c ≠ c' → ∀ x ∈ part c, ∀ y ∈ part c', Orth x y

example {X : Type} [AddCommGroup X] [Module ℂ X] (Orth : X → X → Prop) (Y : Submodule ℂ X) :
    IsOrthSum Orth Y (fun _ : Unit => Y) Set.univ := by
  refine ⟨Set.toFinite _, by simp, ?_, fun c _ c' _ h => absurd (Subsingleton.elim c c') h⟩
  exact iSupIndep_subsingleton _

example {X ι : Type} [AddCommGroup X] [Module ℂ X] (Orth : X → X → Prop) (Y : Submodule ℂ X) (part : ι → Submodule ℂ X)
    (h : IsOrthSum Orth Y part ∅) : Y = ⊥ := by
  rw [h.2.1]; exact iSup_of_empty _

variable {D : D7}

def IsBadSet (D : D7) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))) : Prop :=
  ∀ v, v ∈ Sb ↔ ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal

def IsPlaceMatch {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg) : Prop :=
  ∀ (v : LevelCuspCharacters.Sq D.host) (x : 𝓞 D.host.F) (y : 𝓞 D.host.E),
    (y : D.host.E) = algebraMap D.host.F D.host.E (x : D.host.F) → (x ∈ v.2.1.asIdeal ↔ y ∈ (pl v).1.asIdeal)

def readG0 {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg)
    (red : ∀ v : LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1)) {n : ℕ} (hn : n = D.R.r)
    (x : Formalism.L2.DIV.G0 Pg n) : LevelCuspCharacters.LevelGroup D.host := fun v =>
  Units.map (Matrix.reindexAlgEquiv (ZMod (D.host.g v.1)) (ZMod (D.host.g v.1)) (finCongr hn)).toAlgHom.toMonoidHom
    (Matrix.GeneralLinearGroup.map (red v).toRingHom (x (pl v)))

def levelDatumAtBasePrime (V : HSp D) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)) (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ) :
    Formalism.L2.DIV.LevDat D.host.E ℂ V.rank :=
  Lev.datW V.rank Pg (Formalism.L2.DIV.P0 Pg V.rank ψ) Lev.Frm.A

def actLin (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank)
    (g0 : Formalism.L2.DIV.G0 L.Pg L.r) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := Lev.actG0 V β L g0
  map_add' F G := by
    unfold Lev.actG0
    split_ifs
    · funext h; exact mul_add _ _ _
    · exact (add_zero _).symm
  map_smul' a F := by
    unfold Lev.actG0
    split_ifs
    · funext h; exact mul_left_comm _ a _
    · exact (smul_zero _).symm

def eGoodOp (V : HSp D) (hV : V.rank = D.R.r) (β : GL (Fin V.rank) (Lev.EAf D)) {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ) (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg)
    (red : ∀ v : LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1))
    (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) :=
  haveI : Finite (Formalism.L2.DIV.G0 Pg V.rank) := by
    haveI : ∀ PP : ↥Pg, Finite (Formalism.L2.DIV.kP PP.1) := fun PP => Ideal.finiteQuotientOfFreeOfNeBot _ PP.1.ne_bot
    infer_instance
  haveI := Fintype.ofFinite (Formalism.L2.DIV.G0 Pg V.rank)
  ∑ x : Formalism.L2.DIV.G0 Pg V.rank,
    (LevelCuspCharacters.goodIdem (H := D.host) om).coeff (readG0 pl red hV x) • actLin V β (levelDatumAtBasePrime V Pg ψ) x

def IsFrameAtG (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) : Prop :=
  ∃ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (a : ℕ), Lev.IsBaseFrame V β Λ ((D.host.g 0 * D.host.g 1) ^ a)

abbrev EigSys (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

abbrev ModelW (D : D7) (j : ℕ) : Type 1 := DSModel (D.sp.W j) (parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))

section Spaces

variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))
  (j : ℕ) (hj : (D.sp.W j).rank = D.R.r) (M : ModelW D j) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D))
  {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ)
  (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg) (red : ∀ v : LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1))
  (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))

def goodW : Submodule ℂ (MMap M) :=
  WgoodRec θ j M (Lev.levG (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ) : Set (GA D (D.sp.W j)))
    (Lev.levChi (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ)) (eGoodOp (D.sp.W j) hj β ψ pl red om)

def partW (c : EigSys D) : Submodule ℂ (MMap M) :=
  Wpart θ j M (Lev.levG (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ) : Set (GA D (D.sp.W j)))
    (Lev.levChi (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ)) (eGoodOp (D.sp.W j) hj β ψ pl red om) Sb c

def occursW : Set (EigSys D) :=
  IxFull θ M (Lev.levG (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ) : Set (GA D (D.sp.W j)))
    (Lev.levChi (D.sp.W j) β (levelDatumAtBasePrime (D.sp.W j) Pg ψ)) Sb (eGoodOp (D.sp.W j) hj β ψ pl red om)

end Spaces

def PetOrth {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (T T' : MMap M) : Prop :=
  AllSome (fun μ : Measure (GA D V) => μ.IsHaarMeasure) fun μ =>
    AllSome (fun 𝓕 : Set (GA D V) => IsFundamentalDomain (GQ V) 𝓕 μ) fun 𝓕 => IsMultIP M μ 𝓕 T T' 0

def SumW (D : D7) : Prop :=
  ∀ (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ →
  ∀ (pb : Fin 2 → 𝓞 D.host.E) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), Lev.IsTypePlaces D.host.g pb Pg →
  ∀ (pl : LevelCuspCharacters.Sq D.host ≃ ↥Pg), IsPlaceMatch pl →
  ∀ (red : ∀ v : LevelCuspCharacters.Sq D.host, Formalism.L2.DIV.kP (pl v).1 ≃+* ZMod (D.host.g v.1))
    (ψ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, AddChar (Formalism.L2.DIV.kP PP) ℂ), Formalism.L2.DIV.IsGenericPsi Pg ψ →
  ∀ (om : ∀ i : Fin 2, (ZMod (D.host.g i))ˣ →* ℂˣ), LevelCuspCharacters.IsGeneratorFamily (H := D.host) om →
  ∀ (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), IsBadSet D Sb →
  ∀ (hm : (D.sp.W D.R.m).rank = D.R.r) (Mm : ModelW D D.R.m) (βm : GL (Fin (D.sp.W D.R.m).rank) (Lev.EAf D)),
    IsFrameAtG (D.sp.W D.R.m) βm →
  ∀ (j : ℕ), 1 ≤ j → j ≤ D.R.m →
  ∀ (hj : (D.sp.W j).rank = D.R.r) (M : ModelW D j) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    IsFrameAtG (D.sp.W j) β →
    IsOrthSum (PetOrth M) (goodW θ j hj M β ψ pl red om) (partW θ j hj M β ψ pl red om Sb)
      (occursW θ D.R.m hm Mm βm ψ pl red om Sb)

example (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : (D.sp.W j).rank = D.R.r := D.sp.W_rank j h1 h2

end GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading
end
end

-- bundled from Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LinearCoefficientData
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.L2.DIV
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsRecPlaces (D : D7) (Pg : Finset (Pl D.host.E)) : Prop :=
  ∀ PP, PP ∈ Pg ↔ ∃ kv : (Σ k : Fin 2, D.nd.PlG k), D.naut.plGw kv.1 kv.2 = PP

def resMap {E : Type} [Field E] [NumberField E] (p : ℕ) (PP : Pl E) (h : (p : 𝓞 E) ∈ PP.asIdeal) :
    ZMod p →+* kP PP :=
  ZMod.castHom (m := ringChar (kP PP))
    ((ringChar.spec (kP PP) p).1 (by
      rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 h)) (kP PP)

def idx {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) : (Σ k : Fin 2, D.nd.PlG k) :=
  ((h PP.1).1 PP.2).choose

theorem idx_spec {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) :
    D.naut.plGw (idx h PP).1 (idx h PP).2 = PP.1 :=
  ((h PP.1).1 PP.2).choose_spec

theorem idx_mem {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) :
    ((D.host.g (idx h PP).1 : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
  have h1 := D.naut.plGw_over (idx h PP).1 (idx h PP).2
  rw [idx_spec h PP] at h1
  exact h1

theorem idx_eq {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (PP : ↥Pg) (kv : Σ k : Fin 2, D.nd.PlG k)
    (e : D.naut.plGw kv.1 kv.2 = PP.1) : idx h PP = kv := by
  have h1 := idx_mem h PP
  have h2 : ((D.host.g kv.1 : ℕ) : 𝓞 D.host.E) ∈ PP.1.asIdeal := by
    have := D.naut.plGw_over kv.1 kv.2
    rw [e] at this
    exact this
  have h3 := idx_spec h PP
  generalize idx h PP = a at h1 h3
  obtain ⟨k, v⟩ := a
  obtain ⟨k', v'⟩ := kv
  have hk : k = k' := by
    by_contra hne
    have hg : D.host.g k ≠ D.host.g k' := by
      have := D.host.g_ne
      fin_cases k <;> fin_cases k' <;> first | exact absurd rfl hne | exact this | exact this.symm
    have hc : IsCoprime ((D.host.g k : ℕ) : 𝓞 D.host.E) ((D.host.g k' : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes (D.host.g_prime k) (D.host.g_prime k')).2 hg)
    obtain ⟨a, b, hab⟩ := hc
    refine PP.1.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    rw [← hab]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  subst hk
  have hv : v = v' := D.naut.plGw_inj k (h3.trans e.symm)
  rw [hv]

def toG0 {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (γ : G0g D.nd) : G0 Pg D.R.r := fun PP =>
  Matrix.GeneralLinearGroup.map (resMap (D.host.g (idx h PP).1) PP.1 (idx_mem h PP)) (γ (idx h PP))

def eCoef {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) : G0 Pg D.R.r →₀ ℂ :=
  Finsupp.mapDomain (toG0 h) D.ntypes.e0.coeff

def datR (V : HSp D) (hr : V.rank = D.R.r) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) (fr : Lev.Frm) :
    LevDat D.host.E ℂ V.rank :=
  Lev.datY V.rank D.R.r D.R.t 0 hr.ge Pg ∅ P (fun _ _ => 1) (fun _ => 1) fr

def eLin (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ V.rank) (e : G0 L.Pg L.r →₀ ℂ) :
    (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun F := Lev.eAct V β L e F
  map_add' F G := by
    funext x
    simp only [Lev.eAct, Finsupp.sum, Pi.add_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold Lev.actG0
    split_ifs
    · simp only [Pi.add_apply]; ring
    · simp
  map_smul' c F := by
    funext x
    simp only [Lev.eAct, Finsupp.sum, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    unfold Lev.actG0
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul]; ring
    · simp

theorem rank_zeroth_component_eq (D : D7) : (D.sp.Y 0).rank = D.R.r := by
  rw [D.sp.Y_rank 0 (Nat.zero_le _)]; simp [Ranks.rankY]

abbrev InfFam (D : D7) : Type := D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)

abbrev Eig (D : D7) : Type := HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ

abbrev datE (D : D7) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) : LevDat D.host.E ℂ (D.sp.Y 0).rank :=
  datR (D.sp.Y 0) (rank_zeroth_component_eq D) Pg P Lev.Frm.B

abbrev datWj (D : D7) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) :
    LevDat D.host.E ℂ (D.sp.W j).rank :=
  datR (D.sp.W j) (D.sp.W_rank j h1 h2) Pg P Lev.Frm.A

def EEc (θ : InfFam D) (M : Mult.DSModel (D.sp.Y 0) (Mult.parB (Mult.tparRec D) 0)) {Pg : Finset (Pl D.host.E)}
    (h : IsRecPlaces D Pg) (β : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (P : LevelP Pg D.R.r ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Eig D) : Submodule ℂ (Mult.MMap M) :=
  Mult.EEpart θ M (Lev.levG (D.sp.Y 0) β (datE D Pg P)) (Lev.levChi (D.sp.Y 0) β (datE D Pg P))
    (eLin (D.sp.Y 0) β (datE D Pg P) (eCoef h)) S c

def Wc (θ : InfFam D) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M : Mult.DSModel (D.sp.W j) (Mult.parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j)))) {Pg : Finset (Pl D.host.E)}
    (h : IsRecPlaces D Pg) (β : GL (Fin (D.sp.W j).rank) (Lev.EAf D)) (P : LevelP Pg D.R.r ℂ)
    (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (c : Eig D) : Submodule ℂ (Mult.MMap M) :=
  Mult.Wpart θ j M (Lev.levG (D.sp.W j) β (datWj D j h1 h2 Pg P)) (Lev.levChi (D.sp.W j) β (datWj D j h1 h2 Pg P))
    (eLin (D.sp.W j) β (datWj D j h1 h2 Pg P) (eCoef h)) S c

def ParamGap (D : D7) : Prop :=
  ∀ τ (n : ℕ), n + 1 < D.R.r → Formalism.L2.NTheta.lamAt (D.hc τ) (n + 1) + (D.R.r : ℚ) ≤ Formalism.L2.NTheta.lamAt (D.hc τ) n

def IsFrameOf (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) : Prop :=
  ∃ (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), Lev.IsBaseFrame V β Λ N

def DimPartsAt {Pg : Finset (Pl D.host.E)} (h : IsRecPlaces D Pg) (P : LevelP Pg D.R.r ℂ) : Prop :=
  ∀ (θ : InfFam D), IsInfFam θ →
  ∀ (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (M₀ : Mult.DSModel (D.sp.Y 0) (Mult.parB (Mult.tparRec D) 0))
    (M₁ : Mult.DSModel (D.sp.W j) (Mult.parW (D.sp.W j) (Formalism.L2.NTheta.wtOf D (D.sp.W j))))
    (β₀ : GL (Fin (D.sp.Y 0).rank) (Lev.EAf D)) (β₁ : GL (Fin (D.sp.W j).rank) (Lev.EAf D)),
    IsFrameOf (D.sp.Y 0) β₀ → IsFrameOf (D.sp.W j) β₁ →
  ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)),
    Mult.SphOff (Lev.levG (D.sp.Y 0) β₀ (datE D Pg P) : Set (GA D (D.sp.Y 0)))
      (Lev.levChi (D.sp.Y 0) β₀ (datE D Pg P)) S →
    Mult.SphOff (Lev.levG (D.sp.W j) β₁ (datWj D j h1 h2 Pg P) : Set (GA D (D.sp.W j)))
      (Lev.levChi (D.sp.W j) β₁ (datWj D j h1 h2 Pg P)) S →
  ∀ c : Eig D,
    FiniteDimensional ℂ (EEc θ M₀ h β₀ P S c) ∧ FiniteDimensional ℂ (Wc θ j h1 h2 M₁ h β₁ P S c) ∧
      Module.finrank ℂ (Wc θ j h1 h2 M₁ h β₁ P S c) = Module.finrank ℂ (EEc θ M₀ h β₀ P S c)

def DimensionDecompositionAtBasePrime (D : D7) : Prop :=
  ∀ (Pg : Finset (Pl D.host.E)) (h : IsRecPlaces D Pg) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ),
    IsGenericPsi Pg ψ → DimPartsAt h (P0 Pg D.R.r ψ)

def DimParts : Prop :=
  ∀ D : D7, ParamGap D → GlobalTheory.GLq.ESerTie D → DimensionDecompositionAtBasePrime D

def DimPartsThree : Prop :=
  ∀ D : D7, ParamGap D → GlobalTheory.GLq.ESerTie D →
    ∀ (Pg : Finset (Pl D.host.E)) (h : IsRecPlaces D Pg) (ψ : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ),
      IsGenericPsi Pg ψ → DimPartsAt h (LevelP.triv Pg D.R.r ℂ) ∧ DimPartsAt h (P0 Pg D.R.r ψ) ∧
        DimPartsAt h (PsharpSym Pg D.R.r D.R.rS D.R.k ψ)

theorem DimPartsThree.dimParts (h : DimPartsThree) : DimParts :=
  fun D h1 h2 Pg hP ψ hψ => (h D h1 h2 Pg hP ψ hψ).2.1

theorem exists_isRecPlaces (D : D7) : ∃ Pg, IsRecPlaces D Pg := by
  classical
  letI := D.nd.finPlG
  exact ⟨Finset.univ.image fun kv : (Σ k : Fin 2, D.nd.PlG k) => D.naut.plGw kv.1 kv.2, fun PP => by simp⟩

example (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (Pg : Finset (Pl D.host.E)) (P : LevelP Pg D.R.r ℂ) :
    (datE D Pg P).P = P ∧ (datWj D j h1 h2 Pg P).P = P.conj := ⟨rfl, rfl⟩

end GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData

end
end

