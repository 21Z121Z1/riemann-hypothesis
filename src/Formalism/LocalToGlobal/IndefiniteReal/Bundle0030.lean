import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0004
import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.AutomorphicEvaluation
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory Matrix IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR.Mult
open scoped TensorProduct ContDiff InnerProductSpace

namespace Formalism.IndefR.AutomorphicEvaluation

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar}

def ev (M : DSModel V S) (v₀ : M.Vec) : MMap M →ₗ[ℂ] (GA D V → ℂ) where
  toFun T := T v₀
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ev_apply (M : DSModel V S) (v₀ : M.Vec) (T : MMap M) : ev M v₀ T = T v₀ := rfl

def IsLowVec (M : DSModel V S) (v₀ : M.Vec) : Prop :=
  ∀ τ, IsLowUnit (M.ε τ) (M.lam τ) (M.σ τ) (v₀ τ : M.H τ)

theorem ev_pair (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T T' : MMap M) {c : ℂ}
    (h : IsMultIP M μ 𝓕 T T' c) (v₀ v₀' : M.Vec) :
    ∫ g in 𝓕, star (ev M v₀ T g) * ev M v₀' T' g ∂μ = c * ∏ τ, ⟪(v₀ τ : M.H τ), (v₀' τ : M.H τ)⟫_ℂ :=
  (h v₀ v₀').2

theorem ev_norm (M : DSModel V S) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) (T : MMap M) {c : ℂ}
    (h : IsMultIP M μ 𝓕 T T c) (v₀ : M.Vec) (hv : ∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) :
    ∫ g in 𝓕, ((‖ev M v₀ T g‖ ^ 2 : ℝ) : ℂ) ∂μ = c := by
  have h1 := ev_pair M μ 𝓕 T T h v₀ v₀
  have h2 : ∏ τ, ⟪(v₀ τ : M.H τ), (v₀ τ : M.H τ)⟫_ℂ = 1 := by
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [inner_self_eq_norm_sq_to_K, hv τ]
    norm_num
  rw [h2, mul_one] at h1
  rw [← h1]
  congr 1
  funext g
  rw [Complex.star_def, Complex.conj_mul']
  norm_cast

def ResInj (M : DSModel V S) (C : Submodule ℂ (MMap M)) {TK : Type} [AddCommGroup TK] [Module ℂ TK]
    (emb : TK →ₗ[ℂ] ⨂[ℂ] τ, M.sm τ) : Prop :=
  ∀ T ∈ C, (PiTensorProduct.lift T) ∘ₗ emb = 0 → T = 0

def ResInjVec (M : DSModel V S) (C : Submodule ℂ (MMap M)) : Prop :=
  ∀ T ∈ C, ∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ≠ 0) → T v = 0 → T = 0

theorem resInj_of_vec (M : DSModel V S) (C : Submodule ℂ (MMap M)) {TK : Type} [AddCommGroup TK] [Module ℂ TK]
    (emb : TK →ₗ[ℂ] ⨂[ℂ] τ, M.sm τ) (h : ResInjVec M C)
    (hv : ∃ v : M.Vec, (∀ τ, (v τ : M.H τ) ≠ 0) ∧ ∃ x, emb x = PiTensorProduct.tprod ℂ v) : ResInj M C emb := by
  intro T hT h0
  obtain ⟨v, hv0, x, hx⟩ := hv
  refine h T hT v hv0 ?_
  have h1 := LinearMap.congr_fun h0 x
  rw [LinearMap.comp_apply, hx, PiTensorProduct.lift.tprod, LinearMap.zero_apply] at h1
  exact h1

open Formalism.L2.SG.RowDict in

def EvalTie (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0))) (𝓕 : Set (GA D (D.sp.Y 0)))
    (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (c : ℝ) : Prop :=
  ∃ v₀ : M.Vec, (∀ τ, ‖(v₀ τ : M.H τ)‖ = 1) ∧ ∃ j : E ≃ₗ[ℂ] EEC X G, ∀ T : E,
    ((j T : EEC X G) : L2X X) =ᵐ[muX X] (fun x => ev M v₀ (T : MMap M) (ι.symm x)) ∧
      ‖((j T : EEC X G) : L2X X)‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re

end Formalism.IndefR.AutomorphicEvaluation

end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.BridgeSeed
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField

namespace Formalism.IndefR.Seed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

abbrev RowSideT (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T) (cX : CoefA D.sp.X') (pl : Pl0 → Pl D.host.E) (t : T) : Type :=
  Bridge.SideReal D D.sp.X' (Bridge.envOf cX.coef (levEnvOf D.sp.X' L.βX (L.datXt t) pl (A3.A.ok t)))
    (A3.A.MtildeCSD t) (A3.A.leftGroupActionRight t) (A3.A.heckeR t) (fun i => i.2)

abbrev LiftSideT (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T) (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (i : Fin D.R.m) (t : T) : Type :=
  Bridge.SideReal D (Vc D i) (Bridge.envOf (cV i).coef (levEnvOf (Vc D i) (L.βV i) (L.datVt i t) pl (A3.A.ok t)))
    (A3.A.MtCSD i t) (A3.A.leftGroupActionLift i t) (A3.A.heckeL i t) (fun i => i.2)

open Classical in

def PrIso {D : D7} (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (cX : CoefA D.sp.X') (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ) : Prop :=
  ∀ (ι : D.what₂.Tau → Type) [∀ τ, Fintype (ι τ)] (b : ∀ τ, OrthonormalBasis (ι τ) ℂ (MX.sm τ)) (w w' : cX.W),
    inner ℂ w w' = ∑ f : (∀ τ, ι τ),
      starRingEnd ℂ (prX w (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))) * prX w' (PiTensorProduct.tprod ℂ fun τ => b τ (f τ))

theorem brgAt_of_sides (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T)
    (h : ∀ eG : G ≃* Formalism.L2.DIV.G0 L.Pg D.R.r, RecL A3 L eG → ∀ θ : InfFam D, IsInfFam θ →
      ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m),
      ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (plI : I0 → Pl D.host.E)
        (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ)
        (RS : ∀ t, Set (RowSideT A3 L cX pl t)) (LS : ∀ i t, Set (LiftSideT A3 L cV pl i t)),
        cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ (∀ t, (RS t).Nonempty) ∧ (∀ i t, (LS i t).Nonempty) ∧
        (D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t ∧ ∀ i : Fin D.R.m, (Vc D i).rank = A3.A.r + A3.A.t) ∧
        ∀ B : BType A3 L cX cV pl, (∀ t, B.R t ∈ RS t) → (∀ i t, B.L i t ∈ LS i t) → BrgL A3 L eG cX cV pl Sb B plI SF) :
    BrgAt A3 L := by
  unfold BrgAt
  intro eG hrec θ hθ MX
  obtain ⟨cX, cV, pl, Sb, plI, SF, prX, RS, LS, hcX, hcV, hdual, hRS, hLS, hrk, hB⟩ := h eG hrec θ hθ MX
  refine ⟨cX, cV, pl, Sb, ⟨fun t => (hRS t).some, fun i t => (hLS i t).some, hrk.1, hrk.2⟩, plI, SF, prX, hcX, hcV, hdual, ?_⟩
  exact hB _ (fun t => (hRS t).some_mem) (fun i t => (hLS i t).some_mem)

theorem brgAtP_of_sides (A3 : Formalism.L2.DIV.FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (L : LevCh D T)
    (Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (_cv : ∀ i, CoefA (Vc D i)), (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop)
    (h : ∀ eG : G ≃* Formalism.L2.DIV.G0 L.Pg D.R.r, RecL A3 L eG → ∀ θ : InfFam D, IsInfFam θ →
      ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m),
      ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (plI : I0 → Pl D.host.E)
        (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ)
        (RS : ∀ t, Set (RowSideT A3 L cX pl t)) (LS : ∀ i t, Set (LiftSideT A3 L cV pl i t)),
        cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Pr MX cX cV prX ∧ (∀ t, (RS t).Nonempty) ∧ (∀ i t, (LS i t).Nonempty) ∧
        (D.sp.X'.rank = A3.A.r + D.R.m * A3.A.t ∧ ∀ i : Fin D.R.m, (Vc D i).rank = A3.A.r + A3.A.t) ∧
        ∀ B : BType A3 L cX cV pl, (∀ t, B.R t ∈ RS t) → (∀ i t, B.L i t ∈ LS i t) → BrgL A3 L eG cX cV pl Sb B plI SF) :
    BrgAtP A3 L Pr := by
  unfold BrgAtP
  intro eG hrec θ hθ MX
  obtain ⟨cX, cV, pl, Sb, plI, SF, prX, RS, LS, hcX, hcV, hdual, hPr, hRS, hLS, hrk, hB⟩ := h eG hrec θ hθ MX
  refine ⟨cX, cV, pl, Sb, ⟨fun t => (hRS t).some, fun i t => (hLS i t).some, hrk.1, hrk.2⟩, plI, SF, prX, hcX, hcV, hdual, hPr, ?_⟩
  exact hB _ (fun t => (hRS t).some_mem) (fun i t => (hLS i t).some_mem)

end Formalism.IndefR.Seed
end
end

-- bundled from Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
section
open Module NumberField IsDedekindDomain
open scoped Matrix InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.BasicNotions Formalism.L2.Col Formalism.IndefR.Links

section Face

variable {Fl : Fields} {Pr : Primes Fl} {Rk : Ranks} (W : Wts Fl Pr.Word Rk) (Ch : Chars Fl Pr Rk.m)
  (sel : HeightOneSpectrum (𝓞 Fl.F) → HeightOneSpectrum (𝓞 Fl.E)) {Sg : Set ℕ}
  {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def faceCol (hX : Fl.Ok) (A : FamIn Fl.K G Pl0 T m) (P1 : Subgroup G) (ψ1 : P1 →* Fl.Kˣ)
    {P : LevFam Fl.E Fl.K Rk.r Pr.vGs} (Xg : Finset (G0 Fl.E Pr.vGs Rk.r → Fl.K)) {m2 : ℕ} {Gc : ChGlob Fl Rk.m}
    (mu : A.fam.base.Tup → Tup Fl.F Fl.E Fl.K Sg) (cst : ∀ t, LocCst Fl (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx Fl Pr Rk (QE sel (mu t : Chr Fl.F Fl.E Fl.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x)) (Am : Formalism.L2.Ker.Amb Fl)
    (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok)
    (ev : ∀ (Zs : DefSub A.fam.amb) t, (Fin ((A.side P1 ψ1 Zs).nV t) → Fl.K) →ₗ[Fl.K] V0X W Ch sel (mu t) Xg P) :
    ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs) := fun Zs =>
  colFace hX (A.side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY
    (fun t x => Formalism.L2.Ker.chKerC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P (hK t x)) hF (ev Zs)

def faceColT (hX : Fl.Ok) (A : FamIn Fl.K G Pl0 T m) (P1 : Subgroup G) (ψ1 : P1 →* Fl.Kˣ)
    {P : LevFam Fl.E Fl.K Rk.r Pr.vGs} (Xg : Finset (G0 Fl.E Pr.vGs Rk.r → Fl.K)) {m2 : ℕ} {Gc : ChGlob Fl Rk.m}
    (mu : A.fam.base.Tup → Tup Fl.F Fl.E Fl.K Sg) (cst : ∀ t, LocCst Fl (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx Fl Pr Rk (QE sel (mu t : Chr Fl.F Fl.E Fl.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    {D : D7} (sm : Formalism.L2.Ker.Seam D Fl) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ)
    (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) (Formalism.L2.Ker.ambOf sm B χ cD) (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok)
    (ev : ∀ (Zs : DefSub A.fam.amb) t, (Fin ((A.side P1 ψ1 Zs).nV t) → Fl.K) →ₗ[Fl.K] V0X W Ch sel (mu t) Xg P) :
    ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs) :=
  faceCol W Ch sel hX A P1 ψ1 Xg mu cst L hL hP Mem wd b hY (Formalism.L2.Ker.ambOf sm B χ cD) hK hF ev

theorem faceCol_Pt (hX : Fl.Ok) (A : FamIn Fl.K G Pl0 T m) (P1 : Subgroup G) (ψ1 : P1 →* Fl.Kˣ)
    {P : LevFam Fl.E Fl.K Rk.r Pr.vGs} (Xg : Finset (G0 Fl.E Pr.vGs Rk.r → Fl.K)) {m2 : ℕ} {Gc : ChGlob Fl Rk.m}
    (mu : A.fam.base.Tup → Tup Fl.F Fl.E Fl.K Sg) (cst : ∀ t, LocCst Fl (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx Fl Pr Rk (QE sel (mu t : Chr Fl.F Fl.E Fl.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x)) (Am : Formalism.L2.Ker.Amb Fl)
    (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok)
    (ev : ∀ (Zs : DefSub A.fam.amb) t, (Fin ((A.side P1 ψ1 Zs).nV t) → Fl.K) →ₗ[Fl.K] V0X W Ch sel (mu t) Xg P)
    (Zs : DefSub A.fam.amb) (x : Mem) (t : A.fam.base.Tup) :
    (faceCol W Ch sel hX A P1 ψ1 Xg mu cst L hL hP Mem wd b hY Am hK hF ev Zs).Pt x t =
      colPer hX (hP t) Xg (Formalism.L2.Ker.chKerC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P (hK t x))
        (hF t x) (hL t) (ev Zs t) := rfl

end Face

section Sp

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

structure PerW (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) where

  Dt : Set X.B.I.GA
  hD : IsReps X u Dt
  hin : InHH X u hK
  hlin : PuLinear X u hK Dt

  F : Formalism.L2.Forms.Forms0 D u

  Tr : Transport X u F
  hI : ColDictInto X Tr hK
  hB : ColDictBij X Tr hK

variable {X}

def PerW.op {hK : X.LevelSubgroupCharacter} {u : D.what₂.Word} (p : PerW X hK u) : (D.mem u).A.Mu0 →ₗ[ℂ] HHX X :=
  Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X u hK p.Dt p.hD p.hin p.hlin ∘ₗ (colDict X p.Tr hK p.hI p.hB).symm.toLinearMap

def ramCrd {u : D.what₂.Word} {n : ℕ} (bR : Fin n → (D.mem u).A.Mram) : (Fin n → ℂ) →ₗ[ℂ] (D.mem u).A.Mu0 :=
  Submodule.inclusion inf_le_left ∘ₗ Fintype.linearCombination ℂ bR

def cjVec (s : Bool) (n : ℕ) : (Fin n → ℂ) →ₛₗ[cj s] (Fin n → ℂ) where
  toFun φ i := cj s (φ i)
  map_add' φ ψ := by funext i; simp
  map_smul' a φ := by funext i; simp

def perTw (s : Bool) {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] HHX X) : (Fin n → ℂ) →ₗ[ℂ] Tw s (HHX X) :=
  Tw.semi (σ := cj s) (σ' := RingHom.id ℂ) s (fun a => (cj_cj s a).symm) (f.comp (cjVec s n))

def spOf (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df) (hK : X.LevelSubgroupCharacter) (G : GoodOp X)
    (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) : SPer Dc where
  HH := Tw s (HHX X)
  nHH := inferInstance
  iHH := inferInstance
  Pu x := perTw s ((pw x).op ∘ₗ ramCrd (bR x))
  Rw := Tw.sub s ((goodSub X G).comap (HHX X).subtype)

section Facts

variable (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df) (hK : X.LevelSubgroupCharacter) (G : GoodOp X)
  (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)

theorem spOf_Pu (x : Dc.Mem) (φ : Fin (Dc.a x) → ℂ) :
    Tw.out (s := s) ((spOf s Dc hK G wdD pw bR).Pu x φ) = (pw x).op (ramCrd (bR x) (cjVec s _ φ)) := rfl

theorem mem_spOf_Rw (y : Tw s (HHX X)) :
    y ∈ (spOf s Dc hK G wdD pw bR).Rw ↔ ((Tw.out (s := s) y : HHX X) : L2X X) ∈ goodSub X G := Iff.rfl

theorem spOf_Rw_range {ι : D.s.HH ≃ₗᵢ[ℂ] HHX X} (h : RowDictTie X G ι) (y : Tw s (HHX X)) :
    y ∈ (spOf s Dc hK G wdD pw bR).Rw ↔ ∃ F : D.what₂.EE, ι (D.sEE F) = Tw.out (s := s) y := by
  rw [mem_spOf_Rw]
  obtain ⟨j, hj⟩ := h
  have hj' : ∀ F, ι (D.sEE F) = conjHH X G (j F) := hj
  constructor
  · intro hm
    have hF' : star ((Tw.out (s := s) y : HHX X) : L2X X) ∈ EEC X G := by
      rw [mem_EEC, star_star]; exact hm
    refine ⟨j.symm ⟨_, hF'⟩, ?_⟩
    rw [hj', LinearIsometryEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [conjHH_apply]
    exact star_star _
  · rintro ⟨F, hF⟩
    rw [← hF, hj', conjHH_apply]
    have h2 := (j F).2
    rw [mem_EEC] at h2
    exact h2

end Facts

end Sp

section Seam

open Classical in

structure ColSeam {D : D7} {Fl : Fields} {Pr : Primes Fl} (Ch : Chars Fl Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 Fl.F) → HeightOneSpectrum (𝓞 Fl.E)) {Sg : Set ℕ} (s : Formalism.L2.Ker.Seam D Fl) (σK : Fl.K →+* ℂ)
    (Gc : ChGlob Fl D.R.m) (C : Formalism.L2.Host.CharFrame D) (Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))) {T : Type}
    (mu : T → Tup Fl.F Fl.E Fl.K Sg) (Q : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (P : LevFam Fl.E Fl.K D.R.r Pr.vGs) : Prop where
  ok : s.Ok
  sig : s.σ₀ = σK
  sigG : Gc.σ₀ = σK
  xi0 : s.iE Gc.xi0 = D.host.xi0
  mu0 : ∀ j, Gc.mu0 j = Formalism.L2.Host.CT.transport s.iE (C.mu0 j)
  vGs : Pr.vGs.image (Formalism.L2.Host.CT.plMap s.iE) = Pg
  twQ : ∀ t, (QE sel (mu t : Chr Fl.F Fl.E Fl.K)).image (Formalism.L2.Host.CT.plMap s.iE) = Q t
  lev : P = rPsymF Ch

end Seam

section FaceSp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}

def faceSp (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (s : Bool) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hK : X.LevelSubgroupCharacter)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (wdD : ∀ Zs, (Dc Zs).Mem → D.what₂.Word) (pw : ∀ Zs x, PerW X hK (wdD Zs x))
    (bR : ∀ Zs x, Fin ((Dc Zs).a x) → (D.mem (wdD Zs x)).A.Mram) (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) : Face D A where
  P0 := P0
  ψ0 := ψ0
  P1 := P1
  ψ1 := ψ1
  Dc := Dc
  Sp Zs := spOf s (Dc Zs) hK Gd (wdD Zs) (pw Zs) (bR Zs)
  Zsc := Zsc

end FaceSp

end Formalism.IndefR.Cx
end
end

