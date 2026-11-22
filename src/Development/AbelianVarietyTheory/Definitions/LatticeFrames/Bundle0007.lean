import Mathlib
import Formalism.LocalToGlobal.HermitianForms.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar
import Formalism.LocalToGlobal.HermitianForms.TiedSym

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.MidChart
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
variable {D : D7}

abbrev EF (D : D7) : Type := D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F

section Gen
variable (θ : InfFam D) (V : HSp D) {n : ℕ} (hn : V.rank = n)

def finM (g : GA D V) : Matrix (Fin n) (Fin n) (EF D) :=
  ((mt V g).map (toEAf D)).reindex (finCongr hn) (finCongr hn)

def infM (g : GA D V) (τ : D.what₂.Tau) : Matrix (Fin n) (Fin n) ℂ :=
  (compAt θ τ (mt V g)).reindex (finCongr hn) (finCongr hn)

variable {J : Matrix (Fin n) (Fin n) D.host.E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (S : StepLevel D.host.F D.host.E (sigD D) J T f bad) {cl : Type}
  (yc : cl → UPts (sigD D) J (FiniteAdeleRing (𝓞 D.host.F) D.host.F))

def IsDec (x : Matrix (Fin n) (Fin n) (EF D)) (p : cl × GL (Fin n) D.host.E × S.U) : Prop :=
  p.2.1 ∈ UJ (sigD D : D.host.E →+* D.host.E) J ∧
    x = (bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) p.2.1 * (yc p.1).1 * p.2.2.1).1

def atFr {G : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ} (φ : Frames G → ℂ) (y : D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  if h : ∀ τ, IsUnit (y τ).det then φ ⟨y, h⟩ else 0

def rdS (ψ : cl → Frames (gramC J (embT D)) → ℂ) (y : Frames (gramC J (embT D))) (g : GA D V) : ℂ :=
  if h : ∃ p, IsDec S yc (finM V hn g) p then
    ((S.chi h.choose.2.2 : ℂˣ) : ℂ) * atFr (ψ h.choose.1) fun τ =>
      atInf (embT D) ((h.choose.2.1)⁻¹ : GL (Fin n) D.host.E).1 τ * infM θ V hn g τ * y.1 τ
  else 0

end Gen

structure Chart (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) where

  cl : Type

  inc : cl → (D.mem u).C.cls i

  K : LevelChart D (D.mem u).A.T (badG D) i hi (fun c : cl => (D.mem u).C.stab i (inc c)) (fun c => clsCrd D u i hi (inc c))

  eY : (D.mem u).C.Y i ≃ Fr D i hi

variable {u : D.what₂.Word}

def Chart.rd {i : ℕ} {hi : i ≤ D.R.m} (Q : Chart D u i hi) (θ : InfFam D)
    (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) (y : (D.mem u).C.Y i) : GA D (D.sp.X i) → ℂ :=
  rdS θ (D.sp.X i) (rankN D i hi) Q.K.lev Q.K.y (fun c z => ψ (Q.inc c) (Q.eY.symm z)) (Q.eY y)

section Sym
variable {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)

def endChart (i : ℕ) (hi : i ≤ D.R.m) (h : i = 0 ∨ i = D.R.m) : Chart D u i hi where
  cl := (D.mem u).C.cls i
  inc := id
  K := (F.cls i hi h).toChart
  eY := (F.val i hi h).eY

def midChart (i : ℕ) (h1 : 1 ≤ i) (h2 : i + 1 ≤ D.R.m) (β : Ch i) : Chart D u i (le_of_succ_m h2) where
  cl := {c // chOf i c = β}
  inc := Subtype.val
  K := F.ch i h1 h2 β
  eY := F.eYC i h1 h2

def chart (i : ℕ) (hi : i ≤ D.R.m) (β : Ch i) : Chart D u i hi :=
  if h : i = 0 ∨ i = D.R.m then endChart F i hi h else midChart F i (by omega) (by omega) β

def rd (θ : InfFam D) (i : ℕ) (hi : i ≤ D.R.m) (β : Ch i) (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ)
    (y : (D.mem u).C.Y i) : GA D (D.sp.X i) → ℂ :=
  (chart F i hi β).rd θ ψ y

def OnChart (i : ℕ) (hi : i ≤ D.R.m) (β : Ch i) (ψ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) : Prop :=
  ∀ c, c ∉ Set.range (chart F i hi β).inc → ψ c = 0

def rdP (θ : InfFam D) (z : (D.mem u).P.Wrow) (y : FrP D) : GA D D.sp.X' → ℂ :=
  rdS θ D.sp.X' (rankP D) F.clsP.lev F.clsP.y (F.valP.eW z) y

end Sym

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepsOnto
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.Core.Rk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000 in

structure Tower (D : D7) extends LevCh D Unit where

  θ : InfFam D

  ψ : AddChar (AF D.host.F) ℂ

  MY : ∀ j, DSModel (Yc D j) (parB (Ptw D) (min j D.R.m))

  MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)

  νY : ∀ j, Measure (GA D (Yc D j))
  fdY : ∀ j, Set (GA D (Yc D j))

  νX : Measure (GA D D.sp.X')
  fdX : Set (GA D D.sp.X')

  ωY : ∀ k, GA D (Yc D k) × GA D (Yc D (k + 1)) →* Module.End ℂ (WO (Yc D k) (Yc D (k + 1)) → ℂ)

  ωX : GA D (Yc D (D.R.m - 1)) × GA D D.sp.X' →* Module.End ℂ (WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ)

  vac : ∀ k, WO (Yc D k) (Yc D (k + 1)) → ℂ
  vacX : WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ

  vY : ∀ k, WO (Yc D k) (Yc D (k + 1)) → ℂ
  vX : WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ

  ItY : ∀ k, PolF D (Yc D (k + 1)).rank (Yc D k).rank →ₗ[ℂ] SmT (MY (k + 1)) →ₗ[ℂ] SmT (MY k)
  ItX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank →ₗ[ℂ] SmT MX →ₗ[ℂ] SmT (MY (D.R.m - 1))

  ioY : ∀ k, MultT θ (MY (k + 1)) (levS _ (βY (k + 1)) (toLevCh.datYt () (k + 1) toLevCh.triv))
      (levChi _ (βY (k + 1)) (toLevCh.datYt () (k + 1) toLevCh.triv)) →ₗ[ℂ]
    MultT θ (MY k) (levS _ (βY k) (toLevCh.datYt () k toLevCh.triv)) (levChi _ (βY k) (toLevCh.datYt () k toLevCh.triv))

  ioX : MultT θ MX (levS _ βX (toLevCh.datXt ())) (levChi _ βX (toLevCh.datXt ())) →ₗ[ℂ]
    MultT θ (MY (D.R.m - 1)) (levS _ (βY (D.R.m - 1)) (toLevCh.datYt () (D.R.m - 1) toLevCh.triv))
      (levChi _ (βY (D.R.m - 1)) (toLevCh.datYt () (D.R.m - 1) toLevCh.triv))

namespace Tower

variable {D : D7} (W : Tower D)

abbrev Lv : Type := LevelP W.Pg D.R.r ℂ

abbrev CP (P : W.Lv) (j : ℕ) : Submodule ℂ (SmT (W.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) :=
  MultT W.θ (W.MY j) (levS _ (W.βY j) (W.datYt () j P)) (levChi _ (W.βY j) (W.datYt () j P))

abbrev CC (j : ℕ) : Submodule ℂ (SmT (W.MY j) →ₗ[ℂ] (GA D (Yc D j) → ℂ)) := W.CP W.triv j

def datXP (P : W.Lv) : LevDat D.host.E ℂ D.sp.X'.rank :=
  datY _ D.R.r D.R.t D.R.m r_le_X W.Pg (W.Q ()) P W.chi (W.xiR ()) Frm.B

abbrev CXP (P : W.Lv) : Submodule ℂ (SmT W.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) :=
  MultT W.θ W.MX (levS _ W.βX (W.datXP P)) (levChi _ W.βX (W.datXP P))

abbrev CX : Submodule ℂ (SmT W.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) :=
  MultT W.θ W.MX (levS _ W.βX (W.datXt ())) (levChi _ W.βX (W.datXt ()))

def ptY (k : ℕ) : PolF D (Yc D (k + 1)).rank (Yc D k).rank → (WO (Yc D k) (Yc D (k + 1)) → ℂ) :=
  pureTensorO W.ψ W.θ (Yc D k) (Yc D (k + 1)) (cart (W.MY k)) (cart (W.MY (k + 1))) (onb (W.MY k)) (onb (W.MY (k + 1))) (W.vY k)

def ptX : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank → (WO (Yc D (D.R.m - 1)) D.sp.X' → ℂ) :=
  pureTensorO W.ψ W.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (W.MY (D.R.m - 1))) (cart W.MX) (onb (W.MY (D.R.m - 1))) (onb W.MX) W.vX

structure Pre : Prop where
  chars : W.toLevCh.Is ()
  inf : IsInfFam W.θ
  std : IsStdChar D W.ψ (-1)
  νY : ∀ j, j + 1 < D.R.m → IsMeasFD (Yc D j) (lev D.sp.cm (Yc D j).gram (W.βY j) (W.datYt () j W.triv)) (W.νY j) (W.fdY j)
  νY' : IsMeasDef (Yc D (D.R.m - 1))
    (lev D.sp.cm (Yc D (D.R.m - 1)).gram (W.βY (D.R.m - 1)) (W.datYt () (D.R.m - 1) W.triv)) (W.νY (D.R.m - 1)) (W.fdY (D.R.m - 1))
  νX : IsMeasDef D.sp.X' (lev D.sp.cm D.sp.X'.gram W.βX (W.datXt ())) W.νX W.fdX
  ωY : ∀ k, k + 1 < D.R.m → IsWeilDatumO W.ψ (Yc D k) (Yc D (k + 1)) (Lift.chrStep (W.toLevCh.mu ()) W.eta (k + 1)).1
    (Lift.chrStep (W.toLevCh.mu ()) W.eta (k + 1)).2 (W.ωY k)
  ωX : IsWeilDatumO W.ψ (Yc D (D.R.m - 1)) D.sp.X' (Lift.chrStep (W.toLevCh.mu ()) W.eta D.R.m).1
    (Lift.chrStep (W.toLevCh.mu ()) W.eta D.R.m).2 W.ωX
  vY : ∀ k, k + 1 < D.R.m → IsStepVecOf W.ψ W.θ (Yc D k) (Yc D (k + 1)) (cart (W.MY k)) (cart (W.MY (k + 1))) (W.ΛY k)
    (W.ΛY (k + 1)) (W.βY k) (W.βY (k + 1)) (W.datYt () k W.triv) (W.chi (k + 1)) (W.Q ()) (W.xiR ()) (W.vac k) (W.vY k)
  vX : IsStepVecOf W.ψ W.θ (Yc D (D.R.m - 1)) D.sp.X' (cart (W.MY (D.R.m - 1))) (cart W.MX) (W.ΛY (D.R.m - 1)) W.ΛX
    (W.βY (D.R.m - 1)) W.βX (W.datYt () (D.R.m - 1) W.triv) (W.chi D.R.m) (W.Q ()) (W.xiR ()) W.vacX W.vX
  ptY : ∀ k, k + 1 < D.R.m → ∀ P, IsThetaFunO W.ψ (Yc D k) (Yc D (k + 1)) (W.ptY k P)
  ptX : ∀ P, IsThetaFunO W.ψ (Yc D (D.R.m - 1)) D.sp.X' (W.ptX P)
  ItY : ∀ k, k + 1 < D.R.m → IsItW W.θ (W.MY k) (W.MY (k + 1)) (W.ωY k) (W.ptY k) (W.ItY k)
  ItX : IsItW W.θ (W.MY (D.R.m - 1)) W.MX W.ωX W.ptX W.ItX

structure Is : Prop extends W.Pre where
  ioY : Lift.IsChainIo W.CC (D.R.m - 1) W.νY W.fdY (fun k => thetaKO (W.ωY k)) W.ptY W.ItY W.ioY
  ioX : Lift.IsIo W.νX W.fdX (thetaKO W.ωX) W.ptX W.ItX _ _ W.ioX

def thDn : W.CX →ₗ[ℂ] W.CC 0 := Lift.thetaDn W.CC W.ioY (D.R.m - 1) ∘ₗ W.ioX

def IsDn (T : SmT W.MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)) (T₀ : SmT (W.MY 0) →ₗ[ℂ] (GA D (Yc D 0) → ℂ)) : Prop :=
  ∃ h : T ∈ W.CX, T₀ = (W.thDn ⟨T, h⟩ : W.CC 0)

def DnLev (P : W.Lv) : Prop := ∀ T ∈ W.CXP P, ∃ T₀ ∈ W.CP P 0, W.IsDn T T₀

def Onto (P : W.Lv) : Prop := ∀ T₀ ∈ W.CP P 0, ∃ T ∈ W.CXP P, W.IsDn T T₀

def Onto1 : Prop := Function.Surjective W.thDn

def StepsOnto : Prop := (∀ k, k + 1 < D.R.m → Function.Surjective (W.ioY k)) ∧ Function.Surjective W.ioX

end Tower

end GlobalTheory.Core.Rk

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
open scoped TensorProduct

namespace GlobalTheory.Core.Rk.Top

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {u : D.what₂.Word}

def HasMat (h : GA D D.sp.X')
    (y : GL (Fin (D.R.N D.R.m - 1)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Prop :=
  h ∈ GfC D.sp.X' ∧ ∀ i j, (Formalism.UG.bc (Lev.swapAE D) (finHom D.sp.X' h)).1 i j = y.1 (finCongr (rankP D) i) (finCongr (rankP D) j)

def TopLev (K : ClsPTied u) (J : Set (GA D D.sp.X')) (χ : GA D D.sp.X' → ℂ) : Prop :=
  (∀ h, h ∈ J ↔ ∃ κ : K.lev.U, HasMat h κ.1) ∧ ∀ h (κ : K.lev.U), HasMat h κ.1 → χ h = star ((K.lev.chi κ : ℂˣ) : ℂ)

open Classical in

structure IsJ (u : D.what₂.Word) {S : D.what₂.Tau → SPar} (M : DSModel D.sp.X' S) (j : SmT M →ₗ[ℂ] (FrP D → ℂ)) : Prop where
  inj : Function.Injective j
  range : LinearMap.range j = ValC (gramC (gramP D) (embT D)) (sgT u)
  eqv : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
    ∀ y y' : FrP D, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr (rankP D)) (finCongr (rankP D)))) y' y →
      j (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = j (PiTensorProduct.tprod ℂ v) y'

open Classical in

def TopFormula {K : ClsPTied u} (V : ValPTied u K) {S : D.what₂.Tau → SPar} (M : DSModel D.sp.X' S) (j : SmT M →ₗ[ℂ] (FrP D → ℂ))
    (eT : (D.mem u).P.Mt → SmT M →ₗ[ℂ] (GA D D.sp.X' → ℂ)) : Prop :=
  ∀ (F : (D.mem u).P.Mt) (c : (D.fm u).clsP) (v : SmT M) (h : GA D D.sp.X'), HasMat h (K.y c).1 →
    eT F v h = (Nat.card ((D.fm u).stabilizer₂ c) : ℂ) * (D.mem u).P.period (V.eW.symm (Pi.single c (j v))) F

end GlobalTheory.Core.Rk.Top

end
end

