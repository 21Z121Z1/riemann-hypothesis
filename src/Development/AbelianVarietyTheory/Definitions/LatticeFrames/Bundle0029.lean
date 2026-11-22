import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0027
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0260
import Formalism.LocalToGlobal.Columns.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HtPsiLeIffExists
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotInhAbsOfGamLe
import Formalism.LocalRingCardinality.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotBadPrimeBase
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0104

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.BuiltCols
section
noncomputable section

namespace GlobalTheory.Core.Rk

open NumberField Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2

def BuiltCols (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    I.Ok ∧ TC.Pins B X ∧ I.IsTw ∧ ColIn.JetsIn I ∧ D = I.rec7 l Z

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev MtTrue : HLat B.LL :=
  MtildeH (Pr := B.primes X) B.wts I.Ch (GlobalTheory.Mem.FieldsLaws.fields_ok B) I.sel (I.tup I.mu0) I.Ps

variable (l : I.Laws) (u : B.Word)

def IsRowEmb (j : (MtTrue I).V →ₛₗ[B.embLL] (I.per l u I.mu0).Mt) : Prop :=
  ∀ (z : (MtTrue I).V) (p : (I.stX I.mu0).D ()),
    (j z).1 () p = MvPolynomial.map B.embLL (z.1 (toRow I.sel (I.tup I.mu0) p.1.1)).1

def IsPerTrue (j : (MtTrue I).V →ₛₗ[B.embLL] (I.per l u I.mu0).Mt)
    (e : (I.fm l u I.mu0).ptLat.V →ₗ[B.LL] Module.Dual B.LL (MtTrue I).V) : Prop :=
  ∀ x z, B.embLL (e x z) = (I.per l u I.mu0).period ((I.fm l u I.mu0).ptEmb x) (j z)

def AmbIsTrue (Z : TC.Later B (I.cols l)) (Am : AmbForm (I.rec7 l Z) (RowSide.sharp (I.rec7 l Z))) : Prop :=
  ∃ s : (MtTrue I).V ≃ₗ[B.LL] (show HLat B.LL from Mt (I.rec7 l Z) Am).V,
    (∀ z, s z ∈ (show HLat B.LL from Mt (I.rec7 l Z) Am).L ↔ z ∈ (MtTrue I).L) ∧
    (∀ (v : InfinitePlace B.LL) z,
      Formalism.HermitianLatticesTheory.normAt (show HLat B.LL from Mt (I.rec7 l Z) Am).b (show HLat B.LL from Mt (I.rec7 l Z) Am).X v (s z) =
        Formalism.HermitianLatticesTheory.normAt (MtTrue I).b (MtTrue I).X v z) ∧
    ∀ (w : B.Word) (j : (MtTrue I).V →ₛₗ[B.embLL] (I.per l w I.mu0).Mt), IsRowEmb I l w j → ∀ z,
      ((I.rec7 l Z).eMt w).symm (Am.jAmb (I.rec7 l Z).what₂.mu0 (s z)) = j z

end GlobalTheory.Core.Rk

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsRatDatum
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

def intVec (D : D7) (n : ℕ) : Set (Fin n → D.host.E) := {x | ∀ k, IsIntegral ℤ (x k)}

def IsFinComb {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ (n : ℕ) (c : Fin n → ℂ) (x : Fin n → WO S T), (∀ k, (x k).map (infPart D) = 0) ∧ f = ∑ k, c k • heisO ψ S T (x k) f₀

abbrev stdHom {D : D7} (S T : HSp D) : AddSubgroup (WO S T) := latO S T (intVec D S.rank) (intVec D T.rank) fun _ => True

def IsRatDatum {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D)
    (Ξ : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ) (f₀ f : WO S T → ℂ) : Prop :=
  ∃ Φ : WO S T → ℂ, IsSBHalf e (stdHom S T) Φ ∧ (∀ γ, Φ (γ.map fun a => e * incA D a) = Ξ γ) ∧
    IsThetaAt ψ (symplO S T) (heisO ψ S T) e (stdHom S T) 1 f₀ Φ f

section Dat
variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word)

structure ColDat (Ch : ℕ → Type) where

  ch : ∀ i, Ch i

  chr : ℕ → ((AE (I.rec7 l Z))ˣ →* Circle)

  om : ∀ i, Om ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1))

  vac : ∀ i, WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ

  w : ∀ i, WO ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) → ℂ

  μ : ∀ i, Measure (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))
  fd : ∀ i, Set (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i))

  e : AE (I.rec7 l Z)

  kb : ∀ i, TC.GA B (B.R.N i)
  b0 : ∀ i, Idx I.sel (I.tup I.mu0) (I.idx I.mu0) i
  p0 : ∀ i, PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u i

variable {I l Z u} {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i}

namespace ColDat
variable (A : ColDat I l Z u Ch) (F : FormsTiedSym (I.rec7 l Z) u Ch chOf)
  (ψ : AddChar (AF (I.rec7 l Z).host.F) ℂ) (θ : InfFam (I.rec7 l Z))

def xi (i : ℕ) (hi : i + 1 ≤ B.R.m)
    (γ : Matrix (Fin ((I.rec7 l Z).sp.X (i + 1)).rank) (Fin ((I.rec7 l Z).sp.X i).rank) (I.rec7 l Z).host.E) : ℂ :=
  B.embLL (xiAt I.Ch I.sel (I.tup I.mu0) (I.cst I.mu0) (I.idx I.mu0) u i (A.b0 i) (A.b0 (i + 1)) (A.p0 i) (A.p0 (i + 1))
    (Matrix.toLin' (γ.reindex (finCongr (rankN (I.rec7 l Z) (i + 1) hi)) (finCongr (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi))))))

abbrev Q (i : ℕ) (hi : i ≤ B.R.m) : Chart (I.rec7 l Z) u i hi := chart F i hi (A.ch i)

structure Is : Prop where
  std : IsStdChar (I.rec7 l Z) ψ (-1)
  inf : IsInfFam θ
  chr : ∀ j : Fin B.R.m, ChrEq (A.chr ((j : ℕ) + 1)) (I.C.mu0 j)
  om : ∀ i, i < B.R.m → IsWeilDatumO ψ _ _ (A.chr (i + 1)) (A.chr (i + 1)) (A.om i)
  vac : ∀ i, i < B.R.m → IsVacO ψ θ _ _ (fun _ => 1) (fun _ => 1) (intVec _ _) (intVec _ _) (A.vac i)
  idem : IsIdemSum A.e (Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup I.mu0) u)
  datum : ∀ i (hi : i + 1 ≤ B.R.m), IsRatDatum ψ _ _ A.e (A.xi i hi) (A.vac i) (A.w i)
  comb : ∀ i, i < B.R.m → IsFinComb ψ _ _ (A.vac i) (A.w i)
  haar : ∀ i, i ≤ B.R.m → (A.μ i).IsHaarMeasure ∧ IsFundamentalDomain (GQ ((I.rec7 l Z).sp.X i)) (A.fd i) (A.μ i)

  base : ∀ i, i ≤ B.R.m → TC.PtOf (A.kb i) (A.p0 i).1.1 ∧ (A.p0 i).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)

  chart_ne : ∀ i hi, Nonempty (A.Q F i hi).cl
  rep : ∀ i hi (c : (A.Q F i hi).cl),
    TC.PtOf ((show TC.GA B (B.R.N i) from ((A.Q F i hi).K.y c).1) * A.kb i) ((I.stp u I.mu0 i).rep ((A.Q F i hi).inc c)).1.1 ∧
      (show (I.stp u I.mu0 i).Cl from (A.Q F i hi).inc c).1 = A.b0 i ∧
      cosetIn ((I.stp u I.mu0 i).rep ((A.Q F i hi).inc c)) = cosetIn (A.p0 i)

def IsForm (i : ℕ) (hi : i ≤ B.R.m) (φ : ((I.rec7 l Z).mem u).C.cls i → ((I.rec7 l Z).mem u).C.Y i → ℂ) : Prop :=
  φ ∈ ((I.rec7 l Z).fm u).Fi i ∧ OnChart F i hi (A.ch i) φ

def Keeps : Prop :=
  ∀ i (hi : i + 1 ≤ B.R.m) φ, A.IsForm F i (Nat.le_of_succ_le hi) φ → A.IsForm F (i + 1) hi (((I.rec7 l Z).mem u).C.K i φ)

abbrev rd (i : ℕ) (hi : i ≤ B.R.m) := (A.Q F i hi).rd θ

def pt (i : ℕ) := pureTensorO ψ θ ((I.rec7 l Z).sp.X i) ((I.rec7 l Z).sp.X (i + 1)) (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) (A.w i)

def KJstep : Prop :=
  ∀ i (hi : i + 1 ≤ B.R.m) (y : ((I.rec7 l Z).mem u).C.Y i) P, ∃ a : ((I.rec7 l Z).mem u).C.Y (i + 1) →₀ ℂ,
    ∀ φ, A.IsForm F i (Nat.le_of_succ_le hi) φ →
      liftT (A.om i) (A.μ i) (A.fd i) (A.rd F θ i (Nat.le_of_succ_le hi) φ y) (A.pt ψ θ i P) =
        a.sum fun y' s => s • A.rd F θ (i + 1) hi (((I.rec7 l Z).mem u).C.K i φ) y'

def KJback : Prop :=
  ∀ i (hi : i + 1 ≤ B.R.m) (y' : ((I.rec7 l Z).mem u).C.Y (i + 1)), ∃ (n : ℕ) (y : Fin n → ((I.rec7 l Z).mem u).C.Y i) (P : Fin n → _),
    ∀ φ, A.IsForm F i (Nat.le_of_succ_le hi) φ →
      A.rd F θ (i + 1) hi (((I.rec7 l Z).mem u).C.K i φ) y' =
        ∑ k, liftT (A.om i) (A.μ i) (A.fd i) (A.rd F θ i (Nat.le_of_succ_le hi) φ (y k)) (A.pt ψ θ i (P k))

def KJCoreAt : Prop :=
  ∀ i (hi : i + 1 ≤ B.R.m), ∃ c₀ s : ℂ, c₀ ≠ 0 ∧ s ≠ 0 ∧
    ∀ (c : (A.Q F i (Nat.le_of_succ_le hi)).cl) (c' : (A.Q F (i + 1) hi).cl) g g', g ∈ GfC _ → g' ∈ GfC _ →
      finM _ (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) g = ((A.Q F i (Nat.le_of_succ_le hi)).K.y c).1.1 →
      finM _ (rankN (I.rec7 l Z) (i + 1) hi) g' = ((A.Q F (i + 1) hi).K.y c').1.1 → ∀ P,
      thetaKO (A.om i) g g' (A.pt ψ θ i P) =
        c₀ * (I.chIn u I.mu0).rho i ((A.Q F i (Nat.le_of_succ_le hi)).inc c) * (I.chIn u I.mu0).rho' i ((A.Q F (i + 1) hi).inc c') *
          ∑ k ∈ P.support, P.coeff k * Formalism.L2.Ker.jetC (fun _ => s)
            (I.th u I.mu0 i _ _ ((I.stp u I.mu0 i).rep ((A.Q F i (Nat.le_of_succ_le hi)).inc c))
              ((I.stp u I.mu0 (i + 1)).rep ((A.Q F (i + 1) hi).inc c')))
            (k.mapDomain fun v => (v.1, Fin.cast (rankN (I.rec7 l Z) (i + 1) hi) v.2.1,
              Fin.cast (rankN (I.rec7 l Z) i (Nat.le_of_succ_le hi)) v.2.2))

end ColDat
end Dat

def RamAt {D : D7} (u : D.what₂.Word) (i : ℕ) (φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ) : Prop :=
  ∀ v c, ∑ a : ((D.mem u).A.Fv v)ˣ, (D.fm u).dilT i v a c (φ ((D.fm u).dil i v a c)) = 0

def IsEmbTop {D : D7} (z0 : Fin (D.R.N D.R.m) → D.host.E) (emb : GA D D.sp.X' →* GA D (D.sp.X D.R.m)) : Prop :=
  ∀ h, IsExt D z0 (incA D) ((mt _ h).reindex (finCongr (rankP D)) (finCongr (rankP D)))
    ((mt _ (emb h)).reindex (finCongr (rankN D _ le_rfl)) (finCongr (rankN D _ le_rfl)))

def PerLast {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    (W : Tower D) (L : Link D u W) : Prop :=
  ∀ emb, IsEmbTop F.til.z0 emb → ∀ (y : (D.mem u).C.Y D.R.m) (v : SmT W.MX), ∃ a : ℂ,
    ∀ φ ∈ (D.fm u).Fi D.R.m, ∀ G : (D.mem u).P.Mt,
      ∫ h in W.fdX, (L.eT G).1 v h * (endChart F D.R.m le_rfl (Or.inr rfl)).rd W.θ φ y (emb h) ∂W.νX =
        a * (D.mem u).P.Ptil φ G

def TopForm {D : D7} {u : D.what₂.Word} {Ch : ℕ → Type} {chOf : ∀ i, (D.mem u).C.cls i → Ch i} (F : FormsTiedSym D u Ch chOf)
    {par} (M : Formalism.IndefR.Mult.DSModel D.sp.X' par) (eT : (D.mem u).P.Mt → SmT M → GA D D.sp.X' → ℂ) : Prop :=
  ∃ J : SmT M →ₗ[ℂ] (FrP D → ℂ), Function.Injective J ∧ (∀ v, J v ∈ ValC (gramC (gramP D) (embT D)) (sgT u)) ∧
    (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D D.sp.X' τ), ∀ (v : M.Vec) (w : M.sm τ), (w : M.H τ) = M.rep τ g (v τ) →
      ∀ y y' : FrP D, IsTr (Function.update (fun _ => 1) τ (g.reindex (finCongr (rankP D)) (finCongr (rankP D)))) y' y →
        J (PiTensorProduct.tprod ℂ (Function.update v τ w)) y = J (PiTensorProduct.tprod ℂ v) y') ∧
    ∀ (G : (D.mem u).P.Mt) (c : (D.fm u).clsP) (v : SmT M) (h : GA D D.sp.X'), h ∈ GfC D.sp.X' →
      finM _ (rankP D) h = (F.clsP.y c).1.1 →
      eT G v h = (Nat.card ((D.fm u).stabilizer₂ c) : ℂ) * (D.mem u).P.period (F.valP.eW.symm (Pi.single c (J v))) G

structure PinColAt {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word}
    {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (d : GlobalTheory.SeeSaw.Dat (I.rec7 l Z) u)
    (F : FormsTiedSym (I.rec7 l Z) u Ch chOf) (A : ColDat I l Z u Ch) : Prop where
  is : A.Is F d.c.ψ d.c.θ
  keeps : A.Keeps F
  rd : ∀ j (hj : j ≤ B.R.m), d.rd j = A.rd F d.c.θ j hj
  ram : ∀ j (hj : j ≤ B.R.m) φ, φ ∈ d.Ram j ↔ A.IsForm F j hj φ ∧ RamAt (D := I.rec7 l Z) u j φ
  om : ∀ j, j < B.R.m → (d.k j).om = A.om j
  vac : ∀ j, j < B.R.m → (d.k j).vac = A.vac j
  w : ∀ j, j < B.R.m → GlobalTheory.SeeSaw.comb d.c.ψ _ _ (d.k j).c (d.k j).vac = A.w j
  x : ∀ j, j ≤ B.R.m → (d.x j).s = (fun _ => 1) ∧ (d.x j).B = (fun _ => 1) ∧ (∀ z, z ∈ (d.x j).L ↔ z ∈ intVec (I.rec7 l Z) _) ∧
    (d.x j).vol.μ = A.μ j ∧ (d.x j).vol.𝓕 = A.fd j
  emb : IsEmbTop F.til.z0 ((d.oT B.R.m rfl).emb.comp (MonoidHom.inl _ _))
  top : TopForm F d.top.M fun G v => (d.eT G).1 v
  onto : d.TopOnto

def PinCol {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} (w : World I l Z) {u : B.Word}
    (d : GlobalTheory.SeeSaw.Dat (I.rec7 l Z) u) : Prop :=
  ∃ A : ColDat I l Z u (w.C.herm.base.Ch u), PinColAt d (w.C.forms u) A

def KJCore : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word)
    (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → A.KJCoreAt (w.C.forms u) ψ θ

def KJ : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word)
    (A : ColDat I l Z u (w.C.herm.base.Ch u)) ψ θ, A.Is (w.C.forms u) ψ θ → A.KJstep (w.C.forms u) ψ θ

def ColDatEx : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z), I.IsTw → ∀ (u : B.Word) ψ θ,
    IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ →
    ∃ A : ColDat I l Z u (w.C.herm.base.Ch u), A.Is (w.C.forms u) ψ θ ∧ A.Keeps (w.C.forms u)

def PerAll : Prop :=
  ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z) (u : B.Word)
    (W : Tower (I.rec7 l Z)) (L : Link (I.rec7 l Z) u W), W.Is → L.TopPin (w.C.forms u) → PerLast (w.C.forms u) W L

end GlobalTheory.AdForm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsScaleWithBoundedGamma
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S

namespace GlobalTheory.Core.Rk

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

def TrueF (D : D7) : Prop :=
  ∃ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)),
    D = I.rec7 l Z ∧ I.IsTw ∧ ∃ w : World I l Z, IdE w.S.X

open GlobalTheory.Mem GlobalTheory.Mem.Col2 in

theorem TrueF.elim {Q : D7 → Prop}
    (h : ∀ (B : Base) (X : PreX B.toPre) (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (w : World I l Z),
      I.IsTw → IdE w.S.X → Q (I.rec7 l Z)) {D : D7} (hD : TrueF D) : Q D := by
  obtain ⟨B, X, I, l, Z, rfl, h1, w, hw⟩ := hD
  exact h B X I l Z w h1 hw

def BigGap (D : D7) : Prop := D.NodeGap (4 * ((D.R.N D.R.m : ℕ) : ℝ) ^ 3 + 2 * D.R.t + 6)

def CanE (D : D7) (_L _C' : ℝ) : Prop := TrueF D ∧ BigGap D

def IsScaleWithBoundedGamma (D : D7) (L C' : ℝ) : Prop := ∃ large₂ : SizeData₂ D, large₂.sc.L = L ∧ 8 * large₂.CGam ≤ C' ∧ 1 ≤ large₂.CGam

def StdE (D : D7) (L C' : ℝ) : Prop := CanE D L C' ∧ IsScaleWithBoundedGamma D L C'

theorem Row.mono {E E' : D7 → ℝ → ℝ → Prop} (hE : ∀ D L C', E' D L C' → E D L C') {Q : ∀ D : D7, D.what₂.Word → ℝ → ℝ → Prop}
    (h : Row E Q) : Row E' Q := fun Cg cb Cu cT CT h1 h2 =>
  let ⟨C, a, b, hC, h⟩ := h Cg cb Cu cT CT h1 h2
  ⟨C, a, b, hC, fun C' Cl ha hb D L u hD he hH => h C' Cl ha hb D L u hD (hE _ _ _ he) hH⟩

def RKStd : Prop := RKFam StdE

def JointEx (E : D7 → ℝ → ℝ → Prop) : Prop :=
  ∃ Cg cb Cu cT CT : ℝ, 0 < cb ∧ 0 < cT ∧ ∀ C C'₀ Cl₀ : ℝ, ∃ (C' Cl L : ℝ) (D : D7), C'₀ ≤ C' ∧ Cl₀ ≤ Cl ∧
    TrueE D ∧ E D L C' ∧ HD D L C' Cl Cg cb Cu cT CT ∧ ∀ u, RankMu D u ∧ C * mfL D L ≤ Real.log (D.mem u).A.GamP

end GlobalTheory.Core.Rk

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.LatticeFrames.NotUnitRatioBase
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.Core.Rk.Top GlobalTheory.Core.Rk.Top.Model
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam.Check

variable {D : D7}

section Read

variable {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {Pm : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A Pm} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
  (K : ClassesAtPrimes M bad)

theorem levG_exists (x : GA D D.sp.X') : ∃ J χ, LevG K x J χ ∧ ∀ κ : K.lev.U, ∃ h, HasMat h κ.1 ∧ x⁻¹ * h * x ∈ J := by
  let χ : GA D D.sp.X' → ℂ := fun h => if hh : ∃ κ : K.lev.U, HasMat h κ.1 then star ((K.lev.chi hh.choose : ℂˣ) : ℂ) else 0
  have hχ : ∀ h (κ : K.lev.U), HasMat h κ.1 → χ h = star ((K.lev.chi κ : ℂˣ) : ℂ) := by
    intro h κ hk
    have hh : ∃ κ : K.lev.U, HasMat h κ.1 := ⟨κ, hk⟩
    simp only [χ, dif_pos hh]
    rw [show hh.choose = κ from Subtype.ext (hasMat_mat hh.choose_spec hk)]
  have e : ∀ h : GA D D.sp.X', x * (x⁻¹ * h * x) * x⁻¹ = h := fun h => by group
  refine ⟨{k | ∃ κ : K.lev.U, HasMat (x * k * x⁻¹) κ.1}, fun k => χ (x * k * x⁻¹), ⟨fun h => ?_, fun h κ hk => ?_⟩, fun κ => ?_⟩
  · simp only [Set.mem_setOf_eq, e]
  · simp only [e]; exact hχ h κ hk
  · obtain ⟨h, hh⟩ := hasMat_exists ⟨κ.1, ((K.lev.U_eq _).1 κ.2).1⟩
    exact ⟨h, hh, κ, by rw [e]; exact hh⟩

theorem levG_type {x : GA D D.sp.X'} {J : Set (GA D D.sp.X')} {χ : GA D D.sp.X' → ℂ} (hL : LevG K x J χ) (f : GA D D.sp.X' → ℂ)
    (hf : ∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) (g h : GA D D.sp.X') (κ : K.lev.U) (hk : HasMat h κ.1) :
    f (g * h * x) = star ((K.lev.chi κ : ℂˣ) : ℂ) * f (g * x) := by
  rw [← hL.2 h κ hk, ← hf _ ((hL.1 h).2 ⟨κ, hk⟩)]
  congr 1; group

variable {S : D.what₂.Tau → SPar} {MX : DSModel D.sp.X' S} (eW : Pm.Wrow ≃ₗ[ℂ] (M.clsP → FrP D → ℂ))
  (j : SmT MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X')

theorem y_inj : Function.Injective fun c => (K.y c).1 := fun a b h =>
  K.y_bij.1 (by have : K.y a = K.y b := Subtype.ext h
                simp only [this])

theorem readsG_exists (G : Pm.Mt) : ∃ f, ReadsG K eW j x G f := by
  let φ : M.clsP → SmT MX →ₗ[ℂ] ℂ := fun c => (Nat.card (M.stabilizer₂ c) : ℂ) •
    ((Pm.period.flip G) ∘ₗ (eW.symm : _ →ₗ[ℂ] Pm.Wrow) ∘ₗ (LinearMap.single ℂ (fun _ => FrP D → ℂ) c) ∘ₗ j)
  refine ⟨LinearMap.pi fun g => if hh : ∃ c, HasMat (g * x⁻¹) (K.y c).1 then φ hh.choose else 0, fun c v h hc => ?_⟩
  have hh : ∃ c, HasMat (h * x * x⁻¹) (K.y c).1 := ⟨c, by rwa [mul_inv_cancel_right]⟩
  have e : hh.choose = c := y_inj K (hasMat_mat hh.choose_spec (by rwa [mul_inv_cancel_right]))
  simp only [LinearMap.pi_apply, dif_pos hh, e, φ]
  simp

theorem ReadsG.period_eq {G G' : Pm.Mt} {f : SmT MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)} (h : ReadsG K eW j x G f) (h' : ReadsG K eW j x G' f)
    (w : Pm.Wrow) (hw : ∀ c, eW w c ∈ LinearMap.range j) : Pm.period w G = Pm.period w G' := by
  choose v hv using hw
  have e : w = ∑ c, eW.symm (Pi.single c (j (v c))) := by
    rw [← map_sum, LinearEquiv.eq_symm_apply]
    simp only [hv]
    exact (Finset.univ_sum_single _).symm
  rw [e, map_sum, LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  obtain ⟨g, hg⟩ := hasMat_exists (K.y c)
  have hc : (Nat.card (M.stabilizer₂ c) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := M.stabilizer₂ c)).ne'
  exact mul_left_cancel₀ hc ((h c _ g hg).symm.trans (h' c _ g hg))

theorem not_readsG_zero {G : Pm.Mt} (w : Pm.Wrow) (hw : ∀ c, eW w c ∈ LinearMap.range j) (hG : Pm.period w G ≠ 0) :
    ¬ ReadsG K eW j x G 0 := fun h =>
  hG (by simpa using ReadsG.period_eq K eW j x h (readsG_zero K eW j x) w hw)

theorem ReadsG.scalar {G : Pm.Mt} {f : SmT MX →ₗ[ℂ] (GA D D.sp.X' → ℂ)} {a : ℂ} (h : ReadsG K eW j x G f)
    (h' : ReadsG K eW (a • j) x G f) (w : Pm.Wrow) (hw : ∀ c, eW w c ∈ LinearMap.range j) (hG : Pm.period w G ≠ 0) : a = 1 := by
  have h2 : ReadsG K eW j x (a • G) f := fun c v g hg => by
    rw [h' c v g hg]
    simp [Pi.single_smul']
  have := ReadsG.period_eq K eW j x h h2 w hw
  rw [map_smul, smul_eq_mul] at this
  exact (mul_right_cancel₀ hG (this.symm.trans (one_mul _).symm))

end Read

section Package

variable {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks]
  [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {P : LevelP R.Pg D.R.r ℂ} {u : D.what₂.Word} {g : Geo D}

theorem chars_agree {t : T} {r : RowCh R P u g t} (h : r.Is) :
    (∀ j ρ hj, ((r.sBF j ρ hj).χV, (r.sBF j ρ hj).χW) = Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1)) ∧
    ∀ j σ hj, ((r.sFB j σ hj).χV, (r.sFB j σ hj).χW) = Lift.chrStep (R.toLevCh.mu t) R.eta (j + 1 + 1) := by
  obtain ⟨a, ha⟩ := D.R.m_even
  refine ⟨fun j ρ hj => ?_, fun j σ hj => ?_⟩
  · have : Odd (j + 1) := ⟨a - ρ - 1, by omega⟩
    rw [(h.sBF j ρ hj).2.2.1, (h.sBF j ρ hj).2.2.2, Lift.chrStep, if_pos this]
  · have : ¬ Odd (j + 1 + 1) := Nat.not_odd_iff_even.2 ⟨a - σ - 1, by omega⟩
    rw [(h.sFB j σ hj).2.2.1, (h.sFB j σ hj).2.2.2, Lift.chrStep, if_neg this]

theorem isStepVector_trivial_of_chain (hv : R.chain_vY) (t : T) (j : ℕ) (hj : j + 1 < D.R.m) :
    IsStepVecOf R.ψ R.θ (Yc D j) (Yc D (j + 1)) (cart (R.MY j)) (cart (R.MY (j + 1))) (R.ΛY j)
      (R.ΛY (j + 1)) (R.βY j) (R.βY (j + 1)) (R.datYt t j R.triv) (R.chi (j + 1)) (R.Q t) (R.xiR t) (R.vac j) (R.vY t j) := hv t j hj

example (t : T) (j : ℕ) : CP R R.triv t j = R.CC t j := rfl

example (t : T) : datXP R R.triv t = R.datXt t := rfl

theorem GeoMeas.common (h : GeoMeas R g) (t t' : T) :
    ENNReal.ofReal (g.κ D.R.m * volLev R g t (D.R.m - 1)) • R.νX t = ENNReal.ofReal (g.κ D.R.m * volLev R g t' (D.R.m - 1)) • R.νX t' :=
  (h.volT t).symm.trans (h.volT t')

theorem not_geoMeas (t : T) (h0 : R.νX t = 0) : ¬ GeoMeas R g := fun h => by
  have := g.volT.haar
  exact NeZero.ne g.volT.μ (by rw [h.volT t, h0, smul_zero])

theorem colCh_nonempty (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) : ∃ k : ColCh u C, ∀ j, Nonempty (k.Ch j) :=
  ⟨{ kom := fun _ => 1, Ch := fun _ => Unit, dd := fun _ _ _ => 0, e := fun _ _ => Finsupp.single 1 1, eT := fun _ _ _ => Finsupp.single 1 1,
     Ram := fun _ => Set.univ, S := fun _ => id, rd := fun _ _ _ _ _ => 0, cV := fun _ => 1, cK := fun _ => 1, cP := 1 },
    fun _ => ⟨()⟩⟩

theorem geo_nonempty (bes : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → BesAt (Yc D j) (D.sp.X j) ρ)
    (jac : ∀ j ρ, j + 2 * ρ + 2 = D.R.m → JacAt (Yc D (j + 1)) (D.sp.X (j + 1)) ρ)
    (lnk : ∀ j σ h v, Link ((bes j (σ + 1) h).lev v) (bes (j + 1 + 1) σ (idx_step h)).L (bes (j + 1 + 1) σ (idx_step h)).ζ)
    (Lz : HSp D) (o : OrthDec (D.sp.X D.R.m) D.sp.X' Lz) : Nonempty (Geo D) := by
  obtain ⟨h1, -, h3, -⟩ := VolExist.measures_exist D
  exact ⟨{ vol := fun _ => (h1 _).some, volT := (h1 _).some, x := fun j => ⟨fun _ => 1, fun _ => 1, ⊥, (h1 _).some⟩, vac := fun _ _ => 0,
           bes := bes, jac := jac, lnk := fun j σ h => lnk j σ h _, vL := fun _ _ _ => (h3 _ _).some, Lz := Lz,
           oT := fun n h => h ▸ o, μf := fun _ => 0, μT := 0, ρJ := fun _ _ _ => 0, ρB := fun _ _ _ => 0, κ := fun _ => 1,
           b := fun _ => 1, bT := 1, LT := ⊥ }⟩

end Package

section Real

open GlobalTheory.MiS

variable {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex)

theorem reads_exists (u : D.what₂.Word) (j : SmT (pk W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (μ : D.what₂.Tup) (G : D.what₂.Amb μ) :
    ∃ f, Reads W u j x μ G f := by
  by_cases h : μ = D.what₂.mu0
  · subst h
    obtain ⟨f, hf⟩ := readsG_exists (W.R.T.cols.forms u).clsP.toG (W.R.T.cols.forms u).valP.eW j x ((D.eMt u).symm G)
    exact ⟨f, fun _ => hf, fun h => absurd rfl h⟩
  · obtain ⟨f, hf⟩ := readsG_exists (W.R.T.tw.pt.cls u μ h) (W.R.T.tw.pt.val u μ h).eW j x ((D.eMtTw u μ).symm G)
    exact ⟨f, fun h' => absurd h' h, fun _ => hf⟩

theorem tailOf_eq (u : D.what₂.Word) (j : SmT (pk W).MX →ₗ[ℂ] (FrP D → ℂ)) (x : GA D D.sp.X') (μ : D.what₂.Tup) (h : μ ≠ D.what₂.mu0)
    (ψ : (D.chTw u μ).cls D.R.m → (D.chTw u μ).Y D.R.m → ℂ) (G : D.what₂.Amb μ) (f : SmT (pk W).MX →ₗ[ℂ] (GA D D.sp.X' → ℂ))
    (hG : Reads W u j x μ G f)
    (hψ : ∀ c, (W.R.T.tw.pt.val u μ h).eW ((D.PTw u μ).lowerMap ((D.PTw u μ).evz ψ)) c ∈ LinearMap.range j) :
    tailOf W u j x μ ψ f = (D.PTw u μ).Ptil ψ ((D.eMtTw u μ).symm G) := by
  have hx : ∃ G, Reads W u j x μ G f := ⟨G, hG⟩
  rw [tailOf, dif_pos hx, dif_neg h]
  exact ReadsG.period_eq _ _ j x (hx.choose_spec.2 h) (hG.2 h) _ hψ

theorem not_topReadAt_zero (u : D.what₂.Word) (x : GA D D.sp.X') : ¬ TopReadAt W u 0 x := fun h => not_isJ_zero _ h.1

theorem not_unitRatio_base (u : D.what₂.Word) (p : ℕ) (hp : p.Prime) : ¬ UnitRatio (badPrime W u W.P.A3.A.μ0) (p : ℂ) 1 := by
  rintro ⟨-, k, hk, r, -, e, hS⟩
  have hr : r = ((p ^ k : ℕ) : ℚ) := by
    have : (r : ℂ) = (((p ^ k : ℕ) : ℚ) : ℂ) := by rw [← e]; simp
    exact_mod_cast this
  refine not_badPrime_base W u p (hS p hp ?_)
  have := Fact.mk hp
  rw [hr, padicValRat.of_nat, padicValNat.prime_pow]
  exact_mod_cast hk.ne'

end Real

end GlobalTheory.Fam.Check

end
end

