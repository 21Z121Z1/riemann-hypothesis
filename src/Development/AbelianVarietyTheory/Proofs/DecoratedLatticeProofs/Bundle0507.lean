import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.UnimodularTower
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumNonzeroCuspForm
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0263
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BilinearVacuumCentralCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0254
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0237
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0245
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0175
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1524
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0368
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0493
import Formalism.LocalRingCardinality.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1151
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignFirst
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0386
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.AlternatingFormStandardHermitian
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1939
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0358
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOverBoth
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0362
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumBoxTensorLineOverVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartLevelStandardBasePointEqMember
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0037
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationDeterminesCharUnramifiedSplitP

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RepresentsOfLink
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.IndefiniteRowSideFullHecke.UnimodularTower
open GlobalTheory.ChainOnto (Com PiLocalization₂)
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SeeSawCompare

variable {D : D7} {u : D.what₂.Word}

theorem defSp_is {V : HSp D} (hs : V.SigOK) (hp : V.IsPosDef) {S : D.what₂.Tau → SPar} (M : DSModel V S) (x : DefSp V)
    (h1 : x.s = cart M) (h2 : x.B = onb M) (h3 : IsSelfDualC V x.L) : x.Is := by
  have hs' : ∀ τ, Formalism.UG.HasSignature (gramAt D V τ) V.rank 0 := fun τ => by
    have := hs (tauE D τ)
    rw [hp (tauE D τ)] at this
    exact this
  have hJ : ∀ τ, Formalism.REAL.Jm (M.ε τ) = 1 := fun τ => by
    have := signs_pos_of_frame_gram_posdef (M.ε τ) (M.fr τ) _ (M.fr_gram τ) (hs' τ)
    unfold Formalism.REAL.Jm; simp [this]
  have hd := fun τ => (Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ)
  have hc : ∀ τ, x.s τ = 1 := fun τ => by rw [h1, cart, hJ, Matrix.mul_one, Matrix.nonsing_inv_mul _ (hd τ)]
  refine ⟨hs, Inh.coCpt_of_isDefinite hs fun τ => Or.inl (hp τ), fun τ => ?_, fun τ => Or.inl (hc τ), fun τ => ?_, h3⟩
  · rw [hc]
    exact ⟨by simp, by simp, by simpa using Formalism.IndefR.Fin.Lifts.posDef_of_sig _ (hs' τ)⟩
  · refine ⟨V.rank, fun _ => 1, fun a => Or.inl ⟨rfl, a.2⟩, ?_, by simp [hc]⟩
    rw [h2, onb, ← M.fr_gram τ, hJ, Matrix.mul_one, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul,
      Matrix.mul_nonsing_inv _ (hd τ), Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_nonsing_inv _ (hd τ)]
    simp

abbrev Live (D : D7) (u : D.what₂.Word) : Type := ∀ j, Submodule ℂ (Fn D u j)

variable (W : Live D u) {c : Com D}

structure PassageOn : Prop where
  ff_ram : ∀ i, i + 2 ≤ D.R.m → ∀ ε, ∀ φ ∈ Ram D u i ⊓ W i, ffStar D u i ε φ ∈ Ram D u i ⊓ W i
  ker_ram : ∀ i, i + 3 ≤ D.R.m → ∀ φ ∈ Ram D u i ⊓ W i, Formalism.MainNotions.product_first_zeroth_parts.KT D u i φ ∈ Ram D u (i + 1) ⊓ W (i + 1)
  comm : ∀ i, i + 3 ≤ D.R.m → ∃ a : ℂ, a ≠ 0 ∧ ∀ ε, ∀ φ ∈ Ram D u i ⊓ W i,
    ffStar D u (i + 1) ε (Formalism.MainNotions.product_first_zeroth_parts.KT D u i φ) = a • Formalism.MainNotions.product_first_zeroth_parts.KT D u i (ffStar D u i ε φ)
  bij : ∀ ε, Set.BijOn (ffStar D u 0 ε) (Ram D u 0) (Ram D u 0)

structure ColIsOn {X : HSp D} {j : ℕ} (A : ColOn c u X j) : Prop where
  rank : X.rank = D.R.N j
  sig : ∀ τ : D.host.E →+* ℂ, X.sig τ = (D.R.N j, 0)
  fin : A.K ≤ GfC X
  opn : ∃ U : Subgroup (GA D X), IsOpen (U : Set (GA D X)) ∧ U ⊓ GfC X ≤ A.K
  inj : ∀ φ : Fm D u j, (φ : Fn D u j) ∈ W j → A.a φ = 0 → φ = 0
  cont : ∀ φ v, IsContAut X (A.sc φ v)

structure StepIsOn {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)} (k : ColStep A A') (vol : Vol X) :
    Prop where
  weil : IsWeilDatumO c.ψ X X' (c.μ (j + 1)) (c.μ (j + 1)) k.om
  theta : ∀ P, IsThetaFunO c.ψ X X' (k.pt P)
  maps : ∀ φ ∈ Fm D u j ⊓ W j, Formalism.MainNotions.product_first_zeroth_parts.KT D u j φ ∈ Fm D u (j + 1) ⊓ W (j + 1)
  it_ne : k.it ≠ 0
  sum : ∀ (φ : Fm D u j) (φ' : Fm D u (j + 1)), (φ : Fn D u j) ∈ W j → (φ' : Fn D u (j + 1)) = Formalism.MainNotions.product_first_zeroth_parts.KT D u j φ →
    ∀ P v, k.lift vol (A.sc φ v) P = A'.sc φ' (k.it P v)

structure NodeIsOn {ρ j : ℕ} (N : Node c u ρ j) : Prop where
  row : N.row.Is c j
  col : ColIsOn W N.col
  line : Represents N.B.L (-((D.mem u).A.T : D.host.E))
  base : N.b ∈ GfC N.B.V
  unimod : Unimod (besGrp N.B.d N.B.o) N.B.μR

section Dbl

variable {σ j : ℕ} {N : Node c u (σ + 1) j} {N' : Node c u σ (j + 1 + 1)} (d : Dbl N N')

def SuppA (x : GA D N.B.V) : Prop :=
  ∀ P₁ P₂ (φ : Fm D u j), (φ : Fn D u j) ∈ Ram D u j ⊓ W j → ∀ v,
    ∀ h₁ ∉ dcos (jacGrp d.J.d) d.b d.row.lev, ∀ h₂, d.hand P₁ P₂ (N.col.sc φ v) (x * N.b) h₁ h₂ = 0

def SuppB (x : GA D N.B.V) : Prop :=
  ∀ P₁ P₂ (φ : Fm D u j), (φ : Fn D u j) ∈ Ram D u j ⊓ W j → ∀ v, ∀ x₁ ∈ GinfC d.J.W,
    ∀ h₂ ∉ dcos (besGrp N'.B.d N'.B.o) N'.b N'.row.lev, d.hand P₁ P₂ (N.col.sc φ v) (x * N.b) (x₁ * d.b) h₂ = 0

def ValAt (x : GA D N.B.V) : Prop :=
  ∀ P₁ P₂, ∀ x₁ ∈ GinfC d.J.W, ∀ x₂ ∈ GinfC N'.B.V,
    ∃ (n : ℕ) (Q₁ : Fin n → PolF D d.J.W₀.rank N.B.A.rank) (Q₂ : Fin n → PolF D N'.B.A.rank d.J.W₀.rank),
      ∀ φ φ' : Fm D u j, (φ : Fn D u j) ∈ Ram D u j ⊓ W j → (φ' : Fn D u j) = ffStar D u j d.ε φ → ∀ v,
        d.hand P₁ P₂ (N.col.sc φ v) (x * N.b) (x₁ * d.b) (x₂ * N'.b) =
          ∑ i, d.k₂.lift d.J.v0 (d.k₁.lift N.B.vA (N.col.sc φ' v) (Q₁ i)) (Q₂ i)

structure DblIsOn : Prop where
  row : d.row.Is c (j + 1)
  col : ColIsOn W d.col
  base : d.b ∈ GfC d.J.W
  unimod : Unimod (jacGrp d.J.d) d.J.μR
  step₁ : RowStep (j + 1) d.p₁ d.s₁
  step₂ : RowStep (j + 1 + 1) d.p₂ d.s₂
  ker₁ : StepIsOn W d.k₁ N.B.vA
  ker₂ : StepIsOn W d.k₂ d.J.v0
  supp₁ : ∀ x ∈ GinfC N.B.V, SuppA W d x
  supp₂ : ∀ x ∈ GinfC N.B.V, SuppB W d x
  val : ∀ x ∈ GinfC N.B.V, ValAt W d x

end Dbl

section Fin2

variable {j : ℕ} {N : Node c u 0 j} {T : HSp D} {top : RowOn T} (e : Fin2 N top)

def ValTop : Prop :=
  ∀ P₁ P₂, ∀ x ∈ GinfC N.B.V,
    ∃ (n : ℕ) (Q₁ : Fin n → PolF D e.t.J.W.rank N.B.A.rank) (Q₂ : Fin n → PolF D e.X.rank e.t.J.W.rank),
      ∀ φ φ' : Fm D u j, (φ : Fn D u j) ∈ Ram D u j ⊓ W j → (φ' : Fn D u j) = ffStar D u j e.ε φ → ∀ v h',
        e.inner P₁ P₂ (N.col.sc φ v) (x * N.b) h' =
          ∑ i, e.k₂.lift e.t.s.vW (e.k₁.lift N.B.vA (N.col.sc φ' v) (Q₁ i)) (Q₂ i) (e.o.emb (h', 1))

def PeriodTop : Prop :=
  ∀ (φ : Fm D u (j + 1 + 1)) (φ' : Fn D u D.R.m), (φ : Fn D u (j + 1 + 1)) ∈ W (j + 1 + 1) → HEq φ' (φ : Fn D u (j + 1 + 1)) →
    ∀ (F : (D.mem u).P.Mt) v w,
      ∫ h' in top.fd, PiLocalization₂.val (e.ι F) w h' * e.col₂.sc φ v (e.o.emb (h', 1)) ∂top.ν = e.br v w * (D.mem u).P.Ptil φ' F

structure FinIsOn : Prop where
  idx : j + 1 + 1 = D.R.m
  row : e.row.Is c (j + 1)
  top_is : top.st.Is c (j + 1 + 1)
  top_cont : ∀ (y : top.st.CC c) w, IsContAut T (PiLocalization₂.val y w)
  col₁ : ColIsOn W e.col₁
  col₂ : ColIsOn W e.col₂
  line : e.L.rank = 1 ∧ Represents e.L ((D.mem u).A.T : D.host.E)
  step₁ : RowStep (j + 1) e.p₁ e.t.s
  is₂ : e.p₂.Is (j + 1 + 1)
  onto₂ : e.row.st.KF ≤ Submodule.span ℂ {x | ∃ P, ∃ w ∈ top.st.KF, x = e.p₂.It P w}
  χS : e.t.χS = c.chS (j + 1 + 1)
  χT : e.t.χT = c.chT (j + 1 + 1)
  om : e.t.om = e.p₂.ω
  μ : e.t.vT.μ = top.ν
  fd : e.t.vT.𝓕 = top.fd
  ker₁ : StepIsOn W e.k₁ N.B.vA
  ker₂ : StepIsOn W e.k₂ e.t.s.vW
  val : ValTop W e
  br_ne : e.br ≠ 0
  period : PeriodTop W e

end Fin2

noncomputable def TowerIsOn {T : HSp D} {top : RowOn T} : {ρ j : ℕ} → {N : Node c u ρ j} → Tower c u top ρ j N → Prop
  | _, _, N, .last e => NodeIsOn W N ∧ FinIsOn W e
  | _, _, N, .step _ d t => NodeIsOn W N ∧ DblIsOn W d ∧ TowerIsOn t

def LawsOn : Prop :=
  PassageOn W ∧ ∃ c : Com D, c.Is ∧ IsSharp c ∧ ∃ (T : HSp D) (top : RowOn T) (N : Node c u D.R.rS 0)
    (t : Tower c u top D.R.rS 0 N), TowerIsOn W t ∧ LinkP N

structure Kept : Prop where
  ker : ∀ j, j < D.R.m → ∀ φ ∈ Fm D u j ⊓ W j, Formalism.MainNotions.product_first_zeroth_parts.KT D u j φ ∈ W (j + 1)
  ff : ∀ j, j + 2 ≤ D.R.m → ∀ ε, ∀ φ ∈ Ram D u j ⊓ W j, ffStar D u j ε φ ∈ W j

variable {W}

theorem ColIsOn.is {X : HSp D} {j : ℕ} {A : ColOn c u X j} (h : ColIsOn ⊤ A) : A.Is :=
  ⟨h.rank, h.sig, h.fin, h.opn, (injective_iff_map_eq_zero _).2 fun φ => h.inj φ trivial, h.cont⟩

section Step

variable {X X' : HSp D} {j : ℕ} {A : ColOn c u X j} {A' : ColOn c u X' (j + 1)} {k : ColStep A A'} {vol : Vol X}

theorem StepIsOn.is (h : StepIsOn ⊤ k vol) : k.Is vol :=
  ⟨h.weil, h.theta, fun φ hφ => (h.maps φ ⟨hφ, trivial⟩).1, h.it_ne, fun φ φ' => h.sum φ φ' trivial⟩

end Step

theorem NodeIsOn.is {ρ j : ℕ} {N : Node c u ρ j} (h : NodeIsOn ⊤ N) : N.Is := ⟨h.row, h.col.is, h.line, h.base, h.unimod⟩

end GlobalTheory.SeeSawCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualCOf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HalfBInt

variable {D : D7}

theorem selfDualC_of (V : HSp D) (hV : V.gram = 1) (N : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (h : Formalism.L2.Col.IsSdLat N) : IsSelfDualC V N := by
  refine ⟨h.1, fun y => ?_⟩
  have h2 : Formalism.HermitianLatticesTheory.dual (Formalism.L2.Col.hStd D.host.E V.rank) N = N := h.2
  conv_lhs => rw [← h2]
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply, Submodule.mem_one]
  refine forall_congr' fun x => imp_congr_right fun _ => ?_
  have e : Formalism.L2.Col.hStd D.host.E V.rank x y = ∑ i, ∑ j, star (x i) * V.gram i j * y j := by
    rw [hV]
    simp [Formalism.L2.Col.hStd, Matrix.one_apply]
  rw [e]

theorem noConj {e : AE D} {SS : Finset (Formalism.L2.DIV.Pl D.host.E)} (hE : IsIdemSum e SS) :
    ∀ P ∈ SS, Formalism.L2.Col.conjPrime₂ P ∉ SS := by
  obtain ⟨⟨es, hes, he⟩, hc⟩ := hE
  intro P hP hP'
  have hv : Formalism.IndefR.Fin.belowPl P = Formalism.IndefR.Fin.belowPl (Formalism.L2.Col.conjPrime₂ P) :=
    HeightOneSpectrum.ext (congrArg HeightOneSpectrum.asIdeal (GlobalTheory.GridPlaces.under_conjP P)).symm
  have h := Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_below_inj hes he hc hP hP' hv
  exact GlobalTheory.ModulusNorm.conjPl_ne_of_isIdemAt (hes P hP) ((GlobalTheory.PlaceDict.conjP_eq_conjPl D P).symm.trans h.symm)

end GlobalTheory.HalfBInt

open GlobalTheory.HalfBInt in

theorem GlobalTheory.HalfBInt.trace_int : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (a b : ℕ) (hS : S.rank = a) (hT : T.rank = b) (δ : ℂ) (sc : ℝ), StdPair θ S T δ sc ψ → ∀ (e : AE D) (SS : Finset (Formalism.L2.DIV.Pl D.host.E)), IsIdemSum e SS → ∀ (N : Submodule (𝓞 D.host.E) (Fin a → D.host.E)) (N' : Submodule (𝓞 D.host.E) (Fin b → D.host.E)) (c : ℕ), 0 < c → Odd c → (∀ Q ∈ SS, ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → (ΛS : Set (Fin S.rank → D.host.E)) = latFr S hS N → (ΛT : Set (Fin T.rank → D.host.E)) = latFr T hT N' → ∀ y ∈ halfBO SS (perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) N N') c, ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ D.host.E (D.host.xi0 * ((1 + D.host.sqrtMinusD) / 2) ^ 2 * GlobalTheory.LatVac.hRat S T ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm)) ((LinearMap.toMatrix' (y)).reindex (finCongr hT.symm) (finCongr hS.symm))) := by
  intro D ψ θ S T a b hS hT δ sc hP e SS hE N N' c hc _ _ ΛS ΛT dS dT eS eT y hy
  subst hS hT
  obtain rfl : ΛS = N := SetLike.coe_injective eS
  obtain rfl : ΛT = N' := SetLike.coe_injective eT
  have hnc := noConj hE
  have hyT : y ∈ perO (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) ΛS (twist₂ ΛT c (expS SS)) := by
    rw [← Formalism.L2.Ker.twist_homomorphism _ _ _ _ ΛS ΛT c _ dS.1.fg hc]
    exact hy
  have hsdT := (GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS _ _ ΛT c SS hnc (GlobalTheory.StdMove.isSdLat_of T hP.gT ΛT dT) hc).1
  have dT' : IsSelfDualC T (twist₂ ΛT c (expS SS)) := selfDualC_of T hP.gT _ hsdT
  have hrat := GlobalTheory.AdForm.RatLatPer.finRat_mem_latO_of_perO D ψ θ S T _ _ rfl rfl δ sc hP ΛS (twist₂ ΛT c (expS SS)) ΛS (twist₂ ΛT c (expS SS)) dS dT' rfl rfl y hyT
  have hneg : GlobalTheory.VacUnique.finRat S T (-((LinearMap.toMatrix' y).reindex (finCongr (rfl : T.rank = T.rank).symm) (finCongr (rfl : S.rank = S.rank).symm))) ∈
      latO S T ((ΛS : Set (Fin S.rank → D.host.E))) ((twist₂ ΛT c (expS SS) : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
    rw [map_neg]
    exact neg_mem hrat
  have h0 : IsLatVac (heisO ψ S T) (latO S T ((ΛS : Set (Fin S.rank → D.host.E))) ((twist₂ ΛT c (expS SS) : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) : Set (Fin T.rank → D.host.E)) (fun _ => True)) (0 : WO S T → ℂ) :=
    ⟨fun _ _ => by funext w; simp [heisO], fun _ _ _ _ _ => by funext w; simp [heisO]⟩
  obtain ⟨k, hk, -⟩ := GlobalTheory.LatVacSign.heisO_finRat_sign ψ S T ΛS (twist₂ ΛT c (expS SS)) hP.std dS dT' 0 h0 _ hneg
  exact ⟨k, hk⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualCoreComponentGluedAlongPair
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatMatch

open GlobalTheory.LatPair in

theorem exists_pair_of_line {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : Type}
    (Λ : Submodule 𝒪[k] (n ⊕ Fin 1 → k)) (hΛ : Λ.IsLattice k) (q : Unif k) (m : k)
    (h1 : ∀ t : k, (Sum.elim 0 (fun _ => t) : n ⊕ Fin 1 → k) ∈ Λ ↔ m * t ∈ 𝒪[k])
    (h2 : ∀ s : k, (∀ x ∈ Λ, s * ((q.1 : k) * (m * x (Sum.inr 0))) ∈ 𝒪[k]) ↔ s ∈ 𝒪[k]) :
    ∃ P : Pair k n, ∀ x : n ⊕ Fin 1 → k, x ∈ Λ ↔
      Sum.elim (fun a => x (Sum.inl a)) (fun j => m * x (Sum.inr j)) ∈ gluedS q 1 P.ker P.vec := by
  have hq := GlobalTheory.LevelUnfold.mul_inv_q q
  have hint : ∀ x ∈ Λ, (q.1 : k) * (m * x (Sum.inr 0)) ∈ 𝒪[k] := fun x hx => by
    simpa using (h2 1).2 (one_mem _) x hx
  have hqi : q.inv ∉ 𝒪[k] := fun h => q.2.not_isUnit (IsUnit.of_mul_eq_one ⟨_, h⟩ (Subtype.ext hq))
  obtain ⟨e, he, he1⟩ : ∃ e ∈ Λ, (q.1 : k) * (m * e (Sum.inr 0)) = 1 := by
    have h := mt (h2 q.inv).1 hqi
    push Not at h
    obtain ⟨x, hx, hx'⟩ := h
    have hu : IsUnit (⟨_, hint x hx⟩ : 𝒪[k]) := by
      rw [← IsLocalRing.notMem_maximalIdeal, q.mem_max_iff]
      rintro ⟨c, hc⟩
      have hc' : (q.1 : k) * (m * x (Sum.inr 0)) = (q.1 : k) * c := congrArg Subtype.val hc
      apply hx'
      rw [hc', ← mul_assoc, mul_comm q.inv, hq, one_mul]
      exact c.2
    obtain ⟨c, hc⟩ := hu.exists_left_inv
    have hc' : (c : k) * ((q.1 : k) * (m * x (Sum.inr 0))) = 1 := congrArg Subtype.val hc
    refine ⟨c • x, Λ.smul_mem c hx, ?_⟩
    rw [← hc']
    change _ * (m * ((c : k) * _)) = _
    ring
  have hsplit : ∀ x : n ⊕ Fin 1 → k, x = inX k n 1 (x ∘ Sum.inl) + (Sum.elim 0 (fun _ => x (Sum.inr 0)) : n ⊕ Fin 1 → k) := fun x => by
    ext (j | j)
    · simp [inX]
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      simp [inX]
  let L : Submodule 𝒪[k] (n → k) := Λ.comap (inX k n 1)
  have hL : ∀ x : n ⊕ Fin 1 → k, m * x (Sum.inr 0) ∈ 𝒪[k] → (x ∈ Λ ↔ x ∘ Sum.inl ∈ L) := fun x hx => by
    conv_lhs => rw [hsplit x]
    exact Λ.add_mem_iff_left ((h1 _).2 hx)
  have key : ∀ (x : n ⊕ Fin 1 → k) (s : 𝒪[k]), (q.1 : k) * (m * x (Sum.inr 0)) = s →
      (x ∈ Λ ↔ x ∘ Sum.inl - s • (e ∘ Sum.inl) ∈ L) := fun x s hs => by
    rw [← Λ.sub_mem_iff_left (Λ.smul_mem s he)]
    refine hL (x - s • e) ?_
    have h0 : (q.1 : k) * (m * (x - s • e) (Sum.inr 0)) = 0 := by
      change (q.1 : k) * (m * (x _ - (s : k) * e _)) = 0
      linear_combination hs - (s : k) * he1
    rw [(mul_eq_zero.1 h0).resolve_left q.ne_zero]
    exact zero_mem _
  have hqe : q.1 • (e ∘ Sum.inl) ∈ L := by
    refine (hL (q.1 • e) ?_).1 (Λ.smul_mem _ he)
    change m * ((q.1 : k) * e _) ∈ _
    rw [mul_left_comm, he1]
    exact one_mem _
  have hlat : L.IsLattice k := by
    refine ⟨?_, ?_⟩
    · refine Submodule.fg_of_fg_map_injective (inX k n 1) (fun x y h => ?_) (hΛ.fg.of_le (Submodule.map_comap_le _ _))
      funext j
      exact congrFun h (Sum.inl j)
    · rw [eq_top_iff]
      intro y _
      have hle : Submodule.span k (Λ : Set (n ⊕ Fin 1 → k)) ≤
          (Submodule.span k (L : Set (n → k))).comap (LinearMap.funLeft k k Sum.inl) := by
        refine Submodule.span_le.2 fun x hx => ?_
        have h3 := (key x ⟨_, hint x hx⟩ rfl).1 hx
        have h4 : e ∘ Sum.inl ∈ Submodule.span k (L : Set (n → k)) := by
          rw [← q.inv_smul_smul (e ∘ Sum.inl)]
          exact Submodule.smul_mem _ _ (Submodule.subset_span hqe)
        have h5 := add_mem (Submodule.subset_span (R := k) (s := (L : Set (n → k))) h3)
          (Submodule.smul_mem _ ((q.1 : k) * (m * x (Sum.inr 0))) h4)
        have h6 : ∀ a b : n → k, a - (⟨_, hint x hx⟩ : 𝒪[k]) • b + ((q.1 : k) * (m * x (Sum.inr 0))) • b = a :=
          fun a b => sub_add_cancel a _
        rw [h6] at h5
        exact h5
      exact hle (x := Sum.elim y 0) (by rw [hΛ.span_eq_top]; trivial)
  have hglue : IsGlue L (e ∘ Sum.inl) := by
    refine (isGlue_iff q).2 ⟨hlat, fun h => hqi ?_, hqe⟩
    have h3 : (Sum.elim 0 (fun _ => e (Sum.inr 0)) : n ⊕ Fin 1 → k) ∈ Λ := by
      rw [← Λ.add_mem_iff_right (show inX k n 1 (e ∘ Sum.inl) ∈ Λ from h), ← hsplit]
      exact he
    have h4 : q.inv = m * e (Sum.inr 0) := by
      rw [← mul_one q.inv, ← he1, ← mul_assoc, mul_comm q.inv, hq, one_mul]
    rw [h4]
    exact (h1 _).1 h3
  obtain ⟨P, hk, hv⟩ := hglue.exists_pair
  have hd : e ∘ Sum.inl - P.vec ∈ L := hk ▸ Pair.sub_vec_mem hv
  have hvec : ∀ (y : n → k) (s : 𝒪[k]), y - s • (e ∘ Sum.inl) ∈ L ↔ y - s • P.vec ∈ L := fun y s => by
    rw [← L.add_mem_iff_left (L.smul_mem s hd), smul_sub, sub_add_sub_cancel]
  refine ⟨P, fun x => ?_⟩
  rw [GlobalTheory.LevelUnfold.mem_gluedS, hk]
  constructor
  · intro hx
    refine ⟨⟨_, hint x hx⟩, (hvec _ _).1 ((key x _ rfl).1 hx), fun i => ⟨fun _ => ?_, fun hi => absurd hi (by omega)⟩⟩
    obtain rfl : i = 0 := Subsingleton.elim _ _
    change m * x _ = q.inv * ((q.1 : k) * _)
    rw [← mul_assoc, mul_comm q.inv, hq, one_mul]
  · rintro ⟨s, hs, hs'⟩
    have h3 : m * x (Sum.inr 0) = q.inv * s := (hs' 0).1 rfl
    refine (key x s ?_).2 ((hvec _ _).2 hs)
    rw [h3, ← mul_assoc, hq, one_mul]

section Place

open GlobalTheory.FinPl.FrameLat GlobalTheory.SeeSaw.CoreGlue

variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k)

theorem pr_cA_sec (c : k) : p.pr (cA D (p.sec c)) = 0 := by
  have he : p.pr p.e = 1 := by rw [← sec_one, p.pr_sec]
  have h0 : p.e * cA D (p.sec c) = 0 := by
    rw [← cA_cA p.e, ← map_mul, ← e_mul_sec p c, ← mul_assoc, cAe_mul_e, zero_mul, map_zero]
  have h1 := congrArg p.pr h0
  rwa [RingHom.map_mul, he, one_mul, RingHom.map_zero] at h1

theorem mul_sec_mem_intAt_iff (a : AE D) (t : k) : a * p.sec t ∈ intAt D (· = p.v) ↔ p.pr a * t ∈ 𝒪[k] := by
  rw [mul_comm, sec_mul_right, mem_intAt_iff p (sec_mem_idAt p _), pr_cA_sec, p.pr_sec, and_iff_left (zero_mem _), mul_comm]

theorem cA_sec_mul (a : AE D) (t : k) : cA D (p.sec t) * a = cA D (p.sec (t * p.pr (cA D a))) := by
  rw [← sec_mul_right, RingHom.map_mul, cA_cA]

theorem mul_cA_sec_mem_intAt_iff (a : AE D) (t : k) :
    a * cA D (p.sec t) ∈ intAt D (· = p.v) ↔ p.pr (cA D a) * t ∈ 𝒪[k] := by
  rw [mul_comm, cA_sec_mul, mem_intAt_iff p (csec_mem_idAt _), pr_cA_sec, cA_cA, p.pr_sec, and_iff_right (zero_mem _), mul_comm]

theorem exists_gluedW : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (S A L : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E) (n : Type) [Fintype n] [DecidableEq n] (β : GlobalTheory.FinPl.Frame p A n) (β₀ : GlobalTheory.FinPl.Frame p S (n ⊕ Fin 1)) (M : Lat S) (μ : D.host.E) (T : ℕ) (q : GlobalTheory.LatPair.Unif k), IsSumFrame o ζ β β₀ → IsSelfDualC S M → μ ≠ 0 → LineAt (vecB o ζ) μ M p.v → star ζ ⬝ᵥ L.gram *ᵥ ζ = -(μ * star μ * (T : D.host.E)) → valuation k (p.pr (incA D (T : D.host.E))) = valuation k ((q.1 : 𝒪[k]) : k) → ∃ P : GlobalTheory.LatPair.Pair k n, GluedW β₀ M q (p.pr (incA D μ)) P := by
  intro D k _ _ _ _ p S A L o ζ n _ _ β β₀ M μ T q hs hM hμ hline hnorm hT
  have hb : p.pr (incA D (star μ)) ≠ 0 := (map_ne_zero (p.pr.comp (incA D))).2 (star_ne_zero.2 hμ)
  refine exists_pair_of_line (latW β₀ hM) ?_ q (p.pr (incA D μ)) (fun t => ?_) (fun s => ?_)
  · obtain ⟨Λ, h1, h2, -⟩ := exists_lat D k p S _ β₀ M hM
    rwa [show latW β₀ hM = Λ from Submodule.ext fun x => (h2 x).symm]
  · refine Iff.trans ?_ ((hline _ (sec_mem_idAt p t)).trans (mul_sec_mem_intAt_iff p _ t))
    have h2 : (fun i => p.sec ((β₀.b *ᵥ (Sum.elim 0 (fun _ => t) : n ⊕ Fin 1 → k)) i)) = p.sec t • ratV (vecB o ζ) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, sec_mul_right, hs]
      congr 1
      simp [mulVec, dotProduct, Fintype.sum_sum_type, mul_comm]
    rw [← h2]
    rfl
  · obtain ⟨s', rfl⟩ : ∃ s', s = p.pr (incA D (star μ)) * s' := ⟨_, (mul_inv_cancel_left₀ hb s).symm⟩
    refine Iff.trans ?_ ((hline _ (csec_mem_idAt (p := p) s')).trans (mul_cA_sec_mem_intAt_iff p _ s'))
    have h2 : cA D (p.sec s') • ratV (vecB o ζ) =
        fun i => cA D (p.sec (s' * p.pr (incA D (star (vecB o ζ i))))) := funext fun i => cA_sec_mul p _ s'
    rw [h2]
    refine Iff.trans ?_ (csec_mem_iff hM _).symm
    have h3 : ∀ x : n ⊕ Fin 1 → k, s' * (p.pr (incA D (star ζ ⬝ᵥ L.gram *ᵥ ζ)) * x (Sum.inr 0)) ∈ 𝒪[k] ↔
        p.pr (incA D (star μ)) * s' * ((q.1 : k) * (p.pr (incA D μ) * x (Sum.inr 0))) ∈ 𝒪[k] := fun x => by
      rw [Valuation.mem_integer_iff, Valuation.mem_integer_iff, hnorm, RingHom.map_neg, RingHom.map_neg, RingHom.map_mul,
        RingHom.map_mul, RingHom.map_mul, RingHom.map_mul]
      generalize p.pr (incA D (T : D.host.E)) = a at hT
      generalize p.pr (incA D μ) = b
      generalize p.pr (incA D (star μ)) = c
      have h4 : valuation k (s' * (-(b * c * a) * x (Sum.inr 0))) =
          valuation k (c * s' * ((q.1 : k) * (b * x (Sum.inr 0)))) := by
        simp only [Valuation.map_mul, Valuation.map_neg, hT]
        ac_rfl
      rw [h4]
    constructor
    · intro h x hx
      have hx' : x = β₀.b *ᵥ (β₀.b' *ᵥ x) := by rw [mulVec_mulVec, β₀.bb', one_mulVec]
      rw [hx'] at hx ⊢
      rw [pair_sumFrame o ζ hs, h3]
      exact h _ hx
    · intro h x hx
      rw [← h3, ← pair_sumFrame o ζ hs]
      exact h _ hx

end Place

end GlobalTheory.Core.Mi.LatMatch

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceDatumBoxTensorLineOverVacuumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.AppendedVectorData (lastKer lastPair cosetInd withRow)
open GlobalTheory.FinPl.ExtZero (colFun rowFun)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitPlace_datum_boxTensor_line_over_vacuum : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n'' : Type) [Fintype n] [DecidableEq n] [Fintype n''] [DecidableEq n''] (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → p.UnitAA → ∀ (S X T L'' : HSp D) (o'' : OrthDec X T L'') (ζ₀ : Fin L''.rank → D.host.E), IsLineVec L'' ζ₀ → ∀ (β : Frame p S n) (γ : Frame p T n'') (γ₀ : Frame p X (n'' ⊕ Fin 1)), IsSumFrame o'' ζ₀ γ γ₀ → ∀ (LS : Lat S) (LT : Lat T) (LX : Lat X), IsSelfDualC S LS → IsSelfDualC T LT → IsSelfDualC X LX → ∀ (f₂ F₂ : WO S T → ℂ) (Ψ₂ : Matrix n'' n k → ℂ), Over ψ β γ LS LT f₂ Ψ₂ F₂ → ∀ (b : (n → k) → ℂ) (g₃ : WO S L'' → ℂ) (T₃ : (WO S L'' → ℂ) →ₗ[ℂ] (WO S L'' → ℂ)), IsThetaFunO ψ S L'' g₃ → IsPlaceModel ψ (symplO S L'') (heisO ψ S L'') p.e (latO S L'' (LS : Set _) ((Submodule.span (NumberField.RingOfIntegers D.host.E) {ζ₀} : Lat L'') : Set _) (· = p.v)) 1 g₃ T₃ → GlobalTheory.FinPl.tensRow Ψ₂ b ∈ SB (Matrix (n'' ⊕ Fin 1) n k) → ∃ g, Over ψ β γ₀ LS LX g (GlobalTheory.FinPl.tensRow Ψ₂ b) (o''.boxT S F₂ (T₃ (rowFun β ζ₀ b))) := by
  first | exact @GlobalTheory.FinPl.BoxDatum.over_boxT | exact GlobalTheory.FinPl.BoxDatum.over_boxT | (intros; apply GlobalTheory.FinPl.BoxDatum.over_boxT <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroChartLevelStandardBasePointEqMemberStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepZeroChartLevel_standardBasePoint_eq_member : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (C : Formalism.L2.Forms.ColsTiedSym (I.rec7 l Z)), I.StdC l Z C → ∀ (u : B.Word) (a : I.ι) (Ch : ℕ → Type) (A : GlobalTheory.AdForm.TwDat I l Z u a Ch), A.Is → ∀ (β : Ch 0), A.kb 0 β = TC.kStd X u (B.R.N 0) → ∀ x, x ∈ (A.K 0 (Nat.zero_le _) β).lev.U ↔ x ∈ (C.forms u).to0.cls0.lev.U := by
  first | exact @GlobalTheory.ZeroLevel.lev_zero_std | exact GlobalTheory.ZeroLevel.lev_zero_std | (intros; apply GlobalTheory.ZeroLevel.lev_zero_std <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationDeterminesCharUnramifiedSplitPStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_determines_charUnramified_splitPlace : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT χS' χT' : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S T χS' χT' om → (0 < S.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χT' p.v) ∧ (0 < T.rank → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS p.v → GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D χS' p.v) := by
  first | exact @GlobalTheory.CharsFromWeil.charUnram_of_weil | exact GlobalTheory.CharsFromWeil.charUnram_of_weil | (intros; apply GlobalTheory.CharsFromWeil.charUnram_of_weil <;> assumption)
end

