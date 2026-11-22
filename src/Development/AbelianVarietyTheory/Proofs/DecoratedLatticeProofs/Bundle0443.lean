import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0393
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0431
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0443
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0294
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
import Formalism.LocalToGlobal.Columns.AdelicLemmas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0433
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0432
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0151
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0379
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0338
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LastSeeSawThetaIdentity
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.SeeLastPf

theorem ofAdj_zero (D : D7) (L S : HSp D) : GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S 0 = 0 := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj]

theorem seeLast : ∀ D : D7, SeeLast D := by
  intro D ψ V₀ A L S X T L'' o o'' τ hL hL'' hτ χA χz χS χS' χT om₁ oma omz omX omT omz'' h₁ ha hz hX hT hz'' Ξ Φ₂ hΞ hΦ₂
  have hψ : IsStdChar D ψ (-1) := h₁.std
  have hsrc := GlobalTheory.T.thetaTensorRule_orthogonalSum_source D ψ hψ V₀ A L o S
  have htgt := GlobalTheory.T.thetaTensorRule_targetOrthogonalSum D ψ hψ X T L'' o'' S
  have hτ' : τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L''.gram := by
    rw [hτ]; simp
  have hrk : L.rank = L''.rank := hL.trans hL''.symm
  have hline := fun u => GlobalTheory.T.weilRep_sourceLine_eq_opposite_targetLine D ψ L L'' S τ hrk hτ' χz χS χS' omz omz'' hz hz''
    (fun v => Ξ ((o.resS S).symm (u, v))) ((hsrc.slice_theta Ξ hΞ).2 u)
  refine ⟨fun u => (hline u).1, ?_⟩
  intro h₀ h h'
  have e1 : ∀ u, omX (h, o''.emb (h', 1)) (o''.boxT S Φ₂ fun w => Ξ ((o.resS S).symm
      (u, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L''.rank) ⬝ w)))) 0 =
      omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0 := by
    intro u
    rw [htgt.om_box χS' χT χz⁻¹ omX omT omz'' hX hT hz'' h h' 1 Φ₂ _ hΦ₂ (hline u).1, htgt.box_zero,
      (hline u).2 h]
    beta_reduce
    congr 1
    exact congrArg (omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))))
      ((congrArg (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S) (Matrix.mul_zero _)).trans (ofAdj_zero D L S))
  have e2 := (hsrc.om_slice χA χz χS om₁ oma omz h₁ ha hz h₀ 1 h Ξ hΞ 0).2 0
  have e0 : (o.resS S).symm (0, 0) = 0 := by
    rw [← Prod.zero_eq_mk, map_zero]
  rw [e0] at e2
  simp only [e1]
  rw [e2]
  have : (fun u => omT (h, h') Φ₂ 0 * omz (1, h) (fun v => Ξ ((o.resS S).symm (u, v))) 0) =
      omT (h, h') Φ₂ 0 • (fun u' => omz (1, h) (fun v' => Ξ ((o.resS S).symm (u', v'))) 0) := by
    funext u; simp
  rw [this, map_smul]
  simp

end GlobalTheory.SeeLastPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatEqOfCarries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.BaseCosetPt

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}

theorem lat_eq_of_carries {g : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {N₁ N₂ : Submodule (𝓞 E) (Fin n → E)}
    (h₁ : Submodule.IsLattice E N₁) (h₂ : Submodule.IsLattice E N₂)
    (c₁ : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N₁) (c₂ : Formalism.L2.Herm.Carries g (Formalism.L2.Col.stdLat E n) N₂) :
    N₁ = N₂ := by
  have key : ∀ N : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E N → ∀ x : Fin n → E,
      (x ∈ N ↔ (fun j => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x j)) ∈ Formalism.L2.Herm.hatL (F := F) N) := by
    intro N hN x
    have hone := Formalism.UG.P.global_lattice_one_holds F E (Fin n) N (Module.Finite.iff_fg.mpr hN.fg) hN.span_eq_top
    conv_lhs => rw [← hone]
    show (((1 : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))⁻¹ : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) : Matrix (Fin n) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) *ᵥ (fun i => Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F) (x i)) ∈ Formalism.L2.Herm.hatL (F := F) N ↔ _
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
  ext x
  rw [key N₁ h₁, key N₂ h₂, c₁, c₂]

end Gen

section Pt

open Formalism.L2.Col Formalism.MainNotions Formalism.L2.DIV

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

theorem frsF_symm_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) {w : Sp X.E (R.N j)}
    (hw : w ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N) : (frsF sel mu p P).symm w ∈ stdAt X.E (R.N j) P.1 := by
  have hfr := isFr_ptFr p P.1
  rw [← frsF_eq_ptFr sel mu p P] at hfr
  exact (hfr _).1 (by simpa using hw)

theorem frsF_mem {u : Pr.Word} {j : ℕ} (p : ChPt (R := R) sel mu u j) (P : rowSG Pr sel mu) {x : Sp X.E (R.N j)}
    (hx : x ∈ stdAt X.E (R.N j) P.1) : frsF sel mu p P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N := by
  have hfr := isFr_ptFr p P.1
  rw [← frsF_eq_ptFr sel mu p P] at hfr
  exact (hfr _).2 hx

theorem cosetIn_eq_of {u : Pr.Word} {j : ℕ} (r : PtAt R sel mu cst u j) (P : rowSG Pr sel mu) (hP : P.1 ∈ Pr.vGs)
    (y : Sp X.E (R.N j)) (e : rowSG Pr sel mu → ℤ) (he : e P = 0)
    (hY : r.1.2 = {z | z - y ∈ locLat (rowSG Pr sel mu) r.1.1.deco.1.N e}) :
    cosetIn r P = {z | z - (frsF sel mu r.1.1 P).symm y ∈ stdAt X.E (R.N j) P.1} := by
  classical
  ext z
  simp only [cosetIn, if_pos hP, pow_zero, inv_one, one_smul, Set.mem_setOf_eq, hY]
  constructor
  · rintro ⟨y', hy', hz⟩
    have h1 : y' - y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal r.1.1.deco.1.N := by
      have := (Submodule.mem_iInf _).1 hy' P
      simpa [Submodule.mem_comap, he] using this
    have := add_mem hz (frsF_symm_mem r.1.1 P h1)
    rwa [map_sub, sub_add_sub_cancel] at this
  · intro hz
    exact ⟨y, by simp, hz⟩

end Pt

end GlobalTheory.BaseCosetPt

namespace GlobalTheory.BaseCosetPt

open Formalism.L2.Col Formalism.MainNotions Formalism.L2.DIV

end GlobalTheory.BaseCosetPt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeEqBaseOffTwist
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Fam

theorem lattice_eq_base_off_twist : ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ row col, (a.fam row col).c.Is → ∀ p, p ∉ a.v.tP → GlobalTheory.FinPl.latV ((I.rec7 l Z).sp.X 0) (a.g.x 0).L (· = p) = GlobalTheory.FinPl.latV ((I.rec7 l Z).sp.X 0) ((F0 W u).cls0.lev.Lb.map ((LinearEquiv.funCongrLeft (I.rec7 l Z).host.E (I.rec7 l Z).host.E (finCongr (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)))).toLinearMap.restrictScalars (𝓞 (I.rec7 l Z).host.E))) (· = p) := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr row col hc p hp
  obtain ⟨hs⟩ := hW.tr.std
  obtain ⟨k, hk⟩ := (hs u).ends 0 (Nat.zero_le _) (Or.inl rfl)
  have hx := (hTr.pinX.xs 0 (Nat.zero_le _)).2.2
  have hlb := hk.lb ()
  have hTp : (((B.T u : ℕ) : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
    intro h; apply hp; rw [(ha.tie row col).1.tP p]; exact_mod_cast h
  have hd : ((B.T u : ℕ) : ℤ) ≠ 0 := fun h => hTp (by rw [h]; simp)
  have h1 : ((1 : ℤ) : 𝓞 (I.rec7 l Z).host.F) ∉ p.asIdeal := by
    rw [Int.cast_one]; exact fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h)
  set e := finCongr (Formalism.L2.Forms.rankN (I.rec7 l Z) 0 (Nat.zero_le _)) with he
  have hpi : X.piT u ∣ ((B.T u : ℕ) : 𝓞 B.host.E) := by
    refine ⟨⟨B.host.conj (X.piT u : B.host.E), map_isIntegral_int (B.host.conj : B.host.E →+* B.host.E) (X.piT u).2⟩, ?_⟩
    apply RingOfIntegers.ext
    have := X.piT_norm u
    push_cast
    exact this.symm
  refine le_antisymm (GlobalTheory.FinPl.latV_le_of_int_smul _ _ _ ((B.T u : ℕ) : ℤ) hd ?_ p hTp)
    (GlobalTheory.FinPl.latV_le_of_int_smul _ _ _ 1 one_ne_zero ?_ p h1)
  · intro y hy
    have hyi : ∀ j, IsIntegral ℤ (y j) := (hx y).1 hy
    refine Submodule.mem_map.2 ⟨fun j => (((B.T u : ℕ) : ℤ) • y) (e.symm j), (hlb _).2 fun j => ?_, ?_⟩
    · refine ⟨((B.T u : ℕ) : 𝓞 B.host.E) * ⟨y (e.symm j), hyi _⟩, ?_, fun _ => dvd_mul_of_dvd_left hpi _⟩
      show (((B.T u : ℕ) : ℤ) • y) (e.symm j) = _
      rw [Pi.smul_apply, zsmul_eq_mul]
      push_cast
      rfl
    · funext i
      show (((B.T u : ℕ) : ℤ) • y) (e.symm (e i)) = _
      rw [Equiv.symm_apply_apply]
  · rintro _ ⟨x, hxm, rfl⟩
    rw [one_smul]
    refine (hx _).2 fun j => ?_
    obtain ⟨r, hr, -⟩ := (hlb x).1 hxm (e j)
    show IsIntegral ℤ (x (e j))
    rw [hr]; exact r.2

end GlobalTheory.Fam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeResiduePairEqScalarOfSameStabilizer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing

noncomputable section

namespace GlobalTheory.LatPair.StabScal

section SlopeTestRemainingChoices
variable {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n]

def scal (s : k) (hs : s ≠ 0) : GL n k :=
  ⟨s • 1, s⁻¹ • 1, by rw [smul_mul_smul_comm, one_mul, mul_inv_cancel₀ hs, one_smul],
    by rw [smul_mul_smul_comm, one_mul, inv_mul_cancel₀ hs, one_smul]⟩

theorem scal_inv_smul (s : k) (hs : s ≠ 0) (x : n → k) : (scal s hs : GL n k)⁻¹ • x = s⁻¹ • x := by
  show (s⁻¹ • (1 : Matrix n n k)) *ᵥ x = _
  rw [Matrix.smul_mulVec, one_mulVec]

theorem scal_comm (s : k) (hs : s ≠ 0) (h : GL n k) : h * scal s hs = scal s hs * h := by
  ext1
  show h.val * (s • (1 : Matrix n n k)) = (s • (1 : Matrix n n k)) * h.val
  rw [mul_smul_comm, mul_one, smul_mul_assoc, one_mul]

def trv (b d : n) (t : k) (hbd : b ≠ d) : GL n k :=
  ⟨Matrix.transvection b d t, Matrix.transvection b d (-t),
   by rw [Matrix.transvection_mul_transvection_same b d hbd, add_neg_cancel, Matrix.transvection_zero],
   by rw [Matrix.transvection_mul_transvection_same b d hbd, neg_add_cancel, Matrix.transvection_zero]⟩

theorem transvection_mulVec' (b d : n) (t : k) (x : n → k) :
    Matrix.transvection b d t *ᵥ x = x + Pi.single b (t * x d) := by
  ext j
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, Pi.single_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, ite_and]
  by_cases h : b = j
  · subst h; simp
  · simp [h, Ne.symm h]

theorem trv_inv_smul (b d : n) (t : k) (hbd : b ≠ d) (x : n → k) :
    (trv b d t hbd)⁻¹ • x = x + Pi.single b (-t * x d) := transvection_mulVec' b d (-t) x

end SlopeTestRemainingChoices

theorem transvection_smul_stdPair : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i b d : n) (t : 𝒪[k]) (g : GL n k), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → g.val = Matrix.transvection b d (t : k) → g • GlobalTheory.LatPair.stdPair k i = GlobalTheory.LatPair.stdPair k i := by
  intro k _ _ _ _ n _ _ i b d t g hbd hbi hg
  have hinv : (g⁻¹ : GL n k).val = Matrix.transvection b d (-(t : k)) := by
    have h1 : (g⁻¹ : GL n k).val * g.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (g⁻¹ : GL n k).val = (g⁻¹ : GL n k).val * (g.val * Matrix.transvection b d (-(t : k))) := by
          rw [hg, Matrix.transvection_mul_transvection_same b d hbd, add_neg_cancel, Matrix.transvection_zero,
            mul_one]
      _ = _ := by rw [← mul_assoc, h1, one_mul]
  have htO : (t : k) ∈ 𝒪[k] := t.2
  refine Pair.ext fun x a => ?_
  let y : n → k := x + Pi.single b (-(t : k) * x d)
  have hyj : ∀ j, y j = x j + (Pi.single b (-(t : k) * x d) : n → k) j := fun j => rfl
  have hsm : g⁻¹ • x = y := by
    show (g⁻¹ : GL n k).val *ᵥ x = _
    rw [hinv, transvection_mulVec']
  rw [Pair.smul_hasVal, hsm, stdPair_hasVal, stdPair_hasVal]
  have hd : y d = x d := by rw [hyj]; simp [Pi.single_apply, Ne.symm hbd]
  have hint : (∀ j, y j ∈ 𝒪[k]) ↔ ∀ j, x j ∈ 𝒪[k] := by
    constructor
    · intro hy j
      have hxd : x d ∈ 𝒪[k] := by rw [← hd]; exact hy d
      have : x j = y j + (Pi.single b ((t : k) * x d) : n → k) j := by
        rw [hyj]
        simp only [Pi.single_apply]
        split_ifs <;> ring
      rw [this]
      refine add_mem (hy j) ?_
      rw [Pi.single_apply]
      split_ifs
      · exact mul_mem htO hxd
      · exact zero_mem _
    · intro hx j
      rw [hyj, Pi.single_apply]
      split_ifs
      · exact add_mem (hx j) (mul_mem (neg_mem htO) (hx d))
      · simpa using hx j
  have hres : ∀ (hx : ∀ j, x j ∈ 𝒪[k]) (hy : ∀ j, y j ∈ 𝒪[k]),
      IsLocalRing.residue 𝒪[k] ⟨y i, hy i⟩ = IsLocalRing.residue 𝒪[k] ⟨x i, hx i⟩ := by
    intro hx hy
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    by_cases hb : b = i
    · subst hb
      have hm : t ∈ IsLocalRing.maximalIdeal 𝒪[k] := hbi.resolve_left (not_not.2 rfl)
      have : (⟨y b, hy b⟩ : 𝒪[k]) - ⟨x b, hx b⟩ = -(t * ⟨x d, hx d⟩) := by
        apply Subtype.ext
        push_cast
        rw [hyj, Pi.single_eq_same]
        ring
      rw [this]
      exact neg_mem (Ideal.mul_mem_right _ _ hm)
    · have : (⟨y i, hy i⟩ : 𝒪[k]) - ⟨x i, hx i⟩ = 0 := by
        apply Subtype.ext
        show y i - x i = 0
        rw [hyj]
        simp [Pi.single_apply, Ne.symm hb]
      rw [this]
      exact zero_mem _
  constructor
  · rintro ⟨hy, rfl⟩
    exact ⟨hint.1 hy, (hres _ hy).symm⟩
  · rintro ⟨hx, rfl⟩
    exact ⟨hint.2 hx, hres hx _⟩

theorem eq_scalar_smul_of_stab : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (P P' : GlobalTheory.LatPair.Pair k n), 3 ≤ Fintype.card n → (∀ g : GL n k, g • P = P ↔ g • P' = P') → ∃ (g : GL n k) (s : k), s ≠ 0 ∧ g.val = s • (1 : Matrix n n k) ∧ P' = g • P := by
  intro k _ _ _ _ n _ _ P P' hn hst
  obtain ⟨i⟩ : Nonempty n := Fintype.card_pos_iff.1 (by omega)
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (GL n k) (stdPair k i) P
  set Q := h⁻¹ • P' with hQ
  clear_value Q
  have hstQ : ∀ g : GL n k, g • stdPair k i = stdPair k i → g • Q = Q := by
    intro g hg
    have h1 : (h * g * h⁻¹) • P = P := by rw [← hh, smul_smul, show h * g * h⁻¹ * h = h * g by group, mul_smul, hg]
    have h2 := (hst _).1 h1
    rw [hQ, smul_smul]
    calc (g * h⁻¹) • P' = h⁻¹ • (h * g * h⁻¹) • P' := by rw [smul_smul]; congr 1; group
      _ = h⁻¹ • P' := by rw [h2]
  have hcl : ∀ (x : n → k) (a : 𝓀[k]), Q.HasVal x a → ∀ (b d : n) (t : 𝒪[k]), b ≠ d →
      (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → Q.HasVal (x + Pi.single b ((t : k) * x d)) a := by
    intro x a hx b d t hbd hbi
    have hg : trv b d ((-t : 𝒪[k]) : k) hbd • stdPair k i = stdPair k i :=
      transvection_smul_stdPair k n i b d (-t) _ hbd (hbi.imp id (fun h => (IsLocalRing.maximalIdeal 𝒪[k]).neg_mem_iff.2 h)) rfl
    have h2 : (trv b d ((-t : 𝒪[k]) : k) hbd • Q).HasVal x a := by rw [hstQ _ hg]; exact hx
    rw [Pair.smul_hasVal, trv_inv_smul] at h2
    convert h2 using 3
    push_cast
    ring
  have hlat : ∀ x ∈ Q.lat, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) →
      x + Pi.single b ((t : k) * x d) ∈ Q.lat := fun x hx b d t hbd hbi =>
    (hcl x _ (Q.hasVal_fn ⟨x, hx⟩) b d t hbd hbi).mem
  obtain ⟨c, hc0, hcb, hca⟩ := GlobalTheory.T.localLattice_exists_scalar_bound_attained k n Q.lat Q.isLat ⟨i⟩
  rcases GlobalTheory.T.transvectionStable_localLattice_shape k n i Q.lat c hn hc0 hlat hcb hca with hA | hB
  swap
  · exact (GlobalTheory.T.no_transvectionInvariant_pair_on_scaledKernel k n i Q c hn hc0 hB hcl).elim
  obtain ⟨ε, hε0, hε⟩ := GlobalTheory.T.transvectionInvariant_pair_functional_residue k n i Q c (by omega) hc0 hA hcl
  obtain ⟨w, hw⟩ := IsLocalRing.residue_surjective (R := 𝒪[k]) ε
  have hwu : IsUnit w := by
    rw [← IsLocalRing.notMem_maximalIdeal, ← IsLocalRing.residue_eq_zero_iff, hw]
    exact hε0
  obtain ⟨u, hu⟩ := hwu
  have huw : (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) * (w : k) = 1 := by
    have h1 : ((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) * w = 1 := by rw [← hu, Units.inv_mul]
    have h2 := congrArg (fun z : 𝒪[k] => (z : k)) h1
    simpa using h2
  have hw0 : (w : k) ≠ 0 := fun h0 => by simp [h0] at huw
  have hint : ∀ y : k, (w : k) * y ∈ 𝒪[k] → y ∈ 𝒪[k] := by
    intro y hy
    have : y = (((u⁻¹ : 𝒪[k]ˣ) : 𝒪[k]) : k) * ((w : k) * y) := by rw [← mul_assoc, huw, one_mul]
    rw [this]
    exact mul_mem (u⁻¹ : 𝒪[k]ˣ).val.2 hy
  set s := c * (w : k)⁻¹ with hs_def
  have hs : s ≠ 0 := mul_ne_zero hc0 (inv_ne_zero hw0)
  have key : ∀ y : k, s⁻¹ * y = (w : k) * (c⁻¹ * y) := by
    intro y
    rw [hs_def, mul_inv, inv_inv]
    ring
  have hQs : Q = (scal s hs : GL n k) • stdPair k i := by
    refine Pair.ext fun x a => ?_
    rw [Pair.smul_hasVal, stdPair_hasVal, scal_inv_smul]
    constructor
    · intro hQx
      have hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k] := (hA x).1 hQx.mem
      refine ⟨fun j => ?_, ?_⟩
      · rw [Pi.smul_apply, smul_eq_mul, key]
        exact mul_mem w.2 (hx j)
      · rw [hQx.unique (hε x hx), ← hw, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Pi.smul_apply, smul_eq_mul, key]
        push_cast
        ring
    · rintro ⟨hx', rfl⟩
      have hx : ∀ j, c⁻¹ * x j ∈ 𝒪[k] := fun j => hint _ (by have := hx' j; rwa [Pi.smul_apply, smul_eq_mul, key] at this)
      convert hε x hx using 1
      rw [← hw, ← map_mul]
      congr 1
      apply Subtype.ext
      simp only [Pi.smul_apply, smul_eq_mul, key]
      push_cast
      ring
  refine ⟨(scal s hs : GL n k), s, hs, rfl, ?_⟩
  calc P' = h • Q := by rw [hQ, smul_inv_smul]
    _ = h • (scal s hs : GL n k) • stdPair k i := by rw [hQs]
    _ = (scal s hs : GL n k) • P := by rw [← hh, smul_smul, smul_smul, scal_comm]

end GlobalTheory.LatPair.StabScal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LowerBlockParameterTwistLFactorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lower_block_parameter_twist_L_factor : ∀ (D : D7) (c : Com D) (w : Twist D), w.Is c → ∀ k < D.R.m, ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ x ϖ, IsLocUnif φ x ϖ → (∀ z t, GlobalTheory.LFun.seg PP z t = GlobalTheory.ParHecke.segL ϖ z t) ∧ (qPar c PP x k).card = k * D.R.t ∧ ∀ α : Fin (k * D.R.t) → ℂˣ, Finset.univ.val.map α = (qPar c PP x k).map (· * (Circle.toUnits (c.chT (k + 1) x))⁻¹) → (∀ i, ‖(α i : ℂ)‖ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2) ∧ ‖(α i : ℂ)‖⁻¹ ≤ (Ideal.absNorm PP.asIdeal : ℝ) ^ (((D.R.t : ℝ) - 1) / 2)) ∧ GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.lFactor (Ideal.absNorm PP.asIdeal) α⁻¹ ((D.R.t : ℂ) / 2 + 1 / 2) * GlobalTheory.GLDoubling.invNormFactor (Ideal.absNorm PP.asIdeal) (k * D.R.t) ((D.R.t : ℂ) / 2) = blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ) := by
  first | exact @GlobalTheory.ChainTw.qPar_twist_lFactor | exact GlobalTheory.ChainTw.qPar_twist_lFactor | (intros; apply GlobalTheory.ChainTw.qPar_twist_lFactor <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelFormulasWittSourceProof
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.MixSourceFormulas

theorem mixed_source : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.MixedSource D := by
  intro D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ f hf
  have hth : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ ho.std S T).1
  have hbr : ∀ (f : WO S T → ℂ) x, d.mixS T ψ μ 𝓕 f x = d.mixS T ψ μ 𝓕 (heisO ψ S T (d.extX T x) f) 0 :=
    fun f x => (GlobalTheory.T.wittSourceMixedCoord_heisenbergRestriction D ψ S S₀ T ρ d).2.2.2.2.2.2.1 μ 𝓕 f x
  have hmv := GlobalTheory.T.weil_operators_witt_parabolic_origin_to_point D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hun := GlobalTheory.T.wittMixedModel_unipotent_formulas D ψ S S₀ T ρ d χS χT om ho μ 𝓕 hμ f hf
  have hlv := fun w => GlobalTheory.T.weilRepresentation_value_at_origin_leviFactor D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ (heisO ψ S T w f) (hth w f hf)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro h x
    rw [(hmv x).1 h, GlobalTheory.T.mixedCoordinate_origin_weilRep_target_equivariant D ψ S S₀ T ρ d χS χT om om₀ ho ho₀ μ 𝓕 hμ h _ (hth _ f hf), ← hbr]
  · intro g x
    have e := (hmv x).2.1 1 g
    rw [map_one, one_mul, Units.val_one, Matrix.mul_one] at e
    rw [e, (hlv _).1 g, ← hbr]
  · intro a x
    have e := (hmv x).2.1 a 1
    rw [map_one, mul_one] at e
    rw [e, (hlv _).2.2 a, ← hbr]
  · intro b x
    exact (hun x).1 b
  · intro c x
    exact (hun x).2 c

end GlobalTheory.MixSourceFormulas
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulFractionalIdealCompletionSubsetIffMemQuotientStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mul_fractionalIdealCompletion_subset_iff_mem_quotient : ∀ (D : D7) (v : Pl D) (𝔞 𝔟 : FI D), 𝔞 ≠ 0 → 𝔟 ≠ 0 → ∀ s ∈ idAt D (· = v), (∀ a ∈ idV 𝔞 v, s * a ∈ idV 𝔟 v) ↔ s ∈ idV (𝔟 * 𝔞⁻¹) v := by
  first | exact @GlobalTheory.IdealQuot.mul_subset_iff | exact GlobalTheory.IdealQuot.mul_subset_iff | (intros; apply GlobalTheory.IdealQuot.mul_subset_iff <;> assumption)
end

