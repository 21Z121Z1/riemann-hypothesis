import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
import Formalism.LocalToGlobal.Divisibility.NumbersLink
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1901
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1906
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CmThetaTaylorCoeffAlgebraicAndConjugate
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1809
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1873
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1914
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0031
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneCosetOfIsTensor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationLeOneOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteCoefficientBound
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0325
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledDarbouxCoordsCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1498

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemberRowsOfKernelDatumSizes
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColRows
open scoped ComplexOrder

namespace GlobalTheory.ColRows

theorem rowsBody_of_kerTies : ∀ CY CT : ℝ, 0 ≤ CT → ∃ C0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : G.Inst D L) (Gl : G.LatInst D) (K : G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl K Y cX) (t : KerEntTied ex) [IsTotallyComplex t.X.K] (W : Formalism.L2.Col.Wts t.X t.Pr.Word D.R) (Del h0 : ℕ) (hX : t.X.Ok) (Bs : DefBase t.X.K) (Df : DefSide Bs) (Xg : Finset (Formalism.L2.Col.G0 t.X.E t.Pr.vGs D.R.r → t.X.K)) (tup : Bs.Tup → D.what₂.Tup) (hP : ∀ τ, (mtildeGSD W t.Ch t.sel (t.tup (tup τ)) (rPsymF (R := D.R) t.Ch)).Ok) (b : ∀ τ, D.what₂.Word → (t.idx (tup τ)).β (t.m2 + 1)) (hY : ∀ τ x, YbHyp (R := D.R) t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) (t.word x) t.m2 (b τ x)) (hK : ∀ τ x, KerEquivC W t.Ch t.sel (t.tup (tup τ)) (t.cst (tup τ)) (t.idx (tup τ)) t.amb (t.word x) t.m2 (b τ x) (hY τ x) (rPsymF (R := D.R) t.Ch)) (hF : ∀ τ x j, (chF W t.sel (t.tup (tup τ)) (t.idx (tup τ)) (t.word x) j).Ok) (hE : ∀ x, (evGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch) (t.word x)).Ok) (ev : ∀ τ, (Fin (Df.nV τ) → t.X.K) →ₗ[t.X.K] V0X W t.Ch t.sel (t.tup (tup τ)) Xg (rPsymF (R := D.R) t.Ch)) (u : D.what₂.Word) (eJ : Bs.J ≃ Fin D.R.m) (Nc lam0 c0 ce Ch Sw C1 : ℝ) (H : (ofRecord D L Del h0).NumFacts (letterOf D L Del h0 u) Nc lam0 c0 ce Ch Sw C1), tup Bs.μ0 = D.what₂.mu0 → KerTies t W Del h0 → KerSizes t W Del h0 CY CT → C0 ≤ Ch → (∀ v : InfinitePlace t.X.K, ((Df.HV Bs.μ0).map v.embedding).PosDef) → (∀ X0, IsFrames Df X0 → ∀ v F, ((mtildeGSD W t.Ch t.sel (t.tup (tup Bs.μ0)) (rPsymF (R := D.R) t.Ch)).ipAt (hP Bs.μ0) v ((ev Bs.μ0 F).1).1 ((ev Bs.μ0 F).1).1).re ≤ Formalism.HermitianLatticesTheory.normAt (Pi.basisFun t.X.K (Fin (Df.nV Bs.μ0))) X0 v F ^ 2) → RowsBody (colFace hX Df Xg (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) (fun τ => t.idx_ok (tup τ)) hP D.what₂.Word t.word b hY (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK) hF ev) u (memQ (A := (kerRec (fun τ => t.tup (tup τ)) (fun τ => t.cst (tup τ)) (fun τ => t.idx (tup τ)) t.word b hY t.amb hK)) (hF := hF) hE (x := u)) (colsIn W t.Ch hX t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.idx (tup Bs.μ0)) (t.idx_ok (tup Bs.μ0)) (t.word u)) (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) ∧ ∀ v, IsUnit ((MramH W t.Ch hX (t.word u)).X v).det := by
  intro CY CT hCT
  obtain ⟨C0, hC0⟩ := GlobalTheory.T.columnsMemberRows_of_logLevel_le CY CT hCT
  refine ⟨C0, fun D L hT Gi Gl K Y cX ex t _ W Del h0 hX Bs Df Xg tup hP b hY hK hF hE ev u eJ Nc lam0 c0 ce Ch Sw C1 H hmu hTi hS hC hPD hFr => ?_⟩
  obtain ⟨pl, hpl⟩ := hTi.wts
  have hmu0 : t.tup (tup Bs.μ0) = 1 := hmu ▸ hTi.mu0
  have hsh : (t.cst (tup Bs.μ0)).sharp = true := by rw [hmu]; exact hTi.sharp
  have hfld : FieldOfDefinition W t.sel (t.tup (tup Bs.μ0)) (t.cst (tup Bs.μ0)) (t.word u) t.amb := by
    rw [hmu]; exact hTi.fld u
  have hlog : Real.log (t.Pr.T (t.word u) : ℝ) ≤ CT * D.R.m * L.sc.L := by rw [t.T_rec u]; exact hS.logT u
  have hRd : Reads (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (t.Pr.T (t.word u))
      (RecNums.ofNum (ofRecord D L Del h0) eJ (letterOf D L Del h0 u) (D.mem u).A.T Nc lam0 c0 ce Ch Sw C1 H) := by
    rw [t.T_rec u]; exact NumReads.ofNum_reads _ _ eJ _ _ Nc lam0 c0 ce Ch Sw C1 H
  have hm2 := hTi.m2
  have hcc := t.cc_rec
  have hsz := hS.sizes
  have hrw := hS.what₂ u
  have hho := hTi.host
  have hch := hTi.chr
  have han := hTi.an
  have hwt := hpl u
  clear hTi hS hpl
  rcases t with ⟨cc, cc_rec, cc_ok, δ, δ_ok, B, χ, χ_ok, idl, idl_ok, χ_rec, cD, X, seam, seam_ok, Pr, pr_ok, g_rec, ChT, sel, S, word, T_rec, tupT, Q_rec, cst, idx, m2, glob, glob_σ, glob_xi, idx_ok, O, rd, rd_chain, O_dgen, O_S, O_lat, O_Th, unf, ent, ent_lam, kf, kf_un, served⟩
  dsimp only at *
  subst hm2
  subst hcc
  exact hC0 D (ofRecord D L Del h0) X seam Pr W ChT glob sel S hX Bs Df Xg (fun τ => tupT (tup τ)) (fun τ => cst (tup τ))
    (fun τ => idx (tup τ)) (fun τ => idx_ok (tup τ)) hP D.what₂.Word word b hY δ B χ cD hK hF hE ev pl u (letterOf D L Del h0 u) eJ _
    hho hwt hch han hmu0 hsh hfld hsz hrw hlog hRd hC hPD hFr

end GlobalTheory.ColRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinorPolIsHomogeneous
section
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

namespace GlobalTheory.RotJets

theorem det_X_isHomogeneous {σ : Type*} {a : ℕ} (f : Fin a → Fin a → σ) :
    (Matrix.of fun i i' => (MvPolynomial.X (f i i') : MvPolynomial σ ℂ)).det.IsHomogeneous a := by
  rw [Matrix.det_apply']
  refine MvPolynomial.IsHomogeneous.sum _ _ _ (fun e _ => ?_)
  have h1 : (∏ i, (Matrix.of fun i i' => (MvPolynomial.X (f i i') : MvPolynomial σ ℂ)) (e i) i).IsHomogeneous
      (∑ _i : Fin a, 1) :=
    MvPolynomial.IsHomogeneous.prod _ _ _ (fun i _ => MvPolynomial.isHomogeneous_X ℂ _)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at h1
  have h0 : (((Equiv.Perm.sign e : ℤ) : MvPolynomial σ ℂ)).IsHomogeneous 0 := by
    have : (((Equiv.Perm.sign e : ℤ) : MvPolynomial σ ℂ)) = MvPolynomial.C ((Equiv.Perm.sign e : ℤ) : ℂ) := by simp
    rw [this]; exact MvPolynomial.isHomogeneous_C _ _
  simpa using h0.mul h1

theorem minorPol_isHomogeneous {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n) :
    (GlobalTheory.NormSum.minorPol D T).IsHomogeneous (a * ∑ τ, n τ) := by
  unfold GlobalTheory.NormSum.minorPol
  have h := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset D.what₂.Tau)
    (fun τ => ∏ j, (Matrix.of fun i i' => (MvPolynomial.X (τ, ((T τ j) : Fin a → Fin d) i, i') :
      MvPolynomial (GL3Theta.Idx D a d) ℂ)).det) (fun τ => ∑ _j : Fin (n τ), a) (fun τ _ =>
      MvPolynomial.IsHomogeneous.prod _ _ _ (fun j _ => det_X_isHomogeneous _))
  convert h using 1
  simp [Finset.mul_sum, mul_comm]

theorem card_of_mem_support {D : D7} {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : GlobalTheory.NormSum.Tup D a d n)
    {α : TaylorLogMetric.Mono D a d} (hα : α ∈ (GlobalTheory.NormSum.minorPol D T).support) :
    Multiset.card (Finsupp.toMultiset α) = a * ∑ τ, n τ := by
  have h := minorPol_isHomogeneous T (MvPolynomial.mem_support_iff.mp hα)
  rw [Finsupp.card_toMultiset]
  rw [← h]
  simp [Finsupp.weight_apply, Finsupp.sum]

end GlobalTheory.RotJets
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedProjectionPreservesSchwartzAdm
section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MixedForm

variable {F : Type} [Field F] [NumberField F] {κ : Type}

def finRepl (v : Pl F) (z : κ → Af F) (x : κ → Fv F v) : κ → Af F :=
  fun i => z i - GlobalTheory.AdelicU.singleFin v (evalV F v (z i)) + GlobalTheory.AdelicU.singleFin v (x i)

def finProj (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) (g : (κ → Af F) → ℂ) :
    (κ → Af F) → ℂ :=
  fun z => φ₀ (fun i => evalV F v (z i)) * l fun x => g (finRepl v z x)

theorem evalV_finRepl (v : Pl F) (z : κ → Af F) (x : κ → Fv F v) (i : κ) :
    evalV F v (finRepl v z x i) = x i := by
  simp [finRepl, GlobalTheory.AdelicU.evalV_singleFin_self]

theorem finRepl_finRepl (v : Pl F) (z : κ → Af F) (x : κ → Fv F v) :
    finRepl v (finRepl v z x) (fun i => evalV F v (z i)) = z := by
  funext i
  have := evalV_finRepl v z x i
  simp only [finRepl] at this ⊢
  rw [this]; abel

theorem continuous_finRepl (v : Pl F) :
    Continuous fun p : (κ → Af F) × (κ → Fv F v) => finRepl v p.1 p.2 := by
  refine continuous_pi fun i => ?_
  have h1 : Continuous fun p : (κ → Af F) × (κ → Fv F v) => p.1 i := (continuous_apply i).comp continuous_fst
  have h2 : Continuous fun p : (κ → Af F) × (κ → Fv F v) => p.2 i := (continuous_apply i).comp continuous_snd
  exact (h1.sub ((GlobalTheory.AdelicU.continuous_singleFin v).comp ((RestrictedProduct.continuous_eval v).comp h1))).add
    ((GlobalTheory.AdelicU.continuous_singleFin v).comp h2)

theorem finProj_mem_SB [Fintype κ] (v : Pl F) {φ₀ : (κ → Fv F v) → ℂ} (hφ₀ : φ₀ ∈ SB (κ → Fv F v))
    (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    finProj v φ₀ l g ∈ SB (κ → Af F) := by
  haveI : T2Space (Af F) := GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F
  have he : Continuous fun z : κ → Af F => fun i => evalV F v (z i) :=
    continuous_pi fun i => (RestrictedProduct.continuous_eval v).comp (continuous_apply i)
  have hs : Continuous fun z : κ → Af F => fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z i)) :=
    continuous_pi fun i => (GlobalTheory.AdelicU.continuous_singleFin v).comp
      ((RestrictedProduct.continuous_eval v).comp (continuous_apply i))
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro z₀
    let δ : (κ → Af F) → (κ → Af F) := fun z =>
      (z₀ - fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z₀ i))) -
        (z - fun i => GlobalTheory.AdelicU.singleFin v (evalV F v (z i)))
    have hδ : Filter.Tendsto δ (nhds z₀) (nhds 0) := by
      have hc : Continuous δ := continuous_const.sub (continuous_id.sub hs)
      simpa [δ] using hc.tendsto z₀
    have hφe : ∀ᶠ z in nhds z₀, φ₀ (fun i => evalV F v (z i)) = φ₀ (fun i => evalV F v (z₀ i)) :=
      (hφ₀.1.comp_continuous he).eventually_eq z₀
    filter_upwards [hδ.eventually (GlobalTheory.SBConv.eventually_translate hg), hφe] with z hz h1
    simp only [finProj]
    rw [h1]
    congr 2
    funext x
    have e : finRepl v z x = finRepl v z₀ x - δ z := by
      funext i; simp only [finRepl, δ, Pi.sub_apply]; abel
    rw [e, hz]
  · refine HasCompactSupport.intro ((hg.2.isCompact.prod hφ₀.2.isCompact).image (continuous_finRepl v)) ?_
    intro z hz
    by_contra h
    apply hz
    simp only [finProj] at h
    have h1 : φ₀ (fun i => evalV F v (z i)) ≠ 0 := left_ne_zero_of_mul h
    have h2 := right_ne_zero_of_mul h
    obtain ⟨x, hx⟩ : ∃ x, g (finRepl v z x) ≠ 0 := by
      by_contra hc
      push_neg at hc
      apply h2
      have : (fun x => g (finRepl v z x)) = 0 := funext hc
      rw [this, map_zero]
    refine ⟨(finRepl v z x, fun i => evalV F v (z i)), ⟨subset_tsupport _ hx, subset_tsupport _ h1⟩, ?_⟩
    exact finRepl_finRepl v z x

theorem proj_pureA [Fintype κ] (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ) (l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ)
    (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g : (κ → Af F) → ℂ) :
    proj v φ₀ l (pureA F f g) = pureA F f (finProj v φ₀ l g) := by
  funext y
  have e : (fun x => pureA F f g (repl v y x)) =
      f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1) • fun x => g (finRepl v (fun i => (y i).2) x) := by
    funext x
    have a1 : ∀ i, (repl v y x i).1 = (y i).1 := fun i => by
      show (y i).1 - (0 : Ainf F) + 0 = (y i).1
      rw [sub_zero, add_zero]
    have a2 : ∀ i, (repl v y x i).2 = finRepl v (fun i => (y i).2) x i := fun i => rfl
    show f (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (repl v y x i).1) * g (fun i => (repl v y x i).2) = _
    simp only [a1, a2, Pi.smul_apply, smul_eq_mul]
  rw [proj_apply, e, map_smul]
  simp only [pureA, finProj, smul_eq_mul]
  change φ₀ (fun i => evalV F v (y i).2) * _ = _
  ring

theorem proj_schA_adm : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (v : Pl F) (φ₀ : (κ → Fv F v) → ℂ), φ₀ ∈ SB (κ → Fv F v) → ∀ l : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ,
    (∀ Φ ∈ schA F κ, GlobalTheory.MixedForm.proj v φ₀ l Φ ∈ schA F κ) ∧
      ∀ L ∈ (adeleClass F).adm κ, L ∘ₗ GlobalTheory.MixedForm.proj v φ₀ l ∈ (adeleClass F).adm κ := by
  intro F _ _ κ _ v φ₀ hφ₀ l
  refine ⟨fun Φ hΦ => ?_, fun L hL => ?_⟩
  · induction hΦ using Submodule.span_induction with
    | mem Φ hΦ =>
      obtain ⟨f, g, hg, rfl⟩ := hΦ
      rw [proj_pureA]
      exact Submodule.subset_span ⟨f, _, finProj_mem_SB v hφ₀ l hg, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  · intro g hg
    obtain ⟨T, hT⟩ := hL _ (finProj_mem_SB v hφ₀ l hg)
    exact ⟨T, fun f => by rw [LinearMap.comp_apply, proj_pureA, hT]⟩

end GlobalTheory.MixedForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MovedStaircaseTensorPeriodicUniformizerPow
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.UnfoldLoss

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem stairElt_diag (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (e : ℕ) (J : G.Level) (X : ℕ × ℕ) :
    ∃ n : Fin (G.rank X) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) X =
        diagGL fun a => ϖ ^ n a := by
  have h1 : ∀ Y : ℕ × ℕ, ∃ n : Fin (G.rank Y) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      (1 : GL (Fin (G.rank Y)) k) = diagGL fun a => ϖ ^ n a := fun Y =>
    ⟨fun _ => 0, fun _ => Nat.zero_le _, Units.ext (by simp)⟩
  have h2 : ∀ j : ℕ, ∃ n : Fin (G.rank (G.m, j)) → ℕ, (∀ a, n a ≤ e * (G.m - 1)) ∧
      stair G ϖ e j = diagGL fun a => ϖ ^ n a := fun j =>
    ⟨fun a => e * (a.val + 1 - topRank G j), fun a => Nat.mul_le_mul_left _ (by
      have := topRank_add hs j; have := a.2; omega), rfl⟩
  obtain ⟨i, j⟩ := X
  by_cases hi : i = G.m
  · subst hi
    by_cases hj : j + 2 ≤ G.m
    · borelize k
      rw [through_elt _ hj]; exact h2 j
    · rw [Reps.elt, onColumn_apply]
      cases j with
      | zero => exact h2 0
      | succ j =>
        have : ¬ j < G.m - 2 := by omega
        simp only [dif_neg this]
        exact h1 _
  · rw [Reps.elt, onColumn, dif_neg hi]
    exact h1 _

theorem valuation_fill_sub_le (G : Grid k) (hs : 1 ≤ G.s) (ϖ : kˣ) (n : ℕ) (x : ColArgs G) (y : RowArgs G)
    (v l : Vars G) (hl : l ∈ varLat G ϖ n) (b : Edge) (r : Fin (G.rank b.tgt)) (s : Fin (G.rank b.src)) :
    valuation k ((fill hs x y (v + l) - fill hs x y v) b r s) ≤ valuation k ((ϖ ^ n : kˣ) : k) := by
  rcases b with ⟨i, j⟩ | ⟨i, j⟩ <;> simp only [Pi.sub_apply, Matrix.sub_apply, fill] <;> split_ifs
  · simp only [Matrix.transpose_apply, Matrix.submatrix_apply, downMap]
    split_ifs with h
    · simp only [Matrix.reindex_apply, Matrix.submatrix_apply, stepPt, Matrix.add_apply, Matrix.of_apply,
        add_sub_add_left_eq_sub]
      split_ifs
      · simp only [Pi.add_apply, add_sub_cancel_left]
        exact hl ⟨j, h⟩ _
      · simp
    · simp
    · simp
  all_goals simp

end

theorem moved_stair_periodic : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : Grid k) (hs : 1 ≤ G.s)
    (ϖ : kˣ), IsUnif ϖ → ∀ (e : ℕ) (T : G.Args → ℂ), G.IsTensor ϖ e (oppositePath G.m) T → ∀ (J : G.Level) (keep : Bool)
    (x : ColArgs G) (y : RowArgs G) (v l : Vars G), l ∈ varLat G ϖ (G.m * e) →
    moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y (v + l)) =
      moved G keep ((Reps.through hs J (stair G ϖ e)).elt fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) T (fill hs x y v) := by
  intro k _ _ _ _ G hs ϖ hϖ e T hT J keep x y v l hl
  rcases Nat.eq_zero_or_pos G.m with hm | hm
  · have : l = 0 := funext fun j => absurd j.2 (by omega)
    rw [this, add_zero]
  have hd := stairElt_diag G hs ϖ e J
  generalize (Reps.through hs J (stair G ϖ e)).elt (fun i => DoubleCoset.mk _ _ (stair G ϖ e (i + 1))) = g at hd ⊢
  have hf := valuation_fill_sub_le G hs ϖ _ x y v l hl
  have hsum : G.moveArgs .one g (fill hs x y (v + l)) =
      G.moveArgs .one g (fill hs x y v) + G.moveArgs .one g (fill hs x y (v + l) - fill hs x y v) := by
    funext b
    simp only [Grid.moveArgs, Pi.add_apply, Pi.sub_apply, Matrix.mul_sub, Matrix.sub_mul, add_sub_cancel]
  simp only [moved, Grid.pathAct]
  rw [hsum, hT.2.2]
  intro b r
  generalize fill hs x y (v + l) - fill hs x y v = d at hf
  obtain ⟨n, -, hn⟩ := hd b.tgt
  obtain ⟨n', hn1, hn'⟩ := hd b.src
  have h0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have h1 : valuation k (ϖ : k) ≤ 1 := hϖ.mem
  rw [SplitFlip.stdLat, smul_diagLat, mem_diagLat]
  intro s
  have hv : (G.moveArgs .one g d b).row r s = (ϖ : k) ^ n r * d b r s * ((ϖ : k) ^ n' s)⁻¹ := by
    have hinv : ((diagGL fun a => ϖ ^ n' a : GL (Fin (G.rank b.src)) k)⁻¹).val =
        Matrix.diagonal fun a => ((ϖ : k) ^ n' a)⁻¹ := by
      rw [Matrix.coe_units_inv]
      refine Matrix.inv_eq_right_inv ?_
      simp [Matrix.diagonal_mul_diagonal]
    simp only [Grid.moveArgs, Assignment.read, invT_inv_val, invT_val, hn, hn', hinv, diagGL_val,
      Matrix.diagonal_transpose, Matrix.row, Matrix.mul_diagonal, Matrix.diagonal_mul, Units.val_pow_eq_pow_val]
  have h2 := hf b r s
  rw [hv]
  simp only [map_mul, map_inv₀, map_pow, Units.val_pow_eq_pow_val, Pi.one_apply, mul_one] at h2 ⊢
  rw [mul_inv_le_iff₀ (pow_pos h0 _), ← pow_add]
  refine (mul_le_of_le_one_left' (pow_le_one' h1 _)).trans (h2.trans (pow_le_pow_right_of_le_one' h1 ?_))
  have := hn1 s
  obtain ⟨m', hm'⟩ := Nat.exists_eq_add_of_le' hm
  rw [hm'] at this ⊢
  simp only [Nat.succ_eq_add_one, zero_add, Nat.add_sub_cancel] at this ⊢
  nlinarith

end GlobalTheory.UnfoldLoss
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAdaptedProjectionExists
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DblSiegelChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hTens_vecMulVec_split {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A)
    {α β : Type} [Fintype α] [Fintype β] (JA : Matrix α α A) (JB : Matrix β β A) (a a' : α → A) (x x' : β → A) :
    hTens c JA JB (Matrix.vecMulVec a x) (Matrix.vecMulVec a' x') =
      (∑ i, ∑ k, a i * JA i k * c (a' k)) * ∑ j, ∑ l, x j * JB j l * c (x' l) := by
  simp only [hTens, Matrix.vecMulVec_apply, map_mul]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem invol {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem form_swap {σ : E →ₐ[F] E} (hσ : ∀ z, σ (σ z) = z) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) : form σ J y x = σ (form σ J x y) := by
  simp only [form, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, hσ, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem form_inc {σ : E →ₐ[F] E} {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ∑ j, ∑ l, incV F x j * incM F J j l * cA σ (incV F y l) = inclR (F := F) (AF F) (form σ J x y) := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul, mul_assoc]

theorem trace_one_tmul (e : E) : Algebra.trace (AF F) (AE F E) ((1 : AF F) ⊗ₜ[F] e) = algebraMap F (AF F) (Algebra.trace F E e) := by
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  rw [Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange, ← Algebra.trace_apply]

theorem eq_zero_of_psi_trace {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (a : AE F E)
    (h : ∀ t : AE F E, ψ (Algebra.trace (AF F) (AE F E) (a * t)) = 1) : a = 0 := by
  classical
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let bb : Module.Basis _ (AF F) (AE F E) := Algebra.TensorProduct.basis (AF F) b
  have hco : ∀ i, ∀ x : AE F E, Algebra.trace (AF F) (AE F E) (x * ((1 : AF F) ⊗ₜ[F] b.traceDual i)) = bb.repr x i := by
    intro i x
    conv_lhs => rw [← bb.sum_repr x]
    rw [Finset.sum_mul, map_sum]
    simp only [smul_mul_assoc, map_smul, bb, Algebra.TensorProduct.basis_apply, Algebra.TensorProduct.tmul_mul_tmul,
      one_mul, trace_one_tmul, mul_comm (b _) (b.traceDual i), Module.Basis.trace_traceDual_mul]
    simp
  refine bb.ext_elem fun i => ?_
  rw [map_zero, Finsupp.zero_apply]
  apply GlobalTheory.DiagNonvan.eq_zero_of_psi_mul hψ
  intro y
  have := h (y • ((1 : AF F) ⊗ₜ[F] b.traceDual i))
  rwa [mul_smul_comm, map_smul, hco, smul_eq_mul, mul_comm] at this

end GlobalTheory.DblSiegelChar

namespace GlobalTheory.DblSiegelChar

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def vdiff (σ : E →ₐ[F] E) {d : ℕ} (c : Fin d ⊕ Fin d → AE F E) : Fin d → AE F E :=
  fun l => cA σ (c (Sum.inl l)) - cA σ (c (Sum.inr l))

theorem vdiff_add (σ : E →ₐ[F] E) {d : ℕ} (a b : Fin d ⊕ Fin d → AE F E) :
    vdiff σ (a + b) = vdiff σ a + vdiff σ b := by
  funext l
  simp only [vdiff, Pi.add_apply, map_add]
  ring

def pairL (σ : E →ₐ[F] E) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E)) (c : Fin d ⊕ Fin d → AE F E) :
    (Fin d → AE F E) →ₗ[AF F] AF F where
  toFun u := Algebra.trace (AF F) (AE F E) (-1 * (u ⬝ᵥ (JW *ᵥ vdiff σ c)))
  map_add' u u' := by simp only [add_dotProduct, mul_add, map_add]
  map_smul' r u := by simp only [smul_dotProduct, mul_smul_comm, map_smul, RingHom.id_apply]

theorem pairL_apply (σ : E →ₐ[F] E) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E)) (c : Fin d ⊕ Fin d → AE F E)
    (u : Fin d → AE F E) : pairL σ JW c u = Algebra.trace (AF F) (AE F E) (-1 * (u ⬝ᵥ (JW *ᵥ vdiff σ c))) := rfl

theorem pairL_add (σ : E →ₐ[F] E) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E)) (a b : Fin d ⊕ Fin d → AE F E) :
    pairL σ JW (a + b) = pairL σ JW a + pairL σ JW b := by
  refine LinearMap.ext fun u => ?_
  simp only [pairL_apply, LinearMap.add_apply, vdiff_add, Matrix.mulVec_add, dotProduct_add, mul_add, map_add]

theorem symp_eq (σ : E →ₐ[F] E) {n n₁ d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (H : Plane E n n₁) (hf : ∑ i, ∑ k, incV F H.y i * incM F JX i k * cA σ (incV F H.x k) = 1)
    (c : Fin d ⊕ Fin d → AE F E) (u : Fin d → AE F E) :
    symp (cA σ) (-1) (incM F JX) (dbl (incM F JW)) (GlobalTheory.DblSiegelX.zs H u) (Matrix.vecMulVec (incV F H.x) c) =
      pairL σ (incM F JW) c u := by
  rw [symp, GlobalTheory.DblSiegelX.zs, hTens_vecMulVec_split, hf, one_mul, pairL_apply]
  congr 2
  have e1 : ((diagCols (Fin d) : Matrix (Fin d ⊕ Fin d) (Fin d) (AE F E)) *ᵥ u) = Sum.elim u u := by
    rw [diagCols, Matrix.fromRows_mulVec, Matrix.one_mulVec]
  have e2 : ∀ U : Fin d ⊕ Fin d → AE F E, ∑ j, ∑ l, U j * dbl (incM F JW) j l * cA σ (c l) =
      U ⬝ᵥ (dbl (incM F JW) *ᵥ fun l => cA σ (c l)) := by
    intro U
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have e3 : vdiff σ c = (fun l => cA σ (c (Sum.inl l))) - fun l => cA σ (c (Sum.inr l)) := rfl
  rw [e1, e2, dbl, Matrix.fromBlocks_mulVec, e3, Matrix.mulVec_sub]
  simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero, zero_add,
    Matrix.neg_mulVec, Pi.neg_apply, Pi.sub_apply, Pi.add_apply, mul_neg, mul_sub, Finset.sum_sub_distrib,
    Finset.sum_neg_distrib, sub_eq_add_neg]
  simp only [mul_add, mul_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  rfl

theorem sep (σ : E →ₐ[F] E) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {d : ℕ} (JW : Matrix (Fin d) (Fin d) (AE F E))
    (hdet : IsUnit JW.det) (u : Fin d → AE F E) (h : ∀ c, ψ (pairL σ JW c u) = 1) : u = 0 := by
  classical
  funext j
  refine eq_zero_of_psi_trace hψ (u j) fun t => ?_
  have := h (Sum.elim (fun l => GlobalTheory.ArchTraceNondeg.cAinv σ ((JW⁻¹ *ᵥ Pi.single j (-t)) l)) 0)
  have hv : vdiff σ (Sum.elim (fun l => GlobalTheory.ArchTraceNondeg.cAinv σ ((JW⁻¹ *ᵥ Pi.single j (-t)) l)) 0) =
      JW⁻¹ *ᵥ Pi.single j (-t) := by
    funext l
    simp [vdiff, GlobalTheory.ArchTraceNondeg.cA_cAinv]
  rw [pairL_apply, hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec, dotProduct_single] at this
  simpa [neg_mul, mul_neg] using this

end GlobalTheory.DblSiegelChar

namespace GlobalTheory.DblSiegelChar

theorem main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d)
    (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (n₁ : ℕ) (X₁ : Spc F E n₁) (H : Plane E n n₁) (j₀ j₁ : ℕ), H.IsAdapted σ B X X₁ j₀ j₁ →
    ∃ p : (Fin d ⊕ Fin d → AE F E) → (Fin d → AE F E) →ₗ[AF F] AF F, (∀ a b, p (a + b) = p a + p b) ∧
      (∀ c u, p c u = symp (cA σ) (-1) (incM F X.J) (dbl (incM F W.J)) (GlobalTheory.DblSiegelX.zs H u) (Matrix.vecMulVec (incV F H.x) c)) ∧
      ∀ u, (∀ c, B.ψ (p c u) = 1) → u = 0 := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP n₁ X₁ H j₀ j₁ hH
  have hcm : IsCMExt F E σ := hP.base.cm
  have hψ : IsStd B.ψ := hP.base.std
  have hf : ∑ i, ∑ k, incV F H.y i * incM F X.J i k * cA σ (incV F H.x k) = 1 := by
    rw [form_inc, form_swap (invol hcm) hP.herm.herm, hH.xy, map_one, map_one]
  have hdet : IsUnit (incM F W.J).det := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h1 := GlobalTheory.ArchTraceNondeg.det_ne_zero_of_hasSig (hP.skew.sig w)
    rw [Matrix.det_smul] at h1
    have h2 : (W.J.map (B.emb w).1).det ≠ 0 := right_ne_zero_of_mul h1
    have h3 : W.J.det ≠ 0 := fun h0 => h2 (by
      have := RingHom.map_det (B.emb w).1 W.J
      rw [h0, map_zero] at this
      exact this.symm)
    have h : (incM F W.J).det = inclR (F := F) (AF F) W.J.det := by rw [RingHom.map_det]; rfl
    rw [h]
    exact (isUnit_iff_ne_zero.2 h3).map _
  exact ⟨pairL σ (incM F W.J), pairL_add σ _, fun c u => (symp_eq σ X.J W.J H hf c u).symm,
    fun u hu => sep σ hψ _ hdet u hu⟩

end GlobalTheory.DblSiegelChar
end
end

