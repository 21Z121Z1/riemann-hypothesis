import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSelfDualLatticeNormOneIdealRankOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RamifiedColumnsTrueColumnsEqConcrete
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0420
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0096
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfRangeEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0121
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CmHostRootComplexEqPmSqrt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0082
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0387

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChKerCCongr
section
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Indef GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.R3
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.SelC

section Congr

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {A A' : Amb X} (hA : ∀ (a b : ℕ) T (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) c x,
    IsSdLat N → IsSdLat N' → A.jetK T N N' c x = A'.jetK T N N' c x)

include hA in

theorem kerOf_congr (u : Pr.Word) (i : ℕ) {b : ℕ} (lam' : X.Tau → DomWeight b) (T cA cB) {N : Submodule (𝓞 X.E) (Sp X.E (R.N i))}
    {N' : Submodule (𝓞 X.E) (Sp X.E b)} (hN : IsSdLat N) (hN' : IsSdLat N') (fr fr' Ξ) :
    kerOf (stepC W Ch sel mu cst A u i lam') T cA cB N fr N' fr' Ξ = kerOf (stepC W Ch sel mu cst A' u i lam') T cA cB N fr N' fr' Ξ := by
  unfold kerOf stepC thDistC
  simp only [hA _ _ _ _ _ _ _ hN hN']

include hA in

theorem chKerC_congr (u : Pr.Word) (m2 : ℕ) (b : L.β (m2 + 1)) (hY : YbHyp (R := R) sel mu cst L u m2 b) (P : LevFam X.E X.K R.r Pr.vGs)
    (h : KerEquivC W Ch sel mu cst L A u m2 b hY P) (h' : KerEquivC W Ch sel mu cst L A' u m2 b hY P) :
    chKerC W Ch sel mu cst L A u m2 b hY P h = chKerC W Ch sel mu cst L A' u m2 b hY P h' := by
  classical
  have e1 : matK W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) = matK W Ch sel mu cst L (chTh W Ch sel mu cst A' u m2) := by
    funext i al be p p'
    exact kerOf_congr W Ch sel mu cst hA u i _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ _ _
  have e2 : cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A u m2) = cp1K W Ch sel mu cst L (chTh W Ch sel mu cst A' u m2) := by
    funext al p p' Y
    unfold cp1K
    exact if_congr Iff.rfl
      (kerOf_congr W Ch sel mu cst hA u m2 _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩ ⟨p'.deco.2.lat, p'.deco.2.uni⟩ _ _ _) rfl
  have e3 : cp2K W Ch sel mu cst (chTh W Ch sel mu cst A u m2) = cp2K W Ch sel mu cst (chTh W Ch sel mu cst A' u m2) := by
    funext p Y d
    unfold cp2K
    exact if_congr Iff.rfl
      (kerOf_congr W Ch sel mu cst hA u (m2 + 1) _ _ _ _ ⟨p.deco.2.lat, p.deco.2.uni⟩
        ⟨(tilQ sel mu u d).2.lat, (tilQ sel mu u d).2.uni⟩ _ _ _) rfl
  unfold chKerC chKer
  congr 1
  · funext i al be
    split_ifs
    · congr 1
      rw [e1]
    · rfl
  · funext al
    congr 1
    rw [e2]

end Congr

section True

open GlobalTheory.Core.Ht2 GlobalTheory.Mem.Col2.KerRat

variable {B : Base} {X : PreX B.toPre} {I : TC B X} (h : I.Ok) (hp : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
  (ht : I.IsTw) (hJ : ColIn.JetsIn I)
  (χ : Submodule (𝓞 B.host.E) B.host.E → ℂ) (hχ : ∀ 𝔞, TaylorLogMetric.N1 (I.rec7 l Z) 𝔞 → χ 𝔞 = I.chi 𝔞) (hX : B.fields.Ok)

include hχ in

theorem jetK_chi (a b : ℕ) (T) (N : Submodule (𝓞 B.fields.E) (Sp B.fields.E a)) (N' : Submodule (𝓞 B.fields.E) (Sp B.fields.E b)) (c x)
    (hN : IsSdLat N) (hN' : IsSdLat N') : (I.J.amb B χ).jetK T N N' c x = I.A.jetK T N N' c x := by
  have hf : Th.chiFac B.host χ a b N N' = Th.chiFac B.host I.chi a b N N' := by
    unfold Th.chiFac
    rw [hχ (Th.detId B.host (Th.stdL B.host _) N) (RcHyp.n1_detStd I l Z hN),
      hχ (Th.detId B.host (Th.stdL B.host _) N') (RcHyp.n1_detStd I l Z hN')]
  have e3 : (I.J.amb B χ).e a b N N' = I.A.e a b N N' := by
    show I.J.V.eNat χ _ _ N N' = I.J.V.eNat I.chi _ _ N N'
    unfold Th.VacIn.eNat
    rw [hf]
  have e4 : (I.J.amb B χ).thInd T N N' c x = I.A.thInd T N N' c x := by
    funext z
    unfold Amb.thInd
    rw [e3]
    rfl
  funext m
  unfold Amb.jetK
  rw [e4, show (I.J.amb B χ).chiF a b N N' = I.A.chiF a b N N' from hf]
  rfl

include hp ht hJ hχ in

theorem exists_cpl (u : B.Word) (a : I.ι) (cst : LocCst B.fields (rowSG (B.primes X) I.sel (I.tup a)))
    (L : ChIdx B.fields (B.primes X) B.R (I.Q a)) (e1 : cst = I.cst a) (e2 : L = I.idx a) (b : L.β (B.R.m - 2 + 1))
    (hY : YbHyp (Pr := B.primes X) (R := B.R) I.sel (I.tup a) cst L u (B.R.m - 2) b)
    (hK : KerEquivC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) cst L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps)
    (hF : ∀ j, (chF (Pr := B.primes X) B.wts I.sel (I.tup a) L u j).Ok) (hL : L.Ok I.Ch I.sel (I.tup a) cst I.glob (B.R.m - 2)) :
    ∃ c : CplData I u a, ∀ (φ : ColsK I u) (z : RowsK I a),
      PtilFF (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) I.Ps (mtildeOk (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) hX I.Ps) u
        (colC (chKerC (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) cst L (I.J.amb B χ) u (B.R.m - 2) b hY I.Ps hK) hF hL φ).1 z.1 =
        c.per h hX φ z := by
  subst e1 e2
  have hK' := (RcHyp.hyps_of_isTw I h hp l Z ht hJ I.chi (fun _ _ => rfl) a u).2.2.2 b hY
  refine ⟨⟨b, hY, hK', hF⟩, fun φ z => ?_⟩
  rw [chKerC_congr (Pr := B.primes X) B.wts I.Ch I.sel (I.tup a) (I.cst a) (I.idx a) (jetK_chi l Z χ hχ) u _ b hY I.Ps hK hK']
  rfl

theorem exists_eNu (l0 : I.Law0 l) (u : B.Word) :
    ∃ e : (Fin (ramDim (Pr := B.primes X) B.wts I.Ch hX u) → B.LL) ≃ₗ[B.LL] (Z.V.div.Nu u).V,
      (∀ v x y, Formalism.HermitianLatticesTheory.majAt (Z.V.div.Nu u).b (Z.V.div.Nu u).X v (e x) (e y) =
        Formalism.HermitianLatticesTheory.majAt (Pi.basisFun B.LL _) (MramH (Pr := B.primes X) B.wts I.Ch hX u).X v x y) ∧
      ∀ x, Z.V.nuIn u (e x) = colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) := by
  obtain ⟨eM, hs, -, hn, -⟩ := GlobalTheory.AtG.ramCols_true I h l Z l0 u
  let eL : (Z.V.div.Nu u).V ≃ₗ[B.LL] MramV (Pr := B.primes X) B.wts I.Ch u := { eM with map_smul' := hs }
  let bs := ramBas (Pr := B.primes X) B.wts I.Ch hX u
  have hin : ∀ x, Z.V.nuIn u ((bs.equivFun.symm.trans eL.symm) x) =
      colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) := fun x =>
    (hn _).trans (congrArg (fun φ : MramV (Pr := B.primes X) B.wts I.Ch u => colForm I l h u I.mu0 φ.1) (eL.apply_symm_apply _))
  refine ⟨bs.equivFun.symm.trans eL.symm, fun v x y => ?_, hin⟩
  haveI : IsTotallyComplex B.LL := hX.cplxK
  refine GlobalTheory.Mem.RowSides.majAt_eq_of_normAt _ _ _ _ v (bs.equivFun.symm.trans eL.symm).toLinearMap (fun x => congrArg (· ^ 2) ?_) x y
  refine (Z.V.nuIn_norm u v _).trans ?_
  rw [LinearEquiv.coe_coe, hin]
  refine (GlobalTheory.Core.ColNorm.nrm_stepZero_eq I h hX l u I.mu0 _ (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x) (fun _ => rfl) v).trans ?_
  refine (ramInclH_norm (Pr := B.primes X) B.wts I.Ch hX u v (bs.equivFun.symm x)).symm.trans ?_
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord Formalism.HermitianLatticesTheory.vecAt
  congr 2
  funext i
  exact congrArg v.embedding (congrFun (bs.equivFun.apply_symm_apply x) i)

include hJ in

theorem perCol_eq (l0 : I.Law0 l) (e : ∀ a : (I.cols l).Tup, Df.MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (h0 : ∀ u F, Df.SameForm I l u I.mu0 F ((Z.W.eMt0 u).symm (e (I.cols l).mu0 F)))
    (h1 : ∀ u (a : (I.cols l).Tup) F, Df.SameForm I l u a F ((Z.W.eMtTw u a).symm (e a F)))
    (u : B.Word) (a : I.ι) (c : CplData I u a) (n : (Z.V.div.Nu u).V) (φ : ColsK I u) (hn : Z.V.nuIn u n = colForm I l h u I.mu0 φ)
    (z : RowsK I a) : Z.W.perCol u a (Z.V.jN u n) (e a (Df.toCx I hX a z)) = B.embLL (c.per h hX φ z) := by
  obtain ⟨-, -, -, -, hT⟩ := GlobalTheory.AtG.ramCols_true I h l Z l0 u
  have hM := (colMatchAll I h hX l Z hJ u a).2 c (colForm I l h u a φ) φ
  have hj := (Z.V.nuIn_jN u n).trans (congrArg ((I.fm l u I.mu0).emb 0) hn)
  by_cases ha : a = I.mu0
  · subst ha
    refine (Z.W.perCol_base_eq_PtilCol u _ _).trans ?_
    rw [hj]
    exact hM _ z (fun _ => rfl) fun p => h0 u _ p
  · refine (Z.W.perCol_tie u a ha _ _).trans ?_
    rw [hj, ← hT a φ]
    exact hM _ z (fun _ => rfl) fun p => h1 u a _ p

set_option maxHeartbeats 1000000 in

theorem face_pt (l0 : I.Law0 l) (e : ∀ a : (I.cols l).Tup, Df.MtCx I a ≃ₗ[ℂ] Z.W.Amb a)
    (h0 : ∀ u F, Df.SameForm I l u I.mu0 F ((Z.W.eMt0 u).symm (e (I.cols l).mu0 F)))
    (h1 : ∀ u (a : (I.cols l).Tup) F, Df.SameForm I l u a F ((Z.W.eMtTw u a).symm (e a F)))
    (U : Set I.ι) (Xg : Finset (Gc B X → B.LL)) (tr : TrI B X)
    (Zs : DefSub (famC I hX U Xg tr).fam3.amb3) (u : B.Word) (a : I.ι) (ha) (x : Fin (ramDim (Pr := B.primes X) B.wts I.Ch hX u) → B.LL)
    (n : (Z.V.div.Nu u).V) (hn : Z.V.nuIn u n = colForm I l h u I.mu0 (colOfCoord (Pr := B.primes X) B.wts I.Ch hX u x))
    (f : Fin (((famC I hX U Xg tr).side3 (lev1 I) (chr1 I) Zs).nV ⟨I.tup a, ha⟩) → B.LL) (z : RowsK I a)
    (hz : z.1 = ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).ev Zs ⟨I.tup a, ha⟩ f).1.1) :
    B.embLL (((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).face Zs).Pt u ⟨I.tup a, ha⟩ x f) =
      Z.W.perCol u a (Z.V.jN u n) (e a (Df.toCx I hX a z)) := by
  obtain ⟨c, hc⟩ := exists_cpl h hp l Z ht hJ χ hχ hX u a _ _ (cstT_tup ht a) (idxT_tup ht a)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).b ⟨I.tup a, ha⟩ u) ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hY ⟨I.tup a, ha⟩ u)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hK ⟨I.tup a, ha⟩ u) ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hF ⟨I.tup a, ha⟩ u)
    ((colRecC h hp l Z ht hJ χ hχ hX U Xg tr).hL ⟨I.tup a, ha⟩)
  rw [perCol_eq h l Z hJ hX l0 e h0 h1 u a c n _ hn z, ← hc, hz]
  rfl

end True

end GlobalTheory.Mem.R3.SelC

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComplexPointsBaseLevelLiftReadAtBaseEmbedding
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.LiftForms

theorem exists_mat {K K' : Type} [Field K] [Field K'] (φ : K →+* K') {n n' : ℕ} (hn : n = n')
    (V : Submodule K (Fin n → K)) (V' : Submodule K' (Fin n' → K'))
    (hV : V' = Submodule.span K' {x' | ∃ x ∈ V, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    ∃ G : Matrix (Fin (Module.finrank K' V')) (Fin (Module.finrank K V)) K', Function.Bijective G.mulVec ∧
      ∀ y : Fin (Module.finrank K V) → K, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' →
        (∑ l, (G.mulVec (fun i => φ (y i))) l • (Module.finBasis K' V' l : Fin n' → K')) k' =
          φ ((∑ i, y i • (Module.finBasis K V i : Fin n → K)) k) := by
  subst hn
  classical
  set b := Module.finBasis K V
  set Φ : (Fin n → K) → (Fin n → K') := fun x k => φ (x k) with hΦ
  have hrel : ∀ x' : Fin n → K', ∀ x : Fin n → K, (∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)) ↔ x' = Φ x := by
    intro x' x
    constructor
    · intro h; funext k; exact h k k rfl
    · rintro rfl k k' hk; rw [Fin.ext hk]
  have hS : {x' | ∃ x ∈ V, ∀ (k k' : Fin n), (k : ℕ) = k' → x' k' = φ (x k)} = Φ '' V := by
    ext x'; simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨x, hx, h⟩; exact ⟨x, hx, ((hrel x' x).1 h).symm⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (hrel _ x).2 rfl⟩
  rw [hS] at hV
  have hΦadd : ∀ x y, Φ (x + y) = Φ x + Φ y := fun x y => by funext k; simp [hΦ]
  have hΦsmul : ∀ (a : K) x, Φ (a • x) = φ a • Φ x := fun a x => by funext k; simp [hΦ]
  have hΦsum : ∀ y : Fin (Module.finrank K V) → K, Φ (∑ i, y i • (b i : Fin n → K)) = ∑ i, φ (y i) • Φ (b i) := by
    intro y
    funext k
    simp [hΦ, Finset.sum_apply, map_sum]
  let c : Fin (Module.finrank K V) → Fin n → K' := fun i => Φ (b i)
  have hc_mem : ∀ i, c i ∈ V' := fun i => hV ▸ Submodule.subset_span ⟨b i, (b i).2, rfl⟩
  have hli : LinearIndependent K' c := by
    letI := φ.toAlgebra
    have h0 : LinearIndependent K (fun i => (b i : Fin n → K)) := b.linearIndependent.map' V.subtype V.ker_subtype
    exact (linearIndependent_algebraMap_comp_iff).2 h0
  have hspan : Submodule.span K' (Set.range c) = V' := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hc_mem i
    · rw [hV, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      have hx' : (⟨x, hx⟩ : V) = ∑ i, (b.repr ⟨x, hx⟩ i) • b i := (b.sum_repr _).symm
      have hx2 : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Fin n → K) := by
        have := congrArg Subtype.val hx'
        rw [Submodule.coe_sum] at this
        simpa only [Submodule.coe_smul] using this
      rw [hx2, hΦsum]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  let cV : Fin (Module.finrank K V) → V' := fun i => ⟨c i, hc_mem i⟩
  have hliV : LinearIndependent K' cV := LinearIndependent.of_comp V'.subtype hli
  have hspV : ⊤ ≤ Submodule.span K' (Set.range cV) := by
    rintro ⟨x, hx⟩ _
    rw [← hspan] at hx
    have : Set.range c = V'.subtype '' Set.range cV := by
      ext z; simp [cV, c]
    rw [this, ← Submodule.map_span] at hx
    obtain ⟨w, hw, hwx⟩ := hx
    have : w = ⟨x, hspan ▸ (by rw [this, ← Submodule.map_span]; exact ⟨w, hw, hwx⟩)⟩ := Subtype.ext hwx
    rw [← this]; exact hw
  let bc : Module.Basis (Fin (Module.finrank K V)) K' V' := Module.Basis.mk hliV hspV
  set b' := Module.finBasis K' V'
  refine ⟨Matrix.of fun l i => b'.repr (bc i) l, ?_, ?_⟩
  · have hG : (Matrix.of fun l i => b'.repr (bc i) l).mulVec = fun y => b'.equivFun (bc.equivFun.symm y) := by
      funext y l
      simp [Matrix.mulVec, dotProduct, Module.Basis.equivFun_symm_apply, map_sum, mul_comm]
    rw [hG]
    exact b'.equivFun.bijective.comp bc.equivFun.symm.bijective
  · intro y k k' hk
    rw [← Fin.ext hk]
    have e1 : (∑ l, ((Matrix.of fun l i => b'.repr (bc i) l).mulVec (fun i => φ (y i))) l • (b' l : Fin n → K')) =
        ((∑ i, φ (y i) • bc i : V') : Fin n → K') := by
      have : ∑ l, ((Matrix.of fun l i => b'.repr (bc i) l).mulVec (fun i => φ (y i))) l • b' l = ∑ i, φ (y i) • bc i := by
        rw [← b'.sum_repr (∑ i, φ (y i) • bc i)]
        congr 1; funext l; congr 1
        simp [Matrix.mulVec, dotProduct, map_sum, mul_comm]
      have := congrArg Subtype.val this
      simpa [Submodule.coe_sum] using this
    rw [e1]
    have e2 : ((∑ i, φ (y i) • bc i : V') : Fin n → K') = ∑ i, φ (y i) • c i := by
      simp [Submodule.coe_sum, bc, cV]
    rw [e2, ← hΦsum]

theorem lat_coords {K K' : Type} [Field K] [Field K'] [NumberField K] [NumberField K'] (φ : K →+* K') {n n' d d' : ℕ}
    (hn : n = n') (b : Fin d → Fin n → K) (b' : Fin d' → Fin n' → K') (hb' : LinearIndependent K' b')
    (G : Matrix (Fin d') (Fin d) K')
    (hG : ∀ y : Fin d → K, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' →
        (∑ l, (G.mulVec (fun i => φ (y i))) l • b' l) k' = φ ((∑ i, y i • b i) k))
    (M : Submodule (𝓞 K) (Fin n → K)) (hM : ∀ x ∈ M, x ∈ Submodule.span K (Set.range b))
    (M' : Submodule (𝓞 K') (Fin n' → K'))
    (hM' : M' = Submodule.span (𝓞 K') {x' | ∃ x ∈ M, ∀ (k : Fin n) (k' : Fin n'), (k : ℕ) = k' → x' k' = φ (x k)}) :
    M'.comap ((Fintype.linearCombination K' b').restrictScalars (𝓞 K')) =
      Submodule.span (𝓞 K') ((fun y : Fin d → K => G.mulVec fun i => φ (y i)) ''
        (M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) : Set (Fin d → K))) := by
  subst hn
  set L' := (Fintype.linearCombination K' b').restrictScalars (𝓞 K') with hL'
  have hL'apply : ∀ c, L' c = ∑ l, c l • b' l := fun c => by
    simp [hL', Fintype.linearCombination_apply]
  have key : ∀ y : Fin d → K, L' (G.mulVec fun i => φ (y i)) = fun k => φ ((∑ i, y i • b i) k) := by
    intro y; funext k; rw [hL'apply]; exact hG y k k rfl
  have hinj : Function.Injective L' := by
    intro c₁ c₂ h
    rw [hL'apply, hL'apply] at h
    have h0 : ∑ l, (c₁ - c₂) l • b' l = 0 := by
      simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, h, sub_self]
    funext l
    exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb' _ h0 l)
  apply le_antisymm
  · intro c hc
    have hc' : L' c ∈ M' := hc
    have hle : M' ≤ (Submodule.span (𝓞 K') ((fun y : Fin d → K => G.mulVec fun i => φ (y i)) ''
        (M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) : Set (Fin d → K)))).map L' := by
      rw [hM', Submodule.span_le]
      rintro x' ⟨x, hx, hrel⟩
      obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hM x hx)
      have hyM : y ∈ M.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K)) := by
        show (Fintype.linearCombination K b) y ∈ M
        rw [Fintype.linearCombination_apply, hy]; exact hx
      have : x' = L' (G.mulVec fun i => φ (y i)) := by
        rw [key y, hy]; funext k; exact hrel k k rfl
      rw [this]
      exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨y, hyM, rfl⟩)
    obtain ⟨e, he, hec⟩ := hle hc'
    rw [← hinj hec]; exact he
  · rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    show L' (G.mulVec fun i => φ (y i)) ∈ M'
    rw [hM', key y]
    refine Submodule.subset_span ⟨∑ i, y i • b i, ?_, fun k k' hk => by rw [Fin.ext hk]⟩
    have : (Fintype.linearCombination K b) y ∈ M := hy
    rwa [Fintype.linearCombination_apply] at this

theorem complexPoints_baseLevelLift_readAtBaseEmbedding {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (i : Fin D.R.m)
    (y : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) :
    @Tw.out (twAt D.what₂.embLL A3.A.v0) _ ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y)) =
      (R.FW i).j (sg0 D A3.A) (∑ k, y k • R.toRealDat.bL F.lv2 false i k) := by
  have hpos : (0:ℝ) < RealDat.nP F.lv2 false := by
    unfold RealDat.nP; exact_mod_cast Nat.card_pos
  set s := twAt D.what₂.embLL A3.A.v0
  set WS := R.toRealDat.WS F.lv2 false i (sg0 D A3.A)
  have h2 : (@Tw.out s WS ((R.toCx3 F).wC false i A3.fam3.base3.v0 (cpt A3.fam3.base3.v0.embedding y))) =
      ∑ k, cj s (cpt A3.fam3.base3.v0.embedding y k) • (⟨R.toRealDat.bC F.lv2 false i (sg0 D A3.A) k, Submodule.subset_span ⟨k, rfl⟩⟩ : WS) := by
    simp only [CxData.wC, lin, Fintype.linearCombination_apply]
    rfl
  have h1 : ∀ x : Tw s WS, @Tw.out s _ ((R.toCx3 F).eW false i x) = (((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ)) • ((Tw.out x : WS) : (R.HW i (sg0 D A3.A)).H) := fun x => rfl
  refine Eq.trans (h1 ((R.toCx3 F).wC false i A3.fam3.base3.v0 (cpt A3.fam3.base3.v0.embedding y))) ?_
  rw [h2, Submodule.coe_sum, Finset.smul_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul, map_smulₛₗ, smul_comm]
  have he : cj s (cpt A3.fam3.base3.v0.embedding y k) = sg0 D A3.A (y k) := by
    show cj s (A3.A.v0.embedding (y k)) = _
    rw [emb_eq D.what₂.embLL A3.A.v0 (y k), cj_cj]
  rw [he]
  congr 1
  show ((Real.sqrt (RealDat.nP F.lv2 false) : ℝ) : ℂ) • ((((Real.sqrt (RealDat.nP F.lv2 false))⁻¹ : ℝ) : ℂ) • (R.FW i).j (sg0 D A3.A) (R.toRealDat.bL F.lv2 false i k)) = _
  rw [smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (Real.sqrt_pos.2 hpos).ne', Complex.ofReal_one, one_smul]

theorem liftWeight_complexPoint_eq_twist {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (i : Fin D.R.m)
    (y : Fin ((R.toCx3 F).dW false i) → D.what₂.LL) :
    HEq ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y))
      ((R.FW i).j D.what₂.embLL (∑ k, y k • R.toRealDat.bL F.lv2 false i k)) := by
  have e := complexPoints_baseLevelLift_readAtBaseEmbedding R F i y
  have hs : sg0 D A3.A = D.what₂.embLL := sgAt_mk _ R.hv0
  have key : ∀ (σ σ' : D.what₂.LL →+* ℂ), σ = σ' → ∀ v, HEq ((R.FW i).j σ v) ((R.FW i).j σ' v) := by
    intro σ σ' h v; subst h; rfl
  show HEq (@Tw.out (twAt D.what₂.embLL A3.A.v0) _ ((R.toCx3 F).w0C false i (cpt A3.fam3.base3.v0.embedding y))) _
  rw [e]
  exact key _ _ hs _

theorem nat_eq_of_heq {m m' : ℕ} (hm : m' = m) {f : Fin m → ℕ} {f' : Fin m' → ℕ} (h : HEq f' f) (i : Fin m) (i' : Fin m')
    (hi : (i : ℕ) = i') : f i = f' i' := by
  subst hm
  have := eq_of_heq h
  subst this
  rw [Fin.ext hi]

theorem mem_span_basis {K : Type} [Field K] {n : ℕ} (V : Submodule K (Fin n → K)) [Module.Finite K V] {x : Fin n → K}
    (hx : x ∈ V) : x ∈ Submodule.span K (Set.range fun k => (Module.finBasis K V k : Fin n → K)) := by
  have hx' : (⟨x, hx⟩ : V) = ∑ i, ((Module.finBasis K V).repr ⟨x, hx⟩ i) • Module.finBasis K V i := ((Module.finBasis K V).sum_repr _).symm
  have hx2 : x = ∑ i, ((Module.finBasis K V).repr ⟨x, hx⟩ i) • (Module.finBasis K V i : Fin n → K) := by
    have := congrArg Subtype.val hx'
    rw [Submodule.coe_sum] at this
    simpa only [Submodule.coe_smul] using this
  rw [hx2]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory.Mem.R3.LiftForms

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoverFieldOfWeberLev
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting NumberField IsDedekindDomain
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.FieldSize GlobalTheory.FinalJoin
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl.CoverAt

theorem exists_finset_weberIn (r : ℂ) (M : ℕ) (hM : M ≠ 0) : ∃ S : Finset ℂ, (∀ z ∈ S, IsAlgebraic ℚ z) ∧
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), H.rt0 = r →
      ∀ F : IntermediateField ℚ ℂ, (∀ z ∈ S, z ∈ F) → WeberIn H F M := by
  by_cases h : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), H.rt0 = r
  · obtain ⟨E₀, _, _, _, H₀, h₀⟩ := h
    obtain ⟨L₀, hL₀⟩ := GlobalTheory.FinalJoin.CurveField.exists_periodPair H₀
    obtain ⟨hfin, halg, -⟩ := weberSet_finite_algebraic_permuted L₀ M (Nat.pos_of_ne_zero hM)
      (GlobalTheory.CompRat.Weber.g₂_ne_zero H₀ L₀ hL₀) (GlobalTheory.CompRat.Weber.g₃_ne_zero H₀ L₀ hL₀)
    refine ⟨hfin.toFinset, fun z hz => halg (GlobalTheory.WeberField.invariant_isAlgebraic H₀ L₀ hL₀) z (hfin.mem_toFinset.1 hz), ?_⟩
    intro E _ _ _ H hH F hF L hL
    have hw : ∀ s, GlobalTheory.CompRat.wC H s = GlobalTheory.CompRat.wC H₀ s := fun s => by
      unfold GlobalTheory.CompRat.wC
      rw [hH, h₀]
    have e : weberSet L M = weberSet L₀ M :=
      GlobalTheory.FieldSize.SmallField.weberSet_congr (Submodule.ext fun z => by
        rw [hL z, hL₀ z]
        simp only [hw]) M
    have hs : ∀ z ∈ weberSet L M, z ∈ F := fun z hz => hF z (hfin.mem_toFinset.2 (e ▸ hz))
    exact ⟨hs _ (Set.mem_insert _ _), fun s hs' => hs _ (Set.mem_insert_of_mem _ ⟨_, (hL _).2 ⟨s, rfl⟩, hs', rfl⟩)⟩
  · exact ⟨∅, by simp, fun E _ _ _ H hH => absurd ⟨E, _, _, _, H, hH⟩ h⟩

open Classical in

def WeberLev (B : Base) (f : Fr B.toPre) (T : TwDat B) : Prop :=
  ∀ S : Finset (HeightOneSpectrum (𝓞 B.host.E)), (∀ Q ∈ S, ∃ χ ∈ T.set f, ¬ χ.UnrAt Q) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
      H.rt0 = B.host.φ₀ B.host.sqrtMinusD →
      WeberIn H B.LLC (B.host.g 0 * B.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q)

open Classical in

theorem lg_weberLev (K : Ctx) : large₂ K WeberLev := by
  have h : ∀ (P : Pre) (Ξ : Set (HChar P.host.E)), ∃ Z : Finset ℂ, (∀ z ∈ Z, IsAlgebraic ℚ z) ∧
      ({Q : HeightOneSpectrum (𝓞 P.host.E) | ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}.Finite →
        ∀ S : Finset (HeightOneSpectrum (𝓞 P.host.E)), (∀ Q ∈ S, ∃ χ ∈ Ξ, ¬ χ.UnrAt Q) →
        ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
          H.rt0 = P.host.φ₀ P.host.sqrtMinusD → ∀ F : IntermediateField ℚ ℂ, (∀ z ∈ Z, z ∈ F) →
          WeberIn H F (P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q)) := by
    intro P Ξ
    have hne : ∀ S : Finset (HeightOneSpectrum (𝓞 P.host.E)),
        P.host.g 0 * P.host.g 1 * ∏ q ∈ S.image (fun Q => Nat.card (kP Q)), q ≠ 0 := fun S => by
      refine mul_ne_zero (mul_ne_zero (P.host.g_prime 0).ne_zero (P.host.g_prime 1).ne_zero) ?_
      rw [Finset.prod_ne_zero_iff]
      intro q hq
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.1 hq
      exact GlobalTheory.Plug.TwistLevels.card_residueField_ne_zero Q
    choose Z hZ hZ' using fun S => exists_finset_weberIn (P.host.φ₀ P.host.sqrtMinusD) _ (hne S)
    by_cases hA : {Q : HeightOneSpectrum (𝓞 P.host.E) | ∃ χ ∈ Ξ, ¬ χ.UnrAt Q}.Finite
    · refine ⟨hA.toFinset.powerset.biUnion Z, fun z hz => ?_, fun _ S hS E _ _ _ H hH F hF => ?_⟩
      · obtain ⟨S, -, hz⟩ := Finset.mem_biUnion.1 hz
        exact hZ S z hz
      · exact hZ' S E H hH F fun z hz => hF z (Finset.mem_biUnion.2
          ⟨S, Finset.mem_powerset.2 fun Q hQ => hA.mem_toFinset.2 (hS Q hQ), hz⟩)
    · exact ⟨∅, by simp, fun h => absurd h hA⟩
  choose Z hZ hZ' using h
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun P _ _ _ Ξ => Z P Ξ, by simp,
    fun P _ _ _ Ξ => hZ P Ξ, fun B f T _ hH _ _ S hS E _ _ _ H hr => ?_⟩
  refine hZ' B.toPre (T.set f) ?_ S hS E H hr _ hH.2
  refine ((GlobalTheory.Mem.Top.TwFin.tw_fin B f T).1.biUnion fun χ hχ => GlobalTheory.Plug.TwistLevels.ram_finite B f T χ hχ).subset ?_
  rintro Q ⟨χ, hχ, hr⟩
  exact Set.mem_biUnion (x := χ) hχ hr

set_option maxHeartbeats 1000000 in

theorem coverField_of_weberLev {B : Base} {f : Fr B.toPre} {T : TwDat B} (hW : WeberLev B f T) (w : ColW B f T) (Z : w.Lt)
    (hX : B.fields.Ok) (Wt : Set B.places.Pl) (z : R3.Dat (w.st Z) w.I hX T Wt) :
    GlobalTheory.TwistField.CoverField z.core z.R.toRealDat := by
  intro i t l₂ _ hM hA Xo₂ c₂ hc
  have hP : z.core.Q.Pins := z.geo.fw.laws.pins
  have hS : ∀ Q ∈ z.R.Q t, ∃ χ ∈ T.set f, ¬ χ.UnrAt Q := fun Q hQ =>
    ⟨z.R.xiH t, by
      rw [z.lev.xiH t, ← w.xi_range]
      exact ⟨_, rfl⟩, (z.lev.is.Q_ram t Q).2 (Or.inl hQ)⟩
  have hw := hW (z.R.Q t) hS _ z.core.Q.H hP.1.2.2.1
  have hlev : l₂.M = B.host.g 0 * B.host.g 1 * GlobalTheory.TwistField.tupPrime z.R.toRealDat t := by
    rw [hM, show z.core.Q.l.M = _ from hP.2.1.1]
    rfl
  have hw' : WeberIn z.core.Q.H c₂.F l₂.M := by
    rw [hlev, hc]
    exact hw
  refine GlobalTheory.FinalJoin.FieldAlg.fnAlgClosed_of_weberIn _ z.core.Q hP ((i : ℕ) + 1) ⟨Nat.succ_le_succ (Nat.zero_le _), i.2⟩ l₂ Xo₂ c₂
    l₂.M (lt_of_lt_of_le (by norm_num) l₂.three_le) ?_ (Or.inl hw')
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level.M', hA, Nat.lcm_one_right]

end GlobalTheory.Mem.Top.Bl.CoverAt

end
end

