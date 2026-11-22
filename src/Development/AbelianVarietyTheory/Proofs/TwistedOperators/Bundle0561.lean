import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0543
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0751
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.JointSmooth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0389
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0395
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0393
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0011
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatSelf
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0537
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0227
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0252
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0288
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0524
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0519
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousReprSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0241
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0499
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0525
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0428

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormJets
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.FunObj

noncomputable section

namespace GlobalTheory.NFJetProof

theorem exists_nf_of_finite (E : Set ℂ) (hE : E.Finite) (hA : ∀ z ∈ E, IsAlgebraic ℚ z) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ E ⊆ Set.range (algebraMap M ℂ) := by
  haveI : Finite E := hE.to_subtype
  refine ⟨IntermediateField.adjoin ℚ E, IntermediateField.finiteDimensional_adjoin fun z hz => (hA z hz).isIntegral,
    fun z hz => ⟨⟨z, IntermediateField.subset_adjoin ℚ E hz⟩, rfl⟩⟩

def dset {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (t : T) (Φ : G.Datum) (β : CosFam G t) (k : ℕ) : Set (PureDat G t) :=
  {d | ∃ τ, IsCosetExpansion S t Φ β k τ ∧ d ∈ τ.support}

end GlobalTheory.NFJetProof

namespace GlobalTheory.NFJetProof

theorem jetCl_of_choice {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (large₂ : SizeData₂ D) (F : Face D A)
    (hS : HidaSetting large₂ R F) (ch : Choice R) (hch : ch.Is) (hI : GlobalTheory.NormSum.Inp D) (hok : ∀ t a, ch.S.SumOK t (ch.Phi a))
    (hD : GlobalTheory.SumSize.DictAt ch) : InNF fun _ σ => JetCl σ ch.S.toGridChoice := by
  have hok' : ∀ t Φ, ch.S.SumOK t Φ := fun t Φ => by
    obtain ⟨a, rfl⟩ := GlobalTheory.T.rowTestChoice_datum_surjective large₂ F hS ch hch Φ
    exact hok t a
  haveI : Finite T := hS.fin
  haveI : Finite ch.G.Datum := Finite.of_surjective ch.Phi fun Φ => GlobalTheory.T.rowTestChoice_datum_surjective large₂ F hS ch hch Φ
  set S := ch.S.toGridChoice with hSdef
  let E : Set ℂ := ⋃ t, ⋃ Φ, ⋃ β ∈ S.supp t Φ, ⋃ d ∈ dset S t Φ β (expDepth S t Φ β), ⋃ c : S.Classes t Φ β,
    ((⋃ j : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.1 j) (S.ptTop c j) (S.ptTop c (j + 1)) a b}) ∪
      (⋃ i : Fin D.R.m, ⋃ a, ⋃ b, {S.Z.kk (d.2 i) (S.ptRow c i) (S.ptRow c (i + 1)) a b}))
  have hE : E.Finite := by
    refine Set.finite_iUnion fun t => Set.finite_iUnion fun Φ => Set.Finite.biUnion (hok' t Φ).fin fun β _ =>
      Set.Finite.biUnion (GlobalTheory.T.finite_pureData_of_cosetIndicatorExpansions_depth S t Φ β _) fun d _ => ?_
    haveI := (hok' t Φ).cls β
    exact Set.finite_iUnion fun c => Set.Finite.union
      (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _)
      (Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_iUnion fun _ => Set.finite_singleton _)
  have hA : ∀ z ∈ E, IsAlgebraic ℚ z := by
    intro z hz
    simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop] at hz
    obtain ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hdτ⟩, c, h⟩ := hz
    obtain ⟨hk, hexp, hcos⟩ := hτ
    obtain ⟨e, -, hP, -⟩ := id hexp
    have hw := (hok' t Φ).wts
    have hv := (hok' t Φ).vec β τ hexp d hdτ
    rcases h with ⟨j, a, b, rfl⟩ | ⟨i, a, b, rfl⟩
    · exact GlobalTheory.T.normalisedDefiniteKernel_entries_isAlgebraic large₂ F hS ch hch hI hD t (.top t j) (show (j : ℕ) + 1 ≤ D.R.m from j.2) (hw j j.2).1 _ (d.1 j) hk
        ((hcos d hdτ).1 j) ((hP d hdτ).1 j).2.2 ((hP d hdτ).1 j).1 (hv.1 j) _ _ a b
    · exact GlobalTheory.T.normalisedDefiniteKernel_entries_isAlgebraic large₂ F hS ch hch hI hD t (.chi i D.R.m) (show (i : ℕ) + 1 ≤ D.R.m ∧ D.R.m = D.R.m from ⟨i.2, rfl⟩) (hw i i.2).2 _
        (d.2 i) hk ((hcos d hdτ).2 i) ((hP d hdτ).2 i).2.2 ((hP d hdτ).2 i).1 (hv.2 i) _ _ a b
  obtain ⟨M, hM, hsub⟩ := exists_nf_of_finite E hE hA
  refine ⟨M, hM, fun t Φ β hβ τ hτ d hd c => ⟨fun j a b => hsub ?_, fun i a b => hsub ?_⟩⟩
  · simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inl ⟨j, a, b, rfl⟩⟩
  · simp only [E, dset, Set.mem_iUnion, Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq, exists_prop]
    exact ⟨t, Φ, β, hβ, d, ⟨τ, hτ, hd⟩, c, Or.inr ⟨i, a, b, rfl⟩⟩

theorem nfJet_holds : SumOKK → (∀ D, GlobalTheory.NormSum.Inp D) → (Big fun ch => GlobalTheory.SumSize.DictAt ch) → NFJet := by
  intro h1 h2 h3
  obtain ⟨C, hC⟩ := Big.and h1 h3
  refine ⟨C, fun ε CF hCF => ?_⟩
  obtain ⟨x, hx⟩ := hC ε CF hCF
  exact ⟨x, fun D large₂ he hxx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc =>
    jetCl_of_choice large₂ F hS ch hch (h2 D) (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).1
      (hx D large₂ he hxx Γ Pl0 T A Ks R F hS ch hch hsc).2⟩

end GlobalTheory.NFJetProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorAddStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedKernelOfVector_add : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) {f f' : WO (G.pS p) (G.pT p) → ℂ},
    IsThetaFunO W.ψ _ _ f → IsThetaFunO W.ψ _ _ f' → ∀ (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (f + f') x y = kkVec S p f x y + kkVec S p f' x y := by
  first | exact @GlobalTheory.TopZeroInv.kkVec_add | exact GlobalTheory.TopZeroInv.kkVec_add | (intros; apply GlobalTheory.TopZeroInv.kkVec_add <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedKernelOfVectorSmulStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.TopZeroInv
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedKernelOfVector_smul : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) (p : Pair T) (c : ℂ) (f : WO (G.pS p) (G.pT p) → ℂ) (x : FinPt G p.small) (y : FinPt G p.big),
    kkVec S p (c • f) x y = c • kkVec S p f x y := by
  first | exact @GlobalTheory.TopZeroInv.kkVec_smul | exact GlobalTheory.TopZeroInv.kkVec_smul | (intros; apply GlobalTheory.TopZeroInv.kkVec_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedThetaEqFiniteHeisenbergTranslatesVacua
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum NumberField
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinDecomp

open GlobalTheory.PlaceModel GlobalTheory.SeeSaw

variable {D : D7} {S T : HSp D}

theorem comb_eq_linearCombination (ψ : AddChar (AF D.host.F) ℂ) (c : WO S T →₀ ℂ) (f : WO S T → ℂ) :
    comb ψ S T c f = Finsupp.linearCombination ℂ (fun u => heisO ψ S T u f) c := by
  rw [Finsupp.linearCombination_apply]; rfl

theorem comb_sum_single {ι : Type} [Fintype ι] (ψ : AddChar (AF D.host.F) ℂ) (x : ι → WO S T) (a : ι → ℂ)
    (f : WO S T → ℂ) :
    comb ψ S T (∑ i, Finsupp.single (x i) (a i)) f = ∑ i, a i • heisO ψ S T (x i) f := by
  rw [comb_eq_linearCombination, map_sum]
  exact Finset.sum_congr rfl fun i _ => Finsupp.linearCombination_single _ _ _

theorem isFinComb_sum_single {ι : Type} [Fintype ι] (x : ι → WO S T) (a : ι → ℂ)
    (hx : ∀ i, (x i).map (infPart D) = 0) : IsFinComb (∑ i, Finsupp.single (x i) (a i)) := by
  classical
  intro u hu
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (Finsupp.support_finset_sum hu)
  rw [Finset.mem_singleton.1 (Finsupp.support_single_subset hi)]
  exact hx i

theorem map_infPart_add_neg {x y : WO S T} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + -y).map (infPart D) = 0 := by
  ext i j
  have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
  show infPart D (x i j + -y i j) = 0
  rw [map_add, map_neg, h1, h2, neg_zero, add_zero]

theorem symplO_neg_right (x y : WO S T) : symplO S T x (-y) = -symplO S T x y := by
  have h := symplO_add_right S T x y (-y)
  rw [add_neg_cancel, symplO_zero_right] at h
  linear_combination -h

theorem symplO_self (x : WO S T) : symplO S T x x = 0 := by
  have h := symplO_skew S T x x
  have hh := half_mul_two D
  linear_combination (algebraMap D.host.F (AF D.host.F) (1 / 2)) * h - symplO S T x x * hh

theorem heisL_cancel (ψ : AddChar (AF D.host.F) ℂ) (x : WO S T) (f : WO S T → ℂ) :
    heisL S T ψ x (heisL S T ψ (-x) f) = f := by
  rw [heisL_heisL, symplOH, symplO_neg_right, symplO_self, neg_zero, mul_zero, AddChar.map_zero_eq_one, one_smul,
    add_neg_cancel]
  funext w
  change ψ (symplOH S T w 0) * f (w + 0) = f w
  rw [symplOH, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one, one_mul, add_zero]

theorem lamE_two_nsmul {ψ : AddChar (AF D.host.F) ℂ} {Λ : AddSubgroup (WO S T)} {e : AE D}
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1) (he : ∀ u ∈ Λ, e • u ∈ Λ) (hc : ∀ u ∈ Λ, cA D e • u ∈ Λ)
    {u : WO S T} (hu : u ∈ Λ) : lamE ψ S T e (2 • u) = 1 := by
  have h := hΛ _ (he u hu) _ (hc _ (Λ.nsmul_mem hu 2))
  rw [← h]
  unfold lamE symplOH
  congr 1
  rw [two_nsmul u, smul_add e, symplO_add_left]
  have hh := half_mul_two D
  linear_combination (symplO S T (e • u) (cA D e • (u + u))) * hh

theorem lamE_half {ψ : AddChar (AF D.host.F) ℂ} (e : AE D) {e' : AE D} (he' : e' * cA D e' = 0) {u : WO S T}
    (hu : IsHalf e' u) : lamE ψ S T e u = 1 := by
  have h : e' • u = u := (isHalf_iff S T).1 hu
  have h1 : e • u = e' • (e • u) := by rw [smul_comm, h]
  have h2 : cA D e' • (cA D e • u) = 0 := by
    rw [smul_comm, ← h, smul_smul (cA D e'), mul_comm, he', zero_smul, smul_zero]
  unfold lamE symplOH
  rw [h1, symplO_smul, h2, symplO_zero_right, mul_zero, AddChar.map_zero_eq_one]

theorem finite_Qm {V : Type} [AddCommGroup V] {Λ : AddSubgroup V} {m : ℕ} {R : Set V} (hR : R.Finite)
    (h : ∀ t ∈ Λ, ∃ r ∈ R, ∃ u ∈ Λ, t = r + m • u) : Finite (Qm m Λ) := by
  classical
  haveI : Finite R := hR
  refine Finite.of_surjective
    (fun r : R => if hr : (r : V) ∈ Λ then (QuotientAddGroup.mk (⟨r, hr⟩ : Λ) : Qm m Λ) else 0) fun q => ?_
  obtain ⟨r, hr, u, hu, ht⟩ := h _ (repm_mem q)
  have hrΛ : r ∈ Λ := by
    have := Λ.sub_mem (repm_mem q) (Λ.nsmul_mem hu m)
    rwa [ht, add_sub_cancel_right] at this
  refine ⟨⟨r, hr⟩, ?_⟩
  simp only [dif_pos hrΛ]
  rw [← mk_repm q, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  refine mem_mLat.2 ⟨u, hu, ?_⟩
  change m • u = -r + repm q
  rw [ht]; abel

theorem decomp_of_lam (ψ : AddChar (AF D.host.F) ℂ) (Λ : AddSubgroup (WO S T)) (m : ℕ) (hm : 0 < m)
    (hinf : ∀ u ∈ Λ, u.map (infPart D) = 0) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1)
    (hmax : ∀ x : WO S T, x.map (infPart D) = 0 → (∀ u ∈ Λ, ψ (symplO S T x u) = 1) → x ∈ Λ)
    (lam : WO S T → ℂ) (hlam : ∀ x ∈ Λ, ∀ y ∈ Λ, lam (x + y) = lam x * lam y * ψ (symplOH S T x y))
    (hlm : ∀ l ∈ Λ, lam (m • l) = 1) [Fintype (Qm m Λ)] (f : WO S T → ℂ) (hf : ∀ l ∈ Λ, heisO ψ S T (m • l) f = f) :
    ∃ (u : Qm m Λ → WO S T) (c : Qm m Λ → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, IsFinComb (c i)) ∧
      (∀ i, ∀ b ∈ Λ, lam b • heisO ψ S T b (comb ψ S T (c i) f) = comb ψ S T (c i) f) ∧
      f = ∑ i, heisO ψ S T (u i) (comb ψ S T (c i) f) := by
  classical
  obtain ⟨s, hs⟩ : ∃ s : Qm m Λ → WO S T, ∀ a, s a = incA D ((m : D.host.E)⁻¹) • repm a := ⟨_, fun _ => rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℂ, N = (Fintype.card (Qm m Λ) : ℂ) := ⟨_, rfl⟩
  have hN0 : N ≠ 0 := by rw [hN]; exact_mod_cast Fintype.card_ne_zero
  have hsinf : ∀ a, (s a).map (infPart D) = 0 := fun a => by
    rw [hs]; exact map_infPart_smul _ (hinf _ (repm_mem a))
  have hcomb : ∀ a, comb ψ S T (∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
      (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a)))) f =
      ∑ q : Qm m Λ, lam (repm q) • heisO ψ S T (repm q) (N⁻¹ • heisL S T ψ (-s a) f) := by
    intro a
    rw [comb_sum_single]
    refine Finset.sum_congr rfl fun q _ => ?_
    change _ = lam (repm q) • heisL S T ψ (repm q) (N⁻¹ • heisL S T ψ (-s a) f)
    rw [map_smul, heisL_heisL, smul_smul, smul_smul]
    rfl
  refine ⟨s, fun a => ∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
      (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a))), hsinf,
    fun a => isFinComb_sum_single _ _ fun q => map_infPart_add_neg (hinf _ (repm_mem q)) (hsinf a), fun a b hb => ?_, ?_⟩
  · rw [hcomb]
    refine heisAvg_invariant D ψ S T Λ m lam hlam _ (fun l hl => ?_) b hb
    change lam (m • l) • heisL S T ψ (m • l) (N⁻¹ • heisL S T ψ (-s a) f) = _
    have h1 : ψ (symplO S T (m • l) (-s a)) = 1 := by
      rw [symplO_neg_right, ← symplO_skew, hs, symplO_inv_smul_nsmul hm]
      exact hΛ _ (repm_mem a) _ hl
    have h2 : heisL S T ψ (m • l) f = f := hf l hl
    rw [hlm l hl, one_smul, map_smul, heisL_comm, h1, one_smul, h2]
  · have h3 : ∀ a, heisO ψ S T (s a) (comb ψ S T (∑ q : Qm m Λ, Finsupp.single (repm q + -s a)
        (lam (repm q) * N⁻¹ * ψ (symplOH S T (repm q) (-s a)))) f) =
        ∑ q : Qm m Λ, ψ (symplO S T (s a) (repm q)) • ((lam (repm q) * N⁻¹) • heisL S T ψ (repm q) f) := by
      intro a
      rw [hcomb]
      change heisL S T ψ (s a) (∑ q : Qm m Λ, lam (repm q) • heisL S T ψ (repm q) (N⁻¹ • heisL S T ψ (-s a) f)) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, map_smul, map_smul, heisL_comm, heisL_cancel, smul_smul, smul_smul, smul_smul]
      congr 1
      ring
    simp only [h3]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hs, charSum_selfAnn D ψ S T Λ m hm hinf hΛ hmax, ← hN, ite_smul, zero_smul]
    rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
    obtain ⟨l, hl, hl'⟩ := mem_mLat.1 (repm_zero_mem (m := m) (Λ := Λ))
    have h2 : heisL S T ψ (m • l) f = f := hf l hl
    rw [← hl', hlm l hl, h2, one_mul, smul_smul, mul_inv_cancel₀ hN0, one_smul]

theorem theta_eq_sum_latVac : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → IsVacO ψ θ S T sS sT LS LT f₀ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∃ (n : ℕ) (u : Fin n → WO S T) (c : Fin n → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, GlobalTheory.SeeSaw.IsFinComb (c i)) ∧ (∀ i, IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) (GlobalTheory.SeeSaw.comb ψ S T (c i) f)) ∧ f = ∑ i, heisO ψ S T (u i) (GlobalTheory.SeeSaw.comb ψ S T (c i) f) := by
  intro D ψ θ S T sS sT LS LT f₀ hS hT hv f hf
  have hψ := hv.1
  obtain ⟨k, hk, hfk⟩ := Formalism.IndefR.Fin.latLevel_of (Formalism.IndefR.Fin.latSelfDual D) ψ hψ S T LS LT hS hT f hf
  obtain ⟨-, -, hmod, hdual⟩ := Formalism.IndefR.Fin.latSelfDual D ψ hψ S T LS LT hS hT
  have hinf := fun u (hu : u ∈ latO S T LS LT fun _ => True) => Formalism.IndefR.Fin.latAll_inf S T LS LT hu
  obtain ⟨R, hR, hRc⟩ := GlobalTheory.LatFinMod.latO_finite_mod D S T _ _ hS.1.fg hT.1.fg (fun _ => True) (2 * k) (by omega)
  change ∀ u ∈ latO S T LS LT fun _ => True, _ at hfk
  generalize latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at hfk hmod hdual hinf hRc ⊢
  haveI : Finite (Qm (2 * k) Λ) := finite_Qm hR hRc
  letI : Fintype (Qm (2 * k) Λ) := Fintype.ofFinite _
  obtain ⟨e, h1, h2, hi, hi', h, hh, h3⟩ := GlobalTheory.TwoPlaceIdem.exists_idem_half D
  have hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, ψ (symplO S T x y) = 1 := fun x hx => (hdual x (hinf x hx)).1 hx
  have hr : ∀ u ∈ Λ, ∃ z ∈ Λ, (1 - e - cA D e) • u = 2 • z := fun u hu =>
    ⟨h • u, hmod h hh u hu, by rw [← h3, two_mul, add_smul, two_nsmul]⟩
  have hl2 : ∀ u ∈ Λ, lamE ψ S T e (2 • u) = 1 := fun u hu => lamE_two_nsmul hΛ (hmod e hi) (hmod _ hi') hu
  obtain ⟨u, c, hu, hc, hfix, hsum⟩ := decomp_of_lam ψ Λ (2 * k) (by omega) hinf hΛ (fun x hx h => (hdual x hx).2 h)
    (lamE ψ S T e) (lamE_add_of_lattice D ψ S T Λ e h1 h2 hΛ (hmod e hi) (hmod _ hi') hr)
    (fun l hl => by rw [mul_nsmul']; exact hl2 _ (Λ.nsmul_mem hl k)) f
    (fun l hl => by rw [mul_nsmul]; exact hfk _ (Λ.nsmul_mem hl 2))
  let ι := (Fintype.equivFin (Qm (2 * k) Λ)).symm
  refine ⟨_, fun i => u (ι i), fun i => c (ι i), fun i => hu _, fun i => hc _, fun i => ⟨fun b hb => ?_, fun e' he' b hb hb' => ?_⟩, ?_⟩
  · have := hfix (ι i) _ (Λ.nsmul_mem hb 2)
    rwa [hl2 b hb, one_smul] at this
  · have := hfix (ι i) b hb
    rwa [lamE_half e he'.2.1 hb', one_smul] at this
  · exact hsum.trans (Equiv.sum_comp ι fun q => heisO ψ S T (u q) (comb ψ S T (c q) f)).symm

end GlobalTheory.FinDecomp

end

theorem _root_.GlobalTheory.T.orientedTheta_eq_finite_heisenbergTranslates_vacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → IsVacO ψ θ S T sS sT LS LT f₀ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → ∃ (n : ℕ) (u : Fin n → WO S T) (c : Fin n → WO S T →₀ ℂ), (∀ i, (u i).map (infPart D) = 0) ∧ (∀ i, GlobalTheory.SeeSaw.IsFinComb (c i)) ∧ (∀ i, IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) (GlobalTheory.SeeSaw.comb ψ S T (c i) f)) ∧ f = ∑ i, heisO ψ S T (u i) (GlobalTheory.SeeSaw.comb ψ S T (c i) f) :=
  GlobalTheory.FinDecomp.theta_eq_sum_latVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairExistenceOfFunctoriality
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.PairIt

open GlobalTheory.Chain GlobalTheory.Chain.RealIt

theorem exists_locIt_pair {D : D7} {V W : HSp D} {S S' : D.what₂.Tau → SPar} {X : ProvA} (hX : ChosenSeries X)
    (h1 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisFirst X) (h2 : Formalism.MainNotions.SchurIrreducible.ArchimedeanRallisSecond X) (hB : GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.ModelsAreCoverSeries D)
    (M : DSModel V S) (M' : DSModel W S') (τ : D.what₂.Tau) {aS aT : ℚ}
    (hP : GlobalTheory.PairLift.PairPar (S τ) (S' τ) aS aT) :
    (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ aS aT A := by
  obtain ⟨t, P, P', hS, hS', hc⟩ := hP
  rcases hc with ⟨⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩, -⟩ | ⟨al, be, ga, de, e1, ⟨hd, e2⟩ | ⟨hd, e2⟩⟩
  · exact exists_locIt hX h1 h2 hB M M' τ hd (hS.trans (congrArg dualPar e1)) (hS'.trans (congrArg dualPar e2))
  · obtain ⟨hr, A, hA⟩ := GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e2)) (hS.trans (congrArg dualPar e1))
    obtain ⟨A', hA'⟩ := GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · obtain ⟨hr, A, hA⟩ := exists_locIt hX h1 h2 hB M' M τ hd
      (hS'.trans (congrArg dualPar e1)) (hS.trans (congrArg dualPar e2))
    obtain ⟨A', hA'⟩ := GlobalTheory.T.localFockIntertwiner_adjoint_exchangedPair D W V _ _ M' M τ _ _ A hA
    exact ⟨⟨hr.2, hr.1⟩, A', hA'⟩
  · exact GlobalTheory.Chain.RealItLarge.exists_locIt_large hX h1 h2 hB M M' τ hd
      (hS.trans (congrArg dualPar e2)) (hS'.trans (congrArg dualPar e1))

theorem pairEx : GlobalTheory.FunPr.Hypotheses₂ → PairEx := by
  intro hPr D S S' aS aT hP V W M M' θ ψ hθ
  have hD := hPr.discreteSeriesCover
  have hH := hPr.harishChandraModules
  obtain ⟨X, hX, h1, h2⟩ := GlobalTheory.Chain.ItPairObj.exists_record hD hH
  have hB := GlobalTheory.T.thetaModels_eq_coverDiscreteSeries hD hH D
  have key : ∀ τ, (0 < V.rank ∧ 0 < W.rank) ∧ ∃ A, LocIt M M' τ (aS τ) (aT τ) A := fun τ =>
    exists_locIt_pair hX h1 h2 hB M M' τ (hP τ)
  choose hr A hA using key
  obtain ⟨It, I, hI⟩ := GlobalTheory.T.exists_globalFockIntertwiner_tensor_realPlaces D V W _ _ M M' aS aT A GlobalTheory.Contr.contraction.2 (GlobalTheory.T.gluing_law_holds D _ _) hA
  refine ⟨It, fun ω ⟨χS, χT, hω, he⟩ f hf => ?_⟩
  have hc := fun τ => GlobalTheory.T.thetaVacuumCharacters_atRealPlaces D V W _ _ M M' θ ψ χS χT ω f τ _ _ hθ hω (he τ).1 (he τ).2 hf
  exact isItW_of_globIt hθ hI hr (GlobalTheory.T.fockVectorsOverVacuumIsometry_of_skeletonDatum D V W _ _ M M' ψ θ hω.std hθ f hf).2.2.2.2
    (fun τ => (hc τ).2.1) fun τ => (hc τ).2.2

end GlobalTheory.PairIt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialColumnFourierInversionSchwartzBruhat
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.ColFourier

noncomputable section
namespace GlobalTheory.ColFourier

theorem fourier_pi_inversion_at {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] {n : Type*} [Fintype n] [DecidableEq n]
    {ψ : AddChar k Circle} {c : kˣ} {ν : Measure k} (h : HasConductor ψ c) (hν : IsSelfDual ψ ν)
    {g : (n → k) → ℂ} (hg : g ∈ SB (n → k)) (a : n → k) :
    ∫ y : n → k, (∫ x, g x * (ψ (x ⬝ᵥ y) : ℂ) ∂(Measure.pi fun _ => ν)) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)
      ∂(Measure.pi fun _ => ν) = g a := by
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  have hh : (fun x => g (x + a)) ∈ SB (n → k) :=
    ⟨hg.1.comp_continuous (by fun_prop), hg.2.comp_homeomorph (Homeomorph.addRight a)⟩
  have h1 := (FourierPi.fourier_pi_of_conductor h hν hh).2
  simp only [zero_add] at h1
  rw [← h1]
  congr 1
  funext y
  rw [← integral_mul_const,
    ← integral_add_right_eq_self (fun x => g x * (ψ (x ⬝ᵥ y) : ℂ) * (ψ⁻¹ (y ⬝ᵥ a) : ℂ)) a]
  congr 1
  funext x
  rw [add_dotProduct, AddChar.map_add_eq_mul, AddChar.inv_apply', dotProduct_comm y a, mul_assoc,
    ← Circle.coe_mul, mul_inv_cancel_right]

theorem fourierInt_inv_fourierInt : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (A C : Type) [Fintype A] [DecidableEq A] [DecidableEq C] (ψ : AddChar k Circle) (m : Measure k), HasConductor ψ 1 → IsUnitVol m → ∀ (P : Finset C), ∀ Ξ ∈ SB (Matrix A C k), fourierInt ψ⁻¹ m P (fourierInt ψ m P Ξ) = Ξ := by
  intro k _ _ _ _ _ _ A C _ _ _ ψ m hψ hm P Ξ hΞ
  have hν : IsSelfDual ψ m := isSelfDual_of_isUnitVol m hψ hm
  haveI := hν.1
  haveI := secondCountable k
  haveI := t2Space k
  funext X
  have h0 := comp_setCols_mem_SB hΞ P X
  have hg : (fun x : (_ : A) × P → k => Ξ (setCols P X (Matrix.of fun i j => x ⟨i, j⟩))) ∈
      SB ((_ : A) × P → k) :=
    ⟨h0.1.comp_continuous (f := fun x : (_ : A) × P → k => (Matrix.of fun i j => x ⟨i, j⟩ : Matrix A P k))
        (continuous_pi fun i => continuous_pi fun j => continuous_apply _),
      HasCompactSupport.intro (h0.2.image (f := fun (U : Matrix A P k) (p : (_ : A) × P) => U p.1 p.2)
        (continuous_pi fun p => (continuous_apply p.2).comp (continuous_apply p.1)))
        fun x hx => image_eq_zero_of_notMem_tsupport (f := fun U => Ξ (setCols P X U)) fun h => hx ⟨_, h, rfl⟩⟩
  have h1 := fourier_pi_inversion_at hψ hν hg (fun p => X p.1 p.2)
  have h2 : setCols P X (Matrix.of fun i (j : P) => X i j) = X := setCols_restrictCols P X
  simp only [h2] at h1
  rw [← h1, fourierInt_eq_pi]
  congr 1
  funext y
  rw [fourierInt_eq_pi]
  have h3 : (fun p : (_ : A) × P => setCols P X (Matrix.of fun i j => y ⟨i, j⟩) p.1 p.2) = y := by
    funext p
    simp [setCols, p.2.2]
  simp only [setCols_setCols, h3]

end GlobalTheory.ColFourier
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PartialFourierSumInverseOfLatticeDepthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At piW psiLoc chrW)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlipMatch

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.partialFourierSum_inverse_of_latticeDepth : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A : Type) [Fintype A] [DecidableEq A] (C : Type) [Fintype C] [DecidableEq C] (ψ : AddChar k Circle) (ϖ : kˣ) (n : ℕ) (P : Finset C), IsUnif ϖ → HasConductor ψ 1 →
    ∀ Ξ : Matrix A C k → ℂ, HasDepth ϖ n (blockLat ϖ n P) Ξ → fourierSum ψ ϖ n P (invFourierSum ψ ϖ n P Ξ) = Ξ := by
  first | exact @GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum | exact GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum | (intros; apply GlobalTheory.FlipMatch.FourierInv.fourierSum_invFourierSum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PathConvergenceDownChainStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.path_convergence_down_chain : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank), GlobalTheory.FlipStart.ChainVecs ch t f → GlobalTheory.FlipStart.ChainPols ch q → ∀ M : Vol ch.G, M.Is t → ∀ y : (R.HX t).H, PathConv ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) ∧ liftP ch.W M (downPath t 0 D.R.m) (GlobalTheory.FlipStart.colPure ch.W t f fun j => q j) (formTop ch t y) = ch.cv.lift t y := by
  first | exact @GlobalTheory.FlipStart.column | exact GlobalTheory.FlipStart.column | (intros; apply GlobalTheory.FlipStart.column <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PositiveRealPartTraceCharacterMemNhdsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positiveRealPart_traceCharacter_mem_nhds : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (n ρ : ℕ) (L : Mx D ρ n) (x : Mx D n ρ), {z : Mx D n ρ | 0 < (star (psiE ψ (upSum (L ⬝ (z - x))))).re} ∈ nhds x := by
  first | exact @GlobalTheory.PosNhdsChar.posNhds | exact GlobalTheory.PosNhdsChar.posNhds | (intros; apply GlobalTheory.PosNhdsChar.posNhds <;> assumption)
end

