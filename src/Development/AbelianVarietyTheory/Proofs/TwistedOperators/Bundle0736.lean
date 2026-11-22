import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0469
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1771
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1770
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0930
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0157
import Formalism.SharpRestriction.Divisibility.JetPolynomialLogs.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0529
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0546
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0588
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0717
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0552
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0568
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0551
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0730
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OmEqSumLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0543
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1155
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0181
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0353
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0705
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0733

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormToricRatio
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx.RatioField

open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

theorem kap_add_big (D : D7) (C : ℝ) (i j : Fin D.R.m) (τ : D.what₂.Tau) {s : ℕ} (hs : s ≤ bigN D + 1) :
    (kap D C i j s τ : ℤ) + s = (num D C τ).e (j + 1) + cen D C τ (D.R.m - i) ∧ 0 < kap D C i j s τ := by
  have h := SqNum.Model.gap_le D C i j τ
  have h2 := (GlobalTheory.ChiGrid.isLeast_gap D C).1.2.1
  have h4 : bigN D ≤ bigN D ^ 3 := Nat.le_self_pow (by norm_num) _
  unfold kap
  omega

theorem isValChar_shift {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s s' : ℕ}
    {κ κ' : I → ℕ} {𝔣 : Ideal (OF E)} {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E}
    (h : IsValChar φ s κ 𝔣 Q χ) (e : ∀ i, (κ i : ℤ) + s = κ' i + s') : IsValChar φ s' κ' 𝔣 Q χ := by
  obtain ⟨a, b, c, d⟩ := h
  have : (fun i => (κ' i : ℤ) + s') = fun i => (κ i : ℤ) + s := funext fun i => (e i).symm
  exact ⟨a, b, this ▸ c, d⟩

theorem cmPhi_comp_eq {D : D7} (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (τ τ' : D.what₂.Tau) :
    (cmPhi D τ).comp (algebraMap D.host.K D.host.E) = (cmPhi D τ').comp (algebraMap D.host.K D.host.E) := by
  obtain ⟨w, hw, hφw⟩ := hfd.2.2.2.2.2.2.2
  refine GlobalTheory.ToricRatioBridge.comp_eq_of_sqrt D.host _ _ ?_
  have hs := Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have h0 : (D.host.sqrtMinusD - w) * (D.host.sqrtMinusD + w) = 0 := by linear_combination hs - hw
  rcases mul_eq_zero.1 h0 with h | h
  · rw [sub_eq_zero.1 h, hφw, hφw]
  · rw [eq_neg_of_add_eq_zero_left h, map_neg, map_neg, hφw, hφw]

open Classical in

theorem ratio_algebraic (hTR : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates) {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts}
    {μ₀ : T} (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl))
    (i j : Fin D.R.m) (t : T) (s : ℕ) (hs1 : 1 ≤ s) (hs2 : s ≤ bigN D + 1) (Λ Λ₀ : ℂ → ℂ)
    (hΛ : IsHeckeL (nuH G t i j) Λ) (hΛ₀ : IsHeckeL (nuH G μ₀ i j) Λ₀) :
    IsAlgebraic ℚ (Λ s / Λ₀ s) := by
  haveI := hcm
  have hU : UnramFin D.host.E := hfd.2.2.1
  have hφ : IsCMType (cmPhi D) := hfd.2.2.2.2.2.2.1
  have e : ∀ τ, (kap D sc.cGap i j 0 τ : ℤ) + ((0 : ℕ) : ℤ) = kap D sc.cGap i j s τ + s := fun τ =>
    (SqNum.Model.kap_add D sc.cGap i j τ (Nat.zero_le _)).1.trans (kap_add_big D sc.cGap i j τ hs2).1.symm
  have hv0 : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) :=
    isValChar_shift (SqNum.Model.isValChar_nu hL G i j (Nat.zero_le _)).1 e
  obtain ⟨Q, hQdef⟩ : ∃ Q : Finset (HeightOneSpectrum (OF D.host.E)),
      Q = (GlobalTheory.SqTop.twPl G t).image fun P => P.under (𝓞 D.host.F) := ⟨_, rfl⟩
  have hvt : IsValChar (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) :=
    hQdef ▸ isValChar_shift (GlobalTheory.SqTop.TwVal.isValChar_nu_twist G hL t i j (Nat.zero_le _)) e
  have hQaux : IsFinSetSplitPlacesCoprimeConductor (condF G.pl) Q := hQdef ▸ GlobalTheory.KummerTwistLemmas.twist_places_under_split_coprime_conductor G hL t
  have hQram := GlobalTheory.SqTop.nuH_not_unrAt_twPl G hL t i j
  have hex : ∀ q ∈ Q, ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q := fun q hq => by
    rw [hQdef] at hq
    exact Finset.mem_image.1 hq
  let Pq : HeightOneSpectrum (OF D.host.E) → HeightOneSpectrum (𝓞 D.host.E) := fun q =>
    if h : ∃ P ∈ GlobalTheory.SqTop.twPl G t, P.under (𝓞 D.host.F) = q then h.choose else G.pl.w G.pl.v0
  have hPq : ∀ q ∈ Q, Pq q ∈ GlobalTheory.SqTop.twPl G t ∧ (Pq q).under (𝓞 D.host.F) = q := fun q hq => by
    have h := hex q hq
    simp only [Pq, dif_pos h]
    exact h.choose_spec
  have hov : ∀ q ∈ Q, Over (Pq q) q := fun q hq =>
    (show Over (Pq q) ((Pq q).under (OF D.host.E)) from rfl).trans (congrArg HeightOneSpectrum.asIdeal (hPq q hq).2)

  have htor := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) Q (nuH G t i j) Pq Λ hU hs1 hbc hQaux hvt hov hΛ
  rw [Finset.filter_false_of_mem (fun q hq => hQram _ (hPq q hq).1), Finset.prod_empty, mul_one] at htor

  have htor0 := GlobalTheory.ToricSumValue.toricSum_eq GlobalTheory.Published.HeckeEntire_holds D.host.E D.what₂.Tau (cmPhi D) hφ s
    (kap D sc.cGap i j s) (condF G.pl) ∅ (nuH G μ₀ i j) (fun _ => G.pl.w G.pl.v0) Λ₀ hU hs1 hbc
    (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 (fun q hq => absurd hq (Finset.notMem_empty q)) hΛ₀
  simp only [condQ, Finset.prod_empty, mul_one, Finset.filter_empty] at htor0

  have hnu : nuH G t i j = nuH G μ₀ i j * Lc.xiH t := by
    rw [nuH, nuH, hL.xi_base, mul_one, div_mul_eq_mul_div]

  obtain ⟨k, hk, hko⟩ := hL.xi_fin t
  have hinf : ∀ y : D.host.Eˣ, (Lc.xiH t).inf y = 1 := fun y => GlobalTheory.TypeValues.inf_eq_one _ hk hko y
  have hu : ∀ u ∈ hatOUnits (condQ (condF G.pl) Q), finPart (Lc.xiH t) u = 1 := fun u hu => by
    have a := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) Q (nuH G t i j) hU hbc hQaux hvt u hu
    have hle : condQ (condF G.pl) Q ≤ condQ (condF G.pl) ∅ := by
      simp only [condQ, Finset.prod_empty, mul_one]
      exact Ideal.mul_le_left
    have b := GlobalTheory.CMVal.OrderUnits.finPart_eq_one D.host.E D.what₂.Tau (cmPhi D) hφ s (kap D sc.cGap i j s)
      (condF G.pl) ∅ (nuH G μ₀ i j) hU hbc (fun q hq => absurd hq (Finset.notMem_empty q)) hv0 u
      (hatOUnits_mono hle hu)
    rw [hnu, finPart_mul, b, one_mul] at a
    exact a
  have hker : princ ⊔ hatOUnits (condQ (condF G.pl) Q) ≤ (finPart (Lc.xiH t)).ker := by
    refine sup_le ?_ fun u hu' => hu u hu'
    rintro _ ⟨a, rfl⟩
    have := finPart_mul_inf (Lc.xiH t) a
    rw [hinf a, mul_one] at this
    exact this
  let ψ : PicO (condQ (condF G.pl) Q) →* ℂˣ := QuotientGroup.lift _ (finPart (Lc.xiH t)) hker

  haveI : Nonempty D.what₂.Tau := Fintype.card_pos_iff.1 (by have := hfd.2.2.2.2.2.1; omega)
  let τ₀ : D.what₂.Tau := Classical.arbitrary _
  have hK2 : Module.finrank ℚ D.host.K = 2 := Formalism.MainNotions.DIV.Bridge.LogAbsNormDifferent.finrank_K D
  let δ : D.host.K := ⟨D.host.sqrtMinusD, GlobalTheory.Mem.Col2.HostK.sqrt_mem D.host⟩
  have hδ : δ ^ 2 = -(D.host.d : D.host.K) := Subtype.ext (by simpa using Formalism.BasicNotions.Host.sqrtMinusD_sq D.host)
  obtain ⟨T₀, Tf, hT₀, -, hTw, hAlg, -⟩ := hTR D.host.E D.host.K D.host.d δ
    ((cmPhi D τ₀).comp (algebraMap D.host.K D.host.E)) D.what₂.Tau (cmPhi D) s (kap D sc.cGap i j s) (condF G.pl) Q
    (nuH G μ₀ i j) hU hK2 hfd.1.pos hδ hφ (fun τ => cmPhi_comp_eq hfd τ τ₀) hs1
    (fun τ => (kap_add_big D sc.cGap i j τ hs2).2) hbc hQaux hv0
  have e1 : T₀ = Λ₀ s := hT₀.unique htor0
  have e2 : Tf ψ = Λ s :=
    ((GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.isTwistedSum_iff_isToricSum (ξ := Lc.xiH t) (fun y => rfl) _).1 (hTw ψ)).unique (hnu ▸ htor)
  rw [← e1, ← e2]
  exact hAlg ψ

end GlobalTheory.RowEx.RatioField

namespace GlobalTheory.RowEx.RatioField

open GlobalTheory.FunObj.SqNum GlobalTheory.CMVal

theorem inNF_ratios (hTR : GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates) {D : D7} {T : Type} [Finite T] {Lc : LevCh D T} {sc : Consts}
    {μ₀ : T} (hL : Lc.Is μ₀) (G : GridData Lc sc) (hcm : IsCMField D.host.E)
    (hfd : GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData D.host.d (cmPhi D)) (hbc : IsBaseCond (condF G.pl)) :
    InNF fun _ σ => ∀ i j, LRatiosIn G σ μ₀ i j := by
  let S : Set ℂ := ⋃ (i : Fin D.R.m) (j : Fin D.R.m) (t : T) (s ∈ Set.Icc 1 (bigN D + 1)),
    {z | ∃ Λ Λ₀ : ℂ → ℂ, IsHeckeL (nuH G t i j) Λ ∧ IsHeckeL (nuH G μ₀ i j) Λ₀ ∧ z = Λ s / Λ₀ s}
  have hS : S.Finite := by
    refine Set.finite_iUnion fun i => Set.finite_iUnion fun j => Set.finite_iUnion fun t =>
      (Set.finite_Icc _ _).biUnion fun s _ => Set.Subsingleton.finite ?_
    rintro _ ⟨Λ, Λ₀, h1, h2, rfl⟩ _ ⟨Λ', Λ₀', h1', h2', rfl⟩
    rw [h1.unique h1', h2.unique h2']
  have hSa : ∀ z ∈ S, IsAlgebraic ℚ z := by
    intro z hz
    simp only [S, Set.mem_iUnion, Set.mem_setOf_eq] at hz
    obtain ⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩ := hz
    exact ratio_algebraic hTR hL G hcm hfd hbc i j t s h1 h2 Λ Λ₀ hΛ hΛ₀
  haveI : Finite S := hS.to_subtype
  refine ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin fun z hz => (hSa z hz).isIntegral,
    fun i j t Λ Λ₀ hΛ hΛ₀ s h1 h2 _ => ⟨⟨Λ s / Λ₀ s, IntermediateField.subset_adjoin ℚ S ?_⟩, rfl⟩⟩
  simp only [S, Set.mem_iUnion, Set.mem_setOf_eq]
  exact ⟨i, j, t, s, ⟨h1, h2⟩, Λ, Λ₀, hΛ, hΛ₀, rfl⟩

theorem nfRatio : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols.ToricRatioConjugates → GlobalTheory.SqTop.FieldDat → GlobalTheory.SqTop.LNe → NFRatio := by
  intro _ hTR hFD _
  obtain ⟨CF0, hF⟩ := hFD
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x₀, hF⟩ := hF ε CF hCF
  refine ⟨x₀, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ hsc => ?_⟩
  have hRec : GlobalTheory.SqTop.Rec large₂ := (GlobalTheory.SqTop.Model.rec_iff large₂).2 ⟨hS.size, hS.host⟩
  haveI : Finite T := hS.fin
  have key : ∀ (sc : Consts) (G : GridData R.toLevCh sc), sc = ⟨1, CF, large₂.sc.b⟩ →
      InNF fun _ σ => ∀ i j, LRatiosIn G σ A.μ0 i j := by
    rintro sc G rfl
    obtain ⟨hcm, -, hfd, hbc, -⟩ := hF C0 le_rfl D large₂ he hx hRec T R.toLevCh A.μ0 hS.core.lev G
    exact inNF_ratios hTR hS.core.lev G hcm hfd hbc
  exact key ch.sc ch.G hsc

end GlobalTheory.RowEx.RatioField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProductFunctionTotalTensorInvariantLastArrows
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.LastVertexTensor

open GlobalTheory.LastVertexMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem lat_col (S : GridChoice W U) {t : T} (ht : t ∈ U) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl)
    (x : WO (G.pS (.top t (lastIx D))) (G.pT (.top t (lastIx D)))) :
    actO _ _ (colPt S t (finEmb G.sp.topDec k)).1⁻¹ (colPt S t (finEmb G.sp.topDec k)).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔
      x ∈ stdLat S (.top t (lastIx D)) :=
  GlobalTheory.LastColLat.colPt_inv_mem_stdLat_iff S ht k hk x

theorem lat_row (S : GridChoice W U) {t : T} (ht : t ∈ U) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl)
    (x : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T))) :
    actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔ x ∈ stdLat S (.chi (lastIx D) D.R.m) :=
  GlobalTheory.LastRowLat.rowPt_mem_stdLat S ht k hk x

theorem vac_col (S : GridChoice W U) (t : T) (g : FinPt G (.top D.R.m))
    (hlat : ∀ x, actO _ _ (colPt S t g).1⁻¹ (colPt S t g).2⁻¹ x ∈ stdLat S (.top t (lastIx D)) ↔ x ∈ stdLat S (.top t (lastIx D))) :
    ∃ c : ℂ, colShift S t g (S.Z.vac (.top t (lastIx D))) = c • S.Z.vac (.top t (lastIx D)) :=
  GlobalTheory.LastVertexVac.colShift_vac_eq_smul S t g hlat

theorem vac_row (S : GridChoice W U) (k : FinPt G (.grid D.R.m D.R.m))
    (hlat : ∀ x, actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔
      x ∈ stdLat S (.chi (lastIx D) D.R.m)) :
    ∃ c : ℂ, rowShift S k (S.Z.vac (.chi (lastIx D) D.R.m)) = c • S.Z.vac (.chi (lastIx D) D.R.m) :=
  GlobalTheory.LastRowVac.vac_row_scalar S k hlat

theorem sb_std (S : GridChoice W U) {t : T} (ht : t ∈ U) {p : Pair T} (hp : DefPair D.R.m p) (d : FinDatum G t p)
    (hP : d.P = locPl G t) : IsSBHalf d.e (stdLat S p) d.fn :=
  GlobalTheory.LastVertexMove.isSBHalf_stdLat S ht hp d hP

theorem loc (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T}
    (hL : L.Is μ₀) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (ht : t ∈ U) (hβ : β ∈ S.supp t Φ) (hexp : S.IsExpansion t Φ β τ)
    (hvec : ∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i))
    (k : FinPt G (.grid D.R.m D.R.m)) (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) (cc cr : ℂ)
    (hcc : colShift S t (finEmb G.sp.topDec k) (S.Z.vac (.top t (lastIx D))) = cc • S.Z.vac (.top t (lastIx D)))
    (hcr : rowShift S k (S.Z.vac (.chi (lastIx D) D.R.m)) = cr • S.Z.vac (.chi (lastIx D) D.R.m))
    (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
    (y : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))) :
    (τ.sum fun d a => a *
      (∏ j, Function.update (fun j => (d.1 j).fn) (lastIx D)
        (cc • moveFn (colPt S t (finEmb G.sp.topDec k)) (d.1 (lastIx D)).fn) j (x j)) *
      ∏ i, Function.update (fun i => (d.2 i).fn) (lastIx D) (cr • moveFn (rowPt S k) (d.2 (lastIx D)).fn) i (y i)) =
    τ.sum fun d a => a * (∏ j, (d.1 j).fn (x j)) * ∏ i, (d.2 i).fn (y i) :=
  GlobalTheory.T.expansion_sumProd_lastVertex_moved_eq S hL hde hc ht hβ hexp hvec k hk cc cr hcc hcr x y

end GlobalTheory.LastVertexTensor

namespace GlobalTheory.LastVertexTensor

open GlobalTheory.LastVertexMove

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem vec_eq_model (S : GridChoice W U) {t : T} {p : Pair T} (d : FinDatum G t p) (h : S.Z.HasVec d) (hz : d.z = 1)
    (Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ))
    (hT : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) d.e (stdLat S p) 1 (S.Z.vac p) Tm) : S.Z.vec d = Tm d.fn := by
  obtain ⟨f, hf⟩ := h
  rw [Normal.vec, FinDatum.vec_eq W hf, hz, Prod.mk_one_one, map_one, Module.End.one_apply]
  exact hf.2 Tm hT

theorem selfDual_std (S : GridChoice W U) {p : Pair T} (hp : DefPair D.R.m p) :
    IsSelfDualC (G.pS p) (S.N.latS p) ∧ IsSelfDualC (G.pT p) (S.N.latT p) := by
  have key : ∀ X, DefNode D.R.m X → IsSelfDualC (G.V X) (colLat (S.N.fr X)) := fun X hX =>
    OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on X hX)
  have hn := hp.nodes
  cases p with
  | chi i j => exact ⟨isSelfDualC_neg (key _ hn.2), key _ hn.1⟩
  | mu _ i j => exact (by simp [DefPair] at hp)
  | core i => exact (by simp [DefPair] at hp)
  | top _ j => exact ⟨key _ hn.1, key _ hn.2⟩

theorem om_model (S : GridChoice W U) {p : Pair T} (hp : DefPair D.R.m p) (hIn : p.InRange D.R.m) {e : AE D} {P : Finset (Pl D.host.E)}
    (he : IsIdemSum e P) (Tm : (WO (G.pS p) (G.pT p) → ℂ) →ₗ[ℂ] (WO (G.pS p) (G.pT p) → ℂ))
    (hT : IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLat S p) 1 (S.Z.vac p) Tm) (q : GA D (G.pS p) × GA D (G.pT p))
    (c : ℂ) (hlat : ∀ x, actO _ _ q.1⁻¹ q.2⁻¹ x ∈ stdLat S p ↔ x ∈ stdLat S p) (heig : W.om p q (S.Z.vac p) = c • S.Z.vac p)
    (Φ : WO (G.pS p) (G.pT p) → ℂ) (hΦ : IsSBHalf e (stdLat S p) Φ) : W.om p q (Tm Φ) = c • Tm (moveFn q Φ) := by
  have hind : (fun x => halfInd e (stdLat S p) (actO _ _ q.1⁻¹ q.2⁻¹ x)) = (1 : ℂ) • halfInd e (stdLat S p) := by
    funext x
    rw [Pi.smul_apply, one_smul]
    unfold halfInd
    by_cases h : x ∈ stdLat S p ∧ IsHalf e x
    · rw [if_pos ((and_congr (hlat x) (GlobalTheory.SchrMove.isHalf_actO_iff _ _ _)).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((and_congr (hlat x) (GlobalTheory.SchrMove.isHalf_actO_iff _ _ _)).1 h')), if_neg h]
  have hc : W.om p (q.1, q.2) (S.Z.vac p) = c • Tm (fun x => halfInd e (stdLat S p) (actO _ _ q.1⁻¹ q.2⁻¹ x)) := by
    rw [hind, hT.vac, Prod.mk.eta]
    exact heig
  have := GlobalTheory.SplitLinear.om_model_of_base D W.ψ _ _ _ _ (W.om p) (S.N.latS p) (S.N.latT p) e (S.Z.vac p) Tm (W.om_is p hIn)
    (selfDual_std S hp).1 (selfDual_std S hp).2 (GlobalTheory.PlaceDatum.idemSum_mul_self he) (GlobalTheory.PlaceDatum.infPart_idemSum he)
    (S.Z.vac_is p hp).2.theta hT q.1 q.2 c hc Φ hΦ
  rw [Prod.mk.eta] at this
  exact this

end GlobalTheory.LastVertexTensor

namespace GlobalTheory.LastVertexTensor

open GlobalTheory.LastVertexMove

def prodForm {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    (A : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (B : ∀ j, (Y j → ℂ) →ₗ[ℂ] (Y j → ℂ)) (x : ∀ i, X i) (y : ∀ j, Y j) :
    MultilinearMap ℂ (fun i => (⊤ : Submodule ℂ (X i → ℂ))) (MultilinearMap ℂ (fun j => (⊤ : Submodule ℂ (Y j → ℂ))) ℂ) :=
  ((MultilinearMap.mkPiAlgebra ℂ ι ℂ).compLinearMap fun i =>
      (LinearMap.proj (R := ℂ) (φ := fun _ : X i => ℂ) (x i)) ∘ₗ A i ∘ₗ (⊤ : Submodule ℂ (X i → ℂ)).subtype).smulRight
    ((MultilinearMap.mkPiAlgebra ℂ κ ℂ).compLinearMap fun j =>
      (LinearMap.proj (R := ℂ) (φ := fun _ : Y j => ℂ) (y j)) ∘ₗ B j ∘ₗ (⊤ : Submodule ℂ (Y j → ℂ)).subtype)

theorem prodForm_apply {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {X : ι → Type} {Y : κ → Type}
    (A : ∀ i, (X i → ℂ) →ₗ[ℂ] (X i → ℂ)) (B : ∀ j, (Y j → ℂ) →ₗ[ℂ] (Y j → ℂ)) (x : ∀ i, X i) (y : ∀ j, Y j)
    (f : ∀ i, (⊤ : Submodule ℂ (X i → ℂ))) (g : ∀ j, (⊤ : Submodule ℂ (Y j → ℂ))) :
    prodForm A B x y f g = (∏ i, A i (f i) (x i)) * ∏ j, B j (g j) (y j) := by
  simp [prodForm, MultilinearMap.smulRight_apply, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem productFn_invariant : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ k : FinPt G (.grid D.R.m D.R.m), finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ (w : ∀ j : Fin D.R.m, WO (G.pS (.top t j)) (G.pT (.top t j)))
      (v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T))),
    (τ.sum fun d a => a *
      (∏ j, Function.update (fun j => S.Z.vec (d.1 j)) (lastIx D)
        (colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D)))) j (w j)) *
      ∏ i, Function.update (fun i => S.Z.vec (d.2 i)) (lastIx D) (rowShift S k (S.Z.vec (d.2 (lastIx D)))) i (v i)) =
    τ.sum fun d a => a * (∏ j, S.Z.vec (d.1 j) (w j)) * ∏ i, S.Z.vec (d.2 i) (v i) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hde hc ht hβ hexp hvec k hk w v
  obtain ⟨e, he, hdat, -⟩ := id hexp
  obtain ⟨cc, hcc⟩ := vac_col S t (finEmb G.sp.topDec k) (lat_col S ht k hk)
  obtain ⟨cr, hcr⟩ := vac_row S k (lat_row S ht k hk)
  have hloc := loc S hL hde hc ht hβ hexp hvec k hk cc cr hcc hcr
  rcases τ.support.eq_empty_or_nonempty with h0 | ⟨d₀, hd₀⟩
  · simp [Finsupp.sum, h0]
  have hTc : ∀ j : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLat S (.top t j)) 1
      (S.Z.vac (.top t j)) Tm := by
    intro j
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).1 j
    have h1 := hf.1
    rw [((hdat d₀ hd₀).1 j).2.1] at h1
    exact h1
  have hTr : ∀ i : Fin D.R.m, ∃ Tm, IsPlaceModel W.ψ (symplO _ _) (heisO W.ψ _ _) e (stdLat S (.chi i D.R.m)) 1
      (S.Z.vac (.chi i D.R.m)) Tm := by
    intro i
    obtain ⟨f, hf⟩ := (hvec d₀ hd₀).2 i
    have h1 := hf.1
    rw [((hdat d₀ hd₀).2 i).2.1] at h1
    exact h1
  choose Tc hTc using hTc
  choose Tr hTr using hTr
  have hvc : ∀ d ∈ τ.support, ∀ j, S.Z.vec (d.1 j) = Tc j (d.1 j).fn := fun d hd j =>
    vec_eq_model S (d.1 j) ((hvec d hd).1 j) ((hdat d hd).1 j).2.2 (Tc j) (by rw [((hdat d hd).1 j).2.1]; exact hTc j)
  have hvr : ∀ d ∈ τ.support, ∀ i, S.Z.vec (d.2 i) = Tr i (d.2 i).fn := fun d hd i =>
    vec_eq_model S (d.2 i) ((hvec d hd).2 i) ((hdat d hd).2 i).2.2 (Tr i) (by rw [((hdat d hd).2 i).2.1]; exact hTr i)
  have hsc : ∀ d ∈ τ.support, colShift S t (finEmb G.sp.topDec k) (S.Z.vec (d.1 (lastIx D))) =
      Tc (lastIx D) (cc • moveFn (colPt S t (finEmb G.sp.topDec k)) (d.1 (lastIx D)).fn) := by
    intro d hd
    have hsb := sb_std S ht (defPair_top t (lastIx D)) (d.1 (lastIx D)) ((hdat d hd).1 (lastIx D)).1
    rw [((hdat d hd).1 (lastIx D)).2.1] at hsb
    rw [hvc d hd, map_smul, colShift_eq]
    exact om_model S (defPair_top t (lastIx D)) (inRange_top t (lastIx D)) he (Tc (lastIx D)) (hTc (lastIx D)) _ cc
      (lat_col S ht k hk) hcc _ hsb
  have hsr : ∀ d ∈ τ.support, rowShift S k (S.Z.vec (d.2 (lastIx D))) =
      Tr (lastIx D) (cr • moveFn (rowPt S k) (d.2 (lastIx D)).fn) := by
    intro d hd
    have hsb := sb_std S ht (defPair_chi (lastIx D)) (d.2 (lastIx D)) ((hdat d hd).2 (lastIx D)).1
    rw [((hdat d hd).2 (lastIx D)).2.1] at hsb
    rw [hvr d hd, map_smul, rowShift_eq]
    exact om_model S (defPair_chi (lastIx D)) (inRange_chi (lastIx D)) he (Tr (lastIx D)) (hTr (lastIx D)) _ cr
      (lat_row S ht k hk) hcr _ hsb
  have key := GlobalTheory.funProd_multilinear_sum_eq (prodForm Tc Tr w v) τ
    (fun d j => ⟨Function.update (fun j => (d.1 j).fn) (lastIx D)
      (cc • moveFn (colPt S t (finEmb G.sp.topDec k)) (d.1 (lastIx D)).fn) j, Submodule.mem_top⟩)
    (fun d j => ⟨(d.1 j).fn, Submodule.mem_top⟩)
    (fun d i => ⟨Function.update (fun i => (d.2 i).fn) (lastIx D) (cr • moveFn (rowPt S k) (d.2 (lastIx D)).fn) i,
      Submodule.mem_top⟩)
    (fun d i => ⟨(d.2 i).fn, Submodule.mem_top⟩) hloc
  simp only [prodForm_apply] at key
  rw [Finsupp.sum, Finsupp.sum] at key ⊢
  refine (Finset.sum_congr rfl fun d hd => ?_).trans (key.trans (Finset.sum_congr rfl fun d hd => ?_))
  · rw [mul_assoc]
    congr 2
    · refine Finset.prod_congr rfl fun j _ => ?_
      rw [show (fun j => S.Z.vec (d.1 j)) = fun j => Tc j (d.1 j).fn from funext (hvc d hd), hsc d hd,
        ← Function.apply_update (fun j => ⇑(Tc j)) (fun j => (d.1 j).fn) (lastIx D)]
    · refine Finset.prod_congr rfl fun i _ => ?_
      rw [show (fun i => S.Z.vec (d.2 i)) = fun i => Tr i (d.2 i).fn from funext (hvr d hd), hsr d hd,
        ← Function.apply_update (fun i => ⇑(Tr i)) (fun i => (d.2 i).fn) (lastIx D)]
  · rw [mul_assoc]
    congr 2
    · exact Finset.prod_congr rfl fun j _ => by rw [hvc d hd]
    · exact Finset.prod_congr rfl fun i _ => by rw [hvr d hd]

end GlobalTheory.LastVertexTensor
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSwap
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section
namespace GlobalTheory.LineKillV

theorem isDatum_list_sum {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} {M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd}
    {ψ : AddChar (AF F) ℂ} {Z : Type} {crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z}
    (hψ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ) {ι : Type} (l : List ι) (Ψ : ι → (Fin n × Fin d → AF F) → ℂ) (f : ι → Z → ℂ)
    (h : ∀ i, IsDatum M ψ crd (Ψ i) (f i)) : IsDatum M ψ crd (l.map Ψ).sum (l.map f).sum := by
  induction l with
  | nil => simpa using (GlobalTheory.SquareAgree.CoinvPass.isDatum_zero (M := M) (ψ := ψ) (crd := crd))
  | cons a l ih => simpa [List.map_cons, List.sum_cons] using GlobalTheory.SquareAgree.CoinvPass.isDatum_add hψ (h a) ih

theorem lineV_kill : GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁)
    (B : Fr X) (α β : (AE D)ˣ →* Circle) (ν : Measure (GA D W)) (𝓕 : Set (GA D W)) (ν₁ : Measure (GA D W₁))
    (𝓕₁ : Set (GA D W₁)) (ωA : WRep W X) (ωB : WRep W₁ X) (e : Fin X.rank ≃ Fin (W.rank + W₁.rank))
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W)
    (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W) (cA : Matrix (Fin W.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W X)
    (cB : Matrix (Fin W₁.rank) (Fin (W.rank + W₁.rank)) (AE D) ≃+ WO W₁ X),
    IsInfFam θ → IsTriple W W₁ X α β → ∀ (hO : IsOver ψ θ A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' →
    ∀ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
    ∀ γ ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Lines D.sp.cm.sig Γ.V, ∀ ΦD ∈ algD Γ.M Bs.ψ Bs.emb, ∀ Φ₁D ∈ algD Γ.M Bs.ψ Bs.emb,
    (∀ x, HasDerivAt (fun t : ℝ => om (γ (Multiplicative.ofAdd t), 1) ΦD x) (Φ₁D x) 0) → ∀ Φ₁,
    IsDatum Γ.M ψ cA Φ₁D Φ₁ → p Φ₁ = 0 := by
  intro hP D ψ θ W W₁ X A A₁ B α β ν 𝓕 ν₁ 𝓕₁ ωA ωB e Bs Γ Xc om om' cA cB hθ hT hO hTr Pi rf rl p p' hm γ hγ ΦD hΦD
    Φ₁D hΦ₁D hder Φ₁ hΦ₁
  have hψ : Bs.ψ = ψ := hO.psi
  have hstd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ := hψ ▸ hTr.base.std
  obtain ⟨Y, γs, hY, hγs, hγsY, hprod⟩ := GlobalTheory.T.unitaryArchimedeanOneParam_eq_prod_cmType_lines D θ hθ W Γ.V hO.JW γ hγ
  obtain ⟨Ψ, hΨ, hΨd, hsum⟩ := GlobalTheory.T.theta_pair_list_product hP _ _ _ Bs _ _ _ _ Γ.M _ _ om _ _ _ _
    (GlobalTheory.ThK.RealUniq.isPair_V hTr) _ γs hγs γ hγ hprod ΦD hΦD Φ₁D hder
  obtain ⟨Φ, hΦalg, hΦ⟩ := hO.algA' ΦD hΦD
  choose Φ' hΦ'alg hΦ' using fun τ => hO.algA' (Ψ τ) (hΨ τ)
  have hder' : ∀ τ, IsDer θ W (fun g => ωA (g, 1)) τ (Y τ) Φ (Φ' τ) := by
    intro τ z
    obtain ⟨u, rfl⟩ := cA.surjective z
    have h1 := hΨd τ u
    have e1 : (fun t : ℝ => GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (om (γs τ (Multiplicative.ofAdd t), 1) ΦD))) =
        fun t : ℝ => ωA (oneP θ W τ (Y τ) t, 1) Φ (cA u) := by
      funext t
      have h2 := (hO.weilA ΦD Φ hΦ (oneP θ W τ (Y τ) t) 1).2 u
      rw [GlobalTheory.KapXLine.kapX_one, ← hγsY τ t] at h2
      rw [hψ]; exact h2
    have e2 : GlobalTheory.WeilM.thetaSum D.host.F (Γ.M.co.rho Bs.ψ u (Ψ τ)) = Φ' τ (cA u) := by
      rw [hψ]; exact (hΦ' τ).2 u
    rw [e1, e2] at h1
    exact h1
  have hp : ∀ τ, p (Φ' τ) = 0 := fun τ =>
    hm.mapA.invl τ (Y τ) (hY τ) Φ hΦalg (Φ' τ) (hΦ'alg τ) (hder' τ)
  have hsumD : IsDatum Γ.M ψ cA Φ₁D (((Finset.univ : Finset D.what₂.Tau).toList.map Φ').sum) := by
    rw [hsum]; exact isDatum_list_sum hstd _ Ψ Φ' hΦ'
  rw [IsDatum.fun_eq Γ.M ψ cA cA.surjective hΦ₁ hsumD, map_list_sum, List.map_map]
  exact List.sum_eq_zero fun x hx => by
    obtain ⟨τ, -, rfl⟩ := List.mem_map.1 hx
    exact hp τ

end GlobalTheory.LineKillV

end
end

