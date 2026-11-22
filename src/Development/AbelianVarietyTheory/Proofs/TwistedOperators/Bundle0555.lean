import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0544
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetExpansionExpDepth
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLu
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0545
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
import Formalism.LocalToGlobal.IndefiniteReal.LinksLemmas
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0535
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0570
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApprox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0536
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1425

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClassSumSchwartzProductsGridPath
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped Pointwise

noncomputable section

namespace GlobalTheory.FlipRun

open GlobalTheory.FunObj.LocTensor
open scoped ValuativeRel

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem locArg_eq_locM (B : Frames G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) :
    ∃ (β : GL (Fin (G.pT a.pair).rank) (Lev.EAf D)) (β' : GL (Fin (G.pS a.pair).rank) (Lev.EAf D)), ∀ w,
      ∃ (f : Fin ((locGrid G t w).rank (edgeOf a).tgt) → Fin (G.pS a.pair).rank)
        (g : Fin ((locGrid G t w).rank (edgeOf a).src) → Fin (G.pT a.pair).rank),
        f.Surjective ∧ g.Surjective ∧ ∀ x r c, locArg B t w a x r c = locM β β' w x (g c) (f r) := by
  have sur : ∀ {m n : ℕ} (h : m = n), (Fin.cast h).Surjective := fun h y => ⟨Fin.cast h.symm y, by simp⟩
  rcases ha with ⟨i, j, hi, hj, rfl⟩ | ⟨i, j, hi, hj, rfl⟩
  · refine ⟨B.β i j, B.β (i + 1) j, fun w => ⟨Fin.cast (rank_vertex G t w (X := (i + 1, j)) ⟨hi, hj⟩),
      Fin.cast (rank_vertex G t w (X := (i, j)) ⟨hi.le, hj⟩), sur _, sur _, fun x r c => ?_⟩⟩
    have e : locArg B t w (.right i j) x = B.coord t w (X := (i, j)) (Y := (i + 1, j)) ⟨hi.le, hj⟩ ⟨hi, hj⟩
        (x.map fun c => cpt w (toEAf D c)) := dif_pos ⟨hi, hj⟩
    rw [e]
    rfl
  · refine ⟨B.β i (j + 1), B.β i j, fun w => ⟨Fin.cast (rank_vertex G t w (X := (i, j)) ⟨hi, hj.le⟩),
      Fin.cast (rank_vertex G t w (X := (i, j + 1)) ⟨hi, hj⟩), sur _, sur _, fun x r c => ?_⟩⟩
    have e : locArg B t w (.down t i j) x = B.coord t w (X := (i, j + 1)) (Y := (i, j)) ⟨hi, hj⟩ ⟨hi, hj.le⟩
        (x.map fun c => cpt w (toEAf D c)) := dif_pos ⟨hi, hj⟩
    rw [e]
    rfl

theorem locArg_add (B : Frames G) {t : T} {a : Arrow T} (ha : IsGridArrow D.R.m t a) (w : Pl D.host.E)
    (x u : WO (G.pS a.pair) (G.pT a.pair)) : locArg B t w a (x + u) = locArg B t w a x + locArg B t w a u := by
  obtain ⟨β, β', h⟩ := locArg_eq_locM B ha
  obtain ⟨f, g, -, -, h⟩ := h w
  ext r c
  rw [Matrix.add_apply, h, h, h, locM_add, Matrix.add_apply]

theorem arrow_sb {W : G.Weil} (B : Frames G) (ρ : RealMatch W) {μ₀ : T} (hL : L.Is μ₀) {t : T} {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {a : Arrow T} (ha : IsGridArrow D.R.m t a) {Y : Type}
    (F : WO (G.pS a.pair) (G.pT a.pair) → Y → ℂ)
    (h1 : ∀ x u y, (∀ w ∈ locPl G t, GivenAdm.CongM (unifAt w ^ n w) (locArg B t w a u)) → F (x + u) y = F x y)
    (h2 : ∀ x y, F x y ≠ 0 → ∀ w ∈ locPl G t, ∀ r c, locArg B t w a x r c ∈ 𝒪[Kw w]) :
    ∃ (ι : Type) (s : Finset ι) (φ : ι → Sch G a) (r : ι → WO (G.pS a.pair) (G.pT a.pair)),
      (∀ i ∈ s, IsSBHalf e (latA G a) (φ i)) ∧ ∀ x y, IsHalf e x → F x y = ∑ i ∈ s, φ i x * F (r i) y := by
  obtain ⟨hS, hT, -⟩ := arrow_data ρ hL ha
  obtain ⟨β, β', hβ⟩ := locArg_eq_locM B ha
  obtain ⟨k, hk, k1, k2⟩ := exists_mult hS.1 hT.1 he β β' n
  exact exists_sb hS.1.fg hT.1.fg (GlobalTheory.PlaceVec.idemSum_mul_self he) F hk
    (fun u hu x y => h1 x (k • u) y fun w hw r c => by
      obtain ⟨f, g, -, -, h⟩ := hβ w
      rw [h]
      exact k1 u hu w hw _ _)
    fun x y hx h0 => k2 x hx fun w hw i j => by
      obtain ⟨f, g, hf, hg, h⟩ := hβ w
      obtain ⟨c, rfl⟩ := hg i
      obtain ⟨r, rfl⟩ := hf j
      rw [← h]
      exact h2 x y h0 w hw r c

theorem exists_classSum_schwartzProducts_pathInduction {μ₀ : T} (hL : L.Is μ₀) {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}
    (he : IsIdemSum e (locPl G t)) (n : Pl D.host.E → ℕ) {X : Node} : ∀ {Y : Node} (p : Path T X Y), OnGrid D.R.m t p →
    (edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ),
    (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b,
      z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) →
    (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ edges p,
      x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) →
    ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → ArgT G p), (∀ κ ∈ s, VecAll ρ e p (φ κ) (d κ)) ∧
      ∀ (x : ArgT G p) (y : U), HalfAll e p x →
        K (fun w => pathArgs B t w p x) y = ∑ κ ∈ s, famProd p (φ κ) x * K (fun w => pathArgs B t w p (r κ)) y
  | _, .nil, _, _, U, K, _, _ => ⟨Unit, {()}, fun _ => (), fun _ => (), fun _ => (), fun _ _ => trivial, fun x y _ => by
      rw [Finset.sum_singleton]
      exact (one_mul _).symm⟩
  | _, .snoc a p, hg, hnd, U, K, hK1, hK2 => by
    rw [edges_snoc] at hnd
    obtain ⟨hnd1, -, hdis⟩ := List.nodup_append.1 hnd
    have hnot : edgeOf a ∉ edges p := fun h => hdis _ h _ (List.mem_singleton_self _) rfl
    have ha := hg.last
    obtain ⟨ι₁, s₁, φa, r₁, hφa, hexp⟩ := arrow_sb B ρ hL he n ha
      (fun x (z : ArgT G p × U) => K (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x)) z.2)
      (fun x u (z : ArgT G p × U) hu => by
        have e1 : (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a (x + u))) =
            (fun w => Function.update (pathArgs B t w p z.1) (edgeOf a) (locArg B t w a x)) +
              fun w => Function.update (0 : (locGrid G t w).Args) (edgeOf a) (locArg B t w a u) := by
          funext w b
          rcases eq_or_ne b (edgeOf a) with rfl | hb
          · simp only [Pi.add_apply, Function.update_self, locArg_add B ha]
          · simp only [Pi.add_apply, Function.update_of_ne hb, Pi.zero_apply, add_zero]
        show K _ z.2 = K _ z.2
        rw [e1]
        refine hK1 _ _ _ fun w hw b => ?_
        rcases eq_or_ne b (edgeOf a) with rfl | hb
        · rw [Function.update_self]
          exact GivenAdm.mem_matLat_smul.2 (hu w hw)
        · rw [Function.update_of_ne hb]
          exact zero_mem _)
      (fun x (z : ArgT G p × U) h0 w hw r c => by
        have h := hK2 _ z.2 h0 w hw (edgeOf a) (by rw [edges_snoc]; exact List.mem_append_right _ (List.mem_singleton_self _))
        rw [Function.update_self] at h
        exact GlobalTheory.SplitFlip.mem_matLat_stdLat.1 h r c)
    obtain ⟨ι₂, s₂, φ₂, d₂, r₂, hv, hexp₂⟩ := exists_classSum_schwartzProducts_pathInduction hL B ρ t he n p hg.init hnd1 (U := ι₁ × U)
      (fun Xa (z : ι₁ × U) => K (fun w => Function.update (Xa w) (edgeOf a) (locArg B t w a (r₁ z.1))) z.2)
      (fun x z y hz => by
        have e1 : (fun w => Function.update ((x + z) w) (edgeOf a) (locArg B t w a (r₁ y.1))) =
            (fun w => Function.update (x w) (edgeOf a) (locArg B t w a (r₁ y.1))) +
              fun w => Function.update (z w) (edgeOf a) 0 := by
          funext w b
          rcases eq_or_ne b (edgeOf a) with rfl | hb
          · simp only [Pi.add_apply, Function.update_self, add_zero]
          · simp only [Pi.add_apply, Function.update_of_ne hb]
        show K _ y.2 = K _ y.2
        rw [e1]
        refine hK1 _ _ _ fun w hw b => ?_
        rcases eq_or_ne b (edgeOf a) with rfl | hb
        · rw [Function.update_self]
          exact zero_mem _
        · rw [Function.update_of_ne hb]
          exact hz w hw b)
      (fun x y h0 w hw b hb => by
        have h := hK2 _ y.2 h0 w hw b (by rw [edges_snoc]; exact List.mem_append_left _ hb)
        rwa [Function.update_of_ne (ne_of_mem_of_not_mem hb hnot)] at h)
    obtain ⟨Tm, hTm, -, -⟩ := exists_arrowModel ρ hL he ha
    refine ⟨ι₂ × ι₁, s₂ ×ˢ s₁, fun κ => (φ₂ κ.1, φa κ.2), fun κ => (d₂ κ.1, Tm (φa κ.2)), fun κ => (r₂ κ.1, r₁ κ.2),
      fun κ hκ => ?_, fun x y hx => ?_⟩
    · obtain ⟨h1, h2⟩ := Finset.mem_product.1 hκ
      exact ⟨hv _ h1, (hTm _ _).2 ⟨hφa _ h2, rfl⟩⟩
    · have hx' : HalfAll e p x.1 ∧ IsHalf e x.2 := hx
      have e1 : (fun w => pathArgs B t w (.snoc a p) x) =
          fun w => Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a x.2) :=
        funext fun w => pathArgs_snoc B t w a p x
      calc K (fun w => pathArgs B t w (.snoc a p) x) y
          = ∑ i ∈ s₁, φa i x.2 * K (fun w => Function.update (pathArgs B t w p x.1) (edgeOf a) (locArg B t w a (r₁ i))) y := by
            rw [e1]
            exact hexp x.2 (x.1, y) hx'.2
        _ = ∑ i ∈ s₁, φa i x.2 * ∑ κ ∈ s₂, famProd p (φ₂ κ) x.1 *
              K (fun w => Function.update (pathArgs B t w p (r₂ κ)) (edgeOf a) (locArg B t w a (r₁ i))) y :=
            Finset.sum_congr rfl fun i _ => congrArg _ (hexp₂ x.1 (i, y) hx'.1)
        _ = _ := by
            rw [Finset.sum_product_right]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun κ _ => ?_
            have e2 : (fun w => pathArgs B t w (.snoc a p) ((r₂ κ, r₁ i) : ArgT G (.snoc a p))) =
                fun w => Function.update (pathArgs B t w p (r₂ κ)) (edgeOf a) (locArg B t w a (r₁ i)) :=
              funext fun w => pathArgs_snoc B t w a p _
            show _ = famProd p (φ₂ κ) x.1 * φa i x.2 * K (fun w => pathArgs B t w (.snoc a p) ((r₂ κ, r₁ i) : ArgT G (.snoc a p))) y
            rw [e2]
            ring

theorem exists_classes_path : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ {W : G.Weil} (B : Frames G) (ρ : RealMatch W) (t : T) {e : AE D}, IsIdemSum e (locPl G t) → ∀ (n : Pl D.host.E → ℕ) {X Y : Node} (p : Path T X Y), GlobalTheory.FlipRun.OnGrid D.R.m t p → (GlobalTheory.FlipRun.edges p).Nodup → ∀ {U : Type} (K : (∀ w, (locGrid G t w).Args) → U → ℂ), (∀ (x z : ∀ w, (locGrid G t w).Args) (y : U), (∀ w ∈ locPl G t, ∀ b, z w b ∈ GlobalTheory.SplitFlip.matLat _ (unifAt w ^ n w • GlobalTheory.SplitFlip.stdLat (Kw w) _)) → K (x + z) y = K x y) → (∀ (x : ∀ w, (locGrid G t w).Args) (y : U), K x y ≠ 0 → ∀ w ∈ locPl G t, ∀ b ∈ GlobalTheory.FlipRun.edges p, x w b ∈ GlobalTheory.SplitFlip.matLat _ (GlobalTheory.SplitFlip.stdLat (Kw w) _)) → ∃ (ι : Type) (s : Finset ι) (φ d : ι → PureT G p) (r : ι → GlobalTheory.FlipRun.ArgT G p), (∀ κ ∈ s, GlobalTheory.FlipRun.VecAll ρ e p (φ κ) (d κ)) ∧ ∀ (x : GlobalTheory.FlipRun.ArgT G p) (y : U), GlobalTheory.FlipRun.HalfAll e p x → K (fun w => GlobalTheory.FlipRun.pathArgs B t w p x) y = ∑ κ ∈ s, GlobalTheory.FlipRun.famProd p (φ κ) x * K (fun w => GlobalTheory.FlipRun.pathArgs B t w p (r κ)) y :=
  by
  intro D T L sc G μ₀ hL W B ρ t e he n X Y p hg hnd U K hK1 hK2
  exact exists_classSum_schwartzProducts_pathInduction hL B ρ t he n p hg hnd K hK1 hK2

end GlobalTheory.FlipRun

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHalfCosetRepresentativesCardDvd
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.HalfCosetCount

set_option maxHeartbeats 2000000 in

theorem halfCoset_reps_card : ∀ {D : D7} (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ (e : AE D) (P : Finset (Pl D.host.E)), IsIdemSum e P → ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), (∀ y ∈ R, IsHalf (cA D e) y ∧ k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ (∀ y : WO S T, IsHalf (cA D e) y → k • y ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) → ∃! r, r ∈ R ∧ y - r ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) ∧ R.card ∣ k ^ (D.R.f * S.rank * T.rank) := by
  intro D S T ΛS ΛT hS hT e P he k hk
  classical
  obtain ⟨⟨es, hes, rfl⟩, hec⟩ := he
  set Λ := (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) with hΛ
  set c := cA D (∑ Q ∈ P, es Q) with hcdef
  have hc : c = ∑ Q ∈ P, cA D (es Q) := map_sum _ _ _
  have hes_orth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → es Q * es Q' = 0 := fun Q hQ Q' hQ' hne =>
    (GlobalTheory.PlaceModelSum.eq_or_mul_eq_zero (hes Q hQ).1 (hes Q' hQ').1).resolve_left fun h => hne
      (HeightOneSpectrum.ext (Ideal.ext fun x => by
        by_cases hx : x = 0
        · rw [hx]; exact iff_of_true (zero_mem _) (zero_mem _)
        · rw [(hes Q hQ).2 x hx, (hes Q' hQ').2 x hx, h]))
  have hidem : ∀ Q ∈ P, cA D (es Q) * cA D (es Q) = cA D (es Q) := fun Q hQ => by
    rw [← map_mul, (hes Q hQ).1.1]
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → cA D (es Q) * cA D (es Q') = 0 := fun Q hQ Q' hQ' hne => by
    rw [← map_mul, hes_orth Q hQ Q' hQ' hne, map_zero]
  have hstab : ∀ Q ∈ P, ∀ u ∈ Λ, cA D (es Q) • u ∈ Λ := fun Q hQ u hu =>
    GlobalTheory.PlaceModelSum.idem_smul_latO (hidem Q hQ) hu
  have hch : ∀ Q : ↥P, ∃ w : HeightOneSpectrum (𝓞 D.host.F), ∃ π : AE D →+* Fv D.host.F w,
      GlobalTheory.SplitHecke.Chart (cA D (es Q)) w π := fun Q =>
    GlobalTheory.SplitChart.exists_chart _ (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1)
  choose v π hπ using hch
  have hvinj : Function.Injective v :=
    GlobalTheory.T.conjugate_idempotent_chart_places_injective _ P es (fun Q hQ => hes Q hQ) rfl hec v fun Q => ⟨π Q, hπ Q⟩

  have hcount : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex
      (Λ ⊓ GlobalTheory.PlaceModel.half S T c) =
      (∏ Q : ↥P, Nat.card ((v Q).adicCompletionIntegers D.host.F ⧸
        Ideal.span {(k : (v Q).adicCompletionIntegers D.host.F)})) ^ (S.rank * T.rank) := by
    rw [hc, GlobalTheory.T.relIndex_nsmul_half_orthogonal_idempotent_sum S T Λ P (fun Q => cA D (es Q)) hidem horth hstab k, ← Finset.prod_pow,
      ← Finset.prod_attach P]
    refine Finset.prod_congr rfl fun Q _ => ?_
    exact GlobalTheory.T.relIndex_nsmul_idempotentHalf_at_splitPlace S T ΛS ΛT hS.1 hT.1 _ (v Q) (π Q) (GlobalTheory.PlaceModelSum.isSplitIdem_cA (hes Q Q.2).1) (hπ Q) k hk
  have hdvd : (AddSubgroup.map (nsmulAddMonoidHom k) (Λ ⊓ GlobalTheory.PlaceModel.half S T c)).relIndex
      (Λ ⊓ GlobalTheory.PlaceModel.half S T c) ∣ k ^ (D.R.f * S.rank * T.rank) := by
    have h1 := GlobalTheory.T.prod_card_adicCompletionIntegers_quot_dvd_pow_finrank D.host.F (Finset.univ.image v) k hk
    rw [Finset.prod_image fun x _ y _ h => hvinj h, Formalism.MainNotions.J.finrank_F_eq] at h1
    rw [hcount, mul_assoc, pow_mul k D.R.f]
    exact pow_dvd_pow_of_dvd h1 _

  set M := Λ ⊓ GlobalTheory.PlaceModel.half S T c with hM
  set Y := Λ.comap (nsmulAddMonoidHom k) ⊓ GlobalTheory.PlaceModel.half S T c with hY
  have hinj : Function.Injective (nsmulAddMonoidHom k : WO S T →+ WO S T) := fun x y h => nsmul_cancel_mx hk h
  have hu : IsUnit (k : AE D) := by
    rw [← map_natCast (algebraMap D.host.F (AE D))]
    exact (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hk.ne')).map _
  have hYM : Y.map (nsmulAddMonoidHom k) = M := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hy1, hy2⟩ := AddSubgroup.mem_inf.1 hy
      exact AddSubgroup.mem_inf.2 ⟨hy1, (GlobalTheory.PlaceModel.half S T c).nsmul_mem hy2 k⟩
    · intro hx
      obtain ⟨hx1, hx2⟩ := AddSubgroup.mem_inf.1 hx
      have key : k • ((↑hu.unit⁻¹ : AE D) • x) = x := by
        rw [← Nat.cast_smul_eq_nsmul (AE D), smul_smul, IsUnit.mul_val_inv, one_smul]
      refine ⟨(↑hu.unit⁻¹ : AE D) • x, AddSubgroup.mem_inf.2 ⟨?_, ?_⟩, key⟩
      · rw [AddSubgroup.mem_comap]
        change k • _ ∈ Λ
        rw [key]; exact hx1
      · refine (GlobalTheory.PlaceModel.mem_half S T).2 ?_
        have hx3 : c • x = x := (GlobalTheory.PlaceModel.mem_half S T).1 hx2
        rw [smul_comm c (↑hu.unit⁻¹ : AE D) x, hx3]
  have hMY : M.relIndex Y = (M.map (nsmulAddMonoidHom k)).relIndex M := by
    rw [← AddSubgroup.relIndex_map_map_of_injective (f := (nsmulAddMonoidHom k : WO S T →+ WO S T)) M Y hinj, hYM]
  have hne : (M.addSubgroupOf Y).index ≠ 0 := by
    change M.relIndex Y ≠ 0
    rw [hMY]
    exact fun h => (pow_pos hk _).ne' (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))
  haveI : Finite (↥Y ⧸ M.addSubgroupOf Y) := AddSubgroup.index_ne_zero_iff_finite.1 hne
  obtain ⟨R, hRc, hRY, hRu⟩ := GlobalTheory.SplitLinear.exists_reps M Y
  refine ⟨R, fun y hy => ?_, fun y hy1 hy2 => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := AddSubgroup.mem_inf.1 (hRY y hy)
    exact ⟨(GlobalTheory.PlaceModel.isHalf_iff S T).2 h2, h1⟩
  · have hyY : y ∈ Y := AddSubgroup.mem_inf.2 ⟨hy2, (GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1⟩
    obtain ⟨r, ⟨hr, hyr⟩, huniq⟩ := hRu y hyY
    refine ⟨r, ⟨hr, (AddSubgroup.mem_inf.1 hyr).1⟩, fun r' hr' => huniq r' ⟨hr'.1, AddSubgroup.mem_inf.2 ⟨hr'.2, ?_⟩⟩⟩
    exact sub_mem ((GlobalTheory.PlaceModel.isHalf_iff S T).1 hy1) (AddSubgroup.mem_inf.1 (hRY r' hr'.1)).2
  · rw [hRc, hMY]
    exact hdvd

end GlobalTheory.HalfCosetCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsInnerStepIntertwinersThetaChain
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Chain.ExItY

theorem ex_ItY_holds : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (G : Type) [Group G]
    [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks]
    [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → HostHyp D → R.IsChainW →
    R.ex_ItY := by
  intro hDS hHC D G _ _ Pl0 T A Ks _ _ _ R hL _ hM hH hW
  have hθ : IsInfFam R.θ := hM.inf
  exact GlobalTheory.Chain.innerIntertwiners_of_pair D G Pl0 T A Ks R (GlobalTheory.T.exists_uniformRealThetaIntertwiner_chainStep hDS hHC D)
    (GlobalTheory.Chain.ParOfNodeGap.chainPar_of_nodeGap D hH.nodeGap) hθ
    (GlobalTheory.Chain.StepVac.stepsOK D G Pl0 T A Ks R hL hθ hW.ωY hW.ωX hW.vY hW.vX)

end GlobalTheory.Chain.ExItY
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntEqExponentAddHalfIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.SplitParity

theorem exists_eq_of_sigR_fixed {F E R : Type} [Field F] [CharZero F] [Field E] [Algebra F E] [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) (hr : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hne : ∃ x, σ x ≠ x)
    (z : R ⊗[F] E) (hz : sigR R σ z = z) : ∃ r : R, algebraMap R (R ⊗[F] E) r = z := by
  obtain ⟨δ, b, -, hb0, hb1, -⟩ := GlobalTheory.QuadNormBase.exists_basis F E σ hr hσ hne
  let B := Algebra.TensorProduct.basis R b
  have hB : ∀ i, B i = 1 ⊗ₜ[F] b i := fun i => Algebra.TensorProduct.basis_apply b i
  have h0 : B 0 = 1 := by rw [hB, hb0]; rfl
  have hs : ∀ (r : R) (e : E), sigR R σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := fun r e => rfl
  have hz' := B.sum_repr z
  rw [Fin.sum_univ_two] at hz'
  set x := B.repr z 0
  set y := B.repr z 1
  have e : sigR R σ (x • B 0 + y • B 1) = x • B 0 - y • B 1 := by
    rw [map_add, hB, hB, TensorProduct.smul_tmul', TensorProduct.smul_tmul', hs, hs, hb1, hb0,
      map_one, TensorProduct.tmul_neg, sub_eq_add_neg]
  rw [← hz', e] at hz
  have h2 : (2 * y) • B 1 = 0 := by
    have : x • B 0 - y • B 1 - (x • B 0 + y • B 1) = 0 := by rw [hz, sub_self]
    rw [two_mul, add_smul]
    linear_combination (-1 : R ⊗[F] E) * this
  have h3 : 2 * y = 0 := by
    have := congrArg (fun w => B.repr w 1) h2
    simpa using this
  have h4 : y = 0 := by
    have hu : (2 : R) * algebraMap F R (1 / 2) = 1 := by
      rw [← map_ofNat (algebraMap F R) 2, ← map_mul]; norm_num
    calc y = algebraMap F R (1 / 2) * (2 * y) := by linear_combination (-y) * hu
      _ = 0 := by rw [h3, mul_zero]
  refine ⟨x, ?_⟩
  rw [← hz', h4, zero_smul, add_zero, h0, Algebra.algebraMap_eq_smul_one]

end GlobalTheory.SplitParity

namespace GlobalTheory.SplitParity

theorem exists_idF_of_fixed (D : D7) (u : (AE D)ˣ) (hu : cA D (u : AE D) = u) : ∃ y, idF D y = u := by
  have hfx : ∀ z : AE D, cA D z = z → ∃ r : AF D.host.F, algebraMap (AF D.host.F) (AE D) r = z := fun z hz =>
    exists_eq_of_sigR_fixed D.sp.cm.sig D.sp.cm.deg2 (fun x => star_star x)
      (GlobalTheory.VolHeckeCompare.exists_not_fixed D) z hz
  obtain ⟨r, hr⟩ := hfx _ hu
  have hu' : cA D ((u⁻¹ : (AE D)ˣ) : AE D) = ((u⁻¹ : (AE D)ˣ) : AE D) := by
    have h1 : (u : AE D) * cA D ((u⁻¹ : (AE D)ˣ) : AE D) = 1 := by
      rw [← hu, ← map_mul, Units.mul_inv, map_one]
    exact (Units.inv_eq_of_mul_eq_one_right h1).symm
  obtain ⟨r', hr'⟩ := hfx _ hu'
  have m1 : r * r' = 1 := GlobalTheory.VolHeckeCompare.algebraMap_AE_injective D (by
    rw [map_mul, hr, hr', Units.mul_inv, map_one])
  refine ⟨⟨r, r', m1, by rw [mul_comm]; exact m1⟩, Units.ext ?_⟩
  exact hr

theorem exists_int_add_half : ∀ (D : D7) (χ : (AE D)ˣ →* Circle) (n : ℕ) (τ : D.what₂.Tau) (a : ℚ),
    IsHeckeChar D χ → ResEta D χ n → HasInfExp D χ τ a → ∃ e : ℤ, (e : ℚ) = a + (n : ℚ) / 2 := by
  intro D χ n τ a _ hr ha
  classical
  obtain ⟨N, hN, ⟨θ, hθ⟩, hχ⟩ := ha
  obtain ⟨η, -, -, hη1, hη2⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  obtain ⟨N1, hN1, -, hηx⟩ := hη2 τ
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨e, -, e1, e2⟩ := GlobalTheory.SplitCharExp.exists_real_hom h
  set w : D.what₂.Tau → ℂ := Pi.mulSingle τ (-1) with hw
  have wτ : w τ = -1 := by simp [w]
  have wo : ∀ τ', τ' ≠ τ → w τ' = 1 := fun τ' ht => by simp [w, Pi.mulSingle_eq_of_ne ht]
  have ww : w * w = 1 := by
    funext τ'
    by_cases ht : τ' = τ
    · subst ht; simp [wτ]
    · simp [wo τ' ht]
  let x : (AE D)ˣ := ⟨e w, e w, by rw [← map_mul, ww, map_one], by rw [← map_mul, ww, map_one]⟩
  have x1 : finPart D (x : AE D) = 1 := e1 w
  have x2 : ∀ τ', θ τ' (infPart D (x : AE D)) = w τ' := e2 w
  have xτ : θ τ (infPart D (x : AE D)) = -1 := by rw [x2, wτ]
  have xo : ∀ τ', τ' ≠ τ → θ τ' (infPart D (x : AE D)) = 1 := fun τ' ht => by rw [x2, wo τ' ht]
  have hcx : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ N := by rw [hχ θ hθ x x1 xo, xτ]; simp
  have hN1' : N1 = 1 := by
    have : (N1 : ℚ) = 1 := by rw [hN1]; norm_num
    exact_mod_cast this
  have hηc : ((η x : Circle) : ℂ) = -1 := by rw [hηx θ hθ x x1 xo, xτ, hN1']; simp
  have hfix : cA D (x : AE D) = x := by
    refine GlobalTheory.SplitCharExp.ext_of_chart h ?_ fun τ' => ?_
    · have e3 : finPart D (cA D (x : AE D)) = sigR (Af D.host.F) D.sp.cm.sig (finPart D (x : AE D)) :=
        GlobalTheory.FockCompare.LiftUnitary.snd_sigR D.sp.cm.sig (x : AE D)
      rw [e3, x1, RingHom.map_one]
    · rw [GlobalTheory.FockCompare.comp_cA hθ, x2]
      by_cases ht : τ' = τ
      · rw [ht, wτ]; simp
      · rw [wo τ' ht]; simp
  obtain ⟨y, hy⟩ := exists_idF_of_fixed D x hfix
  obtain ⟨⟨ε, hε⟩, hrχ⟩ := hr
  have c1 := hrχ ε hε y
  have c2 := hη1.2 ε hε y
  rw [hy] at c1 c2
  have c2' : ((ε y : Circle) : ℂ) = -1 := by rw [← hηc, c2, pow_one]
  have c1' : ((χ x : Circle) : ℂ) = (-1 : ℂ) ^ n := by rw [c1, Circle.coe_pow, c2']
  have hE : (-1 : ℂ) ^ N = (-1 : ℂ) ^ (n : ℤ) := by rw [← hcx, c1', zpow_natCast]
  have hP : (-1 : ℂ) ^ (N + (n : ℤ)) = 1 := by
    rw [zpow_add₀ (by norm_num), hE, ← zpow_add₀ (by norm_num), ← two_mul, zpow_mul]; norm_num
  rcases Int.even_or_odd (N + (n : ℤ)) with ⟨k, hk⟩ | ho
  · refine ⟨k, ?_⟩
    have : ((N + (n : ℤ) : ℤ) : ℚ) = ((k + k : ℤ) : ℚ) := by rw [hk]
    push_cast at this
    linarith
  · rw [ho.neg_one_zpow] at hP
    norm_num at hP

end GlobalTheory.SplitParity
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIteratedCompactAverageApproxStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_KFinite_iteratedCompactAverage_approx : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.Size.RapidDecSm θ N.V φ → ∀ (l : List D.what₂.Tau), l.Nodup → ∀ (d : ℕ) (η : ℝ), 0 < η → ∃ e : ∀ τ, Formalism.REAL.KG (N.M.ε τ) → ℂ, (∀ τ, GlobalTheory.TypeSum.KFinFun (N.M.ε τ) (e τ)) ∧ GlobalTheory.Size.growthSob θ N.V d 0 (φ - GlobalTheory.CuspApproxAll.avgList θ N e l φ) ≤ ENNReal.ofReal η := by
  first | exact @GlobalTheory.KAvgApprox.approx_avgList | exact GlobalTheory.KAvgApprox.approx_avgList | (intros; apply GlobalTheory.KAvgApprox.approx_avgList <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalDictionarySplitPlaceStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_dictionary_splitPlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    {d : ℕ} (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s →
    ∀ (v : Pl F), (∀ w : HeightOneSpectrum (𝓞 E), ¬ Formalism.UG.IsInertAt F E v w) → PsiUnr B.ψ v →
    ∃ (π₁ π₂ : AE F E →+* Fv F v) (b₁ b₂ : GL (Fin d) (Fv F v)),
      ((∀ z, π₁ (cA σ z) = π₂ z) ∧ (∀ z, π₂ (cA σ z) = π₁ z) ∧
      (∀ a : AF F, π₁ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ a : AF F, π₂ (algebraMap (AF F) (AE F E) a) = evFin F v a) ∧
      (∀ z : AE F E, At (evFin F v) z → π₁ z = 0 → π₂ z = 0 → z = 0) ∧
      (∀ x₁ x₂ : Fv F v, ∃ z : AE F E, At (evFin F v) z ∧ π₁ z = x₁ ∧ π₂ z = x₂) ∧
      (∀ z : Fin d → AE F E, z ∈ GlobalTheory.InertSph.latAt W v ↔ At (evFin F v) z ∧
        (∀ i, (((b₁⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₁ (z j)) i ∈
          v.adicCompletionIntegers F) ∧
        (∀ i, (((b₂⁻¹ : GL (Fin d) (Fv F v)) : Matrix (Fin d) (Fin d) (Fv F v)) *ᵥ fun j => π₂ (z j)) i ∈
          v.adicCompletionIntegers F))) ∧
      ∃ S : Matrix (Fin d) (Fin d) (v.adicCompletionIntegers F), IsUnit S.det ∧
        S.map (fun x => (x : Fv F v)) =
          (b₁ : Matrix (Fin d) (Fin d) (Fv F v))ᵀ * (incM F W.J).map π₁ * (b₂ : Matrix (Fin d) (Fin d) (Fv F v)) := by
  first | exact @GlobalTheory.SplitDict.exists_split_dictionary | exact GlobalTheory.SplitDict.exists_split_dictionary | (intros; apply GlobalTheory.SplitDict.exists_split_dictionary <;> assumption)
end

