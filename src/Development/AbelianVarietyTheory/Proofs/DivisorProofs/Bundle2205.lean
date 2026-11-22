import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2176
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0027
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1292
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1023
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0538
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0827
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2096
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0120
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2103
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
import Formalism.LocalToGlobal.GroupLattices.JointServices.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueIsTanFrameOfIsEmpty
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeOrdVpBaseChangeOfNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSecReadingDecreasingIntegerExponentsStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSec_reading_decreasing_integer_exponents : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r), Nonempty (KeySec Xo c) → GoodEmb c σ → IsUnf U → 1 ≤ Dw.p + Dw.q → ∀ G : WTZ E, Even G.2 → (∀ (τ : E →+* ℂ) (i j : ℕ), i ≤ j → j < Dw.mult τ → G.1 (τ, j) ≤ G.1 (τ, i)) → ∀ f ∈ secZ Xo c (exZ Dw G), ∀ k, (U.X k).IsSec (modelWt U G k) (rdU U f k) := by
  first | exact @GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU | exact GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU | (intros; apply GlobalTheory.FlatTw.Hol.isSec_modelWt_rdU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransportIdentityOfMemComponentGroupStatement
section
open NumberField IsDedekindDomain Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.CovTop Formalism.L2.Pj GlobalTheory.FormTies GlobalTheory.Shares
open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTransport_identity_of_mem_componentGroup : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz), More p → ∀ (r : TwoRuns p.T p.P.Gp) (h : RunsOk (fw2 p) r), OwnPin r → ∀ (i : Fin D.R.m) (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (ψ : ∀ k : (uAt r v i).Comp, LaMod (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l ≃ₗ[𝓞 D.host.E] latQ p r i v k) (k : (uAt r v i).Comp) (γ₀ : GL (Fin D.R.r) D.host.E), γ₀ ∈ ((uAt r v i).X k).Γ → IsTransp p r i v ψ 1 k k γ₀ := by
  first | exact @GlobalTheory.ShareOn.isTransp_one_of_mem_Γ | exact GlobalTheory.ShareOn.isTransp_one_of_mem_Γ | (intros; apply GlobalTheory.ShareOn.isTransp_one_of_mem_Γ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicFactorDepthEqSumFactorDepths
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.IsoFactorDepth

open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns in

def colEmb {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    (cx : Lt1 Dw → ℕ) : Col cx ↪ (Σ f : Lt1 Dw, Fin (rk f)) where
  toFun b := ⟨b.1.1, b.2⟩
  inj' := by
    rintro ⟨⟨f, hf⟩, a⟩ ⟨⟨g, hg⟩, b⟩ h
    simp only [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h⟩ := h
    cases h
    rfl

open GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns in

theorem prodP_eq_rename_polyH {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (C : Type) [Field C] (cx : Lt1 Dw → ℕ) :
    prodP C cx = MvPolynomial.rename (fun x : Let cx =>
      (⟨colEmb cx x.1, x.2⟩ : Σ b : (Σ f : Lt1 Dw, Fin (rk f)), Fin (rk b.1))) (polyH C cx) := by
  classical
  unfold prodP polyH
  rw [map_prod]
  simp_rw [MvPolynomial.rename_rename]
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun f : Lt1 Dw => cx f ≠ 0)]
  have h1 : ∏ f : {f : Lt1 Dw // ¬ cx f ≠ 0}, MvPolynomial.rename (fun ℓ : (Σ _ : Fin (rk f.1), Fin (rk f.1)) =>
      (⟨⟨f.1, ℓ.1⟩, ℓ.2⟩ : Σ b : (Σ f : Lt1 Dw, Fin (rk f)), Fin (rk b.1))) (GlobalTheory.FGDepth.detPow C (rk f.1) (cx f.1)) = 1 := by
    refine Finset.prod_eq_one fun f _ => ?_
    have h0 : cx f.1 = 0 := not_not.1 f.2
    rw [GlobalTheory.FGDepth.detPow, h0, pow_zero, map_one]
  rw [h1, mul_one]
  rfl

theorem nuH_vp_eq_nuP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (X : ValExt T p) (cx : Lt1 Dw → ℕ), GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp Ch X cx = nuP p y cx ∧ 0 ≤ nuP p y cx ∧ nuP p y cx ≠ ⊤ := by
  intro E _ _ _ H Dw l Xo c
  classical
  letI := H.starRing
  intro p _ T io y Ch X cx
  have hfac := (GlobalTheory.T.detFactorDepth_eq_chart_value_and_sum E H Dw l Xo c p T io y Ch X).1
  have hsum : nuP p y cx = ∑ f, nuFacC Ch X f (cx f) :=
    Finset.sum_congr rfl fun f _ => hfac f (cx f)
  have hbd : ∀ f, 0 ≤ nuFacC Ch X f (cx f) ∧
      nuFacC Ch X f (cx f) ≤ ((((rk f * cx f : ℕ) : ℝ) / (p - 1) : ℝ) : EReal) := fun f => by
    have h := GlobalTheory.T.formalGroupDeterminantPowDepth_bounds X.C (vX_vp X) p Fact.out (vX_vp_p X) (rk f) (chD Ch.ch) (cx f) (fgl Ch X)
      (frame Ch X f) (isSatFrame_frame Ch X f)
    refine ⟨h.1, h.2.2.trans (le_of_eq ?_)⟩
    push_cast; rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [hsum, ← GlobalTheory.FactorDepthProd.nuProdC_eq_sum]
    unfold nuProdC GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp
    rw [prodP_eq_rename_polyH]
    exact (GlobalTheory.FGDepth.depth_restrict X.C (vX_vp X) (Σ f : Lt1 Dw, Fin (rk f)) (fun _ => chD Ch.ch)
      (fun _ => fgl Ch X) (fun b => Fin (rk b.1)) (fun b => frame Ch X b.1) (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx)
      (colEmb cx) (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx)).symm
  · rw [hsum]
    exact Finset.sum_nonneg fun f _ => (hbd f).1
  · rw [hsum]
    have hreal : ∃ r : ℝ, ∑ f, nuFacC Ch X f (cx f) = (r : EReal) := by
      refine Finset.sum_induction _ (fun x : EReal => ∃ r : ℝ, x = r) ?_ ⟨0, rfl⟩ ?_
      · rintro a b ⟨r, rfl⟩ ⟨s, rfl⟩
        exact ⟨r + s, (EReal.coe_add r s).symm⟩
      · intro f _
        have h0 := (hbd f).1
        have h1 := (hbd f).2
        refine ⟨(nuFacC Ch X f (cx f)).toReal, (EReal.coe_toReal ?_ ?_).symm⟩
        · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
        · exact ne_bot_of_le_ne_bot (by simp) h0
    obtain ⟨r, hr⟩ := hreal
    rw [hr]
    exact EReal.coe_ne_top r

end GlobalTheory.IsoFactorDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KawamataViehwegVanishingOfNadelPairs
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Cartier GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.NadelApp

theorem isIso_idealModuleι_of_forall_notMem {X : Scheme.{0}} (I : X.IdealSheafData)
    (h : ∀ x, x ∉ I.support) : IsIso (idealModuleι I) := by
  have h0 : toSubscheme I = 0 := by
    haveI : IsEmpty I.subscheme := ⟨fun z => h _ (I.range_subschemeι.le ⟨z, rfl⟩)⟩
    ext V t
    have e : I.subschemeι ⁻¹ᵁ V = ⊥ := eq_bot_iff.2 fun z _ => isEmptyElim z
    have : Subsingleton Γ(I.subscheme, I.subschemeι ⁻¹ᵁ V) := by
      rw [e]
      infer_instance
    exact this.elim _ _
  exact kernel.ι_of_zero h0

theorem qWeil_zero {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] (m : ℕ) :
    qWeil (0 : CartierDiv X) m = 0 := by
  funext z
  have : (0 : CartierDiv X).mult z = 0 := by
    rw [(CartierDiv.isEqn_zero z).mult_eq]
    by_cases hz : Order.coheight z = 1
    · exact (Scheme.ord_eq_iff hz one_ne_zero).2 (by simp)
    · exact Scheme.ord_eq_zero_of_coheight_neq_one hz _
  simp [qWeil, this]

theorem kawamataViehweg_complex : GlobalTheory.Published.NadelVanishingPair → ∀ (X : Scheme.{0}) (p : X ⟶ Sp ℂ) (D : ℕ) [SmoothOfRelativeDimension D p], IsProjOver p → IsIntegral X → ∀ (K : CanonLB p D) (N : LB X), (letI := algebraΓOfHom p; IsNef ℂ N) → (letI := algebraΓOfHom p; IsBig ℂ N) → ∀ q : ℕ, 0 < q → Subsingleton (coh (twist (GlobalTheory.structureModule X) (tens K.bundle N)) q) := by
  intro hN X p D _ hproj _ K N hnef hbig q hq
  letI := algebraΓOfHom p
  haveI : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hproj
  obtain ⟨J, hJ, hv⟩ := nadel_canonical_add hN X p D hproj K N N hnef.isLB 0 1 1 one_pos one_pos
    CartierDiv.eff_zero hnef hbig (fun C _ => by
      rw [interNumRed_one_eq_zero (isLB_toLB 0) (by rw [← toPic_apply, map_zero])]
      simp)
  haveI := isIso_idealModuleι_of_forall_notMem J fun x hx => (hJ x).1 hx (by
    rw [qWeil_zero]
    exact kltAt_zero_of_smooth (topologicalKrullDim_eq_of_smooth X p D) x)
  exact @Function.Injective.subsingleton _ _ _ (cohOn.mapIso Γ(X, ⊤) ⊤ q
    ((twistFunctor (tens K.bundle N)).mapIso (asIso (idealModuleι J)))).symm.injective (hv q hq)

end GlobalTheory.NadelApp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LevelIsometry

section Free

open NumberField AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.LevelCusp GlobalTheory.DictMove GlobalTheory.AllWt GlobalTheory.LevDesc GlobalTheory.LevelKeeps
open GlobalTheory.Dict (castFr)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.FormTies (levFull)
open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem val_transl_nonneg (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (γ : LevelAut Dw l) {e : Ix Dw → ℤ}
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (h : ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) :
    ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v (transl Xo c γ f) := by
  rintro la _ ⟨⟨q, S, io, n, ho, y, hy, η, hη, rfl⟩, rfl⟩
  let := io.toAlgebra
  have hmv := levR_move hpq hA γ y.1
  let y' : IntFr Xo c S io :=
    ⟨_, GlobalTheory.FlagTan.fromTest_of_isLocalRing _,
      GlobalTheory.FormTies.LevelMove.integral_of_levR _ _ _ _ _ _ (levFull Dw l γ) S io y.1 _ hmv y.2.2⟩
  have h0 : 0 ≤ nval S.V n (evI y' f) := h la _ ⟨PtV.mk la ho y' hy () trivial, rfl⟩
  have e1 : evI y (transl Xo c γ f) = evI y' f := evR_transl hpq hA γ hf y.1
  show 0 ≤ nval S.V n (evI y (transl Xo c γ f))
  rw [e1]
  exact h0

variable {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {g : ℕ} {e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)}
  {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
  {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 E] (U.X k).Λ}

theorem norm_rdU_transl (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hP : HasPeriods φ)
    (hxi : ∀ k k', (U.X k).ξ0 = (U.X k').ξ0) (γ : LevelAut Dw l) {k k' : U.Comp} {δ : GL (Fin r) E}
    (h : Carries φ (levFull Dw l γ).1 k k' δ) {w : Ix Dw → ℤ} (hw : Even (w none)) {f : Rul Xo c}
    (hf : f ∈ secZ Xo c w) {x : Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ‖rdU U (transl Xo c γ f) k x‖ = ‖rdU U f k' (lact δ (castFr h.mt.psi x))‖ := by
  haveI : IsLocalRing (CAt σ) := inferInstanceAs (IsLocalRing ℂ)
  have hA' : l.A.Coprime l.M := by rw [hA]; exact Nat.coprime_one_left _
  obtain ⟨z, hz1, hz⟩ := exists_const_of_carries (w := 0) (n := 2) (s' := (levFull Dw l γ).2) hσ hU hpq hA hP hxi
    ⟨fun _ => antitone_const, even_two⟩ (transl Xo c γ)
    (fun f hf => by rw [← secZ_nat] at hf ⊢; exact transl_mem_secZ hpq hA' γ hf)
    (fun y => by
      obtain ⟨ρ, ν, -, hν, hm⟩ := levR_move hpq hA' γ y
      exact ⟨ρ, ν, _, hν, hm, fun f hf => by rw [← secZ_nat] at hf; exact evR_transl hpq hA' γ hf y⟩) h
  obtain ⟨m, hm⟩ := hw
  obtain ⟨ρ, ν, -, hν, hmv⟩ := levR_move hpq hA' γ (U.un k ⟨x, hx⟩)
  obtain ⟨a₁, b₁⟩ := move_eq hσ hpq hA hP h hν ⟨x, hx⟩ hmv
  obtain ⟨t₀, ht⟩ := GlobalTheory.GeoLevel.exists_frBor_gen _ _ a₁ b₁
  have key : ∀ (w : Ix Dw → ℤ), ∀ f ∈ secZ Xo c w, rdU U (transl Xo c γ f) k x =
      toC (t₀ : CAt σ) ^ w none * rdU U f k' (lact δ (castFr h.mt.psi x)) := fun w f hf => by
    have v1 : rdU U (transl Xo c γ f) k x = toC (evR Xo c (transl Xo c γ f) (U.un k ⟨x, hx⟩)) := dif_pos hx
    have v2 : rdU U f k' (lact δ (castFr h.mt.psi x)) = toC (evR Xo c f (U.un k' ⟨_, h.mt.mem_dom hx⟩)) :=
      dif_pos (h.mt.mem_dom hx)
    rw [v1, v2, evR_transl hpq hA' γ hf, GlobalTheory.FlagTan.evR_frBor hf ht, Fintype.prod_option]
    simp only [Option.elim, one_zpow, Finset.prod_const_one, mul_one]
    exact congrArg (· * toC (evR Xo c f (U.un k' ⟨_, h.mt.mem_dom hx⟩))) (Units.val_zpow_eq_zpow_val (α := ℂ) t₀ _)
  obtain ⟨f₂, hf₂, h0⟩ := exists_sec_two hσ hU (hU.1 ▸ hpq) k' (h.mt.mem_dom hx)
  have h2 := hz f₂ hf₂ x hx
  rw [← secZ_nat] at hf₂
  rw [key _ f₂ hf₂] at h2
  have h3 : toC (t₀ : CAt σ) ^ (2 : ℤ) = z := mul_right_cancel₀ h0 h2
  rw [key w f hf, hm, ← two_mul, zpow_mul, h3, norm_mul, norm_zpow, hz1, one_zpow, one_mul]

end Free

section Adelic

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
  Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.AllWt GlobalTheory.LevDesc GlobalTheory.DictMove
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.FormTies (levFull)
open scoped Matrix TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def rightEquiv (V : HSp D) (κ : GA D V) : AutQ V ≃ᵐ AutQ V :=
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have hrel : ∀ (k a b : GA D V), QuotientGroup.rightRel (GQ V) a b → QuotientGroup.rightRel (GQ V) (a * k) (b * k) :=
    fun k a b h => by
      rw [QuotientGroup.rightRel_apply] at h ⊢
      rwa [mul_inv_rev, mul_assoc, mul_inv_cancel_left]
  have hm : ∀ k : GA D V, Measurable (Quotient.map' (· * k) (hrel k) : AutQ V → AutQ V) := fun k _ hs =>
    measurable_mul_const k (autMk_measurable V hs)
  { toFun := Quotient.map' (· * κ) (hrel κ)
    invFun := Quotient.map' (· * κ⁻¹) (hrel κ⁻¹)
    left_inv := fun q => Quotient.inductionOn q fun a => congrArg (autMk V) (mul_inv_cancel_right a κ)
    right_inv := fun q => Quotient.inductionOn q fun a => congrArg (autMk V) (inv_mul_cancel_right a κ)
    measurable_toFun := hm κ
    measurable_invFun := hm κ⁻¹ }

theorem eLpNorm_right (V : HSp D) (hs : V.SigOK) (κ : GA D V) (Φ : GA D V → ℝ)
    (hΦ : ∀ γ ∈ GQ V, ∀ g, Φ (γ * g) = Φ g) (p : ENNReal) :
    eLpNorm (fun q : AutQ V => Φ (q.out * κ)) p (muQ1 V) = eLpNorm (fun q : AutQ V => Φ q.out) p (muQ1 V) := by
  obtain ⟨hP, hV⟩ := GlobalTheory.FinalJoin2.volPairEx_and_finVol D V hs
  have hR := ((GlobalTheory.CoreLawsCompare.invProb_iff V hP hV _).2 rfl).2
  have hmap : (muQ1 V).map (rightEquiv V κ) = muQ1 V := Measure.ext fun s hs => by
    rw [MeasurableEquiv.map_apply]
    exact hR κ _ (fun _ => rfl) s hs
  have hout : ∀ g, Φ (autMk V g).out = Φ g := fun g => by
    have e : (QuotientGroup.rightRel (GQ V)) g (autMk V g).out := Quotient.exact (Quotient.out_eq (autMk V g)).symm
    rw [QuotientGroup.rightRel_apply] at e
    rw [← hΦ _ e g, inv_mul_cancel_right]
  conv_rhs => rw [← hmap, (rightEquiv V κ).measurableEmbedding.eLpNorm_map_measure]
  congr 1
  funext q
  rw [← hout (q.out * κ)]
  exact congrArg (fun q' : AutQ V => Φ (rightEquiv V κ q').out) (Quotient.out_eq q)

variable {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H}

theorem exists_induces (V : HSp D) {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} (hι : LatEmb V ι)
    (γ : LevelAut Dw l) : ∃ κ, Induces V l ι (levFull Dw l γ).1 κ := by
  obtain ⟨red, h1, -, h3⟩ := GlobalTheory.LevelReduction.exists_isReduction D H Dw l V ι hι
  obtain ⟨k, rfl⟩ := h1 γ
  refine ⟨k, k.2.1, ?_, fun a ha => ?_⟩
  · have e : Formalism.L2.Pj.gLat V k = Formalism.L2.Pj.gLat V 1 := by
      unfold Formalism.L2.Pj.gLat
      rw [map_one, Units.val_one]
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨_, (k.2.2 y).2 hy, Matrix.one_mulVec _⟩
      · rintro ⟨y, hy, rfl⟩
        refine ⟨_, ((k⁻¹).2.2 y).2 hy, ?_⟩
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one,
          map_one, Units.val_one]
    unfold latGHat
    rw [e]
  · obtain ⟨w, hw, e⟩ := h3 k a ha
    exact ⟨-w, neg_mem hw, by rw [neg_nsmul, ← e, neg_sub]; exact (add_sub_cancel _ _).symm⟩

set_option maxHeartbeats 1000000 in

theorem petE_transl {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} {V : HSp D}
    (hs : V.SigOK) (hr : V.rank = r) {dict : GA D V → Σ k, Frame (U.X k).Ψ r}
    {ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)} {g : ℕ}
    {e : Fin g ≃ Σ τ : D.host.E →+* ℂ, Fin (Dw.mult τ)}
    {F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)}
    {ik : U.Comp → Fin F.n} {φ : ∀ k, (F.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (U.X k).Λ}
    {th th' : ∀ k, (U.X k).Ψ → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
    {x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ} {Kf : Subgroup (GA D V)}
    (hσ : GoodEmb c σ) (hU : IsUnf U) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A = 1) (hW : ∀ k, ModelW V hr (U.X k))
    (hι : LatEmb V ι) (hL : DictLat U V hr dict ι e F ik φ th x₀) (hth : ∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ))
    (hD : DictIsUnif V dict Kf th' hr) (hu : ∀ g τ i, ‖dmin (U.X (dict g).1).Gm (dict g).2 τ i‖ = 1)
    {G : WTZ D.host.E} (hG : Even G.2) (hχ : ∀ k, ∀ γ ∈ (U.X k).Γ, (U.X k).χ (modelWt U G k) γ = 1)
    (γ : LevelAut Dw l) {f : Rul Xo c} (hf : f ∈ secZ Xo c (exZ Dw G)) (hfc : rdU U f ∈ holSub U.X (modelWt U G)) :
    petE V dict (muQ1 V) (modelWt U G) (rdU U (transl Xo c γ f)) = petE V dict (muQ1 V) (modelWt U G) (rdU U f) := by
  subst hr
  obtain ⟨κ, hκ⟩ := exists_induces V hι γ
  have hN : ∀ (P : FDSec U.X) g, ptN (modelWt U G) P (dict g) = ‖P (dict g).1 (dict g).2‖ := fun P g =>
    pnorm_eq_of_unit _ _ _ _ (hu g)
  unfold petE
  simp only [hN]
  rw [← eLpNorm_right V hs κ (fun g => ‖rdU U f (dict g).1 (dict g).2‖) fun a ha h => by
    obtain ⟨a', ha', e₁⟩ := hD.1 a ha h
    have := (GlobalTheory.CuspSecFin.mem_SS_of_mem_holSub _ _ hfc (dict h).1).1.1.2.2 a' ha' _ (hD.2.2.2.1 h)
    rw [hχ _ _ ha', one_mul] at this
    rw [e₁]
    exact congrArg norm this]
  congr 1
  funext q
  obtain ⟨hx, δ, hc, e₁⟩ := GlobalTheory.StabMove.exists_carries (V := V) (W := V) rfl rfl rfl (dict := dict) ι hU hW hL hth
    hD.2.2.2.1 hκ q.out
  change (dict (q.out * κ)).2 = _ at e₁
  rw [e₁]
  exact norm_rdU_transl hσ hU hpq hA hL.1.2 (fun k k' => (hW k).2.trans (hW k').2.symm) γ hc hG hf hx

end Adelic

end GlobalTheory.LevelIsometry

end

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory.LevDesc (transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open scoped TensorProduct
open GlobalTheory GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar in
set_option maxHeartbeats 1000000 in

theorem GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ G : WTZ D.host.E, Even G.2 → KeepsCusp Y.U G ∧ ∀ (γ : LevelAut (T.Q.Dw j) Y.d.l₂) (f g : Y.V G), (g : Rul Y.d.Xo₂ Y.d.c₂) = pull Y.d.Xo₂ Y.d.c₂ γ f → (f ∈ AllWt.latW Y.U G → g ∈ AllWt.latW Y.U G) ∧ ∀ σ, Y.nrm G σ g = Y.nrm G σ f := by
  intro D T hT j hp _ _ hj Y e o hY G hG
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := le_add_right hp
  have hA := hY.lev.2
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hA]; exact Nat.coprime_one_left _
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hT.pins.2.1.1]
  have hχ := fun σ hσ => GlobalTheory.AllWt.Model.chi_modelWt (Y.U σ) (hY.chiTriv σ hσ) G hG
  obtain ⟨ι, hι, -, hpin⟩ := hY.adPin
  refine ⟨GlobalTheory.LevelKeeps.keepsCusp_of_isUnf hpq hA hG hY.unf (fun σ hσ k k' => ?_) (fun σ hσ => ?_) hχ,
    fun γ f g hg => ⟨fun hf => ?_, fun σ => ?_⟩⟩
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    exact ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    obtain ⟨th, _, hth, hD⟩ := hY.dictU σ hσ
    obtain ⟨x₀, h0, _, g, e, F, ik, φ, th', hth', hL⟩ := hpin σ hσ
    obtain rfl : th = th' := funext fun k => funext fun τ =>
      GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth k τ) (hth' k τ)
    exact GlobalTheory.LevelKeeps.mem_group (hY.unf σ hσ) hA ((hY.unf σ hσ).1 ▸ hpq) hr hW h0 (hM ▸ hY.levelK) hth hD fun h => by
      obtain ⟨γ, -, -, -, h3⟩ := hL.2 h
      exact ⟨_, h3⟩
  · intro la v hv
    show 0 ≤ v (g : Rul Y.d.Xo₂ Y.d.c₂)
    rw [hg]
    exact GlobalTheory.LevelIsometry.val_transl_nonneg hpq hA' γ⁻¹ (AllWt.mem_cuspW.1 f.2).1 hf la v hv
  · have hσ := goodEmb_goodOf (c := Y.d.c₂) σ
    obtain ⟨hr, hW⟩ := hY.modelW _ hσ
    obtain ⟨th, _, -, hD⟩ := hY.dictU _ hσ
    obtain ⟨x₀, -, _, g', e, F, ik, φ, th', hth', hL⟩ := hpin _ hσ
    have := GlobalTheory.LevelIsometry.petE_transl (D.sp.W_sig j) hr hσ (hY.unf _ hσ) hpq hA hW hι hL hth' hD (hY.unit _ hσ) hG
      (hχ _ hσ) γ⁻¹ (AllWt.mem_cuspW.1 f.2).1 ((AllWt.mem_cuspW.1 f.2).2 _ hσ)
    show _ * (AllWt.petE _ _ _ _ (rdU _ (g : Rul Y.d.Xo₂ Y.d.c₂))).toReal = _
    rw [hg]
    exact congrArg (fun t : ENNReal => AllWt.lieFacZ (T.Q.Dw j) (xiR D) G * t.toReal) this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRationalityAtPlace
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem kerOfAt : KerOfAt := by
  refine ⟨1, one_pos, fun _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun Fm _ _ _ => ⟨0, fun x hx _ i p hR hM w hw j => ?_⟩⟩⟩
  intro ρ hρ hpin
  have hL := GlobalTheory.BigOn.links2_of_rows _ _ _ _ _ _ _ _ _ _ p hR hM.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hBo : BaseOf (R2 p) j (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) := by
    have h0 := baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
    exact { h0 with }
  have hpl := placesAt (j := j) hw hρ hpin
  have hl : (Fm.D x i).ntw.l ((Fm.ex x hx i).nch.twI w) = Formalism.EigenvalueLevelCeiling.plc ((Fm.D x i).plEq w) := by
    rw [(Fm.ex x hx i).nch.twI_l, Formalism.L2.G.ServJoint.plc_plEq]
  have hpD : ∀ P, P ∈ (Fm.D x i).ntw.pD ((Fm.ex x hx i).nch.twI w) ↔
      ((ownAt (Fm.D x i) ((Fm.D x i).plEq w) : ℕ) : 𝓞 (Fm.D x i).host.E) ∈ P.asIdeal := fun P => by
    rw [← Finset.mem_coe, (Fm.D x i).ntw.pD_eq, ownAt, ← hl]
    rfl
  have hQ : (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.Q = plW p w := by
    ext P
    rw [hpl.1 P, hpD P]
    unfold plW GlobalTheory.OnTies.placesOver
    classical
    rw [Finset.mem_filter]
    rfl
  have hwt : (Fm.D x i).plEq w ∈ (R2 p).twPl := hw
  obtain ⟨ω, φ, hK⟩ := GlobalTheory.OnCmp.exists_baseKernel _ _ _ _ _ _ (R2 p) (F2 p) hC j _ hwt hL.1.tup.mu_on
  obtain ⟨χ, ξR, hD⟩ := GlobalTheory.OnBaseKer.kerDat_of_isBaseKernel _ _ _ _ _ _ (R2 p) (F2 p) hC j _ hwt hL.1.tup.mu_on ω φ hK
  have hχ : χ = (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)).de.chi :=
    GlobalTheory.ChrEqUnique.idc_unique _ _ _ _ hD.chr (hl ▸ hpin.delta _ j _)
  subst hχ
  have hω := hρ.weil_base ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)
  rw [Base.IsWeil, mul_one, Base.mu, hpin.psi, hpin.mu0, hpin.eta] at hω
  refine ⟨hBo, hQ, ξR, φ, { hD with weil := hω }⟩

end GlobalTheory.BigOn.Exp.SerBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerMatrixUniqueStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_matrix_unique : GlobalTheory.CovTop.Hypotheses₂ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → ∀ M M' : GlobalTheory.FlagTan.HIx Dw (GlobalTheory.FlagTan.psiSet H) → K, GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' M' → M = M' := by
  first | exact @GlobalTheory.FlagTan.isKS_unique | exact GlobalTheory.FlagTan.isKS_unique | (intros; apply GlobalTheory.FlagTan.isKS_unique <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanFieldStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_field : ∀ {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber K))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm K (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR K ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 K) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* K) (ub : ∀ σ, Fin (m σ) → (epsR K ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span K (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent K (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR K ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → K, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  first | exact @GlobalTheory.KSExist.ksRow_exists_lieComb | exact GlobalTheory.KSExist.ksRow_exists_lieComb | (intros; apply GlobalTheory.KSExist.ksRow_exists_lieComb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowDualEigenvectorMemSpanRingStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodairaSpencerRow_dual_eigenvector_mem_span_ring : ∀ {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] [IsCommMonObj A] {A' : Over (Sp (DualNumber R))} [GrpObj A'] {i : A.left ⟶ A'.left} (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed R) i) {O : Type} [CommRing O] (a : OAct O A) (cO : O → O) (ψ : LinearMap.BilinForm R (HdR A)), (∀ f ∈ Fil A, ∀ g ∈ Fil A, ψ f g = 0) → (∀ f, (∀ g ∈ Fil A, ψ f g = 0) → f ∈ Fil A) → LinearMap.IsPerfPair ψ → IsAdjointFor a cO ψ → KSRegular h → (∀ (z : O) (f : HdR A) (w : epsR R ⟶ A), IsKSValue h f w → IsKSValue h (act (dp0 R) (𝟙 _) a z f) (w ≫ a.act z)) → ∀ {ι : Type} {m : ι → ℕ} (χ : ι → O →+* R) (ub : ∀ σ, Fin (m σ) → (epsR R ⟶ A)) (hb : (Σ σ, Fin (m σ)) → HdR A), Submodule.span R (Set.range hb) ⊔ Fil A = ⊤ → LinearIndependent R (fun k => (Submodule.Quotient.mk (hb k) : HdR A ⧸ Fil A)) → (∀ k (z : O), act (dp0 R) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A) → (∀ σ (w : epsR R ⟶ A), IsTangent w → (∀ z, w ≫ a.act z = GlobalTheory.GrpTangent.epsScale (χ σ z) ≫ w) → ∃ cf, IsLieComb cf (ub σ) w) → ∀ (τ τb : ι), (∀ z, χ τb (cO z) = χ τ z) → ∀ (j : Fin (m τb)), ∃ cf : Fin (m τ) → R, ∃ w, IsLieComb cf (ub τ) w ∧ GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨τb, j⟩ w := by
  first | exact @GlobalTheory.KSRing.ksRow_exists_lieComb_ring | exact GlobalTheory.KSRing.ksRow_exists_lieComb_ring | (intros; apply GlobalTheory.KSRing.ksRow_exists_lieComb_ring <;> assumption)
end

