import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1381
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1042
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1384
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1382
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.TrivialExtensionSideWellFormed
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1216
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1379
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1201
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1140
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1137
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1195
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1337
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1380
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialStabilizerTransferConjSelfDualLatticStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR.Mult Formalism.UG GlobalTheory.SphPar GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefTransfer
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hyperspecial_stabilizer_transfer_conj_selfDual_lattice : ∀ (D : D7) [IsCMField D.host.E] (V : HSp D) (j : UA D.host.E V.rank ≃ₜ* GA D V) (h₀ : GA D V)
    (M : Matrix (Fin V.rank) (Fin V.rank) D.host.E),
    cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * M = 1 → h₀ ∈ GfC V → (∀ x, x ∈ finU D.host.E V.rank ↔ j x ∈ GfC V) →
    (∀ x, finMat D.sp.cm.sig V.gram (j x) =
      M.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) *
      ((x : GL (Fin V.rank) (Ad D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Ad D.host.E)).map
        (fun a => (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).symm (pFin D.host.E a)) *
      M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) →
    (∀ y, y ∈ latHat D.host.F D.host.E (L0c D V) ↔
      IntVec (Matrix.mulVec (M⁻¹.map (Algebra.TensorProduct.includeRight : D.host.E →ₐ[D.host.F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) (Matrix.mulVec (finMat D.sp.cm.sig V.gram h₀) y))) →
    (∀ (P : HeightOneSpectrum (𝓞 D.host.E)) e f, IsPrimeIdem P e f → ∀ x,
      x ∈ locU V.rank P ↔ cj j h₀ x ∈ GfC V ∧ SuppF V f (cj j h₀ x)) →
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) x, cj j h₀ x ∈ GlobalTheory.Hk3.hyp V P ↔ x ∈ KP V.rank P := by
  first | exact @GlobalTheory.TransferHyp.cj_mem_hyp_iff | exact GlobalTheory.TransferHyp.cj_mem_hyp_iff | (intros; apply GlobalTheory.TransferHyp.cj_mem_hyp_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedLatticeMapRadical
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticeBasisLifts GlobalTheory.GeoLevel
open GlobalTheory.Member (FinCong IotaOK)
open GlobalTheory.LevelCusp (IsMatch)
open GlobalTheory.Dict (castFr)
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoLevel

theorem isLift_inv_mul {D : D7} {V : HSp D} {r : ℕ} {hr : V.rank = r} {β : GL (Fin r) (EAf D)}
    {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)} {g : Formalism.L2.DIV.G0 Pg r} {κ₀ κ : GA D V}
    (h₀ : IsLift V hr β Pg g κ₀) (h : IsLift V hr β Pg g κ) : IsLift V hr β Pg 1 (κ₀⁻¹ * κ) := by
  obtain ⟨a₀, b₀, c₀⟩ := h₀
  obtain ⟨a, b, c⟩ := h
  have e : finR V hr (κ₀⁻¹ * κ) = (finR V hr κ₀)⁻¹ * finR V hr κ := by rw [map_mul, map_inv]
  have hb : finR V hr (κ₀⁻¹ * κ) ∈ Formalism.L2.DIV.St β := by
    rw [e]; exact mul_mem (inv_mem b₀) b
  refine ⟨mul_mem (inv_mem a₀) a, hb, fun w => ?_⟩
  have e2 : (⟨finR V hr (κ₀⁻¹ * κ), hb⟩ : Formalism.L2.DIV.St β) = (⟨finR V hr κ₀, b₀⟩ : Formalism.L2.DIV.St β)⁻¹ * ⟨finR V hr κ, b⟩ :=
    Subtype.ext e
  rw [e2, map_mul, map_inv, c₀, c, inv_mul_cancel]
  rfl

theorem cong_latG_of_finCong {D : D7} {V : HSp D} {M : ℕ} {k : GA D V} (hk : FinCong V M k)
    {a : Fin V.rank → D.host.E} (ha : a ∈ latG V 1) :
    ∃ w ∈ latGHat V 1, (finHom V k).1 *ᵥ finVec V a - finVec V a = M • w := by
  refine ((GlobalTheory.Member.AALev.congruences_agree D V k).2 M ⊤).1 (fun b _ z hz => hk _ ?_) a (by rwa [Submodule.top_smul])
  rw [GlobalTheory.Member.AALev.latHat_eq] at hz ⊢
  exact GlobalTheory.Member.AALev.hat_smul_int _ b hz

theorem exists_induces : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (l : Level H) (V : HSp D) (r : ℕ) (hr : V.rank = r) (β : GL (Fin r) (EAf D)) (Pg : Finset (Formalism.L2.DIV.Pl D.host.E)), IsLatBasis V hr β → (∀ w, w ∈ Pg ↔ l.Mb ≤ w.asIdeal) → l.Mb.IsRadical → ∀ (Dw : Datum H) (ι₀ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)), LatEmb V (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) → ∀ g : Formalism.L2.DIV.G0 Pg r, ∃ γ₀, Induces Dw l V hr ι₀ β Pg g γ₀ := by
  intro D H l V r hr β Pg hβ hPg hrad Dw ι₀ hι g
  obtain ⟨κ₀, h₀⟩ := GlobalTheory.T.level_group_lift_exists D H l V r hr β Pg hβ hPg g
  obtain ⟨c1, c2⟩ := GlobalTheory.T.level_lift_finite_congruence D H l V r hr β Pg hβ hPg
  have hk₀ := c1 g κ₀ h₀
  obtain ⟨γ₀, hγ⟩ := GlobalTheory.T.lattice_congruence_endomorphism D V Dw.La _ hι l.M (lt_of_lt_of_le (by norm_num) l.three_le) κ₀ hk₀
  refine ⟨γ₀, fun κ hκ a _ => ?_⟩
  obtain ⟨w', hw', e'⟩ := hγ a
  obtain ⟨w, hw, e⟩ := cong_latG_of_finCong (c2 hrad _ (isLift_inv_mul h₀ hκ))
    (hι.2 ▸ LinearMap.mem_range_self _ a :
      (LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) a ∈ latG V 1)
  refine ⟨(finHom V κ₀).1 *ᵥ w + w', add_mem ((GlobalTheory.Member.AALev.congruences_agree D V κ₀).1.2 hk₀ w hw) hw', ?_⟩
  change (finHom V κ).1 *ᵥ finVec V ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) a) -
    finVec V ((LinearMap.funLeft (𝓞 D.host.E) D.host.E (Fin.cast hr) ∘ₗ ι₀) (γ₀ a)) = _
  have e1 : (finHom V κ).1 = (finHom V κ₀).1 * (finHom V (κ₀⁻¹ * κ)).1 := by
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel_left]
  have e3 : (finHom V κ₀).1 *ᵥ (l.M • w) = l.M • (finHom V κ₀).1 *ᵥ w := map_nsmul (finHom V κ₀).1.mulVecLin l.M w
  rw [nsmul_add, ← e', ← e3, ← e, Matrix.mulVec_sub, Matrix.mulVec_mulVec, ← e1, sub_add_sub_cancel]

end GlobalTheory.GeoLevel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertEigenvaluesIffThetaLiftInertLabelsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertEigenvalues_iff_thetaLift_inertLabels : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → ∀ (j : Fin D.R.m) c c' (u u' : (A3.liftI j A3.A.μ0).OpIx → D.what₂.LL) (x x' : (A3.A.fam.L j A3.A.μ0).S.Forms), (∀ i, (A3.liftI j A3.A.μ0).opAll i x = u i • x) → (∀ i, (A3.liftI j A3.A.μ0).opAll i x' = u' i • x') → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ∈ R.Wc' j c → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ∈ R.Wc' j c' → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x) ≠ 0 → R.thG j A3.A.μ0 (R.jV j A3.A.μ0 x') ≠ 0 → ((∀ k, u (Sum.inr k) = u' (Sum.inr k)) ↔ (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D j) P d → c P d = c' P d)) := by
  first | exact @GlobalTheory.InertTransferW.inertEigenvalues_iff_thetaLift_inertLabels_alt | exact GlobalTheory.InertTransferW.inertEigenvalues_iff_thetaLift_inertLabels_alt | (intros; apply GlobalTheory.InertTransferW.inertEigenvalues_iff_thetaLift_inertLabels_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertIntegralTwistedConjugatesTwistedCentralizerStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_integral_twistedConjugates_twistedCentralizer_mul_maxCompact : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (w : Pl E), ¬ IsSplitAt w →
    ∀ y g : GLw n w, y ∈ GlobalTheory.LFun.KGL w n →
    (∃ u v : (w.adicCompletion E)[X], (∀ i, u.coeff i ∈ w.adicCompletionIntegers E) ∧
      (∀ i, v.coeff i ∈ w.adicCompletionIntegers E) ∧
      u * (nrmL n w y).val.charpoly + v * derivative (nrmL n w y).val.charpoly = 1) →
    g⁻¹ * y * thL n w g ∈ GlobalTheory.LFun.KGL w n → ∃ t ∈ twCent (thL n w) y, ∃ k ∈ GlobalTheory.LFun.KGL w n, g = t * k := by
  first | exact @GlobalTheory.InertUniq.eq_twCent_mul_KGL | exact GlobalTheory.InertUniq.eq_twCent_mul_KGL | (intros; apply GlobalTheory.InertUniq.eq_twCent_mul_KGL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertValuesIffInertLabelsCarriedEigensystemsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertValues_iff_inertLabels_carriedEigensystems : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, GlobalTheory.Chain.LiftInteg D → A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → SchurAll R.toRealDat → (∀ P, Good R.toRealDat A3.A.μ0 P → conjPl P = P → TwoSided R.toRealDat A3.A.μ0 P) → ((∀ t (k : A3.okI t × List ℕ), A3.heckeRI t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.R t).n y ∧ A3.heckeRI t k = A3.heckeRI t (k.1, y)) ∧ ∀ j t (k : A3.okI t × List ℕ), A3.heckeLI j t k = 0 ∨ ∃ y, Formalism.L2.Col.InertTypeOk (A3.A.fam.L j t).n y ∧ A3.heckeLI j t k = A3.heckeLI j t (k.1, y)) → (∀ p, ∀ w ∈ R.EEp3 p, LinearMap.adjoint (R.Th A3.A.μ0) w = 0 → w = 0) → ∀ (i : Fin D.R.m) (p p' : A3.fam3.base3.Ix) c c', R.Carries p c → R.Carries p' c' → ((∀ k : A3.okI A3.A.μ0 × List ℕ, p.1.2 (k.1.1, k.2) = p'.1.2 (k.1.1, k.2)) ↔ (∀ P d, Good R.toRealDat A3.A.μ0 P → conjPl P = P → IsLab (Wc D i) P d → c P d = c' P d)) := by
  first | exact @GlobalTheory.InertValLab.inert_vals_iff_labels | exact GlobalTheory.InertValLab.inert_vals_iff_labels | (intros; apply GlobalTheory.InertValLab.inert_vals_iff_labels <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveOfMapPderivEqAndMapOneNeZeroStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_of_map_pderiv_eq_and_map_one_ne_zero : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] {ι : Type} (Φ₀ : MvPolynomial ι ℂ →ₗ[ℂ] V)
    (d : ι → Module.End ℂ V), (∀ (i : ι) (p : MvPolynomial ι ℂ), Φ₀ (MvPolynomial.pderiv i p) = d i (Φ₀ p)) →
    Φ₀ 1 ≠ 0 → Function.Injective Φ₀ := by
  first | exact @GlobalTheory.FockAlg.injective_of_pderiv | exact GlobalTheory.FockAlg.injective_of_pderiv | (intros; apply GlobalTheory.FockAlg.injective_of_pderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableFullRankZetaStatement
section
open MeasureTheory GlobalTheory.SplitFlip
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_full_rank_zeta : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (n d : ℕ) (ν : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar ν →
    ∀ Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
    ∀ Y : Matrix (Fin n) (Fin d) k, Integrable (fun g : GL (Fin n) k =>
      Ψ (g.val * Y) * (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2)) (haarVol (GlobalTheory.SplitWeil.KO k (Fin n))) := by
  first | exact @GlobalTheory.FullRankCoinv.integrable_fibre_target | exact GlobalTheory.FullRankCoinv.integrable_fibre_target | (intros; apply GlobalTheory.FullRankCoinv.integrable_fibre_target <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnChernTransgressionTermPoincareGrowth
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_corrC : ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (V n)) (G₀ G₁ : V n → Matrix r r ℂ) (ρ : V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ offHyp S U, MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ offHyp S U, ∀ a i j, ‖conn G₁ v (coordVec a) i j‖ * poinWt S v a ≤ c) → (∀ v ∈ offHyp S U, ∀ a b i j, ‖curv G₁ v (coordVec a) (coordVec b) i j‖ * (poinWt S v a * poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (corrC ρ G₀ G₁) (offHyp S U) := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hsmall hG₀ hG₁ hconn hcurv hρ hρK
  obtain ⟨C, hC0, hCb⟩ := exists_bound_smooth_data U K G₀ ρ hU hK hKU hG₀ hρ
  set c' : ℝ := |c| + C + C * (|c| + C) with hc'
  have hposition : ∀ v ∈ offHyp S U, v ∈ K → ∀ j : Fin n, ∀ i a b p q,
      ‖intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j i a b p q‖ *
        (poinWt S v a * poinWt S v b) ≤ c' := by
    intro v hv hvK j i a b p q
    obtain ⟨-, hdb, hcn, hcv⟩ := hCb v hvK
    have hw01 := (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv.1)).1
    have hwa := hw01 a
    have hwb := hw01 b
    have hab : poinWt S v a * poinWt S v b ≤ 1 := mul_le_one₀ hwa.2 hwb.1 hwb.2
    have hab0 : 0 ≤ poinWt S v a * poinWt S v b := mul_nonneg hwa.1 hwb.1
    have hca : 0 ≤ |c| := abs_nonneg c
    have hCc : 0 ≤ C * (|c| + C) := mul_nonneg hC0 (add_nonneg hca hC0)
    unfold intersection_update_fsHerm_neg_one
    split_ifs with h1 h2
    · have := hcurv v hv a b p q
      simp only [curvAt]
      linarith [le_abs_self c]
    · simp only [cutForm, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, norm_mul]
      have e1 := hconn v hv a p q
      have e2 := hcn a p q
      have e3 := hdb b
      have hxy := norm_sub_le (conn G₁ v (coordVec a) p q) (conn G₀ v (coordVec a) p q)
      have hD0 := norm_nonneg (dbar (fun x => (ρ x : ℂ)) v (coordVec b))
      have hN0 := norm_nonneg (conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q)
      have hwab : poinWt S v a * poinWt S v b ≤ poinWt S v a := mul_le_of_le_one_right hwa.1 hwb.2
      have hY : ‖conn G₀ v (coordVec a) p q‖ * poinWt S v a ≤ C :=
        (mul_le_mul e2 hwa.2 hwa.1 hC0).trans (by rw [mul_one])
      have hS : (‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖) * poinWt S v a ≤ |c| + C := by
        calc _ ≤ (‖conn G₁ v (coordVec a) p q‖ + ‖conn G₀ v (coordVec a) p q‖) * poinWt S v a :=
              mul_le_mul_of_nonneg_right hxy hwa.1
          _ ≤ |c| + C := by rw [add_mul]; linarith [le_abs_self c]
      calc _ ≤ ‖dbar (fun x => (ρ x : ℂ)) v (coordVec b)‖ *
              ‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖ * poinWt S v a :=
            mul_le_mul_of_nonneg_left hwab (mul_nonneg hD0 hN0)
        _ = ‖dbar (fun x => (ρ x : ℂ)) v (coordVec b)‖ *
              (‖conn G₁ v (coordVec a) p q - conn G₀ v (coordVec a) p q‖ * poinWt S v a) := by ring
        _ ≤ C * (|c| + C) := mul_le_mul e3 hS (mul_nonneg hN0 hwa.1) hC0
        _ ≤ c' := by linarith
    · have := hcv a b p q
      simp only [curvAt]
      have : ‖curv G₀ v (coordVec a) (coordVec b) p q‖ * (poinWt S v a * poinWt S v b) ≤ C :=
        (mul_le_mul this hab hab0 hC0).trans (by rw [mul_one])
      linarith
  refine GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound S U K (corrC ρ G₀ G₁)
    ((n : ℝ) * ((Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c'| ^ n)) hU hK hKU hsmall ?_ ?_ ?_
  · intro v hv
    have hvU := hv.1
    have hρv : ContDiffAt ℝ 1 ρ v :=
      (hρ.contDiffAt (hU.mem_nhds hvU)).of_le (WithTop.coe_le_coe.2 le_top)
    exact (GlobalTheory.T.continuousAt_transgressionTopCoeffComplex hρv ((hG₀ v hvU).1.of_le (WithTop.coe_le_coe.2 le_top)) (hG₀ v hvU).2
      ((hG₁ v hv).1.of_le (WithTop.coe_le_coe.2 le_top)) (hG₁ v hv).2).continuousWithinAt
  · intro v hv hvK
    apply GlobalTheory.T.transgressionTopCoeffComplex_eq_zero_of_cutoff_zero
    have : U \ K ∈ 𝓝 v := (hU.sdiff hK.isClosed).mem_nhds ⟨hv.1, hvK⟩
    filter_upwards [this] with x hx
    exact hρK x hx.1 hx.2
  · intro v hv hvK
    have hwpos : ∀ a, 0 < poinWt S v a := (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv.1)).2 hv.2
    calc ‖corrC ρ G₀ G₁ v‖
        ≤ ∑ j : Fin n, ‖mixTop (intersection_update_fsHerm_neg_one (curvAt G₁ v) (cutForm ρ G₀ G₁ v) (curvAt G₀ v) j)‖ := norm_sum_le _ _
      _ ≤ ∑ _j : Fin n, (Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c'| ^ n *
            ∏ a, (poinWt S v a)⁻¹ ^ 2 :=
          Finset.sum_le_sum fun j _ => GlobalTheory.T.norm_polarisedTopChernCoeff_le_of_weighted_bound _ _ c' hwpos (hposition v hv hvK j)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnCutoffTopChernFormPoincareGrowth
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma mem_offHyp_iff {n : ℕ} {S : Finset (Fin n)}
    {U : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n} :
    v ∈ _root_.GlobalTheory.GoodTop.offHyp S U ↔ v ∈ U ∧ ∀ a ∈ S, v.ofLp a ≠ 0 := by
  unfold _root_.GlobalTheory.GoodTop.offHyp
  exact Iff.rfl

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in
private lemma continuousAt_cutoff_mul_mix_curvAt {n : ℕ} {r : Type} [Fintype r]
    [DecidableEq r] {G : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ} {ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ} {v : _root_.ReciprocityTheory.L2DbarEstimates.V n}
    (hG : _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G v) (hdet : IsUnit (G v).det) (hρ : ContinuousAt ρ v) :
    ContinuousAt (fun x => (ρ x : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G x)
      v := by
  refine ContinuousAt.mul (Complex.continuous_ofReal.continuousAt.comp (f := ρ) hρ) ?_
  refine _root_.GlobalTheory.GoodTop.continuousAt_mixTop (K := fun x _ => _root_.GlobalTheory.GoodTop.curvAt G x)
    fun i a b p q => ?_
  have h := hG.curv (j := 0) hdet
    (by rw [zero_add]; first | exact le_top | exact_mod_cast (le_top : ((2 : ℕ∞) ≤ ⊤)) | exact WithTop.coe_le_coe.2 le_top)
    (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) p q
  exact h.continuousAt

open MeasureTheory Filter Topology in
open scoped ContDiff Matrix in
set_option autoImplicit false in

theorem _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_curvAt :
    ∀ {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] (S : Finset (Fin n)) (U K : Set (_root_.ReciprocityTheory.L2DbarEstimates.V n)) (G₀ G₁ : _root_.ReciprocityTheory.L2DbarEstimates.V n → Matrix r r ℂ) (ρ : _root_.ReciprocityTheory.L2DbarEstimates.V n → ℝ) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U → (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ v ∈ U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₀ v ∧ IsUnit (G₀ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, _root_.GlobalTheory.HermFrame.MContDiffAt ∞ G₁ v ∧ IsUnit (G₁ v).det) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a i j, ‖_root_.GlobalTheory.HermFrame.conn G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) i j‖ * _root_.GlobalTheory.GoodMetric.poinWt S v a ≤ c) → (∀ v ∈ _root_.GlobalTheory.GoodTop.offHyp S U, ∀ a b i j, ‖_root_.GlobalTheory.HermFrame.curv G₁ v (_root_.GlobalTheory.GoodMetric.coordVec a) (_root_.GlobalTheory.GoodMetric.coordVec b) i j‖ * (_root_.GlobalTheory.GoodMetric.poinWt S v a * _root_.GlobalTheory.GoodMetric.poinWt S v b) ≤ c) → ContDiffOn ℝ ∞ ρ U → (∀ v ∈ U, v ∉ K → ρ v = 0) → IntegrableOn (fun v => (ρ v : ℂ) * _root_.GlobalTheory.GoodTop.mixTop fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) (_root_.GlobalTheory.GoodTop.offHyp S U) := by
  intro n r _ _ S U K G₀ G₁ ρ c hU hK hKU hS hG₀ hG₁ hconn hcurv hρ hρK
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn (hρ.continuousOn.mono hKU)
  refine _root_.GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound S U K _
    (C₀ * ((Fintype.card r : ℝ) ^ n * (n.factorial : ℝ) ^ 2 * |c| ^ n)) hU hK hKU hS ?_ ?_ ?_
  · intro v hv
    have hvU := (mem_offHyp_iff.1 hv).1
    exact (continuousAt_cutoff_mul_mix_curvAt (hG₁ v hv).1 (hG₁ v hv).2
      (hρ.contDiffAt (hU.mem_nhds hvU)).continuousAt).continuousWithinAt
  · intro v hv hvK
    rw [hρK v (mem_offHyp_iff.1 hv).1 hvK, Complex.ofReal_zero, zero_mul]
  · intro v hv hvK
    have hpos := (_root_.GlobalTheory.GoodTop.poinWt_mem_Icc_and_pos S v
      (hS v (mem_offHyp_iff.1 hv).1)).2 (mem_offHyp_iff.1 hv).2
    have hP := _root_.GlobalTheory.GoodTop.norm_mixTop_le_of_weighted
      (fun _ => _root_.GlobalTheory.GoodTop.curvAt G₁ v) (_root_.GlobalTheory.GoodMetric.poinWt S v) c hpos
      (fun _ a b p q => hcurv v hv a b p q)
    rw [norm_mul, Complex.norm_real]
    exact (mul_le_mul (hC₀ v hvK) hP (norm_nonneg _) ((norm_nonneg _).trans (hC₀ v hvK))).trans_eq
      (by ring)

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAntiholomorphicJacobianEqZeroPoincareGro
section
set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem continuousOn_det_dbar {n : ℕ} {Ω : Set (V n)} (hΩ : IsOpen Ω) {g : Fin n → V n → ℂ}
    (hg : ∀ i, ContDiffOn ℝ 2 (g i) Ω) :
    ContinuousOn (fun v => (Matrix.of fun i b => dbar (g i) v (coordVec b)).det) Ω := by
  have he : ∀ i (w : V n), ContinuousOn (fun v => dbar (g i) v w) Ω := by
    intro i w
    have hd := (hg i).continuousOn_fderiv_of_isOpen hΩ one_le_two
    simp only [dbar_apply]
    exact ((hd.clm_apply continuousOn_const).add
      ((hd.clm_apply continuousOn_const).const_smul Complex.I)).const_smul (1 / 2 : ℂ)
  have hM : ContinuousOn (fun v => Matrix.of fun i b => dbar (g i) v (coordVec b)) Ω :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun b => he i _
  exact (continuous_id.matrix_det).comp_continuousOn hM

theorem det_dbar_eq_zero_of_row {n : ℕ} {g : Fin n → V n → ℂ} {v : V n} (j : Fin n)
    (h : g j =ᶠ[𝓝 v] fun _ => 0) :
    (Matrix.of fun i b => dbar (g i) v (coordVec b)).det = 0 := by
  apply Matrix.det_eq_zero_of_row_eq_zero j
  intro b
  simp [dbar_congr h]

theorem integral_det_dbar_eq_zero_of_poincare : ∀ {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (f : Fin n → V n → ℂ)
    (j : Fin n) (u : Equiv.Perm (Fin n)) (c : ℝ), IsOpen U → IsCompact K → K ⊆ U →
    (∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → (∀ i, ContDiffOn ℝ 2 (f i) (offHyp S U)) →
    (∀ v ∈ offHyp S U, v ∉ K → f j v = 0) → (∀ v ∈ offHyp S U, v ∈ K → ‖f j v‖ * poinWt S v (u j) ≤ c) →
    (∀ v ∈ offHyp S U, v ∈ K → ∀ i b, ‖dbar (f i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ c) →
    IntegrableOn (fun v => (Matrix.of fun i b => dbar (f i) v (coordVec b)).det) (offHyp S U) ∧
      ∫ v in offHyp S U, (Matrix.of fun i b => dbar (f i) v (coordVec b)).det = 0 := by
  intro n S U K f j u c hU hK hKU hsmall hf hf0 hfb hdb
  have hΩ : IsOpen (offHyp S U) := GlobalTheory.T.isOpen_offCoordinateHyperplanes S U hU
  have hΩm : MeasurableSet (offHyp S U) := hΩ.measurableSet
  have hKc : IsClosed K := hK.isClosed
  have hwt : ∀ v ∈ offHyp S U, ∀ a, 0 < poinWt S v a := fun v hv =>
    (GlobalTheory.T.poincareCoordinateLength_mem_Icc_and_pos S v (hsmall v hv.1)).2 hv.2
  have hoff : ∀ g : Fin n → V n → ℂ, (∀ v ∈ offHyp S U, v ∉ K → g j v = 0) → ∀ v ∈ offHyp S U, v ∉ K →
      (Matrix.of fun i b => dbar (g i) v (coordVec b)).det = 0 := fun g hg v hv hvK =>
    det_dbar_eq_zero_of_row j (Filter.eventually_of_mem ((hΩ.sdiff hKc).mem_nhds ⟨hv, hvK⟩)
      fun x hx => hg x hx.1 hx.2)
  have hbd : ∀ (g : Fin n → V n → ℂ) (c' : ℝ), (∀ v ∈ offHyp S U, v ∈ K → ∀ i b,
      ‖dbar (g i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ c') → ∀ v ∈ offHyp S U, v ∈ K →
      ‖(Matrix.of fun i b => dbar (g i) v (coordVec b)).det‖ ≤
        (n.factorial : ℝ) * |c'| ^ n * ∏ a, (poinWt S v a)⁻¹ ^ 2 :=
    fun g c' h v hv hvK => GlobalTheory.T.norm_det_le_of_weighted_entry_bound _ u _ c' (hwt v hv) (h v hv hvK)
  have hint := GlobalTheory.T.integrableOn_offCoordinateHyperplanes_of_poincareBound S U K (fun v => (Matrix.of fun i b => dbar (f i) v (coordVec b)).det) _ hU hK hKU hsmall
    (continuousOn_det_dbar hΩ hf) (hoff f hf0) (hbd f c hdb)
  refine ⟨hint, ?_⟩
  obtain ⟨C, χ, hχs, hχ01, hχ0, hχ1, hχd⟩ := GlobalTheory.T.exists_logCutoff_coordinateHyperplanes_poincareBound S
  let F : ℕ → Fin n → V n → ℂ := fun k => Function.update f j (fun x => (χ k x : ℂ) * f j x)
  have hFj : ∀ k, F k j = fun x => (χ k x : ℂ) * f j x := fun k => by simp [F]
  have hFi : ∀ k i, i ≠ j → F k i = f i := fun k i hi => by simp [F, Function.update_of_ne hi]
  have hχC : ∀ k, ContDiffOn ℝ 2 (fun x => (χ k x : ℂ)) (offHyp S U) := fun k =>
    (Complex.ofRealCLM.contDiff.comp (by exact_mod_cast contDiff_infty.1 (hχs k) 2)).contDiffOn
  have hFs : ∀ k i, ContDiffOn ℝ 2 (F k i) (offHyp S U) := by
    intro k i
    by_cases hi : i = j
    · rw [hi, hFj]; exact (hχC k).mul (hf j)
    · rw [hFi k i hi]; exact hf i
  have hF0 : ∀ k, ∀ v ∈ offHyp S U, v ∉ K → F k j v = 0 := fun k v hv hvK => by
    rw [hFj]; simp [hf0 v hv hvK]
  have hzero : ∀ k, ∫ v in offHyp S U, (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det = 0 := by
    intro k
    have hsub : K ∩ tsupport (χ k) ⊆ offHyp S U := by
      rintro v ⟨hvK, hvt⟩
      refine ⟨hKU hvK, fun a ha h0 => ?_⟩
      exact (notMem_tsupport_iff_eventuallyEq.2 (hχ0 k v ⟨a, ha, h0⟩)) hvt
    refine GlobalTheory.T.integral_dbarJacobian_det_eq_zero_of_compactSupport (offHyp S U) (K ∩ tsupport (χ k)) (F k) j hΩ (hK.inter_right (isClosed_tsupport _))
      hsub (hFs k) ?_
    intro v hv hvn
    by_cases hvK : v ∈ K
    · have : v ∉ tsupport (χ k) := fun h => hvn ⟨hvK, h⟩
      rw [hFj]; simp [image_eq_zero_of_notMem_tsupport this]
    · exact hF0 k v hv hvK
  have hFb : ∀ k, ∀ v ∈ offHyp S U, v ∈ K → ∀ i b,
      ‖dbar (F k i) v (coordVec b)‖ * (poinWt S v (u i) * poinWt S v b) ≤ |c| + |C| * |c| := by
    intro k v hv hvK i b
    have hw := hwt v hv
    have hCc : 0 ≤ |C| * |c| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
    by_cases hi : i = j
    · rw [hi, hFj]
      have hvn := hΩ.mem_nhds hv
      rw [dbar_mul (a := fun x => (χ k x : ℂ)) (b := f j)
        (((hχC k).differentiableOn two_ne_zero).differentiableAt hvn)
        (((hf j).differentiableOn two_ne_zero).differentiableAt hvn) (coordVec b)]
      have h1 := hdb v hv hvK j b
      have h2 := hχd k v b
      have h3 := hfb v hv hvK
      have hχv := hχ01 k v
      have hp : 0 ≤ poinWt S v (u j) * poinWt S v b := mul_nonneg (hw _).le (hw _).le
      have hA : 0 ≤ ‖dbar (f j) v (coordVec b)‖ * (poinWt S v (u j) * poinWt S v b) :=
        mul_nonneg (norm_nonneg _) hp
      have hB : 0 ≤ ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b :=
        mul_nonneg (norm_nonneg _) (hw _).le
      have hE : 0 ≤ ‖f j v‖ * poinWt S v (u j) := mul_nonneg (norm_nonneg _) (hw _).le
      calc ‖(χ k v : ℂ) * dbar (f j) v (coordVec b) + dbar (fun x => (χ k x : ℂ)) v (coordVec b) * f j v‖ *
            (poinWt S v (u j) * poinWt S v b)
          ≤ (‖(χ k v : ℂ) * dbar (f j) v (coordVec b)‖ + ‖dbar (fun x => (χ k x : ℂ)) v (coordVec b) * f j v‖) *
            (poinWt S v (u j) * poinWt S v b) := mul_le_mul_of_nonneg_right (norm_add_le _ _) hp
        _ = χ k v * (‖dbar (f j) v (coordVec b)‖ * (poinWt S v (u j) * poinWt S v b)) +
            (‖dbar (fun x => (χ k x : ℂ)) v (coordVec b)‖ * poinWt S v b) * (‖f j v‖ * poinWt S v (u j)) := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hχv.1]; ring
        _ ≤ |c| + |C| * |c| := by
          refine add_le_add ?_ ?_
          · exact (mul_le_of_le_one_left hA hχv.2).trans (h1.trans (le_abs_self c))
          · exact mul_le_mul (h2.trans (le_abs_self C)) (h3.trans (le_abs_self c)) hE (abs_nonneg _)
    · rw [hFi k i hi]
      exact (hdb v hv hvK i b).trans ((le_abs_self c).trans (le_add_of_nonneg_right hCc))
  let bound : V n → ℝ := K.indicator fun v =>
    (n.factorial : ℝ) * |(|c| + |C| * |c|)| ^ n * ∏ a, (poinWt S v a)⁻¹ ^ 2
  have hbint : Integrable bound (volume.restrict (offHyp S U)) := by
    rw [integrable_indicator_iff hKc.measurableSet, IntegrableOn,
      Measure.restrict_restrict hKc.measurableSet]
    exact IntegrableOn.mono_set ((GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc S K hK fun v hv => hsmall v (hKU hv)).const_mul
      ((n.factorial : ℝ) * |(|c| + |C| * |c|)| ^ n)) Set.inter_subset_left
  have hmeas : ∀ k, AEStronglyMeasurable (fun v => (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det)
      (volume.restrict (offHyp S U)) := fun k =>
    (continuousOn_det_dbar hΩ (hFs k)).aestronglyMeasurable hΩm
  have hle : ∀ k, ∀ᵐ v ∂(volume.restrict (offHyp S U)),
      ‖(Matrix.of fun i b => dbar (F k i) v (coordVec b)).det‖ ≤ bound v := by
    intro k
    refine (ae_restrict_iff' hΩm).2 (Filter.Eventually.of_forall fun v hv => ?_)
    by_cases hvK : v ∈ K
    · simp only [bound, Set.indicator_of_mem hvK]
      exact hbd (F k) _ (hFb k) v hv hvK
    · simp only [bound, Set.indicator_of_notMem hvK]
      rw [hoff (F k) (hF0 k) v hv hvK, norm_zero]
  have hlim : ∀ᵐ v ∂(volume.restrict (offHyp S U)),
      Tendsto (fun k => (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det) atTop
        (𝓝 ((Matrix.of fun i b => dbar (f i) v (coordVec b)).det)) := by
    refine (ae_restrict_iff' hΩm).2 (Filter.Eventually.of_forall fun v hv => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hχ1 v hv.2] with k hk
    congr 1
    ext i b
    by_cases hi : i = j
    · simp only [Matrix.of_apply, hi, hFj]
      rw [dbar_congr (f := f j) (g := fun x => (χ k x : ℂ) * f j x) (hk.mono fun x hx => by simp [hx])]
    · simp only [Matrix.of_apply, hFi k i hi]
  have hT := tendsto_integral_of_dominated_convergence bound hmeas hbint hle hlim
  have h0 : (fun k => ∫ v in offHyp S U, (Matrix.of fun i b => dbar (F k i) v (coordVec b)).det) = fun _ => 0 :=
    funext hzero
  rw [h0] at hT
  exact tendsto_nhds_unique hT tendsto_const_nhds

end GlobalTheory.GoodTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralModuleOfCharPolyStatement
section
open Matrix GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_module_of_char_poly : ∀ (A : Type) [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H : A), (∀ i ∈ I, H * i ∈ I) → ∀ (N : ℕ) (c q : ℕ → A), c N = 1 → (∀ k ≤ N, c k ∈ Z) → (∀ u : ℂ, ∑ k ∈ Finset.range (N + 1), u ^ k • c k - (u • (1 : A) + H) * ∑ k ∈ Finset.range N, u ^ k • q k ∈ I) → IsIntMod Z I H := by
  first | exact @GlobalTheory.isIntMod_of_monic_dvd_affine | exact GlobalTheory.isIntMod_of_monic_dvd_affine | (intros; apply GlobalTheory.isIntMod_of_monic_dvd_affine <;> assumption)
end

