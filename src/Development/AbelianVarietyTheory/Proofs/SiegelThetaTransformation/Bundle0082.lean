import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.Bundle0009
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0047
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.UniformisationComponentLatticesMarkings
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0043
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0039
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.Bundle0081
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0016
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0112
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0015
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.DatEqZero
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0012
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0045
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0006
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0081
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0076

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsAnFibAllPoints
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

namespace GlobalTheory.Dict

theorem perFr_castFr_of_sameSp {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r}
    (h : SameSp X' X) (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    Formalism.L2.PjFree.perFr X' x v τ i = Formalism.L2.PjFree.perFr X (castFr h.psi x) v τ i := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  cases X'
  cases X
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem exists_anFib_all_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), 1 ≤ Dw.p + Dw.q → ∀ n : ℕ, Even n → ∃ s : c.F →+* ℂ, letI : Algebra c.F ℂ := s.toAlgebra; ∃ (r g : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw) (hr : X.p0 + Dw.p = r) (eL : LtN Dw n ≃ Harm.Var X.Ψ Dw.p X.p0 (Fin n)), IsSympl X bas ∧ r = Dw.p + Dw.q ∧ (∀ ℓ, letterDir X hr idx (eL ℓ) = Pi.single ℓ.2.2 (Pi.single (e.symm ⟨ℓ.1, ℓ.2.1⟩) 1)) ∧ (∀ j, rowType X (idx j) = relab c s (e j).1) ∧ ∀ y : FrPt Xo c ℂ, ∃ (y₀ : FrPt Xo c ℂ) (t : Ix Dw → ℂˣ) (x : Frame X.Ψ r) (L : Lt E r), FrBor t y₀ y ∧ x ∈ X.dom ∧ SelfD X L ∧ Nonempty (AnFib X bas idx e x L y₀) := by
  intro E _ _ _ H Dw l Xo c h1 n hn
  obtain ⟨ξ, hξ, hξ0, hneg⟩ := GlobalTheory.SpanInhab.exists_imag_neg H
  obtain ⟨Gm, φ, hφ⟩ := GlobalTheory.exists_herm_coord_of_datum E H Dw (-ξ)
    (by rw [show cc (-ξ) = -cc ξ by simp [cc], hξ]) (neg_ne_zero.2 hξ0) _ rfl
  have hσ : Formalism.L2.PjFree.GoodEmb c c.F.val.toRingHom := rfl
  generalize c.F.val.toRingHom = σ at hσ
  obtain ⟨U, hU, -, ⟨k₀⟩, -, hG, -⟩ :=
    GlobalTheory.FrameUnif.exists_unf_hasPrinc E H Dw l Xo c σ _ ξ Gm φ h1 hσ hξ hneg hφ
  obtain ⟨W⟩ := nonempty_uw hU
  have huw := GlobalTheory.Dict.uw_lattice E H Dw l Xo c σ _ U hσ hU h1 W
  have hsame : ∀ k, SameSp (U.X k) (U.X k₀) := fun k =>
    ⟨Finset.ext fun τ => ((hU.2.1 k).2 τ).trans ((hU.2.1 k₀).2 τ).symm, (hG k).1.trans (hG k₀).1.symm,
      (hU.2.1 k).1.trans (hU.2.1 k₀).1.symm, (hG k).2.trans (hG k₀).2.symm,
      by rw [(huw k).1, (huw k₀).1, (hG k).2, (hG k₀).2]⟩
  have hdom : Formalism.L2.Pj.Dom (fun _ : (E →+* ℂ) × ℕ => 0) n := ⟨fun _ => antitone_const, hn⟩
  choose Dc hDe using fun k => GlobalTheory.Dict.exists_dic E H Dw l c σ _ W.g n (U.X k) (fun _ => 0) W.e hσ rfl
    (hU.2.1 k).1 (hU.2.1 k).2 (huw k).2.1 hdom
  have hper : ∀ k x v j, pv (U.X k) (Dc k).idx x v j =
      Formalism.L2.PjFree.perFr (U.X k) x v (relab c σ (W.e j).1) (W.e j).2 := fun k x v j => by
    rw [(Dc k).per_eq, (hDe k).1]
  have hty : ∀ k j, rowType (U.X k) ((Dc k).idx j) = relab c σ (W.e j).1 := fun k j => by
    rw [(Dc k).ty_eq, (hDe k).1]
  refine ⟨σ, _, W.g, U.X k₀, (Dc k₀).bas, (Dc k₀).idx, W.e, (Dc k₀).hr, (Dc k₀).eL, (Dc k₀).sympl, rfl,
    fun ℓ => ?_, hty k₀, fun y => ?_⟩
  · rw [(Dc k₀).dir_eq, (hDe k₀).1]
  · let _ : Algebra c.F ℂ := σ.toAlgebra
    obtain ⟨k, x, t, hx, ht⟩ := (GlobalTheory.FrameNorm.exists_unitFr_frBor E H Dw l Xo c σ _ U hσ hU).2 y
    obtain ⟨A, -⟩ := GlobalTheory.Dict.uw_anFib E H Dw l Xo c σ _ U hσ hU h1 W k (Dc k).bas (Dc k).idx (Dc k).sympl
      (hper k) (hty k) x hx
    obtain ⟨e1, -, e2, A', -⟩ := GlobalTheory.Dict.anFib_move E H Dw l Xo c _ W.g (U.X k) (U.X k₀) (hsame k)
      (Dc k).bas (Dc k).idx (Dc k₀).bas (Dc k₀).idx W.e x.1 (U.X k).Λ (unC U k x) A 1 (Dc k).sympl (Dc k₀).sympl
      x.2 (huw k).2.1 (by simp [IsUn])
      (fun v => funext fun j => by rw [hper, hper, perFr_castFr_of_sameSp (hsame k)])
      (fun j => by rw [hty, hty])
    exact ⟨unC U k x, t, _, _, ht, e1, e2, ⟨A'⟩⟩

end GlobalTheory.Dict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSectionOneClassSeriesDescendsStatement
section
open AlgebraicGeometry CategoryTheory NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj GlobalTheory.Dict GlobalTheory.ClsVal
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_section_oneClass_series_descends : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (n : ℕ) (d : DeltaDat Xo c n), d.IsLev → d.l₂.A = l.A → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → ∀ (ψ : (LaI Xo c d ≃ₗ[𝓞 E] LaI Xo c d) →* c.Fˣ), d.PsiTie ψ → ∀ w : (Fin n → LevQ Dw d.l₂) → c.F, DatEq d ψ w → ∀ (Λ : GenLat E n) (N : ℕ), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ HHa Dw.mult n c.F ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) → ∃ f ∈ sec Xo c a n, IsThClsD Xo c d (fun _ : Unit => w) (fun _ => Λ) (fun _ => N) (fun _ => 1) 1 (fun _ => 1) LinearMap.id (fun _ => P) f := by
  first | exact @GlobalTheory.ClsDescent.exists_sec_oneClass | exact GlobalTheory.ClsDescent.exists_sec_oneClass | (intros; apply GlobalTheory.ClsDescent.exists_sec_oneClass <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatAtAndSpanAtOfHypC
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps GlobalTheory

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.RunLat

theorem thc_le_shortTh {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) : X.Thc s w ≤ X.shortTh w := by
  intro x hx
  simp only [PJ.Thc, PJ.scaled, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply] at hx
  obtain ⟨y, ⟨z, hz, rfl⟩, rfl⟩ := hx
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hz)

theorem spanAt_of_shortG {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} (X : WeightAlgebra.PJ D B P j)
    (s : 𝓞 B.KO) (w : WeightFamilies.Wt D j) (β : ℝ) (h : WeightAlgebra.ShortG X w (X.Thc s w) β) : PullbackSections.SpanAt X w := by

  obtain ⟨Sh, hSh, hspan, -⟩ := h
  show Submodule.span _ _ = ⊤
  rw [eq_top_iff, ← hspan]
  exact Submodule.span_mono fun x hx => thc_le_shortTh X s w (hSh hx)

theorem latAt_and_spanAt_of_hypC : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal (recB h.toLawsCore)) (ka wL wF : WeightFamilies.Wt D j) (Tn nP nW : ℕ) (h0 : ℝ) (nus : IsDedekindDomain.HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO) → ℝ), EtaleWeightGaps.HypC large₂ (recPlus h j hj) H C2 A2 CR Bx CT S ka wL wF Tn nP nW h0 nus → EtaleWeightGaps.LatAt (recB h.toLawsCore) j ka ∧ ∀ u ∈ ({wF, (recPlus h j hj).wF0 wL wF, ka} : Set (WeightFamilies.Wt D j)), PullbackSections.SpanAt (recPlus h j hj) u := by
  intro D T h j hj large₂ H C2 A2 CR Bx CT S ka wL wF Tn nP nW h0 nus hC
  obtain ⟨hPar, -, hScal, -, hH2, -, -, -⟩ := hC
  obtain ⟨-, -, -, hsK, -, po, -, -, PLam, -, -, hF, hF0, hK⟩ := hScal
  have hSpK : PullbackSections.SpanAt (recPlus h j hj) ka := spanAt_of_shortG _ _ _ _ hK
  refine ⟨GlobalTheory.latAt_record D _ h.toLawsCore (GlobalTheory.RunIn.gamAt_of_lawsCore' D _ h.toLawsCore) large₂ H.CA hPar
    j ka _ (recPlus h j hj) S wL wF hsK hSpK hH2, ?_⟩
  intro u hu
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with rfl | rfl | rfl
  · exact spanAt_of_shortG _ _ _ _ hF
  · exact spanAt_of_shortG _ _ _ _ hF0
  · exact hSpK

end GlobalTheory.RunLat
end

