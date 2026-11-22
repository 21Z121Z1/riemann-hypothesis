import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0737
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0735
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0830
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0828
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0839
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0692
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0190
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0483
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0827
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0738
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0016
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemConnectedComponentOfOneOfPos
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0831
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0565
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0824

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointwiseHodge
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

namespace GlobalTheory.PointHodge

theorem chernTop_add {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n)
    (P Q : MvPolynomial (ι × ℕ) ℝ) : chernTop (P + Q) G v = chernTop P G v + chernTop Q G v := by
  simp only [chernTop, map_add, topCoeff, coeff_add, mul_add, Finset.sum_add_distrib, Complex.add_re]

theorem chernTop_smul {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ) (v : ReciprocityTheory.L2DbarEstimates.V n)
    (r : ℝ) (P : MvPolynomial (ι × ℕ) ℝ) : chernTop (r • P) G v = r * chernTop P G v := by
  have h : ∀ Q : MvPolynomial (Fin n × Fin n) ℂ, topCoeff (r • Q) = (r : ℂ) * topCoeff Q := fun Q => by
    simp only [topCoeff, coeff_smul, Complex.real_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  simp only [chernTop, map_smul, h, Complex.re_ofReal_mul]
  ring

noncomputable def chernLin {n : ℕ} {ι : Type} {m : ι → ℕ} (G : ReciprocityTheory.L2DbarEstimates.V n → FlagBundle.Mat m ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : MvPolynomial (ι × ℕ) ℝ →ₗ[ℝ] ℝ where
  toFun P := chernTop P G v
  map_add' P Q := chernTop_add G v P Q
  map_smul' r P := chernTop_smul G v r P

theorem pointwise_hodge : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ (Φ.C k).Y.dim) = chernRoots Dw.mult R * rootDiscr Dw.mult → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), chernTop R (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) * chernTop (pointPoly H Dw) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL la R hR y hy c' hyc A hA
  have hD : (Φ.C k).Y.dim = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) := by
    rw [Φ.dim_eq k, GlobalTheory.T.card_cmTypeEmbeddingsFixingRoot_eq_half_finrank E H]
  exact GlobalTheory.T.compactDual_linearForm_flagDegree_pointClass E H Dw la R X.dim (Φ.C k).Y.dim (chernLin (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y)) hD hR
    (fun Q d hQ hd => GlobalTheory.T.chernPolyTopDensity_eq_zero_of_weightedDegree_ne_dim _ _ _ _ _ Q d hQ hd) (fun τ Q => (GlobalTheory.T.chernPolyTopDensity_unit_and_above_rank _ _ _ _ _ τ Q).1) (fun τ k Q hk => (GlobalTheory.T.chernPolyTopDensity_unit_and_above_rank _ _ _ _ _ τ Q).2 k hk)
    (fun τ k' Q hk => GlobalTheory.T.hodgeMetric_chernDensity_lieGram_relation E H Dw l Xo c O β Y T F e σ U hσ hU Φ k X j f f₀ Eb A₀ hj hL y hy c' hyc A hA τ k' Q hk)

end GlobalTheory.PointHodge
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionSeriesB0
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.Up.PointwiseSettings
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem exists_Sx (D : D7) : ∃ Sx : Finset (PlE D.host), (∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑Sx) ∧
    OverSet D Sx (lowAll D) ∧ (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) := by
  have hne : ∀ p ∈ lowAll D, p ≠ 0 := by
    intro p hp
    simp only [lowAll, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl
    · exact lowPr_ne_zero D p hp
    · exact (D.host.g_prime 0).ne_zero
    · exact (D.host.g_prime 1).ne_zero
    · exact D.host.pde_prime.ne_zero
    · exact D.host.pde'_prime.ne_zero
  have hfin : (⋃ p ∈ (lowAll D : Set ℕ), placesOver D.host.E p).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => Formalism.L2.TwC.placesOver_finite' D.host.E p (hne p hp)
  refine ⟨hfin.toFinset, fun p hp Q hQ => ?_, fun Q hQ => ?_, fun Q Q' hQ hc => ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 hp) hQ
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact ⟨p, hp, hQp⟩
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact (Set.Finite.mem_toFinset hfin).2 (Set.mem_biUnion hp (placesOver_conj D p hQp hc))

open Formalism.L2.TwC in

theorem pointwise (hPr : PrN) (hSer : SerN) (hL : GlobalTheory.Published.LocalLanglandsGL) (cDep : ℝ) {K : Ctx} {B : Base}
    {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : LI hL x)
    (G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩)
    (hF : GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x))) (hOk : (GlobalTheory.BigTop.Fun.lamOf G).Ok)
    (hC : (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x) (hq : (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x)) :
    ∃ x' : St P, Nonempty (SettingsLevel hL x') ∧ ListSt cDep x' := by
  have hgal : GalEx (Dof x) :=
    GlobalTheory.HeightCounting.galEx_of_cgTrue hL hPr.what₂.fin hPr.what₂.gal (Dof x) l.a.A.wdT ⟨l.a.cg⟩
  have hcheb := GlobalTheory.ChebSplitDense.chebSplit_nd hPr.what₂.cheb (Dof x)
  obtain ⟨c0f, hf⟩ := GlobalTheory.T.row_cusp_multiplicity_input hPr.what₂.art (Dof x) (cfOf x) l.a.jE l.a.A l.rat.S l.rat.In (lowAll (Dof x)) l.Pq
    l.mt.M _ (QOf P) l.mt.mt l.Pq_over hgal l.cusp hcheb l.a.elem.star l.a.elem.int l.a.elem.split
  have hJ := fun (p : ℕ) [Fact p.Prime] (v : HeightOneSpectrum (𝓞 ↥(Dof x).LL0))
      (hv : ((p : ℕ) : 𝓞 ↥(Dof x).LL0) ∈ v.asIdeal) => Formalism.BasicNotions.Examples₂.LB.exists_embAt (l := p) v hv
  obtain ⟨c0r, hr⟩ := GlobalTheory.T.exists_twistRings_characters_classGroups hPr.what₂.art (Dof x) (cfOf x) (fun p _ v hv => (hJ p v hv).choose)
    (fun p _ v hv y => (hJ p v hv).choose_spec y) l.a.val l.a.elem.star l.a.elem.int
  let b0 : Big (Dof x) := fun p _ j =>
    ⟨(c0f p j).1 ⊔ (c0r p j).1, by haveI := (c0f p j).2; haveI := (c0r p j).2; infer_instance⟩
  obtain ⟨Sx, hSx1, hSx2, hSx3⟩ := exists_Sx (Dof x)
  obtain ⟨T', Sp, -⟩ := hr b0 b0 Sx (fun p _ j => le_sup_right)
  have hSbSx : l.rat.In.Sb ⊆ Sx := l.rat.rat.Sb_le.subset hSx1
  obtain ⟨F, ex, h0, hfg, hsb⟩ := hf b0 b0 Sx T' Sp (fun p _ j => le_sup_left) hSbSx hSx3 hSx1
  have hSxS0 : ∀ i, ∀ Q ∈ Sx, Q ∈ T'.S0 i := fun i Q hQ => by
    have h := Sp.ringSpec_excludedPlaces_eq i
    have : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := by
      rw [h]; exact Or.inr (Finset.mem_coe.2 hQ)
    exact Finset.mem_coe.1 this
  have hratio : ∀ i, ∀ y ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)),
      ∀ z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)), ‖y‖ ≤ ‖z‖ →
        y / z ∈ clC (T'.l i) (Kt (T'.l i) (Sp.K0 i) (Sp.Lw i)) := fun i => by
    have h := GlobalTheory.CycClosure.exists_cyclotomic_integers (T'.l i) (Sp.K0 i) (Sp.Lw i) 0
    have h0 : Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) ⊔ muK (T'.l i) 0 = Kt (T'.l i) (Sp.K0 i) (Sp.Lw i) := by
      rw [h.snd.2.2.2.2.1, sup_bot_eq]
    rw [h0] at h
    exact h.snd.2.2.2.1
  choose iC hiC using fun i => GlobalTheory.Mem.Df.exists_iC_of_clC (T'.l i) (T'.O i) _ (Sp.eO i) (hratio i)
  obtain ⟨L, hLam⟩ := GlobalTheory.T.exists_toricCharacters_in_twistCoefficientRings hPr.what₂.cheb hPr.what₂.art hSer.ratio (Dof x) l.a.A.bare (cfOf x) l.a.A.row
    (lowAll (Dof x)) l.Pq l.rat.S l.rat.In.hL l.rat.In.eig l.rat.In.θ b0 b0 Sx T' Sp (GlobalTheory.BigTop.Fun.lamOf G) hC hOk
    (GlobalTheory.BigTop.Fun.lamOf_teich G) l.a.val (fun a => hF.values (a.1 + 1) (by omega) a.2)
    (fun i Q hQ => by
      obtain ⟨p, hp, hQp⟩ := GlobalTheory.T.conductor_primes_in_low_set (Dof x) _ hOk hq Q hQ
      exact hSxS0 i Q (Finset.mem_coe.1 (hSx1 p hp hQp)))
  obtain ⟨htie, hside⟩ := hLam F
  obtain ⟨th0⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F (TwL.empty T')) ex
    (fun i => ⟨iC i, hiC i⟩) hfg
  obtain ⟨th1⟩ := GlobalTheory.HeightCounting.exists_nth_of_fg_full (Dof x) (T'.ntw l.a.A.bare F L) { ex with }
    (fun i => ⟨iC i, hiC i⟩) hfg
  have hB := hside ex h0 th0 (hsb th0) th1
  refine GlobalTheory.T.side_data_over_set_levels hL cDep x l ⟨T'.ntw l.a.A.bare F L, { ex with }, h0, th1, Sp.br, Sp.br_ind⟩ hB
    (fun i => hSbSx.trans fun Q hQ => hSxS0 i Q hQ) (fun i Q hQ => ?_) G hF hOk hC hq htie
  have h := Sp.ringSpec_excludedPlaces_eq i
  have hQ' : Q ∈ (T'.S0 i : Set (HeightOneSpectrum (𝓞 (Dof x).host.E))) := Finset.mem_coe.2 hQ
  rw [h] at hQ'
  simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_coe] at hQ'
  rcases hQ' with (((h1 | ⟨k, h1⟩) | h1) | h1) | h1
  · exact ⟨_, Finset.mem_insert_self _ _, h1⟩
  · refine ⟨(Dof x).host.g k, Finset.mem_insert_of_mem ?_, h1⟩
    fin_cases k <;> simp [lowAll]
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · exact ⟨_, Finset.mem_insert_of_mem (by simp [lowAll]), h1⟩
  · obtain ⟨p, hp, hQp⟩ := hSx2 Q h1
    exact ⟨p, Finset.mem_insert_of_mem hp, hQp⟩

theorem sb0l : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ∀ cDep : ℝ, SettingsFormsExistList hL cDep := by
  intro hPr hSer hL cDep
  exact (GlobalTheory.T.exists_character_grid_data hPr cDep).trans (StepW.of_all fun K B f T w _ _ h P x l => by
    obtain ⟨G, hF, hOk, hC, hq⟩ := h P x
    exact pointwise hPr hSer hL cDep x l G hF hOk hC hq)

end GlobalTheory.HeightCounting.Up.PointwiseSettings
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeriesRationalIntegral
section
namespace GlobalTheory

theorem seriesRatS_and_serInt_of_globalArtin :
    GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.SerStd.SeriesRatS ∧ GlobalTheory.IndefiniteRowSideFullHecke.TwistSeries.SerInt :=
  fun hA => ⟨GlobalTheory.T.thetaSeriesRationalOnGoodCovers_of_untwisted (GlobalTheory.Published.GlobalArtinReciprocity.rayClassFieldSt hA) GlobalTheory.T.untwisted_theta_rational_on_good_covers,
    GlobalTheory.T.thetaSeries_integral_uniform_prime_power⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ServedPlaceLevelsClassesComparisonMapsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.served_place_levels_classes_comparison_maps : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (_ : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      (∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m) →
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∃ (Lv : G.Levels (Fl u v hg))
        (clsS : ∀ j, Lv.compS j → ((Fl u v hg).Pj (j + 1)).Tup → ((w.D Z).chTw u ((w.D Z).what₂.muAt v)).cls (j + 1))
        (up : Formalism.L2.G.Cmp.CmpUp t.cmp (w.tw Z) u v hg Lv),
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ (a a' : Lv.compS j) (L L' : ((Fl u v hg).Pj (j + 1)).Tup),
          ((Fl u v hg).Pj (j + 1)).IsLatTup L → ((Fl u v hg).Pj (j + 1)).IsLatTup L' →
          (clsS j a L = clsS j a' L' ↔ a = a' ∧ ∃ γ : (Lv.levS j a).Γ, L' = (Lv.levS j a).smul γ L)) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → ∀ x, ∃ a L, ((Fl u v hg).Pj (j + 1)).IsLatTup L ∧ clsS j a L = x) ∧
        (∀ j, j + 1 ≤ (w.D Z).R.m → Submodule.span ((w.D Z).gat u v hg).O
          (up.cmpS j '' ((((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).L :
            Set (((w.tw Z).fm u ((w.D Z).what₂.muAt v)).lat (j + 1)).V)) = Lv.Int (j + 1)) := by
  first | exact @GlobalTheory.Mem.Top.KerOne.levels_cls_cmp_at_served | exact GlobalTheory.Mem.Top.KerOne.levels_cls_cmp_at_served | (intros; apply GlobalTheory.Mem.Top.KerOne.levels_cls_cmp_at_served <;> assumption)
end

