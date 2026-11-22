import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0825
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0031
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0028
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0682
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0726
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0736
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0730
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0768
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0765
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0763
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0766
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0799
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0807
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0826
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0028
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0814
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2062
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0744
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyPtsOfReading
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisor
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0037
import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0694
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0732
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0802
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0770
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0686
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0689
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0420
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitenessOfHyp
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0707

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CentralLocalFrameAtMemberStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.central_local_frame_at_member : ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t _ _ c => ∀ (ad : MtAd t.r.Y c.a.all.gal.mt) (i : (w.st Z).toD7.nd.Loc) s k, t.r.Y.tup s = (w.st Z).toD7.nd.mu i → GlobalTheory.CenLocAt.FrameAt t.r.Y t.r.z.cG k (ad.PV k) s := by
  first | exact @GlobalTheory.CenLocAt.frameAt_of_layer | exact GlobalTheory.CenLocAt.frameAt_of_layer | (intros; apply GlobalTheory.CenLocAt.frameAt_of_layer <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompactDualLinearFormFlagDegreePointClass
section
namespace GlobalTheory.GrassTop
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem add_mul_pred_div_two : ∀ (a b : ℕ), (a + b) * (a + b - 1) / 2 = a * (a - 1) / 2 + b * (b - 1) / 2 + a * b := by
  have g : ∀ n : ℕ, (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
    intro n
    rw [Nat.add_sub_cancel]
    cases n with
    | zero => simp
    | succ k =>
      rw [Nat.add_sub_cancel, show (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) by ring,
        Nat.add_mul_div_left _ _ (by norm_num)]
  intro a b
  induction b with
  | zero => simp
  | succ b ih =>
    rw [← add_assoc, g (a + b), g b, ih]; ring

theorem pointPoly_isWeightedHomogeneous : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), IsWeightedHomogeneous Prod.snd (pointPoly H Dw) (Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q)) := by
  intro E _ _ _ H Dw
  unfold pointPoly
  have hs : Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) = ∑ τ : GlobalTheory.AllWt.Psi H, Dw.p * Dw.q := by simp
  rw [hs]
  apply IsWeightedHomogeneous.prod
  intro τ _
  have hm : Dw.mult τ.1 = Dw.p := by simp [Datum.mult, τ.2]
  rw [hm, show Dw.p + Dw.q - Dw.p = Dw.q by omega]
  have h1 : IsWeightedHomogeneous (Prod.snd : (E →+* ℂ) × ℕ → ℕ)
      (C ((-1 : ℝ) ^ Dw.p) * X (τ.1, Dw.p) : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) Dw.p := by
    simpa using (isWeightedHomogeneous_C (Prod.snd : (E →+* ℂ) × ℕ → ℕ) ((-1 : ℝ) ^ Dw.p)).mul
      (isWeightedHomogeneous_X ℝ (Prod.snd : (E →+* ℂ) × ℕ → ℕ) (τ.1, Dw.p))
  simpa [mul_comm] using h1.pow Dw.q

theorem antisymm_isHomogeneous : ∀ {ι : Type} [Fintype ι] {m : ι → ℕ} (P : MvPolynomial (Root m) ℝ) (d : ℕ), P.IsHomogeneous d → (antisymm P).IsHomogeneous d := by
  intro ι _ m P d h
  unfold GlobalTheory.GoodMetric.antisymm
  apply IsHomogeneous.sum
  intro w _
  have h1 := h.rename_isHomogeneous (f := fun x : Root m => (⟨x.fst, (w x.fst) x.snd⟩ : Root m))
  have h2 := (mem_homogeneousSubmodule _ _).mpr h1
  exact (mem_homogeneousSubmodule _ _).mp (Submodule.smul_of_tower_mem _ _ h2)

theorem intGr_sub {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (A B : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : intGr H Dw (A - B) = intGr H Dw A - intGr H Dw B := by
  unfold intGr Formalism.DegreeFormula.degFl
  simp only [map_sub, sub_mul, coeff_sub, mul_sub, Finset.sum_sub_distrib, sub_div]

theorem intGr_C_mul {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (c : ℝ) (A : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) : intGr H Dw (C c * A) = c * intGr H Dw A := by
  unfold intGr Formalism.DegreeFormula.degFl
  have hc : rho H Dw (C c) = C c := by
    simpa [MvPolynomial.algebraMap_eq] using (rho H Dw).commutes c
  have hc0 : chernRoots Dw.mult (C c) = C c := by
    simpa [MvPolynomial.algebraMap_eq] using (chernRoots Dw.mult).commutes c
  simp only [map_mul, hc0, hc, mul_assoc, coeff_C_mul]
  rw [mul_div_assoc']
  congr 1
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => by ring

theorem intGr_of_chernRoots_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Dw : Datum H) (A : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (h : chernRoots Dw.mult A = 0) :
    intGr H Dw A = 0 := by
  unfold intGr Formalism.DegreeFormula.degFl
  simp [h]

theorem grass_top : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (la : GlobalTheory.AllWt.Weight Dw) (R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (n D : ℕ) (L : MvPolynomial ((E →+* ℂ) × ℕ) ℝ →ₗ[ℝ] ℝ), D = Fintype.card (GlobalTheory.AllWt.Psi H) * ((Dw.p + Dw.q) * (Dw.p + Dw.q - 1) / 2) → antisymm ((∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) * MvPolynomial.X x) ^ D) = chernRoots Dw.mult R * rootDiscr Dw.mult → (∀ (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ) (d : ℕ), MvPolynomial.IsWeightedHomogeneous (Prod.snd : (E →+* ℂ) × ℕ → ℕ) Q d → d ≠ n → L Q = 0) → (∀ (τ : E →+* ℂ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), L ((MvPolynomial.X (τ, 0) - 1) * Q) = 0) → (∀ (τ : E →+* ℂ) (k : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), Dw.mult τ < k → L (MvPolynomial.X (τ, k) * Q) = 0) → (∀ (τ : GlobalTheory.AllWt.Psi H) (k : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), 1 ≤ k → L ((∑ a ∈ Finset.range (k + 1), MvPolynomial.C ((-1 : ℝ) ^ (k - a)) * MvPolynomial.X (τ.1, a) * MvPolynomial.X (conjEmb τ.1, k - a)) * Q) = 0) → L R = Formalism.DegreeFormula.flagDeg (GlobalTheory.AllWt.Psi H) (Dw.p + Dw.q) (fun τ i => (la τ i : ℝ)) * L (pointPoly H Dw) := by
  intro E _ _ _ H Dw la R n D L hD hR hdeg hJ0 hJk hrel

  have hL : ∀ Q ∈ relIdeal H Dw, L Q = 0 := by
    intro Q hQ
    have key : ∀ a, L (Q * a) = 0 := by
      refine Submodule.span_induction (p := fun x _ => ∀ a, L (x * a) = 0) ?_ ?_ ?_ ?_ hQ
      · rintro x ((⟨τ, rfl⟩ | ⟨τ, k, hk, rfl⟩) | ⟨τ, k, hk, rfl⟩) a
        · exact hJ0 τ a
        · exact hJk τ k a hk
        · exact hrel τ k a hk
      · intro a; simp
      · intro x y _ _ hx hy a; rw [add_mul, map_add, hx, hy, add_zero]
      · intro b x _ hx a; rw [smul_eq_mul, mul_comm b x, mul_assoc]; exact hx _
    simpa using key 1
  have hker : ∀ Q, chernRoots Dw.mult Q = 0 → L Q = 0 := by
    intro Q hQ
    apply hL
    refine Ideal.span_mono ?_ (GlobalTheory.T.mem_span_of_chernClassesOfRoots_eq_zero Dw.mult Q hQ)
    exact Set.subset_union_left
  set e := Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * Dw.q) with he
  set δ := Fintype.card (GlobalTheory.AllWt.Psi H) * (Dw.p * (Dw.p - 1) / 2 + Dw.q * (Dw.q - 1) / 2) with hδ

  have hRh : (chernRoots Dw.mult R).IsHomogeneous e := by
    refine GlobalTheory.T.isHomogeneous_of_mul_isHomogeneous_of_ne_zero_right _ _ e δ (by apply GlobalTheory.GoodMetric.rootDiscr_ne_zero) (GlobalTheory.T.flagRelativeTangentTopChern_isHomogeneous_cmType H Dw) ?_
    rw [← hR]
    have hed : e + δ = D := by
      rw [hD, he, hδ, add_mul_pred_div_two]; ring
    rw [hed]
    apply antisymm_isHomogeneous
    have hlin : (∑ x : Root Dw.mult, MvPolynomial.C (-(GlobalTheory.AllWt.exOf Dw la 0 (some x) : ℝ)) *
        MvPolynomial.X x).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ fun x _ => isHomogeneous_C_mul_X _ _
    simpa using hlin.pow D
  set Re := weightedHomogeneousComponent (Prod.snd : (E →+* ℂ) × ℕ → ℕ) e R with hRe
  have hReW : IsWeightedHomogeneous (Prod.snd : (E →+* ℂ) × ℕ → ℕ) Re e :=
    weightedHomogeneousComponent_isWeightedHomogeneous _ _
  have hrest : chernRoots Dw.mult (R - Re) = 0 := by
    have hc : ∀ d, homogeneousComponent d (chernRoots Dw.mult (R - Re)) = 0 := by
      intro d
      rw [GlobalTheory.T.homogeneousComponent_chernClassesOfRoots, map_sub]
      by_cases hd : d = e
      · rw [hd, hReW.weightedHomogeneousComponent_same]
        simp [hRe]
      · rw [map_sub, ← GlobalTheory.T.homogeneousComponent_chernClassesOfRoots, homogeneousComponent_of_mem ((mem_homogeneousSubmodule _ _).mpr hRh), if_neg hd,
          weightedHomogeneousComponent_of_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).mpr hReW), if_neg hd,
          map_zero, sub_zero]
    rw [← sum_homogeneousComponent (chernRoots Dw.mult (R - Re))]
    exact Finset.sum_eq_zero fun d _ => hc d
  have hLR : L R = L Re := by
    have := hker _ hrest
    rw [map_sub, sub_eq_zero] at this
    exact this
  have hIR : intGr H Dw R = intGr H Dw Re := by
    have := intGr_of_chernRoots_eq_zero H Dw _ hrest
    rw [intGr_sub, sub_eq_zero] at this
    exact this
  by_cases hn : n = e
  · obtain ⟨c, hc⟩ := GlobalTheory.T.grassmannProduct_topDegree_eq_smul_pointClass H Dw Re hReW
    have h1 := hL _ hc
    rw [map_sub, sub_eq_zero, C_mul', map_smul, smul_eq_mul] at h1
    have h2 := GlobalTheory.T.grassmannProductIntegral_eq_zero_of_mem_relIdeal H Dw _ hc
    rw [intGr_sub, intGr_C_mul, GlobalTheory.T.grassmannProductIntegral_pointClass_eq_one, mul_one, sub_eq_zero] at h2
    rw [hLR, h1, ← h2, ← hIR, GlobalTheory.T.grassmannProductIntegral_eq_flagDegree_weight H Dw la R D hD hR]
  · have h1 : L Re = 0 := hdeg Re e hReW (Ne.symm hn)
    have h2 : L (pointPoly H Dw) = 0 := hdeg _ e (pointPoly_isWeightedHomogeneous H Dw) (Ne.symm hn)
    rw [hLR, h1, h2, mul_zero]

end GlobalTheory.GrassTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ComparisonDataStepsNonReferenceTupleStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparison_data_steps_non_reference_tuple : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
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
      (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0 →
      ∃ (Lv : G.Levels (Fl u v hg)) (I : Formalism.MainNotions.G.CmpJ.CmpJIn (w.tw Z) u ((w.D Z).what₂.muAt v) v hg Lv),
        Formalism.MainNotions.G.CmpJ.CmpJHyp t.cmp I ∧
        (∀ j hj, (I.at' j hj).C = (w.D Z).chTw u ((w.D Z).what₂.muAt v)) ∧
        (∀ j hj, Formalism.MainNotions.G.KAat.ChX (I.at' j hj).st) ∧
        (∀ j, (w.D Z).R.m ≤ j → IsEmpty (Lv.compS j)) := by
  first | exact @GlobalTheory.Mem.Top.KerTwLv.cmpJ_data_ne | exact GlobalTheory.Mem.Top.KerTwLv.cmpJ_data_ne | (intros; apply GlobalTheory.Mem.Top.KerTwLv.cmpJ_data_ne <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseOfFlagCpt
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem GlobalTheory.LieBase.exists_base_of_flagCpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∃ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (E' : Fr (ratOf (Φ.C k).Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] (Φ.C k).Y.Fn), (j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str) ∧ IsLieBase e (Φ.C k) X j f f₀ Eb A₀ ∧ Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => (Φ.C k).gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k
  obtain ⟨X, j, hoi, hj, hr⟩ := GlobalTheory.T.exists_variety_connectedComponent_genericFibre E H Dw l Xo c O β T.Z F e T.smooth (Φ.C k).Y (Φ.C k).π (Φ.C k).π_str
  let f : (Φ.C k).Y.X ⟶ X.X := IsOpenImmersion.lift j (Φ.C k).π hr
  have hf : f ≫ j = (Φ.C k).π := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨f₀, Eb, A₀, hT⟩ := GlobalTheory.ShFam.TieBase.exists_tied E H Dw l Xo c O β T.Z F e X j hj
  have hcar := GlobalTheory.T.flagSpace_component_unique_point_each_flag E H Dw l Xo c O β T.Z F e σ _ U Φ k X j hoi hj f hf
  obtain ⟨E', φ, hR, hG⟩ := GlobalTheory.T.flagSpaceComponent_refines_lie_frames_graded E H Dw l Xo c O β T.Z F e (Φ.C k) X j hoi hj f hf f₀ Eb A₀ hT
    (fun K _ _ χ x hx g => hcar K χ x hx g)
  exact ⟨X, j, f, f₀, Eb, A₀, E', φ, hj, ⟨hoi, hf, hT⟩, hR, hG⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterGridData
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeightCounting.Up.GridLg

theorem lamOf_ok (D : D7) {T : Type} (L : Formalism.IndefR.Links.LevCh D T) (cDep b : ℝ) (G : GlobalTheory.ChiGrid.GridData L ⟨1, cDep, b⟩)
    (w0 : HeightOneSpectrum (𝓞 D.host.E)) (h : GlobalTheory.LamTie.PlacesOk D.host (AbsolutelyIrreducibleSpan.q0 D) w0) :
    (GlobalTheory.BigTop.Fun.lamOf G).Ok := by
  classical
  refine ⟨⟨?_, h.distinct, h.splits⟩, GlobalTheory.T.lamOf_chi_is_chosen_hecke_character_of_placesOk D L _ G w0 h, fun j a g => ?_⟩
  · have h1 := G.pl.basePlace_over_qZero
    have h2 := G.pl.w_over G.pl.v0 (Finset.mem_insert_self _ _)
    show ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w G.pl.v0).asIdeal
    have h3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((GlobalTheory.ChiGrid.q0 D : ℕ) : 𝓞 D.host.F) ∈ (G.pl.w G.pl.v0).asIdeal := by
      rw [← h2] at h1; exact h1
    rwa [map_natCast] at h3
  · exact GlobalTheory.BigTop.Fun.nFun_add_one_lt_eExp_add_cen 1 j a g

theorem exists_grid : PrN → ∀ cDep : ℝ, AllSt fun K _ _ _ _ _ x =>
    ∃ G : GlobalTheory.ChiGrid.GridData x.m.z.R.toRealDat.toLevCh ⟨1, cDep, K.s.b⟩, GlobalTheory.BigTop.Fun.FieldHas G (embLL0 (Dof x)) ∧
      (GlobalTheory.BigTop.Fun.lamOf G).Ok ∧ (GlobalTheory.BigTop.Fun.lamOf G).C = cfOf x ∧ (GlobalTheory.BigTop.Fun.lamOf G).q0 = AbsolutelyIrreducibleSpan.q0 (Dof x) := by
  intro _ cDep
  have hd : AllSt fun K _ _ _ _ _ x => ∃ w0, GlobalTheory.LamTie.PlacesOk (Dof x).host (AbsolutelyIrreducibleSpan.q0 (Dof x)) w0 :=
    (Step.of_evLgG GlobalTheory.T.eventually_sizes_congruences_hostFacts_columnChoices).trans (Step.of_all fun K B f T _ hk _ H w _ P x => (H hk T w x.o.Z).2.2.2.2.2.2)
  refine (StepW.and (GlobalTheory.T.exists_grid_unit_gap_field_contains_values cDep) hd).trans (StepW.of_all fun K B f T w _ _ H P x => ?_)
  obtain ⟨G, hG⟩ := H.1 P x
  obtain ⟨w0, h0⟩ := H.2 P x
  exact ⟨G, hG, lamOf_ok _ _ _ _ G w0 h0, x.m.z.lev.C.trans rfl, rfl⟩

end GlobalTheory.HeightCounting.Up.GridLg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantOrbitCentreMarkingPolyFanStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_orbitCentre_marking_polyFan : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)),
    (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) →
    IsPolyFan H.bar q φ → IsTwInv H φ → IsTwInv H lab → SimpLab H.bar q φ lab → ∀ M : ℕ, 2 ≤ M →
    maxMult H.bar q φ ≤ M → ∀ c : FormFamily (𝓞 E),
    ∃ w : InvFun (𝓞 E), IsTwInv H w ∧ IsCentreSet H.bar q φ w ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), IsMultCell H.bar φ M δ → c.Carries δ →
          ∃ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) ∧ w.evalZ β = 1 ∧ InRCone δ β) ∧
      (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
        Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell H.bar φ δ),
          LinearIndependent ℤ δ → (∀ i, IsPrim H.bar (⟨δ i, h.mem i⟩ : balForms H.bar X)) →
          ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
          ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1) := by
  first | exact @GlobalTheory.PolFan.OrbMark.centres_exists | exact GlobalTheory.PolFan.OrbMark.centres_exists | (intros; apply GlobalTheory.PolFan.OrbMark.centres_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLb2OfThetaTieStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lb2_of_theta_tie : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {P : Pre2 K w} (x : St P) (l : SeriesLevel hL x) (th : NTh (Dof x).R (Dof x).host (Dof x).what₂ (Dof x).LL0 (Dof x).nd (Dof x).ntw (Dof x).nexp), GlobalTheory.GeoTie.ThetaTie l.b.YS x.m.z.geo.fw th → ∃ x' : St P, Nonempty (StrictHenselianAcyclic hL x') ∧ x'.o = oTw x (thTw (Dof x) th) ∧ HEq x'.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x.o.Z) (oTw x (thTw (Dof x) th)).Z x.m.z.R.toRealDat.toLevCh) := by
  first | exact @GlobalTheory.HeightCounting.Up.points_carry | exact GlobalTheory.HeightCounting.Up.points_carry | (intros; apply GlobalTheory.HeightCounting.Up.points_carry <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsModelPresentingDivisorStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_model_presenting_divisor : HTBoundSt → ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (fl : s.Flag), AdmEx S κ → ∀ (k : s.Comp) (w : Sym D.host.E →₀ ℤ), (∀ a ∈ w.support, {q | a.1 q = true}.Finite) → ∃ (M : GlobalTheory.TrueGeo.Model (fl.C k).Y) (L : LB M.X) (m : ℕ+) (r : (L.pull M.j).ι → (fl.C k).Y.Fnˣ), L.IsLB ∧ Presents ((m : ℕ) • divOf (fl.C k) (expo S.Dw w)) (L.pull M.j) r ∧ ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)) (e : Ext v) (y : AlgPt (fl.C k).Y) (yt : Sp e.O ⟶ M.X) (i : (L.pull M.j).ι), spMap e.O.subtype ≫ yt = y.1 ≫ M.j → ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) → ((m : ℕ) : ℝ) * lgOf (fl.C k) w v e y = Real.log (e.w (valAt y.1 (((eqn (divOf (fl.C k) (expo S.Dw w)) (below y.1))⁻¹ ^ (m : ℕ) * r i : (fl.C k).Y.Fnˣ) : (fl.C k).Y.Fn))) := by
  first | exact @GlobalTheory.LineNorm.exists_model_lgOf | exact GlobalTheory.LineNorm.exists_model_lgOf | (intros; apply GlobalTheory.LineNorm.exists_model_lgOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan

theorem exists_starSubdivision : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsTwInv H ψ → IsTwInv H w → IsCentreSet H.bar q ψ w → ∃ ψ' : InvFun (𝓞 E), IsPolyFan H.bar q ψ' ∧ IsTwInv H ψ' ∧ Subordinate H.bar q ψ' ψ ∧ IsStarOf H.bar q ψ w ψ' := by
  intro E _ _ _ H q ψ w hDom hψ htψ htw hW
  obtain ⟨K, D, hK, hD, hint, hs1, hs2⟩ := GlobalTheory.T.exists_starSubdivision_function_integral_strictly_concave E H q ψ w hDom hψ hW
  obtain ⟨hl1, hl2⟩ := GlobalTheory.T.starSubdivision_function_linearOn_cells E H q ψ w K D hW
  have c1 : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ →
        (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) →
        IsCell H.bar (starFun H.bar ψ w K D) γ :=
    fun X _ _ _ _ hX m γ hγ hno => ⟨hγ.mem, hγ.nonneg, hl1 X hX m γ hγ hno, hs1 X hX m γ hγ hno⟩
  have c2 : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ →
        ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ →
        ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
        IsCell H.bar (starFun H.bar ψ w K D) (Fin.cons β₀ fun j => γ (s j)) := by
    intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos
    refine ⟨fun i => ?_, fun i y => ?_, hl2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos,
      hs2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hβ₀
      · simpa using hγ.mem (s j)
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hp y
      · simpa using hγ.nonneg (s j) y
  have hstar : IsStarOf H.bar q ψ w (starFun H.bar ψ w K D) := GlobalTheory.T.isStarOf_of_cells_starCone_or_centreless E H q ψ w _ hψ hW c1 c2
  have hpos : ∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X],
      Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 →
        0 < (starFun H.bar ψ w K D).evalZ β := by
    intro X _ _ _ _ hX β hβ hp h0
    rw [starFun_evalZ]
    have h1 := (hψ X hX).pos β hβ hp h0
    have h2 : 0 ≤ (starDepth H.bar ψ w).evalZ β := starDepth_eval_nonneg _
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    positivity
  exact ⟨starFun H.bar ψ w K D, GlobalTheory.T.isPolyFan_of_starSubdivision_cells E H q ψ w _ hψ hW hstar hint hpos,
    isTwInv_starFun H htψ (GlobalTheory.T.starSubdivisionDepth_hostFixingAut_invariant E H ψ w htψ htw) K D, GlobalTheory.T.starSubdivision_subordinate_to_fan _ H.bar q ψ w _ hstar, hstar⟩

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTiedDataReciprocity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

open Formalism.L2 in
set_option maxHeartbeats 1000000 in

theorem tiedDataS_assemble {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D}
    {K : Formalism.MainNotions.G.Consts} {Y : DivX D} {cX : ExtraC} (ex : Extra D L hT Gi Gl K Y cX)
    (host : Formalism.L2.Host.HostTied D) (level : Formalism.L2.Host.LevelTied D) (cols : Formalism.L2.Forms.ColsTiedSym D) (full : Formalism.L2.Forms.ColsFullS cols)
    (extra : Formalism.L2.Forms.ColsExtraTiedS full ex) (provA : Formalism.BasicNotions.TH.ProvA) (theta : Formalism.L2.Theta.AllTied D ex.th provA) (twIn : Formalism.MainNotions.TwIn D)
    (n : Formalism.L2.NormalizedTwistCompatibility D ex.nch twIn) (frameN : ∀ x, n.gal.fr.jE x = host.fr.j x)
    (cf : Formalism.L2.Host.CharFrame D) (tp : Formalism.L2.Host.TupTied D cf ex.nch)
    (h : (⟨n.cf, n.tp⟩ : Σ c : Formalism.L2.Host.CharFrame D, Formalism.L2.Host.TupTied D c ex.nch) = ⟨cf, tp⟩)
    (thetaChr : Formalism.L2.Host.ThetaChrTied D cf ex.nch tp ex.th) (chrVal : Formalism.L2.Host.ValLL0 D cf) (chrDt : Formalism.L2.Host.DtTied D cf)
    (chrN : Formalism.L2.Host.NCharTied D cf ex.nch tp) (chrGal : Formalism.L2.Host.NGalChrTied D cf ex.nch tp)
    (chrPsi : Formalism.L2.Host.PsiChoiceCompatible D cf ex.nch tp) (sameChr : Formalism.L2.JoinChr.SameChr theta.T thetaChr)
    (what₂ : Formalism.L2.Rows.RowsCompatible D host cf tp) (inK : Y.Lev → ℕ → Prop) (geo : Formalism.L2.Geo.GeoTiedP Y inK)
    (tw0 : TwForms D) (he : ex.tw = tw0) (tw : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes tp cols tw0) (emt : Formalism.L2.Rows.EMtTied D cols tw)
    (g : Formalism.L2.G.GroupCompatibilityAll D hT ex.cmp) (herm_eq : g.herm = full.1.to0) (forms_eq : g.forms = fun u => (cols.forms u).to0)
    (P : ∀ (c : Formalism.L2.Host.CharFrame D) (t : Formalism.L2.Host.TupTied D c ex.nch) (C : Formalism.L2.Forms.ColsTiedSym D), Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes t C tw0 → Prop)
    (hP : P cf tp cols tw) :
    ∃ S : Formalism.L2.LinkedFamilyData ex, S.host = host ∧ S.cols = cols ∧ HEq S.full full ∧ S.g = g ∧
      (⟨S.provA, S.theta⟩ : Σ a, Formalism.L2.Theta.AllTied D ex.th a) = ⟨provA, theta⟩ ∧
      (⟨S.twIn, S.n⟩ : Σ I, Formalism.L2.NormalizedTwistCompatibility D ex.nch I) = ⟨twIn, n⟩ ∧ HEq S.thetaChr thetaChr ∧
      (∀ a, S.chrDt.eDt a = chrDt.eDt a) ∧
      (S.what₂.O.pieces.rcf = what₂.O.pieces.rcf ∧ S.what₂.O.pieces.MDel = what₂.O.pieces.MDel) ∧
      S.inK = inK ∧ HEq S.geo geo ∧ P _ _ _ (he ▸ S.tw) := by
  cases h
  subst he
  first
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, frameN := frameN, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩
  | exact ⟨{ host := host, level := level, cols := cols, full := full, extra := extra, provA := provA, theta := theta,
               twIn := twIn, n := n, thetaChr := thetaChr, chrVal := chrVal, chrDt := chrDt, chrN := chrN,
               chrGal := chrGal, chrPsi := chrPsi, sameChr := sameChr, what₂ := what₂, inK := inK, geo := geo, tw := tw, emt := emt,
               g := g, herm_eq := herm_eq, forms_eq := forms_eq },
        rfl, rfl, HEq.rfl, rfl, rfl, rfl, HEq.rfl, fun _ => rfl, ⟨rfl, rfl⟩, rfl, HEq.rfl, hP⟩

theorem ColW.cf_eq {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T) (Z : w.Lt) :
    Fr.at (w.st Z) f = TC.cf w.I w.l Z := by
  have h := w.C_eq
  have : Fr.at (w.st Z) w.I.C = TC.cf w.I w.l Z := rfl
  rw [← this, h]

set_option maxHeartbeats 2000000 in

theorem WPt.tiedDataS_pinned : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.WeberRayFieldSt → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL) (K : Ctx) (q : WPt p.s K), Formalism.L2.Host.LevelTied (q.w.D q.Z) → Formalism.L2.Rows.ZetaCompatible (q.w.D q.Z) → ∃ S : Formalism.L2.LinkedFamilyData q.O.ex, SPin q S := by
  intro hA hW hL p K q hlev hze
  obtain ⟨extra, g, hg, hherm, hforms⟩ := WPt.extraTied_col p.s K q
  obtain ⟨I, n, hE, hgood, hchr, h1, h2, h3, h4, h5, h6, h7, h8⟩ := nTiedAll_atWit hL p K q
  obtain ⟨he, tw, hstd, emt⟩ := GlobalTheory.Mem.Top.Bl.WPt.colsTwTied p.s K q
  obtain ⟨dt, hdt⟩ := TC.dtTied_true q.w.I q.w.ok q.w.pins q.w.l q.Z
  have hO : ∃ O : Formalism.L2.Rows.OTied (q.w.D q.Z) q.core.a.host (TC.cf q.w.I q.w.l q.Z),
      O.pieces.rcf = GlobalTheory.Mem.HD.qb q.core.a.host.fr.ι q.w.δ.ray ∧ O.pieces.MDel = GlobalTheory.Mem.HD.qb q.core.a.host.fr.ι q.w.δ.M' := by
    generalize q.core.a.host = H
    rw [← ColW.cf_eq]
    exact GlobalTheory.Mem.CyclotomicFieldContainment.oTied_of_ksExact hA hW (q.w.st q.Z) q.f q.w.δ q.w.exact H
  obtain ⟨O, hO1, hO2⟩ := hO
  have hval : Formalism.L2.Host.ValLL0 (q.w.D q.Z) (TC.cf q.w.I q.w.l q.Z) := by
    rw [← ColW.cf_eq]
    exact q.w.val _ _ _ _ _ _
  have hfr : ∀ x, n.gal.fr.jE x = q.core.a.host.fr.j x := by
    rw [h1]
    exact q.core.a.frameN
  obtain ⟨S, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12⟩ :=
    tiedDataS_assemble q.O.ex q.core.a.host hlev q.x.col.C q.x.col.full extra q.x.th.provA q.x.th.all I n hfr
      (TC.cf q.w.I q.w.l q.Z) q.x.n.tp hchr q.x.th.chr hval dt q.core.a.chrN q.core.a.chrGal q.x.n.chrPsi q.x.th.same
      ⟨O, q.O.ex.kap_def, hze⟩ q.x.div.inK q.x.div.geo (q.w.tw q.Z) he tw emt g hherm hforms
      (fun _ _ _ t => TC.StdTw q.w.I q.w.l q.Z q.w.l0 t) hstd
  have key : ∀ Q : (Σ I, Formalism.L2.NormalizedTwistCompatibility (q.w.D q.Z) q.O.ex.nch I) → Prop, Q ⟨I, n⟩ → Q ⟨S.twIn, S.n⟩ :=
    fun Q hQ => s6 ▸ hQ
  refine ⟨S, s1, s2, s3, s4 ▸ hg, s5, key (fun z => z.1.E = _) hE, key (fun z => DQ.GoodAllAt _ _ z.1) hgood,
    key (fun z => (⟨z.2.cf, z.2.tp⟩ : Σ c : CharFrame (q.w.D q.Z), TupTied (q.w.D q.Z) c q.O.ex.nch) = _) hchr,
    key (fun z => z.2.gal = _) h1, key (fun z => z.2.n = _) h2, key (fun z => z.2.exp = _) h3,
    key (fun z => z.2.chiD = _) h4, key (fun z => z.2.twF = _) h5, key (fun z => HEq z.2.types _) h6,
    key (fun z => HEq z.2.cover _) h7, key (fun z => z.2.plB = _) h8, s7, fun a => (s8 a).trans (hdt a), ?_, s10, s11, he, s12⟩
  rw [s9.1, s9.2, s1]
  exact ⟨hO1, hO2⟩

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinitenessOfPublishedInputsStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteness_of_localLanglands : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → PrN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, ArchCmp hL → SEta hL → SXd hL → SFin hL ∧ ∀ cDep : ℝ, SFinl hL cDep := by
  first | exact @GlobalTheory.HeightCounting.Fin3.sFin | exact GlobalTheory.HeightCounting.Fin3.sFin | (intros; apply GlobalTheory.HeightCounting.Fin3.sFin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricChernDensityLieGramRelationStatement
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodgeMetric_chernDensity_lieGram_relation : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∀ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (hj : j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str), IsLieBase e (Φ.C k) X j f f₀ Eb A₀ → ∀ y ∈ ptsIn X.str (σ.comp e.toRingHom) (openPart j), ∀ c' : AlgChart X.str (σ.comp e.toRingHom) X.dim, y ∈ c'.e.source → ∀ A ∈ Eb.S (under y), ∀ (τ : GlobalTheory.AllWt.Psi H) (k' : ℕ) (Q : MvPolynomial ((E →+* ℂ) × ℕ) ℝ), 1 ≤ k' → chernTop ((∑ a ∈ Finset.range (k' + 1), MvPolynomial.C ((-1 : ℝ) ^ (k' - a)) * MvPolynomial.X (τ.1, a) * MvPolynomial.X (conjEmb τ.1, k' - a)) * Q) (fun w => lieGram e U hj f₀ A₀ A (c'.e.symm w)) (c'.e y) = 0 := by
  first | exact @GlobalTheory.HodgeRelation.chernTop_lieGram_rel_mul | exact GlobalTheory.HodgeRelation.chernTop_lieGram_rel_mul | (intros; apply GlobalTheory.HodgeRelation.chernTop_lieGram_rel_mul <;> assumption)
end

