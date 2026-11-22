import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0259
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0031
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0051
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0050
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteContinuousCocyclesLocalGaloisRep

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitBCOfGalIso
section
noncomputable section

namespace GlobalTheory.SplitDetermines

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

theorem spehLoc_unr (p : Part A.CG) (w : PlE H) (h : A.unr (A.locG p.π w)) : A.unr (spehLoc N A p w) := by
  unfold spehLoc
  induction List.range p.d with
  | nil => exact A.lpZero_unr w
  | cons k l ih => exact (A.unr_sum _ _).2 ⟨(A.unr_tw _ _).2 h, ih⟩

theorem isoLoc_unr_ae (P : List (Part A.CG)) : ∀ᶠ w in Filter.cofinite, A.unr (isoLoc N A P w) := by
  induction P with
  | nil => exact Filter.Eventually.of_forall fun w => A.lpZero_unr w
  | cons p P ih =>
    filter_upwards [ih, A.locG_unr_ae p.π] with w h1 h2
    exact (A.unr_sum _ _).2 ⟨spehLoc_unr N A p w h2, h1⟩

end GlobalTheory.SplitDetermines

namespace GlobalTheory.RowTie

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem splitBC_of_galIso : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N)
    (i : N.Loc), GlobalTheory.RowTie.GalIso N A i → GlobalTheory.RowTie.ChebSplit N → GlobalTheory.RowCopy.IsobaricDiscreteSelfDualStrongMultiplicityOne N A →
    GlobalTheory.RowTie.SplitBC N A i := by
  intro R H what₂ N A i hG hC hAN P P' hag Pa Pa' hB hB'
  obtain ⟨r, hrc, -, hr⟩ := hG P Pa hB
  obtain ⟨r', hrc', -, hr'⟩ := hG P' Pa' hB'
  have hfin : (placesOver H.E (N.l i)).Finite := by
    have h0 : Ideal.span {((N.l i : ℕ) : 𝓞 H.E)} ≠ 0 := by
      simpa using (Fact.out : (N.l i).Prime).ne_zero
    exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.2 hv
  have hinj : Function.Injective (Polynomial.map (A.iotaQC i).toRingHom) :=
    Polynomial.map_injective _ (A.iotaQC i).injective
  have hgood : ∀ᶠ w in Filter.cofinite, (w ∉ placesOver H.E (N.l i) ∧ A.unr (isoLoc N A Pa w) ∧
      A.unr (isoLoc N A Pa' w)) ∧ (IsSplitPl H w → A.locV i P w = A.locV i P' w) := by
    filter_upwards [hfin.eventually_cofinite_notMem, GlobalTheory.SplitDetermines.isoLoc_unr_ae N A Pa,
      GlobalTheory.SplitDetermines.isoLoc_unr_ae N A Pa', hag] with w h1 h2 h3 h4
    exact ⟨⟨h1, h2, h3⟩, h4⟩
  have hS := Filter.eventually_cofinite.1 hgood
  have hd := hC hS.toFinset
  have hu : ∀ w, w ∉ placesOver H.E (N.l i) → A.unr (isoLoc N A Pa w) → A.unr (A.wdOf i r w) := fun w h1 h2 => by
    rw [hr w h1]; exact (A.unr_tw _ _).2 h2
  have hu' : ∀ w, w ∉ placesOver H.E (N.l i) → A.unr (isoLoc N A Pa' w) → A.unr (A.wdOf i r' w) := fun w h1 h2 => by
    rw [hr' w h1]; exact (A.unr_tw _ _).2 h2
  have key := GlobalTheory.TypeLeaf.charpoly_eq_of_dense (G H.E N.Om) (Qbar (N.l i)) R.nV
    (fun g => ((r g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))))
    (fun g => ((r' g : GL (Fin R.nV) (Qbar (N.l i))) : Matrix (Fin R.nV) (Fin R.nV) (Qbar (N.l i))))
    _ hd hrc hrc' (by
      rintro g ⟨w, hw, hsp, B, hBw, hg⟩
      have hw' : ¬ ¬ ((w ∉ placesOver H.E (N.l i) ∧ A.unr (isoLoc N A Pa w) ∧
          A.unr (isoLoc N A Pa' w)) ∧ (IsSplitPl H w → A.locV i P w = A.locV i P' w)) := by
        simpa using hw
      obtain ⟨⟨h1, h2, h3⟩, h4⟩ := not_not.1 hw'
      apply hinj
      have e : A.wdOf i r w = A.wdOf i r' w := by
        rw [hr w h1, hr' w h1, hB.2.2.2.1 w hsp, hB'.2.2.2.1 w hsp, h4 hsp]
      rw [A.wdOf_frob i r w h1 hrc (hu w h1 h2) B g hBw hg,
        A.wdOf_frob i r' w h1 hrc' (hu' w h1 h3) B g hBw hg, e])
  refine hAN Pa Pa' hB.1 hB'.1 ?_
  filter_upwards [hgood] with w hw
  obtain ⟨⟨h1, h2, h3⟩, -⟩ := hw
  obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 w)
  have e1 := A.wdOf_frob i r w h1 hrc (hu w h1 h2) _ σ (N.plOm.2 w) hσ
  have e2 := A.wdOf_frob i r' w h1 hrc' (hu' w h1 h3) _ σ (N.plOm.2 w) hσ
  have hm : A.frobEig (A.wdOf i r w) = A.frobEig (A.wdOf i r' w) := by
    have e3 := congrArg Polynomial.roots (e1.symm.trans ((congrArg _ (key σ)).trans e2))
    rwa [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e3
  have e4 : A.wdOf i r w = A.wdOf i r' w := by
    rw [A.unr_eq_lpUnr _ (hu w h1 h2), hm, ← A.unr_eq_lpUnr _ (hu' w h1 h3)]
  rw [hr w h1, hr' w h1] at e4
  have e5 := congrArg (fun a => A.lpTw a (-((1 - (R.nV : ℝ)) / 2))) e4
  simpa only [A.lpTw_add, add_neg_cancel, A.lpTw_zero] using e5

end GlobalTheory.RowTie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThetaOneGenusOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

namespace GlobalTheory.Proof.ThetaOneGenusOne

theorem thetaOne_of_ties : ∀ (D : D7), (∀ i : D.nd.Loc, GlobalTheory.RowCopy.LamPos D (D.nd.mu i) (D.nd.j i)) → (∀ i, GlobalTheory.RowTie.PairLift D.nd D.naut i) → (∀ i, GlobalTheory.ThetaExh.TypeOrth D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.BCEx D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.SplitBC D.nd D.naut i) → (∀ i, GlobalTheory.RowTie.RepOfLoc D.nd D.naut i) → GlobalTheory.RowCopy.ThetaOne D := by
  intro D hpos hpair horth hbc hsplit hrep
  exact GlobalTheory.Proof.HoweThetaLiftComponents.eachRowHasThetaLift_of_howe _ _ _ D.nd D.naut hpos
    (fun i => GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces _ _ _ D.nd D.naut i (hpair i) (hbc i) (hsplit i) (hrep i)) horth

end GlobalTheory.Proof.ThetaOneGenusOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TranslateMemTwistedJacquetKernelRamified
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.CartanCoinv

open GlobalTheory.PRep

section Gen
variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G)

theorem sub_mem_coinv {k : G} (hk : k ∈ K) (v : V) : ρ k v - v ∈ twKer ρ K 1 :=
  Submodule.subset_span ⟨⟨k, hk⟩, v, by simp⟩

theorem apply_mem_coinv {k : G} (hk : k ∈ K) {v : V} (hv : v ∈ twKer ρ K 1) : ρ k v ∈ twKer ρ K 1 := by
  have := (twKer ρ K 1).add_mem (sub_mem_coinv ρ K hk v) hv
  simpa using this

theorem mem_coinv_of_eigen {k : G} (hk : k ∈ K) {v : V} {c : ℂ} (hc : c ≠ 1) (hv : ρ k v = c • v) :
    v ∈ twKer ρ K 1 := by
  have h := (twKer ρ K 1).smul_mem (c - 1)⁻¹ (sub_mem_coinv ρ K hk v)
  have e : (c - 1)⁻¹ • (ρ k v - v) = v := by
    have : ρ k v - v = (c - 1) • v := by rw [hv, sub_smul, one_smul]
    rw [this, smul_smul, inv_mul_cancel₀ (sub_ne_zero.2 hc), one_smul]
  rwa [e] at h

end Gen

def diagUnit {R : Type} [CommRing R] {a : ℕ} (f : Fin a → Rˣ) : GL (Fin a) R where
  val := Matrix.diagonal fun i => (f i : R)
  inv := Matrix.diagonal fun i => ((f i)⁻¹ : Rˣ)
  val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
  inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp

theorem exists_diag {L : Type} [Field L] (O : Subring L) {a : ℕ} (ha : 1 ≤ a) (u : Lˣ) (h1 : (u : L) ∈ O)
    (h2 : ((u⁻¹ : Lˣ) : L) ∈ O) : ∃ d ∈ Formalism.UG.GLint (Fin a) O, Matrix.GeneralLinearGroup.det d = u ∧
      ∃ f : Fin a → L, (d : Matrix (Fin a) (Fin a) L) = Matrix.diagonal f := by
  let u' : Oˣ := ⟨⟨u, h1⟩, ⟨(u⁻¹ : Lˣ), h2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  let f : Fin a → Oˣ := Function.update 1 ⟨0, ha⟩ u'
  have hm : ((Formalism.UG.bc O.subtype (diagUnit f) : GL (Fin a) L) : Matrix (Fin a) (Fin a) L) =
      Matrix.diagonal fun i => ((f i : O) : L) := by
    change (Matrix.diagonal fun i => (f i : O)).map O.subtype = _
    rw [Matrix.diagonal_map (map_zero _)]
    rfl
  refine ⟨Formalism.UG.bc O.subtype (diagUnit f), ⟨_, rfl⟩, ?_, _, hm⟩
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, hm, Matrix.det_diagonal,
    Finset.prod_eq_single (⟨0, ha⟩ : Fin a)]
  · simp [f, u']
  · intro b _ hb
    simp [f, Function.update_of_ne hb]
  · simp

theorem translate_mem_twKer : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (a : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ (GL (Fin a) (w.adicCompletion E)) V) (χ : (w.adicCompletion E)ˣ →* ℂˣ) (u : (w.adicCompletion E)ˣ), 1 ≤ a → Valued.v (u : w.adicCompletion E) = 1 → χ u ≠ 1 → ∀ y : V, (∀ k ∈ GlobalTheory.LFun.KGL w a, ρ k y = (((χ (Matrix.GeneralLinearGroup.det k))⁻¹ : ℂˣ) : ℂ) • y) → ∀ g, ρ g y ∈ GlobalTheory.PRep.twKer ρ (GlobalTheory.LFun.KGL w a) 1 := by
  intro E _ _ w a V _ _ ρ χ u ha hu hχ y hy g
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  obtain ⟨ex, -, k₁, hk₁, k₂, hk₂, e⟩ :=
    Formalism.UG.Final.CartanDecomp E w a ϖ (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) hϖ g
  set D : GL (Fin a) (w.adicCompletion E) := k₁⁻¹ * g * k₂⁻¹ with hDdef
  have hD : (D : Matrix (Fin a) (Fin a) (w.adicCompletion E)) = Formalism.UG.diagPow E w ϖ ex := by
    rw [hDdef, Units.val_mul, Units.val_mul, e]
    simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  have hg : g = k₁ * D * k₂ := by rw [hDdef]; group
  clear_value D
  have h1 : (u : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
    change Valued.v (u : w.adicCompletion E) ≤ 1
    exact hu.le
  have h2 : ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ∈ Formalism.UG.Ov E w := by
    change Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1
    rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]
  obtain ⟨d, hd, hdet, f, hf⟩ := exists_diag (Formalism.UG.Ov E w) ha u h1 h2
  have hcomm : d * D = D * d := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hD, hf, Formalism.UG.diagPow, Matrix.diagonal_mul_diagonal,
      Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hDy : ρ D y ∈ twKer ρ (GlobalTheory.LFun.KGL w a) 1 := by
    refine mem_coinv_of_eigen ρ _ hd (c := (((χ u)⁻¹ : ℂˣ) : ℂ)) ?_ ?_
    · intro h
      exact hχ (inv_eq_one.1 (Units.ext h))
    · rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hy d hd, hdet, map_smul]
  rw [hg, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hy k₂ hk₂, map_smul, map_smul]
  exact Submodule.smul_mem _ _ (apply_mem_coinv ρ _ hk₁ hDy)

end GlobalTheory.CartanCoinv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualContinuousIntegralOverEnlargedCoeff
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistedDualLoc

theorem continuous_T2O (D : D7) (i : D.nd.Loc) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i)))
    (π : D.nd.X i)
    (hρ : Continuous fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) :
    Continuous (T2O D.nd i ρ π) := by
  have h1 : Continuous fun g : GE D.nd => ((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) :=
    D.nd.chi_cont i 1
  have h2 : Continuous fun g : GE D.nd => ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) :=
    GlobalTheory.LocalInv.eps_cont D.nd i
  have h3 : Continuous fun g : GE D.nd => ((ρ π g⁻¹ : GL (Fin D.R.r) (D.nd.O i)) :
      Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) := hρ.comp continuous_inv
  refine continuous_matrix fun a b => ?_
  have h : ∀ g : GE D.nd, T2O D.nd i ρ π g a b =
      ((epsU D.nd i g : (D.nd.O i)ˣ) : D.nd.O i) * (((chiU D.nd i 1 g : (D.nd.O i)ˣ) : D.nd.O i) *
        ((ρ π g⁻¹ : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)) b a) := by
    intro g
    simp [T2O, WpO, rhoO, twistM, dualM]
  simp only [h]
  exact h2.mul (h1.mul (h3.matrix_elem b a))

theorem continuous_and_integral : ∀ (D : D7) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (LL' : FinExt (D.nd.l i)) (h : (D.nbr i w hw).LL.1 ≤ LL'.1) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), Continuous (fun g => ((ρ π g : GL (Fin D.R.r) (D.nd.O i)) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i))) → Continuous (fun g => mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g) ∧ ∀ g a b, ‖((mapM (IntermediateField.inclusion h).toRingHom (Br.loc D.nbr i w hw (T2O D.nd i ρ π)) g a b : ↥LL'.1) : Om (D.nd.l i))‖ ≤ 1 := by
  intro D i w hw LL' h ρ π hρ
  have hc := GlobalTheory.WordJumpsCompare.continuous_loc D i w hw (T2O D.nd i ρ π) (continuous_T2O D i ρ π hρ)
  refine ⟨continuous_matrix fun a b => ?_, fun g a b => ?_⟩
  · exact Continuous.subtype_mk (continuous_subtype_val.comp (hc.matrix_elem a b)) _
  · exact GlobalTheory.LocalH1Finiteness.norm_toLL_le (D.nbr i w hw) _

end GlobalTheory.TwistedDualLoc
end
end

