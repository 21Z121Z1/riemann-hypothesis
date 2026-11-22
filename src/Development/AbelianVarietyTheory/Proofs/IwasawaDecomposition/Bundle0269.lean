import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0256
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsGloballyGeneratedIffGeneratingSections
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallySubsingletonCohTwistZOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.EventuallyExistsFiniteSubsetNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0229
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0239
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0250
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0025
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsDefiniteOfAllPlus

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SobolevEmbeddingDiscreteSeriesHilbertSchmidtStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sobolev_embedding_discrete_series_hilbertSchmidt : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mx n → (H →L[ℂ] H)), Std ε σ → ∃ (S : List (List (Mx n))) (C : ℝ), Words (lieSet ε) S ∧ 0 ≤ C ∧ ∀ (ι : Type) [Fintype ι] (f x : ι → H) (A : ℝ), 0 ≤ A → (∀ j, Sm ε σ (x j)) → (∀ l ∈ S, ∀ z : ι → ℂ, ‖∑ j, z j • Dw σ l (x j)‖ ^ 2 ≤ A * ∑ j, ‖z j‖ ^ 2) → ‖∑ j, ⟪f j, x j⟫_ℂ‖ ^ 2 ≤ C * A * ∑ j, ‖f j‖ ^ 2 := by
  first | exact @GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt | exact GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt | (intros; apply GlobalTheory.TypeSum.SobHS.sobolev_hilbertSchmidt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpectralRedivisionTermEquivKeepsTermDataStatement
section
open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2 Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.ConcreteSettingExists GlobalTheory.Mem GlobalTheory.Mem.SRe
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectralRedivisionTermEquiv_keeps_term_data : ∀ (D : D7) (Z : New D) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), (∀ t : RT Y u u', (Formalism.L2.SG.FourParts.termIsId t ↔ Formalism.L2.SG.FourParts.termIsId (eRT Z Y u u' t)) ∧ (Formalism.L2.SG.FourParts.termInS t ↔ Formalism.L2.SG.FourParts.termInS (eRT Z Y u u' t)) ∧ (t.relevant ↔ (eRT Z Y u u' t).relevant) ∧ (t.FeqF ↔ (eRT Z Y u u' t).FeqF) ∧ (t.generic ↔ (eRT Z Y u u' t).generic) ∧ t.G = (eRT Z Y u u' t).G ∧ (∀ p, Formalism.L2.SG.Saturated.termBBne t p ↔ Formalism.L2.SG.Saturated.termBBne (eRT Z Y u u' t) p) ∧ Formalism.L2.SG.PairVal.ptOf t = Formalism.L2.SG.PairVal.ptOf (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.massTerm t = Formalism.L2.SG.PairVal.massTerm (eRT Z Y u u' t) ∧ Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef D u u' (X.Fu u) (Y.what₂ u) Y.δ Y.M) t = Formalism.L2.SG.PairVal.cTerm (Formalism.L2.SG.PairVal.vRdef (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) (reY Z Y).δ (reY Z Y).M) (eRT Z Y u u' t)) ∧ ∀ w, Formalism.L2.SG.PairVal.meanCount D u u' (X.Fu u) (Y.what₂ u) w = Formalism.L2.SG.PairVal.meanCount (reD D Z) (wd Z u) (wd Z u') ((reX Z X).Fu (wd Z u)) ((reY Z Y).what₂ (wd Z u)) w := by
  first | exact @GlobalTheory.Mem.SRe.eRT_keeps_term_data | exact GlobalTheory.Mem.SRe.eRT_keeps_term_data | (intros; apply GlobalTheory.Mem.SRe.eRT_keeps_term_data <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.SplitPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

variable (E) in

abbrev conjE : E ≃+* E := (IsCMField.complexConj E).toRingEquiv

theorem conjSrc_conjSrc_cm (v : HeightOneSpectrum (𝓞 E)) : conjSrc (conjE E) (conjSrc (conjE E) v) = v :=
  (eq_conjSrc fun x => by
    rw [← conjPl_conjSrc (conjE E) v ((conjE E) x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm

theorem conjPl_self_conjSrc (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.Mem.Chr.ConjPl (conjE E) w (conjSrc (conjE E) w) := by
  have h := conjPl_conjSrc (conjE E) (conjSrc (conjE E) w)
  rwa [conjSrc_conjSrc_cm] at h

theorem over_split {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) :
    conjSrc (conjE E) w ≠ w ∧
      (conjSrc (conjE E) w).under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) ∧
      ∀ u : HeightOneSpectrum (𝓞 E), u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) →
        u = w ∨ u = conjSrc (conjE E) w := by
  have key := GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
    (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) w
  have h2 : ∀ u, GlobalTheory.Mem.Chr.ConjPl (conjE E) w u → u = conjSrc (conjE E) w := fun u h => by
    rw [eq_conjSrc h, conjSrc_conjSrc_cm]
  obtain ⟨u, hu, hu'⟩ := hw
  refine ⟨?_, (key _).2 (Or.inr (conjPl_self_conjSrc w)), fun u' h => ((key u').1 h).imp_right (h2 u')⟩
  rcases (key u).1 hu' with h | h
  · exact absurd h hu
  · rw [← h2 u h]; exact hu

theorem comp_eq (x : UA E n) (u : HeightOneSpectrum (𝓞 E)) :
    ((cLoc (conjSrc (conjE E) u) x).val.map (conjLoc (conjE E) u))ᵀ * (cLoc u x).val = 1 := by
  have h : cT (conjAd E) (x.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * x.1.val = 1 := x.2
  rw [Matrix.mul_one] at h
  have h2 := congrArg (RingHom.mapMatrix ((pLoc E u).comp (pFin E))) h
  rw [map_one, map_mul] at h2
  exact h2

theorem eq_one_of_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (z : locU n w) (h1 : cLoc w z.1 = 1) :
    z = 1 := by
  obtain ⟨-, -, hover⟩ := over_split hw
  have hw1 : ∀ v, v = w → cLoc v z.1 = 1 := by
    rintro v rfl
    exact h1
  have hall : ∀ u, cLoc u z.1 = 1 := by
    intro u
    by_cases hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · rcases hover u hu with rfl | rfl
      · exact h1
      · have hce := comp_eq z.1 (conjSrc (conjE E) w)
        rw [hw1 _ (conjSrc_conjSrc_cm w), Units.val_one, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.transpose_one, Matrix.one_mul] at hce
        exact Units.ext hce
    · have hz := (Subgroup.mem_inf.1 z.2).2
      exact MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hz u) hu)
  have hinf : cInf z.1 = 1 := MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 z.2).1
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · exact hinf.trans (map_one _).symm
  · rw [Subgroup.coe_one, Subgroup.coe_one, map_one]
    refine Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => ?_)
    have := congrArg (fun g : GL (Fin n) (u.adicCompletion E) => g.val i j) (hall u)
    simp only [Units.val_one, Matrix.one_apply] at this
    refine this.trans ?_
    split_ifs with hij <;> simp [hij]

def psi (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →+* (conjSrc (conjE E) w).adicCompletion E :=
  (GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose

theorem psi_spec (w : HeightOneSpectrum (𝓞 E)) : Continuous (psi w) ∧
    ∀ k : E, psi w (algebraMap E _ k) = algebraMap E _ (conjE E k) :=
  ⟨(GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose_spec.1,
    (GlobalTheory.Mem.Chr.exists_finCompl_map (conjE E) (conjPl_self_conjSrc w)).choose_spec.2.1⟩

theorem conjLoc_psi (w : HeightOneSpectrum (𝓞 E)) (y : w.adicCompletion E) : conjLoc (conjE E) w (psi w y) = y := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) w).equalizer
    ((conjLoc_spec (conjE E) w).1.comp (psi_spec w).1) continuous_id (funext fun k => ?_)) y
  simp only [Function.comp_apply, id, (psi_spec w).2, (conjLoc_spec (conjE E) w).2.1]
  exact congrArg _ (IsCMField.complexConj_apply_apply E k)

theorem conjLoc_pLoc (w : HeightOneSpectrum (𝓞 E)) (a : Af E) :
    conjLoc (conjE E) (conjSrc (conjE E) w) (pLoc E (conjSrc (conjE E) (conjSrc (conjE E) w)) a) = psi w (pLoc E w a) := by
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = w)
      (f : v.adicCompletion E →+* (conjSrc (conjE E) w).adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (conjE E k)) → f (pLoc E v a) = psi w (pLoc E w a) := by
    rintro v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf (psi_spec v).1
      (funext fun k => (h k).trans ((psi_spec v).2 k).symm)) _
  exact key _ (conjSrc_conjSrc_cm w) _ (conjLoc_spec (conjE E) _).1 (conjLoc_spec (conjE E) _).2.1

theorem invT_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (g : GL (Fin n) R) :
    GeneralLinearGroup.map f (invT n R g) = invT n S (GeneralLinearGroup.map f g) := by
  apply Units.ext
  change ((g⁻¹ : GL (Fin n) R).val)ᵀ.map f = ((GeneralLinearGroup.map f g)⁻¹).valᵀ
  rw [← map_inv]
  rfl

def finPt (w : HeightOneSpectrum (𝓞 E)) (h : GL (Fin n) (w.adicCompletion E)) : GL (Fin n) (Af E) :=
  locGL E n w h * locGL E n (conjSrc (conjE E) w) (invT n _ (GeneralLinearGroup.map (psi w) h))

theorem finPt_w {w : HeightOneSpectrum (𝓞 E)} (hne : conjSrc (conjE E) w ≠ w) (h : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E w) (finPt w h) = h := by
  rw [finPt, map_mul, pLoc_locGL, pLoc_locGL_of_ne (Ne.symm hne), mul_one]

theorem finPt_w' {w : HeightOneSpectrum (𝓞 E)} (hne : conjSrc (conjE E) w ≠ w) (h : GL (Fin n) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) w)) (finPt w h) =
      invT n _ (GeneralLinearGroup.map (psi w) h) := by
  rw [finPt, map_mul, pLoc_locGL, pLoc_locGL_of_ne hne, one_mul]

theorem finPt_other {w u : HeightOneSpectrum (𝓞 E)} (h1 : u ≠ w) (h2 : u ≠ conjSrc (conjE E) w)
    (h : GL (Fin n) (w.adicCompletion E)) : GeneralLinearGroup.map (pLoc E u) (finPt w h) = 1 := by
  rw [finPt, map_mul, pLoc_locGL_of_ne h1, pLoc_locGL_of_ne h2, one_mul]

omit [IsCMField E] in
theorem matAf_ext {M N : Matrix (Fin n) (Fin n) (Af E)}
    (h : ∀ u, RingHom.mapMatrix (pLoc E u) M = RingHom.mapMatrix (pLoc E u) N) : M = N :=
  Matrix.ext fun i j => FiniteAdeleRing.ext (R := 𝓞 E) E fun u => congrFun (congrFun (h u) i) j

theorem matAd_ext {M N : Matrix (Fin n) (Fin n) (Ad E)} (h1 : RingHom.mapMatrix (pInf E) M = RingHom.mapMatrix (pInf E) N)
    (h2 : RingHom.mapMatrix (pFin E) M = RingHom.mapMatrix (pFin E) N) : M = N :=
  Matrix.ext fun i j => ad_ext (congrFun (congrFun h1 i) j) (congrFun (congrFun h2 i) j)

theorem finGL_mem_UA (k : GL (Fin n) (Af E))
    (hk : ∀ u, ((GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) u)) k).val.map (conjLoc (conjE E) u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) k).val = 1) : finGL E n k ∈ UA E n := by
  show cT (conjAd E) (finGL E n k).val * 1 * (finGL E n k).val = 1
  rw [Matrix.mul_one]
  have hinf : (finGL E n k).val.map (pInf E) = 1 := congrArg Units.val (pInf_finGL k)
  have hfin : (finGL E n k).val.map (pFin E) = k.val := congrArg Units.val (pFin_finGL k)
  refine matAd_ext ?_ ?_
  · rw [map_mul, map_one]
    have e : RingHom.mapMatrix (pInf E) (cT (conjAd E) (finGL E n k).val) = 1 := by
      refine Matrix.ext fun i j => ?_
      have hji := congrFun (congrFun hinf j) i
      change pInf E (conjAd E ((finGL E n k).val j i)) = _
      rw [show pInf E (conjAd E ((finGL E n k).val j i)) = starRingEnd (Cinf E) (pInf E ((finGL E n k).val j i)) from
        (infEq E).symm_apply_apply _]
      change starRingEnd (Cinf E) (((finGL E n k).val.map (pInf E)) j i) = _
      rw [hinf]
      simp [Matrix.one_apply, eq_comm]
    rw [e, one_mul]
    exact hinf
  · rw [map_mul, map_one]
    have e : RingHom.mapMatrix (pFin E) (cT (conjAd E) (finGL E n k).val) = cT (conjFin (conjE E)) k.val := by
      rw [← hfin]; rfl
    change RingHom.mapMatrix (pFin E) (cT (conjAd E) (finGL E n k).val) * (finGL E n k).val.map (pFin E) = 1
    rw [e, hfin]
    refine matAf_ext fun u => ?_
    rw [map_mul, map_one]
    exact hk u

theorem finPt_cond {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E))
    (u : HeightOneSpectrum (𝓞 E)) :
    ((GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) u)) (finPt w h)).val.map (conjLoc (conjE E) u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) (finPt w h)).val = 1 := by
  obtain ⟨hne, -, -⟩ := over_split hw
  by_cases h1 : u = w
  · rw [h1, finPt_w' hne, finPt_w hne]
    change ((GeneralLinearGroup.map (conjLoc (conjE E) w) (invT n _ (GeneralLinearGroup.map (psi w) h))).val)ᵀ * h.val = 1
    rw [invT_map, show GeneralLinearGroup.map (conjLoc (conjE E) w) (GeneralLinearGroup.map (psi w) h) = h from
      Units.ext (Matrix.ext fun i j => conjLoc_psi w _)]
    change (((h⁻¹ : GL (Fin n) _).val)ᵀ)ᵀ * h.val = 1
    rw [Matrix.transpose_transpose, Units.inv_mul]
  · by_cases h2 : u = conjSrc (conjE E) w
    · rw [h2, finPt_w' hne]
      have e : (GeneralLinearGroup.map (pLoc E (conjSrc (conjE E) (conjSrc (conjE E) w))) (finPt w h)).val.map
          (conjLoc (conjE E) (conjSrc (conjE E) w)) = (GeneralLinearGroup.map (psi w) h).val := by
        refine Matrix.ext fun i j => ?_
        refine (conjLoc_pLoc w _).trans ?_
        have := congrArg (fun g : GL (Fin n) (w.adicCompletion E) => g.val i j) (finPt_w hne h)
        exact congrArg (psi w) this
      rw [e]
      change (GeneralLinearGroup.map (psi w) h).valᵀ * ((GeneralLinearGroup.map (psi w) h)⁻¹).valᵀ = 1
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
    · have h3 : conjSrc (conjE E) u ≠ w := fun e => h2 (by rw [← e, conjSrc_conjSrc_cm])
      have h4 : conjSrc (conjE E) u ≠ conjSrc (conjE E) w := fun e => h1 (conjSrc_injective _ e)
      rw [finPt_other h3 h4, finPt_other h1 h2]
      simp

theorem cLoc_finGL (u : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (Af E)) (hk : finGL E n k ∈ UA E n) :
    cLoc u (⟨finGL E n k, hk⟩ : UA E n) = GeneralLinearGroup.map (pLoc E u) k := by
  change GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) (finGL E n k) = _
  have e : ∀ g : GA E n, GeneralLinearGroup.map ((pLoc E u).comp (pFin E)) g =
      GeneralLinearGroup.map (pLoc E u) (GeneralLinearGroup.map (pFin E) g) := fun g => Units.ext rfl
  rw [e, pFin_finGL]

def locPt {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E)) : locU n w :=
  ⟨⟨finGL E n (finPt w h), finGL_mem_UA _ (finPt_cond hw h)⟩, by
    obtain ⟨-, hw', -⟩ := over_split hw
    refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (pInf_finGL _), Subgroup.mem_iInf.2 fun u =>
      Subgroup.mem_iInf.2 fun hu => MonoidHom.mem_ker.2 ?_⟩
    rw [cLoc_finGL]
    exact finPt_other (fun e => hu (by rw [e])) (fun e => hu (by rw [e, hw'])) h⟩

theorem cLoc_locPt {w : HeightOneSpectrum (𝓞 E)} (hw : IsSplitAt w) (h : GL (Fin n) (w.adicCompletion E)) :
    cLoc w (locPt hw h).1 = h :=
  (cLoc_finGL w _ _).trans (finPt_w (over_split hw).1 h)

theorem continuous_invT (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (invT n R) :=
  Units.continuous_iff.2 ⟨Units.continuous_coe_inv.matrix_transpose, Units.continuous_val.matrix_transpose⟩

end GlobalTheory.SplitPts

open GlobalTheory.SplitPts in

theorem GlobalTheory.locU_equiv_GL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ)
    (w : HeightOneSpectrum (𝓞 E)), IsSplitAt w →
      ∃ e : locU n w ≃ₜ* GL (Fin n) (w.adicCompletion E), ∀ x : locU n w, e x = cLoc w (x : UA E n) := by
  intro E _ _ _ n w hw
  have inj : ∀ a b : locU n w, cLoc w a.1 = cLoc w b.1 → a = b := fun a b hab => by
    have := eq_one_of_cLoc hw (a * b⁻¹)
      (by rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hab, mul_inv_cancel])
    exact mul_inv_eq_one.1 this
  have hfin : Continuous (finGL E n) :=
    Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
      (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))
  refine ⟨{ toFun := fun x => cLoc w x.1
            invFun := locPt hw
            left_inv := fun x => inj _ _ (cLoc_locPt hw _)
            right_inv := fun h => cLoc_locPt hw h
            map_mul' := fun x y => map_mul (cLoc w) x.1 y.1
            continuous_toFun := ?_
            continuous_invFun := ?_ }, fun x => rfl⟩
  · exact (Continuous.units_map _ (continuous_id.matrix_map
      ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp
      (continuous_subtype_val.comp continuous_subtype_val)
  · refine Continuous.subtype_mk (Continuous.subtype_mk (hfin.comp ?_) _) _
    exact (CuspSub.continuous_locGL w).mul ((CuspSub.continuous_locGL _).comp ((continuous_invT _).comp
      (Continuous.units_map _ (continuous_id.matrix_map (psi_spec w).1))))
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepZeroClassesBijectiveSameDeco
section
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr

namespace GlobalTheory.Mem.Col2.ClsZero

section Canon
variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (Λ : LevFam X.E X.K n SG)

def canon (d : DecoSet X.E n ST SG) : DecoSet X.E n ST SG :=
  Classical.epsilon (p := fun d' => ∃ (γ : UF X.E n) (k : Λ.grp),
    d' = ((γ, (k.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) • d) (h := ⟨d⟩)

theorem canon_spec (d : DecoSet X.E n ST SG) : ∃ (γ : UF X.E n) (k : Λ.grp),
    canon Λ d = ((γ, (k.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) • d :=
  Classical.epsilon_spec (p := fun d' => ∃ (γ : UF X.E n) (k : Λ.grp), d' = ((γ, (k.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) • d)
    ⟨d, 1, 1, (one_smul _ d).symm⟩

theorem canon_smul (γ : UF X.E n) (k : Λ.grp) (d : DecoSet X.E n ST SG) :
    canon Λ (((γ, (k.1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) • d) = canon Λ d := by
  unfold canon
  congr 1
  funext d'
  apply propext
  constructor
  · rintro ⟨γ', k', rfl⟩
    exact ⟨γ' * γ, k' * k, by rw [← mul_smul]; rfl⟩
  · rintro ⟨γ', k', rfl⟩
    refine ⟨γ' * γ⁻¹, k' * k⁻¹, ?_⟩
    rw [← mul_smul]
    congr 1
    ext1 <;> simp

theorem canon_idem (d : DecoSet X.E n ST SG) : canon Λ (canon Λ d) = canon Λ d := by
  obtain ⟨γ, k, h⟩ := canon_spec Λ d
  conv_lhs => rw [h]
  exact canon_smul Λ γ k d

theorem orb_iff (y : Ys X n) (Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ) (Θ : LevQFam X.E X.K n Q) (hΘ : Θ = LevQFam.top X.E X.K n Q)
    (hy : y = Ys.triv X n) (p p' : PtY ST SG Q y) :
    (letI := ptYAct (ST := ST) y Λ' Θ; ∃ g : FrmG Λ' Θ, g • p = p') ↔ canon Λ p'.1.1.deco = canon Λ p.1.1.deco := by
  subst hΛ hΘ hy
  constructor
  · rintro ⟨g, rfl⟩
    exact canon_smul Λ' g.1 g.2.1 p.1.1.deco
  · intro h
    obtain ⟨γ₁, k₁, h₁⟩ := canon_spec Λ' p.1.1.deco
    obtain ⟨γ₂, k₂, h₂⟩ := canon_spec Λ' p'.1.1.deco
    have e : p'.1.1.deco = (((γ₂⁻¹ * γ₁ : UF X.E n), ((k₂⁻¹ * k₁ : Λ'.grp).1 : GLG X.E n SG)) : UF X.E n × GLG X.E n SG) • p.1.1.deco := by
      have := h₂.symm.trans (h.trans h₁)
      rw [← eq_inv_smul_iff, ← mul_smul] at this
      exact this
    generalize γ₂⁻¹ * γ₁ = γ at e
    generalize k₂⁻¹ * k₁ = k at e
    let q : DecoF X.E n ST SG Q := ((γ, k.1, 1) : UF X.E n × GLG X.E n SG × GLQ X.E n Q) • p.1.1
    have hq : q.deco = p'.1.1.deco := e.symm
    have hc : ∀ P : Q, (p'.1.1.fr P)⁻¹ * q.fr P ∈ GLint X.E n P.1 := by
      intro P x
      have h1 := q.2 P x
      have h2 := p'.1.1.2 P ((p'.1.1.fr P)⁻¹ (q.fr P x))
      have h3 : p'.1.1.1.2 P ((p'.1.1.fr P)⁻¹ (q.fr P x)) = q.fr P x := LinearEquiv.apply_symm_apply _ _
      rw [h3] at h2
      have h4 : q.1.1 = p'.1.1.1.1 := hq
      rw [h4] at h1
      exact h2.symm.trans h1
    refine ⟨(γ, k, ⟨fun P => ⟨_, hc P⟩, fun _ _ => trivial⟩), ?_⟩
    refine Subtype.ext (Prod.ext (Subtype.ext (Prod.ext e.symm ?_)) ?_)
    · funext P
      show γ.1 * p.1.1.fr P * ((p'.1.1.fr P)⁻¹ * (γ.1 * p.1.1.fr P * ((1 : GLQ X.E n Q) P)⁻¹.1))⁻¹ = p'.1.1.fr P
      simp only [Pi.one_apply, inv_one, OneMemClass.coe_one, mul_one]
      group
    · have h1 : p.1.2 = ∅ := p.2
      have h2 : p'.1.2 = ∅ := p'.2
      show (fun v => γ.1 v) '' p.1.2 = p'.1.2
      rw [h1, h2, Set.image_empty]

theorem eps_eq (y : Ys X n) (Λ' : LevFam X.E X.K n SG) (hΛ : Λ' = Λ) (Θ : LevQFam X.E X.K n Q) (p : PtY ST SG Q y) :
    (letI := ptYAct (ST := ST) y Λ' Θ
     Classical.epsilon (p := fun r => ∃ g : FrmG Λ' Θ, r = (g • p).1.1.deco) (h := ⟨p.1.1.deco⟩)) = canon Λ p.1.1.deco := by
  subst hΛ
  unfold canon
  congr 1
  funext r
  apply propext
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨g.1, g.2.1, rfl⟩
  · rintro ⟨γ, k, rfl⟩
    exact ⟨(γ, k, 1), rfl⟩

end Canon

attribute [local instance] starE
variable {B : Base} {X : PreX B.toPre} {I : TC B X}

theorem levelTypePrimes_stepZero_eq_colLev (h : I.Ok) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) :
    levGAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b = colLev I.Ch 0 := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (by have := B.R.two_le_m; omega)) (by simp)
  · exact (h.idx_ok a).zero_G b

theorem chartIndexLevelTwistPrimes_stepZero_eq_top (h : I.Ok) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) :
    levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b = LevQFam.top _ _ _ _ := by
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 (by have := B.R.two_le_m; omega)) (by simp)
  · exact (h.idx_ok a).zero_Q b

theorem ys0 (a : I.ι) : ysAt B.R I.sel (I.tup a) (I.cst a) 0 = Ys.triv _ _ :=
  if_neg (by have := B.R.two_le_m; omega)

theorem stepZero_chartIndex_subsingleton (h : I.Ok) (a : I.ι) (b b' : Idx I.sel (I.tup a) (I.idx a) 0) : b = b' := by
  have hm : 0 < B.R.m := by have := B.R.two_le_m; omega
  obtain ⟨b0, hb0⟩ := (h.idx_ok a).zero_uniq
  obtain ⟨_ | b, hb⟩ := b
  · exact absurd (hb.2 hm) (by simp)
  obtain ⟨_ | b', hb'⟩ := b'
  · exact absurd (hb'.2 hm) (by simp)
  obtain rfl : b = b' := (hb0 b).trans (hb0 b').symm
  rfl

theorem stepZero_chartIndex_nonempty (h : I.Ok) (a : I.ι) : Nonempty (Idx I.sel (I.tup a) (I.idx a) 0) := by
  obtain ⟨b0, -⟩ := (h.idx_ok a).zero_uniq
  exact ⟨⟨some b0, by have := B.R.two_le_m; simp; omega⟩⟩

theorem cl_eq_iff (h : I.Ok) (u : B.Word) (a : I.ι) (b b' : Idx I.sel (I.tup a) (I.idx a) 0) (p p' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) :
    (I.stp u a 0).cl b p = (I.stp u a 0).cl b' p' ↔ canon (colLev I.Ch 0) p.1.1.deco = canon (colLev I.Ch 0) p'.1.1.deco := by
  obtain rfl := stepZero_chartIndex_subsingleton h a b b'
  rw [← orb_iff (colLev I.Ch 0) _ _ (levelTypePrimes_stepZero_eq_colLev h a b) _ (chartIndexLevelTwistPrimes_stepZero_eq_top h a b) (ys0 a) p' p]
  constructor
  · intro e
    exact Quotient.exact (eq_of_heq (Sigma.mk.inj e).2)
  · intro e
    exact congrArg (Sigma.mk b) (Quotient.sound e)

theorem cl_rep {E K : Type} [Field E] [NumberField E] [Field K] {n : ℕ} (S : GStep E K n) (c : S.Cl) : S.cl c.1 (S.rep c) = c :=
  congrArg (Sigma.mk c.1) (S.rp_spec c.1 c.2)

theorem bij0 (h : I.Ok) (u : B.Word) (a : I.ι) (b) : Function.Bijective (I.cl0 u a b) := by
  constructor
  · intro c c' e
    have e1 := (cl_eq_iff h u a b b _ _).1 e
    rw [← cl_rep _ c, ← cl_rep _ c']
    exact (cl_eq_iff h u I.mu0 _ _ _ _).2 e1
  · intro c
    obtain ⟨b0⟩ := stepZero_chartIndex_nonempty h I.mu0
    refine ⟨(I.stp u I.mu0 0).cl b0 (I.pt0 u a I.mu0 ((I.stp u a 0).rep c)), ?_⟩
    have e := (cl_eq_iff h u I.mu0 _ _ _ _).1 (cl_rep _ ((I.stp u I.mu0 0).cl b0 (I.pt0 u a I.mu0 ((I.stp u a 0).rep c))))
    refine Eq.trans ?_ (cl_rep _ c)
    exact (cl_eq_iff h u a _ _ _ _).2 e

theorem stepZero_preferred_iff_canonicalRep (h : I.Ok) (u : B.Word) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0)
    (p : PtAt B.R I.sel (I.tup a) (I.cst a) u 0) :
    I.pref u a 0 b p ↔ p.1.1.deco = canon (colLev I.Ch 0) p.1.1.deco := by
  have hm := B.R.two_le_m
  have e := eps_eq (ST := (B.primes X).vT u) (colLev I.Ch 0) _ _ (levelTypePrimes_stepZero_eq_colLev h a b)
    (levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) 0 b) p
  constructor
  · intro hp
    exact Eq.trans (hp.1 rfl) e
  · intro hp
    exact ⟨fun _ => hp.trans e.symm, fun e' => absurd e' (by omega),
      topLev_pref_ne I.Ch I.sel (I.tup a) (I.cst a) I.Ps u (by omega) _⟩

theorem empty_mem_couplingIndexAtStep_zero (a : I.ι) (N) : ∅ ∈ (ysAt B.R I.sel (I.tup a) (I.cst a) 0).ys N := by
  rw [ys0]; rfl

theorem stepZero_representative_deco_eq_canonical (h : I.Ok) (u : B.Word) (a : I.ι) (c : (I.stp u a 0).Cl) :
    ((I.stp u a 0).rep c).1.1.deco = canon (colLev I.Ch 0) ((I.stp u a 0).rep c).1.1.deco := by
  obtain ⟨b, q⟩ := c
  let p := (I.stp u a 0).rep ⟨b, q⟩
  obtain ⟨γ, k, e⟩ := canon_spec (colLev I.Ch 0) p.1.1.deco
  let p' : PtAt B.R I.sel (I.tup a) (I.cst a) u 0 := ⟨(((γ, k.1, 1) : UF B.fields.E (B.R.N 0) × GLG B.fields.E (B.R.N 0) (B.primes X).vGs × GLQ B.fields.E (B.R.N 0) (I.Q a)) • p.1.1, ∅), empty_mem_couplingIndexAtStep_zero a _⟩
  have e' : p'.1.1.deco = canon (colLev I.Ch 0) p.1.1.deco := e.symm
  have hc : (I.stp u a 0).cl b p' = ⟨b, q⟩ := by
    refine Eq.trans ?_ (cl_rep _ ⟨b, q⟩)
    refine (cl_eq_iff h u a b b _ _).2 ?_
    rw [e', canon_idem]
  have hp := @pref_prefRep _ _ _ ((I.stp0 u a 0).actD b) (I.pref u a 0 b) p'
    ((stepZero_preferred_iff_canonicalRep h u a b p').2 (by rw [e', canon_idem]))
  have hq : q = Quotient.mk _ p' := (eq_of_heq (Sigma.mk.inj hc).2).symm
  refine (stepZero_preferred_iff_canonicalRep h u a b _).1 ?_
  rw [hq]
  exact hp

theorem stepZero_corresponding_representatives_same_deco (h : I.Ok) (u : B.Word) (a : I.ι) (b) (c : (I.stp u I.mu0 0).Cl) :
    ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco := by
  refine (stepZero_representative_deco_eq_canonical h u a _).trans (Eq.trans ?_ (stepZero_representative_deco_eq_canonical h u I.mu0 c).symm)
  exact (cl_eq_iff h u a (I.cl0 u a b c).1 b ((I.stp u a 0).rep (I.cl0 u a b c))
    (I.pt0 u I.mu0 a ((I.stp u I.mu0 0).rep c))).1 (cl_rep (I.stp u a 0) (I.cl0 u a b c))

theorem stepZero_classes_bijective_same_deco : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ u a b,
    Function.Bijective (I.cl0 u a b) ∧
      ∀ c, ((I.stp u a 0).rep (I.cl0 u a b c)).1.1.deco = ((I.stp u I.mu0 0).rep c).1.1.deco :=
  fun _ h u a b => ⟨bij0 h u a b, stepZero_corresponding_representatives_same_deco h u a b⟩

end GlobalTheory.Mem.Col2.ClsZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportPushforwardSubsetImageOfIsClosedImmersionStatement
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.support_pushforward_subset_image : ∀ {X Y : Scheme.{0}} (g : Y ⟶ X) [IsClosedImmersion g] (E : Y.Modules), support ((Scheme.Modules.pushforward g).obj E) ⊆ g '' support E := by
  first | exact @GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion | exact GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion | (intros; apply GlobalTheory.support_pushforward_subset_image_of_isClosedImmersion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopMultAndExtVInjective
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DefiniteMult

theorem topMult_and_extV_injective : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), R.BaseW F → Formalism.IndefR.RecTie.TopMultH R ∧ ∀ i t, Function.Injective (R.extV i t) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F h
  refine ⟨?_, fun i t => extV_injective R h.models.HV i t⟩
  intro t
  exact range_top R h.models.inf h.models.cX h.models.prX h.models.HX t

end GlobalTheory.DefiniteMult
end

