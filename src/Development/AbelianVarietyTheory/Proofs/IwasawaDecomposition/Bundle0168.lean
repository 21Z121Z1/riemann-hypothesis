import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0164
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0008
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0059
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0161
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertialOrderFifteenCharAuxiliaryPrimeSpec
import ReciprocityTheory.GaloisValuations.Global
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0084
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0092
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0154
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0091
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIndexIdeal

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleRepresentativesFiniteLevelCosets
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Mem.Col2.IdxFin

open GlobalTheory.Mem.LevFin

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem exists_classes {N q : ℕ} (hq : (q : E) ≠ 0) (e : ℕ → ℤ) (j : ℕ) :
    ∃ (ι : Type) (_ : Finite ι) (f : (Sp E N ≃ₗ[E] Sp E N) → ι), ∀ h h' : Sp E N ≃ₗ[E] Sp E N,
      (∀ x ∈ LocE.sclLat P q N e, h⁻¹ x ∈ LocE.sclLat P q N e ∧ ((q : E) ^ j) • h x ∈ LocE.sclLat P q N e) →
      (∀ x ∈ LocE.sclLat P q N e, h'⁻¹ x ∈ LocE.sclLat P q N e ∧ ((q : E) ^ j) • h' x ∈ LocE.sclLat P q N e) →
      f h = f h' → ∀ x ∈ LocE.sclLat P q N e, (q : E)⁻¹ • ((h⁻¹ * h') x - x) ∈ LocE.sclLat P q N e := by
  classical
  have hc : ((q ^ (j + 1) : ℕ) : E) ≠ 0 := by rw [Nat.cast_pow]; exact pow_ne_zero _ hq
  have hq' : ((q ^ (j + 1) : ℕ) : 𝓞 E) ≠ 0 := fun h0 => hc (by simpa using congrArg (algebraMap (𝓞 E) E) h0)
  have hfin : Finite (𝓞 E ⧸ Ideal.span {((q ^ (j + 1) : ℕ) : 𝓞 E)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa only [Ne, Ideal.span_singleton_eq_bot] using hq')
  have hz : ∀ l : ℕ, (q : E) ^ e l ≠ 0 := fun l => zpow_ne_zero _ hq
  have he : ∀ i : Fin N, (Pi.single i ((q : E) ^ e i.1) : Sp E N) ∈ LocE.sclLat P q N e := by
    intro i
    rw [GlobalTheory.CongLevel.mem_sclLat]
    intro l
    rw [Pi.single_apply]
    split_ifs with hl
    · rw [hl, inv_mul_cancel₀ (hz _)]
      exact GlobalTheory.GO.ChRoot.intAt_one'
    · rw [mul_zero]
      exact GlobalTheory.GO.ChRoot.intAt_zero'
  let m : (Sp E N ≃ₗ[E] Sp E N) → Fin N → Fin N → E :=
    fun h i l => ((q : E) ^ e l.1)⁻¹ * ((q : E) ^ j * h (Pi.single i ((q : E) ^ e i.1)) l)
  have hex : ∀ a : E, ∃ r : 𝓞 E, IntAt P a → IntAt P (((q ^ (j + 1) : ℕ) : E)⁻¹ * (a - algebraMap (𝓞 E) E r)) := by
    intro a
    by_cases ha : IntAt P a
    · obtain ⟨r, hr⟩ := exists_int_congr hc ha
      exact ⟨r, fun _ => hr⟩
    · exact ⟨0, fun h => (ha h).elim⟩
  choose r hr using hex
  refine ⟨Fin N → Fin N → 𝓞 E ⧸ Ideal.span {((q ^ (j + 1) : ℕ) : 𝓞 E)}, inferInstance,
    fun h i l => Ideal.Quotient.mk _ (r (m h i l)), fun a b ha hb hab x hx => ?_⟩
  have hma : ∀ i l, IntAt P (m a i l) := fun i l => (GlobalTheory.CongLevel.mem_sclLat P q N e _).1 (ha _ (he i)).2 l
  have hmb : ∀ i l, IntAt P (m b i l) := fun i l => (GlobalTheory.CongLevel.mem_sclLat P q N e _).1 (hb _ (he i)).2 l
  have h1 : ∀ i l, IntAt P (((q ^ (j + 1) : ℕ) : E)⁻¹ * (m b i l - m a i l)) := by
    intro i l
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 (congrFun (congrFun hab i) l))
    have ht' := congrArg (algebraMap (𝓞 E) E) ht
    simp only [map_mul, map_natCast, map_sub] at ht'
    have := ((hr _ (hmb i l)).add (intAt_neg (hr _ (hma i l)))).add (intAt_neg (IntAt.coe P t))
    convert this using 1
    generalize ((q ^ (j + 1) : ℕ) : E) = c at *
    field_simp
    linear_combination ht'
  have e1 : (q : E)⁻¹ • ((a⁻¹ * b) x - x) = a⁻¹ ((q : E)⁻¹ • (b x - a x)) := by
    rw [map_smul, map_sub, show a⁻¹ (a x) = x from LinearEquiv.symm_apply_apply _ x]
    rfl
  rw [e1]
  refine (ha _ ?_).1
  rw [GlobalTheory.CongLevel.mem_sclLat] at hx ⊢
  intro l
  have ex : x = ∑ i, (((q : E) ^ e i.1)⁻¹ * x i) • (Pi.single i ((q : E) ^ e i.1) : Sp E N) := by
    funext l
    have := hz l.1
    simp [Finset.sum_apply, Pi.single_apply]
    field_simp
  have e2 : ((q : E) ^ e l.1)⁻¹ * ((q : E)⁻¹ • (b x - a x)) l =
      ∑ i, (((q : E) ^ e i.1)⁻¹ * x i) * (((q ^ (j + 1) : ℕ) : E)⁻¹ * (m b i l - m a i l)) := by
    conv_lhs => rw [ex]
    simp only [map_sum, map_smul, Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, ← Finset.sum_sub_distrib,
      Finset.mul_sum, m]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hz l.1
    have := hz i.1
    push_cast
    field_simp
    ring
  rw [e2]
  exact Finset.sum_induction _ (IntAt P) (fun _ _ => IntAt.add) GlobalTheory.GO.ChRoot.intAt_zero' fun i _ =>
    (hx i).mul (h1 i l)

theorem exists_finite_index_of_adm_cosets : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), ∃ (ι : Type) (_ : Finite ι) (f : AutY X R j → ι), ∀ h h' : AutY X R j, admitted Pr j P h → admitted Pr j P h' → f h = f h' → h⁻¹ * h' ∈ Jat (Pr := Pr) sharp j P := by
  intro X Pr R sharp j P
  classical
  have hq := qOf_ne P
  have hb : ∀ h : AutY X R j, admitted Pr j P h → ∀ x ∈ lamYat (Pr := Pr) (R := R) j P,
      h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧ ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P := by
    intro h hh
    by_cases hP : P ∈ Pr.vGs
    · have hs := hh.1 hP
      intro x hx
      refine ⟨((inv_mem hs) x).2 hx, ?_⟩
      rw [← Nat.cast_pow]
      exact natCast_smul_mem _ _ ((hs x).2 hx)
    · exact (between_iff hP h).2 (hh.2 hP)
  obtain ⟨ι, hι, f, hf⟩ := exists_classes (P := P) (N := R.N j + cOf R j) hq
    (LocE.scE (R.N j) (if P ∈ Pr.vGs then fun i => i + 1 else 0)) j
  refine ⟨ι, hι, f, fun h h' hh hh' e => ?_⟩
  have h1 := hf h h' (hb h hh) (hb h' hh') e
  have h2 := hf h' h (hb h' hh') (hb h hh) e.symm
  refine mem_Jat _ _ _ _ (stab_of_cong hq _ _ h1 ?_) h1
  rw [mul_inv_rev, inv_inv]
  exact h2

end GlobalTheory.Mem.Col2.IdxFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineChartOfLeftInverseMatrix
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
open MvPolynomial GlobalTheory.ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.SplitCells

variable {R : Type} [CommRing R] {N r : ℕ}

def lin (a : Fin (N + 1) → R) : MvPolynomial (Fin (N + 1)) R := ∑ j, C (a j) * X j

theorem lin_hom (a : Fin (N + 1) → R) : (lin a).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun j _ => (isHomogeneous_X R j).C_mul _

theorem eval₂_lin {m : Type} {A : Type} [CommRing A] (c : R →+* A) (M : Matrix m (Fin (N + 1)) R) (k : m)
    (w : Fin (N + 1) → A) : eval₂ c w (lin (M k)) = (M.map c).mulVec w k := by
  simp [lin, eval₂_sum, Matrix.mulVec, dotProduct]

abbrev tv (R : Type) [CommRing R] (c : Fin (r + 1)) : Fin (r + 1) → MvPolynomial (Fin r) R :=
  Fin.insertNth (α := fun _ => MvPolynomial (Fin r) R) c 1 X

def res (Q : Matrix (Fin (N + 1)) (Fin (r + 1)) R) (Q' : Matrix (Fin (r + 1)) (Fin (N + 1)) R) :
    Matrix (Fin (N + 1)) (Fin (N + 1)) R := 1 - Q * Q'

theorem mulVec_inv {A : Type} [CommRing A] (c : R →+* A) {Q : Matrix (Fin (N + 1)) (Fin (r + 1)) R}
    {Q' : Matrix (Fin (r + 1)) (Fin (N + 1)) R} (h : Q' * Q = 1) (v : Fin (r + 1) → A) :
    (Q'.map c).mulVec ((Q.map c).mulVec v) = v := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero c) (map_one c), Matrix.one_mulVec]

section
variable {Q : Matrix (Fin (N + 1)) (Fin (r + 1)) R} {Q' : Matrix (Fin (r + 1)) (Fin (N + 1)) R} (h : Q' * Q = 1)
include h

theorem isImmersion_cell (c : Fin (r + 1)) (hv) :
    IsImmersion (pt (C : R →+* MvPolynomial (Fin r) R) ((Q.map C).mulVec (tv R c)) hv) := by
  have he : ∀ k, eval₂Hom (C : R →+* MvPolynomial (Fin r) R) ((Q.map C).mulVec (tv R c)) (lin (Q' k)) = tv R c k :=
    fun k => by rw [coe_eval₂Hom, eval₂_lin, mulVec_inv _ h]
  have h1 : eval₂Hom (C : R →+* MvPolynomial (Fin r) R) ((Q.map C).mulVec (tv R c)) (lin (Q' c)) = 1 := by
    rw [he, tv, Fin.insertNth_apply_same]
  have hu : IsUnit (eval₂Hom (C : R →+* MvPolynomial (Fin r) R) ((Q.map C).mulVec (tv R c)) (lin (Q' c))) :=
    h1 ▸ isUnit_one
  have hm : lin (Q' c) ∈ grading R N 1 := lin_hom _
  rw [pt, ProjPoint.ofHom_eq_awayι _ _ _ one_pos hm hu]
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (ProjPoint.awayLift (grading R N) _ _ hu))) := by
    refine IsClosedImmersion.spec_of_surjective _ fun p => ?_
    change p ∈ (ProjPoint.awayLift (grading R N) _ _ hu).range
    induction p using MvPolynomial.induction_on with
    | C a =>
      have := ProjPoint.awayLift_mk_mul (grading R N) _ hu hm 0 (C a) (isHomogeneous_C _ a)
      rw [pow_zero, mul_one, eval₂Hom_C] at this
      exact ⟨_, this⟩
    | add F G hF hG => exact add_mem hF hG
    | mul_X F k hF =>
      refine mul_mem hF ?_
      have := ProjPoint.awayLift_mk_mul (grading R N) _ hu hm 1 (lin (Q' (c.succAbove k))) (lin_hom _)
      rw [h1, one_pow, mul_one, he] at this
      exact ⟨_, this.trans (Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (Fin r) R) c 1 X k)⟩
  infer_instance

omit h in
theorem exists_pt (x : PSpace R N) : ∃ (K : Type) (_ : Field K) (c : R →+* K) (w : Fin (N + 1) → K) (hw : _)
    (y : Sp K), pt c w hw y = x := by
  let φ := (PSpace R N).fromSpecResidueField x
  let K : Type := (PSpace R N).residueField x
  obtain ⟨w, hw, e⟩ := exists_eq_pt (A := K) (Spec.preimage (φ ≫ PSpace.str R N)).hom φ (Spec.map_preimage _).symm
  exact ⟨K, inferInstance, _, w, hw, IsLocalRing.closedPoint _, by rw [← e]; exact Scheme.fromSpecResidueField_apply x _⟩

omit h in
theorem pt_mem {m A : Type} [CommRing A] (c : R →+* A) (w : Fin (N + 1) → A) (hw) (y : Sp A)
    (M : Matrix m (Fin (N + 1)) R) (k : m) :
    pt c w hw y ∈ Proj.basicOpen (grading R N) (lin (M k)) ↔ (M.map c).mulVec w k ∉ y.asIdeal := by
  rw [← mem_spOpen, ← eval₂_lin, ← pt_preimage_basicOpen c w hw one_pos (lin_hom _)]
  rfl

omit h in
theorem pt_mem_field {m K : Type} [Field K] (c : R →+* K) (w : Fin (N + 1) → K) (hw) (y : Sp K)
    (M : Matrix m (Fin (N + 1)) R) (k : m) :
    pt c w hw y ∈ Proj.basicOpen (grading R N) (lin (M k)) ↔ (M.map c).mulVec w k ≠ 0 := by
  rw [pt_mem, (Ideal.eq_bot_or_top y.asIdeal).resolve_right y.isPrime.ne_top, Ideal.mem_bot]

omit h in
theorem fix_of_not_mem {K : Type} [Field K] (c : R →+* K) (w : Fin (N + 1) → K) (hw) (y : Sp K)
    (H : ∀ k, pt c w hw y ∉ Proj.basicOpen (grading R N) (lin (res Q Q' k))) :
    (Q.map c).mulVec ((Q'.map c).mulVec w) = w := by
  have : ((res Q Q').map c).mulVec w = 0 := funext fun k => by
    have := H k
    rwa [pt_mem_field, not_not] at this
  rw [res, Matrix.map_sub _ (map_sub c), Matrix.map_one _ (map_zero c) (map_one c), Matrix.sub_mulVec,
    Matrix.one_mulVec, Matrix.map_mul, ← Matrix.mulVec_mulVec, sub_eq_zero] at this
  exact this.symm

theorem mem_range_cell (c : Fin (r + 1)) (hv) (x : PSpace R N) :
    x ∈ Set.range (pt (C : R →+* MvPolynomial (Fin r) R) ((Q.map C).mulVec (tv R c)) hv) ↔
      (∀ k, x ∉ Proj.basicOpen (grading R N) (lin (res Q Q' k))) ∧
        x ∈ Proj.basicOpen (grading R N) (lin (Q' c)) := by
  constructor
  · rintro ⟨y, rfl⟩
    refine ⟨fun k => ?_, ?_⟩
    · rw [pt_mem, not_not, Matrix.mulVec_mulVec, ← Matrix.map_mul, res, Matrix.sub_mul, Matrix.mul_assoc, h,
        Matrix.one_mul, Matrix.mul_one, sub_self, Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec]
      exact zero_mem _
    · rw [pt_mem, mulVec_inv _ h, tv, Fin.insertNth_apply_same]
      exact fun h1 => y.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1)
  · rintro ⟨h1, h2⟩
    obtain ⟨K, _, b, w, hw, y, rfl⟩ := exists_pt x
    have h3 := fix_of_not_mem b w hw y h1
    rw [pt_mem_field] at h2
    set u := (Q'.map b).mulVec w
    let ψ : MvPolynomial (Fin r) R →+* K := eval₂Hom b fun k => (u c)⁻¹ * u (c.succAbove k)
    have hb : ψ.comp C = b := RingHom.ext fun a => eval₂Hom_C _ _ a
    have h4 : ψ ∘ tv R c = (u c)⁻¹ • u := by
      funext k
      refine Fin.succAboveCases c ?_ (fun k => ?_) k
      · simp [h2]
      · simp [ψ]
    have h5 : ψ ∘ (Q.map C).mulVec (tv R c) = (u c)⁻¹ • w := by
      funext k
      rw [Function.comp_apply, RingHom.map_mulVec, Matrix.map_map, ← RingHom.coe_comp, hb, h4,
        Matrix.mulVec_smul, h3]
    refine ⟨spMap ψ y, ?_⟩
    rw [← Scheme.Hom.comp_apply, spMap_pt]
    have h6 : ∀ (b' : R →+* K) (w' : Fin (N + 1) → K) (hw' : _), b' = b → w' = (u c)⁻¹ • w →
        pt b' w' hw' = pt b w hw := by
      rintro _ w' hw' rfl e
      exact ((pt_eq_pt_iff _ hw hw').2 ⟨(Units.mk0 _ h2)⁻¹, e⟩).symm
    rw [h6 _ _ _ hb h5]

omit h in
theorem exists_mem (x : PSpace R N) (H : ∀ k, x ∉ Proj.basicOpen (grading R N) (lin (res Q Q' k))) :
    ∃ c, x ∈ Proj.basicOpen (grading R N) (lin (Q' c)) := by
  obtain ⟨K, _, b, w, hw, y, rfl⟩ := exists_pt x
  have h3 := fix_of_not_mem b w hw y H
  by_contra! hc
  have : (Q'.map b).mulVec w = 0 := funext fun k => by
    have := hc k
    rwa [pt_mem_field, not_not] at this
  rw [this, Matrix.mulVec_zero] at h3
  exact span_range_eq_top_iff_ne_zero.1 hw h3.symm

end

theorem cells_locallyClosed : ∀ (O : Type) [CommRing O] (Z P : Scheme.{0}) (s : Z ⟶ Sp O) (N r : ℕ) (p₁ : P ⟶ Z) (p₂ : P ⟶ PSpace O N), IsPullback p₁ p₂ s (PSpace.str O N) → ∀ (R : Type) [CommRing R] (χ : Sp R ⟶ Z) (g : O →+* R) (Q : Matrix (Fin (N + 1)) (Fin (r + 1)) R) (Q' : Matrix (Fin (r + 1)) (Fin (N + 1)) R) (i : Fin (r + 1) → (Sp (MvPolynomial (Fin r) R) ⟶ P)), IsOpenImmersion χ → χ ≫ s = spMap g → Q' * Q = 1 → (∀ c, i c ≫ p₁ = spMap (MvPolynomial.C : R →+* MvPolynomial (Fin r) R) ≫ χ) → (∀ c, ∃ hv, i c ≫ p₂ = GlobalTheory.ProjSpace.pt ((MvPolynomial.C : R →+* MvPolynomial (Fin r) R).comp g) ((Q.map (MvPolynomial.C : R →+* MvPolynomial (Fin r) R)).mulVec (Fin.insertNth (α := fun _ => MvPolynomial (Fin r) R) c 1 MvPolynomial.X)) hv) → (∀ c, IsImmersion (i c)) ∧ (∀ c, ∃ U : P.Opens, Set.range (i c) = (⋃ c', Set.range (i c')) ∩ (U : Set P)) ∧ ∃ T : Set P, IsClosed T ∧ ⋃ c, Set.range (i c) = T ∩ p₁ ⁻¹' Set.range χ := by
  intro O _ Z P s N r p₁ p₂ hP R _ χ g Q Q' i hχ hg h hi₁ hi₂
  have hb := isPullback_baseChange N g
  rw [← hg] at hb
  let e : PSpace R N ⟶ P := hP.flip.lift (baseChange N g) (PSpace.str R N ≫ χ) (by rw [hb.w, Category.assoc])
  have he : IsPullback e (PSpace.str R N) p₁ χ := hb.of_right' hP.flip
  have he₂ : e ≫ p₂ = baseChange N g := hP.flip.lift_fst _ _ _
  have heo : IsOpenImmersion e := MorphismProperty.of_isPullback he.flip hχ
  have hr : Set.range e = p₁ ⁻¹' Set.range χ := by
    rw [← Scheme.Pullback.range_fst, ← he.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact he.isoPullback.hom.surjective.range_comp _
  choose hv hi₂ using hi₂
  have hj : ∀ c, i c = pt C ((Q.map C).mulVec (tv R c)) (hv c) ≫ e := fun c =>
    hP.hom_ext (by rw [hi₁, Category.assoc, he.w, pt_str_assoc]) (by rw [hi₂, Category.assoc, he₂, pt_baseChange])
  have hm : ∀ c x, x ∈ Set.range (i c) ↔ ∃ y, ((∀ k, y ∉ Proj.basicOpen (grading R N) (lin (res Q Q' k))) ∧
      y ∈ Proj.basicOpen (grading R N) (lin (Q' c))) ∧ e y = x := fun c x => by
    simp only [← mem_range_cell h c (hv c)]
    rw [hj, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    rfl
  have hinj := e.isOpenEmbedding.injective
  refine ⟨fun c => ?_, fun c => ⟨e ''ᵁ Proj.basicOpen (grading R N) (lin (Q' c)), Set.ext fun x => ?_⟩,
    (e ''ᵁ ⨆ k, Proj.basicOpen (grading R N) (lin (res Q Q' k)) : Set P)ᶜ, (TopologicalSpace.Opens.isOpen _).isClosed_compl,
    Set.ext fun x => ?_⟩
  · have := isImmersion_cell h c (hv c)
    rw [hj]
    infer_instance
  · simp only [Set.mem_inter_iff, Set.mem_iUnion, hm]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨c, y, hy, rfl⟩, y, hy.2, rfl⟩
    · rintro ⟨⟨c', y, hy, rfl⟩, y', hy', e'⟩
      obtain rfl := hinj e'
      exact ⟨y', ⟨hy.1, hy'⟩, rfl⟩
  · simp only [Set.mem_inter_iff, Set.mem_iUnion, hm, ← hr]
    constructor
    · rintro ⟨c, y, hy, rfl⟩
      refine ⟨?_, y, rfl⟩
      rintro ⟨y', hy', e'⟩
      obtain rfl := hinj e'
      obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy'
      exact hy.1 k hk
    · rintro ⟨hx, y, rfl⟩
      have hy : ∀ k, y ∉ Proj.basicOpen (grading R N) (lin (res Q Q' k)) := fun k hk =>
        hx ⟨y, TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk⟩, rfl⟩
      obtain ⟨c, hc⟩ := exists_mem y hy
      exact ⟨c, y, ⟨hy, hc⟩, rfl⟩

end GlobalTheory.SplitCells
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineEigenvalueEqOneOfBoxSumNeZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero

def periods {V K : Type} [AddCommGroup V] (f : V → K) : AddSubgroup V where
  carrier := {u | ∀ t, f (t + u) = f t}
  zero_mem' := fun t => by simp
  add_mem' := fun {a b} ha hb t => by rw [← add_assoc, hb, ha]
  neg_mem' := fun {a} ha t => by rw [← ha (t + -a)]; simp

theorem eigen_eq_one_of_reps {V K : Type} [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (L : AddSubgroup V)
    (S : Finset V) (hf : ∀ v, ∀ u ∈ L, f (v + u) = f v) (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ L → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ L) (T : V ≃+ V) (b : V) (χ : K) (hT : ∀ t, f (T t + b) = χ * f t)
    (hS : ∑ s ∈ S, f s ≠ 0) : χ = 1 := by
  classical
  obtain ⟨t₀, -, ht₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero hS
  have hsurj : ∀ v, ∃ t, T t + b = v := fun v => ⟨T.symm (v - b), by simp⟩
  have hχ : χ ≠ 0 := by
    rintro rfl
    obtain ⟨t, rfl⟩ := hsurj t₀
    exact ht₀ (by rw [hT, zero_mul])
  set M := periods f with hM
  have hMf : ∀ v, ∀ u ∈ M, f (v + u) = f v := fun v u hu => hu v
  have hLM : L ≤ M := fun u hu t => hf t u hu
  have hTM : ∀ u, T u ∈ M ↔ u ∈ M := fun u => by
    have e : ∀ t, f (T t + b + T u) = χ * f (t + u) := fun t => by
      rw [← hT, map_add]; congr 1; abel
    constructor
    · intro h t
      apply mul_left_cancel₀ hχ
      rw [← e, hMf _ _ h, hT]
    · intro h v
      obtain ⟨t, rfl⟩ := hsurj v
      rw [e, hMf _ _ h, hT]
  have hmap : M.map (T : V →+ V) = M := by
    ext v
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hTM u).2 hu
    · intro hv
      exact ⟨T.symm v, (hTM _).1 (by simpa using hv), by simp⟩
  have hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v := fun v => by
    have h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M := by
      rw [← QuotientAddGroup.eq]; simp
    simpa using hMf v _ h
  let S' : Finset V := S.image fun s => (QuotientAddGroup.mk s : V ⧸ M).out
  have hinj' : ∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ M → s = s' := fun s hs s' hs' h => by
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hs
    obtain ⟨a', -, rfl⟩ := Finset.mem_image.1 hs'
    have := QuotientAddGroup.eq_iff_sub_mem.2 h
    simp only [QuotientAddGroup.out_eq'] at this
    rw [this]
  have hcov' : ∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ M := fun v hv => by
    obtain ⟨s, hs, e⟩ := hcov v hv
    refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
    rw [← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.out_eq', QuotientAddGroup.eq_iff_sub_mem]
    exact hLM e
  have i1 : M.relIndex L ≠ 0 := by rw [AddSubgroup.relIndex_eq_one.2 hLM]; exact one_ne_zero
  have i2 : L.relIndex M ≠ 0 :=
    boxSum_ne_zero_invariant_affineChange.relIndex_ne_zero_of_cover L M (S.image fun s => s - t₀) fun k hk => by
      obtain ⟨s, hs, e⟩ := hcov (t₀ + k) (by rwa [hMf _ _ hk])
      refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
      convert e using 1
      abel
  have h1 := (sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff V K f L M S S' i1 i2 hf hMf hinj hcov hinj' hcov').1 hS
  have h2 := sum_coset_reps_ne_zero_iff_commensurable.finsum_quot_eq f M M S' le_rfl (by simp) hMf hinj' hcov'
  rw [AddSubgroup.relIndex_self, Nat.cast_one, one_mul] at h2
  rw [← h2] at h1
  let e : V ⧸ M ≃ V ⧸ M := (QuotientAddGroup.congr M M T hmap).toEquiv.trans (Equiv.addRight (QuotientAddGroup.mk b))
  have he : ∀ c : V ⧸ M, f (e c).out = χ * f c.out := fun c => by
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective c
    have : e (QuotientAddGroup.mk v) = QuotientAddGroup.mk (T v + b) := rfl
    rw [this, hout, hout, hT]
  have h3 : ∑ᶠ c : V ⧸ M, f (e c).out = ∑ᶠ c : V ⧸ M, f c.out := finsum_comp_equiv (f := fun c : V ⧸ M => f c.out) e
  simp only [he] at h3
  rw [← mul_finsum] at h3
  exact mul_right_cancel₀ h1 (by rw [h3, one_mul])

theorem eigen_eq_one : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E) (χ : K), (∀ t, f (T t + b) = χ * f t) → boxSum P N N f ≠ 0 → χ = 1 := by
  intro E _ _ K _ _ P hP ι _ _ f N hf T b χ hT hS
  have hq := NormalFormAtPrime.qOf_ne_zero P
  have h3 := rationalFractions_represent_primeNormQuotient.valsQ_reps E P hP N N
  refine eigen_eq_one_of_reps f (boxSum_ne_zero_invariant_affineChange.lat P ι ((qOf P : E) ^ N)⁻¹)
    (Fintype.piFinset fun _ : ι => LocE.valsQ E (qOf P) N N) (fun v u hu => ?_) (fun s hs s' hs' h => ?_)
    (fun v hv => ?_) T.toAddEquiv b χ hT (right_ne_zero_of_mul hS)
  · have := hf.2 v (((qOf P : E) ^ N)⁻¹ • u) hu
    rwa [smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hq), one_smul] at this
  · funext i
    exact h3.1 _ (Fintype.mem_piFinset.1 hs i) _ (Fintype.mem_piFinset.1 hs' i) (h i)
  · choose s hs hs' using fun i => h3.2 (v i) (hf.1 v hv i)
    exact ⟨s, Fintype.mem_piFinset.2 hs, hs'⟩

end GlobalTheory.Proof.affine_eigenvalue_eq_one_of_boxSum_ne_zero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockValAeStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_block_val_at_and_exists_inv_eq : ∀ {E : Type} [Field E] [NumberField E] {K : Type} [Field K] (ε : K →+* ℂ) (μ η : HChar E), AlmostIn ε μ → η.ValuesIn (1 / 2) ε → ∀ {r : ℕ}, Odd r → ∀ (μH ηH : Formalism.L2.NC.HC E), μH.χ = (μ : Ideles E →* ℂˣ) → ηH.χ = (η : Ideles E →* ℂˣ) → ∀ᶠ v in Filter.cofinite, (μH * ηH⁻¹).At v ((((block μ η r).val v : ℂˣ) : ℂ) * (Real.sqrt (normV v) : ℂ) ^ (-(r : ℤ))) ∧ ∃ y : K, ε y = (((block μ η r).val v : ℂˣ) : ℂ)⁻¹ := by
  first | exact @GlobalTheory.BlockVal.block_val_ae | exact GlobalTheory.BlockVal.block_val_ae | (intros; apply GlobalTheory.BlockVal.block_val_ae <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharEqOfApplyRootEqStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_char_eq_of_inertia_condition : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (P : HeightOneSpectrum (𝓞 E)), IsPlaceOver A P → ∀ {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ (χ : G E Ω →* Oˣ), Continuous (fun g => ((χ g : Oˣ) : O)) → ∀ (m : ℕ), 0 < m → ((m : ℕ) : 𝓞 E) ∉ P.asIdeal → (∀ σ ∈ Ine (F := E) A, χ σ ^ m = 1) → ∀ (ϖ : 𝓞 E), ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → ∀ π : Ω, π ^ m = algebraMap E Ω (ϖ : E) → ∀ σ ∈ Ine (F := E) A, ∀ σ' ∈ Ine (F := E) A, σ π = σ' π → χ σ = χ σ' := by
  first | exact @GlobalTheory.TameTau.char_eq_of_apply_root_eq | exact GlobalTheory.TameTau.char_eq_of_apply_root_eq | (intros; apply GlobalTheory.TameTau.char_eq_of_apply_root_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeNormGeneratorOfKummerFieldLeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmTypeNorm_generator_of_kummerField_le : ∀ (P : Pre) (δ : FieldDat P) (F : IntermediateField ℚ ℂ) [FiniteDimensional ℚ F] (j : ℕ), δ.KPsi j ≤ F → ∀ 𝔞 : Ideal (𝓞 P.host.E), 𝔞 ≠ ⊥ → ∃ β : F, β ≠ 0 ∧ Submodule.span (𝓞 F) {β} = ∏ g : Tau P.R, (Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (a : P.host.E))} ^ (P.R.sigW j).1 * Submodule.span (𝓞 F) {x : F | ∃ a ∈ 𝔞, (x : ℂ) = P.host.φ₀ (P.host.sigmaOf g (P.host.conj (a : P.host.E)))} ^ (P.R.sigW j).2) ∧ ∀ σ : F →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((P.R.sigW j).1 + (P.R.sigW j).2) := by
  first | exact @GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le | exact GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le | (intros; apply GlobalTheory.Mem.KPsiGen.typeNorm_gen_of_kPsi_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetSpanConjMulIntegralOfIntegralPairingStatement
section
open NumberField IsDedekindDomain Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detSpan_conj_mul_integral_of_integral_pairing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M M' : Submodule (𝓞 E) (Fin n → E)), (∀ v ∈ M, ∀ w ∈ M', ∑ j, IsCMField.complexConj E (v j) * w j ∈ (algebraMap (𝓞 E) E).range) → ∀ x ∈ GlobalTheory.BetaEx.detSpan M, ∀ y ∈ GlobalTheory.BetaEx.detSpan M', IsCMField.complexConj E x * y ∈ (algebraMap (𝓞 E) E).range := by
  first | exact @GlobalTheory.detSpan_conj_mul_mem_range | exact GlobalTheory.detSpan_conj_mul_mem_range | (intros; apply GlobalTheory.detSpan_conj_mul_mem_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EffCartierOfProportionalSections
section
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.ProjBlowup

namespace GlobalTheory.ProjBlowup

theorem mem_nonZeroDivisors_of_dense_compl_support {W T : Scheme.{0}} (I : W.IdealSheafData) (d : T ⟶ W)
    [IsSchemeTheoreticallyDominant d] [QuasiCompact d] (hd : ∀ t : T, d t ∉ I.support)
    (A : W.affineOpens) (s : Γ(W, A.1)) (hs : I.ideal A = Ideal.span {s}) : s ∈ nonZeroDivisors Γ(W, A.1) := by
  have hu : IsUnit (d.app A.1 s) := by
    refine T.toRingedSpace.isUnit_of_isUnit_germ _ _ fun t ht => ?_
    refine (T.mem_basicOpen _ t ht).1 ?_
    rw [← Scheme.preimage_basicOpen]
    have h := hd t
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem (U := A) ht, hs, Scheme.zeroLocus_span,
      Scheme.zeroLocus_singleton] at h
    exact not_not.1 h
  rw [mem_nonZeroDivisors_iff_right]
  intro x hx
  apply d.app_injective A.1
  have h := congrArg (d.app A.1) hx
  rw [map_mul, map_zero] at h
  rw [map_zero]
  exact hu.mul_left_eq_zero.1 h

theorem effCartier_of_proportional (R : Type) [CommRing R] (X W T : Scheme.{0}) (I : W.IdealSheafData) (L : LB X)
    (m : ℕ) (σ : Fin (m + 1) → L.Sec) (g : W ⟶ X) (ψ : W ⟶ PSpace R m) (d : T ⟶ W)
    (hI : GeneratesAlong I σ g) (hp : Proportional σ g ψ) (h₁ : IsSchemeTheoreticallyDominant d)
    (h₂ : QuasiCompact d) (hd : ∀ t : T, d t ∉ I.support) : FinalTheorems.EffCartier I := by
  intro w
  obtain ⟨k, hk⟩ : ∃ k, w ∈ g ⁻¹ᵁ L.U k :=
    TopologicalSpace.Opens.mem_iSup.1 (hI.1.ge (show w ∈ (⊤ : W.Opens) from trivial))
  obtain ⟨i, hi⟩ := GlobalTheory.ProjSpace.exists_mem_chart R m (ψ w)
  obtain ⟨A, hA, hw, hle⟩ := exists_isAffineOpen_mem_and_subset
    (show w ∈ g ⁻¹ᵁ L.U k ⊓ ψ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R m i from ⟨hk, hi⟩)
  have hAk : A ≤ g ⁻¹ᵁ L.U k := fun x hx => (hle hx).1
  have hAi : A ≤ ψ ⁻¹ᵁ GlobalTheory.ProjSpace.chart R m i := fun x hx => (hle hx).2
  have hs : I.ideal ⟨A, hA⟩ = Ideal.span {(g.appLE (L.U k) A hAk).hom ((σ i).f k)} := by
    rw [hI.2 k ⟨A, hA⟩ hAk]
    refine le_antisymm (Ideal.span_le.2 ?_) (Ideal.span_mono (Set.singleton_subset_iff.2 ⟨i, rfl⟩))
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_span_singleton'.2 ⟨_, (hp A k hAk i hAi j).symm⟩
  exact ⟨⟨A, hA⟩, _, hw, mem_nonZeroDivisors_of_dense_compl_support I d hd ⟨A, hA⟩ _ hs, hs⟩

end GlobalTheory.ProjBlowup
end

