import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSCoord
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

variable {A : Type u} [CommRing A] {N : ℕ}

lemma X_pow_mem_grading (j : Fin (N + 1)) (n : ℕ) :
    (MvPolynomial.X j ^ n : MvPolynomial (Fin (N + 1)) A) ∈ ProjSpace.grading A N n := by
  simpa using SetLike.pow_mem_graded n (ProjSpace.X_mem (A := A) (n := N) j)

def fracOn {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ ProjSpace.grading A N n)
    (j : Fin (N + 1)) : ringOn (self A N).X (ProjSpace.stdOpen A N j) :=
  (Proj.awayToSection (ProjSpace.grading A N) (MvPolynomial.X j)).hom
    (HomogeneousLocalization.mk ⟨n, ⟨P, hP⟩, ⟨MvPolynomial.X j ^ n, X_pow_mem_grading j n⟩, ⟨n, rfl⟩⟩)

lemma resM_polySection {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A} (hP : P ∈ ProjSpace.grading A N n)
    (j : Fin (N + 1)) :
    resM ((preMod (self A N).X).obj (twistN A N n)) le_top
        (polySection hP : ((preMod (self A N).X).obj (twistN A N n)).obj (op ⊤)) =
      fracOn hP j • stdFrame A j n := by
  apply ProjTwist.ext (k := (n : ℤ)) (U := ProjSpace.stdOpen A N j)
  funext x
  change Localization.mk P 1 = ((fracOn hP j).1 x).val *
    ProjTwist.val (k := (n : ℤ)) (U := Proj.basicOpen (ProjSpace.grading A N) (MvPolynomial.X j))
      (ProjTwist.upow (ProjSpace.grading A N) (ProjSpace.X_mem j) (n : ℤ)) x
  erw [ProjTwist.val_upow]
  change Localization.mk P 1 = (HomogeneousLocalization.mk _).val * _
  rw [HomogeneousLocalization.val_mk]
  unfold ProjTwist.twistFrac
  rw [Localization.mk_mul,
    Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [Submonoid.coe_mul, OneMemClass.coe_one, one_mul, Int.toNat_natCast]
  simp
  ring

lemma evalAtPoint_fracOn {ρ : A →+* ℂ} (x : (self A N).complexPoints ρ) {j : Fin (N + 1)}
    (hp : (self A N).point x ∈ ProjSpace.stdOpen A N j) {n : ℕ} {P : MvPolynomial (Fin (N + 1)) A}
    (hP : P ∈ ProjSpace.grading A N n) :
    (self A N).evalAtPoint x (germR (X := (self A N).X) hp (fracOn hP j)) = evalAt ρ x.1.rep P / x.1.rep j ^ n := by
  have e := Scheme.Hom.germ_stalkMap_apply (self A N).ι (ProjSpace.stdOpen A N j) ((self A N).point x)
    hp (fracOn hP j)
  have e2 : germR (X := (self A N).X) hp (fracOn hP j) = ((self A N).ι.stalkMap ((self A N).point x)).hom
      ((projectiveSpace A N).presheaf.germ (ProjSpace.stdOpen A N j)
        ((self A N).ι.base ((self A N).point x)) hp (fracOn hP j)) := by
    rw [e]
    rfl
  rw [e2]
  change (self A N).evalStalk ((self A N).isOver_point x) _ = _
  rw [evalStalk_stalkMap]
  unfold evalStalkProj
  rw [RingHom.comp_apply]
  have e1 : (Proj.stalkIso (ProjSpace.grading A N) _).hom.hom
      ((projectiveSpace A N).presheaf.germ (ProjSpace.stdOpen A N j)
        ((self A N).ι.base ((self A N).point x)) hp (fracOn hP j)) = (fracOn hP j).1 ⟨_, hp⟩ :=
    Proj.stalkIso'_germ _ _ _ hp _
  rw [e1]
  refine (evalAtPrime_mk _ _).trans ?_
  simp [evalAt]

lemma fibreEquivComplex_fibreMk {X : Scheme.{u}} {L : X.Modules} {p : X} {φ : locRing X p →+* ℂ}
    {U : X.Opens} (hp : p ∈ U) {e : ((preMod X).obj L).obj (op U)}
    (he : IsBasisOn ((preMod X).obj L) U e) (r : locRing X p) :
    fibreEquivComplex φ hp he (fibreMk L φ 1 (r • germM hp e)) = φ r := by
  have h := fibreEquiv_fibreMk (φ := φ) hp he 1 r
  rw [mul_one] at h
  exact (congrArg (Via.ofComplex φ).symm h).trans (RingEquiv.symm_apply_apply _ _)

theorem FSCoord.proof : FSCoord.Statement.{u} := by
  intro A _ N n ρ P hP x j hj
  have hp := point_mem_stdOpen x hj
  have hg := (germM_resM (X := (self A N).X) (le_top : ProjSpace.stdOpen A N j ≤ ⊤) hp
      (polySection hP : ((preMod (self A N).X).obj (twistN A N n)).obj (op ⊤))).symm.trans
    ((congrArg (germM (X := (self A N).X) hp) (resM_polySection hP j)).trans (germM_smul hp _ _))
  have hv : (self A N).evalGlobalSection (twistN A N n) x (polySection hP) =
      fibreMk _ ((self A N).evalAtPoint x) 1
        (germR (X := (self A N).X) hp (fracOn hP j) • germM (X := (self A N).X) hp (stdFrame A j n)) :=
    congrArg (fibreMk _ ((self A N).evalAtPoint x) 1) hg
  have key := (congrArg (fibreEquivComplex ((self A N).evalAtPoint x) hp
      (isBasisOn_frame (A := A) j n)) hv).trans
    ((fibreEquivComplex_fibreMk hp (isBasisOn_frame (A := A) j n) _).trans (evalAtPoint_fracOn x hp hP))
  exact (congrArg (· * x.1.rep j ^ n) key).trans (div_mul_cancel₀ _ (pow_ne_zero _ hj))

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSIndex
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace NumberField GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

theorem FSIndex.proof (h : FSCoord.Statement.{u}) : FSIndex.Statement.{u} := by
  intro A _ N n ρ x j hj s
  set k := CP.chartIndex x.1
  have hk : x.1.rep k ≠ 0 := rep_chartIndex_ne_zero x.1
  have hP : (MvPolynomial.X k : MvPolynomial (Fin (N + 1)) A) ^ n ∈ ProjSpace.grading A N n :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X_pow k n)
  set w := (self A N).evalGlobalSection (twistN A N n) x (polySection hP)
  set ek := fsFrameCoord n ρ x
  set ej := fibreEquivComplex ((self A N).evalAtPoint x) (point_mem_stdOpen x hj)
    (isBasisOn_frame (A := A) j n)
  have hev : evalAt ρ x.1.rep ((MvPolynomial.X k : MvPolynomial (Fin (N + 1)) A) ^ n) =
      x.1.rep k ^ n := by simp [evalAt]
  have hwk : ek w = 1 := by
    have h1 := h A N n ρ _ hP x k hk
    rw [hev] at h1
    exact mul_right_cancel₀ (pow_ne_zero n hk) (h1.trans (one_mul _).symm)
  have hwj : ej w * x.1.rep j ^ n = x.1.rep k ^ n := by
    have h1 := h A N n ρ _ hP x j hj
    rwa [hev] at h1

  have hs : s = ek s • w := by
    apply ek.injective
    rw [LinearEquiv.map_smul, hwk, smul_eq_mul, mul_one]
  have hnj : ‖ej w‖ * ‖x.1.rep j‖ ^ n = ‖x.1.rep k‖ ^ n := by
    rw [← norm_pow, ← norm_pow, ← norm_mul, hwj]
  have hfs : fsFibreNorm n ρ x s = ‖ek s‖ * ‖x.1.rep k‖ ^ n / norm2 x.1.rep ^ n := rfl
  rw [hfs]
  conv_rhs => rw [hs, LinearEquiv.map_smul, smul_eq_mul, norm_mul, mul_assoc, hnj]

example (h : FSCoord.Statement.{0}) (s : (self (𝓞 ℚ) 1).Fibre (twistN (𝓞 ℚ) 1 1) pointQ) :
    fsFibreNorm 1 _ pointQ s =
      ‖fibreEquivComplex ((self (𝓞 ℚ) 1).evalAtPoint pointQ) (point_mem_stdOpen pointQ pointQ_rep_ne_zero)
          (isBasisOn_frame (A := 𝓞 ℚ) 0 1) s‖ * ‖pointQ.1.rep 0‖ ^ 1 / norm2 pointQ.1.rep ^ 1 :=
  FSIndex.proof h _ _ _ _ _ _ pointQ_rep_ne_zero _

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PFSNormConj
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace GroundTheory.Arith.SchemeCoh

universe u

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma fibreEquivComplex_value_eq {X : Scheme.{u}} {L : X.Modules} {p : X}
    (φ : locRing X p →+* ℂ) {U V : X.Opens} (hpU : p ∈ U) (hpV : p ∈ V)
    {e : ((preMod X).obj L).obj (op V)} (he : IsBasisOn ((preMod X).obj L) V e)
    (s : ((preMod X).obj L).obj (op U)) (r : locRing X p) (hr : germM hpU s = r • germM hpV e) :
    fibreEquivComplex φ hpV he (value φ hpU s) = φ r := by
  change (Via.ofComplex φ).symm (fibreEquiv φ hpV he (fibreMk L φ 1 (germM hpU s))) = φ r
  rw [hr, fibreEquiv_fibreMk, mul_one, RingEquiv.symm_apply_apply]

theorem FSNormConj.proof (h : FSIndex.Statement.{u}) : FSNormConj.Statement.{u} := by
  intro A _ N n ρ U s x hx hx'
  obtain ⟨j, hj⟩ : ∃ j, x.1.rep j ≠ 0 := ⟨_, rep_chartIndex_ne_zero x.1⟩
  obtain ⟨c, hc⟩ := exists_rep_conj x.1
  have hcj : (CP.conj x.1).rep j = (c : ℂ) * starRingEnd ℂ (x.1.rep j) := by
    rw [hc, Pi.smul_apply, smul_eq_mul, CP.conjVec_apply]
  have hj' : ((self A N).conjPoint ρ x).1.rep j ≠ 0 := by
    change (CP.conj x.1).rep j ≠ 0
    rw [hcj]
    exact mul_ne_zero c.ne_zero ((map_ne_zero _).mpr hj)
  have hpj := point_mem_stdOpen x hj
  obtain ⟨r, hr⟩ := (bijective_smul_germ hpj (isBasisOn_frame (A := A) j n)).2 (germM hx s)
  obtain ⟨V, -, hpV, f, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq (X := (self A N).X.toTopCat) (self A N).X.sheaf.obj r hx
  have key : ∀ (q : (self A N).X) (_ : q = (self A N).point x) (φ : locRing (self A N).X q →+* ℂ)
      (hqU : q ∈ U) (hqj : q ∈ ProjSpace.stdOpen A N j) (hqV : q ∈ V),
      fibreEquivComplex φ hqj (isBasisOn_frame (A := A) j n) (value φ hqU s) = φ (germR hqV f) := by
    intro q hq φ hqU hqj hqV
    subst hq
    exact fibreEquivComplex_value_eq φ hqU hqj _ s _ hr.symm
  have hV' : (self A N).point ((self A N).conjPoint ρ x) ∈ V := by
    rw [point_conjPoint]
    exact hpV
  have hj'' := point_mem_stdOpen _ hj'
  rw [h A N n _ _ j hj', h A N n ρ x j hj]
  unfold sectionValue
  rw [key _ (point_conjPoint _ x) _ hx' hj'' hV', key _ rfl _ hx hpj hpV,
    evalAtPoint_conjPoint_germ _ x hpV hV', Complex.norm_conj]
  have hn : norm2 (CP.conj x.1).rep = ‖(c : ℂ)‖ * norm2 x.1.rep := by
    rw [hc, euclideanNorm_smul]
    congr 1
    simp [norm2, normSq2, CP.conjVec_apply]
  have hc0 : 0 < ‖(c : ℂ)‖ := norm_pos_iff.mpr c.ne_zero
  change _ * ‖(CP.conj x.1).rep j‖ ^ n / norm2 (CP.conj x.1).rep ^ n = _
  rw [hn, hcj, norm_mul, Complex.norm_conj, mul_pow, mul_pow]
  field_simp

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PMonomialBasis
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry GroundTheory.Arith.SchemeCoh

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma polySection_congr {A : Type u} [CommRing A] {N n : ℕ} {P Q : MvPolynomial (Fin (N + 1)) A}
    (hP : P ∈ ProjSpace.grading A N n) (hQ : Q ∈ ProjSpace.grading A N n) (h : P = Q) :
    polySection hP = polySection hQ := by
  subst h; rfl

def monomialBasisGrading (A : Type u) [CommRing A] (N n : ℕ) :
    Module.Basis {a : Fin (N + 1) →₀ ℕ // a.degree = n} A (ProjSpace.grading A N n) :=
  (MvPolynomial.basisRestrictSupport A {a : Fin (N + 1) →₀ ℕ | a.degree = n}).map
    (LinearEquiv.ofEq _ _ (MvPolynomial.homogeneousSubmodule_eq_finsupp_supported (σ := Fin (N + 1)) (R := A) n).symm)

lemma monomialBasisGrading_apply (A : Type u) [CommRing A] (N n : ℕ)
    (a : {a : Fin (N + 1) →₀ ℕ // a.degree = n}) :
    (monomialBasisGrading A N n a : MvPolynomial (Fin (N + 1)) A) = MvPolynomial.monomial a.1 1 := by
  have h : monomialBasisGrading A N n a = ⟨_, monomial_mem_grading (A := A) a.1 a.2⟩ := by
    rw [Module.Basis.apply_eq_iff]
    ext b
    simp only [monomialBasisGrading, MvPolynomial.basisRestrictSupport, Module.Basis.map_repr,
      Finsupp.single_apply, Subtype.ext_iff]
    change MvPolynomial.coeff b.1 (MvPolynomial.monomial a.1 (1 : A)) = _
    rw [MvPolynomial.coeff_monomial]
  rw [h]

theorem MonomialBasis.proof (h : PolySections.Statement.{u}) : MonomialBasis.Statement.{u} := by
  intro A _ N n
  obtain ⟨e, he⟩ := h A N n
  refine ⟨(monomialBasisGrading A N n).map e, fun a => ?_⟩
  rw [Module.Basis.map_apply, he]
  exact polySection_congr _ _ (monomialBasisGrading_apply A N n a)

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PPNFlat
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory GroundTheory.Arith.SchemeCoh MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

lemma chart_structureMap_eq (A : Type u) [CommRing A] (N : ℕ) (j : Fin (N + 1)) :
    (HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading A N)
        (Submonoid.powers (X j : MvPolynomial (Fin (N + 1)) A))).comp
        (algebraMap A (ProjSpace.grading A N 0)) =
      (ProjSpace.polyToChart A j).comp C := by
  rw [ProjSpace.polyToChart, MvPolynomial.eval₂Hom_comp_C]

lemma flat_chart_structureMap (A : Type u) [CommRing A] (N : ℕ) (j : Fin (N + 1)) :
    ((HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading A N)
        (Submonoid.powers (X j : MvPolynomial (Fin (N + 1)) A))).comp
        (algebraMap A (ProjSpace.grading A N 0))).Flat := by
  rw [chart_structureMap_eq]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (ProjSpace.chartEquiv A j).symm.bijective)
  rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
  infer_instance

theorem PNFlat.proof : PNFlat.Statement.{u} := by
  intro A _ N
  change Flat (𝟙 _ ≫ ProjSpace.toSpecBase A N)
  rw [Category.id_comp]
  have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top _ (ProjSpace.iSup_stdOpen (A := A) (n := N))).mpr
    fun j => ?_
  change Flat ((Proj.basicOpen (ProjSpace.grading A N) (X j)).ι ≫ ProjSpace.toSpecBase A N)
  have e : (Proj.basicOpen (ProjSpace.grading A N) (X j)).ι =
      (Proj.basicOpenIsoSpec (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos).hom ≫
        Proj.awayι (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos := by
    rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have h : Flat (Proj.awayι (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos ≫
      ProjSpace.toSpecBase A N) := by
    rw [ProjSpace.toSpecBase, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, Flat.SpecMap_iff]
    exact flat_chart_structureMap A N j
  rw [e, Category.assoc]
  infer_instance

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.PPNReduced
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry GroundTheory.Arith.SchemeCoh

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

lemma SectionsLatticeFS.isReduced_homogeneousLocalization {ι R A : Type*} [CommRing R]
    [CommRing A] [Algebra R A] [AddCommMonoid ι] [DecidableEq ι] {𝒜 : ι → Submodule R A}
    [GradedAlgebra 𝒜] {S : Submonoid A} [IsReduced (Localization S)] :
    IsReduced (HomogeneousLocalization 𝒜 S) := by
  refine ⟨fun y ⟨n, hn⟩ => HomogeneousLocalization.val_injective (𝒜 := 𝒜) (x := S) ?_⟩
  rw [HomogeneousLocalization.val_zero]
  refine IsReduced.eq_zero _ ⟨n, ?_⟩
  rw [← HomogeneousLocalization.val_pow, hn, HomogeneousLocalization.val_zero]

theorem SectionsLatticeFS.PNReduced.proof : SectionsLatticeFS.PNReduced.Statement.{u} := by
  intro A _ _ N
  have : ∀ x : projectiveSpace A N,
      _root_.IsReduced ((projectiveSpace A N).presheaf.stalk x) := fun x => by
    have := x.isPrime
    have : _root_.IsReduced (CommRingCat.of
        (HomogeneousLocalization.AtPrime (ProjSpace.grading A N)
          x.asHomogeneousIdeal.toIdeal)) :=
      SectionsLatticeFS.isReduced_homogeneousLocalization
    exact isReduced_of_injective _
      (Proj.stalkIso (ProjSpace.grading A N) x).commRingCatIsoToRingEquiv.injective
  exact isReduced_of_isReduced_stalk (projectiveSpace A N)

end GroundTheory.Heights₂.Heights
end

